package main

//
// Process MAT INPUT, MAT PRINT and MAT READ
//

func matOperate(opcode int, ops []*tokenNode) {

	var option1, option2, printNL bool
	var subs []int16
	var i, j int16
	var opsLen int
	var sym *symtabNode

	switch opcode {
	case PRINT:
		opsLen = 2

		if ops[1] != nil {
			if ops[1].token == TRAILING_COMMA {
				option1 = true
			}
			printNL = true
		} else {
			option2 = true
		}

	case INPUT:
		fallthrough
	case READ:
		opsLen = 1
	}

	runtimeCheck(len(ops) == opsLen, "matOperate botch")

	sym = lookupMatrix(ops[0], LOOKUPMATRIXANY)

	ndims := len(sym.dims)
	switch ndims {
	case 1:
		subs = make([]int16, 1)

	case 2:
		subs = make([]int16, 2)
	}

	for i = 1; i <= sym.dims[0]; i++ {
		subs[0] = i

		switch ndims {
		case 1:
			matOperateInner(opcode, sym, option1, option2, subs...)

		case 2:
			for j = 1; j <= sym.dims[1]; j++ {
				subs[1] = j
				matOperateInner(opcode, sym, option1, option2, subs...)
			}

			if i != sym.dims[0] && !option2 {
				resetPrint(false)
			}
		}
	}

	if printNL {
		resetPrint(true)
	}
}

//
// Low-level routine to process specific array elements for matOperate
//

func matOperateInner(opcode int, sym *symtabNode,
	option1, option2 bool, subs ...int16) {

	var val any

	switch opcode {
	case INPUT:
		input := readInputLine(0, executePrompt)
		if sym.vType == FVAR {
			storeFloatVar(sym, convertFloat(input), subs...)
		} else {
			storeIntVar(sym, convertInt16(input), subs...)
		}

	case PRINT:
		if sym.vType == FVAR {
			val = fetchFloatVar(sym, subs...)
		} else {
			val = fetchIntVar(sym, subs...)
		}

		basicPrint(basicFormat(val), 0, false)
		basicPrint("", 0, option1)
		if option2 {
			resetPrint(true)
		}

	case READ:
		val = readDataItem()

		if sym.vType == FVAR {
			storeFloatVar(sym, val.(float64), subs...)
		} else {
			storeIntVar(sym, val.(int16), subs...)
		}
	}
}

//
// Process array assignment functionality
//

func matAssign(ops []*tokenNode) {

	mtype := LOOKUPMATRIXANY

	basicAssert(len(ops) == 2, "MAT EQ botch")

	ops0 := ops[0]
	ops1 := ops[1]

	switch ops1.token {
	default:
		unexpectedTokenError(ops1.token)

	case IDN:
		mtype = LOOKUPMATRIXSQUARE

		//	case INV:
		//		mtype = LOOKUPMATRIXSQUARE

	case TRN:
		mtype = LOOKUPMATRIX2D

	case FVAR, IVAR, CON, ZER, PLUS, MINUS, STAR:
	}

	lhs := lookupMatrix(ops0, mtype)

	switch ops1.token {
	case CON:
		initializeMatrix(lhs, CON)

	case IDN:
		initializeMatrix(lhs, IDN)

		//	case INV:
		//		rhs := lookupMatrix(ops1.operands[0], mtype)
		//		runtimeCheck(lhs.vType == FVAR && rhs.vType == FVAR,
		//			"INV does not support integer matrices")
		//		checkMatrixDestination(lhs, rhs)
		//		checkMatrixCompatility(lhs, rhs, true)
		//		runtimeError("NOT YET IMPLEMENTED!")

	case TRN:
		rhs := lookupMatrix(ops1.operands[0], mtype)
		checkMatrixDestination(lhs, rhs)
		checkMatrixCompatility(lhs, rhs, true)
		transposeMatrix(lhs, rhs)

	case ZER:
		initializeMatrix(lhs, ZER)

	case PLUS, MINUS:
		rhs1 := lookupMatrix(ops1.operands[0], mtype)
		rhs2 := lookupMatrix(ops1.operands[1], mtype)

		checkMatrixCompatility(rhs1, rhs2, false)
		checkMatrixCompatility(lhs, rhs1, false)
		checkMatrixCompatility(lhs, rhs2, false)

		switch ops1.token {
		case PLUS:
			addMatrices(lhs, rhs1, rhs2, false)

		case MINUS:
			addMatrices(lhs, rhs1, rhs2, true)
		}

	case STAR:
		tops := ops1.operands[0]
		switch tops.token {
		default:
			unexpectedTokenError(tops.token)

		case NRPN:
			mult := evaluateNumericExpr(tops)
			rhs := lookupMatrix(ops1.operands[1], mtype)

			checkMatrixCompatility(lhs, rhs, false)

			//
			// We also need to make sure the scalar multiplier and
			// the RHS are the same type
			//

			ok := true

			switch mult.(type) {
			case float64:
				if rhs.vType != FVAR {
					ok = false
				}

			case int16:
				if rhs.vType != IVAR {
					ok = false
				}
			}

			runtimeCheck(ok, "Matrix and multiplier are not compatible")

			scalarMultiplyMatrix(lhs, rhs, mult)

		case FVAR, IVAR:
			rhs1 := lookupMatrix(ops1.operands[0], mtype)
			rhs2 := lookupMatrix(ops1.operands[1], mtype)
			checkMatrixDestination(lhs, rhs1)
			checkMatrixDestination(lhs, rhs2)
			checkMatrixCompatility(rhs1, rhs2, true)
			checkMatrixDims(lhs, rhs1, rhs2)
			multiplyMatrices(lhs, rhs1, rhs2)
		}

	case FVAR, IVAR:
		rhs := lookupMatrix(ops1, mtype)
		checkMatrixDestination(lhs, rhs)
		checkMatrixCompatility(lhs, rhs, false)
		copyMatrix(lhs, rhs)
	}
}

func initializeMatrix(sym *symtabNode, opcode int) {

	var i, j int16

	ndims := len(sym.dims)

	for i = 1; i <= sym.dims[0]; i++ {
		switch ndims {
		case 1:
			basicAssert(opcode == CON || opcode == ZER,
				"initializeMatrix botch")

			switch sym.vType {
			case FVAR:
				val := 0.0
				if opcode == CON {
					val = 1.0
				}
				sym.value.f[0][i] = val

			case IVAR:
				val := 0
				if opcode == CON {
					val = 1
				}
				sym.value.i[0][i] = int16(val)
			}

		case 2:
			basicAssert(opcode == CON || opcode == IDN || opcode == ZER,
				"initializeMatrix botch")

			for j = 1; j <= sym.dims[1]; j++ {
				switch sym.vType {
				case FVAR:
					val := 0.0
					if opcode == CON || (opcode == IDN && i == j) {
						val = 1.0
					}
					sym.value.f[i][j] = float64(val)

				case IVAR:
					val := 0
					if opcode == CON || (opcode == IDN && i == j) {
						val = 1
					}
					sym.value.i[i][j] = int16(val)
				}
			}
		}
	}
}

func transposeMatrix(lhs, rhs *symtabNode) {

	var i, j int16

	for i = 1; i <= rhs.dims[0]; i++ {
		for j = 1; j <= rhs.dims[1]; j++ {
			switch rhs.vType {
			case FVAR:
				lhs.value.f[j][i] = rhs.value.f[i][j]

			case IVAR:
				lhs.value.i[j][i] = rhs.value.i[i][j]
			}

		}
	}
}

func copyMatrix(lhs, rhs *symtabNode) {

	switch rhs.vType {
	case FVAR:
		copy(lhs.value.f, rhs.value.f)

	case IVAR:
		copy(lhs.value.i, rhs.value.i)
	}
}

func addMatrices(lhs, rhs1, rhs2 *symtabNode, sub bool) {

	var i, j int16
	var sign int16
	var fsign float64

	ndims := len(lhs.dims)

	if sub {
		sign = -1
		fsign = -1.0
	} else {
		sign = 1
		fsign = 1.0
	}

	for i = 1; i <= lhs.dims[0]; i++ {
		switch ndims {
		case 1:
			switch lhs.vType {
			case FVAR:
				lhs.value.f[0][i] = rhs1.value.f[0][i] +
					fsign*rhs2.value.f[0][i]
				checkMatrixFloatingStatus(lhs.value.f[0][i])

			case IVAR:
				lhs.value.i[0][i] = rhs1.value.i[0][i] +
					sign*rhs2.value.i[0][i]
			}

		case 2:
			for j = 1; j <= lhs.dims[1]; j++ {
				switch lhs.vType {
				case FVAR:
					lhs.value.f[i][j] = rhs1.value.f[i][j] +
						fsign*rhs2.value.f[i][j]
					checkMatrixFloatingStatus(lhs.value.f[i][j])

				case IVAR:
					lhs.value.i[i][j] = rhs1.value.i[i][j] +
						sign*rhs2.value.i[i][j]
				}
			}
		}
	}
}

func scalarMultiplyMatrix(lhs, rhs *symtabNode, mult any) {

	var i, j int16
	var imult int16
	var fmult float64

	ndims := len(lhs.dims)

	switch mult := mult.(type) {
	case float64:
		fmult = mult

	case int16:
		imult = mult
	}

	for i = 1; i <= lhs.dims[0]; i++ {
		switch ndims {
		case 1:
			switch lhs.vType {
			case FVAR:
				lhs.value.f[0][i] = rhs.value.f[0][i] * fmult
				checkMatrixFloatingStatus(lhs.value.f[0][i])

			case IVAR:
				lhs.value.i[0][i] = rhs.value.i[0][i] * imult
			}

		case 2:
			for j = 1; j <= lhs.dims[1]; j++ {
				switch lhs.vType {
				case FVAR:
					lhs.value.f[i][j] = rhs.value.f[i][j] * fmult
					checkMatrixFloatingStatus(lhs.value.f[i][j])

				case IVAR:
					lhs.value.i[i][j] = rhs.value.i[i][j] * imult
				}
			}
		}
	}
}

func multiplyMatrices(lhs, rhs1, rhs2 *symtabNode) {

	var dr, dc, i int16

	for dr = 1; dr <= rhs1.dims[0]; dr++ {
		for dc = 1; dc <= rhs2.dims[1]; dc++ {
			sum := 0.0
			for i = 1; i <= rhs1.dims[1]; i++ {
				sum += rhs1.value.f[dr][i] * rhs2.value.f[i][dc]
			}

			checkMatrixFloatingStatus(sum)
			lhs.value.f[dr][dc] = sum
		}
	}
}

func checkMatrixDestination(dsym, ssym *symtabNode) {

	runtimeCheck(dsym.name != ssym.name,
		"Matrix cannot be source and destination")
}

func checkMatrixDims(lhs, rhs1, rhs2 *symtabNode) {

	runtimeCheck(lhs.dims[0] == rhs1.dims[0] &&
		lhs.dims[1] == rhs2.dims[1], "Incompatible matrix dimensions")
}

func checkMatrixCompatility(sym1, sym2 *symtabNode, swapDims bool) {

	runtimeCheck(sym1.vType == sym2.vType, "Incompatible matrix types")

	bad := (len(sym1.dims) != len(sym2.dims))

	if !bad {
		switch len(sym1.dims) {
		case 1:
			bad = sym1.dims[0] != sym2.dims[0]

		case 2:
			if swapDims {
				bad = (sym1.dims[0] != sym2.dims[1] ||
					sym1.dims[1] != sym2.dims[0])
			} else {
				bad = (sym1.dims[0] != sym2.dims[0] ||
					sym1.dims[1] != sym2.dims[1])
			}
		}
	}

	if bad {
		runtimeError("Incompatible matrix dimensions")
	}
}

func checkMatrixFloatingStatus(val float64) {

	state := createExecutionState(nil)
	rpnPush(&state.stack, val)
	checkFloatingStatus(state)
}
