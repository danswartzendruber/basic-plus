package main

//
// Process MAT requests
//

import (
	_ "fmt"
	"github.com/Arceus-7/matrix"
)

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

	sym = lookupArray(ops[0], LOOKUPMATRIXANY)

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

		//
		// Ugly: BASIC-PLUS requires DATA items as floats for READ
		// even if the variable is integer
		//

	case READ:
		val := readDataItem()

		if sym.vType == FVAR {
			storeFloatVar(sym, val.(float64), subs...)
		} else {
			storeIntVar(sym, floatToInt16(val.(float64)), subs...)
		}
	}
}

//
// Process array assignment functionality
//

func matAssign(ops []*tokenNode) {

	var err error

	mtype := LOOKUPMATRIXANY

	basicAssert(len(ops) == 2, "MAT EQ botch")

	ops0 := ops[0]
	ops1 := ops[1]

	switch ops1.token {
	default:
		unexpectedTokenError(ops1.token)

	case IDN:
		mtype = LOOKUPMATRIXSQUARE

	case INV:
		mtype = LOOKUPMATRIXSQUARE

	case TRN, STAR:
		mtype = LOOKUPMATRIX2D

	case FVAR, IVAR, CON, ZER, PLUS, MINUS:
	}

	lhs := lookupArray(ops0, mtype)

	switch ops1.token {
	case CON:
		initializeArray(lhs, CON)

	case IDN:
		initializeArray(lhs, IDN)

	case INV:
		rhs := lookupArray(ops1.operands[0], mtype)

		checkArrayDestination(lhs, rhs)
		checkArrayCompatibility(lhs, rhs, true)

		if rhs.vType == FVAR {
			var srcMatrix *matrix.Matrix[float64]
			var dstMatrix *matrix.Matrix[float64]
			var tmp [][]float64

			tmp = removeFirstRowAndCol[float64](rhs.value.f)
			srcMatrix, _ = matrix.New[float64](tmp) /// cannot fail

			if dstMatrix, err = srcMatrix.Inverse(); err != nil {
				runtimeError(EMATRIXERROR)
			}

			if r.det, err = srcMatrix.Det(); err != nil {
				runtimeError(EMATRIXERROR) // is this even possible?
			}

			lhs.value.f = insertFirstRowAndCol[float64](dstMatrix.Data())

		} else {
			runtimeError("INV does not support integer matrices")
		}

	case TRN:
		rhs := lookupArray(ops1.operands[0], mtype)

		if rhs.vType == FVAR {
			var srcMatrix *matrix.Matrix[float64]
			var dstMatrix *matrix.Matrix[float64]
			tmp := removeFirstRowAndCol[float64](rhs.value.f)
			srcMatrix, _ = matrix.New[float64](tmp) // cannot fail
			dstMatrix = matrix.Transpose(srcMatrix)
			lhs.value.f = insertFirstRowAndCol[float64](dstMatrix.Data())
		} else {
			var srcMatrix *matrix.Matrix[int16]
			var dstMatrix *matrix.Matrix[int16]
			tmp := removeFirstRowAndCol[int16](rhs.value.i)
			srcMatrix, _ = matrix.New[int16](tmp) // cannot fail
			dstMatrix = matrix.Transpose(srcMatrix)
			lhs.value.i = insertFirstRowAndCol[int16](dstMatrix.Data())
		}

	case ZER:
		initializeArray(lhs, ZER)

	case PLUS, MINUS:
		rhs1 := lookupArray(ops1.operands[0], mtype)
		rhs2 := lookupArray(ops1.operands[1], mtype)

		checkArrayCompatibility(rhs1, rhs2, false)
		checkArrayCompatibility(lhs, rhs1, false)
		checkArrayCompatibility(lhs, rhs2, false)

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
			rhs := lookupArray(ops1.operands[1], mtype)

			checkArrayCompatibility(lhs, rhs, false)

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
			rhs1 := lookupArray(ops1.operands[0], mtype)
			rhs2 := lookupArray(ops1.operands[1], mtype)
			checkArrayDestination(lhs, rhs1)
			checkArrayDestination(lhs, rhs2)
			checkArrayCompatibility(rhs1, rhs2, true)
			checkArrayDims(lhs, rhs1, rhs2)

			if rhs1.vType == FVAR {
				var srcMatrix1, srcMatrix2 *matrix.Matrix[float64]
				var dstMatrix *matrix.Matrix[float64]
				tmp := removeFirstRowAndCol[float64](rhs1.value.f)
				srcMatrix1, _ = matrix.New[float64](tmp) // cannot fail
				tmp = removeFirstRowAndCol[float64](rhs2.value.f)
				srcMatrix2, _ = matrix.New[float64](tmp)          // ditto
				dstMatrix, _ = matrix.Mul(srcMatrix1, srcMatrix2) // ditto
				lhs.value.f = insertFirstRowAndCol[float64](dstMatrix.Data())
				checkArrayFloatingStatus(lhs.value.f)
			} else {
				var srcMatrix1, srcMatrix2 *matrix.Matrix[int16]
				var dstMatrix *matrix.Matrix[int16]
				tmp := removeFirstRowAndCol[int16](rhs1.value.i)
				srcMatrix1, _ = matrix.New[int16](tmp) // cannot fail
				tmp = removeFirstRowAndCol[int16](rhs2.value.i)
				srcMatrix2, _ = matrix.New[int16](tmp)            // ditto
				dstMatrix, _ = matrix.Mul(srcMatrix1, srcMatrix2) // ditto
				lhs.value.i = insertFirstRowAndCol[int16](dstMatrix.Data())
			}
		}

	case FVAR, IVAR:
		rhs := lookupArray(ops1, mtype)
		checkArrayDestination(lhs, rhs)
		checkArrayCompatibility(lhs, rhs, false)
		copyMatrix(lhs, rhs)
	}
}

func initializeArray(sym *symtabNode, opcode int) {

	var i, j int16

	ndims := len(sym.dims)

	for i = 1; i <= sym.dims[0]; i++ {
		switch ndims {
		case 1:
			basicAssert(opcode == CON || opcode == ZER,
				"initializeArray botch")

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
				"initializeArray botch")

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

				case IVAR:
					lhs.value.i[i][j] = rhs1.value.i[i][j] +
						sign*rhs2.value.i[i][j]
				}
			}
		}
	}

	if lhs.vType == FVAR {
		checkArrayFloatingStatus(lhs.value.f)
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

			case IVAR:
				lhs.value.i[0][i] = rhs.value.i[0][i] * imult
			}

		case 2:
			for j = 1; j <= lhs.dims[1]; j++ {
				switch lhs.vType {
				case FVAR:
					lhs.value.f[i][j] = rhs.value.f[i][j] * fmult

				case IVAR:
					lhs.value.i[i][j] = rhs.value.i[i][j] * imult
				}
			}
		}
	}

	if lhs.vType == FVAR {
		checkArrayFloatingStatus(lhs.value.f)
	}
}

func checkArrayDestination(dsym, ssym *symtabNode) {

	runtimeCheck(dsym.name != ssym.name,
		"Matrix cannot be source and destination")
}

func checkArrayDims(lhs, rhs1, rhs2 *symtabNode) {

	runtimeCheck(lhs.dims[0] == rhs1.dims[0] &&
		lhs.dims[1] == rhs2.dims[1], "Incompatible matrix dimensions")
}

func checkArrayCompatibility(sym1, sym2 *symtabNode, swapDims bool) {

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

//
// The routines that do matrix arithmetic don't check for floating
// errorw, so when they finish, we scan the slices looking for errors
//

func checkArrayFloatingStatus(sl [][]float64) {

	if len(sl) == 1 {
		for i := 1; i < len(sl[0]); i++ {
			if floatingError(sl[0][i]) {
				runtimeError(EFLOATINGERROR)
			}
		}
	} else {
		for i := 1; i < len(sl); i++ {
			for j := 1; j < len(sl[i]); j++ {
				if floatingError(sl[i][j]) {
					runtimeError(EFLOATINGERROR)
				}
			}
		}
	}
}

//
// Ugliness: BASIC-PLUS arrays run from 0 to H, but the matrix package
// we are leveraging is the usual 0 to N-1.  BASIC-PLUS matrix operations
// ignore the 0th element.  We cope by copying the source matrix to a new
// slice of slices omitting the 0th entries.  Gack!
//

func removeFirstRowAndCol[M float64 | int16](src [][]M) [][]M {

	newLen := len(src) - 1
	dst := make([][]M, newLen)

	for i := 0; i < newLen; i++ {
		dst[i] = make([]M, newLen)
		for j := 0; j < newLen; j++ {
			dst[i][j] = src[i+1][j+1]
		}
	}

	return dst
}

//
// Copy a Matrix to a BASIC-PLUS matrix
//

func insertFirstRowAndCol[M float64 | int16](src [][]M) [][]M {

	newLen := len(src) + 1
	dst := make([][]M, newLen)

	for i := 0; i < newLen-1; i++ {
		dst[i+1] = make([]M, newLen)
		for j := 0; j < newLen-1; j++ {
			dst[i+1][j+1] = src[i][j]
		}
	}

	return dst
}
