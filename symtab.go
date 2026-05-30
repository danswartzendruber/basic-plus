package main

import (
	"fmt"
	"strings"
)

// A complication arises from the fact that BASIC-PLUS allows scalar
// and array variables to have the same name. An array reference here
// will be known by the optional dims parameters being present.
// We handle this by having an array of 2 symtab maps.  The first is for
// scalar variables, and the second for arrays
//

//
// Initialize the symbol table to pristine state
//

func initSymbolTable() {

	g.symtabMap[0] = make(map[string]*symtabNode)
	g.symtabMap[1] = make(map[string]*symtabNode)
}

//
// This function takes a variable token and returns the token type
//

func decodeVarToken(token any) (int, string) {

	var varType int
	var name string

	switch token.(type) {
	default:
		unexpectedTypeError(token)

	case fvarToken:
		varType, name = FVAR, getVarName(token)

	case ivarToken:
		varType, name = IVAR, getVarName(token)

	case svarToken:
		varType, name = SVAR, getVarName(token)
	}

	return varType, name
}

//
// This function takes an arbitrary object, and gins up an appropriate
// varToken object.  This is necessary because the symbol lookup and
// create routines can be called from the expression processor, which
// pass in varToken objects, or tokenNode pointers, if called from
// the LHS code in executeLet() or processDim().  If we already have
// a varToken object, just return it
//

func generateVarToken(token any) any {

	switch token.(type) {
	default:
		unexpectedTypeError(token)

	case fnfvarToken, fnivarToken, fnsvarToken:
		// NOP

	case fvarToken, ivarToken, svarToken:
		// NOP

	case *tokenNode:
		tnode := token.(*tokenNode)
		if tnode.token == SUBSCR {
			tnode = token.(*tokenNode).operands[0]
		}

		switch tnode.token {

		default:
			unexpectedTokenError(tnode.token)

		case FNFVAR:
			token = fnfvarToken(tnode.tokenData.(string))

		case FNIVAR:
			token = fnivarToken(tnode.tokenData.(string))

		case FNSVAR:
			token = fnsvarToken(tnode.tokenData.(string))

		case FVAR:
			token = fvarToken(tnode.tokenData.(string))

		case IVAR:
			token = ivarToken(tnode.tokenData.(string))

		case SVAR:
			token = svarToken(tnode.tokenData.(string))
		}
	}

	return token
}

//
// This function takes a variable name and and options subscript(s)
// and returns its current value
//

func lookupSymbolValue(token any, subs ...int16) any {

	token = generateVarToken(token)

	sym := lookupSymbolRef(token, subs...)

	switch token.(type) {
	default:
		unexpectedTypeError(token)
		panic(nil) // avoid compiler complaint

	case fvarToken:
		return fetchFloatVar(sym, subs...)

	case ivarToken:
		return fetchIntVar(sym, subs...)

	case svarToken:
		return fetchStringVar(sym, subs...)
	}
}

//
// Lookup a symbol, and if it doesn't exists, create it with optional
// dimensionality
//

func lookupSymbolRef(token any, subs ...int16) (ret *symtabNode) {

	var dims []int16

	token = generateVarToken(token)

	//
	// Check to make sure the symbol in question is not a formal
	// parameter of an active user defined function.  If it is,
	// throw an exception.  We don't need to check anything other
	// than the top-level active function due to BASIC-PLUS not
	// having lexical scope
	//

	if getParamValue(getVarName(token)) != nil {
		runtimeError("Function parameters may not be modified")
	}

	sym := lookupSymbol(token, len(subs))
	if sym == nil {
		switch len(subs) {
		case 2:
			dims = append(dims, maxImplicitSubscript)
			fallthrough
		case 1:
			dims = append(dims, maxImplicitSubscript)
		}
		sym = createSymbol(token, dims...)
	}

	return sym
}

//
// Lookup a 1 or 2 dimensional symbol, throwing an error if it
// does not exist (should have been created by a DIM statement),
// optionally enforcing squareness or 2d-ness
//

func lookupArray(token any, mtype int) *symtabNode {

	var sym *symtabNode

	if sym = lookupSymbol(token, -1); sym == nil {
		runtimeError("Matrix not dimensioned")
	}

	switch mtype {
	case LOOKUPMATRIX2D:
		runtimeCheck(len(sym.dims) == 2, "Matrix must be two dimensional")

	case LOOKUPMATRIXSQUARE:
		runtimeCheck(len(sym.dims) == 2 && sym.dims[0] == sym.dims[1],
			"Matrix must be square")
	}

	return sym
}

//
// Lookup a symbol, optionally checking for an illegal redimensioning
//

func lookupSymbol(token any, ndims int) *symtabNode {

	var sym *symtabNode
	var mapIdx int

	_, name := decodeVarToken(generateVarToken(token))

	if ndims != 0 {
		mapIdx = 1
	}

	sym = g.symtabMap[mapIdx][name]

	//
	// If the symbol is not present, or we just care about whether
	// it exists or not, 'ndims' will be -1, otherwise ensure that
	// the caller is not trying to change the dimensionality
	//

	runtimeCheck(sym == nil || ndims <= 0 || ndims == len(sym.dims),
		fmt.Sprintf("Attempt to change array dimensionality of %s", name))

	return sym
}

//
// Create the requested symbol.  The arrays are created by utility routines
// Complication: in BASIC, array subscripts run not from 1:N or 0:N-1,
// but from 0:N.  This means we cannot use int16 variables for slice
// operations, as the length of a matrix slice could be 32768
//

func createSymbol(token any, adims ...int16) *symtabNode {

	var dims []int16
	var sym *symtabNode
	var bounds [2]int
	var mapIdx int

	varType, name := decodeVarToken(generateVarToken(token))

	if len(adims) != 0 {
		dims = adims
		mapIdx = 1
	}

	basicAssert(g.symtabMap[mapIdx][name] == nil, "Symbol already defined")

	sym = &symtabNode{name: name}
	sym.dims = dims

	switch int16(len(dims)) {
	default:
		fatalError(fmt.Sprintf("Too many dimensions (%d)", len(dims)))

	case 0:
		bounds[0] = 1
		bounds[1] = 1

	case 1:
		bounds[0] = 1
		bounds[1] = int(dims[0]) + 1

	case 2:
		bounds[0] = int(dims[0]) + 1
		bounds[1] = int(dims[1]) + 1
	}

	switch varType {
	case FVAR:
		sym.vType = FVAR
		sym.value.f = createFloatArray(bounds)

	case IVAR:
		sym.vType = IVAR
		sym.value.i = createIntegerArray(bounds)

	case SVAR:
		sym.vType = SVAR
		sym.value.s = createStringArray(bounds)
	}

	g.symtabMap[mapIdx][name] = sym

	return sym
}

func processDimStmt(stmt *stmtNode) {

	for op := stmt.operands[0]; op != nil; op = op.next {
		var dims []int16

		num := len(op.operands)

		if num == 0 {
			fatalError("DIM variable with no dimensions!")
		}

		switch op.token {
		default:
			unexpectedTokenError(op.token)

		case FVAR, IVAR, SVAR:
			// NOP
		}

		dims = append(dims, int16(op.operands[0].tokenData.(int16)))

		if num == 2 {
			dims = append(dims, int16(op.operands[1].tokenData.(int16)))
		}

		//
		// Disallow duplicate DIM statements
		//

		if lookupSymbol(op, -1) != nil {
			runtimeErrorStmt("Duplicate DIM statement", stmt)
		} else {
			_ = createSymbol(op, dims...)
		}
	}

	checkArrayUsage(stmt, false)
}

//
// helper functions to fetch and store variables
//

func fetchFloatVar(sym *symtabNode, subs ...int16) float64 {

	sub1, sub2 := computeSubs(sym, subs)

	return sym.value.f[sub1][sub2]
}

func fetchIntVar(sym *symtabNode, subs ...int16) int16 {

	sub1, sub2 := computeSubs(sym, subs)

	return sym.value.i[sub1][sub2]
}

func fetchStringVar(sym *symtabNode, subs ...int16) string {

	sub1, sub2 := computeSubs(sym, subs)

	return sym.value.s[sub1][sub2]
}

func storeFloatVar(sym *symtabNode, val float64, subs ...int16) {

	sub1, sub2 := computeSubs(sym, subs)

	traceVar(sym.name, sub1, sub2, sym.value.f[sub1][sub2], val)

	sym.value.f[sub1][sub2] = val
}

func storeIntVar(sym *symtabNode, val int16, subs ...int16) {

	sub1, sub2 := computeSubs(sym, subs)

	traceVar(sym.name, sub1, sub2, sym.value.i[sub1][sub2], val)

	sym.value.i[sub1][sub2] = val
}

func storeStringVar(sym *symtabNode, val string, priv bool, subs ...int16) {

	//
	// If a variable is FIELD mapped, don't allow regular callers to
	// change the contents.  DEC allows this and documents that doing
	// so unmaps the variable, which would seem to silently corrupt
	// the field.  We pass a boolean to indicate a 'privileged' caller
	// (e.g. LSET, RSET or executeGet)
	//

	runtimeCheck(priv || sym.flde == nil, "Unable to modify mapped variable!")

	sub1, sub2 := computeSubs(sym, subs)

	traceVar(sym.name, sub1, sub2, sym.value.s[sub1][sub2], val)

	sym.value.s[sub1][sub2] = val
}

func traceVar(name string, sub1, sub2 int16, oval, nval any) {

	if g.traceVars || tracedVarsMap[name] {
		fmtStr := " changed from "

		fmt.Printf("Variable %s", name)

		if sub1 == 0 {
			if sub2 != 0 {
				fmt.Printf("(%d)", sub2)
			}
		} else {
			fmt.Printf("(%d,%d)", sub1, sub2)
		}

		if strings.HasSuffix(name, "$") {
			fmtStr += "%q to %q"
		} else if strings.HasSuffix(name, "%") {
			fmtStr += "%d to %d"
		} else {
			fmtStr += "%g to %g"
		}

		fmt.Printf(fmtStr, oval, nval)
		fmt.Println()
	}
}
