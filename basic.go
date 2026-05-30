package main

import (
	"bytes"
	"fmt"
	"github.com/danswartzendruber/avl"
	"github.com/goforj/godump"
	"golang.org/x/term"
	"math"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"strings"
	"syscall"
	"time"
)

//
// Tricky: init is called under the hood by the GO runtime when
// we fire up, so there are no visible calls to it!
//

func init() {

	initEnv()

	initHacks()

	initMaps()

	initErrors()

	initParser()
}

func main() {

	//
	// We need to close the Liner instances in reverse order, to make
	// sure we end up back in normal (cooked) terminal mode
	//

	defer func() {
		cleanupLiners()
	}()

	switch len(os.Args) {
	default:
		crash("Usage: basic-plus [program]")

	case 1:
		// nothing to do

	case 2:
		if fname, ok := validateProgramFilename(os.Args[1]); !ok {
			fmt.Println("Invalid filename!")
		} else {
			executeOld(fname)
		}
	}

	clearScreen()

	printVersionInfo()

	initAvl()

	//
	// Run the signal handling code in a goroutine
	//

	go sigHdlr()

	//
	// Loop forever, or until we quit
	//

	for !g.exiting {
		g.running = false
		parsingUneg = false
		parsingDef = false
		deferredStmtNo = 0

		call(parser)

		resetPrint(false)
	}
}

func initHacks() {

	//
	// Unfortunately, goyacc won't let us define token names with a
	// trailing '$' or '%', but some builtin functions do in fact have
	// trailing '$' (for example: chr$) or '%'.  We cope with this by
	// changing the token name string in the yyToknames array.
	// I'd prefer to fix up the name for the interpreter code only,
	// but then the parser will print out incorrect token names
	// (e.g. 'chr' instead of 'chr$')
	//

	for _, bif := range bifsHack {
		*getTokenNameAddr(bif.token) = bif.realName
	}
}

func initEnv() {

	checkTerminal()

	setupWindow()

	setupLiners()

	g.loginTime = time.Now()
}

//
// Read terminal geometry and set output zones
//

func setupWindow() {

	var err error

	g.window.rows, g.window.cols, err = term.GetSize(0)
	if err != nil {
		crash("Unable to read terminal parameters")
	}

	if g.window.rows < minWindowRows {
		crash("Terminal width must be >= 70 characters")
	}

	g.numOutputZones = g.window.rows / zoneWidth
}

func initParser() {

	yyDebug = 1
	yyErrorVerbose = false

	initSymbolTable()
}

func initAvl() {

	g.program = avl.NewAvlTree()
}

func initMaps() {

	isStringMap = make(map[int]bool)
	for i := range stringOps {
		isStringMap[stringOps[i]] = true
	}

	isNumericMap = make(map[int]bool)
	for i := range numericOps {
		isNumericMap[numericOps[i]] = true
	}

	//
	// Set up a map to map a string to a keyword token.  The low-level
	// lexer will identify keywords as floating variables.  We use the
	// aforementioned maps to correct the mis-lexing.  Make sure the
	// keywords are lower case.  This is unfortunately unavoidable, due
	// to the fact that we support long variable names, so it's impossible
	// for the lexer to tell if 'for' is a floating point variable, or a
	// BASIC keyword
	//

	keywordMap = make(map[string]int)

	for tok := yyFirsttok; tok <= yyLasttok; tok++ {
		lstr := strings.ToLower(getTokenName(tok))
		//		if len(lstr) == 1 {
		fmt.Printf("token %q is a keyword???\n", lstr)
		//		}
		keywordMap[lstr] = tok
	}

	errorMap = make(map[string]int16)
	errorMapRev = make(map[int16]string)

	tracedVarsMap = make(map[string]bool)

}

func writeGoroutineStacks() {

	name := "goroutines-stacks"
	mode := (os.O_CREATE | os.O_WRONLY)

	dumpFile, err := os.OpenFile(name, mode, 0644)
	if err != nil {
		iErr := err.(*os.PathError)
		fmt.Fprintf(os.Stderr, "Unable to open %s (%s)\n",
			name, iErr.Err.Error())
		return
	}

	_ = pprof.Lookup("goroutine").WriteTo(dumpFile, 2)

	m := fmt.Sprintf("Dumping goroutine stacks to %v and exiting", name)

	crash(m)
}

func sigHdlr() {

	ch := make(chan os.Signal, 1)

	signal.Ignore(syscall.SIGTSTP)

	signal.Notify(ch, syscall.SIGQUIT)
	signal.Notify(ch, syscall.SIGINT)
	signal.Notify(ch, syscall.SIGWINCH)

	for {
		sig := <-ch

		switch sig {

		default:
			crash(fmt.Sprintf("Unexpected signal %d", sig))

		case syscall.SIGWINCH:
			setupWindow()

		case syscall.SIGQUIT:
			writeGoroutineStacks() // does not return

		case syscall.SIGINT:
			g.interrupted = true
		}
	}
}

//
// This procedure is called by the panic deferred recovery function.
// It walks back the right number of frames to find the caller who
// caused the panic.  Four cases here: implicit calls to panic by the
// Go runtime code, a call to fatalError, a call to runtimeError or
// a crawlout exception (used solely to exit quietly to parse CLI).
// One confusing item: it seems impossible to cleanly find the caller
// of panic in the case of internal (Go runtime) generated calls,
// since there can be one or more support routines prior to that.
// Ugly: the best thing I've been able to come up with is to scan the
// call stack, looking for a function named 'runtime.gopanic', and
// picking the next non-runtime frame. For explicit calls to panic,
// we need the next frame past panic.  There may be a better way
// using debug/gosym, but I haven't (yet) figured that out
//

func decodePanic(e any) {

	var frame runtime.Frame
	var more bool
	var panicSeen bool
	var panicFrame runtime.Frame
	var panicCount int

	switch e := e.(type) {
	default:
		//
		// We got some kind of internally generated GO panic, so we have
		// to grovel for the code that panicked, not the caller of panic,
		// since that is somewhere inside GO.  Complication: if we get an
		// internally generated panic in the execute code, it will throw
		// another panic, so we need to keep track of the last panic frame
		//
		// Make sure we close the program file (if open) before proceeding,
		// lest we get multiple stack traces
		//

		closeProgramFile()

		pcs := make([]uintptr, 99) // XXX really?

		_ = pcs[:runtime.Callers(1, pcs)]

		frames := runtime.CallersFrames(pcs)

		for {
			frame, more = frames.Next()
			if !more {
				break
			}

			if frame.Function == "runtime.gopanic" {
				panicSeen = true
				panicCount++
			} else if panicSeen {
				if !strings.HasPrefix(frame.Function, "runtime.") {
					panicFrame = frame
					panicSeen = false
				}
			}
		}

		if panicCount == 0 { // impossible?
			crash("Unable to locate panic caller")
		}

		fmt.Printf("%s at %s line %d\n", e, filepath.Base(panicFrame.File),
			panicFrame.Line)

		debug.PrintStack()

	case *crawloutException:

		//
		// This is a dummy exception.  If a multiline user defined
		// function needs to abort (panic), we can't just pass along
		// the exception info when we call panic in userFunctionWrapper(),
		// as that could result in 2 stack traces - one from the actual
		// error in the goroutine, and the other a bogus one in the
		// main goroutine.  We avoid this by having userFunctionWrapper
		// forward a dummy exception structure address, which we
		// dutifully ignore.  This is also triggered by exitToPrompt().
		// We nuke the current execution state to avoid an attempt to
		// continue if requested
		//

		if !e.continuable {
			r.curStmt = nil
		}

		r.fip = nil

	case *basicErrorInfo:
		fmt.Printf("%q at %s line %d\n", e.msg, filepath.Base(e.file), e.line)

		r.curStmt = nil
		r.fip = nil

		debug.PrintStack()

	case *runtimeErrorInfo:
		re := processFault(e)
		sp := re.fip.state.stmt

		//
		// Special-case the EINTERRUPTED case.  This is not actually
		// an error, but we need to abort whatever was running, and
		// return to command level
		//

		if re.msg == EINTERRUPTED {
			msg := EINTERRUPTED + " at line " + decodeStmtNoString(r.curStmt)
			fmt.Println(msg)
			return
		} else if sp != nil {
			printErrorLocStmt(sp, re.msg)
		} else {
			fmt.Println(re.msg)
		}

		if g.running {
			r.curStmt = nil
			r.fip = nil
		}

		if g.traceStack {
			debug.PrintStack()
		}

		printStatistics()
	}
}

func processFault(e any) *runtimeErrorInfo {

	re := e.(*runtimeErrorInfo)

	r.fip = re.fip

	return re
}

//
// Wrapper routine for a function.  We need this so that panic calls
// can be caught and decoded before returning to our caller
//

func call(f func()) {

	defer func() {
		err := recover()
		if err != nil {
			decodePanic(err)
		}
	}()

	f()
}

//
// This function checks if 2 floating point numbers are effectively
// equal.  What this means: due to the limitations of output formats,
// it's possible to have 2 floating point numbers that are different
// in the Nth bit, but look the same when displayed. The easiest way
// to do this is to convert them to a PRINT style string, and compare
// the two strings
//

func floatValuesApproxEqual(f1, f2 float64) bool {

	return basicFormat(f1) == basicFormat(f2)
}

func floatingError(val float64) bool {

	if math.IsNaN(val) || math.IsInf(val, 0) {
		return true
	} else {
		//
		// Reject denorm values?
		//
		exp := (math.Float64bits(val) & 0x7ff0000000000000) >> 52
		if val != 0 && exp == 0 && !g.denorm {
			return true
		}
	}

	return false
}

//
// This function is called after one of the 5 numeric binary operators
// (PLUS, MINUS, STAR, SLASH and POW).  It pops the top of the RPN stack,
// checks for Inf or Nan, and if so, calls arithFault, else pushes the
// original number back on the stack.  Whether arithFault throws a fault
// or not, either way, we end up with 0.0 as the top of the RPN stack
// for error recovery
//

func checkFloatingStatus(state *procState) {

	val := rpnPopFloat(&state.stack)

	if floatingError(val) {
		arithFault(EFLOATINGERROR, state, float64(0.0))
	} else {
		rpnPush(&state.stack, val)
	}
}

//
// This function needs to provide more information in the faultInfo
// structure, to allow restart/continuation.  It also needs to push
// a 'zero' of the appropriate type, passed by the caller
//

func arithFault(msg string, state *procState, zeroVal any) {

	rpnPush(&state.stack, zeroVal)

	state.stmt = r.curStmt

	if r.onErrorStmtNo == 0 {
		printErrorLocStmt(r.curStmt, msg)
	} else {
		runtimeErrorInternal(msg, state, getErrorNo(msg))
	}
}

//
// This function prints the line that was executing at the time
// runtimeError was called (if any).  If there are multiple
// statements on the line, it will underline the offending one.
// Make sure to pass false for the doPanic argument :)
//
// This function is also called while tracing execution
//

func printErrorLocStmt(stmt *stmtNode, msg string) {

	if stmt == nil || msg == EINTERRUPTED {
		errorLocFull("", msg, false)
	} else {
		errorLocFull(stmt.line, msg, false, &stmt.tokenLoc)
	}
}

//
// A couple of handy 'assert' functions
//

func basicAssert(chk bool, msg string) {

	if g.checkAsserts && !chk {
		fatalError(msg)
	}
}

func runtimeCheck(chk bool, msg string) {

	if !chk {
		runtimeError(msg)
	}
}

//
// The standard BASIC-PLUS error messages are simple strings,
// and I don't want to mess with that.  On the other hand, there
// are places where we can be more informative (file errors for
// example).  Nothing that comes in here is going to be continuable,
// except EINTERRUPTED.  Arithmetic faults are handled by arithFault,
// which ends up calling runtimeErrorInternal.  We do need to special
// case EINTERRUPTED though
//

func runtimeError(msg string) {

	runtimeErrorInternal(msg, createExecutionState(r.curStmt), getErrorNo(msg))
}

func runtimeErrorStmt(f string, stmt *stmtNode, args ...any) {

	//
	// Bit of a hack here.  Callers of runtimeError() may want to
	// pass in the *stmtNode that they are complaining about.
	// Normally, during execution, r.curStmt is the offending *stmtNode;
	// but while checking DIM, DATA and DEF statements, we are scanning
	// the program tree, and r.curStmt is not valid, so those callers
	// pass in the *stmtNode to diagnose.
	// In those contexts, there is no numeric error code, nor is the
	// exception continuable
	//

	msg := fmt.Sprintf(f, args...)

	runtimeErrorInternal(msg, createExecutionState(stmt), -1)
}

func runtimeErrorInternal(msg string, state *procState, err int16) {

	runtime.GC()

	//
	// Do not allow CONT if user program caught an exception
	// but did not RESUME, then caused another exception
	//

	if r.fip != nil {
		err = -1
	}

	fip := &faultInfo{state: state, err: err}

	panic(&runtimeErrorInfo{msg: strings.TrimSuffix(msg, "\n"), fip: fip})
}

//
// Runtime errors raised by the interpreter itself.  Almost always
// due to a basicAssertion failure, subscript range error, etc...
// We find filename and line number of our caller, and stuff those
// into the basicErrorInfo structure before calling panic
//

func fatalError(msg string) {

	//
	// Make sure we close the program file (if open) before proceeding,
	// lest we get multiple stack traces
	//

	closeProgramFile()

	_, file, line, ok := runtime.Caller(2)
	if !ok {
		crash("Unable to find caller frame!\n")
	}

	msg = strings.TrimRight(msg, "\n")

	m := &basicErrorInfo{msg, file, line}

	panic(m)
}

//
// Wrapper for the parser generated by goyacc
//

func parser() {

	g.yylex = NewLexer()

	basicAssert(g.yylex != nil, "NewLexer botch!")

	basicAssert(yyParse(g.yylex) == 0, "yyParse botch!")
}

func makeStmtNode(token int, operands ...*tokenNode) *stmtNode {

	node := &stmtNode{token: token, line: g.yylex.line, operands: operands}

	if g.traceDump {
		godump.Dump(node)
	}

	return node
}

//
// Helper functions to simplify parser rules.  We really could replace
// NRPN and SRPN with, say, RPN.  We go with 2 discrete tokens, since
// these can be inserted into the numericOps and stringOps, so the
// parser action rules can detect string/numeric mismatches and print
// a more useful message than 'syntax error' :)
//

func makeNrpnTokenNode(tnode *tokenNode) *tokenNode {

	return makeTokenNode(NRPN, createRpnExprInternal(tnode))
}

func makeSrpnTokenNode(tnode *tokenNode) *tokenNode {

	return makeTokenNode(SRPN, createRpnExprInternal(tnode))
}

func makeTokenNode(token int, operands ...any) *tokenNode {

	node := &tokenNode{token: token}

	//
	// We can have 0 or more operands here. If 0, there's nothing
	// to do.  If 1, it's the only token node or a primitive data type.
	// Else all N tokens are token node pointers.
	// This implies that if we didn't pass in a primitive type as
	// the single operand, the tokenData field in the node will be nil
	//

	switch len(operands) {
	case 0:
		// NOP

	case 1:
		switch operands[0].(type) {
		default:
			node.tokenData = operands[0]

		case *tokenNode:
			node.operands = append(node.operands, operands[0].(*tokenNode))
		}

	default:
		for i := range operands {
			node.operands = append(node.operands, operands[i].(*tokenNode))
		}
	}

	if g.traceDump {
		godump.Dump(node)
	}

	return node
}

func cmpInt16Key(key any, node any) int {

	return cmpInt16Items(key.(int16), node.(*stmtNode).stmtNo)
}

func cmpInt16Snode(node1, node2 any) int {

	return cmpInt16Items(node1.(*stmtNode).stmtNo, node2.(*stmtNode).stmtNo)
}

func cmpInt16Items(item1, item2 int16) int {

	if item1 < item2 {
		return -1
	} else if item1 > item2 {
		return 1
	} else {
		return 0
	}
}

func saveProgram(file *file) {

	fname := file.filename

	for stmt := stmtAvlTreeFirstInOrder(); stmt != nil; {
		if _, err := file.writer.WriteString(stmt.line + "\n"); err != nil {
			iErr := err.(*os.PathError)
			runtimeError(fmt.Sprintf("Unable to save %q (%v)", fname, iErr))
		}

		stmt = stmtAvlTreeNextInOrder(stmt)
	}

	err := file.writer.Flush()
	if err != nil {
		iErr := err.(*os.PathError)
		runtimeError(fmt.Sprintf("Unable to save %q (%v)", fname, iErr))
	}
}

func processStmtNode(stmtNo int16, delete bool) {

	processStmtRange(stmtNo, stmtNo, delete)
}

func processStmtRange(firstStmt, lastStmt int16, delete bool) {

	var nextStmt *stmtNode

	for stmt := stmtAvlTreeFirstInOrder(); stmt != nil; stmt = nextStmt {
		nextStmt = stmtAvlTreeNextInOrder(stmt)

		if stmt.stmtNo < firstStmt {
			continue
		} else if stmt.stmtNo > lastStmt {
			break
		}

		if delete {
			stmtAvlTreeRemove(stmt)
		} else {
			fmt.Println(stmt.line)
		}
	}
}

func insertStmtNode(snode *stmtNode, stmtNo int16) {

	//
	// Look for this statement in the statement tree.  If we
	// find it, delete it
	//

	stmt := stmtAvlTreeLookup(stmtNo, cmpInt16Key)
	if stmt != nil {
		stmtAvlTreeRemove(stmt)
	}

	//
	// Set the stmtNo field for this statement node, and give it
	// a copy of the current line
	//

	snode.stmtNo = stmtNo
	snode.line = strings.Clone(g.yylex.line)

	//
	// Walk through any statement nodes chained off of this head
	// node, setting their head pointer to point back to us.
	// We need this so as to be able to look up the next numbered
	// statement in this program, if we have just executed the last
	// statement in a chain
	//

	for stmt = snode.next; stmt != nil; stmt = stmt.next {
		stmt.head = snode
	}

	// And finally, add it to the tree

	stmtAvlTreeInsert(snode, cmpInt16Snode)
}

//
// Helper functions for the parser to call.  They enforce various
// syntatic and/or semantic requirements, and may be passed token
// location information so as to be able to flag the offending
// invalid name
//

func requireImmediateStatement(token int, yyloc *yySymLoc) {

	if deferredStmtNo != 0 {
		msg := fmt.Sprintf("%s is only valid in immediate mode",
			getTokenName(token))
		errorLoc(msg, yyloc)
	}
}

func requireDeferredStatement(token int, yyloc *yySymLoc) {

	if deferredStmtNo == 0 {
		msg := fmt.Sprintf("%s is not valid in immediate mode",
			getTokenName(token))
		errorLoc(msg, yyloc)
	}
}

func requireIntegerOperand(node *tokenNode, yyloc *yySymLoc) {

	if expressionType(node) != INTEGER {
		errorLoc("Integer operand expected", yyloc)
	}
}

func requireNumericOperand(node *tokenNode, yyloc *yySymLoc) {

	if !isNumeric(node) {
		errorLoc("Numeric operand expected", yyloc)
	}
}

func requireStringOperand(node *tokenNode, yyloc *yySymLoc) {

	if !isString(node) {
		errorLoc("String operand expected", yyloc)
	}
}

//
// This function is called by the parser to ensure that the left
// and right operands of an operator are of compatible types.
// e.g. they are both string or numeric.  A side effect of this
// is that a numeric operator token (returned by the lexer) will
// be morphed into a string operator token if LHS and RHS are both
// string operands.  e.g. PLUS will morph into CONCAT, EQ will morph
// into STREQ, etc...
//

func requireCompatibleOperands(onode int, lnode, rnode *tokenNode,
	yyloc1 *yySymLoc, yyloc2 *yySymLoc) (ret int) {

	ret = onode

	lNumeric := isNumeric(lnode)
	rNumeric := isNumeric(rnode)

	//
	// The left and right operands must match. If this is not the case,
	// throw an exception
	//

	if lNumeric != rNumeric {
		errorLoc("Incompatible operands", yyloc1, yyloc2)
	}

	//
	// If both are numeric, we will return the operator token unchanged,
	// else we will map it to the equivalent non-numeric operator
	//

	if lNumeric {
		return
	}

	switch onode {
	case PLUS:
		ret = CONCAT

	case EQ:
		ret = STREQ

	case NE:
		ret = STRNE

	case LT:
		ret = STRLT

	case LE:
		ret = STRLE

	case GT:
		ret = STRGT

	case GE:
		ret = STRGE

	default:
		// nothing to do
	}

	return
}

//
// This function will take a list of numeric operands and ensure that
// they are all either integer or float, depending on the type the caller
// passes in to it.  This to to disallow things like the following:
// 'for i = 100 to 200% step 3', which is apparently legal, but really
// stupid, and likely to cause the program to fail in odd ways, due to
// integer overflow, rounding errors, etc...
// All operands of a 'for' statement must have the same numeric type
// as the loop variable.  We pass in pairs of token nodes and their
// corresponding token locations, to facilitate generating useful
// diagnostics
//
// Complication: any of the 2 or 3 elements involved can be expressions.
// This makes it non-trivial to diagnose a BASIC-PLUS statement such as
// '100 for i = 1 to 100/3', for example.  We call a helper function which
// will walk each operand tree, and return INTEGER or FLOAT.  That function
// will apply normal mixed mode rules.  We already know that all of the
// operands are numeric due to a previous parser check, so things like
// builtin functions can be assumed to be numeric.  According to the
// BASIC-PLUS manual, there is only one builtin that returns an explictly
// INTEGER result, SWAP%.  Any others are assumed to be FLOAT
//

func requireCompatibleNumericOperands(op *tokenNode, operands ...any) {

	var opType int
	var opStr string

	basicAssert(len(operands)%2 == 0, "odd number of operands")

	switch op.token {
	default:
		unexpectedTokenError(op.token)

	case IVAR:
		opType = INTEGER
		opStr = "integer"

	case FVAR:
		opType = FLOAT
		opStr = "float"
	}

	for i := 0; i < len(operands); i += 2 {
		if opType != expressionType(operands[i].(*tokenNode)) {
			errorLoc("FOR operand must be "+opStr, operands[i+1].(*yySymLoc))
			break
		}
	}
}

//
// This function walks an operand tree and returns INTEGER or FLOAT
// (see comments in requireCompatibleNumericOperands).
// We really should enumerate all of the builtin functions here, but
// that's a PITA, and not really necessary, as the parser won't have
// allowed anything bogus here.  Since the data type of builtins is
// predefined, we needn't walk their operands.  Builtin functions
// have predefined types, so there is no point in walking their
// call arguments, even if present
//

func expressionType(tnode *tokenNode) int {

	var lOpType, rOpType int

	switch tnode.token {
	default:
		// handled after the switch

	case FLOAT, FVAR, FNFVAR:
		return FLOAT

	case INTEGER, IVAR, FNIVAR:
		return INTEGER

		//
		// Numeric operators returning INTEGER
		//

	case AND, APPROX, EQ, EQV, GE, GT, IMP, LE, LT, NE, NOT, OR, XOR:
		return INTEGER

		//
		// String operators returning INTEGER
		//

	case STREQ, STRNE, STRGE, STRGT, STRLE, STRLT:
		return INTEGER

		//
		// Builtins returning INTEGER
		//

	case ASCII, CVTSI, ERR, ERL, LEN, SWAPI:
		return INTEGER
	}

	//
	// Anything at this point is either a numeric operator or
	// a builtin returning FLOAT
	//

	switch len(tnode.operands) {
	default:
		fatalError(fmt.Sprintf("Invalid number of operands (%d)",
			len(tnode.operands)))

	case 0, 1:
		return FLOAT

	case 2:
		lOpType = expressionType(tnode.operands[0])
		rOpType = expressionType(tnode.operands[1])
	}

	if lOpType == rOpType {
		return lOpType
	} else {
		return FLOAT
	}
}

//
// Complication: an array reference will have a SUBSCR node with the
// LHS being a FVAR, IVAR or SVAR.  If we see that, we need to peek
// at the LHS for the type.  Same goes for isString()
//

func isNumeric(node *tokenNode) bool {

	lhs := node

	if lhs.token == SUBSCR {
		lhs = lhs.operands[0]
	}

	return isNumericMap[lhs.token]
}

func isString(node *tokenNode) bool {

	lhs := node

	if lhs.token == SUBSCR {
		lhs = lhs.operands[0]
	}

	return isStringMap[lhs.token]
}

func isInt(value any) bool {

	switch value := value.(type) {
	default:
		unexpectedTypeError(value)

	case lhsRetVal:
		if value.sym.vType == IVAR {
			return true
		} else {
			return false
		}

	case *int16, int16, ivarToken:
		return true

	case *float64, float64, fvarToken:
		return false
	}

	panic(nil) // avoid compiler complaint
}

func fetchOperands(curStmt *stmtNode) []*tokenNode {

	ret := make([]*tokenNode, 0)

	for i := 0; i < len(curStmt.operands); i++ {
		basicAssert(curStmt.operands[i] != nil,
			fmt.Sprintf("nil operand[%d]", i))
		ret = append(ret, curStmt.operands[i])
	}

	return ret
}

func unexpectedTokenError(token int) {

	fatalError(fmt.Sprintf("Unexpected token %s", getTokenName(token)))
}

func unexpectedTypeError(item any) {

	fatalError(fmt.Sprintf("Unexpected type %T", item))
}

func checkSubscript(sub int16, maxSub int16) {

	runtimeCheck(sub >= 0 && sub <= maxSub, ESUBSCRIPTERROR)
}

func checkInt16(msg string, n, low int64, yyloc *yySymLoc) {

	if (n < low) || (n > math.MaxInt16) {
		errorLoc(msg, yyloc)
	}
}

//
// Ensure that the string passed in is no longer than the specified
// maximum.  We only call this from evaluateRpnExpr().  It is possible
// for intermediate results in that function to be too long, but
// evaluateRpnExpr() will definitely call us before returning, so the
// user will never see a string that is 'too long'
//

func checkStringLen(s string) {

	runtimeCheck(len(s) <= maxStringLen,
		fmt.Sprintf("Maximum string length (%d) exceeded", maxStringLen))
}

func checkStringIndex(s string, indx int16) {

	sLen := int16(len(s))

	runtimeCheck(indx >= 1,
		fmt.Sprintf("string index (%d) too small", indx))
	runtimeCheck(indx <= sLen,
		fmt.Sprintf("string index (%d) too large", indx))
}

func printStatistics() {

	var mem runtime.MemStats

	if g.printStats {
		fmt.Println()
		printCpuUsage()
		runtime.GC()
		runtime.ReadMemStats(&mem)
		fmt.Printf("%dMB memory used\n", convertToMB(mem.HeapAlloc))
		fmt.Printf("%d %s executed\n", s.numStatements,
			pluralize("statement", s.numStatements))
	}
}

func resetStatistics() {
	s.utime = 0
	s.stime = 0
	s.numStatements = 0
}

func setModified() {

	g.modified = true
}

func clearModified() {

	g.modified = false
}

func checkModified() {

	if g.modified {
		if !promptYesNo("Discard modified program") {
			exitToPrompt("Please save the current program first")
		}
	}
}

func printVersionInfo() {

	fmt.Printf("BASIC-PLUS clone version %s - built %s\n",
		VERSION, buildTimestampStr)
}

func executeConfig() {

	fmt.Printf("%s\n", floatingPointMode)
	fmt.Printf("%d MB DIM space\n", convertToMB(maxArrayMemory))
	if maxVariableLen > 2 {
		fmt.Printf("Long variable names\n")
	}
	fmt.Printf("%d output zones\n", g.numOutputZones)
	printDenormState()
}

//
// Process declaration statements.  While not technically illegal,
// it doesn't make a lot of sense to allow DATA or DIM statements
// inside a multiline function definition, so throw an error if we
// see one in that context
//

func processDeclarations() {

	var defStmt *stmtNode
	var fname string

	r.userDefMap = make(map[string]*stmtNode)
	r.fieldMap = make(map[int]*field)

	for stmt := stmtAvlTreeFirstInOrder(); stmt != nil; stmt = stmtAvlTreeNextInOrder(stmt) {

		switch stmt.token {
		default:
			// nothing to do

		case DATA:
			if defStmt != nil {
				runtimeErrorStmt("DATA statement not allowed here", stmt)
			}

			processDataStmt(stmt)

		case DEF:
			//
			// if there is no expression operand, this is a multiline
			// function, so defer adding to the table until we find the
			// matching FNEND.  For a single line function, we're done.
			// Either way, add the function name to the map
			//

			if defStmt != nil {
				runtimeErrorStmt("Nested DEF functions not allowed", stmt)
			}

			fname = getVarName(stmt.operands[0])
			if r.userDefMap[fname] != nil {
				runtimeErrorStmt("Duplicate DEF statement", stmt)
			} else {
				r.userDefMap[fname] = stmt
			}

			if stmt.operands[1] == nil {
				defStmt = stmt
			}

		case DIM:
			if defStmt != nil {
				runtimeErrorStmt("DIM statement not allowed here", stmt)
			}

			processDimStmt(stmt)

		case FNEND:
			if defStmt == nil {
				runtimeErrorStmt("Matching DEF not found", stmt)
			}

			//
			// This FNEND must match the current multiline function,
			// so allocate and initialize the userDefNode entry for
			// it and finish up
			//

			udre := userDefNode{fname: fname, firstStmt: defStmt,
				lastStmt: stmt}
			r.userDefList = append(r.userDefList, udre)

			defStmt = nil
		}
	}

	if defStmt != nil {
		runtimeErrorStmt("Matching FNEND not found", defStmt)
	}
}

//
// If we are leaving from inside a FOR loop, if we're not executing
// a GOSUB, pop FOR nodes as needed.  If it is a GOSUB, reject it,
// as it not feasible to keep track (ex: we do a GOSUB from inside
// the loop, and that code then does one or more transfers of control
// before returning to the loop - note that the DEC implementation
// tries to handle this but can't - it doesn't print an error, just
// fails strangely
//

func checkForExit(targetStmtNo int16, exitFor bool) {

	curStmtNo := fetchStmtNo(r.curStmt)

	for i, fsp := range r.forStack {
		forStmtNo := fetchStmtNo(fsp.stmt)
		nextStmtNo := fetchStmtNo(fsp.nextStmt)
		if curStmtNo >= forStmtNo && curStmtNo <= nextStmtNo {
			if targetStmtNo < forStmtNo ||
				targetStmtNo > nextStmtNo {
				if exitFor {
					popForStackEntry(i)
					return
				}
			}
		}
	}
}

//
// Check to ensure we are not entering or exiting a multiline
// user defined function
//

func checkStmtTargetScope(targetStmtNo int16) {

	var fromIdx int

	if r.curStmt.stmtNo == 0 {
		fromIdx = lookupStmtInUserFunctionList(r.curStmt.head.stmtNo)
	} else {
		fromIdx = lookupStmtInUserFunctionList(r.curStmt.stmtNo)
	}

	toIdx := lookupStmtInUserFunctionList(targetStmtNo)

	//
	// The following is tricky.  If toIdx != fromIdx the transfer of
	// control is NOT inside the same scope.  If fromIdx is >= 0,
	// we are jumping out of a multiline function.  Doesn't matter
	// if it's into another function or the global scope.  If fromIdx
	// is < 0, we are jumping into a multiline function.  We only care
	// about the distinction for the purposes of printing a clear message
	//

	if toIdx != fromIdx {
		if fromIdx >= 0 {
			runtimeError("Invalid transfer out of user defined function")
		} else {
			runtimeError("Invalid transfer into user defined function")
		}
	}
}

//
// If we have N multiline user-defined functions, the list will be
// numbered from 0 to N-1.  This implies that statements NOT in any
// multiline function have an index of -1
//

func lookupStmtInUserFunctionList(stmtNo int16) int {

	for idx, udre := range r.userDefList {
		if stmtNo >= udre.firstStmt.stmtNo && stmtNo <= udre.lastStmt.stmtNo {
			return idx
		}
	}

	return -1
}

func processDataStmt(stmt *stmtNode) {

	basicAssert(len(stmt.operands) == 1,
		fmt.Sprintf("numOperands != 1 (%d)", len(stmt.operands)))

	for tp := stmt.operands[0]; tp != nil; tp = tp.next {
		switch tp.token {
		default:
			unexpectedTokenError(tp.token)

		case INTEGER, EINTEGER, FLOAT, STRING:
		}

		r.dataList = append(r.dataList, tp.tokenData)
	}

}

//
// This function takes a singly-linked tokenNode list and
// converts it to a slice
//

func createTokenNodeSlice(tp *tokenNode) []*tokenNode {

	var np *tokenNode
	ret := make([]*tokenNode, 0)

	for p := tp; p != nil; p = np {
		ret = append(ret, p)
		np = p.next
		p.next = nil
	}

	return ret
}

//
// This function takes a token node tree and returns a postfix (RPN)
// format list hung off of an NRPN or SRPN node
//

func createRpnExpr(tp *tokenNode) *tokenNode {

	var rp *tokenNode

	if isNumeric(tp) {
		rp = makeNrpnTokenNode(tp)
	} else if isString(tp) {
		rp = makeSrpnTokenNode(tp)
	} else {
		fatalError(fmt.Sprintf("%s is neither numeric nor string",
			getTokenName(tp.token)))
	}

	if g.traceDump {
		godump.Dump(rp)
	}

	return rp
}

//
// This function walks a token node tree.  Whenever it finds SUBSCR,
// it fetches the symbol name from the left operand, and searches for
// it in the list of formal parameter names passed by the caller.
// If there is a match, we throw an error
//

func checkDefExpr(params []*tokenNode, expr *tokenNode) {

	for i := range expr.operands {
		checkDefExpr(params, expr.operands[i])
	}

	if expr.token == SUBSCR {
		exprName := getVarName(expr.operands[0])

		for _, param := range params {
			pName := getVarName(param)
			if exprName == pName {
				m := fmt.Sprintf("Invalid subscripted reference to %q", pName)
				errorLoc(m)
			}
		}
	}
}

//
// This function takes a stmtNode and return a string representation
// of the statement number.  This handles the fact that if we have
// multiple statements on a line, only the first one has a non-zero
// stmtNo field.  Subsequent nodes point back to the head, so look there

func decodeStmtNoString(stmt *stmtNode) string {

	return fmt.Sprintf("%d", fetchStmtNo(stmt))
}

func fetchStmtNoFromFip(fip *faultInfo) int16 {

	if fip != nil && fip.state != nil && fip.state.stmt != nil {
		return fetchStmtNo(fip.state.stmt)
	} else {
		return 0
	}
}

func fetchStmtNo(stmt *stmtNode) int16 {

	if stmt.head == nil {
		return stmt.stmtNo
	} else {
		return stmt.head.stmtNo
	}
}

//
// This routine accepts two tokenList parameters, appends the second
// to the first and returns the result.  If the first tokenList is
// nil, just return the second one
//

func appendTokenList(tla, tlb tokenList) tokenList {

	var ret tokenList

	if tla == nil {
		ret = tlb
	} else {
		ret = append(tla, tlb...)
	}

	return ret
}

func createRpnExprInternal(tnode *tokenNode) tokenList {

	var tl tokenList

	for _, op := range tnode.operands {
		tl = appendTokenList(tl, createRpnExprInternal(op))
	}

	//
	// SUBSCR and INTPAIR are handled specially.  Because the resulting
	// list is in postfix order, when the expression processor encounters
	// SUBSCR, it cannot know if there are 1 or 2 subscripts.  We handle
	// that as follows: if we see SUBSCR, we emit SUBSCR1.  If we see
	// INTPAIR, we emit SUBSCR2.  The INTPAIR will have already been seen
	// and appended in the default case
	//

	switch tnode.token {
	default:
		tl = append(tl, tnode.token)

	case SUBSCR:
		lidx := len(tl) - 1
		if tl[lidx] == INTPAIR {
			tl[lidx] = SUBSCR2
		} else {
			tl = append(tl, SUBSCR1)
		}

	case FNFVAR:
		tl = append(tl, fnfvarToken(tnode.tokenData.(string)))

	case FNIVAR:
		tl = append(tl, fnivarToken(tnode.tokenData.(string)))

	case FNSVAR:
		tl = append(tl, fnsvarToken(tnode.tokenData.(string)))

	case FVAR:
		tl = append(tl, fvarToken(tnode.tokenData.(string)))

	case IVAR:
		tl = append(tl, ivarToken(tnode.tokenData.(string)))

	case SVAR:
		tl = append(tl, svarToken(tnode.tokenData.(string)))

	case FLOAT:
		tl = append(tl, tnode.tokenData.(float64))

	case INTEGER:
		tl = append(tl, tnode.tokenData.(int16))

	case STRING:
		tl = append(tl, tnode.tokenData.(string))

	case NRPN, SRPN:
		unexpectedTokenError(tnode.token)
	}

	return tl
}

func decodeRpnItem(item any) string { // nolint:unused

	switch item := item.(type) {
	default:
		unexpectedTypeError(item)

	case fnfvarToken:
		return fmt.Sprintf("FNFVAR %s", getVarName(item))

	case fnivarToken:
		return fmt.Sprintf("FNIVAR %s", getVarName(item))

	case fnsvarToken:
		return fmt.Sprintf("FNSVAR %s", getVarName(item))

	case fvarToken:
		return fmt.Sprintf("FVAR %s", getVarName(item))

	case ivarToken:
		return fmt.Sprintf("IVAR %s", getVarName(item))

	case svarToken:
		return fmt.Sprintf("SVAR %s", getVarName(item))

	case float64:
		return fmt.Sprintf("FLOAT %g", item)

	case int16:
		return fmt.Sprintf("INT16 %d", item)

	case int:
		return fmt.Sprintf("OP %s", getTokenName(item))

	case string:
		return fmt.Sprintf("STRING %q", item)
	}

	panic(nil) // avoid compiler complaint
}

func printRpnStack(stackp *rpnStack) { // nolint:unused

	if len(stackp.entries) == 0 {
		fmt.Println("Stack is empty")
		return
	}

	for i, item := range stackp.entries {
		fmt.Print("<")

		switch item := item.(type) {
		default:
			fmt.Printf("%v", item)

		case string:
			fmt.Printf("%q", item)

		case svarToken:
			fmt.Printf("%q", getVarName(item))
		}

		fmt.Printf(" (%T)>", item)

		if i != len(stackp.entries)-1 {
			fmt.Printf(" ")
		}
	}

	fmt.Println()
}

func rpnPush(stackp *rpnStack, value any) {

	stackp.entries = append(stackp.entries, value)
}

func rpnPushString(stackp *rpnStack, str string) {

	//
	// Ensure the resulting string has a sane length.  The documention
	// says 'limited only by core', so we allow a reasonable but bounded
	// limit (32767) This *should* only be possible for the CONCAT
	// operator or space$ builtin.  This also allows us to use int16 value
	// for string indices.  In point of fact, the manual's description of
	// BASIC-PLUS strings specifically gives a limit of 32767 characters
	//

	checkStringLen(str)

	rpnPush(stackp, str)
}

func rpnPop(stackp *rpnStack) any {

	slen := len(stackp.entries)
	if slen == 0 {
		fatalError("RPN stack underflow")
	}

	value := stackp.entries[slen-1]

	stackp.entries = stackp.entries[:slen-1]

	return value
}

//
// This function pops a symbol reference from the stack
//

func rpnPopSymbol(stackp *rpnStack) any {

	ret := rpnPop(stackp)

	switch ret.(type) {
	default:
		unexpectedTypeError(ret)

	case fnfvarToken, fnivarToken, fnsvarToken, fvarToken, ivarToken, svarToken:
	}

	return ret
}

//
// This function pops a value from the stack and returns a string
// Pop a value off the stack.
// If it's a string, we're done.
// Otherwise throw an error.
//

func rpnPopString(stackp *rpnStack) string {

	var str string

	val := rpnPopValue(stackp)
	str, ok := val.(string)
	if !ok {
		unexpectedTypeError(val)
	}

	return str
}

//
// This function pops a value from the stack and returns a float64
// Pop a value off the stack.
// If it's a float64, we're done.
// If it's an int16, convert to float64.
// Otherwise throw an exception.
//

func rpnPopFloat(stackp *rpnStack) float64 {

	var f float64

	val := rpnPopValue(stackp)
	switch val := val.(type) {
	default:
		unexpectedTypeError(val)

	case float64:
		f = val

	case int16:
		f = float64(val)
	}

	return f
}

//
// Pop a value from the stack and return a boolean
//

func rpnPopBool(stackp *rpnStack) bool {

	b := rpnPopInt16(stackp)
	if b != 0 {
		return true
	} else {
		return false
	}
}

//
// This function pops a value from the stack and returns an int16
// Pop a value off the stack.
// If it's an int16, we're done.
// If it's a float64, convert to int16.
// Otherwise throw an error.
//

func rpnPopInt16(stackp *rpnStack) int16 {

	var i int16

	val := rpnPopValue(stackp)
	switch val := val.(type) {
	default:
		unexpectedTypeError(val)

	case float64:
		i = floatToInt16(val)

	case int16:
		i = val
	}

	return i
}

//
// This function pops a value from the stack and returns an int
// Pop a value off the stack.
// If it's an int16, convert to int.
// If it's a float64, convert to int.
// Otherwise throw an error.
//

func rpnPopInt(stackp *rpnStack) int {

	return anyToInt(rpnPopValue(stackp))
}

//
// Peek at the RPN stack top and return a boolean indicating whether
// it is numeric or string
//

func rpnStackTopNumeric(stackp *rpnStack) bool {

	topToken := stackp.entries[len(stackp.entries)-1]
	switch topToken.(type) {
	default:
		unexpectedTypeError(topToken)

	case ivarToken, int16, fvarToken, float64:
		return true

	case string, svarToken:
		return false
	}

	panic(nil) // avoid compiler complaint
}

//
// Pop a single number off the RPN stack.  Return the numeric item,
// as well as a boolean indicating integer or not
//

func rpnPopNumber(stackp *rpnStack) (any, bool) {

	e := rpnPopValue(stackp)
	switch e.(type) {
	default:
		unexpectedTypeError(e)

	case float64:
		return e, false

	case int16:
		return e, true
	}

	panic(nil) // avoid compiler complaint
}

//
// Pop two values off the RPN stack.  If they are both numeric,
// do the appropriate mixed-mode conversion.  If either operand
// is not a numeric type (should not happen), isInt will throw
// an exception
//

func rpnPopTwoNumbers(stackp *rpnStack) (ret1, ret2 any) {

	ret2 = rpnPopValue(stackp)
	ret1 = rpnPopValue(stackp)

	if isInt(ret1) {
		if !isInt(ret2) {
			ret1 = float64(ret1.(int16))
		}
	} else {
		if isInt(ret2) {
			ret2 = float64(ret2.(int16))
		}
	}

	return
}

//
// This function pops two strings off the RPN stack
//

func rpnPopTwoStrings(stackp *rpnStack) (ret1, ret2 string) {

	ret2 = rpnPopString(stackp)
	ret1 = rpnPopString(stackp)

	return
}

//
// Pop a value off the RPN stack.  If it's a literal (numeric or string)
// just return it.  If it's a symbol, look up the current value and return
// it unless it matches a formal parameter at the top of the user function
// stack, in which case we return the actual argument value
//

func rpnPopValue(stackp *rpnStack) any {

	item := rpnPop(stackp)

	switch item.(type) {
	default:
		unexpectedTypeError(item)

	case float64, int16, string:
		return item

	case fvarToken, ivarToken, svarToken:

		// if this is a formal parameter, return its value

		argVal := getParamValue(getVarName(item))
		if argVal != nil {
			return argVal
		}

		// not a formal parameter, look up the symbol and return its value

		return lookupSymbolValue(item)
	}

	panic(nil) // avoid compiler complaint
}

//
// This function is called by checkFunctionArgs to pop the last N
// items off the RPN stack, so it can do a type check of each
// such item vs the corresponding formal parameter.
// NB: it would be nice if we could just slice off the last N
// stack entries, but sadly, we can't.  We have to deal with
// formal references vs actual values
//

func rpnPopSubStack(stackp *rpnStack, nItems int) rpnStack {

	var subStack rpnStack

	subStack.entries = make([]any, nItems)

	for i := nItems - 1; i >= 0; i-- {
		subStack.entries[i] = rpnPopValue(stackp)
	}

	return subStack
}

//
// Gin up the appropriate 2 dimensions
//

func computeSubs(sym *symtabNode, subs []int16) (int16, int16) {

	switch len(subs) {
	default:
		fatalError(fmt.Sprintf("Invalid number of subscripts (%d)", len(subs)))

	case 0:
		return 0, 0

	case 1:
		checkSubscript(subs[0], sym.dims[0])

		return 0, subs[0]

	case 2:
		checkSubscript(subs[0], sym.dims[0])
		checkSubscript(subs[1], sym.dims[1])

		return subs[0], subs[1]
	}

	panic(nil) // avoid compiler complaint
}

func printRpnState(state *procState) { // nolint:unused

	fmt.Println("**** RPN state *****")

	printRpnStack(&state.stack)

	if state.stmt != nil {
		fmt.Printf("stmt = %p (stmtNo = %d)\n", state.stmt,
			state.stmt.stmtNo)
	}

	fmt.Println("********************")
}

//
// This function builds a dummy procState structure, whose only
// non-default field is a *stmtNode
//

func createExecutionState(stmt *stmtNode) *procState {

	return &procState{stmt: stmt}
}

func resetRpnStack(stack *rpnStack) {

	*stack = rpnStack{}
}

//
// This function fetches the variable name associated with a number
// of data structures
//

func getVarName(arg any) string {

	switch arg := arg.(type) {
	default:
		return ""

	case fvarToken:
		return string(arg)

	case ivarToken:
		return string(arg)

	case svarToken:
		return string(arg)

	case fnfvarToken:
		return string(arg)

	case fnivarToken:
		return string(arg)

	case fnsvarToken:
		return string(arg)

	case *tokenNode:
		switch arg.token {
		default:
			unexpectedTokenError(arg.token)

		case FNFVAR, FNIVAR, FNSVAR, FVAR, IVAR, SVAR:
			return arg.tokenData.(string)
		}
	}

	panic(nil) // avoid compiler complaint
}

//
// Takes a datum and returns the base type (FLOAT, INTEGER or STRING)
//

func getBaseType(arg any) int {

	switch arg := arg.(type) {
	default:
		unexpectedTypeError(arg)

	//	case float64, fvarToken:
	case float64, fvarToken:
		return FLOAT

	//	case int16, ivarToken:
	case int16, ivarToken:
		return INTEGER

	//	case string, svarToken:
	case string, svarToken:
		return STRING

	case *tokenNode:
		token := arg.token
		switch token {
		default:
			unexpectedTokenError(token)

		case IVAR, INTEGER:
			return INTEGER

		case FVAR, FLOAT:
			return FLOAT

		case SVAR, STRING:
			return STRING
		}
	}

	panic(nil) // avoid compiler complaint
}

func callFunction(fn any, args rpnStack) any {

	var fname string
	var res any
	var rpnToken int

	nargs := len(args.entries)

	runtimeCheck(r.level < fnRecursionMax, "Function nesting exceeded")

	switch fn := fn.(type) {
	default:
		unexpectedTypeError(fn)

	case fnfvarToken:
		fname = string(fn)
		rpnToken = NRPN

	case fnivarToken:
		fname = string(fn)
		rpnToken = NRPN

	case fnsvarToken:
		fname = string(fn)
		rpnToken = SRPN
	}

	r.level++

	defStmt := r.userDefMap[fname]

	runtimeCheck(defStmt != nil,
		fmt.Sprintf("Function %q has not been defined", fname))

	defNargs := len(defStmt.operands) - 2

	runtimeCheck(defNargs == nargs,
		fmt.Sprintf("%q called with %d %s but needs %d",
			fname, nargs, pluralize("argument", nargs), defNargs))

	params := fetchUserDefParams(fname)

	if defStmt.operands[1] != nil {

		//
		// Single line user defined function
		// Clone the RHS expression for later
		//

		newTl := copyTokenList(defStmt.operands[1].tokenData.(tokenList))

		//
		// Iterate through list of formal parameters, verifying
		// that the types match
		//

		for ix := 0; ix < nargs; ix++ {
			argType := getBaseType(args.entries[ix])
			paramName := params.paramNames[ix]
			paramType := params.paramTypes[ix]

			runtimeCheck(argType == paramType,
				fmt.Sprintf("Type mismatch for parameter %q", paramName))
		}

		//
		// Iterate through the entries in the RHS expression, replacing
		// any variable references that match formal parameters with the
		// actual value.  NB: we are lazy here - if an expression element
		// is not a variable, varName will be an empty string, which of
		// course will not match any formal parameter :)
		// We do not need to check if there are any subscripted references
		// to a formal parameter (which is illegal), as this check will
		// have been made by the parser
		//

		for jx := 0; jx < len(newTl); jx++ {
			varName := getVarName(newTl[jx])
			for ix := 0; ix < defNargs; ix++ {
				if varName == params.paramNames[ix] {
					newTl[jx] = args.entries[ix]
					break
				}
			}
		}

		return evaluateRpnExpr(makeTokenNode(rpnToken, newTl), false)
	}

	//
	// Multi-line function call
	// Make sure to initialize the return value to the appropriate
	// zero value in case the user program doesn't set it
	// (this *should* be an error, but DEC doesn't complain, they
	// just see junk)
	//

	switch fname[len(fname)-1] {
	default:
		res = 0.0

	case '$':
		res = ""

	case '%':
		res = int16(0)
	}

	udStkNode := userDefStackNode{fname: fname, retval: res}
	udStkNode.paramMap = make(map[string]any)

	for ix := 0; ix < nargs; ix++ {
		argType := getBaseType(args.entries[ix])
		paramName := params.paramNames[ix]
		paramType := params.paramTypes[ix]

		runtimeCheck(argType == paramType,
			fmt.Sprintf("Type mismatch for parameter %q", paramName))

		udStkNode.paramMap[paramName] = args.entries[ix]
	}

	r.userDefStack = append(r.userDefStack, udStkNode)

	res = spawnUserFunction(defStmt)

	if len(r.userDefStack) == 1 {
		r.userDefStack = nil
	} else {
		r.userDefStack = r.userDefStack[0 : len(r.userDefStack)-1]
	}

	r.level--

	return res
}

func copyTokenList(oldTl tokenList) tokenList {

	newTl := make([]any, len(oldTl))
	copy(newTl, oldTl)

	return newTl
}

func spawnUserFunction(stmt *stmtNode) any {

	ch := make(chan any)

	//
	// Complication: we have to save r.curStmt and restore it after
	// the function call returns.  Even trickier: we have to save
	// and clear any onErrorStmtNo, as otherwise, if an exception
	// occurs in the called function, we might try to transfer out
	// of the function, which is not allowed
	//

	savedCurStmt := r.curStmt
	savedOnErrorStmtNo := r.onErrorStmtNo
	r.onErrorStmtNo = 0

	go userFunctionWrapper(ch, stmt)

	resp := <-ch

	if resp != nil {
		r.curStmt = savedCurStmt
		r.onErrorStmtNo = savedOnErrorStmtNo
	}

	//
	// Anything other than a primitive data type
	// (float64, int16 or string) is some sort of
	// fatal error that was raised.
	// and let upstream handle it, else if nil, the goroutine
	// will have printed anything useful, so crawlout, else
	// return it to our caller
	//

	switch resp := resp.(type) {
	default:
		unexpectedTypeError(resp)

	case nil:
		panic(&crawloutException{true})

	case float64:
		return resp

	case int16:
		return resp

	case string:
		return resp
	}

	panic(nil) // avoid compiler complaint
}

func userFunctionWrapper(ch chan any, stmt *stmtNode) {

	//
	// If we caught an exception, decode (and print) it.  We then
	// close the channel, so spawnUserFunction will get a nil return
	// value, and resignal the panic
	//

	defer func() {
		if e := recover(); e != nil {
			decodePanic(e)
		}

		close(ch)
	}()

	//
	// Tricky: we need to start executing with the first statement
	// after the DEF, otherwise we would end up skipping over the
	// entire function.  We also don't want executeRunInternal to
	// print statistics if called from here
	//
	// Also, we do NOT want to reset the print zone just because
	// we called a multi-line user-defined function!
	//

	executeRunInternal(createExecutionState(computeNextStmt(stmt)),
		false, false)

	udStkNode := &r.userDefStack[len(r.userDefStack)-1]

	ch <- udStkNode.retval
}

func fetchUserDefParams(fname string) userDefParams {

	var params userDefParams

	stmt := r.userDefMap[fname]

	for ix := 0; ix < len(stmt.operands)-2; ix++ {
		paramType := getBaseType(stmt.operands[ix+2])
		paramName := stmt.operands[ix+2].tokenData.(string)
		params.paramNames = append(params.paramNames, paramName)
		params.paramTypes = append(params.paramTypes, paramType)
	}

	return params
}

//
// This function takes a string and searches the formal parameter
// map for the top-level active user defined function, and returns
// the value of the corresponding actual argument.
//
// There are 3 cases here:
//
// 1. There are no active functions - we return nil
// 2. There is at least one active function, but the name does
//    not represent a formal parameter - we return nil
// 3. There is at least one active function, and the name DOES
//    represent a formal parameter - we return the value in the map
//

func getParamValue(name string) any {

	if len(r.userDefStack) != 0 {
		udStkNode := &r.userDefStack[len(r.userDefStack)-1]
		argVal := udStkNode.paramMap[name]
		if argVal != nil {
			return argVal
		}
	}

	return nil
}

func executeReload() {

	checkModified()

	cleanupLiners()

	prog := os.Args[0]
	args := make([]string, 0)
	args = append(args, prog)
	env := os.Environ()

	//
	// If we have a saved program, use that as the 2nd argument to Exec
	//

	if g.programFilename != "" {
		args = append(args, g.programFilename)
	}

	err := syscall.Exec(prog, args, env)
	if err != nil {
		crash("executeReload: " + os.Args[0] + " (" + err.Error() + ")")
	}
}

//
// Routine to open a BASIC-PLUS source file
//

func openBasicFile(filename string, iomode int) *file {

	if tfile, err := openFileFull(filename, iomode, true); err != nil {
		fmt.Printf("%s\n", error.Error(err))
		return nil
	} else {
		return tfile
	}
}

//
// Edit the current program
//

func executeEdit() {

	var err error
	var wstatus syscall.WaitStatus
	var cmd string
	var savedHistory bytes.Buffer

	editor := os.Getenv("EDITOR")
	fds := []uintptr{0, 1, 2}
	args := []string{editor, g.programFilename}

	//
	// Make sure a usable editor has been defined
	//

	if editor == "" {
		runtimeError("EDITOR not set")
	}

	if cmd, err = exec.LookPath(editor); err != nil {
		runtimeError(fmt.Sprintf("Editor %v not found", editor))
	}

	if g.programFilename == "" {
		runtimeError("No program file is active")
	}

	//
	// make sure we don't lose any active changes
	//

	checkModified()

	//
	// Save the command history, since we need to delete the
	// active liners, do the edit, and recreate them
	//

	if _, err = g.parserLiner.WriteHistory(&savedHistory); err != nil {
		fatalError(fmt.Sprintf("Unable to save command history (%v)", err))
	}

	//
	// Put us back in cooked mode, in case the editor is something
	// like 'ed'
	//

	cleanupLiners()

	pa := &syscall.ProcAttr{Env: os.Environ(), Files: fds}

	//
	// Invoke the editor on the current program
	//

	if _, _, err = syscall.StartProcess(cmd, args, pa); err != nil {
		editError(cmd + " " + err.Error())
	}

	//
	// Wait for it to exit
	//

	if _, err = syscall.Wait4(-1, &wstatus, 0, nil); err != nil {
		editError(err.Error())
	} else if wstatus != 0 {
		editError(fmt.Sprintf("%v failed - status %v", editor, wstatus))
	}

	//
	// Reenable the liners
	//

	setupLiners()

	//
	// Restore the command history
	//

	fmt.Println(savedHistory)

	if _, err = g.parserLiner.ReadHistory(&savedHistory); err != nil {
		fatalError(fmt.Sprintf("Unable to restore command history (%v)", err))
	}

	//
	// Restore the output view and command history
	//

	clearScreen()

	//
	// Finally, reload the current program
	//

	executeOld(g.programFilename)
}

//
// Reenable liners and throw the requested error
//

func editError(msg string) {

	setupLiners()

	runtimeError(msg)
}

//
// Clear the screen and position the cursor at column 0 of the
// last line
//

func clearScreen() {

	fmt.Print(clearScreenSeq)
	for i := 0; i < g.window.rows; i++ {
		fmt.Println()
	}
}

//
// Ugly: BASIC-PLUS requires DATA items as floats for READ
// even if the variable is integer.  Return a float and let
// convert if needed, if we see an integer
//

func readDataItem() any {

	runtimeCheck(r.dataIndex < len(r.dataList), EOUTOFDATA)

	dataItem := r.dataList[r.dataIndex]

	r.dataIndex++

	switch dataItem.(type) {
	case int16:
		return float64(dataItem.(int16))

	case float64:
		return dataItem.(float64)

	case string:
		return dataItem.(string)
	}

	return dataItem
}
