package main

import (
	"bytes"
	"crypto/sha256"
	"crypto/sha512"
	"fmt"
	"math"
	"math/rand"
	"runtime"
	"strconv"
	"strings"
	"time"
)

func executeBye() {

	checkModified()

	g.exiting = true
}

func executeClose(args []*tokenNode) {

	basicAssert(len(args) > 0, "CLOSE botch")

	for i := 0; i < len(args); i++ {
		filenum := anyToInt(evaluateRpnExpr(args[i], false))

		checkFilenum(filenum)

		fp := getOpenFile(filenum)

		closeFile(&fp)

		delete(r.openFiles, filenum)
	}
}

func executeCont() {

	var nextStmt *stmtNode

	if r.curStmt != nil && r.nextStmt != nil {
		nextStmt = r.nextStmt
		r.nextStmt = nil
	}

	if nextStmt == nil {
		exitToPrompt("Unable to continue")
	}

	executeRunInternal(createExecutionState(nextStmt), true, true)
}

//
// The old, new and save commands need to reset the modified flag,
// to indicate it is ok to quit.  We can't do it in executeOld(),
// as that routine is just setting up input for the lexer, such
// that even if we did do so, the parser would just set the flag
// again anyway when it reads one or more BASIC statements.
// The hack: when the lexer closes a file, it will be on behalf of
// executeOld(), so clearing the flag there does the job
//

func executeNew(tnode *tokenNode) {

	var name string
	var fp *file

	if tnode != nil {
		name = tnode.tokenData.(string)
	}

	//
	// If we have an unsaved program prompt for confirmation
	// If a filename was given, we also need to verify we're
	// not overwriting an existing file (confirmation here too)
	//

	checkModified()

	if name != "" && fileExists(name) {
		checkOverwrite(name)
	}

	initAvl()

	g.endStmtNo = 0

	initSymbolTable()

	clearModified()

	//
	// If the user said 'new' with no filename, clear the current
	// filename, as otherwise a subsequent 'save' command will
	// overwrite the previous file!  We also attempt to create the
	// file, to ensure a later save attempt will succeed
	//

	if name != "" {
		if fp = openBasicFile(name, IOWRITE); fp != nil {
			closeFile(&fp)
		}
	}

	setProgramFilename(name)

	initializeRun()
}

func executeOld(filename string) {

	checkModified()

	initializeRun()

	initAvl()

	g.endStmtNo = 0

	initSymbolTable()

	g.programFile = openBasicFile(filename, IOREAD)
	if g.programFile == nil {
		return
	}

	if fileSize(g.programFile) == 0 {
		fmt.Printf("File %s is empty?\n", filename)
	}

	setProgramFilename(filename)

	clearModified()
}

func initializeRun() {

	if r.openFiles != nil {
		for _, fp := range r.openFiles {
			closeFile(&fp)
		}
	}

	r = run{}

	r.openFiles = make(map[int]*file)
}

func executeRestore() {
	r.dataIndex = 0
}

func missingEnd() {

	exitToPrompt("Missing END statement")
}

func executeRenumber(tnode *tokenNode) {

	var oldStmtNo int16
	var op *tokenNode
	var ok bool
	var oldNoStr, newNoStr string
	var modified bool

	increment := tnode.tokenData.(int16)
	newStmtNo := increment
	renumberMap := make(map[int16]int16)
	renumberNodeList := make([]*renumberNode, 0)

	//
	// Phase 1: walk the program tree in increasing statement number order,
	// recording each statement number, along with its proposed replacement.
	// We also save the stmtNode pointers in a list, as we will have to
	// rebuild the AVL tree from scratch, lest we get any statements with
	// duplicate statement numbers.  We can detect this because newStmtNo
	// will wrap to a value <= 0
	//

	for stmt := stmtAvlTreeFirstInOrder(); stmt != nil; stmt = stmtAvlTreeNextInOrder(stmt) {

		if newStmtNo <= 0 {
			runtimeError(fmt.Sprintf("Too many statements to renumber by %d\n", increment))
		}

		renumberNodeList = append(renumberNodeList, &renumberNode{stmt: stmt})

		checkIfModified(stmt.stmtNo, newStmtNo, &modified)

		renumberMap[stmt.stmtNo] = newStmtNo
		newStmtNo += increment
	}

	//
	// Phase 2: walk renumberNodeList, switch on the statement token,
	// verifying that the target statement number actually exists
	// (during normal processing, we don't bother doing this, but when
	// renumbering, we don't want the target statement number to be zero
	// (from the map) or the original statement number, as in that case,
	// it could end up going somewhere unexpected.
	//

	badStmtNo := false

	for _, rnl := range renumberNodeList {
		tokenNodeList := make([]*tokenNode, 0)

		for stmt := rnl.stmt; stmt != nil; stmt = stmt.next {

			switch stmt.token {
			case ONERROR:
				if len(stmt.operands) == 0 {
					continue
				}

				op = stmt.operands[0]
				oldStmtNo = op.tokenData.(int16)
				if oldStmtNo == 0 {
					continue
				}

				newStmtNo, ok = renumberMap[oldStmtNo]
				if !ok {
					fmt.Printf("Statement %d does not exist!\n", oldStmtNo)
					badStmtNo = true
				} else {
					checkIfModified(oldStmtNo, newStmtNo, &modified)
					tokenNodeList = append(tokenNodeList, op)
				}

			case RESUME:
				if len(stmt.operands) == 0 {
					continue
				}

				fallthrough

			case GOSUB:
				fallthrough

			case GOTO:
				op = stmt.operands[0]
				oldStmtNo = op.tokenData.(int16)

				newStmtNo, ok = renumberMap[oldStmtNo]
				if !ok {
					fmt.Printf("Statement %d does not exist!\n", oldStmtNo)
					badStmtNo = true
				} else {
					checkIfModified(oldStmtNo, newStmtNo, &modified)
					tokenNodeList = append(tokenNodeList, op)
				}

			case IF:
				for idx := 1; idx < len(stmt.operands); idx++ {

					op = stmt.operands[idx]
					if op.token != STMT {
						unexpectedTokenError(op.token)
					}

					ifStmt := op.tokenData.(*stmtNode)

					switch ifStmt.token {
					case RESUME:
						if len(ifStmt.operands) == 0 {
							continue
						}

						fallthrough

					case GOSUB:
						fallthrough

					case GOTO:
						op = ifStmt.operands[0]
						oldStmtNo = op.tokenData.(int16)

						newStmtNo, ok = renumberMap[oldStmtNo]
						if !ok {
							fmt.Printf("Statement %d does not exist!\n",
								oldStmtNo)
							badStmtNo = true
						} else {
							checkIfModified(oldStmtNo, newStmtNo, &modified)
							tokenNodeList = append(tokenNodeList, op)
						}
					}
				}

			case ONGOSUB:
				fallthrough

			case ONGOTO:
				for idx := 1; idx < len(stmt.operands); idx++ {
					op := stmt.operands[idx]

					oldStmtNo = op.tokenData.(int16)
					newStmtNo, ok = renumberMap[oldStmtNo]
					if !ok {
						fmt.Printf("Statement %d does not exist!\n", oldStmtNo)
						badStmtNo = true
					} else {
						checkIfModified(oldStmtNo, newStmtNo, &modified)
						tokenNodeList = append(tokenNodeList, op)
					}
				}
			}
		}

		rnl.tnodeList = tokenNodeList
	}

	if badStmtNo {
		runtimeError("One or more non-existent statements was found")
	}

	//
	// If modified is false, nothing would change, so don't bother
	// redoing the AVL tree, and especially, don't bother marking
	// the program as modified, which would force the user to take
	// action before they can exit
	//

	if !modified {
		return
	}

	//
	// Phase 3: nuke the program tree, and iterate through the
	// renumberNodeList, updating the stmtNo in each node, then inserting
	// it into the program tree.  We also have to modify the saved line
	// string in each statement node, which is non-trivial :)
	//

	initAvl()

	g.endStmtNo = 0

	for _, rnl := range renumberNodeList {
		stmt := rnl.stmt

		stmt.stmtNo = renumberMap[stmt.stmtNo]
		newNoStr = strconv.FormatInt(int64(stmt.stmtNo), 10)

		bias := len(newNoStr) - stmt.stmtNoTokenLoc.end.column

		stmt.line = replaceSubstring(stmt.line, 0,
			uint16(stmt.stmtNoTokenLoc.end.column), newNoStr)

		stmt.stmtNoTokenLoc.end.column += bias

		for i := 0; i < len(rnl.tnodeList); i++ {
			tp := rnl.tnodeList[i]
			oldNoStr = strconv.FormatInt(int64(tp.tokenData.(int16)), 10)
			newNo := renumberMap[tp.tokenData.(int16)]
			newNoStr = strconv.FormatInt(int64(newNo), 10)
			tp.tokenData = renumberMap[tp.tokenData.(int16)]

			tp.tlocs += uint16(bias)
			tp.tloce += uint16(bias)

			stmt.line = replaceSubstring(stmt.line, tp.tlocs,
				tp.tloce, newNoStr)

			tp.tloce = tp.tlocs + uint16(len(newNoStr))
			bias += len(newNoStr) - len(oldNoStr)
		}

		stmtAvlTreeInsert(stmt, cmpInt16Snode)
	}
}

//
// It's silly to mark the program as modified if the renumber command
// didn't actually change anything
//

func checkIfModified(oldStmtNo, newStmtNo int16, modified *bool) {

	if oldStmtNo != newStmtNo {
		*modified = true
	}
}

//
// This function is the common case.  We don't have any fault state
// to recover from, so we initialize a state structure with the only
// non-default field being the *stmtNode to run from
//

func executeRun(stmt *stmtNode, brief bool) {

	runtimeCheck(stmtAvlTreeFirstInOrder() != nil, "No program loaded")

	if g.endStmtNo == 0 {
		missingEnd()
	}

	//
	// Print version info if requested
	//

	if !brief {
		printVersionInfo()
	}

	//
	// Reinitialize any needed fields in the 'r' structure,
	// as well as nuking the symbol table
	//

	initializeRun()

	initSymbolTable()

	//
	// Run the GC (twice) to clean things up from last time (if needed)
	//

	runtime.GC()

	runtime.GC()

	//
	// Process declaration statements (DEF, DATA, DIM and FNEND)
	//

	processDeclarations()

	//
	// We don't want to reset the statistics and clock in
	// executeRunInternal because it's called by executeCont,
	// as well as the fault recovery code, and that would zero
	// out valid statistics
	//

	resetStatistics()

	initClock()

	//
	// We're being called from the parser on behalf of the
	// RUN/RUNNH commands, so fetch the lowest numbered statement,
	//

	executeRunInternal(createExecutionState(stmtAvlTreeFirstInOrder()),
		true, true)
}

func executeRunInternal(state *procState, resetPrintZone, doStats bool) {

	var arg any

	curStmt := state.stmt

	//
	// Almost always, the routines executeStmt calls take one parameter,
	// which is the statement node to execute.  The only exception at this
	// time is executeFor.  It can be invoked because we are starting a
	// new loop, or because it was passed the FOR statement node address
	// returned by executeNext.  In the former case, we need to do all the
	// sanity checking, initialization, etc.  In the latter case, we just
	// do the normal loop update&check stuff.  It might be handy for some
	// other routine to be passed an additional argument, so rather than
	// hardcode 'arg' as a bool, we make it an empty interface, and rely
	// on executeFor to pull the bool out
	//
	// Update: we actually pass a procState variable around, which
	// encapsulates the statement number.  Used for fault recovery
	//

	r.curStmt = curStmt
	g.running = true
	g.interrupted = false

	//
	// Do NOT reset the print zone unless requested!
	//

	if resetPrintZone {
		resetPrint(false)
	}

	//
	// executeStmt() will compute a new statement to execute.
	// It will return the next statement to execute, unless
	// we ran off the end of the program, in which case nil will be
	// be returned.
	// A non-nil stmtNode is computed either explicitly by the verbs
	// such as GOSUB, GOTO, RETURN or IF, or implicitly, by fetching
	// the next sequential statement in the program.
	///

	for curStmt != nil {
		state, arg = executeStmt(state, arg)
		curStmt = state.stmt
		r.nextStmt = curStmt

		if curStmt != nil {
			curStmtNo := curStmt.stmtNo
			if curStmtNo != 0 {
				runtimeCheck(curStmtNo <= g.endStmtNo,
					"Transfer past END statement")
			}

			r.curStmt = curStmt
		}

		s.numStatements++
	}

	if doStats {
		printStatistics()
	}
}

func executeSleep(args []*tokenNode) {

	var sleepVal int16

	basicAssert(len(args) == 1, "SLEEP botch")

	arg0 := args[0]

	val := evaluateRpnExpr(arg0, false)

	switch val := val.(type) {
	default:
		unexpectedTypeError(val)

	case int16:
		sleepVal = val

	case float64:
		sleepVal = floatToInt16(val)
	}

	runtimeCheck(sleepVal >= 1, "Invalid sleep time")

	sleep(sleepVal)
}

func executeWait(args []*tokenNode) {

	var waitVal int16

	basicAssert(len(args) == 1, "WAIT botch")

	arg0 := args[0]

	val := evaluateRpnExpr(arg0, false)

	switch val := val.(type) {
	default:
		unexpectedTypeError(val)

	case int16:
		waitVal = val
		runtimeCheck(waitVal >= 0, "Invalid wait time")

	case float64:
		runtimeCheck(val >= float64(0) && val <= float64(math.MaxInt16),
			"Invalid wait time")
		waitVal = int16(val)
	}

	r.ioTimeout = waitVal
}

func executeSave(tnode *tokenNode) {

	var of *file
	var name string

	if tnode != nil {
		name = tnode.tokenData.(string)
	}

	setName := false

	//
	// 4 cases:
	//
	// No filename given, and a current filename is defined - use that name
	// No filename given, and no current filename - error
	// A Filename was given, and a current filename is defined - change the
	//   current filename
	// A filename was given, and no current filename is defined - set the
	//   current filename
	//
	// Do not overwrite an existing file without confirmation
	//

	runtimeCheck(g.program != nil, "No program to save!")

	if name == "" {
		if g.programFilename == "" {
			runtimeError("Filename required")
		} else {
			name = g.programFilename
		}
	} else {
		if fileExists(name) {
			checkOverwrite(name)
		}

		setName = true
	}

	if of = openBasicFile(name, IOWRITE); of == nil {
		return
	}

	saveProgram(of)

	closeFile(&of)

	if setName {
		setProgramFilename(name)
	}

	clearModified()
}

func evaluateRpnExpr(tnode *tokenNode, lhs bool) any {

	var state procState

	if tnode.token != NRPN && tnode.token != SRPN {
		unexpectedTokenError(tnode.token)
	}

	state.expr = tnode.tokenData.(tokenList)

	return evaluateRpnExprInternal(&state, lhs)
}

func evaluateRpnExprInternal(state *procState, lhs bool) any {

	var ret any
	var dims, lhsDims []int16
	var sub2 int16
	var intRes bool
	var idx int
	var t, zeroTime time.Time

	stackp := &state.stack

	//
	// Walk the token list, pushing, popping and operating as required
	//

	for idx = 0; idx < len(state.expr); {
		item := state.expr[idx]
		idx++

		switch item := item.(type) {
		case fnfvarToken, fnivarToken, fnsvarToken:
			rpnPush(stackp, item)

		case fvarToken, ivarToken, svarToken:
			rpnPush(stackp, item)

		case float64:
			rpnPush(stackp, item)

		case int16:
			rpnPush(stackp, item)

		case string:
			rpnPush(stackp, item)

		//
		// Operator tokens are GO 'int' values
		//

		case int:
			switch item {
			default:
				unexpectedTokenError(item)

			case ABS:
				ret, intRes = rpnPopNumber(stackp)
				if intRes {
					tmp16 := ret.(int16)
					runtimeCheck(tmp16 != math.MinInt16, EINTEGERERROR)
					rpnPush(stackp, int16(math.Abs(float64(tmp16))))
				} else {
					rpnPush(stackp, math.Abs(ret.(float64)))
				}

			case AND:
				right := rpnPopInt16(stackp)
				left := rpnPopInt16(stackp)
				rpnPush(stackp, left&right)

			case APPROX:
				vl, vr := rpnPopTwoNumbers(stackp)

				if isInt(vl) {
					rpnPush(stackp, boolToInt16(vl.(int16) == vr.(int16)))
				} else {
					o := floatValuesApproxEqual(vl.(float64), vr.(float64))
					rpnPush(stackp, boolToInt16(o))
				}

			case ASCII:
				str := rpnPopString(stackp)
				if len(str) == 0 {
					rpnPush(stackp, int16(0))
				} else {
					rpnPush(stackp, int16(str[0]))
				}

			case ATN:
				rpnPush(stackp, math.Atan(rpnPopFloat(stackp)))

			case CHRS:
				i8 := rpnPopInt16(stackp)
				runtimeCheck(i8 >= 0 && i8 <= math.MaxUint8,
					EINTEGERERROR)
				rpnPushString(stackp, string(rune(i8)))

			case CONCAT:
				strr := rpnPopString(stackp)
				strl := rpnPopString(stackp)
				rpnPushString(stackp, strl+strr)

			case COS:
				rpnPush(stackp, math.Cos(rpnPopFloat(stackp)))

			case CVTFS:
				ui := math.Float64bits(rpnPopFloat(stackp))
				bs := make([]byte, 8)
				for j := 0; j < 8; j++ {
					bs[j] = byte(ui >> (56 - j*8))
				}
				rpnPushString(stackp, string(bs))

			case CVTIS:
				i := rpnPopInt16(stackp)
				rpnPushString(stackp, string(rune(i/256))+string(rune(i%256)))

			case CVTSF:
				var ui64 uint64
				var byte uint64

				str := rpnPopString(stackp)

				for i := 0; i < 8; i++ {
					if i >= len(str) {
						byte = 0
					} else {
						byte = uint64(str[i])
					}

					ui64 = ui64*256 + byte
				}

				rpnPush(stackp, math.Float64frombits(ui64))

			case CVTSI:
				str := rpnPopString(stackp)
				switch len(str) {
				case 0:
					rpnPush(stackp, int16(0))

				case 1:
					rpnPush(stackp, int16(int(str[0])*256))

				default:
					rpnPush(stackp, int16(int(str[0])*256+int(str[1])))
				}

			case DATES:
				dateNum := rpnPopInt(stackp)
				if dateNum == 0 {
					t = time.Now()
				} else {
					//
					// Annoying: BASIC-PLUS epoch is 1/1/1970, but the
					// GO "zero value" for time is 1/1/0001, NOT 1/1/0000,
					// so we have to fudge by 1969 instead of 1970
					//

					runtimeCheck(dateNum >= 0, badDateMsg)
					yearOff := dateNum/1000 + 1969
					dayOff := dateNum % 1000
					runtimeCheck(yearOff < 9999 && dayOff < 365,
						badDateMsg)
					t = zeroTime.AddDate(yearOff, 0, dayOff)
				}

				rpnPushString(stackp, t.Format("02-Jan-2006"))

				//	case DET:
				//		runtimeError("NOT YET IMPLEMENTED!")
				//		rpnPush(stackp, r.det)

			case EQ:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, boolToInt16(vl.(int16) == vr.(int16)))
				} else {
					rpnPush(stackp, boolToInt16(vl.(float64) == vr.(float64)))
				}

			case EQV:
				right := rpnPopBool(stackp)
				left := rpnPopBool(stackp)
				rpnPush(stackp, boolToInt16(left == right))

			case ERL:
				rpnPush(stackp, fetchStmtNoFromFip(r.fip))

			case ERR:
				if r.fip != nil {
					rpnPush(stackp, r.fip.err)
				} else {
					rpnPush(stackp, int16(0))
				}

			case EXP:
				f := rpnPopFloat(stackp)
				if f > maxExpArg || f < minExpArg {
					arithFault(EEXPERROR, state, float64(0))
					continue
				}
				rpnPush(stackp, math.Exp(f))
				checkFloatingStatus(state)

			case FIX:
				rpnPush(stackp, computeFix(rpnPopFloat(stackp)))

			case GE:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, boolToInt16(vl.(int16) >= vr.(int16)))
				} else {
					rpnPush(stackp, boolToInt16(vl.(float64) >= vr.(float64)))
				}

			case GT:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, boolToInt16(vl.(int16) > vr.(int16)))
				} else {
					rpnPush(stackp, boolToInt16(vl.(float64) > vr.(float64)))
				}

			case IMP:
				right := rpnPopBool(stackp)
				left := rpnPopBool(stackp)
				if left && !right {
					rpnPush(stackp, boolToInt16(false))
				} else {
					rpnPush(stackp, boolToInt16(true))
				}

			case INSTR:
				substr := rpnPopString(stackp)
				target := rpnPopString(stackp)
				idx := rpnPopInt16(stackp)
				checkStringIndex(target, idx)
				fidx := int16(strings.Index(target, substr)) + 1

				if fidx < idx {
					fidx = 0
				}
				rpnPush(stackp, fidx)

			case INT:
				rpnPush(stackp, computeInt(rpnPopFloat(stackp)))

			case LE:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, boolToInt16(vl.(int16) <= vr.(int16)))
				} else {
					rpnPush(stackp, boolToInt16(vl.(float64) <= vr.(float64)))
				}

			case LEFT:
				nchars := int(rpnPopInt16(stackp))
				str := rpnPopString(stackp)
				rpnPush(stackp, basicSubstring(str, 1, nchars))

			case LEN:
				rpnPush(stackp, int16(len(rpnPopString(stackp))))

			case LOG:
				f := rpnPopFloat(stackp)
				if f <= 0 {
					arithFault(ELOGERROR, state, float64(0))
					continue
				}

				rpnPush(stackp, math.Log(f))

			case LOG10:
				f := rpnPopFloat(stackp)
				if f <= 0 {
					arithFault(ELOGERROR, state, float64(0))
					continue
				}

				rpnPush(stackp, math.Log10(f))

			case LT:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, boolToInt16(vl.(int16) < vr.(int16)))
				} else {
					rpnPush(stackp, boolToInt16(vl.(float64) < vr.(float64)))
				}

			case MID:
				nchars := int(rpnPopInt16(stackp))
				start := int(rpnPopInt16(stackp))
				str := rpnPopString(stackp)
				rpnPush(stackp, basicSubstring(str, start, nchars))

			case MINUS:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, vl.(int16)-vr.(int16))
				} else {
					rpnPush(stackp, vl.(float64)-vr.(float64))
					checkFloatingStatus(state)
				}

				//
				// We don't actually care if the call is NCALL or SCALL,
				// as it was only so the parser could diagnose string vs
				// numeric mismatches
				//

			case NCALL:
				fallthrough
			case SCALL:

				fn := rpnPop(stackp)
				nargs := int(rpnPopInt16(stackp))
				args := rpnPopSubStack(stackp, nargs)

				res := callFunction(fn, args)
				rpnPush(stackp, res)

			case NE:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, boolToInt16(vl.(int16) != vr.(int16)))
				} else {
					rpnPush(stackp, boolToInt16(vl.(float64) != vr.(float64)))
				}

			case NOT:
				i16 := rpnPopInt16(stackp)
				i16 = fixupBoolInt16(i16)
				i16 = i16 ^ -1
				rpnPush(stackp, i16)

			case NUMS:
				f64, _ := rpnPopNumber(stackp)
				rpnPush(stackp, basicFormat(f64))

			case OR:
				right := rpnPopInt16(stackp)
				left := rpnPopInt16(stackp)

				rpnPush(stackp, left|right)

			case PI:
				rpnPush(stackp, math.Pi)

			case PLUS:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, vl.(int16)+vr.(int16))
				} else {
					rpnPush(stackp, vl.(float64)+vr.(float64))
					checkFloatingStatus(state)
				}

			case POS:
				fd := rpnPopInt16(stackp)
				runtimeCheck(fd == 0, "Invalid file number")
				rpnPush(stackp, int16(curPrintPos()))

			case POW:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					fl := float64(vl.(int16))
					fr := float64(vr.(int16))
					rpnPush(stackp, int16(math.Pow(fl, fr)))
				} else {
					rpnPush(stackp, math.Pow(vl.(float64), vr.(float64)))
					checkFloatingStatus(state)
				}

			case RIGHT:
				start := int(rpnPopInt16(stackp))
				str := rpnPopString(stackp)
				rpnPush(stackp, basicSubstring(str, start, len(str)-start+1))

			case RND:
				rpnPush(stackp, rand.Float64())

			case SGN:
				rpnPush(stackp, computeSgn(rpnPopFloat(stackp)))

			case SHA256:
				str := rpnPopString(stackp)
				str = fmt.Sprintf("%x", sha256.Sum256([]byte(str)))
				rpnPushString(stackp, str)

			case SHA512:
				str := rpnPopString(stackp)
				str = fmt.Sprintf("%x", sha512.Sum512([]byte(str)))
				rpnPushString(stackp, str)

			case SIN:
				rpnPush(stackp, math.Sin(rpnPopFloat(stackp)))

			case SLASH:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vr) {
					if vr.(int16) == 0 {
						arithFault(EDIVISIONBYZERO, state, int16(0))
						continue
					}

					rpnPush(stackp, vl.(int16)/vr.(int16))
				} else {
					if vr.(float64) == 0.0 {
						arithFault(EDIVISIONBYZERO, state, float64(0))
						continue
					}

					rpnPush(stackp, vl.(float64)/vr.(float64))
					checkFloatingStatus(state)
				}

			case SPACES:
				n := int(rpnPopInt16(stackp))
				rpnPush(stackp, strings.Repeat(" ", n))

			case SQR:
				f := rpnPopFloat(stackp)
				if f < 0 {
					arithFault(ESQRERROR, state, float64(0))
					continue
				}

				rpnPush(stackp, math.Sqrt(f))

			case STAR:
				vl, vr := rpnPopTwoNumbers(stackp)
				if isInt(vl) {
					rpnPush(stackp, vl.(int16)*vr.(int16))
				} else {
					rpnPush(stackp, vl.(float64)*vr.(float64))
				}

			case STREQ:
				vl, vr := rpnPopTwoStrings(stackp)
				rpnPush(stackp, boolToInt16(vl == vr))

			case STRNE:
				vl, vr := rpnPopTwoStrings(stackp)
				rpnPush(stackp, boolToInt16(vl != vr))

			case STRGE:
				vl, vr := rpnPopTwoStrings(stackp)
				rpnPush(stackp, boolToInt16(vl >= vr))

			case STRGT:
				vl, vr := rpnPopTwoStrings(stackp)
				rpnPush(stackp, boolToInt16(vl > vr))

			case STRLE:
				vl, vr := rpnPopTwoStrings(stackp)
				rpnPush(stackp, boolToInt16(vl <= vr))

			case STRLT:
				vl, vr := rpnPopTwoStrings(stackp)
				rpnPush(stackp, boolToInt16(vl < vr))

			case SUBSCR2:
				sub2 = rpnPopInt16(stackp)
				fallthrough
			case SUBSCR1:

				dims = append(dims, rpnPopInt16(stackp))

				//
				// If we fell into this from the SUBSCR2 case, we need
				// to append sub2 after sub1.  Everything else just falls
				// into place automatically

				if item == SUBSCR2 {
					dims = append(dims, sub2)
				}

				//
				// If we're in the LHS of a LET statement, and we're
				// the lvalue symbol, do nothing here, we must be the
				// last item in the RPN list, and the final EA will be
				// computed before we return, so we leave the symbol
				// node on the RPN stack.  We do, however, need to save
				// the 'dims' for the LHS to use at the end
				//

				if !lhs || idx < len(state.expr)-1 {
					sym := rpnPop(stackp) // the symbol ref
					rval := lookupSymbolValue(sym, dims...)
					rpnPush(stackp, rval)
				} else {
					lhsDims = dims
				}
				dims = nil

			case SWAPI:
				i16 := rpnPopInt16(stackp)
				highByte := i16 / 256
				lowByte := i16 % 256
				rpnPush(stackp, int16(lowByte*256+highByte))

			case TAB:
				newPos := int(rpnPopInt16(stackp))
				curPos := curPrintPos()
				if newPos > curPrintPos() {
					rpnPush(stackp, strings.Repeat(" ", newPos-curPos))
				} else {
					rpnPush(stackp, "")
				}

			case TAN:
				rpnPush(stackp, math.Tan(rpnPopFloat(stackp)))

			case TIME:
				iomode := rpnPopInt16(stackp)
				switch iomode {
				default:
					runtimeError(fmt.Sprintf("Invalid iomode %d", iomode))

				case 0:
					//
					// Time since midnight in seconds
					//

					t := time.Now()
					midnight := time.Date(t.Year(), t.Month(), t.Day(), 0,
						0, 0, 0, t.Location())
					secs := math.Floor(time.Since(midnight).Seconds())

					rpnPush(stackp, float64(secs))

				case 1:
					//
					// Login (session) CPU time in 10ms units
					//

					utime, stime := getCPUInfo(10)

					rpnPush(stackp, float64(utime+stime))

				case 2:
					//
					// Login (session) time in minutes
					//

					mins := math.Floor(time.Since(g.loginTime).Minutes())

					rpnPush(stackp, mins)
				}

			case TIMES:
				t := time.Now()
				minutes := rpnPopInt16(stackp)
				runtimeCheck(minutes >= 0 && minutes <= 1440,
					"Invalid input to TIME$")

				if minutes != 0 {
					t = time.Date(t.Year(), t.Month(), t.Day(), 0,
						1440-int(minutes), 0, 0, t.Location())
				}

				rpnPushString(stackp, t.Format("3:04PM"))

			case WHILE, UNTIL:
				v := rpnPopInt16(stackp)
				if v != 0 {
					rpnPush(stackp, boolInt16True)
				} else {
					rpnPush(stackp, boolInt16False)
				}

			case UNEG:
				ret, intRes = rpnPopNumber(stackp)
				if intRes {
					rpnPush(stackp, -ret.(int16))
				} else {
					rpnPush(stackp, -ret.(float64))
				}

			case VAL:
				rpnPush(stackp, convertFloat(rpnPopString(stackp)))

			case XOR:
				right := rpnPopInt16(stackp)
				left := rpnPopInt16(stackp)
				rpnPush(stackp, left^right)
			}
		}
	}

	switch len(stackp.entries) {
	default:
		fatalError(fmt.Sprintf("%d items left on RPN stack",
			len(stackp.entries)))

	case 0:
		fatalError("RPN stack is empty")

	case 1:
		// OK
	}

	//
	// The LHS case is tricky.  The value field in the symbol table
	// node is any (e.g. a catchall).  What we would *like* to do
	// is compute the effective address of the LHS (which could be
	// non-trivial, since it can be a 2 dimensional array reference),
	// and have executeLet store into that.  Sadly, GO doesn't have a good
	// (or at least safe&portable) way of doing that.  Instead, we have a
	// struct called lhsRetVal which holds a symbol table node address, as
	// well as 1 or 2 subscript values.  In the LHS case below, we gin up
	// one of these structs, copy the 2 or 3 items into it, and return that.
	// executeLet then has to pull out the items and call the appropriate
	// store*Var helper function.  Even more annoyingly, the way a multi
	// line function returns a value is by assigning it to the function
	// name!  We look up the function name for the currently active user
	// defined function and throw an exception if there isn't one, or there
	// is, but the name doesn't match the LHS.  If it's legit, we return
	// nil for the return value, and executeLet will know to stash the
	// RHS in the top-level UD stack node.  We have to do this in two phases
	// since in the 'lhs' block below, we don't know what the RHS is
	//

	if lhs {
		lhsObj := rpnPopSymbol(stackp)
		switch lhsObj.(type) {
		case fnfvarToken, fnivarToken, fnsvarToken:
			lhsFunctioname := getVarName(lhsObj)

			if len(r.userDefStack) != 0 {
				udStkNode := &r.userDefStack[len(r.userDefStack)-1]
				fname := udStkNode.fname
				if lhsFunctioname == fname {
					return nil
				}
			}

			runtimeError("This function is not active")

		case fvarToken, ivarToken, svarToken:
			sym := lookupSymbolRef(lhsObj, lhsDims...)
			ret = lhsRetVal{sym: sym, subs: lhsDims}
		}
	} else {
		if rpnStackTopNumeric(stackp) {
			ret, intRes = rpnPopNumber(stackp)

			//
			// It is possible (and legal) for IEEE-754 floating point
			// operations to result in -0.0.  I think this is prone to
			// cause confusion, and given that IEEE-754 requires 0.0
			// and -0.0 to compare equal, we will play it safe and make
			// sure zero is always positive.  If there is a float as the
			// top stack item, it *should* be valid, due to the various
			// operators checking as they go, but check again to be safe
			// The RSTS-11 implementation treats -0.0 as 0.0 anyway!
			//

			if !intRes {
				f := ret.(float64)
				if f == 0.0 {
					ret = float64(0.0)
				} else {
					rpnPush(stackp, f)
					checkFloatingStatus(state)
					ret = rpnPopFloat(stackp)
				}
			}
		} else {
			ret = rpnPopString(stackp)
		}
	}

	return ret
}

func executeStmt(state *procState, arg any) (s *procState, a any) {

	//
	// Be prepared to catch any runtime errors, since there may be
	// an ON ERROR GOTO in force.  If the exception is either not
	// a BASIC runtime error, or it is, but no handler is active,
	// call panic(e) to 'continue to signal', and the exception will
	// be caught by the top-level handler, otherwise, we look up the
	// stmt node for the handler's statement number, and return that
	// to executeRun.  It *should* be impossible for the AVL lookup
	// to fail, as executeOnError will throw a runtime exception
	// before enabling the handler, if the statement doesn't exist
	//
	// NB: we need to make sure we do NOT handle any exceptions here
	// if there is an active fault and a fault handler is enabled,
	// as otherwise any errors in the fault handler (like a RESUME
	// to a non-existent statement) will recurse
	//

	defer func() {
		if e := recover(); e != nil {

			switch e.(type) {
			default:
				panic(e)

			case *runtimeErrorInfo:

				//
				// If we are already processing a fault, signal the
				// current one, but ensure that it is NOT continuable
				//

				if r.fip != nil {
					panic(e)
				}

				re := processFault(e)
				fip := re.fip

				//
				// Non catchable error - pass it upstream
				//

				if fip.err < 0 {
					panic(e)
				}

				//
				// Continuable error with a user defined error handler,
				// set the next statement to the ON ERROR handler,
				// otherwise pass the error upstream
				//

				if r.onErrorStmtNo != 0 {
					stmt := stmtAvlTreeLookup(r.onErrorStmtNo, cmpInt16Key)
					s = createExecutionState(stmt)
					_ = processFault(e)
					return
				} else {
					panic(e)
				}
			}
		}
	}()

	checkInterrupts()

	return executeStmtInternal(state, arg)
}

func executeStmtInternal(state *procState, arg any) (*procState, any) {

	var stmt *stmtNode
	var ret *procState

	curStmt := state.stmt

	//
	// For any verb which causes transfer of control to an explicit
	// statement number, we need to call checkStmtTargetScope to ensure
	// that we are not transferring into or out of a multiline user
	// defined function.  This is obviously not an issue with executeFor or
	// executeReturn.  executeOn and executeOnError call checkStmtTargetScope
	// explicitly, because they modify state and/or call other execution
	// routines, so by the time we get back here, it's too late.
	// Also, we do the check in executeOnError even though that's just the
	// setup of the ON ERROR handler, as we know the transfer would not be
	// legal if&when a fault occurs
	//

	if g.traceExec {
		printErrorLocStmt(curStmt, "")
	}

	switch curStmt.token {
	default:
		unexpectedTokenError(curStmt.token)

	case CHANGE:
		executeChange(curStmt)

	case CLOSE:
		executeClose(curStmt.operands)

	case COMMENT:
		// nothing to do

	//
	// The DIM and DATA statements are ignored by the execution loop.
	// They are processed at the staer of execution by processDimStmts
	// and processDataStmts.
	// Any statements between a DEF and its matching FNEND are also
	// ignored in the top-level execution loop
	//

	case DATA, DIM:
		// nothing to do

	//
	// If we see a DEF, skip over everything up to and including
	// the matching FNEND.  We don't actually skip the FNEND
	// statement itself, as the call to computeNextStmt() at the end of
	// this function will do that as a side-effect of normal execution.
	// None of this is germane for a single-line function, as the same
	// call will skip it
	//

	case DEF:
		idx := lookupStmtInUserFunctionList(curStmt.stmtNo)
		if idx >= 0 {
			curStmt = r.userDefList[idx].lastStmt
		}

	case END:
		initializeRun()
		return createExecutionState(nil), nil

	case FIELD:
		executeField(curStmt.operands)

	case FNEND:
		return createExecutionState(nil), nil

		//
		// Unlike FORTRAN, where the DO condition is evaluated at the
		// end of the loop, BASIC requires us to evaluate it at the
		// beginning of each iteration.  If the loop termination
		// expression indicates the loop should terminate, we need to
		// resume at the statement *after* the NEXT statement, not the
		// NEXT statement itself.  In that case, executeFor will return
		// the stmt node address of the statement after the NEXT statement
		//

	case FOR:
		ret = executeFor(curStmt, arg)
		if ret.stmt != nil {
			return ret, nil
		}

	case GET:
		executeGet(curStmt.operands)

	case GOSUB:
		op := curStmt.operands[0]
		checkStmtTargetScope(op.tokenData.(int16))
		checkForExit(op.tokenData.(int16), false)
		return createExecutionState(executeGosub(op)), nil

	case GOTO:
		op := curStmt.operands[0]
		checkStmtTargetScope(op.tokenData.(int16))
		checkForExit(op.tokenData.(int16), true)
		return createExecutionState(executeGoto(op)), nil

	case IF:

		//
		// executeIf will return a non-nil stmt if the flow of control
		// is being altered.  If the THEN or ELSE clause fired, it will
		// execute the relevant function.  If that is a function that
		// changes flow of control, executeIf just passes that along.
		// If it's a function that doesn't (like LET or PRINT), or there
		// is no ELSE clause, but it would have fired if one was present,
		// it returns nil
		//
		// Ugly hack: jumping out of a FOR loop terminates the FOR loop,
		// except for GOSUB, which is kind of essential.  This code path
		// has no easy way to tell what executeIf does, so we cheat and
		// stash the GOSUB stack level before calling executeIf, and
		// compare the current level against the saved level, and pass
		// that to checkForExit
		//

		ogsl := len(r.gosubStack)
		ret = executeIf(curStmt)
		ngsl := len(r.gosubStack)
		if ret.stmt != nil {
			checkStmtTargetScope(ret.stmt.stmtNo)
			checkForExit(ret.stmt.stmtNo, ogsl == ngsl)
			return ret, nil
		}

	case INPUT:
		executeInput(curStmt.operands)

	case KILL:
		executeKill(curStmt.operands)

	case LET:
		executeLet(state)

	case LSET:
		executeSet(curStmt.operands, false)

	case MAT:
		executeMat(curStmt.operands)

	case NEXT:

		//
		// executeNext is a peculiar beast.  If it returns a non-nil
		// *stmtNode, it means executeRun should execute that statement
		// next, and it is the matching FOR statement.  We pass executeFor
		// a boolean true to tell it that we are iterating, as opposed
		// to initializing.  The following is non-obvious, as we are
		// returning true to executeRun, which will dutifully pass it to
		// executeFor, so it knows whether we are initializing or iterating!
		//

		return createExecutionState(executeNext(curStmt)), true

	case ONGOSUB, ONGOTO:
		return createExecutionState(executeOn(curStmt)), nil

	case ONERROR:
		executeOnError(curStmt.operands)

	case OPEN:
		executeOpen(curStmt.operands)

	case PRINT:
		executePrint(curStmt.operands)

	case PUT:
		executePut(curStmt.operands)

	case RANDOMIZE:
		executeRandomize()

	case RESTORE:
		executeRestore()

	case READ:
		executeRead(curStmt)

	case REM:
		// nothing to do

	case RESUME:
		var op *tokenNode
		if len(curStmt.operands) != 0 {
			op = curStmt.operands[0]
			checkStmtTargetScope(op.tokenData.(int16))
			checkForExit(op.tokenData.(int16), false)
		}

		return executeResume(op), nil

	case RETURN:
		curStmt = executeReturn()

	case RSET:
		executeSet(curStmt.operands, true)

	case STOP:
		executeStop()
		fatalError("executeStop returned")

	case SLEEP:
		executeSleep(curStmt.operands)

	case WAIT:
		executeWait(curStmt.operands)
	}

	stmt = computeNextStmt(curStmt)

	//
	// If we ran off the end of the program, we can't CONT
	//

	if stmt == nil {
		initializeRun()
	}

	return createExecutionState(stmt), nil
}

func executeGet(args []*tokenNode) {

	var of *file
	var recNo int
	var tmpStr string

	basicAssert(len(args) == 2, "GET botch")

	ioch := evaluateIntegerExpr(args[0])
	checkFilenum(ioch)

	//
	// If a record number was specified, fetch it
	//

	if op1 := args[1]; op1 != nil {
		basicAssert(op1.token == RECORD, "RECORD botch")
		basicAssert(len(op1.operands) == 1, "RECORD botch")

		recNo = evaluateIntegerExpr(op1.operands[0])
		runtimeCheck(recNo >= 1, "Record number must be >= 1")
	}

	//
	// If specified channel not open, punt
	//

	if of = r.openFiles[ioch]; of == nil {
		runtimeError(ENOTOPEN)
	}

	//
	// If printFile, punt
	//

	runtimeCheck(of.fileType != printFile, EPROTECTIONVIOLATION)

	//
	// If this was an empty file, convert it now
	//

	if of.fileType == emptyFile {
		setRecordFile(of)
	}

	fldp := r.fieldMap[ioch]
	runtimeCheck(fldp != nil, fmt.Sprintf("No field for channel %d\n", ioch))

	//
	// If we were passed a record number, use it, otherwise bump
	// the last used record number
	//

	if recNo != 0 {
		of.recNo = recNo
	} else {
		of.recNo++
	}

	readRecord(of, ioch)

	for _, fldel := range (*fldp).fldel {
		for _, flde := range fldel.flde {
			sym := flde.fieldVar
			flen := flde.flen
			offset := flde.offset
			subs := flde.subs
			tmpStr = string(of.recBuf[offset : offset+int16(flen)])
			storeStringVar(sym, tmpStr, true, subs...)
		}
	}
}

func executePut(args []*tokenNode) {

	var of *file
	var recNo int

	basicAssert(len(args) == 2, "PUT botch")

	ioch := evaluateIntegerExpr(args[0])
	checkFilenum(ioch)

	//
	// If a record number was specified, fetch it
	//

	if op1 := args[1]; op1 != nil {
		basicAssert(op1.token == RECORD, "RECORD botch")
		basicAssert(len(op1.operands) == 1, "RECORD botch")

		recNo = evaluateIntegerExpr(op1.operands[0])
		runtimeCheck(recNo >= 1, "Record number must be >= 1")
	}

	//
	// If specified channel not open, punt
	// If printFile, punt
	//

	if of = r.openFiles[ioch]; of == nil {
		runtimeError(ENOTOPEN)
	} else {
		runtimeCheck(of.fileType != printFile, EPROTECTIONVIOLATION)
	}

	fldp := r.fieldMap[ioch]
	runtimeCheck(fldp != nil, fmt.Sprintf("No field for channel %d\n", ioch))

	//
	// If we were passed a record number, use it, otherwise bump
	// the last used record number
	//

	if recNo != 0 {
		of.recNo = recNo
	} else {
		of.recNo++
	}

	if of.fileType == emptyFile {
		setRecordFile(of)
	}

	for _, fldel := range fldp.fldel {
		for _, flde := range fldel.flde {
			sym := flde.fieldVar
			flen := flde.flen
			offset := flde.offset
			subs := flde.subs
			tmpStr := fetchStringVar(sym, subs...)
			if len(tmpStr) != 0 {
				tmpBuf := []byte(copyString(tmpStr, int(flen), false))
				copy(of.recBuf[offset:offset+int16(flen)], tmpBuf)
			}
		}
	}

	writeRecord(of, ioch)
}

func executeField(args []*tokenNode) {

	var sym *symtabNode
	var offset int16
	var flen int
	var fldp *field
	var fldel fieldElementList
	var goffset int16

	basicAssert(len(args) == 2, "FIELD botch")

	ioch := evaluateIntegerExpr(args[0])
	checkFilenum(ioch)

	//
	// If specified channel not open, punt
	//

	if of := r.openFiles[ioch]; of == nil {
		runtimeError(ENOTOPEN)
	}

	//
	// If field exists, use it, else gin up an empty one
	//

	if fldp = r.fieldMap[ioch]; fldp == nil {
		fldp = &field{}
	}

	//
	// Calculate where the next sub-record goes
	//

	for i := 0; i < len(fldp.fldel); i++ {
		fldelp := &fldp.fldel[i]
		for j := 0; j < len(fldelp.flde); j++ {
			goffset += fldelp.flde[j].flen
		}
	}

	for tp := args[1]; tp != nil; tp = tp.next {
		if args[1].token != FIELDELEMENT {
			unexpectedTokenError(args[1].token)
		}

		op0 := tp.operands[0]
		if op0.token != NRPN {
			unexpectedTokenError(op0.token)
		} else {
			flen = anyToInt(evaluateRpnExpr(op0, false))
		}

		op1 := tp.operands[1]
		lval := evaluateRpnExpr(op1, true).(lhsRetVal)
		sym = lval.sym

		flde := fieldElement{fieldVar: sym, subs: lval.subs,
			offset: offset + goffset, flen: int16(flen)}

		sym.flde = &flde

		offset += int16(flen)

		fldel.flde = append(fldel.flde, flde)
	}

	runtimeCheck(offset < blockSize, "FIELD overflow")

	fldp.fldel = append(fldp.fldel, fldel)

	r.fieldMap[ioch] = fldp
}

func executeRandomize() {
}

//
// So originally we had STOP causing a nil execution state, so the
// execution loop would terminate.  Unfortunately, this does NOT work
// well if STOP is used after THEN or ELSE, since the contract with
// executeIf states that executeIf will return nil unless the verb
// after THEN or ELSE transfer control.  It's seriously ugly to try to
// band-aid around that.  What we do instead is call exitToPrompt.
// We need to explicitly set r.nextStmt here in case the user enters
// the CONT command.  This only works because STOP cannot be part of
// a chain of multiple statements
//

func executeStop() {

	msg := fmt.Sprintf("STOP at line %s", decodeStmtNoString(r.curStmt))

	r.nextStmt = stmtAvlTreeNextStmt(r.curStmt)

	exitToPrompt(msg)
}

func executeMat(args []*tokenNode) {

	basicAssert(len(args) == 1, "MAT botch")

	opcode := args[0].token
	ops := args[0].operands
	tops := make([]*tokenNode, 1)

	switch opcode {
	default:
		unexpectedTokenError(opcode)

	case EQ:
		//	godump.Dump(args)
		matAssign(ops)

	case INPUT:
		fallthrough
	case READ:
		for tp := ops[0]; tp != nil; tp = tp.next {
			tops[0] = tp
			matOperate(opcode, tops)
		}

	case PRINT:
		matOperate(opcode, ops)
	}
}

func executeChange(curStmt *stmtNode) {

	var i int16
	var str string

	dims := make([]int16, 1)

	numOperands := len(curStmt.operands)

	basicAssert(numOperands == 2,
		fmt.Sprintf("CHANGE expected 2 operands got %d", numOperands))

	op0 := curStmt.operands[0]
	op1 := curStmt.operands[1]

	if isString(op0) && isNumeric(op1) {
		sym := lookupSymbolRef(op1, 1)
		if sym == nil {
			dims[0] = maxImplicitSubscript
			sym = createSymbol(op1, dims...)
		}

		if op0.token == STRING {
			str = op0.tokenData.(string)
		} else {
			str = lookupSymbolValue(op0).(string)
		}

		checkSubscript(int16(len(str)), sym.dims[0])

		for i = 0; i <= int16(len(str)); i++ {
			switch op1.token {
			case FVAR:
				if i == 0 {
					storeFloatVar(sym, float64(len(str)))
				} else {
					storeFloatVar(sym, float64(str[i-1]), i)
				}

			case IVAR:
				if i == 0 {
					storeIntVar(sym, int16(len(str)))
				} else {
					storeIntVar(sym, int16(str[i-1]), i)
				}

			default:
				unexpectedTokenError(op1.token)
			}

		}
	} else if isNumeric(op0) && isString(op1) {
		lsym := lookupSymbolRef(op0, dims...)
		if lsym == nil {
			dims[0] = maxImplicitSubscript
			lsym = createSymbol(op0, dims...)
		}

		rsym := lookupSymbolRef(op1)

		var iMax, i int16

		switch op0.token {
		default:
			unexpectedTokenError(op0.token)

		case FVAR:
			iMax = int16(fetchFloatVar(lsym))

		case IVAR:
			iMax = fetchIntVar(lsym)
		}

		for i = 1; i <= iMax; i++ {
			var ch rune

			switch op0.token {
			default:
				unexpectedTokenError(op0.token)

			case FVAR:
				ch = rune(fetchFloatVar(lsym, i))

			case IVAR:
				ch = rune(fetchIntVar(lsym, i))
			}

			str += string(ch)
		}
		storeStringVar(rsym, str, false)
	} else {
		fatalError("Incompatible arguments")
	}
}

//
// Ugly (or clever) hack
//
// There are 2 forms of FOR.  One form has a 'TO' termination expression,
// and the other has a boolean termination expression.  The FOR node has
// 3 or 4 operands.  3 if there if no STEP expression, 4 if there is.
// Because the TO and the boolean forms are mutually exclusive, the 3rd
// operand is either the TO expression or the boolean.  The runtime code
// can tell what is going on because the TO case has a simple numeric
// expression, whereas the WHILE/UNTIL case has a WHILE or UNTIL operator
// as the last item in the RPN list
//

func executeFor(curStmt *stmtNode, arg any) *procState {

	var res [5]any
	var fsp *forStackNode
	var fsIdx int
	var lastToken int
	var stmt *stmtNode

	ret := &procState{}

	// arg might be nil so default to false
	iterating, _ := arg.(bool)

	loopVar := getLoopVar(curStmt)

	if !iterating {

		//
		// Hitting the FOR statement from outside the loop is tricky:
		// If the loop variable matches that of an entry on the FOR
		// statement stack, there are 2 possibilities:
		// 1. The statement number is different - reject as a duplicate FOR
		// 2. The statement number is the same - we have to assume that the
		//    loop was exited via a GOTO or somesuch and treat this as a
		//    brand-new loop
		//

		fsIdx, fsp = findForStackEntryVar(loopVar)
		if fsp != nil {
			runtimeCheck(fsp.stmt == curStmt, "Duplicate FOR statement")
			popForStackEntry(fsIdx)
		}

		runtimeCheck(len(r.forStack) < forStackMax, "FOR stack overflow")

		res[0] = evaluateRpnExpr(curStmt.operands[0], true)
		res[1] = evaluateRpnExpr(curStmt.operands[1], false)

		//
		// Tricky: if the termination expression is for a WHILE or UNTIL
		// we do not evaluate it here, just stash it for later.
		// If the termination expression is not WHILE or UNTIL, we need
		// to evaluate it (and store the result) before executing the
		// loop.  Since the expressions are always RPN, this means that
		// the last token in the expression will be WHILE, UNTIL or
		// something else
		//

		lastToken = fetchForTerminationToken(curStmt.operands[2])
		if lastToken != WHILE && lastToken != UNTIL {
			res[2] = evaluateRpnExpr(curStmt.operands[2], false)
		} else {
			res[2] = curStmt.operands[2]
		}

		//
		// If there is no STEP expression, gin up a +1 of the
		// appropriate type
		//

		if len(curStmt.operands) == 3 {
			if isInt(res[0]) {
				res[3] = int16(1)
			} else {
				res[3] = float64(1.0)
			}
		} else {
			var zeroStep bool

			res[3] = evaluateRpnExpr(curStmt.operands[3], false)
			if isInt(res[3]) {
				if res[3].(int16) == 0 {
					zeroStep = true
				}
			} else if res[3].(float64) == 0.0 {
				zeroStep = true
			}

			runtimeCheck(!zeroStep, "STEP expression must be non-zero")
		}

		nextStmt := findNext(curStmt)

		runtimeCheck(nextStmt != nil, "No matching NEXT")

		processLhs(res[0], res[1])

		fsp = &forStackNode{stmt: curStmt, nextStmt: nextStmt,
			item: res, lastToken: lastToken}

		r.forStack = append(r.forStack, fsp)

		//
		// By definition if we get here, fsIdx must be -1, but if the
		// loop never executes at all, we would try to pop entry -1
		// from the FOR stack, crashing.  Since we're appending the
		// newly created FOR stack entry, fsIdx must be the last one
		//

		if fsIdx < 0 {
			fsIdx = len(r.forStack) - 1
		}
	} else {
		fsIdx, fsp = findForStackEntryVar(loopVar)
		lastToken = fsp.lastToken
	}

	//
	// Check to see if the loop should terminate.  For a standard TO
	// loop, we need to restore the previous loop variable (another
	// BASIC oddity)
	//

	switch lastToken {
	default:
		if checkLoopTermination(fsp) {
			restoreLoopVar(fsp)
			stmt = fsp.nextStmt
			popForStackEntry(fsIdx)
		}

	case WHILE:
		termExpr := evaluateRpnExpr(fsp.item[2].(*tokenNode), false)
		if termExpr.(int16) == 0 {
			stmt = fsp.nextStmt
			popForStackEntry(fsIdx)
		}

	case UNTIL:
		termExpr := evaluateRpnExpr(fsp.item[2].(*tokenNode), false)
		if termExpr.(int16) != 0 {
			stmt = fsp.nextStmt
			popForStackEntry(fsIdx)
		}
	}

	//
	// If stmt is non-nil, we need to look up the *stmtNode for the
	// successor of our matching NEXT (which shouldn't be nil,
	// since executeRun requires an END statement as the highest
	// numbered statement in the program, but even if it is nil,
	// somehow, executeRun will just terminate
	//

	if stmt != nil {
		ret = createExecutionState(computeNextStmt(stmt))
	}

	return ret
}

func executeNext(curStmt *stmtNode) *stmtNode {

	runtimeCheck(len(r.forStack) > 0, "FOR stack underflow")

	_, fsp := findForStackEntryVar(getLoopVar(curStmt))
	if fsp != nil {
		incrementLoopVar(fsp)
		return fsp.stmt
	}

	runtimeError("NEXT statement without matching FOR")

	panic(nil) // avoid compiler complaint
}

func executeRead(curStmt *stmtNode) {

	for op := curStmt.operands[0]; op != nil; op = op.next {

		dataItem := readDataItem()
		sym := lookupSymbolRef(op)

		//
		// NB: we don't need to sanity check op.token since the call
		// to lookupSymbolRef we just made will throw a runtime error
		// if it isn't one of the 3 scalar variable types
		//

		switch op.token {
		case FVAR:
			val, ok := dataItem.(float64)
			runtimeCheck(ok, EDATATYPEERROR)
			storeFloatVar(sym, val)

		case IVAR:
			val, ok := dataItem.(int16)
			runtimeCheck(ok, EDATATYPEERROR)
			storeIntVar(sym, val)

		case SVAR:
			val, ok := dataItem.(string)
			runtimeCheck(ok, EDATATYPEERROR)
			storeStringVar(sym, val, false)
		}
	}
}

//
// This routine should be passed a slice of length 3.
// The first slice element is LINE if doing INPUT LINE or nil
// if vanilla INPUT.
// The second slice element is a numeric (NRPN) expression
// if doing I/O to/from a channel, or nil if to/from the terminal.
// The third slice element is a tokenList of expressions, which
// should be numeric (NRPN) or string (SRPN) expressions, in addition
// to separators such as COMMA, etc.  In the case of INPUT LINE,
// this must be a single string variable
//

func executeInput(args []*tokenNode) {

	var doPair bool
	var sym *symtabNode
	var nextOp *tokenNode
	var inputLine string
	var inputToken string
	var ioch int

	prompt := executePrompt

	//
	// Ugliness forced on us by the BASIC-PLUS manual.  As we scan
	// the list of input items from left to right, if an item is a
	// string literal, it's a prompt for the next item, which must
	// be an input variable.  In this scenario, the input items MUST
	// be alone on the input line.  e.g. the only time that we can
	// provide multiple items on a line, separated by commas, is if
	// none of said input variables is paired with a prompt string
	//

	basicAssert(len(args) == 3, "INPUT botch")

	if args[1] == nil {
		ioch = 0
	} else if args[1].token == NRPN {
		ioch = evaluateIntegerExpr(args[1])
	} else {
		unexpectedTokenError(args[1].token)
	}

	//
	// INPUT LINE is much simpler, so handle that here and return
	//

	if args[0] != nil {
		if args[0].token != LINE {
			unexpectedTokenError(args[0].token)
		}

		op := args[2]
		basicAssert(op.next == nil && op.token == SVAR, "INPUT LINE botch")

		storeStringVar(lookupSymbolRef(op), readInputLine(ioch, prompt), false)

		return
	}

	for op := args[2]; op != nil; op = nextOp {
		nextOp = op.next
		prompt = executePrompt

		switch op.token {
		default:
			unexpectedTokenError(op.token)

		case INPUTPAIR:
			doPair = true
			prompt = op.operands[0].tokenData.(string) + prompt
			sym = lookupSymbolRef(op.operands[1])

		case FVAR, IVAR, SVAR:
			sym = lookupSymbolRef(op)
		}

		//
		// If processing an INPUTPAIR, we have a string prompt,
		// followed by a variable.  Only one of these is allowed
		// on any input line
		//

		if doPair {
			inputVariable(ioch, prompt, sym)
			doPair = false
			continue
		}

		if len(inputLine) == 0 {
			inputLine = readInputLine(ioch, prompt)
		}

		idx := strings.IndexRune(inputLine, ',')
		if idx < 0 {
			inputToken = inputLine
			inputLine = ""
		} else {
			inputToken = inputLine[0:idx]
			inputLine = strings.Clone(inputLine[idx+1:])
		}

		inputToken = strings.TrimSpace(inputToken)

		switch sym.vType {
		case FVAR:
			storeFloatVar(sym, convertFloat(inputToken))

		case IVAR:
			storeIntVar(sym, convertInt16(inputToken))

		case SVAR:
			storeStringVar(sym, inputToken, false)
		}
	}
}

//
// Functions to convert strings to various numeric formats
// If the conversion is unsuccessful, print an error and
// abort to command level
//

func convertFloat(s string) float64 {

	f, err := strconv.ParseFloat(s, 64)
	if err != nil {
		if err.(*strconv.NumError).Err == strconv.ErrRange {
			runtimeError(EFLOATINGERROR)
		} else {
			runtimeError(EILLEGALNUMBER)
		}
	} else {
		return f
	}

	panic(nil) // avoid compiler complaint
}

func convertInt16(s string) int16 {

	i, err := strconv.ParseInt(s, 10, 16)
	if err != nil {
		if err.(*strconv.NumError).Err == strconv.ErrRange {
			runtimeError(EINTEGERERROR)
		} else {
			runtimeError(EILLEGALNUMBER)
		}
	} else {
		return int16(i)
	}

	panic(nil) // avoid compiler complaint
}

//
// This function reads a line from the terminal, parsing as required
//

func inputVariable(ioch int, prompt string, sym *symtabNode) {

	input := readInputLine(ioch, prompt)

	switch sym.vType {
	case FVAR:
		storeFloatVar(sym, convertFloat(input))

	case IVAR:
		storeIntVar(sym, convertInt16(input))

	case SVAR:
		storeStringVar(sym, input, false)
	}
}

//
// This function is a more user-friendly version of readLine.
// It handles blank lines and EOF (ignoring those and re-reading)
// The prompt is ignored if reading from a formatted file
//

func readInputLine(ioch int, prompt string) string {

	var input string
	var err error

	if ioch == 0 {
		if err = g.inputLiner.SetTimeout(r.ioTimeout); err != nil {
			fatalError(err.Error())
		}
		input, _ = readLine(g.inputLiner, prompt, false)
		checkInterrupts()
	} else {
		of := getOpenFile(ioch)

		checkIOMode(of, IOREAD)

		//
		// Do not allow formatted input from a record file!
		//

		runtimeCheck(of.fileType != recordFile, EPROTECTIONVIOLATION)

		if input, err = of.reader.ReadString('\n'); err != nil {
			if err.Error() == "EOF" {
				runtimeError(EENDOFFILE)
			} else {
				runtimeError(mapOSError(err).Error())
			}
		}
	}

	if bytes.ContainsRune([]byte(input), ctrlZ) {
		runtimeError(EENDOFFILE)
	}

	return strings.TrimSpace(input)
}

//
// This routine should be passed a slice of length 3.
// The first slice element is a numeric (NRPN) expression
// if doing I/O to/from a channel, or nil if to/from the terminal.
// The second slice element is a string expression for PRINT USING,
// or nil if vanilla PRINT
// The third slice element is a tokenList of expressions, which
// should be numeric (NRPN) or string (SRPN) expressions, in addition
// to separators such as COMMA, etc...
//
// 5 cases:
// 1. empty print => [nil, nil, nil]
// 2. vanilla print => [nil, nil, tokenList]
// 3. print using to/from terminal => [nil, SRPN, tokenList]
// 4. vanilla print to/from I/O channell => [NRPN, nil, tokenList]
// 5. print using to/from I/O channell => [NRPN, SRPN, tokenList]
//

func executePrint(args []*tokenNode) {

	var printBuf string
	var tp *tokenNode
	var prtuList []any
	var tokList []prtuToken
	var ioch int

	basicAssert(len(args) == 3, "PRINT botch")

	if args[0] == nil && args[1] == nil && args[2] == nil {
		fmt.Println()
		return
	}

	//
	// Set up ioch if any
	//

	if args[0] == nil {
		ioch = 0
	} else if args[0].token == NRPN {
		ioch = evaluateIntegerExpr(args[0])
	} else {
		unexpectedTokenError(args[0].token)
	}

	//
	// The manual states that PRINT USING will accept a trailing
	// semicolon, doing the obvious.  Does not mention a trailing
	// comma though.  Given that PRINT USING is supposed to print
	// a precisely formatted string, we ignore either in the case
	// of PRINT USING, since it makes the parser cleaner
	//

	if args[1] == nil {
		// vanilla print
	} else if args[1].token == SRPN {
		fmtStr := evaluateStringExpr(args[1])
		prtuCtl := prtuLexer{buf: fmtStr}

		prtuParse(&prtuCtl)

		for i := 0; i < len(prtuCtl.tokens); i++ {
			tokList = append(tokList, prtuCtl.tokens[i])
		}

		//
		// The parser will hand us a full-blown list with comma,
		// semicolon, etc.  Ignore anything except numeric or
		// string expressions
		//

		for tp = args[2]; tp != nil; tp = tp.next {
			if tp.token == NRPN || tp.token == SRPN {
				prtuList = append(prtuList, evaluateRpnExpr(tp, false))
			}
		}

		printUsing(ioch, tokList, prtuList)

		return
	} else {
		unexpectedTokenError(args[1].token)
	}

	printNL := true

	for tp = args[2]; tp != nil; tp = tp.next {
		switch tp.token {
		default:
			unexpectedTokenError(tp.token)

		case NRPN:
			res := evaluateRpnExpr(tp, false)
			printBuf = basicFormat(res)
			basicPrint(printBuf, ioch, false)

		case SRPN:
			res := evaluateRpnExpr(tp, false).(string)
			basicPrint(res, ioch, false)
			if len(res) == zoneWidth && ioch == 0 {
				basicPrint("", ioch, true)
			}

		case DCOMMA:
			basicPrint("", ioch, true)
			fallthrough

		case COMMA:
			basicPrint("", ioch, true)

		case SEMI:
			// NOP

		case TRAILING_COMMA:
			p.trailingOp = tp.token
			basicPrint("", ioch, true)
			printNL = false

		case TRAILING_SEMI:
			printNL = false
		}
	}

	if printNL && ioch == 0 {
		resetPrint(true)
	}
}

func executeIf(curStmt *stmtNode) *procState {

	var tp *tokenNode
	var stmt *stmtNode

	ret := createExecutionState(nil)

	operands := fetchOperands(curStmt)

	ifRes := evaluateBooleanExpr(operands[0])
	if ifRes {
		tp = operands[1]
	} else if len(operands) == 3 {
		tp = operands[2]
	}

	if tp == nil {
		basicAssert(!ifRes, "No THEN clause")
		return ret
	}

	if tp.token != STMT {
		unexpectedTokenError(tp.token)
	}

	stmt = tp.tokenData.(*stmtNode)

	switch stmt.token {
	default:
		unexpectedTokenError(stmt.token)

	case CLOSE:
		executeClose(stmt.operands)

	case GOSUB:
		ret = createExecutionState(executeGosub(stmt.operands[0]))

	case GOTO:
		ret = createExecutionState(executeGoto(stmt.operands[0]))

	case KILL:
		executeKill(stmt.operands)

	case LET:
		executeLet(createExecutionState(stmt))

	case OPEN:
		executeOpen(stmt.operands)

	case PRINT:
		executePrint(stmt.operands)

	case RANDOMIZE:
		executeRandomize()

	case RESTORE:
		executeRestore()

	case RESUME:
		if len(stmt.operands) == 0 {
			ret = executeResume(nil)
		} else {
			ret = executeResume(stmt.operands[0])
		}

	case RETURN:
		ret = createExecutionState(executeReturn())

	case SLEEP:
		executeSleep(stmt.operands)

	case STOP:
		executeStop()
		fatalError("executeStop returned")

	case WAIT:
		executeWait(stmt.operands)

	}

	return ret
}

func executeKill(args []*tokenNode) {

	basicAssert(len(args) == 1, "KILL botch")

	filename := evaluateStringExpr(args[0])

	//
	// This is really ineffcient.  It would be nice to be able
	// to look up open files by filenum OR name, but GO maps
	// don't support that.  This is not a performance critical
	// code path, so we don't bother with a second map, we just
	// iterate through the entire map, which is no big deal, since
	// there are no more than 12 entries anyway, and this is only
	// a sanity check
	//

	for _, fp := range r.openFiles {
		if fp.filename == filename {
			runtimeError(EFILEINUSE)
		}
	}

	if err := fileRemove(filename); err != nil {
		runtimeError(err.Error())
	}
}

func executeSet(args []*tokenNode, leftPad bool) {

	basicAssert(len(args) == 2, "SET botch")

	for tp := args[0]; tp != nil; tp = tp.next {
		lval := evaluateRpnExpr(tp, true).(lhsRetVal)
		val := evaluateRpnExpr(args[1], false).(string)

		storeStringVar(lval.sym, val, true, lval.subs...)
	}
}

func executeLet(state *procState) {

	operands := fetchOperands(state.stmt)

	state.expr = operands[0].tokenData.(tokenList)
	lval := evaluateRpnExprInternal(state, true)

	resetRpnStack(&state.stack)

	state.expr = operands[1].tokenData.(tokenList)
	rval := evaluateRpnExprInternal(state, false)

	processLhs(lval, rval)
}

func processLhs(lval, rval any) {

	if lval == nil {
		udStkNode := &r.userDefStack[len(r.userDefStack)-1]
		udStkNode.retval = rval

		return
	}

	lhsRet := lval.(lhsRetVal)
	sym := lhsRet.sym

	switch sym.vType {
	default:
		fatalError(fmt.Sprintf("Invalid symbol type %d", sym.vType))

	case FVAR:
		if isInt(rval) {
			storeFloatVar(sym, float64(rval.(int16)), lhsRet.subs...)
		} else {
			storeFloatVar(sym, rval.(float64), lhsRet.subs...)
		}

	case IVAR:
		if isInt(rval) {
			storeIntVar(sym, rval.(int16), lhsRet.subs...)
		} else {
			storeIntVar(sym, floatToInt16(rval.(float64)), lhsRet.subs...)
		}

	case SVAR:
		storeStringVar(sym, rval.(string), false, lhsRet.subs...)
	}
}

func executeOnError(args []*tokenNode) {

	if len(args) == 0 {
		r.onErrorStmtNo = 0
		return
	}

	targetStmtNo := args[0].tokenData.(int16)

	if targetStmtNo != 0 {
		checkStmtTargetScope(targetStmtNo)
		targetStmt := stmtAvlTreeLookup(targetStmtNo, cmpInt16Key)
		runtimeCheck(targetStmt != nil,
			fmt.Sprintf("ON ERROR GOTO with non-existent statement %d",
				targetStmtNo))
	}

	r.onErrorStmtNo = targetStmtNo
}

func executeOpen(args []*tokenNode) {

	var err error
	var basFileOk bool
	var fp *file

	basicAssert(len(args) == 3, "OPEN botch")

	filename := evaluateStringExpr(args[0])

	if args[1].token != INTEGER {
		unexpectedTokenError(args[1].token)
	}

	iomode := int(args[1].tokenData.(int16))

	switch iomode {
	default:
		fatalError(fmt.Sprintf("Invalid iomode == %0x\n", iomode))

	case IOREAD:
		basFileOk = true

	case iomode | IOWRITE:
		basFileOk = false
	}

	filenum := anyToInt(evaluateRpnExpr(args[2], false))

	checkFilenum(filenum)

	suffix, ok := getFilenameSuffix(filename)
	if !ok {
		runtimeError(EILLEGALFILENAME)
	} else if !basFileOk && suffix == basFileSuffix {
		runtimeError(EPROTECTIONVIOLATION)
	}

	if fp, err = openFileFull(filename, iomode, false); err != nil {
		runtimeError(err.Error())
	}

	runtimeCheck(r.openFiles[filenum] == nil, EALREADYOPEN)

	r.openFiles[filenum] = fp
}

func executeOn(curStmt *stmtNode) *stmtNode {
	numStmts := len(curStmt.operands) - 1
	var ret *stmtNode

	basicAssert(numStmts > 0, "Missing expression node")

	switch curStmt.token {
	default:
		unexpectedTokenError(curStmt.token)

	case ONGOTO, ONGOSUB:
	}

	idx := evaluateIntegerExpr(curStmt.operands[0])
	runtimeCheck(idx >= 1 && idx <= numStmts, EONERROR)

	//
	// We have to do the following here, rather than executeStmt because
	// we don't yet know which statement number to transfer to
	//

	op := curStmt.operands[idx]
	checkStmtTargetScope(op.tokenData.(int16))

	switch curStmt.token {
	default:
		unexpectedTokenError(curStmt.token)

	case ONGOTO:
		ret = executeGoto(op)

	case ONGOSUB:
		ret = executeGosub(op)
	}

	return ret
}

func executeGoto(tnode *tokenNode) *stmtNode {

	stmtNo := tnode.tokenData.(int16)

	stmt := stmtAvlTreeLookup(stmtNo, cmpInt16Key)
	runtimeCheck(stmt != nil,
		fmt.Sprintf("GOTO to non-existent statement %d", stmtNo))

	return stmt
}

func executeGosub(tnode *tokenNode) *stmtNode {

	targetStmtNo := tnode.tokenData.(int16)
	targetStmt := stmtAvlTreeLookup(targetStmtNo, cmpInt16Key)

	runtimeCheck(targetStmt != nil,
		fmt.Sprintf("GOSUB to non-existent statement %d",
			targetStmtNo))
	runtimeCheck(len(r.gosubStack) < gosubStackMax, "GOSUB stack overflow")

	r.gosubStack = append(r.gosubStack, r.curStmt)

	return targetStmt
}

func executeResume(tnode *tokenNode) *procState {

	var stmtNo int16

	//
	// We need to make sure to clear the fault info before returning,
	// in case another runtime exception is thrown
	//

	fip := r.fip
	r.fip = nil

	runtimeCheck(fip != nil, "No error handler active")

	//
	// If resuming to the faulted statement, reset the execution
	// state structure, since the manual states that RESUME will
	// re-execute the offending statement from the beginning.
	// If the exception was an interrupt, a statement number
	// is required, as otherwise we could have an infinite loop
	//

	if tnode != nil {
		stmtNo = tnode.tokenData.(int16)
	} else {
		stmtNo = 0
	}

	if stmtNo == 0 {
		runtimeCheck(getErrorMsg(fip.err) != EINTERRUPTED,
			"RESUME from interrupt requires a statement number")
		return createExecutionState(fip.state.stmt)
	}

	stmt := stmtAvlTreeLookup(stmtNo, cmpInt16Key)

	runtimeCheck(stmt != nil,
		fmt.Sprintf("RESUME to non-existent statement %d", stmtNo))

	return createExecutionState(stmt)
}

func executeReturn() *stmtNode {

	var tmp []*stmtNode

	runtimeCheck(len(r.gosubStack) > 0, "GOSUB stack underflow")

	ret := r.gosubStack[len(r.gosubStack)-1]

	tmp = append(tmp, r.gosubStack[:len(r.gosubStack)-1]...)
	r.gosubStack = tmp

	return ret
}

func processStmtList(stmtList *tokenNode, delete bool) {

	for node := stmtList; node != nil; node = node.next {
		switch node.token {
		default:
			unexpectedTokenError(node.token)

		case INTEGER:
			processStmtNode(node.tokenData.(int16), delete)

		case INTPAIR:
			stmtStart := node.operands[0].tokenData.(int16)
			stmtEnd := node.operands[1].tokenData.(int16)

			processStmtRange(stmtStart, stmtEnd, delete)
		}
	}
}

func executeDelete(stmtList *tokenNode) {
	processStmtList(stmtList, true)
}

func executeList(stmtList *tokenNode, brief bool) {

	if !brief {
		printVersionInfo()
	}

	//
	// If the parser passed us a nil statement list, fake up an INTPAIR
	// with the range 1-math.MaxInt16
	//

	if stmtList == nil {
		firstStmtNode := makeTokenNode(INTEGER, int16(1))
		lastStmtNode := makeTokenNode(INTEGER, int16(math.MaxInt16))
		stmtList = makeTokenNode(INTPAIR, firstStmtNode, lastStmtNode)
	}

	processStmtList(stmtList, false)
}

func evaluateIntegerExpr(node *tokenNode) int {
	res := evaluateNumericExpr(node)

	switch res := res.(type) {
	default:
		unexpectedTypeError(res)
		panic(nil) // avoid compiler complaint

	case int16:
		return int(res)

	case float64:
		return floatToInt(res)
	}
}

func evaluateBooleanExpr(tnode *tokenNode) bool {

	var f float64

	expr := evaluateNumericExpr(tnode)
	switch expr := expr.(type) {
	default:
		unexpectedTypeError(expr)

	case float64:
		f = expr

	case int16:
		f = float64(expr)
	}

	if f != 0 {
		return true
	} else {
		return false
	}
}

func evaluateStringExpr(tnode *tokenNode) string {

	if tnode.token != SRPN {
		unexpectedTokenError(tnode.token)
	}

	return evaluateRpnExpr(tnode, false).(string)
}

func evaluateNumericExpr(tnode *tokenNode) any {

	if tnode.token != NRPN {
		unexpectedTokenError(tnode.token)
	}

	return evaluateRpnExpr(tnode, false)
}

func computeFix(f float64) float64 {

	return computeSgn(f) * computeInt(math.Abs(f))
}

func computeInt(f float64) float64 {

	return math.Floor(f)
}

func computeSgn(f float64) float64 {
	if f < 0.0 {
		return -1.0
	} else if f > 0.0 {
		return 1.0
	} else {
		return 0.0
	}
}

func boolToInt16(b bool) int16 {

	if b {
		return boolInt16True
	} else {
		return boolInt16False
	}
}

func fixupBoolInt16(num int16) int16 {

	if num == 0 {
		return boolInt16False
	} else {
		return boolInt16True
	}
}

func fetchForTerminationToken(tnode *tokenNode) int {

	if tnode.token != NRPN {
		unexpectedTokenError(tnode.token)
	}

	tokenList := tnode.tokenData.(tokenList)

	token := tokenList[len(tokenList)-1]
	switch token := token.(type) {
	default:
		fatalError(fmt.Sprintf("Unexpected type %T\n", token))
		panic(nil) // avoid compiler complaint

	case fvarToken, float64:
		return FLOAT

	case ivarToken, int16:
		return INTEGER

	case int:
		return token
	}
}

//
// Given a FOR statement node, search forward in the program for
// the matching NEXT.
// Complication: if there is in fact a matching NEXT, it may not
// have a statement number (e.g. it might be in a multi-statement
// line
//

func findNext(curStmt *stmtNode) *stmtNode {

	var stmt *stmtNode

	forLoopVar := getLoopVar(curStmt)

	//
	// Keep scanning until we either find a NEXT statement with a
	// matching loop variable, or we run off the end of the program.
	// If there is a chained stmt node, look at that, else advance
	// to the next statement in the AVL tree
	//

	for stmt = computeNextStmt(curStmt); stmt != nil; stmt = computeNextStmt(stmt) {
		loopVar := getLoopVar(stmt)
		if loopVar == forLoopVar {
			break
		}
	}

	return stmt
}

//
// Extract the loop variable for the statement node passed in
//

func getLoopVar(stmt *stmtNode) string {

	if stmt.token != FOR && stmt.token != NEXT {
		return ""
	}

	op0 := stmt.operands[0]

	tl0 := op0.tokenData.(tokenList)[0]

	switch tl0.(type) {
	default:
		unexpectedTypeError(tl0)
		panic(nil) // avoid compiler complaint

	case fvarToken, ivarToken:
		return getVarName(tl0)
	}
}

//
// This function takes a *stmtNode and determines the next *stmtNode
// to execute.  If there is another statement on the same line, we
// use that, otherwise, we look up the next numbered statement in the
// program tree, else nil
//

func computeNextStmt(curStmt *stmtNode) *stmtNode {

	var nextStmt *stmtNode

	if curStmt.next != nil {
		nextStmt = curStmt.next
	} else {
		nextStmt = stmtAvlTreeNextStmt(curStmt)
	}

	return nextStmt
}

//
// Increment the lvalue whose reference is passed in by the expression
// Before we increment the target, save its current value in the 5th
// slot.  This is necessary because when a BASIC FOR loop terminates,
// the loop variable is the last value, not the one which caused it to
// terminate.  Blech...
//
// For a floating loop index, we need to ensure we don't have an infinite
// loop, which can happen if the loop value gets too big.  e.g. X+1 = X.
// For an integer loop index, we need to check that the loop index will
// not overflow or underflow
//

func incrementLoopVar(fsp *forStackNode) {

	sym := fsp.item[0].(lhsRetVal).sym
	step := fsp.item[3]

	switch sym.vType {
	default:
		fatalError(fmt.Sprintf("Invalid symbol type %d", sym.vType))

	case FVAR:
		fval := fetchFloatVar(sym)
		fstep := step.(float64)
		fsp.item[4] = fval

		runtimeCheck(!floatValuesApproxEqual(fval+fstep, fval),
			"Infinite loop detected")

		storeFloatVar(sym, fval+fstep)

	case IVAR:
		ival := fetchIntVar(sym)
		istep := step.(int16)
		itemp := int(ival) + int(istep)
		good := true

		if istep > 0 {
			if itemp > maxForInteger {
				good = false
			}
		} else if istep < 0 {
			if itemp < minForInteger {
				good = false
			}
		}

		runtimeCheck(good, EFOROVERFLOW)

		fsp.item[4] = ival
		storeIntVar(sym, int16(itemp))
	}
}

//
// Restore the saved loop value
//

func restoreLoopVar(fsp *forStackNode) {

	sym := fsp.item[0].(lhsRetVal).sym
	savedVal := fsp.item[4]

	//
	// If the saved value is nil, we never executed the loop
	// at all, so do nothing
	//

	if savedVal == nil {
		return
	}

	switch sym.vType {
	default:
		fatalError(fmt.Sprintf("Invalid symbol type %d", sym.vType))

	case FVAR:
		storeFloatVar(sym, savedVal.(float64))

	case IVAR:
		storeIntVar(sym, savedVal.(int16))
	}
}

//
// Given a variable, search the FOR stack for a matching entry.
// If we don't find one, return nil
//

func findForStackEntryVar(loopVar string) (int, *forStackNode) {

	for i, fsp := range r.forStack {
		if getLoopVar(fsp.stmt) == loopVar {
			return i, fsp
		}
	}

	return -1, nil
}

//
// This function pops an entry off of the FOR stack.  If there are
// any subsidiary FOR entries, those will be popped as well
//

func popForStackEntry(fsIdx int) {

	var tmp []*forStackNode

	if fsIdx == 0 {
		r.forStack = nil
	} else {
		tmp = append(tmp, r.forStack[:fsIdx]...)
		r.forStack = tmp
	}
}

//
// This function examines the state of a FOR loop stack node and
// returns a boolean indicating whether the loop should terminate
// NB: the step expression can't be zero here (this is rejected much
// earlier in the process
//

func checkLoopTermination(fsp *forStackNode) bool {

	sym := fsp.item[0].(lhsRetVal).sym
	to := fsp.item[2]
	step := fsp.item[3]

	switch sym.vType {
	default:
		fatalError(fmt.Sprintf("Invalid symbol type %d", sym.vType))

	case FVAR:
		loopVar := fetchFloatVar(sym)
		fto := to.(float64)
		fstep := step.(float64)

		if fstep > 0.0 {
			if loopVar > fto {
				return true
			}
		} else {
			if loopVar < fto {
				return true
			}
		}

	case IVAR:
		loopVar := fetchIntVar(sym)
		ito := to.(int16)
		istep := step.(int16)

		if istep > 0 {
			if loopVar > ito {
				return true
			}
		} else {
			if loopVar < ito {
				return true
			}
		}
	}

	return false
}

//
// This function prints an error message, but calls panic with a special
// argument, as we want to crawl back to command prompt without doing
// any of the usual runtimeError stuff.  This is needed for cases where
// we are executing, but there is no valid statement to diagnose, as well
// as when the parser wants to diagnose a syntax error of some sort
//

func exitToPrompt(m string) {

	fmt.Println(m)

	panic(&crawloutException{true})
}
