%{

package main

import ("math")

var parsingUneg bool

%}

%union {
  stringVal string
  intVal int
  int64Val int64
  float64Val float64
  snodeVal *stmtNode
  tnodeVal *tokenNode
}

//
// There are a number of tokens defined here that are never
// returned by the lexer - they are present to faciliate various
// action rules
//

//
// The following section is tokens that represent actual keywords
// that are returned by the lexer.  We split them out, because
// otherwise, when the low-level scanner sees a 'word' such as 'LT',
// it would otherwise return the token LT, which is supposed to be
// returned when the lexer sees '<'.  If we allow that, then a syntactic
// construct such as '100 if foo lt bar then 1000' would be accepted
// as legitimate by the parser
//

%token ABS
%token AS
%token ASSERT
%token ASCII
%token AND
%token ATN
%token BYE
%token CHANGE
%token CHRS
%token CLOSE
%token CLUSTERSIZE
%token CON
%token CONFIG
%token CONT
%token COS
%token COUNT
%token CVTFS
%token CVTIS
%token CVTSF
%token CVTSI
%token DATA
%token DATES
%token DEF
%token DELETE
%token DENORM
 //%token DET
%token DIM
%token DUMP
%token EDIT
%token ELSE
%token END
%token EOL
%token EQV
%token ERL
%token ERR
%token ERROR
%token EXP
%token FIELD
%token FILE
%token FILENAME
%token FIX
%token FLOAT
%token FOR
%token FNEND
%token GET
%token GOSUB
%token GOTO
%token HELP
%token IDN
%token IF
%token IMP
%token INPUT
%token INSTR
 //%token INV
%token INT
%token KILL
%token LEN
%token LEFT
%token LET
%token LINE
%token LIST
%token LISTNH
%token LOG
%token LOG10
%token LSET
%token MAT
%token MID
%token MODE
%token NEXT
%token NEW
%token NOT
%token NUMS
%token OLD
%token ON
%token OR
%token OPEN
%token OUTPUT
%token PI
%token POS
%token PRINT
%token PUT
%token READ
%token RECORD
%token RECORDSIZE
%token RELOAD
%token REM
%token RANDOMIZE
%token RENUMBER
%token RESTORE
%token RESUME
%token RETURN
%token RIGHT
%token RND
%token RSET
%token RUN
%token RUNNH
%token SAVE
%token SGN
%token SHA256
%token SHA512
%token SIN
%token SLASH
%token SLEEP
%token SPACES
%token SQR
%token STATS
%token STEP
%token STOP
%token SWAPI
%token TAB
%token TAN
%token THEN
%token TIME
%token TIMES
%token TO
%token TRACE
%token TRN
%token UNTIL
%token USING
%token VAL
%token VARS
%token WHILE
%token WAIT
%token XOR
%token ZER

//
// The following section is tokens that are not to be entered into the
// keyword map
//

%token APPROX
%token BADFILENAME
%token BADFUNCNAME
%token BADTOKEN
%token BADVARIABLE
%token CHAR
%token COLON
%token COMMA
%token COMMENT
%token CONCAT
%token DCOMMA
%token DOLLAR
%token EINTEGER
%token EQ
%token EXEC
%token FIELDELEMENT
%token FILLCHAR
%token FNFVAR
%token FNIVAR
%token FNSVAR
%token FVAR
%token GT
%token GE
%token INTEGER
%token INPUTPAIR
%token INTPAIR
%token IVAR
%token LE
%token LONGLINE
%token LPAR
%token LT
%token MINUS
%token NCALL
%token NE
%token NRPN
%token ONERROR
%token ONGOSUB
%token ONGOTO
%token PLUS
%token POUND
%token POW
%token RPAR
%token SCALL
%token SEMI
%token SRPN
%token STAR
%token STMT
%token STRGE
%token STRGT
%token STREQ
%token STRING
%token STRLE
%token STRLT
%token STRNE
%token SUBSCR
%token SUBSCR1
%token SUBSCR2
%token SVAR
%token TRAILING_COMMA
%token TRAILING_SEMI
%token UNEG
%token UPLUS
%token USTRING

// YACC precedence rules

%left IMP
%left EQV
%left OR XOR
%left AND
%left NOT
%left EQ GE GT LE LT NE APPROX
%left MINUS PLUS
%left STAR SLASH
%left UNEG UPLUS
%right POW

%%

// Grammar definition

//
// We *could* define immediate mode to accept 'statement' instead of
// 'statement_list', but then we would get a 'syntax error' message
// instead of providing our own, more friendly one
//

line:
        EOL
        {
            return 0
        }
|
        LONGLINE
        {
            errorLoc(ELINETOOLONG)
        }
|
        stmt_no EOL
        {
            // entering a line with stmt number 'nnn' and nothing else
            // is equivalent to 'DELETE nnn'

            executeDelete($<tnodeVal>1)

            return 0
        }
|
        statement_list EOL
        {
            var tp []*tokenNode

            sp := $<snodeVal>1

            basicAssert(len(sp.operands) <= 3,
                        "Too many immediate operands!")

            tp = sp.operands

            //
            // The action rule for COLON will reject any parse
            // if we are in immediate mode.  Nonetheless, check
            // to make sure we have one and only one stmtNode
            //

            basicAssert(sp.next == nil,
                        "More than one statement in immediate mode")
            
            if g.programFile != nil {
               errorLoc("Immediate mode statement not allowed in files!")
            }

            switch sp.token {
            default:
                 unexpectedTokenError(sp.token)

            case ASSERT:
                 executeAssert()

            case BYE:
                 executeBye()

            case CONFIG:
                 executeConfig()

            case CONT:
                 executeCont()
                 
            case DELETE:
                 executeDelete(tp[0])

            case DENORM:
                 executeDenorm()

            case EDIT:
                 executeEdit()

            case HELP:
                 if len(tp) == 0 {
                    executeHelp(nil)
                 } else {
                    executeHelp(tp[0])
                 }

            case KILL:
                 executeKill(tp)

            case LET:
                 executeLet(createExecutionState(sp))

            case LIST:
                 if len(tp) == 0 {
                    executeList(nil, false)
                 } else {
                    executeList(tp[0], false)
                 }

            case LISTNH:
                 if len(tp) == 0 {
                    executeList(nil, true)
                 } else {
                    executeList(tp[0], true)
                 }

            case MAT:
                 executeMat(tp)

            case NEW:
                 executeNew(tp[0])

            case OLD:
                 runtimeCheck(tp[0] != nil, "Filename required")
                 executeOld(tp[0].tokenData.(string))

            case PRINT:
                 executePrint(tp)
 
            case RELOAD:
                 executeReload()

            case RENUMBER:
                 executeRenumber(tp[0])

            case RUN:
                 executeRun(nil, false)

            case RUNNH:
                 executeRun(nil, true)

            case SAVE:
                 executeSave(tp[0])

            case STATS:
                 executeStats()

            case TRACE:
                 executeTrace(tp[0])            
            }

            return 0
        }
|
        stmt_no statement_list EOL
        {
            head := $<snodeVal>2

            for sp := head ; sp != nil ; sp = sp.next {
                if head.next != nil {
                   if sp.token == DEF || sp.token == DIM ||
                      sp.token == FNEND || sp.token == REM ||
                      sp.token == STOP {
                      errorLoc("Invalid use of multiple statements!")
                   }
                }
            }

            //
            // Ensure we're not adding a statement after an existing
            // END statement
            //

            if g.endStmtNo != 0 && deferredStmtNo > g.endStmtNo {
               errorLoc("Statement must precede END statement")
            }

            head.stmtNoTokenLoc.pos.column = 1
            head.stmtNoTokenLoc.end.column = head.tokenLoc.pos.column-2

            insertStmtNode(head, deferredStmtNo)

            //
            // The manual states that no statements following the
            // END statement are returned to the parser.
            // Close the file, ensuring that the lexer will read any
            // further tokens from the keyboard.  Due to the preceding
            // check, any numbered lines will be disallowed anyway!
            //

            if g.endStmtNo != 0 {
               closeProgramFile()
            }
           
            return 0
        }
|
        error EOL
        {
            return 1
        }

statement_list:
        statement COLON statement_list
        {
            sp1 := $<snodeVal>1
            spn := $<snodeVal>3

            if deferredStmtNo == 0 {
               errorLoc("Multiple statements not allowed in immediate mode")
            }

            sp1.next = spn
            sp1.tokenLoc = @1
            $<snodeVal>$ = sp1
        }
|
        statement
        {
            sp := $<snodeVal>1
            sp.tokenLoc = @1

            $<snodeVal>$ = sp
        }

string_val:
        string
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        string_var
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

string_var:
        svar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        svar_ref
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

nvar:
        simple_nvar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        nvar_ref        
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

nvar_ref:
        fvar_ref
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        ivar_ref
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

simple_var:
        simple_nvar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        svar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

simple_nvar_list:
        simple_nvar COMMA simple_nvar_list
        {
            tp1 := $<tnodeVal>1
            tp1.next = $<tnodeVal>3
            $<tnodeVal>$ = tp1
        }
|
        simple_nvar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
                            
simple_nvar:
        fvar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        ivar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        BADVARIABLE
        {
            errorLoc("Invalid variable!", &@1)
        }

statement:
        ASSERT
        {
            requireImmediateStatement(ASSERT, &@1)

            $<snodeVal>$ = makeStmtNode(ASSERT)
        }
|
        BYE
        {
            requireImmediateStatement(BYE, &@1)

            $<snodeVal>$ = makeStmtNode(BYE)
        }
|
        CHANGE string TO simple_nvar
        {
            requireDeferredStatement(CHANGE, &@1)

            $<snodeVal>$ = makeStmtNode(CHANGE, $<tnodeVal>2, $<tnodeVal>4)
        }
|
        CHANGE svar TO simple_nvar
        {
            requireDeferredStatement(CHANGE, &@1)

            $<snodeVal>$ = makeStmtNode(CHANGE, $<tnodeVal>2, $<tnodeVal>4)
        }
|
        CHANGE simple_nvar TO svar
        {
            requireDeferredStatement(CHANGE, &@1)

            $<snodeVal>$ = makeStmtNode(CHANGE, $<tnodeVal>2, $<tnodeVal>4)
        }
|
        COMMENT
        {
            requireDeferredStatement(COMMENT, &@1)

            $<snodeVal>$ = makeStmtNode(COMMENT)
        }
|

        close_stmt
        {
            $<snodeVal>$ = $<snodeVal>1
        }
|
        CONT
        {
            requireImmediateStatement(CONT, &@1)

            $<snodeVal>$ = makeStmtNode(CONT)
        }
|
        CONFIG
        {
            requireImmediateStatement(CONFIG, &@1)

            $<snodeVal>$ = makeStmtNode(CONFIG)
        }
|
        DATA data_list
        {
            tp2 := $<tnodeVal>2

            requireDeferredStatement(DATA, &@1)

            $<snodeVal>$ = makeStmtNode(DATA, tp2)
        }
|
        DEF fn_var fn_param_list
        {
            tp2 := $<tnodeVal>2
            tp3 := createTokenNodeSlice($<tnodeVal>3)
            tpx := make([]*tokenNode, 0)

            requireDeferredStatement(DEF, &@1)

            if len(tp3) > maxDefArgs {
               errorLoc("Too many function parameters", &@3)
            }

            tpx = append(tpx, tp2)
            tpx = append(tpx, nil)

            for ix := 0 ; ix < len(tp3) ; ix++ {
                tpx = append(tpx, tp3[ix])
            }

            $<snodeVal>$ = makeStmtNode(DEF, tpx...)
        }
|
        DEF fn_var fn_param_list EQ rpn_expr
        {
            requireDeferredStatement(DEF, &@1)

            tp2 := $<tnodeVal>2
            tp3 := createTokenNodeSlice($<tnodeVal>3)
            tp5 := $<tnodeVal>5
            tpx := make([]*tokenNode, 0)

            if len(tp3) > maxDefArgs {
               errorLoc("Too many function parameters", &@3)
            }

            if isNumeric(tp2) {
                requireNumericOperand(tp5, &@5)
            } else {
                requireStringOperand(tp5, &@5)
            }

            if tp3 != nil {
                checkDefExpr(tp3, tp5)
            }

            tpx = append(tpx, tp2)
            tpx = append(tpx, tp5)

            for ix := 0 ; ix < len(tp3) ; ix++ {
                tpx = append(tpx, tp3[ix])
            }

            $<snodeVal>$ = makeStmtNode(DEF, tpx...)
        }
|
        DELETE
        {
            requireImmediateStatement(DELETE, &@1)

            errorLoc("Missing statement number(s)", &@1)
        }
|
        DELETE stmt_range_list
        {
            requireImmediateStatement(DELETE, &@1)

            $<snodeVal>$ = makeStmtNode(DELETE, $<tnodeVal>2)
        }
|
        DENORM
        {
            requireImmediateStatement(DENORM, &@1)

            $<snodeVal>$ = makeStmtNode(DENORM)
        }
|
        DIM dim_list
        {
            requireDeferredStatement(DIM, &@1)

            $<snodeVal>$ = makeStmtNode(DIM, $<tnodeVal>2)
        }
|
        EDIT
        {
            requireImmediateStatement(EDIT, &@1)

            $<snodeVal>$ = makeStmtNode(EDIT)
        }
|
        END
        {
            requireDeferredStatement(END, &@1)

            if g.endStmtNo == 0 {
               lastStmt := stmtAvlTreeLastInOrder()
               if lastStmt != nil && lastStmt.stmtNo > deferredStmtNo {
                  errorLoc("END statement must be last")
               }
            } else if g.endStmtNo != deferredStmtNo {
               errorLoc("Multiple END statements not allowed")
            }

            $<snodeVal>$ = makeStmtNode(END)
        }
|
        FIELD POUND rpn_expr COMMA field_list
        {
            requireDeferredStatement(FIELD, &@1)

            tp3 := $<tnodeVal>3

            requireNumericOperand(tp3, &@3)

            $<snodeVal>$ = makeStmtNode(FIELD, tp3, $<tnodeVal>5)
        }
|
        FOR simple_nvar EQ expr TO expr
        {
            tp2 := $<tnodeVal>2
            tp4 := $<tnodeVal>4
            tp6 := $<tnodeVal>6

            rpn2 := makeNrpnTokenNode(tp2)
            rpn4 := makeNrpnTokenNode(tp4)
            rpn6 := makeNrpnTokenNode(tp6)

            requireDeferredStatement(FOR, &@1)
            requireNumericOperand(rpn4, &@4)
            requireNumericOperand(rpn6, &@6)
            requireCompatibleNumericOperands(tp2, tp4, &@4, tp6, &@6)

            $<snodeVal>$ = makeStmtNode(FOR, rpn2, rpn4, rpn6)
        }
|
        FOR simple_nvar EQ expr TO expr STEP expr
        {
            tp2 := $<tnodeVal>2
            tp4 := $<tnodeVal>4
            tp6 := $<tnodeVal>6
            tp8 := $<tnodeVal>8

            rpn2 := makeNrpnTokenNode(tp2)
            rpn4 := makeNrpnTokenNode(tp4)
            rpn6 := makeNrpnTokenNode(tp6)
            rpn8 := makeNrpnTokenNode(tp8)

            requireDeferredStatement(FOR, &@1)
            requireNumericOperand(rpn4, &@4)
            requireNumericOperand(rpn6, &@6)
            requireNumericOperand(rpn8, &@8)

            requireCompatibleNumericOperands(tp2, tp4, &@4,tp6,
                                             &@6, tp8, &@8)

            $<snodeVal>$ = makeStmtNode(FOR, rpn2, rpn4, rpn6, rpn8)
        }
|
        FOR simple_nvar EQ expr while_until
        {
            tp2 := $<tnodeVal>2
            tp4 := $<tnodeVal>4
            tp5 := $<tnodeVal>5

            rpn2 := makeNrpnTokenNode(tp2)
            rpn4 := $<tnodeVal>4
            rpn5 := makeNrpnTokenNode(tp5)

            requireDeferredStatement(FOR, &@1)
            requireNumericOperand(rpn4, &@4)
            requireCompatibleNumericOperands(tp2, tp4, &@4)


            $<snodeVal>$ = makeStmtNode(FOR, rpn2, rpn4, rpn5)
        }
|
        FOR simple_nvar EQ expr STEP expr while_until
        {
            tp2 := $<tnodeVal>2
            tp4 := $<tnodeVal>4
            tp6 := $<tnodeVal>6
            tp7 := $<tnodeVal>7

            rpn2 := makeNrpnTokenNode(tp2)
            rpn4 := makeNrpnTokenNode(tp4)
            rpn6 := makeNrpnTokenNode(tp6)
            rpn7 := makeNrpnTokenNode(tp7)

            requireDeferredStatement(FOR, &@1)
            requireNumericOperand(rpn4, &@4)
            requireNumericOperand(rpn6, &@6)
            requireCompatibleNumericOperands(tp2, tp4, &@4, tp6, &@6)

            //
            // The following is NOT a typo.  To simplify the code
            // in executeFor, we ensure that the STEP expression,
            // if present, is always the last operand
            //

            $<snodeVal>$ = makeStmtNode(FOR, rpn2, rpn4, rpn7, rpn6)
        }
|
        FNEND
        {
            $<snodeVal>$ = makeStmtNode(FNEND)
        }
|
        GET POUND rpn_expr get_opts
        {
            $<snodeVal>$ = makeStmtNode(GET, $<tnodeVal>3, $<tnodeVal>4)
        }
|
        GOSUB stmt_no
        { 
            requireDeferredStatement(GOSUB, &@1)

            $<snodeVal>$ = makeStmtNode(GOSUB, $<tnodeVal>2)
        }
|
        GOTO stmt_no
        { 
            requireDeferredStatement(GOTO, &@1)

            $<snodeVal>$ = makeStmtNode(GOTO, $<tnodeVal>2)
        }
|
        HELP
        { 
            requireImmediateStatement(HELP, &@1)

            $<snodeVal>$ = makeStmtNode(HELP)
        }
|
        HELP help_targets
        { 
            requireImmediateStatement(HELP, &@1)

            $<snodeVal>$ = makeStmtNode(HELP, $<tnodeVal>2)
        }
|
        IF rpn_expr THEN if_target
        { 
            requireDeferredStatement(IF, &@1)

            $<snodeVal>$ = makeStmtNode(IF, $<tnodeVal>2, $<tnodeVal>4)
        }
|
        IF rpn_expr GOTO stmt_no
        { 
            requireDeferredStatement(IF, &@1)

            sp := makeStmtNode(GOTO, $<tnodeVal>4)
            tp := makeTokenNode(STMT, sp)
            $<snodeVal>$ = makeStmtNode(IF, $<tnodeVal>2, tp)
        }
|
        IF rpn_expr THEN if_target ELSE if_target
        { 
            requireDeferredStatement(IF, &@1)

            $<snodeVal>$ = makeStmtNode(IF, $<tnodeVal>2, $<tnodeVal>4,
                                        $<tnodeVal>6)
        }
|
        INPUT input_list
        {
            requireDeferredStatement(INPUT, &@1)

            $<snodeVal>$ = makeStmtNode(INPUT, nil, nil, $<tnodeVal>2)
        }
|
        inputc rpn_expr COMMA input_list
        {
            requireDeferredStatement(INPUT, &@1)

            tp2 := $<tnodeVal>2

            requireNumericOperand($<tnodeVal>2, &@2)

            $<snodeVal>$ = makeStmtNode(INPUT, nil, tp2, $<tnodeVal>4)
        }
|
        INPUT LINE simple_var
        {
            requireDeferredStatement(INPUT, &@1)

            tp3 := $<tnodeVal>3
            ilp := makeTokenNode(LINE)

            requireStringOperand(tp3, &@3)

            $<snodeVal>$ = makeStmtNode(INPUT, ilp, nil, tp3)
        }
|
        INPUT LINE POUND rpn_expr COMMA simple_var
        {
            requireDeferredStatement(INPUT, &@1)

            tp4 := $<tnodeVal>4
            ilp := makeTokenNode(LINE)
            tp6 := $<tnodeVal>6

            requireNumericOperand(tp4, &@4)
            requireStringOperand(tp6, &@6)

            $<snodeVal>$ = makeStmtNode(INPUT, ilp, tp4, tp6)
        }
|
        kill_stmt
        {
            $<snodeVal>$ = $<snodeVal>1
        }
|
        LSET set_vars_list EQ rpn_expr
        {
            requireDeferredStatement(LSET, &@1)

            tp4 := $<tnodeVal>4

            requireStringOperand(tp4, &@4)

            $<snodeVal>$ = makeStmtNode(LSET, $<tnodeVal>2, tp4)
        }
|
        LIST
        {
            requireImmediateStatement(LIST, &@1)

            $<snodeVal>$ = makeStmtNode(LIST)
        }
|
        LISTNH
        {
            requireImmediateStatement(LISTNH, &@1)

            $<snodeVal>$ = makeStmtNode(LISTNH)
        }
|
        LIST stmt_range_list
        {
            requireImmediateStatement(LIST, &@1)

            $<snodeVal>$ = makeStmtNode(LIST, $<tnodeVal>2)
        }
|
        LISTNH stmt_range_list
        {
            requireImmediateStatement(LISTNH, &@1)

            $<snodeVal>$ = makeStmtNode(LISTNH, $<tnodeVal>2)
        }
|
        MAT mat_ops
        {
            $<snodeVal>$ = makeStmtNode(MAT, $<tnodeVal>2)
        }
|
        NEW filename
        {
            requireImmediateStatement(NEW, &@1)

            $<snodeVal>$ = makeStmtNode(NEW, $<tnodeVal>2)
        }
|
        NEXT simple_nvar
        { 
            requireDeferredStatement(NEXT, &@1)

            rpn := makeNrpnTokenNode($<tnodeVal>2)
            $<snodeVal>$ = makeStmtNode(NEXT, rpn)
        }
|
        OLD filename
        {
            requireImmediateStatement(OLD, &@1)

            $<snodeVal>$ = makeStmtNode(OLD, $<tnodeVal>2)
        }
|
        ON rpn_expr GOSUB on_list
        {
            requireDeferredStatement(ON, &@1)

            stmtList := make([]*tokenNode, 1)
            stmtList[0] = $<tnodeVal>2
            stmtList = append(stmtList, createTokenNodeSlice($<tnodeVal>4)...)
            $<snodeVal>$ = makeStmtNode(ONGOSUB, stmtList...)
        }
|
        ON rpn_expr GOTO on_list
        {
            requireDeferredStatement(ON, &@1)

            stmtList := make([]*tokenNode, 1)
            stmtList[0] = $<tnodeVal>2
            stmtList = append(stmtList, createTokenNodeSlice($<tnodeVal>4)...)
            $<snodeVal>$ = makeStmtNode(ONGOTO, stmtList...)
        }
|
        ON ERROR GOTO onerror_stmt_no
        {
            requireDeferredStatement(ON, &@1)

            $<snodeVal>$ = makeStmtNode(ONERROR, $<tnodeVal>4)
        }
|
        ON ERROR GOTO
        {
            requireDeferredStatement(ON, &@1)

            $<snodeVal>$ = makeStmtNode(ONERROR)
        }
|
        open_stmt
        {
            $<snodeVal>$ = $<snodeVal>1
        }
|
        print_stmt
        {
            $<snodeVal>$ = $<snodeVal>1
        }
|
        PUT POUND rpn_expr put_opts
        {
            $<snodeVal>$ = makeStmtNode(PUT, $<tnodeVal>3, $<tnodeVal>4)
        }
|
        RANDOMIZE
        { 
            requireDeferredStatement(RANDOMIZE, &@1)

            $<snodeVal>$ = makeStmtNode(RANDOMIZE)
        }
|
        READ read_list
        {
            requireDeferredStatement(READ, &@1)

            $<snodeVal>$ = makeStmtNode(READ, $<tnodeVal>2)
        }
|
        REM
        { 
            requireDeferredStatement(REM, &@1)

            $<snodeVal>$ = makeStmtNode(REM)
        }
|
        RELOAD
        {
            requireImmediateStatement(RELOAD, &@1)

            $<snodeVal>$ = makeStmtNode(RELOAD)
        }
|
        RENUMBER
        {
            requireImmediateStatement(RENUMBER, &@1)

            errorLoc("Missing statement number", &@1)
        }
|
        RENUMBER stmt_no
        {
            requireImmediateStatement(RENUMBER, &@1)

            $<snodeVal>$ = makeStmtNode(RENUMBER, $<tnodeVal>2)
        }
|
        RESTORE
        {
            requireDeferredStatement(RESTORE, &@1)

            $<snodeVal>$ = makeStmtNode(RESTORE)
        }
|
        RESUME
        {
            requireDeferredStatement(RESTORE, &@1)

            $<snodeVal>$ = makeStmtNode(RESUME)
        }
|
        RESUME onerror_stmt_no
        {
            requireDeferredStatement(RESTORE, &@1)

            $<snodeVal>$ = makeStmtNode(RESUME, $<tnodeVal>2)
        }
|
        RETURN
        { 
            requireDeferredStatement(RETURN, &@1)

            $<snodeVal>$ = makeStmtNode(RETURN)
        }
|
        RSET set_vars_list EQ rpn_expr
        {
            requireDeferredStatement(RSET, &@1)

            tp4 := $<tnodeVal>4

            requireStringOperand(tp4, &@4)

            $<snodeVal>$ = makeStmtNode(RSET, $<tnodeVal>2, tp4)
        }
|
        RUN
        {
            requireImmediateStatement(RUN, &@1)

            $<snodeVal>$ = makeStmtNode(RUN)
        }
|
        RUNNH
        {
            requireImmediateStatement(RUNNH, &@1)

            $<snodeVal>$ = makeStmtNode(RUNNH)
        }
|
        SAVE filename
        {
            requireImmediateStatement(SAVE, &@1)

            $<snodeVal>$ = makeStmtNode(SAVE, $<tnodeVal>2)
        }
|
        SLEEP rpn_expr
        {
            requireDeferredStatement(SLEEP, &@1)

            $<snodeVal>$ = makeStmtNode(SLEEP, $<tnodeVal>2)
        }
|
        STATS
        {
            requireImmediateStatement(STATS, &@1)

            $<snodeVal>$ = makeStmtNode(STATS)
        }
|
        STOP
        {
            requireDeferredStatement(STOP, &@1)

            $<snodeVal>$ = makeStmtNode(STOP)
        }
|
        TRACE trace_switches
        {
            requireImmediateStatement(TRACE, &@1)

            $<snodeVal>$ = makeStmtNode(TRACE, $<tnodeVal>2)
        }
|
       WAIT rpn_expr
        {
            requireDeferredStatement(WAIT, &@1)

            $<snodeVal>$ = makeStmtNode(WAIT, $<tnodeVal>2)
        }
|
        assign_stmt
        { 
            $<snodeVal>$ = $<snodeVal>1
        }

mat_ops:
       simple_nvar EQ simple_nvar
       {
            $<tnodeVal>$ = makeTokenNode(EQ, $<tnodeVal>1, $<tnodeVal>3)
       }
|
       simple_nvar EQ mat_binops
       {
            $<tnodeVal>$ = makeTokenNode(EQ, $<tnodeVal>1, $<tnodeVal>3)
       }
|
       simple_nvar EQ mat_funcs
       {
            $<tnodeVal>$ = makeTokenNode(EQ, $<tnodeVal>1, $<tnodeVal>3)
       }
|
       PRINT simple_nvar opt_trailing_cs
       {
            $<tnodeVal>$ = makeTokenNode(PRINT, $<tnodeVal>2, $<tnodeVal>3)
       }
|
       INPUT simple_nvar_list
       {
            $<tnodeVal>$ = makeTokenNode(INPUT, $<tnodeVal>2)
       }
|
       READ simple_nvar_list
       {
            $<tnodeVal>$ = makeTokenNode(READ, $<tnodeVal>2)
       }

mat_binops:
       simple_nvar PLUS simple_nvar
       {
            $<tnodeVal>$ = makeTokenNode(PLUS, $<tnodeVal>1, $<tnodeVal>3)
       }
|
       simple_nvar MINUS simple_nvar
       {
            $<tnodeVal>$ = makeTokenNode(MINUS, $<tnodeVal>1, $<tnodeVal>3)
       }
|
       simple_nvar STAR simple_nvar
       {
            $<tnodeVal>$ = makeTokenNode(STAR, $<tnodeVal>1, $<tnodeVal>3)
       }
|
       LPAR rpn_expr RPAR STAR simple_nvar
       {
            $<tnodeVal>$ = makeTokenNode(STAR, $<tnodeVal>2, $<tnodeVal>5)
       }

mat_funcs:
       CON
       {
            $<tnodeVal>$ = makeTokenNode(CON)
       }
|
       IDN
       {
            $<tnodeVal>$ = makeTokenNode(IDN)
       }
|
       //       INV LPAR simple_var RPAR
       //       {
       //            $<tnodeVal>$ = makeTokenNode(INV, $<tnodeVal>3)
       //       }
       //|
       TRN LPAR simple_var RPAR
       {
            $<tnodeVal>$ = makeTokenNode(TRN, $<tnodeVal>3)
       }
|
       ZER
       {
            $<tnodeVal>$ = makeTokenNode(ZER)
       }

set_vars_list:
        string_var COMMA set_vars_list
        {
            tp1 := makeSrpnTokenNode($<tnodeVal>1)
            tp3 := $<tnodeVal>3

            tp1.next = tp3
            $<tnodeVal>$ = tp1
        }
|
        string_var
        {
            $<tnodeVal>$ = makeSrpnTokenNode($<tnodeVal>1)
        }

field_list:
        field_pair COMMA field_list
        {
            tp1 := $<tnodeVal>1
            tp3 := $<tnodeVal>3

            tp1.next = tp3
            $<tnodeVal>$ = tp1
        }
|
        field_pair
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

field_pair:
        rpn_expr AS string_var
        {
            tp1 := $<tnodeVal>1

            requireNumericOperand(tp1, &@1)

            tp3 := makeSrpnTokenNode($<tnodeVal>3)

            $<tnodeVal>$ = makeTokenNode(FIELDELEMENT, tp1, tp3)
        }

get_opts:
        COMMA RECORD rpn_expr
        {
            tp3 := $<tnodeVal>3

            requireNumericOperand(tp3, &@3)

            $<tnodeVal>$ = makeTokenNode(RECORD, tp3)
        }
|
        /* empty */
        {
            $<tnodeVal>$ = nil
        }

put_opts:
        COMMA RECORD rpn_expr count
        {
            tp3 := $<tnodeVal>3

            requireNumericOperand(tp3, &@3)

            $<tnodeVal>$ = makeTokenNode(RECORD, tp3)
        }
|
        /* empty */
        {
            $<tnodeVal>$ = nil
        }

//
// COUNT is parsed but ignored
//

count:
        COMMA COUNT
|
        /* empty */

close_stmt:
        CLOSE close_list
        {
            tp2 := $<tnodeVal>2

            requireDeferredStatement(CLOSE, &@1)

            $<snodeVal>$ = makeStmtNode(CLOSE, createTokenNodeSlice(tp2)...)
        }
                    
kill_stmt:
        KILL rpn_expr
        {
            tp2 := $<tnodeVal>2

            requireStringOperand(tp2, &@2)

            $<snodeVal>$ = makeStmtNode(KILL, tp2)
        }

open_stmt:
        OPEN rpn_expr open_mode_opt AS FILE rpn_expr open_opts
        {
            tp2 := $<tnodeVal>2
            tp3 := $<tnodeVal>3
            tp6 := $<tnodeVal>6

            requireDeferredStatement(OPEN, &@1)
            requireStringOperand(tp2, &@2)
            requireNumericOperand(tp6, &@6)

            $<snodeVal>$ = makeStmtNode(OPEN, tp2, tp3, tp6)
        }

open_mode_opt:
        FOR open_mode
        {
            $<tnodeVal>$ = $<tnodeVal>2
        }
|
        /* empty */
        {
            $<tnodeVal>$ = makeTokenNode(INTEGER, int16(IOREAD | IOWRITE))
        }

open_mode:
        INPUT
        { 
            $<tnodeVal>$ = makeTokenNode(INTEGER, int16(IOREAD))
        }
|
        OUTPUT
        { 
            $<tnodeVal>$ = makeTokenNode(INTEGER, int16(IOWRITE))
        }

//
// CLUSTERSIZE, RECORDSIZE and MODE must be parsed but are ignored!
//

open_opts:
        COMMA CLUSTERSIZE INTEGER
|
        COMMA RECORDSIZE INTEGER
|
        COMMA CLUSTERSIZE INTEGER COMMA RECORDSIZE INTEGER
|
        COMMA RECORDSIZE INTEGER COMMA CLUSTERSIZE INTEGER 
|
        COMMA MODE INTEGER
|
        /* empty */

help_targets:
        BYE
        {
            $<tnodeVal>$ = makeTokenNode(BYE)
        }
|
        CONFIG
        {
            $<tnodeVal>$ = makeTokenNode(CONFIG)
        }
|
        CONT
        {
            $<tnodeVal>$ = makeTokenNode(CONT)
        }
|
        DELETE
        {
            $<tnodeVal>$ = makeTokenNode(DELETE)
        }
|
        DENORM
        {
            $<tnodeVal>$ = makeTokenNode(DENORM)
        }
|
        EDIT
        {
            $<tnodeVal>$ = makeTokenNode(EDIT)
        }
|
        KILL
        {
            $<tnodeVal>$ = makeTokenNode(KILL)
        }
|
        LIST
        {
            $<tnodeVal>$ = makeTokenNode(LIST)
        }
|
        LISTNH
        {
            $<tnodeVal>$ = makeTokenNode(LISTNH)
        }
|
        NEW
        {
            $<tnodeVal>$ = makeTokenNode(NEW)
        }
|
        OLD
        {
            $<tnodeVal>$ = makeTokenNode(OLD)
        }
|
        RELOAD
        {
            $<tnodeVal>$ = makeTokenNode(RELOAD)
        }
|
        RUN
        {
            $<tnodeVal>$ = makeTokenNode(RUN)
        }
|
        RUNNH
        {
            $<tnodeVal>$ = makeTokenNode(RUNNH)
        }
|
        SAVE
        {
            $<tnodeVal>$ = makeTokenNode(SAVE)
        }
|
        STATS
        {
            $<tnodeVal>$ = makeTokenNode(STATS)
        }
|
        TRACE
        {
            $<tnodeVal>$ = makeTokenNode(TRACE)
        }

trace_switches:
        trace_switch trace_switches
        {
            tp1 := $<tnodeVal>1

            tp1.next = $<tnodeVal>2

            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        trace_switch
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

trace_switch:
        DUMP
        {
            $<tnodeVal>$ = makeTokenNode(DUMP)
        }
|
        EXEC
        {
            $<tnodeVal>$ = makeTokenNode(EXEC)
        }
|
        VARS
        {
            $<tnodeVal>$ = makeTokenNode(VARS)
        }
|
        simple_var
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

//
// We need help from the lexer to deal with user defined function names,
// as otherwise, it's impossible for the parser to tell if 'fnfoo(1,2)'
// is a call to a user defined function with arguments 1 and 2, or an
// array reference to floating array 'fnfoo' with 2 subscripts.  The lexer
// has to see the 'fn' as the first two letters of a variable name, and
// change [FIS]VAR token to FN[FIS]VAR token.  This is ugly, but we would
// have needed to do something anyway to make the runtime code understand
// what is going on
//

//
// I really want to have simple_var below diagnosing exactly what is
// wrong, but that causes a bazillion reduce/reduce conflicts in the
// 'expr' non-terminal
//

fn_var:
        FNFVAR
        {
            $<tnodeVal>$ = makeTokenNode(FNFVAR, $<stringVal>1)
        }
|
        FNIVAR
        {
            $<tnodeVal>$ = makeTokenNode(FNIVAR, $<stringVal>1)
        }
|
        FNSVAR
        {
            $<tnodeVal>$ = makeTokenNode(FNSVAR, $<stringVal>1)
        }
|
        BADFUNCNAME
        {
            errorLoc("Invalid function name", &@1)
        }

fn_arg_list:
        /* empty */
        {
            $<tnodeVal>$ = nil
        }
|
        LPAR RPAR
        {
            $<tnodeVal>$ = nil
        }
|
        LPAR fn_arg_list_inner RPAR
        {
            $<tnodeVal>$ = $<tnodeVal>2
        }

fn_arg_list_inner:
        expr
        {
            tp1 := $<tnodeVal>1
            $<tnodeVal>$ = tp1
        }
|
        expr COMMA fn_arg_list_inner
        {
            tp1 := $<tnodeVal>1

            tp1.next = $<tnodeVal>3
            $<tnodeVal>$ = tp1
        }

fn_param_list:
        /* empty */
        {
            $<tnodeVal>$ = nil
        }
|
        LPAR RPAR
        {
            $<tnodeVal>$ = nil
        }
|
        LPAR fn_param_list_inner RPAR
        {
            $<tnodeVal>$ = $<tnodeVal>2
        }

fn_param_list_inner:
        fn_param
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        fn_param COMMA fn_param_list_inner
        {
            tp1 := $<tnodeVal>1

            tp1.next = $<tnodeVal>3
            $<tnodeVal>$ = tp1
        }

fn_param:
        simple_var
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        fn_var
        {
            errorLoc("Invalid function parameter", &@1)
        }

print_stmt:
        PRINT
        {
            $<snodeVal>$ = makeStmtNode(PRINT, nil, nil, nil)
        }
|
        PRINT print_list opt_trailing_cs
        {
            t2 := $<tnodeVal>2

            for t := t2 ; t != nil ; t = t.next {
                if t.next == nil {
                   t.next = $<tnodeVal>3
                   break
                }
            }

            $<snodeVal>$ = makeStmtNode(PRINT, nil, nil, t2)
        }
|
        PRINT USING rpn_expr COMMA print_list
        {
            t3 := $<tnodeVal>3
             
            requireStringOperand(t3, &@3)

            $<snodeVal>$ = makeStmtNode(PRINT, nil, t3, $<tnodeVal>5)
        }
|
        // ignore any trailing COMMA or SEMI
        printc rpn_expr COMMA print_list opt_trailing_cs
        {
            //
            // Formatting and zones are not relevant when doing
            // PRINT to a file, but the BNF requires us to accept
            // COMMA, etc.  After parsing the entire command, we
            // change anything other than NRPN or SRPN to SEMI,
            // which is ignored by basicPrint.  Since we are writing
            // to a file, ignoring any trailing COMMA or SEMI
            //

            t2 := $<tnodeVal>2
            t4 := $<tnodeVal>4

            for t := t4 ; t != nil ; t = t.next {
                if t.token != NRPN && t.token != SRPN {
                   t.token = SEMI
                }
            }

            requireNumericOperand(t2, &@2)

            $<snodeVal>$ = makeStmtNode(PRINT, t2, nil, t4)
        }
|
        printc rpn_expr USING rpn_expr COMMA print_list opt_trailing_cs
        {
            //
            // Formatting and zones are not relevant when doing
            // PRINT to a file, but the BNF requires us to accept
            // COMMA, etc.  After parsing the entire command, we
            // change anything other than NRPN or SRPN to SEMI,
            // to a file, ignoring any trailing COMMA or SEMI
            // which is ignored by basicPrint
            //

            t2 := $<tnodeVal>2
            t4 := $<tnodeVal>4
            t6 := $<tnodeVal>6

            for t := t6 ; t != nil ; t = t.next {
                if t.token != NRPN && t.token != SRPN {
                   t.token = SEMI
                }
            }

            requireNumericOperand(t2, &@2)
            requireStringOperand(t4, &@4)

            $<snodeVal>$ = makeStmtNode(PRINT, t2, t4, t6)
        }

//
// 3 clients of the filename non-terminal
//
// 1. OLD  - there must be a filename
// 2. NEW  - there can be a filename
// 3. SAVE - there can be a filename
//
// Unfortunately for #2 and #3, the parser is not able to make
// this call on its own, so we just hand back a nil token node
// pointer, and let the execute code figure it out
//

filename:
        FILENAME
        {
            $<tnodeVal>$ = makeTokenNode(FILENAME, $<stringVal>1)
        }
|
        BADFILENAME
        {
            errorLoc("Invalid filename!")
        }
|
        {
            $<tnodeVal>$ = nil
        }

close_list:
        filenum COMMA close_list
        {
            tp1 := $<tnodeVal>1
            tp1.next = $<tnodeVal>3
            $<tnodeVal>$ = tp1
        }
|
        filenum
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

filenum:
       rpn_expr
       {
            tp1 := $<tnodeVal>1

            requireNumericOperand(tp1, &@1)

            $<tnodeVal>$ = tp1
       }

on_list:
        stmt_no COMMA on_list
        {
            tp1 := $<tnodeVal>1
            tp1.next = $<tnodeVal>3
            $<tnodeVal>$ = tp1
        }
|
        stmt_no
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

while_until:
        WHILE expr
        {
            $<tnodeVal>$ = makeTokenNode(WHILE, $<tnodeVal>2)
        }
|
        UNTIL expr
        {
            $<tnodeVal>$ = makeTokenNode(UNTIL, $<tnodeVal>2)
        }

        //
        // The great majority of the time, a statement node has a
        // statement number, and is registered in the program table.
        // There are a few exceptions: the 'then' and 'else' clauses of
        // the 'if' statement can take not only a simple statement
        // number, but a limited set of explicit statements.
        // Those statements do not have a statement number, and need
        // to be hung off the 'then' or 'else' fields in the stmt node,
        // but the operands list in the stmt node refer to token nodes,
        // nothing else.  So, we have a pseudo token type, STMT, whose
        // only purpose is to hold a pointer to a stmtNode in its
        // token_data field
        //

if_target:
        close_stmt
        {
            $<tnodeVal>$ = makeTokenNode(STMT, $<snodeVal>1)
        }
|
        GOSUB stmt_no
        {
            sp := makeStmtNode(GOSUB, $<tnodeVal>2)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }
|
        GOTO stmt_no
        {
            sp := makeStmtNode(GOTO, $<tnodeVal>2)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }
|
        kill_stmt
        {
            $<tnodeVal>$ = makeTokenNode(STMT, $<snodeVal>1)
        }
|
        open_stmt
        {
            $<tnodeVal>$ = makeTokenNode(STMT, $<snodeVal>1)
        }
|
        print_stmt
        {
            $<tnodeVal>$ = makeTokenNode(STMT, $<snodeVal>1)
        }
|
        RANDOMIZE
        {
            sp := makeStmtNode(RANDOMIZE)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }
|
        RESTORE
        {
            sp := makeStmtNode(RESTORE)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }
|
        RESUME
        {
            sp := makeStmtNode(RESUME)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }
|
        RESUME stmt_no
        {
            sp := makeStmtNode(RESUME, $<tnodeVal>2)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }
|
        RETURN
        {
            sp := makeStmtNode(RANDOMIZE)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }
|
        STOP
        {
            sp := makeStmtNode(STOP)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }
|
assign_stmt
        {
            $<tnodeVal>$ = makeTokenNode(STMT, $<snodeVal>1)
        }
|
        stmt_no
        {
            sp := makeStmtNode(GOTO, $<tnodeVal>1)
            $<tnodeVal>$ = makeTokenNode(STMT, sp)
        }

assign_stmt:
        LET nvar EQ rpn_expr
        {
            requireNumericOperand($<tnodeVal>4, &@4)

            lhs := makeNrpnTokenNode($<tnodeVal>2)

            $<snodeVal>$ = makeStmtNode(LET, lhs, $<tnodeVal>4)
        }
|
        nvar EQ rpn_expr
        {
            requireNumericOperand($<tnodeVal>3, &@3)

            lhs := makeNrpnTokenNode($<tnodeVal>1)

            $<snodeVal>$ = makeStmtNode(LET, lhs, $<tnodeVal>3)
        }
|
        LET string_var EQ rpn_expr
        {
            requireStringOperand($<tnodeVal>4, &@4)

            lhs := makeSrpnTokenNode($<tnodeVal>2)

            $<snodeVal>$ = makeStmtNode(LET, lhs, $<tnodeVal>4)
        }
|
        string_var EQ rpn_expr
        {
            requireStringOperand($<tnodeVal>3, &@3)

            lhs := makeSrpnTokenNode($<tnodeVal>1)

            $<snodeVal>$ = makeStmtNode(LET, lhs, $<tnodeVal>3)
        }
|
        LET fn_var EQ rpn_expr
        {
            if isNumeric($<tnodeVal>2) {
               requireNumericOperand($<tnodeVal>4, &@4)
            } else {
               requireStringOperand($<tnodeVal>4, &@4)
            }

            lhs := makeNrpnTokenNode($<tnodeVal>2)

            $<snodeVal>$ = makeStmtNode(LET, lhs, $<tnodeVal>4)
        }
|
        fn_var EQ rpn_expr
        {
            if isNumeric($<tnodeVal>1) {
               requireNumericOperand($<tnodeVal>3, &@3)
            } else {
               requireStringOperand($<tnodeVal>3, &@3)
            }

            lhs := makeNrpnTokenNode($<tnodeVal>1)

            $<snodeVal>$ = makeStmtNode(LET, lhs, $<tnodeVal>3)
        }

stmt_range_list:
        stmt_range COMMA stmt_range_list
        {
            $<tnodeVal>1.next = $<tnodeVal>3
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        stmt_range
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

stmt_range:
        stmt_no MINUS stmt_no
        {
            firstStmt := $<tnodeVal>1.tokenData.(int16)
            lastStmt := $<tnodeVal>3.tokenData.(int16)

            if firstStmt > lastStmt {
                errorLoc("Invalid statement number range", &@1)
            }

            $<tnodeVal>$ = makeTokenNode(INTPAIR,  $<tnodeVal>1,
                                          $<tnodeVal>3)
        }
|
        stmt_no
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

dim_list:
        dim_var COMMA dim_list
        {
            tp1 := $<tnodeVal>1
            tp2 := $<tnodeVal>3
            tp1.next = tp2

            $<tnodeVal>$ = tp1
        }
|
        dim_var
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

dim_var:
        simple_nvar LPAR array_bounds RPAR
        {
            tp1 := $<tnodeVal>1
            tp1.operands = append(tp1.operands, $<tnodeVal>3)

            $<tnodeVal>$ = tp1
        }
|
        simple_nvar LPAR array_bounds COMMA array_bounds RPAR
        {
            tp1 := $<tnodeVal>1
            tp1.operands = append(tp1.operands, $<tnodeVal>3)
            tp1.operands = append(tp1.operands, $<tnodeVal>5)

            $<tnodeVal>$ = tp1
        }
|
        svar LPAR array_bounds RPAR
        {
            tp1 := $<tnodeVal>1
            tp1.operands = append(tp1.operands, $<tnodeVal>3)

            $<tnodeVal>$ = tp1
        }
|
        svar LPAR array_bounds COMMA array_bounds RPAR
        {
            tp1 := $<tnodeVal>1
            tp1.operands = append(tp1.operands, $<tnodeVal>3)
            tp1.operands = append(tp1.operands, $<tnodeVal>5)

            $<tnodeVal>$ = tp1
        }

//
// Another nuance with input vs print.  For the latter, comma and
// semicolon are relevant, since they determine print formatting.
// For input, however, they are purely syntactic sugar, so we don't
// bother creating token nodes for them, as we'd just be deleting
// them in the parent rule, or ignoring them at runtime.
//
// Also, we need to disallow string prompt if an I/O channel is used
//

input_list:
        input_item
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        input_item input_sep input_list
        {
            tp1 := $<tnodeVal>1

            tp1.next = $<tnodeVal>3
            $<tnodeVal>$ = tp1
        }

input_item:
        any_var
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
                           
|
        string input_sep any_var
        {
            tp1 := $<tnodeVal>1
            tp3 := $<tnodeVal>3

            $<tnodeVal>$ = makeTokenNode(INPUTPAIR, tp1, tp3)
        }

read_list:
        any_var COMMA read_list
        {
            tp1 := $<tnodeVal>1
            tp1.next = $<tnodeVal>3

            $<tnodeVal>$ = tp1
        }
|
        any_var
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

data_list:
        data_item COMMA data_list
        {
            tp1 := $<tnodeVal>1
            tp1.next = $<tnodeVal>3

            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        data_item
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

data_item:
        float
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        integer
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        einteger
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        string
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

any_var:
        nvar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        svar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

inputc:
        INPUT POUND

input_sep:
        COMMA
|
        SEMI

printc:
        PRINT POUND

print_list:
        print_item print_sep print_list
        {
            tp1 := $<tnodeVal>1
            tp2 := $<tnodeVal>2
            tp3 := $<tnodeVal>3

            tp1.next = tp2
            tp2.next = tp3
            $<tnodeVal>$ = tp1
        }
|
        print_item
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
                                                                
opt_trailing_cs:
        TRAILING_COMMA
        {
            $<tnodeVal>$ = makeTokenNode(TRAILING_COMMA)
        }
|
        TRAILING_SEMI
        {
            $<tnodeVal>$ = makeTokenNode(TRAILING_SEMI)
        }
|
        // empty
        {
            $<tnodeVal>$ = nil
        }
        
print_item:
        rpn_expr
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

print_sep:
        DCOMMA
        {
            $<tnodeVal>$ = makeTokenNode(DCOMMA)
        }
|
        COMMA
        {
            $<tnodeVal>$ = makeTokenNode(COMMA)
        }
|
        SEMI
        {
            $<tnodeVal>$ = makeTokenNode(SEMI)
        }

string:
        STRING
        {
            $<tnodeVal>$ = makeTokenNode(STRING, $<stringVal>1)
        }
|
        USTRING
        {
            errorLoc("Unterminated string", &@1)
        }

fvar_ref:
        fvar array_sub
        {
            $<tnodeVal>$ = makeTokenNode(SUBSCR, $<tnodeVal>1, $<tnodeVal>2)
        }

fvar:
        FVAR
        {
            $<tnodeVal>$ = makeTokenNode(FVAR, $<stringVal>1)
        }

ivar_ref:
        ivar array_sub
        {
            $<tnodeVal>$ = makeTokenNode(SUBSCR, $<tnodeVal>1, $<tnodeVal>2)
        }

ivar:
        IVAR
        {
            $<tnodeVal>$ = makeTokenNode(IVAR, $<stringVal>1)
        }

svar_ref:
        svar array_sub
        {
            $<tnodeVal>$ = makeTokenNode(SUBSCR, $<tnodeVal>1, $<tnodeVal>2)
        }

svar:
        SVAR
        {
            $<tnodeVal>$ = makeTokenNode(SVAR, $<stringVal>1)
        }

//
// Even though BASIC-PLUS provides a shortword integer data type, BASIC in
// general has only ever provided a floating point data type.  Statement
// numbers are integers that must be greater than 0.  If the lexer returned
// an actual shortword, it would be impossible to reliably detect out of
// range inputs.  We have the lexer return integers as int64 which allows
// the parser to sanity check the input
//

array_bounds:
        INTEGER
        {
            i64 := $<int64Val>1

            checkInt16(ESUBSCRIPTERROR, i64, 1, &@1)

            $<tnodeVal>$ = makeTokenNode(INTEGER, int16(i64))
        }

onerror_stmt_no:
        INTEGER
        {
            i64 := $<int64Val>1

            checkInt16(EILLEGALLINENUMBER, i64, 0, &@1)

            tp := makeTokenNode(INTEGER, int16(i64))
            tp.tlocs = uint16(@1.pos.column)-1
            tp.tloce = uint16(@1.end.column)
            $<tnodeVal>$ = tp
        }

stmt_no:
        INTEGER
        {
            i64 := $<int64Val>1

            checkInt16(EILLEGALLINENUMBER, i64, 1, &@1)

            tp := makeTokenNode(INTEGER, int16(i64))
            tp.tlocs = uint16(@1.pos.column)-1
            tp.tloce = uint16(@1.end.column)
            $<tnodeVal>$ = tp
        }

einteger:
        EINTEGER
        {
            //
            // Tricky: we are parsing an explicit integer, so we need
            // to take account of the asymmetry in signed integers
            //

            i64 := $<int64Val>1

            if parsingUneg {
               i64 = -i64
            }

            checkInt16(EINTEGERERROR, i64, math.MinInt16, &@1)

            $<tnodeVal>$ = makeTokenNode(INTEGER, int16(i64))
        }

integer:
        INTEGER
        {
            $<tnodeVal>$ = makeTokenNode(FLOAT, float64($<int64Val>1))
        }

float:
        FLOAT
        {
            $<tnodeVal>$ = makeTokenNode(FLOAT, $<float64Val>1)
        }

        //
        // Intermediate non-terminal to allow us to convert a token
        // tree into a tokenList.  Because the operands of a stmtNode
        // are *tokenNode, we have fake tokens NRPN and SRPN whose
        // tokenData field contains the rpnList
        //

rpn_expr:
        expr
        {
            $<tnodeVal>$ = createRpnExpr($<tnodeVal>1)
        }

        //
        // NB: we kinda cheat here and let an 'expr' be numeric or
        // string, relying on the requireXXX routines to diagnose
        // mixing string and numeric.  We do this because it makes
        // the grammar cleaner, as well as allowing more useful
        // messages than 'Syntax error' :)
        //

expr:
        integer
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        einteger
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        float
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        fn_var fn_arg_list
        {
            tp1 := $<tnodeVal>1
            tp2 := createTokenNodeSlice($<tnodeVal>2)
            tpx := make([]any, 0)

            if len(tp2) > maxDefArgs {
               errorLoc("Too many function arguments", &@2)
            }

            //
            // To make life easier on the RPN processor, we push the
            // function token last, so it can tell how many values to
            // copy off the stack (it needs to match number and type of
            // arguments with formal parameters).  We also need to have
            // the number of arguments on the stack next to the function
            // token
            //

            for ix := 0 ; ix < len(tp2) ; ix++ {
                tpx = append(tpx, tp2[ix])
            }

            tpx = append(tpx, makeTokenNode(INTEGER, int16(len(tp2))))
            tpx = append(tpx, tp1)

            if isNumeric(tp1) {
                $<tnodeVal>$ = makeTokenNode(NCALL, tpx...)
            } else {
                $<tnodeVal>$ = makeTokenNode(SCALL, tpx...)
            }
        }
|
        nvar
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        expr PLUS expr
        {
            token := requireCompatibleOperands(PLUS, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)

            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr MINUS expr
        {
            requireNumericOperand($<tnodeVal>1, &@1)
            requireNumericOperand($<tnodeVal>3, &@3)

            $<tnodeVal>$ = makeTokenNode(MINUS, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr STAR expr
        {
            requireNumericOperand($<tnodeVal>1, &@1)
            requireNumericOperand($<tnodeVal>3, &@3)

            $<tnodeVal>$ = makeTokenNode(STAR, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr SLASH expr
        {
            requireNumericOperand($<tnodeVal>1, &@1)
            requireNumericOperand($<tnodeVal>3, &@3)

            $<tnodeVal>$ = makeTokenNode(SLASH, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr POW expr
        {
            requireNumericOperand($<tnodeVal>1, &@1)
            requireNumericOperand($<tnodeVal>3, &@3)

            $<tnodeVal>$ = makeTokenNode(POW, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        MINUS { parsingUneg = true } expr %prec UNEG
        {
            requireNumericOperand($<tnodeVal>3, &@2)

            $<tnodeVal>$ = makeTokenNode(UNEG, $<tnodeVal>3)

            parsingUneg = false
        }
|
        PLUS expr %prec UPLUS
        {
            requireNumericOperand($<tnodeVal>2, &@2)

            $<tnodeVal>$ = $<tnodeVal>2
        }
|
        numeric_par_expr
        {

            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        basic_bif
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        boolean_ops
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        logical_ops
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }
|
        string_val
        {
            $<tnodeVal>$ = $<tnodeVal>1
        }

basic_bif:
        ABS numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(ABS, $<tnodeVal>2)
        }
|
        ASCII string_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(ASCII, $<tnodeVal>2)
        }
|
        ATN numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(ATN, $<tnodeVal>2)
        }
|
        CHRS numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(CHRS, $<tnodeVal>2)
        }
|
        COS numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(COS, $<tnodeVal>2)
        }
|
        CVTFS numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(CVTFS, $<tnodeVal>2)
        }
|
        CVTIS numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(CVTIS, $<tnodeVal>2)
        }
|
        CVTSF string_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(CVTSF, $<tnodeVal>2)
        }
|
        CVTSI string_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(CVTSI, $<tnodeVal>2)
        }
|
        DATES numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(DATES, $<tnodeVal>2)
        }
|
        //       DET
        //       {
        //            $<tnodeVal>$ = makeTokenNode(DET)
        //       }
        //|
        ERL
        {
            $<tnodeVal>$ = makeTokenNode(ERL)
        }
|
        ERR
        {
            $<tnodeVal>$ = makeTokenNode(ERR)
        }
|
        EXP numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(EXP, $<tnodeVal>2)
        }
|
        FIX numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(FIX, $<tnodeVal>2)
        }
|
        INSTR LPAR expr COMMA expr COMMA expr RPAR
        {
            arg1 := $<tnodeVal>3
            arg2 := $<tnodeVal>5
            arg3 := $<tnodeVal>7

            requireNumericOperand(arg1, &@3)
            requireStringOperand(arg2, &@5)
            requireStringOperand(arg3, &@7)

            $<tnodeVal>$ = makeTokenNode(INSTR, arg1, arg2, arg3)
        }
|
        INT numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(INT, $<tnodeVal>2)
        }
|
        LEFT LPAR expr COMMA expr RPAR
        {
            arg1 := $<tnodeVal>3
            arg2 := $<tnodeVal>5

            requireStringOperand(arg1, &@3)
            requireNumericOperand(arg2, &@5)

            $<tnodeVal>$ = makeTokenNode(LEFT, arg1, arg2)
        }
|
        LEN string_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(LEN, $<tnodeVal>2)
        }
|
        LOG numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(LOG, $<tnodeVal>2)
        }
|
        LOG10 numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(LOG10, $<tnodeVal>2)
        }
|
        MID LPAR expr COMMA expr COMMA expr RPAR
        {
            arg1 := $<tnodeVal>3
            arg2 := $<tnodeVal>5
            arg3 := $<tnodeVal>7

            requireStringOperand(arg1, &@3)
            requireNumericOperand(arg2, &@5)
            requireNumericOperand(arg3, &@7)

            $<tnodeVal>$ = makeTokenNode(MID, arg1, arg2, arg3)
        }
|
        NUMS numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(NUMS, $<tnodeVal>2)
        }
|
        PI
        {
            $<tnodeVal>$ = makeTokenNode(PI)
        }
|
        POS numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(POS, $<tnodeVal>2)
        }
|
        RIGHT LPAR expr COMMA expr RPAR
        {
            arg1 := $<tnodeVal>3
            arg2 := $<tnodeVal>5

            requireStringOperand(arg1, &@3)
            requireNumericOperand(arg2, &@5)

            $<tnodeVal>$ = makeTokenNode(RIGHT, arg1, arg2)
        }
|
        RND
        {
            $<tnodeVal>$ = makeTokenNode(RND)
        }
|
        RND numeric_par_expr
        {
            // ignore the argument!
            $<tnodeVal>$ = makeTokenNode(RND)
        }
|
        SGN numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(SGN, $<tnodeVal>2)
        }
|
        SHA256 string_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(SHA256, $<tnodeVal>2)
        }
|
        SHA512 string_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(SHA512, $<tnodeVal>2)
        }
|
        SIN numeric_par_expr
        { 
            $<tnodeVal>$ = makeTokenNode(SIN, $<tnodeVal>2)
        }
|
        SPACES numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(SPACES, $<tnodeVal>2)
        }
|
        SQR numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(SQR, $<tnodeVal>2)
        }
|
        SWAPI numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(SWAPI, $<tnodeVal>2)
        }
|
        TAB numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(TAB, $<tnodeVal>2)
        }
|
        TAN numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(TAN, $<tnodeVal>2)
        }
|
        TIME numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(TIME, $<tnodeVal>2)
        }
|
        TIMES numeric_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(TIMES, $<tnodeVal>2)
        }
|
        VAL string_par_expr
        {
            $<tnodeVal>$ = makeTokenNode(VAL, $<tnodeVal>2)
        }

logical_ops:
        expr APPROX expr
        {
            token := requireCompatibleOperands(APPROX, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr EQ expr
        {
            token := requireCompatibleOperands(EQ, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr GE expr
        {
            token := requireCompatibleOperands(GE, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr GT expr
        {
            token := requireCompatibleOperands(GT, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr LE expr
        {
            token := requireCompatibleOperands(LE, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr LT expr
        {
            token := requireCompatibleOperands(LT, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr NE expr
        {
            token := requireCompatibleOperands(NE, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        NOT expr
        {
            requireIntegerOperand($<tnodeVal>2, &@2)
            $<tnodeVal>$ = makeTokenNode(NOT, $<tnodeVal>2)
        }

boolean_ops:
        expr AND expr
        {
            requireIntegerOperand($<tnodeVal>1, &@1)
            requireIntegerOperand($<tnodeVal>3, &@3)
            token := requireCompatibleOperands(AND, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr IMP expr
        {
            requireIntegerOperand($<tnodeVal>1, &@1)
            requireIntegerOperand($<tnodeVal>3, &@3)
            token := requireCompatibleOperands(IMP, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr EQV expr
        {
            requireIntegerOperand($<tnodeVal>1, &@1)
            requireIntegerOperand($<tnodeVal>3, &@3)
            token := requireCompatibleOperands(EQV, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr OR expr
        {
            requireIntegerOperand($<tnodeVal>1, &@1)
            requireIntegerOperand($<tnodeVal>3, &@3)
            token := requireCompatibleOperands(OR, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }
|
        expr XOR expr
        {
            requireIntegerOperand($<tnodeVal>1, &@1)
            requireIntegerOperand($<tnodeVal>3, &@3)
            token := requireCompatibleOperands(XOR, $<tnodeVal>1,
                                               $<tnodeVal>3, &@1, &@3)
            $<tnodeVal>$ = makeTokenNode(token, $<tnodeVal>1, $<tnodeVal>3)
        }

numeric_expr:
        expr
        {
            requireNumericOperand($<tnodeVal>1, &@1)
            $<tnodeVal>$ = $<tnodeVal>1
        }

numeric_par_expr:
        LPAR numeric_expr RPAR
        {
            $<tnodeVal>$ = $<tnodeVal>2
        }

string_par_expr:
        LPAR expr RPAR
        {
            requireStringOperand($<tnodeVal>2, &@2)
            $<tnodeVal>$ = $<tnodeVal>2
        }

array_sub:
        LPAR expr RPAR
        {
            requireNumericOperand($<tnodeVal>2, &@2)

            $<tnodeVal>$ = $<tnodeVal>2
        }
|
        LPAR expr COMMA expr RPAR
        {
            requireNumericOperand($<tnodeVal>2, &@2)
            requireNumericOperand($<tnodeVal>4, &@4)

            $<tnodeVal>$ = makeTokenNode(INTPAIR, $<tnodeVal>2, $<tnodeVal>4)
        }

%%

