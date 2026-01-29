package main

import (
	"bufio"
	"errors"
	"github.com/danswartzendruber/avl"
	"github.com/danswartzendruber/liner"
	"math"
	"os"
	"time"
)

//
// Constants
//

const myMaxFNum = 9007199254740992.0

const badDateMsg = "Invalid input to DATE$"

const VERSION = "1.1.2"

const basFileSuffix = ".bas"

const forStackMax = 10
const gosubStackMax = 10
const fnRecursionMax = 1000

const maxFilenums = 12

const maxLineLen = math.MaxUint8
const maxStringLen = math.MaxInt16

const maxVariableLen = 29

const minWindowRows = 70

const maxArrayMemory = (1024 * 1024 * 1000)

const floatingPointMode = "IEEE-754 64-bit Floating Point"

const maxImplicitSubscript = 10

const maxDefArgs = 5

const myPrompt = "% "

const zoneWidth = 14

const blockSize = 512

// FIX THESE AT SOME POINT
const yyFirsttok = ABS
const yyLasttok = ZER

const colorRedSeq = "\033[31m"
const colorResetSeq = "\033[0m"
const colorInverseVideoSeq = "\033[7m"
const clearScreenSeq = "\033[2J"

const executePrompt = "? "

const boolInt16False int16 = 0
const boolInt16True int16 = -1

const maxForInteger = 32766
const minForInteger = -32766

const minExpArg = -745
const maxExpArg = 709

const ctrlZ = rune(26)

const (
	LOOKUPMATRIXANY = iota
	LOOKUPMATRIX2D
	LOOKUPMATRIXSQUARE
)

//
// I/O mode definitions
//

const (
	IOREAD = 1 << iota
	IOWRITE
)

//
// File types
//

const (
	emptyFile = iota
	printFile
	recordFile
)

//
// Type definitions
//

type bifHack struct {
	token    int
	realName string
}

type symtabNode struct {
	name  string
	vType int
	flde  *fieldElement
	dims  []int16
	value symValue
}

type symValue struct {
	f [][]float64
	i [][]int16
	s [][]string
}

type renumberNode struct {
	stmt      *stmtNode
	tnodeList []*tokenNode
}

type prtuLexer struct {
	buf    string
	tokens []prtuToken
	idx    int
}

type prtuToken any

type prtuChar struct {
	ch string
}

type prtuString struct {
	len int
}

type prtuNumeric struct {
	left          int
	right         int
	dollar        bool
	fillchar      bool
	trailingMinus bool
	doComma       bool
	exponential   bool
}

type Lval struct {
	token int       // YACC token
	lval  yySymType // YACC token value and location
}

type Lexer struct {
	tokens []Lval
	line   string
}

type fnfvarToken string

type fnivarToken string

type fnsvarToken string

type fvarToken string

type ivarToken string

type svarToken string

type tokenList []any

type rpnStack struct {
	entries []any
}

type procState struct {
	stmt  *stmtNode
	expr  tokenList
	stack rpnStack
}

type faultInfo struct {
	state *procState
	err   int16
}

type tokenNode struct {
	token     int
	tlocs     uint16
	tloce     uint16
	tokenData any
	operands  []*tokenNode
	next      *tokenNode
}

type stmtNode struct {
	avl            avl.AvlNode
	token          int
	tokenLoc       yySymLoc
	line           string
	next           *stmtNode
	head           *stmtNode
	operands       []*tokenNode
	stmtNoTokenLoc yySymLoc
	stmtNo         int16
}

type crawloutException struct {
	continuable bool
}

type runtimeErrorInfo struct {
	msg string
	fip *faultInfo
}

type basicErrorInfo struct {
	msg  string
	file string
	line int
}

//
// A standard BASIC-PLUS file (e.g. written to by 'PRINT #xxx'
// will have standard Linux file permissions, whereas a record
// file (written to by 'PUT #XXX' will leverage the otherwise
// unused 'sticky' bit
//

type file struct {
	filename string
	osFile   *os.File
	reader   *bufio.Reader
	writer   *bufio.Writer
	iomode   int
	recNo    int
	recBuf   []byte
	fileType int8
}

type forStackNode struct {
	stmt      *stmtNode
	nextStmt  *stmtNode
	item      [5]any
	lastToken int
}

type userDefNode struct {
	fname     string
	firstStmt *stmtNode
	lastStmt  *stmtNode
}

type userDefStackNode struct {
	fname    string
	retval   any
	paramMap map[string]any
}

type userDefParams struct {
	paramNames []string
	paramTypes []int
}

type lhsRetVal struct {
	sym  *symtabNode
	subs []int16
}

type field struct {
	fldel []fieldElementList
}

type fieldElementList struct {
	flde []fieldElement
}

type fieldElement struct {
	fieldVar *symtabNode
	subs     []int16
	offset   int16
	flen     int16
}

type run struct {
	curStmt      *stmtNode
	nextStmt     *stmtNode
	dataList     []any
	gosubStack   []*stmtNode
	forStack     []*forStackNode
	userDefList  []userDefNode
	userDefMap   map[string]*stmtNode
	userDefStack []userDefStackNode
	openFiles    map[int]*file
	fieldMap     map[int]*field
	fip          *faultInfo
	//	det           float64
	dataIndex     int
	onErrorStmtNo int16
	level         int16
	ioTimeout     int16
}

type window struct {
	rows int
	cols int
}

//
// Global variables
//

var buildTimestampStr string

//
// This structure contains the non-persistent state of a program
//

var r run

//
// This structure contains persistent data
//

var g struct {
	program         *avl.AvlTree
	symtabMap       [2]map[string]*symtabNode
	yylex           *Lexer
	parserLiner     *liner.State
	inputLiner      *liner.State
	programFile     *file
	programFilename string
	window          window
	numOutputZones  int
	endStmtNo       int16
	loginTime       time.Time
	denorm          bool
	exiting         bool
	interrupted     bool
	modified        bool
	running         bool
	printStats      bool
	checkAsserts    bool
	traceStack      bool
	traceExec       bool
	traceVars       bool
	traceDump       bool
}

//
// Print zone state
//

var p struct {
	cursorPos  int
	outputZone int
	trailingOp int
}

//
// Runtime statistics for executing program
//

var s struct {
	elapsed       time.Time
	utime         int64
	stime         int64
	numStatements int64
}

//
// These map numeric errors to the corresponding error test and
// vice-versa
//

var errorMap map[string]int16
var errorMapRev map[int16]string

//
// This map is used to keep track of variables which are being traced
//

var tracedVarsMap map[string]bool

// Various BASIC-PLUS errors

var errFilenotfound = errors.New(EFILENOTFOUND)               //nolint:staticcheck
var errProtectionviolation = errors.New(EPROTECTIONVIOLATION) //nolint:staticcheck
var errInvaliddevice = errors.New(EINVALIDDEVICE)             //nolint:staticcheck
var errEndoffile = errors.New(EENDOFFILE)                     //nolint:staticcheck

var isStringMap map[int]bool
var isNumericMap map[int]bool

var bifsHack = []bifHack{{CHRS, "CHR$"}, {CVTFS, "CVTF$"},
	{CVTIS, "CVT%$"}, {CVTSF, "CVT$F"}, {CVTSI, "CVT$%"},
	{DATES, "DATE$"}, {NUMS, "NUM$"}, {SPACES, "SPACE$"},
	{SWAPI, "SWAP%"}, {TIMES, "TIME$"}}

var stringOps = []int{CONCAT, CHRS, CVTFS, CVTIS, DATES, FNSVAR,
	LEFT, MID, NUMS, RIGHT, SCALL, SHA256, SHA512, SPACES, SRPN,
	STRING, SVAR, TAB, TIMES}

var numericOps = []int{ABS, AND, APPROX, ASCII, ATN, COS, CVTSF, CVTSI,
	/*DET,*/ EQ, EQV, ERL, ERR, EXP, FIX, FLOAT, FNFVAR, FNIVAR, FVAR, GE,
	GT, IMP, INT, INSTR, INTEGER, IVAR, LE, LEN, LOG, LOG10, LT, MINUS,
	OR, NCALL, NE, NOT, NRPN, PI, POS, PLUS, POW, RND, SGN, SIN, SLASH,
	SQR, STAR, STREQ, STRGE, STRGT, STRLE, STRLT, STRNE, SWAPI, TAN,
	TIME, UNEG, VAL, XOR, ZER}
