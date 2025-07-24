package main

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"github.com/danswartzendruber/liner"
	"github.com/tklauser/go-sysconf"
	"golang.org/x/term"
	"io"
	"io/fs"
	"math"
	"os"
	"runtime"
	"strconv"
	"strings"
	"syscall"
	"time"
	"unicode"
)

//
// Ensure we are connected to a tty!
//

func checkTerminal() {

	if !term.IsTerminal(2) {
		crash("")
	}

	if !term.IsTerminal(0) {
		crash("Standard input must be a terminal")
	}

	if !term.IsTerminal(1) {
		crash("Standard output must be a terminal")
	}
}

// We create two Liner instances.  One for the parser, and one for
// any INPUT statements.  We do this because we want a scrollback
// history for the parser, but not for user input.  We need to create
// and destroy them in LIFO order, as the Close method is documented
// as 'restoring the terminal to its previous state'.  This means that
// if we create the parser instance, and then the 'input' instance, the
// terminal state will go normal => raw => raw.  If we then close them
// in reverse order, we will see raw => raw => normal
//

func setupLiners() {
	g.parserLiner = setupLiner(false)
	g.inputLiner = setupLiner(true)
}

func setupLiner(allowCtrlC bool) *liner.State {

	l := liner.NewLiner()

	l.SetMultiLineMode(allowCtrlC)

	return l
}

//
// Restore terminal state
//
// We need to Close the Liner instances in reverse order, to make
// sure we end up back in cooked mode.  NB: we cannot call (or cause
// to be called) crash(), as that would recurse
//

func cleanupLiners() {
	cleanupLiner(&g.inputLiner)
	cleanupLiner(&g.parserLiner)
}

func cleanupLiner(linerState **liner.State) {

	if *linerState != nil {
		_ = (*linerState).Close()
		*linerState = nil
	}
}

//
// Read a line from the terminal, with editing and history
//

func readLine(l *liner.State, prompt string, history bool) (string, bool) {

	//
	// Read a line from the liner package
	//

	s, err := l.Prompt(prompt)

	//
	// Annoyingly, a non-nil error here can be totally okay.
	// This happens in the case that the user enters ^D at
	// the beginning of the line (so EOF is seen).  We need to
	// correctly handle ^C in an input statement.  Cleanest way
	// is to signal a runtime error with the same message as if
	// we hit ^C while executing code.  I assume it's also possible
	// to get a 'real' error if something goes wrong (such as the
	// network glitching...)
	//

	if err != nil {
		runtimeCheck((l != g.inputLiner) || (err != liner.ErrPromptAborted),
			EINTERRUPTED)

		switch err {
		default:
			crash(fmt.Sprintf("readLine error: %q\n", err)) // not useful?

		case io.EOF:
			return "", true

		case liner.ErrTimedOut:
			runtimeError(ETIMEOUT)
		}
	}

	runtimeCheck(!g.running || len(s) <= maxLineLen, ELINETOOLONG)

	//
	// If we got here, add the line we just read to our history
	//

	if history {
		l.AppendHistory(s)
	}

	//
	// Finally, hand it back to our caller
	//

	return s, false
}

//
// Prettify the input string.  Eliminate leading and trailing
// whitespace, and replace multiple whitespace characters elsewhere
// with a single space character if not inside a quoted string.
// This is a little more complicated as we can have a single quote
// character inside a double-quoted string, or vice-versa.  We also
// have to require the closing quote character to be the same as the
// opening one
//

func trimWhitespace(s string) string {

	src := []byte(s)
	var dst []byte
	var lastWasBlank bool
	var quoting bool
	var quoteCh byte

	for _, ch := range src {
		if ch == '"' || ch == '\'' {
			if !quoting {
				quoting = true
				quoteCh = ch
				dst = append(dst, ch)
				continue
			} else if ch == quoteCh {
				quoting = false
				dst = append(dst, ch)
				lastWasBlank = false
				continue
			}
		}

		if quoting {
			dst = append(dst, ch)
			continue
		}

		if unicode.IsSpace(rune(ch)) {
			if !lastWasBlank {
				lastWasBlank = true
				dst = append(dst, byte(' '))
			} else { // nolint:staticcheck
				// extra whitespace character - discard
			}
		} else {
			lastWasBlank = false
			dst = append(dst, ch)
		}
	}

	dst = bytes.TrimLeft(dst, " \t")
	dst = bytes.TrimRight(dst, " \t")

	return string(dst)
}

func resetPrint(forceNL bool) {

	printNL := forceNL

	if p.cursorPos != 0 || p.outputZone != 0 {
		printNL = true
		p.outputZone = 0
		p.cursorPos = 0
		p.trailingOp = 0
	}

	if printNL {
		fmt.Println()
	}
}

func curPrintPos() int {

	return (zoneWidth * p.outputZone) + p.cursorPos
}

func basicPrint(msg string, ioch int, checkZone bool) {

	f := os.Stdout

	//
	// Do not allow formatted output to a record file!
	//

	if ioch > 0 {
		of := getOpenFile(ioch)
		checkIOMode(of, IOWRITE)
		runtimeCheck(of.fileType != recordFile, EPROTECTIONVIOLATION)
		of.fileType = printFile
		f = of.osFile
	} else if p.trailingOp == TRAILING_COMMA {
		checkZone = true
	}

	p.trailingOp = 0

	//
	// If writing to an I/O channel, print each item on its own line
	//

	if ioch > 0 {
		msg += "\n"
	}

	if _, err := f.WriteString(msg); err != nil {
		runtimeError(err.Error())
	}

	//
	// If writing to an I/O channel, do not mess with print zones
	//

	if ioch > 0 {
		return
	}

	p.cursorPos += len(msg)

	if !checkZone {
		return
	}

	resid := zoneWidth - p.cursorPos

	for resid < 0 {
		p.outputZone++
		resid += zoneWidth
	}

	if resid > 0 {
		fmt.Printf("%s", strings.Repeat(" ", resid))
		p.cursorPos += resid
	}

	p.outputZone++
	p.cursorPos = 0

	if p.outputZone >= g.numOutputZones {
		resetPrint(false)
	}
}

//
// basicFormat formats a numeric item to be no more than zoneWidth-1
// characters long, taking care to truncate excess characters
// of the mantissa, if needed.  For cosmetic reasons, if we are
// trimming non-zero digits from the right, ensure we don't leave
// any trailing '0' characters, as that looks weird.  e.g. don't
// return something like '123.45600000'
//

func basicFormat(x any) string {

	var retBuf string

	w := zoneWidth - 2

	switch x := x.(type) {
	default:
		unexpectedTypeError(x)

	case int16:
		//
		// retBuf doesn't need to be more than 6 characters long,
		// 5 for an int16 and 1 for the sign, so truncation will
		// never be required
		//

		retBuf = strconv.FormatInt(int64(x), 10)

	case float64:

		//
		// Trim the converted output to the constrained length.
		// If everything after the decimal point is '0', we also
		// want to remove the now extraneous '.'.  e.g. don't return
		// something like '123.'
		//

		fltStr := strconv.FormatFloat(x, 'g', w, 64)
		fltParts := strings.Split(fltStr, "e")

		switch len(fltParts) {
		default:
			fatalError("string.Split botch")

		case 1:
			retBuf = trimString(fltParts[0], w)

		case 2:
			estr := "e" + fltParts[1]
			fltParts[0] = trimString(fltParts[0], w-len(estr))
			fltParts[0] = strings.TrimRight(fltParts[0], "0")
			fltParts[0] = strings.TrimSuffix(fltParts[0], ".")
			retBuf = fltParts[0] + estr
		}
	}

	if retBuf[0] != '-' {
		retBuf = " " + retBuf
	}

	return retBuf + " "
}

//
// Trim a string to a specified maximum length
//

func trimString(str string, maxlen int) string {

	return strings.Clone(str[0:min(len(str), maxlen)])
}

//
// Pad a string with spaces if needed
//

func padString(str string, minlen int, leftPad bool) string {
	if len(str) < minlen {
		if leftPad {
			return strings.Repeat(" ", minlen-len(str)) + strings.Clone(str)
		} else {
			return strings.Clone(str) + strings.Repeat(" ", minlen-len(str))
		}
	} else {
		return str
	}
}

//
// Copy a string, padding with spaces on the left or right as
// indicated, if the string is shorter than the requested length,
// and truncating if it is longer
//

func copyString(src string, reqlen int, leftPad bool) string {

	if len(src) < reqlen {
		return padString(src, reqlen, leftPad)
	} else if len(src) > reqlen {
		return trimString(src, reqlen)
	} else {
		return src
	}
}

//
// Functions to create a 2 dimensional slice of a specified type
// Sleazy: to avoid having 9 value fields (3 types, 3 dimensionalities),
// the symValue entries are always 2-dimensional, where a 1 dimensional
// array is 1,N.  This is complicated by the fact that 1 or 2 dimensional
// arrays run from 0:N in BASIC-PLUS
//

func createFloatArray(bounds [2]int) [][]float64 {

	matrix := make([][]float64, bounds[0])
	for i := 0; i < int(bounds[0]); i++ {
		matrix[i] = make([]float64, bounds[1])
	}

	return matrix
}

func createIntegerArray(bounds [2]int) [][]int16 {

	matrix := make([][]int16, bounds[0])

	for i := 0; i < int(bounds[0]); i++ {
		matrix[i] = make([]int16, bounds[1])
	}

	return matrix
}

func createStringArray(bounds [2]int) [][]string {

	matrix := make([][]string, bounds[0])

	for i := 0; i < int(bounds[0]); i++ {
		matrix[i] = make([]string, bounds[1])
	}

	return matrix
}

func checkArrayUsage(stmt *stmtNode, printIt bool) {

	var mem runtime.MemStats

	runtime.ReadMemStats(&mem)

	if mem.HeapAlloc > maxArrayMemory {
		runtimeErrorStmt(EMATRIXTOOLARGE, stmt)
	}
}

func convertToMB(num uint64) uint64 {

	const MB = 1024 * 1024

	return (num + MB - 1) / MB
}

//
// Routines to interface with OS filesystem code
//

func fileRemove(filename string) error {

	var err error

	if err = os.Remove(filename); err != nil {
		err = mapOSError(err)
	}

	return err
}

func openFileFull(filename string, iomode int, textMode bool) (*file, error) {

	var err error
	var mode int
	var perm fs.FileMode = 0644
	var of file
	var finfo os.FileInfo

	//
	// Sanity check iomode, setting up OS mode for os.OpenFile.
	//

	switch iomode {
	default:
		unexpectedTokenError(iomode)

	case IOREAD:
		mode = os.O_RDONLY

	case IOWRITE:
		mode = (os.O_CREATE | os.O_WRONLY | os.O_TRUNC)

	case IOREAD | IOWRITE:
		mode = (os.O_CREATE | os.O_RDWR)
	}

	//
	// Stat the filename - errFilenotfound is OK
	//

	if finfo, err = os.Stat(filename); err != nil {
		err = mapOSError(err)
	}

	switch err {
	default:
		return nil, err

	//
	// If the file exists, try to determine if it is a BASIC-PLUS
	// record oriented file.  Sticky bit means it is.  Otherwise,
	// a zero-length file is set as emptyFile until we know better
	//

	case nil:
		if !finfo.Mode().IsRegular() {
			return nil, errInvaliddevice
		}

		if (finfo.Mode() & fs.ModeSticky) != 0 {

			//
			// Disallow opening a record file as a text file
			//

			if textMode {
				runtimeError(EPROTECTIONVIOLATION)
			}

			of.fileType = recordFile
		} else if finfo.Size() == 0 {
			of.fileType = emptyFile
		} else {
			of.fileType = printFile
		}

	case errFilenotfound:

		// If errFilenotfound and iomode does not allow writing, bail!

		if (iomode & IOWRITE) == 0 {
			return nil, err
		} else {
			of.fileType = emptyFile
		}
	}

	if of.osFile, err = os.OpenFile(filename, mode, perm); err != nil {
		return nil, mapOSError(err)
	} else {

		of.filename = filename
		of.iomode = iomode

		//
		// reader&writer only for known text file.
		//

		if of.fileType == printFile || textMode {
			of.reader = bufio.NewReader(of.osFile)
			of.writer = bufio.NewWriter(of.osFile)
		} else if of.fileType == recordFile {
			of.recBuf = make([]byte, blockSize)
		}

		return &of, nil
	}
}

func fileExists(filename string) bool {

	//
	// Return false if the file exists and can be seen.
	// We don't care if it can't be opened by the caller,
	// as they will handle any permissions issues
	//

	if _, err := os.Stat(filename); err == nil {
		return true
	} else {
		return false
	}
}

func closeFile(file **file) {

	if err := (*file).osFile.Close(); err != nil {
		fatalError(err.Error())
	}
	*file = nil
}

func fileSize(file *file) int64 {

	name := file.filename

	finfo, err := g.programFile.osFile.Stat()
	if err != nil {
		iErr := err.(*os.PathError)
		runtimeError(fmt.Sprintf("Cannot stat %q (%s)", name,
			iErr.Err.Error()))
	}

	return finfo.Size()
}

func setProgramFilename(name string) {

	g.programFilename = name
}

//
// Prompt user for an action requiring a yes/no
//

func promptYesNo(msg string) bool {

	for {
		prompt := fmt.Sprintf("%s (yes/no)? ", msg)
		line, _ := readLine(g.parserLiner, prompt, false)

		switch line {
		default:
			fmt.Println("Answer yes or no!")
			continue

		case "yes":
			return true

		case "no":
			return false
		}
	}
}

//
// If the file already exists, prompt for confirmation
//

func checkOverwrite(filename string) {

	if !promptYesNo(fmt.Sprintf("Overwrite %s", filename)) {
		runtimeError("File not overwritten")
	}
}

func pluralize(str string, anum any) string {

	var num int
	retString := str

	switch anum := anum.(type) {
	default:
		unexpectedTypeError(anum)

	case int16:
		num = int(anum)

	case int64:
		num = int(anum)

	case uint64:
		num = int(anum)

	case int:
		num = anum
	}

	//
	// Oddity: 0 is considered plural
	//

	if num != 1 {
		retString += "s"
	}

	return retString
}

//
// Check to see if sigHdlr has posted an interrupt
//

func checkInterrupts() {

	if g.interrupted {
		g.interrupted = false
		runtimeError(EINTERRUPTED)
	}
}

func switchSetting(b bool) string {

	if b {
		return "ON"
	} else {
		return "OFF"
	}
}

//
// Helper functions to convert a float64 to different integer
// types, throwing an exception if out of range
//

func floatToInt16(f float64) int16 {

	runtimeCheck(f >= math.MinInt16 && f <= math.MaxInt16, EINTEGERERROR)

	return int16(f)
}

func floatToInt(f float64) int {

	runtimeCheck(f >= math.MinInt32 && f <= math.MaxInt32, EINTEGERERROR)

	return int(f)
}

func floatToInt64(f float64) int64 { //nolint:unused

	runtimeCheck(f >= math.MinInt64 && f <= math.MaxInt64, EINTEGERERROR)

	return int64(f)
}

//
// Accept 'any' and return int
//

func anyToInt(a any) int {

	var i int

	switch a := a.(type) {
	default:
		unexpectedTypeError(a)

	case int:
		i = a

	case float64:
		i = floatToInt(a)

	case int16:
		i = int(a)
	}

	return i
}

//
// Initialize the clock
//

func initClock() {

	s.elapsed = time.Now()
	s.utime, s.stime = getCPUInfo(1)
}

func printCpuUsage() {

	elapsed := time.Since(s.elapsed)
	utime, stime := getCPUInfo(1)

	fmt.Printf("CPU Usage: elapsed = %s / user = %s / system = %s\n",
		formatCPUTime(int64(elapsed.Seconds())),
		formatCPUTime(utime-s.utime), formatCPUTime(stime-s.stime))
}

func formatCPUTime(t int64) string {

	var h, m int64

	if t >= 3600 {
		h = t / 3600
		t = t % 3600
	}

	if t >= 60 {
		m = t / 60
		t = t % 60
	}

	return fmt.Sprintf("%02d:%02d:%02d", h, m, t)
}

func getCPUInfo(divisor int64) (int64, int64) {

	clktck, err := sysconf.Sysconf(sysconf.SC_CLK_TCK)
	if err != nil {
		panic(err)
	} else {
		clktck /= divisor
	}

	contents, err := os.ReadFile("/proc/self/stat")
	if err != nil {
		panic(err)
	}

	fields := strings.Fields(string(contents))

	utime, err := strconv.ParseInt(fields[13], 10, 64)
	if err != nil {
		panic(err)
	}

	stime, err := strconv.ParseInt(fields[14], 10, 64)
	if err != nil {
		panic(err)
	}

	return utime / clktck, stime / clktck
}

//
// This routine implements replacement of a substring.  It's more
// complicated than a simple string replacement, since we want to
// be able to replace a specified substring with another string that
// can be longer, equal or shorter in length.  The location parameters
// are uint16, since the maximum BASIC PLUS string length is 255, but
// the slice end is half-open, so we need to allow 256 as a value.
// NB: the replaced substring can be empty (e.g. sloc and eloc are
// equal), in which case we're basically inserting the replacement
// string at that location
//
// NB: this should only be called on a copy of the line image for a
// statement, as otherwise the token location info will be wrong
//

func replaceSubstring(src string, sloc, eloc uint16, rep string) string {

	first := strings.Clone(src[0:sloc])
	last := strings.Clone(src[eloc:])

	return first + strings.Clone(rep) + last
}

//
// Return a copy of the input string modified per the escape string
//

func colorizeString(str string, tloc *yySymLoc, esc string) string {

	s := uint16(tloc.pos.column) - 1
	e := uint16(tloc.end.column)

	return replaceSubstring(str, s, e, esc+str[s:e]+colorResetSeq)
}

//
// Print denorm state
//

func printDenormState() {
	fmt.Print("Denormalized floats ")

	if g.denorm {
		fmt.Println("enabled")
	} else {
		fmt.Println("disabled")
	}
}

//
// Toggle denorm flag
//

func executeDenorm() {

	g.denorm = !g.denorm

	printDenormState()
}

func executeAssert() {
	if g.checkAsserts {
		fmt.Println("Disabling assertions")
		g.checkAsserts = false
	} else {
		fmt.Println("Enabling assertions")
		g.checkAsserts = true
	}
}

func executeStats() {

	if g.printStats {
		fmt.Println("Disabling statistics")
		g.printStats = false
	} else {
		fmt.Println("Enabling statistics")
		g.printStats = true
	}
}

//
// Toggle trace flags
//

func executeTrace(sw *tokenNode) {

	for tp := sw; tp != nil; tp = tp.next {

		switch tp.token {
		default:
			unexpectedTokenError(tp.token)

		case FVAR:
			fallthrough
		case IVAR:
			fallthrough
		case SVAR:

			//
			// If (un)tracing specific variables, disable global
			// variable trace flag, if set
			//

			g.traceVars = false
			symName := tp.tokenData.(string)
			fmt.Printf("Tracing variable %q ", symName)
			if tracedVarsMap[symName] {
				fmt.Println("disabled")
			} else {
				fmt.Println("enabled")
			}
			tracedVarsMap[symName] = !tracedVarsMap[symName]

		case DUMP:
			g.traceDump = !g.traceDump
			fmt.Printf("toggling traceDump %s\n", switchSetting(g.traceDump))

		case EXEC:
			g.traceExec = !g.traceExec
			fmt.Printf("toggling traceExec %s\n", switchSetting(g.traceExec))

		case VARS:
			g.traceVars = !g.traceVars
			fmt.Printf("toggling traceVars %s\n", switchSetting(g.traceVars))
		}
	}
}

//
// Print a fatal message and abort the process.  We write to standard
// error, since the user may have redirected standard output, and we
// would not see it then.  It would be nice to detect standard error
// being redirected, but where do we write that message?  Also, dup
// os.Stdout, then close os.Stdout and os.Stderr in case another goroutine
// is writing to the terminal.  Make sure to call cleanupLiners, so the
// terminal state is sane
//

func crash(msg string) {

	var w *os.File

	cleanupLiners()

	if msg != "" {
		fd, err := syscall.Dup(int(os.Stderr.Fd()))
		if err == nil {
			_ = os.Stdout.Close()
			_ = os.Stderr.Close()
			w = os.NewFile(uintptr(fd), "stdout on new fd")
		} else {
			w = os.Stderr
		}

		_, _ = fmt.Fprintln(w, msg)
	}

	os.Exit(1)
}

//
// Function to implement an interrutible sleep
//

func sleep(sleepVal int16) {

	for i := 0; i < int(sleepVal); i++ {
		time.Sleep(time.Second)
		checkInterrupts()
	}
}

func closeProgramFile() {

	if g.programFile != nil {
		closeFile(&g.programFile)
		clearModified()
	}
}

//
// Map various Linux errors to our BASIC-PLUS errors, if needed
//

func mapOSError(err error) error {

	if iErr, ok := err.(*os.PathError); ok {
		if errors.Is(err, fs.ErrPermission) {
			err = errProtectionviolation
		} else if errors.Is(err, fs.ErrNotExist) {
			err = errFilenotfound
		} else {
			err = iErr.Err
		}
	} else {
		if err.Error() == "EOF" {
			err = errEndoffile
		}
	}

	return err
}

func checkFilenum(filenum int) {

	runtimeCheck((filenum > 0) && (filenum < maxFilenums), EILLEGALIOCHANNEL)
}

//
// Return valid suffix if present
//

func getFilenameSuffix(filename string) (string, bool) {

	strs := strings.Split(filename, ".")

	switch len(strs) {
	default:
		return "", false

	case 1:
		return "", true

	case 2:
		return "." + strs[1], true
	}
}

//
// Check a requested IO mode against an open file, throwing an
// exception if needed
//

func checkIOMode(fp *file, iomode int) {

	if (fp.iomode & iomode) != iomode {
		runtimeError(EPROTECTIONVIOLATION)
	}
}

//
// Map an ioch to an openFiles entry, throwing an exception if needed
//

func getOpenFile(ioch int) *file {

	var f *file

	checkFilenum(ioch)

	if f = r.openFiles[ioch]; f == nil {
		runtimeError(ENOTOPEN)
	}

	return f
}

//
// Take a filename for a source program and sanity check any
// possible suffix.  If no suffix, append ".bas" and return
// the new filename
//

func validateProgramFilename(filename string) (string, bool) {

	suffix, ok := getFilenameSuffix(filename)
	if !ok || (suffix != "" && suffix != basFileSuffix) {
		return "", false
	} else if suffix == "" {
		return filename + basFileSuffix, true
	} else {
		return filename, true
	}
}

//
// Read a 512 byte block to the 'current' record.  Throws an
// exception if needed
//

func readRecord(of *file, ioch int) {

	osSeekOff := int64((of.recNo - 1) * blockSize)

	//	fmt.Printf("Read record %d from channel %d\n", of.recNo, ioch)

	if _, err := of.osFile.Seek(osSeekOff, 0); err != nil {
		runtimeError(fmt.Sprintf("Seek failure (%s)", err.Error()))
	}

	if _, err := of.osFile.Read(of.recBuf); err != nil {
		runtimeError(mapOSError(err).Error())
	}
}

//
// Write a 512 byte block to the 'current' record.  Throws an
// exception if needed
//

func writeRecord(of *file, ioch int) {

	osSeekOff := int64((of.recNo - 1) * blockSize)

	fmt.Printf("Write record %d to channel %d\n", of.recNo, ioch)

	if _, err := of.osFile.Seek(osSeekOff, 0); err != nil {
		runtimeError(fmt.Sprintf("Seek failure (%s)", err.Error()))
	}

	if _, err := of.osFile.Write(of.recBuf); err != nil {
		runtimeError(fmt.Sprintf("Write error (%s)", err.Error()))
	}
}

//
// Mark the current file as a record file, and set the sticky bit
// to indicate this
//

func setRecordFile(of *file) {

	var fileMode fs.FileMode

	of.fileType = recordFile
	of.recNo = 1
	of.recBuf = make([]byte, blockSize)

	if finfo, err := os.Stat(of.filename); err != nil {
		runtimeError(fmt.Sprintf("Stat failed (%v)", mapOSError(err)))
	} else {
		fileMode = finfo.Mode()
	}

	fileMode |= fs.ModeSticky

	if err := os.Chmod(of.filename, fileMode); err != nil {
		runtimeError(fmt.Sprintf("setRecordFile failed (%v)", err))
	}
}

//
// Function to return a substring.  We need this to clip the start
// and/or length to the actual values for that string, rather than
// throwing an exception - compatibility with DEC implementation
//

func basicSubstring(str string, start, length int) string {

	slen := len(str)

	if start > slen || start <= 0 || length <= 0 {
		return ""
	} else if length+start > slen {
		length = slen - start + 1
	}

	sidx := start - 1
	eidx := length + sidx

	return str[sidx:eidx]
}
