package main

import (
	"fmt"
	"io"
	"os"
	"strconv"
	"strings"
	"unicode"
)

// #region util functions

// Input file
var currentFile *File

// A list of all input files
var inputFiles []*File

// True if the current position is at the beginning of a line.
var tAtBol bool

// True if the current position follows a space character
var tHasSpace bool

func check(err error) {
	if err != nil {
		panic(err)
	}
}

// Reports an error message in the following format and exit.
//
// foo.c:10: x = y + 1;
// .             ^ <error message here>
func verrorAt(filename string, input string, pos int, format string, args ...interface{}) {
	// Find the line number and column for the error position
	line := 1
	lineStart := 0
	for i := range pos {
		if i >= len(input) {
			break
		}
		if input[i] == '\n' {
			line++
			lineStart = i + 1
		}
	}
	col := pos - lineStart

	// Find the end of the current line
	lineEnd := lineStart
	for lineEnd < len(input) && input[lineEnd] != '\n' {
		lineEnd++
	}

	// Extract the line content
	lineContent := input[lineStart:lineEnd]

	// Print the formatted error location and line content
	n, _ := fmt.Fprintf(os.Stderr, "%s:%d: ", filename, line)
	fmt.Fprintf(os.Stderr, "%s\n", lineContent)

	// Print spaces up to the error position
	fmt.Fprint(os.Stderr, strings.Repeat(" ", col+n))

	// Print caret and error message
	fmt.Fprintf(os.Stderr, "^ ")
	fmt.Fprintf(os.Stderr, format, args...)
	fmt.Fprintln(os.Stderr)
}

func errorAt(pos int, format string, args ...interface{}) {
	verrorAt(currentFile.name, currentFile.contents, pos, format, args...)
	panic("error occurred, exiting")
}

func errorTok(tok *Token, format string, args ...interface{}) {
	verrorAt(tok.file.name, tok.file.contents, tok.pos, format, args...)
	panic("error occurred, exiting")
}

func warnTok(tok *Token, format string, args ...interface{}) {
	verrorAt(tok.file.name, tok.file.contents, tok.pos, format, args...)
}

func ispunct(ch rune) bool {
	return unicode.IsPrint(ch) && !unicode.IsLetter(ch) && !unicode.IsDigit(ch) && !unicode.IsSpace(ch)
}

func readFile(filename string) string {
	if filename == "-" {
		// read from stdin
		data, err := io.ReadAll(os.Stdin)
		check(err)
		return string(data)
	} else {
		data, err := os.ReadFile(filename)
		check(err)
		return string(data)
	}
}

// startswith2 is a case-insensitive version of startswith.
func startswith2(s, prefix string) bool {
	if len(s) < len(prefix) {
		return false
	}
	p := s[:len(prefix)]
	return strings.EqualFold(p, prefix)
}

// #endregion

// #region Tokenizer
type TokenKind int

const (
	TK_IDENT   TokenKind = iota // identifiers
	TK_PUNCT                    // punctuation
	TK_KEYWORD                  // keywords
	TK_STR                      // string literals
	TK_NUM                      // numbers literals
	TK_PP_NUM                   // preprocessor numbers
	TK_EOF                      // end of file
)

type File struct {
	name     string // File name
	fileNo   int    // File number
	contents string // File contents
}

type Token struct {
	kind    TokenKind
	next    *Token
	literal string

	pos    int
	lineno int

	val  int64
	fval float64
	ty   *Type  // Used if TK_NUM or TK_STR
	str  string // String literal contents

	file     *File // Source location
	atBol    bool  // True if this token is at the beginning of a line
	hasSpace bool  // True if this token follows a space character

	hideset *Hideset // For macro expansion
	origin  *Token   // If this is expanded from a macro, the original token
}

func (t *Token) equal(op string) bool {
	return t.literal == op
}

func (t *Token) consume(op string) *Token {
	if !t.equal(op) {
		errorTok(t, "expected '%s', but got '%s'", op, t.literal)
	}
	return t.next
}

func (t *Token) getNumber() int64 {
	if t.kind != TK_NUM {
		errorTok(t, "expected number, but got '%s'", t.literal)
	}
	return t.val
}

// Returns true if c is valid as the first character of an identifier.
func isIdent1(ch rune) bool {
	return unicode.IsLetter(ch) || ch == '_'
}

// Returns true if c is valid as a non-first character of an identifier.
func isIdent2(ch rune) bool {
	return isIdent1(ch) || unicode.IsDigit(ch)
}

func fromHex(ch rune) int {
	if '0' <= ch && ch <= '9' {
		return int(ch - '0')
	} else if 'a' <= ch && ch <= 'f' {
		return int(ch - 'a' + 10)
	}
	return int(ch - 'A' + 10)
}

func readPunct(input string, p int) int {
	kw := []string{
		"<<=", ">>=", "...",
		"==", "!=", "<=", ">=", "->", "+=", "-=", "*=", "/=", "++", "--", "%=", "&=", "|=", "^=", "&&", "||",
		"<<", ">>", "##",
	}
	s := input[p:]
	for _, k := range kw {
		if strings.HasPrefix(s, k) {
			return len(k)
		}
	}
	if ispunct(rune(input[p])) {
		return 1
	}
	return 0
}

func ishexdigit(ch rune) bool {
	return '0' <= ch && ch <= '9' || 'a' <= ch && ch <= 'f' || 'A' <= ch && ch <= 'F'
}

func readEscapedChar(input string, p int) (int, int) {
	if input[p] >= '0' && input[p] <= '7' {
		// Octal escape sequence
		// Read up to 3 octal digits
		octal := 0
		i := 0
		for ; i < 3 && p+i < len(input) && input[p+i] >= '0' && input[p+i] <= '7'; i++ {
			octal = octal*8 + int(input[p+i]-'0')
		}
		return octal, i
	}

	if input[p] == 'x' {
		// Hexadecimal escape sequence
		p++
		hex := 0
		i := 0
		for ; p+i < len(input) && ishexdigit(rune(input[p+i])); i++ {
			if '0' <= input[p+i] && input[p+i] <= '9' {
				hex = hex*16 + int(input[p+i]-'0')
			} else if 'a' <= input[p+i] && input[p+i] <= 'f' {
				hex = hex*16 + int(input[p+i]-'a'+10)
			} else if 'A' <= input[p+i] && input[p+i] <= 'F' {
				hex = hex*16 + int(input[p+i]-'A'+10)
			}
		}
		return hex, i + 1
	}

	// Escape sequences are defined using themselves here. E.g.
	// '\n' is implemented using '\n'. This tautological definition
	// works because the compiler that compiles our compiler knows
	// what '\n' actually is. In other words, we "inherit" the ASCII
	// code of '\n' from the compiler that compiles our compiler,
	// so we don't have to teach the actual code here.
	//
	// This fact has huge implications not only for the correctness
	// of the compiler but also for the security of the generated code.
	// For more info, read "Reflections on Trusting Trust" by Ken Thompson.
	// https://github.com/rui314/chibicc/wiki/thompson1984.pdf
	switch input[p] {
	case 'a':
		return '\a', 1
	case 'b':
		return '\b', 1
	case 't':
		return '\t', 1
	case 'n':
		return '\n', 1
	case 'v':
		return '\v', 1
	case 'f':
		return '\f', 1
	case 'r':
		return '\r', 1
	// [GNU] \e for the ASCII escape character is a GNU C extension.
	case 'e':
		return 27, 1
	default:
		return int(input[p]), 1
	}

}

// Find a closing double-quote
func stringLiteralEnd(input string, p int) int {
	for p <= len(input)-1 && input[p] != '"' {
		if input[p] == '\n' {
			errorAt(p, "unclosed string literal")
		}
		if input[p] == '\\' {
			p++
		}
		p++
	}
	if p > len(input)-1 {
		errorAt(p, "unclosed string literal")
	}
	return p
}

func readStringLiteral(input string, p int, quote int) *Token {
	start := p
	end := stringLiteralEnd(input, quote+1)

	sb := strings.Builder{}
	for p = quote + 1; p < end; p++ {
		if input[p] == '\\' {
			b, n := readEscapedChar(input, p+1)
			sb.WriteByte(byte(b))
			p += n
		} else {
			sb.WriteByte(input[p])
		}
	}

	tok := NewToken(TK_STR, input[start:end+1], start)
	tok.str = sb.String()
	tok.ty = arrayOf(charType(), len(tok.str)+1) // +1 for null terminator
	return tok
}

func NewToken(kind TokenKind, literal string, pos int) *Token {
	v := tAtBol
	v2 := tHasSpace
	tAtBol = false
	tHasSpace = false
	return &Token{
		kind:     kind,
		next:     nil,
		val:      0,
		literal:  literal,
		pos:      pos,
		file:     currentFile,
		atBol:    v,
		hasSpace: v2,
	}
}

// Read a UTF-8-encoded string literal and transcode it in UTF-16.
//
// UTF-16 is yet another variable-width encoding for Unicode. Code
// points smaller than U+10000 are encoded in 2 bytes. Code points
// equal to or larger than that are encoded in 4 bytes. Each 2 bytes
// in the 4 byte sequence is called "surrogate", and a 4 byte sequence
// is called a "surrogate pair".
func readUTF16StringLiteral(input string, p int, quote int) *Token {
	start := p
	end := stringLiteralEnd(input, quote+1)
	var buf []uint16

	for p = quote + 1; p < end; {
		if input[p] == '\\' {
			c, n := readEscapedChar(input, p+1)
			buf = append(buf, uint16(c))
			p += n + 1
			continue
		}

		c, n := decodeUTF8(input[p:])
		p += n
		if c < 0x10000 {
			// Encode a code point in 2 bytes.
			buf = append(buf, uint16(c))
		} else {
			// Encode a code point in 4 bytes.
			c -= 0x10000
			// The first surrogate is 0xD800 + (c >> 10) & 0x3FF
			buf = append(buf, uint16(0xD800+(c>>10)&0x3FF))
			// The second surrogate is 0xDC00 + (c & 0x3FF)
			buf = append(buf, uint16(0xDC00+(c&0x3FF)))
		}
	}

	bytes := make([]byte, len(buf)*2+2) // +2 for null terminator
	for i, c := range buf {
		bytes[i*2] = byte(c & 0xFF)          // Low byte
		bytes[i*2+1] = byte((c >> 8) & 0xFF) // High byte
	}
	tok := NewToken(TK_STR, input[start:end+1], start)
	tok.ty = arrayOf(ushortType(), len(buf)+1) // +1 for null terminator
	tok.str = string(bytes)
	return tok
}

// Read a UTF-8-encoded string literal and transcode it in UTF-32.
//
// UTF-32 is a fixed-width encoding for Unicode. Each code point is
// encoded in 4 bytes.
func readUTF32StringLiteral(input string, p int, quote int, ty *Type) *Token {
	start := p
	end := stringLiteralEnd(input, quote+1)
	var buf []uint32

	for p = quote + 1; p < end; {
		if input[p] == '\\' {
			c, n := readEscapedChar(input, p+1)
			buf = append(buf, uint32(c))
			p += n + 1
			continue
		}

		c, n := decodeUTF8(input[p:])
		p += n
		buf = append(buf, c)
	}

	bytes := make([]byte, len(buf)*4+4) // +4 for null terminator
	for i, c := range buf {
		bytes[i*4] = byte(c & 0xFF)           // Low byte
		bytes[i*4+1] = byte((c >> 8) & 0xFF)  // Second byte
		bytes[i*4+2] = byte((c >> 16) & 0xFF) // Third byte
		bytes[i*4+3] = byte((c >> 24) & 0xFF) // High byte
	}
	tok := NewToken(TK_STR, input[start:end+1], start)
	tok.ty = arrayOf(ty, len(buf)+1) // +1 for null terminator
	tok.str = string(bytes)
	return tok
}

func readCharLiteral(input string, p int, quote int, ty *Type) *Token {
	start := p
	p = quote + 1
	if p >= len(input) {
		errorAt(p, "unclosed character literal")
	}

	var c int
	if input[p] == '\\' {
		c1, n := readEscapedChar(input, p+1)
		c = int(c1)
		p += n + 1
	} else {
		c1, len := decodeUTF8(input[p:])
		p += len
		c = int(c1)
	}

	if p >= len(input) || input[p] != '\'' {
		errorAt(p, "unclosed character literal")
	}

	tok := NewToken(TK_NUM, input[start:p+1], start)
	tok.val = int64(c)
	tok.ty = ty
	return tok
}

func hasCasePrefix(input string, prefix string) bool {
	if len(input) < len(prefix) {
		return false
	}
	start := strings.ToLower(input[:len(prefix)])
	prefix = strings.ToLower(prefix)
	return start == prefix
}

func isNumChar(b byte) bool {
	return (b >= '0' && b <= '9') || (b >= 'a' && b <= 'f') || (b >= 'A' && b <= 'F')
}

func isNumChar2(base int, b byte) bool {
	switch base {
	case 2:
		return b == '0' || b == '1'
	case 8:
		return b >= '0' && b <= '7'
	case 10:
		return b >= '0' && b <= '9'
	case 16:
		return (b >= '0' && b <= '9') || (b >= 'a' && b <= 'f') || (b >= 'A' && b <= 'F')
	default:
		return false
	}
}

func convertPPInt(tok *Token) bool {
	input := tok.literal + "  "
	start := 0
	p := start

	// Read a binary, octal, decimal or hexadecimal number.
	base := 10
	if hasCasePrefix(input[p:], "0x") && isNumChar(input[p+2]) {
		base = 16
		p += 2
	} else if hasCasePrefix(input[p:], "0b") && isNumChar(input[p+2]) {
		base = 2
		p += 2
	} else if input[p] == '0' {
		// if !isNumChar(input[p+1]) {
		// 	// 0
		// 	tok := NewToken(TK_NUM, input[start:p+1], start)
		// 	tok.val = 0
		// 	return tok
		// }
		if isNumChar(input[p+1]) {
			base = 8
			p++
		}
	}

	numStart := p
	for p < len(input) && (isNumChar2(base, input[p])) {
		p++
	}

	val, err := strconv.ParseUint(input[numStart:p], base, 64)
	check(err)

	// Read U, L or LL suffixes.
	l := false
	u := false

	if startswith2(input[p:], "LLU") || startswith2(input[p:], "ULL") {
		p += 3
		l = true
		u = true
	} else if startswith2(input[p:], "UL") || startswith2(input[p:], "LU") {
		p += 2
		l = true
		u = true
	} else if startswith2(input[p:], "LL") {
		p += 2
		l = true
	} else if startswith2(input[p:], "L") {
		p++
		l = true
	} else if startswith2(input[p:], "U") {
		p++
		u = true
	}

	if p < len(tok.literal) {
		return false
	}

	// Infer a type.
	var ty *Type
	if base == 10 {
		if l && u {
			ty = ulongType()
		} else if l {
			ty = longType()
		} else if u {
			val2 := val >> 32
			if val2 != 0 {
				ty = ulongType()
			} else {
				ty = uintType()
			}
		} else {
			val2 := val >> 31
			if val2 != 0 {
				ty = longType()
			} else {
				ty = intType()
			}
		}
	} else {
		if l && u {
			ty = ulongType()
		} else if l {
			val2 := val >> 63
			if val2 != 0 {
				ty = ulongType()
			} else {
				ty = longType()
			}
		} else if u {
			val2 := val >> 32
			if val2 != 0 {
				ty = ulongType()
			} else {
				ty = uintType()
			}
		} else if (val >> 63) != 0 {
			ty = ulongType()
		} else if (val >> 32) != 0 {
			ty = longType()
		} else if (val >> 31) != 0 {
			ty = uintType()
		} else {
			ty = intType()
		}
	}

	tok.kind = TK_NUM
	tok.val = int64(val)
	tok.ty = ty
	return true
}

// The definition of the numeric literal at the preprocessing stage
// is more relaxed than the definition of that at the later stages.
// In order to handle that, a numeric literal is tokenized as a
// "pp-number" token first and then converted to a regular number
// token after preprocessing.
//
// This function converts a pp-number token to a regular number token.
func convertPPNumber(tok *Token) {
	input := tok.literal + "  " // Add trailing space to avoid boundary checks
	p := 0
	if input[p] != '.' {
		// Try to parse as an integer constant.
		if convertPPInt(tok) {
			return
		}
	}

	numEnd := strings.IndexByte(tok.literal, '.')
	if numEnd == -1 {
		numEnd = 0
	}
	for numEnd < len(input) && strings.ContainsRune("abcdefABCDEF0123456789.eEp", rune(input[numEnd])) {
		numEnd++
		if numEnd < len(input) && (input[numEnd-1] == 'e' || input[numEnd-1] == 'E') && (input[numEnd] == '+' || input[numEnd] == '-') {
			numEnd++
		} else if numEnd < len(input) && (input[numEnd-1] == 'p' || input[numEnd-1] == 'P') && (input[numEnd] == '+' || input[numEnd] == '-') {
			numEnd++
		}
	}

	// If it's not an integer, it must be a floating point constant.
	if input[numEnd-1] == 'f' || input[numEnd-1] == 'F' {
		numEnd--
	}
	val, err := strconv.ParseFloat(input[p:numEnd], 64)
	check(err)

	var ty *Type
	if input[numEnd] == 'f' || input[numEnd] == 'F' {
		numEnd++
		ty = floatType()
	} else if input[numEnd] == 'l' || input[numEnd] == 'L' {
		numEnd++
		ty = doubleType()
	} else {
		ty = doubleType()
	}

	if numEnd < len(tok.literal) {
		errorTok(tok, "invalid numeric constant")
	}

	tok.kind = TK_NUM
	tok.fval = val
	tok.ty = ty
}

var keywords = map[string]TokenKind{
	"return":       TK_KEYWORD,
	"if":           TK_KEYWORD,
	"else":         TK_KEYWORD,
	"for":          TK_KEYWORD,
	"while":        TK_KEYWORD,
	"int":          TK_KEYWORD,
	"sizeof":       TK_KEYWORD,
	"char":         TK_KEYWORD,
	"struct":       TK_KEYWORD,
	"union":        TK_KEYWORD,
	"short":        TK_KEYWORD,
	"long":         TK_KEYWORD,
	"void":         TK_KEYWORD,
	"typedef":      TK_KEYWORD,
	"_Bool":        TK_KEYWORD,
	"enum":         TK_KEYWORD,
	"static":       TK_KEYWORD,
	"goto":         TK_KEYWORD,
	"break":        TK_KEYWORD,
	"continue":     TK_KEYWORD,
	"switch":       TK_KEYWORD,
	"case":         TK_KEYWORD,
	"default":      TK_KEYWORD,
	"extern":       TK_KEYWORD,
	"_Alignof":     TK_KEYWORD,
	"_Alignas":     TK_KEYWORD,
	"do":           TK_KEYWORD,
	"signed":       TK_KEYWORD,
	"unsigned":     TK_KEYWORD,
	"const":        TK_KEYWORD,
	"volatile":     TK_KEYWORD,
	"auto":         TK_KEYWORD,
	"register":     TK_KEYWORD,
	"restrict":     TK_KEYWORD,
	"__restrict":   TK_KEYWORD,
	"__restrict__": TK_KEYWORD,
	"_Noreturn":    TK_KEYWORD,
	"float":        TK_KEYWORD,
	"double":       TK_KEYWORD,
}

func convertPPTokens(tok *Token) {
	for t := tok; t != nil; t = t.next {
		if _, ok := keywords[t.literal]; ok {
			t.kind = TK_KEYWORD
		} else if t.kind == TK_PP_NUM {
			convertPPNumber(t)
		}
	}
}

// Initialize line info for all tokens.
func addLineNumbers(tok *Token) {
	line := 1
	lineStart := 0
	for t := tok; t != nil; t = t.next {
		for i := lineStart; i < t.pos; i++ {
			if currentFile.contents[i] == '\n' {
				line++
				lineStart = i + 1
			}
		}
		t.lineno = line
	}
}

func isdigit(ch byte) bool {
	return ch >= '0' && ch <= '9'
}

func isalnum(ch byte) bool {
	return isdigit(ch) || (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
}

// Tokenize the input string and return a linked list of tokens.
func tokenize(file *File) *Token {
	currentFile = file

	input := file.contents
	var head Token
	cur := &head

	tAtBol = true
	tHasSpace = false

	p := 0
	for p < len(input) {
		ch := input[p]

		// Skip line comments.
		if strings.HasPrefix(input[p:], "//") {
			p += 2
			for p < len(input) && input[p] != '\n' {
				p++
			}
			tHasSpace = true
			continue
		}

		// Skip block comments.
		if strings.HasPrefix(input[p:], "/*") {
			q := strings.Index(input[p+2:], "*/")
			if q == -1 {
				errorAt(p, "unclosed block comment")
			}
			p += 2 + q + 2
			tHasSpace = true
			continue
		}

		// Skip newline.
		if ch == '\n' {
			p++
			tAtBol = true
			tHasSpace = false
			continue
		}

		// Skip whitespace characters.
		if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' {
			p++
			tHasSpace = true
			continue
		}

		// Handle numbers
		start := p
		if isdigit(ch) || (ch == '.' && p+1 < len(input) && isdigit(input[p+1])) {
			p++
			for {
				if p+2 < len(input) && strings.ContainsRune("eEpP", rune(input[p])) && strings.Contains("+-", string(input[p+1])) {
					p += 2 // Skip 'e' or 'E' and the sign
				} else if p < len(input) && (isalnum(input[p]) || input[p] == '.') {
					p++
				} else {
					break
				}
			}
			cur.next = NewToken(TK_PP_NUM, input[start:p], start)
			cur = cur.next
			continue
		}

		// Handle string literals
		if ch == '"' {
			cur.next = readStringLiteral(input, p, p)
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// UTF-8 string literal
		if strings.HasPrefix(input[p:], "u8\"") {
			cur.next = readStringLiteral(input, p, p+2)
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// UTF-16 string literal
		if strings.HasPrefix(input[p:], "u\"") {
			cur.next = readUTF16StringLiteral(input, p, p+1)
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// UTF-32 string literal
		if strings.HasPrefix(input[p:], "U\"") {
			cur.next = readUTF32StringLiteral(input, p, p+1, uintType())
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// Handle character literals
		if ch == '\'' {
			cur.next = readCharLiteral(input, p, p, intType())
			cur = cur.next
			cur.val = int64(int8(cur.val)) // Convert to int8
			p += len(cur.literal)
			continue
		}

		// UTF-16 character literal
		if strings.HasPrefix(input[p:], "u'") {
			cur.next = readCharLiteral(input, p, p+1, ushortType())
			cur = cur.next
			cur.val = int64(uint16(cur.val)) // Convert to uint16
			p += len(cur.literal)
			continue
		}

		// Wide character literal
		if strings.HasPrefix(input[p:], "L'") {
			cur.next = readCharLiteral(input, p, p+1, intType())
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// UTF-32 character literal
		if strings.HasPrefix(input[p:], "U'") {
			cur.next = readCharLiteral(input, p, p+1, uintType())
			cur = cur.next
			p += len(cur.literal)
			continue
		}

		// Handle identifiers or keywords
		if isIdent1(rune(ch)) {
			for p < len(input) && isIdent2(rune(input[p])) {
				p++
			}
			cur.next = NewToken(TK_IDENT, input[start:p], start)
			cur = cur.next
			continue
		}

		// Handle punctuation
		punctLen := readPunct(input, p)
		if punctLen > 0 {
			cur.next = NewToken(TK_PUNCT, input[p:p+punctLen], start)
			cur = cur.next
			p += punctLen
			continue
		}

		errorAt(p, "unexpected character: '%c'", ch)
	}
	cur.next = NewToken(TK_EOF, "", p)
	addLineNumbers(head.next)
	return head.next
}

// #endregion

func getInputFiles() []*File {
	return inputFiles
}

func NewFile(name string, fileNo int, contents string) *File {
	return &File{
		name:     name,
		fileNo:   fileNo,
		contents: contents,
	}
}

// Replaces \r or \r\n with \n.
func canonicalizeNewline(p string) string {
	var sb strings.Builder
	i := 0
	for i < len(p) {
		if p[i] == '\r' {
			if i+1 < len(p) && p[i+1] == '\n' {
				i++ // Skip \r\n
			}
			sb.WriteByte('\n')
		} else {
			sb.WriteByte(p[i])
		}
		i++
	}
	return sb.String()
}

// Removes backslashes followed by a newline.
func removeBackslashNewline(p string) string {
	var sb strings.Builder
	i := 0
	for i < len(p) {
		// Check for backslash followed by newline
		if i+1 < len(p) && p[i] == '\\' && p[i+1] == '\n' {
			i += 2 // Skip both characters
		} else {
			sb.WriteByte(p[i])
			i++
		}
	}
	return sb.String()
}

func readUniversalChar(p string, len int) uint32 {
	var c uint32 = 0
	for i := range len {
		if !ishexdigit(rune(p[i])) {
			return 0
		}
		c = (c << 4) | uint32(fromHex(rune(p[i])))
	}
	return c
}

// Replace \u or \U escape sequences with corresponding UTF-8 bytes.
func convertUniversalChars(p string) string {
	var sb strings.Builder
	idx := 0
	len := len(p)

	for idx < len {
		if strings.HasPrefix(p[idx:], "\\u") {
			c := readUniversalChar(p[idx+2:], 4)
			if c != 0 {
				idx += 6 // Skip \uXXXX
				b := encodeUTF8(c)
				sb.Write(b)
			} else {
				sb.WriteByte(p[idx])
				idx++
			}
		} else if strings.HasPrefix(p[idx:], "\\U") {
			c := readUniversalChar(p[idx+2:], 8)
			if c != 0 {
				idx += 10 // Skip \UXXXXXXXX
				b := encodeUTF8(c)
				sb.Write(b)
			} else {
				sb.WriteByte(p[idx])
				idx++
			}
		} else if p[idx] == '\\' {
			sb.WriteByte(p[idx])
			idx++
			sb.WriteByte(p[idx])
			idx++
		} else {
			sb.WriteByte(p[idx])
			idx++
		}
	}
	return sb.String()
}

var fileNo int = 0

func tokenizeFile(filename string) *Token {
	p := readFile(filename)

	p = canonicalizeNewline(p)
	p = removeBackslashNewline(p)
	p = convertUniversalChars(p)

	file := NewFile(filename, fileNo+1, p)

	// Save the filename for assembler .file directive
	inputFiles = append(inputFiles, file)

	fileNo++

	return tokenize(file)
}
