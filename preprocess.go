// This file implements the C preprocessor.
//
// The preprocessor takes a list of tokens as an input and returns a
// new list of tokens as an output.
//
// The preprocessing language is designed in such a way that that's
// guaranteed to stop even if there is a recursive macro.
// Informally speaking, a macro is applied only once for each token.
// That is, if a macro token T appears in a result of direct or
// indirect macro expansion of T, T won't be expanded any further.
// For example, if T is defined as U, and U is defined as T, then
// token T is expanded to U and then to T and the macro expansion
// stops at that point.
//
// To achieve the above behavior, we attach for each token a set of
// macro names from which the token is expanded. The set is called
// "hideset". Hideset is initially empty, and every time we expand a
// macro, the macro name is added to the resulting tokens' hidesets.
//
// The above macro expansion algorithm is explained in this document
// written by Dave Prossor, which is used as a basis for the
// standard's wording:
// https://github.com/rui314/chibicc/wiki/cpp.algo.pdf

package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"
)

func consume(rest **Token, tok *Token, s string) bool {
	if tok.equal(s) {
		*rest = tok.next
		return true
	}
	*rest = tok
	return false
}

type CondInclKind int

const (
	IN_THEN CondInclKind = iota // In the `#if` branch
	IN_ELIF                     // In the `#elif` branch
	IN_ELSE                     // In the `#else` branch
)

type MacroParam struct {
	next *MacroParam // Next parameter
	name string      // Name of the parameter
}

type MacroArg struct {
	next *MacroArg // Next argument
	name string
	tok  *Token
}

type macroHandlerFn func(tok *Token) *Token

type Macro struct {
	next       *Macro // Next macro
	name       string // Name of the macro
	isObjlike  bool   // Object-lik or function-like macro
	params     *MacroParam
	isVariadic bool
	body       *Token // Body of the macro
	deleted    bool
	handler    macroHandlerFn // Handler for this macro
}

// `#if` can be nested, so we use a stack to manage nested `#if`s.
type CondIncl struct {
	next     *CondIncl    // Next condition
	ctx      CondInclKind // Context of this condition
	tok      *Token       // Token that starts this condition
	included bool         // Whether this condition is included
}

var sMacros *Macro      // List of defined macros
var sCondIncl *CondIncl // Stack of conditional inclusions

type Hideset struct {
	next *Hideset // Next hideset
	name string
}

func isHash(tok *Token) bool {
	return tok.atBol && tok.equal("#")
}

func copyToken(tok *Token) *Token {
	t := &Token{}
	*t = *tok
	t.next = nil
	return t
}

func newEof(tok *Token) *Token {
	t := copyToken(tok)
	t.kind = TK_EOF
	t.literal = ""
	return t
}

func newHideset(name string) *Hideset {
	h := &Hideset{
		next: nil,
		name: name,
	}
	return h
}

func hidesetUnion(hs1, hs2 *Hideset) *Hideset {
	head := Hideset{}
	cur := &head

	for ; hs1 != nil; hs1 = hs1.next {
		cur.next = newHideset(hs1.name)
		cur = cur.next
	}
	cur.next = hs2
	return head.next
}

func hidesetContains(hs *Hideset, s string) bool {
	for ; hs != nil; hs = hs.next {
		if hs.name == s {
			return true
		}
	}
	return false
}

func hidesetIntersection(hs1, hs2 *Hideset) *Hideset {
	head := Hideset{}
	cur := &head

	for ; hs1 != nil; hs1 = hs1.next {
		if hidesetContains(hs2, hs1.name) {
			cur.next = newHideset(hs1.name)
			cur = cur.next
		}
	}
	return head.next
}

func addHideset(tok *Token, hs *Hideset) *Token {
	head := Token{}
	cur := &head

	for ; tok != nil; tok = tok.next {
		t := copyToken(tok)
		t.hideset = hidesetUnion(t.hideset, hs)
		cur.next = t
		cur = cur.next
	}
	return head.next
}

// Append tok2 to the end of tok1
func appendToken(tok1, tok2 *Token) *Token {
	if tok1.kind == TK_EOF {
		return tok2
	}

	head := Token{}
	cur := &head

	for ; tok1.kind != TK_EOF; tok1 = tok1.next {
		cur.next = copyToken(tok1)
		cur = cur.next
	}
	cur.next = tok2
	return head.next
}

func skipCondIncl2(tok *Token) *Token {
	for tok.kind != TK_EOF {
		if isHash(tok) && (tok.next.equal("if") || tok.next.equal("ifdef") || tok.next.equal("ifndef")) {
			tok = skipCondIncl2(tok.next.next)
			continue
		}
		if isHash(tok) && tok.next.equal("endif") {
			return tok.next.next
		}
		tok = tok.next
	}
	return tok
}

// Skip until next `#else`, `#elif` or `#endif`.
// Nested `#if` and `#endif` are skipped.
func skipCondIncl(tok *Token) *Token {
	for tok.kind != TK_EOF {
		if isHash(tok) && (tok.next.equal("if") || tok.next.equal("ifdef") || tok.next.equal("ifndef")) {
			// skip nested `#if`
			tok = skipCondIncl2(tok.next.next)
			continue
		}
		if isHash(tok) && (tok.next.equal("elif") || tok.next.equal("else") || tok.next.equal("endif")) {
			break
		}
		tok = tok.next
	}
	return tok
}

// Double-quote a given string and returns it.
func quoteString(s string) string {
	// Escape double quotes and backslashes.
	s = strings.ReplaceAll(s, `\`, `\\`)
	s = strings.ReplaceAll(s, `"`, `\"`)

	// Add double quotes at the beginning and end.
	return fmt.Sprintf(`"%s"`, s)
}

func newStrToken(str string, tmpl *Token) *Token {
	buf := quoteString(str)
	f := NewFile(tmpl.file.name, tmpl.file.fileNo, buf)
	return tokenize(f)
}

// Copy all tokens until the next newline, terminate them with
// an EOF token and then returns them. This function is used to
// create a new list of tokens for `#if` arguments.
func copyLine(rest **Token, tok *Token) *Token {
	head := Token{}
	cur := &head

	for ; !tok.atBol; tok = tok.next {
		cur.next = copyToken(tok)
		cur = cur.next
	}
	cur.next = newEof(tok)
	*rest = tok
	return head.next
}

func newNumToken(val int64, tmpl *Token) *Token {
	buf := fmt.Sprintf("%d\n", val)
	return tokenize(NewFile(tmpl.file.name, tmpl.file.fileNo, buf))
}

func readConstExpr(rest **Token, tok *Token) *Token {
	tok = copyLine(rest, tok)

	head := Token{}
	cur := &head

	for tok.kind != TK_EOF {
		// "defined(foo)" or "defined foo" becomes "1" if macro "foo"
		// is defined. Otherwise "0".
		if tok.equal("defined") {
			start := tok
			hasParen := consume(&tok, tok.next, "(")

			if tok.kind != TK_IDENT {
				errorTok(start, "macro name must be an identifier")
			}
			m := findMacro(tok)
			tok = tok.next

			if hasParen {
				tok = tok.consume(")")
			}

			var ntok *Token
			if m != nil {
				ntok = newNumToken(1, start)
			} else {
				ntok = newNumToken(0, start)
			}
			cur.next = ntok
			cur = cur.next
			continue
		}

		cur.next = tok
		cur = cur.next
		tok = tok.next
	}

	cur.next = tok
	return head.next
}

// Read and evaluate a constant expression.
func evalConstExpr(rest **Token, tok *Token) int64 {
	start := tok
	expr := readConstExpr(rest, tok.next)
	expr = preprocess2(expr)

	if expr.kind == TK_EOF {
		errorTok(start, "no expression")
	}

	// [https://www.sigbus.info/n1570#6.10.1p4] The standard requires
	// we replace remaining non-macro identifiers with "0" before
	// evaluating a constant expression. For example, `#if foo` is
	// equivalent to `#if 0` if foo is not defined.
	for t := expr; t.kind != TK_EOF; t = t.next {
		if t.kind == TK_IDENT {
			next := t.next
			*t = *newNumToken(0, t)
			t.next = next
		}
	}

	// Convert pp-numbers to regular numbers
	convertPPTokens(expr)

	gtok = expr
	val := constExpr()
	if gtok.kind != TK_EOF {
		errorTok(gtok, "extra token")
	}
	return val
}

func pushCondIncl(tok *Token, included bool) *CondIncl {
	ci := &CondIncl{
		next:     sCondIncl,
		ctx:      IN_THEN,
		tok:      tok,
		included: included,
	}
	sCondIncl = ci
	return ci
}

func findMacro(tok *Token) *Macro {
	if tok.kind != TK_IDENT {
		return nil
	}
	for m := sMacros; m != nil; m = m.next {
		if m.name == tok.literal {
			if m.deleted {
				return nil
			} else {
				return m
			}
		}
	}
	return nil
}

func addMacro(name string, isObjlike bool, body *Token) *Macro {
	m := &Macro{
		next:      sMacros,
		name:      name,
		isObjlike: isObjlike,
		body:      body,
	}
	sMacros = m
	return m
}

func readMacroParams(rest **Token, tok *Token, isVariadic *bool) *MacroParam {
	head := MacroParam{}
	cur := &head

	for !tok.equal(")") {
		if cur != &head {
			tok = tok.consume(",")
		}

		if tok.equal("...") {
			*isVariadic = true
			*rest = tok.next.consume(")")
			return head.next
		}

		if tok.kind != TK_IDENT {
			errorTok(tok, "expected an identifier")
		}
		m := &MacroParam{
			name: tok.literal,
		}
		cur.next = m
		cur = cur.next
		tok = tok.next
	}

	*rest = tok.next
	return head.next
}

func readMacroDefinition(rest **Token, tok *Token) {
	if tok.kind != TK_IDENT {
		errorTok(tok, "macro name must be an identifier")
	}
	name := tok.literal
	tok = tok.next

	if !tok.hasSpace && tok.equal("(") {
		// Function-like macro
		isVariadic := false
		params := readMacroParams(&tok, tok.next, &isVariadic)

		m := addMacro(name, false, copyLine(rest, tok))
		m.params = params
		m.isVariadic = isVariadic
	} else {
		// Object-like macro
		addMacro(name, true, copyLine(rest, tok))
	}
}

func readMacroArgOne(rest **Token, tok *Token, readRest bool) *MacroArg {
	head := Token{}
	cur := &head
	level := 0

	for {
		if level == 0 && tok.equal(")") {
			break
		}
		if level == 0 && !readRest && tok.equal(",") {
			break
		}

		if tok.kind == TK_EOF {
			errorTok(tok, "premature end of input")
		}

		if tok.equal("(") {
			level++
		} else if tok.equal(")") {
			level--
		}

		cur.next = copyToken(tok)
		cur = cur.next
		tok = tok.next
	}

	cur.next = newEof(tok)

	arg := &MacroArg{
		tok: head.next,
	}
	*rest = tok
	return arg
}

func readMacroArgs(rest **Token, tok *Token, params *MacroParam, isVariadic bool) *MacroArg {
	start := tok
	tok = tok.next.next

	head := MacroArg{}
	cur := &head

	pp := params
	for ; pp != nil; pp = pp.next {
		if cur != &head {
			tok = tok.consume(",")
		}
		cur.next = readMacroArgOne(&tok, tok, false)
		cur = cur.next
		cur.name = pp.name
	}

	if isVariadic {
		var arg *MacroArg
		if tok.equal(")") {
			arg = &MacroArg{}
			arg.tok = newEof(tok)
		} else {
			if pp != params {
				tok = tok.consume(",")
			}
			arg = readMacroArgOne(&tok, tok, true)
		}
		arg.name = "__VA_ARGS__"
		cur.next = arg
		cur = cur.next
	} else if pp != nil {
		errorTok(start, "too many arguments")
	}

	tok.consume(")")
	*rest = tok
	return head.next
}

func findArg(args *MacroArg, tok *Token) *MacroArg {
	for ap := args; ap != nil; ap = ap.next {
		if ap.name == tok.literal {
			return ap
		}
	}
	return nil
}

// Concatenates all tokens in `tok` and returns a new string.
func joinTokens(tok *Token, end *Token) string {
	// Copy token texts
	var buf strings.Builder
	for t := tok; t != nil && t != end && t.kind != TK_EOF; t = t.next {
		if t != tok && t.hasSpace {
			buf.WriteString(" ")
		}
		buf.WriteString(t.literal)
	}
	return buf.String()
}

// Concatenates all tokens in `arg` and returns a new string token.
// This function is used for the stringizing operator (#).
func stringize(hash *Token, arg *Token) *Token {
	// Create a new string token. We need to set some value to its
	// source location for error reporting function, so we use a macro
	// name token as a template.
	s := joinTokens(arg, nil)
	return newStrToken(s, hash)
}

// Concatenate two tokens to create a new token.
func paste(lhs *Token, rhs *Token) *Token {
	// Paste the two tokens.
	buf := fmt.Sprintf("%s%s", lhs.literal, rhs.literal)

	// Tokenize the resulting string.
	tok := tokenize(NewFile(lhs.file.name, lhs.file.fileNo, buf))
	if tok.next.kind != TK_EOF {
		errorTok(lhs, "pasting forms '%s', an invalid token", buf)
	}
	return tok
}

func hasVarargs(args *MacroArg) bool {
	for ap := args; ap != nil; ap = ap.next {
		if ap.name == "__VA_ARGS__" {
			return ap.tok.kind != TK_EOF
		}
	}
	return false
}

// Replace func-like macro parameters with given arguments.
// tok 是宏定义的 body
func subst(tok *Token, args *MacroArg) *Token {
	head := Token{}
	cur := &head

	for tok.kind != TK_EOF {
		// "#" followed by a parameter is replaced with stringized actuals.
		if tok.equal("#") {
			arg := findArg(args, tok.next)
			if arg == nil {
				errorTok(tok.next, "'#' is not followed by a macro parameter")
			}
			cur.next = stringize(tok, arg.tok)
			cur = cur.next
			tok = tok.next.next // Skip the parameter token
			continue
		}

		// [GNU] If __VA_ARG__ is empty, `,##__VA_ARGS__` is expanded
		// to the empty token list. Otherwise, its expaned to `,` and
		// __VA_ARGS__.
		if tok.equal(",") && tok.next.equal("##") {
			arg := findArg(args, tok.next.next)
			if arg != nil && arg.name == "__VA_ARGS__" {
				if arg.tok.kind == TK_EOF {
					tok = tok.next.next.next // Skip ",##__VA_ARGS__"
				} else {
					cur.next = copyToken(tok) // Keep the comma
					cur = cur.next
					tok = tok.next.next
				}
				continue
			}
		}

		if tok.equal("##") {
			if cur == &head {
				errorTok(tok, "'##' cannot appear at start of macro expansion")
			}

			if tok.next.kind == TK_EOF {
				errorTok(tok, "'##' cannot appear at end of macro expansion")
			}

			arg := findArg(args, tok.next)
			if arg != nil {
				if arg.tok.kind != TK_EOF {
					*cur = *paste(cur, arg.tok)
					for t := arg.tok.next; t.kind != TK_EOF; t = t.next {
						cur.next = copyToken(t)
						cur = cur.next
					}
				}
				tok = tok.next.next
				continue
			}

			*cur = *paste(cur, tok.next)
			tok = tok.next.next
			continue
		}

		arg := findArg(args, tok)

		if arg != nil && tok.next.equal("##") {
			rhs := tok.next.next

			if arg.tok.kind == TK_EOF {
				arg2 := findArg(args, rhs)
				if arg2 != nil {
					for t := arg2.tok; t.kind != TK_EOF; t = t.next {
						cur.next = copyToken(t)
						cur = cur.next
					}
				} else {
					cur.next = copyToken(rhs)
					cur = cur.next
				}
				tok = rhs.next
				continue
			}

			for t := arg.tok; t.kind != TK_EOF; t = t.next {
				cur.next = copyToken(t)
				cur = cur.next
			}
			tok = tok.next
			continue
		}

		// If __VA_ARG__ is empty, __VA_OPT__(x) is expanded to the
		// empty token list. Otherwise, __VA_OPT__(x) is expanded to x.
		if tok.equal("__VA_OPT__") && tok.next.equal("(") {
			arg := readMacroArgOne(&tok, tok.next.next, true)
			if hasVarargs(args) {
				for t := arg.tok; t.kind != TK_EOF; t = t.next {
					cur.next = t
					cur = cur.next
				}
			}
			tok = tok.consume(")")
			continue
		}

		// Handle a macro token. Macro arguments are completely macro-expanded
		// before they are substituted into a macro body.
		if arg != nil {
			// 将宏形参替换为实参
			// 跳过形参 token ，拼接上实参 token
			t := preprocess2(arg.tok)
			t.atBol = tok.atBol
			t.hasSpace = tok.hasSpace
			for ; t.kind != TK_EOF; t = t.next {
				cur.next = copyToken(t)
				cur = cur.next
			}
			tok = tok.next
			continue
		}

		// Handle a non-macro token.
		cur.next = copyToken(tok)
		cur = cur.next
		tok = tok.next
		continue
	}

	cur.next = tok
	return head.next
}

// If tok is a macro, expand it and return true.
// Otherwise, do nothing and return false.
func expandMacro(rest **Token, tok *Token) bool {
	if hidesetContains(tok.hideset, tok.literal) {
		return false
	}

	m := findMacro(tok)
	if m == nil {
		return false
	}

	// Built-in dynamic macro application such as __LINE__
	if m.handler != nil {
		*rest = m.handler(tok)
		(*rest).next = tok.next
		return true
	}

	// Object-like macro application
	if m.isObjlike {
		hs := hidesetUnion(tok.hideset, newHideset(m.name))
		body := addHideset(m.body, hs)
		for t := body; t.kind != TK_EOF; t = t.next {
			t.origin = tok
		}
		*rest = appendToken(body, tok.next)
		(*rest).atBol = tok.atBol
		(*rest).hasSpace = tok.hasSpace
		return true
	}

	// If a funclike macro token is not followed by an argument list,
	// treat it as a normal identifier.
	if !tok.next.equal("(") {
		return false
	}

	// Function-like macro application
	macroToken := tok
	args := readMacroArgs(&tok, tok, m.params, m.isVariadic)
	rparen := tok

	// Tokens that consist a func-like macro invocation may have different
	// hidesets, and if that's the case, it's not clear what the hideset
	// for the new tokens should be. We take the interesection of the
	// macro token and the closing parenthesis and use it as a new hideset
	// as explained in the Dave Prossor's algorithm.
	hs := hidesetIntersection(macroToken.hideset, rparen.hideset)
	hs = hidesetUnion(hs, newHideset(m.name))

	body := subst(m.body, args)
	body = addHideset(body, hs)
	for t := body; t.kind != TK_EOF; t = t.next {
		t.origin = macroToken
	}
	*rest = appendToken(body, tok.next)
	(*rest).atBol = macroToken.atBol
	(*rest).hasSpace = macroToken.hasSpace
	return true
}

func searchIncludePaths(filename string) string {
	if filename[0] == '/' {
		return filename // Absolute path
	}

	// Search a file from the include paths.
	for i := 0; i < len(includePaths); i++ {
		path := fmt.Sprintf("%s/%s", includePaths[i], filename)
		if fileExists(path) {
			return path
		}
	}
	return ""
}

// Read an #include argument.
func readIncludeFilename(rest **Token, tok *Token, isDquote *bool) string {
	// Pattern 1: #include "foo.h"
	if tok.kind == TK_STR {
		// A double-quoted filename for #include is a special kind of
		// token, and we don't want to interpret any escape sequences in it.
		// For example, "\f" in "C:\foo" is not a formfeed character but
		// just two non-control characters, backslash and f.
		// So we don't want to use token->str.
		*isDquote = true
		*rest = skipLine(tok.next)
		return tok.literal[1 : len(tok.literal)-1] // Strip the surrounding double quotes
	}

	// Pattern 2: #include <foo.h>
	if tok.equal("<") {
		// Reconstruct a filename from a sequence of tokens between
		// "<" and ">".
		start := tok

		// Find closing ">".
		for ; !tok.equal(">"); tok = tok.next {
			if tok.atBol || tok.kind == TK_EOF {
				errorTok(tok, "expected '>'")
			}
		}

		*isDquote = false
		*rest = skipLine(tok.next)
		return joinTokens(start.next, tok) // Join tokens between "<" and ">"
	}

	// Pattern 3: #include FOO
	// In this case FOO must be macro-expanded to either
	// a single string token or a sequence of "<" ... ">".
	if tok.kind == TK_IDENT {
		tok2 := preprocess2(copyLine(rest, tok))
		return readIncludeFilename(&tok2, tok2, isDquote)
	}

	errorTok(tok, "expected a filename")
	return "" // Unreachable, but keeps the compiler happy
}

func includeFile(tok *Token, path string, filenameTok *Token) *Token {
	tok2 := tokenizeFile(path)
	if tok2 == nil {
		errorTok(filenameTok, "%s: cannot open file", path)
	}
	return appendToken(tok2, tok)
}

// Some preprocessor directives such as #include allow extraneous
// tokens before newline. This function skips such tokens.
func skipLine(tok *Token) *Token {
	if tok.atBol {
		return tok
	}
	warnTok(tok, "extra token")
	for tok.atBol {
		tok = tok.next
	}
	return tok
}

// Read #line arguments
func readLineMarker(rest **Token, tok *Token) {
	start := tok
	tok = preprocess(copyLine(rest, tok))

	if tok.kind != TK_NUM || tok.ty.kind != TY_INT {
		errorTok(tok, "invalid line marker")
	}
	start.file.lineDelta = int(tok.val) - start.lineno

	tok = tok.next
	if tok.kind == TK_EOF {
		return
	}

	if tok.kind != TK_STR {
		errorTok(tok, "filename expected")
	}
	start.file.displayName = tok.str
}

// Visit all tokens in `tok` while evaluating preprocessing
// macros and directives.
func preprocess2(tok *Token) *Token {
	head := Token{}
	cur := &head

	for tok.kind != TK_EOF {
		// If it is a macro, expand it.
		if expandMacro(&tok, tok) {
			continue
		}

		// Pass through if it is not a "#"
		if !isHash(tok) {
			tok.lineDelta = tok.file.lineDelta
			tok.filename = tok.file.displayName
			cur.next = tok
			cur = cur.next
			tok = tok.next
			continue
		}

		start := tok
		tok = tok.next

		if tok.equal("include") {
			var isDquote bool
			filename := readIncludeFilename(&tok, tok.next, &isDquote)

			if filename[0] != '/' && isDquote {
				path := fmt.Sprintf("%s/%s", filepath.Dir(start.file.name), filename)
				if fileExists(path) {
					tok = includeFile(tok, path, start.next.next)
					continue
				}
			}

			path := searchIncludePaths(filename)
			if path == "" {
				tok = includeFile(tok, filename, start.next.next)
			} else {
				tok = includeFile(tok, path, start.next.next)
			}
			continue
		}

		if tok.equal("define") {
			readMacroDefinition(&tok, tok.next)
			continue
		}

		if tok.equal("undef") {
			tok = tok.next
			if tok.kind != TK_IDENT {
				errorTok(tok, "macro name must be an identifier")
			}
			name := tok.literal
			undefMacro(name)
			tok = skipLine(tok.next)
			continue
		}

		if tok.equal("if") {
			val := evalConstExpr(&tok, tok)
			pushCondIncl(start, val != 0)
			if val == 0 {
				tok = skipCondIncl(tok)
			}
			continue
		}

		if tok.equal("ifdef") {
			defined := findMacro(tok.next) != nil
			pushCondIncl(tok, defined)
			tok = skipLine(tok.next.next)
			if !defined {
				// 条件不满足，跳过 `#ifdef` 部分
				tok = skipCondIncl(tok)
			}
			continue
		}

		if tok.equal("ifndef") {
			defined := findMacro(tok.next) != nil
			pushCondIncl(tok, !defined)
			tok = skipLine(tok.next.next)
			if defined {
				// 条件不满足，跳过 `#ifndef` 部分
				tok = skipCondIncl(tok)
			}
			continue
		}

		if tok.equal("elif") {
			if sCondIncl == nil || sCondIncl.ctx == IN_ELSE {
				errorTok(tok, "stray `#elif`")
			}
			sCondIncl.ctx = IN_ELIF

			if !sCondIncl.included && evalConstExpr(&tok, tok) != 0 {
				sCondIncl.included = true
			} else {
				// 条件不满足，跳过 `#elif` 部分
				tok = skipCondIncl(tok)
			}
			continue
		}

		if tok.equal("else") {
			if sCondIncl == nil || sCondIncl.ctx == IN_ELSE {
				errorTok(tok, "stray `#else`")
			}
			sCondIncl.ctx = IN_ELSE
			tok = skipLine(tok.next)

			if sCondIncl.included {
				// 条件满足，跳过 `#else` 部分
				tok = skipCondIncl(tok)
			}
			continue
		}

		if tok.equal("endif") {
			if sCondIncl == nil {
				errorTok(tok, "stray `#endif`")
			}
			sCondIncl = sCondIncl.next
			tok = skipLine(tok.next)
			continue
		}

		if tok.equal("line") {
			readLineMarker(&tok, tok.next)
			continue
		}

		if tok.kind == TK_PP_NUM {
			readLineMarker(&tok, tok)
			continue
		}

		if tok.equal("error") {
			errorTok(tok, "error")
		}

		// `#`-only line is legal. It's called a null directive.
		if tok.atBol {
			continue
		}

		errorTok(tok, "invalid preprocessor directive")
	}

	cur.next = tok
	return head.next
}

func defineMacro(name string, buf string) {
	tok := tokenize(NewFile("<built-in>", 1, buf))
	addMacro(name, true, tok)
}

func undefMacro(name string) {
	m := addMacro(name, true, nil)
	m.deleted = true
}

func addBuiltin(name string, fn macroHandlerFn) *Macro {
	m := addMacro(name, true, nil)
	m.handler = fn
	return m
}

func fileMacro(tmpl *Token) *Token {
	for tmpl.origin != nil {
		tmpl = tmpl.origin
	}
	return newStrToken(tmpl.file.displayName, tmpl)
}

// __COUNTER__ is expanded to serial values starting from 0.
var counter int64 = 0

func counterMacro(tmpl *Token) *Token {
	t := newNumToken(counter, tmpl)
	counter++
	return t
}

func lineMacro(tmpl *Token) *Token {
	for tmpl.origin != nil {
		tmpl = tmpl.origin
	}
	i := tmpl.lineno + tmpl.file.lineDelta
	return newNumToken(int64(i), tmpl)
}

// __TIMESTAMP__ is expanded to a string describing the last
// modification time of the current file. E.g.
// "Fri Jul 24 01:32:50 2020"
func timestampMacro(tmpl *Token) *Token {
	var fileinfo os.FileInfo
	var err error
	if fileinfo, err = os.Stat(tmpl.file.name); err != nil {
		return newStrToken("??? ??? ?? ??:??:?? ????", tmpl)
	}

	return newStrToken(fileinfo.ModTime().Format("Mon Jan 02 15:04:05 2006"), tmpl)
}

func basefileMacro(tmpl *Token) *Token {
	return newStrToken(baseFile, tmpl)
}

// __DATE__ is expanded to the current date, e.g. "May 17 2020".
func formatDate(dt time.Time) string {
	// Format the date as "May 17 2020".
	return dt.Format("\"Jan 02 2006\"")
}

// __TIME__ is expanded to the current time, e.g. "13:34:03".
func formatTime(dt time.Time) string {
	// Format the time as "13:34:03".
	return dt.Format("\"15:04:05\"")
}

func initMacros() {
	// Define predefined macros
	defineMacro("_LP64", "1")
	defineMacro("__C99_MACRO_WITH_VA_ARGS", "1")
	defineMacro("__ELF__", "1")
	defineMacro("__LP64__", "1")
	defineMacro("__SIZEOF_DOUBLE__", "8")
	defineMacro("__SIZEOF_FLOAT__", "4")
	defineMacro("__SIZEOF_INT__", "4")
	defineMacro("__SIZEOF_LONG_DOUBLE__", "8")
	defineMacro("__SIZEOF_LONG_LONG__", "8")
	defineMacro("__SIZEOF_LONG__", "8")
	defineMacro("__SIZEOF_POINTER__", "8")
	defineMacro("__SIZEOF_PTRDIFF_T__", "8")
	defineMacro("__SIZEOF_SHORT__", "2")
	defineMacro("__SIZEOF_SIZE_T__", "8")
	defineMacro("__SIZE_TYPE__", "unsigned long")
	defineMacro("__STDC_HOSTED__", "1")
	defineMacro("__STDC_NO_ATOMICS__", "1")
	defineMacro("__STDC_NO_COMPLEX__", "1")
	defineMacro("__STDC_NO_THREADS__", "1")
	defineMacro("__STDC_NO_VLA__", "1")
	defineMacro("__STDC_UTF_16__", "1")
	defineMacro("__STDC_UTF_32__", "1")
	defineMacro("__STDC_VERSION__", "201112L")
	defineMacro("__STDC__", "1")
	defineMacro("__USER_LABEL_PREFIX__", "")
	defineMacro("__alignof__", "_Alignof")
	defineMacro("__amd64", "1")
	defineMacro("__amd64__", "1")
	defineMacro("__chibicc__", "1")
	defineMacro("__const__", "const")
	defineMacro("__gnu_linux__", "1")
	defineMacro("__inline__", "inline")
	defineMacro("__linux", "1")
	defineMacro("__linux__", "1")
	defineMacro("__signed__", "signed")
	defineMacro("__typeof__", "typeof")
	defineMacro("__unix", "1")
	defineMacro("__unix__", "1")
	defineMacro("__volatile__", "volatile")
	defineMacro("__x86_64", "1")
	defineMacro("__x86_64__", "1")
	defineMacro("linux", "1")
	defineMacro("unix", "1")

	addBuiltin("__FILE__", fileMacro)
	addBuiltin("__LINE__", lineMacro)
	addBuiltin("__COUNTER__", counterMacro)
	addBuiltin("__TIMESTAMP__", timestampMacro)
	addBuiltin("__BASE_FILE__", basefileMacro)

	t := time.Now()
	defineMacro("__DATE__", formatDate(t))
	defineMacro("__TIME__", formatTime(t))
}

type StringKind int

const (
	STR_NONE StringKind = iota
	STR_UTF8
	STR_UTF16
	STR_UTF32
	STR_WIDE
)

func getStringKind(tok *Token) StringKind {
	if tok.literal == "u8" {
		return STR_UTF8
	}

	switch tok.literal[0] {
	case '"':
		return STR_NONE
	case 'u':
		return STR_UTF16
	case 'U':
		return STR_UTF32
	case 'L':
		return STR_WIDE
	}
	unreachable()
	return STR_NONE // Unreachable, but keeps the compiler happy
}

// Concatenate adjacent string literals into a single string literal
// as per the C spec.
func joinAdjacentStringLiterals(tok *Token) {
	// First pass: If regular string literals are adjacent to wide
	// string literals, regular string literals are converted to a wide
	// type before concatenation. In this pass, we do the conversion.
	for tok1 := tok; tok1.kind != TK_EOF; {
		if tok1.kind != TK_STR || tok1.next.kind != TK_STR {
			tok1 = tok1.next
			continue
		}

		kind := getStringKind(tok1)
		basety := tok1.ty.base

		for t := tok1.next; t.kind == TK_STR; t = t.next {
			k := getStringKind(t)
			if kind == STR_NONE {
				kind = k
				basety = t.ty.base
			} else if k != STR_NONE && k != kind {
				errorTok(t, "unsupported non-standard concatenation of string literals")
			}
		}

		if basety.size > 1 {
			for t := tok1; t.kind == TK_STR; t = t.next {
				if t.ty.base.size == 1 {
					*t = *tokenizeStringLiteral(t, basety)
				}
			}
		}

		for tok1.kind == TK_STR {
			tok1 = tok1.next
		}
	}

	// Second pass: concatenate adjacent string literals.
	for tok1 := tok; tok1.kind != TK_EOF; {
		if tok1.kind != TK_STR || tok1.next.kind != TK_STR {
			tok1 = tok1.next
			continue
		}

		tok2 := tok1.next
		for tok2.kind == TK_STR {
			tok2 = tok2.next
		}

		var sb strings.Builder
		for t := tok1; t != tok2; t = t.next {
			// Strip the surrounding double quotes.
			end := len(t.str)
			if len(t.str) == t.ty.size {
				end = end - t.ty.base.size
			}
			sb.WriteString(t.str[:end])
		}
		// Fill NULL bytes to the end of the string.
		// The size of the string is determined by the base type.
		for range tok1.ty.base.size {
			sb.WriteByte(0)
		}

		newStr := sb.String()
		*tok1 = *copyToken(tok1)
		tok1.ty = arrayOf(tok1.ty.base, int(len(newStr)/tok1.ty.base.size))
		tok1.str = newStr
		tok1.next = tok2
		tok1 = tok2
	}
}

func preprocess(tok *Token) *Token {
	tok = preprocess2(tok)
	convertPPTokens(tok)
	joinAdjacentStringLiterals(tok)

	for t := tok; t != nil; t = t.next {
		t.lineno += t.lineDelta
	}
	return tok
}
