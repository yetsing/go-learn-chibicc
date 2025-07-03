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
	"path/filepath"
	"strings"
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

type Macro struct {
	next      *Macro // Next macro
	name      string // Name of the macro
	isObjlike bool   // Object-lik or function-like macro
	params    *MacroParam
	body      *Token // Body of the macro
	deleted   bool
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

func readMacroParams(rest **Token, tok *Token) *MacroParam {
	head := MacroParam{}
	cur := &head

	for !tok.equal(")") {
		if cur != &head {
			tok = tok.consume(",")
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
		params := readMacroParams(&tok, tok.next)
		m := addMacro(name, false, copyLine(rest, tok))
		m.params = params
	} else {
		// Object-like macro
		addMacro(name, true, copyLine(rest, tok))
	}
}

func readMacroArgOne(rest **Token, tok *Token) *MacroArg {
	head := Token{}
	cur := &head
	level := 0

	for level > 0 || (!tok.equal(",") && !tok.equal(")")) {
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

func readMacroArgs(rest **Token, tok *Token, params *MacroParam) *MacroArg {
	start := tok
	tok = tok.next.next

	head := MacroArg{}
	cur := &head

	pp := params
	for ; pp != nil; pp = pp.next {
		if cur != &head {
			tok = tok.consume(",")
		}
		cur.next = readMacroArgOne(&tok, tok)
		cur = cur.next
		cur.name = pp.name
	}

	if pp != nil {
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

	// Object-like macro application
	if m.isObjlike {
		hs := hidesetUnion(tok.hideset, newHideset(m.name))
		body := addHideset(m.body, hs)
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
	args := readMacroArgs(&tok, tok, m.params)
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
	*rest = appendToken(body, tok.next)
	(*rest).atBol = macroToken.atBol
	(*rest).hasSpace = macroToken.hasSpace
	return true
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

			if filename[0] != '/' {
				path := fmt.Sprintf("%s/%s", filepath.Dir(start.file.name), filename)
				if fileExists(path) {
					tok = includeFile(tok, path, start.next.next)
					continue
				}
			}

			// TODO: Search a file from the include paths.
			tok = includeFile(tok, filename, start.next.next)
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
			tok = skipLine(tok.next)
			m := addMacro(name, true, nil)
			m.deleted = true
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

		// `#`-only line is legal. It's called a null directive.
		if tok.atBol {
			continue
		}

		errorTok(tok, "invalid preprocessor directive")
	}

	cur.next = tok
	return head.next
}

func preprocess(tok *Token) *Token {
	tok = preprocess2(tok)
	convertKeywords(tok)
	return tok
}
