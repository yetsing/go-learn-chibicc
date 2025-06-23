package main

import (
	"fmt"
	"path"
)

type CondInclKind int

const (
	IN_THEN CondInclKind = iota // In the `#if` branch
	IN_ELIF                     // In the `#elif` branch
	IN_ELSE                     // In the `#else` branch
)

type Macro struct {
	next    *Macro // Next macro
	name    string // Name of the macro
	body    *Token // Body of the macro
	deleted bool
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
		if isHash(tok) && tok.next.equal("if") {
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
		if isHash(tok) && tok.next.equal("if") {
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

// Read and evaluate a constant expression.
func evalConstExpr(rest **Token, tok *Token) int64 {
	start := tok
	expr := copyLine(rest, tok.next)

	if expr.kind == TK_EOF {
		errorTok(start, "no expression")
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

func addMacro(name string, body *Token) *Macro {
	m := &Macro{
		next: sMacros,
		name: name,
		body: body,
	}
	sMacros = m
	return m
}

// If tok is a macro, expand it and return true.
// Otherwise, do nothing and return false.
func expandMacro(rest **Token, tok *Token) bool {
	m := findMacro(tok)
	if m == nil {
		return false
	}

	*rest = appendToken(m.body, tok.next)
	return true
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
			tok = tok.next

			if tok.kind != TK_STR {
				errorTok(tok, "expected a filename")
			}

			var ipath string
			if tok.str[0] == '/' {
				ipath = tok.str
			} else {
				ipath = fmt.Sprintf("%s/%s", path.Dir(tok.file.name), tok.str)
			}
			tok2 := tokenizeFile(ipath)
			if tok2 == nil {
				errorTok(tok, "could not tokenize file '%s'", ipath)
			}
			tok = skipLine(tok.next)
			tok = appendToken(tok2, tok)
			continue
		}

		if tok.equal("define") {
			tok = tok.next
			if tok.kind != TK_IDENT {
				errorTok(tok, "macro name must be an identifier")
			}
			name := tok.literal
			addMacro(name, copyLine(&tok, tok.next))
			continue
		}

		if tok.equal("undef") {
			tok = tok.next
			if tok.kind != TK_IDENT {
				errorTok(tok, "macro name must be an identifier")
			}
			name := tok.literal
			tok = skipLine(tok.next)
			m := addMacro(name, nil)
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
