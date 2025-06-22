package main

import (
	"fmt"
	"path"
)

// `#if` can be nested, so we use a stack to manage nested `#if`s.
type CondIncl struct {
	next *CondIncl // Next condition
	tok  *Token    // Token that starts this condition
}

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
	if tok1 == nil || tok1.kind == TK_EOF {
		return tok2
	}

	head := Token{}
	cur := &head

	for ; tok1 != nil && tok1.kind != TK_EOF; tok1 = tok1.next {
		cur.next = copyToken(tok1)
		cur = cur.next
	}
	cur.next = tok2
	return head.next
}

// Skip until next `#endif`.
// Nested `#if` and `#endif` are skipped.
func skipCondIncl(tok *Token) *Token {
	for tok.kind != TK_EOF {
		if isHash(tok) && tok.next.equal("if") {
			tok = skipCondIncl(tok.next.next)
			tok = tok.next
			continue
		}
		if isHash(tok) && tok.next.equal("endif") {
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

func pushCondIncl(tok *Token) *CondIncl {
	ci := &CondIncl{
		next: sCondIncl,
		tok:  tok,
	}
	sCondIncl = ci
	return ci
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

		if tok.equal("if") {
			val := evalConstExpr(&tok, tok)
			pushCondIncl(start)
			if val == 0 {
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
