package main

import (
	"fmt"
	"path"
)

func isHash(tok *Token) bool {
	return tok.atBol && tok.equal("#")
}

func copyToken(tok *Token) *Token {
	t := &Token{}
	*t = *tok
	t.next = nil
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

		tok = tok.next

		if tok.equal("include") {
			tok = tok.next

			if tok.kind != TK_STR {
				errorTok(tok, "expected a filename")
			}

			ipath := fmt.Sprintf("%s/%s", path.Dir(tok.file.name), tok.str)
			tok2 := tokenizeFile(ipath)
			if tok2 == nil {
				errorTok(tok, "could not tokenize file '%s'", ipath)
			}
			tok = skipLine(tok.next)
			tok = appendToken(tok2, tok.next)
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
