package main

func preprocess(tok *Token) *Token {
	convertKeywords(tok)
	return tok
}
