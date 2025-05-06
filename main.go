package main

import (
	"fmt"
	"os"
)

func main() {
	args := os.Args
	if len(args) != 2 {
		fmt.Println("Usage: ./chibicc <expression>")
		return
	}

	tok := tokenize(args[1])
	node := parse(tok)
	codegen(node)

}
