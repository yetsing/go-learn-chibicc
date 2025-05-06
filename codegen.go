package main

// #region Code Generator
var depth int = 0

func push() {
	sout("  push %%rax\n")
	depth++
}

func pop(arg string) {
	sout("  pop %s\n", arg)
	depth--
}

func genExpr(node *Node) {
	switch node.kind {
	case ND_NUM:
		sout("  mov $%d, %%rax\n", node.val)
		return
	case ND_NEG:
		genExpr(node.lhs)
		sout("  neg %%rax\n")
		return
	}

	genExpr(node.rhs)
	push()
	genExpr(node.lhs)
	pop("%rdi")

	switch node.kind {
	case ND_ADD:
		sout("  add %%rdi, %%rax\n")
		return
	case ND_SUB:
		sout("  sub %%rdi, %%rax\n")
		return
	case ND_MUL:
		sout("  imul %%rdi, %%rax\n")
		return
	case ND_DIV:
		sout("  cqo\n")
		sout("  idiv %%rdi\n")
		return
	case ND_EQ:
		fallthrough
	case ND_NE:
		fallthrough
	case ND_LT:
		fallthrough
	case ND_LE:
		sout("  cmp %%rdi, %%rax\n")

		if node.kind == ND_EQ {
			sout("  sete %%al\n")
		} else if node.kind == ND_NE {
			sout("  setne %%al\n")
		} else if node.kind == ND_LT {
			sout("  setl %%al\n")
		} else if node.kind == ND_LE {
			sout("  setle %%al\n")
		}
		sout("  movzb %%al, %%rax\n")
		return
	}
	errorf("invalid expression %s", node.kind)
}

func genStmt(node *Node) {
	if node.kind == ND_EXPR_STMT {
		genExpr(node.lhs)
		return
	}

	errorf("invalid statement %s", node.kind)
}

// #endregion

func codegen(node *Node) {
	sout("  .global main\n")
	sout("main:\n")

	for node != nil {
		genStmt(node)
		if depth != 0 {
			panic("stack depth is not 0")
		}
		node = node.next
	}
	sout("  ret\n")
}
