package main

// #region Code Generator
var depth int = 0
var gcount int = 0

func count() int {
	gcount++
	return gcount
}

func push() {
	sout("  push %%rax\n")
	depth++
}

func pop(arg string) {
	sout("  pop %s\n", arg)
	depth--
}

// Round up `n` to the nearest multiple of `align`. For instance,
// align_to(5, 8) returns 8 and align_to(11, 8) returns 16.
func alignTo(n, align int) int {
	return (n + align - 1) / align * align
}

// Compute the absolute address of a given node.
// It's an error if a given node does not reside in memory.
func genAddr(node *Node) {
	switch node.kind {
	case ND_VAR:
		sout("  lea %d(%%rbp), %%rax\n", node.variable.offset)
		return
	case ND_DEREF:
		// *p: p 本身就是地址，直接加载 p 的值
		genExpr(node.lhs)
		return
	}

	errorTok(node.tok, "not a lvalue %s", node.kind)
}

// Generate code for a given node.
func genExpr(node *Node) {
	switch node.kind {
	case ND_NUM:
		sout("  mov $%d, %%rax\n", node.val)
		return
	case ND_NEG:
		genExpr(node.lhs)
		sout("  neg %%rax\n")
		return
	case ND_VAR:
		genAddr(node)
		// 首先把 RAX 中的值作为内存地址，读取该地址存储的内容，然后再将读取到的内容放到 RAX 中
		sout("  mov (%%rax), %%rax\n")
		return
	case ND_DEREF:
		genExpr(node.lhs)
		// 首先把 RAX 中的值作为内存地址，读取该地址存储的内容，然后再将读取到的内容放到 RAX 中
		sout("  mov (%%rax), %%rax\n")
		return
	case ND_ADDR:
		genAddr(node.lhs)
		return
	case ND_ASSIGN:
		genAddr(node.lhs) // 赋值表达式的左边是个地址（左值）
		push()
		genExpr(node.rhs)
		pop("%rdi")
		// 将 RAX 中的值保存到 RDI 保存的地址位置
		sout("  mov %%rax, (%%rdi)\n")
		return
	case ND_FUNCALL:
		sout("  mov $0, %%rax\n")
		sout("  call %s\n", node.funcname)
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
	errorTok(node.tok, "invalid expression %s", node.kind)
}

func genStmt(node *Node) {
	switch node.kind {
	case ND_FOR:
		c := count()
		if node.init != nil {
			genStmt(node.init)
		}
		sout(".L.begin.%d:\n", c)
		if node.cond != nil {
			genExpr(node.cond)
			sout("  cmp $0, %%rax\n")
			sout("  je .L.end.%d\n", c)
		}
		genStmt(node.then)
		if node.inc != nil {
			genExpr(node.inc)
		}
		sout("  jmp .L.begin.%d\n", c)
		sout(".L.end.%d:\n", c)
		return
	case ND_IF:
		c := count()
		genExpr(node.cond)
		sout("  cmp $0, %%rax\n")
		sout("  je .L.else.%d\n", c)
		genStmt(node.then)
		sout("  jmp .L.end.%d\n", c)
		sout(".L.else.%d:\n", c)
		if node.els != nil {
			genStmt(node.els)
		}
		sout(".L.end.%d:\n", c)
		return
	case ND_BLOCK:
		for n := node.body; n != nil; n = n.next {
			genStmt(n)
		}
		return
	case ND_RETURN:
		genExpr(node.lhs)
		sout("  jmp .L.return\n")
		return
	case ND_EXPR_STMT:
		genExpr(node.lhs)
		return
	}

	if node.kind == ND_EXPR_STMT {
		genExpr(node.lhs)
		return
	}

	errorTok(node.tok, "invalid statement %s", node.kind)
}

// Assign offsets to local variables.
func assignLVarOffsets(prog *Function) {
	offset := 0
	for lvar := prog.locals; lvar != nil; lvar = lvar.next {
		offset += 8
		lvar.offset = -offset
	}

	prog.stackSize = alignTo(offset, 16)
}

// #endregion

func codegen(prog *Function) {
	assignLVarOffsets(prog)

	sout("  .global main\n")
	sout("main:\n")

	// Prologue
	sout("  push %%rbp\n")
	sout("  mov %%rsp, %%rbp\n")
	sout("  sub $%d, %%rsp\n", prog.stackSize)

	genStmt(prog.body)
	if depth > 0 {
		panic("stack not empty")
	}

	sout(".L.return:\n")
	sout("  mov %%rbp, %%rsp\n")
	sout("  pop %%rbp\n")
	sout("  ret\n")
}
