package main

// #region Code Generator
var depth int = 0
var gcount int = 0
var argreg8 = []string{
	"%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b",
}
var argreg64 = []string{
	"%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9",
}
var currentFn *Obj

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
		if node.variable.isLocal {
			// Local variable
			sout("  lea %d(%%rbp), %%rax\n", node.variable.offset)
		} else {
			// Global variable
			sout("  lea %s(%%rip), %%rax\n", node.variable.name)
		}
		return
	case ND_DEREF:
		// *p: p 本身就是地址，直接加载 p 的值
		genExpr(node.lhs)
		return
	}

	errorTok(node.tok, "not a lvalue %s", node.kind)
}

// Load a value from where %rax is pointing to.
func load(ty *Type) {
	if ty.kind == TY_ARRAY {
		// If it is an array, do not attempt to load a value to the
		// register because in general we can't load an entire array to a
		// register. As a result, the result of an evaluation of an array
		// becomes not the array itself but the address of the array.
		// This is where "array is automatically converted to a pointer to
		// the first element of the array in C" occurs.
		return
	}

	// 首先把 RAX 中的值作为内存地址，读取该地址存储的内容，然后再将读取到的内容放到 RAX 中
	if ty.size == 1 {
		// 1 byte
		sout("  movsbq (%%rax), %%rax\n")
	} else {
		sout("  mov (%%rax), %%rax\n")
	}
}

// Store %rax to an address that the stack top is pointing to.
func store(ty *Type) {
	pop("%rdi")
	// 将 RAX 中的值保存到 RDI 保存的地址位置
	if ty.size == 1 {
		// 1 byte
		sout("  mov %%al, (%%rdi)\n")
	} else {
		sout("  mov %%rax, (%%rdi)\n")
	}
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
		load(node.ty)
		return
	case ND_DEREF:
		genExpr(node.lhs)
		load(node.ty)
		return
	case ND_ADDR:
		genAddr(node.lhs)
		return
	case ND_ASSIGN:
		genAddr(node.lhs) // 赋值表达式的左边是个地址（左值）
		push()
		genExpr(node.rhs)
		store(node.ty)
		return
	case ND_FUNCALL:
		nargs := 0
		for arg := node.args; arg != nil; arg = arg.next {
			genExpr(arg)
			push()
			nargs++
		}

		for i := nargs - 1; i >= 0; i-- {
			pop(argreg64[i])
		}

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
		sout("  jmp .L.return.%s\n", currentFn.name)
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
func assignLVarOffsets(prog *Obj) {
	for fn := prog; fn != nil; fn = fn.next {
		if !fn.isFunction {
			continue
		}

		offset := 0
		for lvar := fn.locals; lvar != nil; lvar = lvar.next {
			offset += lvar.ty.size
			lvar.offset = -offset
		}

		fn.stackSize = alignTo(offset, 16)
	}
}

// #endregion

// #region Emit

func emitData(prog *Obj) {
	for g := prog; g != nil; g = g.next {
		if g.isFunction {
			continue
		}

		sout("  .data\n")
		sout("  .global %s\n", g.name)
		sout("%s:\n", g.name)
		sout("  .zero %d\n", g.ty.size)
	}
}

func emitText(prog *Obj) {
	for fn := prog; fn != nil; fn = fn.next {
		if !fn.isFunction {
			continue
		}

		sout("  .global %s\n", fn.name)
		sout("  .text\n")
		sout("%s:\n", fn.name)
		currentFn = fn

		// Prologue
		sout("  push %%rbp\n")
		sout("  mov %%rsp, %%rbp\n")
		sout("  sub $%d, %%rsp\n", fn.stackSize)

		// Save passed-by-register arguments to the stack
		i := 0
		for variable := fn.params; variable != nil; variable = variable.next {
			if variable.ty.size == 1 {
				sout("  mov %s, %d(%%rbp)\n", argreg8[i], variable.offset)
			} else {
				sout("  mov %s, %d(%%rbp)\n", argreg64[i], variable.offset)
			}
			i++
		}

		// Emit code
		genStmt(fn.body)
		if depth > 0 {
			panic("stack not empty")
		}

		// Epilogue
		sout(".L.return.%s:\n", fn.name)
		sout("  mov %%rbp, %%rsp\n")
		sout("  pop %%rbp\n")
		sout("  ret\n")
	}
}

// #endregion

func codegen(prog *Obj) {
	assignLVarOffsets(prog)
	emitData(prog)
	emitText(prog)
}
