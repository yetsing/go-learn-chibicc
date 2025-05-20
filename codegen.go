package main

import (
	"fmt"
	"os"
)

// #region output utils

var outFile *os.File

func sout(format string, args ...interface{}) {
	fmt.Fprintf(outFile, format, args...)
	fmt.Fprintln(outFile)
}

func unreachable() {
	panic("unreachable")
}

// #endregion

// #region Code Generator
var depth int = 0
var gcount int = 0
var argreg8 = []string{
	"%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b",
}
var argreg16 = []string{"%di", "%si", "%dx", "%cx", "%r8w", "%r9w"}
var argreg32 = []string{
	"%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d",
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
	sout("  push %%rax")
	depth++
}

func pop(arg string) {
	sout("  pop %s", arg)
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
			sout("  lea %d(%%rbp), %%rax", node.variable.offset)
		} else {
			// Global variable
			sout("  lea %s(%%rip), %%rax", node.variable.name)
		}
		return
	case ND_DEREF:
		// *p: p 本身就是地址，直接加载 p 的值
		genExpr(node.lhs)
		return
	case ND_COMMA:
		genExpr(node.lhs)
		genAddr(node.rhs)
		return
	case ND_MEMBER:
		genAddr(node.lhs)
		sout("  add $%d, %%rax", node.member.offset)
		return
	}

	errorTok(node.tok, "not a lvalue %s", node.kind)
}

// Load a value from where %rax is pointing to.
func load(ty *Type) {
	if ty.kind == TY_ARRAY || ty.kind == TY_STRUCT || ty.kind == TY_UNION {
		// If it is an array, do not attempt to load a value to the
		// register because in general we can't load an entire array to a
		// register. As a result, the result of an evaluation of an array
		// becomes not the array itself but the address of the array.
		// This is where "array is automatically converted to a pointer to
		// the first element of the array in C" occurs.
		return
	}

	// When we load a char or a short value to a register, we always
	// extend them to the size of int, so we can assume the lower half of
	// a register always contains a valid value. The upper half of a
	// register for char, short and int may contain garbage. When we load
	// a long value to a register, it simply occupies the entire register.
	// 首先把 RAX 中的值作为内存地址，读取该地址存储的内容，然后再将读取到的内容放到 RAX 中
	if ty.size == 1 {
		sout("  movsbl (%%rax), %%eax")
	} else if ty.size == 2 {
		sout("  movswl (%%rax), %%eax")
	} else if ty.size == 4 {
		sout("  movsxd (%%rax), %%rax")
	} else {
		sout("  mov (%%rax), %%rax")
	}
}

// Store %rax to an address that the stack top is pointing to.
func store(ty *Type) {
	pop("%rdi")

	if ty.kind == TY_STRUCT || ty.kind == TY_UNION {
		// 将结构体赋值给另外一个结构体， rdi rax 保存的都是地址
		// 需要将 rax 中的值逐个字节保存到 rdi 保存的地址中
		for i := range ty.size {
			sout("  mov %d(%%rax), %%r8b", i)
			sout("  mov %%r8b, %d(%%rdi)", i)
		}
		return
	}

	// 将 RAX 中的值保存到 RDI 保存的地址位置
	if ty.size == 1 {
		// 1 byte
		sout("  mov %%al, (%%rdi)")
	} else if ty.size == 2 {
		sout("  mov %%ax, (%%rdi)")
	} else if ty.size == 4 {
		sout("  mov %%eax, (%%rdi)")
	} else {
		sout("  mov %%rax, (%%rdi)")
	}
}

func cmpZero(ty *Type) {
	if ty.isInteger() && ty.size <= 4 {
		sout("  cmp $0, %%eax")
	} else {
		sout("  cmp $0, %%rax")
	}
}

const (
	I8 int = iota
	I16
	I32
	I64
)

func getTypeId(ty *Type) int {
	switch ty.kind {
	case TY_CHAR:
		return I8
	case TY_SHORT:
		return I16
	case TY_INT:
		return I32
	default:
		return I64
	}
}

const (
	i32i8  string = "movsbl %al, %eax"
	i32i16 string = "movswl %ax, %eax"
	i32i64 string = "movsxd %eax, %rax"
)

var castTable = map[int]map[int]string{
	I8: {
		I8:  "",
		I16: "",
		I32: "",
		I64: i32i64,
	},
	I16: {
		I8:  i32i8,
		I16: "",
		I32: "",
		I64: i32i64,
	},
	I32: {
		I8:  i32i8,
		I16: i32i16,
		I32: "",
		I64: i32i64,
	},
	I64: {
		I8:  i32i8,
		I16: i32i16,
		I32: "",
		I64: "",
	},
}

func genCast(from, to *Type) {
	if to.kind == TY_VOID {
		return
	}

	if to.kind == TY_BOOL {
		cmpZero(from)
		sout("  setne %%al")
		sout("  movzb %%al, %%rax")
		return
	}

	t1 := getTypeId(from)
	t2 := getTypeId(to)
	s, ok := castTable[t1][t2]
	if ok {
		sout("  %s", s)
		return
	}
}

// Generate code for a given node.
func genExpr(node *Node) {
	sout("  .loc 1 %d", node.tok.lineno)

	switch node.kind {
	case ND_NUM:
		sout("  mov $%d, %%rax", node.val)
		return
	case ND_NEG:
		genExpr(node.lhs)
		sout("  neg %%rax")
		return
	case ND_VAR:
		genAddr(node)
		load(node.ty)
		return
	case ND_MEMBER:
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
	case ND_STMT_EXPR:
		for n := node.body; n != nil; n = n.next {
			genStmt(n)
		}
		return
	case ND_COMMA:
		genExpr(node.lhs)
		genExpr(node.rhs)
		return
	case ND_CAST:
		genExpr(node.lhs)
		genCast(node.lhs.ty, node.ty)
		return
	case ND_NOT:
		genExpr(node.lhs)
		sout("  cmp $0, %%rax")
		sout("  sete %%al")
		sout("  movzx %%al, %%rax")
		return
	case ND_BITNOT:
		genExpr(node.lhs)
		sout("  not %%rax")
		return
	case ND_LOGAND:
		c := count()
		genExpr(node.lhs)
		sout("  cmp $0, %%rax")
		sout("  je .L.false.%d", c)
		genExpr(node.rhs)
		sout("  cmp $0, %%rax")
		sout("  je .L.false.%d", c)
		sout("  mov $1, %%rax")
		sout("  jmp .L.end.%d", c)
		sout(".L.false.%d:", c)
		sout("  mov $0, %%rax")
		sout(".L.end.%d:", c)
		return
	case ND_LOGOR:
		c := count()
		genExpr(node.lhs)
		sout("  cmp $0, %%rax")
		sout("  jne .L.true.%d", c)
		genExpr(node.rhs)
		sout("  cmp $0, %%rax")
		sout("  jne .L.true.%d", c)
		sout("  mov $0, %%rax")
		sout("  jmp .L.end.%d", c)
		sout(".L.true.%d:", c)
		sout("  mov $1, %%rax")
		sout(".L.end.%d:", c)
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

		sout("  mov $0, %%rax")
		sout("  call %s", node.funcname)
		return
	}

	genExpr(node.rhs)
	push()
	genExpr(node.lhs)
	pop("%rdi")

	var ax, di string
	if node.lhs.ty.kind == TY_LONG || node.lhs.ty.base != nil {
		ax = "%rax"
		di = "%rdi"
	} else {
		ax = "%eax"
		di = "%edi"
	}

	switch node.kind {
	case ND_ADD:
		sout("  add %s, %s", di, ax)
		return
	case ND_SUB:
		sout("  sub %s, %s", di, ax)
		return
	case ND_MUL:
		sout("  imul %s, %s", di, ax)
		return
	case ND_DIV:
		fallthrough
	case ND_MOD:
		if node.lhs.ty.size == 8 {
			sout("  cqo")
		} else {
			sout("  cdq")
		}
		sout("  idiv %s", di)

		if node.kind == ND_MOD {
			sout("  mov %%rdx, %%rax")
		}
		return
	case ND_BITAND:
		sout("  and %%rdi, %%rax")
		return
	case ND_BITOR:
		sout("  or %%rdi, %%rax")
		return
	case ND_BITXOR:
		sout("  xor %%rdi, %%rax")
		return
	case ND_EQ:
		fallthrough
	case ND_NE:
		fallthrough
	case ND_LT:
		fallthrough
	case ND_LE:
		sout("  cmp %s, %s", di, ax)

		if node.kind == ND_EQ {
			sout("  sete %%al")
		} else if node.kind == ND_NE {
			sout("  setne %%al")
		} else if node.kind == ND_LT {
			sout("  setl %%al")
		} else if node.kind == ND_LE {
			sout("  setle %%al")
		}
		sout("  movzb %%al, %%rax")
		return
	}
	errorTok(node.tok, "invalid expression %s", node.kind)
}

func genStmt(node *Node) {
	sout("  .loc 1 %d", node.tok.lineno)

	switch node.kind {
	case ND_IF:
		c := count()
		genExpr(node.cond)
		sout("  cmp $0, %%rax")
		sout("  je .L.else.%d", c)
		genStmt(node.then)
		sout("  jmp .L.end.%d", c)
		sout(".L.else.%d:", c)
		if node.els != nil {
			genStmt(node.els)
		}
		sout(".L.end.%d:", c)
		return
	case ND_FOR:
		c := count()
		if node.init != nil {
			genStmt(node.init)
		}
		sout(".L.begin.%d:", c)
		if node.cond != nil {
			genExpr(node.cond)
			sout("  cmp $0, %%rax")
			sout("  je %s", node.breakLabel)
		}
		genStmt(node.then)
		sout("%s:", node.continueLabel)
		if node.inc != nil {
			genExpr(node.inc)
		}
		sout("  jmp .L.begin.%d", c)
		sout("%s:", node.breakLabel)
		return
	case ND_BLOCK:
		for n := node.body; n != nil; n = n.next {
			genStmt(n)
		}
		return
	case ND_GOTO:
		sout("  jmp %s", node.uniqueLabel)
		return
	case ND_LABEL:
		sout("%s:", node.uniqueLabel)
		genStmt(node.lhs)
		return
	case ND_RETURN:
		genExpr(node.lhs)
		sout("  jmp .L.return.%s", currentFn.name)
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
			// 每个局部变量的地址必须是其类型大小的整数倍（对齐要求）
			offset = alignTo(offset, lvar.ty.align)
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

		sout("  .data")
		if g.isStatic {
			sout("  .local %s", g.name)
		} else {
			sout("  .globl %s", g.name)
		}
		sout("%s:", g.name)

		if g.initData != "" {
			for i := range len(g.initData) {
				sout("  .byte %d", g.initData[i])
			}
			// C 语言中，字符串是以 \0 结尾的
			sout("  .byte 0")
		} else {
			sout("  .zero %d", g.ty.size)
		}
	}
}

func storeGP(r, offset, sz int) {
	switch sz {
	case 1:
		sout("  mov %s, %d(%%rbp)", argreg8[r], offset)
		return
	case 2:
		sout("  mov %s, %d(%%rbp)", argreg16[r], offset)
		return
	case 4:
		sout("    mov %s, %d(%%rbp)", argreg32[r], offset)
		return
	case 8:
		sout("    mov %s, %d(%%rbp)", argreg64[r], offset)
		return
	}
	unreachable()
}

func emitText(prog *Obj) {
	for fn := prog; fn != nil; fn = fn.next {
		if !fn.isFunction || !fn.isDefinition {
			continue
		}

		sout("  .globl %s", fn.name)
		sout("  .text")
		sout("%s:", fn.name)
		currentFn = fn

		// Prologue
		sout("  push %%rbp")
		sout("  mov %%rsp, %%rbp")
		sout("  sub $%d, %%rsp", fn.stackSize)

		// Save passed-by-register arguments to the stack
		i := 0
		for variable := fn.params; variable != nil; variable = variable.next {
			storeGP(i, variable.offset, variable.ty.size)
			i++
		}

		// Emit code
		genStmt(fn.body)
		if depth > 0 {
			panic("stack not empty")
		}

		// Epilogue
		sout(".L.return.%s:", fn.name)
		sout("  mov %%rbp, %%rsp")
		sout("  pop %%rbp")
		sout("  ret")
	}
}

// #endregion

func codegen(prog *Obj, out *os.File) {
	outFile = out
	assignLVarOffsets(prog)
	emitData(prog)
	emitText(prog)
}
