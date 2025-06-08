package main

import (
	"fmt"
	"math"
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

func pushf() {
	sout("  sub $8, %%rsp")
	sout("  movsd %%xmm0, (%%rsp)")
	depth++
}

func popf(reg int) {
	sout("  movsd (%%rsp), %%xmm%d", reg)
	sout("  add $8, %%rsp")
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
	switch ty.kind {
	case TY_ARRAY:
		fallthrough
	case TY_STRUCT:
		fallthrough
	case TY_UNION:
		// If it is an array, do not attempt to load a value to the
		// register because in general we can't load an entire array to a
		// register. As a result, the result of an evaluation of an array
		// becomes not the array itself but the address of the array.
		// This is where "array is automatically converted to a pointer to
		// the first element of the array in C" occurs.
		return
	case TY_FLOAT:
		sout("  movss (%%rax), %%xmm0")
		return
	case TY_DOUBLE:
		sout("  movsd (%%rax), %%xmm0")
		return
	}

	var insn string
	if ty.isUnsigned {
		insn = "movz"
	} else {
		insn = "movs"
	}

	// When we load a char or a short value to a register, we always
	// extend them to the size of int, so we can assume the lower half of
	// a register always contains a valid value. The upper half of a
	// register for char, short and int may contain garbage. When we load
	// a long value to a register, it simply occupies the entire register.
	// 首先把 RAX 中的值作为内存地址，读取该地址存储的内容，然后再将读取到的内容放到 RAX 中
	if ty.size == 1 {
		sout("  %sbl (%%rax), %%eax", insn)
	} else if ty.size == 2 {
		sout("  %swl (%%rax), %%eax", insn)
	} else if ty.size == 4 {
		sout("  movsxd (%%rax), %%rax")
	} else {
		sout("  mov (%%rax), %%rax")
	}
}

// Store %rax to an address that the stack top is pointing to.
func store(ty *Type) {
	pop("%rdi")

	switch ty.kind {
	case TY_STRUCT:
		fallthrough
	case TY_UNION:
		// 将结构体赋值给另外一个结构体， rdi rax 保存的都是地址
		// 需要将 rax 中的值逐个字节保存到 rdi 保存的地址中
		for i := range ty.size {
			sout("  mov %d(%%rax), %%r8b", i)
			sout("  mov %%r8b, %d(%%rdi)", i)
		}
		return
	case TY_FLOAT:
		sout("  movss %%xmm0, (%%rdi)")
		return
	case TY_DOUBLE:
		sout("  movsd %%xmm0, (%%rdi)")
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
	switch ty.kind {
	case TY_FLOAT:
		sout("  xorps %%xmm1, %%xmm1")
		sout("  ucomiss %%xmm1, %%xmm0")
		return
	case TY_DOUBLE:
		sout("  xorpd %%xmm1, %%xmm1")
		sout("  ucomisd %%xmm1, %%xmm0")
		return
	}

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
	U8
	U16
	U32
	U64
	F32
	F64
)

func getTypeId(ty *Type) int {
	switch ty.kind {
	case TY_CHAR:
		if ty.isUnsigned {
			return U8
		} else {
			return I8
		}
	case TY_SHORT:
		if ty.isUnsigned {
			return U16
		} else {
			return I16
		}
	case TY_INT:
		if ty.isUnsigned {
			return U32
		} else {
			return I32
		}
	case TY_LONG:
		if ty.isUnsigned {
			return U64
		} else {
			return I64
		}
	case TY_FLOAT:
		return F32
	case TY_DOUBLE:
		return F64
	}

	return U64
}

const (
	i32i8  string = "movsbl %al, %eax"
	i32u8  string = "movzbl %al, %eax"
	i32i16 string = "movswl %ax, %eax"
	i32u16 string = "movzwl %ax, %eax"
	i32f32 string = "cvtsi2ssl %eax, %xmm0"
	i32i64 string = "movsxd %eax, %rax"
	i32f64 string = "cvtsi2sdl %eax, %xmm0"

	u32f32 string = "mov %eax, %eax; cvtsi2ssq %rax, %xmm0"
	u32i64 string = "mov %eax, %eax"
	u32f64 string = "mov %eax, %eax; cvtsi2sdq %rax, %xmm0"

	i64f32 string = "cvtsi2ssq %rax, %xmm0"
	i64f64 string = "cvtsi2sdq %rax, %xmm0"

	u64f32 string = "cvtsi2ssq %rax, %xmm0"
	u64f64 string = `test %rax,%rax; js 1f; pxor %xmm0,%xmm0; cvtsi2sd %rax,%xmm0; jmp 2f; 1: mov %rax,%rdi; and $1,%eax; pxor %xmm0,%xmm0; shr %rdi; or %rax,%rdi; cvtsi2sd %rdi,%xmm0; addsd %xmm0,%xmm0; 2:`

	f32i8  string = "cvttss2sil %xmm0, %eax; movsbl %al, %eax"
	f32u8  string = "cvttss2sil %xmm0, %eax; movzbl %al, %eax"
	f32i16 string = "cvttss2sil %xmm0, %eax; movswl %ax, %eax"
	f32u16 string = "cvttss2sil %xmm0, %eax; movzwl %ax, %eax"
	f32i32 string = "cvttss2sil %xmm0, %eax"
	f32u32 string = "cvttss2siq %xmm0, %rax"
	f32i64 string = "cvttss2siq %xmm0, %rax"
	f32u64 string = "cvttss2siq %xmm0, %rax"
	f32f64 string = "cvtss2sd %xmm0, %xmm0"

	f64i8  string = "cvttsd2sil %xmm0, %eax; movsbl %al, %eax"
	f64u8  string = "cvttsd2sil %xmm0, %eax; movzbl %al, %eax"
	f64i16 string = "cvttsd2sil %xmm0, %eax; movswl %ax, %eax"
	f64u16 string = "cvttsd2sil %xmm0, %eax; movzwl %ax, %eax"
	f64i32 string = "cvttsd2sil %xmm0, %eax"
	f64u32 string = "cvttsd2siq %xmm0, %rax"
	f64f32 string = "cvtsd2ss %xmm0, %xmm0"
	f64i64 string = "cvttsd2siq %xmm0, %rax"
	f64u64 string = "cvttsd2siq %xmm0, %rax"
)

var castTable = map[int]map[int]string{
	I8: {
		I8:  "",
		I16: "",
		I32: "",
		I64: i32i64,
		U8:  i32u8,
		U16: i32u16,
		U32: "",
		U64: i32i64,
		F32: i32f32,
		F64: i32f64,
	},
	I16: {
		I8:  i32i8,
		I16: "",
		I32: "",
		I64: i32i64,
		U8:  i32u8,
		U16: i32u16,
		U32: "",
		U64: i32i64,
		F32: i32f32,
		F64: i32f64,
	},
	I32: {
		I8:  i32i8,
		I16: i32i16,
		I32: "",
		I64: i32i64,
		U8:  i32u8,
		U16: i32u16,
		U32: "",
		U64: i32i64,
		F32: i32f32,
		F64: i32f64,
	},
	I64: {
		I8:  i32i8,
		I16: i32i16,
		I32: "",
		I64: "",
		U8:  i32u8,
		U16: i32u16,
		U32: "",
		U64: "",
		F32: i64f32,
		F64: i64f64,
	},
	U8: {
		I8:  i32i8,
		I16: "",
		I32: "",
		I64: i32i64,
		U8:  "",
		U16: "",
		U32: "",
		U64: i32i64,
		F32: i32f32,
		F64: i32f64,
	},
	U16: {
		I8:  i32i8,
		I16: i32i16,
		I32: "",
		I64: i32i64,
		U8:  i32u8,
		U16: "",
		U32: "",
		U64: i32i64,
		F32: i32f32,
		F64: i32f64,
	},
	U32: {
		I8:  i32i8,
		I16: i32i16,
		I32: "",
		I64: u32i64,
		U8:  i32u8,
		U16: i32u16,
		U32: "",
		U64: u32i64,
		F32: u32f32,
		F64: u32f64,
	},
	U64: {
		I8:  i32i8,
		I16: i32i16,
		I32: "",
		I64: "",
		U8:  i32u8,
		U16: i32u16,
		U32: "",
		U64: "",
		F32: u64f32,
		F64: u64f64,
	},
	F32: {
		I8:  f32i8,
		I16: f32i16,
		I32: f32i32,
		I64: f32i64,
		U8:  f32u8,
		U16: f32u16,
		U32: f32u32,
		U64: f32u64,
		F32: "",
		F64: f32f64,
	},
	F64: {
		I8:  f64i8,
		I16: f64i16,
		I32: f64i32,
		I64: f64i64,
		U8:  f64u8,
		U16: f64u16,
		U32: f64u32,
		U64: f64u64,
		F32: f64f32,
		F64: "",
	},
}

func genCast(from, to *Type) {
	if to.kind == TY_VOID {
		return
	}

	if to.kind == TY_BOOL {
		cmpZero(from)
		sout("  setne %%al")
		sout("  movzx %%al, %%eax")
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

func pushArgs(args *Node) {
	if args != nil {
		pushArgs(args.next)

		genExpr(args)
		if args.ty.isFlonum() {
			pushf()
		} else {
			push()
		}
	}
}

// Generate code for a given node.
func genExpr(node *Node) {
	sout("  .loc 1 %d", node.tok.lineno)

	switch node.kind {
	case ND_NULL_EXPR:
		return
	case ND_NUM:
		switch node.ty.kind {
		case TY_FLOAT:
			sout("  mov $%d, %%eax  # float %f", math.Float32bits(float32(node.fval)), node.fval)
			sout("  movq %%rax, %%xmm0")
			return
		case TY_DOUBLE:
			sout("  mov $%d, %%rax  # double %f", math.Float64bits(node.fval), node.fval)
			sout("  movq %%rax, %%xmm0")
			return
		}

		sout("  mov $%d, %%rax", node.val)
		return
	case ND_NEG:
		genExpr(node.lhs)

		switch node.ty.kind {
		case TY_FLOAT:
			sout("  mov $1, %%rax")
			sout("  shl $31, %%rax")
			sout("  movq %%rax, %%xmm1")
			sout("  xorps %%xmm1, %%xmm0")
			return
		case TY_DOUBLE:
			sout("  mov $1, %%rax")
			sout("  shl $63, %%rax")
			sout("  movq %%rax, %%xmm1")
			sout("  xorpd %%xmm1, %%xmm0")
			return
		}

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
	case ND_MEMZERO:
		// `rep stosb` is equivalent to `memset(%rdi, %al, %rcx)`.
		sout("  mov $%d, %%rcx", node.variable.ty.size)
		sout("  lea %d(%%rbp), %%rdi", node.variable.offset)
		sout("  mov $0, %%al")
		sout("  rep stosb")
		return
	case ND_COND:
		c := count()
		genExpr(node.cond)
		cmpZero(node.cond.ty)
		sout("  je .L.else.%d", c)
		genExpr(node.then)
		sout("  jmp .L.end.%d", c)
		sout(".L.else.%d:", c)
		genExpr(node.els)
		sout(".L.end.%d:", c)
		return
	case ND_NOT:
		genExpr(node.lhs)
		cmpZero(node.lhs.ty)
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
		cmpZero(node.lhs.ty)
		sout("  je .L.false.%d", c)
		genExpr(node.rhs)
		cmpZero(node.rhs.ty)
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
		cmpZero(node.lhs.ty)
		sout("  jne .L.true.%d", c)
		genExpr(node.rhs)
		cmpZero(node.rhs.ty)
		sout("  jne .L.true.%d", c)
		sout("  mov $0, %%rax")
		sout("  jmp .L.end.%d", c)
		sout(".L.true.%d:", c)
		sout("  mov $1, %%rax")
		sout(".L.end.%d:", c)
		return
	case ND_FUNCALL:
		pushArgs(node.args)

		gp := 0
		fp := 0
		for arg := node.args; arg != nil; arg = arg.next {
			if arg.ty.isFlonum() {
				popf(fp)
				fp++
			} else {
				pop(argreg64[gp])
				gp++
			}
		}

		// push 一次栈大小增加 8 字节
		// 偶数次刚好是 16 字节对齐
		// 奇数次需要先 sub rsp 8 字节，调用完函数后再 add rsp 8 字节
		if depth%2 == 0 {
			sout("  call %s", node.funcname)
		} else {
			sout("  sub $8, %%rsp")
			sout("  call %s", node.funcname)
			sout("  add $8, %%rsp")
		}

		// It looks like the most significant 48 or 56 bits in RAX may
		// contain garbage if a function return type is short or bool/char,
		// respectively. We clear the upper bits here.
		switch node.ty.kind {
		case TY_BOOL:
			sout("  movzx %%al, %%rax")
			return
		case TY_CHAR:
			if node.ty.isUnsigned {
				sout("  movzbl %%al, %%eax")
			} else {
				sout("  movsbl %%al, %%eax")
			}
			return
		case TY_SHORT:
			if node.ty.isUnsigned {
				sout("  movzwl %%ax, %%eax")
			} else {
				sout("  movswl %%ax, %%eax")
			}
			return
		}
		return
	}

	if node.lhs.ty.isFlonum() {
		genExpr(node.rhs)
		pushf()
		genExpr(node.lhs)
		popf(1)

		var sz string
		if node.lhs.ty.kind == TY_FLOAT {
			sz = "ss"
		} else {
			sz = "sd"
		}

		switch node.kind {
		case ND_ADD:
			sout("  add%s %%xmm1, %%xmm0", sz)
			return
		case ND_SUB:
			sout("  sub%s %%xmm1, %%xmm0", sz)
			return
		case ND_MUL:
			sout("  mul%s %%xmm1, %%xmm0", sz)
			return
		case ND_DIV:
			sout("  div%s %%xmm1, %%xmm0", sz)
			return
		case ND_EQ:
			fallthrough
		case ND_NE:
			fallthrough
		case ND_LT:
			fallthrough
		case ND_LE:
			sout("  ucomi%s %%xmm0, %%xmm1", sz)

			if node.kind == ND_EQ {
				sout("  sete %%al")
				sout("  setnp %%dl")
				sout("  and %%dl, %%al")
			} else if node.kind == ND_NE {
				sout("  setne %%al")
				sout("  setp %%dl")
				sout("  or %%dl, %%al")
			} else if node.kind == ND_LT {
				sout("  seta %%al")
			} else {
				sout("  setae %%al")
			}

			sout("  and $1, %%al")
			sout("  movzb %%al, %%rax")
			return
		}

		errorTok(node.tok, "invalid expression %s", node.kind)
	}

	genExpr(node.rhs)
	push()
	genExpr(node.lhs)
	pop("%rdi")

	var ax, di, dx string
	if node.lhs.ty.kind == TY_LONG || node.lhs.ty.base != nil {
		ax = "%rax"
		di = "%rdi"
		dx = "%rdx"
	} else {
		ax = "%eax"
		di = "%edi"
		dx = "%edx"
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
		if node.ty.isUnsigned {
			sout("  mov $0, %s", dx)
			sout("  div %s", di)
		} else {
			if node.lhs.ty.size == 8 {
				sout("  cqo")
			} else {
				sout("  cdq")
			}
			sout("  idiv %s", di)
		}

		if node.kind == ND_MOD {
			sout("  mov %%rdx, %%rax")
		}
		return
	case ND_BITAND:
		sout("  and %s, %s", di, ax)
		return
	case ND_BITOR:
		sout("  or %s, %s", di, ax)
		return
	case ND_BITXOR:
		sout("  xor %s, %s", di, ax)
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
			if node.lhs.ty.isUnsigned {
				sout("  setb %%al")
			} else {
				sout("  setl %%al")
			}
		} else if node.kind == ND_LE {
			if node.lhs.ty.isUnsigned {
				sout("  setbe %%al")
			} else {
				sout("  setle %%al")
			}
		}

		sout("  movzb %%al, %%rax")
		return
	case ND_SHL:
		sout("  mov %%rdi, %%rcx")
		sout("  shl %%cl, %s", ax)
		return
	case ND_SHR:
		sout("  mov %%rdi, %%rcx")
		if node.lhs.ty.isUnsigned {
			sout("  shr %%cl, %s", ax)
		} else {
			sout("  sar %%cl, %s", ax)
		}
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
		cmpZero(node.cond.ty)
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
			cmpZero(node.cond.ty)
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
	case ND_DO:
		c := count()
		sout(".L.begin.%d:", c)
		genStmt(node.then)
		sout("%s:", node.continueLabel)
		genExpr(node.cond)
		cmpZero(node.cond.ty)
		sout("  jne .L.begin.%d", c)
		sout("%s:", node.breakLabel)
		return
	case ND_SWITCH:
		genExpr(node.cond)

		for n := node.caseNext; n != nil; n = n.caseNext {
			reg := "%eax"
			if node.cond.ty.size == 8 {
				reg = "%rax"
			}
			sout("  cmp $%d, %s", n.val, reg)
			sout("  je %s", n.label)
		}

		if node.defaultCase != nil {
			sout("  jmp %s", node.defaultCase.label)
		}

		sout("  jmp %s", node.breakLabel)
		genStmt(node.then)
		sout("%s:", node.breakLabel)
		return
	case ND_CASE:
		sout("%s:", node.label)
		genStmt(node.lhs)
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
		if node.lhs != nil {
			genExpr(node.lhs)
		}
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
			offset = alignTo(offset, lvar.align)
			lvar.offset = -offset
		}

		fn.stackSize = alignTo(offset, 16)
	}
}

// #endregion

// #region Emit

func emitData(prog *Obj) {
	for g := prog; g != nil; g = g.next {
		if g.isFunction || !g.isDefinition {
			continue
		}

		if g.isStatic {
			sout("  .local %s", g.name)
		} else {
			sout("  .globl %s", g.name)
		}

		sout("  .align %d", g.align)

		if len(g.initData) > 0 {
			sout("  .data")
			sout("%s:", g.name)

			rel := g.rel
			pos := 0
			for pos < g.ty.size {
				if rel != nil && pos == rel.offset {
					sout("  .quad %s%+d", rel.label, rel.addend)
					rel = rel.next
					pos += 8
				} else {
					sout("  .byte %d", g.initData[pos])
					pos++
				}
			}
			continue
		}

		sout("  .bss")
		sout("%s:", g.name)
		sout("  .zero %d", g.ty.size)
	}

}

func storeFp(r, offset, sz int) {
	switch sz {
	case 4:
		sout("  movss %%xmm%d, %d(%%rbp)", r, offset)
		return
	case 8:
		sout("  movsd %%xmm%d, %d(%%rbp)", r, offset)
		return
	}
	unreachable()
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

		if fn.isStatic {
			sout("  .local %s", fn.name)
		} else {
			sout("  .globl %s", fn.name)
		}

		sout("  .text")
		sout("%s:", fn.name)
		currentFn = fn

		// Prologue
		sout("  push %%rbp")
		sout("  mov %%rsp, %%rbp")
		sout("  sub $%d, %%rsp", fn.stackSize)

		// Save arg registers if function is variadic
		if fn.vaArea != nil {
			gp := 0
			fp := 0
			for var_ := fn.params; var_ != nil; var_ = var_.next {
				if var_.ty.isFlonum() {
					fp++
				} else {
					gp++
				}
			}

			off := fn.vaArea.offset

			// va_elem
			sout("  movl $%d, %d(%%rbp)", gp*8, off)
			sout("  movl $%d, %d(%%rbp)", fp*8+48, off+4)
			sout("  movq %%rbp, %d(%%rbp)", off+16)
			sout("  addq $%d, %d(%%rbp)", off+24, off+16)

			// __reg_save_area__
			sout("  movq %%rdi, %d(%%rbp)", off+24)
			sout("  movq %%rsi, %d(%%rbp)", off+32)
			sout("  movq %%rdx, %d(%%rbp)", off+40)
			sout("  movq %%rcx, %d(%%rbp)", off+48)
			sout("  movq %%r8, %d(%%rbp)", off+56)
			sout("  movq %%r9, %d(%%rbp)", off+64)
			sout("  movsd %%xmm0, %d(%%rbp)", off+72)
			sout("  movsd %%xmm1, %d(%%rbp)", off+80)
			sout("  movsd %%xmm2, %d(%%rbp)", off+88)
			sout("  movsd %%xmm3, %d(%%rbp)", off+96)
			sout("  movsd %%xmm4, %d(%%rbp)", off+104)
			sout("  movsd %%xmm5, %d(%%rbp)", off+112)
			sout("  movsd %%xmm6, %d(%%rbp)", off+120)
			sout("  movsd %%xmm7, %d(%%rbp)", off+128)
		}

		// Save passed-by-register arguments to the stack
		gp := 0
		fp := 0
		for var_ := fn.params; var_ != nil; var_ = var_.next {
			if var_.ty.isFlonum() {
				storeFp(fp, var_.offset, var_.ty.size)
				fp++
			} else {
				storeGP(gp, var_.offset, var_.ty.size)
				gp++
			}
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
