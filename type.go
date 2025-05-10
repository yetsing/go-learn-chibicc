package main

type TypeKind int

const (
	TY_INT  TypeKind = iota // int
	TY_PTR                  // pointer
	TY_FUNC                 // function
)

type Type struct {
	kind TypeKind // Type kind

	// Pinter
	base *Type

	// Declaration
	name *Token

	// Function Type
	returnTy *Type
	params   *Type
	next     *Type // next parameter type
}

func newType(kind TypeKind) *Type {
	t := &Type{
		kind: kind,
	}
	return t
}

func intType() *Type {
	t := &Type{
		kind: TY_INT,
	}
	return t
}

func pointerTo(base *Type) *Type {
	t := &Type{
		kind: TY_PTR,
		base: base,
	}
	return t
}

func funcType(returnTy *Type) *Type {
	t := &Type{
		kind:     TY_FUNC,
		returnTy: returnTy,
	}
	return t
}

func (t *Type) isInteger() bool {
	return t.kind == TY_INT
}

func copyType(t *Type) *Type {
	if t == nil {
		return nil
	}

	newTy := &Type{
		kind:     t.kind,
		base:     t.base,
		name:     t.name,
		returnTy: t.returnTy,
		params:   t.params,
		next:     t.next,
	}
	return newTy
}

func addType(node *Node) {
	if node == nil || node.ty != nil {
		return
	}

	addType(node.lhs)
	addType(node.rhs)
	addType(node.cond)
	addType(node.then)
	addType(node.els)
	addType(node.init)
	addType(node.inc)

	for n := node.body; n != nil; n = n.next {
		addType(n)
	}
	for n := node.args; n != nil; n = n.next {
		addType(n)
	}

	switch node.kind {
	case ND_ADD:
		node.ty = node.lhs.ty
		return
	case ND_SUB:
		node.ty = node.lhs.ty
		return
	case ND_MUL:
		node.ty = node.lhs.ty
		return
	case ND_DIV:
		node.ty = node.lhs.ty
		return
	case ND_NEG:
		node.ty = node.lhs.ty
		return
	case ND_ASSIGN:
		node.ty = node.lhs.ty
		return
	case ND_EQ:
		node.ty = intType()
		return
	case ND_NE:
		node.ty = intType()
		return
	case ND_LT:
		node.ty = intType()
		return
	case ND_LE:
		node.ty = intType()
		return
	case ND_VAR:
		node.ty = node.variable.ty
		return
	case ND_NUM:
		node.ty = intType()
		return
	case ND_FUNCALL:
		node.ty = intType()
		return
	case ND_ADDR:
		node.ty = pointerTo(node.lhs.ty)
		return
	case ND_DEREF:
		if node.lhs.ty.kind == TY_PTR {
			node.ty = node.lhs.ty.base
		} else {
			errorTok(node.tok, "invalid pointer dereference")
		}
		return

	}
}
