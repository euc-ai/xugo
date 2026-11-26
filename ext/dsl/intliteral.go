package dsl

import "github.com/euc-ai/xugo/utils"

// The chapters write an integer literal `&n`; the parser-faithful
// printers write it `int_of_num(n)`, because a `&` standing alone reads
// as the real embedding. The chapter spelling folds the long form back
// exactly where the parser reads the short one as the integer: beside
// a partner whose own text types it.
//
// The partner rule is the build's (build.go, reconcileNumericDomain):
// the two operands of an arithmetic operator, a comparison or an
// equation are built each by itself, and a side that came out real
// where its partner came out int is rebuilt at int — a `&`, a `-` over
// one, a `+ - *` of such and a power of one rebuild there, nothing
// else does. So an `int_of_num(t)` on one side folds when the OTHER
// side is int by its own spelling (intAnchored), and folds through the
// negations, the sums, differences and products and the power bases
// above it, the positions the rebuild reaches.
//
// Two literals facing each other (`int_of_num(0) < int_of_num(1)`) have
// no such partner and keep the long form: `&0 < &1` is a statement
// about reals. The operands of a congruence need none — `x ≡ y (mod m)`
// is read over ℕ or ℤ and never over ℝ, so a `&` there is the integer's.

// integerLiteralHead is the constant an integer literal is an
// application of; powerSymbol is the operator of the three built-in
// powers, whose exponent is a num whatever the base.
const (
	integerLiteralHead = "int_of_num"
	powerSymbol        = "^"
)

// foldIntLiterals rewrites, bottom-up, every `int_of_num(t)` standing
// where its operator's other operand anchors the integer domain into
// `&t`.
func foldIntLiterals(node astNode, bound map[string]int, declared map[string]bool, changed *bool) astNode {
	again := func(n astNode) astNode { return foldIntLiterals(n, bound, declared, changed) }
	named := func(name string) bool { return bound[name] > 0 || declared[name] }
	switch n := node.(type) {
	case *astField:
		n.receiver = again(n.receiver)
	case *astApp:
		n.fun = again(n.fun)
		for i, a := range n.args {
			n.args[i] = again(a)
		}
	case *astBinOp:
		n.left, n.right = again(n.left), again(n.right)
		if !reconcilesNumericDomain(n.op) {
			return n
		}
		if intAnchored(n.left, named) || intAnchored(n.right, named) {
			n.left = coerceIntLiterals(n.left, named, changed)
			n.right = coerceIntLiterals(n.right, named, changed)
		}
	case *astCong:
		// A congruence has no real instance (cong.go): a `&` among its
		// operands is the integer's with no partner to say so.
		n.left = coerceIntLiterals(again(n.left), named, changed)
		n.right = coerceIntLiterals(again(n.right), named, changed)
		n.modulus = coerceIntLiterals(again(n.modulus), named, changed)
	case *astTendsAt:
		n.fn, n.limit, n.point = again(n.fn), again(n.limit), again(n.point)
	case *astNotNode:
		n.body = again(n.body)
	case *astCoerce:
		n.operand = again(n.operand)
	case *astNeg:
		n.operand = again(n.operand)
	case *astOutfix:
		for i, a := range n.args {
			n.args[i] = again(a)
		}
		if n.sub != nil {
			n.sub = again(n.sub)
		}
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = again(n.body)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astAbsNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		n.body = again(n.body)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
		}
		n.body = again(n.body)
		for _, lf := range leaves {
			bound[lf.name]--
		}
	case *astBigOp:
		n.bound = again(n.bound)
		bound[n.binder]++
		n.body = again(n.body)
		bound[n.binder]--
	}
	return node
}

// reconcilesNumericDomain reports whether op's two operands are built
// each by itself and then brought to one numeric domain: the
// arithmetic operators and comparisons that have an integer instance,
// the equation and its negation.
func reconcilesNumericDomain(op string) bool {
	return op == "=" || op == utils.NeqStr || !intOperator(op).IsZero()
}

// intAnchored reports whether node, an operand standing at type int,
// is typed int by its own text — whether its partner's `&` reads as
// the integer beside it. A name carries its type: a variable the text
// binds or declares, a variable the reading scope types (a text
// printed without declarations, a display), a constant, whose
// instance the printers pin where it is not its declared one. So do
// an application and a notation. A `&` does not, and neither does an
// `int_of_num(t)`, which is what the fold is about to turn into one.
// A negation is anchored as its operand is, a power as its base is, a
// sum, a difference or a product as either of its operands is.
func intAnchored(node astNode, named func(string) bool) bool {
	switch n := node.(type) {
	case *astVar:
		return true
	case *astField:
		return true
	case *astApp:
		return !isIntLiteral(n, named)
	case *astOutfix:
		return true
	case *astNeg:
		return intAnchored(n.operand, named)
	case *astBinOp:
		if n.op == powerSymbol {
			return intAnchored(n.left, named)
		}
		return isValueArithOp(n.op) && (intAnchored(n.left, named) || intAnchored(n.right, named))
	}
	return false
}

// isIntLiteral reports whether n is `int_of_num(t)`, the name being
// the constant's (a variable of that name is not the embedding).
func isIntLiteral(n *astApp, named func(string) bool) bool {
	head, isVar := n.fun.(*astVar)
	return isVar && head.name == integerLiteralHead && len(n.args) == 1 &&
		len(head.typeAnnot) == 0 && !named(head.name)
}

// coerceIntLiterals turns the `int_of_num(t)` of node into `&t` at the
// positions a rebuild at int reaches: node itself, the operand of a
// negation, the operands of a sum, a difference or a product, the base
// of a power.
func coerceIntLiterals(node astNode, named func(string) bool, changed *bool) astNode {
	switch n := node.(type) {
	case *astApp:
		if isIntLiteral(n, named) {
			*changed = true
			return &astCoerce{operand: n.args[0], pos: n.pos}
		}
	case *astNeg:
		n.operand = coerceIntLiterals(n.operand, named, changed)
	case *astBinOp:
		switch {
		case n.op == powerSymbol:
			n.left = coerceIntLiterals(n.left, named, changed)
		case isValueArithOp(n.op):
			n.left = coerceIntLiterals(n.left, named, changed)
			n.right = coerceIntLiterals(n.right, named, changed)
		}
	}
	return node
}
