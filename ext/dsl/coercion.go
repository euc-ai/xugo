package dsl

import (
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// The chapters write a declared coercion — the constant marked as the
// embedding of the real line into a type, complex_of_real into ℂ
// (ConstSyntax.Coercion) — as `&`: `&x` for a real x, and for a
// numeral under it the numeral's own `&` (`complex_of_real(&0)` is
// `&0`), which the build reads through the real line into the
// codomain. The parser-faithful printers write the application in
// full, and the chapter spelling folds it back to `&` only where
// the build reads the `&` as the lift. A `&` has no type of its own:
// the build types it by its position (build.go, buildCoerce) — the
// domain a constant hands the argument, the domain the application's
// other arguments give a slot they decide where its default does not
// build (buildArgsAgainst), the type of the other operand of an
// equation or an arithmetic operator
// (buildEqOperands, reconcileNumericDomain), the codomain of a λ
// standing at such a position — and where no position asks, a numeral
// is read on the real line and a real is refused at a real domain. So the fold is the
// integer literals' partner rule (intliteral.go) read off the text's
// local types (localType), and a lift whose position the text leaves
// open stays spelled, as the chapters write it:
//
//   - an argument of a constant spelled by name folds at a slot whose
//     declared type is the codomain, or a letter the arguments before
//     it pin to the codomain by their own types:
//     `polynomial_eval(complex_add, &0, complex_mul, &1, p, z)`; a
//     slot no earlier argument pins — a COND's first branch, the zero
//     of a sum whose operation comes after it — keeps
//     `complex_of_real(…)`, though the build reads a `&` there at the
//     type the later arguments give it;
//     so does the argument of a function the text binds or declares
//     at a domain other than the codomain;
//   - an operand of `=`, `≠`, `+`, `-`, `*`, `/`, `≤` or `<` folds
//     where the other operand is typed at the codomain by its own
//     text, and not by a `&` of its own: `z = &0`, `&x - w`,
//     `μ(s) ≤ &0`; of two lifts facing each other the left keeps its
//     spelling (`complex_of_real(x) = &y`);
//   - a lift declared for numerals alone (Coercion.NumeralsOnly) folds
//     only where its operand is the `&` of a num: `extended_of_real(&1)`
//     is `&1`, and `extended_of_real(x)` at a real x keeps its name;
//   - the body of a λ, and the operand of a negation, fold where the
//     λ or the negation stands at such a position.
//
// Every other position keeps the lift spelled: the argument of an
// overloaded word (`exp(complex_of_real(&0))` — the word is picked by
// the argument's type, and `exp(&0)` is ℝ's exponential), of a record
// field, of an outfix several constants share (`|&x|` picks none), the
// operands of a set operator, a term on its own.

// foldCoercions rewrites, top-down, every application of a declared
// coercion standing where the build hands its codomain into `&` of
// its operand. expected is the type the build hands node's position,
// nil where it hands none; bound is the walk's binder stack, whose
// annotated types c.binderTypes keeps beside it.
func (c *implicitCompletion) foldCoercions(node astNode, expected core.HolType, bound map[string]int, changed *bool) astNode {
	fold := func(n astNode, expected core.HolType) astNode { return c.foldCoercions(n, expected, bound, changed) }
	switch n := node.(type) {
	case *astApp:
		head, isVar := n.fun.(*astVar)
		if !isVar {
			n.fun = fold(n.fun, nil)
			for i, a := range n.args {
				n.args[i] = fold(a, nil)
			}
			return n
		}
		if lift := c.liftSyntax(head, n, bound); lift != nil && expected != nil && expected.Equals(lift.Into) && (!lift.NumeralsOnly || c.isNumeralOperand(n.args[0], bound)) {
			*changed = true
			if inner, ok := n.args[0].(*astCoerce); ok {
				return fold(inner, nil)
			}
			return &astCoerce{operand: fold(n.args[0], nil), pos: n.pos}
		}
		// Each argument at the domain the build hands it: the slot
		// under the letters the arguments before it pinned.
		slots := c.argumentDomains(head, n, bound)
		isConstLetter := func(v core.VarType) bool { return strings.HasPrefix(string(v.Name()), constLetterMark) }
		var sigma []core.TypeSubst
		for i, a := range n.args {
			var slot core.HolType
			if i < len(slots) {
				slot = slots[i].Substitute(sigma...)
			}
			n.args[i] = fold(a, slot)
			if slot == nil {
				continue
			}
			if ty, coercion, known := c.localType(n.args[i], bound); known && !coercion {
				if more, ok := slot.Matches(ty, isConstLetter); ok {
					sigma = append(sigma, more...)
				}
			}
		}
		return n
	case *astBinOp:
		if !liftsPartner(n.op) {
			n.left, n.right = fold(n.left, nil), fold(n.right, nil)
			return n
		}
		// The right operand against the left as written, then the left
		// against the right as it now stands: of two lifts facing each
		// other the left keeps its spelling, and the build reads the
		// right one against it.
		n.right = fold(n.right, c.liftCodomain(n.left, bound))
		n.left = fold(n.left, c.liftCodomain(n.right, bound))
		return n
	case *astNeg:
		n.operand = fold(n.operand, expected)
	case *astAbsNode:
		var body core.HolType
		if expected != nil && ext.IsFunType(expected) {
			body = expected.(core.CompositeType).SubType(1)
		}
		for _, name := range n.boundNames() {
			bound[name]++
		}
		c.binderTypes[n.varName] = append(c.binderTypes[n.varName], chapterBinderType(c.syntax, n.varType))
		n.body = fold(n.body, body)
		c.popBinder(n.varName)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astQuantNode:
		for _, name := range n.boundNames() {
			bound[name]++
		}
		c.binderTypes[n.varName] = append(c.binderTypes[n.varName], chapterBinderType(c.syntax, n.varType))
		n.body = fold(n.body, nil)
		c.popBinder(n.varName)
		for _, name := range n.boundNames() {
			bound[name]--
		}
	case *astPatternAbs:
		leaves := n.pat.leaves(nil)
		for _, lf := range leaves {
			bound[lf.name]++
			c.pushBinder(lf.name, nil)
		}
		n.body = fold(n.body, nil)
		for _, lf := range leaves {
			c.popBinder(lf.name)
			bound[lf.name]--
		}
	case *astBigOp:
		n.bound = fold(n.bound, nil)
		bound[n.binder]++
		c.pushBinder(n.binder, nil)
		n.body = fold(n.body, nil)
		c.popBinder(n.binder)
		bound[n.binder]--
	case *astField:
		n.receiver = fold(n.receiver, nil)
	case *astCong:
		n.left, n.right, n.modulus = fold(n.left, nil), fold(n.right, nil), fold(n.modulus, nil)
	case *astTendsAt:
		n.fn, n.limit, n.point = fold(n.fn, nil), fold(n.limit, nil), fold(n.point, nil)
	case *astNotNode:
		n.body = fold(n.body, nil)
	case *astCoerce:
		n.operand = fold(n.operand, nil)
	case *astOutfix:
		for i, a := range n.args {
			n.args[i] = fold(a, nil)
		}
		if n.sub != nil {
			n.sub = fold(n.sub, nil)
		}
	}
	return node
}

// isNumeralOperand reports whether a lift's operand is the `&` of a num
// — a numeral, or a num the text types — the one operand a
// numerals-only lift folds back to `&` (`extended_of_real(&0)` is `&0`,
// `extended_of_real(x)` at a real x stays spelled).
func (c *implicitCompletion) isNumeralOperand(operand astNode, bound map[string]int) bool {
	inner, ok := operand.(*astCoerce)
	if !ok {
		return false
	}
	ty, _, known := c.localType(inner.operand, bound)
	return known && ty.Equals(NumType)
}

// liftSyntax is the coercion declaration of an application's head where
// the application is a declared coercion applied to its one operand:
// a constant of the table, not a name the text binds or declares, and
// carrying no instance annotation. nil otherwise.
func (c *implicitCompletion) liftSyntax(head *astVar, n *astApp, bound map[string]int) *Coercion {
	if len(n.args) != 1 || len(head.typeAnnot) > 0 || bound[head.name] > 0 || c.declared(head.name) {
		return nil
	}
	syn := c.syntax.ConstSyntax(head.name)
	if syn == nil {
		return nil
	}
	return syn.Coercion
}

// argumentDomains is the domains the build hands the arguments of an
// application headed by the variable head: a bound or declared
// function's annotated domains; a constant's declared slots with its
// letters marked apart (constTypeApart), less the implicit prefix the
// chapter spelling elided (astApp.elided); nil where the text fixes
// none — a head the overload fold replaced by its word names no
// constant.
func (c *implicitCompletion) argumentDomains(head *astVar, n *astApp, bound map[string]int) []core.HolType {
	if bound[head.name] > 0 || c.declared(head.name) {
		var ty core.HolType
		if bound[head.name] > 0 {
			ty = c.binderType(head.name)
		} else if c.declaredType != nil {
			ty = c.declaredType(head.name)
		}
		if ty == nil {
			return nil
		}
		return argumentSlots(ty)
	}
	t, ok := c.constTypeApart(head.name, head.typeAnnot, constLetterMark)
	if !ok {
		return nil
	}
	slots := argumentSlots(t)
	if n.elided {
		names := c.args(head.name)
		if len(names) > len(slots) {
			return nil
		}
		slots = slots[len(names):]
	}
	return slots
}

// liftCodomain is the type the build hands the partner's other
// operand: the partner's own local type where the text fixes it, it is
// not a `&` itself, and its arrows end in a type a declared coercion
// lifts into (liftResult) — a λ at that type reads the result at its
// body. The build reads the operand at it by the same rule
// (reconcileNumericDomain rebuilds a side the real line typed against
// such a partner, liftsAtResult; buildEqOperands rebuilds a refused
// side against it). nil otherwise.
func (c *implicitCompletion) liftCodomain(partner astNode, bound map[string]int) core.HolType {
	ty, coercion, known := c.localType(partner, bound)
	if !known || coercion || liftResult(c.syntax, ty) == nil {
		return nil
	}
	return ty
}

// liftResult is the type at the result of ty's arrows where some
// constant is the declared coercion into it, nil otherwise: the type a
// `&` standing at the result of a term of type ty reads at — the term
// itself, or the body of a λ of type ty, each λ peeling one arrow.
// Both halves of the partner rule read it: the chapter spelling folds a
// lift against a partner of such a type (liftCodomain), and the build
// rebuilds against it the operand the real line typed there
// (liftsAtResult).
func liftResult(table SyntaxTable, ty core.HolType) core.HolType {
	if table == nil || ty == nil {
		return nil
	}
	result := spineResult(ty)
	if table.CoercionConst(result) == "" {
		return nil
	}
	return result
}

// liftsPartner reports whether op's operands are built each by itself
// and a `&` among them then read against the other: the equation and
// its negation, the value arithmetic, the division and the order a
// type declares (`μ(s) ≤ &0` on [0, ∞]).
func liftsPartner(op string) bool {
	return op == "=" || op == utils.NeqStr || isValueArithOp(op) || op == "/" || op == "≤" || op == "<"
}
