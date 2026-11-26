package prop

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

// A denoted multi-binder λ must fold EVERY instance of its body, in
// particular one sitting under enclosing binders whose order differs
// from the λ's own. The single-order wrap folds λx.λy only where the
// site's binder path happens to run x-then-y; under ∀y.∀x the wrap
// abstracts λy.λx, the rigid bodies fail α, and the site silently
// stays unfolded — the clause set then mixes the atom with raw
// expansions the refuter cannot bridge (int_divides.Bezout's
// WF-induction close was the live failure). DenoteRewrite therefore
// runs the wrap in permuted mode (unifyEqRewriteAbsPermuted).
func TestDenoteRewrite_FoldsUnderSwappedBinders(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	u := Var("u", TypeA)
	xp := Var("xp", TypeA)
	yp := Var("yp", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	d := Var("d", TypeA)
	xw := Var("xw", TypeA)
	yw := Var("yw", TypeA)
	Dv := Var("D", MakeFun(TypeA, TypeA, TypeBool))
	pl := Var("pl", MakeFun(TypeA, TypeA, TypeA))
	tm := Var("tm", MakeFun(TypeA, TypeA, TypeA))
	Lt := Var("Lt", MakeFun(TypeA, TypeA, TypeBool))
	B := Var("B", MakeFun(TypeA, TypeA, TypeBool))

	// The Bezout shape: a rigid two-binder body with the vars deep
	// inside nested quantifiers.
	body := func(p, q *ext.TermWrapper) *ext.TermWrapper {
		return ext.Exists(d)(Dv.Apply(d, p).And(Dv.Apply(d, q)).And(
			ext.Exists(xw, yw)(d.Eq(pl.Apply(tm.Apply(p, xw), tm.Apply(q, yw))))))
	}
	lam := a.To(b.To(body(a, b)))
	rw := DenoteRewrite(B.Core().(VarTerm), lam)

	fold := func(s Term) Term {
		w := rw(s)
		if w == nil {
			return nil
		}
		return Rhs(w)
	}

	// Binder order matching the λ — folded by the plain wrap.
	assertFolded(t,
		ext.ForAll(a, b)(B.Apply(a, b)),
		fold(ext.ForAll(a, b)(body(a, b))))

	// Swapped enclosing binders — the permuted wrap's case.
	assertFolded(t,
		ext.ForAll(y, x)(B.Apply(x, y)),
		fold(ext.ForAll(y, x)(body(x, y))))

	// The live failure's full shape: swapped binders, intervening
	// binders of other variables, the site one disjunct among folded
	// atoms.
	got := fold(ext.ForAll(y, x)(ext.Exists(z, u)(ext.ForAll(xp, yp)(
		body(x, y).Or(
			ext.Not(B.Apply(z, u)).And(
				ext.Not(Lt.Apply(xp, yp)).Or(B.Apply(xp, yp))))))))
	assertFolded(t,
		ext.ForAll(y, x)(ext.Exists(z, u)(ext.ForAll(xp, yp)(
			B.Apply(x, y).Or(
				ext.Not(B.Apply(z, u)).And(
					ext.Not(Lt.Apply(xp, yp)).Or(B.Apply(xp, yp))))))),
		got)
}

func assertFolded(t *testing.T, want, got Term) {
	t.Helper()
	if got == nil {
		t.Fatalf("fold returned nil; want %s", ext.PrintTerm(want))
	}
	assert.True(t, want.AlphaEquals(got),
		"want %s\ngot  %s", ext.PrintTerm(want), ext.PrintTerm(got))
}
