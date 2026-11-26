package prop

import (
	"testing"

	"github.com/stretchr/testify/assert"
)

// TestIndependentExistsPrenexRewrite: at ∀ȳ.∃k̄.Φ the ∃-binders whose
// components of Φ mention no ȳ rise above the ∀ block; the ones a
// component ties to a ȳ, directly or through another ∃-binder, stay.
func TestIndependentExistsPrenexRewrite(t *testing.T) {
	y := Var("y", TypeA)
	y2 := Var("y'", TypeA)
	z := Var("z", TypeB)
	k := Var("k", TypeA)
	l := Var("l", TypeB)
	A := Var("A", MakeFun(TypeA, TypeBool))
	B := Var("B", MakeFun(TypeA, TypeBool))
	C := Var("C", MakeFun(TypeB, TypeBool))
	D := Var("D", MakeFun(TypeA, TypeB, TypeBool))
	E := Var("E", MakeFun(TypeA, TypeB, TypeBool))
	G := Var("G", MakeFun(TypeA, TypeA, TypeBool))

	rewrite := IndependentExistsPrenexRewrite

	// ∀y.∃k.(A(k) ∧ B(y)) = ∃k.(A(k) ∧ ∀y.B(y))
	assertRewrite(t, rewrite,
		ForAll(y)(Exists(k)(A.Apply(k).And(B.Apply(y)))),
		Exists(k)(A.Apply(k).And(ForAll(y)(B.Apply(y)))))

	// The ∨-chain: ∀y.∃k.(A(k) ∨ B(y)) = ∃k.(A(k) ∨ ∀y.B(y))
	assertRewrite(t, rewrite,
		ForAll(y)(Exists(k)(A.Apply(k).Or(B.Apply(y)))),
		Exists(k)(A.Apply(k).Or(ForAll(y)(B.Apply(y)))))

	// Blocks, and a chain of more than two components: the independent
	// binders keep their order, their components keep theirs.
	// ∀y.∀y'.∃k.∃l.(C(l) ∧ G(y, y') ∧ A(k)) = ∃k.∃l.((C(l) ∧ A(k)) ∧ ∀y.∀y'.G(y, y'))
	assertRewrite(t, rewrite,
		ForAll(y, y2)(Exists(k, l)(C.Apply(l).And(G.Apply(y, y2)).And(A.Apply(k)))),
		Exists(k, l)(C.Apply(l).And(A.Apply(k)).And(ForAll(y, y2)(G.Apply(y, y2)))))

	// A binder a component ties to the ∀ stays under it; the other rises:
	// ∀y.∃k.∃l.(A(k) ∧ D(y, l)) = ∃k.(A(k) ∧ ∀y.∃l.D(y, l))
	assertRewrite(t, rewrite,
		ForAll(y)(Exists(k, l)(A.Apply(k).And(D.Apply(y, l)))),
		Exists(k)(A.Apply(k).And(ForAll(y)(Exists(l)(D.Apply(y, l))))))

	// Tied through another ∃-binder, nothing rises:
	// ∀y.∃k.∃l.(E(k, l) ∧ D(y, l))
	assert.Nil(t, rewrite(ForAll(y)(Exists(k, l)(E.Apply(k, l).And(D.Apply(y, l))))))

	// Under a further ∀ block the ∧-chain still splits, and the inner
	// block distributes over the split:
	// ∀y.∃k.∀z.(E(k, z) ∧ D(y, z)) = ∃k.((∀z.E(k, z)) ∧ ∀y.∀z.D(y, z))
	assertRewrite(t, rewrite,
		ForAll(y)(Exists(k)(ForAll(z)(E.Apply(k, z).And(D.Apply(y, z))))),
		Exists(k)(ForAll(z)(E.Apply(k, z)).And(ForAll(y, z)(D.Apply(y, z)))))

	// An ∨-chain under a further ∀ block is not an equivalence: nothing.
	assert.Nil(t, rewrite(ForAll(y)(Exists(k)(ForAll(z)(E.Apply(k, z).Or(D.Apply(y, z)))))))

	// Every binder tied to the ∀, or the ∀ never mentioned: nothing.
	assert.Nil(t, rewrite(ForAll(y)(Exists(k)(G.Apply(y, k).And(A.Apply(k))))))
	assert.Nil(t, rewrite(ForAll(y)(Exists(k)(A.Apply(k).And(B.Apply(k))))))
	// No ∀ above, or no ∃ below: nothing.
	assert.Nil(t, rewrite(Exists(k)(A.Apply(k).And(B.Apply(y)))))
	assert.Nil(t, rewrite(ForAll(y)(A.Apply(y).And(B.Apply(y)))))
}

// TestSkolemRewriteWorkflow_IndependentWitnessIsAConstant: the Skolem
// stage on the negated conclusion of `(∃k. A(k)) ⇒ ∃k. B(k)` under a
// ∀, in the prelude's ∀-outside-∃ form, makes the witness of A a
// constant and not a function of the universal.
func TestSkolemRewriteWorkflow_IndependentWitnessIsAConstant(t *testing.T) {
	y := Var("y", TypeA)
	k := Var("k", TypeA)
	A := Var("A", MakeFun(TypeA, TypeBool))
	B := Var("B", MakeFun(TypeA, TypeBool))

	// ∀y.∃k.(A(k) ∧ ¬B(y))
	s := ForAll(y)(Exists(k)(A.Apply(k).And(Not(B.Apply(y)))))
	w := SkolemRewriteWorkflow(s)
	// = ∃k.(A(k) ∧ ∀y.¬B(y)): the ∃ is at the top, with no Skolem
	// function in sight.
	assertTermAlphaEqual(t, Rhs(w), Exists(k)(A.Apply(k).And(ForAll(y)(Not(B.Apply(y))))))
}
