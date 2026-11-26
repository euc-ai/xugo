// laws.go — the bilinear form's algebra: what the fold mechanism and
// the ring's laws say together.
//
// Every member unfolds `dot` to the fold over the range and then reads
// the fold mechanism: congruence when the summands agree pointwise
// (symmetry); the pointwise law when a summand splits into two (left
// additivity); relation transfer when an operation on the summands
// carries to the folds (the scalar and the negation moving out); the
// vanishing law when every summand is the neutral element (the zero
// vector). The right-handed laws are the left-handed ones through
// symmetry, each turn one application of a law. What the mechanism asks
// of the ring's addition — that it folds, and from which element — the
// ring chapter states (comm_ring.MonoidalAdd, comm_ring.NeutralAdd).

package dot

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// Sym — the form is symmetric: at every index the two products are one
// product with its factors exchanged, and folds of pointwise-equal
// summands agree.
var Sym = symThm{family.Add(registry.ProofEntry{
	Name: "Sym",
	Key:  "prop_d6381b0654cc237e",
	Build: comm_ring.CommRing.Law(Statement{
		Binders:    "∀n:num. ∀u v:(num → A).",
		Conclusion: "⟪u, v⟫_n = ⟪v, u⟫_n",
	},
		func(a *Argument, ring Fact, n, u, v Term) {
			agree := a.Have(
				"at every index the two products are one product with its factors exchanged",
				"∀i:num. i ∈ «activeRange» ⇒ u(i) * v(i) = v(i) * u(i)",
				By(comm_monoid.Comm, comm_ring.MulMonoid, ring))
			a.Show(
				"so the two folds agree",
				Unfold(DotDef),
				By(agree, comm_ring.MonoidalAdd, ring, monoidal.Congruence))
		}),
})}

// AddLeft — the form is additive in its first argument: each summand
// splits by distributivity, and a fold of sums is the sum of the folds.
var AddLeft = addLeftThm{family.Add(registry.ProofEntry{
	Name: "AddLeft",
	Key:  "prop_6a8e3d745397a530",
	Build: comm_ring.CommRing.Law(Statement{
		Binders:    "∀n:num. ∀u v w:(num → A).",
		Conclusion: "⟪u + v, w⟫_n = ⟪u, w⟫_n + ⟪v, w⟫_n",
	},
		func(a *Argument, ring Fact, n, u, v, w Term) {
			folds := a.Have(
				"the ring's addition folds",
				"monoidal_op(R.add)",
				By(comm_ring.MonoidalAdd, ring))
			finite := a.Have(
				"the range is finite",
				"finite(«activeRange»)",
				Cite(num_segment.FiniteBelowStrict))
			split := a.Have(
				"at every index the summand splits by distributivity",
				"∀i:num. i ∈ «activeRange» ⇒ (u + v)(i) * w(i) = u(i) * w(i) + v(i) * w(i)",
				Unfold(vec_space.VecAddDef),
				By(comm_ring.RightDistrib, ring))
			splitFold := a.Term("Σ_{i<n} (u(i) * w(i) + v(i) * w(i))")
			a.Do(Unfold(DotDef), CalcEq(
				Leg(
					splitFold,
					"the fold of the split summands",
					By(split, folds, monoidal.Congruence)),
				FinalLeg(
					"is the sum of the two folds",
					By(finite, folds, monoidal.Pointwise)),
			))
		}),
})}

// SmulLeft — a scalar on the first argument comes out of the form:
// relation transfer at "is c times", which addition respects by
// distributivity and the neutral element by zero's absorption.
var SmulLeft = smulLeftThm{family.Add(registry.ProofEntry{
	Name: "SmulLeft",
	Key:  "prop_da06dc2349d7767c",
	Build: comm_ring.CommRing.Law(Statement{
		Binders:    "∀n:num. ∀c:A. ∀u v:(num → A).",
		Conclusion: "⟪c • u, v⟫_n = c * ⟪u, v⟫_n",
		Abbrev: Abbrev{
			{Name: "scaledProducts", Text: "Σ_{i<n} (c • u)(i) * v(i)"},
		},
	},
		func(a *Argument, ring Fact, n, c, u, v Term) {
			finite := a.Have(
				"the range is finite",
				"finite(«activeRange»)",
				Cite(num_segment.FiniteBelowStrict))
			a.Do(Unfold(DotDef))
			// The transfer law is applied at the relation "is c times",
			// the one binder the goal cannot spell; its obligations are
			// stated here in the law's own words.
			scalesBy := a.Term("λx:A. λy:A. c * x = y")
			respectsAddition := a.Have(
				"the relation survives addition, which is distributivity",
				"∀x₁ y₁ x₂ y₂:A. c * x₁ = x₂ ∧ c * y₁ = y₂ ⇒ c * (x₁ + y₁) = x₂ + y₂",
				By(Normalized, comm_ring.LeftDistrib, ring))
			fixesNeutral := a.Have(
				"and relates the element the fold starts from to itself",
				"c * neutral_elem(R.add) = neutral_elem(R.add)",
				By(Normalized, comm_ring.NeutralAdd, comm_ring.MulRightZero, ring))
			pointwise := a.Have(
				"and holds between each product and the scaled product",
				"∀i:num. i ∈ «activeRange» ⇒ c * (u(i) * v(i)) = (c • u)(i) * v(i)",
				Unfold(vec_space.VecScalarMulDef),
				By(comm_monoid.Assoc, comm_ring.MulMonoid, ring))
			reached := a.Have(
				"so the relation reaches the two folds: c times the fold is the fold of the scaled products",
				"c * («products») = «scaledProducts»",
				By(
					finite,
					respectsAddition,
					fixesNeutral,
					pointwise,
					comm_ring.MonoidalAdd,
					ring,
					Where(monoidal.Related, "R", scalesBy)))
			a.Show(
				"which is the claim, read from right to left",
				By(reached))
		}),
})}

// NegLeft — negating the first argument negates the form: relation
// transfer at "is the negation of", which addition respects and the
// neutral element fixes.
var NegLeft = negLeftThm{family.Add(registry.ProofEntry{
	Name: "NegLeft",
	Key:  "prop_4e71de51bd40f41c",
	Build: comm_ring.CommRing.Law(Statement{
		Binders:    "∀n:num. ∀u v:(num → A).",
		Conclusion: "⟪-u, v⟫_n = -⟪u, v⟫_n",
		Abbrev: Abbrev{
			{Name: "negatedProducts", Text: "Σ_{i<n} (-u)(i) * v(i)"},
		},
	},
		func(a *Argument, ring Fact, n, u, v Term) {
			abelian := a.Have(
				"the ring's additive structure is an abelian group",
				"abelian_group(additive_group(R))",
				By(comm_ring.AddGroup, ring))
			finite := a.Have(
				"the range is finite",
				"finite(«activeRange»)",
				Cite(num_segment.FiniteBelowStrict))
			a.Do(Unfold(DotDef))
			negates := a.Term("λx:A. λy:A. -x = y")
			respectsAddition := a.Have(
				"the relation survives addition: the negation of a sum is the sum of the negations",
				"∀x₁ y₁ x₂ y₂:A. -x₁ = x₂ ∧ -y₁ = y₂ ⇒ -(x₁ + y₁) = x₂ + y₂",
				By(Normalized, abelian_group.NegAdd, abelian))
			fixesNeutral := a.Have(
				"and relates the element the fold starts from to itself",
				"-neutral_elem(R.add) = neutral_elem(R.add)",
				By(Normalized, comm_ring.NeutralAdd, ring, group.InvOne.Read(abelian_group.Group.Read(abelian))))
			pointwise := a.Have(
				"and holds between each product and the product with the first factor negated",
				"∀i:num. i ∈ «activeRange» ⇒ -(u(i) * v(i)) = (-u)(i) * v(i)",
				Unfold(vec_space.VecNegDef),
				By(comm_ring.MulLeftNeg, ring))
			reached := a.Have(
				"so the relation reaches the two folds: the negation "+
					"of the fold is the fold of the negated products",
				"-(«products») = «negatedProducts»",
				By(
					finite,
					respectsAddition,
					fixesNeutral,
					pointwise,
					comm_ring.MonoidalAdd,
					ring,
					Where(monoidal.Related, "R", negates)))
			a.Show(
				"which is the claim, read from right to left",
				By(reached))
		}),
})}

// ZeroLeft — the zero vector is annihilated by the form: every summand
// is zero times an entry, which is the element the fold starts from.
var ZeroLeft = zeroLeftThm{family.Add(registry.ProofEntry{
	Name: "ZeroLeft",
	Key:  "prop_cd76e1904ee9dc56",
	Build: comm_ring.CommRing.Law(Statement{
		Binders:    "∀n:num. ∀v:(num → A).",
		Conclusion: "⟪vec_zero, v⟫_n = R.zero",
	},
		func(a *Argument, ring Fact, n, v Term) {
			neutralIsZero := a.Have(
				"the element the ring's addition folds from is the ring's zero",
				"neutral_elem(R.add) = R.zero",
				By(comm_ring.NeutralAdd, ring))
			silent := a.Have(
				"every summand is zero times an entry, which is the element the fold starts from",
				"∀i:num. i ∈ «activeRange» ⇒ vec_zero(i) * v(i) = neutral_elem(R.add)",
				Unfold(vec_space.VecZeroDef),
				By(neutralIsZero, comm_ring.MulLeftZero, ring))
			a.Show(
				"so the fold is that element, which is zero",
				Unfold(DotDef),
				neutralIsZero.RwRev(),
				By(silent, comm_ring.MonoidalAdd, ring, monoidal.EqNeutral))
		}),
})}

// SubLeft — the form is additive in a difference on the left: read the
// difference as a sum with a negation, split, negate, and read the
// ring's difference back.
var SubLeft = subLeftThm{family.Add(registry.ProofEntry{
	Name: "SubLeft",
	Key:  "prop_f9096b08a6085de6",
	Build: comm_ring.CommRing.Law("∀n:num. ∀u v w:(num → A). ⟪u - v, w⟫_n = ⟪u, w⟫_n - ⟪v, w⟫_n",
		func(a *Argument, ring Fact, n, u, v, w Term) {
			asAddNeg := a.Have(
				"the difference of vectors is a sum with a negation",
				"u - v = u + -v",
				By(vec_space.SubAddNeg, ring))
			a.Show(
				"the form splits over that sum, its negated part is the negated "+
					"form, and that is how the ring spells the difference of the two forms",
				asAddNeg.Rw(),
				By(AddLeft, ring, NegLeft, comm_ring.SubAddNeg))
		}),
})}

// ---------------------------------------------------------------------------
// The right-handed laws — each is its left-handed twin through symmetry
// ---------------------------------------------------------------------------

// AddRight — additive in the second argument.
var AddRight = addRightThm{family.Add(registry.ProofEntry{
	Name: "AddRight",
	Key:  "prop_2ba143d37e7c766f",
	Build: comm_ring.CommRing.Law("∀n:num. ∀u v w:(num → A). ⟪u, v + w⟫_n = ⟪u, v⟫_n + ⟪u, w⟫_n",
		func(a *Argument, ring Fact, n, u, v, w Term) {
			a.Show(
				"the form turned around splits on the left, and each part turns back",
				By(Sym, ring, AddLeft))
		}),
})}

// SmulRight — a scalar on the second argument comes out.
var SmulRight = smulRightThm{family.Add(registry.ProofEntry{
	Name: "SmulRight",
	Key:  "prop_1090f817a7390afb",
	Build: comm_ring.CommRing.Law("∀n:num. ∀c:A. ∀u v:(num → A). ⟪u, c • v⟫_n = c * ⟪u, v⟫_n",
		func(a *Argument, ring Fact, n, c, u, v Term) {
			a.Show(
				"the form turned around gives up its scalar on the left and turns back",
				By(Sym, ring, SmulLeft))
		}),
})}

// NegRight — negating the second argument negates the form.
var NegRight = negRightThm{family.Add(registry.ProofEntry{
	Name: "NegRight",
	Key:  "prop_c7a38c0fda1031ca",
	Build: comm_ring.CommRing.Law("∀n:num. ∀u v:(num → A). ⟪u, -v⟫_n = -⟪u, v⟫_n",
		func(a *Argument, ring Fact, n, u, v Term) {
			a.Show(
				"the form turned around gives up its negation on the left and turns back",
				By(Sym, ring, NegLeft))
		}),
})}

// SubRight — a difference on the right.
var SubRight = subRightThm{family.Add(registry.ProofEntry{
	Name: "SubRight",
	Key:  "prop_f54d336a0a40a314",
	Build: comm_ring.CommRing.Law("∀n:num. ∀u v w:(num → A). ⟪u, v - w⟫_n = ⟪u, v⟫_n - ⟪u, w⟫_n",
		func(a *Argument, ring Fact, n, u, v, w Term) {
			a.Show(
				"the form turned around splits over the difference on the left, and each part turns back",
				By(Sym, ring, SubLeft))
		}),
})}

// ZeroRight — the zero vector on the right.
var ZeroRight = zeroRightThm{family.Add(registry.ProofEntry{
	Name: "ZeroRight",
	Key:  "prop_a3a9215d8474e586",
	Build: comm_ring.CommRing.Law("∀n:num. ∀u:(num → A). ⟪u, vec_zero⟫_n = R.zero",
		func(a *Argument, ring Fact, n, u Term) {
			a.Show(
				"the form turned around is annihilated on the left",
				By(Sym, ZeroLeft, ring))
		}),
})}
