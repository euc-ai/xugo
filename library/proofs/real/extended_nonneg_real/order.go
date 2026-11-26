// order.go — the order on ⟦0, ∞⟧: a total order with 0 at the bottom and
// ∞ at the top, which the embedding of the nonnegative reals preserves
// and reflects. Being total, it is strict exactly where it fails the
// other way.
//
// Every law of the order unfolds it at its points and argues on the
// finite values, ∞ being decided by the definition's first clause; the
// strict order is read from those laws.

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"

	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// LeRefl — the order is reflexive.
var LeRefl = leReflThm{family.Add(registry.ProofEntry{
	Name: "LeRefl",
	Key:  "prop_5b51800df1e01740",
	Build: family.Theorem("∀x:extended_nonneg_real. x ≤ x",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			a.Show(
				"x is ∞, or its finite value is at most itself",
				ByArith(ExtendedLeDef.At(x, x)))
		}),
})}

// LeTrans — the order is transitive: a chain ending at ∞ ends above
// everything, and a finite chain is a chain of finite values.
var LeTrans = leTransThm{family.Add(registry.ProofEntry{
	Name: "LeTrans",
	Key:  "prop_2cbd5ec4d63c702b",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:extended_nonneg_real.",
		Hypotheses: []string{
			"x ≤ y",
			"y ≤ z",
		},
		Conclusion: "x ≤ z",
	}, func(a *Argument, x, y, z *Expr[ExtendedNonnegReal], chain Fact) {
		a.Show(
			"z is ∞, or all three are finite and their values chain",
			ByArith(chain, ExtendedLeDef.At(x, y), ExtendedLeDef.At(y, z), ExtendedLeDef.At(x, z)))
	}),
})}

// LeAntisym — the order is antisymmetric: only ∞ lies above ∞, and two
// finite values below each other are equal, so their images are.
var LeAntisym = leAntisymThm{family.Add(registry.ProofEntry{
	Name: "LeAntisym",
	Key:  "prop_556db25cc011c21d",
	Build: family.Theorem(Statement{
		Binders: "∀x y:extended_nonneg_real.",
		Hypotheses: []string{
			"x ≤ y",
			"y ≤ x",
		},
		Conclusion: "x = y",
	}, func(a *Argument, x, y *Expr[ExtendedNonnegReal], both Fact) {
		a.Show(
			"both are ∞, or both are the images of one finite value",
			By(
				both,
				ExtendedLeDef.At(x, y),
				ExtendedLeDef.At(y, x),
				OfRealToReal.At(x),
				OfRealToReal.At(y),
				real_construction.LessEqAntisym.At(
					a.TermAs[Real]("extended_to_real(x)"), a.TermAs[Real]("extended_to_real(y)"))))
	}),
})}

// LeTotal — any two extended values are comparable: if neither is ∞,
// their finite values are.
var LeTotal = leTotalThm{family.Add(registry.ProofEntry{
	Name: "LeTotal",
	Key:  "prop_3c32114245cd1df1",
	Build: family.Theorem("∀x y:extended_nonneg_real. x ≤ y ∨ y ≤ x",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Show(
				"the finite values of x and y are comparable",
				By(
					ExtendedLeDef.At(x, y),
					ExtendedLeDef.At(y, x),
					real_construction.LessEqTotal.At(
						a.TermAs[Real]("extended_to_real(x)"), a.TermAs[Real]("extended_to_real(y)"))))
		}),
})}

// ZeroLe — 0 is the least extended value: its finite value is 0, and
// every finite value is nonnegative.
var ZeroLe = zeroLeThm{family.Add(registry.ProofEntry{
	Name: "ZeroLe",
	Key:  "prop_1e2157e2d265f20",
	Build: family.Theorem("∀x:extended_nonneg_real. &0 ≤ x",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			a.Show(
				"0 is finite with value 0, at most the value of any finite x",
				ByArith(
					ExtendedLeDef.At(a.TermAs[ExtendedNonnegReal]("&0"), x),
					ZeroNotInfinity,
					ToRealZero,
					ToRealNonneg.At(x)))
		}),
})}

// LeInfinity — ∞ is the greatest extended value.
var LeInfinity = leInfinityThm{family.Add(registry.ProofEntry{
	Name: "LeInfinity",
	Key:  "prop_e4eb1e050f49eb54",
	Build: family.Theorem("∀x:extended_nonneg_real. x ≤ extended_infinity",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			a.Show(
				"the order puts everything below ∞",
				By(ExtendedLeDef.At(x, a.TermAs[ExtendedNonnegReal]("extended_infinity"))))
		}),
})}

// OfRealMono — the embedding is monotone: where s is nonnegative it compares
// r and s as the reals do, and where s is negative so is r, both embedding
// as 0.
var OfRealMono = ofRealMonoThm{family.Add(registry.ProofEntry{
	Name: "OfRealMono",
	Key:  "prop_5848ccfe27a75a30",
	Build: family.Theorem(Statement{
		Binders:    "∀r s:real.",
		Hypotheses: []string{"r ≤ s"},
		Conclusion: "extended_of_real(r) ≤ extended_of_real(s)",
	},
		func(a *Argument, r, s *Expr[Real], below Fact) {
			a.Show(
				"as the reals do where s is nonnegative, and both 0 where it is negative",
				ByArith(below, OfRealLe.At(r, s), OfRealNeg.At(r), OfRealNeg.At(s), LeRefl))
		}),
})}

// OfRealLe — the embedding compares a real with a nonnegative real as the
// reals do: a nonnegative r is read back by its image, and a negative r
// embeds as 0, which lies below every image as r lies below s.
var OfRealLe = ofRealLeThm{family.Add(registry.ProofEntry{
	Name: "OfRealLe",
	Key:  "prop_6a699fcc8d2d9aef",
	Build: family.Theorem(Statement{
		Binders:    "∀r s:real.",
		Hypotheses: []string{"&0 ≤ s"},
		Conclusion: "extended_of_real(r) ≤ extended_of_real(s) ⇔ r ≤ s",
	},
		func(a *Argument, r, s *Expr[Real], nonneg Fact) {
			a.Cases(a.Term("&0 ≤ r"))
			a.When(
				"r is nonnegative: both images are finite with values r and s",
				func(b *Argument, rNonneg Fact) {
					b.Show(
						"the order of the images is the order of r and s",
						ByArith(
							rNonneg,
							nonneg,
							ExtendedLeDef.At(
								b.TermAs[ExtendedNonnegReal]("extended_of_real(r)"),
								b.TermAs[ExtendedNonnegReal]("extended_of_real(s)")),
							OfRealNotInfinity.At(r),
							OfRealNotInfinity.At(s),
							ToRealOfReal.At(r),
							ToRealOfReal.At(s)))
				})
			a.Otherwise(
				"r is negative: its image is 0, below the image of s, and r < 0 ≤ s",
				func(b *Argument, rNegative Fact) {
					b.Show(
						"both sides hold",
						ByArith(
							rNegative,
							nonneg,
							OfRealNeg.At(r),
							ZeroLe.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(s)"))))
				})
		}),
})}

// LtIffNotLe — the order is total, so x lies strictly below y exactly
// when y does not lie below x.
var LtIffNotLe = ltIffNotLeThm{family.Add(registry.ProofEntry{
	Name: "LtIffNotLe",
	Key:  "prop_a4ad7c888cc3aecf",
	Build: family.Theorem("∀x y:extended_nonneg_real. x < y ⇔ ¬(y ≤ x)",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Show(
				"x and y are comparable, and equal when each lies below the other",
				By(ExtendedLtDef.At(x, y), LeTotal.At(x, y), LeAntisym.At(x, y), LeRefl.At(x)))
		}),
})}

// OfRealLt — the image of r lies strictly below the image of y exactly
// when r < y and y is positive: a nonnegative r is read back by OfRealLe,
// and a negative r embeds as 0, which lies strictly below the images of
// the positive reals alone.
var OfRealLt = ofRealLtThm{family.Add(registry.ProofEntry{
	Name: "OfRealLt",
	Key:  "prop_5afb76e9de38489e",
	Build: family.Theorem("∀r y:real. extended_of_real(r) < extended_of_real(y) ⇔ r < y ∧ &0 < y",
		func(a *Argument, r, y *Expr[Real]) {
			zero := a.TermAs[Real]("&0")
			image := a.TermAs[ExtendedNonnegReal]("extended_of_real(y)")
			a.Cases(a.Term("&0 ≤ r"))
			a.When(
				"r is nonnegative: the strict order is OfRealLe failing the other way",
				func(b *Argument, rNonneg Fact) {
					reals := b.Have(
						"for r ≥ 0, y fails to lie below r exactly when r < y and y is positive",
						"¬(y ≤ r) ⇔ r < y ∧ &0 < y",
						ByArith(rNonneg))
					b.Show(
						"so the images compare as r and y do",
						By(
							rNonneg,
							reals,
							LtIffNotLe.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(r)"), image),
							OfRealLe.At(y, r)))
				})
			a.Otherwise(
				"r is negative: its image is 0",
				func(b *Argument, rNegative Fact) {
					reals := b.Have(
						"for r < 0, y fails to lie below 0 exactly when r < y and y is positive",
						"r ≤ &0 ∧ (¬(y ≤ &0) ⇔ r < y ∧ &0 < y)",
						ByArith(rNegative))
					b.Show(
						"so the image of r, which is 0, lies below the image of y exactly when y is positive",
						By(
							reals,
							real_order_ring.LessEqRefl.At(zero),
							OfRealNeg.At(r),
							LtIffNotLe.At(b.TermAs[ExtendedNonnegReal]("extended_of_real(r)"), image),
							OfRealLe.At(y, zero)))
				})
		}),
})}

// EqInfinityIffAboveNaturals — a value of ⟦0, ∞⟧ is ∞ exactly when it
// exceeds every natural number: ∞ lies above every embedded real, and a
// finite value is an embedded real, which some natural number exceeds.
var EqInfinityIffAboveNaturals = eqInfinityIffAboveNaturalsThm{family.Add(registry.ProofEntry{
	Name: "EqInfinityIffAboveNaturals",
	Key:  "prop_8ba953b8bb041afe",
	Build: family.Theorem("∀y:extended_nonneg_real. "+
		"    y = extended_infinity ⇔ ∀n:num. extended_of_real(&n) < y",
		func(a *Argument, y *Expr[ExtendedNonnegReal]) {
			a.Iff()
			a.Forward(
				"infinity exceeds every embedded natural number",
				func(c *Argument, infinite Fact) {
					c.FixAs[Nat]("n")
					nReal := c.TermAs[Real]("&n")
					c.Show(
						"every real embedding is below infinity and differs from it",
						By(
							infinite,
							OfRealNotInfinity.At(nReal),
							LeInfinity.At(c.TermAs[ExtendedNonnegReal]("extended_of_real(&n)")),
							LtIffNotLe,
							LeAntisym))
				})
			a.Backward(
				"a finite value is bounded above by a natural number",
				func(c *Argument, above Fact) {
					finite := c.SupposeNot()
					v, value := c.ObtainAs[Real](
						"the finite extended value is an embedded real",
						"∃v:real. &0 ≤ v ∧ y = extended_of_real(v)",
						By(finite, ExtendedCases.At(y)))
					n, beyond := c.ObtainAs[Nat](
						"some natural number lies above that real",
						"∃n:num. v < &n",
						By(real_archimedean.ExistsNumStrictlyAbove.At(v)))
					below := c.Have(
						"the same number would also lie below it",
						"&n < v",
						By(Normalized, above.At(n), value, OfRealLt))
					c.Show(
						"the strict inequalities contradict each other",
						ByArith(beyond, below))
				})
		}),
})}
