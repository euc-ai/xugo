// linearity.go — a sum reads its summand linearly, and what makes one
// vanish.
//
// Three parts, marked by banners:
//
// - What silences a sum
// - Linearity in the summand
// - The constant sum
//
// Closes marked `Normalized` land by simplification once the cited law
// is read at the goal's own point; the marker records that no
// refutation is wanted.

package real_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// What silences a sum
// ---------------------------------------------------------------------------
//
// Zero is both the value a sum returns when it has nothing to add and
// the value a term contributes when it is not heard. Both readings are
// the fold's neutral element at real addition, so everything below that
// has to argue a sum away argues it down to one of these two. And a
// term that is not heard is not summed either: the index set may be
// cut down to the points where the summand is heard at no cost, which
// is how every member that assumes nothing finite begins.

// Heard — a sum hears only the points where its summand is not zero:
// restricting the index set to them changes nothing. This is the fold's
// own law that it never sees past its support, read at ℝ, where the
// support is the carve-out at zero. It is the opening move of every
// member that assumes nothing finite, because the sum over the points
// heard is the one that can be a sum of anything.
var Heard = heardThm{family.Add(registry.ProofEntry{
	Name: "Heard",
	Key:  "prop_a27f52f09ed4f546",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → real). sum(s, f) = sum({x:A | x ∈ s ∧ f(x) ≠ &0}, f)",
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real]) {
			support := a.Have(
				"the points heard are the fold's support — where "+
					"the summand differs from the neutral, which is zero",
				"op_support(real_add, f, s) = {x:A | x ∈ s ∧ f(x) ≠ &0}",
				Unfold(monoidal.OpSupportDef),
				By(real_ring.NeutralAdd))
			a.Show(
				"and the fold never sees past its support",
				By(support, OnSupport.At(s, f)))
		}),
})}

// EqZero — a summand that is zero at every point of the index set sums
// to zero. Nothing is assumed finite, and nothing need be: past
// finiteness the fold answers with its neutral element, which is the
// same zero.
var EqZero = eqZeroThm{family.Add(registry.ProofEntry{
	Name: "EqZero",
	Key:  "prop_78db618f2039f24f",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ f(x) = &0",
			},
			Conclusion: "sum(s, f) = &0",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.EqNeutral, real_ring.MonoidalAdd, real_ring.NeutralAdd))
		}),
})}

// Zero — the sum of the summand that is zero outright. EqZero above at
// the one summand whose hypothesis needs no checking.
var Zero = zeroThm{family.Add(registry.ProofEntry{
	Name: "Zero",
	Key:  "prop_528d7ce3bb91d1c0",
	Build: family.Theorem("∀s:set(A). sum(s, λn:A. &0) = &0",
		func(a *Argument) {
			a.Do(By(EqZero))
		}),
})}

// ---------------------------------------------------------------------------
// Linearity in the summand
// ---------------------------------------------------------------------------
//
// A sum is a linear reading of its summand: summands add, scalars move
// through, and signs come out. Over a finite index set the first two are
// laws of the fold — addition is the operation being folded, and
// multiplying by a scalar is a map that keeps 0 and addition. What is ℝ's
// own is the rest: a scalar needs no finite index set, where the fold's
// laws do. And with a scalar coming out on either side, two finite sums
// multiply out into one sum over the pairs of their indices.

// Add — two summands over one index set may be added before or after
// summing. Finiteness is what the fold's pointwise law asks of the
// index set; past it neither side is a sum of anything.
var Add = addThm{family.Add(registry.ProofEntry{
	Name: "Add",
	Key:  "prop_4f055ce1a222abb7",
	Build: family.Theorem(
		Statement{
			Binders: "∀f g:(A → real). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "sum(s, f) + sum(s, g) = sum(s, λx:A. f(x) + g(x))",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Pointwise, real_ring.MonoidalAdd))
		}),
})}

// ScalarLeft — a scalar factor moves through a sum, with no finiteness
// assumed anywhere. That absence is the whole difficulty: where the
// summand is heard at infinitely many points there is no sum to
// distribute over, only the convention answering zero, and the argument
// has to show the convention scales as well. The case labels below carry
// the rest.
var ScalarLeft = scalarLeftThm{family.Add(registry.ProofEntry{
	Name: "ScalarLeft",
	Key:  "prop_5a5c8ea1894bf94d",
	Build: family.Sections(Statement{
		Binders:    "∀c:real. ∀f:(A → real). ∀s:set(A).",
		Conclusion: "c * sum(s, f) = sum(s, λx:A. c * f(x))",
		Abbrev: Abbrev{
			{Name: "heardScaledAt", Text: "{x:A | x ∈ s ∧ c * f(x) ≠ &0}"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {

			overFinite := ctx.Lemma(
				Statement{
					Binders: "∀c:real. ∀f:(A → real). ∀s:set(A).",
					Hypotheses: []string{
						"finite(s)",
					},
					Conclusion: "c * sum(s, f) = sum(s, λx:A. c * f(x))",
				},
				func(a *Argument, c *Expr[Real], f *Arrow[A, Real], s *Expr[Set[A]],
					finite Fact) {
					a.Do(Unfold(RealSumDef))
					scaling := a.TermAs[Fun[Real, Real]]("λu:real. c * u")
					keepsZero := a.Have(
						"multiplying by c keeps the element the fold starts from",
						"c * neutral_elem(real_add) = neutral_elem(real_add)",
						By(real_ring.NeutralAdd, real_ring.MulRightZero))
					keepsAddition := a.Have(
						"and distributes over addition",
						"∀u v:real. c * (u + v) = c * u + c * v",
						By(real_construction.LeftDistrib))
					a.Show(
						"so it passes through the fold",
						By(
							finite,
							keepsZero,
							keepsAddition,
							real_ring.MonoidalAdd,
							Where(monoidal.Homomorphic, "h", scaling)))
				})

			return ctx.Theorem(headline, func(a *Argument, c *Expr[Real],
				f *Arrow[A, Real], s *Expr[Set[A]]) {
				scaled := a.TermAs[Fun[A, Real]]("λx:A. c * f(x)")
				heard := a.TermAs[Set[A]]("«heardAt»")

				a.Cases(a.Term("finite(«heardAt»)"))
				a.When(
					"heard finitely often: both sides are already sums "+
						"over those points, and there the scalar comes out",
					func(b *Argument, finite Fact) {
						// The sum shrinks to the points heard by Heard. The scaled sum
						// does not: read at the scaled summand, Heard shrinks it to the
						// points where THAT is heard, a different set. So its shrink is
						// argued from the summand's silence off the points heard.
						inside := b.Have(
							"the points heard lie in the index set",
							"«heardAt» ⊆ s",
							BySets())
						silent := b.Have(
							"and everywhere else in it the summand is zero",
							"∀u:A. u ∈ s ∧ ¬(u ∈ «heardAt») ⇒ f(u) = &0",
							BySets())
						scaledPlain := b.Have(
							"so the scaled sum, zero wherever the summand is, shrinks to those points at no cost",
							"sum(«heardAt», λx:A. c * f(x)) = sum(s, λx:A. c * f(x))",
							By(inside, silent, real_ring.MulRightZero, Superset.At(heard, s, scaled)))
						b.Show(
							"the sum itself shrinks to them outright, and across a finite index set the scalar comes out",
							By(Heard.At(s, f), scaledPlain, finite, At(overFinite, c, f, heard)))
					})
				a.Otherwise(
					"heard infinitely often: neither side is a sum of anything, so both are the convention's zero",
					func(b *Argument, infinite Fact) {
						vanishes := b.Have(
							"nothing to add, so the fold answers zero",
							"sum(s, f) = &0",
							By(infinite, Degenerate.At(s, f)))
						scaledVanishes := b.Have(
							"and the scaled sum is zero too, for one of two reasons",
							"sum(s, λx:A. c * f(x)) = &0",
							Derive(func(d *Argument) {
								d.Cases(d.Term("c = &0"))
								d.When(
									"a scalar that vanishes silences every term at once",
									func(e *Argument, cIsZero Fact) {
										silenced := e.Have(
											"every scaled value is a product with zero",
											"∀u:A. u ∈ s ⇒ c * f(u) = &0",
											By(cIsZero, real_ring.MulLeftZero))
										e.Show(
											"which is what the vanishing law asks for",
											By(silenced, EqZero.At(s, scaled)))
									})
								d.Otherwise(
									"a scalar that does not vanish silences no term, so "+
										"the scaled summand is heard as often as the summand",
									func(e *Argument, cNotZero Fact) {
										sameSet := e.Have(
											"a product is zero only when one of its factors is",
											"«heardScaledAt» = «heardAt»",
											BySets(cNotZero, real_ring.MulEqZero))
										alsoInfinite := e.Have(
											"so the scaled summand is heard infinitely often as well",
											"¬finite(«heardScaledAt»)",
											By(infinite, sameSet))
										e.Show(
											"and the same convention answers zero",
											By(alsoInfinite, Degenerate.At(s, scaled)))
									})
							}))
						b.Show(
							"and a scalar times zero is zero",
							By(vanishes, scaledVanishes, real_ring.MulRightZero))
					})
			})
		}),
})}

// ScalarRight — the same on the other side, reached by commuting twice:
// once around the whole sum, to put the scalar where it is already known
// to come out, and once back inside the summand, where the same
// commutation is a statement about the summand as a function rather than
// about any one of its values.
var ScalarRight = scalarRightThm{family.Add(registry.ProofEntry{
	Name: "ScalarRight",
	Key:  "prop_ff3a82eb156b4074",
	Build: family.Theorem(
		"∀c:real. ∀f:(A → real). ∀s:set(A). sum(s, f) * c = sum(s, λx:A. f(x) * c)",
		func(a *Argument, c *Expr[Real], f *Arrow[A, Real], s *Expr[Set[A]]) {
			a.Do(CalcEq(
				Leg(
					a.Term("c * sum(s, f)"),
					"commute the two factors",
					Cite(real_construction.MulSym)),
				Leg(
					a.Term("sum(s, λx:A. c * f(x))"),
					"on the left the scalar already comes out",
					Cite(ScalarLeft)),
				FinalLeg(
					"and commute back, this time inside the summand",
					Cite(real_construction.MulSym)),
			))
		}),
})}

// ProductOfSums — the product of two finite sums is the sum, over the pairs
// of indices, of the products of their terms. Each factor enters the other's
// sum term by term, and the double sum of f(x)·g(y) is the sum over the
// cross product of the two index sets.
var ProductOfSums = productOfSumsThm{family.Add(registry.ProofEntry{
	Name: "ProductOfSums",
	Key:  "prop_67e48efc1545eff1",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → real). ∀g:(B → real).",
		Hypotheses: []string{
			"finite(s)",
			"finite(t)",
		},
		Conclusion: "(Σ_{x∈s} f(x)) * Σ_{y∈t} g(y) = Σ_{p∈set_cross(s, t)} f(fst(p)) * g(snd(p))",
	},
		func(
			a *Argument,
			s *Expr[Set[A]],
			t *Expr[Set[B]],
			f *Arrow[A, Real],
			g *Arrow[B, Real],
			finS, finT Fact,
		) {
			summand := a.TermAs[Fun2[A, B, Real]]("λx:A. λy:B. f(x) * g(y)")
			a.Show(
				"multiply out, then gather the double sum over the pairs",
				CalcEq(
					Leg(
						a.TermAs[Real]("Σ_{x∈s} Σ_{y∈t} f(x) * g(y)"),
						"the sum over t is a constant factor of each f(x), and f(x) a constant factor of each g(y)",
						Simp(Fwd(ScalarRight), Fwd(ScalarLeft))),
					FinalLeg(
						"a double sum over finite index sets is the sum over the pairs, read through the projections",
						Unfold(RealSumDef),
						By(
							finS,
							finT,
							real_ring.MonoidalAdd,
							monoidal.Fubini.At(
								a.TermAs[Op[Real]]("real_add"), s, a.TermAs[Fun2[A, B, Bool]]("λx:A. t"), summand),
							set_product.SetCrossDef.At(s, t),
							pairs.PairedLambda.At(summand))),
				))
		}),
})}

// Neg — a sign comes out of a sum. The unary minus is multiplication by
// -1, so nothing new is needed: read the sign as that scalar, let
// ScalarLeft carry it out, and read it back inside the summand.
var Neg = negThm{family.Add(registry.ProofEntry{
	Name: "Neg",
	Key:  "prop_8e64197f20be145f",
	Build: family.Theorem(
		"∀f:(A → real). ∀s:set(A). -sum(s, f) = sum(s, λx:A. -f(x))",
		func(a *Argument, f *Arrow[A, Real], s *Expr[Set[A]]) {
			a.Do(CalcEq(
				Leg(
					a.Term("-&1 * sum(s, f)"),
					"read the sign as the scalar it is",
					Cite(real_ring.NegMinusOne)),
				Leg(
					a.Term("sum(s, λx:A. -&1 * f(x))"),
					"and that scalar comes out like any other",
					Cite(ScalarLeft)),
				FinalLeg(
					"leaving the sign to be read back, inside the summand",
					Cite(real_ring.NegMinusOne)),
			))
		}),
})}

// Sub — subtraction is addition of the negation, and both of those have
// already crossed the sum. Finiteness comes from the additive half; the
// sign needs none.
var Sub = subThm{family.Add(registry.ProofEntry{
	Name: "Sub",
	Key:  "prop_34f77564fb30ea69",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f g:(A → real).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "sum(s, λx:A. f(x) - g(x)) = sum(s, f) - sum(s, g)",
		},
		func(a *Argument) {
			// Read the subtractions on both sides as what they abbreviate;
			// the two laws are stated of that form.
			a.Do(Unfold(real_ring.RealSubDef), By(Add, Neg))
		}),
})}

// ---------------------------------------------------------------------------
// The constant sum
// ---------------------------------------------------------------------------

// Const — a constant summand contributes its value once per point.
// Transport the natural sum of ones to ℝ, then scale it by the constant.
var Const = constThm{family.Add(registry.ProofEntry{
	Name: "Const",
	Key:  "prop_3569a49e248a8fe3",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀c:real.",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "&card(s) * c = sum(s, λn:A. c)",
		},
		func(a *Argument, s *Expr[Set[A]], c *Expr[Real], finite Fact) {
			a.Do(CalcEq(
				Leg(
					a.Term("sum(s, λx:A. &1) * c"),
					"the natural sum of ones counts s, and transport preserves its sum",
					By(
						Normalized,
						finite,
						nat_sum.SumOfOnes.At(s),
						RealOfNatSum.At(s, a.TermAs[Fun[A, Nat]]("λx:A. 1")))),
				FinalLeg(
					"scaling each one gives the constant summand",
					Simp(Fwd(ScalarRight), Fwd(real_construction.MulLeftId)),
					Refl())))
		}),
})}

// ConstBelow — the n terms below n of a constant sum to n times it: Const
// above at {k | k < n}, a finite set of n elements.
var ConstBelow = constBelowThm{family.Add(registry.ProofEntry{
	Name: "ConstBelow",
	Key:  "prop_1a617ffc64bb65fd",
	Build: family.Theorem("∀n:num. ∀c:real. &n * c = sum({k:num | k < n}, λk:num. c)",
		func(a *Argument, n *Expr[Nat], c *Expr[Real]) {
			below := a.TermAs[Set[Nat]]("{k:num | k < n}")
			a.Show(
				"{k | k < n} is a finite set of n elements",
				By(num_segment.HasSizeBelowStrict.At(n), cardinality.HasSizeDef.At(below, n), Const.At(below, c)))
		}),
})}

// CardAsSum — counting a finite set is summing 1 over it. Const above
// at the value 1, where the multiplication it is stated with has
// nothing left to do.
var CardAsSum = cardAsSumThm{family.Add(registry.ProofEntry{
	Name: "CardAsSum",
	Key:  "prop_a19679335ed8ed5c",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "sum(s, λx:A. &1) = &card(s)",
		},
		func(a *Argument) {
			// Normalized: once the identity factor is cancelled the two
			// sides are the same equation, so simplification finishes.
			a.Do(By(Normalized, Const, real_ring.MulRightId))
		}),
})}

// IndicatorSum counts the accepted points of a finite set by summing their indicators.
var IndicatorSum = indicatorSumThm{family.Add(registry.ProofEntry{
	Name: "IndicatorSum",
	Key:  "prop_9f5495d61ea54af7",
	Build: family.Theorem(Statement{
		Binders:    "∀T:set(A). ∀P:(A → bool).",
		Hypotheses: []string{"finite(T)"},
		Conclusion: "sum(T, λx:A. COND(P(x), &1, &0)) = &card({x:A | x ∈ T ∧ P(x)})",
	},
		func(a *Argument, T *Expr[Set[A]], P *Arrow[A, Bool], finite Fact) {
			part := a.TermAs[Set[A]]("{x:A | x ∈ T ∧ P(x)}")
			a.Show(
				"restrict the sum of ones to the points accepted by P",
				By(
					finite,
					finite_set.FiniteRestrict.At(T, P),
					CardAsSum.At(part),
					Restrict.At(T, P, a.TermAs[Fun[A, Real]]("λx:A. &1"))))
		}),
})}
