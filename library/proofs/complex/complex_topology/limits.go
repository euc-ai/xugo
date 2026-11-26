// limits.go — limits of complex functions at a point: a point of a
// punctured disc and one disc serving two limits, the elementary limits,
// the algebra of limits, uniqueness, locality, composition with a
// function continuous at the limit, and the limit read along sequences.
//
// The arguments are the line's, with the modulus in place of the
// absolute value. The modulus is no part of the arithmetic of ℝ, so each
// estimate names what it reads of it: the triangle inequality, the
// modulus of a product and of a negative, and the equation of complex
// numbers that regroups a deviation, rewritten into the modulus before
// the bounds are combined.
//
// Opening the goal's `complex_limit_at` with `Unfold` opens it in every
// fact in hand as well, so a body reads its limit hypotheses by their
// definition first, or opens the goal alone with the definition's `Simp`
// where it cites a limit hypothesis as it stands (LimitAtAdd, LimitAtMul).
// A radius obtained with its positivity is one conjunction, whose ∀ half a
// body states on its own before applying it at a point.

package complex_topology

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/registry"
)

// PuncturedDiscPoint — the point a real half-radius out from c lies in the
// punctured disc of that radius.
//
// c + d/2 sits at distance d/2 from c: c cancels, leaving the real number
// d/2, whose modulus is its absolute value, positive and below d.
var PuncturedDiscPoint = puncturedDiscPointThm{family.Add(registry.ProofEntry{
	Name: "PuncturedDiscPoint",
	Key:  "prop_e38084f346e76d00",
	Build: family.Theorem(Statement{
		Binders: "∀c:complex. ∀d:real.",
		Hypotheses: []string{
			"&0 < d",
		},
		Conclusion: "&0 < |c + &(d / &2) - c| ∧ |c + &(d / &2) - c| < d",
	},
		func(a *Argument, c *Expr[Complex], d *Expr[Real], pos Fact) {
			offset := a.Have(
				"the point lies the real number d/2 away from c: c cancels",
				"c + &(d / &2) - c = &(d / &2)",
				ByArith())
			a.Show(
				"the modulus of a real number is its absolute value, and d/2 is positive and below d",
				ByArith(offset, complex_abs.AbsOfReal.At(a.TermAs[Real]("d / &2")), pos))
		}),
})}

// LimitAtCommonRadius — two limits at one point share, for every ε, one
// punctured disc on which both functions are within ε of their limits.
//
// Each limit answers ε with a radius of its own. The smaller of the two
// is positive, since both are, and a distance below it is below either,
// so a point of its punctured disc lies in both discs.
var LimitAtCommonRadius = limitAtCommonRadiusThm{family.Add(registry.ProofEntry{
	Name: "LimitAtCommonRadius",
	Key:  "prop_1b8f472b7098a635",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex. ∀ε:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ (∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < ε ∧ |g(z) - m| < ε)",
	},
		func(
			a *Argument,
			f, g *Arrow[Complex, Complex],
			c, l, m *Expr[Complex],
			ε *Expr[Real],
			toL, toM, pos Fact,
		) {
			nearL := a.Unfolded(toL, ComplexLimitAtDef)
			nearM := a.Unfolded(toM, ComplexLimitAtDef)
			d0, radiusL := a.ObtainAs[Real](
				"f ⟶ l (at c) at ε hands over a radius δ₀ inside which the values of f are within ε of l",
				"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < ε",
				By(nearL.At(ε), pos),
				Named("δ₀"))
			d1, radiusM := a.ObtainAs[Real](
				"and g ⟶ m (at c) at ε hands over a radius δ₁ inside which the values of g are within ε of m",
				"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |g(z) - m| < ε",
				By(nearM.At(ε), pos),
				Named("δ₁"))
			withinL := a.Have(
				"on the punctured disc of radius δ₀ the values of f are within ε of l",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < δ₀ ⇒ |f(z) - l| < ε",
				By(radiusL))
			withinM := a.Have(
				"on the punctured disc of radius δ₁ the values of g are within ε of m",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < δ₁ ⇒ |g(z) - m| < ε",
				By(radiusM))

			a.Take(a.TermAs[Real]("min(δ₀, δ₁)"))
			a.Do(SplitConj(
				Case(
					"the smaller radius is positive, both radii being positive",
					By(real_sup_inf.LessThanMin.At(d0, d1, a.TermAs[Real]("&0")), radiusL, radiusM)),
				Case(
					"and a point of its punctured disc lies in both discs, where both values are within ε",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						disc := b.Assume()
						inBoth := b.Have(
							"a distance below the smaller radius is below δ₀ and below δ₁",
							"|z - c| < δ₀ ∧ |z - c| < δ₁",
							By(real_sup_inf.LessThanMin.At(d0, d1, b.TermAs[Real]("|z - c|")), disc))
						b.Show(
							"so z lies in both discs: |f(z) − l| < ε and |g(z) − m| < ε",
							By(withinL.At(z), withinM.At(z), disc, inBoth))
					})),
			))
		}),
})}

// LimitAtConst — a constant function tends to its value.
//
// Any radius answers any ε: the value at every point is k itself, and
// k − k is zero, whose modulus is zero, below ε.
var LimitAtConst = limitAtConstThm{family.Add(registry.ProofEntry{
	Name: "LimitAtConst",
	Key:  "prop_9ff65153349ff5a1",
	Build: family.Theorem("∀c k:complex. (λz:complex. k) ⟶ k (at c)",
		func(a *Argument, c, k *Expr[Complex]) {
			a.Do(Unfold(ComplexLimitAtDef))
			a.FixAs[Real]("ε")
			pos := a.Assume()
			a.Take(a.TermAs[Real]("&1"))
			a.Do(SplitConj(
				Case(
					"the radius 1 is positive",
					ByArith()),
				Case(
					"and at every point of the disc the value is k, at distance |k − k| = 0 from k",
					Derive(func(b *Argument) {
						b.FixAs[Complex]()
						b.Assume()
						b.Show(
							"k − k is zero, and only zero has modulus zero, which is below ε",
							ByArith(complex_abs.AbsEqZero.At(b.TermAs[Complex]("k - k")), pos))
					})),
			))
		}),
})}

// LimitAtId — the identity tends to the point.
//
// The radius is ε itself: the identity's value at a point of the disc of
// radius ε around c is that point, within ε of c by the disc's own
// condition.
var LimitAtId = limitAtIdThm{family.Add(registry.ProofEntry{
	Name: "LimitAtId",
	Key:  "prop_b854c1b14fa43c8e",
	Build: family.Theorem("∀c:complex. (λz:complex. z) ⟶ c (at c)",
		func(a *Argument, c *Expr[Complex]) {
			a.Do(Unfold(ComplexLimitAtDef))
			eps := a.FixAs[Real]("ε")
			pos := a.Assume()
			a.Take(eps)
			a.Do(SplitConj(
				Case(
					"the radius is ε itself, which is positive",
					By(pos)),
				Case(
					"and at every point of the disc the value is the "+
						"point itself, within ε of c by the disc's condition",
					Derive(func(b *Argument) {
						b.FixAs[Complex]("z")
						disc := b.Assume()
						b.Show(
							"|z − c| < ε is the disc's second condition",
							By(disc))
					})),
			))
		}),
})}

// LimitAtNeg — the negative of a function tends to the negative of its
// limit.
//
// The same radius answers the same ε: −f(z) − (−l) is −(f(z) − l), and
// negation leaves the modulus alone.
var LimitAtNeg = limitAtNegThm{family.Add(registry.ProofEntry{
	Name: "LimitAtNeg",
	Key:  "prop_842ded208d2b33c1",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c l:complex.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
		},
		Conclusion: "(λz:complex. -f(z)) ⟶ -l (at c)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex], limit Fact) {
			near := a.Unfolded(limit, ComplexLimitAtDef)
			a.Do(Unfold(ComplexLimitAtDef))
			eps := a.FixAs[Real]("ε")
			pos := a.Assume()
			δ, radius := a.ObtainAs[Real](
				"f ⟶ l (at c) at ε hands over a radius δ inside which the values of f are within ε of l",
				"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < ε",
				By(near.At(eps), pos),
				Named("δ"))
			within := a.Have(
				"on the punctured disc of radius δ the values of f are within ε of l",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < ε",
				By(radius))
			a.Take(δ)
			a.Do(SplitConj(
				Case(
					"the radius δ is positive, as it was obtained",
					By(radius)),
				Case(
					"and at every point of the disc the value of −f is within ε of −l",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						disc := b.Assume()
						negated := b.Have(
							"the deviation of −f(z) from −l is the negative of the deviation of f(z) from l",
							"-f(z) - -l = -(f(z) - l)",
							ByArith())
						b.Show(
							"|−f(z) − (−l)| = |−(f(z) − l)| = |f(z) − l|, below ε as z lies in the disc",
							ByArith(negated, complex_abs.AbsNeg.At(b.TermAs[Complex]("f(z) - l")), within.At(z), disc))
					})),
			))
		}),
})}

// LimitAtAdd — the sum of two functions tends to the sum of their
// limits.
//
// Each limit is given half of ε: on the punctured disc the two limits
// share at ε/2, f is within ε/2 of l and g within ε/2 of m, the deviation
// of the sum is the sum of the deviations, and the triangle inequality
// puts it within ε/2 + ε/2 = ε of zero.
var LimitAtAdd = limitAtAddThm{family.Add(registry.ProofEntry{
	Name: "LimitAtAdd",
	Key:  "prop_4454a182a9e21589",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
		},
		Conclusion: "(λz:complex. f(z) + g(z)) ⟶ l + m (at c)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c, l, m *Expr[Complex], toL, toM Fact) {
			// The goal read as its ε-δ statement; the two limits stay as they
			// are, read by LimitAtCommonRadius below.
			a.Do(Simp(Fwd(ComplexLimitAtDef)))
			a.FixAs[Real]("ε")
			pos := a.Assume()
			half := a.TermAs[Real]("ε / &2")
			halfPos := a.Have(
				"half of ε is positive",
				"&0 < ε / &2",
				ByArith(pos))
			δ, radius := a.ObtainAs[Real](
				"the two limits share, at ε/2, a punctured disc of some radius "+
					"δ, inside which f is within ε/2 of l and g within ε/2 of m",
				"∃δ:real. "+
					"    &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < ε / &2 ∧ |g(z) - m| < ε / &2",
				By(LimitAtCommonRadius.At(f, g, c, l, m, half), toL, toM, halfPos),
				Named("δ"))
			within := a.Have(
				"on the punctured disc of radius δ, f is within ε/2 of l and g within ε/2 of m",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < ε / &2 ∧ |g(z) - m| < ε / &2",
				By(radius))
			a.Take(δ)
			a.Do(SplitConj(
				Case(
					"the radius δ is positive, as it was obtained",
					By(radius)),
				Case(
					"and at every point of the disc the value of f + g is within ε of l + m",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						disc := b.Assume()
						regroup := b.Have(
							"the deviation of the sum is the sum of the deviations",
							"f(z) + g(z) - (l + m) = (f(z) - l) + (g(z) - m)",
							ByArith())
						b.Show(
							"|(f(z) + g(z)) − (l + m)| ≤ |f(z) − l| + |g(z) − m| < ε/2 + ε/2 = ε, z lying in the disc",
							regroup.Rw(),
							ByArith(
								complex_abs.AbsTriangle.At(b.TermAs[Complex]("f(z) - l"), b.TermAs[Complex]("g(z) - m")),
								within.At(z),
								disc))
					})),
			))
		}),
})}

// LimitAtSub — the difference of two functions tends to the difference
// of their limits.
//
// f − g is f + (−g): the negative of g tends to −m, so the sum of f and
// −g tends to l + (−m), which is l − m.
var LimitAtSub = limitAtSubThm{family.Add(registry.ProofEntry{
	Name: "LimitAtSub",
	Key:  "prop_699a102db0a1095c",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
		},
		Conclusion: "(λz:complex. f(z) - g(z)) ⟶ l - m (at c)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c, l, m *Expr[Complex], toL, toM Fact) {
			negG := a.Have(
				"g tends to m, so its negative tends to −m",
				"(λz:complex. -g(z)) ⟶ -m (at c)",
				By(LimitAtNeg.At(g, c, m), toM))
			// Subtraction is addition of the negation, in the function and in
			// the limit alike.
			a.Do(Simp(Fwd(complex_field.ComplexSubDef)))
			a.Show(
				"f tends to l and −g to −m, so f + (−g) tends to l + (−m)",
				By(LimitAtAdd, toL, negG))
		}),
})}

// LimitAtMul — the product of two functions tends to the product of
// their limits.
//
// One tolerance serves both limits. Where f(z) is within η of l and g(z)
// within η of m, the deviation of the product splits into three terms,
// f(z)·g(z) − l·m = (f(z) − l)(g(z) − m) + l(g(z) − m) + m(f(z) − l), whose
// moduli are at most η·η, |l|·η and |m|·η; with η ≤ 1 the first is below
// η, so the whole is below η·(|l| + |m| + 1). The tolerance
// η = ε / (ε + |l| + |m| + 1) is positive, at most 1, and makes that bound
// less than ε.
var LimitAtMul = limitAtMulThm{family.Add(registry.ProofEntry{
	Name: "LimitAtMul",
	Key:  "prop_5fd249b35eb36f89",
	Build: family.Sections(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
		},
		Conclusion: "(λz:complex. f(z) * g(z)) ⟶ l * m (at c)",
		Abbrev: Abbrev{
			{Name: "η", Text: "ε / (ε + |l| + |m| + &1)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The deviation of a product from a product splits into three
			// terms, each a product with one deviation as a factor; the
			// triangle inequality bounds the modulus of the sum by the sum of
			// the moduli, and the modulus of each product is the product of
			// the moduli.
			threeTerms := ctx.Lemma("∀u v l m:complex. "+
				"    |u * v - l * m| ≤ |u - l| * |v - m| + |l| * |v - m| + |m| * |u - l|",
				func(s *Argument, u, v, l, m *Expr[Complex]) {
					devU, devV := s.TermAs[Complex]("u - l"), s.TermAs[Complex]("v - m")
					split := s.Have(
						"u·v − l·m = (u − l)(v − m) + l(v − m) + m(u − l)",
						"u * v - l * m = (u - l) * (v - m) + l * (v - m) + m * (u - l)",
						ByArith())
					s.Show(
						"the modulus of the three-term sum is at most the sum of "+
							"the moduli, each the product of the moduli of its factors",
						split.Rw(),
						ByArith(
							complex_abs.AbsTriangle.At(
								s.TermAs[Complex]("(u - l) * (v - m) + l * (v - m)"), s.TermAs[Complex]("m * (u - l)")),
							complex_abs.AbsTriangle.At(
								s.TermAs[Complex]("(u - l) * (v - m)"), s.TermAs[Complex]("l * (v - m)")),
							complex_abs.AbsMul.At(devU, devV),
							complex_abs.AbsMul.At(l, devV),
							complex_abs.AbsMul.At(m, devU)))
				})
			// The estimate at a tolerance η ≤ 1: the three terms are below η,
			// |l|·η and |m|·η.
			estimate := ctx.Lemma(Statement{
				Binders: "∀u v l m:complex. ∀η:real.",
				Hypotheses: []string{
					"&0 < η",
					"η ≤ &1",
					"|u - l| < η",
					"|v - m| < η",
				},
				Conclusion: "|u * v - l * m| < η * (|l| + |m| + &1)",
			},
				func(s *Argument, u, v, l, m *Expr[Complex], η *Expr[Real], pos, atMostOne, nearU, nearV Fact) {
					absDevU, absDevV := s.TermAs[Real]("|u - l|"), s.TermAs[Real]("|v - m|")

					square := s.Have(
						"η is at most 1, so η·η is at most η",
						"η * η ≤ η",
						ByArith(pos, atMostOne))
					first := s.Have(
						"|u − l|·|v − m| < η·η ≤ η",
						"|u - l| * |v - m| < η",
						ByArith(
							real_order_ring.LessThanMul2.At(absDevU, η, absDevV, η),
							complex_abs.AbsNonneg.At(s.TermAs[Complex]("u - l")),
							complex_abs.AbsNonneg.At(s.TermAs[Complex]("v - m")),
							square,
							nearU,
							nearV))
					second := s.Have(
						"|l|·|v − m| ≤ |l|·η",
						"|l| * |v - m| ≤ |l| * η",
						ByArith(complex_abs.AbsNonneg.At(l), nearV))
					third := s.Have(
						"|m|·|u − l| ≤ |m|·η",
						"|m| * |u - l| ≤ |m| * η",
						ByArith(complex_abs.AbsNonneg.At(m), nearU))
					s.Show(
						"the three terms add to less than η + |l|·η + |m|·η = η·(|l| + |m| + 1)",
						ByArith(At(threeTerms, u, v, l, m), first, second, third))
				})

			return ctx.Theorem(headline,
				func(a *Argument, f, g *Arrow[Complex, Complex], c, l, m *Expr[Complex], toL, toM Fact) {
					// The goal read as its ε-δ statement; the two limits stay as
					// they are, read by LimitAtCommonRadius below.
					a.Do(Simp(Fwd(ComplexLimitAtDef)))
					eps := a.FixAs[Real]("ε")
					pos := a.Assume()

					denominator := a.TermAs[Real]("ε + |l| + |m| + &1")
					η := a.TermAs[Real]("«η»")
					denomPos := a.Have(
						"ε + |l| + |m| + 1 is positive",
						"&0 < ε + |l| + |m| + &1",
						ByArith(pos, complex_abs.AbsNonneg.At(l), complex_abs.AbsNonneg.At(m)))
					ηPos := a.Have(
						"so the tolerance η, a quotient of two positives, is positive",
						"&0 < «η»",
						ByArith(pos, denomPos))
					ηOne := a.Have(
						"and at most 1, ε being at most ε + |l| + |m| + 1",
						"«η» ≤ &1",
						ByArith(denomPos, complex_abs.AbsNonneg.At(l), complex_abs.AbsNonneg.At(m)))
					ηBound := a.Have(
						"and η·(|l| + |m| + 1) < η·(ε + |l| + |m| + 1) = ε",
						"«η» * (|l| + |m| + &1) < ε",
						ByArith(field.DivLeftMul.Read(real_field.Field).At(eps, denominator), denomPos, pos, ηPos))

					δ, radius := a.ObtainAs[Real](
						"the two limits share, at η, a punctured disc of some radius "+
							"δ, inside which f is within η of l and g within η of m",
						"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < «η» ∧ |g(z) - m| < «η»",
						By(LimitAtCommonRadius.At(f, g, c, l, m, η), toL, toM, ηPos),
						Named("δ"))
					within := a.Have(
						"on the punctured disc of radius δ, f is within η of l and g within η of m",
						"∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < «η» ∧ |g(z) - m| < «η»",
						By(radius))
					a.Take(δ)
					a.Do(SplitConj(
						Case(
							"the radius δ is positive, as it was obtained",
							By(radius)),
						Case(
							"and at every point of the disc the value of f·g is within ε of l·m",
							Derive(func(b *Argument) {
								z := b.FixAs[Complex]("z")
								disc := b.Assume()
								product := b.Have(
									"z lies in the disc, so f(z) is within η of l and g(z) within η "+
										"of m, and the estimate gives |f(z)·g(z) − l·m| < η·(|l| + |m| + 1)",
									"|f(z) * g(z) - l * m| < «η» * (|l| + |m| + &1)",
									By(At(estimate, f.Apply(z), g.Apply(z), l, m, η), ηPos, ηOne, within.At(z), disc))
								b.Show(
									"and η·(|l| + |m| + 1) < ε",
									ByArith(product, ηBound))
							})),
					))
				})
		}),
})}

// LimitAtInv — the inverse of a function with a nonzero limit tends to
// the inverse of the limit.
//
// Two discs are met. On the first, the values of f stay away from zero:
// within |l|/2 of l, |f(z)| exceeds |l|/2. On the second, f is within the
// tolerance η = ε·|l|·|l|/2 of l. On the smaller of the two both bounds
// hold, and the estimate on the inverse (InvEstimate) puts 1/f(z) within
// ε of 1/l.
var LimitAtInv = limitAtInvThm{family.Add(registry.ProofEntry{
	Name: "LimitAtInv",
	Key:  "prop_e805fb856acb4185",
	Build: family.Sections(Statement{
		Binders: "∀f:(complex → complex). ∀c l:complex.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"l ≠ &0",
		},
		Conclusion: "(λz:complex. complex_inv(f(z))) ⟶ complex_inv(l) (at c)",
		Abbrev: Abbrev{
			{Name: "η", Text: "ε * |l| * |l| / &2"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A nonzero limit keeps the function away from zero: on a punctured
			// disc where f is within |l|/2 of l, |f(z)| exceeds |l|/2.
			awayFromZero := ctx.Lemma(Statement{
				Binders: "∀f:(complex → complex). ∀c l:complex.",
				Hypotheses: []string{
					"f ⟶ l (at c)",
					"l ≠ &0",
				},
				Conclusion: "∃δ:real. &0 < δ ∧ (∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |l| / &2 < |f(z)|)",
			},
				func(s *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex], limit, nonzero Fact) {
					near := s.Unfolded(limit, ComplexLimitAtDef)
					half := s.TermAs[Real]("|l| / &2")
					halfPos := s.Have(
						"l is not zero, so half of |l| is positive",
						"&0 < |l| / &2",
						ByArith(complex_abs.AbsPosIffNonzero.At(l), nonzero))
					δ, radius := s.ObtainAs[Real](
						"f ⟶ l (at c) at |l|/2 hands over a radius δ inside which the values of f are within |l|/2 of l",
						"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < |l| / &2",
						By(near.At(half), halfPos),
						Named("δ"))
					within := s.Have(
						"on the punctured disc of radius δ the values of f are within |l|/2 of l",
						"∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < |l| / &2",
						By(radius))
					s.Take(δ)
					s.Do(SplitConj(
						Case(
							"the radius δ is positive, as it was obtained",
							By(radius)),
						Case(
							"and at every point of the disc |f(z)| exceeds |l|/2",
							Derive(func(b *Argument) {
								z := b.FixAs[Complex]("z")
								disc := b.Assume()
								b.Show(
									"|l| − |f(z)| ≤ |f(z) − l| < |l|/2, the moduli differing by "+
										"at most the modulus of the difference, and z lying in the disc",
									ByArith(complex_abs.AbsTriangleReverse.At(f.Apply(z), l), within.At(z), disc))
							})),
					))
				})

			return ctx.Theorem(headline,
				func(a *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex], limit, nonzero Fact) {
					near := a.Unfolded(limit, ComplexLimitAtDef)
					d0, awayDisc := a.ObtainAs[Real](
						"a nonzero limit keeps f away from zero: on a punctured disc of radius δ₀, |f(z)| exceeds |l|/2",
						"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |l| / &2 < |f(z)|",
						By(At(awayFromZero, f, c, l), limit, nonzero),
						Named("δ₀"))
					awayParts := a.Conjuncts(
						awayDisc,
						"δ₀ is positive",
						"and on the punctured disc of radius δ₀, |f(z)| exceeds |l|/2")
					d0Pos, away := awayParts[0], awayParts[1]
					a.Do(Unfold(ComplexLimitAtDef))
					eps := a.FixAs[Real]("ε")
					pos := a.Assume()
					lPos := a.Have(
						"l is not zero, so |l| is positive",
						"&0 < |l|",
						By(complex_abs.AbsPosIffNonzero.At(l), nonzero))

					η := a.TermAs[Real]("«η»")
					ηPos := a.Have(
						"so the tolerance η = ε·|l|·|l|/2 is positive",
						"&0 < «η»",
						ByArith(pos, lPos))
					d1, radius := a.ObtainAs[Real](
						"f ⟶ l (at c) at η hands over a radius δ₁ inside which the values of f are within η of l",
						"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < «η»",
						By(near.At(η), ηPos),
						Named("δ₁"))
					within := a.Have(
						"on the punctured disc of radius δ₁ the values of f are within η of l",
						"∀z:complex. &0 < |z - c| ∧ |z - c| < δ₁ ⇒ |f(z) - l| < «η»",
						By(radius))

					a.Take(a.TermAs[Real]("min(δ₀, δ₁)"))
					a.Do(SplitConj(
						Case(
							"the smaller radius is positive, both radii being positive",
							By(real_sup_inf.LessThanMin.At(d0, d1, a.TermAs[Real]("&0")), d0Pos, radius)),
						Case(
							"and at every point of its punctured disc the inverse of f is within ε of the inverse of l",
							Derive(func(b *Argument) {
								z := b.FixAs[Complex]("z")
								disc := b.Assume()
								inBoth := b.Have(
									"a distance below the smaller radius is below δ₀ and below δ₁",
									"|z - c| < δ₀ ∧ |z - c| < δ₁",
									By(real_sup_inf.LessThanMin.At(d0, d1, b.TermAs[Real]("|z - c|")), disc))
								bounds := b.Have(
									"so z lies in both discs: |f(z)| exceeds |l|/2, and f(z) is within η of l",
									"|l| / &2 < |f(z)| ∧ |f(z) - l| < «η»",
									By(away.At(z), within.At(z), disc, inBoth))
								b.Show(
									"the estimate on the inverse at the value f(z): |1/f(z) − 1/l| < ε",
									By(InvEstimate.At(f.Apply(z), l, eps), pos, nonzero, bounds))
							})),
					))
				})
		}),
})}

// LimitAtUnique — a function has at most one limit at a point.
//
// Were l ≠ m, half their distance would be a positive ε. The two limits
// share a punctured disc on which f is within ε of l and within ε of m;
// at the point of that disc a half-radius out from c, the triangle
// inequality through the value of f there puts l and m less than
// ε + ε = |l − m| apart.
var LimitAtUnique = limitAtUniqueThm{family.Add(registry.ProofEntry{
	Name: "LimitAtUnique",
	Key:  "prop_4d129cdfbb3aa2ff",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"f ⟶ m (at c)",
		},
		Conclusion: "l = m",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c, l, m *Expr[Complex], toL, toM Fact) {
			apart := a.SupposeNot()
			pos := a.Have(
				"two different numbers are a positive distance apart, so half of it is a positive ε",
				"&0 < |l - m| / &2",
				ByArith(apart, complex_abs.AbsPosIffNonzero.At(a.TermAs[Complex]("l - m"))))
			δ, radius := a.ObtainAs[Real](
				"the two limits share a punctured disc of some radius "+
					"δ on which f is within ε of l and within ε of m",
				"∃δ:real. "+
					"    &0 < δ ∧ "+
					"    ∀z:complex. "+
					"        &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < |l - m| / &2 ∧ |f(z) - m| < |l - m| / &2",
				By(LimitAtCommonRadius, toL, toM, pos),
				Named("δ"))
			within := a.Have(
				"on that disc f is within ε of l and within ε of m",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < |l - m| / &2 ∧ |f(z) - m| < |l - m| / &2",
				By(radius))

			point := a.TermAs[Complex]("c + &(δ / &2)")
			inDisc := a.Have(
				"the point a half-radius out from c lies in the punctured disc",
				"&0 < |c + &(δ / &2) - c| ∧ |c + &(δ / &2) - c| < δ",
				By(At(PuncturedDiscPoint, c, δ), radius))
			near := a.Have(
				"so at that point f is within ε of l and within ε of m",
				"|f(c + &(δ / &2)) - l| < |l - m| / &2 ∧ |f(c + &(δ / &2)) - m| < |l - m| / &2",
				By(within.At(point), inDisc))
			value := f.Apply(point)
			a.Show(
				"then |l − m| ≤ |l − f| + |f − m| = |f − l| + |f − m| < ε + ε = |l − m|",
				ByArith(complex_abs.AbsSubTriangle.At(l, value, m), complex_abs.AbsSubComm.At(l, value), near))
		}),
})}

// LimitAtLocal — two functions that agree near a point have the same
// limits there.
//
// A limit reads only the values near the point, so the predicate "is a
// limit of f at c" cannot tell f from a function that agrees with it on a
// punctured disc about c. One lemma carries a limit across the agreement:
// where g ⟶ l (at c), on the punctured disc of the smaller of d and the
// radius the limit of g answers ε with, f(z) is g(z), within ε of l. Read
// from f to g and from g to f it gives both directions, and function
// extensionality equates the two predicates.
var LimitAtLocal = limitAtLocalThm{family.Add(registry.ProofEntry{
	Name: "LimitAtLocal",
	Key:  "prop_11e74abdea90dead",
	Build: family.Sections(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex. ∀d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀z:complex. &0 < |z - c| ∧ |z - c| < d ⇒ f(z) = g(z)",
		},
		Conclusion: "complex_limit_at(f, c) = complex_limit_at(g, c)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			transport := ctx.Lemma(Statement{
				Binders: "∀f g:(complex → complex). ∀c l:complex. ∀d:real.",
				Hypotheses: []string{
					"&0 < d",
					"∀z:complex. &0 < |z - c| ∧ |z - c| < d ⇒ f(z) = g(z)",
					"g ⟶ l (at c)",
				},
				Conclusion: "f ⟶ l (at c)",
			},
				func(
					a *Argument,
					f, g *Arrow[Complex, Complex],
					c, l *Expr[Complex],
					d *Expr[Real],
					dPos, agree, limit Fact,
				) {
					near := a.Unfolded(limit, ComplexLimitAtDef)
					a.Do(Unfold(ComplexLimitAtDef))
					eps := a.FixAs[Real]("ε")
					pos := a.Assume()
					δ, radius := a.ObtainAs[Real](
						"g ⟶ l (at c) at ε hands over a radius δ inside which the values of g are within ε of l",
						"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |g(z) - l| < ε",
						By(near.At(eps), pos),
						Named("δ"))
					within := a.Have(
						"on the punctured disc of radius δ the values of g are within ε of l",
						"∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |g(z) - l| < ε",
						By(radius))

					a.Take(a.TermAs[Real]("min(d, δ)"))
					a.Do(SplitConj(
						Case(
							"the smaller of d and δ is positive, both being positive",
							By(real_sup_inf.LessThanMin.At(d, δ, a.TermAs[Real]("&0")), dPos, radius)),
						Case(
							"and at every point of its punctured disc f(z) is g(z), within ε of l",
							Derive(func(b *Argument) {
								z := b.FixAs[Complex]("z")
								disc := b.Assume()
								inBoth := b.Have(
									"a distance below the smaller radius is below d and below δ",
									"|z - c| < d ∧ |z - c| < δ",
									By(real_sup_inf.LessThanMin.At(d, δ, b.TermAs[Real]("|z - c|")), disc))
								b.Show(
									"z lies in both discs, where f(z) = g(z) and g(z) is within ε of l",
									By(Normalized, agree.At(z), within.At(z), disc, inBoth))
							})),
					))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					f, g *Arrow[Complex, Complex],
					c *Expr[Complex],
					d *Expr[Real],
					dPos, agree Fact,
				) {
					// The two predicates are equal when they agree at every value l.
					a.Do(Funext())
					l := a.FixAs[Complex]("l")
					a.Iff()
					a.Forward(
						"a limit of f is a limit of g, which agrees with f near c",
						func(b *Argument, fLimit Fact) {
							// The transport is stated with the agreement as f(z) = g(z); read
							// at (g, f) it asks for g(z) = f(z), and a By does not match an
							// equation up to its orientation.
							agreeRev := b.Have(
								"the agreement read from g to f",
								"∀z:complex. &0 < |z - c| ∧ |z - c| < d ⇒ g(z) = f(z)",
								Derive(func(e *Argument) {
									e.FixAs[Complex]("z")
									disc := e.Assume()
									e.Do(Symm())
									e.Show(
										"f(z) = g(z) there",
										By(agree, disc))
								}))
							b.Show(
								"every limit of f is a limit of g",
								By(At(transport, g, f, c, l, d), dPos, agreeRev, fLimit))
						})
					a.Backward(
						"a limit of g is a limit of f, which agrees with g near c",
						func(b *Argument, gLimit Fact) {
							b.Show(
								"every limit of g is a limit of f",
								By(At(transport, f, g, c, l, d), dPos, agree, gLimit))
						})
				})
		}),
})}

// LimitAtCompose — a function continuous at the limit carries the limit
// along: where f ⟶ l (at c) and g is continuous at l, g ∘ f tends to g(l).
//
// For ε, continuity of g at l hands over a radius η inside which g is
// within ε of g(l). The limit of f, asked for η as its ε, hands over a
// punctured disc on which f is within η of l, and there g(f(z)) is within
// ε of g(l). Continuity, not a limit, is asked of g: f(z) may be l itself.
var LimitAtCompose = limitAtComposeThm{family.Add(registry.ProofEntry{
	Name: "LimitAtCompose",
	Key:  "prop_dfd22a3795428612",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l:complex.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"complex_continuous_at(g, l)",
		},
		Conclusion: "(g ∘ f) ⟶ g(l) (at c)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c, l *Expr[Complex], limit, gContinuous Fact) {
			near := a.Unfolded(limit, ComplexLimitAtDef)
			continuous := a.Unfolded(gContinuous, ComplexContinuousAtDef)
			// The goal read as its ε-δ statement, and `o` unfolded so that the
			// values of g ∘ f are the values g(f(z)).
			a.Do(Unfold(ComplexLimitAtDef), Unfold(functions.ComposeApply))
			eps := a.FixAs[Real]("ε")
			pos := a.Assume()
			η, radiusG := a.ObtainAs[Real](
				"continuity of g at l, at ε, hands over a radius η "+
					"inside which the values of g are within ε of g(l)",
				"∃η:real. &0 < η ∧ ∀w:complex. |w - l| < η ⇒ |g(w) - g(l)| < ε",
				By(continuous.At(eps), pos),
				Named("η"))
			nearL := a.Have(
				"within η of l, g is within ε of g(l)",
				"∀w:complex. |w - l| < η ⇒ |g(w) - g(l)| < ε",
				By(radiusG))
			δ, radiusF := a.ObtainAs[Real](
				"f ⟶ l (at c), asked for η as its ε, hands over a "+
					"radius δ inside which the values of f are within η of l",
				"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < η",
				By(near.At(η), radiusG),
				Named("δ"))
			within := a.Have(
				"on the punctured disc of radius δ the values of f are within η of l",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < η",
				By(radiusF))
			a.Take(δ)
			a.Do(SplitConj(
				Case(
					"the radius δ is positive, as it was obtained",
					By(radiusF)),
				Case(
					"and at every point of the disc g(f(z)) is within ε of g(l)",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						disc := b.Assume()
						b.Show(
							"f(z) lies within η of l, where g is within ε of g(l)",
							By(nearL.At(f.Apply(z)), within.At(z), disc))
					})),
			))
		}),
})}

// LimitAtSequential — f tends to l at c exactly when it carries every
// sequence that tends to c without touching it to a sequence tending to l.
//
// Forward: the radius the limit at c hands over for ε is the ε the
// sequence is asked for; past the index it answers with, a term lies
// within that radius of c and, never being c, in the punctured disc, where
// f is within ε of l. Backward, by contradiction: an ε the limit fails at
// leaves in every disc about c a point other than c where f is not within
// ε of l. Those bad points accumulate at c, so a sequence of them tends to
// c, and f carries it to a sequence tending to l — yet no value of f at a
// bad point comes within ε of l.
var LimitAtSequential = limitAtSequentialThm{family.Add(registry.ProofEntry{
	Name: "LimitAtSequential",
	Key:  "prop_bc48ca465de76cb9",
	Build: family.Theorem("∀f:(complex → complex). ∀c l:complex. "+
		"    f ⟶ l (at c) ⇔ ∀a:(num → complex). (∀n:num. a(n) ≠ c) ∧ a ⟶ c ⇒ (λn:num. f(a(n))) ⟶ l",
		func(arg *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex]) {
			arg.Iff()
			arg.Forward(
				"a limit at c carries every sequence tending to c without touching it to a sequence tending to l",
				func(b *Argument, toL Fact) {
					near := b.Unfolded(toL, ComplexLimitAtDef)
					b.FixAs[Fun[Nat, Complex]]("a")
					given := b.Assume()
					parts := b.Conjuncts(
						given,
						"no term of a is c",
						"and a tends to c")
					avoid := parts[0]
					approach := b.Unfolded(parts[1], ComplexConvergesToDef)
					b.Do(Unfold(ComplexConvergesToDef))
					eps := b.FixAs[Real]("ε")
					pos := b.Assume()
					δ, radius := b.ObtainAs[Real](
						"the limit at ε hands over a radius δ inside whose "+
							"punctured disc the values of f are within ε of l",
						"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < ε",
						By(near.At(eps), pos),
						Named("δ"))
					N, tail := b.ObtainAs[Nat](
						"a ⟶ c, asked for δ, hands over an index N past which the terms lie within δ of c",
						"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - c| < δ",
						By(approach.At(δ), radius),
						Named("N"))
					b.Take(N)
					n := b.FixAs[Nat]("n")
					past := b.Assume()
					inDisc := b.Have(
						"a(n) is not c, so it lies a positive distance from c, and past N within δ of it",
						"&0 < |a(n) - c| ∧ |a(n) - c| < δ",
						ByArith(
							complex_abs.AbsPosIffNonzero.At(b.TermAs[Complex]("a(n) - c")),
							avoid.At(n),
							tail.At(n),
							past))
					b.Show(
						"so f carries a(n) within ε of l",
						By(radius, inDisc))
				})
			arg.Backward(
				"a function carrying every such sequence to l tends to "+
					"l at c: the points where it fails would accumulate at c",
				func(b *Argument, sequential Fact) {
					notLimit := b.SupposeNot()
					eps, failing := b.ObtainAs[Real](
						"then some ε > 0 is answered by no radius: every punctured "+
							"disc about c holds a point where f is not within ε of l",
						"∃ε:real. &0 < ε ∧ ∀δ:real. &0 < δ ⇒ ∃z:complex. (&0 < |z - c| ∧ |z - c| < δ) ∧ ¬(|f(z) - l| < ε)",
						By(b.Unfolded(notLimit, ComplexLimitAtDef)),
						Named("ε"))
					bad, badDef := b.LetAs[Set[Complex]]("bad", "{z:complex | z ≠ c ∧ ¬(|f(z) - l| < ε)}")
					inBad := b.Have(
						"a point is bad when it is not c and f is not within ε of l there",
						"∀z:complex. z ∈ bad ⇔ z ≠ c ∧ ¬(|f(z) - l| < ε)",
						BySets(badDef))
					meets := b.Have(
						"every disc about c holds a bad point",
						"∀r:real. &0 < r ⇒ ball(𝕌, complex_dist, c, r) ∩ bad ≠ ∅",
						Derive(func(e *Argument) {
							r := e.FixAs[Real]("r")
							pos := e.Assume()
							z, point := e.ObtainAs[Complex](
								"the punctured disc of radius r holds a point z where f is not within ε of l",
								"∃z:complex. &0 < |z - c| ∧ |z - c| < r ∧ ¬(|f(z) - l| < ε)",
								By(failing, pos),
								Named("z"))
							other := e.Have(
								"z lies a positive distance from c, so it is not c",
								"z ≠ c",
								ByArith(point, complex_abs.AbsPosIffNonzero.At(e.TermAs[Complex]("z - c"))))
							both := e.Have(
								"z lies within r of c, so in the ball of the distance about c, and it is bad",
								"z ∈ ball(𝕌, complex_dist, c, r) ∩ bad",
								By(other, inBad.At(z), point, ComplexBall.At(c, r, z), set_basic.InInter))
							e.Show(
								"so the ball meets the bad points",
								BySets(both))
						}))
					x, sequence := b.ObtainAs[Fun[Nat, Complex]](
						"so a sequence x of bad points tends to c for the distance",
						"∃x:(num → complex). (∀n:num. x(n) ∈ bad) ∧ metric_converges_to(𝕌, complex_dist, x, c)",
						By(
							complete_metric.ApproachingSequence.Read(ComplexMetric).At(
								bad,
								b.MemberOf[on.Any](c, set_basic.InUniv.At(c))),
							meets),
						Named("x"))
					avoid := b.Have(
						"no term of x is c, its terms being bad",
						"∀n:num. x(n) ≠ c",
						Derive(func(e *Argument) {
							e.FixAs[Nat]("n")
							e.Show(
								"x(n) is bad",
								By(inBad.At(e.TermAs[Complex]("x(n)")), sequence))
						}))
					carried := b.Have(
						"x tends to c without touching it, so f carries it to a sequence tending to l",
						"(λn:num. f(x(n))) ⟶ l",
						By(sequential.At(x), avoid, sequence, ConvergesIffMetric.At(x, c)))
					N, tail := b.ObtainAs[Nat](
						"asked for ε, that limit hands over an index N past which the values are within ε of l",
						"∃N:num. ∀n:num. N ≤ n ⇒ |f(x(n)) - l| < ε",
						By(b.Unfolded(carried, ComplexConvergesToDef).At(eps), failing),
						Named("N"))
					b.Show(
						"at N itself f(x(N)) is within ε of l, and, x(N) being bad, it is not",
						By(tail.At(N), inBad.At(b.TermAs[Complex]("x(N)")), sequence, nat_order.LessEqRefl.At(N)))
				})
		}),
})}
