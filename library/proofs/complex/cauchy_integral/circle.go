// circle.go — once round a circle, 1/(z − w) integrates to 2πi for every w
// inside it. With q(z) = (w − c)/(z − c), which has modulus |w − c|/r < 1 on
// the circle, the field identity 1/(z − w) = 1/(z − c) + q(z)/(z − w) cuts
// the geometric series in q after any number of terms; the first term
// integrates to 2πi, every later one has a primitive along the circle and
// so integrates to 0, and the remainder after N terms is at most a fixed
// multiple of (|w − c|/r)ᴺ.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// CutSeriesContinuous — the terms qᴺ/(z − c) and the remainders qᴺ/(z − w)
// of the series cut off after N terms are continuous wherever they are
// defined: off c and v, the translates z − c and z − v are holomorphic and
// not 0, so q = (w − c)/(z − c), its powers and their quotients by z − v
// are holomorphic there, and a function with a derivative at a point is
// continuous at it.
var CutSeriesContinuous = cutSeriesContinuousThm{family.Add(registry.ProofEntry{
	Name: "CutSeriesContinuous",
	Key:  "prop_787f22ecbca8bff9",
	Build: family.Theorem(Statement{
		Binders: "∀c w v z:complex. ∀N:num.",
		Hypotheses: []string{
			"z ≠ c",
			"z ≠ v",
		},
		Conclusion: "complex_continuous_at(λu:complex. «q»(u) ^ N / (u - v), z)",
		Abbrev: Abbrev{
			{Name: "q", Text: "λz:complex. (w - c) / (z - c)"},
		},
	},
		func(a *Argument, c, w, v, z *Expr[Complex], N *Expr[Nat], offC, offV Fact) {
			translates := a.Have(
				"each translate u − b has derivative 1 everywhere, so is holomorphic off c and v",
				"∀b:complex. holomorphic_on({u:complex | u ≠ c ∧ u ≠ v}, λu:complex. u - b)",
				By(
					complex_derivative.HolomorphicOnDef,
					complex_derivative.DerivativeSub,
					complex_derivative.DerivativeId,
					complex_derivative.DerivativeConst))
			awayC := a.Have(
				"off c and v, u − c is not 0",
				"∀u:complex. u ∈ {u:complex | u ≠ c ∧ u ≠ v} ⇒ u - c ≠ &0",
				ByArith())
			awayV := a.Have(
				"nor is u − v",
				"∀u:complex. u ∈ {u:complex | u ≠ c ∧ u ≠ v} ⇒ u - v ≠ &0",
				ByArith())
			power := a.Have(
				"so q(u) = (w − c)/(u − c) is holomorphic off c and v, and so is its N-th power",
				"holomorphic_on({u:complex | u ≠ c ∧ u ≠ v}, λu:complex. «q»(u) ^ N)",
				By(
					translates,
					awayC,
					complex_derivative.HolomorphicOnPow,
					complex_derivative.HolomorphicOnDiv,
					complex_derivative.HolomorphicOnConst))
			quotient := a.Have(
				"and so is its quotient by u − v",
				"holomorphic_on({u:complex | u ≠ c ∧ u ≠ v}, λu:complex. «q»(u) ^ N / (u - v))",
				By(translates, awayV, power, complex_derivative.HolomorphicOnDiv))
			a.Show(
				"z lies off c and v, where the quotient has a derivative, so it is continuous at z",
				By(
					quotient,
					offC,
					offV,
					complex_derivative.HolomorphicOnDef,
					complex_derivative.DerivativeContinuous))
		}),
})}

// CircleHigherTermVanishes — round a circle about c every term of the
// series after the first integrates to 0: qⁿ⁺¹/(z − c), with
// q(z) = (w − c)/(z − c), is the derivative of −qⁿ⁺¹/(n + 1) off c, by the
// quotient rule for q and the chain rule for its power, and the circle,
// which avoids c and is closed, takes the primitive back to its value at
// the start.
var CircleHigherTermVanishes = circleHigherTermVanishesThm{family.Add(registry.ProofEntry{
	Name: "CircleHigherTermVanishes",
	Key:  "prop_a2a4e09c4bf07f2d",
	Build: family.Theorem(Statement{
		Binders: "∀c w:complex. ∀r:real. ∀n:num.",
		Hypotheses: []string{
			"&0 < r",
		},
		Conclusion: "«circleInt»(λz:complex. «q»(z) ^ (n + 1) / (z - c), c, r) = &0",
		Abbrev: Abbrev{
			{Name: "q", Text: "λz:complex. (w - c) / (z - c)"},
		},
	},
		func(a *Argument, c, w *Expr[Complex], r *Expr[Real], n *Expr[Nat], positive Fact) {
			primitive := a.TermAs[Fun[Complex, Complex]](
				"λu:complex. -complex_inv(complex_of_real(&(n + 1))) * «q»(u) ^ (n + 1)")
			term := a.TermAs[Fun[Complex, Complex]]("λz:complex. «q»(z) ^ (n + 1) / (z - c)")
			derivative := a.Have(
				"off c, −qⁿ⁺¹/(n + 1) has derivative qⁿ⁺¹/(z − c)",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"z ≠ c",
					},
					Conclusion: "complex_derivative_at( " +
						"    λu:complex. -complex_inv(complex_of_real(&(n + 1))) * «q»(u) ^ (n + 1), " +
						"    z, " +
						"    «q»(z) ^ (n + 1) / (z - c))",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					off := b.Assume()
					away := b.Have(
						"z − c is not 0",
						"z - c ≠ &0",
						ByArith(off))
					zero, one := b.TermAs[Complex]("complex_of_real(&0)"), b.TermAs[Complex]("complex_of_real(&1)")
					translate := b.TermAs[Fun[Complex, Complex]]("λu:complex. u - c")
					ratio := b.TermAs[Fun[Complex, Complex]]("«q»")
					qSlope := b.TermAs[Complex](
						"(complex_of_real(&0) * (z - c) - (w - c) * complex_of_real(&1)) / (z - c) ^ 2")
					powSlope := b.TermAs[Complex]("complex_of_real(&(n + 1)) * «q»(z) ^ n")
					shifted := b.Have(
						"u − c has derivative 1 at z, the identity's 1 less the constant's 0",
						"complex_derivative_at(λu:complex. u - c, z, &1)",
						By(
							b.Have(
								"1 − 0 is 1",
								"complex_of_real(&1) - &0 = &1",
								ByArith()),
							complex_derivative.DerivativeSub.At(
								b.TermAs[Fun[Complex, Complex]]("λu:complex. u"),
								b.TermAs[Fun[Complex, Complex]]("λu:complex. c"),
								z,
								one,
								zero),
							complex_derivative.DerivativeId.At(z),
							complex_derivative.DerivativeConst.At(z, c)))
					quotient := b.Have(
						"so q, a constant over u − c, has its derivative by the quotient rule",
						"complex_derivative_at(«q», "+
							"    z, "+
							"    (complex_of_real(&0) * (z - c) - (w - c) * complex_of_real(&1)) / (z - c) ^ 2)",
						By(
							away,
							shifted,
							complex_derivative.DerivativeConst.At(z, b.TermAs[Complex]("w - c")),
							complex_derivative.DerivativeDiv.At(
								b.TermAs[Fun[Complex, Complex]]("λu:complex. w - c"),
								translate,
								z,
								zero,
								one)))
					power := b.Unfolded(
						b.Have(
							"and qⁿ⁺¹ by the chain rule, through the power rule at q(z)",
							"complex_derivative_at((λy:complex. y ^ (n + 1)) ∘ «q», "+
								"    z, "+
								"    complex_of_real(&(n + 1)) * "+
								"    «q»(z) ^ n * "+
								"    ((complex_of_real(&0) * (z - c) - (w - c) * complex_of_real(&1)) / (z - c) ^ 2))",
							By(
								quotient,
								complex_derivative.DerivativePow.At(b.TermAs[Nat]("n + 1"), b.TermAs[Complex]("«q»(z)")),
								nat_arith.Add1.At(n),
								nat_monus.SucSubOne.At(n),
								complex_derivative.DerivativeChain.At(
									b.TermAs[Fun[Complex, Complex]]("λy:complex. y ^ (n + 1)"),
									ratio,
									z,
									powSlope,
									qSlope))),
						functions.ComposeApply)
					value := b.Have(
						"−1/(n + 1) times that derivative is qⁿ⁺¹/(z − c), q being (w − c)·1/(z − c)",
						"-complex_inv(complex_of_real(&(n + 1))) * "+
							"(complex_of_real(&(n + 1)) * "+
							"    «q»(z) ^ n * "+
							"    ((complex_of_real(&0) * (z - c) - (w - c) * complex_of_real(&1)) / (z - c) ^ 2)) = "+
							"«q»(z) ^ (n + 1) / (z - c)",
						Simp(
							Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
							Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid)),
							Fwd(comm_monoid.PowTwo.Read(complex_field.MulMonoid)),
							Fwd(field.DivMulInv.Read(complex_field.Field)),
							Fwd(field.InvMul.Read(complex_field.Field))),
						ByArith())
					b.Show(
						"so scaling qⁿ⁺¹ by −1/(n + 1) scales its derivative to qⁿ⁺¹/(z − c)",
						By(
							value,
							power,
							complex_derivative.DerivativeScale.At(
								b.TermAs[Fun[Complex, Complex]]("λx:complex. «q»(x) ^ (n + 1)"),
								z,
								b.TermAs[Complex](
									"complex_of_real(&(n + 1)) * "+
										"«q»(z) ^ n * "+
										"((complex_of_real(&0) * (z - c) - (w - c) * complex_of_real(&1)) / (z - c) ^ 2)"),
								b.TermAs[Complex]("-complex_inv(complex_of_real(&(n + 1)))"))))
				}))
			onCircle := a.Have(
				"on the circle, which misses its centre, the primitive "+
					"has the term as its derivative, and the term is continuous",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"|z - c| = r",
					},
					Conclusion: "complex_derivative_at( " +
						"    λu:complex. -complex_inv(complex_of_real(&(n + 1))) * «q»(u) ^ (n + 1), " +
						"    z, " +
						"    «q»(z) ^ (n + 1) / (z - c)) ∧ " +
						"complex_continuous_at(λu:complex. «q»(u) ^ (n + 1) / (u - c), z)",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					on := b.Assume()
					off := b.Have(
						"z is not c, lying at distance r > 0 from it",
						"z ≠ c",
						ByArith(on, positive, complex_abs.AbsPosIffNonzero.At(b.TermAs[Complex]("z - c"))))
					b.Show(
						"off c the primitive has that derivative, and the term is continuous",
						By(off, derivative.At(z), CutSeriesContinuous.At(c, w, c, z, b.TermAs[Nat]("n + 1"))))
				}))
			a.Show(
				"so the term, which has a primitive on the circle, integrates to 0 round it",
				ByArith(positive, onCircle, path_integral.CircleIntegralPrimitive.At(primitive, term, c, r)))
		}),
})}

// CircleRemainder — once round a circle about c, the integral of 1/(z − w)
// for w inside is 2πi plus the integral of the remainder qᴺ⁺¹/(z − w) left
// when the series in q(z) = (w − c)/(z − c) is cut after N + 1 terms. Off c
// and w, qᵏ/(z − w) = qᵏ/(z − c) + qᵏ⁺¹/(z − w), and the circle avoids both
// points, so round it the remainder after k terms is the (k + 1)-th term
// plus the remainder after k + 1. The first term, 1/(z − c), integrates to
// 2πi and every later one to 0, so by induction on N the terms cut off
// contribute 2πi in all.
var CircleRemainder = circleRemainderThm{family.Add(registry.ProofEntry{
	Name: "CircleRemainder",
	Key:  "prop_98bf9d918859b806",
	Build: family.Theorem(Statement{
		Binders: "∀c w:complex. ∀r:real. ∀N:num.",
		Hypotheses: []string{
			"|w - c| < r",
		},
		Conclusion: "«circleInt»(λz:complex. complex_inv(z - w), c, r) = " +
			"&(&2 * pi) * complex_i + «circleInt»(λz:complex. «q»(z) ^ (N + 1) / (z - w), c, r)",
		Abbrev: Abbrev{
			{Name: "q", Text: "λz:complex. (w - c) / (z - c)"},
		},
	},
		func(a *Argument, c, w *Expr[Complex], r *Expr[Real], inside Fact) {
			positive := a.Have(
				"the radius is positive, exceeding |w − c| ≥ 0",
				"&0 < r",
				ByArith(inside, complex_abs.AbsNonneg.At(a.TermAs[Complex]("w - c"))))
			notOn := a.Have(
				"w is not on the circle, lying nearer c than r",
				"|w - c| ≠ r",
				ByArith(inside))
			avoids := a.Have(
				"a point of the circle is neither c nor w",
				"∀z:complex. |z - c| = r ⇒ z ≠ c ∧ z ≠ w",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("z")
					on := b.Assume()
					off := b.Have(
						"z is not c, lying at distance r > 0 from it",
						"z ≠ c",
						ByArith(on, positive, complex_abs.AbsPosIffNonzero.At(b.TermAs[Complex]("z - c"))))
					b.Show(
						"nor w, which is not on the circle",
						By(Normalized, on, notOn, off))
				}))
			cut := a.Have(
				"off c and w one more term is cut off by 1/(z − w) = 1/(z − c) + q/(z − w), multiplied by qᵏ",
				Statement{
					Binders: "∀k:num. ∀z:complex.",
					Hypotheses: []string{
						"z ≠ c",
						"z ≠ w",
					},
					Conclusion: "«q»(z) ^ k / (z - w) = «q»(z) ^ k / (z - c) + «q»(z) ^ (k + 1) / (z - w)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.FixAs[Complex]("z")
					off := b.Assume()
					away := b.Have(
						"z − c and z − w are not 0",
						"z - c ≠ &0 ∧ z - w ≠ &0",
						ByArith(off))
					b.Show(
						"with q = (w − c)·1/(z − c), the two sides differ by qᵏ times "+
							"multiples of (z − c)·1/(z − c) − 1 and (z − w)·1/(z − w) − 1",
						Simp(
							Fwd(comm_monoid.PowAdd.Read(complex_field.MulMonoid)),
							Fwd(comm_monoid.PowOne.Read(complex_field.MulMonoid)),
							Fwd(field.DivMulInv.Read(complex_field.Field))),
						ByArith(away))
				}))
			shift := a.Have(
				"so round the circle the remainder after k terms is "+
					"the (k + 1)-th term plus the remainder after k + 1",
				"∀k:num. "+
					"    «circleInt»(λz:complex. «q»(z) ^ k / (z - w), c, r) = "+
					"    «circleInt»(λz:complex. «q»(z) ^ k / (z - c), c, r) + "+
					"    «circleInt»(λz:complex. «q»(z) ^ (k + 1) / (z - w), c, r)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					agree := b.Have(
						"on the circle, which misses c and w, the remainder is the term plus the next remainder",
						Statement{
							Binders: "∀z:complex.",
							Hypotheses: []string{
								"|z - c| = r",
							},
							Conclusion: "«q»(z) ^ k / (z - w) = «q»(z) ^ k / (z - c) + «q»(z) ^ (k + 1) / (z - w)",
						},
						By(avoids, cut))
					continuous := b.Have(
						"and the term and the next remainder are continuous there",
						"(∀z:complex. |z - c| = r ⇒ complex_continuous_at(λu:complex. «q»(u) ^ k / (u - c), z)) ∧ "+
							"(∀z:complex. |z - c| = r ⇒ complex_continuous_at(λu:complex. «q»(u) ^ (k + 1) / (u - w), z))",
						By(avoids, CutSeriesContinuous))
					term := b.TermAs[Fun[Complex, Complex]]("λz:complex. «q»(z) ^ k / (z - c)")
					next := b.TermAs[Fun[Complex, Complex]]("λz:complex. «q»(z) ^ (k + 1) / (z - w)")
					b.Show(
						"and the integral round the circle sees the integrand "+
							"only there and is additive in functions continuous there",
						ByArith(
							positive,
							agree,
							continuous,
							path_integral.CircleIntegralCongruence.At(
								b.TermAs[Fun[Complex, Complex]]("λz:complex. «q»(z) ^ k / (z - w)"),
								b.TermAs[Fun[Complex, Complex]]("λz:complex. «q»(z) ^ k / (z - c) + «q»(z) ^ (k + 1) / (z - w)"),
								c,
								r),
							path_integral.CircleIntegralAdd.At(term, next, c, r)))
				}))
			first := a.Have(
				"the first term, q⁰/(z − c) = 1/(z − c), integrates to 2πi",
				"«circleInt»(λz:complex. «q»(z) ^ 0 / (z - c), c, r) = &(&2 * pi) * complex_i",
				Simp(
					Fwd(comm_monoid.MonoidPowDef.Inst[Complex]()),
					Fwd(field.DivMulInv.Read(complex_field.Field)),
					Fwd(comm_monoid.LeftIdentity.Read(complex_field.MulMonoid))),
				By(positive, path_integral.CircleIntegralInverse))
			start := a.Have(
				"and the remainder after no terms, q⁰/(z − w) = 1/(z − w), is the integrand itself",
				"«circleInt»(λz:complex. complex_inv(z - w), c, r) = "+
					"«circleInt»(λz:complex. «q»(z) ^ 0 / (z - w), c, r)",
				Simp(
					Fwd(comm_monoid.MonoidPowDef.Inst[Complex]()),
					Fwd(field.DivMulInv.Read(complex_field.Field)),
					Fwd(comm_monoid.LeftIdentity.Read(complex_field.MulMonoid))),
				Refl())
			a.Induct("N")
			a.Base(
				"cutting off the first term leaves its integral 2πi and the remainder after it",
				By(shift.At(a.TermAs[Nat]("0")), start, first))
			a.Step(
				"each further term cut off integrates to 0",
				func(b *Argument, ih Fact) {
					index := b.Have(
						"the index suc(N) + 1 is N + 1 + 1",
						"suc(N) + 1 = N + 1 + 1",
						ByArith())
					b.Show(
						"the remainder after N + 1 terms is the (N + 2)-th "+
							"term, of integral 0, plus the remainder after N + 2",
						index.Rw(),
						ByArith(
							ih,
							shift.At(b.TermAs[Nat]("N + 1")),
							CircleHigherTermVanishes.At(c, w, r, b.TermAs[Nat]("N")),
							positive))
				})
		}),
})}

// CircleRemainderBound — the remainder after N terms is small: it is
// Taylor's weighted remainder for the constant weight 1, bounded by 1, so its
// integral round the circle is at most 2πr·(|w − c|/r)ᴺ/(r − |w − c|).
var CircleRemainderBound = circleRemainderBoundThm{family.Add(registry.ProofEntry{
	Name: "CircleRemainderBound",
	Key:  "prop_33346a31edeb67f8",
	Build: family.Theorem(Statement{
		Binders: "∀c w:complex. ∀r:real. ∀N:num.",
		Hypotheses: []string{
			"|w - c| < r",
		},
		Conclusion: "|«circleInt»(λz:complex. «q»(z) ^ N / (z - w), c, r)| ≤ " +
			"&2 * pi * r * real_pow(|w - c| / r, N) / (r - |w - c|)",
		Abbrev: Abbrev{
			{Name: "q", Text: "λz:complex. (w - c) / (z - c)"},
		},
	},
		func(a *Argument, c, w *Expr[Complex], r *Expr[Real], N *Expr[Nat], inside Fact) {
			weight := a.TermAs[Fun[Complex, Complex]]("λv:complex. &(&1)")
			constant := a.Have(
				"the constant weight 1 is continuous, and of modulus 1",
				"∀u:complex. |u - c| = r ⇒ complex_continuous_at(λv:complex. &(&1), u) ∧ |&(&1)| ≤ &1",
				ByArith(complex_topology.ContinuousAtConst, complex_abs.AbsOfReal.At(a.TermAs[Real]("&1"))))
			unweighted := a.Have(
				"weighting the remainder by 1 leaves it, and so its integral, as it is",
				"«circleInt»(λu:complex. &(&1) * («q»(u) ^ N / (u - w)), c, r) = "+
					"«circleInt»(λz:complex. «q»(z) ^ N / (z - w), c, r)",
				By(a.Have(
					"1 times the remainder is the remainder",
					"(λu:complex. &(&1) * («q»(u) ^ N / (u - w))) = (λz:complex. «q»(z) ^ N / (z - w))",
					Funext(),
					ByArith())))
			a.Show(
				"so Taylor's bound for the weight 1 bounds the remainder",
				ByArith(
					inside,
					constant,
					unweighted,
					TaylorRemainderBound.At(weight, c, w, r, a.TermAs[Real]("&1"), N)))
		}),
})}

// CircleWindingInside — once round a circle, 1/(z − w) integrates to 2πi
// for every w inside, not only the centre. For every n the integral differs
// from 2πi by the remainder after n + 1 terms of the series in
// (w − c)/(z − c), which is at most 2πr/(r − |w − c|)·(|w − c|/r)ⁿ⁺¹; these
// bounds tend to 0 since |w − c|/r < 1, so the fixed distance between the
// integral and 2πi, below all of them, is 0.
var CircleWindingInside = circleWindingInsideThm{family.Add(registry.ProofEntry{
	Name: "CircleWindingInside",
	Key:  "prop_5012637fd783c980",
	Build: family.Theorem(Statement{
		Binders: "∀c w:complex. ∀r:real.",
		Hypotheses: []string{
			"|w - c| < r",
		},
		Conclusion: "«circleInt»(λz:complex. complex_inv(z - w), c, r) = &(&2 * pi) * complex_i",
		Abbrev: Abbrev{
			{Name: "q", Text: "λz:complex. (w - c) / (z - c)"},
		},
	},
		func(a *Argument, c, w *Expr[Complex], r *Expr[Real], inside Fact) {
			sizes := a.Have(
				"r and r − |w − c| are positive, and the ratio |w − c|/r lies in [0, 1)",
				"&0 < r ∧ &0 < r - |w - c| ∧ &0 ≤ |w - c| / r ∧ |w - c| / r < &1",
				ByArith(inside, complex_abs.AbsNonneg.At(a.TermAs[Complex]("w - c"))))
			below := a.Have(
				"for every n the distance of the integral from 2πi is at most 2πr/(r − |w − c|)·(|w − c|/r)ⁿ⁺¹",
				"∀n:num. "+
					"    |«circleInt»(λz:complex. complex_inv(z - w), c, r) - &(&2 * pi) * complex_i| ≤ "+
					"    &2 * pi * r / (r - |w - c|) * real_pow(|w - c| / r, n + 1)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					remainder := b.Have(
						"the distance is the remainder after n + 1 terms",
						"«circleInt»(λz:complex. complex_inv(z - w), c, r) - &(&2 * pi) * complex_i = "+
							"«circleInt»(λz:complex. «q»(z) ^ (n + 1) / (z - w), c, r)",
						ByArith(inside, CircleRemainder.At(c, w, r, n)))
					b.Show(
						"whose modulus the remainder bound controls",
						ByArith(remainder, inside, CircleRemainderBound.At(c, w, r, b.TermAs[Nat]("n + 1"))))
				}))
			ratio := a.TermAs[Real]("|w - c| / r")
			scale := a.TermAs[Real]("&2 * pi * r / (r - |w - c|)")
			zero := a.TermAs[Real]("&0")
			powers := a.Have(
				"the powers of the ratio tend to 0, the ratio lying in [0, 1)",
				"real_converges_to(λn:num. real_pow(|w - c| / r, n), &0)",
				ByArith(sizes, real_sequences.PowerTendsToZero.At(ratio)))
			bounds := a.Have(
				"so do the bounds 2πr/(r − |w − c|)·(|w − c|/r)ⁿ⁺¹",
				"real_converges_to(λn:num. &2 * pi * r / (r - |w - c|) * real_pow(|w - c| / r, n + 1), "+
					"    &2 * pi * r / (r - |w - c|) * &0)",
				By(
					powers,
					real_sequences.LimitShift.At(a.TermAs[Fun[Nat, Real]]("λn:num. real_pow(|w - c| / r, n)"), zero),
					real_sequences.LimitScale.At(
						a.TermAs[Fun[Nat, Real]]("λn:num. real_pow(|w - c| / r, n + 1)"), zero, scale)))
			distance := a.TermAs[Real](
				"|«circleInt»(λz:complex. complex_inv(z - w), c, r) - &(&2 * pi) * complex_i|")
			limit := a.Have(
				"the fixed distance, below every bound, is at most their limit",
				"|«circleInt»(λz:complex. complex_inv(z - w), c, r) - &(&2 * pi) * complex_i| ≤ "+
					"&2 * pi * r / (r - |w - c|) * &0",
				By(
					below,
					bounds,
					real_sequences.LimitConst.At(distance),
					real_sequences.LimitLessEq.At(
						a.TermAs[Fun[Nat, Real]](
							"λn:num. |«circleInt»(λz:complex. complex_inv(z - w), c, r) - &(&2 * pi) * complex_i|"),
						a.TermAs[Fun[Nat, Real]]("λn:num. &2 * pi * r / (r - |w - c|) * real_pow(|w - c| / r, n + 1)"),
						distance,
						a.TermAs[Real]("&2 * pi * r / (r - |w - c|) * &0"),
						a.TermAs[Nat]("0"))))
			difference := a.TermAs[Complex](
				"«circleInt»(λz:complex. complex_inv(z - w), c, r) - &(&2 * pi) * complex_i")
			a.Show(
				"so the distance is 0, and the integral is 2πi",
				ByArith(limit, complex_abs.AbsNonneg.At(difference), complex_abs.AbsEqZero.At(difference)))
		}),
})}
