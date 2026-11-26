// perturbation.go — a nonzero constant term of a nonconstant polynomial is
// not a modulus minimum.

package complex_polynomial

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialStrictDecrease — a nonzero constant term of a
// nonconstant polynomial cannot be a modulus minimum. Align the first
// nonconstant coefficient inward and make the higher tail smaller.
var PolynomialStrictDecrease = polynomialStrictDecreaseThm{family.Add(registry.ProofEntry{
	Name: "PolynomialStrictDecrease",
	Key:  "prop_49e1a3c3813fb0ee",
	Build: family.Sections(Statement{
		Binders:    "∀P:(num → complex).",
		Hypotheses: []string{"polynomial_over(𝕌, P)", "0 < polynomial_degree(P)", "P(0) ≠ &0"},
		Conclusion: "∃z:complex. |«v»(z)| < |P(0)|",
		Abbrev: Abbrev{
			{Name: "v", Text: "λz:complex. polynomial_eval(P, z)"},
			{Name: "head", Text: "λk:num. λz:complex. P(0) + P(k) * z ^ k"},
			{Name: "tail", Text: "λk:num. λz:complex. " +
				"    module_sum(complex_add, " +
				"        complex_of_real(&0), " +
				"        {i:num | k < i ∧ i ≤ polynomial_degree(P)}, " +
				"        λi:num. P(i) * z ^ i)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		belowBoth := ctx.Lemma(Statement{
			Binders: "∀A B:real.", Hypotheses: []string{"&0 < A", "&0 < B"},
			Conclusion: "∃r:real. &0 < r ∧ r ≤ &1 ∧ r < A ∧ r < B",
		}, func(a *Argument, A, B *Expr[Real], h Fact) {
			a.Take(a.TermAs[Real]("min(&1, min(A, B)) / &2"))
			a.Show(
				"half the positive minimum lies below both bounds",
				ByArith(h))
		})
		smallRadius := ctx.Lemma(Statement{
			Binders: "∀a gap C:real.", Hypotheses: []string{"&0 < a", "&0 < gap", "&0 ≤ C"},
			Conclusion: "∃r:real. &0 < r ∧ r ≤ &1 ∧ a * r < &1 ∧ C * r < gap",
		}, func(arg *Argument, a, gap, C *Expr[Real], h Fact) {
			positive := arg.Have(
				"the two controlling radius bounds are positive",
				"&0 < &1 / (a + &1) ∧ &0 < gap / (C + &1)",
				ByArith(
					h,
					real_order_field.DivPos.At(arg.TermAs[Real]("&1"), arg.TermAs[Real]("a + &1")),
					real_order_field.DivPos.At(gap, arg.TermAs[Real]("C + &1"))))
			r, bounds := arg.ObtainAs[Real](
				"choose a radius below both controlling bounds",
				"∃r:real. &0 < r ∧ r ≤ &1 ∧ r < &1 / (a + &1) ∧ r < gap / (C + &1)",
				By(positive, At(belowBoth, arg.TermAs[Real]("&1 / (a + &1)"), arg.TermAs[Real]("gap / (C + &1)"))))
			arg.Take(r)
			arg.Show(
				"clear the positive denominators to obtain the product bounds",
				ByArith(
					h,
					bounds,
					real_order_field.LessThanDivMulLeft.At(r, gap, arg.TermAs[Real]("C + &1")),
					real_order_field.LessThanDivMulLeft.At(r, arg.TermAs[Real]("&1"), arg.TermAs[Real]("a + &1"))))
		})
		radial := ctx.Lemma(Statement{
			Binders:    "∀c d u:complex. ∀r:real. ∀k:num.",
			Hypotheses: []string{"&0 ≤ r", "d * u ^ k = -complex_of_real(|d|)", "|d| * r ^ k ≤ &1"},
			Conclusion: "|c + (c * d) * (complex_of_real(r) * u) ^ k| = |c| * (&1 - |d| * r ^ k)",
		}, func(arg *Argument, c, d, u *Expr[Complex], r *Expr[Real], k *Expr[Nat], h Fact) {
			powers := arg.Have(
				"separate the radial power from the unit-direction power",
				"(complex_of_real(r) * u) ^ k = complex_of_real(r ^ k) * u ^ k",
				Simp(
					Fwd(comm_monoid.MulPow.Read(comm_ring.MulMonoid.Read(complex_field.CommRing))),
					Rev(complex_field.OfRealPow)),
				Basic())
			grouped := arg.Have(
				"expose the aligned coefficient inside the factorization",
				"c + (c * d) * (complex_of_real(r) * u) ^ k = c * (&1 + complex_of_real(r ^ k) * (d * u ^ k))",
				Simp(Fwd(powers)),
				ByArith(complex_field.CommRing))
			factor := arg.Have(
				"the first two terms are a nonnegative real contraction of c",
				"c + (c * d) * (complex_of_real(r) * u) ^ k = c * complex_of_real(&1 + -(|d| * r ^ k))",
				Simp(
					Fwd(grouped),
					Fwd(h),
					Fwd(complex_field.OfRealAdd),
					Fwd(complex_field.OfRealNeg),
					Fwd(complex_field.OfRealMul)),
				ByArith(complex_field.CommRing))
			realFactor := arg.Have(
				"the real contraction factor is nonnegative",
				"|&1 + -(|d| * r ^ k)| = &1 - |d| * r ^ k",
				ByArith(h))
			arg.Show(
				"take the modulus of the contraction",
				Simp(Fwd(factor), Fwd(complex_abs.AbsMul), Fwd(complex_abs.AbsOfReal)),
				By(realFactor))
		})
		return ctx.Theorem(headline, func(arg *Argument, P *Arrow[Nat, Complex], h Fact) {
			k, first := arg.ObtainAs[Nat](
				"choose the first nonconstant coefficient",
				"∃k:num. 0 < k ∧ P(k) ≠ &0 ∧ (∀i:num. 0 < i ∧ i < k ⇒ P(i) = &0)",
				By(
					h,
					polynomial.FirstNonconstantTerm.At(
						arg.TermAs[Complex]("complex_of_real(&0)"), arg.TermAs[Set[Complex]]("𝕌"), P)))
			d, ratio := arg.LetAs[Complex]("d", "P(k) / P(0)")
			nonzero := arg.Have(
				"both selected coefficients are nonzero",
				"P(k) ≠ &0 ∧ P(0) ≠ &0",
				By(first, h))
			coefficient := arg.Have(
				"the normalized ratio recovers the first coefficient",
				"P(0) * d = P(k)",
				By(
					Normalized,
					ratio,
					nonzero,
					field.DivLeftMul.Read(complex_field.Field).At(
						arg.TermAs[Complex]("P(k)"), arg.TermAs[Complex]("P(0)"))))
			dNonzero := arg.Have(
				"the normalized first coefficient is nonzero",
				"d ≠ &0",
				By(
					Normalized,
					coefficient,
					nonzero,
					comm_ring.MulRightZero.Read(complex_field.CommRing).At(arg.TermAs[Complex]("P(0)"))))
			u, direction := arg.ObtainAs[Complex](
				"align the first coefficient inward",
				"∃u:complex. |u| = &1 ∧ d * u ^ k = -complex_of_real(|d|)",
				By(dNonzero, first, DescendingDirection.At(k, d)))
			C, tailCoefficients := arg.LetAs[Real](
				"C", "sum({i:num | k < i ∧ i ≤ polynomial_degree(P)}, λi:num. |P(i)|)")
			positive := arg.Have(
				"the constant and first coefficient moduli are positive and the tail bound is nonnegative",
				"&0 < |d| ∧ &0 < |P(0)| ∧ &0 ≤ C",
				SplitConjAll(
					Case(
						"positive normalized coefficient modulus",
						By(dNonzero, complex_abs.AbsPosIffNonzero.At(d))),
					Case(
						"positive constant modulus",
						By(nonzero, complex_abs.AbsPosIffNonzero.At(arg.TermAs[Complex]("P(0)")))),
					Case(
						"nonnegative sum of tail coefficient moduli",
						Simp(Fwd(tailCoefficients)),
						By(real_sum.Nonneg, complex_abs.AbsNonneg))))
			r, radius := arg.ObtainAs[Real](
				"choose a radius controlling both the first term and the higher tail",
				"∃r:real. &0 < r ∧ r ≤ &1 ∧ |d| * r < &1 ∧ C * r < |P(0)| * |d|",
				ByArith(positive, At(smallRadius, arg.TermAs[Real]("|d|"), arg.TermAs[Real]("|P(0)| * |d|"), C)))
			z, point := arg.LetAs[Complex]("z", "complex_of_real(r) * u")
			arg.Take(z)
			norm := arg.Have(
				"the radial perturbation has modulus r",
				"|z| = r",
				Simp(Fwd(point), Fwd(complex_abs.AbsMul), Fwd(complex_abs.AbsOfReal), Fwd(direction)),
				ByArith(radius))
			expansion := arg.Have(
				"expand into the constant, first, and higher terms",
				"«v»(z) = P(0) + (P(k) * z ^ k + «tail»(k,z))",
				By(
					h,
					first,
					polynomial_evaluation.EvalFirstTermExpansion.Read(complex_field.CommRingOn).AsFact().At(P, k, z),
					complex_field.ComplexRingDef,
					set_basic.InUniv.Inst[Complex]()))
			powers := arg.Have(
				"positive powers of a small radius do not exceed it",
				"&0 < r ^ k ∧ r ^ k ≤ r ∧ |d| * r ^ k < &1",
				ByArith(
					first,
					positive,
					radius,
					real_pow.PowPos.At(r, k),
					real_pow.PowMonoExpBelowOne.At(r, arg.TermAs[Nat]("1"), k),
					real_pow.PowOne.At(r),
					real_order_ring.LessEqMulLeft.At(arg.TermAs[Real]("|d|"), arg.TermAs[Real]("r ^ k"), r)))
			tail := arg.Have(
				"the higher terms are bounded by one additional power of r",
				"|«tail»(k,z)| ≤ C * r ^ (k + 1)",
				ByArith(
					tailCoefficients,
					norm,
					radius,
					PolynomialHigherTermsBound.At(P, k, arg.TermAs[Nat]("polynomial_degree(P)"), z)))
			headModulus := arg.Have(
				"the inward first term decreases the constant modulus exactly",
				"|«head»(k,z)| = |P(0)| * (&1 - |d| * r ^ k)",
				Simp(Rev(coefficient), Fwd(point)),
				ByArith(direction, radius, powers, At(radial, arg.TermAs[Complex]("P(0)"), d, u, r, k)))
			triangle := arg.Have(
				"the full modulus is at most the first-part modulus plus the higher tail",
				"|«v»(z)| ≤ |«head»(k,z)| + |«tail»(k,z)|",
				Derive(func(b *Argument) {
					grouped := b.Have(
						"group the two leading terms together",
						"«v»(z) = «head»(k,z) + «tail»(k,z)",
						ByArith(expansion, complex_field.CommRing))
					b.Show(
						"apply the complex triangle inequality",
						Simp(Fwd(grouped)),
						By(complex_abs.AbsTriangle))
				}))
			higherOrder := arg.Simplified(tail, Fwd(real_pow.PowAddOne))
			arg.Show(
				"the tail is smaller than the strict first-term loss",
				ByArith(
					headModulus,
					higherOrder,
					triangle,
					powers,
					radius,
					real_order_ring.LessThanMulRight.At(
						arg.TermAs[Real]("C * r"), arg.TermAs[Real]("|P(0)| * |d|"), arg.TermAs[Real]("r ^ k"))))
		})
	}),
})}
