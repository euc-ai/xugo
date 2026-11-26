// roots.go — the reciprocal roots of a smooth curve: their power sums measure how
// far the point counts lie from q^m + 1, a coarse bound along a progression puts
// each root in the disk of radius √q, their product q^g fixes each modulus, and the
// Hasse-Weil bound follows in every extension.

package weil_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/finite_spectrum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_zeta"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/twist_quotient_bound"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// PowerSumIsPointDefect — the trace formula read as a modulus: the m-th power sum
// of the reciprocal roots has the modulus of N(m) − (q^m + 1), how far the count
// over the extension of degree m lies from q^m + 1. The formula makes the power
// sum that defect, embedded in ℂ and negated, and neither moves a modulus.
var PowerSumIsPointDefect = powerSumIsPointDefectThm{family.Add(registry.ProofEntry{
	Name: "PowerSumIsPointDefect",
	Key:  "prop_cd0c32e4e3e0b1e8",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀a:(num → complex). ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"curve_reciprocal_roots(«functionRing», k, A₀, A₁, A₀₁, a)",
			"0 < m",
		},
		Conclusion: "complex_abs(finite_power_sum(2 * «genus», a, m)) = " +
			"real_abs(real_of_num(«count»(m)) - real_of_num(card(k) ^ m + 1))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, Complex],
		m *Expr[Nat],
		closed, subK, curve, roots, positive Fact,
	) {
		trace := arg.Conjuncts(
			GroupPremises(subK, curve, curve_zeta.CurvePointCountTraceFormula.Read(M).At(K, k, A0, A1, A01, t)),
			"P has a family of 2g reciprocal roots",
			"and every such family computes the point counts and the base changes of P")
		counting := arg.Conjuncts(
			GroupPremises(roots, trace[1].At(a)),
			"the point counts are q^m + 1 less the power sums",
			"the product of the roots is q^g",
			"over each extension the numerator has their powers as reciprocal roots",
			"their reversed polynomial vanishes at each of them")
		defect := arg.Have(
			"so the power sum is the defect embedded in ℂ and negated",
			"finite_power_sum(2 * «genus», a, m) = "+
				"complex_neg(complex_of_real(real_of_num(«count»(m)) - real_of_num(card(k) ^ m + 1)))",
			Simp(Fwd(complex_field.OfRealSub)),
			ByArith(counting[0].At(m), positive))
		arg.Show(
			"negation and the embedding of ℝ keep the modulus",
			By(defect, complex_abs.AbsNeg, complex_abs.AbsOfReal))
	}),
})}

// RootOfConstantsPositive — √q is positive for a smooth curve over a finite field
// of q elements: the constants are a finite field, so a finite set with a point.
var RootOfConstantsPositive = rootOfConstantsPositiveThm{family.Add(registry.ProofEntry{
	Name: "RootOfConstantsPositive",
	Key:  "prop_38f0b5a180004ed8",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"smooth_finite_curve(F, k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "&0 < real_sqrt(«q»)",
	}, func(arg *Argument, F *Expr[FieldOps[A]], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
		constants := arg.Unfolded(
			arg.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef), algebraic_curve.CurveOverLineDef)
		points := arg.Have(
			"the constants are a finite field, so a finite set with a point",
			"0 < card(k)",
			By(
				Normalized,
				constants,
				field.SubfieldZero.At(F, k),
				set_basic.MemberNotEmpty.At(k),
				cardinality.CardEqZero.At(k),
				nat_order.PosIffNonzero.At(arg.TermAs[Nat]("card(k)"))))
		arg.Show(
			"so q is positive, and with it √q",
			ByArith(points, real_sqrt.SqrtPos.At(arg.TermAs[Real]("«q»"))))
	}),
})}

// CurveReciprocalRootsUpperModulus — every reciprocal root of a smooth curve over
// a finite field has modulus at most √q. The coarse bound holds at every multiple
// of 2r, so R may be chosen after seeing the spectrum: a multiple of 2r at which
// every collision of powers of the roots has already happened
// (RootOfUnityRatiosKilledByPower). Equal R-th powers then group with positive
// multiplicities, so nothing cancels in the power sums, and the coarse bound on
// them puts each root in the disk of radius √q (ScaledProgressionModulusBound).
var CurveReciprocalRootsUpperModulus = curveReciprocalRootsUpperModulusThm{family.Add(registry.ProofEntry{
	Name: "CurveReciprocalRootsUpperModulus",
	Key:  "prop_d287f15e067960ea",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀a:(num → complex). ∀i:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"curve_reciprocal_roots(«functionRing», k, A₀, A₁, A₀₁, a)",
			"i < 2 * «genus»",
		},
		Conclusion: "complex_abs(a(i)) ≤ real_sqrt(«q»)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, Complex],
		i *Expr[Nat],
		closed, subK, curve, roots, member Fact,
	) {
		count := arg.TermAs[Nat]("2 * «genus»")
		size := arg.TermAs[Nat]("card(k)")
		q := arg.TermAs[Real]("«q»")
		rootOfQ := arg.TermAs[Real]("real_sqrt(«q»)")
		_, h0, admissible := arg.Unpack2As[Nat, Nat](
			GroupPremises(
				subK,
				curve,
				twist_quotient_bound.CoarseBoundAfterAdmissibleBaseChange.Read(M).At(K, k, A0, A1, A01, t)),
			"r",
			"h₀")
		degrees := arg.Conjuncts(
			admissible,
			"the admissible degree r is positive",
			"the progression step h₀ is positive",
			"every positive multiple of 2r has a coarse bound of its own")
		twoRPositive := arg.Have(
			"so 2r is positive",
			"0 < 2 * r",
			ByArith(degrees[0]))
		R, killing := arg.UnpackAs[Nat](
			GroupPremises(
				twoRPositive,
				finite_spectrum.RootOfUnityRatiosKilledByPower.At(count, arg.TermAs[Nat]("2 * r"), a)),
			"R")
		chosen := arg.Conjuncts(
			killing,
			"choose a positive R",
			"a multiple of 2r",
			"at which every power collision among the roots has already happened")
		bounded := arg.Have(
			"R being a positive multiple of 2r, the coarse bound at R "+
				"bounds the power sums along its multiples by powers of √q",
			"∃B:real. ∃N:num. ∀n:num. "+
				"    N ≤ n ⇒ "+
				"    complex_abs(finite_power_sum(2 * «genus», a, R * (1 + h₀ * n))) ≤ "+
				"    B * real_sqrt(«q») ^ (R * (1 + h₀ * n))",
			Derive(func(d *Argument) {
				B, n0, coarse := d.Unpack2As[Real, Nat](
					GroupPremises(chosen[0], chosen[1], degrees[2].At(R)), "B", "n₀")
				d.Take(B)
				d.Take(n0)
				d.FixAs[Nat]("n")
				past := d.Assume()
				exponent := d.TermAs[Nat]("R * (1 + h₀ * n)")
				d.Show(
					"the power sum has the modulus of the defect, which the coarse bound controls",
					real_order_ring.OrderCalc(d.Ctx()).CalcLeibniz(
						d.TermAs[Real]("complex_abs(finite_power_sum(2 * «genus», a, R * (1 + h₀ * n)))"),
						EqLeg(
							d.TermAs[Real](
								"real_abs(real_of_num(«count»(R * (1 + h₀ * n))) - real_of_num(card(k) ^ (R * (1 + h₀ * n)) + 1))"),
							"it is the defect of the count over the extension of that degree",
							ByArith(
								closed,
								subK,
								curve,
								roots,
								chosen[0],
								PowerSumIsPointDefect.Read(M).At(K, k, A0, A1, A01, t, a, exponent))),
						LeLeg(
							d.TermAs[Real]("B * real_sqrt(real_of_num(card(k) ^ (R * (1 + h₀ * n))))"),
							"the coarse bound at R",
							By(past, coarse)),
						EqLeg(
							d.TermAs[Real]("B * real_sqrt(«q») ^ (R * (1 + h₀ * n))"),
							"the root of the power is the power of the root",
							ByArith(real_sqrt.SqrtOfPow.At(q, exponent), real_pow.OfNumPow.At(size, exponent)))))
			}))
		reciprocal := arg.Unfolded(roots, curve_zeta.CurveReciprocalRootsDef)
		positiveCollision := arg.Have(
			"the collision exponent R · h₀ is positive",
			"0 < R * h₀",
			ByArith(chosen[0], degrees[1], nat_arith.MulEqZero.At(R, h0)))
		arg.Show(
			"the growth theorem at radius √q and step R, a collision at R · h₀ being one at R",
			By(
				chosen[0],
				degrees[1],
				curve,
				RootOfConstantsPositive.At(arg.TermAs[FieldOps[A]]("restrict_field(M, K)"), k, A0, A1, A01, t),
				reciprocal,
				chosen[2].At(arg.TermAs[Nat]("R * h₀")),
				positiveCollision,
				bounded,
				member,
				finite_spectrum.ScaledProgressionModulusBound.At(count, R, h0, rootOfQ, a, i)))
	}),
})}

// RiemannHypothesisGeneralCurves — the Riemann hypothesis for a smooth curve of
// genus g over a finite field of q elements: the 2g reciprocal roots of the zeta
// numerator all have modulus √q, and the zeros of the numerator all have modulus
// 1/√q. The product of the 2g roots has modulus q^g = (√q)^(2g), while each root has
// modulus at most √q, so each attains that bound; a zero of the numerator is the
// reciprocal of a root.
var RiemannHypothesisGeneralCurves = riemannHypothesisGeneralCurvesThm{family.Add(registry.ProofEntry{
	Name: "RiemannHypothesisGeneralCurves",
	Key:  "prop_175cf46bc6013698",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀a:(num → complex).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"curve_reciprocal_roots(«functionRing», k, A₀, A₁, A₀₁, a)",
		},
		Conclusion: "(∀i:num. i < 2 * «genus» ⇒ complex_abs(a(i)) = real_sqrt(«q»)) ∧ " +
			"(∀z:complex. " +
			"    polynomial_eval(complex_add, " +
			"        complex_of_real(real_of_num(0)), " +
			"        complex_mul, " +
			"        complex_of_real(real_of_num(1)), " +
			"        λn:num. complex_of_real(«numerator»(n)), " +
			"        z) = " +
			"    complex_of_real(real_of_num(0)) ⇒ " +
			"    complex_abs(z) = real_of_num(1) / real_sqrt(«q»))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, Complex],
		closed, subK, curve, roots Fact,
	) {
		count := arg.TermAs[Nat]("2 * «genus»")
		genus := arg.TermAs[Nat]("«genus»")
		q := arg.TermAs[Real]("«q»")
		rootOfQ := arg.TermAs[Real]("real_sqrt(«q»)")
		positive := arg.Simplified(GroupPremises(
			curve,
			RootOfConstantsPositive.At(arg.TermAs[FieldOps[A]]("restrict_field(M, K)"), k, A0, A1, A01, t)))
		trace := arg.Conjuncts(
			GroupPremises(subK, curve, curve_zeta.CurvePointCountTraceFormula.Read(M).At(K, k, A0, A1, A01, t)),
			"the numerator has a family of reciprocal roots",
			"and each such family has the trace formula's properties")
		counting := arg.Conjuncts(
			GroupPremises(roots, trace[1].At(a)),
			"the point counts are q^m + 1 less the power sums",
			"the product of the roots is q^g",
			"over each extension the numerator has their powers as reciprocal roots",
			"their reversed polynomial vanishes at each of them")
		modulus := arg.Have(
			"so the product of the roots has modulus q^g, which is (√q)^(2g)",
			"complex_abs(product({i:num | i < 2 * «genus»}, a)) = real_sqrt(«q») ^ (2 * «genus»)",
			ByArith(
				counting[1],
				complex_abs.AbsOfNonnegReal.At(arg.TermAs[Real]("«q» ^ «genus»")),
				real_pow.PowNonneg.At(q, genus),
				real_sqrt.SqrtPowTwo.At(q),
				real_pow.PowPow.At(rootOfQ, arg.TermAs[Nat]("2"), genus)))
		moduli := arg.Have(
			"each root has modulus at most √q and they multiply to (√q)^(2g), so each is √q",
			"∀i:num. i < 2 * «genus» ⇒ complex_abs(a(i)) = real_sqrt(«q»)",
			arg.ForEach(func(i *Expr[Nat]) Action {
				return By(
					positive,
					closed,
					subK,
					curve,
					roots,
					CurveReciprocalRootsUpperModulus.Read(M),
					modulus,
					finite_spectrum.ProductModulusAtBound.At(count, a, rootOfQ, i))
			}))
		reciprocal := arg.Conjuncts(
			arg.Unfolded(roots, curve_zeta.CurveReciprocalRootsDef),
			"the roots are not zero",
			"the numerator is their reciprocal product")
		zeros := arg.Have(
			"a zero of the numerator is the reciprocal of a root, so its modulus is 1/√q",
			Statement{
				Binders: "∀z:complex.",
				Hypotheses: []string{
					"polynomial_eval(complex_add, " +
						"    complex_of_real(real_of_num(0)), " +
						"    complex_mul, " +
						"    complex_of_real(real_of_num(1)), " +
						"    λn:num. complex_of_real(«numerator»(n)), " +
						"    z) = " +
						"complex_of_real(real_of_num(0))",
				},
				Conclusion: "complex_abs(z) = real_of_num(1) / real_sqrt(«q»)",
			},
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]()
				zero := b.Assume()
				i, inverse := b.ObtainAs[Nat](
					"z is a zero of the reciprocal product, so a root times z is one",
					"∃i:num. i < 2 * «genus» ∧ complex_mul(a(i), z) = complex_of_real(real_of_num(1))",
					By(zero, reciprocal[1], finite_spectrum.ReciprocalProductZero.At(count, a, z)))
				b.Show(
					"|a(i)| |z| is one and |a(i)| is √q",
					ByArith(
						inverse,
						positive,
						moduli.At(i),
						complex_abs.AbsMul.At(b.TermAs[Complex]("a(i)"), z),
						complex_abs.AbsOfReal.At(b.TermAs[Real]("&1"))))
			}))
		arg.Show(
			"the roots and the zeros are the two halves of the theorem",
			By(moduli, zeros))
	}),
})}

// HasseWeilAllExtensions — the Hasse-Weil bound in every extension: the number of
// points over the extension of degree m lies within 2g√(q^m) of q^m + 1. That
// distance is the modulus of the m-th power sum of the 2g reciprocal roots
// (PowerSumIsPointDefect), each of modulus √q by the Riemann hypothesis, so the
// triangle inequality bounds it by 2g(√q)^m, and (√q)^m is √(q^m).
var HasseWeilAllExtensions = hasseWeilAllExtensionsThm{family.Add(registry.ProofEntry{
	Name: "HasseWeilAllExtensions",
	Key:  "prop_2c1a78078156d8fc",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"0 < m",
		},
		Conclusion: "real_abs(real_of_num(«count»(m)) - real_of_num(card(k) ^ m + 1)) ≤ " +
			"real_of_num(2 * «genus») * real_sqrt(real_of_num(card(k) ^ m))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		m *Expr[Nat],
		closed, subK, curve, positive Fact,
	) {
		trace := arg.Conjuncts(
			GroupPremises(subK, curve, curve_zeta.CurvePointCountTraceFormula.Read(M).At(K, k, A0, A1, A01, t)),
			"P has a family of 2g reciprocal roots",
			"and every such family computes the point counts and the base changes of P")
		a, roots := arg.UnpackAs[Fun[Nat, Complex]](trace[0], "a")
		moduli := arg.Conjuncts(
			GroupPremises(
				closed, subK, curve, roots, RiemannHypothesisGeneralCurves.Read(M).At(K, k, A0, A1, A01, t, a)),
			"each reciprocal root has modulus √q",
			"each zero of P has modulus 1/√q")
		count := arg.TermAs[Nat]("2 * «genus»")
		size := arg.TermAs[Nat]("card(k)")
		q := arg.TermAs[Real]("«q»")
		rootOfQ := arg.TermAs[Real]("real_sqrt(«q»)")
		arg.Show(
			"the distance from q^m + 1 is a sum of 2g powers of modulus (√q)^m",
			real_order_ring.OrderCalc(arg.Ctx()).CalcLeibniz(
				arg.TermAs[Real]("real_abs(real_of_num(«count»(m)) - real_of_num(card(k) ^ m + 1))"),
				EqLeg(
					arg.TermAs[Real]("complex_abs(finite_power_sum(2 * «genus», a, m))"),
					"it is the modulus of the power sum of the reciprocal roots",
					By(
						closed,
						subK,
						curve,
						roots,
						positive,
						PowerSumIsPointDefect.Read(M).At(K, k, A0, A1, A01, t, a, m))),
				LeLeg(
					arg.TermAs[Real]("real_of_num(2 * «genus») * real_sqrt(«q») ^ m"),
					"each of the 2g reciprocal roots has modulus √q",
					By(
						moduli[0],
						real_order_ring.LessEqRefl,
						finite_spectrum.PowerSumModulusBound.At(count, m, a, rootOfQ))),
				EqLeg(
					arg.TermAs[Real]("real_of_num(2 * «genus») * real_sqrt(real_of_num(card(k) ^ m))"),
					"the power of the root is the root of the power",
					ByArith(real_sqrt.SqrtOfPow.At(q, m), real_pow.OfNumPow.At(size, m)))))
	}),
})}
