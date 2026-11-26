// psi_series.go — the Dirichlet series of ψ(n)/n − 1. Partial summation
// writes the series of ψ(n)/n as D(Λ, s)/s plus a correction series that is
// holomorphic on Re s > 0; D(Λ, s) and ζ have the same pole at 1, so the
// series of ψ(n)/n − 1 continues holomorphically to an open set containing
// Re s ≥ 1, and by Newman's theorem it converges at s = 1.

package prime_asymptotics

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/complex/riemann_zeta"
	"github.com/euc-ai/xugo/library/proofs/complex/tauberian"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PsiCorrectionTermBound — for s ≠ 0 with Re s ≥ −2, a linear bound
// ψ(n + 1) ≤ C·(n + 1) bounds the shifted correction term by C times |s + 1|
// times the power with exponent −Re s − 1: the tangent remainder bound of
// the power at s + 1 bounds the bracket by |s + 1| times the power with
// exponent −Re s − 2, and the factor n + 1 of the linear bound raises that
// exponent by one.
var PsiCorrectionTermBound = psiCorrectionTermBoundThm{family.Add(registry.ProofEntry{
	Name: "PsiCorrectionTermBound",
	Key:  "prop_d36595f8e30527bb",
	Build: family.Theorem(Statement{
		Binders: "∀s:complex. ∀n:num. ∀C:real.",
		Hypotheses: []string{
			"-&2 ≤ re(s)",
			"s ≠ complex_of_real(&0)",
			"chebyshev_psi(n + 1) ≤ C * &(n + 1)",
		},
		Conclusion: "|«correctionTerm»(s, n)| ≤ C * |s + complex_of_real(&1)| * «correctionPower»(s, n)",
		Abbrev: Abbrev{
			{Name: "extraDecay", Text: "λs:complex. λn:num. real_rpow(&(n + 1), -re(s) - &2)"},
			{Name: "bracketMajorant", Text: "λs:complex. λn:num. " +
				"    |s + complex_of_real(&1)| * «extraDecay»(s, n)"},
		},
	}, func(
		a *Argument,
		s *Expr[Complex],
		n *Expr[Nat],
		C *Expr[Real],
		realPart, nonzero, linearBound Fact,
	) {
		one := a.TermAs[Real]("&1")
		oneComplex := a.TermAs[Complex]("complex_of_real(&1)")
		sShift := a.TermAs[Complex]("s + complex_of_real(&1)")
		index := a.TermAs[Nat]("n + 1")
		indexReal := a.TermAs[Real]("&(n + 1)")
		bracket := a.TermAs[Complex]("«correctionBracket»(s, n)")
		size := a.TermAs[Real]("|«correctionBracket»(s, n)|")
		majorant := a.TermAs[Real]("«bracketMajorant»(s, n)")

		applies := a.Have(
			"the tangent remainder bound applies at s + 1, whose "+
				"real part is at least −1, and at the index n + 1",
			"-&1 ≤ re(s + complex_of_real(&1)) ∧ 0 < n + 1",
			ByArith(realPart, complex_field.PartsAdd.At(s, oneComplex), complex_field.PartsOfReal.At(one)))
		exponents := a.Have(
			"at s + 1 its exponents s' − 1, −s' and 1 − s' are s, −s − 1 and −s, its next base n + 2",
			"(s + complex_of_real(&1)) - complex_of_real(&1) = s ∧ "+
				"-(s + complex_of_real(&1)) = -s - complex_of_real(&1) ∧ "+
				"complex_of_real(&1) - (s + complex_of_real(&1)) = -s ∧ "+
				"n + 1 + 1 = n + 2",
			ByArith())
		decayExponent := a.Have(
			"and its decay exponent −Re(s + 1) − 1 is −Re s − 2",
			"-re(s + complex_of_real(&1)) - &1 = -re(s) - &2",
			ByArith(complex_field.PartsAdd.At(s, oneComplex), complex_field.PartsOfReal.At(one)))
		zetaBound := a.Have(
			"the tangent remainder bound at s + 1 and index n + 1 bounds s times the bracket",
			"|s * «shiftedPower»(s, n) - «powerDifference»(s, n)| ≤ "+
				"|s| * |s + complex_of_real(&1)| * «extraDecay»(s, n)",
			By(applies, exponents, decayExponent, complex_cpow.CpowTangentRemainderBound.At(sShift, index)))
		positiveAbs := a.Have(
			"the modulus of s is positive",
			"&0 < |s|",
			ByArith(nonzero, complex_abs.AbsEqZero.At(s), complex_abs.AbsNonneg.At(s)))
		product := a.Have(
			"multiplication by s removes the denominator",
			"s * «correctionBracket»(s, n) = s * «shiftedPower»(s, n) - «powerDifference»(s, n)",
			Simp(Fwd(complex_field.ComplexDivDef)),
			ByArith(nonzero, At(field.MulRightInverse.Read(complex_field.Field), s)))
		scaledBracket := a.Have(
			"take the modulus of the product with s",
			"|s| * |«correctionBracket»(s, n)| ≤ |s| * «bracketMajorant»(s, n)",
			ByArith(product, zetaBound, complex_abs.AbsMul.At(s, bracket)))
		bracketBound := a.Have(
			"cancel the positive modulus of s",
			"|«correctionBracket»(s, n)| ≤ «bracketMajorant»(s, n)",
			By(
				positiveAbs,
				scaledBracket,
				real_order_ring.LessEqCancelMulLeft.At(a.TermAs[Real]("|s|"), size, majorant)))
		psi := a.TermAs[Real]("chebyshev_psi(n + 1)")
		termModulus := a.Have(
			"multiplication by the nonnegative ψ scales the modulus",
			"|«correctionTerm»(s, n)| = chebyshev_psi(n + 1) * |«correctionBracket»(s, n)|",
			ByArith(prime_distribution.PsiNonneg.At(index)))
		linear := a.Have(
			"the linear bound on ψ multiplies the bracket estimate",
			"|«correctionTerm»(s, n)| ≤ (C * &(n + 1)) * «bracketMajorant»(s, n)",
			By(
				prime_distribution.PsiNonneg.At(index),
				bracketBound,
				termModulus,
				complex_abs.AbsNonneg.At(bracket),
				linearBound,
				real_order_ring.LessEqMul2.At(psi, a.TermAs[Real]("C * &(n + 1)"), size, majorant)))
		decay := a.Have(
			"the linear factor adds one to the exponent of the power",
			"&(n + 1) * «extraDecay»(s, n) = «correctionPower»(s, n)",
			ByArith(
				real_order_ring.OfNumLessThan.At(a.TermAs[Nat]("0"), index),
				real_rpow.RpowAdd.At(indexReal, one, a.TermAs[Real]("-re(s) - &2")),
				real_rpow.RpowOneExponent.At(indexReal)))
		a.Show(
			"collect the power and the constant in the term estimate",
			ByArith(
				linear,
				Scaled(a.TermAs[Real]("C * |s + complex_of_real(&1)|"), decay),
				complex_abs.AbsNonneg.At(sShift)))
	}),
})}

// PsiCorrectionSums — for Re s > 0 the correction series converges to
// «correction»(s).
var PsiCorrectionSums = psiCorrectionSumsThm{family.Add(registry.ProofEntry{
	Name: "PsiCorrectionSums",
	Key:  "prop_7b9561bdffa41ea7",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&0 < re(s)"},
		Conclusion: "complex_sums(«correctionTerm»(s), «correction»(s))",
		Abbrev: Abbrev{
			{Name: "correctionMajorant", Text: "λs:complex. λn:num. " +
				"    &5 * |s + complex_of_real(&1)| * «correctionPower»(s, n)"},
		},
	}, func(a *Argument, s *Expr[Complex], right Fact) {
		powers := a.TermAs[Fun[Nat, Real]]("«correctionPower»(s)")
		majorant := a.TermAs[Fun[Nat, Real]]("«correctionMajorant»(s)")
		terms := a.TermAs[Fun[Nat, Complex]]("«correctionTerm»(s)")
		scale := a.TermAs[Real]("&5 * |s + complex_of_real(&1)|")
		exponent := a.Have(
			"the exponent of the power has real part less than minus one",
			"&1 < re(s) + &1",
			ByArith(right))
		t, powerSum := a.UnpackAs[Real](
			GroupPremises(exponent, real_rpow.RpowSeriesConverges.At(a.TermAs[Real]("re(s) + &1"))),
			"t")
		scaled := a.Have(
			"scale the power series to obtain the summable majorant",
			"real_sums(«correctionMajorant»(s), &5 * |s + complex_of_real(&1)| * t)",
			By(powerSum, real_series.SumsScale.At(powers, t, scale)))
		compared := a.Have(
			"the majorant bounds the moduli of the correction terms",
			"∀n:num. |«correctionTerm»(s, n)| ≤ «correctionMajorant»(s, n)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"read the term estimate at Chebyshev's linear bound ψ(n + 1) ≤ 5(n + 1)",
					ByArith(
						right,
						complex_field.PartsOfReal.At(b.TermAs[Real]("&0")),
						prime_distribution.PsiLinearBound.At(b.TermAs[Nat]("n + 1")),
						PsiCorrectionTermBound.At(s, n, b.TermAs[Real]("&5"))))
			}))
		exists := a.Have(
			"comparison with the summable majorant yields a complex sum",
			"∃v:complex. complex_sums(«correctionTerm»(s), v)",
			By(
				compared,
				scaled,
				complex_series.Comparison.At(
					terms, majorant, a.TermAs[Real]("&5 * |s + complex_of_real(&1)| * t"))))
		a.Show(
			"the correction is the selected sum of this series",
			By(exists))
	}),
	Reading: "The series is indexed from n = 1 by the shift n + 1.",
})}

// PsiCorrectionHolomorphic — «correction» is holomorphic on Re s > 0. Each
// term of its series is holomorphic there, and the term bound
// (PsiCorrectionTermBound) at Chebyshev's ψ(n + 1) ≤ 5(n + 1) puts the n-th
// term at most 5·(|s| + 1)²·(n + 1)^(−Re s − 1), so the series has a
// holomorphic sum (DominatedSeriesHolomorphic), which is the correction.
var PsiCorrectionHolomorphic = psiCorrectionHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "PsiCorrectionHolomorphic",
	Key:  "prop_46dcea4aa82bb5ed",
	Build: family.Theorem(Statement{
		Conclusion: "holomorphic_on({s:complex | &0 < re(s)}, «correction»)",
		Abbrev: Abbrev{
			{Name: "power", Text: "λx:real. λw:complex. complex_cpow(complex_of_real(x), w)"},
		},
	}, func(a *Argument) {
		S := a.TermAs[Set[Complex]]("«halfPlane»")
		universe := a.TermAs[Set[Complex]]("𝕌")
		one := a.TermAs[Complex]("complex_of_real(&1)")
		five := a.TermAs[Real]("&5")
		id := a.TermAs[Fun[Complex, Complex]]("λw:complex. w")
		neg := a.TermAs[Fun[Complex, Complex]]("λw:complex. -w")
		shiftedNeg := a.TermAs[Fun[Complex, Complex]]("λw:complex. -w - complex_of_real(&1)")
		open := complex_topology.RightHalfPlaneOpen.At(a.TermAs[Real]("&0"))
		nonzero := a.Have(
			"the half-plane excludes the pole of division by w",
			"∀w:complex. w ∈ «halfPlane» ⇒ w ≠ complex_of_real(&0)",
			Derive(func(b *Argument) {
				b.FixAs[Complex]()
				member := b.Assume()
				b.Show(
					"zero has real part zero",
					ByArith(member, complex_field.PartsOfReal.At(b.TermAs[Real]("&0"))))
			}))
		negation := a.Have(
			"negation is holomorphic",
			"holomorphic_on(«halfPlane», λw:complex. -w)",
			By(complex_derivative.HolomorphicOnId.At(S), complex_derivative.HolomorphicOnNeg.At(S, id)))
		translated := a.Have(
			"translating negation by a constant preserves holomorphy",
			"holomorphic_on(«halfPlane», λw:complex. -w - complex_of_real(&1))",
			By(
				negation,
				complex_derivative.HolomorphicOnConst.At(S, one),
				complex_derivative.HolomorphicOnSub.At(
					S, neg, a.TermAs[Fun[Complex, Complex]]("λw:complex. complex_of_real(&1)"))))
		shiftedPowers := a.Have(
			"composing with the affine exponents makes both shifted powers holomorphic",
			Statement{
				Binders:    "∀x:real.",
				Hypotheses: []string{"&0 < x"},
				Conclusion: "holomorphic_on(«halfPlane», λw:complex. «power»(x, -w)) ∧ " +
					"holomorphic_on(«halfPlane», λw:complex. «power»(x, -w - complex_of_real(&1)))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Real]()
				positive := b.Assume()
				power := b.TermAs[Fun[Complex, Complex]]("«power»(x)")
				b.Show(
					"both affine exponents take values in the domain of the entire power",
					By(
						positive,
						complex_cpow.CpowHolomorphicExponent.At(x),
						negation,
						translated,
						set_basic.InUniv.Inst[Complex](),
						complex_derivative.HolomorphicOnCompose.At(S, universe, power, neg),
						complex_derivative.HolomorphicOnCompose.At(S, universe, power, shiftedNeg),
						functions.ComposeApply))
			}))
		terms := a.Have(
			"each summand is holomorphic on the half-plane",
			"∀n:num. holomorphic_on(«halfPlane», λw:complex. «correctionTerm»(w, n))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				shifted := b.TermAs[Fun[Complex, Complex]]("λw:complex. «shiftedPower»(w, n)")
				difference := b.TermAs[Fun[Complex, Complex]]("λw:complex. «powerDifference»(w, n)")
				quotient := b.TermAs[Fun[Complex, Complex]]("λw:complex. «powerDifference»(w, n) / w")
				bracket := b.TermAs[Fun[Complex, Complex]]("λw:complex. «correctionBracket»(w, n)")
				psi := b.TermAs[Complex]("complex_of_real(chebyshev_psi(n + 1))")
				parts := b.Have(
					"take powers at the two positive bases, then take their difference",
					"holomorphic_on(«halfPlane», λw:complex. «shiftedPower»(w, n)) ∧ "+
						"holomorphic_on(«halfPlane», λw:complex. «powerDifference»(w, n))",
					ByArith(
						shiftedPowers.At(b.TermAs[Real]("&(n + 1)")),
						shiftedPowers.At(b.TermAs[Real]("&(n + 2)")),
						complex_derivative.HolomorphicOnSub.At(
							S,
							b.TermAs[Fun[Complex, Complex]]("λw:complex. «power»(&(n + 1), -w)"),
							b.TermAs[Fun[Complex, Complex]]("λw:complex. «power»(&(n + 2), -w)"))))
				divided := b.Have(
					"divide by the identity, which never vanishes here",
					"holomorphic_on(«halfPlane», λw:complex. «powerDifference»(w, n) / w)",
					By(
						parts,
						nonzero,
						complex_derivative.HolomorphicOnId.At(S),
						complex_derivative.HolomorphicOnDiv.At(S, difference, id)))
				b.Show(
					"subtract the quotient and multiply by the constant coefficient",
					By(
						parts,
						divided,
						complex_derivative.HolomorphicOnSub.At(S, shifted, quotient),
						complex_derivative.HolomorphicOnConst.At(S, psi),
						complex_derivative.HolomorphicOnMul.At(S,
							b.TermAs[Fun[Complex, Complex]]("λw:complex. complex_of_real(chebyshev_psi(n + 1))"), bracket)))
			}))
		bounded := a.Have(
			"on the half-plane the n-th term is at most 5·(|w| + 1)²·(n + 1)^(−Re w − 1)",
			Statement{
				Binders:    "∀n:num. ∀w:complex.",
				Hypotheses: []string{"&0 < re(w)"},
				Conclusion: "|«correctionTerm»(w, n)| ≤ " +
					"&5 * (|w| + &1) * (|w| + &1) * real_rpow(&(n + 1), -re(w) - &1)",
			},
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				w := b.FixAs[Complex]()
				right := b.Assume()
				termBound := b.Have(
					"the term estimate at Chebyshev's linear bound ψ(n + 1) ≤ 5(n + 1)",
					"|«correctionTerm»(w, n)| ≤ &5 * |w + complex_of_real(&1)| * «correctionPower»(w, n)",
					ByArith(
						right,
						complex_field.PartsOfReal.At(b.TermAs[Real]("&0")),
						prime_distribution.PsiLinearBound.At(b.TermAs[Nat]("n + 1")),
						PsiCorrectionTermBound.At(w, n, five)))
				power := b.Have(
					"its power has exponent −(Re w + 1), which is −Re w − 1",
					"«correctionPower»(w, n) = real_rpow(&(n + 1), -re(w) - &1)",
					ByArith())
				scale := b.Have(
					"|w + 1| is at most |w| + 1, which is at most its square",
					"|w + complex_of_real(&1)| ≤ (|w| + &1) * (|w| + &1)",
					ByArith(complex_abs.AbsTriangle.At(w, one), complex_abs.AbsNonneg.At(w)))
				b.Show(
					"and the power is nonnegative, so its product with |w + 1| is at most its product with (|w| + 1)²",
					ByArith(
						termBound,
						power,
						scale,
						real_order_ring.LessEqMulRight.At(
							b.TermAs[Real]("|w + complex_of_real(&1)|"),
							b.TermAs[Real]("(|w| + &1) * (|w| + &1)"),
							b.TermAs[Real]("real_rpow(&(n + 1), -re(w) - &1)")),
						real_rpow.RpowNonneg.At(b.TermAs[Real]("&(n + 1)"), b.TermAs[Real]("-re(w) - &1"))))
			}))
		F, sums := a.ObtainAs[Fun[Complex, Complex]](
			"the dominated series has a holomorphic sum",
			"∃F:(complex → complex). "+
				"    (∀w:complex. &0 < re(w) ⇒ complex_sums(«correctionTerm»(w), F(w))) ∧ "+
				"    holomorphic_on(«halfPlane», F)",
			By(
				terms,
				bounded,
				dirichlet_series.DominatedSeriesHolomorphic.At(
					a.TermAs[Fun2[Nat, Complex, Complex]]("λn:num. λw:complex. «correctionTerm»(w, n)"), five)))
		parts := a.Conjuncts(
			sums,
			"the pointwise series sums to F",
			"F is holomorphic")
		agree := a.Have(
			"uniqueness of the series sum identifies the correction with F",
			"∀w:complex. w ∈ «halfPlane» ⇒ «correction»(w) = F(w)",
			Derive(func(b *Argument) {
				w := b.FixAs[Complex]()
				member := b.Assume()
				b.Show(
					"both values sum the same series at this point",
					By(
						member,
						parts[0].At(w),
						PsiCorrectionSums.At(w),
						complex_series.SumsUnique.At(b.TermAs[Fun[Nat, Complex]]("«correctionTerm»(w)"),
							b.TermAs[Complex]("«correction»(w)"), b.TermAs[Complex]("F(w)"))))
			}))
		a.Show(
			"transfer holomorphy by agreement on the open half-plane",
			By(
				open,
				parts[1],
				agree,
				complex_derivative.HolomorphicOnAgree.At(S, a.TermAs[Fun[Complex, Complex]]("«correction»"), F)))
	}),
})}

// PsiSeriesIdentity — for Re s > 1 the Dirichlet series of ψ(n)/n converges,
// and its sum is the series of Λ divided by s, plus the correction.
var PsiSeriesIdentity = psiSeriesIdentityThm{family.Add(registry.ProofEntry{
	Name: "PsiSeriesIdentity",
	Key:  "prop_ac0e8f4371d4419a",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&1 < re(s)"},
		Conclusion: "dirichlet_sums(λn:num. complex_of_real(chebyshev_psi(n) / &n), " +
			"    s, " +
			"    dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)), s) / s + «correction»(s))",
		Abbrev: Abbrev{
			{Name: "psi", Text: "λn:num. complex_of_real(chebyshev_psi(n))"},
			{Name: "weight", Text: "λs:complex. λn:num. complex_cpow(complex_of_real(&n), -s)"},
			{Name: "delta", Text: "λs:complex. λn:num. «psi»(n) * («weight»(s, n) - «weight»(s, n + 1))"},
			{Name: "deltaShift", Text: "λs:complex. λn:num. «delta»(s, n + 1)"},
			{Name: "psiTerm", Text: "λs:complex. λn:num. «psiRatio»(n + 1) * «weight»(s, n + 1)"},
			{Name: "mangoldtWeight", Text: "λs:complex. λn:num. «mangoldt»(n) * «weight»(s, n)"},
			{Name: "mangoldtTerm", Text: "λs:complex. λn:num. «mangoldtWeight»(s, n + 1)"},
			{Name: "tailTerm", Text: "λs:complex. λn:num. «psi»(n + 1) * «weight»(s, n + 2)"},
			{Name: "majorantPower", Text: "λs:complex. λn:num. real_rpow(&(n + 1), -(re(s) - &1))"},
			{Name: "mangoldtPartial", Text: "λs:complex. λn:num. Σ_{k∈0 .. n} «mangoldtTerm»(s, k)"},
			{Name: "deltaPartial", Text: "λs:complex. λn:num. Σ_{k∈0 .. n} «deltaShift»(s, k)"},
		},
	}, func(a *Argument, s *Expr[Complex], right Fact) {
		zero := a.TermAs[Nat]("0")
		one := a.TermAs[Nat]("1")
		zeroComplex := a.TermAs[Complex]("complex_of_real(&0)")
		oneReal := a.TermAs[Real]("&1")
		negS := a.TermAs[Complex]("-s")
		complexAddition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
		inverse := At(field.MulRightInverse.Read(complex_field.Field), s)
		nonzero := a.Have(
			"s has positive real part, so it is nonzero",
			"s ≠ complex_of_real(&0)",
			ByArith(right, complex_field.PartsOfReal.At(a.TermAs[Real]("&0"))))
		bounded := a.Have(
			"the linear bound on ψ bounds the Dirichlet coefficients ψ(n)/n",
			"∀n:num. |«psiRatio»(n)| ≤ &5",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				b.Show(
					"the modulus of the embedded quotient is the quotient, which lies between 0 and 5",
					ByArith(prime_distribution.PsiRatioBound.At(n)))
			}))
		psiRatios := a.TermAs[Fun[Nat, Complex]]("«psiRatio»")
		mangoldt := a.TermAs[Fun[Nat, Complex]]("«mangoldt»")
		v, psiSums := a.ObtainAs[Complex](
			"bounded coefficients give the Dirichlet sum of ψ(n)/n",
			"∃v:complex. dirichlet_sums(«psiRatio», s, v)",
			By(
				bounded,
				right,
				dirichlet_series.BoundedCoefficientsConverge.At(psiRatios, a.TermAs[Real]("&5"), s)))
		psiTerm := a.TermAs[Fun[Nat, Complex]]("«psiTerm»(s)")
		correction := a.TermAs[Complex]("«correction»(s)")
		correctionTerm := a.TermAs[Fun[Nat, Complex]]("«correctionTerm»(s)")
		weighted := a.Have(
			"read the sum of the shifted weighted coefficients",
			"complex_sums(«psiTerm»(s), v)",
			By(psiSums, dirichlet_series.DirichletSumsDef.At(psiRatios, s, v)))
		corrected := a.Have(
			"the correction series sums to the chosen correction value",
			"complex_sums(«correctionTerm»(s), «correction»(s))",
			ByArith(right, PsiCorrectionSums.At(s)))
		differences := a.Have(
			"subtract the correction and multiply by s to get the weighted power differences",
			"(λn:num. s * («psiTerm»(s, n) - «correctionTerm»(s, n))) = «deltaShift»(s)",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				x := b.TermAs[Real]("&(n + 1)")
				positive := b.Have(
					"the base is positive",
					"&0 < &(n + 1)",
					ByArith())
				shifted := b.Have(
					"subtracting one from the exponent multiplies by the reciprocal base",
					"complex_cpow(complex_of_real(&(n + 1)), -s - complex_of_real(&1)) = "+
						"«weight»(s, n + 1) * complex_of_real(real_inv(&(n + 1)))",
					Derive(func(d *Argument) {
						reciprocal := d.Have(
							"the power at minus one is the embedded reciprocal",
							"complex_cpow(complex_of_real(&(n + 1)), -complex_of_real(&1)) = "+
								"complex_of_real(real_inv(&(n + 1)))",
							Simp(Rev(complex_field.OfRealNeg)),
							ByArith(
								positive,
								complex_cpow.CpowRealExponent.At(x, d.TermAs[Real]("-&1")),
								real_rpow.RpowNeg.At(x, oneReal),
								real_rpow.RpowOneExponent.At(x)))
						d.Show(
							"split the exponent sum",
							Simp(Fwd(complex_field.ComplexSubDef)),
							By(
								positive,
								reciprocal,
								complex_cpow.CpowAdd.At(x, negS, d.TermAs[Complex]("-complex_of_real(&1)"))))
					}))
				next := b.Have(
					"align the second weight with the successor index",
					"n + 1 + 1 = n + 2",
					ByArith())
				b.Show(
					"the common power cancels and multiplication by s removes the denominator",
					Simp(Fwd(real_field.RealDivDef), Fwd(complex_field.ComplexDivDef)),
					Simp(Fwd(shifted), Fwd(next), Fwd(complex_field.OfRealMul)),
					ByArith(nonzero, inverse))
			}))
		deltaTerms := a.TermAs[Fun[Nat, Complex]]("«deltaShift»(s)")
		limit := a.TermAs[Complex]("s * (v - «correction»(s))")
		deltaSums := a.Have(
			"the weighted power differences sum to s times the difference of the two sums",
			"complex_sums(«deltaShift»(s), s * (v - «correction»(s)))",
			By(
				weighted,
				corrected,
				differences,
				complex_series.SumsSub.At(psiTerm, correctionTerm, v, correction),
				complex_series.SumsScale.At(
					a.TermAs[Fun[Nat, Complex]]("λn:num. «psiTerm»(s, n) - «correctionTerm»(s, n)"),
					a.TermAs[Complex]("v - «correction»(s)"),
					s)))
		deltaLimit := a.Have(
			"the partial sums of the differences converge to that value",
			"«deltaPartial»(s) ⟶ s * (v - «correction»(s))",
			By(deltaSums, complex_series.SumsIffPartialSums.At(deltaTerms, limit)))
		castPsi := a.Have(
			"the real embedding carries the partial sum of Λ to the complex partial sum",
			"∀n:num. «psi»(n) = Σ_{k∈1 .. n} «mangoldt»(k)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				b.Show(
					"ψ(n) is the real sum of Λ over the finite interval 1 .. n",
					Simp(Fwd(prime_distribution.ChebyshevPsiDef)),
					By(
						num_segment.Finite.At(one, n),
						complex_field.OfRealSum.At(b.TermAs[Set[Nat]]("1 .. n"), b.TermAs[Fun[Nat, Real]]("von_mangoldt"))))
			}))
		abel := a.Have(
			"partial summation gives the ψ boundary and the weighted differences",
			"∀N:num. "+
				"    (Σ_{k∈1 .. N} «mangoldtWeight»(s, k)) = "+
				"    «psi»(N) * «weight»(s, N + 1) + (Σ_{k∈1 .. N} «delta»(s, k))",
			Derive(func(b *Argument) {
				N := b.FixAs[Nat]()
				b.Show(
					"the cumulative complex Mangoldt sums are the embedded ψ values",
					Simp(Fwd(castPsi)),
					By(dirichlet_series.DirichletPartialSummation.At(mangoldt, s, N)))
			}))
		shiftedAbel := a.Have(
			"shift both finite sums to the series index starting at zero",
			"∀n:num. «mangoldtPartial»(s, n) = «tailTerm»(s, n) + «deltaPartial»(s, n)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				shift := monoidal.Shift.Read(complexAddition)
				indices := b.Have(
					"align the shifted endpoints",
					"0 + 1 = 1 ∧ n + 1 + 1 = n + 2",
					ByArith())
				mangoldtReindexed := b.Have(
					"read the shifted weighted Mangoldt sum",
					"«mangoldtPartial»(s, n) = Σ_{k∈1 .. n + 1} «mangoldtWeight»(s, k)",
					By(shift.At(zero, n, one, b.TermAs[Fun[Nat, Complex]]("«mangoldtWeight»(s)"))))
				deltaReindexed := b.Have(
					"read the shifted weighted difference sum",
					"«deltaPartial»(s, n) = Σ_{k∈1 .. n + 1} «delta»(s, k)",
					By(shift.At(zero, n, one, b.TermAs[Fun[Nat, Complex]]("«delta»(s)"))))
				b.Show(
					"evaluate the finite partial summation at n plus one",
					By(indices, mangoldtReindexed, deltaReindexed, abel.At(b.TermAs[Nat]("n + 1"))))
			}))
		tailBound := a.Have(
			"the boundary is bounded by five times the majorant power at n + 1",
			"∀n:num. |«tailTerm»(s, n)| ≤ &5 * «majorantPower»(s, n + 1)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				next := b.TermAs[Nat]("n + 1")
				x := b.TermAs[Real]("&(n + 2)")
				exponent := b.TermAs[Real]("-re(s)")
				psi := b.TermAs[Real]("chebyshev_psi(n + 1)")
				positive := b.Have(
					"the real base is positive",
					"&0 < &(n + 2) ∧ &0 ≤ &(n + 2)",
					ByArith())
				base := b.Have(
					"the majorant power at n + 1 has base n + 2",
					"n + 1 + 1 = n + 2",
					ByArith())
				modulus := b.Have(
					"the boundary modulus is ψ times the real power",
					"|«tailTerm»(s, n)| = chebyshev_psi(n + 1) * real_rpow(&(n + 2), -re(s))",
					By(
						positive,
						prime_distribution.PsiNonneg.At(next),
						complex_abs.AbsMul.At(b.TermAs[Complex]("«psi»(n + 1)"), b.TermAs[Complex]("«weight»(s, n + 2)")),
						complex_abs.AbsOfNonnegReal.At(psi),
						complex_cpow.AbsCpow.At(x, negS),
						complex_field.PartsNeg.At(s)))
				power := b.Have(
					"multiplication by the base raises the exponent by one",
					"&(n + 2) * real_rpow(&(n + 2), -re(s)) = real_rpow(&(n + 2), -(re(s) - &1))",
					ByArith(positive, real_rpow.RpowAdd.At(x, oneReal, exponent), real_rpow.RpowOneExponent.At(x)))
				b.Show(
					"the linear bound on ψ is at most five times the base",
					ByArith(
						positive,
						base,
						modulus,
						power,
						prime_distribution.PsiLinearBound.At(next),
						real_rpow.RpowPositive.At(x, exponent)))
			}))
		tailLimit := a.Have(
			"the boundary tends to zero, being at most five times a shifted power that does",
			"«tailTerm»(s) ⟶ complex_of_real(&0)",
			Derive(func(b *Argument) {
				zero := b.TermAs[Real]("&0")
				five := b.TermAs[Real]("&5")
				majorant := b.TermAs[Fun[Nat, Real]]("«majorantPower»(s)")
				shifted := b.TermAs[Fun[Nat, Real]]("λn:num. «majorantPower»(s, n + 1)")
				powerLimit := b.Have(
					"the real majorant power tends to zero because the real-part gap is positive",
					"«majorantPower»(s) ⟶ &0",
					ByArith(right, real_rpow.RpowNegTendsToZero.At(b.TermAs[Real]("re(s) - &1"))))
				boundLimit := b.Have(
					"so does five times its shift by one",
					"(λn:num. &5 * «majorantPower»(s, n + 1)) ⟶ &0",
					By(
						powerLimit,
						real_sequences.LimitShift.At(majorant, zero),
						real_sequences.LimitScale.At(shifted, zero, five),
						real_ring.MulRightZero.At(five)))
				b.Show(
					"the bound squeezes the boundary to zero",
					By(
						tailBound,
						boundLimit,
						complex_topology.LimitSqueezeZero.At(
							b.TermAs[Fun[Nat, Complex]]("«tailTerm»(s)"),
							b.TermAs[Fun[Nat, Real]]("λn:num. &5 * «majorantPower»(s, n + 1)"))))
			}))
		partialEq := a.Have(
			"the sequence of Mangoldt partial sums is the sum of the two sequences",
			"(λn:num. «tailTerm»(s, n) + «deltaPartial»(s, n)) = «mangoldtPartial»(s)",
			Funext(),
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]()
				b.Show(
					"apply the finite identity at each index",
					By(shiftedAbel.At(n)))
			}))
		mangoldtLimit := a.Have(
			"take limits in the shifted partial summation",
			"«mangoldtPartial»(s) ⟶ s * (v - «correction»(s))",
			ByArith(
				tailLimit,
				deltaLimit,
				partialEq,
				complex_topology.LimitAdd.At(
					a.TermAs[Fun[Nat, Complex]]("«tailTerm»(s)"), a.TermAs[Fun[Nat, Complex]]("«deltaPartial»(s)"),
					zeroComplex, limit)))
		mangoldtSums := a.Have(
			"the shifted partial sums give the Dirichlet sum of Λ",
			"dirichlet_sums(«mangoldt», s, s * (v - «correction»(s)))",
			By(
				mangoldtLimit,
				complex_series.SumsIffPartialSums.At(a.TermAs[Fun[Nat, Complex]]("«mangoldtTerm»(s)"), limit),
				dirichlet_series.DirichletSumsDef.At(mangoldt, s, limit)))
		value := a.Have(
			"so the series of Λ has the value s times the difference of the two sums",
			"dirichlet_series(«mangoldt», s) = s * (v - «correction»(s))",
			By(mangoldtSums, dirichlet_series.DirichletSeriesValue.At(mangoldt, s, limit)))
		recovered := a.Have(
			"divide by the nonzero s and add back the correction",
			"v = dirichlet_series(«mangoldt», s) / s + «correction»(s)",
			Simp(Fwd(value)),
			Simp(Fwd(complex_field.ComplexDivDef)),
			ByArith(nonzero, inverse))
		a.Show(
			"the series of ψ(n)/n sums to that value",
			By(Normalized, psiSums, recovered))
	}),
	Reading: "ψ is the partial-sum function of Λ: this is partial summation carried to the limit.",
})}

// PsiSeriesContinuation — the Dirichlet series of ψ(n)/n − 1 continues
// holomorphically to an open set containing Re s ≥ 1.
var PsiSeriesContinuation = psiSeriesContinuationThm{family.Add(registry.ProofEntry{
	Name: "PsiSeriesContinuation",
	Key:  "prop_ee94da12c2cd3bf7",
	Build: family.Theorem(Statement{
		Conclusion: "∃U:set(complex). ∃F:(complex → complex). " +
			"    U ∈ complex_topology ∧ " +
			"    (∀s:complex. &1 ≤ re(s) ⇒ s ∈ U) ∧ " +
			"    holomorphic_on(U, F) ∧ " +
			"    ∀s:complex. " +
			"        &1 < re(s) ⇒ dirichlet_sums(λn:num. complex_of_real(chebyshev_psi(n) / &n - &1), s, F(s))",
		Abbrev: Abbrev{
			{Name: "regular", Text: "λg:(complex → complex). λk:(complex → complex). λs:complex. " +
				"    (g(s) - complex_of_real(&1)) / s + «correction»(s) - k(s)"},
			{Name: "ones", Text: "λn:num. complex_of_real(&1)"},
		},
	}, func(a *Argument) {
		S := a.TermAs[Set[Complex]]("«halfPlane»")
		one := a.TermAs[Complex]("complex_of_real(&1)")
		oneReal := a.TermAs[Real]("&1")
		zeroReal := a.TermAs[Real]("&0")
		U, g, mangoldtData := a.Obtain2As[Set[Complex], Fun[Complex, Complex]](
			"continue the Mangoldt series after removing its simple pole",
			"∃U:set(complex). ∃g:(complex → complex). "+
				"    U ∈ complex_topology ∧ "+
				"    (∀s:complex. &1 ≤ re(s) ⇒ s ∈ U) ∧ "+
				"    holomorphic_on(U, g) ∧ "+
				"    ∀s:complex. "+
				"        &1 < re(s) ⇒ "+
				"        dirichlet_series(«mangoldt», s) = complex_inv(s - complex_of_real(&1)) + g(s)",
			By(riemann_zeta.MangoldtSeriesContinuation))
		mangoldt := a.Conjuncts(
			mangoldtData,
			"U is open",
			"U contains Re s at least one",
			"g is holomorphic",
			"g is the Mangoldt remainder")
		k, zetaData := a.ObtainAs[Fun[Complex, Complex]](
			"continue zeta after removing its simple pole",
			"∃k:(complex → complex). "+
				"    holomorphic_on(«halfPlane», k) ∧ "+
				"    ∀s:complex. "+
				"        &0 < re(s) ∧ s ≠ complex_of_real(&1) ⇒ "+
				"        riemann_zeta(s) = complex_inv(s - complex_of_real(&1)) + k(s)",
			By(riemann_zeta.ZetaContinuation))
		zeta := a.Conjuncts(
			zetaData,
			"k is holomorphic",
			"k is the zeta remainder")
		V := a.TermAs[Set[Complex]]("U ∩ «halfPlane»")
		F := a.TermAs[Fun[Complex, Complex]]("«regular»(g, k)")
		halfOpen := complex_topology.RightHalfPlaneOpen.At(zeroReal)
		open := a.Have(
			"intersect the two open domains",
			"U ∩ «halfPlane» ∈ complex_topology",
			By(
				halfOpen,
				mangoldt[0],
				topological_space.InterOpen.Read(complex_topology.ComplexTopology).AsFact().At(U, S)))
		containing := a.Have(
			"the intersection still contains all points with real part at least one",
			"∀s:complex. &1 ≤ re(s) ⇒ s ∈ U ∩ «halfPlane»",
			Derive(func(b *Argument) {
				s := b.FixAs[Complex]()
				right := b.Assume()
				both := b.Have(
					"the point belongs to U and has positive real part",
					"&0 < re(s) ∧ s ∈ U",
					ByArith(right, mangoldt[1].At(s)))
				b.Show(
					"read membership in the intersection",
					BySets(both))
			}))
		nonzero := a.Have(
			"the new domain excludes zero",
			"∀s:complex. s ∈ U ∩ «halfPlane» ⇒ s ≠ complex_of_real(&0)",
			Derive(func(b *Argument) {
				b.FixAs[Complex]()
				inside := b.Assume()
				positive := b.Have(
					"the real part is positive",
					"&0 < re(s)",
					BySets(inside))
				b.Show(
					"zero has real part zero",
					ByArith(positive, complex_field.PartsOfReal.At(zeroReal)))
			}))
		subsets := a.Have(
			"the common domain lies in the two original domains",
			"U ∩ «halfPlane» ⊆ U ∧ U ∩ «halfPlane» ⊆ «halfPlane»",
			BySets())
		correction := a.TermAs[Fun[Complex, Complex]]("«correction»")
		restricted := a.Have(
			"restrict all three holomorphic functions to the common domain",
			"holomorphic_on(U ∩ «halfPlane», g) ∧ "+
				"holomorphic_on(U ∩ «halfPlane», k) ∧ "+
				"holomorphic_on(U ∩ «halfPlane», «correction»)",
			By(
				subsets,
				mangoldt[2],
				zeta[0],
				PsiCorrectionHolomorphic,
				complex_derivative.HolomorphicOnSubset.At(U, V, g),
				complex_derivative.HolomorphicOnSubset.At(S, V, k),
				complex_derivative.HolomorphicOnSubset.At(S, V, correction)))
		quotient := a.TermAs[Fun[Complex, Complex]]("λs:complex. (g(s) - complex_of_real(&1)) / s")
		divided := a.Have(
			"the shifted Mangoldt remainder can be divided by s on this domain",
			"holomorphic_on(U ∩ «halfPlane», λs:complex. (g(s) - complex_of_real(&1)) / s)",
			By(
				restricted,
				nonzero,
				complex_derivative.HolomorphicOnConst.At(V, one),
				complex_derivative.HolomorphicOnSub.At(
					V, g, a.TermAs[Fun[Complex, Complex]]("λs:complex. complex_of_real(&1)")),
				complex_derivative.HolomorphicOnId.At(V),
				complex_derivative.HolomorphicOnDiv.At(
					V,
					a.TermAs[Fun[Complex, Complex]]("λs:complex. g(s) - complex_of_real(&1)"),
					a.TermAs[Fun[Complex, Complex]]("λs:complex. s"))))
		holomorphic := a.Have(
			"the pole-cancelled combination is holomorphic",
			"holomorphic_on(U ∩ «halfPlane», «regular»(g, k))",
			By(
				restricted,
				divided,
				complex_derivative.HolomorphicOnAdd.At(V, quotient, correction),
				complex_derivative.HolomorphicOnSub.At(
					V,
					a.TermAs[Fun[Complex, Complex]]("λs:complex. (g(s) - complex_of_real(&1)) / s + «correction»(s)"),
					k)))
		agreement := a.Have(
			"to the right of one, the sum of the ψ series less ζ is the regular combination",
			Statement{
				Binders:    "∀s:complex.",
				Hypotheses: []string{"&1 < re(s)"},
				Conclusion: "dirichlet_series(«mangoldt», s) / s + " +
					"«correction»(s) + " +
					"-complex_of_real(&1) * riemann_zeta(s) = " +
					"«regular»(g, k, s)",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[Complex]()
				right := b.Assume()
				realParts := b.Have(
					"compare the real parts to those of zero and one",
					"&0 < re(s) ∧ "+
						"re(s) ≠ re(complex_of_real(&0)) ∧ "+
						"re(s) ≠ re(complex_of_real(&1)) ∧ "+
						"re(s - complex_of_real(&1)) ≠ re(complex_of_real(&0))",
					ByArith(
						right,
						complex_field.PartsOfReal.At(zeroReal),
						complex_field.PartsOfReal.At(oneReal),
						complex_field.PartsSub.At(s, one)))
				away := b.Have(
					"the right half-plane excludes both zero and the pole at one",
					"&0 < re(s) ∧ "+
						"s ≠ complex_of_real(&0) ∧ "+
						"s ≠ complex_of_real(&1) ∧ "+
						"s - complex_of_real(&1) ≠ complex_of_real(&0)",
					By(Normalized, realParts))
				continued := b.Have(
					"express the series of Λ and ζ by their regular parts and the pole",
					"dirichlet_series(«mangoldt», s) = complex_inv(s - complex_of_real(&1)) + g(s) ∧ "+
						"riemann_zeta(s) = complex_inv(s - complex_of_real(&1)) + k(s)",
					By(away, right, mangoldt[3].At(s), zeta[1].At(s)))
				cancelled := b.Have(
					"the partial fraction 1/(s − 1) = 1/s + 1/(s(s − 1))",
					"complex_inv(s - complex_of_real(&1)) = "+
						"complex_inv(s) + complex_inv(s - complex_of_real(&1)) * complex_inv(s)",
					Derive(func(d *Argument) {
						factor := d.Have(
							"multiply the pole by s using its inverse identity",
							"s * complex_inv(s - complex_of_real(&1)) = "+
								"complex_of_real(&1) + complex_inv(s - complex_of_real(&1))",
							ByArith(
								away,
								At(field.MulRightInverse.Read(complex_field.Field), d.TermAs[Complex]("s - complex_of_real(&1)"))))
						d.Show(
							"cancel s on the left",
							ByArith(
								away,
								Scaled(d.TermAs[Complex]("complex_inv(s)"), factor),
								At(field.MulRightInverse.Read(complex_field.Field), s)))
					}))
				b.Show(
					"substitute the series values and cancel the pole",
					Simp(Fwd(continued)),
					Simp(Fwd(complex_field.ComplexDivDef)),
					ByArith(cancelled))
			}))
		difference := a.Have(
			"adding −1 to the coefficients ψ(n)/n gives the centered coefficients",
			"(λn:num. «psiRatio»(n) + -complex_of_real(&1) * «ones»(n)) = «centeredRatio»",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				b.Show(
					"the real embedding respects subtraction",
					Simp(Fwd(complex_field.OfRealSub)),
					ByArith())
			}))
		psiRatios := a.TermAs[Fun[Nat, Complex]]("«psiRatio»")
		ones := a.TermAs[Fun[Nat, Complex]]("«ones»")
		minusOne := a.TermAs[Complex]("-complex_of_real(&1)")
		summed := a.Have(
			"the regular combination sums the centered series for Re s above one",
			"∀s:complex. &1 < re(s) ⇒ dirichlet_sums(«centeredRatio», s, «regular»(g, k, s))",
			Derive(func(b *Argument) {
				s := b.FixAs[Complex]()
				right := b.Assume()
				z := b.TermAs[Complex]("riemann_zeta(s)")
				v := b.TermAs[Complex]("dirichlet_series(«mangoldt», s) / s + «correction»(s)")
				negated := b.Have(
					"scaling the series of ζ by −1 gives the Dirichlet sum −ζ(s) of the coefficients −1",
					"dirichlet_sums(λn:num. -complex_of_real(&1) * «ones»(n), "+
						"    s, "+
						"    -complex_of_real(&1) * riemann_zeta(s))",
					By(
						right,
						riemann_zeta.ZetaSums.At(s),
						dirichlet_series.DirichletSumsScale.At(ones, s, z, minusOne)))
				subtracted := b.Have(
					"adding the two series subtracts ζ from the series of ψ(n)/n",
					"dirichlet_sums(λn:num. «psiRatio»(n) + -complex_of_real(&1) * «ones»(n), "+
						"    s, "+
						"    dirichlet_series(«mangoldt», s) / s + "+
						"    «correction»(s) + "+
						"    -complex_of_real(&1) * riemann_zeta(s))",
					By(
						right,
						PsiSeriesIdentity.At(s),
						negated,
						dirichlet_series.DirichletSumsAdd.At(
							psiRatios,
							b.TermAs[Fun[Nat, Complex]]("λn:num. -complex_of_real(&1) * «ones»(n)"),
							s,
							v,
							b.TermAs[Complex]("-complex_of_real(&1) * riemann_zeta(s)"))))
				b.Show(
					"the coefficients of the sum are the centered ones, and its value the regular combination",
					By(right, subtracted, agreement.At(s), difference))
			}))
		a.Take(V)
		a.Take(F)
		a.Show(
			"the open domain and the regular combination provide the continuation",
			By(open, containing, holomorphic, summed))
	}),
	Reading: "The cancellation of the two poles at 1 is the analytic " +
		"content of ψ(n) ~ n: the series of ψ(n)/n and ζ have the same pole.",
})}

// PsiSeriesConverges — the Dirichlet series of ψ(n)/n − 1 converges at s = 1:
// its coefficients are bounded, and it continues holomorphically to an open
// set containing Re s ≥ 1 (PsiSeriesContinuation), so Newman's theorem gives
// its sum at 1.
var PsiSeriesConverges = psiSeriesConvergesThm{family.Add(registry.ProofEntry{
	Name: "PsiSeriesConverges",
	Key:  "prop_52c9b276cb2f4e32",
	Build: family.Theorem(Statement{
		Conclusion: "∃v:complex. " +
			"    dirichlet_sums(λn:num. complex_of_real(chebyshev_psi(n) / &n - &1), complex_of_real(&1), v)",
	}, func(a *Argument) {
		coefficients := a.TermAs[Fun[Nat, Complex]]("«centeredRatio»")
		one := a.TermAs[Complex]("complex_of_real(&1)")
		five := a.TermAs[Real]("&5")
		bounded := a.Have(
			"the coefficients are bounded",
			"∀n:num. |«centeredRatio»(n)| ≤ &5",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"ψ(n)/n lies between 0 and 5, so its difference from 1 has modulus at most 5",
					ByArith(prime_distribution.PsiRatioBound.At(n)))
			}))
		_, _, continuation := a.Obtain2(
			"the series continues to an open set containing the closed half-plane Re s ≥ 1",
			"∃U:set(complex). ∃F:(complex → complex). "+
				"    U ∈ complex_topology ∧ "+
				"    (∀s:complex. &1 ≤ re(s) ⇒ s ∈ U) ∧ "+
				"    holomorphic_on(U, F) ∧ "+
				"    (∀s:complex. &1 < re(s) ⇒ dirichlet_sums(«centeredRatio», s, F(s)))",
			Cite(PsiSeriesContinuation))
		onBoundary := a.Have(
			"the point 1 belongs to the closed half-plane",
			"&1 ≤ re(complex_of_real(&1))",
			ByArith(complex_field.PartsOfReal.At(a.TermAs[Real]("&1"))))
		a.Show(
			"Newman's theorem gives the sum at 1",
			Witness(a.TermAs[Complex]("F(complex_of_real(&1))")),
			By(
				bounded,
				continuation,
				onBoundary,
				tauberian.NewmanTauberian.At(
					coefficients, five, a.TermAs[Set[Complex]]("U"), a.TermAs[Fun[Complex, Complex]]("F"), one)))
	}),
	Reading: "This is the discrete form of the convergence of the integral of " +
		"(ψ(x) − x)/x²: the one place the theory of ζ enters the count of primes.",
})}
