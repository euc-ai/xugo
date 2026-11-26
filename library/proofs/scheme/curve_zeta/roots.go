// roots.go — the reciprocal roots of the numerator, over the curve and over its
// constant extensions.

package curve_zeta

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/finite_spectrum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexZetaRecurrence — over ℂ too the zeta series of a smooth curve has the
// point counts as its counting sequence: the embedding of ℝ in ℂ carries the
// recurrence of the Euler product.
var ComplexZetaRecurrence = complexZetaRecurrenceThm{family.Add(registry.ProofEntry{
	Name: "ComplexZetaRecurrence",
	Key:  "prop_f197e59747174e51",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "series_recurrence(complex_ring, " +
			"    «complexZeta», " +
			"    λm:num. complex_of_real(real_of_num(«count»(m))))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		algebraicallyClosed, inField, curve Fact,
	) {
		a.Show(
			"the recurrence of the Euler product embeds in ℂ",
			By(
				algebraicallyClosed,
				inField,
				curve,
				ZetaEulerProductAndLogDerivative.Read(M).At(K, k, A0, A1, A01, t),
				complex_field.CommRingOn,
				complex_field.OfRealRingHomomorphism,
				formal_series.RecurrenceRingMap.Read(real_ring.CommRingOn).At(
					a.TermAs[module_record.RingOps[Complex]]("complex_ring"),
					a.TermAs[Fun[Real, Complex]]("complex_of_real"),
					a.TermAs[Fun[Nat, Real]]("«zeta»"),
					a.TermAs[Fun[Nat, Real]]("λm:num. real_of_num(«count»(m))"))))
	}),
})}

// ComplexZetaProduct — the rationality of the zeta series read over ℂ: the
// numerator is (1 − T)(1 − qT) times the zeta series, with the two factors in the
// reciprocal linear form the spectrum chapter states. The embedding of ℝ in ℂ
// carries a convolution to a convolution, and each real binomial 1 − rT to the
// reciprocal linear factor at r, coefficient by coefficient.
var ComplexZetaProduct = complexZetaProductThm{family.Add(registry.ProofEntry{
	Name: "ComplexZetaProduct",
	Key:  "prop_26c26d2d4831e660",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "polynomial_mul(complex_add, " +
			"    complex_of_real(&0), " +
			"    complex_mul, " +
			"    «denominator»(card(k)), " +
			"    «complexZeta») = " +
			"λn:num. complex_of_real(«numerator»(n))",
		Abbrev: Abbrev{
			{Name: "variable", Text: "basis_vector(&0, &1, 1)"},
			{Name: "binomial", Text: "λr:real. " +
				"    vec_sub(real_sub, basis_vector(&0, &1, 0), vec_scalar_mul(real_mul, r, «variable»))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		algebraicallyClosed, inField, curve Fact,
	) {
		rational := a.Have(
			"over ℝ the numerator is (1 − T)(1 − qT) times the zeta series",
			"polynomial_mul(real_add, "+
				"    &0, "+
				"    real_mul, "+
				"    polynomial_mul(real_add, &0, real_mul, «1−T», «1−qT»), "+
				"    «zeta») = "+
				"«numerator»",
			By(algebraicallyClosed, inField, curve, ZetaNumeratorRationality.Read(M).At(K, k, A0, A1, A01, t)))
		convolution := a.Have(
			"the embedding of ℝ in ℂ carries a real convolution to the complex one",
			"∀p q:(num → real). "+
				"    (λn:num. complex_of_real(polynomial_mul(real_add, &0, real_mul, p, q, n))) = "+
				"    polynomial_mul(complex_add, "+
				"        complex_of_real(&0), "+
				"        complex_mul, "+
				"        λn:num. complex_of_real(p(n)), "+
				"        λn:num. complex_of_real(q(n)))",
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[Nat, Real]]("p")
				q := b.FixAs[Fun[Nat, Real]]("q")
				b.Show(
					"the embedding is a ring homomorphism and every real lies in ℝ's carrier",
					By(
						set_basic.InUniv.Inst[Real](),
						complex_field.CommRingOn,
						complex_field.OfRealRingHomomorphism,
						polynomial.ConvolutionRingMap.Read(real_ring.CommRingOn).At(
							b.TermAs[module_record.RingOps[Complex]]("complex_ring"),
							b.TermAs[Fun[Real, Complex]]("complex_of_real"),
							p,
							q)))
			}))
		binomial := a.Have(
			"a real binomial 1 − rT embeds as the reciprocal linear factor at r",
			"∀r:real. (λn:num. complex_of_real(«binomial»(r, n))) = «linearFactor»(complex_of_real(r))",
			Derive(func(b *Argument) {
				b.FixAs[Real]("r")
				b.Do(Funext())
				b.FixAs[Nat]("n")
				b.Do(Simp(
					Fwd(vec_space.VecSubDef),
					Fwd(vec_space.VecScalarMulDef),
					Fwd(vec_space.BasisVectorDef),
					Fwd(complex_field.OfRealSub),
					Fwd(complex_field.OfRealMul)))
				notZero := b.Unless(
					b.TermAs[Bool]("n = 0"),
					"the constant coefficients are both one",
					Given(func(c *Argument, isZero Fact) {
						c.Do(ByArith(isZero))
					}))
				notOne := b.Unless(
					b.TermAs[Bool]("n = 1"),
					"the linear coefficients are both −r",
					Given(func(c *Argument, isOne Fact) {
						c.Do(ByArith(notZero, isOne))
					}))
				b.Show(
					"all higher coefficients vanish",
					ByArith(notZero, notOne))
			}))
		first := a.Simplified(
			binomial.At(a.TermAs[Real]("&1")),
			Fwd(vec_space.SmulOne.Read(real_ring.CommRing)))
		denominator := a.Have(
			"so the denominator is the embedded real polynomial (1 − T)(1 − qT)",
			"«denominator»(card(k)) = "+
				"λn:num. complex_of_real(polynomial_mul(real_add, &0, real_mul, «1−T», «1−qT», n))",
			By(
				first,
				binomial.At(a.TermAs[Real]("«q»")),
				convolution.At(
					a.TermAs[Fun[Nat, Real]]("«1−T»"),
					a.TermAs[Fun[Nat, Real]]("«1−qT»"))))
		a.Do(denominator.Rw())
		a.Show(
			"and the real product with the effective series embeds as the complex product",
			By(
				rational,
				convolution.At(
					a.TermAs[Fun[Nat, Real]]("polynomial_mul(real_add, &0, real_mul, «1−T», «1−qT»)"),
					a.TermAs[Fun[Nat, Real]]("«zeta»"))))
	}),
})}

// CurveReciprocalRootsExist — the numerator of a smooth curve has reciprocal
// roots. Embedded in ℂ it is a polynomial with constant term one, of degree
// exactly 2g since its top coefficient is q^g, so the complex factorization
// writes it as the reciprocal product of 2g nonzero numbers. No case split on the
// genus is needed: the factorization holds at degree zero.
var CurveReciprocalRootsExist = curveReciprocalRootsExistThm{family.Add(registry.ProofEntry{
	Name: "CurveReciprocalRootsExist",
	Key:  "prop_503c26bf8c860494",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "∃a:(num → complex). «reciprocalRoots»(a)",
		Abbrev: Abbrev{
			{Name: "complexNumerator", Text: "λn:num. complex_of_real(«numerator»(n))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		algebraicallyClosed, inField, curve Fact,
	) {
		rational := arg.Conjuncts(
			GroupPremises(inField, curve, ZetaNumeratorRationality.Read(M).At(K, k, A0, A1, A01, t)),
			"the numerator is a polynomial with integer coefficients",
			"its constant term is one",
			"its degree is at most 2g",
			"it vanishes past 2g",
			"its value at one is the class number",
			"it is (1 − T)(1 − qT) times the effective series")
		functionField := arg.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(inField, field.SubfieldFieldOn.Read(M).At(K)))
		large := arg.Have(
			"k is a finite subfield of M, so it has more than one element",
			"1 < card(k)",
			By(curve, ConstantsAtLeastTwo.Read(functionField).At(k, A0, A1, A01, t)))
		top := arg.Have(
			"the functional equation makes the top coefficient q^g",
			"«numerator»(2 * «genus») = «q» ^ «genus»",
			By(
				algebraicallyClosed,
				inField,
				curve,
				CurveZetaFunctionalEquation.Read(M).At(K, k, A0, A1, A01, t)))
		nonzeroTop := arg.Have(
			"which embeds as a nonzero number",
			"«complexNumerator»(2 * «genus») ≠ complex_of_real(&0)",
			ByArith(
				large,
				top,
				real_pow.PowPos.At(arg.TermAs[Real]("«q»"), arg.TermAs[Nat]("«genus»")),
				complex_field.OfRealInjective.At(
					arg.TermAs[Real]("«numerator»(2 * «genus»)"), arg.TermAs[Real]("&0"))))
		bounded := arg.Have(
			"the embedded numerator vanishes past 2g, so it is a vector of length 2g + 1",
			"vec⟨suc(2 * «genus»)⟩(complex_of_real(&0), «complexNumerator»)",
			Unfold(vec_space.VecDef),
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				past := b.Assume()
				b.Show(
					"past 2g the real coefficient is zero",
					By(past, rational[3].At(i), nat_order.SucLessEqIffLessThan))
			}))
		over := arg.Have(
			"so it is a polynomial",
			"polynomial_over(complex_of_real(&0), 𝕌, «complexNumerator»)",
			Unfold(polynomial.PolynomialOverDef),
			By(bounded, set_basic.InUniv))
		degree := arg.Have(
			"of degree exactly 2g",
			"polynomial_degree(complex_of_real(&0), «complexNumerator») = 2 * «genus»",
			By(over, bounded, nonzeroTop, polynomial.DegreeExact))
		constant := arg.Have(
			"its constant term is one",
			"«complexNumerator»(0) = complex_of_real(&1)",
			By(rational[1]))
		constantNonzero := arg.Have(
			"which is not zero",
			"«complexNumerator»(0) ≠ complex_of_real(&0)",
			ByArith(constant, complex_field.OfRealInjective.At(arg.TermAs[Real]("&1"), arg.TermAs[Real]("&0"))))
		a, factored := arg.UnpackAs[Fun[Nat, Complex]](arg.Simplified(
			GroupPremises(
				over,
				constantNonzero,
				finite_spectrum.ComplexPolynomialReciprocalFactorization.At(
					arg.TermAs[Fun[Nat, Complex]]("«complexNumerator»"))),
			Fwd(degree),
			Fwd(constant)))
		parts := arg.Conjuncts(
			factored,
			"the factorization has nonzero roots",
			"and writes each coefficient through their reciprocal product")
		arg.Take(a)
		arg.Show(
			"these are the two clauses of the definition",
			Unfold(CurveReciprocalRootsDef),
			SplitConj(
				Case(
					"the 2g roots are nonzero",
					By(parts[0])),
				Case(
					"and the numerator, with constant term one, is their reciprocal product",
					Funext(),
					arg.ForEach(func(n *Expr[Nat]) Action {
						return ByArith(parts[1].At(n))
					})),
			))
	}),
})}

// PointCountPowerSum — the trace formula: over the extension of degree m a smooth
// curve has q^m + 1 points less the m-th power sum of its reciprocal roots. The
// roots make the numerator their reciprocal product, so the denominator times the
// zeta series is that product, and its logarithmic derivative is a recurrence for
// the zeta series with this counting sequence. The Euler product gives a recurrence
// with the point counts, and a recurrence determines its counting sequence.
var PointCountPowerSum = pointCountPowerSumThm{family.Add(registry.ProofEntry{
	Name: "PointCountPowerSum",
	Key:  "prop_e2a013013663a657",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀a:(num → complex). ∀m:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
			"«reciprocalRoots»(a)",
			"0 < m",
		},
		Conclusion: "complex_of_real(real_of_num(«count»(m))) = " +
			"complex_sub(complex_of_real(real_of_num(card(k) ^ m + 1)), finite_power_sum(2 * «genus», a, m))",
		Abbrev: Abbrev{
			{Name: "rootCounts", Text: "λj:num. " +
				"    COND(j = 0, " +
				"        complex_of_real(&0), " +
				"        complex_sub(complex_of_real(real_of_num(card(k) ^ j + 1)), " +
				"            finite_power_sum(2 * «genus», a, j)))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, Complex],
		m *Expr[Nat],
		algebraicallyClosed, inField, curve, roots, positive Fact,
	) {
		complexZeta := arg.TermAs[Fun[Nat, Complex]]("«complexZeta»")
		factored := arg.Conjuncts(
			arg.Unfolded(roots, CurveReciprocalRootsDef),
			"the roots are nonzero",
			"and the numerator is their reciprocal product")
		product := arg.Simplified(
			GroupPremises(
				algebraicallyClosed, inField, curve, ComplexZetaProduct.Read(M).At(K, k, A0, A1, A01, t)),
			Fwd(factored[1]))
		recurrence := arg.Have(
			"the denominator times the zeta series is their reciprocal "+
				"product, whose logarithmic derivative recurs with the power sums",
			"series_recurrence(complex_ring, «complexZeta», «rootCounts»)",
			By(
				product,
				finite_spectrum.ReciprocalProductLogDerivative.At(
					arg.TermAs[Nat]("card(k)"),
					arg.TermAs[Nat]("2 * «genus»"),
					a,
					complexZeta)))
		counts := arg.Have(
			"the point counts give a recurrence too, and a recurrence determines its counting sequence",
			"∀j:num. complex_of_real(real_of_num(«count»(j))) = «rootCounts»(j)",
			By(
				algebraicallyClosed,
				inField,
				curve,
				recurrence,
				ComplexZetaRecurrence.Read(M).At(K, k, A0, A1, A01, t),
				formal_series.RecurrenceDeterminesCounts.Read(complex_field.CommRingOn).At(
					complexZeta,
					arg.TermAs[Fun[Nat, Complex]]("λj:num. complex_of_real(real_of_num(«count»(j)))"),
					arg.TermAs[Fun[Nat, Complex]]("«rootCounts»"))))
		arg.Show(
			"at positive m the counting sequence is q^m + 1 less the power sum",
			ByArith(positive, counts.At(m)))
	}),
})}

// ExtensionReciprocalRoots — the r-th powers of the reciprocal roots are the
// reciprocal roots of the same curve over the constants with q^r elements. By base
// change that curve counts at m what the curve counts at r·m, so the trace formula
// at r·m makes its counting sequence q^(rm) + 1 less the m-th power sum of the a(i)^r.
// That counting sequence recovers a reciprocal product from the zeta series of the
// extended curve, which is its numerator by the rationality at q^r.
var ExtensionReciprocalRoots = extensionReciprocalRootsThm{family.Add(registry.ProofEntry{
	Name: "ExtensionReciprocalRoots",
	Key:  "prop_bcc7eb5e7a0b2bb9",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀a:(num → complex). ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
			"«reciprocalRoots»(a)",
			"0 < r",
		},
		Conclusion: "(λn:num. complex_of_real(«extendedNumerator»(r)(n))) = " +
			"reciprocal_product(2 * «genus», «powers»)",
		Abbrev: Abbrev{
			{Name: "complexExtendedZeta", Text: "λn:num. " +
				"    complex_of_real(«extendedEffective»(r)(int_of_num(n)))"},
			{Name: "powers", Text: "λi:num. monoid_pow(complex_mul, complex_of_real(&1), a(i), r)"},
			{Name: "powerCounts", Text: "λj:num. " +
				"    COND(j = 0, " +
				"        complex_of_real(&0), " +
				"        complex_sub(complex_of_real(real_of_num((card(k) ^ r) ^ j + 1)), " +
				"            finite_power_sum(2 * «genus», «powers», j)))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		a *Arrow[Nat, Complex],
		r *Expr[Nat],
		algebraicallyClosed, inField, curve, roots, positive Fact,
	) {
		constants := arg.TermAs[Set[A]]("«constants»(r)")
		composite := arg.TermAs[Set[A]]("«composite»(r)")
		chart0, chart1, chart01 :=
			arg.TermAs[Set[A]]("«constantChart»(r, A₀)"),
			arg.TermAs[Set[A]]("«constantChart»(r, A₁)"),
			arg.TermAs[Set[A]]("«constantChart»(r, A₀₁)")
		extension := arg.Conjuncts(
			GroupPremises(inField, curve, positive, ConstantExtensionCurve.Read(M).At(K, k, A0, A1, A01, t, r)),
			"the composite of K with the constants of q^r elements is a subfield of M",
			"over those constants the charts are a smooth curve",
			"and the constants have q^r elements")
		compositeField, extended, extendedConstantCount := extension[0], extension[1], extension[2]
		recurrence := arg.Have(
			"the zeta series of the extended curve recurs with its point counts",
			"series_recurrence(complex_ring, "+
				"    «complexExtendedZeta», "+
				"    λm:num. complex_of_real(real_of_num(«extendedCount»(r)(m))))",
			By(
				algebraicallyClosed,
				compositeField,
				extended,
				ComplexZetaRecurrence.Read(M).At(composite, constants, chart0, chart1, chart01, t)))
		product := arg.Have(
			"the rationality of the extended curve over ℂ, whose constants have q^r elements",
			"polynomial_mul(complex_add, "+
				"    complex_of_real(&0), "+
				"    complex_mul, "+
				"    «denominator»(card(k) ^ r), "+
				"    «complexExtendedZeta») = "+
				"λn:num. complex_of_real(«extendedNumerator»(r)(n))",
			By(
				algebraicallyClosed,
				compositeField,
				extended,
				extendedConstantCount,
				ComplexZetaProduct.Read(M).At(composite, constants, chart0, chart1, chart01, t)))
		sums := arg.Have(
			"the power sum of the a(i) at r·m is the power sum of the a(i)^r at m",
			"∀m:num. finite_power_sum(2 * «genus», a, r * m) = finite_power_sum(2 * «genus», «powers», m)",
			Simp(Fwd(finite_spectrum.PowerSumDef), Fwd(comm_monoid.PowPow.Read(complex_field.MulMonoid))),
			Basic())
		counts := arg.Have(
			"so the extended curve counts (q^r)^m + 1 less the m-th power sum of the a(i)^r",
			"∀m:num. complex_of_real(real_of_num(«extendedCount»(r)(m))) = «powerCounts»(m)",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				nonzero := b.Unless(
					b.TermAs[Bool]("m = 0"),
					"both counts are zero at index zero",
					Given(func(c *Argument, zero Fact) {
						c.Do(ByArith(zero, curve_point_count.CurveExtensionCountDef))
					}))
				positiveIndex := b.Have(
					"m is positive",
					"0 < m",
					ByArith(nonzero))
				positiveScaled := b.Have(
					"and so is r·m",
					"0 < r * m",
					ByArith(positive, positiveIndex, nat_arith.MulEqZero.At(r, m)))
				baseChange := b.Have(
					"the extended curve counts at m what the curve counts at r·m",
					"«extendedCount»(r)(m) = «count»(r * m)",
					By(
						algebraicallyClosed,
						inField,
						curve,
						positive,
						positiveIndex,
						curve_point_count.ExtensionCountBaseChange.Read(M).At(K, k, A0, A1, A01, t, r, m)))
				trace := b.Have(
					"where the trace formula applies",
					"complex_of_real(real_of_num(«count»(r * m))) = "+
						"complex_sub(complex_of_real(real_of_num(card(k) ^ (r * m) + 1)), "+
						"    finite_power_sum(2 * «genus», a, r * m))",
					By(
						algebraicallyClosed,
						inField,
						curve,
						roots,
						positiveScaled,
						PointCountPowerSum.Read(M).At(K, k, A0, A1, A01, t, a, b.TermAs[Nat]("r * m"))))
				b.Show(
					"q^(rm) is (q^r)^m, and the power sums agree",
					ByArith(
						nonzero,
						baseChange,
						trace,
						sums.At(m),
						nat_arith.PowPow.At(b.TermAs[Nat]("card(k)"), r, m)))
			}))
		powerRecurrence := arg.Have(
			"so the extended zeta series recurs with the power sums of the a(i)^r",
			"series_recurrence(complex_ring, «complexExtendedZeta», «powerCounts»)",
			By(recurrence, counts))
		arg.Show(
			"which makes the extended numerator, the denominator "+
				"at q^r times that series, their reciprocal product",
			product.RwRev(),
			By(
				powerRecurrence,
				finite_spectrum.ReciprocalProductOfCounts.At(
					arg.TermAs[Nat]("card(k) ^ r"),
					arg.TermAs[Nat]("2 * «genus»"),
					arg.TermAs[Fun[Nat, Complex]]("«powers»"),
					arg.TermAs[Fun[Nat, Complex]]("«complexExtendedZeta»"))))
	}),
})}

// CurvePointCountTraceFormula — the reciprocal roots of the numerator of a smooth
// curve exist and compute the curve. Their power sums are q^m + 1 less the point
// counts, their product is q^g, their r-th powers are the reciprocal roots over the
// constants with q^r elements, and each is a root of the reversed numerator. The
// product is read from the top coefficient of the numerator, q^g, and the sign of
// degree 2g; the reversed numerator is the reversal of the reciprocal product.
var CurvePointCountTraceFormula = curvePointCountTraceFormulaThm{family.Add(registry.ProofEntry{
	Name: "CurvePointCountTraceFormula",
	Key:  "prop_15fe3e2ed4212f6c",
	Reading: "The reversed numerator has integer coefficients and leading coefficient " +
		"one, and every a(i) is a root of it, so the reciprocal roots are algebraic " +
		"integers: an output of this theorem, not part of the chosen-root predicate.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "(∃a:(num → complex). «reciprocalRoots»(a)) ∧ " +
			"(∀a:(num → complex). " +
			"    «reciprocalRoots»(a) ⇒ " +
			"    (∀m:num. " +
			"        0 < m ⇒ " +
			"        complex_of_real(real_of_num(«count»(m))) = " +
			"        complex_sub(complex_of_real(real_of_num(card(k) ^ m + 1)), " +
			"            finite_power_sum(2 * «genus», a, m))) ∧ " +
			"    product({i:num | i < 2 * «genus»}, a) = complex_of_real(«q» ^ «genus») ∧ " +
			"    (∀r:num. " +
			"        0 < r ⇒ " +
			"        (λn:num. complex_of_real(«extendedNumerator»(r)(n))) = " +
			"        reciprocal_product(2 * «genus», " +
			"            λi:num. monoid_pow(complex_mul, complex_of_real(real_of_num(1)), a(i), r))) ∧ " +
			"    (∀i:num. " +
			"        i < 2 * «genus» ⇒ " +
			"        polynomial_eval(complex_add, " +
			"            complex_of_real(real_of_num(0)), " +
			"            complex_mul, " +
			"            complex_of_real(real_of_num(1)), " +
			"            λn:num. " +
			"                COND(n ≤ 2 * «genus», " +
			"                    complex_of_real(«numerator»(2 * «genus» - n)), " +
			"                    complex_of_real(real_of_num(0))), " +
			"            a(i)) = " +
			"        complex_of_real(real_of_num(0))))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		algebraicallyClosed, inField, curve Fact,
	) {
		arg.Do(SplitConj(
			Case(
				"complex factorization supplies reciprocal roots",
				By(
					algebraicallyClosed,
					inField,
					curve,
					CurveReciprocalRootsExist.Read(M).At(K, k, A0, A1, A01, t))),
			Case(
				"and every family of them computes the curve",
				Derive(func(b *Argument) {
					a := b.FixAs[Fun[Nat, Complex]]("a")
					roots := b.Assume()
					rootCount := b.TermAs[Nat]("2 * «genus»")
					numerator := b.Conjuncts(
						b.Unfolded(roots, CurveReciprocalRootsDef),
						"the roots are nonzero",
						"and the numerator is their reciprocal product")
					coefficients := b.Have(
						"each coefficient of the numerator is that of the reciprocal product",
						"∀n:num. complex_of_real(«numerator»(n)) = reciprocal_product(2 * «genus», a, n)",
						By(numerator[1]))
					b.Do(SplitConjAll(
						Case(
							"the point counts are the trace formula",
							By(algebraicallyClosed, inField, curve, roots, PointCountPowerSum.Read(M))),
						Case(
							"the product of the roots is q^g",
							Derive(func(c *Argument) {
								top := c.Have(
									"the top coefficient of the numerator is q^g",
									"«numerator»(2 * «genus») = «q» ^ «genus»",
									By(
										algebraicallyClosed,
										inField,
										curve,
										CurveZetaFunctionalEquation.Read(M).At(K, k, A0, A1, A01, t)))
								one := c.TermAs[Complex]("complex_of_real(&1)")
								sign := c.Have(
									"an even power of −1 is one",
									"monoid_pow(complex_mul, complex_of_real(&1), complex_neg(complex_of_real(&1)), 2 * «genus») = "+
										"complex_of_real(&1)",
									By(
										comm_ring.NegPowEven.Read(complex_field.CommRing).At(one, c.TermAs[Nat]("«genus»")),
										comm_monoid.IdentityPow.Read(complex_field.MulMonoid).At(rootCount)))
								c.Show(
									"the top coefficient reads the product",
									ByArith(
										sign,
										top,
										coefficients.At(rootCount),
										finite_spectrum.ReciprocalProductTop.At(rootCount, a)))
							})),
						Case(
							"the powers of the roots are the reciprocal roots over the extensions",
							By(algebraicallyClosed, inField, curve, roots, ExtensionReciprocalRoots.Read(M))),
						Case(
							"the roots are roots of the reversed numerator",
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]("i")
								below := c.Assume()
								c.Do(Simp(Fwd(coefficients)))
								c.Show(
									"which is the reversal of the reciprocal product",
									By(below, finite_spectrum.ReciprocalReverseRoot.At(rootCount, i, a)))
							})),
					))
				})),
		))
	}),
})}
