// recurrence.go — reciprocal products and the recurrences of their
// coefficients: their recursion and that of the power sums, convolution by a
// linear factor and its geometric inverse, the inverse of the denominator
// (1 − T)(1 − qT), and the counting sequences of a finite reciprocal product and
// of its quotient by that denominator, read from the recurrence calculus of
// formal_series at the ring ℂ.

package finite_spectrum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ReciprocalProductClauses — the empty reciprocal product is one, and adding
// the next reciprocal root multiplies it by its linear factor: the convolution
// factors commute, so finite-set recursion applies to the indexed spectrum.
var ReciprocalProductClauses = reciprocalProductClausesThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalProductClauses",
	Key:  "prop_17b55166e5f089f9",
	Build: family.Theorem(
		"∀s:num. ∀a:(num → complex). "+
			"    reciprocal_product(0, a) = basis_vector(0) ∧ "+
			"    reciprocal_product(suc(s), a) = "+
			"    polynomial_mul(«linearFactor»(a(s)), reciprocal_product(s, a))",
		func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex]) {
			step := arg.TermAs[Fun2[Nat, Fun[Nat, Complex], Fun[Nat, Complex]]](
				"λi:num. λP:(num → complex). polynomial_mul(«linearFactor»(a(i)), P)")
			unit := arg.TermAs[Fun[Nat, Complex]]("basis_vector(0)")
			commute := arg.Have(
				"multiplication by two indexed factors commutes",
				Statement{
					Binders:    "∀x y:num. ∀P:(num → complex).",
					Hypotheses: []string{"x ≠ y"},
					Conclusion: "polynomial_mul(«linearFactor»(a(x)), polynomial_mul(«linearFactor»(a(y)), P)) = " +
						"polynomial_mul(«linearFactor»(a(y)), polynomial_mul(«linearFactor»(a(x)), P))",
				},
				By(
					set_basic.InUniv.Inst[Complex](),
					polynomial.PolynomialMulLeftComm.Read(complex_field.CommRingOn)))
			arg.Do(SplitConj(
				Case(
					"the empty spectrum contributes the multiplicative identity",
					Simp(Fwd(ReciprocalProductDef), Fwd(num_segment.BelowStrictClauses)),
					By(commute, cardinality.FiniteRecursion.At(step, unit))),
				Case(
					"the next reciprocal root contributes its linear factor",
					Simp(Fwd(ReciprocalProductDef), Fwd(num_segment.BelowStrictClauses)),
					By(
						Normalized,
						commute,
						cardinality.FiniteRecursion.At(step, unit),
						num_segment.FiniteBelowStrict.At(s),
						nat_order.LessThanIrrefl.At(s))),
			))
		}),
})}

// ReciprocalProductCongruence — reciprocal products depend only on their
// listed prefix: induction on its length compares the last factors.
var ReciprocalProductCongruence = reciprocalProductCongruenceThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalProductCongruence",
	Key:  "prop_b1ce946e8150e2b6",
	Build: family.Theorem(Statement{
		Binders:    "∀s:num. ∀a b:(num → complex).",
		Hypotheses: []string{"∀i:num. i < s ⇒ a(i) = b(i)"},
		Conclusion: "reciprocal_product(s, a) = reciprocal_product(s, b)",
	}, func(arg *Argument, s *Expr[Nat], a, b *Arrow[Nat, Complex]) {
		arg.Induct(s)
		arg.Base(
			"both empty products are the unit",
			Simp(Fwd(ReciprocalProductClauses)),
			Basic())
		arg.Step(
			"equal prefixes and equal last factors give equal products",
			func(step *Argument, ih Fact) {
				agree := step.Assume()
				prefix := step.Have(
					"agreement on the longer prefix includes its last entry",
					"(∀i:num. i < s ⇒ a(i) = b(i)) ∧ a(s) = b(s)",
					ByArith(agree))
				step.Show(
					"apply the product recursion to the equal factors",
					Simp(Fwd(ReciprocalProductClauses)),
					By(Normalized, ih, prefix))
			})
	}),
})}

// PowerSumClauses — the empty spectrum has zero power sums, and the next
// indexed reciprocal root adds its power: the finite prefix-sum recursion retains
// every index, including repetitions among the reciprocal roots.
var PowerSumClauses = powerSumClausesThm{family.Add(registry.ProofEntry{
	Name: "PowerSumClauses",
	Key:  "prop_551ae2d9e5e9696b",
	Build: family.Theorem(
		"∀s m:num. ∀a:(num → complex). "+
			"    finite_power_sum(0, a, m) = &0 ∧ "+
			"    finite_power_sum(suc(s), a, m) = finite_power_sum(s, a, m) + a(s) ^ m",
		func(arg *Argument, s, m *Expr[Nat], a *Arrow[Nat, Complex]) {
			arg.Do(Simp(Fwd(PowerSumDef)))
			powers := arg.TermAs[Fun[Nat, Complex]]("λi:num. a(i) ^ m")
			arg.Show(
				"the prefix sum starts at zero and adds the last indexed power",
				By(
					set_basic.InUniv.Inst[Complex](),
					module.ModuleSumBelowClauses.Read(module.RegularModuleOn.Read(complex_field.CommRingOn)).At(
						powers)))
		}),
})}

// ReciprocalLinearConvolution — multiplication by the reciprocal linear factor
// 1 − rT takes a coefficient p(n) to p(n) − r·p(n − 1), the second term absent
// at n = 0: the factor is the binomial 1 − rT of the polynomial chapter.
var ReciprocalLinearConvolution = reciprocalLinearConvolutionThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalLinearConvolution",
	Key:  "prop_9aa0c460ab00e5e4",
	Build: family.Theorem(
		"∀r:complex. ∀p:(num → complex). ∀n:num. "+
			"    polynomial_mul(«linearFactor»(r), p, n) = p(n) + COND(1 ≤ n, -(r * p(n - 1)), &0)",
		func(arg *Argument, r *Expr[Complex], p *Arrow[Nat, Complex], n *Expr[Nat]) {
			binomial := arg.Have(
				"the factor is the binomial 1 − rT, coefficient by coefficient",
				"«linearFactor»(r) = basis_vector(0) - vec_scalar_mul(complex_mul, r, basis_vector(1))",
				Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
				Funext(),
				Derive(func(arg *Argument) {
					arg.FixAs[Nat]("j")
					notZero := arg.Unless(
						arg.TermAs[Bool]("j = 0"),
						"both constant coefficients are one, the variable term vanishing at zero",
						Given(func(arg *Argument, isZero Fact) {
							arg.Do(ByArith(isZero))
						}))
					notOne := arg.Unless(
						arg.TermAs[Bool]("j = 1"),
						"both linear coefficients are minus r, the constant term vanishing at one",
						Given(func(arg *Argument, isOne Fact) {
							arg.Do(ByArith(notZero, isOne))
						}))
					arg.Show(
						"all higher coefficients vanish",
						ByArith(notZero, notOne))
				}))
			arg.Do(binomial.Rw())
			arg.Show(
				"read the binomial's convolution at degree one",
				By(
					set_basic.InUniv.Inst[Complex](),
					polynomial.BinomialConvolution.Read(complex_field.CommRingOn).AsFact().At(
						r, arg.TermAs[Nat]("1"), n, p)))
		}),
})}

// ReciprocalLinearGeometricInverse — a reciprocal linear factor times its
// geometric series is one: its positive coefficients are consecutive powers
// whose difference vanishes, while the constant coefficient is one.
var ReciprocalLinearGeometricInverse = reciprocalLinearGeometricInverseThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalLinearGeometricInverse",
	Key:  "prop_3f1658ca9c22276e",
	Build: family.Theorem(
		"∀r:complex. polynomial_mul(«linearFactor»(r), «geometric»(r)) = basis_vector(0)",
		func(arg *Argument, r *Expr[Complex]) {
			arg.Do(Funext())
			arg.FixAs[Nat]("n")
			arg.Do(Simp(Fwd(ReciprocalLinearConvolution), Fwd(vec_space.BasisVectorDef)))
			nonzero := arg.Unless(
				arg.TermAs[Bool]("n = 0"),
				"the constant coefficient of the product is the zeroth power, one",
				Given(func(arg *Argument, isZero Fact) {
					arg.Do(ByArith(isZero, comm_monoid.MonoidPowDef))
				}))
			index := arg.Have(
				"a positive index is the successor of its predecessor",
				"1 ≤ n ∧ suc(n - 1) = n",
				ByArith(nonzero))
			arg.Show(
				"consecutive powers cancel in every positive coefficient",
				ByArith(nonzero, index, comm_monoid.MonoidPowDef))
		}),
})}

// ReciprocalDenominatorInverse — the two geometric series invert the denominator
// (1 − T)(1 − qT): each inverts its own linear factor, and convolution commutes.
var ReciprocalDenominatorInverse = reciprocalDenominatorInverseThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalDenominatorInverse",
	Key:  "prop_294fcb6aed33f3c5",
	Build: family.Theorem(
		"∀q:num. polynomial_mul(«denominatorInverse»(q), «denominator»(q)) = basis_vector(0)",
		func(arg *Argument, q *Expr[Nat]) {
			one := arg.TermAs[Complex]("complex_of_real(&1)")
			qComplex := arg.TermAs[Complex]("complex_of_real(&q)")
			firstFactor := arg.TermAs[Fun[Nat, Complex]]("«linearFactor»(complex_of_real(&1))")
			secondFactor := arg.TermAs[Fun[Nat, Complex]]("«linearFactor»(complex_of_real(&q))")
			firstSeries := arg.TermAs[Fun[Nat, Complex]]("«geometric»(complex_of_real(&1))")
			secondSeries := arg.TermAs[Fun[Nat, Complex]]("«geometric»(complex_of_real(&q))")
			denominator := arg.TermAs[Fun[Nat, Complex]]("«denominator»(q)")
			inverse := arg.TermAs[Fun[Nat, Complex]]("«denominatorInverse»(q)")
			arg.Show(
				"the two geometric series invert the denominator's two factors",
				By(
					ReciprocalLinearGeometricInverse.At(one),
					ReciprocalLinearGeometricInverse.At(qComplex),
					set_basic.InUniv.Inst[Complex](),
					polynomial.PolynomialMulComm.Read(complex_field.CommRingOn).At(inverse, denominator),
					polynomial.PolynomialMulAssoc.Read(complex_field.CommRingOn).At(firstFactor, secondFactor, inverse),
					polynomial.PolynomialMulLeftComm.Read(complex_field.CommRingOn).At(
						secondFactor, firstSeries, secondSeries),
					polynomial.PolynomialMulAssoc.Read(complex_field.CommRingOn).At(
						firstFactor,
						firstSeries,
						arg.TermAs[Fun[Nat, Complex]](
							"polynomial_mul(«linearFactor»(complex_of_real(&q)), «geometric»(complex_of_real(&q)))")),
					polynomial.PolynomialOneMul.Read(complex_field.CommRingOn).At(
						arg.TermAs[Fun[Nat, Complex]]("basis_vector(0)"))))
		}),
})}

// ReciprocalLinearRecurrence — a reciprocal linear factor has the negative
// powers of its reciprocal root as its counting sequence, past the zero at
// n = 0: that sequence is one minus the geometric inverse, and the factor times
// it is the factor minus one.
var ReciprocalLinearRecurrence = reciprocalLinearRecurrenceThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalLinearRecurrence",
	Key:  "prop_f56b03100665851",
	Build: family.Sections(
		"∀r:complex. series_recurrence(complex_ring, «linearFactor»(r), «linearCounts»(r))",
		func(ctx *Script, headline string) *GoalStackNode {
			eulerLinear := ctx.Lemma(
				"∀r:complex. (λn:num. &n * «linearFactor»(r, n)) = «linearFactor»(r) - basis_vector(0)",
				func(arg *Argument, r *Expr[Complex]) {
					arg.Do(Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.BasisVectorDef)), Funext())
					arg.FixAs[Nat]("n")
					notZero := arg.Unless(
						arg.TermAs[Bool]("n = 0"),
						"the Euler derivative and the subtraction of the unit both kill the constant coefficient",
						Given(func(arg *Argument, isZero Fact) {
							arg.Do(ByArith(isZero))
						}))
					notOne := arg.Unless(
						arg.TermAs[Bool]("n = 1"),
						"the Euler derivative fixes the linear coefficient, to which the unit contributes nothing",
						Given(func(arg *Argument, isOne Fact) {
							arg.Do(ByArith(notZero, isOne))
						}))
					arg.Show(
						"all other coefficients vanish",
						ByArith(notZero, notOne))
				})
			counts := ctx.Lemma(
				"∀r:complex. «linearCounts»(r) = basis_vector(0) - «geometric»(r)",
				func(arg *Argument, r *Expr[Complex]) {
					arg.Do(Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.BasisVectorDef)), Funext())
					arg.FixAs[Nat]("n")
					nonzero := arg.Unless(
						arg.TermAs[Bool]("n = 0"),
						"the unit cancels the geometric series' constant coefficient",
						Given(func(arg *Argument, isZero Fact) {
							arg.Do(ByArith(isZero, comm_monoid.MonoidPowDef))
						}))
					arg.Show(
						"at a positive index the unit vanishes and the negative power remains",
						ByArith(nonzero))
				})
			return ctx.Theorem(headline, func(arg *Argument, r *Expr[Complex]) {
				arg.Do(Simp(
					Fwd(formal_series.RecurrenceEuler.Read(complex_field.CommRingOn)),
					Fwd(complex_field.AddPowOne),
					Fwd(set_basic.InUniv),
					Fwd(eulerLinear)))
				linear := arg.TermAs[Fun[Nat, Complex]]("«linearFactor»(r)")
				unit := arg.TermAs[Fun[Nat, Complex]]("basis_vector(0)")
				geometric := arg.TermAs[Fun[Nat, Complex]]("«geometric»(r)")
				rightUnit := arg.Have(
					"multiplication by the constant unit leaves the factor unchanged",
					"polynomial_mul(«linearFactor»(r), basis_vector(0)) = «linearFactor»(r)",
					By(
						set_basic.InUniv.Inst[Complex](),
						polynomial.PolynomialOneMul.Read(complex_field.CommRingOn).At(linear),
						polynomial.PolynomialMulComm.Read(complex_field.CommRingOn).At(linear, unit)))
				arg.Do(Simp(Fwd(counts)))
				arg.Show(
					"distribute the product over unit minus geometric inverse",
					By(
						rightUnit,
						set_basic.InUniv.Inst[Complex](),
						At(ReciprocalLinearGeometricInverse, r),
						polynomial.PolynomialMulComm.Read(complex_field.CommRingOn).At(
							arg.TermAs[Fun[Nat, Complex]]("basis_vector(0) - «geometric»(r)"), linear),
						polynomial.PolynomialMulSub.Read(complex_field.CommRingOn).At(linear, unit, geometric)))
			})
		}),
})}

// ReciprocalProductRecurrence — adjoining a reciprocal root adds its negative
// powers to the counting sequence; induction starts with the unit, whose
// counting sequence is zero.
var ReciprocalProductRecurrence = reciprocalProductRecurrenceThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalProductRecurrence",
	Key:  "prop_91312c6bd89772d9",
	Build: family.Sections(
		"∀s:num. ∀a:(num → complex). "+
			"    series_recurrence(complex_ring, reciprocal_product(s, a), «spectrumCounts»(s, a))",
		func(ctx *Script, headline string) *GoalStackNode {
			emptyCounts := ctx.Lemma("∀a:(num → complex). "+
				"    «spectrumCounts»(0, a) = (λn:num. complex_of_real(&0))", func(
				arg *Argument,
				a *Arrow[Nat, Complex],
			) {
				arg.Do(Simp(Fwd(PowerSumClauses)), Funext())
				arg.FixAs[Nat]("n")
				arg.Cases(arg.TermAs[Bool]("n = 0"))
				arg.When(
					"the constant term is zero",
					func(arg *Argument, isZero Fact) {
						arg.Do(ByArith(isZero))
					})
				arg.Otherwise(
					"a positive term is the negative empty sum, which is zero",
					func(arg *Argument, nonzero Fact) {
						arg.Do(ByArith(nonzero))
					})
			})
			nextCounts := ctx.Lemma("∀s:num. ∀a:(num → complex). "+
				"    (λn:num. «linearCounts»(a(s), n) + «spectrumCounts»(s, a, n)) = "+
				"    «spectrumCounts»(suc(s), a)", func(
				arg *Argument,
				s *Expr[Nat],
				a *Arrow[Nat, Complex],
			) {
				arg.Do(Simp(Fwd(PowerSumClauses)), Funext())
				arg.FixAs[Nat]("n")
				arg.Cases(arg.TermAs[Bool]("n = 0"))
				arg.When(
					"the constant terms add to zero",
					func(arg *Argument, isZero Fact) {
						arg.Do(ByArith(isZero))
					})
				arg.Otherwise(
					"negation distributes across the power-sum step, adding the next power",
					func(arg *Argument, nonzero Fact) {
						arg.Do(ByArith(nonzero))
					})
			})
			return ctx.Theorem(headline, func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex]) {
				arg.Induct(s)
				arg.Base(
					"the empty product is the unit with the zero counting sequence",
					Simp(Fwd(ReciprocalProductClauses), Fwd(emptyCounts)),
					By(formal_series.RecurrenceUnit.Read(complex_field.CommRingOn)))
				arg.Step(
					"adjoin the next reciprocal linear factor",
					func(arg *Argument, ih Fact) {
						countStep := arg.Have(
							"the new factor adds its counting sequence of negative powers",
							"(λn:num. «linearCounts»(a(s), n) + «spectrumCounts»(s, a, n)) = «spectrumCounts»(suc(s), a)",
							By(At(nextCounts, s, a)))
						arg.Do(countStep.RwRev(), Simp(Fwd(ReciprocalProductClauses)))
						arg.Show(
							"the product rule adds the two counting sequences",
							By(
								ih,
								ReciprocalLinearRecurrence.At(arg.TermAs[Complex]("a(s)")),
								formal_series.RecurrenceProduct.Read(complex_field.CommRingOn)))
					})
			})
		}),
})}

// ReciprocalProductLogDerivative — the logarithmic derivative T·c′/c of a
// series c is its counting sequence, and here that sequence is qᵐ + 1 minus
// the m-th power sum. A finite reciprocal product has the negative power sums
// as its counting sequence, the two invertible denominator factors contribute
// -1 and -qᵐ, and subtracting theirs leaves that of c.
var ReciprocalProductLogDerivative = reciprocalProductLogDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalProductLogDerivative",
	Key:  "prop_adfd6f792a06d03",
	Build: family.Sections(Statement{
		Binders:    "∀q s:num. ∀a c:(num → complex).",
		Hypotheses: []string{"polynomial_mul(«denominator»(q), c) = reciprocal_product(s, a)"},
		Conclusion: "series_recurrence(complex_ring, " +
			"    c, " +
			"    λm:num. COND(m = 0, complex_of_real(&0), &(q ^ m + 1) - finite_power_sum(s, a, m)))",
		Abbrev: Abbrev{
			{Name: "denominatorCounts", Text: "λq:num. λn:num. " +
				"    «linearCounts»(complex_of_real(&1), n) + «linearCounts»(complex_of_real(&q), n)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		countEmbedding := ctx.Lemma("∀q s:num. ∀a:(num → complex). "+
			"    (λn:num. «spectrumCounts»(s, a, n) - «denominatorCounts»(q, n)) = "+
			"    (λn:num. COND(n = 0, complex_of_real(&0), &(q ^ n + 1) - finite_power_sum(s, a, n)))", func(
			arg *Argument,
			q, s *Expr[Nat],
			a *Arrow[Nat, Complex],
		) {
			arg.Do(Funext())
			n := arg.FixAs[Nat]("n")
			nonzero := arg.Unless(
				arg.TermAs[Bool]("n = 0"),
				"both sides have constant coefficient zero",
				Given(func(arg *Argument, isZero Fact) {
					arg.Do(ByArith(isZero))
				}))
			embedding := arg.Have(
				"the natural number qⁿ + 1 embeds as the sum of the two complex powers",
				"&(q ^ n + 1) = complex_of_real(&q) ^ n + &1",
				By(
					complex_field.OfRealPow.At(arg.TermAs[Real]("&q"), n),
					real_pow.OfNumPow.At(q, n),
					real_construction.OfNumAdd.At(arg.TermAs[Nat]("q ^ n"), arg.TermAs[Nat]("1")),
					complex_field.OfRealAdd.At(arg.TermAs[Real]("&(q ^ n)"), arg.TermAs[Real]("&1"))))
			arg.Show(
				"subtracting the denominator's counting sequence adds the two positive powers",
				ByArith(nonzero, embedding, comm_monoid.IdentityPow.Read(complex_field.MulMonoid).At(n)))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			q, s *Expr[Nat],
			a, c *Arrow[Nat, Complex],
			equation Fact,
		) {
			one := arg.TermAs[Complex]("complex_of_real(&1)")
			qComplex := arg.TermAs[Complex]("complex_of_real(&q)")
			denominator := arg.Have(
				"the denominator's counting sequence adds the two negative power sequences",
				"series_recurrence(complex_ring, «denominator»(q), «denominatorCounts»(q))",
				By(
					ReciprocalLinearRecurrence.At(one),
					ReciprocalLinearRecurrence.At(qComplex),
					formal_series.RecurrenceProduct.Read(complex_field.CommRingOn)))
			numerator := arg.Simplified(At(ReciprocalProductRecurrence, s, a), Rev(equation))
			arg.Do(Simp(Rev(countEmbedding)))
			arg.Show(
				"subtract the denominator's counting sequence from the reciprocal product's",
				By(
					numerator,
					denominator,
					set_basic.InUniv.Inst[Complex](),
					ReciprocalDenominatorInverse.At(q),
					formal_series.RecurrenceQuotient.Read(complex_field.CommRingOn)))
		})
	}),
})}

// ReciprocalProductOfCounts — the converse of ReciprocalProductLogDerivative. The
// two geometric series invert the denominator, so the reciprocal product over the
// denominator is a series whose product with the denominator is the reciprocal
// product. That member gives it the counting sequence of c, and over ℂ, an integral
// domain of characteristic zero, a recurrence determines its series, so c is that
// quotient.
var ReciprocalProductOfCounts = reciprocalProductOfCountsThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalProductOfCounts",
	Key:  "prop_7a3b2c5dd3a1f161",
	Build: family.Theorem(Statement{
		Binders:    "∀q s:num. ∀a c:(num → complex).",
		Hypotheses: []string{"series_recurrence(complex_ring, c, «counts»(q, s, a))"},
		Conclusion: "polynomial_mul(«denominator»(q), c) = reciprocal_product(s, a)",
		Abbrev: Abbrev{
			{Name: "counts", Text: "λq:num. λs:num. λa:(num → complex). λm:num. " +
				"    COND(m = 0, complex_of_real(&0), &(q ^ m + 1) - finite_power_sum(s, a, m))"},
		},
	}, func(arg *Argument, q, s *Expr[Nat], a, c *Arrow[Nat, Complex], recurrence Fact) {
		denominator := arg.TermAs[Fun[Nat, Complex]]("«denominator»(q)")
		inverse := arg.TermAs[Fun[Nat, Complex]]("«denominatorInverse»(q)")
		product := arg.TermAs[Fun[Nat, Complex]]("reciprocal_product(s, a)")
		quotient := arg.TermAs[Fun[Nat, Complex]](
			"polynomial_mul(«denominatorInverse»(q), reciprocal_product(s, a))")
		cancelled := arg.Have(
			"the denominator times the quotient is the reciprocal product",
			"polynomial_mul(«denominator»(q), "+
				"    polynomial_mul(«denominatorInverse»(q), reciprocal_product(s, a))) = "+
				"reciprocal_product(s, a)",
			By(
				ReciprocalDenominatorInverse.At(q),
				set_basic.InUniv.Inst[Complex](),
				polynomial.PolynomialMulComm.Read(complex_field.CommRingOn).At(denominator, inverse),
				polynomial.PolynomialMulAssoc.Read(complex_field.CommRingOn).At(denominator, inverse, product),
				polynomial.PolynomialOneMul.Read(complex_field.CommRingOn).At(product)))
		unique := arg.Have(
			"c and the quotient share their counting sequence, which determines a series over ℂ",
			"c = polynomial_mul(«denominatorInverse»(q), reciprocal_product(s, a))",
			By(
				recurrence,
				cancelled,
				complex_field.ComplexCharacteristicZero,
				ReciprocalProductLogDerivative.At(q, s, a, quotient),
				At(
					formal_series.RecurrenceDeterminesCoefficients.Read(complex_field.ComplexIntegralDomain),
					c,
					quotient,
					arg.TermAs[Fun[Nat, Complex]]("«counts»(q, s, a)"))))
		arg.Show(
			"so the denominator times c is the reciprocal product",
			By(unique, cancelled))
	}),
})}
