// line.go — ζ on Re s ≥ 1: its derivative and its logarithmic derivative
// as Dirichlet series, ζ as the exponential of a Dirichlet series, ζ(s + v)
// as the Dirichlet series of n^(−v), the 3-4-1 inequality for a completely
// multiplicative coefficient and for ζ itself, ζ at a real σ > 1 as a real
// number between 1 and 1 + 1/(σ − 1), the non-vanishing at 1 that the 3-4-1
// bound forces on a function differentiable there, no zero on the line
// Re s = 1, and the continuation of the series of Λ.

package riemann_zeta

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/prime_distribution"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ZetaDerivativeSeries — for Re s > 1 the derivative of ζ is minus the
// Dirichlet series of log n.
var ZetaDerivativeSeries = zetaDerivativeSeriesThm{family.Add(registry.ProofEntry{
	Name: "ZetaDerivativeSeries",
	Key:  "prop_901a463c28c510d0",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&1 < re(s)"},
		Conclusion: "complex_derivative_at(riemann_zeta, s, -dirichlet_series(λn:num. &(log(&n)), s))",
		Abbrev: Abbrev{
			{Name: "ones", Text: "λn:num. complex_of_real(&1)"},
			{Name: "seriesOfOnes", Text: "λz:complex. dirichlet_series(«ones», z)"},
			{Name: "weighted", Text: "λn:num. complex_of_real(log(&n)) * complex_of_real(&1)"},
		},
	}, func(a *Argument, s *Expr[Complex], right Fact) {
		ones := a.TermAs[Fun[Nat, Complex]]("«ones»")
		one := a.TermAs[Real]("&1")
		bounded := a.Have(
			"the constant coefficients are bounded by one",
			"∀n:num. |«ones»(n)| ≤ &1",
			ByArith(complex_abs.AbsOfReal.At(one)))
		converges := a.Have(
			"so their moduli are summable at every real exponent above one",
			"∀σ:real. &1 < σ ⇒ ∃t:real. real_sums(λn:num. |«ones»(n + 1)| * real_rpow(&(n + 1), -σ), t)",
			Derive(func(b *Argument) {
				σ := b.FixAs[Real]("σ")
				aboveOne := b.Assume()
				b.Show(
					"compare with the powers",
					By(bounded, aboveOne, dirichlet_series.BoundedAbsolutelySummable.At(ones, one, σ)))
			}))
		derivative := a.Have(
			"differentiate the Dirichlet series of the constant one",
			"complex_derivative_at(«seriesOfOnes», s, -dirichlet_series(«weighted», s))",
			By(converges, right, dirichlet_series.DirichletSeriesDerivative.At(ones, one, s)))
		positive := a.Have(
			"the distance to the boundary line is positive",
			"&0 < re(s) - &1",
			ByArith(right))
		agree := a.Have(
			"ζ agrees with the Dirichlet series of one on the disc inside the right half-plane",
			"∀z:complex. |z - s| < re(s) - &1 ⇒ riemann_zeta(z) = «seriesOfOnes»(z)",
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]("z")
				near := b.Assume()
				toRight := b.Have(
					"the real displacement cannot reach the line Re z = 1",
					"&1 < re(z)",
					ByArith(near, complex_abs.PartsNonexpanding.At(z, s)))
				b.Show(
					"ZetaSums identifies the chosen Dirichlet value",
					By(
						toRight,
						ZetaSums.At(z),
						dirichlet_series.DirichletSeriesValue.At(ones, z, b.TermAs[Complex]("riemann_zeta(z)"))))
			}))
		local := a.Have(
			"local agreement transfers the derivative to ζ",
			"complex_derivative_at(riemann_zeta, s, -dirichlet_series(«weighted», s))",
			By(
				positive,
				agree,
				derivative,
				complex_derivative.DerivativeLocal.At(
					a.TermAs[Fun[Complex, Complex]]("riemann_zeta"),
					a.TermAs[Fun[Complex, Complex]]("«seriesOfOnes»"),
					s, a.TermAs[Complex]("-dirichlet_series(«weighted», s)"), a.TermAs[Real]("re(s) - &1"))))
		coefficients := a.Have(
			"the factor one can be dropped from the logarithm coefficients",
			"«weighted» = (λn:num. complex_of_real(log(&n)))",
			Simp(Fwd(comm_monoid.RightIdentity.Read(complex_field.MulMonoid))),
			Refl())
		a.Show(
			"the derivative is minus the Dirichlet series with coefficients log n",
			By(local, coefficients))
	}),
})}

// ZetaMangoldt — for Re s > 1 the derivative of ζ is −ζ times the
// Dirichlet series of Λ: the logarithmic derivative of the Dirichlet series
// of the constant one, carried to ζ by its agreement with that series on a
// disc about s.
var ZetaMangoldt = zetaMangoldtThm{family.Add(registry.ProofEntry{
	Name: "ZetaMangoldt",
	Key:  "prop_a361fb349f3971dd",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&1 < re(s)"},
		Conclusion: "complex_derivative_at(riemann_zeta, " +
			"    s, " +
			"    -(riemann_zeta(s) * dirichlet_series(λn:num. &(von_mangoldt(n)), s)))",
		Abbrev: Abbrev{
			{Name: "ones", Text: "λn:num. complex_of_real(&1)"},
			{Name: "seriesOfOnes", Text: "λz:complex. dirichlet_series(«ones», z)"},
			{Name: "weighted", Text: "λn:num. &(von_mangoldt(n)) * complex_of_real(&1)"},
			{Name: "slope", Text: "-(dirichlet_series(«ones», s) * dirichlet_series(«weighted», s))"},
		},
	}, func(a *Argument, s *Expr[Complex], right Fact) {
		ones := a.TermAs[Fun[Nat, Complex]]("«ones»")
		unit := a.Have(
			"the constant one is multiplicative and bounded by one",
			"complex_of_real(&1) = complex_of_real(&1) * complex_of_real(&1) ∧ |complex_of_real(&1)| ≤ &1",
			ByArith(complex_abs.AbsOfReal.At(a.TermAs[Real]("&1"))))
		derivative := a.Have(
			"the logarithmic derivative of the Dirichlet series of the constant one",
			"complex_derivative_at(«seriesOfOnes», s, «slope»)",
			By(unit, right, dirichlet_series.LogarithmicDerivative.At(ones, s)))
		positive := a.Have(
			"the distance to the boundary line is positive",
			"&0 < re(s) - &1",
			ByArith(right))
		agree := a.Have(
			"ζ agrees with the Dirichlet series of one on the disc inside the right half-plane",
			"∀z:complex. |z - s| < re(s) - &1 ⇒ riemann_zeta(z) = «seriesOfOnes»(z)",
			Derive(func(b *Argument) {
				z := b.FixAs[Complex]("z")
				near := b.Assume()
				toRight := b.Have(
					"the real displacement cannot reach the line Re z = 1",
					"&1 < re(z)",
					ByArith(near, complex_abs.PartsNonexpanding.At(z, s)))
				b.Show(
					"ZetaSums identifies the chosen Dirichlet value",
					By(
						toRight,
						ZetaSums.At(z),
						dirichlet_series.DirichletSeriesValue.At(ones, z, b.TermAs[Complex]("riemann_zeta(z)"))))
			}))
		local := a.Have(
			"local agreement transfers the derivative to ζ",
			"complex_derivative_at(riemann_zeta, s, «slope»)",
			By(
				positive,
				agree,
				derivative,
				complex_derivative.DerivativeLocal.At(
					a.TermAs[Fun[Complex, Complex]]("riemann_zeta"),
					a.TermAs[Fun[Complex, Complex]]("«seriesOfOnes»"),
					s, a.TermAs[Complex]("«slope»"), a.TermAs[Real]("re(s) - &1"))))
		zeta := a.Have(
			"ζ is the Dirichlet value for the constant one",
			"dirichlet_series(«ones», s) = riemann_zeta(s)",
			By(
				right,
				ZetaSums.At(s),
				dirichlet_series.DirichletSeriesValue.At(
					ones, s, a.TermAs[Complex]("riemann_zeta(s)"))))
		coefficients := a.Have(
			"the factor one can be dropped from the Mangoldt coefficients",
			"«weighted» = (λn:num. &(von_mangoldt(n)))",
			Simp(Fwd(comm_monoid.RightIdentity.Read(complex_field.MulMonoid))),
			Refl())
		a.Show(
			"read the derivative with ζ for the series of one",
			By(local, zeta, coefficients))
	}),
	Reading: "The series of Λ is minus the logarithmic derivative of ζ, " +
		"without dividing by ζ: the statement holds before ζ is known not to vanish.",
})}

// ZetaExponential — for Re s > 1, ζ is the exponential of the Dirichlet
// series of Λ(n)/log n.
var ZetaExponential = zetaExponentialThm{family.Add(registry.ProofEntry{
	Name: "ZetaExponential",
	Key:  "prop_a5145f4d5776de65",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&1 < re(s)"},
		Conclusion: "riemann_zeta(s) = exp(dirichlet_series(λn:num. &(von_mangoldt(n) / log(&n)), s))",
	}, func(a *Argument, s *Expr[Complex], right Fact) {
		ones := a.TermAs[Fun[Nat, Complex]]("λn:num. complex_of_real(&1)")
		value := a.Have(
			"the Dirichlet series of the constant one sums to ζ(s)",
			"dirichlet_series(λn:num. complex_of_real(&1), s) = riemann_zeta(s)",
			By(
				right,
				ZetaSums.At(s),
				dirichlet_series.DirichletSeriesValue.At(
					ones, s, a.TermAs[Complex]("riemann_zeta(s)"))))
		unit := a.Have(
			"the constant one is multiplicative and bounded by one",
			"complex_of_real(&1) = complex_of_real(&1) * complex_of_real(&1) ∧ |complex_of_real(&1)| ≤ &1",
			ByArith(complex_abs.AbsOfReal.At(a.TermAs[Real]("&1"))))
		exponential := a.Have(
			"apply the logarithmic series identity to the constant one",
			"dirichlet_series(λn:num. complex_of_real(&1), s) = "+
				"exp(dirichlet_series(λn:num. complex_of_real(von_mangoldt(n) / log(&n)) * &1, s))",
			By(right, unit, dirichlet_series.LogarithmicSeries.At(ones, s)))
		coefficients := a.Have(
			"multiplying the coefficients by one leaves them unchanged",
			"(λn:num. complex_of_real(von_mangoldt(n) / log(&n)) * &1) = "+
				"(λn:num. complex_of_real(von_mangoldt(n) / log(&n)))",
			Simp(Fwd(comm_monoid.RightIdentity.Read(complex_field.MulMonoid))),
			Refl())
		a.Show(
			"the exponential sums to ζ(s)",
			By(exponential, value, coefficients))
	}),
	Reading: "This is the Euler product in logarithmic form: the series " +
		"in the exponent is the sum of p^(−ks)/k over the prime powers.",
})}

// ZetaShift — a Dirichlet series whose coefficients are n^(−v) at the
// positive indices is ζ shifted by v: D(g, s) = ζ(s + v) where
// Re(s + v) > 1, the two series having the same terms.
var ZetaShift = zetaShiftThm{family.Add(registry.ProofEntry{
	Name: "ZetaShift",
	Key:  "prop_41063353a863f794",
	Build: family.Theorem(Statement{
		Binders: "∀g:(num → complex). ∀v s:complex.",
		Hypotheses: []string{
			"∀n:num. 0 < n ⇒ g(n) = complex_cpow(&n, -v)",
			"&1 < re(s + v)",
		},
		Conclusion: "dirichlet_series(g, s) = riemann_zeta(s + v)",
	}, func(a *Argument, g *Arrow[Nat, Complex], v, s *Expr[Complex], coefficients, right Fact) {
		shifted := a.TermAs[Complex]("s + v")
		value := a.TermAs[Complex]("riemann_zeta(s + v)")
		ones := a.TermAs[Fun[Nat, Complex]]("λn:num. complex_of_real(&1)")
		terms := a.Have(
			"the two Dirichlet series have the same terms",
			"(λn:num. g(n + 1) * complex_cpow(&(n + 1), -s)) = "+
				"(λn:num. complex_of_real(&1) * complex_cpow(&(n + 1), -(s + v)))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				positive := b.Have(
					"the coefficient index and base are positive",
					"0 < n + 1 ∧ &0 < real_of_num(n + 1)",
					ByArith())
				exponent := b.Have(
					"write the shifted exponent as a sum",
					"-(s + v) = -v + -s",
					ByArith())
				b.Show(
					"positive-base powers take exponent sums to products",
					Simp(Fwd(comm_monoid.LeftIdentity.Read(complex_field.MulMonoid))),
					By(
						coefficients.At(b.TermAs[Nat]("n + 1")),
						positive,
						exponent,
						complex_cpow.CpowAdd.At(b.TermAs[Real]("real_of_num(n + 1)"),
							b.TermAs[Complex]("-v"), b.TermAs[Complex]("-s"))))
			}))
		sum := a.Have(
			"the shifted zeta value sums the series of g",
			"dirichlet_sums(g, s, riemann_zeta(s + v))",
			By(
				right,
				terms,
				ZetaSums.At(shifted),
				dirichlet_series.DirichletSumsDef.At(ones, shifted, value),
				dirichlet_series.DirichletSumsDef.At(g, s, value)))
		a.Show(
			"read the value of the series of g",
			By(sum, dirichlet_series.DirichletSeriesValue.At(g, s, value)))
	}),
})}

// ZetaNonzeroRight — ζ has no zero in Re s > 1: there it is the Dirichlet
// series of the constant one, completely multiplicative and bounded by one,
// and such a series does not vanish.
var ZetaNonzeroRight = zetaNonzeroRightThm{family.Add(registry.ProofEntry{
	Name: "ZetaNonzeroRight",
	Key:  "prop_def98e5ce03bf4e7",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&1 < re(s)"},
		Conclusion: "riemann_zeta(s) ≠ &0",
	},
		func(a *Argument, s *Expr[Complex], right Fact) {
			ones := a.TermAs[Fun[Nat, Complex]]("λn:num. complex_of_real(&1)")
			unit := a.Have(
				"the constant one is multiplicative and bounded by one",
				"complex_of_real(&1) = complex_of_real(&1) * complex_of_real(&1) ∧ |complex_of_real(&1)| ≤ &1",
				ByArith(complex_abs.AbsOfReal.At(a.TermAs[Real]("&1"))))
			a.Show(
				"ζ is the Dirichlet series of the constant one, which has no zero there",
				By(
					Normalized,
					right,
					unit,
					ZetaSums.At(s),
					dirichlet_series.DirichletSeriesValue.At(ones, s, a.TermAs[Complex]("riemann_zeta(s)")),
					dirichlet_series.DirichletSeriesNonzero.At(ones, s)))
		}),
})}

// MertensInequality — for a completely multiplicative f with f(1) = 1 and
// bounded by 1, and a real σ > 1: ζ(σ)³·|D(f, σ)|⁴·|D(f², σ)| ≥ 1. Each
// modulus is the exponential of the real part of a logarithmic series, and
// the combined exponent sums nonnegative weights Λ(n)/log n · n^(−σ) times
// 3 + 4·Re u + Re u² at u = f(n): on the unit circle that is the classical
// 3 + 4cos θ + cos 2θ, and it is nonnegative on the whole closed disc.
var MertensInequality = mertensInequalityThm{family.Add(registry.ProofEntry{
	Name: "MertensInequality",
	Key:  "prop_8695087d363a13c0",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → complex). ∀σ:real.",
		Hypotheses: []string{
			"∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)",
			"f(1) = &1",
			"∀n:num. |f(n)| ≤ &1",
			"&1 < σ",
		},
		Conclusion: "&1 ≤ " +
			"|riemann_zeta(&σ)| ^ 3 * " +
			"|dirichlet_series(f, &σ)| ^ 4 * " +
			"|dirichlet_series(λn:num. f(n) * f(n), &σ)|",
		Abbrev: Abbrev{
			{Name: "ratio", Text: "λn:num. von_mangoldt(n) / log(&n)"},
			{Name: "ones", Text: "λn:num. complex_of_real(&1)"},
			{Name: "square", Text: "λn:num. f(n) * f(n)"},
			{Name: "logCoefficients", Text: "λg:(num → complex). λn:num. &(«ratio»(n)) * g(n)"},
			{Name: "logSeries", Text: "λg:(num → complex). dirichlet_series(«logCoefficients»(g), &σ)"},
			{Name: "realTerms", Text: "λg:(num → complex). λn:num. " +
				"    re(«logCoefficients»(g, n + 1) * complex_cpow(&(n + 1), -complex_of_real(σ)))"},
			{Name: "threeTerms", Text: "λn:num. &3 * «realTerms»(«ones», n)"},
			{Name: "fourTerms", Text: "λn:num. &4 * «realTerms»(f, n)"},
			{Name: "bothTerms", Text: "λn:num. «threeTerms»(n) + «fourTerms»(n)"},
			{Name: "combinedTerms", Text: "λn:num. «bothTerms»(n) + «realTerms»(«square», n)"},
			{Name: "threeSum", Text: "&3 * re(«logSeries»(«ones»))"},
			{Name: "fourSum", Text: "&4 * re(«logSeries»(f))"},
			{Name: "combinedSum", Text: "«threeSum» + «fourSum» + re(«logSeries»(«square»))"},
			{Name: "threeFourOne", Text: "λu:complex. &3 + &4 * re(u) + re(u * u)"},
		},
	}, func(
		a *Argument,
		f *Arrow[Nat, Complex],
		σ *Expr[Real],
		multiplicative, first, bounded, aboveOne Fact,
	) {
		s := a.TermAs[Complex]("complex_of_real(σ)")
		one := a.TermAs[Real]("&1")
		zero := a.TermAs[Real]("&0")
		oneComplex := a.TermAs[Complex]("complex_of_real(&1)")
		ones := a.TermAs[Fun[Nat, Complex]]("«ones»")
		square := a.TermAs[Fun[Nat, Complex]]("«square»")
		right := a.Have(
			"the real exponent lies in the half-plane of convergence",
			"&1 < re(complex_of_real(σ))",
			By(Normalized, aboveOne, complex_field.PartsOfReal.At(σ)))
		atZero := a.Have(
			"the Mangoldt coefficient at zero vanishes",
			"von_mangoldt(0) = &0",
			Derive(func(b *Argument) {
				noPower := b.Have(
					"zero cannot be a positive power of a prime",
					"¬(∃p k:num. nat_prime(p) ∧ 0 < k ∧ 0 = p ^ k)",
					Derive(func(c *Argument) {
						p, k, power := c.Obtain2As[Nat, Nat](
							"suppose zero is a positive power of a prime",
							"∃p k:num. nat_prime(p) ∧ 0 < k ∧ 0 = p ^ k",
							By(c.SupposeNot()))
						c.Show(
							"a prime base is at least two and has nonzero powers",
							ByArith(power, nat_prime.PrimeAtLeastTwo.At(p), nat_arith.PowEqZero.At(p, k)))
					}))
				b.Show(
					"the defining test for a prime power fails at zero",
					Unfold(prime_distribution.VonMangoldtDef),
					By(noPower))
			}))
		ratioBounds := a.Have(
			"the Mangoldt coefficient divided by the logarithm lies between zero and one",
			"∀n:num. &0 ≤ «ratio»(n) ∧ «ratio»(n) ≤ &1",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Cases(b.TermAs[Bool]("n = 0"))
				b.When(
					"at zero the numerator is zero",
					func(c *Argument, nZero Fact) {
						c.Show(
							"the quotient is zero",
							Simp(Fwd(real_field.RealDivDef)),
							ByArith(nZero, atZero))
					})
				b.Otherwise(
					"at a positive index the logarithm bounds the Mangoldt coefficient",
					func(c *Argument, nonzero Fact) {
						positive := c.Have(
							"the index is positive",
							"0 < n",
							ByArith(nonzero))
						below := c.Have(
							"the Mangoldt coefficient is at most the logarithm",
							"von_mangoldt(n) ≤ log(&n)",
							By(positive, prime_distribution.MangoldtLessEqLog.At(n)))
						nonnegative := prime_distribution.MangoldtNonneg.At(n)
						c.Cases(c.TermAs[Bool]("&0 < log(&n)"))
						c.When(
							"divide by the positive logarithm",
							func(d *Argument, logPositive Fact) {
								logarithm := d.TermAs[Real]("log(&n)")
								mangoldt := d.TermAs[Real]("von_mangoldt(n)")
								d.Show(
									"division takes the lower bound to zero and the upper bound to one",
									ByArith(
										nonnegative,
										below,
										logPositive,
										real_order_field.LessEqDivMulLeft.At(zero, mangoldt, logarithm),
										real_order_field.LessEqDivMulRight.At(mangoldt, one, logarithm)))
							})
						c.Otherwise(
							"a nonpositive logarithm forces the numerator to vanish",
							func(d *Argument, logNotPositive Fact) {
								vanishes := d.Have(
									"the Mangoldt coefficient lies between zero and the nonpositive logarithm",
									"von_mangoldt(n) = &0",
									ByArith(nonnegative, below, logNotPositive))
								d.Show(
									"the quotient is zero when the numerator is zero",
									Simp(Fwd(real_field.RealDivDef)),
									ByArith(vanishes))
							})
					})
			}))
		realSums := a.Have(
			"the real projections of the logarithmic terms sum to the real part of the series",
			"∀g:(num → complex). (∀k:num. |g(k)| ≤ &1) ⇒ real_sums(«realTerms»(g), re(«logSeries»(g)))",
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, Complex]]("g")
				unitBound := b.Assume()
				coefficients := b.TermAs[Fun[Nat, Complex]]("«logCoefficients»(g)")
				logBound := b.Have(
					"the logarithmic coefficients are bounded by one",
					"∀k:num. |«logCoefficients»(g, k)| ≤ &1",
					Derive(func(c *Argument) {
						k := c.FixAs[Nat]("k")
						c.Show(
							"the product of the two nonnegative factors is at most one",
							ByArith(
								ratioBounds.At(k),
								unitBound.At(k),
								complex_abs.AbsOfNonnegReal.At(c.TermAs[Real]("«ratio»(k)"))))
					}))
				v, sum := b.ObtainAs[Complex](
					"bounded logarithmic coefficients give a convergent Dirichlet series",
					"∃v:complex. "+
						"    dirichlet_sums(«logCoefficients»(g), &σ, v) ∧ "+
						"    |v - «logCoefficients»(g, 1)| ≤ &1 / (re(complex_of_real(σ)) - &1)",
					By(logBound, right, dirichlet_series.BoundedCoefficientsConverge.At(coefficients, one, s)),
					Named("v"))
				b.Show(
					"the convergent series has its defined value and its real part is the sum of the real parts",
					By(
						sum,
						dirichlet_series.DirichletSeriesValue.At(coefficients, s, v),
						dirichlet_series.DirichletSumsDef.At(coefficients, s, v),
						complex_series.ComplexSumsDef.At(b.TermAs[Fun[Nat, Complex]](
							"λn:num. «logCoefficients»(g, n + 1) * complex_cpow(&(n + 1), -complex_of_real(σ))"), v)))
			}))
		onesBound := a.Have(
			"the constant sequence has unit modulus",
			"∀n:num. |«ones»(n)| ≤ &1",
			ByArith(complex_abs.AbsOfReal.At(one)))
		squareBound := a.Have(
			"the squared sequence is bounded by one",
			"∀n:num. |«square»(n)| ≤ &1",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				z := b.TermAs[Complex]("f(n)")
				b.Show(
					"the square of the modulus is at most one",
					ByArith(bounded.At(n), complex_abs.AbsMul.At(z, z), complex_abs.AbsNonneg.At(z)))
			}))
		squareMultiplicative := a.Have(
			"squaring preserves complete multiplicativity",
			"∀m n:num. 0 < m ∧ 0 < n ⇒ «square»(m * n) = «square»(m) * «square»(n)",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				n := b.FixAs[Nat]("n")
				positive := b.Assume()
				factors := b.Have(
					"f is multiplicative on the positive indices",
					"f(m * n) = f(m) * f(n)",
					By(positive, multiplicative.At(m, n)))
				b.Show(
					"square both factors and commute them",
					Simp(Fwd(factors)),
					ByArith())
			}))
		squareFirst := a.Have(
			"the squared sequence has first value one",
			"«square»(1) = complex_of_real(&1)",
			Simp(Fwd(first)),
			ByArith())
		threeFourOne := a.Have(
			"the combination of real parts is nonnegative on the closed unit disc",
			"∀u:complex. |u| ≤ &1 ⇒ &0 ≤ «threeFourOne»(u)",
			Derive(func(b *Argument) {
				u := b.FixAs[Complex]("u")
				unit := b.Assume()
				modulus := b.TermAs[Real]("|u|")
				squared := b.Have(
					"the squared modulus is at most one",
					"|u| * |u| ≤ &1",
					By(unit, complex_abs.AbsNonneg.At(u), real_order_ring.LessEqMul2.At(modulus, one, modulus, one)))
				b.Show(
					"the combination equals twice the square of 1 + Re u plus 1 minus the squared modulus",
					ByArith(
						squared,
						complex_abs.AbsSquare.At(u),
						complex_field.PartsMul.At(u, u),
						real_order_ring.SquareNonneg.At(b.TermAs[Real]("&1 + re(u)"))))
			}))
		project := a.Have(
			"real factors can be moved outside the real part",
			"∀a b:real. ∀u:complex. re((complex_of_real(a) * u) * complex_of_real(b)) = (a * b) * re(u)",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("a")
				y := b.FixAs[Real]("b")
				u := b.FixAs[Complex]("u")
				b.Show(
					"the embedded factors have zero imaginary part",
					ByArith(
						complex_field.PartsOfReal.At(x),
						complex_field.PartsOfReal.At(y),
						complex_field.PartsMul.At(b.TermAs[Complex]("complex_of_real(a)"), u),
						complex_field.PartsMul.At(b.TermAs[Complex]("complex_of_real(a) * u"),
							b.TermAs[Complex]("complex_of_real(b)"))))
			}))
		nonnegativeTerms := a.Have(
			"each term of the combined real series is nonnegative",
			"∀n:num. &0 ≤ «combinedTerms»(n)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				k := b.TermAs[Nat]("n + 1")
				base := b.TermAs[Real]("real_of_num(n + 1)")
				negativeExponent := b.TermAs[Real]("-σ")
				ratio := b.TermAs[Real]("«ratio»(n + 1)")
				power := b.TermAs[Real]("real_rpow(&(n + 1), -σ)")
				weight := b.TermAs[Real]("«ratio»(n + 1) * real_rpow(&(n + 1), -σ)")
				u := b.TermAs[Complex]("f(n + 1)")
				positiveBase := b.Have(
					"the base is positive",
					"&0 < real_of_num(n + 1)",
					ByArith())
				realPower := b.Have(
					"the Dirichlet power is real",
					"complex_cpow(&(n + 1), -complex_of_real(σ)) = complex_of_real(real_rpow(&(n + 1), -σ))",
					By(
						positiveBase,
						complex_field.OfRealNeg.At(σ),
						complex_cpow.CpowRealExponent.At(base, negativeExponent)))
				weightNonnegative := b.Have(
					"the Mangoldt ratio and the real power have nonnegative product",
					"&0 ≤ «ratio»(n + 1) * real_rpow(&(n + 1), -σ)",
					By(
						ratioBounds.At(k),
						real_rpow.RpowNonneg.At(base, negativeExponent),
						real_construction.LessEqMul.At(ratio, power)))
				weighted := b.Have(
					"multiply the unit-disc inequality by the common weight",
					"&0 ≤ («ratio»(n + 1) * real_rpow(&(n + 1), -σ)) * «threeFourOne»(f(n + 1))",
					By(
						weightNonnegative,
						bounded.At(k),
						threeFourOne.At(u),
						real_construction.LessEqMul.At(weight, b.TermAs[Real]("«threeFourOne»(f(n + 1))"))))
				unitTerm := b.Have(
					"the logarithmic term for the constant one has real part equal to the weight",
					"re((complex_of_real(«ratio»(n + 1)) * complex_of_real(&1)) * "+
						"    complex_of_real(real_rpow(&(n + 1), -σ))) = "+
						"«ratio»(n + 1) * real_rpow(&(n + 1), -σ)",
					ByArith(project.At(ratio, power, oneComplex), complex_field.PartsOfReal.At(one)))
				b.Show(
					"the three projected terms combine into the weighted unit-disc expression",
					Simp(Fwd(realPower)),
					ByArith(
						weighted,
						unitTerm,
						project.At(ratio, power, u),
						project.At(ratio, power, b.TermAs[Complex]("«square»(n + 1)"))))
			}))
		logSeriesF := a.TermAs[Complex]("«logSeries»(f)")
		logSeriesSquare := a.TermAs[Complex]("«logSeries»(«square»)")
		x := a.TermAs[Real]("re(«logSeries»(«ones»))")
		y := a.TermAs[Real]("re(«logSeries»(f))")
		z := a.TermAs[Real]("re(«logSeries»(«square»))")
		three := a.TermAs[Real]("&3")
		four := a.TermAs[Real]("&4")
		threeTerms := a.TermAs[Fun[Nat, Real]]("«threeTerms»")
		fourTerms := a.TermAs[Fun[Nat, Real]]("«fourTerms»")
		squareTerms := a.TermAs[Fun[Nat, Real]]("«realTerms»(«square»)")
		threeSum := a.TermAs[Real]("«threeSum»")
		fourSum := a.TermAs[Real]("«fourSum»")
		bothSum := a.TermAs[Real]("«threeSum» + «fourSum»")
		total := a.TermAs[Real]("«combinedSum»")
		sumThree := a.Have(
			"three times the real series for the constant one has the scaled sum",
			"real_sums(«threeTerms», «threeSum»)",
			By(
				onesBound,
				realSums.At(ones),
				real_series.SumsScale.At(a.TermAs[Fun[Nat, Real]]("«realTerms»(«ones»)"), x, three)))
		sumFour := a.Have(
			"four times the real series for f has the scaled sum",
			"real_sums(«fourTerms», «fourSum»)",
			By(
				bounded,
				realSums.At(f),
				real_series.SumsScale.At(a.TermAs[Fun[Nat, Real]]("«realTerms»(f)"), y, four)))
		sumBoth := a.Have(
			"add the first two scaled series",
			"real_sums(«bothTerms», «threeSum» + «fourSum»)",
			By(sumThree, sumFour, real_series.SumsAdd.At(threeTerms, fourTerms, threeSum, fourSum)))
		sumAll := a.Have(
			"add the real series for the square to get the combined sum",
			"real_sums(«combinedTerms», «combinedSum»)",
			By(
				sumBoth,
				squareBound,
				realSums.At(square),
				real_series.SumsAdd.At(
					a.TermAs[Fun[Nat, Real]]("«bothTerms»"), squareTerms, bothSum, z)))
		totalNonnegative := a.Have(
			"the combined sum is nonnegative by termwise comparison with the zero series",
			"&0 ≤ «combinedSum»",
			By(
				nonnegativeTerms,
				sumAll,
				real_series.SumsZero,
				real_series.SumsLessEq.At(
					a.TermAs[Fun[Nat, Real]]("λn:num. &0"),
					a.TermAs[Fun[Nat, Real]]("«combinedTerms»"),
					zero,
					total)))
		zetaModulus := a.Have(
			"the zeta modulus is the exponential of the real part of its logarithmic series",
			"|riemann_zeta(&σ)| = exp(re(«logSeries»(«ones»)))",
			Simp(Fwd(comm_monoid.RightIdentity.Read(complex_field.MulMonoid))),
			By(
				right,
				ZetaExponential.At(s),
				complex_power_series.AbsExp.At(
					a.TermAs[Complex]("dirichlet_series(λn:num. &(von_mangoldt(n) / log(&n)), &σ)"))))
		fModulus := a.Have(
			"the modulus for f is the exponential of the real part of its logarithmic series",
			"|dirichlet_series(f, &σ)| = exp(re(«logSeries»(f)))",
			By(
				multiplicative,
				first,
				bounded,
				right,
				dirichlet_series.LogarithmicSeries.At(f, s),
				complex_power_series.AbsExp.At(logSeriesF)))
		squareModulus := a.Have(
			"the same exponential formula holds for the squared coefficients",
			"|dirichlet_series(«square», &σ)| = exp(re(«logSeries»(«square»)))",
			By(
				squareMultiplicative,
				squareFirst,
				squareBound,
				right,
				dirichlet_series.LogarithmicSeries.At(square, s),
				complex_power_series.AbsExp.At(logSeriesSquare)))
		expLower := a.Have(
			"the exponential of the combined sum is at least one",
			"&1 ≤ exp(«combinedSum»)",
			ByArith(totalNonnegative, real_exp_log.ExpLowerBound.At(total)))
		exponentiated := a.Have(
			"exponentiating the combined sum gives the product of the three modulus factors",
			"exp(«combinedSum») = "+
				"|riemann_zeta(&σ)| ^ 3 * |dirichlet_series(f, &σ)| ^ 4 * |dirichlet_series(«square», &σ)|",
			By(
				zetaModulus,
				fModulus,
				squareModulus,
				real_exp_log.ExpAdd.At(threeSum, fourSum),
				real_exp_log.ExpAdd.At(bothSum, z),
				real_exp_log.ExpNatMul.At(a.TermAs[Nat]("3"), x),
				real_exp_log.ExpNatMul.At(a.TermAs[Nat]("4"), y)))
		a.Show(
			"the product of moduli is at least one",
			By(expLower, exponentiated))
	}),
	Reading: "One inequality serves ζ and every Dirichlet character. At f(n) = " +
		"n^(−it) it is ζ(σ)³·|ζ(σ + it)|⁴·|ζ(σ + 2it)| ≥ 1, which is ZetaMertens; " +
		"at a character χ the middle factor is L(σ, χ) and the last L(σ, χ²).",
})}

// ZetaMertens — the 3-4-1 inequality for ζ: at a real σ > 1 and a v on
// the imaginary axis, |ζ(σ)|³·|ζ(σ + v)|⁴·|ζ(σ + 2v)| ≥ 1. It is
// MertensInequality at the phase n^(−v), whose series and the series of
// its square ZetaShift reads as ζ at σ + v and at σ + 2v.
var ZetaMertens = zetaMertensThm{family.Add(registry.ProofEntry{
	Name: "ZetaMertens",
	Key:  "prop_95c1ed7624046c56",
	Build: family.Theorem(Statement{
		Binders: "∀v:complex. ∀σ:real.",
		Hypotheses: []string{
			"re(v) = &0",
			"&1 < σ",
		},
		Conclusion: "&1 ≤ " +
			"|riemann_zeta(&σ)| ^ 3 * |riemann_zeta(&σ + v)| ^ 4 * |riemann_zeta(&σ + &2 * v)|",
		Abbrev: Abbrev{
			{Name: "phase", Text: "λn:num. complex_cpow(&n, -v)"},
			{Name: "phaseSquare", Text: "λn:num. «phase»(n) * «phase»(n)"},
		},
	}, func(a *Argument, v *Expr[Complex], σ *Expr[Real], imaginary, aboveOne Fact) {
		negV := a.TermAs[Complex]("-v")
		twoV := a.TermAs[Complex]("&2 * v")
		s := a.TermAs[Complex]("complex_of_real(σ)")
		phase := a.TermAs[Fun[Nat, Complex]]("«phase»")
		phaseSquare := a.TermAs[Fun[Nat, Complex]]("«phaseSquare»")
		multiplicative := a.Have(
			"the phase is completely multiplicative on positive indices",
			"∀m n:num. 0 < m ∧ 0 < n ⇒ «phase»(m * n) = «phase»(m) * «phase»(n)",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				n := b.FixAs[Nat]("n")
				positive := b.Assume()
				bases := b.Have(
					"the embedded bases are positive",
					"&0 < real_of_num(m) ∧ &0 < real_of_num(n)",
					ByArith(positive))
				b.Show(
					"powers of products of positive bases factor",
					By(
						bases,
						real_construction.OfNumMul.At(m, n),
						complex_cpow.CpowMulPositive.At(
							b.TermAs[Real]("real_of_num(m)"), b.TermAs[Real]("real_of_num(n)"), negV)))
			}))
		first := a.Have(
			"the phase at 1 is 1",
			"«phase»(1) = &1",
			By(complex_cpow.CpowOneBase.At(negV)))
		negativeRe := a.Have(
			"negating v keeps zero real part",
			"re(-v) = &0",
			ByArith(imaginary, complex_field.PartsNeg.At(v)))
		bounded := a.Have(
			"every phase coefficient has modulus at most one",
			"∀n:num. |«phase»(n)| ≤ &1",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Cases(b.TermAs[Bool]("n = 0"))
				b.When(
					"at zero the value is a power of zero",
					func(c *Argument, indexZero Fact) {
						value := c.Have(
							"a power of zero is 1 at the exponent 0 and 0 at any other, of modulus at most one",
							"|complex_cpow(complex_of_real(&0), -v)| ≤ &1",
							Simp(Fwd(complex_cpow.ComplexCpowDef)),
							CondRewrite(),
							ByArith())
						c.Show(
							"the phase at zero is that power",
							ByArith(indexZero, value))
					})
				b.Otherwise(
					"at a positive index the phase has modulus one",
					func(c *Argument, indexNonzero Fact) {
						positive := c.Have(
							"the index is positive",
							"0 < n",
							ByArith(indexNonzero))
						base := c.TermAs[Real]("real_of_num(n)")
						basePositive := c.Have(
							"the embedded base is positive",
							"&0 < real_of_num(n)",
							ByArith(positive))
						c.Show(
							"the real power giving the modulus has exponent zero",
							ByArith(
								basePositive,
								negativeRe,
								complex_cpow.AbsCpow.At(base, negV),
								real_rpow.RpowZeroExponent.At(base)))
					})
			}))
		phaseAtPositive := a.Have(
			"the phase restated in the guarded form ZetaShift's hypothesis takes",
			"∀n:num. 0 < n ⇒ «phase»(n) = complex_cpow(&n, -v)",
			ByArith())
		squareAtPositive := a.Have(
			"the squared phase is n^(−2v) at a positive index",
			"∀n:num. 0 < n ⇒ «phaseSquare»(n) = complex_cpow(&n, -(&2 * v))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				positive := b.Assume()
				base := b.Have(
					"the embedded base is positive",
					"&0 < real_of_num(n)",
					ByArith(positive))
				exponent := b.Have(
					"the exponent doubles",
					"-v + -v = -(&2 * v)",
					ByArith())
				b.Show(
					"squaring adds the exponent to itself",
					By(base, exponent, complex_cpow.CpowAdd.At(b.TermAs[Real]("real_of_num(n)"), negV, negV)))
			}))
		doubleRe := a.Have(
			"the doubled shift also has zero real part",
			"re(&2 * v) = &0",
			ByArith(
				imaginary,
				complex_field.PartsMul.At(a.TermAs[Complex]("complex_of_real(&2)"), v),
				complex_field.PartsOfReal.At(a.TermAs[Real]("&2"))))
		right := a.Have(
			"both shifted points lie to the right of the line Re s = 1",
			"&1 < re(complex_of_real(σ) + v) ∧ &1 < re(complex_of_real(σ) + &2 * v)",
			ByArith(
				aboveOne,
				imaginary,
				doubleRe,
				complex_field.PartsAdd.At(s, v),
				complex_field.PartsAdd.At(s, twoV),
				complex_field.PartsOfReal.At(σ)))
		instance := a.Have(
			"Mertens' inequality at the phase",
			"&1 ≤ "+
				"|riemann_zeta(&σ)| ^ 3 * "+
				"|dirichlet_series(«phase», &σ)| ^ 4 * "+
				"|dirichlet_series(«phaseSquare», &σ)|",
			By(multiplicative, first, bounded, aboveOne, MertensInequality.At(phase, σ)))
		shiftOne := a.Have(
			"the series of the phase is ζ at σ + v",
			"dirichlet_series(«phase», &σ) = riemann_zeta(complex_of_real(σ) + v)",
			By(phaseAtPositive, right, ZetaShift.At(phase, v, s)))
		shiftTwo := a.Have(
			"the series of the squared phase is ζ at σ + 2v",
			"dirichlet_series(«phaseSquare», &σ) = riemann_zeta(complex_of_real(σ) + &2 * v)",
			By(squareAtPositive, right, ZetaShift.At(phaseSquare, twoV, s)))
		a.Show(
			"read the two series as the shifted ζ values",
			Simp(Rev(shiftOne), Rev(shiftTwo)),
			By(instance))
	}),
})}

// ZetaRealBounds — at a real σ > 1, ζ(σ) is the nonnegative real |ζ(σ)|,
// which lies between 1 and 1 + 1/(σ − 1): at σ the ζ series is the series
// of the real powers (n + 1)^(−σ) embedded in ℂ, whose sum t is at least
// its first term 1 and at most 1 + 1/(σ − 1), so ζ(σ) is the embedded t,
// and t, being nonnegative, is its own modulus.
var ZetaRealBounds = zetaRealBoundsThm{family.Add(registry.ProofEntry{
	Name: "ZetaRealBounds",
	Key:  "prop_f432ccddc368227f",
	Build: family.Theorem(Statement{
		Binders:    "∀σ:real.",
		Hypotheses: []string{"&1 < σ"},
		Conclusion: "riemann_zeta(&σ) = complex_of_real(|riemann_zeta(&σ)|) ∧ " +
			"&1 ≤ |riemann_zeta(&σ)| ∧ " +
			"|riemann_zeta(&σ)| ≤ &1 + &1 / (σ - &1)",
		Abbrev: Abbrev{
			{Name: "powerTerms", Text: "λσ:real. λn:num. real_rpow(&(n + 1), -σ)"},
			{Name: "tailTerms", Text: "λσ:real. λn:num. real_rpow(&(n + 1 + 1), -σ)"},
			{Name: "zetaTerms", Text: "λσ:real. λn:num. " +
				"    complex_of_real(&1) * complex_cpow(complex_of_real(&(n + 1)), -complex_of_real(σ))"},
		},
	}, func(a *Argument, σ *Expr[Real], aboveOne Fact) {
		powers := a.TermAs[Fun[Nat, Real]]("«powerTerms»(σ)")
		t, realSum := a.ObtainAs[Real](
			"the real power series has a sum with the claimed upper bound",
			"∃t:real. real_sums(«powerTerms»(σ), t) ∧ t ≤ &1 + &1 / (σ - &1)",
			By(aboveOne, real_rpow.RpowSeriesConverges.At(σ)))
		first := a.Have(
			"the first power is 1",
			"real_rpow(&(0 + 1), -σ) = &1",
			By(real_rpow.RpowOneBase.At(a.TermAs[Real]("-σ"))))
		tail := a.TermAs[Fun[Nat, Real]]("«tailTerms»(σ)")
		tailSum := a.Have(
			"removing the first term leaves the sum t − 1",
			"real_sums(«tailTerms»(σ), t - &1)",
			By(realSum, first, real_series.SumsShift.At(powers, t)))
		nonnegative := a.Have(
			"each remaining term is nonnegative",
			"∀n:num. &0 ≤ «tailTerms»(σ, n)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"real powers are nonnegative",
					By(real_rpow.RpowNonneg.At(b.TermAs[Real]("&(n + 1 + 1)"), b.TermAs[Real]("-σ"))))
			}))
		lower := a.Have(
			"the nonnegative tail gives 1 ≤ t",
			"&1 ≤ t",
			ByArith(
				nonnegative,
				tailSum,
				real_series.SumsZero,
				real_series.SumsLessEq.At(
					a.TermAs[Fun[Nat, Real]]("λn:num. &0"), tail,
					a.TermAs[Real]("&0"), a.TermAs[Real]("t - &1"))))
		terms := a.Have(
			"at a real point the ζ series consists of embedded real powers",
			"«zetaTerms»(σ) = (λn:num. complex_of_real(«powerTerms»(σ, n)))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				positive := b.Have(
					"the base n + 1 is positive",
					"&0 < real_of_num(n + 1)",
					ByArith(real_order_ring.OfNumLessThan.At(b.TermAs[Nat]("0"), b.TermAs[Nat]("n + 1"))))
				b.Show(
					"apply the law for a real exponent, its guard the positive base",
					Simp(
						Fwd(comm_monoid.LeftIdentity.Read(complex_field.MulMonoid)),
						Rev(complex_field.OfRealNeg),
						Fwd(complex_cpow.CpowRealExponent),
						Fwd(positive)),
					Refl())
			}))
		s := a.TermAs[Complex]("complex_of_real(σ)")
		series := a.TermAs[Fun[Nat, Complex]]("«zetaTerms»(σ)")
		zetaSum := a.Have(
			"the defining sum at this point is ζ(σ)",
			"complex_sums(«zetaTerms»(σ), riemann_zeta(complex_of_real(σ)))",
			By(
				aboveOne,
				complex_field.PartsOfReal.At(σ),
				ZetaSums.At(s),
				dirichlet_series.DirichletSumsDef.At(
					a.TermAs[Fun[Nat, Complex]]("λn:num. complex_of_real(&1)"), s,
					a.TermAs[Complex]("riemann_zeta(complex_of_real(σ))"))))
		realValue := a.Have(
			"the embedded real sum is also a sum of the ζ terms",
			"complex_sums(«zetaTerms»(σ), complex_of_real(t))",
			By(terms, realSum, complex_series.SumsOfReal.At(powers, t)))
		value := a.Have(
			"uniqueness identifies ζ(σ) with the real sum",
			"riemann_zeta(complex_of_real(σ)) = complex_of_real(t)",
			By(
				zetaSum,
				realValue,
				complex_series.SumsUnique.At(
					series,
					a.TermAs[Complex]("riemann_zeta(complex_of_real(σ))"),
					a.TermAs[Complex]("complex_of_real(t)"))))
		modulus := a.Have(
			"ζ(σ) is the embedded t, and t, being at least 1, is its own modulus",
			"|riemann_zeta(complex_of_real(σ))| = t",
			Simp(Fwd(value)),
			ByArith(lower, complex_abs.AbsOfNonnegReal.At(t)))
		a.Show(
			"ζ(σ) is the embedded real t, its modulus, which lies between 1 and the upper bound",
			Simp(Fwd(modulus)),
			By(value, lower, realSum))
	}),
	Reading: "The first conjunct says that ζ(σ) is a nonnegative real: a complex number " +
		"is the embedding of its own modulus exactly when it is real and at least 0. So " +
		"im(ζ(σ)) = 0 and re(ζ(σ)) = |ζ(σ)|, and the two bounds hold of the real part as well.",
})}

// MertensNonvanishing — a function F that meets the 3-4-1 lower bound
// 1 ≤ |ζ(σ)|³·|F(σ)|⁴·|G(σ)| at every real σ > 1, F differentiable at 1
// and G continuous there, does not vanish at 1. At σ = 1 + h a zero makes
// |F(σ)| at most C·h, continuity bounds |G(σ)| by D, and the pole bounds
// |ζ(σ)| by 1 + 1/h, so the product is at most M·h: below 1 for h small,
// against its lower bound 1.
var MertensNonvanishing = mertensNonvanishingThm{family.Add(registry.ProofEntry{
	Name: "MertensNonvanishing",
	Key:  "prop_698b075e44eee934",
	Build: family.Theorem(Statement{
		Binders: "∀F G:(complex → complex). ∀l:complex.",
		Hypotheses: []string{
			"∀σ:real. &1 < σ ⇒ &1 ≤ |riemann_zeta(&σ)| ^ 3 * |F(&σ)| ^ 4 * |G(&σ)|",
			"complex_derivative_at(F, &1, l)",
			"complex_continuous_at(G, &1)",
		},
		Conclusion: "F(&1) ≠ &0",
	}, func(
		a *Argument,
		F, G *Arrow[Complex, Complex],
		l *Expr[Complex],
		mertens, derivative, continuous Fact,
	) {
		one := a.TermAs[Real]("&1")
		zero := a.TermAs[Real]("&0")
		centre := a.TermAs[Complex]("complex_of_real(&1)")
		zeroComplex := a.TermAs[Complex]("complex_of_real(&0)")
		triangle := a.Have(
			"the modulus of a point is at most its distance to another point plus that point's modulus",
			"∀u v:complex. |u| ≤ |u - v| + |v|",
			Derive(func(b *Argument) {
				u := b.FixAs[Complex]("u")
				v := b.FixAs[Complex]("v")
				zeroSub := b.Have(
					"subtracting zero fixes both points",
					"u - complex_of_real(&0) = u ∧ v - complex_of_real(&0) = v",
					ByArith())
				b.Show(
					"take zero as the third point of the triangle",
					By(Normalized, zeroSub, complex_abs.AbsSubTriangle.At(u, v, zeroComplex)))
			}))
		r, derivativeDisc := a.ObtainAs[Real](
			"take a derivative remainder with error at most the displacement",
			"∃r:real. "+
				"    &0 < r ∧ "+
				"    ∀z:complex. &0 < |z - &1| ∧ |z - &1| < r ⇒ |F(z) - F(&1) - l * (z - &1)| < &1 * |z - &1|",
			By(
				derivative,
				real_order_ring.ZeroLessThanOne,
				complex_derivative.DerivativeIncrement.At(F, centre, l)),
			Named("r"))
		derivativeParts := a.Conjuncts(
			derivativeDisc,
			"the derivative radius is positive",
			"the derivative remainder bound")
		R, continuityDisc := a.ObtainAs[Real](
			"within a disc G differs from its value at 1 by less than one",
			"∃R:real. &0 < R ∧ ∀z:complex. |z - &1| < R ⇒ |G(z) - G(&1)| < &1",
			By(
				continuous,
				real_order_ring.ZeroLessThanOne,
				complex_topology.ComplexContinuousAtDef.At(G, centre)),
			Named("R"))
		continuityParts := a.Conjuncts(
			continuityDisc,
			"the continuity radius is positive",
			"the continuity estimate")
		C, cDef := a.LetAs[Real]("C", "|l| + &1")
		D, dDef := a.LetAs[Real]("D", "|G(&1)| + &1")
		// M is the constant of the upper bound below: (AB)³·B·E ≤ (2C)³·(C·h)·D = M·h.
		M, mDef := a.LetAs[Real]("M", "(&2 * C) ^ 3 * C * D")
		three := a.TermAs[Nat]("3")
		constantsPositive := a.Have(
			"the two local bounds have positive constants",
			"&0 < C ∧ &0 < D ∧ &0 < &2 * C",
			ByArith(cDef, dDef))
		MPositive := a.Have(
			"the product bound has positive coefficient",
			"&0 < M",
			By(
				mDef,
				constantsPositive,
				real_pow.PowPos.At(a.TermAs[Real]("&2 * C"), three),
				real_order_ring.MulPos.At(a.TermAs[Real]("(&2 * C) ^ 3"), C),
				real_order_ring.MulPos.At(a.TermAs[Real]("(&2 * C) ^ 3 * C"), D)))
		cutoff := a.TermAs[Real]("real_inv(M)")
		innerMin := a.TermAs[Real]("min(&1, real_inv(M))")
		middleMin := a.TermAs[Real]("min(R, min(&1, real_inv(M)))")
		_, ρDef := a.LetAs[Real]("ρ", "min(r, min(R, min(&1, real_inv(M))))")
		h, hDef := a.LetAs[Real]("h", "ρ / &2")
		ρPositive := a.Have(
			"the smaller of the radii, one and the reciprocal product coefficient is positive",
			"&0 < ρ",
			By(
				ρDef,
				derivativeParts[0],
				continuityParts[0],
				MPositive,
				real_order_ring.ZeroLessThanOne,
				real_order_field.InvPos.At(M),
				real_sup_inf.LessThanMin.At(r, middleMin, zero),
				real_sup_inf.LessThanMin.At(R, innerMin, zero),
				real_sup_inf.LessThanMin.At(one, cutoff, zero)))
		half := a.Have(
			"half the minimum is positive and smaller than the minimum",
			"&0 < h ∧ h < ρ",
			ByArith(hDef, ρPositive))
		hBounds := a.Have(
			"the displacement fits both radii and the two numerical cutoffs",
			"&0 < h ∧ h < r ∧ h < R ∧ h < &1 ∧ h < real_inv(M)",
			By(
				ρDef,
				half,
				real_sup_inf.LessThanMin.At(r, middleMin, h),
				real_sup_inf.LessThanMin.At(R, innerMin, h),
				real_sup_inf.LessThanMin.At(one, cutoff, h)))
		σ, σDef := a.LetAs[Real]("σ", "&1 + h")
		A, aDef := a.LetAs[Real]("A", "|riemann_zeta(&σ)|")
		B, bDef := a.LetAs[Real]("B", "|F(&σ)|")
		E, eDef := a.LetAs[Real]("E", "|G(&σ)|")
		point := a.TermAs[Complex]("complex_of_real(σ)")
		σBounds := a.Have(
			"the real point exceeds one by h",
			"&1 < σ ∧ σ - &1 = h",
			ByArith(σDef, hBounds))
		distance := a.Have(
			"the real point is displaced by h to the right of 1",
			"|&σ - &1| = h",
			ByArith(σBounds, hBounds, complex_abs.AbsOfRealSub.At(σ, one)))
		atZero := a.SupposeNot()
		firstBound := a.Have(
			"the modulus of F at the real point is at most C times the displacement",
			"B ≤ C * h",
			Derive(func(b *Argument) {
				delta := b.TermAs[Complex]("&σ - &1")
				linear := b.TermAs[Complex]("l * (&σ - &1)")
				remainder := b.Have(
					"the derivative remainder has modulus less than h",
					"|F(&σ) - F(&1) - l * (&σ - &1)| < h",
					ByArith(hBounds, distance, derivativeParts[1].At(point)))
				dropZero := b.Have(
					"with F(1) = 0 the remainder loses its centre value",
					"F(&σ) - F(&1) - l * (&σ - &1) = F(&σ) - l * (&σ - &1)",
					ByArith(atZero))
				errorBound := b.Have(
					"the derivative error uses only the value at the real point",
					"|F(&σ) - l * (&σ - &1)| < h",
					By(remainder, dropZero))
				linearSize := b.Have(
					"the derivative term has modulus its coefficient's modulus times h",
					"|l * (&σ - &1)| = |l| * h",
					By(distance, complex_abs.AbsMul.At(l, delta)))
				b.Show(
					"add the derivative error and the size of the linear term",
					Simp(Fwd(bDef)),
					ByArith(triangle.At(b.TermAs[Complex]("F(&σ)"), linear), errorBound, linearSize, Scaled(h, cDef)))
			}))
		secondBound := a.Have(
			"the modulus of G at the real point is at most D",
			"E ≤ D",
			Simp(Fwd(eDef)),
			ByArith(
				continuityParts[1].At(point),
				distance,
				hBounds,
				dDef,
				triangle.At(a.TermAs[Complex]("G(&σ)"), a.TermAs[Complex]("G(&1)"))))
		realModulus := a.Have(
			"the modulus of zeta at the real point is at most one plus the inverse displacement",
			"A ≤ &1 + &1 / h",
			Simp(Fwd(aDef)),
			By(Normalized, σBounds, ZetaRealBounds.At(σ)))
		poleBound := a.Have(
			"multiplying the real modulus by h bounds it by two",
			"A * h ≤ &2",
			ByArith(
				realModulus,
				hBounds,
				field.DivRightMul.Read(real_field.Field).At(one, h),
				real_order_ring.LessEqMulRight.At(A, a.TermAs[Real]("&1 + &1 / h"), h)))
		moduli := a.Have(
			"all three moduli are nonnegative",
			"&0 ≤ A ∧ &0 ≤ B ∧ &0 ≤ E",
			ByArith(aDef, bDef, eDef))
		AB := a.TermAs[Real]("A * B")
		twoC := a.TermAs[Real]("&2 * C")
		AB3 := a.TermAs[Real]("(A * B) ^ 3")
		twoC3 := a.TermAs[Real]("(&2 * C) ^ 3")
		productAB := a.Have(
			"the zero of F cancels one pole factor",
			"A * B ≤ &2 * C",
			ByArith(
				firstBound,
				poleBound,
				moduli,
				constantsPositive,
				real_order_ring.LessEqMulLeft.At(A, B, a.TermAs[Real]("C * h")),
				real_order_ring.LessEqMulLeft.At(C, a.TermAs[Real]("A * h"), a.TermAs[Real]("&2"))))
		ABNonnegative := a.Have(
			"the first two moduli have nonnegative product",
			"&0 ≤ A * B",
			By(moduli, real_construction.LessEqMul.At(A, B)))
		cubed := a.Have(
			"bound the cube of the paired factors and multiply by the remaining modulus of F",
			"(A * B) ^ 3 * B ≤ (&2 * C) ^ 3 * (C * h)",
			By(
				productAB,
				ABNonnegative,
				moduli,
				firstBound,
				real_pow.PowNonneg.At(AB, three),
				real_pow.PowMonoBase.At(AB, twoC, three),
				real_order_ring.LessEqMul2.At(AB3, twoC3, B, a.TermAs[Real]("C * h"))))
		cubedNonnegative := a.Have(
			"the partial product is nonnegative",
			"&0 ≤ (A * B) ^ 3 * B",
			By(moduli, ABNonnegative, real_pow.PowNonneg.At(AB, three), real_construction.LessEqMul.At(AB3, B)))
		upper := a.Have(
			"multiplying by the final modulus bounds the entire product by M times h",
			"(A * B) ^ 3 * B * E ≤ M * h",
			ByArith(
				cubed,
				secondBound,
				moduli,
				cubedNonnegative,
				Scaled(h, mDef),
				real_order_ring.LessEqMul2.At(
					a.TermAs[Real]("(A * B) ^ 3 * B"),
					a.TermAs[Real]("(&2 * C) ^ 3 * (C * h)"),
					E,
					D)))
		small := a.Have(
			"the displacement was chosen so that M times h is strictly below one",
			"M * h < &1",
			ByArith(
				MPositive,
				hBounds,
				field.MulLeftInverse.Read(real_field.Field).At(M),
				real_order_ring.NonzeroOfPositive.At(M),
				real_order_ring.LessThanMulRightEq.At(h, cutoff, M)))
		factor := a.Have(
			"pair three of the four factors of F with the three of zeta",
			"A ^ 3 * B ^ 4 * E = (A * B) ^ 3 * B * E",
			ByArith(real_pow.MulPowDistrib.At(A, B, three), real_pow.PowAddOne.At(B, three)))
		lower := a.Have(
			"the 3-4-1 bound puts the same product at least one",
			"&1 ≤ A ^ 3 * B ^ 4 * E",
			By(Normalized, σBounds, aDef, bDef, eDef, mertens.At(σ)))
		a.Show(
			"the two product bounds contradict each other",
			ByArith(lower, factor, upper, small))
	}),
	Reading: "The count is 4 against 3: a zero of F at 1 makes |F(σ)|⁴ of " +
		"order (σ − 1)⁴, the pole of ζ makes |ζ(σ)|³ of order (σ − 1)⁻³, and " +
		"G stays bounded, so the product tends to 0 and cannot stay at least 1.",
})}

// ZetaNonzeroOnLine — ζ has no zero on the line Re s = 1. Write s = 1 + v
// with v ≠ 0 on the imaginary axis. The translate ζ(· + v) has a derivative
// at 1, where its value is ζ(s); the translate ζ(· + 2v) is continuous at 1,
// since 1 + 2v is not the pole; and ZetaMertens is the 3-4-1 bound for the
// two, so MertensNonvanishing gives ζ(s) ≠ 0.
var ZetaNonzeroOnLine = zetaNonzeroOnLineThm{family.Add(registry.ProofEntry{
	Name: "ZetaNonzeroOnLine",
	Key:  "prop_a9826cd23e6089b8",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"re(s) = &1", "s ≠ &1"},
		Conclusion: "riemann_zeta(s) ≠ &0",
		Abbrev: Abbrev{
			{Name: "offset", Text: "s - complex_of_real(&1)"},
			{Name: "doubleOffset", Text: "&2 * «offset»"},
			{Name: "secondCentre", Text: "complex_of_real(&1) + «doubleOffset»"},
			{Name: "domain", Text: "{z:complex | &0 < re(z) ∧ z ≠ &1}"},
		},
	}, func(a *Argument, s *Expr[Complex], onLine, away Fact) {
		one := a.TermAs[Real]("&1")
		zero := a.TermAs[Real]("&0")
		oneComplex := a.TermAs[Complex]("complex_of_real(&1)")
		zeroComplex := a.TermAs[Complex]("complex_of_real(&0)")
		offset := a.TermAs[Complex]("«offset»")
		doubleOffset := a.TermAs[Complex]("«doubleOffset»")
		two := a.TermAs[Complex]("complex_of_real(&2)")
		secondCentre := a.TermAs[Complex]("«secondCentre»")
		domain := a.TermAs[Set[Complex]]("«domain»")
		zeta := a.TermAs[Fun[Complex, Complex]]("riemann_zeta")
		identity := a.TermAs[Fun[Complex, Complex]]("λz:complex. z")
		offsetRe := a.Have(
			"the offset from 1 has zero real part",
			"re(«offset») = &0",
			ByArith(onLine, complex_field.PartsSub.At(s, oneComplex), complex_field.PartsOfReal.At(one)))
		offsetNonzero := a.Have(
			"the offset from 1 is nonzero",
			"«offset» ≠ complex_of_real(&0)",
			ByArith(away))
		doubleRe := a.Have(
			"the doubled offset also has zero real part",
			"re(«doubleOffset») = &0",
			ByArith(
				offsetRe,
				complex_field.PartsMul.At(two, offset),
				complex_field.PartsOfReal.At(a.TermAs[Real]("&2"))))
		firstIn := a.Have(
			"the first centre lies in the domain of holomorphy",
			"s ∈ «domain»",
			Derive(func(b *Argument) {
				points := b.Have(
					"the real part is positive and the point differs from 1",
					"&0 < re(s) ∧ s ≠ complex_of_real(&1)",
					ByArith(onLine, away))
				b.Show(
					"the two inequalities give membership",
					BySets(points))
			}))
		l, derivative := a.ObtainAs[Complex](
			"zeta has a derivative at the first centre",
			"∃l:complex. complex_derivative_at(riemann_zeta, s, l)",
			By(firstIn, ZetaHolomorphic, complex_derivative.HolomorphicOnDef.At(domain, zeta)),
			Named("l"))
		translation := a.TermAs[Fun[Complex, Complex]]("λz:complex. z + «offset»")
		translationDerivative := a.Have(
			"translation by the offset has derivative one",
			"complex_derivative_at(λz:complex. z + «offset», &1, &1)",
			ByArith(
				complex_derivative.DerivativeId.At(oneComplex),
				complex_derivative.DerivativeConst.At(oneComplex, offset),
				complex_derivative.DerivativeAdd.At(
					identity,
					a.TermAs[Fun[Complex, Complex]]("λz:complex. «offset»"),
					oneComplex,
					oneComplex,
					zeroComplex)))
		centre := a.Have(
			"translation by the offset takes 1 to s",
			"complex_of_real(&1) + «offset» = s",
			ByArith())
		translated := a.Have(
			"by the chain rule the translate of ζ has the derivative l at 1",
			"complex_derivative_at(λz:complex. riemann_zeta(z + «offset»), &1, l)",
			ByArith(
				translationDerivative,
				derivative,
				centre,
				complex_derivative.DerivativeChain.At(zeta, translation, oneComplex, l, oneComplex),
				functions.ComposeApply.At(zeta, translation)))
		secondIn := a.Have(
			"the second centre also lies in the domain of holomorphy",
			"«secondCentre» ∈ «domain»",
			Derive(func(b *Argument) {
				positive := b.Have(
					"the second centre has positive real part",
					"&0 < re(«secondCentre»)",
					ByArith(
						doubleRe,
						complex_field.PartsAdd.At(oneComplex, doubleOffset),
						complex_field.PartsOfReal.At(one)))
				translated := b.Have(
					"the displacement from 1 is twice the original displacement",
					"«secondCentre» - &1 = complex_of_real(&2) * «offset»",
					ByArith())
				twoNonzero := b.Have(
					"the complex image of 2 is nonzero",
					"complex_of_real(&2) ≠ complex_of_real(&0)",
					By(complex_field.OfRealInjective.At(b.TermAs[Real]("&2"), zero)))
				product := b.Have(
					"doubling a nonzero displacement gives a nonzero displacement",
					"complex_of_real(&2) * «offset» ≠ complex_of_real(&0)",
					By(twoNonzero, offsetNonzero, field.MulEqZero.Read(complex_field.Field).At(two, offset)))
				separate := b.Have(
					"the second centre differs from 1",
					"«secondCentre» ≠ complex_of_real(&1)",
					ByArith(translated, product))
				b.Show(
					"use the positive real part and the nonzero displacement",
					BySets(positive, separate))
			}))
		continuous := a.Have(
			"zeta is continuous at the second centre",
			"complex_continuous_at(riemann_zeta, «secondCentre»)",
			By(
				secondIn,
				ZetaHolomorphic,
				complex_derivative.HolomorphicOnContinuousAt.At(domain, zeta, secondCentre)))
		doubleTranslation := a.TermAs[Fun[Complex, Complex]]("λz:complex. z + «doubleOffset»")
		doubleTranslationContinuous := a.Have(
			"translation by the doubled offset is continuous at 1",
			"complex_continuous_at(λz:complex. z + «doubleOffset», &1)",
			By(
				complex_topology.ContinuousAtId.At(oneComplex),
				complex_topology.ContinuousAtConst.At(oneComplex, doubleOffset),
				complex_topology.ContinuousAtAdd.At(
					identity, a.TermAs[Fun[Complex, Complex]]("λz:complex. «doubleOffset»"), oneComplex)))
		doubleTranslated := a.Have(
			"the translate of ζ by the doubled offset is continuous at 1",
			"complex_continuous_at(λz:complex. riemann_zeta(z + «doubleOffset»), &1)",
			By(
				doubleTranslationContinuous,
				continuous,
				complex_topology.ContinuousAtCompose.At(zeta, doubleTranslation, oneComplex),
				functions.ComposeApply.At(zeta, doubleTranslation)))
		mertens := a.Have(
			"the 3-4-1 bound for the two translates at every real σ > 1",
			Statement{
				Binders:    "∀σ:real.",
				Hypotheses: []string{"&1 < σ"},
				Conclusion: "&1 ≤ " +
					"|riemann_zeta(&σ)| ^ 3 * |riemann_zeta(&σ + «offset»)| ^ 4 * |riemann_zeta(&σ + «doubleOffset»)|",
			},
			Derive(func(b *Argument) {
				σ := b.FixAs[Real]("σ")
				aboveOne := b.Assume()
				b.Show(
					"ZetaMertens at the offset",
					By(offsetRe, aboveOne, ZetaMertens.At(offset, σ)))
			}))
		a.Show(
			"the translate by the offset does not vanish at 1",
			By(
				mertens,
				translated,
				doubleTranslated,
				centre,
				MertensNonvanishing.At(
					a.TermAs[Fun[Complex, Complex]]("λz:complex. riemann_zeta(z + «offset»)"),
					a.TermAs[Fun[Complex, Complex]]("λz:complex. riemann_zeta(z + «doubleOffset»)"),
					l)))
	}),
	Reading: "s = 1 is excluded as the pole: there riemann_zeta is 0 by the " +
		"convention for a quotient by zero, so the statement would be false without " +
		"the exclusion. With ZetaNonzeroRight this is ζ ≠ 0 on the closed half-plane " +
		"Re s ≥ 1 off the pole, the fact the prime number theorem stands on.",
})}

// XiNonzero — «xi» has no zero on the closed half-plane Re s ≥ 1.
var XiNonzero = xiNonzeroThm{family.Add(registry.ProofEntry{
	Name: "XiNonzero",
	Key:  "prop_c4595b1dcae9d665",
	Build: family.Theorem(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&1 ≤ re(s)"},
		Conclusion: "«xi»(s) ≠ &0",
	}, func(a *Argument, s *Expr[Complex], halfPlane Fact) {
		a.Cases(a.TermAs[Bool]("s = complex_of_real(&1)"))
		a.When(
			"at 1 the regularized value is 1",
			func(b *Argument, atOne Fact) {
				b.Show(
					"the value there is nonzero",
					ByArith(atOne, XiAtOne))
			})
		a.Otherwise(
			"away from 1 use the nonvanishing of ζ",
			func(b *Argument, away Fact) {
				nonzero := b.Have(
					"ζ has no zero to the right of the line or on the line off 1",
					"riemann_zeta(s) ≠ complex_of_real(&0)",
					ByArith(away, halfPlane, ZetaNonzeroRight.At(s), ZetaNonzeroOnLine.At(s)))
				b.Show(
					"a quotient with zero numerator would vanish",
					ByArith(b.Unfolded(nonzero, RiemannZetaDef)))
			})
	}),
})}

// MangoldtSeriesContinuationOffZeros — the Dirichlet series of Λ, less
// 1/(s − 1), continues holomorphically to the open set «regularDomain» of
// Re s > 0 where ξ does not vanish, and that set contains 1. The
// continuation is g = −ξ′/ξ, since ζ = ξ/(s − 1) makes
// −ζ′/ζ = 1/(s − 1) − ξ′/ξ on Re s > 1; the set is open and ξ′/ξ is
// holomorphic on it (LogDerivativeHolomorphic), the set holds 1 since
// ξ(1) = 1, and holds Re s > 1 since there ξ is (s − 1)·ζ(s) with ζ(s) ≠ 0.
var MangoldtSeriesContinuationOffZeros = mangoldtSeriesContinuationOffZerosThm{family.Add(registry.ProofEntry{
	Name: "MangoldtSeriesContinuationOffZeros",
	Key:  "prop_8cb4405b86688a7c",
	Build: family.Theorem(Statement{
		Conclusion: "∃g:(complex → complex). " +
			"    «regularDomain» ∈ complex_topology ∧ " +
			"    complex_of_real(&1) ∈ «regularDomain» ∧ " +
			"    holomorphic_on(«regularDomain», g) ∧ " +
			"    ∀s:complex. " +
			"        &1 < re(s) ⇒ dirichlet_series(λn:num. &(von_mangoldt(n)), s) = complex_inv(s - &1) + g(s)",
		Abbrev: Abbrev{
			{Name: "halfPlane", Text: "{s:complex | &0 < re(s)}"},
			{Name: "radius", Text: "λr:real. λc:complex. re(c) - r"},
			{Name: "remainder", Text: "λh:(complex → complex). λs:complex. -(h(s) / «xi»(s))"},
			{Name: "shift", Text: "λs:complex. s - complex_of_real(&1)"},
			{Name: "product", Text: "λs:complex. «shift»(s) * riemann_zeta(s)"},
			{Name: "mangoldtValue", Text: "λs:complex. dirichlet_series(λn:num. &(von_mangoldt(n)), s)"},
			{Name: "productSlope", Text: "λs:complex. " +
				"    complex_of_real(&1) * riemann_zeta(s) + " +
				"    «shift»(s) * (-(riemann_zeta(s) * «mangoldtValue»(s)))"},
		},
	}, func(a *Argument) {
		S := a.TermAs[Set[Complex]]("«halfPlane»")
		U := a.TermAs[Set[Complex]]("«regularDomain»")
		xi := a.TermAs[Fun[Complex, Complex]]("«xi»")
		zeta := a.TermAs[Fun[Complex, Complex]]("riemann_zeta")
		oneComplex := a.TermAs[Complex]("complex_of_real(&1)")
		zeroComplex := a.TermAs[Complex]("complex_of_real(&0)")
		zeroReal := a.TermAs[Real]("&0")
		oneReal := a.TermAs[Real]("&1")
		fieldInverse := field.MulRightInverse.Read(complex_field.Field)
		realPart := a.Have(
			"a disc as wide as the real-part gap lies to the right of the given line",
			"∀r:real. ∀c w:complex. |w - c| < «radius»(r, c) ⇒ r < re(w)",
			Derive(func(b *Argument) {
				b.FixAs[Real]()
				c := b.FixAs[Complex]()
				w := b.FixAs[Complex]()
				near := b.Assume()
				b.Show(
					"the modulus of the displacement bounds its real part in absolute value",
					ByArith(near, complex_abs.PartsNonexpanding.At(w, c)))
			}))
		_, logarithmic := a.UnpackAs[Fun[Complex, Complex]](
			GroupPremises(
				complex_topology.RightHalfPlaneOpen.At(zeroReal),
				XiHolomorphic,
				cauchy_integral.LogDerivativeHolomorphic.At(S, xi)),
			"h")
		parts := a.Conjuncts(
			logarithmic,
			"h is the derivative of ξ on the half-plane",
			"the part of the half-plane where ξ does not vanish is open",
			"h / ξ is holomorphic there")
		holomorphic := a.Have(
			"the negative logarithmic derivative of ξ is holomorphic",
			"holomorphic_on(«regularDomain», «remainder»(h))",
			By(
				parts[2],
				complex_derivative.HolomorphicOnNeg.At(
					U, a.TermAs[Fun[Complex, Complex]]("λs:complex. h(s) / «xi»(s)"))))
		oneIn := a.Have(
			"ξ is 1 at 1, so 1 lies in the domain",
			"complex_of_real(&1) ∈ «regularDomain»",
			Derive(func(b *Argument) {
				inside := b.Have(
					"the real part of 1 is positive and ξ(1) = 1 is nonzero",
					"&0 < re(complex_of_real(&1)) ∧ «xi»(complex_of_real(&1)) ≠ complex_of_real(&0)",
					ByArith(XiAtOne, complex_field.PartsOfReal.At(oneReal)))
				b.Show(
					"these are the two conditions for membership",
					BySets(inside))
			}))
		nonzeroShift := a.Have(
			"the shift s minus one does not vanish to the right of one",
			"∀s:complex. &1 < re(s) ⇒ «shift»(s) ≠ complex_of_real(&0)",
			Derive(func(b *Argument) {
				s := b.FixAs[Complex]()
				right := b.Assume()
				realParts := b.Have(
					"the real part of the shift differs from the real part of zero",
					"re(«shift»(s)) ≠ re(complex_of_real(&0))",
					ByArith(
						right,
						complex_field.PartsSub.At(s, oneComplex),
						complex_field.PartsOfReal.At(oneReal),
						complex_field.PartsOfReal.At(zeroReal)))
				b.Show(
					"the shift differs from zero",
					By(Normalized, realParts))
			}))
		product := a.Have(
			"where s minus one is nonzero, multiplying zeta by it recovers ξ",
			"∀s:complex. «shift»(s) ≠ complex_of_real(&0) ⇒ «xi»(s) = «product»(s)",
			Derive(func(b *Argument) {
				b.FixAs[Complex]()
				away := b.Assume()
				shift := b.TermAs[Complex]("«shift»(s)")
				b.Show(
					"unfold zeta and cancel its denominator",
					Simp(Fwd(RiemannZetaDef), Fwd(complex_field.ComplexDivDef)),
					ByArith(away, At(fieldInverse, shift)))
			}))
		rightNonzero := a.Have(
			"to the right of one ξ is (s − 1)·ζ(s), a product of two nonzero factors",
			"∀s:complex. &1 < re(s) ⇒ «xi»(s) ≠ complex_of_real(&0)",
			Derive(func(b *Argument) {
				s := b.FixAs[Complex]()
				right := b.Assume()
				b.Show(
					"neither factor vanishes",
					By(
						right,
						nonzeroShift.At(s),
						product.At(s),
						ZetaNonzeroRight.At(s),
						field.MulEqZero.Read(complex_field.Field).At(
							b.TermAs[Complex]("«shift»(s)"), b.TermAs[Complex]("riemann_zeta(s)"))))
			}))
		agree := a.Have(
			"the negative logarithmic derivative is the Mangoldt series less its pole",
			"∀s:complex. &1 < re(s) ⇒ «mangoldtValue»(s) = complex_inv(«shift»(s)) + «remainder»(h, s)",
			Derive(func(b *Argument) {
				s := b.FixAs[Complex]()
				right := b.Assume()
				shift := b.TermAs[Fun[Complex, Complex]]("«shift»")
				prod := b.TermAs[Fun[Complex, Complex]]("«product»")
				slope := b.TermAs[Complex]("«productSlope»(s)")
				inside := b.Have(
					"s lies in the half-plane",
					"s ∈ «halfPlane»",
					ByArith(right))
				shiftDerivative := b.Have(
					"the shift s minus one has derivative one",
					"complex_derivative_at(«shift», s, complex_of_real(&1))",
					Derive(func(d *Argument) {
						oneMinusZero := d.Have(
							"one minus zero is one",
							"complex_of_real(&1) - complex_of_real(&0) = complex_of_real(&1)",
							ByArith())
						d.Show(
							"apply the difference rule to the identity and the constant one",
							By(
								oneMinusZero,
								complex_derivative.DerivativeId.At(s),
								complex_derivative.DerivativeConst.At(s, oneComplex),
								complex_derivative.DerivativeSub.At(d.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
									d.TermAs[Fun[Complex, Complex]]("λz:complex. complex_of_real(&1)"), s, oneComplex, zeroComplex)))
					}))
				productDerivative := b.Have(
					"the product rule gives the derivative of the shifted zeta product",
					"complex_derivative_at(«product», s, «productSlope»(s))",
					By(
						shiftDerivative,
						right,
						ZetaMangoldt.At(s),
						complex_derivative.DerivativeMul.At(
							shift, zeta, s, oneComplex, b.TermAs[Complex]("-(riemann_zeta(s) * «mangoldtValue»(s))"))))
				radius := b.TermAs[Real]("«radius»(&1, s)")
				positiveRadius := b.Have(
					"the rightward real-part gap is positive",
					"&0 < «radius»(&1, s)",
					ByArith(right))
				local := b.Have(
					"ξ agrees with the product on the disc to the right of one",
					"∀w:complex. |w - s| < «radius»(&1, s) ⇒ «xi»(w) = «product»(w)",
					Derive(func(d *Argument) {
						w := d.FixAs[Complex]()
						near := d.Assume()
						d.Show(
							"the disc lies where the product identity holds",
							By(near, realPart.At(oneReal, s, w), nonzeroShift.At(w), product.At(w)))
					}))
				slopeEquality := b.Have(
					"uniqueness of the derivative identifies h with the derivative of the product",
					"h(s) = «productSlope»(s)",
					Derive(func(d *Argument) {
						localDerivative := d.Have(
							"the product derivative is a derivative of ξ by local agreement",
							"complex_derivative_at(«xi», s, «productSlope»(s))",
							By(
								positiveRadius,
								local,
								productDerivative,
								complex_derivative.DerivativeLocal.At(xi, prod, s, slope, radius)))
						d.Show(
							"both expressions give the derivative of ξ at s",
							By(
								inside,
								parts[0].At(s),
								localDerivative,
								complex_derivative.DerivativeUnique.At(xi, s, d.TermAs[Complex]("h(s)"), slope)))
					}))
				atS := b.Have(
					"use the product identity at s",
					"«xi»(s) = «product»(s)",
					By(right, nonzeroShift.At(s), product.At(s)))
				expanded := b.Have(
					"the product rule gives ζ minus ξ times the Mangoldt series",
					"h(s) = riemann_zeta(s) - «xi»(s) * «mangoldtValue»(s)",
					Simp(Fwd(slopeEquality), Fwd(atS)),
					ByArith())
				zetaQuotient := b.Have(
					"zeta is ξ times the inverse of the shift",
					"riemann_zeta(s) = «xi»(s) * complex_inv(«shift»(s))",
					Simp(Fwd(RiemannZetaDef), Fwd(complex_field.ComplexDivDef)),
					ByArith())
				scaled := b.Have(
					"multiply the derivative equation by the inverse of ξ",
					"h(s) * complex_inv(«xi»(s)) = "+
						"(«xi»(s) * complex_inv(«shift»(s)) - «xi»(s) * «mangoldtValue»(s)) * complex_inv(«xi»(s))",
					By(expanded, zetaQuotient))
				away := b.Have(
					"ξ is nonzero at s",
					"«xi»(s) ≠ complex_of_real(&0)",
					By(right, rightNonzero.At(s)))
				b.Show(
					"cancel ξ and rearrange the logarithmic derivative",
					Simp(Fwd(complex_field.ComplexDivDef)),
					ByArith(away, scaled, At(fieldInverse, b.TermAs[Complex]("«xi»(s)"))))
			}))
		a.Take(a.TermAs[Fun[Complex, Complex]]("«remainder»(h)"))
		a.Show(
			"the domain is open and holds 1, and the logarithmic derivative is the continuation",
			By(parts[1], oneIn, holomorphic, agree))
	}),
	Reading: "The set is where «xi» does not vanish in Re s > 0, and the statement asks " +
		"of it only that it be open and hold 1, which needs nothing of the zeros of ζ. That " +
		"it holds the line Re s = 1 is ζ ≠ 0 there, which MangoldtSeriesContinuation adds.",
})}

// MangoldtSeriesContinuation — the Dirichlet series of Λ, less 1/(s − 1),
// continues holomorphically to an open set containing Re s ≥ 1: the open
// set of MangoldtSeriesContinuationOffZeros, where ξ does not vanish,
// holds the closed half-plane since ξ has no zero there (XiNonzero).
var MangoldtSeriesContinuation = mangoldtSeriesContinuationThm{family.Add(registry.ProofEntry{
	Name: "MangoldtSeriesContinuation",
	Key:  "prop_ce1d4acc1fef0de8",
	Build: family.Theorem("∃U:set(complex). ∃g:(complex → complex). "+
		"    U ∈ complex_topology ∧ "+
		"    (∀s:complex. &1 ≤ re(s) ⇒ s ∈ U) ∧ "+
		"    holomorphic_on(U, g) ∧ "+
		"    ∀s:complex. "+
		"        &1 < re(s) ⇒ dirichlet_series(λn:num. &(von_mangoldt(n)), s) = complex_inv(s - &1) + g(s)",
		func(a *Argument) {
			g, continuation := a.UnpackAs[Fun[Complex, Complex]](MangoldtSeriesContinuationOffZeros, "g")
			contains := a.Have(
				"the domain contains the closed half-plane to the right of one, where ξ has no zero",
				"∀s:complex. &1 ≤ re(s) ⇒ s ∈ «regularDomain»",
				Derive(func(b *Argument) {
					s := b.FixAs[Complex]()
					right := b.Assume()
					inside := b.Have(
						"the real part is positive and ξ is nonzero",
						"&0 < re(s) ∧ «xi»(s) ≠ complex_of_real(&0)",
						ByArith(right, XiNonzero.At(s)))
					b.Show(
						"these are the two conditions for membership",
						BySets(inside))
				}))
			a.Take(a.TermAs[Set[Complex]]("«regularDomain»"))
			a.Take(g)
			a.Show(
				"the continuation off the zeros of ξ, on a domain holding the closed half-plane",
				By(continuation, contains))
		}),
	Reading: "The open set is left unnamed: it is «regularDomain», where «xi» " +
		"does not vanish, and nothing is known of its shape beyond containing the " +
		"closed half-plane. Newman's theorem asks exactly this much.",
})}

// MangoldtSeriesPole — as a real σ decreases to 1, (σ − 1) times the
// Dirichlet series of Λ at σ tends to 1.
var MangoldtSeriesPole = mangoldtSeriesPoleThm{family.Add(registry.ProofEntry{
	Name: "MangoldtSeriesPole",
	Key:  "prop_573121c44ba282d0",
	Build: family.Theorem(Statement{
		Binders:    "∀ε:real.",
		Hypotheses: []string{"&0 < ε"},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ " +
			"    ∀σ:real. " +
			"        &1 < σ ∧ σ < &1 + δ ⇒ " +
			"        |&(σ - &1) * dirichlet_series(λn:num. &(von_mangoldt(n)), &σ) - &1| < ε",
	},
		func(a *Argument, ε *Expr[Real], positive Fact) {
			g, continuation := a.UnpackAs[Fun[Complex, Complex]](MangoldtSeriesContinuationOffZeros, "g")
			parts := a.Conjuncts(
				continuation,
				"the domain of the continuation is open",
				"the domain contains one",
				"the remainder is holomorphic on the domain",
				"to the right of one the series is the pole plus the remainder")
			U := a.TermAs[Set[Complex]]("«regularDomain»")
			one := a.TermAs[Complex]("complex_of_real(&1)")
			oneReal := a.TermAs[Real]("&1")
			gContinuous := a.Have(
				"the holomorphic remainder is continuous at one",
				"complex_continuous_at(g, &1)",
				By(parts[1], parts[2], complex_derivative.HolomorphicOnContinuousAt.At(U, g, one)))
			factor := a.TermAs[Fun[Complex, Complex]]("λz:complex. z - &1")
			factorContinuous := a.Have(
				"the difference from one is continuous there",
				"complex_continuous_at(λz:complex. z - &1, &1)",
				By(
					complex_topology.ContinuousAtId.At(one),
					complex_topology.ContinuousAtConst.At(one, one),
					complex_topology.ContinuousAtSub.At(a.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
						a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_of_real(&1)"), one)))
			scaled := a.TermAs[Fun[Complex, Complex]]("λz:complex. (z - &1) * g(z)")
			continuous := a.Have(
				"multiplying by the difference from one preserves continuity",
				"complex_continuous_at(λz:complex. (z - &1) * g(z), &1)",
				By(gContinuous, factorContinuous, complex_topology.ContinuousAtMul.At(factor, g, one)))
			delta, ball := a.ObtainAs[Real](
				"continuity bounds the oscillation by ε in a ball about one",
				"∃d:real. "+
					"    &0 < d ∧ "+
					"    (∀z:complex. "+
					"        |z - &1| < d ⇒ "+
					"        |(z - &1) * g(z) - (complex_of_real(&1) - &1) * g(complex_of_real(&1))| < ε)",
				By(positive, continuous, complex_topology.ComplexContinuousAtDef.At(scaled, one)),
				Named("d"))
			a.Show(
				"the ball's radius also works along the real axis",
				Witness(delta),
				SplitConj(
					Case(
						"the radius is positive",
						By(ball)),
					Case(
						"the pole cancels and the scaled remainder tends to zero",
						Derive(func(b *Argument) {
							σ := b.FixAs[Real]("σ")
							interval := b.Assume()
							difference := b.TermAs[Complex]("complex_of_real(σ) - &1")
							displacement := b.Have(
								"the real interval stays inside the complex ball",
								"|complex_of_real(σ) - &1| < d",
								ByArith(interval, complex_abs.AbsOfRealSub.At(σ, oneReal)))
							atOne := b.Have(
								"the scaled remainder at one vanishes",
								"(complex_of_real(σ) - &1) * g(complex_of_real(σ)) - "+
									"(complex_of_real(&1) - &1) * g(complex_of_real(&1)) = "+
									"(complex_of_real(σ) - &1) * g(complex_of_real(σ))",
								ByArith())
							small := b.Have(
								"so in the ball the scaled remainder has modulus less than ε",
								"|(complex_of_real(σ) - &1) * g(complex_of_real(σ))| < ε",
								By(ball, displacement, atOne))
							value := b.Have(
								"the continuation gives the value at the real argument",
								"dirichlet_series(λn:num. &(von_mangoldt(n)), complex_of_real(σ)) = "+
									"complex_inv(complex_of_real(σ) - &1) + g(complex_of_real(σ))",
								ByArith(parts[3], interval, complex_field.PartsOfReal.At(σ)))
							realDifference := b.TermAs[Real]("σ - &1")
							lift := b.Have(
								"the real displacement embeds as the complex displacement",
								"complex_of_real(σ - &1) = complex_of_real(σ) - &1",
								By(complex_field.OfRealSub.At(σ, oneReal)))
							nonzero := b.Have(
								"the displacement is nonzero to the right of one",
								"complex_of_real(σ) - &1 ≠ complex_of_real(&0)",
								ByArith(interval, lift, complex_field.OfRealInjective.At(realDifference, b.TermAs[Real]("&0"))))
							cancels := b.Have(
								"the displacement cancels the simple pole",
								"(complex_of_real(σ) - &1) * complex_inv(complex_of_real(σ) - &1) = complex_of_real(&1)",
								By(nonzero, field.MulRightInverse.Read(complex_field.Field).At(difference)))
							errorTerm := b.Have(
								"the error after subtracting one is the scaled remainder",
								"&(σ - &1) * dirichlet_series(λn:num. &(von_mangoldt(n)), &σ) - &1 = "+
									"(complex_of_real(σ) - &1) * g(complex_of_real(σ))",
								Simp(Fwd(lift), Fwd(value), Fwd(comm_ring.LeftDistrib.Read(complex_field.CommRing)), Fwd(cancels)),
								ByArith())
							b.Show(
								"use the bound on the remainder",
								By(small, errorTerm))
						}))))
		}),
	Reading: "This needs ζ only near the real point 1, not its non-vanishing on " +
		"the line: the continuation it reads is MangoldtSeriesContinuationOffZeros, " +
		"whose open set holds 1 since ξ(1) = 1. Dirichlet's theorem reads it.",
})}

// EulerProduct — for Re s > 1 the products of 1/(1 − p^(−s)) over the
// primes up to N tend to ζ(s).
var EulerProduct = eulerProductThm{family.Add(registry.ProofEntry{
	Name: "EulerProduct",
	Key:  "prop_78e9f4dffa17a93d",
	Build: family.Card(Statement{
		Binders:    "∀s:complex.",
		Hypotheses: []string{"&1 < re(s)"},
		Conclusion: "(λN:num. " +
			"    Π_{p∈{p:num | nat_prime(p) ∧ p ≤ N}} complex_inv(&1 - complex_cpow(&p, -s))) ⟶ " +
			"riemann_zeta(s)",
	},
		"Multiplying the series of n^(−s) by 1 − p^(−s) removes the multiples of p, so ζ(s) times "+
			"the product of 1 − p^(−s) over p ≤ N is the sum of n^(−s) over the n with no prime factor "+
			"≤ N: 1 plus a part of the tail beyond N, which tends to 0 (real_rpow.RpowTailSumBound). "+
			"Each factor is nonzero since |p^(−s)| < 1 (complex_cpow.AbsCpow)."),
	Deps: []registry.EntryLike{ZetaSums, ZetaNonzeroRight, complex_cpow.AbsCpow},
	Reading: "No member of the chapter cites it: the route to ζ ≠ 0 is " +
		"ZetaExponential. It is stated because it is what a reader looks for.",
})}
