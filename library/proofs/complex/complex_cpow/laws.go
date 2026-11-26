// laws.go — the complex power at a positive real base: its reading through
// the real logarithm, its modulus, the exponent laws, its derivatives in
// the exponent and along the base, the bound on the difference of two
// powers n^(−s), and the bound on the tangent remainder of n^(1−s) over a
// unit step.

package complex_cpow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_log"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// CpowPositiveReal — at a positive real base x the power is
// exp(w·log x), with the real logarithm.
var CpowPositiveReal = cpowPositiveRealThm{family.Add(registry.ProofEntry{
	Name: "CpowPositiveReal",
	Key:  "prop_f992ee941c0a57fe",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real. ∀w:complex.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "complex_cpow(&x, w) = exp(w * &(log(x)))",
	},
		func(a *Argument, x *Expr[Real], w *Expr[Complex], positive Fact) {
			nonzero := a.Have(
				"the positive base stays nonzero under the real embedding",
				"&x ≠ &0",
				ByArith(positive, complex_field.OfRealInjective.At(x, a.TermAs[Real]("&0"))))
			a.Show(
				"the nonzero branch uses the principal logarithm, which is real here",
				Simp(Fwd(ComplexCpowDef)),
				By(Normalized, nonzero, positive, complex_log.LogPositiveReal.At(x)))
		}),
})}

// CpowRealExponent — at a positive real base and a real exponent the power
// is the real power.
var CpowRealExponent = cpowRealExponentThm{family.Add(registry.ProofEntry{
	Name: "CpowRealExponent",
	Key:  "prop_28217c8c474ef4cd",
	Build: family.Theorem(Statement{
		Binders:    "∀x a:real.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "complex_cpow(&x, &a) = &(real_rpow(x, a))",
	},
		func(arg *Argument, x, a *Expr[Real], positive Fact) {
			arg.Do(CalcEq(
				Leg(
					arg.TermAs[Complex]("exp(&a * &(log(x)))"),
					"the positive real base uses the real logarithm",
					By(positive, CpowPositiveReal.At(x, arg.TermAs[Complex]("&a")))),
				Leg(
					arg.TermAs[Complex]("&(exp(a * log(x)))"),
					"the real embedding preserves products and the exponential",
					Simp(Rev(complex_field.OfRealMul), Fwd(complex_exp.ExpOfReal)),
					Basic()),
				FinalLeg(
					"this real exponential is the real power",
					Simp(Fwd(real_rpow.RpowExp)),
					Basic())))
		}),
})}

// AbsCpow — the modulus of x^w, x a positive real, is x to the real part
// of w.
var AbsCpow = absCpowThm{family.Add(registry.ProofEntry{
	Name: "AbsCpow",
	Key:  "prop_5596f661823e4ff2",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real. ∀w:complex.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "|complex_cpow(&x, w)| = real_rpow(x, re(w))",
	},
		func(a *Argument, x *Expr[Real], w *Expr[Complex], _ Fact) {
			a.Do(CalcEq(
				Leg(
					a.TermAs[Real]("exp(re(w * &(log(x))))"),
					"the modulus of the complex exponential reads the real part of its argument",
					Simp(Fwd(CpowPositiveReal), Fwd(complex_power_series.AbsExp)),
					Basic()),
				Leg(
					a.TermAs[Real]("exp(re(w) * log(x))"),
					"the logarithm factor has zero imaginary part",
					Simp(
						Fwd(complex_field.PartsMul),
						Fwd(complex_field.PartsOfReal),
						Fwd(real_ring.MulRightZero),
						Fwd(real_ring.SubRightZero)),
					Basic()),
				FinalLeg(
					"the real exponential gives the real power with exponent re(w)",
					Simp(Fwd(real_rpow.RpowExp)),
					Basic())))
		}),
	Reading: "This is why a Dirichlet series converges on " +
		"half-planes: |n^(−s)| = n^(−re s) sees only the real part of s.",
})}

// AbsCpowNegLessEq — at a base at least 1, x^(−s) is at most x^(−σ) in
// modulus once σ ≤ re(s): the modulus is x to the real part of −s, which
// is −re(s), and at such a base the real power increases with the
// exponent (real_rpow.RpowLessEqExponent).
var AbsCpowNegLessEq = absCpowNegLessEqThm{family.Add(registry.ProofEntry{
	Name: "AbsCpowNegLessEq",
	Key:  "prop_90de58e763fa9cee",
	Build: family.Theorem(Statement{
		Binders: "∀x σ:real. ∀s:complex.",
		Hypotheses: []string{
			"&1 ≤ x",
			"σ ≤ re(s)",
		},
		Conclusion: "|complex_cpow(&x, -s)| ≤ real_rpow(x, -σ)",
	}, func(a *Argument, x, σ *Expr[Real], s *Expr[Complex], atLeastOne, toRight Fact) {
		positive := a.Have(
			"the base is positive",
			"&0 < x",
			ByArith(atLeastOne))
		size := a.Have(
			"the modulus of x^(−s) is x to the real part of −s, which is −re(s)",
			"|complex_cpow(&x, -s)| = real_rpow(x, -re(s))",
			By(Normalized, positive, AbsCpow.At(x, a.TermAs[Complex]("-s")), complex_field.PartsNeg.At(s)))
		a.Show(
			"and at a base at least 1 the power increases with the exponent, −re(s) being at most −σ",
			ByArith(
				size,
				atLeastOne,
				toRight,
				real_rpow.RpowLessEqExponent.At(x, a.TermAs[Real]("-re(s)"), a.TermAs[Real]("-σ"))))
	}),
})}

// CpowZeroExponent — every base to the power 0 is 1.
var CpowZeroExponent = cpowZeroExponentThm{family.Add(registry.ProofEntry{
	Name: "CpowZeroExponent",
	Key:  "prop_897416f9f87f0df4",
	Build: family.Theorem("∀z:complex. complex_cpow(z, &0) = &1",
		func(a *Argument, z *Expr[Complex]) {
			a.Cases(a.TermAs[Bool]("z = &0"))
			a.When(
				"at the zero base the definition gives one for the zero exponent",
				Simp(Fwd(ComplexCpowDef)),
				Basic())
			a.Otherwise(
				"at a nonzero base the exponent times the logarithm is zero",
				Simp(Fwd(ComplexCpowDef), Fwd(comm_ring.MulLeftZero.Read(complex_field.CommRing))),
				Cite(complex_exp.ExpZero))
		}),
})}

// CpowOneBase — 1 to every power is 1.
var CpowOneBase = cpowOneBaseThm{family.Add(registry.ProofEntry{
	Name: "CpowOneBase",
	Key:  "prop_88da951c53b1701b",
	Build: family.Theorem("∀w:complex. complex_cpow(&1, w) = &1",
		func(a *Argument, w *Expr[Complex]) {
			a.Do(CalcEq(
				Leg(
					a.TermAs[Complex]("exp(w * &(log(&1)))"),
					"one is a positive real base",
					By(real_order_ring.ZeroLessThanOne, CpowPositiveReal.At(a.TermAs[Real]("&1"), w))),
				Leg(
					a.TermAs[Complex]("exp(complex_of_real(&0))"),
					"the logarithm of one vanishes, so the product in the exponent is zero",
					Simp(Fwd(real_exp_log.LogOne), Fwd(comm_ring.MulRightZero.Read(complex_field.CommRing))),
					Basic()),
				FinalLeg(
					"the exponential at zero is one",
					Cite(complex_exp.ExpZero))))
		}),
})}

// CpowAdd — at a positive real base the power of a sum of exponents is
// the product of the powers.
var CpowAdd = cpowAddThm{family.Add(registry.ProofEntry{
	Name: "CpowAdd",
	Key:  "prop_64e63ee72148f132",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real. ∀v w:complex.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "complex_cpow(&x, v + w) = complex_cpow(&x, v) * complex_cpow(&x, w)",
	},
		func(a *Argument, x *Expr[Real], v, w *Expr[Complex], _ Fact) {
			a.Show(
				"distribute the logarithm factor over the exponent sum, then split the exponential into a product",
				Simp(
					Fwd(CpowPositiveReal),
					Fwd(comm_ring.RightDistrib.Read(complex_field.CommRing)),
					Fwd(complex_power_series.ExpAdd)),
				Basic())
		}),
})}

// CpowNeg — at a positive real base the power at −w is the inverse of the
// power at w.
var CpowNeg = cpowNegThm{family.Add(registry.ProofEntry{
	Name: "CpowNeg",
	Key:  "prop_33bee9b0b394e824",
	Build: family.Card(Statement{
		Binders:    "∀x:real. ∀w:complex.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "complex_cpow(&x, -w) = complex_inv(complex_cpow(&x, w))",
	},
		"CpowAdd at w and −w gives the product 1 (CpowZeroExponent), "+
			"and the factor at w is not 0 (CpowNonzero)."),
	Deps: []registry.EntryLike{CpowAdd, CpowZeroExponent, CpowNonzero},
})}

// CpowNat — at a positive real base and a natural exponent the power is
// the natural power.
var CpowNat = cpowNatThm{family.Add(registry.ProofEntry{
	Name: "CpowNat",
	Key:  "prop_7c6acbae51283430",
	Build: family.Card(Statement{
		Binders:    "∀x:real. ∀n:num.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "complex_cpow(&x, complex_of_real(&n)) = &(x ^ n)",
	}, "CpowRealExponent at a = &n and real_rpow.RpowNat."),
	Deps: []registry.EntryLike{CpowRealExponent},
})}

// CpowMulPositive — the power of a product of two positive reals is the
// product of the powers.
var CpowMulPositive = cpowMulPositiveThm{family.Add(registry.ProofEntry{
	Name: "CpowMulPositive",
	Key:  "prop_5a9ec43c10c5b8c5",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real. ∀w:complex.",
		Hypotheses: []string{
			"&0 < x",
			"&0 < y",
		},
		Conclusion: "complex_cpow(&(x * y), w) = complex_cpow(&x, w) * complex_cpow(&y, w)",
	},
		func(a *Argument, x, y *Expr[Real], w *Expr[Complex], _ Fact) {
			a.Show(
				"the product base stays positive, and the sum of logarithms splits the exponential into factors",
				Simp(
					Fwd(real_order_ring.MulPos),
					Fwd(CpowPositiveReal),
					Fwd(real_exp_log.LogMul),
					Fwd(complex_field.OfRealAdd),
					Fwd(comm_ring.LeftDistrib.Read(complex_field.CommRing)),
					Fwd(complex_power_series.ExpAdd)),
				Basic())
		}),
	Reading: "It fails for general complex bases, where the principal logarithm of a product is the " +
		"sum of the logarithms only up to 2πi; it is what makes n ↦ n^(−s) completely multiplicative.",
})}

// CpowNonzero — a power of a positive real is not 0.
var CpowNonzero = cpowNonzeroThm{family.Add(registry.ProofEntry{
	Name: "CpowNonzero",
	Key:  "prop_1e62933f976cac60",
	Build: family.Card(Statement{
		Binders:    "∀x:real. ∀w:complex.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "complex_cpow(&x, w) ≠ &0",
	}, "CpowPositiveReal and complex_power_series.ExpNonzero."),
	Deps: []registry.EntryLike{CpowPositiveReal, complex_power_series.ExpNonzero},
})}

// CpowDerivativeExponent — as a function of its exponent, x^w has
// derivative x^w·log x.
var CpowDerivativeExponent = cpowDerivativeExponentThm{family.Add(registry.ProofEntry{
	Name: "CpowDerivativeExponent",
	Key:  "prop_159419f3a367075f",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real. ∀w:complex.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "complex_derivative_at(λv:complex. complex_cpow(&x, v), " +
			"    w, " +
			"    complex_cpow(&x, w) * &(log(x)))",
	},
		func(a *Argument, x *Expr[Real], w *Expr[Complex], positive Fact) {
			logarithm := a.TermAs[Complex]("&(log(x))")
			commute := comm_monoid.Comm.Read(complex_field.MulMonoid)
			scaled := a.Have(
				"the power as a function of its exponent is the scaled exponential",
				"(λv:complex. complex_cpow(&x, v)) = (λv:complex. exp(&(log(x)) * v))",
				Funext(),
				a.ForEach(func(v *Expr[Complex]) Action {
					return By(Normalized, positive, CpowPositiveReal.At(x, v), commute.At(v, logarithm))
				}))
			a.Show(
				"differentiate the scaled exponential and commute the logarithm factor to the right",
				scaled.Rw(),
				By(
					commute.At(a.TermAs[Complex]("exp(&(log(x)) * w)"), logarithm),
					complex_power_series.ExpScaledDerivative.At(logarithm, w)))
		}),
	Reading: "So s ↦ n^(−s) is entire, with derivative −log n · n^(−s).",
})}

// CpowHolomorphicExponent — as a function of its exponent, x^w is entire:
// CpowDerivativeExponent gives its derivative at every point.
var CpowHolomorphicExponent = cpowHolomorphicExponentThm{family.Add(registry.ProofEntry{
	Name: "CpowHolomorphicExponent",
	Key:  "prop_3b8819c63b3b3ee7",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "holomorphic_on(𝕌, λz:complex. complex_cpow(&x, z))",
	}, func(a *Argument, x *Expr[Real], positive Fact) {
		a.Do(Unfold(complex_derivative.HolomorphicOnDef))
		z := a.FixAs[Complex]("z")
		a.Assume()
		a.Take(a.TermAs[Complex]("complex_cpow(&x, z) * &(log(x))"))
		a.Show(
			"use the derivative of the power in its exponent",
			By(positive, CpowDerivativeExponent.At(x, z)))
	}),
})}

// CpowPathDerivative — along the positive reals, u ↦ u^w has velocity
// w·u^(w−1).
var CpowPathDerivative = cpowPathDerivativeThm{family.Add(registry.ProofEntry{
	Name: "CpowPathDerivative",
	Key:  "prop_1b9ea1dcb252a90d",
	Build: family.Theorem(Statement{
		Binders:    "∀x:real. ∀w:complex.",
		Hypotheses: []string{"&0 < x"},
		Conclusion: "path_derivative_at(λu:real. complex_cpow(&u, w), x, w * complex_cpow(&x, w - &1))",
		Abbrev: Abbrev{
			{Name: "logPath", Text: "λu:real. w * &(log(u))"},
			{Name: "expPath", Text: "λu:real. exp(w * &(log(u)))"},
			{Name: "powerPath", Text: "λu:real. complex_cpow(&u, w)"},
			{Name: "logRate", Text: "w * &(real_inv(x))"},
			{Name: "expRate", Text: "exp(w * &(log(x))) * «logRate»"},
			{Name: "powerRate", Text: "w * complex_cpow(&x, w - &1)"},
		},
	},
		func(a *Argument, x *Expr[Real], w *Expr[Complex], positive Fact) {
			log := a.TermAs[Fun[Real, Real]]("real_log")
			inverse := a.TermAs[Real]("real_inv(x)")
			inner := a.Have(
				"the real and imaginary parts of w scale the real logarithm and its derivative",
				"path_derivative_at(«logPath», x, «logRate»)",
				Simp(
					Fwd(complex_derivative.PathDerivativeAtDef),
					Fwd(complex_field.PartsMul),
					Fwd(complex_field.PartsOfReal),
					Fwd(real_ring.MulRightZero),
					Fwd(real_ring.SubRightZero),
					Fwd(comm_monoid.LeftIdentity.Read(real_ring.AddMonoid))),
				By(
					positive,
					real_exp_log.LogDerivative.At(x),
					real_derivative.DerivativeScale.At(log, x, inverse, a.TermAs[Real]("re(w)")),
					real_derivative.DerivativeScale.At(log, x, inverse, a.TermAs[Real]("im(w)"))))
			chain := a.Have(
				"the exponential multiplies the logarithmic path velocity by its own value",
				"path_derivative_at(«expPath», x, «expRate»)",
				By(
					inner,
					complex_power_series.ExpDerivative.At(a.TermAs[Complex]("«logPath»(x)")),
					path_integral.PathDerivativeCompose.At(
						a.TermAs[Fun[Complex, Complex]]("complex_exp"),
						a.TermAs[Fun[Real, Complex]]("«logPath»"),
						x,
						a.TermAs[Complex]("«expPath»(x)"),
						a.TermAs[Complex]("«logRate»"))))
			factor := a.Have(
				"split off the power with exponent one, whose value is the base",
				"complex_cpow(&x, w) = complex_cpow(&x, w - &1) * &x",
				ByArith(
					positive,
					CpowAdd.At(x, a.TermAs[Complex]("w - &1"), a.TermAs[Complex]("&1")),
					CpowRealExponent.At(x, a.TermAs[Real]("&1")),
					real_rpow.RpowOneExponent.At(x)))
			velocity := a.Have(
				"the exponential is the power, and the base cancels its inverse",
				"«expRate» = «powerRate»",
				Simp(Rev(CpowPositiveReal), Fwd(factor), Fwd(complex_field.OfRealInv)),
				ByArith(positive))
			agree := a.Have(
				"within radius x the base stays positive, so both paths agree in either projection",
				"∀p:(complex → real). ∀u:real. |u - x| < x ⇒ p(«powerPath»(u)) = p(«expPath»(u))",
				Derive(func(b *Argument) {
					b.FixAs[Fun[Complex, Real]]()
					u := b.FixAs[Real]()
					near := b.Assume()
					b.Show(
						"the positive-real power formula applies here",
						ByArith(near, CpowPositiveReal.At(u, w)))
				}))
			components := a.Simplified(chain, Fwd(velocity), Fwd(complex_derivative.PathDerivativeAtDef))
			a.Show(
				"the two real derivatives transfer by local agreement",
				Simp(Fwd(complex_derivative.PathDerivativeAtDef)),
				By(
					positive,
					agree.At(a.TermAs[Fun[Complex, Real]]("complex_re")),
					agree.At(a.TermAs[Fun[Complex, Real]]("complex_im")),
					components,
					real_derivative.DerivativeLocal.At(
						a.TermAs[Fun[Real, Real]]("λu:real. re(«powerPath»(u))"),
						a.TermAs[Fun[Real, Real]]("λu:real. re(«expPath»(u))"),
						x,
						x,
						a.TermAs[Real]("re(«powerRate»)")),
					real_derivative.DerivativeLocal.At(
						a.TermAs[Fun[Real, Real]]("λu:real. im(«powerPath»(u))"),
						a.TermAs[Fun[Real, Real]]("λu:real. im(«expPath»(u))"),
						x,
						x,
						a.TermAs[Real]("im(«powerRate»)"))))
		}),
	Reading: "The derivative is taken in a real base, " +
		"so the slit of the principal logarithm never enters.",
})}

// CpowDifferenceBound — for 0 < x ≤ y and re(s) ≥ −1, the powers x^(−s)
// and y^(−s) differ by at most |s|·(y − x)·x^(−re(s)−1).
var CpowDifferenceBound = cpowDifferenceBoundThm{family.Add(registry.ProofEntry{
	Name: "CpowDifferenceBound",
	Key:  "prop_fe6e2a7c68f8409c",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real. ∀s:complex.",
		Hypotheses: []string{
			"&0 < x",
			"x ≤ y",
			"-&1 ≤ re(s)",
		},
		Conclusion: "|complex_cpow(&x, -s) - complex_cpow(&y, -s)| ≤ " +
			"|s| * (y - x) * real_rpow(x, -re(s) - &1)",
		Abbrev: Abbrev{
			{Name: "power", Text: "λv:complex. λu:real. complex_cpow(&u, v)"},
			{Name: "velocity", Text: "λv:complex. λu:real. v * «power»(v - &1, u)"},
			{Name: "exponent", Text: "-re(s) - &1"},
			{Name: "speedBound", Text: "|s| * real_rpow(x, «exponent»)"},
		},
	},
		func(a *Argument, x, y *Expr[Real], s *Expr[Complex], positive, ordered, realPart Fact) {
			negativeS := a.TermAs[Complex]("-s")
			interval := a.TermAs[Set[Real]]("⟦x, y⟧")
			power := a.TermAs[Fun[Real, Complex]]("«power»(-s)")
			velocity := a.TermAs[Fun[Real, Complex]]("«velocity»(-s)")
			rates := a.Have(
				"every base on the interval is positive, so every power has its velocity there",
				"∀v:complex. ∀t:real. t ∈ ⟦x, y⟧ ⇒ path_derivative_at(«power»(v), t, «velocity»(v, t))",
				Derive(func(b *Argument) {
					v := b.FixAs[Complex]()
					t := b.FixAs[Real]()
					inside := b.Assume()
					b.Show(
						"the point lies to the right of the positive left endpoint",
						ByArith(
							inside,
							positive,
							real_topology.ClosedIntervalMembership.At(t, x, y),
							CpowPathDerivative.At(t, v)))
				}))
			powersContinuous := a.Have(
				"the velocity of each power makes its real and imaginary parts continuous",
				"∀v:complex. "+
					"    real_continuous_on(⟦x, y⟧, λt:real. re(«power»(v, t))) ∧ "+
					"    real_continuous_on(⟦x, y⟧, λt:real. im(«power»(v, t)))",
				Derive(func(b *Argument) {
					v := b.FixAs[Complex]()
					b.Show(
						"the derivative gives continuity on the interval",
						By(
							rates.At(v),
							path_integral.PathDerivativeContinuousOn.At(
								b.TermAs[Fun[Real, Complex]]("«power»(v)"),
								b.TermAs[Fun[Real, Complex]]("«velocity»(v)"),
								interval)))
				}))
			velocityContinuous := a.Have(
				"multiplying the power with exponent −s − 1 by −s preserves continuity of its parts",
				"real_continuous_on(⟦x, y⟧, λt:real. re(«velocity»(-s, t))) ∧ "+
					"real_continuous_on(⟦x, y⟧, λt:real. im(«velocity»(-s, t)))",
				Simp(Fwd(complex_field.PartsMul)),
				By(
					powersContinuous.At(a.TermAs[Complex]("-s - &1")),
					real_continuous.ContinuousOnConst,
					real_continuous.ContinuousOnMul,
					real_continuous.ContinuousOnSub,
					real_continuous.ContinuousOnAdd))
			I, integral := a.ObtainAs[Complex](
				"the continuous velocity has an integral on the closed interval",
				"∃I:complex. complex_has_integral(«velocity»(-s), x, y, I)",
				By(ordered, velocityContinuous, path_integral.ComplexContinuousIntegrable.At(velocity, x, y)))
			interior := a.Have(
				"the same derivative formula holds in the interior",
				"∀t:real. x < t ∧ t < y ⇒ path_derivative_at(«power»(-s), t, «velocity»(-s, t))",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]()
					inside := b.Assume()
					b.Show(
						"an interior point belongs to the closed interval",
						ByArith(inside, rates.At(negativeS, t), real_topology.ClosedIntervalMembership.At(t, x, y)))
				}))
			increment := a.Have(
				"Newton–Leibniz identifies the integral with the endpoint increment",
				"I = «power»(-s, y) - «power»(-s, x)",
				By(
					powersContinuous.At(negativeS),
					interior,
					integral,
					path_integral.ComplexNewtonLeibniz.At(power, velocity, x, y, I)))
			bounded := a.Have(
				"the speed is bounded by the left-endpoint power times |s|",
				"∀t:real. x ≤ t ∧ t ≤ y ⇒ |«velocity»(-s, t)| ≤ «speedBound»",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]()
					inside := b.Assume()
					b.Have(
						"the base t is positive",
						"&0 < t",
						ByArith(inside, positive))
					powerBound := b.Have(
						"a nonpositive power of a positive base decreases as the base increases",
						"real_rpow(t, «exponent») ≤ real_rpow(x, «exponent»)",
						ByArith(
							positive,
							inside,
							realPart,
							real_rpow.RpowLessEqBaseNonpos.At(x, t, b.TermAs[Real]("«exponent»"))))
					b.Show(
						"the modulus of the velocity scales the real power by |s|",
						Simp(
							Fwd(complex_abs.AbsMul),
							Fwd(complex_abs.AbsNeg),
							Fwd(AbsCpow),
							Fwd(complex_field.PartsSub),
							Fwd(complex_field.PartsNeg),
							Fwd(complex_field.PartsOfReal)),
						ByArith(powerBound))
				}))
			integralBound := a.Have(
				"the integral is bounded by the speed bound times the interval length",
				"|I| ≤ «speedBound» * (y - x)",
				By(
					bounded,
					integral,
					path_integral.ComplexHasIntegralBound.At(velocity, x, y, a.TermAs[Real]("«speedBound»"), I)))
			a.Show(
				"the modulus is unchanged when the endpoints are exchanged",
				ByArith(
					increment,
					integralBound,
					complex_abs.AbsSubComm.At(
						a.TermAs[Complex]("«power»(-s, x)"),
						a.TermAs[Complex]("«power»(-s, y)"))))
		}),
	Reading: "re(s) ≥ −1 is what makes u^(−re(s)−1) largest at the left end; for re(s) " +
		"< −1 the bound holds with y's power instead. Every convergence statement of ζ and " +
		"of Dirichlet series beyond absolute convergence rests on this bound at y = x + 1.",
})}

// CpowTangentRemainderBound — for Re s ≥ −1 and n > 0, the power
// u^(1−s) departs from its tangent line at n by at most
// |s − 1|·|s|·n^(−Re s − 1) over the unit step to n + 1: the remainder is
// the integral over ⟦n, n + 1⟧ of (s − 1)·(n^(−s) − u^(−s)), which
// CpowDifferenceBound bounds.
var CpowTangentRemainderBound = cpowTangentRemainderBoundThm{family.Add(registry.ProofEntry{
	Name: "CpowTangentRemainderBound",
	Key:  "prop_215265c2e8ea4414",
	Build: family.Theorem(Statement{
		Binders: "∀s:complex. ∀n:num.",
		Hypotheses: []string{
			"-&1 ≤ re(s)",
			"0 < n",
		},
		Conclusion: "|(s - &1) * complex_cpow(&n, -s) - " +
			"(complex_cpow(&n, &1 - s) - complex_cpow(&(n + 1), &1 - s))| ≤ " +
			"|s - &1| * |s| * real_rpow(&n, -re(s) - &1)",
		Abbrev: Abbrev{
			{Name: "rightEnd", Text: "real_of_num(n + 1)"},
			{Name: "power", Text: "λv:complex. λu:real. complex_cpow(&u, v)"},
			{Name: "powerRate", Text: "λv:complex. λu:real. v * «power»(v - &1, u)"},
			{Name: "velocity", Text: "λu:real. (&1 - s) * «power»(-s, u)"},
			{Name: "offset", Text: "(s - &1) * «power»(-s, real_of_num(n))"},
			{Name: "integrand", Text: "λu:real. «offset» + «velocity»(u)"},
			{Name: "term", Text: "«offset» - («power»(&1 - s, real_of_num(n)) - «power»(&1 - s, «rightEnd»))"},
			{Name: "decay", Text: "real_rpow(real_of_num(n), -re(s) - &1)"},
			{Name: "bound", Text: "|s - &1| * |s| * «decay»"},
		},
	},
		func(a *Argument, s *Expr[Complex], n *Expr[Nat], realPart, positiveN Fact) {
			x := a.TermAs[Real]("real_of_num(n)")
			y := a.TermAs[Real]("«rightEnd»")
			interval := a.TermAs[Set[Real]]("⟦real_of_num(n), «rightEnd»⟧")
			geometry := a.Have(
				"the interval begins at a positive number and has length one",
				"&0 < real_of_num(n) ∧ «rightEnd» - real_of_num(n) = &1",
				ByArith(positiveN))
			rates := a.Have(
				"all real bases on the interval are positive, so the power has its velocity there",
				Statement{
					Binders: "∀v:complex. ∀u:real.",
					Hypotheses: []string{
						"u ∈ ⟦real_of_num(n), «rightEnd»⟧",
					},
					Conclusion: "path_derivative_at(«power»(v), u, «powerRate»(v, u))",
				},
				Derive(func(b *Argument) {
					v := b.FixAs[Complex]()
					u := b.FixAs[Real]()
					inside := b.Assume()
					b.Show(
						"the point is at least the positive left endpoint",
						ByArith(
							inside,
							geometry,
							real_topology.ClosedIntervalMembership.At(u, x, y),
							CpowPathDerivative.At(u, v)))
				}))
			powersContinuous := a.Have(
				"the derivative of each power gives continuity of both parts",
				"∀v:complex. "+
					"    real_continuous_on(⟦real_of_num(n), «rightEnd»⟧, λu:real. re(«power»(v, u))) ∧ "+
					"    real_continuous_on(⟦real_of_num(n), «rightEnd»⟧, λu:real. im(«power»(v, u)))",
				Derive(func(b *Argument) {
					v := b.FixAs[Complex]()
					b.Show(
						"apply continuity of paths with a velocity",
						By(
							rates.At(v),
							path_integral.PathDerivativeContinuousOn.At(
								b.TermAs[Fun[Real, Complex]]("«power»(v)"),
								b.TermAs[Fun[Real, Complex]]("«powerRate»(v)"),
								interval)))
				}))
			velocityContinuous := a.Have(
				"the two parts of the velocity are continuous since the power is multiplied by a constant",
				"real_continuous_on(⟦real_of_num(n), «rightEnd»⟧, λu:real. re(«velocity»(u))) ∧ "+
					"real_continuous_on(⟦real_of_num(n), «rightEnd»⟧, λu:real. im(«velocity»(u)))",
				Simp(Fwd(complex_field.PartsMul)),
				By(
					powersContinuous.At(a.TermAs[Complex]("-s")),
					real_continuous.ContinuousOnConst,
					real_continuous.ContinuousOnMul,
					real_continuous.ContinuousOnSub,
					real_continuous.ContinuousOnAdd))
			velocity := a.TermAs[Fun[Real, Complex]]("«velocity»")
			I, integral := a.ObtainAs[Complex](
				"the continuous velocity has an integral over the interval",
				"∃I:complex. complex_has_integral(«velocity», real_of_num(n), «rightEnd», I)",
				ByArith(velocityContinuous, path_integral.ComplexContinuousIntegrable.At(velocity, x, y)),
				Named("I"))
			exponent := a.TermAs[Complex]("&1 - s")
			shift := a.Have(
				"decrease the exponent by one",
				"(&1 - s) - &1 = -s",
				ByArith())
			interior := a.Have(
				"the power with exponent 1 − s has the required velocity in the interior",
				Statement{
					Binders: "∀u:real.",
					Hypotheses: []string{
						"real_of_num(n) < u",
						"u < «rightEnd»",
					},
					Conclusion: "path_derivative_at(«power»(&1 - s), u, «velocity»(u))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[Real]()
					inside := b.Assume()
					b.Show(
						"use the power rule at the interior point",
						ByArith(inside, rates.At(exponent, u), shift, real_topology.ClosedIntervalMembership.At(u, x, y)))
				}))
			increment := a.Have(
				"Newton–Leibniz gives the endpoint increment of the power",
				"I = «power»(&1 - s, «rightEnd») - «power»(&1 - s, real_of_num(n))",
				By(
					powersContinuous.At(exponent),
					interior,
					integral,
					path_integral.ComplexNewtonLeibniz.At(
						a.TermAs[Fun[Real, Complex]]("«power»(&1 - s)"), velocity, x, y, I)))
			constant := a.Have(
				"the constant offset integrates to itself on the unit interval",
				"complex_has_integral(λu:real. «offset», real_of_num(n), «rightEnd», «offset»)",
				Simp(Fwd(path_integral.ComplexHasIntegralDef)),
				ByArith(
					geometry,
					real_integral.HasIntegralConst.At(x, y, a.TermAs[Real]("re(«offset»)")),
					real_integral.HasIntegralConst.At(x, y, a.TermAs[Real]("im(«offset»)"))))
			termIntegral := a.Have(
				"adding the constant offset to the velocity gives the regularized term as integral",
				"complex_has_integral(«integrand», real_of_num(n), «rightEnd», «term»)",
				ByArith(
					increment,
					integral,
					constant,
					path_integral.ComplexHasIntegralAdd.At(
						a.TermAs[Fun[Real, Complex]]("λu:real. «offset»"),
						velocity,
						x,
						y,
						a.TermAs[Complex]("«offset»"),
						I)))
			bounded := a.Have(
				"the difference estimate bounds the integrand over the interval",
				"∀u:real. real_of_num(n) ≤ u ∧ u ≤ «rightEnd» ⇒ |«integrand»(u)| ≤ «bound»",
				Derive(func(b *Argument) {
					u := b.FixAs[Real]()
					inside := b.Assume()
					factor := b.Have(
						"factor s − 1 to expose the difference of powers",
						"«integrand»(u) = (s - &1) * («power»(-s, real_of_num(n)) - «power»(-s, u))",
						ByArith())
					width := b.Have(
						"u is at most one unit from the left endpoint",
						"u - real_of_num(n) ≤ &1",
						ByArith(inside, geometry))
					scaled := b.Have(
						"scale the width bound by the nonnegative decay factor",
						"|s| * (u - real_of_num(n)) * «decay» ≤ |s| * «decay»",
						ByArith(
							width,
							geometry,
							real_rpow.RpowPositive.At(x, b.TermAs[Real]("-re(s) - &1")),
							real_order_ring.LessEqMulRight.At(
								b.TermAs[Real]("u - real_of_num(n)"), b.TermAs[Real]("&1"), b.TermAs[Real]("|s| * «decay»"))))
					difference := b.Have(
						"the modulus of the power difference is bounded by the scaled decay",
						"|«power»(-s, real_of_num(n)) - «power»(-s, u)| ≤ |s| * «decay»",
						ByArith(realPart, inside, geometry, scaled, CpowDifferenceBound.At(x, u, s)))
					b.Show(
						"take moduli of the two factors",
						Simp(Fwd(factor), Fwd(complex_abs.AbsMul)),
						ByArith(difference))
				}))
			a.Show(
				"the integral estimate over a unit interval gives the term bound",
				ByArith(
					bounded,
					termIntegral,
					geometry,
					path_integral.ComplexHasIntegralBound.At(
						a.TermAs[Fun[Real, Complex]]("«integrand»"),
						x,
						y,
						a.TermAs[Real]("«bound»"),
						a.TermAs[Complex]("«term»"))))
		}),
	Reading: "Summed over n, the bound is the reason the series of these remainders converges " +
		"for Re s > 0 where Σ n^(−s) does not: one more power of n in the denominator. It holds " +
		"with a factor 1/2 to spare, the integrand being at most |s − 1|·|s|·(u − n)·n^(−re s − 1).",
})}
