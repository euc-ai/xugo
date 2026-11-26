// integrable.go — integrable functions on a measure space. A measurable
// function is integrable when the integral of the embedding of |f| in
// [0, ∞] is finite. A measurable function dominated by an integrable one is
// integrable, and the embeddings of f and of −f, the two parts the integral
// of f takes, have finite integrals. Integrable functions are closed under
// absolute values, sums, real multiples and differences: ||f|| is |f|,
// |f + g| lies below |f| + |g|, whose integral adds, and |c·f| is |c| times
// |f|, whose integral scales.

package measure_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

// RealIntegrableEqOn — replacing an integrable function by one agreeing on Ω
// preserves integrability: measurability transfers and the absolute-value
// integrals agree.
var RealIntegrableEqOn = realIntegrableEqOnThm{family.Add(registry.ProofEntry{
	Name: "RealIntegrableEqOn",
	Key:  "prop_19d72233bdd76b6f",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → real).",
		Hypotheses: []string{"real_integrable(Ω, S, μ, f)", "∀x:A. x ∈ Ω ⇒ f(x) = g(x)"},
		Conclusion: "real_integrable(Ω, S, μ, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f, g *Arrow[A, Real],
		integrable, equal Fact,
	) {
		integrableParts := a.Unfolded(integrable, RealIntegrableDef)
		measurable := a.Have(
			"measurability depends only on values on Ω",
			"real_measurable(Ω, S, g)",
			By(
				integrableParts,
				equal,
				measurable_function.RealMeasurableDef.At(Ω, S, f),
				measurable_space.MeasurableCongruence.At(
					Ω, S, a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), f, g),
				measurable_function.RealMeasurableDef.At(Ω, S, g)))
		a.Show(
			"the equal absolute values have the same finite nonnegative integral",
			By(
				integrableParts,
				equal,
				measurable,
				nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|g(x)|)")),
				RealIntegrableDef.At(Ω, S, μ, g)))
	}),
})}

// IntegrableDominated — a measurable function dominated on Ω by an
// integrable one is integrable: on Ω the embedding of |f| lies below that
// of |h|, so its integral lies below the finite integral of |h|. No
// structure is asked of Ω, S or μ.
var IntegrableDominated = integrableDominatedThm{family.Add(registry.ProofEntry{
	Name: "IntegrableDominated",
	Key:  "prop_6e3f3207c274e959",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f h:(A → real).",
		Hypotheses: []string{
			"real_measurable(Ω, S, f)",
			"∀x:A. x ∈ Ω ⇒ |f(x)| ≤ h(x)",
			"real_integrable(Ω, S, μ, h)",
		},
		Conclusion: "real_integrable(Ω, S, μ, f)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f, h *Arrow[A, Real],
		measurable, dominated, integrable Fact,
	) {
		below := a.Have(
			"on Ω the embedding of |f| lies below that of |h|, |f| lying below h and so below |h|",
			"∀x:A. x ∈ Ω ⇒ extended_of_real(|f(x)|) ≤ extended_of_real(|h(x)|)",
			ByArith(dominated, extended_nonneg_real.OfRealLe, real_sgn_abs.AbsNonneg))
		a.Show(
			"so the integral of |f| lies below the finite integral of |h|",
			By(
				measurable,
				integrable,
				below,
				nonneg_integral.NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|h(x)|)")),
				extended_nonneg_real.ExtendedLeDef,
				RealIntegrableDef.At(Ω, S, μ, f),
				RealIntegrableDef.At(Ω, S, μ, h)))
	}),
})}

// IntegrablePartsFinite — the two parts of an integrable function, the
// embeddings of f and of −f in [0, ∞], have finite integrals: each lies
// below the embedding of |f|, whose integral is finite. No structure is
// asked of Ω, S or μ.
var IntegrablePartsFinite = integrablePartsFiniteThm{family.Add(registry.ProofEntry{
	Name: "IntegrablePartsFinite",
	Key:  "prop_31ae0f60944c49f1",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real).",
		Hypotheses: []string{"real_integrable(Ω, S, μ, f)"},
		Conclusion: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x))) ≠ extended_infinity ∧ " +
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x))) ≠ extended_infinity",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, Real],
		integrable Fact,
	) {
		abs := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)")
		below := a.Have(
			"the embeddings of f and of −f lie below that of |f|",
			"∀x:A. "+
				"    extended_of_real(f(x)) ≤ extended_of_real(|f(x)|) ∧ "+
				"    extended_of_real(-f(x)) ≤ extended_of_real(|f(x)|)",
			ByArith(extended_nonneg_real.OfRealLe, real_sgn_abs.AbsNonneg))
		a.Show(
			"so each integral lies below the finite integral of |f|",
			By(
				integrable,
				below,
				nonneg_integral.NonnegIntegralMono.At(
					Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))"), abs),
				nonneg_integral.NonnegIntegralMono.At(
					Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))"), abs),
				extended_nonneg_real.ExtendedLeDef,
				RealIntegrableDef.At(Ω, S, μ, f)))
	}),
})}

// IntegrableAdd — a sum of integrable functions is integrable: it is
// measurable, and the embedding of |f + g| lies below the sum of the
// embeddings of |f| and |g|, whose integral is the sum of their two finite
// integrals (NonnegIntegralAdd).
var IntegrableAdd = integrableAddThm{family.Add(registry.ProofEntry{
	Name: "IntegrableAdd",
	Key:  "prop_aed81b30ea68c4fd",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f g:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. f(x) + g(x))",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f, g *Arrow[A, Real],
		integrableF, integrableG Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		absF := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)")
		absG := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|g(x)|)")
		measurable := a.Have(
			"f and g are measurable, and so are the embeddings of |f| and |g|",
			"real_measurable(Ω, S, f) ∧ "+
				"real_measurable(Ω, S, g) ∧ "+
				"extended_measurable(Ω, S, λx:A. extended_of_real(|f(x)|)) ∧ "+
				"extended_measurable(Ω, S, λx:A. extended_of_real(|g(x)|))",
			By(
				sigma,
				integrableF,
				integrableG,
				RealIntegrableDef.At(Ω, S, μ, f),
				RealIntegrableDef.At(Ω, S, μ, g),
				measurable_function.RealMeasurableAbs.At(Ω, S, f),
				measurable_function.RealMeasurableAbs.At(Ω, S, g),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |f(x)|")),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |g(x)|"))))
		sum := a.Have(
			"the integral of the sum of those embeddings is the sum of their integrals",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|) + extended_of_real(|g(x)|)) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|)) + "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|g(x)|))",
			By(measure, measurable, nonneg_integral.NonnegIntegralAdd.At(Ω, S, μ, absF, absG)))
		triangle := a.Have(
			"the embedding of |f + g| lies below the sum of the embeddings of |f| and |g|",
			"∀x:A. extended_of_real(|f(x) + g(x)|) ≤ extended_of_real(|f(x)|) + extended_of_real(|g(x)|)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				fx := b.TermAs[Real]("|f(x)|")
				gx := b.TermAs[Real]("|g(x)|")
				b.Show(
					"|f(x) + g(x)| ≤ |f(x)| + |g(x)|, both nonnegative",
					ByArith(
						extended_nonneg_real.OfRealAdd.At(fx, gx),
						extended_nonneg_real.OfRealLe.At(
							b.TermAs[Real]("|f(x) + g(x)|"), b.TermAs[Real]("|f(x)| + |g(x)|")),
						real_sgn_abs.AbsNonneg))
			}))
		a.Show(
			"so f + g is measurable, and the integral of |f + g| lies below a sum of two finite integrals",
			By(
				sigma,
				integrableF,
				integrableG,
				measurable,
				sum,
				triangle,
				RealIntegrableDef.At(Ω, S, μ, f),
				RealIntegrableDef.At(Ω, S, μ, g),
				RealIntegrableDef.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. f(x) + g(x)")),
				measurable_function.RealMeasurableAdd.At(Ω, S, f, g),
				nonneg_integral.NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x) + g(x)|)"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|) + extended_of_real(|g(x)|)")),
				extended_nonneg_real.ExtendedLeDef,
				extended_nonneg_real.AddEqInfinity))
	}),
})}

// IntegrableScale — a real multiple of an integrable function is
// integrable: it is measurable, and the embedding of |c·f| is the embedding
// of |c| times that of |f|, whose integral is |c| times the finite integral
// of |f| (NonnegIntegralScale).
var IntegrableScale = integrableScaleThm{family.Add(registry.ProofEntry{
	Name: "IntegrableScale",
	Key:  "prop_b5cd71c7e39f543c",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀f:(A → real). ∀c:real.",
		Hypotheses: []string{"real_integrable(Ω, S, μ, f)"},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. c * f(x))",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f *Arrow[A, Real],
		c *Expr[Real],
		integrable Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		parts := a.Conjuncts(
			a.Unfolded(integrable, RealIntegrableDef),
			"f is measurable",
			"and |f| has a finite integral")
		product := a.Have(
			"the embedding of |c·f| is the embedding of |c| times that of |f|",
			"(λx:A. extended_of_real(|c * f(x)|)) = (λx:A. extended_of_real(|c|) * extended_of_real(|f(x)|))",
			Funext(),
			By(real_sgn_abs.AbsMul, extended_nonneg_real.OfRealMul, real_sgn_abs.AbsNonneg))
		scaled := a.Have(
			"whose integral is |c| times the integral of |f|",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|c|) * extended_of_real(|f(x)|)) = "+
				"extended_of_real(|c|) * nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|))",
			By(
				measure,
				real_sgn_abs.AbsNonneg.At(c),
				nonneg_integral.NonnegIntegralScale.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)"),
					a.TermAs[Real]("|c|"))))
		a.Show(
			"so c·f is measurable, and the integral of |c·f| is a real multiple of a finite value",
			Unfold(RealIntegrableDef),
			product.Rw(),
			By(
				sigma,
				parts[0],
				parts[1],
				scaled,
				measurable_function.RealMeasurableScale.At(Ω, S, f, c),
				extended_nonneg_real.MulEqInfinity,
				extended_nonneg_real.OfRealNotInfinity))
	}),
})}

// IntegrableSub — a difference of integrable functions is integrable: f − g
// is the sum of f and (−1)·g, and a multiple of an integrable function is
// integrable.
var IntegrableSub = integrableSubThm{family.Add(registry.ProofEntry{
	Name: "IntegrableSub",
	Key:  "prop_950f1f03c95ee1ae",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f g:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. f(x) - g(x))",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f, g *Arrow[A, Real],
		integrableF, integrableG Fact,
	) {
		sum := a.Have(
			"f − g is f plus (−1)·g",
			"(λx:A. f(x) - g(x)) = (λx:A. f(x) + -&1 * g(x))",
			Funext(),
			ByArith())
		a.Show(
			"a sum of integrable functions, the second a multiple of g",
			sum.Rw(),
			By(
				measure,
				integrableF,
				integrableG,
				IntegrableScale.At(Ω, S, μ, g, a.TermAs[Real]("-&1")),
				IntegrableAdd.At(Ω, S, μ, f, a.TermAs[Fun[A, Real]]("λx:A. -&1 * g(x)"))))
	}),
})}

// IntegrableAbs — the absolute value of an integrable function is
// integrable: |f| is measurable, and the absolute value of |f| is |f| itself.
var IntegrableAbs = integrableAbsThm{family.Add(registry.ProofEntry{
	Name: "IntegrableAbs",
	Key:  "prop_4fb06ecd4fa6dfd",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)", "real_integrable(Ω, S, μ, f)"},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. |f(x)|)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, Real],
		h Fact,
	) {
		a.Show(
			"|f| is measurable and its absolute value is itself",
			Simp(Fwd(RealIntegrableDef), Fwd(real_sgn_abs.AbsIdempotent)),
			By(h, RealIntegrableDef.At(Ω, S, μ, f), measurable_function.RealMeasurableAbs.At(Ω, S, f)))
	}),
})}
