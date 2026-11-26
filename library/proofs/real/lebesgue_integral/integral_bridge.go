// integral_bridge.go — the chapter's integrable functions and their
// integral are the general ones on the line, with the σ-algebra of
// Lebesgue measurable sets and the Lebesgue outer measure. Integrability
// asks the same two things either way, measurability and a finite
// integral of |f|; the integral is the same difference either way, the
// chapter taking the positive and negative parts of f where the general
// integral embeds f and −f in [0, ∞], which reads each at its positive
// part.

package lebesgue_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// LebesgueIntegrableIff — a function on the line is integrable exactly when
// it is integrable in the general sense for the Lebesgue σ-algebra and the
// Lebesgue outer measure on the whole line. Both ask that f be measurable,
// the same in either sense (MeasurableFunctionIffRealMeasurable), and that
// the integral of |f| be finite, which, |f| being nonnegative, is the same
// integral either way (LebesgueNonnegIntegralEq).
var LebesgueIntegrableIff = lebesgueIntegrableIffThm{family.Add(registry.ProofEntry{
	Name: "LebesgueIntegrableIff",
	Key:  "prop_287741368f9dcbed",
	Build: family.Theorem("∀f:(real → real). "+
		"    lebesgue_integrable(f) ⇔ "+
		"    real_integrable(𝕌, {s:set(real) | lebesgue_measurable(s)}, lebesgue_outer_measure, f)",
		func(a *Argument, f *Arrow[Real, Real]) {
			a.Show(
				"both ask measurability and a finite integral of |f|, and each is the same either way",
				By(
					LebesgueIntegrableDef.At(f),
					measure_integral.RealIntegrableDef.At(
						a.TermAs[Set[Real]]("𝕌"),
						a.TermAs[Set[Set[Real]]]("{s:set(real) | lebesgue_measurable(s)}"),
						a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure"),
						f),
					MeasurableFunctionIffRealMeasurable.At(f),
					LebesgueNonnegIntegralEq.At(a.TermAs[Fun[Real, Real]]("λx:real. |f(x)|")),
					real_sgn_abs.AbsNonneg))
		}),
})}

// LebesguePositivePartEq — the chapter's integral of the positive part of a
// function on the line is the general integral of the function's embedding
// in [0, ∞], with the Lebesgue σ-algebra and the Lebesgue outer measure. The
// positive part is nonnegative, so its integral is the general integral of
// its own embedding (LebesgueNonnegIntegralEq); and the embedding reads a
// real at its positive part, so that embedding is the embedding of f. Read
// at −f, it says the same of the negative part and the embedding of −f.
var LebesguePositivePartEq = lebesguePositivePartEqThm{family.Add(registry.ProofEntry{
	Name: "LebesguePositivePartEq",
	Key:  "prop_bd4f46f910d8ee46",
	Build: family.Theorem("∀f:(real → real). "+
		"    lebesgue_nonneg_integral(λx:real. max(f(x), &0)) = "+
		"    nonneg_integral(𝕌, "+
		"        {s:set(real) | lebesgue_measurable(s)}, "+
		"        lebesgue_outer_measure, "+
		"        λx:real. extended_of_real(f(x)))",
		func(a *Argument, f *Arrow[Real, Real]) {
			clamp := a.Have(
				"the embedding in [0, ∞] reads a real at its positive part",
				"∀r:real. extended_of_real(max(r, &0)) = extended_of_real(r)",
				Derive(func(b *Argument) {
					b.FixAs[Real]("r")
					b.Cases(b.Term("&0 ≤ r"))
					b.When(
						"a nonnegative r is its own positive part",
						func(c *Argument, nonneg Fact) {
							c.Show(
								"max(r, 0) = r",
								ByArith(nonneg))
						})
					b.Otherwise(
						"a negative r and its positive part 0 both embed as 0",
						func(c *Argument, negative Fact) {
							c.Show(
								"each lies at or below 0",
								ByArith(negative, extended_nonneg_real.OfRealNeg))
						})
				}))
			embedded := a.Have(
				"so the embedding of the positive part of f is the embedding of f",
				"(λx:real. extended_of_real(max(f(x), &0))) = (λx:real. extended_of_real(f(x)))",
				Funext(),
				By(clamp))
			a.Show(
				"the positive part is nonnegative, so its integral is the general integral of its embedding",
				ByArith(embedded, LebesgueNonnegIntegralEq.At(a.TermAs[Fun[Real, Real]]("λx:real. max(f(x), &0)"))))
		}),
})}

// LebesgueIntegralEq — the chapter's integral is the general integral on
// the line, with the Lebesgue σ-algebra and the Lebesgue outer measure, at
// every function. The chapter takes the integrals of the positive part
// max(f, 0) and of the negative part max(−f, 0); those are the general
// integrals of the embeddings of f and of −f in [0, ∞]
// (LebesguePositivePartEq at f and at −f), which the general integral takes.
var LebesgueIntegralEq = lebesgueIntegralEqThm{family.Add(registry.ProofEntry{
	Name: "LebesgueIntegralEq",
	Key:  "prop_dbe730e75ef6c40a",
	Build: family.Theorem("∀f:(real → real). "+
		"    lebesgue_integral(f) = "+
		"    measure_integral(𝕌, {s:set(real) | lebesgue_measurable(s)}, lebesgue_outer_measure, f)",
		func(a *Argument, f *Arrow[Real, Real]) {
			a.Show(
				"the integrals of the two parts are the general integrals of the embeddings of f and of −f",
				By(
					LebesgueIntegralDef.At(f),
					measure_integral.RealIntegralDef.At(
						a.TermAs[Set[Real]]("𝕌"),
						a.TermAs[Set[Set[Real]]]("{s:set(real) | lebesgue_measurable(s)}"),
						a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure"),
						f),
					LebesguePositivePartEq.At(f),
					LebesguePositivePartEq.At(a.TermAs[Fun[Real, Real]]("λx:real. -f(x)"))))
		}),
})}
