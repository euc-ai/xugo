// general_bridge.go — the Lebesgue measurable functions are the real
// measurable functions of the general theory, read on the line with the
// σ-algebra of Lebesgue measurable sets; the chapter's simple functions and
// their integral are the general ones there, with the Lebesgue outer
// measure; and on a nonnegative function the chapter's integral is the
// general nonnegative integral of its embedding in [0, ∞]. The chapter's
// facts about them are the general ones read through these bridges.

package lebesgue_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// MeasurableFunctionIffRealMeasurable — a function on the line is Lebesgue
// measurable exactly when it is measurable for the σ-algebra of Lebesgue
// measurable sets on the whole line. Both say that every upper ray
// {x | c < f(x)} is measurable, the ray criterion of the general theory
// read at the Lebesgue σ-algebra; on the whole line the carrier cuts
// nothing off a ray.
var MeasurableFunctionIffRealMeasurable = measurableFunctionIffRealMeasurableThm{family.Add(registry.ProofEntry{
	Name: "MeasurableFunctionIffRealMeasurable",
	Key:  "prop_8cbdfe24bfe39567",
	Build: family.Theorem("∀f:(real → real). "+
		"    lebesgue_measurable_function(f) ⇔ "+
		"    real_measurable(𝕌, {s:set(real) | lebesgue_measurable(s)}, f)",
		func(a *Argument, f *Arrow[Real, Real]) {
			a.Do(
				Unfold(LebesgueMeasurableFunctionDef),
				Simp(Fwd(measurable_function.RealMeasurableIffRay.Read(lebesgue_measure.LebesgueSigmaAlgebra))))
			a.Show(
				"on the whole line each upper ray is the same set either way",
				By(set_basic.InUniv))
		}),
})}

// ContinuousLebesgueMeasurable — a function continuous on the line is
// measurable for the Lebesgue measurable sets: it is Borel measurable
// (ContinuousBorelMeasurable), and every Borel set is Lebesgue measurable
// (MeasurableBorel), so the larger σ-algebra takes its preimages too.
var ContinuousLebesgueMeasurable = continuousLebesgueMeasurableThm{family.Add(registry.ProofEntry{
	Name: "ContinuousLebesgueMeasurable",
	Key:  "prop_b97602d3f9985e27",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real).",
		Hypotheses: []string{
			"real_continuous_on(𝕌, f)",
		},
		Conclusion: "real_measurable(𝕌, {s:set(real) | lebesgue_measurable(s)}, f)",
	},
		func(a *Argument, f *Arrow[Real, Real], continuous Fact) {
			borelSets := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			lebesgueSets := a.TermAs[Set[Set[Real]]]("{s:set(real) | lebesgue_measurable(s)}")
			borel := a.Have(
				"a function continuous on the line is Borel measurable",
				"real_measurable(𝕌, borel_sets(real_topology), f)",
				By(continuous, borel_function.ContinuousBorelMeasurable.At(f)))
			inclusion := a.Have(
				"every Borel set is Lebesgue measurable",
				"borel_sets(real_topology) ⊆ {s:set(real) | lebesgue_measurable(s)}",
				BySets(lebesgue_measure.MeasurableBorel))
			a.Show(
				"so the Lebesgue measurable sets take every preimage the Borel sets do",
				By(
					borel,
					inclusion,
					measurable_function.RealMeasurableSourceMono.At(
						a.TermAs[Set[Real]]("𝕌"), borelSets, lebesgueSets, f)))
		}),
})}

// LebesgueSimpleIff — a function on the line is a nonnegative simple
// function of the chapter exactly when it is one of the general theory for
// the Lebesgue σ-algebra on the whole line: measurable in either sense by
// MeasurableFunctionIffRealMeasurable, and with the same finitely many
// values and the same sign, 𝕌 being the line.
var LebesgueSimpleIff = lebesgueSimpleIffThm{family.Add(registry.ProofEntry{
	Name: "LebesgueSimpleIff",
	Key:  "prop_857d491a45f32b99",
	Build: family.Theorem("∀s:(real → real). "+
		"    lebesgue_simple(s) ⇔ measure_simple(𝕌, {u:set(real) | lebesgue_measurable(u)}, s)",
		func(a *Argument, s *Arrow[Real, Real]) {
			a.Show(
				"both definitions ask measurability, finitely many values and a nonnegative sign",
				By(
					lebesgueSimpleDef,
					measure_simple.NonnegSimpleDef,
					MeasurableFunctionIffRealMeasurable,
					set_basic.InUniv))
		}),
})}

// LebesgueSimpleIntegralEq — the chapter's simple integral is the general
// one on the whole line with the Lebesgue outer measure: both sum, over the
// values y of s, y times the measure of the set where s takes the value y,
// and on 𝕌 that set is the same either way. No simplicity is needed.
var LebesgueSimpleIntegralEq = lebesgueSimpleIntegralEqThm{family.Add(registry.ProofEntry{
	Name: "LebesgueSimpleIntegralEq",
	Key:  "prop_6bfce07985db5823",
	Build: family.Theorem("∀s:(real → real). "+
		"    lebesgue_simple_integral(s) = measure_simple_integral(𝕌, lebesgue_outer_measure, s)",
		func(a *Argument, s *Arrow[Real, Real]) {
			a.Do(
				Simp(Fwd(LebesgueSimpleIntegralDef), Fwd(measure_simple.SimpleIntegralDef), Fwd(set_basic.InUniv)))
			a.Show(
				"the two sums agree term by term",
				Basic())
		}),
})}

// LebesgueNonnegIntegralEq — on a nonnegative function on the line the
// chapter's integral is the general nonnegative integral of its embedding
// in [0, ∞], on the whole line with the Lebesgue outer measure. f being
// nonnegative, a function lies below f exactly when its embedding lies
// below f's, so the two suprema range over the same simple integrals. The
// nonnegativity is needed: where f is negative somewhere no simple function
// lies below it and the chapter's integral is 0, while the general one is
// that of the positive part.
var LebesgueNonnegIntegralEq = lebesgueNonnegIntegralEqThm{family.Add(registry.ProofEntry{
	Name: "LebesgueNonnegIntegralEq",
	Key:  "prop_2c16cd7d765a7ba2",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(real → real).",
		Hypotheses: []string{"∀x:real. &0 ≤ f(x)"},
		Conclusion: "lebesgue_nonneg_integral(f) = " +
			"nonneg_integral(𝕌, " +
			"    {s:set(real) | lebesgue_measurable(s)}, " +
			"    lebesgue_outer_measure, " +
			"    λx:real. extended_of_real(f(x)))",
	}, func(a *Argument, f *Arrow[Real, Real], nonneg Fact) {
		minorants := a.Have(
			"a function is a simple function below f in the chapter's "+
				"sense exactly when it is one in the general sense",
			"∀s:(real → real). "+
				"    lebesgue_simple(s) ∧ (∀x:real. s(x) ≤ f(x)) ⇔ "+
				"    measure_simple(𝕌, {u:set(real) | lebesgue_measurable(u)}, s) ∧ "+
				"    (∀x:real. x ∈ 𝕌 ⇒ extended_of_real(s(x)) ≤ extended_of_real(f(x)))",
			By(nonneg, LebesgueSimpleIff, extended_nonneg_real.OfRealLe, set_basic.InUniv))
		a.Do(Unfold(LebesgueNonnegIntegralDef), Unfold(nonneg_integral.NonnegIntegralDef))
		same := a.Have(
			"so the two suprema range over the same simple integrals",
			"{m:extended_nonneg_real | "+
				"    ∃s:(real → real). "+
				"        lebesgue_simple(s) ∧ (∀x:real. s(x) ≤ f(x)) ∧ m = lebesgue_simple_integral(s)} = "+
				"{r:extended_nonneg_real | "+
				"    ∃s:(real → real). "+
				"        measure_simple(𝕌, {u:set(real) | lebesgue_measurable(u)}, s) ∧ "+
				"        (∀x:real. x ∈ 𝕌 ⇒ extended_of_real(s(x)) ≤ extended_of_real(f(x))) ∧ "+
				"        r = measure_simple_integral(𝕌, lebesgue_outer_measure, s)}",
			BySets(minorants, LebesgueSimpleIntegralEq))
		a.Show(
			"and so the suprema agree",
			By(same))
	}),
})}
