// measurable.go — Carathéodory's measurable sets: a set s is measurable
// when it splits every set t additively, λ*(t) = λ*(t ∩ s) + λ*(t ∖ s).
// They are the Carathéodory sets of the outer measure on the line
// (MeasurableIffCaratheodory), so they form a σ-algebra on the line, the
// one measure/caratheodory proves for an arbitrary outer measure, read on
// the line.

package lebesgue_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"

	"github.com/euc-ai/xugo/library/proofs/measure/caratheodory"
	"github.com/euc-ai/xugo/library/registry"
)

// LebesgueMeasurableDef — `lebesgue_measurable(s)`: Carathéodory's
// criterion, s cuts every set t into two pieces whose outer measures add
// up to that of t.
var LebesgueMeasurableDef = lebesgueMeasurableDefThm{family.Define(registry.DefEntry{
	Name:  "LebesgueMeasurableDef",
	Key:   "prop_49433697e3f6f5f5",
	Const: "lebesgue_measurable",
	Type:  "set(real) → bool",
	Equations: []string{"∀s:set(real). " +
		"    lebesgue_measurable(s) ⇔ " +
		"    ∀t:set(real). " +
		"        lebesgue_outer_measure(t) = " +
		"        lebesgue_outer_measure(t ∩ s) + lebesgue_outer_measure(t ∖ s)"},
	Deps: []registry.EntryLike{LebesgueOuterMeasureDef},
})}

// LebesgueSigmaAlgebra — the measurable sets form a σ-algebra on the
// line: they are the Carathéodory sets of the outer measure on the line,
// which form a σ-algebra.
var LebesgueSigmaAlgebra = lebesgueSigmaAlgebraThm{family.Add(registry.ProofEntry{
	Name: "LebesgueSigmaAlgebra",
	Key:  "prop_5969396d140c90a4",
	Build: family.Theorem("sigma_algebra_on(𝕌, "+
		"    {s:set(real) | lebesgue_measurable(s)})", func(a *Argument) {
		sets := a.Have(
			"the measurable sets are the Carathéodory sets of the outer measure on the line",
			"{s:set(real) | lebesgue_measurable(s)} = caratheodory_sets(𝕌, lebesgue_outer_measure)",
			BySets(MeasurableIffCaratheodory))
		a.Do(sets.Rw())
		a.Show(
			"the Carathéodory sets of an outer measure form a σ-algebra, read on the line",
			By(LebesgueOuterMeasureOn, caratheodory.SigmaAlgebra))
	}),
})}
