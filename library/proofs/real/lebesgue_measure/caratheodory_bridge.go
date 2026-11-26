// caratheodory_bridge.go — Lebesgue measurability is Carathéodory's
// criterion for the Lebesgue outer measure, read on the whole line.

package lebesgue_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/caratheodory"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// MeasurableIffCaratheodory — a set of reals is Lebesgue measurable exactly
// when it is a Carathéodory set of the Lebesgue outer measure on the line:
// both say the set splits every test set additively, and the carrier's
// inclusions hold of every set of reals.
var MeasurableIffCaratheodory = measurableIffCaratheodoryThm{family.Add(registry.ProofEntry{
	Name: "MeasurableIffCaratheodory",
	Key:  "prop_d2d80356ec7b5358",
	Build: family.Theorem(
		"∀s:set(real). lebesgue_measurable(s) ⇔ s ∈ caratheodory_sets(𝕌, lebesgue_outer_measure)",
		func(a *Argument, s *Expr[Set[Real]]) {
			a.Do(Unfold(LebesgueMeasurableDef), Unfold(caratheodory.CaratheodorySetsDef))
			a.Show(
				"both criteria split every test set alike, and every set of reals lies in the line",
				By(set_order.SubsetUniv))
		}),
})}
