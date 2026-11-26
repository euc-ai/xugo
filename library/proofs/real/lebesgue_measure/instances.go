package lebesgue_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/caratheodory"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/outer_measure"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// LebesgueMeasureOn — the outer measure restricted to the Lebesgue
// measurable sets is a measure on the real line: they are the Carathéodory
// sets of the outer measure on the line, on which Carathéodory's theorem
// makes an outer measure a measure.
var LebesgueMeasureOn = lebesgueMeasureOnThm{family.Add(registry.ProofEntry{
	Name: "LebesgueMeasureOn",
	Key:  "prop_e2d0ca8c5f40bbbb",
	Build: family.Theorem(
		"measure_on(𝕌, {s:set(real) | lebesgue_measurable(s)}, lebesgue_outer_measure)",
		func(a *Argument) {
			sets := a.Have(
				"the measurable sets are the Carathéodory sets of the outer measure on the line",
				"{s:set(real) | lebesgue_measurable(s)} = caratheodory_sets(𝕌, lebesgue_outer_measure)",
				BySets(MeasurableIffCaratheodory))
			a.Do(sets.Rw())
			a.Show(
				"Carathéodory's theorem, read on the line",
				By(LebesgueOuterMeasureOn, caratheodory.MeasureOnCaratheodory))
		}),
})}

// LebesgueSigmaFinite — Lebesgue measure on the line is σ-finite: the
// closed intervals ⟦−n, n⟧ are measurable, each of finite measure 2n, and
// they cover the line, every real lying between −n and n for some n.
var LebesgueSigmaFinite = lebesgueSigmaFiniteThm{family.Add(registry.ProofEntry{
	Name: "LebesgueSigmaFinite",
	Key:  "prop_810229f6fa87f15d",
	Build: family.Theorem(
		"sigma_finite_on(𝕌, {E:set(real) | lebesgue_measurable(E)}, lebesgue_outer_measure)",
		func(a *Argument) {
			measurable := a.Have(
				"each window ⟦−n, n⟧ is a closed interval, so Lebesgue measurable",
				"∀n:num. lebesgue_measurable(⟦-&n, &n⟧)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"a closed interval is measurable",
						By(MeasurableClosedInterval.At(b.TermAs[Real]("-&n"), b.TermAs[Real]("&n"))))
				}))
			finite := a.Have(
				"and has finite measure, its length 2n",
				"∀n:num. lebesgue_outer_measure(⟦-&n, &n⟧) ≠ extended_infinity",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					ordered := b.Have(
						"−n ≤ n, n being nonnegative",
						"-&n ≤ &n",
						ByArith(real_order_ring.NumNonneg.At(n)))
					b.Show(
						"the measure of ⟦−n, n⟧ is the embedded real n − (−n)",
						By(
							Normalized,
							ordered,
							OuterMeasureClosedInterval.At(b.TermAs[Real]("-&n"), b.TermAs[Real]("&n")),
							extended_nonneg_real.OfRealNotInfinity.At(b.TermAs[Real]("&n - -&n"))))
				}))
			cover := a.Have(
				"every real lies between −n and n for some n, so the windows cover the line",
				"⋃image(λn:num. ⟦-&n, &n⟧, 𝕌) = 𝕌",
				BySets(real_archimedean.ExistsNumBounds))
			windows := a.Have(
				"so the windows are a cover of the line by measurable sets of finite measure",
				"∃w:(num → set(real)). "+
					"    (∀n:num. "+
					"        w(n) ∈ {E:set(real) | lebesgue_measurable(E)} ∧ "+
					"        lebesgue_outer_measure(w(n)) ≠ extended_infinity) ∧ "+
					"    ⋃image(w, 𝕌) = 𝕌",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Fun[Nat, Set[Real]]]("λn:num. ⟦-&n, &n⟧"))
					b.Show(
						"the windows ⟦−n, n⟧",
						BySets(measurable, finite, cover))
				}))
			a.Show(
				"Lebesgue outer measure on the measurable sets is a measure, and the windows make it σ-finite",
				Unfold(measure_space.SigmaFiniteDef),
				By(LebesgueMeasureOn, windows))
		}),
})}

// LebesgueOuterMeasureOn — the interval-cover construction is an outer
// measure on the real line: it vanishes on the empty set, is monotone,
// and is countably subadditive.
var LebesgueOuterMeasureOn = lebesgueOuterMeasureOnThm{family.Add(registry.ProofEntry{
	Name: "LebesgueOuterMeasureOn",
	Key:  "prop_d247890fbac76e79",
	Build: family.Instance(outer_measure.OuterMeasureOn,
		"outer_measure_on(𝕌, lebesgue_outer_measure)",
		Case(
			"the empty set has outer measure zero",
			Cite(OuterMeasureEmpty)),
		Case(
			"inclusion increases outer measure",
			By(OuterMeasureMono)),
		Case(
			"a countable union has outer measure at most the sum of the outer measures",
			Derive(func(b *Argument) {
				b.FixAs[Fun2[Nat, Real, Bool]]("a")
				union := b.Have(
					"the union of the sequence is the union of its values",
					"⋃image(a, 𝕌) = {x:real | ∃n:num. x ∈ a(n)}",
					BySets())
				b.Do(union.Rw())
				b.Show(
					"countable subadditivity bounds the outer measure of the union",
					By(OuterMeasureCountableSubadditive))
			})),
	),
})}
