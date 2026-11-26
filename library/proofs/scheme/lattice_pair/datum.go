// datum.go — the biaffine datum: the two charts play symmetric parts, lie
// in the overlap, each inclusion a localization, and form the structure
// pair, a lattice pair with ambient R; a field inside chart 0 is a subring
// of R.

package lattice_pair

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The datum
// ---------------------------------------------------------------------------

// BiaffineSwap — the datum read with its charts exchanged is a datum: a
// statement about chart 0 holds of chart 1 by this one exchange. Every
// conjunct of the definition has its mirror among the datum's, and the
// one equation that changes, s · t = one, is t · s = one read in the
// commutative ring R.
var BiaffineSwap = biaffineSwapThm{family.Add(registry.ProofEntry{
	Name: "BiaffineSwap",
	Key:  "prop_ee5fede735b857b4",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "biaffine(R, A₁, A₀, s, t)",
	},
		func(a *Argument, R *Expr[RingOps[A]], A0, A1 *Expr[Set[A]], t, s *Expr[A], datum Fact) {
			charts := a.Conjuncts(
				a.Unfolded(datum, BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring := charts[0]
			inR := a.Have(
				"t and s lie in R, through the charts that hold them",
				"t ∈ R.carrier ∧ s ∈ R.carrier",
				BySets(
					comm_ring.SubringSubset.Read(charts[1]),
					comm_ring.SubringSubset.Read(charts[2]),
					charts[3],
					charts[4]))
			inverse := a.Have(
				"so s · t = one, R being commutative",
				"s * t = R.one",
				ByArith(ring, inR, charts[5]))
			a.Show(
				"the exchanged datum is the datum's conjuncts with the "+
					"charts exchanged, s · t = one standing for t · s = one",
				By(BiaffineDef, ring, charts[2], charts[1], charts[4], charts[3], inverse, charts[7], charts[6]))
		}),
})}

// BiaffineChartLocalization — each chart's inclusion into the overlap is
// the localization of the chart at the powers of its element: the
// overlap is A₀[1/t] and A₁[1/s] as rings of fractions, not only as sets.
// R is A₀ with t inverted and t has the inverse s in R, so the inclusion
// of A₀ into R is its localization at the powers of t
// (InclusionIsLocalizationAway); R is also A₁ with s inverted, and s has
// the inverse t, R being commutative, so the same holds of A₁ at s.
var BiaffineChartLocalization = biaffineChartLocalizationThm{family.Add(registry.ProofEntry{
	Name: "BiaffineChartLocalization",
	Key:  "prop_6d850533d1540d55",
	Reading: "The target is R itself: R.carrier = ring_away(R, A₀, t) makes R " +
		"the ring A₀[1/t] computed in place, t a unit of it with inverse s. The " +
		"second conjunct is the first read at the exchanged datum (BiaffineSwap).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
		},
		Conclusion: "is_localization_on(restrict_ring(R, A₀), " +
			"    monoid_powers(R.mul, R.one, t), " +
			"    R, " +
			"    λx:A. x) ∧ " +
			"is_localization_on(restrict_ring(R, A₁), monoid_powers(R.mul, R.one, s), R, λx:A. x)",
	},
		func(a *Argument, R *Expr[RingOps[A]], A0, A1 *Expr[Set[A]], t, s *Expr[A], datum Fact) {
			charts := a.Conjuncts(
				a.Unfolded(datum, BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring := charts[0]
			inR := a.Have(
				"t and s lie in R, through the charts that hold them",
				"t ∈ R.carrier ∧ s ∈ R.carrier",
				BySets(
					comm_ring.SubringSubset.Read(charts[1]),
					comm_ring.SubringSubset.Read(charts[2]),
					charts[3],
					charts[4]))
			inverse := a.Have(
				"so s · t = one, R being commutative",
				"s * t = R.one",
				ByArith(ring, inR, charts[5]))
			chart0 := a.Have(
				"R is A₀ with t inverted and s inverts t, so the "+
					"inclusion of A₀ is its localization at the powers of t",
				"is_localization_on(restrict_ring(R, A₀), monoid_powers(R.mul, R.one, t), R, λx:A. x)",
				By(
					ring,
					charts[1],
					charts[3],
					inR,
					charts[5],
					charts[6],
					ring_away.InclusionIsLocalizationAway.At(R, A0, t, s)))
			chart1 := a.Have(
				"R is A₁ with s inverted and t inverts s, so the "+
					"inclusion of A₁ is its localization at the powers of s",
				"is_localization_on(restrict_ring(R, A₁), monoid_powers(R.mul, R.one, s), R, λx:A. x)",
				By(
					ring,
					charts[2],
					charts[4],
					inR,
					inverse,
					charts[7],
					ring_away.InclusionIsLocalizationAway.At(R, A1, s, t)))
			a.Show(
				"so each chart's inclusion is its localization",
				By(chart0, chart1))
		}),
})}

// ChartSubsetInOverlap — a set lying in chart 0 lies in the overlap R:
// the datum puts chart 0 inside R.
var ChartSubsetInOverlap = chartSubsetInOverlapThm{family.Add(registry.ProofEntry{
	Name: "ChartSubsetInOverlap",
	Key:  "prop_762b3211c35ea5d1",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀S:set(A).",
		Hypotheses: []string{
			"«waBiaffine»",
			"S ⊆ A₀",
		},
		Conclusion: "S ⊆ R.carrier",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			S *Expr[Set[A]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"S lies in chart 0")
			chart0Subring := a.Have(
				"chart 0 is a subring of R",
				"subring(R, A₀)",
				By(a.Unfolded(hypotheses[0], BiaffineDef)))
			a.Show(
				"S lies in R, inside chart 0",
				By(
					set_order.SubsetTrans.At(S, A0, a.TermAs[Set[A]]("R.carrier")),
					hypotheses[1],
					comm_ring.SubringSubset.Read(chart0Subring)))
		}),
})}

// ChartFieldSubring — in a biaffine datum, a field k under R's operations
// lying in chart 0 is a subring of R: k lies in R as chart 0 does, and a
// field under R's operations inside R is a subring of it.
var ChartFieldSubring = chartFieldSubringThm{family.Add(registry.ProofEntry{
	Name: "ChartFieldSubring",
	Key:  "prop_49874f8f2b05d1be",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀k:set(A). ∀inv:(A → A).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
		},
		Conclusion: "subring(R, k)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0")
			datum, subfieldK, kIn0 := hypotheses[0], hypotheses[1], hypotheses[2]
			kInR := a.Have(
				"k lies in R, chart 0 lying there",
				"k ⊆ R.carrier",
				By(ChartSubsetInOverlap.At(R, A0, A1, t, s, k), datum, kIn0))
			a.Show(
				"a field under R's operations inside R is a subring of R",
				By(kInR, subfieldK, field.RingSubfieldSubring.At(R, inv, k)))
		}),
})}

// StructurePairLattice — the structure pair (A₀, A₁) is a lattice pair in
// R as a module over itself, and its ambient is R. Each chart, closed
// under its own scalar action, is a submodule of R over itself, and its
// R-span is the ideal it generates (RegularSpanIsIdealSpan), which holds
// one and so is all of R (IdealOneIff).
var StructurePairLattice = structurePairLatticeThm{family.Add(registry.ProofEntry{
	Name: "StructurePairLattice",
	Key:  "prop_e4f0435e5680444a",
	Reading: "Of the datum only the two subrings and R being a commutative " +
		"ring are used: t, s and the two localizations play no part.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A.",
		Hypotheses: []string{
			"«waBiaffine»",
		},
		Conclusion: "lattice_pair(R, A₀, A₁, regular_module(R), (A₀, A₁)) ∧ " +
			"lattice_pair_ambient(R, regular_module(R), (A₀, A₁)) = R.carrier",
	},
		func(a *Argument, R *Expr[RingOps[A]], A0, A1 *Expr[Set[A]], t, s *Expr[A], datum Fact) {
			charts := a.Conjuncts(
				a.Unfolded(datum, BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring, subring0, subring1 := charts[0], charts[1], charts[2]
			chartLaw := a.Have(
				"a subring is a module over itself and spans R",
				Statement{
					Binders:    "∀S:set(A).",
					Hypotheses: []string{"subring(R, S)"},
					Conclusion: "submodule(restrict_ring(R, S), regular_module(R), S) ∧ " +
						"module_span(R, regular_module(R), S) = R.carrier",
				},
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]()
					chart := b.Assume()
					chartModule := b.Have(
						"the chart is closed under addition and its own scalar action",
						"submodule(restrict_ring(R, S), regular_module(R), S)",
						Derive(func(c *Argument) {
							closed := c.Unfolded(chart, comm_ring.SubringDef)
							c.Show(
								"the subring closure laws give the subgroup and scalar closure",
								By(closed, submodule.SubmoduleDef, group.SubgroupDef))
						}))
					inR := b.Have(
						"the chart lies in R",
						"S ⊆ R.carrier",
						By(comm_ring.SubringSubset.Read(chart)))
					spanIsIdeal := b.Have(
						"its R-span in R is the ideal it generates",
						"module_span(R, regular_module(R), S) = ideal_span(R, S)",
						By(ring, inR, submodule.RegularSpanIsIdealSpan.At(R, S)))
					generated := b.TermAs[Set[A]]("ideal_span(R, S)")
					oneIn := b.Have(
						"holding one, as the chart does",
						"R.one ∈ ideal_span(R, S)",
						BySets(comm_ring.SubringOne.Read(chart), ring_ideal.SpanContains.At(R, S)))
					generatedWhole := b.Have(
						"an ideal of R holding one is all of R",
						"ideal_span(R, S) = R.carrier",
						By(
							inR,
							ring_ideal.SpanIdeal.Read(ring).At(S),
							oneIn,
							ring_ideal.IdealOneIff.Read(ring).At(generated)))
					fullSpan := b.Have(
						"so the chart spans R",
						"module_span(R, regular_module(R), S) = R.carrier",
						By(Normalized, spanIsIdeal, generatedWhole))
					b.Show(
						"the chart has its own module structure and full ambient span",
						By(fullSpan, chartModule))
				}))
			chart0 := a.Have(
				"the first chart is a module and spans R",
				"submodule(restrict_ring(R, A₀), regular_module(R), A₀) ∧ "+
					"module_span(R, regular_module(R), A₀) = R.carrier",
				By(subring0, chartLaw.At(A0)))
			first := a.Conjuncts(
				chart0,
				"A₀ is a module over itself",
				"A₀ spans R")
			chart1 := a.Have(
				"the second chart is a module and spans R",
				"submodule(restrict_ring(R, A₁), regular_module(R), A₁) ∧ "+
					"module_span(R, regular_module(R), A₁) = R.carrier",
				By(subring1, chartLaw.At(A1)))
			second := a.Conjuncts(
				chart1,
				"A₁ is a module over itself",
				"A₁ spans R")
			a.Show(
				"the two chart modules have the same span, which is their ambient R",
				Simp(Fwd(LatticePairDef), Fwd(LatticePairAmbientDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(Normalized, module.RegularModuleOn.Read(ring), first[0], second[0], first[1], second[1]))
		}),
})}
