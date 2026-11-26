package definable_andre_quillen

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var AQCoefficientSequenceDefinable = aQCoefficientSequenceDefinableThm{family.Add(registry.ProofEntry{
	Name: "AQCoefficientSequenceDefinable",
	Key:  "prop_ba2cbea5e1e836f2",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N₁:module_ops(C, D). " +
			"∀N₂:module_ops(C, E). " +
			"∀N₃:module_ops(C, F). " +
			"∀i:(D → E). " +
			"∀p:(E → F). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"short_exact_modules(T, N₁, N₂, N₃, i, p)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(N₁.carrier)",
			"countable(N₂.carrier)",
			"countable(N₃.carrier)",
		},
		Conclusion: "cohomology_borel_map(«first», " +
			"    dual_pointwise_topologies(N₁, standard_names(R, S)), " +
			"    n, " +
			"    «middle», " +
			"    dual_pointwise_topologies(N₂, standard_names(R, S)), " +
			"    n, " +
			"    cohomology_map(«middle», «inclusion», n)) ∧ " +
			"cohomology_borel_map(«middle», " +
			"    dual_pointwise_topologies(N₂, standard_names(R, S)), " +
			"    n, " +
			"    «last», " +
			"    dual_pointwise_topologies(N₃, standard_names(R, S)), " +
			"    n, " +
			"    cohomology_map(«last», «projection», n)) ∧ " +
			"cohomology_borel_map(«last», " +
			"    dual_pointwise_topologies(N₃, standard_names(R, S)), " +
			"    n, " +
			"    «first», " +
			"    dual_pointwise_topologies(N₁, standard_names(R, S)), " +
			"    n + 1, " +
			"    coconnecting_hom(«first», «middle», «inclusion», «projection», n))",
		Abbrev: Abbrev{
			{Name: "first", Text: "cotangent_cochain⟨U:U⟩(R, S, f, T, g, N₁)"},
			{Name: "middle", Text: "cotangent_cochain⟨U:U⟩(R, S, f, T, g, N₂)"},
			{Name: "last", Text: "cotangent_cochain⟨U:U⟩(R, S, f, T, g, N₃)"},
			{Name: "inclusion", Text: "λk:num. λw:(U → D). λu:U. i(w(u))"},
			{Name: "projection", Text: "λk:num. λw:(U → E). λu:U. p(w(u))"},
		},
	},
		"The based dual coefficient sequence underlying CotangentCohomologyCoefficientLongExact "+
			"is degreewise short exact. AQScalarPolishModel gives the Polish terms, "+
			"singleton-coordinate dependence gives continuous coefficient maps, and "+
			"CohomologyDefinableFunctor and ConnectingMapDefinable give the three named arrows."),
	Deps: []registry.EntryLike{
		AQScalarPolishModel,
		cotangent_complex.CotangentCohomologyCoefficientLongExact,
		polish_space.FiniteCoordinateContinuous,
		polish_cohomology.CohomologyDefinableFunctor,
		polish_cohomology.ConnectingMapDefinable,
	},
	Reading: "The third arrow changes degree from n to n+1. Its lift uses Borel " +
		"sections; continuity of that lift is not asserted, and T need not be countable.",
})}

var TriangleNamesCountable = triangleNamesCountableThm{family.Add(registry.ProofEntry{
	Name: "TriangleNamesCountable",
	Key:  "prop_c3bb8c78ec136871",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀T:ring_ops(C). ∀p q n:num.",
		Hypotheses: []string{
			"comm_ring(R)",
			"comm_ring(S)",
			"comm_ring(T)",
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(T.carrier)",
		},
		Conclusion: "countable(relative_names⟨U:U⟩(R, S, T, p, q)) ∧ " +
			"countable(triangle_column_names⟨U:U⟩(R, S, T, p, q)) ∧ " +
			"countable(double_total_basis⟨I:U⟩(relative_names(R, S, T), n)) ∧ " +
			"countable(double_total_basis⟨I:U⟩(triangle_column_names(R, S, T), n)) ∧ " +
			"countable( " +
			"    double_total_basis⟨I:U⟩(λp:num. λq:num. image(universe_tag(0), standard_names(R, S, p)), n))",
	},
		"Start with StandardNamesCountable. Induct on the vertical degree of the relative "+
			"names: each successor is a polynomial algebra in the tagged union of two countable "+
			"name sets; each total-degree basis is a finite union of these countable sets."),
	Deps: []registry.EntryLike{StandardNamesCountable},
	Reading: "Only the names, not the modules of all cochains, are countable. " +
		"Total-degree names include the horizontal degree as a tag and range over p+q=n.",
})}

var AQTransitivityDefinable = aQTransitivityDefinableThm{family.Add(registry.ProofEntry{
	Name: "AQTransitivityDefinable",
	Key:  "prop_f9fb2be2e2f35b86",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(T.carrier)",
			"countable(N.carrier)",
		},
		Conclusion: "cohomology_borel_map(«relative», " +
			"    dual_pointwise_topologies(N, standard_names(S, T)), " +
			"    n, " +
			"    «middle», " +
			"    dual_pointwise_topologies(N, standard_names(R, T)), " +
			"    n, " +
			"    co_transitivity_left_map(R, S, f, T, g, N, n)) ∧ " +
			"cohomology_borel_map(«middle», " +
			"    dual_pointwise_topologies(N, standard_names(R, T)), " +
			"    n, " +
			"    «base», " +
			"    dual_pointwise_topologies(N, standard_names(R, S)), " +
			"    n, " +
			"    co_transitivity_right_map(R, S, f, T, g, N, n)) ∧ " +
			"cohomology_borel_map(«base», " +
			"    dual_pointwise_topologies(N, standard_names(R, S)), " +
			"    n, " +
			"    «relative», " +
			"    dual_pointwise_topologies(N, standard_names(S, T)), " +
			"    n + 1, " +
			"    co_transitivity_connecting(R, S, f, T, g, N, n))",
		Abbrev: Abbrev{
			{Name: "relative", Text: "cotangent_cochain⟨U:U⟩(S, T, g, T, λc:C. c, N)"},
			{Name: "middle", Text: "cotangent_cochain⟨U:U⟩(R, T, λa:A. g(f(a)), T, λc:C. c, N)"},
			{Name: "base", Text: "cotangent_cochain⟨U:U⟩(R, S, f, T, g, N)"},
		},
	},
		"TriangleTotalsBased and TriangleNamesCountable give Polish dual total complexes, "+
			"and TriangleTotalSplit gives their short exact sequence. BasedDualMapContinuous "+
			"makes the edges and sequence maps continuous; ConnectingMapDefinable and "+
			"ContinuousQuasiIsoDefinableIso transport its connecting map along the actual edge "+
			"comparisons, while CotangentMapsDualAgreement identifies the two other arrows."),
	Deps: []registry.EntryLike{
		AQScalarPolishModel,
		AQAlgebraMapDefinable,
		TriangleNamesCountable,
		transitivity.TriangleTotalsBased,
		transitivity.TriangleTotalSplit,
		transitivity.CotangentCohomologyTransitivity,
		cotangent_complex.CotangentMapsDualAgreement,
		polish_cohomology.CountableBasedDualPolish,
		polish_cohomology.BasedDualMapContinuous,
		polish_cohomology.CohomologyDefinableFunctor,
		polish_cohomology.ConnectingMapDefinable,
		polish_cohomology.ContinuousQuasiIsoDefinableIso,
	},
	Reading: "These are the existing named arrows of the transitivity sequence. The " +
		"connecting map is defined by dualizing the split sequence of totals and " +
		"inverting the right edge on cohomology; its Borel lift follows that construction.",
})}
