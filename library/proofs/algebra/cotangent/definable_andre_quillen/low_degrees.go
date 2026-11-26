package definable_andre_quillen

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cohomology_one"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var ConormalModelHomeomorphism = conormalModelHomeomorphismThm{family.Add(registry.ProofEntry{
	Name: "ConormalModelHomeomorphism",
	Key:  "prop_1064cef95388148b",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "homeomorphic_map(cocycle_topology(«cochains», aq_topologies(R, S, N), 1), " +
			"    «conormalTopology», " +
			"    cocycle_to_conormal(R, S, f, N)) ∧ " +
			"homeomorphic_map(«conormalTopology», " +
			"    cocycle_topology(«cochains», aq_topologies(R, S, N), 1), " +
			"    conormal_to_cocycle(R, S, f, N))",
		Abbrev: Abbrev{
			{Name: "cochains", Text: "cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N)"},
			{Name: "conormalTopology", Text: "subtopology(indexed_discrete_topology( " +
				"        ring_kernel(S.zero, standard_terms(R, S, 0), standard_eps(R, S, f)), " +
				"        λx:U. N.zero, " +
				"        λx:U. N.carrier), " +
				"    {γ:(U → D) | " +
				"        conormal_hom(universe_algebra_ring(R, standard_names(R, S, 0)), " +
				"            S, " +
				"            standard_eps(R, S, f), " +
				"            N, " +
				"            γ)})"},
		},
	},
		"CocycleConormalLinearInverse gives the inverse linear maps on their carriers. Each output of "+
			"cocycle_to_conormal reads the input at x and at zero, and each output of conormal_to_cocycle "+
			"reads it at u minus its representative; FiniteCoordinateContinuous gives both continuities."),
	Deps: []registry.EntryLike{
		cohomology_one.CocycleConormalLinearInverse,
		cohomology_one.CocycleToConormal,
		cohomology_one.ConormalToCocycle,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "The inverse equations hold on the entire normalized functions. " +
		"No countability is needed for this homeomorphism; with countable data " +
		"it identifies the Polish cocycle model with the closed conormal subgroup.",
})}

var ConormalCoboundariesCorrespond = conormalCoboundariesCorrespondThm{family.Add(registry.ProofEntry{
	Name: "ConormalCoboundariesCorrespond",
	Key:  "prop_a72758b4c22b1769",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "image(cocycle_to_conormal(R, S, f, N), " +
			"    coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1)) = " +
			"{γ:(U → D) | " +
			"    ∃d:(U → D). " +
			"        derivation_on(R, " +
			"            universe_algebra_ring(R, standard_names(R, S, 0)), " +
			"            universe_algebra_const(R), " +
			"            scalar_restriction(standard_eps(R, S, f), N), " +
			"            d) ∧ " +
			"        γ = " +
			"        λx:U. " +
			"            COND(x ∈ ring_kernel(S.zero, standard_terms(R, S, 0), standard_eps(R, S, f)), " +
			"                d(x), " +
			"                N.zero)}",
	},
		"CotangentCoboundaryConormal identifies the inverse image of the coboundaries under "+
			"conormal_to_cocycle with derivation restrictions. CocycleConormalLinearInverse "+
			"converts it into the image equality for the homeomorphism."),
	Deps: []registry.EntryLike{
		cohomology_one.CotangentCoboundaryConormal,
		cohomology_one.CocycleConormalLinearInverse,
		partial_derivative.DerivationRestrictionConormal,
	},
	Reading: "This identifies the actual boundary subgroup, not its " +
		"closure. The restriction is normalized off the presentation kernel, " +
		"even though a derivation itself may have arbitrary off-carrier values.",
})}

var DerivationModelHomeomorphism = derivationModelHomeomorphismThm{family.Add(registry.ProofEntry{
	Name: "DerivationModelHomeomorphism",
	Key:  "prop_335e6104fe96b6ec",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"module_on(S, N)",
		},
		Conclusion: "homeomorphic_map(cocycle_topology(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
			"        aq_topologies(R, S, N), " +
			"        0), " +
			"    subtopology(indexed_discrete_topology(S.carrier, λy:B. N.zero, λy:B. N.carrier), " +
			"        {d:(B → D) | derivation_on(R, S, f, N, d)}), " +
			"    λc:(U → D). λy:B. COND(y ∈ S.carrier, c(carrier_tag(S.carrier, y)), N.zero))",
	},
		"CotangentLowCoboundaries says a zero cocycle is precisely a derivation of the "+
			"presentation that factors through its augmentation. CarrierTagInjective and "+
			"CarrierTagDecode relabel its degree-zero names by S.carrier in both directions; both "+
			"normalized maps read one coordinate, so FiniteCoordinateContinuous makes them continuous."),
	Deps: []registry.EntryLike{
		cohomology_one.CotangentLowCoboundaries,
		simplicial_ring.CarrierTagInjective,
		simplicial_ring.CarrierTagDecode,
		partial_derivative.FreeAlgebraDerivationFromValues,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "derivation_on alone imposes no off-carrier normalization. Intersecting " +
		"its class with the normalized indexed-function space is essential for a " +
		"homeomorphism; arbitrary off-carrier extensions are not extra points of the target.",
})}
