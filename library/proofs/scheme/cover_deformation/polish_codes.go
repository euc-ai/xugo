package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var CoverExtensionCodesRealize = coverExtensionCodesRealizeThm{family.Add(registry.ProofEntry{
	Name: "CoverExtensionCodesRealize",
	Key:  "prop_73f2a144010ab7d",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D).",
			Hypotheses: []string{"cover_datum(R, S, f, N, g, v, t)", "p ∈ cover_code_ambient(R, S, N).carrier"},
			Conclusion: "p ∈ cover_extension_codes(R, S, f, N, g, v) ⇔ " +
				"cover_extension(R, " +
				"    S, " +
				"    f, " +
				"    N, " +
				"    g, " +
				"    v, " +
				"    cover_code_extensions(S, f, N, p), " +
				"    cover_code_maps(S, N, g, v, p))",
		},
		"Expand the explicit map formula. Its projection is automatically g after "+
			"the source projection; composition is exactly the displayed eta equation."),
	Deps: []registry.EntryLike{coverExtensionCodesDef, coverExtensionDef, coverCodeMapsDef},
	Reading: "Expand the explicit map formula. Its projection is automatically g " +
		"after the source projection; composition is exactly the displayed eta equation.",
})}

var CoverExtensionCodesClosed = coverExtensionCodesClosedThm{family.Add(registry.ProofEntry{
	Name: "CoverExtensionCodesClosed",
	Key:  "prop_155094dbd4a819b4",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{"cover_datum(R, S, f, N, g, v, t)"},
			Conclusion: "subgroup(cover_code_ambient(R, S, N), cover_comparison_codes(R, S, f, N, g, v)) ∧ " +
				"closed_in(cover_code_topology(R, S, N), cover_comparison_codes(R, S, f, N, g, v)) ∧ " +
				"subgroup(cover_code_ambient(R, S, N), cover_extension_codes(R, S, f, N, g, v)) ∧ " +
				"closed_in(cover_code_topology(R, S, N), cover_extension_codes(R, S, f, N, g, v))",
		},
		"The local factor-set equations, actual-map equations and composition equations "+
			"are finite-coordinate homogeneous linear equations in z and eta. Their closed "+
			"solution groups use no strictness of chosen localization sections."),
	Deps: []registry.EntryLike{
		coverComparisonCodesDef,
		coverExtensionCodesDef,
		definable_deformation.FactorSetCodesClosed,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "The local factor-set equations, actual-map equations and composition " +
		"equations are finite-coordinate homogeneous linear equations in z and eta. " +
		"Their closed solution groups use no strictness of chosen localization sections.",
})}

var CoverCoboundaryContinuous = coverCoboundaryContinuousThm{family.Add(registry.ProofEntry{
	Name: "CoverCoboundaryContinuous",
	Key:  "prop_41da03bb0caadb5b",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{"cover_datum(R, S, f, N, g, v, t)"},
			Conclusion: "group_homomorphism(cover_gauge_group(S, N), " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"    cover_coboundary(R, S, f, N, g, v)) ∧ " +
				"continuous_map(cover_gauge_topology(S, N), " +
				"    subtopology(cover_code_topology(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"    cover_coboundary(R, S, f, N, g, v))",
		},
		"Conjugate the split extension diagram by the simultaneous zero-preserving "+
			"shears. The explicit formula is additive and reads finitely many coordinates."),
	Deps: []registry.EntryLike{
		coverCoboundaryDef,
		CoverExtensionCodesClosed,
		definable_deformation.FactorSetShear,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Conjugate the split extension diagram by the simultaneous zero-preserving " +
		"shears. The explicit formula is additive and reads finitely many coordinates.",
})}

var CoverExtensionCodesPolishCover = coverExtensionCodesPolishCoverThm{family.Add(registry.ProofEntry{
	Name: "CoverExtensionCodesPolishCover",
	Key:  "prop_551d25770477d7e1",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"countable(R.carrier)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ countable(S(σ).carrier) ∧ countable(N(σ).carrier)",
			},
			Conclusion: "polish_cover_on( " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"    subtopology(cover_code_topology(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"    cover_boundaries(R, S, f, N, g, v)) ∧ " +
				"polish_abelian_group( " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_comparison_codes(R, S, f, N, g, v)), " +
				"    subtopology(cover_code_topology(R, S, N), cover_comparison_codes(R, S, f, N, g, v)))",
		},
		"Finite nonempty subsets of num and their arrows are countable. The ambient products "+
			"are Polish, both equation spaces are closed, and the gauge image is Polishable."),
	Deps: []registry.EntryLike{
		CoverExtensionCodesClosed,
		CoverCoboundaryContinuous,
		polish_group.ProductGroupPolish,
		polish_group.ContinuousHomImagePolishable,
	},
	Reading: "Finite nonempty subsets of num and their arrows are countable. The ambient " +
		"products are Polish, both equation spaces are closed, and the gauge image is Polishable.",
})}

var CoverExtensionIsoIffBoundary = coverExtensionIsoIffBoundaryThm{family.Add(registry.ProofEntry{
	Name: "CoverExtensionIsoIffBoundary",
	Key:  "prop_7052ab2edd461cf2",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀p q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"p ∈ cover_extension_codes(R, S, f, N, g, v)",
				"q ∈ cover_extension_codes(R, S, f, N, g, v)",
			},
			Conclusion: "(∃h:(set(num) → prod(D, B) → prod(D, B)). " +
				"    cover_extension_iso(R, " +
				"        N, " +
				"        cover_code_extensions(S, f, N, p), " +
				"        cover_code_maps(S, N, g, v, p), " +
				"        cover_code_extensions(S, f, N, q), " +
				"        cover_code_maps(S, N, g, v, q), " +
				"        h)) ⇔ " +
				"cover_code_ambient(R, S, N).mul(p, cover_code_ambient(R, S, N).inv(q)) ∈ " +
				"cover_boundaries(R, S, f, N, g, v)",
		},
		"Objectwise marked isomorphisms are normalized shears. Commuting with "+
			"the arrows is exactly the second component of the cover coboundary."),
	Deps: []registry.EntryLike{
		coverExtensionIsoDef,
		coverCoboundaryDef,
		definable_deformation.FactorSetIsoIffBoundary,
	},
	Reading: "Objectwise marked isomorphisms are normalized shears. Commuting " +
		"with the arrows is exactly the second component of the cover coboundary.",
})}

var CoverExtensionExtraction = coverExtensionExtractionThm{family.Add(registry.ProofEntry{
	Name: "CoverExtensionExtraction",
	Key:  "prop_f3286720d3f7d293",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).∀E:(set(num) → square_zero_ops(A, B, I, D)). " +
				"∀F:(set(num) → set(num) → I → I). " +
				"∀s:(set(num) → B → I).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"cover_extension(R, S, f, N, g, v, E, F)",
				"∀σ:set(num). " +
					"    σ ∈ intersection_indices ⇒ " +
					"    s(σ, S(σ).zero) = E(σ).ring.zero ∧ " +
					"    (∀x:B. x ∈ S(σ).carrier ⇒ s(σ, x) ∈ E(σ).ring.carrier ∧ E(σ).projection(s(σ, x)) = x)",
			},
			Conclusion: "∃p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D). " +
				"    p ∈ cover_extension_codes(R, S, f, N, g, v) ∧ " +
				"    cover_extension_iso(R, " +
				"        N, " +
				"        cover_code_extensions(S, f, N, p), " +
				"        cover_code_maps(S, N, g, v, p), " +
				"        E, " +
				"        F, " +
				"        λσ:set(num). λx:prod(D, B). E(σ).ring.add(E(σ).inclusion(fst(x)), s(σ, snd(x))))",
		},
		"Extract each local factor set. Read eta by subtracting the target "+
			"section from F of the source section and applying the inverse "+
			"inclusion. Strict composition of F gives the eta composition equations."),
	Deps: []registry.EntryLike{
		CoverExtensionCodesRealize,
		coverExtensionIsoDef,
		definable_deformation.FactorSetRealization,
	},
	Reading: "Extract each local factor set. Read eta by subtracting the " +
		"target section from F of the source section and applying the inverse " +
		"inclusion. Strict composition of F gives the eta composition equations.",
})}
