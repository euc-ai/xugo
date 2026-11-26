package cech_cohomology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var polishCechDatumDef = polishCechDatumDefThm{family.Define(registry.DefEntry{
	Name:  "polishCechDatumDef",
	Key:   "prop_cf39d56625ec5fe3",
	Const: "polish_cech_datum",
	Type: "ring_ops(B) → " +
		"set(set(A)) → " +
		"(set(A) → module_ops(B, C)) → " +
		"(set(A) → set(A) → C → C) → " +
		"(num → set(A)) → " +
		"(set(A) → set(set(C))) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(B). " +
			"∀T:set(set(A)). " +
			"∀F:(set(A) → module_ops(B, C)). " +
			"∀res:(set(A) → set(A) → C → C). " +
			"∀U:(num → set(A)). " +
			"∀V:(set(A) → set(set(C))). " +
			"    polish_cech_datum(R, T, F, res, U, V) ⇔ " +
			"    module_presheaf(R, T, F, res) ∧ " +
			"    (∀i:num. U(i) ∈ T) ∧ " +
			"    ⋃image(U, 𝕌) = ⋃T ∧ " +
			"    (∀u:set(A). u ∈ T ⇒ polish_abelian_group(module_additive_group(F(u)), V(u))) ∧ " +
			"    (∀u v:set(A). u ∈ T ∧ v ∈ T ∧ v ⊆ u ⇒ continuous_map(V(u), V(v), res(u, v)))",
	},
	Deps: []registry.EntryLike{modulePresheafDef},
	Reading: "A module presheaf of Polish additive groups " +
		"with continuous restrictions. Scalars need no topology."})}

var polishCechTopologiesDef = polishCechTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "polishCechTopologiesDef",
	Key:   "prop_9012c82bd4db6d34",
	Const: "polish_cech_topologies",
	Type: "(set(A) → module_ops(B, C)) → " +
		"(num → set(A)) → " +
		"(set(A) → set(set(C))) → " +
		"num → " +
		"set(set(prod(num, num → num) → C))",
	Equations: []string{
		"∀F:(set(A) → module_ops(B, C)). ∀U:(num → set(A)). ∀V:(set(A) → set(set(C))). ∀n:num. " +
			"    polish_cech_topologies(F, U, V, n) = " +
			"    indexed_product_topology(cech_indices(n), " +
			"        cech_zero(F, U), " +
			"        λt:prod(num, num → num). V(cech_meet(U, t)))",
	},
	Deps: []registry.EntryLike{cechIndicesDef, cechMeetDef, cechZeroDef},
	Reading: "The existing Cech complex carries the supplied " +
		"factor topologies, without discretizing its section groups."})}

var PolishCechModel = polishCechModelThm{family.Add(registry.ProofEntry{
	Name: "PolishCechModel",
	Key:  "prop_56e6205c68455c92",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(B). " +
				"∀T:set(set(A)). " +
				"∀F:(set(A) → module_ops(B, C)). " +
				"∀res:(set(A) → set(A) → C → C). " +
				"∀U:(num → set(A)). " +
				"∀V:(set(A) → set(set(C))).",
			Hypotheses: []string{"polish_cech_datum(R, T, F, res, U, V)"},
			Conclusion: "polish_cochain_complex(R, " +
				"    cech_complex(R, F, res, U), " +
				"    polish_cech_topologies(F, U, V))",
		},
		"The tuple sets are countable, and each differential coordinate is a finite alternating sum "+
			"of continuous restrictions. Apply ProductGroupPolish and FiniteCoordinateProductContinuous."),
	Deps: []registry.EntryLike{
		polishCechDatumDef,
		polishCechTopologiesDef,
		CechIndicesCountable,
		polish_group.ProductGroupPolish,
		polish_space.FiniteCoordinateProductContinuous,
	},
	Reading: "The tuple sets are countable, and each differential coordinate is a finite alternating " +
		"sum of continuous restrictions. Apply ProductGroupPolish and FiniteCoordinateProductContinuous.",
})}

var PolishCechRefinementContinuous = polishCechRefinementContinuousThm{family.Add(registry.ProofEntry{
	Name: "PolishCechRefinementContinuous",
	Key:  "prop_b89fd0ebfdfa0f4e",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(B). " +
				"∀T:set(set(A)). " +
				"∀F:(set(A) → module_ops(B, C)). " +
				"∀res:(set(A) → set(A) → C → C). " +
				"∀U:(num → set(A)). " +
				"∀V:(set(A) → set(set(C))). " +
				"∀W:(num → set(A)). " +
				"∀r:(num → num).",
			Hypotheses: []string{
				"polish_cech_datum(R, T, F, res, U, V)",
				"polish_cech_datum(R, T, F, res, W, V)",
				"∀i:num. W(i) ⊆ U(r(i))",
			},
			Conclusion: "polish_cochain_map(R, " +
				"    cech_complex(R, F, res, U), " +
				"    polish_cech_topologies(F, U, V), " +
				"    cech_complex(R, F, res, W), " +
				"    polish_cech_topologies(F, W, V), " +
				"    cech_refinement_map(F, res, U, W, r))",
		},
		"The existing refinement formula reads one input coordinate and applies one "+
			"continuous restriction. The presheaf identities prove the cochain-map equations."),
	Deps: []registry.EntryLike{
		PolishCechModel,
		cechRefinementMapDef,
		polish_space.FiniteCoordinateProductContinuous,
	},
	Reading: "The existing refinement formula reads one input coordinate and applies " +
		"one continuous restriction. The presheaf identities prove the cochain-map equations.",
})}

var PolishCechRefinementHomotopy = polishCechRefinementHomotopyThm{family.Add(registry.ProofEntry{
	Name: "PolishCechRefinementHomotopy",
	Key:  "prop_fb125fb5741cd34b",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(B). " +
				"∀T:set(set(A)). " +
				"∀F:(set(A) → module_ops(B, C)). " +
				"∀res:(set(A) → set(A) → C → C). " +
				"∀U:(num → set(A)). " +
				"∀V:(set(A) → set(set(C))). " +
				"∀W:(num → set(A)). " +
				"∀r s:(num → num).",
			Hypotheses: []string{
				"polish_cech_datum(R, T, F, res, U, V)",
				"polish_cech_datum(R, T, F, res, W, V)",
				"∀i:num. W(i) ⊆ U(r(i)) ∧ W(i) ⊆ U(s(i))",
			},
			Conclusion: "∃h:(num → (prod(num, num → num) → C) → (prod(num, num → num) → C)). " +
				"    cochain_homotopy(R, " +
				"        cech_complex(R, F, res, U), " +
				"        cech_complex(R, F, res, W), " +
				"        cech_refinement_map(F, res, U, W, r), " +
				"        cech_refinement_map(F, res, U, W, s), " +
				"        h)",
		},
		"Use the alternating prism of the two index maps. Adjacent faces cancel by the presheaf "+
			"laws; no countability of sections and no continuity of the homotopy are required."),
	Deps: []registry.EntryLike{PolishCechModel, cechRefinementMapDef},
	Reading: "Use the alternating prism of the two index maps. Adjacent faces cancel by the " +
		"presheaf laws; no countability of sections and no continuity of the homotopy are required.",
})}
