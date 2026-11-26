package cech_cohomology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var IntersectionIndicesDef = intersectionIndicesDefThm{family.Define(registry.DefEntry{
	Name:      "IntersectionIndicesDef",
	Key:       "prop_c6b833da091d9a54",
	Const:     "intersection_indices",
	Type:      "set(set(num))",
	Equations: []string{"intersection_indices = {σ:set(num) | finite(σ) ∧ ¬(σ = ∅)}"},
	Deps:      []registry.EntryLike{},
	Reading:   "Finite nonempty sets of chart indices."})}

var OrderedCechIndicesDef = orderedCechIndicesDefThm{family.Define(registry.DefEntry{
	Name:  "OrderedCechIndicesDef",
	Key:   "prop_8c524709d3d880d",
	Const: "ordered_cech_indices",
	Type:  "num → set(prod(num, num → num))",
	Equations: []string{
		"∀n:num. " +
			"    ordered_cech_indices(n) = " +
			"    {t:prod(num, num → num) | t ∈ cech_indices(n) ∧ (∀j:num. j < n ⇒ snd(t, j) < snd(t, j + 1))}",
	},
	Deps: []registry.EntryLike{cechIndicesDef},
	Reading: "Strictly increasing tuples with a zero " +
		"tail, representing oriented finite intersections."})}

var CechSupportDef = cechSupportDefThm{family.Define(registry.DefEntry{
	Name:      "CechSupportDef",
	Key:       "prop_e17baf6fd356df6f",
	Const:     "cech_support",
	Type:      "prod(num, num → num) → set(num)",
	Equations: []string{"∀t:prod(num, num → num). cech_support(t) = image(snd(t), 0 .. fst(t))"},
	Deps:      []registry.EntryLike{},
	Reading:   "The nonempty finite set underlying a Cech tuple."})}

var IntersectionModuleDatumDef = intersectionModuleDatumDefThm{family.Define(registry.DefEntry{
	Name:  "IntersectionModuleDatumDef",
	Key:   "prop_32f6c92bb8f5c3a",
	Const: "intersection_module_datum",
	Type:  "ring_ops(A) → (set(num) → module_ops(A, C)) → (set(num) → set(num) → C → C) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀F:(set(num) → module_ops(A, C)). ∀r:(set(num) → set(num) → C → C). " +
			"    intersection_module_datum(R, F, r) ⇔ " +
			"    (∀σ:set(num). " +
			"        σ ∈ intersection_indices ⇒ " +
			"        module_on(R, F(σ)) ∧ (∀x:C. x ∈ F(σ).carrier ⇒ r(σ, σ, x) = x)) ∧ " +
			"    (∀σ τ:set(num). " +
			"        σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
			"        module_homomorphism(R, F(σ), F(τ), r(σ, τ))) ∧ " +
			"    (∀σ τ υ:set(num). ∀x:C. " +
			"        σ ∈ intersection_indices ∧ " +
			"        τ ∈ intersection_indices ∧ " +
			"        υ ∈ intersection_indices ∧ " +
			"        σ ⊆ τ ∧ " +
			"        τ ⊆ υ ∧ " +
			"        x ∈ F(σ).carrier ⇒ " +
			"        r(τ, υ, r(σ, τ, x)) = r(σ, υ, x))",
	},
	Deps: []registry.EntryLike{IntersectionIndicesDef},
	Reading: "A strict module diagram on finite intersections, " +
		"with restriction in the direction of inclusion of index sets."})}

var IntersectionCechComplexDef = intersectionCechComplexDefThm{family.Define(registry.DefEntry{
	Name:  "IntersectionCechComplexDef",
	Key:   "prop_407f9018b90678cc",
	Const: "intersection_cech_complex",
	Type: "ring_ops(A) → " +
		"(set(num) → module_ops(A, C)) → " +
		"(set(num) → set(num) → C → C) → " +
		"complex_ops(A, prod(num, num → num) → C)",
	Equations: []string{
		"∀R:ring_ops(A). ∀F:(set(num) → module_ops(A, C)). ∀r:(set(num) → set(num) → C → C). " +
			"    intersection_cech_complex(R, F, r) = " +
			"    pack_complex(λv:(prod(num, num → num) → C). " +
			"        λw:(prod(num, num → num) → C). " +
			"        λt:prod(num, num → num). " +
			"            F(cech_support(t)).add(v(t), w(t)), " +
			"        λt:prod(num, num → num). F(cech_support(t)).zero, " +
			"        λw:(prod(num, num → num) → C). λt:prod(num, num → num). F(cech_support(t)).neg(w(t)), " +
			"        λa:A. λw:(prod(num, num → num) → C). λt:prod(num, num → num). " +
			"            F(cech_support(t)).smul(a, w(t)), " +
			"        λn:num. " +
			"            indexed_functions(ordered_cech_indices(n), " +
			"                λt:prod(num, num → num). F(cech_support(t)).zero, " +
			"                λt:prod(num, num → num). F(cech_support(t)).carrier), " +
			"        λn:num. λw:(prod(num, num → num) → C). λt:prod(num, num → num). " +
			"            COND(t ∈ ordered_cech_indices(n + 1), " +
			"                module_sum(F(cech_support(t)).add, " +
			"                    F(cech_support(t)).zero, " +
			"                    0 .. n + 1, " +
			"                    λi:num. " +
			"                        F(cech_support(t)).smul(alternating_sign(R.one, R.neg, i), " +
			"                            r(cech_support(cech_delete(t, i)), " +
			"                                cech_support(t), " +
			"                                w(cech_delete(t, i))))), " +
			"                F(cech_support(t)).zero))",
	},
	Deps: []registry.EntryLike{cechDeleteDef, CechSupportDef, OrderedCechIndicesDef},
	Reading: "The alternating Cech complex on increasing tuples, " +
		"with the same zero-tail and deletion conventions as cech_complex."})}

var IntersectionCechTopologiesDef = intersectionCechTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "IntersectionCechTopologiesDef",
	Key:   "prop_72fc47233ed4aa7d",
	Const: "intersection_cech_topologies",
	Type: "(set(num) → module_ops(A, C)) → " +
		"(set(num) → set(set(C))) → " +
		"num → " +
		"set(set(prod(num, num → num) → C))",
	Equations: []string{
		"∀F:(set(num) → module_ops(A, C)). ∀T:(set(num) → set(set(C))). ∀n:num. " +
			"    intersection_cech_topologies(F, T, n) = " +
			"    indexed_product_topology(ordered_cech_indices(n), " +
			"        λt:prod(num, num → num). F(cech_support(t)).zero, " +
			"        λt:prod(num, num → num). T(cech_support(t)))",
	},
	Deps:    []registry.EntryLike{CechSupportDef, OrderedCechIndicesDef},
	Reading: "Actual factor topologies on all finite intersections."})}

var IntersectionCechCochain = intersectionCechCochainThm{family.Add(registry.ProofEntry{
	Name: "IntersectionCechCochain",
	Key:  "prop_aee43f9de6d7c3ef",
	Build: family.Card(
		Statement{
			Binders:    "∀R:ring_ops(A). ∀F:(set(num) → module_ops(A, C)). ∀r:(set(num) → set(num) → C → C).",
			Hypotheses: []string{"intersection_module_datum(R, F, r)"},
			Conclusion: "cochain_complex(R, intersection_cech_complex(R, F, r))",
		},
		"Deleting two coordinates in opposite orders gives the same restriction by "+
			"strict composition. Alternating signs cancel; each differential is linear."),
	Deps: []registry.EntryLike{IntersectionModuleDatumDef, IntersectionCechComplexDef},
	Reading: "Deleting two coordinates in opposite orders gives the same restriction " +
		"by strict composition. Alternating signs cancel; each differential is linear.",
})}

var IntersectionCechPolishModel = intersectionCechPolishModelThm{family.Add(registry.ProofEntry{
	Name: "IntersectionCechPolishModel",
	Key:  "prop_30bf74f65e47e55c",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀F:(set(num) → module_ops(A, C)). " +
				"∀r:(set(num) → set(num) → C → C). " +
				"∀T:(set(num) → set(set(C))).",
			Hypotheses: []string{
				"intersection_module_datum(R, F, r)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ polish_abelian_group(module_additive_group(F(σ)), T(σ))",
				"∀σ τ:set(num). " +
					"    σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
					"    continuous_map(T(σ), T(τ), r(σ, τ))",
			},
			Conclusion: "polish_cochain_complex(R, " +
				"    intersection_cech_complex(R, F, r), " +
				"    intersection_cech_topologies(F, T))",
		},
		"Ordered tuple sets are subsets of the countable zero-tail tuples. Each differential is a finite "+
			"sum of continuous restrictions; use ProductGroupPolish and FiniteCoordinateProductContinuous."),
	Deps: []registry.EntryLike{
		IntersectionCechCochain,
		IntersectionCechTopologiesDef,
		CechIndicesCountable,
		polish_group.ProductGroupPolish,
		polish_space.FiniteCoordinateProductContinuous,
	},
	Reading: "Ordered tuple sets are subsets of the countable zero-tail " +
		"tuples. Each differential is a finite sum of continuous restrictions; " +
		"use ProductGroupPolish and FiniteCoordinateProductContinuous.",
})}
