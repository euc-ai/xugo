package index_comparison

import (
	"github.com/euc-ai/xugo/library/registry"
)

var tangentOpenPushDef = tangentOpenPushDefThm{family.Define(registry.DefEntry{
	Name:  "tangentOpenPushDef",
	Key:   "prop_76abbd401401bb02",
	Const: "tangent_open_push",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"set(prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"            prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))) → " +
		"set(prod(prod(num, prod(B, prod(set(B), B → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(B, prod(set(B), B → num → real) → num → real) → num → num → complex), " +
		"            prod(B, prod(set(B), B → num → real) → num → real) → num → num → complex)))",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))). " +
			"    tangent_open_push(n, T, 𝒜, S, ℬ, f, a) = " +
			"    kc_open_extension(tangent_topology⟨n⟩(S, ℬ), " +
			"        image(tangent_map⟨n, n⟩(T, 𝒜, S, ℬ, f), tangent_bundle⟨n⟩(T, 𝒜)), " +
			"        kc_pullback(subtopology(tangent_topology⟨n⟩(S, ℬ), " +
			"                image(tangent_map⟨n, n⟩(T, 𝒜, S, ℬ, f), tangent_bundle⟨n⟩(T, 𝒜))), " +
			"            inverse_on(tangent_bundle⟨n⟩(T, 𝒜), tangent_map⟨n, n⟩(T, 𝒜, S, ℬ, f)), " +
			"            a))",
	},
})}

var tangentAnalyticDef = tangentAnalyticDefThm{family.Define(registry.DefEntry{
	Name:  "tangentAnalyticDef",
	Key:   "prop_a0356386e523442f",
	Const: "tangent_analytic_index",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"            prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))) → " +
		"int",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))). " +
			"    tangent_analytic_index(n, T, 𝒜, a) = " +
			"    εz:int. ∃g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"        riemannian_metric⟨n⟩(T, 𝒜, g) ∧ " +
			"        z = " +
			"        analytic_index(n, " +
			"            T, " +
			"            𝒜, " +
			"            kc_pullback(cotangent_topology(n, T, 𝒜), " +
			"                inverse_on(tangent_bundle⟨n⟩(T, 𝒜), cotangent_metric_flat(n, T, 𝒜, g)), " +
			"                a))",
	},
})}

var euclideanCoordinatesDef = euclideanCoordinatesDefThm{family.Define(registry.DefEntry{
	Name:  "euclideanCoordinatesDef",
	Key:   "prop_cb4dce0a1e91c546",
	Const: "euclidean_tangent_coordinates",
	Type: "num → " +
		"prod((num → real), prod(set((num → real)), (num → real) → num → real) → num → real) → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀n:num. " +
			"∀p:prod((num → real), prod(set((num → real)), (num → real) → num → real) → num → real). " +
			"∀i:num. " +
			"    euclidean_tangent_coordinates(n, p, i) = " +
			"    COND(i < n, " +
			"        complex_of_real(fst(p)(i)) + " +
			"        complex_i * " +
			"        complex_of_real(snd(p)(({x:(num → real) | vec⟨n⟩(&0, x)}, λx:(num → real). x), i)), " +
			"        complex_of_real(&0))",
	},
})}

var ambientClassDef = ambientClassDefThm{family.Define(registry.DefEntry{
	Name:  "ambientClassDef",
	Key:   "prop_58eedb2fdb2589a9",
	Deps:  []registry.EntryLike{tangentOpenPushDef, euclideanCoordinatesDef},
	Const: "torus_ambient_class",
	Type: "num → " +
		"set(prod(prod(num, (num → complex) → num → num → complex), " +
		"        prod(prod(num, (num → complex) → num → num → complex), " +
		"            (num → complex) → num → num → complex))) → " +
		"set(prod(prod(num, " +
		"            prod((num → complex), " +
		"                prod(set((num → complex)), (num → complex) → num → real) → num → real) → " +
		"            num → " +
		"            num → " +
		"            complex), " +
		"        prod(prod(num, " +
		"                prod((num → complex), " +
		"                    prod(set((num → complex)), (num → complex) → num → real) → num → real) → " +
		"                num → " +
		"                num → " +
		"                complex), " +
		"            prod((num → complex), " +
		"                prod(set((num → complex)), (num → complex) → num → real) → num → real) → " +
		"            num → " +
		"            num → " +
		"            complex)))",
	Equations: []string{
		"∀n:num. " +
			"∀a:set(prod(prod(num, (num → complex) → num → num → complex), " +
			"            prod(prod(num, (num → complex) → num → num → complex), " +
			"                (num → complex) → num → num → complex))). " +
			"    torus_ambient_class(n, a) = " +
			"    tangent_open_push(n, " +
			"        euclidean_topology(n), " +
			"        euclidean_atlas({x:(num → real) | vec⟨n⟩(&0, x)}), " +
			"        smooth_torus_topology(n), " +
			"        smooth_torus_atlas(n), " +
			"        torus_euclidean_map(n), " +
			"        kc_pullback(tangent_topology⟨n⟩(euclidean_topology(n), " +
			"                euclidean_atlas({x:(num → real) | vec⟨n⟩(&0, x)})), " +
			"            euclidean_tangent_coordinates(n), " +
			"            a))",
	},
})}

var AmbientIndexDef = ambientIndexDefThm{family.Define(registry.DefEntry{
	Name:  "AmbientIndexDef",
	Key:   "prop_3aaf0c4ae02d1795",
	Deps:  []registry.EntryLike{tangentAnalyticDef, ambientClassDef},
	Const: "euclidean_analytic_index",
	Type: "num → " +
		"set(prod(prod(num, (num → complex) → num → num → complex), " +
		"        prod(prod(num, (num → complex) → num → num → complex), " +
		"            (num → complex) → num → num → complex))) → " +
		"int",
	Equations: []string{
		"∀n:num. " +
			"∀a:set(prod(prod(num, (num → complex) → num → num → complex), " +
			"            prod(prod(num, (num → complex) → num → num → complex), " +
			"                (num → complex) → num → num → complex))). " +
			"    euclidean_analytic_index(n, a) = " +
			"    tangent_analytic_index(n, " +
			"        smooth_torus_topology(n), " +
			"        smooth_torus_atlas(n), " +
			"        torus_ambient_class(n, a))",
	},
})}
