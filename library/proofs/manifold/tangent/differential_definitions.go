// The differential chooses one source chart at the base point and
// evaluates every active target component by the coordinate Jacobian;
// into Euclidean space it is read in the global identity chart.

package tangent

import "github.com/euc-ai/xugo/library/registry"

// DifferentialDef — the fiber differential as a normalized target family.
var DifferentialDef = differentialDefThm{family.Define(registry.DefEntry{
	Name:  "DifferentialDef",
	Key:   "prop_b7147e4f054fb7e5",
	Const: "manifold_differential",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"A → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"prod(set(B), B → num → real) → " +
		"num → " +
		"real",
	Reading: "The epsilon source chart contains x whenever the source is a " +
		"manifold and x lies in its carrier. Target components are zero on " +
		"incompatible charts and charts missing f(x); DifferentialCoordinate supplies " +
		"the formula for any active source chart, so consumers need not use the choice.",
	Dimensions: []string{"n", "m"},
	Equations: []string{
		"∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real). " +
			"∀d:prod(set(B), B → num → real). " +
			"    manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, x, v, d) = " +
			"    COND(compatible_chart⟨m⟩(S, ℬ, d) ∧ f(x) ∈ fst(d), " +
			"        matrix_act⟨n⟩(vec_jacobian_matrix⟨n, m⟩(«coordinate map»(«source chart», d, f), " +
			"                snd(«source chart»)(x)), " +
			"            v(«source chart»)), " +
			"        λi:num. &0)",
	},
})}

// TangentMapDef — the map on paired total spaces induced by a base map.
var TangentMapDef = tangentMapDefThm{family.Define(registry.DefEntry{
	Name:  "TangentMapDef",
	Key:   "prop_c53b4bb2fd73a22f",
	Const: "tangent_map",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"prod(A, prod(set(A), A → num → real) → num → real) → " +
		"prod(B, prod(set(B), B → num → real) → num → real)",
	Deps:       []registry.EntryLike{DifferentialDef},
	Dimensions: []string{"n", "m"},
	Equations: []string{
		"∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"    tangent_map⟨n, m⟩(T, 𝒜, S, ℬ, f, p) = " +
			"    (f(fst(p)), manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, fst(p), snd(p)))",
	},
})}

// EuclideanDifferentialDef — the differential of a map into ℝᴺ as an N-vector.
var EuclideanDifferentialDef = euclideanDifferentialDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanDifferentialDef",
	Key:   "prop_51ea156ee11a7a2b",
	Const: "manifold_euclidean_differential",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"A → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"num → " +
		"real",
	Dimensions: []string{"n", "N"},
	Reading: "Evaluate the Euclidean-target tangent family in its global " +
		"identity chart. On genuine tangent vectors of a smooth map this is a " +
		"normalized N-vector; no tangent-family representative is chosen.",
	Deps: []registry.EntryLike{DifferentialDef},
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real). " +
			"    manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(x, v) = " +
			"    manifold_differential⟨n, N⟩(T, " +
			"        𝒜, " +
			"        euclidean_topology(N), " +
			"        euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
			"        i, " +
			"        x, " +
			"        v, " +
			"        ({y:num → real | vec⟨N⟩(y)}, identity_map))",
	},
})}
