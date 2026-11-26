// definitions.go — the singular simplicial set of a space: its
// n-simplices are the continuous maps of the standard n-simplex into the
// space, each normalized to `junk` off the simplex so that a map is
// determined by its values on it; its faces and degeneracies precompose
// with the cofaces and codegeneracies of the standard simplices; and a
// continuous map acts on it by postcomposition.

package singular_set

import (
	"github.com/euc-ai/xugo/library/registry"
)

// SingularSimplicesDef — `singular_simplices(T, n)`: the singular
// n-simplices of the space, the normalized continuous maps of the standard
// n-simplex, read as a subspace of ℝⁿ⁺¹, into it.
var SingularSimplicesDef = singularSimplicesDefThm{family.Define(registry.DefEntry{
	Name:     "SingularSimplicesDef",
	Key:      "prop_329d3711e4959edc",
	Const:    "singular_simplices",
	Type:     "set(set(A)) → num → set((num → real) → A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀n:num. " +
			"    singular_simplices(T, n) = " +
			"    continuous_hom_set(subtopology(euclidean_topology(n + 1), euclidean_simplex(n)), T)",
	},
})}

// SingularSetDef — `singular_set(T)`: the simplicial set of singular
// simplices. The i-th face of an n-simplex is its restriction along the
// i-th coface of Δⁿ⁻¹, the i-th degeneracy its composite with the i-th
// codegeneracy of Δⁿ⁺¹, each normalized again off its simplex.
var SingularSetDef = singularSetDefThm{family.Define(registry.DefEntry{
	Name:  "SingularSetDef",
	Key:   "prop_d4f5ee0001efcc62",
	Const: "singular_set",
	Type:  "set(set(A)) → simplicial_ops((num → real) → A)",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    singular_set(T) = " +
			"    mk_simplicial(λn:num. singular_simplices(T, n), " +
			"        λn:num. λi:num. λσ:((num → real) → A). " +
			"            normalize_on(euclidean_simplex(n - 1), junk, σ ∘ euclidean_coface(i)), " +
			"        λn:num. λi:num. λσ:((num → real) → A). " +
			"            normalize_on(euclidean_simplex(n + 1), junk, σ ∘ euclidean_codegeneracy(i)))",
	},
	Reading: "The face of a 0-simplex is a value the simplicial identities never read.",
	Deps:    []registry.EntryLike{SingularSimplicesDef},
})}

// SingularMapDef — `singular_map(f)`: the simplicial map a map of spaces
// induces, f after each singular simplex, normalized off the simplex.
var SingularMapDef = singularMapDefThm{family.Define(registry.DefEntry{
	Name:  "SingularMapDef",
	Key:   "prop_ac179ceef6d5cef9",
	Const: "singular_map",
	Type:  "(A → B) → num → ((num → real) → A) → (num → real) → B",
	Equations: []string{
		"∀f:(A → B). " +
			"    singular_map(f) = " +
			"    λn:num. λσ:((num → real) → A). normalize_on(euclidean_simplex(n), junk, f ∘ σ)",
	},
})}
