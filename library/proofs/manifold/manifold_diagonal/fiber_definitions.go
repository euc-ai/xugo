// A chart identifies a tangent-disk fiber and its diagonal map with Euclidean coordinates.

package manifold_diagonal

import (
	"github.com/euc-ai/xugo/library/registry"
)

var embeddedTangentFiberDiskDef = embeddedTangentFiberDiskDefThm{family.Define(registry.DefEntry{
	Name:  "embeddedTangentFiberDiskDef",
	Key:   "prop_70221898145c7f10",
	Const: "embedded_tangent_fiber_disk",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"A → " +
		"real → " +
		"set(num → real)",
	Dimensions: []string{"n", "N"},
	Reading: "This is the coordinate preimage of the actual tangent disk " +
		"at x. The Euclidean vector guard excludes arbitrary tails. Geometry " +
		"laws require an active chart; nonpositive radii give empty disks.",
	Deps: []registry.EntryLike{EmbeddedTangentDiskDef},
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀δ:real. " +
			"    embedded_tangent_fiber_disk⟨n, N⟩(T, 𝒜, i, c, x, δ) = " +
			"    {u:num → real | " +
			"        vec⟨n⟩(u) ∧ " +
			"        (x, tangent_from_chart⟨n⟩(T, 𝒜, c, x, u)) ∈ embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ)}",
	},
})}

var diagonalFiberMapDef = diagonalFiberMapDefThm{family.Define(registry.DefEntry{
	Name:  "diagonalFiberMapDef",
	Key:   "prop_eeb5fac92ec3473a",
	Const: "diagonal_fiber_map",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"((num → real) → A) → " +
		"prod(set(A), A → num → real) → " +
		"A → " +
		"(num → real) → " +
		"A",
	Dimensions: []string{"n", "N"},
	Reading: "The map reconstructs the tangent vector with coordinate u at x " +
		"and takes the second diagonal-map component. Its values away from normalized " +
		"coordinate vectors are not used by its geometric or integration laws.",
	Deps: []registry.EntryLike{diagonalMapDef},
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀r:((num → real) → A). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀u:(num → real). " +
			"    diagonal_fiber_map⟨n, N⟩(T, 𝒜, i, r, c, x)(u) = " +
			"    snd(diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r)((x, tangent_from_chart⟨n⟩(T, 𝒜, c, x, u))))",
	},
})}
