// Tangent disks measured by the embedding differential, and the retraction-based diagonal map.

package manifold_diagonal

import (
	"github.com/euc-ai/xugo/library/registry"
)

var EmbeddedTangentDiskDef = embeddedTangentDiskDefThm{family.Define(registry.DefEntry{
	Name:  "EmbeddedTangentDiskDef",
	Key:   "prop_fbc0e1ca084b0ae5",
	Const: "embedded_tangent_disk",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"real → " +
		"set(prod(A, prod(set(A), A → num → real) → num → real))",
	Dimensions: []string{"n", "N"},
	Reading: "The radius measures the Euclidean length of the image tangent " +
		"vector. The set includes the tangent-bundle carrier guard; arbitrary host " +
		"chart families are excluded. A nonpositive radius gives the empty disk.",
	Deps: []registry.EntryLike{},
	Equations: []string{
		"∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀i:(A → num → real). ∀δ:real. " +
			"    embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ) = " +
			"    {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"        p ∈ tangent_bundle⟨n⟩(T, 𝒜) ∧ " +
			"        ‖manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(fst(p), snd(p))‖_N < δ}",
	},
})}

var diagonalMapDef = diagonalMapDefThm{family.Define(registry.DefEntry{
	Name:  "diagonalMapDef",
	Key:   "prop_82b41f56aca102a5",
	Const: "diagonal_neighbourhood_map",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"((num → real) → A) → " +
		"prod(A, prod(set(A), A → num → real) → num → real) → " +
		"prod(A, A)",
	Dimensions: []string{"n", "N"},
	Reading: "The first projection is literally the tangent base point. The " +
		"second evaluates the supplied retraction at the ambient affine tangent step; " +
		"smoothness is claimed only where that step stays in the retraction domain.",
	Deps: []registry.EntryLike{},
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀r:((num → real) → A). " +
			"∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"    diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r)(p) = " +
			"    (fst(p), " +
			"        r(λj:num. " +
			"                i(fst(p), j) + " +
			"                manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(fst(p), snd(p))(j)))",
	},
})}

var diagonalHomotopyDef = diagonalHomotopyDefThm{family.Define(registry.DefEntry{
	Name:  "diagonalHomotopyDef",
	Key:   "prop_35ee2b7a2f1c87dc",
	Const: "diagonal_neighbourhood_homotopy",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"((num → real) → A) → " +
		"real → " +
		"prod(prod(A, A), num → real) → " +
		"A",
	Dimensions: []string{"n", "N"},
	Reading: "Pull a neighbourhood point back to its tangent-disk point, scale its ambient " +
		"tangent image by the time coordinate, and retract. The inverse_on value is specified only on " +
		"the disk map image; the homotopy laws also require all scaled ambient steps to remain in U.",
	Deps: []registry.EntryLike{EmbeddedTangentDiskDef, diagonalMapDef},
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀r:((num → real) → A). " +
			"∀δ:real. " +
			"∀z:prod(prod(A, A), num → real). " +
			"    diagonal_neighbourhood_homotopy⟨n, N⟩(T, 𝒜, i, r, δ)(z) = " +
			"    r(λj:num. " +
			"            i(fst(«inverse disk point»(fst(z))), j) + " +
			"            snd(z)(0) * " +
			"            manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(fst(«inverse disk point»(fst(z))), " +
			"                snd(«inverse disk point»(fst(z))))(j))",
	},
})}
