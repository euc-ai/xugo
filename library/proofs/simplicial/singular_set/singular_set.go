// singular_set.go — the singular simplicial set: a simplicial set, whose
// simplicial identities are the cosimplicial identities of the standard
// simplices read through precomposition; a continuous map induces a
// simplicial map, functorially; the singular simplices of a subspace are
// those whose image lies in it, and the vertices are the points; and it is
// a Kan complex, a horn of singular simplices being filled through a
// retraction of the standard simplex onto its horn. Its homotopy groups
// are simplicial/homotopy_group's, and the first is the fundamental group.

package singular_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/homotopy_group"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/fundamental_group"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_simplex"
	"github.com/euc-ai/xugo/library/registry"
)

// SingularSimplicialSet — the singular simplices of a space form a
// simplicial set.
var SingularSimplicialSet = singularSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "SingularSimplicialSet",
	Key:  "prop_4fcaffe8ea0156a7",
	Reading: "Holds for any family T. In every identity the bounds put the inner coface or " +
		"codegeneracy inside the inner normalization's simplex — δⁱ carries Δⁿ into Δⁿ⁺¹ for i ≤ n + " +
		"1, σⁱ carries Δⁿ⁺¹ onto Δⁿ for i ≤ n — so both sides are the simplex after a cosimplicial " +
		"identity on the outer simplex, and junk off it. The face of a vertex is never read.",
	Deps: []registry.EntryLike{
		SingularSetDef,
		simplicial_set.SimplicialSet,
		continuous.NormalizeHomSetIff,
		continuous.Compose,
		euclidean_simplex.CofaceSimplex,
		euclidean_simplex.CofaceContinuous,
		euclidean_simplex.CodegeneracySimplex,
		euclidean_simplex.CodegeneracyContinuous,
		euclidean_simplex.CofaceCoface,
		euclidean_simplex.CodegeneracyCodegeneracy,
		euclidean_simplex.CodegeneracyCofaceBelow,
		euclidean_simplex.CodegeneracyCofaceIdentity,
		euclidean_simplex.CodegeneracyCofaceAbove,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Conclusion: "simplicial_set(singular_set(T))",
	},
		"a face or a degeneracy of a singular simplex is the simplex after a continuous map "+
			"of standard simplices carrying one into the other (CofaceSimplex, CofaceContinuous, "+
			"CodegeneracySimplex, CodegeneracyContinuous), normalized, so a singular simplex "+
			"(Compose, NormalizeHomSetIff); each simplicial identity is a cosimplicial identity "+
			"precomposed, the normalization inside not seen on the smaller simplex"),
})}

// SingularMapSimplicial — a continuous map induces a simplicial map of the
// singular simplicial sets.
var SingularMapSimplicial = singularMapSimplicialThm{family.Add(registry.ProofEntry{
	Name: "SingularMapSimplicial",
	Key:  "prop_7f60ddf8ba6747c8",
	Reading: "Continuity of f is read only to make f ∘ σ a singular " +
		"simplex; faces and degeneracies commute with singular_map for any f.",
	Deps: []registry.EntryLike{
		SingularSimplicialSet,
		SingularMapDef,
		simplicial_set.SimplicialMap,
		continuous.NormalizeHomSetIff,
		continuous.Compose,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"continuous_map(T, S, f)",
		},
		Conclusion: "simplicial_map(singular_set(T), singular_set(S), singular_map(f))",
	},
		"f after a singular simplex, normalized, is a singular simplex (Compose, NormalizeHomSetIff), "+
			"and postcomposing with f commutes with precomposing with a coface or a codegeneracy"),
})}

// SingularMapIdentity — the identity map induces the identity on singular
// simplices.
var SingularMapIdentity = singularMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "SingularMapIdentity",
	Key:  "prop_59a1852f26b87f5",
	Reading: "σ a singular simplex is load-bearing: it is already normalized on Δⁿ; " +
		"for an arbitrary σ the left side is σ normalized, which differs from σ off Δⁿ.",
	Deps: []registry.EntryLike{SingularMapDef, SingularSimplicesDef, continuous.ContinuousHomSetDef},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀n:num. ∀σ:((num → real) → A).",
		Hypotheses: []string{
			"σ ∈ singular_simplices(T, n)",
		},
		Conclusion: "singular_map(λx:A. x, n, σ) = σ",
	},
		"σ is normalized off the simplex (ContinuousHomSetDef), so normalizing it again changes nothing"),
})}

// SingularMapCompose — a composite of maps induces the composite of the
// induced maps.
var SingularMapCompose = singularMapComposeThm{family.Add(registry.ProofEntry{
	Name:    "SingularMapCompose",
	Key:     "prop_a6c6dc5176ca4e0f",
	Reading: "No hypothesis: both sides are g(f(σ(t))) on Δⁿ and junk off it, for every σ.",
	Deps:    []registry.EntryLike{SingularMapDef},
	Build: family.Card(Statement{
		Binders:    "∀f:(A → B). ∀g:(B → C). ∀n:num. ∀σ:((num → real) → A).",
		Conclusion: "singular_map(g ∘ f, n, σ) = singular_map(g, n, singular_map(f, n, σ))",
	},
		"both sides are g(f(σ(t))) on the simplex and junk off it"),
})}

// SubspaceSingularSimplices — the singular simplices of a subspace are the
// singular simplices of the space whose image lies in it.
var SubspaceSingularSimplices = subspaceSingularSimplicesThm{family.Add(registry.ProofEntry{
	Name: "SubspaceSingularSimplices",
	Key:  "prop_dcfe433bc852f530",
	Reading: "u ⊆ ⋃T makes the subspace's points exactly u; once " +
		"the image lies in u, the preimage of w ∩ u is the preimage of w.",
	Deps: []registry.EntryLike{
		SingularSimplicesDef,
		continuous.ContinuousHomSetDef,
		continuous.IntoSubtopology,
		continuous.FromSubtopology,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀u:set(A). ∀n:num.",
		Hypotheses: []string{
			"u ⊆ ⋃T",
		},
		Conclusion: "singular_simplices(subtopology(T, u), n) = " +
			"{σ:((num → real) → A) | σ ∈ singular_simplices(T, n) ∧ image(σ, euclidean_simplex(n)) ⊆ u}",
	},
		"a map is continuous into the subspace on u exactly when it is continuous "+
			"into the space with its values in u (IntoSubtopology, FromSubtopology), "+
			"the points of the standard simplex as a subspace of ℝⁿ⁺¹ being the "+
			"simplex itself; the normalization does not read the topology of the target"),
})}

// SingularVertex — the singular 0-simplices are the constant maps at the
// points of the space.
var SingularVertex = singularVertexThm{family.Add(registry.ProofEntry{
	Name: "SingularVertex",
	Key:  "prop_67e1c26147c02f59",
	Reading: "Δ⁰ = {e₀}, whose subspace topology is {∅, {e₀}}, so a map from it is continuous " +
		"exactly when its value is a point of the space. For the empty space both sides are false.",
	Deps: []registry.EntryLike{
		SingularSimplicesDef,
		continuous.ContinuousHomSetDef,
		continuous.Constant,
		euclidean_simplex.EuclideanSimplexDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀σ:((num → real) → A).",
		Conclusion: "σ ∈ singular_simplices(T, 0) ⇔ " +
			"∃x:A. x ∈ ⋃T ∧ σ = normalize_on(euclidean_simplex(0), junk, λt:(num → real). x)",
	},
		"the standard 0-simplex is one point, so a normalized map on it is the constant at its "+
			"value there, normalized; a constant map at a point of the space is continuous (Constant)"),
})}

// SingularKan — the singular simplicial set of a space is a Kan complex.
var SingularKan = singularKanThm{family.Add(registry.ProofEntry{
	Name: "SingularKan",
	Key:  "prop_2fbfc7b8366582de",
	Reading: "No axiom on T: the pasting is on the horn of Δⁿ⁺¹. For " +
		"the empty space no horn exists, every horn having at least one face.",
	Deps: []registry.EntryLike{
		SingularSimplicialSet,
		kan_complex.KanComplex,
		euclidean_simplex.HornRetraction,
		euclidean_simplex.CofaceImage,
		euclidean_simplex.CodegeneracyCofaceIdentity,
		euclidean_simplex.CodegeneracyContinuous,
		continuous.FiniteClosedPasting,
		continuous.RetractOfDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀T:set(set(A)).",
		Conclusion: "kan_complex(singular_set(T))",
	},
		"a horn of singular n-simplices yᵢ, i ≠ k, defines one map on the horn of Δⁿ⁺¹: on "+
			"the face where coordinate i vanishes, the image of the i-th coface (CofaceImage), it "+
			"is yᵢ after deleting coordinate i, the codegeneracy σⁱ for i ≤ n and σⁿ for the last "+
			"face (CodegeneracyCofaceIdentity, CodegeneracyContinuous); the horn condition makes "+
			"the pieces agree where faces meet, and the faces are finitely many closed sets, so "+
			"the map is continuous (FiniteClosedPasting). The filler is that map after the "+
			"retraction of Δⁿ⁺¹ onto the horn (HornRetraction), normalized; its i-th face is yᵢ"),
})}

// FundamentalGroupSingular — the fundamental group of a space at a point is
// isomorphic to the first homotopy group of its singular simplicial set at
// the vertex of the point.
var FundamentalGroupSingular = fundamentalGroupSingularThm{family.Add(registry.ProofEntry{
	Name: "FundamentalGroupSingular",
	Key:  "prop_d9a1422d84415f9a",
	Reading: "x ∈ ⋃T makes «vertex» a 0-simplex and both records groups. The two products agree in " +
		"order: a 2-simplex with faces x at 2 and y at 0 has face 1 homotopic to the join of x and y.",
	Deps: []registry.EntryLike{
		SingularKan,
		SingularVertex,
		homotopy_group.GroupOn,
		homotopy_group.MulClass,
		homotopy_group.ClassEqIff,
		fundamental_group.FundamentalGroupOn,
		fundamental_group.FundamentalGroupMember,
		fundamental_group.PathClassEq,
		fundamental_group.PathClassJoinClass,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀x:A.",
		Hypotheses: []string{
			"x ∈ ⋃T",
		},
		Conclusion: "∃φ:(set(real → A) → set((num → real) → A)). " +
			"    group_isomorphism(fundamental_group(T, x), " +
			"        mk_group(simplicial_homotopy_mul(singular_set(T), «vertex», 1), " +
			"            simplicial_homotopy_unit(singular_set(T), «vertex», 1), " +
			"            simplicial_homotopy_inv(singular_set(T), «vertex», 1), " +
			"            simplicial_homotopy_group(singular_set(T), «vertex», 1)), " +
			"        φ)",
		Abbrev: Abbrev{
			{Name: "vertex", Text: "normalize_on(euclidean_simplex(0), junk, λt:(num → real). x)"},
		},
	},
		"a loop g at x gives the singular 1-simplex t ↦ g(t₁) on Δ¹, an edge from the vertex of x to "+
			"itself, and every such edge is one, so loops and spheres correspond; a homotopy of loops "+
			"with the ends held, cut along the diagonal of the square, gives a 2-simplex witnessing the "+
			"simplicial homotopy, and a 2-simplex gives a homotopy through the triangle; a product filler "+
			"of two edges is a 2-simplex whose third edge is homotopic to their join, so φ, the class of "+
			"the loop to the class of its edge, is a homomorphism (MulClass), and it is one to one and "+
			"onto by the two directions of the correspondence of homotopies (ClassEqIff, PathClassEq)"),
})}
