// maps_into.go — simplicial maps into a nerve. A map from a simplicial
// set X into the nerve of a category C is decided in low dimensions: a
// map of vertices to objects and of edges to morphisms, keeping the ends
// and the degenerate edges and sending every 2-simplex to a commuting
// triangle, extends to exactly one simplicial map, an n-simplex sent to
// the chain of its spine edges. At X the nerve of another category, the
// two conditions are the functor laws, so the nerve is full and
// faithful: the functors from C to D are the simplicial maps between
// their nerves, through nerve_map, the map of morphisms applied
// termwise.

package nerve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// NerveMapDef — `nerve_map(C, F)`: the map of nerves a functor induces,
// its map of morphisms applied termwise, normalized off each set of
// chains.
var NerveMapDef = nerveMapDefThm{family.Define(registry.DefEntry{
	Name:  "NerveMapDef",
	Key:   "prop_fd666e7401a09df2",
	Const: "nerve_map",
	Type:  "category_ops(A, M) → functor_ops(A, M, B, N) → num → (num → M) → num → N",
	Equations: []string{
		"∀C:category_ops(A, M). ∀F:functor_ops(A, M, B, N). " +
			"    nerve_map(C, F) = " +
			"    λn:num. normalize_on(nerve_simplices(C, n), junk, λf:(num → M). λj:num. F.map(f(j)))",
	},
	Deps: []registry.EntryLike{NerveSimplicesDef},
})}

// NerveMapCriterion — a map of vertices and edges keeping the ends and
// the degenerate edges and sending 2-simplices to commuting triangles
// extends to exactly one simplicial map into the nerve.
var NerveMapCriterion = nerveMapCriterionThm{family.Add(registry.ProofEntry{
	Name: "NerveMapCriterion",
	Key:  "prop_d052c3560ed10fcc",
	Deps: []registry.EntryLike{
		simplicial_set.SpineMapDef,
		simplicial_set.SpineIn,
		simplicial_set.SpineEnds,
		simplicial_set.FaceSpineBelow,
		simplicial_set.FaceSpineAbove,
		simplicial_set.SimplicialMap,
		NerveSimplicesDef,
		NerveFaceDef,
		NerveDegeneracyDef,
		NerveSimplicialSet,
		NerveSpine,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀C:category_ops(B, N). ∀φ₀:(A → B). ∀φ₁:(A → N).",
		Hypotheses: []string{
			"category(C)",
			"∀v:A. v ∈ X.simplices(0) ⇒ φ₀(v) ∈ C.objects",
			"∀e:A. e ∈ X.simplices(1) ⇒ φ₁(e) ∈ category_hom(C, φ₀(X.d(1, 1, e)), φ₀(X.d(1, 0, e)))",
			"∀v:A. v ∈ X.simplices(0) ⇒ φ₁(X.s(0, 0, v)) = C.identity(φ₀(v))",
			"∀w:A. w ∈ X.simplices(2) ⇒ φ₁(X.d(2, 1, w)) = C.compose(φ₁(X.d(2, 0, w)), φ₁(X.d(2, 2, w)))",
		},
		Conclusion: "simplicial_map(X, nerve(C), λn:num. λx:A. λj:num. φ₁(spine_map(n, x, j))) ∧ " +
			"(∀F:(num → A → num → N). " +
			"    simplicial_map(X, nerve(C), F) ∧ (∀e:A. e ∈ X.simplices(1) ⇒ F(1, e, 0) = φ₁(e)) ⇒ " +
			"    ∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ F(n, x) = λj:num. φ₁(spine_map(n, x, j)))",
	}),
		"existence: the spine edges of a simplex are composable edges (SpineIn, SpineEnds), so "+
			"their images form a chain, padded by the identity at the image of the last vertex; a face "+
			"keeps the spine edges away from the deleted vertex (FaceSpineBelow, FaceSpineAbove) and "+
			"at an inner one replaces two by the middle face of the 2-simplex on three consecutive "+
			"vertices, whose image is their composite; a degeneracy inserts a degenerate edge, sent to "+
			"an identity. Uniqueness: a simplicial map commutes with the iterated faces, so the j-th "+
			"term of F(n, x) is read off the edge F carries the j-th spine edge to (NerveSpine)"),
	Reading: "The objects map φ₀ enters only through the ends and the " +
		"identities; the simplices of X above dimension 2 are decided by their spines.",
})}

// NerveFullyFaithful — the functors between two categories are the
// simplicial maps between their nerves.
var NerveFullyFaithful = nerveFullyFaithfulThm{family.Add(registry.ProofEntry{
	Name: "NerveFullyFaithful",
	Key:  "prop_9a0ef49517e5f173",
	Deps: []registry.EntryLike{
		NerveMapDef,
		NerveMapCriterion,
		NerveFunctor,
		NerveVertex,
		NerveEdge,
		category.FunctorDef,
		category.FunctorSetDef,
		simplicial_set.SimplicialMapSetDef,
	},
	Build: family.Card(Statement{
		Binders: "∀C:category_ops(A, M). ∀D:category_ops(B, N).",
		Hypotheses: []string{
			"category(C)",
			"category(D)",
		},
		Conclusion: "injective_on(functor_set(C, D), nerve_map(C)) ∧ " +
			"image(nerve_map(C), functor_set(C, D)) = simplicial_map_set(nerve(C), nerve(D))",
	},
		"a functor induces a simplicial map (NerveFunctor), normalized by construction; it is "+
			"read back on edges and on the identity chains at the vertices (NerveEdge, "+
			"NerveVertex), so the map is one-to-one on the normalized functors; a simplicial map "+
			"between nerves satisfies NerveMapCriterion's conditions at its values on edges, which "+
			"are the functor laws read on chains of length 1 and 2, so it is the map of a functor"),
})}
