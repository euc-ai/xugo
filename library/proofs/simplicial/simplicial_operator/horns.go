// horns.go — horns as maps out of the standard horns. The Kan chapter
// states a horn as a compatible family of faces; the standard horn
// Λⁿ⁺¹ₖ is the sub-simplicial set of Δⁿ⁺¹ of the simplices missing some
// vertex other than k. A compatible family y gives a map out of Λⁿ⁺¹ₖ:
// a simplex θ missing the vertex v ≠ k factors through the coface at v,
// and is sent to the action of the factor on y(v); the choice of v does
// not matter exactly because the family is compatible. Every map out of
// the horn is of this form, read off at the faces, and a map extends to
// Δⁿ⁺¹ exactly when the family has a filler. So the Kan condition, the
// inner horn condition of a quasi-category and unique inner filling are
// each a condition on extending maps out of horns.

package simplicial_operator

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/nerve"
	"github.com/euc-ai/xugo/library/proofs/simplicial/quasi_category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplex_category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// hornFamilyMapDef — `horn_family_map(d, s, n, k, y)`: the map out of
// Λⁿ⁺¹ₖ that a family of faces y gives, a simplex missing the vertex v
// sent to the action of its factor through the coface at v on y(v).
var hornFamilyMapDef = hornFamilyMapDefThm{family.Define(registry.DefEntry{
	Name:  "hornFamilyMapDef",
	Key:   "prop_13a7c3232f515389",
	Const: "horn_family_map",
	Type: "(num → num → A → A) → " +
		"(num → num → A → A) → " +
		"num → " +
		"num → " +
		"(num → A) → " +
		"num → " +
		"(num → num) → " +
		"A",
	Equations: []string{
		"∀d s:(num → num → A → A). ∀n k:num. ∀y:(num → A). " +
			"    horn_family_map(d, s, n, k, y) = " +
			"    λm:num. " +
			"        normalize_on(simplex_horn_simplices(n + 1, k, m), " +
			"            junk, " +
			"            λθ:(num → num). εz:A. ∃v:num. " +
			"                v ≤ n + 1 ∧ " +
			"                v ≠ k ∧ " +
			"                (∀a:num. a ≤ m ⇒ θ(a) ≠ v) ∧ " +
			"                z = " +
			"                simplicial_operator(d, " +
			"                    s, " +
			"                    mk_morphism(m, " +
			"                        n, " +
			"                        normalize_on(0 .. m, 0, λa:num. COND(θ(a) < v, θ(a), θ(a) - 1))), " +
			"                    y(v)))",
	},
	Deps: []registry.EntryLike{SimplicialOperatorDef},
	Reading: "The value is chosen among the missed vertices; HornMapIffCompatibleFaces shows " +
		"it does not depend on the choice when y is compatible, and only then is the map simplicial.",
})}

// HornMapIffCompatibleFaces — the maps out of a standard horn are the
// compatible families of faces.
var HornMapIffCompatibleFaces = hornMapIffCompatibleFacesThm{family.Add(registry.ProofEntry{
	Name: "HornMapIffCompatibleFaces",
	Key:  "prop_9abcf68f6224fffe",
	Deps: []registry.EntryLike{
		hornFamilyMapDef,
		simplicial_set.FaceFamilyDef,
		simplicial_set.FacesCompatibleDef,
		kan_complex.HornFacesMember,
		simplicial_set.SimplexHornSimplicesDef,
		simplicial_set.SimplexHornSub,
		simplicial_set.SimplicialMapSetDef,
		simplex_category.SimplexFaceCoface,
		SimplicialOperatorCompose,
		SimplicialOperatorCoface,
		SimplicialMapIffOperatorNatural,
		StandardSimplexOperator,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀n k:num.",
		Hypotheses: []string{
			"k ≤ n + 1",
		},
		Conclusion: "(∀y:(num → A). " +
			"    face_family(n, horn_faces(n, k), y) ⇒ " +
			"    horn_family_map(X.d, X.s, n, k, y) ∈ simplicial_map_set(simplex_horn(n + 1, k), X) ∧ " +
			"    (∀i:num. " +
			"        i ∈ horn_faces(n, k) ⇒ " +
			"        horn_family_map(X.d, X.s, n, k, y, n, normalize_on(0 .. n, 0, coface(i))) = y(i))) ∧ " +
			"(∀F:(num → (num → num) → A). " +
			"    F ∈ simplicial_map_set(simplex_horn(n + 1, k), X) ⇒ " +
			"    faces_compatible(n, horn_faces(n, k), λi:num. F(n, normalize_on(0 .. n, 0, coface(i)))) ∧ " +
			"    F = horn_family_map(X.d, X.s, n, k, λi:num. F(n, normalize_on(0 .. n, 0, coface(i)))))",
	}),
		"a simplex missing two vertices v < w factors through the cofaces at both, and the two "+
			"values agree: the factors differ by the face identity at (v, w), which is the "+
			"compatibility of y at that pair (SimplicialOperatorCompose, "+
			"SimplicialOperatorCoface); the map then commutes with the operators of the horn, "+
			"precomposition (StandardSimplexOperator), and takes y(i) at the i-th face. Conversely "+
			"a map out of the horn commutes with the operators (SimplicialMapIffOperatorNatural), "+
			"so its values at the faces are compatible and it is determined by them"),
	Reading: "The well-definedness of the glued map, the one step that is " +
		"not a reading of definitions, is exactly the compatibility of the faces.",
})}

// HornExtensionIffFiller — the map out of the horn that a compatible
// family gives extends to the standard simplex exactly when the family
// has a filler.
var HornExtensionIffFiller = hornExtensionIffFillerThm{family.Add(registry.ProofEntry{
	Name: "HornExtensionIffFiller",
	Key:  "prop_12f98690a80bf8e6",
	Deps: []registry.EntryLike{
		HornMapIffCompatibleFaces,
		SimplexYoneda,
		simplicial_set.FacesFillerDef,
		kan_complex.HornFacesMember,
		simplicial_set.SimplexHornSimplicesDef,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"k ≤ n + 1",
			"face_family(n, horn_faces(n, k), y)",
		},
		Conclusion: "(∃G:(num → (num → num) → A). " +
			"    simplicial_map(standard_simplex(n + 1), X, G) ∧ " +
			"    (∀m:num. ∀θ:(num → num). " +
			"        θ ∈ simplex_horn_simplices(n + 1, k, m) ⇒ " +
			"        G(m, θ) = horn_family_map(X.d, X.s, n, k, y, m, θ))) ⇔ " +
			"∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x)",
	}),
		"a map from Δⁿ⁺¹ is named by an (n + 1)-simplex x (SimplexYoneda), and its values "+
			"at the faces of the identity are the faces of x; it extends the horn's map exactly "+
			"when those faces other than the k-th are the members of y, which is a filler"),
})}

// KanIffHornExtension — a simplicial set is a Kan complex exactly when
// every map out of a standard horn extends to the standard simplex.
var KanIffHornExtension = kanIffHornExtensionThm{family.Add(registry.ProofEntry{
	Name: "KanIffHornExtension",
	Key:  "prop_98a64ba09854d46b",
	Deps: []registry.EntryLike{
		kan_complex.KanComplex,
		HornMapIffCompatibleFaces,
		HornExtensionIffFiller,
	},
	Build: family.Card(
		"∀X:simplicial_ops(A). "+
			"    kan_complex(X) ⇔ "+
			"    simplicial_set(X) ∧ "+
			"    (∀n k:num. "+
			"        k ≤ n + 1 ⇒ "+
			"        ∀F:(num → (num → num) → A). "+
			"            simplicial_map(simplex_horn(n + 1, k), X, F) ⇒ "+
			"            ∃G:(num → (num → num) → A). "+
			"                simplicial_map(standard_simplex(n + 1), X, G) ∧ "+
			"                (∀m:num. ∀θ:(num → num). "+
			"                    θ ∈ simplex_horn_simplices(n + 1, k, m) ⇒ G(m, θ) = F(m, θ)))",
		"a map out of the horn, normalized, is the map of its compatible family of faces "+
			"(HornMapIffCompatibleFaces), and it extends exactly when the family has a filler "+
			"(HornExtensionIffFiller); the Kan condition asks a filler of every compatible family"),
})}

// QuasiIffInnerHornExtension — a simplicial set is a quasi-category
// exactly when every map out of an inner horn extends.
var QuasiIffInnerHornExtension = quasiIffInnerHornExtensionThm{family.Add(registry.ProofEntry{
	Name: "QuasiIffInnerHornExtension",
	Key:  "prop_448537d50b7fdf42",
	Deps: []registry.EntryLike{
		quasi_category.QuasiCategory,
		HornMapIffCompatibleFaces,
		HornExtensionIffFiller,
	},
	Build: family.Card(
		"∀X:simplicial_ops(A). "+
			"    quasi_category(X) ⇔ "+
			"    simplicial_set(X) ∧ "+
			"    (∀n k:num. "+
			"        0 < k ∧ k ≤ n ⇒ "+
			"        ∀F:(num → (num → num) → A). "+
			"            simplicial_map(simplex_horn(n + 1, k), X, F) ⇒ "+
			"            ∃G:(num → (num → num) → A). "+
			"                simplicial_map(standard_simplex(n + 1), X, G) ∧ "+
			"                (∀m:num. ∀θ:(num → num). "+
			"                    θ ∈ simplex_horn_simplices(n + 1, k, m) ⇒ G(m, θ) = F(m, θ)))",
		"KanIffHornExtension's argument at the inner horns, 0 < k ≤ n"),
})}

// InnerHornUniqueIffUniqueExtension — unique inner fillers are unique
// extensions of maps out of the inner horns.
var InnerHornUniqueIffUniqueExtension = innerHornUniqueIffUniqueExtensionThm{family.Add(registry.ProofEntry{
	Name: "InnerHornUniqueIffUniqueExtension",
	Key:  "prop_924faa20bfb94bd7",
	Deps: []registry.EntryLike{
		nerve.InnerHornUnique,
		HornMapIffCompatibleFaces,
		HornExtensionIffFiller,
		SimplexYoneda,
	},
	Build: family.Card(
		"∀X:simplicial_ops(A). "+
			"    inner_horn_unique(X) ⇔ "+
			"    simplicial_set(X) ∧ "+
			"    (∀n k:num. "+
			"        0 < k ∧ k ≤ n ⇒ "+
			"        ∀F:(num → (num → num) → A). "+
			"            simplicial_map(simplex_horn(n + 1, k), X, F) ⇒ "+
			"            ∃G:(num → (num → num) → A). "+
			"                simplicial_map(standard_simplex(n + 1), X, G) ∧ "+
			"                (∀m:num. ∀θ:(num → num). "+
			"                    θ ∈ simplex_horn_simplices(n + 1, k, m) ⇒ G(m, θ) = F(m, θ)) ∧ "+
			"                (∀G':(num → (num → num) → A). "+
			"                    simplicial_map(standard_simplex(n + 1), X, G') ∧ "+
			"                    (∀m:num. ∀θ:(num → num). "+
			"                        θ ∈ simplex_horn_simplices(n + 1, k, m) ⇒ G'(m, θ) = F(m, θ)) ⇒ "+
			"                    ∀m:num. ∀θ:(num → num). "+
			"                        θ ∈ standard_simplex_simplices(n + 1, m) ⇒ G'(m, θ) = G(m, θ)))",
		"two extensions are named by two fillers (SimplexYoneda), equal exactly "+
			"when the fillers are; the rest is QuasiIffInnerHornExtension's argument"),
})}
