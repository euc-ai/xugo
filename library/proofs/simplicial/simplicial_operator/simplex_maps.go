// simplex_maps.go — simplicial maps and the action of the monotone
// maps. A family of maps between simplicial sets commutes with every
// operator exactly when it commutes with the faces and the
// degeneracies. An n-simplex x names the map from the standard simplex
// Δⁿ that sends θ to the action of θ on x, and every map from Δⁿ is
// named by its value at the identity: the Yoneda argument at Δ.

package simplicial_operator

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplex_category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Simplicial maps commute with the operators
// ---------------------------------------------------------------------------

// SimplicialMapIffOperatorNatural — a family of maps is a simplicial map
// exactly when it commutes with the action of every monotone map.
var SimplicialMapIffOperatorNatural = simplicialMapIffOperatorNaturalThm{family.Add(registry.ProofEntry{
	Name: "SimplicialMapIffOperatorNatural",
	Key:  "prop_17e77844a3829d3f",
	Deps: []registry.EntryLike{
		simplicial_set.SimplicialMap,
		SimplicialOperatorDef,
		SimplicialOperatorCoface,
		SimplicialOperatorCodegeneracy,
		simplex_category.CanonicalFactorization,
	},
	Build: family.Card(Statement{
		Binders: "∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀F:(num → A → B).",
		Hypotheses: []string{
			"simplicial_set(X)",
			"simplicial_set(Y)",
		},
		Conclusion: "simplicial_map(X, Y, F) ⇔ " +
			"(∀n:num. ∀x:A. x ∈ X.simplices(n) ⇒ F(n, x) ∈ Y.simplices(n)) ∧ " +
			"(∀t:morphism_triple(num, num → num). ∀x:A. " +
			"    t ∈ category_morphisms(simplex_category) ∧ x ∈ X.simplices(t.target) ⇒ " +
			"    F(t.source, simplicial_operator(X.d, X.s, t, x)) = " +
			"    simplicial_operator(Y.d, Y.s, t, F(t.target, x)))",
	},
		"⇐: the faces and degeneracies are the actions of the generators. ⇒: an action "+
			"is a composite of faces and degeneracies through the two folds, past each of "+
			"which F moves; the folds stay within the simplices, where F's laws apply"),
	Reading: "X and Y may live on different types.",
})}

// ---------------------------------------------------------------------------
// The Yoneda reading of a simplex
// ---------------------------------------------------------------------------

// simplexYonedaMapDef — `simplex_yoneda_map(d, s, n, x)`: the map from
// the standard simplex Δⁿ that x names, θ sent to its action on x,
// normalized.
var simplexYonedaMapDef = simplexYonedaMapDefThm{family.Define(registry.DefEntry{
	Name:  "simplexYonedaMapDef",
	Key:   "prop_da9edef59eea263e",
	Const: "simplex_yoneda_map",
	Type:  "(num → num → A → A) → (num → num → A → A) → num → A → num → (num → num) → A",
	Equations: []string{
		"∀d s:(num → num → A → A). ∀n:num. ∀x:A. " +
			"    simplex_yoneda_map(d, s, n, x) = " +
			"    λm:num. " +
			"        normalize_on(standard_simplex_simplices(n, m), " +
			"            junk, " +
			"            λθ:(num → num). simplicial_operator(d, s, mk_morphism(m, n, θ), x))",
	},
	Deps: []registry.EntryLike{SimplicialOperatorDef},
})}

// SimplexYoneda — the n-simplices of X are the maps from Δⁿ to X: x
// names its map, and a map is named by its value at the identity.
var SimplexYoneda = simplexYonedaThm{family.Add(registry.ProofEntry{
	Name: "SimplexYoneda",
	Key:  "prop_d5efeaed56d7aea6",
	Deps: []registry.EntryLike{
		simplexYonedaMapDef,
		SimplicialMapIffOperatorNatural,
		StandardSimplexOperator,
		SimplicialOperatorIdentity,
		SimplicialOperatorCompose,
		simplicial_set.SimplicialMapSetDef,
	},
	Build: family.Card(
		simplicial_set.SimplicialSet.Statement(
			"∀n:num. "+
				"    (∀x:A. "+
				"        x ∈ X.simplices(n) ⇒ "+
				"        simplex_yoneda_map(X.d, X.s, n, x) ∈ simplicial_map_set(standard_simplex(n), X) ∧ "+
				"        simplex_yoneda_map(X.d, X.s, n, x, n, normalize_on(0 .. n, 0, λa:num. a)) = x) ∧ "+
				"    (∀F:(num → (num → num) → A). "+
				"        F ∈ simplicial_map_set(standard_simplex(n), X) ⇒ "+
				"        F = simplex_yoneda_map(X.d, X.s, n, F(n, normalize_on(0 .. n, 0, λa:num. a))))"),
		"the Yoneda argument in Δ, unfolded at X: a map from Δⁿ commutes with every "+
			"operator (SimplicialMapIffOperatorNatural), the operators of Δⁿ being "+
			"precomposition (StandardSimplexOperator), so it is determined by its value at the "+
			"identity; the map x names commutes with the operators by "+
			"SimplicialOperatorCompose and takes x at the identity (SimplicialOperatorIdentity)"),
})}
