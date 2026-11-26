// simplicial_operator.go — the action of a monotone map on the
// simplices of a simplicial set. A morphism θ: [m] → [n] of Δ factors
// canonically into cofaces after codegeneracies (simplex_category), and
// θ acts on an n-simplex by the faces at the values it misses, the
// largest first, and then the degeneracies at the positions it repeats,
// the smallest first: two folds over the canonical index lists, each
// carrying the dimension beside the simplex. The difficult law is that
// the action is contravariantly functorial; it is split into the two
// laws for a canonical form multiplied on the right by one generator,
// whose proofs use the simplicial identities of (d, s), and the general
// law follows by induction along the canonical factorization.

package simplicial_operator

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplex_category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// SimplicialOperatorDef — `simplicial_operator(d, s, t, x)`: the
// faces at coface_indices(t), the largest first, then the degeneracies
// at codegeneracy_indices(t), the smallest first, applied to x from the
// dimension t.target.
var SimplicialOperatorDef = simplicialOperatorDefThm{family.Define(registry.DefEntry{
	Name:  "SimplicialOperatorDef",
	Key:   "prop_21f1504f1d22874d",
	Const: "simplicial_operator",
	Type:  "(num → num → A → A) → (num → num → A → A) → morphism_triple(num, num → num) → A → A",
	Equations: []string{
		"∀d s:(num → num → A → A). ∀t:morphism_triple(num, num → num). ∀x:A. " +
			"    simplicial_operator(d, s, t, x) = " +
			"    snd(list_fold(λj:num. λp:prod(num, A). (fst(p) + 1, s(fst(p), j, snd(p))), " +
			"            list_reverse(codegeneracy_indices(t)), " +
			"            list_fold(λi:num. λp:prod(num, A). (fst(p) - 1, d(fst(p), i, snd(p))), " +
			"                coface_indices(t), " +
			"                (t.target, x))))",
	},
	Reading: "The fold over the cofaces applies the head of the ascending list last, " +
		"so the largest missed value acts first, at the dimension t.target; the degeneracies " +
		"are folded over the reversed list, so the smallest repeated position acts first.",
})}

// SimplicialOperatorIn — the action of θ: [m] → [n] carries an
// n-simplex to an m-simplex.
var SimplicialOperatorIn = simplicialOperatorInThm{family.Add(registry.ProofEntry{
	Name: "SimplicialOperatorIn",
	Key:  "prop_a95ed55c901234e7",
	Deps: []registry.EntryLike{
		SimplicialOperatorDef,
		simplex_category.CofaceIndicesDef,
		simplex_category.CodegeneracyIndicesDef,
		simplicial_set.FaceIn,
		simplicial_set.DegeneracyIn,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀t:morphism_triple(num, num → num). ∀x:A.",
		Hypotheses: []string{
			"t ∈ category_morphisms(simplex_category)",
			"x ∈ X.simplices(t.target)",
		},
		Conclusion: "simplicial_operator(X.d, X.s, t, x) ∈ X.simplices(t.source)",
	}),
		"each face is taken at an index at most the current dimension, the missed values being "+
			"distinct and at most t.target, and each degeneracy at an index at most the current dimension, "+
			"the repeats being distinct and below t.source; the dimension falls by the number of missed "+
			"values and rises by the number of repeats, ending at t.source (FaceIn, DegeneracyIn)"),
})}

// SimplicialOperatorCoface — a coface acts as the face.
var SimplicialOperatorCoface = simplicialOperatorCofaceThm{family.Add(registry.ProofEntry{
	Name: "SimplicialOperatorCoface",
	Key:  "prop_bac8e668211db576",
	Deps: []registry.EntryLike{
		SimplicialOperatorDef,
		simplex_category.CofaceMapDef,
		simplex_category.CofaceIndicesDef,
		simplex_category.CodegeneracyIndicesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀d s:(num → num → A → A). ∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"i ≤ n + 1",
		},
		Conclusion: "simplicial_operator(d, s, coface_map(n, i), x) = d(n + 1, i, x)",
	},
		"δⁱ misses exactly i and repeats nothing, so the folds apply the one face d(n + 1, i)"),
})}

// SimplicialOperatorCodegeneracy — a codegeneracy acts as the
// degeneracy.
var SimplicialOperatorCodegeneracy = simplicialOperatorCodegeneracyThm{family.Add(registry.ProofEntry{
	Name: "SimplicialOperatorCodegeneracy",
	Key:  "prop_53b7be5f06ea5653",
	Deps: []registry.EntryLike{
		SimplicialOperatorDef,
		simplex_category.CodegeneracyMapDef,
		simplex_category.CofaceIndicesDef,
		simplex_category.CodegeneracyIndicesDef,
	},
	Build: family.Card(Statement{
		Binders: "∀d s:(num → num → A → A). ∀n j:num. ∀x:A.",
		Hypotheses: []string{
			"j ≤ n",
		},
		Conclusion: "simplicial_operator(d, s, codegeneracy_map(n, j), x) = s(n, j, x)",
	},
		"σʲ misses nothing, being onto [n] for j ≤ n, and repeats "+
			"exactly at j, so the folds apply the one degeneracy s(n, j)"),
})}

// SimplicialOperatorIdentity — the identity acts as the identity.
var SimplicialOperatorIdentity = simplicialOperatorIdentityThm{family.Add(registry.ProofEntry{
	Name: "SimplicialOperatorIdentity",
	Key:  "prop_3ce0d9356b6cda50",
	Deps: []registry.EntryLike{
		SimplicialOperatorDef,
		simplex_category.SimplexCategoryDef,
		category.CategoryFromHomDef,
		simplex_category.CofaceIndicesDef,
		simplex_category.CodegeneracyIndicesDef,
	},
	Build: family.Card(
		"∀d s:(num → num → A → A). ∀n:num. ∀x:A. "+
			"    simplicial_operator(d, s, category_identity(simplex_category, n), x) = x",
		"the identity misses nothing and repeats nothing, so both "+
			"lists are empty and both folds return their argument"),
})}

// OperatorRightCoface — composing a monotone map on the right with a
// coface acts as the face after the map's action.
var OperatorRightCoface = operatorRightCofaceThm{family.Add(registry.ProofEntry{
	Name: "OperatorRightCoface",
	Key:  "prop_ccc015be135df047",
	Deps: []registry.EntryLike{
		SimplicialOperatorDef,
		simplex_category.CofaceIndicesDef,
		simplex_category.CodegeneracyIndicesDef,
		simplex_category.CofaceMapDef,
		simplex_category.CanonicalFactorization,
		simplex_category.FactorizationUnique,
		simplicial_set.FaceFace,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_set.FaceDegeneracyAbove,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀m i:num. ∀t:morphism_triple(num, num → num). ∀x:A.",
		Hypotheses: []string{
			"t ∈ category_morphisms(simplex_category)",
			"t.source = m + 1",
			"i ≤ m + 1",
			"x ∈ X.simplices(t.target)",
		},
		Conclusion: "simplicial_operator(X.d, " +
			"    X.s, " +
			"    category_compose(simplex_category, t, coface_map(m, i)), " +
			"    x) = " +
			"X.d(m + 1, i, simplicial_operator(X.d, X.s, t, x))",
	}),
		"the canonical lists of θ ∘ δⁱ are those of θ updated: if i lies in a run of "+
			"repeats the run shortens and one codegeneracy disappears, cancelled by d_i s_j "+
			"= 1; otherwise a new value is missed and its coface is inserted in order. In "+
			"either case the face d_i is moved past the degeneracies by the face–degeneracy "+
			"identities and into place among the faces by the face identity, induction on "+
			"the lengths of the two lists; FactorizationUnique identifies the updated lists"),
	Reading: "This and OperatorRightCodegeneracy are the two laws the general composition law is " +
		"built from; they are where the simplicial identities of (d, s) enter, the rest being Δ alone.",
})}

// OperatorRightCodegeneracy — composing on the right with a
// codegeneracy acts as the degeneracy after the map's action.
var OperatorRightCodegeneracy = operatorRightCodegeneracyThm{family.Add(registry.ProofEntry{
	Name: "OperatorRightCodegeneracy",
	Key:  "prop_83e05a5bce1ca787",
	Deps: []registry.EntryLike{
		SimplicialOperatorDef,
		simplex_category.CofaceIndicesDef,
		simplex_category.CodegeneracyIndicesDef,
		simplex_category.CodegeneracyMapDef,
		simplex_category.CanonicalFactorization,
		simplex_category.FactorizationUnique,
		simplicial_set.DegeneracyDegeneracy,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyAbove,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀m j:num. ∀t:morphism_triple(num, num → num). ∀x:A.",
		Hypotheses: []string{
			"t ∈ category_morphisms(simplex_category)",
			"t.source = m",
			"j ≤ m",
			"x ∈ X.simplices(t.target)",
		},
		Conclusion: "simplicial_operator(X.d, " +
			"    X.s, " +
			"    category_compose(simplex_category, t, codegeneracy_map(m, j)), " +
			"    x) = " +
			"X.s(m, j, simplicial_operator(X.d, X.s, t, x))",
	}),
		"θ ∘ σʲ misses what θ misses and repeats at j and at the repeats of θ shifted past j; "+
			"the degeneracy s_j is moved into place among the degeneracies by the degeneracy "+
			"identity, induction on the list of repeats, and FactorizationUnique identifies the lists"),
})}

// SimplicialOperatorCompose — the action is contravariantly
// functorial.
var SimplicialOperatorCompose = simplicialOperatorComposeThm{family.Add(registry.ProofEntry{
	Name: "SimplicialOperatorCompose",
	Key:  "prop_b964f0ea69277438",
	Deps: []registry.EntryLike{
		OperatorRightCoface,
		OperatorRightCodegeneracy,
		simplex_category.CanonicalFactorization,
		simplex_category.CofaceMorphism,
		simplex_category.CodegeneracyMorphism,
		SimplicialOperatorIdentity,
		category.Assoc,
		simplex_category.SimplexCategory,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀t u:morphism_triple(num, num → num). ∀x:A.",
		Hypotheses: []string{
			"t ∈ category_morphisms(simplex_category)",
			"u ∈ category_morphisms(simplex_category)",
			"t.target = u.source",
			"x ∈ X.simplices(u.target)",
		},
		Conclusion: "simplicial_operator(X.d, X.s, category_compose(simplex_category, u, t), x) = " +
			"simplicial_operator(X.d, X.s, t, simplicial_operator(X.d, X.s, u, x))",
	}),
		"induction along the canonical factorization of t, a composite of "+
			"generators (CanonicalFactorization): at the identity both sides are the "+
			"action of u (SimplicialOperatorIdentity); for t = t′ ∘ g with g a "+
			"coface or a codegeneracy, associativity in Δ and OperatorRightCoface or "+
			"OperatorRightCodegeneracy at u ∘ t′ and at t′ move g out on both sides"),
	Reading: "The canonical factorization alone equates monotone maps; that their actions " +
		"agree on an arbitrary simplicial set is the content of the two right-multiplication laws.",
})}

// StandardSimplexOperator — on the standard simplex the action is
// precomposition.
var StandardSimplexOperator = standardSimplexOperatorThm{family.Add(registry.ProofEntry{
	Name: "StandardSimplexOperator",
	Key:  "prop_e113df5e7615300f",
	Deps: []registry.EntryLike{
		SimplicialOperatorDef,
		simplex_category.SimplexFaceCoface,
		simplex_category.SimplexDegeneracyCodegeneracy,
		simplex_category.CanonicalFactorization,
		SimplicialOperatorIn,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀t:morphism_triple(num, num → num). ∀f:(num → num).",
		Hypotheses: []string{
			"t ∈ category_morphisms(simplex_category)",
			"f ∈ standard_simplex_simplices(n, t.target)",
		},
		Conclusion: "simplicial_operator(λm:num. simplex_face, λm:num. simplex_degeneracy, t, f) = " +
			"normalize_on(0 .. t.source, 0, f ∘ t.map)",
	},
		"each face and degeneracy of the standard simplex is precomposition with a "+
			"coface or a codegeneracy (SimplexFaceCoface, SimplexDegeneracyCodegeneracy), "+
			"so the action is precomposition with the canonical composite, which is t.map "+
			"on 0 .. t.source (CanonicalFactorization); past t.source both sides are 0, "+
			"the left side lying in standard_simplex(n, t.source) (SimplicialOperatorIn)"),
})}
