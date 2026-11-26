// generators.go — the generators of Δ. The coface
// δⁱ: [n] → [n + 1] skips the value i, the codegeneracy σʲ: [n + 1] → [n]
// repeats the value j; as maps of numbers they are the coface and the
// codegeneracy, and as morphisms of Δ they are those maps normalized
// and framed by their ends. The standard simplex acts by precomposition:
// its i-th face is precomposition with the coface and its j-th
// degeneracy with the codegeneracy. The ordered set [n] is a category of
// its own, and the standard simplex Δⁿ is its nerve.

package simplex_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/category/preorder_category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/nerve"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The generators
// ---------------------------------------------------------------------------

// CofaceDef — `coface(i)`: the map of numbers skipping the value i.
var CofaceDef = cofaceDefThm{family.Define(registry.DefEntry{
	Name:      "CofaceDef",
	Key:       "prop_73f336912c21b330",
	Const:     "coface",
	Type:      "num → num → num",
	Equations: []string{"∀i:num. coface(i) = λk:num. COND(k < i, k, k + 1)"},
})}

// CodegeneracyDef — `codegeneracy(j)`: the map of numbers repeating the
// value j.
var CodegeneracyDef = codegeneracyDefThm{family.Define(registry.DefEntry{
	Name:      "CodegeneracyDef",
	Key:       "prop_348d69132c63d5f3",
	Const:     "codegeneracy",
	Type:      "num → num → num",
	Equations: []string{"∀j:num. codegeneracy(j) = λk:num. COND(k ≤ j, k, k - 1)"},
})}

// CofaceMapDef — `coface_map(n, i)`: δⁱ from [n] to [n + 1], normalized
// with 0 past n.
var CofaceMapDef = cofaceMapDefThm{family.Define(registry.DefEntry{
	Name:  "CofaceMapDef",
	Key:   "prop_d2ed0186eea553ec",
	Const: "coface_map",
	Type:  "num → num → morphism_triple(num, num → num)",
	Equations: []string{
		"∀n i:num. coface_map(n, i) = mk_morphism(n, n + 1, normalize_on(0 .. n, 0, coface(i)))",
	},
	Deps: []registry.EntryLike{CofaceDef},
})}

// CodegeneracyMapDef — `codegeneracy_map(n, j)`: σʲ from [n + 1] to [n],
// normalized with 0 past n + 1.
var CodegeneracyMapDef = codegeneracyMapDefThm{family.Define(registry.DefEntry{
	Name:  "CodegeneracyMapDef",
	Key:   "prop_8c85f29028002ff0",
	Const: "codegeneracy_map",
	Type:  "num → num → morphism_triple(num, num → num)",
	Equations: []string{
		"∀n j:num. " +
			"    codegeneracy_map(n, j) = mk_morphism(n + 1, n, normalize_on(0 .. n + 1, 0, codegeneracy(j)))",
	},
	Deps: []registry.EntryLike{CodegeneracyDef},
})}

// SimplexFaceCoface — the faces of the standard simplex are
// precomposition with the cofaces.
var SimplexFaceCoface = simplexFaceCofaceThm{family.Add(registry.ProofEntry{
	Name: "SimplexFaceCoface",
	Key:  "prop_952e4dd0b024b2b6",
	Deps: []registry.EntryLike{CofaceDef, simplicial_set.SimplexFaceDef},
	Build: family.Card("∀i:num. ∀f:(num → num). simplex_face(i, f) = f ∘ coface(i)",
		"extensionality at k: both sides are f(k) below i and f(k + 1) from i on"),
})}

// SimplexDegeneracyCodegeneracy — the degeneracies of the standard
// simplex are precomposition with the codegeneracies.
var SimplexDegeneracyCodegeneracy = simplexDegeneracyCodegeneracyThm{family.Add(registry.ProofEntry{
	Name: "SimplexDegeneracyCodegeneracy",
	Key:  "prop_1923c7000b4b0f37",
	Deps: []registry.EntryLike{CodegeneracyDef, simplicial_set.SimplexDegeneracyDef},
	Build: family.Card("∀j:num. ∀f:(num → num). simplex_degeneracy(j, f) = f ∘ codegeneracy(j)",
		"extensionality at k: both sides are f(k) up to j and f(k − 1) past it"),
})}

// CofaceMorphism — the cofaces are morphisms of Δ.
var CofaceMorphism = cofaceMorphismThm{family.Add(registry.ProofEntry{
	Name: "CofaceMorphism",
	Key:  "prop_9027a57d43a15d82",
	Deps: []registry.EntryLike{
		CofaceMapDef,
		SimplexCategoryDef,
		category.CategoryFromHomDef,
		simplicial_set.InStandardSimplex,
	},
	Build: family.Card(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i ≤ n + 1",
		},
		Conclusion: "coface_map(n, i) ∈ category_morphisms(simplex_category)",
	},
		"the normalized coface is monotone on 0 .. n, takes values at most "+
			"n + 1, and is 0 past n, so it lies in standard_simplex(n + 1, n)"),
})}

// CodegeneracyMorphism — the codegeneracies are morphisms of Δ.
var CodegeneracyMorphism = codegeneracyMorphismThm{family.Add(registry.ProofEntry{
	Name: "CodegeneracyMorphism",
	Key:  "prop_8805319115b03063",
	Deps: []registry.EntryLike{
		CodegeneracyMapDef,
		SimplexCategoryDef,
		category.CategoryFromHomDef,
		simplicial_set.InStandardSimplex,
	},
	Build: family.Card(Statement{
		Binders: "∀n j:num.",
		Hypotheses: []string{
			"j ≤ n",
		},
		Conclusion: "codegeneracy_map(n, j) ∈ category_morphisms(simplex_category)",
	},
		"the normalized codegeneracy is monotone on 0 .. n + 1 and takes values at "+
			"most n, since j ≤ n makes the value at n + 1 equal n; it is 0 past n + 1"),
	Reading: "j ≤ n is load-bearing: at j = n + 1 the " +
		"codegeneracy leaves n + 1 where it is, outside [n].",
})}

// ---------------------------------------------------------------------------
// The ordered set [n], and the standard simplex as its nerve
// ---------------------------------------------------------------------------

// OrdinalCategoryDef — `ordinal_category(n)`: the numbers from 0 to n
// ordered by ≤, as a category.
var OrdinalCategoryDef = ordinalCategoryDefThm{family.Define(registry.DefEntry{
	Name:  "OrdinalCategoryDef",
	Key:   "prop_183254ab70618046",
	Const: "ordinal_category",
	Type:  "num → category_ops(num, morphism_triple(num, bool))",
	Equations: []string{
		"∀n:num. ordinal_category(n) = preorder_category(λi:num. λj:num. i ≤ j, 0 .. n)",
	},
})}

// StandardSimplexNerve — the standard simplex Δⁿ is the nerve of the
// ordered set [n]: an m-simplex, a monotone sequence, goes to the chain
// of its steps.
var StandardSimplexNerve = standardSimplexNerveThm{family.Add(registry.ProofEntry{
	Name: "StandardSimplexNerve",
	Key:  "prop_f08664ea12623517",
	Deps: []registry.EntryLike{
		OrdinalCategoryDef,
		preorder_category.PreorderCategory,
		preorder_category.PreorderCategoryThin,
		nerve.NerveSimplicesDef,
		nerve.NerveFaceDef,
		nerve.NerveDegeneracyDef,
		simplicial_set.SimplicialIsomorphismDef,
		simplicial_set.StandardSimplex,
		simplicial_set.InStandardSimplex,
	},
	Build: family.Card(
		"∀n:num. "+
			"    simplicial_isomorphism(standard_simplex(n), "+
			"        nerve(ordinal_category(n)), "+
			"        λm:num. λθ:(num → num). λi:num. "+
			"            COND(i < m, mk_morphism(θ(i), θ(i + 1), ⊤), mk_morphism(θ(m), θ(m), ⊤)))",
		"a monotone sequence into 0 .. n gives the chain of its steps θ(i) ≤ θ(i + 1), padded "+
			"with the identity at θ(m); faces drop or compose steps as the faces of the sequence "+
			"drop or merge values, the composite of two steps being the step between their ends "+
			"(PreorderCategoryThin), and degeneracies insert an identity; a chain recovers the "+
			"sequence from the sources and the last target, and every chain is the chain of one"),
})}
