// factorization.go — the canonical factorization of a monotone map.
// Every morphism θ: [m] → [n] of Δ is a composite of codegeneracies
// followed by cofaces: the cofaces at the values θ misses, applied from
// the smallest, after the codegeneracies at the positions where θ
// repeats a value, the smallest applied last. The two index lists are
// ascending and determined by θ, and the factorization with ascending
// lists of indices within their dimensions is unique. The action of a
// monotone map on a simplicial set is defined through these two lists
// (simplicial_operator).

package simplex_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/registry"
)

// CofaceIndicesDef — `coface_indices(t)`: the values of [t.target] that
// the map of t misses, in increasing order.
var CofaceIndicesDef = cofaceIndicesDefThm{family.Define(registry.DefEntry{
	Name:  "CofaceIndicesDef",
	Key:   "prop_841cc46ede8ff32f",
	Const: "coface_indices",
	Type:  "morphism_triple(num, num → num) → list(num)",
	Equations: []string{
		"∀t:morphism_triple(num, num → num). " +
			"    coface_indices(t) = ascending_list(t.target, λi:num. ∀a:num. a ≤ t.source ⇒ t.map(a) ≠ i)",
	},
})}

// CodegeneracyIndicesDef — `codegeneracy_indices(t)`: the positions j
// below t.source at which the map of t repeats its value, in increasing
// order.
var CodegeneracyIndicesDef = codegeneracyIndicesDefThm{family.Define(registry.DefEntry{
	Name:  "CodegeneracyIndicesDef",
	Key:   "prop_b853e75899f9115c",
	Const: "codegeneracy_indices",
	Type:  "morphism_triple(num, num → num) → list(num)",
	Equations: []string{
		"∀t:morphism_triple(num, num → num). " +
			"    codegeneracy_indices(t) = " +
			"    ascending_list(t.source, λj:num. j < t.source ∧ t.map(j) = t.map(j + 1))",
	},
})}

// CofaceCompositeDef — `coface_composite(l)`: the composite of the
// cofaces at an ascending list, the one at the head applied first.
var CofaceCompositeDef = cofaceCompositeDefThm{family.Define(registry.DefEntry{
	Name:  "CofaceCompositeDef",
	Key:   "prop_667ced823b0368aa",
	Const: "coface_composite",
	Type:  "list(num) → num → num",
	Equations: []string{
		"∀l:list(num). " +
			"    coface_composite(l) = list_fold(λi:num. λg:(num → num). g ∘ coface(i), l, λk:num. k)",
	},
	Deps: []registry.EntryLike{CofaceDef},
})}

// CodegeneracyCompositeDef — `codegeneracy_composite(l)`: the composite
// of the codegeneracies at an ascending list, the one at the head
// applied last.
var CodegeneracyCompositeDef = codegeneracyCompositeDefThm{family.Define(registry.DefEntry{
	Name:  "CodegeneracyCompositeDef",
	Key:   "prop_7ccfc8bee3157906",
	Const: "codegeneracy_composite",
	Type:  "list(num) → num → num",
	Equations: []string{
		"∀l:list(num). " +
			"    codegeneracy_composite(l) = " +
			"    list_fold(λj:num. λg:(num → num). codegeneracy(j) ∘ g, l, λk:num. k)",
	},
	Deps: []registry.EntryLike{CodegeneracyDef},
})}

// CanonicalFactorization — a monotone map is the composite of the
// cofaces at the values it misses after the codegeneracies at the
// positions where it repeats.
var CanonicalFactorization = canonicalFactorizationThm{family.Add(registry.ProofEntry{
	Name: "CanonicalFactorization",
	Key:  "prop_16f3f1a3eb428c38",
	Deps: []registry.EntryLike{
		CofaceIndicesDef,
		CodegeneracyIndicesDef,
		CofaceCompositeDef,
		CodegeneracyCompositeDef,
		SimplexCategoryDef,
		category.CategoryFromHomDef,
		list.AscendingListMember,
	},
	Build: family.Card(Statement{
		Binders: "∀t:morphism_triple(num, num → num).",
		Hypotheses: []string{
			"t ∈ category_morphisms(simplex_category)",
		},
		Conclusion: "t.map = " +
			"normalize_on(0 .. t.source, " +
			"    0, " +
			"    coface_composite(coface_indices(t)) ∘ codegeneracy_composite(codegeneracy_indices(t)))",
	},
		"the codegeneracies at the repeated positions collapse [m] onto [k], k + 1 the "+
			"number of values of θ, monotonically and onto; the cofaces at the missed values, "+
			"from the smallest, carry [k] onto the image of θ in order; both sides are monotone "+
			"on 0 .. m with the same image and the same repeats, hence equal there, and 0 past m"),
})}

// FactorizationUnique — a factorization by ascending lists of indices
// within their dimensions is the canonical one.
var FactorizationUnique = factorizationUniqueThm{family.Add(registry.ProofEntry{
	Name: "FactorizationUnique",
	Key:  "prop_fd1c4790eeb1dc7c",
	Deps: []registry.EntryLike{
		CofaceIndicesDef,
		CodegeneracyIndicesDef,
		CofaceCompositeDef,
		CodegeneracyCompositeDef,
		list.ListAscendingDef,
		list.AscendingListUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀t:morphism_triple(num, num → num). ∀l l':list(num).",
		Hypotheses: []string{
			"t ∈ category_morphisms(simplex_category)",
			"list_ascending(l)",
			"∀i:num. list_member(i, l) ⇒ i ≤ t.target",
			"list_ascending(l')",
			"∀j:num. list_member(j, l') ⇒ j < t.source",
			"list_length(l) + t.source = list_length(l') + t.target",
			"∀a:num. a ≤ t.source ⇒ t.map(a) = (coface_composite(l) ∘ codegeneracy_composite(l'))(a)",
		},
		Conclusion: "l = coface_indices(t) ∧ l' = codegeneracy_indices(t)",
	},
		"the codegeneracies at l′, applied from the largest, are defined on [m] and collapse it "+
			"onto [m − |l′|] with exactly the repeats l′; the cofaces at l, from the smallest, carry "+
			"that onto [n] by the length equation, missing exactly l; so l and l′ are the missed values "+
			"and the repeats of θ, ascending, and equal the canonical lists (AscendingListUnique)"),
	Reading: "The bounds and the length equation are load-bearing: a coface " +
		"or codegeneracy at an index past its dimension acts as the identity on " +
		"the numbers it is applied to, and would add a factor that changes nothing.",
})}
