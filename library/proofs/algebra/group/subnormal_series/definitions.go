// definitions.go — the series of the chapter: a subnormal series of a
// group on a set, the isomorphism of two of their factors, the
// equivalence of two series, a refinement, a composition series, and
// the refinement Schreier's theorem builds from two series.
//
// A series is a map s : num → set(A) read with a length n: s(0) is the
// carrier, each term is a normal subgroup of the one before, and every
// term from the n-th on is the trivial group {one}. Fixing the terms
// past the length lets two series be read at one index set and, once a
// length is nonzero, closes the double series of Schreier's theorem at
// its seams without a case; at length zero the carrier is {one}.
// A term may repeat; equivalence counts the proper factors only.

package subnormal_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// components binds the operations and carrier as one group record.
const components = "∀G:group_ops(A). "

// SubnormalSeriesDef — `subnormal_series(c, s, n)`: s is a subnormal
// series of the group on c of length n.
var SubnormalSeriesDef = subnormalSeriesDefThm{family.Define(registry.DefEntry{
	Name: "SubnormalSeriesDef",
	Key:  "prop_19e3e2a42cfaf389",

	Const: "subnormal_series",
	Type:  "group_ops(A) → (num → set(A)) → num → bool",
	Equations: []string{
		components + "∀s:(num → set(A)). ∀n:num. subnormal_series(G, s, n) ⇔ s(0) = G.carrier ∧ (∀i:num. n ≤ i ⇒ s(i) = {G.one}) ∧ (∀i:num. i < n ⇒ normal_subgroup(restrict_group(G, s(i)), s(i + 1)))",
	},
})}

// SeriesStart — a series starts at the carrier.
var SeriesStart = seriesStartThm{family.Add(registry.ProofEntry{
	Name: "SeriesStart",
	Key:  "prop_d041e9f5d5480426",

	Build: SubnormalSeriesDef.Entry().Conjunct("s(0) = G.carrier"),
})}

// SeriesTail — a series is the trivial group from its length on.
var SeriesTail = seriesTailThm{family.Add(registry.ProofEntry{
	Name: "SeriesTail",
	Key:  "prop_67578e58c035c49e",

	Build: SubnormalSeriesDef.Entry().Conjunct(Statement{
		Binders: "∀i:num.",
		Hypotheses: []string{
			"n ≤ i",
		},
		Conclusion: "s(i) = {G.one}",
	}),
})}

// SeriesNormal — each term of a series is a normal subgroup of the one
// before.
var SeriesNormal = seriesNormalThm{family.Add(registry.ProofEntry{
	Name: "SeriesNormal",
	Key:  "prop_e33bf32e04eb6669",

	Build: SubnormalSeriesDef.Entry().Conjunct(Statement{
		Binders: "∀i:num.",
		Hypotheses: []string{
			"i < n",
		},
		Conclusion: "normal_subgroup(restrict_group(G, s(i)), s(i + 1))",
	}),
})}

// FactorsIsomorphicDef — `factors_isomorphic(s, i, t, j)`: the i-th
// factor of s, the quotient group s(i)/s(i+1), is isomorphic to the
// j-th factor of t.
var FactorsIsomorphicDef = factorsIsomorphicDefThm{family.Define(registry.DefEntry{
	Name: "FactorsIsomorphicDef",
	Key:  "prop_6325e79c903e7a92",

	Const: "factors_isomorphic",
	Type:  "group_ops(A) → (num → set(A)) → num → (num → set(A)) → num → bool",
	Equations: []string{
		components + "∀s:(num → set(A)). ∀i:num. ∀t:(num → set(A)). ∀j:num. factors_isomorphic(G, s, i, t, j) ⇔ group_isomorphic(quotient_group(restrict_group(G, s(i)), s(i + 1)), quotient_group(restrict_group(G, t(j)), t(j + 1)))",
	},
})}

// SeriesEquivalentDef — `series_equivalent(s, n, t, m)`: the proper
// factors of s and of t correspond one to one, corresponding factors
// isomorphic. A proper factor is one whose two terms differ.
var SeriesEquivalentDef = seriesEquivalentDefThm{family.Define(registry.DefEntry{
	Name: "SeriesEquivalentDef",
	Key:  "prop_e6d57619064a19c5",

	Const: "series_equivalent",
	Type:  "group_ops(A) → (num → set(A)) → num → (num → set(A)) → num → bool",
	Equations: []string{
		components + "∀s:(num → set(A)). ∀n:num. ∀t:(num → set(A)). ∀m:num. series_equivalent(G, s, n, t, m) ⇔ ∃p:(num → num). (∀i:num. i < n ∧ s(i + 1) ≠ s(i) ⇒ p(i) < m ∧ t(p(i) + 1) ≠ t(p(i)) ∧ factors_isomorphic(G, s, i, t, p(i))) ∧ (∀i i':num. i < n ∧ s(i + 1) ≠ s(i) ∧ i' < n ∧ s(i' + 1) ≠ s(i') ∧ p(i) = p(i') ⇒ i = i') ∧ (∀j:num. j < m ∧ t(j + 1) ≠ t(j) ⇒ ∃i:num. i < n ∧ s(i + 1) ≠ s(i) ∧ p(i) = j)",
	},
	Deps: []registry.EntryLike{FactorsIsomorphicDef},
})}

// SeriesRefinementDef — `series_refinement(t, m, s, n)`: t, of length m,
// is a refinement of s, of length n: every term of s is a term of t.
// Two series being chains, the terms then come in the same order.
var SeriesRefinementDef = seriesRefinementDefThm{family.Define(registry.DefEntry{
	Name:  "SeriesRefinementDef",
	Key:   "prop_dc3928feaf693fd6",
	Const: "series_refinement",
	Type:  "(num → set(A)) → num → (num → set(A)) → num → bool",
	Equations: []string{
		"∀t:(num → set(A)). ∀m:num. ∀s:(num → set(A)). ∀n:num. " +
			"    series_refinement(t, m, s, n) ⇔ ∀i:num. i ≤ n ⇒ ∃j:num. j ≤ m ∧ t(j) = s(i)",
	},
})}

// CompositionSeriesDef — `composition_series(c, s, n)`: a subnormal
// series each of whose terms is a maximal proper normal subgroup of the
// one before — the factors are simple, said without a simple group.
var CompositionSeriesDef = compositionSeriesDefThm{family.Define(registry.DefEntry{
	Name: "CompositionSeriesDef",
	Key:  "prop_a1153fdabd4b5ab4",

	Const: "composition_series",
	Type:  "group_ops(A) → (num → set(A)) → num → bool",
	Equations: []string{
		components + "∀s:(num → set(A)). ∀n:num. composition_series(G, s, n) ⇔ subnormal_series(G, s, n) ∧ (∀i:num. i < n ⇒ s(i + 1) ≠ s(i) ∧ (∀k:set(A). normal_subgroup(restrict_group(G, s(i)), k) ∧ s(i + 1) ⊆ k ⇒ k = s(i + 1) ∨ k = s(i)))",
	},
	Deps: []registry.EntryLike{SubnormalSeriesDef},
})}

// CompositionSubnormal — a composition series is a subnormal series.
var CompositionSubnormal = compositionSubnormalThm{family.Add(registry.ProofEntry{
	Name: "CompositionSubnormal",
	Key:  "prop_a55eb9cecac93207",

	Build: CompositionSeriesDef.Entry().Conjunct("subnormal_series(G, s, n)"),
})}

// CompositionMaximal — each term of a composition series is a maximal
// proper normal subgroup of the one before.
var CompositionMaximal = compositionMaximalThm{family.Add(registry.ProofEntry{
	Name: "CompositionMaximal",
	Key:  "prop_5c45b1e51bff080f",

	Build: CompositionSeriesDef.Entry().Conjunct(Statement{
		Binders: "∀i:num.",
		Hypotheses: []string{
			"i < n",
		},
		Conclusion: "s(i + 1) ≠ s(i) ∧ " +
			"(∀k:set(A). normal_subgroup(restrict_group(G, s(i)), k) ∧ s(i + 1) ⊆ k ⇒ k = s(i + 1) ∨ k = s(i))",
	}),
})}

// SchreierRefinementDef — `schreier_refinement(s, t, m)`: the series
// that refines s through t, of length m, by inserting between s(i) and
// s(i+1) the chain s(i+1)·(s(i) ∩ t(j)) for j from 0 to m. Its k-th
// term reads i and j off k as div(k, m) and rem(k, m); at j = 0 it is
// s(i), at j = m it is s(i+1), so the chain closes at each seam, and
// past n·m every term is {one} since s is.
var SchreierRefinementDef = schreierRefinementDefThm{family.Define(registry.DefEntry{
	Name:     "SchreierRefinementDef",
	Key:      "prop_ec122c439575a73e",
	Const:    "schreier_refinement",
	Type:     "(A → A → A) → (num → set(A)) → (num → set(A)) → num → num → set(A)",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀s t:(num → set(A)). ∀m k:num. " +
			"    schreier_refinement(mul, s, t, m, k) = " +
			"    set_mul(mul, s(div(k, m) + 1), s(div(k, m)) ∩ t(rem(k, m)))",
	},
})}
