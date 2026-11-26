// series.go — what a subnormal series carries: every term a subgroup
// of the carrier and a group on a set, the terms a chain, each factor
// a group on a set; and the two relations, isomorphism of factors, an
// equivalence, and equivalence of series, symmetric and transitive.

package subnormal_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The terms and the factors
// ---------------------------------------------------------------------------

// SeriesSubgroup — every term of a series is a subgroup of the carrier:
// by induction, each is a subgroup of the one before, and from the
// length on it is {one}.
var SeriesSubgroup = seriesSubgroupThm{family.Add(registry.ProofEntry{
	Name: "SeriesSubgroup",
	Key:  "prop_1308fcd59d77c26d",

	Deps: []registry.EntryLike{
		SeriesStart,
		SeriesTail,
		SeriesNormal,
		group_isomorphism.SubgroupTrans,
		group.NormalSubgroupSubgroup,
		group.CarrierSubgroupOn,
		group.TrivialSubgroupOn,
		peano.Induction,
		nat_order.NotLessThan,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s:(num → set(A)). ∀n i:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
		},
		Conclusion: "subgroup(G, s(i))",
	}),
		"induction on i: s(0) = G.carrier is a subgroup of G.carrier; s(i+1) is a subgroup "+
			"of s(i) for i < n, hence of G.carrier (SubgroupTrans), and is {G.one} for n ≤ i"),
})}

// SeriesGroup — every term of a series is a group on a set.
var SeriesGroup = seriesGroupThm{family.Add(registry.ProofEntry{
	Name: "SeriesGroup",
	Key:  "prop_6f44431e0cc04f26",

	Deps: []registry.EntryLike{SeriesSubgroup, group.SubgroupGroupOn},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s:(num → set(A)). ∀n i:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
		},
		Conclusion: "group_on(restrict_group(G, s(i)))",
	}),
		"SubgroupGroupOn at SeriesSubgroup"),
})}

// SeriesChain — the terms of a series descend.
var SeriesChain = seriesChainThm{family.Add(registry.ProofEntry{
	Name: "SeriesChain",
	Key:  "prop_d448570e121d6342",

	Deps: []registry.EntryLike{
		SeriesTail,
		SeriesNormal,
		group.NormalSubgroupSubgroup,
		group.SubgroupSubset,
		set_order.SubsetTrans,
		set_order.SubsetRefl,
		peano.Induction,
		nat_order.LessEqExists,
		nat_order.NotLessThan,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s:(num → set(A)). ∀n i j:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"i ≤ j",
		},
		Conclusion: "s(j) ⊆ s(i)",
	},
		"j = i + d (LessEqExists), induction on d: s(i+1) ⊆ s(i) for "+
			"every i — as a subgroup for i < n, both {G.one} for n ≤ i"),
})}

// TrivialCarrierSeries — a series of the one-point group is {one}
// throughout: every term lies in s(0) = {one} and holds one.
var TrivialCarrierSeries = trivialCarrierSeriesThm{family.Add(registry.ProofEntry{
	Name: "TrivialCarrierSeries",
	Key:  "prop_2691ef1b6084dbba",

	Deps: []registry.EntryLike{
		SeriesStart,
		SeriesTail,
		SeriesNormal,
		SeriesChain,
		group.NormalSubgroupSubgroup,
		group.SubgroupOne,
		set_basic.InSing,
		set_order.SubsetAntisym,
		peano.Cases,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s:(num → set(A)). ∀n i:num.",
		Hypotheses: []string{
			"subnormal_series(restrict_group(G, {G.one}), s, n)",
		},
		Conclusion: "s(i) = {G.one}",
	},
		"s(i) ⊆ s(0) = {G.one} by the chain; G.one ∈ s(i): at 0 outright, "+
			"at i+1 ≤ n as a subgroup of s(i), from n on by the tail"),
})}

// FactorGroup — each factor of a series is a group on a set: the
// quotient of a term by the normal subgroup after it.
var FactorGroup = factorGroupThm{family.Add(registry.ProofEntry{
	Name: "FactorGroup",
	Key:  "prop_d824a6c005ee203f",

	Deps: []registry.EntryLike{SeriesNormal, SeriesGroup, quotient_group.QuotientGroupOn},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s:(num → set(A)). ∀n i:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"i < n",
		},
		Conclusion: "group_on(quotient_group(restrict_group(G, s(i)), s(i + 1)))",
	}),
		"QuotientGroupOn in the group on s(i) (SeriesGroup), s(i+1) normal in it (SeriesNormal)"),
})}

// FactorTrivialIff — a factor is the one-point group exactly when its
// two terms agree.
var FactorTrivialIff = factorTrivialIffThm{family.Add(registry.ProofEntry{
	Name: "FactorTrivialIff",
	Key:  "prop_be88351b04e1e9d3",

	Deps: []registry.EntryLike{SeriesNormal, SeriesGroup, quotient_group.QuotientTrivialIff},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s:(num → set(A)). ∀n i:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"i < n",
		},
		Conclusion: "left_cosets(s(i), s(i + 1)) = {s(i + 1)} ⇔ s(i + 1) = s(i)",
	}),
		"QuotientTrivialIff in the group on s(i)"),
})}

// ---------------------------------------------------------------------------
// Isomorphism of factors
// ---------------------------------------------------------------------------

// FactorsIsomorphicProper — isomorphic factors are proper together.
var FactorsIsomorphicProper = factorsIsomorphicProperThm{family.Add(registry.ProofEntry{
	Name: "FactorsIsomorphicProper",
	Key:  "prop_dbe40d18153eef7b",

	Deps: []registry.EntryLike{
		FactorsIsomorphicDef,
		FactorTrivialIff,
		group_isomorphism.IsomorphicTrivial,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m i j:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"subnormal_series(G, t, m)",
			"i < n",
			"j < m",
			"factors_isomorphic(G, s, i, t, j)",
		},
		Conclusion: "s(i + 1) ≠ s(i) ⇔ t(j + 1) ≠ t(j)",
	}),
		"IsomorphicTrivial at the two factor groups, each "+
			"trivial exactly when its terms agree (FactorTrivialIff)"),
})}

// FactorsIsomorphicRefl — a factor is isomorphic to itself.
var FactorsIsomorphicRefl = factorsIsomorphicReflThm{family.Add(registry.ProofEntry{
	Name: "FactorsIsomorphicRefl",
	Key:  "prop_cb5cc42d455d72df",

	Deps: []registry.EntryLike{FactorsIsomorphicDef, FactorGroup, group_isomorphism.IsomorphicRefl},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s:(num → set(A)). ∀n i:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"i < n",
		},
		Conclusion: "factors_isomorphic(G, s, i, s, i)",
	}),
		"IsomorphicRefl at the factor group (FactorGroup)"),
})}

// FactorsIsomorphicSym — isomorphism of factors is symmetric.
var FactorsIsomorphicSym = factorsIsomorphicSymThm{family.Add(registry.ProofEntry{
	Name: "FactorsIsomorphicSym",
	Key:  "prop_6f904b7927bcb0ee",

	Deps: []registry.EntryLike{FactorsIsomorphicDef, group_isomorphism.IsomorphicSym},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s t:(num → set(A)). ∀i j:num.",
		Hypotheses: []string{
			"factors_isomorphic(G, s, i, t, j)",
		},
		Conclusion: "factors_isomorphic(G, t, j, s, i)",
	},
		"IsomorphicSym"),
})}

// FactorsIsomorphicTrans — isomorphism of factors is transitive.
var FactorsIsomorphicTrans = factorsIsomorphicTransThm{family.Add(registry.ProofEntry{
	Name: "FactorsIsomorphicTrans",
	Key:  "prop_fe1f7ee75ef79a38",

	Deps: []registry.EntryLike{FactorsIsomorphicDef, group_isomorphism.IsomorphicTrans},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s t u:(num → set(A)). ∀i j k:num.",
		Hypotheses: []string{
			"factors_isomorphic(G, s, i, t, j)",
			"factors_isomorphic(G, t, j, u, k)",
		},
		Conclusion: "factors_isomorphic(G, s, i, u, k)",
	},
		"IsomorphicTrans"),
})}

// ---------------------------------------------------------------------------
// Equivalence of series
// ---------------------------------------------------------------------------

// EquivalentSym — equivalence of series is symmetric: the
// correspondence is inverted on the proper factors, the inverse of a
// proper factor of t being the proper factor of s sent to it.
var EquivalentSym = equivalentSymThm{family.Add(registry.ProofEntry{
	Name: "EquivalentSym",
	Key:  "prop_f23466487b965ab3",

	Deps: []registry.EntryLike{SeriesEquivalentDef, FactorsIsomorphicSym},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s t:(num → set(A)). ∀n m:num.",
		Hypotheses: []string{
			"series_equivalent(G, s, n, t, m)",
		},
		Conclusion: "series_equivalent(G, t, m, s, n)",
	},
		"q(j) = εi. i < n ∧ s(i + 1) ≠ s(i) ∧ p(i) = j, which exists by the onto "+
			"clause and is the only one by the one-to-one clause; FactorsIsomorphicSym"),
})}

// EquivalentTrans — equivalence of series is transitive: the
// correspondences compose.
var EquivalentTrans = equivalentTransThm{family.Add(registry.ProofEntry{
	Name: "EquivalentTrans",
	Key:  "prop_16c5029f057f6144",

	Deps: []registry.EntryLike{SeriesEquivalentDef, FactorsIsomorphicTrans},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s t u:(num → set(A)). ∀n m l:num.",
		Hypotheses: []string{
			"series_equivalent(G, s, n, t, m)",
			"series_equivalent(G, t, m, u, l)",
		},
		Conclusion: "series_equivalent(G, s, n, u, l)",
	},
		"q ∘ p on the proper factors of s: into the proper factors "+
			"of u, one-to-one and onto as each is; FactorsIsomorphicTrans"),
})}
