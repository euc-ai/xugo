// composition.go — the Jordan–Hölder theorem: any two composition
// series of a group on a set are equivalent, and so have one length.
// A refinement of a composition series only repeats its terms, since a
// normal subgroup of s(i) between s(i+1) and s(i) is one of the two;
// so the refinement is equivalent to the series, and Schreier's
// theorem joins the two series through their refinements.

package subnormal_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CompositionSeriesInjective — the terms of a composition series up to
// its length are distinct: the chain descends strictly.
var CompositionSeriesInjective = compositionSeriesInjectiveThm{family.Add(registry.ProofEntry{
	Name: "CompositionSeriesInjective",
	Key:  "prop_ab6cec762f93cef7",

	Deps: []registry.EntryLike{
		CompositionSubnormal,
		CompositionMaximal,
		SeriesChain,
		set_order.SubsetAntisym,
		nat_order.NotLessThan,
		nat_order.SucLessEqIffLessThan,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s:(num → set(A)). ∀n i i':num.",
		Hypotheses: []string{
			"composition_series(G, s, n)",
			"i ≤ n",
			"i' ≤ n",
			"s(i) = s(i')",
		},
		Conclusion: "i = i'",
	},
		"for i < i' ≤ n: s(i') ⊆ s(i + 1) ⊊ s(i) by the chain and properness, so s(i) ≠ s(i')"),
})}

// CompositionRefinementStep — in a refinement t of a composition
// series s, the term after one equal to s(i) is s(i) or s(i+1): it is
// normal in s(i) and contains s(i+1), which is a later term of t.
var CompositionRefinementStep = compositionRefinementStepThm{family.Add(registry.ProofEntry{
	Name: "CompositionRefinementStep",
	Key:  "prop_56c4f38101fe285a",

	Deps: []registry.EntryLike{
		CompositionSubnormal,
		CompositionMaximal,
		SeriesRefinementDef,
		SeriesNormal,
		SeriesChain,
		group.NormalSubgroupSubgroup,
		set_order.SubsetAntisym,
		nat_order.NotLessThan,
		nat_order.SucLessEqIffLessThan,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s t:(num → set(A)). ∀n m i j:num.",
		Hypotheses: []string{
			"composition_series(G, s, n)",
			"subnormal_series(G, t, m)",
			"series_refinement(t, m, s, n)",
			"i < n",
			"t(j) = s(i)",
		},
		Conclusion: "t(j + 1) = s(i) ∨ t(j + 1) = s(i + 1)",
	},
		"s(i+1) = t(j') for some j' ≤ m; j' > j since t(j) ⊆ t(j') would otherwise put s(i) "+
			"inside s(i+1), against properness, so j < m too; then s(i+1) ⊆ t(j+1) ⊆ s(i), and "+
			"t(j+1) is normal in t(j) = s(i) (SeriesNormal), so CompositionMaximal decides it"),
})}

// CompositionRefinementTerm — every term of a refinement of a
// composition series is a term of the series: by induction on the
// index, from t(0) = c = s(0) through CompositionRefinementStep.
var CompositionRefinementTerm = compositionRefinementTermThm{family.Add(registry.ProofEntry{
	Name: "CompositionRefinementTerm",
	Key:  "prop_86aae63025e3cdbd",

	Deps: []registry.EntryLike{
		CompositionRefinementStep,
		CompositionSubnormal,
		SeriesStart,
		SeriesTail,
		SeriesChain,
		SeriesNormal,
		group.NormalSubgroupSubgroup,
		group.SubgroupOne,
		set_basic.InSing,
		set_order.SubsetAntisym,
		nat_order.NotLessThan,
		peano.Induction,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s t:(num → set(A)). ∀n m j:num.",
		Hypotheses: []string{
			"composition_series(G, s, n)",
			"subnormal_series(G, t, m)",
			"series_refinement(t, m, s, n)",
		},
		Conclusion: "∃i:num. i ≤ n ∧ t(j) = s(i)",
	},
		"induction on j: t(0) = G.carrier = s(0); if t(j) = s(i) with i < n then t(j+1) is "+
			"s(i) or s(i+1); if i = n then t(j) = {G.one} and t(j+1) ⊆ t(j) is {G.one} = s(n)"),
})}

// CompositionRefinementProperFactor — a proper factor of a refinement
// of a composition series is a factor of the series.
var CompositionRefinementProperFactor = compositionRefinementProperFactorThm{family.Add(registry.ProofEntry{
	Name: "CompositionRefinementProperFactor",
	Key:  "prop_94b12005ce5c6c0b",

	Deps: []registry.EntryLike{
		CompositionRefinementTerm,
		CompositionRefinementStep,
		SeriesTail,
		SeriesChain,
		SeriesNormal,
		group.NormalSubgroupSubgroup,
		group.SubgroupOne,
		set_basic.InSing,
		set_order.SubsetAntisym,
		nat_order.NotLessThan,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s t:(num → set(A)). ∀n m j:num.",
		Hypotheses: []string{
			"composition_series(G, s, n)",
			"subnormal_series(G, t, m)",
			"series_refinement(t, m, s, n)",
			"j < m",
			"t(j + 1) ≠ t(j)",
		},
		Conclusion: "∃i:num. i < n ∧ t(j) = s(i) ∧ t(j + 1) = s(i + 1)",
	},
		"t(j) = s(i) for some i ≤ n; i = n would make t(j) and t(j+1) both {G.one}; so i < "+
			"n and CompositionRefinementStep gives t(j+1) = s(i+1), the other arm being excluded"),
})}

// CompositionRefinementOnto — every factor of a composition series is
// a proper factor of any refinement: at the last index j with
// t(j) = s(i), the next term is s(i+1).
var CompositionRefinementOnto = compositionRefinementOntoThm{family.Add(registry.ProofEntry{
	Name: "CompositionRefinementOnto",
	Key:  "prop_ee53b16188daffb7",

	Deps: []registry.EntryLike{
		CompositionRefinementStep,
		SeriesRefinementDef,
		CompositionSeriesInjective,
		SeriesTail,
		nat_order.MaximumExists,
	},
	Build: family.Card(Statement{
		Binders: "∀G:group_ops(A). ∀s t:(num → set(A)). ∀n m i:num.",
		Hypotheses: []string{
			"composition_series(G, s, n)",
			"subnormal_series(G, t, m)",
			"series_refinement(t, m, s, n)",
			"i < n",
		},
		Conclusion: "∃j:num. j < m ∧ t(j) = s(i) ∧ t(j + 1) = s(i + 1)",
	},
		"the indices j ≤ m with t(j) = s(i) are not empty (refinement) and "+
			"bounded; at the greatest, t(j+1) ≠ s(i), so t(j+1) = s(i+1) by "+
			"CompositionRefinementStep, and j < m since t(m) = {G.one} = s(n) ≠ s(i)"),
})}

// RefinementOfComposition — a refinement of a composition series is
// equivalent to it: a proper factor of the refinement is a factor of
// the series, and the index of that factor is the correspondence.
var RefinementOfComposition = refinementOfCompositionThm{family.Add(registry.ProofEntry{
	Name: "RefinementOfComposition",
	Key:  "prop_612276f656860e4e",

	Deps: []registry.EntryLike{
		SeriesEquivalentDef,
		CompositionRefinementProperFactor,
		CompositionRefinementOnto,
		CompositionSeriesInjective,
		CompositionSubnormal,
		CompositionMaximal,
		FactorsIsomorphicRefl,
		SeriesChain,
		set_order.SubsetAntisym,
		nat_order.NotLessThan,
		nat_order.SucLessEqIffLessThan,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m:num.",
		Hypotheses: []string{
			"composition_series(G, s, n)",
			"subnormal_series(G, t, m)",
			"series_refinement(t, m, s, n)",
		},
		Conclusion: "series_equivalent(G, t, m, s, n)",
	}),
		"p(j) = εi. i < n ∧ t(j) = s(i) ∧ t(j + 1) = s(i + 1), which exists for a proper j "+
			"(CompositionRefinementProperFactor); the factors are then the same groups "+
			"(FactorsIsomorphicRefl); p is one-to-one: j < j' with t(j) = t(j') = s(i) and t(j+1) = "+
			"s(i+1) gives s(i) = t(j') ⊆ t(j+1) = s(i+1) by SeriesChain, against CompositionMaximal; "+
			"onto by CompositionRefinementOnto, the ε returning i by CompositionSeriesInjective"),
})}

// JordanHolder — the Jordan–Hölder theorem: two composition series of
// a group on a set are equivalent.
var JordanHolder = jordanHolderThm{family.Add(registry.ProofEntry{
	Name: "JordanHolder",
	Key:  "prop_1f7bb0ffe46b9061",

	Deps: []registry.EntryLike{
		Schreier,
		RefinementOfComposition,
		SchreierRefinementSeries,
		SchreierRefinementRefines,
		CompositionSubnormal,
		EquivalentSym,
		EquivalentTrans,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m:num.",
		Hypotheses: []string{
			"composition_series(G, s, n)",
			"composition_series(G, t, m)",
		},
		Conclusion: "series_equivalent(G, s, n, t, m)",
	}),
		"s is equivalent to its Schreier refinement through t (RefinementOfComposition, turned "+
			"round), that to t's refinement through s (Schreier), that to t; EquivalentTrans twice"),
})}

// JordanHolderLength — two composition series of a group on a set have
// one length: every factor is proper, so the correspondence is a
// one-to-one map of {i | i < n} onto {j | j < m}.
var JordanHolderLength = jordanHolderLengthThm{family.Add(registry.ProofEntry{
	Name: "JordanHolderLength",
	Key:  "prop_7dac96fd923e9ae8",

	Deps: []registry.EntryLike{
		JordanHolder,
		SeriesEquivalentDef,
		CompositionMaximal,
		num_segment.HasSizeBelowStrict,
		cardinality.HasSizeImageInj,
		cardinality.HasSizeDef,
		set_basic.InImage,
		set_basic.Extension,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m:num.",
		Hypotheses: []string{
			"composition_series(G, s, n)",
			"composition_series(G, t, m)",
		},
		Conclusion: "n = m",
	}),
		"every factor is proper, so the correspondence of JordanHolder is one-to-one "+
			"on {i | i < n} with image {j | j < m}; HasSizeImageInj gives that image "+
			"size n, HasSizeBelowStrict gives it size m, and a size is one (HasSizeDef)"),
})}
