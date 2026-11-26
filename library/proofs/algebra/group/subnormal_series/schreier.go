// schreier.go — Schreier's refinement theorem: two subnormal series of
// a group on a set have equivalent refinements, and the refinements
// are written out. The refinement of s through t inserts between s(i)
// and s(i+1) the chain s(i+1)·(s(i) ∩ t(j)), j = 0 … m; the butterfly
// lemma at a = s(i), a' = s(i+1), b = t(j), b' = t(j+1) says its
// factor at (i, j) is isomorphic to the other refinement's factor at
// (j, i), and the swap (i, j) ↦ (j, i) of the double index is the
// correspondence.

package subnormal_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// DoubleIndexSwapBelow — the swap of a double index below n·m lands
// below m·n.
var DoubleIndexSwapBelow = doubleIndexSwapBelowThm{family.Add(registry.ProofEntry{
	Name: "DoubleIndexSwapBelow",
	Key:  "prop_b4398baf5cf4e773",

	Deps: []registry.EntryLike{
		nat_div_mod.Division,
		nat_div_mod.LessEqRightDivEq,
		nat_order.NotLessEq,
		nat_order.LessEqMulRightCancel,
		nat_order.SucLessEqIffLessThan,
		nat_arith.MulSym,
		nat_arith.MulSuc,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num.",
		Hypotheses: []string{
			"k < n * m",
		},
		Conclusion: "rem(k, m) * n + div(k, m) < m * n",
	},
		"k < n·m forces m, n ≠ 0; rem(k, m) < m (Division) and div(k, m) < n (n ≤ "+
			"div(k, m) ⇔ m·n ≤ k, LessEqRightDivEq); so rem·n + div + 1 ≤ (rem + 1)·n ≤ m·n"),
})}

// DoubleIndexSwapInverse — swapping twice gives the index back.
var DoubleIndexSwapInverse = doubleIndexSwapInverseThm{family.Add(registry.ProofEntry{
	Name: "DoubleIndexSwapInverse",
	Key:  "prop_b3d741386ba2013",

	Deps: []registry.EntryLike{
		nat_div_mod.Division,
		nat_div_mod.DivMultAdd,
		nat_div_mod.ModMultAdd,
		nat_div_mod.ModLessThan,
		nat_div_mod.DivEqZero,
		nat_div_mod.LessEqRightDivEq,
		nat_order.NotLessEq,
		nat_arith.MulSym,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num.",
		Hypotheses: []string{
			"k < n * m",
		},
		Conclusion: "rem(rem(k, m) * n + div(k, m), n) * m + div(rem(k, m) * n + div(k, m), n) = k",
	},
		"div(k, m) < n, so the swapped index has remainder div(k, m) and quotient "+
			"rem(k, m) by n (DivMultAdd, ModMultAdd); then k = div(k, m) * m + rem(k, m)"),
})}

// SchreierRefinementTerm — the term of the refinement at the double
// index (i, j), with j allowed to reach m: at j = m the term is
// s(i+1), which is also the term at (i+1, 0).
var SchreierRefinementTerm = schreierRefinementTermThm{family.Add(registry.ProofEntry{
	Name: "SchreierRefinementTerm",
	Key:  "prop_5be46387fc70e9cd",

	Deps: []registry.EntryLike{
		SchreierRefinementDef,
		SeriesTail,
		SeriesStart,
		SeriesChain,
		SeriesSubgroup,
		TrivialCarrierSeries,
		group.SubgroupOne,
		group.SubgroupMul,
		group.SubgroupSubset,
		group.RightIdentityOn,
		group_isomorphism.SubsetSetMulRight,
		quotient_group.InSetMul,
		set_order.SubsetInterAbsorption,
		set_order.SubsetAntisym,
		set_basic.InSing,
		nat_div_mod.DivMultAdd,
		nat_div_mod.ModMultAdd,
		nat_div_mod.ModLessThan,
		nat_div_mod.DivEqZero,
		nat_div_mod.DivZero,
		nat_div_mod.ModZero,
		nat_arith.RightAddDistrib,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m i j:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"subnormal_series(G, t, m)",
			"i < n",
			"j ≤ m",
		},
		Conclusion: "schreier_refinement(s, t, m, i * m + j) = set_mul(s(i + 1), s(i) ∩ t(j))",
	}),
		"for j < m the index reads back as (i, j) (DivMultAdd, ModMultAdd, DivEqZero, ModLessThan); "+
			"for j = m with m ≠ 0 it reads as (i + 1, 0), the term is s(i+2)·(s(i+1) ∩ G.carrier) = "+
			"s(i+1) (SeriesChain, SubgroupMul, SubsetSetMulRight) and the right side is s(i+1)·(s(i) ∩ "+
			"{G.one}) = s(i+1)·{G.one} = s(i+1) (RightIdentityOn); for m = 0 the carrier is {G.one} "+
			"(SeriesStart and SeriesTail of t at 0) and both sides are {G.one} (TrivialCarrierSeries)"),
})}

// SchreierRefinementSeries — the refinement is a subnormal series of
// length n·m: each term is normal in the one before by the butterfly
// lemma's ZassenhausNormal at a = s(i), a' = s(i+1), b = t(j),
// b' = t(j+1).
var SchreierRefinementSeries = schreierRefinementSeriesThm{family.Add(registry.ProofEntry{
	Name: "SchreierRefinementSeries",
	Key:  "prop_203bae908d0e0165",

	Deps: []registry.EntryLike{
		SubnormalSeriesDef,
		SchreierRefinementTerm,
		SchreierRefinementDef,
		SeriesStart,
		SeriesTail,
		SeriesNormal,
		SeriesSubgroup,
		SeriesChain,
		TrivialCarrierSeries,
		group_isomorphism.ZassenhausNormal,
		group_isomorphism.SubsetSetMulRight,
		group.SubgroupOne,
		group.MulIn,
		group.CarrierSubgroupOn,
		nat_div_mod.DivMultAdd,
		nat_div_mod.ModMultAdd,
		nat_div_mod.Division,
		nat_div_mod.ZeroDiv,
		nat_div_mod.ZeroMod,
		nat_div_mod.LessEqRightDivEq,
		nat_order.NotLessEq,
		set_order.SubsetInterAbsorption,
		set_order.SubsetAntisym,
		set_basic.InSing,
		nat_arith.MulSym,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"subnormal_series(G, t, m)",
		},
		Conclusion: "subnormal_series(G, schreier_refinement(s, t, m), n * m)",
	}),
		"the term at 0 is s(1)·(s(0) ∩ G.carrier) = s(1)·G.carrier = G.carrier (ZeroDiv, "+
			"ZeroMod, MulIn, SubsetSetMulRight); for m ≠ 0 a term at or past n·m reads i = "+
			"div(k, m) ≥ n (LessEqRightDivEq), so it is {G.one}·({G.one} ∩ t(j)) = {G.one}; for "+
			"m = 0 the carrier is {G.one} and every term is {G.one} (TrivialCarrierSeries); for "+
			"k < n·m, k = i·m + j with i < n, j < m (Division, LessEqRightDivEq, NotLessEq), "+
			"and the term at (i, j+1) is normal in the term at (i, j) by ZassenhausNormal in "+
			"the group on G.carrier, both read through SchreierRefinementTerm with j+1 ≤ m"),
})}

// SchreierRefinementRefines — the refinement of s through t refines s:
// s(i) is its term at (i, 0).
var SchreierRefinementRefines = schreierRefinementRefinesThm{family.Add(registry.ProofEntry{
	Name: "SchreierRefinementRefines",
	Key:  "prop_6d671fc1746f8c25",

	Deps: []registry.EntryLike{
		SeriesRefinementDef,
		SchreierRefinementTerm,
		SchreierRefinementSeries,
		SeriesStart,
		SeriesTail,
		SeriesSubgroup,
		SeriesChain,
		group.SubgroupMul,
		group_isomorphism.SubsetSetMulRight,
		set_order.SubsetInterAbsorption,
		set_order.SubsetAntisym,
		nat_order.LessEqMulRightCancel,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"subnormal_series(G, t, m)",
		},
		Conclusion: "series_refinement(schreier_refinement(s, t, m), n * m, s, n)",
	}),
		"s(i) = s(i+1)·(s(i) ∩ G.carrier) = s(i+1)·s(i), the term at i·m ≤ n·m, for i < "+
			"n; the term at n·m is {G.one} = s(n) by SeriesTail of SchreierRefinementSeries"),
})}

// SchreierRefinementFactor — the factor of the refinement of s through
// t at (i, j) is isomorphic to the factor of the refinement of t
// through s at (j, i): the butterfly lemma.
var SchreierRefinementFactor = schreierRefinementFactorThm{family.Add(registry.ProofEntry{
	Name: "SchreierRefinementFactor",
	Key:  "prop_f6ca6edc70c136e6",

	Deps: []registry.EntryLike{
		FactorsIsomorphicDef,
		SchreierRefinementTerm,
		SeriesNormal,
		SeriesSubgroup,
		group_isomorphism.Zassenhaus,
		set_algebra.InterComm,
		nat_arith.AddAssoc,
		nat_order.SucLessEqIffLessThan,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m i j:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"subnormal_series(G, t, m)",
			"i < n",
			"j < m",
		},
		Conclusion: "factors_isomorphic(G, " +
			"    schreier_refinement(s, t, m), " +
			"    i * m + j, " +
			"    schreier_refinement(t, s, n), " +
			"    j * n + i)",
	}),
		"both factors read off SchreierRefinementTerm (the index after (i, j) is (i, j+1), with "+
			"j+1 ≤ m); Zassenhaus at a = s(i), a' = s(i+1), b = t(j), b' = t(j+1), the refinement of "+
			"t through s spelling its meets as t(j) ∩ s(i) where the lemma has s(i) ∩ t(j) (InterComm)"),
})}

// Schreier — Schreier's refinement theorem: the two refinements are
// equivalent, the swap of the double index matching the proper factors.
var Schreier = schreierThm{family.Add(registry.ProofEntry{
	Name: "Schreier",
	Key:  "prop_8f17b71a005b3822",

	Deps: []registry.EntryLike{
		SeriesEquivalentDef,
		SchreierRefinementFactor,
		SchreierRefinementSeries,
		FactorsIsomorphicProper,
		DoubleIndexSwapBelow,
		DoubleIndexSwapInverse,
		nat_div_mod.Division,
		nat_div_mod.LessEqRightDivEq,
		nat_order.NotLessEq,
		nat_arith.MulSym,
	},
	Build: family.Card(group.GroupOn.Statement(Statement{
		Binders: "∀s t:(num → set(A)). ∀n m:num.",
		Hypotheses: []string{
			"subnormal_series(G, s, n)",
			"subnormal_series(G, t, m)",
		},
		Conclusion: "series_equivalent(G, " +
			"    schreier_refinement(s, t, m), " +
			"    n * m, " +
			"    schreier_refinement(t, s, n), " +
			"    m * n)",
	}),
		"p(k) = rem(k, m) * n + div(k, m): a proper factor at k is sent to "+
			"a proper factor (FactorsIsomorphicProper) below m·n; one-to-one "+
			"and onto since the swap is its own inverse (DoubleIndexSwapInverse)"),
})}
