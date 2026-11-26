// Countable cube covers give the null ideal and exclude nonempty open sets.

package vec_null

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// NullEmpty — the empty set is null in every dimension.
var NullEmpty = nullEmptyThm{family.Add(registry.ProofEntry{
	Name: "NullEmpty",
	Key:  "prop_d27df05bd3c262a4",
	Deps: []registry.EntryLike{real_series.SumsZero},
	Build: family.Card("∀n:num. vec_null_set⟨n⟩(∅)",
		"In dimension zero use the empty-set clause; in positive dimension take "+
			"all centres and radii zero and the zero sum (real_series.SumsZero)."),
})}

// NullZeroDimension — the empty set is the only null subset of ℝ⁰.
var NullZeroDimension = nullZeroDimensionThm{family.Add(registry.ProofEntry{
	Name: "NullZeroDimension",
	Key:  "prop_6e0fafb8e1f78c3d",
	Build: family.Card("∀S:set(num → real). vec_null_set⟨0⟩(S) ⇔ S = ∅",
		"Unfold the dimension-zero clause. The single point "+
			"of ℝ⁰ has counting volume one and is not null."),
})}

// NullSubset — subsets of null sets are null.
var NullSubset = nullSubsetThm{family.Add(registry.ProofEntry{
	Name: "NullSubset",
	Key:  "prop_c3c6428ee7b7bc6",
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀S T:set(num → real).",
		Hypotheses: []string{
			"S ⊆ T",
			"vec_null_set⟨n⟩(T)",
		},
		Conclusion: "vec_null_set⟨n⟩(S)",
	}, "Use each cover of T also as a cover of S; in dimension zero T is empty and so is S."),
})}

// NullCountableUnion — a countable union of null sets is null.
var NullCountableUnion = nullCountableUnionThm{family.Add(registry.ProofEntry{
	Name: "NullCountableUnion",
	Key:  "prop_744d3625d029935e",
	Deps: []registry.EntryLike{
		NullEmpty,
		cardinal.CountableCover,
		real_series.Geometric,
		real_series.SumsPartialLessEq,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀C:set(set(num → real)).",
		Hypotheses: []string{
			"countable(C)",
			"∀S:set(num → real). S ∈ C ⇒ vec_null_set⟨n⟩(S)",
		},
		Conclusion: "vec_null_set⟨n⟩(⋃C)",
	}, "Enumerate C using cardinal.CountableCover, replacing entries outside C by the "+
		"empty set. Give the j-th set volume budget ε/2^(j+2), enumerate the pairs of "+
		"cube indices without repetition, and bound every finite partial sum by the "+
		"geometric total ε/2 (real_series.Geometric, real_series.SumsPartialLessEq); "+
		"monotone bounded partial sums converge. Dimension zero and C empty use NullEmpty."),
})}

// NullCoordinateSubspace — a lower-dimensional coordinate subspace is null.
var NullCoordinateSubspace = nullCoordinateSubspaceThm{family.Add(registry.ProofEntry{
	Name: "NullCoordinateSubspace",
	Key:  "prop_5a10193f830bd35c",
	Deps: []registry.EntryLike{NullCountableUnion},
	Build: family.Card(Statement{
		Binders:    "∀a b:num.",
		Hypotheses: []string{"a < b"},
		Conclusion: "vec_null_set⟨b⟩({x:num → real | vec⟨a⟩(x)})",
	}, "Cover a bounded a-dimensional coordinate box by O(δ^(-a)) open b-cubes of radius "+
		"O(δ). Their total b-volume tends to zero as δ^(b-a), also when a = 0; the coordinate "+
		"subspace is the countable union of its bounded boxes (NullCountableUnion)."),
})}

// OpenNonemptyNotNull — a nonempty open set has positive cube content.
var OpenNonemptyNotNull = openNonemptyNotNullThm{family.Add(registry.ProofEntry{
	Name: "OpenNonemptyNotNull",
	Key:  "prop_63c1a606baf3deec",
	Deps: []registry.EntryLike{
		euclidean_topology.OpenIff,
		euclidean_topology.BoxCompact,
		real_series.SumsPartialLessEq,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:set(num → real).",
		Hypotheses: []string{
			"0 < n",
			"U ∈ euclidean_topology(n)",
			"U ≠ ∅",
		},
		Conclusion: "¬vec_null_set⟨n⟩(U)",
	},
		"Put a positive-side closed cube inside U using euclidean_topology.OpenIff. A countable "+
			"open cube cover has a finite subcover of that cube (euclidean_topology.BoxCompact); a "+
			"grid through all face coordinates proves that its volume is at most the sum of the "+
			"covering volumes, which is at most the series sum (real_series.SumsPartialLessEq). This "+
			"contradicts a budget smaller than the inner cube's volume and uses no product measure."),
})}
