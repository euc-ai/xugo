package real_valued

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/separation"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// LocallyCompactUrysohn — in a locally compact Hausdorff space a compact
// set inside an open one has a compactly supported Urysohn function.
var LocallyCompactUrysohn = locallyCompactUrysohnThm{family.Add(registry.ProofEntry{
	Name: "LocallyCompactUrysohn",
	Key:  "prop_8331bff23fa11814",
	Deps: []registry.EntryLike{
		compact.LocallyCompactHausdorffNeighbourhood,
		compact.CompactUnions,
		compact.CompactClosed,
		compact.CompactInSubtopology,
		topological_space.SubtopologyTopology,
		topological_space.HausdorffSubtopology,
		topological_space.ClosedInSubtopology,
		separation.CompactHausdorffNormal,
		Urysohn,
		continuous.ClosedPasting,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀k w:set(A).",
		Hypotheses: []string{
			"is_topology(T)",
			"locally_compact_space(T)",
			"hausdorff(T)",
			"compact_in(T, k)",
			"w ∈ T",
			"k ⊆ w",
		},
		Conclusion: "∃f:(A → real). ∃l:set(A). " +
			"    continuous_map(T, real_topology, f) ∧ " +
			"    compact_in(T, l) ∧ " +
			"    l ⊆ w ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ &0 ≤ f(x) ∧ f(x) ≤ &1) ∧ " +
			"    (∀x:A. x ∈ k ⇒ f(x) = &1) ∧ " +
			"    (∀x:A. x ∈ ⋃T ∧ x ∉ l ⇒ f(x) = &0)",
	},
		"Cover k by finitely many open sets whose closures are compact and lie in w "+
			"(LocallyCompactHausdorffNeighbourhood); let v be their union and l the union of their "+
			"closures, compact (CompactUnions) and so closed (CompactClosed), with v ⊆ l ⊆ w. The "+
			"subspace on l is a compact Hausdorff space (SubtopologyTopology, CompactInSubtopology, "+
			"HausdorffSubtopology), so normal (CompactHausdorffNormal), and k and l less v are "+
			"closed in it (ClosedInSubtopology): Urysohn gives g, 0 on l less v and 1 on k. f, g on "+
			"v and 0 elsewhere, is continuous, pasted along the closed sets l and ⋃T less v "+
			"(ClosedPasting), each piece agreeing on its carrier with a continuous map."),
	Reading: "The compactly supported form of Urysohn's lemma, for " +
		"spaces that need not be normal. At k = ∅ the zero function and l = " +
		"∅ serve; Hausdorff is load-bearing for the compact closures inside w.",
})}
