// ematch.go — the "ematch" tactic: E-matching ground pre-instantiation
// of resident ∀-hypotheses.
//
// The trigger/match core lives in prover/solver/ematch, so that the By
// executor's grounding stage (the manual's S4) can run the same enumeration
// below the engine→prover layering boundary — see that package's doc for
// the algorithm, the L1/L2/L3 trigger ladder, and the determinism
// contract). This file is the session glue: run the enumeration on the
// focused goal, convert the plans to Specialize entries, and apply them as
// ONE composite `specialize` ministep (proof.ApplySpecialize, sources kept)
// — the recorded step carries the PLANS as data (hyp index + witness tuple
// per entry), not the search that found them, so replay is independent of
// the trigger heuristics and caps (they can evolve without breaking
// recorded proofs), and no drifting-index per-rung instantiate chain
// appears.
//
// The tactic only ADDS hypotheses (sources kept); it never closes a
// goal by itself. The intended shape is `lemma…; ematch; auto` — and
// after wide hyps have served their instances, `clear` remains the
// agent's tool against residual refute-poisoning.

package engine

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/ematch"
)

// applyEMatchGround runs the E-matching grounding pass on the clone's
// focused goal node. Returns the number of ground instantiations
// applied (0 means the tactic did not apply).
func applyEMatchGround(clone *proof.GoalStackNode) int {
	plans := ematch.GroundPlans(clone.Goal)
	if len(plans) == 0 {
		return 0
	}

	// Apply ALL plans as ONE composite `specialize` ministep (sources
	// kept — the ematch contract is only-ADD). Plans were enumerated
	// against the original goal, so every hyp index refers to the same
	// pre-step snapshot the recorded proto carries. A plan whose final
	// instance is already resident is absorbed by the tactic's hyp-set
	// dedup; if EVERY plan is a no-op the step reports no progress and
	// we return 0 ("nothing NEW").
	leaf := firstUnsolvedLeaf(clone)
	if leaf == nil {
		return 0
	}
	specs := make([]proof.SpecializeHyp, 0, len(plans))
	for _, p := range plans {
		// Defensive per-plan validation: one malformed plan must drop
		// out alone, not nil the whole batch (the matcher guarantees
		// shape/type by construction; this mirrors the old chain's
		// per-rung guards).
		idx := hypIndexByAlphaKey(leaf.Goal, p.Hyp)
		if idx < 0 || !p.Valid(leaf.Goal.Hyp(idx)) {
			continue
		}
		specs = append(specs, proof.InstHyp(idx, p.Witnesses...))
	}
	if len(specs) == 0 || !proof.ApplySpecialize(leaf, specs, true) {
		return 0
	}
	return len(specs)
}

// stripLeadingForalls peels the leading ∀-binders off h (the core's
// helper, re-exposed for this package's structural tests/filters).
func stripLeadingForalls(h core.Term) ([]core.VarTerm, core.Term) {
	return ematch.StripLeadingForalls(h)
}

func firstUnsolvedLeaf(n *proof.GoalStackNode) *proof.GoalStackNode {
	leaves := n.UnsolvedLeaves()
	if len(leaves) == 0 {
		return nil
	}
	return leaves[0]
}

func hypIndexByAlphaKey(goal core.Prop, t core.Term) int {
	key := t.AlphaKey()
	for i := range goal.NumHyps() {
		if goal.Hyp(i).AlphaKey() == key {
			return i
		}
	}
	return -1
}
