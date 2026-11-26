package engine

// Internal types used by the repair-hint pipeline (collectRecommendations →
// recommendationsToHints) and by collectStructuralMoves. They are not part
// of the agent-facing wire API — the public surface is Inspect /
// Retrieve / Probe (see api.go).
//
// The recommendation pipeline has one use, an internal one: when ApplyStep or
// CheckDerivation fail, we synthesize repair hints by running the scoring
// pipeline and converting recommendations to text descriptions. Keeping the
// machinery package-private prevents drift between the agent vocabulary and
// these internal records.

// Recommendation is one ranked closing-move candidate from the legacy
// strategy pipeline. It is a *bridge* type: it lives between the expand /
// def_expand / induction probes and recommendationsToHints, which
// flattens the structured info to repair-hint description strings.
type Recommendation struct {
	Tactic      TacticReq
	Mode        string // rewrite, backward, forward, instantiate, contradiction
	Effect      string // close, simplify, branch
	Reversible  bool
	Confidence  float64
	Description string
	BranchCount int // expected subgoal count (0=close, 1=simplify, 2+=branch)
}

// StructuralMove is the package-private name for one applicable
// parameterless structural tactic (strip_imp / split_conj / split_disj /
// strip_quant / cond_rewrite). The agent-facing equivalent is
// StructuralFact, emitted by enumerateStructuralFacts.
type StructuralMove struct {
	Tactic      string
	Description string
	// Unverified is set for a move whose probe was cut off: why, and
	// that the move is neither verified nor ruled out.
	Unverified string
}
