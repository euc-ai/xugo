package engine

// def_expand(set_comprehension) must make net progress — never report
// success on a step that a second def_expand undoes (the TREADMILL) — on a
// goal whose occurrences the polymorphic definition cannot reach by a
// forward rewrite.
//
// set_comprehension's definition is the identity `⊢ set_comprehension = (λp.p)`.
// The agent-facing def_expand routes through proof.ApplyDefExpand, whose
// dispatch (dispatchDefExpandRewrite) tries tactic.TryDefExpand first and
// tactic.LeanRwTactic as the fallback. The hazard is LeanRwTactic's: on a
// goal whose set_comprehension occurrences sit at a type instance the
// polymorphic def thm can't reach (lemma at var:A, occurrences at
// prod(var:A, var:B); the def_expand rewrite runs no type adaptation —
// dispatchDefExpandRewrite — and its unification is type-strict), the
// forward direction finds nothing and
// LeanRwTactic's bidirectional retry flips the rule to
// `⊢ (λp.p) = set_comprehension`. The variable-LHS ban does NOT fire on that
// flipped rule when the goal has an application site s(x') whose head var is
// itself ∀-bound: unifyEqRewrite wraps both env vars, offering
// tAbs = λs.λx'.s(x') at the pattern's FULL type, so the peel level is 0 and
// the pattern body is the identity ABSTRACTION (not a bare var). λp.p would
// unify with tAbs modulo η on an EMPTY substitution and the rule would fold
// s(x') → set_comprehension(s)(x') inside the hyp — Success=true with zero
// def-expansion — and the next def_expand(set_comprehension) would unfold
// exactly that folded site back: an α-key 2-cycle.
//
// The projection-pattern ban in prop.unifyEq
// (ext/prop/eq_rewrite.go isProjectionPattern; unit-pinned by
// prop.TestUnifyEqRewrite_RefusesProjectionRuleAtFullType) rules that fold
// out: LeanRwTactic yields nil on both directions, and the unfold is
// TryDefExpand's per-occurrence one.
//
// Runs on the registry's constants, like the ematch tests.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// comprehensionTreadmillGoalText distills the treadmill state from the
// TestEMatch_GroundsMembershipKit exploration flow to its two essential
// ingredients:
//   - a set_comprehension occurrence at instance prod(var:A, var:B) — unreachable by
//     the polymorphic def thm's forward rewrite (type-strict unify, no
//     type adaptation on the def_expand path), and
//   - a resident wide ∀-hyp (set_basic.InInsert post def_expand(set_member)) whose matrix
//     contains an application site s'(x') with the head var ∀-BOUND at
//     the def thm's own instance var:A — the shape the flipped identity
//     rule absorbed.
const comprehensionTreadmillGoalText = "s:(var:A → bool), t:(var:A → (var:B → bool)), p:prod(var:A, var:B), ∀s':(var:A → bool).∀x':var:A.∀x:var:A.(insert(x, s', x') ⇔ ((x' = x) ∨ s'(x'))) ⊢ set_comprehension(λg:prod(var:A, var:B).(∃x:var:A.∃y:var:B.comprehension_spec(g, s(x) ∧ t(x, y), (x, y))), p)"

// TestDefExpandSetComprehension_NoTreadmill: repeated def_expand(set_comprehension) must make
// monotone progress and reach honest failure — never revisit a goal
// state with Success=true.
func TestDefExpandSetComprehension_NoTreadmill(t *testing.T) {
	e, s, sid := ematchSessionWithGoal(t, comprehensionTreadmillGoalText)
	ctx := context.Background()

	seen := map[core.PropKey]int{}
	seen[s.sections[0].root.Goal.AlphaKey()] = 1
	successes := 0
	for i := 0; i < 4; i++ {
		id := ematchOpenLeafID(t, s)
		out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: id, Tactic: TacticReq{Type: "def_expand", Const: "set_comprehension"}})
		require.NoError(t, err)
		if !out.Success {
			// Honest failure — the const is exhausted. This is the
			// expected terminal state.
			break
		}
		successes++
		leaf := firstUnsolvedLeaf(s.sections[0].root)
		require.NotNil(t, leaf, "def_expand(set_comprehension) should not close this goal outright")
		key := leaf.Goal.AlphaKey()
		seen[key]++
		require.Equal(t, 1, seen[key],
			"TREADMILL: def_expand(set_comprehension) reported Success=true but reproduced an "+
				"already-visited goal state (round %d):\n%s", i, prop.PrintProp(leaf.Goal))
	}

	// The first application must succeed (there IS a set_comprehension to unfold) and
	// must consume every set_comprehension occurrence via the per-occurrence walker —
	// in particular it must NOT introduce one into the InInsert hyp.
	require.GreaterOrEqual(t, successes, 1, "def_expand(set_comprehension) must apply at least once")
	leaf := firstUnsolvedLeaf(s.sections[0].root)
	require.NotNil(t, leaf)
	require.False(t, prop.ContainsConstName(leaf.Goal, "set_comprehension"),
		"def_expand(set_comprehension) must unfold the definition, not fold new set_comprehension "+
			"occurrences; final goal:\n%s", prop.PrintProp(leaf.Goal))
}
