package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// The set driver's two surfaces — the session's `set_tac` and `by
// {settac}`, the Go `SetTac()` and `BySets(…)` — are one path each: a
// close the session finds, its Go twin finds the same way.

// stepDescriptions lists every ministep of a proof tree, preorder.
func stepDescriptions(n *proof.GoalStackNode) []string {
	var out []string
	var walk func(n *proof.GoalStackNode)
	walk = func(n *proof.GoalStackNode) {
		if d := n.StepDescription(); d != "" {
			out = append(out, d)
		}
		for _, c := range n.Children() {
			walk(c)
		}
	}
	walk(n)
	return out
}

// recordedSetTacMode is the mode of the one SetTac ministep a section
// recorded.
func recordedSetTacMode(t *testing.T, s *Session) proof.SetTacMode {
	t.Helper()
	var modes []proof.SetTacMode
	for _, st := range sectionRecord(t, s.sections[len(s.sections)-1]).Steps {
		if setTac, ok := st.Step.(*proof.StepProto_SetTac); ok {
			modes = append(modes, setTac.SetTac.GetMode())
		}
	}
	require.Len(t, modes, 1, "one recorded SetTac ministep")
	return modes[0]
}

// TestSetTac_GoSetTacIsTheSessionsDoor: the composite-witness equation
// `s ∩ ⋃f = ⋃{s ∩ t | t ∈ f}` is a leaf the legacy full expansion
// cannot close (its residual demands a λ-term witness) and the
// membership mode closes. The session's `set_tac` closes it, in the
// membership mode it tries first, and records that mode; the Go
// `SetTac()` — the same door — closes the same statement and records
// the same step. Before, `SetTac()` was the legacy mode alone and
// failed where the session closed (resolution.CanonicalKernelSubmodule's
// comprehension leaf, #1269).
func TestSetTac_GoSetTacIsTheSessionsDoor(t *testing.T) {
	const statement = "∀s:set(A). ∀f:set(set(A)). s ∩ ⋃f = ⋃{s ∩ t | t | t ∈ f}"
	e, s := boundSession(t, "sets/set_order")
	gid := addTextGoal(t, s, statement)
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	require.Equal(t, gid, state.Goals[0].ID)

	// The negative control: the legacy mode alone leaves the leaf open.
	legacy := proof.CreateGoalStack(state.Goals[0].Statement)
	require.False(t, proof.ApplySetTacMode(legacy, e.env, context.Background(), proof.DefaultSetTacConsts(),
		proof.SetTacMode_SET_TAC_LEGACY, nil), "the legacy full expansion does not close the composite-witness leaf")

	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "set_tac"})
	require.Equal(t, proof.SetTacMode_SET_TAC_MEMBERSHIP, recordedSetTacMode(t, s))
	src := emitSole(t, e, s, "Build_ZzInterBigUnion")
	assert.Contains(t, src, "SetTacMembership()", "--- source: ---\n%s", src)

	fam, ok := registry.FamilyByName("sets/set_order")
	require.True(t, ok)
	script := fam.ParseScript(e.env)
	lemma := script.Lemma(statement, func(a *proof.Argument, s, f proof.Term) {
		a.Show("pointwise, with the member of f as the witness", proof.SetTac())
	})
	require.True(t, lemma.Proved())
	assert.Contains(t, stepDescriptions(lemma), fmt.Sprintf("SetTac(%d consts, SET_TAC_MEMBERSHIP)", len(proof.DefaultSetTacConsts())),
		"the Go door records the step of the mode that closed")
}

// TestBySets_PartialTupleKeepsTheStatedInstance: set_product.CrossSwap's
// inclusion leaf holds set_cross at (A, B) and at (B, A). The session's
// `by {settac}` with InCross pinned at (s₀, t₀) and InCrossProjections
// at (t₀, s₀) closes it; the Go `BySets(At(InCross, s, t),
// At(InCrossProjections, t, s))` closes it the same way. Before, the Go
// premise took the clause lane, where the goal's first type adaptation
// — the (B, A) instance — took the tuple permuted to (t₀, s₀), and the
// driver was handed the instance the author did not name: "By:
// SetTacMembership failed" (#1429).
func TestBySets_PartialTupleKeepsTheStatedInstance(t *testing.T) {
	const statement = "∀s:set(A). ∀t:set(B). image(λq:prod(B, A). (snd(q), fst(q)), set_cross(t, s)) ⊆ set_cross(s, t)"
	pins := []LemmaWithSpec{
		{Key: "set_product.InCross", TermSpecialize: map[string]string{"s": "s₀", "t": "t₀"}},
		{Key: "set_product.InCrossProjections", TermSpecialize: map[string]string{"s": "t₀", "t": "s₀"}},
	}
	e, s := boundSession(t, "sets/set_product")
	addTextGoal(t, s, statement)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, WithLemmas: pins})
	assert.Contains(t, strings.Join(diagnosticMessages(res), "\n"), "settac")

	// The Go twin, on the env a member builds in: the corpus served by
	// name, the recorder's refuter budget.
	goEnv := serve.NewSeedEnv()
	goEnv.LibraryResolver = func(name string) (proof.Thm, bool) {
		entry, ok := registry.ByName(name)
		if !ok {
			return nil, false
		}
		return registry.ForceEntry(core.NewForcer(context.Background()), entry), true
	}
	fam, ok := registry.FamilyByName("sets/set_product")
	require.True(t, ok)
	for _, unfolded := range []bool{false, true} {
		script := fam.ParseScript(goEnv)
		lemma := script.Lemma(statement, func(a *proof.Argument, s, t proof.Term) {
			close := proof.BySets(proof.At(set_product.InCross, s, t), proof.At(set_product.InCrossProjections, t, s))
			if unfolded {
				a.Show("a point of the image is the swap of a point of t × s", proof.Unfold(set_basic.SubsetDef), close)
				return
			}
			a.Show("a point of the image is the swap of a point of t × s", close)
		})
		require.True(t, lemma.Proved(), "subset unfolded first: %v", unfolded)
	}
}

// diagnosticMessages is the messages of a step result's diagnostics.
func diagnosticMessages(res *StepResult) []string {
	out := make([]string, len(res.Diagnostics))
	for i, d := range res.Diagnostics {
		out[i] = d.Message
	}
	return out
}
