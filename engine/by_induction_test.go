package engine

import (
	"context"
	"regexp"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// byInductionSession opens a session bound to nat_order on goal.
func byInductionSession(t *testing.T, goal string) (*Engine, *Session, string) {
	t.Helper()
	e := newEngine(statedSessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "nat_num/nat_order", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	gid := addTextGoal(t, s, goal)
	return e, s, gid
}

// TestByInduction_OpensOneLeafPerObligation: `by_induction` at a
// principle grounded at its predicate asserts the principle's
// obligations and closes the goal from them — one open leaf per
// obligation, each the case the author proves next, and nothing else
// open. The record is the shape Go's ByInduction records: the asserts,
// then the by.
func TestByInduction_OpensOneLeafPerObligation(t *testing.T) {
	e, s, gid := byInductionSession(t, "Q:(num → bool) ⊢ ∀n:num. Q(n)")
	res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type:           "by_induction",
		LemmaKey:       "nat_order.StrongInduction",
		TermSpecialize: map[string]string{"P": "Q"},
	}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	require.Len(t, res.Produced, 1, "strong induction has one obligation")
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	assert.Equal(t, "∀n.((∀m.((m < n) ⇒ Q(m))) ⇒ Q(n))", ext.PrintTerm(state.Goals[0].Statement.Conclusion()),
		"the open leaf is the obligation, under the principle's own binder names")
}

// TestByInduction_TheCaseClosesAndTheMemberEmitsAsTheVerb: the case a
// `by_induction` leaves open is proved like any leaf, and the proved
// section emits as `ByInduction(principle, Case(…))` — the verb, not
// the asserts and the by it records, and the principle cited before
// its predicate, because the predicate the table wrote is the one the
// goal reads.
func TestByInduction_TheCaseClosesAndTheMemberEmitsAsTheVerb(t *testing.T) {
	e, s, gid := byInductionSession(t, "∀n:num. n + 0 = n")
	res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type:           "by_induction",
		LemmaKey:       "nat_order.StrongInduction",
		TermSpecialize: map[string]string{"P": "λn:num. n + 0 = n"},
	}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	require.Len(t, res.Produced, 1)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "arith"})
	require.True(t, s.sections[0].root.Proved())
	var asserts, bys int
	for _, st := range s.sections[0].root.DetailedProofProto().GetSteps() {
		switch st.Step.(type) {
		case *proof.StepProto_Assert:
			asserts++
		case *proof.StepProto_By:
			bys++
		}
	}
	assert.Equal(t, 1, asserts, "one assert per obligation — the shape Go's verb records")
	assert.Equal(t, 1, bys, "and the terminal by")

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: "Build_ZzAddZeroByInduction"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, "ByInduction(StrongInduction,\n", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "At(StrongInduction", "the predicate is the goal's own body and is not spelled\n--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "Case(\n\t\t\t\t\t\t\"case_0: ", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AssertStep(", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "ResidentHyp(", "the obligation is a Case, not a premise\n--- source: ---\n%s", out.Go)
	assert.Contains(t, out.DepNames, "nat_order.StrongInduction")
}

// TestByInduction_Refusals: the principle is an entry named by key, the
// table is a prefix of its stated binders, and the entry is an
// induction principle.
func TestByInduction_Refusals(t *testing.T) {
	for _, row := range []struct {
		name   string
		tactic TacticReq
		want   string
	}{
		{"a text principle", TacticReq{Type: "by_induction", LemmaText: "∀P:(num → bool). P(0) ⇒ ∀n:num. P(n)", TermSpecialize: map[string]string{"P": "Q"}}, "named by key"},
		{"a sparse table", TacticReq{Type: "by_induction", LemmaKey: "nat_order.StrongInduction", TermSpecialize: map[string]string{"n": "0"}}, "PREFIX of the principle's stated binders"},
		{"not a principle", TacticReq{Type: "by_induction", LemmaKey: "nat_order.LessEqTrans", TermSpecialize: map[string]string{"m": "0"}}, "whose head is not a variable"},
		{"arith is by's closer", TacticReq{Type: "by_induction", LemmaKey: "nat_order.StrongInduction", TermSpecialize: map[string]string{"P": "Q"}, Arith: true}, "`by`'s closers"},
	} {
		t.Run(row.name, func(t *testing.T) {
			e, s, gid := byInductionSession(t, "Q:(num → bool) ⊢ ∀n:num. Q(n)")
			res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: gid, Tactic: row.tactic})
			require.NoError(t, err)
			require.False(t, res.Success)
			require.NotEmpty(t, res.Diagnostics)
			assert.Contains(t, res.Diagnostics[0].Message, row.want)
		})
	}
}

// TestByInduction_RuleInductionOverAnInductiveRelation: the door on the
// case it was built for — rule induction along an inductive door's
// relation, the principle parametric in A and grounded at a two-place
// predicate and both indices, with the relation's hypothesis as the
// extra. One leaf opens per rule; each closes by the rule it answers;
// the member emits as the `ByInduction` the chapter writes
// (list.PermutationSym).
func TestByInduction_RuleInductionOverAnInductiveRelation(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, "datatypes/list", nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀l m:list(A). list_permutation(l, m) ⇒ list_permutation(m, l)")
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
	applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "strip_imp"})
	perm := 0
	res := applyOnSoleGoal(t, e, info.ID, TacticReq{
		Type:           "by_induction",
		LemmaKey:       "list.ListPermutationInduct",
		TermSpecialize: map[string]string{"P": "λu:list(A). λv:list(A). list_permutation(v, u)", "x0": "l", "x1": "m"},
		ByHyps:         []ByHypSpec{{HypIndex: &perm}},
	})
	require.Len(t, res.Produced, 4, "one leaf per rule of the relation")
	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 4)
	// The obligations are the rules read at the predicate: the nil rule's
	// is the nil rule itself (the pair read backwards is the same pair).
	nilRule, err := e.resolveLemma(s, TacticReq{Type: "lemma", LemmaKey: "list.PermutationNil"}, state.Goals[0].Statement)
	require.NoError(t, err)
	var nilCase int
	for i, g := range state.Goals {
		if g.Statement.Conclusion().AlphaEquals(nilRule.Conclusion()) {
			nilCase++
			_ = i
		}
	}
	require.Equal(t, 1, nilCase, "one of the open leaves is the nil rule at the predicate")
	// Each case closes by the rule it answers, as the chapter's member
	// does — the rule that closes a leaf is the one its obligation came
	// from, so every rule closes exactly one leaf.
	rules := []string{"list.PermutationNil", "list.PermutationCons", "list.PermutationSwap", "list.PermutationTrans"}
	closedBy := map[string]int{}
	for _, g := range state.Goals {
		closed := false
		for _, rule := range rules {
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: TacticReq{
				Type: "by", WithLemmas: []LemmaWithSpec{{Key: rule}}}})
			require.NoError(t, err)
			if res.Success {
				closedBy[rule]++
				closed = true
				break
			}
		}
		require.True(t, closed, "no rule closes the case %s", prop.PrintProp(g.Statement))
	}
	for _, rule := range rules {
		assert.Equal(t, 1, closedBy[rule], "%s closes exactly one case", rule)
	}
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_ZzPermutationSym"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	t.Logf("--- emitted: ---\n%s", out.Go)
	// The predicate and witnesses fix A at the goal's own letter, so
	// the induction premise retains its explicit identity instance; the
	// predicate is the goal read at the index the permutation fixes, so
	// the cite stops before it.
	assert.Contains(t, unspaced(out.Go), unspaced(`ByInduction(ListPermutationInduct.Inst[A](), `), "--- source: ---\n%s", out.Go)
	assert.NotContains(t, unspaced(out.Go), unspaced(`At(ListPermutationInduct.Inst[A]()`), "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AtTypes(", "--- source: ---\n%s", out.Go)
	assert.Len(t, regexp.MustCompile(`Case\(\s*"case_`).FindAllString(out.Go, -1), 4, "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "AssertStep(", "--- source: ---\n%s", out.Go)
	for _, rule := range []string{"PermutationNil", "PermutationCons", "PermutationSwap", "PermutationTrans"} {
		assert.Contains(t, out.Go, "By("+rule+")", "--- source: ---\n%s", out.Go)
	}
}

// TestByInduction_ThePredicateAloneAtAGuardedPrinciple: a principle
// whose index carries a guard, finite(x0), is cited at its predicate
// alone. The terminal reads the stated form as its telescope at that
// tuple, and the entry certifies that telescope as it certifies the
// stated form, with or without a pin on the type letter.
func TestByInduction_ThePredicateAloneAtAGuardedPrinciple(t *testing.T) {
	for name, pin := range map[string]map[string]string{
		"typed by the predicate": nil,
		"pinned":                 {"A": "num"},
	} {
		t.Run(name, func(t *testing.T) {
			e := newEngine(statedSessionEnv())
			ctx := context.Background()
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			_, err = e.SetSessionFamily(info.ID, "sets/finite_set", nil)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			addTextGoal(t, s, "∀T:set(num). finite(T) ⇒ (∀n:num. n ∈ T ⇒ n = n)")
			applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
			applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "strip_imp"})
			finite := 0
			res := applyOnSoleGoal(t, e, info.ID, TacticReq{
				Type:           "by_induction",
				LemmaKey:       "finite_set.FiniteInduct",
				TypeSpecialize: pin,
				TermSpecialize: map[string]string{"P": "λU:set(num). ∀n:num. n ∈ U ⇒ n = n"},
				ByHyps:         []ByHypSpec{{HypIndex: &finite}},
			})
			require.Len(t, res.Produced, 2, "the empty set and the insertion")
		})
	}
}

// TestByInduction_ThePredicateReadFromTheGoal: a table that stops
// before the predicate — here none at all — has the predicate read
// from the goal. With no hypothesis named, the goal is the principle's
// conclusion and its body is the predicate; with the hypothesis that
// states the principle's guard named under by_hyps, the goal is
// abstracted over the index that hypothesis fixes. Either way the
// leaves are the ones the written table opens.
func TestByInduction_ThePredicateReadFromTheGoal(t *testing.T) {
	t.Run("off the goal's binders", func(t *testing.T) {
		e, s, gid := byInductionSession(t, "Q:(num → bool) ⊢ ∀n:num. Q(n)")
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
			Type:     "by_induction",
			LemmaKey: "nat_order.StrongInduction",
		}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		require.Len(t, state.Goals, 1)
		assert.Equal(t, "∀n.((∀m.((m < n) ⇒ Q(m))) ⇒ Q(n))", ext.PrintTerm(state.Goals[0].Statement.Conclusion()))
	})
	t.Run("at the index a hypothesis fixes", func(t *testing.T) {
		e := newEngine(statedSessionEnv())
		ctx := context.Background()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		_, err = e.SetSessionFamily(info.ID, "sets/finite_set", nil)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		addTextGoal(t, s, "∀T:set(num). finite(T) ⇒ (∀n:num. n ∈ T ⇒ n = n)")
		applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "intro"})
		applyOnSoleGoal(t, e, info.ID, TacticReq{Type: "strip_imp"})
		finite := 0
		res := applyOnSoleGoal(t, e, info.ID, TacticReq{
			Type:     "by_induction",
			LemmaKey: "finite_set.FiniteInduct",
			ByHyps:   []ByHypSpec{{HypIndex: &finite}},
		})
		require.Len(t, res.Produced, 2, "the empty set and the insertion")
		state, err := e.InspectState(ctx, info.ID)
		require.NoError(t, err)
		var atEmpty int
		for _, g := range state.Goals {
			if ext.PrintTerm(g.Statement.Conclusion()) == "∀n₀.((n₀ ∈ ∅) ⇒ (n₀ = n₀))" {
				atEmpty++
			}
		}
		assert.Equal(t, 1, atEmpty, "one leaf is the goal read at the empty set; open: %v", func() (out []string) {
			for _, g := range state.Goals {
				out = append(out, ext.PrintTerm(g.Statement.Conclusion()))
			}
			return
		}())
	})
	t.Run("a goal that fits neither reading is refused", func(t *testing.T) {
		e, s, gid := byInductionSession(t, "Q:(num → bool), k:num ⊢ Q(k)")
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
			Type:     "by_induction",
			LemmaKey: "nat_order.StrongInduction",
		}})
		require.NoError(t, err)
		require.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "fits neither reading")
	})
}
