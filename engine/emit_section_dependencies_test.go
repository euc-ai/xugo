package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func applyInEmitSection(t *testing.T, e *Engine, sid string, section int, tactic TacticReq) {
	t.Helper()
	state, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	var ids []string
	for _, goal := range state.Goals {
		if strings.HasPrefix(goal.ID, fmt.Sprintf("s%d_", section)) {
			ids = append(ids, goal.ID)
		}
	}
	require.Len(t, ids, 1)
	result, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: ids[0], Tactic: tactic})
	require.NoError(t, err)
	require.True(t, result.Success, "%s: %+v", tactic.Type, result.Diagnostics)
}

// proveByArith closes the one-binder section by arithmetic, reading the
// sibling statement cited when it is not empty.
func proveByArith(t *testing.T, e *Engine, sid string, section int, cited string) {
	t.Helper()
	applyInEmitSection(t, e, sid, section, TacticReq{Type: "intro"})
	if cited == "" {
		applyInEmitSection(t, e, sid, section, TacticReq{Type: "arith"})
		return
	}
	applyInEmitSection(t, e, sid, section, TacticReq{Type: "by", Arith: true,
		WithLemmas: []LemmaWithSpec{{Text: cited}}})
}

// TestEmitSection_OrdersHelpersByTheirCites: the target opened first,
// its helpers after it, a section proved but cited by nothing beside
// them. The default takes the sections the target's cites reach and
// orders each after what it cites, whatever their slice order; a list
// in either order gives the same member, and a listed section nothing
// cites is refused.
func TestEmitSection_OrdersHelpersByTheirCites(t *testing.T) {
	e := byArithEngine(t)
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	const one, two = "∀n:num. n ≤ n + 1", "∀m:num. m ≤ m + 2"
	addTextGoal(t, s, "∀k:num. k ≤ k + 3")
	addTextGoal(t, s, one)
	addTextGoal(t, s, two)
	addTextGoal(t, s, "∀p:num. p ≤ p + 0")
	proveByArith(t, e, s.ID, 1, "")
	proveByArith(t, e, s.ID, 2, one)
	proveByArith(t, e, s.ID, 3, "")
	proveByArith(t, e, s.ID, 0, two)

	for _, prior := range [][]int{nil, {1, 2}, {2, 1}} {
		out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0,
			IncludePrior: prior, Family: "nat_num/nat_order"})
		require.NoError(t, err, "include_prior %v", prior)
		require.Equal(t, []int{1, 2, 0}, out.SectionsIncluded, "include_prior %v", prior)
		parsesAsGo(t, out.Go)
		require.NotContains(t, out.Go, "TODO: unresolved lemma")
		require.Contains(t, out.Go, "ByArith(lemma1)")
		require.Contains(t, out.Go, "ByArith(lemma2)")
	}

	_, err = e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0,
		IncludePrior: []int{1, 2, 3}, Family: "nat_num/nat_order"})
	require.ErrorContains(t, err, "sections [3] are cited by no section the target reaches")
}

// TestEmitSection_OrdersSectionsProvedOutOfSliceOrder: a helper opened
// before the helper it cites — proved after it — renders after it under
// the default; the slice order would have it read a later local.
func TestEmitSection_OrdersSectionsProvedOutOfSliceOrder(t *testing.T) {
	e := byArithEngine(t)
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	const one, two = "∀n:num. n ≤ n + 1", "∀m:num. m ≤ m + 2"
	addTextGoal(t, s, two)
	addTextGoal(t, s, one)
	addTextGoal(t, s, "∀k:num. k ≤ k + 3")
	proveByArith(t, e, s.ID, 1, "")
	proveByArith(t, e, s.ID, 0, one)
	proveByArith(t, e, s.ID, 2, two)

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 2, Family: "nat_num/nat_order"})
	require.NoError(t, err)
	require.Equal(t, []int{1, 0, 2}, out.SectionsIncluded)
	parsesAsGo(t, out.Go)
	require.NotContains(t, out.Go, "TODO: unresolved lemma")
}

// TestEmitSection_HelperRestatingAnEntryCitesTheEntry: a helper whose
// proof cites the registered theorem it restates cites the theorem, not
// its own node, and a second helper stating the same theorem is no
// second home for the target's cite.
func TestEmitSection_HelperRestatingAnEntryCitesTheEntry(t *testing.T) {
	e := byArithEngine(t)
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addTextGoal(t, s, "∀S T:set(set(B)). ∀b:bool. b ∧ S ⊆ T ∧ T ⊆ S ⇒ S = T")
	const helper = "∀S T:set(A). S ⊆ T ∧ T ⊆ S ⇒ S = T"
	addTextGoal(t, s, helper)
	applyInEmitSection(t, e, s.ID, 1, TacticReq{Type: "lemma", LemmaKey: "set_order.SubsetAntisym"})
	require.True(t, s.sections[0].root.Proved())
	addTextGoal(t, s, helper)
	applyInEmitSection(t, e, s.ID, 2, TacticReq{Type: "lemma", LemmaKey: "set_order.SubsetAntisym"})

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, Family: "sets/set_order"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	require.Equal(t, []int{1, 0}, out.SectionsIncluded)
	require.NotContains(t, out.Go, "TODO: unresolved lemma")
	require.Contains(t, out.Go, "TypeInst(ctx.TypeInstSourceExact(\n\t\t\t\t\t\t\tlemma1.PromisedThm(),\n")
	lemma := out.Go[strings.Index(out.Go, "lemma1 := ctx.Lemma("):strings.Index(out.Go, "return ctx.Theorem(")]
	require.Contains(t, lemma, "SubsetAntisym")
	require.Equal(t, 1, strings.Count(lemma, "lemma1"), "the helper cites its own node:\n%s", lemma)

	_, err = e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0,
		IncludePrior: []int{1, 2}, Family: "sets/set_order"})
	require.ErrorContains(t, err, "sections [2] are cited by no section the target reaches")
}
