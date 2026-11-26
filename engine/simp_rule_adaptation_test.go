package engine

// The simp rule set (simp_with_multi_instance.go): a `simp_with` call
// fires its named rules alone, the session's installed definitions
// firing under the bare `simp`; a polymorphic rule adapts to the type
// instances the rewrite itself exposes; and the bare `simp` fires an
// imported definition at an instance other than the chapter's own
// letters. The tests run on the list chapter.

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// simpAdaptationSession creates a session over the served corpus, bound
// to family (unbound when family is ""), with one goal parsed from text
// in the session's constant scope. Returns the engine, the session id,
// the session and the goal id.
func simpAdaptationSession(t *testing.T, family, goalText string) (*Engine, string, *Session, string) {
	t.Helper()
	e := newEngine(servedEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	if family != "" {
		_, err = e.SetSessionFamily(info.ID, family, nil)
		require.NoError(t, err)
	}
	s, _ := e.getSession(info.ID)
	parsed := dsl.ParsePropTextInScope(goalText, &dsl.ParseScope{
		ConstResolver:      envConstResolver(s.env),
		StrictResolution:   true,
		FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "%v", parsed.Errors)
	s.mu.Lock()
	goalID := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	return e, info.ID, s, goalID
}

// openLeavesMentioning counts the session's open leaves whose
// conclusion still mentions one of the named constants.
func openLeavesMentioning(t *testing.T, e *Engine, sid string, names ...core.TermName) int {
	t.Helper()
	stateRes, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	n := 0
	for _, g := range stateRes.Goals {
		for _, name := range names {
			if termContainsConstNamed(g.Statement.Conclusion(), name) {
				t.Logf("open leaf still mentions %s: %s", name, prop.PrintProp(g.Statement))
				n++
				break
			}
		}
	}
	return n
}

// closeResidual closes the one residual leaf a simp step leaves (a
// reflexive equation under its binders) by `auto` and requires the
// section proved.
func closeResidual(t *testing.T, e *Engine, sid string, s *Session, res *StepResult) {
	t.Helper()
	require.Len(t, res.Produced, 1, "the step leaves exactly the rewritten residual: %+v", res.Produced)
	closed, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: res.Produced[0].GoalID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.Equal(t, "close", closed.Effect, "%+v", closed.Diagnostics)
	require.True(t, s.sections[0].root.Proved())
}

// TestSimpWith_AdaptsToInstancesTheRewriteExposes: in a bare session,
// `simp_with [LetterInverseDef, pairs.Fst, pairs.Snd, pairs.PairEta]` on
// `∀x:prod(A, bool). letter_inverse(letter_inverse(x)) = x` — the
// measured free_group.LetterInverseInverse session. The goal carries no
// pair constructor and no projection, so the three pair laws adapt to
// nothing at resolution and would stay at their own letters; the
// definition fires first and exposes `(fst(x), ¬snd(x))` at (A, bool),
// which the re-adaptation against the residual must catch — the agent
// had pinned each pair law with type_specialize by hand.
func TestSimpWith_AdaptsToInstancesTheRewriteExposes(t *testing.T) {
	e, sid, s, goalID := simpAdaptationSession(t, "",
		"∀x:prod(A, bool). letter_inverse(letter_inverse(x)) = x")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{
			{Key: "free_group.letterInverseDef"}, {Key: "pairs.Fst"}, {Key: "pairs.Snd"}, {Key: "pairs.PairEta"},
		}},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "%+v", res.Diagnostics)
	assert.Equal(t, 0, openLeavesMentioning(t, e, sid, "letter_inverse", "fst", "snd"),
		"all four rules fire in the one call: the pair laws at the instance the unfold exposed")
	closeResidual(t, e, sid, s, res)
	exposed := false
	for _, d := range autoTypeInstanceDiags(res) {
		if strings.Contains(d.Message, "the rewrite itself exposed") {
			exposed = true
		}
	}
	assert.True(t, exposed, "the exposed instances are named in the diagnostics: %+v", res.Diagnostics)
}

// TestFamilySession_SimpFiresImportedClauseAtAnotherInstance: a session
// bound to datatypes/list, goal `∀l:list(prod(A, bool)). list_append(nil, l) = l`.
// The installed append clause is stated at list(A); the bare `simp`
// must fire it at list(prod(A, bool)) — measured on the free group's
// left identity, where the bare simp computed the lifts and class
// equality but left `list_append(nil, y)` standing.
func TestFamilySession_SimpFiresImportedClauseAtAnotherInstance(t *testing.T) {
	e, sid, s, goalID := simpAdaptationSession(t, "datatypes/list",
		"∀l:list(prod(A, bool)). list_append(nil, l) = l")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: goalID, Tactic: TacticReq{Type: "simp"}})
	require.NoError(t, err)
	require.True(t, res.Success, "%+v", res.Diagnostics)
	assert.Equal(t, 0, openLeavesMentioning(t, e, sid, "list_append"),
		"the clause fired at the letter instance")
	closeResidual(t, e, sid, s, res)
	emit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: sid, Section: 0, FuncName: "Build_AppendNilAtLetters", Family: "zz_other", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted:\n%s", emit.Go)
	assert.Contains(t, emit.Go, "ListAppendDef", "the adapted copy's child cites the imported definition's entry")
	assert.NotContains(t, emit.Go, "TODO", "no unresolved leaf")
}

// TestFamilySession_SimpWithFiresOnlyItsNamedRules: a session bound to
// datatypes/list, `simp_with [ReverseAppend]` on
// `∀l m:list(num). list_reverse(list_append(l, list_append(m, nil))) =
// list_append(list_reverse(m), list_reverse(l))`. The cited law splits
// both reversals and leaves `list_reverse(nil)` and `list_append(nil, …)`
// standing: the chapter's reverse and append clauses the binding
// installed do not fire in this call, so the residual is the one an
// unbound session leaves and the step renders as the Go
// `Simp(Fwd(ReverseAppend))` it rehearses; the bare `simp` after it
// fires the installed clauses as a second step naming them. Measured
// on tor_ext.ExtMapLeftHom and four siblings, whose authors rehearse a
// Go `Simp(Fwd(<definition>))` and need the session step to unfold
// that definition and nothing the chapter defines beneath it.
func TestFamilySession_SimpWithFiresOnlyItsNamedRules(t *testing.T) {
	const goal = "∀l m:list(num). list_reverse(list_append(l, list_append(m, nil))) = list_append(list_reverse(m), list_reverse(l))"
	ctx := context.Background()
	var residuals []core.Prop
	var (
		e   *Engine
		s   *Session
		sid string
		res *StepResult
	)
	for _, family := range []string{"", "datatypes/list"} {
		var gid string
		e, sid, s, gid = simpAdaptationSession(t, family, goal)
		var err error
		res, err = e.ApplyStep(ctx, sid, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: "list.ReverseAppend"}}},
		})
		require.NoError(t, err)
		require.True(t, res.Success, "%+v", res.Diagnostics)
		state, err := e.InspectState(ctx, sid)
		require.NoError(t, err)
		require.Len(t, state.Goals, 1)
		residuals = append(residuals, state.Goals[0].Statement)
	}
	require.True(t, residuals[0].AlphaEquals(residuals[1]),
		"the named rules must leave the same residual in bound and unbound sessions")
	// The bound session: the installed clauses fire under the bare simp.
	require.Len(t, res.Produced, 1)
	simped, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: res.Produced[0].GoalID, Tactic: TacticReq{Type: "simp"}})
	require.NoError(t, err)
	require.True(t, simped.Success, "%+v", simped.Diagnostics)
	closeResidual(t, e, sid, s, simped)
	emit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: sid, Section: 0, FuncName: "Build_ReverseOfAppendNil", Family: "zz_other", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted:\n%s", emit.Go)
	assert.NotContains(t, emit.Go, "TODO", "no unresolved leaf")
	var namedStep, installedStep string
	for _, line := range strings.Split(emit.Go, "\n") {
		switch {
		case strings.Contains(line, "ReverseAppend"):
			namedStep = line
		case strings.Contains(line, "ListReverseDef"):
			installedStep = line
		}
	}
	require.NotEmpty(t, namedStep, "the named rule's step is rendered")
	require.NotEmpty(t, installedStep, "the installed clauses' step is rendered")
	assert.Contains(t, namedStep, "Simp(Fwd(list.ReverseAppend")
	assert.NotContains(t, namedStep, "Def", "the named rule's step fires only ReverseAppend")
	assert.Contains(t, installedStep, "ListAppendDef", "the installed clauses fire together under the bare simp")
	assert.Less(t, strings.Index(emit.Go, namedStep), strings.Index(emit.Go, installedStep), "the named step comes first")
}

// TestBy_SessionPrefixTupleAtAPrincipleClosesKeyless: the session twin
// of TestBy_PrefixTupleAtAPrincipleIsCompletedFromTheGoal — the agents'
// measured round: `by` with `term_specialize:{P}` alone on
// nat_order.StrongInduction, the obligation resident as the one by_hyp.
// The index k is read off the goal, the stated form's guard is the
// resident obligation, and the leaf closes by one modus ponens with no
// live search (the refuter budget is the replay sentinel, so a close
// that reached it would fail).
func TestBy_SessionPrefixTupleAtAPrincipleClosesKeyless(t *testing.T) {
	e, sid, s, goalID := simpAdaptationSession(t, "",
		"∀Q:(num → bool). ∀k:num. (∀n:num. (∀m:num. m < n ⇒ Q(m)) ⇒ Q(n)) ⇒ Q(k)")
	s.env.CnfRefuterTimeout = 0
	ctx := context.Background()
	for _, typ := range []string{"strip_quant", "strip_imp"} {
		res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err)
		require.True(t, res.Success, "%s: %+v", typ, res.Diagnostics)
		require.Len(t, res.Produced, 1, "strip %s", typ)
		goalID = res.Produced[0].GoalID
	}
	state, err := e.InspectState(ctx, sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	concl := state.Goals[0].Statement.Conclusion()
	app, isApp := concl.Core().(core.AppliedTerm)
	require.True(t, isApp, "the stripped goal is Q(k): %s", prop.PrintProp(state.Goals[0].Statement))
	predicate, isVar := app.Fun().Core().(core.VarTerm)
	require.True(t, isVar, "the head is the fixed predicate: %s", prop.PrintProp(state.Goals[0].Statement))

	obligation := 0
	res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{
		Type:   "by",
		ByHyps: []ByHypSpec{{HypIndex: &obligation}},
		WithLemmas: []LemmaWithSpec{{
			Key:            "nat_order.StrongInduction",
			TermSpecialize: map[string]string{"P": string(predicate.Name())},
		}},
	}})
	require.NoError(t, err)
	require.True(t, res.Success, "%+v", res.Diagnostics)
	require.Equal(t, "close", res.Effect, "%+v", res.Diagnostics)
	require.True(t, s.sections[0].root.Proved())
}

// A compound pin still contains rigid goal letters; it must stay at
// set(B) while the same definition also occurs at set(C).
func TestSimpWith_ExplicitCompoundInstanceKeepsItsLetters(t *testing.T) {
	prefix := "u:list(set(B)), v:list(set(C)), Q:list(set(B))→list(set(C))→bool ⊢ "
	e, sid, s, gid := simpAdaptationSession(t, "", prefix+"Q(list_append(nil, u), list_append(nil, v))")
	out, err := e.ApplyStep(t.Context(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "simp_with", WithLemmas: []LemmaWithSpec{{Key: "list.ListAppendDef", TypeSpecialize: map[string]string{"A": "set(B)"}}},
	}})
	require.NoError(t, err)
	require.True(t, out.Success, "%+v", out.Diagnostics)
	want := dsl.ParsePropTextInScope(prefix+"Q(u, list_append(nil, v))", &dsl.ParseScope{ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true})
	require.Empty(t, want.Errors)
	state, err := e.InspectState(t.Context(), sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	require.True(t, state.Goals[0].Statement.AlphaEquals(want.Prop), "%s", prop.PrintProp(state.Goals[0].Statement))
}
