package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// The surface a rendered body keeps when a session's proof leaves a
// hypothesis no Go value names, splits on a term, or binds a bundle:
// what emit-section rendered as a wall of kernel-level declarations
// — `comprehension_spec := ctx.Const(…)`, `ctx.Var("F_0", …)`, a
// `ResidentHyp` in the unfolded kernel form with generated binder
// names, a case split over Go-built terms — on
// determinant.MultilinearColumnExpansion and
// determinant.MultilinearMapExpansion, and renders in the chapter's
// Go now.

// applyOnGoalHolding applies a tactic to the one open goal with a
// hypothesis printing as text, the premises named by their index in it.
func applyOnGoalHolding(t *testing.T, e *Engine, s *Session, text string, tactic func(index int) TacticReq) {
	t.Helper()
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	for _, g := range state.Goals {
		for i := range g.Statement.NumHyps() {
			if ext.PrintTerm(g.Statement.Hyp(i)) != text {
				continue
			}
			res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: g.ID, Tactic: tactic(i)})
			require.NoError(t, err)
			require.True(t, res.Success, "on the goal holding %s; diagnostics: %v", text, res.Diagnostics)
			return
		}
	}
	t.Fatalf("no open goal holds %s", text)
}

// TestEmitSection_AHypothesisWithoutAHandleIsItsSurfaceText: a case
// split's two hypotheses — a membership in a set-builder over
// functions and its negation — are premises no Go value names. Each
// renders as `ResidentHyp(ctx.MakePropText("…"))` in the chapter's
// surface form (the set-builder sugar, the bound binders' minted
// names), not the kernel's `set_comprehension(λGEN%PVAR%0…)`; the
// split is on the text the Argument reads, `a.TermAs[Bool]("…").Core()`;
// and the constants the texts spell, which the family's scope serves
// at every instance, get no `ctx.Const` line and no scope override.
func TestEmitSection_AHypothesisWithoutAHandleIsItsSurfaceText(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	const statement = "∀n:num. ∀g:(num → num). g ∈ {f:num → num | ∀j:num. f(j) < n} ⇒ 0 ∈ {m:num | m < n} ⇒ g(0) < n"
	addDoorGoal(t, s, statement)
	for _, step := range []string{"strip_quant", "strip_imp", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "case_split", Const: "g₀ ∈ {f:num → num | f(0) < n₀}"})
	applyOnGoalHolding(t, e, s, "g₀ ∈ {f | f(0) < n₀}", func(i int) TacticReq {
		return TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(i)}}
	})
	applyOnGoalHolding(t, e, s, "g₀ ∉ {f | f(0) < n₀}", func(i int) TacticReq {
		all := hypHolding(t, e, s, holds("g₀(0) < n₀"), "∀j₀")
		return TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(i), hyp(all)}}
	})
	out := emitSoleResult(t, e, s, "Build_ZzSetBuilderCaseProbe")
	src := out.Go
	assert.Equal(t, "∀n:num. ∀g:(num → num). g ∈ {f:num → num | ∀j:num. f(j) < n} ∧ 0 ∈ {m:num | m < n} ⇒ g(0) < n", headlineOf(t, src), "--- source: ---\n%s", src)
	for _, want := range []string{
		"\t\tfunc(a *Argument, n *Expr[Nat], g *Arrow[Nat, Nat], h, _ Fact) {\n",
		"ByCaseStep(a.TermAs[Bool](\"g ∈ {f:num → num | f(0) < n}\").Core(),\n",
		"By(ResidentHyp(ctx.MakePropText(\"g₀ ∈ {f:num → num | f(0) < n₀}\"))),\n",
		"By(ResidentHyp(ctx.MakePropText(\"g₀ ∉ {f:num → num | f(0) < n₀}\")), h),\n",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"GEN%PVAR", "ctx.Const(", "ctx.Var(", "set_comprehension", "comprehension_spec", "MakeProp("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "sets/set_order", "ZzSetBuilderCaseProbe", out)
}

// TestEmitSection_ABundleBinderLiftsPastAVariableOfItsName: a
// statement binding its ring as `∀c:comm_ring_on(A).` and, inside,
// another variable named c at another type (here a bound `∀c:num`;
// in MultilinearColumnExpansion a cited lemma's `c:set(C)`). The
// symbol walk registers both and may hand the Go identifier `c` to the
// other; the lift still binds the bundle as `c comm_ring.CommRingFact[on.C]`
// and the body renders from the first step after the strips, the
// component spelled as the text the Argument reads where a cite
// grounds a term at it (`a.TermAs[RingOps[A]]("c")`).
func TestEmitSection_ABundleBinderLiftsPastAVariableOfItsName(t *testing.T) {
	e, s := boundSession(t, "vector/determinant")
	const statement = "∀c:comm_ring_on(A). ∀n:num. (∀c:num. c < n ⇒ c ≤ n) ⇒ module_on(c, free_module_record(c, {i:num | i < n}))"
	addDoorGoal(t, s, statement)
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	ring := hypHolding(t, e, s, every, "comm_ring_on(")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(ring)}, WithLemmas: []LemmaWithSpec{
		{Key: "free_module.FreeModuleOn", TermSpecialize: map[string]string{"R": "c₀", "S": "{i:num | i < n₀}"}},
	}})
	out := emitSoleResult(t, e, s, "Build_ZzBundlePastAVariableProbe")
	src := out.Go
	for _, want := range []string{
		"\t\tfunc(a *Argument, c comm_ring.CommRingFact[on.C], n *Expr[Nat], _ Fact) {\n",
		"a.TermAs[RingOps[A]](\"c\")",
		"a.TermAs[Set[Nat]](\"{i:num | i < n}\")",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"StripQuant()", "StripImp()", "ctx.Var(", "c_0", "ResidentHyp("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
	replayEmittedInFamily(t, "vector/determinant", "ZzBundlePastAVariableProbe", out)
}

// TestEmitSection_SectionsDeclareEveryIncludedSectionsTable: a session
// reads each section's text under the tables of all its sections, so
// a later section spells an earlier one's names with no table of its
// own. The member the two render as declares the union: the headline
// in parts with the entries, the lemma's text spelling them.
func TestEmitSection_SectionsDeclareEveryIncludedSectionsTable(t *testing.T) {
	e, s := boundSession(t, "sets/set_order")
	table, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "S", Text: "{m:num | m < n}"}})
	require.NoError(t, err)
	scope := s.StatementDoorScope()
	scope.Abbreviations = table
	scope.AbbreviationBinders = map[string]bool{"n": true}
	state := func(text string, own *dsl.AbbreviationTable) {
		parsed := dsl.ParsePropTextInScope(text, scope)
		require.Empty(t, parsed.Errors, "goal %q", text)
		_, err = s.AddGoalWith(parsed.Prop, own)
		require.NoError(t, err)
	}
	state("∀n:num. «S» ⊆ «S»", table)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "set_order.SubsetRefl"}}})
	state("∀n:num. «S» ⊆ «S» ∧ «S» ⊆ «S»", nil)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	// Each conjunct closes by the law, where the proved sibling has
	// not closed it already (auto-match).
	for !s.sections[1].root.Proved() {
		st, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		require.NotEmpty(t, st.Goals)
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: st.Goals[0].ID,
			Tactic: TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "set_order.SubsetRefl"}}}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	}
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 1, IncludePrior: []int{0}, FuncName: "Build_ZzSectionsTableProbe"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	src := out.Go
	for _, want := range []string{
		"family.Sections(Statement{\n",
		"\t\tConclusion: \"«S» ⊆ «S» ∧ «S» ⊆ «S»\",\n",
		"\t\t\t{Name: \"S\", Text: \"{m:num | m < n}\"},\n",
		"ctx.Lemma(\"∀n:num. «S» ⊆ «S»\",\n",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	assert.False(t, strings.Contains(src, "{m:num | m < n} ⊆"), "the texts spell the entry\n--- source: ---\n%s", src)
	replayEmittedInFamily(t, "sets/set_order", "ZzSectionsTableProbe", out)
}
