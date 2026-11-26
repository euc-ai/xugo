package engine

// End-to-end glue for the `by` composite through the curate transport:
// session `by` close → DetailedProofProto (one StepProto_By) →
// emit-section → generated-style Go whose close line is the literal
// math-layer By(...) call. This is the contract the tag exists for —
// what the session validated is what the Go says — so the assertion is
// on the rendered TEXT, not just on parse success.

import (
	"context"
	"go/parser"
	"go/token"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestEmitSection_ByCompositeRendersByCall: close
// `(∀x. F(x)), F(a) ⇒ q ⊢ q` with the `by` tactic — the ∀-hyp ground
// at a (witnessed resident premise) plus the implication — emit the
// section, and require the method body to carry ONE `By(…)` close with
// no clear_hyps / CnfRefute expansion lines. The session states the
// closed goal and strips its premises, so each resident premise is the
// closure parameter the stripped premise lifts to. (The goal must NOT
// be propositionally trivial, or emit's trivial-true path renders no
// tactic body at all.)
func TestEmitSection_ByCompositeRendersByCall(t *testing.T) {
	_, F := curateF()
	a := ext.Var("a", TypeInd)
	x := ext.WrapTerm(ext.Var("x", TypeInd))
	q := ext.Var("q", core.TypeBool())
	goalProp := prop.MakeProp(q,
		ext.ForAll(x)(F.Apply(x)).Core(),
		ext.WrapTerm(F.Apply(a).Core()).Imply(q).Core())

	e := newEngine(emitSectionEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	goalID := addStrippedGoal(t, e, info.ID, goalProp)

	// Locate the two hyps (canonically sorted).
	g := s.goalIndex[goalID].node.Goal
	var hAll, hImp int
	for i := 0; i < g.NumHyps(); i++ {
		if strings.Contains(ext.PrintTerm(g.Hyp(i)), "⇒") {
			hImp = i
		} else {
			hAll = i
		}
	}

	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{
			Type: "by",
			ByHyps: []ByHypSpec{
				{HypIndex: &hAll, Terms: []string{"a"}},
				{HypIndex: &hImp},
			},
		},
	})
	require.NoError(t, err)
	require.True(t, res.Success, "by should close F(a), F(a)⇒q ⊢ q; diagnostics: %v", res.Diagnostics)
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID,
		Section:   0,
		FuncName:  "Build_BYGLUE",
		Family:    "real/real_field",
	})
	require.NoError(t, err)
	require.NotEmpty(t, out.Go)

	if _, perr := parser.ParseFile(token.NewFileSet(), "by_glue.go", out.Go, parser.AllErrors); perr != nil {
		t.Fatalf("emitted source does not parse: %v\n--- source: ---\n%s", perr, out.Go)
	}
	assert.Contains(t, out.Go, "By(At(h, ",
		"the by composite must render as the math-layer By call, witnessed premise first\n--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "), h2),",
		"the bare resident premise must render as the parameter that binds it\n--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "ClearHyps(",
		"no expansion ministeps may leak into the rendering\n--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "CnfRefute()",
		"the internal refute is the composite's own — never a rendered line\n--- source: ---\n%s", out.Go)
}

// TestEmitSection_ByWitnessIsItsText: a session `by` that grounds a law
// at a witness that is no variable emits the witness as a term text,
// parsed by the member's Argument and typed by the phantom of its type
// — `a.TermAs[Real]("(m - l) / &2")`, the spelling a chapter writes —
// and not as the Go tower of the term's constructors down to the bits
// of its numeral. A variable witness stays the Go local it is declared
// as.
func TestEmitSection_ByWitnessIsItsText(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	const law = "real_order_ring.LessEqRefl"
	by := func(witness string) TacticReq {
		return TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: law, TermSpecialize: map[string]string{"x": witness}}}}
	}

	t.Run("a compound witness", func(t *testing.T) {
		src := emitReading(t, e, "real/real_order_ring", "l:real, m:real ⊢ (m - l) / &2 ≤ (m - l) / &2", nil, by("(m - l) / &2"))
		assert.Contains(t, src, `By(At(LessEqRefl, a.TermAs[Real]("(m - l) / &2")))`, "--- source: ---\n%s", src)
		assert.NotContains(t, strings.ToUpper(src), "BIT", "the numeral's tower is not spelled\n--- source: ---\n%s", src)
		assert.NotContains(t, src, ".Apply(", "no Go term expression is left\n--- source: ---\n%s", src)
		assert.NotContains(t, src, " := ctx.", "the text binds no local\n--- source: ---\n%s", src)
		assert.NotContains(t, src, "TODO", "--- source: ---\n%s", src)
	})
	t.Run("a variable", func(t *testing.T) {
		src := emitReading(t, e, "real/real_order_ring", "m:real ⊢ m ≤ m", nil, by("m"))
		assert.Contains(t, src, `By(At(LessEqRefl, m))`, "--- source: ---\n%s", src)
		assert.NotContains(t, src, "TermAs[", "--- source: ---\n%s", src)
	})
}

// TestEmitSection_HavePremiseIsItsHandle: a session that asserts two
// facts in a row and cites them from later `by` steps emits the Have
// chain with each cited fact bound, and the later premise lists name
// the facts by those handles — `By(At(fact1, c))` for a fact grounded
// at a witness, `fact2` for one cited as it stands — where a
// hypothesis no Have of the chain states is the closure parameter its
// stripped premise lifts to.
func TestEmitSection_HavePremiseIsItsHandle(t *testing.T) {
	num := dsl.NumType
	predicate := func(name string) *ext.TermWrapper {
		return ext.WrapTerm(ext.Var(core.TermName(name), core.MakeFun(num, core.TypeBool())))
	}
	P, Q, R := predicate("P"), predicate("Q"), predicate("R")
	x := ext.Var("x", num)
	c := ext.Var("c", num)
	everyPIsQ := ext.ForAll(x)(P.Apply(x).Imply(Q.Apply(x).Core())).Core()
	everyP := ext.ForAll(x)(P.Apply(x)).Core()
	everyQIsR := ext.ForAll(x)(Q.Apply(x).Imply(R.Apply(x).Core())).Core()

	e := newEngine(emitSectionEnv(t))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	addStrippedGoal(t, e, info.ID, prop.MakeProp(R.Apply(c).Core(), everyPIsQ, everyP, everyQIsR))

	// openGoalWith is the open goal with that many hypotheses: an
	// assert's claim branch carries one fewer than its continuation.
	openGoalWith := func(hyps int) *GoalView {
		t.Helper()
		state, err := e.InspectState(ctx, info.ID)
		require.NoError(t, err)
		for i := range state.Goals {
			if state.Goals[i].Statement.NumHyps() == hyps {
				return &state.Goals[i]
			}
		}
		t.Fatalf("no open goal with %d hypotheses", hyps)
		return nil
	}
	apply := func(hyps int, tactic TacticReq) {
		t.Helper()
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: openGoalWith(hyps).ID, Tactic: tactic})
		require.NoError(t, err)
		require.True(t, res.Success, "%s failed; diagnostics: %v", tactic.Type, res.Diagnostics)
	}
	// hyp is the index, in the open goal with that many hypotheses, of
	// the hypothesis that prints as printed.
	hyp := func(hyps int, printed string) *int {
		t.Helper()
		goal := openGoalWith(hyps).Statement
		for i := 0; i < goal.NumHyps(); i++ {
			if ext.PrintTerm(goal.Hyp(i)) == printed {
				return &i
			}
		}
		t.Fatalf("no hypothesis prints as %s in %s", printed, prop.PrintProp(goal))
		return nil
	}
	everyQ := ext.PrintTerm(ext.ForAll(x)(Q.Apply(x)).Core())
	qAtC := ext.PrintTerm(Q.Apply(c).Core())

	apply(3, TacticReq{Type: "assert", ClaimText: "∀x:num. Q(x)"})
	apply(3, TacticReq{Type: "auto"})
	apply(4, TacticReq{Type: "assert", ClaimText: "Q(c)"})
	apply(4, TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: hyp(4, everyQ), Terms: []string{"c"}}}})
	apply(5, TacticReq{Type: "by", ByHyps: []ByHypSpec{
		{HypIndex: hyp(5, qAtC)},
		{HypIndex: hyp(5, ext.PrintTerm(everyQIsR)), Terms: []string{"c"}},
	}})
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_HavePremise", Family: "real/real_field"})
	require.NoError(t, err)
	if _, perr := parser.ParseFile(token.NewFileSet(), "have_premise.go", out.Go, parser.AllErrors); perr != nil {
		t.Fatalf("emitted source does not parse: %v\n--- source: ---\n%s", perr, out.Go)
	}
	assert.Contains(t, out.Go, "fact1 := a.Have(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "fact2 := a.Have(", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "By(At(fact1, c)),", "the second Have cites the first at its witness\n--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "By(fact2, At(h3, c)),", "the Show cites the second Have and the hypothesis no Have states\n--- source: ---\n%s", out.Go)
	assert.Equal(t, 0, strings.Count(out.Go, "ResidentHyp("), "every hypothesis is a Have or a parameter, none a text\n--- source: ---\n%s", out.Go)
}
