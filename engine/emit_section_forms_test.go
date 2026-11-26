package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/xugofmt"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// The chapter forms emit-section renders a section in, where the
// recorded tree has the shape the form records: each test proves a
// statement in a session the way a chapter's member is landed, and
// reads the emitted Go for the chapter's spelling.

// boundSession opens a session bound to family.
func boundSession(t *testing.T, family string) (*Engine, *Session) {
	t.Helper()
	e := newEngine(statedSessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, family, nil)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	return e, s
}

// hyp names a resident premise of a session `by` by its index.
func hyp(i int) ByHypSpec { return ByHypSpec{HypIndex: &i} }

// emitSole renders section 0 of s and checks it parses and is in
// xugo_fmt's layout.
func emitSole(t *testing.T, e *Engine, s *Session, funcName string) string {
	t.Helper()
	require.True(t, s.sections[0].root.Proved())
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: funcName})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	formatted, err := xugofmt.Source([]byte(out.Go))
	require.NoError(t, err)
	assert.Equal(t, string(formatted), out.Go, "the emitted member is not in xugo_fmt's layout")
	return out.Go
}

// TestEmitSection_OneRewriteThenACloseIsAnOpening: a section whose root
// unfolds one definition and whose unfolded goal one action closes is
// the member's statement read through that definition — the chapter
// writes it `Opening(Unfold(…), <close>)`, no closure (set_product.InCross
// is landed so).
func TestEmitSection_OneRewriteThenACloseIsAnOpening(t *testing.T) {
	e, s := boundSession(t, "sets/set_product")
	addTextGoal(t, s, "∀s:set(A). ∀t:set(B). ∀x:A. ∀y:B. (x, y) ∈ set_cross(s, t) ⇒ x ∈ s")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "def_expand", Const: "set_cross"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, WithLemmas: []LemmaWithSpec{{Key: "pairs.PairEq"}}})
	src := emitSole(t, e, s, "Build_ZzCrossFirst")
	assert.Contains(t, src, "\t\tOpening(Unfold(SetCrossDef), BySets(pairs.PairEq))),\n", "--- source: ---\n%s", src)
	for _, banned := range []string{"func(a *Argument)", "a.Do("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
}

// TestEmitSection_AnInductionAfterHavesIsTheVerb: a block that states
// two facts and then proves its goal by an induction on a cited
// principle renders the facts as Haves and the induction as the verb —
// `Show(…, ByInduction(<principle>, Case, Case))`, the principle cited
// before its predicate because the predicate the table wrote is the
// goal's own body — not as two more Haves and a By over the principle.
func TestEmitSection_AnInductionAfterHavesIsTheVerb(t *testing.T) {
	e, s := boundSession(t, "nat_num/nat_arith")
	addTextGoal(t, s, "∀g h:(num → num). (∀k:num. g(k) = k) ∧ (∀k:num. h(k) = k) ⇒ ∀n:num. g(n) + 0 = h(n)")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	conj := []ByHypSpec{hyp(0)}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "∀k:num. g₀(k) = k"})
	applyOnGoalProving(t, e, s, "∀k.(g₀(k) = k)", TacticReq{Type: "by", ByHyps: conj})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "∀k:num. h₀(k) = k"})
	applyOnGoalProving(t, e, s, "∀k.(h₀(k) = k)", TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(1)}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by_induction", LemmaKey: "peano.Induction",
		TermSpecialize: map[string]string{"P": "λn:num. g₀(n) + 0 = h₀(n)"}})
	facts := []ByHypSpec{hyp(0), hyp(1)}
	for range 2 {
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		require.NotEmpty(t, state.Goals)
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID,
			Tactic: TacticReq{Type: "by", ByHyps: facts, WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddZero"}}}})
		require.NoError(t, err)
		require.True(t, res.Success, "obligation: %v", res.Diagnostics)
	}
	src := emitSole(t, e, s, "Build_ZzInductAfterHaves")
	for _, want := range []string{
		"fact1 := a.Have(", "fact2 := a.Have(",
		"a.Show(\n\t\t\t\t\"∀n₀. g(n₀) + 0 = h(n₀)\",\n\t\t\t\tByInduction(peano.Induction,\n",
		"Case(\n\t\t\t\t\t\t\"case_0: g(0) + 0 = h(0)\",",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	assert.NotContains(t, src, "fact3 :=", "the obligations are the verb's cases, not Haves\n--- source: ---\n%s", src)
}

// TestEmitSection_AnAssertedExistentialOpenedAtOnceIsAnObtain: an ∃
// asserted and opened by `strip_quant {hyp_index}` at once is one
// Obtain, and the block's facts after it stay Haves — not an AssertStep
// fan with a positional StripQuantAt on its continuation.
func TestEmitSection_AnAssertedExistentialOpenedAtOnceIsAnObtain(t *testing.T) {
	e, s := boundSession(t, "nat_num/nat_arith")
	addTextGoal(t, s, "∀f:(num → num). ∀P:bool. (∀n:num. ∃m:num. f(m) = n) ⇒ (∀m:num. f(m) + 0 = 0 ⇒ P) ⇒ P")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "∃m:num. f₀(m) = 0"})
	applyOnGoalProving(t, e, s, "∃m.(f₀(m) = 0)", TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0)}})
	two := 2
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant", HypIndex: &two})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "f₀(m₀) + 0 = 0"})
	applyOnGoalProving(t, e, s, "(f₀(m₀) + 0) = 0", TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(2)}, WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddZero"}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(1), hyp(3)}})
	src := emitSole(t, e, s, "Build_ZzObtainThenHave")
	for _, want := range []string{
		"_, fact1 := a.Obtain(\n\t\t\t\t\"∃m. f(m) = 0\",\n\t\t\t\t\"∃m:num. f(m) = 0\",",
		":= a.Have(\n\t\t\t\t\"f(m₀) + 0 = 0\",\n\t\t\t\t\"f(m₀) + 0 = 0\",",
		"a.Show(\n\t\t\t\t\"P\",",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"StripQuantAt(", "AssertStep("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
}

// TestEmitSection_AnObtainOpensItsWholePrefix: the strip after an
// asserted ∃ opens the claim's whole ∃-prefix, so the Obtain it renders
// as is the verb of that many witnesses, its instance bound after as
// many blanks. A prefix no verb opens stays an assert and its strip.
// (The block's receiver letter skips the statement's binders, so the
// verb is read without it.)
func TestEmitSection_AnObtainOpensItsWholePrefix(t *testing.T) {
	for _, tc := range []struct {
		binders    []string
		bind, verb string // "" when no Obtain verb opens the prefix
	}{
		{[]string{"a", "b"}, "\t_, _, fact1 := ", ".Obtain2(\n"},
		{[]string{"a", "b", "c"}, "\t_, _, _, fact1 := ", ".Obtain3(\n"},
		{[]string{"a", "b", "c", "d"}, "\t_, _, _, _, fact1 := ", ".Obtain4(\n"},
		{[]string{"a", "b", "c", "d", "e"}, "\t_, _, _, _, _, fact1 := ", ".Obtain5(\n"},
		{[]string{"a", "b", "c", "d", "e", "f"}, "", ""},
	} {
		t.Run(strings.Join(tc.binders, ""), func(t *testing.T) {
			e, s := boundSession(t, "nat_num/nat_arith")
			relation := strings.Repeat("num → ", len(tc.binders)) + "bool"
			zeros := strings.TrimSuffix(strings.Repeat("0, ", len(tc.binders)), ", ")
			args := strings.Join(tc.binders, ", ")
			addTextGoal(t, s, "∀R:("+relation+"). ∀P:bool. R("+zeros+") ⇒ (∀"+strings.Join(tc.binders, " ")+":num. R("+args+") ⇒ P) ⇒ P")
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "∃" + strings.Join(tc.binders, " ") + ":num. R₀(" + args + ")"})
			ctx := context.Background()
			state, err := e.InspectState(ctx, s.ID)
			require.NoError(t, err)
			claimGoal := ""
			for _, g := range state.Goals {
				if !ext.MatchesEXISTS(g.Statement.Conclusion()).IsZero() {
					claimGoal = g.ID
				}
			}
			require.NotEmpty(t, claimGoal, "the asserted ∃ is an open goal")
			res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: claimGoal,
				Tactic: TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0), hyp(1)}}})
			require.NoError(t, err)
			require.True(t, res.Success, "claim: %v", res.Diagnostics)
			state, err = e.InspectState(ctx, s.ID)
			require.NoError(t, err)
			require.Len(t, state.Goals, 1)
			opened := -1
			for i := range state.Goals[0].Statement.NumHyps() {
				if !ext.MatchesEXISTS(state.Goals[0].Statement.Hyp(i)).IsZero() {
					opened = i
				}
			}
			require.GreaterOrEqual(t, opened, 0, "the asserted ∃ joins the hyps")
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant", HypIndex: &opened})
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(0), hyp(1), hyp(2)}})
			src := emitSole(t, e, s, "Build_ZzObtainPrefix")
			if tc.verb == "" {
				assert.NotContains(t, src, ".Obtain", "--- source: ---\n%s", src)
				assert.Contains(t, src, "StripQuantAt(", "--- source: ---\n%s", src)
				return
			}
			assert.Contains(t, src, tc.bind, "--- source: ---\n%s", src)
			assert.Contains(t, src, tc.verb, "--- source: ---\n%s", src)
			assert.NotContains(t, src, "StripQuantAt(", "--- source: ---\n%s", src)
		})
	}
}

// TestEmitSection_TheHeadlineSpellsSetsAndNoTieItsArgumentsFix: a
// headline over sets prints its set binders `set(τ)` and a constant the
// statement holds at several instances without the ties its arguments
// already fix — the text a chapter writes, of the statement's own key.
// The typed statement served for a member reads the same way.
func TestEmitSection_TheHeadlineSpellsSetsAndNoTieItsArgumentsFix(t *testing.T) {
	e, s := boundSession(t, "sets/set_product")
	addTextGoal(t, s, "∀s:set(A). ∀t:set(B). finite(s) ∧ finite(t) ⇒ finite(set_cross(s, t)) ∨ s = ∅")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{Key: "finite_set.FiniteProduct"}}})
	src := emitSole(t, e, s, "Build_ZzFiniteCrossOrEmpty")
	assert.Equal(t, "∀s:set(A). ∀t:set(B). finite(s) ∧ finite(t) ⇒ finite(set_cross(s, t)) ∨ s = ∅", headlineOf(t, src))

	witt, ok := registry.ByName("order.BourbakiWitt")
	require.True(t, ok)
	typed, ok := FormatStatementTypedUnder(witt.Statement().Prop, witt.Family())
	require.True(t, ok)
	assert.Equal(t, "∀f:(set(A) → set(A)). ∀P:(set(A) → bool). (∀s:set(A). s ⊆ f(s)) ∧ (∀s:set(A). P(s) ⇒ P(f(s))) ∧ "+
		"(∀F:set(set(A)). (∀s:set(A). s ∈ F ⇒ P(s)) ∧ (∀s t:set(A). s ∈ F ∧ t ∈ F ⇒ s ⊆ t ∨ t ⊆ s) ⇒ P(⋃F)) ⇒ "+
		"∃s:set(A). P(s) ∧ f(s) = s", typed, "the served typed statement is the chapter's headline")
}

// TestEmitSection_AStructureLawIsTheLawDoor: a statement that reads
// `∀<components>. <structure>(<components>) ⇒ <body>`, whose proof
// strips the components and the hypothesis first, is a law of the
// structure — `<Structure>.Law(<body>, func(a *Argument, h Fact, …) {…})`,
// the body in parts where it has a premise, the hypothesis the closure's
// Fact wherever the proof reads it and the body's own leading binders
// the closure's further parameters.
func TestEmitSection_AStructureLawIsTheLawDoor(t *testing.T) {
	e, s := boundSession(t, "simplicial/quasi_category")
	addTextGoal(t, s, "∀X:simplicial_ops(A). quasi_category(X) ⇒ ∀f:A. f ∈ simplicial_simplices(X, 1) ⇒ simplicial_set(X)")
	for _, step := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: step})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{
		{Key: "quasi_category.QuasiSimplicialSet", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "quasi_category(")}}}})
	src := emitSole(t, e, s, "Build_ZzQuasiSimplicial")
	for _, want := range []string{
		"\tBuild: QuasiCategory.Law(Statement{\n\t\tBinders: \"∀f:A.\",\n\t\tHypotheses: []string{\n\t\t\t\"f ∈ X.simplices(1)\",\n\t\t},\n\t\tConclusion: \"simplicial_set(X)\",\n\t},\n\t\tfunc(a *Argument, h Fact, f *Expr[A], _ Fact) {\n",
		"By(QuasiSimplicialSet.Read(h)),",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"family.Theorem(", "ResidentHyp("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
}

// TestEmitSection_AParametricInstanceIsTheInstanceDoor: an instance
// stated under a ∀-prefix, proved by stripping the prefix, unfolding the
// predicate and closing one branch per conjunct, renders through the
// Instance door with the statement as written — the door binds the
// prefix itself (topological_space.Discrete is landed so).
func TestEmitSection_AParametricInstanceIsTheInstanceDoor(t *testing.T) {
	e, s := boundSession(t, "topology/topological_space")
	addTextGoal(t, s, "∀X:set(A). is_topology({t:set(A) | t ⊆ X})")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "def_expand", Const: "is_topology"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "split_conj"})
	for range 2 {
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID,
			Tactic: TacticReq{Type: "by", Settac: true}})
		require.NoError(t, err)
		require.True(t, res.Success, "branch: %v", res.Diagnostics)
	}
	src := emitSole(t, e, s, "Build_ZzDiscrete")
	assert.Contains(t, src, "\tBuild: family.Instance(IsTopology, \"∀X:set(A). is_topology({t:set(A) | t ⊆ X})\",\n", "--- source: ---\n%s", src)
	assert.Equal(t, 2, strings.Count(src, "BySets()"), "--- source: ---\n%s", src)
	for _, banned := range []string{"family.Theorem(", "StripQuant(", "Unfold(IsTopology)", "SplitConj"} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
}

// TestEmitSection_AConstantAtAnInstanceHoldingTheStatementsLetter: a
// headline whose `∘` stands at an instance containing the statement's
// own letter reads back — emit's read-back scope reads a constant's
// letters as the constant's own, as the session's doors and the Script
// a landed member runs in read them (FreshenMetaLetters).
func TestEmitSection_AConstantAtAnInstanceHoldingTheStatementsLetter(t *testing.T) {
	e, s := boundSession(t, "sets/functions")
	addTextGoal(t, s, "∀f g h:((num → A) → (num → A)). f ∘ (g ∘ h) = (f ∘ g) ∘ h")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "lean_rw", LemmaKey: "functions.ComposeAssoc"})
	src := emitSole(t, e, s, "Build_ZzComposeAssocAtSequences")
	assert.Equal(t, "∀f g h:((num → A) → num → A). f ∘ g ∘ h = (f ∘ g) ∘ h", headlineOf(t, src), "∘ associates to the right")
}
