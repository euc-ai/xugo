package engine

import (
	"context"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
)

// residentRuleLeaf is a guarded pointwise equation resident beside the
// point's membership: the rule `{hyp_index}` rewrites F(a) to z.
const residentRuleLeaf = "t:(num → bool), F:(num → num), P:(num → bool), z:num, a:num ⊢ " +
	"(∀y:num. y ∈ t ⇒ F(y) = z) ⇒ a ∈ t ⇒ P(z) ⇒ P(F(a))"

// residentRuleHypIndex is the index of the goal's hypothesis whose printed form
// contains text.
func residentRuleHypIndex(t *testing.T, e *Engine, sid, gid, text string) int {
	t.Helper()
	state, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	for _, g := range state.Goals {
		if g.ID != gid {
			continue
		}
		for i := 0; i < g.Statement.NumHyps(); i++ {
			if strings.Contains(ext.PrintTerm(g.Statement.Hyp(i)), text) {
				return i
			}
		}
	}
	t.Fatalf("no hypothesis of %s prints %q", gid, text)
	return -1
}

// A resident guarded equation is a simp_with rule by its index: it
// rewrites where its guard is resident, its child closes on the
// hypothesis (nothing auto-matched), and the residual is the session's.
func TestSimpWith_ResidentRuleRewritesUnderItsGuard(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	sid, gid := bareArithLeaf(t, e, residentRuleLeaf, "strip_imp", "strip_imp", "strip_imp")
	rule := residentRuleHypIndex(t, e, sid, gid, "∀y")
	out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &rule}},
	}})
	require.NoError(t, err)
	require.True(t, out.Success, "diagnostics: %+v", out.Diagnostics)
	require.Empty(t, out.AutoMatched, "the rule's child closes on its hypothesis, never on an entry")
	state, err := e.InspectState(ctx, sid)
	require.NoError(t, err)
	require.Equal(t, 1, state.NumOpen, "the residual alone")
	require.Contains(t, ext.PrintTerm(state.Goals[0].Statement.Conclusion()), "P(z")
}

// Without the guard resident nothing fires, and the session is left as
// it was: a guard is discharged where the context supplies it.
func TestSimpWith_ResidentRuleNeedsItsGuard(t *testing.T) {
	e := newEngine(testEnv())
	sid, gid := bareArithLeaf(t, e,
		"t:(num → bool), F:(num → num), P:(num → bool), z:num, a:num ⊢ (∀y:num. y ∈ t ⇒ F(y) = z) ⇒ P(z) ⇒ P(F(a))",
		"strip_imp", "strip_imp")
	rule := residentRuleHypIndex(t, e, sid, gid, "∀y")
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &rule}},
	}})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.Contains(t, refusal(out), "made no progress")
}

// A rule whose right side holds an instance of its left is refused as a
// rewrite. The refusal names it where its left side matches; where it
// matches nothing the no-progress message stands alone.
func TestSimpWith_NamesASelfEmbeddingRuleWhereItMatches(t *testing.T) {
	refusalAt := func(conclusion string) string {
		e := newEngine(testEnv())
		sid, gid := bareArithLeaf(t, e,
			"R:(num → num → bool), Q:(num → bool), a:num, b:num ⊢ (∀x:num. R(x, a) ⇔ ∃y:num. R(y, a) ∧ Q(x)) ⇒ "+conclusion,
			"strip_imp")
		rule := residentRuleHypIndex(t, e, sid, gid, "∀x")
		out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
			Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &rule}},
		}})
		require.NoError(t, err)
		require.False(t, out.Success)
		return refusal(out)
	}
	named := refusalAt("R(b, a)")
	require.Contains(t, named, "made no progress")
	require.Contains(t, named, "Refused as a rewrite")
	plain := refusalAt("Q(b)")
	require.Contains(t, plain, "made no progress")
	require.NotContains(t, plain, "Refused as a rewrite")
}

// refusal is the message a step that did not apply reports.
func refusal(out *StepResult) string {
	var b strings.Builder
	for _, d := range out.Diagnostics {
		b.WriteString(d.Message)
	}
	return b.String()
}

// A resident ∀-equation rewrites under a binder, where no ground
// instance reaches.
func TestSimpWith_ResidentRuleUnderABinder(t *testing.T) {
	e := newEngine(testEnv())
	sid, gid := bareArithLeaf(t, e,
		"f:(num → num), g:(num → num), Q:((num → num) → bool) ⊢ (∀n:num. f(n) = g(n + 1)) ⇒ Q(λn. g(n + 1)) ⇒ Q(λn. f(n))",
		"strip_imp", "strip_imp")
	rule := residentRuleHypIndex(t, e, sid, gid, "∀n")
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &rule}},
	}})
	require.NoError(t, err)
	require.True(t, out.Success, "diagnostics: %+v", out.Diagnostics)
}

// hyp_index is a rule by itself, of simp_with alone: beside a key, on a
// `by` or `auto_with` entry, under simp_all, and as its own target it
// is refused by name.
func TestSimpWith_ResidentRuleRefusals(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	sid, gid := bareArithLeaf(t, e, residentRuleLeaf, "strip_imp", "strip_imp", "strip_imp")
	rule := residentRuleHypIndex(t, e, sid, gid, "∀y")
	for name, tc := range map[string]struct {
		tactic TacticReq
		want   string
	}{
		"beside a key": {TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &rule, Key: "set_basic.InUniv"}}},
			"no key, text or read_at"},
		"by": {TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{{HypIndex: &rule}}}, "by_hyps"},
		"auto_with": {TacticReq{Type: "auto_with", WithLemmas: []LemmaWithSpec{{HypIndex: &rule}}},
			"in context already"},
		"simp_all": {TacticReq{Type: "simp_all", WithLemmas: []LemmaWithSpec{{HypIndex: &rule}}},
			"simp_all rewrites every hypothesis"},
		"its own target": {TacticReq{Type: "simp_with", HypIndex: &rule, WithLemmas: []LemmaWithSpec{{HypIndex: &rule}}},
			"does not rewrite itself"},
	} {
		out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid, Tactic: tc.tactic})
		require.NoError(t, err, name)
		require.False(t, out.Success, name)
		assert.Contains(t, refusal(out), tc.want, name)
	}
}

// emit-section renders a resident rule as the fact naming the
// hypothesis — here the closure parameter the lifted strip binds — and
// the section's re-run fires the same rule.
func TestEmitSection_ResidentRuleRendersAsTheFact(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, residentRuleLeaf, "strip_imp", "strip_imp", "strip_imp")
	rule := residentRuleHypIndex(t, e, sid, gid, "∀y")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &rule}},
	}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	for _, left := range res.Produced {
		closed, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: left.GoalID, Tactic: TacticReq{Type: "simplify"}})
		require.NoError(t, err)
		require.True(t, closed.Success, "the residual %s: %+v", left.GoalID, closed.Diagnostics)
	}
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: sid, Section: 0, FuncName: "Build_RESIDENT_RULE", Family: "sets/set_basic"})
	require.NoError(t, err, "emit, and the re-run that collects the section's CNF keys")
	assert.Contains(t, out.Go, "func(a *Argument, h, _, _ Fact)", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.Go, "Simp(Fwd(h))", "--- source: ---\n%s", out.Go)
	assert.NotContains(t, out.Go, "TODO", "--- source: ---\n%s", out.Go)
}

// Folding a fibre membership re-creates the condition below a pair
// binder. It is a self-embedding rule, not a terminating simplification.
func TestSimpWith_RefusesReversedFibreMembership(t *testing.T) {
	e := byArithEngine(t)
	stmt := "∀φ:(num → num → num). ∀k:num. ∀x:extended_nonneg_real. " +
		"(∀m n:num. (m, n) ∈ {p:prod(num, num) | φ(fst(p), snd(p)) = k} ⇔ φ(m, n) = k) ⇒ " +
		"extended_series(λm:num. extended_series(λn:num. COND(φ(m, n) = k, x, extended_of_real(&0)))) = x"
	sid, gid := bareArithLeaf(t, e, stmt, "strip_quant", "strip_imp")
	rule := 0
	out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &rule, Flip: true}}},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.Contains(t, refusal(out), "Refused as a rewrite")
	state, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	require.Equal(t, 1, state.NumOpen)
}

// Two rules that feed each other, neither embedding itself, pass the
// rule set's own refusal and are cut by the divergence whistle. The step
// fails saying that the rule set was cut, and the session is unchanged.
// The first pair is first-order; the second is the fibre membership
// stated through a predicate, which re-creates its condition below the
// pair binder.
func TestSimpWith_RefusesATwoRuleFeedAsCut(t *testing.T) {
	e := byArithEngine(t)
	for _, row := range []struct{ name, stmt string }{
		{"first order", "∀f:(num → num). ∀g:(num → num). ∀h:(num → num). ∀a:num. " +
			"(∀x:num. f(x) = g(x)) ⇒ (∀x:num. g(x) = h(f(x))) ⇒ f(a) = a"},
		{"fibre membership", "∀φ:(num → num → num). ∀ψ:(num → num → bool). ∀k:num. ∀x:extended_nonneg_real. " +
			"(∀m n:num. φ(m, n) = k ⇔ ψ(m, n)) ⇒ " +
			"(∀m n:num. ψ(m, n) ⇔ (m, n) ∈ {p:prod(num, num) | φ(fst(p), snd(p)) = k}) ⇒ " +
			"extended_series(λm:num. extended_series(λn:num. COND(φ(m, n) = k, x, extended_of_real(&0)))) = x"},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, row.stmt, "strip_quant", "strip_imp", "strip_imp")
			first, second := 0, 1
			var out *StepResult
			var err error
			done := make(chan struct{})
			go func() {
				defer close(done)
				out, err = e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
					GoalID: gid,
					Tactic: TacticReq{Type: "simp_with", WithLemmas: []LemmaWithSpec{{HypIndex: &first}, {HypIndex: &second}}},
				})
			}()
			select {
			case <-done:
			case <-time.After(60 * time.Second):
				t.Fatal("simp_with over a two-rule feed did not return within 60s")
			}
			require.NoError(t, err)
			require.False(t, out.Success)
			require.Contains(t, refusal(out), "the rule set was cut as divergent")
			require.Contains(t, refusal(out), "The divergence whistle cut the rewrite at firing")
			require.NotContains(t, refusal(out), "Refused as a rewrite")
			state, err := e.InspectState(context.Background(), sid)
			require.NoError(t, err)
			require.Equal(t, 1, state.NumOpen)
		})
	}
}
