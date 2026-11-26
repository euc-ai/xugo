package engine

import (
	"context"
	"github.com/euc-ai/xugo/library/registry"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestTranscriptD_Battery is the well-founded-recursion transcript as a
// literal battery test — every author move as written, against the real
// registry and corpus:
//
//	D1  define gcd2 (recursive, ONE total COND equation, measure λn. n)
//	    → the termination obligation opens: ∀m n. ¬(n = 0) ⇒ nat_mod(m, n) < n
//	D2  by — lemmas: the division theorem — termination, the author's math
//	    → on close: schema wellfounded_recursion (measure), simp_installed 2
//	D3  add-goal  ∀m. gcd2(m, 0) = m
//	D4  simp; refl                      — the derived base reading fires
//	D5  emit-section                    — family.Define with the measure
//
// Env wiring mirrors the A battery.
func TestTranscriptD_Battery(t *testing.T) {

	env := testEnv()
	// In-memory CNF proof store: D2's `by` runs a live refute whose
	// proof the D5 emit-time capture re-reads (the B battery's wiring;
	// production wires the file-backed session store here).
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        registry.GetConstMetaManager().LoadConstMeta,
		LoadOrStoreConstMeta: registry.GetConstMetaManager().LoadOrStoreConstMeta,
		Syntax:               registry.GetConstMetaManager(),
		CNFStore:             proof.NewMemoryCNFStore(),
	}
	env.LibraryThms = serve.InductionPrinciples()
	serve.RegisterAll(env)
	serve.InstallProofPolicy()
	installTestNatBundle()
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)

	apply := func(goalID, tacticType string, tac *TacticReq) *StepResult {
		t.Helper()
		req := TacticReq{Type: tacticType}
		if tac != nil {
			req = *tac
			req.Type = tacticType
		}
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: req})
		require.NoError(t, err, "apply %s on %s", tacticType, goalID)
		require.True(t, res.Success, "apply %s on %s: %+v", tacticType, goalID, res.Diagnostics)
		return res
	}
	addGoal := func(text string) string {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
			ConstResolver:      envConstResolver(s.env),
			StrictResolution:   true,
			FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors, "add-goal %q", text)
		s.mu.Lock()
		defer s.mu.Unlock()
		return s.AddGoal(parsed.Prop)
	}

	// D1 — define gcd2: one total COND equation, recursion on the
	// second argument by the identity measure. The termination
	// obligation opens; nothing is installed yet.
	defRes, err := e.Define(&DefineRequest{
		SessionID: info.ID,
		Recursive: &DefineRecursive{
			Name: "zz_gcd2_d",
			Type: "num → num → num",
			Equations: []string{
				"∀m n:num. zz_gcd2_d(m, n) = COND(n = 0, m, zz_gcd2_d(n, nat_mod(m, n)))",
			},
			Measure: "λn:num. n",
		},
	})
	require.NoError(t, err)
	require.Equal(t, "recursive", defRes.Shape)
	require.Equal(t, "wellfounded_recursion (measure)", defRes.Schema)
	require.Zero(t, defRes.SimpInstalled, "installation happens on close, not at D1")
	require.Contains(t, defRes.Obligation, "nat_mod(m, n) < n",
		"the obligation is the author-readable decrease fact")
	require.NotEmpty(t, defRes.ObligationGoalID)

	// D2 — the termination argument: the remainder is below the
	// divisor. One `by` against nat_div_mod.Division closes it; the completion
	// (the manual's R4: the two derived readings join the simp set) rides this
	// apply's response.
	closed := apply(defRes.ObligationGoalID, "by", &TacticReq{
		WithLemmas: []LemmaWithSpec{{Key: "nat_div_mod.Division"}},
	})
	require.Equal(t, "close", closed.Effect, "D2: the obligation closes")
	require.Len(t, closed.DefineCompleted, 1, "the define completes on this apply")
	done := closed.DefineCompleted[0]
	require.Equal(t, "zz_gcd2_d", done.Defined)
	require.Equal(t, "wellfounded_recursion (measure)", done.Schema)
	require.Equal(t, 2, done.SimpInstalled, "base + step readings")
	require.True(t, s.sections[defRes.Section].root.Proved(), "the definition section is proved")

	// D3–D4 — a USE of the definition, zero setup: the derived base
	// reading fires from the simp set on a ground instance; the
	// reflexivity residual closes. (The dream's original D3 restated
	// the base reading itself — measured circular: simp's driver
	// refuses a rule α-equal to the goal by design. The transcript's
	// post-listing note records the revision, the A4/B6 precedent.)
	base := addGoal("zz_gcd2_d(12, 0) = 12")
	simped := apply(base, "simp", nil)
	require.Len(t, simped.Produced, 1)
	require.Equal(t, "close", apply(simped.Produced[0].GoalID, "simplify", nil).Effect,
		"D4: the reflexivity residual closes")

	// D5 — emit: the definition renders 1:1 as family.Define with the
	// measure and the termination proof as the entry's own fields.
	defEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: defRes.Section,
		FuncName: "Build_Gcd2", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted WF define:\n%s", defEmit.Go)
	require.Contains(t, defEmit.Go, "family.Define(registry.DefEntry{")
	require.Contains(t, defEmit.Go, `Measure: "λn:num. n"`)
	require.Contains(t, defEmit.Go, "Termination: []Action{")
	require.Contains(t, defEmit.Go, `nat_div_mod.Division`,
		"the termination cite is rendered and declared")
	require.NotContains(t, defEmit.Go, "TODO")
}
