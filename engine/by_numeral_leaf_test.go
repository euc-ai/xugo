package engine

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// numeralLeafSession builds the induction base leaf of
// nat_prime.PrimeDividesFactorial — `nat_prime(p₀) ⊢ (p₀ ∣ factorial(0)) ⇔
// (p₀ ≤ 0)` — the leaf where a resident `p₀ = 1` (from DividesOne at p₀),
// read `1 → p₀`, would rewrite the `2` inside PrimeAtLeastTwo's
// `2 ≤ p₀` into `bit0(p₀)`, and where the Broadcast fan under
// Normalized + arith would then never converge. Returns the session id,
// the base goal id, and the three lemmas the leaf cites.
func numeralLeafSession(t *testing.T, e *Engine) (sid, base string, lemmas []LemmaWithSpec) {
	t.Helper()
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope("∀p n:num. nat_prime(p) ⇒ (p ∣ factorial(n) ⇔ p ≤ n)", &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	apply := func(gid string, req TacticReq) *StepResult {
		t.Helper()
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: req})
		require.NoError(t, err, "apply %s", req.Type)
		return res
	}
	for _, typ := range []string{"strip_quant", "strip_imp"} {
		res := apply(gid, TacticReq{Type: typ})
		require.Len(t, res.Produced, 1, typ)
		gid = res.Produced[0].GoalID
	}
	ind := apply(gid, TacticReq{Type: "induction", Const: "n_0"})
	require.Len(t, ind.Produced, 2, "induction produces the base and the step")
	lemmas = []LemmaWithSpec{
		{Key: "nat_arith.Factorial"},
		{Key: "nat_divides.DividesOne", TermSpecialize: map[string]string{"n": "p₀"}},
		{Key: "nat_prime.PrimeAtLeastTwo", TermSpecialize: map[string]string{"p": "p₀"}},
	}
	return info.ID, ind.Produced[0].GoalID, lemmas
}

// TestByArith_NumeralLeafNotRewrittenIntoVariable: the base leaf closes
// under a bare `by {arith:true}` — the retire test of the known issue
// "The ground CC rewrites INSIDE a numeral". Before the numeral rule in
// ext/prop's contextEq the residual read `bit0(p₀) ≤ p₀, p₀ = 1, …`.
func TestByArith_NumeralLeafNotRewrittenIntoVariable(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	sid, base, lemmas := numeralLeafSession(t, e)
	zero := 0
	t0 := time.Now()
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: base, Tactic: TacticReq{
		Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: &zero}}, WithLemmas: lemmas,
	}})
	require.NoError(t, err)
	require.Equal(t, "close", res.Effect, "the base leaf must close under bare arith")
	t.Logf("closed in %v", time.Since(t0))
}

// TestByBroadcast_FanConverges: the same leaf under `arith + normalized
// + broadcast` closes — the numeral rule removes the churn each round
// would re-fan on, so the fan converges inside the Broadcast loop's
// round budget.
func TestByBroadcast_FanConverges(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	sid, base, lemmas := numeralLeafSession(t, e)
	zero := 0
	t0 := time.Now()
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: base, Tactic: TacticReq{
		Type: "by", Arith: true, Broadcast: true, ByShape: &ByShapeReq{Normalized: true},
		ByHyps: []ByHypSpec{{HypIndex: &zero}}, WithLemmas: lemmas,
	}})
	took := time.Since(t0)
	require.NoError(t, err)
	require.Less(t, took, 60*time.Second, "the Broadcast fan must return — it used to run until killed")
	require.Equal(t, "close", res.Effect, "diagnostics: %+v", res.Diagnostics)
}
