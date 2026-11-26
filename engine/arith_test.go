package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func unscopedArithTactic(goal core.Prop) *tactic.SubGoals {
	return tactic.ArithTactic(goal, omega.UnscopedArithPolicy(), nil)
}

// TestApplyStep_Arith_ClosesNumGoals end-to-end-validates Step F: the engine
// surfaces a SINGLE `arith` apply move that auto-dispatches between ring (num
// equality) and linarith (linear comparison). The agent calls `arith` and the
// right procedure runs. A degrade panics (no placeholder fabricator in this test
// binary), so a green run proves the corpus-backed bundle is wired.
func TestApplyStep_Arith_ClosesNumGoals(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	run := func(goalStr string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)

		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)

		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		assert.True(t, out.Success, "%s: arith should succeed", goalStr)
		assert.True(t, out.State.Complete, "%s: proof should be complete", goalStr)
	}

	// Ring branch (num polynomial equalities): additive AC, distribution,
	// numeral folding, symbolic products via MulSortRewrite.
	run("m:num, n:num ⊢ m + n = n + m")
	run("a:num, b:num ⊢ (a + b) * (a + b) = a * a + 2 * (a * b) + b * b")
	run("2 * 3 = 6")

	// Linarith branch (linear comparisons): ℚ-Farkas-valid goals.
	run("a:num, b:num, c:num, a <= b, b <= c ⊢ a <= c")
	run("a:num, b:num, a < b ⊢ a <= b")
	run("a:num, b:num, a <= b, b <= a ⊢ a = b")
}

// TestApplyStep_Arith_ClosesImplicationForms validates the leading-wrapper
// strip: `arith`/`auto` close linear goals whose facts are `⇒`-antecedents
// or sit under a `∀` prenex, NOT only the sequent (hyp ⊢ concl) form. The
// hyp-aware decider is blind to a conclusion wrapper; ApplyArithSimplify strips
// the wrapper (antecedent → hyp, ∀ → fresh var) and retries. These are the
// shapes an agent would otherwise hand-unfold with `strip_imp; arith`
// (or worse, manual loads of the transitivity lemma). The negative case pins the
// commit-only-if-closed contract at the engine surface: an invalid `⇒`-goal
// declines, never landing a half-stripped residual.
func TestApplyStep_Arith_ClosesImplicationForms(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	apply := func(t *testing.T, tac, goalStr string) *StepResult {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)
		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)
		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: tac}})
		require.NoError(t, err)
		return out
	}

	// Positive shapes: each MUST close through BOTH `arith` and `auto` (the
	// arith fast-path is inside auto), since the agent shouldn't have to know
	// which move strips.
	positives := []string{
		// implication-form transitivity (antecedents, not hyps)
		"a:num, b:num, c:num ⊢ (a <= b) => (b <= c) => (a <= c)",
		// implication-form nonneg bound — closes via implicit 0 ≤ n1
		"n0:num, n1:num, m0:num ⊢ (n0 + n1 <= m0) => (n0 <= m0)",
		// ∀-prenex over the implication chain (strip ∀ then ⇒)
		"forall a:num. forall b:num. forall c:num. (a <= b) => (b <= c) => (a <= c)",
	}
	for _, goalStr := range positives {
		for _, tac := range []string{"arith", "auto"} {
			t.Run(tac+": "+goalStr, func(t *testing.T) {
				out := apply(t, tac, goalStr)
				assert.True(t, out.Success, "%s via %s should succeed", goalStr, tac)
				require.NotNil(t, out.State, "%s via %s: success without State", goalStr, tac)
				assert.True(t, out.State.Complete, "%s via %s: proof should be complete", goalStr, tac)
			})
		}
	}

	// Negative: `(a≤b) ⇒ (b≤a)` is invalid; the strip is committed only on full
	// closure, so `arith` declines cleanly (Success=false), leaving nothing
	// behind for the next tactic.
	t.Run("arith declines invalid implication", func(t *testing.T) {
		out := apply(t, "arith", "a:num, b:num ⊢ (a <= b) => (b <= a)")
		assert.False(t, out.Success, "invalid ⇒-goal must NOT close via the strip path")
	})
}

// TestApplyStep_Arith_ClosesBooleanGoals validates the formula-level decider
// (omega/nat.go) at the engine surface: a goal that is a boolean
// combination of comparison atoms which NO single atom decides — a `⇒` nested
// inside a `∨`, an n-ary trichotomy — closes via `arith`/`auto` by atom case
// analysis. These are the shapes the binary-disjunction leaf and the atom
// decider individually leave open. The negative case pins that an invalid
// boolean does NOT falsely close.
func TestApplyStep_Arith_ClosesBooleanGoals(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	apply := func(t *testing.T, tac, goalStr string) *StepResult {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)
		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)
		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: tac}})
		require.NoError(t, err)
		return out
	}

	positives := []string{
		// ⇒ nested inside ∨ (valid via transitivity)
		"a:num, b:num, c:num ⊢ (a <= b => a <= c) \\/ (c < b)",
		// n-ary / nested trichotomy
		"a:num, b:num ⊢ (a < b) \\/ ((a = b) \\/ (b < a))",
		// ⇒ to a disjunctive consequent
		"a:num, b:num ⊢ (a <= b) => ((a < b) \\/ (a = b))",
		// ⇔ between compound boolean combinations (antisymmetry)
		"a:num, b:num ⊢ (a <= b /\\ b <= a) <=> (a = b)",
	}
	for _, goalStr := range positives {
		for _, tac := range []string{"arith", "auto"} {
			t.Run(tac+": "+goalStr, func(t *testing.T) {
				out := apply(t, tac, goalStr)
				assert.True(t, out.Success, "%s via %s should succeed", goalStr, tac)
				require.NotNil(t, out.State, "%s via %s: success without State", goalStr, tac)
				assert.True(t, out.State.Complete, "%s via %s: proof should be complete", goalStr, tac)
			})
		}
	}
}

// TestApplyStep_Auto_ClosesNumArithGoals validates that AutoExpand's pipeline
// includes the unified arithmetic closer: the agent calls `auto` (no explicit
// `arith` move) on a num goal and it closes. Same goals as the `arith` test
// above — they MUST close through `auto` too, otherwise auto's pipeline isn't
// covering arithmetic and the agent has to predict the right move (the very
// burden the unified `arith` design avoids).
func TestApplyStep_Auto_ClosesNumArithGoals(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	run := func(goalStr string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)

		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)

		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "auto"}})
		require.NoError(t, err)
		assert.True(t, out.Success, "%s: auto should succeed", goalStr)
		assert.True(t, out.State.Complete, "%s: proof should be complete", goalStr)
	}

	// Ring goals (num polynomial equalities) close through auto without an
	// explicit `arith` move.
	run("m:num, n:num ⊢ m + n = n + m")
	run("a:num, b:num ⊢ (a + b) * (a + b) = a * a + 2 * (a * b) + b * b")
	run("2 * 3 = 6")
	// Linarith goals close through auto too.
	run("a:num, b:num, c:num, a <= b, b <= c ⊢ a <= c")
	run("a:num, b:num, a < b ⊢ a <= b")
	run("a:num, b:num, a <= b, b <= a ⊢ a = b")
}

// TestApplyStep_Arith_ClosesCompoundNumGoals exercises the arith move's
// non-ring/non-linarith layers (the operator handlers of prover/solver/omega) at the engine surface:
// monus (cancel + case-split), nat_max/nat_min (idempotence + case-split), predecessor bridge,
// nat_div/nat_mod (trivial simp + bounded-atom enrichment + common-factor cancel), and
// the c≤1 nat_pow reductions. Each layer is also covered by omega/corpus unit tests;
// this is the agent-facing contract — the unified `arith` action handles all of
// them. Includes the nat_pow row: a literal exponent is READ in the monomial
// basis (pow_basis.go), so `nat_pow(a, 2) = a * a` decides, while the term
// itself is never expanded by arith (ring_nf spells a power out on request).
//
// predecessor and nat_pow are not default-scope DSL consts (they collide with bound vars in
// their recursive definitions' proofs), so goals that mention them parse
// through `dsl.ParsePropTextInScope` with an extension scope.
func TestApplyStep_Arith_ClosesCompoundNumGoals(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()
	extScope := &dsl.ParseScope{Consts: map[string]core.ConstTerm{
		"predecessor": dsl.NatPreMeta.Term(),
		"nat_pow":     dsl.NatExpMeta.Term(),
	}}

	closesArith := func(t *testing.T, goalStr string, expectClose bool) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)

		res := dsl.ParsePropTextInScope(goalStr, extScope)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)

		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		if expectClose {
			assert.True(t, out.Success, "%s: arith should succeed", goalStr)
			require.NotNil(t, out.State, "%s: success without State", goalStr)
			assert.True(t, out.State.Complete, "%s: proof should be complete", goalStr)
		} else {
			// Decline: out.Success is false and out.State is nil (only the
			// success path populates State). Asserting Success==false guards
			// both possibilities.
			assert.False(t, out.Success, "%s: arith should NOT close this", goalStr)
		}
	}

	t.Run("monus subCancel — n+m-n → m", func(t *testing.T) {
		closesArith(t, "n:num, m:num ⊢ (n + m) - n = m", true)
	})
	t.Run("monus subCancel — (n+m+k)-n → m+k", func(t *testing.T) {
		closesArith(t, "n:num, m:num, k:num ⊢ (n + m + k) - n = m + k", true)
	})
	t.Run("monus subTrunc — 0-n → 0", func(t *testing.T) {
		closesArith(t, "n:num ⊢ 0 - n = 0", true)
	})
	t.Run("monus split — irreducible a-b ≤ a", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ a - b <= a", true)
	})
	// Multi-monus COMPOSITION. Each branch of monusSplittable must inject its
	// ordering GUARD (not just the value pin) so a SIBLING monus atom's split can
	// use it — without that, two interacting monus atoms don't compose (regression
	// guard for the guard-injection fix). And the linear core must dedup
	// Fourier–Motzkin rows, else the 6-monus distance-triangle below explodes
	// super-exponentially (>10⁸ row combinations) instead of closing in seconds.
	t.Run("monus 2-atom compose — a≤b ⊢ a-c ≤ b-c", func(t *testing.T) {
		closesArith(t, "a:num, b:num, c:num, a <= b ⊢ a - c <= b - c", true)
	})
	t.Run("monus 3-atom — triangle helper a-c ≤ (a-b)+(b-c)", func(t *testing.T) {
		closesArith(t, "a:num, b:num, c:num ⊢ a - c <= (a - b) + (b - c)", true)
	})
	t.Run("monus 6-atom — nat distance triangle (post def-expand)", func(t *testing.T) {
		closesArith(t, "m:num, n:num, p:num ⊢ ((m - p) + (p - m)) <= (((m - n) + (n - m)) + ((n - p) + (p - n)))", true)
	})

	t.Run("nat_max idempotence", func(t *testing.T) {
		closesArith(t, "a:num ⊢ nat_max(a, a) = a", true)
	})
	t.Run("nat_min idempotence", func(t *testing.T) {
		closesArith(t, "a:num ⊢ nat_min(a, a) = a", true)
	})
	t.Run("nat_max split — a ≤ nat_max(a, b)", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ a <= nat_max(a, b)", true)
	})
	t.Run("nat_min split — nat_min(a, b) ≤ a", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ nat_min(a, b) <= a", true)
	})
	t.Run("nested nat_min ≤ nat_max (two splits)", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ nat_min(a, b) <= nat_max(a, b)", true)
	})

	t.Run("predecessor bridge — predecessor(suc a) = a", func(t *testing.T) {
		closesArith(t, "a:num ⊢ predecessor(suc(a)) = a", true)
	})
	t.Run("predecessor bridge — predecessor(a+1) = a", func(t *testing.T) {
		closesArith(t, "a:num ⊢ predecessor(a + 1) = a", true)
	})
	t.Run("predecessor bridge — predecessor(0) = 0", func(t *testing.T) {
		closesArith(t, "a:num ⊢ predecessor(0) = 0", true)
	})
	t.Run("predecessor bridge — symbolic predecessor(a) ≤ a", func(t *testing.T) {
		closesArith(t, "a:num ⊢ predecessor(a) <= a", true)
	})

	t.Run("nat_div trivial — nat_div(m, 1) = m", func(t *testing.T) {
		closesArith(t, "m:num ⊢ nat_div(m, 1) = m", true)
	})
	t.Run("nat_mod trivial — nat_mod(m, 1) = 0", func(t *testing.T) {
		closesArith(t, "m:num ⊢ nat_mod(m, 1) = 0", true)
	})
	t.Run("nat_mod reflexive — nat_mod(n, n) = 0", func(t *testing.T) {
		closesArith(t, "n:num ⊢ nat_mod(n, n) = 0", true)
	})
	t.Run("mod bound — nat_mod(m, n) ≤ m", func(t *testing.T) {
		closesArith(t, "m:num, n:num ⊢ nat_mod(m, n) <= m", true)
	})
	t.Run("div bound — nat_div(m, n) ≤ m", func(t *testing.T) {
		closesArith(t, "m:num, n:num ⊢ nat_div(m, n) <= m", true)
	})
	t.Run("division bound, literal divisor — nat_mod(m, 5) < 5", func(t *testing.T) {
		closesArith(t, "m:num ⊢ nat_mod(m, 5) < 5", true)
	})
	t.Run("small dividend, mod — m<n ⊢ nat_mod(m, n) = m", func(t *testing.T) {
		closesArith(t, "m:num, n:num, m < n ⊢ nat_mod(m, n) = m", true)
	})
	t.Run("small dividend, div — m<n ⊢ nat_div(m, n) = 0", func(t *testing.T) {
		closesArith(t, "m:num, n:num, m < n ⊢ nat_div(m, n) = 0", true)
	})
	t.Run("self quotient — n ≥ 1 ⊢ nat_div(n, n) = 1", func(t *testing.T) {
		closesArith(t, "n:num, n >= 1 ⊢ nat_div(n, n) = 1", true)
	})
	t.Run("common factor — nat_div(2a, 2b) = nat_div(a, b)", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ nat_div(2 * a, 2 * b) = nat_div(a, b)", true)
	})

	// Symbolic-n=0 case-split (proveDivModSplitOnZero) + proveNeqZero ¬(n=0)-hyp
	// route. Handles divisors with no `0<n`/`n≠0` info via ExcludedMiddle on n=0
	// + `n≠0 ⇔ 0<n`.
	t.Run("nat_div/nat_mod ¬(n=0) hyp — n!=0 ⊢ nat_mod(m, n) < n", func(t *testing.T) {
		closesArith(t, "m:num, n:num, n != 0 ⊢ nat_mod(m, n) < n", true)
	})
	t.Run("nat_div/nat_mod n=0 hyp — split's n=0 branch ⊢ nat_mod(m, n) = m", func(t *testing.T) {
		closesArith(t, "m:num, n:num, n = 0 ⊢ nat_mod(m, n) = m", true)
	})
	t.Run("nat_div/nat_mod n=0 hyp — split's n=0 branch ⊢ nat_div(m, n) = 0", func(t *testing.T) {
		closesArith(t, "m:num, n:num, n = 0 ⊢ nat_div(m, n) = 0", true)
	})
	// Negative: bare `nat_mod(m, n) < n` is FALSE at n=0 (m<0 over num is false), so
	// the split's n=0 branch can't close and arith correctly declines. Guards
	// against an unsound future change that would auto-close it.
	t.Run("NEGATIVE: bare nat_mod(m, n) < n declines (false at n=0)", func(t *testing.T) {
		closesArith(t, "m:num, n:num ⊢ nat_mod(m, n) < n", false)
	})

	t.Run("nat_pow base — nat_pow(a, 0) = 1", func(t *testing.T) {
		closesArith(t, "a:num ⊢ nat_pow(a, 0) = 1", true)
	})
	t.Run("nat_pow unit — nat_pow(a, 1) = a", func(t *testing.T) {
		closesArith(t, "a:num ⊢ nat_pow(a, 1) = a", true)
	})
	t.Run("base one, symbolic — nat_pow(1, n) = 1", func(t *testing.T) {
		closesArith(t, "n:num ⊢ nat_pow(1, n) = 1", true)
	})
	t.Run("base zero — nat_pow(0, suc a) = 0", func(t *testing.T) {
		closesArith(t, "a:num ⊢ nat_pow(0, suc(a)) = 0", true)
	})
	t.Run("base zero with hyp — 0<n ⊢ nat_pow(0, n) = 0", func(t *testing.T) {
		closesArith(t, "n:num, 0 < n ⊢ nat_pow(0, n) = 0", true)
	})

	// Cross-layer compositions. The deep+fixpoint rewrite folds them in one move.
	t.Run("compound — nat_div(m, 1) + nat_mod(n, n) = m", func(t *testing.T) {
		closesArith(t, "m:num, n:num ⊢ nat_div(m, 1) + nat_mod(n, n) = m", true)
	})
	t.Run("compound — predecessor(suc a) + nat_max(b, b) = a + b", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ predecessor(suc(a)) + nat_max(b, b) = a + b", true)
	})

	// A literal-exponent nat_pow is read in the monomial basis — the two
	// spellings of a square are one unknown — so the identity decides with
	// no expansion of the term (the "no surprise expansion inside arith"
	// contract is about the TERM, which ring_nf spells out on request).
	t.Run("nat_pow(a, 2) = a * a reads in the monomial basis", func(t *testing.T) {
		closesArith(t, "a:num ⊢ nat_pow(a, 2) = a * a", true)
	})
}

// TestApplyStep_Arith_PartialReduction exercises the OTHER half of `arith`'s
// contract: the unified rewrite isn't only a closer — for goals where some
// arithmetic content reduces but the surrounding logical structure doesn't fold
// to ⊤, `arith` advances the conclusion (or first matching hyp) to a strictly
// simpler residual and the agent continues from there. Each case asserts:
//
//  1. arith fires (Success=true).
//  2. The proof is NOT yet complete (Complete=false).
//  3. The residual conclusion is the EXPECTED simpler form.
//
// (3) is load-bearing — it pins what the rewrite actually does, so a future
// change that accidentally over-simplifies or under-simplifies fires this test.
func TestApplyStep_Arith_PartialReduction(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()
	extScope := &dsl.ParseScope{Consts: map[string]core.ConstTerm{
		"predecessor": dsl.NatPreMeta.Term(),
		"nat_pow":     dsl.NatExpMeta.Term(),
	}}

	check := func(t *testing.T, goalStr, wantResidual string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)
		res := dsl.ParsePropTextInScope(goalStr, extScope)
		require.Empty(t, res.Errors, "parse goal: %v", res.Errors)
		gid := s.AddGoal(res.Prop)

		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		require.True(t, out.Success, "%s: arith should fire (make progress)", goalStr)
		require.NotNil(t, out.State, "%s: success without State", goalStr)
		require.False(t, out.State.Complete, "%s: arith should NOT fully close", goalStr)
		require.Len(t, out.State.Goals, 1, "%s: expected one residual goal", goalStr)

		// Pin the residual conclusion — parse the expected form in the same scope
		// (with the goal's free-var bindings) and compare α-equality.
		gotConcl := out.State.Goals[0].Statement.Conclusion()
		wantRes := dsl.ParsePropTextInScope(wantResidual, extScope)
		require.Empty(t, wantRes.Errors, "parse want: %v", wantRes.Errors)
		wantConcl := wantRes.Prop.Conclusion()
		assert.True(t, gotConcl.AlphaEquals(wantConcl),
			"%s:\n  got residual: %v\n  want:         %v", goalStr, gotConcl, wantConcl)
	}

	t.Run("identity simp folds compound concl — (a+0=a) ∧ c → c", func(t *testing.T) {
		check(t,
			"a:num, c:bool ⊢ (a + 0 = a) ∧ c",
			"a:num, c:bool ⊢ c")
	})

	t.Run("atom decision folds compound concl — (a<b+1) ∧ c → c (given a<b)", func(t *testing.T) {
		check(t,
			"a:num, b:num, c:bool, a < b ⊢ (a < b + 1) ∧ c",
			"a:num, b:num, c:bool, a < b ⊢ c")
	})

	t.Run("nat_max idempotence folds ⇒ — (nat_max(a,a)=a) ⇒ c → c", func(t *testing.T) {
		check(t,
			"a:num, c:bool ⊢ (nat_max(a, a) = a) ⇒ c",
			"a:num, c:bool ⊢ c")
	})

	t.Run("predecessor bridge folds ⇒ — (predecessor(suc a)=a) ⇒ c → c", func(t *testing.T) {
		check(t,
			"a:num, c:bool ⊢ (predecessor(suc(a)) = a) ⇒ c",
			"a:num, c:bool ⊢ c")
	})

	// The omega-level Cond cascade reduces `COND(a-a=0, c, ⊥)` to `c`. The
	// parser now resolves `COND` to the ext.COND const (registered in
	// defaultNatScopeConstMetas), so ext.MatchesCond fires and the
	// trivialCondRewrite cascade is visible on parsed text-DSL goals.
	// Previously the parser built a free *var* named "COND", MatchesCond
	// returned false, and this case had to be skipped.
	t.Run("monus subCancel inside COND — COND(a-a=0, c, ⊥) → c", func(t *testing.T) {
		check(t,
			"a:num, c:bool ⊢ COND(a - a = 0, c, false)",
			"a:num, c:bool ⊢ c")
	})

	t.Run("nat_pow(_,1) shortcut folds — (nat_pow(a,1) = a) ⇒ c → c", func(t *testing.T) {
		check(t,
			"a:num, c:bool ⊢ (nat_pow(a, 1) = a) ⇒ c",
			"a:num, c:bool ⊢ c")
	})

	t.Run("mod-bound enrichment folds — (nat_mod(m,n) ≤ m) ∧ c → c", func(t *testing.T) {
		check(t,
			"m:num, n:num, c:bool ⊢ (nat_mod(m, n) <= m) ∧ c",
			"m:num, n:num, c:bool ⊢ c")
	})
}

// TestApplyStep_Arith_ClosesSplitEnrichGoals exercises five case-split /
// enrichment handlers of prover/solver/omega — the goal-side disjunction closer,
// the implication-hypothesis split, the multiple-is-zero and nested-residue
// nat_mod facts, bounded-variable enumeration, and variable-for-variable
// equality substitution — at the engine surface: the agent-facing contract
// that the unified `arith` action closes them. Each is also covered by omega/corpus unit tests; this asserts the engine
// wires them through `ApplyStep`. With serve.InstallNatBundle and no placeholder
// fabricator in this test binary, a leaf degrading to a placeholder would panic,
// so a green run proves the real theorems back every layer. Includes NEGATIVE cases: a non-tautology
// disjunction and a value-dependent bounded goal that is false at some point in
// range must NOT close.
func TestApplyStep_Arith_ClosesSplitEnrichGoals(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	closesArith := func(t *testing.T, goalStr string, expectClose bool) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)

		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)

		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		if expectClose {
			assert.True(t, out.Success, "%s: arith should succeed", goalStr)
			require.NotNil(t, out.State, "%s: success without State", goalStr)
			assert.True(t, out.State.Complete, "%s: proof should be complete", goalStr)
		} else {
			// Clean decline: a false / non-valid goal does not close, AND arith
			// makes no spurious rewrite (in particular it does NOT collapse a
			// decidable hypothesis to ⊤ from itself — arithRewriteTactic rewrites
			// each hyp only under the OTHER hyps). So Success is false outright.
			assert.False(t, out.Success, "%s: arith should NOT close this", goalStr)
		}
	}

	// (1) Goal-side disjunction / totality closer (omega/nat.go).
	t.Run("totality — a≤b ∨ b≤a", func(t *testing.T) {
		closesArith(t, `a:num, b:num ⊢ a <= b \/ b <= a`, true)
	})
	t.Run("totality pivot — a<b ∨ b≤a", func(t *testing.T) {
		closesArith(t, `a:num, b:num ⊢ a < b \/ b <= a`, true)
	})
	t.Run("disjunction direct — a<b ⊢ a≤b ∨ b<a", func(t *testing.T) {
		closesArith(t, `a:num, b:num, a < b ⊢ a <= b \/ b < a`, true)
	})
	t.Run("NEGATIVE non-tautology disjunction — a<b ∨ a=b", func(t *testing.T) {
		closesArith(t, `a:num, b:num ⊢ a < b \/ a = b`, false)
	})

	// (2) Implication-hypothesis split (omega nat_sub.go hypSplittable).
	t.Run("impl-hyp split — {a<b ⇒ b<a} ⊢ b≤a", func(t *testing.T) {
		closesArith(t, `a:num, b:num, a < b => b < a ⊢ b <= a`, true)
	})

	// (3) nat_mod enrichment: a multiple, a nested residue.
	t.Run("nat_mod multiple-is-zero — nat_mod(k*n, n) = 0", func(t *testing.T) {
		closesArith(t, "k:num, n:num ⊢ nat_mod(k * n, n) = 0", true)
	})
	t.Run("nat_mod multiple-is-zero (commuted) — nat_mod(n*k, n) = 0", func(t *testing.T) {
		closesArith(t, "k:num, n:num ⊢ nat_mod(n * k, n) = 0", true)
	})
	t.Run("nat_mod idempotence — nat_mod(nat_mod(m,n), n) = nat_mod(m,n)", func(t *testing.T) {
		closesArith(t, "m:num, n:num ⊢ nat_mod(nat_mod(m, n), n) = nat_mod(m, n)", true)
	})

	// (4) Bounded-variable enumeration split (omega/nat_exp.go).
	t.Run("bounded enum ≤ — n≤2 ⊢ n*n ≤ 4", func(t *testing.T) {
		closesArith(t, "n:num, n <= 2 ⊢ n * n <= 4", true)
	})
	t.Run("bounded enum < — n<3 ⊢ n*n ≤ 2n+1", func(t *testing.T) {
		closesArith(t, "n:num, n < 3 ⊢ n * n <= 2 * n + 1", true)
	})
	t.Run("NEGATIVE bounded enum false-at-a-value — n≤2 ⊢ n*n ≤ 3", func(t *testing.T) {
		// n=2 gives 4 ≤ 3, false — enumeration must NOT close it.
		closesArith(t, "n:num, n <= 2 ⊢ n * n <= 3", false)
	})

	// (5) eqHypSubst var=var into opaque atoms (omega/nat.go).
	t.Run("var=var merge — n=m ⊢ nat_mod(a,n) = nat_mod(a,m)", func(t *testing.T) {
		closesArith(t, "a:num, n:num, m:num, n = m ⊢ nat_mod(a, n) = nat_mod(a, m)", true)
	})
}

// TestArith_HypRewriteContext exercises the per-target rewrite context of the
// unified `arith` move (tactic.arithRewriteTactic): the conclusion is rewritten
// under ALL hypotheses, but each hypothesis is rewritten under the OTHER
// hypotheses only — never under itself. The three outcomes a hypothesis can have
// when judged against the rest of the context:
//
//   - REDUNDANT (the other hyps imply it)       → decided ⊤, the hyp is dropped;
//   - CONTINGENT (others neither prove/refute)   → left unchanged;
//   - CONTRADICTORY (the other hyps refute it)   → decided ⊥ (ex-falso).
//
// And the load-bearing contrast that proves it is NOT self-justification: the
// SAME hypothesis `n*n ≤ 4` collapses to ⊤ when a supporting `n ≤ 2` is present,
// but does NOT collapse when it stands alone — a hyp can never decide itself.
//
// Run under the real installed bundle (the enumeration that decides `n*n ⋈ k` from
// `n ≤ 2` needs the bundle's LessEqSplit / LessThanSucIffLessEq); a placeholder degrade would panic.
func TestArith_HypRewriteContext(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})

	parse := func(g string) core.Prop {
		t.Helper()
		res := dsl.ParsePropText(g)
		require.Empty(t, res.Errors, "parse %q: %v", g, res.Errors)
		return res.Prop
	}
	hasHyp := func(p core.Prop, want core.Term) bool {
		for _, h := range p.Hyps() {
			if h.AlphaEquals(want) {
				return true
			}
		}
		return false
	}
	// containsProduct identifies the `n*n ⋈ k` hypothesis (parse reorders hyps, so
	// we pick it out by content rather than position).
	containsProduct := func(h core.Term) bool {
		for s := range ext.SubTerms(h) {
			if _, _, ok := omega.MatchesStar(s); ok {
				return true
			}
		}
		return false
	}
	// split returns (the product hyp, the supporting hyp) of a 2-hyp goal.
	split := func(p core.Prop) (product, support core.Term) {
		for _, h := range p.Hyps() {
			if containsProduct(h) {
				product = h
			} else {
				support = h
			}
		}
		return
	}

	// REDUNDANT: n*n ≤ 4 is implied by n ≤ 2 (n ∈ {0,1,2} → 0,1,4 ≤ 4). The
	// decider proves it FROM n≤2 (the other hyp), so the product hyp collapses to
	// ⊤ and is dropped; n≤2 itself is retained.
	t.Run("redundant hyp → ⊤ (dropped)", func(t *testing.T) {
		goal := parse("n:num, b:bool, n <= 2, n * n <= 4 ⊢ b")
		product, support := split(goal)
		sg := unscopedArithTactic(goal)
		require.NotNil(t, sg, "arith should rewrite the redundant hyp")
		child := sg.ChildGoal(0)
		assert.True(t, hasHyp(child, prop.T), "the redundant product hyp should become ⊤")
		assert.True(t, hasHyp(child, support), "the supporting hyp n≤2 must be retained")
		assert.False(t, hasHyp(child, product), "the redundant hyp n*n≤4 should be gone")
	})

	// CONTINGENT: n*n ≤ 3 is true at n∈{0,1} but FALSE at n=2, so n≤2 neither
	// proves nor refutes it. It is left untouched; with no rewritable target
	// (conclusion b is opaque too) the move declines outright.
	t.Run("contingent hyp → unchanged (decline)", func(t *testing.T) {
		goal := parse("n:num, b:bool, n <= 2, n * n <= 3 ⊢ b")
		assert.Nil(t, unscopedArithTactic(goal),
			"a contingent hyp must not be rewritten, and nothing else reduces")
	})

	// CONTRADICTORY: under n=2, n*n=4 so n*n ≤ 3 is 4 ≤ 3 = ⊥. The decider refutes
	// the product hyp FROM n=2 (the other hyp), collapsing it to ⊥ (the goal then
	// closes by ex-falso); n=2 is retained.
	t.Run("contradictory hyp → ⊥ (ex-falso)", func(t *testing.T) {
		goal := parse("n:num, b:bool, n = 2, n * n <= 3 ⊢ b")
		product, support := split(goal)
		sg := unscopedArithTactic(goal)
		require.NotNil(t, sg, "arith should refute the contradictory hyp")
		child := sg.ChildGoal(0)
		assert.True(t, hasHyp(child, prop.F), "the contradictory product hyp should become ⊥")
		assert.True(t, hasHyp(child, support), "the refuting hyp n=2 must be retained")
		assert.False(t, hasHyp(child, product), "the contradictory hyp n*n≤3 should be gone")
	})

	// NOT self-justification: the SAME hyp n*n ≤ 4, standing ALONE (no supporting
	// n≤2), is NOT collapsed — a hyp cannot decide itself. This is the exact
	// behaviour the old whole-context rewriteTactic got wrong (it proved n*n≤4
	// FROM n*n≤4 → ⊤).
	t.Run("hyp alone is not self-decided", func(t *testing.T) {
		goal := parse("n:num, b:bool, n * n <= 4 ⊢ b")
		assert.Nil(t, unscopedArithTactic(goal),
			"a lone hyp must not be rewritten to ⊤ from itself")
	})
}

// TestApplyStep_Arith_HypRewriteContext drives the SAME hyp-rewrite scenarios as
// TestArith_HypRewriteContext, but through the ENGINE layer (`ApplyStep` with the
// `arith` move) instead of calling tactic.ArithTactic directly. The engine
// COMPOSITE (`_Arith` + `_TrivialSimplify` on leaves) does strictly more than the
// bare tactic, so the observable outcomes differ — which is exactly why the
// engine path needs its own coverage:
//
//   - REDUNDANT  → the product hyp is decided ⊤ AND the ⊤ hyp is then dropped,
//     so the residual is the clean `n≤2 ⊢ b` (Success, not complete);
//   - CONTINGENT → declines (Success=false);
//   - CONTRADICTORY → the product hyp is refuted to ⊥ and `_TrivialSimplify`
//     discharges the ⊥-hyp goal by ex-falso, so the proof CLOSES (Complete=true)
//     — a close the bare tactic does not produce;
//   - LONE → declines (no self-decide).
func TestApplyStep_Arith_HypRewriteContext(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	apply := func(t *testing.T, goalStr string) *StepResult {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)
		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse %q: %v", goalStr, res.Errors)
		gid := s.AddGoal(res.Prop)
		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		return out
	}

	t.Run("redundant hyp dropped → residual n≤2 ⊢ b", func(t *testing.T) {
		out := apply(t, "n:num, b:bool, n <= 2, n * n <= 4 ⊢ b")
		require.True(t, out.Success, "arith should fire on the redundant hyp")
		require.NotNil(t, out.State)
		assert.False(t, out.State.Complete, "b is unprovable — must not close")
		require.Len(t, out.State.Goals, 1)
		residual := out.State.Goals[0].Statement
		assert.Len(t, residual.Hyps(), 1, "the redundant product hyp (now ⊤) should be dropped")
		want := dsl.ParsePropText("n:num, b:bool, n <= 2 ⊢ b").Prop
		assert.True(t, residual.AlphaEquals(want),
			"residual should be n≤2 ⊢ b, got %v", residual.Conclusion())
	})

	t.Run("contingent hyp → decline", func(t *testing.T) {
		out := apply(t, "n:num, b:bool, n <= 2, n * n <= 3 ⊢ b")
		assert.False(t, out.Success, "a contingent hyp must not be rewritten")
	})

	t.Run("contradictory hyp → closes via ex-falso", func(t *testing.T) {
		out := apply(t, "n:num, b:bool, n = 2, n * n <= 3 ⊢ b")
		require.True(t, out.Success, "arith should refute the contradictory hyp")
		require.NotNil(t, out.State)
		assert.True(t, out.State.Complete,
			"a ⊥ hyp (n*n≤3 under n=2) should close the goal by ex-falso through the composite")
	})

	t.Run("lone hyp not self-decided → decline", func(t *testing.T) {
		out := apply(t, "n:num, b:bool, n * n <= 4 ⊢ b")
		assert.False(t, out.Success, "a lone hyp must not be rewritten to ⊤ from itself")
	})
}

func TestApplyStep_Arith_IgnoresFunctionVarInBoundedEnum(t *testing.T) {
	m, n := ext.Var("m", dsl.NumType), ext.Var("n", dsl.NumType)
	le := func(a, b core.Term) core.Term { return ext.Apply(dsl.NatLeMeta.Term(), a, b) }
	lt := func(a, b core.Term) core.Term { return ext.Apply(dsl.NatLtMeta.Term(), a, b) }
	lessEqSplit := ext.ForAll(m, n)(core.Eq(le(m, n), ext.Apply(prop.OR, lt(m, n), core.Eq(m, n))))
	lessThanSucIffLessEq := ext.ForAll(m, n)(core.Eq(lt(m, ext.Apply(dsl.SUCMeta.Term(), n)), le(m, n)))
	setTestNatBundle(&omega.NatLemmaBundle{
		LessEqSplit:          prop.WrapProp(core.TestThm(lessEqSplit)),
		LessThanSucIffLessEq: prop.WrapProp(core.TestThm(lessThanSucIffLessEq)),
	})
	t.Cleanup(func() { setTestNatBundle(nil) })
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
	s, _ := e.getSession(info.ID)

	f := ext.Var("f", core.MakeFun(dsl.NumType, dsl.NumType))
	fn := ext.Apply(f, omega.Numeral(0))
	product := ext.Apply(dsl.NatStarMeta.Term(), fn, fn)
	concl := le(product, omega.Numeral(4))
	gid := s.AddGoal(core.MakeProp(concl))

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "arith"}})
	require.NoError(t, err)
	require.Nil(t, out.EngineFault, "the bounded enumeration panicked on a function variable")
	assert.False(t, out.Success, "unbounded nonlinear f(0)*f(0)<=4 should decline")
}

// TestApplyStep_Arith_ClosesDivModDistGoals exercises the nat_div/nat_mod distribution
// leaves of prover/solver/omega at the engine surface: DivMultAdd — the
// conditional affine-nat_div simp `nat_div((c·n)+r, n) → c + nat_div(r,n)`, the nat_div companion
// to ModMultAdd (the quotient-extracting half of the residue/quotient normal
// form) — and ModAddMod, wired in the COMBINE (term-shrinking) direction
// `nat_mod(nat_mod(a,n)+nat_mod(b,n), n) → nat_mod(a+b, n)`. Also covered by omega/corpus unit
// tests; this is the agent-facing contract that the unified `arith` action closes
// them through `ApplyStep`. With serve.InstallNatBundle and no placeholder
// fabricator in this test binary, a leaf degrading to a placeholder would panic,
// so a green run proves the real
// DivMultAdd / ModAddMod theorems back both leaves. NEGATIVE: a symbolic divisor must
// NOT close — divMultAdd discharges `n≠0` numerically (literal divisor only), and
// `nat_div(n·a+b, n) = a + nat_div(b,n)` is in fact false at n=0, so arith must decline.
func TestApplyStep_Arith_ClosesDivModDistGoals(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	closesArith := func(t *testing.T, goalStr string, expectClose bool) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)

		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)

		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		if expectClose {
			assert.True(t, out.Success, "%s: arith should succeed", goalStr)
			require.NotNil(t, out.State, "%s: success without State", goalStr)
			assert.True(t, out.State.Complete, "%s: proof should be complete", goalStr)
		} else {
			assert.False(t, out.Success, "%s: arith should NOT close this", goalStr)
		}
	}

	// DivMultAdd — literal divisor, both summand positions and both factor orders
	// of the multiple (distinct clauses the leaf projects).
	t.Run("quotient of a sum: first summand, divisor left — nat_div(2a+b,2) = a+nat_div(b,2)", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ nat_div(2 * a + b, 2) = a + nat_div(b, 2)", true)
	})
	t.Run("quotient of a sum: divisor right factor — nat_div(a*2+b,2) = a+nat_div(b,2)", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ nat_div(a * 2 + b, 2) = a + nat_div(b, 2)", true)
	})
	t.Run("quotient of a sum: second summand — nat_div(b+2a,2) = nat_div(b,2)+a", func(t *testing.T) {
		closesArith(t, "a:num, b:num ⊢ nat_div(b + 2 * a, 2) = nat_div(b, 2) + a", true)
	})

	// ModAddMod — combine direction; unconditional, so it fires for a SYMBOLIC
	// divisor too.
	t.Run("residue of a sum, combine — nat_mod(nat_mod(a,n)+nat_mod(b,n),n) = nat_mod(a+b,n)", func(t *testing.T) {
		closesArith(t, "a:num, b:num, n:num ⊢ nat_mod(nat_mod(a, n) + nat_mod(b, n), n) = nat_mod(a + b, n)", true)
	})

	// NEGATIVE: symbolic divisor — `nat_div(n·a+b, n) = a + nat_div(b,n)` is false at n=0
	// (LHS = nat_div(b,0) = 0, RHS = a), and divMultAdd only discharges a literal n≠0,
	// so arith must decline. Guards the n≠0 side condition.
	t.Run("NEGATIVE symbolic divisor — nat_div(n*a+b,n) = a+nat_div(b,n) declines", func(t *testing.T) {
		closesArith(t, "a:num, b:num, n:num ⊢ nat_div(n * a + b, n) = a + nat_div(b, n)", false)
	})
}

// TestApplyStep_Arith_ClosesACEqualities answers a concrete question raised by
// the /prove nat_div/nat_mod campaign: when a
// proof reduces to a bare multi-atom associative-commutative equality like
//
//	(X+Y)+(Z+W) = (Y+W)+(X+Z)          (the sum of two remainders)
//	(a*b)*(c*d) = (b*d)*(a*c)          (a quotient of two products)
//
// the sub-agents had to hand-drive a ~9-step `trans` + associativity/commutativity chain,
// because they were (correctly) forbidden from calling `arith` — those very
// theorems are arith's own dependencies, so using arith would be circular.
//
// The open question this test settles: IF arith WERE allowed (i.e. for any goal
// of this shape that is NOT an arith dependency), would the AC equality close in
// a single `arith` move? If yes, the hand-rolled chains are only necessary under
// the circularity constraint, and ordinary callers should just use `arith`.
//
// The AC equalities are pure-linear (additive) or pure-monomial (multiplicative)
// over the goal's atoms, so they go through omega's ring/linarith normal form,
// which treats any opaque subterm (a plain variable OR a nat_mod/nat_div application) as
// an atomic indeterminate. We therefore test both:
//   - plain variables (the minimal shape), and
//   - nat_mod-applied atoms (faithful to the actual nat_div/nat_mod proof context, where
//     X,Y,Z,W are nat_mod(_,_) terms opaque to the linear core).
//
// Runs against the real corpus-installed NatLemmaBundle with no placeholder
// fabricator in this test binary, so a green run also proves the close is SOUND
// (a placeholder leaf would panic).
func TestApplyStep_Arith_ClosesACEqualities(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	closes := func(t *testing.T, goalStr string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)

		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)

		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		assert.True(t, out.Success, "%s: arith should succeed", goalStr)
		require.NotNil(t, out.State, "%s: success without State", goalStr)
		assert.True(t, out.State.Complete, "%s: proof should be complete in ONE arith move", goalStr)
	}

	// --- 4-atom additive AC rearrangement ---------------------------------
	t.Run("add-AC 4-atom, plain vars", func(t *testing.T) {
		closes(t, "a:num, b:num, c:num, d:num ⊢ (a + b) + (c + d) = (b + d) + (a + c)")
	})
	// Faithful to the context nat_div_mod's residue-of-a-sum law is proved in: the atoms are nat_mod(_,_) terms,
	// opaque to the linear core but treated as indeterminates by the normal form.
	t.Run("add-AC 4-atom, nat_mod atoms", func(t *testing.T) {
		closes(t, "a:num, b:num, c:num, d:num, n:num ⊢ "+
			"(nat_mod(a, n) + b) + (c + nat_mod(d, n)) = (b + nat_mod(d, n)) + (nat_mod(a, n) + c)")
	})

	// --- multiplicative AC rearrangement ----------------------------------
	t.Run("mult-AC 4-atom, plain vars", func(t *testing.T) {
		closes(t, "a:num, b:num, c:num, d:num ⊢ (a * b) * (c * d) = (b * d) * (a * c)")
	})
	t.Run("mult-AC 4-atom, nat_mod atoms", func(t *testing.T) {
		closes(t, "a:num, b:num, c:num, d:num, n:num ⊢ "+
			"(nat_mod(a, n) * b) * (c * nat_mod(d, n)) = (b * nat_mod(d, n)) * (nat_mod(a, n) * c)")
	})
}

// TestAssert_KeepsATautologousDisjunctionForSplitDisj: `assert` of the
// dichotomy `(a≤b) ∨ (b≤a)` installs the disjunction as written, and
// `split_disj` then splits it into the two case branches. The arith
// decider reads such a disjunction as ⊤; an assert that ran it on its
// residual would leave nothing to split.
//
// Goal shape `R:num→num→bool, a:num, b:num ⊢ R(a,b)`: R(a,b) is opaque to arith
// (R is a free predicate var), so nothing auto-decides the conclusion, and a,b
// appear in the conclusion so `assert`'s goal-local scope resolves them.
func TestAssert_KeepsATautologousDisjunctionForSplitDisj(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	// Expected terms, parsed in the same a:num,b:num scope (free vars match by
	// name/type, so AlphaEquals holds across parses).
	term := func(goalStr string) core.Term {
		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse %q: %v", goalStr, res.Errors)
		return res.Prop.Conclusion()
	}
	disj := term("a:num, b:num ⊢ (a <= b) ∨ (b <= a)")
	aLeB := term("a:num, b:num ⊢ a <= b")
	bLeA := term("a:num, b:num ⊢ b <= a")

	hasHyp := func(g GoalView, want core.Term) bool {
		for _, h := range g.Hypotheses {
			if h.AlphaEquals(want) {
				return true
			}
		}
		return false
	}

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("R:num->num->bool, a:num, b:num ⊢ R(a, b)")
	require.Empty(t, res.Errors, "parse goal: %v", res.Errors)
	origConcl := res.Prop.Conclusion() // R(a,b)
	gid := s.AddGoal(res.Prop)

	// Step 1: assert the dichotomy. Produces [obligation ⊢ D] and [D ⊢ R(a,b)].
	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "assert", ClaimText: "(a <= b) ∨ (b <= a)"}})
	require.NoError(t, err)
	require.True(t, out.Success, "assert should succeed")
	require.NotNil(t, out.State)
	require.Len(t, out.State.Goals, 2, "assert yields obligation + residual")

	// The residual is the goal carrying the disjunction as a hyp.
	var residual *GoalView
	for i := range out.State.Goals {
		if hasHyp(out.State.Goals[i], disj) {
			residual = &out.State.Goals[i]
		}
	}
	require.NotNil(t, residual, "one subgoal must carry the disjunction hyp")
	// The disjunction was introduced INTACT — not rewritten/collapsed by assert
	// (hasHyp(disj) above already established the hyp is the verbatim disjunction).
	// And the residual is the original goal R(a,b), not the obligation ⊢ D.
	assert.True(t, residual.Statement.Conclusion().AlphaEquals(origConcl),
		"residual conclusion should be the original goal R(a,b)")
	assert.False(t, residual.Statement.Conclusion().AlphaEquals(disj),
		"residual must be the goal-with-hyp, not the prove-the-dichotomy obligation")

	// Step 2: split_disj on the residual — NO arith/auto in between.
	out2, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: residual.ID, Tactic: TacticReq{Type: "split_disj"}})
	require.NoError(t, err)
	require.True(t, out2.Success, "split_disj should fire on the disjunction hyp")
	require.NotNil(t, out2.State)

	// Among all open goals, exactly the two case branches must appear: one with
	// `a≤b`, one with `b≤a`, both concluding the original R(a,b); neither still
	// carries the whole disjunction (split_disj consumed it).
	gotALeB, gotBLeA := false, false
	for _, g := range out2.State.Goals {
		if hasHyp(g, aLeB) && !hasHyp(g, disj) {
			gotALeB = true
			t.Logf("branch a≤b: hyps=%d concl matches original=%v", len(g.Hypotheses), g.Statement.Conclusion().AlphaEquals(origConcl))
		}
		if hasHyp(g, bLeA) && !hasHyp(g, disj) {
			gotBLeA = true
			t.Logf("branch b≤a: hyps=%d", len(g.Hypotheses))
		}
	}
	assert.True(t, gotALeB, "expected a branch with the `a≤b` hyp")
	assert.True(t, gotBLeA, "expected a branch with the `b≤a` hyp")
}

// Regression guard for the arith dist+linear-equality-hyp divergence — the
// dist-triangle goal `nat_dist(a,b) ≤ nat_dist(p,q) + nat_dist(r,s) + nat_dist(u,v)` with
// hypotheses `(r+u)=(p+a)` and `(s+v)=(q+b)`.
// The interesting properties of this single goal:
//
//	(a) 8 monus atoms after the dist→monus bridge — enough for FM's
//	    index-order elimination to hit its doubly-exponential worst case;
//	(b) two linear equality hyps linking operand sums — keeps every
//	    proveSplit branch's linear core satisfiable-but-not-refutable, so the
//	    failing-refute direction runs full elimination on every branch.
func TestApplyStep_Arith_DistTriangleWithLinearEqualityHyps(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
	s, _ := e.getSession(info.ID)

	goal := "" +
		"a:num, b:num, p:num, q:num, r:num, s:num, u:num, v:num, " +
		"(r + u) = (p + a), (s + v) = (q + b) " +
		"⊢ nat_dist(,(a, b)) <= (nat_dist(,(p, q)) + nat_dist(,(r, s))) + nat_dist(,(u, v))"

	res := dsl.ParsePropText(goal)
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "arith"}})
	require.NoError(t, err)
	require.True(t, out.Success, "arith should succeed on the dist-triangle goal")
	require.True(t, out.State.Complete, "arith should CLOSE the dist-triangle goal")
}

// TestApplyStep_Arith_ClosesRealGoals is the ℝ twin of
// TestApplyStep_Arith_ClosesBooleanGoals — the empirical proof that the engine
// `arith` move closes REAL goals once goalHasArithContent recognizes real
// content (gated on a real bundle) and the unified ArithDecideWithHyps
// dispatches real. InstallRealBundle binds a REAL theorem for every leaf (no
// placeholder fabricator in this test binary), so a green run is end-to-end SOUND:
// real bool-split + ring + linarith, every leaf real-backed, closing real goals through the engine.
func TestApplyStep_Arith_ClosesRealGoals(t *testing.T) {
	installTestNatBundle() // the of_num bridge lifts real numerals to the num evaluator
	installTestRealBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
		setTestRealBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	apply := func(t *testing.T, tac, goalStr string) *StepResult {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)
		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)
		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: tac}})
		require.NoError(t, err)
		return out
	}

	positives := []string{
		// linear comparison closed by the linear core
		"x:real, y:real, z:real, x <= y, y <= z ⊢ x <= z",
		// ⇒ nested inside ∨ (valid via transitivity) — the real bool-split
		"x:real, y:real, z:real ⊢ (x <= y => x <= z) \\/ (z < y)",
		// nested real trichotomy
		"x:real, y:real ⊢ (x < y) \\/ ((x = y) \\/ (y < x))",
		// ⇒ to a disjunctive consequent
		"x:real, y:real ⊢ (x <= y) => ((x < y) \\/ (x = y))",
		// ⇔ between compound boolean combinations (real antisymmetry)
		"x:real, y:real ⊢ (x <= y /\\ y <= x) <=> (x = y)",
		// ring equality folded in
		"x:real, y:real ⊢ x + y = y + x",
	}
	for _, goalStr := range positives {
		for _, tac := range []string{"arith", "auto"} {
			t.Run(tac+": "+goalStr, func(t *testing.T) {
				out := apply(t, tac, goalStr)
				assert.True(t, out.Success, "%s via %s should succeed", goalStr, tac)
				require.NotNil(t, out.State, "%s via %s: success without State", goalStr, tac)
				assert.True(t, out.State.Complete, "%s via %s: proof should be complete", goalStr, tac)
			})
		}
	}

	t.Run("arith declines invalid real boolean", func(t *testing.T) {
		// (x<y) ∨ (x=y) is false whenever y<x — must not falsely close.
		out := apply(t, "arith", "x:real, y:real ⊢ (x < y) \\/ (x = y)")
		assert.False(t, out.Success, "invalid real boolean must NOT close")
	})
}

// TestApplyStep_Arith_RealGatedOff confirms the shape gate's coupling: with no
// real bundle installed, goalHasArithContent returns false for a pure-real
// goal, so the `arith` move does not close it (Success=false) — the same shape
// the gate-on test above turns into a successful close. A serve installs the
// real bundle; the off arm is an engine built without one.
func TestApplyStep_Arith_RealGatedOff(t *testing.T) {
	installTestNatBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
	})
	require.False(t, omega.RealArithEnabled(), "no real bundle ⇒ real arith disabled")
	e := newEngine(testEnv())
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
	s, _ := e.getSession(info.ID)
	res := dsl.ParsePropText("x:real, y:real, z:real, x <= y, y <= z ⊢ x <= z")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	for _, tac := range []string{"arith", "auto"} {
		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: tac}})
		require.NoError(t, err)
		assert.False(t, out.Success, "%s must not close a real goal with no real bundle", tac)
	}
}

// TestApplyStep_Arith_NatUnaffectedByRealBundle is the regression-safety check
// for production wiring: installing the real bundle ALONGSIDE the nat bundle must
// not change how the `arith` move handles NAT goals — the real leaves
// short-circuit on a nat atom before reading any real field. A nat goal closes
// exactly as it would nat-bundle-only, and a goal MIXING num and real atoms
// closes by per-atom dispatch (each domain's leaves on its own atoms) in one
// engine `arith` pass.
func TestApplyStep_Arith_NatUnaffectedByRealBundle(t *testing.T) {
	installTestNatBundle()
	installTestRealBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
		setTestRealBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	apply := func(t *testing.T, tac, goalStr string) *StepResult {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)
		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)
		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: tac}})
		require.NoError(t, err)
		return out
	}

	goals := []string{
		// pure NAT goal — must still close with the real bundle co-installed
		"a:num, b:num, c:num, a <= b, b <= c ⊢ a <= c",
		"a:num, b:num ⊢ a + b = b + a",
		// MIXED num + real atoms — one arith pass dispatches each to its domain
		"(2 + 3 = 5) /\\ (&2 + &3 = &5)",
		"a:num, x:real ⊢ (a < a + 1) /\\ (x <= x + &1)",
	}
	for _, g := range goals {
		for _, tac := range []string{"arith", "auto"} {
			t.Run(tac+": "+g, func(t *testing.T) {
				out := apply(t, tac, g)
				assert.True(t, out.Success, "%s via %s should close", g, tac)
				require.NotNil(t, out.State, "%s via %s: success without State", g, tac)
				assert.True(t, out.State.Complete, "%s via %s: should be complete", g, tac)
			})
		}
	}
}

// TestApplyStep_Arith_ClosesSubNegGeForms pins the move-across leaves in the
// UNIFIED arith composition (omega composeArithLeaves / NewArithCtx): a
// `≥`/`>` bridge or a total-subtraction/negation atom must be normalized to
// the positive two-sided `<`/`≤` form before the decide leaf's linear
// extractor runs. The dedicated per-domain stacks (realArithDecideWithHypsRaw,
// intComposeArithLeavesWith) always carried these leaves; the unified
// tactic-level dispatch once omitted them, so the engine `arith` move
// declined pure linear goals like `M ≤ M − &1 ⇔ −&1 ≥ &0` that omega's
// RealArithDecide closes directly. Mirrors the production serve setup
// (all three bundles installed).
func TestApplyStep_Arith_ClosesSubNegGeForms(t *testing.T) {
	installTestNatBundle()
	installTestRealBundle()
	serve.InstallIntBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
		setTestRealBundle(nil)
		omega.SetIntLemmaBundle(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	run := func(goalStr string) {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
		s, _ := e.getSession(info.ID)

		res := dsl.ParsePropText(goalStr)
		require.Empty(t, res.Errors, "parse: %v", res.Errors)
		gid := s.AddGoal(res.Prop)

		out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: gid, Tactic: TacticReq{Type: "arith"}})
		require.NoError(t, err)
		require.True(t, out.Success, "%s: arith should succeed", goalStr)
		assert.True(t, out.State.Complete, "%s: proof should be complete", goalStr)
	}

	// The shape that surfaced the gap (stated form, ground):
	// an iff between a subtraction atom and a negation-≥ atom.
	run("M:real ⊢ (M <= M - &1) = (-&1 >= &0)")
	// The normalized-form sibling (iff sides swapped).
	run("M:real ⊢ (-&1 >= &0) = (M <= M - &1)")
	// Control: the pre-normalized residual (no sub/neg/ge) — closed even
	// without the move-across leaves.
	run("M:real ⊢ (M + &1 <= M) = (&1 <= &0)")
	// The int twin — intMoveAcrossLeaf was missing from the unified path too.
	run("x:int ⊢ ~(x <= x - &1)")
}

// TestApplyStep_Arith_IntSgnPiecewise_NoFabricator: the int_sgn / int_max /
// int_min piecewise-def leaves through the ENGINE ApplyStep path, in
// PRODUCTION posture (all three corpus bundles installed, and no
// placeholder fabricator, which this test binary never installs).
// SgnDef/MaxDef/MinDef bind via liftReal(defNorm(...)); a lift
// that left real_of_int residue on the COND branches would crash every
// arith-content RPC on a session goal carrying a bare int_sgn/int_max/int_min
// at the placeholder seam, and omega's condPushRealOfInt is what completes it
// (see TestInstallIntLemmaBundleBindingLeafSeams in
// library/serve/int_bundle_test.go).
//
// The goals are built programmatically with the REAL const metas: a DSL text
// parse in this test binary resolves `int_sgn` as a free variable, which the
// omega matchers rightly ignore — production goals, parsed against the
// registry's constants, carry the const.
func TestApplyStep_Arith_IntSgnPiecewise_NoFabricator(t *testing.T) {
	installTestNatBundle()
	installTestRealBundle()
	serve.InstallIntBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
		setTestRealBundle(nil)
		omega.SetIntLemmaBundle(nil)
		omega.SetIntBridges(nil)
	})
	e := newEngine(testEnv())
	ctx := context.Background()

	n := ext.Var("n", dsl.IntType)
	ilit := func(v uint64) core.Term { return ext.Apply(dsl.IntOfNumMeta.Term(), omega.Numeral(v)) }
	sgn := func(a core.Term) core.Term { return ext.Apply(dsl.IntSgnMeta.Term(), a) }
	imax := func(a, b core.Term) core.Term { return ext.Apply(dsl.IntMaxMeta.Term(), a, b) }

	run := func(name string, concl core.Term, tacs []string, wantComplete bool) {
		t.Run(name, func(t *testing.T) {
			for _, tac := range tacs {
				info, err := e.CreateSession(ctx)
				require.NoError(t, err)
				t.Cleanup(func() { _ = e.CloseSession(ctx, info.ID) })
				s, _ := e.getSession(info.ID)
				gid := s.AddGoal(prop.MakeProp(concl))
				// The move either closes or declines cleanly: a panic at
				// the placeholder seam comes back as an engine fault.
				out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
					GoalID: gid, Tactic: TacticReq{Type: tac}})
				require.NoError(t, err, "%s should not error", tac)
				require.Nil(t, out.EngineFault, "%s met an engine fault", tac)
				if wantComplete {
					require.True(t, out.Success, "%s should succeed", tac)
					assert.True(t, out.State.Complete, "%s should CLOSE the goal", tac)
				}
			}
		})
	}

	// Ground piecewise goals: a real decide is expected.
	run("sgn(&5) = &1 closes", core.Eq(sgn(ilit(5)), ilit(1)), []string{"arith", "auto"}, true)
	run("max(&1,&2) = &2 closes", core.Eq(imax(ilit(1), ilit(2)), ilit(2)), []string{"arith"}, true)
	// Contingent symbolic goal (an int_sgn(n) trigger shape): not
	// closable, but must decline/advance WITHOUT the placeholder-seam panic.
	run("sgn(n) = &1 no panic", core.Eq(sgn(n.Core()), ilit(1)), []string{"arith", "auto"}, false)
}
