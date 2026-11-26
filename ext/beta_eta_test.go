package ext

// Regression tests for the size-gated shared-DAG memo in the β-η
// walkers (BetaCollapse / BetaEtaNormalize). Same bug family as the
// HasName / FindTopSubTerm memo fixes: β-substitution pointer-shares
// the argument at every occurrence of the bound var, so nested
// duplicating redexes produce a term whose naive tree size is
// exponential in nesting depth while the unique-node count stays
// linear. The unmemoized walk visits per-path (O(2^n)); the memoized
// walk visits per-unique-node.

import (
	"context"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
)

// buildDupRedexChain builds u_n = (λx. d(x,x))(u_{n-1}), u_0 = seed.
// Collapsing u_n yields a complete binary tree of d's of depth n over
// seed — naive size ~2^n * |seed| — but the collapsed result is a
// shared DAG with O(n) unique nodes (each level shares its two
// children pointers).
func buildDupRedexChain(n int, seedSize int) core.Term {
	a := core.MakeVarType("A")
	h := core.Var("h", core.MakeFun(a, a))
	d := core.Var("d", core.MakeFun(a, core.MakeFun(a, a)))
	x := core.Var("x", a)

	// seed = h(h(...h(x)...)) with seedSize applications.
	seed := core.Term(core.Var("v", a))
	for i := 0; i < seedSize; i++ {
		seed = core.Apply(h, seed)
	}

	dup := core.Abs(x, core.Apply(core.Apply(d, x), x))
	u := seed
	for i := 0; i < n; i++ {
		u = core.Apply(dup, u)
	}
	return u
}

// naiveBetaCollapse is BetaCollapse's recursion without the memo, kept
// in the test as the measurement baseline: TestBetaCollapseTrend times
// it against the memoized production walker on the same inputs so the
// exponential naive-vs-linear-memo gap is measured, not asserted from
// folklore.
func naiveBetaCollapse(ctx context.Context, t core.Term) core.Term {
	switch t := t.Core().(type) {
	case core.VarTerm, core.ConstTerm:
		return t
	case core.AppliedTerm:
		if tFun, ok := t.Fun().AsAbsTerm(); ok {
			tArg := naiveBetaCollapse(ctx, t.Arg())
			if tFun.Var().Equals(tArg) {
				return naiveBetaCollapse(ctx, tFun.Body())
			}
			return naiveBetaCollapse(ctx, tFun.Body().Substitute(
				core.MakeTermSubst(tFun.Var(), tArg)))
		}
		fun, arg := naiveBetaCollapse(ctx, t.Fun()), naiveBetaCollapse(ctx, t.Arg())
		if !fun.Equals(t.Fun()) || !arg.Equals(t.Arg()) {
			return naiveBetaCollapse(ctx, core.Apply(fun, arg))
		}
		return t
	case core.AbsTerm:
		if s := naiveBetaCollapse(ctx, t.Body()); !s.Equals(t.Body()) {
			return core.Abs(t.Var(), s)
		}
		return t
	default:
		panic("Wrong term type.")
	}
}

// TestBetaCollapseTrend measures the naive walk against the memoized
// one on growing depths, logging the exponential-vs-flat trend.
// The naive side is capped at n=16 to keep the test fast; each +2 levels
// multiplies the naive time ×4 (per-path walk over the shared DAG).
func TestBetaCollapseTrend(t *testing.T) {
	for _, n := range []int{10, 12, 14, 16} {
		u := buildDupRedexChain(n, 128)
		start := time.Now()
		naiveBetaCollapse(context.Background(), u)
		naive := time.Since(start)
		start = time.Now()
		BetaCollapse(context.Background(), u)
		memo := time.Since(start)
		t.Logf("n=%d naive=%v memo=%v", n, naive, memo)
	}
}

// TestBetaCollapseSharedDAGMemo pins the fix: BetaCollapse on a
// depth-24 duplicating-redex chain (collapsed naive size ~2^24 * 130 ≈
// 2*10^9 — hang-class unmemoized; see TestBetaCollapseTrend for the
// measured naive trend) must return in interactive time. The watchdog
// fails the test rather than letting `go test` hit its global timeout,
// so a regression reads as THIS test's failure.
func TestBetaCollapseSharedDAGMemo(t *testing.T) {
	for _, n := range []int{14, 16, 18, 24} {
		u := buildDupRedexChain(n, 128)
		done := make(chan core.Term, 1)
		start := time.Now()
		go func() { done <- BetaCollapse(context.Background(), u) }()
		select {
		case r := <-done:
			t.Logf("n=%d collapsed in %v (result naive size %d)", n, time.Since(start), r.Size())
			// Sanity: the collapsed form must be redex-free and huge in
			// naive size (2^n * seed), proving we actually collapsed.
			if r.Size() <= u.Size() {
				t.Fatalf("n=%d: collapsed size %d not larger than input %d — dup redexes not expanded?", n, r.Size(), u.Size())
			}
		case <-time.After(30 * time.Second):
			t.Fatalf("BetaCollapse(n=%d) exceeded 30s — shared-DAG memo regression (naive per-path walk)", n)
		}
	}
}

// TestBetaEtaNormalizeSharedDAGMemo is the same guard for the
// BetaEtaNormalize entry (the walker HO-unify calls per pair — the one
// that burned in the def_expand(set_comprehension) profile).
func TestBetaEtaNormalizeSharedDAGMemo(t *testing.T) {
	u := buildDupRedexChain(24, 128)
	done := make(chan core.Term, 1)
	start := time.Now()
	go func() { done <- BetaEtaNormalize(context.Background(), u) }()
	select {
	case r := <-done:
		t.Logf("n=24 normalized in %v (result naive size %d)", time.Since(start), r.Size())
	case <-time.After(30 * time.Second):
		t.Fatal("BetaEtaNormalize(n=24) exceeded 30s — shared-DAG memo regression")
	}
}
