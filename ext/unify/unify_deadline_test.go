package unify

import (
	"context"
	"runtime"
	"testing"
	"time"

	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// A Unify under a caller's deadline runs on the calling goroutine
// alone, as it does under the work budget. The CNF refuter runs
// thousands of such searches at once; a pool of workers per fan-out of
// the search tree, nested at every level, multiplied them into
// hundreds of thousands of goroutines, and under load the runtime then
// saw the deadline late and unwound for hours with the session locked.
//
// The problem fans out at every level: F against f(g(a, b), g(b, a))
// offers an imitation and two projections, and each imitation's fresh
// heads do the same against g's arguments. A sampler watches the
// goroutine count while the searches run; the only goroutine above the
// baseline must be the sampler itself.
func TestUnify_DeadlineSearchIsOneGoroutine(t *testing.T) {
	defer goleak.VerifyNone(t)

	a, b := Var("a", TypeA), Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA, TypeA))
	F := Var("F", MakeFun(TypeA, TypeA, TypeA))
	ground := func(n TermName) bool { return n == "a" || n == "b" || n == "f" || n == "g" }
	s := F.Apply(a).Apply(b)
	u := f.Apply(g.Apply(a).Apply(b)).Apply(g.Apply(b).Apply(a))

	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	defer cancel()
	_, hasDeadline := ctx.Deadline()
	require.True(t, hasDeadline)

	baseline := runtime.NumGoroutine()
	stop := make(chan struct{})
	peakSeen := make(chan int, 1)
	go func() {
		peak := runtime.NumGoroutine()
		for {
			select {
			case <-stop:
				peakSeen <- peak
				return
			default:
				if n := runtime.NumGoroutine(); n > peak {
					peak = n
				}
				time.Sleep(20 * time.Microsecond)
			}
		}
	}()
	var solutions int
	for range 10 {
		substs := Unify(ctx, s, u, utils.EmptyPredicate[VarType], ground)
		require.NotEmpty(t, substs, "the imitation F ↦ λx y. f(g(x, y), g(y, x)) solves the pair")
		solutions = len(substs)
	}
	close(stop)
	peak := <-peakSeen
	t.Logf("%d solutions; goroutines: baseline %d, peak %d while searching", solutions, baseline, peak)
	// The sampler is the one goroutine above the baseline. A search that
	// pooled its branches shows at least eight workers and a collector
	// above it for the whole search.
	require.LessOrEqual(t, peak, baseline+1,
		"a Unify under a deadline spawned goroutines: its branches must run on the calling goroutine")
}
