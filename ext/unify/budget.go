package unify

import (
	"context"
	"errors"
	"os"
	"strconv"
	"sync"
	"time"
)

// ErrBudgetExhausted is returned by _BudgetCtx.Err once the deterministic
// work budget is consumed. Callers treat it exactly like a deadline
// expiry: the in-flight unification is abandoned and reported as
// "no unifier found".
var ErrBudgetExhausted = errors.New("unify: work budget exhausted")

// DefaultUnifyBudget is the deterministic work budget (in poll units)
// installed by Unify when the caller's ctx carries no deadline — the
// population the DefaultUnifyTimeout wall-clock cap covers under
// XUGO_UNIFY_WALLCLOCK=1. One unit is consumed per ctx poll: one β-η node visit
// (utils.CheckCtx) or one explicit ctx.Err() check in the search loops.
//
// Unlike the wall-clock cap, the budget makes Unify a pure function of
// its inputs: the same (s, t) pair either succeeds with the same
// substitutions or fails, regardless of machine load. This is the
// determinism contract that record/replay of lemma steps depends on
// (see the [Lemma,Lemma,Auto] search/replay divergence).
//
// Calibration: the value is chosen so every unify that succeeds within
// the 100ms idle-machine wall-clock cap also succeeds within budget,
// with wide margin.
const DefaultUnifyBudget = 2_000_000

// useWallClock reports whether the wall-clock cap is installed instead
// of the deterministic budget (escape hatch: XUGO_UNIFY_WALLCLOCK=1).
var useWallClock = sync.OnceValue(func() bool {
	return os.Getenv("XUGO_UNIFY_WALLCLOCK") == "1"
})

// unifyBudgetUnits returns the per-call budget, overridable via
// XUGO_UNIFY_BUDGET=<units> (calibration / experiments).
var unifyBudgetUnits = sync.OnceValue(func() int64 {
	if s := os.Getenv("XUGO_UNIFY_BUDGET"); s != "" {
		if n, err := strconv.ParseInt(s, 10, 64); err == nil && n > 0 {
			return n
		}
	}
	return DefaultUnifyBudget
})

// _BudgetCtx is a context.Context whose Err() consumes one unit of a
// deterministic work budget per call and reports ErrBudgetExhausted
// once the budget is gone. All existing poll sites (utils.CheckCtx in
// the β-η hot loops, explicit ctx.Err() checks in tryUnify /
// expandSearchTree) thereby consume budget with zero call-site changes.
//
// Contract notes:
//   - Err() is sticky once exhausted (remaining only decreases).
//   - Done() delegates to the parent: budget exhaustion does NOT close
//     the Done channel. The unify package polls exclusively via Err() /
//     CheckCtx, so this is sufficient here; do not hand a _BudgetCtx to
//     code that selects on Done().
//   - The search runs on the one goroutine that called Unify, so the
//     counter is a plain integer; the fixed order of its consumption
//     is what makes the cut point — and hence the result set —
//     deterministic.
type _BudgetCtx struct {
	parent    context.Context
	remaining int64
}

func newBudgetCtx(parent context.Context, units int64) *_BudgetCtx {
	return &_BudgetCtx{parent: parent, remaining: units}
}

func (b *_BudgetCtx) Deadline() (time.Time, bool) { return b.parent.Deadline() }
func (b *_BudgetCtx) Done() <-chan struct{}       { return b.parent.Done() }
func (b *_BudgetCtx) Value(k any) any             { return b.parent.Value(k) }

func (b *_BudgetCtx) Err() error {
	if err := b.parent.Err(); err != nil {
		return err
	}
	b.remaining--
	if b.remaining < 0 {
		return ErrBudgetExhausted
	}
	return nil
}

// WithWorkBudget returns ctx under the bound Unify installs on a context
// that carries no deadline — the deterministic work budget, or the
// wall-clock cap under XUGO_UNIFY_WALLCLOCK=1 — whether or not ctx
// carries one. It is for a caller whose results are read again by a
// later run that has no deadline (a normal form a recorded key is
// computed from): its calls stop where they stop without a deadline,
// and a deadline on ctx can only end one earlier, which the caller then
// treats as its own context's end and never as "no unifier". A context
// handed to Unify as it is, with a deadline, is cut by that clock alone.
func WithWorkBudget(ctx context.Context) (context.Context, context.CancelFunc) {
	if useWallClock() {
		return context.WithTimeout(ctx, DefaultUnifyTimeout)
	}
	return newBudgetCtx(ctx, unifyBudgetUnits()), func() {}
}

func isBudgetCtx(ctx context.Context) bool {
	_, ok := ctx.(*_BudgetCtx)
	return ok
}
