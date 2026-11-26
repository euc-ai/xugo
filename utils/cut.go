// cut.go — a run its context ended, unwound to the owner of the run.

package utils

import (
	"context"
	"errors"
	"fmt"
)

// Cut is the panic a computation raises inside one of its units of work
// when the context it polls is done: a budget or a deadline passed, or
// the caller went away. It is neither the computation's failure nor a
// fault. Nothing was decided, so the owner of the run (the step, the
// probe, the request) reads it as "cut off" and never as "does not
// apply". Failure raises it again for that reason.
//
// The cut is a panic because a unit returning nil would read as an
// answer: a memo would keep it, and a fixpoint would stop at it. A
// panic leaves no answer for anything on the way to the owner.
type Cut struct {
	// Where names the unit of work the cut came before.
	Where string
	// Cause is the context's error.
	Cause error
}

func (c Cut) Error() string {
	return fmt.Sprintf("cut off %s: %v", c.Where, c.Cause)
}

// AsCut is the Cut a recovered panic value is, or wraps as an error.
func AsCut(r any) (Cut, bool) {
	if cut, ok := r.(Cut); ok {
		return cut, true
	}
	var cut Cut
	if err, ok := r.(error); ok && errors.As(err, &cut) {
		return cut, true
	}
	return cut, false
}

// Stopper is the poll of ctx for a loop that polls often. It returns nil
// where ctx is never done (context.Background(), a replay's context),
// and the caller then skips the poll. The poll reads ctx's Done channel,
// which costs a few nanoseconds while the channel is open.
func Stopper(ctx context.Context) func(where string) {
	if ctx == nil {
		return nil
	}
	done := ctx.Done()
	if done == nil {
		return nil
	}
	return func(where string) {
		select {
		case <-done:
			panic(Cut{Where: where, Cause: ctx.Err()})
		default:
		}
	}
}
