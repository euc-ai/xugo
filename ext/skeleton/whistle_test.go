package skeleton

import (
	"sync"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/utils"
)

func labelled(name string) func() string { return func() string { return name } }

// A watch sees the cuts of its own goroutine and no other's: two
// goroutines each hold a watch open while one of them reports a cut,
// as two sessions' closes run side by side in the serve. The cut
// reaches the reporting goroutine's watch, named after it, and the
// other watch stays empty — the process counter moved for both.
func TestWhistleWatch_SeesItsOwnGoroutineOnly(t *testing.T) {
	var hooked []WhistleEvent
	var mu sync.Mutex
	OnWhistleFire = func(ev WhistleEvent) {
		mu.Lock()
		defer mu.Unlock()
		hooked = append(hooked, ev)
	}
	t.Cleanup(func() { OnWhistleFire = nil })
	firesBefore := WhistleFires()

	bothOpen, fired := make(chan struct{}), make(chan struct{})
	var open, done sync.WaitGroup
	var quiet, cut []WhistleEvent
	open.Add(2)
	done.Go(func() {
		w := WatchWhistle(labelled("the quiet step"))
		open.Done()
		<-fired
		quiet = w.Close()
	})
	done.Go(func() {
		w := WatchWhistle(labelled("the step that was cut"))
		open.Done()
		<-bothOpen
		ReportWhistleFire(WhistleEvent{Driver: "mergeTactics", Depth: 3, Budget: 2})
		close(fired)
		cut = w.Close()
	})
	open.Wait()
	close(bothOpen)
	done.Wait()

	assert.Empty(t, quiet, "a cut on another goroutine is not this watch's")
	require.Len(t, cut, 1)
	assert.Equal(t, "the step that was cut", cut[0].Step)
	assert.Equal(t, int64(1), WhistleFires()-firesBefore)
	require.Len(t, hooked, 1, "the hook sees every goroutine's cuts")
	assert.Equal(t, "the step that was cut", hooked[0].Step, "and reads whose it was off the event")
}

// With no watch open on the reporting goroutine the event names no
// step; the counter and the hook see it as before.
func TestWhistleWatch_NoWatchNoStep(t *testing.T) {
	var hooked []WhistleEvent
	OnWhistleFire = func(ev WhistleEvent) { hooked = append(hooked, ev) }
	t.Cleanup(func() { OnWhistleFire = nil })

	ReportWhistleFire(WhistleEvent{Driver: "mergeTactics", Depth: 3, Budget: 2})
	require.Len(t, hooked, 1)
	assert.Empty(t, hooked[0].Step)
}

// Watches on one goroutine nest: a cut is named after the innermost and
// delivered to each, and a closed watch receives nothing more.
func TestWhistleWatch_NestsInnermostNames(t *testing.T) {
	outer := WatchWhistle(labelled("outer"))
	inner := WatchWhistle(labelled("inner"))
	ReportWhistleFire(WhistleEvent{Driver: "mergeTactics", Depth: 1})
	assert.Equal(t, 1, outer.Fired())
	innerCuts := inner.Close()
	ReportWhistleFire(WhistleEvent{Driver: "mergeTactics", Depth: 2})
	outerCuts := outer.Close()

	require.Len(t, innerCuts, 1)
	assert.Equal(t, "inner", innerCuts[0].Step)
	require.Len(t, outerCuts, 2)
	assert.Equal(t, "inner", outerCuts[0].Step)
	assert.Equal(t, "outer", outerCuts[1].Step)
	assert.Equal(t, innerCuts, inner.Close(), "a second Close returns the same cuts")
}

// The label is read at a cut and not before: a step that is never cut
// never pays for its name.
func TestWhistleWatch_LabelReadOnlyAtACut(t *testing.T) {
	calls := 0
	w := WatchWhistle(func() string { calls++; return "step" })
	assert.Equal(t, 0, calls)
	ReportWhistleFire(WhistleEvent{Driver: "mergeTactics"})
	assert.Equal(t, 1, calls)
	w.Close()
}

// Closing a watch while one opened inside it is still open is a breach
// of the nesting the table relies on. It panics as a fault: a By opens
// its watch around rungs whose recovers read any other panic as the
// rung's failure, and would go on to the next rung past the breach.
func TestWhistleWatch_ClosedOutOfOrderPanics(t *testing.T) {
	outer := WatchWhistle(labelled("outer"))
	inner := WatchWhistle(labelled("inner"))
	var breach any
	func() {
		defer func() { breach = recover() }()
		outer.Close()
	}()
	require.NotNil(t, breach, "closing the outer watch first did not panic")
	assert.True(t, utils.IsFault(breach), "the breach is read as a failure, not a fault: %v", breach)
	inner.Close()
	outer.Close()
}

// The id read off the stack header tells goroutines apart and is the
// same on every read within one.
func TestGoroutineID(t *testing.T) {
	here := goroutineID()
	assert.Equal(t, here, goroutineID())
	there := make(chan uint64)
	go func() { there <- goroutineID() }()
	assert.NotEqual(t, here, <-there)
}
