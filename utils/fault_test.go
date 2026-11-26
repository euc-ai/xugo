package utils_test

import (
	"errors"
	"fmt"
	"strings"
	"sync/atomic"
	"testing"

	"github.com/euc-ai/xugo/utils"
)

// raised runs f and returns what it panicked with, nil when it returned.
func raised(f func()) (r any) {
	defer func() { r = recover() }()
	f()
	return nil
}

func breakInATask() { utils.Assert(false) }

// TestTasks_WaitRaisesATasksPanicOnTheWaiter: a task that panics does
// not end the process; its siblings run to their end, and Wait raises
// the panic on the goroutine that waits, as a Fault with the value, the
// site of the raise and the stack of the task's goroutine.
func TestTasks_WaitRaisesATasksPanicOnTheWaiter(t *testing.T) {
	var done atomic.Int32
	tasks := utils.Tasks{}
	tasks.Go(func() { done.Add(1) })
	tasks.Go(breakInATask)
	tasks.Go(func() { done.Add(1) })

	fault, ok := raised(tasks.Wait).(utils.Fault)
	if !ok {
		t.Fatal("Wait did not raise the task's panic as a Fault")
	}
	if done.Load() != 2 {
		t.Errorf("%d of the 2 other tasks ran to their end", done.Load())
	}
	if !utils.IsAssertionFailure(fault.Value) {
		t.Errorf("the fault's value is the task's panic value, got %v", fault.Value)
	}
	if !strings.Contains(fault.Site, "fault_test.go:") || !strings.Contains(fault.Site, "breakInATask") {
		t.Errorf("the site names the raise, got %q", fault.Site)
	}
	if !strings.Contains(fault.Stack, "breakInATask") {
		t.Errorf("the stack is the task goroutine's, got:\n%s", fault.Stack)
	}
	if raised(tasks.Wait) != nil {
		t.Error("a fault is raised once: a second Wait returns")
	}
}

// TestTasks_WaitReturnsWhenNoTaskPanicked: the ordinary fan-out.
func TestTasks_WaitReturnsWhenNoTaskPanicked(t *testing.T) {
	var done atomic.Int32
	tasks := utils.Tasks{}
	for range 8 {
		tasks.Go(func() { done.Add(1) })
	}
	if r := raised(tasks.Wait); r != nil {
		t.Fatalf("Wait raised %v", r)
	}
	if done.Load() != 8 {
		t.Errorf("%d of 8 tasks ran", done.Load())
	}
}

// TestTasks_AFaultHandedOnTwiceKeepsTheStackOfItsGoroutine: a fan-out
// inside a task of another hands its fault to the outer waiter as it
// is, so the record still shows the goroutine that broke.
func TestTasks_AFaultHandedOnTwiceKeepsTheStackOfItsGoroutine(t *testing.T) {
	outer := utils.Tasks{}
	outer.Go(func() {
		inner := utils.Tasks{}
		inner.Go(breakInATask)
		inner.Wait()
	})
	fault, ok := raised(outer.Wait).(utils.Fault)
	if !ok {
		t.Fatal("the outer Wait did not raise a Fault")
	}
	if !utils.IsAssertionFailure(fault.Value) {
		t.Errorf("the value is the first panic's, not a Fault wrapped in a Fault: %v", fault.Value)
	}
	if !strings.Contains(fault.Site, "breakInATask") || !strings.Contains(fault.Stack, "breakInATask") {
		t.Errorf("site %q and stack name the inner task", fault.Site)
	}
}

type _WrappedFault struct{ utils.Fault }

func (w _WrappedFault) Unwrap() error { return w.Fault }

// runtimeErrors are the panics of the Go runtime as a recover reads
// them, by what broke.
func runtimeErrors() map[string]any {
	return map[string]any{
		"a nil dereference": raised(func() {
			var p *struct{ field int }
			_ = p.field
		}),
		"an index out of range": raised(func() {
			var s []int
			_ = s[len(s)]
		}),
		"a failed type assertion": raised(func() {
			var v any = "a string"
			_ = v.(int)
		}),
		"a write to a nil map": raised(func() {
			var m map[string]int
			m["key"] = 1
		}),
	}
}

// TestFailure_RaisesAFaultAgainAndReturnsAFailure: a recover that reads
// a panic as its callee's failure lets a fault pass: a carried Fault, an
// error that wraps one, a failed assertion and an error of the Go
// runtime are raised again as they are; any other value is the failure,
// and nil is no panic.
func TestFailure_RaisesAFaultAgainAndReturnsAFailure(t *testing.T) {
	fault := utils.Fault{Value: "boom", Site: "x.go:1 in f"}
	if r := raised(func() { utils.Failure(fault) }); r != fault {
		t.Errorf("a Fault is raised again as it is, got %v", r)
	}
	wrapped := _WrappedFault{fault}
	if r := raised(func() { utils.Failure(wrapped) }); r != wrapped {
		t.Errorf("an error wrapping a Fault is raised again as it is, got %v", r)
	}
	breach := raised(func() { utils.Assert(false) })
	if r := raised(func() { utils.Failure(breach) }); r != breach {
		t.Errorf("a failed assertion is raised again, got %v", r)
	}
	for name, broke := range runtimeErrors() {
		if r := raised(func() { utils.Failure(broke) }); r != broke {
			t.Errorf("%s is raised again as it is, got %v", name, r)
		}
	}
	if got := utils.Failure("the tactic did not apply"); got != "the tactic did not apply" {
		t.Errorf("an ordinary panic value is the failure, got %v", got)
	}
	if err := errors.New("not a fault"); utils.Failure(err) != err {
		t.Error("an error that wraps no Fault is the failure")
	}
	if utils.Failure(nil) != nil {
		t.Error("no panic, no failure")
	}
}

// TestIsFault: the forms a fault takes on the goroutine that reads it.
func TestIsFault(t *testing.T) {
	for name, broke := range runtimeErrors() {
		if !utils.IsFault(broke) {
			t.Errorf("%s is a fault, got IsFault(%v) = false", name, broke)
		}
		if wrapped := fmt.Errorf("By: the close failed: %w", broke.(error)); !utils.IsFault(wrapped) {
			t.Errorf("an error wrapping %s is a fault", name)
		}
	}
	for _, row := range []struct {
		r    any
		want bool
	}{
		{utils.Fault{Value: "boom"}, true},
		{_WrappedFault{utils.Fault{Value: "boom"}}, true},
		{utils.AssertionFailed + " (at x.go:1 in f)", true},
		{"By: CnfRefute failed", false},
		{fmt.Errorf("an error"), false},
		{nil, false},
	} {
		if got := utils.IsFault(row.r); got != row.want {
			t.Errorf("IsFault(%v) = %v, want %v", row.r, got, row.want)
		}
	}
}

func raiseHere() { panic("the first raise") }

// TestPanicSite_NamesTheFirstRaise: a recover that raises its panic
// again is not where the panic came from; the site stays the first
// raise's through the recovers on the way.
func TestPanicSite_NamesTheFirstRaise(t *testing.T) {
	var site string
	func() {
		defer func() {
			recover()
			site = utils.PanicSite()
		}()
		func() {
			defer func() { panic(recover()) }()
			raiseHere()
		}()
	}()
	if !strings.Contains(site, "fault_test.go:") || !strings.Contains(site, "raiseHere") {
		t.Errorf("the site names the first raise, got %q", site)
	}
}
