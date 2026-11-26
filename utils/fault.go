// fault.go — a panic that marks a defect, as the goroutine that reads
// it sees it, and the fan-out that hands one to its caller.

package utils

import (
	"errors"
	"fmt"
	"runtime"
	"runtime/debug"
	"sync"
)

// Fault is a panic taken off the goroutine it was raised on: the value,
// where it was raised, and that goroutine's stack. A goroutine no caller
// recovers for hands its panic on as one (Tasks, a refutation search),
// so the break is raised where a caller reads it and the process
// outlives it. A Fault is a defect whatever its value: no such goroutine
// panics to report a failure.
type Fault struct {
	// Value is what was panicked with.
	Value any
	// Site is where: "<file>:<line> in <function>".
	Site string
	// Stack is the stack of the goroutine that panicked.
	Stack string
}

func (f Fault) Error() string {
	return fmt.Sprintf("%v\n  at %s", f.Value, f.Site)
}

// RecoveredFault is the Fault a deferred function makes of the panic
// value r it recovered: the Fault r is or wraps, which keeps the site
// and stack of the goroutine that broke through every hand-over, and
// otherwise r with the site and stack of the panic in flight.
func RecoveredFault(r any) Fault {
	if fault, ok := AsFault(r); ok {
		return fault
	}
	return Fault{Value: r, Site: PanicSite(), Stack: string(debug.Stack())}
}

// AsFault is the Fault a recovered panic value is, or wraps as an error.
func AsFault(r any) (Fault, bool) {
	var fault Fault
	if err, ok := r.(error); ok && errors.As(err, &fault) {
		return fault, true
	}
	return fault, false
}

// IsFault reports whether a recovered panic value marks a defect: a
// Fault handed on from another goroutine, or, raised on this one, a
// failed assertion or an error of the Go runtime (a nil dereference, an
// index out of range, a failed type assertion), as it is or wrapped in
// an error. No code panics with a runtime error to report a failure.
func IsFault(r any) bool {
	_, carried := AsFault(r)
	return carried || IsAssertionFailure(r) || isRuntimeError(r)
}

// isRuntimeError reports whether a recovered panic value is, or wraps
// as an error, an error of the Go runtime.
func isRuntimeError(r any) bool {
	var broke runtime.Error
	err, ok := r.(error)
	return ok && errors.As(err, &broke)
}

// Failure reads the panic value a deferred function recovered where a
// panic is how its callee reports a failure: a fault is raised again as
// it is, since a caller that went on after it would hide the break, and
// so is a Cut, which is no failure but a run that did not end; any
// other value is the failure. It returns nil when nothing panicked.
func Failure(r any) any {
	if _, cut := AsCut(r); cut || IsFault(r) {
		panic(r)
	}
	return r
}

// Tasks is a sync.WaitGroup for a fan-out whose caller waits for it: a
// panic in a task does not end the process, the other tasks run to
// their end, and Wait raises the first such panic again, as a Fault, on
// the goroutine that waits. The zero value is ready to use.
type Tasks struct {
	group sync.WaitGroup
	mu    sync.Mutex
	fault *Fault
}

// Go runs task on a goroutine of its own.
func (t *Tasks) Go(task func()) {
	t.group.Go(func() {
		defer func() {
			if r := recover(); r != nil {
				fault := RecoveredFault(r)
				t.mu.Lock()
				defer t.mu.Unlock()
				if t.fault == nil {
					t.fault = &fault
				}
			}
		}()
		task()
	})
}

// Wait returns when every task has, and raises the first panic among
// them. A fault is raised once: a later Wait returns.
func (t *Tasks) Wait() {
	t.group.Wait()
	t.mu.Lock()
	fault := t.fault
	t.fault = nil
	t.mu.Unlock()
	if fault != nil {
		panic(*fault)
	}
}
