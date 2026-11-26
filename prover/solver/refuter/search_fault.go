package refuter

import (
	"context"
	"fmt"
	"sync"

	"github.com/euc-ai/xugo/utils"
)

// SearchFault is what a refutation search raises in place of its answer
// when one of its goroutines panicked. The clause rules and the proof
// builder panic on a broken invariant and on nothing else, so a search
// that met one is trusted with nothing it found, before or after the
// break. The panic is caught on the goroutine where it happens
// (_FaultSlot.guard, setProof), which the process survives; the fault
// is raised again on the goroutine that asked for the search (search),
// so the By, the set driver or the CnfRefute step that owns it ends
// with the fault as its cause, and a recorder refuses the member's
// blob.
type SearchFault struct {
	// Fault is the panic: its value, where it was raised, and the stack
	// of the goroutine that raised it.
	utils.Fault
	// Goal is the sequent the refutation ran on.
	Goal Prop
}

func (f SearchFault) Error() string {
	return fmt.Sprintf("refuter: a goroutine of the search panicked and the refutation is abandoned "+
		"(nothing the search found is trusted): %v\n  at %s", f.Value, f.Site)
}

// Unwrap is the carried panic, so a reader of faults finds it
// (utils.AsFault).
func (f SearchFault) Unwrap() error { return f.Fault }

// _FaultSlot is where the goroutines of one search leave the first
// panic among them, with the search's own stop: shared by a state and
// its sub-states like the cache, written by guard and setProof, and
// read by search when the search has returned.
type _FaultSlot struct {
	mu    sync.Mutex
	fault *utils.Fault
	stop  context.CancelFunc
	// answered: the search has returned. A task still running then (a
	// contradiction check of the detached pool) has no search left to
	// raise its panic, and hands it to late.
	answered bool
	late     func(utils.Fault)
}

// arm installs the cancel of the search's context, so a fault recorded
// from then on stops the search, and where a fault goes that is
// recorded after the search has answered.
func (s *_FaultSlot) arm(stop context.CancelFunc, late func(utils.Fault)) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.stop, s.late = stop, late
}

// guard is task as a goroutine of the search runs it: a panic in it is
// the search's fault, not the end of the process.
func (s *_FaultSlot) guard(task func()) func() {
	return func() {
		defer func() {
			if r := recover(); r != nil {
				s.record(utils.RecoveredFault(r))
			}
		}()
		task()
	}
}

// record keeps the first fault and stops the search. A fault recorded
// after the search has answered goes to the slot's late reader.
func (s *_FaultSlot) record(fault utils.Fault) {
	s.mu.Lock()
	if s.answered {
		late := s.late
		s.mu.Unlock()
		late(fault)
		return
	}
	if s.fault == nil {
		s.fault = &fault
	}
	stop := s.stop
	s.mu.Unlock()
	if stop != nil {
		stop()
	}
}

// recorded is the fault the search met, nil when none.
func (s *_FaultSlot) recorded() *utils.Fault {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.fault
}

// answer closes the slot for the search that armed it: the fault it
// met, nil when none, and every fault from then on is late.
func (s *_FaultSlot) answer() *utils.Fault {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.answered = true
	return s.fault
}

// _LateFaultReportKey is the context key of WithLateFaultReport.
type _LateFaultReportKey struct{}

// WithLateFaultReport gives the searches run under ctx a reader for a
// fault met after its search has answered: a contradiction check runs
// on a pool its search does not wait for, so its panic can come when no
// caller is left to raise it on. A session's engine records such a
// fault against the request that started the search.
func WithLateFaultReport(ctx context.Context, report func(SearchFault)) context.Context {
	return context.WithValue(ctx, _LateFaultReportKey{}, report)
}

// reportLateFault hands a late fault to the reader ctx carries. Under a
// context with none (a chapter's replay, a recorder) the fault is raised
// where it stands, on a goroutine nothing recovers: a broken invariant
// is never dropped.
func reportLateFault(ctx context.Context, fault SearchFault) {
	report, ok := ctx.Value(_LateFaultReportKey{}).(func(SearchFault))
	if !ok {
		panic(fault)
	}
	report(fault)
}
