package utils

import (
	"context"
	"fmt"
	"sync"
	"time"
)

func TrySend[T any](c chan<- T, v T) {
	select {
	case c <- v:
	default:
	}
}

// QuitSentinel is the panic value used to unwind callers when ctx fires
// mid-computation. The unify / beta-eta hot paths panic with this sentinel
// instead of threading cancellation as return values through every recursive
// frame; the top-level entry point recovers it and returns nil. Zero-cost
// when ctx is never cancelled.
type QuitSentinel struct{}

// RecoverQuit is the canonical recover for the quit sentinel. Use as:
//
//	defer func() { result = nil; _ = RecoverQuit(recover()) }()
//
// It returns true if a QuitSentinel was caught (swallowed), false if recover
// returned nil, and re-panics on any other value.
func RecoverQuit(r any) bool {
	if r == nil {
		return false
	}
	if _, ok := r.(QuitSentinel); ok {
		return true
	}
	panic(r)
}

// CheckCtx panics with QuitSentinel if ctx has been cancelled. Used by the
// unify / beta-eta hot loops to abandon computation when a deadline fires or
// the caller cancels. Pairs with RecoverQuit at the top-level entry point.
func CheckCtx(ctx context.Context) {
	if ctx.Err() != nil {
		panic(QuitSentinel{})
	}
}

// nonblocking clear timer.
func clearTimer(timer *time.Timer) {
	if !timer.Stop() {
		select {
		case <-timer.C:
		default:
		}
	}
}

// TimeOutWrapper returns a function that runs f and returns an error
// if f does not return within duration d.
// Note: If f blocks forever, this wrapper will return an error after timeout,
// but f will continue running in the background.
// This may cause resource leaks if f does not return on its own.
func TimeOutWrapper(d time.Duration, f func()) func() error {
	return func() error {
		result := make(chan error, 1)
		go func() {
			defer func() {
				if r := recover(); r != nil {
					TrySend(result, fmt.Errorf("panic: %v", r))
					return
				}
				TrySend(result, nil)
			}()
			f()
		}()

		timer := time.NewTimer(d)
		defer clearTimer(timer)

		select {
		case err := <-result:
			return err
		case <-timer.C:
			return fmt.Errorf("callback did not return within %v", d)
		}
	}
}

type GlobalCounter struct {
	printPeriod int32
	i           int32
	name        string
	t           time.Time
	sync.Mutex
}

func NewCounter(name string, printPeriod int32) *GlobalCounter {
	return &GlobalCounter{
		printPeriod: printPeriod,
		i:           0,
		name:        name,
		t:           time.Now()}
}

func (c *GlobalCounter) TakeOne() int32 {
	c.Lock()
	defer c.Unlock()
	i := c.i
	c.i++
	if c.i%c.printPeriod == 0 {
		fmt.Print(c.name, " ", c.i, " ", time.Since(c.t), "\n")
	}
	return i
}
