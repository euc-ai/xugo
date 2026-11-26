package core

import (
	"context"
	"fmt"
	"runtime"
	"sync"
	"sync/atomic"
	"testing"
	"testing/synctest"

	"github.com/stretchr/testify/assert"
)

// The tests of a force that waits for another goroutine's build run in a
// synctest bubble. synctest.Wait returns once every other goroutine of the
// bubble has exited or is parked on a channel of the bubble, so "this force
// is parked for good" is read from the scheduler and from no clock.

// _ForceEnd is how one Force call ended: ended is set once it has returned
// or panicked, and panicked holds the panic.
type _ForceEnd struct {
	ended    atomic.Bool
	panicked any
}

// goForce forces p on a goroutine of its own.
func goForce(p ThmPromise) *_ForceEnd {
	end := &_ForceEnd{}
	go func() {
		defer func() {
			end.panicked = recover()
			end.ended.Store(true)
		}()
		Force(context.Background(), p)
	}()
	return end
}

// allEnded reports whether every force has ended, and fails the test for
// each that is parked. Having found one parked it settles cells from trust,
// which wakes the goroutines parked on them and lets the bubble end.
func allEnded(t *testing.T, cells []ThmPromise, ends ...*_ForceEnd) bool {
	synctest.Wait()
	parked := false
	for i, end := range ends {
		if !end.ended.Load() {
			t.Errorf("force %d is parked for good", i)
			parked = true
		}
	}
	if parked {
		for _, c := range cells {
			ForceWithBoundary(context.Background(), c, func(Prop) bool { return true })
		}
		synctest.Wait()
	}
	return !parked
}

// numberedProp is the i-th of a family of distinct statements, with a
// certificate for it.
func numberedProp(i int) (Prop, ThmCert) {
	return eqProp(fmt.Sprint("l", i), fmt.Sprint("r", i))
}

// assertForceCycle checks the failure names every promise on the cycle.
func assertForceCycle(t *testing.T, message string, cells ...Prop) {
	t.Helper()
	assert.Contains(t, message, "theorem promise dependency cycle:")
	assert.Contains(t, message, " → ")
	for _, cell := range cells {
		assert.Contains(t, message, string(cell.AlphaKey()))
	}
}

// Two builders on separate goroutines have no shared call stack. Their
// explicit dependencies nevertheless form a cycle; the last edge panics,
// poisons its cell, and wakes the other builder with the same failure.
func TestForceWait_MutualCycleAcrossGoroutinesPanics(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmtA, _ := numberedProp(0)
		stmtB, _ := numberedProp(1)
		enteredA, enteredB := make(chan struct{}), make(chan struct{})
		var a, b ThmPromise
		a = Promise(stmtA, func(f Forcer) ThmCert { close(enteredA); <-enteredB; return f.Force(b) })
		b = Promise(stmtB, func(f Forcer) ThmCert { close(enteredB); <-enteredA; return f.Force(a) })
		endA, endB := goForce(a), goForce(b)
		if !allEnded(t, []ThmPromise{a, b}, endA, endB) {
			return
		}
		for _, end := range []*_ForceEnd{endA, endB} {
			msg := fmt.Sprint(end.panicked)
			assert.Contains(t, msg, "theorem promise dependency cycle:")
			assertForceCycle(t, msg, a, b)
		}
		assert.False(t, a.Proved())
		assert.False(t, b.Proved())
	})
}

// A cycle of three builders on three goroutines: no two of them wait for each
// other, and the third wait to enter closes the cycle.
func TestForceWait_ThreeGoroutineCyclePanics(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		const n = 3
		cells := make([]ThmPromise, n)
		var entered sync.WaitGroup
		entered.Add(n)
		for i := range n {
			stmt, _ := numberedProp(i)
			cells[i] = Promise(stmt, func(f Forcer) ThmCert {
				entered.Done()
				entered.Wait()
				return f.Force(cells[(i+1)%n])
			})
		}
		ends := make([]*_ForceEnd, n)
		for i, c := range cells {
			ends[i] = goForce(c)
		}
		if !allEnded(t, cells, ends...) {
			return
		}
		for _, end := range ends {
			msg := fmt.Sprint(end.panicked)
			assert.Contains(t, msg, "theorem promise dependency cycle:")
			for _, c := range cells {
				assertForceCycle(t, msg, c)
			}
		}
	})
}

// The cycle a → x → b → y → a includes synchronous builds between the
// channel waits. All four promises belong to the dependency path.
func TestForceWait_CycleNamesTheBuildsBetween(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmt := func(i int) Prop { p, _ := numberedProp(i); return p }
		enteredX, enteredY := make(chan struct{}), make(chan struct{})
		var a, x, b, y ThmPromise
		a = Promise(stmt(0), func(f Forcer) ThmCert { return f.Force(x) })
		x = Promise(stmt(1), func(f Forcer) ThmCert { close(enteredX); <-enteredY; return f.Force(b) })
		b = Promise(stmt(2), func(f Forcer) ThmCert { return f.Force(y) })
		y = Promise(stmt(3), func(f Forcer) ThmCert { close(enteredY); <-enteredX; return f.Force(a) })
		endA, endB := goForce(a), goForce(b)
		if !allEnded(t, []ThmPromise{a, x, b, y}, endA, endB) {
			return
		}
		for _, end := range []*_ForceEnd{endA, endB} {
			msg := fmt.Sprint(end.panicked)
			assertForceCycle(t, msg, a, x, b, y)
		}
	})
}

// Changing the computation context retains the builder identity, so it
// cannot erase a dependency on the way round a cycle.
func TestForceWait_CycleThroughChangedContextPanics(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmtA, _ := numberedProp(0)
		stmtB, _ := numberedProp(1)
		var a, b ThmPromise
		a = Promise(stmtA, func(f Forcer) ThmCert { return f.WithContext(context.Background()).Force(b) })
		b = Promise(stmtB, func(f Forcer) ThmCert { return f.Force(a) })
		end := goForce(a)
		if !allEnded(t, []ThmPromise{a, b}, end) {
			return
		}
		msg := fmt.Sprint(end.panicked)
		assert.Contains(t, msg, "theorem promise dependency cycle:")
		assertForceCycle(t, msg, a, b)
	})
}

// A context change also retains dependencies across goroutines and through
// a synchronous intermediate build.
func TestForceWait_CycleAcrossGoroutinesThroughChangedContextPanics(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmt := func(i int) Prop { p, _ := numberedProp(i); return p }
		enteredX, enteredB := make(chan struct{}), make(chan struct{})
		var a, x, b ThmPromise
		a = Promise(stmt(0), func(f Forcer) ThmCert { return f.WithContext(context.Background()).Force(x) })
		x = Promise(stmt(1), func(f Forcer) ThmCert { close(enteredX); <-enteredB; return f.Force(b) })
		b = Promise(stmt(2), func(f Forcer) ThmCert { close(enteredB); <-enteredX; return f.Force(a) })
		endA, endB := goForce(a), goForce(b)
		if !allEnded(t, []ThmPromise{a, x, b}, endA, endB) {
			return
		}
		for _, end := range []*_ForceEnd{endA, endB} {
			msg := fmt.Sprint(end.panicked)
			assert.Contains(t, msg, "theorem promise dependency cycle:")
			assertForceCycle(t, msg, a, x, b)
		}
	})
}

// Waits that close no cycle park and are woken: a diamond whose two sides
// both wait for the base while a third goroutine builds it.
func TestForceWait_WaitsWithoutACycleComplete(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmt := func(i int) Prop { p, _ := numberedProp(i); return p }
		cert := func(i int) ThmCert { _, c := numberedProp(i); return c }
		release := make(chan struct{})
		base := Promise(stmt(0), func(Forcer) ThmCert { <-release; return cert(0) })
		left := Promise(stmt(1), func(f Forcer) ThmCert { f.Force(base); return cert(1) })
		right := Promise(stmt(2), func(f Forcer) ThmCert { f.Force(base); return cert(2) })
		ends := []*_ForceEnd{goForce(base), goForce(left), goForce(right)}
		synctest.Wait()
		for i, end := range ends {
			assert.False(t, end.ended.Load(), "force %d ended before the base was released", i)
		}
		close(release)
		synctest.Wait()
		for i, end := range ends {
			assert.True(t, end.ended.Load(), "force %d is parked", i)
			assert.Nil(t, end.panicked, "force %d", i)
		}
	})
}

// A dependency edge may outlive its target's settlement until the waiter
// runs again. Trust settles inner while outer waits on it; inner's builder
// then requests outer. The completed inner cell must break the apparent
// cycle even if outer has not yet removed its edge to inner.
func TestForceWait_EndedWaitClosesNoCycle(t *testing.T) {
	for range 2000 {
		synctest.Test(t, func(t *testing.T) {
			stmtInner, certInner := numberedProp(0)
			stmtOuter, certOuter := numberedProp(1)
			enteredInner, enteredOuter := make(chan struct{}), make(chan struct{})
			release := make(chan struct{})
			var inner, outer ThmPromise
			inner = Promise(stmtInner, func(f Forcer) ThmCert {
				close(enteredInner)
				<-release
				f.Force(outer)
				return certInner
			})
			outer = Promise(stmtOuter, func(f Forcer) ThmCert {
				close(enteredOuter)
				f.Force(inner)
				return certOuter
			})
			endInner := goForce(inner)
			<-enteredInner
			endOuter := goForce(outer)
			<-enteredOuter
			synctest.Wait()
			assert.False(t, endInner.ended.Load())
			assert.False(t, endOuter.ended.Load())
			ForceWithBoundary(context.Background(), inner, func(Prop) bool { return true })
			close(release)
			if !allEnded(t, []ThmPromise{inner, outer}, endInner, endOuter) {
				return
			}
			assert.Nil(t, endInner.panicked)
			assert.Nil(t, endOuter.panicked)
		})
		if t.Failed() {
			return
		}
	}
}

// Settling a promise wakes callers waiting for its certificate, but the
// caller executing its builder synchronously still waits for that builder
// to return. Its dependency survives a concurrent trust settlement.
func TestForceWait_TrustSettleKeepsSynchronousBuildDependency(t *testing.T) {
	for _, derived := range []bool{false, true} {
		name := "direct"
		if derived {
			name = "through_derived"
		}
		t.Run(name, func(t *testing.T) {
			synctest.Test(t, func(t *testing.T) {
				stmtA, certA := numberedProp(0)
				stmtB, certB := numberedProp(1)
				stmtC, certC := numberedProp(2)
				enteredA, releaseA := make(chan struct{}), make(chan struct{})
				var b, c ThmPromise
				a := Promise(stmtA, func(f Forcer) ThmCert {
					close(enteredA)
					<-releaseA
					f.Force(b)
					return certA
				})
				var dependency Thm = a
				if derived {
					dependency = AsThm(EqSym(a))
				}
				b = Promise(stmtB, func(f Forcer) ThmCert { f.Force(c); return certB })
				c = Promise(stmtC, func(f Forcer) ThmCert { f.Force(dependency); return certC })

				end := goForce(c)
				<-enteredA
				ForceWithBoundary(context.Background(), a, func(Prop) bool { return true })
				close(releaseA)
				if !allEnded(t, []ThmPromise{c, a, b}, end) {
					return
				}
				assertForceCycle(t, fmt.Sprint(end.panicked), c, a, b)
			})
		})
	}
}

// A derived theorem can realize again while its first realization runs a
// builder. Once trust settles that builder's promise, the second realization
// reads its certificate without waiting for the first realization to return.
func TestForceWait_TrustSettleLetsDerivedRealizeAgain(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmtA, certA := numberedProp(0)
		stmtB, certB := numberedProp(1)
		enteredA, releaseA := make(chan struct{}), make(chan struct{})
		var b ThmPromise
		a := Promise(stmtA, func(f Forcer) ThmCert {
			close(enteredA)
			<-releaseA
			f.Force(b)
			return certA
		})
		d := AsThm(EqSym(a))
		b = Promise(stmtB, func(f Forcer) ThmCert { f.Force(d); return certB })

		end := &_ForceEnd{}
		var result ThmCert
		go func() {
			defer func() {
				end.panicked = recover()
				end.ended.Store(true)
			}()
			result = Force(context.Background(), d)
		}()
		<-enteredA
		ForceWithBoundary(context.Background(), a, func(Prop) bool { return true })
		close(releaseA)
		if !allEnded(t, []ThmPromise{a, b}, end) {
			return
		}
		if !assert.Nil(t, end.panicked) {
			return
		}
		assert.True(t, result.AlphaEquals(d))
		assert.True(t, a.Proved())
		assert.True(t, b.Proved())
	})
}

// A runner whose goroutine exits inside the builder (runtime.Goexit, which
// is how t.FailNow leaves a test) poisons the cell: a later force panics
// where it would have parked on a build nobody is running.
func TestBuilderRoot_GoexitInBuilderPoisonsCell(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmt, _ := numberedProp(0)
		p := Promise(stmt, func(Forcer) ThmCert { runtime.Goexit(); panic("unreachable") })
		runner := goForce(p)
		synctest.Wait()
		assert.True(t, runner.ended.Load())
		later := goForce(p)
		if !allEnded(t, []ThmPromise{p}, later) {
			return
		}
		assert.Contains(t, fmt.Sprint(later.panicked), "is poisoned")
		assert.Contains(t, fmt.Sprint(later.panicked), "runtime.Goexit")
		assert.False(t, p.Proved())
	})
}

// A cell settled from trust while its builder runs keeps its certificate when
// the builder then panics: the waiter was woken with the certificate, the
// runner gets its builder's own panic, and the cell is not poisoned.
func TestBuilderRoot_PanicAfterTrustSettleReachesTheRunner(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmt, _ := numberedProp(0)
		entered, release := make(chan struct{}), make(chan struct{})
		p := Promise(stmt, func(Forcer) ThmCert { close(entered); <-release; panic("boom") })
		runner := goForce(p)
		<-entered
		waiter := goForce(p)
		synctest.Wait()
		assert.False(t, waiter.ended.Load(), "the waiter ended while the build was in flight")

		ForceWithBoundary(context.Background(), p, func(Prop) bool { return true })
		synctest.Wait()
		assert.True(t, waiter.ended.Load(), "the trust settle did not wake the waiter")
		assert.Nil(t, waiter.panicked)

		close(release)
		synctest.Wait()
		assert.True(t, runner.ended.Load())
		assert.Equal(t, "boom", runner.panicked)
		assert.True(t, p.Proved(), "the cell lost the certificate trust settled it with")
		assert.NotPanics(t, func() { Force(context.Background(), p) })
	})
}

// A Forcer is a capability of a live build. Its zero value and a value
// retained beyond the build cannot start a new force, even of a certificate.
func TestForcer_ZeroAndEscapedValuesPanic(t *testing.T) {
	stmt, cert := numberedProp(0)
	var zero Forcer
	assert.True(t, zero.IsZero())
	assert.PanicsWithValue(t, "core: the zero Forcer", func() { zero.Force(cert) })
	assert.PanicsWithValue(t, "core: the zero Forcer", func() { zero.Context() })
	assert.PanicsWithValue(t, "core: the zero Forcer", func() { zero.WithContext(context.Background()) })

	for _, fail := range []bool{false, true} {
		name := "return"
		if fail {
			name = "panic"
		}
		t.Run(name, func(t *testing.T) {
			var escaped Forcer
			p := Promise(stmt, func(f Forcer) ThmCert {
				escaped = f
				assert.False(t, f.IsZero())
				if fail {
					panic("builder failure")
				}
				return cert
			})
			if fail {
				assert.PanicsWithValue(t, "builder failure", func() { Force(context.Background(), p) })
			} else {
				assert.True(t, Force(context.Background(), p).AlphaEquals(cert))
			}
			assert.PanicsWithValue(t, "core: Forcer used after its builder returned", func() { escaped.Force(cert) })
			assert.PanicsWithValue(t, "core: Forcer used after its builder returned", func() { escaped.Context() })
			assert.PanicsWithValue(t, "core: Forcer used after its builder returned", func() { escaped.WithContext(context.Background()) })
		})
	}
}

// A context change carries computation values without changing either the
// builder's identity or the trust boundary inherited by its nested forces.
func TestForcer_ContextPreservesValuesAndTrustBoundary(t *testing.T) {
	type _ValueKey struct{}
	stmt, _ := numberedProp(0)
	dep := Promise(stmt, func(Forcer) ThmCert { panic("the boundary must settle this dependency") })
	root := Promise(MakeProp(Eq(stmt.Conclusion(), stmt.Conclusion())), func(f Forcer) ThmCert {
		assert.Equal(t, "outer", f.Context().Value(_ValueKey{}))
		assert.NoError(t, f.Context().Err())
		changed := f.WithContext(context.WithValue(context.Background(), _ValueKey{}, "inner"))
		assert.Equal(t, "inner", changed.Context().Value(_ValueKey{}))
		assert.Equal(t, "outer", f.Context().Value(_ValueKey{}))
		cert := changed.Force(dep)
		return Deduct(cert, cert).AsThmCert()
	})
	ctx, cancel := context.WithCancel(context.WithValue(context.Background(), _ValueKey{}, "outer"))
	cancel()
	cert, trusted := ForceWithBoundary(ctx, root, func(p Prop) bool { return p.AlphaEquals(stmt) })
	assert.Len(t, trusted, 1)
	assert.Len(t, cert.Assumes(), 1)
	assert.Equal(t, BoundaryDoor, cert.Assumes()[0].Door)
	assert.True(t, cert.Assumes()[0].Statement.AlphaEquals(stmt))
}

// Joined parallel children can share their builder's Forcer. Repeated
// requests for the same pending promise remain one dependency until the
// last request returns, and the dependency itself is built only once.
func TestForcer_JoinedChildrenSharePendingDependency(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmt, cert := numberedProp(0)
		release := make(chan struct{})
		var calls atomic.Int32
		dep := Promise(stmt, func(Forcer) ThmCert {
			calls.Add(1)
			<-release
			return cert
		})
		root := Promise(stmt, func(f Forcer) ThmCert {
			const n = 8
			var children sync.WaitGroup
			panics := make([]any, n)
			for i := range n {
				children.Go(func() {
					defer func() { panics[i] = recover() }()
					assert.True(t, f.Force(dep).AlphaEquals(cert))
				})
			}
			children.Wait()
			for _, p := range panics {
				assert.Nil(t, p)
			}
			return cert
		})
		end := goForce(root)
		synctest.Wait()
		assert.False(t, end.ended.Load())
		assert.Equal(t, int32(1), calls.Load())
		close(release)
		if !allEnded(t, []ThmPromise{root, dep}, end) {
			return
		}
		assert.Nil(t, end.panicked)
		assert.True(t, root.Proved())
	})
}

// A builder cannot return a certificate while children still use its
// Forcer. The violation poisons the builder and closes the Forcer's scope.
func TestForcer_UnjoinedChildPoisonsBuilder(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmt, cert := numberedProp(0)
		entered, release := make(chan struct{}), make(chan struct{})
		dep := Promise(stmt, func(Forcer) ThmCert { close(entered); <-release; return cert })
		child := &_ForceEnd{}
		var escaped Forcer
		root := Promise(stmt, func(f Forcer) ThmCert {
			escaped = f
			go func() {
				defer func() { child.panicked = recover(); child.ended.Store(true) }()
				f.Force(dep)
			}()
			<-entered
			return cert
		})
		end := goForce(root)
		synctest.Wait()
		assert.True(t, end.ended.Load())
		assert.Equal(t, "core: builder returned with unfinished forces", end.panicked)
		assert.False(t, root.Proved())
		assert.PanicsWithValue(t, "core: Forcer used after its builder returned", func() { escaped.Force(cert) })
		close(release)
		synctest.Wait()
		assert.True(t, child.ended.Load())
	})
}

// Trust may settle a cell before its builder has finished. That builder's
// Forcer remains live and may force a dependency before returning normally.
func TestForcer_TrustSettleDoesNotEndBuilderScope(t *testing.T) {
	synctest.Test(t, func(t *testing.T) {
		stmt, cert := numberedProp(0)
		depStmt, depCert := numberedProp(1)
		dep := Promise(depStmt, func(Forcer) ThmCert { return depCert })
		entered, release := make(chan struct{}), make(chan struct{})
		root := Promise(stmt, func(f Forcer) ThmCert {
			close(entered)
			<-release
			assert.True(t, f.Force(dep).AlphaEquals(depCert))
			return cert
		})
		end := goForce(root)
		<-entered
		trusted, _ := ForceWithBoundary(context.Background(), root, func(Prop) bool { return true })
		assert.Equal(t, BoundaryDoor, trusted.Assumes()[0].Door)
		close(release)
		synctest.Wait()
		assert.True(t, end.ended.Load())
		assert.Nil(t, end.panicked)
		assert.True(t, dep.Proved())
		assert.Equal(t, BoundaryDoor, Force(context.Background(), root).Assumes()[0].Door)
	})
}
