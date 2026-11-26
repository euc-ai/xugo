package core

import (
	"context"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/utils"
)

// Forcer carries a builder's identity and trust boundary through nested
// forces. A builder must use the Forcer it receives, including through any
// helpers it calls. It may share that value with concurrent child calls,
// provided all of them finish before it returns. The value expires when the
// builder ends; the zero value is invalid.
//
// NewForcer, Force and ForceWithBoundary start independent top-level calls.
// Starting one inside a builder omits that dependency from the graph and is
// forbidden by the builder contract. Locks and waits outside Forcer are not
// tracked.
type Forcer struct{ *_ForcerState }

type _ForcerState struct {
	ctx      context.Context
	boundary *_ForceBoundary
	scope    *_ForceScope
}

// NewForcer starts a top-level force context. Context values are retained;
// cancellation is not consulted, since realization must finish or panic.
// Nested forces use the builder's Forcer instead of constructing a new one.
func NewForcer(ctx context.Context) Forcer {
	return Forcer{&_ForcerState{ctx: context.WithoutCancel(ctx)}}
}

// IsZero reports whether f is the zero handle.
func (f Forcer) IsZero() bool { return f._ForcerState == nil }

// Context returns the context for non-force work performed by the builder.
// Force ownership and trust are carried separately, on the Forcer itself.
func (f Forcer) Context() context.Context {
	f.check()
	return f.ctx
}

// WithContext changes the context values without changing force ownership,
// the trust boundary, or the builder lifetime. Cancellation is not consulted.
func (f Forcer) WithContext(ctx context.Context) Forcer {
	f.check()
	state := *f._ForcerState
	state.ctx = context.WithoutCancel(ctx)
	return Forcer{&state}
}

func (f Forcer) check() {
	if f.IsZero() {
		panic("core: the zero Forcer")
	}
	if f.scope != nil {
		f.scope.mu.Lock()
		closed := f.scope.closed
		f.scope.mu.Unlock()
		if closed {
			panic("core: Forcer used after its builder returned")
		}
	}
}

// Force realizes t to the kernel certificate of its statement: t's kernel
// value itself when that is a ThmCert, and for a ThmPromise the certificate
// its cell settles with, after running the builder (builder-root) or forcing
// every dependency (derived). It returns the ThmCert or panics — there is no
// error path. Realization is synchronous on the caller's goroutine; core
// spawns no goroutine.
//
// This is a top-level entry: ctx supplies values for the builder's work,
// with cancellation removed. Inside a builder, use the supplied Forcer so
// that the active promise graph sees every nested dependency and rejects
// cycles, including those spanning concurrent builds.
func Force(ctx context.Context, t Thm) ThmCert {
	return NewForcer(ctx).Force(t)
}

// ForceWithBoundary forces t under a trust frontier: any root promise on the
// way down — a cell with a builder — whose statement satisfies `trusted` is
// settled directly from its statement instead of being built, so the cert holds
// GIVEN the trusted statements as axioms. A t whose kernel value is a ThmCert
// is returned as it is, with nothing assumed by this call.
//
// Only a root is settled that way. A derived cell is the kernel's own
// derivation over its dependencies and is always derived from them, whatever
// its statement: one whose statement happens to be a trusted one would
// otherwise stand on that statement and not on the dependencies it was
// derived over, an edge no one declared.
//
// What it leaves behind. A cell settled this way stays settled: every later
// force of it, bounded or not, in this call or another, returns the minted
// certificate without running its builder. That certificate assumes its own
// statement, and so does every certificate a rule derives from it
// (ThmCert.Assumes). A build of the cell that was in flight when trust
// settled it changes nothing by failing: the failure reaches the caller that
// ran the build and no other. `assumed` lists the statements THIS call
// settled from trust; a cell an earlier call settled is not in it, so what a
// certificate stands on is read from the certificate.
//
// Soundness: the boundary mint is a TestThm-class trust escape (it stamps a
// certificate over the statement without the builder/α-gate). It is on the
// deferred-cert audit surface alongside `TestThm` / `Promise`:
//
//	grep ForceWithBoundary   # bounded forces — inspect each predicate's frontier
//
// A predicate that trusts given statements compares them with the
// statement it is asked about (Prop.AlphaEquals). A key picks the ones
// to compare and is not the comparison: one key for two statements that
// are not α-equal can be made on purpose (PropKey).
func ForceWithBoundary(ctx context.Context, t Thm, trusted PropPredicate) (cert ThmCert, assumed []Prop) {
	b := &_ForceBoundary{trusts: trusted}
	f := NewForcer(ctx)
	f.boundary = b
	cert = f.Force(t)
	return cert, b.assumed()
}

// Force realizes t as a dependency of this builder, or as an independent
// root for a Forcer made by NewForcer. The kernel reads t's kernel value: a
// type that embeds a Thm has no say in what comes back.
func (f Forcer) Force(t Thm) ThmCert {
	if f.IsZero() {
		panic("core: the zero Forcer")
	}
	var parent *_PromiseCell
	if f.scope != nil {
		f.scope.begin()
		defer f.scope.end()
		parent = f.scope.cell
	}
	return forceThm(t, parent, f.ctx, f.boundary)
}

// _ForceScope is the lifetime of one builder, independent of whether a
// concurrent trust boundary has already settled its promise.
type _ForceScope struct {
	cell   *_PromiseCell
	mu     sync.Mutex
	closed bool
	calls  int
}

func (s *_ForceScope) begin() {
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.closed {
		panic("core: Forcer used after its builder returned")
	}
	s.calls++
}

func (s *_ForceScope) end() {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.calls--
}

func (s *_ForceScope) close() int {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.closed = true
	return s.calls
}

func forceThm(t Thm, parent *_PromiseCell, ctx context.Context, boundary *_ForceBoundary) ThmCert {
	switch k := t.kernel().(type) {
	case ThmCert:
		return k
	case ThmPromise:
		return k.force(parent, ctx, boundary)
	default:
		panic("core: force of a non-theorem")
	}
}

func (c *_PromiseCell) force(parent *_PromiseCell, ctx context.Context, boundary *_ForceBoundary) ThmCert {
	if t := c.result(); !t.IsZero() {
		return t
	}
	// Only root promises may be settled from trust. A derived promise must
	// retain the assumptions of its actual dependencies.
	if boundary != nil && c.builder != nil && boundary.trusts(_Proposition{c._Statement}) {
		boundary.record(c._Statement)
		c.settle(certify(*c._Statement, assumed(*c._Statement, BoundaryDoor)))
		return c.result()
	}
	switch {
	case c.builder != nil:
		return c.forceBuilder(parent, ctx, boundary)
	case len(c.deps) > 0:
		return c.forceDerived(parent, ctx, boundary)
	default:
		panic("theorem promise has neither builder nor dependencies")
	}
}

// forceBuilder claims a single synchronous build or waits for its result.
// A synchronous build keeps its edge until the builder returns; a waiter
// needs only the certificate, so settlement makes its edge inactive.
func (c *_PromiseCell) forceBuilder(parent *_PromiseCell, ctx context.Context, boundary *_ForceBoundary) ThmCert {
	c.mu.Lock()
	switch {
	case !c.thm.IsZero():
		t := c.thm
		c.mu.Unlock()
		return t
	case c.poisoned != nil:
		c.mu.Unlock()
		c.repanicPoisoned()
	case !c.building:
		c.building = true
		c.mu.Unlock()
		return c.runBuilder(parent, ctx, boundary)
	default:
		c.mu.Unlock()
	}
	if parent != nil && forceDeps.enter(parent, c, _ForceWait) {
		defer forceDeps.leave(parent, c, _ForceWait)
	}
	<-c.done
	if t := c.result(); !t.IsZero() {
		return t
	}
	c.repanicPoisoned()
	panic("unreachable")
}

// runBuilder closes the Forcer's lifetime on every exit. A panic or Goexit
// poisons an unsettled cell and wakes its waiters. A concurrent trust settle
// keeps its certificate, while the builder's own caller receives its panic.
func (c *_PromiseCell) runBuilder(parent *_PromiseCell, ctx context.Context, boundary *_ForceBoundary) ThmCert {
	scope := &_ForceScope{cell: c}
	settled := false
	defer func() {
		scope.close()
		if settled {
			return
		}
		r := recover()
		if r == nil {
			c.poison("the runner's goroutine exited inside the builder (runtime.Goexit)")
			return
		}
		c.poison(r)
		panic(r)
	}()
	if parent != nil && forceDeps.enter(parent, c, _ForceCall) {
		defer forceDeps.leave(parent, c, _ForceCall)
	}
	thm := c.builder(Forcer{&_ForcerState{ctx: ctx, boundary: boundary, scope: scope}})
	if scope.close() != 0 {
		panic("core: builder returned with unfinished forces")
	}
	c.settle(thm)
	settled = true
	return thm
}

type _ForceEdgeKind uint8

const (
	_ForceCall _ForceEdgeKind = iota // waits for a synchronous builder to return
	_ForceWait                       // waits only for a certificate or poison
)

// _ForceDeps holds active dependencies between builder-root promise cells.
// Derived promises pass their caller's identity through to their deps: each
// force may realize a derived cell independently. Edges count synchronous
// calls separately from waits, since trust may settle a cell while its
// builder is still running. Entering an edge and checking for a cycle are
// atomic under mu. The lock order is graph then cell; no cell operation
// acquires the graph lock while holding its own.
type _ForceDeps struct {
	mu    sync.Mutex
	edges map[*_PromiseCell]map[*_PromiseCell][2]int
}

var forceDeps = _ForceDeps{edges: map[*_PromiseCell]map[*_PromiseCell][2]int{}}

func (g *_ForceDeps) enter(from, to *_PromiseCell, kind _ForceEdgeKind) bool {
	g.mu.Lock()
	defer g.mu.Unlock()
	if kind == _ForceWait && !to.pending() {
		return false
	}
	if path := g.path(to, from, map[*_PromiseCell]bool{}); path != nil {
		keys := make([]string, 1, len(path)+1)
		keys[0] = string(from.AlphaKey())
		for _, c := range path {
			keys = append(keys, string(c.AlphaKey()))
		}
		panic("theorem promise dependency cycle: " + strings.Join(keys, " → "))
	}
	if g.edges[from] == nil {
		g.edges[from] = map[*_PromiseCell][2]int{}
	}
	counts := g.edges[from][to]
	counts[kind]++
	g.edges[from][to] = counts
	return true
}

func (g *_ForceDeps) leave(from, to *_PromiseCell, kind _ForceEdgeKind) {
	g.mu.Lock()
	defer g.mu.Unlock()
	edges := g.edges[from]
	counts := edges[to]
	utils.Assert(counts[kind] > 0)
	counts[kind]--
	if counts == [2]int{} {
		delete(edges, to)
	} else {
		edges[to] = counts
	}
	if len(edges) == 0 {
		delete(g.edges, from)
	}
}

// path finds a live path from c to target while the graph lock is held.
// Settlement breaks waits even before their callers wake and remove the
// edges. A synchronous call remains active until its builder returns.
func (g *_ForceDeps) path(c, target *_PromiseCell, seen map[*_PromiseCell]bool) []*_PromiseCell {
	if seen[c] {
		return nil
	}
	if c == target {
		return []*_PromiseCell{c}
	}
	seen[c] = true
	for next, counts := range g.edges[c] {
		if counts[_ForceCall] == 0 && !next.pending() {
			continue
		}
		if tail := g.path(next, target, seen); tail != nil {
			return append([]*_PromiseCell{c}, tail...)
		}
	}
	return nil
}

func (c *_PromiseCell) pending() bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.thm.IsZero() && c.poisoned == nil
}
