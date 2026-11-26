package core

import (
	"context"
	"fmt"
	"iter"
	"slices"
	"sync"

	"github.com/euc-ai/xugo/utils"
)

// A PropKey is a digest of a statement, cut from the keys of its
// conclusion and its hypotheses and read as a TermKey is: α-equal
// statements have one key, and a key equal for two statements that are
// not α-equal is the hash collision or the spelled name described
// there. Whoever admits a statement because it is a given one compares
// the statements (Prop.AlphaEquals).
type PropKey string

type Prop interface {
	Conclusion() Term

	// Clone of the hyp list.
	Hyps() []Term

	// Iter of the hyp list.
	HypIter() iter.Seq[Term]

	// Returns the i-th hyp.
	Hyp(int) Term

	NumHyps() int

	// Whether the given term is a hyp (modulo α-equal).
	HasHyp(Term) bool

	// Whether any hyp satisfies the given condition.
	AnyHyp(func(Term) bool) bool

	// Whether all hyps satisfy the given condition.
	AllHyp(func(Term) bool) bool

	Size() int

	HasFreeName(TermName) bool

	Proved() bool

	// If proved, returns the thm itself. Panic otherwise.
	// Can be used to assert being proved.
	AsThmCert() ThmCert

	// If proved, returns the unproved proposition, otherwise returns itself.
	AsProp() Prop

	// Returns the proposition itself.
	// This is to make sure wrappers of the proposition get unwrapped.
	// The kernel does not read it; see kernel().
	Core() Prop

	AlphaEquals(Prop) bool

	AlphaKey() PropKey

	// kernel returns the kernel value this Prop stands on: a bare
	// proposition, a ThmCert or a ThmPromise, the three kinds core defines.
	// Every door of the kernel reads a Prop's statement and its provedness
	// from this value and from nothing else. The method is unexported, so
	// a type outside core satisfies Prop only by embedding a core value,
	// and Go's promotion makes that value's kernel() the embedder's:
	// whatever the embedder's own Conclusion, Proved, Core or AlphaEquals
	// say, a door sees the embedded value. (Core is exported and
	// overridable; the kernel does not read it.)
	kernel() Prop
}

// _Statement is a sequent: a conclusion under hypotheses, the
// hypotheses in a canonical order. It is written once, where it is
// made, and no pointer to it leaves this package: a bare proposition, a
// certificate and a promise each hold one, and hand out its terms and
// copies of its hypothesis list, never the statement. It says nothing
// of a proof: a statement is proved where a certificate holds it.
type _Statement struct {
	conclusion Term
	hyps       []Term
}

// MakeProp states the sequent hyps ⊢ concl, unproved. The hypotheses
// are sorted and α-duplicates dropped in a list of the statement's own;
// the caller's slice is left as it was.
func MakeProp(concl Term, hyps ...Term) Prop {
	return propose(makeStatement(concl, hyps))
}

// propose is the bare proposition saying s.
func propose(s _Statement) _Proposition { return _Proposition{&s} }

// makeStatement is the statement hyps ⊢ concl, each term read through
// kernel() into a list of the statement's own.
func makeStatement(concl Term, hyps []Term) _Statement {
	own := make([]Term, len(hyps))
	for i, h := range hyps {
		own[i] = h.kernel()
	}
	slices.SortFunc(own, Term.Compare)
	return makeStatementFromOrderedHyps(concl.kernel(), slices.CompactFunc(own, Term.AlphaEquals))
}

// makeStatementFromOrderedHyps takes concl, a kernel value, and
// orderedHyps, a fresh ordered list of kernel values, as the
// statement's own.
func makeStatementFromOrderedHyps(concl Term, orderedHyps []Term) _Statement {
	utils.Assert(isBool(concl) && utils.All(orderedHyps, isBool))
	return _Statement{conclusion: concl, hyps: orderedHyps}
}

// isBool is IsBool over a kernel value.
func isBool(t Term) bool { return t.Type().Equals(typeBool) }

// statementOf is the statement a kernel value holds.
func statementOf(p Prop) *_Statement {
	switch p := p.(type) {
	case _Proposition:
		return p._Statement
	case ThmCert:
		return &p._Statement
	case ThmPromise:
		return p._Statement
	default:
		panic("statementOf: not a kernel value")
	}
}

func (p *_Statement) Conclusion() Term { return p.conclusion }

func (p *_Statement) Hyps() []Term { return utils.Clone(p.hyps) }

func (p *_Statement) HypIter() iter.Seq[Term] { return slices.Values(p.hyps) }

func (p *_Statement) Hyp(i int) Term { return p.hyps[i] }

func (p *_Statement) NumHyps() int { return len(p.hyps) }

func (p *_Statement) HasHyp(hyp Term) bool {
	_, found := slices.BinarySearchFunc(p.hyps, hyp.kernel(), Term.Compare)
	return found
}

func (p *_Statement) AnyHyp(f func(Term) bool) bool { return utils.Any(p.hyps, f) }

func (p *_Statement) AllHyp(f func(Term) bool) bool { return utils.All(p.hyps, f) }

func (p *_Statement) Size() int {
	s := p.conclusion.Size()
	for _, h := range p.hyps {
		s += h.Size()
	}
	return s
}

func (p *_Statement) HasFreeName(n TermName) bool {
	return p.conclusion.HasFreeName(n) ||
		utils.Any(p.hyps, utils.Curry(Term.HasFreeName, n))
}

func (p *_Statement) AlphaEquals(s Prop) bool {
	return p.alphaEquals(statementOf(s.kernel()))
}

func (p *_Statement) alphaEquals(q *_Statement) bool {
	return p.conclusion.AlphaEquals(q.conclusion) &&
		slices.EqualFunc(p.hyps, q.hyps, Term.AlphaEquals)
}

func (p *_Statement) AlphaKey() PropKey {
	seeds := make([]TermKey, len(p.hyps)+1)
	seeds[0] = p.conclusion.AlphaKey()
	for i, h := range p.hyps {
		seeds[i+1] = h.AlphaKey()
	}
	return PropKey(_PROP_KEY_PREFIX + utils.GenerateHash(seeds...))
}

// _Proposition is a statement with no proof: a goal, a hypothesis, the
// statement of a certificate read apart from it. Like every kernel
// object it is a handle, one word passed by value.
type _Proposition struct{ *_Statement }

func (_Proposition) Proved() bool { return false }

func (_Proposition) AsThmCert() ThmCert { panic("Not a proved thm.") }

func (p _Proposition) AsProp() Prop { return p }

func (p _Proposition) Core() Prop { return p }

func (p _Proposition) kernel() Prop {
	if p._Statement == nil {
		panic("core: a proposition with no statement")
	}
	return p
}

// Thm is a proven-or-provable proposition: the abstract notion of "a
// theorem", whose certificate is either already in hand or producible on
// demand. Its kernel value is exactly one of two:
//
//   - ThmCert    — a realized kernel certificate (Force is the identity).
//   - ThmPromise — an IOU forceable to a certificate (Force runs the
//     builder / forces the dependency graph).
//
// Unlike a bare Prop (which also admits a bare proposition — an unproved
// goal or hypothesis that may never become a theorem), a Thm always yields
// a kernel certificate: Force is total. Thm is the currency the
// define-then-run proof graph traffics in (Build_<X> returns, struct
// fields, factored citations); the realized-vs-deferred split is a runtime
// detail (IsPromised), not a static one. Use Prop for the engine internals
// that also handle bare goals.
//
// Forcing is a function of this package — Force, ForceWithBoundary,
// Forcer.Force — and not a method of the interface. A type outside the
// package satisfies Thm by embedding one and answers every exported method
// it declares itself, so a force asked of the value would be answered by
// whatever type carries it. The functions read the kernel value: the
// certificate they return is the kernel's own, of that value's statement.
type Thm interface {
	Prop
	// theorem is declared by ThmCert and ThmPromise alone, which is what
	// keeps a bare proposition from being a Thm.
	theorem()
}

// ThmCert is the realized flavor of Thm: a kernel-derived certificate,
// minted only by the kernel's rules (and TestThm), that a ThmPromise
// eventually settles into. It is a handle over a certificate node
// nothing outside this package can reach, so a certificate says what it
// was minted saying for as long as it exists. The zero ThmCert holds no
// statement: it is not proved, and reading it panics.
//
// No other type is a handle over that node. Go converts one struct type
// to another of the same underlying type, and reflect.Value.Convert
// makes the conversion for a type its caller cannot name, so a
// certificate that shared its underlying type with the bare proposition
// would be made from one.
type ThmCert struct{ *_Certificate }

// _Certificate is the node a certificate is a handle over: the statement
// it was minted saying, and what it stands on. certify makes every one.
type _Certificate struct {
	_Statement
	// assumes is the statements this certificate stands on that no rule
	// derived (ThmCert.Assumes).
	assumes *_Assumptions
}

// certify mints the certificate saying s and standing on a. Its callers
// are the rules, through makeThm and deriveProp, a derived promise cell
// that settles, and the three doors AssumptionDoor names.
func certify(s _Statement, a *_Assumptions) ThmCert {
	return ThmCert{&_Certificate{_Statement: s, assumes: a}}
}

// Internal method.
func makeThm(concl Term, hyps ...Term) ThmCert { return certify(makeStatement(concl, hyps), nil) }

// External method. Should only be used in tests. The certificate
// assumes its own statement, through TestDoor.
func TestThm(concl Term, hyps ...Term) ThmCert {
	s := makeStatement(concl, hyps)
	return certify(s, assumed(s, TestDoor))
}

// Assumes returns the statements this certificate stands on that no
// rule derived, each with the door it came in by: an axiom (NewAxiom),
// a statement a bounded force settled from trust (ForceWithBoundary), a
// test's fabrication (TestThm). A rule's certificate assumes what its
// premises assume, so the list is the whole of it, however and whenever
// the certificate was obtained. A certificate that assumes nothing was
// derived by the rules from the definitions alone.
func (t ThmCert) Assumes() []Assumption { return t.assumes.list() }

// IsZero reports whether t is the zero handle.
func (t ThmCert) IsZero() bool { return t._Certificate == nil }

func (t ThmCert) Proved() bool { return t._Certificate != nil }

func (t ThmCert) AsThmCert() ThmCert { return t }

// AsProp is the certificate's statement as a bare proposition, and for
// the zero ThmCert the proposition with no statement.
func (t ThmCert) AsProp() Prop {
	if t._Certificate == nil {
		return _Proposition{}
	}
	return _Proposition{&t._Statement}
}

func (t ThmCert) Core() Prop { return t }

func (t ThmCert) kernel() Prop {
	if t._Certificate == nil {
		panic("core: the zero ThmCert holds no statement")
	}
	return t
}

func (t ThmCert) theorem() {}

// ThmPromise is a stateful proof handle over a statement that never
// changes: only the certificate its cell holds can move, from unresolved
// to resolved. It is a handle over that cell, one word passed by value,
// so a holder can copy it and cannot point it at another cell's
// statement or proof.
//
// A promise yields a ThmCert only after its cell is resolved with a
// kernel-derived theorem whose statement alpha-equals the promised
// statement.
type ThmPromise struct{ *_PromiseCell }

// A _PromiseCell is in exactly one of two flavors, distinguished by which
// realization input it carries:
//
//   - builder-root: builder != nil. Force runs the builder on demand (the
//     generated-corpus case: the proof can build itself). This is the sole
//     root constructor (Promise) and the entire arbitrary-statement audit
//     surface — see Promise.
//   - derived: len(deps) > 0. Produced by deriveProp; realizes itself once
//     every dependency is proved.
//
// A cell moves unsettled → settled-with-a-real-certificate, or (builder-root
// only) unsettled → POISONED when its builder panics. There is no error state a
// caller can limp along with: realization either produces a kernel certificate
// whose statement α-equals this cell's statement, or it panics on the spot (a
// wrong-statement result, an unforceable dependency, a builder failure, or a
// cycle) — and a poisoned cell re-panics on every later Force rather than
// retrying the builder or parking waiters forever, so the fault gets debugged
// immediately.
type _PromiseCell struct {
	// The promised statement, never written after the cell is made.
	*_Statement
	// derived — each is a kernel value, proven-or-provable (deriveProp's
	// guard), held as the handle it was when the cell was made.
	deps    []Thm
	builder func(Forcer) ThmCert // builder-root

	// done is closed by settle; a builder-root's non-runner callers block on it.
	done chan struct{}

	mu sync.Mutex
	// building marks the single synchronous builder invocation. Concurrent
	// callers wait on done; the active promise graph detects dependency cycles.
	building bool
	// thm is the zero ThmCert until settled, then a real certificate
	// α-equal to the statement.
	thm ThmCert
	// poisoned records how a build ended without a certificate — the
	// recovered value of a builder panic, or a note that the runner's
	// goroutine exited inside the builder: non-nil marks the cell PERMANENTLY
	// POISONED. Every subsequent Force re-panics with it (fail-fast: a failed
	// build is a bug to debug immediately, not something to retry or to leave
	// waiters parked on forever). Set by poison, which also closes done to
	// wake concurrent waiters.
	poisoned any
}

// Promise declares a theorem statement whose certificate is produced on demand
// by builder. Force runs the builder (exactly once, shared across concurrent
// callers); the builder's output is gated by a statement-α-equality check, so a
// builder that returns the wrong theorem panics rather than yielding an unsound
// result. A builder that cannot produce its theorem must panic itself, not
// return the zero ThmCert.
//
// This is the ONLY way to mint a root promise from an arbitrary statement, and
// since a ThmPromise is a handle over a cell this package alone can make, the
// only way to fabricate any promise outside core. It is therefore the promise
// analogue of TestThm: the entire soundness audit surface is `grep Promise(`
// (plus the kernel-sound deriveProp path, which mints derived promises from
// statements the primitives compute, and the named axiom-class mint NewAxiom).
// Forcing a promise in CI is the mechanical audit that its builder really
// delivers a certificate matching the claimed statement.
//
// The promise is usable as a Prop immediately (statement only). Proved() never
// runs the builder — only Force does.
// The builder must use its Forcer for all nested forces and join its child
// calls before returning; see Forcer for the lifetime and dependency contract.
func Promise(p Prop, builder func(Forcer) ThmCert) ThmPromise {
	return ThmPromise{&_PromiseCell{
		_Statement: statementOf(p.kernel()),
		builder:    builder,
		done:       make(chan struct{}),
	}}
}

// newDerivedThmPromise takes deps as the cell's own.
func newDerivedThmPromise(statement _Statement, deps []Thm) ThmPromise {
	return ThmPromise{&_PromiseCell{
		_Statement: &statement,
		deps:       deps,
		done:       make(chan struct{}),
	}}
}

// IsZero reports whether p is the zero handle.
func (p ThmPromise) IsZero() bool { return p._PromiseCell == nil }

// Proved is a readiness check. For derived promises it also performs a
// non-blocking lazy realization attempt when every dependency is already
// proved. It never waits for root promises to be resolved.
func (p ThmPromise) Proved() bool {
	if p._PromiseCell == nil {
		return false
	}
	if !p.result().IsZero() {
		return true
	}
	p.tryRealizeReadyDeps()
	return !p.result().IsZero()
}

func (p ThmPromise) AsThmCert() ThmCert {
	utils.Assert(p.Proved())
	return p.result()
}

func (p ThmPromise) AsProp() Prop { return _Proposition{p._Statement} }

// Core preserves promise identity: the bare statement would silently drop
// the certificate cell when wrapper code calls p.Core().
func (p ThmPromise) Core() Prop { return p }

// kernel, like Core, is the promise itself.
func (p ThmPromise) kernel() Prop {
	if p._PromiseCell == nil {
		panic("core: the zero ThmPromise holds no statement")
	}
	return p
}

func (p ThmPromise) theorem() {}

// IsPromised reports whether p is a theorem promise (kernel value
// ThmPromise): an IOU whose certificate is produced on demand by its builder
// or deps. It is a TYPE test, independent of Proved() — a promise reads
// IsPromised==true whether or not it has been realized yet.
//
// Use it where code would otherwise call AsThmCert() eagerly. A promised Prop
// must be threaded onward AS A PROP (kept lazy), never collapsed to a
// ThmCert, because an unrealized promise has no certificate to give and
// AsThmCert() would panic.
//
//	IsPromised   Proved      p is …
//	false        true        a realized ThmCert — AsThmCert() is safe
//	true         false/true  a promise — keep lazy; AsThmCert() only once Proved()
//	false        false       a plain unproved Prop — no certificate path at all
func IsPromised(p Prop) bool {
	_, ok := p.kernel().(ThmPromise)
	return ok
}

// _ForceBoundary is a trust frontier carried through a force run by its Forcer: any
// root promise whose statement `trusts` returns true for is settled directly
// from its statement instead of being built. `hit` accumulates the
// statements this run settled that way.
type _ForceBoundary struct {
	trusts PropPredicate
	mu     sync.Mutex
	hit    []*_Statement
}

func (b *_ForceBoundary) record(s *_Statement) {
	b.mu.Lock()
	b.hit = append(b.hit, s)
	b.mu.Unlock()
}

// assumed returns the statements this run settled from trust.
func (b *_ForceBoundary) assumed() []Prop {
	b.mu.Lock()
	defer b.mu.Unlock()
	out := make([]Prop, len(b.hit))
	for i, s := range b.hit {
		out[i] = _Proposition{s}
	}
	return out
}

// AsThm narrows a Prop that is known to be proven-or-provable to the Thm
// interface WITHOUT forcing it. The kernel value must already be a ThmCert or
// a ThmPromise (the only Thm implementers) — a bare proposition is an
// assertion failure, not a recoverable condition. What comes back is that
// kernel value: of a type that embeds one, the embedded ThmCert or
// ThmPromise, whose every method is this package's.
//
// It is the EXPLICIT Prop→Thm narrowing at the genuine boundary where an
// engine-internal Prop (e.g. the result of a primitive rule like PropTypeInst,
// statically Prop but dynamically a Thm here) re-enters the define-then-run
// graph: narrow once with AsThm, then force (Force(ctx, AsThm(p))).
// Forcing is a Thm operation — there is no "force a Prop" — so this is where the
// "is it actually forceable" check lives, made deliberate rather than hidden.
//
// (Not to be confused with the AsThmCert method on Prop, which collapses to the
// concrete ThmCert and panics on an unforced promise.)
func AsThm(p Prop) Thm {
	if t, ok := p.kernel().(Thm); ok {
		return t
	}
	panic(fmt.Sprintf("AsThm: not a theorem (proven-or-provable): %s", p.AlphaKey()))
}

// poison records how a build ended without a certificate — the builder's
// panic, or its goroutine's exit — and wakes all waiters. The cell is
// permanently failed: building stays set so no new runner starts, and the
// failure branch of forceBuilder re-panics for every subsequent Force. Only
// the single runner poisons.
//
// A cell that settled while its builder ran — from trust, under another
// force's boundary — keeps its certificate: its waiters were woken with it,
// so the failed build is the runner's to report and is not recorded here.
func (c *_PromiseCell) poison(r any) {
	c.mu.Lock()
	defer c.mu.Unlock()
	utils.Assert(c.poisoned == nil)
	if !c.thm.IsZero() {
		return
	}
	c.poisoned = r
	close(c.done)
}

// repanicPoisoned re-raises a poisoned cell's recorded builder panic for a
// non-runner caller, wrapped so the trace shows it is a replay of an earlier
// builder panic rather than a fresh build.
func (c *_PromiseCell) repanicPoisoned() {
	c.mu.Lock()
	r := c.poisoned
	c.mu.Unlock()
	utils.Assert(r != nil)
	panic(fmt.Sprintf("theorem promise %s is poisoned — its builder panicked: %v",
		c.AlphaKey(), r))
}

// forceDerived forces every dependency to a certificate, then stamps the
// statement. It does not serialize: forcing deps is idempotent and the final
// settle is mutex-guarded and idempotent, so concurrent callers converge. Each
// dep is a kernel value of Thm (deriveProp's guard). Derived cells carry their
// caller's builder identity and trust boundary through to the dependencies;
// they do not serialize or merge their concurrent force invocations.
func (c *_PromiseCell) forceDerived(parent *_PromiseCell, ctx context.Context, boundary *_ForceBoundary) ThmCert {
	var assumes *_Assumptions
	for _, dep := range c.deps {
		cert := forceThm(dep, parent, ctx, boundary)
		utils.Assert(cert.Proved())
		assumes = assumes.union(cert.assumes)
	}
	c.settle(certify(*c._Statement, assumes))
	return c.result()
}

func (c *_PromiseCell) tryRealizeReadyDeps() {
	if len(c.deps) == 0 {
		return
	}
	if !c.result().IsZero() {
		return
	}
	var assumes *_Assumptions
	for _, dep := range c.deps {
		if !dep.Proved() {
			return
		}
		assumes = assumes.union(dep.AsThmCert().assumes)
	}
	c.settle(certify(*c._Statement, assumes))
}

// settle records the cell's certificate. The soundness gate: the thm must be a
// real certificate whose statement α-equals this cell's promised statement, or
// settle panics. Idempotent — a second settle with a matching statement is a
// no-op; a non-matching one panics.
func (c *_PromiseCell) settle(thm ThmCert) {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.poisoned != nil {
		// A poisoned cell never settles; done is already closed, and accepting
		// a certificate now would mask the earlier builder panic.
		panic(fmt.Sprintf("theorem promise %s is poisoned — its builder panicked: %v",
			c.AlphaKey(), c.poisoned))
	}
	if thm.IsZero() || !thm.alphaEquals(c._Statement) {
		got := "the zero certificate"
		if !thm.IsZero() {
			got = string(thm.AlphaKey())
		}
		panic(fmt.Sprintf("theorem promise settled with non-matching statement: got %s, want %s",
			got, c.AlphaKey()))
	}
	if !c.thm.IsZero() {
		return // already settled with a matching statement; idempotent
	}
	c.thm = thm
	close(c.done)
}

func (c *_PromiseCell) result() ThmCert {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.thm
}

// deriveProp is the common proof-propagation tail for primitive inference
// rules. The caller has already checked the rule's side conditions and built
// the exact result statement, so if every dependency is proved this primitive
// may return a real theorem. If some dependency is a promise and no dependency
// is a permanently-unproved plain Prop, return a derived promise that will
// become a theorem once its dependencies do.
//
// Every dependency must be proven-or-provable (a Thm — a ThmCert or a
// ThmPromise); a bare proposition means the rule cannot derive, so we hand
// back the plain statement unproved. A dependency is read through kernel(),
// never through a wrapper's own Proved or Core, and kernel() refuses a
// handle that holds no statement. The survivors are kernel values, held in
// the derived cell as the handles they are now and forced by method.
//
// The certificate minted here stands on what the dependencies assume.
func deriveProp(statement _Statement, deps ...Prop) Prop {
	thmDeps := make([]Thm, len(deps))
	needsPromise := false
	var assumes *_Assumptions
	for i, dep := range deps {
		t, ok := dep.kernel().(Thm)
		if !ok {
			return propose(statement) // a dependency is unprovable — cannot derive
		}
		thmDeps[i] = t
		if !t.Proved() {
			needsPromise = true // an unforced promise dep → the result is a promise
		} else if !needsPromise {
			assumes = assumes.union(t.AsThmCert().assumes)
		}
	}
	if needsPromise {
		return newDerivedThmPromise(statement, thmDeps)
	}
	return certify(statement, assumes)
}
