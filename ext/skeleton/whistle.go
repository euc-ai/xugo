// whistle.go implements the trajectory side of the divergence whistle:
// a per-branch history of goals visited by a rewrite-to-fixpoint driver,
// with the "does the current goal embed an earlier one?" check that
// signals divergence. The encoding and the WQO/completeness argument
// live in embed.go.
//
// Intended use (see prover/tactic mergeTactics): the driver extends the
// trajectory with each goal it recurses into, and — once past a backstop
// depth that no terminating stored-corpus trajectory reaches — asks
// EmbedsAncestor before continuing. A positive answer means the branch
// is re-containing structure it already visited (growth) or exactly
// revisiting a state modulo α/free-var renaming (loop); the driver stops
// and returns the current goal as-is. Stopping is always sound: the only
// cost of a false positive is a less-simplified subgoal.

package skeleton

import (
	"bytes"
	"fmt"
	"runtime"
	"strconv"
	"sync"
	"sync/atomic"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

// WhistleEvent describes one divergence-whistle cut. Whistle fires are
// a TRIPWIRE, not telemetry: on healthy paths they are impossible by
// construction (the per-rule prefilter guards plus backstops sized
// above every legitimate maximum), so any fire is a signal that a
// divergent rule got through — a state that would otherwise hang a
// session. A driver that walks goals sets Goal and Entry, one that
// walks bare terms sets Term.
type WhistleEvent struct {
	// Driver names the fixpoint driver that cut: "mergeTactics",
	// "DeepRewriteWhistled", or "RewriteConclRhsRecurWhistled".
	Driver string
	// Depth is the trajectory depth at the cut (mergeTactics /
	// RewriteConclRhsRecurWhistled) or the number of the fire that was
	// cut (DeepRewriteWhistled).
	Depth int
	// Budget is the backstop that was exceeded before the whistle
	// engaged.
	Budget int
	// Open is the number of open leaves the fixpoint had produced when
	// it refused its expansion (mergeTactics' breadth backstop); zero
	// for the depth whistles.
	Open int
	// Goal is the goal at the cut point (goal-trajectory drivers).
	Goal core.Prop
	// Entry is the goal the fixpoint was entered with (goal-trajectory
	// drivers): the root of the cut branch's trajectory. For a breadth
	// cut it is the statement to read — the goal whose case analysis was
	// refused — where Goal is the leaf that happened to reach the count,
	// every split already taken.
	Entry core.Prop
	// Term is the entry/cut term (term-trajectory drivers).
	Term core.Term
	// Step names the step that was running: the label of the innermost
	// watch open on the goroutine that reported the cut (WatchWhistle).
	// Empty when none was open there.
	Step string
}

// String renders the event with core-level identifiers only (skeleton
// cannot import ext/prop for pretty-printing); hook consumers that
// want a readable statement should print Entry/Goal/Term themselves.
func (ev WhistleEvent) String() string {
	var cut string
	switch {
	case ev.Open > 0:
		cut = fmt.Sprintf("whistle driver=%s open=%d budget=%d depth=%d goal=%s",
			ev.Driver, ev.Open, ev.Budget, ev.Depth, ev.Goal.AlphaKey())
	case ev.Goal != nil:
		cut = fmt.Sprintf("whistle driver=%s depth=%d budget=%d goal=%s",
			ev.Driver, ev.Depth, ev.Budget, ev.Goal.AlphaKey())
	case ev.Term != nil:
		cut = fmt.Sprintf("whistle driver=%s fires=%d budget=%d term=%s size=%d",
			ev.Driver, ev.Depth, ev.Budget, ev.Term.AlphaKey(), ev.Term.Size())
	default:
		cut = fmt.Sprintf("whistle driver=%s depth=%d budget=%d",
			ev.Driver, ev.Depth, ev.Budget)
	}
	if ev.Step != "" {
		cut += " step=" + ev.Step
	}
	return cut
}

// whistleFires counts every cut since process start. Always on:
// observation only, never read by proof logic, so it has zero effect
// on results or replay determinism.
var whistleFires atomic.Int64

// OnWhistleFire, when non-nil, receives every WhistleEvent. Install
// ONCE at process init (serve main, test harness setup) before any
// proving concurrency starts — it is read without synchronization on
// the fire path. Typical installs: a stderr printer in the serve
// binary; a collecting gate in the replay harnesses, open around one
// member's replay (where a fire on stored corpus is by definition a
// bug).
var OnWhistleFire func(WhistleEvent)

// ReportWhistleFire records a cut: bumps the process counter, names the
// step watching the reporting goroutine and hands that step the event
// (WatchWhistle), and invokes the hook if installed. Called by the
// fixpoint drivers at their cut points; the fire path is already rare
// and heavyweight (an embedding check just succeeded), so this adds
// nothing measurable.
func ReportWhistleFire(ev WhistleEvent) {
	whistleFires.Add(1)
	if w := watches.innermost(goroutineID()); w != nil {
		ev.Step = w.label()
		for ; w != nil; w = w.outer {
			w.cuts = append(w.cuts, ev)
		}
	}
	if h := OnWhistleFire; h != nil {
		h(ev)
	}
}

// WhistleWatch is one step's view of the whistle: the cuts reported on
// the step's own goroutine while the watch is open. The process counter
// and the hook see every goroutine's cuts and cannot say whose they
// are — in the serve, sessions prove side by side — so a step that must
// know whether ITS search was cut opens a watch around it, and every
// cut reported under the watch carries the step's name
// (WhistleEvent.Step).
//
// A cut belongs to the goroutine that reports it. The fixpoint drivers
// report on the goroutine that called them, so a step that runs its
// tactics on its own goroutine sees all of its cuts; a cut reported on
// a goroutine the step spawned reaches the counter and the hook only.
//
// Watches on one goroutine nest, and close innermost first: a cut is
// named after the innermost and delivered to each.
type WhistleWatch struct {
	goroutine uint64
	label     func() string
	outer     *WhistleWatch
	cuts      []WhistleEvent
	closed    bool
}

// WatchWhistle opens a watch on the calling goroutine. label names the
// step in the events reported under the watch; it is called at a cut
// and not before, so it may be as costly as a message is. Close the
// watch on the goroutine that opened it.
func WatchWhistle(label func() string) *WhistleWatch {
	w := &WhistleWatch{goroutine: goroutineID(), label: label}
	watches.push(w)
	return w
}

// Fired is the number of cuts reported under the watch so far.
func (w *WhistleWatch) Fired() int { return len(w.cuts) }

// Close ends the watch and returns the cuts reported under it, in
// order. A second Close returns the same cuts and does nothing else.
func (w *WhistleWatch) Close() []WhistleEvent {
	if !w.closed {
		watches.pop(w)
		w.closed = true
	}
	return w.cuts
}

// watches holds the innermost open watch of every goroutine that has
// one.
var watches _WatchTable

type _WatchTable struct {
	mu          sync.Mutex
	byGoroutine map[uint64]*WhistleWatch
}

func (t *_WatchTable) innermost(goroutine uint64) *WhistleWatch {
	t.mu.Lock()
	defer t.mu.Unlock()
	return t.byGoroutine[goroutine]
}

func (t *_WatchTable) push(w *WhistleWatch) {
	t.mu.Lock()
	defer t.mu.Unlock()
	if t.byGoroutine == nil {
		t.byGoroutine = map[uint64]*WhistleWatch{}
	}
	w.outer = t.byGoroutine[w.goroutine]
	t.byGoroutine[w.goroutine] = w
}

func (t *_WatchTable) pop(w *WhistleWatch) {
	t.mu.Lock()
	defer t.mu.Unlock()
	if t.byGoroutine[w.goroutine] != w {
		panic(utils.AssertionFailed + " skeleton: a whistle watch closed while a watch opened inside it is still open")
	}
	if w.outer == nil {
		delete(t.byGoroutine, w.goroutine)
		return
	}
	t.byGoroutine[w.goroutine] = w.outer
}

// goroutineID is the calling goroutine's id. The runtime exports none;
// the one place it prints it is the header of the goroutine's stack
// trace, "goroutine <id> [<state>]:", and it is read from there — once
// when a watch opens and once at a cut, tens of microseconds each time
// (the trace is formatted whole before it is cut to the buffer). A
// header that does not read this way is an assertion failure, which no
// recover of a step reads as the step's failure: a watch that could not
// tell goroutines apart would hand one session another's cuts.
func goroutineID() uint64 {
	var buf [64]byte
	header := buf[:runtime.Stack(buf[:], false)]
	digits, found := bytes.CutPrefix(header, []byte("goroutine "))
	end := bytes.IndexByte(digits, ' ')
	if !found || end <= 0 {
		panic(fmt.Sprintf("%s skeleton: no goroutine id in the stack header %q", utils.AssertionFailed, header))
	}
	id, err := strconv.ParseUint(string(digits[:end]), 10, 64)
	if err != nil {
		panic(fmt.Sprintf("%s skeleton: no goroutine id in the stack header %q: %v", utils.AssertionFailed, header, err))
	}
	return id
}

// WhistleFires returns the number of whistle cuts since process start.
// Harnesses that promise whistle-free execution (corpus replay) and
// tests read it as a delta around a call.
func WhistleFires() int64 { return whistleFires.Load() }

// Trajectory is one node of a per-branch goal history, linked toward the
// root so sibling branches share their common prefix. The zero value is
// not used; a nil *Trajectory is the empty history and Extend starts a
// chain from it.
//
// Not safe for concurrent use: a trajectory chain must stay within the
// single goroutine driving one top-level tactic call (encodings are
// cached on nodes without synchronization).
type Trajectory struct {
	parent *Trajectory
	depth  int
	goal   core.Prop
	enc    *propEnc // lazily computed on first embedding check
}

// propEnc is the whistle encoding of one goal: the pooled path set of
// its conclusion and hypotheses, plus the total term size for the
// embedding size gate.
type propEnc struct {
	size  int
	paths []EmbPath
}

// Extend returns a new trajectory node for goal, appended to tr.
// A nil receiver starts a fresh trajectory.
func (tr *Trajectory) Extend(goal core.Prop) *Trajectory {
	depth := 1
	if tr != nil {
		depth = tr.depth + 1
	}
	return &Trajectory{parent: tr, depth: depth, goal: goal}
}

// Depth returns the number of goals recorded up to and including tr.
// A nil trajectory has depth 0.
func (tr *Trajectory) Depth() int {
	if tr == nil {
		return 0
	}
	return tr.depth
}

// Entry returns the first goal of tr's branch: the goal its driver was
// entered with.
func (tr *Trajectory) Entry() core.Prop {
	for tr.parent != nil {
		tr = tr.parent
	}
	return tr.goal
}

// encode computes (once) and caches the whistle encoding of tr's goal.
// Conclusion and hypothesis paths are pooled into one set: formula-role
// mixing only coarsens the approximation, which is the safe direction.
func (tr *Trajectory) encode() *propEnc {
	if tr.enc != nil {
		return tr.enc
	}
	size := 0
	seen := make(map[string]struct{})
	var paths []EmbPath
	var prefix []string
	add := func(t core.Term) {
		size += t.Size()
		embWalk(t, &prefix, seen, &paths)
	}
	for i := range tr.goal.NumHyps() {
		add(tr.goal.Hyp(i))
	}
	add(tr.goal.Conclusion())
	tr.enc = &propEnc{size: size, paths: paths}
	return tr.enc
}

// EmbedsAncestor reports whether some strict ancestor's goal embeds
// into tr's goal under the path over-approximation of homeomorphic
// embedding (PathEmbeds), gated on total term size (tree embedding
// implies the earlier term is no larger). True means the branch is
// growing while re-containing earlier structure, or revisiting a state
// up to α-conversion and free-variable renaming — the divergence
// signal. Ancestor encodings are computed lazily and cached, so
// trajectories that never reach the caller's backstop depth pay
// nothing beyond node allocation.
func (tr *Trajectory) EmbedsAncestor() bool {
	cur := tr.encode()
	for anc := tr.parent; anc != nil; anc = anc.parent {
		if embedsInto(anc.encode(), cur) {
			return true
		}
	}
	return false
}

// embedsInto is the shared size-gated embedding check between one
// ancestor encoding and the current encoding.
func embedsInto(anc, cur *propEnc) bool {
	return anc.size <= cur.size && PathEmbeds(anc.paths, cur.paths)
}

// TermTrajectory is the single-term sibling of Trajectory, for
// rewrite-to-fixpoint drivers whose states are bare terms rather than
// goals (ext/prop RewriteConclRhsRecur: the successive right-hand
// sides of one rewrite chain). Same linked-parent sharing, same lazy
// encoding, same concurrency caveat as Trajectory.
type TermTrajectory struct {
	parent *TermTrajectory
	depth  int
	term   core.Term
	enc    *propEnc
}

// Extend returns a new trajectory node for t, appended to tr.
// A nil receiver starts a fresh trajectory.
func (tr *TermTrajectory) Extend(t core.Term) *TermTrajectory {
	depth := 1
	if tr != nil {
		depth = tr.depth + 1
	}
	return &TermTrajectory{parent: tr, depth: depth, term: t}
}

// Depth returns the number of terms recorded up to and including tr.
// A nil trajectory has depth 0.
func (tr *TermTrajectory) Depth() int {
	if tr == nil {
		return 0
	}
	return tr.depth
}

func (tr *TermTrajectory) encode() *propEnc {
	if tr.enc != nil {
		return tr.enc
	}
	tr.enc = &propEnc{size: tr.term.Size(), paths: EmbPaths(tr.term)}
	return tr.enc
}

// EmbedsAncestor is TermTrajectory's divergence signal — identical
// semantics to Trajectory.EmbedsAncestor, over single terms.
func (tr *TermTrajectory) EmbedsAncestor() bool {
	cur := tr.encode()
	for anc := tr.parent; anc != nil; anc = anc.parent {
		if embedsInto(anc.encode(), cur) {
			return true
		}
	}
	return false
}
