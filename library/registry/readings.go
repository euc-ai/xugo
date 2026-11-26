// readings.go — the laws readable through a projection.
//
// A PROJECTION is a law of one structure whose body states another
// structure at terms over the first's components: `comm_ring_on(R) ⇒
// abelian_group_on(additive_group(R))` (comm_ring.AddGroupOn),
// `ring_homomorphism(R, S, f) ⇒ group_homomorphism(additive_group(R),
// additive_group(S), f)` (ring_homomorphism.AdditiveHomomorphism),
// `comm_ring_on(R) ⇒ is_topology(zariski_topology(R))`
// (prime_spectrum's Zariski topology). Read at a fact of the first structure, a
// projection is an instance of the second, and every law of the second
// is then a value at it — `group_homomorphism.MapOne.Read(
// ring_homomorphism.AdditiveHomomorphism.Read(hom))` states that a ring
// homomorphism keeps zero — which the constitution's §Readings says is
// cited where it is used and never written as a member. What a
// projection makes readable is therefore stated by no entry; this file
// derives it, so that `retrieve`, `query` and the index find it.
//
// The derivation is the kernel's, the one a cite of the reading runs,
// taken at the laws' statements (proof.ReadLawStated): the root
// structure's fact is assumed, the projection is read at it, and each
// law of the structure it states is read at that — a projection among
// them states a third structure, and the walk continues through it
// while the chain visits no structure twice. The body is the one a cite
// hands over, in the instance normal form with the record equations
// installed (prover/tactic, InstanceNormal), each read as its
// statement, so the view builds no proof: a law read at a packed record
// value states its parts. The derived sequent `A(comps) ⊢ body` is then
// written back as the Horn law `∀comps. A(comps) ⇒ body` over the
// root's components — the assumption and the instantiation the walk
// made, undone — so it is matched as a member's statement is. Two
// chains deriving one statement (the ring's additive monoid read
// directly, or through its additive group) keep the shorter. The view
// keeps each statement it derives in nodes shared across all of them
// (readings_sharing.go), since the readings instantiate the same laws
// at the same components many times over. Nothing here is registered:
// a Readable is a view the registry computes from the structure laws
// among the entries, once per state of those laws, of the structure
// predicates and of the record equations installed — what the walk
// reads; an entry that is no structure law leaves the view as it
// stands. The view is walked whole, in the background from an engine's
// construction (WarmReadables), the roots in parallel on half the
// cores; the doors that read it (Readables, ReadablesFor,
// UnreadableLaws) wait for that walk. A view replaced while its walk
// runs walks no further root, and those doors read the view that
// replaced it. A reader of one projection — the index, its pages and
// `xugo query` — asks for its first level alone
// (ReadableDirectlyThrough): the laws of the structure the projection
// states, read at it, and no chain further, so it walks nothing of the
// view. Each readable is prepared as a head in the walk
// (proof.StatedHeadOf) and the view keeps them under an index by the
// rigid heads of the conclusions the plan reads them at, read in the
// instance normal form the view is computed at, since they are many
// times the members: a scan at a goal reads the ones at the goal's head
// and the wild ones alone (ReadablesFor), each declined or read from
// its prepared form.

package registry

import (
	"fmt"
	"runtime"
	"slices"
	"strings"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
)

// Projection is a law of one structure whose body states another: read
// at a fact of From, it is an instance of To.
type Projection struct {
	Law *ProofEntry
	// From and To are the two structures' predicates.
	From, To string
}

// Readable is a law of one structure read through a chain of
// projections from another: the law, the projections it is read
// through — the root structure's first, the law's own structure's last
// — and the statement the reading derives, closed into a Horn law over
// the root structure's components. In Go the value is
// `Law.Read(Through[n-1].Read(… Through[0].Read(fact)))`, the fact a
// statement of the root structure.
type Readable struct {
	Law     *ProofEntry
	Through []*ProofEntry
	// Statement is `∀comps. A(comps) ⇒ body`, A the root structure, body
	// the law's at the components the chain pins; derived by the
	// kernel, keyless, and kept in the view's shared nodes when the whole
	// walk derived it.
	Statement core.Prop
	// sequent retains the root hypothesis separately from the derived
	// conclusion, so spelling the body never searches for an implication.
	sequent core.Prop
	// head is Statement prepared to be read at a goal; the view indexes
	// the readable under its rigid heads. Nil for a readable the
	// first-level door serves (ReadableDirectlyThrough).
	head *proof.StatedHead
}

// Head is the derived statement prepared to be read as a head at a
// goal, once, in the whole walk; nil for a readable the first-level
// door serves, which no goal is matched against.
func (r Readable) Head() *proof.StatedHead { return r.head }

// BodyText spells the derived conclusion in the root chapter's notation.
// The sequent supplies the structure facts that license that notation;
// removing its declaration prelude leaves every binder and condition of
// the conclusion intact, even when the closed law has a bundle binder.
func (r Readable) BodyText() string {
	text := r.Root().Family().SpellStatement(r.sequent)
	_, body, ok := strings.Cut(text, "⊢")
	if !ok {
		panic("registry: a readable law's sequent has no turnstile")
	}
	return strings.TrimSpace(body)
}

// Depth is the chain's length.
func (r Readable) Depth() int { return len(r.Through) }

// Root is the projection the chain starts at: a law of the structure
// whose fact the whole reading is read at.
func (r Readable) Root() *ProofEntry { return r.Through[0] }

// StandsOnCard reports whether the law or a projection in the chain is
// a card, so a cite of the reading stands on one.
func (r Readable) StandsOnCard() bool {
	if r.Law.IsCard() {
		return true
	}
	for _, p := range r.Through {
		if p.IsCard() {
			return true
		}
	}
	return false
}

// readingsView is the view of one state of the registry: the structure
// laws it is computed from — the registry is process-global and a test
// or a session registers entries after the chapters, so a view computed
// before a structure law is recomputed — and the generations of the
// structure predicates and of the record equations a reading's
// instance is computed with (structureGeneration,
// tactic.RecordNormalGeneration). The projections are listed once, by
// the first door that asks (prepare); each projection's readables are
// derived once, by the whole walk (root); and the whole walk, once
// started (start), closes ready when every root is walked and the
// readables are indexed by head, or, the view replaced (stop), when the
// roots already walking are walked, cut.
type readingsView struct {
	laws       []shapedLaw
	structures uint64
	records    uint64

	prepareOnce sync.Once
	shapes      map[*ProofEntry]lawShape
	lawsOf      map[string][]*ProofEntry
	projections []Projection
	// roots holds each projection's walk, by the projection law.
	roots map[*ProofEntry]*rootWalk
	// shared is the table every root's readables are kept in, dropped
	// when the whole walk ends.
	shared *_sharing

	startOnce sync.Once
	ready     chan struct{}
	// stop closes when a view of a later state replaces this one; cut
	// records, before ready closes, that the whole walk stopped at it
	// with roots unwalked and indexed nothing.
	stop chan struct{}
	cut  bool
	all  []Readable
	// byHead holds the positions in all of the readables at each rigid
	// head, ascending, a readable under each head of its readings; the
	// zero head's are the wild ones.
	byHead map[proof.RigidHead][]int
	// skipped records the laws a chain could not read — a law stated
	// at a type the projection's components do not fit — by the law's
	// name, the chain and the reading's refusal.
	skipped []string
}

// rootWalk is one projection's walk: the structure the projection
// states, and, derived once, the laws readable through it and the laws
// its chains could not read.
type rootWalk struct {
	to        string
	once      sync.Once
	readables []Readable
	skipped   []string
}

// shapedLaw is a structure law among the entries, shaped.
type shapedLaw struct {
	entry *ProofEntry
	shape lawShape
}

var readings struct {
	mu   sync.Mutex
	view *readingsView
	// read is how many of the registry's entries are read for the
	// structure laws among them, laws those laws in registration order,
	// and structures the generation of the structure predicates they
	// were read at: a structure added later may make a law read before
	// it one, so the entries are read again from the first.
	read       int
	laws       []shapedLaw
	structures uint64
}

// view is the view of the registry as it stands: the current one, or a
// new one, nothing of it computed yet, which replaces the current one.
// The structure laws only grow — an entry is never removed, and a
// predicate never stops being a structure — so a view whose laws are as
// many as the registry's has the registry's.
func view() *readingsView {
	readings.mu.Lock()
	defer readings.mu.Unlock()
	entries := all
	structures := structureGeneration.Load()
	records := tactic.RecordNormalGeneration()
	if structures != readings.structures {
		readings.read, readings.laws, readings.structures = 0, nil, structures
	}
	for _, e := range entries[readings.read:] {
		if shape, ok := shapeLaw(e); ok {
			readings.laws = append(readings.laws, shapedLaw{entry: e, shape: shape})
		}
	}
	readings.read = len(entries)
	if v := readings.view; v != nil && len(v.laws) == len(readings.laws) && v.structures == structures && v.records == records {
		return v
	}
	if v := readings.view; v != nil {
		close(v.stop)
	}
	v := &readingsView{laws: readings.laws, structures: structures, records: records, ready: make(chan struct{}), stop: make(chan struct{})}
	readings.view = v
	return v
}

// startReadings is the view with its whole walk started.
func startReadings() *readingsView {
	v := view()
	v.start()
	return v
}

// currentReadings is the view, walked whole: a view whose walk was cut
// is read past, to the one that replaced it.
func currentReadings() *readingsView {
	for {
		v := startReadings()
		<-v.ready
		if !v.cut {
			return v
		}
	}
}

// WarmReadables starts computing the view in the background, so that
// the first request reading it waits for none of the walk. An engine
// calls it at construction.
func WarmReadables() { startReadings() }

// Projections lists every projection law, in registration order.
func Projections() []Projection {
	v := view()
	v.prepare()
	return v.projections
}

// ProjectionOf reports the projection a law is, when it is one.
func ProjectionOf(law *ProofEntry) (Projection, bool) {
	v := view()
	v.prepare()
	for _, p := range v.projections {
		if p.Law == law {
			return p, true
		}
	}
	return Projection{}, false
}

// ReadableDirectlyThrough lists the laws of the structure a projection
// law states, read through it: the first level of the walk from the
// projection — each law of that structure in registration order, one
// entry per derived statement, its chain the projection alone — and no
// chain further. Nil for a law that is no projection. The view is not
// walked, and the readables are not prepared as heads: a goal is
// matched against the whole view (ReadablesFor).
func ReadableDirectlyThrough(law *ProofEntry) []Readable {
	v := view()
	v.prepare()
	r := v.roots[law]
	if r == nil {
		return nil
	}
	shape, first := v.firstHop(law, r.to)
	direct, _, _ := v.readHop(shape, first, map[int][]core.Prop{})
	return direct
}

// Readables lists every law readable through every projection, root
// by root in registration order, waiting for the view when its walk is
// still running.
func Readables() []Readable { return currentReadings().all }

// ReadablesFor is Readables narrowed to what a scan at a goal
// concluding target has to read: the readables one of whose readings
// of their statement's conclusion the target may match by its rigid
// head (proof.RigidHead.MayMatch) — headed by a variable or by a
// projection of the reading's record binder, whose part the instance
// decides, or by the target's own constant at as many arguments — in
// the order of Readables, each once. The apply rung's plan declines
// every other before anything else (proof.StatedHead.Read), so the
// candidates read as the whole view would.
func ReadablesFor(target core.Term) []Readable { return currentReadings().candidates(target) }

// ReadablesForIfReady is ReadablesFor without the wait: ok is false
// while the walk is still running, and the caller on a request path
// answers without the view rather than hold the request for it.
func ReadablesForIfReady(target core.Term) ([]Readable, bool) {
	for {
		v := startReadings()
		select {
		case <-v.ready:
			if v.cut {
				continue
			}
			return v.candidates(target), true
		default:
			return nil, false
		}
	}
}

// candidates lists the readables at the target's rigid head and the
// wild ones, merged in the order of all, a readable under both once.
func (v *readingsView) candidates(target core.Term) []Readable {
	wild := v.byHead[proof.RigidHead{}]
	head := proof.RigidHeadOf(target)
	if head.Wild() {
		return v.at(wild)
	}
	same := v.byHead[head]
	positions := make([]int, 0, len(wild)+len(same))
	for len(wild) > 0 && len(same) > 0 {
		switch {
		case wild[0] < same[0]:
			positions, wild = append(positions, wild[0]), wild[1:]
		case wild[0] > same[0]:
			positions, same = append(positions, same[0]), same[1:]
		default:
			positions, wild, same = append(positions, wild[0]), wild[1:], same[1:]
		}
	}
	positions = append(append(positions, wild...), same...)
	return v.at(positions)
}

// at lists the readables at the positions in all.
func (v *readingsView) at(positions []int) []Readable {
	out := make([]Readable, len(positions))
	for i, p := range positions {
		out[i] = v.all[p]
	}
	return out
}

// UnreadableLaws lists the laws some chain could not read, each with
// the reading's refusal: a law of the structure stated at a type its
// projection's components do not fit.
func UnreadableLaws() []string { return currentReadings().skipped }

// lawShape is a structure law read for the walk: its structure's
// predicate, its hypothesis `S(comps)`, its binders and its body.
type lawShape struct {
	pred       string
	hypothesis core.Term
	body       core.Term
	binders    []core.VarTerm
}

// shapeLaw shapes an entry when it is a structure law: a law whose
// hypothesis is a structure predicate applied to its components.
func shapeLaw(e *ProofEntry) (lawShape, bool) {
	hyp, body, binders, ok := proof.StructureLaw(e.Statement().Prop)
	if !ok {
		return lawShape{}, false
	}
	pred := predicateOf(hyp)
	if !IsStructurePredicate(pred) {
		return lawShape{}, false
	}
	return lawShape{pred: pred, hypothesis: hyp, body: body, binders: binders}, true
}

// prepare indexes the structure laws by their structure and lists the
// projections, once.
func (v *readingsView) prepare() {
	v.prepareOnce.Do(func() {
		v.shapes = map[*ProofEntry]lawShape{}
		v.lawsOf = map[string][]*ProofEntry{}
		for _, l := range v.laws {
			v.shapes[l.entry] = l.shape
			v.lawsOf[l.shape.pred] = append(v.lawsOf[l.shape.pred], l.entry)
		}
		v.roots = map[*ProofEntry]*rootWalk{}
		for _, l := range v.laws {
			if to, ok := v.projectsTo(l.entry); ok {
				v.projections = append(v.projections, Projection{Law: l.entry, From: l.shape.pred, To: to})
				v.roots[l.entry] = &rootWalk{to: to}
			}
		}
		v.shared = newSharing()
	})
}

// projectsTo is the structure a law's body states, when the law is a
// projection: a structure law whose body is headed by another
// structure's predicate.
func (v *readingsView) projectsTo(e *ProofEntry) (string, bool) {
	sh, ok := v.shapes[e]
	if !ok {
		return "", false
	}
	to := predicateOf(sh.body)
	if to == "" || to == sh.pred || !IsStructurePredicate(to) {
		return "", false
	}
	return to, true
}

// root is a projection law's walk, derived once; nil for a law that is
// no projection.
func (v *readingsView) root(law *ProofEntry) *rootWalk {
	v.prepare()
	r := v.roots[law]
	if r == nil {
		return nil
	}
	r.once.Do(func() { r.readables, r.skipped = v.walk(law, r.to) })
	return r
}

// start starts the whole walk in the background, once; ready closes
// when it is done.
func (v *readingsView) start() {
	v.startOnce.Do(func() {
		go func() {
			defer close(v.ready)
			v.compute()
		}()
	})
}

// replaced reports whether a view of a later state replaced this one.
func (v *readingsView) replaced() bool {
	select {
	case <-v.stop:
		return true
	default:
		return false
	}
}

// compute walks every projection to the fixpoint of the structures it
// reaches, the roots in parallel, and indexes the readables, in
// registration order — or, the view replaced, stops walking, cut.
func (v *readingsView) compute() {
	v.prepare()
	var wg sync.WaitGroup
	// Half the cores walk, the rest serve the requests the walk
	// overlaps — an engine's first, since the walk starts at its
	// construction: with every core walking, a request is runnable and
	// starved, and answers several times slower. The walk is bound by
	// its largest roots rather than by cores, and takes little longer
	// on half of them.
	workers := make(chan struct{}, max(1, runtime.GOMAXPROCS(0)/2))
	for _, p := range v.projections {
		select {
		case workers <- struct{}{}:
		case <-v.stop:
		}
		// A replaced view walks no further root; the roots already
		// walking finish.
		if v.replaced() {
			v.cut = true
			break
		}
		wg.Go(func() {
			defer func() { <-workers }()
			v.root(p.Law)
		})
	}
	wg.Wait()
	// No root is walked after the whole walk, so no walk reads the
	// table again: the readables hold their shared nodes, and the
	// table's maps go.
	v.shared = nil
	if v.cut {
		// A cut view indexes nothing: the doors read past it.
		return
	}
	v.byHead = map[proof.RigidHead][]int{}
	for _, p := range v.projections {
		r := v.roots[p.Law]
		for _, readable := range r.readables {
			for _, rigid := range readable.head.Rigids() {
				v.byHead[rigid] = append(v.byHead[rigid], len(v.all))
			}
			v.all = append(v.all, readable)
		}
		v.skipped = append(v.skipped, r.skipped...)
	}
}

// hop is one chain under construction: the projections so far, the
// derived instance `A(comps) ⊢ T(args)` the next law is read at, the
// structure T it states, and the structures the chain has visited.
type hop struct {
	through  []*ProofEntry
	instance core.Prop
	pred     string
	visited  map[string]bool
}

// firstHop is the hop a walk from root, a projection stating to,
// starts at: the projection read at its own hypothesis.
func (v *readingsView) firstHop(root *ProofEntry, to string) (lawShape, hop) {
	shape := v.shapes[root]
	first, err := proof.ReadLawStated(root.Statement().Prop, core.Assume(shape.hypothesis))
	if err != nil {
		panic(fmt.Sprintf("registry: the projection %s does not read at its own hypothesis: %v", root.Name, err))
	}
	return shape, hop{through: []*ProofEntry{root}, instance: first, pred: to, visited: map[string]bool{shape.pred: true, to: true}}
}

// readHop reads each law of the structure h states at h's instance, in
// registration order, closed over shape, the root's: the readings whose
// statement seen does not hold yet, recorded in seen; the laws the
// instance does not read, with the reading's refusal; and the hops the
// projections among the readings continue to, each into a structure
// the chain has not visited. seen holds the statements derived so far
// by size: a derived statement is fresh, so it is recognized by
// α-equality with the ones of its size rather than by a key, which
// would copy and hash every node of it.
func (v *readingsView) readHop(shape lawShape, h hop, seen map[int][]core.Prop) (out []Readable, skipped []string, next []hop) {
	for _, law := range v.lawsOf[h.pred] {
		stated := freshenLooseLetters(law.Statement().Prop, v.shapes[law].binders, h.instance)
		derived, err := proof.ReadLawStated(stated, h.instance)
		if err != nil {
			skipped = append(skipped, fmt.Sprintf("%s through %s: %v", law.Name, chainNames(h.through), err))
			continue
		}
		closed := hornLaw(shape.binders, shape.hypothesis, derived.Conclusion())
		size := closed.Size()
		if slices.ContainsFunc(seen[size], closed.AlphaEquals) {
			continue
		}
		seen[size] = append(seen[size], closed)
		out = append(out, Readable{Law: law, Through: h.through, Statement: closed, sequent: derived})
		if to, ok := v.projectsTo(law); ok && !h.visited[to] {
			visited := map[string]bool{to: true}
			for p := range h.visited {
				visited[p] = true
			}
			through := append(append([]*ProofEntry{}, h.through...), law)
			next = append(next, hop{through: through, instance: derived, pred: to, visited: visited})
		}
	}
	return out, skipped, next
}

// walk derives the laws readable through root, a projection stating
// to, breadth-first, so the first chain to derive a statement is a
// shortest one, and keeps each reading in the view's shared nodes.
func (v *readingsView) walk(root *ProofEntry, to string) (out []Readable, skipped []string) {
	shape, first := v.firstHop(root, to)
	queue := []hop{first}
	seen := map[int][]core.Prop{}
	for len(queue) > 0 {
		h := queue[0]
		queue = queue[1:]
		read, refused, next := v.readHop(shape, h, seen)
		out = append(out, read...)
		skipped = append(skipped, refused...)
		queue = append(queue, next...)
	}
	v.shared.share(out)
	for i := range out {
		out[i].head = proof.StatedHeadOf(out[i].Statement)
	}
	return out, skipped
}

// hornLaw is the statement `∀binders. hypothesis ⇒ body`: a derived
// sequent's conclusion written back under the root's hypothesis and
// components.
func hornLaw(binders []core.VarTerm, hypothesis, body core.Term) core.Prop {
	t := core.Term(ext.WrapTerm(hypothesis).Imply(body))
	for i := len(binders) - 1; i >= 0; i-- {
		t = ext.ForAll(binders[i])(t)
	}
	return prop.MakeProp(t)
}

func chainNames(through []*ProofEntry) string {
	names := make([]string, len(through))
	for i, p := range through {
		names[i] = p.Name
	}
	return fmt.Sprint(names)
}

// predicateOf is the constant at the head of a term's application
// spine, "" where the head is no constant.
func predicateOf(t core.Term) string {
	head, _ := ext.MatchesApply(t)
	if c, ok := head.AsConst(); ok {
		return string(c.Name())
	}
	return ""
}

// freshenLooseLetters renames the type letters of a law that no
// component binder's type carries — the letters its instance cannot
// fix — away from the letters the instance carries, so that reading
// the law at the instance does not conflate a letter of the law with
// one of the instance's. A law without such a collision is returned
// as it is.
func freshenLooseLetters(law core.Prop, binders []core.VarTerm, instance core.Prop) core.Prop {
	fixed := map[core.TypeName]bool{}
	for _, b := range binders {
		for _, v := range b.Type().TypeVars() {
			fixed[v.Name()] = true
		}
	}
	taken := map[core.TypeName]bool{}
	note := func(v core.VarType) bool { taken[v.Name()] = true; return false }
	ext.TermAnyTypeVar(instance.Conclusion(), note)
	for _, h := range instance.Hyps() {
		ext.TermAnyTypeVar(h, note)
	}
	var loose []core.VarType
	seen := map[core.TypeName]bool{}
	ext.TermAnyTypeVar(law.Conclusion(), func(v core.VarType) bool {
		if !fixed[v.Name()] && !seen[v.Name()] {
			seen[v.Name()] = true
			loose = append(loose, v)
		}
		return false
	})
	var subst []core.TypeSubst
	for _, v := range loose {
		if !taken[v.Name()] {
			continue
		}
		subst = append(subst, core.MakeTypeSubst(v, core.MakeVarType(freshLetter(taken, seen))))
	}
	if len(subst) == 0 {
		return law
	}
	return prop.WrapProp(law).TypeInst(subst...)
}

// freshLetter picks a type letter neither map holds and marks it taken.
func freshLetter(taken, used map[core.TypeName]bool) string {
	for i := 0; ; i++ {
		var name string
		if i < 26 {
			name = string(rune('A' + i))
		} else {
			name = fmt.Sprintf("T%d", i-25)
		}
		if !taken[core.TypeName(name)] && !used[core.TypeName(name)] {
			taken[core.TypeName(name)] = true
			return name
		}
	}
}
