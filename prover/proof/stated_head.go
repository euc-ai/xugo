// stated_head.go — a stated form prepared to be read as a head.
//
// `retrieve` reads a goal against every member's statement and against
// every law readable through a projection (registry.Readables), by the
// apply rung's own plan. What the plan costs at one stated form is the
// type instances it enumerates and the matches it runs; what it decides
// before either depends on the stated form alone and on little of the
// goal — the rigid skeleton of the conclusion, with its types, and
// whether anything could pin the binders the conclusion does not spell
// — so a StatedHead computes it once per stated form, off the request
// path, and a scan declines most of its candidates at the cost of a
// lookup. The registry keeps one per readable law (under its rigid
// head, the index) and per member statement.
//
// A law stated at a structure record — `∀R:ring_ops(A). comm_ring(R) ⇒
// ∀x:A. R.zero * x = R.zero`, raw `ring_mul(R, ring_zero(R), x) =
// ring_zero(R)` — spells its operations as record projections applied
// to the record binder. At a concrete instance those projections are
// computed away: the instance normal form (prover/tactic,
// InstanceNormal) makes `ring_mul(real_ring)` the `real_mul` the goal
// `&0 * x = &0` spells. A projection applied to a record a stated
// binder decides therefore has no rigid head of its own: the instance
// decides it. The skeleton defers such a node and reads it at the
// record values the goal's hypotheses and the facts offer for the
// binder at the antecedent pieces that take it whole (`comm_ring(R)`
// against `comm_ring(real_ring)`), by the head of the projection's
// part at each value; and Read, where the conclusion as stated meets
// nothing, pins those binders first, from the pieces that take them
// whole, and matches the conclusion read at them in the instance
// normal form — the instance `by` hands over when it reads the law at
// that fact.

package proof

import (
	"context"
	"maps"
	"slices"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// StatedHead is a stated form prepared to be read as a head at any
// goal: the form with its free variables ∀-closed (an install closes
// them too; the binder order differs, and nothing reads the order),
// the conclusions the plan reads it at with the rigid head at the top
// of each, and what its binders are pinned by — the conclusion for the
// ones it spells, and for the rest the antecedent pieces that spell
// them, by the constant at each piece's head.
type StatedHead struct {
	closed core.Prop
	// conclusions are the plan's readings of the matrix — the
	// conclusion under the guarded ∀s, its leading antecedents stripped
	// — as matchHeadSpelling lists them: the matrix whole; each
	// conjunct, where it is a conjunction; and either side, where it is
	// an ⇔, the other side joining the antecedents, and each conjunct
	// of a side that is a conjunction.
	conclusions []_HeadConclusion
	// binders are the telescope's, as stated; spelled are the names
	// occurring in the conclusion, bound or free — the binders its match
	// can pin are among them.
	binders []core.VarTerm
	spelled []core.TermName
	pieces  []_HeadPiece
	// takenWhole holds, for each binder some antecedent piece takes
	// whole — as an argument of the constant at the piece's head, as a
	// structure fact takes its record (`comm_ring(R)`) — those
	// positions: a hypothesis or a fact at that head offers the binder's
	// value as its argument there. They are what pins a binder the
	// conclusion spells only in the record of a projection, before the
	// conclusion is matched (recordSeeds).
	takenWhole map[core.TermName][]_ArgAt
}

// _HeadConclusion is one reading of the conclusion, with its rigid
// head.
type _HeadConclusion struct {
	term  core.Term
	rigid RigidHead
}

// _HeadPiece is one conjunct of an antecedent, as the plan pins binders
// from it: the constants at its head — as spelled and in the membership
// normal form, "" for a piece headed by a slot — and the names
// occurring in it.
type _HeadPiece struct {
	heads  []core.TermName
	spells []core.TermName
}

// _ArgAt is a position an antecedent piece takes a binder at: the
// constant at the piece's head and the argument's index under it.
type _ArgAt struct {
	head  core.TermName
	index int
}

// StatedHeadOf prepares a stated form. A sequent is prepared as it
// stands: Read declines it, and a variable free in its hypotheses is
// not closed over them. The rigid heads are read in the instance normal
// form installed now (decidedByInstance), the one the registry's view
// of readings is computed at.
func StatedHeadOf(stated core.Prop) *StatedHead {
	closed := prop.WrapProp(stated)
	if stated.NumHyps() == 0 && !closed.Conclusion().AllFree(noVariable) {
		closed = closed.ConclForAllList(closed.Conclusion().Frees(nil)...)
	}
	binders, antes, matrix := telescopeStated(closed.Conclusion())
	h := &StatedHead{closed: closed, binders: binders, takenWhole: map[core.TermName][]_ArgAt{}}
	read := []core.Term{matrix}
	if parts := conjuncts(matrix); len(parts) > 1 {
		read = append(read, parts...)
	}
	if l, r, ok := ext.MatchesIFF(matrix); ok {
		read = append(read, r, l)
		for _, side := range []core.Term{r, l} {
			if parts := conjuncts(side); len(parts) > 1 {
				read = append(read, parts...)
			}
		}
	}
	for _, c := range read {
		h.conclusions = append(h.conclusions, _HeadConclusion{term: c, rigid: h.rigidOf(c)})
	}
	h.spelled = ext.CollectVarNames(matrix, nil)
	for _, a := range antes {
		for _, piece := range conjuncts(a) {
			p := _HeadPiece{heads: []core.TermName{pieceHead(piece)}, spells: ext.CollectVarNames(piece, nil)}
			// The rung's reading moves a piece's head where the piece is
			// itself a membership, `x ∈ {p | φ}` read as φ, or a projection
			// of a packed value, read as the part.
			if read := (rungReader{}).reading(piece); !read.Equals(piece) {
				if head := pieceHead(read); head != p.heads[0] {
					p.heads = append(p.heads, head)
				}
			}
			h.pieces = append(h.pieces, p)
			if p.heads[0] == "" {
				continue
			}
			whole := map[core.TermName]bool{}
			_, args := ext.MatchesApply(piece)
			for i, arg := range args {
				if v, ok := arg.AsVar(); ok && h.isBinder(v.Name()) && !whole[v.Name()] {
					whole[v.Name()] = true
					h.takenWhole[v.Name()] = append(h.takenWhole[v.Name()], _ArgAt{head: p.heads[0], index: i})
				}
			}
		}
	}
	return h
}

// setMemberName is the membership constant, by the name the set_basic
// chapter mints it under.
const setMemberName core.TermName = "set_member"

// pieceHead is the constant at the head of a piece's spine, "" for a
// slot.
func pieceHead(piece core.Term) core.TermName {
	head, _ := unify.SpineHeadConst(piece)
	return head
}

// noVariable is the predicate no variable satisfies: a term all of
// whose free variables satisfy it has none.
func noVariable(core.VarTerm) bool { return false }

// Stated is the prepared form, closed.
func (h *StatedHead) Stated() core.Prop { return h.closed }

// Rigids lists the rigid heads of the conclusions the plan reads the
// form at, the matrix's first, each once: what an index keys the head
// under.
func (h *StatedHead) Rigids() []RigidHead {
	var out []RigidHead
	for _, c := range h.conclusions {
		if !slices.Contains(out, c.rigid) {
			out = append(out, c.rigid)
		}
	}
	return out
}

// rigidOf is a reading's rigid head: wild where the instance decides
// the node at its top.
func (h *StatedHead) rigidOf(t core.Term) RigidHead {
	head, args := rigidHead(t)
	if h.decidedByInstance(head, args) {
		return RigidHead{}
	}
	return head
}

// isBinder reports whether name is one of the stated form's binders.
func (h *StatedHead) isBinder(name core.TermName) bool {
	return slices.ContainsFunc(h.binders, func(b core.VarTerm) bool { return b.Name() == name })
}

// decidedByInstance reports whether a node at a rigid head with these
// arguments is a projection applied to a record a stated binder decides:
// a projection the instance normal form computes
// (tactic.IsRecordProjection) whose record, its first argument, spells
// one of the form's binders. Its value is the instance's — the part of
// the record value the binder is pinned to — so its head is no rigid
// head of the stated form.
func (h *StatedHead) decidedByInstance(head RigidHead, args []core.Term) bool {
	if head.Wild() || head.Abs || len(args) == 0 || !tactic.IsRecordProjection(head.Const) {
		return false
	}
	return !args[0].AllFree(func(v core.VarTerm) bool { return !h.isBinder(v.Name()) })
}

// HeadGoal is a goal prepared to be read against stated heads, once
// per request: the goal and the facts it is read with; the targets a
// head's conclusion is matched against — the goal's conclusion and,
// where that is an equation whose sides differ, the equation the
// other way round, which the plan matches too (matchHeadSpelling's
// flip); and what the goal offers the plan to pin a binder the
// conclusion does not spell — the constants at the head of its
// hypotheses, as spelled and in the membership normal form, and of
// the facts, against which an antecedent piece at that head is
// matched, and whether it has a hypothesis at all, which a piece
// headed by a slot is matched against (the first-order approximation
// of a flexible head). What the skeleton reads a projection node at —
// the record values offered at a position, each projection's part at
// a value — is computed on first ask and kept for the request.
type HeadGoal struct {
	goal    Prop
	facts   *FactSource
	targets []core.Term
	heads   utils.Set[core.TermName]
	hyps    bool
	// byHead holds the hypotheses at each constant head, as spelled and
	// in the membership normal form.
	byHead map[core.TermName][]core.Term
	mu     sync.Mutex
	// offered holds the record values at a position (offeredAt); parts
	// the normal form of a projection at a record value (partAt).
	offered map[_ArgAt][]core.Term
	parts   map[_PartAt]core.Term
}

// _PartAt is a projection at a record value: the projection's name and
// the value, by identity — a term the goal's hypotheses or the facts
// hold.
type _PartAt struct {
	projection core.TermName
	record     core.Term
}

// HeadGoalOf prepares a goal, with the facts it is read with, or nil.
func HeadGoalOf(goal Prop, facts *FactSource) *HeadGoal {
	g := &HeadGoal{goal: goal, facts: facts, heads: utils.EmptySet[core.TermName](), hyps: goal.NumHyps() > 0,
		byHead: map[core.TermName][]core.Term{}, offered: map[_ArgAt][]core.Term{}, parts: map[_PartAt]core.Term{}}
	target := goal.Conclusion()
	g.targets = []core.Term{target}
	if a, b, ok := ext.MatchesEQ(target); ok && !a.AlphaEquals(b) {
		g.targets = append(g.targets, ext.WrapTerm(b).Eq(ext.WrapTerm(a)).Core())
	}
	add := func(t core.Term) {
		if head, ok := unify.SpineHeadConst(t); ok {
			g.heads.Add(head)
			g.byHead[head] = append(g.byHead[head], t)
		}
	}
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		add(h)
		if read := (rungReader{}).reading(h); !read.Equals(h) {
			add(read)
		}
	}
	if facts != nil {
		for head := range facts.ByHead {
			g.heads.Add(head)
		}
	}
	return g
}

// offeredAt lists the record values the goal's hypotheses and the facts
// hold at a position: the argument there of each one at the position's
// head, each once.
func (g *HeadGoal) offeredAt(at _ArgAt) []core.Term {
	g.mu.Lock()
	defer g.mu.Unlock()
	if values, ok := g.offered[at]; ok {
		return values
	}
	var values []core.Term
	collect := func(t core.Term) {
		if _, args := ext.MatchesApply(t); at.index < len(args) && !slices.ContainsFunc(values, args[at.index].AlphaEquals) {
			values = append(values, args[at.index])
		}
	}
	for _, h := range g.byHead[at.head] {
		collect(h)
	}
	if g.facts != nil {
		for _, f := range g.facts.ByHead[at.head] {
			collect(f)
		}
	}
	g.offered[at] = values
	return values
}

// partAt is a projection applied to a record value, in the instance
// normal form (tactic.InstanceNormalTerm) — the record's part the
// projection names, where the value is one the normal form computes at.
// The projection is the stated form's, at the stated letters; its type
// instance is the record's.
func (g *HeadGoal) partAt(projection core.ConstTerm, record core.Term) core.Term {
	key := _PartAt{projection: projection.Name(), record: record}
	g.mu.Lock()
	part, ok := g.parts[key]
	g.mu.Unlock()
	if ok {
		return part
	}
	var env []core.TypeSubst
	if !core.MatchTypeInto(ext.MatchesFun(projection.Type())[0], record.Type(), anyLetter, &env) {
		panic("StatedHead: a projection's record type does not meet the record value its binder's type met (engine invariant)")
	}
	part = tactic.InstanceNormalTerm(core.Apply(projection.TypeSubstitute(env...), record))
	g.mu.Lock()
	g.parts[key] = part
	g.mu.Unlock()
	return part
}

// MayRead is a necessary condition of Read, decided before the stated
// form's type instances are enumerated and before any match runs — the
// enumeration is most of what reading a polymorphic form costs. A
// sequent is out of Read's scope (the stated-form path telescopes a
// conclusion; a sequent member is not read here — a deliberate cut).
// The rigid skeleton of one of the plan's readings of the conclusion
// must sit against one of the goal's targets, with the types
// (_Skeleton.mayMatch), its projection nodes an instance decides read
// at the record values offered (instancesMayMatch); and every binder
// the conclusion does not spell must be spelled by some antecedent
// piece the goal can match — a piece at a head its hypotheses or the
// facts carry, or headed by a slot where it has a hypothesis — since a
// binder nothing pins is the miss the plan reports.
func (h *StatedHead) MayRead(g *HeadGoal) bool {
	may, _ := h.mayRead(g)
	return may
}

// mayRead is MayRead, with whether some reading sits against a target
// only at an instance — through a projection node the skeleton
// deferred — which is where Read pins the record binders first.
func (h *StatedHead) mayRead(g *HeadGoal) (may, atAnInstance bool) {
	if h.closed.NumHyps() > 0 || !h.pinnable(g) {
		return false, false
	}
	for _, c := range h.conclusions {
		for _, target := range g.targets {
			sk := &_Skeleton{head: h}
			if !sk.mayMatch(c.term, target) || !h.instancesMayMatch(g, sk.deferred, sk.letters, nil) {
				continue
			}
			if len(sk.deferred) > 0 {
				return true, true
			}
			may = true
		}
	}
	return may, false
}

func (h *StatedHead) pinnable(g *HeadGoal) bool {
	for _, b := range h.binders {
		if !containsName(h.spelled, b.Name()) && !h.pinnedByAPiece(g, b.Name()) {
			return false
		}
	}
	return true
}

// pinnedByAPiece reports whether some antecedent piece spelling the
// binder is one the goal can match: at a head its hypotheses or the
// facts carry, or headed by a slot where it has a hypothesis.
func (h *StatedHead) pinnedByAPiece(g *HeadGoal, name core.TermName) bool {
	for _, p := range h.pieces {
		if !containsName(p.spells, name) {
			continue
		}
		for _, head := range p.heads {
			if head == "" && g.hyps || head != "" && g.heads.Has(head) {
				return true
			}
		}
	}
	return false
}

func containsName(names []core.TermName, name core.TermName) bool {
	for _, n := range names {
		if n == name {
			return true
		}
	}
	return false
}

// instancesMayMatch decides the projection nodes the skeleton deferred
// (_Deferred) at the instances the goal offers. Read pins a node's
// record binders before the conclusion is matched, each from an
// antecedent piece that takes it whole (recordSeeds), so every binder
// the record spells must be offered a value at such a position
// (offeredFor). Where the record is that binder alone, the node is
// read at each of its values — one value per binder across the nodes
// (at): it sits against the goal's subterm where the projection's part
// at the value does, a part at the subterm's head with the node's
// further arguments the subterm's last ones, which the skeleton reads
// on, the subterm's first ones the part's own. A part headed by a
// variable or an abstraction decides nothing; nor does a node whose
// record is compound, which the skeleton cannot read without building
// the instance.
func (h *StatedHead) instancesMayMatch(g *HeadGoal, pending []_Deferred, letters []core.TypeSubst, at map[core.TermName]core.Term) bool {
	if len(pending) == 0 {
		return true
	}
	d, rest := pending[0], pending[1:]
	binder, bare := d.record.AsVar()
	if !bare {
		for _, v := range d.record.Frees(nil) {
			if h.isBinder(v.Name()) && len(h.offeredFor(g, v.Name())) == 0 {
				return false
			}
		}
		return h.instancesMayMatch(g, rest, letters, at)
	}
	values, assigned := []core.Term{at[binder.Name()]}, at[binder.Name()] != nil
	if !assigned {
		values = h.offeredFor(g, binder.Name())
	}
	for _, v := range values {
		sub := slices.Clone(letters)
		if !core.MatchTypeInto(binder.Type(), v.Type(), anyLetter, &sub) {
			continue
		}
		next := at
		if !assigned {
			next = maps.Clone(at)
			if next == nil {
				next = map[core.TermName]core.Term{}
			}
			next[binder.Name()] = v
		}
		part := g.partAt(d.projection, v)
		head, own := rigidHead(part)
		if head.Wild() || head.Abs {
			if h.instancesMayMatch(g, rest, sub, next) {
				return true
			}
			continue
		}
		targetHead, targetArgs := rigidHead(d.target)
		if targetHead.Abs || targetHead.Const != head.Const || targetHead.Args != len(own)+len(d.further) {
			continue
		}
		sk := &_Skeleton{head: h, letters: sub}
		matched := true
		for i, a := range d.further {
			if !sk.mayMatch(a, targetArgs[len(own)+i]) {
				matched = false
				break
			}
		}
		if matched && h.instancesMayMatch(g, append(sk.deferred, rest...), sk.letters, next) {
			return true
		}
	}
	return false
}

// offeredFor lists the values the goal offers a binder at the
// positions antecedent pieces take it whole (takenWhole).
func (h *StatedHead) offeredFor(g *HeadGoal, name core.TermName) []core.Term {
	var values []core.Term
	for _, position := range h.takenWhole[name] {
		for _, v := range g.offeredAt(position) {
			if !slices.Contains(values, v) {
				values = append(values, v)
			}
		}
	}
	return values
}

// Read runs the apply rung's plan over the stated form at a goal, as
// `by` reads a named premise's stated form: a form MayRead declines —
// a sequent among them — is declined before anything else, and the
// head is tried at
// every type instance the goal offers, the identity instance last, and
// then at the instances the facts' structure instances offer for its
// antecedents (FactSource.instances) — the carrier of a law whose
// conclusion spells no constant the goal shares. Where no instance's
// conclusion as stated matches and some reading sits against the goal
// only through a projection node the instance decides (mayRead), the
// form is tried again at each instance with the binders its
// conclusion spells in a projection's record (recordBinders) pinned
// first, from the antecedent pieces that take them whole against the
// goal's hypotheses and the facts (recordSeeds), its conclusion then
// read at them in the instance normal form — the law at a structure
// record whose operations the goal spells by the values the record's
// instance computes them to.
// ok is false when no instance's conclusion matches the goal with
// every binder pinned. A bare fact — no binders, no antecedents — is
// not a head either; that is the exact match's business. Nor is a head
// whose conclusion is one of its own binders (`∀a. a ⇒ a`): it matches
// every goal and pins nothing from it, and the rung only ever fires it
// where assumption already closed.
func (h *StatedHead) Read(g *HeadGoal) (*HeadReading, bool) {
	may, atAnInstance := h.mayRead(g)
	if !may {
		return nil, false
	}
	goal, facts := g.goal, g.facts
	candidates := headCandidates(h.closed, goal)
	if facts != nil {
		offered := map[core.PropKey]bool{}
		for _, cand := range candidates {
			offered[cand.AlphaKey()] = true
		}
		for _, inst := range facts.instances(h.closed) {
			if !offered[inst.AlphaKey()] {
				candidates = append(candidates, inst)
			}
		}
	}
	for _, cand := range candidates {
		if reading, ok := readPlan(goal, cand.Conclusion(), nil, facts); ok {
			return reading, true
		}
	}
	if !atAnInstance {
		return nil, false
	}
	records := h.recordBinders()
	for _, cand := range candidates {
		for _, seeds := range recordSeeds(cand.Conclusion(), records, g) {
			if reading, ok := readPlan(goal, cand.Conclusion(), seeds, facts); ok {
				return reading, true
			}
		}
	}
	return nil, false
}

// readPlan is the plan at one instance of the head, seeded with the
// binders named, read off as the witnesses and the antecedents at them.
func readPlan(goal Prop, head core.Term, seeds []NamedWitness, facts *FactSource) (*HeadReading, bool) {
	plan, _ := planHead(readerOf(nil), goal, head, "", seeds, facts)
	if plan == nil {
		return nil, false
	}
	if v, isVar := plan.concl.AsVar(); isVar && plan.slots.Has(v.Name()) {
		return nil, false
	}
	// Telescope renamed the binders away from the goal's names
	// position by position: the stated name at index j is the slot
	// binders[j].
	statedBinders, _ := ematch.StripGuardedForalls(head)
	reading := &HeadReading{}
	subs := make([]core.TermSubst, len(plan.binders))
	for j, b := range plan.binders {
		reading.Witnesses = append(reading.Witnesses, NamedWitness{Binder: string(statedBinders[j].Name()), Witness: plan.witnesses[j]})
		subs[j] = core.MakeTermSubst(b, plan.witnesses[j])
	}
	ctx := context.Background()
	for _, a := range plan.antes {
		inst := tactic.InstanceNormalTerm(ext.BetaCollapse(ctx, a.Substitute(subs...)))
		reading.Premises = append(reading.Premises, HeadPremise{Term: inst, Resident: structurallyResident(goal, inst, rungOpts{})})
	}
	return reading, true
}

// recordBinders lists the binders the conclusion's readings spell in
// the record of a projection the instance normal form computes, in
// order of occurrence.
func (h *StatedHead) recordBinders() []core.TermName {
	var out []core.TermName
	var walk func(t core.Term)
	walk = func(t core.Term) {
		if abs, ok := t.AsAbsTerm(); ok {
			walk(abs.Body())
			return
		}
		head, args := ext.MatchesApply(t)
		if c, ok := head.AsConst(); ok && len(args) > 0 && tactic.IsRecordProjection(c.Name()) {
			for _, v := range args[0].Frees(nil) {
				if h.isBinder(v.Name()) && !slices.Contains(out, v.Name()) {
					out = append(out, v.Name())
				}
			}
		} else if _, ok := head.AsAbsTerm(); ok {
			walk(head)
		}
		for _, a := range args {
			walk(a)
		}
	}
	for _, c := range h.conclusions {
		walk(c.term)
	}
	return out
}

// recordSeeds pins the record binders of one instance of a head from
// the antecedent pieces that take them whole — a structure fact's
// record, `comm_ring(R)` — before any match: each such piece taking
// one still unpinned, in stated order, matched as spelled against the
// goal's hypotheses at its head (as spelled and in the membership
// normal form) and against the facts there, every consistent extension
// taken — a piece nothing meets passed over — pinningBound pinnings in
// all. A pinning is the values of the record binders the pieces take
// whole, by stated name; the plan reads every other binder as it reads
// an unseeded head.
func recordSeeds(head core.Term, records []core.TermName, g *HeadGoal) [][]NamedWitness {
	binders, antes, _ := telescopeStated(head)
	slots := utils.EmptySet[core.TermName]()
	for _, b := range binders {
		slots.Add(b.Name())
	}
	pinnings := []unify.MatchBindings{{}}
	for _, a := range antes {
		for _, piece := range conjuncts(a) {
			at, whole := pieceHead(piece), takenWholeBy(piece, records)
			if at == "" || len(whole) == 0 {
				continue
			}
			sources := g.byHead[at]
			if g.facts != nil {
				sources = append(slices.Clone(sources), g.facts.ByHead[at]...)
			}
			var next []unify.MatchBindings
			for _, pinning := range pinnings {
				if !slices.ContainsFunc(whole, func(r core.TermName) bool { _, has := pinning[r]; return !has }) {
					next = append(next, pinning)
					continue
				}
				met := false
				for _, source := range sources {
					trial := copyBindings(pinning)
					if !unify.TermMatchApproxEtaWith(piece, source, slots, trial) {
						continue
					}
					met = true
					extended := copyBindings(pinning)
					for _, r := range whole {
						extended[r] = trial[r]
					}
					if !slices.ContainsFunc(next, func(o unify.MatchBindings) bool { return sameBindings(o, extended) }) {
						next = append(next, extended)
					}
				}
				if !met {
					next = append(next, pinning)
				}
			}
			pinnings = next[:min(len(next), pinningBound)]
		}
	}
	var out [][]NamedWitness
	for _, pinning := range pinnings {
		if len(pinning) == 0 {
			continue
		}
		var seeds []NamedWitness
		for _, r := range records {
			if v, has := pinning[r]; has {
				seeds = append(seeds, NamedWitness{Binder: string(r), Witness: v})
			}
		}
		out = append(out, seeds)
	}
	return out
}

// takenWholeBy lists the record binders a piece takes whole, as
// arguments of the constant at its head.
func takenWholeBy(piece core.Term, records []core.TermName) []core.TermName {
	head, args := ext.MatchesApply(piece)
	if _, ok := head.AsConst(); !ok {
		return nil
	}
	var whole []core.TermName
	for _, arg := range args {
		if v, ok := arg.AsVar(); ok && slices.Contains(records, v.Name()) && !slices.Contains(whole, v.Name()) {
			whole = append(whole, v.Name())
		}
	}
	return whole
}

// sameBindings reports whether two bindings bind the same names to
// α-equal terms.
func sameBindings(a, b unify.MatchBindings) bool {
	if len(a) != len(b) {
		return false
	}
	for k, v := range a {
		if w, has := b[k]; !has || !v.AlphaEquals(w) {
			return false
		}
	}
	return true
}

// RigidHead is the top of a term's rigid skeleton, the first thing
// _Skeleton.mayMatch decides: the constant at the head of the
// application spine with its number of arguments, an abstraction, or
// the zero value for a term headed by a variable — a slot, a bound
// variable — which decides nothing. A stated form's are read once off
// the plan's readings of its conclusion (StatedHead.Rigids), a reading
// topped by a projection node the instance decides wild like a
// variable's, and a goal's off its conclusion as it stands
// (RigidHeadOf), so a scan over many stated forms keeps them under an
// index by head (registry.ReadablesFor) and reads, at a goal, the wild
// ones and the ones at the goal's own head alone: Read declines every
// other before anything else.
type RigidHead struct {
	Const core.TermName
	Args  int
	Abs   bool
}

// RigidHeadOf reads a term's rigid head.
func RigidHeadOf(t core.Term) RigidHead {
	head, _ := rigidHead(t)
	return head
}

// Wild reports the head that decides nothing: a variable's.
func (h RigidHead) Wild() bool { return h == RigidHead{} }

// MayMatch is what the skeleton decides at its top: a wild head sits
// against anything, an abstraction against an abstraction alone, and a
// constant against the same constant at as many arguments.
func (h RigidHead) MayMatch(target core.Term) bool {
	return h.Wild() || RigidHeadOf(target) == h
}

// rigidHead reads a term's rigid head, with the spine's arguments
// under a constant.
func rigidHead(t core.Term) (RigidHead, []core.Term) {
	if _, ok := t.AsAbsTerm(); ok {
		return RigidHead{Abs: true}, nil
	}
	head, args := ext.MatchesApply(t)
	if c, ok := head.AsConst(); ok {
		return RigidHead{Const: c.Name(), Args: len(args)}, args
	}
	return RigidHead{}, nil
}

// telescopeStated reads a stated conclusion as Telescope reads it: the
// ∀-binders and the antecedents met through leading ∀s and ⇒s in any
// interleaving, in stated order, and the matrix below them all. It is
// StripGuardedForalls with the antecedents the matrix keeps stripped
// again — a ⇒ it leaves in the matrix is one with no ∀ below, which
// the strip reaches too — read without rebuilding the matrix.
func telescopeStated(stated core.Term) (binders []core.VarTerm, antes []core.Term, matrix core.Term) {
	matrix = stated
	for {
		if abs := ext.MatchesFORALL(matrix); !abs.IsZero() {
			binders = append(binders, abs.Var())
			matrix = abs.Body()
			continue
		}
		if ante, rest, ok := ext.MatchesIMPLY(matrix); ok {
			antes = append(antes, ante)
			matrix = rest
			continue
		}
		return binders, antes, matrix
	}
}

// conclusionMatrix is a stated conclusion's matrix alone.
func conclusionMatrix(stated core.Term) core.Term {
	_, _, matrix := telescopeStated(stated)
	return matrix
}

// skeletonMayMatch is a necessary condition of matchHead's conclusion
// match, read before the stated form is closed and before any type
// instance is enumerated. What is decided is the rigid skeleton of
// unify's match: a stated subterm headed by a constant sits only
// against a goal subterm headed by that constant with as many
// arguments, argument by argument, and an abstraction only against an
// abstraction; a subterm headed by a variable — a slot, the law stated
// for an arbitrary operation or predicate, or a bound variable —
// decides nothing of what is below it. The match equates the types at
// every node it visits, after the stated form's letters are
// instantiated — by the goal or by a fact's carrier — and never the
// goal's: so at every node the stated type must match the goal's with
// the stated letters open and one substitution across the skeleton,
// which declines an equation of sets at an equation of reals before
// any instance of it is built. Read with no stated form's binders, no
// projection node is the instance's.
func skeletonMayMatch(matrix, target core.Term) bool {
	sk := &_Skeleton{}
	return sk.mayMatch(matrix, target)
}

// anyLetter instantiates every type variable of a stated form.
func anyLetter(core.VarType) bool { return true }

// _Skeleton is one reading of the rigid skeleton against a target: the
// stated form whose binders decide which projection nodes are the
// instance's (nil: none is), the type letters instantiated so far — one
// substitution across the skeleton — and the projection nodes deferred
// to the instances (StatedHead.instancesMayMatch).
type _Skeleton struct {
	head     *StatedHead
	letters  []core.TypeSubst
	deferred []_Deferred
}

// _Deferred is a projection node the instance decides, against the
// goal's subterm there: the projection, its record, the arguments
// after the record, and the subterm.
type _Deferred struct {
	projection core.ConstTerm
	record     core.Term
	further    []core.Term
	target     core.Term
}

// mayMatch decides the skeleton top down: the types, the heads
// (RigidHead.MayMatch), then an abstraction's bodies or a constant's
// arguments position by position. A projection node the instance
// decides (StatedHead.decidedByInstance) at a subterm of another head
// is deferred rather than declined.
func (sk *_Skeleton) mayMatch(pattern core.Term, target core.Term) bool {
	if !core.MatchTypeInto(pattern.Type(), target.Type(), anyLetter, &sk.letters) {
		return false
	}
	head, args := rigidHead(pattern)
	if head.Wild() {
		return true
	}
	if head.Abs {
		pAbs, _ := pattern.AsAbsTerm()
		tAbs, ok := target.AsAbsTerm()
		return ok && sk.mayMatch(pAbs.Body(), tAbs.Body())
	}
	targetHead, targetArgs := rigidHead(target)
	if targetHead != head {
		if sk.head == nil || !sk.head.decidedByInstance(head, args) {
			return false
		}
		projection, _ := ext.MatchesApply(pattern)
		c, _ := projection.AsConst()
		sk.deferred = append(sk.deferred, _Deferred{projection: c, record: args[0], further: args[1:], target: target})
		return true
	}
	for i := range args {
		if !sk.mayMatch(args[i], targetArgs[i]) {
			return false
		}
	}
	return true
}
