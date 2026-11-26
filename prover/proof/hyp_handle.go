// hyp_handle.go — named, position-independent references to hypotheses.
//
// Goal hyp lists are Compare-sorted and α-deduped (core.MakeProp), so a
// hypothesis's INDEX is a function of its content relative to the
// ambient context: every hyp-adding step re-sorts the list and
// renumbers everything (see engine-side canonicalization notes). A
// positional index in a proof script is therefore both unreadable (the
// reader must simulate the whole hyp list) and brittle (any upstream
// edit shifts it). CiteSpecialize / GroundHyp already remove indices
// for the install-and-ground-now and address-by-exact-content cases;
// what they cannot address is a hyp whose content has been TRANSFORMED
// since install — the dominant case being an ∃-hyp Skolemized by
// StripQuant, whose post-strip form no longer α-matches the cert that
// installed it.
//
// HypHandle closes that gap: a Go value naming one hypothesis, bound at
// the step that introduces it and usable at any later step, with the
// current index resolved at execution time. The proof reads like Lean /
// Coq named-hypothesis style (`have hB := …; specialize hB n; clear
// hB`) instead of index bookkeeping:
//
//	cauchyX := NewHypHandle("cauchyX")
//	…
//	Chain(
//	    cauchyX.From(CiteSpecialize(ctx.DepNormalized(Cauchy), x0)),
//	    StripQuant(),                  // Skolemizes the ∃-bound; the handle follows
//	    …
//	    cauchyX.Ground(n0),            // instead of Specialize(InstHyp(<index>, n0))
//	    Clear(otherHandle),
//	)
//
// Tracking is LAZY and side-effect-free: binding records (node, hyp
// term) once; resolution walks the goal-tree path from the binding node
// down to the current leaf and follows the hyp through each step. A
// handle names a proposition: a step after which the child still holds
// the content needs no bookkeeping, whatever the step did to the slot
// the content stood in. Where the content is gone, a step records which
// hypothesis of its goal each hypothesis of a child descends from
// (tactic.SubGoals.HypSuccessors) — the rewrites Rw and Subst, Unfold
// with its tidy, Let and Denote, Simp at a hypothesis, Specialize,
// Clear, the quantifier strips and the connective splits of Basic and
// TrivialSimplify all do — and the walk reads that map: a rewritten
// hypothesis is followed to its rewrite however many others the step
// rewrote beside it, and one the step dropped or split into several
// fails resolution loudly with the step named. A step that records no
// provenance — a lemma install (Cite, UseLemma, By's premise installs),
// an induction or recursion principle, Witness, Instantiate, the AC
// regroup — is followed by its before/after hyp diff: a step that
// transforms exactly that one hyp maps it to its unique successor; a
// step that transforms SEVERAL hyps at once fails resolution loudly with
// the step named. There is deliberately no guessing (a mis-tracked
// handle would silently target the wrong hyp).
//
// A handle bound before a split resolves independently (and correctly)
// in every branch: the one state a branch adds is a Simp at the
// hypothesis, which records the rewritten content at the residual leaf
// it left (rebound), and resolution starts from the deepest binding
// above the current leaf — so a rewrite in one branch is invisible to
// its siblings, which still read the bind. Handles are single-bind:
// create them inside the proof's body (locals), never at package level
// — a second From on the same handle panics, which also catches a
// package-level handle surviving into a second Build run.
//
// Failure modes are all loud panics: unbound use, double bind, use in a
// branch the binding node is not an ancestor of, use after the hyp was
// consumed, ambiguous transformation. Resolution errors name the handle
// and the offending step.

package proof

import (
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// HypHandle names one hypothesis of an in-progress proof. Zero value is
// unusable; construct with NewHypHandle. Bound (once) by wrapping the
// hyp-introducing action in From; consumed by the use-side methods
// (Ground / Rw / Subst / CongrArg / SplitDisj) and the package-level
// Clear.
type HypHandle struct {
	name     string
	bindNode *GoalStackNode // leaf whose Goal first carried the hyp
	term     core.Term      // the hyp's content at bind time
	// rebound is the hypothesis as a Simp at it respelled it, one
	// binding per rewrite, at the residual leaf the rewrite left.
	rebound []_HypBinding
}

// _HypBinding is the handle's content at one node of the tree: the
// bind, or a rewrite of the hypothesis below it.
type _HypBinding struct {
	node *GoalStackNode
	term core.Term
}

// bindingAt is the handle's binding made at node — the rewrite whose
// residual leaf node is, else the bind — or nil.
func (h *HypHandle) bindingAt(node *GoalStackNode) *_HypBinding {
	for i := len(h.rebound) - 1; i >= 0; i-- {
		if h.rebound[i].node == node {
			return &h.rebound[i]
		}
	}
	if node == h.bindNode {
		return &_HypBinding{node: h.bindNode, term: h.term}
	}
	return nil
}

// boundTerm is the hypothesis as the binding in force at leaf spelled
// it: the deepest binding at leaf or above it, the bind-time content
// where none is above it.
func (h *HypHandle) boundTerm(leaf *GoalStackNode) core.Term {
	for n := leaf; n != nil; n = n.parent {
		if b := h.bindingAt(n); b != nil {
			return b.term
		}
	}
	return h.term
}

// content is the hypothesis as the handle's latest binding spelled it
// — the last rewrite at it, in whichever branch, else the bind: the
// reading of a surface with no leaf at hand (Fact.BoundContent, By's
// evidence listing). A verb at a leaf resolves there instead.
func (h *HypHandle) content() core.Term {
	if n := len(h.rebound); n > 0 {
		return h.rebound[n-1].term
	}
	return h.term
}

// contentAt is the hypothesis as leaf states it — the handle resolved
// there — or the handle's own content where it does not resolve at
// leaf, or leaf is nil.
func (h *HypHandle) contentAt(leaf *GoalStackNode) core.Term {
	if leaf != nil {
		if idx, err := h.resolve(leaf); err == nil {
			return leaf.Goal.Hyp(idx)
		}
	}
	return h.content()
}

// NewHypHandle creates an unbound handle. The name is display-only —
// it appears in panic messages and reads as the hypothesis's
// mathematical role at the call sites (`cauchyX`, `slackEq`), so pick a
// name that says what the fact IS, not where it sits.
func NewHypHandle(name string) *HypHandle { return &HypHandle{name: name} }

// Name returns the display name the handle was created with.
func (h *HypHandle) Name() string { return h.name }

// From binds the handle to the single hypothesis that `act` introduces:
// run act on the current leaf, require it to leave exactly one unsolved
// leaf with exactly one net-new hyp (before/after diff, the
// CiteSpecialize locate-by-content discipline), and record that hyp as
// the handle's referent.
//
// Typical wrapped actions: CiteSpecialize / CiteSpecializeKeep's
// non-Keep half, UseLemma / UseLemmaExact (resident install), StripImp
// (an antecedent becoming a hyp). Actions that add two hyps at once
// (CiteSpecializeKeep adds source AND instance) are rejected — bind the
// resident source via UseLemmaExact + From and take instances with
// GroundKeep instead.
func (h *HypHandle) From(act Action) Action { return _HypBindAction{h: h, act: act} }

type _HypBindAction struct {
	h   *HypHandle
	act Action
}

func (a _HypBindAction) applyAction(s *Script, root *GoalStackNode) {
	if a.h.bindNode != nil {
		panic(fmt.Sprintf("HypHandle %q: already bound — one handle names one hypothesis; "+
			"create a fresh NewHypHandle for a second binding (and never declare handles at package level)",
			a.h.name))
	}
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic(fmt.Sprintf("HypHandle %q.From: no unsolved leaves remaining "+
			"(section already proved — extra step in chain?)", a.h.name) + closedLeafNote(root))
	}
	before := anchor.Goal
	a.act.applyAction(s, anchor)
	leaves := anchor.UnsolvedLeaves()
	if len(leaves) != 1 {
		panic(fmt.Sprintf("HypHandle %q.From: the wrapped action left %d unsolved leaves — "+
			"exactly 1 is required to bind the new hypothesis unambiguously", a.h.name, len(leaves)))
	}
	leaf := leaves[0]
	idx, err := newHypIndex(before, leaf.Goal)
	if err != nil {
		panic(fmt.Sprintf("HypHandle %q.From: cannot identify the hypothesis the action introduced: %v\n"+
			"(goal after action: %s)", a.h.name, err, prop.PrintProp(leaf.Goal)))
	}
	a.h.bindTo(leaf, leaf.Goal.Hyp(idx))
}

// bindTo records the binding, guarding the single-bind contract. All
// binding surfaces (From, FromResident, the named-Have unwrap in
// Deduce, CiteSpecializeKeepAs) funnel through here.
func (h *HypHandle) bindTo(leaf *GoalStackNode, t core.Term) {
	if h.bindNode != nil {
		panic(fmt.Sprintf("HypHandle %q: already bound — one handle names one hypothesis; "+
			"create a fresh NewHypHandle for a second binding (and never declare handles at package level)",
			h.name))
	}
	h.bindNode = leaf
	h.term = t
}

// FromResident binds the handle to an ALREADY-RESIDENT hyp, located by
// content (α-equality) — the binding surface for hyps that no single
// wrappable action introduces: a ByCaseStep / Split* branch hypothesis
// (content = the discriminant term, or its negation in the false
// branch), an AssertStep claim hyp in the legacy non-Deduce form
// (content = the claim Prop), or a lemma install whose action nets
// several hyps at once (content = the installed cert). content may be
// a Prop (its conclusion is matched) or a Term. No match / ambiguous
// match panics.
func (h *HypHandle) FromResident(content any) Action {
	return _HypFromResidentAction{h: h, content: content}
}

type _HypFromResidentAction struct {
	h       *HypHandle
	content any
}

func (a _HypFromResidentAction) applyAction(s *Script, root *GoalStackNode) {
	leaf := a.h.mustLeaf("FromResident", root)
	t := contentHypTerm("FromResident", a.content)
	idx, err := findHypIndex(leaf.Goal, t)
	if err != nil {
		panic(fmt.Sprintf("HypHandle %q.FromResident: %v\n(goal: %s)",
			a.h.name, err, prop.PrintProp(leaf.Goal)))
	}
	a.h.bindTo(leaf, leaf.Goal.Hyp(idx))
}

// CiteSpecializeKeepAs is CiteSpecializeKeep with both of its net-new
// hyps bound to handles: `source` names the cited ∀-source that stays
// resident, `instance` the grounded instance. Either handle may be nil
// to skip that binding. This is the binding surface for the
// keep-variant install, which nets TWO hyps and therefore cannot be
// wrapped in From.
func CiteSpecializeKeepAs(source, instance *HypHandle, target CiteTarget, witnesses ...TermLike) Action {
	return _CiteSpecializeKeepAsAction{src: source, inst: instance, target: targetFact("CiteSpecializeKeepAs", target), witnesses: ext.CoreTerms(witnesses)}
}

type _CiteSpecializeKeepAsAction struct {
	src, inst *HypHandle
	target    Fact
	witnesses []Term
}

func (a _CiteSpecializeKeepAsAction) applyAction(s *Script, root *GoalStackNode) {
	anchor := root.unsolvedLeaf(0)
	if anchor == nil {
		panic("CiteSpecializeKeepAs: no unsolved leaves remaining" + closedLeafNote(root))
	}
	before := anchor.Goal
	L := resolveLemmaTarget("CiteSpecializeKeepAs", s, a.target)
	anchor.citeSpecialize(L, true, a.witnesses...)
	leaves := anchor.UnsolvedLeaves()
	if len(leaves) != 1 {
		panic(fmt.Sprintf("CiteSpecializeKeepAs: the install left %d unsolved leaves (need exactly 1 to bind)", len(leaves)))
	}
	leaf := leaves[0]
	// Diff: the keep-install nets the ∀-source and the instance. The
	// source is the hyp α-equal to the cited statement; the other new
	// hyp is the instance.
	var added []core.Term
	for i := 0; i < leaf.Goal.NumHyps(); i++ {
		if hy := leaf.Goal.Hyp(i); !goalHasHypAlpha(before, hy) {
			added = append(added, hy)
		}
	}
	stmt := L.AsProp().Conclusion()
	var srcT, instT core.Term
	for _, hy := range added {
		if hy.AlphaEquals(stmt) {
			srcT = hy
		} else if instT == nil {
			instT = hy
		} else {
			instT = nil // more than one non-source candidate — ambiguous
			break
		}
	}
	if a.src != nil {
		if srcT == nil {
			panic(fmt.Sprintf("CiteSpecializeKeepAs: no net-new hyp α-matches the cited statement "+
				"(%d added; the install may have been rewritten on injection) — bind by FromResident instead\n(goal: %s)",
				len(added), prop.PrintProp(leaf.Goal)))
		}
		a.src.bindTo(leaf, srcT)
	}
	if a.inst != nil {
		if instT == nil {
			panic(fmt.Sprintf("CiteSpecializeKeepAs: cannot single out the grounded instance among %d net-new hyp(s)\n(goal: %s)",
				len(added), prop.PrintProp(leaf.Goal)))
		}
		a.inst.bindTo(leaf, instT)
	}
}

// Ground grounds the handle's ∀-hyp at one witness tuple — the
// composite Specialize with the index resolved from the handle. The
// ∀-source is consumed (Lean `specialize h w…` semantics); GroundKeep
// keeps it resident.
func (h *HypHandle) Ground(witnesses ...Term) Action {
	return _HypGroundAction{h: h, witnesses: witnesses}
}

// GroundKeep is Ground with the ∀-source kept resident after grounding
// (SpecializeKeep semantics) — for a wide ∀-hyp serving several witness
// tuples.
func (h *HypHandle) GroundKeep(witnesses ...Term) Action {
	return _HypGroundAction{h: h, witnesses: witnesses, keep: true}
}

type _HypGroundAction struct {
	h         *HypHandle
	witnesses []Term
	keep      bool
}

func (a _HypGroundAction) applyAction(s *Script, root *GoalStackNode) {
	leaf, idx := a.h.mustResolve("Ground", root)
	spec := Specialize(InstHyp(idx, a.witnesses...))
	if a.keep {
		spec = SpecializeKeep(InstHyp(idx, a.witnesses...))
	}
	s.Do(leaf, spec)
}

// Note on Ground + consumption: consuming Specialize REPLACES the
// ∀-source with the ground instance, and the handle's lazy tracking
// follows that replacement — after h.Ground(w), h refers to the
// INSTANCE (so a later Clear(h) or h.Rw() targets it). After
// h.GroundKeep(w) the source and the instance are both resident; the
// diff at that step adds one hyp without removing the tracked one, so h
// keeps referring to the ∀-SOURCE.

// Clear lives on the Fact surface (fact.go) — it takes Fact values and
// anything that reads as one, so a *HypHandle still passes directly.

// Rw rewrites with the handle's equality hyp to fixpoint across the
// conclusion and all other hyps, in the hyp's written direction (l → r)
// — the handle form of Rw(idx, false). RwRev is the same step read
// right to left; the pair spells the orientation the way Fwd / Rev
// spell it for a simp rule, so no call site carries a bare bool.
func (h *HypHandle) Rw() Action { return h.rw(false) }

// RwRev rewrites with the handle's equality hyp REVERSED (r → l)
// — the handle form of Rw(idx, true).
func (h *HypHandle) RwRev() Action { return h.rw(true) }

// rw is the shared bottom of the pair — the one ministep both spell.
func (h *HypHandle) rw(flip bool) Action {
	op := "Rw"
	if flip {
		op = "RwRev"
	}
	return _HypStepAction{h: h, op: op, flip: flip}
}

// Subst substitutes using the handle's equality hyp (must be an
// equality between a free variable and a term) — the handle form of
// Subst(idx).
func (h *HypHandle) Subst() Action { return _HypStepAction{h: h, op: "Subst"} }

// Simp rewrites THIS hypothesis with the rules, in its place — Lean's
// `simp at h`: the rules' side conditions discharge against the other
// hypotheses, the conclusion is untouched, and the handle goes on naming
// the rewritten hypothesis. No rule firing is a panic, as for Simp.
func (h *HypHandle) Simp(rules ...SimpRule) Action {
	return _HypStepAction{h: h, op: "Simp", rules: flattenSimpRules(rules)}
}

// CongrArg applies forward congruence on the handle's equality hyp
// under the function fn — the handle form of CongrArg(fn, idx).
func (h *HypHandle) CongrArg(fn Term) Action {
	return _HypStepAction{h: h, op: "CongrArg", fn: fn}
}

// SplitDisj splits the handle's disjunction hyp into its two branches,
// each claimed by the disjunct it assumes — the handle form of
// SplitDisjAt(idx, left, right).
func (h *HypHandle) SplitDisj(left DisjLeftHolds, right DisjRightHolds) Action {
	return _HypStepAction{h: h, op: "SplitDisj", cases: []Case{left.c, right.c}}
}

// SplitIff splits the handle's ⇔-shaped hyp into the branch where both
// sides hold and the branch where neither does — the handle form of
// SplitHypIffAt(idx, both, neither). Content-addressed: the index is
// resolved at run time from the handle's binding, so no integer hyp
// address (a value the reader must simulate the hyp list to check)
// appears in the proof text. Tree-identical to the At form at the
// resolved index — converting a call site never re-records a pb.
func (h *HypHandle) SplitIff(both IffBothHold, neither IffNeitherHolds) Action {
	return _HypStepAction{h: h, op: "SplitIff", cases: []Case{both.c, neither.c}}
}

// SplitImply splits the handle's ⇒-shaped hyp — the handle form of
// SplitHypImplyAt(idx, cases…). See SplitIff for the content-addressing
// contract.
func (h *HypHandle) SplitImply(cases ...Case) Action {
	return _HypStepAction{h: h, op: "SplitImply", cases: cases}
}

// DismissLeft / DismissRight are the linearizing spellings of a BINARY
// disjunctive-hyp split (the Assuming / Unless analog at the hyp
// level, action.go §"Linearizing side-case combinators"): split the
// handle's disjunction, discharge the named disjunct's branch inline
// with the labeled proof, and leave the surviving branch — with the
// other disjunct resident — as THE unsolved leaf the enclosing chain
// continues on. Same ministep, same subgoals, same tree as the
// Case-nested SplitDisj spelling; the side proof must close its
// branch or the combinator panics with the label. Binary splits only:
// a disjunction that fans out to n ≠ 2 branches panics.
func (h *HypHandle) DismissLeft(label string, body ...Action) Action {
	return _DismissDisjAction{h: h, sideIdx: 0, label: label, body: body}
}

// DismissRight discharges the right disjunct's branch; the proof
// continues with the left disjunct resident. See DismissLeft.
func (h *HypHandle) DismissRight(label string, body ...Action) Action {
	return _DismissDisjAction{h: h, sideIdx: 1, label: label, body: body}
}

type _DismissDisjAction struct {
	h       *HypHandle
	sideIdx int
	label   string
	body    []Action
}

func (a _DismissDisjAction) applyAction(s *Script, root *GoalStackNode) {
	op := "DismissLeft"
	if a.sideIdx == 1 {
		op = "DismissRight"
	}
	leaf, idx := a.h.mustResolve(op, root)
	s.Do(leaf, SplitDisjAtCases(idx))
	if len(leaf.children) != 2 {
		panic(fmt.Sprintf("HypHandle %q.%s: the disjunction split into %d branches — "+
			"the dismiss combinators are binary-only",
			a.h.name, op, len(leaf.children)))
	}
	side := leaf.children[a.sideIdx]
	for _, act := range a.body {
		act.applyAction(s, side)
	}
	if leaves := side.UnsolvedLeaves(); len(leaves) != 0 {
		msg := fmt.Sprintf("HypHandle %q.%s: side case %q did not close (%d unsolved leaf(ves))",
			a.h.name, op, a.label, len(leaves))
		for _, l := range leaves {
			msg += "\n  leaf: " + prop.PrintProp(l.Goal)
		}
		panic(msg)
	}
}

type _HypStepAction struct {
	h     *HypHandle
	op    string
	flip  bool
	fn    Term
	cases []Case
	rules []SimpRule
}

func (a _HypStepAction) applyAction(s *Script, root *GoalStackNode) {
	leaf, idx := a.h.mustResolve(a.op, root)
	if a.op == "Simp" {
		// The hypothesis is rewritten in its place; the handle follows
		// it onto the residual leaf by its new content — the residual's
		// hypotheses are in the kernel's order, and the rewritten one
		// may have merged with an α-equal resident.
		residual, rewritten := simpAtHyp("Simp", s, leaf, idx, a.rules)
		a.h.rebound = append(a.h.rebound, _HypBinding{node: residual, term: rewritten})
		return
	}
	var step Step
	switch a.op {
	case "Rw", "RwRev":
		step = Rw(idx, a.flip)
	case "Subst":
		step = Subst(idx)
	case "CongrArg":
		step = CongrArg(a.fn, idx)
	case "SplitDisj":
		step = SplitDisjAtCases(idx, a.cases...)
	case "SplitIff":
		step = SplitHypIffAtCases(idx, a.cases...)
	case "SplitImply":
		step = SplitHypImplyAt(idx, a.cases...)
	default:
		panic("HypHandle: unknown op " + a.op)
	}
	if _, carries := step.(caseCarrier); carries {
		s.Do(leaf, step)
		return
	}
	// A step on the hypothesis alone: refused, it names the hypothesis
	// as it stands, what an earlier step made of the fact the handle was
	// bound to, and for a rewrite the side that occurs nowhere and the
	// step whose tidy substituted it (context_history.go).
	if !leaf.runStep(step) {
		panic(fmt.Sprintf("HypHandle %q.%s: the step did not apply to its hypothesis\n  hyp: %s%s\n  on leaf goal: %s",
			a.h.name, a.op, ext.PrintTerm(leaf.Goal.Hyp(idx)), a.refusalNote(leaf, idx), prop.PrintProp(leaf.Goal)))
	}
}

// refusalNote is why a hypothesis step found nothing to do: the handle
// bound to a fact an earlier step rewrote; a rewrite whose rewritten
// side occurs nowhere else in the goal, with the step past which it
// stopped occurring; a rewrite or substitution on no equation.
func (a _HypStepAction) refusalNote(leaf *GoalStackNode, idx int) string {
	hyp := leaf.Goal.Hyp(idx)
	note := ""
	if bound := a.h.boundTerm(leaf); !hyp.AlphaEquals(bound) {
		note += fmt.Sprintf("\n  the handle was bound to %s%s", ext.PrintTerm(bound), rewrittenAwayNote(leaf, bound))
	}
	if a.op != "Rw" && a.op != "RwRev" && a.op != "Subst" {
		return note
	}
	l, r, ok := ext.MatchesEQ(hyp)
	if !ok {
		return note + "\n  the hypothesis is no equation"
	}
	if l.AlphaEquals(r) {
		return note + "\n  both sides of the equation are the same term, so there is nothing to rewrite"
	}
	side, name := l, "left"
	other := r
	if a.flip {
		side, name = r, "right"
		other = l
	}
	// The oriented left side occurring in the oriented right side is a
	// rewrite with no fixpoint, which the step refuses before looking
	// for an occurrence (prover/tactic, RwHypTactic).
	if occursIn(other, side) {
		return note + fmt.Sprintf("\n  the rewrite %s → %s is self-expanding (its %s side occurs in the other), so the step refuses it: rewrite the other way, or take the equation as a By premise",
			ext.PrintTerm(side), ext.PrintTerm(other), name)
	}
	isHyp := hyp.AlphaEquals
	elsewhere := occursIn(leaf.Goal.Conclusion(), side)
	for i := range leaf.Goal.NumHyps() {
		if h := leaf.Goal.Hyp(i); i != idx && !isHyp(h) && occursIn(h, side) {
			elsewhere = true
		}
	}
	if !elsewhere {
		note += fmt.Sprintf("\n  its %s side %s occurs nowhere else in the goal, so there is nothing to rewrite%s",
			name, ext.PrintTerm(side), lastOccurrenceNote(leaf, side, isHyp))
	}
	return note
}

// ---------------------------------------------------------------------------
// Resolution
// ---------------------------------------------------------------------------

func (h *HypHandle) mustLeaf(op string, root *GoalStackNode) *GoalStackNode {
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("HypHandle %q.%s: no unsolved leaves remaining "+
			"(section already proved — extra step in chain?)", h.name, op) + closedLeafNote(root))
	}
	return leaf
}

func (h *HypHandle) mustResolve(op string, root *GoalStackNode) (*GoalStackNode, int) {
	leaf := h.mustLeaf(op, root)
	return leaf, h.resolveOrPanic(op, leaf)
}

func (h *HypHandle) resolveOrPanic(op string, leaf *GoalStackNode) int {
	idx, err := h.resolve(leaf)
	if err != nil {
		panic(fmt.Sprintf("HypHandle %q.%s: %v\n(current goal: %s)",
			h.name, op, err, prop.PrintProp(leaf.Goal)))
	}
	return idx
}

// resolve returns the handle's hyp index in leaf.Goal: walk the tree
// path from the deepest binding above leaf — the bind, or a Simp's
// rewrite in this branch — down to leaf, carrying the hyp through each
// step — kept while the child holds its content, else by the
// provenance the step recorded, else by its before/after hyp diff —
// then α-locate the final content in the leaf's (canonically sorted)
// hyp list.
func (h *HypHandle) resolve(leaf *GoalStackNode) (int, error) {
	if h.bindNode == nil {
		return 0, fmt.Errorf("not bound — wrap the introducing action in %s.From(...)", h.name)
	}
	// Ancestor chain leaf → … → the binding in force.
	var chain []*GoalStackNode
	var start *_HypBinding
	for n := leaf; n != nil && start == nil; n = n.parent {
		chain = append(chain, n)
		start = h.bindingAt(n)
	}
	if start == nil {
		return 0, fmt.Errorf("bound at a node that is not an ancestor of the current leaf " +
			"(handle used outside the branch it was bound in)")
	}
	// Walk downward from the binding, following the hyp through each
	// step: kept while the child holds it, else by the step's provenance
	// where it recorded one, else by its hyp diff. Invariant: t is a hyp
	// of chain[i+1] entering iteration i.
	t := start.term
	for i := len(chain) - 2; i >= 0; i-- {
		parent, child := chain[i+1], chain[i]
		if goalHasHypAlpha(child.Goal, t) {
			// The handle names a proposition: while the child holds it,
			// the handle holds it too, whatever the step did to the slot
			// it stood in (a tidy that rewrote the slot by a resident ⇔
			// and the ⇔ back into the proposition leaves the proposition
			// resident and the slot's successor another one).
			continue
		}
		if successors := parent.hypSuccessors(child); successors != nil {
			at, err := alphaHypIndex(parent.Goal, t)
			if err != nil {
				panic(fmt.Sprintf("HypHandle %q: the tracked hypothesis is not a hypothesis of the goal it was followed into: %v", h.name, err))
			}
			if successors[at] == tactic.NoSuccessor {
				return 0, fmt.Errorf("its hypothesis was consumed by step %q and has no single successor past it — %s, "+
					"so the handle cannot be used past that step; %s",
					parent.StepDescription(), consumedNote(t, child.Goal), handleRepair(parent))
			}
			t = child.Goal.Hyp(successors[at])
			continue
		}
		succ, err := trackHypThrough(parent, child)
		if err != nil {
			return 0, err
		}
		t = succ
	}
	return findHypIndex(leaf.Goal, t)
}

// consumedNote says what a step made of a hypothesis it left no single
// successor for: a conjunction whose conjuncts the child holds one by
// one was split into them — the tidy after an Unfold does this — and
// anything else was dropped or split past recognition.
func consumedNote(hyp core.Term, child core.Prop) string {
	parts := ext.DecomposesAND(hyp)
	if len(parts) < 2 || slices.ContainsFunc(parts, func(p core.Term) bool { return !goalHasHypAlpha(child, p) }) {
		return "the step dropped it or split it into several"
	}
	spelled := make([]string, len(parts))
	for i, p := range parts {
		spelled[i] = ext.PrintTerm(p)
	}
	return fmt.Sprintf("the step split it into its conjuncts, %s, each resident on its own "+
		"(cite them as ResidentHyp, or take them before the step with a.Conjuncts)", strings.Join(spelled, " and "))
}

// handleRepair is the way around a handle lost at parent's step: an
// Unfold has two narrower spellings; any other step is used after the
// handle, or the fact is re-introduced after it.
func handleRepair(parent *GoalStackNode) string {
	if unfold, ok := parent.miniStep.(_DefExpandStep); ok {
		// An Unfold rewrites every resident hypothesis the constant
		// occurs in and tidies the rest; the author who wanted the goal
		// alone has two narrower spellings.
		c := unfold.constTerm.Name()
		return fmt.Sprintf("an Unfold rewrites every resident hypothesis and tidies the rest; to open the goal alone, "+
			"rewrite it by the definition entry, Simp(Fwd(<%s's definition>)), to open one fact, "+
			"a.Unfolded(h, <%s's definition>), or use the handle before the Unfold", c, c)
	}
	return "use the handle before that step, or re-introduce the fact after it"
}

// trackHypThrough finds the unique hypothesis replacement across
// parent's step by hyp-set diff — the tracking for a step that recorded
// no provenance. The caller invokes it only after the currently tracked
// hypothesis has disappeared from child.Goal, so in the unambiguous
// 1-removed/1-added case the removed hypothesis is the tracked one and
// the added hypothesis is its successor. Anything else fails loudly —
// no guessing.
func trackHypThrough(parent, child *GoalStackNode) (core.Term, error) {
	var removed, added []core.Term
	for i := 0; i < parent.Goal.NumHyps(); i++ {
		if ph := parent.Goal.Hyp(i); !goalHasHypAlpha(child.Goal, ph) {
			removed = append(removed, ph)
		}
	}
	for i := 0; i < child.Goal.NumHyps(); i++ {
		if ch := child.Goal.Hyp(i); !goalHasHypAlpha(parent.Goal, ch) {
			added = append(added, ch)
		}
	}
	step := parent.StepDescription()
	if len(added) == 0 {
		return nil, fmt.Errorf("its hypothesis was consumed by step %q with no successor — "+
			"the handle cannot be used past that step", step)
	}
	if len(removed) == 1 && len(added) == 1 {
		return added[0], nil
	}
	return nil, fmt.Errorf("step %q transformed several hypotheses at once "+
		"(%d removed, %d added) and the tracked hyp's successor is ambiguous — %s", step, len(removed), len(added), handleRepair(parent))
}

func goalHasHypAlpha(g Prop, t core.Term) bool {
	return g.HasHyp(t) || g.AnyHyp(t.AlphaEquals)
}

// WithSource brackets an install-and-clear pattern for a wide ∀-hyp
// serving several witness tuples: install `src` via `install`, run
// `body`, then Clear(src) on the way out. Pure sugar — the desugar is
// Chain(src.From(install), body..., Clear(src)), tree-identical to the
// hand-written three-piece expansion (same ministep sequence, same
// recorded pb).
//
// The value beyond line count is scope: the source's lifetime is
// visually bracketed by one call, and the closing Clear cannot be
// forgotten. Every existing loud-panic contract carries over unchanged
// — install failing to bind src panics at From, an ambiguous or spent
// handle panics at Clear, an empty body inside a Chain panics through
// the same paths as a bare Chain.
//
// Typical shape:
//
//	WithSource(cauchySrc, UseLemmaExact(Cauchy),
//	    cauchyAtX.From(cauchySrc.GroundKeep(x_0)),
//	    cauchyN0N1.From(cauchyAtX.GroundKeep(n_0, n_1)),
//	)
//
// vs the three-line hand-written form it replaces:
//
//	cauchySrc.From(UseLemmaExact(Cauchy)),
//	cauchyAtX.From(cauchySrc.GroundKeep(x_0)),
//	cauchyN0N1.From(cauchyAtX.GroundKeep(n_0, n_1)),
//	Clear(cauchySrc),
func WithSource(src *HypHandle, install Action, body ...Action) Action {
	steps := make([]Action, 0, len(body)+2)
	steps = append(steps, src.From(install))
	steps = append(steps, body...)
	steps = append(steps, Clear(src))
	return Chain(steps...)
}
