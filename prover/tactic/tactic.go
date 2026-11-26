/**
 * File: tactic.go
 *
 * Implements the tactic system for goal-directed theorem proving.
 *
 * Types and structures:
 * - _TacticReconstruct: Function type that reconstructs proof from subproofs
 *
 * - SubGoals: Structure representing goal decomposition
 *   Fields:
 *   - goal: Original goal proposition
 *   - reconstruct: Function to combine subgoal proofs into original goal proof
 *   - childrenGoals: Array of simpler propositions to be proved
 *   Methods:
 *   - Reconstruct(thms ...Prop): Combines proofs of subgoals
 *   - ChildGoal(i int): Returns the i-th subgoal
 *   - Size(): Returns number of subgoals
 *
 * - Tactic: Function type that transforms a goal into subgoals
 *   Methods:
 *   - expand(s *SubGoals): Applies tactic to all subgoals of s
 *
 * Functions:
 * - makeSubGoals(goal Prop, c _TacticReconstruct, childrenGoals ...Prop): Creates SubGoals
 *   Deduplicates and optimizes subgoals by strength
 *
 * - MakeEmptySubGoals(goal Prop, thm Thm): Creates SubGoals with no children
 *   Used when a goal is directly proven
 *
 * - mergeTactics(tactics ...Tactic): Creates tactic that tries each input tactic
 *   Recursively applies itself to resulting subgoals
 *
 * - chainTactics(tactics ...Tactic): Applies tactics sequentially once
 *
 * Exported tactics:
 * - TrivialSimplifyTactic: Basic simplification producing at most one subgoal
 * - BasicTactics: More comprehensive transformations, may produce multiple subgoals
 * - ByCaseTactic: Case analysis tactic
 * - DenoteTactic: Introduces new variables for frequently occurring subterms such that
 *   the rewritten proposition is simpler than the original one
 * - HilbertDenoteTactic: Denotes ε terms by introducing new variables
 * - LemmaTactic: Applies known lemmas
 */

// Package tactic is subgoal computation: a Tactic takes a goal to the
// SubGoals that suffice for it, together with the function that
// rebuilds the goal's theorem from theirs.
//
// It sits below the proof calculus (prover/proof), beside the solvers.
// The tactics here cover simplification and case analysis, denoting,
// equations and quantifiers, induction and recursion, the expansion of
// a definition, lemma application, the arithmetic entry, set_tac and
// simp_with.
package tactic

import (
	"context"
	"fmt"
	"os"
	"runtime"
	"slices"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/utils"
)

// _TacticReconstruct rebuilds a goal's theorem from its children's. For
// each child it is handed any theorem IsStronger than that child's goal:
// one that rests on fewer hypotheses, or one that concludes ⊥ where the
// child states a conclusion, as a child closed by contradiction does. It
// returns a theorem IsStronger than the goal. SubGoals.Reconstruct
// asserts both ends, and the gate at a step's creation runs the
// function ahead of any proof (makeSubGoalsAt).
type _TacticReconstruct func(...Prop) Prop

var trivialReconstruct = func(thms ...Prop) Prop { return thms[0] }

type SubGoals struct {
	goal          Prop
	reconstruct   _TacticReconstruct
	childrenGoals []Prop
	creationSite  string // LEAK-PROBE: file:line of MakeSubGoals caller
	// hypSuccessors is the step's hypothesis provenance, one entry per
	// child: hypSuccessors[k][i] is the index in child k of the hypothesis
	// that hypothesis i of goal became there, or NoSuccessor where the
	// child holds no single hypothesis for it (dropped, or split into
	// several). Two hypotheses the step rewrites to one term share one
	// successor, the kernel having merged them. A nil entry is a child
	// the tactic recorded no provenance for; nil altogether, no child.
	hypSuccessors [][]int
	// onOwnGoals is what reconstruct returned on childrenGoals themselves
	// when the step was made, kept for the step that folds this one
	// (reconstructOn); nil for a step a probe built.
	onOwnGoals Prop
	// held is what the stronger-close gate ran on the step, one entry per
	// reading, kept for the same reader (holdStrongerCloses); nil where
	// the gate did not run.
	held []heldCloses
}

// heldCloses is one reading of the stronger-close gate on a step:
// stronger[k] is the theorem child k was replaced by, nil for a child
// the gate leaves; returned[k] is what the reconstruction returned with
// that one child replaced; all is what it returned with every such child
// replaced, nil where fewer than two are.
type heldCloses struct {
	stronger []Prop
	returned []Prop
	all      Prop
}

// reconstructOn is reconstruct on thms. A reconstruction is a function
// of the statements it is handed, so where the step ran it on these
// very theorems when it was made, the result it kept is returned and
// nothing is run (keptOn). A fold reads its pieces through this
// (expandUnder): handed the leaves of a subtree, all their own goals or
// one of them replaced by the gate, it runs its own step and reads the
// pieces below, where the reconstruction alone would run every piece of
// the subtree again.
func (s *SubGoals) reconstructOn(thms []Prop) Prop {
	if kept := s.keptOn(thms); kept != nil {
		return kept
	}
	return s.reconstruct(thms...)
}

// keptOn is the result the step kept for thms, nil where it kept none.
// It kept three: on its children's own goals; on those goals with one
// child replaced by the theorem the gate replaced it by; and on them
// with every child the gate replaces replaced so. thms are read object
// by object, never by statement: a theorem that only states what a kept
// one states is run.
func (s *SubGoals) keptOn(thms []Prop) Prop {
	if s.onOwnGoals == nil || len(thms) != len(s.childrenGoals) {
		return nil
	}
	replaced, last := 0, -1
	for i := range thms {
		if thms[i].Core() != s.childrenGoals[i].Core() {
			replaced++
			last = i
		}
	}
	if replaced == 0 {
		return s.onOwnGoals
	}
	for _, h := range s.held {
		if replaced == 1 {
			if h.stronger[last] != nil && h.stronger[last].Core() == thms[last].Core() {
				return h.returned[last]
			}
			continue
		}
		if h.all != nil && h.replacesAll(s.childrenGoals, thms) {
			return h.all
		}
	}
	return nil
}

// replacesAll reports whether thms are goals with every child the
// reading replaces replaced by its theorem, and the others as they are.
func (h heldCloses) replacesAll(goals, thms []Prop) bool {
	for i := range thms {
		expected := h.stronger[i]
		if expected == nil {
			expected = goals[i]
		}
		if thms[i].Core() != expected.Core() {
			return false
		}
	}
	return true
}

// NoSuccessor marks, in a hypothesis provenance map, a hypothesis the
// child goal holds no single successor of.
const NoSuccessor = -1

func MakeSubGoals(goal Prop, c _TacticReconstruct, childrenGoals ...Prop) *SubGoals {
	_, file, line, _ := runtime.Caller(1)
	site := fmt.Sprintf("%s:%d", file, line)
	return makeSubGoalsAt(fullSearch, goal, c, site, nil, nil, childrenGoals...)
}

// MakeTrackedSubGoals is MakeSubGoals with the step's hypothesis
// provenance: successors[k] maps each hypothesis of goal, by index, to
// its index in childrenGoals[k] or to NoSuccessor (HypSuccessors), and
// is nil for a child the tactic says nothing about. The map follows its
// child through the deduplication every construction performs.
func MakeTrackedSubGoals(goal Prop, c _TacticReconstruct, successors [][]int, childrenGoals ...Prop) *SubGoals {
	_, file, line, _ := runtime.Caller(1)
	site := fmt.Sprintf("%s:%d", file, line)
	return makeSubGoalsAt(fullSearch, goal, c, site, successors, nil, childrenGoals...)
}

// callSite names the line its caller builds a step at, as MakeSubGoals
// names the line it is called from.
func callSite() string {
	_, file, line, _ := runtime.Caller(1)
	return fmt.Sprintf("%s:%d", file, line)
}

// HypSuccessors is the step's hypothesis provenance for child k: for
// each hypothesis of the goal, by index, the index of its successor in
// the child, or NoSuccessor when the child holds no single hypothesis
// for it. Nil when the tactic recorded none for that child.
func (s *SubGoals) HypSuccessors(k int) []int {
	if s.hypSuccessors == nil {
		return nil
	}
	return s.hypSuccessors[k]
}

// ComposeSuccessors is the provenance of two steps run in sequence:
// first maps a goal's hypotheses into an intermediate goal's, second
// that goal's into a child's. Nil when either step recorded none.
func ComposeSuccessors(first, second []int) []int {
	if first == nil || second == nil {
		return nil
	}
	out := make([]int, len(first))
	for i, j := range first {
		if j == NoSuccessor {
			out[i] = NoSuccessor
		} else {
			out[i] = second[j]
		}
	}
	return out
}

// hypIndexOf is the index of the hypothesis of g α-equal to t, or
// NoSuccessor when g holds none.
func hypIndexOf(g Prop, t Term) int { return hypIndexIn(g.Hyps(), t) }

// hypIndexIn is hypIndexOf over a goal's hypothesis list: a binary
// search in the kernel's order, confirmed by α-equality, and a linear
// α-scan where the order does not place t.
func hypIndexIn(hyps []Term, t Term) int {
	if i, found := slices.BinarySearchFunc(hyps, t.Core(), Term.Compare); found && hyps[i].AlphaEquals(t) {
		return i
	}
	for i, h := range hyps {
		if h.AlphaEquals(t) {
			return i
		}
	}
	return NoSuccessor
}

// hypSuccessorsOf is the provenance of a child a tactic built from
// images: images[i] is the term hypothesis i of the parent became, nil
// where the step dropped it. Each image is located in child by
// α-equality, since MakeProp sorted and merged the list the caller
// built, so two hypotheses rewritten to one term share one successor.
func hypSuccessorsOf(child Prop, images []Term) []int {
	hyps := child.Hyps()
	succ := make([]int, len(images))
	for i, image := range images {
		if image == nil {
			succ[i] = NoSuccessor
			continue
		}
		succ[i] = hypIndexIn(hyps, image)
		Assert(succ[i] != NoSuccessor)
	}
	return succ
}

// makeImageProp is the goal `images ⊢ concl` over the non-nil images,
// built from a copy: MakeProp sorts the list it is handed in place, and
// the caller reads images back through hypSuccessorsOf.
func makeImageProp(concl Term, images []Term) Prop {
	hyps := make([]Term, 0, len(images))
	for _, image := range images {
		if image != nil {
			hyps = append(hyps, image)
		}
	}
	return MakeProp(concl, hyps...)
}

// keptSuccessors is the provenance of a child that keeps every
// hypothesis of goal, whatever it adds.
func keptSuccessors(goal, child Prop) []int { return hypSuccessorsOf(child, goal.Hyps()) }

// hypImages is goal's hypotheses with hypothesis i replaced by image —
// nil for a step that drops it — the list a tactic hands to MakeProp and
// to hypSuccessorsOf alike.
func hypImages(goal Prop, i int, image Term) []Term {
	images := goal.Hyps()
	images[i] = image
	return images
}

// dropHypSubGoals is the one child `Γ \ {hypothesis i} ⊢ C`, sound by
// weakening so the reconstruction is the identity, with its provenance.
func dropHypSubGoals(goal Prop, i int) *SubGoals {
	images := hypImages(goal, i, nil)
	child := MakeProp(goal.Conclusion(), restHyps(goal, i)...)
	return MakeTrackedSubGoals(goal, trivialReconstruct, [][]int{hypSuccessorsOf(child, images)}, child)
}

// checkSuccessors asserts a provenance map's shape: one entry per
// hypothesis of goal, each a slot of child or NoSuccessor.
func checkSuccessors(goal, child Prop, succ []int) {
	Assert(len(succ) == goal.NumHyps())
	for _, j := range succ {
		Assert(j == NoSuccessor || (0 <= j && j < child.NumHyps()))
	}
}

// _SearchMode is how a merged fixpoint runs (mergeTacticsUnder). Its
// deadline is polled throughout the search (abandonIfDone); once the
// deadline is done the search is abandoned. A probe's SubGoals is read
// for its size and never folded into a proof, so makeSubGoalsAt does not
// run the reconstruct gate on the nodes a probe builds.
type _SearchMode struct {
	deadline context.Context
	probe    bool
	// normalForms holds the pre-CNF normal forms the rule rewrites of
	// one run of the search have read (ruleCache). The fixpoint calls
	// its equality tactics on one goal after another, and a goal keeps
	// most of its hypotheses from the one before, so the run reads each
	// hypothesis's normal form once. nil for a mode that is no one run:
	// fullSearch, whose every rule set then reads for itself.
	normalForms *prop.PreCNFCache
}

// fullSearch is the unbounded driver: never abandoned, every node gated.
var fullSearch = _SearchMode{deadline: context.Background()}

// probeSearch is a search bounded by ctx whose result is only measured.
func probeSearch(ctx context.Context) _SearchMode {
	return _SearchMode{deadline: ctx, probe: true}.asRun()
}

// asRun is mode as one run of a fixpoint: a mode that holds no normal
// forms is given a cache of its own for them, and one that does is
// returned as it is, the fixpoint being a step of that run. The cache
// lives as long as the run's tactics do.
func (mode _SearchMode) asRun() _SearchMode {
	if mode.normalForms == nil {
		mode.normalForms = new(prop.PreCNFCache)
	}
	return mode
}

// unbounded is the unbounded driver as a step of mode's run: fullSearch
// reading the run's normal forms.
func (mode _SearchMode) unbounded() _SearchMode {
	return _SearchMode{deadline: fullSearch.deadline, normalForms: mode.normalForms}
}

// ruleCache is the cache one rule set's rewrites read their pre-CNF
// fallback from (prop.ContextEqRewriteOpt), in front of the run's normal
// forms (prop.NewPreCNFCacheOver).
func (mode _SearchMode) ruleCache() *prop.PreCNFCache {
	return prop.NewPreCNFCacheOver(mode.normalForms)
}

// boundedSearch is a search bounded by ctx whose result is kept: every
// node is gated as in fullSearch, so a search that reaches its fixpoint
// before the deadline returns what fullSearch returns.
func boundedSearch(ctx context.Context) _SearchMode {
	return _SearchMode{deadline: ctx}.asRun()
}

// makeSubGoalsAt builds the SubGoals; mode's deadline is polled inside
// the dedup pass — a pass quadratic in the children, which for a
// case-split subtree is where a bounded search would otherwise spend its
// time after the deadline.
//
// below is nil for a step a tactic makes. A fold's children are the
// children of the steps it folds (expandUnder), and below[r][i] is the
// theorem the gate of the step child i came from replaced it by in
// reading r, nil where it replaced none: the fold's gate replaces the
// child by that same theorem, so the step below is read and not run.
func makeSubGoalsAt(mode _SearchMode, goal Prop, c _TacticReconstruct, site string, successors [][]int, below [][]Prop, childrenGoals ...Prop) *SubGoals {
	Assert(utils.None(childrenGoals, goal.AlphaEquals))
	Assert(utils.None(childrenGoals, Prop.Proved))
	if successors != nil {
		Assert(len(successors) == len(childrenGoals))
		for k, succ := range successors {
			if succ != nil {
				checkSuccessors(goal, childrenGoals[k], succ)
			}
		}
	}
	// dedup children goals.
	compactGoals := make([]Prop, 0, len(childrenGoals))
	// mapping[i] = j means the i-th child goal is weaker than j-th, so it can be replaced.
	goalsMapping := make([]int, len(childrenGoals))
	// source[j] is the child goal that stands in compact slot j — the
	// one whose provenance the slot keeps.
	source := make([]int, 0, len(childrenGoals))
	for i, g := range childrenGoals {
		mode.abandonIfDone()
		foundWeaker := false
		for j := range compactGoals {
			if IsStronger(compactGoals[j], g) {
				goalsMapping[i] = j
				foundWeaker = true
				break
			} else if IsStronger(g, compactGoals[j]) {
				compactGoals[j] = g
				source[j] = i
				goalsMapping[i] = j
				foundWeaker = true
				break
			}
		}
		// if no weaker goal is found, simply add it as usual.
		if !foundWeaker {
			goalsMapping[i] = len(compactGoals)
			compactGoals = append(compactGoals, g)
			source = append(source, i)
		}
	}
	mode.abandonIfDone()
	compactSuccessors := successors
	if successors != nil && len(compactGoals) != len(childrenGoals) {
		compactSuccessors = make([][]int, len(compactGoals))
		for j, i := range source {
			compactSuccessors[j] = successors[i]
		}
	}
	// The reconstruct gate: the callback is run here, ahead of any proof,
	// on the children's own goals, which holds it on a child closed at its
	// conclusion from all its hypotheses; a process that asked for it
	// (HoldStrongerCloses) holds it on a child closed by a stronger
	// theorem as well: by contradiction, and from no hypothesis. What the
	// runs return is kept on the step (onOwnGoals, held), and a fold's
	// callback reads it (reconstructOn): a run at a fold costs the fold's
	// own step, not the subtree under it. A piece is run again only
	// where the dedup above stood another goal in for one of its leaves.
	//
	// A probe's SubGoals is read for its size and never folded into a
	// proof, so the callback it would validate is never called: no run
	// is made there and nothing is kept.
	if len(compactGoals) == len(childrenGoals) {
		made := &SubGoals{goal: goal, reconstruct: c, childrenGoals: childrenGoals, creationSite: site, hypSuccessors: successors}
		if !mode.probe {
			made.onOwnGoals = c(childrenGoals...)
			Assert(IsStronger(made.onOwnGoals, goal))
			made.held = holdStrongerCloses(goal, c, site, childrenGoals, below)
		}
		return made
	}
	callback := func(childrenGoals ...Prop) Prop {
		mappedGoals := make([]Prop, len(goalsMapping))
		for i, j := range goalsMapping {
			Assert(i >= j)
			mappedGoals[i] = childrenGoals[j]
		}
		return c(mappedGoals...)
	}
	made := &SubGoals{goal: goal, reconstruct: callback, childrenGoals: compactGoals, creationSite: site, hypSuccessors: compactSuccessors}
	if !mode.probe {
		made.onOwnGoals = callback(compactGoals...)
		Assert(IsStronger(made.onOwnGoals, goal))
		// A compact slot takes the theorem of the child that stands in it.
		var compactBelow [][]Prop
		for _, row := range below {
			compactRow := make([]Prop, len(compactGoals))
			for j, i := range source {
				compactRow[j] = row[i]
			}
			compactBelow = append(compactBelow, compactRow)
		}
		made.held = holdStrongerCloses(goal, callback, site, compactGoals, compactBelow)
	}
	return made
}

// strongerCloses is the state of the half of the creation-time gate
// that reads a child closed by a theorem stronger than its goal
// (holdStrongerCloses): whether this process asked for it, and what it
// refused.
var strongerCloses struct {
	on      atomic.Bool
	mu      sync.Mutex
	refused []string
}

// HoldStrongerCloses runs run, a test binary's m.Run, with every step
// built from then on held to its children closed by a stronger theorem,
// by contradiction and from no hypothesis (holdStrongerCloses), and
// returns the exit code:
//
//	os.Exit(tactic.HoldStrongerCloses(m.Run))
//
// A refusal is a fault (utils.IsFault), which a recover that reads
// failures raises again; one that reads nothing can still swallow it,
// and the engine answers a fault as a failed move. So each refusal is
// also kept: where any was made the refusals are printed and the code
// is not 0, whatever run returned. The check costs two more
// runs of the reconstruction per child at every step, which is why a
// test binary of the engine's own packages asks for it and a proving
// process does not.
func HoldStrongerCloses(run func() int) int {
	strongerCloses.on.Store(true)
	code, refused := strongerCloseVerdict(run())
	for _, r := range refused {
		fmt.Fprintln(os.Stderr, r)
	}
	return code
}

// strongerCloseVerdict is the exit code of a run that returned
// code, and the refusals made during it: code itself where there were
// none, and never 0 where there were.
func strongerCloseVerdict(code int) (int, []string) {
	strongerCloses.mu.Lock()
	defer strongerCloses.mu.Unlock()
	if len(strongerCloses.refused) > 0 && code == 0 {
		code = 1
	}
	return code, slices.Clone(strongerCloses.refused)
}

// strongerClose is one way a child is closed by a theorem stronger than
// its goal: how the refusal names it, and the theorem that closes the
// child.
type strongerClose struct {
	how string
	thm func(child Prop) Prop
}

// strongerCloseReadings are the two ways the gate asks about. A child
// closed by contradiction is `its hypotheses ⊢ ⊥`; a child closed from
// no hypothesis is `⊢ its conclusion`, the theorem that rests on the
// fewest hypotheses.
var strongerCloseReadings = []strongerClose{
	{"closed by contradiction", func(child Prop) Prop { return MakeProp(F, child.Hyps()...) }},
	{"closed from no hypothesis", func(child Prop) Prop { return MakeProp(child.Conclusion()) }},
}

// holdStrongerCloses runs the reconstruction c of a step made at site
// on children closed by a theorem stronger than their goals, in each of
// the two ways (strongerCloseReadings): each child that states a
// conclusion over at least one hypothesis is replaced by the theorem of
// that reading, one child at a time and then all of them together, and
// c must return a theorem IsStronger than goal each time. Where c
// panics or returns anything else the step is refused: the refusal, a
// failed assertion naming the site, the children replaced and the
// reading, is kept (HoldStrongerCloses) and panicked with. A child with
// no hypothesis is left as it is, its goal being the strongest theorem
// that closes it, and so is a child that states ⊥, which no theorem
// closes from no hypothesis.
//
// A child is replaced by below[reading][child] where that is given, the
// theorem the gate of a step below replaced it by (makeSubGoalsAt), and
// by a theorem made here otherwise. The theorems and what c returned on
// them are returned, for the step to keep (heldCloses). Nothing is run,
// and nil is returned, unless the process asked.
func holdStrongerCloses(goal Prop, c _TacticReconstruct, site string, children []Prop, below [][]Prop) []heldCloses {
	if !strongerCloses.on.Load() {
		return nil
	}
	var closable []int
	for k, child := range children {
		if child.NumHyps() > 0 && !child.Conclusion().Equals(F) {
			closable = append(closable, k)
		}
	}
	run := func(reading strongerClose, stronger []Prop, closed []int) Prop {
		thms := slices.Clone(children)
		for _, k := range closed {
			thms[k] = stronger[k]
		}
		defer func() {
			r := recover()
			if r == nil {
				return
			}
			if _, abandoned := r.(searchAbandoned); abandoned {
				panic(r)
			}
			if _, cut := utils.AsCut(r); cut {
				panic(r)
			}
			refusal := fmt.Sprintf("%s The reconstruction of the step made at %s does not take its child(ren) %v %s: %v\n"+
				"(of %d children; a reconstruction is handed any theorem IsStronger than its child's goal)\ngoal: %s",
				utils.AssertionFailed, site, closed, reading.how, r, len(children), prop.PrintProp(goal))
			strongerCloses.mu.Lock()
			strongerCloses.refused = append(strongerCloses.refused, refusal)
			strongerCloses.mu.Unlock()
			panic(refusal)
		}()
		thm := c(thms...)
		if !IsStronger(thm, goal) {
			panic(fmt.Sprintf("it returns a theorem that is not IsStronger than the goal:\n%s", prop.PrintProp(thm)))
		}
		return thm
	}
	held := make([]heldCloses, len(strongerCloseReadings))
	for r, reading := range strongerCloseReadings {
		h := heldCloses{stronger: make([]Prop, len(children)), returned: make([]Prop, len(children))}
		for _, k := range closable {
			if below != nil && below[r][k] != nil {
				h.stronger[k] = below[r][k]
			} else {
				h.stronger[k] = reading.thm(children[k])
			}
		}
		for _, k := range closable {
			h.returned[k] = run(reading, h.stronger, []int{k})
		}
		if len(closable) > 1 {
			h.all = run(reading, h.stronger, closable)
		}
		held[r] = h
	}
	return held
}

// MakeEmptySubGoals closes a goal outright with thm (no subgoals). thm is a
// Prop, not a Thm, so a promise-backed closer threads through Reconstruct into
// the goal stack's provedThm without forcing; a realized Thm satisfies Prop, so
// every existing caller is unaffected. IsStronger reads only statements, so the
// guard holds for an unforced promise too.
func MakeEmptySubGoals(goal Prop, thm Prop) *SubGoals {
	Assert(IsStronger(thm, goal))
	return MakeSubGoals(goal, func(...Prop) Prop { return thm })
}

func (s *SubGoals) ChildGoal(i int) Prop { return s.childrenGoals[i] }

func (s *SubGoals) Reconstruct(thms ...Prop) Prop {
	Assert(slices.EqualFunc(thms, s.childrenGoals, IsStronger))
	thm := s.reconstruct(thms...)
	Assert(IsStronger(thm, s.goal))
	// Thm-preservation gate: when every input is Thm-backed (a realized
	// ThmCert or an unforced ThmPromise), the reconstruct callback must
	// produce a Thm-backed Prop too. A bare proposition here is a leak —
	// the goal_stack later narrows it via core.AsThm for the parent's
	// PromisedThm() and panics with "AsThm: not a theorem". The early
	// assert names the offending callback's creation site so the leak is
	// fixed at its source rather than bandaged downstream.
	if !thm.Proved() && !core.IsPromised(thm) {
		allInputsThm := true
		for _, t := range thms {
			if !t.Proved() && !core.IsPromised(t) {
				allInputsThm = false
				break
			}
		}
		if allInputsThm {
			panic(fmt.Sprintf(
				"SubGoals.Reconstruct: callback from %s returned a bare "+
					"proposition (key=%s) from %d Thm-backed inputs. The "+
					"callback must wrap its output in a kernel-derived Thm "+
					"or a core.Promise that forces inputs first. AsThm "+
					"downstream would panic otherwise.",
				s.creationSite, thm.AlphaKey(), len(thms)))
		}
	}
	return thm
}

func (s *SubGoals) Size() int { return len(s.childrenGoals) }

func (s *SubGoals) String() string {
	props := make([]string, len(s.childrenGoals)+1)
	props[0] = fmt.Sprintln(
		"goal:\n", prop.PrintProp(s.goal),
		"\nnum of sub goals:", len(s.childrenGoals))
	for i, p := range s.childrenGoals {
		props[i+1] = fmt.Sprintln("sub goal", i, ":\n", prop.AddTab(prop.PrintProp(p)))
	}
	return strings.Join(props, "")
}

type Tactic func(Prop) *SubGoals

var nilTactic = func(Prop) *SubGoals { return nil }

// Uses the given tactic to expand the subgoals, then flattens the children.
func (t Tactic) expand(s *SubGoals) *SubGoals { return t.expandUnder(fullSearch, s) }

// expandUnder is expand in a search mode (see mergeTacticsUnder).
func (t Tactic) expandUnder(mode _SearchMode, s *SubGoals) *SubGoals {
	expanded := false
	var flattenSubGoals []Prop
	// The flattened children's provenance: a child's own map composed
	// with its expansion's, nil as soon as either side recorded none.
	var flattenSuccessors [][]int
	tracked := false
	arities := make([]int, s.Size())
	expansions := make([]*SubGoals, s.Size())
	for i, goal := range s.childrenGoals {
		mode.abandonIfDone()
		own := s.HypSuccessors(i)
		if sg := t(goal); sg != nil {
			expanded = true
			arities[i] = sg.Size()
			flattenSubGoals = append(flattenSubGoals, sg.childrenGoals...)
			expansions[i] = sg
			for k := range sg.childrenGoals {
				composed := ComposeSuccessors(own, sg.HypSuccessors(k))
				tracked = tracked || composed != nil
				flattenSuccessors = append(flattenSuccessors, composed)
			}
		} else {
			arities[i] = 1
			flattenSubGoals = append(flattenSubGoals, goal)
			expansions[i] = nil
			tracked = tracked || own != nil
			flattenSuccessors = append(flattenSuccessors, own)
		}
	}
	if !expanded {
		return s
	}
	if !tracked {
		flattenSuccessors = nil
	}
	reconstruct := func(provedProps ...Prop) Prop {
		j := 0
		thms := make([]Prop, s.Size())
		for i := range s.childrenGoals {
			if expansions[i] == nil {
				thms[i] = provedProps[j]
			} else {
				thms[i] = expansions[i].reconstructOn(provedProps[j : j+arities[i]])
			}
			j += arities[i]
		}
		thm := s.Reconstruct(thms...)
		return thm
	}
	// The theorems the gates of the folded steps replaced their children
	// by, child for child, for this step's gate to replace them by too
	// (makeSubGoalsAt); a child no step below was gated on has none.
	var below [][]Prop
	if strongerCloses.on.Load() && !mode.probe {
		for r := range strongerCloseReadings {
			row := make([]Prop, 0, len(flattenSubGoals))
			for i := range s.childrenGoals {
				if expansions[i] != nil && expansions[i].held != nil {
					row = append(row, expansions[i].held[r].stronger...)
				} else {
					row = append(row, make([]Prop, arities[i])...)
				}
			}
			below = append(below, row)
		}
	}
	// The repetition among flattenSubGoals (if any)
	// will be removed in makeSubGoals.
	_, file, line, _ := runtime.Caller(0)
	return makeSubGoalsAt(mode, s.goal, reconstruct, fmt.Sprintf("%s:%d", file, line), flattenSuccessors, below, flattenSubGoals...)
}

// abandonIfDone is the deadline poll of a search: past the deadline the
// search is abandoned by panic, recovered at the tactic's entry
// (mergeTacticsUnder), which returns nil.
func (mode _SearchMode) abandonIfDone() {
	if mode.deadline.Err() != nil {
		panic(searchAbandoned{})
	}
}

// whistleBackstopDepth is the trajectory depth at which the merged-
// tactic fixpoint starts running the divergence whistle
// (skeleton.Trajectory.EmbedsAncestor). Below it the driver runs
// unchecked — one node allocation per step — so every terminating
// trajectory short of the backstop replays bit-identically, every
// recorded proof in the corpus included (see the measurement below).
// Past the backstop, only trajectories that would spin forever (or grind
// far beyond anything the corpus ever stored) are affected: the
// whistle stops the branch and returns the current goal as-is, which
// is always sound. Kruskal's tree theorem makes the whistle complete —
// no infinite trajectory escapes it (see ext/skeleton/embed.go) — so
// termination of the fixpoint does not rest on any per-rule guard.
//
// Derivation: instrumenting this driver over the FULL corpus replay
// (TestReplayAll) measured a maximum trajectory depth of 30; 128 ≈ 4×
// that maximum. The margin is deliberately wide because its only cost is
// how many extra steps a divergent branch burns before being cut,
// while the benefit is that no realistically-terminating trajectory —
// stored today or authored later — comes near the whistle. Re-measure
// (append-to-file probe on qNode.Depth(), env-gated) before lowering.
//
// A var (not a const) only so whistle tests can exercise the driver at
// a small depth; production code never writes it.
var whistleBackstopDepth = 128

// openLeafBackstop is the breadth dual of whistleBackstopDepth. The
// whistle bounds a DIVERGENT trajectory; it cannot see a terminating
// one that fans. A goal with k hypotheses of the shape A ⇔ B (or A ∨ B,
// A ⇒ B) whose sides no rule decides case-splits into 2^k open leaves,
// and every level of the driver then deduplicates its flattened
// children pairwise (makeSubGoalsAt, a hyp-set subsumption walk per
// pair), quadratic in that fan: at k = 16 the fixpoint never returns.
//
// The count is per invocation: the open leaves — children no tactic
// simplifies, the ones the whistle left unexpanded included — this
// fixpoint has produced so far. Reaching the backstop refuses the WHOLE
// expansion: the invocation returns nil, "nothing applied", and the
// caller's remaining tactics still run on the goal (Basic's rewrites
// and non-branching simplifications go on after its case-split
// component declines). Refusing all of it rather than keeping a
// partial fan is what bounds the cost: the partial tree is never folded
// or deduplicated, and a case analysis the driver could not finish is
// no simplification to hand back. The refusal is a pure function of
// the goal (the expansion order is fixed), so a conditioning stage that
// keys its output on the result stays deterministic — a wall-clock
// bound could not stand here.
//
// Derivation: instrumenting the driver over the FULL corpus replay
// (TestReplayAll, 1968 entries) measured a maximum of 256 open leaves
// in one invocation — bit_set.MaskAsBitSet's Basic, whose inner
// case-split fixpoint (boolOpDivide) spreads 8 independent ⇔
// hypotheses into 256 branches that the outer Basic then closes one by
// one. 512 is 2× that maximum. The margin is narrower than the
// whistle's 4× because the cost of a refusal is quadratic in the
// backstop (the completed subtrees below it were deduplicated), and a
// case analysis of 512 open branches is already the slowest thing
// Basic does; an argument that needs more belongs to the refuter,
// which reads ⇔ in clause form. Re-measure (append-to-file probe on
// the open count at the driver's entry, env-gated) before lowering.
//
// A var (not a const) only so tests can exercise the driver at a small
// breadth; production code never writes it.
var openLeafBackstop = 512

// The merged tactic recursively runs all given tactics.
//
// Termination: the recursion itself carries the mechanism — a
// per-branch skeleton.Trajectory of the goals visited, checked (past
// whistleBackstopDepth) with the homeomorphic-embedding whistle. When
// the whistle blows for a child goal, that branch simply keeps the
// child unexpanded (the tactic returns nil for it), which is the
// driver's ordinary "no further simplification" outcome. The per-rule
// guards inside the component tactics (eq_rewrite.go's IsSub/self-embed
// probes etc.) are cheap pre-filters and do not bear the termination
// burden. Breadth is bounded separately, by openLeafBackstop.
func mergeTactics(tactics ...Tactic) Tactic { return mergeTacticsUnder(fullSearch, tactics...) }

// mergeTacticsUnder is mergeTactics in a search mode: once the mode's
// deadline is done the search is ABANDONED and the tactic returns nil,
// as if nothing applied. The whistle bounds a divergent trajectory and
// openLeafBackstop a fanning one; a caller that runs the fixpoint as a
// probe (the recorder's economy audit) additionally puts its
// wall-clock budget here. Abandoning is the whole point: the search's
// partial tree is worthless to a probe, and folding it back (every
// level flattens and dedups its leaves, a quadratic pass over
// thousands of case-split goals, each comparison a hyp-set walk) costs
// far more than the search did — so the deadline is polled inside that
// pass too (expandUnder, makeSubGoalsAt), not only at each new child.
func mergeTacticsUnder(mode _SearchMode, tactics ...Tactic) Tactic {
	inner := mergeTacticsNestedUnder(mode, tactics...)
	return func(p Prop) (result *SubGoals) {
		defer func() {
			if r := recover(); r != nil {
				switch r.(type) {
				case searchAbandoned, breadthExceeded:
					result = nil
				default:
					panic(r)
				}
			}
		}()
		return inner(p)
	}
}

// mergeTacticsWithin is mergeTacticsUnder as a step of a search whose
// entry reads the abandon (LemmaPreserveTacticUntil): a breadth refusal
// ends the fixpoint here as it does at mergeTacticsUnder's entry — nil,
// nothing applied — and a deadline abandon is left to that entry. In
// fullSearch, which is never abandoned, it is mergeTactics.
func mergeTacticsWithin(mode _SearchMode, tactics ...Tactic) Tactic {
	inner := mergeTacticsNestedUnder(mode, tactics...)
	return func(p Prop) (result *SubGoals) {
		defer func() {
			if r := recover(); r != nil {
				if _, refused := r.(breadthExceeded); !refused {
					panic(r)
				}
				result = nil
			}
		}()
		return inner(p)
	}
}

// mergeTacticsNestedUnder is the fixpoint WITHOUT the entry recover —
// the form a component takes when it is itself a component of another
// merged fixpoint (Basic's case splits and connective simplifications,
// TrivialSimplify's, a lemma install's residual simplify). Its breadth
// refusal propagates to the ENCLOSING driver, which records it and does
// not enter that component again for the rest of its own invocation; a
// deadline abandon propagates all the way to the outermost entry.
//
// Recovering at each nesting level instead — every level its own
// counter, a refused inner search handed to the outer as an ordinary
// "nothing applied" leaf — would let the outer re-enter the inner
// fixpoint after each of its own cheap simplifications: one connective
// peeled, one child, the split tried again from the top, fanned to the
// backstop again, refused again. A `by` whose conditioned premises fan
// does exactly that — eight inner refusals in one attempt, each at
// open=512 and each costing the fold-back of the completed subtrees
// beneath it, for a close none of those refusals contributes to. The
// refusal stays LOCAL (the outer goes on with its non-branching
// simplifications, as TestBreadthBackstopIsLocalToTheInvocation pins)
// and is not repeated. The corpus never reaches an inner refusal (its
// measured
// maximum is 256 open leaves, inside one such inner fixpoint), so no
// recorded proof sees the difference — the replay harness's
// whistle-free gate certifies that.
func mergeTacticsNestedUnder(mode _SearchMode, tactics ...Tactic) Tactic {
	if len(tactics) == 0 {
		return nilTactic
	}
	// open is this invocation's open-leaf count (openLeafBackstop);
	// refused marks the components — nested fixpoints — that reached
	// their own backstop during this invocation, not to be entered again.
	var run func(p Prop, node *skeleton.Trajectory, open *int, refused []bool) *SubGoals
	run = func(p Prop, node *skeleton.Trajectory, open *int, refused []bool) *SubGoals {
		for k, t := range tactics {
			if refused[k] {
				continue
			}
			if s := applyUnlessBreadthRefused(t, p, &refused[k]); s != nil {
				var child Tactic = func(q Prop) *SubGoals {
					mode.abandonIfDone()
					qNode := node.Extend(q)
					var r *SubGoals
					if qNode.Depth() > whistleBackstopDepth &&
						qNode.EmbedsAncestor() {
						skeleton.ReportWhistleFire(skeleton.WhistleEvent{
							Driver: "mergeTactics",
							Depth:  qNode.Depth(),
							Budget: whistleBackstopDepth,
							Goal:   q,
							Entry:  qNode.Entry(),
						})
					} else {
						r = run(q, qNode, open, refused)
					}
					if r == nil {
						*open++
						if *open >= openLeafBackstop {
							skeleton.ReportWhistleFire(skeleton.WhistleEvent{
								Driver: "mergeTactics",
								Depth:  qNode.Depth(),
								Budget: openLeafBackstop,
								Open:   *open,
								Goal:   q,
								Entry:  qNode.Entry(),
							})
							panic(breadthExceeded{})
						}
					}
					return r
				}
				return child.expandUnder(mode, s)
			}
		}
		return nil
	}
	return func(p Prop) *SubGoals {
		open := 0
		var root *skeleton.Trajectory
		return run(p, root.Extend(p), &open, make([]bool, len(tactics)))
	}
}

// applyUnlessBreadthRefused runs one component on the goal. A breadth
// refusal raised INSIDE the component (a nested fixpoint at its
// backstop) is caught here, the component is marked refused for the
// rest of the enclosing invocation, and the goal is left as the
// component found it — nil, "nothing applied". The enclosing driver's
// own breadth refusal is raised in its child expansion, outside this
// call, and still reaches its entry; a deadline abandon is not caught.
func applyUnlessBreadthRefused(t Tactic, p Prop, mark *bool) (s *SubGoals) {
	defer func() {
		if r := recover(); r != nil {
			if _, ok := r.(breadthExceeded); ok {
				*mark = true
				s = nil
				return
			}
			panic(r)
		}
	}()
	return t(p)
}

// searchAbandoned is the panic mergeTacticsUnder raises at its
// deadline, and breadthExceeded the one it raises at openLeafBackstop;
// both are recovered at the tactic's entry — the two ways out of the
// fixpoint that skip the fold-back of the partial tree.
type searchAbandoned struct{}

type breadthExceeded struct{}

// The chained tactic run all given tactics sequentially for once.
func chainTactics(tactics ...Tactic) Tactic {
	if len(tactics) == 0 {
		return nilTactic
	}
	return func(p Prop) *SubGoals {
		var s *SubGoals
		for _, t := range tactics {
			if s == nil {
				s = t(p)
			} else {
				s = t.expand(s)
			}
		}
		return s
	}
}

// Export tactics
// This tactic only returns up to 1 sub goal. Each call is one run of the
// fixpoint, with the run's normal forms (_SearchMode.asRun).
var TrivialSimplifyTactic Tactic = func(p Prop) *SubGoals {
	run := fullSearch.asRun()
	return mergeTactics(
		simplestTrivialTactic,
		rewriteTactic(prop.BasicRewrite),
		boolOpSimplifyNestedUnder(fullSearch),
		eqSimplifyUnder(run),
		trivialTactic,
	)(p)
}

// UnfoldTidyTactic is the tidy that follows an unfolded definition
// (the def_expand composite): TrivialSimplifyTactic without
// eqSimplifyUnder, the rewrite by resident facts. The unfolded sequent
// is β-reduced and its connectives simplified, a resident conjunction
// split, a leaf whose conclusion a hypothesis states as a whole or whose
// hypotheses contradict closed — and no resident fact is read into the
// goal, neither an equation nor a fact as the rewrite `P ↦ ⊤`: an author
// who wants the opened goal rewritten or closed by one spells it
// (`eq.Rw()`, `a.Simplified(h, Fwd(eq))`, `By(Normalized, clauses…)`), so
// a proof says which facts it leans on. At most one subgoal.
var UnfoldTidyTactic = mergeTactics(
	simplestTrivialTactic,
	rewriteTactic(prop.BasicRewrite),
	boolOpSimplifyNestedUnder(fullSearch),
	trivialTactic,
)

// This tactic may return multiple sub goals. Each call is one run of the
// fixpoint, with the run's normal forms (_SearchMode.asRun).
var BasicTactics Tactic = func(p Prop) *SubGoals {
	return mergeTactics(basicTactics(fullSearch.asRun())...)(p)
}

// basicTactics is Basic's component list; the two components that are
// merged fixpoints of their own (the case splits and the connective
// simplifications) run in the same search mode. The equality tactic is
// the unbounded one whatever the mode, and reads the run's normal forms.
func basicTactics(mode _SearchMode) []Tactic {
	return []Tactic{
		simplestTrivialTactic,
		rewriteTactic(prop.BasicRewritesWith(prop.UniqueRewrite)),
		boolOpDivideNestedUnder(mode),
		boolOpSimplifyNestedUnder(mode),
		unifyEqSimplifyUnder(mode.unbounded()),
		trivialTactic,
	}
}

// BasicTacticsUnder is BasicTactics as a probe bounded by ctx (see
// mergeTacticsUnder): the same fixpoint, abandoned (nil) at the
// deadline. The SubGoals it returns is for measuring only: a probe's
// nodes skip the reconstruct gate (makeSubGoalsAt), so a caller does not
// fold it into a proof.
func BasicTacticsUnder(ctx context.Context) Tactic {
	mode := probeSearch(ctx)
	return mergeTacticsUnder(mode, basicTactics(mode)...)
}

// BasicTacticsUntil runs the BasicTactics fixpoint on p until ctx is
// done. A search that reaches its fixpoint returns what BasicTactics
// returns, every node gated, and folds into a proof. abandoned reports
// that the deadline ended the search first: sg is then nil and stands
// for nothing — the caller does not read it as "nothing applied". The
// deadline is polled between the fixpoint's steps (mergeTacticsUnder),
// never before the first.
func BasicTacticsUntil(ctx context.Context, p Prop) (sg *SubGoals, abandoned bool) {
	mode := boundedSearch(ctx)
	inner := mergeTacticsNestedUnder(mode, basicTactics(mode)...)
	defer func() {
		if r := recover(); r != nil {
			switch r.(type) {
			case searchAbandoned:
				sg, abandoned = nil, true
			case breadthExceeded:
				sg = nil
			default:
				panic(r)
			}
		}
	}()
	return inner(p), false
}

// WithHyp returns the decomposition as it reads once h is a hypothesis
// of the goal: h joins the goal and every child goal, the reconstruction
// is unchanged. Sound because certificates are monotone in the goal's
// hypotheses — a proof of a child certifies the child with h as well —
// so a subtree closed under the original decomposition closes under
// this one. The receiver is not mutated: checkpoints share SubGoals by
// pointer. A goal that already carries h (α-equal) is returned as is.
func (s *SubGoals) WithHyp(h Term) *SubGoals {
	goal := WithHyp(s.goal, h)
	children := make([]Prop, len(s.childrenGoals))
	for i, g := range s.childrenGoals {
		children[i] = WithHyp(g, h)
	}
	// The provenance re-indexed over the widened goal: a hypothesis the
	// goal had keeps its successor, and h — present in every child —
	// is its own.
	var successors [][]int
	if s.hypSuccessors != nil {
		successors = make([][]int, len(children))
		for k, succ := range s.hypSuccessors {
			if succ == nil {
				continue
			}
			images := make([]Term, goal.NumHyps())
			for p := range goal.NumHyps() {
				t := goal.Hyp(p)
				q := hypIndexOf(s.goal, t)
				switch {
				case q == NoSuccessor:
					images[p] = h
				case succ[q] != NoSuccessor:
					images[p] = s.childrenGoals[k].Hyp(succ[q])
				}
			}
			successors[k] = hypSuccessorsOf(children[k], images)
		}
	}
	return &SubGoals{
		goal:          goal,
		reconstruct:   s.reconstruct,
		childrenGoals: children,
		creationSite:  s.creationSite,
		hypSuccessors: successors,
	}
}

// WithHyp is g with h as one more hypothesis (canonically placed — the
// hyp list stays sorted), or g itself when it already carries h.
func WithHyp(g Prop, h Term) Prop {
	if g.HasHyp(h) {
		return g
	}
	return prop.MakeProp(g.Conclusion(), append(g.Hyps(), h)...)
}
