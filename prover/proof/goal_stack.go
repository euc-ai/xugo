/** File: goal_stack.go
 *
 * This file defines the GoalStackNode structure and its associated functions.
 *
 * GoalStackNode represents a goal in the proof process, serving as the fundamental
 * building block of the proof tree. Each node contains a goal proposition to be proved,
 * references to its parent expansion and its own expansion, and a linked list of proof
 * actions.
 *
 * Key components:
 * - _SubGoalsExpansion: represents the expansion of a goal node, containing the
 *   MiniStep used for expansion, resulting subgoals, and child nodes
 * - _ProveStatus: tracks the proof status of a node (pending, succeed)
 * - _ProofActionLinkedList: A linked list of Actions representing the proof steps
 *
 * Each GoalStackNode can be expanded using MiniSteps, which transform a goal
 * into subgoals. A node is considered proved when all of its subgoals are proved.
 */

package proof

import (
	"context"
	"errors"
	"fmt"
	"io"
	"iter"
	"slices"
	"strings"
	sync "sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

type _ProveStatus int

const (
	pending _ProveStatus = iota
	succeed
)

func (s _ProveStatus) String() string {
	switch s {
	case pending:
		return "Pending"
	case succeed:
		return "Succeed"
	default:
		panic("Wrong status.")
	}
}

// A linked list of Actions representing the proof steps.
type _ProofActionLinkedList struct {
	action Macro
	next   *GoalStackNode
}

type GoalStackNode struct {
	// The Goal that needs to be proved.
	Goal Prop

	// The parent node. Nil if this is the root.
	parent *GoalStackNode

	// Expansion result of this node (one mini step) if expanded.
	// If not expanded, miniStep == nil and subGoals/children/provedThm are unset.
	miniStep _Step
	subGoals *SubGoals
	children []*GoalStackNode
	// provedThm is the certificate for this node's Goal once closed. It is a
	// Prop, not a Thm: when the closing reconstruction runs over promise-backed
	// subgoals it is a derived ThmPromise (the promises pass through),
	// realized only on Force. A plain Thm (the eager case) is also a Prop.
	// nil until closed.
	provedThm Prop

	// The proof action linked list of this node.
	proofAction *_ProofActionLinkedList

	// Owning script. Set only on section roots created via
	// Script.Section / SectionText; nil for
	// every other GoalStackNode (kernel-only uses, expansion children,
	// clones). Read by Qed() — which walks up parents to find the
	// enclosing section root and delegates to root.script.ClaimProved.
	// Kept unexported because users of the kernel proof tree shouldn't
	// poke at script state directly.
	script *Script

	// proofScope is immutable lexical theorem identity/capability state.
	// Unlike script it is copied to every child so ministeps never need a
	// process-global "current theorem".
	proofScope *ProofScope
}

// SetProofScope attaches an explicit ProofScope to this goal tree.
// Engine sessions arm every tactic clone with the session's
// witness-derived static scope (NewStaticProofScope from the target's
// recorded policy variant) so per-Arith-call bundle selection honours
// the same omega circularity gate the replay harness enforces.
// Children inherit the scope via commitStep.
func (n *GoalStackNode) SetProofScope(scope *ProofScope) { n.proofScope = scope }

func (n *GoalStackNode) ProofScope() *ProofScope { return n.proofScope }

// ExpansionPlan captures the full effect of an action on a goal node.
// It holds a fully-expanded clone that, when committed, transplants its
// subtree onto the target node. The plan is produced by TryExpandPlan
// (which runs the complete action on a clone) and consumed by Commit.
type ExpansionPlan struct {
	expanded *GoalStackNode // fully-expanded clone of the target node
}

func CreateGoalStack(g Prop) *GoalStackNode { return &GoalStackNode{Goal: g} }

func (n *GoalStackNode) String() string {
	if n.Proved() {
		// Raw cert Prop (promise-preserving), NOT the collapsing ProvedThm():
		// String() is reached from panic/error messages, and a node closed via
		// promise-backed lemmas carries an unforced promise that ProvedThm()
		// would panic on — crashing the very error report. The statement is all
		// we print, and a promise's statement is immutable.
		return fmt.Sprintln(
			"status:", n.status(),
			"\ngoal:\n", prop.PrintProp(n.provedThm))
	}
	if n.miniStep == nil {
		return fmt.Sprintln(
			"status:", n.status(),
			"\ngoal:\n", prop.PrintProp(n.Goal), "\nno known subgoal.")
	}

	UnsolvedLeaves := n.UnsolvedLeaves()

	props := make([]string, len(UnsolvedLeaves)+1)
	props[0] = fmt.Sprintln(
		"status:", n.status(),
		"\ngoal:\n", prop.PrintProp(n.Goal),
		"\nnum of unfinished leave subgoals:", len(UnsolvedLeaves))
	for i, c := range UnsolvedLeaves {
		props[i+1] = fmt.Sprintln("sub goal", i, ":\n",
			prop.AddTab(prop.PrintProp(c.Goal)))
	}
	return strings.Join(props, "")
}

func (n *GoalStackNode) PrintAction() string {
	if n.proofAction != nil {
		return n.proofAction.action.String()
	}
	return ""
}

// StepDescription returns a short human-readable description of the
// ministep that expanded this node, or "" for an unexpanded leaf. Falls
// back to the concrete step's type name when the step has no Stringer.
// Read by the engine's dump-section walk over proved (e.g. seeded)
// section trees.
func (n *GoalStackNode) StepDescription() string {
	if n.miniStep == nil {
		return ""
	}
	if s, ok := n.miniStep.(fmt.Stringer); ok {
		return s.String()
	}
	return strings.TrimPrefix(fmt.Sprintf("%T", n.miniStep), "prover.")
}

func (n *GoalStackNode) ChildrenIter() iter.Seq[*GoalStackNode] { return slices.Values(n.children) }

// hypSuccessors is the hypothesis provenance n's step recorded for
// child, one of n's children: for each hypothesis of n.Goal, by index,
// its index in child.Goal, or tactic.NoSuccessor where the step left no
// single hypothesis for it. Nil when the step recorded none.
func (n *GoalStackNode) hypSuccessors(child *GoalStackNode) []int {
	if n.subGoals == nil {
		return nil
	}
	for k, c := range n.children {
		if c == child {
			return n.subGoals.HypSuccessors(k)
		}
	}
	panic("GoalStackNode.hypSuccessors: the node is not a child of the receiver")
}

// ProvedThm is the external collapse boundary: it returns this node's
// certificate as a realized Thm (or nil if the node is not closed). Where
// promises pass through, the node's certificate may be an unforced
// ThmPromise; this accessor does NOT yet thread it — asRealizedThm panics
// if a promise reaches here, pinpointing the next caller to convert to
// Prop. Internal goal-stack reconstruction reads the raw provedThm field
// instead, so promises thread up the tree without collapsing.
func (n *GoalStackNode) ProvedThm() ThmCert {
	if n.provedThm != nil {
		Assert(n.miniStep != nil && IsStronger(n.provedThm, n.Goal))
		return asRealizedThm(n.provedThm)
	}
	return ThmCert{}
}

// PromisedThm is the promise-preserving certificate accessor: the node's cert
// as the Thm interface — a realized ThmCert in the eager case, or an unforced
// ThmPromise on the define-then-run path. Unlike ProvedThm() it never forces
// or collapses, so a promise threads through goal-stack reconstruction (and
// a member's Build) instead of panicking at the asRealizedThm boundary.
// (Named PromisedThm, not "Proved…", precisely because the cert may be an
// unforced promise, not yet proved.) The node must be closed — core.AsThm
// asserts provedThm is a thm/promise, panicking on an open (nil) node.
func (n *GoalStackNode) PromisedThm() Thm { return core.AsThm(n.provedThm) }

// Proved is the non-collapsing closed-node test: it reports whether the node
// holds a closing certificate, WITHOUT realizing it. Use this (not
// `ProvedThm() != nil`) for pure existence checks: a node closed via
// promise-backed ● lemmas carries an unforced ThmPromise, and ProvedThm()
// routes through asRealizedThm/AsThmCert which panics on such a promise (the
// documented collapse boundary). `ProvedThm() != nil` is identical to Proved()
// on the eager path and only differs by that panic, so every nil-check existence
// site is strictly safer using Proved().
func (n *GoalStackNode) Proved() bool { return n.provedThm != nil }

// Children returns the node's immediate children — the subgoals produced
// by n's miniStep (for an internal node) or nil (for a leaf, open or
// just-closed). Read-only accessor used by engine-package walkers that
// need to traverse the goal tree (e.g. enumerate closed sub-derivations
// for `cite-node` / `inspect`'s `closed_subtrees` field).
func (n *GoalStackNode) Children() []*GoalStackNode { return n.children }

func (n *GoalStackNode) status() _ProveStatus {
	if n.Proved() {
		return succeed
	}
	return pending
}

// Clone creates a deep copy of the goal tree rooted at this node.
// All logical content (Prop, Thm, SubGoals, MiniStep) is shared by reference
// since it is immutable. Only tree structure (node pointers, parent/children
// links) is copied. Proved subtrees are shared directly — once a node's
// provedThm is set, it and its descendants are never mutated again, so sharing
// is safe. Cost: O(unsolved nodes) rather than O(total nodes).
func (n *GoalStackNode) Clone() *GoalStackNode {
	return n.cloneWithParent(nil)
}

func (n *GoalStackNode) cloneWithParent(parent *GoalStackNode) *GoalStackNode {
	cloneNode := &GoalStackNode{
		Goal:       n.Goal,
		parent:     parent,
		miniStep:   n.miniStep,
		subGoals:   n.subGoals,
		provedThm:  n.provedThm,
		proofScope: n.proofScope,
	}
	if len(n.children) > 0 {
		cloneNode.children = make([]*GoalStackNode, len(n.children))
		for i, c := range n.children {
			if c.Proved() {
				// Proved subtree: create a thin wrapper with correct parent
				// pointer but share the entire subtree below.
				wrapper := &GoalStackNode{
					Goal:       c.Goal,
					parent:     cloneNode,
					miniStep:   c.miniStep,
					subGoals:   c.subGoals,
					provedThm:  c.provedThm,
					proofScope: c.proofScope,
					children:   c.children, // shared — never mutated
				}
				cloneNode.children[i] = wrapper
			} else {
				cloneNode.children[i] = c.cloneWithParent(cloneNode)
			}
		}
	}
	return cloneNode
}

// NodePath returns the child-index path from this node (as root) to target.
// Returns nil if target is not found in the subtree.
func (n *GoalStackNode) NodePath(target *GoalStackNode) []int {
	if n == target {
		return []int{}
	}
	for i, c := range n.children {
		if sub := c.NodePath(target); sub != nil {
			return append([]int{i}, sub...)
		}
	}
	return nil
}

// NodeAt follows a child-index path and returns the node at that position.
// Panics if any index is out of range.
func (n *GoalStackNode) NodeAt(path []int) *GoalStackNode {
	cur := n
	for _, idx := range path {
		cur = cur.children[idx]
	}
	return cur
}

func (n *GoalStackNode) child(i int) *GoalStackNode {
	Assert(n.miniStep != nil && len(n.children) > i)
	return n.children[i]
}

// Child is the exported, lenient twin of `child`: returns the i-th
// immediate child of n, or nil if n hasn't been split yet (no
// miniStep set) or i is out of range. Used by out-of-package callers
// (today: emit.advanceAfter) that need to peek at a specific
// child by index after Action.Apply, without first asserting the
// kernel mutation's child arity.
func (n *GoalStackNode) Child(i int) *GoalStackNode {
	if n.miniStep == nil || i < 0 || i >= len(n.children) {
		return nil
	}
	return n.children[i]
}

func (n *GoalStackNode) preorderTraverse() []*GoalStackNode {
	leaves := []*GoalStackNode{n}
	if len(n.children) > 0 {
		for _, child := range n.children {
			leaves = append(leaves, child.preorderTraverse()...)
		}
	}
	return leaves
}

func (n *GoalStackNode) NumUnsolvedLeaves() int {
	if n.miniStep == nil {
		return 1
	}
	if n.Proved() {
		return 0
	}
	k := 0
	for _, child := range n.children {
		k += child.NumUnsolvedLeaves()
	}
	return k
}

func (n *GoalStackNode) UnsolvedLeaves() []*GoalStackNode {
	if n.miniStep == nil {
		return []*GoalStackNode{n}
	}
	if n.Proved() {
		return nil
	}
	var leaves []*GoalStackNode
	for _, child := range n.children {
		leaves = append(leaves, child.UnsolvedLeaves()...)
	}
	return leaves
}

func (n *GoalStackNode) unsolvedLeavesIter() iter.Seq[*GoalStackNode] {
	if n.miniStep == nil {
		return utils.SingleIter(n)
	}
	if n.Proved() {
		return utils.EmptyIter[*GoalStackNode]
	}
	return utils.ConcatSeqIter(
		utils.MapIter(
			slices.Values(n.children),
			(*GoalStackNode).unsolvedLeavesIter))
}

func (n *GoalStackNode) unsolvedLeafImpl(i int) (*GoalStackNode, int) {
	Assert(i >= 0)
	if n.miniStep == nil {
		if i == 0 {
			return n, -1
		}
		return nil, 1
	}
	if n.Proved() {
		return nil, 0
	}
	k := 0
	for _, child := range n.children {
		n, j := child.unsolvedLeafImpl(i - k)
		if n != nil {
			return n, -1
		}
		k += j
	}
	return nil, k
}

func (n *GoalStackNode) unsolvedLeaf(i int) *GoalStackNode {
	leaf, _ := n.unsolvedLeafImpl(i)
	return leaf
}

func (n *GoalStackNode) thmLeavesIter() iter.Seq[*GoalStackNode] {
	if n.miniStep == nil {
		return utils.EmptyIter[*GoalStackNode]
	}
	if _, ok := n.miniStep.(_KnownThmStep); ok {
		return utils.SingleIter(n)
	}
	return utils.ConcatSeqIter(
		utils.MapIter(
			slices.Values(n.children),
			(*GoalStackNode).thmLeavesIter))
}

// Runs a ministep on a node.
// Returns whether the ministep is successful.
//
// Two optional Step hooks are honored here:
//
//   - applyRecording lets a step COMMIT A DIFFERENT VALUE than it was
//     handed — the step as its apply actually resolved it. A search-y
//     step whose choice is a decision, not a derivation (_AutoDenote's
//     subterm selection), returns itself with that decision filled in, so
//     what gets recorded is the choice rather than the recipe. Same
//     rationale as chooseTypeAdaptedStep committing its winner through
//     commitStep, and the same shape: decide, then commit once. A step
//     whose result a later action reads back from the node commits it
//     the same way (_SimpWithStep's rewritten hypothesis).
//   - applyScoped threads the node's ProofScope into the tactic.
//
// A step implements at most one; applyRecording receives the scope too.
func (n *GoalStackNode) runStep(step _Step) bool {
	if rec, ok := step.(interface {
		applyRecording(Prop, *ProofScope) (_Step, *SubGoals)
	}); ok {
		recorded, subGoals := rec.applyRecording(n.Goal, n.proofScope)
		return n.commitStep(recorded, subGoals)
	}
	if scoped, ok := step.(interface {
		applyScoped(Prop, *ProofScope) *SubGoals
	}); ok {
		return n.commitStep(step, scoped.applyScoped(n.Goal, n.proofScope))
	}
	return n.commitStep(step, step.apply(n.Goal))
}

// commitStep finalizes a ministep whose SubGoals have already been
// computed by the caller (against n.Goal), avoiding a redundant re-apply.
// `subGoals == nil` means the tactic did not apply — same contract as
// `runStep` returning false. Callers that compute SubGoals as part of
// a selection decision (e.g. chooseTypeAdaptedStep, which applies both the
// original and the type-adapted lemma to pick the better one) commit the
// winning SubGoals here instead of running the chosen tactic a third time.
func (n *GoalStackNode) commitStep(step _Step, subGoals *SubGoals) bool {
	Assert(n.miniStep == nil && !n.Goal.Proved())

	if subGoals == nil {
		return false
	}

	n.miniStep = step
	n.subGoals = subGoals
	if subGoals.Size() == 0 {
		// Keep the reconstruction as a Prop — a derived promise when the
		// reconstruction ran over promise-backed leaves. No eager .AsThm().
		n.provedThm = subGoals.Reconstruct()
		Assert(IsStronger(n.provedThm, n.Goal))
		n.updateUpwards()
		return true
	}

	n.children = make([]*GoalStackNode, subGoals.Size())
	for i := range n.children {
		Assert(!subGoals.ChildGoal(i).Proved())
		n.children[i] = &GoalStackNode{
			Goal:       subGoals.ChildGoal(i),
			parent:     n,
			proofScope: n.proofScope,
		}
	}
	return true
}

// Runs a ministep on all unsolved leaves, serially.
//
// Serial execution is deliberate: the caller (AutoExpand, ApplySimplify) is
// already running under some outer parallelism (prove sweep workers, engine
// request handlers), and fanning out here would just stack concurrency onto an
// already-saturated CPU, delaying ctx-deadline observations.
//
// ctx is polled between leaves so that a cancelled ctx stops the loop
// promptly. The current leaf's ministep is not interrupted — individual
// ministeps don't yet accept a quit signal.
func (n *GoalStackNode) runStepOnLeaves(ctx context.Context, s _Step) {
	for _, leaf := range n.UnsolvedLeaves() {
		if ctx.Err() != nil {
			return
		}
		leaf.runStep(s)
	}
}

// If a node is proved, tries to prove its parent recursively.
func (n *GoalStackNode) updateUpwards() {
	Assert(n.Proved())
	if n.parent == nil {
		return
	}
	if n.parent.provedThm == nil {
		// If all children are proved, proves the parent node.
		if !utils.All(n.parent.children, (*GoalStackNode).Proved) {
			return
		}
		thms := make([]Prop, n.parent.subGoals.Size())
		for i := range n.parent.children {
			// Raw cert Prop (promise-preserving), NOT the collapsing ProvedThm().
			thms[i] = n.parent.children[i].PromisedThm()
		}
		// Reconstruct over the children's certificate Props — a derived promise
		// if any child is promise-backed. No eager .AsThm().
		n.parent.provedThm = n.parent.subGoals.Reconstruct(thms...)
		Assert(IsStronger(n.parent.provedThm, n.parent.Goal))
	}
	n.parent.updateUpwards()
}

// TryApply attempts to apply an action, returning false if it fails.
func (n *GoalStackNode) TryApply(action Macro) bool {
	if n.miniStep != nil || !action.Apply(n) {
		return false
	}
	n.proofAction = &_ProofActionLinkedList{action: action}
	UnsolvedLeaves := n.UnsolvedLeaves()
	switch len(UnsolvedLeaves) {
	case 0:
		n.proofAction.next = nil
	case 1:
		n.proofAction.next = UnsolvedLeaves[0]
	default:
		return false
	}
	return true
}

// Apply applies an action, panicking on failure. Returns the single
// unsolved leaf if the proof still has work; returns the receiver itself
// when the action completed the proof (so chains can tail-call .Qed()
// without a nil-guard). The receiver's miniStep is set by TryApply on
// any further Apply against it, so a malformed double-Apply still
// surfaces as a TryApply assertion failure — the receiver-as-sentinel
// only matters as a target for Qed.
//
// Apply navigates to the section's first unsolved leaf before running —
// same pattern Cite/Rewrite/Do use — so it works equally well with a
// fluent chain receiver (which is itself the current leaf) and an
// imperative section-root receiver `sec.Do(...); sec.CloseByAuto()`
// (where the receiver stays the root and each call
// walks down to the advancing leaf).
func (n *GoalStackNode) Apply(action Macro) *GoalStackNode {
	leaf := n.unsolvedLeaf(0)
	if leaf == nil {
		panic("GoalStackNode.Apply: no unsolved leaves remaining " +
			"(section already proved — extra Apply call?). Action: " +
			action.String() + closedLeafNote(n))
	}
	traceStep("Apply", action.String(), leaf, func() {
		Assert(leaf.TryApply(action))
	})
	if leaf.proofAction.next == nil {
		return leaf
	}
	return leaf.proofAction.next
}

// Qed closes the enclosing section: walks up parent pointers to the
// section root (the node with script != nil — set by Script.Section*
// when the section was opened), then calls root.script.ClaimProved(root).
// Designed as the fluent terminator for an `Apply(...).Apply(...).Qed()`
// chain — replaces the longer `ctx.ClaimProved(<section>)` postfix and
// removes the need to repeat the section variable name.
//
// Panics if no script-bearing ancestor exists, i.e. the node belongs to
// a proof tree not opened via the Script API. Hand-written
// kernel-driven proofs without a Script keep using the standalone
// Env.ClaimProved.
func (n *GoalStackNode) Qed() {
	root := n.findScriptRoot()
	root.script.ClaimProved(root)
}

// findScriptRoot returns the section root (the first script-bearing
// ancestor, including the receiver). Panics if none exists.
func (n *GoalStackNode) findScriptRoot() *GoalStackNode {
	root := n
	for root != nil && root.script == nil {
		root = root.parent
	}
	if root == nil {
		panic("GoalStackNode: no script-owned ancestor — " +
			"section was not opened via Script.Section*")
	}
	return root
}

// findScript returns the owning Script (read off the section root). Used
// by node-level methods that need env / cache access (Auto, Induct, …)
// to look like a property of the node rather than a separate `ctx.X`
// call.
func (n *GoalStackNode) findScript() *Script {
	return n.findScriptRoot().script
}

// ----- Fluent Apply-style shortcuts ----------------------------------------
//
// Each of these is `Apply(<corresponding action>)` packaged as a method
// on the receiver: the chain reads `sec.Auto()` instead of
// `sec.Apply(script.Auto())`. Both need the environment, so they walk
// up to the section root's script via findScript() — the back-pointer
// Qed uses. A proof that bypasses the Script API calls `Apply(<action>)`.

// Auto runs the CNF refuter on the current goal. Walks up to the
// section root's script to pull env (the refuter closes over it).
func (n *GoalStackNode) Auto() *GoalStackNode {
	return n.Apply(n.findScript().Auto())
}

// CloseByAuto is the fluent terminator for an Auto chain step. Tries
// _TrivialNormalizedStep (Normalize→⊤) first; on miss falls back to
// env.AutoExpand — the same two steps as prover.CloseByAuto.
//
// Panics if the leaf can't be closed by either path.
func (n *GoalStackNode) CloseByAuto() *GoalStackNode {
	// Navigate to the section's first unsolved leaf before running —
	// same pattern Apply/UseLemma/Rewrite/Do use — so this works equally
	// well as a chain step (receiver IS the current leaf, navigation
	// is identity) and as an imperative section-root call (receiver
	// is the root, navigation walks down to the advancing leaf).
	leaf := n.unsolvedLeaf(0)
	if leaf == nil {
		panic("GoalStackNode.CloseByAuto: no unsolved leaves remaining " +
			"(section already proved — extra CloseByAuto call?)" + closedLeafNote(n))
	}
	if leaf.runStep(_TrivialNormalizedStep{}) {
		return leaf
	}
	return leaf.Apply(leaf.findScript().Env.AutoExpand())
}

// ----- Fused ministep idioms -----------------------------------------------
//
// Cite and Rewrite collapse two consecutive ministep calls into one
// statement at the call site. The two-Do form is what the kernel
// serializes; the fused form is what emit produces (and what a reader
// of an emitted member sees). Runtime semantics is identical — these
// methods fire exactly the same two Do calls, in the same order.
//
// The fused names are deliberately chosen to read as the IDIOM the
// reader cares about ("cite a known lemma", "rewrite by a def thm")
// rather than the two-step kernel mechanic (introduce-and-discharge).

// UseLemma is the idiom for "apply lemma L whose obligation is
// closed by L itself via cache" — emits as `Lemma(L)` then `KnownThm(L)`
// at the kernel level (surfaced as `CiteKnown(L)` in the Step API — see
// prover.Cite).
//
// Routes the first step through ApplyLemma so polymorphic-lemma
// type-adaptation is selected against the leaf goal — shared with the
// Action/search side. A `script.Do(n, Lemma(L))`
// call would bypass this, going straight to _LemmaTactic.apply with L
// unadapted; if L is polymorphic and the goal is monomorphic the
// tactic then returns nil and the fluent method panics on a goal that
// the proto-recorded form (already adapted by ApplyLemma at record
// time) handled cleanly. The claim child is then closed with L itself
// — at the type instance the adaptation chose, when L is polymorphic
// and the goal is not: the child's goal is L's statement under that
// σ, so the closing certificate is `PropTypeInst(L, σ)` (recovered by
// type-matching L against the child), exactly what the retired
// LemmaMacro did before handing its child to the same _KnownThmStep.
//
// Section-rooted call pattern: a caller invokes UseLemma as
// `<section>.UseLemma(...)` where the receiver is the section root, not
// the current unsolved leaf — same shape Script.Do uses. The section's
// first unsolved leaf is resolved here and used as the ApplyLemma
// target, so the chain of `Do / UseLemma / Rewrite` calls all operate
// on the same advancing leaf without the caller chaining return values.
func (n *GoalStackNode) UseLemma(L Prop) {
	leaf := n.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("GoalStackNode.UseLemma: no unsolved leaves remaining "+
			"(section already proved — extra UseLemma call?). Lemma: %s",
			prop.PrintProp(L)) + closedLeafNote(n))
	}
	if !ApplyLemma(leaf, L) {
		panic(fmt.Sprintf("GoalStackNode.UseLemma: ApplyLemma failed for lemma %s on goal %s",
			prop.PrintProp(L), prop.PrintProp(leaf.Goal)))
	}
	Assert(len(leaf.children) >= 1)
	closing := L
	if substs, ok := prop.IsTypeMatchOf(L, leaf.child(0).Goal, utils.FullPredicate[core.VarType]); ok && len(substs) != 0 {
		closing = core.PropTypeInst(L, substs...)
	}
	n.findScript().Do(leaf, CiteKnown(closing))
}

// UseLemmaExact is the replay-exact fused form of
// `LemmaPreserve(L)` + `KnownThm(L)`. It applies the stored
// LemmaPreserve payload exactly as serialized, without re-running
// chooseTypeAdaptedStep. Emit produces this for DetailedProofProto
// lemma_preserve+known_thm fusions so record-time type-instantiated
// payloads are not re-adapted under replay's pointer/name environment.
//
// "Exact" refers to replay faithfulness (no re-adaptation of the
// stored payload). The underlying tactic is LemmaPreserve, which
// installs L on the leaf without whole-context simplify — that shape
// is what the recorded KnownThm anchor expects.
func (n *GoalStackNode) UseLemmaExact(L Prop) {
	leaf := n.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("GoalStackNode.UseLemmaExact: no unsolved leaves remaining "+
			"(section already proved — extra UseLemmaExact call?). Lemma: %s",
			prop.PrintProp(L)) + closedLeafNote(n))
	}
	if !ApplyLemmaPreserveExactWithSource(leaf, L, "") {
		panic(fmt.Sprintf("GoalStackNode.UseLemmaExact: LemmaPreserve failed for lemma %s on goal %s",
			prop.PrintProp(L), prop.PrintProp(leaf.Goal)))
	}
	n.findScript().Do(leaf, CiteKnown(L))
}

// CiteSpecialize is the fused "cite L, then ground it at one witness
// tuple" — UseLemmaExact(L) followed by ONE composite Specialize of the
// hyp that cite just installed, with the hyp located BY CONTENT (the
// added hyp α-equal to L's conclusion — see installedHypIndex) rather
// than by a caller-supplied index. Goal hyp lists are Compare-sorted and
// α-deduped (core.MakeProp), so a freshly installed hyp's index is a
// function of its content relative to the ambient context — unknowable
// at authoring time and shifted by any context edit. The
// locate-by-content removes the index from the authoring surface
// entirely, INCLUDING at absorption sites where the install nets several
// hyps; the recorded proto still carries the resolved concrete index (a
// plain `specialize` ministep), so replay shape and determinism are
// unchanged.
//
// The ∀-source is dropped after grounding (Lean `specialize` /
// Specialize semantics). For a second instance of the same lemma, cite
// it again at that use site — each use is then self-contained, which is
// the cite-at-use discipline this constructor exists to support. Use
// CiteSpecializeKeep to keep the source resident instead.
func (n *GoalStackNode) CiteSpecialize(L Prop, witnesses ...core.Term) {
	n.citeSpecialize(L, false, witnesses...)
}

// CiteSpecializeKeep is CiteSpecialize with the cited ∀-source kept
// resident after grounding (SpecializeKeep semantics) — for the case
// where a following step needs the general form too.
func (n *GoalStackNode) CiteSpecializeKeep(L Prop, witnesses ...core.Term) {
	n.citeSpecialize(L, true, witnesses...)
}

func (n *GoalStackNode) citeSpecialize(L Prop, keep bool, witnesses ...core.Term) {
	n.citeSpecializeRef(L, nil, keep, false, nil, witnesses...)
}

// citeSpecializeRef is citeSpecialize with an optional REFERENCE
// statement: when ref is non-nil, the witness tuple is read in ref's
// stated binder order and permuted onto the installed hyp's ∀-prefix
// (witness_order.go). The modern cite verbs (Cite / By) pass the
// target's raw form as ref; the legacy Action spellings and exported
// CiteSpecialize methods pass nil — positional against the install
// prefix, the recorded-replay semantics. It returns the leaf the install
// left and the installed hypothesis there, before its grounding — the
// node and term a handle that follows the fact to its instance binds to
// — or nil when the install closed the section. exact marks an
// EXPLICIT instance (isExplicitInstance): the author chose its types,
// so it installs as written, where any other polymorphic form is typed
// by its tuple and the goal (witnessTypedForm). listed is what the
// instance's guards may be discharged from (dischargeGuards): the
// facts a fact in hand lists, nil for a cite, which reads the context.
func (n *GoalStackNode) citeSpecializeRef(L Prop, ref Prop, keep, exact bool, listed *_ListedSuppliers, witnesses ...core.Term) (*GoalStackNode, core.Term) {
	if len(witnesses) == 0 {
		panic("GoalStackNode.CiteSpecialize: no witnesses (use UseLemmaExact for a bare cite)")
	}
	leaf := n.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("GoalStackNode.CiteSpecialize: no unsolved leaves remaining "+
			"(section already proved — extra CiteSpecialize call?). Lemma: %s",
			prop.PrintProp(L)) + closedLeafNote(n))
	}
	before := leaf.Goal
	sc := n.findScript()
	// A polymorphic cite is typed by its tuple before it is installed
	// (witness_order.go); the instance is registered so the KnownThm
	// anchor below resolves it. An explicit instance is not retyped: a
	// goal holding the law's constant at another instance alone would
	// carry the author's choice off to it.
	if !exact && ext.PropHasTypeVars(L) {
		if inst := witnessTypedForm(L, witnesses, leaf.Goal); !inst.AlphaEquals(L) {
			L = sc.registerKnownThm(inst)
		}
	}
	// A statement in the standard form is cited as the telescope at the
	// tuple's prefix (prop.PrefixTelescope): the hypotheses about the
	// grounded binders stand ahead, as the guards the discharge below
	// takes from the context, and the rest behind the binders left.
	if telescoped := prop.PrefixTelescope(L, len(witnesses)); !telescoped.Conclusion().AlphaEquals(L.Conclusion()) {
		L = sc.registerKnownThm(telescoped)
	}
	// Install exactly as UseLemmaExact does: replay-exact LemmaPreserve
	// + the recorded KnownThm anchor.
	if !ApplyLemmaPreserveExactWithSource(leaf, L, "") {
		panic(fmt.Sprintf("GoalStackNode.CiteSpecialize: LemmaPreserve failed for lemma %s on goal %s",
			prop.PrintProp(L), prop.PrintProp(leaf.Goal)))
	}
	sc.Do(leaf, CiteKnown(L))
	res := n.unsolvedLeaf(0)
	if res == nil {
		if witnessesNameClosedGoal(ref, witnesses, before.Conclusion()) {
			// Lean's `exact foo a b`: the install closed the goal at the
			// very instance the tuple names — checked against the closed
			// goal, so the tuple is not unchecked text.
			return nil, nil
		}
		panic(fmt.Sprintf("GoalStackNode.CiteSpecialize: cite of %s closed the section; "+
			"witnesses are unused — cite bare instead (Cite(dep) / UseLemmaExact)", prop.PrintProp(L)))
	}
	idx, err := installedHypIndex(before, res.Goal, L)
	if err != nil {
		panic(fmt.Sprintf("GoalStackNode.CiteSpecialize: cannot locate the hyp installed by %s: %v\n(goal after install: %s)\n"+
			"the install rewrote the goal by the fact, or applied it to the conclusion, so the witnesses ground nothing: "+
			"cite it bare to take that, or Have the instance By(fact.At(w…))",
			prop.PrintProp(L), err, prop.PrintProp(res.Goal)))
	}
	installed := res.Goal.Hyp(idx)
	wits := reorderWitnessesToInstall(ref, installed, witnesses)
	spec := Specialize(InstHyp(idx, wits...))
	if keep {
		spec = SpecializeKeep(InstHyp(idx, wits...))
	}
	pre := res.Goal
	sc.Do(res, spec)
	// The ground instance's guards are discharged where the context
	// supplies them (Lean's `f x₀ ‹A›`), from the listed facts alone
	// where listed names them, so a fact stated `∀x. A ⇒ ∃y. …` stands
	// ∃-headed for the Unpack/StripQuant that follows, as its prenex
	// form does.
	if gl := n.unsolvedLeaf(0); gl != nil {
		if gi, err := newHypIndex(pre, gl.Goal); err == nil {
			dischargeGuards(gl, gl.Goal.Hyp(gi), false, rungOpts{}, listed)
		}
	}
	return res, installed
}

// GroundHyp grounds an EXISTING resident ∀-hyp at one witness tuple,
// locating the hyp by content (α-equality against `content`'s term)
// instead of by index — the literal-facts / qpat addressing style. Use
// it where the fact to ground did not just arrive via a cite: a premise
// introduced by StripImp, a claim installed by AssertStep, or a lemma
// installed by a multi-step idiom (LemmaPreserve + TypeInst). The
// ∀-source is dropped after grounding; GroundHypKeep keeps it.
//
// content may be a Prop (its conclusion term is matched) or a Term.
func (n *GoalStackNode) GroundHyp(content any, witnesses ...core.Term) {
	n.groundHyp(content, false, witnesses...)
}

// GroundHypKeep is GroundHyp with the ∀-source kept resident after
// grounding (SpecializeKeep semantics).
func (n *GoalStackNode) GroundHypKeep(content any, witnesses ...core.Term) {
	n.groundHyp(content, true, witnesses...)
}

func (n *GoalStackNode) groundHyp(content any, keep bool, witnesses ...core.Term) {
	t := contentHypTerm("GroundHyp", content)
	leaf := n.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("GoalStackNode.GroundHyp: no unsolved leaves remaining. Content: %s",
			ext.PrintTerm(t)) + closedLeafNote(n))
	}
	idx, err := findHypIndex(leaf.Goal, t)
	if err != nil {
		panic(fmt.Sprintf("GoalStackNode.GroundHyp: %v\n(goal: %s)", err, prop.PrintProp(leaf.Goal)))
	}
	spec := Specialize(InstHyp(idx, witnesses...))
	if keep {
		spec = SpecializeKeep(InstHyp(idx, witnesses...))
	}
	pre := leaf.Goal
	n.findScript().Do(leaf, spec)
	// As on the cite-at-use path: the instance's guards are discharged
	// from the context where it supplies them (Lean's `f x₀ ‹A›`).
	if gl := n.unsolvedLeaf(0); gl != nil {
		if gi, err := newHypIndex(pre, gl.Goal); err == nil {
			dischargeGuards(gl, gl.Goal.Hyp(gi), false, rungOpts{}, nil)
		}
	}
}

// contentHypTerm normalizes GroundHyp's content argument to the hyp
// term to α-match: a Prop contributes its conclusion, a Term itself.
func contentHypTerm(who string, content any) core.Term {
	switch c := content.(type) {
	case core.Prop:
		return c.AsProp().Conclusion()
	case core.Term:
		return c
	case TermLike:
		return c.Core()
	default:
		panic(fmt.Sprintf("%s: content must be Prop or Term; got %T", who, content))
	}
}

// newHypIndex diffs the hyp lists before/after a lemma install and
// returns the index (in `after`) of the single newly-added hyp.
func newHypIndex(before, after Prop) (int, error) {
	added := -1
	for i := 0; i < after.NumHyps(); i++ {
		h := after.Hyp(i)
		if before.HasHyp(h) || before.AnyHyp(h.AlphaEquals) {
			continue
		}
		if added >= 0 {
			return 0, fmt.Errorf("ambiguous: install added more than one hyp (indices %d and %d)", added, i)
		}
		added = i
	}
	if added < 0 {
		return 0, fmt.Errorf("install added no hyp (absorbed by simplification, or already resident)")
	}
	return added, nil
}

// installedHypIndex locates the hyp a cite of `installed` just added,
// among the hyps that appeared between `before` and `after`. It is
// newHypIndex refined by CONTENT: of the newly-added hyps, the one
// α-equal to the cited lemma's conclusion is the installed one.
//
// The refinement exists because "exactly one hyp appeared" is not an
// invariant of a cite. Two shapes routinely break it, and without the
// refinement each forces the author out of the fused cite verb entirely:
//
//   - ∨-ABSORPTION: a clause-shaped goal (`¬A ∨ ¬B ∨ C`, the corpus
//     default at nonneg_real_formal_diff/real_construction after a StripQuant) folds during the
//     install, so the goal's own negated disjuncts land as hyps
//     ALONGSIDE the lemma's. The extra hyps are not from the lemma at
//     all.
//   - ⇔-SPLIT: an install whose normalize splits a biconditional into
//     per-direction clauses nets one hyp per clause.
//
// In both, the lemma's own conclusion is present verbatim among the
// added hyps, so content picks it out unambiguously.
//
// When NO added hyp α-matches the conclusion — the install went through
// LemmaTactic's rewriting path rather than the forward load, so what
// arrived is a derived form, not the lemma — the answer falls back to
// the net-new diff, which is exactly the pre-refinement behavior
// (including its errors: nothing added, or several added with no way to
// tell them apart). This is not a defensive retry papering over a
// failure: the two branches answer the same question about
// structurally different installs, and the diff branch is the only
// available answer when the installed term isn't the cited one.
func installedHypIndex(before, after Prop, installed Prop) (int, error) {
	concl := installed.AsProp().Conclusion()
	found := -1
	for i := 0; i < after.NumHyps(); i++ {
		h := after.Hyp(i)
		if before.HasHyp(h) || before.AnyHyp(h.AlphaEquals) {
			continue
		}
		if !h.AlphaEquals(concl) {
			continue
		}
		if found >= 0 {
			// Two added hyps both α-equal the conclusion is impossible:
			// MakeProp α-dedupes a goal's hyp list.
			return 0, fmt.Errorf(
				"ambiguous: hyps %d and %d both α-match the cited conclusion", found, i)
		}
		found = i
	}
	if found >= 0 {
		return found, nil
	}
	return newHypIndex(before, after)
}

// errAmbiguousHyp is a hyp locate's refusal when two resident hyps
// match what it was asked for.
var errAmbiguousHyp = errors.New("ambiguous")

// alphaHypIndex locates the resident hyp α-equal to t, and errors when
// none is or two are. The apply rung's locate: the dry run reads the
// head and its kernel instance by this spelling, and the commit finds
// the same hypotheses on the real leaf by it — a hyp that is t only up
// to normal form (a premise's clause form beside its stated form, a
// disjunction beside the implication) is another hypothesis, on which
// the commit's next step would be the wrong one.
func alphaHypIndex(goal Prop, t core.Term) (int, error) {
	found := -1
	for i := range goal.NumHyps() {
		if goal.Hyp(i).AlphaEquals(t) {
			if found >= 0 {
				return 0, fmt.Errorf("%w: hyps %d and %d both α-match %s", errAmbiguousHyp, found, i, ext.PrintTerm(t))
			}
			found = i
		}
	}
	if found < 0 {
		return 0, fmt.Errorf("no resident hyp α-matches %s", ext.PrintTerm(t))
	}
	return found, nil
}

// findHypIndex locates the resident hyp α-equal to t — or, when none
// is, the one that is t up to pre-CNF normal form (binder-block order,
// equation orientation, disjunct order: the representation choices
// Normalize makes and an author's spelling need not). A resident hyp
// that came through the normalizer has its ∃/∀ blocks sorted, so
// `a.Hyp("∃B N. …")` must still find the resident `∃N.∃B.…`.
func findHypIndex(goal Prop, t core.Term) (int, error) {
	if idx, err := alphaHypIndex(goal, t); err == nil || errors.Is(err, errAmbiguousHyp) {
		return idx, err
	}
	found := -1
	normT := prop.Rhs(prop.PreCNFNormalizeTerm(t))
	for i := range goal.NumHyps() {
		if prop.Rhs(prop.PreCNFNormalizeTerm(goal.Hyp(i))).AlphaEquals(normT) {
			if found >= 0 {
				return 0, fmt.Errorf("%w: hyps %d and %d both match %s up to normal form", errAmbiguousHyp, found, i, ext.PrintTerm(t))
			}
			found = i
		}
	}
	if found < 0 {
		return 0, fmt.Errorf("no resident hyp α-matches %s", ext.PrintTerm(t))
	}
	return found, nil
}

// Rewrite is the idiom for "rewrite by def thm d whose obligation is
// discharged by axiom-def expansion of const c" — emits as `LeanRw(d)`
// then `AxiomDefStep(c)`.
//
// Routes the first step through ApplyLeanRwExactWithSource because emit
// builds this call from an already-recorded DetailedProofProto LeanRw payload.
// Re-running adaptive lemma selection here can choose a different rewrite
// result than the stored ministep.
func (n *GoalStackNode) Rewrite(d Prop, c Term) {
	leaf := n.unsolvedLeaf(0)
	if leaf == nil {
		panic(fmt.Sprintf("GoalStackNode.Rewrite: no unsolved leaves remaining "+
			"(section already proved — extra Rewrite call?). LeanRw: %s",
			prop.PrintProp(d)) + closedLeafNote(n))
	}
	if !ApplyLeanRwExactWithSource(leaf, d, "") {
		panic(fmt.Sprintf("GoalStackNode.Rewrite: ApplyLeanRwExactWithSource failed for lemma %s on goal %s",
			prop.PrintProp(d), prop.PrintProp(leaf.Goal)))
	}
	n.findScript().Do(leaf, AxiomDefStep(c))
}

// Do applies a Step to this section's first unsolved leaf. The
// node-method form of `Script.Do(focus, step)` — drops the
// redundant `<section>` argument and the `ctx.` prefix at the call
// site, so emitted member bodies read uniformly as
// `<section>.CiteKnown(...)` / `<section>.Rewrite(...)` / `<section>.Do(<step>)`
// instead of mixing fluent node methods with `ctx.Do(<section>, ...)`.
//
// Runtime semantics is identical to Script.Do: each Step's applyAction
// runs against the node's section root via the script back-pointer.
// Returns the receiver for any chain that wants to continue with
// further `.Do(...)` calls, though most emit usage is a single
// `<section>.Do(<step>)` per line.
func (n *GoalStackNode) Do(step Action) *GoalStackNode {
	traceStep("Do", traceStepLabel(step), n, func() {
		step.applyAction(n.findScript(), n)
	})
	return n
}

func (n *GoalStackNode) ProofSteps() []*GoalStackNode {
	Assert(n.Proved())
	proof := []*GoalStackNode{n}
	for n.proofAction.next != nil {
		proof = append(proof, n.proofAction.next)
		n = n.proofAction.next
	}
	return proof
}

// TryExpandPlan runs the complete action on a clone of n and returns an
// ExpansionPlan capturing the full result. The original node is not mutated.
// The plan can later be applied to the real node via Commit.
func TryExpandPlan(n *GoalStackNode, action Macro) (*ExpansionPlan, bool) {
	Assert(n.miniStep == nil && !n.Goal.Proved())
	clone := &GoalStackNode{Goal: n.Goal}
	if !action.Apply(clone) {
		return nil, false
	}
	return &ExpansionPlan{expanded: clone}, true
}

// Commit transplants the fully-expanded subtree from the plan onto n.
//
// Returns false (rather than asserting) when n is not a valid commit target —
// already expanded (a tactic was applied, miniStep set) or already proved.
// This makes the precondition a clean caller contract: user entry points
// (ApplyStep / BatchApply / CommitPlan) translate a false return into a typed
// "goal is not an open leaf" error instead of letting a stale goal_id — e.g.
// an agent retrying a goal, or a retry after a recovered panic left the
// session pointing at a now-internal node — trip an assertion ("Should not
// happen.") and a second, opaque panic. Internal callers always Commit onto
// fresh nodes, so they never observe the false path.
func (n *GoalStackNode) Commit(plan *ExpansionPlan) bool {
	if n.miniStep != nil || n.Goal.Proved() {
		return false
	}
	if plan == nil || plan.expanded == nil || plan.expanded.miniStep == nil {
		return false
	}
	e := plan.expanded
	n.miniStep = e.miniStep
	n.subGoals = e.subGoals
	n.provedThm = e.provedThm
	n.children = e.children
	// Re-parent direct children to point to n (deeper descendants are correct
	// because they point to these same child objects).
	for _, c := range n.children {
		c.parent = n
	}
	if n.Proved() {
		n.updateUpwards()
	}
	return true
}

// MakeExpansionPlan wraps an already-expanded clone as an ExpansionPlan.
// Used by the engine to build plans from tactic application results.
func MakeExpansionPlan(expanded *GoalStackNode) *ExpansionPlan {
	return &ExpansionPlan{expanded: expanded}
}

// tryStep applies a single ministep to a goal and returns the resulting
// subgoals. Used by search-phase Try* functions that need to inspect what
// children a single ministep produces, without building a full ExpansionPlan.
func tryStep(goal Prop, step _Step) (*SubGoals, bool) {
	subGoals := step.apply(goal)
	if subGoals == nil {
		return nil, false
	}
	return subGoals, true
}

// Step-by-step replay tracing. When a trace writer is installed (see
// SetReplayTrace), every GoalStackNode.Apply / .Do logs the action or
// ministep it ran, the goal it ran on, and the resulting leaf state.
// This is the debugging counterpart to the assertion-only verification
// the replay path normally does: it lets a caller watch a member's Build
// execute one step at a time and see exactly where the goal shape stops
// matching expectations.
//
// The single-entry probe (library/integrity/gates TestZZRecurateProbe)
// wires this to os.Stderr when the XUGO_REPLAY_TRACE env var is set,
// so a single member can be traced with:
//
//	XUGO_RECURATE_PROBE=<NAME> XUGO_REPLAY_TRACE=1 go test -run TestZZRecurateProbe -v ./library/integrity/gates/
var (
	traceMu sync.Mutex
	traceW  io.Writer
)

// SetReplayTrace directs replay step tracing to w; pass nil to disable.
// Safe to call concurrently, though the probe drives one proof so
// output stays readable.
func SetReplayTrace(w io.Writer) {
	traceMu.Lock()
	traceW = w
	traceMu.Unlock()
}

func traceWriter() io.Writer {
	traceMu.Lock()
	defer traceMu.Unlock()
	return traceW
}

// traceStep wraps the mutating body of an Apply / Do call: it logs the
// step label and the pre-step goal, runs body, then logs the resulting
// leaf state of n. A no-op (just runs body) when tracing is disabled.
func traceStep(kind, label string, n *GoalStackNode, body func()) {
	w := traceWriter()
	if w == nil {
		body()
		return
	}
	fmt.Fprintf(w, "[%s] %s\n      on: %s\n", kind, label, traceGoalLine(n.Goal))
	body()
	fmt.Fprintf(w, "     ==> %s\n", traceResult(n))
}

func traceGoalLine(p Prop) string {
	return strings.Join(strings.Fields(prop.PrintProp(p)), " ")
}

func traceResult(n *GoalStackNode) string {
	if n.Proved() {
		return "PROVED"
	}
	leaves := n.UnsolvedLeaves()
	parts := make([]string, len(leaves))
	for i, l := range leaves {
		parts[i] = traceGoalLine(l.Goal)
	}
	return fmt.Sprintf("%d unsolved leaf/leaves: [ %s ]",
		len(leaves), strings.Join(parts, " | "))
}

func traceStepLabel(step Action) string {
	if s, ok := step.(fmt.Stringer); ok {
		return s.String()
	}
	return fmt.Sprintf("%T", step)
}
