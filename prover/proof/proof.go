// proof.go — the Proof (a script's section roots) and the wire form of a
// closed section: DetailedProofProto, the ministep tree in preorder, which
// a session records and emit renders as a family member
// (library/emit). Nothing decodes a recorded tree back into runnable
// steps: a member replays as Go.

// Package proof is the proof calculus: the goal state, the Step, Macro
// and Action layers a goal is transformed by, the record a closed
// section leaves, and the surface a chapter's proof is written in —
// Script, Fact, Cite, Derive, Calc.
//
// It is one package by necessity: the Action world is closed — applying
// an action is unexported, and each action has its tag in proof.proto —
// and that closure is what record and replay rest on. The solvers under
// prover/solver sit below the calculus; a kit such as prover/algebra
// sits above it and produces actions. Nothing here imports library/:
// what the calculus needs from the corpus is installed into it at
// startup. prover/README.md has the layering.
package proof

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// A proof is a sequence of proof sections.
// Each section has a node tree, whose root is stored here.
type Proof struct{ sectionRoots []*GoalStackNode }

func (proof *Proof) Length() int { return len(proof.sectionRoots) }

func (proof *Proof) Goal() Prop {
	return utils.Last(proof.sectionRoots).Goal
}

func (proof *Proof) SectionIter() iter.Seq[*GoalStackNode] {
	return slices.Values(proof.sectionRoots)
}

// SectionThms returns each section root's promised Thm, in section
// creation order: the *Proof a member's Build returns records every
// section the Script opened, so a replay runner can force the proof in
// parts.
// (TypeDefExpand outputs and other structurally-recovered Thms are not
// section roots; they are reached transitively when the sections that
// cite them force.)
func (proof *Proof) SectionThms() []Thm {
	out := make([]Thm, 0, len(proof.sectionRoots))
	for _, root := range proof.sectionRoots {
		out = append(out, root.PromisedThm())
	}
	return out
}

func (proof *Proof) AddSection(goal Prop) *GoalStackNode {
	n := CreateGoalStack(goal)
	proof.sectionRoots = append(proof.sectionRoots, n)
	return n
}

// ---------------------------------------------------------------------------
// In-memory → wire-form serializers
// ---------------------------------------------------------------------------

func (n *GoalStackNode) miniStepProto(b *ext.PoolBuilder) *StepProto {
	Assert(n.miniStep != nil)
	subGoals := utils.MapSlice(
		n.children,
		func(c *GoalStackNode) *ext.HolPropProto {
			return b.PropRef(c.Goal)
		})
	return &StepProto{
		Goal:     b.PropRef(n.Goal),
		SubGoals: subGoals,
		Step:     n.miniStep.proto(b),
	}
}

// DetailedProofProto serializes the nodes in the proof tree in preorder
// traversal. Each node's miniStep is emitted as a StepProto. Works
// off the miniStep tree directly and handles arbitrary tree shapes
// including multi-branch tactics.
//
// Returns nil if the node is not fully proved.
func (n *GoalStackNode) DetailedProofProto() *DetailedProofProto {
	if !n.Proved() {
		return nil
	}
	b := ext.NewPoolBuilder()
	steps := utils.MapSlice(
		n.preorderTraverse(),
		func(n *GoalStackNode) *StepProto {
			Assert(n.miniStep != nil)
			return n.miniStepProto(b)
		})
	return &DetailedProofProto{Steps: steps, Pool: b.Pool()}
}

// PolymorphicSourceKeys returns a slice parallel to
// DetailedProofProto().Steps, carrying — at each index whose ministep is a
// Lemma or LeanRw whose pre-adaptation form was a polymorphic registry
// lemma — the key of that pre-adaptation form (lemmaSourceKey). KnownThm
// and TypeInst ministeps contribute their sourceEntryKey through the same
// channel: the registry identity the engine's auto-match / sourceKey-
// channel close resolved at apply time, stamped so emit's leaf resolution
// reads the entry directly instead of re-deriving it from the session-form
// payload. All other indices are empty.
//
// A registry entry is keyed by the AlphaKey of its normalized statement.
// At session time, applyLemma / ApplyLemma / applyLeanRw / ApplyLeanRw may
// run tryAdaptLemmaTypes to substitute the lemma's type-vars to fit the
// goal's type context; the resulting adapted prop is what runtime needs
// (so binders carry the goal's concrete types for downstream
// `instantiate` / rewrite passes) and is what gets recorded in
// StepProto.lemma / lean_rw on the wire. But the dep should resolve
// against the polymorphic source, not the specialization — that's the
// statement whose key an entry actually carries.
//
// The polymorphic source itself is not serialized into the proto (no
// schema change). Instead, the engine's emit (engine/emit_section.go,
// polymorphicSourceLeafResolver) reads this slice and resolves the
// step's external leaf through the override key where it's non-empty,
// falling back to the proto-based Normalize+AlphaKey lookup on the
// recorded payload otherwise (which is correct when no adaptation
// happened — the recorded form IS the polymorphic source).
//
// Returns nil if the node is not fully proved.
func (n *GoalStackNode) PolymorphicSourceKeys() []core.PropKey {
	if !n.Proved() {
		return nil
	}
	return utils.MapSlice(
		n.preorderTraverse(),
		func(node *GoalStackNode) core.PropKey {
			Assert(node.miniStep != nil)
			switch step := node.miniStep.(type) {
			case _LemmaTactic:
				return step.polymorphicSourceKey
			case _LemmaPreserveTactic:
				return step.polymorphicSourceKey
			case _LeanRwTactic:
				return step.polymorphicSourceKey
			case _KnownThmStep:
				return step.sourceEntryKey
			case _TypeInstStep:
				return step.sourceEntryKey
			}
			return ""
		})
}

// ByPremiseSourceKeys returns a slice parallel to
// DetailedProofProto().Steps: at each index whose ministep is a By, a
// slice parallel to that ByProto's premises, carrying the entry each
// session key premise was loaded from (ByPremiseSpec.SourceKey) and ""
// for every other premise; nil at every other index.
//
// A named premise's claim child is implied by the premise list, so emit
// names the premise by its recorded install alone, and an explicit type
// instance's install has no entry at its own key. The By record does
// not carry these keys (no schema change); the engine's emit
// (engine/emit_section.go, polymorphicSourceLeafResolver) reads them to
// resolve such an install through the entry it came from.
//
// Returns nil if the node is not fully proved.
func (n *GoalStackNode) ByPremiseSourceKeys() [][]core.PropKey {
	if !n.Proved() {
		return nil
	}
	return utils.MapSlice(
		n.preorderTraverse(),
		func(node *GoalStackNode) []core.PropKey {
			step, ok := node.miniStep.(_ByStep)
			if !ok {
				return nil
			}
			return utils.MapSlice(step.premises, func(p byPremise) core.PropKey { return p.sourceKey })
		})
}
