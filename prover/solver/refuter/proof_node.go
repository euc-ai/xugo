/**
 * File: proof_node.go
 *
 * Defines node types for representing proof structures in a directed acyclic graph.
 *
 * Key interfaces and structures:
 * - _ProofNode: Interface for all nodes in the proof DAG
 *   Methods:
 *   - Children(): Returns child nodes
 *   - replaceChild(int, _ProofNode): Replaces a specific child node
 *   - clone(): Creates a shallow copy of the node
 *
 * - _DeduceStep: Represents a deduction step (factoring or resolution)
 *   Fields:
 *   - clauseThm: The derived clause theorem
 *   - children: Child nodes that are premises for this step
 *   Methods:
 *   - addChild(child): Adds a premise to the deduction
 *   - conclClause(): Returns the conclusion clause
 *
 * - _MergeStep: Represents a merge operation from divide-and-conquer
 *   Fields:
 *   - clauseThm: The resulting merged clause theorem
 *   - division: Information about the division structure
 *   - states: Refutation states for each sub-problem
 *   - divisibleChild: Node for the divisible parent clause
 *   - subProofChildren: Nodes for each divided clause's proof
 *   Methods:
 *   - setSubProofChild(i, child): Sets a sub-proof for a divided component
 *
 * - _ClauseLeaf: Represents a leaf node in the proof (base clause)
 *   Fields:
 *   - clause: The clause represented by this leaf
 *   - leafType: Type indicator (original, assumed, or dangling)
 *   Methods:
 *   - isOriginal(), isAssumed(), isDangling(): Type checking
 *
 * - _ProofCache: Wrapper for storing complete proof structures in cache
 */

package refuter

import (
	"github.com/euc-ai/xugo/ext/clause"
)

// Interface of a node in the proof DAG.
// It can be:
// - a deduce step
// - a merge step
// - a leaf, which is a clause
// ProofCache also satisfies this interface for convenience,
// but it never shows up in a DAG.
type _ProofNode interface {
	Children() []_ProofNode

	// Replaces the i-th child with a new step.
	replaceChild(int, _ProofNode)

	// Shallow clone, only copies the payload of the node.
	// The children are not recursively cloned.
	clone() _ProofNode
}

// Deduce step from either factoring or resolution.
type _DeduceStep struct {
	clauseThm *ClauseThm
	children  []_ProofNode
}

func makeDeduceStep(clauseThm *ClauseThm) *_DeduceStep {
	Assert(clauseThm != nil && clauseThm.NumHyps() <= 2)
	return &_DeduceStep{clauseThm: clauseThm}
}

func (s *_DeduceStep) Children() []_ProofNode { return s.children }

func (s *_DeduceStep) addChild(child _ProofNode) {
	s.children = append(s.children, child)
}

func (s *_DeduceStep) replaceChild(i int, child _ProofNode) {
	Assert(i < len(s.children))
	s.children[i] = child
}

func (s *_DeduceStep) clone() _ProofNode { return makeDeduceStep(s.clauseThm) }

// _MergeStep represents a merge operation in a proof, combining multiple sub-proofs
// that were derived from a divided clause.
// It is a crucial component in the divide-and-conquer strategy of automated theorem proving,
// where a complex problem is split into simpler sub-problems, solved individually,
// and then recombined to form a complete proof.
type _MergeStep struct {
	// The theorem produced by merging sub-proofs
	clauseThm *ClauseThm

	// Detailed information about how the original clause was divided
	// Includes references to the divided clauses and the merge function
	division *clause.ClauseDivision

	// States for each divided component, preserving the same order as the divided clauses
	states []*_RefuteState

	// The proof node for the divisible clause (parent clause)
	// Can be either a derived step or an original assumption
	divisibleChild _ProofNode

	// Proof nodes for each of the divided components
	// Each holds the complete proof for one of the divided clauses
	// Order matches division.DividedClauses
	subProofChildren []_ProofNode
}

func makeMergeStep(
	clauseThm *ClauseThm,
	division *clause.ClauseDivision,
	states []*_RefuteState) *_MergeStep {
	n := len(division.DividedClauses)
	// For bool ground var split (i.e. b₀ = ⊤ ∨ b₀ = ⊥),
	// RefutingThm has n hyps (no divisible clause hypothesis).
	// For regular clause divisions, RefutingThm has n+1 hyps.
	Assert(
		clauseThm != nil &&
			clauseThm.IsRefuted() &&
			division != nil &&
			len(states) == n &&
			(division.RefutingThm.NumHyps() == n+1 ||
				division.RefutingThm.NumHyps() == n))
	return &_MergeStep{
		clauseThm:        clauseThm,
		division:         division,
		states:           states,
		subProofChildren: make([]_ProofNode, len(states))}
}

func (s *_MergeStep) Children() []_ProofNode {
	if s.divisibleChild == nil {
		return s.subProofChildren
	}
	return append([]_ProofNode{s.divisibleChild}, s.subProofChildren...)
}

func (s *_MergeStep) setSubProofChild(i int, child _ProofNode) {
	Assert(i < len(s.subProofChildren))
	s.subProofChildren[i] = child
}

func (s *_MergeStep) replaceChild(i int, child _ProofNode) {
	Assert(i == 0)
	s.divisibleChild = child
}

func (s *_MergeStep) clone() _ProofNode {
	return makeMergeStep(s.clauseThm, s.division, s.states)
}

type _ClauseLeafType int

const (
	// the original init clause for the whole problem
	origInit _ClauseLeafType = iota
	// the assumed init clause that is inherited from the upper level
	assumed
	// the dangling clause that needs to be deduced
	// this kind of leaf should only exist in intermediate steps
	dangling
)

// The clause leaf that can be consumed for deduce / merge steps.
type _ClauseLeaf struct {
	clause   *Clause
	leafType _ClauseLeafType
}

func (*_ClauseLeaf) Children() []_ProofNode { return nil }

func (*_ClauseLeaf) replaceChild(int, _ProofNode) { panic("Should not call.") }

func (l *_ClauseLeaf) clone() _ProofNode { return &_ClauseLeaf{l.clause, l.leafType} }

func (l *_ClauseLeaf) isOriginal() bool { return l.leafType == origInit }

func (l *_ClauseLeaf) isAssumed() bool { return l.leafType == assumed }

func (l *_ClauseLeaf) isDangling() bool { return l.leafType == dangling }

// A cache of a finished proof.
type _ProofCache struct{ proof *_ProofDAG }

func makeProofCache(p *_ProofDAG) *_ProofCache { return &_ProofCache{p} }

func (*_ProofCache) Children() []_ProofNode { return nil }

func (*_ProofCache) replaceChild(int, _ProofNode) { panic("Should not call.") }

func (*_ProofCache) clone() _ProofNode { panic("Should not call.") }
