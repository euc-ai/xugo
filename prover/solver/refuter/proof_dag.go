package refuter

import (
	"sync"

	"github.com/euc-ai/xugo/utils"
)

type _ProofDAG struct {
	// The root of the DAG can be either a deduce step or a merge step.
	root _ProofNode

	// The clause thm with hyps from the leaves of the DAG.
	// It's always a refuted thm which conclusion is ⊥.
	// It's updated during the reconstruction along with the growth of the DAG.
	clauseThm *ClauseThm

	// The nodes are keyed by their pointers, not content.
	nodeSet utils.Set[_ProofNode]

	sync.RWMutex
}

func emptyProof() *_ProofDAG {
	return &_ProofDAG{nodeSet: utils.EmptySet[_ProofNode]()}
}

func (dag *_ProofDAG) Root() _ProofNode {
	dag.RLock()
	defer dag.RUnlock()
	Assert(dag.clauseThm != nil)
	return dag.root
}

func (dag *_ProofDAG) ClauseThm() *ClauseThm {
	dag.RLock()
	defer dag.RUnlock()
	return dag.clauseThm
}

// Returns if there is any clause leaf in the DAG that satisfies
// the given predicate f.
// This method should be called under the read lock.
func (dag *_ProofDAG) anyLeaf(f func(*_ClauseLeaf) bool) bool {
	for node := range dag.nodeSet {
		if node, ok := node.(*_ClauseLeaf); ok && f(node) {
			return true
		}
	}
	return false
}

// Deeply clones the DAG, maintaining its structure.
//
// The locking strategy here is intentionally fine-grained to prevent deadlocks.
// A proof DAG is built within a write lock in `_RefuteState.setProof`. During this
// build process, the builder might need to clone another existing DAG (e.g., from a cache).
// If we held a read lock for the entire duration of this `clone` method, it could lead
// to an AB-BA deadlock, where two threads are building proofs, each holding a write
// lock on their new DAG and waiting for a read lock on the other's cached DAG.
//
// By locking only to copy the pointers/slices we need and then immediately unlocking,
// we minimize the lock contention window. The rest of the cloning process operates on
// these local copies. This is safe because the source DAG is effectively immutable
// once it has been constructed and cached.
func (dag *_ProofDAG) clone() *_ProofDAG {
	dag.RLock()
	Assert(dag.root != nil && dag.clauseThm != nil)
	// Copy shared data to local variables under read lock.
	root := dag.root
	clauseThm := dag.clauseThm
	originalNodeSet := dag.nodeSet
	dag.RUnlock()

	// map of all proof steps to their clone.
	clones := make(map[_ProofNode]_ProofNode, len(originalNodeSet))
	// node set for the new proof DAG.
	nodeSet := make(utils.Set[_ProofNode], len(clones))

	for node := range originalNodeSet {
		clone := node.clone()
		clones[node] = clone
		nodeSet.Add(clone)
	}

	for node, clone := range clones {
		switch node := node.(type) {
		case *_DeduceStep:
			children := make([]_ProofNode, len(node.children))
			for i, child := range node.children {
				children[i] = clones[child]
				Assert(children[i] != nil)
			}
			clone.(*_DeduceStep).children = children
		case *_MergeStep:
			children := make([]_ProofNode, len(node.subProofChildren))
			for i, child := range node.subProofChildren {
				children[i] = clones[child]
				Assert(children[i] != nil)
			}
			clone := clone.(*_MergeStep)
			clone.subProofChildren = children
			if node.divisibleChild != nil {
				clone.divisibleChild = clones[node.divisibleChild]
				Assert(clone.divisibleChild != nil)
			}
		case *_ClauseLeaf:
		default:
			panic("Wrong node type.")
		}
	}
	return &_ProofDAG{
		root:      clones[root],
		clauseThm: clauseThm,
		nodeSet:   nodeSet}
}
