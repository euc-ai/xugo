/**
 * File: proof_builder.go
 *
 * ProofBuilder is responsible for constructing complete, immutable proof DAGs.
 * It takes deduction records and initial clauses as input, and builds a fully
 * expanded proof tree by recursively resolving all dangling references.
 *
 * The main entry point is Build(rootNode), which returns a complete _ProofDAG
 * that is ready for validation and use.
 */

package refuter

import "github.com/euc-ai/xugo/utils"

// _ProofContext provides the necessary context for building proofs.
// It abstracts away the details of the refutation state.
type _ProofContext struct {
	isOrigInitClause   func(*Clause) bool
	isAssumptionClause func(*Clause) bool
	isInitClause       func(*Clause) bool
	findInitClause     func(*Clause) *Clause
	lookUpDeduceStep   func(*Clause) *_DeduceStep
}

// _ProofBuilder constructs complete proof DAGs from root nodes.
type _ProofBuilder struct {
	// Context for determining clause types
	_ProofContext

	// The proof being built
	proof *_ProofDAG

	// Tracks which nodes we've already expanded to avoid cycles
	expandedNodes utils.Set[_ProofNode]
}

// newProofBuilder creates a new ProofBuilder with the given context.
func newProofBuilder(
	ctx _ProofContext,
	proof *_ProofDAG,
) *_ProofBuilder {
	return &_ProofBuilder{
		_ProofContext: ctx,
		proof:         proof,
		expandedNodes: utils.EmptySet[_ProofNode](),
	}
}

// build constructs a complete proof DAG from the given root node.
// It recursively expands all dangling references and returns an immutable proof.
// This method assumes that the caller holds the lock on b.proof.
func (b *_ProofBuilder) build(root _ProofNode) {
	if b.proof.root != nil {
		Assert(b.proof.clauseThm != nil)
		return
	}

	// Initialize the proof with the root node
	b.initializeRoot(root)

	// Expand all dangling references recursively to build the graph structure
	b.proof.root = b.expand(b.proof.root)

	// Rebuild nodeSet from the final graph structure to remove intermediate nodes
	b.rebuildNodeSet()

	// Compute the final theorem from the complete graph structure
	b.proof.clauseThm = b.computeFinalThm(b.proof.root)

	// Align hypotheses with initial clauses
	b.alignHypotheses()
}

// initializeRoot sets up the initial proof structure based on the root node type.
func (b *_ProofBuilder) initializeRoot(root _ProofNode) {
	switch root := root.(type) {
	case *_DeduceStep:
		b.initializeFromDeduction(root)
	case *_MergeStep:
		b.initializeFromMerge(root)
	case *_ProofCache:
		b.initializeFromCache(root)
	default:
		panic("Unknown root node type")
	}
}

// expand recursively expands a proof node, resolving all dangling references.
// This is the core recursive function that builds the complete proof tree.
func (b *_ProofBuilder) expand(node _ProofNode) _ProofNode {
	// Avoid expanding the same node twice
	if b.expandedNodes.Has(node) {
		return node
	}
	b.expandedNodes.Add(node)

	switch n := node.(type) {
	case *_ClauseLeaf:
		return b.expandLeaf(n)
	case *_DeduceStep:
		return b.expandDeduceStep(n)
	case *_MergeStep:
		return b.expandMergeStep(n)
	default:
		return node
	}
}

// expandLeaf expands a clause leaf node.
// If it's dangling and we have a deduction record for it, expand it.
// Otherwise, return it as-is.
func (b *_ProofBuilder) expandLeaf(leaf *_ClauseLeaf) _ProofNode {
	if !leaf.isDangling() {
		return leaf
	}

	// Look up the deduction step for this dangling clause
	step := b.lookUpDeduceStep(leaf.clause)
	if step == nil {
		// No deduction found - this leaf remains dangling
		return leaf
	}

	// Clone the step to avoid modifying the original
	expandedStep := step.clone().(*_DeduceStep)

	// Create child nodes for the step's hypotheses
	for h := range expandedStep.clauseThm.HypClauseIter() {
		child := b.createLeafNode(h)
		expandedStep.addChild(child)
		b.proof.nodeSet.Add(child)
	}

	b.proof.nodeSet.Add(expandedStep)

	// Recursively expand the new step
	return b.expand(expandedStep)
}

// expandDeduceStep recursively expands all children of a deduction step.
func (b *_ProofBuilder) expandDeduceStep(step *_DeduceStep) _ProofNode {
	// Clone to avoid modifying the original
	expanded := step.clone().(*_DeduceStep)
	expanded.children = make([]_ProofNode, len(step.children))

	// Recursively expand each child
	for i, child := range step.children {
		expanded.children[i] = b.expand(child)
	}

	b.proof.nodeSet.Add(expanded)
	return expanded
}

// expandMergeStep recursively expands all children of a merge step.
func (b *_ProofBuilder) expandMergeStep(step *_MergeStep) _ProofNode {
	// Clone to avoid modifying the original
	expanded := step.clone().(*_MergeStep)

	// Expand the divisible child (nil for bool ground var split)
	if step.divisibleChild != nil {
		expanded.divisibleChild = b.expand(step.divisibleChild)
	}

	// Expand each sub-proof child
	expanded.subProofChildren = make([]_ProofNode, len(step.subProofChildren))
	for i, child := range step.subProofChildren {
		expanded.subProofChildren[i] = b.expand(child)
	}

	b.proof.nodeSet.Add(expanded)
	return expanded
}

// createLeafNode creates a leaf node with the appropriate type based on the clause.
func (b *_ProofBuilder) createLeafNode(clause *Clause) *_ClauseLeaf {
	if b.isOrigInitClause(clause) {
		return &_ClauseLeaf{clause, origInit}
	}
	if b.isAssumptionClause(clause) {
		return &_ClauseLeaf{clause, assumed}
	}
	return &_ClauseLeaf{clause, dangling}
}

// initializeFromDeduction initializes the proof from a deduction step root.
func (b *_ProofBuilder) initializeFromDeduction(root *_DeduceStep) {
	// Clone to avoid modifying the original
	root = root.clone().(*_DeduceStep)
	Assert(root.clauseThm != nil && root.clauseThm.IsRefuted())

	// Create leaf nodes for all hypotheses
	for h := range root.clauseThm.HypClauseIter() {
		leaf := b.createLeafNode(h)
		root.addChild(leaf)
		b.proof.nodeSet.Add(leaf)
	}

	Assert(root.clauseThm.NumHyps() == len(root.Children()))
	b.proof.root = root
	b.proof.nodeSet.Add(root)
	b.proof.clauseThm = root.clauseThm
}

// initializeFromMerge initializes the proof from a merge step root.
func (b *_ProofBuilder) initializeFromMerge(root *_MergeStep) {
	// Clone to avoid modifying the original
	root = root.clone().(*_MergeStep)
	Assert(root.clauseThm != nil && root.clauseThm.IsRefuted())

	// Set up the divisible child.
	// For bool ground var split (i.e. b₀ = ⊤ ∨ b₀ = ⊥), the divisible clause
	// is a tautology with no hypothesis in RefutingThm, so no child is needed.
	if root.division.RefutingThm.NumHyps() > len(root.division.DividedClauses) {
		if b.isOrigInitClause(root.division.DivisibleClause) {
			root.divisibleChild = &_ClauseLeaf{
				root.division.DivisibleClause, origInit}
		} else {
			Assert(!b.isAssumptionClause(root.division.DivisibleClause))
			root.divisibleChild = &_ClauseLeaf{
				root.division.DivisibleClause, dangling}
		}
		b.proof.nodeSet.Add(root.divisibleChild)
	}

	// Link sub-proofs
	for i, state := range root.states {
		subproof := state.proof.clone()
		root.setSubProofChild(i, subproof.root)
		for n := range subproof.nodeSet {
			b.proof.nodeSet.Add(n)
		}
	}

	Assert(root.division.RefutingThm.NumHyps() == len(root.Children()))
	b.proof.root = root
	b.proof.nodeSet.Add(root)
	b.proof.clauseThm = root.clauseThm
}

// initializeFromCache initializes the proof from a cached proof.
func (b *_ProofBuilder) initializeFromCache(cache *_ProofCache) {
	// Deep clone the cached proof
	proofClone := cache.proof.clone()
	b.proof.root = proofClone.root
	b.proof.clauseThm = proofClone.clauseThm

	// Reconcile leaf types with current context
	b.reconcileLeafTypes(proofClone)

	// A cached merge root may have a stale local theorem after reconciliation.
	// The proof-wide final theorem is still valid for the unique root occurrence.
	if root, ok := b.proof.root.(*_MergeStep); ok {
		root.clauseThm = b.proof.clauseThm
	}
}

// adjusts leaf node types based on the current context.
//
// WHY THIS IS NECESSARY:
// A cached proof was constructed in a specific context with its own set of assumption clauses.
// When we load this cached proof into a new refutation state, the context has changed:
//   - Some clauses that were "assumed" in the cached context might now be "dangling"
//     (meaning they need to be proved by deduction steps in the current context)
//   - Some clauses that were "dangling" in the cached context might now be "assumed"
//     (meaning they are given as assumptions in the current context)
//
// The leaf type (original/assumed/dangling) is not an inherent property of the clause itself,
// but rather depends on the context in which the proof is being used. Therefore, when we
// reuse a cached proof, we must adapt these leaf types to match the current context.
//
// EXAMPLE:
// Cached proof was built with assumptions {A, B}, where C was dangling (to be proved).
// Current context has assumptions {A, C}, where B needs to be proved.
// We must change: B from "assumed" to "dangling", C from "dangling" to "assumed".
//
// This complexity is inherent to the proof caching mechanism and cannot be eliminated
// without losing the ability to reuse proofs across different contexts.
func (b *_ProofBuilder) reconcileLeafTypes(proofClone *_ProofDAG) {
	for node := range proofClone.nodeSet {
		if len(node.Children()) == 0 {
			continue
		}
		b.proof.nodeSet.Add(node)

		for i, child := range node.Children() {
			b.proof.nodeSet.Add(child)
			if leaf, ok := child.(*_ClauseLeaf); ok {
				if newLeaf := b.reconcileLeaf(leaf); newLeaf != leaf {
					node.replaceChild(i, newLeaf)
					b.proof.nodeSet.Add(newLeaf)
					delete(b.proof.nodeSet, child)
				}
			}
		}
	}

	Assert(len(b.proof.nodeSet) == len(proofClone.nodeSet))
}

// reconcileLeaf adjusts a single leaf's type based on the current context.
// It determines whether a leaf should be marked as original, assumed, or dangling
// based on the current refutation state's context.
func (b *_ProofBuilder) reconcileLeaf(leaf *_ClauseLeaf) *_ClauseLeaf {
	// CASE 1: Original leaves (from the very beginning of the problem) never change
	if leaf.isOriginal() {
		Assert(b.isOrigInitClause(leaf.clause))
		return leaf
	}

	// CASE 2: Special handling for merge step leaves
	// In merge steps, some assumption clauses from sub-proofs don't appear
	// in the final theorem's hypotheses. These are internal to the sub-proof
	// and don't need reconciliation.
	if !b.proof.clauseThm.HasHypClause(leaf.clause) {
		return leaf
	}

	// CASE 3: Context-dependent reconciliation
	// The leaf's type depends on whether it's an assumption in the current context

	if leaf.isAssumed() && !b.isAssumptionClause(leaf.clause) {
		// Was treated as given (assumed) when the cached proof was created,
		// but in our current context, we need to prove it (dangling)
		return &_ClauseLeaf{leaf.clause, dangling}
	}

	if leaf.isDangling() && b.isAssumptionClause(leaf.clause) {
		// Was something to be proved (dangling) when the cached proof was created,
		// but in our current context, it's given as an assumption
		return &_ClauseLeaf{leaf.clause, assumed}
	}

	// No change needed - the leaf's type matches the current context
	return leaf
}

// rebuildNodeSet rebuilds the nodeSet from the final graph structure.
// This removes any intermediate nodes that were created during expansion
// but are no longer part of the final proof DAG.
func (b *_ProofBuilder) rebuildNodeSet() {
	cleanNodeSet := utils.EmptySet[_ProofNode]()
	b.collectReachableNodes(b.proof.root, cleanNodeSet)
	b.proof.nodeSet = cleanNodeSet
}

// collectReachableNodes collects all nodes reachable from the given node.
func (b *_ProofBuilder) collectReachableNodes(
	node _ProofNode, nodeSet utils.Set[_ProofNode]) {
	if nodeSet.Has(node) {
		return
	}
	nodeSet.Add(node)

	// Recursively collect children
	for _, child := range node.Children() {
		b.collectReachableNodes(child, nodeSet)
	}
}

// alignHypotheses aligns the final theorem's hypotheses with the exact initial clauses.
func (b *_ProofBuilder) alignHypotheses() {
	if b.proof.clauseThm == nil {
		return
	}

	// Align hypotheses with exact initial clauses from the context
	b.proof.clauseThm = b.proof.clauseThm.AlignHyps(b.findInitClause)
}

// computeFinalThm computes the final theorem by traversing the expanded proof graph.
// It starts from the root theorem and iteratively derives new theorems by replacing
// hypotheses with their corresponding deduction steps, similar to the original
// traceBackDeduceSteps approach.
func (b *_ProofBuilder) computeFinalThm(node _ProofNode) *ClauseThm {
	// Start with the theorem at the root
	var startThm *ClauseThm
	switch n := node.(type) {
	case *_DeduceStep:
		startThm = n.clauseThm
	case *_MergeStep:
		startThm = n.clauseThm
	default:
		panic("Root node must be DeduceStep or MergeStep")
	}

	Assert(startThm != nil && startThm.IsRefuted())

	currentThm, _ := deriveThroughProof(
		startThm,
		buildClauseToNodeMap(node),
		b.isInitClause,
	)
	// Verify all remaining hypotheses are initial clauses
	for h := range currentThm.HypClauseIter() {
		Assert(b.isInitClause(h))
	}

	// Align hypotheses with exact initial clauses
	currentThm = currentThm.AlignHyps(b.findInitClause)

	return currentThm
}

// buildClauseToNodeMap builds a map from clause keys to the deduce nodes that
// prove them. It is shared by runtime proof completion and proto certificate
// serialization.
func buildClauseToNodeMap(root _ProofNode) map[ClauseKey]_ProofNode {
	clauseMap := make(map[ClauseKey]_ProofNode)
	visited := utils.EmptySet[_ProofNode]()
	buildClauseToNodeMapRec(root, clauseMap, visited)
	return clauseMap
}

func buildClauseToNodeMapRec(
	node _ProofNode,
	clauseMap map[ClauseKey]_ProofNode,
	visited utils.Set[_ProofNode]) {

	if visited.Has(node) {
		return
	}
	visited.Add(node)

	switch n := node.(type) {
	case *_DeduceStep:
		// Map the conclusion clause to this deduction step
		if !n.clauseThm.IsRefuted() {
			clauseMap[n.clauseThm.ConclClause().Key()] = n
		}
		// Recursively process children
		for _, child := range n.children {
			buildClauseToNodeMapRec(child, clauseMap, visited)
		}

	case *_MergeStep:
		// Recursively process children
		if n.divisibleChild != nil {
			buildClauseToNodeMapRec(n.divisibleChild, clauseMap, visited)
		}
		for _, child := range n.subProofChildren {
			buildClauseToNodeMapRec(child, clauseMap, visited)
		}

	case *_ClauseLeaf:
	// Leaf nodes don't prove anything, they are the base cases

	default:
		panic("Unknown node type in buildClauseToNodeMapRec")
	}
}

// deriveThroughProof repeatedly discharges hypotheses using reachable deduce
// nodes until every remaining hypothesis satisfies shouldStop.
//
// It returns both the resulting theorem and the exact deduce theorems that were
// used, in replay order. Different callers can then decide how to finish:
// computeFinalThm aligns to init clauses, while proto serialization may continue
// with explicit weakening steps to match a target theorem boundary.
func deriveThroughProof(
	startThm *ClauseThm,
	clauseToNode map[ClauseKey]_ProofNode,
	shouldStop func(*Clause) bool,
) (*ClauseThm, []*ClauseThm) {
	currentThm := startThm
	appearedThms := make(utils.Set[PropKey])
	steps := make([]*ClauseThm, 0)

	for {
		thmKey := currentThm.AlphaKey()
		if appearedThms.Has(thmKey) {
			panic("Cycle detected in proof derivation")
		}
		appearedThms.Add(thmKey)

		var expandStep *_DeduceStep
		for h := range currentThm.HypClauseIter() {
			if shouldStop(h) {
				continue
			}
			if node, ok := clauseToNode[h.Key()]; ok {
				if step, ok := node.(*_DeduceStep); ok {
					expandStep = step
					break
				}
			}
		}

		if expandStep == nil {
			break
		}

		currentThm = currentThm.DeriveHypFrom(expandStep.clauseThm)
		steps = append(steps, expandStep.clauseThm)
	}

	return currentThm, steps
}
