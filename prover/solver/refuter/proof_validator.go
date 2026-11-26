/**
 * File: proof_validator.go
 *
 * ProofValidator is responsible for validating the correctness and completeness
 * of proof DAGs. It performs various checks to ensure the proof is well-formed,
 * including cycle detection, dangling reference checks, and hypothesis validation.
 */

package refuter

import (
	"fmt"

	"github.com/euc-ai/xugo/utils"
)

// validateDAG performs comprehensive validation of a proof DAG.
// Returns an error if any validation check fails, nil if the proof is valid.
func (v *_ProofContext) validateDAG(dag *_ProofDAG) error {
	// Check basic structure
	if err := checkBasicStructure(dag); err != nil {
		return err
	}

	// Check for cycles
	if err := checkNoCycles(dag); err != nil {
		return err
	}

	// Check for dangling leaves
	if err := checkNoDanglingLeaves(dag); err != nil {
		return err
	}

	// Validate hypotheses
	if err := v.validateHypotheses(dag); err != nil {
		return err
	}

	// Validate node consistency
	if err := v.validateNodeConsistency(dag); err != nil {
		return err
	}

	return nil
}

// checkBasicStructure ensures the DAG has a valid basic structure.
func checkBasicStructure(dag *_ProofDAG) error {
	if dag.root == nil {
		return fmt.Errorf("proof DAG has no root node")
	}

	if dag.clauseThm == nil || !dag.clauseThm.IsRefuted() {
		return fmt.Errorf("proof theorem is not refuted")
	}

	if !dag.nodeSet.Has(dag.root) {
		return fmt.Errorf("root node not in node set")
	}

	return nil
}

// checkNoCycles detects cycles in the proof DAG.
func checkNoCycles(dag *_ProofDAG) error {
	visited := utils.EmptySet[_ProofNode]()
	recursionStack := utils.EmptySet[_ProofNode]()

	var detectCycle func(node _ProofNode) error
	detectCycle = func(node _ProofNode) error {
		if recursionStack.Has(node) {
			return fmt.Errorf("cycle detected in proof DAG at node %v", node)
		}

		if visited.Has(node) {
			return nil
		}

		visited.Add(node)
		recursionStack.Add(node)

		for _, child := range node.Children() {
			if err := detectCycle(child); err != nil {
				return err
			}
		}

		delete(recursionStack, node)
		return nil
	}

	return detectCycle(dag.root)
}

// checkNoDanglingLeaves ensures there are no dangling clause leaves in the DAG.
func checkNoDanglingLeaves(dag *_ProofDAG) error {
	if dag.anyLeaf(func(leaf *_ClauseLeaf) bool {
		return leaf.isDangling()
	}) {
		return fmt.Errorf("dangling clause leaf found")
	}
	return nil
}

// validateHypotheses ensures all hypotheses are properly formed and referenced.
func (v *_ProofContext) validateHypotheses(dag *_ProofDAG) error {
	// Check that all hypotheses are initial clauses
	for h := range dag.clauseThm.HypClauseIter() {
		if !v.isInitClause(h) {
			return fmt.Errorf("hypothesis is not an initial clause: %v", h)
		}

		// Hypothesis must be one of: original, assumption, or dangling (for upper levels)
		if !utils.OneOf(
			v.isOrigInitClause(h),
			v.isAssumptionClause(h),
			dag.anyLeaf(func(leaf *_ClauseLeaf) bool {
				return leaf.isDangling() && leaf.clause.Equivalent(h)
			})) {
			return fmt.Errorf("hypothesis has invalid type: %v", h)
		}
	}

	// Check that all dangling leaves correspond to a hypothesis
	if dag.anyLeaf(func(leaf *_ClauseLeaf) bool {
		return leaf.isDangling() && !dag.clauseThm.HasHypClause(leaf.clause)
	}) {
		return fmt.Errorf("dangling leaf not in hypotheses")
	}

	return nil
}

// validateNodeConsistency checks that all nodes are properly connected and typed.
func (v *_ProofContext) validateNodeConsistency(dag *_ProofDAG) error {
	// Check that all nodes in the DAG are reachable from the root
	reachable := collectReachableNodes(dag.root)
	for node := range dag.nodeSet {
		if !reachable.Has(node) {
			return fmt.Errorf("node in nodeSet is not reachable from root: %v", node)
		}
	}

	// Validate each node type
	for node := range dag.nodeSet {
		if err := v.validateNode(node, dag); err != nil {
			return err
		}
	}

	return nil
}

// collectReachableNodes returns all nodes reachable from the given node.
func collectReachableNodes(root _ProofNode) utils.Set[_ProofNode] {
	reachable := utils.EmptySet[_ProofNode]()
	queue := []_ProofNode{root}

	for len(queue) > 0 {
		node := queue[0]
		queue = queue[1:]
		if reachable.Has(node) {
			continue
		}
		reachable.Add(node)
		queue = append(queue, node.Children()...)
	}
	return reachable
}

// validateNode validates a single node based on its type.
func (v *_ProofContext) validateNode(node _ProofNode, dag *_ProofDAG) error {
	switch n := node.(type) {
	case *_DeduceStep:
		return validateDeduceStep(n)
	case *_MergeStep:
		return validateMergeStep(n)
	case *_ClauseLeaf:
		return v.validateClauseLeaf(n, dag)
	default:
		return fmt.Errorf("unknown node type: %T", node)
	}
}

// validateDeduceStep validates a deduction step node.
func validateDeduceStep(step *_DeduceStep) error {
	if step.clauseThm == nil {
		return fmt.Errorf("deduce step has no clause theorem")
	}

	// Check that the number of children matches the number of hypotheses
	if step.clauseThm.NumHyps() != len(step.Children()) {
		return fmt.Errorf("deduce step hypothesis count mismatch: theorem has %d, node has %d children",
			step.clauseThm.NumHyps(), len(step.Children()))
	}

	// Validate that hypotheses match children
	for i, child := range step.Children() {
		if leaf, ok := child.(*_ClauseLeaf); ok {
			if !step.clauseThm.HasHypClause(leaf.clause) {
				return fmt.Errorf("deduce step child %d clause not in hypotheses", i)
			}
		}
	}

	return nil
}

// validateMergeStep validates a merge step node.
func validateMergeStep(step *_MergeStep) error {
	// Validate hypothesis count.
	// For regular divisions: n+1 hyps (n negated components + divisible clause).
	// For bool ground var split (i.e. b₀ = ⊤ ∨ b₀ = ⊥): n hyps (no divisible clause).
	n := len(step.division.DividedClauses)
	numHyps := step.division.RefutingThm.NumHyps()
	if numHyps != n+1 && numHyps != n {
		return fmt.Errorf("merge step hypothesis count mismatch: expected %d or %d, got %d",
			n, n+1, numHyps)
	}

	return nil
}

// validateClauseLeaf validates a clause leaf node.
func (v *_ProofContext) validateClauseLeaf(leaf *_ClauseLeaf, dag *_ProofDAG) error {
	if leaf.clause == nil {
		return fmt.Errorf("clause leaf has no clause")
	}

	// Validate leaf type consistency
	switch leaf.leafType {
	case origInit:
		if !v.isOrigInitClause(leaf.clause) {
			return fmt.Errorf("leaf marked as original but clause is not original initial")
		}
	case assumed:
		if !v.isAssumptionClause(leaf.clause) {
			// When reusing a cached proof, an "assumed" leaf might be from a sub-proof
			// (e.g. in a merge step) where it was a valid assumption, but that
			// assumption was discharged and is not part of the final theorem's hypotheses.
			// In this case, we don't validate it against the current context, as it's
			// considered an internal, implementation detail of the cached proof.
			// However, if it IS a hypothesis of the final theorem, it MUST be a valid
			// assumption in the current context.
			if dag.clauseThm.HasHypClause(leaf.clause) {
				return fmt.Errorf("leaf marked as assumed but clause is not assumption")
			}
		}
	case dangling:
		// Dangling leaves should not exist in a complete proof
		return fmt.Errorf("dangling leaf found: %v", leaf.clause)
	default:
		return fmt.Errorf("invalid leaf type: %v", leaf.leafType)
	}

	return nil
}

// validate checks that a proof is complete and ready for use.
// This method assumes that the caller holds the lock on dag.
func (v *_ProofContext) validate(dag *_ProofDAG) error {
	// First run all standard validations
	if err := v.validateDAG(dag); err != nil {
		return err
	}

	clauseThm := dag.clauseThm
	// Ensure the proof actually proves false (⊥)
	if !clauseThm.IsRefuted() {
		return fmt.Errorf("proof does not conclude with ⊥")
	}

	// Ensure all hypotheses can be traced back to initial clauses
	for h := range clauseThm.HypClauseIter() {
		initClause := v.findInitClause(h)
		if initClause == nil {
			return fmt.Errorf("hypothesis cannot be traced to initial clause: %v", h)
		}
		if !h.Term().AlphaEquals(initClause.Term()) {
			return fmt.Errorf("hypothesis body does not match initial clause body")
		}
	}

	return nil
}
