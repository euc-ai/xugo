package refuter

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/utils"
)

func describeClauseProto(p *clause.DisjunctClauseProto) string {
	if p == nil {
		return "<nil concl => FClause>"
	}
	return fmt.Sprintf("clause(%d lits, %d univ)", len(p.GetLits()), len(p.GetUniv()))
}

type _ProtoSerializeContext struct {
	isInitClause func(*Clause) bool
	findInit     func(*Clause) *Clause
	pool         *ext.PoolBuilder // shared pool for the whole certificate
}

// proofStateProto serializes one completed refutation state into a self-contained
// certificate for that refuted subproof.
//
// The important design choice is that proto nodes do not mirror every node in
// the in-memory proof DAG. Each proto node represents one finished
// refuted subproof:
//   - its target theorem is exactly state.proof.ClauseThm()
//   - its base construction is either a local deduce step or a merge over child
//     refuted subproofs
//   - any remaining gap from that base theorem to the target theorem is recorded
//     explicitly as replay steps
//
// This avoids asking the reconstructor to rediscover discharge order or recover
// occurrence-specific theorem boundaries from a compressed DAG.
func proofStateProto(state *_RefuteState, pool *ext.PoolBuilder) *RefuteStepProto {
	ctx := _ProtoSerializeContext{
		isInitClause: state.isInitClause,
		findInit:     state.findInitClause,
		pool:         pool,
	}
	return serializeRefuteState(state, ctx)
}

// serializeRefuteState emits the certificate for a single refuted subproof.
//
// A serialized node always records:
// - the exact target hypothesis boundary of the subproof
// - an explicit replay script from the node's base theorem to that target
//
// Then it records one of two base constructions:
//   - Deduce: the root itself is a local refuted deduce step, so the base theorem
//     is reconstructable directly from ClauseThmProto.
//   - Merge: the base theorem is obtained by recursively reconstructing each child
//     subproof, weakening a child back to its divided clause when necessary, and
//     then applying division.Merge.
//
// Note that merge children are serialized from their own _RefuteState rather
// than from the cloned DAG fragment hanging under the parent merge node. This is
// deliberate: each child state already carries the exact final theorem for that
// subproblem, and treating it as an independent certificate avoids the stale
// occurrence-boundary problems that appeared when serializing the merged DAG
// shape directly.
func serializeRefuteState(
	state *_RefuteState,
	ctx _ProtoSerializeContext,
) *RefuteStepProto {
	targetThm := state.proof.ClauseThm()
	protoNode := &RefuteStepProto{
		Hyps:   serializeHypClauses(targetThm, ctx.pool),
		Replay: buildReplayProto(state, ctx),
	}

	switch root := state.proof.Root().(type) {
	case *_DeduceStep:
		Assert(root.clauseThm.IsRefuted())
		protoNode.Step = &RefuteStepProto_Deduce{Deduce: &DeduceProofProto{
			LocalStep: clause.SerializeClauseThm(root.clauseThm, ctx.pool),
		}}

	case *_MergeStep:
		dividedClausesProto := make([]*clause.DisjunctClauseProto, len(root.division.DividedClauses))
		for i, c := range root.division.DividedClauses {
			dividedClausesProto[i] = clause.SerializeClause(c, ctx.pool)
		}

		childProofs := make([]*RefuteStepProto, len(root.states))
		for i, childState := range root.states {
			childCtx := _ProtoSerializeContext{
				isInitClause: childState.isInitClause,
				findInit:     childState.findInitClause,
				pool:         ctx.pool,
			}
			childProofs[i] = serializeRefuteState(childState, childCtx)
		}

		protoNode.Step = &RefuteStepProto_Merge{Merge: &MergeProofProto{
			DivisibleClause: clause.SerializeClause(root.division.DivisibleClause, ctx.pool),
			DividedClauses:  dividedClausesProto,
			Children:        childProofs,
		}}

	default:
		panic("Wrong root node type.")
	}

	return protoNode
}

// serializeHypClauses records only the hypothesis boundary of a theorem.
//
// The target theorem of a refuted subproof may have arbitrarily many hyps, so we
// intentionally serialize just its shape here instead of trying to serialize it
// as a directly reconstructable ClauseThmProto.
func serializeHypClauses(t *ClauseThm, pool *ext.PoolBuilder) []*clause.DisjunctClauseProto {
	hyps := make([]*clause.DisjunctClauseProto, 0, t.NumHyps())
	for h := range t.HypClauseIter() {
		hyps = append(hyps, clause.SerializeClause(h, pool))
	}
	return hyps
}

// buildReplayProto computes the explicit replay script that turns the base
// theorem of this refuted subproof into its final target theorem.
//
// The script has two kinds of steps:
//   - Derive(step): apply a local deduce theorem from the proof DAG via
//     DeriveHypFrom. This removes one current hypothesis and replaces it with the
//     hypotheses of that deduce step.
//   - Weaken(hyp): add back a target hypothesis that is missing from the current
//     theorem. This is sound because weakening only adds assumptions.
//
// The base theorem is produced by replayStartTheorem. From there we repeatedly
// discharge any non-target hypothesis that already has a corresponding deduce
// node in the proof DAG. Once no more such discharge is possible, we add back
// any remaining target hyps via weakening and finally align clause identities to
// the exact init/assumption clauses of this state.
//
// The result is a purely explicit certificate: the reconstructor will later
// execute exactly these replay steps, in order, instead of searching the graph.
func buildReplayProto(
	state *_RefuteState,
	ctx _ProtoSerializeContext,
) []*ReplayStepProto {
	targetThm := state.proof.ClauseThm()
	targetByKey := make(map[ClauseKey]*Clause, targetThm.NumHyps())
	for h := range targetThm.HypClauseIter() {
		targetByKey[h.Key()] = h
	}

	currentThm, deriveSteps := deriveThroughProof(
		replayStartTheorem(state),
		buildClauseToNodeMap(state.proof.Root()),
		func(c *Clause) bool { return targetByKey[c.Key()] != nil },
	)

	replay := make([]*ReplayStepProto, 0, len(deriveSteps))
	for _, step := range deriveSteps {
		replay = append(replay, &ReplayStepProto{
			Step: &ReplayStepProto_Derive{
				Derive: clause.SerializeClauseThm(step, ctx.pool),
			},
		})
	}

	targetHyps := make([]*Clause, 0, targetThm.NumHyps())
	for hyp := range targetThm.HypClauseIter() {
		targetHyps = append(targetHyps, hyp)
	}
	slices.SortFunc(targetHyps, func(c0, c1 *Clause) int {
		return c0.Term().Compare(c1.Term())
	})
	for _, hyp := range targetHyps {
		if currentThm.HasHypClause(hyp) {
			continue
		}
		currentThm = currentThm.AddHyps(hyp)
		replay = append(replay, &ReplayStepProto{
			Step: &ReplayStepProto_Weaken{
				Weaken: clause.SerializeClause(hyp, ctx.pool),
			},
		})
	}

	currentThm = currentThm.AlignHyps(func(c *Clause) *Clause {
		if target := targetByKey[c.Key()]; target != nil {
			return target
		}
		if initClause := ctx.findInit(c); initClause != nil {
			return initClause
		}
		return c
	})

	Assert(currentThm.NumHyps() == targetThm.NumHyps())
	for h := range currentThm.HypClauseIter() {
		Assert(targetByKey[h.Key()] != nil)
	}
	return replay
}

// replayStartTheorem returns the base theorem from which the replay script for a
// refuted subproof should start.
//
// For a deduce-root proof this is trivial: the root local step already is the
// base theorem.
//
// For a merge-root proof we intentionally do not trust root.clauseThm as the
// base theorem. In cached proofs that value may already have been normalized to
// the final theorem of the whole subproof. Instead we reconstruct the merge base
// theorem from the child subproof theorems:
//  1. each child contributes its own final theorem
//  2. if that final theorem no longer mentions the divided clause, we weaken it
//     back to include the divided clause so it can legally participate in the
//     merge rule
//  3. division.Merge(children) yields the actual merge base theorem
//
// This is the key step that keeps serialization on the theorem-replay side of
// the core boundary: we reconstruct merge bases using sound operations rather
// than restoring arbitrary theorems from raw data.
func replayStartTheorem(state *_RefuteState) *ClauseThm {
	switch root := state.proof.Root().(type) {
	case *_DeduceStep:
		Assert(root.clauseThm.IsRefuted())
		return root.clauseThm

	case *_MergeStep:
		childrenThms := make([]*ClauseThm, len(root.states))
		for i, childState := range root.states {
			childThm := childState.proof.ClauseThm()
			dividedClause := root.division.DividedClauses[i]
			Assert(childThm.HasHypClause(dividedClause))
			childrenThms[i] = childThm
		}
		return root.division.Merge(childrenThms)

	default:
		panic("Wrong root node type.")
	}
}

type _ProtoProofReconstructor struct {
	reader *ext.PoolReader
}

func newProtoProofReconstructor(reader *ext.PoolReader) *_ProtoProofReconstructor {
	return &_ProtoProofReconstructor{reader: reader}
}

// deserializeTargetHyps reconstructs the exact target hypothesis boundary stored
// in proto and returns both:
// - the sorted slice of target clauses
// - a key lookup used during alignment/validation
//
// The stored target is theorem shape information only; it does not itself claim
// that the theorem has been proved. The actual proof comes from replaying the
// base construction plus the explicit replay script.
func deserializeTargetHyps(
	node *RefuteStepProto,
	reader *ext.PoolReader,
) ([]*Clause, map[ClauseKey]*Clause) {
	targetHyps := utils.MapSlice(
		node.Hyps,
		func(h *clause.DisjunctClauseProto) *Clause {
			return clause.DeserializeClause(h, reader)
		},
	)
	slices.SortFunc(targetHyps, func(c0, c1 *Clause) int {
		return c0.Term().Compare(c1.Term())
	})

	targetByKey := make(map[ClauseKey]*Clause, len(targetHyps))
	for _, h := range targetHyps {
		targetByKey[h.Key()] = h
	}
	return targetHyps, targetByKey
}

// theorem reconstructs the exact theorem certified by one proto node.
//
// Reconstruction is deliberately mechanical:
// 1. Rebuild the node's base theorem.
//   - Deduce nodes deserialize their local refuted deduce step.
//   - Merge nodes recursively reconstruct child subproof theorems, weaken a
//     child back to its divided clause when necessary, and apply Merge.
//
// 2. Execute the explicit replay script in order.
//   - Derive steps replay a serialized local deduce theorem.
//   - Weaken steps add back a target hypothesis explicitly.
//     3. Align the resulting hypothesis clauses to the exact target clause objects
//     recorded in proto, then assert exact target-shape equality.
//
// The reconstructor never searches the graph, never does last-wins clause lookup
// and never infers a missing occurrence theorem boundary. All of that choice is
// already baked into the serialized replay script.
func (r *_ProtoProofReconstructor) theorem(node *RefuteStepProto) *ClauseThm {
	targetHyps, targetByKey := deserializeTargetHyps(node, r.reader)

	var currentThm *ClauseThm
	switch step := node.Step.(type) {
	case *RefuteStepProto_Deduce:
		currentThm = clause.DeserializeClauseThm(step.Deduce.LocalStep, r.reader)
		if currentThm == nil {
			panic(fmt.Sprintf("DeserializeClauseThm returned nil for deduce base step "+
				"(%s concl): the recorded inference recipe did not reproduce the thm "+
				"(stale recipe).",
				describeClauseProto(step.Deduce.LocalStep.GetConcl())))
		}

	case *RefuteStepProto_Merge:
		childrenThms := make([]*ClauseThm, len(step.Merge.Children))
		divisibleClause := clause.DeserializeClause(step.Merge.DivisibleClause, r.reader)
		for i, child := range step.Merge.Children {
			dividedClause := clause.DeserializeClause(step.Merge.DividedClauses[i], r.reader)
			childThm := r.theorem(child)
			Assert(childThm.HasHypClause(dividedClause))
			childrenThms[i] = childThm
		}
		division := divisibleClause.Division()
		if division == nil {
			// Bool ground var case split: the divisible clause is a synthetic
			// tautology Or(b, ¬b) that has no component-based division.
			// Reconstruct via BoolVarDivision from the first divided clause.
			lits := clause.DeserializeClause(step.Merge.DividedClauses[0], r.reader).Lits()
			Assert(len(lits) == 1)
			b, ok := lits[0].AsVar()
			Assert(ok && ext.IsBool(b))
			division = clause.BoolVarDivision(b)
		}
		currentThm = division.Merge(childrenThms)

	default:
		panic("Wrong node type.")
	}

	for replayIdx, replayStep := range node.Replay {
		switch step := replayStep.Step.(type) {
		case *ReplayStepProto_Derive:
			derived := clause.DeserializeClauseThm(step.Derive, r.reader)
			if derived == nil {
				panic(fmt.Sprintf("DeserializeClauseThm returned nil at replay[%d] "+
					"(%s concl): the recorded inference recipe did not reproduce the thm "+
					"(stale recipe).",
					replayIdx, describeClauseProto(step.Derive.GetConcl())))
			}
			currentThm = currentThm.DeriveHypFrom(derived)
		case *ReplayStepProto_Weaken:
			currentThm = currentThm.AddHyps(
				clause.DeserializeClause(step.Weaken, r.reader))
		default:
			panic("Wrong replay step type.")
		}
	}

	currentThm = currentThm.AlignHyps(func(c *Clause) *Clause {
		if target := targetByKey[c.Key()]; target != nil {
			return target
		}
		return c
	})

	Assert(currentThm.NumHyps() == len(targetHyps))
	for h := range currentThm.HypClauseIter() {
		Assert(targetByKey[h.Key()] != nil)
	}

	return currentThm
}

// ReconstructCNFProofNode rebuilds the final CNF refutation theorem from the
// root certificate node.
//
// The returned theorem should alpha-equal refuter.refutedCNFClauseThm. All
// proof search has already happened before serialization; reconstruction is just
// trusted replay of the explicit certificate.
func ReconstructCNFProofNode(
	node *RefuteStepProto,
	reader *ext.PoolReader,
) *ClauseThm {
	reconstructor := newProtoProofReconstructor(reader)
	return reconstructor.theorem(node)
}
