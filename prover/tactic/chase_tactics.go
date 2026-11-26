package tactic

import (
	"github.com/euc-ai/xugo/prover/solver/chase"
)

// ChaseTactic closes the goal by the diagram chase at the given depth
// (prover/solver/chase): the goal's hypotheses read as an abelian
// diagram, its conclusion decided against them, the kernel handed the
// derivation. nil when the chase does not close the goal, with the
// chase's report saying where it stopped; it panics when the closer's
// laws are not installed or the diagram is refused (a cycle). indexArith
// grants the bridging of degree indices by the nat ring normalizer.
func ChaseTactic(goal Prop, depth int, indexArith bool) (*SubGoals, chase.Result) {
	thm, res, err := chase.Close(goal, chase.Options{Depth: depth, IndexArith: indexArith})
	if err != nil {
		panic("chase: " + err.Error())
	}
	if thm == nil {
		return nil, res
	}
	return MakeEmptySubGoals(goal, thm), res
}
