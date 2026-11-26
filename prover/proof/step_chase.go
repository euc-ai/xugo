package proof

// step_chase.go — the diagram-chase closer as the terminal step of a
// By composite (`ByChase(Depth(k), premises…)`, fact.go). It runs on
// the By executor's private stack only: the composite records the call
// (ByProto.chase, chase_depth) and replay re-runs the same executor, so
// the step has no wire form of its own, as the grounding step has none.
// The closer is deterministic and bounded (prover/solver/chase): it
// records no key and searches nothing at replay. A leaf it does not
// close panics with the chase's report — which element at which module
// stayed outside which image after how many rounds — and the By
// diagnostics wrap it; there is no fall-through to another closer.

import (
	"fmt"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/chase"
	"github.com/euc-ai/xugo/prover/tactic"
)

// _ChaseStep closes a leaf by the diagram chase at the given depth.
type _ChaseStep struct {
	depth int
}

func (step _ChaseStep) String() string { return fmt.Sprintf("Chase(depth %d)", step.depth) }

func (_ChaseStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	panic("_ChaseStep has no wire form: the By composite that runs it records the call (ByProto.chase)")
}

func (step _ChaseStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }

func (step _ChaseStep) apply(p Prop) *SubGoals { return step.applyScoped(p, nil) }

// applyScoped runs the chase under the leaf's proof scope: the scope
// must allow the chase capability (a member the closer's laws rest on
// may not use it), and index arithmetic — a ∀-fact over degrees
// instantiated at a degree the leaf spells another way — is granted
// where the scope allows nat arithmetic. A chase that used nat
// arithmetic — a degree it rewrote, numeral literals a scalar ring
// folded — stands on the nat-arithmetic laws: the scope must allow that
// too, and records it.
func (step _ChaseStep) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	if scope != nil {
		scope.RequireCapability(CapabilityChase)
	}
	thm, res, err := chase.Close(p, chase.Options{
		Depth:      step.depth,
		IndexArith: scope == nil || scope.allows(CapabilityArithNat),
		Reader:     libraryReader(scope),
	})
	if err != nil {
		panic(fmt.Sprintf("ByChase: %v", err))
	}
	if thm == nil {
		panic("ByChase: " + res.Report)
	}
	if res.NatArith && scope != nil {
		scope.RequireCapability(CapabilityArithNat)
	}
	return tactic.MakeEmptySubGoals(p, thm)
}

// _ChaseRecordsStep puts the leaf in the chase closer's normal form
// (chase.RewriteRecords), which exposes record components before Basic
// can substitute an element equal to zero in the flat module laws.
// Otherwise that substitution cannot reach the same zero hidden inside a
// record endpoint.
type _ChaseRecordsStep struct{}

func (_ChaseRecordsStep) String() string { return "ChaseRecords" }
func (_ChaseRecordsStep) proto(*ext.PoolBuilder) isStepProto_Step {
	panic("_ChaseRecordsStep has no wire form: the By composite records it")
}
func (step _ChaseRecordsStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }
func (step _ChaseRecordsStep) apply(p Prop) *SubGoals                     { return step.applyScoped(p, nil) }
func (_ChaseRecordsStep) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	if scope != nil {
		scope.RequireCapability(CapabilityChase)
	}
	reader := libraryReader(scope)
	concl := p.Conclusion()
	conclEq := chase.RewriteRecords(concl, reader)
	if conclEq != nil {
		concl = prop.Rhs(conclEq)
	}
	hyps := p.Hyps()
	bridges := make([]*prop.PropWrapper, len(hyps))
	changed := conclEq != nil
	for i, h := range hyps {
		if eq := chase.RewriteRecords(h, reader); eq != nil {
			bridges[i], hyps[i], changed = eq, prop.Rhs(eq), true
		}
	}
	if !changed {
		return nil
	}
	return tactic.MakeSubGoals(p, func(thms ...Prop) Prop {
		w := prop.WrapProp(thms[0])
		if conclEq != nil && !w.Conclusion().Equals(ext.F) {
			w = conclEq.EqSym().EqMP(w)
		}
		for _, eq := range bridges {
			if eq != nil {
				w = prop.WrapProp(eq.LeftAssume().MaybeDeriveTrans(w))
			}
		}
		return w
	}, prop.MakeProp(concl, hyps...))
}
