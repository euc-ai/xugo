// step_ac.go — the AC kit's goal face as ONE composite ministep
// (StepProto_AcRegroup, tag 62): the leaf is the bare equation
// `lhs = rhs` between two ⊕-sums over one leaf multiset, the kit
// derives the rearrangement certificate from the assoc/sym pair, and
// the composite closes the leaf outright or — when the leaf is not
// itself the regroup equation — installs the certificate as a resident
// hypothesis grounded back to the literal equation, leaving ONE
// residual child for the author's downstream close.
//
// One executor for three callers, the record/emit/replay code-reuse
// principle (step_composite.go): the session `ac_regroup` tactic
// (ApplyACRegroup), the ACRegroup / ACRegroupWith Actions (fact.go),
// and a replay of either. The payload is the certificate PAIR's
// statements — what identifies the derivation, and what emit renders
// back as `ACRegroup(<assoc>, <sym>)` with each half a cite target. The
// derived certificate itself is never recorded: it has no registry
// identity, and recording it as a known_thm was exactly what left the
// step unrenderable, an unresolved TODO placeholder in the emitted text.
//
// The moves inside are the ones the pre-composite Action recorded
// (CiteKnown on the degenerate close; LemmaPreserve + its
// reproduction-child close + a grounding Specialize otherwise), run on
// a PRIVATE goal stack whose reconstruction becomes the composite's —
// the By composite's assembly (buildByReconstruct).

package proof

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ac"
	"github.com/euc-ai/xugo/prover/tactic"
)

type _ACRegroupStep struct {
	// assoc and sym are the certificates the kit reads: the
	// associativity law ∀m n p. (m⊕n)⊕p = m⊕(n⊕p) (either orientation)
	// and the commutativity law ∀m n. m⊕n = n⊕m over the same ⊕. Certs
	// (or promise-backed statements — a session cite); the proto
	// carries their statements.
	assoc, sym Prop
}

// ACRegroupStep is the ministep constructor: the AC kit's goal face as
// a Step, for a Do chain. assoc and sym must be certificates (a
// registry entry's, `ctx.Dep(name)`); a bare statement panics at apply.
func ACRegroupStep(assoc, sym Thm) Step {
	if assoc == nil || sym == nil {
		panic("ACRegroupStep: nil assoc/sym certificate")
	}
	return _ACRegroupStep{assoc: assoc, sym: sym}
}

func (step _ACRegroupStep) String() string {
	return fmt.Sprintf("ACRegroup: assoc %s, sym %s",
		prop.PrintProp(step.assoc), prop.PrintProp(step.sym))
}

func (step _ACRegroupStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	return &StepProto_AcRegroup{AcRegroup: &AcRegroupProto{
		Assoc: b.PropRef(step.assoc),
		Sym:   b.PropRef(step.sym),
	}}
}

// apply derives the regroup certificate for the leaf's equation and
// closes or installs it. Panics (soundness-first, recovered by the
// session dispatch into its error channel) carry the kit's own
// contract diagnostics: a non-equation leaf, sides that are not
// AC-equal, a certificate of the wrong shape.
func (step _ACRegroupStep) apply(p Prop) *SubGoals {
	if step.assoc == nil || step.sym == nil {
		panic("ac_regroup: nil assoc/sym certificate")
	}
	if !step.assoc.Proved() && !core.IsPromised(step.assoc) ||
		!step.sym.Proved() && !core.IsPromised(step.sym) {
		panic("ac_regroup: the assoc/sym pair must be certificates (a registry entry's, " +
			"ctx.Dep(entry)), not bare statements")
	}
	l, r, ok := prop.MatchesEQ(p.Conclusion())
	if !ok {
		panic(fmt.Sprintf("ac_regroup: leaf goal is not an equation — strip the "+
			"binders first so the goal is the bare `lhs = rhs`\n  goal: %s",
			PrintProp(p)))
	}
	d := ac.New(core.AsThm(step.assoc), core.AsThm(step.sym))
	d.Validate(l, r)
	eq := d.RegroupEq(l, r)
	if IsStronger(eq, p) {
		// The leaf IS the regroup equation — the degenerate close.
		return tactic.MakeEmptySubGoals(p, eq)
	}
	// Otherwise the equation is installed as a resident hypothesis
	// for a downstream close: the preserving install (∀-closed over
	// the equation's frees by hypMatching), its reproduction child
	// closed from the derived certificate, the closure grounded back
	// at its own variables — on a private tree whose reconstruction
	// becomes this composite's.
	root := CreateGoalStack(p)
	before := root.Goal
	if !ApplyLemmaPreserveExactWithSource(root, eq, "") {
		panic(fmt.Sprintf("ac_regroup: LemmaPreserve failed for the derived equation %s "+
			"on goal %s", PrintProp(eq), PrintProp(p)))
	}
	if cl := root.unsolvedLeaf(0); cl == nil ||
		!cl.runStep(_KnownThmStep{strongerGoal: eq}) {
		panic("ac_regroup: the derived certificate does not close its own reproduction child")
	}
	res := root.unsolvedLeaf(0)
	if res != nil {
		if idx, err := newHypIndex(before, res.Goal); err == nil {
			// A single new hyp: the ∀-closure of the equation. Ground it
			// at its own variables (the CiteSpecialize shape). No single
			// new hyp means the preserving chain consumed the equation
			// another way (a conclusion rewrite) — a deterministic,
			// recorded outcome, accepted as the Action always did.
			vars, body := ac.StripForallBinders(res.Goal.Hyp(idx))
			if len(vars) > 0 {
				if !body.AlphaEquals(eq.Conclusion()) {
					panic(fmt.Sprintf("ac_regroup: installed hyp is not a ∀-closure of the derived "+
						"equation — unexpected install shape\n  installed: %s\n  derived:   %s",
						ext.PrintTerm(res.Goal.Hyp(idx)), PrintProp(eq)))
				}
				witnesses := make([]Term, len(vars))
				for i, v := range vars {
					witnesses[i] = v
				}
				if !res.runStep(Specialize(InstHyp(idx, witnesses...))) {
					panic("ac_regroup: grounding the installed ∀-closure back at its own variables failed")
				}
			}
		}
	}
	residual := root.unsolvedLeaf(0)
	if residual == nil {
		Assert(root.Proved())
		return tactic.MakeEmptySubGoals(p, root.provedThm)
	}
	rootFn := buildByReconstruct(root, map[*GoalStackNode]int{residual: 0})
	return tactic.MakeSubGoals(p, func(certs ...Prop) Prop { return rootFn(certs) }, residual.Goal)
}

func (step _ACRegroupStep) applyAction(s *Script, root *GoalStackNode) { s.Do(root, step) }
