// cases.go — the chapter's structural principle: every list is empty or
// a head in front of a tail.
//
// It stands alone because it belongs to neither an operation nor the
// definitional layer. The datatype door derives induction, the recursion
// schema and the constructors' injectivity and distinctness; the plain
// case analysis is not among them. It is what a proof reaches for when
// it must decompose an unknown list and has no use for a hypothesis
// about the tail — `LengthEqCons` here, and `listing.SetOfListEqEmpty`
// next door.

package list

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// Cases — the split the datatype door leaves out. Its four principles
// give induction, the recursion schema and the constructors'
// injectivity and distinctness, but not the plain case analysis an
// argument over an unknown list opens with. Induction is what buys it,
// and its hypothesis is never consulted: what the principle contributes
// here is only its reach — that nil and cons exhaust the lists — while
// each constructor decides the disjunction on sight.
var Cases = casesThm{family.Add(registry.ProofEntry{
	Name: "Cases",
	Key:  "prop_1ae14a7e00c6f381",
	Build: family.Theorem("∀l:list(A). l = nil ∨ (∃h:A. ∃t:list(A). l = cons(h, t))",
		func(a *Argument) {
			a.Induct("l")
			a.Base(
				"at nil the left disjunct is nil = nil",
				TrivialNormalized())
			// The hypothesis is never consulted: distinctness rules the
			// left disjunct out, and the right is witnessed by the
			// constructor's own two arguments — named here, and handed
			// straight back as the witnesses.
			a.Step(
				"at cons(h, t): a cons is never nil, so the left disjunct "+
					"is out and the right holds at this list's own head and tail",
				func(b *Argument) {
					parts := b.StepArgs("h", "t")
					head, tail := parts[0], parts[1]
					// Simplification brings the tail's binder outermost, so
					// the witnesses go in as tail, then head.
					b.Show(
						"the constructor's own head and tail witness the right disjunct",
						Simp(Fwd(NilNotCons)),
						Witness(tail),
						Witness(head),
						TrivialNormalized())
				})
		}),
})}
