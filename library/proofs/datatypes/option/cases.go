// cases.go — the chapter's structural principle: every optional value is
// absent or present.
//
// It stands alone because it belongs to neither an operation nor the
// definitional layer. The datatype door derives induction, the recursion
// schema and the constructors' injectivity and distinctness; the plain
// case analysis is not among them. It is what a proof reaches for when
// it must decompose an unknown optional value inside a deduction — a
// finite stopping time's index, a representative's value — rather than
// open a split on it.

package option

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// Cases — the split the datatype door leaves out. Induction is what buys
// it: what the principle contributes here is only its reach — that none
// and some exhaust the optional values — while each constructor decides
// the disjunction on sight.
var Cases = casesThm{family.Add(registry.ProofEntry{
	Name: "Cases",
	Key:  "prop_21bc5eb66f968456",
	Build: family.Theorem("∀t:option(A). t = none ∨ (∃a:A. t = some(a))",
		func(a *Argument) {
			a.Induct("t")
			a.Base(
				"at none the left disjunct is none = none",
				TrivialNormalized())
			a.Step(
				"at some(a): a present value is never none, so the "+
					"right disjunct holds at the constructor's own argument",
				func(b *Argument) {
					value := b.StepArgs("a")[0]
					b.Show(
						"the constructor's own argument witnesses the right disjunct",
						Simp(Fwd(NoneNotSome)),
						Witness(value),
						TrivialNormalized())
				})
		}),
})}
