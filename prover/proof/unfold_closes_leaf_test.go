package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
)

// An Unfold whose tidy closes the leaf — the opened conclusion is a
// hypothesis — leaves nothing for the step after it, and that step's
// refusal names the Unfold, where it was written, and what its tidy
// found, so the author drops what follows instead of hunting for the
// close.

// Inside one Show, the By after the Unfold is refused at its own site.
func TestUnfoldClosesLeaf_TheNextActionNamesTheUnfold(t *testing.T) {
	ctx := wrappedTestScript()
	requirePanicContains(t, "the step that closed the last leaf: the Unfold of zz_wrapped at prover/proof/unfold_closes_leaf_test.go:", func() {
		ctx.Theorem("∀P:num → bool. ∀x:num. P(x) ⇒ "+wrappedTestConst+"(P, x)",
			func(a *Argument, P *ext.Expr[natSet], x *ext.Expr[ext.Nat], holds Fact) {
				a.Show("the opened goal is the hypothesis", Unfold(wrappedTestDefinition), By(holds))
			})
	})
}

// Inside a Have's proof — the sightings' spelling — the same, and the
// refusal says what the tidy found.
func TestUnfoldClosesLeaf_InsideAHave(t *testing.T) {
	ctx := wrappedTestScript()
	requirePanicContains(t, "its tidy found the opened conclusion P₀(x₀) stated by a hypothesis", func() {
		ctx.Theorem("∀P Q:num → bool. ∀x:num. P(x) ⇒ Q(x) ⇒ "+wrappedTestConst+"(P, x) ∧ Q(x)",
			func(a *Argument, P, Q *ext.Expr[natSet], x *ext.Expr[ext.Nat], holds, also Fact) {
				wrapped := a.Have("the wrapped fact", wrappedTestConst+"(P, x)", Unfold(wrappedTestDefinition), By(holds))
				a.Show("with Q(x), the goal", By(wrapped, also))
			})
	})
}

// A verb after an a.Do(Unfold) that closed the block names the Unfold,
// not a Show the block never ran.
func TestUnfoldClosesLeaf_AVerbAfterTheBlockClosed(t *testing.T) {
	ctx := wrappedTestScript()
	requirePanicContains(t, "the step that closed the last leaf: the Unfold of zz_wrapped at prover/proof/unfold_closes_leaf_test.go:", func() {
		ctx.Theorem("∀P:num → bool. ∀x:num. P(x) ⇒ "+wrappedTestConst+"(P, x)",
			func(a *Argument, P *ext.Expr[natSet], x *ext.Expr[ext.Nat], holds Fact) {
				a.Do(Unfold(wrappedTestDefinition))
				a.Do(Basic())
			})
	})
}
