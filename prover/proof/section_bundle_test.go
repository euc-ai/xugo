package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// A Fact parameter where the statement offers a run of ∀ binders binds
// the run and the ⇒-antecedent that mentions each of them — what a
// bundle binder `∀N:S(…).` states — as one: the binders are fixed under
// their own names and the antecedent assumed. The rest of the closure
// binds after it as before.
func TestSection_FactBindsABundleSlot(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := ctx.Theorem("∀f:(num → num). ∀s:(num → bool). (∀x:num. x ∈ s ⇒ f(x) ∈ s) ⇒ ∀x:num. x ∈ s ⇒ f(f(x)) ∈ s",
		func(a *Argument, closed Fact, x *ext.Expr[ext.Nat], member Fact) {
			once := a.Have("f(x) lies in s", "f(x) ∈ s", By(closed, member))
			a.Show("and f of it again", By(closed, once))
		})
	require.True(t, sec.Proved())
}

// A run whose antecedent leaves a binder out is no bundle: the Fact
// parameter is refused at the ∀ slot, as it always was.
func TestSection_FactRefusedWhereTheAntecedentMissesABinder(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	defer func() {
		r := recover()
		require.NotNil(t, r)
		require.Contains(t, fmt.Sprint(r), "a Fact parameter binds")
	}()
	ctx.Theorem("∀f:(num → num). ∀s:(num → bool). (∀x:num. x ∈ s) ⇒ ∀x:num. x ∈ s",
		func(a *Argument, closed Fact, x *ext.Expr[ext.Nat]) {
			a.Show("s holds everything", By(closed))
		})
}
