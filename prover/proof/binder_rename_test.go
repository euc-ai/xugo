// binder_rename_test.go — Binder (derive.go) takes the STATEMENT's
// name even after an earlier strip α-renamed the binder.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// The trap this closes: a section closure binding its first binder as
// a parameter leaves the second binder spelled `n₀` in the goal, and
// `a.Induct("n")` panicked "no leading ∀-binder by that name (binders:
// [n_0])" — so the string form was safe only in a zero-parameter
// closure, and six corpus sites spelled the engine's `n_0`.
func TestBinder_InvertsTheRenameAnEarlierStripLeaves(t *testing.T) {
	env := makeStepTestEnv()
	env.LibraryThms = map[string]Thm{"num_induction": numInductionThm}
	ctx := NewScript(env)
	Q := ctx.Var("Q", MakeFun(numType, numType, TypeBool))
	m := Var("m", numType)
	n := Var("n", numType)
	// ∀m n. Q(m, n), with ∀m. Q(m, 0) and ∀m n. Q(m, n) ⇒ Q(m, suc(n)) resident.
	baseLaw := ForAll(m)(Q.Apply(m, zeroTerm)).Core()
	stepLaw := ForAll(m)(ForAll(n)(Q.Apply(m, n).Imply(Q.Apply(m, sucOf(n))))).Core()
	goal := MakeProp(ForAll(m)(ForAll(n)(Q.Apply(m, n))), baseLaw, stepLaw)

	sec := ctx.Section(goal)
	var spelled string
	sec.Do(Derive(func(a *Argument) {
		mTerm := a.Fix("m")
		// The goal now reads ∀n₀. Q(m, n₀) (or still ∀n. …) — either way
		// the statement's name is the spelling.
		nTerm := a.Binder("n")
		spelled = ext.PrintTerm(nTerm.Core())
		a.Induct("n")
		a.Base("Q(m, 0) is the base law at m", By(a.Hyp(baseLaw).At(mTerm)))
		a.Step("the step law at m and the induction hypothesis", func(b *Argument, ih Fact) {
			b.Show("by the step law", By(ih, b.Hyp(stepLaw).At(mTerm)))
		})
	}))
	require.True(t, sec.Proved())
	require.NotEqual(t, "n", spelled, "the strip renamed the binder, so the statement's name was resolved through the rename")
	t.Logf("the goal spelled the binder %s", spelled)
}

func TestBinder_RefusesAnUnknownNameWithTheLegend(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	sec := ctx.Section(MakeProp(ForAll(n)(Q.Apply(n)), ForAll(n)(Q.Apply(n))))
	msg := panicMessage(func() {
		sec.Do(Derive(func(a *Argument) {
			a.Binder("k")
			a.Show("never", Assumption())
		}))
	})
	require.Contains(t, msg, `Binder("k")`)
	require.Contains(t, msg, "no leading ∀-binder")
	_ = prop.PrintProp
}
