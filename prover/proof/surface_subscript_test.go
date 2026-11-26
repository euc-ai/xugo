// surface_subscript_test.go — a surface name given to a verb is the
// identifier a claim text reads it as (derive.go §"Surface names"): the
// lexer folds a printed subscript to the kernel's `_digits`, so
// `Fix("s₁")` and a claim spelling `s₁` (read `s_1`) name one variable,
// and `s_1` written by the author is the same name. The three tests
// cover the three verb families that take a surface name — Fix (FixAs
// is fixImpl plus a type assertion), the witness names of Obtain and
// Unpack, and Binder — each with a goal whose own binder is NOT the
// subscripted name, so the binding is the only road to it.

package proof

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestSurfaceAlias_SubscriptedNameIsTheLexersIdentifier is the reported
// repro, reduced: the goal binds `x`, the author names the mint `s₁`,
// and the claims spell `s₁`. Both spellings resolve to the mint; an
// undeclared subscripted name is still refused (the negative control);
// and a nested block may not re-point the name under either spelling.
//
//	∀x. R(x) ∧ Q(x) ⇒ Q(x)
func TestSurfaceAlias_SubscriptedNameIsTheLexersIdentifier(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	x := ctx.Var("x", numType)

	sec := ctx.Section(MakeProp(
		ForAll(x)(R.Apply(x).And(Q.Apply(x)).Imply(Q.Apply(x)))))
	sec.Do(Derive(func(a *Argument) {
		fixed := a.Fix("s₁")
		require.True(t, a.Term("s₁").Core().Equals(fixed.Core()),
			"the subscripted spelling must resolve to the mint")
		require.True(t, a.Term("s_1").Core().Equals(fixed.Core()),
			"the kernel spelling is the same identifier")
		h := a.Assume()
		a.Have("a claim spelling the subscript", "R(s₁)", By(h))
		func() {
			defer func() {
				r := recover()
				require.NotNil(t, r, "an undeclared subscripted name must still be refused")
				require.Contains(t, fmt.Sprint(r), "undeclared free [s_2:num]", "the panic must name the typo")
			}()
			a.Have("a typo in the claim", "R(s₂)", By(h))
		}()
		a.Have("an inner ∀ under the live name", "∀n:num. R(n) ∧ Q(n) ⇒ Q(n)",
			Derive(func(b *Argument) {
				require.Panics(t, func() { b.Fix("s₁") },
					"the live name is refused under the author's spelling")
				require.Panics(t, func() { b.Fix("s_1") },
					"and under the kernel's — one name, one meaning")
				b.Fix()
				h2 := b.Assume()
				b.Show("close the inner claim", By(h2))
			}))
		a.Show("close", By(h))
	}))
	require.True(t, sec.Proved(), "the block did not close")
}

// TestSurfaceAlias_SubscriptedWitnessNames: the witness-naming verbs
// take the same key — Named("m₁") on an Obtain whose claim binds `∃w₁`
// as the reported one did, and Unpack's trailing name — and a name live
// under one spelling is refused under the other.
//
//	R(k) ⊢ ∃j. R(j) ∨ Q(j)
func TestSurfaceAlias_SubscriptedWitnessNames(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	k := ctx.Var("k", numType)
	j := Var("j", numType)

	sec := ctx.Section(MakeProp(Exists(j)(R.Apply(j).Or(Q.Apply(j))), R.Apply(k)))
	sec.Do(Derive(func(a *Argument) {
		rk := a.Hyp(R.Apply(k).Core())
		w, got := a.Obtain("R is inhabited (at k)", "∃w₁:num. R(w₁)", By(rk), Named("m₁"))
		require.True(t, a.Term("m₁").Core().Equals(w.Core()),
			"the named subscripted spelling must alias to the witness")
		a.Have("a claim spelling the witness's name", "R(m₁) ∨ Q(m₁)", By(got))

		again := a.Have("R is inhabited, again", "∃w:num. R(w)", By(rk))
		u, _ := a.Unpack(again, "p₂")
		require.True(t, a.Term("p₂").Core().Equals(u.Core()),
			"Unpack's trailing name takes the same key")
		third := a.Have("R is inhabited, a third time", "∃w:num. R(w)", By(rk))
		require.Panics(t, func() { a.Unpack(third, "m_1") },
			"the witness's name is live under the kernel spelling too — one name, one meaning")

		a.Take(a.Term("m₁"))
		a.Show("the obtained fact closes the goal", By(got))
	}))
	require.True(t, sec.Proved(), "the named witness did not carry the goal")
}

// TestSurfaceAlias_SubscriptedBinderName: Binder reads its name by the
// same rule — the goal spells `n_0`, which prints `n₀`, and the author
// writes what the goal prints.
//
//	∀n₀. R(n₀) ∧ Q(n₀) ⇒ Q(n₀)
func TestSurfaceAlias_SubscriptedBinderName(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	R := ctx.Var("R", MakeFun(numType, TypeBool))
	Q := ctx.Var("Q", MakeFun(numType, TypeBool))
	n0 := Var("n_0", numType)

	sec := ctx.Section(MakeProp(
		ForAll(n0)(R.Apply(n0).And(Q.Apply(n0)).Imply(Q.Apply(n0)))))
	sec.Do(Derive(func(a *Argument) {
		bound := a.Binder("n₀")
		require.True(t, bound.Core().Equals(n0.Core()), "the printed spelling must name the goal's binder")
		fixed := a.Fix()
		require.True(t, a.Term("n₀").Core().Equals(fixed.Core()))
		h := a.Assume()
		a.Have("the claim spells the binder as the goal prints it", "R(n₀)", By(h))
		a.Show("close", By(h))
	}))
	require.True(t, sec.Proved(), "the block did not close")
}
