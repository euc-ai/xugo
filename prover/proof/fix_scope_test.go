package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// A name fresh for a leaf is not fresh for the block the leaf is proved
// in: the statement's `x` is fixed as x₀:num, and the leaf of a Have
// whose claim does not mention it has no free x₀. A strip there offers
// x₀ again; where its binder has another type that is a second type
// for one name, which the Script's scope refuses (Script.Var), so the
// strip fixes the next name.

// TestFix_NameDeclaredAtAnotherType: Fix inside such a Have. The
// variable it fixes bears another name than the statement's, and a
// claim of the inner block spells both, each at its own type.
func TestFix_NameDeclaredAtAnotherType(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("R", MakeFun(numType, TypeBool))
	sec := ctx.Theorem("∀x:num. (∀n:num. R(n)) ⇒ R(x)", func(a *Argument, x Term, everywhere Fact) {
		a.Have("R follows from itself beside any predicate", "∀x:(num → bool). ∀n:num. x(n) ∧ R(n) ⇒ R(n)", Derive(func(d *Argument) {
			p := d.Fix("p")
			outer, _ := x.Core().AsVar()
			inner, _ := p.Core().AsVar()
			require.NotEqual(t, outer.Name(), inner.Name(), "the block fixed a second variable under the statement's name")
			require.True(t, inner.Type().Equals(MakeFun(numType, TypeBool)))
			d.Have("the statement's x and the block's p in one claim", "p(x) ∧ R(x) ⇒ R(x)", CnfRefute())
			d.Fix()
			both := d.Assume()
			d.Show("it is the second conjunct", By(both))
		}))
		a.Show("R holds everywhere", By(everywhere))
	})
	require.True(t, sec.Proved())
}

// TestUnpack_NameDeclaredAtAnotherType: the same leaf, a witness in
// place of a fixed variable — Unpack of an ∃-fact whose binder bears
// the statement's name at another type.
func TestUnpack_NameDeclaredAtAnotherType(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("R", MakeFun(numType, TypeBool))
	sec := ctx.Theorem("∀x:num. (∃x:(num → bool). x(0)) ∧ (∀n:num. R(n)) ⇒ R(x)", func(a *Argument, x Term, some, everywhere Fact) {
		a.Have("a predicate that holds at 0 or at 1", "∃y:(num → bool). y(0) ∨ y(1)", Derive(func(d *Argument) {
			w, at := d.Unpack(some)
			outer, _ := x.Core().AsVar()
			witness, _ := w.Core().AsVar()
			require.NotEqual(t, outer.Name(), witness.Name(), "the block took a witness under the statement's name")
			d.Show("the witness serves", By(at))
		}))
		a.Show("R holds everywhere", By(everywhere))
	})
	require.True(t, sec.Proved())
}

// TestFix_AVacuousBinder: a binder the statement's body does not
// mention is fixed like any other. The strip leaves a goal that holds
// no new variable, and the variable it fixed is still the one the
// parameter receives, declared under its minted name and aliased by the
// binder's: a closure binds `∀k y. …` with two term parameters whether
// or not the body reads y, and FixAs does inside a block.
func TestFix_AVacuousBinder(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("R", MakeFun(numType, TypeBool))
	sec := ctx.Theorem("∀k:num. ∀y:num. (∀n:num. R(n)) ⇒ R(k)", func(a *Argument, k, y Term, everywhere Fact) {
		outer, isVar := y.Core().AsVar()
		require.True(t, isVar)
		require.Equal(t, "y_0", string(outer.Name()))
		require.True(t, outer.Type().Equals(numType))
		require.True(t, a.Term("y").Core().Equals(y.Core()), "the binder's name reads as the variable fixed")

		a.Have("R at each m beside an unused index", "∀m:num. ∀z:num. R(m)", Derive(func(d *Argument) {
			d.FixAs[ext.Nat]()
			z := d.FixAs[ext.Nat]("w")
			inner, _ := z.Core().AsVar()
			require.Equal(t, "z_0", string(inner.Name()))
			require.True(t, d.Term("w").Core().Equals(z.Core()), "the surface name reads as the variable fixed")
			d.Show("it is the premise at m", By(everywhere))
		}))
		a.Show("R holds everywhere", By(everywhere))
	})
	require.True(t, sec.Proved())
}
