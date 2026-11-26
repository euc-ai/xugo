package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestTermText_MatchesGoExprForm is TermText's whole point: the text
// form and the Apply-spelling it replaces build the SAME term, so a
// site converts without moving anything the kernel or the CNF cache
// can see.
func TestTermText_MatchesGoExprForm(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	m := ctx.Var("m", dsl.NumType)
	n0 := ctx.Var("n_0", dsl.NumType)

	plus := func(x, y Term) Term { return ext.Apply(dsl.NatPlusMeta.Term(), x, y) }
	times := func(x, y Term) Term { return ext.Apply(dsl.NatStarMeta.Term(), x, y) }
	suc := func(x Term) Term { return ext.Apply(dsl.SUCMeta.Term(), x) }

	// MulSuc's outer bridge: suc(m + (m*n₀ + n₀)).
	want := suc(plus(m, plus(times(m, n0), n0)))
	got := ctx.TermText("suc(m + (m * n₀ + n₀))")

	require.True(t, want.AlphaEquals(got),
		"text and Go-expr forms must agree:\n  want %s\n  got  %s",
		ext.PrintTerm(want), ext.PrintTerm(got))
}

func TestTermAs_EmbedsNaturalsAtInt(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("a", dsl.NumType)
	ctx.Var("k", dsl.NumType)
	node := ctx.Theorem("a + k = k + a", func(c *Argument) {
		short := c.TermAs[dsl.Int]("a * k")
		long := c.TermAs[dsl.Int]("int_of_num(a * k)")
		require.True(t, short.Core().AlphaEquals(long.Core()))
		shortMonus := c.TermAs[dsl.Int]("a - k")
		longMonus := c.TermAs[dsl.Int]("int_of_num(a - k)")
		require.True(t, shortMonus.Core().AlphaEquals(longMonus.Core()))
		natural := c.TermAs[ext.Nat]("a * k")
		require.True(t, natural.Core().Type().Equals(dsl.NumType))
		c.Show("…", ByArith())
	})
	require.True(t, node.Proved())
}

// TestTermText_UnicodeSubscriptIsTheMintedName: `n₀` in the text and
// the `n_0` Script.Var registers are one name — the spelling the
// corpus's statement style uses for Skolem mints.
func TestTermText_UnicodeSubscriptIsTheMintedName(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	n0 := ctx.Var("n_0", dsl.NumType)
	require.True(t, n0.AlphaEquals(ctx.TermText("n₀")))
	require.True(t, n0.AlphaEquals(ctx.TermText("n_0")))
}

// TestTermText_UndeclaredFreePanics is the negative control for the
// contract: a name the scope never declared is a typo, not a fresh
// variable, and the panic names it rather than letting a wrong bridge
// term reach the leaf.
func TestTermText_UndeclaredFreePanics(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	ctx.Var("m", dsl.NumType)

	require.PanicsWithValue(t,
		`Script.TermText: "m + n₀": undeclared free [n_0:num] — declare via Script.Var, or check the spelling against the minted name (declared: [m])`,
		func() { ctx.TermText("m + n₀") })
}

// TestTermText_TextBoundNameIsNotUndeclared: a λ binds its own
// variable, so the undeclared-free check must not fire on it.
func TestTermText_TextBoundNameIsNotUndeclared(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	m := ctx.Var("m", dsl.NumType)

	got := ctx.TermText("λk:num. k + m")
	k := ext.Var("k", dsl.NumType)
	want := k.To(ext.Apply(dsl.NatPlusMeta.Term(), k, m))
	require.True(t, want.AlphaEquals(got),
		"want %s\n got %s", ext.PrintTerm(want), ext.PrintTerm(got))
}

// TestTermText_RejectsPropText: a Prop passed where a Term belongs
// gets the DSL's own diagnostic, not a confusing downstream failure.
func TestTermText_RejectsPropText(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	require.Panics(t, func() { ctx.TermText("⊢ T") })
}
