package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
)

// Take on a goal `∃!x. P(x)` leaves one goal, the body at the witness
// together with the claim that the body holds of nothing else, which
// SplitConj opens into the two obligations.
func TestTake_UniqueExistence(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem(dsl.Statement{
			Binders:    "∀J P:(num → bool). ∀v:num.",
			Hypotheses: []string{"J(v)", "P(v)", "∀y:num. J(y) ∧ P(y) ⇒ y = v"},
			Conclusion: "∃!x:num. J(x) ∧ P(x)",
		},
			func(a *Argument, J, P *ext.Expr[natSet], v *ext.Expr[ext.Nat], jv, pv, only Fact) {
				a.Take(v)
				a.Do(SplitConj(
					MakeCase("the body holds at the witness", By(jv, pv)),
					MakeCase("and of nothing else", By(only))))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Unpack on a fact `∃!x. P(x)` opens it at its definition and hands
// over the witness with the fact that P holds of exactly it,
// `∀y. P(y) ⇔ x = y`: the fact unfolded at ∃! and then unpacked hands
// over the same, by the same steps.
func TestUnpack_UniqueExistence(t *testing.T) {
	statement := dsl.Statement{
		Binders:    "∀P:(num → bool). ∀u v:num.",
		Hypotheses: []string{"∃!x:num. P(x)", "P(u)", "P(v)"},
		Conclusion: "u = v",
	}
	var read, spelled string
	for _, unpack := range []struct {
		form *string
		open func(a *Argument, unique Fact) Fact
	}{
		{&read, func(a *Argument, unique Fact) Fact {
			_, only := a.Unpack(unique, "c")
			return only
		}},
		{&spelled, func(a *Argument, unique Fact) Fact {
			_, only := a.Unpack(a.Unfolded(unique, uniqueExistence), "c")
			return only
		}},
	} {
		ctx := NewScript(makeStepTestEnv())
		sec := provesInHand(t, func() *GoalStackNode {
			return ctx.Theorem(statement,
				func(a *Argument, P *ext.Expr[natSet], u, v *ext.Expr[ext.Nat], unique, pu, pv Fact) {
					only := unpack.open(a, unique)
					*unpack.form = ext.PrintTerm(a.cur.Goal.Hyp(only.handle.resolveOrPanic("test", a.cur)))
					a.Show("both are the one witness", By(only, pu, pv))
				})
		})
		require.True(t, sec != nil && sec.Proved())
	}
	require.Equal(t, spelled, read, "Unpack reads the fact as its unfolding spells it")
	require.Contains(t, read, "⇔", "the witness's property holds of exactly it: %s", read)
}
