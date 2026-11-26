package engine

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/utils"
)

// TestTermSpecialize_TheServedSpellingOfASubscriptedBinder: a law
// stated `∀x₀:num` is printed so by every served statement, and its
// binder is the kernel's `x_0`. A term_specialize table names it either
// way; naming it both ways is refused, and an unknown name lists the
// binders in the spelling they are served in.
func TestTermSpecialize_TheServedSpellingOfASubscriptedBinder(t *testing.T) {
	scope := &dsl.ParseScope{ConstResolver: registryConstResolver, FreshenMetaLetters: true, Syntax: constSyntax()}
	law := dsl.ParsePropTextInScope("∀x₀:num. ∀n:num. x₀ + n = n + x₀", scope)
	require.Empty(t, law.Errors)
	goal := dsl.ParsePropTextInScope("k:num ⊢ k = k", scope)
	require.Empty(t, goal.Errors)
	e := newEngine(testEnv())

	none := utils.EmptyPredicate[core.VarType]
	for _, key := range []string{"x₀", "x_0"} {
		ws, _, _, err := e.resolveTermSpecializeWitnesses(law.Prop, map[string]string{key: "k"}, goal.Prop, nil, none)
		require.NoError(t, err, key)
		require.Len(t, ws, 1)
		require.Equal(t, "x_0", ws[0].name, "%q names the binder x_0", key)
	}

	_, _, _, err := e.resolveTermSpecializeWitnesses(law.Prop, map[string]string{"x₀": "k", "x_0": "k"}, goal.Prop, nil, none)
	require.EqualError(t, err, `term_specialize: "x_0" and "x₀" name one binder, x₀ — name it once`)

	_, _, _, err = e.resolveTermSpecializeWitnesses(law.Prop, map[string]string{"y": "k"}, goal.Prop, nil, none)
	require.ErrorContains(t, err, "available: [n x₀]")

	_, err = e.buildTermSpecializedLemma(law.Prop, map[string]string{"x₀": "k"}, goal.Prop, nil, none)
	require.NoError(t, err, "the rewrite-path door reads the table the same way")
}
