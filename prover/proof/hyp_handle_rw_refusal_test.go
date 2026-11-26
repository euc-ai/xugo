package proof

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
)

// recoveredText runs f and returns the text of the panic it raises.
func recoveredText(t *testing.T, f func()) (msg string) {
	t.Helper()
	defer func() {
		r := recover()
		require.NotNil(t, r, "expected a panic")
		msg = fmt.Sprint(r)
	}()
	f()
	return ""
}

// A hypothesis rewrite's refusal names the verb the author wrote and
// says why the step found nothing to do: `p + z = p` reversed rewrites
// p to a term holding p, which the step refuses as self-expanding. The
// forward orientation of the same equation rewrites.
func TestHypHandle_RwRevRefusalNamesTheVerbAndTheSelfExpansion(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	msg := recoveredText(t, func() {
		ctx.Theorem("∀P:num → bool. ∀p z:num. p + z = p ⇒ P(p + z) ⇒ P(p)",
			func(a *Argument, P *ext.Expr[natSet], p, z *ext.Expr[ext.Nat], eq, held Fact) {
				a.Do(eq.RwRev())
				a.Show("after the rewrite", By(held))
			})
	})
	require.Contains(t, msg, `.RwRev: the step did not apply to its hypothesis`)
	require.Contains(t, msg, "the rewrite p₀ → p₀ + z₀ is self-expanding (its right side occurs in the other)")

	sec := ctx.Theorem("∀P:num → bool. ∀p z:num. p + z = p ⇒ P(p) ⇒ P(p + z)",
		func(a *Argument, P *ext.Expr[natSet], p, z *ext.Expr[ext.Nat], eq, held Fact) {
			a.Do(eq.Rw())
			a.Show("after the rewrite", By(held))
		})
	require.True(t, sec.Proved())
}
