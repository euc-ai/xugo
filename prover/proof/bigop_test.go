package proof

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dimtypes"
	"github.com/euc-ai/xugo/ext/dsl"
)

// VecFixAs digs the goal's leading binder as an anchored vector: the
// same value VecAs would rebuild from the binder's name, without the
// name being spelled a second time.
func TestVecFixAs_DigsAnAnchoredVector(t *testing.T) {
	ctx := newVecTestScript()
	sec := ctx.Theorem(vecTestStatement,
		func(a *Argument, n *ext.Expr[ext.Nat]) {
			u := a.VecFixAs[dsl.Real, dimtypes.DimN]()
			mem := a.Assume()
			require.True(t, u.Anchored())
			require.True(t, u.Dim().Equals(n.Core()), "anchored at %s, want the fixed %s", ext.PrintTerm(u.Dim()), ext.PrintTerm(n))
			require.True(t, u.Core().Equals(a.VecAs[dsl.Real, dimtypes.DimN]("u").Core()), "the dug vector is the binder VecAs names")
			// The membership pairs with it: the fact names this vector.
			Inhabit(u, mem)
			a.Take(u)
			a.Show("the vector itself", By(mem))
		})
	require.True(t, sec.Proved())
}

// BigOpAs refuses what is not a big-operator application, naming the
// head. (The positive path — a Σ read as its range and summand and
// handed to the sum laws — is exercised by the corpus: every
// `BigOpAs` site in library/proofs replays under the recorder.)
func TestBigOpAs_RefusesANonBigOp(t *testing.T) {
	ctx := newVecTestScript()
	refused := func(text, want string) {
		t.Helper()
		defer func() {
			r := recover()
			require.NotNil(t, r, "%s was read as a big operator", text)
			require.Contains(t, fmt.Sprint(r), want)
		}()
		ctx.Theorem(vecTestStatement,
			func(a *Argument, n *ext.Expr[ext.Nat], u *dimtypes.Vec[dsl.Real, dimtypes.DimN], mem Fact) {
				a.BigOpAs[ext.Nat, dsl.Real](text)
			})
	}
	// A variable head is no constant, so no syntax can declare it.
	refused("P(n, u)", "is not a constant")
	// A constant head the scope declares no big operator at.
	refused("u(n) + u(n)", "declares no big operator at")
}
