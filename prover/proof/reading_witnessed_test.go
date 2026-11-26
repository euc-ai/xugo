package proof

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A law read under a resident hypothesis and grounded at a tuple is the
// sequent `S(m) ⊢ ∀k n. P(m, k, n) ∧ R(m, k, n)`: its hypothesis is the
// leaf's and its free variable m is the leaf's own term. With a
// conjunctive matrix the By grounds a premise's clause form, and the
// closed clause form of this sequent would ∀-close m and fold S(m)
// back in as an antecedent — the law the reading was taken from, its
// instance lost — so the close would need the refuter. Grounded as
// stated, the reading is `P(m, k₀, n₀) ∧ R(m, k₀, n₀)` under S(m), and
// the leaf closes with no key, live and from an empty store. In the
// second case the inner binder bears the instance's name at another
// type, as `∀L:field_on(A). ∀K M:set(A)` read at a field named M does:
// the names play no part.
func TestBy_WitnessedConjunctiveReadingKeepsItsInstance(t *testing.T) {
	for _, inner := range []ext.TermName{"n", "m"} {
		live := groundTestEnv(t)
		ctx := NewScript(live)
		ind := TypeInd
		set := MakeFun(ind, TypeBool)
		pred := MakeFun(set, MakeFun(ind, MakeFun(ind, TypeBool)))
		live.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_reading_s", MakeFun(set, TypeBool)))
		live.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_reading_p", pred))
		live.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_reading_r", pred))
		S := ctx.Const("zz_reading_s", MakeFun(set, TypeBool))
		P := ctx.Const("zz_reading_p", pred)
		R := ctx.Const("zz_reading_r", pred)

		m := Var("m", set)
		k := Var("k", ind)
		n := Var(inner, ind)
		k0 := Var("k₀", ind)
		n0 := Var("n₀", ind)
		reading := core.MakeProp(
			ext.ForAll(k, n)(P.Apply(m, k, n).And(R.Apply(m, k, n))).Core(),
			S.Apply(m).Core())
		goal := prop.MakeProp(P.Apply(m, k0, n0).Core(), S.Apply(m).Core())
		spec := BySpec{Premises: []ByPremiseSpec{{
			Install:      reading,
			ReadingUnder: true,
			Witnesses:    []Term{k0, n0},
			Describe:     "the law read under S(m), at (k₀, n₀)",
		}}}

		st := newGroundByStore()
		st.wire(live, true)
		require.True(t, ApplyByStep(CreateGoalStack(goal), live, t.Context(), spec),
			"inner binder %s: the reading at its tuple closes the leaf", inner)
		assert.Empty(t, st.Proofs(), "inner binder %s: keyless — the reading kept its instance m", inner)

		strict := groundTestEnv(t)
		newGroundByStore().wire(strict, true)
		strict.RequireCNFCacheHit = true
		require.True(t, ApplyByStep(CreateGoalStack(goal), strict, t.Context(), spec),
			"inner binder %s: from an empty store the close reaches no refute", inner)
	}
}
