package engine

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"
)

// TestByArith_CastOfASum: a cast of a num sum, product or successor
// written in a real or int atom is read as the sum or product of the
// casts (omega's cast basis), so `&m` and `&(m + 1)` are one unknown and a
// constant apart. Each row is linear once the cast is read so, and was
// outside the closer while `&(m + 1)` was an unknown of its own.
func TestByArith_CastOfASum(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	strips := []string{"strip_quant", "strip_imp"}
	runByArithRows(t, byArithEngine(t), []byArithRow{
		{"a real bound stepped by one",
			"∀m:num. ∀A B:real. &m ≤ A ∧ A + &1 < B ⇒ &(m + 1) < B", strips, []int{0}},
		{"a successor",
			"∀n:num. ∀x:real. x < &n ⇒ x < &(suc(n))", strips, []int{0}},
		{"a product of two sums",
			"∀j k:num. ∀x:real. x ≤ &j * &k ⇒ x ≤ &((j + 1) * (k + 1))", strips, []int{0}},
		{"a product keeps its sign",
			"∀j k:num. ∀x:real. x < &0 ⇒ x < &(j * k)", strips, []int{0}},
		{"over the integers",
			"∀m:num. ∀a b:int. &m ≤ a ∧ a + &1 < b ⇒ &(m + 1) < b", strips, []int{0}},
	})
}

// TestByArith_CastOfATruncatedDifference: the cast is a homomorphism of
// + and * alone. `&(m - 1)` is not `&m - &1` — num's difference stops at
// zero — and stays the unknown it was: the closer does not prove the
// statement the false reading would.
func TestByArith_CastOfATruncatedDifference(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	zero := 0
	sid, gid := bareArithLeaf(t, e, "∀m:num. ∀A:real. &m ≤ A ⇒ &(m - 1) + &1 ≤ A", "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
		GoalID: gid, Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: &zero}}},
	})
	require.NoError(t, err)
	require.False(t, res.Success, "at m = 0 the left side is &1 and &0 ≤ A does not bound it")
}
