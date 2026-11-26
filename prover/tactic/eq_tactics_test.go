package tactic

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// An equation between two sides of one size rewrites in neither
// direction under the size-monotone guard alone: the larger side would
// go on the left, and neither is larger. The guard admits the rewrite
// where it settles against the context (settlesAgainstContext) — here
// the conclusion `y = face(X, n + 1, n, f(n - 1))`, rewritten by
// `f(n - 1) = deg(X, n, n, y)`, becomes the symmetric of the resident
// `face(X, n + 1, n, deg(X, n, n, y)) = y`, and the leaf closes. A
// rewrite of one size that settles nothing is still refused.
func TestEqSimplify_EqualSizedEquationSettlesAgainstTheContext(t *testing.T) {
	A := core.MakeVarType("A")
	R := ext.MakeType("zz_eq_rec", A)
	num := dsl.NumType
	op := MakeFun(R, MakeFun(num, MakeFun(num, MakeFun(A, A))))
	face := core.MakeConstTerm(core.MakeConstMeta("zz_eq_face", op), op)
	deg := core.MakeConstTerm(core.MakeConstMeta("zz_eq_deg", op), op)
	X, y := Var("X", R), Var("y", A)
	f := Var("f", MakeFun(num, A))
	n := Var("n", num)
	one := omega.Numeral(1)
	previous := ext.Apply(dsl.NatMinusMeta.Term(), n, one)
	next := ext.Apply(dsl.NatPlusMeta.Term(), n, one)
	fPrevious, degenerate := ext.Apply(f, previous), ext.Apply(deg, X, n, n, y)
	require.Equal(t, fPrevious.Size(), degenerate.Size(), "the two spellings of the simplex have one size")

	closes := MakeProp(core.Eq(y, ext.Apply(face, X, next, n, fPrevious)),
		core.Eq(fPrevious, degenerate),
		core.Eq(ext.Apply(face, X, next, n, degenerate), y))
	sg := TrivialSimplifyTactic(closes)
	require.NotNil(t, sg, "the equation rewrites the conclusion into the symmetric of a hypothesis")
	require.Equal(t, 0, sg.Size(), "and the leaf closes: %s", sg)

	P := Var("P", MakeFun(A, core.TypeBool()))
	settlesNothing := MakeProp(ext.Apply(P, fPrevious), core.Eq(fPrevious, degenerate))
	require.Nil(t, TrivialSimplifyTactic(settlesNothing), "a rewrite of one size that settles nothing is refused")
}
