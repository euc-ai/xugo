package prop

import (
	"testing"

	"github.com/stretchr/testify/require"
)

// TestSkolemEqBridge: a fact `∀x̄. ∃y. P` and the statement of its choice
// function, `∃f. ∀x̄. P[f(x̄)]`, are one statement through the Skolem
// stage, and the bridge proves the equation between them — whatever the
// two call their bound variables, in whatever order the matrix stands,
// and where the two arguments differ in type, so that the pre-CNF form
// reorders the ∀-block. The function takes its arguments in the order
// the fact binds them: a statement that writes them the other way round
// is another statement to the bridge.
func TestSkolemEqBridge(t *testing.T) {
	x, n := Var("x", TypeA), Var("n", TypeInd)
	y, z := Var("y", TypeA), Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, MakeFun(TypeInd, MakeFun(TypeA, TypeBool))))
	G := Var("G", MakeFun(TypeA, MakeFun(TypeInd, TypeBool)))
	R := Var("R", MakeFun(TypeA, MakeFun(TypeInd, TypeA)))
	S := Var("S", MakeFun(TypeInd, MakeFun(TypeA, TypeA)))

	fact := ForAll(x, n)(G.Apply(x, n).Imply(Exists(y)(P.Apply(x, n, y).And(G.Apply(y, n)))))
	rxn := R.Apply(x, n)
	chosen := Exists(R)(ForAll(x, n)(G.Apply(x, n).Imply(P.Apply(x, n, rxn).And(G.Apply(rxn, n)))))

	bridge := SkolemEqBridge(fact, chosen)
	require.NotNil(t, bridge, "the fact and the statement of its choice function share no form")
	require.Zero(t, bridge.NumHyps())
	require.True(t, Lhs(bridge).AlphaEquals(fact) && Rhs(bridge).AlphaEquals(chosen))
	require.True(t, bridge.EqMP(Assume(fact)).Conclusion().AlphaEquals(chosen))

	// The matrix in the other order, the witness under another name.
	reordered := ForAll(x, n)(G.Apply(x, n).Imply(Exists(z)(G.Apply(z, n).And(P.Apply(x, n, z)))))
	require.NotNil(t, SkolemEqBridge(reordered, chosen))

	// The arguments the other way round: S(n, x) is not the choice
	// function of a fact that binds x before n.
	snx := S.Apply(n, x)
	swapped := Exists(S)(ForAll(x, n)(G.Apply(x, n).Imply(P.Apply(x, n, snx).And(G.Apply(snx, n)))))
	require.Nil(t, SkolemEqBridge(fact, swapped))

	// A weaker fact is not the statement.
	weaker := ForAll(x, n)(G.Apply(x, n).Imply(Exists(y)(P.Apply(x, n, y))))
	require.Nil(t, SkolemEqBridge(weaker, chosen))
}
