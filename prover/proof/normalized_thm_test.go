package proof

import (
	"testing"

	"github.com/stretchr/testify/assert"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// The install form of a dep keeps the dep's own binder order: a witness
// tuple grounds it positionally in the order the statement was written,
// whatever prefix order Normalize's canonical labeling chose.
func TestStatedPrefixOrderFollowsTheStatement(t *testing.T) {
	m := ext.Var("m", TypeInd)
	n := ext.Var("n", TypeInd)
	p := ext.Var("p", TypeInd)
	le := ext.Var("le", MakeFun(TypeInd, TypeInd, TypeBool))
	// ∀m n p. le(m,n) ∧ le(n,p) ⇒ le(m,p)
	stated := core.TestThm(ForAll(m, n, p)(le.Apply(m, n).And(le.Apply(n, p)).Imply(le.Apply(m, p))).Core())
	norm, _ := Normalize(stated)
	install := statedPrefixOrder(stated, norm)

	vars, _ := DecomposesFORALL(install.Conclusion())
	got := make([]string, vars.Size())
	for i := range got {
		got[i] = string(vars.Ind(i).Name())
	}
	// `le` is free in the statement and closed by Normalize, so the
	// statement is not a pure prefix over the same binders: the install
	// form keeps Normalize's order.
	assert.Equal(t, install.Conclusion().Equals(norm.Conclusion()), true, "free variable closed: no reorder")
	_ = got

	// Closed over le as well: a pure ∀-prefix, reordered to the statement.
	closed := core.TestThm(ForAll(le, m, n, p)(le.Apply(m, n).And(le.Apply(n, p)).Imply(le.Apply(m, p))).Core())
	normClosed, _ := Normalize(closed)
	installClosed := statedPrefixOrder(closed, normClosed)
	vars2, _ := DecomposesFORALL(installClosed.Conclusion())
	got2 := make([]string, vars2.Size())
	for i := range got2 {
		got2[i] = string(vars2.Ind(i).Name())
	}
	assert.Equal(t, []string{"le", "m", "n", "p"}, got2)
	renorm, _ := Normalize(installClosed)
	assert.Equal(t, normClosed.AlphaKey(), renorm.AlphaKey(), "the install form is the same theorem")

	// A statement with binders nested under an implication is not a pure
	// prefix either: Normalize pulls x and s up, and the install keeps
	// Normalize's order for them.
	f := ext.Var("f", MakeFun(TypeInd, TypeInd))
	b := ext.Var("b", TypeInd)
	x := ext.Var("x", TypeInd)
	s := ext.Var("s", TypeInd)
	R := ext.Var("R", MakeFun(TypeInd, TypeInd, TypeBool))
	nested := core.TestThm(ForAll(R, f, b)(R.Apply(b, b).Imply(ForAll(x, s)(R.Apply(f.Apply(x), s)))).Core())
	normNested, _ := Normalize(nested)
	assert.True(t, statedPrefixOrder(nested, normNested).Conclusion().Equals(normNested.Conclusion()), "nested binders: no reorder")

}

// The install form also keeps the dep's own binder SHARING: Normalize has
// the clauses of a block share binders by canonical rank, so
// `∀x y. x ≤ max(x,y) ∧ y ≤ max(x,y)` becomes `∀y x. y ≤ max(y,x) ∧ y ≤
// max(x,y)` — the same theorem, but a witness tuple grounding it under the
// stated prefix no longer reads `y ≤ max(x,y)`. The install form's clauses
// are the statement's.
func TestNormalizedFormKeepsTheStatementsSharing(t *testing.T) {
	x, y := ext.Var("x", TypeInd), ext.Var("y", TypeInd)
	mx := ext.Var("mx", MakeFun(TypeInd, TypeInd, TypeInd))
	le := ext.Var("le", MakeFun(TypeInd, TypeInd, TypeBool))
	first := le.Apply(x, mx.Apply(x, y))
	second := le.Apply(y, mx.Apply(x, y))
	stated := core.TestThm(ForAll(mx, le, x, y)(first.And(second)).Core())
	install := NormalizedForm(stated)
	vars, body := DecomposesFORALL(install.Conclusion())
	names := make([]string, vars.Size())
	for i := range names {
		names[i] = string(vars.Ind(i).Name())
	}
	assert.Equal(t, []string{"mx", "le", "x", "y"}, names)
	var clauses []string
	for _, c := range DecomposesAND(body) {
		clauses = append(clauses, ext.PrintTerm(c))
	}
	assert.ElementsMatch(t, []string{ext.PrintTerm(first), ext.PrintTerm(second)}, clauses, "the clauses as stated")
	norm, _ := Normalize(stated)
	renorm, _ := Normalize(install)
	assert.Equal(t, norm.AlphaKey(), renorm.AlphaKey(), "the install form is the same theorem")
}
