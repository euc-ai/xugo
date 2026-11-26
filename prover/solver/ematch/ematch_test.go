package ematch

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// zkTest is a test-local opaque unary const: the trigger walkers want a
// CONST-headed applied subterm, which a free-var-headed fixture cannot
// supply.
var zkTest = core.NewConstDef(ext.Var("zzex", TypeInd).To(ext.Var("zzex", TypeInd)), "zz_ematch_k")

func planFor(t *testing.T, plans []Plan, want ...core.Term) Plan {
	t.Helper()
	for _, p := range plans {
		if len(p.Witnesses) != len(want) {
			continue
		}
		ok := true
		for i := range want {
			if !p.Witnesses[i].AlphaEquals(want[i]) {
				ok = false
				break
			}
		}
		if ok {
			return p
		}
	}
	t.Fatalf("no plan at the wanted tuple among %d plan(s)", len(plans))
	return Plan{}
}

// TestGroundPlans_PrenexExistential is the normalized shape of every
// lemma with an existential hypothesis — the pinning equation sits
// under a leading ∃ in the matrix:
//
//	∀x y. ∃z. (¬P(x) ∨ zk(y) = g(x, y) ∨ Q(z)),  P(a)  ⊢  zk(b) = g(a, b)
//
// The equation is an L1 trigger over the conclusion and pins both
// binders; the ∃-bound z is never a witness, and an atom mentioning it
// (Q(z)) is not a trigger.
func TestGroundPlans_PrenexExistential(t *testing.T) {
	ind2 := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	g := ext.Var("g", ind2)
	P := ext.Var("P", core.MakeFun(TypeInd, core.TypeBool()))
	Q := ext.Var("Q", core.MakeFun(TypeInd, core.TypeBool()))
	a, b := ext.Var("a", TypeInd), ext.Var("b", TypeInd)
	x, y, z := ext.Var("x", TypeInd), ext.Var("y", TypeInd), ext.Var("z", TypeInd)
	zk := ext.WrapTerm(zkTest)

	matrix := ext.Not(P.Apply(x)).Or(zk.Apply(y).Eq(g.Apply(x, y))).Or(Q.Apply(z))
	wide := ext.ForAll(x, y)(ext.Exists(z)(matrix))
	goal := prop.MakeProp(zk.Apply(b).Eq(g.Apply(a, b)).Core(), wide.Core(), P.Apply(a).Core())

	plans := GroundPlans(goal)
	pl := planFor(t, plans, a.Core(), b.Core())
	require.True(t, pl.FullyMatched(), "both binders pinned by the match under the ∃")
	require.True(t, pl.Valid(wide.Core()))
	for _, p := range plans {
		for _, w := range p.Witnesses {
			require.False(t, w.AlphaEquals(z.Core()), "the ∃-bound variable is never a witness")
		}
	}
}

// TestGroundPlans_GuardedLemma is the stated shape of the same law —
// content behind an antecedent:
//
//	∀x. P(x) ⇒ ∀y. zk(y) = g(x, y),  P(a)  ⊢  zk(b) = g(a, b)
//
// Read through the guard the premise has two binders, and the plan
// pins both.
func TestGroundPlans_GuardedLemma(t *testing.T) {
	ind2 := core.MakeFun(TypeInd, core.MakeFun(TypeInd, TypeInd))
	g := ext.Var("g", ind2)
	P := ext.Var("P", core.MakeFun(TypeInd, core.TypeBool()))
	a, b := ext.Var("a", TypeInd), ext.Var("b", TypeInd)
	x, y := ext.Var("x", TypeInd), ext.Var("y", TypeInd)
	zk := ext.WrapTerm(zkTest)

	guarded := ext.ForAll(x)(P.Apply(x).Imply(ext.ForAll(y)(zk.Apply(y).Eq(g.Apply(x, y)))))
	goal := prop.MakeProp(zk.Apply(b).Eq(g.Apply(a, b)).Core(), guarded.Core(), P.Apply(a).Core())

	binders, _ := StripGuardedForalls(guarded.Core())
	require.Len(t, binders, 2, "the binder behind the guard is read")
	outer, _ := StripLeadingForalls(guarded.Core())
	require.Len(t, outer, 1, "the surface read is unchanged")

	pl := planFor(t, GroundPlans(goal), a.Core(), b.Core())
	require.True(t, pl.FullyMatched())
	require.True(t, pl.Valid(guarded.Core()))
}

// TestGroundPlans_ViaConclusion: a plan says which part of the
// hypothesis its witnesses came from. Against the goal `zk(zk(c)) = b`
// the law `∀d. zk(d) = a ⇒ zk(zk(d)) = b` grounds at c through its
// CONCLUSION alone, and at e through its antecedent, which the resident
// `zk(e) = a` triggers.
func TestGroundPlans_ViaConclusion(t *testing.T) {
	a, b := ext.Var("a", TypeInd), ext.Var("b", TypeInd)
	c, e := ext.Var("c", TypeInd), ext.Var("e", TypeInd)
	d := ext.Var("d", TypeInd)
	zk := ext.WrapTerm(zkTest)

	law := ext.ForAll(d)(zk.Apply(d).Eq(a).Imply(zk.Apply(zk.Apply(d)).Eq(b)))
	goal := prop.MakeProp(zk.Apply(zk.Apply(c)).Eq(b).Core(), law.Core(), zk.Apply(e).Eq(a).Core())

	plans := GroundPlans(goal)
	atC := planFor(t, plans, c.Core())
	require.True(t, atC.FullyMatched())
	require.True(t, atC.ViaConclusion(), "the goal spells the conclusion at c; no antecedent took part")
	atE := planFor(t, plans, e.Core())
	require.True(t, atE.FullyMatched())
	require.False(t, atE.ViaConclusion(), "the resident `zk(e) = a` triggered the antecedent")
}
