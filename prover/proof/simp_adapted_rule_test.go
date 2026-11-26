package proof

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A polymorphic Simp rule is adapted to the type instances the goal
// exhibits, and to those the rewrite exposes, as the session's
// simp_with adapts its rules: a rule stated at the letter A fires at
// ind without the author pinning the instance. A rule with nothing to
// rewrite stays a legal member of the list.

// adaptedEnv: the polymorphic f : A → A with its law `∀x:A. f(x) = x`
// served at the letter A, the two-letter h : A → B → A with `∀x y.
// h(x, y) = x`, the monomorphic `∀x:ind. k(x) = c` and `∀x:ind. e(x) =
// f(x)` whose unfold exposes f at ind.
type adaptedEnv struct {
	*simpStatedEnv
	fAtInd, hAtInd, e *ext.TermWrapper
}

func makeAdaptedEnv() *adaptedEnv {
	env := makeSimpStatedEnv()
	typeB := core.MakeVarType("B")
	fMeta := core.MakeConstMeta("simpPolyF", MakeFun(core.TypeA(), core.TypeA()))
	hMeta := core.MakeConstMeta("simpPolyH", MakeFun(core.TypeA(), MakeFun(typeB, core.TypeA())))
	eMeta := core.MakeConstMeta("simpExpose", MakeFun(TypeInd, TypeInd))
	env.ctx.Env.ProofService.LoadOrStoreConstMeta(fMeta)
	env.ctx.Env.ProofService.LoadOrStoreConstMeta(hMeta)
	env.ctx.Env.ProofService.LoadOrStoreConstMeta(eMeta)

	xa, yb := Var("x", core.TypeA()), Var("y", typeB)
	fAtA := ext.WrapTerm(core.MakeConstTerm(fMeta, MakeFun(core.TypeA(), core.TypeA())))
	serveThm(env.ctx, "zz_simp_poly", core.TestThm(ext.ForAll(xa)(fAtA.Apply(xa).Eq(xa)).Core()))
	hAtAB := ext.WrapTerm(core.MakeConstTerm(hMeta, MakeFun(core.TypeA(), MakeFun(typeB, core.TypeA()))))
	serveThm(env.ctx, "zz_simp_poly_two", core.TestThm(ext.ForAll(xa, yb)(hAtAB.Apply(xa, yb).Eq(xa)).Core()))

	x := Var("x", TypeInd)
	fAtInd := ext.WrapTerm(core.MakeConstTerm(fMeta, MakeFun(TypeInd, TypeInd)))
	e := ext.WrapTerm(core.MakeConstTerm(eMeta, MakeFun(TypeInd, TypeInd)))
	serveThm(env.ctx, "zz_simp_k", core.TestThm(ext.ForAll(x)(env.k.Apply(x).Eq(env.c)).Core()))
	serveThm(env.ctx, "zz_simp_expose", core.TestThm(ext.ForAll(x)(e.Apply(x).Eq(fAtInd.Apply(x))).Core()))
	return &adaptedEnv{
		simpStatedEnv: env,
		fAtInd:        fAtInd,
		hAtInd:        ext.WrapTerm(core.MakeConstTerm(hMeta, MakeFun(TypeInd, MakeFun(TypeInd, TypeInd)))),
		e:             e,
	}
}

// simpLeaves runs Simp on a fresh section over goal and returns the
// leaves it leaves.
func (e *adaptedEnv) simpLeaves(goal core.Term, rules ...SimpRule) []*GoalStackNode {
	sec := e.ctx.Section(prop.MakeProp(goal))
	sec.Do(Simp(rules...))
	return sec.UnsolvedLeaves()
}

// The rule at the letter A fires at ind on its own.
func TestSimp_AdaptsAPolymorphicRuleToTheGoalsInstance(t *testing.T) {
	e := makeAdaptedEnv()
	leaves := e.simpLeaves(e.Q.Apply(e.fAtInd.Apply(e.a)).Core(), Fwd(depName("zz_simp_poly")))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.a).Core()),
		"got %s", ext.PrintTerm(leaves[0].Goal.Conclusion()))
}

// Beside a sibling that fires as written, the polymorphic rule fires at
// the goal's instance too, and nothing of its redex is left in the
// residual.
func TestSimp_AdaptsBesideASiblingRule(t *testing.T) {
	e := makeAdaptedEnv()
	leaves := e.simpLeaves(e.Q.Apply(e.fAtInd.Apply(e.k.Apply(e.a))).Core(), Fwd(depName("zz_simp_k")), Fwd(depName("zz_simp_poly")))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.c).Core()),
		"got %s", ext.PrintTerm(leaves[0].Goal.Conclusion()))
}

// An instance the goal does not exhibit until an earlier rule's unfold
// exposes it is adapted to in the same step: e(a) unfolds to f(a) at
// ind, and the rule at A then fires there.
func TestSimp_AdaptsToAnInstanceTheRewriteExposes(t *testing.T) {
	e := makeAdaptedEnv()
	leaves := e.simpLeaves(e.Q.Apply(e.e.Apply(e.a)).Core(), Fwd(depName("zz_simp_expose")), Fwd(depName("zz_simp_poly")))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.a).Core()),
		"got %s", ext.PrintTerm(leaves[0].Goal.Conclusion()))
}

// Two letters at one type — the instance that is not injective on the
// rule's letters, module_on at B := A — is an instance like any other.
func TestSimp_AdaptsARuleWithTwoLettersAtOneType(t *testing.T) {
	e := makeAdaptedEnv()
	leaves := e.simpLeaves(e.Q.Apply(e.hAtInd.Apply(e.a, e.a)).Core(), Fwd(depName("zz_simp_poly_two")))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.a).Core()),
		"got %s", ext.PrintTerm(leaves[0].Goal.Conclusion()))
}

// At a hypothesis the rules are adapted the same way.
func TestSimpAt_AdaptsAPolymorphicRuleAtAHypothesis(t *testing.T) {
	e := makeAdaptedEnv()
	sec := e.ctx.Section(prop.MakeProp(e.P.Apply(e.k).Core(), e.Q.Apply(e.fAtInd.Apply(e.a)).Core()))
	sec.Do(SimpAt(0, Fwd(depName("zz_simp_poly"))))
	leaves := sec.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	require.Equal(t, 1, leaves[0].Goal.NumHyps())
	require.True(t, leaves[0].Goal.Hyp(0).AlphaEquals(e.Q.Apply(e.a).Core()),
		"got %s", ext.PrintTerm(leaves[0].Goal.Hyp(0)))
}

// A polymorphic rule with nothing to rewrite — no instance of it fires
// on the goal or the residual — stays a legal member of the list: a
// rule set is passed whole, and not every rule of it fires at every
// site.
func TestSimp_AllowsAPolymorphicRuleWithNothingToRewrite(t *testing.T) {
	e := makeAdaptedEnv()
	leaves := e.simpLeaves(e.Q.Apply(e.k.Apply(e.a)).Core(), Fwd(depName("zz_simp_k")), Fwd(depName("zz_simp_poly")))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.c).Core()))
}

// SimpAll reads every target for a rule refused as self-embedding: here
// the left side of a served rule stands in a hypothesis, not the conclusion.
func TestSimpAll_NamesARefusedRuleAtAHypothesis(t *testing.T) {
	e := makeAdaptedEnv()
	x := Var("x", TypeInd)
	serveThm(e.ctx, "zz_simp_embed", core.TestThm(ext.ForAll(x)(e.k.Apply(x).Eq(e.e.Apply(e.k.Apply(e.e.Apply(x))))).Core()))
	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(e.a).Core(), e.Q.Apply(e.k.Apply(e.a)).Core()))
	requirePanicContains(t, "Refused as a rewrite", func() { sec.Do(SimpAll(Fwd(depName("zz_simp_embed")))) })
}

// A rule set that feeds itself through two rules, neither embedding
// itself, is cut by the divergence whistle. The panic says that the rule
// set was cut and at which firing, not that no rule fired, and nothing
// is committed: at the conclusion, and at a hypothesis among SimpAll's
// targets.
func TestSimp_NamesARuleSetCutAsDivergent(t *testing.T) {
	e := makeAdaptedEnv()
	x := Var("x", TypeInd)
	serveThm(e.ctx, "zz_simp_feed_out", core.TestThm(ext.ForAll(x)(e.k.Apply(x).Eq(e.e.Apply(x))).Core()))
	serveThm(e.ctx, "zz_simp_feed_back", core.TestThm(ext.ForAll(x)(e.e.Apply(x).Eq(e.fAtInd.Apply(e.k.Apply(x)))).Core()))
	feed := []SimpRule{Fwd(depName("zz_simp_feed_out")), Fwd(depName("zz_simp_feed_back"))}
	redex := e.Q.Apply(e.k.Apply(e.a)).Core()

	sec := e.ctx.Section(prop.MakeProp(redex))
	requirePanicContains(t, "Simp: the rule set was cut as divergent on", func() { sec.Do(Simp(feed...)) })
	require.True(t, sec.UnsolvedLeaves()[0].Goal.Conclusion().AlphaEquals(redex), "nothing is committed")
	sec = e.ctx.Section(prop.MakeProp(redex))
	requirePanicContains(t, "The divergence whistle cut the rewrite at firing", func() { sec.Do(Simp(feed...)) })

	sec = e.ctx.Section(prop.MakeProp(e.Q.Apply(e.a).Core(), redex))
	requirePanicContains(t, "SimpAll: the rule set was cut as divergent on a target of", func() { sec.Do(SimpAll(feed...)) })

	// Either rule alone terminates and is no cut.
	leaves := e.simpLeaves(redex, Fwd(depName("zz_simp_feed_out")))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(e.Q.Apply(e.e.Apply(e.a)).Core()))
}

// The negative control: a rule with no redex at any instance fires
// nowhere, and the refusal names no instance.
func TestSimp_NoRuleFiredWhenNoInstanceHasARedex(t *testing.T) {
	e := makeAdaptedEnv()
	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(e.k.Apply(e.a)).Core()))
	requirePanicContains(t, "Simp: no rule fired", func() {
		sec.Do(Simp(Fwd(depName("zz_simp_poly"))))
	})
	sec = e.ctx.Section(prop.MakeProp(e.Q.Apply(e.k.Apply(e.a)).Core()))
	defer func() {
		r := recover()
		require.NotNil(t, r)
		require.NotContains(t, sprintAny(r), "polymorphic")
	}()
	sec.Do(Simp(Fwd(depName("zz_simp_poly"))))
}

func TestSimp_CompletesFiniteInstances(t *testing.T) {
	e := makeAdaptedEnv()
	var goal, want core.Term
	for i := 0; i < 24; i++ {
		ty := core.MakeVarType(core.TypeName(fmt.Sprintf("T%d", i)))
		f := e.ctx.Const("simpPolyF", MakeFun(ty, ty))
		x := ext.WrapTerm(Var(core.TermName(fmt.Sprintf("x%d", i)), ty))
		q := ext.WrapTerm(Var(core.TermName(fmt.Sprintf("Q%d", i)), MakeFun(ty, TypeBool)))
		term, expected := q.Apply(f.Apply(x)).Core(), q.Apply(x).Core()
		if goal == nil {
			goal, want = term, expected
		} else {
			goal, want = ext.And(goal, term).Core(), ext.And(want, expected).Core()
		}
	}
	leaves := e.simpLeaves(goal, Fwd(depName("zz_simp_poly")))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(want))
}

func TestSimp_ExplicitCompoundInstanceKeepsItsLetters(t *testing.T) {
	e := makeAdaptedEnv()
	setB, setC := MakeFun(core.MakeVarType("B"), TypeBool), MakeFun(core.MakeVarType("C"), TypeBool)
	x, y := ext.WrapTerm(Var("x", setB)), ext.WrapTerm(Var("y", setC))
	qB, qC := ext.WrapTerm(Var("QB", MakeFun(setB, TypeBool))), ext.WrapTerm(Var("QC", MakeFun(setC, TypeBool)))
	fB, fC := e.ctx.Const("simpPolyF", MakeFun(setB, setB)), e.ctx.Const("simpPolyF", MakeFun(setC, setC))
	goal := ext.And(qB.Apply(fB.Apply(x)), qC.Apply(fC.Apply(y))).Core()
	want := ext.And(qB.Apply(x), qC.Apply(fC.Apply(y))).Core()
	leaves := e.simpLeaves(goal, Fwd(e.ctx.AtSoleType(e.ctx.Dep(depName("zz_simp_poly")), setB)))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(want), "%s", prop.PrintProp(leaves[0].Goal))
}

func TestSimp_ClosedReadingKeepsItsInstanceTypes(t *testing.T) {
	e := makeAdaptedEnv()
	typeB, typeC := core.MakeVarType("B"), core.MakeVarType("C")
	funA := MakeFun(core.TypeA(), core.TypeA())
	meta := core.MakeConstMeta("simpFixedStructure", MakeFun(funA, TypeBool))
	e.ctx.Env.ProofService.LoadOrStoreConstMeta(meta)
	structure := e.ctx.Const("simpFixedStructure", MakeFun(funA, TypeBool))
	f, x := ext.WrapTerm(Var("f", funA)), ext.WrapTerm(Var("x", core.TypeA()))
	law := ext.ForAll(f)(structure.Apply(f).Imply(ext.ForAll(x)(f.Apply(x).Eq(x))))
	serveThm(e.ctx, "zz_simp_fixed_law", core.TestThm(law.Core()))
	fB, fC := e.ctx.Const("simpPolyF", MakeFun(typeB, typeB)), e.ctx.Const("simpPolyF", MakeFun(typeC, typeC))
	structureB := e.ctx.Const("simpFixedStructure", MakeFun(MakeFun(typeB, typeB), TypeBool))
	serveThm(e.ctx, "zz_simp_fixed_instance", core.TestThm(structureB.Apply(fB).Core()))
	xB, xC := ext.WrapTerm(Var("xB", typeB)), ext.WrapTerm(Var("xC", typeC))
	qB, qC := ext.WrapTerm(Var("QB", MakeFun(typeB, TypeBool))), ext.WrapTerm(Var("QC", MakeFun(typeC, TypeBool)))
	goal := ext.And(qB.Apply(fB.Apply(xB)), qC.Apply(fC.Apply(xC))).Core()
	want := ext.And(qB.Apply(xB), qC.Apply(fC.Apply(xC))).Core()
	leaves := e.simpLeaves(goal, Fwd(Read(depName("zz_simp_fixed_law"), depName("zz_simp_fixed_instance"))))
	require.Len(t, leaves, 1)
	require.True(t, leaves[0].Goal.Conclusion().AlphaEquals(want), "%s", prop.PrintProp(leaves[0].Goal))
}
