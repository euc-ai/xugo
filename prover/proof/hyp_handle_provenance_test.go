package proof

import (
	"fmt"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A Fact bound to a resident hypothesis follows it through a step that
// transforms SEVERAL hypotheses at once, by the provenance the step
// records: a rewrite that reaches two facts, a Let whose equation
// rewrites two, an Unfold that opens two. A fact the step leaves no
// single hypothesis for — an Unfold whose tidy splits it into its
// conjuncts — fails at its next use, naming the step.

// The fixture constants, minted once per process (a definitional
// constant is global by name):
//
//	HandleTrackAt   = λp:(ind → bool). λx:ind. p(x)
//	HandleTrackBoth = λp q:(ind → bool). λx:ind. p(x) ∧ q(x)
const (
	handleTrackAtConst   = "HandleTrackAt"
	handleTrackBothConst = "HandleTrackBoth"
)

var handleTrackDefs = sync.OnceValue(func() []core.ConstTerm {
	pred := MakeFun(TypeInd, TypeBool)
	p, q, x := Var("p", pred), Var("q", pred), Var("x", TypeInd)
	return []core.ConstTerm{
		core.NewConstDef(p.To(x.To(p.Apply(x))).Core(), handleTrackAtConst),
		core.NewConstDef(p.To(q.To(x.To(p.Apply(x).And(q.Apply(x))))).Core(), handleTrackBothConst),
	}
})

// The two fixture constants as Unfold takes them.
var (
	handleTrackAtDefinition   = mintedDefinition(func() core.ConstTerm { return handleTrackDefs()[0] })
	handleTrackBothDefinition = mintedDefinition(func() core.ConstTerm { return handleTrackDefs()[1] })
)

// handleTrackEnv: the predicates Q, R, T : ind → bool, the points a, b,
// the function f, the bool S, and the two fixture constants declared in
// the script so the statement texts resolve their names.
type handleTrackEnv struct {
	ctx      *Script
	Q, R, T  *ext.TermWrapper
	a, b, S  *ext.TermWrapper
	f        *ext.TermWrapper
	at, both *ext.TermWrapper
}

func makeHandleTrackEnv() *handleTrackEnv {
	env := makeStepTestEnv()
	for _, c := range handleTrackDefs() {
		env.ProofService.LoadOrStoreConstMeta(c.Meta())
	}
	ctx := NewScript(env)
	pred := MakeFun(TypeInd, TypeBool)
	e := &handleTrackEnv{
		ctx: ctx,
		Q:   Var("Q", pred), R: Var("R", pred), T: Var("T", pred),
		a: Var("a", TypeInd), b: Var("b", TypeInd), S: Var("S", TypeBool),
		f: Var("f", MakeFun(TypeInd, TypeInd)),
	}
	for _, c := range handleTrackDefs() {
		w := ctx.Const(string(c.Name()), c.Meta().AbsType())
		if string(c.Name()) == handleTrackAtConst {
			e.at = w
		} else {
			e.both = w
		}
	}
	return e
}

// requireFactNames asserts that f, resolved on the argument's current
// leaf, names the hypothesis content.
func requireFactNames(t *testing.T, arg *Argument, f Fact, content *ext.TermWrapper) {
	t.Helper()
	got := arg.cur.Goal.Hyp(arg.cur.resolveHypIndex(t, f.handle))
	require.True(t, got.AlphaEquals(content.Core()), "the fact names %s, got %s", ext.PrintTerm(content.Core()), ext.PrintTerm(got))
}

// TestHypHandle_FactSurvivesARewriteOfSeveralHypotheses: a Have-bound
// fact R(f(b)) and an assumed Q(f(b)) are both rewritten by
// `eq.RwRev()` with eq : a = f(b); each fact then names its rewrite and
// closes the goal.
//
//	(∀x. R(x)) ⇒ Q(f(b)) ⇒ a = f(b) ⇒ Q(a) ∧ R(a)
func TestHypHandle_FactSurvivesARewriteOfSeveralHypotheses(t *testing.T) {
	e := makeHandleTrackEnv()
	x := Var("x", TypeInd)
	fb := e.f.Apply(e.b)
	sec := e.ctx.Section(prop.MakeProp(ext.ForAll(x)(e.R.Apply(x)).Imply(
		e.Q.Apply(fb).Imply(e.a.Eq(fb).Imply(e.Q.Apply(e.a).And(e.R.Apply(e.a))))).Core()))
	sec.Do(Derive(func(arg *Argument) {
		all := arg.Assume()
		qAtFb := arg.Assume()
		eq := arg.Assume()
		rAtFb := arg.Have("R at f(b)", prop.MakeProp(e.R.Apply(fb).Core()), By(all))
		arg.Do(eq.RwRev())
		requireFactNames(t, arg, qAtFb, e.Q.Apply(e.a))
		requireFactNames(t, arg, rAtFb, e.R.Apply(e.a))
		requireFactNames(t, arg, eq, e.a.Eq(fb))
		arg.Show("both facts, read at a", By(qAtFb, rAtFb))
	}))
	require.True(t, sec.Proved())
}

// TestHypHandle_FactSurvivesALetThatRewritesSeveralHypotheses: the
// definition k = f(b) rewrites both assumed facts; each then names its
// form at k.
//
//	Q(f(b)) ⇒ R(f(b)) ⇒ Q(f(b)) ∧ R(f(b))
func TestHypHandle_FactSurvivesALetThatRewritesSeveralHypotheses(t *testing.T) {
	e := makeHandleTrackEnv()
	fb := e.f.Apply(e.b)
	sec := e.ctx.Section(prop.MakeProp(e.Q.Apply(fb).Imply(e.R.Apply(fb).Imply(e.Q.Apply(fb).And(e.R.Apply(fb)))).Core()))
	sec.Do(Derive(func(arg *Argument) {
		qAtFb := arg.Assume()
		rAtFb := arg.Assume()
		k := arg.Let("k", fb.Core())
		kVar := Var("k", TypeInd)
		requireFactNames(t, arg, qAtFb, e.Q.Apply(kVar))
		requireFactNames(t, arg, rAtFb, e.R.Apply(kVar))
		requireFactNames(t, arg, k, kVar.Eq(fb))
		arg.Show("both facts, read at k", By(qAtFb, rAtFb))
	}))
	require.True(t, sec.Proved())
}

// TestHypHandle_FactSurvivesAnUnfoldThatOpensSeveralHypotheses: the
// constant occurs in two assumed facts; the goal-side Unfold opens both,
// and each fact names its opened form.
//
//	(∀x. Q(x) ∧ R(x) ⇒ T(x)) ⇒ HandleTrackAt(Q, a) ⇒ HandleTrackAt(R, a) ⇒ T(a)
func TestHypHandle_FactSurvivesAnUnfoldThatOpensSeveralHypotheses(t *testing.T) {
	e := makeHandleTrackEnv()
	x := Var("x", TypeInd)
	sec := e.ctx.Section(prop.MakeProp(ext.ForAll(x)(e.Q.Apply(x).And(e.R.Apply(x)).Imply(e.T.Apply(x))).Imply(
		e.at.Apply(e.Q, e.a).Imply(e.at.Apply(e.R, e.a).Imply(e.T.Apply(e.a)))).Core()))
	sec.Do(Derive(func(arg *Argument) {
		implies := arg.Assume()
		qAtA := arg.Assume()
		rAtA := arg.Assume()
		arg.Do(Unfold(handleTrackAtDefinition))
		requireFactNames(t, arg, qAtA, e.Q.Apply(e.a))
		requireFactNames(t, arg, rAtA, e.R.Apply(e.a))
		arg.Show("T at a from the opened facts", By(implies, qAtA, rAtA))
	}))
	require.True(t, sec.Proved())
}

// TestHypHandle_FactSplitByAnUnfoldsTidyFailsNamingTheStep: the Unfold
// opens the fact to Q(a) ∧ R(a) and its tidy splits the conjunction, so
// the fact has no single successor; its next use fails naming the step
// and the narrower spelling that keeps one fact.
//
//	HandleTrackBoth(Q, R, a) ⇒ S
func TestHypHandle_FactSplitByAnUnfoldsTidyFailsNamingTheStep(t *testing.T) {
	e := makeHandleTrackEnv()
	sec := e.ctx.Section(prop.MakeProp(e.both.Apply(e.Q, e.R, e.a).Imply(e.S).Core()))
	defer func() {
		r := recover()
		require.NotNil(t, r, "expected a panic at the use of the split fact")
		msg := fmt.Sprint(r)
		require.Contains(t, msg, "has no single successor past it")
		require.Contains(t, msg, handleTrackBothConst)
		require.Contains(t, msg, "a.Unfolded(h, <"+handleTrackBothConst+"'s definition>)")
	}()
	sec.Do(Derive(func(arg *Argument) {
		both := arg.Assume()
		arg.Do(Unfold(handleTrackBothDefinition))
		leaf := arg.cur
		require.True(t, leaf.Goal.AnyHyp(e.Q.Apply(e.a).Core().AlphaEquals), "the tidy split the conjunction")
		require.True(t, leaf.Goal.AnyHyp(e.R.Apply(e.a).Core().AlphaEquals), "the tidy split the conjunction")
		arg.Do(Clear(both))
		t.Fatal("unreachable: the split fact has no hypothesis to clear")
	}))
}
