package proof

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// letTestEnv: Q : ind → bool, plus : ind → ind → ind, a : ind, and the
// premise ∀x. Q(x) every goal below closes from.
type letTestEnv struct {
	ctx   *Script
	Q     *ext.TermWrapper
	plus  *ext.TermWrapper
	a     *ext.TermWrapper
	allQ  *ext.TermWrapper // ∀x. Q(x)
	sumAA *ext.TermWrapper // plus(a, a)
}

func makeLetTestEnv() *letTestEnv {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	predTy := MakeFun(TypeInd, TypeBool)
	opTy := MakeFun(TypeInd, MakeFun(TypeInd, TypeInd))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("letQ", predTy))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("letPlus", opTy))
	e := &letTestEnv{ctx: ctx, Q: ctx.Const("letQ", predTy), plus: ctx.Const("letPlus", opTy),
		a: ext.WrapTerm(Var("a", TypeInd))}
	x := Var("x", TypeInd)
	e.allQ = ext.ForAll(x)(e.Q.Apply(x))
	e.sumAA = e.plus.Apply(e.a, e.a)
	return e
}

// Let on a term the goal carries: the occurrence becomes the name, the
// definition joins the hypotheses, the goal keeps its form (no ⊥), and
// the block closes with the goal read through the name.
func TestLet_NamesAnOccurrenceAndKeepsTheGoalForm(t *testing.T) {
	e := makeLetTestEnv()
	// (∀x. Q(x)) ⇒ Q(plus(a, a))
	sec := e.ctx.Section(prop.MakeProp(e.allQ.Imply(e.Q.Apply(e.sumAA)).Core()))
	sec.Do(Derive(func(arg *Argument) {
		all := arg.Assume()
		wDef := arg.Let("w", e.sumAA.Core())
		w := Var("w", TypeInd)
		require.True(t, arg.cur.Goal.Conclusion().AlphaEquals(e.Q.Apply(w).Core()),
			"the conclusion reads through the name: Q(w); got %s", ext.PrintTerm(arg.cur.Goal.Conclusion()))
		require.False(t, arg.cur.Goal.Conclusion().Equals(F), "the goal keeps its form — Let is not a SupposeNot")
		require.True(t, arg.cur.Goal.HasHyp(ext.Eq(w, e.sumAA.Core())), "the definition w = plus(a, a) is resident")
		arg.Show("Q holds everywhere, so at w", By(all, wDef))
	}))
	require.True(t, sec.Proved())
}

// Let on a term the goal does not mention: nothing is rewritten, the
// definition is simply there for the argument to build with.
func TestLet_DefinesATermTheGoalDoesNotMention(t *testing.T) {
	e := makeLetTestEnv()
	// (∀x. Q(x)) ⇒ Q(a)
	sec := e.ctx.Section(prop.MakeProp(e.allQ.Imply(e.Q.Apply(e.a)).Core()))
	sec.Do(Derive(func(arg *Argument) {
		all := arg.Assume()
		wDef := arg.Let("w", e.sumAA.Core())
		w := Var("w", TypeInd)
		require.True(t, arg.cur.Goal.Conclusion().AlphaEquals(e.Q.Apply(e.a).Core()), "the goal is untouched")
		require.True(t, arg.cur.Goal.HasHyp(ext.Eq(w, e.sumAA.Core())), "the definition is resident")
		arg.Show("Q holds everywhere", By(all, wDef))
	}))
	require.True(t, sec.Proved())
}

// A name the goal only BINDS — by its ∃, by a λ in a resident equation,
// by a λ in its conclusion — is a Let name like any other: the ∃'s
// witness is named after its bound variable, the natural spelling.
func TestLet_AcceptsANameTheGoalOnlyBinds(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	byTheGoalsExists := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀P:num → bool. ∀b:num. P(b) ⇒ ∃q. P(q)",
			func(a *Argument, P *ext.Expr[natSet], b *ext.Expr[ext.Nat], pb Fact) {
				qDef := a.Let("q", b)
				a.Show("the named witness", By(pb, qDef))
			})
	})
	require.True(t, byTheGoalsExists != nil && byTheGoalsExists.Proved(), "q, bound by the goal's ∃")

	byAResidentLambda := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀P:num → bool. ∀f g:num → num. ∀b:num. f = (λu. g(g(u))) ⇒ P(f(b)) ⇒ P(g(g(b)))",
			func(a *Argument, P *ext.Expr[natSet], f, g *ext.Expr[natFun], b *ext.Expr[ext.Nat], fDef, held Fact) {
				uDef := a.Let("u", b)
				a.Show("at the name", By(fDef, held, uDef))
			})
	})
	require.True(t, byAResidentLambda != nil && byAResidentLambda.Proved(), "u, bound by a λ in a resident equation")

	byTheGoalsLambda := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀f:num → num. ∀b:num. (∀y. f(y) = y + b) ⇒ f = (λx. x + b)",
			func(a *Argument, f *ext.Expr[natFun], b *ext.Expr[ext.Nat], all Fact) {
				xDef := a.Let("x", b)
				a.Show("pointwise", By(all, xDef))
			})
	})
	require.True(t, byTheGoalsLambda != nil && byTheGoalsLambda.Proved(), "x, bound by a λ in the conclusion")
}

// A Let whose term occurs UNDER the binder spelling its name: the
// rewrite renames that binder apart — ∃q. P(q) ∧ P(b) at q := b reads
// ∃q'. P(q') ∧ P(q), never ∃q. P(q) ∧ P(q) — and the block closes.
func TestLet_RenamesAClashingBinderApart(t *testing.T) {
	ctx := NewScript(makeStepTestEnv())
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀P:num → bool. ∀b:num. (∀u. P(u)) ⇒ ∃q. P(q) ∧ P(b)",
			func(a *Argument, P *ext.Expr[natSet], b *ext.Expr[ext.Nat], all Fact) {
				qDef := a.Let("q", b)
				concl := a.cur.Goal.Conclusion()
				require.False(t, concl.AlphaEquals(a.Term("∃q. P(q) ∧ P(q)").Core()),
					"the binder captured the named occurrence: %s", ext.PrintTerm(concl))
				require.True(t, concl.AlphaEquals(a.Term("∃r. P(r) ∧ P(q)").Core()),
					"the binder is renamed apart from the name: got %s", ext.PrintTerm(concl))
				a.Show("P everywhere, so at the name and at the witness", By(all, qDef))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A name the goal uses FREE is refused whether or not a binder spells
// it too.
func TestLet_RefusesANameFreeBesideItsBinder(t *testing.T) {
	e := makeLetTestEnv()
	a := Var("a", TypeInd)
	// (∀x. Q(x)) ⇒ Q(a) ∧ ∃a. Q(a)
	sec := e.ctx.Section(prop.MakeProp(e.allQ.Imply(e.Q.Apply(e.a).And(ext.Exists(a)(e.Q.Apply(a)))).Core()))
	requirePanicContains(t, "already free in the goal", func() {
		sec.Do(Derive(func(arg *Argument) {
			arg.Assume()
			arg.Let("a", e.sumAA.Core())
			t.Fatal("unreachable")
		}))
	})
}

// A block under a definition closes when its hypotheses contradict one
// another. The By below denotes a term, so its leaf is refuted from the
// hypotheses and the negated conclusion; the refutation reads no negated
// conclusion, and the By's theorem concludes ⊥ where the goal states
// Q(c). The definition takes that theorem back to the goal, whether or
// not the contradiction reads the name; the same By closes the goal
// with no definition above it.
func TestLet_ABlockClosedByContradictionCloses(t *testing.T) {
	const statement = "∀P Q:num → bool. ∀g:num → num. ∀b c:num. (∀x. ¬P(x)) ⇒ P(g(g(b))) ⇒ Q(c)"
	type block = func(a *Argument, never, holds Fact)
	for name, body := range map[string]block{
		"a contradiction that reads the name": func(a *Argument, never, holds Fact) {
			a.LetAs[ext.Nat]("w", "g(b)")
			a.Show("P holds at g(w), and nowhere", By(DenotedAs("d", a.Term("g(w)")), never, holds))
		},
		"a contradiction that does not": func(a *Argument, never, holds Fact) {
			a.LetAs[ext.Nat]("w", "g(c)")
			a.Show("P holds at g(g(b)), and nowhere", By(DenotedAs("d", a.Term("g(g(b))")), never, holds))
		},
		"no definition (control)": func(a *Argument, never, holds Fact) {
			a.Show("P holds at g(g(b)), and nowhere", By(DenotedAs("d", a.Term("g(g(b))")), never, holds))
		},
	} {
		t.Run(name, func(t *testing.T) {
			ctx := NewScript(makeStepTestEnv())
			sec := provesInHand(t, func() *GoalStackNode {
				return ctx.Theorem(statement,
					func(a *Argument, P, Q *ext.Expr[natSet], g *ext.Expr[natFun], b, c *ext.Expr[ext.Nat], never, holds Fact) {
						body(a, never, holds)
					})
			})
			require.True(t, sec != nil && sec.Proved())
		})
	}
}

// A name the goal already uses is refused at the step, never renamed.
func TestLet_RefusesANameAlreadyFree(t *testing.T) {
	e := makeLetTestEnv()
	sec := e.ctx.Section(prop.MakeProp(e.allQ.Imply(e.Q.Apply(e.a)).Core()))
	defer func() {
		r := recover()
		require.NotNil(t, r)
		require.Contains(t, sprintAny(r), "already free in the goal")
	}()
	sec.Do(Derive(func(arg *Argument) {
		arg.Assume()
		arg.Let("a", e.sumAA.Core())
		t.Fatal("unreachable")
	}))
}

// letAsTestScript: P over num and g : num → num, for the goal
// `(∀n:num. P(n)) ⇒ P(g(0))`, which a definition `w := g(0)` rewrites
// to P(w).
func letAsTestScript() *Script {
	env := makeStepTestEnv()
	env.ProofService.CNFStore = NewMemoryCNFStore()
	ctx := NewScript(env)
	ctx.Var("P", MakeFun(numType, TypeBool))
	ctx.Var("g", MakeFun(numType, numType))
	return ctx
}

const letAsTestStatement = "(∀n:num. P(n)) ⇒ P(g(0))"

// LetAs reads its text at the phantom and returns the name as the typed
// handle beside its definition: the handle is the variable w:num, the
// Fact is the resident equation w = g(0), and the goal reads through
// the name.
func TestLetAs_ReturnsTheNameAtItsTypeBesideTheDefinition(t *testing.T) {
	sec := letAsTestScript().Theorem(letAsTestStatement, func(a *Argument, allP Fact) {
		w, wDef := a.LetAs[ext.Nat]("w", "g(0)")
		v, isVar := w.Core().AsVar()
		require.True(t, isVar, "the handle is a variable, got %s", ext.PrintTerm(w.Core()))
		require.Equal(t, "w", string(v.Name()))
		require.True(t, w.Core().Type().Equals(numType))
		content, bound := wDef.BoundContent()
		require.True(t, bound, "the Fact is resident")
		require.True(t, content.AlphaEquals(ext.Eq(w.Core(), a.Term("g(0)").Core())),
			"the Fact is the definition w = g(0), got %s", ext.PrintTerm(content))
		require.True(t, a.cur.Goal.Conclusion().AlphaEquals(a.Term("P(w)").Core()),
			"the goal reads through the name: got %s", ext.PrintTerm(a.cur.Goal.Conclusion()))
		a.Show("P holds everywhere, so at w", By(allP.At(w)))
	})
	require.True(t, sec.Proved())
}

// stepsOf is the tree's steps in preorder, one description per node.
func stepsOf(n *GoalStackNode) []string {
	out := []string{n.StepDescription()}
	for _, c := range n.children {
		out = append(out, stepsOf(c)...)
	}
	return out
}

// The same steps as the Let and the TermAs of its name it abbreviates.
func TestLetAs_RecordsTheLetStep(t *testing.T) {
	run := func(body func(a *Argument, allP Fact)) *GoalStackNode {
		return letAsTestScript().Theorem(letAsTestStatement, body)
	}
	short := run(func(a *Argument, allP Fact) {
		w, wDef := a.LetAs[ext.Nat]("w", "g(0)")
		a.Show("…", By(allP.At(w), wDef))
	})
	long := run(func(a *Argument, allP Fact) {
		wDef := a.Let("w", a.TermAs[ext.Nat]("g(0)"))
		w := a.TermAs[ext.Nat]("w")
		a.Show("…", By(allP.At(w), wDef))
	})
	require.True(t, short.Proved())
	require.True(t, long.Proved())
	require.Equal(t, stepsOf(long), stepsOf(short))
}

// A text that cannot be read at the phantom is refused at the parse,
// naming the verb and the expected type, before any step runs.
func TestLetAs_RefusesATextNotReadableAtThePhantom(t *testing.T) {
	defer func() {
		r := recover()
		require.NotNil(t, r)
		require.Contains(t, sprintAny(r), "Argument.LetAs")
		require.Contains(t, sprintAny(r), "expected bool")
	}()
	letAsTestScript().Theorem(letAsTestStatement, func(a *Argument, allP Fact) {
		a.LetAs[ext.Bool]("b", "g(0)")
		t.Fatal("unreachable")
	})
}

// A subscripted name is the identifier a claim text reads it as: LetAs
// ("i₀"), Let("u₁") and Denote("d₂") name the variables i_0, u_1 and
// d_2, which print back as written, and a later claim spells each
// either way.
func TestLetAs_ASubscriptedNameIsSpelledByLaterClaims(t *testing.T) {
	sec := letAsTestScript().Theorem(letAsTestStatement, func(a *Argument, allP Fact) {
		i, iDef := a.LetAs[ext.Nat]("i₀", "g(0)")
		v, isVar := i.Core().AsVar()
		require.True(t, isVar, "the handle is a variable, got %s", ext.PrintTerm(i.Core()))
		require.Equal(t, "i_0", string(v.Name()))
		require.Equal(t, "i₀", ext.PrintTerm(i.Core()))
		a.Have("P at g of i₀", "P(g(i₀))", By(allP.At(a.Term("g(i_0)"))))
		uDef := a.Let("u₁", a.Term("g(i₀)"))
		a.Have("P at g of u₁", "P(g(u₁))", By(allP.At(a.Term("g(u_1)"))))
		a.Have("u₁ is g at i₀, through both definitions", "u_1 = g(g(0))", By(uDef, iDef))
		a.Show("P at i₀", By(allP.At(i)))
	})
	require.True(t, sec.Proved())
	sec = letAsTestScript().Theorem(letAsTestStatement, func(a *Argument, allP Fact) {
		dDef := a.Denote("d₂", a.Term("g(0)"))
		a.Have("P at g of d₂", "P(g(d₂))", By(allP.At(a.Term("g(d_2)"))))
		require.True(t, a.Goal().HasHyp(ext.Eq(Var("d_2", numType), a.Term("g(0)").Core())), "d_2 = g(0) is resident")
		require.True(t, a.Goal().HasHyp(dDef.handle.term), "the equation is the Fact")
		a.Show("P at d₂ refutes its negation", CnfRefute())
	})
	require.True(t, sec.Proved())
}

// Let's term slot is a TermLike: a text read by a.Term and a typed
// value are taken as they are, with no Core() at the site.
func TestLet_TakesATermLike(t *testing.T) {
	sec := letAsTestScript().Theorem(letAsTestStatement, func(a *Argument, allP Fact) {
		a.Let("u", a.Term("g(0)"))
		a.Let("v", a.TermAs[ext.Nat]("g(u)"))
		require.True(t, a.cur.Goal.HasHyp(ext.Eq(Var("u", numType), a.Term("g(0)").Core())), "u = g(0) is resident")
		require.True(t, a.cur.Goal.HasHyp(ext.Eq(Var("v", numType), a.Term("g(u)").Core())), "v = g(u) is resident")
		require.True(t, a.cur.Goal.Conclusion().AlphaEquals(a.Term("P(u)").Core()),
			"the goal reads through u: got %s", ext.PrintTerm(a.cur.Goal.Conclusion()))
		a.Show("P holds everywhere, so at u", By(allP.At(a.Term("u"))))
	})
	require.True(t, sec.Proved())
}
