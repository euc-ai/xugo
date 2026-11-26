package proof

// Argument.Unfolded and ForEach — the Fact-level face of Unfold and the
// one-line ∀-lift (derive.go). The fixture is section_opening_test.go's
// minted constant OpeningTestConj = λf g n. f(n) ∧ g(n).

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

func TestUnfolded_ReadsTheFactByItsDefinition(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem(openingTestStatement, func(a *Argument, n Term, h Fact) {
		before := a.cur.Goal
		u := a.Unfolded(h, openingTestDefinition)
		content, ok := u.BoundContent()
		require.True(t, ok)
		require.True(t, content.AlphaEquals(a.Term("R(n) ∧ Q(n)").Core()),
			"the unfolded fact is the definition's body at the arguments, one Fact; got %s", ext.PrintTerm(content))
		// The folded fact survives, the goal is untouched, and the only
		// change to the context is the one new hypothesis.
		hc, ok := h.BoundContent()
		require.True(t, ok)
		require.Contains(t, ext.PrintTerm(hc), openingTestConst)
		require.True(t, a.cur.Goal.Conclusion().AlphaEquals(before.Conclusion()))
		require.Equal(t, before.NumHyps()+1, a.cur.Goal.NumHyps())
		a.Show("the second conjunct is the goal", By(u))
	})
	require.True(t, sec.Proved())
}

// The recorded tree is the hand-written idiom's: a Have whose claim is
// the unfolded statement, closed by Unfold — same node count, same
// theorem.
func TestUnfolded_RecordsTheHaveUnfoldIdiom(t *testing.T) {
	run := func(body func(a *Argument, n Term, h Fact)) *GoalStackNode {
		ctx := newOpeningTestScript()
		return ctx.Theorem(openingTestStatement, body)
	}
	verb := run(func(a *Argument, n Term, h Fact) {
		a.Show("…", By(a.Unfolded(h, openingTestDefinition)))
	})
	hand := run(func(a *Argument, n Term, h Fact) {
		a.Show("…", By(a.Have("opened", "R(n) ∧ Q(n)", Unfold(openingTestDefinition))))
	})
	require.True(t, verb.Proved())
	require.True(t, hand.Proved())
	require.Equal(t, countNodes(hand), countNodes(verb), "the verb must record the idiom's tree")
	require.True(t, hand.Goal.AlphaEquals(verb.Goal))
}

func countNodes(n *GoalStackNode) int {
	total := 1
	for _, c := range n.children {
		total += countNodes(c)
	}
	return total
}

func TestUnfolded_Refusals(t *testing.T) {
	expectPanic := func(t *testing.T, want string, body func(a *Argument, n Term, h Fact)) {
		t.Helper()
		defer func() {
			r := recover()
			require.NotNil(t, r, "expected a panic mentioning %q", want)
			require.Contains(t, fmt.Sprint(r), want)
		}()
		newOpeningTestScript().Theorem(openingTestStatement, body)
	}
	t.Run("no definition", func(t *testing.T) {
		expectPanic(t, "Unfolded: no definition to open", func(a *Argument, n Term, h Fact) {
			a.Unfolded(h, nil)
		})
	})
	t.Run("the fact does not mention the constant", func(t *testing.T) {
		expectPanic(t, "does not mention", func(a *Argument, n Term, h Fact) {
			plain := a.Have("a fact without the constant", "Q(n) ⇒ Q(n)", TrivialNormalized())
			a.Unfolded(plain, openingTestDefinition)
		})
	})
}

// forEachTestScript: predicates P, R over num, for `∀n. R(n)` from a
// wide `∀n. P(n)` and a pointwise law `∀n. P(n) ⇒ R(n)`.
func forEachTestScript() *Script {
	env := makeStepTestEnv()
	env.ProofService.CNFStore = NewMemoryCNFStore()
	ctx := NewScript(env)
	ctx.Var("P", MakeFun(numType, TypeBool))
	ctx.Var("R", MakeFun(numType, TypeBool))
	return ctx
}

const forEachTestStatement = "(∀n:num. P(n)) ⇒ (∀n:num. P(n) ⇒ R(n)) ⇒ ∀n:num. R(n)"

func TestForEach_ClosesKeylessAndRecordsNoPlan(t *testing.T) {
	ctx := forEachTestScript()
	store := ctx.Env.ProofService.CNFStore.(*MemoryCNFStore)
	var fixed *ext.Expr[ext.Nat]
	sec := ctx.Theorem(forEachTestStatement, func(a *Argument, allP, law Fact) {
		a.Show("for every n, the law at n", a.ForEach(func(n *ext.Expr[ext.Nat]) Action {
			fixed = n
			return By(allP.At(n), law.At(n))
		}))
	})
	require.True(t, sec.Proved())
	require.NotNil(t, fixed)
	v, isVar := fixed.Core().AsVar()
	require.True(t, isVar)
	require.Equal(t, "n", SurfaceBase(string(v.Name())),
		"the binder is fixed as FixAs fixes it: the engine's mint off the stated name (its surface spelling is the block's)")
	require.Empty(t, store.Plans(), "the author grounded the premises: no conditioning plan")
	require.Empty(t, store.Proofs(), "the apply rung closes: no certificate")
}

// The same tree as the Derive block it abbreviates.
func TestForEach_RecordsTheDeriveBlock(t *testing.T) {
	run := func(body func(a *Argument, allP, law Fact)) *GoalStackNode {
		return forEachTestScript().Theorem(forEachTestStatement, body)
	}
	short := run(func(a *Argument, allP, law Fact) {
		a.Show("…", a.ForEach(func(n *ext.Expr[ext.Nat]) Action { return By(allP.At(n), law.At(n)) }))
	})
	long := run(func(a *Argument, allP, law Fact) {
		a.Show("…", Derive(func(g *Argument) {
			n := g.FixAs[ext.Nat]()
			g.Show("the law at n", By(allP.At(n), law.At(n)))
		}))
	})
	require.True(t, short.Proved())
	require.True(t, long.Proved())
	require.Equal(t, countNodes(long), countNodes(short))
}

func TestForEach_Refusals(t *testing.T) {
	expectPanic := func(t *testing.T, want string, body func(a *Argument, allP, law Fact)) {
		t.Helper()
		defer func() {
			r := recover()
			require.NotNil(t, r, "expected a panic mentioning %q", want)
			require.Contains(t, fmt.Sprint(r), want, "got: %s", fmt.Sprint(r))
		}()
		forEachTestScript().Theorem(forEachTestStatement, body)
	}
	t.Run("no leading ∀", func(t *testing.T) {
		expectPanic(t, "no leading ∀", func(a *Argument, allP, law Fact) {
			n := a.FixAs[ext.Nat]()
			a.Show("…", a.ForEach(func(m *ext.Expr[ext.Nat]) Action { return By(allP.At(n), law.At(n)) }))
		})
	})
	t.Run("binder of another type", func(t *testing.T) {
		expectPanic(t, "type", func(a *Argument, allP, law Fact) {
			a.Show("…", a.ForEach(func(n *ext.Expr[ext.Bool]) Action { return By(allP, law) }))
		})
	})
	t.Run("the action leaves the leaf open", func(t *testing.T) {
		expectPanic(t, "ForEach: block ended with", func(a *Argument, allP, law Fact) {
			a.Show("…", a.ForEach(func(n *ext.Expr[ext.Nat]) Action { return Chain() }))
		})
	})
	t.Run("a text that spells the loop's variable", func(t *testing.T) {
		// The variable is fixed with no surface name, so "n" is no free
		// of the goal; the refusal says which spelling has one.
		expectPanic(t, "inside a ForEach", func(a *Argument, allP, law Fact) {
			a.Show("…", a.ForEach(func(n *ext.Expr[ext.Nat]) Action {
				return By(allP.At(a.Term("n")), law.At(n))
			}))
		})
	})
	t.Run("the same text outside a ForEach is refused without the note", func(t *testing.T) {
		defer func() {
			r := recover()
			require.NotNil(t, r)
			require.NotContains(t, fmt.Sprint(r), "inside a ForEach")
		}()
		forEachTestScript().Theorem(forEachTestStatement, func(a *Argument, allP, law Fact) {
			a.Term("n")
		})
	})
	t.Run("a text inside a ForEach that does not spell its variable", func(t *testing.T) {
		defer func() {
			r := recover()
			require.NotNil(t, r)
			require.NotContains(t, fmt.Sprint(r), "inside a ForEach")
		}()
		forEachTestScript().Theorem(forEachTestStatement, func(a *Argument, allP, law Fact) {
			a.Show("…", a.ForEach(func(n *ext.Expr[ext.Nat]) Action {
				return By(allP.At(a.Term("nowhere")), law.At(n))
			}))
		})
	})
	_ = strings.Contains
}

func TestUnfolded_AdvancesAfterInstallingNamedFact(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem("∀n:num. Q(n)", func(a *Argument, n Term) {
		serveThm(ctx, "zz_unfold_named", core.TestThm(a.Term(openingTestConst+"(R, Q, n)").Core()))
		u := a.Unfolded(NamedFact(depName("zz_unfold_named")), openingTestDefinition)
		a.Show("the unfolded fact supplies Q", By(u))
	})
	require.True(t, sec.Proved())
}
