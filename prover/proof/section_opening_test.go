// section_opening_test.go — the OPENED section (section.go's Opening):
// one opening action runs on the section root before any binder is
// bound, and the body is then bound against the goal the opening left.
//
// The fixture is a minted definitional constant
//
//	OpeningTestConj = λf g:(num → bool). λn:num. f(n) ∧ g(n)
//
// so that `∀n:num. OpeningTestConj(R, Q, n) ⇒ Q(n)` unfolds, under an
// opening Unfold, to `∀n:num. R(n) ∧ Q(n) ⇒ Q(n)` — the shape the
// surface-alias tests prove — with the rewrite landing INSIDE the
// ⇒-antecedent the closure binds. The tests read the hypothesis the
// closure receives and check it is the unfolded one.

package proof

import (
	"fmt"
	"strings"
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

const openingTestConst = "OpeningTestConj"

// openingTestDef mints the fixture constant once per process: a
// definitional const is process-global by name, so the tests share one
// mint rather than re-defining it.
var openingTestDef = sync.OnceValue(func() core.ConstTerm {
	pred := MakeFun(numType, TypeBool)
	f := Var("f", pred)
	g := Var("g", pred)
	n := Var("n", numType)
	body := f.To(g.To(n.To(f.Apply(n).And(g.Apply(n)))))
	return core.NewConstDef(body.Core(), openingTestConst)
})

// openingTestDefinition is the fixture constant as Unfold takes it.
var openingTestDefinition = mintedDefinition(openingTestDef)

// newOpeningTestScript is the step-test env with the fixture constant
// declared (Script.Const, the runtime declaration route — so the
// statement text resolves the name) and the predicates R, Q
// the statements are written in.
func newOpeningTestScript() *Script {
	env := makeStepTestEnv()
	c := openingTestDef()
	env.ProofService.LoadOrStoreConstMeta(c.Meta())
	ctx := NewScript(env)
	ctx.Const(openingTestConst, c.Meta().AbsType())
	ctx.Var("R", MakeFun(numType, TypeBool))
	ctx.Var("Q", MakeFun(numType, TypeBool))
	return ctx
}

const openingTestStatement = "∀n:num. " + openingTestConst + "(R, Q, n) ⇒ Q(n)"

// requireUnfolded asserts that the Fact the closure received is the
// UNFOLDED antecedent — `R(n) ∧ Q(n)` at the minted n, spelled through
// the statement's surface name — and no longer mentions the constant.
func requireUnfolded(t *testing.T, a *Argument, h Fact) {
	t.Helper()
	content, ok := h.BoundContent()
	require.True(t, ok, "a closure-bound antecedent is a resident fact")
	require.False(t, strings.Contains(ext.PrintTerm(content), openingTestConst),
		"the closure must receive the hypothesis AFTER the opening unfold; got %s", ext.PrintTerm(content))
	require.True(t, content.AlphaEquals(a.Term("R(n) ∧ Q(n)").Core()),
		"expected the unfolded antecedent R(n) ∧ Q(n); got %s", ext.PrintTerm(content))
}

// TestOpening_UnfoldedAntecedentReachesClosure (a): an opening Unfold
// of a constant inside the ⇒-antecedent; the closure's Fact is the
// unfolded hypothesis, the ∀-binder keeps the statement's own name,
// and the section proves.
func TestOpening_UnfoldedAntecedentReachesClosure(t *testing.T) {
	ctx := newOpeningTestScript()
	ran := false
	sec := ctx.Theorem(openingTestStatement,
		Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
			ran = true
			require.True(t, a.Term("n").Core().Equals(n.Core()),
				"the statement's binder name must still alias the mint after the opening")
			requireUnfolded(t, a, h)
			a.Have("R at n, read off the unfolded hypothesis", "R(n)", By(h))
			a.Show("the other conjunct is the goal", By(h))
		}))
	require.True(t, ran, "the closure must run")
	require.True(t, sec.Proved(), "the opened section did not close")
}

// TestOpening_TypedBinderAdoptsAfterOpening (b): the same with a TYPED
// binder parameter — the adopted value carries the binder's HOL type
// and is the minted variable the surface name resolves to.
func TestOpening_TypedBinderAdoptsAfterOpening(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem(openingTestStatement,
		Opening(Unfold(openingTestDefinition), func(a *Argument, n *ext.Expr[ext.Nat], h Fact) {
			require.True(t, n.Core().Type().Equals(ext.NumType), "adopted at :num; got %s", ext.FormatType(n.Core().Type()))
			v, ok := n.Core().AsVar()
			require.True(t, ok, "the typed parameter is the minted variable")
			require.True(t, a.Term("n").Core().Equals(v), "the surface name resolves to the typed parameter's mint")
			requireUnfolded(t, a, h)
			a.Show("the other conjunct is the goal", By(h))
		}))
	require.True(t, sec.Proved(), "the typed opened section did not close")
}

// TestOpening_OneActionBody (c): Opening composes with the one-Action
// section — the opening move, then the one action on the opened goal.
// The action here is a Derive block, which can also read the goal it
// was handed: the constant is already unfolded.
func TestOpening_OneActionBody(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem(openingTestStatement,
		Opening(Unfold(openingTestDefinition), Derive(func(a *Argument) {
			require.False(t, strings.Contains(PrintProp(a.Goal()), openingTestConst),
				"the one action must run on the OPENED goal; got %s", PrintProp(a.Goal()))
			a.Fix()
			h := a.Assume()
			a.Show("the other conjunct is the goal", By(h))
		})))
	require.True(t, sec.Proved(), "the one-action opened section did not close")
}

// TestOpening_LemmaGetsIt (3): Script.Lemma is the same door.
func TestOpening_LemmaGetsIt(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Lemma(openingTestStatement,
		Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
			requireUnfolded(t, a, h)
			a.Show("the other conjunct is the goal", By(h))
		}))
	require.True(t, sec.Proved(), "the opened Lemma did not close")
}

// TestOpening_PlanFollowsOpenedGoal: the plan is read off the goal the
// opening LEFT, both ways. An opening StripQuant1 consumes the ∀, so
// (i) a closure still declaring the Term parameter fails at plan time,
// naming the parameter and the opened goal (d); and (ii) a closure
// declaring only the Fact binds — the antecedent, still folded, since
// this opening did not unfold it.
func TestOpening_PlanFollowsOpenedGoal(t *testing.T) {
	t.Run("mismatch names the parameter against the opened goal", func(t *testing.T) {
		ctx := newOpeningTestScript()
		defer func() {
			r := recover()
			require.NotNil(t, r, "a parameter the opened goal no longer offers must panic")
			msg := fmt.Sprint(r)
			require.Contains(t, msg, "Opening", "the panic names Opening")
			require.Contains(t, msg, "AS OPENED", "the panic says the mismatch is against the opened goal")
			require.Contains(t, msg, "parameter 1 binds a binder, but the statement offers none there",
				"the existing plan error fires with the parameter index")
			// The prefix quotes the statement TEXT (which spells ∀n); the
			// goal the plan printed is the tail, and that one is the
			// OPENED goal — its ∀ consumed by the opening strip.
			_, printed, found := strings.Cut(msg, "(statement:")
			require.True(t, found, "the plan error prints the goal it planned against")
			require.False(t, strings.Contains(printed, "∀"),
				"the goal printed is the OPENED one (∀ consumed); got %s", printed)
			require.Contains(t, printed, openingTestConst+"(R, Q, n")
		}()
		// One parameter, so the opened goal's one slot (the ⇒) is
		// matched against it by KIND — the index-bearing plan error.
		ctx.Theorem(openingTestStatement,
			Opening(StripQuant1(), func(a *Argument, n Term) {
				t.Error("the closure must not run when its parameters do not plan")
			}))
	})
	t.Run("arity is counted against the opened goal", func(t *testing.T) {
		ctx := newOpeningTestScript()
		defer func() {
			r := recover()
			require.NotNil(t, r, "two parameters against a one-slot opened goal must panic")
			msg := fmt.Sprint(r)
			require.Contains(t, msg, "Opening")
			require.Contains(t, msg, "binds a binder, but the statement offers none there")
		}()
		ctx.Theorem(openingTestStatement,
			Opening(StripQuant1(), func(a *Argument, n Term, h Fact) {
				t.Error("the closure must not run when its parameters do not plan")
			}))
	})
	t.Run("typed parameter type-checks against the opened goal", func(t *testing.T) {
		ctx := newOpeningTestScript()
		defer func() {
			r := recover()
			require.NotNil(t, r, "a cross-typed parameter must panic at plan time")
			msg := fmt.Sprint(r)
			require.Contains(t, msg, "Opening")
			require.Contains(t, msg, "parameter 1 asserts type bool but the statement's binder is ∀n:num")
		}()
		ctx.Theorem(openingTestStatement,
			Opening(Unfold(openingTestDefinition), func(a *Argument, n *ext.Expr[ext.Bool], h Fact) {
				t.Error("the closure must not run when its parameters do not plan")
			}))
	})
	t.Run("a binder the opening consumed is no longer a slot", func(t *testing.T) {
		ctx := newOpeningTestScript()
		sec := ctx.Theorem(openingTestStatement,
			Opening(StripQuant1(), func(a *Argument, h Fact) {
				content, ok := h.BoundContent()
				require.True(t, ok)
				require.True(t, strings.Contains(ext.PrintTerm(content), openingTestConst),
					"this opening did not unfold, so the bound antecedent is the folded one; got %s", ext.PrintTerm(content))
				// Unfolding the resident antecedent leaves `R(n₀) ∧ Q(n₀) ⊢
				// Q(n₀)`, which the unfold's residual simplification
				// closes — a terminal move, so it is a Show.
				a.Show("unfolded, the hypothesis' second conjunct is the goal", Unfold(openingTestDefinition))
			}))
		require.True(t, sec.Proved(), "the Fact-only opened section did not close")
	})
}

// TestOpening_NoOpMatchesUnwrapped (e): the section-boundary fixture
// (TestSurfaceAlias_TheoremClosureParams' statement), with an untyped
// and a typed binder closure, run plain and under a no-op Opening
// (Chain() of nothing): the same recorded step sequence, the same node
// count and the same theorem.
func TestOpening_NoOpMatchesUnwrapped(t *testing.T) {
	run := func(body any) *GoalStackNode {
		ctx := NewScript(makeStepTestEnv())
		ctx.Var("R", MakeFun(numType, TypeBool))
		ctx.Var("Q", MakeFun(numType, TypeBool))
		ctx.Var("n", numType)
		return ctx.Theorem("Q(n) ⇒ (∀k:num. R(k)) ⇒ ∀n:num. R(n) ∨ Q(n)", body)
	}
	untyped := func(a *Argument, decoy, law Fact, nn Term) {
		step := a.Have("R at n through the surface name", "R(n)", By(law.At(a.Term("n"))))
		a.Show("left disjunct", By(step))
	}
	typed := func(a *Argument, decoy, law Fact, nn *ext.Expr[ext.Nat]) {
		require.True(t, nn.Core().Type().Equals(ext.NumType))
		step := a.Have("R at n through the surface name", "R(n)", By(law.At(nn)))
		a.Show("left disjunct", By(step))
	}
	for name, body := range map[string]any{"untyped": untyped, "typed": typed} {
		t.Run(name, func(t *testing.T) {
			plain := run(body)
			opened := run(Opening(Chain(), body))
			require.True(t, plain.Proved())
			require.True(t, opened.Proved())
			require.Equal(t, recordedSteps(plain), recordedSteps(opened),
				"a no-op Opening must record the same steps as the unwrapped body")
			require.Equal(t, plain.PromisedThm().AlphaKey(), opened.PromisedThm().AlphaKey())
		})
	}
}

// recordedSteps renders the section tree's step descriptions in
// preorder — one line per recorded node — as the comparable record of
// what a section ran.
func recordedSteps(n *GoalStackNode) []string {
	out := []string{n.StepDescription()}
	for _, c := range n.Children() {
		out = append(out, recordedSteps(c)...)
	}
	return out
}

// TestOpening_Panics (6): each misuse names Opening.
func TestOpening_Panics(t *testing.T) {
	body := func(a *Argument, n Term, h Fact) {}
	cases := map[string]func(){
		"nil opening action": func() { Opening(nil, body) },
		"nested wrapper":     func() { Opening(Unfold(openingTestDefinition), Opening(StripQuant1(), body)) },
		"nil body":           func() { Opening(Unfold(openingTestDefinition), nil) },
		"unsupported body":   func() { Opening(Unfold(openingTestDefinition), "BySets()") },
	}
	for name, do := range cases {
		t.Run(name, func(t *testing.T) {
			defer func() {
				r := recover()
				require.NotNil(t, r, "%s must panic", name)
				require.Contains(t, fmt.Sprint(r), "Opening", "the panic names Opening")
			}()
			do()
		})
	}
	t.Run("opening action that fails is attributed", func(t *testing.T) {
		ctx := newOpeningTestScript()
		defer func() {
			r := recover()
			require.NotNil(t, r)
			msg := fmt.Sprint(r)
			require.Contains(t, msg, "Opening — the opening action failed")
			require.Contains(t, msg, wrappedTestConst)
		}()
		// zz_wrapped does not occur in the statement: its Unfold opens nothing.
		ctx.Theorem(openingTestStatement, Opening(Unfold(wrappedTestDefinition), body))
	})
}
