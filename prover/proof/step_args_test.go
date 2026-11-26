// step_args_test.go — StepArgs (branch.go): an induction step's
// constructor arguments get the author's names.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/tactic"

	"github.com/stretchr/testify/require"
)

// listTestEnv is the list twin of givenTestEnv: an env serving the
// polymorphic list principle under the name the induction tactic reads,
// and a predicate Q over lists of num to induct for. nil and cons are
// read off the principle itself, so the test's constructors are the
// principle's own constants at the instance the goal pins.
type listTestEnv struct {
	ctx      *Script
	listNum  core.HolType
	nilTerm  Term
	consTerm Term
	Q        *ext.TermWrapper
}

func makeListTestEnv() *listTestEnv {
	env := makeStepTestEnv()
	principle := tactic.ListInductProp()
	env.LibraryThms = map[string]Thm{
		"list_induction": core.TestThm(principle.Conclusion(), principle.Hyps()...),
	}
	listNum := core.MakeCompositeType(core.MakeMetaType("list", 1), numType)
	// The principle's constructors, as its template reads them: nil
	// from the first case, cons from the second.
	tmpl, err := tactic.AnalyzeInductionPrinciple(principle)
	if err != nil {
		panic(err)
	}
	consHead, _ := ext.MatchesApply(tmpl.Cases[1].Constructor)
	atNum := core.MakeTypeSubst(core.TypeA(), numType)
	ctx := NewScript(env)
	e := &listTestEnv{
		ctx:      ctx,
		listNum:  listNum,
		nilTerm:  tmpl.Cases[0].Constructor.TypeSubstitute(atNum),
		consTerm: consHead.TypeSubstitute(atNum),
		// Declared, so a claim text may spell it.
		Q: ctx.Var("Q", MakeFun(listNum, TypeBool)),
	}
	// The constructors resolve in claim texts as the principle's own
	// constants, so a spelled `cons(x, xs)` is the engine's term for it.
	if e.ctx.ParseScope.Consts == nil {
		e.ctx.ParseScope.Consts = map[string]core.ConstTerm{}
	}
	e.ctx.ParseScope.Consts["nil"] = e.nilTerm.Core().(core.ConstTerm)
	e.ctx.ParseScope.Consts["cons"] = e.consTerm.Core().(core.ConstTerm)
	return e
}

// cons builds cons(h, t) at the test's instance.
func (e *listTestEnv) cons(h, t Term) Term { return ext.Apply(e.consTerm, h, t) }

// listGoal is the principle's own shape at Q: Q(nil), ∀h t. Q(t) ⇒
// Q(cons(h, t)) ⊢ ∀l. Q(l). The step law is what a StepArgs-naming
// proof grounds at the step's own head and tail.
func (e *listTestEnv) listGoal() (goal Prop, stepLaw Term) {
	l := Var("l", e.listNum)
	h := Var("h", numType)
	t := Var("t", e.listNum)
	stepLaw = ForAll(h)(ForAll(t)(e.Q.Apply(t).Imply(e.Q.Apply(e.cons(h, t))))).Core()
	goal = MakeProp(ForAll(l)(e.Q.Apply(l)), e.Q.Apply(e.nilTerm), stepLaw)
	return goal, stepLaw
}

// panicMessage runs f and returns the string it panicked with, or ""
// when it returned.
func panicMessage(f func()) (msg string) {
	defer func() {
		if r := recover(); r != nil {
			msg, _ = r.(string)
		}
	}()
	f()
	return ""
}

// TestStepArgs_NamesTheConstructorArguments: inside a Step body, the
// head and tail of the cons the step introduced are spellable by the
// names the author gives them, the tail IS the induction variable, and
// the terms returned ground a law at the step's own arguments.
func TestStepArgs_NamesTheConstructorArguments(t *testing.T) {
	e := makeListTestEnv()
	goal, stepLaw := e.listGoal()
	sec := e.ctx.Section(goal)

	var spelled, minted Term
	var tail *ext.TermWrapper
	sec.Do(Derive(func(a *Argument) {
		l := a.Binder("l")
		a.Induct(l)
		a.Base("Q holds at nil by hypothesis", Assumption())
		a.Step("at cons(x, xs): the step law at x and xs, from Q(xs)", func(b *Argument, ih Fact) {
			args := b.StepArgs("x", "xs")
			require.Len(t, args, 2)
			tail = args[1]
			// The author's spelling of the constructor application is
			// the engine's own term for it.
			spelled = b.Term("cons(x, xs)")
			minted = e.cons(args[0].Core(), args[1].Core())
			law := b.Hyp(stepLaw)
			b.Show("modus ponens on the step law at the step's own head and tail",
				By(ih, law.At(args[0], args[1])))
		})
	}))
	require.True(t, sec.Proved(), "a Step naming its arguments through StepArgs did not close")
	require.True(t, spelled.Core().Equals(minted),
		"the claim-text spelling cons(x, xs) did not denote the constructor application the step introduced")
	require.True(t, tail.Core().Equals(Var("l", e.listNum)),
		"the primary recursive argument is the induction variable itself, and StepArgs must return that variable")
}

// TestStepArgs_TreeIsUnchanged: binding names records nothing — a step
// written with StepArgs and the same step written without it record
// the identical tree, so every recorded key keeps hitting.
func TestStepArgs_TreeIsUnchanged(t *testing.T) {
	build := func(naming bool) *GoalStackNode {
		e := makeListTestEnv()
		goal, stepLaw := e.listGoal()
		sec := e.ctx.Section(goal)
		sec.Do(Derive(func(a *Argument) {
			a.Induct("l")
			a.Base("Q holds at nil by hypothesis", Assumption())
			a.Step("at cons: the step law", func(b *Argument, ih Fact) {
				if naming {
					b.StepArgs("x", "xs")
				}
				b.Show("modus ponens on the step law", By(ih, b.Hyp(stepLaw)))
			})
		}))
		require.True(t, sec.Proved())
		return sec
	}
	require.Equal(t, dumpTree(build(false), 0), dumpTree(build(true), 0),
		"StepArgs changed the recorded tree — a binding must record nothing")
}

// TestStepArgs_TheInductionVariablesOwnNameIsANoOp: the tail is the
// induction variable, so naming it by that variable's own name binds
// nothing new and is accepted — one name, one meaning, already.
func TestStepArgs_TheInductionVariablesOwnNameIsANoOp(t *testing.T) {
	e := makeListTestEnv()
	goal, stepLaw := e.listGoal()
	sec := e.ctx.Section(goal)
	sec.Do(Derive(func(a *Argument) {
		a.Induct("l")
		a.Base("Q holds at nil by hypothesis", Assumption())
		a.Step("at cons(x, l)", func(b *Argument, ih Fact) {
			args := b.StepArgs("x", "l")
			b.Show("modus ponens on the step law", By(ih, b.Hyp(stepLaw).At(args[0], args[1])))
		})
	}))
	require.True(t, sec.Proved())
}

// TestStepArgs_AfterShaping: the arguments are read off the enclosing
// branch, so a StepArgs after a shaping step in the same body still
// finds them — the verb is not confined to the head of the body.
func TestStepArgs_AfterShaping(t *testing.T) {
	e := makeListTestEnv()
	goal, stepLaw := e.listGoal()
	sec := e.ctx.Section(goal)
	sec.Do(Derive(func(a *Argument) {
		a.Induct("l")
		a.Base("Q holds at nil by hypothesis", Assumption())
		a.Step("at cons(x, xs), after a step moved the spine", func(b *Argument, ih Fact) {
			denied := b.SupposeNot()
			args := b.StepArgs("x", "xs")
			b.Show("the step law at x and xs contradicts the denial", By(ih, denied, b.Hyp(stepLaw).At(args[0], args[1])))
		})
	}))
	require.True(t, sec.Proved())
}

// TestStepArgs_Refusals: the authoring errors, each a loud panic naming
// the shape — outside any induction, at the base case, with the wrong
// number of names, and re-pointing a live name.
func TestStepArgs_Refusals(t *testing.T) {
	e := makeListTestEnv()
	goal, _ := e.listGoal()

	t.Run("no enclosing induction", func(t *testing.T) {
		sec := e.ctx.Section(goal)
		msg := panicMessage(func() { sec.Do(Derive(func(a *Argument) { a.StepArgs("x", "xs") })) })
		require.Contains(t, msg, "Argument.StepArgs: no enclosing induction step")
	})

	t.Run("the base case introduces nothing", func(t *testing.T) {
		sec := e.ctx.Section(goal)
		msg := panicMessage(func() {
			sec.Do(Derive(func(a *Argument) {
				a.Induct("l")
				a.Base("names nothing", func(b *Argument) { b.StepArgs() })
			}))
		})
		require.Contains(t, msg, "introduces no constructor argument")
	})

	t.Run("one name per argument", func(t *testing.T) {
		sec := e.ctx.Section(goal)
		msg := panicMessage(func() {
			sec.Do(Derive(func(a *Argument) {
				a.Induct("l")
				a.Base("Q holds at nil by hypothesis", Assumption())
				a.Step("at cons", func(b *Argument, ih Fact) { b.StepArgs("x") })
			}))
		})
		require.Contains(t, msg, "takes 2 argument(s)")
		require.Contains(t, msg, "1 name(s) were given")
	})

	t.Run("a live name is not re-pointed", func(t *testing.T) {
		sec := e.ctx.Section(goal)
		msg := panicMessage(func() {
			sec.Do(Derive(func(a *Argument) {
				a.Induct("l")
				a.Base("Q holds at nil by hypothesis", Assumption())
				// "l" is the induction variable: as the HEAD's name it
				// would re-point a live spelling at another variable.
				a.Step("at cons", func(b *Argument, ih Fact) { b.StepArgs("l", "xs") })
			}))
		})
		require.Contains(t, msg, `Argument.StepArgs("l"): that name is already`)
	})
}
