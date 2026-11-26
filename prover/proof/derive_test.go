// derive_test.go — the deduction block forms (derive.go): Given, the
// branch form that receives the hypothesis its parent step introduced.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext"

	"github.com/stretchr/testify/require"
)

// =======================================================================
// Given — the three parent shapes
// =======================================================================
//
// A Given body is legal under any step whose branch adds exactly one
// hypothesis. The three that occur in the corpus are covered here: an
// Induct step case (the IH), a ByCaseStep branch (the discriminant and
// its negation), and a SplitDisj arm (the disjunct).

// givenTestEnv is the shared setup: an env carrying the package's num
// induction principle (try_test.go's numInductionThm — TestThm is
// acceptable inside _test.go, the template analyzer reads the statement
// only) plus the predicate vocabulary the goals below are built from.
type givenTestEnv struct {
	ctx  *Script
	x, k *ext.TermWrapper
	P, Q *ext.TermWrapper // A → bool
	R    *ext.TermWrapper // num → bool
}

func makeGivenTestEnv() *givenTestEnv {
	env := makeStepTestEnv()
	env.LibraryThms = map[string]Thm{"num_induction": numInductionThm}
	return &givenTestEnv{
		ctx: NewScript(env),
		x:   Var("x", TypeA),
		k:   Var("k", numType),
		P:   Var("P", MakeFun(TypeA, TypeBool)),
		Q:   Var("Q", MakeFun(TypeA, TypeBool)),
		R:   Var("R", MakeFun(numType, TypeBool)),
	}
}

func sucOf(t Term) Term { return ext.Apply(sucTerm, t) }

// TestGiven_InductStepCase: the motivating shape — the step case
// receives the induction hypothesis as a value, with no text restating
// what the engine just built.
//
//	R(_0), ∀n. R(n) ⇒ R(suc n) ⊢ R(k)
func TestGiven_InductStepCase(t *testing.T) {
	e := makeGivenTestEnv()
	n := Var("n", numType)
	stepHyp := ForAll(n)(e.R.Apply(n).Imply(e.R.Apply(sucOf(n))))
	base := e.R.Apply(zeroTerm)

	sec := e.ctx.Section(MakeProp(e.R.Apply(e.k), base, stepHyp))
	sec.Do(Derive(func(a *Argument) {
		a.Induct(e.k)
		a.Base("base k = 0: the base hypothesis IS the goal", Assumption())
		a.Step("step k → suc k: the induction hypothesis feeds the step law", func(a *Argument, ih Fact) {
			law := a.Hyp(stepHyp.Core())
			a.Show("the step law at k carries R(k) to R(suc k)", By(ih, law.At(e.k)))
		})
	}))
	require.True(t, sec.Proved(), "Given under an Induct step case did not close the section")
}

// TestGiven_ByCaseBranches: both branches of a classical split are
// Given bodies — one receives the discriminant, the other its negation.
//
//	P(x) ⇒ R(x), ¬P(x) ⇒ R(x) ⊢ R(x)
func TestGiven_ByCaseBranches(t *testing.T) {
	e := makeGivenTestEnv()
	R := Var("R", MakeFun(TypeA, TypeBool))
	pos := e.P.Apply(e.x).Imply(R.Apply(e.x))
	neg := Not(e.P.Apply(e.x)).Imply(R.Apply(e.x))

	sec := e.ctx.Section(MakeProp(R.Apply(e.x), pos, neg))
	sec.Do(Derive(func(a *Argument) {
		a.Cases(e.P.Apply(e.x))
		a.When("P(x): the positive law applies", func(a *Argument, h Fact) {
			a.Show("modus ponens on the positive law", By(h, a.Hyp(pos.Core())))
		})
		a.Otherwise("¬P(x): the negative law applies", func(a *Argument, h Fact) {
			a.Show("modus ponens on the negative law", By(h, a.Hyp(neg.Core())))
		})
	}))
	require.True(t, sec.Proved(), "Given under a ByCaseStep branch did not close the section")
}

// TestGiven_SplitDisjArms: each arm of a disjunctive hypothesis receives
// its own disjunct.
//
//	P(x) ∨ Q(x), P(x) ⇒ R(x), Q(x) ⇒ R(x) ⊢ R(x)
func TestGiven_SplitDisjArms(t *testing.T) {
	e := makeGivenTestEnv()
	R := Var("R", MakeFun(TypeA, TypeBool))
	fromP := e.P.Apply(e.x).Imply(R.Apply(e.x))
	fromQ := e.Q.Apply(e.x).Imply(R.Apply(e.x))

	sec := e.ctx.Section(MakeProp(R.Apply(e.x),
		e.P.Apply(e.x).Or(e.Q.Apply(e.x)), fromP, fromQ))
	sec.Do(SplitDisj(
		LeftHolds("P(x)", Given(func(a *Argument, h Fact) {
			a.Show("modus ponens on the P law", By(h, a.Hyp(fromP.Core())))
		})),
		RightHolds("Q(x)", Given(func(a *Argument, h Fact) {
			a.Show("modus ponens on the Q law", By(h, a.Hyp(fromQ.Core())))
		})),
	))
	require.True(t, sec.Proved(), "Given under a SplitDisj arm did not close the section")
}

// =======================================================================
// Given — the loud failures
// =======================================================================

// TestGiven_NoParentStep: a Given at a section root has no branch
// hypothesis to receive.
// TestGiven_MidChain: a Given after an Unless INSIDE the same body binds
// the hypothesis the linearizer's surviving branch introduced. This is
// the shape that distinguishes anchor.parent from root.parent — root is
// still the enclosing body's node here, so diffing against it would see
// that body's own hypotheses instead of ¬P(x).
//
//	P(x) ⇒ R(x), ¬P(x) ⇒ R(x) ⊢ R(x)
func TestGiven_MidChain(t *testing.T) {
	e := makeGivenTestEnv()
	R := Var("R", MakeFun(TypeA, TypeBool))
	pos := e.P.Apply(e.x).Imply(R.Apply(e.x))
	neg := Not(e.P.Apply(e.x)).Imply(R.Apply(e.x))

	sec := e.ctx.Section(MakeProp(R.Apply(e.x), pos, neg))
	sec.Do(Chain(
		// The true branch is discharged inline; the proof continues on
		// the ¬P(x) branch, which is where the Given picks it up.
		Unless(e.P.Apply(e.x).Core(),
			"P(x) holds: the positive law closes it",
			Derive(func(b *Argument) {
				hp := b.Hyp(e.P.Apply(e.x).Core())
				b.Show("modus ponens on the positive law", By(hp, b.Hyp(pos.Core())))
			})),
		Given(func(b *Argument, notP Fact) {
			b.Show("modus ponens on the negative law", By(notP, b.Hyp(neg.Core())))
		}),
	))
	require.True(t, sec.Proved(), "Given used mid-chain did not close the section")
}

func TestGiven_NoParentStep(t *testing.T) {
	e := makeGivenTestEnv()
	sec := e.ctx.Section(MakeProp(e.P.Apply(e.x), e.P.Apply(e.x)))
	requirePanicContains(t, "Given: no parent step", func() {
		sec.Do(Given(func(a *Argument, h Fact) { a.Show("unreachable", Assumption()) }))
	})
}

// TestGiven_ParentAddedNoHypothesis: an induction BASE case introduces
// nothing — the message sends the author to Derive.
func TestGiven_ParentAddedNoHypothesis(t *testing.T) {
	e := makeGivenTestEnv()
	n := Var("n", numType)
	stepHyp := ForAll(n)(e.R.Apply(n).Imply(e.R.Apply(sucOf(n))))
	sec := e.ctx.Section(MakeProp(e.R.Apply(e.k), e.R.Apply(zeroTerm), stepHyp))
	requirePanicContains(t, "Given: the parent step introduced 0 hypotheses", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Induct(e.k)
			a.Base("base", func(a *Argument, h Fact) { a.Show("unreachable", Assumption()) })
			a.Step("step", Assumption())
		}))
	})
}

// TestGiven_ParentAddedSeveralHypotheses: a ⇔-hyp split hands its
// branch BOTH sides — Given binds one, so the message names the
// alternative (Derive + a.Hyp per hypothesis).
func TestGiven_ParentAddedSeveralHypotheses(t *testing.T) {
	e := makeGivenTestEnv()
	R := Var("R", MakeFun(TypeA, TypeBool))
	sec := e.ctx.Section(MakeProp(R.Apply(e.x), e.P.Apply(e.x).Eq(e.Q.Apply(e.x))))
	requirePanicContains(t, "Given: the parent step introduced 2 hypotheses", func() {
		sec.Do(SplitHypIff(
			BothHold("both", Given(func(a *Argument, h Fact) { a.Show("unreachable", Assumption()) })),
			NeitherHolds("neither", Assumption()),
		))
	})
}

// TestGiven_BodyMustCloseItsBranch: Given carries Derive's must-close
// contract.
func TestGiven_BodyMustCloseItsBranch(t *testing.T) {
	e := makeGivenTestEnv()
	R := Var("R", MakeFun(TypeA, TypeBool))
	sec := e.ctx.Section(MakeProp(R.Apply(e.x), e.P.Apply(e.x).Or(e.Q.Apply(e.x))))
	requirePanicContains(t, "Given: block ended with 1 open goal(s)", func() {
		sec.Do(SplitDisj(
			LeftHolds("P(x)", Given(func(a *Argument, h Fact) { _ = h })),
			RightHolds("Q(x)", Assumption()),
		))
	})
}

// =======================================================================
// Denote — the abbreviation verb
// =======================================================================

// TestDenote_NamesTheTermAndReturnsTheEquation: the third deduction
// verb next to Have and Obtain, and the one with no proof obligation.
// The spine's goal comes back speaking about the NAME, and the defining
// equation is returned as a Fact a later premise list can cite.
//
//	P(f(x)), ∀y. P(y) ⇒ Q(y) ⊢ Q(f(x))
//
// naming f(x) turns the whole argument into one about `d`.
func TestDenote_NamesTheTermAndReturnsTheEquation(t *testing.T) {
	e := makeGivenTestEnv()
	f := Var("f", MakeFun(TypeA, TypeA))
	y := Var("y", TypeA)
	fx := f.Apply(e.x)
	law := ForAll(y)(e.P.Apply(y).Imply(e.Q.Apply(y)))

	sec := e.ctx.Section(MakeProp(e.Q.Apply(fx), e.P.Apply(fx), law))
	sec.Do(Derive(func(a *Argument) {
		d := a.Denote("d", fx)
		require.NotNil(t, d.handle, "Denote must return the defining equation as a resident fact")

		// The spine now speaks about d, not about f(x).
		dVar := Var("d", TypeA)
		require.True(t, a.Goal().HasHyp(ext.Eq(dVar.Core(), fx.Core())),
			"the defining equation d = f(x) must be resident:\n%s", a.Goal())

		// The denote leaves the spine in ⊥-form (the negated conclusion
		// is among the hyps), so the close is a plain refutation.
		a.Show("the law at d carries P(d) to Q(d)", CnfRefute())
	}))
	require.True(t, sec.Proved(), "a Derive block using Denote did not close the section")
}

// The abbreviation must fail on the line that writes it, not downstream:
// a term the goal does not contain, and an empty name (the anonymous
// form is the engine's own search stage, never an authoring move).
func TestDenote_RejectsAbsentTermAndEmptyName(t *testing.T) {
	e := makeGivenTestEnv()
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA))

	run := func(body func(a *Argument)) (msg any) {
		defer func() { msg = recover() }()
		sec := e.ctx.Section(MakeProp(e.Q.Apply(f.Apply(e.x)), e.P.Apply(f.Apply(e.x))))
		sec.Do(Derive(body))
		return nil
	}

	require.NotNil(t, run(func(a *Argument) { a.Denote("d", g.Apply(e.x)) }),
		"naming a term the goal does not contain must panic")
	require.NotNil(t, run(func(a *Argument) { a.Denote("", f.Apply(e.x)) }),
		"an unnamed abbreviation is not an authoring move")
}
