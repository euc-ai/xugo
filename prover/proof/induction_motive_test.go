// induction_motive_test.go — the predicate of a cited induction read
// from the goal (induction_motive.go).
//
// Each proof case cites a principle before its predicate and has to
// close the section: the cases are proved from one resident conjunction
// of the obligations the READ predicate yields, so a predicate read
// wrongly leaves a case that does not follow. The reading cases state
// the tuple inductionMotive returns.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// motiveEnv serves three induction principles:
//
//   - zz_finite_induction, polymorphic in the element type, guarded:
//     ∀P. P(∅) ∧ (∀x s. P(s) ⇒ P(ins(x, s))) ⇒ ∀a. fin(a) ⇒ P(a)
//   - zz_closure_induction, a rule induction with a parameter of the
//     predicate's own type:
//     ∀R P. (∀x y. R(x, y) ⇒ P(x, y)) ∧ (∀x y z. P(x, y) ∧ P(y, z) ⇒ P(x, z))
//     ⇒ ∀x0 x1. tc(R, x0, x1) ⇒ P(x0, x1)
//   - zz_strong_induction, unguarded:
//     ∀P. (∀n. (∀m. m < n ⇒ P(m)) ⇒ P(n)) ⇒ ∀n. P(n)
//   - zz_finite_induction_on, polymorphic, with a condition Q on the
//     members bound after the predicate and stated by a guard that
//     applies it:
//     ∀P Q. P(∅) ∧ (∀x s. P(s) ∧ Q(x) ⇒ P(ins(x, s)))
//     ⇒ ∀a. (∀y. in(y, a) ⇒ Q(y)) ∧ fin(a) ⇒ P(a)
//
// and the constants they mention at the instance the sections use, the
// element type ind.
type motiveEnv struct {
	ctx *Script
	set core.HolType // ind → bool
	rel core.HolType // ind → ind → bool

	fin, ins, empty, tc, lt, in       *ext.TermWrapper
	finite, closure, strong, finiteOn Prop
}

func makeMotiveEnv(t *testing.T) *motiveEnv {
	t.Helper()
	env := makeStepTestEnv()
	ctx := NewScript(env)
	elem := core.MakeVarType("A")
	setOf := func(a core.HolType) core.HolType { return MakeFun(a, TypeBool) }
	relOf := func(a core.HolType) core.HolType { return MakeFun(a, MakeFun(a, TypeBool)) }
	ltType := MakeFun(numType, MakeFun(numType, TypeBool))
	for _, c := range []struct {
		name string
		ty   core.HolType
	}{
		{"zzMotiveFin", MakeFun(setOf(elem), TypeBool)},
		{"zzMotiveIns", MakeFun(elem, MakeFun(setOf(elem), setOf(elem)))},
		{"zzMotiveEmpty", setOf(elem)},
		{"zzMotiveTc", MakeFun(relOf(elem), relOf(elem))},
		{"zzMotiveIn", MakeFun(elem, MakeFun(setOf(elem), TypeBool))},
	} {
		env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta(core.TermName(c.name), c.ty))
	}
	at := func(a core.HolType) (fin, ins, empty, tc *ext.TermWrapper) {
		return ctx.Const("zzMotiveFin", MakeFun(setOf(a), TypeBool)),
			ctx.Const("zzMotiveIns", MakeFun(a, MakeFun(setOf(a), setOf(a)))),
			ctx.Const("zzMotiveEmpty", setOf(a)),
			ctx.Const("zzMotiveTc", MakeFun(relOf(a), relOf(a)))
	}
	e := &motiveEnv{ctx: ctx, set: setOf(TypeInd), rel: relOf(TypeInd)}
	e.fin, e.ins, e.empty, e.tc = at(TypeInd)
	e.lt = WrapTerm(core.MakeConstTerm(core.MakeConstMeta("<", ltType), ltType))
	memberOf := func(a core.HolType) *ext.TermWrapper {
		return ctx.Const("zzMotiveIn", MakeFun(a, MakeFun(setOf(a), TypeBool)))
	}
	e.in = memberOf(TypeInd)

	// The principles are stated at the letter.
	fin, ins, empty, tc := at(elem)
	P := Var("P", MakeFun(setOf(elem), TypeBool))
	x, s, a := Var("x", elem), Var("s", setOf(elem)), Var("a", setOf(elem))
	finite := ForAll(P)(P.Apply(empty).
		And(ForAll(x)(ForAll(s)(P.Apply(s).Imply(P.Apply(ins.Apply(x, s)))))).
		Imply(ForAll(a)(fin.Apply(a).Imply(P.Apply(a)))))
	e.finite = core.MakeProp(finite)

	R, PR := Var("R", relOf(elem)), Var("P", relOf(elem))
	y, z, x0, x1 := Var("y", elem), Var("z", elem), Var("x0", elem), Var("x1", elem)
	closure := ForAll(R)(ForAll(PR)(
		ForAll(x)(ForAll(y)(R.Apply(x, y).Imply(PR.Apply(x, y)))).
			And(ForAll(x)(ForAll(y)(ForAll(z)(PR.Apply(x, y).And(PR.Apply(y, z)).Imply(PR.Apply(x, z)))))).
			Imply(ForAll(x0)(ForAll(x1)(tc.Apply(R, x0, x1).Imply(PR.Apply(x0, x1)))))))
	e.closure = core.MakeProp(closure)

	n, m := Var("n", numType), Var("m", numType)
	PN := Var("P", MakeFun(numType, TypeBool))
	strong := ForAll(PN)(ForAll(n)(ForAll(m)(e.lt.Apply(m, n).Imply(PN.Apply(m))).Imply(PN.Apply(n))).
		Imply(ForAll(n)(PN.Apply(n))))
	e.strong = core.MakeProp(strong)

	// The member guard is stated ahead of fin(a), so the reading meets it
	// with the element type still a letter.
	QM := Var("Q", setOf(elem))
	finiteOn := ForAll(P)(ForAll(QM)(P.Apply(empty).
		And(ForAll(x)(ForAll(s)(P.Apply(s).And(QM.Apply(x)).Imply(P.Apply(ins.Apply(x, s)))))).
		Imply(ForAll(a)(ForAll(y)(memberOf(elem).Apply(y, a).Imply(QM.Apply(y))).And(fin.Apply(a)).Imply(P.Apply(a))))))
	e.finiteOn = core.MakeProp(finiteOn)

	serveThm(ctx, "zz_finite_induction_on", core.TestThm(finiteOn.Core()))
	serveThm(ctx, "zz_finite_induction", core.TestThm(finite.Core()))
	serveThm(ctx, "zz_closure_induction", core.TestThm(closure.Core()))
	serveThm(ctx, "zz_strong_induction", core.TestThm(strong.Core()))
	return e
}

// finiteCases is the two obligations of the finite induction at a
// predicate over sets of ind, as one conjunction.
func (e *motiveEnv) finiteCases(at func(s *ext.TermWrapper) *ext.TermWrapper) *ext.TermWrapper {
	x, s := Var("x", TypeInd), Var("s", e.set)
	return at(e.empty).And(ForAll(x)(ForAll(s)(at(s).Imply(at(e.ins.Apply(x, s))))))
}

// (a) The index is read off a premise: the finite induction, cited
// bare, with the fact `fin(c)` beside it. The predicate is the goal
// `Q(c)` abstracted over c.
func TestByInduction_PredicateReadAtAPremise(t *testing.T) {
	e := makeMotiveEnv(t)
	Q := Var("Q", MakeFun(e.set, TypeBool))
	c := Var("c", e.set)
	cases := e.finiteCases(func(s *ext.TermWrapper) *ext.TermWrapper { return Q.Apply(s) })
	sec := e.ctx.Section(core.MakeProp(cases.Imply(e.fin.Apply(c).Imply(Q.Apply(c))).Core()))
	sec.Do(Derive(func(a *Argument) {
		given := a.Assume()
		finite := a.Assume()
		a.Show("by induction on the finite set c",
			ByInduction(depName("zz_finite_induction"), finite,
				MakeCase("at the empty set", By(given)),
				MakeCase("across an insertion", By(given))))
	}))
	require.True(t, sec.Proved())
}

// (b) A rule induction cited bare: the premise `tc(R0, a, b)` fixes the
// PARAMETER and the index, and the goal `S(b, a)` abstracts to
// `λx y. S(y, x)` — the index in the order the principle's conclusion
// applies its predicate, whatever order the goal mentions it in.
func TestByInduction_PremiseFixesParameterAndIndex(t *testing.T) {
	e := makeMotiveEnv(t)
	S, R0 := Var("S", e.rel), Var("R0", e.rel)
	a0, b0 := Var("a", TypeInd), Var("b", TypeInd)
	x, y, z := Var("x", TypeInd), Var("y", TypeInd), Var("z", TypeInd)
	cases := ForAll(x)(ForAll(y)(R0.Apply(x, y).Imply(S.Apply(y, x)))).
		And(ForAll(x)(ForAll(y)(ForAll(z)(S.Apply(y, x).And(S.Apply(z, y)).Imply(S.Apply(z, x))))))
	sec := e.ctx.Section(core.MakeProp(cases.Imply(e.tc.Apply(R0, a0, b0).Imply(S.Apply(b0, a0))).Core()))
	sec.Do(Derive(func(a *Argument) {
		given := a.Assume()
		walk := a.Assume()
		a.Show("by induction on the walk",
			ByInduction(depName("zz_closure_induction"), walk,
				MakeCase("one step reversed", By(given)),
				MakeCase("two reversed walks joined in reverse order", By(given))))
	}))
	require.True(t, sec.Proved())

	// The same cite at its parameter reads the same predicate.
	tuple, err := inductionMotive(e.closureAt(), []Term{R0.Core()},
		core.MakeProp(S.Apply(b0, a0).Core()), []Term{e.tc.Apply(R0, a0, b0).Core()}, nil, "the principle")
	require.NoError(t, err)
	require.Len(t, tuple, 4)
	u, v := Var("u", TypeInd), Var("v", TypeInd)
	require.True(t, tuple[1].AlphaEquals(u.To(v.To(S.Apply(v, u))).Core()),
		"the predicate is λx y. S(y, x); got %s", ext.PrintTerm(tuple[1]))
	require.True(t, tuple[2].AlphaEquals(a0.Core()) && tuple[3].AlphaEquals(b0.Core()), "the index is (a, b)")
}

// closureAt is the closure induction at the element type ind.
func (e *motiveEnv) closureAt() Prop {
	return core.PropTypeInst(e.closure, core.MakeTypeSubst(core.MakeVarType("A"), TypeInd))
}

// (c) The goal is the principle's conclusion, its guard conjoined with
// a hypothesis of the statement: `∀s. fin(s) ∧ B(s) ⇒ C(s)`. No premise
// states the guard, so the predicate is the goal's body without it,
// `λs. B(s) ⇒ C(s)`.
func TestByInduction_PredicateReadOffTheGoalsBinders(t *testing.T) {
	e := makeMotiveEnv(t)
	B, C := Var("B", MakeFun(e.set, TypeBool)), Var("C", MakeFun(e.set, TypeBool))
	s := Var("s", e.set)
	cases := e.finiteCases(func(s *ext.TermWrapper) *ext.TermWrapper { return B.Apply(s).Imply(C.Apply(s)) })
	goal := ForAll(s)(e.fin.Apply(s).And(B.Apply(s)).Imply(C.Apply(s)))
	sec := e.ctx.Section(core.MakeProp(cases.Imply(goal).Core()))
	sec.Do(Derive(func(a *Argument) {
		given := a.Assume()
		a.Show("by induction on a finite set",
			ByInduction(depName("zz_finite_induction"),
				MakeCase("at the empty set", By(given)),
				MakeCase("across an insertion", By(given))))
	}))
	require.True(t, sec.Proved())
}

// (d) An unguarded principle: strong induction cited bare at the goal
// `∀n. Q(n)`. The predicate is the goal's body.
func TestByInduction_UnguardedPrincipleReadsTheGoalsBody(t *testing.T) {
	e := makeMotiveEnv(t)
	Q := Var("Q", MakeFun(numType, TypeBool))
	n, m := Var("n", numType), Var("m", numType)
	// Q holds at n or fails somewhere below: the obligation is proved
	// from it, not restated.
	closure := ForAll(n)(Q.Apply(n).Or(Exists(m)(e.lt.Apply(m, n).And(Not(Q.Apply(m))))))
	sec := e.ctx.Section(core.MakeProp(closure.Imply(ForAll(n)(Q.Apply(n))).Core()))
	sec.Do(Derive(func(a *Argument) {
		given := a.Assume()
		a.Show("by strong induction",
			ByInduction(depName("zz_strong_induction"), Normalized,
				MakeCase("Q holds at n once it holds everywhere below n", By(given))))
	}))
	require.True(t, sec.Proved())
}

// (e) Generalizing: the goal `C(c)` holds under a hypothesis `B(c)` on
// the index, which the induction has to carry. The predicate is
// `λs. B(s) ⇒ C(s)` and the terminal discharges it at c from the fact.
func TestByInduction_GeneralizingCarriesAHypothesis(t *testing.T) {
	e := makeMotiveEnv(t)
	B, C := Var("B", MakeFun(e.set, TypeBool)), Var("C", MakeFun(e.set, TypeBool))
	c := Var("c", e.set)
	cases := e.finiteCases(func(s *ext.TermWrapper) *ext.TermWrapper { return B.Apply(s).Imply(C.Apply(s)) })
	sec := e.ctx.Section(core.MakeProp(
		cases.Imply(e.fin.Apply(c).Imply(B.Apply(c).Imply(C.Apply(c)))).Core()))
	sec.Do(Derive(func(a *Argument) {
		given := a.Assume()
		finite := a.Assume()
		bounded := a.Assume()
		a.Show("by induction on the finite set c, carrying its bound",
			ByInduction(depName("zz_finite_induction"), finite, Generalizing(bounded),
				MakeCase("at the empty set", By(given)),
				MakeCase("across an insertion", By(given))))
	}))
	require.True(t, sec.Proved())
}

// (f) The reading agrees with the written cite: the tuple read off a
// premise is the one a cite at the predicate and the index spells, so
// the obligations are the same.
func TestInductionMotive_ReadsTheTupleTheWrittenCiteSpells(t *testing.T) {
	e := makeMotiveEnv(t)
	Q := Var("Q", MakeFun(e.set, TypeBool))
	c, s := Var("c", e.set), Var("s", e.set)
	goal := core.MakeProp(Q.Apply(c).Core())
	tuple, typed, err := InductionMotive(e.finite, nil, goal, []Term{e.fin.Apply(c).Core()}, nil, "the principle")
	require.NoError(t, err)
	require.Len(t, tuple, 2)
	require.False(t, ext.PropHasTypeVars(typed), "the statement comes back typed at the tuple's instance")
	require.True(t, tuple[0].AlphaEquals(s.To(Q.Apply(s)).Core()), "the predicate is λs. Q(s); got %s", ext.PrintTerm(tuple[0]))
	require.True(t, tuple[1].AlphaEquals(c.Core()), "the index is c")

	script := NewScript(makeStepTestEnv())
	read := inductionObligations(script, MakeFact(e.finite).At(WrapTerm(tuple[0]), WrapTerm(tuple[1])), 2, goal)
	written := inductionObligations(script, MakeFact(e.finite).At(s.To(Q.Apply(s)), c), 2, goal)
	for i := range written {
		require.True(t, read[i].Conclusion().AlphaEquals(written[i].Conclusion()),
			"obligation %d: read %s, written %s", i, ext.PrintTerm(read[i].Conclusion()), ext.PrintTerm(written[i].Conclusion()))
	}
}

// (g) What the reading refuses, in words that say which reading failed.
func TestInductionMotive_Refusals(t *testing.T) {
	e := makeMotiveEnv(t)
	Q := Var("Q", MakeFun(e.set, TypeBool))
	c := Var("c", e.set)
	d := Var("d", TypeInd)

	// An index that is a compound term: the goal is not abstracted over it.
	compound := e.ins.Apply(d, c)
	_, _, err := InductionMotive(e.finite, nil, core.MakeProp(Q.Apply(compound).Core()),
		[]Term{e.fin.Apply(compound).Core()}, nil, "the principle")
	require.ErrorContains(t, err, "not a tuple of distinct variables")
	require.ErrorContains(t, err, "is written")

	// No premise states the guard and the goal is no ∀-statement.
	_, _, err = InductionMotive(e.finite, nil, core.MakeProp(Q.Apply(c).Core()), nil, nil, "the principle")
	require.ErrorContains(t, err, "fits neither reading")
	require.ErrorContains(t, err, "zzMotiveFin(a)", "the message names the guard a premise would state")

	// The goal is a ∀-statement without the principle's guard.
	s := Var("s", e.set)
	_, _, err = InductionMotive(e.finite, nil, core.MakeProp(ForAll(s)(Q.Apply(s)).Core()), nil, nil, "the principle")
	require.ErrorContains(t, err, "is not among the goal's antecedents")

	// A tuple that reaches the predicate is read as written.
	_, _, err = InductionMotive(e.finite, []Term{Q.Core()}, core.MakeProp(Q.Apply(c).Core()), nil, nil, "the principle")
	require.ErrorContains(t, err, "reaches its predicate")

	// Generalizing with no premise to fix the index.
	_, _, err = InductionMotive(e.finite, nil, core.MakeProp(ForAll(s)(e.fin.Apply(s).Imply(Q.Apply(s))).Core()),
		nil, []Term{Q.Apply(c).Core()}, "the principle")
	require.ErrorContains(t, err, "Generalizing carries hypotheses")
}

// (h) Generalizing beside a cite that states its predicate is refused:
// what the predicate assumes is written in it.
func TestByInduction_GeneralizingBesideAWrittenPredicateIsRefused(t *testing.T) {
	e := makeMotiveEnv(t)
	Q := Var("Q", MakeFun(e.set, TypeBool))
	c := Var("c", e.set)
	cases := e.finiteCases(func(s *ext.TermWrapper) *ext.TermWrapper { return Q.Apply(s) })
	sec := e.ctx.Section(core.MakeProp(cases.Imply(e.fin.Apply(c).Imply(Q.Apply(c))).Core()))
	msg := panicTextOf(t, func() {
		sec.Do(Derive(func(a *Argument) {
			given := a.Assume()
			finite := a.Assume()
			a.Show("the predicate is written",
				ByInduction(At(depName("zz_finite_induction"), Q, c), finite, Generalizing(finite),
					MakeCase("at the empty set", By(given)),
					MakeCase("across an insertion", By(given))))
		}))
	})
	require.Contains(t, msg, "cited at its predicate")
}

// (i) A binder stated after the predicate, fixed by a guard that applies
// it: the premise `∀y. in(y, c) ⇒ B(y, k)` states the principle's guard
// `∀y. in(y, a) ⇒ Q(y)` at the index c and at Q := λy. B(y, k), which no
// first-order reading of the two aligns. The cite stays bare, and the
// cases are proved at that Q.
func TestByInduction_GuardFixesABinderStatedAfterThePredicate(t *testing.T) {
	e := makeMotiveEnv(t)
	G := Var("G", MakeFun(e.set, TypeBool))
	B := Var("B", e.rel)
	c, k := Var("c", e.set), Var("k", TypeInd)
	x, y, s := Var("x", TypeInd), Var("y", TypeInd), Var("s", e.set)
	cases := G.Apply(e.empty).
		And(ForAll(x)(ForAll(s)(G.Apply(s).And(B.Apply(x, k)).Imply(G.Apply(e.ins.Apply(x, s))))))
	members := ForAll(y)(e.in.Apply(y, c).Imply(B.Apply(y, k)))
	sec := e.ctx.Section(core.MakeProp(
		cases.Imply(e.fin.Apply(c).Imply(members.Imply(G.Apply(c)))).Core()))
	sec.Do(Derive(func(a *Argument) {
		given := a.Assume()
		finite := a.Assume()
		within := a.Assume()
		a.Show("by induction on the finite set c, whose members stand in B to k",
			ByInduction(depName("zz_finite_induction_on"), finite, within,
				MakeCase("at the empty set", By(given)),
				MakeCase("across the insertion of a member", By(given))))
	}))
	require.True(t, sec.Proved())

	tuple, typed, err := InductionMotive(e.finiteOn, nil, core.MakeProp(G.Apply(c).Core()),
		[]Term{e.fin.Apply(c).Core(), members.Core()}, nil, "the principle")
	require.NoError(t, err)
	require.Len(t, tuple, 3)
	require.False(t, ext.PropHasTypeVars(typed), "the statement comes back typed at the tuple's instance")
	require.True(t, tuple[0].AlphaEquals(s.To(G.Apply(s)).Core()), "the predicate is λs. G(s); got %s", ext.PrintTerm(tuple[0]))
	require.True(t, tuple[1].AlphaEquals(y.To(B.Apply(y, k)).Core()), "Q is λy. B(y, k); got %s", ext.PrintTerm(tuple[1]))
	require.True(t, tuple[2].AlphaEquals(c.Core()), "the index is c")
}

// (j) The same principle at a goal that is its conclusion: the member
// guard is among the goal's antecedents, and the tuple the reading
// returns runs past the predicate to Q, the index left to the goal's
// binder.
func TestByInduction_GoalsAntecedentFixesABinderStatedAfterThePredicate(t *testing.T) {
	e := makeMotiveEnv(t)
	G := Var("G", MakeFun(e.set, TypeBool))
	B := Var("B", e.rel)
	k := Var("k", TypeInd)
	x, y, s := Var("x", TypeInd), Var("y", TypeInd), Var("s", e.set)
	cases := G.Apply(e.empty).
		And(ForAll(x)(ForAll(s)(G.Apply(s).And(B.Apply(x, k)).Imply(G.Apply(e.ins.Apply(x, s))))))
	goal := ForAll(s)(ForAll(y)(e.in.Apply(y, s).Imply(B.Apply(y, k))).And(e.fin.Apply(s)).Imply(G.Apply(s)))
	sec := e.ctx.Section(core.MakeProp(cases.Imply(goal).Core()))
	sec.Do(Derive(func(a *Argument) {
		given := a.Assume()
		a.Show("by induction on a finite set whose members stand in B to k",
			ByInduction(depName("zz_finite_induction_on"),
				MakeCase("at the empty set", By(given)),
				MakeCase("across the insertion of a member", By(given))))
	}))
	require.True(t, sec.Proved())

	tuple, _, err := InductionMotive(e.finiteOn, nil, core.MakeProp(goal.Core()), nil, nil, "the principle")
	require.NoError(t, err)
	require.Len(t, tuple, 2, "the predicate and Q; the index is the goal's binder")
	require.True(t, tuple[0].AlphaEquals(s.To(G.Apply(s)).Core()), "the predicate is λs. G(s); got %s", ext.PrintTerm(tuple[0]))
	require.True(t, tuple[1].AlphaEquals(y.To(B.Apply(y, k)).Core()), "Q is λy. B(y, k); got %s", ext.PrintTerm(tuple[1]))
}

// (k) A binder stated after the predicate that no listed fact fixes is
// refused by the guard a fact would state, not by a cite at it, which
// would reach the predicate.
func TestInductionMotive_BinderAfterThePredicateLeftOpen(t *testing.T) {
	e := makeMotiveEnv(t)
	G := Var("G", MakeFun(e.set, TypeBool))
	B := Var("B", e.rel)
	c, k, y := Var("c", e.set), Var("k", TypeInd), Var("y", TypeInd)

	// The finiteness is listed and the condition on the members is not.
	_, _, err := InductionMotive(e.finiteOn, nil, core.MakeProp(G.Apply(c).Core()),
		[]Term{e.fin.Apply(c).Core()}, nil, "the principle")
	require.ErrorContains(t, err, "leave Q open, which the principle binds after its predicate")
	require.ErrorContains(t, err, "a fact that states its guard ∀y.(zzMotiveIn(y, a) ⇒ Q(y)) fixes it")

	// A condition stated at another set fixes the index there, and the
	// goal is no predicate of that set.
	d := Var("d", e.set)
	other := ForAll(y)(e.in.Apply(y, d).Imply(B.Apply(y, k)))
	_, _, err = InductionMotive(e.finiteOn, nil, core.MakeProp(G.Apply(c).Core()),
		[]Term{e.fin.Apply(c).Core(), other.Core()}, nil, "the principle")
	require.ErrorContains(t, err, "fix its index at (d), which the goal does not mention")
}
