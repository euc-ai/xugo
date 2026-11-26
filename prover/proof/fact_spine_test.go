// fact_spine_test.go — the spine/step surface of the fact layer:
// Broadcast (a By whose shaping fans the residual closes every leaf),
// Fact as a spine step (a.Do(f.At(w…)) grounds for a downstream STEP),
// and Unpack on a NAMED fact (the naming path for the resident a
// `Cite(X) + StripQuant()` pair leaves anonymous).

package proof

import (
	"strconv"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// spineTestEnv: predicate CONSTS over ind plus a propositional atom —
// enough to build ∀/∃ facts whose refutations are trivial and
// deterministic. The predicates are consts (not Vars) because the
// Unpack tests cite them inside TestThm "theorems", and a lemma with
// free variables would be ∀-closed over them on install — registry
// entries are closed formulas, and the tests mirror that.
type spineTestEnv struct {
	ctx    *Script
	R1, R2 *ext.TermWrapper // ind → bool
	S      *ext.TermWrapper // ind → ind → bool
	T      *ext.TermWrapper // ind → ind → ind → bool
	Qb     *ext.TermWrapper // bool atom
	c      *ext.TermWrapper // a ground point
}

func makeSpineTestEnv() *spineTestEnv {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	predTy := MakeFun(TypeInd, TypeBool)
	relTy := MakeFun(TypeInd, predTy)
	triTy := MakeFun(TypeInd, relTy)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("spineR1", predTy))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("spineR2", predTy))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("spineS", relTy))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("spineT", triTy))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("spineQ", TypeBool))
	return &spineTestEnv{
		ctx: ctx,
		R1:  ctx.Const("spineR1", predTy),
		R2:  ctx.Const("spineR2", predTy),
		S:   ctx.Const("spineS", relTy),
		T:   ctx.Const("spineT", triTy),
		Qb:  ctx.Const("spineQ", TypeBool),
		c:   Var("c", TypeInd),
	}
}

// =======================================================================
// Broadcast
// =======================================================================

// broadcastFanSetup builds the fanning shape: a conjunction goal
// q1(rhs) ∧ q2(rhs) whose conjuncts each need their OWN refutation —
// rhs is an AC-permutation of lhs, so each leaf closes only by
// paramodulating over the resident assoc/sym ∀-equations, which Basic's
// simplification cannot do. The Normalized shaping fans the conjunction
// into two such leaves (probed: 2 leaves, one CnfRefute each).
func broadcastFanSetup() (e *acRegroupTestEnv, sec *GoalStackNode, h1t, h2t Term) {
	e = makeACRegroupTestEnv(false)
	q1 := Var("q1", MakeFun(TypeInd, TypeBool))
	q2 := Var("q2", MakeFun(TypeInd, TypeBool))
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.c, e.plus.Apply(e.b, e.a))
	sec = e.ctx.Section(prop.MakeProp(q1.Apply(rhs).And(q2.Apply(rhs)),
		q1.Apply(lhs), q2.Apply(lhs)))
	return e, sec, q1.Apply(lhs).Core(), q2.Apply(lhs).Core()
}

// TestBy_BroadcastClosesFannedResidual: the motivating shape — the
// Normalized shaping fans the residual, and the terminal refutation
// runs once per leaf, from the same premises.
func TestBy_BroadcastClosesFannedResidual(t *testing.T) {
	e, sec, h1t, h2t := broadcastFanSetup()
	sec.Do(Derive(func(a *Argument) {
		h1, h2 := a.Hyp(h1t), a.Hyp(h2t)
		a.Show("each conjunct is the AC-permuted fact",
			By(Normalized, Broadcast, h1, h2, e.assoc, e.sym))
	}))
	require.True(t, sec.Proved(),
		"By(Normalized, Broadcast, …) did not close the fanned residual")
}

// TestBy_ConjunctiveGoalClosesConjunctByConjunct: a conjunctive goal
// is its conjuncts to the conditioning stage, which splits it and
// closes each in its turn — no Broadcast, and no shaping to fan it.
// The same close under Normalized is the same: the stage has split the
// goal before the shaping sees it.
func TestBy_ConjunctiveGoalClosesConjunctByConjunct(t *testing.T) {
	for name, shaped := range map[string]bool{"plain": false, "Normalized": true} {
		e, sec, h1t, h2t := broadcastFanSetup()
		sec.Do(Derive(func(a *Argument) {
			h1, h2 := a.Hyp(h1t), a.Hyp(h2t)
			if shaped {
				a.Show("each conjunct is the AC-permuted fact", By(Normalized, h1, h2, e.assoc, e.sym))
				return
			}
			a.Show("each conjunct is the AC-permuted fact", By(h1, h2, e.assoc, e.sym))
		}))
		require.True(t, sec.Proved(), "%s: the conjunctive goal did not close conjunct by conjunct", name)
	}
}

// shapingFanSetup builds a fan the SHAPING makes and the conditioning
// stage does not: an ⇔ goal, which Normalized turns into its two
// directions, each needing its own refutation over the AC laws. The two
// sides meet through both laws, so no one law's rewrite carries a
// direction's conclusion into its hypothesis and closes it ahead of the
// refuter.
func shapingFanSetup() (e *acRegroupTestEnv, sec *GoalStackNode) {
	e = makeACRegroupTestEnv(false)
	q := Var("q", MakeFun(TypeInd, TypeBool))
	lhs := e.plus.Apply(e.plus.Apply(e.a, e.b), e.c)
	rhs := e.plus.Apply(e.plus.Apply(e.c, e.a), e.b)
	sec = e.ctx.Section(prop.MakeProp(ext.Apply(core.IFF(), q.Apply(rhs), q.Apply(lhs))))
	return e, sec
}

// TestBy_FannedResidualWithoutBroadcastIsLoud: a fan the shaping makes
// is the author's to declare — the close WITHOUT Broadcast takes one
// leaf, panics on the rest, and the panic names the option; with it the
// close runs once per leaf.
func TestBy_FannedResidualWithoutBroadcastIsLoud(t *testing.T) {
	e, sec := shapingFanSetup()
	requirePanicContains(t, "Broadcast", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Show("fans into two leaves, single-leaf close", By(Normalized, e.assoc, e.sym))
		}))
	})

	// A close that returns with a leaf open prints its premise list
	// beside the residual, as a close that fails outright does.
	e, sec = shapingFanSetup()
	requirePanicContains(t, "are still open:", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Show("fans into two leaves, single-leaf close", By(Normalized, e.assoc, e.sym))
		}))
	})
	e, sec = shapingFanSetup()
	requirePanicContains(t, "\nwith premises:\n  ", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Show("fans into two leaves, single-leaf close", By(Normalized, e.assoc, e.sym))
		}))
	})

	e, sec = shapingFanSetup()
	sec.Do(Derive(func(a *Argument) {
		a.Show("each direction is the AC-permuted fact", By(Normalized, Broadcast, e.assoc, e.sym))
	}))
	require.True(t, sec.Proved())
}

// TestBy_BroadcastSingleLeafIsHarmless: Broadcast on a close whose
// residual never fans degrades to the plain single-leaf close.
func TestBy_BroadcastSingleLeafIsHarmless(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	allR1 := ForAll(x)(e.R1.Apply(x))

	sec := e.ctx.Section(MakeProp(e.R1.Apply(e.c), allR1))
	sec.Do(Derive(func(a *Argument) {
		h1 := a.Hyp(allR1.Core())
		a.Show("one leaf, broadcast anyway", By(Broadcast, h1))
	}))
	require.True(t, sec.Proved())
}

// TestBy_ShapingOptionsMerge: shaping values merge (the ε-heavy
// Denoted+HilbertDenoted combination); a no-op Hilbert pass is
// recover-absorbed rather than read as a premise error. Conflicting
// denote sizes stay loud.
func TestBy_ShapingOptionsMerge(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	allR1 := ForAll(x)(e.R1.Apply(x))

	sec := e.ctx.Section(MakeProp(e.R1.Apply(e.c), allR1))
	sec.Do(Derive(func(a *Argument) {
		h1 := a.Hyp(allR1.Core())
		// No ε in sight and nothing to denote — both shaping passes
		// no-op, and the close still lands from the premise.
		a.Show("merged shaping no-ops are harmless", By(PreNormalized, HilbertDenoted, h1))
	}))
	require.True(t, sec.Proved())

	requirePanicContains(t, "two Denoted sizes", func() {
		sec2 := e.ctx.Section(MakeProp(e.R1.Apply(e.c), allR1))
		sec2.Do(Derive(func(a *Argument) {
			h1 := a.Hyp(allR1.Core())
			a.Show("conflict", By(Denoted(4), Denoted(8), h1))
		}))
	})
}

// =======================================================================
// Fact as a spine step — a.Do(f.At(w…))
// =======================================================================

// TestFactAt_RunsAsSpineStep: grounding a resident ∀-fact ON THE SPINE
// (for a downstream step consumer): the instance joins the ambient
// hyps and the ∀-source is KEPT — spine facts stay re-groundable.
func TestFactAt_RunsAsSpineStep(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	allR1 := ForAll(x)(e.R1.Apply(x))
	inst := e.R1.Apply(e.c)

	sec := e.ctx.Section(MakeProp(inst, allR1))
	sec.Do(Derive(func(a *Argument) {
		src := a.Hyp(allR1.Core())
		a.Do(src.At(e.c)) // ground R1(c) on the spine

		g := a.Goal()
		require.Equal(t, 2, g.NumHyps(),
			"the instance joins the hyps and the ∀-source is kept")
		found := false
		for i := 0; i < g.NumHyps(); i++ {
			if g.Hyp(i).AlphaEquals(inst.Core()) {
				found = true
			}
		}
		require.True(t, found, "the ground instance is resident on the spine")

		a.Show("the instance is the goal", By(a.Hyp(inst.Core())))
	}))
	require.True(t, sec.Proved())
}

// TestFactAt_RegroundsAtOtherWitnesses: because the source survives its
// grounding, the same fact grounds again at a different witness later.
func TestFactAt_RegroundsAtOtherWitnesses(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	d := Var("d", TypeInd)
	allR1 := ForAll(x)(e.R1.Apply(x))

	sec := e.ctx.Section(MakeProp(e.R1.Apply(e.c).And(e.R1.Apply(d)), allR1))
	sec.Do(Derive(func(a *Argument) {
		src := a.Hyp(allR1.Core())
		a.Do(src.At(e.c))
		a.Do(src.At(d))
		a.Show("both instances resident", By(Normalized, Broadcast,
			a.Hyp(e.R1.Apply(e.c).Core()), a.Hyp(e.R1.Apply(d).Core())))
	}))
	require.True(t, sec.Proved())
}

// TestFactAt_StepGuards: the narrow contract — a named fact as a step
// points at Cite, a bare resident fact is not a step.
func TestFactAt_StepGuards(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	allR1 := ForAll(x)(e.R1.Apply(x))

	sec := e.ctx.Section(MakeProp(e.R1.Apply(e.c), allR1))
	requirePanicContains(t, "Cite", func() {
		sec.Do(NamedFact(depName("some.Dep")).At(e.c))
	})
	requirePanicContains(t, "not a step", func() {
		sec.Do(Derive(func(a *Argument) {
			src := a.Hyp(allR1.Core())
			a.Do(src) // bare resident fact as a step
		}))
	})
}

// =======================================================================
// Unpack on a NAMED fact
// =======================================================================

// TestUnpack_NamedTheorem: ∃-elimination straight off an established
// theorem — install + Skolemize + return the instance as a Fact, the
// spelling that replaces an anonymous Cite(X) + StripQuant() pair.
//
// The goal needs a SECOND named fact (allS, cited only in the final
// By) so the install of the ∃-theorem cannot close the goal by itself
// — mirroring the real sites, where the correspondence lemma's install
// is one premise of several.
func TestUnpack_NamedTheorem(t *testing.T) {
	e := makeSpineTestEnv()
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	existsR := core.TestThm(Exists(x)(e.R1.Apply(x)))
	allS := core.TestThm(ForAll(x)(e.S.Apply(x, x)))
	imp := ForAll(x)(e.R1.Apply(x).Imply(ForAll(y)(e.S.Apply(x, y).Imply(e.Qb))))

	sec := e.ctx.Section(MakeProp(e.Qb, imp))
	sec.Do(Derive(func(a *Argument) {
		w, inst := a.Unpack(existsR)
		impF := a.Hyp(imp.Core())
		a.Show("Qb from the witness and its S-fact", By(impF, inst, At(MakeFact(allS), w)))
	}))
	require.True(t, sec.Proved(),
		"Unpack of a named ∃-theorem did not yield a usable instance")
}

// TestUnpack_NamedTheoremAtWitnesses: the At-form — a ∀-theorem's
// ∃-instance at witnesses, installed ground and then Skolemized. As
// above, the goal needs a second named fact so the instance's install
// cannot close it alone.
func TestUnpack_NamedTheoremAtWitnesses(t *testing.T) {
	e := makeSpineTestEnv()
	x, k := Var("x", TypeInd), Var("k", TypeInd)
	forallExists := core.TestThm(ForAll(k)(Exists(x)(e.S.Apply(k, x))))
	allR1 := core.TestThm(ForAll(x)(e.R1.Apply(x)))
	imp := ForAll(x)(e.S.Apply(e.c, x).Imply(e.R1.Apply(x).Imply(e.Qb)))

	sec := e.ctx.Section(MakeProp(e.Qb, imp))
	sec.Do(Derive(func(a *Argument) {
		_, inst := a.Unpack(At(MakeFact(forallExists), e.c))
		impF := a.Hyp(imp.Core())
		// allR1 goes in BARE: its ∀-form install discharges the R1
		// obligation; bare, the apply rung pins its instance from the
		// context (the tuple form is the test below).
		a.Show("Qb from the instance witness", By(impF, inst, allR1))
	}))
	require.True(t, sec.Proved())
}

// TestBy_WitnessTupleIsApplied: a premise's install never closes the goal —
// By installs the fact the author named by plain add (no stage reclassifies
// a premise), so a witness tuple is always APPLIED, never absorbed at a
// ∀-form install. A tuple the install never applied would be unchecked
// text, a wrong tuple replaying green; that is excluded by construction: the
// right tuple grounds the instance the argument needs and the leaf closes on
// it; a WRONG tuple grounds an instance the argument cannot use, and the
// close fails by mathematics, not by a spelling rule.
func TestBy_WitnessTupleIsApplied(t *testing.T) {
	build := func(wrong bool) *GoalStackNode {
		e := makeSpineTestEnv()
		x, k := Var("x", TypeInd), Var("k", TypeInd)
		forallExists := core.TestThm(ForAll(k)(Exists(x)(e.S.Apply(k, x))))
		allR1 := core.TestThm(ForAll(x)(e.R1.Apply(x)))
		imp := ForAll(x)(e.S.Apply(e.c, x).Imply(e.R1.Apply(x).Imply(e.Qb)))
		sec := e.ctx.Section(MakeProp(e.Qb, imp))
		sec.Do(Derive(func(a *Argument) {
			w, inst := a.Unpack(At(MakeFact(forallExists), e.c))
			impF := a.Hyp(imp.Core())
			at := At(MakeFact(allR1), w)
			if wrong {
				at = At(MakeFact(allR1), e.c) // R1 at the wrong point: nothing the argument can use
			}
			a.Show("Qb from the instance witness", By(impF, inst, at))
		}))
		return sec
	}
	require.True(t, build(false).Proved(), "the right tuple grounds R1 at the witness and the leaf closes")
	require.Panics(t, func() { build(true) }, "a wrong tuple grounds an unusable instance and the close fails")
}

// TestUnpack2_NamedTheorem: the two-witness form on a named ∃∃-fact.
func TestUnpack2_NamedTheorem(t *testing.T) {
	e := makeSpineTestEnv()
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	existsS := core.TestThm(Exists(x)(Exists(y)(e.S.Apply(x, y))))
	allR1 := core.TestThm(ForAll(x)(e.R1.Apply(x)))
	imp := ForAll(x)(ForAll(y)(e.S.Apply(x, y).Imply(e.R1.Apply(x).Imply(e.Qb))))

	sec := e.ctx.Section(MakeProp(e.Qb, imp))
	sec.Do(Derive(func(a *Argument) {
		wx, wy, inst := a.Unpack2(existsS)
		_, _ = wx, wy // both witnesses minted and registered; the close needs only the facts
		impF := a.Hyp(imp.Core())
		// allR1 bare — the apply rung pins its instance from the
		// context (see TestBy_WitnessTupleIsApplied for the tuple form).
		a.Show("Qb from the witness pair", By(impF, inst, allR1))
	}))
	require.True(t, sec.Proved())
}

// _SpineInd is the phantom of the spine fixtures' atomic type `ind`,
// for the typed verbs.
type _SpineInd struct{}

func (_SpineInd) Reify() HolType { return TypeInd }

// TestUnpack3_NamedTheorem: the three-witness form on a named ∃∃∃-fact,
// its names binding the witnesses in the fact's binder order.
func TestUnpack3_NamedTheorem(t *testing.T) {
	e := makeSpineTestEnv()
	x, y, z := Var("x", TypeInd), Var("y", TypeInd), Var("z", TypeInd)
	existsT := core.TestThm(Exists(x)(Exists(y)(Exists(z)(e.T.Apply(x, y, z)))))
	allR1 := core.TestThm(ForAll(x)(e.R1.Apply(x)))
	imp := ForAll(x)(ForAll(y)(ForAll(z)(e.T.Apply(x, y, z).Imply(e.R1.Apply(z).Imply(e.Qb)))))

	sec := e.ctx.Section(MakeProp(e.Qb, imp))
	sec.Do(Derive(func(a *Argument) {
		u, v, w, inst := a.Unpack3As[_SpineInd, _SpineInd, _SpineInd](existsT, "u", "v", "w")
		require.True(t, a.Term("u").Core().Equals(u.Core()), "the first name must resolve to the first witness")
		require.True(t, a.Term("w").Core().Equals(w.Core()), "the third name must resolve to the third witness")
		require.False(t, v.Core().Equals(w.Core()), "the witnesses are distinct mints")
		a.Show("Qb from the witness triple", By(a.Hyp(imp.Core()), inst, allR1))
	}))
	require.True(t, sec.Proved())
}

// TestObtain3_ProvesThenOpens: Obtain3 proves its ∃∃∃-claim and opens it
// in one step, Named spelling the three witnesses.
func TestObtain3_ProvesThenOpens(t *testing.T) {
	e := makeSpineTestEnv()
	x, y, z := Var("x", TypeInd), Var("y", TypeInd), Var("z", TypeInd)
	claim := Exists(x)(Exists(y)(Exists(z)(e.T.Apply(x, y, z))))
	existsT := core.TestThm(claim)
	imp := ForAll(x)(ForAll(y)(ForAll(z)(e.T.Apply(x, y, z).Imply(e.Qb))))

	sec := e.ctx.Section(MakeProp(e.Qb, imp))
	sec.Do(Derive(func(a *Argument) {
		_, _, w, inst := a.Obtain3As[_SpineInd, _SpineInd, _SpineInd]("a triple is related",
			MakeProp(claim), By(existsT), Named("u", "v", "w"))
		require.True(t, a.Term("w").Core().Equals(w.Core()), "Named must spell the third witness")
		a.Show("Qb from the obtained triple", By(a.Hyp(imp.Core()), inst))
	}))
	require.True(t, sec.Proved())
}

// TestUnpack_ArityIsTheWholePrefix: one Skolemization opens the fact's
// whole ∃-prefix, so a verb of fewer witnesses than the prefix holds is
// refused, not left with a residual ∃.
func TestUnpack_ArityIsTheWholePrefix(t *testing.T) {
	e := makeSpineTestEnv()
	x, y, z := Var("x", TypeInd), Var("y", TypeInd), Var("z", TypeInd)
	exT := Exists(x)(Exists(y)(Exists(z)(e.T.Apply(x, y, z))))
	sec := e.ctx.Section(MakeProp(e.Qb, exT))
	requirePanicContains(t, "expected 2 minted witness(es), found 3", func() {
		sec.Do(Derive(func(a *Argument) { a.Unpack2(a.Hyp(exT.Core())) }))
	})
}

// TestUnpack_BinderTheBodyDoesNotMention: a binder its body does not
// mention fixes no variable of the instance, so the verb has no witness
// to return for it and says so.
func TestUnpack_BinderTheBodyDoesNotMention(t *testing.T) {
	e := makeSpineTestEnv()
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	exR := Exists(x)(Exists(y)(e.R1.Apply(x)))
	sec := e.ctx.Section(MakeProp(e.Qb, exR))
	requirePanicContains(t, "the fact binds 2 witness(es) and its body mentions 1 of them", func() {
		sec.Do(Derive(func(a *Argument) { a.Unpack2(a.Hyp(exR.Core())) }))
	})
}

// TestUnpack_WitnessIsItsBindersByPosition: the strip says which variable
// it fixes for which binder, so a witness is read off its binder's place
// in the prefix and not off its name. The goal holds a t_1 of its own,
// and the strip renames the binder t_1 apart from it to a name that
// does not begin with the binder's; the witnesses come back in the
// binders' order all the same.
func TestUnpack_WitnessIsItsBindersByPosition(t *testing.T) {
	e := makeSpineTestEnv()
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	t1, u := Var("t_1", TypeInd), Var("u", TypeInd)
	exS := Exists(t1)(Exists(u)(e.S.Apply(t1, u)))
	imp := ForAll(x)(ForAll(y)(e.S.Apply(x, y).Imply(e.Qb)))

	sec := e.ctx.Section(MakeProp(e.Qb, exS, imp, e.R1.Apply(t1)))
	sec.Do(Derive(func(a *Argument) {
		first, second, inst := a.Unpack2(a.Hyp(exS.Core()))
		require.False(t, first.Core().Equals(t1.Core()), "the binder is renamed apart from the goal's t_1")
		instance := a.cur.Goal.Hyp(inst.handle.resolveOrPanic("test", a.cur))
		require.True(t, instance.Equals(e.S.Apply(first, second).Core()),
			"the instance is S at the witnesses in the binders' order: %s", ext.PrintTerm(instance))
		a.Show("Qb from the witness pair", By(a.Hyp(imp.Core()), inst))
	}))
	require.True(t, sec.Proved())
}

// TestUnpack_ResidentFactUnchanged: the original resident flavor keeps
// its behavior — a sequent ∃-premise named by a.Hyp unpacks in place.
func TestUnpack_ResidentFactUnchanged(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	exHyp := Exists(x)(e.R1.Apply(x))
	imp := ForAll(x)(e.R1.Apply(x).Imply(e.Qb))

	sec := e.ctx.Section(MakeProp(e.Qb, exHyp, imp))
	sec.Do(Derive(func(a *Argument) {
		ex := a.Hyp(exHyp.Core())
		w, inst := a.Unpack(ex)
		impF := a.Hyp(imp.Core())
		a.Show("Qb from the premise's witness", By(impF.At(w), inst))
	}))
	require.True(t, sec.Proved())
}

// TestUnpack_NamedWitnesses: two resident facts sharing one ∃-binder
// (`∃c. R1(c)`, `∃c. R2(c)` — two memberships read off one definition
// say exactly this) are opened under names of the author's choosing,
// and the claim texts spell both witnesses by those names. Unnamed, the
// second witness would be spellable only by its mint.
//
//	∃c. R1(c), ∃c. R2(c), ∀x y. R1(x) ∧ R2(y) ⇒ S(x, y) ⊢ ∃x y. S(x, y)
func TestUnpack_NamedWitnesses(t *testing.T) {
	e := makeSpineTestEnv()
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	exR1 := Exists(e.c)(e.R1.Apply(e.c))
	exR2 := Exists(e.c)(e.R2.Apply(e.c))
	joins := ForAll(x)(ForAll(y)(e.R1.Apply(x).And(e.R2.Apply(y)).Imply(e.S.Apply(x).Apply(y))))

	sec := e.ctx.Section(MakeProp(Exists(x)(Exists(y)(e.S.Apply(x).Apply(y))), exR1, exR2, joins))
	sec.Do(Derive(func(a *Argument) {
		u, first := a.Unpack(a.Hyp(exR1.Core()), "u")
		v, second := a.Unpack(a.Hyp(exR2.Core()), "v")
		require.True(t, a.Term("u").Core().Equals(u.Core()), "the chosen name must resolve to the first witness")
		require.True(t, a.Term("v").Core().Equals(v.Core()), "the chosen name must resolve to the second witness")
		require.False(t, u.Core().Equals(v.Core()), "the two witnesses are distinct mints")
		related := a.Have("the two witnesses are related", "spineS(u, v)", By(a.Hyp(joins.Core()), first, second))
		a.Take(u)
		a.Take(v)
		a.Show("so some pair is", By(related))
	}))
	require.True(t, sec.Proved())
}

// spineWitnesses is the fixture of the four- and five-witness verbs:
// five variables over ind, `T(x, y, z) ∧ S(u, v)` over all five and
// `T(x, y, z) ∧ R1(u)` over the first four, each ∃-closed in that order
// (five, four) and ∀-closed into an implication of Qb (fiveQ, fourQ).
func spineWitnesses(e *spineTestEnv) (five, four, fiveQ, fourQ *ext.TermWrapper) {
	x, y, z := Var("x", TypeInd), Var("y", TypeInd), Var("z", TypeInd)
	u, v := Var("u", TypeInd), Var("v", TypeInd)
	body5 := e.T.Apply(x, y, z).And(e.S.Apply(u, v))
	body4 := e.T.Apply(x, y, z).And(e.R1.Apply(u))
	five = Exists(x)(Exists(y)(Exists(z)(Exists(u)(Exists(v)(body5)))))
	four = Exists(x)(Exists(y)(Exists(z)(Exists(u)(body4))))
	fiveQ = ForAll(x)(ForAll(y)(ForAll(z)(ForAll(u)(ForAll(v)(body5.Imply(e.Qb))))))
	fourQ = ForAll(x)(ForAll(y)(ForAll(z)(ForAll(u)(body4.Imply(e.Qb)))))
	return five, four, fiveQ, fourQ
}

// TestUnpack4And5_NamedTheorem: the four- and five-witness forms on a
// named fact, their names binding the witnesses in the fact's binder
// order.
func TestUnpack4And5_NamedTheorem(t *testing.T) {
	t.Run("four", func(t *testing.T) {
		e := makeSpineTestEnv()
		_, four, _, fourQ := spineWitnesses(e)
		sec := e.ctx.Section(MakeProp(e.Qb, fourQ))
		sec.Do(Derive(func(a *Argument) {
			p, _, _, s, inst := a.Unpack4As[_SpineInd, _SpineInd, _SpineInd, _SpineInd](
				core.TestThm(four), "p", "q", "r", "s")
			require.True(t, a.Term("p").Core().Equals(p.Core()), "the first name must resolve to the first witness")
			require.True(t, a.Term("s").Core().Equals(s.Core()), "the fourth name must resolve to the fourth witness")
			a.Show("Qb from the four witnesses", By(a.Hyp(fourQ.Core()), inst))
		}))
		require.True(t, sec.Proved())
	})
	t.Run("five", func(t *testing.T) {
		e := makeSpineTestEnv()
		five, _, fiveQ, _ := spineWitnesses(e)
		sec := e.ctx.Section(MakeProp(e.Qb, fiveQ))
		sec.Do(Derive(func(a *Argument) {
			p, _, _, s, w, inst := a.Unpack5As[_SpineInd, _SpineInd, _SpineInd, _SpineInd, _SpineInd](
				core.TestThm(five), "p", "q", "r", "s", "w")
			require.True(t, a.Term("p").Core().Equals(p.Core()), "the first name must resolve to the first witness")
			require.True(t, a.Term("w").Core().Equals(w.Core()), "the fifth name must resolve to the fifth witness")
			require.False(t, s.Core().Equals(w.Core()), "the witnesses are distinct mints")
			a.Show("Qb from the five witnesses", By(a.Hyp(fiveQ.Core()), inst))
		}))
		require.True(t, sec.Proved())
	})
}

// TestObtain4And5_ProveThenOpen: Obtain4 and Obtain5 prove their claim
// and open it in one step, Named spelling the witnesses.
func TestObtain4And5_ProveThenOpen(t *testing.T) {
	t.Run("four", func(t *testing.T) {
		e := makeSpineTestEnv()
		_, four, _, fourQ := spineWitnesses(e)
		sec := e.ctx.Section(MakeProp(e.Qb, fourQ))
		sec.Do(Derive(func(a *Argument) {
			_, _, _, s, inst := a.Obtain4As[_SpineInd, _SpineInd, _SpineInd, _SpineInd]("four points are related",
				MakeProp(four), By(core.TestThm(four)), Named("p", "q", "r", "s"))
			require.True(t, a.Term("s").Core().Equals(s.Core()), "Named must spell the fourth witness")
			a.Show("Qb from the obtained four", By(a.Hyp(fourQ.Core()), inst))
		}))
		require.True(t, sec.Proved())
	})
	t.Run("five", func(t *testing.T) {
		e := makeSpineTestEnv()
		five, _, fiveQ, _ := spineWitnesses(e)
		sec := e.ctx.Section(MakeProp(e.Qb, fiveQ))
		sec.Do(Derive(func(a *Argument) {
			_, _, _, _, w, inst := a.Obtain5As[_SpineInd, _SpineInd, _SpineInd, _SpineInd, _SpineInd](
				"five points are related", MakeProp(five), By(core.TestThm(five)), Named("p", "q", "r", "s", "w"))
			require.True(t, a.Term("w").Core().Equals(w.Core()), "Named must spell the fifth witness")
			a.Show("Qb from the obtained five", By(a.Hyp(fiveQ.Core()), inst))
		}))
		require.True(t, sec.Proved())
	})
}

// TestUnpackAndObtain_ALongerPrefixNamesItsVerb: a leading ∃-prefix
// opens whole, so a verb of a shorter arity is refused, and the refusal
// names the verb of the prefix's length; past five there is none, and
// the refusal says to nest.
func TestUnpackAndObtain_ALongerPrefixNamesItsVerb(t *testing.T) {
	e := makeSpineTestEnv()
	five, _, _, _ := spineWitnesses(e)
	x, y, z := Var("x", TypeInd), Var("y", TypeInd), Var("z", TypeInd)
	u, v, w := Var("u", TypeInd), Var("v", TypeInd), Var("w", TypeInd)
	six := Exists(x)(Exists(y)(Exists(z)(Exists(u)(Exists(v)(Exists(w)(
		e.T.Apply(x, y, z).And(e.T.Apply(u, v, w))))))))
	for _, tc := range []struct {
		name, want string
		open       func(a *Argument)
	}{
		{"Unpack3 of five", "Unpack5 opens this one", func(a *Argument) { a.Unpack3(a.Hyp(five.Core())) }},
		{"Unpack of five", "Unpack5 opens this one", func(a *Argument) { a.Unpack(a.Hyp(five.Core())) }},
		{"Unpack5 of six", "no Unpack verb opens more than 5 witnesses", func(a *Argument) { a.Unpack5(a.Hyp(six.Core())) }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			sec := e.ctx.Section(MakeProp(e.Qb, five, six))
			requirePanicContains(t, tc.want, func() { sec.Do(Derive(tc.open)) })
		})
	}
	t.Run("Obtain2 of five", func(t *testing.T) {
		sec := e.ctx.Section(MakeProp(e.Qb))
		requirePanicContains(t, "Obtain5 opens this one", func() {
			sec.Do(Derive(func(a *Argument) {
				a.Obtain2("five points are related", MakeProp(five), By(core.TestThm(five)))
			}))
		})
	})
}

// TestUnpack_NamedWitnessIsStrict: a chosen name is strict, as
// Fix("u") is — a name that already means something is loud, and so
// are a partial name list, a repeated name and an empty one.
func TestUnpack_NamedWitnessIsStrict(t *testing.T) {
	e := makeSpineTestEnv()
	exR1 := Exists(e.c)(e.R1.Apply(e.c))
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	exS := Exists(x)(Exists(y)(e.S.Apply(x).Apply(y)))
	z := Var("z", TypeInd)
	exT := Exists(x)(Exists(y)(Exists(z)(e.T.Apply(x, y, z))))
	for _, tc := range []struct {
		name, want string
		open       func(a *Argument)
	}{
		{"taken", "already", func(a *Argument) { a.Unpack(a.Hyp(exR1.Core()), "spineR1") }},
		{"empty", "non-empty", func(a *Argument) { a.Unpack(a.Hyp(exR1.Core()), "") }},
		{"partial", "name every witness or none", func(a *Argument) { a.Unpack2(a.Hyp(exS.Core()), "u") }},
		{"repeated", "given twice", func(a *Argument) { a.Unpack2(a.Hyp(exS.Core()), "u", "u") }},
		{"partial of three", "name every witness or none", func(a *Argument) { a.Unpack3(a.Hyp(exT.Core()), "u", "v") }},
	} {
		t.Run(tc.name, func(t *testing.T) {
			sec := e.ctx.Section(MakeProp(e.Qb, exR1, exS, exT))
			requirePanicContains(t, tc.want, func() { sec.Do(Derive(tc.open)) })
		})
	}
}

// TestObtain_ResidentClaimSaysUnpack: Obtain PROVES its claim, so a
// claim α-equal to a resident hypothesis — renaming its binder does not
// change that — is refused by the assert, and the refusal names the
// verb that opens a resident ∃-fact.
func TestObtain_ResidentClaimSaysUnpack(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	exR1 := Exists(e.c)(e.R1.Apply(e.c))
	sec := e.ctx.Section(MakeProp(e.Qb, exR1))
	requirePanicContains(t, "Unpack", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Obtain("the witness, renamed", MakeProp(Exists(x)(e.R1.Apply(x))), By(a.Hyp(exR1.Core())))
		}))
	})
}

// TestUnpack_NamedNonExistentialIsLoud: a named fact with no leading ∃
// is rejected with the binder count, not silently installed. (The goal
// is an unrelated atom — a goal the fact itself closes dies earlier,
// on the "closed the goal outright" guard.)
func TestUnpack_NamedNonExistentialIsLoud(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	allR1 := core.TestThm(ForAll(x)(e.R1.Apply(x)))

	sec := e.ctx.Section(MakeProp(e.Qb))
	requirePanicContains(t, "leading ∃", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Unpack(allR1)
		}))
	})
}

// =======================================================================
// ObtainChosen — ∃-elimination by Hilbert choice
// =======================================================================

// TestObtainChosen_RealizesTheChoice: from an established ∃x.R1(x),
// the verb computes and proves R1(εx.R1(x)) — the CHOSEN fact — and
// the returned ε-term feeds a later ground premise. The consumer
// implication speaks about the ε-term itself (∀y. R1(y) ⇒ S(y,y) at
// the choice point), mirroring the real sites where sibling statements
// spell the ε.
func TestObtainChosen_RealizesTheChoice(t *testing.T) {
	e := makeSpineTestEnv()
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	existsR := core.TestThm(Exists(x)(e.R1.Apply(x)))
	imp := ForAll(y)(e.R1.Apply(y).Imply(e.Qb))

	sec := e.ctx.Section(MakeProp(e.Qb, imp))
	sec.Do(Derive(func(a *Argument) {
		eps, chosen := a.ObtainChosen("the choice set is inhabited",
			MakeProp(Exists(x)(e.R1.Apply(x))), existsR)
		// The chosen fact is literally R1(εx.R1(x)) — computed, not spelled.
		require.True(t, eps.Core().AlphaEquals(
			x.SuchThat(e.R1.Apply(x)).Core()),
			"returned term is the canonical ε-term")
		impF := a.Hyp(imp.Core())
		a.Show("Qb from the chosen point", By(chosen, impF.At(eps)))
	}))
	require.True(t, sec.Proved(),
		"ObtainChosen did not realize the choice as a usable fact")
}

// TestObtainChosen_Guards: no leading ∃ and an empty premise list are
// authoring errors, loud and named.
func TestObtainChosen_Guards(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	existsR := core.TestThm(Exists(x)(e.R1.Apply(x)))

	sec := e.ctx.Section(MakeProp(e.Qb))
	requirePanicContains(t, "no leading ∃", func() {
		sec.Do(Derive(func(a *Argument) {
			a.ObtainChosen("not an exists", MakeProp(e.Qb.Core()), existsR)
		}))
	})
	requirePanicContains(t, "premises required", func() {
		sec.Do(Derive(func(a *Argument) {
			a.ObtainChosen("no premises", MakeProp(Exists(x)(e.R1.Apply(x))))
		}))
	})
}

// TestObtainChosen_AtItsOwnGoal: where the goal is the chosen fact
// itself the verb says so and names the close that works, and that
// close closes the goal.
func TestObtainChosen_AtItsOwnGoal(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	existsR := core.TestThm(Exists(x)(e.R1.Apply(x)))
	chosen := e.R1.Apply(x.SuchThat(e.R1.Apply(x)))

	sec := e.ctx.Section(MakeProp(chosen))
	requirePanicContains(t, "the goal is the chosen fact itself", func() {
		sec.Do(Derive(func(a *Argument) {
			a.ObtainChosen("the choice set is inhabited", MakeProp(Exists(x)(e.R1.Apply(x))), existsR)
		}))
	})

	sec = e.ctx.Section(MakeProp(chosen))
	sec.Do(Derive(func(a *Argument) {
		a.Show("the choice set is inhabited", By(HilbertDenoted, existsR))
	}))
	require.True(t, sec.Proved(), "the close the refusal names closes the goal")
}

// TestHave_ClaimIsTheGoal: a Have whose claim is the goal's conclusion
// is refused with the reason, and the Show the reason names closes the
// goal with the same proof.
func TestHave_ClaimIsTheGoal(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	allR1 := core.TestThm(ForAll(x)(e.R1.Apply(x)))
	goal := e.R1.Apply(Var("c", TypeInd))

	sec := e.ctx.Section(MakeProp(goal))
	requirePanicContains(t, "the claim is the goal's conclusion", func() {
		sec.Do(Derive(func(a *Argument) {
			a.Have("R1 at c", MakeProp(goal), By(allR1))
		}))
	})

	sec = e.ctx.Section(MakeProp(goal))
	sec.Do(Derive(func(a *Argument) {
		a.Show("R1 at c", By(allR1))
	}))
	require.True(t, sec.Proved())
}

// TestSplitConj_CaseCountNamesTheBinarySplit: SplitConj splits a
// conclusion in two however its conjuncts are nested, so one Case per
// conjunct is refused with the split it made and the verb that gives a
// subgoal per conjunct; that verb takes the four Cases.
func TestSplitConj_CaseCountNamesTheBinarySplit(t *testing.T) {
	e := makeSpineTestEnv()
	at := func(name core.TermName) *ext.TermWrapper { return e.R1.Apply(Var(name, TypeInd)) }
	nested := at("a").And(at("b")).And(at("c")).And(at("d"))
	require.Len(t, ext.DecomposesAND(nested.Core()), 4)
	hyps := []core.Term{at("a").Core(), at("b").Core(), at("c").Core(), at("d").Core()}
	four := func(is ...int) []Case {
		cases := make([]Case, len(is))
		for i := range is {
			cases[i] = MakeCase("conjunct "+strconv.Itoa(i), Basic())
		}
		return cases
	}

	for _, concl := range []*ext.TermWrapper{
		nested,
		at("a").And(at("b").And(at("c").And(at("d")))),
	} {
		sec := e.ctx.Section(prop.MakeProp(concl.Core(), hyps...))
		requirePanicContains(t, "SplitConjAll gives one subgoal per conjunct", func() {
			sec.Do(SplitConj(four(0, 1, 2, 3)...))
		})
		sec = e.ctx.Section(prop.MakeProp(concl.Core(), hyps...))
		requirePanicContains(t, "4 Case body(ies) provided but SplitConj produced 2 subgoal(s)", func() {
			sec.Do(SplitConj(four(0, 1, 2, 3)...))
		})

		sec = e.ctx.Section(prop.MakeProp(concl.Core(), hyps...))
		sec.Do(SplitConjAll(four(0, 1, 2, 3)...))
		require.True(t, sec.Proved(), "SplitConjAll takes one Case per conjunct")
	}
}

// =======================================================================
// Per-leaf {shape, close} under Broadcast + DenoteRefute
// =======================================================================

// TestBy_BroadcastPerLeafShaping: the denote/realize stage runs as each
// leaf's own preamble — on the fanned AC shape, adding Denoted to the
// broadcast close still lands (the later leaves' preambles no-op and
// recover; the close per leaf is unchanged). The regression this pins:
// per-leaf composition must not break the plain same-closer fan.
func TestBy_BroadcastPerLeafShaping(t *testing.T) {
	e, sec, h1t, h2t := broadcastFanSetup()
	sec.Do(Derive(func(a *Argument) {
		h1, h2 := a.Hyp(h1t), a.Hyp(h2t)
		a.Show("each conjunct closes after its own preamble",
			By(Normalized, Denoted(64), Broadcast, h1, h2, e.assoc, e.sym))
	}))
	require.True(t, sec.Proved(),
		"per-leaf shaping broke the broadcast fan close")
}

// TestDenoteRefute_TreeIdenticalSugar: DenoteRefute(n) is the literal
// Chain(Denote(n), Basic(), CnfRefute()) — same steps, same close. The
// goal's point term is nested past the size threshold so the Denote
// stage has genuine work (the raw litany stays strict — a site with
// nothing to denote panics exactly as the spelled-out triple would).
func TestDenoteRefute_TreeIdenticalSugar(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	f := Var("f", MakeFun(TypeInd, TypeInd))
	// The point term is nested past the threshold AND frequent (it
	// recurs between the premise and the conclusion) — Denote's two
	// conditions for introducing the atom.
	big := f.Apply(f.Apply(f.Apply(f.Apply(e.c))))
	impR2R1 := ForAll(x)(e.R2.Apply(x).Imply(e.R1.Apply(x)))

	sec := e.ctx.Section(MakeProp(e.R1.Apply(big), e.R2.Apply(big), impR2R1))
	sec.Do(DenoteRefute(3))
	require.True(t, sec.Proved(), "DenoteRefute did not close the leaf")
}

// =======================================================================
// Fact context verbs — branch splitting, and Clear
// =======================================================================

// splitSection builds the shape the branch-splitting tests share: goal
// Qb under a disjunction R1(c) ∨ R2(c) plus one implication per
// disjunct, so each split branch closes by refutation from its own hyps.
// The disjunction's TERM comes back too, for the a.Hyp / FromResident
// lookups the two spellings do.
func (e *spineTestEnv) splitSection() (*GoalStackNode, core.Term) {
	disj := e.R1.Apply(e.c).Or(e.R2.Apply(e.c))
	sec := e.ctx.Section(MakeProp(e.Qb, disj,
		e.R1.Apply(e.c).Imply(e.Qb), e.R2.Apply(e.c).Imply(e.Qb)))
	return sec, disj.Core()
}

func splitBranches() (DisjLeftHolds, DisjRightHolds) {
	return LeftHolds("R1(c) with its implication", CnfRefute()),
		RightHolds("R2(c) with its implication", CnfRefute())
}

// TestFactSplitDisj_ResidentIsHandleIdentical: on the RESIDENT flavor
// the split forwards straight onto the handle op — the claim that
// converting such a site cannot move a pb. Both spellings prove the same
// section, and their recorded ministep trees are equal.
func TestFactSplitDisj_ResidentIsHandleIdentical(t *testing.T) {
	build := func(asFact bool) *GoalStackNode {
		e := makeSpineTestEnv()
		sec, disj := e.splitSection()
		if asFact {
			sec.Do(Derive(func(a *Argument) {
				a.Do(a.Hyp(disj).SplitDisj(splitBranches()))
			}))
		} else {
			h := NewHypHandle("disj")
			sec.Do(Chain(h.FromResident(disj), h.SplitDisj(splitBranches())))
		}
		return sec
	}
	fact, handle := build(true), build(false)
	require.True(t, fact.Proved(), "the Fact spelling must prove")
	require.True(t, handle.Proved(), "the handle spelling must prove")
	require.Equal(t, describeTree(handle), describeTree(fact),
		"a resident Fact's SplitDisj must record exactly the handle op's ministeps")
}

// TestFactSplitDisj_NamedInstallsThenSplits: the NAMED flavor is NOT
// delegation — a description has no hyp index, so the fact is installed
// first (the Cite verb's path, at the given witnesses) and the arrival
// is split. The claim under test is that this records exactly what
// `h.From(Cite(dep, w…))` + `h.SplitDisj(…)` records, in that order.
func TestFactSplitDisj_NamedInstallsThenSplits(t *testing.T) {
	build := func(asFact bool) *GoalStackNode {
		e := makeSpineTestEnv()
		x := Var("x", TypeInd)
		disjThm := core.TestThm(ForAll(x)(e.R1.Apply(x).Or(e.R2.Apply(x))))
		sec := e.ctx.Section(MakeProp(e.Qb,
			e.R1.Apply(e.c).Imply(e.Qb), e.R2.Apply(e.c).Imply(e.Qb)))
		if asFact {
			sec.Do(At(MakeFact(disjThm), e.c).SplitDisj(splitBranches()))
		} else {
			h := NewHypHandle("disj")
			sec.Do(Chain(h.From(Cite(MakeFact(disjThm), e.c)), h.SplitDisj(splitBranches())))
		}
		return sec
	}
	fact, handle := build(true), build(false)
	require.True(t, fact.Proved(), "At(dep, w…).SplitDisj must install and split")
	require.True(t, handle.Proved(), "the handle spelling must prove")
	require.Equal(t, describeTree(handle), describeTree(fact),
		"install-then-split must record the same ministeps as From(Cite(…)) + SplitDisj")
}

// TestFactDismissLeft_SurvivorStaysNamed: the linearizing split, and the
// property that makes it usable as a value — the SAME Fact names the
// surviving disjunct afterwards (handle tracking follows the split), so
// the continuation cites it without re-binding.
func TestFactDismissLeft_SurvivorStaysNamed(t *testing.T) {
	e := makeSpineTestEnv()
	sec, disj := e.splitSection()
	sec.Do(Derive(func(a *Argument) {
		f := a.Hyp(disj)
		a.Do(f.DismissLeft("left: R1(c) closes from its own implication", CnfRefute()))
		a.Show("right: the surviving disjunct with its implication",
			By(f, a.Hyp(e.R2.Apply(e.c).Imply(e.Qb).Core())))
	}))
	require.True(t, sec.Proved(),
		"the Fact must still name the surviving disjunct after DismissLeft")
}

// TestFactSplitDisj_GroundInstanceGroundsThenSplits: a resident fact
// AT WITNESSES is grounded on the spine as a.Do(f.At(w…)) grounds it —
// the ∀-source kept — and the instance is split: the same ministeps as
// the two-statement spelling that grounds first and splits the instance
// by its content.
func TestFactSplitDisj_GroundInstanceGroundsThenSplits(t *testing.T) {
	build := func(inHand bool) *GoalStackNode {
		e := makeSpineTestEnv()
		x := Var("x", TypeInd)
		allDisj := ForAll(x)(e.R1.Apply(x).Or(e.R2.Apply(x)))
		sec := e.ctx.Section(MakeProp(e.Qb, allDisj,
			e.R1.Apply(e.c).Imply(e.Qb), e.R2.Apply(e.c).Imply(e.Qb)))
		sec.Do(Derive(func(a *Argument) {
			src := a.Hyp(allDisj.Core())
			if inHand {
				a.Do(src.At(e.c).SplitDisj(splitBranches()))
				return
			}
			a.Do(src.At(e.c))
			a.Do(a.Hyp(e.R1.Apply(e.c).Or(e.R2.Apply(e.c)).Core()).SplitDisj(splitBranches()))
		}))
		return sec
	}
	inHand, twoSteps := build(true), build(false)
	require.True(t, inHand.Proved(), "f.At(w…).SplitDisj must ground and split")
	require.True(t, twoSteps.Proved())
	require.Equal(t, describeTree(twoSteps), describeTree(inHand),
		"grounding then splitting must record what a.Do(f.At(w…)) and a split of the instance record")
}

// TestFactContextVerbs_Guards: the flavors Clear has no address for.
func TestFactContextVerbs_Guards(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	allDisj := ForAll(x)(e.R1.Apply(x).Or(e.R2.Apply(x)))

	// Clear refuses a NAMED fact: nothing was installed, so there is
	// nothing to drop (and installing one in order to drop it is not an
	// argument anyone means to make).
	requirePanicContains(t, "not resident", func() {
		sec := e.ctx.Section(MakeProp(e.Qb, allDisj))
		sec.Do(Clear("some.Dep"))
	})
	requirePanicContains(t, "no facts given", func() {
		sec := e.ctx.Section(MakeProp(e.Qb, allDisj))
		sec.Do(Clear())
	})
	requirePanicContains(t, "pending witnesses", func() {
		sec := e.ctx.Section(MakeProp(e.Qb, allDisj))
		sec.Do(Derive(func(a *Argument) {
			a.Do(Clear(a.Hyp(allDisj.Core()).At(e.c)))
		}))
	})
}

// TestClear_DropsFactNamedHyp: the positive path — a spent ∀-source
// named as a Fact is dropped from the context, and only it.
func TestClear_DropsFactNamedHyp(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	spent := ForAll(x)(e.R1.Apply(x))

	sec := e.ctx.Section(MakeProp(e.Qb, spent, e.Qb))
	sec.Do(Derive(func(a *Argument) {
		a.Do(Clear(a.Hyp(spent.Core())))
		require.Equal(t, 1, a.Goal().NumHyps(),
			"exactly the named ∀-source was dropped")
		a.Show("the goal is itself a premise", By(a.Hyp(e.Qb.Core())))
	}))
	require.True(t, sec.Proved())
}

// TestClear_FactAndHandleAreIdentical: Clear gained the Fact value; it
// did not change what it does. The handle spelling and the Fact
// spelling record the same single ClearHyps ministep, which is why
// converting a Clear site is pb-free.
func TestClear_FactAndHandleAreIdentical(t *testing.T) {
	build := func(asFact bool) *GoalStackNode {
		e := makeSpineTestEnv()
		x := Var("x", TypeInd)
		spent := ForAll(x)(e.R1.Apply(x))
		sec := e.ctx.Section(MakeProp(e.Qb, spent, e.Qb))
		if asFact {
			sec.Do(Derive(func(a *Argument) {
				a.Do(Clear(a.Hyp(spent.Core())), Assumption())
			}))
		} else {
			h := NewHypHandle("spent")
			sec.Do(Chain(h.FromResident(spent.Core()), Clear(h), Assumption()))
		}
		return sec
	}
	fact, handle := build(true), build(false)
	require.True(t, fact.Proved())
	require.True(t, handle.Proved(),
		"a *HypHandle must still pass to Clear unchanged")
	require.Equal(t, describeTree(handle), describeTree(fact),
		"Clear records one ClearHyps either way — converting a site is pb-free")
}

// TestCiteTarget_FactFlavors: the cite verbs' half of the pointing
// discipline. `Fact` is three things, and only one of them is a fact
// Cite can bring to bear; the other two are mistakes about the VERB,
// and each panic names the spelling that IS right.
//
// The RESIDENT case is the one that motivated this: an
// author holding a fact from `Given` reached for `Cite(f)` on the
// strength of a plan sentence that overloaded one letter across two
// type universes. Cite brings an OUTSIDE fact to bear; a resident fact
// is already in context, so its close is `By(f)`.
func TestCiteTarget_FactFlavors(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	allR1 := ForAll(x)(e.R1.Apply(x))

	// Resident flavor → points at By(f).
	sec := e.ctx.Section(MakeProp(e.R1.Apply(e.c), allR1))
	requirePanicContains(t, "By(f)", func() {
		sec.Do(Derive(func(a *Argument) {
			src := a.Hyp(allR1.Core())
			a.Do(Cite(src))
		}))
	})

	// A named fact already carrying its grounding → points at the
	// positional witness form.
	sec2 := e.ctx.Section(MakeProp(e.R1.Apply(e.c), allR1))
	requirePanicContains(t, "Cite(dep, w…)", func() {
		sec2.Do(Cite(At(depName("some.Dep"), e.c)))
	})

	// NAMED flavor unwraps: MakeFact(dep) and dep name the same fact, so
	// a cite of one must not depend on which spelling reached it. Both
	// resolve to the same Prop.
	thm := core.TestThm(allR1)
	require.Equal(t,
		resolveLemmaTarget("Cite", e.ctx, thm),
		resolveLemmaTarget("Cite", e.ctx, MakeFact(thm)))
}

// TestUnpack_ReadsTheFactNotTheGoal: Unpack records StripQuantAt at the
// hypothesis it resolved, so it eliminates the named ∃ (a) under a
// conclusion whose ∀-prefix is still standing and (b) when another
// ∃-hyp sits before it in the canonical hyp order — the two shapes the
// pick-first StripQuant refused ("also changed the CONCLUSION" /
// "another ∃-hyp was strippable").
func TestUnpack_ReadsTheFactNotTheGoal(t *testing.T) {
	e := makeSpineTestEnv()
	x, z := Var("x", TypeInd), Var("z", TypeInd)
	exR1 := Exists(x)(e.R1.Apply(x)).Core()
	exR2 := Exists(x)(e.R2.Apply(x)).Core()
	impR1 := ForAll(x)(e.R1.Apply(x).Imply(e.Qb)).Core()
	impR2 := ForAll(x)(e.R2.Apply(x).Imply(e.Qb)).Core()
	concl := ForAll(z)(e.S.Apply(z, z).Imply(e.Qb)).Core()

	sec := e.ctx.Section(MakeProp(concl, exR1, exR2, impR1, impR2))
	// The target is whichever ∃-hyp the canonical order puts SECOND, so
	// a pick-first strip would have opened the other one.
	iR1, iR2 := -1, -1
	for i := range sec.Goal.NumHyps() {
		switch h := sec.Goal.Hyp(i); {
		case h.AlphaEquals(exR1):
			iR1 = i
		case h.AlphaEquals(exR2):
			iR2 = i
		}
	}
	require.NotEqual(t, -1, iR1)
	require.NotEqual(t, -1, iR2)
	target, decoy, imp := exR2, exR1, impR2
	if iR1 > iR2 {
		target, decoy, imp = exR1, exR2, impR1
	}

	sec.Do(Derive(func(a *Argument) {
		_, inst := a.Unpack(a.Hyp(target))
		require.False(t, ext.MatchesFORALL(a.cur.Goal.Conclusion()).IsZero(), "Unpack must not strip the conclusion's ∀-prefix: %s", prop.PrintProp(a.cur.Goal))
		require.True(t, a.cur.Goal.AnyHyp(decoy.AlphaEquals),
			"Unpack must not open the other ∃-hyp: %s", prop.PrintProp(a.cur.Goal))
		require.False(t, a.cur.Goal.AnyHyp(target.AlphaEquals),
			"the named ∃-hyp is the one opened: %s", prop.PrintProp(a.cur.Goal))
		a.Show("Qb from the witness", By(a.Hyp(imp), inst))
	}))
	require.True(t, sec.Proved())
}

// TestObtain_OpensItsOwnClaim: Obtain proves an ∃-claim and opens THAT
// hypothesis, whatever else is resident — an ∃-fact stated earlier for a
// later use stays closed, wherever the canonical hyp order puts it, and
// is unpacked when its turn comes. The shape of
// real_sequences.IncreasingBoundedConvergesToSup: the range's bound
// `∃b. …` resident, the approach witness obtained after it.
func TestObtain_OpensItsOwnClaim(t *testing.T) {
	e := makeSpineTestEnv()
	x := Var("x", TypeInd)
	exR1 := Exists(x)(e.R1.Apply(x)).Core()
	exR2 := Exists(x)(e.R2.Apply(x)).Core()
	r1c, r2c := e.R1.Apply(e.c).Core(), e.R2.Apply(e.c).Core()
	impBoth := ForAll(x)(e.R1.Apply(x).Imply(ForAll(x)(e.R2.Apply(x).Imply(e.Qb)))).Core()

	// Each of the two ∃-facts takes the resident role once, so one of
	// the two runs has the resident sort before the claim.
	for _, run := range []struct {
		name            string
		resident, claim core.Term
		ground          core.Term
	}{
		{"R1 resident, R2 obtained", exR1, exR2, r2c},
		{"R2 resident, R1 obtained", exR2, exR1, r1c},
	} {
		sec := e.ctx.Section(MakeProp(e.Qb, run.resident, run.ground, impBoth))
		sec.Do(Derive(func(a *Argument) {
			_, mine := a.Obtain("the point c witnesses it", MakeProp(run.claim), By(a.Hyp(run.ground)))
			require.True(t, a.cur.Goal.AnyHyp(run.resident.AlphaEquals),
				"%s: Obtain must leave the resident ∃-fact closed: %s", run.name, prop.PrintProp(a.cur.Goal))
			require.False(t, a.cur.Goal.AnyHyp(run.claim.AlphaEquals),
				"%s: the claim's own ∃ is the one opened: %s", run.name, prop.PrintProp(a.cur.Goal))
			_, theirs := a.Unpack(a.Hyp(run.resident))
			a.Show("Qb from the two witnesses", By(a.Hyp(impBoth), mine, theirs))
		}))
		require.True(t, sec.Proved(), run.name)
	}
}
