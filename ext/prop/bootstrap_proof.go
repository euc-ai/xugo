/**
 * File: bootstrap_proof.go
 *
 * This file contains the proofs for the theorems in the bootstrap.go file
 */

package prop

import (
	"context"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// ⊢ ⊤
func derivesTrueProof() *PropWrapper {
	p := initVars.p
	return ExpandDef(T).
		EqSym().
		EqMP(Refl(p.To(p)))
}

// ⊥ ⊢ p
func falseDerivesProof() func(Term) *PropWrapper {
	p := initVars.p
	return ExpandDef(F).
		LeftAssume().
		RightApply(p).
		RewriteConcl(DeepBeta).
		EqSym().
		EqMP(DerivesTrue).
		instVar(p.AssertVar())
}

// ¬⊤ ⇔ ⊥
func notTrueProof() *PropWrapper {
	return Assume(Eq(T, F)).
		EqMP(DerivesTrue).
		Deduct(FalseDerives(Eq(T, F))).
		EqTrans(EqualsFalse(T)).
		EqSym()
}

// ¬⊥ ⇔ ⊤
func notFalseProof() *PropWrapper {
	return EqualsFalse(F).
		EqMP(Refl(F)).
		Deduct(DerivesTrue)
}

// ¬p, p ⊢ ⊥
func contradictProof() func(Term) *PropWrapper {
	p := initVars.p
	return EqualsFalse(p).
		RightAssume().
		LeftAssume().
		instVar(p.AssertVar())
}

// ⊢ (p = ⊥) = ¬p
func equalsFalseProof() func(Term) *PropWrapper {
	p := initVars.p
	return ExpandDef(NOT, p).
		EqSym().
		instVar(p.AssertVar())
}

// ⊢ (p ⇒ ⊥) = ¬p
func impliesFalseProof() func(Term) *PropWrapper {
	p := initVars.p
	return Contradict(p).
		PromoteHyp(p).
		Deduct(EqualsFalse(p).EqMP(FalseDerives(p).Deduct(ModusPonens(p, F)))).
		instVar(p.AssertVar())
}

// p ∧ q ⊢ p, p ∧ q ⊢ q
func hypANDProof() (
	func(Term, Term) *PropWrapper,
	func(Term, Term) *PropWrapper) {
	p, q := initVars.p, initVars.q

	// p ∧ q ⊢ λh.h(⊤, ⊤) = λh.h(p, q)
	w := ExpandDef(AND, p, q).
		LeftAssume().
		EqSym()

	// p ∧ q ⊢ p
	u := w.
		RightApply(p.To(q.To(p))).
		RewriteConcl(DeepBeta).
		EqMP(DerivesTrue).
		inst2Vars(p.AssertVar(), q.AssertVar())
	// p ∧ q ⊢ q
	v := w.
		RightApply(p.To(q.To(q))).
		RewriteConcl(DeepBeta).
		EqMP(DerivesTrue).
		inst2Vars(p.AssertVar(), q.AssertVar())
	return u, v
}

// p0 ∧ p1 ∧ ... ∧ pn ⊢ pi
func hypANDRecursiveProof(ps ...Term) []*PropWrapper {
	Assert(len(ps) > 0)

	if len(ps) == 1 {
		return []*PropWrapper{Assume(ps[0])}
	}

	h := And(utils.BeforeLast(ps)...)
	t, tLast := HypAND0(h, utils.Last(ps)), HypAND1(h, utils.Last(ps))

	var thms []*PropWrapper
	for _, thm := range hypANDRecursiveProof(utils.BeforeLast(ps)...) {
		thms = append(thms, t.DeriveTrans(thm))
	}
	thms = append(thms, tLast)
	return thms
}

// p, q ⊢ p ∧ q
func conclANDProof() func(Term, Term) *PropWrapper {
	p, q, h := initVars.p, initVars.q, initVars.h
	return Refl(h).
		Apply(Assume(p).Deduct(DerivesTrue)).
		Apply(Assume(q).Deduct(DerivesTrue)).
		Abs(h).
		DeriveTrans(ExpandDef(AND, p, q).RightAssume()).
		inst2Vars(p.AssertVar(), q.AssertVar())
}

// p0, p1, ..., pn ⊢ p0 ∧ p1 ∧ ... ∧ pn
func conclANDRecursiveProof(ps ...Term) *PropWrapper {
	Assert(len(ps) > 0)

	if len(ps) == 1 {
		return Assume(ps[0])
	}
	return ConclAND(And(utils.BeforeLast(ps)...), utils.Last(ps)).
		DeriveHypFrom(conclANDRecursiveProof(utils.BeforeLast(ps)...))
}

// c, p, q:
// p ∨ q, p ⇒ c, q ⇒ c ⊢ c
func byCasesProof() func(Term, Term, Term) *PropWrapper {
	r, p, q := initVars.r, initVars.p, initVars.q
	return ExpandDef(OR, p, q).
		LeftAssume().
		ConclForAllInst(r).
		DemoteHyp().
		DeriveHypFrom(ConclAND(p.Imply(r), q.Imply(r))).
		inst3Vars(r.AssertVar(), p.AssertVar(), q.AssertVar())
}

// c, p0, p1, ...:
// p0 ∨ p1 ∨ ..., p0 ⇒ c, p1 ⇒ c, ...  ⊢ c
func byCasesRecursiveProof(c Term, ps ...Term) *PropWrapper {
	Assert(len(ps) > 0)
	if len(ps) == 1 {
		return ModusPonens(ps[0], c)
	}
	if len(ps) == 2 {
		return ByCases(c, ps[0], ps[1])
	}
	t := Or(utils.BeforeLast(ps)...)
	return byCasesRecursiveProof(c, utils.BeforeLast(ps)...).
		PromoteHyp(t).
		DeriveTrans(ByCases(c, t, utils.Last(ps)))
}

// p ⊢ p ∨ q, q ⊢ p ∨ q
func conclORProof() (
	func(Term, Term) *PropWrapper,
	func(Term, Term) *PropWrapper) {
	p, q, r := initVars.p, initVars.q, initVars.r

	// (∀r.(((p ⇒ r) ∧ (q ⇒ r)) ⇒ r)) = (p ∨ q)
	w := ExpandDef(OR, p, q).EqSym()

	u := HypAND0(p.Imply(r), q.Imply(r)).
		DemoteHyp().                            // p, (p ⇒ r) ∧ (q ⇒ r) ⊢ r
		PromoteHyp(p.Imply(r).And(q.Imply(r))). // p ⊢ ((p ⇒ r) ∧ (q ⇒ r)) ⇒ r
		ConclForAll(r.AssertVar())              // p ⊢ ∀r.((p ⇒ r) ∧ (q ⇒ r)) ⇒ r
	u = w.EqMP(u) // p ⊢ p ∨ q

	v := HypAND1(p.Imply(r), q.Imply(r)).
		DemoteHyp().                            // q, (p ⇒ r) ∧ (q ⇒ r) ⊢ r
		PromoteHyp(p.Imply(r).And(q.Imply(r))). // q ⊢ ((p ⇒ r) ∧ (q ⇒ r)) ⇒ r
		ConclForAll(r.AssertVar())              // q ⊢ ∀r.((p ⇒ r) ∧ (q ⇒ r)) ⇒ r
	v = w.EqMP(v) // q ⊢ p ∨ q

	return u.inst2Vars(p.AssertVar(), q.AssertVar()), v.inst2Vars(p.AssertVar(), q.AssertVar())
}

// ¬p0, ¬p1, ..., ¬pn, p0 ∨ p1 ∨ ... ∨ pn ⊢ ⊥
func contradictRecursiveProof(ps ...Term) *PropWrapper {
	Assert(len(ps) > 0)
	if len(ps) == 1 {
		return Contradict(ps[0])
	}
	if len(ps) == 2 {
		return ByCases(F, ps[0], ps[1]).
			DeriveHypFrom(Contradict(ps[0]).PromoteHyp(ps[0])).
			DeriveHypFrom(Contradict(ps[1]).PromoteHyp(ps[1]))
	}
	p := Or(utils.BeforeLast(ps)...)
	return contradictRecursiveProof(utils.BeforeLast(ps)...).
		NegHyp(p).
		DeriveTrans(contradictRecursiveProof(p, utils.Last(ps)))
}

// p, p ⇒ q ⊢ q
func modusPonensProof() func(Term, Term) *PropWrapper {
	p, q := initVars.p, initVars.q
	return ExpandDef(IMPLY, p, q).
		LeftAssume().
		EqSym().
		LeftAssume().
		DeriveTrans(HypAND1(p, q)).
		inst2Vars(p.AssertVar(), q.AssertVar())
}

// ⊢ (x = y) ⇔ (y = x)
func commuteEQProof() func(Term, Term) *PropWrapper {
	x, y := initVars.x, initVars.y
	w := Assume(Eq(y, x)).
		EqSym().
		Deduct(Assume(Eq(x, y)).EqSym())
	return func(s, t Term) *PropWrapper {
		return w.
			TypeInst(MakeTypeSubst(TypeA, s.Type())).
			TermInst(
				makeTermSubstWithType(x, s),
				makeTermSubstWithType(y, t))
	}
}

// ⊢ (p ∧ q) ⇔ (q ∧ p)
func commuteANDProof() func(Term, Term) *PropWrapper {
	p, q := initVars.p, initVars.q
	return BoolInduct(p.To(p.And(q).Eq(q.And(p)))).
		eqRewrite(BooleanThms["p ∧ ⊤"](q)).
		eqRewrite(BooleanThms["p ∧ ⊥"](q)).
		eqRewrite(BooleanThms["⊤ ∧ p"](q)).
		eqRewrite(BooleanThms["⊥ ∧ p"](q)).
		DeriveHypFrom(Refl(q)).
		DeriveHypFrom(Refl(F)).
		inst2Vars(p.AssertVar(), q.AssertVar())
}

// ⊢ (p ∨ q) ⇔ (q ∨ p)
func commuteORProof() func(Term, Term) *PropWrapper {
	p, q := initVars.p, initVars.q
	return BoolInduct(p.To(p.Or(q).Eq(q.Or(p)))).
		eqRewrite(BooleanThms["p ∨ ⊤"](q)).
		eqRewrite(BooleanThms["p ∨ ⊥"](q)).
		eqRewrite(BooleanThms["⊤ ∨ p"](q)).
		eqRewrite(BooleanThms["⊥ ∨ p"](q)).
		DeriveHypFrom(Refl(q)).
		DeriveHypFrom(Refl(T)).
		inst2Vars(p.AssertVar(), q.AssertVar())
}

// ⊢ p ∨ ¬p
// Diaconescu's proof, uses the axiom of choice.
func excludedMiddleProof() func(Term) *PropWrapper {
	p := initVars.p
	x, y := Var("x", TypeBool), Var("y", TypeBool)

	// Q(x, y) := (x = y) ∨ p
	Q := x.Eq(y).Or(p)

	// R(y) := (εx.Q(x, y)) = y
	R := x.SuchThat(Q).Eq(y)

	// Notice that ⊢ (y = y) ∨ p is true, so by the axiom of choice
	// we have ⊢ Q(εx.Q(x, y), y),
	// which is identical to ⊢ R(y) ∨ p
	w := Refl(y).
		DeriveTrans(ConclOR0(Eq(y, y), p)).       // ⊢ (y = y) ∨ p
		DeriveTrans(InstExists(Exists(x)(Q), y)). // ⊢ ∃x.((x = y) ∨ p)
		DeriveTrans(SelectExists(x.To(Q)))        // ⊢ R(y) ∨ p

	// R(y) ⇒ (p ∨ ¬p) ⊢ p ∨ ¬p
	w = ByCases(p.Or(Not(p)), R, p).
		DeriveHypFrom(ConclOR0(p, Not(p)).PromoteHyp(p)).
		DeriveHypFrom(w)

	// R(⊤) := εx.Q(x, ⊤) ⇔ ⊤
	// R(⊥) := εx.Q(x, ⊥) ⇔ ⊥
	RT, RF := R.Substitute(MakeTermSubst(y, T)), R.Substitute(MakeTermSubst(y, F))

	hilbert := Const(core.MetaHilbert(), MakeFun(MakeFun(TypeBool, TypeBool), TypeBool))
	thm := ConclOR1(x.Eq(T), p).
		Deduct(ConclOR1(x.Eq(F), p)).                 // p ⊢ Q(x, ⊤) = Q(x, ⊥)
		Abs(x).                                       // p ⊢ λx.Q(x, ⊤) = λx.Q(x, ⊥)
		LeftApply(hilbert).                           // p ⊢ εx.Q(x, ⊤) = εx.Q(x, ⊥)
		EqTrans(Assume(RF)).                          // R(⊥), p ⊢ εx.Q(x, ⊤) = ⊥
		EqMP(Assume(RT).EqSym().EqMP(DerivesTrue)).   // R(⊤), R(⊥), p ⊢ ⊥
		NegHyp(p).                                    // R(⊤), R(⊥) ⊢ ¬p
		DeriveTrans(ConclOR1(p, Not(p))).             // R(⊤), R(⊥) ⊢ p ∨ ¬p
		PromoteHyp(RT).                               // R(⊥) ⊢ R(⊤) ⇒ (p ∨ ¬p)
		DeriveTrans(w.TermInst(MakeTermSubst(y, T))). // R(⊥) ⊢ p ∨ ¬p
		PromoteHyp(RF).                               // ⊢ R(⊥) ⇒ (p ∨ ¬p)
		DeriveTrans(w.TermInst(MakeTermSubst(y, F)))  // ⊢ p ∨ ¬p

	return thm.instVar(p.AssertVar())
}

// λp.S(p):
// S(⊤), S(⊥) ⊢ S(p)
func boolInductProof() func(Term) *PropWrapper {
	p, S := initVars.p, initVars.S

	u := Assume(Eq(T, p)).
		DeriveHypFrom(DerivesTrue.Deduct(Assume(p))).
		LeftApply(S).
		LeftAssume().
		PromoteHyp(p) // S(⊤) ⊢ p ⇒ S(p)

	v := Assume(Eq(p, F)).
		EqSym().
		DeriveHypFrom(EqualsFalse(p).RightAssume()).
		LeftApply(S).
		LeftAssume().
		PromoteHyp(Not(p)) // S(⊥) ⊢ ¬p ⇒ S(p)

	w := ByCases(S.Apply(p), p, Not(p)).
		DeriveHypFrom(u).
		DeriveHypFrom(v).
		DeriveHypFrom(ExcludedMiddle(p))

	return func(t Term) *PropWrapper {
		_t, ok := t.AsAbsTerm()
		Assert(ok && IsBool(_t.Var()) && IsBool(_t.Body()))
		return w.
			TermInst(
				MakeTermSubst(p, _t.Var()),
				MakeTermSubst(S, _t)).
			Rewrite(betaAbsRewrite(_t))
	}
}

// λp.S(p):
// ⊢ ∀p.S(p) ⇔ S(⊤) ∧ S(⊥)
func boolForAllProof() func(Term) *PropWrapper {
	p, S := initVars.p, initVars.S

	u := BoolInduct(p.To(S.Apply(p))).
		DeriveHypFrom(HypAND0(S.Apply(T), S.Apply(F))).
		DeriveHypFrom(HypAND1(S.Apply(T), S.Apply(F))).
		ConclForAll(p.AssertVar())

	v := ConclAND(S.Apply(T), S.Apply(F)).
		DeriveHypFrom(InstForAll(ForAll(p)(S.Apply(p)), T)).
		DeriveHypFrom(InstForAll(ForAll(p)(S.Apply(p)), F))

	w := u.Deduct(v)

	return func(t Term) *PropWrapper {
		_t, ok := t.AsAbsTerm()
		Assert(ok && IsBool(_t.Var()) && IsBool(_t.Body()))
		return w.
			RewriteConcl(BoundVarRewrite(p.AssertVar(), _t.Var())).
			TermInst(MakeTermSubst(S, _t)).
			Rewrite(DeepBetaAbs(_t))
	}
}

// λp.S(p):
// ⊢ ∃p.S(p) ⇔ S(⊤) ∨ S(⊥)
func boolExistsProof() func(Term) *PropWrapper {
	p, S := initVars.p, initVars.S

	w := BoolForAll(p.To(Not(S.Apply(p)))).
		LeftApply(NOT).
		Rewrite(DeepNegRewrite)

	return func(t Term) *PropWrapper {
		_t, ok := t.AsAbsTerm()
		Assert(ok && IsBool(_t.Var()) && IsBool(_t.Body()))
		return w.
			RewriteConcl(BoundVarRewrite(p.AssertVar(), _t.Var())).
			TermInst(MakeTermSubst(S, _t)).
			Rewrite(DeepBetaAbs(_t))
	}
}

// ⊢ ¬¬p ⇔ p
func doubleNegProof() func(Term) *PropWrapper {
	p := initVars.p
	return BoolInduct(p.To(Not(Not(p)).Eq(p))).
		DeriveHypFrom(NotTrue.LeftApply(NOT).EqTrans(NotFalse)).
		DeriveHypFrom(NotFalse.LeftApply(NOT).EqTrans(NotTrue)).
		instVar(p.AssertVar())
}

func booleanThmsProof() map[string]func(Term) *PropWrapper {
	thms := map[string]func(Term) *PropWrapper{}

	p, np := initVars.p, Not(initVars.p)

	thms["p ⇔ ⊤"] =
		Assume(p).
			Deduct(DerivesTrue).
			Deduct(Assume(p.Eq(T)).EqSym().EqMP(DerivesTrue)).
			instVar(p.AssertVar())

	thms["p ⇔ ⊥"] = EqualsFalse

	thms["⊤ ⇔ p"] =
		DerivesTrue.
			Deduct(Assume(p)).
			Deduct(Assume(Eq(T, p)).EqMP(DerivesTrue)).
			instVar(p.AssertVar())

	thms["⊥ ⇔ p"] =
		Assume(p.Eq(F)).
			EqSym().
			Deduct(Assume(Eq(F, p)).EqSym()).
			EqTrans(EqualsFalse(p)).
			instVar(p.AssertVar())

	thms["p ⇔ p"] =
		Refl(p).
			Deduct(DerivesTrue).
			instVar(p.AssertVar())

	thms["p ⇔ ¬p"] =
		BoolInduct(p.To(p.Eq(np).Eq(F))).
			eqRewrite(NotFalse).
			eqRewrite(NotTrue).
			eqRewrite(EqualsFalse(T)).
			eqRewrite(thms["p ⇔ ⊤"](F)).
			eqRewrite(NotTrue).
			DeriveHypFrom(Refl(F)).
			instVar(p.AssertVar())

	thms["¬p ⇔ p"] =
		BoolInduct(p.To(np.Eq(p).Eq(F))).
			eqRewrite(NotFalse).
			eqRewrite(NotTrue).
			eqRewrite(EqualsFalse(T)).
			eqRewrite(thms["p ⇔ ⊤"](F)).
			eqRewrite(NotTrue).
			DeriveHypFrom(Refl(F)).
			instVar(p.AssertVar())

	thms["p ∧ ⊤"] =
		ConclAND(p, T).
			DeriveHypFrom(DerivesTrue).
			Deduct(HypAND0(p, T)).
			instVar(p.AssertVar())

	thms["p ∧ ⊥"] =
		FalseDerives(p.And(F)).
			Deduct(HypAND1(p, F)).
			instVar(p.AssertVar())

	thms["⊤ ∧ p"] =
		ConclAND(T, p).
			DeriveHypFrom(DerivesTrue).
			Deduct(HypAND1(T, p)).
			instVar(p.AssertVar())

	thms["⊥ ∧ p"] =
		FalseDerives(And(F, p)).
			Deduct(HypAND0(F, p)).
			instVar(p.AssertVar())

	thms["p ∧ p"] =
		ConclAND(p, p).
			Deduct(HypAND0(p, p)).
			instVar(p.AssertVar())

	thms["p ∧ ¬p"] =
		Contradict(p).
			DeriveHypFrom(HypAND0(p, np)).
			DeriveHypFrom(HypAND1(p, np)).
			Deduct(FalseDerives(p.And(np))).
			EqSym().
			instVar(p.AssertVar())

	thms["¬p ∧ p"] =
		Contradict(p).
			DeriveHypFrom(HypAND0(np, p)).
			DeriveHypFrom(HypAND1(np, p)).
			Deduct(FalseDerives(np.And(p))).
			EqSym().
			instVar(p.AssertVar())

	thms["p ∨ ⊤"] =
		ConclOR1(p, T).
			Deduct(DerivesTrue).
			instVar(p.AssertVar())

	thms["p ∨ ⊥"] =
		ByCases(p, p, F).
			DeriveHypFrom(FalseDerives(p).PromoteHyp(F)).
			DeriveHypFrom(Assume(p).PromoteHyp(p)).
			Deduct(ConclOR0(p, F)).
			EqSym().
			instVar(p.AssertVar())

	thms["⊤ ∨ p"] =
		ConclOR0(T, p).
			Deduct(DerivesTrue).
			instVar(p.AssertVar())

	thms["⊥ ∨ p"] =
		ByCases(p, F, p).
			DeriveHypFrom(FalseDerives(p).PromoteHyp(F)).
			DeriveHypFrom(Assume(p).PromoteHyp(p)).
			Deduct(ConclOR1(F, p)).
			EqSym().
			instVar(p.AssertVar())

	thms["p ∨ p"] =
		ByCases(p, p, p).
			DeriveHypFrom(Assume(p).PromoteHyp(p)).
			Deduct(ConclOR0(p, p)).
			EqSym().
			instVar(p.AssertVar())

	thms["p ∨ ¬p"] =
		ExcludedMiddle(p).
			Deduct(DerivesTrue).
			instVar(p.AssertVar())

	thms["¬p ∨ p"] =
		ExcludedMiddle(np).
			eqRewrite(DoubleNeg(p)).
			Deduct(DerivesTrue).
			instVar(p.AssertVar())

	thms["p ⇒ ⊤"] =
		DerivesTrue.
			PromoteHyp(p).
			Deduct(DerivesTrue).
			instVar(p.AssertVar())

	thms["p ⇒ ⊥"] = ImpliesFalse

	thms["⊤ ⇒ p"] =
		Assume(p).
			PromoteHyp(T).
			Deduct(DerivesTrue.DeriveTrans(ModusPonens(T, p))).
			instVar(p.AssertVar())

	thms["⊥ ⇒ p"] =
		FalseDerives(p).
			PromoteHyp(F).
			Deduct(DerivesTrue).
			instVar(p.AssertVar())

	thms["p ⇒ p"] =
		Assume(p).
			PromoteHyp(p).
			Deduct(DerivesTrue).
			instVar(p.AssertVar())

	thms["p ⇒ ¬p"] =
		BoolInduct(p.To(p.Imply(np).Eq(np))).
			eqRewrite(NotFalse).
			eqRewrite(NotTrue).
			eqRewrite(ImpliesFalse(T)).
			eqRewrite(thms["⊥ ⇒ p"](T)).
			eqRewrite(NotTrue).
			DeriveHypFrom(Refl(T)).
			DeriveHypFrom(Refl(F)).
			instVar(p.AssertVar())

	thms["¬p ⇒ p"] =
		BoolInduct(p.To(np.Imply(p).Eq(p))).
			eqRewrite(NotFalse).
			eqRewrite(NotTrue).
			eqRewrite(ImpliesFalse(T)).
			eqRewrite(thms["⊥ ⇒ p"](T)).
			eqRewrite(NotTrue).
			DeriveHypFrom(Refl(T)).
			DeriveHypFrom(Refl(F)).
			instVar(p.AssertVar())

	return thms
}

// (¬p ⇔ ¬q) ⇔ (p ⇔ q)
func negIffNegProof() func(Term, Term) *PropWrapper {
	p, q := initVars.p, initVars.q
	return Assume(Eq(Not(p), Not(q))).
		LeftApply(NOT).
		EqTrans(DoubleNeg(q)).
		eqRewrite(DoubleNeg(p)).
		Deduct(Assume(Eq(p, q)).LeftApply(NOT)).
		EqSym().
		inst2Vars(p.AssertVar(), q.AssertVar())
}

func binaryThmsProof() map[string]func(Term, Term) *PropWrapper {
	thms := map[string]func(Term, Term) *PropWrapper{}

	p, q := initVars.p, initVars.q
	np, nq := Not(p), Not(q)

	thms["(¬p ⇔ ¬q) ⇔ (p ⇔ q)"] = negIffNegProof()

	thms["(p ⇒ q) ⇔ (¬p ∨ q)"] =
		BoolInduct(p.To(p.Imply(q).Eq(np.Or(q)))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["(p ∨ q) ⇔ (¬p ⇒ q)"] =
		BoolInduct(p.To(p.Or(q).Eq(np.Imply(q)))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["¬(p ∨ q) ⇔ (¬p ∧ ¬q)"] =
		BoolInduct(p.To(Not(p.Or(q)).Eq(np.And(nq)))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["¬(p ∧ q) ⇔ (¬p ∨ ¬q)"] =
		BoolInduct(p.To(Not(p.And(q)).Eq(np.Or(nq)))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["¬(p ⇒ q) ⇔ (p ∧ ¬q)"] =
		BoolInduct(p.To(Not(p.Imply(q)).Eq(p.And(nq)))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["(p ⊕ q) ⇔ (¬p ⇔ q)"] =
		BoolInduct(q.To(p.Xor(q).Eq(np.Eq(q)))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["p ∧ (p ∨ q) ⇔ p"] =
		BoolInduct(q.To(p.And(p.Or(q)).Eq(p))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["p ∨ (p ∧ q) ⇔ p"] =
		BoolInduct(q.To(p.Or(p.And(q)).Eq(p))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["(p ⇔ q) ⇔ ((p ∧ q) ∨ (¬p ∧ ¬q))"] =
		BoolInduct(q.To(p.Eq(q).Eq(p.And(q).Or(np.And(nq))))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	thms["(p ⊕ q) ⇔ ((p ∨ q) ∧ (¬p ∨ ¬q))"] =
		BoolInduct(q.To(p.Xor(q).Eq(p.Or(q).And(np.Or(nq))))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DoubleNeg(p)).
			DeriveHypFrom(DerivesTrue).
			inst2Vars(p.AssertVar(), q.AssertVar())

	return thms
}

func ternaryThmsProof() map[string]func(Term, Term, Term) *PropWrapper {
	thms := map[string]func(Term, Term, Term) *PropWrapper{}

	p, q, r := initVars.p, initVars.q, initVars.r
	thms["((p ∧ q) ∧ r) ⇔ (p ∧ (q ∧ r))"] =
		BoolInduct(p.To((p.And(q)).And(r).Eq(p.And(q.And(r))))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())

	thms["((p ∨ q) ∨ r) ⇔ (p ∨ (q ∨ r))"] =
		thms["((p ∧ q) ∧ r) ⇔ (p ∧ (q ∧ r))"](Not(p), Not(q), Not(r)).
			LeftApply(NOT).
			Rewrite(DeepNegRewrite).
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())

	thms["((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r))"] =
		BoolInduct(p.To((p.Eq(q)).Eq(r).Eq(p.Eq(q.Eq(r))))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			DeriveHypFrom(BinaryThms["(p ⊕ q) ⇔ (¬p ⇔ q)"](q, r).EqSym()).
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())

	thms["(p ⇒ (q ∧ r)) ⇔ ((p ⇒ q) ∧ (p ⇒ r))"] =
		BoolInduct(p.To(p.Imply(q.And(r)).Eq((p.Imply(q)).And(p.Imply(r))))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())

	thms["(p ∧ (q ∨ r)) ⇔ ((p ∧ q) ∨ (p ∧ r))"] =
		BoolInduct(p.To(p.And(q.Or(r)).Eq((p.And(q)).Or(p.And(r))))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())

	thms["(p ∨ (q ∧ r)) ⇔ ((p ∨ q) ∧ (p ∨ r))"] =
		BoolInduct(p.To(p.Or(q.And(r)).Eq((p.Or(q)).And(p.Or(r))))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())

	thms["p ⇒ q, p ∧ r ⊢ q ∧ r"] =
		BoolInduct(r.To(p.And(r).Imply(q.And(r)))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			DemoteHyp().
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())

	thms["p ⇒ q, p ∨ r ⊢ q ∨ r"] =
		BoolInduct(r.To(p.Or(r).Imply(q.Or(r)))).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			DemoteHyp().
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())

	thms["(p ⇒ r) ∧ (q ⇒ r) ⇔ ((p ∨ q) ⇒ r)"] =
		BoolInduct(r.To(p.Imply(r).And(q.Imply(r)).Eq(p.Or(q).Imply(r)))).
			Rewrite(DeepBoolRewrite).
			eqRewrite(BinaryThms["¬(p ∨ q) ⇔ (¬p ∧ ¬q)"](p, q)).
			Rewrite(DeepBoolRewrite).
			DeriveHypFrom(DerivesTrue).
			inst3Vars(p.AssertVar(), q.AssertVar(), r.AssertVar())
	return thms
}

// c, x:
// ⊢ Cond(c, x, x) = x
func condIdProof() func(Term, Term) *PropWrapper {
	p, x, y := initVars.p, initVars.x, initVars.y
	u := ExpandDef(ext.COND, p, x, x).
		eqRewrite(TernaryThms["(p ⇒ r) ∧ (q ⇒ r) ⇔ ((p ∨ q) ⇒ r)"](p, Not(p), y.Eq(x)).Abs(y)).
		RewriteConclRhs(DeepBoolRewrite).
		RewriteConclRhs(hilbertRewrite)
	return func(c, x Term) *PropWrapper {
		Assert(IsBool(c))
		return u.
			TypeInst(MakeTypeSubst(TypeA, x.Type())).
			TermInst(
				makeTermSubstWithType(initVars.p, c),
				makeTermSubstWithType(initVars.x, x))
	}
}

// x, y:
// ⊢ Cond(⊤, x, y) = x
// ⊢ Cond(⊥, x, y) = y
func condClauseProof() (
	func(Term, Term) *PropWrapper,
	func(Term, Term) *PropWrapper) {
	x, y := initVars.x, initVars.y
	wT := ExpandDef(ext.COND, T, x, y).
		RewriteConclRhs(DeepBoolRewrite).
		RewriteConclRhs(hilbertRewrite)
	wF := ExpandDef(ext.COND, F, x, y).
		RewriteConclRhs(DeepBoolRewrite).
		RewriteConclRhs(hilbertRewrite)
	return func(x, y Term) *PropWrapper {
			return wT.
				TypeInst(MakeTypeSubst(TypeA, x.Type())).
				TermInst(
					makeTermSubstWithType(initVars.x, x),
					makeTermSubstWithType(initVars.y, y))
		}, func(x, y Term) *PropWrapper {
			return wF.
				TypeInst(MakeTypeSubst(TypeA, x.Type())).
				TermInst(
					makeTermSubstWithType(initVars.x, x),
					makeTermSubstWithType(initVars.y, y))
		}
}

// ∀x.P(x), t:
// ∀x.P(x) ⊢ P(t)
func instForAllProof() func(Term, Term) *PropWrapper {
	// ∀(P) ⊢ P(x)
	w := expandFORALL.
		LeftAssume().
		RightApply(initVars.x).
		RewriteConclRhs(betaRewrite).
		EqSym().
		EqMP(DerivesTrue)
	return func(s, t Term) *PropWrapper {
		abs := MatchesFORALL(s)
		Assert(!abs.IsZero() && abs.Var().Type().Equals(t.Type()))
		return w.
			TypeInst(MakeTypeSubst(TypeA, abs.Var().Type())).
			TermInst(
				makeTermSubstWithType(initVars.P, abs),
				makeTermSubstWithType(initVars.x, t)).
			RewriteConcl(betaAbsRewrite(abs))
	}
}

// λx.P(x):
// ⊢ ¬(∀x.P(x)) ⇔ ∃x.¬P(x)
func negForAllProof() func(Term) *PropWrapper {
	x, P := initVars.x, initVars.P
	w := NegExists(x.To(P.Apply(x))).
		EqSym().
		LeftApply(NOT).
		Abs(P).
		RightApply(x.To(Not(P.Apply(x)))).
		RewriteConcl(DeepBeta).
		Rewrite(DeepRewrite(DoubleNegRewrite))

	return func(t Term) *PropWrapper {
		_t, ok := t.AsAbsTerm()
		Assert(ok && IsBool(_t.Body()))
		return w.
			TypeInst(MakeTypeSubst(TypeA, _t.Var().Type())).
			RewriteConcl(rewriteInitVar(initVars.x, _t.Var())).
			TermInst(makeTermSubstWithType(initVars.P, _t)).
			Rewrite(DeepBetaAbs(_t))
	}
}

// λx.P(x), λx.Q(x):
// ⊢ ∀x.(P(x) ∧ Q(x)) ⇔ (∀x.P(x) ∧ ∀x.Q(x))
func forAllANDProof() func(Term, Term) *PropWrapper {
	x := initVars.x
	Px, Qx := initVars.P.Apply(x), initVars.Q.Apply(x)

	u := ConclAND(Px, Qx).
		HypForAllInst(x.AssertVar(), Px).
		HypForAllInst(x.AssertVar(), Qx).
		DeriveHypFrom(HypAND0(ForAll(x)(Px), ForAll(x)(Qx))).
		DeriveHypFrom(HypAND1(ForAll(x)(Px), ForAll(x)(Qx))).
		ConclForAll(x.AssertVar())

	v := ConclAND(ForAll(x)(Px), ForAll(x)(Qx)).
		DeriveHypFrom(
			HypAND0(Px, Qx).
				HypForAllInst(x.AssertVar(), Px.And(Qx)).
				ConclForAll(x.AssertVar())).
		DeriveHypFrom(
			HypAND1(Px, Qx).
				HypForAllInst(x.AssertVar(), Px.And(Qx)).
				ConclForAll(x.AssertVar()))

	w := u.Deduct(v)
	return instPredicates(w)
}

// λx.P(x), λx.Q(x):
// ∀x.(P(x) ⇒ Q(x)), ∀x.P(x) ⊢ ∀x.Q(x)
func forAllIMPLYProof() func(Term, Term) *PropWrapper {
	x := initVars.x
	Px, Qx := initVars.P.Apply(x), initVars.Q.Apply(x)

	w := ModusPonens(Px, Qx).
		DeriveHypFrom(HypAND0(Px, Px.Imply(Qx))).
		DeriveHypFrom(HypAND1(Px, Px.Imply(Qx))).
		HypForAllInst(x.AssertVar(), Px.And(Px.Imply(Qx))).
		eqRewrite(ForAllAND(x.To(Px), x.To(Px.Imply(Qx)))).
		DeriveHypFrom(ConclAND(ForAll(x)(Px), ForAll(x)(Px.Imply(Qx)))).
		ConclForAll(x.AssertVar())

	return instPredicates(w)
}

// x, Q:
// ⊢ (∀x.Q) ⇔ Q (given x not in Q)
func mootForAllProof() func(VarTerm, Term) *PropWrapper {
	x, q := initVars.x, initVars.q

	// ⊢ (∀x.⊤) ⇔ ⊤
	u := DerivesTrue.
		ConclForAll(x.AssertVar()).
		Deduct(DerivesTrue)

	// ⊢ (∀x.⊥) ⇔ ⊥
	v := FalseDerives(ForAll(x)(F)).
		Deduct(InstForAll(ForAll(x)(F), x))

	// ⊢ (∀x.q) ⇔ q
	w := BoolInduct(q.To(ForAll(x)(q).Eq(q))).
		DeriveHypFrom(u).
		DeriveHypFrom(v)

	return func(x VarTerm, t Term) *PropWrapper {
		Assert(IsBool(t) && !t.HasFree(x))
		return w.
			TypeInst(MakeTypeSubst(TypeA, x.Type())).
			RewriteConcl(rewriteInitVar(initVars.x, x)).
			TermInst(MakeTermSubst(q, t))
	}
}

// t0, t1
// where t0 and t1 have the same body
// and the same univ quantifiers with different order:
// ⊢ t0 ⇔ t1
func reorderForAllProof() func(Term, Term) *PropWrapper {
	rewriteForAllBinders := func(t0, t1 Term) *PropWrapper {
		if t0.AlphaEquals(t1) {
			return Refl(t1)
		}
		vars0, _ := DecomposesFORALL(t0)
		vars1, _ := DecomposesFORALL(t1)
		Assert(!vars0.Empty() && !vars1.Empty() &&
			vars0.Size() == vars1.Size() && t0.AlphaEquals(t1))

		w := Refl(t0)
		current := t0
		for i := range vars0.Size() {
			currentVars, _ := DecomposesFORALL(current)
			Assert(currentVars.Size() == vars1.Size())
			if currentVars.Ind(i).Equals(vars1.Ind(i)) {
				continue
			}
			u := BoundVarRewrite(currentVars.Ind(i), vars1.Ind(i))(current)
			Assert(u != nil)
			w = w.EqTrans(u)
			current = Rhs(u)
		}
		Assert(Rhs(w).AlphaEquals(t1))
		return w
	}

	reorderExact := func(t0, t1 Term) *PropWrapper {
		// Remove universal vars one by one,
		// then add them back in new order.
		induct := func(
			vars0, vars1 []VarTerm,
			t Term, c chan<- *PropWrapper) {
			u := InstForAll(t, vars0[0])
			for _, v := range vars0[1:] {
				u = u.ConclForAllInst(v)
			}

			for _, v := range slices.Backward(vars1) {
				u = u.ConclForAll(v)
			}
			c <- u
		}

		if t0.AlphaEquals(t1) {
			return Refl(t1)
		}
		vars0, body0 := DecomposesFORALL(t0)
		vars1, body1 := DecomposesFORALL(t1)
		Assert(!vars0.Empty() && !vars1.Empty() &&
			vars0.ElementEquals(&vars1) && body0.AlphaEquals(body1))
		// find i and j such that vars are only different between [i:j+1].
		i, j := 0, vars0.Size()-1
		var consts []ConstTerm // records the corresponding ∀ before i.
		for ; i < vars0.Size() && vars0.Ind(i).Equals(vars1.Ind(i)); i++ {
			consts = append(consts, t0.Core().(AppliedTerm).Fun().(ConstTerm))
			t0 = MatchesFORALL(t0).Body()
			t1 = MatchesFORALL(t1).Body()
		}
		for ; j >= 0 && vars0.Ind(j).Equals(vars1.Ind(j)); j-- {
		}

		diffVars0, diffVars1 := vars0.Section(i, j+1), vars1.Section(i, j+1)

		u0, u1 := make(chan *PropWrapper, 1), make(chan *PropWrapper, 1)
		go induct(diffVars0, diffVars1, t0, u0)
		go induct(diffVars1, diffVars0, t1, u1)
		u := (<-u1).Deduct(<-u0)
		for k := i - 1; k >= 0; k-- {
			u = u.Abs(vars0.Ind(k)).LeftApply(consts[k])
		}
		return u
	}

	return func(t0, t1 Term) *PropWrapper {
		if t0.AlphaEquals(t1) {
			return Refl(t1)
		}
		vars0, _ := DecomposesFORALL(t0)
		vars1, _ := DecomposesFORALL(t1)
		Assert(!vars0.Empty() && !vars1.Empty() &&
			vars0.Size() == vars1.Size())
		if vars0.ElementEquals(&vars1) {
			return reorderExact(t0, t1)
		}

		sorted0 := univQuantifiersSort(t0)
		sorted1 := univQuantifiersSort(t1)
		Assert(sorted0.AlphaEquals(sorted1))
		w := reorderExact(t0, sorted0).
			EqTrans(rewriteForAllBinders(sorted0, sorted1)).
			EqTrans(reorderExact(sorted1, t1))
		Assert(Lhs(w).AlphaEquals(t0) && Rhs(w).AlphaEquals(t1))
		return w
	}
}

// λx.f(x), λx.g(x):
// ⊢ (λx.f(x) = λx.g(x)) ⇔ ∀x.(f(x) = g(x))
func funEqProof() func(Term, Term) *PropWrapper {
	return func(s, t Term) *PropWrapper {
		_s, ok0 := s.AsAbsTerm()
		_t, ok1 := t.AsAbsTerm()
		Assert(ok0 && ok1 &&
			_s.Var().Equals(_t.Var()) &&
			_s.Body().Type().Equals(_t.Body().Type()))
		x := _s.Var()
		// ∀x.(f(x) = g(x)) ⊢ λx.f(x) = λx.g(x)
		u := InstForAll(ForAll(x)(Eq(_s.Body(), _t.Body())), x).Abs(x)
		// λx.f(x) = λx.g(x) ⊢ ∀x.(f(x) = g(x))
		v := Beta(Apply(s, x)).
			EqSym().
			EqTrans(Assume(Eq(s, t)).RightApply(x)).
			EqTrans(Beta(Apply(t, x))).
			ConclForAll(x)
		return u.Deduct(v)
	}
}

// ∃x.P(x), t:
// P(t) ⊢ ∃x.P(x)
func instExistsProof() func(Term, Term) *PropWrapper {
	P, x := initVars.P, initVars.x
	// P(x) ⊢ ∃(P)
	w := expandEXISTS.
		EqSym().
		EqMP(Select(P.Apply(x)))
	return func(s, t Term) *PropWrapper {
		abs := MatchesEXISTS(s)
		Assert(!abs.IsZero() && abs.Var().Type().Equals(t.Type()))
		return w.
			TypeInst(MakeTypeSubst(TypeA, abs.Var().Type())).
			TermInst(
				makeTermSubstWithType(initVars.P, abs),
				makeTermSubstWithType(initVars.x, t)).
			Rewrite(betaAbsRewrite(abs))
	}
}

// λx.P(x):
// ∃x.P(x) ⊢ P(εx.P(x))
func selectExistsProof() func(Term) *PropWrapper {
	// ∃(P) ⊢ P(εP)
	w := expandEXISTS.LeftAssume()
	return func(t Term) *PropWrapper {
		_t, ok := t.AsAbsTerm()
		Assert(ok && IsBool(_t.Body()))
		return w.
			TypeInst(MakeTypeSubst(TypeA, _t.Var().Type())).
			TermInst(makeTermSubstWithType(initVars.P, _t)).
			Rewrite(betaAbsRewrite(_t))
	}
}

// λx.P(x):
// ⊢ ¬∃x.P(x) ⇔ ∀x.¬P(x)
func negExistsProof() func(Term) *PropWrapper {
	x, P := initVars.x, initVars.P
	Px := P.Apply(x)

	u := EqualsFalse(P.Apply(x.SuchThat(Px))).
		EqSym().
		// ∀x.¬P(x) ⊢ P(εx.P(x)) = ⊥
		EqMP(InstForAll(ForAll(x)(Not(Px)), x.SuchThat(Px))).
		// ∀x.¬P(x), ∃x.P(x) ⊢ ⊥
		EqMP(SelectExists(x.To(Px))).
		// ∀x.¬P(x) ⊢ ¬(∃x.P(x))
		NegHyp(Exists(x)(Px))

	v := InstExists(Exists(x)(Px), x).
		Contraposition(Px).        // ¬∃x.P(x) ⊢ ¬P(x)
		ConclForAll(x.AssertVar()) // ¬∃x.P(x) ⊢ ∀x.¬P(x)

	// ⊢ ¬(∃x.P(x)) = ∀x.¬P(x)
	w := u.Deduct(v)

	return func(t Term) *PropWrapper {
		_t, ok := t.AsAbsTerm()
		Assert(ok && IsBool(_t.Body()))
		return w.
			TypeInst(MakeTypeSubst(TypeA, _t.Var().Type())).
			RewriteConcl(rewriteInitVar(initVars.x, _t.Var())).
			TermInst(makeTermSubstWithType(initVars.P, _t)).
			Rewrite(DeepBetaAbs(_t))
	}
}

// λx.P(x), λx.Q(x):
// ∃x.(P(x) ∧ Q(x)) ⊢ ∃x.P(x) ∧ ∃x.Q(x)
func existsANDProof() func(Term, Term) *PropWrapper {
	x := initVars.x
	Px, Qx := initVars.P.Apply(x), initVars.Q.Apply(x)

	// ⊢ (∀x.¬P(x)) ⇒ (∀x.(¬P(x) ∨ ¬Q(x)))
	u := ConclOR0(Not(Px), Not(Qx)).
		HypForAllInst(x.AssertVar(), Not(Px)).
		ConclForAll(x.AssertVar()).
		PromoteHyp(ForAll(x)(Not(Px)))

	// ⊢ (∀x.¬Q(x)) ⇒ (∀x.(¬P(x) ∨ ¬Q(x)))
	v := ConclOR1(Not(Px), Not(Qx)).
		HypForAllInst(x.AssertVar(), Not(Qx)).
		ConclForAll(x.AssertVar()).
		PromoteHyp(ForAll(x)(Not(Qx)))

	// (∀x.¬P(x)) ∨ (∀x.¬Q(x)) ⊢ (∀x.(¬P(x) ∨ ¬Q(x)))
	w := ByCases(
		ForAll(x)(Not(Px).Or(Not(Qx))),
		ForAll(x)(Not(Px)),
		ForAll(x)(Not(Qx))).
		DeriveHypFrom(u).
		DeriveHypFrom(v).
		Contraposition(ForAll(x)(Not(Px)).Or(ForAll(x)(Not(Qx)))).
		Rewrite(DeepNegRewrite)
	return instPredicates(w)
}

// λx.P(x), λx.Q(x):
// ⊢ ∃x.(P(x) ∨ Q(x)) ⇔ (∃x.P(x) ∨ ∃x.Q(x))
func existsORProof() func(Term, Term) *PropWrapper {
	x := initVars.x
	Px, Qx := initVars.P.Apply(x), initVars.Q.Apply(x)

	w := ForAllAND(x.To(Not(Px)), x.To(Not(Qx))).
		LeftApply(NOT).
		Rewrite(DeepNegRewrite)
	return instPredicates(w)
}

// λx.P(x), λx.Q(x):
// ∀x.(P(x) ⇒ Q(x)), ∃x.P(x) ⊢ ∃x.Q(x)
func existsIMPLYProof() func(Term, Term) *PropWrapper {
	x := initVars.x
	Px, Qx := initVars.P.Apply(x), initVars.Q.Apply(x)
	ePx, eQx := Exists(x)(Px), Exists(x)(Qx)

	w := ExistsAND(
		ePx.Core().(AppliedTerm).Arg(),
		eQx.Core().(AppliedTerm).Arg()).
		eqRewrite(
			ExpandDef(IMPLY, Px, Qx).
				EqMP(InstForAll(ForAll(x)(Px.Imply(Qx)), x)).
				Abs(x).
				LeftApply(ePx.Core().(AppliedTerm).Fun())).
		DeriveTrans(HypAND1(ePx, eQx))
	return instPredicates(w)
}

// x, Q:
// ⊢ (∃x.Q) ⇔ Q (given x not in Q)
func mootExistsProof() func(VarTerm, Term) *PropWrapper {
	x, q := initVars.x, initVars.q

	// ⊢ (∃x.⊥) ⇔ ⊥
	u := FalseDerives(Exists(x)(F)).
		Deduct(Assume(F).HypExists(x.AssertVar(), F))

	// ⊢ (∃x.⊤) ⇔ ⊤
	v := InstExists(Exists(x)(T), x).
		Deduct(DerivesTrue)

	// ⊢ (∃x.q) ⇔ q
	w := BoolInduct(q.To(Exists(x)(q).Eq(q))).
		DeriveHypFrom(u).
		DeriveHypFrom(v)

	return func(x VarTerm, t Term) *PropWrapper {
		Assert(IsBool(t) && !t.HasFree(x))
		return w.
			TypeInst(MakeTypeSubst(TypeA, x.Type())).
			RewriteConcl(rewriteInitVar(initVars.x, x)).
			TermInst(MakeTermSubst(q, t))
	}
}

// t0, t1
// where t0 and t1 have the same body
// and the same existential quantifiers with different order:
// ⊢ t0 ⇔ t1
func reorderExistsProof(t0, t1 Term) *PropWrapper {
	if t0.AlphaEquals(t1) {
		return Refl(t1)
	}
	vars0, body0 := DecomposesEXISTS(t0)
	vars1, body1 := DecomposesEXISTS(t1)
	Assert(!vars0.Empty() && !vars1.Empty() && vars0.Size() == vars1.Size())
	s0, s1 := Not(body0), Not(body1)
	for _, v := range vars0.Backward() {
		s0 = ForAll(v)(s0)
	}
	for _, v := range vars1.Backward() {
		s1 = ForAll(v)(s1)
	}
	w := ReorderForAll(s0, s1).
		LeftApply(NOT).
		Rewrite(DeepNegRewrite)
	if u := DeepNegRewrite(body0); u != nil {
		w = w.eqReplacementConcl(u.EqSym())
	}
	if u := DeepNegRewrite(body1); u != nil {
		w = w.eqReplacementConcl(u.EqSym())
	}
	Assert(Lhs(w).AlphaEquals(t0) && Rhs(w).AlphaEquals(t1))
	return w
}

func prenexThmsProof() map[string]func(Term, Term) *PropWrapper {
	thms := map[string]func(Term, Term) *PropWrapper{}

	x, Px, q := initVars.x, initVars.P.Apply(initVars.x), initVars.q
	forall := Const(FORALL.Meta(), MakeFun(MakeFun(TypeA, TypeBool), TypeBool))
	exists := Const(EXISTS.Meta(), MakeFun(MakeFun(TypeA, TypeBool), TypeBool))

	instantiate := func(w *PropWrapper) func(Term, Term) *PropWrapper {
		return func(s, t Term) *PropWrapper {
			_s, ok := s.AsAbsTerm()
			Assert(ok && IsBool(_s.Body()) && IsBool(t))
			return w.
				TypeInst(MakeTypeSubst(TypeA, _s.Var().Type())).
				RewriteConcl(rewriteInitVar(initVars.x, _s.Var())).
				TermInst(
					makeTermSubstWithType(initVars.P, _s),
					MakeTermSubst(q, t)).
				Rewrite(DeepBetaAbs(_s))
		}
	}

	w := ForAllAND(x.To(Px), x.To(q)).
		EqSym().
		eqRewrite(MootForAll(x.AssertVar(), q))
	thms["(∀x.P(x)) ∧ Q ⇔ ∀x.(P(x) ∧ Q)"] = instantiate(w)

	w = ForAllAND(x.To(q), x.To(Px)).
		EqSym().
		eqRewrite(MootForAll(x.AssertVar(), q))
	thms["Q ∧ ∀x.P(x) ⇔ ∀x.(Q ∧ P(x))"] = instantiate(w)

	// ⊢ (∀x.P(x)) ∨ ⊥ ⇔ ∀x.(P(x) ∨ ⊥)
	u := BooleanThms["p ∨ ⊥"](ForAll(x)(Px)).
		EqTrans(
			BooleanThms["p ∨ ⊥"](Px).
				Abs(x.AssertVar()).
				LeftApply(FORALL).
				EqSym())
	// ⊢ (∀x.P(x)) ∨ ⊤ ⇔ ∀x.(P(x) ∨ ⊤)
	v := BooleanThms["p ∨ ⊤"](Px).Abs(x.AssertVar()).
		LeftApply(FORALL).
		EqTrans(MootForAll(x.AssertVar(), T)).
		EqSym()
	v = BooleanThms["p ∨ ⊤"](ForAll(x)(Px)).EqTrans(v)
	// ⊢ (∀x.P(x)) ∨ Q ⇔ ∀x.(P(x) ∨ Q)
	w = BoolInduct(
		q.To(ForAll(x)(Px).Or(q).Eq(ForAll(x)(Px.Or(q))))).
		DeriveHypFrom(u).
		DeriveHypFrom(v)
	thms["(∀x.P(x)) ∨ Q ⇔ ∀x.(P(x) ∨ Q)"] = instantiate(w)

	// ⊢ ⊥ ∨ ∀x.P(x) ⇔ ∀x.(⊥ ∨ P(x))
	u = BooleanThms["⊥ ∨ p"](ForAll(x)(Px)).
		EqTrans(
			BooleanThms["⊥ ∨ p"](Px).
				Abs(x.AssertVar()).
				LeftApply(FORALL).
				EqSym())

	// ⊢ ⊤ ∨ ∀x.P(x) = ∀x.(⊤ ∨ P(x))
	v = BooleanThms["⊤ ∨ p"](Px).Abs(x.AssertVar()).
		LeftApply(FORALL).
		EqTrans(MootForAll(x.AssertVar(), T)).
		EqSym()
	v = BooleanThms["⊤ ∨ p"](ForAll(x)(Px)).EqTrans(v)

	// ⊢ Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))
	w = BoolInduct(
		q.To(q.Or(ForAll(x)(Px)).Eq(ForAll(x)(q.Or(Px))))).
		DeriveHypFrom(u).
		DeriveHypFrom(v)
	thms["Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))"] = instantiate(w)

	w = thms["(∀x.P(x)) ∨ Q ⇔ ∀x.(P(x) ∨ Q)"](x.To(Not(Px)), Not(q)).
		LeftApply(NOT).
		Rewrite(DeepNegRewrite)
	thms["(∃x.P(x)) ∧ Q ⇔ ∃x.(P(x) ∧ Q)"] = instantiate(w)

	w = thms["Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))"](x.To(Not(Px)), Not(q)).
		LeftApply(NOT).
		Rewrite(DeepNegRewrite)
	thms["Q ∧ ∃x.P(x) ⇔ ∃x.(Q ∧ P(x))"] = instantiate(w)

	w = ExistsOR(x.To(Px), x.To(q)).
		EqSym().
		eqRewrite(MootExists(x.AssertVar(), q))
	thms["(∃x.P(x)) ∨ Q ⇔ ∃x.(P(x) ∨ Q)"] = instantiate(w)

	w = ExistsOR(x.To(q), x.To(Px)).
		EqSym().
		eqRewrite(MootExists(x.AssertVar(), q))
	thms["Q ∨ ∃x.P(x) ⇔ ∃x.(Q ∨ P(x))"] = instantiate(w)

	// ⊢ (∀x.P(x)) ⇒ Q ⇔ ∃x.(P(x) ⇒ Q)
	w = thms["(∃x.P(x)) ∨ Q ⇔ ∃x.(P(x) ∨ Q)"](x.To(Not(Px)), q).
		eqRewrite(
			BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](Px, q).EqSym().Abs(x).LeftApply(exists)).
		eqRewrite(NegForAll(x.To(Px)).EqSym()).
		eqRewrite(
			BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](ForAll(x)(Px), q).EqSym())
	thms["(∀x.P(x)) ⇒ Q ⇔ ∃x.(P(x) ⇒ Q)"] = instantiate(w)

	// ⊢ Q ⇒ ∀x.P(x) ⇔ ∀x.(Q ⇒ P(x))
	w = thms["Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))"](x.To(Px), Not(q)).
		eqRewrite(
			BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](q, Px).EqSym().Abs(x).LeftApply(forall)).
		eqRewrite(
			BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](q, ForAll(x)(Px)).EqSym())
	thms["Q ⇒ ∀x.P(x) ⇔ ∀x.(Q ⇒ P(x))"] = instantiate(w)

	// ⊢ (∃x.P(x)) ⇒ Q ⇔ ∀x.(P(x) ⇒ Q)
	w = thms["(∀x.P(x)) ∨ Q ⇔ ∀x.(P(x) ∨ Q)"](x.To(Not(Px)), q).
		eqRewrite(
			BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](Px, q).EqSym().Abs(x).LeftApply(forall)).
		eqRewrite(NegExists(x.To(Px)).EqSym()).
		eqRewrite(BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](Exists(x)(Px), q).EqSym())
	thms["(∃x.P(x)) ⇒ Q ⇔ ∀x.(P(x) ⇒ Q)"] = instantiate(w)

	// ⊢ Q ⇒ ∃x.P(x) ⇔ ∃x.(Q ⇒ P(x))
	w = thms["Q ∨ ∃x.P(x) ⇔ ∃x.(Q ∨ P(x))"](x.To(Px), Not(q)).
		eqRewrite(
			BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](q, Px).EqSym().Abs(x).LeftApply(exists)).
		eqRewrite(BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](q, Exists(x)(Px)).EqSym())
	thms["Q ⇒ ∃x.P(x) ⇔ ∃x.(Q ⇒ P(x))"] = instantiate(w)

	return thms
}

// x, s, λx.P(x)
// ⊢ P(s) ⇔ ∀x.((x = s) ⇒ P(x))
func forAllDenoteProof() func(VarTerm, Term, Term) *PropWrapper {
	x, y := initVars.x, initVars.y
	Px := initVars.P.Apply(x)
	eq := x.Eq(y)

	u := InstForAll(ForAll(x)(eq.Imply(Px)), y).
		DemoteHyp().
		DeriveHypFrom(Refl(y))

	v := EqRewrite(Assume(eq))(Px).
		RightAssume().
		PromoteHyp(eq).
		ConclForAll(x.AssertVar())

	w := u.Deduct(v)
	return instDenote(w)
}

// x, s, λx.P(x)
// ⊢ P(s) ⇔ ∃x.((x = s) ∧ P(x))
func existsDenoteProof() func(VarTerm, Term, Term) *PropWrapper {
	x, y := initVars.x, initVars.y
	Px, Py := initVars.P.Apply(x), initVars.P.Apply(y)
	eq := x.Eq(y)

	u := InstExists(Exists(x)(eq.And(Px)), y).
		DeriveHypFrom(ConclAND(y.Eq(y), Py)).
		DeriveHypFrom(Refl(y))

	v := EqRewrite(Assume(eq))(Px).
		LeftAssume().
		DeriveHypFrom(HypAND0(eq, Px)).
		DeriveHypFrom(HypAND1(eq, Px)).
		HypExists(x.AssertVar(), eq.And(Px))

	w := v.Deduct(u)
	return instDenote(w)
}

// f, λx.λz.R(x, z):
// ⊢ ∀x.∃z.R(x, z) ⇔ ∃f.∀x.R(x, f(x))
func skolemProof() func(VarTerm, Term) *PropWrapper {
	x, z, f, R := initVars.x, initVars.z, initVars.f, initVars.R

	// R(x, f(x)) ⊢ ∃z.R(x, z)
	u := InstExists(Exists(z)(R.Apply(x, z)), f.Apply(x)).
		// ∀x.R(x, f(x)) ⊢ ∃z.R(x, z)
		HypForAllInst(x.AssertVar(), R.Apply(x, f.Apply(x))).
		// ∃f.∀x.R(x, f(x)) ⊢ ∃z.R(x, z)
		HypExists(f.AssertVar(), ForAll(x)(R.Apply(x, f.Apply(x)))).
		// ∃f.∀x.R(x, f(x)) ⊢ ∀x.∃z.R(x, z)
		ConclForAll(x.AssertVar())

	s, _ := Exists(z)(R.Apply(x, z)).AsAppliedTerm()

	v := ExpandDef(s.Fun().(ConstTerm), s.Arg()).
		RewriteConcl(DeepBetaAbs(s.Arg().(AbsTerm))).
		LeftAssume(). // ∃z.R(x, z) ⊢ R(x, εz.R(x, z))
		HypForAllInst(x.AssertVar(), s).
		ConclForAll(x.AssertVar()) // ∀x.∃z.R(x, z) ⊢ ∀x.R(x, εz.R(x, z))

	v = InstExists(
		Exists(f)(ForAll(x)(R.Apply(x, f.Apply(x)))), x.To(z.SuchThat(R.Apply(x, z)))).
		Rewrite(DeepBeta).
		DeriveHypFrom(v) // ∀x.∃z.R(x, z) ⊢ ∃f.∀x.R(x, f(x))

	// ⊢ ∀x.∃z.R(x, z) = ∃f.∀x.R(x, f(x))
	w := u.Deduct(v)
	return instSkolem(w)
}

// λx.P(x):
// ⊢ ∃!x.P(x) ⇔ ∃x.P(x) ∧ ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x = y))
func altUniqueProof() func(Term) *PropWrapper {
	x, y := initVars.x, initVars.y
	Px, Py := initVars.P.Apply(x), initVars.P.Apply(y)

	// ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x = y))
	S0 := ForAll(x, y)(Px.And(Py).Imply(x.Eq(y)))
	// ∀y.(P(y) = (x = y))
	S1 := ForAll(y)(Py.Eq(x.Eq(y)))

	// Give these notations, we need to prove ⊢ ∃x.S1(x) = ∃x.P(x) ∧ S0

	// ∃x.S1(x) ⊢ ∃x.P(x) ∧ S0
	u := Assume(Px.Eq(x.SuchThat(S1).Eq(x))).
		LeftAssume().
		EqSym().
		EqTrans(Assume(Py.Eq(x.SuchThat(S1).Eq(y))).LeftAssume()).
		DeriveHypFrom(HypAND0(Px, Py)).
		DeriveHypFrom(HypAND1(Px, Py)).
		HypForAllInst(y.AssertVar(), Py.Eq(x.SuchThat(S1).Eq(y))).
		HypForAllInst(x.AssertVar(), Px.Eq(x.SuchThat(S1).Eq(x))).
		PromoteHyp(Px.And(Py)).
		ConclForAll(y.AssertVar()).
		ConclForAll(x.AssertVar()).
		DeriveTrans(ConclAND(Exists(x)(Px), S0)).
		DeriveHypFrom(InstExists(Exists(x)(Px), x.SuchThat(S1))).
		DeriveHypFrom(InstForAll(ForAll(y)(Py.Eq(x.SuchThat(S1).Eq(y))), x.SuchThat(S1)).
			EqSym().
			EqMP(Refl(x.SuchThat(S1)))).
		DeriveHypFrom(SelectExists(x.To(S1)))

	v := InstForAll(ForAll(x, y)(Px.And(Py).Imply(x.Eq(y))), x.SuchThat(Px)).
		eqRewrite(SelectExists(x.To(Px)).Deduct(DerivesTrue)).
		RewriteConcl(DeepBoolRewrite).
		ConclForAllInst(y).
		DemoteHyp(). // ∃x.P(x), S0, P(y) ⊢ εx.P(x) = y
		Deduct(SelectExists(x.To(Px)).eqReplacementConcl(Assume(x.SuchThat(Px).Eq(y)))).
		EqSym(). // ∃x.P(x), S0 ⊢ P(y) ⇔ (εx.P(x) = y)
		ConclForAll(y.AssertVar()).
		DeriveTrans(InstExists(Exists(x)(S1), x.SuchThat(Px))). // ∃x.P(x), S0 ⊢ ∃x.S1(x)
		DeriveHypFrom(HypAND0(Exists(x)(Px), S0)).
		DeriveHypFrom(HypAND1(Exists(x)(Px), S0)) // ∃x.P(x) ∧ S0 ⊢ ∃x.S1(x)

	// ∃!x.P(x) ⇔ ∃x.P(x) ∧ S0
	w := ExpandDef(
		core.MakeConstTerm(
			UNIQUE.Meta(),
			MakeFun(x.To(Px).Type(), TypeBool)), x.To(Px)).
		Rewrite(DeepBetaAbs(x.To(Px).Core().(AbsTerm))).
		EqTrans(v.Deduct(u))

	return instUnique(w)
}

// Returns the thm macro for a thm on ∃!x.P(x) stated over the init
// variables x, y and P: the macro instantiates it at a predicate term
// λx.P(x), with the bound y renamed apart from the predicate's binder.
func instUnique(w *PropWrapper) func(Term) *PropWrapper {
	return func(t Term) *PropWrapper {
		_t, ok := t.AsAbsTerm()
		Assert(ok && IsBool(_t.Body()))
		return w.
			TypeInst(MakeTypeSubst(TypeA, _t.Var().Type())).
			RewriteConcl(rewriteInitVar(initVars.y, _t.Var().Rename())).
			RewriteConcl(rewriteInitVar(initVars.x, _t.Var())).
			TermInst(makeTermSubstWithType(initVars.P, _t)).
			Rewrite(DeepBetaAbs(_t))
	}
}

// λx.P(x):
// ⊢ ∃!x.P(x) ⇔ ∃x.(P(x) ∧ ∀y.(P(y) ⇒ (y = x)))
func witnessUniqueProof() func(Term) *PropWrapper {
	x, y, P := initVars.x, initVars.y, initVars.P
	Px, Py := P.Apply(x), P.Apply(y)

	// ⊢ ∃!x.P(x) ⇔ ∃x.P(x) ∧ S0
	alt := AltUnique(x.To(Px))
	// ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x = y))
	S0 := ForAll(x, y)(Px.And(Py).Imply(x.Eq(y)))
	// C(x) := P(x) ∧ ∀y.(P(y) ⇒ (y = x))
	Cx := Px.And(ForAll(y)(Py.Imply(y.Eq(x))))

	// ∃x.C(x) ⊢ ∃!x.P(x): the witness is e := εx.C(x); two things P holds
	// of both equal e, so they are equal, and P(e) gives the existence.
	e := x.SuchThat(Cx)
	Pe := P.Apply(e)
	onlyE := ForAll(y)(Py.Imply(y.Eq(e)))
	u := Assume(Px.Imply(x.Eq(e))).
		DemoteHyp(). // P(x) ⇒ x = e, P(x) ⊢ x = e
		EqTrans(Assume(Py.Imply(y.Eq(e))).DemoteHyp().EqSym()).
		DeriveHypFrom(HypAND0(Px, Py)).
		DeriveHypFrom(HypAND1(Px, Py)).
		HypForAllInst(y.AssertVar(), Py.Imply(y.Eq(e))).
		HypForAllInst(x.AssertVar(), Px.Imply(x.Eq(e))). // α-equal to the one above: one hypothesis
		PromoteHyp(Px.And(Py)).
		ConclForAll(y.AssertVar()).
		ConclForAll(x.AssertVar()). // ∀y.(P(y) ⇒ y = e) ⊢ S0
		DeriveTrans(ConclAND(Exists(x)(Px), S0)).
		DeriveHypFrom(InstExists(Exists(x)(Px), e)) // ∀y.(P(y) ⇒ y = e), P(e) ⊢ ∃x.P(x) ∧ S0
	u = alt.EqSym().
		EqMP(u).
		DeriveHypFrom(HypAND0(Pe, onlyE)).
		DeriveHypFrom(HypAND1(Pe, onlyE)).
		DeriveHypFrom(SelectExists(x.To(Cx))) // ∃x.C(x) ⊢ ∃!x.P(x)

	// ∃!x.P(x) ⊢ ∃x.C(x): the witness is d := εx.P(x); S0 at d and y
	// sends each y that P holds of to d.
	d := x.SuchThat(Px)
	Pd := P.Apply(d)
	onlyD := ForAll(y)(Py.Imply(y.Eq(d)))
	v := InstForAll(S0, d).
		ConclForAllInst(y).
		DemoteHyp(). // S0, P(d) ∧ P(y) ⊢ d = y
		EqSym().
		DeriveHypFrom(ConclAND(Pd, Py)).
		PromoteHyp(Py).
		ConclForAll(y.AssertVar()). // S0, P(d) ⊢ ∀y.(P(y) ⇒ y = d)
		DeriveTrans(ConclAND(Pd, onlyD)).
		DeriveTrans(InstExists(Exists(x)(Cx), d)). // S0, P(d) ⊢ ∃x.C(x)
		DeriveHypFrom(SelectExists(x.To(Px))).
		DeriveHypFrom(HypAND0(Exists(x)(Px), S0)).
		DeriveHypFrom(HypAND1(Exists(x)(Px), S0)).
		DeriveHypFrom(alt.EqMP(Assume(Lhs(alt)))) // ∃!x.P(x) ⊢ ∃x.C(x)

	// ⊢ ∃!x.P(x) ⇔ ∃x.C(x)
	w := u.Deduct(v)

	return instUnique(w)
}

// f, λx.λz.R(x, z):
// ⊢ ∀x.∃!z.R(x, z) ⇔ ∃f.∀x.∀z.(R(x, z) ⇔ (f(x) = z))
func skolemUniqueProof() func(VarTerm, Term) *PropWrapper {
	x, z, f, R := initVars.x, initVars.z, initVars.f, initVars.R
	y := Var("y", TypeB)

	zRxz := z.To(R.Apply(x, z)).Core().(AbsTerm)
	w := ExpandDef(
		core.MakeConstTerm(
			UNIQUE.Meta(),
			MakeFun(zRxz.Type(), TypeBool)), zRxz).
		Rewrite(DeepBetaAbs(zRxz)).
		Abs(x.AssertVar()).
		LeftApply(FORALL).
		EqTrans(Skolem(f.AssertVar(),
			x.To(y.To(ForAll(z)(R.Apply(x, z).Eq(y.Eq(z)))))))
	return instSkolem(w)
}

// f, λx.λz.R(x, z):
// ⊢ ∀x.∃!z.R(x, z) ⇔ ∃!f.∀x.R(x, f(x))
func skolemAltUniqueProof() func(VarTerm, Term) *PropWrapper {
	x, z, f, R := initVars.x, initVars.z, initVars.f, initVars.R
	g := WrapTerm(f.AssertVar().Rename())

	Rf, Rg := R.Apply(x, f.Apply(x)), R.Apply(x, g.Apply(x))

	// ∃f.(∀x.R(x, f(x)))
	S0 := Exists(f)(ForAll(x)(Rf))
	// ∀f.∀g.(((∀x.R(x, f(x))) ∧ (∀x.R(x, g(x)))) ⇒ (f = g))
	S1 := ForAll(f, g)(ForAll(x)((Rf)).And(ForAll(x)((Rg))).Imply(f.Eq(g)))
	// ∃f.∀x.∀z.(R(x, z) ⇔ (f(x) = z))
	S2 := Exists(f)(ForAll(x, z)(R.Apply(x, z).Eq(f.Apply(x).Eq(z))))

	// First we prove ∀x.∃!z.R(x, z) ⊢ ∃!f.∀x.R(x, f(x)).

	// ∀x.∃!z.R(x, z) ⊢ S0 ∧ ∀x.∀z.∀zʹ.((R(x, z) ∧ R(x, zʹ)) ⇒ (z = zʹ))
	u0 := AltUnique(z.To(R.Apply(x, z))).
		Abs(x.AssertVar()).
		LeftApply(FORALL).
		RewriteConclRhs(ForAllANDRewrite).
		eqRewrite(Skolem(f.AssertVar(), x.To(z.To(R.Apply(x, z))))).
		LeftAssume()

	zp := z.AssertVar().Rename()
	// ∀z.∀zʹ.((R(x, z) ∧ R(x, zʹ)) ⇒ (z = zʹ))
	RUnique := ForAll(z, zp)(R.Apply(x, z).And(R.Apply(x, zp)).Imply(z.Eq(zp)))
	u := InstForAll(RUnique, f.Apply(x)).
		ConclForAllInst(g.Apply(x)).
		PromoteHyp(RUnique).
		ConclForAll(x.AssertVar()).
		DeriveTrans(ForAllIMPLY(
			x.To(RUnique),
			x.To(Rf.And(Rg).Imply(f.Apply(x).Eq(g.Apply(x)))))).
		DeriveTrans(ForAllIMPLY(
			x.To(Rf.And(Rg)),
			x.To(f.Apply(x).Eq(g.Apply(x))))).
		DeriveTrans(FunEq(x.To(f.Apply(x)), x.To(g.Apply(x))).RightAssume()).
		RewriteConcl(DeepRewrite(etaRewrite)).
		eqRewrite(ForAllAND(x.To(Rf), x.To(Rg))).
		PromoteHyp(ForAll(x)(Rf).And(ForAll(x)(Rg))).
		ConclForAll(g.AssertVar()).
		ConclForAll(f.AssertVar()). // ∀x.∀z.∀zʹ.((R(x, z) ∧ R(x, zʹ)) ⇒ (z = zʹ)) ⊢ S1
		DeriveTrans(ConclAND(S0, S1)).
		DeriveHypFrom(HypAND0(S0, ForAll(x)(RUnique))).
		DeriveHypFrom(HypAND1(S0, ForAll(x)(RUnique))).
		DeriveHypFrom(u0) // ∀x.∃!z.R(x, z) ⊢ S0 ∧ S1

	// ⊢ ∃!f.∀x.R(x, f(x)) ⇔ S0 ∧ S1
	fUnique := AltUnique(f.To(ForAll(x)(Rf)))

	// ∀x.∃!z.R(x, z) ⊢ ∃!f.∀x.R(x, f(x))
	u = fUnique.EqSym().EqMP(u)

	// Prove the other side ∃!f.∀x.R(x, f(x)) ⊢ ∀x.∃!z.R(x, z).

	// Take f0 such that ∀x.R(x, f(x))
	// ∃f.(∀x.R(x, f(x))) ⊢ ∀x.R(x, f0(x))
	f0 := Var("f0", f.Type())
	f0Satisfies := Assume(S0).ConclSelectExists(f0.AssertVar())

	// Assuming ¬S2,
	// take x0 and z0 such that ¬R(x0, z0) = (f0(x0) = z0)
	x0, z0 := Var("x0", x.Type()), Var("z0", z.Type())
	x0z0Satisfy := DeepRewrite(PushNegRewrite)(Not(S2)).
		LeftAssume().
		ConclForAllInst(f0).
		ConclSelectExists(x0.AssertVar()).
		ConclSelectExists(z0.AssertVar())

	// ¬(∃f.∀x.∀z.(R(x, z) ⇔ (f(x) = z))), ∃f.∀x.R(x, f(x)) ⊢ f0(x0) ≠ z0
	v0 := x0z0Satisfy.
		EqSym().
		eqReplacementConcl(Assume(f0.Apply(x0).Eq(z0)).EqSym()).
		RewriteConcl(DeepBoolRewrite).
		DeriveTrans(Contradict(R.Apply(x0, f0.Apply(x0)))).
		DeriveHypFrom(f0Satisfies.ConclForAllInst(x0)).
		NegHyp(f0.Apply(x0).Eq(z0))

	// Define g0(x) as "if x = x0 then z0 else f0(x)"
	g0 := z.SuchThat(
		x.Eq(x0).Imply(z.Eq(z0)).
			And(x.Neq(x0).Imply(z.Eq(f0.Apply(x)))))

	// Discuss by cases.
	// x = x0, S0, ¬S2 ⊢ R(x, g0(x))
	v1 := EqRewrite(Assume(x.Eq(x0)))(R.Apply(x, g0)).
		RewriteConcl(DeepBoolRewrite).
		RewriteConcl(DeepRewrite(hilbertRewrite)).
		RightAssume().
		DeriveHypFrom(x0z0Satisfy.
			EqTrans(EqualsFalse(f0.Apply(x0).Eq(z0)).RightAssume()).
			RewriteConcl(BoolRewrite).
			RewriteConcl(DoubleNegRewrite)).
		DeriveHypFrom(v0)
	// x ≠ x0, S0, ¬S2 ⊢ R(x, g0(x))
	v2 := EqRewrite(EqualsFalse(x.Eq(x0)).RightAssume())(R.Apply(x, g0)).
		RewriteConcl(DeepBoolRewrite).
		RewriteConcl(DeepRewrite(hilbertRewrite)).
		RightAssume().
		DeriveHypFrom(f0Satisfies.ConclForAllInst(x))

	// ¬(∃f.∀x.∀z.(R(x, z) ⇔ (f(x) = z))), ∃f.∀x.R(x, f(x)) ⊢ ∀x.R(x, g0(x))
	v3 := ByCases(R.Apply(x, g0), x.Eq(x0), x.Neq(x0)).
		DeriveHypFrom(ExcludedMiddle(x.Eq(x0))).
		DeriveHypFrom(v1.PromoteHyp(x.Eq(x0))).
		DeriveHypFrom(v2.PromoteHyp(x.Neq(x0))).
		ConclForAll(x.AssertVar())

	// Put together
	v := InstForAll(S1, f0).
		eqRewrite(f0Satisfies.Deduct(DerivesTrue)).
		RewriteConcl(DeepBoolRewrite).
		ConclForAllInst(x.To(g0)).
		RewriteConcl(DeepBetaAbs(x.To(g0).Core().(AbsTerm))).
		DemoteHyp().
		DeriveHypFrom(v3). // S0, S1, ¬S2 ⊢ f0 = g0
		RightApply(x0).
		RewriteConclRhs(betaRewrite).
		RewriteConclRhs(DeepBoolRewrite).
		RewriteConclRhs(hilbertRewrite). // S0, S1, ¬S2 ⊢ f0(x0) = z0
		DeriveTrans(Contradict(f0.Apply(x0).Eq(z0))).
		DeriveHypFrom(v0). // S0, S1, ¬S2 ⊢ ⊥
		NegHyp(Not(S2)).
		RewriteConcl(DoubleNegRewrite). // S0, S1 ⊢ S2
		RemoveVarHyp(z0.AssertVar()).
		RemoveVarHyp(x0.AssertVar()).
		RemoveVarHyp(f0.AssertVar()).
		DeriveHypFrom(HypAND0(S0, S1)).
		DeriveHypFrom(HypAND1(S0, S1)).     // S0 ∧ S1 ⊢ S2
		DeriveHypFrom(fUnique.LeftAssume()) // ∃!f.∀x.R(x, f(x)) ⊢ S2

	// ∃!f.∀x.R(x, f(x)) ⊢ ∀x.∃!z.R(x, z)
	v = SkolemUnique(f.AssertVar(), x.To(z.To(R.Apply(x, z)))).EqSym().EqMP(v)

	// ⊢ ∀x.∃!z.R(x, z) ⇔ ∃!f.∀x.R(x, f(x))
	w := v.Deduct(u)
	return instSkolem(w)
}

func (t *PropWrapper) instVar(v VarTerm) func(Term) *PropWrapper {
	return func(s Term) *PropWrapper { return t.TermInst(MakeTermSubst(v, s)) }
}

func (t *PropWrapper) inst2Vars(v0, v1 VarTerm) func(Term, Term) *PropWrapper {
	return func(s0, s1 Term) *PropWrapper {
		return t.TermInst(
			MakeTermSubst(v0, s0),
			MakeTermSubst(v1, s1))
	}
}

func (t *PropWrapper) inst3Vars(
	v0, v1, v2 VarTerm) func(Term, Term, Term) *PropWrapper {
	return func(s0, s1, s2 Term) *PropWrapper {
		return t.TermInst(
			MakeTermSubst(v0, s0),
			MakeTermSubst(v1, s1),
			MakeTermSubst(v2, s2))
	}
}

// ⊢ ∀(P) ⇔ (P = (λx.⊤))
var expandFORALL = ExpandDef(FORALL, initVars.P)

// ⊢ ∃(P) ⇔ P(εP)
var expandEXISTS = ExpandDef(EXISTS, initVars.P)

func rewriteInitVar(initVar *ext.TermWrapper, v VarTerm) Rewrite {
	if initVar.Equals(v) {
		return NilRewrite
	}
	return BoundVarRewrite(core.Var(initVar.AssertVar().Name(), v.Type()), v)
}

func makeTermSubstWithType(v *ext.TermWrapper, t Term) TermSubst {
	if v.Type().Equals(t.Type()) {
		return MakeTermSubst(v, t)
	}
	return MakeTermSubst(Var(v.AssertVar().Name(), t.Type()), t)
}

// Returns thm macro for the input thm such as
// ⊢ ∀x.(P(x) ∧ Q(x)) = (∀x.P(x) ∧ ∀x.Q(x))
// The macro turns 2 predicate terms λx.P(x), λx.Q(x) to a thm.
// The abstracted vars of the 2 terms should be aligned.
func instPredicates(w *PropWrapper) func(Term, Term) *PropWrapper {
	return func(s, t Term) *PropWrapper {
		_s, ok0 := s.AsAbsTerm()
		_t, ok1 := t.AsAbsTerm()
		sDeepBetaAbs, tDeepBetaAbs := DeepBetaAbs(_s), DeepBetaAbs(_t)
		Assert(ok0 && ok1 &&
			_s.Var().Equals(_t.Var()) &&
			IsBool(_s.Body()) && IsBool(_t.Body()))
		wInst := w.
			TypeInst(MakeTypeSubst(TypeA, _s.Var().Type())).
			RewriteConcl(rewriteInitVar(initVars.x, _s.Var()))
		if sDeepBetaAbs(_t) != nil {
			Q := core.Var(initVars.Q.AssertVar().Name(), _t.Type())
			for _s.HasFreeName(Q.Name()) {
				Q = Q.Rename()
			}
			return wInst.
				TermInst(
					makeTermSubstWithType(initVars.P, _s),
					makeTermSubstWithType(initVars.Q, Q)).
				Rewrite(sDeepBetaAbs).
				TermInst(MakeTermSubst(Q, _t)).
				Rewrite(tDeepBetaAbs)
		} else if tDeepBetaAbs(_s) != nil {
			P := core.Var(initVars.P.AssertVar().Name(), _s.Type())
			for _t.HasFreeName(P.Name()) {
				P = P.Rename()
			}
			return wInst.
				TermInst(
					makeTermSubstWithType(initVars.P, P),
					makeTermSubstWithType(initVars.Q, _t)).
				Rewrite(tDeepBetaAbs).
				TermInst(MakeTermSubst(P, _s)).
				Rewrite(sDeepBetaAbs)
		}
		return wInst.
			TermInst(
				makeTermSubstWithType(initVars.P, _s),
				makeTermSubstWithType(initVars.Q, _t)).
			Rewrite(DeepBetaAbs(_s)).
			Rewrite(DeepBetaAbs(_t))
	}
}

// Returns thm macro for denote thms such as
// ⊢ P(s) ⇔ ∀x.((x = s) ⇒ P(x))
// ⊢ P(s) ⇔ ∃x.((x = s) ∧ P(x))
// The macro turns x, s, λx.P(x) to a thm.
func instDenote(w *PropWrapper) func(VarTerm, Term, Term) *PropWrapper {
	return func(x VarTerm, s, t Term) *PropWrapper {
		abs, ok := t.AsAbsTerm()
		Assert(ok &&
			x.Type().Equals(s.Type()) &&
			x.Type().Equals(abs.Var().Type()))

		return w.
			TypeInst(MakeTypeSubst(TypeA, x.Type())).
			RewriteConcl(rewriteInitVar(initVars.x, abs.Var())).
			TermInst(
				makeTermSubstWithType(initVars.x, x),
				makeTermSubstWithType(initVars.y, s),
				makeTermSubstWithType(initVars.P, abs)).
			RewriteConcl(DeepBetaAbs(abs))
	}
}

// Returns thm macro for skolem thms
// ⊢ ∀x.∃z.R(x, z) ⇔ ∃f.∀x.R(x, f(x))
// ⊢ ∀x.∃!z.R(x, z) ⇔ ∃f.∀x.∀z.(R(x, z) ⇔ (f(x) = z))
// ⊢ ∀x.∃!z.R(x, z) ⇔ ∃!f.∀x.R(x, f(x))
func instSkolem(w *PropWrapper) func(VarTerm, Term) *PropWrapper {
	return func(f VarTerm, t Term) *PropWrapper {
		t0, ok0 := t.AsAbsTerm()
		t1, ok1 := t0.Body().AsAbsTerm()
		fType, ok := f.Type().(CompositeType)
		Assert(ok0 && ok1 && ok && IsBool(t1.Body()) &&
			fType.Meta().Equals(core.MetaTypeFun()) &&
			fType.SubType(0).Equals(t0.Var().Type()) &&
			fType.SubType(1).Equals(t1.Var().Type()))
		// The final deep β step may change the body as well,
		// as there is no simple way to control exactly what beta
		// is needed.
		// So to prevent potential bug we request the body to be
		// β-collapse free.
		Assert(ext.BetaCollapse(context.Background(), t1).AlphaEquals(t1))
		x, z := t0.Var(), t1.Var()
		return w.
			TypeInst(
				MakeTypeSubst(TypeA, x.Type()),
				MakeTypeSubst(TypeB, z.Type())).
			RewriteConcl(rewriteInitVar(initVars.f, f)).
			RewriteConcl(rewriteInitVar(initVars.z, z)).
			RewriteConcl(rewriteInitVar(initVars.x, x)).
			TermInst(makeTermSubstWithType(initVars.R, t0)).
			RewriteConcl(DeepBeta)
	}
}
