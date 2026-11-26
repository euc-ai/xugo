package prop

import (
	"context"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// Rewrite a term using all possible β.
func betaRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if t, ok := t.AsAppliedTerm(); ok {
			if abs, ok := t.Fun().AsAbsTerm(); ok {
				if abs.Var().Equals(t.Arg()) {
					return Beta(t)
				}
				return Beta(Apply(abs, abs.Var())).
					TermInst(MakeTermSubst(abs.Var(), t.Arg()))
			}
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// Rewrite a term using β of the input abs term.
func betaAbsRewriteImpl(abs AbsTerm) Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if t, ok := t.AsAppliedTerm(); ok && t.Fun().AlphaEquals(abs) {
			abs := t.Fun().(AbsTerm)
			if abs.Var().Equals(t.Arg()) {
				return Beta(t)
			}
			return Beta(Apply(abs, abs.Var())).
				TermInst(MakeTermSubst(abs.Var(), t.Arg()))
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

func etaRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if body := etaRedex(t); !body.IsZero() {
			return Eta(body)
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// etaRedex returns the body g(x) of an η-redex λx.g(x) (x not free in
// g), and nil for any other term.
func etaRedex(t Term) AppliedTerm {
	abs, ok := t.AsAbsTerm()
	if !ok {
		return AppliedTerm{}
	}
	body, ok := abs.Body().AsAppliedTerm()
	if !ok || !abs.Var().Equals(body.Arg()) || body.Fun().HasFree(abs.Var()) {
		return AppliedTerm{}
	}
	return body
}

// η-reduction where the normal form is η-short. An η-redex λx.g(x)
// reduces to g when it is the argument of an application or the body
// of an abstraction. The rule fires at the parent of the λ because the
// direction of η is a property of the context, which a shallow rewrite
// of the λ itself cannot see: under ∀ / ∃ / ∃! / ε the normal form is
// the EXPANDED λ (QuantifierRewrite and hilbertRewrite turn ∀P into
// ∀x.P(x)), and at a function-typed `=` FunEqRewrite expands both
// sides towards ∀x.(l(x) = r(x)). Those heads are excluded; an
// unguarded η would ping-pong with each of them. A λ in function
// position is a β-redex, which betaRewrite takes. A λ at the root of
// the term has no context and is left alone.
func etaContextRewriteImpl() Rewrite {
	expandsItsArgument := func(f Term) bool {
		for {
			app, ok := f.AsAppliedTerm()
			if !ok {
				break
			}
			f = app.Fun()
		}
		c, ok := f.AsConst()
		if !ok {
			return false
		}
		m := c.Meta()
		return m.Equals(FORALL.Meta()) || m.Equals(EXISTS.Meta()) || m.Equals(UNIQUE.Meta()) ||
			m.Equals(core.MetaHilbert()) || m.Equals(core.MetaEq())
	}
	rewrite := func(t Term) *PropWrapper {
		switch t := t.Core().(type) {
		case AppliedTerm:
			if expandsItsArgument(t.Fun()) {
				return nil
			}
			if body := etaRedex(t.Arg()); !body.IsZero() {
				return Eta(body).LeftApply(t.Fun())
			}
		case AbsTerm:
			if body := etaRedex(t.Body()); !body.IsZero() {
				return Eta(body).Abs(t.Var())
			}
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// P(⊤) ⊕ P(⊥) ⊢ (εx.P(x)) ⇔ P(⊤)
func hilbertBoolProof(P *ext.TermWrapper) *PropWrapper {
	x := Var("x", TypeBool)
	Px, PT, PF := P.Apply(x), P.Apply(T), P.Apply(F)
	hilbert, e := x.SuchThat(Px), Exists(x)(Px)
	// P(⊤) ⊕ P(⊥) ⊢ P(⊥) ⇔ ¬P(⊤)
	assumption := Assume(PT.Xor(PF)).
		RewriteConcl(PushNegRewrite).
		EqSym()

	// P(⊤) ⊕ P(⊥) ⊢ P(εx.P(x))
	w := SelectExists(x.To(Px)).
		DeriveHypFrom(ByCases(e, PT, PF)).
		DeriveHypFrom(InstExists(e, T).PromoteHyp(PT)).
		DeriveHypFrom(InstExists(e, F).PromoteHyp(PF)).
		eqRewrite(assumption).
		Rewrite(BoolRewrite).
		DeriveHypFrom(DerivesTrue)

	// εx.P(x), P(⊤) ⊕ P(⊥) ⊢ (εx.P(x)) ⇔ P(⊤)
	uT := w.
		RewriteConcl(EqRewrite(Assume(hilbert).Deduct(DerivesTrue)))
	uT = Assume(hilbert).Deduct(uT)

	// ¬(εx.P(x)), P(⊤) ⊕ P(⊥) ⊢ (εx.P(x)) ⇔ P(⊤)
	uF := w.
		RewriteConcl(EqRewrite(EqualsFalse(hilbert).RightAssume()))
	uF = Assume(Not(hilbert)).
		Deduct(assumption.EqMP(uF)).
		RewriteConcl(BoolRewrite)

	return ByCases(hilbert.Eq(PT), hilbert, Not(hilbert)).
		DeriveHypFrom(ExcludedMiddle(hilbert)).
		DeriveHypFrom(uT.PromoteHyp(hilbert)).
		DeriveHypFrom(uF.PromoteHyp(Not(hilbert)))

}

func hilbertRewriteImpl() Rewrite {
	simplify := DeepRewrite(
		betaRewrite,
		BoolRewrite,
		DoubleNegRewrite,
		PushNegRewrite,
		QuantifierRewrite)
	simplifyEq := EqualityFromRewrite(simplify)
	P := Var("P", MakeFun(TypeBool, TypeBool))
	// P(⊤) ⊕ P(⊥) ⊢ (εx.P(x)) ⇔ P(⊤)
	w := hilbertBoolProof(P)

	rewrite := func(t Term) *PropWrapper {
		_t, ok := t.AsAppliedTerm()
		if !ok {
			return nil
		}
		fun, ok := _t.Fun().AsConst()
		if !ok || !fun.Meta().Equals(core.MetaHilbert()) {
			return nil
		}

		arg, ok := _t.Arg().(AbsTerm)
		if !ok {
			x := core.Var(
				utils.X_DOT,
				_t.Arg().Type().(CompositeType).SubType(0)).
				RenameToAvoid(_t.Arg())
			return Eta(Apply(_t.Arg(), x)).
				EqSym().
				LeftApply(_t.Fun())
		}

		v := arg.Var()
		if l, r, ok := MatchesEQ(arg.Body()); ok {
			if l.Equals(v) && !r.HasFree(v) {
				s := Apply(arg, r)
				return betaRewrite(s).
					EqSym().
					EqMP(Refl(r)).
					DeriveTrans(Select(s)).
					RewriteConcl(betaRewrite)
			} else if r.Equals(v) && !l.HasFree(v) {
				s := Apply(arg, l)
				return betaRewrite(s).
					EqSym().
					EqMP(Refl(l)).
					DeriveTrans(Select(s)).
					RewriteConcl(betaRewrite).
					EqSym()
			}
		}

		// For boolean var, if P(⊤) and P(⊥) condradicts,
		// we can rewrite the term εv.P(v) to P(⊤).
		if !IsBool(v) {
			return nil
		}
		s0 := arg.Body().Substitute(MakeTermSubst(v, T))
		s1 := arg.Body().Substitute(MakeTermSubst(v, F))

		if u := simplifyEq(Not(s0), s1); u != nil {
			// ⊢ s0 ⊕ s1
			u = PushNegRewrite(WrapTerm(s0).Xor(s1)).EqSym().EqMP(u)
			return w.
				TermInst(MakeTermSubst(P, arg)).
				Rewrite(DeepBetaAbs(arg)).
				RewriteConclRhs(simplify).
				DeriveHypFrom(u) // ⊢ εv.P(v) ⇔ P(⊤)
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

func hilbertExistsRewriteImpl() Rewrite {
	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		s := ext.HilbertSubTerm(t)
		if s == nil {
			return nil
		}
		vars, body := MatchesAbs(s)
		Assert(body.(AppliedTerm).Fun().(ConstTerm).Meta().
			Equals(core.MetaHilbert()))
		// argument of the application of ε.
		arg := body.(AppliedTerm).Arg()
		Assert(ext.IsFunType(arg.Type()))

		// The term to be rewritten. For example,
		// if s = εx.P(x), then rewriteTerm = P(εx.P(x)).
		rewriteTerm := Term(Apply(arg, body))
		if w := betaRewrite(rewriteTerm); w != nil {
			rewriteTerm = Rhs(w)
		}

		for _, v := range slices.Backward(vars) {
			rewriteTerm = Abs(v, rewriteTerm)
		}

		// The rewrite only works if rewriteTerm is a subterm of t.
		// Most of the time this condition is not satisfied and we return early.
		if !ext.IsSub(rewriteTerm, t) {
			return nil
		}

		vType := arg.Type().(CompositeType).SubType(0)
		u := expandEXISTS.
			TypeInst(MakeTypeSubst(TypeA, vType)).
			TermInst(makeTermSubstWithType(initVars.P, arg)).
			RewriteConclRhs(betaRewrite).
			EqSym()
		for _, v := range slices.Backward(vars) {
			u = u.Abs(v)
		}
		// u is the equality from the term containing ε term
		// to the existential term.
		// e.g. P(εx.P(x)) ⇔ ∃x.P(x)
		Assert(Lhs(u).AlphaEquals(rewriteTerm))
		w := EqRewrite(u)(t)
		Assert(w != nil)
		rhs := Rhs(u)
		for abs, ok := rhs.AsAbsTerm(); ok; abs, ok = rhs.AsAbsTerm() {
			w = w.RewriteConclRhs(DeepBetaAbs(abs))
			rhs = abs.Body()
		}

		// There might be more than one hilbert subterms.
		return w.RewriteConclRhsRecur(rewrite)
	}
	return verifyRewrite(rewrite)
}

func boolRewriteImpl() Rewrite {
	negIffNeg := negIffNegProof()
	rewrite := func(t Term) *PropWrapper {
		if _t := MatchesNOT(t); _t != nil {
			if _t.Equals(F) {
				return NotFalse
			} else if _t.Equals(T) {
				return NotTrue
			}
		}

		// (l = l) → ⊤
		if l, r, ok := MatchesEQ(t); ok && l.AlphaEquals(r) {
			return Refl(l).Deduct(DerivesTrue)
		}

		if l, r, ok := MatchesIFF(t); ok {
			// (l = l) → ⊤ has been handled above.

			// (l ⇔ ⊤) → l
			if r.Equals(T) {
				return BooleanThms["p ⇔ ⊤"](l)
			}
			// (l ⇔ ⊥) → ¬l
			if r.Equals(F) {
				return BooleanThms["p ⇔ ⊥"](l)
			}
			// (⊤ ⇔ r) → r
			if l.Equals(T) {
				return BooleanThms["⊤ ⇔ p"](r)
			}
			// (⊥ ⇔ r) → ¬r
			if l.Equals(F) {
				return BooleanThms["⊥ ⇔ p"](r)
			}
			_l, _r := MatchesNOT(l), MatchesNOT(r)
			// (l ⇔ ¬l) → ⊥
			if _r != nil && l.AlphaEquals(_r) {
				return BooleanThms["p ⇔ ¬p"](l)
			}
			// (¬r ⇔ r) → ⊥
			if _l != nil && r.AlphaEquals(_l) {
				return BooleanThms["¬p ⇔ p"](r)
			}
			// (¬l ⇔ ¬r) → (l ⇔ r)
			if _l != nil && _r != nil {
				return negIffNeg(_l, _r)
			}
			// (l = r) ⇔ (r = l) → ⊤
			if ll, lr, ok := MatchesEQ(l); ok {
				if rl, rr, ok := MatchesEQ(r); ok {
					if ll.AlphaEquals(rr) && lr.AlphaEquals(rl) {
						return CommuteEQ(ll, lr).Deduct(DerivesTrue)
					}
				}
			}
		}
		if l, r, ok := MatchesAND(t); ok {
			// (l ∧ ⊤) → l
			if r.Equals(T) {
				return BooleanThms["p ∧ ⊤"](l)
			}
			// (l ∧ ⊥) → ⊥
			if r.Equals(F) {
				return BooleanThms["p ∧ ⊥"](l)
			}
			// (⊤ ∧ r) → r
			if l.Equals(T) {
				return BooleanThms["⊤ ∧ p"](r)
			}
			// (⊥ ∧ r) → ⊥
			if l.Equals(F) {
				return BooleanThms["⊥ ∧ p"](r)
			}
			// (l ∧ l) → l
			if l.AlphaEquals(r) {
				return BooleanThms["p ∧ p"](l)
			}
			// (l ∧ ¬l) → ⊥
			if _r := MatchesNOT(r); _r != nil && l.AlphaEquals(_r) {
				return BooleanThms["p ∧ ¬p"](l)
			}
			// (¬r ∧ r) → ⊥
			if _l := MatchesNOT(l); _l != nil && r.AlphaEquals(_l) {
				return BooleanThms["¬p ∧ p"](r)
			}
		}
		if l, r, ok := MatchesOR(t); ok {
			// (l ∨ ⊤) → ⊤
			if r.Equals(T) {
				return BooleanThms["p ∨ ⊤"](l)
			}
			// (l ∨ ⊥) → l
			if r.Equals(F) {
				return BooleanThms["p ∨ ⊥"](l)
			}
			// (⊤ ∨ r) → ⊤
			if l.Equals(T) {
				return BooleanThms["⊤ ∨ p"](r)
			}
			// (⊥ ∨ r) → r
			if l.Equals(F) {
				return BooleanThms["⊥ ∨ p"](r)
			}
			// (l ∨ l) → l
			if l.AlphaEquals(r) {
				return BooleanThms["p ∨ p"](l)
			}
			// (l ∨ ¬l) → ⊤
			if _r := MatchesNOT(r); _r != nil && l.AlphaEquals(_r) {
				return BooleanThms["p ∨ ¬p"](l)
			}
			// (¬r ∨ r) → ⊤
			if _l := MatchesNOT(l); _l != nil && r.AlphaEquals(_l) {
				return BooleanThms["¬p ∨ p"](r)
			}
		}
		if l, r, ok := MatchesIMPLY(t); ok {
			// (l ⇒ ⊤) → ⊤
			if r.Equals(T) {
				return BooleanThms["p ⇒ ⊤"](l)
			}
			// (l ⇒ ⊥) → ¬l
			if r.Equals(F) {
				return BooleanThms["p ⇒ ⊥"](l)
			}
			// (⊤ ⇒ r) → r
			if l.Equals(T) {
				return BooleanThms["⊤ ⇒ p"](r)
			}
			// (⊥ ⇒ r) → ⊤
			if l.Equals(F) {
				return BooleanThms["⊥ ⇒ p"](r)
			}
			// (l ⇒ l) → ⊤
			if l.AlphaEquals(r) {
				return BooleanThms["p ⇒ p"](l)
			}
			// (l ⇒ ¬l) → ¬l
			if _r := MatchesNOT(r); _r != nil && l.AlphaEquals(_r) {
				return BooleanThms["p ⇒ ¬p"](l)
			}
			// (¬r ⇒ r) → r
			if _l := MatchesNOT(l); _l != nil && r.AlphaEquals(_l) {
				return BooleanThms["¬p ⇒ p"](r)
			}
		}

		if abs := MatchesFORALL(t); !abs.IsZero() {
			// ∀x.s → s if x is not a free var in x
			if !abs.Body().HasFree(abs.Var()) {
				return MootForAll(abs.Var(), abs.Body())
			}
			// ∀x.x → ⊥
			if abs.Body().Equals(abs.Var()) {
				return FalseDerives(t).Deduct(InstForAll(t, F))
			}
			// ∀x.¬x → ⊥
			if n := MatchesNOT(abs.Body()); n != nil && n.Equals(abs.Var()) {
				return FalseDerives(t).Deduct(NotTrue.EqMP(InstForAll(t, T)))
			}
			// ∀f.f(s) → ⊥
			if s, ok := abs.Body().AsAppliedTerm(); ok &&
				s.Fun().Equals(abs.Var()) {
				return FalseDerives(t).
					Deduct(InstForAll(t, Var("_", s.Arg().Type()).To(F)).
						RewriteConcl(betaRewrite))
			}
		}
		if abs := MatchesEXISTS(t); !abs.IsZero() {
			// (∃x.s) → s if x is not a free var in x
			if !abs.Body().HasFree(abs.Var()) {
				return MootExists(abs.Var(), abs.Body())
			}
			// ∃x.x → ⊤
			if abs.Body().Equals(abs.Var()) {
				return InstExists(t, T).Deduct(DerivesTrue)
			}
			// ∃x.¬x → ⊤
			if n := MatchesNOT(abs.Body()); n != nil && n.Equals(abs.Var()) {
				return NotFalse.
					RightAssume().
					DeriveTrans(InstExists(t, F)).
					Deduct(DerivesTrue)
			}
			// ∃f.f(s) → ⊤
			if s, ok := abs.Body().AsAppliedTerm(); ok &&
				s.Fun().Equals(abs.Var()) {
				w := InstExists(t, Var("_", s.Arg().Type()).To(T))
				return betaRewrite(w.Hyp(0)).
					RightAssume().
					DeriveTrans(w).
					Deduct(DerivesTrue)
			}
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

func doubleNegRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if s := MatchesNOT(t); s != nil {
			if _t := MatchesNOT(s); _t != nil {
				return DoubleNeg(_t)
			}
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

func pushNegRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if s := MatchesNOT(t); s != nil {
			if l, r, ok := MatchesIFF(s); ok {
				_l, _r := MatchesNOT(l), MatchesNOT(r)
				if _l != nil && _r == nil {
					return BinaryThms["(p ⊕ q) ⇔ (¬p ⇔ q)"](l, r).
						EqTrans(DoubleNeg(_l).LeftApply(core.IFF()).RightApply(r))
				}
				if _l == nil && _r != nil {
					return BinaryThms["(p ⊕ q) ⇔ (¬p ⇔ q)"](l, r).
						EqTrans(BinaryThms["(¬p ⇔ ¬q) ⇔ (p ⇔ q)"](l, _r))
				}
				return BinaryThms["(p ⊕ q) ⇔ (¬p ⇔ q)"](l, r)
			}
			if l, r, ok := MatchesAND(s); ok {
				return BinaryThms["¬(p ∧ q) ⇔ (¬p ∨ ¬q)"](l, r)
			}
			if l, r, ok := MatchesOR(s); ok {
				return BinaryThms["¬(p ∨ q) ⇔ (¬p ∧ ¬q)"](l, r)
			}
			if l, r, ok := MatchesIMPLY(s); ok {
				return BinaryThms["¬(p ⇒ q) ⇔ (p ∧ ¬q)"](l, r)
			}
			if abs := MatchesFORALL(s); !abs.IsZero() {
				return NegForAll(abs)
			}
			if abs := MatchesEXISTS(s); !abs.IsZero() {
				return NegExists(abs)
			}
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// trivialCondRewriteImpl rewrites COND with a literal boolean case term:
//   - Cond(_, x, x) → x   via CondId
//   - Cond(⊤, x, y) → x   via CondClauseT
//   - Cond(⊥, x, y) → y   via CondClauseF
func trivialCondRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if p, x, y, ok := ext.MatchesCond(t); ok {
			if p.Equals(T) {
				return CondClauseT(x, y)
			}
			if p.Equals(F) {
				return CondClauseF(x, y)
			}
			if x.AlphaEquals(y) {
				return CondId(p, x)
			}
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// condDecideByHypsImpl is CondDecideByHyps: the guard is rewritten to
// ⊤ (or ⊥) by the hypothesis that asserts it — `{c} ⊢ c ⇔ ⊤` is
// the assumption c read as an equation with ⊤, congruence carries it under COND's three
// applications — and CondClauseT / CondClauseF finish. A COND whose
// guard the context does not decide is left alone (nil).
func condDecideByHypsImpl(anyHyp func(func(Term) bool) bool) Rewrite {
	rewrite := func(t Term) *PropWrapper {
		c, x, y, ok := ext.MatchesCond(t)
		if !ok {
			return nil
		}
		// COND(c, x, y) is ((COND c) x) y: the const at the head is
		// what the congruence applies, at the term's own instance.
		app3, ok3 := t.AsAppliedTerm()
		if !ok3 {
			return nil
		}
		app2, ok2 := app3.Fun().AsAppliedTerm()
		if !ok2 {
			return nil
		}
		app1, ok1 := app2.Fun().AsAppliedTerm()
		if !ok1 {
			return nil
		}
		cond := app1.Fun()
		// guardIs lifts `Γ ⊢ c ⇔ v` (v ∈ {⊤, ⊥}) to `Γ ⊢ COND(c, x, y) = COND(v, x, y)`.
		guardIs := func(cIsV *PropWrapper) *PropWrapper {
			return WrapProp(core.PropRightApply(core.PropRightApply(core.PropLeftApply(cond, cIsV), x), y))
		}
		switch {
		case anyHyp(c.AlphaEquals):
			assume := WrapProp(core.Assume(c))                   // {c} ⊢ c
			cIsT := BooleanThms["p ⇔ ⊤"](c).EqSym().EqMP(assume) // {c} ⊢ c ⇔ ⊤
			return guardIs(cIsT).EqTrans(CondClauseT(x, y))
		case anyHyp(Not(c).Core().AlphaEquals):
			assume := WrapProp(core.Assume(Not(c).Core()))       // {¬c} ⊢ ¬c
			cIsF := BooleanThms["p ⇔ ⊥"](c).EqSym().EqMP(assume) // {¬c} ⊢ c ⇔ ⊥
			return guardIs(cIsF).EqTrans(CondClauseF(x, y))
		}
		// A negated guard ¬d decided by the hypothesis d: `{d} ⊢ ¬¬d`
		// by double negation, then ¬d read as an equation with ⊥.
		if d := MatchesNOT(c); d != nil && anyHyp(d.AlphaEquals) {
			assume := WrapProp(core.Assume(d)) // {d} ⊢ d
			notNot := Not(Not(d)).Core()
			dn := DoubleNegRewrite(notNot) // ⊢ ¬¬d ⇔ d
			if dn == nil {
				return nil
			}
			notNotD := dn.EqSym().EqMP(assume)                    // {d} ⊢ ¬¬d
			cIsF := BooleanThms["p ⇔ ⊥"](c).EqSym().EqMP(notNotD) // {d} ⊢ ¬d ⇔ ⊥
			return guardIs(cIsF).EqTrans(CondClauseF(x, y))
		}
		return nil
	}
	// verifyRewrite's check minus its hyp-free clause: this equality
	// carries the deciding hypothesis by design.
	return func(t Term) *PropWrapper {
		w := rewrite(t)
		if w != nil {
			Assert(t.AlphaEquals(Lhs(w)) && !t.AlphaEquals(Rhs(w)))
		}
		return w
	}
}

// formulaDecideByHypsImpl is FormulaDecideByHyps: the assumption t read
// as an equation with ⊤ (`{t} ⊢ t ⇔ ⊤`), the assumption ¬t as t's
// equation with ⊥ (`{¬t} ⊢ t ⇔ ⊥`). A term not of type bool, and ⊤ and
// ⊥ themselves, are left alone.
func formulaDecideByHypsImpl(anyHyp func(func(Term) bool) bool) Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if !t.Type().Equals(core.TypeBool()) || t.AlphaEquals(T) || t.AlphaEquals(F) {
			return nil
		}
		if anyHyp(t.AlphaEquals) {
			assume := WrapProp(core.Assume(t))                  // {t} ⊢ t
			return BooleanThms["p ⇔ ⊤"](t).EqSym().EqMP(assume) // {t} ⊢ t ⇔ ⊤
		}
		negated := func(h Term) bool {
			inner := MatchesNOT(h)
			return inner != nil && inner.AlphaEquals(t)
		}
		if anyHyp(negated) {
			assume := WrapProp(core.Assume(Not(t).Core()))      // {¬t} ⊢ ¬t
			return BooleanThms["p ⇔ ⊥"](t).EqSym().EqMP(assume) // {¬t} ⊢ t ⇔ ⊥
		}
		return nil
	}
	// verifyRewrite's check minus its hyp-free clause: this equality
	// carries the deciding hypothesis by design.
	return func(t Term) *PropWrapper {
		w := rewrite(t)
		if w != nil {
			Assert(t.AlphaEquals(Lhs(w)) && !t.AlphaEquals(Rhs(w)))
		}
		return w
	}
}

// condElimRewriteImpl eliminates a COND subterm in a term t.
//
// Algorithm:
//
//	Find the first bool subterm  (possibly under lambdas) that contains
//	   a COND(c, x, y) subterm in t.
//	Introduce a fresh boolean variable α₀ and substitute it for c via
//	   DenoteRewrite, yielding ⊢ t = t[c↦α₀]. Compute the T-branch
//	   t[c↦⊤] and F-branch t[c↦⊥] by substitution.
//	Prove t[c↦α₀] = (α₀ ⇒ t[c↦⊤]) ∧ (¬α₀ ⇒ t[c↦⊥]) by BoolInduct.
//
// Every walk here — the trivial-COND tidy, the two searches, the rewrite
// back into t — enters only the subterms that carry a COND: the leaf runs
// at every node DeepRewrite visits and again after every elimination, so
// its cost is the part of t that still carries a COND, not t.
func condElimRewriteImpl() Rewrite {
	deepTrivialCondRewrite := deepRewriteCarrying(ext.CondStr, trivialCondRewrite)
	isCondTerm := func(s Term) bool {
		_, _, _, ok := ext.MatchesCond(s)
		return ok
	}

	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		_t := t
		u := deepTrivialCondRewrite(t)
		if u != nil {
			_t = Rhs(u)
		}

		// Find a subterm whose body is bool and contains a cond term.
		boolSubTerm := ext.FindBottomSubTermCarrying(_t, ext.CondStr,
			func(s Term) bool { return IsBool(s) && ext.FindTopSubTermCarrying(s, ext.CondStr, isCondTerm) != nil })
		if boolSubTerm == nil {
			return u
		}

		boolSubTermVars, boolSubTermBody := MatchesAbs(boolSubTerm)
		Assert(IsBool(boolSubTermBody))
		// The cond term we're working on.
		condTerm := ext.FindTopSubTermCarrying(boolSubTermBody, ext.CondStr, isCondTerm)
		Assert(condTerm != nil)

		vars, body := MatchesAbs(condTerm)
		caseTerm, _, _, _ := ext.MatchesCond(body)

		// If any free var in case term is captured by an enclosing lambda,
		// decline at this level. DeepRewrite will recurse inside the binder
		// and retry where the case term is free.
		if utils.Any(vars, caseTerm.HasFree) {
			return u
		}

		// introduce α₀ for the case term.
		alpha := WrapTerm(core.Var(TermName(utils.Subscript(utils.AlphaStr, 0)), TypeBool).
			RenameToAvoid(t))

		// α₀ = c ⊢ boolSubTermBody = P(COND(α₀, x, y))
		w := DenoteRewrite(alpha.AssertVar(), caseTerm)(boolSubTermBody)
		Assert(w != nil)
		// replace α₀ by ⊤/⊥
		caseT := Rhs(w).Substitute(MakeTermSubst(alpha, T))
		caseF := Rhs(w).Substitute(MakeTermSubst(alpha, F))
		vT := deepTrivialCondRewrite(caseT) // P(x)
		vF := deepTrivialCondRewrite(caseF) // P(y)

		// derive the rewrite by BoolInduct on α₀.
		// P(Cond(α₀, x, y)) → (α₀ ⇒ P(x)) ∧ (¬α₀ ⇒ P(y))
		v := BoolInduct(alpha.To(Eq(Rhs(w), alpha.Imply(Rhs(vT)).And(Not(alpha).Imply(Rhs(vF)))))).
			Rewrite(deepTrivialCondRewrite)

		// restore α₀ → case term and discharge trivial hypotheses.
		// β-normalize ONLY the Rhs: Substitute above may introduce redexes
		// (e.g. `(λv:prod. body(v))((a,b))` when caseTerm carries a
		// paired-lambda application), but the Lhs has no α₀ occurrences
		// and no substitution touched it, so it must remain structurally
		// equal to boolSubTermBody. RewriteConcl(DeepBeta) would β-reduce
		// both sides, corrupting Lhs when boolSubTermBody itself carries
		// β-redexes (observed on an iterated-product proof: auto's condElim pass on
		// a set_comprehension/pattern_abstraction-heavy hyp panicked the Assert below).
		w = w.
			EqTrans(v).
			TermInst(MakeTermSubst(alpha, caseTerm)).RewriteConclRhs(DeepBeta)
		Assert(Lhs(w).AlphaEquals(boolSubTermBody))

		for h := range w.HypIter() {
			w = w.DeriveHypFrom(DeepBoolRewrite(h).RightAssume())
		}
		w = w.DeriveHypFrom(DerivesTrue)

		// Add back abstracted vars.
		for _, v := range slices.Backward(boolSubTermVars) {
			w = w.Abs(v)
		}

		if u == nil {
			return eqRewriteCarrying(w, ext.CondStr)(t)
		}
		return u.RewriteConclRhs(eqRewriteCarrying(w, ext.CondStr))
	}
	return verifyRewrite(rewrite)
}

// condSwapRewriteImpl repositions a COND subterm in a term t.
//
// Algorithm:
//  1. Find the first COND(c, x, y) subterm in t (possibly under lambdas).
//  2. If the case term c has free variables captured by an enclosing lambda,
//     decline (return nil) — DeepRewrite will recurse inside the binder and
//     retry at a level where c is free.
//  3. Introduce a fresh boolean variable α₀ and substitute it for c via
//     DenoteRewrite, yielding ⊢ t = t[c↦α₀]. Compute the T-branch
//     t[c↦⊤] and F-branch t[c↦⊥] by substitution.
//  4. prove t[c↦α₀] = Cond(α₀, t[c↦⊤], t[c↦⊥]) by BoolInduct,
//     which pushes COND outward.
//
// The non-bool case may produce no change if the COND is already at the
// outermost position (e.g. Cond(c, a, b) → Cond(c, a, b)), in which case
// nil is returned. Its walks enter only the subterms that carry a COND,
// as condElimRewriteImpl's do.
func condSwapRewriteImpl() Rewrite {
	deepTrivialCondRewrite := deepRewriteCarrying(ext.CondStr, trivialCondRewrite)
	isCondTerm := func(s Term) bool {
		_, _, _, ok := ext.MatchesCond(s)
		return ok
	}

	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		// We don't do CondSwap for bool term Use Cond Elim Rewrite instead.
		if IsBool(t) {
			return nil
		}
		// Nor at an abstraction. Swapping there pulls a COND outward THROUGH
		// the λ — `λx. COND(c, f, g)(x)` → `COND(c, λx.f(x), λx.g(x))`
		// — which leaves a COND of FUNCTIONS as the
		// argument of whatever bound the λ. A quantifier rule then
		// η-expands that argument back into a λ (`∀ P` is `∀x. P(x)`), the
		// swap fires again, and the two never meet: a COND of predicates
		// under `∀` cycled without bound on `def_expand(iterate)` at a fold
		// whose summand carried a COND. The sound fire is one level down,
		// at the application `COND(c, f, g)(x)`, which DeepRewrite reaches
		// by recursing into the body: the argument moves into both arms, `COND(c, f(x), g(x))`,
		// where that site is not bool, elimination where it is; either
		// way the binder's argument stays a λ and the quantifier rule is
		// satisfied. The same judgment the whistle makes for a permutation
		// fire at a function-typed site: no sound orientation there,
		// decline, the applied level decides.
		if _, ok := t.AsAbsTerm(); ok {
			return nil
		}

		_t := t
		u := deepTrivialCondRewrite(t)
		if u != nil {
			_t = Rhs(u)
		}

		condTerm := ext.FindTopSubTermCarrying(_t, ext.CondStr, isCondTerm)
		if condTerm == nil {
			return u
		}
		vars, body := MatchesAbs(condTerm)
		caseTerm, _, _, _ := ext.MatchesCond(body)

		// If any free var in case term is captured by an enclosing lambda,
		// decline at this level. DeepRewrite will recurse inside the binder
		// and retry where the case term is free.
		if utils.Any(vars, caseTerm.HasFree) {
			return u
		}

		// introduce α₀ for the case term.
		alpha := WrapTerm(core.Var(TermName(utils.Subscript(utils.AlphaStr, 0)), TypeBool).
			RenameToAvoid(t))
		// α₀ = c ⊢ condTerm = P(COND(α₀, x, y))
		w := DenoteRewrite(alpha.AssertVar(), caseTerm)(_t)
		Assert(w != nil)
		// replace α₀ by ⊤/⊥
		caseT := Rhs(w).Substitute(MakeTermSubst(alpha, T))
		caseF := Rhs(w).Substitute(MakeTermSubst(alpha, F))
		vT := deepTrivialCondRewrite(caseT) // P(x)
		vF := deepTrivialCondRewrite(caseF) // P(y)

		// if the current cond term is a case of an outside cond term
		// swap would create infinite loop.
		f, args := ext.MatchesApply(Rhs(w))
		if f, ok := f.AsConst(); ok &&
			f.Meta().Equals(ext.COND.Meta()) &&
			len(args) < 3 {
			return u
		}

		// if this COND is already at outermost position — nothing to rewrite.
		if c, p, q, ok := ext.MatchesCond(Rhs(w)); ok &&
			c.AlphaEquals(alpha) && p.AlphaEquals(Rhs(vT)) && q.AlphaEquals(Rhs(vF)) {
			return u
		}

		// derive the rewrite by BoolInduct on α₀.
		// P(Cond(α₀, x, y)) → Cond(α₀, P(x), P(y))
		v := BoolInduct(alpha.To(Eq(Rhs(w), ext.Cond(alpha, Rhs(vT), Rhs(vF))))).
			Rewrite(deepTrivialCondRewrite)

		// restore α₀ → case term and discharge trivial hypotheses.
		// β-normalize ONLY the Rhs (same reasoning as line 569).
		w = w.
			EqTrans(v).
			TermInst(MakeTermSubst(alpha, caseTerm)).RewriteConclRhs(DeepBeta)
		for h := range w.HypIter() {
			w = w.DeriveHypFrom(DeepBoolRewrite(h).RightAssume())
		}
		w = w.DeriveHypFrom(DerivesTrue)

		Assert(Lhs(w).AlphaEquals(_t))
		if u == nil {
			return w
		}
		return u.EqTrans(w)
	}
	return verifyRewrite(rewrite)
}

func quantifierRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		_t, ok := t.AsAppliedTerm()
		if !ok {
			return nil
		}
		fun, ok := _t.Fun().(ConstTerm)
		if !ok {
			return nil
		}
		if !fun.Meta().Equals(FORALL.Meta()) &&
			!fun.Meta().Equals(EXISTS.Meta()) &&
			!fun.Meta().Equals(UNIQUE.Meta()) {
			return nil
		}
		arg := _t.Arg()
		if _, ok := arg.AsAbsTerm(); !ok {
			x := core.Var(
				utils.X_DOT,
				arg.Type().(CompositeType).SubType(0)).
				RenameToAvoid(arg)
			return Eta(Apply(arg, x)).
				EqSym().
				LeftApply(fun)
		}

		if vars, body := DecomposesFORALL(t); !vars.Empty() {
			_t := t
			// ∀P.P(s) → ⊥
			if s, ok := body.AsAppliedTerm(); ok {
				if v, ok := s.Fun().AsVar(); ok && vars.Has(v) {
					if vars.Size() != 1 {
						_t = ForAll(v)(body)
					}
					w := InstForAll(_t,
						Var("_", s.Arg().Type()).To(F)).
						RewriteConcl(betaRewrite)
					w = FalseDerives(_t).Deduct(w)
					return forallReorderHelper(t, &vars, v, w)
				}
			}
			if n := MatchesNOT(body); n != nil {
				// ∀x.(x ≠ s) → ⊥
				if l, r, ok := MatchesEQ(n); ok {
					if l, ok := l.AsVar(); ok &&
						vars.Has(l) &&
						!r.HasFree(l) {
						if vars.Size() != 1 {
							_t = ForAll(l)(body)
						}
						w := InstForAll(_t, r).
							RewriteConcl(DeepBoolRewrite)
						w = FalseDerives(_t).Deduct(w)
						return forallReorderHelper(t, &vars, l, w)
					}
					if r, ok := r.AsVar(); ok &&
						vars.Has(r) &&
						!l.HasFree(r) {
						if vars.Size() != 1 {
							_t = ForAll(r)(body)
						}
						w := InstForAll(_t, l).
							RewriteConcl(DeepBoolRewrite)
						w = FalseDerives(_t).Deduct(w)
						return forallReorderHelper(t, &vars, r, w)
					}
				}
				// ∀P.¬P(s) → ⊤
				if s, ok := n.AsAppliedTerm(); ok {
					if v, ok := s.Fun().AsVar(); ok && vars.Has(v) {
						if vars.Size() != 1 {
							_t = ForAll(v)(body)
						}
						w := InstForAll(_t,
							Var("_", s.Arg().Type()).To(T)).
							RewriteConcl(DeepBeta).
							RewriteConcl(BoolRewrite)
						w = FalseDerives(_t).Deduct(w)
						return forallReorderHelper(t, &vars, v, w)
					}
				}
			}
		}
		if vars, body := DecomposesEXISTS(t); !vars.Empty() {
			_t := t
			// ∃x.(x = s) → ⊤
			if l, r, ok := MatchesEQ(body); ok {
				if l, ok := l.AsVar(); ok &&
					vars.Has(l) &&
					!r.HasFree(l) {
					if vars.Size() != 1 {
						_t = Exists(l)(body)
					}
					w := InstExists(_t, r).
						DeriveHypFrom(Refl(r)).
						Deduct(DerivesTrue)
					return existsReorderHelper(t, &vars, l, w)
				}

				if r, ok := r.AsVar(); ok &&
					vars.Has(r) &&
					!l.HasFree(r) {
					if vars.Size() != 1 {
						_t = Exists(r)(body)
					}
					w := InstExists(_t, l).
						DeriveHypFrom(Refl(l)).
						Deduct(DerivesTrue)
					return existsReorderHelper(t, &vars, r, w)
				}
			}
			// ∃P.P(s) → ⊤
			if s, ok := body.AsAppliedTerm(); ok {
				if v, ok := s.Fun().AsVar(); ok && vars.Has(v) {
					if vars.Size() != 1 {
						_t = Exists(v)(body)
					}
					w := InstExists(_t,
						Var("_", s.Arg().Type()).To(T))
					w = betaRewrite(w.Hyp(0)).
						RightAssume().
						DeriveTrans(w).
						Deduct(DerivesTrue)
					return existsReorderHelper(t, &vars, v, w)
				}
			}
			// ∃P.¬P(s) → ⊤
			if n := MatchesNOT(body); n != nil {
				if s, ok := n.AsAppliedTerm(); ok {
					if v, ok := s.Fun().AsVar(); ok && vars.Has(v) {
						if vars.Size() != 1 {
							_t = Exists(v)(body)
						}
						w := InstExists(_t,
							Var("_", s.Arg().Type()).To(F))
						w = DeepBeta(w.Hyp(0)).
							RewriteConclRhs(BoolRewrite).
							RightAssume().
							DeriveTrans(w).
							Deduct(DerivesTrue)
						return existsReorderHelper(t, &vars, v, w)
					}
				}
			}
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

func uniqueRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if abs := MatchesUNIQUE(t); !abs.IsZero() {
			return AltUnique(abs)
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

func uniqueWitnessRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if abs := MatchesUNIQUE(t); !abs.IsZero() {
			return WitnessUnique(abs)
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// (l ⇒ r) ⇔ (¬l ∨ r)
func implyToOrRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if l, r, ok := MatchesIMPLY(t); ok {
			return BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](l, r)
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// (l ⇔ r) ⇔ ((l ∧ r) ∨ (¬l ∧ ¬r))
func iffToOrRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if l, r, ok := MatchesIFF(t); ok {
			return BinaryThms["(p ⇔ q) ⇔ ((p ∧ q) ∨ (¬p ∧ ¬q))"](l, r)
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

func funEqRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		l, r, ok := MatchesEQ(t)
		if !ok {
			return nil
		}
		if l, ok := l.AsAbsTerm(); ok {
			if r, ok := r.AsAbsTerm(); ok {
				l, r = ext.AlignAbstractedVar(l, r)
				w := FunEq(l, r)
				abs := MatchesFORALL(Rhs(w))
				if !abs.Body().HasFree(abs.Var()) {
					return w.EqTrans(MootForAll(abs.Var(), abs.Body()))
				}
				return w
			}
		}
		types := ext.MatchesFun(l.Type())
		if len(types) == 1 {
			return nil
		}

		if r, ok := r.AsAbsTerm(); ok {
			x := r.Var().RenameToAvoid(l)
			// (l = r) = (λx.l(x) = r)
			return Eta(Apply(l, x)).
				EqSym().
				LeftApply(t.Core().(AppliedTerm).Fun().(AppliedTerm).Fun()).
				RightApply(r)
		}
		var x VarTerm
		if l, ok := l.AsAbsTerm(); ok {
			x = l.Var().RenameToAvoid(r)
		} else {
			x = core.Var(utils.X_DOT, types[0]).RenameToAvoid(r)
		}
		// (l = r) ⇔ (l = λx.r(x))
		return Eta(Apply(r, x)).
			EqSym().
			LeftApply(t.Core().(AppliedTerm).Fun())
	}
	return verifyRewrite(rewrite)
}

// prenexOp is one connective as a quantifier's prenex rule sees it: how
// to recognise its chains, the theorems that pull a quantified component
// out of either side of a node, and — for the connective the quantifier
// distributes over — the theorem that identifies two same-type binders.
type prenexOp struct {
	opConst      Term
	matcher      ext.BinaryOpMatcher
	decompose    ext.BinaryOpDecomposer
	decomposeLen func(Term) int
	// pullLeft(λx.P, Q) proves ⊢ (Qx.P) op Q = Qx.(P op Q);
	// pullRight(λx.P, Q) proves ⊢ Q op (Qx.P) = Qx.(Q op P).
	pullLeft, pullRight func(Term, Term) *PropWrapper
	// merge(λx.s, λx.t) proves ⊢ (Qx.s op Qx.t) = Qx.(s op t); nil when
	// the quantifier does not distribute over op (∀ over ∨, ∃ over ∧).
	merge func(AbsTerm, AbsTerm) *PropWrapper
}

func makePrenexOp(
	opConst Term, matcher ext.BinaryOpMatcher,
	pullLeft, pullRight func(Term, Term) *PropWrapper,
	merge func(AbsTerm, AbsTerm) *PropWrapper,
) prenexOp {
	return prenexOp{
		opConst:      opConst,
		matcher:      matcher,
		decompose:    ext.DecomposesBinaryOp(matcher),
		decomposeLen: ext.DecomposeLenBinaryOp(matcher),
		pullLeft:     pullLeft,
		pullRight:    pullRight,
		merge:        merge,
	}
}

// quantifierPrenexRewriteImpl builds the prenex rule of one quantifier
// kind. The rule works on a whole ∧/∨ CHAIN, flattened, so that the
// result does not depend on how the chain is associated:
//
//   - it declines while some component that is not itself Q-quantified
//     still holds a Q-quantifier the rules will surface (one reachable
//     through ∧/∨ nodes); DeepRewrite then rewrites the operands and
//     re-runs the rule here, and only then does the chain see every
//     binder it must merge — the two binary rules this replaces merged
//     `Qx.s op Qx.t` only when the two happened to be the operands of
//     one node at fire time, so `(A ∧ ∀x.P) ∧ ∀x.Q` kept two binders
//     where `A ∧ (∀x.P ∧ ∀x.Q)` kept one;
//   - for ∃, a quantified component that still holds a ∀ is pulled on
//     its own first (dualHolderPredicate), so the ∀ can rise above the
//     chain's other ∃ before those merge;
//   - over the connective Q distributes across, every Q-quantified
//     component whose binder has one type merges into ONE binder
//     (`∀x.s ∧ B ∧ ∀y.t` becomes `∀x.(s ∧ B ∧ t[x/y])`), one type group
//     per fire, the group of the leftmost such component first;
//   - otherwise the leftmost quantified component is pulled over the
//     rest of the chain.
//
// A fire lifts its binder in place: the chain keeps its component order
// and its association, only the quantifier moves (pullMembers). The
// prefix that results lists binders in the order they were pulled; the
// block sort in DisjunctNormalize (quantifiersSort) canonicalises it.
func quantifierPrenexRewriteImpl(
	matches, dual func(Term) AbsTerm, pullDualHoldersFirst bool, ops ...prenexOp,
) Rewrite {
	hidden := hiddenQuantifierPredicate(matches, dual)
	holdsDual := dualHolderPredicate(matches, dual)
	if !pullDualHoldersFirst {
		holdsDual = nil
	}
	rewrite := func(t Term) *PropWrapper {
		for _, op := range ops {
			if _, _, ok := op.matcher(t); ok {
				return prenexChain(t, matches, hidden, holdsDual, op)
			}
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// dualHolderPredicate reports whether a Q-quantified component still
// holds a quantifier of the dual kind that the prenex rules will
// surface once Q is pulled — one reachable from Q's body through
// further Q binders and ∧/∨ nodes. The ∃ rule pulls such a component
// on its own before it merges anything: `(∃y.A(y)) ∨ ∃N.∀M'.B(N,M')`
// must become ∃N.∀M'.∃y.(A(y) ∨ B'(N,M',y)) — the ∀ risen as far as it
// can, the two witnesses under it merged — not ∃N.∀M'.(A(N) ∨ …) with
// the unboundedness witness identified with the supremum. The ∀ rule
// has no such step: ∀x.∃u.C ∧ ∀y.D merges x and y first, which is what
// keeps that ∀ outside the ∃.
func dualHolderPredicate(matches, dual func(Term) AbsTerm) func(Term) bool {
	var reachable func(Term) bool
	reachable = func(t Term) bool {
		if !dual(t).IsZero() {
			return true
		}
		if abs := matches(t); !abs.IsZero() {
			return reachable(abs.Body())
		}
		l, r, ok := MatchesAND(t)
		if !ok {
			l, r, ok = MatchesOR(t)
		}
		return ok && (reachable(l) || reachable(r))
	}
	return func(t Term) bool {
		abs := matches(t)
		return !abs.IsZero() && reachable(abs.Body())
	}
}

// hiddenQuantifierPredicate reports, for a chain component that is not
// itself Q-quantified, whether a Q-quantifier is reachable from it
// through ∧/∨ nodes and negations — the quantifiers the surrounding
// rewrite will still surface: the prenex rules lift through ∧/∨, and
// negation normal form turns a negated dual quantifier into this kind
// (¬∀x.P into ∃x.¬P) and pushes a negation through ∧/∨. A quantifier
// under another quantifier, a ⇔ or a λ is not reachable: no rule moves it.
func hiddenQuantifierPredicate(matches, dual func(Term) AbsTerm) func(Term) bool {
	var reachable func(Term) bool
	var reachableDual func(Term) bool
	through := func(t Term, same, other func(Term) bool) bool {
		if u := MatchesNOT(t); u != nil {
			return other(u)
		}
		l, r, ok := MatchesAND(t)
		if !ok {
			l, r, ok = MatchesOR(t)
		}
		return ok && (same(l) || same(r))
	}
	reachable = func(t Term) bool {
		return !matches(t).IsZero() || through(t, reachable, reachableDual)
	}
	reachableDual = func(t Term) bool {
		return !dual(t).IsZero() || through(t, reachableDual, reachable)
	}
	return func(t Term) bool { return matches(t).IsZero() && reachable(t) }
}

func prenexChain(
	t Term, matches func(Term) AbsTerm, hidden, holdsDual func(Term) bool, op prenexOp,
) *PropWrapper {
	components := op.decompose(t)
	var quantified []int
	for i, c := range components {
		if !matches(c).IsZero() {
			quantified = append(quantified, i)
		} else if hidden(c) {
			return nil
		}
	}
	if len(quantified) == 0 {
		return nil
	}
	members := map[int]bool{quantified[0]: true}
	if holdsDual != nil {
		for _, i := range quantified {
			if holdsDual(components[i]) {
				return pullMembers(t, components, map[int]bool{i: true}, matches, op)
			}
		}
	}
	if op.merge != nil {
		for k, i := range quantified {
			varType := matches(components[i]).Var().Type()
			group := []int{i}
			for _, j := range quantified[k+1:] {
				if matches(components[j]).Var().Type().Equals(varType) {
					group = append(group, j)
				}
			}
			if len(group) >= 2 {
				members = map[int]bool{}
				for _, j := range group {
					members[j] = true
				}
				break
			}
		}
	}
	return pullMembers(t, components, members, matches, op)
}

// pullMembers proves ⊢ t = Qx.t' for the chain t: every member component
// Qy.s (members indexes t's flattened components; all of one binder
// type) becomes s[x/y] in t', x a variable fresh for t, and everything
// else stays where it is. Walking the chain's tree, a node with members
// on one side pulls that side's binder across the node; a node with
// members on both sides — only reached when Q distributes over op —
// merges the two sides' binders into the common x.
func pullMembers(
	t Term, components []Term, members map[int]bool,
	matches func(Term) AbsTerm, op prenexOp,
) *PropWrapper {
	first := len(components)
	for i := range members {
		first = min(first, i)
	}
	// The first member's binder names the merged binder; it is renamed
	// only when the chain has it FREE somewhere (a capture), never for a
	// bound occurrence — the pulled form keeps the author's name.
	x := matches(components[first]).Var()
	if t.HasFree(x) {
		x = x.RenameToAvoid(t)
	}
	anyMember := func(lo, hi int) bool {
		for i := lo; i < hi; i++ {
			if members[i] {
				return true
			}
		}
		return false
	}
	var pull func(t Term, offset int) *PropWrapper
	pull = func(t Term, offset int) *PropWrapper {
		l, r, ok := op.matcher(t)
		if !ok {
			Assert(members[offset])
			// ⊢ Qx.s[x/y] = Qx.s[x/y]; its left side is the member, up to α.
			abs := matches(t).ChangeAbsVar(x.Name())
			return Refl(Apply(t.Core().(AppliedTerm).Fun(), abs))
		}
		lLen := op.decomposeLen(l)
		inL := anyMember(offset, offset+lLen)
		inR := anyMember(offset+lLen, offset+lLen+op.decomposeLen(r))
		switch {
		case inL && inR:
			Assert(op.merge != nil)
			wl, wr := pull(l, offset), pull(r, offset+lLen)
			// A pull theorem renames its binder when the name clashes
			// with a template variable, so the two sides may reach this
			// node under different names; align them before merging.
			lAbs, rAbs := ext.AlignAbstractedVar(matches(Rhs(wl)), matches(Rhs(wr)))
			return wl.LeftApply(op.opConst).Apply(wr).
				EqTrans(op.merge(lAbs, rAbs))
		case inL:
			wl := pull(l, offset)
			return wl.LeftApply(op.opConst).RightApply(r).
				EqTrans(op.pullLeft(matches(Rhs(wl)), r))
		default:
			wr := pull(r, offset+lLen)
			return wr.LeftApply(t.Core().(AppliedTerm).Fun()).
				EqTrans(op.pullRight(matches(Rhs(wr)), l))
		}
	}
	return pull(t, 0)
}

func universalPrenexRewriteImpl() Rewrite {
	return quantifierPrenexRewriteImpl(MatchesFORALL, MatchesEXISTS, false,
		makePrenexOp(AND, MatchesAND,
			PrenexThms["(∀x.P(x)) ∧ Q ⇔ ∀x.(P(x) ∧ Q)"],
			PrenexThms["Q ∧ ∀x.P(x) ⇔ ∀x.(Q ∧ P(x))"],
			func(l, r AbsTerm) *PropWrapper {
				// (∀x.s ∧ ∀x.t) = ∀x.(s ∧ t)
				return ForAllAND(l, r).EqSym()
			}),
		makePrenexOp(OR, MatchesOR,
			PrenexThms["(∀x.P(x)) ∨ Q ⇔ ∀x.(P(x) ∨ Q)"],
			PrenexThms["Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))"],
			nil))
}

func existentialPrenexRewriteImpl() Rewrite {
	return quantifierPrenexRewriteImpl(MatchesEXISTS, MatchesFORALL, true,
		makePrenexOp(AND, MatchesAND,
			PrenexThms["(∃x.P(x)) ∧ Q ⇔ ∃x.(P(x) ∧ Q)"],
			PrenexThms["Q ∧ ∃x.P(x) ⇔ ∃x.(Q ∧ P(x))"],
			nil),
		makePrenexOp(OR, MatchesOR,
			PrenexThms["(∃x.P(x)) ∨ Q ⇔ ∃x.(P(x) ∨ Q)"],
			PrenexThms["Q ∨ ∃x.P(x) ⇔ ∃x.(Q ∨ P(x))"],
			func(l, r AbsTerm) *PropWrapper {
				// (∃x.s ∨ ∃x.t) = ∃x.(s ∨ t)
				return ExistsOR(l, r).EqSym()
			}))
}

// Rewrite a binary op chain term to left associated form.
// E.g. (x0 ∨ ((x1 ∨ x2) ∨ x3)) --> ((x0 ∨ x1) ∨ x2) ∨ x3
// If nothing to rewrite, return nil.
// Shallow rewrite.
func AssocRewrite(
	opConst Term,
	matcher ext.BinaryOpMatcher,
	associateThm func(Term, Term, Term) *PropWrapper) Rewrite {
	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		l, r, ok := matcher(t)
		if !ok {
			return nil
		}
		if rl, rr, ok := matcher(r); ok {
			// l . (rl . rr) ⇔ (l . rl) . rr
			return associateThm(l, rl, rr).EqSym().RewriteConclRhs(rewrite)
		} else if u := rewrite(l); u != nil {
			return u.LeftApply(opConst).RightApply(r)
		}
		return nil
	}
	return verifyRewriteOpen(rewrite)
}

// (q ∧ ... ) ∨ p → (q ∨ p) ∧ ...
// (q ∨ ... ) ∧ p → (q ∧ p) ∨ ...
// shallow rewrite
func DistributeRewrite(
	innerOpConst ConstTerm,
	outerMatcher, innerMatcher ext.BinaryOpMatcher,
	distribute func(Term, Term, Term) *PropWrapper) Rewrite {
	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		p, s, ok := outerMatcher(t)
		if !ok {
			return nil
		}
		l, r, ok := innerMatcher(s)
		if !ok {
			return nil
		}
		w := distribute(p, l, r)
		_l, _r, _ := innerMatcher(Rhs(w))
		resultL, resultR := rewrite(_l), rewrite(_r)
		if resultL != nil && resultR != nil {
			return w.EqTrans(resultL.LeftApply(innerOpConst).Apply(resultR))
		} else if resultL != nil {
			return w.EqTrans(resultL.LeftApply(innerOpConst).RightApply(_r))
		} else if resultR != nil {
			return w.EqTrans(resultR.LeftApply(Rhs(w).(AppliedTerm).Fun()))
		}
		return w
	}
	return verifyRewrite(rewrite)
}

type ChainArrangement func(Term, int, int) *PropWrapper

// For a term chained by an op with commutativity and associativity,
// e.g. (x0 . ((x1 . x2) . x3)),
// Moves the j-th element right to i-th element and makes the op between them
// be calculated first.
// If i == -1, moves j-th to the first and make it seperated from others.
// Panic if i >= j or i < -1.
// If nothing to move, return Refl, not nil.
// This is a different behavior from most other rewrites.
func ArrangeChain(
	opConst Term,
	matcher ext.BinaryOpMatcher,
	commute func(Term, Term) *PropWrapper,
	associate func(Term, Term, Term) *PropWrapper) ChainArrangement {
	decomposeLen := ext.DecomposeLenBinaryOp(matcher)

	// Rewrite binary op chain term such that the last element is separated.
	// E.g. x0 ∨ ((x1 ∨ x2) ∨ x3) --> (x0 ∨ (x1 ∨ x2)) ∨ x3
	// If nothing to rewrite, return nil.
	var lastSeparate func(Term, Term) *PropWrapper
	lastSeparate = func(l, r Term) *PropWrapper {
		// l . (rl . rr) = (l . rl) . rr
		if rl, rr, ok := matcher(r); ok {
			w := associate(l, rl, rr).EqSym()
			_l, _, _ := matcher(Rhs(w))
			if u := lastSeparate(_l, rr); u != nil {
				w = w.EqTrans(u)
			}
			return w
		}
		return nil
	}

	// this function moves the j element to the last and separate it from others.
	var moveLast func(Term, int) *PropWrapper
	moveLast = func(t Term, j int) *PropWrapper {
		l, r, ok := matcher(t)
		Assert(ok)
		lLen := decomposeLen(l)
		if j < lLen { // element j is in l
			if lLen == 1 {
				return commute(l, r)
			}
			wl := moveLast(l, j)
			jLeft, ej, _ := matcher(Rhs(wl))
			return wl.LeftApply(opConst).RightApply(r).
				EqTrans(associate(jLeft, ej, r)).
				EqTrans(commute(ej, r).LeftApply(Rhs(wl).(AppliedTerm).Fun())).
				EqTrans(associate(jLeft, r, ej).EqSym())
		}
		// element j is in r
		_, _, ok = matcher(r)
		if !ok { // r is the last element.
			Assert(j == lLen) // otherwise j is too large.
			return Refl(t)
		}
		wr := moveLast(r, j-lLen)
		jLeft, ej, _ := matcher(Rhs(wr))
		return wr.
			LeftApply(t.Core().(AppliedTerm).Fun()).
			EqTrans(associate(l, jLeft, ej).EqSym())
	}

	var rewrite func(Term, int, int) *PropWrapper
	rewrite = func(t Term, i, j int) (w *PropWrapper) {
		defer func() {
			if w != nil {
				// The shape only: the laws are the caller's and may carry
				// a structure hypothesis (verifyRewriteOpen).
				Assert(t.Equals(Lhs(w)))
			}
		}()

		l, r, _ := matcher(t)
		lLen := decomposeLen(l)
		Assert(i >= -1 && j >= 0 && i < j)

		// element i & j are both in l
		if j < lLen {
			if lLen == 1 {
				return Refl(t)
			}
			wl := rewrite(l, i, j)
			w := wl.LeftApply(opConst).RightApply(r)
			if i != -1 {
				return w
			}
			// although element j has been separated from the rest in l,
			// it still needs to be separated in the outer level.
			ej, jRight, _ := matcher(Rhs(wl))
			return w.EqTrans(associate(ej, jRight, r))

		}

		// element i & j are both in r
		if i >= lLen {
			return rewrite(r, i-lLen, j-lLen).
				LeftApply(t.Core().(AppliedTerm).Fun())
		}

		// i = -1, element j is in r
		if i == -1 {
			if _, _, ok := matcher(r); ok {
				wr := moveLast(r, j-lLen)
				jLeft, ej, _ := matcher(Rhs(wr))
				return wr.
					LeftApply(t.Core().(AppliedTerm).Fun()).
					EqTrans(associate(l, jLeft, ej).EqSym()).
					EqTrans(commute(Apply(opConst, l, jLeft), ej))
			} else { // r itself is the j-th element.
				Assert(j == lLen) // otherwise j is too large.
				return commute(l, r)
			}
		}

		// i >= 0, element i is in l, element j is in r
		// r has more than one elements
		if _, _, ok := matcher(r); ok {
			wr := rewrite(r, -1, j-lLen)
			ej, jRight, _ := matcher(Rhs(wr))
			return wr.
				LeftApply(t.Core().(AppliedTerm).Fun()).
				EqTrans(associate(l, ej, jRight).EqSym()).
				EqTrans(rewrite(Apply(opConst, l, ej), i, lLen).
					LeftApply(opConst).
					RightApply(jRight))
		}

		// i >= 0, element i is in l.
		// r has 1 element (j).
		Assert(j == lLen) // otherwise j is too large.

		// r has 1 element (j), i is the last in l
		if i == lLen-1 {
			if ll, lr, ok := matcher(l); ok {
				if wl := lastSeparate(ll, lr); wl != nil {
					iLeft, ei, _ := matcher(Rhs(wl))
					return wl.LeftApply(opConst).RightApply(r).
						EqTrans(associate(iLeft, ei, r))
				}
				return associate(ll, lr, r)
			} else {
				Assert(i == 0)
				return Refl(t)
			}
		}

		// r has 1 element (j), i is in l but not last.
		ll, lr, _ := matcher(l)
		if llLen := decomposeLen(ll); i < llLen { // i is in the first half of l
			return associate(ll, lr, r).
				EqTrans(commute(lr, r).LeftApply(l.(AppliedTerm).Fun())).
				EqTrans(associate(ll, r, lr).EqSym()).
				EqTrans(
					rewrite(Apply(opConst, ll, r), i, llLen).
						LeftApply(opConst).
						RightApply(lr))
		} else { // i is in the second half of l
			return associate(ll, lr, r).
				EqTrans(
					rewrite(Apply(opConst, lr, r), i-llLen, lLen-llLen).
						LeftApply(l.(AppliedTerm).Fun()))
		}
	}
	return rewrite
}

// Merges same or negated terms in a binary op list.
// e.g.
// p ∧ (... ∧ p ∧ ...) = p ∧ ..., p ∧ (... ∧ ¬p ∧ ...) = ⊥
// p ∨ (... ∨ p ∨ ...) = p ∨ ..., p ∨ (... ∨ ¬p ∨ ...) = ⊤
// Rewrite on the top level, but works for the whole series.
func binaryOpMergeRewrite(
	matcher ext.BinaryOpMatcher,
	decompose ext.BinaryOpDecomposer,
	arrange ChainArrangement) Rewrite {
	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		l, r, ok := matcher(t)
		if !ok {
			return nil
		}
		var w *PropWrapper
		list := append(decompose(l), decompose(r)...)

		// in the following double loop, it's always held that i < j
		// so we can calculate keys with index j.
		for j, sj := range list {
			for i, si := range list[:j] {
				// if si = sj || ¬si = sj || si = ¬sj
				if si.AlphaEquals(sj) || negAlphaEquals(si, sj) {
					if w == nil {
						// move the identical terms togeter.
						w = arrange(t, i, j).RewriteConclRhs(DeepBoolRewrite)
					} else {
						// there are multiple terms that need to be merged.
						return w.RewriteConclRhs(rewrite)
					}
				}
			}
		}
		if w != nil {
			return w
		}
		return DeepBoolRewrite(t)
	}
	return verifyRewrite(rewrite)
}

// Simplifies distributive terms.
// p ∧ (p ∨ ...) → p, p ∧ (¬p ∨ ...) → p ∧ ...
// p ∨ (p ∧ ...) → p, p ∨ (¬p ∧ ...) → p ∨ ...
// Shallow rewrite.
func distributeSimplifyRewrite(
	outerMatcher, innerMatcher ext.BinaryOpMatcher,
	innerDecompose ext.BinaryOpDecomposer,
	innerArrange ChainArrangement,
	simplify func(Term, Term) *PropWrapper,
	distribute func(Term, Term, Term) *PropWrapper,
) Rewrite {
	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		l, r, ok := outerMatcher(t)
		if !ok {
			return nil
		}
		rl, rr, ok := innerMatcher(r)
		if !ok {
			return nil
		}

		listR := append(innerDecompose(rl), innerDecompose(rr)...)
		for i := range listR {
			if l.AlphaEquals(listR[i]) {
				w := innerArrange(r, -1, i)
				_, rest, _ := innerMatcher(Rhs(w))
				return w.
					LeftApply(t.Core().(AppliedTerm).Fun()).
					EqTrans(simplify(l, rest))
			}
		}

		var w *PropWrapper
		for i := range listR {
			if negAlphaEquals(l, listR[i]) {
				if w == nil {
					u := innerArrange(r, -1, i)
					n, rest, _ := innerMatcher(Rhs(u))
					w = u.
						LeftApply(t.Core().(AppliedTerm).Fun()).
						EqTrans(distribute(l, n, rest)).
						RewriteConclRhs(DeepBoolRewrite)
				} else {
					// there are multiple terms that need to be merged.
					return w.RewriteConclRhs(rewrite)
				}
			}
		}
		if w != nil {
			return w
		}
		return DeepBoolRewrite(t)
	}
	return verifyRewrite(rewrite)
}

// Generate binary ops cross clauses redundant rewrites.
// E.g. ... ∧ p ∧ ... ∧ (... ∨ p ∨ ...) ∧ ...
// or ... ∧ p ∧ ... ∧ (... ∨ ¬p ∨ ...) ∧ ...
// or ... ∧ (p ∨ q) ∧ ... ∧ (... ∨ p ∨ ... ∨ q ∨...) ∧ ...
// Only works for the top level. Should not be called recursively.
func crossBinaryOpSimplifyRewrite(
	outerOpConst, innerOpConst ConstTerm,
	outerMatcher, innerMatcher ext.BinaryOpMatcher,
	outerDecompose, innerDecompose ext.BinaryOpDecomposer,
	outerArrange, innerArrange ChainArrangement,
	outerMerge, innerMerge, distribute, simplify Rewrite,
	outerCommute func(Term, Term) *PropWrapper,
) Rewrite {
	mergeMap := decomposeMapRewrite(outerOpConst, outerMatcher, innerMerge)
	simplifyMap := decomposeMapRewrite(innerOpConst, innerMatcher,
		func(s Term) *PropWrapper {
			l, r, _ := outerMatcher(s)
			return outerCommute(l, r).RewriteConclRhs(simplify)
		})

	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		if _, _, ok := outerMatcher(t); !ok {
			return nil
		}

		w := RewriteOrRefl(mergeMap, t).RewriteConclRhs(outerMerge)

		outerList := outerDecompose(Rhs(w))
		innerList := make([][]Term, len(outerList))

		// in the following double loop, it's always held that i < j
		// so we can calculate keys with index j.
		for j, sj := range outerList {
			if l, r, ok := innerMatcher(sj); ok {
				innerList[j] = append(innerDecompose(l), innerDecompose(r)...)
			}

			for i, si := range outerList[:j] {
				siList, sjList := innerList[i], innerList[j]
				// si ⊆ sj
				if siList != nil && utils.IsSubset(siList, sjList, Term.AlphaEquals) {
					u := outerCommute(si, sj).
						RewriteConclRhs(distribute).
						RewriteConclRhs(simplifyMap)
					return w.
						EqTrans(outerArrange(Rhs(w), i, j)).
						eqRewriteConclRhs(u).
						RewriteConclRhs(rewrite)
				}

				// sj ⊆ si
				if sjList != nil && utils.IsSubset(sjList, siList, Term.AlphaEquals) {
					u := distribute(Apply(outerOpConst, si, sj)).
						RewriteConclRhs(simplifyMap)
					return w.
						EqTrans(outerArrange(Rhs(w), i, j)).
						eqRewriteConclRhs(u).
						RewriteConclRhs(rewrite)
				}

				for k, sjk := range sjList {
					// sj contains ... sjk ... where sjk is either si or ¬si
					if si.AlphaEquals(sjk) || negAlphaEquals(si, sjk) {
						// move sjk to the first position inside sj
						u := innerArrange(sj, -1, k).
							// si . (sjk . (rest of sj))
							LeftApply(Apply(outerOpConst, si)).
							RewriteConclRhs(simplify)
						return w.
							// move sj to the right of si
							EqTrans(outerArrange(Rhs(w), i, j)).
							eqRewriteConclRhs(u).
							RewriteConclRhs(rewrite)
					}
				}

				for k, sik := range siList {
					// si contains ... sik ... where sik is either sj or ¬sj
					if sj.AlphaEquals(sik) || negAlphaEquals(sj, sik) {
						u := outerCommute(si, sj).
							EqTrans(
								// move sik to the first position inside si
								innerArrange(si, -1, k).
									// sj . (sik . (rest of si))
									LeftApply(Apply(outerOpConst, sj))).
							RewriteConclRhs(simplify)
						return w.
							// move sj to the left of si
							EqTrans(outerArrange(Rhs(w), i, j)).
							eqRewriteConclRhs(u).
							RewriteConclRhs(rewrite)
					}
				}
			}
		}
		if !Rhs(w).AlphaEquals(t) {
			return w
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

// Generate binary ops components sorting rewrites
// Only works for the top level. Should not be called recursively.
func BinaryOpSortRewrite(
	matcher ext.BinaryOpMatcher,
	decompose ext.BinaryOpDecomposer,
	chainArrangement ChainArrangement,
	simplifyRewrite, assocRewrite Rewrite,
) Rewrite {
	return binaryOpSortRewriteWithCompare(
		matcher, decompose, chainArrangement, simplifyRewrite, assocRewrite,
		func(t0, t1 Term) int { return t0.Compare(t1) })
}

func binaryOpSortRewriteWithCompare(
	matcher ext.BinaryOpMatcher,
	decompose ext.BinaryOpDecomposer,
	chainArrangement ChainArrangement,
	simplifyRewrite, assocRewrite Rewrite,
	compare func(Term, Term) int,
) Rewrite {
	rewrite := func(t Term) *PropWrapper {
		if _, _, ok := matcher(t); !ok {
			return nil
		}

		_t, w := t, simplifyRewrite(t)
		if w != nil {
			_t = Rhs(w)
		}
		list := decompose(_t)
		orderedTerms := []Term{list[0]}

		for j, term := range list[1:] {
			i, _ := slices.BinarySearchFunc(orderedTerms, term, compare)
			if j+1 != i { // otherwise no need to move.
				if u := chainArrangement(_t, i-1, j+1); u != nil {
					if w == nil {
						w = u
					} else {
						w = w.EqTrans(u)
					}
					_t = Rhs(w)
				}
			}
			orderedTerms = slices.Insert(orderedTerms, i, term)
		}
		if w == nil {
			return assocRewrite(t)
		}
		w = w.RewriteConclRhs(assocRewrite)
		if !Rhs(w).AlphaEquals(t) {
			return w
		}
		return nil
	}
	return verifyRewriteOpen(rewrite)
}

func skolemRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		tAbs := MatchesFORALL(t)
		if tAbs.IsZero() {
			return nil
		}
		if sAbs := MatchesEXISTS(tAbs.Body()); !sAbs.IsZero() {
			f := core.Var(
				TermName(utils.Subscript(utils.F_HOOK, 0)),
				MakeFun(tAbs.Var().Type(), sAbs.Var().Type())).RenameToAvoid(t)
			if w := DeepBeta(t); w != nil {
				// The skolem function contains a deep β step, so we β-collapse
				// here in advance.
				return w.EqTrans(
					Skolem(f, Abs(tAbs.Var(), ext.BetaCollapse(context.Background(), sAbs))))
			}
			return Skolem(f, Abs(tAbs.Var(), ext.BetaCollapse(context.Background(), sAbs)))
		}
		if sAbs := MatchesUNIQUE(tAbs.Body()); !sAbs.IsZero() {
			f := core.Var(
				TermName(utils.Subscript(utils.F_HOOK, 0)),
				MakeFun(tAbs.Var().Type(), sAbs.Var().Type())).RenameToAvoid(t)
			// it's possible that the skolem function changes the body of t
			if w := DeepBeta(t); w != nil {
				// The skolem function contains a deep β step, so we β-collapse
				// here in advance.
				return w.EqTrans(
					SkolemAltUnique(f, Abs(tAbs.Var(), ext.BetaCollapse(context.Background(), sAbs))))
			}
			return SkolemAltUnique(f, Abs(tAbs.Var(), sAbs))
		}
		return nil
	}
	return verifyRewrite(rewrite)
}

func forAllANDRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		tAbs := MatchesFORALL(t)
		if tAbs.IsZero() {
			return nil
		}
		x := tAbs.Var()
		// (∀x.s) = s if x is not a free var in s
		if !tAbs.Body().HasFree(x) {
			return MootForAll(x, tAbs.Body())
		}
		l, r, ok := MatchesAND(tAbs.Body())
		if !ok {
			return nil
		}
		// ∀x.(l ∧ r) = (∀x.l ∧ ∀x.r)
		return ForAllAND(Abs(x, l), Abs(x, r))
	}
	return verifyRewrite(rewrite)
}

func existsORRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		tAbs := MatchesEXISTS(t)
		if tAbs.IsZero() {
			return nil
		}
		x := tAbs.Var()
		// (∃x.s) = s if x is not a free var in s
		if !tAbs.Body().HasFree(x) {
			return MootExists(x, tAbs.Body())
		}
		l, r, ok := MatchesOR(tAbs.Body())
		if !ok {
			return nil
		}
		// ∃x.(l ∨ r) = (∃x.l ∨ ∃x.r)
		return ExistsOR(Abs(x, l), Abs(x, r))
	}
	return verifyRewrite(rewrite)
}

// Given a term with ∀ quantifiers and disjunctive body, find the term groups that contains
// the first quantifier var and can be separated from other disjunctive components.
// For example, given ∀x.∀y.∀z.(P(x) ∨ P(y) ∨ Q(x, z))
// Returns var set {x, z}, indices {0, 2}, relevant term P(x) ∨ Q(x, z), rest term P(y)
// and whether the whole term is divisible (in this case yes).
func forAllDisjunctiveGroupFirst(t Term) (*VarList, []int, Term, Term, bool) {
	vars, s := DecomposesFORALL(t)
	if vars.Empty() {
		return nil, nil, nil, nil, false
	}
	components := DecomposesOR(s)
	if len(components) == 1 {
		return nil, nil, nil, nil, false
	}
	v := vars.Ind(0)
	selectedVars := VarList{}
	selectedVars.Add(v)
	var selectedIndices []int
	queue := []VarTerm{v}
	for len(queue) > 0 {
		_v := queue[0]
		for i, component := range components {
			j, found := slices.BinarySearch(selectedIndices, i)
			if !found && component.HasFree(_v) {
				selectedIndices = slices.Insert(selectedIndices, j, i)
				for _, x := range component.Frees(vars.Has) {
					if selectedVars.HasNo(x) {
						selectedVars.Add(x)
						queue = append(queue, x)
					}
				}
			}
		}
		queue[0], queue = VarTerm{}, queue[1:]
	}
	if len(selectedIndices) == len(components) {
		return &vars, selectedIndices, s, nil, false
	}

	relevantTerms := make([]Term, 0, len(components))
	restTerms := make([]Term, 0, len(components))
	i := 0
	for j, term := range components {
		if i < len(selectedIndices) && j == selectedIndices[i] {
			relevantTerms = append(relevantTerms, term)
			i++
		} else {
			restTerms = append(restTerms, term)
		}
	}
	Assert(len(relevantTerms) > 0 && len(restTerms) > 0)
	relevantTerm, restTerm := Or(relevantTerms...), Or(restTerms...)
	return &selectedVars, selectedIndices, relevantTerm, restTerm, true
}

func forAllORRewriteImpl() Rewrite {
	pushLeft := PrenexThms["(∀x.P(x)) ∨ Q ⇔ ∀x.(P(x) ∨ Q)"]
	pushRight := PrenexThms["Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))"]
	var rewrite Rewrite
	rewrite = func(t Term) *PropWrapper {
		selectedVars, selectedIndices, relevantTerm, restTerm, ok :=
			forAllDisjunctiveGroupFirst(t)
		if !ok {
			return AssocORRewrite(t)
		}

		// Now selectedIndices are indices of terms contains selected vars.
		Assert(slices.IsSorted(selectedIndices))

		_restTerm, _relevantTerm := restTerm, relevantTerm
		vars, body := DecomposesFORALL(t)
		Assert(!vars.Empty())
		// For later uses.
		pushLeftProps := make([]*PropWrapper, selectedVars.Size())
		pushRightProps := make([]*PropWrapper, vars.Size())
		var restResult *PropWrapper
		wg := utils.Tasks{}
		for i, v := range selectedVars.Backward() {
			_relevantTerm = ForAll(v)(_relevantTerm)
			s := _relevantTerm.Core().(AppliedTerm).Arg()
			wg.Go(func() {
				pushLeftProps[i] = pushLeft(s, restTerm).EqSym()
			})
		}
		for i, v := range vars.Backward() {
			if selectedVars.Has(v) {
				continue
			}
			_restTerm = ForAll(v)(_restTerm)
			s := _restTerm.Core().(AppliedTerm).Arg()
			wg.Go(func() {
				pushRightProps[i] = pushRight(s, _relevantTerm).EqSym()
			})
		}
		// Start rewriting the rest part in parallel.
		wg.Go(func() { restResult = rewrite(_restTerm) })

		// Reorder OR components such that relevant terms are at first.
		u := Refl(body)
		for i, j := range selectedIndices {
			u = u.EqTrans(ArrangeORChain(Rhs(u), i-1, j))
		}
		u = u.RewriteConclRhs(AssocORRewrite)
		// separate v-relevant terms and rest.
		if v := AssocORRewrite(Or(relevantTerm, restTerm)); v != nil {
			u = u.EqTrans(v.EqSym())
		}

		// rewrite t using u.
		w := RewriteOrRefl(EqReplacementRewrite(u), t)

		// push selected vars to innermost while keeping the in-group order.
		if vars, _t := DecomposesFORALL(Rhs(w)); !vars.Empty() {
			for _, v := range selectedVars.Backward() {
				_t = ForAll(v)(_t)
			}
			for _, v := range vars.Backward() {
				if selectedVars.HasNo(v) {
					_t = ForAll(v)(_t)
				}
			}
			// now t is the term with the desired univ quantifiers order.
			w = w.EqTrans(ReorderForAll(Rhs(w), _t))
		}

		wg.Wait()
		// attach v on v-relevant terms
		for _, p := range slices.Backward(pushLeftProps) {
			w = w.eqReplacementConclRhs(p)
		}
		// attach rest vars on rest terms
		for _, p := range slices.Backward(pushRightProps) {
			if p != nil {
				w = w.eqReplacementConclRhs(p)
			}
		}
		// add the rest result
		if restResult != nil {
			w = w.eqReplacementConclRhs(restResult)
		}
		return w.RewriteConclRhs(AssocORRewrite)
	}
	return verifyRewrite(rewrite)
}

func existsANDRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		_, body := DecomposesEXISTS(t)
		if _, _, ok := MatchesAND(body); !ok {
			return nil
		}

		u := DeepNegRewrite(Not(t))
		Assert(u != nil)

		if w := ForAllORRewrite(Rhs(u)); w != nil {
			u = u.EqTrans(w)
		} else {
			return nil
		}

		return DoubleNeg(t).
			EqSym().
			EqTrans(u.LeftApply(NOT).RewriteConclRhs(DeepNegRewrite))
	}
	return verifyRewrite(rewrite)
}

func boundVarRewriteImpl(old, new VarTerm) Rewrite {
	if old.Equals(new) {
		return NilRewrite
	}

	// subTermsRewrite is predefined so it doesn't need allocation
	// for every rewriteWithEnv calls.
	var rewriteWithEnv, subTermsRewrite RewriteWithEnv
	var rewrite Rewrite

	// check whether the current level can be rewritten.
	rewriteWithEnv = func(t Term, env ...VarTerm) *PropWrapper {
		if t, ok := t.AsAbsTerm(); ok {
			if t.Var().Equals(old) {
				n := new.Name()
				for ext.NameInVars(env, n) || t.HasName(n) {
					n = utils.NextName(n)
				}
				return Refl(t.ChangeAbsVar(n))
			}
		}

		// the rewriteConclRhsRecur part guarantee that this is a recursive run.
		if s := subTermsRewrite(t, env...); s != nil {
			return s.RewriteConclRhsRecur(rewrite)
		}
		return nil
	}

	rewrite = func(t Term) *PropWrapper { return rewriteWithEnv(t) }

	// rewrite the immediate subterms.
	// since rewriteWithEnv is passed into RewriteSubTermsWithEnv,
	// it will keep going down.
	subTermsRewrite = RewriteSubTermsWithEnv(
		rewriteWithEnv,
		utils.EmptyPredicate)

	// No verifyRewrite because it keeps the term α-equal.
	return rewrite
}
