/**
 * File: prop_wrapper.go
 *
 * Wrapper for propositions with additional methods for inference rules.
 *
 * Axiomatic rules:
 * - Refl: ⊢ t = t
 * - Assume: t ⊢ t
 * - Beta: (λx.t)(x) = t
 * - Eta: λx.(t(x)) = t (provided x is not in t)
 * - Select: P(x) ⊢ P(εP)
 *
 * Inference rules:
 * - Apply:
 * 		{h0} ⊢ l = r
 * 		{h1} ⊢ a = b
 * 		------------------
 * 		{h0} + {h1} ⊢ l(a) = r(b)
 * - LeftApply:
 * 		{h0} ⊢ a = b
 * 		------------------
 * 		{h0} ⊢ l(a) = l(b)
 * - RightApply:
 * 		{h0} ⊢ l = r
 * 		------------------
 * 		{h0}⊢ l(a) = r(a)
 * - Abs:
 * 		{h0} ⊢ l = r
 * 		------------------
 * 		{h0} ⊢ λx.l = λx.r
 * - EqMP:
 * 		{h0} ⊢ l = r
 * 		{h1} ⊢ l
 * 		------------------
 * 		{h0} + {h1} ⊢ r
 * - Deduct:
 * 		{h0}, l ⊢ r
 * 		{h1}, r ⊢ l
 * 		--------------------
 * 		{h0} + {h1} ⊢ l = r
 * - DeriveTrans:
 *		{h0} ⊢ l
 * 		{h1}, l ⊢ r
 * 		--------------------
 * 		{h0} + {h1}, l ⊢ r
 * - EqTrans:
 *		{h0} ⊢ l = m
 * 		{h1} ⊢ m = r
 * 		--------------------
 * 		{h0} + {h1} ⊢ l = r
 * - EqSym:
 * 		{h0} ⊢ l = r
 * 		------------------
 * 		{h0} ⊢ r = l
 *
 * - TypeInst: type substitution in a proposition
 * - TermInst: term substitution in a proposition
 *
 * Derived methods:
 * - PromoteHyp:
 * 		..., h ⊢ c
 * 		----------
 * 		... ⊢ h ⇒ c
 * - NegHyp:
 * 		..., h ⊢ ⊥
 * 		-------------
 * 		... ⊢ ¬h
 * - NegConcl:
 * 		... ⊢ c
 * 		-------------
 * 		..., ¬c ⊢ ⊥
 * - DemoteHyp:
 * 		... ⊢ h ⇒ c
 * 		--------------
 * 		..., h ⊢ c
 * - LeftAssume:
 * 		... ⊢ l = r
 * 		--------------
 * 		..., l ⊢ r
 * - RightAssume:
 * 		... ⊢ l = r
 * 		--------------
 * 		..., r ⊢ l
 * - ConclForAll (provided x not free in hyps):
 * 		... ⊢ c
 * 		-------------
 * 		... ⊢ ∀x.c
 * - ConclForAllInst:
 * 		... ⊢ ∀x.c
 * 		-------------
 * 		... ⊢ c(s)
 * - ConclForAllInsts (iterated ConclForAllInst):
 * 		... ⊢ ∀x₀…xₙ.c   (args s₀…sₖ)
 * 		-------------
 * 		... ⊢ c[x₀:=s₀]…
 * - StripConclForAll (iterated at each binder's own var):
 * 		... ⊢ ∀x₀…xₙ.c
 * 		-------------
 * 		... ⊢ c   (+ the freed vars x₀…xₙ, for ConclForAllList)
 * - ConclForAllList (iterated ConclForAll; inverse of StripConclForAll):
 * 		... ⊢ c
 * 		-------------
 * 		... ⊢ ∀x₀…xₙ.c
 * - ConclExistsInst:
 * 		... ⊢ c
 * 		-------------
 * 		... ⊢ ∃x.c
 * - HypExists (provided x not free in other hyps and conclusion):
 * 		..., h ⊢ c
 * 		-------------
 * 		..., ∃x.h ⊢ c
 * - HypForAllInst:
 * 		..., h ⊢ c
 * 		-------------
 * 		..., ∀x.h ⊢ c
 * - ConclSelectExists (s is an introduced term that equals the selected element):
 * 		... ⊢ ∃x.P(x)
 * 		-------------------------
 * 		..., s = εx.P(x) ⊢ P(s)
 * - RemoveHyps:
 * 		h, ... ⊢ c
 * 		----------------
 * 		⊢ c ∨ ¬h ∨ ...
 * - RemoveVarHyp (x is a var that is not appearing anywhere else):
 * 		..., x = _ ⊢ t
 * 		-------------
 * 		... ⊢ t
 */

package prop

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

type PropWrapper struct{ Prop }

func WrapProp(p Prop) *PropWrapper { return &PropWrapper{p.Core()} }

// Wraps axiomatic inference rules: Refl, Assume, Beta, Eta, Select.
func wrapAxiomaticProp[T Term](f func(T) Thm) func(Term) *PropWrapper {
	return func(t Term) *PropWrapper { return WrapProp(f(t.Core().(T))) }
}

// axiomatic inference rules
var (
	// t --> ⊢ t = t
	Refl = wrapAxiomaticProp(core.Refl)

	// t: bool --> t ⊢ t
	// panic for non boolean.
	Assume = wrapAxiomaticProp(core.Assume)

	// (λx.t)(x) --> ⊢ (λx.t)(x) = t
	Beta = wrapAxiomaticProp(core.Beta)

	// t(x) --> ⊢ λx.(t(x)) = t
	// provided x is not in t.
	// panic when not matching.
	Eta = wrapAxiomaticProp(core.Eta)

	// Axiom of ε-calculus
	// P(x): bool --> P(x) ⊢ P(εP)
	// panic when not matching.
	Select = wrapAxiomaticProp(core.Select)
)

// {h0} ⊢ f = g
// {h1} ⊢ a = b
// -------------------------
// {h0} + {h1} ⊢ f a = g b
// panic when not matching.
func (t0 *PropWrapper) Apply(t1 Prop) *PropWrapper {
	return WrapProp(core.PropApply(t0, t1))
}
func (t0 *PropWrapper) LeftApply(term Term) *PropWrapper {
	return WrapProp(core.PropLeftApply(term, t0))
}
func (t0 *PropWrapper) RightApply(term Term) *PropWrapper {
	return WrapProp(core.PropRightApply(t0, term))
}

// ... ⊢ l = r
// ------------------
// ... ⊢ λx.l = λx.r
// provided x is not in hyps
// panic when not matching.
func (t *PropWrapper) Abs(v Term) *PropWrapper {
	return WrapProp(core.PropAbs(v.Core().(VarTerm), t))
}

// {h0} ⊢ l = r
// {h1} ⊢ l
// ------------------
// {h0} + {h1} ⊢ r
// panic when not matching.
func (t0 *PropWrapper) EqMP(t1 Prop) *PropWrapper {
	return WrapProp(core.EqMP(t0, t1))
}

// {h0}, r ⊢ l
// {h1}, l ⊢ r
// ---------------------
// {h0} + {h1} ⊢ l = r
// never panic.
func (t0 *PropWrapper) Deduct(t1 Prop) *PropWrapper {
	return WrapProp(core.Deduct(t0, t1))
}

// {h0} ⊢ l
// {h1}, l ⊢ r
// --------------------
// {h0} + {h1} ⊢ r
// Panic when the conclusion of t0 is not one of the hyps of t1.
func (t0 *PropWrapper) DeriveTrans(t1 Prop) *PropWrapper {
	// This assersion is not necessary for the line below to work.
	// However, sometimes it is a sign of some hidden bugs if it doesn't hold,
	// so we check it here to make sure.
	Assert(t1.HasHyp(t0.Conclusion()))
	return WrapProp(core.DeriveTrans(t0, t1))
}

// Reverse direction of deriveTrans.
func (t0 *PropWrapper) DeriveHypFrom(t1 Prop) *PropWrapper {
	return WrapProp(t1).DeriveTrans(t0)
}

// If t1 contains the conclusion of t0 as a hyp, derives that hyp
// using t0, otherwise does nothing.
func (t0 *PropWrapper) MaybeDeriveTrans(t1 Prop) Prop {
	if t1.HasHyp(t0.Conclusion()) {
		return core.DeriveTrans(t0, t1)
	}
	return t1
}

// {h0} ⊢ l = m
// {h1} ⊢ m = r
// ---------------------
// {h0} + {h1} ⊢ l = r
// panic when not matching.
func (t0 *PropWrapper) EqTrans(t1 Prop) *PropWrapper {
	return WrapProp(core.EqTrans(t0, t1))
}

// ... ⊢ l = r
// -------------
// ... ⊢ r = l
// panic if not an equality.
func (t *PropWrapper) EqSym() *PropWrapper {
	return WrapProp(core.EqSym(t))
}

func (t *PropWrapper) TypeInst(subst ...TypeSubst) *PropWrapper {
	return WrapProp(core.PropTypeInst(t, subst...))
}

func (t *PropWrapper) TermInst(subst ...TermSubst) *PropWrapper {
	return WrapProp(core.PropTermInst(t, subst...))
}

// ..., h ⊢ c
// -------------
// ... ⊢ h ⇒ c
// if h is not a hyp of t, this still works (by directly adding h).
func (t *PropWrapper) PromoteHyp(h Term) *PropWrapper {
	w := ExpandDef(IMPLY, h, t.Conclusion()).
		EqSym().
		EqMP(t.
			Deduct(ConclAND(h, t.Conclusion())). // ..., h ⊢ c = h ∧ c
			EqMP(t).                             // ..., h ⊢ h ∧ c
			Deduct(HypAND0(h, t.Conclusion())))  // ... ⊢ h ∧ c = h
	Assert(!w.HasHyp(h))
	return w
}

// ..., h ⊢ ⊥
// -------------
// ... ⊢ ¬h
// if h is not a hyp of t, this still works (by directly adding h).
func (t *PropWrapper) NegHyp(h Term) *PropWrapper {
	Assert(t.Conclusion().Equals(F))
	return ImpliesFalse(h).EqMP(t.PromoteHyp(h))
}

// ... ⊢ c
// -------------
// ..., ¬c ⊢ ⊥
func (t *PropWrapper) NegConcl() *PropWrapper {
	if t.Conclusion().Equals(F) {
		return t
	}
	return t.DeriveTrans(Contradict(t.Conclusion()))
}

// ... h ⊢ c
// -------------
// ... ¬c ⊢ ¬h
// if h is not a hyp of t, this still works (by directly adding h).
func (t *PropWrapper) Contraposition(h Term) *PropWrapper {
	return t.NegConcl().NegHyp(h)
}

// ... ⊢ h ⇒ c
// --------------
// ..., h ⊢ c
func (t *PropWrapper) DemoteHyp() *PropWrapper {
	h, c, ok := MatchesIMPLY(t.Conclusion())
	Assert(ok)
	return t.DeriveTrans(ModusPonens(h, c))
}

// ... ⊢ l = r
// --------------
// ..., l ⊢ r
func (t *PropWrapper) LeftAssume() *PropWrapper {
	l, _, ok := MatchesIFF(t.Conclusion())
	Assert(ok)
	return t.EqMP(Assume(l))
}

// ... ⊢ l = r
// --------------
// ..., r ⊢ l
func (t *PropWrapper) RightAssume() *PropWrapper {
	_, r, ok := MatchesIFF(t.Conclusion())
	Assert(ok)
	return t.EqSym().EqMP(Assume(r))
}

// ... ⊢ c
// ------------
// ... ⊢ ∀x.c
// provided x not free in hyps
func (t *PropWrapper) ConclForAll(x VarTerm) *PropWrapper {
	Assert(NotFreeInHyps(t, x))
	w := t.Deduct(DerivesTrue).Abs(x)
	return expandFORALL.
		EqSym().
		TypeInst(MakeTypeSubst(TypeA, x.Type())).
		TermInst(makeTermSubstWithType(initVars.P, Lhs(w))).
		EqMP(w)
}

// ... ⊢ ∀x.c
// -------------
// ... ⊢ c(s)
func (t *PropWrapper) ConclForAllInst(s Term) *PropWrapper {
	return t.DeriveTrans(InstForAll(t.Conclusion(), s))
}

// ... ⊢ ∀x₀…xₙ.c   (and args s₀…sₖ)
// ----------------------------------
// ... ⊢ c[x₀:=s₀]…[xₖ:=sₖ]
// Iterated ConclForAllInst: instantiate the leading ∀'s at the given
// terms in order, stopping when the args are exhausted or the conclusion is no
// longer ∀-headed.
func (t *PropWrapper) ConclForAllInsts(ss ...Term) *PropWrapper {
	for _, s := range ss {
		if MatchesFORALL(t.Conclusion()).IsZero() {
			break
		}
		t = t.ConclForAllInst(s)
	}
	return t
}

// ... ⊢ ∀x₀…xₙ.c
// ------------------
// ... ⊢ c        (returns x₀…xₙ, outer→inner)
// Iterated ConclForAllInst at each binder's OWN variable: strip
// every leading ∀, freeing each bound var, and return the freed vars in binding
// order so ConclForAllList can re-generalize. A binder whose name is free in a
// hypothesis is first renamed to a fresh variant, so every returned var stays
// re-generalizable (the ConclForAll guard) — an assumption-aware
// renaming. For ∀-closed, hyp-free props (the common case) nothing is renamed.
func (t *PropWrapper) StripConclForAll() (*PropWrapper, []VarTerm) {
	var vars []VarTerm
	for abs := MatchesFORALL(t.Conclusion()); !abs.IsZero(); abs = MatchesFORALL(t.Conclusion()) {
		v := abs.Var()
		if !NotFreeInHyps(t, v) {
			n := v.Name()
			for !NotFreeInHyps(t, core.Var(n, v.Type())) || t.Conclusion().HasFreeName(n) {
				n = utils.NextName(n)
			}
			v = core.Var(n, v.Type())
		}
		t = t.ConclForAllInst(v)
		vars = append(vars, v)
	}
	return t, vars
}

// ... ⊢ c
// --------------------
// ... ⊢ ∀x₀…xₙ.c   (xs = x₀…xₙ, x₀ outermost)
// Iterated ConclForAll: generalize the conclusion over xs with the
// first var outermost — the exact inverse of StripConclForAll. Each step
// requires its var not free in the hyps (the ConclForAll guard).
func (t *PropWrapper) ConclForAllList(xs ...VarTerm) *PropWrapper {
	for i := len(xs) - 1; i >= 0; i-- {
		t = t.ConclForAll(xs[i])
	}
	return t
}

// ... ⊢ c
// ------------
// ... ⊢ ∃x.c
func (t *PropWrapper) ConclExistsInst(x VarTerm) *PropWrapper {
	return t.DeriveTrans(InstExists(Exists(x)(t.Conclusion()), x))
}

// ..., h ⊢ c
// ---------------
// ..., ∃x.h ⊢ c
// provided x not free in other hyps and conclusion
func (t *PropWrapper) HypExists(x VarTerm, h Term) *PropWrapper {
	Assert(t.HasHyp(h) &&
		!t.Conclusion().HasFree(x) &&
		NotFreeInHyps(t, x, h))

	hilbert := core.Hilbert(x, h)
	return t.
		TermInst(MakeTermSubst(x, hilbert)).
		DeriveHypFrom(SelectExists(hilbert.Arg()))
}

// ..., h ⊢ c
// ---------------
// ..., ∀x.h ⊢ c
func (t *PropWrapper) HypForAllInst(x VarTerm, h Term) *PropWrapper {
	return t.DeriveHypFrom(InstForAll(ForAll(x)(h), x))
}

// ... ⊢ ∃x.P(x)
// -------------------------
// ..., s = εx.P(x) ⊢ P(s)
// where s is an introduced term that equals the selected element.
func (t *PropWrapper) ConclSelectExists(s Term) *PropWrapper {
	abs := MatchesEXISTS(t.Conclusion())
	Assert(!abs.IsZero())
	hilbert := Const(core.MetaHilbert(),
		MakeFun(MakeFun(abs.Var().Type(), TypeBool), abs.Var().Type()))
	return Assume(Eq(s, hilbert.Apply(abs))).
		EqSym().
		LeftApply(abs).
		RewriteConcl(DeepBetaAbs(abs)).
		EqMP(t.DeriveTrans(SelectExists(abs)))
}

// h, ... ⊢ c
// ----------------
// ⊢ c ∨ ¬h ∨ ...
// Move hyps to the conclusion side as disjunction.
// only move the hyps that satisfies the given predicate.
// if the predicate is nil, move all hyps.
func (t *PropWrapper) MoveHypsToConcl(prediacate utils.Predicate[Term]) *PropWrapper {
	if t.NumHyps() == 0 {
		return t
	}
	for h := range t.HypIter() {
		if prediacate == nil || prediacate(h) {
			if t.Conclusion().Equals(F) {
				return t.NegHyp(h).MoveHypsToConcl(prediacate)
			}
			return BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](h, t.Conclusion()).
				EqTrans(CommuteOR(Not(h), t.Conclusion())).
				EqMP(t.PromoteHyp(h)).
				MoveHypsToConcl(prediacate)
		}
	}
	return t
}

// ⊢ ... ∨ ¬h ∨ ...
// ----------------
// h, ... ⊢ c
// Move selected disjunctive component in conclusion to hyps side.
func (t *PropWrapper) MoveConclDisjComponentToHyp(h Term) *PropWrapper {
	nh := Not(h)
	if t.Conclusion().AlphaEquals(nh) {
		// This means that the original prop is h ⊢ ⊥
		return Contradict(h).DeriveHypFrom(t)
	}

	components := DecomposesOR(t.Conclusion())
	i := slices.IndexFunc(components, nh.AlphaEquals)
	// It's caller's responsibility to assure h can be found.
	Assert(i >= 0)
	// move ¬h to the first position among the disjunction
	// the conclusion is in the form of ⊢ (¬h ∨ rest)
	t = ArrangeORChain(t.Conclusion(), -1, i).EqMP(t)
	_nh, rest, ok := MatchesOR(t.Conclusion())
	Assert(ok && _nh.Equals(nh))
	// (¬h ∨ rest) becomes h ⊢ rest
	return BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](h, rest).
		EqSym().
		EqMP(t).
		DemoteHyp()
}

// ⊢ rest ∨ ¬h
// ----------------
// h, ... ⊢ rest
// Demote the RIGHTMOST disjunctive component of the conclusion into a
// hypothesis, positionally — no search for a matching ¬h.
//
// MoveConclDisjComponentToHyp(h) above finds the FIRST disjunct α-matching
// `¬h` and moves it; that is ambiguous when the same `¬h` disjunct occurs
// more than once. This happens during Normalize's reconstruct when a hyp
// `h` has its negation `¬h` ALSO present as a disjunct of the original
// conclusion φ: MoveHypsToConcl then produces `φ ∨ … ∨ ¬h` with two `¬h`
// disjuncts, and the search-based undo removes φ's own `¬h` (which must
// stay) instead of the appended one — corrupting the reconstruction and
// eventually tripping the pop-loop on a positive disjunct.
//
// MoveHypsToConcl appends each `¬hi` as the rightmost disjunct, so the
// reconstruct peels rightmost-first (hyps come back in reverse order) and
// never touches a `¬h` belonging to φ. This positional peel is the exact
// inverse of that append.
func (t *PropWrapper) MoveConclLastDisjComponentToHyp() *PropWrapper {
	rest, nh, ok := MatchesOR(t.Conclusion())
	Assert(ok)
	h := MatchesNOT(nh)
	Assert(h != nil)
	// (rest ∨ ¬h) ⇔ (¬h ∨ rest), then demote ¬h to hyp h.
	t = CommuteOR(rest, nh).EqMP(t)
	return BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](h, rest).
		EqSym().
		EqMP(t).
		DemoteHyp()
}

// ..., x = _ ⊢ t
// ----------------
// ... ⊢ t
// x is a var that is not appearing anywhere else.
func (t *PropWrapper) RemoveVarHyp(x VarTerm) *PropWrapper {
	for h := range t.HypIter() {
		if v, r, ok := MatchesEQ(h); ok &&
			x.Equals(v) &&
			!r.HasFree(x) &&
			!t.Conclusion().HasFree(x) &&
			NotFreeInHyps(t, x, h) {
			return t.
				TermInst(MakeTermSubst(v, r)).
				DeriveHypFrom(Refl(r))
		}
	}
	panic("Nothing to remove.")
}

func (t *PropWrapper) String() string { return PrintProp(t) }
