// set_tac_fuse.go — the ∃-one-point FUSION rule of membership-mode
// set_tac (the one-point unwinding class):
//
//	∃w. (∃u₁…∃uₖ. P ∧ (w = T)) ∧ R(w)   ⇔   ∃u₁…∃uₖ. P ∧ R[w:=T]
//
// This is what makes the class of `s ∩ ⋃f = ⋃{s ∩ t | t ∈ f}` refutable at all. The
// comprehension collapse leaves the set witness as an EQUATION
// `w = intersection u t` under the big_union-produced ∃w. Sets are function-typed,
// and the refuter's pre-CNF normalization (prop.FunEqRewrite — see
// ext/clause/funext.go's header) dissolves every function-typed equality
// into pointwise form before clause extraction; under the ⇒-direction's
// NEGATIVE polarity the dissolved form skolemizes and the witness TERM
// becomes unsynthesizable — refuted probes: the equation form idles out
// at 30s, the fused form closes in 70ms.
// Fusing substitutes the witness through BEFORE the refuter sees the
// goal: the equation disappears, R[w:=T] re-exposes membership redexes
// (`(intersection u t)(x)`) that the next fixpoint pass consumes, and the
// residual is pure first-order.
//
// The gate is deliberately RIGID — exactly the shape our own
// set_comprehension/comprehension_spec collapse emits (comprehension_spec := λv P t. P ∧ (v = t), so the
// equality is the right conjunct of the innermost AND; the ∃u⃗ prefix is
// the comprehension's parameter block; the fused conjunct may sit on
// either side of the outer AND — the bridge mirrors the matched order).
// P, R and T must already be β-normal (redexes belong to the driver's
// own β pass, which runs the fixpoint before this rule fires again).
// Any mismatch declines — soundness never depends on the gate, only
// coverage does — and every composition against a precondition Assert
// is guarded so residual mismatches decline instead of panicking.
//
// The bridge is pure kernel composition (Assume/Deduct/InstExists/
// HypExists/ConclAND/HypAND + one β) — no search, deterministic, no
// cited deps.

package tactic

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// existsOnePointFuse matches the fusion shape at t and returns the
// bridge `⊢ t ⇔ fused` — nil when the gate declines.
func existsOnePointFuse(t core.Term) *prop.PropWrapper {
	wAbs := ext.MatchesEXISTS(t)
	if wAbs.IsZero() {
		return nil
	}
	w := wAbs.Var()
	l, r, ok := ext.MatchesAND(wAbs.Body())
	if !ok {
		return nil
	}
	// The comprehension conjunct may be on either side of the outer AND;
	// swapped records which side it was matched on, and the bridge
	// mirrors that order throughout.
	if b := tryFuseAt(t, wAbs, w, l, r, false); b != nil {
		return b
	}
	if b := tryFuseAt(t, wAbs, w, r, l, true); b != nil {
		return b
	}
	// The DEGENERATE case of the same rule — no ∃u⃗-prefix and no `P ∧`
	// companion, i.e. the classical UNWIND / one-point rule
	//
	//	∃w. (w = T) ∧ R(w)   ⇔   R[w:=T]
	//
	// tryFuseAt cannot reach it: after peeling the (empty) ∃u⃗-prefix it
	// requires `MatchesAND(inner)` to split E into `P ∧ EQ`, and here E
	// IS the bare equation. This is the shape set_comprehension/comprehension_spec collapse
	// emits at the OUTER comprehension level (`set_comprehension(λg. ∃x. comprehension_spec(g,
	// P(x), x))(y)` β-collapses to `∃x. P(x) ∧ (y = x)`), so it occurs in
	// every set-builder membership the driver expands. See tryFuseBareEq.
	if b := tryFuseBareEq(t, wAbs, w, l, r, false); b != nil {
		return b
	}
	return tryFuseBareEq(t, wAbs, w, r, l, true)
}

// instExistsThrough is the ∃-introduction of t at the witness T from
// fin, whose conclusion is the body of t at T in the canonical DeepBeta
// form every bridge component is built from: `{Γ} ⊢ t`, nil where the
// two do not meet. The kernel's instance (prop.InstExists) states the
// body with T substituted RAW, which differs from the reduced form
// exactly when T is an abstraction the body applies — a map's
// membership in a set of functions, where the substitution makes the
// redexes `(λx. …)(y)` — and the one DeepBeta reduction carries fin's
// conclusion to the raw body.
func instExistsThrough(t, T core.Term, fin *prop.PropWrapper) *prop.PropWrapper {
	instW := prop.InstExists(t, T)
	if instW.HasHyp(fin.Conclusion()) {
		return fin.DeriveTrans(instW)
	}
	var raw core.Term
	for h := range instW.HypIter() {
		raw = h
	}
	if raw == nil {
		return nil
	}
	reduced := prop.WrapProp(core.Refl(raw)).RewriteConclRhs(prop.DeepBeta) // ⊢ raw = β(raw)
	if !prop.Rhs(reduced).AlphaEquals(fin.Conclusion()) {
		return nil
	}
	bridged := reduced.EqSym().EqMP(fin) // {Γ} ⊢ raw
	if !instW.HasHyp(bridged.Conclusion()) {
		return nil
	}
	return bridged.DeriveTrans(instW)
}

// tryFuseBareEq is tryFuseAt's degenerate face: the comprehension conjunct
// is the BARE equation `w = T` (no ∃u⃗-prefix, no `P ∧` companion), so the
// fused form is just `R[w:=T]`. EQ is the conjunct matched as the
// equation and R the remainder; swapped records which side of the outer
// AND EQ sat on, and every discharge against the ORIGINAL body mirrors
// that order, as tryFuseAt's do.
func tryFuseBareEq(t core.Term, wAbs core.AbsTerm, w core.VarTerm, EQ, R core.Term, swapped bool) *prop.PropWrapper {
	el, er, ok := MatchesEQ(EQ)
	if !ok {
		return nil
	}
	var T core.Term
	var flip bool
	switch {
	case el.Equals(w) && !er.HasFree(w):
		T = er
	case er.Equals(w) && !el.HasFree(w):
		T, flip = el, true
	default:
		return nil
	}
	// β-face gate, verbatim from tryFuseAt: every component below is built
	// from THE ONE canonical DeepBeta reduction.
	if prop.DeepBeta(R) != nil || prop.DeepBeta(T) != nil {
		return nil
	}

	lamR := core.Abs(w, R)
	betaR := prop.WrapProp(core.Refl(core.Apply(lamR, T))).
		RewriteConclRhs(prop.DeepBeta)
	RT := prop.Rhs(betaR) // R[w:=T]

	andBody := wAbs.Body()

	// ---- π₁: {t} ⊢ R[w:=T] -------------------------------------------
	projEQ, projR := prop.HypAND0(EQ, R), prop.HypAND1(EQ, R)
	if swapped {
		projEQ, projR = prop.HypAND1(R, EQ), prop.HypAND0(R, EQ)
	}
	eqProj := projEQ
	if flip {
		eqProj = eqProj.EqSym()
	}
	bridgeR := eqProj.LeftApply(lamR).RewriteConcl(prop.DeepBeta)
	rFromRw := bridgeR.EqMP(prop.Assume(prop.Lhs(bridgeR))) // {andBody, R} ⊢ RT
	if !rFromRw.HasHyp(R) {
		return nil // defense in depth — decline, never panic
	}
	c := projR.DeriveTrans(rFromRw) // {andBody} ⊢ RT
	if !c.HasHyp(andBody) || c.Conclusion().HasFree(w) ||
		!prop.NotFreeInHyps(c, w, andBody) {
		return nil
	}
	pi1 := c.HypExists(w, andBody) // {t} ⊢ RT

	// ---- π₂: {R[w:=T]} ⊢ t -------------------------------------------
	betaBody := prop.WrapProp(core.Refl(core.Apply(wAbs, T))).
		RewriteConclRhs(prop.DeepBeta)
	bodyT := prop.Rhs(betaBody)
	cl, cr, ok := ext.MatchesAND(bodyT)
	if !ok {
		return nil
	}
	eqSide, rSide := cl, cr
	if swapped {
		eqSide, rSide = cr, cl
	}
	if !rSide.AlphaEquals(RT) {
		return nil
	}
	// eqSide is the equation at w := T, i.e. `T = T`.
	refl := prop.WrapProp(core.Refl(T))
	if !refl.Conclusion().AlphaEquals(eqSide) {
		return nil
	}
	fin := prop.ConclAND(cl, cr) // {cl, cr} ⊢ cl ∧ cr
	if !fin.HasHyp(eqSide) {
		return nil // eqSide α-equal rSide, deduplicated — decline
	}
	fin = refl.DeriveTrans(fin)        // {RT} ⊢ bodyT
	fin = instExistsThrough(t, T, fin) // {RT} ⊢ t
	if fin == nil {
		return nil
	}

	return fin.Deduct(pi1)
}

// tryFuseAt attempts the fusion with E as the comprehension conjunct and
// R as the remainder (which may mention w). swapped records the side of
// the outer AND the comprehension conjunct was matched on — the original
// body is AND(E, R) when false, AND(R, E) when true — and every
// discharge/reassembly against the ORIGINAL body mirrors that order.
// The fused OUTPUT is always the canonical AND(P, R[w:=T]).
func tryFuseAt(t core.Term, wAbs core.AbsTerm, w core.VarTerm, E, R core.Term, swapped bool) *prop.PropWrapper {
	// Peel E's ∃-prefix: E = ∃u₁…∃uₖ. AND(P, EQ), k ≥ 0. Record the
	// suffix terms — the HypExists folds re-use them verbatim.
	var us []core.VarTerm
	suffixes := []core.Term{E}
	inner := E
	for {
		abs := ext.MatchesEXISTS(inner)
		if abs.IsZero() {
			break
		}
		us = append(us, abs.Var())
		inner = abs.Body()
		suffixes = append(suffixes, inner)
	}
	P, EQ, ok := ext.MatchesAND(inner)
	if !ok {
		return nil
	}
	el, er, ok := MatchesEQ(EQ)
	if !ok {
		return nil
	}
	// Orient: EQ must equate w with a w-free term T.
	var T core.Term
	var flip bool
	switch {
	case el.Equals(w) && !er.HasFree(w):
		T = er
	case er.Equals(w) && !el.HasFree(w):
		T, flip = el, true
	default:
		return nil
	}
	if P.HasFree(w) {
		return nil
	}
	// Binder hygiene: distinct u⃗, none equal to w, none free in R (a
	// same-named var in R would be captured by the fused ∃u⃗ prefix).
	seen := map[core.TermKey]bool{w.AlphaKey(): true}
	for _, u := range us {
		if seen[u.AlphaKey()] || R.HasFree(u) {
			return nil
		}
		seen[u.AlphaKey()] = true
	}
	// β-face gate: every bridge component below is built from THE ONE
	// canonical DeepBeta reduction, so a β-redex already sitting inside
	// P, R or T makes the raw and normalized forms diverge mid-bridge
	// (π₁ discharges the RAW R at the outer AND, π₂ builds T = T from
	// the RAW T). Such redexes only reach here on start-of-pass terms
	// the earlier fixpoint passes never fired on — decline and let the
	// driver's own β pass consume them first.
	if prop.DeepBeta(P) != nil || prop.DeepBeta(R) != nil || prop.DeepBeta(T) != nil {
		return nil
	}

	// Canonical R[w:=T]: β of (λw.R)(T). Both directions and the fused
	// term are built from THIS one reduction, so every α-form agrees.
	lamR := core.Abs(w, R)
	betaR := prop.WrapProp(core.Refl(core.Apply(lamR, T))).
		RewriteConclRhs(prop.DeepBeta)
	RT := prop.Rhs(betaR) // R[w:=T]

	// Fused term t' = ∃u₁…∃uₖ. AND(P, RT).
	fusedBody := ext.WrapTerm(P).And(RT).Core()
	tPrime := fusedBody
	fusedSuffixes := []core.Term{fusedBody}
	for i := len(us) - 1; i >= 0; i-- {
		tPrime = ext.Exists(us[i])(tPrime).Core()
		fusedSuffixes = append([]core.Term{tPrime}, fusedSuffixes...)
	}

	andER := wAbs.Body()

	// ---- π₁: {t} ⊢ t' ----------------------------------------------
	// From the innermost assumption AND(P, EQ):
	pProj := prop.HypAND0(P, EQ) // {P∧EQ} ⊢ P
	eqProj := prop.HypAND1(P, EQ)
	if flip {
		eqProj = eqProj.EqSym()
	}
	// {P∧EQ} ⊢ R(w) = R(T): congruence over λw.R, then β both sides.
	bridgeR := eqProj.LeftApply(lamR).RewriteConcl(prop.DeepBeta)
	// {P∧EQ, R(w)} ⊢ RT
	rFromRw := bridgeR.EqMP(prop.Assume(prop.Lhs(bridgeR)))

	c := prop.ConclAND(P, RT) // {P, RT} ⊢ P ∧ RT
	c = pProj.DeriveTrans(c)  // {P∧EQ, RT} ⊢ P ∧ RT
	if !c.HasHyp(rFromRw.Conclusion()) {
		// Defense in depth: a shape this gate did not anticipate (e.g.
		// P α-equal RT, deduplicated in the hyp set) declines instead
		// of tripping DeriveTrans's precondition Assert.
		return nil
	}
	c = rFromRw.DeriveTrans(c)
	// {P∧EQ, R(w)} ⊢ P ∧ RT; ∃-intro u⃗ (innermost first).
	for i := len(us) - 1; i >= 0; i-- {
		c = c.ConclExistsInst(us[i])
	}
	// Fold the AND(P,EQ) hyp back under E's ∃-prefix.
	for i := len(us) - 1; i >= 0; i-- {
		if !c.HasHyp(suffixes[i+1]) || c.Conclusion().HasFree(us[i]) ||
			!prop.NotFreeInHyps(c, us[i], suffixes[i+1]) {
			return nil // defense in depth — decline, never panic
		}
		c = c.HypExists(us[i], suffixes[i+1])
	}
	// {E, R(w)} ⊢ t'  →  {andER} ⊢ t'  →  {t} ⊢ t'. The two projections
	// mirror the MATCHED conjunct order — andER is the ground-truth
	// body, AND(E, R) or AND(R, E) — so that HypExists discharges
	// exactly andER, never a reassembled variant.
	projE, projR := prop.HypAND0(E, R), prop.HypAND1(E, R)
	if swapped {
		projE, projR = prop.HypAND1(R, E), prop.HypAND0(R, E)
	}
	if !c.HasHyp(E) {
		return nil // defense in depth — decline, never panic
	}
	c = projE.DeriveTrans(c)
	if !c.HasHyp(R) {
		// E α-equal R: the single deduplicated hyp was already
		// discharged above — decline.
		return nil
	}
	c = projR.DeriveTrans(c)
	if !c.HasHyp(andER) || c.Conclusion().HasFree(w) ||
		!prop.NotFreeInHyps(c, w, andER) {
		return nil // defense in depth — decline, never panic
	}
	pi1 := c.HypExists(w, andER)

	// ---- π₂: {t'} ⊢ t ----------------------------------------------
	pP := prop.HypAND0(P, RT) // {P∧RT} ⊢ P
	pR := prop.HypAND1(P, RT)
	// Body of t at witness T, canonically: β((λw. E∧R)(T)) = AND(EwT, RT).
	betaBody := prop.WrapProp(core.Refl(core.Apply(wAbs, T))).
		RewriteConclRhs(prop.DeepBeta)
	bodyT := prop.Rhs(betaBody)
	cl, cr, ok := ext.MatchesAND(bodyT)
	if !ok {
		return nil
	}
	// bodyT is the β of the ORIGINAL body at T, so the comprehension
	// image sits on the same side E was matched on.
	EwT, RTcheck := cl, cr
	if swapped {
		EwT, RTcheck = cr, cl
	}
	if !RTcheck.AlphaEquals(RT) {
		// R[w:=T] must agree between the two canonical β paths; a
		// divergence means an α-subtlety this gate doesn't cover.
		return nil
	}
	// Prove {P∧RT} ⊢ EwT = (∃u⃗'. P' ∧ (T = T')): instantiate the primed
	// binders at u⃗ outside-in; the innermost instance is AND(P, T = T),
	// provable from P + Refl.
	eqTT := ext.WrapTerm(T).Eq(T).Core()
	acc := prop.ConclAND(P, eqTT) // {P, T=T} ⊢ AND(P, T=T)
	acc = pP.DeriveTrans(acc)     // {P∧RT, T=T} ⊢ …
	if !acc.HasHyp(eqTT) {
		// P α-equal T = T: the single deduplicated hyp was already
		// discharged above — decline.
		return nil
	}
	acc = prop.WrapProp(core.Refl(T)).DeriveTrans(acc) // {P∧RT} ⊢ AND(P, T=T)
	// Peel EwT's ∃-prefix. The kernel's capture-avoiding β RENAMED the
	// binders (T's u⃗ occur free in EwT's left equality sides and must
	// stay free) — collect the fresh binder vars v⃗ alongside the
	// suffixes. The ∃-intro chain below then instantiates the
	// PARTIALLY-substituted targets c_i := ewtSuffix_i[v_j:=u_j ∀j<i]
	// at witness u_i — c_0 = EwT, and c_k α-matches acc's conclusion.
	// (A plain ConclExistsInst chain would bind the LEFT T's u⃗ too and
	// produce a term that is NOT α-equal to EwT.)
	ewtSuffixes := []core.Term{EwT}
	var vs []core.VarTerm
	innerT := EwT
	for range us {
		abs := ext.MatchesEXISTS(innerT)
		if abs.IsZero() {
			return nil
		}
		vs = append(vs, abs.Var())
		innerT = abs.Body()
		ewtSuffixes = append(ewtSuffixes, innerT)
	}
	cTerm := func(i int) core.Term {
		subs := make([]core.TermSubst, 0, i)
		for j := 0; j < i; j++ {
			subs = append(subs, core.MakeTermSubst(vs[j], us[j]))
		}
		return ewtSuffixes[i].Substitute(subs...)
	}
	for i := len(us) - 1; i >= 0; i-- {
		step := prop.InstExists(cTerm(i), us[i])
		if !step.HasHyp(acc.Conclusion()) {
			return nil
		}
		acc = acc.DeriveTrans(step)
	}
	// {P∧RT} ⊢ EwT; combine with RT in the MATCHED order and ∃-intro w
	// at witness T.
	var fin *prop.PropWrapper
	if swapped {
		fin = prop.ConclAND(RTcheck, EwT)
	} else {
		fin = prop.ConclAND(EwT, RTcheck)
	}
	if !fin.HasHyp(acc.Conclusion()) {
		// The raw-built AND(P, T=T) diverged from the DeepBeta'd EwT —
		// a residual normalization face; decline instead of tripping
		// DeriveTrans's precondition Assert.
		return nil
	}
	fin = acc.DeriveTrans(fin)
	if !fin.HasHyp(pR.Conclusion()) {
		return nil // defense in depth — decline, never panic
	}
	fin = pR.DeriveTrans(fin)          // {P∧RT} ⊢ the matched-order AND
	fin = instExistsThrough(t, T, fin) // {P∧RT} ⊢ t
	if fin == nil {
		return nil
	}
	// Fold t' over the hyp.
	for i := len(us) - 1; i >= 0; i-- {
		if !fin.HasHyp(fusedSuffixes[i+1]) || fin.Conclusion().HasFree(us[i]) ||
			!prop.NotFreeInHyps(fin, us[i], fusedSuffixes[i+1]) {
			return nil // defense in depth — decline, never panic
		}
		fin = fin.HypExists(us[i], fusedSuffixes[i+1])
	}

	// ⊢ t = t' (Deduct removes t' from π₂'s hyps and t from π₁'s).
	return fin.Deduct(pi1)
}
