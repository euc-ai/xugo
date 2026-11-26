package omega

import (
	"math/big"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// Integer (Presburger) strengthening of the ℚ-Farkas core. SOUND and strictly
// stronger than linarith — it decides integer-unsat systems ℚ-Farkas misses —
// via three integer inferences, then the existing Fourier–Motzkin refuter:
//
//   • GCD equality test:  Σcᵢxᵢ = k  is unsat when gcd(cᵢ) ∤ k.
//   • gcd rounding cut:    g·y ≤ b   ⟹   y ≤ ⌊b/g⌋   (per-row tightening).
//   • equation elimination: an equation solved for an atom of coefficient ±1
//     and substituted into the other rows, each substituted row rounded
//     (equation_elimination.go).
//
// This is NOT full Presburger: it does no quantifier elimination, solves no
// equation without an atom of coefficient ±1, cuts no row Fourier–Motzkin
// derives, and does no dark/gray-shadow splintering — those are the open
// integer-completeness frontier (README, "Future work"). It is sound (every
// UNSAT it reports is a real ℕ contradiction) and complete for the common
// integer-gap cases. The decision is untrusted; IntRefuteProof replays it as a
// real proof.

// vecGCD is the gcd of the absolute values of a coefficient vector (0 if all 0).
func vecGCD(coeffs []_Integer) _Integer {
	var g _Integer
	for _, c := range coeffs {
		g = g.gcd(c)
	}
	return g
}

// tightenLe applies the gcd rounding cut to a `Σcx + konst ≤ 0` row, returning
// the (possibly) tightened coeffs/konst and whether rounding changed it.
func tightenLe(coeffs []_Integer, konst _Integer) ([]_Integer, _Integer, bool) {
	g := vecGCD(coeffs)
	if g.cmp(integerOne) <= 0 {
		return coeffs, konst, false
	}
	nc := make([]_Integer, len(coeffs))
	for i, c := range coeffs {
		nc[i], _ = c.divMod(g)
	}
	// Σ(c/g)x ≤ -konst/g, floored.
	bound, remainder := konst.neg().divMod(g)
	return nc, bound.neg(), !remainder.isZero()
}

// eqGCDUnsat reports whether `Σcx + konst = 0` is unsatisfiable by the GCD test.
func eqGCDUnsat(coeffs []_Integer, konst _Integer) bool {
	g := vecGCD(coeffs)
	if g.isZero() { // no variables: konst = 0 required
		return !konst.isZero()
	}
	_, remainder := konst.divMod(g)
	return !remainder.isZero()
}

// IntUnsat decides (soundly) whether the constraint conjunction is unsatisfiable
// over ℕ, using the GCD test + gcd rounding cuts + the elimination of
// equations + Fourier–Motzkin. ok=false means a side was nonlinear. Shares the
// constraint pipeline with the proof path (buildIntProv + finalize +
// eliminateEquations).
func IntUnsat(cs []LinConstraint) (unsat bool, ok bool) {
	p, built := buildIntProv(cs)
	if !built {
		return false, false
	}
	if p.gcdUnsat { // untrusted gcd verdict — independent of proof-leaf supply
		return true, true
	}
	fm2, prs2 := finalize(p.tbl, p.fm, p.prs)
	if e, eliminated := eliminateEquations(p.tbl, fm2, prs2, natEliminationLeaves); eliminated {
		fm2 = e.system()
	}
	_, refuted := fmRefute(p.tbl.n(), fm2)
	return refuted, true
}

// Integer-refutation proof replay. Reuses the linarith certificate replay wholesale:
// the gcd-rounded constraints are valid ℕ inequalities, so the Farkas
// combination still cancels the variables to a false constant — exactly what
// `replay` discharges. The only new ingredients are the integer-cut provenance
// (orig ⇒ rounded) and the GCD-equality contradiction, both PLACEHOLDER leaves.

// The rank-1 integer rounding cut, REAL via LessEqRightDivEq + DivModUniq + ring.
//
// Each FM row arrives as a `≤`-proof `{H} ⊢ oL ≤ oR` whose combined signed
// linear form is `Σ Cᵢxᵢ + K ≤ 0` (g = gcd Cᵢ). The rounding cut tightens it to
// `Σ(Cᵢ/g)xᵢ + ⌈K/g⌉ ≤ 0`, written two-sided as `Lr ≤ Rr`. The proof:
//
//	  s := g·⌈K/g⌉ − K  ∈ [0, g)         (the rounding remainder)
//	  D := g·Rr + s
//	  ring:        oL + D = oR + g·Lr     (a polynomial identity — see below)
//	  add D, cancel oR:  {H} ⊢ g·Lr ≤ D
//	  LessEqRightDivEq(Lr, D, g), g≠0:  g·Lr ≤ D  ⟹  Lr ≤ nat_div(D, g)
//	  DivModUniq:  nat_div(D, g) = Rr           (D = Rr·g + s, s < g)
//	  ⟹ {H} ⊢ Lr ≤ Rr
//
// The ring identity holds for EVERY constant placement and sign pattern (upper
// bound, lower bound, two-sided with variables on both sides), so the one
// LessEqRightDivEq instantiation discharges them all. The identity is checked
// on the canonical forms of its two sides (roundedCutIdL), so a miscomputed
// g/s makes the cut DECLINE (ok=false) rather than producing an unsound cert.
// A row with g = 1 has nothing to round and is not cut (buildIntProv).

// leCongr: ⊢ (a ≤ b) = (a' ≤ b') from eqL: ⊢ a = a' and eqR: ⊢ b = b'.
func leCongr(eqL, eqR *prop.PropWrapper) *prop.PropWrapper {
	aP := prop.Rhs(eqL)
	b := prop.Lhs(eqR)
	return eqL.LeftApply(natLe).RightApply(b).
		EqTrans(eqR.LeftApply(ext.Apply(natLe, aP)))
}

// roundedCut builds `{H} ⊢ Lr ≤ Rr` from leProof: `{H} ⊢ oL ≤ oR`, given the cut
// data (divisor g ≥ 1, remainder s ∈ [0,g), and the canonical linForms of Lr/Rr).
// ok=false ⇒ a needed bundle thm is absent or a ring/numeral step did not fit,
// so the caller uses the placeholder.
func roundedCut(leProof *prop.PropWrapper, oL, oR, Lr, Rr Term, lfLr, lfRr linForm, g, s _Integer) (*prop.PropWrapper, bool) {
	rdiv := lessEqRightDivEqThm()
	uniq := divModUniqThm()
	if rdiv == nil || uniq == nil {
		return nil, false
	}
	gT, sT := numeralOf(g), numeralOf(s)
	gLr := star(gT, Lr)
	D := plus(star(gT, Rr), sT) // D = g·Rr + s

	// ring identity (commuted so a single left-cancel of oR finishes):
	//   D + oL = oR + g·Lr  (built directly from cut data — see roundedCutIdL)
	//   D + oR = oR + D     (pure commutativity of + — one AddSym cite).
	// idL is not a generic RingProveFull(plus(D, oL), plus(oR, gLr)) call:
	// Lr/Rr are already-canonical .toTerm(lf) forms, and RingProveFull would
	// re-walk their structure (~50% of the per-cut normalize cost). roundedCutIdL
	// consumes the known lfLr/lfRr from signedToLe and skips the walk.
	idL, ok1 := roundedCutIdL(oL, oR, Lr, Rr, lfLr, lfRr, g, s)
	idR := commuteADD(D, oR)
	if !ok1 {
		return nil, false
	}
	// add D on the left of the orig row, then rewrite to oR + g·Lr ≤ oR + D.
	addD := addLcancelLe(D, oL, oR).RightAssume()                      // {oL≤oR} ⊢ D+oL ≤ D+oR
	stepB := leProof.DeriveTrans(addD)                                 // {H} ⊢ D+oL ≤ D+oR
	stepC := leCongr(idL, idR).EqMP(stepB)                             // {H} ⊢ oR+g·Lr ≤ oR+D
	scaled := stepC.DeriveTrans(addLcancelLe(oR, gLr, D).LeftAssume()) // {H} ⊢ g·Lr ≤ D

	// LessEqRightDivEq (raw disjunction) at (Lr, D, g):
	//   ⊢ ((Lr ≤ nat_div(D, g)) ⇔ (g·Lr ≤ D)) ∨ (g = 0).
	// Discharge the `g = 0` disjunct on the concrete g≠0, leaving the iff; then
	// its RHS→LHS direction turns `g·Lr ≤ D` into `Lr ≤ nat_div(D, g)`.
	disj := instAll(rdiv, []Term{Lr, D, gT})
	iff, okIff := rdivDischargeZero(disj, gT)
	if !okIff {
		return nil, false
	}
	leDiv := scaled.DeriveTrans(iff.RightAssume()) // {H} ⊢ Lr ≤ nat_div(D, g)

	// DivModUniq: nat_div(D, g) = Rr  (witness D = Rr·g + s, s < g).
	divEq, ok := divUniqQuotient(uniq, D, gT, Rr, sT)
	if !ok {
		return nil, false
	}
	// rewrite the bound `Lr ≤ nat_div(D, g)` → `Lr ≤ Rr`.
	cong := divEq.LeftApply(ext.Apply(natLe, Lr)) // ⊢ (Lr ≤ nat_div(D, g)) = (Lr ≤ Rr)
	return cong.EqMP(leDiv), true
}

// roundedCutIdL builds `⊢ D + oL = oR + g·Lr` directly from cut data — the
// structural identity over the rank-1 rounding cut. It does without a generic
// RingProveFull on `(D+oL, oR+g·Lr)` by exploiting two cut-construction facts
// the generic normalizer can't see:
//
//   - Lr, Rr are ALREADY canonical: signedToLe builds them via linForm.toTerm,
//     so we know lfLr/lfRr without walking the term. scaleProof(g, lfRr/lfLr)
//     applies directly, skipping ringProveFull → normalizeFull's structural
//     re-walk of Lr/Rr (~50% of a cut's kernel work under the generic call).
//
//   - The canonical LHS / RHS forms are equal by construction of (g, s, nc, nk):
//     `g·nk − s = K` (signed konst) and `g·nc_i = C_i` (signed coeff per atom),
//     so linAdd(scale(g, lfRr), linConst(s), lfL) ≡ linAdd(lfR, scale(g, lfLr))
//     as forms. We Refl-check on canonical equality and fail (cut algorithm bug,
//     caller declines) only on mismatch — there is no normalize-then-compare.
//
// The unavoidable cost is normalizing the hyp shapes oL, oR; nothing in the
// cut data lets us skip those.
func roundedCutIdL(oL, oR, Lr, Rr Term, lfLr, lfRr linForm, g, s _Integer) (*prop.PropWrapper, bool) {
	// Normalize hyp shapes — unavoidable: oL/oR are arbitrary hyp terms.
	lfL, wL, ok1 := natRing.normalizeProof(oL) // ⊢ oL = toTerm(lfL)
	if !ok1 {
		return nil, false
	}
	lfR, wR, ok2 := natRing.normalizeProof(oR) // ⊢ oR = toTerm(lfR)
	if !ok2 {
		return nil, false
	}

	sT := numeralOf(s)

	// g·Rr, g·Lr — Lr/Rr are toTerm(lfLr)/toTerm(lfRr) by signedToLe, so
	// scaleProof applies WITHOUT re-walking the term.
	wGRr := natRing.scaleProof(g, lfRr) // ⊢ g·Rr = toTerm(linScale(g, lfRr))
	wGLr := natRing.scaleProof(g, lfLr) // ⊢ g·Lr = toTerm(linScale(g, lfLr))
	lfGRr := linScale(g, lfRr)
	lfGLr := linScale(g, lfLr)

	// D = g·Rr + s → toTerm(lfGRr) + s → toTerm(lfD).
	// insertConstEq(lfGRr, s) handles both s=0 (the `+ 0 = _` fold) and s>0 paths.
	wDCong := wGRr.LeftApply(natPlus).RightApply(sT) // ⊢ g·Rr + s = toTerm(lfGRr) + s
	wDMerge := natRing.insertConstEq(lfGRr, s)       // ⊢ toTerm(lfGRr) + s = toTerm(lfD)
	wD := wDCong.EqTrans(wDMerge)
	lfD := linAdd(lfGRr, linConst(s))

	// LHS: D + oL = toTerm(lfD) + toTerm(lfL) = toTerm(linAdd(lfD, lfL))
	wLhs := wD.LeftApply(natPlus).Apply(wL).
		EqTrans(natRing.mergeProof(lfD, lfL))
	lfLHS := linAdd(lfD, lfL)

	// RHS: oR + g·Lr = toTerm(lfR) + toTerm(lfGLr) = toTerm(linAdd(lfR, lfGLr))
	wRhs := wR.LeftApply(natPlus).Apply(wGLr).
		EqTrans(natRing.mergeProof(lfR, lfGLr))
	lfRHS := linAdd(lfR, lfGLr)

	// Canonical forms MUST coincide. signedToLe + cut construction guarantee
	// it; a mismatch is a cut-algorithm bug (decline the row, surface visibly).
	if !natDomain.buildTerm(lfLHS).AlphaEquals(natDomain.buildTerm(lfRHS)) {
		return nil, false
	}
	return wLhs.EqTrans(wRhs.EqSym()), true
}

// rdivDischargeZero turns LessEqRightDivEq's instantiated disjunction
// `⊢ (IFF) ∨ (g = z)` into `⊢ IFF`, given g is a concrete numeral ≠ z (= 0).
// The `g = z` disjunct is killed by ByCases against ⊢ ¬(g = z) (NormNatNe).
// ok=false on an unexpected shape (e.g. not a 2-way disjunction, or no g=numeral
// disjunct), so the caller (roundedCut) declines.
func rdivDischargeZero(disj *prop.PropWrapper, gT Term) (*prop.PropWrapper, bool) {
	comps := prop.DecomposesOR(disj.Conclusion())
	if len(comps) != 2 {
		return nil, false
	}
	var iffC, zeroRhs Term
	for _, c := range comps {
		if l, r, ok := prop.MatchesEQ(c); ok {
			if _, isNum := asNumeral(r); isNum && l.AlphaEquals(gT) {
				zeroRhs = r // the `g = 0` disjunct
				continue
			}
		}
		iffC = c // the iff disjunct
	}
	if iffC == nil || zeroRhs == nil {
		return nil, false
	}
	ne, ok := NormNatNe(gT, zeroRhs) // ⊢ (g ≠ z) ⇔ ⊤  (g is a nonzero numeral)
	if !ok {
		return nil, false
	}
	negZero := iffTrueElim(ne) // ⊢ ¬(g = z)
	mkImp := func(comp Term) *prop.PropWrapper {
		if comp.AlphaEquals(iffC) {
			return prop.Assume(iffC).PromoteHyp(iffC) // ⊢ IFF ⇒ IFF
		}
		// ⊢ (g = z) ⇒ IFF, vacuously (the antecedent contradicts ¬(g = z)).
		return prop.Contradict(comp).DeriveHypFrom(negZero).
			DeriveTrans(prop.FalseDerives(iffC)).PromoteHyp(comp)
	}
	return prop.ByCases(iffC, comps[0], comps[1]).
		DeriveHypFrom(disj).
		DeriveHypFrom(mkImp(comps[0])).
		DeriveHypFrom(mkImp(comps[1])), true
}

// divUniqQuotient discharges DivModUniq to ⊢ (nat_div(m, n) = q) from a symbolic
// witness `m = q·n + r` (ring) and `r < n` (numeral). Mirrors norm_num's
// divmodEval but with m / q symbolic (n, r numerals). ok=false on a missing
// step or a shape-mismatched bundle thm.
func divUniqQuotient(uniq *prop.PropWrapper, m, n, q, r Term) (*prop.PropWrapper, bool) {
	// Fast path for the only production caller (roundedCut), which always passes
	// m = plus(star(n, q), r) verbatim — D = `g·Rr + s` built in roundedCut and
	// re-handed as (m, n, q, r) = (D, g, Rr, s). The desired `m = q·n + r` then
	// differs from m by exactly one ⊢ g·Rr = Rr·g (commuteMUL), lifted through
	// `_ + s`. Skips the full ring-normalizer round-trip on BOTH sides — the
	// dominant cost when an omega refutation walks dist-expanded hyps (each cut
	// row hands divUniqQuotient a fresh roundedCut-shaped m).
	var wEq *prop.PropWrapper
	if ml, mr, ok := MatchesPlus(m); ok && mr.AlphaEquals(r) {
		if sl, sr, ok := MatchesStar(ml); ok && sl.AlphaEquals(n) && sr.AlphaEquals(q) {
			wEq = commuteMUL(n, q).LeftApply(natPlus).RightApply(r) // ⊢ n·q + r = q·n + r
		}
	}
	if wEq == nil {
		var ok bool
		wEq, ok = RingProveFull(m, plus(star(q, n), r)) // ⊢ m = q·n + r
		if !ok {
			return nil, false
		}
	}
	ltW, ok := NormNatLt(r, n) // ⊢ (r < n) ⇔ ⊤
	if !ok {
		return nil, false
	}
	ltProof := iffTrueElim(ltW) // ⊢ r < n
	divEq := eqT(divT(m, n), q)
	modEq := eqT(modT(m, n), r)
	eqConcl := eqT(m, plus(star(q, n), r))
	ltConcl := lt(r, n)
	ante := prop.ConclAND(eqConcl, ltConcl).DeriveHypFrom(wEq).DeriveHypFrom(ltProof)
	impl, ok := macroThm(uniq, []Term{m, n, q, r},
		imply(prop.And(eqConcl, ltConcl), prop.And(divEq, modEq)))
	if !ok {
		return nil, false
	}
	full := mp(impl, ante) // ⊢ (nat_div(m, n) = q) ∧ (nat_mod(m, n) = r)
	return full.DeriveTrans(prop.HypAND0(divEq, modEq)), true
}

// cutProv produces `{H} ⊢ Lr ≤ Rr` for one rounded FM row: the trivial proof
// when oL≤oR already IS the rounded row, the real roundedCut when the bundle
// supplies LessEqRightDivEq + DivModUniq. ok=false (no proof) when the rank-1 cut is
// not supported for this row — the integer-frontier nil contract: buildIntProv
// then declines the whole refutation rather than fabricating a row.
func cutProv(leProof *prop.PropWrapper, oL, oR, Lr, Rr Term, lfLr, lfRr linForm, g, s _Integer) (*prop.PropWrapper, bool) {
	if le(oL, oR).AlphaEquals(le(Lr, Rr)) {
		return leProof, true
	}
	if w, ok := roundedCut(leProof, oL, oR, Lr, Rr, lfLr, lfRr, g, s); ok {
		return w, true
	}
	return nil, false
}

// groundedGcdEq builds a REAL `{et} ⊢ ⊥` for an equality whose GCD test fails,
// in the common shape where one side is a pure constant and the other a pure
// variable form V (gcd g, g ∤ c). The argument: V = g·M (ring), so g·M = c
// (hyp), hence c = M·g, so `∃q. c = q·g` holds (∃-intro at witness M) — i.e.
// `g divides c` in omega's nat-native sense — contradicting ¬∃ from the
// divisibility decision. Real composition (MulSym + ∃-intro); only the
// ¬-divides leaf (notDivides → ModEqZero + nat_mod evaluator) is supply-gated.
// ok=false — a two-sided equality, or the leaf unsupplied — ⇒ IntRefuteProof
// refutes through the equality's two ≤ rows and their rounding cuts instead.
func groundedGcdEq(e intExt) (*prop.PropWrapper, bool) {
	la, ok1 := linOf(e.lhs)
	lb, ok2 := linOf(e.rhs)
	if !ok1 || !ok2 {
		return nil, false
	}
	// orient: V = variable side (monos, no constant), c = pure-constant side.
	var v linForm
	var vTerm, cTerm Term
	var vIsLhs bool
	switch {
	case len(la.monos) > 0 && la.konst.isZero() && len(lb.monos) == 0:
		v, vTerm, cTerm, vIsLhs = la, e.lhs, e.rhs, true
	case len(lb.monos) > 0 && lb.konst.isZero() && len(la.monos) == 0:
		v, vTerm, cTerm, vIsLhs = lb, e.rhs, e.lhs, false
	default:
		return nil, false
	}
	c := lb.konst
	if !vIsLhs {
		c = la.konst
	}
	// g = gcd of V's coefficients
	var g _Integer
	for _, m := range v.monos {
		g = g.gcd(m.coeff)
	}
	if g.cmp(integerOne) <= 0 {
		return nil, false
	}
	if _, remainder := c.divMod(g); remainder.isZero() {
		return nil, false
	}
	// M = V/g, gM = g·M
	red := make([]monomialL, len(v.monos))
	for i, m := range v.monos {
		reduced, _ := m.coeff.divMod(g)
		red[i] = monomialL{coeff: reduced, atom: m.atom}
	}
	redLf := linForm{monos: red}
	gTerm := numeralOf(g)
	mTerm := redLf.toTerm()

	// ⊢ V = g·M by construction (scaling red by g recovers v, since each red[i]
	// = v.monos[i]/g). Skips RingProveFull's normalize+compare; both sides are
	// linOf-shaped, so normalizeProof matches the model linForm and scaleProof
	// applies directly to the already-canonical mTerm = toTerm(redLf).
	vNorm, wV, vok := natRing.normalizeProof(vTerm) // ⊢ V = toTerm(vNorm); vNorm == v
	if !vok {
		return nil, false
	}
	scaledRed := linScale(g, redLf)
	if !natDomain.buildTerm(scaledRed).AlphaEquals(natDomain.buildTerm(vNorm)) {
		return nil, false // scale(g, V/g) != V — linOf/linScale contract violation, surface as decline
	}
	scaleW := natRing.scaleProof(g, redLf) // ⊢ g·M = toTerm(scaledRed) (== toTerm(vNorm))
	ringEq := wV.EqTrans(scaleW.EqSym())   // ⊢ V = g·M
	asm := e.assumeEq()                    // {prov} ⊢ (e.lhs = e.rhs)
	// gMeqC : {prov} ⊢ g·M = c
	var gMeqC *prop.PropWrapper
	if vIsLhs { // et : V = c
		gMeqC = ringEq.EqSym().EqTrans(asm)
	} else { // et : c = V
		gMeqC = asm.EqTrans(ringEq).EqSym()
	}
	// c = M·g  (g·M = c flipped, then MulSym), so `∃q. c = q·g` at witness M.
	cEqMg := gMeqC.EqSym().EqTrans(commuteMUL(gTerm, mTerm))                // {et} ⊢ c = M·g
	gDivC := prop.InstExists(dvd(gTerm, cTerm), mTerm).DeriveHypFrom(cEqMg) // {et} ⊢ ∃q. c = q·g
	// ¬(g divides c) from the decision (g ∤ c)
	negDiv, holds, dok := NormNatDivides(gTerm, cTerm)
	if !dok || holds {
		return nil, false
	}
	// {et} ⊢ ⊥
	return negDiv.DeriveTrans(gDivC.DeriveTrans(prop.Contradict(dvd(gTerm, cTerm)))), true
}

// signedToLe rebuilds a canonical two-sided `L ≤ R` term from a signed row
// `Σ coeffs·x + konst ≤ 0`: positive coeffs and a positive constant go left,
// negatives go right. Returns BOTH the term and the linForm for each side —
// roundedCutIdL consumes the linForms directly (skipping a round-trip through
// linOf on the canonical .toTerm() output). Each side's monomials enter
// through addMono, so the forms keep linForm's invariant — monomials sorted
// by atom — whatever order the table met the atoms in (a hypothesis read
// first enters its atoms first): roundedCutIdL adds them to forms the
// normalizer built and checks the canonical terms coincide, which only
// sorted operands satisfy.
func signedToLe(coeffs []_Integer, konst _Integer, tbl *atomTable) (lfL linForm, lT Term, lfR linForm, rT Term) {
	var lm, rm []monomialL
	for i, c := range coeffs {
		switch c.sign() {
		case 1:
			lm = addMono(lm, c, tbl.atoms[i])
		case -1:
			rm = addMono(rm, c.neg(), tbl.atoms[i])
		}
	}
	var lk, rk _Integer
	switch konst.sign() {
	case 1:
		lk = konst
	case -1:
		rk = konst.neg()
	}
	lfL = linForm{konst: lk, monos: lm}
	lfR = linForm{konst: rk, monos: rm}
	return lfL, lfL.toTerm(), lfR, lfR.toTerm()
}

type intExt struct {
	coeffs   []_Integer
	konst    _Integer
	op       relOp
	lhs, rhs Term
	hyp      Term              // original `>`/`≥` term to carry, if any (see LinConstraint.Hyp)
	hypProof *prop.PropWrapper // precomputed base assumption proof (see LinConstraint.HypProof)
}

// assumeEq returns the EQ-row base assumption (`{prov} ⊢ (lhs=rhs)`): the
// precomputed hypProof (a conjunction projection) when set, else `Assume(et)`.
func (e intExt) assumeEq() *prop.PropWrapper {
	if e.hypProof != nil {
		return e.hypProof
	}
	return prop.Assume(eqT(e.lhs, e.rhs))
}

// intProv is buildIntProv's result: the untrusted FM model (tbl/fm) plus the
// index-aligned provenance rows (prs). The MODEL is always complete when built;
// each row's PROOF is materialized on demand by replay. A row that declines
// (its bundle leaf is absent) only surfaces if replay actually needs it
// (lambda > 0); rows the Farkas combination doesn't pick never pay.
//
// gcdUnsat flags a single equality the GCD test refutes directly. gcdBuild is
// likewise deferred: IntUnsat needs only the verdict, while IntRefuteProof calls
// the builder to obtain the real ⊥ proof and, where it declines, refutes the
// rows — the equality's own two ≤ rows are among them, rounding cuts and all.
type intProv struct {
	tbl      *atomTable
	fm       []row
	prs      []provRow
	gcdBuild func() (*prop.PropWrapper, bool)
	gcdUnsat bool
}

// buildIntProv extracts constraints, applies the gcd rounding cut to each row
// whose coefficients share a divisor, and produces FM rows aligned with
// provenance proofs. The bool is false only for nonlinear input (no model);
// see intProv for the model/proof split.
func buildIntProv(cs []LinConstraint) (intProv, bool) {
	tbl := &atomTable{}
	var exts []intExt
	for _, c := range cs {
		lf, ok1 := linOf(c.Lhs)
		rf, ok2 := linOf(c.Rhs)
		if !ok1 || !ok2 {
			return intProv{}, false
		}
		coeffs, konst := signedDifference(tbl, lf, rf)
		exts = append(exts, intExt{coeffs, konst, c.Op, c.Lhs, c.Rhs, c.Hyp, c.HypProof})
	}
	pad := func(c []_Integer) []_Integer {
		out := make([]_Integer, tbl.n())
		copy(out, c)
		return out
	}

	var fm []row
	var prs []provRow
	var gcdBuild func() (*prop.PropWrapper, bool)
	gcdUnsat := false
	// emit appends one FM row. (oL,oR) is the two-sided source whose combined
	// signed form is `Σ coeffs·x + konst ≤ 0`; buildLe constructs
	// `{H} ⊢ oL ≤ oR` only if replay selects this row.
	// A row whose coefficients share no divisor has nothing to round: it
	// stands in the terms it is written in, and the refutation's last step
	// normalizes it with the rows it is summed with. Where g = gcd > 1 the
	// rounding cut divides it to `Lr ≤ Rr` (remainder s ∈ [0,g)), and
	// cutProv wraps buildLe. Replay materializes either only when
	// lambda[j] > 0, so the assumption/bridge work and the per-cut
	// LessEqRightDivEq/DivModUniq work is paid only for rows the Farkas
	// combination actually uses (typically O(variables), often ≪ K).
	emit := func(coeffs []_Integer, konst _Integer, oL, oR Term, buildLe func() *prop.PropWrapper) {
		full := pad(coeffs)
		g := vecGCD(full)
		if g.cmp(integerOne) <= 0 {
			prs = append(prs, lazyProvRow(oL, oR, false, buildLe))
			fm = append(fm, row{coeffs: vectorOf(full), konst: konst})
			return
		}
		nc, nk, _ := tightenLe(full, konst)
		lfL, lt2, lfR, rt := signedToLe(nc, nk, tbl)
		s := g.mul(nk).sub(konst) // = g·⌈konst/g⌉ − konst ∈ [0, g)
		prs = append(prs, provRow{L: lt2, R: rt, build: func() (*prop.PropWrapper, bool) {
			return cutProv(buildLe(), oL, oR, lt2, rt, lfL, lfR, g, s)
		}})
		fm = append(fm, row{coeffs: vectorOf(nc), konst: nk})
	}

	for _, e := range exts {
		switch e.op {
		case opLE:
			emit(e.coeffs, e.konst, e.lhs, e.rhs, func() *prop.PropWrapper {
				return canonAssume(e.lhs, e.rhs, opLE, e.hyp, e.hypProof)
			})
		case opLT:
			// `a < b` over ℤ is `suc a ≤ b` (Σ<0 ⟺ Σ+1≤0): bridge the proof via
			// SucLessEqIffLessThan and feed the cut the `suc a ≤ b` row (konst+1, oL = suc a).
			emit(e.coeffs, e.konst.add(integerOne), sucT(e.lhs), e.rhs, func() *prop.PropWrapper {
				return canonAssume(e.lhs, e.rhs, opLT, e.hyp, e.hypProof).
					DeriveTrans(sucLessEqIffLessThan(e.lhs, e.rhs).LeftAssume())
			})
		case opEQ:
			if eqGCDUnsat(pad(e.coeffs), e.konst) && gcdBuild == nil {
				// Untrusted: this single equality is gcd-unsat, which is
				// IntUnsat's whole verdict. Its ⊥ PROOF is the grounded
				// one-side-constant route first (groundedGcdEq); the
				// equality's two ≤ rows below are emitted all the same,
				// because their rounding cuts decide every single gcd-unsat
				// equality — Σcx = k with g ∤ k tightens to ⌊k/g⌋ + 1 ≤
				// Σ(c/g)x ≤ ⌊k/g⌋ — and roundedCut proves each cut, which
				// is the proof for the two-sided shapes the grounded route
				// declines (m + m = n + n + 3).
				gcdUnsat = true
				gcdBuild = func() (*prop.PropWrapper, bool) { return groundedGcdEq(e) }
			}
			emit(e.coeffs, e.konst, e.lhs, e.rhs, func() *prop.PropWrapper {
				return mp(lessEqOfEq(e.lhs, e.rhs), e.assumeEq())
			})
			emit(negated(e.coeffs), e.konst.neg(), e.rhs, e.lhs, func() *prop.PropWrapper {
				return mp(lessEqOfEqSwapped(e.lhs, e.rhs), e.assumeEq())
			})
		}
	}
	for i := 0; i < tbl.n(); i++ {
		x := tbl.atoms[i]
		prs = append(prs, lazyProvRow(Numeral(0), x, false, func() *prop.PropWrapper {
			return zeroLe(x)
		}))
		fm = append(fm, unitRow(tbl.n(), i, integerOf(-1)))
	}
	return intProv{tbl: tbl, fm: fm, prs: prs, gcdBuild: gcdBuild, gcdUnsat: gcdUnsat}, true
}

// finalize fixes the rows' coefficient width, readying them for the
// certificate-free FM pass. (Dark-shadow tightening is NOT added here: the dark
// shadow is a SUFFICIENT condition for integer satisfiability, not a necessary
// one, so it cannot soundly strengthen a refutation — the valid integer
// strengthening beyond the per-constraint rounding cut is the gray shadow /
// iterated cuts, which require case-split / provenance-DAG machinery.)
func finalize(tbl *atomTable, fm []row, prs []provRow) ([]row, []provRow) {
	for i := range fm {
		fm[i] = fm[i].padCoeffs(tbl.n())
	}
	return fm, prs
}

// IntRefuteProof decides integer-unsatisfiability and, on success, returns a real
// refutation `{hyps} ⊢ ⊥`. Strengthens LinRefuteProof with the GCD-equality test,
// gcd rounding cuts and the elimination of equations: a gcd-unsat equality is
// proved by the grounded route where its shape allows, else by the cuts of its
// own two ≤ rows. ok=false ⇒ nonlinear input or not refutable by this (sound,
// incomplete) integer procedure.
func IntRefuteProof(cs []LinConstraint) (*prop.PropWrapper, bool) {
	p, ok := buildIntProv(cs)
	if !ok {
		return nil, false
	}
	if p.gcdUnsat && p.gcdBuild != nil {
		if gcdProof, provable := p.gcdBuild(); provable {
			return gcdProof, true
		}
		// The grounded one-side-constant shape declined: the equality's
		// two ≤ rows are in fm, and their rounding cuts refute it below.
	}
	fm2, prs2 := finalize(p.tbl, p.fm, p.prs)
	// The equations go first (equation_elimination.go): Fourier–Motzkin on
	// the two `≤` rows of an equation is the rational projection, and the
	// rows the substitution leaves are the ones whose rounding the integers
	// decide.
	if e, eliminated := eliminateEquations(p.tbl, fm2, prs2, natEliminationLeaves); eliminated {
		lambda, refuted := refute(p.tbl.n(), e.system())
		if !refuted {
			return nil, false
		}
		return replay(e.nodes, e.certificate(lambda))
	}
	lambda, refuted := refute(p.tbl.n(), fm2)
	if !refuted {
		return nil, false
	}
	// replay materializes each used row's proof via pr.proof(); a lazy cut row
	// with an unavailable bundle leaf declines there — replay's per-row check,
	// not an eager upfront one: the same external (nil, false) contract, paid
	// only per used row.
	return replay(prs2, lambda)
}

// Divisibility layer: an omega-INTERNAL `d divides n` predicate and a numeral
// `d divides n` decision (the norm_num comparison's analogue for divisibility), reusing
// norm_num's multiplication.
//
// IMPORTANT — omega's `dvd` is NOT a library divisibility const.
// A divisibility defined through the int subtype tower
// (`a divides b ⟺ int_of_num a int_divides int_of_num b`), with `int` a
// subtype of `real`, routes the proof through the whole ℝ layer when it
// is unfolded. omega never
// needs that: `dvd` is a private predicate used only inside the integer
// refutation (IntRefuteProof / the gcd-equality contradiction), and it is
// EXPOSED to no one — the user-facing `LinProve`/`OmegaProve` goals are linear
// `</≤/=/≠` comparisons, never `divides`. So we define `dvd` nat-natively as the
// existential `∃q. n = q·d`, which keeps the whole integer layer real-free:
//
//   • notDivides bottoms on ModEqZero (`(∃q. n=q·d) ⇔ (0 = nat_mod(n, d))`)
//     + the proof-producing nat_mod evaluator — pure `num`, no `divides`/real.
//   • dividesIntro is a trivial witness intro (∃-intro + MulSym), no bundle
//     lemma of its own.
//
// The cost is only cosmetic: omega's `dvd` is not the corpus's
// divisibility symbol, but since it is purely internal that deviation is
// invisible outside the package.

// NatDividesMeta is a `divides : num→num→bool` const, kept so the test DSL
// can still parse a `divides(d, n)` literal (domain_test.go). It is NOT used
// by omega's proof leaves — see the comment above.
var NatDividesMeta = core.MakeConstMeta("divides", core.MakeFun(dsl.NumType, dsl.NumType, core.TypeBool()))

// dividesWitness is the bound variable of the existential `dvd` builds. Numerals
// (the only terms `dvd` is ever applied to) contain no free vars, so the fixed
// name is capture-safe.
var dividesWitness = ext.Var("q", dsl.NumType)

// dvd builds omega's nat-native divisibility predicate `d divides n` as the
// existential `∃q. n = q·d` (witness on the left of the product, matching
// ModEqZero's shape so notDivides binds it without a commutativity bridge).
func dvd(d, n Term) Term {
	return prop.Exists(dividesWitness)(eqT(n, star(dividesWitness, d)))
}

// dividesIntro: ⊢ (n = d · c) ⇒ ∃q. n = q·d — the ∃-introduction for `dvd`.
// REAL with no bundle lemma of its own: bridge the antecedent `n = d·c` to
// `n = c·d` (MulSym, via commuteMUL) and ∃-intro at witness c. The only named
// dependency is MulSym, already supplied by the ring layer.
func dividesIntro(d, n, c Term) *prop.PropWrapper {
	ante := eqT(n, star(d, c))                          // n = d·c
	body := prop.Assume(ante).EqTrans(commuteMUL(d, c)) // {n=d·c} ⊢ n = c·d
	intro := prop.InstExists(dvd(d, n), c)              // (n = c·d) ⊢ ∃q. n = q·d
	return intro.DeriveHypFrom(body).PromoteHyp(ante)   // ⊢ (n = d·c) ⇒ ∃q. n = q·d
}

// notDivides: ⊢ ¬∃q. n = q·d   (that d ∤ n). REAL via ModEqZero + the nat_mod
// evaluator: compute `nat_mod(n, d) = r`, show `r ≠ 0`, so ModEqZero's RHS `0 = nat_mod(n, d)`
// is ⊥, so its LHS `∃q. n = q·d` is ⊥, i.e. ¬-divides. Sound the moment ModEqZero
// (bundle field ModEqZero) and the nat_mod evaluator (DivModUniq) are
// both supplied; ok=false (no proof) when either is absent — the integer-frontier
// nil contract, declined upstream. NO `divides`/`num_divides`/real dependency.
func notDivides(d, n Term) (*prop.PropWrapper, bool) {
	me := modEqZeroThm()
	modW, okMod := NormNatMod(n, d) // ⊢ nat_mod(n, d) = r
	if me == nil || !okMod {
		return nil, false
	}
	r := prop.Rhs(modW)
	// iff : ⊢ (∃q. n = q·d) ⇔ (0 = nat_mod(n, d)).
	iff := instAll(me, []Term{n, d})
	// ¬(0 = nat_mod(n, d)): assume it, rewrite `nat_mod(n, d) → r` to get `0 = r`, refute it.
	rhs := eqT(Numeral(0), modT(n, d))
	eqFalse, _ := NormNatEq(Numeral(0), r)                 // ⊢ (0 = r) ⇔ ⊥
	contra := eqFalse.EqMP(prop.Assume(rhs).EqTrans(modW)) // {0 = nat_mod(n, d)} ⊢ ⊥
	notRHS := contra.NegHyp(rhs)                           // ⊢ ¬(0 = nat_mod(n, d))
	// ¬LHS from the iff (¬LHS = ¬RHS, and ¬RHS is proven).
	return iff.LeftApply(prop.NOT).EqSym().EqMP(notRHS), true // ⊢ ¬(∃q. n = q·d)
}

// NormNatDivides decides `d divides n` for numeral literals d, n, returning a
// proof (⊢ ∃q. n = q·d  or  ⊢ ¬∃q. n = q·d), whether it holds, and ok.
func NormNatDivides(d, n Term) (*prop.PropWrapper, bool, bool) {
	dx, ok1 := asNumeral(d)
	nx, ok2 := asNumeral(n)
	if !ok1 || !ok2 {
		return nil, false, false
	}
	dv, _ := ext.NumeralValue(dx)
	nv, _ := ext.NumeralValue(nx)
	if dv.Sign() == 0 { // 0 divides n ⟺ n = 0
		if nv.Sign() == 0 { // 0 divides 0: witness anything, e.g. 0·0 = 0.
			mul, _ := NormNatMul(d, Numeral(0)) // ⊢ 0·0 = 0
			return mp(dividesIntro(d, n, Numeral(0)), mul.EqSym()), true, true
		}
		if w, ok := notDivides(d, n); ok {
			return w, false, true
		}
		return nil, false, false
	}
	if quotient, remainder := new(big.Int).QuoRem(nv, dv, new(big.Int)); remainder.Sign() == 0 {
		q := ext.MakeNumeral(quotient)
		mul, _ := NormNatMul(d, q)                     // ⊢ d·q = Numeral(n)
		dThm := mp(dividesIntro(d, n, q), mul.EqSym()) // (n = d·q) ⇒ (∃q. n = q·d)
		return dThm, true, true
	}
	if w, ok := notDivides(d, n); ok {
		return w, false, true
	}
	return nil, false, false
}
