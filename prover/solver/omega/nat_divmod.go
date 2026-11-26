package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// nat_div/nat_mod bounded-atom enrichment — turns opaque nat_div/nat_mod atoms
// into LINARITH-CONSTRAINED atoms by pre-injecting their bounds as extra
// hypotheses, then re-running the linear prover. This is the analog of the
// `0 ≤ x` non-negativity rows the integer refuter injects per num atom
// (buildIntProv, nat_omega.go) — same "atom→bound" pattern, surfaced at the
// goal-decision layer rather than baked into the refuter.
//
// The UNCONDITIONAL bounds
//   • ModLessEq: ∀m n. nat_mod(m,n) ≤ m   (always true, even when n=0)
//   • DivLessEq: ∀m n. nat_div(m,n) ≤ m   (always true)
//
// alone close a large class of goals — `nat_mod(m,n) ≤ m`, `m + nat_mod(a,b) ≤
// m + a`, `nat_div(m,n) ≤ m + 1`, etc. — without any side conditions or case
// splits. The conditional facts (ModLessThan's `m<n ⇒ m=nat_mod(m,n)`, DivEqZero's
// `m<n ⇔ nat_div(m,n)=0` under `n≠0`, the Division identity at a divisor shown
// nonzero) are further entries in the per-atom fact list (divModFacts), each
// gated by a side-condition discharge through proveLinThenInt.

// proveLinDivMod tries `{hyps} ⊢ goal` by injecting unconditional nat_div/nat_mod
// bounds for every nat_div/nat_mod atom in hyps∪{goal}, then calling the linear
// prover with the enriched hyp list. Returns (nil,false) when there is no
// nat_div/nat_mod atom (no enrichment possible — the caller already tried linarith
// directly), or when no bound leaf is available, or when linarith still fails.
//
// Each injected fact is cut back via MaybeDeriveTrans so the returned wrapper
// carries only the original `hyps` — the same "introduce + cut" pattern
// proveSplit uses for case-split branches.
func proveLinDivMod(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	facts := divModFacts(collectDivModAtoms(append(slices.Clone(hyps), goal)), hyps)
	if len(facts) == 0 {
		return nil, false
	}
	return enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) { return proveLinThenInt(slices.Values(h), goal) },
		hyps, facts)
}

// divModFacts builds the per-atom bound proofs. Three tiers, all gated on
// bundle-field availability so a partial supply still injects what it can:
//
//  1. UNCONDITIONAL — `nat_mod(m,n) ≤ m`, `nat_div(m,n) ≤ m`, `nat_mod(n,n) = 0`. Always
//     injected when the corresponding lemma is present.
//  2. n≠0 conditional — Division's `nat_mod(m,n) < n` + `m = nat_div(m,n)·n + nat_mod(m,n)`,
//     DivRefl's `nat_div(n,n) = 1`. Fires when `n ≠ 0` can be discharged from the
//     input hyps via linarith (e.g. literal nonzero n, or symbolic n with
//     `0 < n` in hyps). Division's two conjuncts go in together for a
//     `nat_mod(m,n)` atom and for a `nat_div(m,n)` atom alike, once per (m, n):
//     the remainder's bound says nothing of the dividend without the
//     identity, and the identity leaves the remainder unbounded without the
//     bound (`nat_odd(n) ∧ 1 < n ⊢ 3 ≤ n` reads both, and so does
//     `3 ≤ n ⊢ 1 ≤ nat_div(n, 2)`).
//  3. m<n conditional — ModLessThan's `m = nat_mod(m,n)`. Fires when `m < n` discharges.
//  4. m<n AND n≠0 — DivEqZero's `nat_div(m,n) = 0`. Fires when both discharge; uses
//     DivEqZero's iff direction `m<n ⇒ nat_div(m,n) = 0` (under n≠0).
//
// Each conditional discharges *without* the injected facts — pure proveLinThenInt
// on the input hyps — so there is no nat_div/nat_mod enrichment recursion.
func divModFacts(atoms []Term, hyps []Term) []*prop.PropWrapper {
	var facts []*prop.PropWrapper
	add := func(f *prop.PropWrapper) {
		if f != nil {
			facts = append(facts, f)
		}
	}
	var divided [][2]Term
	division := func(m, n Term) {
		for _, d := range divided {
			if d[0].AlphaEquals(m) && d[1].AlphaEquals(n) {
				return
			}
		}
		divided = append(divided, [2]Term{m, n})
		rest := divisionRest(m, n, hyps)
		if rest == nil {
			return
		}
		bound, identity := lt(modT(m, n), n), eqT(m, plus(star(divT(m, n), n), modT(m, n)))
		add(rest.DeriveTrans(prop.HypAND0(bound, identity)))
		add(rest.DeriveTrans(prop.HypAND1(bound, identity)))
	}
	for _, a := range atoms {
		if m, n, ok := MatchesMod(a); ok {
			if modLessEqThm() != nil {
				add(modLessEq(m, n))
			}
			if m.AlphaEquals(n) && modReflThm() != nil {
				add(modRefl(n))
			}
			// m<n conditional: ModLessThan pins m = nat_mod(m,n).
			if modLessThanThm() != nil {
				if mLt, ok := proveLinThenInt(slices.Values(hyps), lt(m, n)); ok {
					add(mLt.DeriveTrans(modLessThanImp(m, n).DemoteHyp()))
				}
			}
			// n≠0 conditional: Division pins nat_mod(m,n) < n and the identity.
			division(m, n)
			// Dividend a syntactic multiple of the divisor ⇒ nat_mod = 0 (ModEqZero).
			add(modMultZero(m, n))
			// Nested nat_mod with the same divisor ⇒ idempotence (ModModRefl).
			add(modIdemp(m, n))
			continue
		}
		if m, n, ok := MatchesDiv(a); ok {
			if divLessEqThm() != nil {
				add(divLessEq(m, n))
			}
			// Floor LOWER bound n·nat_div(m,n) ≤ m (DivMulLessEq, unconditional) — the
			// companion to divLessEq's upper bound; lets the linear core combine the
			// two into the exact-quotient corridor without re-deriving it.
			if divMulLessEqThm() != nil {
				add(divMulLessEq(m, n))
			}
			// nat_div(n,n) when n≠0 discharges: DivRefl pins nat_div(n,n) = 1.
			if m.AlphaEquals(n) {
				add(divReflFact(n, hyps))
			}
			// m<n AND n≠0 discharge: DivEqZero pins nat_div(m,n) = 0.
			add(divEqZeroFact(m, n, hyps))
			// n≠0 conditional: Division pins the identity and nat_mod(m,n) < n.
			division(m, n)
			// Affine dividend (c·n)+r with n≠0 from hyps: DivMultAdd pins
			// nat_div(c·n+r, n) = c + nat_div(r,n). The symbolic-divisor companion to the
			// literal-only divMultAdd simp leaf — the simp pass already cleared the
			// literal case, so this fires for a symbolic divisor (n≠0 from hyps).
			if divMultAddThm() != nil {
				add(divMultAddFact(m, n, hyps))
			}
		}
	}
	return facts
}

// divisionRest returns Division's right disjunct (the conjunction `nat_mod(m,n) < n
// ∧ m = nat_div(m,n)·n + nat_mod(m,n)`) when `n≠0` discharges, else nil. The discharge
// uses pure linarith on the input hyps — no nat_div/nat_mod enrichment recursion.
func divisionRest(m, n Term, hyps []Term) *prop.PropWrapper {
	if divisionThm() == nil {
		return nil
	}
	nNeq0 := proveNeqZero(n, hyps)
	if nNeq0 == nil {
		return nil
	}
	// Division binder order is (n, m): ∀n m. (n=0) ∨ (nat_mod(m,n)<n ∧ m = nat_div(m,n)·n + nat_mod(m,n))
	disj := instAll(divisionThm(), []Term{n, m})
	return disjSyllogism(disj, nNeq0)
}

// divEqZeroFact returns `⊢ nat_div(m,n) = 0` from DivEqZero when BOTH `n≠0` and `m<n`
// discharge from hyps, else nil.
//
// BOUND SHAPE (the entry's normal form): `∀m n. ((m<n) ⇔ (0 = nat_div(m,n))) ∨ (n=0)` — the iff is the
// LEFT disjunct, (n=0) is on the RIGHT. This is OPPOSITE to the natural order
// my fact-injectors usually see (e.g. Division / DivRefl both have (n=0) on
// the left). disjSyllogism is orientation-agnostic — it discharges the (n=0)
// disjunct whether it is stated on the left or the right — so no manual
// CommuteOR is needed here.
//
// (Historical bug this guards against: an earlier disjSyllogism only extracted
// the RIGHT disjunct given a refutation of the LEFT, so callers had to
// pre-CommuteOR. A caller assuming the (n=0)∨(iff) order — which the TestThm
// unit bundle happened to have — passed its unit test but silently produced a
// partial reduction against the real bound form's (iff)∨(n=0). The orientation-
// agnostic disjSyllogism removes that whole failure class.)
func divEqZeroFact(m, n Term, hyps []Term) *prop.PropWrapper {
	if divEqZeroThm() == nil {
		return nil
	}
	nNeq0 := proveNeqZero(n, hyps)
	if nNeq0 == nil {
		return nil
	}
	mLt, ok := proveLinThenInt(slices.Values(hyps), lt(m, n))
	if !ok {
		return nil
	}
	disj := instAll(divEqZeroThm(), []Term{m, n})
	iff := disjSyllogism(disj, nNeq0) // ⊢ (m<n) ⇔ (0 = nat_div(m,n))
	if iff == nil {
		return nil
	}
	zeroEqDiv := iff.EqMP(mLt) // ⊢ 0 = nat_div(m,n)
	return zeroEqDiv.EqSym()   // ⊢ nat_div(m,n) = 0
}

// divReflFact returns `⊢ nat_div(n,n) = 1` from DivRefl when `n≠0` discharges, else
// nil. DivRefl is `∀n. (n=0) ∨ (1 = nat_div(n,n))`; same disjSyllogism flow.
func divReflFact(n Term, hyps []Term) *prop.PropWrapper {
	if divReflThm() == nil {
		return nil
	}
	nNeq0 := proveNeqZero(n, hyps)
	if nNeq0 == nil {
		return nil
	}
	disj := instAll(divReflThm(), []Term{n})
	rest := disjSyllogism(disj, nNeq0) // ⊢ 1 = nat_div(n,n)
	if rest == nil {
		return nil
	}
	return rest.EqSym() // ⊢ nat_div(n,n) = 1
}

// proveNeqZero proves `⊢ ¬(n = 0)` when it can. Three routes:
//   - direct hyp: `¬(n = 0)` or `¬(0 = n)` is already in hyps — return it.
//   - literal n: NormNatEq decides `(n=0)` numerically; if it yields `⊥`,
//     iffFalseToNot extracts `¬(n=0)`.
//   - symbolic n: discharge `0 < n` via linarith on hyps; then `0<n` and an
//     assumed `n=0` contradict (subst n→0 in 0<n gives 0<0 ⇒ ⊥).
//
// Returns nil when none of the routes closes.
func proveNeqZero(n Term, hyps []Term) *prop.PropWrapper {
	nEq0 := eqT(n, natZero)
	zeroEqN := eqT(natZero, n)
	for _, h := range hyps {
		if h.AlphaEquals(not(nEq0)) {
			return prop.Assume(h) // ⊢ ¬(n = 0)
		}
		if h.AlphaEquals(not(zeroEqN)) {
			// {¬(0=n)} ⊢ ¬(n=0) via the symmetric form of `=`.
			//   prop.CommuteEQ(0, n) : ⊢ (0 = n) ⇔ (n = 0)
			//   ⇒ ¬(0 = n) ⇔ ¬(n = 0) via congruence on ¬, then EqMP with hyp.
			congEq := prop.CommuteEQ(natZero, n).LeftApply(prop.NOT) // ⊢ ¬(0=n) = ¬(n=0)
			return congEq.EqMP(prop.Assume(h))                       // {¬(0=n)} ⊢ ¬(n=0)
		}
	}
	if eqW, ok := NormNatEq(n, natZero); ok && prop.Rhs(eqW).Equals(prop.F) {
		return iffFalseToNot(eqW) // ⊢ ¬(n = 0)
	}
	if pos, ok := proveLinThenInt(slices.Values(hyps), lt(natZero, n)); ok {
		// {hyps, n=0} ⊢ 0<0: rewrite 0<n with n=0. The partial application is
		// `(0 <)`, i.e. ext.Apply(natLt, natZero), so LeftApply on `n=0` gives
		// `⊢ (0 < n) = (0 < 0)`. Then EqMP with `0 < n` flips the equation.
		eqHyp := prop.Assume(eqT(n, natZero))
		cong := eqHyp.LeftApply(ext.Apply(natLt, natZero)) // ⊢ (0<n) = (0<0)
		ltZero := cong.EqMP(pos)                           // {hyps, n=0} ⊢ 0<0
		ltFalse, _ := NormNatLt(natZero, natZero)          // ⊢ (0<0) ⇔ ⊥
		falsity := ltFalse.EqMP(ltZero)
		return falsity.NegHyp(eqT(n, natZero)) // ⊢ ¬(n=0) under {hyps}
	}
	return nil
}

// projectDisjClause finds, among the clauses of `thm`, the disjunction
// `(nonzero = 0) ∨ eq` whose `eq` is `⊢ a = b` in either orientation,
// discharges the `nonzero = 0` disjunct with `nNeq0` (⊢ ¬(nonzero = 0)), and
// returns the equality oriented exactly as `⊢ a = b`. `thm` may be a single
// disjunction or a conjunction of them (splitConjuncts handles both), so this is
// the conditional analog of clauseLeaf/projectMatch — those project an
// unconditional equality conjunct; this projects a `(nonzero=0) ∨ eq` clause and
// kills the side condition. The clause's binders — the conjunction's leading
// ∀ and any conjunct-local ∀ — are matched as metavariables (stripForalls +
// matchBoth, `=` commutative at every level), so how the served normal form
// merges or orders them is not read: a normalized clause pack's binder
// count changes with the normalizer, and positional instantiation once
// read it. nil when no clause matches or the discharge fails.
func projectDisjClause(thm, nNeq0 *prop.PropWrapper, nonzero, a, b Term) *prop.PropWrapper {
	if thm == nil || nNeq0 == nil {
		return nil
	}
	zero := eqT(nonzero, natZero)
	targets := []Term{ext.Or(zero, eqT(a, b)), ext.Or(eqT(a, b), zero)}
	w, base := stripForalls(thm, nil)
	for _, c := range splitConjuncts(w) {
		cc, metas := stripForalls(c, base)
		if _, _, ok := prop.MatchesOR(cc.Conclusion()); !ok {
			continue
		}
		for _, target := range targets {
			sub, ok := matchBoth(cc.Conclusion(), target, nil, nil, metas)
			if !ok {
				continue
			}
			eq := disjSyllogism(cc.TermInst(sub...), nNeq0) // ⊢ (a = b) or (b = a)
			if eq == nil {
				continue
			}
			if el, _, _ := prop.MatchesEQ(eq.Conclusion()); el.AlphaEquals(a) {
				return eq
			}
			return eq.EqSym() // orient ⊢ b = a  →  ⊢ a = b
		}
	}
	return nil
}

// iffFalseToNot: given `⊢ C ⇔ ⊥`, returns `⊢ ¬C`. Inverse of eqfIntro.
func iffFalseToNot(pf *prop.PropWrapper) *prop.PropWrapper {
	return prop.BooleanThms["p ⇔ ⊥"](prop.Lhs(pf)).EqMP(pf)
}

// collectDivModAtoms returns the distinct nat_div/nat_mod subterms of `terms` (inner
// occurrences inside other nat_div/nat_mod are kept — each gets its own bound).
func collectDivModAtoms(terms []Term) []Term {
	return collectRawSubterms(terms, func(t Term) bool {
		if _, _, ok := MatchesDiv(t); ok {
			return true
		}
		_, _, ok := MatchesMod(t)
		return ok
	})
}

// ── Symbolic-n=0 case-split ───────────────────────────────────────────────────
//
// `proveDivModSplitOnZero` handles the gap left by the conditional enricher: an
// irreducible nat_div/nat_mod atom whose divisor `n` is symbolic AND has no `n=0` /
// `0<n` / `n≠0` info in hyps. The basic enricher's `proveNeqZero` declines (no
// way to discharge `n≠0`), so Division / DivRefl / DivEqZero don't fire and the
// goal can't close even when it's actually true.
//
// The split is `(n=0) ∨ (0<n)` — derived from `ExcludedMiddle(n=0)` rewritten
// through PosIffNonzero (`(n≠0) ⇔ (0<n)`) to put the `0<n` form on the right. Per branch:
//
//   - `n=0` branch: inject `nat_mod(m, n) = m` for every nat_mod(_, n) atom (and
//     `nat_div(m, n) = 0` for every nat_div(_, n)), derived via ModZero / DivZero at m
//     plus congruence on n. Recurse — the injected equations replace the opaque
//     nat_div/nat_mod atoms with their `n=0`-branch values, so linarith / ring decide
//     the goal on a value-known atom.
//
//   - `0<n` branch: just inject the hyp; the existing enricher
//     (Division's conjuncts / `divEqZeroFact` / `divReflFact`) fires
//     because `proveNeqZero`'s symbolic route now discharges via the `0<n` hyp.
//
// Both branches recurse into `proveBranchDecAtom` which is `proveDecAtom`
// minus the monus split (no cross-mechanism recursion) plus a back-edge into
// this split (for multiple distinct divisors).  The `doneN` set tracks divisors
// already split on to bound the recursion.

// proveDivModSplitOnZero attempts `{hyps} ⊢ goal` by case-splitting the first
// symbolic divisor n not yet split on (per `doneN`). Returns nil when no such
// divisor exists, when PosIffNonzero / ModZero / DivZero is unbundled, or when either
// branch fails to close.
func proveDivModSplitOnZero(hyps []Term, goal Term, doneN []Term) (*prop.PropWrapper, bool) {
	if posIffNonzeroThm() == nil || modZeroThm() == nil || divZeroThm() == nil {
		return nil, false
	}
	n, ok := firstUnsplitDivisor(hyps, goal, doneN)
	if !ok {
		return nil, false
	}
	doneN = append(slices.Clone(doneN), n)

	nEq0 := eqT(n, natZero)
	zeroLtN := lt(natZero, n)

	// Build disjunction `(n=0) ∨ (0<n)`:
	//   ExcludedMiddle(n=0)               ⊢ (n=0) ∨ ¬(n=0)
	//   PosIffNonzero at n                         ⊢ (n≠0) ⇔ (0<n)
	//   congruence on `(n=0) ∨ _`          ⊢ ((n=0) ∨ ¬(n=0)) ⇔ ((n=0) ∨ (0<n))
	//   EqMP                              ⊢ (n=0) ∨ (0<n)
	em := prop.ExcludedMiddle(nEq0)
	iff := instAll(posIffNonzeroThm(), []Term{n})
	disjPart := ext.Apply(prop.OR, nEq0)
	cong := iff.LeftApply(disjPart)
	disj := cong.EqMP(em)

	// Branch 1: assume n=0. Inject nat_mod(m, n) = m / nat_div(m, n) = 0 for all atoms
	// with divisor n.
	facts := nZeroFactsForDivisor(n, hyps, goal)
	g1, ok1 := enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) { return proveBranchDecAtom(h, goal, doneN) },
		append(slices.Clone(hyps), nEq0), facts)
	if !ok1 {
		return nil, false
	}
	imp1 := g1.PromoteHyp(nEq0)

	// Branch 2: assume 0<n. Existing enricher fires.
	hyps2 := append(slices.Clone(hyps), zeroLtN)
	g2, ok2 := proveBranchDecAtom(hyps2, goal, doneN)
	if !ok2 {
		return nil, false
	}
	imp2 := g2.PromoteHyp(zeroLtN)

	return prop.ByCases(goal, nEq0, zeroLtN).
		DeriveHypFrom(disj).
		DeriveHypFrom(imp1).
		DeriveHypFrom(imp2), true
}

// proveBranchDecAtom is `proveDecAtom` minus the monus split (avoids cross-
// mechanism deep recursion), plus a back-edge into `proveDivModSplitOnZero` to
// handle goals with multiple distinct symbolic divisors.
func proveBranchDecAtom(hyps []Term, goal Term, doneN []Term) (*prop.PropWrapper, bool) {
	if l, r, ok := ext.MatchesEQ(goal); ok && isNat(l) {
		if w, ok := RingProveFull(l, r); ok {
			return w, true
		}
	}
	if w, ok := proveLinThenInt(slices.Values(hyps), goal); ok {
		return w, true
	}
	if w, ok := proveLinDivMod(hyps, goal); ok {
		return w, true
	}
	return proveDivModSplitOnZero(hyps, goal, doneN)
}

// firstUnsplitDivisor returns the first divisor of a nat_div/nat_mod atom in `hyps∪
// {goal}` that is (a) symbolic (not a numeral literal), (b) not already split on
// (per `done`), and (c) has no `n=0` / `0<n` / `n≠0` info already in hyps (in
// which case the conditional enricher would have handled it without a split).
func firstUnsplitDivisor(hyps []Term, goal Term, done []Term) (Term, bool) {
	for _, atom := range collectDivModAtoms(append(slices.Clone(hyps), goal)) {
		var n Term
		if _, na, ok := MatchesMod(atom); ok {
			n = na
		} else if _, na, ok := MatchesDiv(atom); ok {
			n = na
		} else {
			continue
		}
		if isNumeralLit(n) || slices.ContainsFunc(done, n.AlphaEquals) {
			continue
		}
		if hypsAlreadyDecideN(n, hyps) {
			continue
		}
		return n, true
	}
	return nil, false
}

// hypsAlreadyDecideN reports whether `hyps` already give the conditional
// enricher (Division / DivRefl / DivEqZero etc.) what it needs without a split —
// `0<n`, `n≥1`, `¬(n=0)`, `¬(0=n)`. Crucially NOT the `n=0` form: in that case
// the enricher CAN'T fire (it needs n≠0), but the split's n=0 branch CAN —
// it injects nat_mod(m, n) = m / nat_div(m, n) = 0 directly. So a hyp `n=0` is left to
// the split, not flagged here.
func hypsAlreadyDecideN(n Term, hyps []Term) bool {
	for _, h := range hyps {
		if h.AlphaEquals(lt(natZero, n)) || h.AlphaEquals(le(Numeral(1), n)) {
			return true
		}
		if h.AlphaEquals(not(eqT(n, natZero))) || h.AlphaEquals(not(eqT(natZero, n))) {
			return true
		}
	}
	return false
}

// nZeroFactsForDivisor builds the `n=0`-branch fact list: for every nat_mod(m, n)
// atom in `hyps∪{goal}` with matching divisor n, the equation `nat_mod(m, n) = m`
// (derived via the assumed `n=0` plus ModZero at m and a congruence on n); for
// every nat_div(m, n) atom, `nat_div(m, n) = 0` similarly via DivZero. Each returned
// PropWrapper carries `{n=0}` as a hypothesis.
func nZeroFactsForDivisor(n Term, hyps []Term, goal Term) []*prop.PropWrapper {
	var facts []*prop.PropWrapper
	nEq0Assume := prop.Assume(eqT(n, natZero)) // {n=0} ⊢ n = 0
	for _, atom := range collectDivModAtoms(append(slices.Clone(hyps), goal)) {
		if m, na, ok := MatchesMod(atom); ok && na.AlphaEquals(n) {
			// {n=0} ⊢ nat_mod(m, n) = nat_mod(m, 0)   [congruence on n in `nat_mod(m, _)`]
			cong := nEq0Assume.LeftApply(ext.Apply(natMod, m))
			// ⊢ nat_mod(m, 0) = m
			zEq := modZero(m)
			// {n=0} ⊢ nat_mod(m, n) = m
			facts = append(facts, cong.EqTrans(zEq))
		} else if m, na, ok := MatchesDiv(atom); ok && na.AlphaEquals(n) {
			cong := nEq0Assume.LeftApply(ext.Apply(natDiv, m))
			zEq := divZero(m)
			facts = append(facts, cong.EqTrans(zEq))
		}
	}
	return facts
}

// Integer Euclidean division/remainder (`int_div`/`int_rem`) — the `int`-type twin of the
// num nat_div/nat_mod bounded-atom enrichment. `int_div`/`int_rem` are opaque to
// linarith and the ring atomizes them; this file turns them into LINARITH-
// CONSTRAINED atoms by injecting their bounds as extra hypotheses and re-running
// the int forward prover (the same "atom → bound" pattern as the num side).
//
// ONE int twist reshapes it. num leans on the UNCONDITIONAL `nat_mod(m,n) ≤ m` /
// `nat_div(m,n) ≤ m` — but those are FALSE for a signed dividend (int `rem ≥ 0`, so
// `m < 0 ⇒ int_rem(m,n) > m`; `int_rem(m,n) ≤ m` is no theorem, and the quotient bound is
// `|div| ≤ |m|`). So the backbone here is instead:
//
//   - DivisionIdentity `m = int_div(m,n)·n + int_rem(m,n)` — UNCONDITIONAL, injected for
//     every int_div/int_rem atom;
//   - RemNonneg `(n=&0) ∨ (&0 ≤ int_rem(m,n))` and RemBelowDivisor `(&0<n) ⇒ int_rem(m,n)<n`
//     — the [0,n) bound, injected when `&0 < n` discharges from the hyps.
//
// For a LITERAL (or otherwise positive) divisor n the identity `int_div(m,n)·n` is
// linear in the `int_div` atom, so these three facts pin the values via linarith +
// ℤ-discreteness with NO separate literal evaluator: e.g. `int_div(&7,&2) = &3` falls
// out of `7 = 2·d + r ∧ 0 ≤ r < 2`. Plus a simp pass for the divisor-0/1 folds.
//
// Out of this first cut (the natural extension): the int_abs-carrying general
// bound RemUpperAbs (`int_rem(m,n) < int_abs(n)`) for a NEGATIVE / unknown-sign
// divisor — which composes with the int_abs case split (int_split.go) — and the
// symbolic `n=&0` split off RemUpperAbs's own `(n=&0) ∨ …` disjunction.

// ── simp folds (divisor 0 / 1) ────────────────────────────────────────────────

// intDivModSimp folds a `int_div`/`int_rem` with a CONSTANT divisor: literal operands
// evaluate to their numeric value (DivModUnique), and a `&0` / `&1` divisor
// folds even for a symbolic dividend (DivByZero / RemByZero / DivByOne /
// RemByOne). nil otherwise. Driven deep + to fixpoint by intArithSimpStep's
// DeepRewrite, so a int_div/int_rem redex anywhere collapses before the decide leaf runs.
func intDivModSimp(t Term) *prop.PropWrapper {
	if m, n, ok := MatchesIntDiv(t); ok {
		return intDivModFold(m, n, true)
	}
	if m, n, ok := MatchesIntRem(t); ok {
		return intDivModFold(m, n, false)
	}
	return nil
}

// intDivModFold rewrites `int_div(m,n)` (wantDiv) or `int_rem(m,n)` for a constant
// divisor: literal operands → numeric value via DivModUnique; `&0` / `&1`
// divisor → the def folds. nil otherwise.
func intDivModFold(m, n Term, wantDiv bool) *prop.PropWrapper {
	// Literal operands, nonzero divisor → evaluate. Int literals are
	// nonnegative, so divMod gives the Euclidean (q,r) with 0 ≤ r < n.
	if mv, mok := intLitVal(m); mok {
		if nv, nok := intLitVal(n); nok && !nv.isZero() {
			quotient, remainder := mv.divMod(nv)
			return intDivModUniqWitness(m, n, intLitOf(quotient), intLitOf(remainder), wantDiv)
		}
	}
	// OfNum bridge fallback: when both operands are int_of_num-wrapped
	// but the intLitVal path declined (e.g. a symbolic num expression as the
	// inner num arg), route through num's nat_div/nat_mod evaluator via OfNumDiv
	// / OfNumRem. Same coverage as intLitVal for bit-tree pairs; useful
	// when a future num-side normalization makes the inner num args evaluable.
	if wantDiv {
		if w, ok := intNormNatDiv(m, n); ok {
			return w
		}
	} else {
		if w, ok := intNormNatMod(m, n); ok {
			return w
		}
	}
	// DivMulAdd / RemMulAdd distribution: when the dividend
	// is of the form `residual + n·p` and n is a literal nonzero, strip the
	// `n·p` summand. Discharging `~(n=&0)` requires n be a literal — for a
	// symbolic n with the nonzero hyp in context, a separate enrichment-style
	// handler would be needed; not in this cut.
	if w := intDivModAddMulFold(m, n, wantDiv); w != nil {
		return w
	}
	if isIntZero(n) { // int_div(m,&0)=&0 / int_rem(m,&0)=m
		if wantDiv {
			return intEqLeaf(intDivByZeroThm(), []Term{m}, intDivT(m, intLit(0)), intLit(0))
		}
		return intEqLeaf(intRemByZeroThm(), []Term{m}, intRemT(m, intLit(0)), m)
	}
	if isIntOne(n) { // int_div(m,&1)=m / int_rem(m,&1)=&0
		if wantDiv {
			return intEqLeaf(intDivByOneThm(), []Term{m}, intDivT(m, intLit(1)), m)
		}
		return intEqLeaf(intRemByOneThm(), []Term{m}, intRemT(m, intLit(1)), intLit(0))
	}
	return nil
}

// intDivModAddMulFold folds `int_div(X, n) → int_div(residual, n) + p` (wantDiv) or
// `int_rem(X, n) → int_rem(residual, n)` when X is of form `residual + (n · p)` and n
// is a literal nonzero — via DivMulAdd / RemMulAdd. nil otherwise.
//
// Discharging the div law's `~(n=&0)` requires n be a literal in this cut
// (norm_num evaluates `&k = &0` to ⊥ for k>0). A symbolic n with `n ≠ &0` in
// hyps would need a separate enrichment-style handler; left out. The rem law
// has no guard, and the fold keeps the same literal-nonzero gate for it: a
// zero divisor is the caller's own fold path.
//
// Match shape: X = `residual + (n · p)` — the outer `+` of X, with the n·p
// monomial as its RIGHT factor. Commuted / left-position / non-rightmost-
// summand forms aren't matched here; ring AC normalization typically puts the
// dividend into right-associated canonical order before this simp visits it,
// so the rightmost-summand match catches the common case.
func intDivModAddMulFold(X, n Term, wantDiv bool) *prop.PropWrapper {
	nv, nok := intLitVal(n)
	if !nok || nv.isZero() {
		return nil // need a literal nonzero n to discharge ~(n=&0)
	}
	residual, summandStar, ok := intDomain.matchPlus(X)
	if !ok {
		return nil
	}
	nFac, p, ok := intDomain.matchStar(summandStar)
	if !ok || !nFac.AlphaEquals(n) {
		return nil // RHS of the outer + must be exactly n · p
	}
	// Discharge ~(&n = &0) from the literal evaluator: NormNatEq(&n, &0) ⇔ ⊥.
	iff, ok := intNormNatEq(n, intLit(0))
	if !ok {
		return nil
	}
	if !prop.Rhs(iff).Equals(prop.F) {
		return nil // n was &0 — different fold path, the caller handles it
	}
	notEq := iffFalseToNot(iff) // ⊢ ~(&n = &0)
	if wantDiv {
		return mp(intDivMulAdd(residual, n, p), notEq)
	}
	return intRemMulAdd(residual, n, p)
}

// intDivModUniqWitness folds `int_div(m,n)` (wantDiv) / `int_rem(m,n)` to a CONSTANT
// witness (q,r) via DivModUnique, when the three premises `m = q·n + r`,
// `&0 ≤ r`, `r < int_abs(n)` all decide to ⊤ (ground — the int_abs upper bound
// through the int_abs split). The int twin of num's divModUniqWitness, with
// DivModUnique's extra `&0 ≤ r` conjunct + int_abs in the upper bound. nil
// when a premise does not close.
func intDivModUniqWitness(m, n, q, r Term, wantDiv bool) *prop.PropWrapper {
	eqConcl := eqT(m, intPlusT(intStarT(q, n), r))
	leConcl := intLeT(intLit(0), r)
	ltConcl := intLtT(r, intAbsT(n))
	eqP, ok1 := intDecideTrueProof(eqConcl)
	leP, ok2 := intDecideTrueProof(leConcl)
	ltP, ok3 := intDecideTrueProof(ltConcl)
	if !ok1 || !ok2 || !ok3 {
		return nil
	}
	// antecedent `(m=q·n+r ∧ &0≤r) ∧ r<int_abs(n)` — left-associated, the shape the
	// bound clause `(((m≠q·n+r)∨¬(&0≤r))∨¬(r<|n|)) ∨ concl` normalizes to.
	inner := prop.ConclAND(eqConcl, leConcl).DeriveHypFrom(eqP).DeriveHypFrom(leP)
	ante := prop.ConclAND(prop.And(eqConcl, leConcl), ltConcl).
		DeriveHypFrom(inner).DeriveHypFrom(ltP) // ⊢ (eqConcl ∧ leConcl) ∧ ltConcl
	divEq := eqT(q, intDivT(m, n)) // bound orientation q = int_div(m,n)
	remEq := eqT(r, intRemT(m, n))
	impl := intImplyLeaf(intDivModUniqueThm(), []Term{m, q, n, r},
		imply(prop.And(prop.And(eqConcl, leConcl), ltConcl), prop.And(divEq, remEq)))
	full := mp(impl, ante) // ⊢ (q=int_div(m,n)) ∧ (r=int_rem(m,n))
	if wantDiv {
		return full.DeriveTrans(prop.HypAND0(divEq, remEq)).EqSym() // ⊢ int_div(m,n) = q
	}
	return full.DeriveTrans(prop.HypAND1(divEq, remEq)).EqSym() // ⊢ int_rem(m,n) = r
}

// intDecideTrueProof returns `⊢ goal` when the int decider collapses goal to ⊤.
func intDecideTrueProof(goal Term) (*prop.PropWrapper, bool) {
	w := IntArithDecide(goal)
	if w == nil || !prop.Rhs(w).Equals(prop.T) {
		return nil, false
	}
	return iffTrueElim(w), true
}

// ── bounded-atom enrichment ───────────────────────────────────────────────────

// intProveDivRem tries `{hyps} ⊢ goal` by injecting the int_div/int_rem bounds for every
// int_div/int_rem atom in hyps∪{goal}, then re-running the int linear prover with the
// enriched hyp list. Returns (nil,false) when there is no int_div/int_rem atom (no
// enrichment possible) or when linarith still fails. Each injected fact is cut
// back via enrichAndCut so the returned wrapper carries only the original `hyps`
// (the IsStronger contract). The inner prover is IntLinProve — pure linarith, so
// no re-entry into this handler.
func intProveDivRem(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	facts := intDivModFacts(collectIntDivRemPairs(append(slices.Clone(hyps), goal)), hyps)
	if len(facts) == 0 {
		return nil, false
	}
	// The re-run is IntLinProve, then the int_abs split: a general `rem < int_abs(n)`
	// bound (negative/unknown-sign divisor) only reaches a sign-specific goal like
	// `rem < −n` after the int_abs(n) atom is pinned per the divisor's sign. The
	// split's branch prover stays IntLinProve, so this never re-enters intProveDivRem.
	return enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) {
			if w, ok := IntLinProve(slices.Values(h), goal); ok {
				return w, true
			}
			return intProveSplit(IntLinProve, nil, h, goal, nil)
		},
		hyps, facts)
}

// intDivModFacts builds the per-(m,n) bound proofs:
//
//  1. UNCONDITIONAL — DivisionIdentity's identity `m = int_div(m,n)·n + int_rem(m,n)`,
//     injected for every distinct divisor pair.
//  2. 0<n conditional — RemNonneg's `&0 ≤ int_rem(m,n)` (via `¬(n=&0)` derived from
//     the `&0<n` discharge) and RemBelowDivisor's `int_rem(m,n) < n`. Fires when `&0 < n`
//     discharges from the input hyps via linarith (a literal positive divisor, or
//     a symbolic one with `&0 < n` in hyps).
//
// The conditional discharge uses pure IntLinProve on the input hyps — no int_div/int_rem
// enrichment recursion.
func intDivModFacts(pairs [][2]Term, hyps []Term) []*prop.PropWrapper {
	var facts []*prop.PropWrapper
	add := func(f *prop.PropWrapper) {
		if f != nil {
			facts = append(facts, f)
		}
	}
	for _, p := range pairs {
		m, n := p[0], p[1]
		add(intDivIdentity(m, n)) // m = int_div(m,n)·n + int_rem(m,n)  (always)
		if zeroLt, ok := IntLinProve(slices.Values(hyps), intLtT(intLit(0), n)); ok {
			neq0 := intNeqZeroFromPos(n, zeroLt)
			add(intRemNonneg(m, n, neq0))  // &0 ≤ int_rem(m,n)
			add(intRemUpper(m, n, zeroLt)) // int_rem(m,n) < n  (tight: 0 < n)
		} else if neq0, ok := intProveNeqZero(hyps, n); ok {
			// negative / unknown-sign divisor: the general division bounds
			// `&0 ≤ int_rem(m,n)` and `int_rem(m,n) < int_abs(n)` (RemBelowDivisor's `rem < n` is false
			// here). The int_abs upper bound composes with the int_abs case split.
			add(intRemNonneg(m, n, neq0))   // &0 ≤ int_rem(m,n)
			add(intRemUpperAbs(m, n, neq0)) // int_rem(m,n) < int_abs(n)
		}
	}
	return facts
}

// intDivIdentity returns `⊢ m = int_div(m,n)·n + int_rem(m,n)` (DivisionIdentity,
// unconditional). Placeholder-backed via intEqLeaf when unbundled.
func intDivIdentity(m, n Term) *prop.PropWrapper {
	rhs := intPlusT(intStarT(intDivT(m, n), n), intRemT(m, n))
	return intEqLeaf(intDivisionIdentityThm(), []Term{m, n}, m, rhs)
}

// intRemNonneg returns `{hyps} ⊢ &0 ≤ int_rem(m,n)` from RemNonneg's
// `(n=&0) ∨ (&0 ≤ int_rem(m,n))`, discharging the `n=&0` disjunct with `neq0`
// (`⊢ ¬(n=&0)`). The disjunction comes through intImplyLeaf (the bound shape
// directly, or a placeholder stand-in), so no bundle-nil guard. nil when neq0 is
// nil. Binder order (b,a) → [n,m].
func intRemNonneg(m, n Term, neq0 *prop.PropWrapper) *prop.PropWrapper {
	if neq0 == nil {
		return nil
	}
	disj := intImplyLeaf(intRemNonnegThm(), []Term{n, m},
		or(eqT(n, intLit(0)), intLeT(intLit(0), intRemT(m, n)))) // ⊢ (n=&0) ∨ (&0 ≤ int_rem(m,n))
	return disjSyllogism(disj, neq0) // {hyps} ⊢ &0 ≤ int_rem(m,n)
}

// intRemUpper returns `{hyps} ⊢ int_rem(m,n) < n` from RemBelowDivisor's implication
// `(&0<n) ⇒ int_rem(m,n)<n` (the macro reshapes the bound clause `¬(&0<n) ∨
// int_rem(x,n)<n`), modus-ponens'd with the `&0<n` proof. Binder order (n,x) → [n,m].
func intRemUpper(m, n Term, zeroLt *prop.PropWrapper) *prop.PropWrapper {
	if zeroLt == nil {
		return nil
	}
	imp := intImplyLeaf(intRemBelowDivisorThm(), []Term{n, m},
		imply(intLtT(intLit(0), n), intLtT(intRemT(m, n), n))) // ⊢ (&0<n) ⇒ int_rem(m,n)<n
	return zeroLt.DeriveTrans(imp.DemoteHyp()) // {hyps} ⊢ int_rem(m,n) < n
}

// intNeqZeroFromPos derives `{hyps} ⊢ ¬(n=&0)` from `zeroLt = {hyps} ⊢ &0<n`:
// assume n=&0, rewrite `&0<n` to `&0<&0`, which norm_num refutes, then NegHyp.
// Mirror of the symbolic route of num's proveNeqZero. nil if the
// `&0<&0` norm_num fold is unavailable.
func intNeqZeroFromPos(n Term, zeroLt *prop.PropWrapper) *prop.PropWrapper {
	nEq0 := eqT(n, intLit(0))
	cong := prop.Assume(nEq0).LeftApply(ext.Apply(intLt, intLit(0))) // ⊢ (&0<n) = (&0<&0)
	ltZero := cong.EqMP(zeroLt)                                      // {hyps, n=&0} ⊢ &0<&0
	ltFalse, ok := intNormNatLt(intLit(0), intLit(0))                // ⊢ (&0<&0) ⇔ ⊥
	if !ok {
		return nil
	}
	return ltFalse.EqMP(ltZero).NegHyp(nEq0) // {hyps} ⊢ ¬(n=&0)
}

// intNeqZeroFromNeg derives `{hyps} ⊢ ¬(n=&0)` from `ltZero = {hyps} ⊢ n<&0`:
// assume n=&0, rewrite `n<&0` to `&0<&0`, refute. The negative-divisor twin of
// intNeqZeroFromPos. nil if the `&0<&0` norm_num fold is unavailable.
func intNeqZeroFromNeg(n Term, ltZero *prop.PropWrapper) *prop.PropWrapper {
	nEq0 := eqT(n, intLit(0))
	cong := prop.Assume(nEq0).LeftApply(intLt).RightApply(intLit(0)) // ⊢ (n<&0) = (&0<&0)
	zZero := cong.EqMP(ltZero)                                       // {hyps, n=&0} ⊢ &0<&0
	ltFalse, ok := intNormNatLt(intLit(0), intLit(0))                // ⊢ (&0<&0) ⇔ ⊥
	if !ok {
		return nil
	}
	return ltFalse.EqMP(zZero).NegHyp(nEq0) // {hyps} ⊢ ¬(n=&0)
}

// intProveNeqZero derives `{hyps} ⊢ ¬(n=&0)` for the int_div/int_rem general bound: an
// explicit `¬(n=&0)` hyp, or `&0<n` / `n<&0` derivable from the hyps. ok=false
// when n's nonzeroness cannot be established.
func intProveNeqZero(hyps []Term, n Term) (*prop.PropWrapper, bool) {
	nNeq0 := not(eqT(n, intLit(0)))
	if slices.ContainsFunc(hyps, nNeq0.AlphaEquals) {
		return prop.Assume(nNeq0), true
	}
	if zeroLt, ok := IntLinProve(slices.Values(hyps), intLtT(intLit(0), n)); ok {
		if w := intNeqZeroFromPos(n, zeroLt); w != nil {
			return w, true
		}
	}
	if ltZero, ok := IntLinProve(slices.Values(hyps), intLtT(n, intLit(0))); ok {
		if w := intNeqZeroFromNeg(n, ltZero); w != nil {
			return w, true
		}
	}
	return nil, false
}

// intRemUpperAbs returns `{hyps} ⊢ int_rem(m,n) < int_abs(n)` from RemUpperAbs's
// `(n=&0) ∨ (int_rem(m,n) < int_abs(n))`, discharging the `n=&0` disjunct with `neq0`
// (`⊢ ¬(n=&0)`). The negative/unknown-sign-divisor companion of intRemUpper (whose
// `rem < n` bound is false for n < &0). nil when neq0 is nil. Binder (b,a) → [n,m].
func intRemUpperAbs(m, n Term, neq0 *prop.PropWrapper) *prop.PropWrapper {
	if neq0 == nil {
		return nil
	}
	disj := intImplyLeaf(intRemUpperAbsThm(), []Term{n, m},
		or(eqT(n, intLit(0)), intLtT(intRemT(m, n), intAbsT(n)))) // ⊢ (n=&0) ∨ (int_rem(m,n) < int_abs(n))
	return disjSyllogism(disj, neq0) // {hyps} ⊢ int_rem(m,n) < int_abs(n)
}

// collectIntDivRemPairs returns the distinct `(m,n)` dividend/divisor pairs of
// every `int_div(m,n)` / `int_rem(m,n)` subterm in `terms` (a div and a rem with the same
// (m,n) collapse to one pair, since the injected identity references both).
func collectIntDivRemPairs(terms []Term) [][2]Term {
	atoms := collectRawSubterms(terms, func(t Term) bool {
		if _, _, ok := MatchesIntDiv(t); ok {
			return true
		}
		_, _, ok := MatchesIntRem(t)
		return ok
	})
	var pairs [][2]Term
	for _, a := range atoms {
		var m, n Term
		if mm, nn, ok := MatchesIntDiv(a); ok {
			m, n = mm, nn
		} else if mm, nn, ok := MatchesIntRem(a); ok {
			m, n = mm, nn
		} else {
			continue
		}
		if !slices.ContainsFunc(pairs, func(q [2]Term) bool {
			return q[0].AlphaEquals(m) && q[1].AlphaEquals(n)
		}) {
			pairs = append(pairs, [2]Term{m, n})
		}
	}
	return pairs
}

// Trivial nat_div/nat_mod simp leaves — the closed-form rewrites that fire
// inside arithSimpStep. Each handles a syntactic case (literal divisor 0/1,
// reflexive nat_mod) the symbolic enricher would otherwise carry as an opaque atom.
//
// Unconditional (no side condition needed):
//   nat_div(m, 0) → 0  (DivZero)         nat_div(m, 1) → m  (DivModUniq witness q=m,r=0)
//   nat_mod(m, 0) → m  (ModZero)         nat_mod(m, 1) → 0  (DivModUniq witness q=m,r=0)
//   nat_mod(n, n) → 0  (ModRefl)
//
// Conditional / case-split shapes (`nat_div(n, n) → 1` needs n≠0; `nat_mod(m,n) → m` needs
// m<n) live in the symbolic enricher, not here.

// divModSimp dispatches a `nat_div(_,_)` or `nat_mod(_,_)` redex to its closed-form
// rewrite, or nil when no syntactic case applies. arithSimpStep calls it.
func divModSimp(t Term) *prop.PropWrapper {
	if m, n, ok := MatchesDiv(t); ok {
		switch {
		case isZeroNum(n): // nat_div(m, 0) → 0
			return divZero(m)
		case isOneNum(n): // nat_div(m, 1) → m
			return divOneSimp(m)
		}
		// Common-factor cancellation `nat_div(c·a, c·b) → nat_div(a, b)` for literal
		// nonzero c (DivMult2). Simp leaves have no hyps access, so symbolic c
		// with c≠0 dischargeable from hyps is left to a future enricher path.
		if w := divCommonFactor(m, n); w != nil {
			return w
		}
		// Nested nat_div `nat_div(nat_div(p,q), n) → nat_div(p, q·n)` (DivDiv, unconditional).
		if w := divDivNest(m, n); w != nil {
			return w
		}
		// Conditional affine nat_div `nat_div((c·n)+r, n) → c + nat_div(r,n)` (DivMultAdd,
		// literal divisor only — the n≠0 side condition discharges numerically).
		if w := divMultAdd(m, n); w != nil {
			return w
		}
		return divModEvalSimp(m, n, true) // literal `nat_div(c1, c2) → c`
	}
	if m, n, ok := MatchesMod(t); ok {
		switch {
		case isZeroNum(n): // nat_mod(m, 0) → m
			return modZero(m)
		case isOneNum(n): // nat_mod(m, 1) → 0
			return modOneSimp(m)
		case m.AlphaEquals(n): // nat_mod(n, n) → 0
			return modRefl(m)
		}
		// Affine nat_mod `nat_mod(c·n + r, n) → nat_mod(r, n)` (ModMultAdd, unconditional);
		// generalizes the multiple-is-zero fact `nat_mod(k·n, n) = 0`.
		if w := modMultAdd(m, n); w != nil {
			return w
		}
		// Combine `nat_mod(nat_mod(a,n)+nat_mod(b,n), n) → nat_mod(a+b, n)` (ModAddMod, the
		// term-shrinking direction of the bound form's distribute orientation).
		if w := modAddMod(m, n); w != nil {
			return w
		}
		return divModEvalSimp(m, n, false) // literal `nat_mod(c1, c2) → c`
	}
	return nil
}

// divDivNest rewrites a nested `nat_div(nat_div(p,q), n) → nat_div(p, q·n)` via DivDiv
// (`∀m n p. (nat_div(m, n)) nat_div p = m nat_div (n·p)`, unconditional). nil when the dividend
// is not itself a nat_div or DivDiv is unbundled. eqLeaf auto-orients.
func divDivNest(dividend, n Term) *prop.PropWrapper {
	if divDivThm() == nil {
		return nil
	}
	p, q, ok := MatchesDiv(dividend)
	if !ok {
		return nil
	}
	return eqLeaf(divDivThm(), []Term{p, q, n}, divT(divT(p, q), n), divT(p, star(q, n)))
}

// modMultAdd rewrites an affine `nat_mod(c·n + r, n) → nat_mod(r, n)` via ModMultAdd
// when one summand of the dividend is a multiple of the divisor n. The bound
// ModMultAdd is a 4-CLAUSE conjunction covering every shape — multiple as the
// first or second summand, n as the left or right factor (`nat_mod(p,n)=nat_mod(m·n+p,n)`,
// `nat_mod(s,n)=nat_mod(n·m+s,n)`, `nat_mod(r,n)=nat_mod(r+n·k,n)`, `nat_mod(r,n)=nat_mod(r+k·n,n)`) — so
// clauseLeaf/projectMatch picks the matching conjunct (either orientation) with no
// manual MulSym bridge. Generalizes modMultZero (the r=0 case) to a
// nonzero remainder. nil when neither summand is a multiple of n / when unbundled.
func modMultAdd(x, n Term) *prop.PropWrapper {
	if modMultAddThm() == nil {
		return nil
	}
	a, b, ok := MatchesPlus(x)
	if !ok {
		return nil
	}
	var r Term
	switch {
	case isMultipleOf(a, n): // x = (c·n) + r
		r = b
	case isMultipleOf(b, n): // x = r + (c·n)
		r = a
	default:
		return nil // neither summand is a multiple of n.
	}
	// Project the conjunct matching `nat_mod(x, n) = nat_mod(r, n)` from the conjunction.
	return clauseLeaf(modMultAddThm(), nil, modT(x, n), modT(r, n))
}

// isMultipleOf reports whether t is a product `c·n` or `n·c` (n appears as a
// syntactic factor).
func isMultipleOf(t, n Term) bool {
	f1, f2, ok := MatchesStar(t)
	return ok && (f1.AlphaEquals(n) || f2.AlphaEquals(n))
}

// divModEvalSimp evaluates a fully-literal `nat_div(c1, c2)` / `nat_mod(c1, c2)` to its
// numeral value via divmodEval (DivModUniq witness). Guards make it a graceful
// no-op rather than a placeholder-emitting leaf: it requires both operands to be
// BIT-tree literals, the DivModUniq bundle field present, and — belt and braces —
// snapshots the unsound-leaf counter, rejecting the result if divmodEval degraded
// to a placeholder (which would bump it). So under the real bundle it folds the
// literal; with no/partial bundle it leaves the nat_mod/nat_div opaque, never unsound.
// This is what makes a bridged literal parity goal close (nat_even 4 → 0 = nat_mod(4, 2) →
// 0 = 0), and folds any literal nat_div/nat_mod redex the prior special cases missed.
func divModEvalSimp(m, n Term, wantDiv bool) *prop.PropWrapper {
	if divModUniqThm() == nil {
		return nil
	}
	if !isBitTree(m) || !isBitTree(n) {
		return nil
	}
	w, ok := divmodEval(m, n, wantDiv)
	if !ok {
		return nil
	}
	return w
}

// divOneSimp / modOneSimp: derive `nat_div(m, 1) = m` / `nat_mod(m, 1) = 0` from DivModUniq
// at the witness (q := m, r := 0): `m = m·1 + 0 ∧ 0 < 1`. The first conjunct is
// ring; the second is a numeric NormNatLt.
func divOneSimp(m Term) *prop.PropWrapper {
	return divModUniqWitness(m, Numeral(1), m, natZero, true)
}
func modOneSimp(m Term) *prop.PropWrapper {
	return divModUniqWitness(m, Numeral(1), m, natZero, false)
}

// divModUniqWitness proves `nat_div(m,n) = q` (wantDiv) or `nat_mod(m,n) = r` from
// DivModUniq at the witness (q, r) for a concrete divisor n. The premises
// `m = q·n + r` (ring) and `r < n` (NormNatLt) must both close. nil on absent
// DivModUniq supply or a witness that does not ring-witness; never marks the
// unsound counter (the soundness is in DivModUniq itself, ring is sound).
func divModUniqWitness(m, n, q, r Term, wantDiv bool) *prop.PropWrapper {
	uniq := divModUniqThm()
	if uniq == nil {
		return nil
	}
	// Fast path for the only production callers (divOneSimp/modOneSimp): witness
	// (q := m, n := 1, r := 0) — the identity `m = m·1 + 0` is two trivial
	// MulClauses / AddClauses leaves, no ringProveFull needed.
	var eqW *prop.PropWrapper
	if isOneNum(n) && isZeroNum(r) && q.AlphaEquals(m) {
		// ⊢ m·1 + 0 = m + 0 = m   ⇒  ⊢ m = m·1 + 0
		eqW = mulOneR(m).LeftApply(natPlus).RightApply(natZero).
			EqTrans(addZeroR(m)).EqSym()
	} else {
		var ok bool
		eqW, ok = RingProveFull(m, plus(star(q, n), r)) // ⊢ m = q·n + r
		if !ok {
			return nil
		}
	}
	ltW, ok := NormNatLt(r, n) // ⊢ (r < n) ⇔ ⊤
	if !ok {
		return nil
	}
	ltProof := ltW.EqSym().EqMP(prop.DerivesTrue) // ⊢ r < n
	eqConcl := eqT(m, plus(star(q, n), r))
	ltConcl := lt(r, n)
	divEq := eqT(divT(m, n), q)
	modEq := eqT(modT(m, n), r)
	ante := prop.ConclAND(eqConcl, ltConcl).DeriveHypFrom(eqW).DeriveHypFrom(ltProof)
	impl, ok := macroThm(uniq, []Term{m, n, q, r},
		imply(prop.And(eqConcl, ltConcl), prop.And(divEq, modEq)))
	if !ok {
		return nil
	}
	full := mp(impl, ante) // ⊢ (nat_div(m,n) = q) ∧ (nat_mod(m,n) = r)
	if wantDiv {
		return full.DeriveTrans(prop.HypAND0(divEq, modEq))
	}
	return full.DeriveTrans(prop.HypAND1(divEq, modEq))
}

// divCommonFactor rewrites `nat_div(c·a, c·b) → nat_div(a, b)` when c is a literal
// nonzero numeral and both operands have c as their LEFT factor. Built from
// DivMult2 (`∀m n p. (m=0) ∨ (nat_div(n,p) = nat_div(m·n, m·p))`): instantiate at
// (c, a, b), disjSyllogism out the `c=0` branch (c≠0 via NormNatEq since c is a
// literal), EqSym for the wanted rewrite direction. nil when DivMult2 is
// unbundled, no shared literal factor, or c=0 / c is non-literal.
//
// Right-factor `nat_div(a·c, b·c)` is NOT handled here (the bound DivMult2 fixes
// the factor on the left); it could be added via a MulSym rewrite of both
// operands first, but in practice the engine's products carry literal
// coefficients on the left (`2*a`, not `a*2`), so left-factor is the common case.
func divCommonFactor(num, den Term) *prop.PropWrapper {
	if divMult2Thm() == nil {
		return nil
	}
	c1, a, ok := MatchesStar(num)
	if !ok || !isNumeralLit(c1) {
		return nil
	}
	c2, b, ok := MatchesStar(den)
	if !ok || !c1.AlphaEquals(c2) {
		return nil
	}
	nNeq0 := proveNeqZero(c1, nil) // literal-only route (no hyps in simp)
	if nNeq0 == nil {
		return nil
	}
	// DivMult2 clause is `(c=0) ∨ (nat_div(a,b) = nat_div(c·a, c·b))`; projectDisjClause
	// discharges c≠0 and orients to the reducing direction ⊢ nat_div(c·a,c·b)=nat_div(a,b).
	return projectDisjClause(divMult2Thm(), nNeq0, c1, divT(num, den), divT(a, b))
}

// nat_div/nat_mod distribution leaves. They complete the
// residue/quotient normal form alongside the already-wired ModMultAdd /
// DivDiv / ModModRefl:
//
//   - divMultAdd — the nat_div companion to modMultAdd: extracts the multiple-of-n
//     part of an affine dividend as the quotient. CONDITIONAL (n≠0). It fires on
//     two surfaces sharing one core (divMultAddEq): a literal-divisor SIMP rewrite
//     (divMultAdd, hyp-free n≠0 discharge — a valid prop.Rewrite leaf) and a
//     symbolic-divisor ENRICHMENT fact (divMultAddFact, n≠0 discharged from hyps —
//     injected by divModFacts). The split is forced by the prop.Rewrite contract:
//     a rewrite must be hyp-free, so a symbolic n≠0 — whose proof carries goal
//     hyps — can only enter as a fact, not as a simp rewrite.
//   - modAddMod — ModAddMod wired in the COMBINE (term-shrinking) direction.
//
// DivAddMod is deliberately NOT given a leaf: it is a relational iff with no
// normalizing direction (see bundle.go's DivAddMod doc). All are kernel-backed
// and degrade to a no-op (nil) when their bundle field is absent or the syntactic
// shape does not match.

// divMultAddEq builds the DivMultAdd equality
//
//	nat_div((c·den) + r, den) = c + nat_div(r, den)     (multiple is the FIRST summand)
//	nat_div(r + (c·den), den) = nat_div(r, den) + c     (multiple is the SECOND summand)
//
// — both factor orders of the multiple covered — given a discharged
// `nNeq0 : ⊢ ¬(den = 0)`. The result inherits nNeq0's hyps: a hyp-free nNeq0
// (literal divisor) yields a rewrite-grade equality; a hyp-carrying nNeq0
// (symbolic divisor, n≠0 from hyps) yields an enrichment fact.
//
// The bound DivMultAdd is the 4-clause conjunction of `(den=0) ∨ eq`
// disjunctions; this builds the exact target clause it needs and projectDisjClause
// finds it among the conjuncts by shape (independent of clause ordering and of
// how the served normal form binds the clauses' variables), kills the
// `(den=0)` disjunct with nNeq0, and orients to the reducing direction. nil when
// no summand is a multiple of den, the matching clause is absent, DivMultAdd is
// unbundled, or nNeq0 is nil. Self-validating: a clause that does not match the
// built target is skipped, so a shape drift degrades to nil rather than a wrong
// rewrite.
func divMultAddEq(num, den Term, nNeq0 *prop.PropWrapper) *prop.PropWrapper {
	thm := divMultAddThm()
	if thm == nil || nNeq0 == nil {
		return nil
	}
	x, y, ok := MatchesPlus(num)
	if !ok {
		return nil
	}
	// resultLHS is the reduced RHS (nat_div(num,den) = resultLHS); the matching
	// clause — whichever factor order it states the multiple in — is found
	// by shape.
	var resultLHS Term
	switch {
	case isMultipleOf(x, den): // num = (coeff·den | den·coeff) + r
		resultLHS = plus(otherFactor(x, den), divT(y, den))
	case isMultipleOf(y, den): // num = r + (coeff·den | den·coeff)
		resultLHS = plus(divT(x, den), otherFactor(y, den))
	default:
		return nil
	}
	// Each DivMultAdd clause is `(den=0) ∨ (resultLHS = nat_div(num,den))`;
	// projectDisjClause finds the matching one among the four, discharges den≠0,
	// and orients to the reducing direction ⊢ nat_div(num,den) = resultLHS.
	return projectDisjClause(thm, nNeq0, den, divT(num, den), resultLHS)
}

// divMultAdd is the literal-divisor SIMP rewrite — `nat_div((c·n)+r, n) → c + nat_div(r,n)`
// — discharging `n≠0` numerically (proveNeqZero's literal route; no hyps in the
// simp pass, exactly divCommonFactor's pattern). Hyp-free, so it is a valid
// prop.Rewrite leaf. nil for a symbolic divisor — that case is divMultAddFact's.
func divMultAdd(num, den Term) *prop.PropWrapper {
	return divMultAddEq(num, den, proveNeqZero(den, nil))
}

// divMultAddFact is the symbolic-divisor ENRICHMENT companion to divMultAdd:
// discharge `n≠0` from the goal's hyps (proveNeqZero's symbolic / ¬(n=0)-hyp
// routes) and return `{hyps'} ⊢ nat_div((c·n)+r, n) = c + nat_div(r,n)` as a fact for
// divModFacts to inject — relating the two opaque nat_div atoms for the linear core
// (it does NOT term-simplify the goal, unlike the literal simp). nil when n≠0 does
// not discharge, num is not an affine multiple of den, or DivMultAdd is
// unbundled. The literal case is already cleared by the simp pass, so this fires
// in practice only for a symbolic divisor.
func divMultAddFact(num, den Term, hyps []Term) *prop.PropWrapper {
	return divMultAddEq(num, den, proveNeqZero(den, hyps))
}

// modAddMod rewrites nat_mod(nat_mod(a,n) + nat_mod(b,n), n) → nat_mod(a+b, n) — the COMBINE
// (term-shrinking) direction of ModAddMod. The bound form states ModAddMod in
// the DISTRIBUTE direction `nat_mod(a+b,n) = nat_mod(nat_mod(a,n)+nat_mod(b,n),n)`, which as an
// auto-simp would GROW the term and loop; eqLeaf auto-orients to the reducing
// direction. nil when the dividend is not a sum of two same-divisor MODs, or
// ModAddMod is unbundled.
func modAddMod(dividend, n Term) *prop.PropWrapper {
	if modAddModThm() == nil {
		return nil
	}
	l, r, ok := MatchesPlus(dividend)
	if !ok {
		return nil
	}
	a, na, ok := MatchesMod(l)
	if !ok || !na.AlphaEquals(n) {
		return nil
	}
	b, nb, ok := MatchesMod(r)
	if !ok || !nb.AlphaEquals(n) {
		return nil
	}
	return eqLeaf(modAddModThm(), []Term{a, b, n},
		modT(plus(modT(a, n), modT(b, n)), n), modT(plus(a, b), n))
}

// otherFactor returns the factor of a product `prod` that is not den (the other
// operand of `f1·f2` when one equals den). Caller must have established
// isMultipleOf(prod, den); nil if prod is not a product.
func otherFactor(prod, den Term) Term {
	f1, f2, ok := MatchesStar(prod)
	if !ok {
		return nil
	}
	if f1.AlphaEquals(den) {
		return f2
	}
	return f1
}

// nat_div/nat_mod enrichment for a multiple and for a nested residue — two
// bounded-atom facts the linear core cannot derive from the Division/ModLessThan
// injection (both would need a NONLINEAR step: a `q·n = 0` cancellation
// linarith can't see):
//
//   - MULTIPLE-IS-ZERO: a nat_mod atom whose dividend is a syntactic multiple of the
//     divisor pins to 0. DERIVED from the already-bound ModEqZero (no new lemma):
//     `∃q. (k·n) = q·n` (witness k) ⇒ `0 = (k·n) nat_mod n`.
//   - IDEMPOTENCE: a nested `nat_mod(nat_mod(m,n), n)` pins to its inner `nat_mod(m,n)`. Via
//     ModModRefl (`∀m n. nat_mod(m,n) = nat_mod(nat_mod(m,n),n)`).
//
// Both return nil when their shape does not match or their lemma is unbundled,
// so divModFacts injects them only when applicable — same per-atom, gated,
// graceful-degradation discipline as the rest of the nat_div/nat_mod enrichment.

// modMultZero returns `⊢ nat_mod(X, n) = 0` when the dividend X is a syntactic
// product with n as one factor (X = k·n or X = n·k). nil otherwise, or when
// ModEqZero is unbundled. The witness ∃q. X = q·n is built by dividesIntro (the
// MulSym bridge handles the n·k orientation), then ModEqZero turns it into
// `0 = nat_mod(X, n)`.
func modMultZero(x, n Term) *prop.PropWrapper {
	if modEqZeroThm() == nil {
		return nil
	}
	f1, f2, ok := MatchesStar(x)
	if !ok {
		return nil
	}
	var k, eqXnk = Term(nil), (*prop.PropWrapper)(nil)
	switch {
	case f2.AlphaEquals(n): // X = k·n  ⇒  X = n·k via commuteMUL(k, n)
		k, eqXnk = f1, commuteMUL(f1, n)
	case f1.AlphaEquals(n): // X = n·k  ⇒  X = n·k by reflexivity
		k, eqXnk = f2, prop.Refl(x)
	default:
		return nil // n is not a factor of the dividend.
	}
	divEx := mp(dividesIntro(n, x, k), eqXnk)    // ⊢ ∃q. X = q·n
	iff := instAll(modEqZeroThm(), []Term{x, n}) // ⊢ (∃q. X=q·n) ⇔ (0 = nat_mod(X,n))
	return iff.EqMP(divEx).EqSym()               // ⊢ nat_mod(X, n) = 0
}

// modIdemp returns `⊢ nat_mod(nat_mod(m,n), n) = nat_mod(m,n)` (idempotence) when the nat_mod
// atom's dividend is itself a nat_mod with the SAME divisor n. nil otherwise, or when
// ModModRefl is unbundled. eqLeaf auto-orients the bound form's reversed statement.
func modIdemp(dividend, n Term) *prop.PropWrapper {
	if modModReflThm() == nil {
		return nil
	}
	p, n2, ok := MatchesMod(dividend)
	if !ok || !n2.AlphaEquals(n) {
		return nil // dividend is not nat_mod(_, n) — not a nested same-divisor nat_mod.
	}
	return eqLeaf(modModReflThm(), []Term{p, n}, modT(modT(p, n), n), modT(p, n))
}

// Named-theorem leaves for the nat_div/nat_mod layer. Same discipline as
// the rest of omega: each reads its theorem from the installed NatLemmaBundle
// (instantiated and oriented by eqLeaf/implyLeaf) and falls back to a placeholder
// stand-in (bundle.go, test-only) when the field is nil.

// ── Unconditional bounded-atom hyps (injected by divModFacts) ─────────────────

// divLessEq: ⊢ nat_div(m, n) ≤ m   (real: DivLessEq, unconditional).
func divLessEq(m, n Term) *prop.PropWrapper {
	return implyLeaf(divLessEqThm(), []Term{m, n}, le(divT(m, n), m))
}

// modLessEq: ⊢ nat_mod(m, n) ≤ m   (real: ModLessEq, unconditional).
func modLessEq(m, n Term) *prop.PropWrapper {
	return implyLeaf(modLessEqThm(), []Term{m, n}, le(modT(m, n), m))
}

// divMulLessEq: ⊢ n * nat_div(m, n) ≤ m   (real: DivMulLessEq, unconditional — the floor
// LOWER bound). Bound binder order is (n, m): `∀n m. (n * nat_div(m,n)) ≤ m`.
func divMulLessEq(m, n Term) *prop.PropWrapper {
	return implyLeaf(divMulLessEqThm(), []Term{n, m}, le(star(n, divT(m, n)), m))
}

// ── Unconditional simp rewrites ───────────────────────────────────────────────

// modRefl: ⊢ nat_mod(n, n) = 0   (real: ModRefl, unconditional).
func modRefl(n Term) *prop.PropWrapper {
	return eqLeaf(modReflThm(), []Term{n}, modT(n, n), natZero)
}

// divZero: ⊢ nat_div(m, 0) = 0   (real: DivZero, unconditional).
func divZero(m Term) *prop.PropWrapper {
	return eqLeaf(divZeroThm(), []Term{m}, divT(m, natZero), natZero)
}

// modZero: ⊢ nat_mod(m, 0) = m   (real: ModZero, unconditional).
func modZero(m Term) *prop.PropWrapper {
	return eqLeaf(modZeroThm(), []Term{m}, modT(m, natZero), m)
}

// ── Conditional lemmas (need a discharged side condition) ─────────────────────

// modLessThanImp: ⊢ (m < n) ⇒ (m = nat_mod(m, n))   (real: ModLessThan, IMPLICATION form via
// PromiseForGeneral; its normal form is the `¬(m<n) ∨ (m = nat_mod(m,n))` clause).
func modLessThanImp(m, n Term) *prop.PropWrapper {
	return implyLeaf(modLessThanThm(), []Term{m, n}, imply(lt(m, n), eqT(m, modT(m, n))))
}
