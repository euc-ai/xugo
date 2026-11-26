package omega

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Integer case-split engine — the `int`-type twin of the num case split
// (nat_sub.go), bootstrapped against its first client `int_abs`.
//
// `int_abs x = COND(&0 ≤ x, x, −x)` is piecewise-linear by the guard `&0 ≤ x`,
// exactly the shape a proof-producing excluded middle elimination reduces to a
// closed `+`-form per branch — and the `−x` branch then flows through the int
// signed normalizer (subneg.go) into the positive-linear decider. So the
// engine is the int analogue of the num nat_max/nat_min handler: split on the guard,
// pin int_abs to its branch value, recurse into the int forward prover.
//
// The reusable pieces (splittableAtom / splitBranch / enrichAndCut /
// collectRawSubterms / prop.ByCases / prop.ExcludedMiddle) are SHARED with the
// num engine; only the recognizer (int_abs), the int comparison vocabulary
// (intNegComparison), and the COND collapser (intCondPin, over the int decider)
// are int-specific. As with the rest of the int layer the int_abs DEF leaf is
// placeholder-backed (int_lemmas.go intAbsBySign) — the composition around it is
// real kernel work, sound once serve.InstallIntBundle binds AbsBySign.

// intProveSplit is the int case split (intFirstSplittable) with the given
// provers — caseSplit (engine.go) holds the recursion: prove at every branch,
// a further split, and leaf where nothing is left to split.
func intProveSplit(prove, leaf proveFn, hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	return caseSplit{domain: intDomain, first: intFirstSplittable, prove: prove, leaf: leaf}.split(hyps, goal, done)
}

// intProveLeaf is the int split's leaf prover: the handlers of the decide
// chain that read the hypotheses and prove without re-entering it — the
// sign-known nonlinear fragment, the cancellation and the products pass. A
// branch's pin `s = &1` reaches `s·s = &1` here; the linear prover alone
// reads s·s as an unknown.
func intProveLeaf(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	hs := slices.Collect(hyps)
	for _, handler := range []func([]Term, Term) (*prop.PropWrapper, bool){
		intProveMonotone, intProvePowSign, intProveAbsTriangle, intProveStrictSquare,
		intProveMulEqZeroSquare, intProveCancelMul, intProveProducts,
	} {
		if w, ok := handler(hs, goal); ok {
			return w, true
		}
	}
	return nil, false
}

// intFirstSplittable returns the first int splittable atom of hyps∪{goal} not
// already split (in `done`), mirroring the num firstSplittable's two families:
//
//   - HYPOTHESIS-based (intHypSplittable): a disjunction `p∨q`, an int `≠`, or an
//     int implication `p⇒q` HYPOTHESIS — boolean/relational structure the linear
//     core drops. Sound only because the term IS a hyp, so restricted to the
//     top-level hyps.
//   - TAUTOLOGY-based (intSplittableKinds): an opaque operator (int_abs / int_max
//     / int_min / int_sgn / raw int COND) anywhere BINDER-FREE in hyps∪{goal},
//     split on an unconditionally-true disjunction (excluded middle). Sound
//     regardless of position; an occurrence under a ∀/∃/λ is skipped as a
//     candidate (collectBinderFreeSubterms) because its pin mentions the bound
//     variable and meets no constraint row — the same reason
//     intComparisonAtomsOf collects binder-free.
func intFirstSplittable(hyps []Term, goal Term, done []Term) (splittableAtom, bool) {
	for _, h := range hyps {
		if slices.ContainsFunc(done, h.AlphaEquals) {
			continue
		}
		if sa, ok := intHypSplittable(h); ok {
			return sa, true
		}
	}
	for _, t := range collectBinderFreeSubterms(append(slices.Clone(hyps), goal), isIntSplitCandidate) {
		if slices.ContainsFunc(done, t.AlphaEquals) {
			continue
		}
		for _, kind := range intSplittableKinds() {
			if sa, ok := kind(t); ok {
				return sa, true
			}
		}
	}
	return splittableAtom{}, false
}

// intSplittableKinds: the tautology-split recognizers, each returning ok=false
// when not its kind or its def is unbundled. A function (not a var) to avoid a
// static-init cycle (the kinds reach intProveSplit, which reads this list).
func intSplittableKinds() []func(Term) (splittableAtom, bool) {
	return []func(Term) (splittableAtom, bool){
		intAbsSplittable, intMaxSplittable, intMinSplittable, intSgnSplittable, intCondSplittable,
	}
}

// isIntSplitCandidate reports whether t is an opaque int operator some tautology
// kind might split (the cheap pre-filter for collectRawSubterms).
func isIntSplitCandidate(t Term) bool {
	if _, ok := MatchesIntAbs(t); ok {
		return true
	}
	if _, _, ok := MatchesIntMax(t); ok {
		return true
	}
	if _, _, ok := MatchesIntMin(t); ok {
		return true
	}
	if _, ok := MatchesIntSgn(t); ok {
		return true
	}
	// A raw int-typed COND `COND(guard, x, y) : int` whose guard the linear core
	// can't decide (intCondSplittable does the guard-shape filtering).
	if _, _, _, ok := ext.MatchesCond(t); ok && isIntTerm(t) {
		return true
	}
	return false
}

// intAbsSplittable is the int_abs kind: split `int_abs x` on excluded middle of
// its def guard `&0 ≤ x`, pinning int_abs x to x (resp. −x) per branch via the
// AbsBySign def. Graceful no-op only if the COND fails to fold (intCondSplit) —
// the def itself is placeholder-backed, so it is always present in tests.
func intAbsSplittable(m Term) (splittableAtom, bool) {
	x, ok := MatchesIntAbs(m)
	if !ok {
		return splittableAtom{}, false
	}
	return intCondSplit(m, intAbsBySign(x), intLeT(intLit(0), x))
}

// intMaxSplittable / intMinSplittable are the int_max/int_min kinds: split on the
// def guard `a ≤ b`, pinning the operator to b/a (resp. a/b). The int twins of
// the num maxSplittable/minSplittable.
func intMaxSplittable(m Term) (splittableAtom, bool) {
	a, b, ok := MatchesIntMax(m)
	if !ok {
		return splittableAtom{}, false
	}
	return intCondSplit(m, intMaxDef(a, b), intLeT(a, b))
}

func intMinSplittable(m Term) (splittableAtom, bool) {
	a, b, ok := MatchesIntMin(m)
	if !ok {
		return splittableAtom{}, false
	}
	return intCondSplit(m, intMinDef(a, b), intLeT(a, b))
}

// intSgnSplittable is the int_sgn kind: split the OUTER guard `&0 < x` of the
// nested def; the else-branch pins int_sgn x to the inner COND `COND(x<&0,−&1,&0)`,
// which the raw-COND kind (intCondSplittable) then splits in the recursion.
func intSgnSplittable(m Term) (splittableAtom, bool) {
	x, ok := MatchesIntSgn(m)
	if !ok {
		return splittableAtom{}, false
	}
	return intCondSplit(m, intSgnDef(x), intLtT(intLit(0), x))
}

// intCondSplittable is the raw-COND kind: an int-typed `COND(guard, x, y)` whose
// guard is a `<`/`≤` comparison the linear core can't decide is split on
// excluded middle of the guard, each arm pinned by the reflexive def. Catches a
// bare int conditional and the inner COND of int_sgn. The int twin of the num
// condSplittable; a guard of any other shape is split by its atoms
// (compoundCondSplit).
func intCondSplittable(c Term) (splittableAtom, bool) {
	guard, _, _, ok := ext.MatchesCond(c)
	if !ok || !isIntTerm(c) {
		return splittableAtom{}, false
	}
	if intDomain.isOrderAtom(guard) {
		return intCondSplit(c, prop.Refl(c), guard)
	}
	return compoundCondSplit(c, prop.Refl(c), guard, intNegComparison)
}

// ── Hypothesis-based splits (int_split.go's hypSplittable twin) ───────────────

// intHypSplittable recognizes a HYPOTHESIS whose structure the linear core cannot
// use directly but a case split can: a disjunction `p∨q`, an int `≠`, or an int
// implication `p⇒q`. The split is sound because h is a real hyp. Returns ok=false
// for any other shape. Mirror of the num hypSplittable.
func intHypSplittable(h Term) (splittableAtom, bool) {
	// Disjunctive hyp `p ∨ q`: split, feeding each disjunct. No lemma — the
	// disjunction proof is the hyp itself.
	if p, q, ok := prop.MatchesOR(h); ok {
		return splittableAtom{
			atom:      h,
			disjProof: prop.Assume(h), // {p∨q} ⊢ p∨q
			branches: [2]splitBranch{
				{guard: p, facts: []*prop.PropWrapper{prop.Assume(p)}},
				{guard: q, facts: []*prop.PropWrapper{prop.Assume(q)}},
			},
		}, true
	}
	// int `≠` hyp `¬(a=b)`: a<b ∨ b<a (LessThanTrichotomy with the `a=b` disjunct killed
	// under the hyp). The complementary comparisons feed the linear core.
	if inner := ext.MatchesNOT(h); inner != nil {
		if a, b, ok := ext.MatchesEQ(inner); ok && isIntTerm(a) {
			tri := intTrichotomyNeq(a, b)
			if tri == nil {
				return splittableAtom{}, false // LessThanTrichotomy unbundled — decline.
			}
			return splittableAtom{
				atom:      h,
				disjProof: tri, // {¬(a=b)} ⊢ (a<b) ∨ (b<a)
				branches: [2]splitBranch{
					{guard: intLtT(a, b), facts: []*prop.PropWrapper{prop.Assume(intLtT(a, b))}},
					{guard: intLtT(b, a), facts: []*prop.PropWrapper{prop.Assume(intLtT(b, a))}},
				},
			}, true
		}
	}
	// Implication hyp `p ⇒ q` (classically ¬p ∨ q): the ¬p branch bridges to the
	// complementary positive comparison (NotLessThan/NotLessEq) when p is a `<`/`≤` atom.
	if p, q, ok := prop.MatchesIMPLY(h); ok {
		np := not(p)
		b0 := []*prop.PropWrapper{prop.Assume(np)}
		if _, bridge, ok := intNegComparison(p); ok {
			b0 = append(b0, bridge) // {¬p} ⊢ the linear-usable complementary comparison
		}
		return splittableAtom{
			atom:      h,
			disjProof: prop.BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](p, q).EqMP(prop.Assume(h)), // {p⇒q} ⊢ ¬p ∨ q
			branches: [2]splitBranch{
				{guard: np, facts: b0},
				{guard: q, facts: []*prop.PropWrapper{prop.Assume(q)}},
			},
		}, true
	}
	// int product `a·b = &0` hyp with DISTINCT factors: a=&0 ∨ b=&0 (MulEqZero —
	// ℤ has no zero divisors). Each disjunct pins a factor, closing e.g.
	// `x·y=&0,x≠&0 ⊢ y=&0`. The square case a==b (`x·x=&0`) collapses to a single
	// guard `x=&0`, a fact and no case, so it is handled forward instead
	// (intProveMulEqZeroSquare).
	if a, b, ok := intProductZeroEq(h); ok && !a.AlphaEquals(b) {
		za, zb := eqT(a, intLit(0)), eqT(b, intLit(0))
		return splittableAtom{
			atom:      h,
			disjProof: intMulEqZeroDisj(h, a, b), // {a·b=&0} ⊢ (a=&0) ∨ (b=&0)
			branches: [2]splitBranch{
				{guard: za, facts: []*prop.PropWrapper{prop.Assume(za)}},
				{guard: zb, facts: []*prop.PropWrapper{prop.Assume(zb)}},
			},
		}, true
	}
	return splittableAtom{}, false
}

// intProductZeroEq matches a hyp `a·b = &0` / `&0 = a·b` (a genuine int product
// equal to zero), returning its two factors — the MulEqZero-splittable shape.
func intProductZeroEq(h Term) (a, b Term, ok bool) {
	l, r, eok := ext.MatchesEQ(h)
	if !eok || !isIntTerm(l) {
		return nil, nil, false
	}
	if isIntZero(r) {
		if x, y, mok := intDomain.matchStar(l); mok {
			return x, y, true
		}
	}
	if isIntZero(l) {
		if x, y, mok := intDomain.matchStar(r); mok {
			return x, y, true
		}
	}
	return nil, nil, false
}

// intMulEqZeroDisj derives `{h} ⊢ (a=&0) ∨ (b=&0)` from MulEqZero
// (`(a·b=&0) ⇔ (a=&0 ∨ b=&0)`), where h is the product-zero hyp in either
// orientation (the `&0 = a·b` form is flipped first).
func intMulEqZeroDisj(h, a, b Term) *prop.PropWrapper {
	prodEq0 := eqT(intStarT(a, b), intLit(0)) // a·b = &0 (MulEqZero's LHS orientation)
	hProof := prop.Assume(h)                  // {h} ⊢ h
	if !h.AlphaEquals(prodEq0) {
		hProof = hProof.EqSym() // h is `&0 = a·b` → {h} ⊢ a·b = &0
	}
	iff := intEqLeaf(intMulEqZeroThm(), []Term{a, b}, prodEq0,
		or(eqT(a, intLit(0)), eqT(b, intLit(0)))) // ⊢ (a·b=&0) ⇔ (a=&0 ∨ b=&0)
	return iff.EqMP(hProof) // {h} ⊢ (a=&0) ∨ (b=&0)
}

// intTrichotomyNeq derives `{¬(a=b)} ⊢ (a<b) ∨ (b<a)` from LessThanTrichotomy
// (`((a<b) ∨ (b<a)) ∨ (a=b)`): disjSyllogism removes the `a=b` disjunct (on the
// RIGHT) under the `¬(a=b)` hyp. Mirror of trichotomyNeq.
func intTrichotomyNeq(a, b Term) *prop.PropWrapper {
	ltc := intLessThanTrichotomy(a, b) // ⊢ ((a<b) ∨ (b<a)) ∨ (a=b)
	return disjSyllogism(ltc, prop.Assume(not(eqT(a, b))))
}

// intCondSplit builds the excluded middle split of an int atom whose value is
// piecewise by a comparison `guard`, given `def : ⊢ atom = COND(guard, x, y)`
// (the int twin of condSplit):
//
//	guard ∨ ¬guard                          [excluded middle]
//	guard  branch:  pin atom = x            [COND collapses under guard]
//	¬guard branch:  pin atom = y            [COND collapses under ¬guard's positive form]
//
// The ¬guard branch bridges to the complementary positive comparison
// (intNegComparison via NotLessThan / NotLessEq) so the int prover can both
// consume it and let the COND fold. ok=false when the guard is not a `<`/`≤`
// comparison or a pin fails to fold.
func intCondSplit(atom Term, def *prop.PropWrapper, guard Term) (splittableAtom, bool) {
	negPos, negBridge, ok := intNegComparison(guard)
	if !ok {
		return splittableAtom{}, false // guard not a `<`/`≤` comparison.
	}
	pinT := intCondPin(def, guard)     // {guard} ⊢ atom = x
	pinFraw := intCondPin(def, negPos) // {negPos} ⊢ atom = y
	if pinT == nil || pinFraw == nil {
		return splittableAtom{}, false
	}
	pinF := prop.WrapProp(negBridge.MaybeDeriveTrans(pinFraw)) // {¬guard} ⊢ atom = y
	return splittableAtom{
		atom:      atom,
		disjProof: prop.ExcludedMiddle(guard), // guard ∨ ¬guard
		branches: [2]splitBranch{
			{guard: guard, facts: []*prop.PropWrapper{prop.Assume(guard), pinT}},
			{guard: not(guard), facts: []*prop.PropWrapper{negBridge, pinF}},
		},
	}, true
}

// intNegComparison maps a `<`/`≤` int comparison `guard` to its complementary
// positive comparison `negPos` plus the bridge `{¬guard} ⊢ negPos` (NotLessThan /
// NotLessEq), the int twin of negComparison:
//
//	u < v  →  v ≤ u   (NotLessThan: ¬(u<v) ⇔ v≤u)
//	u ≤ v  →  v < u   (NotLessEq: ¬(u≤v) ⇔ v<u)
//
// ok=false for any other shape; a COND on such a guard is split by the
// guard's atoms (compoundCondSplit).
func intNegComparison(guard Term) (negPos Term, bridge *prop.PropWrapper, ok bool) {
	if u, v, m := intDomain.matchLt(guard); m {
		return intLeT(v, u), intNotLT(u, v).LeftAssume(), true // {¬(u<v)} ⊢ v≤u
	}
	if u, v, m := intDomain.matchLe(guard); m {
		return intLtT(v, u), intNotLE(u, v).LeftAssume(), true // {¬(u≤v)} ⊢ v<u
	}
	return nil, nil, false
}

// intCondPin collapses the COND on the RHS of `def` under the branch guard,
// returning `{guardHyp} ⊢ (def.lhs) = <branch value>` (the int twin of condPin).
// IntArithDecideWithHyps([guardHyp]) decides the COND's guard from guardHyp and
// folds it — so the result carries {guardHyp} and pins the int_abs atom to its
// actual value. nil when the guard does not fold the COND.
func intCondPin(def *prop.PropWrapper, guardHyp Term) *prop.PropWrapper {
	// Raw (no pre-simp): guardHyp is a branch-pin whose AlphaEquals identity
	// downstream paths rely on — see intArithDecideWithHypsRaw.
	simp := intArithDecideWithHypsRaw([]Term{guardHyp})(prop.Rhs(def))
	if simp == nil {
		return nil
	}
	return def.EqTrans(simp)
}

// Formula-level linear decider over the `int` type — the twin of the num/real
// arithBoolLeaf. A goal whose validity is genuinely *propositional
// over several contingent int comparison atoms* — `(a≤b ⇒ a≤c) ∨ (c<b)`, the
// 3-way trichotomy `(x<y) ∨ (x=y) ∨ (y<x)` — has no atom that decides alone and
// no binary disjunct that follows, so the atom decider declines. intArithBoolLeaf
// closes it by interleaved case analysis on the comparison atoms (collapse the
// formula under each new atom-hypothesis FIRST, so it shrinks before the next
// split — the same lazy DPLL-style pruning the num/real twins use).
//
// Everything structural (splittableAtom / splitBranch / enrichAndCut / ByCases /
// ExcludedMiddle / collectRawSubterms) is shared; only the atom-domain primitives
// are int-specific: the int comparison matchers, the int `¬A → complementary`
// bridge (intNegComparison, NotLessThan/NotLessEq), and the int forward decider
// (intProveDecAtom). The branch collapse is intArithCollapseRewrite (the decider
// MINUS this leaf), which bounds the split recursion.

// intArithBoolLeaf is the deep-rewrite leaf for a contingent boolean combination
// of int comparison atoms. Returns `⊢ G ⇔ ⊤` when the case analysis closes G,
// else nil. Placed LAST in IntArithDecideWithHyps' leaf list.
//
// The nil `done` is a FRESH split, which is correct only because this leaf is
// wired exclusively into top-level decider entries (IntArithDecideWithHyps /
// intArithDecideWithHypsRaw and the unified arithDecideWithHypsRaw) — never
// into the branch sub-deciders an ongoing split recurses through
// (intArithCollapseRewrite and intArithDecideWithHypsRawBranch both
// exclude it, see their docs). If this leaf ever becomes reachable from
// inside intProveBoolGoal's recursion, the caller's `done` must be
// threaded through here instead of nil — a nil-reset on that path does
// not terminate.
func intArithBoolLeaf(hyps []Term) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		if !isIntBooleanOverComparisons(t) {
			return nil
		}
		// NOTE — deliberately NO zero-hyp weakening pre-pass here (try `⊢ G`
		// before `{hyps} ⊢ G`). It is sound, and it makes valid-alone goals
		// cost exactly the zero-hyp decision — but it GROWS this leaf's
		// success set (it fires where the with-hyps search fails; hyps are
		// not monotone for the SEARCH even though they are for provability),
		// and any success-set growth diverges replay of steps recorded under
		// the old driver (observed on 3 corpus proofs).
		// Re-add only together with a corpus re-record wave.
		// splitByCases' proof-core pruning already bounds irrelevant-hyp cost
		// to a per-leaf linear pass, which is what kills the exponential.
		if w, ok := intProveBoolGoal(hyps, t, nil); ok {
			return eqtIntro(w) // ⊢ (G) ⇔ ⊤
		}
		return nil
	}
}

// isIntBooleanOverComparisons gates intArithBoolLeaf: t has an ∧/∨/⇒/⇔ head and
// mentions at least one BINDER-FREE int comparison atom (see
// intComparisonAtomsOf). Mirror of isBooleanOverComparisons.
func isIntBooleanOverComparisons(t Term) bool {
	isBool := false
	if _, _, ok := prop.MatchesAND(t); ok {
		isBool = true
	} else if _, _, ok := prop.MatchesOR(t); ok {
		isBool = true
	} else if _, _, ok := prop.MatchesIMPLY(t); ok {
		isBool = true
	} else if _, _, ok := ext.MatchesIFF(t); ok {
		isBool = true
	}
	return isBool && len(intComparisonAtomsOf(t)) > 0
}

// intProveBoolGoal closes `{hyps} ⊢ goal` by case-splitting on one int comparison
// atom and recombining via ByCases with proof-core pruning (mirror of
// proveBoolGoal; see splitByCases).
func intProveBoolGoal(hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	sa, ok := firstIntComparisonAtomSplit(goal, done)
	if !ok {
		return nil, false
	}
	done = append(slices.Clone(done), sa.atom)
	return splitByCases(sa, hyps, goal,
		func(h []Term) (*prop.PropWrapper, bool) { return intProveBoolBranch(h, goal, done) })
}

// intProveBoolBranch closes one split branch (mirror of proveBoolBranch):
// collapse the formula under the new hypothesis FIRST (intArithCollapseRewrite,
// bool leaf excluded), so it shrinks before any further split; ⊤ closes, ⊥ aborts
// (goal not valid in a feasible branch), a residual recurses, else the linear
// core decides directly or a further atom splits.
func intProveBoolBranch(hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	// A bool-split branch is INSIDE a case-split handler, so it takes the
	// branch discipline intProveDecAtomBranch documents — linear core, ring,
	// enrichments, structural splits, never a case-split handler. Concretely
	// the NoSignSplit decider on both legs below: the full decider's
	// intImageSplit (a 4-way sign split per int variable, its branches
	// carrying `x = ±&n` pins that every IntLinProve then pushes through the
	// signed normalizer's kernel derivations) and intProveBoundedEnum are
	// exactly what the engine's own int leaf excludes for cost, and a
	// hypothesis the engine's hyp loop decides under the OTHER hyps meets this
	// leaf with an empty context, where that search is hopeless and paid in
	// full. Measured, with the full decider here: the bool leaf on
	// `&0 < p ∧ p·a ≤ p·b` under {} costs about six times as much, under the
	// placeholder bundle and under the production bundles alike; the ℝ twin
	// pays under three times because ℝ has no sign split to enter.
	if w := intArithCollapseRewriteNoSignSplit(hyps)(goal); w != nil {
		v := prop.Rhs(w)
		switch {
		case v.AlphaEquals(prop.T):
			return iffTrueElim(w), true // ⊢ goal ⇔ ⊤  →  ⊢ goal
		case v.AlphaEquals(prop.F):
			return nil, false // goal false under a feasible branch → not valid
		default:
			pf, ok := intProveBoolBranch(hyps, v, done)
			if !ok {
				return nil, false
			}
			return prop.WrapProp(w.EqSym().EqMP(pf)), true // (V⇔goal) ∘ ⊢V → ⊢goal
		}
	}
	// No further collapse. The residual may be a bare int comparison the linear
	// core decides (after the splits pinned enough atoms), else split another atom.
	if pf, ok := intProveDecAtomNoSignSplit(slices.Values(hyps), goal); ok {
		return pf, true
	}
	return intProveBoolGoal(hyps, goal, done)
}

// firstIntComparisonAtomSplit returns the ExcludedMiddle split for the first
// not-yet-split int comparison atom of goal (mirror of firstComparisonAtomSplit).
func firstIntComparisonAtomSplit(goal Term, done []Term) (splittableAtom, bool) {
	for _, a := range intComparisonAtomsOf(goal) {
		if slices.ContainsFunc(done, a.AlphaEquals) {
			continue
		}
		return intComparisonAtomSplit(a), true
	}
	return splittableAtom{}, false
}

// intComparisonAtomSplit builds `⊢ A ∨ ¬A` for a normalized int comparison atom A
// (mirror of comparisonAtomSplit); the negative branch bridges ¬A to the
// complementary comparison via intNegComparison (NotLessThan/NotLessEq). For an `=` atom
// no bridge is needed — intProveNeg matches the `¬(a=b)` hyp directly.
func intComparisonAtomSplit(a Term) splittableAtom {
	posFacts := []*prop.PropWrapper{prop.Assume(a)}
	negFacts := []*prop.PropWrapper{prop.Assume(not(a))}
	if _, bridge, ok := intNegComparison(a); ok {
		negFacts = append(negFacts, bridge) // {¬A} ⊢ complementary comparison
	}
	return splittableAtom{
		atom:      a,
		disjProof: prop.ExcludedMiddle(a), // ⊢ A ∨ ¬A
		branches: [2]splitBranch{
			{guard: a, facts: posFacts},
			{guard: not(a), facts: negFacts},
		},
	}
}

// intComparisonAtomsOf collects the distinct positive int comparison atoms of t,
// normalizing `>`/`≥` to swapped `<`/`≤` (mirror of comparisonAtomsOf).
//
// BINDER-FREE only (collectBinderFreeSubterms, NOT the raw walk): an atom with
// a free occurrence of an enclosing ∀/∃/λ-bound variable is not a split
// candidate — EM-splitting on the capture-stripped atom can never decide the
// quantifier, so the split only spends branches, and can fail to
// terminate. This also gates isIntBooleanOverComparisons: a boolean head
// whose ONLY comparison atoms sit under binders does not trigger the
// bool-split leaf at all.
func intComparisonAtomsOf(t Term) []Term {
	raw := collectBinderFreeSubterms([]Term{t}, isIntPositiveCmpAtom)
	var out []Term
	for _, a := range raw {
		n := intNormalizeCmpAtom(a)
		if !slices.ContainsFunc(out, n.AlphaEquals) {
			out = append(out, n)
		}
	}
	return out
}

// isIntPositiveCmpAtom matches a positive int comparison atom `< ≤ = > ≥` (mirror
// of isPositiveCmpAtom).
func isIntPositiveCmpAtom(t Term) bool {
	if _, _, ok := intDomain.matchLt(t); ok {
		return true
	}
	if _, _, ok := intDomain.matchLe(t); ok {
		return true
	}
	if _, _, ok := intDomain.matchGt(t); ok {
		return true
	}
	if _, _, ok := intDomain.matchGe(t); ok {
		return true
	}
	if l, _, ok := ext.MatchesEQ(t); ok {
		return isIntTerm(l)
	}
	return false
}

// intNormalizeCmpAtom rewrites `a > b → b < a` and `a ≥ b → b ≤ a`, leaving
// `< ≤ =` untouched (mirror of normalizeCmpAtom).
func intNormalizeCmpAtom(a Term) Term {
	if x, y, ok := intDomain.matchGt(a); ok {
		return intLtT(y, x)
	}
	if x, y, ok := intDomain.matchGe(a); ok {
		return intLeT(y, x)
	}
	return a
}
