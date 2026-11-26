package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// subCancel rewrites `a - b → d` when a ≥ b, where d = la − lb is the genuine
// difference (representable over num, i.e. componentwise non-negative). The proof
// is a single ring identity + one bundle lemma, no case split:
//
//	a − b = (b + d) − b     [ring: a = b + d, congruenced under (_ − b)]
//	      = d               [AddSubLeftCancel: (m+n) − m = n]
//
// Because d : num (hence d ≥ 0), the ring identity `a = b + d` IS the a ≥ b
// witness — the truncation obligation is discharged structurally. The ring
// identity is built by addWitnessRingId (by-construction from linSub's spec —
// skips ringProveFull's normalize+compare), so a wrong d degrades to nil (no
// rewrite). Subsumes the syntactic `n−0 → n`, `n−n → 0`, and compositional
// `n+m−n → m`, `(n+m+k)−n → m+k`.
func subCancel(a, b Term) *prop.PropWrapper {
	d, ok := linSub(mpolyOf(a), mpolyOf(b))
	if !ok {
		return nil // a < b somewhere (truncating or mixed) — not a cancellation.
	}
	dTerm := d.toTerm()
	e1, ok := addWitnessRingId(a, b, d, dTerm) // ⊢ a = b + d
	if !ok {
		return nil
	}
	// a − b = (b+d) − b   [congruence on e1 under (_ − b)] ; then AddSubLeftCancel.
	return e1.LeftApply(natMinus).RightApply(b).EqTrans(addSubLeftCancel(b, dTerm))
}

// subTrunc rewrites `a - b → 0` when a ≤ b (the monus truncates). e = lb − la is
// the representable slack, so `b = a + e` (ring) gives `a ≤ b` (LessEqAdd), and
// SubEqZero turns that into `0 = a − b`:
//
//	a ≤ a + e = b           [LessEqAdd + ring witness b = a + e]
//	0 = a − b               [SubEqZero EqMP the a ≤ b]
//
// Needs SubEqZero + LessEqAdd; nil-checks SubEqZero (pending) so it is a no-op until
// supplied. Subsumes `0 − n → 0` and `n − (n+m) → 0`. The ring witness uses
// addWitnessRingId (by-construction; skips ringProveFull) — same mechanism as
// subCancel's, just oriented the other way.
func subTrunc(a, b Term) *prop.PropWrapper {
	if subEqZeroThm() == nil || lessEqAddThm() == nil {
		return nil // pending SubEqZero / LessEqAdd supply — degrade to no rewrite.
	}
	e, ok := linSub(mpolyOf(b), mpolyOf(a))
	if !ok {
		return nil // a > b somewhere — not a pure truncation.
	}
	eTerm := e.toTerm()
	w, ok := addWitnessRingId(b, a, e, eTerm) // ⊢ b = a + e
	if !ok {
		return nil
	}
	// a ≤ b : rewrite the `a + e` in LessEqAdd's `a ≤ a + e` to b via w⁻¹.
	leAB := w.EqSym().LeftApply(applyLe(a)).EqMP(lessEqAdd(a, eTerm)) // ⊢ a ≤ b
	return subEqZero(a, b).EqMP(leAB).EqSym()                         // ⊢ a − b = 0
}

// addWitnessRingId builds `⊢ left = right + rightDeltaTerm` directly from cut
// data, given `rightDelta = linSub(mpolyOf(left), mpolyOf(right))` succeeded.
// Shared by subCancel (left=a, right=b, rightDelta=d) and subTrunc (left=b,
// right=a, rightDelta=e). Same shape as the rank-1 cut's roundedCutIdL: skips
// RingProveFull's normalize-and-compare by exploiting linSub's contract —
//
//	linSub(lLeft, lRight) = rightDelta  ⇒  linAdd(lRight, rightDelta) ≡ lLeft
//
// at the linForm level (componentwise). So the identity is by construction;
// only the hyp-side normalize-and-merge is unavoidable work. Uses normalizeFull
// (mpolyOf's proof twin) so the inputs and the linForm arithmetic agree on
// nonlinear expansion (linOf's atomization would diverge from mpolyOf on
// `(m+n)·p`-shaped terms, breaking the contract above).
func addWitnessRingId(left, right Term, rightDelta linForm, rightDeltaTerm Term) (*prop.PropWrapper, bool) {
	lLeft, wLeft := natRing.normalizeFull(left)    // ⊢ left  = toTerm(lLeft)
	lRight, wRight := natRing.normalizeFull(right) // ⊢ right = toTerm(lRight)
	// Sanity-net for linSub's contract: a violation would surface as a wrong
	// claim, not a wrong proof — the kernel would refuse the EqTrans. Bail
	// before constructing rather than after.
	if !natDomain.buildTerm(linAdd(lRight, rightDelta)).AlphaEquals(natDomain.buildTerm(lLeft)) {
		return nil, false
	}
	// right + rightDeltaTerm = toTerm(lRight) + toTerm(rightDelta)
	//                        = toTerm(linAdd(lRight, rightDelta))
	//                        ≡ toTerm(lLeft)   (by construction above)
	rhs := wRight.LeftApply(natPlus).RightApply(rightDeltaTerm).
		EqTrans(natRing.mergeProof(lRight, rightDelta))
	return wLeft.EqTrans(rhs.EqSym()), true
}

// applyLe partially applies `≤` to its left argument: `(a ≤ ·)`. Used to lift an
// equation `x = y` to the congruence `(a ≤ x) ⇔ (a ≤ y)` via LeftApply.
func applyLe(a Term) Term { return ext.Apply(natLe, a) }

// ── Decision: the LessEqTotal case-split engine (the gray-shadow bootstrap) ──────
//
// A `splittableAtom` is an opaque-to-linarith subterm (monus, nat_max, nat_min, …) that a
// single proof-producing disjunction elimination reduces to a closed `+`-form per
// branch. The engine `proveSplit` is shared; each operator supplies its
// `splittableAtom` via a kind constructor. This is the reusable case-split
// machinery — the gray-shadow proof-structure bootstrap — with monus as its first
// client and nat_max/nat_min as the second.

// splittableKinds: each recognizes its operator on a candidate subterm and
// returns the split (ok=false when not its kind, when the atom is reducible by
// the simp pass, or when its bundle supply is incomplete). A function (not a
// package var) to avoid a static initialization cycle — the kinds transitively
// reach proveSplit, which reads this list.
func splittableKinds() []func(Term) (splittableAtom, bool) {
	return []func(Term) (splittableAtom, bool){
		monusSplittable, maxSplittable, minSplittable, condSplittable,
	}
}

// firstSplittable returns the first splittable atom of hyps∪{goal} not already
// split (in `done`). Two families, hypothesis-based first:
//
//   - HYPOTHESIS-based (hypSplittable): a disjunction `p ∨ q` or a num
//     disequality `a ≠ b` HYPOTHESIS — boolean/relational structure the linear
//     core drops (parseHypConstraint only ingests `< ≤ = > ≥`). Sound ONLY
//     because the term IS a hyp, so restricted to the top-level hyps — never a
//     goal subterm (a goal-side `∨` is not known true), never buried.
//   - TAUTOLOGY-based (splittableKinds): an opaque atom (monus/nat_max/nat_min/COND)
//     ANYWHERE in hyps∪{goal}, split on an unconditionally-true disjunction
//     (LessEqTotal / excluded middle). Sound regardless of position.
func firstSplittable(hyps []Term, goal Term, done []Term) (splittableAtom, bool) {
	for _, h := range hyps {
		if slices.ContainsFunc(done, h.AlphaEquals) {
			continue
		}
		if sa, ok := hypSplittable(h); ok {
			return sa, true
		}
	}
	for _, t := range collectSplitCandidates(append(slices.Clone(hyps), goal)) {
		if slices.ContainsFunc(done, t.AlphaEquals) {
			continue
		}
		for _, kind := range splittableKinds() {
			if sa, ok := kind(t); ok {
				return sa, true
			}
		}
	}
	return splittableAtom{}, false
}

// hypSplittable recognizes a HYPOTHESIS whose structure the linear core cannot
// use directly but a case split can. The split is sound because h is a real hyp:
// the disjunction proof either IS the hyp (Assume(h), for `p ∨ q`) or is derived
// with h as its only hyp (trichotomyNeq, for `≠`; MulEqZero, for a zero
// product). Returns ok=false for any
// other shape — the tautology kinds (splittableKinds) handle opaque atoms.
func hypSplittable(h Term) (splittableAtom, bool) {
	// Disjunctive hyp `p ∨ q`: split, feeding each disjunct to a branch. No lemma
	// — the disjunction proof is the hyp itself. (Mirrors tactic.HypDisjTactic.)
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
	// `≠` hyp `¬(a=b)` over num: a<b ∨ b<a (LessThanTrichotomy with the `a=b` disjunct
	// killed under the hyp). The complementary comparisons feed the linear core.
	if inner := ext.MatchesNOT(h); inner != nil {
		if a, b, ok := ext.MatchesEQ(inner); ok && isNat(a) {
			tri := trichotomyNeq(a, b)
			if tri == nil {
				return splittableAtom{}, false // LessThanTrichotomy unbundled — decline.
			}
			return splittableAtom{
				atom:      h,
				disjProof: tri, // {¬(a=b)} ⊢ (a<b) ∨ (b<a)
				branches: [2]splitBranch{
					{guard: lt(a, b), facts: []*prop.PropWrapper{prop.Assume(lt(a, b))}},
					{guard: lt(b, a), facts: []*prop.PropWrapper{prop.Assume(lt(b, a))}},
				},
			}, true
		}
	}
	// Implication hyp `p ⇒ q`: classically `¬p ∨ q` — a disjunction the linear
	// core drops entirely (parseHypConstraint ingests only `< ≤ = > ≥`). Split on
	// the derived `{p⇒q} ⊢ ¬p ∨ q`: the ¬p branch additionally bridges to the
	// complementary positive comparison (NotLessThan/NotLessEq) when p is a `<`/`≤` atom,
	// so the linear core can use it; the q branch feeds q. No new supply — the
	// disjunction comes from the prop-layer BinaryThm. (NOT is a distinct const
	// from IMPLY, so the `≠` branch above never reaches here.)
	if p, q, ok := prop.MatchesIMPLY(h); ok {
		np := not(p)
		b0 := []*prop.PropWrapper{prop.Assume(np)}
		if negPos, bridge, ok := negComparison(p); ok {
			_ = negPos
			b0 = append(b0, bridge) // {¬p} ⊢ negPos — the linear-usable form of ¬p
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
	// Product hyp `a·b = 0` / `0 = a·b`: a = 0 ∨ b = 0 (MulEqZero — ℕ has
	// no zero divisors; nat_products.go).
	return natProductZeroSplit(h)
}

// trichotomyNeq derives `{¬(a=b)} ⊢ (a<b) ∨ (b<a)` from LessThanTrichotomy
// (`((a<b) ∨ (b<a)) ∨ (a=b)`): disjSyllogism (orientation-agnostic) removes the
// `a=b` disjunct — here on the RIGHT — under the `¬(a=b)` hyp, with no manual
// CommuteOR. nil when LessThanTrichotomy is unbundled (graceful decline, like the monus
// split's nil-checks — avoids the implyLeaf placeholder being used in a real
// proof).
func trichotomyNeq(a, b Term) *prop.PropWrapper {
	if lessThanTrichotomyThm() == nil {
		return nil
	}
	ltc := lessThanTrichotomy(a, b) // ⊢ ((a<b) ∨ (b<a)) ∨ (a=b)
	return disjSyllogism(ltc, prop.Assume(not(eqT(a, b))))
}

// monusSplittable is the subtraction kind: an irreducible `a − b` split on
// LessEqTotal, pinned by SubEqZero (0 = a−b) / SubAddCancel (a = (a−b)+b). Reducible monus
// (one operand dominates — the simp pass clears it) and the degenerate a≡b are
// skipped, as is an incomplete SubEqZero/SubAddCancel/LessEqTotal supply.
//
// Each branch injects BOTH the ordering guard (`prop.Assume(le(…))`) AND the pin
// — mirroring condSplit. The guard is load-bearing for COMPOSING
// splits: the `0 = a−b` truncation pin does NOT encode the ordering `a≤b`, so a
// SIBLING monus atom split deeper in the recursion (whose own closing argument
// needs this branch's ordering, e.g. the `b≤c` leg of a triangle inequality)
// would be missing it. The relating pin `a = (a−b)+b` happens to imply `b≤a`
// already, but injecting the guard uniformly is harmless (redundant) and is what
// lets the linear core see every ordering the case analysis has established.
func monusSplittable(m Term) (splittableAtom, bool) {
	a, b, ok := MatchesMinus(m)
	if !ok || monusReducible(a, b) {
		return splittableAtom{}, false
	}
	if subEqZeroThm() == nil || subAddCancelThm() == nil || lessEqTotalThm() == nil {
		return splittableAtom{}, false
	}
	return splittableAtom{
		atom:      m,
		disjProof: lessEqTotal(a, b), // (a≤b) ∨ (b≤a)
		branches: [2]splitBranch{
			{guard: le(a, b), facts: []*prop.PropWrapper{prop.Assume(le(a, b)), subEqZero(a, b).LeftAssume()}},      // {a≤b} ⊢ a≤b, 0 = a−b
			{guard: le(b, a), facts: []*prop.PropWrapper{prop.Assume(le(b, a)), subAddCancelImp(b, a).DemoteHyp()}}, // {b≤a} ⊢ b≤a, a = (a−b)+b
		},
	}, true
}

// monusReducible reports whether `a − b` is simplifiable to a closed form by the
// simp pass — i.e. one operand's linear form dominates the other componentwise
// (a ≥ b ⇒ subCancel, or a ≤ b ⇒ subTrunc). Cheap: the classifier only, no proof.
func monusReducible(a, b Term) bool {
	if _, ok := linSub(mpolyOf(a), mpolyOf(b)); ok {
		return true
	}
	_, ok := linSub(mpolyOf(b), mpolyOf(a))
	return ok
}

// Named-theorem leaves for the subtraction (monus) layer. Same
// bundle discipline as the rest of omega: each reads its theorem from the
// installed NatLemmaBundle (instantiated + oriented by eqLeaf/implyLeaf) and
// falls back to a placeholder stand-in (bundle.go, test-only) when the
// field is nil. In a non-test build (no fabricator), a nil/shape-mismatched field
// panics — so every leaf below MUST have its bundle field wired (serve.InstallNatBundle).

// addSubLeftCancel: ⊢ (b + d) - b = d   (real: AddSubLeftCancel `∀n m. n = (m+n)-n`, reversed).
// The cancellation congruence: subCancel ring-proves `a = b+d`, congruences it to
// `a-b = (b+d)-b`, then this closes `(b+d)-b = d`.
func addSubLeftCancel(b, d Term) *prop.PropWrapper {
	return eqLeaf(addSubLeftCancelThm(), []Term{d, b}, minus(plus(b, d), b), d)
}

// subEqZero: ⊢ (a ≤ b) ⇔ (0 = a - b)   (real: SubEqZero). The truncate-to-0
// equivalence: the a≤b branch of the monus split EqMP's its LHS to pin `a-b = 0`;
// subTrunc EqMP's the discharged `a≤b` the other way to REWRITE `a-b → 0`.
func subEqZero(a, b Term) *prop.PropWrapper {
	return eqLeaf(subEqZeroThm(), []Term{a, b}, le(a, b), eqT(natZero, minus(a, b)))
}

// subAddCancelImp: ⊢ (b ≤ a) ⇒ (a = (a - b) + b)   (real: SubAddCancel, IMPLICATION form).
// The b≤a branch of the monus split DemoteHyp's this to `{b≤a} ⊢ a = (a-b)+b`,
// pinning the difference atom `a-b` to a `+`-fact the linear core can use.
// SubAddCancel's normal form is the clause `¬(n≤m) ∨ (m=(m-n)+n)`; the bundle adapts
// it to this implication via PromiseForGeneral (same seam as the *Add2 lemmas).
func subAddCancelImp(b, a Term) *prop.PropWrapper {
	return implyLeaf(subAddCancelThm(), []Term{b, a}, imply(le(b, a), eqT(a, plus(minus(a, b), b))))
}

// lessEqTotal: ⊢ (a ≤ b) ∨ (b ≤ a)   (real: LessEqTotal). The source disjunction the
// monus split case-eliminates over. (implyLeaf is the generic "named theorem by
// conclusion α-match" leaf — it accepts any conclusion shape, here a ∨.)
func lessEqTotal(a, b Term) *prop.PropWrapper {
	return implyLeaf(lessEqTotalThm(), []Term{a, b}, or(le(a, b), le(b, a)))
}

// lessThanTrichotomy: ⊢ ((a<b) ∨ (b<a)) ∨ (a=b)   (real: LessThanTrichotomy). The trichotomy source
// for the `≠`-hypothesis split (trichotomyNeq), which kills the `a=b`
// disjunct under the `¬(a=b)` hyp to leave the `a<b ∨ b<a` case split. Note the
// LEFT-association `(P∨Q)∨R` — the normalized form.
func lessThanTrichotomy(a, b Term) *prop.PropWrapper {
	return implyLeaf(lessThanTrichotomyThm(), []Term{a, b}, or(or(lt(a, b), lt(b, a)), eqT(a, b)))
}

// lessEqAdd: ⊢ a ≤ (a + e)   (real: LessEqAdd). subTrunc uses it to derive `a ≤ b` from
// the ring witness `b = a + e` before discharging SubEqZero into the `a-b → 0`
// rewrite.
func lessEqAdd(a, e Term) *prop.PropWrapper {
	return implyLeaf(lessEqAddThm(), []Term{a, e}, le(a, plus(a, e)))
}

// nat_max / nat_min — the case-split engine's second client. Both are
// defined as `nat_max a b = COND(a≤b, b, a)` / `nat_min a b = COND(a≤b, a, b)`, i.e.
// piecewise-linear by the guard `a≤b` — exactly the shape proveSplit eliminates.
// Unlike monus (LessEqTotal, both guards positive), nat_max/nat_min split on excluded middle
// of the guard, because the def's then/else selection turns on `a≤b` itself: a
// `b≤a` branch would leave the guard contingent at `a=b`. The pins reuse the arith
// deep rewrite to collapse the COND under each branch's guard — no manual COND
// surgery, and the collapse is by the true value (sound even on the vacuous arm
// of a concrete nat_max, where the decider folds the guard numerically).

// maxSplittable / minSplittable are the kind constructors registered in
// splittableKinds. Graceful no-op when the nat_max/nat_min def is unbundled.
func maxSplittable(m Term) (splittableAtom, bool) {
	a, b, ok := MatchesMax(m)
	if !ok {
		return splittableAtom{}, false
	}
	return minMaxSplittable(m, a, b, maxDef(a, b))
}

func minSplittable(m Term) (splittableAtom, bool) {
	a, b, ok := MatchesMin(m)
	if !ok {
		return splittableAtom{}, false
	}
	return minMaxSplittable(m, a, b, minDef(a, b))
}

// minMaxSplittable builds the excluded middle split shared by nat_max and nat_min, given
// the instantiated def `⊢ (nat_max/nat_min a b) = COND(a≤b, x, y)`:
//
//	(a≤b) ∨ ¬(a≤b)                               [excluded middle]
//	a≤b branch:   pin (nat_max/nat_min a b) = x          [COND collapses under a≤b]
//	¬(a≤b) branch: pin (nat_max/nat_min a b) = y          [COND collapses under b<a]
//
// The ¬(a≤b) branch bridges its guard to the positive `b<a` (NotLessEq) so the
// linear prover can both consume it and let the COND fold. A thin wrapper over
// the generic condSplit (which the raw-COND kind also uses) with guard a≤b.
func minMaxSplittable(m, a, b Term, def *prop.PropWrapper) (splittableAtom, bool) {
	if def == nil {
		return splittableAtom{}, false // nat_max/nat_min def unbundled — decline gracefully.
	}
	return condSplit(m, def, le(a, b))
}

// condSplit builds the excluded middle split of an atom whose value is piecewise
// by a comparison `guard`, given `def : ⊢ atom = COND(guard, x, y)`:
//
//	guard ∨ ¬guard                          [excluded middle]
//	guard  branch:  pin atom = x            [COND collapses under guard]
//	¬guard branch:  pin atom = y            [COND collapses under ¬guard's positive form]
//
// The ¬guard branch bridges to the complementary positive comparison (negComparison
// via NotLessThan/NotLessEq) so the linear prover can both consume it and let the COND fold.
// Used by nat_max/nat_min (via minMaxSplittable, def = the const-def) and by the raw-COND
// kind (condSplittable, def = reflexivity). Returns ok=false when the guard is not
// a `<`/`≤` comparison or a pin fails to fold.
func condSplit(atom Term, def *prop.PropWrapper, guard Term) (splittableAtom, bool) {
	negPos, negBridge, ok := negComparison(guard)
	if !ok {
		return splittableAtom{}, false // guard not a `<`/`≤` comparison.
	}
	pinT := condPin(def, guard)     // {guard} ⊢ atom = x
	pinFraw := condPin(def, negPos) // {negPos} ⊢ atom = y
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

// negComparison maps a `<`/`≤` comparison `guard` to its complementary positive
// comparison `negPos` plus the bridge `{¬guard} ⊢ negPos` (NotLessThan / NotLessEq):
//
//	u < v  →  v ≤ u   (NotLessThan: ¬(u<v) ⇔ v≤u)
//	u ≤ v  →  v < u   (NotLessEq: ¬(u≤v) ⇔ v<u)
//
// ok=false for any other shape; a COND on such a guard is split by the
// guard's atoms (compoundCondSplit).
func negComparison(guard Term) (negPos Term, bridge *prop.PropWrapper, ok bool) {
	if u, v, m := MatchesLt(guard); m {
		return le(v, u), notLT(u, v).LeftAssume(), true // {¬(u<v)} ⊢ v≤u
	}
	if u, v, m := MatchesLe(guard); m {
		return lt(v, u), notLE(u, v).LeftAssume(), true // {¬(u≤v)} ⊢ v<u
	}
	return nil, nil, false
}

// condSplittable is the raw-COND kind: a num-typed `COND(guard, x, y)` whose guard
// is a `<`/`≤` comparison the linear core can't decide is split on excluded middle
// of the guard, each arm pinned by the reflexive def. (nat_max/nat_min have their own kinds
// — they expand a const-def first; this catches a bare arith conditional, e.g. a
// def-expanded `if a≤b then … else …`.) A foldable COND is cleared by the simp
// pass before reaching here, exactly as monusReducible gates the monus split.
// A guard of any other shape is split by its atoms (compoundCondSplit).
func condSplittable(c Term) (splittableAtom, bool) {
	guard, _, _, ok := ext.MatchesCond(c)
	if !ok || !isNat(c) {
		return splittableAtom{}, false
	}
	if natDomain.isOrderAtom(guard) {
		return condSplit(c, prop.Refl(c), guard)
	}
	return compoundCondSplit(c, prop.Refl(c), guard, negComparison)
}

// condPin collapses the COND on the RHS of `def` under the branch guard, returning
// `{guardHyp} ⊢ (def.lhs) = <branch value>`. It reuses the arith deep rewrite:
// ArithDecideWithHyps([guardHyp]) decides the COND's guard from guardHyp and
// trivialCondRewrite folds the COND — so the result carries {guardHyp} and pins
// the nat_max/nat_min atom to its actual value. nil when the guard does not fold the COND.
func condPin(def *prop.PropWrapper, guardHyp Term) *prop.PropWrapper {
	// Raw (no pre-simp): guardHyp is a branch-pin whose AlphaEquals identity
	// downstream paths rely on — see arithDecideWithHypsRaw.
	simp := arithDecideWithHypsRaw([]Term{guardHyp})(prop.Rhs(def))
	if simp == nil {
		return nil
	}
	return def.EqTrans(simp)
}

// ── Idempotence simp leaves (arithSimpStep): nat_max a a → a, nat_min a a → a ─────────

// maxIdemp / minIdemp rewrite `nat_max a a → a` / `nat_min a a → a` via the def + CondId
// (`COND(c, x, x) = x`) — no guard decision needed. nil when the def is unbundled
// or the COND branches differ (a ≢ b).
func maxIdemp(a Term) *prop.PropWrapper { return minMaxIdemp(maxDef(a, a)) }
func minIdemp(a Term) *prop.PropWrapper { return minMaxIdemp(minDef(a, a)) }

func minMaxIdemp(def *prop.PropWrapper) *prop.PropWrapper {
	if def == nil {
		return nil
	}
	guard, x, y, ok := ext.MatchesCond(prop.Rhs(def))
	if !ok || !x.AlphaEquals(y) {
		return nil
	}
	return def.EqTrans(prop.CondId(guard, x)) // ⊢ (nat_max/nat_min a a) = a
}

// maxDef / minDef instantiate the bundled const-def at (a, b):
// `⊢ (nat_max/nat_min a b) = COND(a≤b, …)`, or nil when unbundled.
func maxDef(a, b Term) *prop.PropWrapper { return defInst(maxDefThm(), a, b) }
func minDef(a, b Term) *prop.PropWrapper { return defInst(minDefThm(), a, b) }

func defInst(thm *prop.PropWrapper, a, b Term) *prop.PropWrapper {
	if thm == nil {
		return nil
	}
	return instAll(thm, []Term{a, b})
}

// predecessor has no algebra of its own: `predecessor n = n - 1`
// (truncated), so a single simp leaf bridges it into the monus layer and
// everything downstream is already handled — `predecessor(suc n) → suc n − 1 → n` and
// `predecessor 0 → 0 − 1 → 0` collapse via subCancel/subTrunc, and a symbolic `predecessor m` (in
// a comparison) is decided by the monus case split on `m − 1`. So predecessor needs no
// case-split kind of its own, just the bridge.
//
// The bridge is DERIVED from the Sub recursion (already in the corpus) — no
// dedicated `predecessor n = n - 1` lemma is needed:
//
//	predecessor(n − 0) = n − suc 0     [Sub clause 2 at (m:=n, n:=0)]
//	predecessor(n)     = n − suc 0     [n − 0 = n, Sub clause 1, under predecessor]
//	predecessor(n) = n − 1 [suc 0 = 1]

// preBridge proves `⊢ predecessor n = n − 1`, or nil when the Sub recursion is unbundled.
// The two Sub clauses are projected by shape (projectMatch handles Sub's
// per-conjunct ∀ and either orientation), so it is robust to the form
// `(∀m. m−0=m) ∧ (∀m n. m−suc n=predecessor(m−n))`:
//
//	predecessor(n−0) = n − suc 0     [clause 2 at (m:=n, n:=0)]
//	n − 0    = n             [clause 1 at m:=n]   ⇒  predecessor(n) = n − suc 0
//	predecessor(n) = n − 1 [suc 0 = 1]
func preBridge(n Term) *prop.PropWrapper {
	sub := subThm()
	if sub == nil {
		return nil
	}
	nSub0, ok1 := projectMatch(sub, minus(n, natZero), n)                             // n−0 = n
	preEq, ok2 := projectMatch(sub, preT(minus(n, natZero)), minus(n, sucT(natZero))) // predecessor(n−0) = n−suc 0
	if !ok1 || !ok2 {
		return nil
	}
	step := nSub0.LeftApply(natPre).EqSym().EqTrans(preEq) // predecessor(n) = predecessor(n−0) = n − suc 0
	// n − suc 0 = n − 1   [suc 0 = 1, under (n − ·)].
	minusCong := sucBits(natZero).LeftApply(ext.Apply(natMinus, n))
	return step.EqTrans(minusCong) // predecessor(n) = n − 1
}

// Parity (nat_even/nat_odd) → nat_mod-2 bridge. nat_even/nat_odd are not given their own
// decision procedure; they are rewritten into the nat_mod-2 form so the existing
// nat_div/nat_mod machinery decides them:
//
//	nat_even n  ⇔  (0 = nat_mod(n, 2))    [EvenIffModTwoZero]
//	nat_odd n   ⇔  (1 = nat_mod(n, 2))    [nat_parity.OddIffModTwoOne]
//
// parityBridge is a shallow rewrite leaf (composed into the deep+fixpoint rewrite
// alongside arithSimpStep / arithDecideLeaf). After it fires, the cascade closes
// the common cases through layers that already exist:
//   - literal n: the nat_mod evaluator simp (divModSimp's literal case) reduces
//     `nat_mod(n, 2)` to its value, leaving `0 = 0` / `1 = 0` etc. for the atom decider.
//   - nat_even/nat_odd as a HYP: the rewritten `0 = nat_mod(n, 2)` hypothesis is a num equality
//     the linear core ingests (the opaque `nat_mod(n, 2)` atom pinned to 0).
//   - `nat_mod(n, 2) = 0` goal under such a hyp: decided by the same equality.
//
// Both leaves nil-CHECK their bundle field, so an incomplete bundle degrades to a
// graceful no-op (nat_even/nat_odd stay opaque) rather than an eqLeaf placeholder.

// parityBridge rewrites a `nat_even n` / `nat_odd n` atom. A parity over a PRODUCT or SUM
// is decomposed STRUCTURALLY (EvenMul / EvenAdd) so a NONLINEAR parity goal
// reduces through the bool layer; everything else falls to the nat_mod-2 bridge. nil
// for a non-parity atom / when the needed bundle lemma is absent.
func parityBridge(t Term) *prop.PropWrapper {
	if n, ok := MatchesEven(t); ok {
		if w := evenStructural(n); w != nil {
			return w
		}
		return evenBridge(n)
	}
	if n, ok := MatchesOdd(t); ok {
		if w := oddStructural(n); w != nil {
			return w
		}
		return oddBridge(n)
	}
	return nil
}

// evenStructural decomposes a parity atom over a PRODUCT or SUM via the
// multiplicative / additive parity lemmas, the route for NONLINEAR parity goals
// (where the nat_mod-2 bridge would only leave an opaque `(a*b) nat_mod 2`):
//
//	nat_even(a·b) ⇔ nat_even a ∨ nat_even b        [EvenMul]
//	nat_even(a+b) ⇔ (nat_even a ⇔ nat_even b)      [EvenAdd]
//
// The deep rewrite then re-bridges the smaller nat_even a / nat_even b atoms and the bool
// layer closes the residual — OR-idempotence (`nat_even(n·n) ⇔ nat_even n`), excluded
// middle (`nat_even(n·(n+1))` → `nat_even n ∨ ¬nat_even n` → ⊤), the `⊤ ∨ _` / `p ⇔ ⊤` folds.
// nil for a non-product/sum arg or an unsupplied lemma.
func evenStructural(n Term) *prop.PropWrapper {
	if a, b, ok := MatchesStar(n); ok && evenMulThm() != nil {
		return eqLeaf(evenMulThm(), []Term{a, b}, evenT(star(a, b)), or(evenT(a), evenT(b)))
	}
	if a, b, ok := MatchesPlus(n); ok && evenAddThm() != nil {
		return eqLeaf(evenAddThm(), []Term{a, b}, evenT(plus(a, b)), eqT(evenT(a), evenT(b)))
	}
	return nil
}

// oddStructural mirrors evenStructural through OddIffNotEven — `nat_odd(a·b) ⇔ ¬(nat_even a ∨
// nat_even b)`, `nat_odd(a+b) ⇔ ¬(nat_even a ⇔ nat_even b)` — after which the deep rewrite's
// PushNegRewrite distributes the ¬ and each nat_even bridges. nil when the arg is not
// a product/sum or a needed lemma is unbundled.
func oddStructural(n Term) *prop.PropWrapper {
	return oddViaNotEven(n, evenStructural(n))
}

// evenBridge: ⊢ nat_even n ⇔ (0 = nat_mod(n, 2))   (real: EvenIffModTwoZero). nil when unbundled.
func evenBridge(n Term) *prop.PropWrapper {
	if evenIffModTwoZeroThm() == nil {
		return nil
	}
	return eqLeaf(evenIffModTwoZeroThm(), []Term{n}, evenT(n), eqT(natZero, modT(n, Numeral(2))))
}

// oddBridge: ⊢ nat_odd n ⇔ ¬(0 = nat_mod(n, 2))   composed from OddIffNotEven (`nat_odd n ⇔ ¬nat_even n`)
// and EvenIffModTwoZero (`nat_even n ⇔ (0 = nat_mod(n, 2))`):
//
//	nat_odd n ⇔ ¬nat_even n                         [OddIffNotEven]
//	¬nat_even n ⇔ ¬(0 = nat_mod(n, 2))               [EvenIffModTwoZero lifted through (¬p⇔¬q)⇔(p⇔q)]
//	────────────────────────────────────
//	nat_odd n ⇔ ¬(0 = nat_mod(n, 2))                  [EqTrans]
//
// The ¬-form (vs the `1 = nat_mod(n, 2)` form) composes directly with the literal nat_mod
// eval (`nat_odd 7 → ¬(0 = 1) → ⊤`) and the ≠-hyp split, and avoids that form's stale
// emit. nil when either lemma is unbundled.
func oddBridge(n Term) *prop.PropWrapper {
	return oddViaNotEven(n, evenBridge(n))
}

// oddViaNotEven lifts an even-equivalence `⊢ nat_even n ⇔ X` to `⊢ nat_odd n ⇔ ¬X` via
// OddIffNotEven (`nat_odd n ⇔ ¬nat_even n`) and `(¬p ⇔ ¬q) ⇔ (p ⇔ q)`. Shared by oddBridge
// (X = the nat_mod-2 form) and oddStructural (X = the EvenMul/EvenAdd decomposition).
// nil when evenEquiv is nil or OddIffNotEven is unbundled.
func oddViaNotEven(n Term, evenEquiv *prop.PropWrapper) *prop.PropWrapper {
	if evenEquiv == nil || oddIffNotEvenThm() == nil {
		return nil
	}
	X := prop.Rhs(evenEquiv)                                                       // nat_even n ⇔ X  →  X
	oddIffNotEven := eqLeaf(oddIffNotEvenThm(), []Term{n}, oddT(n), not(evenT(n))) // ⊢ nat_odd n ⇔ ¬nat_even n
	// ¬nat_even n ⇔ ¬X  from evenEquiv via (¬p ⇔ ¬q) ⇔ (p ⇔ q).
	notCong := prop.BinaryThms["(¬p ⇔ ¬q) ⇔ (p ⇔ q)"](evenT(n), X).EqSym().EqMP(evenEquiv)
	return oddIffNotEven.EqTrans(notCong) // ⊢ nat_odd n ⇔ ¬X
}

// proveLinParity is the HYPOTHESIS-side parity bridge (the dual of the goal-side
// parityBridge leaf): the deep rewrite rewrites nat_even/nat_odd in the GOAL, but an
// nat_even/nat_odd HYP is dropped by the linear core (parseHypConstraint ingests only
// `< ≤ = > ≥`). For each nat_even n / nat_odd n hyp this derives its nat_mod-2 equation as a
// fact (`{nat_even n} ⊢ 0 = nat_mod(n, 2)` via EvenIffModTwoZero ∘ Assume), injects it, runs the
// linear prover, and cuts the fact back — the same introduce+cut pattern as
// proveLinDivMod, so the returned wrapper carries only the original nat_even/nat_odd hyps.
// Returns (nil,false) when there is no parity hyp (or the bridge is unbundled, or
// linarith still fails). Closes e.g. `nat_even n ⊢ 0 = nat_mod(n, 2)` and the
// `nat_even n, nat_odd n ⊢ …` contradiction (0 = nat_mod(n, 2) ∧ 1 = nat_mod(n, 2) ⇒ 0 = 1).
func proveLinParity(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	var facts []*prop.PropWrapper
	for _, h := range hyps {
		if n, ok := MatchesEven(h); ok {
			if b := evenBridge(n); b != nil {
				facts = append(facts, b.EqMP(prop.Assume(h))) // {nat_even n} ⊢ 0 = nat_mod(n, 2)
			}
		} else if n, ok := MatchesOdd(h); ok {
			if b := oddBridge(n); b != nil {
				facts = append(facts, b.EqMP(prop.Assume(h))) // {nat_odd n} ⊢ 1 = nat_mod(n, 2)
			}
		}
	}
	if len(facts) == 0 {
		return nil, false
	}
	return enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) { return proveLinThenInt(slices.Values(h), goal) },
		hyps, facts)
}

// dist → monus bridge. num distance is `nat_dist(m,n) = (m-n) + (n-m)`
// (= |m-n|). Like predecessor, dist
// is not given its own decision procedure: a simp leaf rewrites `nat_dist(,(m,n)) →
// (m-n) + (n-m)`, routing ALL dist into the truncated-subtraction layer —
// `nat_dist(n,n)`/`nat_dist(0,n)`/`nat_dist(n,0)` collapse via subCancel/subTrunc, and a
// symbolic `nat_dist(m,n)` in a comparison is decided by the monus case split on its
// two `a-b` atoms.
//
// dist's argument is a PAIR. Its raw const definition is over that pair via fst/snd
// (`∀p. nat_dist(p) = (fst p - snd p) + (snd p - fst p)`), but the chapter's `dist`
// THEOREM (nat_monus.Dist) is the clean `∀m n. nat_dist(,(m,n)) = (m-n) + (n-m)` — so
// the bundle binds it directly (Dist) and the bridge is one monomorphic
// instantiation, no fst/snd reduction. nil-checks Dist so an incomplete bundle
// degrades to a graceful no-op (dist stays opaque) rather than a placeholder
// rewrite.

// distBridge: ⊢ nat_dist(,(m,n)) = (m-n) + (n-m)   (nat_monus.Dist's ∀m n form at (m,n)).
func distBridge(m, n Term) *prop.PropWrapper {
	if distThm() == nil {
		return nil
	}
	return instAll(distThm(), []Term{m, n})
}
