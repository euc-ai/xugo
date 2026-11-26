package omega

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// Integer (ℤ) identity-fold simp + comparison-decision leaf — the twin of the
// real section of real.go. Together they are the int analogue of
// ArithDecideWithHyps: the shallow `+`/`*` identity folds plus the atom decider
// (RingProve for `=`, IntLinProve for `< ≤ = ≠ > ≥`), driven deep + to fixpoint
// by the shared prop.DeepRewrite. ℤ has no integer-cut/parity/divmod/split
// fallbacks in this first cut, so this is the whole decision fragment.

func isIntLit(t Term) bool {
	x, ok := MatchesIntOfNum(t)
	return ok && isBitTree(x)
}

func isIntZero(t Term) bool { return t.AlphaEquals(intLit(0)) }
func isIntOne(t Term) bool  { return t.AlphaEquals(intLit(1)) }

// The mirror orientations are DERIVED via commutativity (intCommuteADD/MUL) like
// the real leaves, keeping the bundle minimal.

// intAddLeftIdentity: ⊢ &0 + a = a   (commute then right-identity).
func intAddLeftIdentity(a Term) *prop.PropWrapper {
	return intCommuteADD(intLit(0), a).EqTrans(intAddZeroR(a))
}

// intMulRid: ⊢ a · &1 = a   (commute then left-identity).
func intMulRid(a Term) *prop.PropWrapper {
	return intCommuteMUL(a, intLit(1)).EqTrans(intOneMul(a))
}

// intMulRzero: ⊢ a · &0 = &0   (commute then left-zero).
func intMulRzero(a Term) *prop.PropWrapper {
	return intCommuteMUL(a, intLit(0)).EqTrans(intZeroMul(a))
}

// intArithSimpStep is the one-level identity-fold rewrite (mirror of
// realArithSimpStep): the matching identity leaf or numeral fold, or nil when t
// is not a reducible int `+`/`*` redex. DeepRewrite drives it deep + to fixpoint.
func intArithSimpStep(t Term) *prop.PropWrapper {
	if w := intAbsSgnSimp(t); w != nil { // abs/sgn algebraic laws (push abs/sgn to leaves)
		return w
	}
	if w := intPowLawSimp(t); w != nil { // pow distribution: abs(x) pow 2 → x pow 2  (SquareOfAbs)
		return w
	}
	if w := intAbsLessEqIffPowTwoLessEqSimp(t); w != nil { // x^2 ≤ y^2 → |x| ≤ |y|  (AbsLessEqIffPowTwoLessEq)
		return w
	}
	if w := intNegEqZeroSimp(t); w != nil { // (−x = &0) ⇔ (x = &0)  (NegEqZero)
		return w
	}
	if w := intDividesIffRemZeroSimp(t); w != nil { // int_rem(m,n) = &0 → int_divides(n,m)  (DividesIffRemZero)
		return w
	}
	if w := intPowSimp(t); w != nil { // int_pow m c → product chain (literal c ≤ 1)
		return w
	}
	if w := intDivModSimp(t); w != nil { // int_div/int_rem with divisor &0/&1 → folded (nat_divmod.go)
		return w
	}
	if l, r, ok := intDomain.matchPlus(t); ok {
		switch {
		case isIntZero(r): // x + &0 → x
			return intAddZeroR(l)
		case isIntZero(l): // &0 + x → x
			return intAddLeftIdentity(r)
		case isIntLit(l) && isIntLit(r): // &m + &n → &k
			if w, ok := intNormNatAdd(l, r); ok {
				return w
			}
		}
		return nil
	}
	if l, r, ok := intDomain.matchStar(t); ok {
		switch {
		case isIntZero(r): // x * &0 → &0
			return intMulRzero(l)
		case isIntZero(l): // &0 * x → &0
			return intZeroMul(r)
		case isIntOne(r): // x * &1 → x
			return intMulRid(l)
		case isIntOne(l): // &1 * x → x
			return intOneMul(r)
		case isIntLit(l) && isIntLit(r): // &m * &n → &k
			if w, ok := intNormNatMul(l, r); ok {
				return w
			}
		}
		return nil
	}
	return nil
}

// ── comparison / equality decision leaf ─────────────────────────────────────

// isIntComparisonGoal reports whether t is an int comparison/equality atom (the
// gate the decide leaf applies). The isIntTerm guard on the `=` / `≠` cases keeps
// a bool `⇔` or a non-int `=` out.
func isIntComparisonGoal(t Term) bool {
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
	if inner := ext.MatchesNOT(t); inner != nil {
		if l, _, ok := ext.MatchesEQ(inner); ok {
			return isIntTerm(l)
		}
	}
	return false
}

// matchIntEq reports whether P is an int equality `a = b` (not a bool ⇔, not a
// non-int `=`).
func matchIntEq(P Term) (Term, Term, bool) {
	a, b, ok := ext.MatchesEQ(P)
	if !ok || !isIntTerm(a) {
		return nil, nil, false
	}
	return a, b, true
}

// intProveDecAtom is the ⊤-direction prover the int decider uses: try the ring
// normalizer first for an `=` atom (IntRingProveFull closes universally-true int
// equalities incl. nonlinear products and like-term merges, hyp-free), then fall
// through to the linear forward prover (IntLinProve — `<` `≤` `=` `≠` and
// `>`/`≥` via the definitional bridge), the various enrichment + structural
// handlers, and finally the sign-split (Image) and bounded-enum fallbacks.
func intProveDecAtom(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	return intProveDecAtomGated(hyps, goal, true, true)
}

// intProveDecAtomNoSignSplit is intProveDecAtom WITHOUT the sign-split-style
// fallbacks (intImageSplit + intProveBoundedEnum). Used by the engine's
// unified int decide leaf (composeArithLeaves), where the per-atom sign
// split's 4-way × per-atom × multi-pass explosion is too expensive. The
// linear core, ring, all enrichments, structural splits (which use IntLinProve
// as their own branch prover so they don't recurse), divides-skolemize, and
// ONE level of Gaussian elimination (intElimEqHyps, whose own sub-decider is
// the branch prover below) are all still available — only the sign-split
// itself is pruned.
func intProveDecAtomNoSignSplit(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	return intProveDecAtomGated(hyps, goal, false, true)
}

// intProveDecAtomBranch is the BRANCH prover: no sign-split fallbacks AND no
// Gaussian elimination. Used (via intArithDecideWithHypsRawBranch) as the
// sub-prover INSIDE case-split-style handlers (imageBranchImp, intElimEqHyps),
// so a branch can't recursively re-enter the machinery that spawned it and
// loop. intElimEqHyps must be excluded here just like intImageSplit: its
// recursion guard is identity-keyed on the CURRENT hyp slice, which a nested
// self-reentry extends every level (fresh substituted copies + ν-var pins), so
// un-gated it self-recurses with monotonically growing hyps and never
// terminates. One structural boundary stands in place of per-call-site
// reentry guards: a branch gets linear core, ring, enrichments, and
// structural splits — never a case-split handler.
func intProveDecAtomBranch(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	return intProveDecAtomGated(hyps, goal, false, false)
}

// intProveDecAtomGated is the shared implementation of intProveDecAtom /
// intProveDecAtomNoSignSplit / intProveDecAtomBranch. The `allowSignSplit`
// flag gates the last two handlers (intImageSplit + intProveBoundedEnum); the
// `allowElimEq` flag gates the Gaussian cross-hyp elimination (intElimEqHyps)
// — every other handler is always run.
func intProveDecAtomGated(hyps iter.Seq[Term], goal Term, allowSignSplit, allowElimEq bool) (*prop.PropWrapper, bool) {
	hs := slices.Collect(hyps)
	if l, r, ok := ext.MatchesEQ(goal); ok && isIntTerm(l) {
		if w, ok := IntRingProveFull(l, r); ok {
			return w, true
		}
	}
	if w, ok := IntLinProve(slices.Values(hs), goal); ok {
		return w, true
	}
	// Euclidean int_div/int_rem bounded-atom enrichment (nat_divmod.go): inject the
	// DivisionIdentity identity + the `&0 ≤ int_rem(m,n) < n` bounds for every int_div/int_rem
	// atom, then re-run linarith — for a literal/positive divisor this pins the
	// values via ℤ-discreteness (`int_div(&7,&2) = &3`, `int_rem(m,&3) < &3`, …).
	if w, ok := intProveDivRem(hs, goal); ok {
		return w, true
	}
	// int_divides ↔ div size bound (DivisorBoundedByDividend): a divides hyp
	// paired with `e ≠ &0` injects `|d| ≤ |e|`, refuting `int_divides(&5,&3)`
	// and producing `|d| ≤ |e|` facts for linarith elsewhere.
	if w, ok := intProveDivisorBound(hs, goal); ok {
		return w, true
	}
	// Exact-division identity (QuotientExactOfDivides): a divides hyp `q ∣ m`
	// injects `int_div(m,q)·q = m`, so linarith can substitute `int_div(m,q)` away
	// under the divisibility assumption.
	if w, ok := intProveQuotientExact(hs, goal); ok {
		return w, true
	}
	// Monotone scaling / sign-of-product: a nonlinear `c·a ⋈ c·b`
	// or `&0 ≤ x·y` whose sign/order side conditions discharge from the hyps —
	// `a≤b ∧ &0≤c ⊢ c·a≤c·b`, `&0≤x ∧ &0≤y ⊢ &0≤x·y`.
	if w, ok := intProveMonotone(hs, goal); ok {
		return w, true
	}
	// int_pow sign: `&0 ≤ int_pow x n` from `&0 ≤ x` (PowNonneg), the
	// no-hyp `&0 ≤ int_pow x 2` (PowTwoNonneg), `&0 < int_pow x n` from `&0 < x`
	// (PowPos). Sign-known nonlinear (NOT full RCF).
	if w, ok := intProvePowSign(hs, goal); ok {
		return w, true
	}
	// abs triangle inequality: `|t1 + (... + tn)| ≤ rhs` via iterated
	// AbsTriangle + linarith on the abs-sum bound. n-ary closed when each
	// |tᵢ| has a derivable bound and linarith can sum them.
	if w, ok := intProveAbsTriangle(hs, goal); ok {
		return w, true
	}
	// No-hyp square nonnegativity: `&0 ≤ x·x` (SquareNonneg) — the
	// single-lemma alternative to Image's sign split (placed BEFORE
	// intImageSplit below so it preempts the case-split cost).
	if w, ok := intProveSquareNonneg(goal); ok {
		return w, true
	}
	// Strict square positivity (int.go): `x ≠ &0 ⊢ &0 < x·x` — combine `&0 ≤ x·x`
	// (the SquareNonneg image split) with `x·x ≠ &0` (MulEqZero square-collapse
	// contrapositive of the hyp), eliminating the `=` disjunct of LessEqSplit.
	if w, ok := intProveStrictSquare(hs, goal); ok {
		return w, true
	}
	// Divisibility goal: `int_divides(d, e)` via an ∃-witness.
	if w, ok := intDividesGoal(goal); ok {
		return w, true
	}
	// int_of_num homomorphism collapse: a goal whose sides are
	// `&`-coerced num images — `&n·&n = &(n·n)`, `&0 ≤ &n·&n` — that linarith and
	// the ring miss (`&n` is opaque, int atoms have no default ≥0). Hyp-free;
	// the num facts reach the rows through the cast (domain.go liftHyp).
	if w, ok := intProveOfNum(goal); ok {
		return w, true
	}
	// Integral-domain square (int.go): a hyp `x·x = &0` forces `x = &0` (MulEqZero
	// collapses `x=&0 ∨ x=&0` via (p∨p)⇔p — no case split, its guards coincide). The
	// distinct-factor `x·y=&0` form is the splittable hyp below.
	if w, ok := intProveMulEqZeroSquare(hs, goal); ok {
		return w, true
	}
	// Positive-factor cancellation from a HYPOTHESIS (int_cancel.go): a hyp
	// `P·a ⋈ P·b` (or `a·P ⋈ b·P`) whose factor is provably `&0 < P` yields the
	// cancelled `a ⋈ b`, injected for one linear run and cut back. The converse
	// of the goal-side monotone scaling, and outside the Farkas fragment by
	// construction (cancelling scales a premise by a VARIABLE). Declines on a
	// structural scan when no hyp compares two products; placed last before the
	// split so nothing an earlier handler closes changes route, and so the cheap
	// cancellation is tried before the exponential case split.
	if w, ok := intProveCancelMul(hs, goal); ok {
		return w, true
	}
	// The pairwise products of the context's differences (int_products.go) —
	// the nlinarith step, real_products.go's twin; last before the split, and
	// only where a constraint carries a product.
	if w, ok := intProveProducts(hs, goal); ok {
		return w, true
	}
	// Case-split fallback (int_split.go): when the goal/hyps carry an
	// opaque-to-linarith operator (int_abs / int_max / int_min / int_sgn / raw
	// COND) or a disjunctive/≠/⇒/product-zero hypothesis, split it and prove each
	// branch. Internal to the prover — a single {hyps} ⊢ goal. The branches use the
	// linear forward prover, and intProveLeaf where nothing is left to split;
	// the −x branches flow through the signed normalizer.
	if w, ok := intProveSplit(IntLinProve, intProveLeaf, hs, goal, nil); ok {
		return w, true
	}
	// Image sign split: a bare int variable in a nonlinear
	// position is split on its sign (x = ±&n), each branch flowing through the
	// of_num collapse — closes `&0 ≤ x·x` (SquareNonneg). Sign-split style: its
	// branch sub-prover is the branch decider (intProveDecAtomBranch),
	// so a branch can't recursively re-enter this. Gated by allowSignSplit.
	if allowSignSplit {
		if w, ok := intImageSplit(hs, goal); ok {
			return w, true
		}
	}
	// Divisibility hypothesis skolemize: a `int_divides(d, e)` hyp
	// becomes a fresh linear equation `e = d·z₀` (∃-elimination), feeding the gcd test —
	// `int_divides(&2, &1)` is contradictory.
	if w, ok := intDividesSkolem(hs, goal); ok {
		return w, true
	}
	// Cross-hyp equality elimination: combine equality hyps sharing
	// a variable (`x=2z₀, x+1=2w₀` → `2z₀+1=2w₀`) so the gcd test sees the
	// eliminated form — the Gaussian step closing `2∣x ∧ 2∣(x+1) ⊢ ⊥`. Gated by
	// allowElimEq: a case-split handler's branch sub-prover must not re-enter it
	// (see intProveDecAtomBranch — un-gated this self-recurses unboundedly).
	if allowElimEq {
		if w, ok := intElimEqHyps(hs, goal); ok {
			return w, true
		}
	}
	// Bounded-variable enumeration: a goal nonlinear in a variable
	// the hyps bound by a two-sided literal range is decided by enumerating that
	// variable's finitely many values. Itself uses ByCases over branches that
	// re-enter the full decider, so it is also gated by allowSignSplit to keep
	// the restricted sub-decider bounded.
	if allowSignSplit {
		return intProveBoundedEnum(hs, goal)
	}
	return nil, false
}

// intProveNeg builds `⊢ ¬P` (mirror of realProveNeg):
//
//	¬(a<b) ⇐ b≤a   (NotLessThan)
//	¬(a≤b) ⇐ b<a   (NotLessEq)
//	¬(a=b)  is the ≠ goal      prove ¬(a=b) directly
func intProveNeg(prove proveFn, hyps iter.Seq[Term], P Term) (*prop.PropWrapper, bool) {
	if a, b, ok := intDomain.matchLt(P); ok { // ¬(a<b) ⇐ b≤a
		g, gok := prove(hyps, intLeT(b, a))
		if !gok {
			return nil, false
		}
		return intNotLT(a, b).EqSym().EqMP(g), true
	}
	if a, b, ok := intDomain.matchLe(P); ok { // ¬(a≤b) ⇐ b<a
		g, gok := prove(hyps, intLtT(b, a))
		if !gok {
			return nil, false
		}
		return intNotLE(a, b).EqSym().EqMP(g), true
	}
	if a, b, ok := matchIntEq(P); ok { // ¬(a=b) is the ≠ goal
		g, gok := prove(hyps, not(eqT(a, b)))
		if !gok {
			return nil, false
		}
		return g, true
	}
	return nil, false
}

// intDecideCmp decides a single int comparison atom P (mirror of realDecideCmp):
// `⊢ P ⇔ ⊤` or `⊢ P ⇔ ⊥`, or (nil,false). The `>` / `≥` atoms reduce to swapped
// `<` / `≤` through the definitional bridge, the resulting iff prepended.
func intDecideCmp(prove proveFn, hyps iter.Seq[Term], P Term) (*prop.PropWrapper, bool) {
	if a, b, ok := intDomain.matchGt(P); ok { // a>b ⇔ b<a
		inner, iok := intDecideCmp(prove, hyps, intLtT(b, a))
		if !iok {
			return nil, false
		}
		return intGtBridge(a, b).EqTrans(inner), true
	}
	if a, b, ok := intDomain.matchGe(P); ok { // a≥b ⇔ b≤a
		inner, iok := intDecideCmp(prove, hyps, intLeT(b, a))
		if !iok {
			return nil, false
		}
		return intGeBridge(a, b).EqTrans(inner), true
	}
	if pf, ok := prove(hyps, P); ok { // ⊤: P follows from hyps
		return eqtIntro(pf), true
	}
	if npf, ok := intProveNeg(prove, hyps, P); ok { // ⊥: ¬P follows
		return eqfIntro(npf), true
	}
	return nil, false
}

// intArithDecideLeaf is the shallow atom-decision leaf under `hyps`: returns
// `⊢ atom ⇔ V` for a decidable int comparison/equality, nil otherwise. Uses
// the full decider (intProveDecAtom).
func intArithDecideLeaf(hyps []Term) prop.Rewrite {
	return intArithDecideLeafWith(hyps, intProveDecAtom)
}

// intArithDecideLeafNoSignSplit is the restricted-decider variant of
// intArithDecideLeaf: uses intProveDecAtomNoSignSplit, so the leaf never
// enters intImageSplit / intProveBoundedEnum. Wired into the engine's unified
// int dispatch (composeArithLeaves).
func intArithDecideLeafNoSignSplit(hyps []Term) prop.Rewrite {
	return intArithDecideLeafWith(hyps, intProveDecAtomNoSignSplit)
}

// intArithDecideLeafBranch is the branch-prover variant of intArithDecideLeaf:
// uses intProveDecAtomBranch, so the leaf enters neither the sign-split
// fallbacks nor the Gaussian elimination. Wired into the branch raw decider
// (intArithDecideWithHypsRawBranch) used INSIDE case-split-style handlers.
func intArithDecideLeafBranch(hyps []Term) prop.Rewrite {
	return intArithDecideLeafWith(hyps, intProveDecAtomBranch)
}

// intArithDecideLeafWith builds a decide leaf parameterized by which prover
// to call. Shared body of the three intArithDecideLeaf* variants.
func intArithDecideLeafWith(hyps []Term, prove proveFn) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		if isIntComparisonGoal(t) {
			if w, ok := intDecideCmp(prove, slices.Values(hyps), t); ok {
				return w
			}
			return nil
		}
		// Divisibility goal `int_divides(d, e)` — not a comparison atom, so route it
		// to the decider (intDividesGoal) directly and lift `⊢ P` to `⊢ P ⇔ ⊤`.
		if _, _, ok := MatchesIntDivides(t); ok {
			if pf, ok := prove(slices.Values(hyps), t); ok {
				return eqtIntro(pf)
			}
		}
		return nil
	}
}

// ── the unified deep+fixpoint rewrite ───────────────────────────────────────

// intMoveAcrossLeaf rewrites a comparison/equality atom carrying total
// subtraction/negation into its positive two-sided equivalent (subneg.go),
// so the identity-fold + decide leaves then act on a sub/neg-free atom. nil on a
// positive atom (no-op) — so it neither loops nor preempts the existing path.
func intMoveAcrossLeaf(t Term) *prop.PropWrapper { return intSubneg.moveAcrossCmp(t) }

// IntArithDecideWithHyps is the PUBLIC entry — pre-simp + decider + bridge-back.
// Recursive internal callers (intElimEqHyps / imageBranchImp / intCondPin /
// intProveBoundedEnum) MUST instead use intArithDecideWithHypsRaw: pre-simp can
// fold an augmented hyp like `&0·y=&0` to ⊤, which preserves provability but
// breaks identity-keyed termination invariants downstream (e.g. intElimEqHyps'
// `slices.ContainsFunc(hyps, hSub.AlphaEquals)` check, which loops forever once
// the hyp it just added is folded out of recognition by the next recursion's
// pre-simp).
func IntArithDecideWithHyps(hyps []Term) prop.Rewrite {
	hypFreeSimp := prop.BasicRewritesWith(intArithSimpStep)
	simplifiedHyps, bridges := preSimpHyps(hyps, hypFreeSimp)
	raw := withCompoundEqSubst(hyps, intComposeArithLeaves(simplifiedHyps, intArithBoolLeaf))
	return func(t Term) *prop.PropWrapper {
		w := raw(t)
		if w == nil {
			return nil
		}
		return bridgeBackHyps(w, bridges)
	}
}

// IntArithDecideWithHypsWithPolicy is the policy-gated twin of
// IntArithDecideWithHyps: identical when the caller's lexical policy allows the
// int bundle, a rewrite that always declines when it does not — mirroring how
// NewArithCtxWithPolicy drops the int leaves under !policy.Int. The words
// channels delegate through this entry under the CALLER's ArithPolicy, so a
// word-goal lowering cannot become a laundering path for an int bundle the
// current target's policy forbids; the ungated original remains for legacy and
// low-level callers that own no scope.
func IntArithDecideWithHypsWithPolicy(hyps []Term, policy ArithPolicy) prop.Rewrite {
	if !policy.Int {
		return func(Term) *prop.PropWrapper { return nil }
	}
	return IntArithDecideWithHyps(hyps)
}

// intArithDecideWithHypsRaw is IntArithDecideWithHyps WITHOUT the hyp pre-simp
// pass, for recursive INTERNAL callers that augment the hyp set and rely on the
// added hyps' shape surviving roundtrip (intElimEqHyps Gaussian cut, the image
// sign-split's `x=±&n0` pin, the COND-pin handlers). Each of these grows hyps
// by an explicit derived hyp whose AlphaEquals identity is the recursion guard;
// pre-simp could fold the added hyp into a different shape (or ⊤) and break
// the guard, looping forever. Public entries (IntArithDecideWithHyps and the
// engine `arith` move via the unified path) still pre-simp — that's where the
// abs/sgn / pow / numeral folds on caller hyps are wanted.
func intArithDecideWithHypsRaw(hyps []Term) prop.Rewrite {
	return intComposeArithLeaves(hyps, intArithBoolLeaf)
}

// intArithDecideWithHypsRawBranch is the BRANCH raw entry (no pre-simp + no
// sign-split fallback + no Gaussian elimination + no bool-split leaf). Used
// as the branch sub-prover by case-split-style handlers (today:
// imageBranchImp and intElimEqHyps), so a branch can't recursively re-enter
// the case-split machinery — intImageSplit / intProveBoundedEnum /
// intElimEqHyps — and loop, as it would on `sgn(x·y) = sgn x · sgn y` or
// `q ∣ m ⊢ m − int_div(m,q)·q = &0`: one structural boundary in place of
// per-call-site reentry guards.
//
// Two exclusions keep the int decide terminating:
//
//   - intArithBoolLeaf, for the same termination reason documented at
//     intArithCollapseRewrite: intElimEqHyps is reachable from INSIDE an
//     ongoing bool split (intProveBoolBranch → intProveDecAtomNoSignSplit →
//     intElimEqHyps), and a bool leaf here would re-fire intProveBoolGoal on
//     the same boolean subterm with `done` reset to nil — under hyps grown by
//     fresh ν-var pins that defeat every identity-keyed guard. (A bool-split
//     branch does not enter intImageSplit at all: it runs the NoSignSplit
//     decider on both its legs, the branch discipline this function
//     documents, so the image split's own branch prover is reached only from
//     the decider a bool split sits OUTSIDE of.)
//   - intElimEqHyps (via intProveDecAtomBranch): its recursion guard is
//     identity-keyed on the current hyp slice, which a nested self-reentry
//     extends every level, so un-gated it self-recurses with monotonically
//     growing hyps. (A single "non-reentrant" elim-eq level in image branches
//     is no alternative: crossed with the bool split's EM branches it
//     re-opens a combinatorial space in which the sibling-normalized shape
//     `∀x d y. ∃z. (x ≠ −(d·y)) ∨ (x = d·z)` does not finish.)
//
// A branch that still needs boolean case analysis or a Gaussian cut gets it
// from the CALLER's machinery, never from its own sub-decider.
func intArithDecideWithHypsRawBranch(hyps []Term) prop.Rewrite {
	return intComposeArithLeavesBranch(hyps)
}

// intArithCollapseRewrite is IntArithDecideWithHyps MINUS intArithBoolLeaf: the
// deep atom-decision + bool-simplification used INSIDE the formula-level case
// split to collapse a branch's formula under its new atom-hypothesis
// (int_split.go). Excluding the bool leaf here is load-bearing — it stops the
// split recursion from re-entering itself with a fresh (empty) `done`, which
// would defeat termination. Also raw (no pre-simp), for the same termination
// reason as intArithDecideWithHypsRaw. The int twin of arithCollapseRewrite.
func intArithCollapseRewrite(hyps []Term) prop.Rewrite { return intComposeArithLeaves(hyps) }

// intArithCollapseRewriteNoSignSplit is intArithCollapseRewrite over the
// NoSignSplit decide leaf — the collapse a bool-split BRANCH runs
// (intProveBoolBranch), which must not re-enter the case-split handlers from
// inside a case split.
func intArithCollapseRewriteNoSignSplit(hyps []Term) prop.Rewrite {
	return intComposeArithLeavesWith(hyps, intArithDecideLeafNoSignSplit)
}

// intComposeArithLeaves builds the int deep+fixpoint rewrite from the standard
// basic rewrites plus the int arith leaves, optionally extended with `extraCtors`
// trailing-leaf constructors (intArithBoolLeaf for the full decider; none for
// the in-branch collapse). The int twin of composeArithLeaves.
//
// RAW: this function does NOT pre-simp hyps. Pre-simp is layered above it in
// IntArithDecideWithHyps only. Recursive internal callers wire to either this
// (via intArithDecideWithHypsRaw or intArithCollapseRewrite) so an augmented
// hyp's AlphaEquals identity survives the recursion.
//
// `extraCtors` are CONSTRUCTORS over the hyp set rather than already-built
// leaves, so an extra leaf binds the SAME hyps the inner stack sees —
// otherwise the bool-split's hyps and the decide-leaf's hyps could disagree
// after a wrapping pre-simp layer, breaking the IsStronger contract.
func intComposeArithLeaves(hyps []Term, extraCtors ...func([]Term) prop.Rewrite) prop.Rewrite {
	return intComposeArithLeavesWith(hyps, intArithDecideLeaf, extraCtors...)
}

// intComposeArithLeavesBranch is the branch-prover compose: uses
// intArithDecideLeafBranch instead of intArithDecideLeaf, so the leaf's atom
// decider recurses into neither intImageSplit / intProveBoundedEnum nor
// intElimEqHyps.
func intComposeArithLeavesBranch(hyps []Term, extraCtors ...func([]Term) prop.Rewrite) prop.Rewrite {
	return intComposeArithLeavesWith(hyps, intArithDecideLeafBranch, extraCtors...)
}

// intComposeArithLeavesWith builds the int deep+fixpoint rewrite with the
// given atom-decide-leaf constructor. Shared body of intComposeArithLeaves /
// intComposeArithLeavesBranch.
func intComposeArithLeavesWith(hyps []Term, decideLeaf func([]Term) prop.Rewrite,
	extraCtors ...func([]Term) prop.Rewrite) prop.Rewrite {
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hyps, pred) }
	// The COND leaf is the unified stack's (composeArithLeaves): a guard
	// that is a hyp, or whose negation is, selects its arm.
	leaves := []prop.Rewrite{
		eqHypSubst(hyps, isIntTerm, ArithPolicy{Int: true}), intCoeffEqSubst(hyps), prop.CondDecideByHyps(anyHyp),
		intArithSimpStep, intMoveAcrossLeaf, decideLeaf(hyps),
	}
	for _, ctor := range extraCtors {
		leaves = append(leaves, ctor(hyps))
	}
	return prop.BasicRewritesWithEnv(anyHyp, leaves...)
}

// IntArithDecide is the hyp-free entry point. Returns `⊢ t = t'`, or nil.
func IntArithDecide(t Term) *prop.PropWrapper { return IntArithDecideWithHyps(nil)(t) }

// IntArithEnabled reports whether int arith dispatch is live — i.e. an int
// bundle is installed (the engine's arith shape gate ANDs it with
// IsIntArithContent, so the move is never offered and then declined).
func IntArithEnabled() bool { return intLemmaBundle != nil }

// IsIntArithContent reports whether s is int-arith content the unified decider's
// int leaves can act on — an int `+`/`*` subterm or an int comparison atom.
// Structural only (no bundle check); the engine pairs it with
// IntArithEnabled. The ℤ analogue of IsRealArithContent.
func IsIntArithContent(s Term) bool {
	if _, _, ok := intDomain.matchPlus(s); ok {
		return true
	}
	if _, _, ok := intDomain.matchStar(s); ok {
		return true
	}
	return isIntComparisonGoal(s)
}

// Bounded-variable enumeration over the `int` type — the int twin of nat_exp.go,
// adapted to ℤ's lack of a default lower bound. When a goal atom is NONLINEAR in
// a variable x (so linarith/the case split decline) but the hypotheses bound x by
// two concrete literals `&a ≤ x` and `x ≤ &b` (a ≤ b, b−a ≤ enumMax), the atom is
// decided by ENUMERATION: build the finite disjunction `(x=&a) ∨ … ∨ (x=&b)`,
// substitute each value into the goal (intEqHypSubst makes the opaque atom
// literal, the int literal simps evaluate it), and recombine via ByCasesRecursive.
//
// Two ℤ-specific differences from the num enum: int has no implicit `0 ≤ x`, so a
// SINGLE upper bound is not enough — a two-sided literal range is required; and
// there is no suc, so the value disjunction is not built by the num's
// LessEqSplit/LessThanSucIffLessEq peel but is PROVED from the two bound hyps by the int bool-split
// (intProveBoolGoal) — a valid QF-linear formula it closes by case analysis +
// ℤ-discreteness. Everything else (proveAtValue, ByCasesRecursive recombination)
// mirrors the num enum. It lives entirely inside the forward prover, as the last
// fallback in intProveDecAtom.
//
// Only NON-NEGATIVE literal bounds are recognized (an int literal is `int_of_num
// n`, n ≥ 0); a negative bound `int_neg(&k) ≤ x` is not matched. Placeholder-
// backed; the per-value proofs use only the existing int simp/eval leaves.

// intProveBoundedEnum tries `{hyps} ⊢ goal` for a goal nonlinear in a variable x
// that the hyps bound by a two-sided literal range, by enumerating x's values.
func intProveBoundedEnum(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	x, a, b, ok := firstIntEnumBound(hyps, goal)
	if !ok {
		return nil, false
	}
	var eqs []Term
	for v := a; v.cmp(b) <= 0; v = v.add(integerOne) {
		eqs = append(eqs, eqT(x, intLitOf(v)))
	}
	// The value disjunction `(x=&a) ∨ … ∨ (x=&b)`, proved from the two bound hyps
	// by the int bool-split (it is QF-linear-valid: a≤x≤b pins x to one of the
	// b−a+1 integers). Left-nested to match ByCasesRecursive's expected shape.
	disjGoal := leftNestedOr(eqs)
	disj, ok := intProveBoolGoal(hyps, disjGoal, nil) // {hyps'} ⊢ (x=&a) ∨ … ∨ (x=&b)
	if !ok {
		return nil, false
	}

	imps := make([]*prop.PropWrapper, 0, len(eqs))
	for _, eqv := range eqs {
		gv, ok := proveAtIntValue(hyps, goal, eqv)
		if !ok {
			return nil, false // this value doesn't close — enumeration fails.
		}
		imps = append(imps, gv) // {hyps} ⊢ (x=v) ⇒ goal
	}
	res := prop.ByCasesRecursive(goal, eqs...).DeriveHypFrom(disj)
	for _, imp := range imps {
		res = res.DeriveHypFrom(imp)
	}
	return res, true
}

// proveAtIntValue proves `{hyps} ⊢ (x=v) ⇒ goal` by routing the goal through the
// full int decision rewrite with x pinned to the literal v: intEqHypSubst
// substitutes x→v, the literal simps evaluate the now-ground opaque atom, and the
// comparison decides. The int twin of proveAtValue (PromoteHyp'd to the
// implication form ByCasesRecursive wants).
func proveAtIntValue(hyps []Term, goal, eqv Term) (*prop.PropWrapper, bool) {
	// Raw (no pre-simp): the augmented pin `eqv = (x=v)` must roundtrip
	// shape-intact; pre-simp could fold it (e.g. `x=&0` rewrites `x·x=&0` in
	// other hyps to ⊤ and breaks downstream termination — see
	// intArithDecideWithHypsRaw).
	w := intArithDecideWithHypsRaw(append(slices.Clone(hyps), eqv))(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		return nil, false
	}
	return iffTrueElim(w).PromoteHyp(eqv), true // {hyps} ⊢ (x=v) ⇒ goal
}

// firstIntEnumBound finds the first free int variable x of `goal` with BOTH a
// literal lower bound `&a ≤ x` and a literal upper bound `x ≤ &b` among the hyps,
// with a ≤ b and b−a ≤ enumMax. ok=false when no such two-sided range exists.
//
// Gated on `goal` having a NONLINEAR side (intGoalHasNonlinearSide): a fully
// linear goal is linarith's job, and enumerating it would loop — each per-value
// branch proves a LINEAR residual (`x = &v`) whose own decision would re-enter
// enumeration on the same x before the substitution lands (the int twin of the
// num enum's `!ComparisonSidesLinear` + `!hasEqHyp` guards).
func firstIntEnumBound(hyps []Term, goal Term) (x Term, a, b _Integer, ok bool) {
	if !intGoalHasNonlinearSide(goal) {
		return nil, _Integer{}, _Integer{}, false
	}
	for _, v := range freeIntVars(goal) {
		if hasEqHyp(v, hyps) {
			continue // an `x = e` hyp is handled by intEqHypSubst; enumerating loops.
		}
		lo, gotLo := _Integer{}, false
		hi, gotHi := _Integer{}, false
		for _, h := range hyps {
			l, r, m := intDomain.matchLe(h)
			if !m {
				continue
			}
			if isVar(r) && r.AlphaEquals(v) { // &a ≤ v
				if n, shaped, k := intDomain.asLiteral(l); shaped && k {
					lo, gotLo = n, true
				}
			}
			if isVar(l) && l.AlphaEquals(v) { // v ≤ &b
				if n, shaped, k := intDomain.asLiteral(r); shaped && k {
					hi, gotHi = n, true
				}
			}
		}
		if gotLo && gotHi && lo.cmp(hi) <= 0 && hi.sub(lo).cmp(integerOfUint(enumMax)) <= 0 {
			return v, lo, hi, true
		}
	}
	return nil, _Integer{}, _Integer{}, false
}

// intGoalHasNonlinearSide reports whether `goal` is an int comparison/equality
// with a side that is NOT genuinely linear over int — a product atom on it,
// which linarith reads as one unknown it cannot relate to the factors' bounds
// (the only case worth enumerating). The int twin of the num
// `!ComparisonSidesLinear` gate.
func intGoalHasNonlinearSide(goal Term) bool {
	var l, r Term
	switch {
	case match2(intDomain.matchLt, goal, &l, &r):
	case match2(intDomain.matchLe, goal, &l, &r):
	case match2(intDomain.matchGt, goal, &l, &r):
	case match2(intDomain.matchGe, goal, &l, &r):
	default:
		e := goal
		if inner := ext.MatchesNOT(goal); inner != nil {
			e = inner
		}
		a, b, ok := ext.MatchesEQ(e)
		if !ok || !isIntTerm(a) {
			return false
		}
		l, r = a, b
	}
	return !intDomain.genuinelyLinear(l) || !intDomain.genuinelyLinear(r)
}

// leftNestedOr builds `((e0 ∨ e1) ∨ …) ∨ eₙ` (the foldl shape ByCasesRecursive
// and enumLeDisj both use). Panics on an empty slice (callers pass ≥ 1).
func leftNestedOr(es []Term) Term {
	res := es[0]
	for _, e := range es[1:] {
		res = or(res, e)
	}
	return res
}

// freeIntVars collects the distinct free int variables of t. Mirror of freeNumVars.
func freeIntVars(t Term) []Term {
	return collectRawSubterms([]Term{t}, func(s Term) bool { return isVar(s) && isIntTerm(s) })
}

// ── Coefficient-equality solve→substitute (the SAT dual of the GCD-eq test) ────
//
// `intEqHypSubst` only substitutes a hyp `v = e` whose LHS is a BARE variable, so
// `2·x = &4` is invisible to it (the linear core uses it as two inequalities, but
// it never reaches INSIDE an opaque atom like `x·x`). intCoeffEqSubst closes that
// gap: a hyp `c·x = k` with an int variable x, literal c ≥ 2 and k, and c ∣ k, is
// SOLVED to the bare-variable form `x = &(k/c)`, then handed to the same
// deep-rewrite substitution path so `x` folds inside opaque atoms.
//
// The solve is the SAT counterpart of the GCD-equality test: `c·x = k` with c ∤ k
// is integer-UNSAT (intGroundedGcdEq refutes it), while c ∣ k pins x to the unique
// integer k/c — and that `c·x = k ⊢ x = &(k/c)` is itself proved by IntLinProve
// (discreteness squeezes the single ℚ-point from both sides, e.g. `2·x = &4 ⊢
// x = &2`). So this is a forward enrichment built on discreteness, no division.
// The substituted `x → &(k/c)` is ground, so termination is immediate (like the
// literal case of intEqHypSubst).
func intCoeffEqSubst(hyps []Term) prop.Rewrite {
	type sub struct {
		from Term
		eq   *prop.PropWrapper
	}
	var subs []sub
	for _, h := range hyps {
		if v, eq, ok := intSolveCoeffEq(h); ok {
			subs = append(subs, sub{v, eq})
		}
	}
	if len(subs) == 0 {
		return func(Term) *prop.PropWrapper { return nil }
	}
	return func(s Term) *prop.PropWrapper {
		for _, sb := range subs {
			if s.AlphaEquals(sb.from) {
				return sb.eq // ⊢ x = &(k/c), carrying {c·x = k}
			}
		}
		return nil
	}
}

// intSolveCoeffEq detects a hyp `c·x = k` (int variable x, literal c ≥ 2 and k,
// c ∣ k) and returns the solved substitution `x → &(k/c)` with its proof
// `{h} ⊢ x = &(k/c)` (derived by IntLinProve — discreteness pins the single
// integer point). ok=false otherwise. (c = 1, the bare `x = k` shape, is left to
// intEqHypSubst; c ∤ k is integer-unsat and handled by the GCD-equality test.)
func intSolveCoeffEq(h Term) (v Term, eq *prop.PropWrapper, ok bool) {
	a, b, m := ext.MatchesEQ(h)
	if !m || !isIntTerm(a) {
		return nil, nil, false
	}
	x, c, k, mok := matchIntCoeffLiteral(a, b)
	if !mok {
		x, c, k, mok = matchIntCoeffLiteral(b, a)
	}
	if !mok || c.cmp(integerOf(2)) < 0 {
		return nil, nil, false
	}
	quotient, remainder := k.divMod(c)
	if !remainder.isZero() {
		return nil, nil, false
	}
	proof, pok := IntLinProve(slices.Values([]Term{h}), eqT(x, intLitOf(quotient)))
	if !pok {
		return nil, nil, false
	}
	return x, proof, true
}

// matchIntCoeffLiteral matches `litSide = k` (a numeral) and `monoSide = c·x` (a
// single coeff·variable monomial), returning (x, c, k). The variable must be bare
// (a nonlinear product is rejected by linOf, so any monomial here has a var atom).
func matchIntCoeffLiteral(litSide, monoSide Term) (x Term, c, k _Integer, ok bool) {
	lk, shaped, kok := intDomain.asLiteral(litSide)
	if !shaped || !kok {
		return nil, _Integer{}, _Integer{}, false
	}
	lf, lok := intDomain.linOf(monoSide)
	if !lok || !lf.konst.isZero() || len(lf.monos) != 1 || !isVar(lf.monos[0].atom) {
		return nil, _Integer{}, _Integer{}, false
	}
	return lf.monos[0].atom, lf.monos[0].coeff, lk, true
}

// The Image sign split. Every int is ±a-nat (Image: ∀x. ∃n. x=−&n ∨ x=&n),
// so a goal whose validity is sign-dependent — `&0 ≤ x·x` (SquareNonneg) — is
// decided by splitting a bare int variable x on its sign, feeding `x = ±&n` to the
// int_of_num collapse: each branch becomes `&0 ≤ (±&n)·(±&n)` →
// `&(n·n)` → the num `0 ≤ n·n`, which num's default-nonneg closes.
//
// The existential needs ∃-elimination: the ε-witness `εn.(x=…)` mentions x, so it cannot
// be substituted into the goal (occurs check). Instead the branches are proved
// under a FRESH num var n₀ (so the eq-subst x→±&n₀ is valid), recombined to
// `{D[n₀]} ⊢ goal`, then n₀ is instantiated to the ε-witness ONLY in that hyp and
// the existence claim discharges it (`selected.DeriveTrans`). Reuses the full int
// decider for the branches (eq-subst + the of_num collapse) and prop.ByCases for
// the disjunction.

// intImageSplit decides `{hyps} ⊢ goal` by an Image sign split on a bare int
// variable occurring nonlinearly in the goal. ok=false when no such variable
// exists, it is already pinned by an equality hyp (the recursion guard), or a
// branch does not close.
func intImageSplit(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	x, ok := pickIntSquareVar(goal)
	if !ok || pinnedByHyp(x, hyps) {
		return nil, false
	}
	n0 := freshNumVar(append(slices.Clone(hyps), goal))
	ampN0 := intOfNumT(n0)
	gNeg := eqT(x, intNegT(ampN0)) // x = −&n0
	gPos := eqT(x, ampN0)          // x = &n0
	D := or(gNeg, gPos)
	existsStmt := prop.Exists(n0)(D) // ∃n0. (x=−&n0 ∨ x=&n0)

	// ⊢ ∃n0. D — Image instantiated at x (placeholder-backed when bundle-nil).
	th1 := intImplyLeaf(intImageThm(), []Term{x}, existsStmt)

	// Branch implications {hyps} ⊢ (x=±&n0) ⇒ goal, via the full decider.
	imp0, ok0 := imageBranchImp(hyps, gNeg, goal)
	imp1, ok1 := imageBranchImp(hyps, gPos, goal)
	if !ok0 || !ok1 {
		return nil, false
	}
	// {hyps, D} ⊢ goal — D supplied as a hyp (Assume); ByCases recombines.
	th2 := prop.ByCases(goal, gNeg, gPos).
		DeriveHypFrom(prop.Assume(D)).
		DeriveHypFrom(imp0).
		DeriveHypFrom(imp1)

	// ∃-elimination: discharge D against the existence claim.
	return chooseElim(th1, n0, D, th2), true
}

// imageBranchImp proves {hyps} ⊢ (eqFact ⇒ goal) by closing the branch under
// the added equality hyp with the branch int decider (its eq-subst leaf
// rewrites x to ±&n0, then the of_num collapse closes), then promoting eqFact
// to an implication. The branch sub-prover is the BRANCH variant — a branch
// can't recursively re-enter intImageSplit / intProveBoundedEnum /
// intElimEqHyps / intArithBoolLeaf, so the recursion is bounded structurally
// rather than by per-call-site ad-hoc guards. ok=false if the branch does not
// collapse to ⊤.
func imageBranchImp(hyps []Term, eqFact, goal Term) (*prop.PropWrapper, bool) {
	bh := append(slices.Clone(hyps), eqFact)
	// Raw (no pre-simp): pinnedByHyp matches the literal `x=±&n0` shape — see
	// intArithDecideWithHypsRaw. Branch: keeps the branch from re-entering
	// the case-split machinery, where it would not terminate.
	w := intArithDecideWithHypsRawBranch(bh)(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		return nil, false
	}
	return iffTrueElim(w).PromoteHyp(eqFact), true // {hyps} ⊢ eqFact ⇒ goal
}

// pickIntSquareVar returns an int variable occurring in a NONLINEAR product
// (int_mul of two non-literal factors) anywhere in goal — the shape a sign
// split can help (`x·x`, `x·y`). ok=false if none.
//
// No wrapper guard needed: imageBranchImp's branch sub-decider is the
// restricted (no-sign-split) variant, so a fruitless sign-split inside
// sgn/abs/int_div/int_rem returns nil quickly via the bounded sub-decider instead of
// looping. The recursion termination is structural rather than per-shape.
func pickIntSquareVar(goal Term) (Term, bool) {
	muls := collectRawSubterms([]Term{goal}, func(t Term) bool {
		l, r, ok := intDomain.matchStar(t)
		if !ok {
			return false
		}
		_, _, okL := intDomain.asLiteral(l)
		_, _, okR := intDomain.asLiteral(r)
		return !okL && !okR // nonlinear: neither factor a literal coefficient
	})
	for _, s := range muls {
		vars := collectRawSubterms([]Term{s}, func(t Term) bool { return isVar(t) && isIntTerm(t) })
		if len(vars) > 0 {
			return vars[0], true
		}
	}
	return nil, false
}

// pinnedByHyp reports whether some hyp is `x = e` or `e = x` (x already resolved),
// the guard that stops a branch's added `x = ±&n0` from re-triggering the split.
func pinnedByHyp(x Term, hyps []Term) bool {
	for _, h := range hyps {
		if a, b, ok := ext.MatchesEQ(h); ok && (a.AlphaEquals(x) || b.AlphaEquals(x)) {
			return true
		}
	}
	return false
}

// The int_of_num homomorphism collapse. An int term all of whose leaves are
// `&`-coerced nums (int_of_num), combined by int_neg / int_mul / same-sign
// int_add, reduces to a SIGNED num image `±&(num expr)`. This is the int twin of
// the real of_num lift, generalized past literals to arbitrary num args: the
// homomorphism OfNumAdd/OfNumMul run as proof-producing REWRITES (not numeral
// evaluation), with the sign tracked through MulRightNeg / NegNeg.
//
// It closes goals the linear core and the full ring both miss, because `&n` (n a
// num VARIABLE) is linarith-opaque AND int atoms carry no default ≥0 bound:
//   - `&n·&n = &(n·n)` — the homomorphism itself (IntRingProveFull atomizes `&n`,
//     so it can't see this);
//   - `&0 ≤ &n·&n` — drop to the num `0 ≤ n·n`, which num's default-nonneg closes.
// With the Image sign split (int_split.go) feeding `x = ±&n`, it closes
// `&0 ≤ x·x` (SquareNonneg).
//
// Sign-mixed int_add is out of scope: num has no subtraction, so `&a + (−&b)`
// declines (the signed normalizer's linear job, not this).

// Notation in the comments below: `signWrap(neg, x)` denotes −x when neg, else
// x. Used purely as a symbolic shorthand — the actual term construction inlines
// to intNegT(x) / x at each call site.

// liftUnderSign lifts ⊢ A = B to ⊢ signWrap(neg,A) = signWrap(neg,B).
func liftUnderSign(neg bool, w *prop.PropWrapper) *prop.PropWrapper {
	if neg {
		return w.LeftApply(intNeg)
	}
	return w
}

// intOfNumNormalize reduces t to (neg, u, ⊢ t = signWrap(neg, &u)), u a num term,
// when every leaf is int_of_num and the structure is int_neg / int_mul /
// same-sign int_add. ok=false otherwise (t is left for the other leaves).
func intOfNumNormalize(t Term) (neg bool, u Term, w *prop.PropWrapper, ok bool) {
	if m, isOfNum := MatchesIntOfNum(t); isOfNum {
		return false, m, prop.Refl(t), true // &m = signWrap(false, &m)
	}
	if a, isNeg := MatchesIntNeg(t); isNeg {
		na, ua, wa, okA := intOfNumNormalize(a)
		if !okA {
			return false, nil, nil, false
		}
		inner := wa.LeftApply(intNeg) // ⊢ int_neg(a) = int_neg(signWrap(na, &ua))
		if !na {                      // a = &ua ⇒ int_neg(a) = signWrap(true, &ua)
			return true, ua, inner, true
		}
		// na: a = −&ua ⇒ int_neg(a) = −(−&ua) = &ua  (NegNeg)
		nn := intNegNegLeaf(intOfNumT(ua)) // ⊢ −(−&ua) = &ua
		return false, ua, inner.EqTrans(nn), true
	}
	if l, r, isMul := intDomain.matchStar(t); isMul {
		nl, ul, wl, okl := intOfNumNormalize(l)
		nr, ur, wr, okr := intOfNumNormalize(r)
		if !okl || !okr {
			return false, nil, nil, false
		}
		lu, ru := intOfNumT(ul), intOfNumT(ur)
		cong := wl.LeftApply(intStar).Apply(wr) // ⊢ l·r = signWrap(nl,&ul)·signWrap(nr,&ur)
		sx, resNeg := intMulSignExtract(nl, lu, nr, ru)
		bridge := intOfNumMulLeaf(ul, ur)       // ⊢ &ul·&ur = &(ul·ur)
		lifted := liftUnderSign(resNeg, bridge) // under the result sign
		return resNeg, star(ul, ur), cong.EqTrans(sx).EqTrans(lifted), true
	}
	if l, r, isAdd := intDomain.matchPlus(t); isAdd {
		nl, ul, wl, okl := intOfNumNormalize(l)
		nr, ur, wr, okr := intOfNumNormalize(r)
		if !okl || !okr || nl != nr {
			return false, nil, nil, false // sign-mixed add = subtraction: decline
		}
		lu, ru := intOfNumT(ul), intOfNumT(ur)
		cong := wl.LeftApply(intPlus).Apply(wr) // ⊢ l+r = signWrap(nl,&ul)+signWrap(nr,&ur)
		bridge := intOfNumAddLeaf(ul, ur)       // ⊢ &ul+&ur = &(ul+ur)
		if !nl {
			return false, plus(ul, ur), cong.EqTrans(bridge), true
		}
		// both neg: (−&ul)+(−&ur) = −(&ul+&ur) [NegAdd, reversed] = −&(ul+ur)
		negAdd := intNegAddLeaf(lu, ru).EqSym() // ⊢ (−&ul)+(−&ur) = −(&ul+&ur)
		lifted := bridge.LeftApply(intNeg)      // ⊢ −(&ul+&ur) = −&(ul+ur)
		return true, plus(ul, ur), cong.EqTrans(negAdd).EqTrans(lifted), true
	}
	return false, nil, nil, false
}

// intMulSignExtract proves ⊢ signWrap(nl,lu)·signWrap(nr,ru) = signWrap(nl⊕nr, lu·ru),
// pushing the negations out of a product via MulRightNeg (+ its derived left-factor twin, NegNeg).
func intMulSignExtract(nl bool, lu Term, nr bool, ru Term) (*prop.PropWrapper, bool) {
	switch {
	case !nl && !nr: // lu·ru
		return prop.Refl(intStarT(lu, ru)), false
	case !nl && nr: // lu·(−ru) = −(lu·ru)
		return intMulRightNegLeaf(lu, ru), true
	case nl && !nr: // (−lu)·ru = −(lu·ru)
		return intMulLnegProof(lu, ru), true
	default: // (−lu)·(−ru) = lu·ru
		step1 := intMulRightNegLeaf(intNegT(lu), ru)       // (−lu)·(−ru) = −((−lu)·ru)
		step2 := intMulLnegProof(lu, ru).LeftApply(intNeg) // −((−lu)·ru) = −(−(lu·ru))
		step3 := intNegNegLeaf(intStarT(lu, ru))           // −(−(lu·ru)) = lu·ru
		return step1.EqTrans(step2).EqTrans(step3), false
	}
}

// intMulLnegProof: ⊢ (−a)·b = −(a·b), derived (the bundle carries only the
// MulRightNeg form): (−a)·b = b·(−a) [MulSym] = −(b·a) [MulRightNeg] = −(a·b) [MulSym under neg].
func intMulLnegProof(a, b Term) *prop.PropWrapper {
	return intCommuteMUL(intNegT(a), b). // (−a)·b = b·(−a)
						EqTrans(intMulRightNegLeaf(b, a)).             // = −(b·a)
						EqTrans(intCommuteMUL(b, a).LeftApply(intNeg)) // = −(a·b)
}

// ── leaf builders (bundle-thm instantiations, placeholder-backed) ─────────────

// intNegNegLeaf: ⊢ −(−x) = x   (NegNeg).
func intNegNegLeaf(x Term) *prop.PropWrapper {
	return intEqLeaf(intNegNegThm(), []Term{x}, intNegT(intNegT(x)), x)
}

// intMulRightNegLeaf: ⊢ a·(−b) = −(a·b)   (MulRightNeg).
func intMulRightNegLeaf(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intMulRightNegThm(), []Term{a, b}, intStarT(a, intNegT(b)), intNegT(intStarT(a, b)))
}

// intNegAddLeaf: ⊢ −(a+b) = (−a)+(−b)   (NegAdd).
func intNegAddLeaf(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intNegAddThm(), []Term{a, b}, intNegT(intPlusT(a, b)), intPlusT(intNegT(a), intNegT(b)))
}

// intOfNumMulLeaf: ⊢ &a·&b = &(a·b)   (OfNumMul, the homomorphism).
func intOfNumMulLeaf(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intOfNumMulThm(), []Term{a, b}, intStarT(intOfNumT(a), intOfNumT(b)), intOfNumT(star(a, b)))
}

// intOfNumAddLeaf: ⊢ &a+&b = &(a+b)   (OfNumAdd).
func intOfNumAddLeaf(a, b Term) *prop.PropWrapper {
	return intEqLeaf(intOfNumAddThm(), []Term{a, b}, intPlusT(intOfNumT(a), intOfNumT(b)), intOfNumT(plus(a, b)))
}

// ── the decide hook ───────────────────────────────────────────────────────────

// intProveOfNum closes a comparison/equality goal whose sides are int_of_num
// images. For `=` both sides collapse to the same signed image (the of_num twin
// of IntRingProveFull). For `≤`/`<` both sides must be NONNEGATIVE images, which
// drop to the num goal `uL ⋈ uR` (OfNumLe/OfNumLt) closed by the num prover —
// `&0 ≤ &n·&n → 0 ≤ n·n`. Hyp-free, as realProveOfNum and for its reason: the
// num facts reach the rows through the cast (domain.go liftHyp). ok=false on
// any non-collapsing or negative-sided shape.
func intProveOfNum(goal Term) (*prop.PropWrapper, bool) {
	// Equality: collapse both sides; close if their signed images coincide,
	// else — both nonnegative — as the num equality under the num facts.
	if l, r, ok := ext.MatchesEQ(goal); ok && isIntTerm(l) {
		nl, _, wl, okl := intOfNumNormalize(l)
		nr, _, wr, okr := intOfNumNormalize(r)
		if !okl || !okr {
			return nil, false
		}
		if nl == nr && prop.Rhs(wl).AlphaEquals(prop.Rhs(wr)) {
			return wl.EqTrans(wr.EqSym()), true // ⊢ l = signWrap = r
		}
		if nl || nr {
			return nil, false
		}
		return intDropCmp(l, r, eqConstOf(l), eqT, intOfNumEqThm())
	}
	// `≤` / `<`: drop two nonnegative images to the num comparison.
	if l, r, ok := intDomain.matchLe(goal); ok {
		return intDropCmp(l, r, intLe, le, intOfNumLeThm())
	}
	if l, r, ok := intDomain.matchLt(goal); ok {
		return intDropCmp(l, r, intLt, lt, intOfNumLtThm())
	}
	return nil, false
}

// intLiftNumHyp is intDomain.liftHyp: realLiftNumHyp's twin through the
// OfNum* bridges.
func intLiftNumHyp(h Term) []*prop.PropWrapper {
	return liftNumHyp(h, intOfNumT, intLeT, intLtT, intOfNumLeThm, intOfNumLtThm, intOfNumEqThm, intEqLeaf,
		intOfNumAddLeaf, intOfNumMulLeaf)
}

// intDropCmp proves ⊢ (l ⋈ r) when l,r are NONNEGATIVE int_of_num images: collapse
// each to `&uL`,`&uR`, rewrite the relation, drop to the num goal `uL ⋈ uR` via the
// OfNum* bridge, and close it with the num prover. ok=false if a side is
// negative / non-collapsing or the num goal does not close.
func intDropCmp(l, r, relConst Term, numRel func(a, b Term) Term, bridgeThm *prop.PropWrapper) (*prop.PropWrapper, bool) {
	nl, ul, wl, okl := intOfNumNormalize(l)
	nr, ur, wr, okr := intOfNumNormalize(r)
	if !okl || !okr || nl || nr { // need both sides nonnegative
		return nil, false
	}
	numGoal := numRel(ul, ur)
	numW, ok := LinProve(slices.Values([]Term(nil)), numGoal) // ⊢ uL ⋈ uR  (num)
	if !ok {
		return nil, false
	}
	cong := wl.LeftApply(relConst).Apply(wr)                                // ⊢ (l ⋈ r) = (&uL ⋈ &uR)
	bridge := intEqLeaf(bridgeThm, []Term{ul, ur}, prop.Rhs(cong), numGoal) // ⊢ (&uL ⋈ &uR) ⇔ (uL ⋈ uR)
	return cong.EqTrans(bridge).EqSym().EqMP(numW), true                    // {hs'} ⊢ (l ⋈ r)
}

// Cross-hypothesis equality elimination — the Gaussian step the per-equation gcd
// test needs. The decide's eq-subst rewrites a variable in the GOAL using an
// equality hyp, but never rewrites one HYP into another; so two equalities sharing
// a variable (`x=2z₀`, `x+1=2w₀`, from skolemizing `2∣x ∧ 2∣(x+1)`) stay separate,
// and neither alone is gcd-unsat (each has coefficient gcd 1). intElimEqHyps closes
// that gap: an equality hyp `x = e` (x a variable not in e) derives the substituted
// copy `H[x:=e]` of another hyp H — proof-producing, via the equality — adds it as a
// fact, and re-decides, so the COMBINED `2z₀+1 = 2w₀` reaches the gcd test (gcd 2 ∤
// 1). General over equalities, not divisibility-specific: it is exactly the
// "cross-hyp rewrite" the goal-only eq-subst is not.
//
// Sound (every added fact is derived from real hyps) and terminating: each fire
// strictly removes the variable x from one hyp, and an already-present substituted
// copy is skipped, so the augmented system cannot grow unboundedly.
func intElimEqHyps(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	for _, eqHyp := range hyps {
		x, ok := intEqElimVar(eqHyp)
		if !ok {
			continue
		}
		rule := func(s Term) *prop.PropWrapper {
			if s.AlphaEquals(x) {
				return prop.Assume(eqHyp) // {x=e} ⊢ x = e  (x is the LHS)
			}
			return nil
		}
		// rule's leaves carry the single hyp eqHyp; without capture-aware
		// recursion, lifting through a binder whose bound var occurs free in
		// eqHyp trips PropAbs's `v ∉ FV(hyps)` side condition. See the
		// DeepRewriteWithEnv doc.
		anyHyp := func(pred func(Term) bool) bool { return pred(eqHyp) }
		deep := prop.DeepRewriteWithEnv(anyHyp, rule)
		for _, h := range hyps {
			if h.AlphaEquals(eqHyp) {
				continue
			}
			// Only combine into other EQUALITY hyps — the linear system the gcd test
			// reads. Rewriting an opaque predicate (e.g. `int_divides(d, x)`) would
			// just relocate x into a new divisibility that re-skolemizes; the Gaussian
			// step is about the equalities, not the predicates.
			if _, _, ok := ext.MatchesEQ(h); !ok {
				continue
			}
			congr := deep(h) // ⊢ h = h[x:=e], or nil if x ∉ h
			if congr == nil {
				continue
			}
			hSub := prop.Rhs(congr)
			if slices.ContainsFunc(hyps, hSub.AlphaEquals) {
				continue // already present — no progress
			}
			hSubProof := congr.EqMP(prop.Assume(h)) // {x=e, h} ⊢ h[x:=e]
			// Raw (no pre-simp): the ContainsFunc guard above is identity-keyed on
			// hSub's shape — pre-simp can fold hSub (e.g. `&0·y=&0` → ⊤) so the
			// next recursion never finds it and loops. See
			// intArithDecideWithHypsRaw.
			// Branch: intElimEqHyps is a case-split-style handler (Gaussian
			// cut), and the branch sub-prover of such a handler must NOT
			// re-enter intImageSplit / intProveBoundedEnum — that would
			// compound the cut with sign splits into expensive search
			// (the neutral element and monoid laws of ℤ's product) — NOR intElimEqHyps
			// itself: the ContainsFunc guard above is keyed on THIS hyps
			// slice, which a nested self-reentry extends every level (fresh
			// substituted copies), so an un-gated reentry self-recurses with
			// monotonically growing hyps and never converges.
			w := intArithDecideWithHypsRawBranch(append(slices.Clone(hyps), hSub))(goal)
			if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
				continue
			}
			wGoal := iffTrueElim(w) // {⊆ hyps + hSub} ⊢ goal
			// The branch witness need not have consumed the cut: the branch
			// decider's composed leaves (intEqHypSubst / intCoeffEqSubst) can
			// close the goal from the ORIGINAL hyps alone — e.g. eq-substituting
			// eqHyp itself into the goal — leaving hSub unused. Then wGoal is
			// already {⊆ hyps} ⊢ goal, and discharging the absent hyp would trip
			// DeriveTrans's strict hyp-membership assert
			// (TestIntElimEq_BranchWitnessWithoutCut). Discharge hSub only
			// when it is actually a hyp of the witness.
			if !wGoal.HasHyp(hSub) {
				return wGoal, true // {hyps} ⊢ goal — the cut went unused
			}
			return hSubProof.DeriveTrans(wGoal), true // {hyps} ⊢ goal
		}
	}
	return nil, false
}

// intEqElimVar returns the eliminable variable of an int equality hyp `x = e`: x is
// the LHS, an int variable not occurring in e (so the rewrite `x → e` strictly
// removes it). The skolemized divisibility equation `dividend = d·z₀` has exactly
// this shape. ok=false otherwise.
func intEqElimVar(h Term) (Term, bool) {
	l, r, isEq := ext.MatchesEQ(h)
	if !isEq || !isVar(l) || !isIntTerm(l) {
		return nil, false
	}
	if len(collectRawSubterms([]Term{r}, l.AlphaEquals)) > 0 {
		return nil, false // x occurs in e — not a clean elimination
	}
	return l, true
}

// int_divides: `int_divides d e ⇔ ∃z. e = d·z` (DividesDef). A divisibility GOAL
// is closed by an ∃-witness intro (z the syntactic quotient, or e/d for literals);
// a divisibility HYP is skolemized to a linear equation `e = d·z₀` (∃-elimination, via
// chooseElim), which the gcd-equality test then exploits — `int_divides(&2, &1)`
// is contradictory because `&1 = &2·z` is `2z = 1`, gcd 2 ∤ 1.
//
// A variable divisor is Cooper-territory; this is the bounded/literal fragment
// (the sub-Cooper sweet spot, the int twin of the num divides layer, nat_omega.go).

// intDividesDefIff: ⊢ (∃z. e = d·z) ⇔ int_divides(d, e) — DividesDef instantiated
// at d,e over the bound int var z (placeholder-backed when the bundle is nil).
func intDividesDefIff(d, e Term, z *ext.TermWrapper) (*prop.PropWrapper, Term) {
	existsStmt := prop.Exists(z)(eqT(e, intStarT(d, z)))
	iff := intImplyLeaf(intDividesDefThm(), []Term{d, e}, eqT(existsStmt, intDividesT(d, e)))
	return iff, existsStmt
}

// intDividesGoal proves a divisibility goal `int_divides(d, e)` by exhibiting a
// witness with ⊢ e = d·witness (the syntactic quotient `d·t`, or e/d for literals),
// ∃-introducing, and folding through the definition. ok=false otherwise.
func intDividesGoal(goal Term) (*prop.PropWrapper, bool) {
	d, e, ok := MatchesIntDivides(goal)
	if !ok {
		return nil, false
	}
	witness, wproof, ok := intDividesWitness(d, e)
	if !ok {
		return nil, false
	}
	z := freshVar([]Term{goal, witness}, dsl.IntType)
	iff, existsStmt := intDividesDefIff(d, e, z)
	intro := prop.InstExists(existsStmt, witness).DeriveHypFrom(wproof) // ⊢ ∃z. e=d·z
	return iff.EqMP(intro), true                                        // ⊢ int_divides(d, e)
}

// intDividesWitness finds a z and ⊢ e = d·z: the syntactic quotient when e is
// `d·t`, else e/d when d,e are nonnegative int literals with d ∣ e (the divisor
// nonzero). ok=false otherwise.
func intDividesWitness(d, e Term) (witness Term, proof *prop.PropWrapper, ok bool) {
	if l, r, ok := intDomain.matchStar(e); ok && l.AlphaEquals(d) {
		return r, prop.Refl(e), true // e = d·r exactly
	}
	dv, okd := intLitVal(d)
	ev, oke := intLitVal(e)
	if okd && oke && !dv.isZero() {
		if quotient, remainder := ev.divMod(dv); remainder.isZero() {
			t := intLitOf(quotient)
			if w, ok := IntRingProveFull(e, intStarT(d, t)); ok {
				return t, w, true // ⊢ e = d·(e/d)
			}
		}
	}
	return nil, nil, false
}

// intLitVal extracts a nonnegative int literal `&n`'s value.
func intLitVal(t Term) (_Integer, bool) {
	n, shaped, ok := intDomain.asLiteral(t)
	return n, shaped && ok
}

// intDividesSkolem decides `{hyps} ⊢ goal` when a divisibility HYP is contradictory
// (or otherwise drives the goal): skolemize one `int_divides(d, e)` hyp to a fresh
// linear equation `e = d·z₀`, prove the goal with it added (the gcd-equality test
// refutes a gcd-impossible one — `int_divides(&2,&1)` ⊢ anything), and discharge
// the existential (∃-elimination). Pin-guarded so the added equation does not re-trigger
// it. ok=false when no fresh divisibility hyp drives the goal.
func intDividesSkolem(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	// Collect every not-yet-skolemized divisibility hyp and skolemize them ALL in
	// one pass (fresh vars), so the discharge below is a flat fold of independent
	// CHOOSEs — NOT nested. (Nesting renames the inner ε-witness and breaks the
	// outer DeriveTrans; a flat fold keeps each ε first-order, like the single-hyp
	// case.) The combined linear equations then reach the gcd test via the
	// cross-hyp elimination.
	type sk struct {
		v       *ext.TermWrapper
		eqFact  Term
		exProof *prop.PropWrapper // {h} ⊢ ∃z. e=d·z
	}
	var sks []sk
	aug := slices.Clone(hyps)
	for _, h := range hyps {
		d, e, ok := MatchesIntDivides(h)
		if !ok || dividesSkolemized(d, e, aug) {
			continue
		}
		z := freshVar(append(slices.Clone(aug), goal), dsl.IntType)
		eqFact := eqT(e, intStarT(d, z)) // e = d·z
		iff, _ := intDividesDefIff(d, e, z)
		sks = append(sks, sk{z, eqFact, iff.EqSym().EqMP(prop.Assume(h))})
		aug = append(aug, eqFact)
	}
	if len(sks) == 0 {
		return nil, false
	}
	// Prove the goal once with every skolemized equation added. Raw (no pre-
	// simp): the skolemized `e = d·z` pins must roundtrip shape-intact — see
	// intArithDecideWithHypsRaw.
	w := intArithDecideWithHypsRaw(aug)(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		return nil, false
	}
	proof := iffTrueElim(w) // {hyps, eqFact₀, …} ⊢ goal
	// Discharge each existential (flat fold, last-skolemized first).
	for i := len(sks) - 1; i >= 0; i-- {
		proof = chooseElim(sks[i].exProof, sks[i].v, sks[i].eqFact, proof)
	}
	return proof, true
}

// dividesSkolemized reports whether some hyp is already `e = d·_` (the divisibility
// for (d,e) has been skolemized), the guard against re-skolemizing it.
func dividesSkolemized(d, e Term, hyps []Term) bool {
	for _, h := range hyps {
		a, b, ok := ext.MatchesEQ(h)
		if !ok || !a.AlphaEquals(e) {
			continue
		}
		if l, _, ok := intDomain.matchStar(b); ok && l.AlphaEquals(d) {
			return true
		}
	}
	return false
}

// Monotone scaling + sign-of-product — a sub-RCF fragment the linear core and the
// ⊤-only ring both miss. A goal with a product on a side is NONLINEAR, so linarith
// atomizes the product into an opaque atom and the Farkas scaling fires only on a
// LITERAL multiplier (intScale). This handler closes the SYMBOLIC cases by applying
// the monotonicity / product-sign lemmas directly, with the sign/order side
// conditions discharged from the hyps:
//
//   - monotone scaling: `a ⋈ b ∧ &0 ⋈′ c ⊢ c·a ⋈ c·b` via LessEqMulLeft / LessThanMulLeft
//     (the bundle's LessEqMulLeft/LessThanMulLeft); the `a·c`/`b·c` (right-factor)
//     orientation reduces to it by commuting (intCommuteMUL), so no right-factor leaf;
//   - sign-of-product: ALL four sign combinations of `&0 ⋈ x·y` and `x·y ⋈ &0` via
//     LessEqMul / MulPos. The negated-factor combos reduce to
//     these two on `(−·)` operands (negNegMul / negLmul / mulRightNeg push the negation
//     out), and the nonpositive target flips `&0 ⋈ −(x·y)` to `x·y ⋈ &0` through
//     hyp-side move-across (intProveSignedProduct);
//   - two-sided product bound: `&0≤a ∧ a≤b ∧ &0≤c ∧ c≤d ⊢ a·c ≤ b·d`,
//     DERIVED from two monotone scalings + transitivity, so no new bundle field
//     (intProveProductMul2).
//
// These are genuinely nonlinear but NOT full RCF: the inputs are sign/order facts,
// the output is a lemma instantiation. The side conditions discharge through the
// LINEAR forward prover (intLinProveSigned = IntLinProve + one move-across pass, so
// a negated goal like `&0 ≤ −x` positivizes) — never the full decider, which could
// recurse. Shared shape with ℝ/num (the lemmas lift), though this cut is wired for
// int. Out of it: the strict two-sided bound, and the genuine RCF `a≤b ⊢ a²≤b²`
// (no sign assumption on the factors).

// intProveMonotone tries `{hyps} ⊢ goal` for a `≤` / `<` goal whose sides are
// products (monotone scaling) or whose RHS is a product bounded below by &0
// (product nonnegativity). nil/false when the goal is not such a shape or a side
// condition does not discharge.
func intProveMonotone(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if l, r, ok := intDomain.matchLe(goal); ok {
		return intMonotoneAtom(hyps, l, r, false)
	}
	if l, r, ok := intDomain.matchLt(goal); ok {
		return intMonotoneAtom(hyps, l, r, true)
	}
	return nil, false
}

// intMonotoneAtom dispatches the (l ⋈ r) atom (strict selects </≤).
func intMonotoneAtom(hyps []Term, l, r Term, strict bool) (*prop.PropWrapper, bool) {
	// sign-of-product: &0 ⋈ x·y (nonneg/pos target) or x·y ⋈ &0 (nonpos/neg target).
	if isIntZero(l) {
		if x, y, ok := intDomain.matchStar(r); ok {
			if w, ok := intProveSignedProduct(hyps, x, y, true, strict); ok {
				return w, true
			}
		}
	}
	if isIntZero(r) {
		if x, y, ok := intDomain.matchStar(l); ok {
			if w, ok := intProveSignedProduct(hyps, x, y, false, strict); ok {
				return w, true
			}
		}
	}
	// monotone scaling: l, r both products sharing a factor — or one side a
	// product and the other its bare factor, read as that factor times &1.
	la, ra, okL := intDomain.matchStar(l)
	lb, rb, okR := intDomain.matchStar(r)
	switch {
	case okL && !okR:
		return intMonoScaleOne(hyps, la, ra, r, strict, true)
	case !okL && okR:
		return intMonoScaleOne(hyps, lb, rb, l, strict, false)
	case !okL && !okR:
		return nil, false
	}
	if la.AlphaEquals(lb) { // x·a ⋈ x·b — scale by the shared LEFT factor x = la.
		return intMonoScaleLeft(hyps, la, ra, rb, strict)
	}
	if ra.AlphaEquals(rb) { // a·x ⋈ b·x — scale by the shared RIGHT factor x = ra.
		return intMonoScaleRight(hyps, ra, la, lb, strict)
	}
	// two-sided a·c ≤ b·d (distinct factors), non-strict.
	if !strict {
		return intProveProductMul2(hyps, la, ra, lb, rb)
	}
	return nil, false
}

// intMonoScaleLeft proves `{hyps} ⊢ c·a ⋈ c·b` from `&0 ⋈′ c` and `a ⋈ b`
// (both discharged by IntLinProve) via LessEqMulLeft / LessThanMulLeft. nil/false when
// either side condition fails.
func intMonoScaleLeft(hyps []Term, c, a, b Term, strict bool) (*prop.PropWrapper, bool) {
	rel, thm := intLeT, intLessEqMulLeftThm()
	if strict {
		rel, thm = intLtT, intLessThanMulLeftThm()
	}
	sideRel := rel(intLit(0), c) // &0 ⋈ c
	side, ok := IntLinProve(slices.Values(hyps), sideRel)
	if !ok {
		return nil, false
	}
	relAB, ok := IntLinProve(slices.Values(hyps), rel(a, b)) // a ⋈ b
	if !ok {
		return nil, false
	}
	// LessEqMulLeft/LessThanMulLeft: ∀c a b. (&0 ⋈ c) ⇒ (a ⋈ b) ⇒ (c·a ⋈ c·b)
	// (binder [c, a, b], the intScale order).
	imp := intImplyLeaf(thm, []Term{c, a, b},
		imply(sideRel, imply(rel(a, b), rel(intStarT(c, a), intStarT(c, b)))))
	return mp(mp(imp, side), relAB), true // ⊢ c·a ⋈ c·b
}

// intMonoScaleRight proves `{hyps} ⊢ a·c ⋈ b·c` by scaling on the LEFT (c·a ⋈ c·b)
// and commuting both sides back (intCommuteMUL), so no right-factor leaf is needed.
// intMulOne: ⊢ a · &1 = a — MulSym then MulLeftIdentity. Mirror of realMulOne.
func intMulOne(a Term) *prop.PropWrapper {
	return intCommuteMUL(a, intLit(1)).EqTrans(intOneMul(a))
}

// intMonoScaleOne proves the monotone scaling whose bare side is the shared
// factor itself (`x·a ⋈ x`, `x ⋈ b·x`, …): the bare side is the factor times
// &1, and the identity reads the `x·&1` back as x. Mirror of realMonoScaleOne,
// which carries the account.
func intMonoScaleOne(hyps []Term, left, right, bare Term, strict, productOnLeft bool) (*prop.PropWrapper, bool) {
	one := intLit(1)
	var factor, other Term
	var scaleRight bool
	switch {
	case left.AlphaEquals(bare):
		factor, other, scaleRight = left, right, false
	case right.AlphaEquals(bare):
		factor, other, scaleRight = right, left, true
	default:
		return nil, false
	}
	a, b := other, one
	if !productOnLeft {
		a, b = one, other
	}
	var scaled *prop.PropWrapper
	var ok bool
	if scaleRight {
		scaled, ok = intMonoScaleRight(hyps, factor, a, b, strict)
	} else {
		scaled, ok = intMonoScaleLeft(hyps, factor, a, b, strict)
	}
	if !ok {
		return nil, false
	}
	relC := intLe
	if strict {
		relC = intLt
	}
	identity := intMulOne(factor)
	product := intStarT(factor, other)
	if scaleRight {
		identity = intOneMul(factor)
		product = intStarT(other, factor)
	}
	var cong *prop.PropWrapper
	if productOnLeft {
		cong = identity.LeftApply(ext.Apply(relC, product))
	} else {
		cong = identity.LeftApply(relC).RightApply(product)
	}
	return cong.EqMP(scaled), true
}

func intMonoScaleRight(hyps []Term, c, a, b Term, strict bool) (*prop.PropWrapper, bool) {
	caCb, ok := intMonoScaleLeft(hyps, c, a, b, strict) // ⊢ c·a ⋈ c·b
	if !ok {
		return nil, false
	}
	relC := intLe
	if strict {
		relC = intLt
	}
	cb, ac := intStarT(c, b), intStarT(a, c)
	// (c·a ⋈ c·b) = (a·c ⋈ b·c): commute the LEFT side, then the RIGHT side.
	cong := intCommuteMUL(c, a).LeftApply(relC).RightApply(cb). // (c·a⋈c·b) = (a·c⋈c·b)
									EqTrans(intCommuteMUL(c, b).LeftApply(ext.Apply(relC, ac))) // = (a·c⋈b·c)
	return cong.EqMP(caCb), true // ⊢ a·c ⋈ b·c
}

// intLinProveSigned proves `{hyps} ⊢ goal` where goal may carry top-level
// subtraction/negation, by first trying plain linarith and, failing that, ONE
// moveAcrossCmp pass to positivize the goal before re-running linarith. It does NOT
// re-enter the monotone/decide handlers (move-across + IntLinProve only), so it is
// safe to call from intProveSignedProduct's side conditions (e.g. `&0 ≤ −x`, whose
// neg the plain IntLinProve goal-side does not see).
func intLinProveSigned(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if pf, ok := IntLinProve(slices.Values(hyps), goal); ok {
		return pf, true
	}
	mac := intSubneg.moveAcrossCmp(goal) // ⊢ goal ⇔ positive
	if mac == nil {
		return nil, false
	}
	pf, ok := IntLinProve(slices.Values(hyps), prop.Rhs(mac))
	if !ok {
		return nil, false
	}
	return mac.EqSym().EqMP(pf), true // ⊢ goal
}

// intMulPosLemma proves `{hyps} ⊢ &0 ⋈ a·b` from `&0 ⋈ a` and `&0 ⋈ b` via
// LessEqMul (⋈ = ≤) / MulPos (⋈ = <). The two side conditions
// discharge through intLinProveSigned, so a NEGATED operand `−x` (used by the
// sign-mixed reductions) positivizes. nil/false when a side condition fails.
func intMulPosLemma(hyps []Term, a, b Term, strict bool) (*prop.PropWrapper, bool) {
	relT, thm := intLeT, intLessEqMulThm()
	if strict {
		relT, thm = intLtT, intMulPosThm()
	}
	a0, ok := intLinProveSigned(hyps, relT(intLit(0), a))
	if !ok {
		return nil, false
	}
	b0, ok := intLinProveSigned(hyps, relT(intLit(0), b))
	if !ok {
		return nil, false
	}
	imp := intImplyLeaf(thm, []Term{a, b},
		imply(relT(intLit(0), a), imply(relT(intLit(0), b), relT(intLit(0), intStarT(a, b)))))
	return mp(mp(imp, a0), b0), true // ⊢ &0 ⋈ a·b
}

// intProveSignedProduct proves a product's sign from its factors' signs — the
// sign-known nonlinear fragment (NOT full RCF). wantNonneg selects the target:
//
//	wantNonneg:  `&0 ⋈ x·y`  from (&0⋈x ∧ &0⋈y) OR (x⋈&0 ∧ y⋈&0);
//	!wantNonneg: `x·y ⋈ &0`  from (x⋈&0 ∧ &0⋈y) OR (&0⋈x ∧ y⋈&0).
//
// The negated-factor combos reduce to intMulPosLemma on `(−·)` operands, then push
// the negation out with negNegMul / negLmul / mulRightNeg; the nonpositive target then
// flips `&0 ⋈ −(x·y)` to `x·y ⋈ &0` (intFlipNeg). nil/false when no sign
// combination discharges (so `&0 ≤ x·x` with no hyps falls through to the Image
// split, unchanged).
func intProveSignedProduct(hyps []Term, x, y Term, wantNonneg, strict bool) (*prop.PropWrapper, bool) {
	rel, relT := intLe, intLeT
	if strict {
		rel, relT = intLt, intLtT
	}
	prod := intStarT(x, y)
	if wantNonneg {
		if w, ok := intMulPosLemma(hyps, x, y, strict); ok { // &0⋈x, &0⋈y
			return w, true
		}
		if w, ok := intMulPosLemma(hyps, intNegT(x), intNegT(y), strict); ok { // x⋈&0, y⋈&0
			eq := intSubneg.negNegMul(x, y)                 // (−x)·(−y) = x·y
			cong := eq.LeftApply(ext.Apply(rel, intLit(0))) // (&0⋈(−x)·(−y)) = (&0⋈x·y)
			return cong.EqMP(w), true                       // ⊢ &0 ⋈ x·y
		}
		return nil, false
	}
	if w, ok := intMulPosLemma(hyps, intNegT(x), y, strict); ok { // x⋈&0, &0⋈y
		return intFlipNeg(w, intSubneg.negLmul(x, y), prod, rel, relT, strict) // (−x)·y = −(x·y)
	}
	if w, ok := intMulPosLemma(hyps, x, intNegT(y), strict); ok { // &0⋈x, y⋈&0
		return intFlipNeg(w, intSubneg.mulRightNeg(x, y), prod, rel, relT, strict) // x·(−y) = −(x·y)
	}
	return nil, false
}

// intFlipNeg turns `w : Γ ⊢ &0 ⋈ negProd` plus `eq : ⊢ negProd = −prod` into
// `Γ ⊢ prod ⋈ &0`: rewrite w to `&0 ⋈ −prod`, then flip to `prod ⋈ &0` via the
// neg-order iff NegNonneg / NegPositiveIffNegative instantiated at the product. The flip is
// at the PROOF level because linarith atomizes `−prod` and `prod` as independent
// opaque atoms and cannot relate them.
func intFlipNeg(w, eq *prop.PropWrapper, prod, rel Term, relT func(a, b Term) Term, strict bool) (*prop.PropWrapper, bool) {
	cong := eq.LeftApply(ext.Apply(rel, intLit(0))) // (&0 ⋈ negProd) = (&0 ⋈ −prod)
	negFact := cong.EqMP(w)                         // Γ ⊢ &0 ⋈ −prod
	flipThm := intNegNonnegThm()
	if strict {
		flipThm = intNegPositiveIffNegativeThm()
	}
	flipIff := intEqLeaf(flipThm, []Term{prod},
		relT(intLit(0), intNegT(prod)), relT(prod, intLit(0))) // ⊢ (&0 ⋈ −prod) = (prod ⋈ &0)
	return flipIff.EqMP(negFact), true // Γ ⊢ prod ⋈ &0
}

// intProveProductMul2 proves `{hyps} ⊢ a·c ≤ b·d` from the four
// bounds `&0≤a, a≤b, &0≤c, c≤d` — DERIVED, no new bundle field: scale `a ≤ b` by c
// on the right (intMonoScaleRight, side condition &0≤c) to `a·c ≤ b·c`, scale
// `c ≤ d` by b on the left (intMonoScaleLeft, side condition &0≤b which follows from
// &0≤a ∧ a≤b) to `b·c ≤ b·d`, then transitivity over the opaque product atoms
// (IntLinProve). nil/false when any bound fails to discharge.
func intProveProductMul2(hyps []Term, a, c, b, d Term) (*prop.PropWrapper, bool) {
	acbc, ok := intMonoScaleRight(hyps, c, a, b, false) // ⊢ a·c ≤ b·c
	if !ok {
		return nil, false
	}
	bcbd, ok := intMonoScaleLeft(hyps, b, c, d, false) // ⊢ b·c ≤ b·d
	if !ok {
		return nil, false
	}
	// transitivity a·c ≤ b·c ≤ b·d (LessEqTrans; int does not atomize the product
	// atoms, so plain linarith cannot chain them).
	ac, bc, bd := intStarT(a, c), intStarT(b, c), intStarT(b, d)
	imp := intImplyLeaf(intLessEqTransThm(), []Term{ac, bc, bd},
		imply(intLeT(ac, bc), imply(intLeT(bc, bd), intLeT(ac, bd))))
	return mp(mp(imp, acbc), bcbd), true // Γ ⊢ a·c ≤ b·d
}

// Integral-domain (MulEqZero) square specializations — ℤ has no zero divisors.
// The distinct-factor `x·y=&0` is the splittable hyp (int_split.go); the square
// cases a==b are handled here (the split's two guards would coincide).

// intProveMulEqZeroSquare closes a goal from a hyp `x·x = &0`: MulEqZero gives
// `(x=&0) ∨ (x=&0)`, collapsed to the single fact `x = &0` by (p∨p)⇔p (no case
// split — its two guards coincide). The fact is
// added and the goal re-proved by the linear core, closing `x·x=&0 ⊢ x=&0` (and
// anything else following from x=&0). nil/false when no square-zero hyp helps.
func intProveMulEqZeroSquare(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	for _, h := range hyps {
		a, b, ok := intProductZeroEq(h)
		if !ok || !a.AlphaEquals(b) {
			continue
		}
		za := eqT(a, intLit(0))
		fact := prop.BooleanThms["p ∨ p"](za).EqMP(intMulEqZeroDisj(h, a, b)) // {h} ⊢ a=&0
		w, ok := IntLinProve(slices.Values(append(slices.Clone(hyps), za)), goal)
		if !ok {
			continue
		}
		return fact.DeriveTrans(w), true // {hyps} ⊢ goal (cut a=&0)
	}
	return nil, false
}

// intProveStrictSquare closes `{hyps} ⊢ &0 < x·x` given a hyp `x ≠ &0`: split x on
// its sign via the trichotomy (LessThanTrichotomy, the same engine the `≠`-hyp split
// uses), and close each branch with the STRICT sign-of-product (both factors the
// same definite sign → MulPos, reusing intProveSignedProduct). The two guards
// `x<&0` / `&0<x` are distinct, so ByCases recombines. Requires the canonical
// `¬(x=&0)` hyp form. nil/false otherwise.
func intProveStrictSquare(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	l, r, ok := intDomain.matchLt(goal)
	if !ok || !isIntZero(l) {
		return nil, false // goal must be `&0 < r`
	}
	x, y, ok := intDomain.matchStar(r)
	if !ok || !x.AlphaEquals(y) {
		return nil, false // r must be a square x·x
	}
	if !slices.ContainsFunc(hyps, not(eqT(x, intLit(0))).AlphaEquals) {
		return nil, false // need the `x ≠ &0` hyp (else &0 < x·x is not valid)
	}
	tri := intTrichotomyNeq(x, intLit(0)) // {¬(x=&0)} ⊢ (x<&0) ∨ (&0<x)
	if tri == nil {
		return nil, false
	}
	gNeg, gPos := intLtT(x, intLit(0)), intLtT(intLit(0), x)
	negBr, ok := intProveSignedProduct([]Term{gNeg}, x, x, true, true) // {x<&0} ⊢ &0<x·x
	if !ok {
		return nil, false
	}
	posBr, ok := intProveSignedProduct([]Term{gPos}, x, x, true, true) // {&0<x} ⊢ &0<x·x
	if !ok {
		return nil, false
	}
	return prop.ByCases(goal, gNeg, gPos).
		DeriveHypFrom(tri).
		DeriveHypFrom(negBr.PromoteHyp(gNeg)).
		DeriveHypFrom(posBr.PromoteHyp(gPos)), true // {¬(x=&0)} ⊢ &0 < x·x
}

// int_pow (integer exponentiation `int_pow : int → num → int`) — the int twin of
// the num nat_pow layer (nat_exp.go). int_pow is opaque to linarith/ring in general; the
// only tractable case is a LITERAL num exponent c, unfolded to a product chain
// `m · m · … · m` (c copies, `&1` for c=0) feeding the int ring/linear core. This
// file is that recursive unfold: a strictly-shrinking c≤1 fold auto-fires inside
// intArithSimpStep, and ExpandIntPowRewrite unfolds every literal-exponent atom
// (the agent-controlled c≥2 surface, since `int_pow(complex, c)` grows term size).
//
// The exponent is `num` (suc/Numeral/sucBits are the num successor machinery,
// reused unchanged); only the base and the result are int. Placeholder-backed
// (PowZero/PowSuc), like the rest of the int layer.

// intPowUnfold proves `⊢ int_pow m c = <unfolded product>` for a literal c ≥ 0.
// nil when c exceeds expUnfoldMax (the shared cap). Mirror of expUnfold.
func intPowUnfold(m Term, c uint64) *prop.PropWrapper {
	if c > expUnfoldMax {
		return nil
	}
	if c == 0 {
		return intPowZero(m) // ⊢ int_pow m 0 = &1
	}
	return intPowStep(m, c)
}

// intPowStep is the recursive case: build `⊢ int_pow m c = m · P` from inner
// `int_pow m (c-1) = P` and the PowSuc recursion at n = c-1. Mirror of
// expStep (the int PowSuc is already in the `pow(suc n) = m·pow(n)` orientation,
// so no EqSym of the recursion clause is needed).
func intPowStep(m Term, c uint64) *prop.PropWrapper {
	inner := intPowUnfold(m, c-1) // ⊢ int_pow m (c-1) = P
	if inner == nil {
		return nil
	}
	cMinus1 := Numeral(c - 1)
	// powSuc: ⊢ int_pow m (suc(c-1)) = m · int_pow m (c-1)   [PowSuc]
	powSuc := intPowSuc(m, cMinus1)
	// sucEq: ⊢ suc(c-1) = c   [numeric, via sucBits on the bit-tree]
	sucEq := sucBits(cMinus1)
	if sucEq == nil {
		return nil
	}
	// cong: ⊢ int_pow m (suc(c-1)) = int_pow m c   [congruence under int_pow m _]
	cong := sucEq.LeftApply(ext.Apply(intPow, m))
	// step2: ⊢ int_pow m c = m · int_pow m (c-1)   [cong⁻¹ ∘ powSuc]
	step2 := cong.EqSym().EqTrans(powSuc)
	// congMul: ⊢ m · int_pow m (c-1) = m · P   [congruence under m·_]
	congMul := inner.LeftApply(ext.Apply(intStar, m))
	// result: ⊢ int_pow m c = m · P
	return step2.EqTrans(congMul)
}

// intPowSimp is the intArithSimpStep entry: ONLY the strictly size-reducing
// literal cases c ≤ 1 (`int_pow m 0 → &1`, `int_pow m 1 → m`). Higher exponents
// are NOT auto-unfolded (a complex base to a high power explodes); the agent
// drives those through ExpandIntPowRewrite. Mirror of expSimp's literal path.
//
// The OfNumPow bridge — `int_pow(int_of_num m, n) → int_of_num(nat_pow(m, n))`
// when the base is `&_`. The wrapped num expression `nat_pow(m, n)` is left for num-side
// simp to fold (when a num nat_pow literal evaluator lands; today it falls back to
// ExpandEXPRewrite + ring for the literal case). Strict size-shrinks at the int
// head (replaces int_pow with int_of_num + num nat_pow), so the DeepRewrite fixpoint
// converges.
func intPowSimp(t Term) *prop.PropWrapper {
	m, n, ok := MatchesIntPow(t)
	if !ok {
		return nil
	}
	if c, ok := BitsToUint(n); ok && c <= 1 {
		return intPowUnfold(m, c)
	}
	// OfNumPow: base is `&inner` → bridge to num nat_pow. Fires for symbolic n too
	// (the lemma is universally quantified in n).
	if inner, isOfNum := MatchesIntOfNum(m); isOfNum {
		return intOfNumPow(inner, n)
	}
	return nil
}

// intPowUnfoldLeaf unfolds a single `int_pow m c` atom for any literal c ≥ 0 (no
// c ≤ 1 restriction). Mirror of expUnfoldLeaf.
func intPowUnfoldLeaf(t Term) *prop.PropWrapper {
	m, n, ok := MatchesIntPow(t)
	if !ok {
		return nil
	}
	c, ok := BitsToUint(n)
	if !ok {
		return nil
	}
	return intPowUnfold(m, c)
}

// ExpandIntPowRewrite is the deep+fixpoint rewrite that unfolds every literal-
// exponent int_pow atom anywhere in a term into a product chain — the int twin of
// ExpandEXPRewrite. The agent decides when to pay the term-growth cost.
func ExpandIntPowRewrite() prop.Rewrite { return prop.DeepRewrite(intPowUnfoldLeaf) }

// ── Square / pow-sign / abs ordering / n-ary triangle / square↔abs ────────────
// Handlers lifted from ℝ (lift via IntOfRealThm; native int proof
// unnecessary). Each is a near-mechanical mirror of the realProve* /
// real*Simp handler in real_ops.go.

// intPowLawSimp folds one int_pow law at t's head, or nil otherwise. Currently
// only SquareOfAbs: `int_abs(x) pow 2 → x pow 2` (strictly shrinks —
// removes abs). The int twin of realPowLawSimp's SquareOfAbs clause; placed first
// inside intArithSimpStep so the DeepRewrite fixpoint folds every abs-squared
// redex anywhere. Future home for the product, quotient, tower and unit-base laws of int_pow.
func intPowLawSimp(t Term) *prop.PropWrapper {
	base, exp, ok := MatchesIntPow(t)
	if !ok {
		return nil
	}
	if a, ok := MatchesIntAbs(base); ok && exp.AlphaEquals(Numeral(2)) {
		return intSquareOfAbs(a)
	}
	return nil
}

// intNegEqZeroSimp folds `(−x = &0) ⇔ (x = &0)` at t's head, or nil otherwise
// (NegEqZero). The neg twin of NegNonneg/NegPositiveIffNegative: zero-detection through neg, so
// linarith — which atomizes `−x` and `x` independently — can see the zero. The
// equation is matched with `&0` on either side (zeroSidedEq). The int twin of
// realInvSignSimp's NegEqZero case.
func intNegEqZeroSimp(t Term) *prop.PropWrapper {
	l, turned, ok := zeroSidedEq(t, isIntZero)
	if !ok {
		return nil
	}
	x, isNeg := MatchesIntNeg(l)
	if !isNeg {
		return nil
	}
	return afterTurn(turned, intNegEqZero(x))
}

// intAbsLessEqIffPowTwoLessEqSimp folds `int_pow x 2 ≤ int_pow y 2 → int_abs x ≤ int_abs y`
// at t's head, or nil otherwise (AbsLessEqIffPowTwoLessEq). Goal-side direction —
// pushes toward the canonical abs LHS form. Composes with SquareOfAbs (`|x|^2 →
// x^2`): a goal `|x|^2 ≤ |y|^2` strips abs first via SquareOfAbs to `x^2 ≤ y^2`,
// then this simp converts to `|x| ≤ |y|`; the cascade terminates since neither
// produces the other's input shape. Only fires for the literal exponent &2 (the
// general `x^n ≤ y^n` monotonicity is a separate sub-RCF tier). The int twin of
// realAbsLessEqIffPowTwoLessEqSimp.
func intAbsLessEqIffPowTwoLessEqSimp(t Term) *prop.PropWrapper {
	l, r, ok := intDomain.matchLe(t)
	if !ok {
		return nil
	}
	xb, xe, okx := MatchesIntPow(l)
	if !okx || !xe.AlphaEquals(Numeral(2)) {
		return nil
	}
	yb, ye, oky := MatchesIntPow(r)
	if !oky || !ye.AlphaEquals(Numeral(2)) {
		return nil
	}
	return intAbsLessEqIffPowTwoLessEq(xb, yb)
}

// intProveSquareNonneg closes `⊢ &0 ≤ x·x` with NO sign hypothesis
// (SquareNonneg, lifted from ℝ). The single-lemma alternative to
// the Image sign split (which closes the same goal via a ±&n case split + of_num
// collapse); placed BEFORE intImageSplit in intProveDecAtom so a square-nonneg
// goal preempts the case-split cost. intProveMonotone (needing factor-sign
// hyps) declines on this shape. The int twin of realProveSquareNonneg. ok=false
// when the goal is not `&0 ≤ (square)`.
func intProveSquareNonneg(goal Term) (*prop.PropWrapper, bool) {
	l, r, ok := intDomain.matchLe(goal)
	if !ok || !isIntZero(l) {
		return nil, false
	}
	x, y, ok := intDomain.matchStar(r)
	if !ok || !x.AlphaEquals(y) {
		return nil, false
	}
	return intSquareNonneg(x), true
}

// intProvePowSign closes a sign goal on an int_pow atom from the BASE's sign —
// the int_pow twin of the sign-of-product layer / mirror of
// realProvePowSign. The input is a base-sign fact, the output a single lemma
// instantiation. For `&0 ⋈ (int_pow x n)`, n any num term:
//
//	&0 ≤ int_pow x n  from  &0 ≤ x   (PowNonneg, symbolic n);
//	&0 ≤ int_pow x 2  with NO hyp    (PowTwoNonneg — an even square is nonneg);
//	&0 < int_pow x n  from  &0 < x   (PowPos).
//
// ok=false when the goal is not such a shape or the base sign does not
// discharge. Lifted from ℝ's PowNonneg / PowTwoNonneg / PowPos.
func intProvePowSign(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if l, r, ok := intDomain.matchLe(goal); ok && isIntZero(l) {
		if x, n, ok := MatchesIntPow(r); ok {
			return intPowNonneg(hyps, x, n, r)
		}
	}
	if l, r, ok := intDomain.matchLt(goal); ok && isIntZero(l) {
		if x, n, ok := MatchesIntPow(r); ok {
			return intPowPos(hyps, x, n, r)
		}
	}
	return nil, false
}

// intPowNonneg proves `{hyps} ⊢ &0 ≤ pow` (pow = int_pow x n): from `&0 ≤ x`
// via PowNonneg (any n), or unconditionally when n is the literal 2 via
// PowTwoNonneg. Mirror of realPowNonneg.
func intPowNonneg(hyps []Term, x, n, pow Term) (*prop.PropWrapper, bool) {
	zero := intLit(0)
	if base, ok := IntLinProve(slices.Values(hyps), intLeT(zero, x)); ok {
		return mp(intPowNonnegLeaf(x, n), base), true
	}
	if c, ok := BitsToUint(n); ok && c == 2 {
		return intPowTwoNonneg(x), true
	}
	return nil, false
}

// intPowPos proves `{hyps} ⊢ &0 < pow` (pow = int_pow x n) from `&0 < x` via
// PowPos. Mirror of realPowPos.
func intPowPos(hyps []Term, x, n, pow Term) (*prop.PropWrapper, bool) {
	base, ok := IntLinProve(slices.Values(hyps), intLtT(intLit(0), x))
	if !ok {
		return nil, false
	}
	return mp(intPowPosLeaf(x, n), base), true
}

// intProveAbsTriangle closes a goal `int_abs(sum) ≤ rhs` where sum is a right-
// associated n-ary sum `t1 + (t2 + (... + tn))` (n ≥ 2). Three stages:
//
//  1. Decompose sum into [t1, ..., tn]; build absSum = |t1| + (|t2| + (... + |tn|)).
//  2. Iterated AbsTriangle + LessEqAdd2 + LessEqTrans to prove |sum| ≤ absSum.
//  3. IntLinProve to prove absSum ≤ rhs (when |tᵢ| bounds appear in hyps).
//  4. Transitivity LessEqTrans.
//
// The binary case (`|x+y| ≤ |x|+|y|` directly or with a linarith-derivable rhs)
// is the recursion's base. Mirror of realProveAbsTriangle.
func intProveAbsTriangle(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	l, rhs, ok := intDomain.matchLe(goal)
	if !ok {
		return nil, false
	}
	inner, ok := MatchesIntAbs(l)
	if !ok {
		return nil, false
	}
	terms := decomposeIntPlusRight(inner)
	if len(terms) < 2 {
		return nil, false
	}
	absSum, triangleProof := iteratedIntAbsTriangle(terms)
	if rhs.AlphaEquals(absSum) {
		return triangleProof, true
	}
	boundLeRhs, ok := IntLinProve(slices.Values(hyps), intLeT(absSum, rhs))
	if !ok {
		return nil, false
	}
	return intLessEqTransProof(triangleProof, boundLeRhs), true
}

// decomposeIntPlusRight flattens a right-associated int_add chain.
// `a + (b + (c + d))` → [a, b, c, d]; a non-sum t → [t]. Mirror of
// decomposeRealPlusRight.
func decomposeIntPlusRight(t Term) []Term {
	if a, b, ok := intDomain.matchPlus(t); ok {
		return append([]Term{a}, decomposeIntPlusRight(b)...)
	}
	return []Term{t}
}

// iteratedIntAbsTriangle returns (absSum, ⊢ |sum| ≤ absSum) for a list of n ≥ 2
// terms, where sum = right-associated build of `terms` and absSum =
// right-associated build of `[|t1|, ..., |tn|]`. Recursive over the tail; the
// n=2 base is one AbsTriangle. Mirror of iteratedAbsTriangle.
func iteratedIntAbsTriangle(terms []Term) (Term, *prop.PropWrapper) {
	t1 := terms[0]
	abst1 := intAbsT(t1)
	if len(terms) == 2 {
		t2 := terms[1]
		absSum := intPlusT(abst1, intAbsT(t2))
		return absSum, intAbsTriangle(t1, t2)
	}
	tail := terms[1:]
	tailSum := buildIntPlusRight(tail)
	tailAbsSum, tailProof := iteratedIntAbsTriangle(tail) // ⊢ |tailSum| ≤ tailAbsSum
	absSum := intPlusT(abst1, tailAbsSum)
	// Step 1: AbsTriangle(t1, tailSum) — `|t1 + tailSum| ≤ |t1| + |tailSum|`.
	step1Bound := intPlusT(abst1, intAbsT(tailSum))
	step1 := intAbsTriangle(t1, tailSum)
	// Step 2: Pad tailProof with `|t1| ≤ |t1|` via LessEqAdd2 to get
	// `|t1| + |tailSum| ≤ |t1| + tailAbsSum`. Reflexivity discharges trivially.
	refl, _ := IntLinProve(slices.Values([]Term{}), intLeT(abst1, abst1))
	add2 := intAddLe2(abst1, abst1, intAbsT(tailSum), tailAbsSum)
	step2 := mp(mp(add2, refl), tailProof)
	// Step 3: Transit step1 + step2.
	_ = step1Bound
	proof := intLessEqTransProof(step1, step2)
	return absSum, proof
}

// buildIntPlusRight rebuilds a right-associated int sum from a list. len ≥ 1.
func buildIntPlusRight(terms []Term) Term {
	if len(terms) == 1 {
		return terms[0]
	}
	return intPlusT(terms[0], buildIntPlusRight(terms[1:]))
}

// intLessEqTransProof builds ⊢ a ≤ c from `ab: a ≤ b` and `bc: b ≤ c` via
// LessEqTrans. Mirror of realLessEqTransProof.
func intLessEqTransProof(ab, bc *prop.PropWrapper) *prop.PropWrapper {
	a, b, _ := intDomain.matchLe(ab.Conclusion())
	_, c, _ := intDomain.matchLe(bc.Conclusion())
	imp := intImplyLeaf(intLessEqTransThm(), []Term{a, b, c},
		imply(intLeT(a, b), imply(intLeT(b, c), intLeT(a, c))))
	return mp(mp(imp, ab), bc)
}

// ── int_div/int_rem ↔ divides bridges ────────────────────────────────────────

// intDividesIffRemZeroSimp folds `int_rem(m,n) = &0 → int_divides(n, m)` at t's head, or
// nil otherwise (DividesIffRemZero). Bridges the rem subsystem to the divides
// subsystem: a goal `int_rem(m,n) = &0` becomes a divisibility goal (closed by
// intDividesGoal); a hyp `int_rem(m,n) = &0` (after the same simp on the hyp side)
// becomes `int_divides(n, m)` and feeds intDividesSkolem. The equation is
// matched with `&0` on either side (zeroSidedEq).
//
// Skips n = &0 / &1: those are the divmod-simp's domain (RemByZero / RemByOne
// fold `int_rem(m,&0)→m` / `int_rem(m,&1)→&0`, which then collapse the eq directly).
// Without the skip the deep-rewrite of `int_rem(m,&1)=&0` flips to
// `int_divides(&1,m)` before the inner-fold cleanup runs, blocking the trivial
// close path.
func intDividesIffRemZeroSimp(t Term) *prop.PropWrapper {
	l, turned, ok := zeroSidedEq(t, isIntZero)
	if !ok {
		return nil
	}
	m, n, ok := MatchesIntRem(l)
	if !ok {
		return nil
	}
	if isIntZero(n) || isIntOne(n) {
		return nil // hand to intDivModSimp's RemByZero / RemByOne fold
	}
	return afterTurn(turned, intDividesIffRemZero(m, n))
}

// intProveDivisorBound is an enrichment for intProveDecAtom: when a hyp
// `int_divides(d, e)` is present AND `e ≠ &0` discharges, inject the bound
// `int_abs d ≤ int_abs e` (DivisorBoundedByDividend) and re-decide. Closes the bare
// contradictory `int_divides(&5, &3) ⊢ ⊥` class — the gcd-rank-1 test doesn't
// fire on a bare `int_divides(lit, lit)` (each row's coefficient gcd is 1),
// but the size bound `|&5| ≤ |&3|` reduces (after the int_abs split on literals)
// to `&5 ≤ &3`, which linarith refutes. nil/false when no usable divisibility
// hyp.
func intProveDivisorBound(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	var facts []*prop.PropWrapper
	for _, h := range hyps {
		d, e, ok := MatchesIntDivides(h)
		if !ok {
			continue
		}
		neq, nok := intProveNeqZero(hyps, e)
		if !nok {
			continue
		}
		want := intLeT(intAbsT(d), intAbsT(e))
		if slices.ContainsFunc(hyps, want.AlphaEquals) {
			continue // performance: already enriched, skip re-injecting
		}
		// DivisorBoundedByDividend: int_divides(d,e) ⇒ ~(e=&0) ⇒ |d| ≤ |e|. The divides
		// premise discharges via prop.Assume (h is one of `hyps`); the nonzero
		// via the derived `neq`.
		bnd := mp(mp(intDivisorBoundedByDividend(d, e), prop.Assume(h)), neq)
		facts = append(facts, bnd)
	}
	if len(facts) == 0 {
		return nil, false
	}
	return enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) {
			if w, ok := IntLinProve(slices.Values(h), goal); ok {
				return w, true
			}
			return intProveSplit(IntLinProve, nil, h, goal, nil)
		},
		hyps, facts)
}

// intProveQuotientExact is an enrichment for intProveDecAtom: when a hyp
// `int_divides(q, m)` is present, inject the exact-division identity
// `int_div(m, q) · q = m` (QuotientExactOfDivides) and re-decide. So a goal that depends
// on substituting `int_div(m, q)` away (under the divisibility hyp) reaches
// linarith with the bridge equation in hand. nil/false when no divisibility
// hyp is usable.
func intProveQuotientExact(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	var facts []*prop.PropWrapper
	for _, h := range hyps {
		q, m, ok := MatchesIntDivides(h)
		if !ok {
			continue
		}
		want := eqT(intStarT(intDivT(m, q), q), m)
		if slices.ContainsFunc(hyps, want.AlphaEquals) {
			continue // performance: already enriched, skip re-injecting
		}
		eq := mp(intQuotientExactOfDivides(m, q), prop.Assume(h))
		facts = append(facts, eq) // {h ∪ hyps} ⊢ int_div(m,q)·q = m
	}
	if len(facts) == 0 {
		return nil, false
	}
	return enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) {
			// Hyp-echo: the injected eq IS often the goal (e.g. user wrote the
			// identity as the goal under the divisibility hyp). intProveDecAtom
			// lacks an explicit hyp-echo, so do it here before linarith. Eq is
			// symmetric, so accept either orientation.
			if pf, ok := intHypEchoEq(h, goal); ok {
				return pf, true
			}
			if w, ok := IntLinProve(slices.Values(h), goal); ok {
				return w, true
			}
			return intProveSplit(IntLinProve, nil, h, goal, nil)
		},
		hyps, facts)
}

// intHypEchoEq reports whether goal follows from a hyp under either eq
// orientation, with a ring-bridge fallback. Three layers, cheap-first:
//
//  1. direct alpha — `goal ∈ hyps`.
//  2. swapped alpha — `(b = a) ∈ hyps` for goal `a = b`.
//  3. ring-bridged — for some hyp eq `c = d`, `a` and `c` (resp. `a` and `d`)
//     close via IntRingProveFull, and likewise for `b`. Closes the alpha-miss
//     class produced when one side has been canonicalized (e.g. moveAcrossCmp's
//     signedNorm reorders a product `div·q → q·div` via the multivariate sort,
//     while the fact intProveQuotientExact injects stays in the raw `div·q = m` shape) — a
//     case where layers 1/2 fail but the goal is provably equal to the hyp.
//
// Sound: only ring-provable equalities bridge (a miscomputed certificate makes
// IntRingProveFull return nil, so the bridge silently declines). Cheap: each
// hyp tried twice, IntRingProveFull declines fast on different-canonical-shape
// pairs (it computes both canonicals first and compares — O(term size)).
func intHypEchoEq(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if slices.ContainsFunc(hyps, goal.AlphaEquals) {
		return prop.Assume(goal), true
	}
	a, b, isEq := ext.MatchesEQ(goal)
	if !isEq {
		return nil, false
	}
	swapped := eqT(b, a)
	if slices.ContainsFunc(hyps, swapped.AlphaEquals) {
		return prop.Assume(swapped).EqSym(), true
	}
	// Ring-bridged fallback.
	if !isIntTerm(a) {
		return nil, false
	}
	for _, h := range hyps {
		c, d, hOk := ext.MatchesEQ(h)
		if !hOk || !isIntTerm(c) {
			continue
		}
		// Try (a=c) ∧ (b=d) via ring → bridge `a = c, c = d (hyp), b = d ⊢ a = b`.
		if ac, ok1 := IntRingProveFull(a, c); ok1 {
			if bd, ok2 := IntRingProveFull(b, d); ok2 {
				return ac.EqTrans(prop.Assume(h)).EqTrans(bd.EqSym()), true
			}
		}
		// Try (a=d) ∧ (b=c) via ring → bridge `a = d, d = c (hyp sym), b = c ⊢ a = b`.
		if ad, ok1 := IntRingProveFull(a, d); ok1 {
			if bc, ok2 := IntRingProveFull(b, c); ok2 {
				return ad.EqTrans(prop.Assume(h).EqSym()).EqTrans(bc.EqSym()), true
			}
		}
	}
	return nil, false
}

// intNormNatDiv proves ⊢ int_div(&m, &n) = &(nat_div(m, n)) via OfNumDiv + the num
// nat_div evaluator. The int_div/int_rem twin of intNormNatAdd/Mul. ok=false unless both
// operands are `&<bit-tree>` and the num side evaluates.
func intNormNatDiv(l, r Term) (*prop.PropWrapper, bool) {
	return intNormNatBin(l, r, intDivT, divT, intOfNumDivThm(), NormNatDiv)
}

// intNormNatMod proves ⊢ int_rem(&m, &n) = &(nat_mod(m, n)) via OfNumRem + the
// num nat_mod evaluator.
func intNormNatMod(l, r Term) (*prop.PropWrapper, bool) {
	return intNormNatBin(l, r, intRemT, modT, intOfNumRemThm(), NormNatMod)
}

// ── abs / sgn algebraic laws ─────────────────────────────────────────────────

// intAbsSgnSimp folds one int_abs / int_sgn algebraic redex at t's head, or
// nil otherwise. The int twin of realAbsSgnSimp — pushes abs/sgn toward the
// leaves over a COMPOUND argument (product / neg / abs / int_of_num):
//
//	|x·y| = |x|·|y|     (AbsMul)
//	|−x| = |x|          (AbsEven)
//	||x|| = |x|         (AbsIdempotent)
//	|&n| = &n           (OfNumAbs, n a num term)
//	sgn(x·y) = sgn x · sgn y   (SgnMul)
//	sgn(−x) = −(sgn x)         (SgnOdd)
//
// Distinct from the case split (int_split.go) — which eliminates a bare
// `int_abs x` / `int_sgn x` by its piecewise guard. Both layers coexist: the
// simp folds compound-arg abs/sgn first; a bare `int_abs(variable)` /
// `int_sgn(variable)` falls through to the case split.
//
// Wired in intArithSimpStep so DeepRewrite folds every abs/sgn redex anywhere.
// Each fold is unconditional (laws hold even at degenerate points) and every
// law is a corpus theorem, so this is a fully real-cert path once the
// bundle binds — no placeholder dependence.
func intAbsSgnSimp(t Term) *prop.PropWrapper {
	if x, ok := MatchesIntAbs(t); ok {
		return intAbsLaw(x)
	}
	if x, ok := MatchesIntSgn(t); ok {
		return intSgnLaw(x)
	}
	return nil
}

// intAbsLaw folds `int_abs(x)` when x is a product / neg / abs / int_of_num —
// pushing abs inward (or removing it). nil for a bare `int_abs(variable)`,
// which the leaf case split handles.
func intAbsLaw(x Term) *prop.PropWrapper {
	if a, b, ok := intDomain.matchStar(x); ok { // |a·b| = |a|·|b|
		return intAbsMul(a, b)
	}
	if a, ok := MatchesIntNeg(x); ok { // |−a| = |a|
		return intAbsEven(a)
	}
	if a, ok := MatchesIntAbs(x); ok { // ||a|| = |a|
		return intAbsIdempotent(a)
	}
	if n, ok := MatchesIntOfNum(x); ok { // |&n| = &n
		return intOfNumAbs(n)
	}
	return nil
}

// intSgnLaw folds `int_sgn(x)` when x is a product / neg. nil otherwise (a
// bare `int_sgn(variable)` is the leaf case split's; SgnPow / SgnPreservedByInv / SgnDiv
// have no int analogue — int has no inv/div).
func intSgnLaw(x Term) *prop.PropWrapper {
	if a, b, ok := intDomain.matchStar(x); ok { // sgn(a·b) = sgn a · sgn b
		return intSgnMul(a, b)
	}
	if a, ok := MatchesIntNeg(x); ok { // sgn(−a) = −(sgn a)
		return intSgnOdd(a)
	}
	return nil
}
