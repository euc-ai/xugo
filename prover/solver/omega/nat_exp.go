package omega

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// nat_pow (exponentiation) layer. nat_pow is unbounded in general, so
// linarith treats a nat_pow atom with a SYMBOLIC exponent as opaque; a literal
// exponent is read in the monomial basis (pow_basis.go, natPowChainUnfold), so
// `nat_pow(x, 2)` and `x * x` are one unknown. The ONLY tractable case for ring is
// a LITERAL exponent c, which can be unfolded to a product chain `m·m·…·m` (c
// copies) feeding RingProveFull. expUnfold is that recursive unfolding:
// arithSimpStep fires it for c ≤ 1 (expSimp), ExpandEXPRewrite for every
// literal c on request.
//
// Bound: expUnfoldMax caps the unfolding depth at 32. Corpus uses are typically
// c ≤ 5 (`(a+b)² = a²+2ab+b²` is the canonical case); anything beyond ~32 would
// produce a product chain too large for ring to normalize practically.

const expUnfoldMax = 32

// expUnfold proves `⊢ nat_pow(m, c) = <unfolded product>` for a literal c ≥ 0.
// Returns nil when the nat_pow bundle is unsupplied or c exceeds expUnfoldMax.
//
// Base cases (direct lemmas where available):
//
//	c=0: nat_pow(m, 0) = 1     [nat_pow recursion clause 1, projected]
//	c=1: nat_pow(m, 1) = m     [PowOne, EqSym; falls through to recursion if unbundled]
//	c=2: nat_pow(m, 2) = m·m   [PowTwo, EqSym; falls through if unbundled]
//
// Recursion (c ≥ 3, OR c=1/2 when the shortcut is unbundled):
//
//	nat_pow(m, suc k) = m · nat_pow(m, k)           [nat_pow recursion clause 2 at k = c-1]
//	suc(c-1) = c                            [sucBits at c-1]
//	→ nat_pow(m, c) = m · nat_pow(m, c-1)           [congruence + EqSym + EqTrans]
//	nat_pow(m, c-1) = P                          [recursive call]
//	→ nat_pow(m, c) = m · P                     [congruence on m·_]
func expUnfold(m Term, c uint64) *prop.PropWrapper {
	if c > expUnfoldMax {
		return nil
	}
	if c == 0 {
		return expBase(m)
	}
	if c == 1 {
		if w := powOne(m); w != nil {
			return w
		}
		// Fall through to recursion (uses nat_pow clause 2 + base).
	}
	if c == 2 {
		if w := powTwo(m); w != nil {
			return w
		}
		// Fall through to recursion.
	}
	return expStep(m, c)
}

// expStep is the recursive case: build `⊢ nat_pow(m, c) = m · P` from inner
// `nat_pow(m, c-1) = P` and the nat_pow recursion clause 2 at n=c-1.
func expStep(m Term, c uint64) *prop.PropWrapper {
	inner := expUnfold(m, c-1) // ⊢ nat_pow(m, c-1) = P
	if inner == nil {
		return nil
	}
	return expStepFrom(m, c, inner)
}

// natPowChainUnfold proves `⊢ nat_pow(m, c) = natDomain.powChain(m, c)` — the
// UNIFORM product chain `m·(m·(…·1))`, c factors over the numeral 1 — for a
// literal c within expUnfoldMax. It is the pow basis's proof half for num
// (pow_basis.go): expUnfold shortcuts c = 1 and c = 2 to their own shapes
// (`m`, `m·m`), which the basis cannot read as one chain, so the basis takes
// this unfold while the simp step keeps expUnfold. nil when the nat_pow
// bundle is unsupplied or c exceeds the cap.
func natPowChainUnfold(m Term, c uint64) *prop.PropWrapper {
	if c > expUnfoldMax {
		return nil
	}
	if c == 0 {
		return expBase(m) // ⊢ nat_pow(m, 0) = 1
	}
	inner := natPowChainUnfold(m, c-1) // ⊢ nat_pow(m, c-1) = chain(c-1)
	if inner == nil {
		return nil
	}
	return expStepFrom(m, c, inner)
}

// expStepFrom builds `⊢ nat_pow(m, c) = m · P` from a proved inner
// `⊢ nat_pow(m, c-1) = P` and the nat_pow recursion clause 2 at n = c-1 — the
// step expStep and natPowChainUnfold share, each supplying its own inner shape.
func expStepFrom(m Term, c uint64, inner *prop.PropWrapper) *prop.PropWrapper {
	cMinus1 := Numeral(c - 1)
	// step1: ⊢ m · nat_pow(m, c-1) = nat_pow(m, suc(c-1))   [nat_pow recursion clause 2]
	step1 := expRecursion2(m, cMinus1)
	if step1 == nil {
		return nil
	}
	// sucEq: ⊢ suc(c-1) = c   [numeric, via sucBits on the bit-tree]
	sucEq := sucBits(cMinus1)
	if sucEq == nil {
		return nil
	}
	// cong: ⊢ nat_pow(m, suc(c-1)) = nat_pow(m, c)   [congruence under nat_pow(m, _)]
	cong := sucEq.LeftApply(ext.Apply(natExp, m))
	// step2: ⊢ nat_pow(m, c) = m · nat_pow(m, c-1)   [chain step1 with cong⁻¹]
	step2 := cong.EqSym().EqTrans(step1.EqSym())
	// congMul: ⊢ m · nat_pow(m, c-1) = m · P   [congruence under m·_]
	congMul := inner.LeftApply(ext.Apply(natStar, m))
	// result: ⊢ nat_pow(m, c) = m · P   [chain step2 with congMul]
	return step2.EqTrans(congMul)
}

// expBase: ⊢ nat_pow(m, 0) = 1   (from nat_pow recursion clause 1, oriented).
// clauseLeaf via projectMatch auto-orients the bound clause to the wanted shape
// whichever way it is stated.
func expBase(m Term) *prop.PropWrapper {
	if natPowThm() == nil {
		return nil
	}
	return clauseLeaf(natPowThm(), nil, expT(m, natZero), Numeral(1))
}

// expRecursion2: ⊢ m · nat_pow(m, n) = nat_pow(m, suc n)   (nat_pow recursion clause 2,
// oriented by projectMatch); callers EqSym when they need the reverse.
func expRecursion2(m, n Term) *prop.PropWrapper {
	if natPowThm() == nil {
		return nil
	}
	return clauseLeaf(natPowThm(), nil, star(m, expT(m, n)), expT(m, sucT(n)))
}

// powOne: ⊢ nat_pow(m, 1) = m   (real: PowOne `∀n. n = nat_pow(n, 1)`, reversed). nil when
// the bundle is unsupplied — caller (expUnfold) falls through to the recursion.
func powOne(m Term) *prop.PropWrapper {
	if powOneThm() == nil {
		return nil
	}
	return eqLeaf(powOneThm(), []Term{m}, expT(m, Numeral(1)), m)
}

// powTwo: ⊢ nat_pow(m, 2) = m · m   (real: PowTwo `∀n. n·n = nat_pow(n, 2)`, reversed). nil
// when unsupplied — caller falls through.
func powTwo(m Term) *prop.PropWrapper {
	if powTwoThm() == nil {
		return nil
	}
	return eqLeaf(powTwoThm(), []Term{m}, expT(m, Numeral(2)), star(m, m))
}

// onePow: ⊢ nat_pow(1, n) = 1   (real: OnePow `∀n. 1 = nat_pow(1, n)`, reversed).
// Symbolic n; term strictly shrinks. nil when OnePow is unsupplied.
func onePow(n Term) *prop.PropWrapper {
	if onePowThm() == nil {
		return nil
	}
	return eqLeaf(onePowThm(), []Term{n}, expT(Numeral(1), n), Numeral(1))
}

// zeroPow: ⊢ nat_pow(0, n) = COND(n = 0, 1, 0)   (real: ZeroPow, direct orientation).
// Symbolic n; the Cond exposes the structural choice but doesn't grow term size
// significantly. arith's atom decider + trivialCondRewrite collapse the Cond when
// the guard discharges (`n=0` decidable via NormNatEq for literal n, or `n≠0` via
// linarith from `0<n` in hyps). nil when ZeroPow is unsupplied.
func zeroPow(n Term) *prop.PropWrapper {
	if zeroPowThm() == nil {
		return nil
	}
	rhs := ext.Cond(eqT(n, natZero), Numeral(1), natZero)
	return eqLeaf(zeroPowThm(), []Term{n}, expT(natZero, n), rhs)
}

// expSimp is the arithSimpStep entry: ONLY handles the harmless size-reducing
// cases c=0 and c=1. Higher exponents are explicitly NOT unfolded here because
// the unified arith move is agent-uncontrollable, and expanding `nat_pow(complex, c)`
// for c≥2 can blow up term size (a complex base raised to a high power explodes
// — `nat_pow(a+b+c+d, 5)` becomes a chain of 5 copies). That kind of size-changing
// rewrite is a deliberate proof-step choice; agents drive it through the
// separate ExpandEXPRewrite / ExpandEXPTactic surface, not by surprise inside
// arith.
//
// What auto-fires inside arith:
//
//	nat_pow(m, 0) → 1                       (literal c=0 — strictly smaller)
//	nat_pow(m, 1) → m                       (literal c=1 — strictly smaller)
//	nat_pow(1, n) → 1                       (OnePow, ANY n — strictly smaller)
//	nat_pow(0, n) → COND(n = 0, 1, 0)       (ZeroPow — Cond's guard then collapses
//	                                     through trivialCondRewrite + the atom
//	                                     decider, giving 0 when n≠0 dischargeable
//	                                     and 1 when n=0; bounded growth)
//
// What does NOT auto-fire (use ExpandEXPRewrite explicitly):
//
//	nat_pow(m, c) for c ≥ 2 with symbolic m  (could grow term size by a factor of c)
//	nat_pow(m, n) with both m and n non-special  (opaque)
//
// What DOES auto-fire when both operands are literals (≥ c=2 is otherwise out):
//
//	nat_pow(&m, &c) for literal m, c ≥ 2  (NormNatExp evaluates to a single &literal —
//	                                   strictly term-shrinking, the sibling of
//	                                   NormNatAdd/Mul that auto-fire on &m+&n / &m·&n)
func expSimp(t Term) *prop.PropWrapper {
	m, n, ok := MatchesExp(t)
	if !ok {
		return nil
	}
	// Literal-c path for c ≤ 1: strictly term-shrinking unfold.
	if c, ok := BitsToUint(n); ok && c <= 1 {
		return expUnfold(m, c)
	}
	// Literal-literal evaluator: collapse `&m nat_pow &c` (c ≥ 2) to a single literal
	// via NormNatExp. Strictly term-shrinking (one literal vs base + exponent),
	// so safe to auto-fire inside arith — the sibling of `&m + &c → &k` and
	// `&m · &c → &k` already in arithSimpStep. Placed BEFORE the symbolic-n
	// special-base clauses so a literal `0 nat_pow &5` / `1 nat_pow &5` folds directly
	// to its value via NormNatExp (rather than declining when ZeroPow / OnePow
	// is unsupplied — those handle symbolic n, NormNatExp covers the literal
	// case unconditionally).
	if isNumeralLit(m) && isNumeralLit(n) {
		if w, ok := NormNatExp(m, n); ok {
			return w
		}
	}
	// Special-base path (any n): OnePow / ZeroPow. For SYMBOLIC n: OnePow
	// gives `nat_pow(1, n) = 1` directly; ZeroPow gives `nat_pow(0, n) = COND(n=0, 1, 0)`
	// which the cond simp then collapses once n's verdict discharges. Falls
	// through to nil when the lemma is unsupplied or m isn't a special literal.
	if isOneNum(m) {
		return onePow(n)
	}
	if isZeroNum(m) {
		return zeroPow(n)
	}
	return nil
}

// ── Agent-controlled deep expansion of EVERY literal-exponent nat_pow ─────────────
//
// `ExpandEXPRewrite` is the rewrite surface for an agent to deliberately request
// "expand all my nat_pow atoms into product chains" — usually as a setup step before
// `arith` / `ring` closes a polynomial identity (`(a+b)² = a²+2ab+b²` and
// friends). Unlike expSimp, this DOES unfold c ≥ 2 because the agent has chosen
// to: it knows it's about to grow the term.

// expUnfoldLeaf is the shallow rewrite that unfolds a single `nat_pow(m, c)` atom
// for any literal c ≥ 0 (no c ≤ 1 restriction). prop.DeepRewrite wraps it for
// the full traversal.
func expUnfoldLeaf(t Term) *prop.PropWrapper {
	m, n, ok := MatchesExp(t)
	if !ok {
		return nil
	}
	c, ok := BitsToUint(n)
	if !ok {
		return nil
	}
	return expUnfold(m, c)
}

// ExpandEXPRewrite is the deep+fixpoint rewrite that unfolds every literal-
// exponent nat_pow atom anywhere in a term into a product chain. Wrap it in
// tactic.rewriteTactic to invoke as an agent action — the agent decides when
// to pay the term-growth cost of expanding `nat_pow(complex, c)` for c ≥ 2.
//
// Non-literal exponents are left alone (the rewrite returns nil at those atoms,
// so subterms continue traversal unchanged). nat_pow atoms exceeding expUnfoldMax
// are also left alone.
func ExpandEXPRewrite() prop.Rewrite { return prop.DeepRewrite(expUnfoldLeaf) }

// Bounded-variable enumeration split — a finite, terminating
// special case of the gray-shadow case split. When a comparison atom is
// NON-linear in a variable x (so linarith/omega treat x's occurrence — `x*x`,
// `nat_pow(a,x)`, `nat_mod(a,x)`, … — as opaque and decline) but a hypothesis bounds x
// by a concrete literal (`x ≤ c` or `x < c`, c ≤ enumMax), the atom is decided by
// ENUMERATION: peel the bound into the finite disjunction `x=0 ∨ … ∨ x=c`,
// substitute each value into the goal (eqHypSubst makes the opaque atom literal,
// the existing literal simps evaluate it to ⊤), and recombine via ByCasesRecursive.
//
// This is the bounded twin of the rank-k cut frontier: where the general integer
// completeness frontier must SYNTHESIZE a splitting disjunction, a concrete bound
// hands one over for free, and the per-value substitution reuses the whole literal
// simp/eval stack. It lives entirely inside the forward prover (returns one
// `{hyps} ⊢ goal`), as the last fallback in proveDecAtom — so the engine / simp /
// Farkas layers are untouched.
//
// Termination: each value branch substitutes x out of the goal (x → literal), so
// the recursive decision sees an x-free atom and never re-enters enumeration on
// the same variable; nested bounds (y also bounded) give a finite product of
// branches. The enumMax cap bounds the disjunction width.
//
// Supply: the bundle fields LessEqSplit + LessThanSucIffLessEq; degrades to a
// graceful no-op when either is unbundled. The per-value proofs use only the existing simp/eval
// leaves, so no unsound-integer counter bump beyond whatever a branch itself uses.

// enumMax caps the literal bound: a disjunction of up to enumMax+1 values, each
// triggering a full decision rewrite. Kept small — bounded-nonlinear goals in the
// corpus use tiny bounds; a large bound would be a sign linarith should handle it.
const enumMax = 12

// proveBoundedEnum tries `{hyps} ⊢ goal` for a comparison atom that is nonlinear
// in a literal-bounded variable, by enumerating that variable's values.
func proveBoundedEnum(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	if lessEqSplitThm() == nil || lessThanSucIffLessEqThm() == nil {
		return nil, false // enumeration lemmas unbundled — decline gracefully.
	}
	x, k, leToK, ok := firstEnumBound(hyps, goal)
	if !ok || !isNat(x) {
		return nil, false
	}
	disjK, ok := enumLeDisj(x, k) // {x≤K} ⊢ (x=0) ∨ … ∨ (x=K)
	if !ok {
		return nil, false
	}
	disj := leToK.DeriveTrans(disjK) // {boundHyp} ⊢ (x=0) ∨ … ∨ (x=K)

	eqs := make([]Term, 0, k+1)
	imps := make([]*prop.PropWrapper, 0, k+1)
	for v := uint64(0); v <= k; v++ {
		eqv := eqT(x, Numeral(v))
		gv, ok := proveAtValue(hyps, goal, eqv)
		if !ok {
			return nil, false // this value doesn't close — enumeration fails.
		}
		eqs = append(eqs, eqv)
		imps = append(imps, gv.PromoteHyp(eqv)) // {hyps} ⊢ (x=v) ⇒ goal
	}
	// ByCasesRecursive expects the Or(eqs) hyp in foldl (left-nested) form — the
	// same nesting enumLeDisj builds — plus each `eqv ⇒ goal`.
	res := prop.ByCasesRecursive(goal, eqs...).DeriveHypFrom(disj)
	for _, imp := range imps {
		res = res.DeriveHypFrom(imp)
	}
	return res, true
}

// proveAtValue proves `{hyps, x=v} ⊢ goal` by routing the goal through the full
// decision rewrite with x pinned to the literal v: eqHypSubst substitutes x→v,
// the literal simps evaluate the now-ground opaque atom, and the comparison
// decides. ok=false unless the goal reduces all the way to ⊤.
func proveAtValue(hyps []Term, goal, eqv Term) (*prop.PropWrapper, bool) {
	// Raw (no pre-simp): the augmented value-pin `eqv = (x=v)` must roundtrip
	// shape-intact — see arithDecideWithHypsRaw.
	w := arithDecideWithHypsRaw(append(slices.Clone(hyps), eqv))(goal)
	if w == nil || !prop.Rhs(w).AlphaEquals(prop.T) {
		return nil, false
	}
	return iffTrueElim(w), true // {H} ⊢ goal, H ⊆ hyps∪{x=v}
}

// firstEnumBound finds the first hypothesis bounding a variable x by a literal
// (`x ≤ c` ⇒ K=c, or `x < c` ⇒ K=c-1) where x occurs NON-linearly in the goal
// atom (so linarith already declined). Returns x, the numeric bound k, and
// `leToK : {boundHyp} ⊢ x ≤ K` (the bridge that ties the enumeration disjunction
// back to the actual input hypothesis). ok=false when no such bound exists.
func firstEnumBound(hyps []Term, goal Term) (x Term, k uint64, leToK *prop.PropWrapper, ok bool) {
	// Only a comparison atom with a nonlinear side is worth enumerating; a fully
	// linear atom is linarith/omega's job (and it already ran and failed).
	if !IsLinComparisonGoal(goal) || ComparisonSidesLinear(goal) {
		return nil, 0, nil, false
	}
	goalVars := freeNumVars(goal)
	occurs := func(v Term) bool { return slices.ContainsFunc(goalVars, v.AlphaEquals) }
	// A candidate var that already has an equality hyp is handled by eqHypSubst
	// (which substitutes it directly); enumerating it would be redundant AND would
	// loop — each per-value branch re-adds an `x=v` hyp and the inner decision
	// would re-enter enumeration on the same x before the substitution lands.
	for _, h := range hyps {
		if a, b, m := MatchesLe(h); m && isVar(a) && isNat(a) && occurs(a) && !hasEqHyp(a, hyps) {
			if k, ok := enumBoundK(b, false); ok {
				return a, k, prop.Assume(h), true // {x≤c} ⊢ x≤c
			}
		}
		if a, b, m := MatchesLt(h); m && isVar(a) && isNat(a) && occurs(a) && !hasEqHyp(a, hyps) {
			if k, ok := enumBoundK(b, true); ok {
				// {x<c} ⊢ x ≤ c-1  via  (x<c) ⇔ (x ≤ c-1);  here c = k+1.
				return a, k, ltToLeBridge(a, k+1).EqMP(prop.Assume(h)), true
			}
		}
	}
	// Fallback: no SYNTACTIC literal bound. Try to DERIVE one via ℚ-linarith — a
	// transitive / combined bound `x ≤ c` the hyps imply but no single hyp states
	// (e.g. `x≤y, y≤3 ⊢ x≤3`). Smallest provable c wins (minimal disjunction). Use
	// LinProve (ℚ only), never the integer core, for this discovery scan; the
	// derived `leToK : {hyps'} ⊢ x≤c` carries a hyp-subset, which DeriveTrans /
	// DeriveHypFrom thread through unchanged. (Integer-TIGHTENED bounds like
	// `2x≤5 ⊢ x≤2` need OmegaProve and are deferred, to keep this scan ℚ-only.)
	for _, v := range goalVars {
		if !isVar(v) || !isNat(v) || hasEqHyp(v, hyps) {
			continue
		}
		for c := uint64(0); c <= enumMax; c++ {
			if p, ok := LinProve(slices.Values(hyps), le(v, Numeral(c))); ok {
				return v, c, p, true // {hyps'} ⊢ v ≤ c
			}
		}
	}
	return nil, 0, nil, false
}

// enumBoundK converts a literal bound term into the maximum enumerable value k,
// applying the strict→non-strict offset (strict `v<c` ⇒ k=c-1; non-strict
// `v≤c` ⇒ k=c) and the enumMax gate. Shared by firstEnumBound (∀-enumeration)
// and literalUpperBound (∃-witness search). ok=false when bound
// is not a literal, a strict bound is 0 (empty range), or k>enumMax.
func enumBoundK(bound Term, strict bool) (uint64, bool) {
	c, ok := BitsToUint(bound)
	if !ok {
		return 0, false
	}
	if strict {
		if c == 0 || c-1 > enumMax {
			return 0, false
		}
		return c - 1, true
	}
	if c > enumMax {
		return 0, false
	}
	return c, true
}

// hasEqHyp reports whether some hyp is an equality with v as one side (so
// eqHypSubst will substitute v, and enumeration must stand down — see the loop
// note in firstEnumBound).
func hasEqHyp(v Term, hyps []Term) bool {
	for _, h := range hyps {
		if l, r, ok := ext.MatchesEQ(h); ok && (l.AlphaEquals(v) || r.AlphaEquals(v)) {
			return true
		}
	}
	return false
}

// enumLeDisj builds `{x ≤ K} ⊢ (x=0) ∨ (x=1) ∨ … ∨ (x=k)` (K = Numeral(k)) in
// the foldl/left-nested Or shape, by peeling one value at a time:
//
//	{x≤K} ⊢ (x<K) ∨ (x=K)           [LessEqSplit]
//	      ⊢ (x≤K-1) ∨ (x=K)          [bridge x<K ⇔ x≤K-1]
//	recurse on x≤K-1, then ByCases-recombine appending the x=K disjunct.
//
// Base k=0: `{x≤0} ⊢ x=0` by antisymmetry with `0≤x`.
func enumLeDisj(x Term, k uint64) (*prop.PropWrapper, bool) {
	if !isNat(x) {
		return nil, false
	}
	if k == 0 {
		// {x≤0} ⊢ x=0   (lessEqAntisym applied to x≤0 and the implicit 0≤x).
		return mp(mp(lessEqAntisym(x, natZero), prop.Assume(le(x, natZero))), zeroLe(x)), true
	}
	K, Km1 := Numeral(k), Numeral(k-1)
	eqK := eqT(x, K)

	split := lessEqSplit(x, K).EqMP(prop.Assume(le(x, K))) // {x≤K} ⊢ (x<K) ∨ (x=K)
	// Rewrite the left disjunct (x<K) → (x≤K-1): congruence on OR's first arg.
	cong := ltToLeBridge(x, k).LeftApply(prop.OR).RightApply(eqK) // ((x<K)∨eqK) = ((x≤Km1)∨eqK)
	splitLe := cong.EqMP(split)                                   // {x≤K} ⊢ (x≤K-1) ∨ (x=K)

	sub, ok := enumLeDisj(x, k-1) // {x≤K-1} ⊢ Or(x=0 … x=K-1)
	if !ok {
		return nil, false
	}
	D := sub.Conclusion()
	imp0 := prop.ConclOR0(D, eqK).DeriveHypFrom(sub).PromoteHyp(le(x, Km1)) // (x≤K-1) ⇒ D∨eqK
	imp1 := prop.ConclOR1(D, eqK).DeriveHypFrom(prop.Assume(eqK)).PromoteHyp(eqK)
	res := prop.ByCases(or(D, eqK), le(x, Km1), eqK).
		DeriveHypFrom(splitLe).
		DeriveHypFrom(imp0).
		DeriveHypFrom(imp1) // {x≤K} ⊢ D ∨ (x=K) = Or(x=0 … x=K)
	return res, true
}

// ltToLeBridge proves `⊢ (x < K) ⇔ (x ≤ K-1)` for a literal k ≥ 1 (K=Numeral(k)):
// LessThanSucIffLessEq gives `(x < suc(K-1)) ⇔ (x ≤ K-1)`, and `suc(K-1) = K` (sucBits) folds
// the strict bound's RHS.
func ltToLeBridge(x Term, k uint64) *prop.PropWrapper {
	Km1 := Numeral(k - 1)
	congLt := sucBits(Km1).LeftApply(applyLt(x)) // ⊢ (x < suc(K-1)) = (x < K)
	return congLt.EqSym().EqTrans(lessThanSucIffLessEq(x, Km1))
}

// applyLt partially applies `<` to its left argument: `(x < ·)`.
func applyLt(x Term) Term { return ext.Apply(natLt, x) }

// ── Named-lemma leaves ────────────────────────────────────────────────────────

// lessEqSplit: ⊢ (a ≤ b) ⇔ ((a < b) ∨ (a = b))   (real: LessEqSplit).
func lessEqSplit(a, b Term) *prop.PropWrapper {
	return eqLeaf(lessEqSplitThm(), []Term{a, b}, le(a, b), or(lt(a, b), eqT(a, b)))
}

// lessThanSucIffLessEq: ⊢ (a < suc b) ⇔ (a ≤ b)   (real: LessThanSucIffLessEq).
func lessThanSucIffLessEq(a, b Term) *prop.PropWrapper {
	return eqLeaf(lessThanSucIffLessEqThm(), []Term{a, b}, lt(a, sucT(b)), le(a, b))
}

// Bounded existential witness search — the quantifier extension
// of the bounded-variable enumeration above (proveBoundedEnum). A goal
//
//	{hyps} ⊢ ∃i. (i < c ∧ P i)        (c a literal numeral, c ≤ enumMax)
//
// is closed by SEARCHING the finite range {0, …, c-1} for one value v whose
// instantiated body `(v < c) ∧ P v` the arith decider closes, then ∃-introducing
// at v. It is the witness-side dual of proveBoundedEnum: where the ∀-flavoured
// enumeration case-splits a bounded decision and must close EVERY branch,
// here a SINGLE satisfied value suffices — so there is no disjunction to
// recombine, just InstExists at the found witness.
//
// IMPORTANT — this is INTENTIONALLY NOT wired into proveDecAtom / arith / the
// engine. proveBoundedEnum belongs in the always-on arith move because its trigger
// (an atom nonlinear in a literal-bounded var, `x·x ≤ 4`) is a true LAST RESORT —
// nothing else closes it, so it competes with no better proof. A bounded-∃ goal is
// different: it frequently has a better structural proof (an explicit witness the
// agent already knows, a general existence lemma), so enumerating it from inside
// the cheap always-on arith move would PREEMPT those and persist a brittle
// search-derived proof into the corpus. Bounded-∃ search therefore belongs to an
// explicit, agent/orchestrator-invoked move, sequenced AFTER the structural
// attempts. That move does not exist yet; this function is its reusable kernel.
// (The arith-vs-separate rationale: a method may live in always-on arith only if
// it is BOTH all-or-nothing-closing AND the last resort for its goal shape —
// bounded-∃ satisfies the former but not the latter.)
//
// Bound shapes recognized (i = the ∃-bound var, c a literal numeral ≤ enumMax),
// as a conjunct of the body: `i < c` / `i ≤ c` / `c > i` / `c ≥ i`. Nested bounded
// ∃ (`∃i.∃j. …`) is handled by recursion on the per-value body.
//
// Termination: each level peels one ∃ and substitutes its var to a literal, so the
// recursion strictly reduces quantifier depth and the per-value range is finite.
// All-or-nothing: on failure the goal is untouched (returns nil,false).

// proveBoundedExists tries `{hyps} ⊢ ∃i. body(i)` by searching a literal-bounded
// range of i for a witness whose instantiated body closes. Returns (nil,false)
// when the goal is not a bounded ∃, no literal bound conjunct on i is found, or no
// value in range closes.
func proveBoundedExists(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	abs := prop.MatchesEXISTS(goal)
	if abs.IsZero() {
		return nil, false
	}
	i := abs.Var()
	k, ok := boundedExistsRange(i, abs.Body())
	if !ok {
		return nil, false
	}
	for v := uint64(0); v <= k; v++ {
		val := Numeral(v)
		bodyV := abs.Body().Substitute(core.MakeTermSubst(i, val))
		proof, ok := proveExistsBody(hyps, bodyV)
		if !ok {
			continue // this value's body does not close — try the next.
		}
		// InstExists: body[i:=v] ⊢ ∃i. body. Discharge its body hyp with the proof
		// of body[i:=v] under the input hyps, leaving `{hyps'} ⊢ ∃i. body`
		// (hyps' ⊆ hyps — the witness is a literal, never a hypothesis).
		return prop.InstExists(goal, val).DeriveHypFrom(proof), true
	}
	return nil, false
}

// proveExistsBody proves `{hyps} ⊢ bodyV` for a witness-instantiated body. It
// first runs the arith decider: if that closes the body to ⊤, done. Otherwise, if
// the body reduces to (or already is) a bounded existential — the NESTED-∃ case,
// where folding the outer bound conjunct leaves `∃j. …` as the residual — it
// recurses, then composes the residual's proof back through the rewrite. ok=false
// when neither closes.
func proveExistsBody(hyps []Term, bodyV Term) (*prop.PropWrapper, bool) {
	// Raw (no pre-simp): same hyps as the surrounding call — pre-simp would
	// repeat work already done by the public entry. See arithDecideWithHypsRaw.
	w := arithDecideWithHypsRaw(hyps)(bodyV)
	if w == nil {
		// No simplification fired; recurse only if bodyV is itself a bounded ∃.
		if !prop.MatchesEXISTS(bodyV).IsZero() {
			return proveBoundedExists(hyps, bodyV)
		}
		return nil, false
	}
	residual := prop.Rhs(w) // ⊢ bodyV ⇔ residual
	if residual.AlphaEquals(prop.T) {
		return iffTrueElim(w), true // {hyps} ⊢ bodyV
	}
	// Reduced but not to ⊤. If the residual is a bounded ∃ (the outer bound
	// conjunct folded away, leaving the inner quantifier), search it and EqMP back.
	if !prop.MatchesEXISTS(residual).IsZero() {
		if rp, ok := proveBoundedExists(hyps, residual); ok {
			return w.EqSym().EqMP(rp), true // {hyps} ⊢ bodyV
		}
	}
	return nil, false
}

// boundedExistsRange finds a conjunct of the body that upper-bounds the ∃-bound
// var i by a literal and returns the maximum enumerable value k (k=c-1 for a
// strict bound, k=c for a non-strict one), gated by enumMax. ok=false when no
// literal upper bound on i appears in the body.
func boundedExistsRange(i, body Term) (uint64, bool) {
	for _, conj := range DecomposesAnd(body) {
		if k, ok := literalUpperBound(i, conj); ok {
			return k, true
		}
	}
	return 0, false
}

// literalUpperBound reports whether comparison `t` upper-bounds `v` by a literal
// within enumMax, returning the maximum enumerable value k. Recognizes all four
// orientations — `v<c` / `v≤c` / `c>v` / `c≥v` — delegating the strict→k offset
// and the enumMax gate to the shared enumBoundK. ok=false otherwise.
func literalUpperBound(v, t Term) (uint64, bool) {
	if a, b, ok := MatchesLt(t); ok && a.AlphaEquals(v) { // v < c
		return enumBoundK(b, true)
	}
	if a, b, ok := MatchesLe(t); ok && a.AlphaEquals(v) { // v ≤ c
		return enumBoundK(b, false)
	}
	if a, b, ok := MatchesGt(t); ok && b.AlphaEquals(v) { // c > v  ⇔  v < c
		return enumBoundK(a, true)
	}
	if a, b, ok := MatchesGe(t); ok && b.AlphaEquals(v) { // c ≥ v  ⇔  v ≤ c
		return enumBoundK(a, false)
	}
	return 0, false
}
