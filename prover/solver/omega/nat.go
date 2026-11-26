package omega

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// isZeroNum / isOneNum recognize the raw bit-tree literals 0 / 1. A literal is
// just the bare BIT-tree, so matching structurally against Numeral(0)/Numeral(1)
// guarantees the identity leaf's LHS α-matches the term being rewritten.
func isZeroNum(t Term) bool { return t.AlphaEquals(natZero) }

func isOneNum(t Term) bool { return t.AlphaEquals(Numeral(1)) }

// isNumeralLit reports whether t is a (raw bit-tree) numeral literal.
func isNumeralLit(t Term) bool { _, ok := asNumeral(t); return ok }

// mulOneR: ⊢ a · 1 = a   (real: MulClauses `m*1=m` conjunct). The `a*1`
// companion to the existing oneMulL (`1*a=a`); both project from MulClauses.
func mulOneR(a Term) *prop.PropWrapper {
	return clauseLeaf(mulClausesThm(), a, star(a, Numeral(1)), a)
}

// arithSimpStep is the one-level (shallow) identity/numeral fold: inspects the
// head operator of t and returns the matching identity-law leaf or numeral fold,
// or nil when t is not a reducible redex. The deep rewrite drives it deep
// + to a fixpoint (composeArithLeaves, engine.go).
func arithSimpStep(t Term) *prop.PropWrapper {
	if l, r, ok := MatchesPlus(t); ok {
		switch {
		case isZeroNum(r): // a + 0 → a
			return addZeroR(l)
		case isZeroNum(l): // 0 + a → a
			return zeroAddBits(r)
		case isNumeralLit(l) && isNumeralLit(r): // c1 + c2 → c
			if w, ok := NormNatAdd(l, r); ok {
				return w
			}
		}
		return nil
	}
	if l, r, ok := MatchesStar(t); ok {
		switch {
		case isZeroNum(r): // a * 0 → 0
			return mulZeroR(l)
		case isZeroNum(l): // 0 * a → 0
			return zeroMulNum(r)
		case isOneNum(r): // a * 1 → a
			return mulOneR(l)
		case isOneNum(l): // 1 * a → a
			return oneMulL(r)
		case isNumeralLit(l) && isNumeralLit(r): // c1 * c2 → c
			if w, ok := NormNatMul(l, r); ok {
				return w
			}
		}
		return nil
	}
	if l, r, ok := MatchesMinus(t); ok {
		// Truncated subtraction: cancellation `a−b → d` when a ≥ b,
		// else truncation `a−b → 0` when a ≤ b. Both are sound ring-witnessed
		// rewrites; a mixed-sign monus yields nil (opaque — the decision-layer
		// case split handles it). subCancel reads AddSubLeftCancel; subTrunc reads SubEqZero
		// and LessEqAdd, and rewrites nothing while either field is nil.
		if w := subCancel(l, r); w != nil {
			return w
		}
		return subTrunc(l, r)
	}
	// nat_max/nat_min idempotence: nat_max a a → a, nat_min a a → a (CondId). The
	// contingent nat_max/nat_min cases are decided by the case-split, not simplified here.
	if l, r, ok := MatchesMax(t); ok && l.AlphaEquals(r) {
		return maxIdemp(l)
	}
	if l, r, ok := MatchesMin(t); ok && l.AlphaEquals(r) {
		return minIdemp(l)
	}
	// predecessor n → n - 1: bridge predecessor into the monus layer (suc/0 cases
	// then collapse via subCancel/subTrunc; a symbolic predecessor m is decided by the
	// monus split on m-1).
	if n, ok := MatchesPre(t); ok {
		return preBridge(n)
	}
	// nat_dist(m,n) → (m-n) + (n-m): bridge the num distance into the
	// monus layer (the nat→real lift foundation). Symbolic dist is then decided by
	// the monus split on its two `a-b` atoms; nat_dist(n,n)/nat_dist(0,n) collapse via
	// subCancel/subTrunc.
	if m, n, ok := MatchesDist(t); ok {
		return distBridge(m, n)
	}
	// nat_div/nat_mod trivial simp: nat_div(m, 0)/1, nat_mod(m, 0)/1, nat_mod(n,n).
	// Contingent shapes (nat_div(n,n)→1 needs n≠0, nat_mod(m,n)→m needs m<n) are decided
	// by the symbolic enricher (nat_divmod.go) in proveDecAtom, not here.
	if w := divModSimp(t); w != nil {
		return w
	}
	// nat_pow, the reductions that never grow the term: nat_pow(m, 0) → 1,
	// nat_pow(m, 1) → m, a power of two literals folded to its numeral,
	// nat_pow(1, n) → 1 and nat_pow(0, n) → COND(n = 0, 1, 0). A literal exponent
	// c ≥ 2 over any other base is unfolded only on request (ExpandEXPRewrite).
	if w := expSimp(t); w != nil {
		return w
	}
	// factorial literal evaluation: factorial(c) → c! for literal c. Size-safe
	// (literal → numeral), so it fires here unconditionally; symbolic factorial is opaque.
	if w := factSimp(t); w != nil {
		return w
	}
	return nil
}

// ── Comparison / equality decision leaf ───────────────────────────────────

// proveLinThenInt mirrors OmegaTactic's strategy: try the pure ℚ-Farkas prover
// first (LinProve — no integer leaves), and only fall back to the integer
// extension (OmegaProve) for genuinely integer validities. Without this, even a
// pure-linear decision like `a<a+1` would route through OmegaProve's
// strict→non-strict integer fold and read its leaf (SucLessEqIffLessThan) —
// declining a perfectly sound ℚ rewrite when that isn't supplied.
//
// The answer is memoized per question (natLinMemo, a linProveMemo), as
// RealLinProve's is: the case split asks its branch questions once per atom
// per direction, and the enrichments re-enter with the facts they injected.
func proveLinThenInt(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	hs := slices.Collect(hyps)
	key := linQuestionKey(hs, goal)
	if e, ok := natLinMemo.lookup(key, hs, goal); ok {
		return e.proof, e.proof != nil
	}
	proof, ok := LinProve(slices.Values(hs), goal)
	if !ok {
		proof, ok = OmegaProve(slices.Values(hs), goal)
	}
	if !ok {
		proof = nil
	}
	natLinMemo.store(key, linAnswer{hyps: hs, goal: goal, proof: proof})
	return proof, ok
}

// natLinMemo memoizes proveLinThenInt and natDecMemo proveDecAtom; both are
// released with the step's other memos (ReleaseStepMemos).
var natLinMemo, natDecMemo linProveMemo

// proveDecAtom is the ⊤-direction prover the comparison decider uses: try the
// commutative-semiring normalizer first (RingProveFull — closes nonlinear
// universally-true equalities like `a*b = b*a`, `(a+b)² = a²+2ab+b²`, hyp-free,
// no integer leaves), then fall through to linear/integer. This is what makes
// the decider subsume the old "arith" closer's ring path: a buried `a*b=b*a`
// collapses to ⊤ in place. Ring only proves ⊤-direction for `=` (two
// distinct polys can still be equal under some assignment, so it cannot
// refute), so the ⊥-direction (proveNeg) still uses proveLinThenInt only —
// linear/integer disequalities `2a=1 → ⊥`, etc.
//
// The decision is memoized per question (natDecMemo), as realProveDecAtom's
// is: an arith step decides each hypothesis under the others and each atom
// once and once negated, round after round over one context.
func proveDecAtom(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	hs := slices.Collect(hyps)
	key := linQuestionKey(hs, goal)
	if e, ok := natDecMemo.lookup(key, hs, goal); ok {
		return e.proof, e.proof != nil
	}
	proof, ok := proveDecAtomChain(hs, goal)
	if !ok {
		proof = nil
	}
	natDecMemo.store(key, linAnswer{hyps: hs, goal: goal, proof: proof})
	return proof, ok
}

// proveDecAtomChain is the decide chain behind proveDecAtom.
func proveDecAtomChain(hs []Term, goal Term) (*prop.PropWrapper, bool) {
	if l, r, ok := ext.MatchesEQ(goal); ok && isNat(l) {
		if w, ok := RingProveFull(l, r); ok {
			return w, true
		}
	}
	if w, ok := proveLinThenInt(slices.Values(hs), goal); ok {
		return w, true
	}
	// Parity-hyp enrichment: a nat_even/nat_odd hyp is dropped by the
	// linear core; inject its nat_mod-2 equation as a fact and retry. (The goal-side
	// nat_even/nat_odd is already bridged by parityBridge before we get here.)
	if w, ok := proveLinParity(hs, goal); ok {
		return w, true
	}
	// nat_div/nat_mod enrichment fallback: inject the bounds of every
	// nat_div/nat_mod atom in hyps∪{goal} (divModFacts) and retry linarith.
	// Cheap, sound (the facts are real `Thm`), and useful enough that most
	// opaque-nat_div/nat_mod comparisons close here before reaching the case split.
	divMod := divModFacts(collectDivModAtoms(append(slices.Clone(hs), goal)), hs)
	if len(divMod) > 0 {
		if w, ok := enrichAndCut(
			func(h []Term) (*prop.PropWrapper, bool) { return proveLinThenInt(slices.Values(h), goal) },
			hs, divMod); ok {
			return w, true
		}
	}
	// A product of positive factors is positive and a power that is zero
	// has a zero base (nat_products.go), and a hypothesis whose two sides
	// share a positive factor compares what is left of them
	// (nat_scaling.go): these join the enrichment's facts, for one more
	// linear run and for the split below.
	facts := divMod
	products := append(natPositiveProducts(hs, goal), natZeroPowerFacts(hs)...)
	if products = append(products, natCancelFacts(hs)...); len(products) > 0 {
		facts = append(slices.Clone(divMod), products...)
		if w, ok := enrichAndCut(
			func(h []Term) (*prop.PropWrapper, bool) { return proveLinThenInt(slices.Values(h), goal) },
			hs, facts); ok {
			return w, true
		}
	}
	// A goal that compares two products sharing a factor, or two products
	// factor by factor, follows from the comparison of what is left
	// (nat_scaling.go) — the converse of the cancellation above — and a
	// goal whose scaling by a positive factor the facts prove linearly
	// follows by cancelling the factor.
	if w, ok := enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) {
			if w, ok := natProveScaled(h, goal); ok {
				return w, true
			}
			return natProveCancelled(h, goal)
		},
		hs, facts); ok {
		return w, true
	}
	// Case-split fallback: when the goal has an opaque-to-linarith atom
	// (irreducible monus, nat_max, nat_min) the linear core can't decide, split it on
	// an LE-guard disjunction into `+`-facts and prove each branch. Internal
	// to the prover — returns a single {hyps} ⊢ goal. The branches hold the
	// enrichment's facts: a hypothesis `0 ≠ nat_mod(n, 2)` is read by its
	// split alone and `nat_mod(n, 2) ≤ n` is a fact of the enrichment alone,
	// so `n ≠ 0` follows only where a branch has both; and `0 < a·b` decides
	// `suc(a·b − 1) = a·b` only in the branch of its monus. A branch with
	// nothing left to split that the linear prover leaves open goes to
	// natProveLeaf.
	if w, ok := enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) {
			return proveSplit(proveLinThenInt, natProveLeaf, h, goal, nil)
		},
		hs, facts); ok {
		return w, true
	}
	// Bounded-variable enumeration (nat_exp.go): a comparison atom nonlinear in a
	// literal-bounded variable (`x ≤ c ⊢ x*x ≤ 4`) is decided by enumerating the
	// variable's finitely many values and evaluating each substituted (literal)
	// instance. Reuses the literal simp/eval stack per value.
	if w, ok := proveBoundedEnum(hs, goal); ok {
		return w, true
	}
	// nat_div/nat_mod symbolic-n=0 case-split (last resort): for a nat_div/nat_mod atom with
	// purely-symbolic divisor n (no n=0 / 0<n / n≠0 info in hyps), split on
	// `(n=0) ∨ (0<n)` via PosIffNonzero. The n=0 branch substitutes nat_mod(_,n)=m /
	// nat_div(_,n)=0; the 0<n branch lets the existing Division-class enricher
	// fire. Each branch recurses through proveBranchDecAtom.
	return proveDivModSplitOnZero(hs, goal, nil)
}

// decideCmp decides a single comparison atom P with the given forward prover,
// returning `⊢ P ⇔ ⊤` (P holds under hyps) or `⊢ P ⇔ ⊥` (¬P holds), or
// (nil,false) when neither is derivable. `>`/`≥` are reduced to swapped
// `<`/`≤` through the definitional bridge and the resulting iff is prepended,
// exactly mirroring proveWith's goal handling.
func decideCmp(prove proveFn, hyps iter.Seq[Term], P Term) (*prop.PropWrapper, bool) {
	// a > b  ⇔  b < a   (then decide b<a and chain the bridge).
	if a, b, ok := MatchesGt(P); ok {
		inner, iok := decideCmp(prove, hyps, lt(b, a))
		if !iok {
			return nil, false
		}
		return gtBridge(a, b).EqTrans(inner), true // (a>b)⇔(b<a) ∘ (b<a)⇔V
	}
	if a, b, ok := MatchesGe(P); ok {
		inner, iok := decideCmp(prove, hyps, le(b, a))
		if !iok {
			return nil, false
		}
		return geBridge(a, b).EqTrans(inner), true
	}
	// ⊤: P follows from hyps.
	if pf, ok := prove(hyps, P); ok {
		return eqtIntro(pf), true
	}
	// ⊥: ¬P follows from hyps.
	if npf, ok := proveNeg(prove, hyps, P); ok {
		return eqfIntro(npf), true
	}
	return nil, false
}

// proveNeg builds `⊢ ¬P` by proving P's negation in the comparison fragment the
// forward prover understands, then bridging:
//
//	¬(a<b) ⇔ b≤a   (NotLessThan)   prove b≤a
//	¬(a≤b) ⇔ b<a   (NotLessEq)   prove b<a
//	¬(a=b)  is the ≠ goal      prove ¬(a=b) directly
//
// It does NOT special-case P already being a `≠` (P = ¬(a=b)) — and it needn't:
// the unified deep rewrite descends into the inner `a=a`, decides it ⊤ via
// `decideCmp`'s ⊤-branch, and BoolRewrite (part of BasicRewritesWith) collapses
// `¬⊤ ⇔ ⊥` in the SAME fixpoint pass — no separate trivial-close round needed.
func proveNeg(prove proveFn, hyps iter.Seq[Term], P Term) (*prop.PropWrapper, bool) {
	if a, b, ok := MatchesLt(P); ok { // ¬(a<b) ⇐ b≤a
		g, gok := prove(hyps, le(b, a))
		if !gok {
			return nil, false
		}
		return notLT(a, b).EqSym().EqMP(g), true // (b≤a)⇔¬(a<b) applied to ⊢b≤a
	}
	if a, b, ok := MatchesLe(P); ok { // ¬(a≤b) ⇐ b<a
		g, gok := prove(hyps, lt(b, a))
		if !gok {
			return nil, false
		}
		return notLE(a, b).EqSym().EqMP(g), true
	}
	if a, b, ok := matchNumEq(P); ok { // ¬(a=b) is the ≠ goal
		g, gok := prove(hyps, not(eqT(a, b)))
		if !gok {
			return nil, false
		}
		return g, true
	}
	return nil, false
}

// matchNumEq reports whether P is a num equality `a = b` (not a bool ⇔, not a
// non-num `=`). The num guard mirrors proveWith's isLinear gate.
func matchNumEq(P Term) (Term, Term, bool) {
	a, b, ok := ext.MatchesEQ(P)
	if !ok || !isNat(a) {
		return nil, nil, false
	}
	return a, b, true
}

// arithDecideLeaf is the shallow leaf for atom-level decision under the given
// hyps: returns `⊢ atom ⇔ V` for a decidable comparison/equality, nil for
// anything else (non-atom or contingent atom). Curried so the same body is
// reused across calls with different hyp contexts.
//
// The IsLinComparisonGoal gate is load-bearing, not just an optimization: the
// deep rewrite applies this leaf to EVERY subterm, including bare num terms
// (a `COND`/`nat_max`/`+` node). decideCmp on a non-comparison would fall through to
// proveDecAtom's proveSplit, which — finding that very term as a split candidate —
// can re-enter the deep rewrite via condPin and recurse forever (COND splits its
// own goal). Restricting to comparison/equality atoms confines the splitter to a
// real proposition; buried comparison atoms are still reached, since DeepRewrite
// recurses into subterms and re-applies this leaf at each.
func arithDecideLeaf(hyps []Term) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		if !IsLinComparisonGoal(t) {
			return nil
		}
		if w, ok := decideCmp(proveDecAtom, slices.Values(hyps), t); ok {
			return w
		}
		return nil
	}
}

// factorial layer. factorial is unbounded in general, so linarith
// treats every factorial atom as opaque. The tractable case is a LITERAL argument c:
// unlike nat_pow (whose base stays symbolic, so the unfolding GROWS the term), a
// literal `factorial(c)` evaluates ALL THE WAY to a single numeral `c!` — exactly like
// the literal nat_div/nat_mod evaluator (divmodEval). So this is a size-SAFE simp leaf
// (`factorial(c) → c!`), fired unconditionally from arithSimpStep, with no separate
// agent-controlled surface (cf. nat_pow's ExpandEXPRewrite for the size-growing case).
//
// Bound: factEvalMax caps c at 10 (10! = 3 628 800). Corpus uses are tiny; a large
// c would build a long NormNatMul chain to a many-bit numeral for no real benefit.

const factEvalMax = 10

// factEval proves `⊢ factorial(c) = <c! numeral>` for a literal c ≤ factEvalMax.
// Returns nil when the factorial bundle is unsupplied or c exceeds the cap.
//
//	c=0:  factorial(0) = 1                        [factorial clause 1, projected]
//	c≥1:  factorial(c) = factorial(suc(c-1))           [suc(c-1) = c, congruence]
//	             = suc(c-1) · factorial(c-1)      [factorial clause 2 at n=c-1]
//	             = c · (c-1)!                [congruence: suc(c-1)→c, factorial(c-1)→(c-1)!]
//	             = c!                         [NormNatMul]
func factEval(c uint64) *prop.PropWrapper {
	if factorialThm() == nil || c > factEvalMax {
		return nil
	}
	if c == 0 {
		return factBase() // ⊢ factorial(0) = 1
	}
	inner := factEval(c - 1) // ⊢ factorial(c-1) = (c-1)!
	if inner == nil {
		return nil
	}
	cm1, cNum := Numeral(c-1), Numeral(c)
	prevFact := prop.Rhs(inner) // (c-1)! as a numeral

	// step1: ⊢ factorial(suc(c-1)) = suc(c-1) · factorial(c-1)   [clause 2 at n = c-1]
	step1 := factRecursion2(cm1)
	if step1 == nil {
		return nil
	}
	sucEq := sucBits(cm1) // ⊢ suc(c-1) = c
	if sucEq == nil {
		return nil
	}
	// congFact: ⊢ factorial(suc(c-1)) = factorial(c)   [congruence under factorial(_)]
	congFact := sucEq.LeftApply(natFact)
	// base: ⊢ factorial(c) = suc(c-1) · factorial(c-1)
	base := congFact.EqSym().EqTrans(step1)
	// prodCong: ⊢ suc(c-1)·factorial(c-1) = c · (c-1)!   [left operand, then right]
	leftCong := sucEq.LeftApply(natStar).RightApply(factT(cm1)) // suc(c-1)·factorial(c-1) = c·factorial(c-1)
	rightCong := inner.LeftApply(ext.Apply(natStar, cNum))      // c·factorial(c-1) = c·(c-1)!
	prodCong := leftCong.EqTrans(rightCong)
	// mulEq: ⊢ c · (c-1)! = c!   [numeral multiply]
	mulEq, ok := NormNatMul(cNum, prevFact)
	if !ok {
		return nil
	}
	return base.EqTrans(prodCong).EqTrans(mulEq) // ⊢ factorial(c) = c!
}

// factBase: ⊢ factorial(0) = 1   (factorial recursion clause 1; projectMatch auto-orients
// if the bound statement is reversed).
func factBase() *prop.PropWrapper {
	return clauseLeaf(factorialThm(), nil, factT(natZero), Numeral(1))
}

// factRecursion2: ⊢ factorial(suc n) = suc n · factorial n   (factorial recursion clause 2).
func factRecursion2(n Term) *prop.PropWrapper {
	return clauseLeaf(factorialThm(), nil, factT(sucT(n)), star(sucT(n), factT(n)))
}

// factSimp is the arithSimpStep entry: a LITERAL `factorial(c)` (c ≤ factEvalMax) folds
// to its numeral value. A symbolic argument is left opaque (nil), as is c beyond
// the cap or an unsupplied bundle.
func factSimp(t Term) *prop.PropWrapper {
	n, ok := MatchesFact(t)
	if !ok {
		return nil
	}
	c, ok := BitsToUint(n)
	if !ok {
		return nil
	}
	return factEval(c)
}

// arithBoolLeaf is the deep-rewrite leaf for a contingent boolean combination of
// comparison atoms. Returns `⊢ G ⇔ ⊤` when the case analysis closes G, else nil.
// Placed LAST in ArithDecideWithHyps' leaf list: the cheaper leaves (atom
// decision, binary disj, iff) and BoolRewrite fire first, so this only ever sees
// a boolean whose atoms are individually contingent — the genuine gap.
func arithBoolLeaf(hyps []Term) prop.Rewrite {
	return arithBoolLeafWithPolicy(hyps, UnscopedArithPolicy(), nil)
}

func arithBoolLeafWithPolicy(hyps []Term, policy ArithPolicy, reader *LibraryReader) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		if !isBooleanOverComparisons(t) {
			return nil
		}
		// NOTE — deliberately NO zero-hyp weakening pre-pass here: sound, but it
		// grows this leaf's success set and diverges replay of steps recorded
		// under the old driver — see the full rationale at intArithBoolLeaf.
		if w, ok := proveBoolGoalWithPolicy(hyps, t, nil, policy, reader); ok {
			return eqtIntro(w) // ⊢ (G) ⇔ ⊤
		}
		return nil
	}
}

// isBooleanOverComparisons gates arithBoolLeaf: t has an ∧/∨/⇒/⇔ head (the case
// analysis only buys something for a multi-atom propositional structure) and
// mentions at least one comparison atom. A bare comparison is arithDecideLeaf's
// job; a `¬`-headed goal is left to BoolRewrite/PushNeg (which normalizes it
// into an ∧/∨ this leaf then handles). The `⇔` case is a bool equality (`P⇔Q`,
// both sides bool) — NOT a num equality `a=b`, which is a comparison atom; the
// arithIffLeaf, ordered before this one, has already handled (or declined) a
// `⇔` whose two sides are SINGLE comparisons, so here `⇔` covers iffs between
// compound boolean combinations (`(a≤b ∧ b≤a) ⇔ (a=b)`).
func isBooleanOverComparisons(t Term) bool {
	isBool := false
	if _, _, ok := prop.MatchesAND(t); ok {
		isBool = true
	} else if _, _, ok := prop.MatchesOR(t); ok {
		isBool = true
	} else if _, _, ok := prop.MatchesIMPLY(t); ok {
		isBool = true
	} else if _, _, ok := ext.MatchesIFF(t); ok {
		isBool = true // a `⇔` (bool-typed EQ); a num `=` is a comparison atom
	}
	return isBool && len(comparisonAtomsOf(t)) > 0
}

// proveBoolGoal closes `{hyps} ⊢ goal` by case-splitting on one comparison atom
// and recombining the two branches via ByCases (with proof-core pruning — see
// splitByCases) — the goal-side analogue of proveSplit, with
// comparisonAtomSplit (ExcludedMiddle) as the disjunction.
func proveBoolGoal(hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	return proveBoolGoalWithPolicy(hyps, goal, done, UnscopedArithPolicy(), nil)
}

func proveBoolGoalWithPolicy(hyps []Term, goal Term, done []Term, policy ArithPolicy, reader *LibraryReader) (*prop.PropWrapper, bool) {
	sa, ok := firstComparisonAtomSplit(goal, done)
	if !ok {
		return nil, false
	}
	done = append(slices.Clone(done), sa.atom)
	return splitByCases(sa, hyps, goal,
		func(h []Term) (*prop.PropWrapper, bool) {
			return proveBoolBranchWithPolicy(h, goal, done, policy, reader)
		})
}

// proveBoolBranch closes one split branch (hyps already carry the branch's
// atom-fact). The interleave: collapse the formula under the new hypothesis
// FIRST, so it shrinks before any further split.
//
//   - collapse to ⊤            → branch closed (iffTrueElim);
//   - collapse to ⊥            → goal is false in this (feasible) branch — the
//     goal is not valid, so decline (caller aborts);
//   - collapse to a residual V → recurse on V (smaller), then chain ⊢ G⇔V ∘ ⊢ V;
//   - no collapse, but the linear core now decides it directly → done;
//   - otherwise                → split a further atom.
func proveBoolBranch(hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	return proveBoolBranchWithPolicy(hyps, goal, done, UnscopedArithPolicy(), nil)
}

func proveBoolBranchWithPolicy(hyps []Term, goal Term, done []Term, policy ArithPolicy, reader *LibraryReader) (*prop.PropWrapper, bool) {
	if w := arithCollapseRewriteWithPolicy(hyps, policy, reader)(goal); w != nil {
		v := prop.Rhs(w)
		switch {
		case v.AlphaEquals(prop.T):
			return iffTrueElim(w), true // ⊢ goal ⇔ ⊤  →  ⊢ goal
		case v.AlphaEquals(prop.F):
			return nil, false // goal false under a feasible branch → not valid
		default:
			pf, ok := proveBoolBranchWithPolicy(hyps, v, done, policy, reader)
			if !ok {
				return nil, false
			}
			return prop.WrapProp(w.EqSym().EqMP(pf)), true // (V⇔goal) ∘ ⊢V → ⊢goal
		}
	}
	// No further collapse. The residual may be a bare comparison the linear core
	// decides (after the splits pinned enough atoms), else split another atom.
	if pf, ok := proveDecAtom(slices.Values(hyps), goal); ok {
		return pf, true
	}
	return proveBoolGoalWithPolicy(hyps, goal, done, policy, reader)
}

// firstComparisonAtomSplit returns the ExcludedMiddle split for the first
// not-yet-split comparison atom of goal. Atoms are read from the live goal, so a
// residual that has shed atoms never re-splits a vanished one.
func firstComparisonAtomSplit(goal Term, done []Term) (splittableAtom, bool) {
	for _, a := range comparisonAtomsOf(goal) {
		if slices.ContainsFunc(done, a.AlphaEquals) {
			continue
		}
		return comparisonAtomSplit(a), true
	}
	return splittableAtom{}, false
}

// comparisonAtomSplit builds the ExcludedMiddle split `⊢ A ∨ ¬A` for a
// normalized comparison atom A (`< ≤ =`). The positive branch assumes A; the
// negative branch assumes ¬A and, when A is a `<`/`≤`, additionally bridges ¬A
// to the complementary positive comparison (`negComparison`, NotLessThan/NotLessEq) so
// the linear core can use it — exactly the bridge hypSplittable's `⇒` arm uses.
// For an `=` atom no bridge is needed: decideCmp's proveNeg matches the `¬(a=b)`
// hypothesis directly.
func comparisonAtomSplit(a Term) splittableAtom {
	posFacts := []*prop.PropWrapper{prop.Assume(a)}
	negFacts := []*prop.PropWrapper{prop.Assume(not(a))}
	if _, bridge, ok := negComparison(a); ok {
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

// comparisonAtomsOf collects the distinct positive comparison atoms of t,
// normalizing `>`/`≥` to the swapped `<`/`≤` so the split (and its
// negComparison bridge) operate on the canonical orientation. BINDER-FREE
// only (collectBinderFreeSubterms, as intComparisonAtomsOf): an atom under
// an enclosing ∀/∃/λ is no split candidate, since the deep rewrite renames
// the binder away from the assumed guard and the case never reaches it.
func comparisonAtomsOf(t Term) []Term {
	raw := collectBinderFreeSubterms([]Term{t}, isPositiveCmpAtom)
	var out []Term
	for _, a := range raw {
		n := normalizeCmpAtom(a)
		if !slices.ContainsFunc(out, n.AlphaEquals) {
			out = append(out, n)
		}
	}
	return out
}

// isPositiveCmpAtom matches a positive comparison atom `< ≤ = > ≥` over num — the
// split candidates. (A `≠` is a `¬`-wrapped equality; the split's negative arm
// produces it, so it is never a split target itself.)
func isPositiveCmpAtom(t Term) bool {
	if _, _, ok := MatchesLt(t); ok {
		return true
	}
	if _, _, ok := MatchesLe(t); ok {
		return true
	}
	if _, _, ok := MatchesGt(t); ok {
		return true
	}
	if _, _, ok := MatchesGe(t); ok {
		return true
	}
	if l, _, ok := ext.MatchesEQ(t); ok {
		return isNat(l)
	}
	return false
}

// normalizeCmpAtom rewrites `a > b → b < a` and `a ≥ b → b ≤ a`, leaving
// `< ≤ =` untouched. The goal still contains the `>`/`≥` occurrence; decideCmp's
// gtBridge/geBridge decide it from the swapped atom-hypothesis the split adds.
func normalizeCmpAtom(a Term) Term {
	if x, y, ok := MatchesGt(a); ok {
		return lt(y, x)
	}
	if x, y, ok := MatchesGe(a); ok {
		return le(y, x)
	}
	return a
}

// freeNumVars collects the distinct free num variables of t, via the shared raw
// walker. Small terms only — arith atoms — so the scan is cheap.
func freeNumVars(t Term) []Term {
	return collectRawSubterms([]Term{t}, func(s Term) bool { return isVar(s) && isNat(s) })
}

// isVar reports whether t is a (free) variable.
func isVar(t Term) bool { _, ok := t.AsVar(); return ok }

// Goal-side disjunction closer — the goal-side dual of the
// hypothesis-disjunction split (hypSplittable). A disjunction GOAL
// `g0 ∨ g1` whose disjuncts are num comparisons is closed in one of two ways:
//
//   - DIRECT: one disjunct already follows from the hyps — prove it and
//     introduce the disjunction (ConclOR0/ConclOR1). Closes `{a<b} ⊢ a≤b ∨ Q`.
//   - TOTALITY / TRICHOTOMY: neither disjunct holds universally, but the
//     disjunction is valid — `a≤b ∨ b≤a`, `a≤b ∨ b<a`, `a<b ∨ b≤a`, … Pick a
//     `<`/`≤` pivot disjunct, assume its negation (bridged to the complementary
//     positive comparison via negComparison so the linear core can use it), and
//     close the OTHER disjunct under that assumption; recombine via ExcludedMiddle
//     + ByCases.
//
// This is the gap the deep rewrite's BoolRewrite cannot reach: BoolRewrite only
// collapses `g ∨ ⊤` once a disjunct decides to ⊤, but a totality disjunction has
// no universally-true disjunct, so it would otherwise stay stuck. The leaf lives
// in the SAME fixpoint pass as the atom decider (composed into ArithDecideWithHyps),
// so a disjunction anywhere in the conclusion reduces to ⊤ in place.
//
// Soundness: arithDisjLeaf returns `⊢ (g0∨g1) ⇔ ⊤` only after a real proof of
// `{hyps} ⊢ g0∨g1`, so the equivalence is valid at any position. A sub-proof
// that cannot derive a real cert returns ok=false (the integer-frontier nil
// contract), so the branch is declined rather than relayed.

// arithDisjLeaf is the shallow deep-rewrite leaf for a disjunction goal. Fires
// only when at least one disjunct is a recognized num comparison (the totality /
// direct cases the linear prover can act on); otherwise nil, leaving boolean
// disjunctions to the standard BoolRewrite.
func arithDisjLeaf(hyps []Term) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		g0, g1, ok := prop.MatchesOR(t)
		if !ok {
			return nil
		}
		if !IsLinComparisonGoal(g0) && !IsLinComparisonGoal(g1) {
			return nil
		}
		if w, ok := proveDisj(proveDecAtom, hyps, g0, g1); ok {
			return eqtIntro(w) // ⊢ (g0∨g1) ⇔ ⊤
		}
		return nil
	}
}

// proveDisj closes `{hyps} ⊢ g0 ∨ g1`. Tries, in order: g0 directly, g1
// directly, then the totality structure pivoting on g0, then on g1. Returns
// (nil,false) when none applies (e.g. both disjuncts contingent and neither a
// `<`/`≤` pivot, or the disjunction is simply not valid under the hyps).
func proveDisj(prove proveFn, hyps []Term, g0, g1 Term) (*prop.PropWrapper, bool) {
	// DIRECT: a disjunct already follows from the hyps.
	if w, ok := prove(slices.Values(hyps), g0); ok {
		return prop.ConclOR0(g0, g1).DeriveHypFrom(w), true // {hyps} ⊢ g0∨g1
	}
	if w, ok := prove(slices.Values(hyps), g1); ok {
		return prop.ConclOR1(g0, g1).DeriveHypFrom(w), true
	}
	// TOTALITY: pivot on a `<`/`≤` disjunct, prove the other under its negation.
	if w, ok := pivotDisj(prove, hyps, g0, g1, true); ok { // pivot g0, prove g1
		return w, true
	}
	return pivotDisj(prove, hyps, g0, g1, false) // pivot g1, prove g0
}

// pivotDisj closes `g0 ∨ g1` by ExcludedMiddle on one disjunct (the pivot) and
// proving the other under ¬pivot. `pivotG0=true` pivots on g0 (proving g1);
// `false` pivots on g1 (proving g0). The pivot must be a `<`/`≤` comparison so
// negComparison can bridge ¬pivot to a positive comparison the linear core uses.
func pivotDisj(prove proveFn, hyps []Term, g0, g1 Term, pivotG0 bool) (*prop.PropWrapper, bool) {
	pivot, other := g0, g1
	if !pivotG0 {
		pivot, other = g1, g0
	}
	negPos, bridge, ok := negComparison(pivot) // bridge: {¬pivot} ⊢ negPos
	if !ok {
		return nil, false // pivot not a `<`/`≤` comparison.
	}
	// Prove the OTHER disjunct under the bridged negation.
	w, ok := prove(slices.Values(append(slices.Clone(hyps), negPos)), other)
	if !ok {
		return nil, false
	}
	// {hyps, negPos} ⊢ g0∨g1, then cut the bridge back to {hyps, ¬pivot}.
	introOther := prop.ConclOR1(g0, g1) // {g1} ⊢ g0∨g1   (other == g1 when pivotG0)
	if !pivotG0 {
		introOther = prop.ConclOR0(g0, g1) // {g0} ⊢ g0∨g1
	}
	disjUnderNeg := introOther.DeriveHypFrom(w)                          // {hyps, negPos} ⊢ g0∨g1
	disjUnderNot := prop.WrapProp(bridge.MaybeDeriveTrans(disjUnderNeg)) // {hyps, ¬pivot} ⊢ g0∨g1
	impNeg := disjUnderNot.PromoteHyp(not(pivot))                        // {hyps} ⊢ ¬pivot ⇒ g0∨g1

	// pivot branch: pivot ⇒ g0∨g1 (trivial DisjIntro).
	introPivot := prop.ConclOR0(g0, g1) // {g0} ⊢ g0∨g1   (pivot == g0 when pivotG0)
	if !pivotG0 {
		introPivot = prop.ConclOR1(g0, g1)
	}
	impPos := introPivot.PromoteHyp(pivot) // ⊢ pivot ⇒ g0∨g1

	goal := or(g0, g1)
	return prop.ByCases(goal, pivot, not(pivot)).
		DeriveHypFrom(prop.ExcludedMiddle(pivot)). // pivot ∨ ¬pivot
		DeriveHypFrom(impPos).
		DeriveHypFrom(impNeg), true
}
