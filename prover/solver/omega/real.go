package omega

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Real arithmetic deep rewrite — the ℝ twin of the num arith simplifier-or-
// decider (ArithDecideWithHyps). Same composition shape: prop.BasicRewritesWithEnv folds
// the real arith leaves on top of the standard basic rewrites (β / bool / cond
// / neg / quantifier / hilbert) and drives the whole bundle through the shared
// prop.DeepRewrite — so the cascade iterates to fixpoint across all rules. A
// cascade like `x + Cond(x=x, &0, &1) → x` resolves in one call (decide x=x→⊤
// via RealRingProve, Cond(⊤,&0,&1)→&0 via trivialCondRewrite, x+&0→x via the
// identity leaf), exactly as the num twin does for nat.
//
// The real leaves (realMoveAcrossLeaf, the sub/neg positivization, sits
// between these two):
//
//   - realArithSimpStep — conservative identity-law / numeral fold over ℝ:
//     x+&0→x, &0+x→x, x*&0→&0, &0*x→&0, x*&1→x, &1*x→x, &m+&n→&k, &m*&n→&k.
//     Local, never grows a term — the real analog of a default `simp` set
//     (AddRightId / MulLeftId / …), NOT a ring normal form (that is
//     realNormalizeProof / RealRingProve's job).
//
//   - realArithDecideLeaf — decide a real comparison/equality atom (`<` `≤`
//     `>` `≥` `=`) to ⊤/⊥ under the goal's hyps. Linear comparisons via
//     RealLinProve (ℚ-Farkas), commutative-semiring equalities via
//     RealRingProve (the ⊤ direction, incl. like-term merges).
//
// Soundness: every real leaf is either bundle-sound or, in a non-test build,
// panics at the placeholder seam (no fabricator installed); a contingent real
// atom that fails to decide leaves the leaf returning nil. This matches the num
// side, which also relies purely on ok=false + a full bundle — there is no
// unsound-leaf counter on either side.

// ── identity-fold leaf ──────────────────────────────────────────────────────

// isRealLit reports whether t is a real LITERAL `&n` = real_of_num(<bit-tree>).
// `&k` for a num variable k is real_of_num-shaped but NOT a literal, so the
// numeral-fold guards exclude it (the num evaluator would decline anyway).
func isRealLit(t Term) bool {
	x, ok := MatchesRealOfNum(t)
	return ok && isBitTree(x)
}

func isRealZero(t Term) bool { return t.AlphaEquals(realLit(0)) }

func isRealOne(t Term) bool { return t.AlphaEquals(realLit(1)) }

// The right-identity / left-zero orientations are bundle leaves (real_lemmas.go:
// realAddZeroR `x+&0=x`, realOneMul `&1·x=x`, realZeroMul `&0·x=&0`). Their
// mirror orientations are DERIVED via commutativity (realCommuteADD/MUL, also
// bundle leaves) rather than given their own bundle fields — keeping the bundle
// minimal (the canonical form only ever needs the un-mirrored ones).

// realAddLeftId: ⊢ &0 + a = a   (commute then right-identity).
func realAddLeftId(a Term) *prop.PropWrapper {
	return realCommuteADD(realLit(0), a).EqTrans(realAddZeroR(a))
}

// realMulRid: ⊢ a · &1 = a   (commute then left-identity).
func realMulRid(a Term) *prop.PropWrapper {
	return realCommuteMUL(a, realLit(1)).EqTrans(realOneMul(a))
}

// realMulRzero: ⊢ a · &0 = &0   (commute then left-zero).
func realMulRzero(a Term) *prop.PropWrapper {
	return realCommuteMUL(a, realLit(0)).EqTrans(realZeroMul(a))
}

// realArithSimpStep is the one-level (shallow) identity-fold rewrite: inspects
// t's head operator and returns the matching identity leaf or numeral fold, or
// nil when t is not a reducible real `+`/`*` redex. DeepRewrite drives it deep
// + to fixpoint. realArithSimpStepHypSafe is the hyp-pre-simp variant (omits
// realSquarePosSimp, which destroys the canonical nonzero shape downstream
// handlers consume — see realSquarePosSimp's docstring).
func realArithSimpStep(t Term) *prop.PropWrapper {
	if w := realArithSimpStepHypSafe(t); w != nil {
		return w
	}
	if w := realSquarePosSimp(t); w != nil { // ~(x=&0) → &0 < x·x  (SquarePos, goal-only)
		return w
	}
	return nil
}

// realArithSimpStepHypSafe is realArithSimpStep WITHOUT the goal-only
// realSquarePosSimp clause. Used by the hyp pre-simp in RealArithDecideWithHyps.
func realArithSimpStepHypSafe(t Term) *prop.PropWrapper {
	if w := realAbsSgnSimp(t); w != nil { // abs/sgn algebraic laws (push abs/sgn to leaves)
		return w
	}
	if w := realInvSimp(t); w != nil { // inv algebraic laws (push inv to leaves)
		return w
	}
	if w := realInvSignSimp(t); w != nil { // inv sign monotonicity (atom rewrite)
		return w
	}
	if w := realPowSimp(t); w != nil { // real_pow m c → product chain (literal c ≤ 1)
		return w
	}
	if w := realPowLawSimp(t); w != nil { // pow distribution: (·) pow n / &1 pow n / (·^m)^n
		return w
	}
	if w := realAbsLessEqIffPowTwoLessEqSimp(t); w != nil { // x^2 ≤ y^2 → |x| ≤ |y|  (AbsLessEqIffPowTwoLessEq)
		return w
	}
	if x, b, ok := MatchesRealDiv(t); ok && isRealOne(b) { // x / &1 → x
		return realDivOne(x)
	}
	if w := realClearLiteralDivSimp(t); w != nil { // (x/&k ⋈ y) → (x ⋈ y·&k)
		return w
	}
	if a, ok := MatchesRealInv(t); ok && isRealOne(a) { // inv &1 → &1
		return realInvOne()
	}
	if a, ok := MatchesRealSgn(t); ok && isRealZero(a) { // real_sgn &0 → &0
		return realEqLeaf(realSgnOfZeroThm(), nil, realSgnT(realLit(0)), realLit(0))
	}
	if l, r, ok := realDomain.matchPlus(t); ok {
		switch {
		case isRealZero(r): // x + &0 → x
			return realAddZeroR(l)
		case isRealZero(l): // &0 + x → x
			return realAddLeftId(r)
		case isRealLit(l) && isRealLit(r): // &m + &n → &k
			if w, ok := realNormNatAdd(l, r); ok {
				return w
			}
		}
		return nil
	}
	if l, r, ok := realDomain.matchStar(t); ok {
		switch {
		case isRealZero(r): // x * &0 → &0
			return realMulRzero(l)
		case isRealZero(l): // &0 * x → &0
			return realZeroMul(r)
		case isRealOne(r): // x * &1 → x
			return realMulRid(l)
		case isRealOne(l): // &1 * x → x
			return realOneMul(r)
		case isRealLit(l) && isRealLit(r): // &m * &n → &k
			if w, ok := realNormNatMul(l, r); ok {
				return w
			}
		}
		return nil
	}
	return nil
}

// ── comparison / equality decision leaf ─────────────────────────────────────

// isRealComparisonGoal reports whether t is a real comparison/equality atom
// (the gate the decide leaf applies before attempting a decision — the ℝ twin
// of IsLinComparisonGoal). The isRealTerm guard on the `=` / `≠` cases keeps a
// bool `⇔` or a non-real `=` out.
func isRealComparisonGoal(t Term) bool {
	if _, _, ok := realDomain.matchLt(t); ok {
		return true
	}
	if _, _, ok := realDomain.matchLe(t); ok {
		return true
	}
	if _, _, ok := realDomain.matchGt(t); ok {
		return true
	}
	if _, _, ok := realDomain.matchGe(t); ok {
		return true
	}
	if l, _, ok := ext.MatchesEQ(t); ok {
		return isRealTerm(l)
	}
	if inner := ext.MatchesNOT(t); inner != nil {
		if l, _, ok := ext.MatchesEQ(inner); ok {
			return isRealTerm(l)
		}
	}
	return false
}

// matchRealEq reports whether P is a real equality `a = b` (not a bool ⇔, not a
// non-real `=`).
func matchRealEq(P Term) (Term, Term, bool) {
	a, b, ok := ext.MatchesEQ(P)
	if !ok || !isRealTerm(a) {
		return nil, nil, false
	}
	return a, b, true
}

// realProveDecAtom is the ⊤-direction prover the real decider uses (the real twin
// of intProveDecAtom): the ring normalizer first for an `=` atom (RealRingProveFull
// closes universally-true real equalities incl. nonlinear products and like-term
// merges, hyp-free), then the linear forward prover (RealLinProve — `<` `≤` `=` `≠`
// and `>`/`≥` via its definitional bridge), then the sign-known nonlinear fragment
// (monotone scaling / sign-of-product / integral domain), the hypothesis-side
// positive-factor cancellation, and the case-split fallback. ℝ has no integer
// divmod/divides/discreteness/enumeration fallbacks — those are int-only.
//
// The decision is memoized per question (realDecMemo, a linProveMemo): it is
// a function of the hypotheses, the goal and the lemma bundle, and the
// engine's arith step asks the same questions over and over — each
// hypothesis decided under the others, each atom once and once negated, the
// enrichments re-entering with the facts they injected. On the
// thirteen-hypothesis ε-δ context of TestInspect_ArithProbeOnWideRealContext
// seven decisions in eight had been made before (6 000 calls, 767
// questions), and a decision that fails walks the whole chain.
func realProveDecAtom(hyps iter.Seq[Term], goal Term) (*prop.PropWrapper, bool) {
	hs := slices.Collect(hyps)
	key := linQuestionKey(hs, goal)
	if e, ok := realDecMemo.lookup(key, hs, goal); ok {
		return e.proof, e.proof != nil
	}
	proof, ok := realProveDecAtomChain(hs, goal)
	if !ok {
		proof = nil
	}
	realDecMemo.store(key, linAnswer{hyps: hs, goal: goal, proof: proof})
	return proof, ok
}

// realDecMemo memoizes realProveDecAtom; dropped with the constraint memos.
var realDecMemo linProveMemo

// realProveDecAtomChain is the decide chain behind realProveDecAtom.
func realProveDecAtomChain(hs []Term, goal Term) (*prop.PropWrapper, bool) {
	// Hyp echo: a goal that is literally a hypothesis closes directly, before
	// any extraction — the cheapest close for an atom the field/monotone layers
	// reduce a goal to (`x·z ≤ y`) when that atom is resident verbatim.
	if slices.ContainsFunc(hs, goal.AlphaEquals) {
		return prop.Assume(goal), true
	}
	// A quotient by a numeral is a linear unknown once its defining
	// equation `y = (y/&k)·&k` is resident, and a monomial that multiplies
	// it is one once that equation times the cofactor is
	// (real_quotient.go): inject them for every literal quotient the
	// sequent mentions and run the whole chain over the enriched set.
	// Re-entry finds every equation resident and falls through.
	if facts := realQuotientFacts(hs, goal); len(facts) > 0 {
		return enrichAndCut(func(h []Term) (*prop.PropWrapper, bool) {
			return realProveDecAtom(slices.Values(h), goal)
		}, hs, facts)
	}
	if l, r, ok := ext.MatchesEQ(goal); ok && isRealTerm(l) {
		if w, ok := RealRingProveFull(l, r); ok {
			return w, true
		}
	}
	// A factor and its inverse cancel wherever they stand in a monomial,
	// once the unit fact is resident for each cofactor in sight
	// (real_unit_facts.go). After the hyp-free ring, which needs no fact;
	// re-entry finds every fact resident and falls through.
	if facts := realUnitFacts(hs, goal); len(facts) > 0 {
		return enrichAndCut(func(h []Term) (*prop.PropWrapper, bool) {
			return realProveDecAtom(slices.Values(h), goal)
		}, hs, facts)
	}
	if w, ok := RealLinProve(slices.Values(hs), goal); ok {
		return w, true
	}
	// Monotone scaling / sign-of-product (real_ops.go): a nonlinear `c·a ⋈ c·b`
	// or `&0 ⋈ x·y` whose sign/order side conditions discharge from the hyps —
	// `a≤b ∧ &0≤c ⊢ c·a≤c·b`, `&0≤x ∧ &0≤y ⊢ &0≤x·y`.
	if w, ok := realProveMonotone(hs, goal); ok {
		return w, true
	}
	// Field layer (realProveDivField): inverse cancellation (`y·inv y → &1` for y≠&0)
	// and denominator clearing (`x ⋈ y/z` → `x·z ⋈ y` under z's sign). No-op when
	// the goal carries no real_div/real_inv structure.
	if w, ok := realProveDivField(hs, goal); ok {
		return w, true
	}
	// real_pow sign: `&0 ≤ x pow n` from `&0 ≤ x` (PowNonneg), the
	// no-hyp `&0 ≤ x pow 2` (PowTwoNonneg), `&0 < x pow n` from `&0 < x` (PowPos).
	if w, ok := realProvePowSign(hs, goal); ok {
		return w, true
	}
	// real_pow base monotonicity (real_ops.go): `x^n ⋈ y^n` from `&0 ≤ x ∧ x ⋈ y`
	// — PowMonoBase / PowMonoBaseStrict. Sub-RCF (sign-known nonlinear).
	if w, ok := realProvePowBaseMono(hs, goal); ok {
		return w, true
	}
	// real_pow exponent monotonicity: `x^m ≤ x^n` from `&1 ≤ x ∧ m ≤ n`
	// — PowMonoExp.
	if w, ok := realProvePowExpMono(hs, goal); ok {
		return w, true
	}
	// abs triangle inequality: `|t1 + (... + tn)| ≤ rhs` via iterated
	// AbsTriangle + linarith on the abs-sum bound.
	if w, ok := realProveAbsTriangle(hs, goal); ok {
		return w, true
	}
	// No-hyp square nonnegativity (real_ops.go): `&0 ≤ x·x` (SquareNonneg) —
	// where realProveMonotone, needing factor-sign hyps, declines.
	if w, ok := realProveSquareNonneg(goal); ok {
		return w, true
	}
	// Abs nonnegativity (real_ops.go): `&0 ≤ real_abs t` via AbsNonneg. Closes
	// the bare `&0 ≤ |x|` directly (preempting the abs case split) and powers the
	// sign-of-product side-condition discharge for `&0 ≤ |x|·|y|` below.
	if w, ok := realProveAbsNonneg(goal); ok {
		return w, true
	}
	// Strict square positivity (real_ops.go): `x ≠ &0 ⊢ &0 < x·x` — the
	// trichotomy split + strict sign-of-product per branch.
	if w, ok := realProveStrictSquare(hs, goal); ok {
		return w, true
	}
	// real_of_num homomorphism collapse (real_ops.go): a goal whose sides are
	// `&`-coerced num images — `&n·&n = &(n·n)`, `&0 ≤ &n` — that linarith and the
	// ring miss (`&n` is opaque, real atoms have no default ≥0). Hyp-free;
	// the num facts reach the rows through the cast (domain.go liftHyp).
	if w, ok := realProveOfNum(goal); ok {
		return w, true
	}
	// Integral-domain square (real_ops.go): a hyp `x·x = &0` forces `x = &0`
	// (MulEqZero collapses `x=&0 ∨ x=&0` via (p∨p)⇔p — no case split). The
	// distinct-factor `x·y=&0` form is the splittable hyp below.
	if w, ok := realProveMulEqZeroSquare(hs, goal); ok {
		return w, true
	}
	// A hypothesis that a power is zero puts its base at zero
	// (real_nonzero.go): the converse of a power's nonzero evidence.
	if w, ok := realProveZeroPower(hs, goal); ok {
		return w, true
	}
	// Positive-factor cancellation from a HYPOTHESIS (real_cancel.go): a hyp
	// `P·a ⋈ P·b` (or `a·P ⋈ b·P`) whose factor is provably `&0 < P` yields the
	// cancelled `a ⋈ b`, injected as an extra hyp for one linear run and cut back.
	// The converse of the goal-side monotone scaling, and outside the Farkas
	// fragment by construction (cancelling scales a premise by a VARIABLE).
	// Declines on a pure structural scan when no hyp compares two products, so a
	// goal without one pays a walk of the hyp list; placed last before the split
	// so nothing an earlier handler already closes changes route, and so the
	// cheap cancellation is tried before the exponential case-split fallback.
	if w, ok := realProveCancelMul(hs, goal); ok {
		return w, true
	}
	// The pairwise products of the context's differences (real_products.go) —
	// the nlinarith step: `x·y = &1 ∧ &0 < x ⊢ &0 < y`, `a ≤ b ∧ c ≤ d ⊢ a·d +
	// b·c ≤ a·c + b·d`. One FOIL per pair, so it runs only once everything
	// above has declined, and only where a constraint carries a product.
	if w, ok := realProveProducts(hs, goal); ok {
		return w, true
	}
	// Case-split fallback (real_ops.go): when the goal/hyps carry an
	// opaque-to-linarith operator (real_abs / real_max / real_min / real_sgn / raw
	// COND) or a disjunctive/≠/⇒/product-zero hypothesis, split it and prove each
	// branch (the branches use the linear forward prover, and realProveLeaf where
	// nothing is left to split; −x branches flow through the signed normalizer).
	return realProveSplit(RealLinProve, realProveLeaf, hs, goal, nil)
}

// realProveNeg builds `⊢ ¬P` by proving P's negation in the real comparison
// fragment, then bridging (mirror of proveNeg):
//
//	¬(a<b) ⇐ b≤a   (NotLessThan)
//	¬(a≤b) ⇐ b<a   (NotLessEq)
//	¬(a=b)  is the ≠ goal      prove ¬(a=b) directly
func realProveNeg(prove proveFn, hyps iter.Seq[Term], P Term) (*prop.PropWrapper, bool) {
	if a, b, ok := realDomain.matchLt(P); ok { // ¬(a<b) ⇐ b≤a
		g, gok := prove(hyps, realLeT(b, a))
		if !gok {
			return nil, false
		}
		return realNotLT(a, b).EqSym().EqMP(g), true
	}
	if a, b, ok := realDomain.matchLe(P); ok { // ¬(a≤b) ⇐ b<a
		g, gok := prove(hyps, realLtT(b, a))
		if !gok {
			return nil, false
		}
		return realNotLE(a, b).EqSym().EqMP(g), true
	}
	if a, b, ok := matchRealEq(P); ok { // ¬(a=b) is the ≠ goal
		g, gok := prove(hyps, not(eqT(a, b)))
		if !gok {
			return nil, false
		}
		return g, true
	}
	return nil, false
}

// realDecideCmp decides a single real comparison atom P (mirror of decideCmp):
// `⊢ P ⇔ ⊤` (P holds under hyps) or `⊢ P ⇔ ⊥` (¬P holds), or (nil,false). The
// `>` / `≥` atoms reduce to swapped `<` / `≤` through the definitional bridge,
// the resulting iff prepended.
func realDecideCmp(prove proveFn, hyps iter.Seq[Term], P Term) (*prop.PropWrapper, bool) {
	if a, b, ok := realDomain.matchGt(P); ok { // a>b ⇔ b<a
		inner, iok := realDecideCmp(prove, hyps, realLtT(b, a))
		if !iok {
			return nil, false
		}
		return realGtBridge(a, b).EqTrans(inner), true
	}
	if a, b, ok := realDomain.matchGe(P); ok { // a≥b ⇔ b≤a
		inner, iok := realDecideCmp(prove, hyps, realLeT(b, a))
		if !iok {
			return nil, false
		}
		return realGeBridge(a, b).EqTrans(inner), true
	}
	if pf, ok := prove(hyps, P); ok { // ⊤: P follows from hyps
		return eqtIntro(pf), true
	}
	if npf, ok := realProveNeg(prove, hyps, P); ok { // ⊥: ¬P follows
		return eqfIntro(npf), true
	}
	return nil, false
}

// realArithDecideLeaf is the shallow atom-decision leaf under `hyps`: returns
// `⊢ atom ⇔ V` for a decidable real comparison/equality, nil otherwise. The
// isRealComparisonGoal gate confines the decider to real propositions (the deep
// rewrite applies this to every subterm).
func realArithDecideLeaf(hyps []Term) prop.Rewrite {
	return realArithDecideLeafWith(hyps, realProveDecAtom)
}

// realArithDecideLeafWith is realArithDecideLeaf deciding through prove:
// the atom prover of the policy the leaf is composed under.
func realArithDecideLeafWith(hyps []Term, prove proveFn) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		if !isRealComparisonGoal(t) {
			return nil
		}
		if w, ok := realDecideCmp(prove, slices.Values(hyps), t); ok {
			return w
		}
		return nil
	}
}

// ── the unified deep+fixpoint rewrite ───────────────────────────────────────

// realMoveAcrossLeaf is the ℝ twin of intMoveAcrossLeaf: it pushes
// total subtraction/negation across a real comparison/equality into the positive
// two-sided atom the decide leaf then handles. nil on a positive atom.
func realMoveAcrossLeaf(t Term) *prop.PropWrapper { return realSubneg.moveAcrossCmp(t) }

// RealArithDecideWithHyps is the PUBLIC entry — pre-simp + decider + bridge.
// Hyp pre-simp (engine.go preSimpHyps): fold each hyp through the SAME hyp-free
// leaves the goal-side stack uses (realArithSimpStep + realMoveAcrossLeaf + the
// standard basic rewrites), so abs/sgn / pow / div / numeral / identity / sub-
// neg-move-across folds reach a hyp before linarith's shallow
// parseHypConstraint atomizes whatever survives. Hyp-free → no "other hyps
// only" discipline needed; a hyp the rewrite leaves untouched passes through
// with a nil bridge (zero kernel work). DecideLeaf gets the SIMPLIFIED hyp
// set; bridgeBackHyps cuts each h' back to its original h so the result's
// hyps stay ⊆ the original (IsStronger contract).
//
// Recursive internal callers (realCondPin, etc.) use realArithDecideWithHypsRaw
// — see intArithDecideWithHypsRaw for the rationale (pre-simp can fold an
// augmented branch-pin hyp to ⊤ and break identity-keyed termination
// invariants downstream).
func RealArithDecideWithHyps(hyps []Term) prop.Rewrite {
	// Hyp-pre-simp uses realArithSimpStepHypSafe (omits realSquarePosSimp's
	// `~(x=&0) → &0 < x·x` rewrite) — goal-only rewrites that destroy a
	// canonical shape downstream hyp-readers depend on must stay off the hyp
	// side, the same shape of carve-out d9350352 applies to intMoveAcrossLeaf.
	hypFreeSimp := prop.BasicRewritesWith(realArithSimpStepHypSafe, realMoveAcrossLeaf)
	simplifiedHyps, bridges := preSimpHyps(hyps, hypFreeSimp)
	raw := withCompoundEqSubst(hyps, realArithDecideWithHypsRaw(simplifiedHyps))
	return func(t Term) *prop.PropWrapper {
		w := raw(t)
		if w == nil {
			return nil
		}
		return bridgeBackHyps(w, bridges)
	}
}

// realArithDecideWithHypsRaw is RealArithDecideWithHyps WITHOUT the hyp pre-
// simp pass, for recursive INTERNAL callers (realCondPin and any future case-
// split arm that injects a pin) that augment the hyp set and need the added
// hyp's AlphaEquals identity to survive the recursion. The int twin is
// intArithDecideWithHypsRaw.
//
// It is the unified real arith deep rewrite under `hyps`: the standard basic
// rewrites (β / bool / cond / neg / quantifier / hilbert) PLUS the identity-fold
// leaf PLUS the move-across PLUS atom decision, all driven to fixpoint by the
// shared capture-aware DeepRewrite. Returns a Rewrite producing `⊢ t = t'`
// (the simplified conclusion), or nil when nothing reduces. `hyps` empty → the
// hyp-free decider (universally-valid/false atoms only). A COND whose guard
// or negated guard is a hyp is read at that arm first, as in the unified
// stack (composeArithLeaves).
func realArithDecideWithHypsRaw(hyps []Term) prop.Rewrite {
	anyHyp := func(pred func(prop.Term) bool) bool { return slices.ContainsFunc(hyps, pred) }
	return prop.BasicRewritesWithEnv(anyHyp,
		eqHypValues(hyps, isRealTerm, ArithPolicy{Real: true}), prop.CondDecideByHyps(anyHyp),
		realArithSimpStep, realMoveAcrossLeaf, realArithDecideLeaf(hyps))
}

// RealArithDecide is the hyp-free entry point: the unified deep+fixpoint real
// rewrite with no hyps. Returns `⊢ t = t'`, or nil when nothing reduces.
func RealArithDecide(t Term) *prop.PropWrapper { return RealArithDecideWithHyps(nil)(t) }

// RealArithEnabled reports whether real arith dispatch is live — i.e. a real
// bundle is installed (the same gate composeArithLeaves uses). The engine's
// arith shape gate ANDs this with IsRealArithContent so the move is offered on a
// real goal only when it can actually act on it, never offer-then-decline in
// production (which installs only the nat bundle).
func RealArithEnabled() bool { return realLemmaBundle != nil }

// IsRealArithContent reports whether s is real-arith content the unified
// decider's real leaves can act on — a real `+`/`*` subterm or a real
// comparison atom. Structural only (no bundle check); the engine pairs it with
// RealArithEnabled. The ℝ analogue of the omega.MatchesPlus/MatchesStar/
// IsLinComparisonGoal trio the nat shape gate uses.
func IsRealArithContent(s Term) bool {
	if _, _, ok := realDomain.matchPlus(s); ok {
		return true
	}
	if _, _, ok := realDomain.matchStar(s); ok {
		return true
	}
	return isRealComparisonGoal(s)
}

// ── Formula-level bool split over ℝ ─────────────────────────────────────────
//
// The formula-level case-split decider of nat.go (arithBoolLeaf), over the real
// comparison atoms. It closes the QF-LRA-validity-modulo-boolean-structure gap for ℝ: a goal whose
// validity is propositional over several contingent real comparison atoms —
// `(x≤y ⇒ x≤z) ∨ (z<y)`, the real trichotomy `(x<y) ∨ (x=y) ∨ (y<x)` — has no
// atom that decides alone, so realArithDecideLeaf / arithDisjLeaf decline; this
// closes it by case analysis.
//
// Almost everything is SHARED with the nat path, not re-derived: the
// case-split structs (splittableAtom / splitBranch), enrichAndCut, the
// collectRawSubterms walker, and the ByCases / ExcludedMiddle recombination are
// type-generic; the branch collapse is arithCollapseRewrite (composeArithLeaves
// with no bool leaf), which dispatches real atoms (the gated real leaves
// live in composeArithLeaves, engine.go) — and excluding the bool leaves there is
// what bounds the split recursion, for nat and real alike. Only the atom-domain
// primitives differ: real comparison matchers, the real `¬A → complementary`
// bridge (NotLessThan/NotLessEq), and the real forward decider (realProveDecAtom).
//
// Wiring: realArithBoolLeaf is added (gated) as a trailing `extra` leaf of
// ArithDecideWithHyps alongside the nat arithBoolLeaf, so it is excluded from
// arithCollapseRewrite — the split recursion is driven by its own `done` set,
// never by re-entering itself.

// realArithBoolLeaf is the deep-rewrite leaf for a contingent boolean
// combination of real comparison atoms. Returns `⊢ G ⇔ ⊤` when the case
// analysis closes G, else nil. Placed after the cheaper real leaves so it only
// sees a boolean whose real atoms are individually contingent.
func realArithBoolLeaf(hyps []Term) prop.Rewrite {
	return realArithBoolLeafWithPolicy(hyps, UnscopedArithPolicy(), nil)
}

func realArithBoolLeafWithPolicy(hyps []Term, policy ArithPolicy, reader *LibraryReader) prop.Rewrite {
	return func(t Term) *prop.PropWrapper {
		if !isRealBooleanOverComparisons(t) {
			return nil
		}
		// NOTE — deliberately NO zero-hyp weakening pre-pass here: sound, but it
		// grows this leaf's success set and diverges replay of steps recorded
		// under the old driver — see the full rationale at intArithBoolLeaf.
		if w, ok := realProveBoolGoalWithPolicy(hyps, t, nil, policy, reader); ok {
			return eqtIntro(w) // ⊢ (G) ⇔ ⊤
		}
		return nil
	}
}

// isRealBooleanOverComparisons gates realArithBoolLeaf: t has an ∧/∨/⇒/⇔ head
// and mentions at least one REAL comparison atom (mirror of
// isBooleanOverComparisons).
func isRealBooleanOverComparisons(t Term) bool {
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
	return isBool && len(realComparisonAtomsOf(t)) > 0
}

// realProveBoolGoal closes `{hyps} ⊢ goal` by case-splitting on one real
// comparison atom and recombining via ByCases with proof-core pruning (mirror
// of proveBoolGoal; see splitByCases).
func realProveBoolGoal(hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	return realProveBoolGoalWithPolicy(hyps, goal, done, UnscopedArithPolicy(), nil)
}

func realProveBoolGoalWithPolicy(hyps []Term, goal Term, done []Term, policy ArithPolicy, reader *LibraryReader) (*prop.PropWrapper, bool) {
	sa, ok := firstRealComparisonAtomSplit(goal, done)
	if !ok {
		return nil, false
	}
	done = append(slices.Clone(done), sa.atom)
	return splitByCases(sa, hyps, goal,
		func(h []Term) (*prop.PropWrapper, bool) {
			return realProveBoolBranchWithPolicy(h, goal, done, policy, reader)
		})
}

// realProveBoolBranch closes one split branch (mirror of proveBoolBranch):
// collapse the formula under the new hypothesis FIRST (via the shared
// arithCollapseRewrite, which dispatches real), so it shrinks before any further
// split; ⊤ closes, ⊥ aborts (goal not valid in a feasible branch), a residual
// recurses, else the linear core decides directly or a further atom splits.
func realProveBoolBranch(hyps []Term, goal Term, done []Term) (*prop.PropWrapper, bool) {
	return realProveBoolBranchWithPolicy(hyps, goal, done, UnscopedArithPolicy(), nil)
}

func realProveBoolBranchWithPolicy(hyps []Term, goal Term, done []Term, policy ArithPolicy, reader *LibraryReader) (*prop.PropWrapper, bool) {
	if w := arithCollapseRewriteWithPolicy(hyps, policy, reader)(goal); w != nil {
		v := prop.Rhs(w)
		switch {
		case v.AlphaEquals(prop.T):
			return iffTrueElim(w), true // ⊢ goal ⇔ ⊤  →  ⊢ goal
		case v.AlphaEquals(prop.F):
			return nil, false // goal false under a feasible branch → not valid
		default:
			pf, ok := realProveBoolBranchWithPolicy(hyps, v, done, policy, reader)
			if !ok {
				return nil, false
			}
			return prop.WrapProp(w.EqSym().EqMP(pf)), true // (V⇔goal) ∘ ⊢V → ⊢goal
		}
	}
	// No further collapse. The residual may be a bare real comparison the linear
	// core decides (after the splits pinned enough atoms), else split another atom.
	if pf, ok := policy.realProver(reader)(slices.Values(hyps), goal); ok {
		return pf, true
	}
	return realProveBoolGoalWithPolicy(hyps, goal, done, policy, reader)
}

// firstRealComparisonAtomSplit returns the ExcludedMiddle split for the first
// not-yet-split real comparison atom of goal (mirror of firstComparisonAtomSplit).
func firstRealComparisonAtomSplit(goal Term, done []Term) (splittableAtom, bool) {
	for _, a := range realComparisonAtomsOf(goal) {
		if slices.ContainsFunc(done, a.AlphaEquals) {
			continue
		}
		return realComparisonAtomSplit(a), true
	}
	return splittableAtom{}, false
}

// realComparisonAtomSplit builds `⊢ A ∨ ¬A` for a normalized real comparison
// atom A (mirror of comparisonAtomSplit); the negative branch bridges ¬A to the
// complementary comparison via realNegComparison (NotLessThan/NotLessEq). For an `=`
// atom no bridge is needed — realProveNeg matches the `¬(a=b)` hyp directly.
func realComparisonAtomSplit(a Term) splittableAtom {
	posFacts := []*prop.PropWrapper{prop.Assume(a)}
	negFacts := []*prop.PropWrapper{prop.Assume(not(a))}
	if _, bridge, ok := realNegComparison(a); ok {
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

// realNegComparison bridges `¬A` to the complementary positive comparison for a
// real `<`/`≤` atom (mirror of negComparison, via NotLessThan/NotLessEq). ok=false for
// an `=` atom (no bridge needed).
func realNegComparison(guard Term) (negPos Term, bridge *prop.PropWrapper, ok bool) {
	if u, v, m := realDomain.matchLt(guard); m {
		return realLeT(v, u), realNotLT(u, v).LeftAssume(), true // {¬(u<v)} ⊢ v≤u
	}
	if u, v, m := realDomain.matchLe(guard); m {
		return realLtT(v, u), realNotLE(u, v).LeftAssume(), true // {¬(u≤v)} ⊢ v<u
	}
	return nil, nil, false
}

// realComparisonAtomsOf collects the distinct positive real comparison atoms of
// t, normalizing `>`/`≥` to swapped `<`/`≤` (mirror of comparisonAtomsOf /
// intComparisonAtomsOf). BINDER-FREE only (collectBinderFreeSubterms): an atom
// mentioning a variable bound by an enclosing ∀/∃/λ is no split candidate —
// the deep rewrite renames the binder away from the assumed guard, so the
// case never reaches the atom it was split for, and the branch only spends
// a level. This also gates isRealBooleanOverComparisons: a boolean whose only
// comparison atoms sit under binders does not trigger the bool-split leaf.
func realComparisonAtomsOf(t Term) []Term {
	raw := collectBinderFreeSubterms([]Term{t}, isRealPositiveCmpAtom)
	var out []Term
	for _, a := range raw {
		n := realNormalizeCmpAtom(a)
		if !slices.ContainsFunc(out, n.AlphaEquals) {
			out = append(out, n)
		}
	}
	return out
}

// isRealPositiveCmpAtom matches a positive real comparison atom `< ≤ = > ≥`
// (mirror of isPositiveCmpAtom).
func isRealPositiveCmpAtom(t Term) bool {
	if _, _, ok := realDomain.matchLt(t); ok {
		return true
	}
	if _, _, ok := realDomain.matchLe(t); ok {
		return true
	}
	if _, _, ok := realDomain.matchGt(t); ok {
		return true
	}
	if _, _, ok := realDomain.matchGe(t); ok {
		return true
	}
	if l, _, ok := ext.MatchesEQ(t); ok {
		return isRealTerm(l)
	}
	return false
}

// realNormalizeCmpAtom rewrites `a > b → b < a` and `a ≥ b → b ≤ a`, leaving
// `< ≤ =` untouched (mirror of normalizeCmpAtom).
func realNormalizeCmpAtom(a Term) Term {
	if x, y, ok := realDomain.matchGt(a); ok {
		return realLtT(y, x)
	}
	if x, y, ok := realDomain.matchGe(a); ok {
		return realLeT(y, x)
	}
	return a
}
