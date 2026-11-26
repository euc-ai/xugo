package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Cancelling a positive factor out of a HYPOTHESIS — the converse of the
// goal-side monotone scaling (real_ops.go realMonoScaleLeft/Right, which turns
// `a ⋈ b` into `c·a ⋈ c·b`). Since the monomial-basis landing the linear layer
// reads `P·a` and `P·b` as two distinct monomial UNKNOWNS, so the row
// `P·a ⋈ P·b` says nothing at all about `a ⋈ b`: relating them means scaling a
// premise by a VARIABLE, which no Farkas combination over the basis supplies.
// It has to be a handler, and it is a HYPOTHESIS-side enrichment — derive the
// cancelled comparison, hand it to the linear prover, cut it back (engine.go
// enrichAndCut, the same shape the divmod/parity bound injections use).
//
// The sign side condition is STRICT — `&0 < P`, never `&0 ≤ P`. `&0·a ≤ &0·b`
// holds for every a and b, so a nonnegative factor cancels nothing; the four
// cancellation theorems (left and right factor, `≤` and `<`) all state the strict premise,
// and realCancelFacts discharges exactly that.

// realCancelMulLeft turns a hypothesis proof `Γh ⊢ c·a ⋈ c·b` plus a sign proof
// `Γs ⊢ &0 < c` into `Γh ∪ Γs ⊢ a ⋈ b`, through LessEqCancelMulLeft (⋈ = ≤) /
// LessThanCancelMulLeft (⋈ = <), whose curried shape is
//
//	∀c a b. (&0 < c) ⇒ (c·a ⋈ c·b) ⇒ (a ⋈ b)
//
// (binder order [c, a, b], c the cancelled factor — the realMonoScaleLeft
// order, so the two directions instantiate their lemmas identically).
func realCancelMulLeft(sign, scaled *prop.PropWrapper, c, a, b Term, strict bool) *prop.PropWrapper {
	relT, thm := realLeT, realLessEqCancelMulLeftThm()
	if strict {
		relT, thm = realLtT, realLessThanCancelMulLeftThm()
	}
	imp := realImplyLeaf(thm, []Term{c, a, b},
		imply(realLtT(realLit(0), c), imply(relT(realStarT(c, a), realStarT(c, b)), relT(a, b))))
	return mp(mp(imp, sign), scaled) // ⊢ a ⋈ b
}

// realCancelCommuteBoth builds `⊢ (a·c ⋈ b·c) = (c·a ⋈ c·b)` — the RIGHT-factor
// spelling read as the left one, so the right-factor cancellation needs no
// bundle field of its own (the mirror of what realMonoScaleRight does on the
// goal side, run in the opposite direction).
func realCancelCommuteBoth(c, a, b Term, strict bool) *prop.PropWrapper {
	rel := realLe
	if strict {
		rel = realLt
	}
	cb, ac := realStarT(c, b), realStarT(a, c)
	// (c·a ⋈ c·b) = (a·c ⋈ c·b) = (a·c ⋈ b·c), then read right-to-left.
	cong := realCommuteMUL(c, a).LeftApply(rel).RightApply(cb).
		EqTrans(realCommuteMUL(c, b).LeftApply(ext.Apply(rel, ac)))
	return cong.EqSym()
}

// realCancelCandidate is one hypothesis whose two sides are products sharing a
// factor: `{h} ⊢ factor·left ⋈ factor·right`, already commuted into the LEFT
// spelling, plus the cancelled comparison the handler wants to add.
type realCancelCandidate struct {
	factor, left, right Term
	strict              bool
	scaled              *prop.PropWrapper // {h} ⊢ factor·left ⋈ factor·right
	cancelled           Term              // left ⋈ right
}

// realCancelPositive reads a hypothesis as `{h} ⊢ l ⋈ r` with ⋈ ∈ {≤, <}. A
// `≥` / `>` hypothesis bridges to the swapped `≤` / `<` (realGeBridge /
// realGtBridge) so the capability does not depend on how the fact was spelled —
// the same reconciliation hypConstraints makes for negated comparisons.
// ok=false when h is not a real `<`/`≤`/`>`/`≥` comparison.
func realCancelPositive(h Term) (l, r Term, strict bool, proof *prop.PropWrapper, ok bool) {
	if a, b, m := realDomain.matchLe(h); m {
		return a, b, false, prop.Assume(h), true
	}
	if a, b, m := realDomain.matchLt(h); m {
		return a, b, true, prop.Assume(h), true
	}
	if a, b, m := realDomain.matchGe(h); m { // (a ≥ b) ⇒ (b ≤ a)
		return b, a, false, realGeBridge(a, b).EqMP(prop.Assume(h)), true
	}
	if a, b, m := realDomain.matchGt(h); m { // (a > b) ⇒ (b < a)
		return b, a, true, realGtBridge(a, b).EqMP(prop.Assume(h)), true
	}
	return nil, nil, false, nil, false
}

// realCancelCandidates is the CHEAP DECLINE: a purely structural scan of the
// hypotheses for the `P·a ⋈ P·b` / `a·P ⋈ b·P` shape. No sign is discharged and
// no lemma is instantiated here, so a goal whose hypotheses carry no
// product-vs-product comparison costs one walk of the hyp list. A candidate
// whose cancelled comparison is already resident is dropped — enriching with a
// fact the prover already has is pure cost.
func realCancelCandidates(hyps []Term) []realCancelCandidate {
	var out []realCancelCandidate
	for _, h := range hyps {
		l, r, strict, base, ok := realCancelPositive(h)
		if !ok {
			continue
		}
		la, ra, okL := realDomain.matchStar(l)
		lb, rb, okR := realDomain.matchStar(r)
		if !okL || !okR {
			continue
		}
		cand := realCancelCandidate{strict: strict}
		switch {
		case la.AlphaEquals(lb): // P·a ⋈ P·b — the shared factor is on the left.
			cand.factor, cand.left, cand.right, cand.scaled = la, ra, rb, base
		case ra.AlphaEquals(rb): // a·P ⋈ b·P — commute both sides into the left form.
			cand.factor, cand.left, cand.right = ra, la, lb
			cand.scaled = realCancelCommuteBoth(ra, la, lb, strict).EqMP(base)
		default:
			continue
		}
		relT := realLeT
		if strict {
			relT = realLtT
		}
		cand.cancelled = relT(cand.left, cand.right)
		if slices.ContainsFunc(hyps, cand.cancelled.AlphaEquals) {
			continue
		}
		out = append(out, cand)
	}
	return out
}

// realCancelFacts discharges each candidate's sign side condition `&0 < P`
// against the ORIGINAL hypotheses (through realProveFactorSign — linarith over
// the resident facts via realLinProveSigned, and for a factor that is itself a
// product the sign-of-product descent down its factor tree, the same discharge
// the goal-side sign handlers use — never the full decider, which would
// recurse) and returns the derived `Γ ⊢ a ⋈ b`. Each
// fact's hypotheses are the sign proof's (⊆ hyps) plus the one product
// hypothesis it cancelled (∈ hyps), so every fact is provable from hyps alone —
// which is what lets enrichAndCut's cut-back leave the result's hypotheses ⊆ the
// goal's (the IsStronger contract). A candidate whose factor has no derivable
// STRICT positivity is dropped, silently and soundly.
func realCancelFacts(hyps []Term) []*prop.PropWrapper {
	var facts []*prop.PropWrapper
	for _, cand := range realCancelCandidates(hyps) {
		sign, ok := realProveFactorSign(hyps, cand.factor, true) // Γ ⊢ &0 < P
		if !ok {
			continue
		}
		facts = append(facts,
			realCancelMulLeft(sign, cand.scaled, cand.factor, cand.left, cand.right, cand.strict))
	}
	return facts
}

// An EQUATION cancels a factor on weaker evidence: `P·a = P·b` gives `a = b`
// wherever P is not zero, whatever its sign (MulEqCancel). The evidence is
// realProveNeqZero's — a disequation as written or in its square form, a
// sign, a resident fact P = &0 would contradict — so `x ≠ &0`, which the
// arith step holds as `&0 < x·x`, cancels x as `&0 < x` does. The two sides
// are read by the factors they share (shared_factors.go), one factor
// cancelled at a time, each on its own evidence.

// realCancelEquation cancels from eq, `Γ ⊢ l = r`, every factor its two
// sides share that hyps show not zero: `Γ′ ⊢ l′ = r′`, Γ′ ⊆ Γ ∪ hyps. nil
// where no factor cancels.
func realCancelEquation(hyps []Term, eq *prop.PropWrapper) *prop.PropWrapper {
	var cancelled *prop.PropWrapper
	for {
		l, r, _ := ext.MatchesEQ(eq.Conclusion())
		shared, restL, restR := realDomain.sharedFactors(l, r)
		step := func() *prop.PropWrapper {
			for i, f := range shared {
				others := slices.Concat(shared[:i], shared[i+1:])
				a := realDomain.productOf(slices.Concat(others, restL))
				b := realDomain.productOf(slices.Concat(others, restR))
				if a.AlphaEquals(b) {
					continue
				}
				nonzero := realProveNeqZero(hyps, f) // Γ ⊢ ¬(f = &0)
				if nonzero == nil {
					continue
				}
				scaled := eqT(realStarT(f, a), realStarT(f, b))
				// The equation in the law's spelling: one linear row, read
				// up to the order and the grouping of the factors.
				spelled, ok := RealLinProve(slices.Values([]Term{eq.Conclusion()}), scaled)
				if !ok {
					continue
				}
				spelled = prop.WrapProp(eq.MaybeDeriveTrans(spelled)) // Γ ⊢ f·a = f·b
				law := realEqLeaf(realMulEqCancelThm(), []Term{f, a, b},
					scaled, or(eqT(f, realLit(0)), eqT(a, b)))
				return disjSyllogism(law.EqMP(spelled), nonzero) // Γ ⊢ a = b
			}
			return nil
		}()
		if step == nil {
			return cancelled
		}
		eq, cancelled = step, step
	}
}

// realCancelEquations lists the cancelled equation of each equation
// hypothesis whose two sides share a factor shown not zero, less those a
// hypothesis already states.
//
// A UNIT FACT is passed over: `R·(inv t · t) = R` shares R between its
// sides, and what cancelling R leaves is the statement that t and its
// inverse multiply to one, which the fact exists to say at the cofactor R
// (real_unit_facts.go). A field-heavy decision holds one such equation per
// cofactor in sight, and the evidence asked for each factor of each would
// be most of what the decision costs.
//
// The evidence search reads every hypothesis, and one context is decided
// against many targets, so the answer for a hypothesis under its context
// is kept for the arith step (realCancelMemo, ReleaseStepMemos).
func realCancelEquations(hyps []Term) []*prop.PropWrapper {
	if realMulEqCancelThm() == nil {
		return nil
	}
	var facts []*prop.PropWrapper
	for _, h := range hyps {
		l, r, ok := matchRealEq(h)
		if !ok {
			continue
		}
		shared, restL, restR := realDomain.sharedFactors(l, r)
		if len(shared) == 0 || realHoldsUnitPair(restL) || realHoldsUnitPair(restR) {
			continue
		}
		key := linQuestionKey(hyps, h)
		e, known := realCancelMemo.lookup(key, hyps, h)
		if !known {
			e = linAnswer{hyps: hyps, goal: h, proof: realCancelEquation(hyps, prop.Assume(h))}
			realCancelMemo.store(key, e)
		}
		if e.proof == nil || slices.ContainsFunc(hyps, e.proof.Conclusion().AlphaEquals) {
			continue
		}
		facts = append(facts, e.proof)
	}
	return facts
}

// realCancelMemo holds, for an equation hypothesis under a context, the
// equation its cancellation leaves, or that it leaves none.
var realCancelMemo linProveMemo

// realHoldsUnitPair reports whether factors hold a term beside its own
// inverse.
func realHoldsUnitPair(factors []Term) bool {
	for _, f := range factors {
		if t, ok := MatchesRealInv(f); ok && slices.ContainsFunc(factors, t.AlphaEquals) {
			return true
		}
	}
	return false
}

// realProveCancelMul proves `{hyps} ⊢ goal` by cancelling a positive factor out
// of every product-comparison hypothesis that admits one and a factor that is
// not zero out of every equation hypothesis that admits one, injecting the
// cancelled comparisons as extra hypotheses, running the LINEAR prover on the
// enriched set, and cutting the injected facts back (enrichAndCut). So
//
//	&0 < p, p·a ≤ p·b ⊢ a ≤ b
//
// closes: `p·a` and `p·b` are two unrelated monomial unknowns to linarith, and
// the row that relates them — a premise scaled by the VARIABLE p — is outside
// the Farkas fragment by construction.
//
// The enriched prover is deliberately the linear one (plus the signed
// move-across and the abs leaf, i.e. realLinProveSigned): the cancelled
// comparisons are ordinary linear rows, and keeping the decider out of the
// enriched run is what makes the handler non-recursive. nil/false when no
// hypothesis has the shape, when no factor's evidence discharges, or
// when the enriched linear run still does not close the goal.
func realProveCancelMul(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	facts := append(realCancelFacts(hyps), realCancelEquations(hyps)...)
	if len(facts) == 0 {
		return nil, false
	}
	return enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) { return realLinProveSigned(h, goal) },
		hyps, facts)
}
