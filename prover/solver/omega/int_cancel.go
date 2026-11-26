package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Cancelling a positive factor out of a HYPOTHESIS over ℤ — the twin of
// real_cancel.go, and the converse of the goal-side monotone scaling
// (intMonoScaleLeft/Right). Since the monomial basis the linear layer reads
// `P·a` and `P·b` as two distinct monomial UNKNOWNS, so the row `P·a ⋈ P·b`
// says nothing about `a ⋈ b`: relating them scales a premise by a VARIABLE,
// which no Farkas combination over the basis supplies.
//
// The sign side condition is STRICT — `&0 < P`, never `&0 ≤ P`, since
// `&0·a ≤ &0·b` holds for every a and b.
//
// ℤ states neither cancellation law natively; the bundle fields are the REAL
// pair lifted through IntOfRealThm at install time (serve/int_bundle.go).

// intProveFactorSign proves `{hyps} ⊢ &0 ⋈ f` for a factor f: the linear
// prover first, and for a factor that is itself a product the sign-of-product
// descent down its factor tree. Never the full decider — that would recurse
// through the handler that calls this. Mirror of realProveFactorSign.
func intProveFactorSign(hyps []Term, f Term, strict bool) (*prop.PropWrapper, bool) {
	relT := intLeT
	if strict {
		relT = intLtT
	}
	if w, ok := intLinProveSigned(hyps, relT(intLit(0), f)); ok {
		return w, true
	}
	if p, q, ok := intDomain.matchStar(f); ok {
		return intProveSignedProduct(hyps, p, q, true, strict)
	}
	return nil, false
}

// intCancelMulLeft turns a hypothesis proof `Γh ⊢ c·a ⋈ c·b` plus a sign proof
// `Γs ⊢ &0 < c` into `Γh ∪ Γs ⊢ a ⋈ b`, through LessEqCancelMulLeft (⋈ = ≤) /
// LessThanCancelMulLeft (⋈ = <), whose curried shape is
//
//	∀c a b. (&0 < c) ⇒ (c·a ⋈ c·b) ⇒ (a ⋈ b)
//
// (binder order [c, a, b], c the cancelled factor — the intMonoScaleLeft
// order, so the two directions instantiate their lemmas identically).
func intCancelMulLeft(sign, scaled *prop.PropWrapper, c, a, b Term, strict bool) *prop.PropWrapper {
	relT, thm := intLeT, intLessEqCancelMulLeftThm()
	if strict {
		relT, thm = intLtT, intLessThanCancelMulLeftThm()
	}
	imp := intImplyLeaf(thm, []Term{c, a, b},
		imply(intLtT(intLit(0), c), imply(relT(intStarT(c, a), intStarT(c, b)), relT(a, b))))
	return mp(mp(imp, sign), scaled) // ⊢ a ⋈ b
}

// intCancelCommuteBoth builds `⊢ (a·c ⋈ b·c) = (c·a ⋈ c·b)` — the RIGHT-factor
// spelling read as the left one, so the right-factor cancellation needs no
// bundle field of its own.
func intCancelCommuteBoth(c, a, b Term, strict bool) *prop.PropWrapper {
	rel := intLe
	if strict {
		rel = intLt
	}
	cb, ac := intStarT(c, b), intStarT(a, c)
	cong := intCommuteMUL(c, a).LeftApply(rel).RightApply(cb).
		EqTrans(intCommuteMUL(c, b).LeftApply(ext.Apply(rel, ac)))
	return cong.EqSym()
}

// intCancelCandidate is one hypothesis whose two sides are products sharing a
// factor, already commuted into the LEFT spelling.
type intCancelCandidate struct {
	factor, left, right Term
	strict              bool
	scaled              *prop.PropWrapper // {h} ⊢ factor·left ⋈ factor·right
	cancelled           Term              // left ⋈ right
}

// intCancelPositive reads a hypothesis as `{h} ⊢ l ⋈ r` with ⋈ ∈ {≤, <}. A
// `≥` / `>` hypothesis bridges to the swapped form, so the capability does not
// depend on how the fact was spelled. ok=false when h is not a comparison.
func intCancelPositive(h Term) (l, r Term, strict bool, proof *prop.PropWrapper, ok bool) {
	if a, b, m := intDomain.matchLe(h); m {
		return a, b, false, prop.Assume(h), true
	}
	if a, b, m := intDomain.matchLt(h); m {
		return a, b, true, prop.Assume(h), true
	}
	if a, b, m := intDomain.matchGe(h); m { // (a ≥ b) ⇒ (b ≤ a)
		return b, a, false, intGeBridge(a, b).EqMP(prop.Assume(h)), true
	}
	if a, b, m := intDomain.matchGt(h); m { // (a > b) ⇒ (b < a)
		return b, a, true, intGtBridge(a, b).EqMP(prop.Assume(h)), true
	}
	return nil, nil, false, nil, false
}

// intCancelCandidates is the CHEAP DECLINE: a purely structural scan of the
// hypotheses for the `P·a ⋈ P·b` / `a·P ⋈ b·P` shape. No sign is discharged and
// no lemma instantiated, so a goal whose hypotheses carry no
// product-vs-product comparison costs one walk of the hyp list. A candidate
// whose cancelled comparison is already resident is dropped.
func intCancelCandidates(hyps []Term) []intCancelCandidate {
	var out []intCancelCandidate
	for _, h := range hyps {
		l, r, strict, base, ok := intCancelPositive(h)
		if !ok {
			continue
		}
		la, ra, okL := intDomain.matchStar(l)
		lb, rb, okR := intDomain.matchStar(r)
		if !okL || !okR {
			continue
		}
		cand := intCancelCandidate{strict: strict}
		switch {
		case la.AlphaEquals(lb): // P·a ⋈ P·b
			cand.factor, cand.left, cand.right, cand.scaled = la, ra, rb, base
		case ra.AlphaEquals(rb): // a·P ⋈ b·P — commute both sides into the left form
			cand.factor, cand.left, cand.right = ra, la, lb
			cand.scaled = intCancelCommuteBoth(ra, la, lb, strict).EqMP(base)
		default:
			continue
		}
		relT := intLeT
		if strict {
			relT = intLtT
		}
		cand.cancelled = relT(cand.left, cand.right)
		if slices.ContainsFunc(hyps, cand.cancelled.AlphaEquals) {
			continue
		}
		out = append(out, cand)
	}
	return out
}

// intCancelFacts discharges each candidate's sign side condition `&0 < P`
// against the ORIGINAL hypotheses and returns the derived `Γ ⊢ a ⋈ b`. Each
// fact's hypotheses are the sign proof's (⊆ hyps) plus the one product
// hypothesis it cancelled (∈ hyps), which is what lets enrichAndCut's cut-back
// leave the result's hypotheses ⊆ the goal's. A candidate whose factor has no
// derivable STRICT positivity is dropped, silently and soundly.
func intCancelFacts(hyps []Term) []*prop.PropWrapper {
	var facts []*prop.PropWrapper
	for _, cand := range intCancelCandidates(hyps) {
		sign, ok := intProveFactorSign(hyps, cand.factor, true) // Γ ⊢ &0 < P
		if !ok {
			continue
		}
		facts = append(facts,
			intCancelMulLeft(sign, cand.scaled, cand.factor, cand.left, cand.right, cand.strict))
	}
	return facts
}

// intProveCancelMul proves `{hyps} ⊢ goal` by cancelling a positive factor out
// of every product-comparison hypothesis that admits one, injecting the
// cancelled comparisons, running the LINEAR prover on the enriched set, and
// cutting the injected facts back. The enriched prover is deliberately the
// linear one (plus the signed move-across), which is what makes the handler
// non-recursive.
func intProveCancelMul(hyps []Term, goal Term) (*prop.PropWrapper, bool) {
	facts := intCancelFacts(hyps)
	if len(facts) == 0 {
		return nil, false
	}
	return enrichAndCut(
		func(h []Term) (*prop.PropWrapper, bool) { return intLinProveSigned(h, goal) },
		hyps, facts)
}
