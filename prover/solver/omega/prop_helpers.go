package omega

import (
	"slices"
	"strconv"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// Domain-generic kernel-rule helpers — pure wrappers over `prop` / `ext`
// machinery (no num/real/int dependency). The ∃-elimination rule for discharging an
// existential, and the fresh-variable utility its freshness side condition
// relies on. Consumed cross-domain: by the int-side Image sign split and
// int_divides skolemize, and by the real-side symbolic-nat_even pow-nonneg handler.

// chooseElim discharges an existential (the ∃-elimination rule). Given:
//   - existsProof: `{Γ} ⊢ ∃v. body[v]`,
//   - the fresh var v (the abstraction's binder, free in NEITHER goal nor the
//     other hyps of branchProof),
//   - the body,
//   - branchProof: `{Δ, body[v]} ⊢ goal`,
//
// it returns `{Γ, Δ} ⊢ goal`. The ε-witness `εv.body` is substituted ONLY into
// branchProof's `body[v]` hyp (v is fresh elsewhere), so goal/Δ are untouched;
// SelectExists then supplies `⊢ body[εv]` to discharge it.
//
// Pin-unused tolerance: the branch prover may have closed WITHOUT consuming
// the skolemized pin `body[v]` — it found an independent route. (Reproduced:
// `gcd ∣ abs(m·n) ⊢ abs(m·n) = gcd·int_div(abs(m·n), gcd)` — the div enrichment
// closes this directly from the divides hyp, so intDividesSkolem's
// `abs = gcd·ν` pin goes unused, and the strict DeriveTrans below panicked
// "Should not happen." on the discharge fold — the arith/auto_with/rw
// engine fault on div/abs/gcd goals.) In that case there is no existential
// to discharge: v is fresh by construction, so a pin-free proof is v-free,
// and branchProof already is a `{Δ} ⊢ goal` with Δ ⊆ the caller's hyps —
// return it unchanged. ONLY this exact case is tolerated: a proof still
// carrying v anywhere (a pin DEFORMED by a normalizer rather than unused)
// falls through to the strict path and keeps failing loudly, so genuine
// pin-roundtrip bugs stay visible.
func chooseElim(existsProof *prop.PropWrapper, v *ext.TermWrapper, body Term, branchProof *prop.PropWrapper) *prop.PropWrapper {
	if !branchProof.HasHyp(body) && !sequentContainsVar(branchProof, v) {
		return branchProof
	}
	absP := v.To(body)
	selected := prop.SelectExists(absP).DeriveHypFrom(existsProof) // {Γ} ⊢ body[v := εv]
	eps := v.SuchThat(body)                                        // εv. body
	branchInst := branchProof.TermInst(ext.MakeTermSubst(v, eps))  // {Δ, body[εv]} ⊢ goal
	return selected.DeriveTrans(branchInst)                        // {Γ, Δ} ⊢ goal
}

// sequentContainsVar reports whether v occurs as a raw var subterm anywhere in
// the proof's sequent (conclusion or any hypothesis). The chooseElim
// pin-unused guard: a branch proof that never consumed the pin cannot mention
// the fresh v at all.
func sequentContainsVar(p *prop.PropWrapper, v *ext.TermWrapper) bool {
	terms := append(slices.Collect(p.HypIter()), p.Conclusion())
	return slices.ContainsFunc(collectRawSubterms(terms, isVar), v.AlphaEquals)
}

// freshVar returns a variable of the given type free in none of the given terms —
// the ∃-elimination freshness side condition (so the TermInst inside chooseElim touches
// only the body hyp, never goal or hyps). Matched by AlphaEquals, exactly the
// (name,type) identity the substitution keys on.
func freshVar(terms []Term, ty core.HolType) *ext.TermWrapper {
	var frees []Term
	for _, t := range terms {
		frees = append(frees, collectRawSubterms([]Term{t}, isVar)...)
	}
	for i := 0; ; i++ {
		cand := ext.Var(ext.TermName("ν"+strconv.Itoa(i)), ty)
		if !slices.ContainsFunc(frees, cand.AlphaEquals) {
			return cand
		}
	}
}

// freshNumVar is freshVar at the num type (the Image skolem var n:num, the
// EvenIffDouble skolem var m:num, etc.).
func freshNumVar(terms []Term) *ext.TermWrapper { return freshVar(terms, dsl.NumType) }

// disjSyllogism: given `⊢ p ∨ q` and `⊢ ¬X` where X is one of the disjuncts,
// returns `⊢` the OTHER disjunct via ByCases — the refuted branch contradicts
// ¬X (ex falso), the surviving branch is identity. Orientation-agnostic: ¬X may
// negate the LEFT or the RIGHT disjunct (the right case is normalized via
// CommuteOR), so callers need not pre-arrange the refuted disjunct to the left.
// nil when disj is not an ∨, notOne is not a ¬, or ¬X negates neither disjunct.
func disjSyllogism(disj, notOne *prop.PropWrapper) *prop.PropWrapper {
	p, q, ok := prop.MatchesOR(disj.Conclusion())
	if !ok {
		return nil
	}
	neg := prop.MatchesNOT(notOne.Conclusion())
	if neg == nil {
		return nil
	}
	switch {
	case neg.AlphaEquals(p): // refute the left disjunct — the base case below.
	case neg.AlphaEquals(q): // refute the right: commute to (q ∨ p) so it is left.
		disj = prop.CommuteOR(p, q).EqMP(disj) // ⊢ q ∨ p
		p, q = q, p
	default:
		return nil
	}
	// Now ¬p is notOne; p branch: {hyps, p} ⊢ ⊥ via Contradict(p); ⊥ ⊢ q via FalseDerives.
	contra := prop.WrapProp(prop.Contradict(p).DeriveHypFrom(prop.Assume(p)))
	contra = prop.WrapProp(notOne.MaybeDeriveTrans(contra)) // ⊢ ⊥ from {hyps, p}
	impP := contra.DeriveTrans(prop.FalseDerives(q)).PromoteHyp(p)
	impQ := prop.Assume(q).PromoteHyp(q)
	return prop.ByCases(q, p, q).
		DeriveHypFrom(disj).
		DeriveHypFrom(impP).
		DeriveHypFrom(impQ)
}
