package omega

import (
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// The ring normal form as a REWRITE — Lean's `ring_nf` beside the closer
// `ring` is here as RingProveFull. The closer proves `⊢ l = r` and says
// nothing about a term that is not one side of an equation; the rewrite
// puts every arithmetic subterm of a goal — a summand of an inequality, an
// argument of a function, a term under a binder — into the one spelling
// the ring normalizer reads (ring.go normalizeProof: a sum of monomials,
// each a numeral coefficient times a sorted product of atoms, the
// constant last), so two spellings of one polynomial meet as one term
// for every step that follows, the refuter and a cited law included.
//
// The spelling is the canonical form read for people: a unit
// coefficient and a zero constant are elided (`1·a + 0` is written `a`,
// `2·(a·b) + 0` is `2·(a·b)`), proved from the vocabulary's own identity
// leaves (oneMul, addZeroR). A term already in that spelling is left
// alone, and so is every piece of one — `2·(a·b)`, `a·b`, `a` — which is
// what lets the deep rewrite terminate at the normal form instead of
// re-reading the pieces it just wrote.
//
// What it reads is what the normalizer reads: `+`, `·`, numerals, a
// literal-exponent power (the pow basis) and, over ℝ, a quotient (the
// quotient basis); subtraction and negation stay atoms, as linOf leaves
// them — the signed normalizer is the hypothesis-side machinery and is
// not a rewrite of a term.

// RingNormalizeRewrite is the `ring_nf` rewrite: deep over the term,
// firing at every arithmetic subterm (num, int or real) whose pretty
// normal form differs from its spelling.
func RingNormalizeRewrite() prop.Rewrite {
	return RingNormalizeRewriteWithPolicy(UnscopedArithPolicy())
}

// RingNormalizeRewriteWithPolicy is RingNormalizeRewrite under a lexical
// arith policy: a carrier the policy withholds (an arith-foundation
// entry's own) is left as written. The policy's Stop is polled before
// each subterm is read: one subterm's normal form is the unit a cut
// waits for.
func RingNormalizeRewriteWithPolicy(policy ArithPolicy) prop.Rewrite {
	stop := utils.Stopper(policy.Stop)
	return prop.DeepRewrite(func(t Term) *prop.PropWrapper {
		if stop != nil {
			stop("inside ring_nf, before a subterm is normalized")
		}
		return ringNormalizeLeaf(t, policy)
	})
}

// ringNormalizeLeaf proves `⊢ t = pretty(t)` for an arithmetic t not
// already in its pretty normal form; nil otherwise, and nil for a term
// the normalizer declines (a non-literal numeral) or a carrier the policy
// withholds.
func ringNormalizeLeaf(t Term, policy ArithPolicy) *prop.PropWrapper {
	v := ringVocabOf(t, policy)
	if v == nil {
		return nil
	}
	lf, w, ok := v.normalizeProof(t)
	if !ok {
		return nil
	}
	pretty := v.prettyTerm(lf)
	if pretty.Equals(t) {
		return nil
	}
	return w.EqTrans(v.prettyProof(lf)) // ⊢ t = canonical = pretty
}

// ringVocabOf is the ring vocabulary of t's carrier, nil off the three
// and nil for a carrier the policy withholds. The leaves read their
// bundles as every omega leaf does: a field no theorem backs panics in
// production and fabricates under the test seam.
func ringVocabOf(t Term, policy ArithPolicy) *ringVocab {
	switch {
	case natDomain.isElem(t) && policy.Nat:
		return natRing
	case realDomain.isElem(t) && policy.Real:
		return realRing
	case intDomain.isElem(t) && policy.Int:
		return intRing
	}
	return nil
}

// prettyMono is the monomial as read: its atom alone under a unit
// coefficient, `coeff·atom` otherwise.
func (v *ringVocab) prettyMono(m monomialL) Term {
	if m.coeff.isOne() {
		return m.atom
	}
	return v.dom.star(v.dom.numeral(m.coeff), m.atom)
}

// prettyTerm is buildTerm's spelling with unit coefficients and a zero
// constant elided; a form with no monomial is its constant.
func (v *ringVocab) prettyTerm(lf linForm) Term {
	if len(lf.monos) == 0 {
		return v.dom.numeral(lf.konst)
	}
	res := v.prettyMono(lf.monos[0])
	for _, m := range lf.monos[1:] {
		res = v.dom.plus(res, v.prettyMono(m))
	}
	if !lf.konst.isZero() {
		res = v.dom.plus(res, v.dom.numeral(lf.konst))
	}
	return res
}

// prettyProof proves `⊢ buildTerm(lf) = prettyTerm(lf)`, summand by
// summand along the canonical term's left-nested spine: oneMul drops a
// unit coefficient, addZeroR the trailing zero.
func (v *ringVocab) prettyProof(lf linForm) *prop.PropWrapper {
	if len(lf.monos) == 0 {
		return prop.Refl(v.dom.numeral(lf.konst))
	}
	mono := func(m monomialL) *prop.PropWrapper {
		if m.coeff.isOne() {
			return v.oneMul(m.atom) // ⊢ 1·atom = atom
		}
		return prop.Refl(v.dom.star(v.dom.numeral(m.coeff), m.atom))
	}
	acc := mono(lf.monos[0]) // ⊢ s₁ = p₁
	for _, m := range lf.monos[1:] {
		acc = acc.LeftApply(v.plusOp).Apply(mono(m)) // ⊢ S + s = P + p
	}
	k := v.dom.numeral(lf.konst)
	acc = acc.LeftApply(v.plusOp).Apply(prop.Refl(k)) // ⊢ S + k = P + k
	if lf.konst.isZero() {
		pretty := v.prettyTerm(linForm{monos: lf.monos}) // P, the sum without its constant
		acc = acc.EqTrans(v.addZeroR(pretty))            // ⊢ P + 0 = P
	}
	return acc
}
