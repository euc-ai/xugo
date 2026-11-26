package omega

import "github.com/euc-ai/xugo/ext/prop"

// The cast basis: a cast of a num sum, product or successor, written in a
// real or int term, read as the sum or product of the casts it denotes —
// `&(m + 1)` as `&m + &1`, `&(a * b)` as `&a * &b` — so that `&m` and
// `&(m + 1)` are one unknown and a constant apart in the linear layer and
// not two unknowns: `&m ≤ A ∧ A + &1 < B ⊢ &(m + 1) < B` is linear.
//
// It is the quotient basis's move (quotient_basis.go): the TERM is
// untouched, only its reading changes, in the readers that must agree —
// the model (domain.go linOf) and the certificate (ring.go normalizeProof
// and normalizeFull). A num hypothesis lifted to the carrier was already
// written over the casts of its leaves (liftNumHyp's pushCast); this is
// the same reading for a cast the author wrote, so the two meet.
//
// The cast is a homomorphism of + and *, and no more is read: a cast of a
// truncated difference `&(a - b)` is not `&a - &b`, a cast of a power is
// the pow handlers' (the of_num bridge spells it `&(m ^ n)`), and a cast
// of a variable or of any other num term is the unknown it was. A cast of
// a literal is asLiteral's, ahead of the basis.
//
// The split is read only where its bridge is bound (OfNumAdd, OfNumMul;
// the successor needs num's Add1 as well): a proof that runs without one
// reads the cast as before.
//
// A comparison whose sides are casts throughout is still dropped to its
// num statement and decided there (realProveOfNum, intProveOfNum): that
// is a decision of the atom, taken before any linear reading.
func init() {
	realDomain.castSplit = castSplitter(MatchesRealOfNum, realOfNumT, realPlusT, realStarT,
		func() bool { return realOfNumAddThm() != nil }, func() bool { return realOfNumMulThm() != nil })
	realRing.castUnfold = castUnfolder(MatchesRealOfNum, realOfNum, realOfNumAddLeaf, realOfNumMulLeaf)
	intDomain.castSplit = castSplitter(MatchesIntOfNum, intOfNumT, intPlusT, intStarT,
		func() bool { return intOfNumAddThm() != nil }, func() bool { return intOfNumMulThm() != nil })
	intRing.castUnfold = castUnfolder(MatchesIntOfNum, intOfNum, intOfNumAddLeaf, intOfNumMulLeaf)
}

// castSplitter is a domain's castSplit: match recognizes the cast, img
// builds it, and addBound / mulBound report whether the bridge a split
// is proved by is bound.
func castSplitter(match func(Term) (Term, bool), img func(Term) Term, plusT, starT func(a, b Term) Term,
	addBound, mulBound func() bool) func(Term) (Term, bool) {
	return func(t Term) (Term, bool) {
		u, ok := match(t)
		if !ok {
			return nil, false
		}
		if a, b, ok := MatchesPlus(u); ok && addBound() {
			return plusT(img(a), img(b)), true
		}
		if a, b, ok := MatchesStar(u); ok && mulBound() {
			return starT(img(a), img(b)), true
		}
		if a, ok := natDomain.matchSuc(u); ok && addBound() && add1Thm() != nil {
			return plusT(img(a), img(Numeral(1))), true
		}
		return nil, false
	}
}

// castUnfolder is a ring's castUnfold, `⊢ img(u) = split` for the splits
// castSplitter reads: OfNumAdd and OfNumMul read right to left, and for a
// successor `suc a = a + 1` under the cast first. cast is the cast's
// constant, addLeaf and mulLeaf the bridges `⊢ img a ⋆ img b = img(a ⋆ b)`.
func castUnfolder(match func(Term) (Term, bool), cast Term,
	addLeaf, mulLeaf func(a, b Term) *prop.PropWrapper) func(Term) *prop.PropWrapper {
	return func(t Term) *prop.PropWrapper {
		u, ok := match(t)
		if !ok {
			return nil
		}
		if a, b, ok := MatchesPlus(u); ok {
			return addLeaf(a, b).EqSym() // ⊢ img(a + b) = img a + img b
		}
		if a, b, ok := MatchesStar(u); ok {
			return mulLeaf(a, b).EqSym() // ⊢ img(a * b) = img a * img b
		}
		if a, ok := natDomain.matchSuc(u); ok {
			under := sucAdd1(a).LeftApply(cast) // ⊢ img(suc a) = img(a + 1)
			return under.EqTrans(addLeaf(a, Numeral(1)).EqSym())
		}
		return nil
	}
}
