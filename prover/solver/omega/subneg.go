package omega

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Signed normalization — the layer that makes total sub/neg first-class linear
// over ℤ and ℝ (one implementation, two instances). It brings TOTAL subtraction (`a − b`) and negation
// (`−a`) into the positive linear pipeline WITHOUT making the shared
// natural-coefficient linForm/poly signed: it peels `sub`/`neg` down to a
// two-positive-sided form
//
//	⊢ t = P + (−N)
//
// where P, N are ordinary positive canonical linForms (the existing
// ringVocab.normalizeProof outputs). Every step is real kernel work composed
// from five primitive leaves (SubDef / NegAdd / NegNeg / NegZero / MulRightNeg,
// and their ℤ lifts) plus the EXISTING positive ring AC/merge/scale — no new
// ring variant, no 4-var rearrangement lemmas (those are derived here).
//
// Domain-generic over a subnegVocab (the sub/neg twin of ringVocab); realSubneg
// and intSubneg are the two instances. `num` has no instance — its `-` is
// truncated monus (nat_sub.go), a different operator. The relation-level move-across
// that turns `(Pl − Nl) ⋈ (Pr − Nr)` into a positive two-sided comparison the
// decider eats is a SEPARATE step (the discharge integration); this file just
// produces the per-side `P + (−N)` normal form + its proof.

// subnegVocab bundles the sub/neg proof vocabulary the signed normalizer
// composes over: the embedded positive ringVocab (term builders + matchers + the
// AC/merge/scale machinery, shared with the model side), the raw `neg` const for
// congruence, and the five primitive leaf closures.
type subnegVocab struct {
	ring  *ringVocab
	negOp Term // raw `neg` const, for LeftApply congruence under negation

	subToAddNeg func(a, b Term) *prop.PropWrapper // ⊢ a − b = a + (−b)
	negAdd      func(a, b Term) *prop.PropWrapper // ⊢ −(a+b) = (−a) + (−b)
	negNeg      func(a Term) *prop.PropWrapper    // ⊢ −(−a) = a
	negZero     func() *prop.PropWrapper          // ⊢ −(&0) = &0
	mulRightNeg func(c, b Term) *prop.PropWrapper // ⊢ c·(−b) = −(c·b)

	// Relation-level move-across vocabulary (moveAcrossCmp): the comparison
	// builders, the >/≥→</≤ bridges, and the right / left subtraction move-across families.
	leT, ltT           func(a, b Term) Term
	gtBridge, geBridge func(x, y Term) *prop.PropWrapper // ⊢ (x>y)=(y<x) / (x≥y)=(y≤x)
	lessEqSubAddRight, lessEqSubAddLeft,
	lessThanSubAddRight, lessThanSubAddLeft,
	eqSubRightAdd, eqSubLeftAdd func(x, y, z Term) *prop.PropWrapper

	// expansions memoizes expansionRow per monomial — see there.
	expansions constraintMemo
}

var realSubneg = &subnegVocab{
	ring: realRing, negOp: realNeg,
	subToAddNeg: realSubToAddNeg, negAdd: realNegAddL, negNeg: realNegNegL,
	negZero: realNegZeroL, mulRightNeg: realMulRightNegL,
	leT: realLeT, ltT: realLtT, gtBridge: realGtBridge, geBridge: realGeBridge,
	lessEqSubAddRight: realLessEqSubAddRight, lessEqSubAddLeft: realLessEqSubAddLeft,
	lessThanSubAddRight: realLessThanSubAddRight, lessThanSubAddLeft: realLessThanSubAddLeft,
	eqSubRightAdd: realEqSubRightAdd, eqSubLeftAdd: realEqSubLeftAdd,
}

var intSubneg = &subnegVocab{
	ring: intRing, negOp: intNeg,
	subToAddNeg: intSubToAddNeg, negAdd: intNegAddL, negNeg: intNegNegL,
	negZero: intNegZeroL, mulRightNeg: intMulRightNegL,
	leT: intLeT, ltT: intLtT, gtBridge: intGtBridge, geBridge: intGeBridge,
	lessEqSubAddRight: intLessEqSubAddRight, lessEqSubAddLeft: intLessEqSubAddLeft,
	lessThanSubAddRight: intLessThanSubAddRight, lessThanSubAddLeft: intLessThanSubAddLeft,
	eqSubRightAdd: intEqSubRightAdd, eqSubLeftAdd: intEqSubLeftAdd,
}

// Wire the hyp-side move-across hook (deferred to init to avoid the intDomain ⇄
// intSubneg ⇄ intRing var-initialization cycle).
func init() {
	intDomain.moveAcrossHyp = intSubneg.moveAcrossCmp
	realDomain.moveAcrossHyp = realSubneg.moveAcrossCmp

	// Un-negation of comparison hyps, wired for all three domains (each has
	// NotLessThan / NotLessEq). Deferred to init for the same var-cycle reason: the
	// leaves read their bundle through package-level accessors.
	natDomain.wireUnnegate(notLT, notLE)
	intDomain.wireUnnegate(intNotLT, intNotLE)
	realDomain.wireUnnegate(realNotLT, realNotLE)

	// The num layer's facts, read in ℝ and ℤ through their casts (domain.go
	// liftHyp).
	realDomain.liftHyp = realLiftNumHyp
	intDomain.liftHyp = intLiftNumHyp
}

// hasSubNeg reports whether t contains any `sub`/`neg` (so the base fast-path —
// the existing positive normalizer — is unsafe and we must decompose).
func (v *subnegVocab) hasSubNeg(t Term) bool {
	d := v.ring.dom
	if _, ok := d.matchNeg(t); ok {
		return true
	}
	if _, _, ok := d.matchSub(t); ok {
		return true
	}
	if l, r, ok := d.matchPlus(t); ok {
		return v.hasSubNeg(l) || v.hasSubNeg(r)
	}
	if l, r, ok := d.matchStar(t); ok {
		return v.hasSubNeg(l) || v.hasSubNeg(r)
	}
	if product, ok := d.fieldProduct(t); ok {
		return v.hasSubNeg(product)
	}
	return false
}

// subNegOnlyInSquares reports whether every sub/neg in t sits inside a SQUARE
// factor `p·p`, which an ordered reading keeps opaque to retain the square's
// sign. A sub reached at the top, under a `+`, or inside a NON-square product
// answers false.
func (v *subnegVocab) subNegOnlyInSquares(t Term) bool {
	d := v.ring.dom
	if _, ok := d.matchNeg(t); ok {
		return false
	}
	if _, _, ok := d.matchSub(t); ok {
		return false
	}
	if l, r, ok := d.matchStar(t); ok {
		if l.AlphaEquals(r) {
			return true // a square: whatever it holds is protected
		}
		return v.subNegOnlyInSquares(l) && v.subNegOnlyInSquares(r)
	}
	if l, r, ok := d.matchPlus(t); ok {
		return v.subNegOnlyInSquares(l) && v.subNegOnlyInSquares(r)
	}
	if product, ok := d.fieldProduct(t); ok {
		return v.subNegOnlyInSquares(product)
	}
	return true
}

// negOfEq is the `(neg ·)` congruence helper: w.LeftApply(negOp) turns ⊢ X = Y
// into ⊢ −X = −Y.
func (v *subnegVocab) negOfEq(w *prop.PropWrapper) *prop.PropWrapper { return w.LeftApply(v.negOp) }

// interchangeADD: ⊢ (A+B)+(C+D) = (A+C)+(B+D), derived from the ring AC leaves.
// The one non-leaf rearrangement the add case needs.
func (v *subnegVocab) interchangeADD(a, b, c, d Term) *prop.PropWrapper {
	r := v.ring
	cd := r.dom.plus(c, d)
	bd := r.dom.plus(b, d)
	// (A+B)+(C+D) = A+(B+(C+D))
	s1 := r.associateADD(a, b, cd)
	// B+(C+D) = (B+C)+D, under A+·
	s2 := r.associateADD(b, c, d).EqSym().LeftApply(r.plusLeft(a))
	// (B+C)+D = (C+B)+D, under A+·
	s3 := r.commuteADD(b, c).LeftApply(r.plusOp).RightApply(d).LeftApply(r.plusLeft(a))
	// (C+B)+D = C+(B+D), under A+·
	s4 := r.associateADD(c, b, d).LeftApply(r.plusLeft(a))
	// A+(C+(B+D)) = (A+C)+(B+D)
	s5 := r.associateADD(a, c, bd).EqSym()
	return s1.EqTrans(s2).EqTrans(s3).EqTrans(s4).EqTrans(s5)
}

// signedNorm computes (P, N, ⊢ t = P + (−N), ok) — P, N positive canonical
// linForms. ok=false on a nonlinear-with-subtraction term (e.g. atom·(a−b)).
func (v *subnegVocab) signedNorm(t Term) (linForm, linForm, *prop.PropWrapper, bool) {
	d := v.ring.dom

	// Base fast-path: a sub/neg-free subterm goes straight through the existing
	// positive normalizer, then we wrap it as `P + (−&0)`.
	if !v.hasSubNeg(t) {
		// Linear fast path (unchanged). Fall back to the full multivariate
		// normalizer for a sub-free NONLINEAR subterm — the signed FOIL recurses
		// onto factors that may themselves be sub-free products (e.g. x·z in
		// (x·z − y)·…).
		lf, w, ok := v.ring.normalizeProof(t) // ⊢ t = P (linear)
		if !ok {
			lf, w = v.ring.normalizeFull(t) // ⊢ t = P (multivariate)
		}
		return lf, linForm{}, w.EqTrans(v.baseWrap(d.buildTerm(lf))), true
	}

	// −a : swap the two sides.
	if a, ok := d.matchNeg(t); ok {
		pa, na, wa, ok := v.signedNorm(a)
		if !ok {
			return linForm{}, linForm{}, nil, false
		}
		Pa, Na := d.buildTerm(pa), d.buildTerm(na)
		// −a = −(Pa + −Na) = (−Pa) + (−−Na) = (−Pa) + Na = Na + (−Pa)
		w := v.negOfEq(wa). // ⊢ −a = −(Pa + −Na)
					EqTrans(v.negAdd(Pa, d.neg(Na))).                            // = (−Pa)+(−−Na)
					EqTrans(v.negNeg(Na).LeftApply(v.ring.plusLeft(d.neg(Pa)))). // = (−Pa)+Na
					EqTrans(v.ring.commuteADD(d.neg(Pa), Na))                    // = Na+(−Pa)
		return na, pa, w, true
	}

	// a − b : rewrite to a + (−b) and recurse.
	if a, b, ok := d.matchSub(t); ok {
		rewr := v.subToAddNeg(a, b) // ⊢ a − b = a + (−b)
		p, n, w2, ok := v.signedNorm(d.plus(a, d.neg(b)))
		if !ok {
			return linForm{}, linForm{}, nil, false
		}
		return p, n, rewr.EqTrans(w2), true
	}

	// a + b : combine the two signed forms, folding the negative parts.
	if a, b, ok := d.matchPlus(t); ok {
		pa, na, wa, ok1 := v.signedNorm(a)
		pb, nb, wb, ok2 := v.signedNorm(b)
		if !ok1 || !ok2 {
			return linForm{}, linForm{}, nil, false
		}
		cong := wa.LeftApply(v.ring.plusOp).Apply(wb) // a+b = (Pa+−Na)+(Pb+−Nb)
		pSum, nSum, comb := v.combineSignedAdd(pa, na, pb, nb)
		return pSum, nSum, cong.EqTrans(comb), true
	}

	// u / v by a symbolic divisor, or the inverse of a product: the
	// product it denotes.
	if unfold := v.ring.fieldUnfolded(t); unfold != nil {
		p, n, w, ok := v.signedNorm(prop.Rhs(unfold))
		if !ok {
			return linForm{}, linForm{}, nil, false
		}
		return p, n, unfold.EqTrans(w), true
	}

	// c·(signed) / (signed)·c with c a sub-free literal coefficient.
	if x, y, ok := d.matchStar(t); ok {
		if cVal, shaped, okL := d.asLiteral(x); shaped && okL {
			return v.scaleSigned(x, cVal, y)
		}
		if cVal, shaped, okL := d.asLiteral(y); shaped && okL {
			w0 := v.ring.commuteMUL(x, y) // ⊢ x·y = y·x
			p, n, w1, ok := v.scaleSigned(y, cVal, x)
			if !ok {
				return linForm{}, linForm{}, nil, false
			}
			return p, n, w0.EqTrans(w1), true
		}
		return v.mulSigned(x, y) // general nonlinear product — the signed FOIL
	}

	return linForm{}, linForm{}, nil, false
}

// combineSignedAdd combines two signed forms `(Pa + −Na)` and `(Pb + −Nb)` into
// one — `(Pa+Pb) + (−(Na+Nb))` merged to canonical `Pfin + (−Nfin)` — returning
// (pSum, nSum, ⊢ (Pa+−Na)+(Pb+−Nb) = Pfin+(−Nfin)). Factored from signedNorm's
// `+` case; also the regroup step the signed FOIL (mulSigned) ends with.
func (v *subnegVocab) combineSignedAdd(pa, na, pb, nb linForm) (linForm, linForm, *prop.PropWrapper) {
	d := v.ring.dom
	Pa, Na := d.buildTerm(pa), d.buildTerm(na)
	Pb, Nb := d.buildTerm(pb), d.buildTerm(nb)
	pSum, nSum := linAdd(pa, pb), linAdd(na, nb)
	Pfin := d.buildTerm(pSum)
	inter := v.interchangeADD(Pa, d.neg(Na), Pb, d.neg(Nb))                        // = (Pa+Pb)+((−Na)+(−Nb))
	foldNeg := v.negAdd(Na, Nb).EqSym().LeftApply(v.ring.plusLeft(d.plus(Pa, Pb))) // (−Na)+(−Nb) = −(Na+Nb)
	mP := v.ring.mergeProof(pa, pb).LeftApply(v.ring.plusOp).RightApply(d.neg(d.plus(Na, Nb)))
	mN := v.negOfEq(v.ring.mergeProof(na, nb)).LeftApply(v.ring.plusLeft(Pfin))
	return pSum, nSum, inter.EqTrans(foldNeg).EqTrans(mP).EqTrans(mN)
}

// negLmul: ⊢ (−a)·b = −(a·b), derived from mulRightNeg + commuteMUL (the bundle
// carries only the MulRightNeg form). The domain-generic twin of int.go's intMulLnegProof.
func (v *subnegVocab) negLmul(a, b Term) *prop.PropWrapper {
	d := v.ring.dom
	return v.ring.commuteMUL(d.neg(a), b). // (−a)·b = b·(−a)
						EqTrans(v.mulRightNeg(b, a)).               // = −(b·a)
						EqTrans(v.negOfEq(v.ring.commuteMUL(b, a))) // = −(a·b)
}

// negNegMul: ⊢ (−a)·(−b) = a·b, derived from mulRightNeg / negLmul / negNeg.
func (v *subnegVocab) negNegMul(a, b Term) *prop.PropWrapper {
	d := v.ring.dom
	return v.mulRightNeg(d.neg(a), b). // (−a)·(−b) = −((−a)·b)
						EqTrans(v.negOfEq(v.negLmul(a, b))). // = −(−(a·b))
						EqTrans(v.negNeg(d.star(a, b)))      // = a·b
}

// mulSigned computes (P, N, ⊢ x·y = P + (−N)) for two SIGNED operands — the FOIL
// `(Px+−Nx)·(Py+−Ny) = (Px·Py + Nx·Ny) + (−(Px·Ny + Nx·Py))` (signed
// polynomial multiplication). Each of the four positive·positive products folds to a canonical
// multivariate polynomial via the full ring (mulProofFull); the two cross-sign
// products carry one negation pushed out by mulRightNeg / negLmul / negNeg. The result
// regroups via combineSignedAdd. Handles `(x−y)²`, `(a−b)(a+b)`, etc.
func (v *subnegVocab) mulSigned(x, y Term) (linForm, linForm, *prop.PropWrapper, bool) {
	d := v.ring.dom
	px, nx, wx, ok1 := v.signedNorm(x)
	py, ny, wy, ok2 := v.signedNorm(y)
	if !ok1 || !ok2 {
		return linForm{}, linForm{}, nil, false
	}
	Px, Nx := d.buildTerm(px), d.buildTerm(nx)
	Py, Ny := d.buildTerm(py), d.buildTerm(ny)
	nNx, nNy := d.neg(Nx), d.neg(Ny)

	// the four positive products, folded to canonical polynomials.
	qpp, mpp := v.ring.mulProofFull(px, py) // ⊢ Px·Py = Qpp
	qpn, mpn := v.ring.mulProofFull(px, ny) // ⊢ Px·Ny = Qpn
	qnp, mnp := v.ring.mulProofFull(nx, py) // ⊢ Nx·Py = Qnp
	qnn, mnn := v.ring.mulProofFull(nx, ny) // ⊢ Nx·Ny = Qnn

	// x·y = (Px+−Nx)·(Py+−Ny)
	cong := wx.LeftApply(v.ring.starOp).Apply(wy)
	// = Px·(Py+−Ny) + (−Nx)·(Py+−Ny)
	rd := v.ring.rightDistrib(Px, nNx, d.plus(Py, nNy))
	// Px·(Py+−Ny) = Px·Py + Px·(−Ny), under `+ (−Nx)·(Py+−Ny)`
	ld1 := v.ring.distributeMUL(Px, Py, nNy).LeftApply(v.ring.plusOp).RightApply(d.star(nNx, d.plus(Py, nNy)))
	// (−Nx)·(Py+−Ny) = (−Nx)·Py + (−Nx)·(−Ny), under `(Px·Py+Px·(−Ny)) +`
	ld2 := v.ring.distributeMUL(nNx, Py, nNy).LeftApply(v.ring.plusLeft(d.plus(d.star(Px, Py), d.star(Px, nNy))))

	// rewrite the four products to their canonical (signed) forms.
	rwA := mpp                                           // Px·Py = Qpp
	rwB := v.mulRightNeg(Px, Ny).EqTrans(v.negOfEq(mpn)) // Px·(−Ny) = −Qpn
	rwC := v.negLmul(Nx, Py).EqTrans(v.negOfEq(mnp))     // (−Nx)·Py = −Qnp
	rwD := v.negNegMul(Nx, Ny).EqTrans(mnn)              // (−Nx)·(−Ny) = Qnn
	rwAB := rwA.LeftApply(v.ring.plusOp).Apply(rwB)      // (Px·Py+Px·(−Ny)) = (Qpp + −Qpn)
	rwCD := rwC.LeftApply(v.ring.plusOp).Apply(rwD)      // ((−Nx)·Py+(−Nx)·(−Ny)) = (−Qnp + Qnn)
	rw4 := rwAB.LeftApply(v.ring.plusOp).Apply(rwCD)     // = (Qpp+−Qpn) + (−Qnp+Qnn)

	// commute the second summand `(−Qnp)+Qnn` to `Qnn+(−Qnp)` so it is `P+(−N)`.
	QppT, QpnT := d.buildTerm(qpp), d.buildTerm(qpn)
	QnpT, QnnT := d.buildTerm(qnp), d.buildTerm(qnn)
	first := d.plus(QppT, d.neg(QpnT))
	commuteSnd := v.ring.commuteADD(d.neg(QnpT), QnnT).LeftApply(v.ring.plusLeft(first)) // = (Qpp+−Qpn) + (Qnn+−Qnp)

	// regroup the two signed forms into one canonical P+(−N).
	pSum, nSum, comb := v.combineSignedAdd(qpp, qpn, qnn, qnp)
	w := cong.EqTrans(rd).EqTrans(ld1).EqTrans(ld2).EqTrans(rw4).EqTrans(commuteSnd).EqTrans(comb)
	return pSum, nSum, w, true
}

// baseWrap: ⊢ P = P + (−&0)   (the leaf/sub-free wrap into `P + −N` shape).
func (v *subnegVocab) baseWrap(Pt Term) *prop.PropWrapper {
	// (P + −&0) = (P + &0) = P, then EqSym.
	return v.negZero().LeftApply(v.ring.plusLeft(Pt)). // ⊢ P+(−&0) = P+&0
								EqTrans(v.ring.addZeroR(Pt)). // = P
								EqSym()                       // ⊢ P = P+(−&0)
}

// scaleSigned: ⊢ cTerm·y = Pfin + (−Nfin) for a literal coefficient cTerm (value
// cVal) and a signed operand y.
func (v *subnegVocab) scaleSigned(cTerm Term, cVal _Integer, y Term) (linForm, linForm, *prop.PropWrapper, bool) {
	d := v.ring.dom
	py, ny, wy, ok := v.signedNorm(y)
	if !ok {
		return linForm{}, linForm{}, nil, false
	}
	Py, Ny := d.buildTerm(py), d.buildTerm(ny)
	pfin, nfin := linScale(cVal, py), linScale(cVal, ny)
	Pfin := d.buildTerm(pfin)
	// The distinguished zero/one of a structure ring can have a
	// different spelling from the numeral scaleProof consumes.
	coefficient := prop.Refl(cTerm)
	if v.ring.literalBridge != nil {
		coefficient = v.ring.literalBridge(cTerm, cVal)
	}
	c := d.numeral(cVal)
	start := coefficient.LeftApply(v.ring.starOp).RightApply(y)
	// c·y = c·(Py + −Ny)
	s1 := wy.LeftApply(v.ring.starLeft(c))
	// = c·Py + c·(−Ny)
	s2 := v.ring.distributeMUL(c, Py, d.neg(Ny))
	// c·(−Ny) = −(c·Ny), under c·Py + ·
	s3 := v.mulRightNeg(c, Ny).LeftApply(v.ring.plusLeft(d.star(c, Py)))
	// c·Py = Pfin, as the left summand
	s4 := v.ring.scaleProof(cVal, py).LeftApply(v.ring.plusOp).RightApply(d.neg(d.star(c, Ny)))
	// c·Ny = Nfin, under −(·) and Pfin + ·
	s5 := v.negOfEq(v.ring.scaleProof(cVal, ny)).LeftApply(v.ring.plusLeft(Pfin))
	w := start.EqTrans(s1).EqTrans(s2).EqTrans(s3).EqTrans(s4).EqTrans(s5)
	return pfin, nfin, w, true
}

// toSubForm returns (P, N, ⊢ t = P − N, ok): the signed normal form re-expressed
// with a top-level subtraction (`P − N`) rather than `P + (−N)`, the shape the
// subtraction move-across leaves consume.
func (v *subnegVocab) toSubForm(t Term) (linForm, linForm, *prop.PropWrapper, bool) {
	p, n, w, ok := v.signedNorm(t) // ⊢ t = P + (−N)
	if !ok {
		return linForm{}, linForm{}, nil, false
	}
	d := v.ring.dom
	Pt, Nt := d.buildTerm(p), d.buildTerm(n)
	// subToAddNeg(Pt,Nt): ⊢ Pt−Nt = Pt+(−Nt); EqSym → Pt+(−Nt) = Pt−Nt
	return p, n, w.EqTrans(v.subToAddNeg(Pt, Nt).EqSym()), true
}

// relHead extracts the binary relation/operator const head of `(head L) R`.
func relHead(atom Term) (Term, bool) {
	a, ok := atom.AsAppliedTerm()
	if !ok {
		return nil, false
	}
	f, ok := a.Fun().AsAppliedTerm()
	if !ok {
		return nil, false
	}
	return f.Fun(), true
}

// moveAcrossCmp turns a comparison/equality atom whose sides carry total
// subtraction/negation into the equivalent POSITIVE two-sided atom the decider
// already handles, returning `⊢ atom ⇔ positiveAtom`. nil when the atom is not a
// recognized ≤/</=/>/≥ over this domain, has no sub/neg to move, or its signed
// normalization declines.
//
// For `L ⋈ R` with signed forms `L = Pl − Nl`, `R = Pr − Nr` it derives
// `L ⋈ R ⇔ (Pl + Nr) ⋈ (Pr + Nl)` by: the left move-across (clear the right subtraction) →
// re-normalize the left side back to `P − N` (reusing signedNorm, so no separate
// rearrangement lemma) → the right move-across (clear the left subtraction). >/≥ bridge to
// </≤ first.
func (v *subnegVocab) moveAcrossCmp(atom Term) *prop.PropWrapper {
	d := v.ring.dom

	// >/≥ : bridge to the swapped </≤ then move-across the inner atom.
	if a, b, ok := d.matchGt(atom); ok {
		inner := v.moveAcrossCmp(v.ltT(b, a))
		if inner == nil {
			return nil
		}
		return v.gtBridge(a, b).EqTrans(inner)
	}
	if a, b, ok := d.matchGe(atom); ok {
		inner := v.moveAcrossCmp(v.leT(b, a))
		if inner == nil {
			return nil
		}
		return v.geBridge(a, b).EqTrans(inner)
	}

	var l, r Term
	var subRadd, subLadd func(x, y, z Term) *prop.PropWrapper
	switch {
	case match3(d.matchLe, atom, &l, &r):
		subRadd, subLadd = v.lessEqSubAddRight, v.lessEqSubAddLeft
	case match3(d.matchLt, atom, &l, &r):
		subRadd, subLadd = v.lessThanSubAddRight, v.lessThanSubAddLeft
	default:
		a, b, ok := ext.MatchesEQ(atom)
		if !ok || !d.isElem(a) {
			return nil
		}
		l, r = a, b
		subRadd, subLadd = v.eqSubRightAdd, v.eqSubLeftAdd
	}
	if !v.hasSubNeg(l) && !v.hasSubNeg(r) {
		return nil // already positive — the existing decider handles it
	}
	if (v.leT != nil || v.ltT != nil) && v.subNegOnlyInSquares(l) && v.subNegOnlyInSquares(r) {
		// Ordered arithmetic keeps square factors opaque so their sign can
		// price either comparison side. Expanding (x−y)² loses that sign
		// from the monomial basis. Other signed products and additive
		// spines still normalize. A structure ring has no order reading,
		// so its equality normalizer expands squared signed expressions.
		return nil
	}

	pl, nl, wL, ok1 := v.toSubForm(l) // ⊢ l = Pl − Nl
	pr, nr, wR, ok2 := v.toSubForm(r) // ⊢ r = Pr − Nr
	if !ok1 || !ok2 {
		return nil
	}
	rel, ok := relHead(atom)
	if !ok {
		return nil
	}
	Pl, Nl := d.buildTerm(pl), d.buildTerm(nl)
	Pr, Nr := d.buildTerm(pr), d.buildTerm(nr)

	// atom = rel(Pl−Nl, Pr−Nr)
	cong := wL.LeftApply(rel).Apply(wR)
	// left move-across: rel(Pl−Nl, Pr−Nr) ⇔ rel((Pl−Nl)+Nr, Pr)
	s1 := subLadd(d.sub(Pl, Nl), Pr, Nr)
	// re-normalize the left side: (Pl−Nl)+Nr = PMid − NMid  (PMid = Pl+Nr, NMid = Nl)
	mid := d.plus(d.sub(Pl, Nl), Nr)
	pm, nm, wMid, ok3 := v.toSubForm(mid)
	if !ok3 {
		return nil
	}
	PMid, NMid := d.buildTerm(pm), d.buildTerm(nm)
	s2 := wMid.LeftApply(rel).RightApply(Pr)
	// right move-across: rel(PMid−NMid, Pr) ⇔ rel(PMid, Pr+NMid)
	s3 := subRadd(PMid, NMid, Pr)
	return cong.EqTrans(s1).EqTrans(s2).EqTrans(s3)
}

// expansionRow is the square guard's other half. moveAcrossCmp keeps a
// product whose only sub/neg sits inside a square as ONE unknown, so that
// the square keeps the sign the sign rows give it; this row gives the same
// unknown its expansion — `m + N = P`, from the signed normal form `⊢ m =
// P − N` — so that an identity which needs the square multiplied out
// (`(x − y)·(x − y) + 2·x·y = x·x + y·y`) closes as well. Both readings reach
// the refutation: a row adds a way to refute and takes none away. ok is
// false when m carries no sub/neg or the normalizer declines it.
//
// The row is memoized per monomial (expansions), a decline as a row is. It
// is a theorem with no hypotheses, a function of m and the lemma bundle
// alone, and the signed normal form behind it is a kernel derivation; the
// sign rows ask for it at every monomial of every linear run, once per atom
// per direction per case-split level, over monomials that do not change
// from one run to the next (real_sign_rows.go, int_sign_rows.go). On an ε-δ
// context whose products carry differences the runs of one proof asked
// 26,000 times about 511 monomials, and the answers were a third of the
// proof's time. The memo is the constraint memo's, with its hit test and
// its bound, and the bundle setters drop it with the others
// (resetConstraintMemos).
func (v *subnegVocab) expansionRow(m Term) (LinConstraint, bool) {
	if !v.hasSubNeg(m) {
		return LinConstraint{}, false
	}
	if rows, ok := v.expansions.lookup(m); ok {
		if len(rows) == 0 {
			return LinConstraint{}, false
		}
		return rows[0], true
	}
	row, ok := v.expansionRowOf(m)
	if !ok {
		v.expansions.store(m, nil)
		return LinConstraint{}, false
	}
	v.expansions.store(m, []LinConstraint{row})
	return row, true
}

// expansionRowOf is the uncached expansion behind expansionRow, of a
// monomial that carries a sub/neg.
func (v *subnegVocab) expansionRowOf(m Term) (LinConstraint, bool) {
	p, n, w, ok := v.toSubForm(m) // ⊢ m = P − N
	if !ok {
		return LinConstraint{}, false
	}
	d := v.ring.dom
	P, N := d.buildTerm(p), d.buildTerm(n)
	row := v.eqSubLeftAdd(m, P, N).EqMP(w) // ⊢ m + N = P
	return LinConstraint{Lhs: d.plus(m, N), Rhs: P, Op: opEQ, HypProof: row}, true
}

// powExpansionRow is expansionRow for a power: one the pow basis leaves as
// one unknown because its base carries sub/neg (domain.go powLiteral), so
// that the power of a difference or of a negation meets its expansion as the
// same product written out does — `pow(b, c) + N = P`, from the domain's own
// unfold `⊢ pow(b, c) = b·(b·(…·1))` and the chain's signed normal form
// `⊢ chain = P − N`. ok is false for any other term.
func (v *subnegVocab) powExpansionRow(t Term) (LinConstraint, bool) {
	d := v.ring.dom
	if d.matchPow == nil || v.ring.powUnfold == nil {
		return LinConstraint{}, false
	}
	base, exponent, ok := d.matchPow(t)
	if !ok || !d.carriesSubNeg(base) {
		return LinConstraint{}, false
	}
	c, ok := BitsToUint(exponent)
	if !ok || !ext.IsCanonicalNumeral(exponent) || c > powChainMax {
		return LinConstraint{}, false
	}
	unfold := v.ring.powUnfold(base, c) // ⊢ pow(b, c) = chain
	if unfold == nil {
		return LinConstraint{}, false
	}
	p, n, w, ok := v.toSubForm(prop.Rhs(unfold)) // ⊢ chain = P − N
	if !ok {
		return LinConstraint{}, false
	}
	P, N := d.buildTerm(p), d.buildTerm(n)
	row := v.eqSubLeftAdd(t, P, N).EqMP(unfold.EqTrans(w)) // ⊢ pow + N = P
	return LinConstraint{Lhs: d.plus(t, N), Rhs: P, Op: opEQ, HypProof: row}, true
}

// powExpansionRows collects powExpansionRow over a constraint set's atoms
// (Domain.atomsOf).
func (v *subnegVocab) powExpansionRows(atoms []Term) []LinConstraint {
	var rows []LinConstraint
	for _, atom := range atoms {
		if r, ok := v.powExpansionRow(atom); ok {
			rows = append(rows, r)
		}
	}
	return rows
}

// match3 binds (l,r) from a binary matcher; a small switch helper.
func match3(m func(Term) (Term, Term, bool), t Term, l, r *Term) bool {
	a, b, ok := m(t)
	if ok {
		*l, *r = a, b
	}
	return ok
}

// SignedNormalizeProof returns (P, N, ⊢ t = P + (−N), ok) over ℤ — the algorithm
// entry point for the int signed normalizer (the ℝ twin is RealSignedNormalizeProof).
func IntSignedNormalizeProof(t Term) (linForm, linForm, *prop.PropWrapper, bool) {
	return intSubneg.signedNorm(t)
}

// RealSignedNormalizeProof is the ℝ twin of IntSignedNormalizeProof.
func RealSignedNormalizeProof(t Term) (linForm, linForm, *prop.PropWrapper, bool) {
	return realSubneg.signedNorm(t)
}
