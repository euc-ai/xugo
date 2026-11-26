package omega

import (
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The sign of a MONOMIAL over ℤ, supplied to the int refutation as extra rows —
// the twin of real_sign_rows.go.
//
// Since the monomial basis a product of variables is one unknown, and over ℤ a
// bare unknown carries no sign at all: `buildAll` injects the `0 ≤ x` row per
// atom only over `num`, where every term is nonnegative. So a refutation that
// turns on `&0 ≤ a·b` has no row to combine with, even when the context states
// both factors' signs — the sign-known handlers (intProveSignedProduct) answer
// that question only about a GOAL.
//
// For each sign-bearing atom in the constraint set:
//
//   - the SQUARE reading — every base atom occurs an even number of times, so
//     the monomial IS a square `t·t` (the full ring proves the regrouping) and
//     SquareNonneg gives `&0 ≤ m` with no hypothesis at all;
//   - the FACTORS' SIGNS — every base atom has a sign among the constraints,
//     folded pairwise through LessEqMul / MulPos and the neg-order flips,
//     exactly as intProveSignedProduct folds a binary product on the goal side;
//   - an `&n` COERCION is nonnegative because n is.
//
// Each derived fact rides as a `LinConstraint` whose `HypProof` is the proof
// just built. Because that proof is assembled from the SOURCE constraints' own
// proofs (intCanonAssume, which honours `Hyp`/`HypProof`), its hypotheses are
// theirs and the refutation's stay a subset of the goal's — the IsStronger
// contract — including when a source was projected out of a conjunction.
//
// As over ℝ, a pair of factors whose signs differ in strictness folds to the
// non-strict sign of the product, the strict fact weakened first
// (intWeakenLt), and a FACTOR's sign is never inferred from the monomial's
// (that is division by a variable, the cancel handler's business).

// intSignFact is a proved sign for a term: `&0 ⋈ term` when nonneg is true,
// `term ⋈ &0` when it is false, with strict selecting `<` over `≤`.
type intSignFact struct {
	term   Term
	proof  *prop.PropWrapper
	nonneg bool
	strict bool
}

// intConstraintSign reads a constraint that states the sign of a single term —
// one side is the literal `&0` — and returns that term's sign fact.
func intConstraintSign(c LinConstraint) (intSignFact, bool) {
	if c.Op != opLE && c.Op != opLT {
		return intSignFact{}, false
	}
	strict := c.Op == opLT
	zero := intLit(0)
	switch {
	case c.Lhs.AlphaEquals(zero) && !c.Rhs.AlphaEquals(zero):
		return intSignFact{term: c.Rhs, proof: intCanonAssume(c.Lhs, c.Rhs, c.Op, c.Hyp, c.HypProof),
			nonneg: true, strict: strict}, true
	case c.Rhs.AlphaEquals(zero) && !c.Lhs.AlphaEquals(zero):
		return intSignFact{term: c.Lhs, proof: intCanonAssume(c.Lhs, c.Rhs, c.Op, c.Hyp, c.HypProof),
			nonneg: false, strict: strict}, true
	}
	return intSignFact{}, false
}

// intFactorSigns collects every sign the constraint set states. The fold
// needs one sign per factor, and a term with several keeps the strongest:
// a strict one stated after a non-strict one of the same direction takes
// its place, as in realFactorSigns.
func intFactorSigns(cs []LinConstraint) []intSignFact {
	var signs []intSignFact
	for _, c := range cs {
		f, ok := intConstraintSign(c)
		if !ok {
			continue
		}
		if i := slices.IndexFunc(signs, func(s intSignFact) bool { return s.term.AlphaEquals(f.term) }); i >= 0 {
			if f.strict && !signs[i].strict && f.nonneg == signs[i].nonneg {
				signs[i] = f
			}
			continue
		}
		signs = append(signs, f)
	}
	return signs
}

// intLookupSign finds the sign fact for a factor.
func intLookupSign(signs []intSignFact, factor Term) (intSignFact, bool) {
	i := slices.IndexFunc(signs, func(s intSignFact) bool { return s.term.AlphaEquals(factor) })
	if i < 0 {
		return intSignFact{}, false
	}
	return signs[i], true
}

// intNonnegForm restates a sign fact as `&0 ⋈ g`: g is the term itself when the
// fact is already nonneg, else `−term`, the proof carried across by the
// neg-order iff (NegNonneg / NegPositiveIffNegative). The multiplication leaves take
// both operands in this form.
func intNonnegForm(f intSignFact) (Term, *prop.PropWrapper) {
	if f.nonneg {
		return f.term, f.proof
	}
	relT, thm := intLeT, intNegNonnegThm()
	if f.strict {
		relT, thm = intLtT, intNegPositiveIffNegativeThm()
	}
	neg := intNegT(f.term)
	// ⊢ (&0 ⋈ −t) = (t ⋈ &0); the fact proves the right side.
	iff := intEqLeaf(thm, []Term{f.term}, relT(intLit(0), neg), relT(f.term, intLit(0)))
	return neg, iff.EqSym().EqMP(f.proof)
}

// intMulPosFromProofs applies LessEqMul / MulPos to two proved
// nonnegativities: `Γ ⊢ &0 ⋈ a` and `Γ ⊢ &0 ⋈ b` give `Γ ⊢ &0 ⋈ a·b`. The
// side-condition-discharging twin is intMulPosLemma (int.go), which proves the
// two premises from the hypotheses instead of taking them.
func intMulPosFromProofs(a0, b0 *prop.PropWrapper, a, b Term, strict bool) *prop.PropWrapper {
	relT, thm := intLeT, intLessEqMulThm()
	if strict {
		relT, thm = intLtT, intMulPosThm()
	}
	imp := intImplyLeaf(thm, []Term{a, b},
		imply(relT(intLit(0), a), imply(relT(intLit(0), b), relT(intLit(0), intStarT(a, b)))))
	return mp(mp(imp, a0), b0)
}

// intWeakSign is a sign fact's non-strict reading: itself when it is
// non-strict, else `&0 ≤ term` from `&0 < term` (`term ≤ &0` from `term < &0`).
func intWeakSign(f intSignFact) intSignFact {
	if !f.strict {
		return f
	}
	l, r := intLit(0), f.term
	if !f.nonneg {
		l, r = f.term, intLit(0)
	}
	return intSignFact{term: f.term, proof: intWeakenLt(l, r, f.proof), nonneg: f.nonneg}
}

// intMulSigns multiplies two sign facts into the sign of their product,
// mirroring intProveSignedProduct's four cases with the premises already
// proved. The product is strict when both facts are; a strict fact beside a
// non-strict one is weakened first.
func intMulSigns(fa, fb intSignFact) (intSignFact, bool) {
	if fa.strict != fb.strict {
		fa, fb = intWeakSign(fa), intWeakSign(fb)
	}
	strict := fa.strict
	ga, pa := intNonnegForm(fa)
	gb, pb := intNonnegForm(fb)
	prodG := intMulPosFromProofs(pa, pb, ga, gb, strict) // ⊢ &0 ⋈ ga·gb
	prod := intStarT(fa.term, fb.term)
	rel, relT := intLe, intLeT
	if strict {
		rel, relT = intLt, intLtT
	}
	switch {
	case fa.nonneg && fb.nonneg: // ga·gb IS a·b
		return intSignFact{term: prod, proof: prodG, nonneg: true, strict: strict}, true
	case !fa.nonneg && !fb.nonneg: // (−a)·(−b) = a·b
		cong := intSubneg.negNegMul(fa.term, fb.term).LeftApply(ext.Apply(rel, intLit(0)))
		return intSignFact{term: prod, proof: cong.EqMP(prodG), nonneg: true, strict: strict}, true
	case fa.nonneg: // a·(−b) = −(a·b), so the product is nonpositive
		w, ok := intFlipNeg(prodG, intSubneg.mulRightNeg(fa.term, fb.term), prod, rel, relT, strict)
		if !ok {
			return intSignFact{}, false
		}
		return intSignFact{term: prod, proof: w, nonneg: false, strict: strict}, true
	default: // (−a)·b = −(a·b)
		w, ok := intFlipNeg(prodG, intSubneg.negLmul(fa.term, fb.term), prod, rel, relT, strict)
		if !ok {
			return intSignFact{}, false
		}
		return intSignFact{term: prod, proof: w, nonneg: false, strict: strict}, true
	}
}

// intMonomialSign folds the factors' signs along the monomial's own nesting.
// The accumulated term must come out α-equal to the monomial: a monomial the
// polyMul fuse left as one opaque product may be nested some other way, and a
// row about a differently-spelled term is a row about a different atom.
func intMonomialSign(m Term, signs []intSignFact) (intSignFact, bool) {
	factors := intDecomposeStar(m)
	if len(factors) < 2 {
		return intSignFact{}, false
	}
	acc, ok := intLookupSign(signs, factors[0])
	if !ok {
		return intSignFact{}, false
	}
	for _, factor := range factors[1:] {
		next, ok := intLookupSign(signs, factor)
		if !ok {
			return intSignFact{}, false
		}
		if acc, ok = intMulSigns(acc, next); !ok {
			return intSignFact{}, false
		}
	}
	if !acc.term.AlphaEquals(m) {
		return intSignFact{}, false
	}
	return acc, true
}

// intSquareSign proves `⊢ &0 ≤ m` for a monomial whose every base atom occurs
// an even number of times: m is then the square of the product of the halved
// multiplicities, the full ring proves that regrouping, and SquareNonneg
// prices it. Hypothesis-free — this is the one sign the context need not state.
// Kept per monomial (intSquareSigns), as the real twin's is.
func intSquareSign(m Term) (*prop.PropWrapper, bool) {
	factors := intDecomposeStar(m)
	if len(factors) < 2 {
		return nil, false
	}
	sorted := slices.Clone(factors)
	slices.SortStableFunc(sorted, func(a, b Term) int { return a.Compare(b) })
	var half []Term
	for i := 0; i < len(sorted); {
		j := i
		for j < len(sorted) && sorted[j].Compare(sorted[i]) == 0 {
			j++
		}
		if (j-i)%2 != 0 {
			return nil, false
		}
		for k := 0; k < (j-i)/2; k++ {
			half = append(half, sorted[i])
		}
		i = j
	}
	if rows, held := intSquareSigns.lookup(m); held {
		if len(rows) == 0 {
			return nil, false
		}
		return rows[0].HypProof, true
	}
	root := intRing.monoProductOf(half)
	square := intStarT(root, root)
	eq, ok := IntRingProveFull(m, square) // ⊢ m = root·root
	if !ok {
		intSquareSigns.store(m, nil)
		return nil, false
	}
	nonneg := intImplyLeaf(intSquareNonnegThm(), []Term{root}, intLeT(intLit(0), square))
	cong := eq.LeftApply(ext.Apply(intLe, intLit(0))) // ⊢ (&0 ≤ m) = (&0 ≤ root·root)
	sign := cong.EqSym().EqMP(nonneg)
	intSquareSigns.store(m, []LinConstraint{{Lhs: intLit(0), Rhs: m, Op: opLE, HypProof: sign}})
	return sign, true
}

// intSquareSigns memoizes intSquareSign, as realSquareSigns does its twin.
var intSquareSigns constraintMemo

// intOfNumNonneg proves `⊢ &0 ≤ &n` for an `int_of_num` atom: the of_num order
// bridge read against num's own `0 ≤ n`. `&n` is nonnegative because n is, and
// no bundle field of its own is needed.
func intOfNumNonneg(atom Term) (*prop.PropWrapper, bool) {
	n, ok := MatchesIntOfNum(atom)
	if !ok {
		return nil, false
	}
	bridge := intEqLeaf(intOfNumLeThm(), []Term{Numeral(0), n},
		intLeT(intLit(0), atom), le(Numeral(0), n))
	return bridge.EqSym().EqMP(zeroLe(n)), true
}

// intCastFactorSigns adds to signs the sign of every `&n` factor of the
// monomials, where the set states none of its own (realCastFactorSigns'
// twin): a product of casts, what the cast basis reads `&(a * b)` as, has
// by the fold the sign the one unknown `&(a * b)` has.
func intCastFactorSigns(signs []intSignFact, monos []Term) []intSignFact {
	for _, m := range monos {
		for _, factor := range intDecomposeStar(m) {
			if _, stated := intLookupSign(signs, factor); stated {
				continue
			}
			if w, ok := intOfNumNonneg(factor); ok {
				signs = append(signs, intSignFact{term: factor, proof: w, nonneg: true})
			}
		}
	}
	return signs
}

// intSignAtoms picks, among the atoms a constraint set's linear forms are
// written over (Domain.atomsOf), those a sign row could be about: the
// product monomials, and the `&n` coercions.
func intSignAtoms(atoms []Term) []Term {
	var bearing []Term
	for _, atom := range atoms {
		_, _, isProduct := intDomain.matchStar(atom)
		_, isOfNum := MatchesIntOfNum(atom)
		if isProduct || isOfNum {
			bearing = append(bearing, atom)
		}
	}
	return bearing
}

// intMonomialSignConstraints derives the sign rows for the constraint set's
// sign-bearing atoms. Returns nil — at the cost of one linOf pass — when the
// set has none, which is every purely linear goal over free variables.
func intMonomialSignConstraints(cs []LinConstraint) []LinConstraint {
	return intMonomialSignRows(cs, cs)
}

// intMonomialSignRows derives the sign rows for the sign-bearing atoms of
// over from the signs that facts states, as the real twin does
// (realMonomialSignRows): one set for the linear refutation, the model's
// rows over the context's signs for the products pass.
func intMonomialSignRows(facts, over []LinConstraint) []LinConstraint {
	// A power left one unknown for its sub/neg base gets its expansion
	// (subneg.go powExpansionRow), whether or not a product is in the set.
	all := intDomain.atomsOf(over)
	extra := intSubneg.powExpansionRows(all)
	atoms := intSignAtoms(all)
	if len(atoms) == 0 {
		return extra
	}
	signs := intCastFactorSigns(intFactorSigns(facts), atoms)
	folds := intFoldsUnder(signs)
	for _, m := range atoms {
		if w, ok := intOfNumNonneg(m); ok { // `&n` is nonnegative because n is
			extra = append(extra, LinConstraint{Lhs: intLit(0), Rhs: m, Op: opLE, HypProof: w})
			continue
		}
		// A product carrying a subtraction inside a square is one unknown
		// here (subneg.go's guard); its expansion rides beside its sign.
		if r, ok := intSubneg.expansionRow(m); ok {
			extra = append(extra, r)
		}
		// Both readings are emitted, never one instead of the other: an even
		// monomial whose factors are all POSITIVE is strictly positive, and
		// the square reading alone gives only `&0 ≤ m`.
		if w, ok := intSquareSign(m); ok {
			extra = append(extra, LinConstraint{Lhs: intLit(0), Rhs: m, Op: opLE, HypProof: w})
		}
		f, ok := folds.sign(m)
		if !ok {
			continue
		}
		op := opLE
		if f.strict {
			op = opLT
		}
		if f.nonneg {
			extra = append(extra, LinConstraint{Lhs: intLit(0), Rhs: m, Op: op, HypProof: f.proof})
		} else {
			extra = append(extra, LinConstraint{Lhs: m, Rhs: intLit(0), Op: op, HypProof: f.proof})
		}
	}
	return extra
}

// intFolds is the fold of the factors' signs under one list of sign
// facts, through the step's memo (monomialSignMemo), as realFolds is.
type intFolds struct {
	signs []intSignFact
	under *signContext
}

func intFoldsUnder(signs []intSignFact) intFolds {
	shared := make([]signFact, len(signs))
	for i, f := range signs {
		shared[i] = signFact(f)
	}
	return intFolds{signs: signs, under: intMonomialSigns.under(shared)}
}

// sign is the sign m's factors fold to (intMonomialSign).
func (folds intFolds) sign(m Term) (intSignFact, bool) {
	if f, ok, held := intMonomialSigns.lookup(folds.under, m); held {
		return intSignFact(f), ok
	}
	f, ok := intMonomialSign(m, folds.signs)
	intMonomialSigns.store(folds.under, m, signFact(f), ok)
	return f, ok
}
