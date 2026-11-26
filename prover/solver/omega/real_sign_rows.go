package omega

import (
	"slices"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The sign of a MONOMIAL, supplied to the ℝ linear refutation as extra rows.
//
// Since the monomial basis (domain.go polyMul), a product of variables is one
// unknown to the linear layer — and over ℝ a bare unknown carries no sign at
// all, where `num` gets a `0 ≤ x` row per atom from buildAll. So a refutation
// that turns on `a·b ≥ 0` cannot find it: nothing in the row set relates the
// monomial to the factors whose signs the context states. The sign-known
// handlers (real_ops.go realProveSignedProduct) answer the same question, but
// only about a GOAL, and only when the goal IS the product's sign.
//
// This pass supplies exactly those rows. For each product monomial in the
// constraint set it tries, in order:
//
//   - the SQUARE reading — every base atom occurs an even number of times, so
//     the monomial IS a square `t·t` (the full ring proves the regrouping) and
//     SquareNonneg gives `&0 ≤ m` with no hypothesis at all. This is what
//     lets `x·x ≤ y ⊢ &0 ≤ y` and `x·x + y·y = &0 ⊢ x·x = &0` close;
//   - the FACTORS' SIGNS — every base atom has a sign among the constraints
//     (`&0 < f`, `&0 ≤ f`, `f < &0`, `f ≤ &0`), folded pairwise through
//     LessEqMul / MulPos and the neg-order flips, exactly as the
//     goal-side realProveSignedProduct folds a binary product.
//
// The factors need not be the monomial's BASE atoms. A sign the context
// states about a product — `&0 < a·b`, or a quotient `&0 < e / d`, which the
// quotient basis reads as the monomial e·inv(d) — is the sign of a PIECE of
// every monomial that product divides: `&0 < e / d` and `&0 < e` price
// e·e·inv(d), where neither inv(d) nor d has a sign of its own in sight
// (realMonomialSignByPieces). And an inverse atom takes its sign from its
// argument's, as the goal-side realProveFactorSign reads it.
//
// Each derived fact rides as a `LinConstraint` whose `HypProof` is the proof
// just built. Because that proof is assembled from the SOURCE constraints'
// own proofs (realCanonAssume, which already honours `Hyp`/`HypProof`), its
// hypotheses are theirs, and the refutation's hypotheses stay a subset of the
// goal's — the IsStronger contract — including when a source constraint was
// projected out of a conjunction.
//
// A pair of factors whose signs differ in strictness (`&0 < a` with `&0 ≤ b`)
// folds to the non-strict sign of the product, the strict fact weakened
// first (realWeakenLt).
//
// One thing it deliberately does not do: it never infers a FACTOR's sign
// from the monomial's (`x·y = &1 ∧ &0 < x ⊢ &0 < y`). That is division by a
// variable, which is the cancel handler's business, not a row's.

// realSignFact is a proved sign for a term: `&0 ⋈ term` when nonneg is true,
// `term ⋈ &0` when it is false, with strict selecting `<` over `≤`.
type realSignFact struct {
	term   Term
	proof  *prop.PropWrapper
	nonneg bool
	strict bool
}

// realConstraintSign reads a constraint that states the sign of a single term
// — one side is the literal `&0` — and returns that term's sign fact. The
// proof comes from realCanonAssume, so a constraint carrying a projection or
// a `>`/`≥` origin contributes the provenance it was built with. ok=false for
// an equation or a comparison between two non-zero sides.
func realConstraintSign(c LinConstraint) (realSignFact, bool) {
	if c.Op != opLE && c.Op != opLT {
		return realSignFact{}, false
	}
	strict := c.Op == opLT
	switch {
	case isRealZero(c.Lhs) && !isRealZero(c.Rhs):
		return realSignFact{term: c.Rhs, proof: realCanonAssume(c.Lhs, c.Rhs, c.Op, c.Hyp, c.HypProof),
			nonneg: true, strict: strict}, true
	case isRealZero(c.Rhs) && !isRealZero(c.Lhs):
		return realSignFact{term: c.Lhs, proof: realCanonAssume(c.Lhs, c.Rhs, c.Op, c.Hyp, c.HypProof),
			nonneg: false, strict: strict}, true
	}
	return realSignFact{}, false
}

// realFactorSigns collects every sign the constraint set states. The fold
// needs one sign per factor, and a term with several sign constraints
// keeps the strongest: a strict one stated after a non-strict one of the
// same direction takes its place, whatever order the set holds them in —
// `&0 ≤ |z|`, which holds of every modulus, must not stand in for a
// resident `&0 < |z|`.
func realFactorSigns(cs []LinConstraint) []realSignFact {
	var signs []realSignFact
	for _, c := range cs {
		f, ok := realConstraintSign(c)
		if !ok {
			continue
		}
		if i := slices.IndexFunc(signs, func(s realSignFact) bool { return s.term.AlphaEquals(f.term) }); i >= 0 {
			if f.strict && !signs[i].strict && f.nonneg == signs[i].nonneg {
				signs[i] = f
			}
			continue
		}
		signs = append(signs, f)
	}
	return signs
}

// realLookupSign finds the sign fact for a factor.
func realLookupSign(signs []realSignFact, factor Term) (realSignFact, bool) {
	i := slices.IndexFunc(signs, func(s realSignFact) bool { return s.term.AlphaEquals(factor) })
	if i < 0 {
		return realSignFact{}, false
	}
	return signs[i], true
}

// realNonnegForm restates a sign fact as `&0 ⋈ g`: g is the term itself when
// the fact is already nonneg, else `−term`, the proof carried across by the
// neg-order iff (NegNonnegativeIffNonpositive / NegPositiveIffNegative). The multiplication leaves take
// both operands in this form.
func realNonnegForm(f realSignFact) (Term, *prop.PropWrapper) {
	if f.nonneg {
		return f.term, f.proof
	}
	relT, thm := realLeT, realNegNonnegativeIffNonpositiveThm()
	if f.strict {
		relT, thm = realLtT, realNegPositiveIffNegativeThm()
	}
	neg := realNegT(f.term)
	// ⊢ (&0 ⋈ −t) = (t ⋈ &0); the fact proves the right side.
	iff := realEqLeaf(thm, []Term{f.term}, relT(realLit(0), neg), relT(f.term, realLit(0)))
	return neg, iff.EqSym().EqMP(f.proof)
}

// realMulPosFromProofs applies LessEqMul / MulPos to two proved
// nonnegativities: `Γ ⊢ &0 ⋈ a` and `Γ ⊢ &0 ⋈ b` give `Γ ⊢ &0 ⋈ a·b`. The
// side-condition-discharging twin is realMulPosLemma (real_ops.go), which
// proves the two premises from the hypotheses instead of taking them.
func realMulPosFromProofs(a0, b0 *prop.PropWrapper, a, b Term, strict bool) *prop.PropWrapper {
	relT, thm := realLeT, realLessEqMulThm()
	if strict {
		relT, thm = realLtT, realMulPosThm()
	}
	imp := realImplyLeaf(thm, []Term{a, b},
		imply(relT(realLit(0), a), imply(relT(realLit(0), b), relT(realLit(0), realStarT(a, b)))))
	return mp(mp(imp, a0), b0)
}

// realWeakSign is a sign fact's non-strict reading: itself when it is
// non-strict, else `&0 ≤ term` from `&0 < term` (`term ≤ &0` from `term < &0`).
func realWeakSign(f realSignFact) realSignFact {
	if !f.strict {
		return f
	}
	l, r := realLit(0), f.term
	if !f.nonneg {
		l, r = f.term, realLit(0)
	}
	return realSignFact{term: f.term, proof: realWeakenLt(l, r, f.proof), nonneg: f.nonneg}
}

// realMulSigns multiplies two sign facts into the sign of their product,
// mirroring realProveSignedProduct's four cases with the premises already
// proved. The product is strict when both facts are; a strict fact beside a
// non-strict one is weakened first.
func realMulSigns(fa, fb realSignFact) (realSignFact, bool) {
	if fa.strict != fb.strict {
		fa, fb = realWeakSign(fa), realWeakSign(fb)
	}
	strict := fa.strict
	ga, pa := realNonnegForm(fa)
	gb, pb := realNonnegForm(fb)
	prodG := realMulPosFromProofs(pa, pb, ga, gb, strict) // ⊢ &0 ⋈ ga·gb
	prod := realStarT(fa.term, fb.term)
	rel, relT := realLe, realLeT
	if strict {
		rel, relT = realLt, realLtT
	}
	switch {
	case fa.nonneg && fb.nonneg: // ga·gb IS a·b
		return realSignFact{term: prod, proof: prodG, nonneg: true, strict: strict}, true
	case !fa.nonneg && !fb.nonneg: // (−a)·(−b) = a·b
		cong := realSubneg.negNegMul(fa.term, fb.term).LeftApply(ext.Apply(rel, realLit(0)))
		return realSignFact{term: prod, proof: cong.EqMP(prodG), nonneg: true, strict: strict}, true
	case fa.nonneg: // a·(−b) = −(a·b), so the product is nonpositive
		w, ok := realFlipNeg(prodG, realSubneg.mulRightNeg(fa.term, fb.term), prod, rel, relT, strict)
		if !ok {
			return realSignFact{}, false
		}
		return realSignFact{term: prod, proof: w, nonneg: false, strict: strict}, true
	default: // (−a)·b = −(a·b)
		w, ok := realFlipNeg(prodG, realSubneg.negLmul(fa.term, fb.term), prod, rel, relT, strict)
		if !ok {
			return realSignFact{}, false
		}
		return realSignFact{term: prod, proof: w, nonneg: false, strict: strict}, true
	}
}

// realMonomialSign folds the factors' signs along the monomial's own nesting.
// The accumulated term must come out α-equal to the monomial: a monomial the
// polyMul fuse left as one opaque product may be nested some other way, and a
// row about a differently-spelled term would be a row about a different atom.
func realMonomialSign(m Term, signs []realSignFact) (realSignFact, bool) {
	factors := realDecomposeStar(m)
	if len(factors) < 2 {
		return realSignFact{}, false
	}
	acc, ok := realLookupSign(signs, factors[0])
	if !ok {
		return realSignFact{}, false
	}
	for _, factor := range factors[1:] {
		next, ok := realLookupSign(signs, factor)
		if !ok {
			return realSignFact{}, false
		}
		if acc, ok = realMulSigns(acc, next); !ok {
			return realSignFact{}, false
		}
	}
	if !acc.term.AlphaEquals(m) {
		return realSignFact{}, false
	}
	return acc, true
}

// realSignPiece is a sign fact together with the base atoms of the monomial
// its term denotes, Compare-sorted — what the fact is the sign OF, in the
// basis the rows are written over.
type realSignPiece struct {
	fact    realSignFact
	factors []Term
}

// realMonomialFactors reads t as one monomial with coefficient 1 and returns
// its base atoms, sorted. ok=false for a sum, a scaled term or a constant.
func realMonomialFactors(t Term) ([]Term, bool) {
	lf, ok := realDomain.linOf(t)
	if !ok || !lf.konst.isZero() || len(lf.monos) != 1 || !lf.monos[0].coeff.isOne() {
		return nil, false
	}
	factors := slices.Clone(realDecomposeStar(lf.monos[0].atom))
	slices.SortStableFunc(factors, func(a, b Term) int { return a.Compare(b) })
	return factors, true
}

// realInverseSign derives the sign of `inv x` from a stated nonnegative or
// positive sign of x: ⊢ (&0 ⋈ inv x) = (&0 ⋈ x) (InvNonneg /
// InvPos), read backwards. A negative x is left to a stated sign of
// the inverse itself.
func realInverseSign(inv Term, signs []realSignFact) (realSignFact, bool) {
	x, ok := MatchesRealInv(inv)
	if !ok {
		return realSignFact{}, false
	}
	of, ok := realLookupSign(signs, x)
	if !ok || !of.nonneg {
		return realSignFact{}, false
	}
	relT, thm := realLeT, realInvNonnegThm()
	if of.strict {
		relT, thm = realLtT, realInvPosThm()
	}
	iff := realEqLeaf(thm, []Term{x}, relT(realLit(0), inv), relT(realLit(0), x))
	return realSignFact{term: inv, proof: iff.EqSym().EqMP(of.proof), nonneg: true, strict: of.strict}, true
}

// realSignPieces is every sign the context states about a monomial, with
// the inverse atoms of target priced from their arguments where the context
// prices those, and a product of inverses priced from the product: the
// inverse basis reads inv(a·b) as the monomial inv(a)·inv(b)
// (quotient_basis.go), so a sign stated of a·b — which says nothing of a or
// of b alone — is the sign of that pair of atoms together.
func realSignPieces(signs []realSignFact, target []Term) []realSignPiece {
	var pieces []realSignPiece
	for _, f := range signs {
		if factors, ok := realMonomialFactors(f.term); ok {
			pieces = append(pieces, realSignPiece{fact: f, factors: factors})
		}
		if _, _, isProduct := realDomain.matchStar(f.term); !isProduct {
			continue
		}
		inv := realInvT(f.term)
		factors, ok := realMonomialFactors(inv)
		if !ok || len(factors) < 2 {
			continue
		}
		if _, divides := removeFactors(target, factors); !divides {
			continue
		}
		if of, ok := realInverseSign(inv, signs); ok {
			pieces = append(pieces, realSignPiece{fact: of, factors: factors})
		}
	}
	for i, atom := range target {
		if i > 0 && target[i-1].Compare(atom) == 0 {
			continue
		}
		if slices.ContainsFunc(pieces, func(p realSignPiece) bool {
			return len(p.factors) == 1 && p.factors[0].AlphaEquals(atom)
		}) {
			continue
		}
		if f, ok := realInverseSign(atom, signs); ok {
			pieces = append(pieces, realSignPiece{fact: f, factors: []Term{atom}})
		}
	}
	return pieces
}

// realCoverSign multiplies pieces into the sign of the monomial whose base
// atoms are target: a piece that holds target's first atom and divides
// target, then a cover of what is left. A piece may serve twice (`&0 < e`
// prices both e's of e·e). The first cover whose signs fold is taken; one
// whose fold declines gives way to the next.
func realCoverSign(target []Term, pieces []realSignPiece) (realSignFact, bool) {
	for _, p := range pieces {
		if !slices.ContainsFunc(p.factors, func(a Term) bool { return a.Compare(target[0]) == 0 }) {
			continue
		}
		rest, ok := removeFactors(target, p.factors)
		if !ok {
			continue
		}
		if len(rest) == 0 {
			return p.fact, true
		}
		tail, ok := realCoverSign(rest, pieces)
		if !ok {
			continue
		}
		if prod, ok := realMulSigns(p.fact, tail); ok {
			return prod, true
		}
	}
	return realSignFact{}, false
}

// signBridgeMemo memoizes the ring equations the sign rows carry a sign
// across — `⊢ product = m` for a monomial priced by pieces, `⊢ m = root·root`
// for a square. The rows are rebuilt by every linarith run, once per atom per
// direction per case-split level, over monomials that do not change from
// one run to the next; the equation is a full ring normalization of both
// sides with a kernel derivation behind it, and on a thirteen-hypothesis
// ε-δ context whose quotients the basis reads as products it was nine
// tenths of the rows' cost. It is a theorem with no hypotheses and a
// function of its two terms and the lemma bundle alone, so an entry is
// keyed by the pair — the hit test EXACT equality on both, the AlphaKeys
// only the bucket — a decline is kept as well as a proof, and the bundle
// setters drop the memo with the constraint memos (resetConstraintMemos).
// Released with the step's other memos (ReleaseStepMemos) and bounded
// within the step as their proofs are.
type signBridgeMemo struct {
	mu      sync.Mutex
	entries map[signBridgeKey]signBridgeEntry
}

type signBridgeKey struct{ l, r core.TermKey }

type signBridgeEntry struct {
	l, r  Term
	proof *prop.PropWrapper // nil: the ring declined
}

var realSignBridgeMemo signBridgeMemo

func (m *signBridgeMemo) lookup(l, r Term) (signBridgeEntry, bool) {
	m.mu.Lock()
	defer m.mu.Unlock()
	e, ok := m.entries[signBridgeKey{l.AlphaKey(), r.AlphaKey()}]
	if !ok || !e.l.Equals(l) || !e.r.Equals(r) {
		return signBridgeEntry{}, false
	}
	return e, true
}

func (m *signBridgeMemo) store(e signBridgeEntry) {
	m.mu.Lock()
	defer m.mu.Unlock()
	if len(m.entries) >= linMemoProofCap {
		m.entries = nil
	}
	if m.entries == nil {
		m.entries = make(map[signBridgeKey]signBridgeEntry)
	}
	m.entries[signBridgeKey{e.l.AlphaKey(), e.r.AlphaKey()}] = e
}

func (m *signBridgeMemo) reset() {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.entries = nil
}

// realSignBridge is the memoized RealRingProveFull of the sign rows.
func realSignBridge(l, r Term) (*prop.PropWrapper, bool) {
	if e, ok := realSignBridgeMemo.lookup(l, r); ok {
		return e.proof, e.proof != nil
	}
	proof, ok := RealRingProveFull(l, r)
	if !ok {
		proof = nil
	}
	realSignBridgeMemo.store(signBridgeEntry{l: l, r: r, proof: proof})
	return proof, ok
}

// realMonomialSignByPieces prices a monomial from the signs the context
// states about pieces of it. The pieces' product is some other nesting of
// m's atoms — and may spell a quotient where m spells the inverse — so the
// full ring carries the sign across `⊢ product = m`.
func realMonomialSignByPieces(m Term, signs []realSignFact) (realSignFact, bool) {
	target := slices.Clone(realDecomposeStar(m))
	if len(target) < 2 {
		return realSignFact{}, false
	}
	slices.SortStableFunc(target, func(a, b Term) int { return a.Compare(b) })
	acc, ok := realCoverSign(target, realSignPieces(signs, target))
	if !ok {
		return realSignFact{}, false
	}
	if acc.term.AlphaEquals(m) {
		return acc, true
	}
	eq, ok := realSignBridge(acc.term, m) // ⊢ product = m
	if !ok {
		return realSignFact{}, false
	}
	rel := realLe
	if acc.strict {
		rel = realLt
	}
	var cong *prop.PropWrapper
	if acc.nonneg {
		cong = eq.LeftApply(ext.Apply(rel, realLit(0))) // ⊢ (&0 ⋈ product) = (&0 ⋈ m)
	} else {
		cong = eq.LeftApply(rel).RightApply(realLit(0)) // ⊢ (product ⋈ &0) = (m ⋈ &0)
	}
	return realSignFact{term: m, proof: cong.EqMP(acc.proof), nonneg: acc.nonneg, strict: acc.strict}, true
}

// realSquareSign proves `⊢ &0 ≤ m` for a monomial whose every base atom
// occurs an even number of times: m is then the square of the product of the
// halved multiplicities, the full ring proves that regrouping, and
// SquareNonneg prices it. Hypothesis-free — this is the one sign the
// context does not have to state.
//
// The sign of a square is kept per monomial (realSquareSigns), a decline of
// the ring as a proof is. It is a theorem with no hypotheses, a function of
// m and the lemma bundle alone, and it is asked for at every even monomial
// of every linear run and of every run of the products pass's model, whose
// rows are built again from the same differences each time
// (real_products.go).
func realSquareSign(m Term) (*prop.PropWrapper, bool) {
	factors := realDecomposeStar(m)
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
	if rows, held := realSquareSigns.lookup(m); held {
		if len(rows) == 0 {
			return nil, false
		}
		return rows[0].HypProof, true
	}
	root := realRing.monoProductOf(half)
	square := realStarT(root, root)
	eq, ok := realSignBridge(m, square) // ⊢ m = root·root
	if !ok {
		realSquareSigns.store(m, nil)
		return nil, false
	}
	nonneg := realImplyLeaf(realSquareNonnegThm(), []Term{root}, realLeT(realLit(0), square))
	cong := eq.LeftApply(ext.Apply(realLe, realLit(0))) // ⊢ (&0 ≤ m) = (&0 ≤ root·root)
	sign := cong.EqSym().EqMP(nonneg)
	realSquareSigns.store(m, []LinConstraint{{Lhs: realLit(0), Rhs: m, Op: opLE, HypProof: sign}})
	return sign, true
}

// realSquareSigns memoizes realSquareSign: per even monomial m its row
// `&0 ≤ m`, or no row where the ring declined the regrouping. The constraint
// memo's hit test and bound; the bundle setters drop it with the others
// (resetConstraintMemos).
var realSquareSigns constraintMemo

// realOfNumNonneg proves `⊢ &0 ≤ &n` for a `real_of_num` atom: the of_num order
// bridge read against num's own `0 ≤ n`. `&n` is nonnegative because n is, and
// no bundle field of its own is needed — a SYMBOLIC `&n` is otherwise an
// unknown like any other, since ℝ injects no nonnegativity row per atom the way
// num does. (A literal `&5` never reaches here: asLiteral reads it as a
// constant, not an atom.)
func realOfNumNonneg(atom Term) (*prop.PropWrapper, bool) {
	n, ok := MatchesRealOfNum(atom)
	if !ok {
		return nil, false
	}
	// ⊢ (&0 ≤ &n) = (0 ≤ n), read right-to-left against the num fact.
	bridge := realEqLeaf(realOfNumLessEqThm(), []Term{Numeral(0), n},
		realLeT(realLit(0), atom), le(Numeral(0), n))
	return bridge.EqSym().EqMP(zeroLe(n)), true
}

// realCastFactorSigns adds to signs the sign of every `&n` factor of the
// monomials, where the set states none of its own: a cast is nonnegative
// because its num is (realOfNumNonneg). A product of casts — what the
// cast basis reads `&(a * b)` as — then has, by the fold, the sign the one
// unknown `&(a * b)` has.
func realCastFactorSigns(signs []realSignFact, monos []Term) []realSignFact {
	for _, m := range monos {
		for _, factor := range realDecomposeStar(m) {
			if _, stated := realLookupSign(signs, factor); stated {
				continue
			}
			if w, ok := realOfNumNonneg(factor); ok {
				signs = append(signs, realSignFact{term: factor, proof: w, nonneg: true})
			}
		}
	}
	return signs
}

// realSignAtoms picks, among the atoms a constraint set's linear forms are
// written over (Domain.atomsOf), those a sign row could be about: the
// product monomials, the `&n` coercions, and the inverses standing alone.
func realSignAtoms(atoms []Term) []Term {
	var bearing []Term
	for _, atom := range atoms {
		_, _, isProduct := realDomain.matchStar(atom)
		_, isOfNum := MatchesRealOfNum(atom)
		_, isInv := MatchesRealInv(atom)
		if isProduct || isOfNum || isInv {
			bearing = append(bearing, atom)
		}
	}
	return bearing
}

// realMonomialSignConstraints derives the sign rows for the constraint set's
// sign-bearing atoms. Returns nil — at the cost of one linOf pass — when the
// set has none, which is every purely linear goal over free variables.
func realMonomialSignConstraints(cs []LinConstraint) []LinConstraint {
	return realMonomialSignRows(cs, cs)
}

// realMonomialSignRows derives the sign rows for the sign-bearing atoms of
// over from the signs that facts states. The linear refutation reads both
// off one set (realMonomialSignConstraints). The products pass's model
// reads the atoms off its rows, the product rows among them, and the signs
// off the context alone (real_products.go): a product row that states a
// sign is then a row of the model's refutation in its own name, never a
// sign row's premise.
func realMonomialSignRows(facts, over []LinConstraint) []LinConstraint {
	atoms := realDomain.atomsOf(over)
	// A power left one unknown for its sub/neg base gets its expansion
	// (subneg.go powExpansionRow), whether or not a product is in the set.
	extra := realSubneg.powExpansionRows(atoms)
	monos := realSignAtoms(atoms)
	if len(monos) == 0 {
		return extra
	}
	signs := realCastFactorSigns(realFactorSigns(facts), monos)
	folds := realFoldsUnder(signs)
	for _, m := range monos {
		if w, ok := realOfNumNonneg(m); ok { // `&n` is nonnegative because n is
			extra = append(extra, LinConstraint{Lhs: realLit(0), Rhs: m, Op: opLE, HypProof: w})
			continue
		}
		// An inverse standing alone takes its sign from its argument's, as an
		// inverse factor of a product does — unless the set states its own.
		if _, isInv := MatchesRealInv(m); isInv {
			if _, stated := realLookupSign(signs, m); stated {
				continue
			}
			if f, ok := realInverseSign(m, signs); ok {
				op := opLE
				if f.strict {
					op = opLT
				}
				extra = append(extra, LinConstraint{Lhs: realLit(0), Rhs: m, Op: op, HypProof: f.proof})
			}
			continue
		}
		// A product carrying a subtraction inside a square is one unknown
		// here (subneg.go's guard); its expansion rides beside its sign.
		if r, ok := realSubneg.expansionRow(m); ok {
			extra = append(extra, r)
		}
		// Both readings are emitted, never one instead of the other: an even
		// monomial whose factors are all POSITIVE is strictly positive, and
		// the square reading alone gives only `&0 ≤ m`. Letting it preempt
		// the fold cost real_sqrt.ApproachFromAbove its close, whose last
		// step needs `&0 < w·w` from `&0 < w`. Two rows about one monomial
		// are independently proved and cost the refutation nothing.
		if w, ok := realSquareSign(m); ok {
			extra = append(extra, LinConstraint{Lhs: realLit(0), Rhs: m, Op: opLE, HypProof: w})
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
			extra = append(extra, LinConstraint{Lhs: realLit(0), Rhs: m, Op: op, HypProof: f.proof})
		} else {
			extra = append(extra, LinConstraint{Lhs: m, Rhs: realLit(0), Op: op, HypProof: f.proof})
		}
	}
	return extra
}

// realFolds is the fold of the factors' signs under one list of sign
// facts, through the step's memo (monomialSignMemo).
type realFolds struct {
	signs []realSignFact
	under *signContext
}

func realFoldsUnder(signs []realSignFact) realFolds {
	shared := make([]signFact, len(signs))
	for i, f := range signs {
		shared[i] = signFact(f)
	}
	return realFolds{signs: signs, under: realMonomialSigns.under(shared)}
}

// sign is the sign m's factors fold to: the base atoms' own signs, and
// where those do not fold the signs stated about larger pieces and the
// inverses' arguments.
func (folds realFolds) sign(m Term) (realSignFact, bool) {
	if f, ok, held := realMonomialSigns.lookup(folds.under, m); held {
		return realSignFact(f), ok
	}
	f, ok := realMonomialSign(m, folds.signs)
	if !ok {
		f, ok = realMonomialSignByPieces(m, folds.signs)
	}
	realMonomialSigns.store(folds.under, m, signFact(f), ok)
	return f, ok
}
