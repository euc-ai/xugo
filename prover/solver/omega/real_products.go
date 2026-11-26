package omega

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// The degree-2 products of the context — the step Lean's `nlinarith` adds to
// `linarith`. Every comparison the refutation holds, the negated goal included,
// is a nonnegative DIFFERENCE (`l ≤ r` is `&0 ≤ r − l`, `l < r` is `&0 < r − l`,
// an equation is both differences), and the product of two nonnegative
// quantities is nonnegative (LessEqMul; MulPos when both are strict).
// Each pairwise product, squares included, is injected as one more hypothesis
// for a single linear run and cut back afterwards (enrichAndCut), so the
// result rests on the context's own hypotheses. The hypothesis-side signed
// normalizer reads the product (the FOIL over `P + (−N)`), so a product of
// differences is the polynomial row the linear layer combines:
// `x·y = &1 ∧ &0 < x ⊢ &0 < y` closes from `(&0 − y)·x ≥ 0`, the negated
// goal's difference times the sign of x, beside the equation; `a ≤ b ∧ c ≤ d
// ⊢ a·d + b·c ≤ a·c + b·d` from `(b − a)·(d − c) ≥ 0`.
//
// The sign rows (real_sign_rows.go) are the special case of this where the
// factors are the context's own sign facts and the product is a monomial; the
// products pass reaches a product of two arbitrary linear differences, at the
// price of one FOIL per pair, so it runs last in the decide chain, only once
// every cheaper handler has declined, only where some constraint carries a
// product monomial — a context with nothing nonlinear in it gains nothing from
// a quadratic row — and model first: the product rows are read as linear forms
// with no proof (realProductsModel), and a ℚ-Farkas refutation found there
// is the only reason to prove a product and replay. The arith step asks a wide
// context hundreds of questions that decline, and proving seventy-eight
// products for each multiplies the step's time several times over (the
// engine's TestInspect_ArithProbeOnWideRealContext is such a context). The
// model's refutation also names the products it combines — two of them, or none, where the
// pairs are seventy-eight — and those are the products proved: each one
// proved is a FOIL of its own and a sign row for every monomial it brings.
// Every pair is proved only where the proved rows of the named ones do not
// refute as the model's did.
// A strict difference meets a non-strict one through the weakening
// `l < r ⊢ l ≤ r` (realWeakenLt), which reads neither side.
//
// What stays out: products of three or more facts, and products with a
// variable that no fact bounds (`a ≤ b ⊢ a·c ≤ b·c` needs the sign of c) —
// the Positivstellensatz degree is two and the multipliers are the facts.

// productFactCap bounds the base facts multiplied pairwise: n facts give
// n(n+1)/2 products, each one FOIL and one row.
const productFactCap = 12

// realNonnegFact is `{…} ⊢ &0 ⋈ d` for a linear difference d, strict for `<`.
// weak is the non-strict reading of a strict fact, derived once on demand.
type realNonnegFact struct {
	d      Term
	proof  *prop.PropWrapper
	strict bool
	weak   *prop.PropWrapper
}

// realProveProducts decides `{hs} ⊢ goal` with the pairwise products of the
// context's differences added to the refutation. `>`/`≥` go through the
// swapped comparison and `=` through antisymmetry, as realProveWith.
func realProveProducts(hs []Term, goal Term) (*prop.PropWrapper, bool) {
	if a, b, ok := realDomain.matchGt(goal); ok {
		inner, iok := realProveProducts(hs, realLtT(b, a))
		if !iok {
			return nil, false
		}
		return realGtBridge(a, b).EqSym().EqMP(inner), true
	}
	if a, b, ok := realDomain.matchGe(goal); ok {
		inner, iok := realProveProducts(hs, realLeT(b, a))
		if !iok {
			return nil, false
		}
		return realGeBridge(a, b).EqSym().EqMP(inner), true
	}
	if a, b, ok := ext.MatchesEQ(goal); ok && realDomain.isElem(a) {
		if !realDomain.isLinear(a) || !realDomain.isLinear(b) {
			return nil, false
		}
		g1, ok1 := realProveProducts(hs, realLeT(a, b))
		if !ok1 {
			return nil, false
		}
		g2, ok2 := realProveProducts(hs, realLeT(b, a))
		if !ok2 {
			return nil, false
		}
		return mp(mp(realLessEqAntisym(a, b), g1), g2), true
	}
	_, nTerm, finish, ok := realNegateGoal(goal)
	if !ok {
		return nil, false
	}
	all := append(slices.Clone(hs), nTerm)
	cs := realDomain.hypConstraints(slices.Values(all))
	if !realHasProductContent(cs) {
		return nil, false
	}
	// The untrusted model first: the product rows as linear forms, no
	// proof, beside the context's rows — a ℚ-Farkas refutation found there
	// is the only reason to prove a product (one FOIL per pair) and replay.
	used, refutable := realProductsModel(cs)
	if !refutable {
		return nil, false
	}
	// The products the model's refutation combines, and no other. A model
	// that combines no product row refutes from the context's rows beside
	// the negated goal, which is read here as a hypothesis is.
	if facts := realProductFactsOf(cs, used); len(facts) == len(used) {
		if R, ok := realRefuteWithProducts(all, facts); ok {
			return finish(R.NegHyp(nTerm)), true
		}
	}
	// Every pair, where those do not refute: a proved row is the signed
	// normalizer's reading of its product, which may spell a monomial the
	// model's row did not.
	facts := realProductFacts(cs)
	if len(facts) == 0 {
		return nil, false
	}
	R, ok := realRefuteWithProducts(all, facts)
	if !ok {
		return nil, false
	}
	return finish(R.NegHyp(nTerm)), true // R: {hs', nTerm} ⊢ ⊥
}

// realRefuteWithProducts is `{…} ⊢ ⊥` from the context all with the product
// facts added for one linear run and cut back (enrichAndCut): the result
// rests on hypotheses of all.
func realRefuteWithProducts(all []Term, facts []*prop.PropWrapper) (*prop.PropWrapper, bool) {
	return enrichAndCut(func(enriched []Term) (*prop.PropWrapper, bool) {
		return RealLinRefuteProof(realDomain.hypConstraints(slices.Values(enriched)))
	}, all, facts)
}

// realHasProductContent reports whether some constraint side carries a
// product monomial — the only contexts where a quadratic row can matter.
func realHasProductContent(cs []LinConstraint) bool {
	for _, c := range cs {
		if !realDomain.genuinelyLinear(c.Lhs) || !realDomain.genuinelyLinear(c.Rhs) {
			return true
		}
	}
	return false
}

// productSource names a base difference of the products pass: the
// constraint it is read off and, for an equation, which of its two
// differences it is.
type productSource struct {
	constraint int
	swapped    bool
}

// productPair names a product by its two base differences, in the order
// the pass multiplies them.
type productPair struct{ a, b productSource }

// realProductFacts builds the pairwise products of the constraints' nonnegative
// differences: `{…} ⊢ &0 ≤ dᵢ·dⱼ` for i ≤ j (LessEqMul), strict when both
// differences are strict (MulPos).
func realProductFacts(cs []LinConstraint) []*prop.PropWrapper {
	return realProductFactsWhere(cs, func(productPair) bool { return true })
}

// realProductFactsOf builds the products of the pairs in only.
func realProductFactsOf(cs []LinConstraint, only []productPair) []*prop.PropWrapper {
	return realProductFactsWhere(cs, func(p productPair) bool { return slices.Contains(only, p) })
}

// realProductFactsWhere builds the products of the pairs want admits, the
// base differences read and capped as realProductFacts reads them.
func realProductFactsWhere(cs []LinConstraint, want func(productPair) bool) []*prop.PropWrapper {
	var base []realNonnegFact
	var sources []productSource
	for ci, c := range cs {
		if len(base) >= productFactCap {
			break
		}
		switch c.Op {
		case opLE, opLT:
			w := realCanonAssume(c.Lhs, c.Rhs, c.Op, c.Hyp, c.HypProof) // {…} ⊢ Lhs ⋈ Rhs
			if f, ok := realDiffFact(c.Lhs, c.Rhs, w, c.Op == opLT); ok {
				base = append(base, f)
				sources = append(sources, productSource{constraint: ci})
			}
		case opEQ:
			w := c.HypProof
			if w == nil {
				w = prop.Assume(eqT(c.Lhs, c.Rhs))
			}
			if f, ok := realDiffFact(c.Lhs, c.Rhs, mp(realLessEqOfEq(c.Lhs, c.Rhs), w), false); ok {
				base = append(base, f)
				sources = append(sources, productSource{constraint: ci})
			}
			if f, ok := realDiffFact(c.Rhs, c.Lhs, mp(realLessEqOfEqSwapped(c.Lhs, c.Rhs), w), false); ok {
				base = append(base, f)
				sources = append(sources, productSource{constraint: ci, swapped: true})
			}
		}
	}
	if len(base) > productFactCap {
		base = base[:productFactCap]
	}
	var facts []*prop.PropWrapper
	for i := range base {
		for j := i; j < len(base); j++ {
			if !want(productPair{a: sources[i], b: sources[j]}) {
				continue
			}
			fi, fj := &base[i], &base[j]
			strict := fi.strict && fj.strict
			relT, thm := realLeT, realLessEqMulThm()
			pi, pj := fi.proof, fj.proof
			if strict {
				relT, thm = realLtT, realMulPosThm()
			} else {
				pi, pj = fi.weakened(), fj.weakened()
			}
			imp := realImplyLeaf(thm, []Term{fi.d, fj.d},
				imply(relT(realLit(0), fi.d), imply(relT(realLit(0), fj.d), relT(realLit(0), realStarT(fi.d, fj.d)))))
			facts = append(facts, mp(mp(imp, pi), pj)) // {…} ⊢ &0 ⋈ dᵢ·dⱼ
		}
	}
	return facts
}

// weakened is the fact's non-strict reading `{…} ⊢ &0 ≤ d`: itself when the
// fact is non-strict, else the weakening of `{…} ⊢ &0 < d`, derived once.
func (f *realNonnegFact) weakened() *prop.PropWrapper {
	if !f.strict {
		return f.proof
	}
	if f.weak == nil {
		f.weak = realWeakenLt(realLit(0), f.d, f.proof)
	}
	return f.weak
}

// realWeakenLt turns `Γ ⊢ l < r` into `Γ ⊢ l ≤ r`. The linear prover answers
// `a < b ⊢ a ≤ b` over two variables and the answer is instantiated at l and
// r, so the sides are read by no normalizer: a difference `y − x`, which the
// linear prover does not take as a goal side, weakens as an atom does.
func realWeakenLt(l, r Term, w *prop.PropWrapper) *prop.PropWrapper {
	a, b := ext.Var("a", dsl.RealType), ext.Var("b", dsl.RealType)
	lin, ok := RealLinProve(slices.Values([]Term{realLtT(a, b)}), realLeT(a, b))
	if !ok {
		panic("omega: the real linear prover declined a < b ⊢ a ≤ b")
	}
	at := lin.TermInst(core.MakeTermSubst(a.AssertVar(), l), core.MakeTermSubst(b.AssertVar(), r)) // {l < r} ⊢ l ≤ r
	return prop.WrapProp(w.MaybeDeriveTrans(at))
}

// realDiffFact turns `{…} ⊢ L ⋈ R` into the nonnegative difference `{…} ⊢ &0
// ⋈ R − L` — through LessEqSubAddLeft / LessThanSubAddLeft at `(&0 ⋈ R − L) ⇔
// (&0 + L ⋈ R)` and the ring identity `&0 + L = L`. A fact that already
// states a sign (`&0 ⋈ R`) is its own difference.
func realDiffFact(L, R Term, w *prop.PropWrapper, strict bool) (realNonnegFact, bool) {
	if isRealZero(L) {
		return realNonnegFact{d: R, proof: w, strict: strict}, true
	}
	zl, ok := RealRingProveFull(realPlusT(realLit(0), L), L) // ⊢ &0 + L = L
	if !ok {
		return realNonnegFact{}, false
	}
	rel, ladd := realLe, realLessEqSubAddLeft
	if strict {
		rel, ladd = realLt, realLessThanSubAddLeft
	}
	cong := zl.LeftApply(rel).RightApply(R) // ⊢ (&0 + L ⋈ R) = (L ⋈ R)
	w2 := cong.EqSym().EqMP(w)              // {…} ⊢ &0 + L ⋈ R
	bridge := ladd(realLit(0), R, L)        // ⊢ (&0 ⋈ R − L) ⇔ (&0 + L ⋈ R)
	return realNonnegFact{d: realSubT(R, L), proof: bridge.EqSym().EqMP(w2), strict: strict}, true
}

// realProductsModel is the untrusted half of the products pass: the
// pairwise product rows as linear constraints over the monomial basis with
// NO proof (`Rᵢ·Lⱼ + Lᵢ·Rⱼ ⋈ Rᵢ·Rⱼ + Lᵢ·Lⱼ` for the differences Rᵢ − Lᵢ and
// Rⱼ − Lⱼ, strict when both are), read for a ℚ-Farkas refutation beside the
// context's rows and the sign rows of the monomials in sight. A context
// whose products refute nothing costs one model run and never a kernel FOIL
// — on a wide context (thirteen hypotheses, quotients read as products) the
// arith step asks hundreds of questions that decline, and proving
// seventy-eight products for each was the whole cost. Over ℤ the check is
// ℚ-Farkas only, so a refutation that needs the integer cuts AND a product
// is declined here.
//
// The sign rows are the proving half's own (realMonomialSignRows): of the
// monomials of the model's rows, from the signs the context states. So the
// model refutes what the proving half would. A refutation that needs a
// square's unconditional sign and a product is found here, in the context
// that states it, and is not left to a case split whose branch happens to
// open the model another way. One reading of the sign rules serves both
// halves; the model pays for it one pass over its own rows per run, and a
// larger table to refute over. The signs themselves are folded once for
// the step (monomialSignMemo): the model's rows are the products of the
// same differences from one question to the next. The signs are the context's and not the product rows': a product
// row that states a sign — a sign fact times a difference of an equation
// with a zero side — is a row the refutation combines under its own pair,
// and the proving half is told of it.
//
// used is the product rows the refutation found combines, each named by its
// pair: the products the proving half proves.
func realProductsModel(cs []LinConstraint) (used []productPair, refutable bool) {
	rows, pairs := realProductRows(cs)
	if len(rows) == 0 {
		return nil, false
	}
	// The product rows follow the context's, one row each; an equation of
	// the context is two rows.
	first := 0
	for _, c := range cs {
		first++
		if c.Op == opEQ {
			first++
		}
	}
	model := append(slices.Clone(cs), rows...)
	model = append(model, realMonomialSignRows(cs, model)...)
	tbl, signed, _, built := realBuildAll(model)
	if !built {
		return nil, false
	}
	lambda, ok := refute(tbl.n(), signed)
	if !ok {
		return nil, false
	}
	for k := range rows {
		if lambda[first+k].sign() > 0 {
			used = append(used, pairs[k])
		}
	}
	return used, true
}

// realProductRows builds the product rows of the model, in the order
// realProductFacts proves them: the base differences of the comparison and
// equation constraints (an equation is two), capped as the facts are,
// then every pair i ≤ j through the domain's checked polynomial product,
// each row with the pair it is the product of.
func realProductRows(cs []LinConstraint) ([]LinConstraint, []productPair) {
	type diff struct {
		l, r   linForm
		strict bool
		source productSource
	}
	var base []diff
	for ci, c := range cs {
		if len(base) >= productFactCap {
			break
		}
		lf, ok1 := realDomain.linOf(c.Lhs)
		rf, ok2 := realDomain.linOf(c.Rhs)
		if !ok1 || !ok2 {
			continue
		}
		switch c.Op {
		case opLE, opLT:
			base = append(base, diff{l: lf, r: rf, strict: c.Op == opLT, source: productSource{constraint: ci}})
		case opEQ:
			base = append(base, diff{l: lf, r: rf, source: productSource{constraint: ci}},
				diff{l: rf, r: lf, source: productSource{constraint: ci, swapped: true}})
		}
	}
	if len(base) > productFactCap {
		base = base[:productFactCap]
	}
	var rows []LinConstraint
	var pairs []productPair
	for i := range base {
		for j := i; j < len(base); j++ {
			a, b := base[i], base[j]
			rl, ok1 := realDomain.polyMul(a.r, b.l)
			lr, ok2 := realDomain.polyMul(a.l, b.r)
			rr, ok3 := realDomain.polyMul(a.r, b.r)
			ll, ok4 := realDomain.polyMul(a.l, b.l)
			if !ok1 || !ok2 || !ok3 || !ok4 {
				continue
			}
			op := opLE
			if a.strict && b.strict {
				op = opLT
			}
			rows = append(rows, LinConstraint{Lhs: realDomain.buildTerm(linAdd(rl, lr)), Rhs: realDomain.buildTerm(linAdd(rr, ll)), Op: op})
			pairs = append(pairs, productPair{a: a.source, b: b.source})
		}
	}
	return rows, pairs
}
