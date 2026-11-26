package omega

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// The degree-2 products of the context over ℤ — real_products.go's twin, on
// the int vocabulary and the ℤ refuter (IntLinRefuteProof, so a product row
// meets discreteness and the gcd cuts like any other). Same shape, same cap,
// same place in the decide chain, and the same two halves: the model's
// refutation names the products the proving half proves.

// intNonnegFact is `{…} ⊢ &0 ⋈ d` for a linear difference d, strict for `<`.
// weak is the non-strict reading of a strict fact, derived once on demand.
type intNonnegFact struct {
	d      Term
	proof  *prop.PropWrapper
	strict bool
	weak   *prop.PropWrapper
}

// intProveProducts decides `{hs} ⊢ goal` with the pairwise products of the
// context's differences added to the refutation. `>`/`≥` go through the
// swapped comparison and `=` through antisymmetry, as intProveWith.
func intProveProducts(hs []Term, goal Term) (*prop.PropWrapper, bool) {
	if a, b, ok := intDomain.matchGt(goal); ok {
		inner, iok := intProveProducts(hs, intLtT(b, a))
		if !iok {
			return nil, false
		}
		return intGtBridge(a, b).EqSym().EqMP(inner), true
	}
	if a, b, ok := intDomain.matchGe(goal); ok {
		inner, iok := intProveProducts(hs, intLeT(b, a))
		if !iok {
			return nil, false
		}
		return intGeBridge(a, b).EqSym().EqMP(inner), true
	}
	if a, b, ok := ext.MatchesEQ(goal); ok && intDomain.isElem(a) {
		if !intDomain.isLinear(a) || !intDomain.isLinear(b) {
			return nil, false
		}
		g1, ok1 := intProveProducts(hs, intLeT(a, b))
		if !ok1 {
			return nil, false
		}
		g2, ok2 := intProveProducts(hs, intLeT(b, a))
		if !ok2 {
			return nil, false
		}
		return mp(mp(intLessEqAntisym(a, b), g1), g2), true
	}
	_, nTerm, finish, ok := intNegateGoal(goal)
	if !ok {
		return nil, false
	}
	all := append(slices.Clone(hs), nTerm)
	cs := intDomain.hypConstraints(slices.Values(all))
	if !intHasProductContent(cs) {
		return nil, false
	}
	// The untrusted model first: the product rows as linear forms, no
	// proof, beside the context's rows — a ℚ-Farkas refutation found there
	// is the only reason to prove a product (one FOIL per pair) and replay.
	used, refutable := intProductsModel(cs)
	if !refutable {
		return nil, false
	}
	// The products the model's refutation combines, and no other, as in
	// the real twin.
	if facts := intProductFactsOf(cs, used); len(facts) == len(used) {
		if R, ok := intRefuteWithProducts(all, facts); ok {
			return finish(R.NegHyp(nTerm)), true
		}
	}
	// Every pair, where those do not refute.
	facts := intProductFacts(cs)
	if len(facts) == 0 {
		return nil, false
	}
	R, ok := intRefuteWithProducts(all, facts)
	if !ok {
		return nil, false
	}
	return finish(R.NegHyp(nTerm)), true // R: {hs', nTerm} ⊢ ⊥
}

// intRefuteWithProducts is `{…} ⊢ ⊥` from the context all with the product
// facts added for one linear run and cut back (enrichAndCut): the result
// rests on hypotheses of all.
func intRefuteWithProducts(all []Term, facts []*prop.PropWrapper) (*prop.PropWrapper, bool) {
	return enrichAndCut(func(enriched []Term) (*prop.PropWrapper, bool) {
		return IntLinRefuteProof(intDomain.hypConstraints(slices.Values(enriched)))
	}, all, facts)
}

// intHasProductContent reports whether some constraint side carries a
// product monomial — the only contexts where a quadratic row can matter.
func intHasProductContent(cs []LinConstraint) bool {
	for _, c := range cs {
		if !intDomain.genuinelyLinear(c.Lhs) || !intDomain.genuinelyLinear(c.Rhs) {
			return true
		}
	}
	return false
}

// intProductFacts builds the pairwise products of the constraints' nonnegative
// differences: `{…} ⊢ &0 ≤ dᵢ·dⱼ` for i ≤ j (LessEqMul), strict when both
// differences are strict (MulPos).
func intProductFacts(cs []LinConstraint) []*prop.PropWrapper {
	return intProductFactsWhere(cs, func(productPair) bool { return true })
}

// intProductFactsOf builds the products of the pairs in only.
func intProductFactsOf(cs []LinConstraint, only []productPair) []*prop.PropWrapper {
	return intProductFactsWhere(cs, func(p productPair) bool { return slices.Contains(only, p) })
}

// intProductFactsWhere builds the products of the pairs want admits, the
// base differences read and capped as intProductFacts reads them.
func intProductFactsWhere(cs []LinConstraint, want func(productPair) bool) []*prop.PropWrapper {
	var base []intNonnegFact
	var sources []productSource
	for ci, c := range cs {
		if len(base) >= productFactCap {
			break
		}
		switch c.Op {
		case opLE, opLT:
			w := intCanonAssume(c.Lhs, c.Rhs, c.Op, c.Hyp, c.HypProof) // {…} ⊢ Lhs ⋈ Rhs
			if f, ok := intDiffFact(c.Lhs, c.Rhs, w, c.Op == opLT); ok {
				base = append(base, f)
				sources = append(sources, productSource{constraint: ci})
			}
		case opEQ:
			w := c.HypProof
			if w == nil {
				w = prop.Assume(eqT(c.Lhs, c.Rhs))
			}
			if f, ok := intDiffFact(c.Lhs, c.Rhs, mp(intLessEqOfEq(c.Lhs, c.Rhs), w), false); ok {
				base = append(base, f)
				sources = append(sources, productSource{constraint: ci})
			}
			if f, ok := intDiffFact(c.Rhs, c.Lhs, mp(intLessEqOfEqSwapped(c.Lhs, c.Rhs), w), false); ok {
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
			relT, thm := intLeT, intLessEqMulThm()
			pi, pj := fi.proof, fj.proof
			if strict {
				relT, thm = intLtT, intMulPosThm()
			} else {
				pi, pj = fi.weakened(), fj.weakened()
			}
			imp := intImplyLeaf(thm, []Term{fi.d, fj.d},
				imply(relT(intLit(0), fi.d), imply(relT(intLit(0), fj.d), relT(intLit(0), intStarT(fi.d, fj.d)))))
			facts = append(facts, mp(mp(imp, pi), pj)) // {…} ⊢ &0 ⋈ dᵢ·dⱼ
		}
	}
	return facts
}

// weakened is the fact's non-strict reading `{…} ⊢ &0 ≤ d`: itself when the
// fact is non-strict, else the weakening of `{…} ⊢ &0 < d`, derived once.
func (f *intNonnegFact) weakened() *prop.PropWrapper {
	if !f.strict {
		return f.proof
	}
	if f.weak == nil {
		f.weak = intWeakenLt(intLit(0), f.d, f.proof)
	}
	return f.weak
}

// intWeakenLt turns `Γ ⊢ l < r` into `Γ ⊢ l ≤ r`. The linear prover answers
// `a < b ⊢ a ≤ b` over two variables and the answer is instantiated at l and
// r, so the sides are read by no normalizer: a difference `y − x`, which the
// linear prover does not take as a goal side, weakens as an atom does.
func intWeakenLt(l, r Term, w *prop.PropWrapper) *prop.PropWrapper {
	a, b := ext.Var("a", dsl.IntType), ext.Var("b", dsl.IntType)
	lin, ok := IntLinProve(slices.Values([]Term{intLtT(a, b)}), intLeT(a, b))
	if !ok {
		panic("omega: the integer linear prover declined a < b ⊢ a ≤ b")
	}
	at := lin.TermInst(core.MakeTermSubst(a.AssertVar(), l), core.MakeTermSubst(b.AssertVar(), r)) // {l < r} ⊢ l ≤ r
	return prop.WrapProp(w.MaybeDeriveTrans(at))
}

// intDiffFact turns `{…} ⊢ L ⋈ R` into the nonnegative difference `{…} ⊢ &0
// ⋈ R − L` — through LessEqSubAddLeft / LessThanSubAddLeft at `(&0 ⋈ R − L) ⇔
// (&0 + L ⋈ R)` and the ring identity `&0 + L = L`. A fact that already
// states a sign (`&0 ⋈ R`) is its own difference.
func intDiffFact(L, R Term, w *prop.PropWrapper, strict bool) (intNonnegFact, bool) {
	if isIntZero(L) {
		return intNonnegFact{d: R, proof: w, strict: strict}, true
	}
	zl, ok := IntRingProveFull(intPlusT(intLit(0), L), L) // ⊢ &0 + L = L
	if !ok {
		return intNonnegFact{}, false
	}
	rel, ladd := intLe, intLessEqSubAddLeft
	if strict {
		rel, ladd = intLt, intLessThanSubAddLeft
	}
	cong := zl.LeftApply(rel).RightApply(R) // ⊢ (&0 + L ⋈ R) = (L ⋈ R)
	w2 := cong.EqSym().EqMP(w)              // {…} ⊢ &0 + L ⋈ R
	bridge := ladd(intLit(0), R, L)         // ⊢ (&0 ⋈ R − L) ⇔ (&0 + L ⋈ R)
	return intNonnegFact{d: intSubT(R, L), proof: bridge.EqSym().EqMP(w2), strict: strict}, true
}

// intProductsModel is the untrusted half of the products pass: the
// pairwise product rows as linear constraints over the monomial basis with
// NO proof (`Rᵢ·Lⱼ + Lᵢ·Rⱼ ⋈ Rᵢ·Rⱼ + Lᵢ·Lⱼ` for the differences Rᵢ − Lᵢ and
// Rⱼ − Lⱼ, strict when both are), read for a ℚ-Farkas refutation beside the
// context's rows and the sign rows of the monomials in sight, the proving
// half's own from the context's signs (intMonomialSignRows), as in the real
// twin. A context
// whose products refute nothing costs one model run and never a kernel FOIL
// — on a wide context (thirteen hypotheses, quotients read as products) the
// arith step asks hundreds of questions that decline, and proving
// seventy-eight products for each was the whole cost. Over ℤ the check is
// ℚ-Farkas only, so a refutation that needs the integer cuts AND a product
// is declined here.
//
// used is the product rows the refutation found combines, each named by its
// pair: the products the proving half proves.
func intProductsModel(cs []LinConstraint) (used []productPair, refutable bool) {
	rows, pairs := intProductRows(cs)
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
	model = append(model, intMonomialSignRows(cs, model)...)
	tbl, signed, _, built := intBuildAll(model)
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

// intProductRows builds the product rows of the model, in the order
// intProductFacts proves them: the base differences of the comparison and
// equation constraints (an equation is two), capped as the facts are,
// then every pair i ≤ j through the domain's checked polynomial product,
// each row with the pair it is the product of.
func intProductRows(cs []LinConstraint) ([]LinConstraint, []productPair) {
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
		lf, ok1 := intDomain.linOf(c.Lhs)
		rf, ok2 := intDomain.linOf(c.Rhs)
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
			rl, ok1 := intDomain.polyMul(a.r, b.l)
			lr, ok2 := intDomain.polyMul(a.l, b.r)
			rr, ok3 := intDomain.polyMul(a.r, b.r)
			ll, ok4 := intDomain.polyMul(a.l, b.l)
			if !ok1 || !ok2 || !ok3 || !ok4 {
				continue
			}
			op := opLE
			if a.strict && b.strict {
				op = opLT
			}
			rows = append(rows, LinConstraint{Lhs: intDomain.buildTerm(linAdd(rl, lr)), Rhs: intDomain.buildTerm(linAdd(rr, ll)), Op: op})
			pairs = append(pairs, productPair{a: a.source, b: b.source})
		}
	}
	return rows, pairs
}
