// independent_exists_prenex.go — the Skolem stage's prenex correction: an
// ∃ block rises above the ∀ block it is independent of before
// Skolemization reads the prefix.
//
// The pre-CNF prelude puts every ∀ it can lift outside every ∃
// (disjunctConclSimplifyRewrite), a canonical prefix for statement
// identity. Read by SkolemRewrite, that prefix makes a witness a
// function of every universal above it, whether or not its part of the
// matrix ever meets them: the negated conclusion of `(∃m n. A(m, n)) ⇒
// ∃m n. B(m, n)` reaches the stage as ∀m.∀n.∃k.∃l.(A(k, l) ∧ ¬B(m, n))
// and its witnesses become ƒ(m, n) and ƒ'(m, n) in place of two
// constants. The spurious arguments let the refuter nest the Skolem
// terms without end, and the sequent `∀x.(M(x) ⇒ M'(x)), ∀x.(N(x) ⇒
// N'(x)) ⊢ ∀x.((∃m n. M(m) ∧ N(n) ∧ x = c(m, n)) ⇒ ∃m n. M'(m) ∧ N'(n)
// ∧ x = c(m, n))` closes in a millisecond with constant witnesses and
// not at all under the budget with function witnesses when c is a
// constant head.
//
// The rule, at ∀ȳ.∃k̄.Φ with both blocks maximal: Φ is an ∧-chain,
// directly or under one more ∀ block, or an ∨-chain with nothing in
// between. Two binders are connected when one component of the chain
// mentions both; K₀ is the ∃-binders connected to no ȳ, directly or
// through other ∃-binders, and Φ_K the components that mention one of
// them — which then mention no ȳ and no other ∃-binder. The rewrite is
//
//	∀ȳ.∃K₀.∃K₁.∀z̄.(Φ_K ∧ Φ_R)  =  ∃K₀.((∀z̄.Φ_K) ∧ ∀ȳ.∃K₁.∀z̄.Φ_R)
//	∀ȳ.∃K₀.∃K₁.(Φ_K ∨ Φ_R)      =  ∃K₀.(Φ_K ∨ ∀ȳ.∃K₁.Φ_R)
//
// each a chain of the prenex theorems read inward and outward, ForAllAND
// over the inner ∀ block, and the reordering of the ∃ block. The
// surrounding Skolem workflow then Skolemizes ∃K₁ under ȳ alone and
// prenexes the ∀ blocks back together; an ∃ at the top of a hypothesis
// is a constant of the clause set (negateGoalCNF). An ∨-chain under a
// further ∀ block is left alone: ∀ does not distribute over ∨, so the
// split is not an equivalence there.

package prop

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// IndependentExistsPrenexRewrite raises, at ∀ȳ.∃k̄.Φ, the ∃-binders
// whose part of the ∧- or ∨-chain Φ mentions no ȳ above the ∀ block
// (the file comment has the rule). Shallow rewrite; it runs in
// SkolemRewriteWorkflow ahead of SkolemRewrite.
var IndependentExistsPrenexRewrite = independentExistsPrenexRewriteImpl()

// _IndependentExistsOp is one chain connective as the rule sees it: its
// constant, matcher, chain tools, and the prenex theorems that move a
// quantifier across it.
type _IndependentExistsOp struct {
	opConst   Term
	matcher   ext.BinaryOpMatcher
	decompose ext.BinaryOpDecomposer
	arrange   ChainArrangement
	assoc     Rewrite
	// associate(p, q, r) proves ⊢ ((p op q) op r) ⇔ (p op (q op r)).
	associate func(Term, Term, Term) *PropWrapper
	// existsLeft(λx.P, Q) proves ⊢ (∃x.P) op Q ⇔ ∃x.(P op Q);
	// existsRight(λx.P, Q) proves ⊢ Q op ∃x.P ⇔ ∃x.(Q op P);
	// forAllRight(λx.P, Q) proves ⊢ Q op ∀x.P ⇔ ∀x.(Q op P).
	existsLeft, existsRight, forAllRight func(Term, Term) *PropWrapper
}

var independentExistsAND = _IndependentExistsOp{
	opConst:     AND,
	matcher:     MatchesAND,
	decompose:   DecomposesAND,
	arrange:     ArrangeANDChain,
	assoc:       AssocANDRewrite,
	associate:   TernaryThms["((p ∧ q) ∧ r) ⇔ (p ∧ (q ∧ r))"],
	existsLeft:  PrenexThms["(∃x.P(x)) ∧ Q ⇔ ∃x.(P(x) ∧ Q)"],
	existsRight: PrenexThms["Q ∧ ∃x.P(x) ⇔ ∃x.(Q ∧ P(x))"],
	forAllRight: PrenexThms["Q ∧ ∀x.P(x) ⇔ ∀x.(Q ∧ P(x))"],
}

var independentExistsOR = _IndependentExistsOp{
	opConst:     OR,
	matcher:     MatchesOR,
	decompose:   DecomposesOR,
	arrange:     ArrangeORChain,
	assoc:       AssocORRewrite,
	associate:   TernaryThms["((p ∨ q) ∨ r) ⇔ (p ∨ (q ∨ r))"],
	existsLeft:  PrenexThms["(∃x.P(x)) ∨ Q ⇔ ∃x.(P(x) ∨ Q)"],
	existsRight: PrenexThms["Q ∨ ∃x.P(x) ⇔ ∃x.(Q ∨ P(x))"],
	forAllRight: PrenexThms["Q ∨ ∀x.P(x) ⇔ ∀x.(Q ∨ P(x))"],
}

func independentExistsPrenexRewriteImpl() Rewrite {
	rewrite := func(t Term) *PropWrapper {
		ys, afterForAll := DecomposesFORALL(t)
		if ys.Empty() {
			return nil
		}
		ks, body := DecomposesEXISTS(afterForAll)
		if ks.Empty() {
			return nil
		}
		zs, matrix := DecomposesFORALL(body)
		var op *_IndependentExistsOp
		if _, _, ok := MatchesAND(matrix); ok {
			op = &independentExistsAND
		} else if _, _, ok := MatchesOR(matrix); ok && zs.Empty() {
			op = &independentExistsOR
		} else {
			return nil
		}
		components := op.decompose(matrix)
		independent, inK := independentExistsPartition(ys, ks, components)
		if independent == nil {
			return nil
		}
		var k0, k1 []VarTerm
		for k := range ks.Iter() {
			if slices.Contains(independent, k) {
				k0 = append(k0, k)
			} else {
				k1 = append(k1, k)
			}
		}
		kOrder := slices.Concat(k0, k1)
		zList := slices.Collect(zs.Iter())
		yList := slices.Collect(ys.Iter())

		// ⊢ ∃k̄.∀z̄.Φ = ∃K₀.∃K₁.∀z̄.Φ
		w := ReorderExists(afterForAll, quantifyAll(EXISTS, kOrder, body))
		// ⊢ Φ = Φ_K op Φ_R
		chain := op.groupChain(matrix, inK)
		phiK, phiR, _ := op.matcher(Rhs(chain))
		w = w.EqTrans(liftUnder(EXISTS, kOrder, liftUnder(FORALL, zList, chain)))
		// ⊢ ∀z̄.(Φ_K ∧ Φ_R) = (∀z̄.Φ_K) ∧ (∀z̄.Φ_R)
		psiK, psiR := phiK, phiR
		if len(zList) > 0 {
			distributed := forAllOverAND(zList, phiK, phiR)
			w = w.EqTrans(liftUnder(EXISTS, kOrder, distributed))
			psiK, psiR, _ = MatchesAND(Rhs(distributed))
		}
		// ⊢ ∃K₀.∃K₁.(Ψ_K op Ψ_R) = ∃K₀.(Ψ_K op ∃K₁.Ψ_R) = (∃K₀.Ψ_K) op ∃K₁.Ψ_R
		existsK1PsiR := quantifyAll(EXISTS, k1, psiR)
		w = w.EqTrans(liftUnder(EXISTS, k0, op.existsInward(k1, psiK, psiR, false)))
		w = w.EqTrans(op.existsInward(k0, psiK, existsK1PsiR, true))
		// ⊢ ∀ȳ.((∃K₀.Ψ_K) op ∃K₁.Ψ_R) = (∃K₀.Ψ_K) op ∀ȳ.∃K₁.Ψ_R
		//   = ∃K₀.(Ψ_K op ∀ȳ.∃K₁.Ψ_R)
		existsK0PsiK := quantifyAll(EXISTS, k0, psiK)
		w = liftUnder(FORALL, yList, w).
			EqTrans(op.forAllInward(yList, existsK0PsiK, existsK1PsiR))
		forAllYs := quantifyAll(FORALL, yList, existsK1PsiR)
		return w.EqTrans(op.existsInward(k0, psiK, forAllYs, true).EqSym())
	}
	return verifyRewrite(rewrite)
}

// independentExistsPartition finds the ∃-binders of ks that no chain
// component connects to a binder of ys, directly or through other
// binders of ks, and marks the components that mention one of them.
// nil when there is nothing to raise, or when raising would leave one
// side of the split empty: a ∀ or ∃ block the chain never mentions is
// QuantifierRewrite's.
func independentExistsPartition(ys, ks VarList, components []Term) ([]VarTerm, []bool) {
	binders := slices.Concat(slices.Collect(ys.Iter()), slices.Collect(ks.Iter()))
	parent := make([]int, len(binders))
	for i := range parent {
		parent[i] = i
	}
	var find func(int) int
	find = func(i int) int {
		for parent[i] != i {
			parent[i] = parent[parent[i]]
			i = parent[i]
		}
		return i
	}
	mentionsY := false
	for _, c := range components {
		first := -1
		for i, v := range binders {
			if !c.HasFree(v) {
				continue
			}
			if i < ys.Size() {
				mentionsY = true
			}
			if first < 0 {
				first = i
			} else {
				parent[find(i)] = find(first)
			}
		}
	}
	if !mentionsY {
		return nil, nil
	}
	touchesY := make([]bool, len(binders))
	for i := range ys.Size() {
		touchesY[find(i)] = true
	}
	var independent []VarTerm
	for i := ys.Size(); i < len(binders); i++ {
		if !touchesY[find(i)] {
			independent = append(independent, binders[i])
		}
	}
	if independent == nil {
		return nil, nil
	}
	inK := make([]bool, len(components))
	count := 0
	for i, c := range components {
		for _, k := range independent {
			if c.HasFree(k) {
				inK[i] = true
				count++
				break
			}
		}
	}
	if count == 0 || count == len(components) {
		return nil, nil
	}
	return independent, inK
}

// groupChain proves ⊢ t = Φ_K op Φ_R for the chain t: the components
// inK marks, in their order, then the rest in theirs.
func (op *_IndependentExistsOp) groupChain(t Term, inK []bool) *PropWrapper {
	components := op.decompose(t)
	rank := func(s Term) int {
		for i, c := range components {
			if c.Equals(s) {
				if inK[i] {
					return i
				}
				return len(components) + i
			}
		}
		panic("groupChain: a component the chain does not hold")
	}
	sorted := binaryOpSortRewriteWithCompare(op.matcher, op.decompose, op.arrange, NilRewrite, op.assoc,
		func(s0, s1 Term) int { return rank(s0) - rank(s1) })(t)
	if sorted == nil {
		sorted = Refl(t)
	}
	size := 0
	for _, in := range inK {
		if in {
			size++
		}
	}
	return sorted.EqTrans(op.splitChainAfter(Rhs(sorted), size))
}

// splitChainAfter proves ⊢ t = X op R for the left-associated chain t:
// X its first size components, R the others, both as chains.
func (op *_IndependentExistsOp) splitChainAfter(t Term, size int) *PropWrapper {
	l, r, ok := op.matcher(t)
	Assert(ok)
	if len(op.decompose(l)) == size {
		return Refl(t)
	}
	left := op.splitChainAfter(l, size)
	x, rest, _ := op.matcher(Rhs(left))
	return left.LeftApply(op.opConst).RightApply(r).
		EqTrans(op.associate(x, rest, r))
}

// existsInward proves ⊢ ∃ks.(left op right) = (∃ks.left) op right when
// onLeft, with no k free in right, and ⊢ ∃ks.(left op right) = left op
// ∃ks.right otherwise, with no k free in left.
func (op *_IndependentExistsOp) existsInward(ks []VarTerm, left, right Term, onLeft bool) *PropWrapper {
	if len(ks) == 0 {
		return Refl(Apply(op.opConst, left, right))
	}
	k, rest := ks[0], ks[1:]
	inner := op.existsInward(rest, left, right, onLeft)
	w := quantifyEq(EXISTS, k, inner)
	l, r, _ := op.matcher(Rhs(inner))
	if onLeft {
		return w.EqTrans(op.existsLeft(core.Abs(k, l), r).EqSym())
	}
	return w.EqTrans(op.existsRight(core.Abs(k, r), l).EqSym())
}

// forAllInward proves ⊢ ∀ys.(left op right) = left op ∀ys.right, with
// no y free in left.
func (op *_IndependentExistsOp) forAllInward(ys []VarTerm, left, right Term) *PropWrapper {
	if len(ys) == 0 {
		return Refl(Apply(op.opConst, left, right))
	}
	y, rest := ys[0], ys[1:]
	inner := op.forAllInward(rest, left, right)
	l, r, _ := op.matcher(Rhs(inner))
	return quantifyEq(FORALL, y, inner).
		EqTrans(op.forAllRight(core.Abs(y, r), l).EqSym())
}

// forAllOverAND proves ⊢ ∀zs.(l ∧ r) = (∀zs.l) ∧ (∀zs.r).
func forAllOverAND(zs []VarTerm, l, r Term) *PropWrapper {
	if len(zs) == 0 {
		return Refl(Apply(AND, l, r))
	}
	z, rest := zs[0], zs[1:]
	inner := forAllOverAND(rest, l, r)
	innerL, innerR, _ := MatchesAND(Rhs(inner))
	return quantifyEq(FORALL, z, inner).
		EqTrans(ForAllAND(core.Abs(z, innerL), core.Abs(z, innerR)))
}

// quantifyEq lifts ⊢ a = b to ⊢ Qv.a = Qv.b.
func quantifyEq(quantifier core.ConstTerm, v VarTerm, w *PropWrapper) *PropWrapper {
	return w.Abs(v).LeftApply(Const(quantifier.Meta(), MakeFun(MakeFun(v.Type(), TypeBool), TypeBool)))
}

// liftUnder lifts ⊢ a = b under the binders vars, outermost first.
func liftUnder(quantifier core.ConstTerm, vars []VarTerm, w *PropWrapper) *PropWrapper {
	for _, v := range slices.Backward(vars) {
		w = quantifyEq(quantifier, v, w)
	}
	return w
}

// quantifyAll is Qvars.body, outermost first; body itself for no vars.
func quantifyAll(quantifier core.ConstTerm, vars []VarTerm, body Term) Term {
	for _, v := range slices.Backward(vars) {
		abs := core.Abs(v, body)
		body = Apply(Const(quantifier.Meta(), MakeFun(abs.Type(), TypeBool)), abs)
	}
	return body
}
