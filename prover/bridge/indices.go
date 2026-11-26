package bridge

import (
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/reify"
	"github.com/euc-ai/xugo/utils"
)

// _Bound is a bound a < m of an index variable a: a hypothesis of the
// reifier's question, or a fact of the context with its proof.
type _Bound struct {
	index core.VarTerm
	bound core.Term
	fact  *prop.PropWrapper
}

// boundOf reads h as a < m for a variable a.
func boundOf(h core.Term) (_Bound, bool) {
	head, args := ext.MatchesApply(h)
	k, ok := head.AsConst()
	if !ok || k.Name() != "<" || len(args) != 2 || !args[0].Type().Equals(ext.NumType) {
		return _Bound{}, false
	}
	a, isVar := args[0].AsVar()
	if !isVar {
		return _Bound{}, false
	}
	return _Bound{index: a, bound: args[1]}, true
}

// _Product is suc(a) · t ≤ m · t: the bound a < m carried to the
// cofactor t of a monomial a · t.
type _Product struct {
	bound    _Bound
	cofactor core.Term
}

// statement is suc(a) · t ≤ m · t, as nat_order.LessEqMul2 concludes it.
func (p _Product) statement(lib Library) core.Term {
	succ := constantCall(lib, "suc", p.bound.index)
	return constantCall(lib, "<=", constantCall(lib, "*", succ, p.cofactor), constantCall(lib, "*", p.bound.bound, p.cofactor))
}

// productLimit bounds the products one goal reads.
const productLimit = 32

// products is, for each monomial a · t of an inequality's two sides with
// a an index some bound keeps below m and t not the empty product, the
// product suc(a) · t ≤ m · t, and in turn those of the monomials of each
// m · t. The arithmetic closer reads a product as its monomials and
// never multiplies a hypothesis by a term, so a bound on a · t reaches it
// as such a product: j · N + c < r · N from j < r and c < N through
// suc(j) · N ≤ r · N. Nil for a goal that is no inequality.
func products(lib Library, goal core.Term, bounds []_Bound) []_Product {
	head, args := ext.MatchesApply(goal)
	k, ok := head.AsConst()
	if !ok || len(args) != 2 || (k.Name() != "<" && k.Name() != "<=") || !args[0].Type().Equals(ext.NumType) || len(bounds) == 0 {
		return nil
	}
	queue := append(monomials(args[0]), monomials(args[1])...)
	var out []_Product
	for len(queue) > 0 && len(out) < productLimit {
		m := queue[0]
		queue = queue[1:]
		if len(m) < 2 {
			continue
		}
		for i, atom := range m {
			a, isVar := atom.AsVar()
			if !isVar {
				continue
			}
			rest := slices.Delete(slices.Clone(m), i, i+1)
			cofactor := productOf(lib, rest)
			for _, bd := range bounds {
				if !bd.index.Equals(a) {
					continue
				}
				p := _Product{bound: bd, cofactor: cofactor}
				if slices.ContainsFunc(out, func(q _Product) bool { return sameProduct(p, q) }) {
					continue
				}
				out = append(out, p)
				for _, n := range monomials(bd.bound) {
					queue = append(queue, append(slices.Clone(n), rest...))
				}
			}
		}
	}
	return out
}

func sameProduct(p, q _Product) bool {
	return p.bound.index.Equals(q.bound.index) && p.bound.bound.AlphaEquals(q.bound.bound) && p.cofactor.AlphaEquals(q.cofactor)
}

// monomialLimit bounds the monomials a term is read as; past it the
// term is one atom.
const monomialLimit = 256

// monomials is t read as a sum of products of atoms, each product its
// atoms with their multiplicity and its coefficient dropped: a nonzero
// numeral is the empty product, + joins, * multiplies out, suc adds the
// empty product, and any other term is an atom.
func monomials(t core.Term) [][]core.Term {
	if v, ok := ext.NumeralValue(t); ok {
		if v.Sign() == 0 {
			return nil
		}
		return [][]core.Term{nil}
	}
	head, args := ext.MatchesApply(t)
	if k, ok := head.AsConst(); ok {
		switch {
		case k.Name() == "+" && len(args) == 2:
			if out := append(monomials(args[0]), monomials(args[1])...); len(out) <= monomialLimit {
				return out
			}
		case k.Name() == "*" && len(args) == 2:
			left, right := monomials(args[0]), monomials(args[1])
			if len(left)*len(right) <= monomialLimit {
				var out [][]core.Term
				for _, l := range left {
					for _, r := range right {
						out = append(out, append(slices.Clone(l), r...))
					}
				}
				return out
			}
		case k.Name() == "suc" && len(args) == 1:
			return append(monomials(args[0]), nil)
		}
	}
	return [][]core.Term{{t}}
}

// productOf is the product of the atoms, left-nested.
func productOf(lib Library, atoms []core.Term) core.Term {
	t := atoms[0]
	for _, a := range atoms[1:] {
		t = constantCall(lib, "*", t, a)
	}
	return t
}

// productFact is ⊢ suc(a) · t ≤ m · t from the bound's fact a < m
// (nat_order.LessEqMul2).
func (b *_Builder) productFact(p _Product) *prop.PropWrapper {
	succ := b.call("suc", p.bound.index)
	order := b.closer(b.call("<=", succ, p.bound.bound), []*prop.PropWrapper{p.bound.fact})
	refl := b.closer(b.call("<=", p.cofactor, p.cofactor), nil)
	return modusPonens(b.instance(lemmaLessEqMul, succ, p.bound.bound, p.cofactor, p.cofactor), conjoin(order, refl))
}

// _Arithmetic is the reifier's arithmetic over the library's closer: a
// computed index is below its bound when the closer proves it from the
// index bounds and the products they give (products), the facts the
// builder proves it from at the node.
type _Arithmetic struct{ lib Library }

// Arithmetic is the reifier's arithmetic over lib's closer, the one the
// executor reads every proposition with.
func Arithmetic(lib Library) reify.Arithmetic { return _Arithmetic{lib} }

func (a _Arithmetic) Below(hypotheses []core.Term, goal core.Term) bool {
	var bounds []_Bound
	for _, h := range hypotheses {
		if bd, ok := boundOf(h); ok {
			bounds = append(bounds, bd)
		}
	}
	terms := slices.Clone(hypotheses)
	for _, p := range products(a.lib, goal, bounds) {
		terms = append(terms, p.statement(a.lib))
	}
	return a.lib.Arith(core.MakeProp(goal, terms...)) != nil
}

// indexConjunction is the finite conjunction an index node reads: its
// formula at a universal index, the formula under the negation at an
// existential one.
func indexConjunction(n *reify.Node) core.Term {
	if n.Kind == reify.ExistsIndex {
		_, args := ext.MatchesApply(n.Term)
		return args[0]
	}
	return n.Term
}

// existsIndex proves an existential index node: ∃j. j < k ∧ A(j) is
// ¬∀j. j < k ⇒ ¬A(j), the child's negation below k is the evaluation of
// its formula's negation, and the finite conjunction of those holds
// exactly when each does.
func (b *_Builder) existsIndex(n *reify.Node, c *_Context) *prop.PropWrapper {
	conj := indexConjunction(n)
	j, bound := conjoinIndex(conj)
	below := assume(b.call("<", j, bound))
	proved := b.node(n.Children[0], c.with(below), n.Source)
	notA := ext.Not(b.meaning(n.Children[0], n.Source)).Core()
	_, args := ext.MatchesApply(conj)
	negated := args[2].(core.AbsTerm).Body()
	each := unary(notA, proved).EqTrans(b.evalClause(1, c.sigma, operands(negated)[0]).EqSym())
	all := ext.ForAll(j)(ext.WrapTerm(below.Conclusion()).Imply(notA).Core()).Core()
	holds := forallUnder(all, j, below.Conclusion(), each).EqTrans(b.conjoinSemantics(conj, c).EqSym())
	negation := unary(ext.Not(all).Core(), holds).EqTrans(b.evalClause(1, c.sigma, conj).EqSym())
	return existsAsNegatedForall(b.canonical(n)).EqTrans(negation)
}

// existsAsNegatedForall is ⊢ (∃j. g ∧ a) = ¬(∀j. g ⇒ ¬a): a witness
// refutes the universal, and where none exists every j with g fails a.
func existsAsNegatedForall(t core.Term) *prop.PropWrapper {
	abs := ext.MatchesEXISTS(t)
	j := abs.Var()
	g, a, ok := ext.MatchesAND(abs.Body())
	utils.Assert(ok)
	all := ext.ForAll(j)(ext.WrapTerm(g).Imply(ext.Not(a).Core()).Core()).Core()

	// g ∧ a, ∀j. g ⇒ ¬a ⊢ ⊥, then ∃j. g ∧ a ⊢ ¬∀j. g ⇒ ¬a.
	body := assume(abs.Body())
	notA := modusPonens(assume(all).ConclForAllInst(j), body.DeriveTrans(prop.HypAND0(g, a)))
	refuted := body.DeriveTrans(prop.HypAND1(g, a)).DeriveTrans(notA.DeriveTrans(prop.Contradict(a)))
	forward := prop.ImpliesFalse(all).EqMP(refuted.HypExists(j, abs.Body()).PromoteHyp(all))

	// ¬∃j. g ∧ a ⊢ ∀j. g ⇒ ¬a, then ¬∀j. g ⇒ ¬a ⊢ ∃j. g ∧ a.
	none := ext.Not(t).Core()
	lam := core.Abs(j, abs.Body())
	allNot := prop.NegExists(lam)
	allNot = reduceRedexes(allNot.Conclusion(), lam).EqMP(allNot).EqMP(assume(none))
	both := conjoin(assume(g), assume(a))
	falsum := both.DeriveTrans(allNot.ConclForAllInst(j).DeriveTrans(prop.Contradict(abs.Body())))
	every := prop.ImpliesFalse(a).EqMP(falsum.PromoteHyp(a)).PromoteHyp(g).ConclForAll(j)
	contradiction := every.DeriveTrans(assume(ext.Not(all).Core()).DeriveTrans(prop.Contradict(all)))
	backward := prop.DoubleNeg(t).EqMP(prop.ImpliesFalse(none).EqMP(contradiction.PromoteHyp(none)))
	return backward.Deduct(forward)
}
