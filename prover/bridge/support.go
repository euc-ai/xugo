package bridge

import (
	"fmt"
	"math/big"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The lemmas the closedness pass cites, as family.Member.
const (
	lemmaWellFormedDef      = "first_order.WellFormedDef"
	lemmaFreeVarsDef        = "first_order.FreeVarsDef"
	lemmaImpliesDef         = "first_order.ImpliesDef"
	lemmaOrDef              = "first_order.OrDef"
	lemmaIffDef             = "first_order.IffDef"
	lemmaForallDef          = "first_order.ForallDef"
	lemmaAllRangeWellFormed = "first_order.AllRangeWellFormed"
	lemmaExistsRangeWF      = "first_order.ExistsRangeWellFormed"
	lemmaConjoinWellFormed  = "first_order.ConjoinWellFormed"
	lemmaExistsBelow        = "first_order.ExistsSupportBelow"
	lemmaAllRangeBelow      = "first_order.AllRangeSupportBelow"
	lemmaExistsRangeBelow   = "first_order.ExistsRangeSupportBelow"
	lemmaConjoinBelow       = "first_order.ConjoinSupportBelow"
	lemmaBelowMono          = "num_segment.BelowStrictMono"
	lemmaBelowClauses       = "num_segment.BelowStrictClauses"
	lemmaCodeBelow          = "polynomial_encoding.CodeSupportBelow"
	lemmaUnivariateBelow    = "polynomial_encoding.UnivariateCodeBelow"
	lemmaUnionSubset        = "set_order.UnionSubset"
	lemmaSubsetTrans        = "set_order.SubsetTrans"
	lemmaSingSubset         = "set_order.SingSubset"
	lemmaEmptySubset        = "set_order.EmptySubset"
	lemmaSubsetEmpty        = "set_order.SubsetEmpty"
	lemmaFormulaValidDef    = "polynomial_formula.FormulaValidDef"
	lemmaFormulaVarsDef     = "polynomial_formula.FormulaVarsDef"
	lemmaFormulaClosedDef   = "polynomial_formula.FormulaClosedDef"
	lemmaRingTrueSupport    = "ring_formula_combinators.RingTrueFormulaSupport"
	lemmaRingEqualSupport   = "ring_formula_combinators.RingEqualityFormulaSupport"
	lemmaLessEqMul          = "nat_order.LessEqMul2"
)

// closed proves ⊢ polynomial_formula_closed(φ) for the reification's
// formula in sentence mode: it is well formed, and its free names lie
// below the first name past the blocks in scope, which at the root is
// 0, so there are none.
func (b *_Builder) closed() *prop.PropWrapper {
	phi := b.res.Formula
	wf, fv := b.support(phi, b.res.Names.Frontier, &_Context{})
	valid := b.instance(lemmaFormulaValidDef, phi).EqSym().EqMP(wf)
	empty := theoremPieces(b.instance(lemmaBelowClauses))[0]
	inEmpty := rewriteBy(fv, empty)
	_, args := ext.MatchesApply(inEmpty.Conclusion())
	none := b.instance(lemmaSubsetEmpty, args[0]).EqMP(inEmpty)
	vars := rewriteBy(none, b.instance(lemmaFormulaVarsDef, phi).EqSym())
	return b.instance(lemmaFormulaClosedDef, phi).EqSym().EqMP(conjoin(valid, vars))
}

func (b *_Builder) supportSets() (ok, S core.Term) {
	return b.call("integer_polynomial"), b.call("integer_polynomial_vars")
}

// support proves ⊢ fo_wf(integer_polynomial, φ) and
// ⊢ fo_fv(integer_polynomial_vars, φ) ⊆ {v | v < k} for a formula the
// reifier writes, k the first name past the blocks in scope: by its
// constructor's law, the derived connectives through their definitions,
// a quantifier's names past k removed by its block, an atom's names its
// polynomials'.
func (b *_Builder) support(phi, k core.Term, c *_Context) (wf, fv *prop.PropWrapper) {
	ok, S := b.supportSets()
	head, args := ext.MatchesApply(phi)
	name := core.TermName("")
	if h, isConst := head.AsConst(); isConst {
		name = h.Name()
	}
	switch name {
	case "fo_implies", "fo_or", "fo_iff", "fo_forall":
		lemma := map[core.TermName]string{"fo_implies": lemmaImpliesDef, "fo_or": lemmaOrDef, "fo_iff": lemmaIffDef, "fo_forall": lemmaForallDef}[name]
		def := b.instance(lemma, args...)
		_, base, _ := core.MatchesEQ(def.Conclusion())
		wfBase, fvBase := b.support(base, k, c)
		back := def.EqSym()
		return rewriteBy(wfBase, back), rewriteBy(fvBase, back)
	case "fo_not":
		inner, innerFV := b.support(args[0], k, c)
		wfLaw := theoremPieces(wrap(b.lib.Theorem(lemmaWellFormedDef)))[1]
		fvLaw := theoremPieces(wrap(b.lib.Theorem(lemmaFreeVarsDef)))[1]
		w := b.normal(instantiate(wfLaw, ok, args[0])).EqSym().EqMP(inner)
		f := rewriteBy(innerFV, b.normal(instantiate(fvLaw, S, args[0])).EqSym())
		return w, f
	case "fo_and":
		lw, lf := b.support(args[0], k, c)
		rw, rf := b.support(args[1], k, c)
		wfLaw := theoremPieces(wrap(b.lib.Theorem(lemmaWellFormedDef)))[2]
		fvLaw := theoremPieces(wrap(b.lib.Theorem(lemmaFreeVarsDef)))[2]
		w := b.normal(instantiate(wfLaw, ok, args[0], args[1])).EqSym().EqMP(conjoin(lw, rw))
		union := b.unionBelow(lf, rf)
		return w, rewriteBy(union, b.normal(instantiate(fvLaw, S, args[0], args[1])).EqSym())
	case "fo_exists":
		inner := b.call("+", args[0], b.numeral(1))
		iw, ifv := b.support(args[1], inner, c)
		wfLaw := theoremPieces(wrap(b.lib.Theorem(lemmaWellFormedDef)))[3]
		w := b.normal(instantiate(wfLaw, ok, args[0], args[1])).EqSym().EqMP(iw)
		f := modusPonens(b.instance(lemmaExistsBelow, S, args[0], args[1]), ifv)
		return w, b.weaken(f, args[0], k, c)
	case "fo_all_range", "fo_exists_range":
		wfLemma, belowLemma := lemmaAllRangeWellFormed, lemmaAllRangeBelow
		if name == "fo_exists_range" {
			wfLemma, belowLemma = lemmaExistsRangeWF, lemmaExistsRangeBelow
		}
		inner := b.call("+", args[0], args[1])
		iw, ifv := b.support(args[2], inner, c)
		w := b.instance(wfLemma, ok, args[0], args[1], args[2]).EqSym().EqMP(iw)
		f := modusPonens(b.instance(belowLemma, S, args[0], args[1], args[2]), ifv)
		return w, b.weaken(f, args[0], k, c)
	case "fo_conjoin":
		return b.conjoinSupport(args[0], args[1], args[2], k, c)
	case "ring_true_formula", "ordered_ring_true_formula":
		lemma := lemmaRingTrueSupport
		if name == "ordered_ring_true_formula" {
			lemma = lemmaOrderedTrueSupport
		}
		facts := theoremPieces(b.instance(lemma))
		w := b.instance(lemmaFormulaValidDef, phi).EqMP(facts[0])
		none := rewriteBy(facts[1], b.instance(lemmaFormulaVarsDef, phi))
		below := b.instance(lemmaEmptySubset, b.below(k))
		return w, rewriteBy(below, none.EqSym())
	case "ring_equality_formula", "ordered_ring_equality_formula", "polynomial_weak_inequality_formula":
		lemma := map[core.TermName]string{"ring_equality_formula": lemmaRingEqualSupport, "ordered_ring_equality_formula": lemmaOrderedEqualSupport, "polynomial_weak_inequality_formula": lemmaWeakSupport}[name]
		lp, lb := b.polynomialSupport(args[0], k, c)
		rp, rb := b.polynomialSupport(args[1], k, c)
		facts := theoremPieces(b.use(lemma, c.with(lp, rp), args[0], args[1]))
		w := b.instance(lemmaFormulaValidDef, phi).EqMP(facts[0])
		within := rewriteBy(facts[1], b.instance(lemmaFormulaVarsDef, phi))
		return w, b.subsetTrans(within, b.unionBelow(lb, rb))
	}
	if name == "fo_atom" && b.lt != nil {
		return b.strictSupport(phi, k, c)
	}
	panic(fmt.Sprintf("bridge: the closedness pass has no law for %s", ext.PrintTerm(phi)))
}

// strictSupport is a strict comparison's two facts, fo_atom(λm. p(m) − q(m)):
// the atom is the one the weak comparison of q and p negates, whose
// support lemma reads p's and q's names.
func (b *_Builder) strictSupport(phi, k core.Term, c *_Context) (wf, fv *prop.PropWrapper) {
	ok, S := b.supportSets()
	_, args := ext.MatchesApply(phi)
	lam := args[0].(core.AbsTerm)
	_, diff := ext.MatchesApply(lam.Body())
	p, q := polynomialAt(diff[0], lam.Var()), polynomialAt(diff[1], lam.Var())
	lp, lb := b.polynomialSupport(p, k, c)
	rp, rb := b.polynomialSupport(q, k, c)
	weak := b.call("polynomial_weak_inequality_formula", q, p)
	facts := theoremPieces(b.use(lemmaWeakSupport, c.with(rp, lp), q, p))
	def := b.instance(lemmaWeakFormulaDef, q, p)
	wfWeak := rewriteBy(b.instance(lemmaFormulaValidDef, weak).EqMP(facts[0]), def)
	fvWeak := rewriteBy(rewriteBy(facts[1], b.instance(lemmaFormulaVarsDef, weak)), def)
	_, negated, _ := core.MatchesEQ(def.Conclusion())
	_, inner := ext.MatchesApply(negated)
	wfLaw := theoremPieces(wrap(b.lib.Theorem(lemmaWellFormedDef)))[1]
	fvLaw := theoremPieces(wrap(b.lib.Theorem(lemmaFreeVarsDef)))[1]
	w := b.normal(instantiate(wfLaw, ok, inner[0])).EqMP(wfWeak)
	f := rewriteBy(fvWeak, b.normal(instantiate(fvLaw, S, inner[0])))
	sameConclusion(w, b.call("fo_wf", ok, phi), "a strict comparison's well-formedness")
	return w, b.subsetTrans(f, b.unionBelow(rb, lb))
}

// polynomialAt is the polynomial p a strict comparison's difference
// reads at the monomial m: p for p(m), and λm. t for a coefficient t
// the reifier wrote β-reduced, the zero polynomial's.
func polynomialAt(t core.Term, m core.VarTerm) core.Term {
	if app, ok := t.AsAppliedTerm(); ok {
		if arg, isVar := app.Arg().AsVar(); isVar && arg.Equals(m) && !app.Fun().HasFree(m) {
			return app.Fun()
		}
	}
	return core.Abs(m, t)
}

func (b *_Builder) numeral(k int64) core.Term { return ext.MakeNumeral(big.NewInt(k)) }

// below is {v:num | v < k}, read off the lemma that states it.
func (b *_Builder) below(k core.Term) core.Term {
	t := b.instance(lemmaBelowMono, k, k).Conclusion()
	_, sets, _ := ext.MatchesIMPLY(t)
	_, args := ext.MatchesApply(sets)
	return args[0]
}

// unionBelow is ⊢ s ∪ t ⊆ B from ⊢ s ⊆ B and ⊢ t ⊆ B.
func (b *_Builder) unionBelow(left, right *prop.PropWrapper) *prop.PropWrapper {
	_, la := ext.MatchesApply(left.Conclusion())
	_, ra := ext.MatchesApply(right.Conclusion())
	law := b.instance(lemmaUnionSubset, la[0], ra[0], la[1])
	return law.EqSym().EqMP(conjoin(left, right))
}

// singletonBelow is ⊢ {v} ⊆ {x | x < k} from v < k, proved in the
// context: the membership v ∈ {x | x < k} read through the set-builder,
// and the singleton's inclusion is that membership (set_order.SingSubset).
func (b *_Builder) singletonBelow(v, k core.Term, c *_Context) *prop.PropWrapper {
	below := b.below(k)
	read := b.memberEq(v, below)
	in := read.EqSym().EqMP(b.prove(rhsOf(read), c, lemmaSingSubset))
	return b.instance(lemmaSingSubset, below, v).EqSym().EqMP(in)
}

// subsetTrans is ⊢ s ⊆ u from ⊢ s ⊆ t and ⊢ t ⊆ u.
func (b *_Builder) subsetTrans(first, second *prop.PropWrapper) *prop.PropWrapper {
	_, fa := ext.MatchesApply(first.Conclusion())
	_, sa := ext.MatchesApply(second.Conclusion())
	law := b.instance(lemmaSubsetTrans, fa[0], fa[1], sa[1])
	return modusPonens(law, conjoin(first, second))
}

// weaken is ⊢ U ⊆ {v | v < k} from ⊢ U ⊆ {v | v < s}, s ≤ k by
// arithmetic; the fact itself when s is k.
func (b *_Builder) weaken(t *prop.PropWrapper, s, k core.Term, c *_Context) *prop.PropWrapper {
	if s.AlphaEquals(k) {
		return t
	}
	mono := b.use(lemmaBelowMono, c, s, k)
	return b.subsetTrans(t, mono)
}

// conjoinSupport proves a finite conjunction's two facts: its base's
// and, for every index below the bound, its body's at that index.
func (b *_Builder) conjoinSupport(base, n, f, k core.Term, c *_Context) (wf, fv *prop.PropWrapper) {
	ok, S := b.supportSets()
	bw, bf := b.support(base, k, c)
	lam := f.(core.AbsTerm)
	i := b.fresh("i", ext.NumType)
	below := assume(b.call("<", i, n))
	body := lam.Body().Substitute(core.MakeTermSubst(lam.Var(), i))
	iw, ifv := b.support(body, k, c.with(below))
	everyWF := discharge(iw, below.Conclusion()).ConclForAll(i)
	everyFV := discharge(ifv, below.Conclusion()).ConclForAll(i)
	law := b.instance(lemmaConjoinWellFormed, ok, base, n, f)
	w := law.EqSym().EqMP(conjoin(bw, everyWF))
	bound := b.use(lemmaConjoinBelow, c.with(bf, everyFV), S, base, n, k, f)
	return w, bound
}

// polynomialSupport proves ⊢ integer_polynomial(p) and
// ⊢ integer_polynomial_vars(p) ⊆ {v | v < k} for an atom's polynomial:
// a variable below k, a code whose two blocks end by k, a ring
// operation or a finite sum of such polynomials.
func (b *_Builder) polynomialSupport(p, k core.Term, c *_Context) (*prop.PropWrapper, *prop.PropWrapper) {
	if _, isAbs := p.AsAbsTerm(); isAbs {
		valid := theoremPieces(b.instance(lemmaZeroValid))
		spelled := unfoldTheorem(firstArg(valid[0].Conclusion()))
		none := rewriteBy(valid[1], spelled)
		return rewriteBy(valid[0], spelled), rewriteBy(b.instance(lemmaEmptySubset, b.below(k)), none.EqSym())
	}
	head, args := ext.MatchesApply(p)
	h, _ := head.AsConst()
	switch {
	case !h.IsZero() && (h.Name() == "ring_add" || h.Name() == "ring_mul" || h.Name() == "ring_neg"):
		below := b.below(k)
		var members []*prop.PropWrapper
		for _, operand := range args[1:] {
			integer, vars := b.polynomialSupport(operand, k, c)
			members = append(members, b.algebraMember(operand, below, integer, vars))
		}
		facts := theoremPieces(b.closure(h.Name(), args[1:], members, below))
		return facts[0], facts[1]
	case !h.IsZero() && h.Name() == "polynomial_algebra_one":
		facts := theoremPieces(b.instance(lemmaOneSupport))
		return facts[0], rewriteBy(b.instance(lemmaEmptySubset, b.below(k)), facts[1].EqSym())
	case !h.IsZero() && h.Name() == "polynomial_algebra_var":
		facts := theoremPieces(b.instance(lemmaVariableSupport, args[1]))
		return facts[0], b.subsetTrans(facts[1], b.singletonBelow(args[1], k, c))
	case !h.IsZero() && h.Name() == "polynomial_code":
		facts := theoremPieces(b.instance(lemmaCodeSupport, args...))
		return facts[0], b.use(lemmaCodeBelow, c.with(b.blockFacts(args[0], args[1], c)...), args[0], args[1], args[2], args[3], k)
	case !h.IsZero() && h.Name() == "module_sum":
		return b.sumSupport(p, k, c)
	case !h.IsZero() && h.Name() == "univariate_code":
		facts := theoremPieces(b.instance(lemmaUnivariateSupport, args...))
		return facts[0], b.use(lemmaUnivariateBelow, c, args[0], args[1], args[2], k)
	}
	panic(fmt.Sprintf("bridge: the closedness pass has no law for the polynomial %s", ext.PrintTerm(p)))
}

// blockFacts is, for each index j < m in the context, the fact
// suc(j) · cc ≤ m · cc for the coefficient count cc of the code at
// hand, so the arithmetic closer can place a family member's block
// below the family's end.
func (b *_Builder) blockFacts(dimension, degree core.Term, c *_Context) []*prop.PropWrapper {
	var out []*prop.PropWrapper
	if c == nil {
		return nil
	}
	cc := b.call("coefficient_count", dimension, degree)
	for _, f := range c.facts {
		head, args := ext.MatchesApply(f.Conclusion())
		k, ok := head.AsConst()
		if !ok || k.Name() != "<" || len(args) != 2 {
			continue
		}
		succ := b.call("suc", args[0])
		order := b.arith(b.call("<=", succ, args[1]), c)
		refl := b.arith(b.call("<=", cc, cc), nil)
		out = append(out, modusPonens(b.instance(lemmaLessEqMul, succ, args[1], cc, cc), conjoin(order, refl)))
	}
	return out
}
