package bridge

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/reify"
	"github.com/euc-ai/xugo/utils"
)

// The lemmas a finite sum is evaluated and supported with, as
// family.Member.
const (
	lemmaMapSum         = "ring_homomorphism.MapSum"
	lemmaSumCongruence  = "module.ModuleSumCongruence"
	lemmaFiniteBelow    = "num_segment.FiniteBelowStrict"
	lemmaSumOnVariables = "polynomial_formula.ParameterPolynomialsSumIn"
)

// sum proves eval(R, σ, Σ_{j<k} p_j) = Σ_{j<k} t_j for a sum node:
// evaluation at a carrier-valued environment is a ring homomorphism
// from the polynomials on 𝕌 (IntegerPolynomialEvalHom), which carries a
// finite sum to the sum of the images (ring_homomorphism.MapSum); each
// image is its summand's value below k (module.ModuleSumCongruence);
// and the summands, polynomials on 𝕌 over a finite index set, sum to
// one (polynomial_formula.ParameterPolynomialsSumIn). The sum's
// addition and zero are spelled as the source spells them.
func (b *_Builder) sum(n *reify.Node, c *_Context) _Scalar {
	_, sargs := ext.MatchesApply(n.Source)
	_, pargs := ext.MatchesApply(n.Term)
	indices := pargs[2]
	family, ok := pargs[3].AsAbsTerm()
	utils.Assert(ok)
	j := family.Var()
	below := assume(b.call("<", j, sumBound(indices)))
	summand := b.scalar(n.Children[0], c.with(below))

	_, envArgs := ext.MatchesApply(c.envOK.Conclusion())
	universe := envArgs[1]
	member := b.algebraMember(family.Body(), universe, summand.support, nil)
	facts := c.with(b.instance(lemmaFiniteBelow, sumBound(indices)), b.overIndices(member, j, indices))

	hom := b.use(lemmaEvalHom, c, b.ring, universe, c.sigma)
	_, homArgs := ext.MatchesApply(hom.Conclusion())
	law := modusPonens(b.instance(lemmaMapSum, homArgs...), hom)
	at := b.normal(instantiate(law, indices, pargs[3]))
	h, _, isImply := ext.MatchesIMPLY(at.Conclusion())
	utils.Assert(isImply)
	value := modusPonens(at, b.prove(h, facts, lemmaMapSum))

	_, image, _ := core.MatchesEQ(value.Conclusion())
	_, iargs := ext.MatchesApply(image)
	images := iargs[3]
	_, t, _ := core.MatchesEQ(summand.eq.Conclusion())
	values := core.Abs(j, t)
	congruence := instantiate(wrap(b.lib.Theorem(lemmaSumCongruence)), iargs[0], iargs[1], indices, images, values)
	congruence = reduceRedexes(congruence.Conclusion(), images).EqMP(congruence)
	congruence = reduceRedexes(congruence.Conclusion(), values).EqMP(congruence)
	termwise := modusPonens(congruence, b.overIndices(summand.eq, j, indices))

	head, _ := ext.MatchesApply(image)
	spelled := prop.Refl(head).
		Apply(b.respelled(sargs[0], iargs[0])).
		Apply(b.respelled(sargs[1], iargs[1])).
		Apply(prop.Refl(indices)).
		Apply(prop.Refl(values))
	eq := value.EqTrans(termwise).EqTrans(spelled.EqSym())

	sumMember := b.use(lemmaSumOnVariables, facts, universe, indices, pargs[3])
	support := theoremPieces(b.instance(lemmaOnVariables, universe, n.Term).EqMP(sumMember))[0]
	return _Scalar{eq: eq, support: support}
}

// sumBound is k for the index set {i | i < k} of a sum the reifier
// wrote.
func sumBound(indices core.Term) core.Term {
	k, ok := belowBound(indices)
	utils.Assert(ok)
	return k
}

// overIndices is ⊢ ∀j. j ∈ B ⇒ φ(j) from j < k ⊢ φ(j), B the index set
// {i | i < k}: membership in B is the bound.
func (b *_Builder) overIndices(t *prop.PropWrapper, j core.VarTerm, indices core.Term) *prop.PropWrapper {
	inB := b.call("set_member", j, indices)
	below := b.memberEq(j, indices).EqMP(assume(inB))
	return wrap(below.MaybeDeriveTrans(t)).PromoteHyp(inB).ConclForAll(j)
}

// respelled is ⊢ s = t for the source's spelling s of a record's part
// and the builder's t: field_ring(F).add is F.add; one spelling is
// reflexivity.
func (b *_Builder) respelled(s, t core.Term) *prop.PropWrapper {
	if s.AlphaEquals(t) {
		return prop.Refl(s)
	}
	eq := b.records(s)
	utils.Assert(eq != nil)
	sameConclusion(eq, core.Eq(s, t), "a record part's respelling")
	return eq
}

// sumSupport proves a finite sum's two facts for the closedness pass:
// each summand's below k, the summands polynomials on {v | v < k} over
// a finite index set, and so their sum.
func (b *_Builder) sumSupport(p, k core.Term, c *_Context) (*prop.PropWrapper, *prop.PropWrapper) {
	_, args := ext.MatchesApply(p)
	indices := args[2]
	family, ok := args[3].AsAbsTerm()
	utils.Assert(ok)
	i := b.fresh("i", ext.NumType)
	body := family.Body().Substitute(core.MakeTermSubst(family.Var(), i))
	below := assume(b.call("<", i, sumBound(indices)))
	integer, vars := b.polynomialSupport(body, k, c.with(below))
	U := b.below(k)
	member := b.algebraMember(body, U, integer, vars)
	facts := c.with(b.instance(lemmaFiniteBelow, sumBound(indices)), b.overIndices(member, i, indices))
	sumMember := b.use(lemmaSumOnVariables, facts, U, indices, args[3])
	pieces := theoremPieces(b.instance(lemmaOnVariables, U, p).EqMP(sumMember))
	return pieces[0], pieces[1]
}
