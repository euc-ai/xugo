package bridge

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/reify"
	"github.com/euc-ai/xugo/utils"
)

// The plan's lemmas the builder dispatches on, as the reifier names
// them.
const (
	lemmaImpliesSemantics    = "first_order.ImpliesSemantics"
	lemmaOrSemantics         = "first_order.OrSemantics"
	lemmaIffSemantics        = "first_order.IffSemantics"
	lemmaEvalDef             = "first_order.EvalDef"
	lemmaEvaluationInCarrier = "polynomial_formula.EvaluationInCarrier"
	lemmaConjoinSemantics    = "first_order.ConjoinSemantics"
	lemmaRingTrueHolds       = "ring_formula_combinators.RingTrueFormulaHolds"
	lemmaRingEqualityEval    = "ring_formula_combinators.RingEqualityFormulaEval"
	lemmaRingTupleEqual      = "polynomial_encoding.RingTupleEqual"
	lemmaMapRingTuple        = "polynomial_encoding.PolynomialMapRingTuple"
	lemmaBoundDef            = "polynomial_encoding.PolynomialBoundDef"
	lemmaVariableValue       = "polynomial_formula.VariableValue"
	lemmaTwoStage            = "polynomial_encoding.TwoStageEvaluation"
	lemmaUnivariateEval      = "polynomial_encoding.UnivariateCodeEvaluation"
	lemmaUnivariateSupport   = "polynomial_encoding.UnivariateCodeSupport"
	lemmaMapDef              = "polynomial_encoding.PolynomialMapDef"
	lemmaDecodeTupleDef      = "polynomial_encoding.DecodeTupleDef"
	lemmaDecodeFamilyDef     = "polynomial_encoding.DecodePolynomialsDef"
	lemmaZeroValid           = "polynomial_formula.ZeroPolynomialValid"
	lemmaOneSupport          = "polynomial_formula.OnePolynomialSupport"
	lemmaOneValue            = "polynomial_formula.OnePolynomialValue"
	lemmaVariableFree        = "polynomial_formula.VariableFreeEvaluation"
	lemmaIntegerMapHom       = "characteristic_zero.IntegerMapHom"
)

// root proves the bridge at the zero environment and restates its
// formula side as the sentence's truth.
func (b *_Builder) root() *prop.PropWrapper {
	v := b.fresh("v", ext.NumType)
	rho := core.Abs(v, b.call("field_zero", b.F))
	c := &_Context{sigma: rho, envOK: b.zeroEnvironment(rho)}
	bridge := b.node(b.res.Plan, c, nil)
	eval := b.evalDef(rho, b.res.Formula)
	truth := b.truthDef(b.res.Formula)
	return bridge.EqTrans(eval.EqSym()).EqTrans(truth.EqSym())
}

// parameterized proves the bridge at a fresh environment ρ, each
// parameter a binder of the root context: its representation in ρ and
// its obligations are hypotheses, as fo_env_ok(F.carrier, 𝕌, ρ) is.
func (b *_Builder) parameterized() (*prop.PropWrapper, core.VarTerm) {
	rho := b.fresh("ρ", ext.MakeFun(ext.NumType, b.call("field_zero", b.F).Type()))
	universe := core.MakeConstTerm(b.lib.Constant("universe"), ext.MakeFun(ext.NumType, core.TypeBool()))
	envOK, _, _ := core.MatchesEQ(b.instance(lemmaEnvOKDef, b.carrier, universe, rho).Conclusion())
	c := &_Context{sigma: rho, envOK: assume(envOK)}
	for _, o := range b.res.Obligations {
		if o.Kind != reify.StructureObligation {
			c.facts = append(c.facts, assume(o.Statement))
		}
	}
	for _, block := range b.res.Names.Blocks {
		if !block.Parameter {
			continue
		}
		value := b.blockValue(block)
		c.binders = append(c.binders, &_Binder{block: block, value: value, rep: assume(b.representation(block, value, rho))})
	}
	bridge := b.node(b.res.Plan, c, nil)
	return bridge.EqTrans(b.evalDef(rho, b.res.Formula).EqSym()), rho
}

// representation is the fact a block's value is represented by in the
// environment ρ: ρ(s) = a for a scalar, decode_tuple(R, n, s, ρ) = x for
// a tuple, decode_polynomial(R, n, d, s, ρ) = p for a polynomial, and
// ∀j. j < k ⇒ decode_polynomials(R, n, d, s, ρ, j) = P(j) for a family.
func (b *_Builder) representation(block *reify.Block, value, rho core.Term) core.Term {
	switch block.Kind {
	case reify.ScalarBlock:
		return core.Eq(core.Apply(rho, block.Start), value)
	case reify.TupleBlock:
		return core.Eq(b.call("decode_tuple", b.ring, block.Dimension, block.Start, rho), value)
	case reify.PolynomialBlock:
		return core.Eq(b.call("decode_polynomial", b.ring, block.Dimension, block.Degree, block.Start, rho), value)
	case reify.FamilyBlock:
		j := core.Var("j", ext.NumType).RenameToAvoid(value, rho, block.Count, block.Dimension, block.Degree, block.Start)
		member := core.Eq(b.call("decode_polynomials", b.ring, block.Dimension, block.Degree, block.Start, rho, j), core.Apply(value, j))
		return ext.ForAll(j)(ext.WrapTerm(b.call("<", j, block.Count)).Imply(member).Core()).Core()
	}
	panic("bridge: a block of no kind")
}

// blockValue is the HOL term a block stands for: its binder's variable,
// or the term of the parameter that owns it.
func (b *_Builder) blockValue(block *reify.Block) core.Term {
	if !block.Variable.IsZero() {
		return block.Variable
	}
	for _, p := range b.in.Parameters {
		if p.Name == block.Owner {
			return p.Term
		}
	}
	panic(fmt.Sprintf("bridge: no binder or parameter owns the block %s", block.Owner))
}

// zeroEnvironment is ⊢ fo_env_ok(F.carrier, 𝕌, ρ) for ρ = λv. F.zero.
func (b *_Builder) zeroEnvironment(rho core.Term) *prop.PropWrapper {
	universe := core.MakeConstTerm(b.lib.Constant("universe"), ext.MakeFun(ext.NumType, core.TypeBool()))
	def := b.instance(lemmaEnvOKDef, b.carrier, universe, rho)
	_, everywhere, _ := core.MatchesEQ(def.Conclusion())
	abs := ext.MatchesFORALL(everywhere)
	inUniverse, _, _ := ext.MatchesIMPLY(abs.Body())
	zero := b.use(lemmaZeroIn, nil, b.ring)
	return def.EqSym().EqMP(zero.PromoteHyp(inUniverse).ConclForAll(abs.Var()))
}

// node proves ⊢ M ⇔ fo_eval(F.carrier, e, σ, φ) for a formula node, M
// its meaning. group is the source the enclosing quantifier prefix
// reads, so a quantifier node knows whether it opens the prefix.
func (b *_Builder) node(n *reify.Node, c *_Context, group core.Term) *prop.PropWrapper {
	var t *prop.PropWrapper
	switch n.Kind {
	case reify.ForallTuple, reify.ExistsTuple, reify.ForallFamily, reify.ExistsFamily,
		reify.ForallPolynomial, reify.ExistsPolynomial, reify.ForallScalar, reify.ExistsScalar:
		t = b.quantifier(n, c)
	case reify.Conjoin:
		t = b.conjoinIndex(n, c)
	case reify.ExistsIndex:
		t = b.existsIndex(n, c)
	case reify.Membership:
		t = b.membership(n, c)
	case reify.Nonempty:
		t = b.nonempty(n, c)
	case reify.Emptiness:
		t = b.emptiness(n, c)
	case reify.Unfolding:
		def := unfoldTheorem(n.Source)
		utils.Assert(def != nil)
		t = def.EqTrans(b.node(n.Children[0], c, nil))
	case reify.Implication:
		t = b.connective(n, c, b.instance(lemmaImpliesSemantics, b.carrier, b.atom, c.sigma, operands(n.Term)[0], operands(n.Term)[1]))
	case reify.Disjunction:
		t = b.connective(n, c, b.instance(lemmaOrSemantics, b.carrier, b.atom, c.sigma, operands(n.Term)[0], operands(n.Term)[1]))
	case reify.Equivalence:
		t = b.connective(n, c, b.instance(lemmaIffSemantics, b.carrier, b.atom, c.sigma, operands(n.Term)[0], operands(n.Term)[1]))
	case reify.Conjunction:
		t = b.connective(n, c, b.evalClause(2, c.sigma, operands(n.Term)[0], operands(n.Term)[1]))
	case reify.Negation:
		inner := b.node(n.Children[0], c, nil)
		t = unary(n.Source, inner).EqTrans(b.evalClause(1, c.sigma, operands(n.Term)[0]).EqSym())
	case reify.Truth:
		t = truthOf(b.truthHolds(c)).EqSym()
	case reify.Falsity:
		holds := b.truthHolds(c)
		negated := b.evalClause(1, c.sigma, holds.Conclusion().(core.AppliedTerm).Arg())
		fails := unary(negated.Conclusion().(core.AppliedTerm).Arg(), truthOf(holds)).EqTrans(wrap(prop.NotTrue))
		t = negated.EqTrans(fails).EqSym()
	case reify.NormalTuple, reify.BoundedPolynomial, reify.CarrierMembership:
		t = b.guardTruth(n, c)
	case reify.TupleEquality:
		t = b.tupleEquality(n, c)
	case reify.Equality, reify.StrictInequality, reify.WeakInequality:
		t = b.equality(n.Source, n.Term, b.scalar(n.Children[0], c), b.scalar(n.Children[1], c), c)
	default:
		panic(fmt.Sprintf("bridge: the builder has no proof for a %s node: %s", n.Kind, ext.PrintTerm(n.Source)))
	}
	expected := b.meaning(n, group)
	if isQuantifier(n.Kind) && !inGroup(n, group) {
		if nest := b.canonical(n); !nest.AlphaEquals(n.Source) {
			t = b.reshape(n.Source, nest).EqTrans(t)
		}
	}
	sameConclusion(t, core.Eq(expected, b.eval(c.sigma, n.Term)), n.Kind.String()+" node")
	return t
}

// inGroup tells whether n continues the prefix whose source is group.
func inGroup(n *reify.Node, group core.Term) bool {
	return group != nil && n.Source.AlphaEquals(group)
}

func isQuantifier(k reify.NodeKind) bool {
	switch k {
	case reify.ForallTuple, reify.ExistsTuple, reify.ForallFamily, reify.ExistsFamily,
		reify.ForallPolynomial, reify.ExistsPolynomial, reify.ForallScalar, reify.ExistsScalar, reify.Conjoin, reify.ExistsIndex:
		return true
	}
	return false
}

// eval is fo_eval(F.carrier, e, σ, φ).
func (b *_Builder) eval(sigma, phi core.Term) core.Term {
	return b.call("fo_eval", b.carrier, b.atom, sigma, phi)
}

// meaning is the HOL side of a node in its parent's reading: the
// source it reads, but at a quantifier inside a prefix the nest the
// plan reads the prefix as (canonical). group is the source of the
// prefix the parent opens, nil outside one.
func (b *_Builder) meaning(n *reify.Node, group core.Term) core.Term {
	if !isQuantifier(n.Kind) || !inGroup(n, group) {
		return n.Source
	}
	return b.canonical(n)
}

// canonical is a quantifier node read as one binder a level, its guard
// the antecedent (∀) or the first conjunct (∃).
func (b *_Builder) canonical(n *reify.Node) core.Term {
	inner := b.meaning(n.Children[0], n.Source)
	switch n.Kind {
	case reify.Conjoin:
		j, bound := conjoinIndex(n.Term)
		return ext.ForAll(j)(ext.WrapTerm(b.call("<", j, bound)).Imply(inner).Core()).Core()
	case reify.ExistsIndex:
		j, bound := conjoinIndex(indexConjunction(n))
		return ext.Exists(j)(ext.And(b.call("<", j, bound), inner).Core()).Core()
	}
	x, guard := n.Block.Variable, b.guard(n.Block)
	switch n.Kind {
	case reify.ExistsTuple, reify.ExistsFamily, reify.ExistsPolynomial, reify.ExistsScalar:
		return ext.Exists(x)(ext.And(guard, inner).Core()).Core()
	}
	return ext.ForAll(x)(ext.WrapTerm(guard).Imply(inner).Core()).Core()
}

// guard is the guard a block's binder carries in the plan's reading.
func (b *_Builder) guard(block *reify.Block) core.Term {
	x := b.blockValue(block)
	switch block.Kind {
	case reify.ScalarBlock:
		return b.call("set_member", x, b.carrier)
	case reify.TupleBlock:
		return b.call("ring_tuple", b.ring, block.Dimension, x)
	case reify.PolynomialBlock:
		return b.call("polynomial_bound", b.ring, block.Dimension, block.Degree, x)
	case reify.FamilyBlock:
		j := core.Var("j", ext.NumType).RenameToAvoid(x, block.Count, block.Dimension, block.Degree)
		bound := b.call("polynomial_bound", b.ring, block.Dimension, block.Degree, core.Apply(x, j))
		return ext.ForAll(j)(ext.WrapTerm(b.call("<", j, block.Count)).Imply(bound).Core()).Core()
	}
	panic("bridge: a block of no kind")
}

func conjoinIndex(t core.Term) (core.VarTerm, core.Term) {
	_, args := ext.MatchesApply(t)
	lam, ok := args[2].AsAbsTerm()
	utils.Assert(ok)
	return lam.Var(), args[1]
}

// quantifier proves a guarded quantifier node by its bridge: the bridge
// at the node's block and the child's meaning as Q, its hypothesis the
// child's equivalence at every environment that agrees with σ below the
// block, holds the binder there and is carrier-valued.
func (b *_Builder) quantifier(n *reify.Node, c *_Context) *prop.PropWrapper {
	child := n.Children[0]
	block := n.Block
	x := block.Variable
	cite := n.Citations[0]
	q := b.fresh("q", ext.MakeFun(x.Type(), core.TypeBool()))
	witnesses := []core.Term{cite.Witnesses[0], b.atom}
	witnesses = append(witnesses, cite.Witnesses[1:]...)
	witnesses = append(witnesses, c.sigma, child.Term, q)
	inst := b.instance(cite.Lemma, witnesses...)
	lam := core.Abs(x, b.meaning(child, n.Source))
	inst = inst.TermInst(core.MakeTermSubst(q, lam))
	inst = reduceRedexes(inst.Conclusion(), lam).EqMP(inst)

	hypothesis, _, ok := ext.MatchesIMPLY(inst.Conclusion())
	utils.Assert(ok)
	var stated core.Term
	for _, piece := range conjunctionPieces(hypothesis) {
		if !ext.MatchesFORALL(piece.Conclusion()).IsZero() {
			stated = piece.Conclusion()
		}
	}
	utils.Assert(stated != nil)
	tau := b.fresh("τ", c.sigma.Type())
	outer := ext.MatchesFORALL(stated)
	body := outer.Body().Substitute(core.MakeTermSubst(outer.Var(), tau))
	innerAbs := ext.MatchesFORALL(body)
	body = innerAbs.Body().Substitute(core.MakeTermSubst(innerAbs.Var(), x))
	given, equivalence, ok := ext.MatchesIMPLY(body)
	utils.Assert(ok)

	pieces := conjunctionPieces(given)
	utils.Assert(len(pieces) == 4)
	envOK, agreement, guard, rep := pieces[0], pieces[1], pieces[2], pieces[3]
	agree := &_Agreement{fact: agreement, tau: tau, sig: c.sigma, start: block.Start}
	next := &_Context{sigma: tau, envOK: envOK, agree: []*_Agreement{agree}}
	next.facts = append(append(next.facts, c.facts...), guard)
	for _, bd := range c.binders {
		next.binders = append(next.binders, &_Binder{block: bd.block, value: bd.value, rep: b.transport(bd, next)})
	}
	next.binders = append(next.binders, &_Binder{block: block, value: x, rep: rep})

	proved := b.node(child, next, n.Source)
	sameConclusion(proved, equivalence, "the child of a "+n.Kind.String()+" node")
	general := proved.PromoteHyp(given).ConclForAllList(tau, x)
	return modusPonens(inst, b.prove(hypothesis, c.with(general), cite.Lemma))
}

// transport carries an outer binder's representation fact from the
// enclosing environment to the child's, which agrees with it below the
// child's block.
func (b *_Builder) transport(bd *_Binder, next *_Context) *prop.PropWrapper {
	block := bd.block
	agree := next.agree[0]
	switch block.Kind {
	case reify.TupleBlock:
		eq := b.use(lemmaDecodeTupleCong, next, b.ring, block.Dimension, block.Start, agree.tau, agree.sig)
		return eq.EqTrans(bd.rep)
	case reify.PolynomialBlock:
		eq := b.use(lemmaDecodeCongruence, next, b.ring, block.Dimension, block.Degree, block.Start, agree.tau, agree.sig)
		return eq.EqTrans(bd.rep)
	case reify.FamilyBlock:
		j := b.fresh("j", ext.NumType)
		below := assume(b.call("<", j, block.Count))
		eq := b.use(lemmaDecodeFamilyCong, next.with(below), b.ring, block.Dimension, block.Degree, block.Start, block.Count, agree.tau, agree.sig, j)
		old := modusPonens(bd.rep.ConclForAllInst(j), below)
		return discharge(eq.EqTrans(old), below.Conclusion()).ConclForAll(j)
	case reify.ScalarBlock:
		at := agree.fact.ConclForAllInst(block.Start)
		return modusPonens(at, b.arith(b.call("<", block.Start, agree.start), next)).EqTrans(bd.rep)
	}
	panic("bridge: a block of no kind")
}

// conjoinIndex proves a bounded index node: the finite conjunction holds
// exactly when its body does below the bound.
func (b *_Builder) conjoinIndex(n *reify.Node, c *_Context) *prop.PropWrapper {
	j, bound := conjoinIndex(n.Term)
	below := assume(b.call("<", j, bound))
	proved := b.node(n.Children[0], c.with(below), n.Source)
	holds := forallUnder(b.canonical(n), j, below.Conclusion(), proved)
	return holds.EqTrans(b.conjoinSemantics(n.Term, c).EqSym())
}

// conjoinSemantics is ⊢ fo_eval(σ, fo_conjoin(⊤, k, f)) ⇔ ∀i. i < k ⇒ fo_eval(σ, f(i)),
// f(i) β-reduced.
func (b *_Builder) conjoinSemantics(conj core.Term, c *_Context) *prop.PropWrapper {
	_, args := ext.MatchesApply(conj)
	return b.use(lemmaConjoinSemantics, c.with(b.truthHolds(c)), b.carrier, b.atom, c.sigma, args[0], args[1], args[2])
}

// truthHolds is ⊢ fo_eval(σ, ring_true_formula).
func (b *_Builder) truthHolds(c *_Context) *prop.PropWrapper {
	var holds *prop.PropWrapper
	if b.lt != nil {
		holds = b.use(lemmaOrderedTrueHolds, nil, b.structureArgs(c.sigma)...)
	} else {
		holds = b.instance(lemmaRingTrueHolds, b.structureArgs(c.sigma)...)
	}
	_, args := ext.MatchesApply(holds.Conclusion())
	return b.evalDef(c.sigma, args[len(args)-1]).EqMP(holds)
}

// connective proves a binary connective by its semantics, the
// formula's evaluation as the connective of its operands', and the
// congruence of the two children's equivalences.
func (b *_Builder) connective(n *reify.Node, c *_Context, semantics *prop.PropWrapper) *prop.PropWrapper {
	left := b.node(n.Children[0], c, nil)
	right := b.node(n.Children[1], c, nil)
	return binary(n.Source, left, right).EqTrans(semantics.EqSym())
}

// operands is the formula arguments of a connective's formula.
func operands(t core.Term) []core.Term {
	_, args := ext.MatchesApply(t)
	return args
}

// evalClause is clause k of first_order.EvalDef at the theory's carrier
// and atom, the environment and the formula's operands: k = 1 reads a
// negation, k = 2 a conjunction.
func (b *_Builder) evalClause(k int, sigma core.Term, phis ...core.Term) *prop.PropWrapper {
	def := wrap(b.lib.Theorem(lemmaEvalDef))
	clause := theoremPieces(def)[k]
	return b.normal(instantiate(clause, append([]core.Term{b.carrier, b.atom, sigma}, phis...)...))
}

// theoremPieces is each conjunct of a theorem's conclusion, flattened,
// as a theorem.
func theoremPieces(t *prop.PropWrapper) []*prop.PropWrapper {
	var out []*prop.PropWrapper
	var walk func(p *prop.PropWrapper)
	walk = func(p *prop.PropWrapper) {
		if l, r, ok := ext.MatchesAND(p.Conclusion()); ok {
			walk(p.DeriveTrans(prop.HypAND0(l, r)))
			walk(p.DeriveTrans(prop.HypAND1(l, r)))
			return
		}
		out = append(out, p)
	}
	walk(t)
	return out
}

// guardTruth proves a node whose formula is the true formula and whose
// proposition holds in the context: a normal tuple, a bounded
// polynomial, a scalar in the carrier. Both sides hold, so they agree.
func (b *_Builder) guardTruth(n *reify.Node, c *_Context) *prop.PropWrapper {
	var holds *prop.PropWrapper
	switch n.Kind {
	case reify.NormalTuple:
		_, args := ext.MatchesApply(n.Source)
		holds = b.normality(args[2], c)
	case reify.BoundedPolynomial:
		holds = b.boundedPolynomial(n.Source, c)
	case reify.CarrierMembership:
		value := b.scalar(n.Children[0], c)
		evaluation, _, _ := core.MatchesEQ(value.eq.Conclusion())
		_, eargs := ext.MatchesApply(evaluation)
		inCarrier := b.use(lemmaEvaluationInCarrier, c.with(value.support), b.ring, c.sigma, eargs[2])
		holds = rewriteBy(inCarrier, value.eq)
	default:
		panic(fmt.Sprintf("bridge: the %s node holds of no guard: %s", n.Kind, ext.PrintTerm(n.Source)))
	}
	sameConclusion(holds, n.Source, n.Kind.String()+" node")
	return holds.Deduct(b.truthHolds(c))
}

// boundedPolynomial is ⊢ polynomial_bound(R, n, d, p) or ⊢ p ∈
// polynomial_algebra(R, {i | i < n}) for a polynomial of the plan: a
// binder by its guard, a family member by the family's guard at its
// index, the membership read off the bound.
func (b *_Builder) boundedPolynomial(h core.Term, c *_Context) *prop.PropWrapper {
	head, args := ext.MatchesApply(h)
	k, _ := head.AsConst()
	member := k.Name() == "set_member"
	polynomial := args[len(args)-1]
	if member {
		polynomial = args[0]
	}
	var bound *prop.PropWrapper
	if app, ok := polynomial.AsAppliedTerm(); ok && ext.IsFunType(app.Fun().Type()) && !b.isBinder(c, polynomial) {
		family := b.binderOf(c, app.Fun())
		guard := c.find(b.guard(family.block))
		bound = modusPonens(guard.ConclForAllInst(app.Arg()), b.prove(b.call("<", app.Arg(), family.block.Count), c, "a family member's bound"))
	} else {
		bd := b.binderOf(c, polynomial)
		bound = c.find(b.guard(bd.block))
	}
	if !member {
		return bound
	}
	_, bargs := ext.MatchesApply(bound.Conclusion())
	def := b.instance(lemmaBoundDef, bargs[0], bargs[1], bargs[2], bargs[3])
	return def.EqMP(bound).DeriveTrans(prop.HypAND0(conjuncts(def)))
}

func (b *_Builder) isBinder(c *_Context, t core.Term) bool {
	for _, bd := range c.binders {
		if bd.value.AlphaEquals(t) {
			return true
		}
	}
	return false
}

// tupleEquality proves l = r for two normal tuples of length k: they are
// equal exactly when their coordinates below k are, each coordinate's
// equality is its atom, and the finite conjunction of the atoms holds
// exactly when each does.
func (b *_Builder) tupleEquality(n *reify.Node, c *_Context) *prop.PropWrapper {
	j, length := conjoinIndex(n.Term)
	_, args := ext.MatchesApply(n.Term)
	atom := args[2].(core.AbsTerm).Body()
	l, r, _ := core.MatchesEQ(n.Source)
	below := assume(b.call("<", j, length))
	cj := c.with(below)
	coordinates := core.Eq(core.Apply(l, j), core.Apply(r, j))
	at := b.equality(coordinates, atom, b.scalar(n.Children[0], cj), b.scalar(n.Children[1], cj), cj)
	pointwise := ext.ForAll(j)(ext.WrapTerm(below.Conclusion()).Imply(coordinates).Core()).Core()
	under := forallUnder(pointwise, j, below.Conclusion(), at)
	normal := c.with(b.normality(l, c), b.normality(r, c))
	equal := b.use(lemmaRingTupleEqual, normal, b.ring, length, l, r)
	return equal.EqTrans(under).EqTrans(b.conjoinSemantics(n.Term, c).EqSym())
}

// normality is ⊢ ring_tuple(R, k, t) for a tuple term of the plan: a
// binder by its guard, a polynomial map by the map's lemma.
func (b *_Builder) normality(t core.Term, c *_Context) *prop.PropWrapper {
	for _, bd := range c.binders {
		if bd.value.AlphaEquals(t) {
			return c.find(b.guard(bd.block))
		}
	}
	head, args := ext.MatchesApply(t)
	if k, ok := head.AsConst(); ok && k.Name() == "polynomial_map" && len(args) == 4 {
		family := b.binderOf(c, args[2])
		algebra := b.familyAlgebra(family, c)
		return b.use(lemmaMapRingTuple, c.with(algebra), args[0], args[1], args[2], args[3])
	}
	panic(fmt.Sprintf("bridge: no normality for the tuple %s", ext.PrintTerm(t)))
}

func (b *_Builder) binderOf(c *_Context, t core.Term) *_Binder {
	for _, bd := range c.binders {
		if bd.value.AlphaEquals(t) {
			return bd
		}
	}
	panic(fmt.Sprintf("bridge: no binder in scope stands for %s", ext.PrintTerm(t)))
}

// familyAlgebra is ⊢ ∀j. j < k ⇒ P(j) ∈ polynomial_algebra(R, {i | i < n})
// from the family's guard, each bound polynomial lying in the algebra.
func (b *_Builder) familyAlgebra(family *_Binder, c *_Context) *prop.PropWrapper {
	block := family.block
	guard := c.find(b.guard(block))
	utils.Assert(guard != nil)
	j := b.fresh("j", ext.NumType)
	below := assume(b.call("<", j, block.Count))
	bound := modusPonens(guard.ConclForAllInst(j), below)
	def := b.instance(lemmaBoundDef, b.ring, block.Dimension, block.Degree, core.Apply(family.value, j))
	member := def.EqMP(bound).DeriveTrans(prop.HypAND0(conjuncts(def)))
	return discharge(member, below.Conclusion()).ConclForAll(j)
}

func conjuncts(def *prop.PropWrapper) (core.Term, core.Term) {
	_, rhs, _ := core.MatchesEQ(def.Conclusion())
	l, r, ok := ext.MatchesAND(rhs)
	utils.Assert(ok)
	return l, r
}

// _Scalar is a scalar node's two facts: ⊢ eval(R, σ, p) = t and
// ⊢ integer_polynomial(p).
type _Scalar struct {
	eq      *prop.PropWrapper
	support *prop.PropWrapper
}

// equality proves an atom's equivalence from the two scalar equations:
// (l = r), ordered_le(lt, l, r) or lt(l, r) ⇔ fo_eval(σ, atom), the atom
// the theory's equality, weak or strict comparison of p and q.
func (b *_Builder) equality(source, atom core.Term, left, right _Scalar, c *_Context) *prop.PropWrapper {
	p, q := scalarPolynomial(left), scalarPolynomial(right)
	facts := c.with(left.support, right.support)
	var evaluated *prop.PropWrapper
	head, _ := ext.MatchesApply(atom)
	k, _ := head.AsConst()
	switch {
	case b.lt == nil:
		evaluated = b.use(lemmaRingEqualityEval, facts, b.F, c.sigma, p, q)
	case k.Name() == "fo_atom":
		evaluated = b.use(lemmaStrictComparison, facts, b.structureArgs(c.sigma, p, q)...)
	case k.Name() == "polynomial_weak_inequality_formula":
		evaluated = theoremPieces(b.use(lemmaComparisonBridge, facts, b.structureArgs(c.sigma, p, q)...))[0]
	default:
		evaluated = theoremPieces(b.use(lemmaComparisonBridge, facts, b.structureArgs(c.sigma, p, q)...))[1]
	}
	read := b.evalDef(c.sigma, atom)
	_, sides, _ := core.MatchesEQ(evaluated.Conclusion())
	pointwise := binary(sides, left.eq, right.eq)
	sameConclusion(pointwise, core.Eq(sides, source), "the atom's values")
	return read.EqSym().EqTrans(evaluated).EqTrans(pointwise).EqSym()
}

// scalarPolynomial is the integer polynomial a scalar's equation
// evaluates.
func scalarPolynomial(s _Scalar) core.Term {
	evaluation, _, _ := core.MatchesEQ(s.eq.Conclusion())
	_, args := ext.MatchesApply(evaluation)
	return args[2]
}

// scalar proves a scalar node's equation and support.
func (b *_Builder) scalar(n *reify.Node, c *_Context) _Scalar {
	s := b.scalarValue(n, c)
	if _, value, _ := core.MatchesEQ(s.eq.Conclusion()); b.records != nil && !value.AlphaEquals(n.Source) {
		if respelled := b.records(n.Source); respelled != nil {
			s.eq = s.eq.EqTrans(respelled.EqSym())
		}
	}
	return s
}

// scalarValue is a scalar node's facts, its value in the builder's
// normal form; scalar respells it as the plan's source writes it, a
// field's ring's part where the source names that.
func (b *_Builder) scalarValue(n *reify.Node, c *_Context) _Scalar {
	switch n.Kind {
	case reify.Coordinate:
		return b.coordinate(n, c)
	case reify.MapCoordinate:
		return b.mapCoordinate(n, c)
	case reify.ScalarVariable:
		return b.scalarVariable(n, c)
	case reify.Zero:
		return b.zeroScalar(n, c)
	case reify.Operation:
		return b.operation(n, c)
	case reify.One:
		return b.oneScalar(n, c)
	case reify.PolynomialValue:
		return b.polynomialValue(n, c)
	case reify.UnivariateValue:
		return b.univariateValue(n, c)
	case reify.Sum:
		return b.sum(n, c)
	}
	panic(fmt.Sprintf("bridge: the builder has no proof for a %s scalar: %s", n.Kind, ext.PrintTerm(n.Source)))
}

// coordinate proves eval(R, σ, var(s + j)) = x(j) for a tuple binder x
// at s: the variable evaluates to σ there, which the tuple decoded from
// the block reads below the tuple's length.
func (b *_Builder) coordinate(n *reify.Node, c *_Context) _Scalar {
	app, ok := n.Source.AsAppliedTerm()
	utils.Assert(ok)
	bd := b.binderOf(c, app.Fun())
	j := app.Arg()
	_, vargs := ext.MatchesApply(n.Term)
	name := vargs[1]
	value := b.use(lemmaVariableValue, c, b.ring, c.sigma, name)
	def := b.instance(lemmaDecodeTupleDef, b.ring, bd.block.Dimension, bd.block.Start, c.sigma, j)
	_, cond, _ := core.MatchesEQ(def.Conclusion())
	reduced := b.condBelow(cond, c)
	_, read, _ := core.MatchesEQ(reduced.Conclusion())
	same := unary(read, b.natEqual(name, readArg(read), c))
	eq := value.EqTrans(same).EqTrans(reduced.EqSym()).EqTrans(def.EqSym()).EqTrans(bd.rep.RightApply(j))
	support := b.instance(lemmaVariableSupport, name).DeriveTrans(prop.HypAND0(splitAnd(b.instance(lemmaVariableSupport, name).Conclusion())))
	return _Scalar{eq: eq, support: support}
}

func readArg(t core.Term) core.Term {
	app, ok := t.AsAppliedTerm()
	utils.Assert(ok)
	return app.Arg()
}

func splitAnd(t core.Term) (core.Term, core.Term) {
	l, r, ok := ext.MatchesAND(t)
	utils.Assert(ok)
	return l, r
}

// mapCoordinate proves eval(R, σ, polynomial_code(n, d, c, s_x)) =
// polynomial_map(R, n, P, x)(j): the code evaluates to the polynomial
// decoded from its block at the tuple decoded from x's, which are P(j)
// and x, and the map's coordinate below n is that value.
func (b *_Builder) mapCoordinate(n *reify.Node, c *_Context) _Scalar {
	app, ok := n.Source.AsAppliedTerm()
	utils.Assert(ok)
	j := app.Arg()
	_, margs := ext.MatchesApply(app.Fun())
	family, tuple := b.binderOf(c, margs[2]), b.binderOf(c, margs[3])
	_, cargs := ext.MatchesApply(n.Term)
	dimension, degree, start, at := cargs[0], cargs[1], cargs[2], cargs[3]
	stages := b.use(lemmaTwoStage, c, b.ring, dimension, degree, start, at, c.sigma)
	slot := b.decodedPolynomial(dimension, degree, start, core.Apply(family.value, j), c)
	_, value, _ := core.MatchesEQ(stages.Conclusion())
	reading := replace(value, slot, tuple.rep)
	def := b.instance(lemmaMapDef, margs[0], margs[1], margs[2], margs[3], j)
	_, cond, _ := core.MatchesEQ(def.Conclusion())
	reduced := b.condBelow(cond, c)
	eq := stages.EqTrans(reading).EqTrans(reduced.EqSym()).EqTrans(def.EqSym())
	codes := b.instance(lemmaCodeSupport, dimension, degree, start, at)
	support := codes.DeriveTrans(prop.HypAND0(splitAnd(codes.Conclusion())))
	return _Scalar{eq: eq, support: support}
}

// slotOf is the block start c of decode_polynomial(R, n, d, c, ρ).
func slotOf(t core.Term) core.Term {
	_, args := ext.MatchesApply(t)
	return args[3]
}

// condBelow is ⊢ COND(j < k, a, b) = a, j < k from the context.
func (b *_Builder) condBelow(cond core.Term, c *_Context) *prop.PropWrapper {
	_, args := ext.MatchesApply(cond)
	test, yes, no := args[0], args[1], args[2]
	decided := replace(cond, truthOf(b.prove(test, c, "a case split")))
	return decided.EqTrans(prop.CondClauseT(yes, no))
}

// natEqual is ⊢ a = b for two spellings of one number, by arithmetic
// when they differ.
func (b *_Builder) natEqual(a, bb core.Term, c *_Context) *prop.PropWrapper {
	if a.AlphaEquals(bb) {
		return prop.Refl(a)
	}
	return b.arith(core.Eq(a, bb), c)
}

// reshape is ⊢ S = K for a quantifier prefix S and the nest K the plan
// reads it as: the same binders and the same hypotheses, grouped and
// ordered otherwise, proved in both directions by instantiating one at
// the other's binders under its hypotheses.
func (b *_Builder) reshape(source, nest core.Term) *prop.PropWrapper {
	if exposed := b.expose(source, nest); exposed != nil {
		_, opened, _ := core.MatchesEQ(exposed.Conclusion())
		return exposed.EqTrans(b.reshape(opened, nest))
	}
	if !ext.MatchesEXISTS(source).IsZero() {
		forward := eliminate(construct(nest, leafFacts(source)), source)
		backward := eliminate(construct(source, leafFacts(nest)), nest)
		return backward.Deduct(forward)
	}
	forward := entail(source, nest)
	backward := entail(nest, source)
	return backward.Deduct(forward)
}

// leafFacts assumes each leaf of an existential prefix: its conjuncts
// below its binders, the binders free.
func leafFacts(t core.Term) []*prop.PropWrapper {
	if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
		return leafFacts(abs.Body())
	}
	if l, r, ok := ext.MatchesAND(t); ok {
		return append(leafFacts(l), leafFacts(r)...)
	}
	if t.Equals(ext.T) {
		return nil
	}
	return []*prop.PropWrapper{assume(t)}
}

// construct proves an existential prefix from its leaves, each binder
// its own witness.
func construct(t core.Term, facts []*prop.PropWrapper) *prop.PropWrapper {
	if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
		return construct(abs.Body(), facts).ConclExistsInst(abs.Var())
	}
	if l, r, ok := ext.MatchesAND(t); ok {
		return conjoin(construct(l, facts), construct(r, facts))
	}
	if t.Equals(ext.T) {
		return wrap(prop.DerivesTrue)
	}
	return fromFacts(t, facts)
}

// eliminate replaces the leaves of an existential prefix among t's
// hypotheses by the prefix itself.
func eliminate(t *prop.PropWrapper, prefix core.Term) *prop.PropWrapper {
	if abs := ext.MatchesEXISTS(prefix); !abs.IsZero() {
		return eliminate(t, abs.Body()).HypExists(abs.Var(), abs.Body())
	}
	if l, r, ok := ext.MatchesAND(prefix); ok {
		t = eliminate(eliminate(t, l), r)
		if t.HasHyp(l) {
			t = prop.HypAND0(l, r).DeriveTrans(t)
		}
		if t.HasHyp(r) {
			t = prop.HypAND1(l, r).DeriveTrans(t)
		}
		return t
	}
	return t
}

// entail is from ⊢ to: to's binders fixed and its hypotheses assumed, from
// instantiated at the same binders and its hypotheses proved from to's.
func entail(from, to core.Term) *prop.PropWrapper {
	var levels []_Level
	var facts []*prop.PropWrapper
	goal := to
	for {
		if abs := ext.MatchesFORALL(goal); !abs.IsZero() {
			levels = append(levels, _Level{v: abs.Var()})
			goal = abs.Body()
			continue
		}
		if h, rest, ok := ext.MatchesIMPLY(goal); ok {
			levels = append(levels, _Level{h: h})
			facts = append(facts, conjunctionPieces(h)...)
			goal = rest
			continue
		}
		break
	}
	t := assume(from)
	for {
		if abs := ext.MatchesFORALL(t.Conclusion()); !abs.IsZero() {
			t = t.ConclForAllInst(binderNamed(levels, abs.Var()))
			continue
		}
		if h, _, ok := ext.MatchesIMPLY(t.Conclusion()); ok && !t.Conclusion().AlphaEquals(goal) {
			t = modusPonens(t, fromFacts(h, facts))
			continue
		}
		break
	}
	sameConclusion(t, goal, "a reshaped prefix")
	for i := len(levels) - 1; i >= 0; i-- {
		if !levels[i].v.IsZero() {
			t = t.ConclForAll(levels[i].v)
		} else {
			t = t.PromoteHyp(levels[i].h)
		}
	}
	return t
}

// _Level is one level of a prefix: a binder or a hypothesis.
type _Level struct {
	v core.VarTerm
	h core.Term
}

func binderNamed(levels []_Level, v core.VarTerm) core.Term {
	for _, l := range levels {
		if !l.v.IsZero() && l.v.Name() == v.Name() && l.v.Type().Equals(v.Type()) {
			return l.v
		}
	}
	panic(fmt.Sprintf("bridge: a reshaped prefix binds %s, which the other does not", v.Name()))
}

func fromFacts(h core.Term, facts []*prop.PropWrapper) *prop.PropWrapper {
	for _, f := range facts {
		if f.Conclusion().AlphaEquals(h) {
			return f
		}
	}
	if l, r, ok := ext.MatchesAND(h); ok {
		return conjoin(fromFacts(l, facts), fromFacts(r, facts))
	}
	panic(fmt.Sprintf("bridge: a reshaped prefix assumes %s, which the other does not", ext.PrintTerm(h)))
}

// scalarVariable proves eval(R, σ, var(v)) = a for a scalar binder a at
// v: the variable evaluates to σ(v), which is a.
func (b *_Builder) scalarVariable(n *reify.Node, c *_Context) _Scalar {
	bd := b.binderOf(c, n.Source)
	_, vargs := ext.MatchesApply(n.Term)
	name := vargs[1]
	value := b.use(lemmaVariableValue, c, b.ring, c.sigma, name)
	support := b.instance(lemmaVariableSupport, name)
	return _Scalar{eq: value.EqTrans(bd.rep), support: support.DeriveTrans(prop.HypAND0(splitAnd(support.Conclusion())))}
}

// polynomialValue proves eval(R, σ, polynomial_code(n, d, c, s_x)) =
// polynomial_value(R, p, x): the code evaluates to the polynomial
// decoded from its block at the tuple decoded from x's, which are p and
// x.
func (b *_Builder) polynomialValue(n *reify.Node, c *_Context) _Scalar {
	_, sargs := ext.MatchesApply(n.Source)
	polynomial, tuple := sargs[1], b.binderOf(c, sargs[2])
	_, cargs := ext.MatchesApply(n.Term)
	dimension, degree, start, at := cargs[0], cargs[1], cargs[2], cargs[3]
	stages := b.use(lemmaTwoStage, c, b.ring, dimension, degree, start, at, c.sigma)
	slot := b.decodedPolynomial(dimension, degree, start, polynomial, c)
	_, value, _ := core.MatchesEQ(stages.Conclusion())
	eq := stages.EqTrans(replace(value, slot, tuple.rep))
	codes := b.instance(lemmaCodeSupport, dimension, degree, start, at)
	return _Scalar{eq: eq, support: codes.DeriveTrans(prop.HypAND0(splitAnd(codes.Conclusion())))}
}

// univariateValue proves eval(R, σ, univariate_code(n, s, t)) =
// polynomial_eval(p, a) for a tuple p of length n at s, read as a
// polynomial in one variable, and a scalar a at t: the code evaluates
// to the tuple decoded from its block at σ(t), which are p and a.
func (b *_Builder) univariateValue(n *reify.Node, c *_Context) _Scalar {
	_, sargs := ext.MatchesApply(n.Source)
	tuple, point := b.binderOf(c, sargs[4]), b.binderOf(c, sargs[5])
	_, cargs := ext.MatchesApply(n.Term)
	length, start, at := cargs[0], cargs[1], cargs[2]
	value := b.use(lemmaUnivariateEval, c, b.ring, length, start, at, c.sigma)
	_, evaluated, _ := core.MatchesEQ(value.Conclusion())
	eq := value.EqTrans(replace(evaluated, tuple.rep, point.rep))
	codes := b.instance(lemmaUnivariateSupport, length, start, at)
	return _Scalar{eq: eq, support: codes.DeriveTrans(prop.HypAND0(splitAnd(codes.Conclusion())))}
}

// decodedPolynomial is ⊢ decode_polynomial(R, n, d, c, σ) = p for a
// polynomial of the plan decoded from the block at c: a polynomial
// binder by its representation fact, a family member P(j) by the
// family's at j, its block at c by arithmetic.
func (b *_Builder) decodedPolynomial(dimension, degree, start, polynomial core.Term, c *_Context) *prop.PropWrapper {
	decoded := b.call("decode_polynomial", b.ring, dimension, degree, start, c.sigma)
	if b.isBinder(c, polynomial) {
		return oriented(b.binderOf(c, polynomial).rep, decoded)
	}
	app, ok := polynomial.AsAppliedTerm()
	utils.Assert(ok)
	family := b.binderOf(c, app.Fun())
	j := app.Arg()
	member := modusPonens(family.rep.ConclForAllInst(j), b.prove(b.call("<", j, family.block.Count), c, "a family member"))
	members := b.instance(lemmaDecodeFamilyDef, b.ring, dimension, degree, family.block.Start, c.sigma, j)
	_, decodedAt, _ := core.MatchesEQ(members.Conclusion())
	return replace(decoded, b.natEqual(start, slotOf(decodedAt), c)).EqTrans(members.EqSym()).EqTrans(member)
}

// zeroScalar proves eval(R, σ, λm. 0) = F.zero: a polynomial with no
// variables evaluates to the integer map at its constant coefficient,
// and the integer map sends 0 to zero.
func (b *_Builder) zeroScalar(n *reify.Node, c *_Context) _Scalar {
	valid := theoremPieces(b.instance(lemmaZeroValid))
	spelled := unfoldTheorem(firstArg(valid[0].Conclusion()))
	support := rewriteBy(valid[0], spelled)
	none := rewriteBy(valid[1], spelled)
	value := b.use(lemmaVariableFree, c.with(none), b.ring, c.sigma, n.Term)
	zero := theoremPieces(b.use(lemmaIntegerMapHom, nil, b.ring))[1]
	return _Scalar{eq: value.EqTrans(zero), support: support}
}

// oneScalar proves eval(R, σ, polynomial_algebra_one(int_ring)) = F.one.
func (b *_Builder) oneScalar(n *reify.Node, c *_Context) _Scalar {
	support := theoremPieces(b.instance(lemmaOneSupport))[0]
	value := b.use(lemmaOneValue, nil, b.ring, c.sigma)
	return _Scalar{eq: value, support: support}
}

// firstArg is a for an application f(a).
func firstArg(t core.Term) core.Term {
	_, args := ext.MatchesApply(t)
	return args[0]
}

// expose is ⊢ S = S' where S' is the prefix S with each hypothesis
// (∀) or conjunct (∃) the nest K does not hold opened to its body: a
// membership read through its set, a defined predicate unfolded — the
// guards the reifier found inside them; nil when S's leaves are K's.
func (b *_Builder) expose(source, nest core.Term) *prop.PropWrapper {
	want := prefixLeaves(nest)
	var eqs []*prop.PropWrapper
	for _, leaf := range prefixLeaves(source) {
		if containsAlpha(want, leaf) {
			continue
		}
		if eq := b.openLeaf(leaf); eq != nil {
			eqs = append(eqs, eq)
		}
	}
	if len(eqs) == 0 {
		return nil
	}
	return replace(source, eqs...)
}

// openLeaf is ⊢ h = body for a membership the reifier reads through or a
// defined predicate it unfolds.
func (b *_Builder) openLeaf(h core.Term) *prop.PropWrapper {
	head, args := ext.MatchesApply(h)
	if k, ok := head.AsConst(); ok && k.Name() == "set_member" && len(args) == 2 {
		return b.memberEq(args[0], args[1])
	}
	return unfoldTheorem(h)
}

// prefixLeaves is the hypotheses of a universal prefix, or the
// conjuncts of an existential one, flattened, its binders free.
func prefixLeaves(t core.Term) []core.Term {
	if abs := ext.MatchesFORALL(t); !abs.IsZero() {
		_, body := ext.DecomposesFORALL(t)
		var out []core.Term
		for {
			h, rest, ok := ext.MatchesIMPLY(body)
			if !ok {
				return out
			}
			out = append(out, ext.DecomposesAND(h)...)
			if !ext.MatchesFORALL(rest).IsZero() {
				out = append(out, prefixLeaves(rest)...)
				return out
			}
			body = rest
		}
	}
	if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
		_, body := ext.DecomposesEXISTS(t)
		var out []core.Term
		for _, piece := range ext.DecomposesAND(body) {
			if !ext.MatchesEXISTS(piece).IsZero() {
				out = append(out, prefixLeaves(piece)...)
				continue
			}
			out = append(out, piece)
		}
		return out
	}
	return nil
}

func containsAlpha(ts []core.Term, t core.Term) bool {
	for _, u := range ts {
		if u.AlphaEquals(t) {
			return true
		}
	}
	return false
}

// The lemmas a ring operation is evaluated and supported with.
const (
	lemmaEvalHom       = "polynomial_formula.IntegerPolynomialEvalHom"
	lemmaOnVariables   = "polynomial_formula.PolynomialOnVariables"
	lemmaParameterRing = "polynomial_formula.ParameterPolynomialsSubring"
	lemmaSubringDef    = "comm_ring.SubringDef"
	lemmaMapAdd        = "ring_homomorphism.MapAdd"
	lemmaMapMul        = "ring_homomorphism.MapMul"
	lemmaMapNeg        = "ring_homomorphism.MapNeg"
)

// operation proves eval(R, σ, op(p₁, …)) = op_F(t₁, …) for a ring
// operation of the integer polynomials: evaluation at a carrier-valued
// environment is a ring homomorphism, so it carries the operation to the
// field's, at the operands' values.
func (b *_Builder) operation(n *reify.Node, c *_Context) _Scalar {
	head, args := ext.MatchesApply(n.Term)
	k, _ := head.AsConst()
	operands := args[1:]
	var children []_Scalar
	for _, child := range n.Children {
		children = append(children, b.scalar(child, c))
	}
	_, envArgs := ext.MatchesApply(c.envOK.Conclusion())
	universe := envArgs[1]
	hom := b.use(lemmaEvalHom, c, b.ring, universe, c.sigma)
	_, homArgs := ext.MatchesApply(hom.Conclusion())
	lemma := map[core.TermName]string{"ring_add": lemmaMapAdd, "ring_mul": lemmaMapMul, "ring_neg": lemmaMapNeg}[k.Name()]
	if lemma == "" {
		panic(fmt.Sprintf("bridge: the builder has no evaluation law for %s", k.Name()))
	}
	law := modusPonens(b.instance(lemma, homArgs...), hom)
	facts := c
	var members []*prop.PropWrapper
	for i, child := range children {
		members = append(members, b.algebraMember(operands[i], universe, child.support, nil))
	}
	at := b.normal(law.ConclForAllInsts(operands...))
	for _, m := range members {
		facts = facts.with(m)
	}
	h, _, ok := ext.MatchesIMPLY(at.Conclusion())
	utils.Assert(ok)
	value := modusPonens(at, b.prove(h, facts, lemma))
	var eqs []*prop.PropWrapper
	for _, child := range children {
		eqs = append(eqs, child.eq)
	}
	_, image, _ := core.MatchesEQ(value.Conclusion())
	eq := value.EqTrans(replace(image, eqs...))
	support := b.closure(k.Name(), operands, members, universe)
	return _Scalar{eq: eq, support: theoremPieces(support)[0]}
}

// algebraMember is ⊢ p ∈ polynomial_algebra(int_ring, U) from
// ⊢ integer_polynomial(p) and, for U ≠ 𝕌, ⊢ integer_polynomial_vars(p) ⊆ U.
func (b *_Builder) algebraMember(p, U core.Term, integer, vars *prop.PropWrapper) *prop.PropWrapper {
	if vars == nil {
		vars = b.instance(lemmaSubsetUniv, b.call("integer_polynomial_vars", p))
	}
	return b.instance(lemmaOnVariables, U, p).EqSym().EqMP(conjoin(integer, vars))
}

// closure is ⊢ integer_polynomial(op(p₁, …)) ∧ integer_polynomial_vars(op(p₁, …)) ⊆ U
// from the operands' memberships in polynomial_algebra(int_ring, U):
// those polynomials are a subring of the integer polynomials.
func (b *_Builder) closure(op core.TermName, operands []core.Term, members []*prop.PropWrapper, U core.Term) *prop.PropWrapper {
	_, setArgs := ext.MatchesApply(members[0].Conclusion())
	algebra := setArgs[1]
	subring := b.instance(lemmaParameterRing, U)
	_, ringArgs := ext.MatchesApply(subring.Conclusion())
	clauses := theoremPieces(b.instance(lemmaSubringDef, ringArgs[0], algebra).EqMP(subring))
	index := map[core.TermName]int{"ring_add": 3, "ring_neg": 4, "ring_mul": 5}[op]
	clause := clauses[index].ConclForAllInsts(operands...)
	member := modusPonens(clause, conjoinAll(members))
	result := rhsOfMember(member)
	return b.instance(lemmaOnVariables, U, result).EqMP(member)
}

func conjoinAll(facts []*prop.PropWrapper) *prop.PropWrapper {
	t := facts[0]
	for _, f := range facts[1:] {
		t = conjoin(t, f)
	}
	return t
}

func rhsOfMember(t *prop.PropWrapper) core.Term {
	_, args := ext.MatchesApply(t.Conclusion())
	return args[0]
}
