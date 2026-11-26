package reify

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// The corpus lemmas the plan cites, as family.Member.
const (
	lemmaEvalDef                = "first_order.EvalDef"
	lemmaImpliesSemantics       = "first_order.ImpliesSemantics"
	lemmaOrSemantics            = "first_order.OrSemantics"
	lemmaIffSemantics           = "first_order.IffSemantics"
	lemmaConjoinSemantics       = "first_order.ConjoinSemantics"
	lemmaForallBridge           = "first_order.ForallQuantifierBridge"
	lemmaExistsBridge           = "first_order.ExistsQuantifierBridge"
	lemmaAllRangeTupleBridge    = "polynomial_encoding.AllRangeTupleBridge"
	lemmaExistsRangeTupleBridge = "polynomial_encoding.ExistsRangeTupleBridge"
	lemmaAllRangePolynomial     = "polynomial_encoding.AllRangePolynomialBridge"
	lemmaExistsRangePolynomial  = "polynomial_encoding.ExistsRangePolynomialBridge"
	lemmaAllRangeFamily         = "polynomial_encoding.AllRangeFamilyBridge"
	lemmaExistsRangeFamily      = "polynomial_encoding.ExistsRangeFamilyBridge"
	lemmaRingTrueHolds          = "ring_formula_combinators.RingTrueFormulaHolds"
	lemmaOrderedTrueHolds       = "ordered_ring_formula_combinators.OrderedTrueFormulaHolds"
	lemmaRingEqualityEval       = "ring_formula_combinators.RingEqualityFormulaEval"
	lemmaComparisonBridge       = "ordered_ring_formula_combinators.ComparisonBridge"
	lemmaStrictComparison       = "ordered_ring_formula_combinators.StrictComparisonBridge"
	lemmaRingTupleEqual         = "polynomial_encoding.RingTupleEqual"
	lemmaPolynomialMapRingTuple = "polynomial_encoding.PolynomialMapRingTuple"
	lemmaPolynomialBoundDef     = "polynomial_encoding.PolynomialBoundDef"
	lemmaMemberNotEmpty         = "set_basic.MemberNotEmpty"
	lemmaSetMemberDef           = "set_basic.SetMemberDef"
	lemmaSetComprehensionDef    = "set_basic.SetComprehensionDef"
	lemmaComprehensionSpecDef   = "set_basic.ComprehensionSpecDef"
	lemmaEvaluationInCarrier    = "polynomial_formula.EvaluationInCarrier"
	lemmaVariableValue          = "polynomial_formula.VariableValue"
	lemmaVariableFreeEvaluation = "polynomial_formula.VariableFreeEvaluation"
	lemmaEvalHom                = "polynomial_formula.IntegerPolynomialEvalHom"
	lemmaMapAdd                 = "ring_homomorphism.MapAdd"
	lemmaMapMul                 = "ring_homomorphism.MapMul"
	lemmaMapNeg                 = "ring_homomorphism.MapNeg"
	lemmaMapSub                 = "ring_homomorphism.MapSub"
	lemmaTwoStageEvaluation     = "polynomial_encoding.TwoStageEvaluation"
	lemmaUnivariateEvaluation   = "polynomial_encoding.UnivariateCodeEvaluation"
	lemmaPolynomialMapDef       = "polynomial_encoding.PolynomialMapDef"
	lemmaDecodeTupleDef         = "polynomial_encoding.DecodeTupleDef"
	lemmaDecodePolynomialsDef   = "polynomial_encoding.DecodePolynomialsDef"
	lemmaMapSum                 = "ring_homomorphism.MapSum"
	lemmaSumCongruence          = "module.ModuleSumCongruence"
	lemmaFiniteBelow            = "num_segment.FiniteBelowStrict"
	lemmaSumOnVariables         = "polynomial_formula.ParameterPolynomialsSumIn"
)

func cite(lemma string, witnesses ...core.Term) Citation {
	return Citation{Lemma: lemma, Witnesses: witnesses}
}

// _Binding is what a name of the proposition stands for inside a
// scope: a parameter or a guarded binder with its block, or an index
// binder, which has no block and appears in name arithmetic instead.
type _Binding struct {
	term  core.Term
	kind  BlockKind
	block *Block
	index core.VarTerm
	bound core.Term
}

// _Scope is the chain of bindings at a point of the proposition and
// the lengths of every block allocated up to it, parameters first:
// their sum is where the next block starts.
type _Scope struct {
	parent  *_Scope
	binding *_Binding
	lengths []core.Term
}

// lookup is the innermost binding of a term α-equal to t.
func (s *_Scope) lookup(t core.Term) *_Binding {
	for sc := s; sc != nil; sc = sc.parent {
		if sc.binding != nil && sc.binding.term.AlphaEquals(t) {
			return sc.binding
		}
	}
	return nil
}

// boundedIndex tells whether i is an index binder of the scope whose
// bound is the given one, so a coordinate or member read at i stays
// inside its block.
func (s *_Scope) boundedIndex(i, bound core.Term) bool {
	b := s.lookup(i)
	return b != nil && !b.index.IsZero() && b.bound.AlphaEquals(bound)
}

// indexBounds is j < m for each index binder of the scope, the
// innermost first; a binder a nearer one of the same name shadows is
// left out.
func (s *_Scope) indexBounds(b *_Builder) []core.Term {
	var out []core.Term
	var seen []core.VarTerm
	for sc := s; sc != nil; sc = sc.parent {
		bd := sc.binding
		if bd == nil || bd.index.IsZero() || slices.ContainsFunc(seen, bd.index.EqualsVar) {
			continue
		}
		seen = append(seen, bd.index)
		out = append(out, b.natLess(bd.index, bd.bound))
	}
	return out
}

func (s *_Scope) with(b *_Binding, length core.Term) *_Scope {
	lengths := s.lengths
	if length != nil {
		lengths = utils.CloneAppend(s.lengths, length)
	}
	return &_Scope{parent: s, binding: b, lengths: lengths}
}

// _Guard is what a binder's guard says of it: the kind of block it
// takes and the bounds read off the guard, or that it is an index
// below bound.
type _Guard struct {
	kind  BlockKind
	index bool
	n, d  core.Term
	k     core.Term
}

type _Reifier struct {
	in          Input
	b           *_Builder
	ordered     bool
	ring        core.Term
	named       []core.Term
	avoid       []core.Term
	blocks      []*Block
	obligations []Obligation
}

// Reify reads the proposition and writes its formula, names,
// obligations and plan, or refuses it at the first subterm outside the
// grammar. The structure's record must have type field_ops(A) and the
// order, if any, type A → A → bool; a parameter must have the type its
// kind names and carry the bounds that kind reads. Those are the
// caller's contract and fail its assertion.
func Reify(in Input) (*Result, error) {
	utils.Assert(in.Vocabulary != nil && in.Structure.Field != nil && in.Proposition != nil)
	carrier, ok := fieldOpsCarrier(in.Structure.Field.Type())
	utils.Assert(ok)
	utils.Assert(core.IsBool(in.Proposition))
	r := &_Reifier{
		in:      in,
		b:       &_Builder{v: in.Vocabulary, types: newTypes(carrier)},
		ordered: in.Structure.Ordered(),
	}
	if r.ordered {
		utils.Assert(in.Structure.Order.Type().Equals(r.b.types.order))
	}
	r.ring = r.b.fieldRing(in.Structure.Field)
	r.named = []core.Term{in.Structure.Field}
	if r.ordered {
		r.named = append(r.named, in.Structure.Order)
	}
	for _, p := range in.Parameters {
		r.named = append(r.named, p.Term)
	}
	r.avoid = append([]core.Term{in.Proposition}, r.named...)
	r.structureObligations()
	scope := &_Scope{}
	for _, p := range in.Parameters {
		scope = r.declare(scope, p)
	}
	if err := r.checkFree(); err != nil {
		return nil, err
	}
	node, err := r.formula(in.Proposition, scope)
	if err != nil {
		return nil, err
	}
	return &Result{
		Formula:     node.Term,
		Names:       Allocation{Blocks: r.blocks, Frontier: r.b.natSum(scope.lengths)},
		Obligations: r.obligations,
		Plan:        node,
	}, nil
}

func (r *_Reifier) fresh(name string, t core.HolType) core.VarTerm {
	return core.Var(name, t).RenameToAvoid(r.avoid...)
}

func (r *_Reifier) structureObligations() {
	F := r.in.Structure.Field
	r.obligations = append(r.obligations, Obligation{Kind: StructureObligation, Statement: r.b.fieldOn(F)})
	if r.ordered {
		r.obligations = append(r.obligations, Obligation{Kind: StructureObligation, Statement: r.b.orderedFieldOn(F, r.in.Structure.Order)})
	}
}

// declare allocates a parameter's block, states its obligations and
// binds its term in the scope.
func (r *_Reifier) declare(scope *_Scope, p Parameter) *_Scope {
	utils.Assert(p.Term != nil && p.Name != "")
	types := r.b.types
	switch p.Kind {
	case ScalarBlock:
		utils.Assert(p.Term.Type().Equals(types.carrier))
	case PolynomialBlock:
		utils.Assert(p.Term.Type().Equals(types.polynomial) && p.Dimension != nil && p.Degree != nil)
	case FamilyBlock:
		utils.Assert(p.Term.Type().Equals(types.family) && p.Dimension != nil && p.Degree != nil && p.Count != nil)
	case TupleBlock:
		utils.Assert(p.Term.Type().Equals(types.tuple) && p.Dimension != nil)
	}
	block := r.allocate(scope, p.Name, _Guard{kind: p.Kind, n: p.Dimension, d: p.Degree, k: p.Count}, true)
	obligation := func(kind ObligationKind, statement core.Term) {
		r.obligations = append(r.obligations, Obligation{Kind: kind, Owner: p.Name, Statement: statement})
	}
	v, i := r.fresh("v", numType), r.fresh("i", numType)
	switch p.Kind {
	case ScalarBlock:
		obligation(ScalarObligation, r.b.member(p.Term, r.b.fieldCarrier(r.in.Structure.Field)))
	case PolynomialBlock:
		obligation(PolynomialObligation, r.b.member(p.Term, r.b.polynomialAlgebraBelow(r.ring, p.Dimension, v, i)))
		obligation(PolynomialObligation, r.b.polynomialBound(r.ring, p.Dimension, p.Degree, p.Term))
	case FamilyBlock:
		j := r.fresh("j", numType)
		member := apply(p.Term, j)
		below := r.b.natLess(j, p.Count)
		algebra := r.b.member(member, r.b.polynomialAlgebraBelow(r.ring, p.Dimension, v, i))
		bound := r.b.polynomialBound(r.ring, p.Dimension, p.Degree, member)
		obligation(PolynomialObligation, ext.ForAll(j)(ext.WrapTerm(below).Imply(algebra).Core()).Core())
		obligation(PolynomialObligation, ext.ForAll(j)(ext.WrapTerm(below).Imply(bound).Core()).Core())
	case TupleBlock:
		obligation(TupleObligation, r.b.ringTuple(r.ring, p.Dimension, p.Term))
	}
	return scope.with(&_Binding{term: p.Term, kind: p.Kind, block: block}, block.Length)
}

// allocate gives owner the next block of the scope: it starts where
// the lengths allocated so far end.
func (r *_Reifier) allocate(scope *_Scope, owner string, g _Guard, parameter bool) *Block {
	var length core.Term
	switch g.kind {
	case ScalarBlock:
		length = r.b.numeral(1)
	case PolynomialBlock:
		length = r.b.coefficientCount(g.n, g.d)
	case FamilyBlock:
		length = r.b.natMul(g.k, r.b.coefficientCount(g.n, g.d))
	case TupleBlock:
		length = g.n
	}
	block := &Block{
		Owner: owner, Kind: g.kind, Parameter: parameter,
		Start: r.b.natSum(scope.lengths), Length: length,
		Dimension: g.n, Degree: g.d, Count: g.k,
	}
	r.blocks = append(r.blocks, block)
	return block
}

// checkFree refuses a free variable the formula cannot name. A numeric
// variable is a dimension or a degree and stays; a variable of the
// structure or of a parameter's term is named by them; any other is
// a parameter the caller did not declare.
func (r *_Reifier) checkFree() error {
	for _, v := range r.in.Proposition.Frees(nil) {
		if v.Type().Equals(numType) {
			continue
		}
		covered := false
		for _, t := range r.named {
			if t.HasFree(v) {
				covered = true
				break
			}
		}
		if !covered {
			return r.freeRefusal(v)
		}
	}
	return nil
}

func (r *_Reifier) freeRefusal(v core.Term) error {
	if len(r.in.Parameters) == 0 {
		return refuse(FreeParameterInSentence, v, "a free variable in sentence mode; generalize the statement over a degree bound, transfer the property, then instantiate it")
	}
	return refuse(UndeclaredParameter, v, "a free variable no parameter names")
}

func (r *_Reifier) leaf(kind NodeKind, source, term core.Term, citations ...Citation) *Node {
	return &Node{Kind: kind, Source: source, Term: term, Citations: citations}
}

func (r *_Reifier) truthCitation() Citation {
	if r.ordered {
		return cite(lemmaOrderedTrueHolds, r.in.Structure.Field, r.in.Structure.Order)
	}
	return cite(lemmaRingTrueHolds, r.in.Structure.Field)
}

func (r *_Reifier) truthNode(kind NodeKind, source core.Term, citations ...Citation) *Node {
	return r.leaf(kind, source, r.b.truth(r.ordered), append([]Citation{r.truthCitation()}, citations...)...)
}

// formula reads a proposition.
func (r *_Reifier) formula(t core.Term, scope *_Scope) (*Node, error) {
	switch {
	case t.Equals(ext.T):
		return r.truthNode(Truth, t), nil
	case t.Equals(ext.F):
		return r.leaf(Falsity, t, r.b.not(r.b.truth(r.ordered)), r.truthCitation(), cite(lemmaEvalDef)), nil
	}
	if inner := ext.MatchesNOT(t); inner != nil {
		if S, ok := r.setEqualsEmpty(inner); ok {
			return r.nonempty(t, S, scope)
		}
		child, err := r.formula(inner, scope)
		if err != nil {
			return nil, err
		}
		return r.compound(Negation, t, r.b.not(child.Term), []Citation{cite(lemmaEvalDef)}, child), nil
	}
	if l, rr, ok := ext.MatchesAND(t); ok {
		return r.connective(Conjunction, t, l, rr, scope, r.b.and, cite(lemmaEvalDef))
	}
	if l, rr, ok := ext.MatchesOR(t); ok {
		if r.b.v.or.IsZero() {
			return nil, refuse(MissingVocabulary, t, "the vocabulary has no fo_or")
		}
		return r.connective(Disjunction, t, l, rr, scope, r.b.or, cite(lemmaOrSemantics))
	}
	if l, rr, ok := ext.MatchesIMPLY(t); ok {
		return r.connective(Implication, t, l, rr, scope, r.b.implies, cite(lemmaImpliesSemantics))
	}
	if l, rr, ok := ext.MatchesIFF(t); ok {
		if r.b.v.iff.IsZero() {
			return nil, refuse(MissingVocabulary, t, "the vocabulary has no fo_iff")
		}
		return r.connective(Equivalence, t, l, rr, scope, r.b.iff, cite(lemmaIffSemantics))
	}
	if !ext.MatchesFORALL(t).IsZero() {
		return r.quantified(t, scope, true)
	}
	if !ext.MatchesEXISTS(t).IsZero() {
		return r.quantified(t, scope, false)
	}
	if l, rr, ok := core.MatchesEQ(t); ok {
		return r.equality(t, l, rr, scope)
	}
	return r.predicate(t, scope)
}

func (r *_Reifier) compound(kind NodeKind, source, term core.Term, citations []Citation, children ...*Node) *Node {
	return &Node{Kind: kind, Source: source, Term: term, Citations: citations, Children: children}
}

func (r *_Reifier) connective(kind NodeKind, t, l, rr core.Term, scope *_Scope, build func(φ, ψ core.Term) core.Term, citations ...Citation) (*Node, error) {
	left, err := r.formula(l, scope)
	if err != nil {
		return nil, err
	}
	right, err := r.formula(rr, scope)
	if err != nil {
		return nil, err
	}
	return r.compound(kind, t, build(left.Term, right.Term), citations, left, right), nil
}

// predicate reads an atom or a defined predicate: an order atom, a
// membership, a guard predicate at a term the grammar already
// normalizes, or a constant the unfolder expands.
func (r *_Reifier) predicate(t core.Term, scope *_Scope) (*Node, error) {
	head, args := ext.MatchesApply(t)
	if r.ordered && len(args) == 2 && head.AlphaEquals(r.in.Structure.Order) {
		return r.strict(t, args[0], args[1], scope)
	}
	c, isConst := head.AsConst()
	if !isConst {
		return nil, refuse(NotFirstOrder, t, "not an atom of the grammar")
	}
	v := r.b.v
	switch {
	case has(c, v.orderedLe) && len(args) == 3:
		if !r.ordered {
			return nil, refuse(NotFirstOrder, t, "an order atom in the ring theory")
		}
		if !args[0].AlphaEquals(r.in.Structure.Order) {
			return nil, refuse(NotFirstOrder, t, "a comparison at another order than the structure's")
		}
		return r.weak(t, args[1], args[2], scope)
	case has(c, v.member) && len(args) == 2:
		return r.membership(t, args[0], args[1], scope)
	case has(c, v.ringTuple) && len(args) == 3 && args[0].AlphaEquals(r.ring):
		tuple, err := r.tuple(args[2], scope)
		if err != nil {
			return nil, err
		}
		if !tuple.length.AlphaEquals(args[1]) {
			return nil, refuse(DimensionMismatch, t, "ring_tuple at another length than the tuple's")
		}
		return r.truthNode(NormalTuple, t, tuple.normality(r)...), nil
	case has(c, v.polynomialBound) && len(args) == 4 && args[0].AlphaEquals(r.ring):
		p, err := r.polynomial(args[3], scope)
		if err != nil {
			return nil, err
		}
		if !p.n.AlphaEquals(args[1]) || !p.d.AlphaEquals(args[2]) {
			return nil, refuse(DimensionMismatch, t, "polynomial_bound at other bounds than the polynomial's block")
		}
		return r.truthNode(BoundedPolynomial, t, cite(lemmaPolynomialBoundDef)), nil
	}
	if body, lemma, ok := r.unfold(t); ok {
		child, err := r.formula(body, scope)
		if err != nil {
			return nil, err
		}
		return r.compound(Unfolding, t, child.Term, []Citation{cite(lemma)}, child), nil
	}
	return nil, refuse(NoUnfolding, t, fmt.Sprintf("the constant %s is outside the grammar and has no unfolding", c.Name()))
}

// unfold expands a constant the grammar does not read through the
// caller's unfolder; a constant of the vocabulary is never unfolded.
func (r *_Reifier) unfold(t core.Term) (core.Term, string, bool) {
	if r.in.Unfold == nil {
		return nil, "", false
	}
	head, _ := ext.MatchesApply(t)
	if c, isConst := head.AsConst(); !isConst || r.inVocabulary(c) {
		return nil, "", false
	}
	return r.in.Unfold.Unfold(t)
}

func (r *_Reifier) inVocabulary(c core.ConstTerm) bool {
	for _, e := range r.b.v.entries() {
		if has(c, *e.slot) {
			return true
		}
	}
	return false
}

func (r *_Reifier) isEmptySet(t core.Term) bool {
	c, isConst := t.AsConst()
	return isConst && has(c, r.b.v.empty)
}

// setEqualsEmpty reads S = ∅ or ∅ = S and returns S.
func (r *_Reifier) setEqualsEmpty(t core.Term) (core.Term, bool) {
	l, rr, ok := core.MatchesEQ(t)
	switch {
	case !ok:
		return nil, false
	case r.isEmptySet(rr):
		return l, true
	case r.isEmptySet(l):
		return rr, true
	}
	return nil, false
}

// nonempty reads ¬(S = ∅) as ∃x. x ∈ S.
func (r *_Reifier) nonempty(t, S core.Term, scope *_Scope) (*Node, error) {
	setType, ok := S.Type().(core.CompositeType)
	utils.Assert(ok)
	x := r.fresh("x", setType.SubType(0))
	exists := ext.Exists(x)(r.b.member(x, S)).Core()
	child, err := r.formula(exists, scope)
	if err != nil {
		return nil, err
	}
	return r.compound(Nonempty, t, child.Term, []Citation{cite(lemmaMemberNotEmpty, S)}, child), nil
}

// equality reads l = r: of scalars, of tuples, or of a set with ∅.
func (r *_Reifier) equality(t, l, rr core.Term, scope *_Scope) (*Node, error) {
	types := r.b.types
	switch {
	case l.Type().Equals(types.carrier):
		left, lnode, err := r.scalar(l, scope)
		if err != nil {
			return nil, err
		}
		right, rnode, err := r.scalar(rr, scope)
		if err != nil {
			return nil, err
		}
		φ, citation := r.equalityAtom(left, right)
		return r.compound(Equality, t, φ, []Citation{citation}, lnode, rnode), nil
	case l.Type().Equals(types.tuple):
		return r.tupleEquality(t, l, rr, scope)
	}
	if S, ok := r.setEqualsEmpty(t); ok {
		child, err := r.nonempty(ext.Not(t).Core(), S, scope)
		if err != nil {
			return nil, err
		}
		return r.compound(Emptiness, t, r.b.not(child.Term), []Citation{cite(lemmaEvalDef)}, child), nil
	}
	return nil, refuse(NotFirstOrder, t, fmt.Sprintf("an equality at type %s is not first-order over the carrier", ext.FormatType(l.Type())))
}

// equalityAtom is the theory's equality of two integer polynomials
// with the lemma reading it.
func (r *_Reifier) equalityAtom(p, q core.Term) (core.Term, Citation) {
	F := r.in.Structure.Field
	if r.ordered {
		return r.b.comparison(r.b.v.orderedEquality, p, q), cite(lemmaComparisonBridge, F, r.in.Structure.Order, p, q)
	}
	return r.b.comparison(r.b.v.ringEquality, p, q), cite(lemmaRingEqualityEval, F, p, q)
}

func (r *_Reifier) strict(t, l, rr core.Term, scope *_Scope) (*Node, error) {
	left, lnode, err := r.scalar(l, scope)
	if err != nil {
		return nil, err
	}
	right, rnode, err := r.scalar(rr, scope)
	if err != nil {
		return nil, err
	}
	m := r.fresh("m", monomialType)
	φ := r.b.atom(r.b.difference(left, right, m))
	return r.compound(StrictInequality, t, φ, []Citation{cite(lemmaStrictComparison, r.in.Structure.Field, r.in.Structure.Order, left, right)}, lnode, rnode), nil
}

func (r *_Reifier) weak(t, l, rr core.Term, scope *_Scope) (*Node, error) {
	left, lnode, err := r.scalar(l, scope)
	if err != nil {
		return nil, err
	}
	right, rnode, err := r.scalar(rr, scope)
	if err != nil {
		return nil, err
	}
	φ := r.b.comparison(r.b.v.weakInequality, left, right)
	return r.compound(WeakInequality, t, φ, []Citation{cite(lemmaComparisonBridge, r.in.Structure.Field, r.in.Structure.Order, left, right)}, lnode, rnode), nil
}

// tupleEquality reads l = r at tuples coordinatewise: both are normal
// tuples of one length n, and they agree exactly when their first n
// coordinates do.
func (r *_Reifier) tupleEquality(t, l, rr core.Term, scope *_Scope) (*Node, error) {
	left, err := r.tuple(l, scope)
	if err != nil {
		return nil, err
	}
	right, err := r.tuple(rr, scope)
	if err != nil {
		return nil, err
	}
	if !left.length.AlphaEquals(right.length) {
		return nil, refuse(DimensionMismatch, t, "an equality of tuples of two lengths")
	}
	j := r.fresh("j", numType)
	p, lnode := r.coordinate(left, j, core.Apply(l, j))
	q, rnode := r.coordinate(right, j, core.Apply(rr, j))
	atom, citation := r.equalityAtom(p, q)
	φ := r.b.conjoin(r.ordered, left.length, j, atom)
	citations := []Citation{cite(lemmaRingTupleEqual, r.ring, left.length, l, rr), cite(lemmaConjoinSemantics, left.length), r.truthCitation(), citation}
	citations = append(citations, left.normality(r)...)
	citations = append(citations, right.normality(r)...)
	return r.compound(TupleEquality, t, φ, citations, lnode, rnode), nil
}

// membership reads x ∈ S: in the carrier, a scalar term's value lies
// there; in the polynomial algebra below n, a polynomial of the
// grammar does; in a comprehension or a defined set, the body at x.
func (r *_Reifier) membership(t, x, S core.Term, scope *_Scope) (*Node, error) {
	if r.isCarrier(S) {
		if !x.Type().Equals(r.b.types.carrier) {
			return nil, refuse(NotFirstOrder, t, "a membership in the carrier at another type")
		}
		p, node, err := r.scalar(x, scope)
		if err != nil {
			return nil, err
		}
		return r.compound(CarrierMembership, t, r.b.truth(r.ordered), []Citation{r.truthCitation(), cite(lemmaEvaluationInCarrier, r.ring, p)}, node), nil
	}
	if n, ok := r.polynomialAlgebraBelow(S); ok {
		p, err := r.polynomial(x, scope)
		if err != nil {
			return nil, err
		}
		if !p.n.AlphaEquals(n) {
			return nil, refuse(DimensionMismatch, t, "membership in the polynomial algebra below another dimension than the polynomial's")
		}
		return r.truthNode(BoundedPolynomial, t, cite(lemmaPolynomialBoundDef)), nil
	}
	body, citations, err := r.reduceMembership(x, S)
	if err != nil {
		return nil, err
	}
	child, err := r.formula(body, scope)
	if err != nil {
		return nil, err
	}
	return r.compound(Membership, t, child.Term, citations, child), nil
}

// carrier is the structure's carrier, F.carrier.
func (r *_Reifier) carrier() core.Term { return r.b.fieldCarrier(r.in.Structure.Field) }

func (r *_Reifier) isCarrier(S core.Term) bool {
	if args, ok := headIs(S, r.b.v.fieldCarrier); ok && len(args) == 1 && args[0].AlphaEquals(r.in.Structure.Field) {
		return true
	}
	args, ok := headIs(S, r.b.v.ringCarrier)
	return ok && len(args) == 1 && args[0].AlphaEquals(r.ring)
}

// polynomialAlgebraBelow reads polynomial_algebra(field_ring(F), {i | i < n})
// and returns n.
func (r *_Reifier) polynomialAlgebraBelow(S core.Term) (core.Term, bool) {
	args, ok := headIs(S, r.b.v.polynomialAlgebra)
	if !ok || len(args) != 2 || !args[0].AlphaEquals(r.ring) {
		return nil, false
	}
	return r.belowBound(args[1])
}

// belowBound reads the set-builder {i | i < n} and returns n.
func (r *_Reifier) belowBound(S core.Term) (core.Term, bool) {
	P, ok := r.comprehensionPredicate(S)
	if !ok {
		return nil, false
	}
	less, ok := headIs(P.Body(), r.b.v.natLess)
	if !ok || len(less) != 2 || !less[0].Equals(P.Var()) || less[1].HasFree(P.Var()) {
		return nil, false
	}
	return less[1], true
}

// comprehensionPredicate reads a set-builder {y | φ(y)} as the text
// parser lowers it, set_comprehension(λv. ∃y. comprehension_spec(v, φ, y)),
// and returns λy. φ.
func (r *_Reifier) comprehensionPredicate(S core.Term) (core.AbsTerm, bool) {
	args, ok := headIs(S, r.b.v.comprehension)
	if !ok || len(args) != 1 {
		return core.AbsTerm{}, false
	}
	generator, isAbs := args[0].AsAbsTerm()
	if !isAbs {
		return core.AbsTerm{}, false
	}
	existential := ext.MatchesEXISTS(generator.Body())
	if existential.IsZero() {
		return core.AbsTerm{}, false
	}
	spec, ok := headIs(existential.Body(), r.b.v.comprehensionSpec)
	if !ok || len(spec) != 3 || !spec[0].Equals(generator.Var()) || !spec[2].Equals(existential.Var()) || spec[1].HasFree(generator.Var()) {
		return core.AbsTerm{}, false
	}
	return core.Abs(existential.Var(), spec[1]), true
}

// reduceMembership reads x ∈ S down to a proposition without the
// membership: the body of a comprehension at x, or a defined set
// unfolded and read again.
func (r *_Reifier) reduceMembership(x, S core.Term) (core.Term, []Citation, error) {
	if P, ok := r.comprehensionPredicate(S); ok {
		body := P.Body().Substitute(core.MakeTermSubst(P.Var(), x))
		return body, []Citation{cite(lemmaSetMemberDef, x, S), cite(lemmaSetComprehensionDef), cite(lemmaComprehensionSpecDef)}, nil
	}
	if body, lemma, ok := r.unfold(S); ok {
		reduced, citations, err := r.reduceMembership(x, body)
		if err != nil {
			return nil, nil, err
		}
		return reduced, append([]Citation{cite(lemma)}, citations...), nil
	}
	return nil, nil, refuse(NoUnfolding, S, "a membership in a set the grammar does not read and the unfolder does not expand")
}

// quantified reads a quantifier prefix with the guards of its binders
// among the hypotheses (a universal) or the conjuncts (an existential),
// allocates a block per guarded binder from the outside in, reads the
// matrix in the extended scope, and wraps it in the formula's
// quantifiers from the inside out.
func (r *_Reifier) quantified(t core.Term, scope *_Scope, universal bool) (*Node, error) {
	var list ext.VarList
	var body core.Term
	if universal {
		list, body = ext.DecomposesFORALL(t)
	} else {
		list, body = ext.DecomposesEXISTS(t)
	}
	vars := slices.Collect(list.Iter())
	var hypotheses []core.Term
	conclusion := body
	if universal {
		for {
			l, rr, ok := ext.MatchesIMPLY(conclusion)
			if !ok {
				break
			}
			hypotheses = append(hypotheses, ext.DecomposesAND(l)...)
			conclusion = rr
		}
	} else {
		hypotheses = ext.DecomposesAND(body)
	}
	guards, rest, exposures, err := r.findGuards(t, vars, hypotheses)
	if err != nil {
		return nil, err
	}
	bindings := make([]*_Binding, len(vars))
	inner := scope
	for i, v := range vars {
		if guards[i].index {
			bindings[i] = &_Binding{term: v, index: v, bound: guards[i].k}
			inner = inner.with(bindings[i], nil)
			continue
		}
		block := r.allocate(inner, string(v.Name()), guards[i], false)
		block.Variable = v
		bindings[i] = &_Binding{term: v, kind: guards[i].kind, block: block}
		inner = inner.with(bindings[i], block.Length)
	}
	var matrix *Node
	switch {
	case universal && len(rest) > 0:
		hypothesis := ext.And(rest...).Core()
		matrix, err = r.connective(Implication, ext.WrapTerm(hypothesis).Imply(conclusion).Core(), hypothesis, conclusion, inner, r.b.implies, cite(lemmaImpliesSemantics))
	case universal:
		matrix, err = r.formula(conclusion, inner)
	case len(rest) > 0:
		matrix, err = r.formula(ext.And(rest...).Core(), inner)
	default:
		matrix = r.truthNode(Truth, ext.T)
	}
	if err != nil {
		return nil, err
	}
	node := matrix
	for i := len(vars) - 1; i >= 0; i-- {
		node = r.wrap(t, bindings[i], node, universal)
	}
	node.Citations = append(node.Citations, exposures...)
	return node, nil
}

// findGuards finds each binder's guard among the hypotheses. A guard
// hidden in a defined predicate or a set membership is exposed by
// expanding the hypotheses that mention an unguarded binder, as many
// rounds as expose something new; the expansions' lemmas are returned
// for the plan. The hypotheses that guard nothing are returned in
// order, the exposed ones in place of what they came from.
func (r *_Reifier) findGuards(t core.Term, vars []core.VarTerm, hypotheses []core.Term) ([]_Guard, []core.Term, []Citation, error) {
	guards := make([]*_Guard, len(vars))
	var exposures []Citation
	current := hypotheses
	for round := 0; round < 64; round++ {
		var remaining []core.Term
		for _, h := range current {
			if i, g := r.classifyGuard(h, vars); i >= 0 && guards[i] == nil {
				guards[i] = &g
				continue
			}
			remaining = append(remaining, h)
		}
		unguarded := slices.IndexFunc(guards, func(g *_Guard) bool { return g == nil })
		if unguarded < 0 {
			found := make([]_Guard, len(vars))
			for i, g := range guards {
				found[i] = *g
			}
			return found, remaining, exposures, nil
		}
		changed := false
		var expanded []core.Term
		for _, h := range remaining {
			if r.mentionsUnguarded(h, vars, guards) {
				if parts, citations, ok := r.expand(h); ok {
					expanded = append(expanded, parts...)
					exposures = append(exposures, citations...)
					changed = true
					continue
				}
			}
			expanded = append(expanded, h)
		}
		if !changed {
			return nil, nil, nil, r.unguardedRefusal(t, vars[unguarded])
		}
		current = expanded
	}
	return nil, nil, nil, refuse(UnguardedQuantifier, t, "the hypotheses expand without end")
}

func (r *_Reifier) unguardedRefusal(t core.Term, v core.VarTerm) error {
	types := r.b.types
	switch {
	case v.Type().Equals(types.carrier):
		return refuse(UnguardedQuantifier, t, fmt.Sprintf("the scalar %s is bound without a carrier guard", v.Name()))
	case v.Type().Equals(types.tuple):
		return refuse(UnguardedQuantifier, t, fmt.Sprintf("the tuple %s is bound without a ring_tuple guard; a carrier guard on its coordinates alone leaves its tail free", v.Name()))
	case v.Type().Equals(types.polynomial):
		return refuse(UnguardedQuantifier, t, fmt.Sprintf("the polynomial %s is bound without a polynomial_bound guard", v.Name()))
	case v.Type().Equals(types.family):
		return refuse(UnguardedQuantifier, t, fmt.Sprintf("the family %s is bound without a bounded polynomial_bound guard", v.Name()))
	case v.Type().Equals(numType):
		return refuse(UnguardedQuantifier, t, fmt.Sprintf("the index %s is bound without a bound j < k", v.Name()))
	}
	return refuse(NotFirstOrder, t, fmt.Sprintf("a quantifier over %s at type %s, which the carrier does not encode", v.Name(), ext.FormatType(v.Type())))
}

func (r *_Reifier) mentionsUnguarded(h core.Term, vars []core.VarTerm, guards []*_Guard) bool {
	for i, v := range vars {
		if guards[i] == nil && h.HasFree(v) {
			return true
		}
	}
	return false
}

// classifyGuard reads h as the guard of one of the binders: a carrier
// membership, a ring_tuple, a polynomial_bound, a bounded family of
// polynomial_bounds, or an index bound. It returns the binder's
// position, or -1.
func (r *_Reifier) classifyGuard(h core.Term, vars []core.VarTerm) (int, _Guard) {
	v := r.b.v
	position := func(t core.Term) int {
		x, isVar := t.AsVar()
		if !isVar {
			return -1
		}
		return slices.IndexFunc(vars, x.EqualsVar)
	}
	if args, ok := headIs(h, v.member); ok && len(args) == 2 && r.isCarrier(args[1]) {
		if i := position(args[0]); i >= 0 {
			return i, _Guard{kind: ScalarBlock}
		}
	}
	if args, ok := headIs(h, v.ringTuple); ok && len(args) == 3 && args[0].AlphaEquals(r.ring) {
		if i := position(args[2]); i >= 0 && !args[1].HasFree(vars[i]) {
			return i, _Guard{kind: TupleBlock, n: args[1]}
		}
	}
	if args, ok := headIs(h, v.polynomialBound); ok && len(args) == 4 && args[0].AlphaEquals(r.ring) {
		if i := position(args[3]); i >= 0 && !args[1].HasFree(vars[i]) && !args[2].HasFree(vars[i]) {
			return i, _Guard{kind: PolynomialBlock, n: args[1], d: args[2]}
		}
	}
	if args, ok := headIs(h, v.natLess); ok && len(args) == 2 {
		if i := position(args[0]); i >= 0 && !args[1].HasFree(vars[i]) {
			return i, _Guard{index: true, k: args[1]}
		}
	}
	if abs := ext.MatchesFORALL(h); !abs.IsZero() && abs.Var().Type().Equals(numType) {
		j := abs.Var()
		if l, rr, ok := ext.MatchesIMPLY(abs.Body()); ok {
			less, lessOK := headIs(l, v.natLess)
			bound, boundOK := headIs(rr, v.polynomialBound)
			if lessOK && boundOK && len(less) == 2 && len(bound) == 4 && less[0].Equals(j) && !less[1].HasFree(j) && bound[0].AlphaEquals(r.ring) && !bound[1].HasFree(j) && !bound[2].HasFree(j) {
				if member, isApp := bound[3].AsAppliedTerm(); isApp && member.Arg().Equals(j) {
					if i := position(member.Fun()); i >= 0 && !less[1].HasFree(vars[i]) && !bound[1].HasFree(vars[i]) && !bound[2].HasFree(vars[i]) {
						return i, _Guard{kind: FamilyBlock, n: bound[1], d: bound[2], k: less[1]}
					}
				}
			}
		}
	}
	return -1, _Guard{}
}

// expand exposes what a hypothesis hides: a membership in a set the
// grammar reads through, or a defined predicate, replaced by the
// conjuncts of its body.
func (r *_Reifier) expand(h core.Term) ([]core.Term, []Citation, bool) {
	if args, ok := headIs(h, r.b.v.member); ok && len(args) == 2 && !r.isCarrier(args[1]) {
		if _, below := r.polynomialAlgebraBelow(args[1]); below {
			return nil, nil, false
		}
		body, citations, err := r.reduceMembership(args[0], args[1])
		if err != nil {
			return nil, nil, false
		}
		return ext.DecomposesAND(body), citations, true
	}
	if body, lemma, ok := r.unfold(h); ok {
		return ext.DecomposesAND(body), []Citation{cite(lemma)}, true
	}
	return nil, nil, false
}

// wrap puts the binder's quantifier around the formula of its body. A
// universal index is the finite conjunction of the body below its
// bound; an existential one is the negation of the finite conjunction
// of the body's negations, ∃j. j < k ∧ φ read as ¬∀j. j < k ⇒ ¬φ.
func (r *_Reifier) wrap(source core.Term, binding *_Binding, inner *Node, universal bool) *Node {
	b := r.b
	φ := inner.Term
	node := &Node{Source: source, Block: binding.block, Children: []*Node{inner}}
	if !binding.index.IsZero() {
		node.Citations = []Citation{cite(lemmaConjoinSemantics, binding.bound), r.truthCitation()}
		if universal {
			node.Kind = Conjoin
			node.Term = b.conjoin(r.ordered, binding.bound, binding.index, φ)
			return node
		}
		node.Kind = ExistsIndex
		node.Term = b.not(b.conjoin(r.ordered, binding.bound, binding.index, b.not(φ)))
		node.Citations = append(node.Citations, cite(lemmaEvalDef))
		return node
	}
	block := binding.block
	pick := func(forall, exists NodeKind, forallLemma, existsLemma string) (NodeKind, string) {
		if universal {
			return forall, forallLemma
		}
		return exists, existsLemma
	}
	rangeConstant := b.v.existsRange
	if universal {
		rangeConstant = b.v.allRange
	}
	switch block.Kind {
	case ScalarBlock:
		kind, lemma := pick(ForallScalar, ExistsScalar, lemmaForallBridge, lemmaExistsBridge)
		quantifier := b.v.exists
		if universal {
			quantifier = b.v.forall
		}
		node.Kind, node.Term = kind, b.quantifier(quantifier, block.Start, φ)
		node.Citations = []Citation{cite(lemma, r.carrier(), block.Start)}
	case TupleBlock:
		kind, lemma := pick(ForallTuple, ExistsTuple, lemmaAllRangeTupleBridge, lemmaExistsRangeTupleBridge)
		node.Kind, node.Term = kind, b.range_(rangeConstant, block.Start, block.Length, φ)
		node.Citations = []Citation{cite(lemma, r.ring, block.Start, block.Dimension)}
	case PolynomialBlock:
		kind, lemma := pick(ForallPolynomial, ExistsPolynomial, lemmaAllRangePolynomial, lemmaExistsRangePolynomial)
		node.Kind, node.Term = kind, b.range_(rangeConstant, block.Start, block.Length, φ)
		node.Citations = []Citation{cite(lemma, r.ring, block.Start, block.Dimension, block.Degree)}
	case FamilyBlock:
		kind, lemma := pick(ForallFamily, ExistsFamily, lemmaAllRangeFamily, lemmaExistsRangeFamily)
		node.Kind, node.Term = kind, b.range_(rangeConstant, block.Start, block.Length, φ)
		node.Citations = []Citation{cite(lemma, r.ring, block.Start, block.Dimension, block.Degree, block.Count)}
	}
	return node
}
