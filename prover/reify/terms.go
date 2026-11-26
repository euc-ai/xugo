package reify

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// _Tuple is a tuple term of the grammar: a block tuple, a guarded
// variable or a tuple parameter, whose coordinates are the block's
// names; or the polynomial map of a family at a block tuple, whose
// coordinates are the family's codes at the tuple's block. Both are
// normal: carrier values below the length, zero from it on.
type _Tuple struct {
	block    *Block
	family   *_Binding
	argument *_Tuple
	length   core.Term
	source   core.Term
}

// normality is the lemma by which the tuple is normal: a polynomial
// map's image by its own lemma; a block tuple by its guard or
// obligation, which cites nothing.
func (t *_Tuple) normality(r *_Reifier) []Citation {
	if t.family == nil {
		return nil
	}
	return []Citation{cite(lemmaPolynomialMapRingTuple, r.ring, t.length, t.family.term, t.argument.source)}
}

// _Polynomial is a polynomial term of the grammar: the coefficient
// block it is decoded from and its bounds.
type _Polynomial struct {
	start core.Term
	n, d  core.Term
}

// tuple reads a tuple term.
func (r *_Reifier) tuple(t core.Term, scope *_Scope) (*_Tuple, error) {
	if b := scope.lookup(t); b != nil && b.kind == TupleBlock {
		return &_Tuple{block: b.block, length: b.block.Dimension, source: t}, nil
	}
	if args, ok := headIs(t, r.b.v.polynomialMap); ok && len(args) == 4 {
		if !args[0].AlphaEquals(r.ring) {
			return nil, refuse(NotFirstOrder, t, "a polynomial map over another ring than the structure's")
		}
		family := scope.lookup(args[2])
		if family == nil || family.kind != FamilyBlock {
			return nil, refuse(NotFirstOrder, args[2], "the polynomial map's family is neither bound by a bounded polynomial_bound guard nor a family parameter")
		}
		argument, err := r.tuple(args[3], scope)
		if err != nil {
			return nil, err
		}
		if argument.block == nil {
			return nil, refuse(NotFirstOrder, t, "a polynomial map at a polynomial map composes polynomials, outside the grammar")
		}
		n := args[1]
		if !family.block.Count.AlphaEquals(n) || !family.block.Dimension.AlphaEquals(n) || !argument.length.AlphaEquals(n) {
			return nil, refuse(DimensionMismatch, t, "the polynomial map's length, its family's count and dimension and its argument's length must agree")
		}
		return &_Tuple{family: family, argument: argument, length: n, source: t}, nil
	}
	if _, isVar := t.AsVar(); isVar {
		return nil, r.freeRefusal(t)
	}
	return nil, refuse(NotFirstOrder, t, "a tuple term outside the grammar")
}

// polynomial reads a polynomial term: a guarded polynomial variable or
// polynomial parameter, or a member of a family at an index.
func (r *_Reifier) polynomial(t core.Term, scope *_Scope) (*_Polynomial, error) {
	if b := scope.lookup(t); b != nil && b.kind == PolynomialBlock {
		return &_Polynomial{start: b.block.Start, n: b.block.Dimension, d: b.block.Degree}, nil
	}
	if app, isApp := t.AsAppliedTerm(); isApp {
		if family := scope.lookup(app.Fun()); family != nil && family.kind == FamilyBlock {
			if !r.indexBelow(scope, app.Arg(), family.block.Count) {
				return nil, refuse(IndexOutsideBlock, t, "a member of a family at an index the arithmetic does not keep below the family's count")
			}
			return &_Polynomial{start: r.codeStart(family.block, app.Arg()), n: family.block.Dimension, d: family.block.Degree}, nil
		}
	}
	if _, isVar := t.AsVar(); isVar {
		return nil, r.freeRefusal(t)
	}
	return nil, refuse(NotFirstOrder, t, "a polynomial term outside the grammar: neither a guarded polynomial, a polynomial parameter nor a member of a family")
}

// codeStart is the coefficient block of member i of a family: i blocks
// of coefficient_count(n, d) names past the family's start.
func (r *_Reifier) codeStart(family *Block, i core.Term) core.Term {
	return r.b.natAdd(family.Start, r.b.natMul(i, r.b.coefficientCount(family.Dimension, family.Degree)))
}

// coordinate is coordinate i of a tuple as an integer polynomial: the
// variable at name start + i of a block tuple, or the code of member
// i of a polynomial map's family at its argument's block.
func (r *_Reifier) coordinate(t *_Tuple, i core.Term, source core.Term) (core.Term, *Node) {
	if t.block != nil {
		name := r.b.natAdd(t.block.Start, i)
		variable := r.b.variable(name)
		return variable, r.leaf(Coordinate, source, variable, cite(lemmaVariableValue, r.ring, name))
	}
	family := t.family.block
	c := r.codeStart(family, i)
	code := r.b.code(family.Dimension, family.Degree, c, t.argument.block.Start)
	return code, r.leaf(MapCoordinate, source, code,
		cite(lemmaPolynomialMapDef, r.ring, t.length, t.family.term, t.argument.source),
		cite(lemmaTwoStageEvaluation, r.ring, family.Dimension, family.Degree, c, t.argument.block.Start))
}

// scalar reads a scalar term as an integer polynomial over the names.
func (r *_Reifier) scalar(t core.Term, scope *_Scope) (core.Term, *Node, error) {
	v := r.b.v
	switch {
	case r.isRecordConstant(t, v.fieldZero, v.ringZero):
		p := r.b.zeroPolynomial(r.fresh("m", monomialType))
		return p, r.leaf(Zero, t, p, cite(lemmaVariableFreeEvaluation, r.ring, p)), nil
	case r.isRecordConstant(t, v.fieldOne, v.ringOne):
		p := r.b.onePolynomial()
		return p, r.leaf(One, t, p, cite(lemmaVariableFreeEvaluation, r.ring, p)), nil
	}
	if args, ok := headIs(t, v.integerMap); ok && len(args) == 2 && args[0].AlphaEquals(r.ring) {
		p := r.b.constantPolynomial(args[1])
		return p, r.leaf(Integer, t, p, cite(lemmaVariableFreeEvaluation, r.ring, p)), nil
	}
	if b := scope.lookup(t); b != nil && b.kind == ScalarBlock {
		p := r.b.variable(b.block.Start)
		return p, r.leaf(ScalarVariable, t, p, cite(lemmaVariableValue, r.ring, b.block.Start)), nil
	}
	if args, ok := headIs(t, v.moduleSum); ok && len(args) == 4 {
		return r.sum(t, args, scope)
	}
	if operation, operands, lemma, ok := r.fieldOperation(t); ok {
		polynomials := make([]core.Term, len(operands))
		nodes := make([]*Node, len(operands))
		for i, operand := range operands {
			p, node, err := r.scalar(operand, scope)
			if err != nil {
				return nil, nil, err
			}
			polynomials[i], nodes[i] = p, node
		}
		p := r.b.polynomialOperation(operation, polynomials...)
		return p, r.compound(Operation, t, p, []Citation{cite(lemmaEvalHom, r.ring), cite(lemma)}, nodes...), nil
	}
	if app, isApp := t.AsAppliedTerm(); isApp && app.Fun().Type().Equals(r.b.types.tuple) {
		tuple, err := r.tuple(app.Fun(), scope)
		if err != nil {
			return nil, nil, err
		}
		if !r.indexBelow(scope, app.Arg(), tuple.length) {
			if _, isNumeral := ext.NumeralValue(app.Arg()); isNumeral {
				return nil, nil, refuse(IndexOutsideBlock, t, "a coordinate at a numeral index not below the tuple's length")
			}
			return nil, nil, refuse(IndexOutsideBlock, t, "a coordinate at an index the arithmetic does not keep below the tuple's length")
		}
		p, node := r.coordinate(tuple, app.Arg(), t)
		return p, node, nil
	}
	if args, ok := headIs(t, v.polynomialValue); ok && len(args) == 3 && args[0].AlphaEquals(r.ring) {
		p, err := r.polynomial(args[1], scope)
		if err != nil {
			return nil, nil, err
		}
		x, err := r.tuple(args[2], scope)
		if err != nil {
			return nil, nil, err
		}
		if x.block == nil {
			return nil, nil, refuse(NotFirstOrder, t, "a polynomial evaluated at a polynomial map composes polynomials, outside the grammar")
		}
		if !x.length.AlphaEquals(p.n) {
			return nil, nil, refuse(DimensionMismatch, t, "a polynomial evaluated at a tuple of another length than its dimension")
		}
		code := r.b.code(p.n, p.d, p.start, x.block.Start)
		return code, r.leaf(PolynomialValue, t, code, cite(lemmaTwoStageEvaluation, r.ring, p.n, p.d, p.start, x.block.Start)), nil
	}
	if args, ok := headIs(t, v.polynomialEval); ok && len(args) == 6 &&
		r.isRecordConstant(args[0], v.fieldAdd, v.ringAdd) && r.isRecordConstant(args[1], v.fieldZero, v.ringZero) &&
		r.isRecordConstant(args[2], v.fieldMul, v.ringMul) && r.isRecordConstant(args[3], v.fieldOne, v.ringOne) {
		p, err := r.tuple(args[4], scope)
		if err != nil {
			return nil, nil, err
		}
		if p.block == nil {
			return nil, nil, refuse(NotFirstOrder, t, "a polynomial in one variable read off a polynomial map composes polynomials, outside the grammar")
		}
		at := scope.lookup(args[5])
		if at == nil || at.kind != ScalarBlock {
			return nil, nil, refuse(NotFirstOrder, t, "a polynomial in one variable evaluated at a term that is no scalar binder or parameter")
		}
		code := r.b.univariateCode(p.length, p.block.Start, at.block.Start)
		return code, r.leaf(UnivariateValue, t, code, cite(lemmaUnivariateEvaluation, r.ring, p.length, p.block.Start, at.block.Start)), nil
	}
	if _, isVar := t.AsVar(); isVar {
		return nil, nil, r.freeRefusal(t)
	}
	head, _ := ext.MatchesApply(t)
	if c, isConst := head.AsConst(); isConst {
		return nil, nil, refuse(NotFirstOrder, t, fmt.Sprintf("the function %s is not one the formulas speak of", c.Name()))
	}
	return nil, nil, refuse(NotFirstOrder, t, "a scalar term outside the grammar")
}

// sum reads module_sum(F.add, F.zero, {j | j < k}, λj. t), a finite sum
// of scalar terms over the indices below k, as the integer polynomial
// ring's sum of t's polynomials over the same indices, t read with j an
// index binder below k.
func (r *_Reifier) sum(t core.Term, args []core.Term, scope *_Scope) (core.Term, *Node, error) {
	v := r.b.v
	if !r.isRecordConstant(args[0], v.fieldAdd, v.ringAdd) || !r.isRecordConstant(args[1], v.fieldZero, v.ringZero) {
		return nil, nil, refuse(NotFirstOrder, t, "a sum under another addition or zero than the structure's")
	}
	k, ok := r.belowBound(args[2])
	if !ok {
		return nil, nil, refuse(NotFirstOrder, args[2], "a sum over an index set other than {j | j < k}")
	}
	family, isAbs := args[3].AsAbsTerm()
	if !isAbs {
		return nil, nil, refuse(NotFirstOrder, args[3], "a sum of a family that is no λ-abstraction over its index")
	}
	j := family.Var()
	p, child, err := r.scalar(family.Body(), scope.with(&_Binding{term: j, index: j, bound: k}, nil))
	if err != nil {
		return nil, nil, err
	}
	sum := r.b.sum(k, j, p, r.fresh("v", numType), r.fresh("i", numType))
	citations := []Citation{cite(lemmaEvalHom, r.ring), cite(lemmaMapSum), cite(lemmaSumCongruence), cite(lemmaFiniteBelow, k), cite(lemmaSumOnVariables)}
	return sum, r.compound(Sum, t, sum, citations, child), nil
}

// indexBelow tells whether the index e stays below k in the scope: a
// binder bounded by k, a numeral below a numeral k, or an index term
// whose bound the input's arithmetic derives from the scope's index
// bounds.
func (r *_Reifier) indexBelow(scope *_Scope, e, k core.Term) bool {
	if scope.boundedIndex(e, k) || numeralBelow(e, k) {
		return true
	}
	if r.in.Arithmetic == nil || !r.isIndexTerm(e) {
		return false
	}
	return r.in.Arithmetic.Below(scope.indexBounds(r.b), r.b.natLess(e, k))
}

// isIndexTerm tells whether e is a natural-number term built from
// numerals and variables by +, * and suc.
func (r *_Reifier) isIndexTerm(e core.Term) bool {
	if !e.Type().Equals(numType) {
		return false
	}
	if _, ok := ext.NumeralValue(e); ok {
		return true
	}
	if _, ok := e.AsVar(); ok {
		return true
	}
	for _, m := range []core.ConstTermMeta{r.b.v.natAdd, r.b.v.natMul} {
		if args, ok := headIs(e, m); ok && len(args) == 2 {
			return r.isIndexTerm(args[0]) && r.isIndexTerm(args[1])
		}
	}
	if args, ok := headIs(e, r.b.v.natSuc); ok && len(args) == 1 {
		return r.isIndexTerm(args[0])
	}
	return false
}

// isRecordConstant reads a field record's constant F.c, or the ring's
// field_ring(F).c, for the field projection and the ring projection
// of one component.
func (r *_Reifier) isRecordConstant(t core.Term, field, ring core.ConstTermMeta) bool {
	if args, ok := headIs(t, field); ok && len(args) == 1 && args[0].AlphaEquals(r.in.Structure.Field) {
		return true
	}
	args, ok := headIs(t, ring)
	return ok && len(args) == 1 && args[0].AlphaEquals(r.ring)
}

// fieldOperation reads an operation of the field record, F.add(a, b)
// or field_ring(F).add(a, b) and the like, and returns the integer
// polynomial ring's projection that reifies it, its operands, and the
// homomorphism reading that carries it.
func (r *_Reifier) fieldOperation(t core.Term) (core.ConstTermMeta, []core.Term, string, bool) {
	head, args := ext.MatchesApply(t)
	c, isConst := head.AsConst()
	if !isConst || len(args) < 2 {
		return core.ConstTermMeta{}, nil, "", false
	}
	v := r.b.v
	operations := []struct {
		field, ring core.ConstTermMeta
		arity       int
		lemma       string
	}{
		{v.fieldAdd, v.ringAdd, 2, lemmaMapAdd},
		{v.fieldMul, v.ringMul, 2, lemmaMapMul},
		{v.fieldNeg, v.ringNeg, 1, lemmaMapNeg},
		{v.fieldSub, v.ringSub, 2, lemmaMapSub},
	}
	for _, op := range operations {
		if len(args) != op.arity+1 {
			continue
		}
		atField := has(c, op.field) && args[0].AlphaEquals(r.in.Structure.Field)
		atRing := has(c, op.ring) && args[0].AlphaEquals(r.ring)
		if atField || atRing {
			return op.ring, args[1:], op.lemma, true
		}
	}
	return core.ConstTermMeta{}, nil, "", false
}

// numeralBelow tells whether the index and the bound are numerals, the
// index below the bound, so a coordinate read at the index stays inside
// its block.
func numeralBelow(index, bound core.Term) bool {
	i, ok := ext.NumeralValue(index)
	if !ok {
		return false
	}
	n, ok := ext.NumeralValue(bound)
	return ok && i.Cmp(n) < 0
}
