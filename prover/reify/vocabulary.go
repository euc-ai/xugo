package reify

import (
	"fmt"
	"math/big"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// Vocabulary is the constants the reifier reads in a proposition and
// writes in a formula: the formula constructors and derived
// connectives of first_order, the two theories' atoms, the integer
// polynomials and their coefficient encoding, the ring and field
// records, the guards of the grammar, the set vocabulary, the finite
// sum, and the arithmetic the names and indices are spelled in. The caller supplies them by
// name: the engine from its constant registry, a test from a table.
// The reifier never imports the corpus, so the corpus can hold the
// cards the closer waits for.
type Vocabulary struct {
	atom, not, and, or, implies, iff, exists, forall, allRange, existsRange, conjoin core.ConstTermMeta

	ringTrue, ringEquality, orderedTrue, weakInequality, orderedEquality core.ConstTermMeta

	polynomialVariable, polynomialOne, polynomialConstant, integerRing, integerPolynomialRing, polynomialCode, univariateCode, coefficientCount core.ConstTermMeta

	ringAdd, ringZero, ringNeg, ringMul, ringOne, ringSub, ringCarrier                   core.ConstTermMeta
	fieldAdd, fieldZero, fieldNeg, fieldMul, fieldOne, fieldSub, fieldCarrier, fieldRing core.ConstTermMeta

	integerMap, polynomialValue, polynomialEval, polynomialMap, polynomialBound, polynomialAlgebra, ringTuple, orderedLe, fieldOn, orderedFieldOn core.ConstTermMeta

	member, comprehension, comprehensionSpec, empty, moduleSum core.ConstTermMeta

	natAdd, natMul, natSuc, natLess, intOfNum, intSub core.ConstTermMeta
}

// _VocabularyEntry is one row of the name table: the constant's name,
// the slot it fills, and whether the vocabulary may lack it. The two
// derived connectives fo_or and fo_iff are optional until their cards
// land; a proposition that needs one is then refused at that node.
type _VocabularyEntry struct {
	name     core.TermName
	slot     *core.ConstTermMeta
	optional bool
}

func (v *Vocabulary) entries() []_VocabularyEntry {
	return []_VocabularyEntry{
		{"fo_atom", &v.atom, false},
		{"fo_not", &v.not, false},
		{"fo_and", &v.and, false},
		{"fo_or", &v.or, true},
		{"fo_implies", &v.implies, false},
		{"fo_iff", &v.iff, true},
		{"fo_exists", &v.exists, false},
		{"fo_forall", &v.forall, false},
		{"fo_all_range", &v.allRange, false},
		{"fo_exists_range", &v.existsRange, false},
		{"fo_conjoin", &v.conjoin, false},

		{"ring_true_formula", &v.ringTrue, false},
		{"ring_equality_formula", &v.ringEquality, false},
		{"ordered_ring_true_formula", &v.orderedTrue, false},
		{"polynomial_weak_inequality_formula", &v.weakInequality, false},
		{"ordered_ring_equality_formula", &v.orderedEquality, false},

		{"polynomial_algebra_var", &v.polynomialVariable, false},
		{"polynomial_algebra_one", &v.polynomialOne, false},
		{"polynomial_algebra_const", &v.polynomialConstant, false},
		{"int_ring", &v.integerRing, false},
		{"integer_polynomial_ring", &v.integerPolynomialRing, false},
		{"polynomial_code", &v.polynomialCode, false},
		{"univariate_code", &v.univariateCode, false},
		{"coefficient_count", &v.coefficientCount, false},

		{"ring_add", &v.ringAdd, false},
		{"ring_zero", &v.ringZero, false},
		{"ring_neg", &v.ringNeg, false},
		{"ring_mul", &v.ringMul, false},
		{"ring_one", &v.ringOne, false},
		{"ring_sub", &v.ringSub, false},
		{"ring_carrier", &v.ringCarrier, false},
		{"field_add", &v.fieldAdd, false},
		{"field_zero", &v.fieldZero, false},
		{"field_neg", &v.fieldNeg, false},
		{"field_mul", &v.fieldMul, false},
		{"field_one", &v.fieldOne, false},
		{"field_sub", &v.fieldSub, false},
		{"field_carrier", &v.fieldCarrier, false},
		{"field_ring", &v.fieldRing, false},

		{"integer_map", &v.integerMap, false},
		{"polynomial_value", &v.polynomialValue, false},
		{"polynomial_eval", &v.polynomialEval, false},
		{"polynomial_map", &v.polynomialMap, false},
		{"polynomial_bound", &v.polynomialBound, false},
		{"polynomial_algebra", &v.polynomialAlgebra, false},
		{"ring_tuple", &v.ringTuple, false},
		{"ordered_le", &v.orderedLe, false},
		{"field_on", &v.fieldOn, false},
		{"ordered_field_on", &v.orderedFieldOn, false},

		{"set_member", &v.member, false},
		{"set_comprehension", &v.comprehension, false},
		{"comprehension_spec", &v.comprehensionSpec, false},
		{"empty_set", &v.empty, false},
		{"module_sum", &v.moduleSum, false},

		{"+", &v.natAdd, false},
		{"*", &v.natMul, false},
		{"suc", &v.natSuc, false},
		{"<", &v.natLess, false},
		{"int_of_num", &v.intOfNum, false},
		{"int_sub", &v.intSub, false},
	}
}

// VocabularyNames is every constant name a vocabulary reads, in table
// order, for a caller that checks its registry before constructing one.
func VocabularyNames() []core.TermName {
	var v Vocabulary
	entries := v.entries()
	names := make([]core.TermName, len(entries))
	for i, e := range entries {
		names[i] = e.name
	}
	return names
}

// NewVocabulary reads every constant of the table through lookup, which
// returns nil for a name it does not know. A required name that is
// missing is an error naming all of them: the corpus the caller runs
// against lacks a chapter the reifier writes in.
func NewVocabulary(lookup func(core.TermName) core.ConstTermMeta) (*Vocabulary, error) {
	v := &Vocabulary{}
	var missing []string
	for _, e := range v.entries() {
		meta := lookup(e.name)
		if meta.IsZero() && !e.optional {
			missing = append(missing, string(e.name))
		}
		*e.slot = meta
	}
	if len(missing) > 0 {
		return nil, fmt.Errorf("reify: the vocabulary lacks %s", strings.Join(missing, ", "))
	}
	return v, nil
}

// has tells whether the constant c is the vocabulary's meta m; false
// for an optional meta the vocabulary lacks.
func has(c core.ConstTerm, m core.ConstTermMeta) bool {
	return !m.IsZero() && c.Meta().Equals(m)
}

// headIs reads t as the application of the vocabulary constant m to
// arguments and returns them; nil, false otherwise.
func headIs(t core.Term, m core.ConstTermMeta) ([]core.Term, bool) {
	head, args := ext.MatchesApply(t)
	c, ok := head.AsConst()
	if !ok || !has(c, m) {
		return nil, false
	}
	return args, true
}

// _Types is the HOL types of one reification: the carrier A read off
// the field record's type field_ops(A), and the types built on it.
type _Types struct {
	carrier    core.HolType // A
	carrierSet core.HolType // set(A), a predicate A → bool
	tuple      core.HolType // num → A
	polynomial core.HolType // (num → num) → A, a polynomial over the carrier
	family     core.HolType // num → (num → num) → A
	fieldOps   core.HolType // field_ops(A)
	ringOps    core.HolType // ring_ops(A)
	order      core.HolType // A → A → bool
}

var (
	numType                   = ext.NumType
	intType                   = ext.MakeType("int")
	monomialType              = ext.MakeFun(numType, numType)
	integerPolynomialType     = ext.MakeFun(monomialType, intType)
	formulaType               = ext.MakeType("fo_formula", integerPolynomialType)
	integerRingType           = ext.MakeType("ring_ops", intType)
	integerPolynomialRingType = ext.MakeType("ring_ops", integerPolynomialType)
)

// fieldOpsCarrier reads A off a type field_ops(A); ok=false for any
// other type.
func fieldOpsCarrier(t core.HolType) (core.HolType, bool) {
	composite, ok := t.(core.CompositeType)
	if !ok || composite.Meta().Name() != "field_ops" {
		return nil, false
	}
	return composite.SubType(0), true
}

func newTypes(carrier core.HolType) _Types {
	return _Types{
		carrier:    carrier,
		carrierSet: ext.MakeFun(carrier, core.TypeBool()),
		tuple:      ext.MakeFun(numType, carrier),
		polynomial: ext.MakeFun(monomialType, carrier),
		family:     ext.MakeFun(numType, monomialType, carrier),
		fieldOps:   ext.MakeType("field_ops", carrier),
		ringOps:    ext.MakeType("ring_ops", carrier),
		order:      ext.MakeFun(carrier, carrier, core.TypeBool()),
	}
}

// _Builder writes the terms of a reification: the formula's nodes, the
// integer polynomials of its atoms, the name arithmetic and the
// obligations' statements. Every constant is instantiated at the type
// the position needs; a vocabulary meta whose abstract type does not
// take that instance is a corpus inconsistency and panics in the
// kernel's constructor.
type _Builder struct {
	v     *Vocabulary
	types _Types
}

func constant(m core.ConstTermMeta, t core.HolType) core.Term {
	return core.MakeConstTerm(m, t)
}

func apply(f core.Term, args ...core.Term) core.Term {
	if len(args) == 0 {
		return f
	}
	return ext.Apply(f, args...)
}

// Formulas.

func (b *_Builder) truth(ordered bool) core.Term {
	if ordered {
		return constant(b.v.orderedTrue, formulaType)
	}
	return constant(b.v.ringTrue, formulaType)
}

func (b *_Builder) unary(m core.ConstTermMeta, φ core.Term) core.Term {
	return apply(constant(m, ext.MakeFun(formulaType, formulaType)), φ)
}

func (b *_Builder) binary(m core.ConstTermMeta, φ, ψ core.Term) core.Term {
	return apply(constant(m, ext.MakeFun(formulaType, formulaType, formulaType)), φ, ψ)
}

func (b *_Builder) not(φ core.Term) core.Term        { return b.unary(b.v.not, φ) }
func (b *_Builder) and(φ, ψ core.Term) core.Term     { return b.binary(b.v.and, φ, ψ) }
func (b *_Builder) implies(φ, ψ core.Term) core.Term { return b.binary(b.v.implies, φ, ψ) }
func (b *_Builder) or(φ, ψ core.Term) core.Term      { return b.binary(b.v.or, φ, ψ) }
func (b *_Builder) iff(φ, ψ core.Term) core.Term     { return b.binary(b.v.iff, φ, ψ) }

func (b *_Builder) atom(p core.Term) core.Term {
	return apply(constant(b.v.atom, ext.MakeFun(integerPolynomialType, formulaType)), p)
}

func (b *_Builder) quantifier(m core.ConstTermMeta, name, φ core.Term) core.Term {
	return apply(constant(m, ext.MakeFun(numType, formulaType, formulaType)), name, φ)
}

func (b *_Builder) range_(m core.ConstTermMeta, start, length, φ core.Term) core.Term {
	return apply(constant(m, ext.MakeFun(numType, numType, formulaType, formulaType)), start, length, φ)
}

// conjoin is fo_conjoin(⊤, k, λj. φ): the finite conjunction of φ over
// the index j below k, with the theory's true formula at its base.
func (b *_Builder) conjoin(ordered bool, k core.Term, j core.VarTerm, φ core.Term) core.Term {
	return apply(
		constant(b.v.conjoin, ext.MakeFun(formulaType, numType, ext.MakeFun(numType, formulaType), formulaType)),
		b.truth(ordered), k, core.Abs(j, φ))
}

func (b *_Builder) comparison(m core.ConstTermMeta, p, q core.Term) core.Term {
	return apply(constant(m, ext.MakeFun(integerPolynomialType, integerPolynomialType, formulaType)), p, q)
}

// difference is the integer polynomial λm. p(m) − q(m), the atom of a
// strict comparison p < q.
func (b *_Builder) difference(p, q core.Term, m core.VarTerm) core.Term {
	sub := constant(b.v.intSub, ext.MakeFun(intType, intType, intType))
	return core.Abs(m, apply(sub, at(p, m), at(q, m)))
}

// at is p applied to m, reduced when p is an abstraction, so the formula
// the reifier writes is β-normal.
func at(p core.Term, m core.VarTerm) core.Term {
	if abs, ok := p.AsAbsTerm(); ok {
		return abs.Body().Substitute(core.MakeTermSubst(abs.Var(), m))
	}
	return apply(p, m)
}

// Integer polynomials.

func (b *_Builder) integerRing() core.Term { return constant(b.v.integerRing, integerRingType) }

func (b *_Builder) zeroPolynomial(m core.VarTerm) core.Term {
	zero := apply(constant(b.v.intOfNum, ext.MakeFun(numType, intType)), b.numeral(0))
	return core.Abs(m, zero)
}

func (b *_Builder) onePolynomial() core.Term {
	return apply(constant(b.v.polynomialOne, ext.MakeFun(integerRingType, integerPolynomialType)), b.integerRing())
}

func (b *_Builder) constantPolynomial(z core.Term) core.Term {
	return apply(constant(b.v.polynomialConstant, ext.MakeFun(integerRingType, intType, integerPolynomialType)), b.integerRing(), z)
}

func (b *_Builder) variable(name core.Term) core.Term {
	return apply(constant(b.v.polynomialVariable, ext.MakeFun(integerRingType, numType, integerPolynomialType)), b.integerRing(), name)
}

func (b *_Builder) code(n, d, c, x core.Term) core.Term {
	return apply(constant(b.v.polynomialCode, ext.MakeFun(numType, numType, numType, numType, integerPolynomialType)), n, d, c, x)
}

// univariateCode is the integer polynomial reading a polynomial in one
// variable with n coefficients from the block at c, at the slot x.
func (b *_Builder) univariateCode(n, c, x core.Term) core.Term {
	return apply(constant(b.v.univariateCode, ext.MakeFun(numType, numType, numType, integerPolynomialType)), n, c, x)
}

// polynomialOperation applies the integer polynomial ring's operation
// read by the ring projection m (ring_add, ring_mul, ring_neg or
// ring_sub) to its operands.
func (b *_Builder) polynomialOperation(m core.ConstTermMeta, operands ...core.Term) core.Term {
	types := []core.HolType{integerPolynomialRingType}
	for range operands {
		types = append(types, integerPolynomialType)
	}
	types = append(types, integerPolynomialType)
	ring := constant(b.v.integerPolynomialRing, integerPolynomialRingType)
	return apply(constant(m, ext.MakeFun(types[0], types[1], types[2:]...)), append([]core.Term{ring}, operands...)...)
}

// Name arithmetic.

func (b *_Builder) numeral(k int64) core.Term { return ext.MakeNumeral(big.NewInt(k)) }

func isNumeral(t core.Term, k int64) bool {
	value, ok := ext.NumeralValue(t)
	return ok && value.IsInt64() && value.Int64() == k
}

func (b *_Builder) natAdd(s, t core.Term) core.Term {
	switch {
	case isNumeral(s, 0):
		return t
	case isNumeral(t, 0):
		return s
	}
	return apply(constant(b.v.natAdd, ext.MakeFun(numType, numType, numType)), s, t)
}

func (b *_Builder) natMul(s, t core.Term) core.Term {
	switch {
	case isNumeral(s, 1):
		return t
	case isNumeral(t, 1):
		return s
	case isNumeral(s, 0) || isNumeral(t, 0):
		return b.numeral(0)
	}
	return apply(constant(b.v.natMul, ext.MakeFun(numType, numType, numType)), s, t)
}

func (b *_Builder) natLess(s, t core.Term) core.Term {
	return apply(constant(b.v.natLess, ext.MakeFun(numType, numType, core.TypeBool())), s, t)
}

// natSum is the sum of the lengths, left-nested, zero summands dropped.
func (b *_Builder) natSum(lengths []core.Term) core.Term {
	sum := b.numeral(0)
	for _, l := range lengths {
		sum = b.natAdd(sum, l)
	}
	return sum
}

func (b *_Builder) coefficientCount(n, d core.Term) core.Term {
	return apply(constant(b.v.coefficientCount, ext.MakeFun(numType, numType, numType)), n, d)
}

// Obligations' statements.

func (b *_Builder) fieldRing(F core.Term) core.Term {
	return apply(constant(b.v.fieldRing, ext.MakeFun(b.types.fieldOps, b.types.ringOps)), F)
}

func (b *_Builder) fieldCarrier(F core.Term) core.Term {
	return apply(constant(b.v.fieldCarrier, ext.MakeFun(b.types.fieldOps, b.types.carrierSet)), F)
}

func (b *_Builder) member(x, S core.Term) core.Term {
	elementType := x.Type()
	return apply(constant(b.v.member, ext.MakeFun(elementType, ext.MakeFun(elementType, core.TypeBool()), core.TypeBool())), x, S)
}

// below is the set {i:num | i < n}, spelled as the text parser lowers
// a set-builder: set_comprehension(λv. ∃i. comprehension_spec(v, i < n, i)).
func (b *_Builder) below(n core.Term, v, i core.VarTerm) core.Term {
	numSet := ext.MakeFun(numType, core.TypeBool())
	spec := apply(constant(b.v.comprehensionSpec, ext.MakeFun(numType, core.TypeBool(), numType, core.TypeBool())), v, b.natLess(i, n), i)
	generator := core.Abs(v, ext.Exists(i)(spec).Core())
	return apply(constant(b.v.comprehension, ext.MakeFun(numSet, numSet)), generator)
}

// sum is module_sum(integer_polynomial_ring.add, integer_polynomial_ring.zero,
// {i | i < k}, λj. p): the finite sum of the integer polynomials p over
// the indices j below k.
func (b *_Builder) sum(k core.Term, j core.VarTerm, p core.Term, v, i core.VarTerm) core.Term {
	ring := constant(b.v.integerPolynomialRing, integerPolynomialRingType)
	add := apply(constant(b.v.ringAdd, ext.MakeFun(integerPolynomialRingType, integerPolynomialType, integerPolynomialType, integerPolynomialType)), ring)
	zero := apply(constant(b.v.ringZero, ext.MakeFun(integerPolynomialRingType, integerPolynomialType)), ring)
	numSet := ext.MakeFun(numType, core.TypeBool())
	family := ext.MakeFun(numType, integerPolynomialType)
	sumType := ext.MakeFun(add.Type(), integerPolynomialType, numSet, family, integerPolynomialType)
	return apply(constant(b.v.moduleSum, sumType), add, zero, b.below(k, v, i), core.Abs(j, p))
}

func (b *_Builder) polynomialAlgebraBelow(ring, n core.Term, v, i core.VarTerm) core.Term {
	numSet := ext.MakeFun(numType, core.TypeBool())
	polynomialSet := ext.MakeFun(b.types.polynomial, core.TypeBool())
	return apply(constant(b.v.polynomialAlgebra, ext.MakeFun(b.types.ringOps, numSet, polynomialSet)), ring, b.below(n, v, i))
}

func (b *_Builder) polynomialBound(ring, n, d, p core.Term) core.Term {
	return apply(constant(b.v.polynomialBound, ext.MakeFun(b.types.ringOps, numType, numType, b.types.polynomial, core.TypeBool())), ring, n, d, p)
}

func (b *_Builder) ringTuple(ring, n, x core.Term) core.Term {
	return apply(constant(b.v.ringTuple, ext.MakeFun(b.types.ringOps, numType, b.types.tuple, core.TypeBool())), ring, n, x)
}

func (b *_Builder) fieldOn(F core.Term) core.Term {
	return apply(constant(b.v.fieldOn, ext.MakeFun(b.types.fieldOps, core.TypeBool())), F)
}

func (b *_Builder) orderedFieldOn(F, lt core.Term) core.Term {
	return apply(constant(b.v.orderedFieldOn, ext.MakeFun(b.types.fieldOps, b.types.order, core.TypeBool())), F, lt)
}
