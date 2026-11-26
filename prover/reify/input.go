package reify

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// Structure is the field record a proposition speaks about: F of type
// field_ops(A), and in the ordered theory the strict order lt of type
// A → A → bool. The theory is read off Order: nil is the ring theory,
// whose atoms are P = 0; an order makes it the ordered ring theory,
// whose atoms are P < 0.
type Structure struct {
	Field core.Term
	Order core.Term
}

// Ordered tells whether the structure carries an order.
func (s Structure) Ordered() bool { return s.Order != nil }

// BlockKind is what a block of names stands for.
type BlockKind int

const (
	// ScalarBlock is one name, standing for a carrier element.
	ScalarBlock BlockKind = iota
	// PolynomialBlock is coefficient_count(n, d) names, the coefficient
	// slots of a polynomial in n variables of degree at most d.
	PolynomialBlock
	// FamilyBlock is k consecutive coefficient blocks, one per member of
	// a family of k polynomials.
	FamilyBlock
	// TupleBlock is n names, the coordinates of a tuple of length n.
	TupleBlock
)

func (k BlockKind) String() string {
	switch k {
	case ScalarBlock:
		return "scalar"
	case PolynomialBlock:
		return "polynomial"
	case FamilyBlock:
		return "family"
	case TupleBlock:
		return "tuple"
	}
	return fmt.Sprintf("BlockKind(%d)", int(k))
}

// Parameter is a term of the proposition the formula names rather than
// quantifies: a scalar, a polynomial with its dimension and degree
// bound, a family of Count polynomials with one bound, or a tuple with
// its length. The term is usually a free variable; in the embedding
// mode it is the image of one, a closed term, and an occurrence is
// recognized up to α-equivalence. The bounds are the caller's: the
// closer reads them off its facts.
type Parameter struct {
	Name      string
	Term      core.Term
	Kind      BlockKind
	Dimension core.Term
	Degree    core.Term
	Count     core.Term
}

// Unfolder expands a defined constant's application into the body its
// definition equates it with. The reifier asks it for every predicate
// or set outside the grammar; ok=false leaves the constant unread,
// and the proposition is refused at that subterm. The lemma is the
// name of the definition, recorded in the plan.
type Unfolder interface {
	Unfold(t core.Term) (body core.Term, lemma string, ok bool)
}

// Arithmetic decides the bound of an index the grammar reads at a
// computed position: whether goal, e < k for the index term e and the
// length or count k, follows from the hypotheses, the bounds j < m of
// the index binders in scope, by the caller's arithmetic. The reifier
// asks it only where the index is not a binder bounded by k itself or a
// numeral below a numeral k; the answer must be the one the bridge's
// arithmetic proves under the same bounds.
type Arithmetic interface {
	Below(hypotheses []core.Term, goal core.Term) bool
}

// Input is one reification: the structure, the proposition about it,
// the parameters it names, the unfolder for its defined constants
// (nil unfolds nothing), the arithmetic that decides a computed index's
// bound (nil reads an index only at a binder bounded by the length or
// count, or at a numeral below a numeral one) and the vocabulary it is
// written in. With no parameters the proposition is read in sentence
// mode and must be closed apart from the structure and its numeric
// data.
type Input struct {
	Structure   Structure
	Proposition core.Term
	Parameters  []Parameter
	Unfold      Unfolder
	Arithmetic  Arithmetic
	Vocabulary  *Vocabulary
}

// Block is a block of consecutive names: Length names from Start. A
// parameter's block carries the parameter's name and bounds; a
// binder's carries the bound variable, its name and the bounds read
// off its guard.
type Block struct {
	Owner     string
	Variable  core.VarTerm
	Kind      BlockKind
	Parameter bool
	Start     core.Term
	Length    core.Term
	Dimension core.Term
	Degree    core.Term
	Count     core.Term
}

// Allocation is the name allocation of one reification: the blocks in
// the order they were allocated, parameters first, and the frontier,
// the first name past the parameters' blocks, where the outermost
// binder's block starts.
type Allocation struct {
	Blocks   []*Block
	Frontier core.Term
}

// ObligationKind sorts the obligations a bridge is proved under.
type ObligationKind int

const (
	// StructureObligation is field_on(F), and ordered_field_on(F, lt) in
	// the ordered theory.
	StructureObligation ObligationKind = iota
	// ScalarObligation is a scalar parameter's membership in the carrier.
	ScalarObligation
	// PolynomialObligation is a polynomial parameter's membership in the
	// polynomial algebra below its dimension, or its degree bound; a
	// family's hold at every member below its count.
	PolynomialObligation
	// TupleObligation is a tuple parameter's ring_tuple guard.
	TupleObligation
)

// Obligation is a statement the caller discharges for the proposition
// and the formula's interpretation to agree: a hypothesis of the
// bridge, closed by the caller's facts.
type Obligation struct {
	Kind      ObligationKind
	Owner     string
	Statement core.Term
}

// Citation names the corpus lemma a node's bridge cites, as
// family.Member, and the witnesses it is instantiated at that the
// syntax determines. The environment the node is evaluated in, and
// the formula bound at a quantifier, are the proof constructor's.
type Citation struct {
	Lemma     string
	Witnesses []core.Term
}

// NodeKind is the shape of a node of the bridge plan.
type NodeKind int

const (
	Truth NodeKind = iota
	Falsity
	Negation
	Conjunction
	Disjunction
	Implication
	Equivalence
	ForallScalar
	ExistsScalar
	ForallTuple
	ExistsTuple
	ForallPolynomial
	ExistsPolynomial
	ForallFamily
	ExistsFamily
	Conjoin
	ExistsIndex
	Equality
	TupleEquality
	StrictInequality
	WeakInequality
	CarrierMembership
	NormalTuple
	BoundedPolynomial
	Nonempty
	Emptiness
	Membership
	Unfolding
	Zero
	One
	Integer
	ScalarVariable
	Coordinate
	MapCoordinate
	Operation
	PolynomialValue
	UnivariateValue
	Sum
)

var nodeKindNames = [...]string{
	Truth: "truth", Falsity: "falsity", Negation: "negation", Conjunction: "conjunction",
	Disjunction: "disjunction", Implication: "implication", Equivalence: "equivalence",
	ForallScalar: "forall scalar", ExistsScalar: "exists scalar", ForallTuple: "forall tuple",
	ExistsTuple: "exists tuple", ForallPolynomial: "forall polynomial", ExistsPolynomial: "exists polynomial",
	ForallFamily: "forall family", ExistsFamily: "exists family", Conjoin: "conjoin", ExistsIndex: "exists index",
	Equality: "equality", TupleEquality: "tuple equality", StrictInequality: "strict inequality",
	WeakInequality: "weak inequality", CarrierMembership: "carrier membership", NormalTuple: "normal tuple",
	BoundedPolynomial: "bounded polynomial", Nonempty: "nonempty", Emptiness: "emptiness",
	Membership: "membership", Unfolding: "unfolding", Zero: "zero", One: "one", Integer: "integer",
	ScalarVariable: "scalar variable", Coordinate: "coordinate", MapCoordinate: "map coordinate",
	Operation: "operation", PolynomialValue: "polynomial value", UnivariateValue: "univariate value", Sum: "sum",
}

func (k NodeKind) String() string {
	if int(k) < len(nodeKindNames) && nodeKindNames[k] != "" {
		return nodeKindNames[k]
	}
	return fmt.Sprintf("NodeKind(%d)", int(k))
}

// Node is one node of the bridge plan: the HOL subterm it reads, the
// term it wrote for it (a formula, or an integer polynomial at a
// scalar node), the block a quantifier node binds, the lemmas its
// bridge cites, and the nodes of its subterms.
type Node struct {
	Kind      NodeKind
	Source    core.Term
	Term      core.Term
	Block     *Block
	Citations []Citation
	Children  []*Node
}

// Result is what a reification yields: the formula, the names, the
// obligations and the plan. The environment the bridge evaluates the
// formula in is the proof constructor's, assembled from the blocks.
type Result struct {
	Formula     core.Term
	Names       Allocation
	Obligations []Obligation
	Plan        *Node
}

// Reason sorts the refusals.
type Reason int

const (
	// NotFirstOrder is a subterm the grammar has no reading of: a
	// function the formulas cannot speak of, a quantifier over a type
	// the carrier does not encode, an equality at such a type.
	NotFirstOrder Reason = iota
	// UnguardedQuantifier is a binder whose guard the grammar needs and
	// no hypothesis supplies: a tuple without ring_tuple, a scalar
	// without the carrier, a polynomial without polynomial_bound, an
	// index without a bound.
	UnguardedQuantifier
	// FreeParameterInSentence is a free carrier-typed variable in
	// sentence mode.
	FreeParameterInSentence
	// UndeclaredParameter is a free carrier-typed variable no parameter
	// names.
	UndeclaredParameter
	// NoUnfolding is a constant outside the grammar whose definition the
	// unfolder does not supply.
	NoUnfolding
	// DimensionMismatch is a polynomial, a map or a tuple whose
	// dimensions disagree where one code must read them.
	DimensionMismatch
	// MissingVocabulary is a connective the vocabulary lacks.
	MissingVocabulary
	// IndexOutsideBlock is a coordinate of a tuple or a member of a
	// family read at an index the arithmetic does not keep below the
	// tuple's length or the family's count: the name it would read lies
	// outside the block.
	IndexOutsideBlock
)

func (r Reason) String() string {
	switch r {
	case NotFirstOrder:
		return "not first-order"
	case UnguardedQuantifier:
		return "unguarded quantifier"
	case FreeParameterInSentence:
		return "free parameter in sentence mode"
	case UndeclaredParameter:
		return "undeclared parameter"
	case NoUnfolding:
		return "no unfolding"
	case DimensionMismatch:
		return "dimension mismatch"
	case MissingVocabulary:
		return "missing vocabulary"
	case IndexOutsideBlock:
		return "index outside the block"
	}
	return fmt.Sprintf("Reason(%d)", int(r))
}

// Refusal is the reifier's answer to a proposition outside the
// grammar: the subterm it stopped at and why. It is the one error
// the package returns, since the proposition is the user's goal.
type Refusal struct {
	Reason  Reason
	Subterm core.Term
	Detail  string
}

func (r *Refusal) Error() string {
	return fmt.Sprintf("reify: %s: %s: %s", r.Reason, r.Detail, ext.PrintTerm(r.Subterm))
}

func refuse(reason Reason, subterm core.Term, detail string) error {
	return &Refusal{Reason: reason, Subterm: subterm, Detail: detail}
}
