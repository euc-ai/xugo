package real_closed_quantifier_elimination

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_closed_quantifier_elimination.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the models quantifiers are
// eliminated over: the pairs of a field and an order, real closed, with the
// field's carrier, reading an atom as negativity.
var family = registry.NewFamily(
	"algebra/field/real_closed_quantifier_elimination", familyCNF).WithAbbrev(Abbrev{
	{Name: "realClosed", Text: "λM:prod(field_ops(A), A → A → bool). " +
		"    real_closed_field(fst(M), snd(M))"},
	{Name: "carrier", Text: "λM:prod(field_ops(A), A → A → bool). fst(M).carrier"},
	{Name: "negative", Text: "λM:prod(field_ops(A), A → A → bool). " +
		"    ordered_ring_formula_atom(fst(M), snd(M))"},
})
