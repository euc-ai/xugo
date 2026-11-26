package finite_field

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed finite_field.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names a field's map from the
// integers and its numerals, the polynomial X^Q − X over a field, the ideal
// and the multiples of an integer, the residues below a number, and a
// field's nonzero squares and the half (q − 1)/2 of its q − 1 nonzero
// elements.
var family = registry.NewFamily("algebra/field/finite_field", familyCNF).WithAbbrev(Abbrev{
	{Name: "integerMap", Text: "λF:field_ops(A). integer_map(field_ring(F))"},
	{Name: "numeral", Text: "λF:field_ops(A). λn:num. monoid_pow(F.add, F.zero, F.one, n)"},
	{Name: "xPowerMinusX", Text: "λF:field_ops(A). λQ:num. " +
		"    vec_sub(F.sub, basis_vector(F.zero, F.one, Q), basis_vector(F.zero, F.one, 1))"},
	{Name: "integerIdeal", Text: "λn:num. ideal_span(int_ring, {int_of_num(n)})"},
	{Name: "multiplesOf", Text: "λd:int. image(λz:int. d * z, 𝕌)"},
	{Name: "residues", Text: "λn:num. {r:num | r < n}"},
	{Name: "squares", Text: "λk:field_ops(A). {k.mul(z, z) | z:A | z ∈ k.carrier ∧ z ≠ k.zero}"},
	{Name: "half", Text: "λk:field_ops(A). div(card(k.carrier) - 1, 2)"},
})
