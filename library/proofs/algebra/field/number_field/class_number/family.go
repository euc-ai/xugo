package class_number

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ideal_norm"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed class_number.cnf.pb
var familyCNF []byte

var family = registry.NewFamily(
	"algebra/field/number_field/class_number", familyCNF).WithOuterAbbrev(
	ideal_norm.ChapterAbbrev).WithAbbrev(Abbrev{
	// The ideal class group: the classes of the invertible fractional ideals
	// modulo the principal ones, under the set product and inverse.
	{Name: "ClassGroup", Text: "mk_group(set_mul(fractional_mul(field_ring(L), «O»)), " +
		"    principal_fractional_ideals(field_ring(L), «O»), " +
		"    set_inv(fractional_inverse(field_ring(L), «O»)), " +
		"    ideal_classes(field_ring(L), «O»))"},
	// The nonzero integral ideals whose norm is at most the class-number bound
	// at the integral basis e.
	{Name: "BoundedIdeals", Text: "{I:set(A) | " +
		"    ring_ideal(«R», I) ∧ " +
		"    I ≠ {L.zero} ∧ " +
		"    number_ideal_norm(field_ring(L), I) ≤ class_number_bound(field_ring(L), n, e)}"},
})
