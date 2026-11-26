package different

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_ideals"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/trace_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/registry"
)

var TraceDualInclusionAndBidual = traceDualInclusionAndBidualThm{family.Add(registry.ProofEntry{
	Name: "TraceDualInclusionAndBidual",
	Key:  "prop_f3149849c4e1bad",
	Deps: []registry.EntryLike{trace_dual.TraceDualMonotone, ring_of_integers.TraceDualFull},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀M N:set(A).",
		Hypotheses: []string{
			"number_field(L)",
			"full_integer_lattice(L, M)",
			"full_integer_lattice(L, N)",
			"M ⊆ N",
		},
		Conclusion: "trace_dual(L, rational_image(L), N, integer_image(field_ring(L))) ⊆ " +
			"trace_dual(L, rational_image(L), M, integer_image(field_ring(L))) ∧ " +
			"trace_dual(L, " +
			"    rational_image(L), " +
			"    trace_dual(L, rational_image(L), M, integer_image(field_ring(L))), " +
			"    integer_image(field_ring(L))) = " +
			"M",
	},
		"Trace testing reverses inclusion. The trace-dual basis of a full integer lattice "+
			"is again a full integer lattice, and taking its dual restores the original basis."),
})}

var CodifferentStructure = codifferentStructureThm{family.Add(registry.ProofEntry{
	Name: "CodifferentStructure",
	Key:  "prop_689c36e8b003459",
	Deps: []registry.EntryLike{
		DifferentDef,
		ring_of_integers.RingOfIntegersFreeRankN,
		ring_of_integers.RingOfIntegersFractionField,
		field_trace.CharZeroTraceNondegenerate,
		int_lattice.IntegerRationalImagesStructure,
		trace_dual.CodifferentBoundedFractionalIdeal,
		trace_dual.CodifferentInvertible,
		number_ideals.NumberRingFactorization,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A).",
		Hypotheses: []string{
			"number_field(L)",
		},
		Conclusion: "bounded_fractional(field_ring(L), " +
			"    ring_of_integers(field_ring(L)), " +
			"    trace_dual(L, " +
			"        rational_image(L), " +
			"        ring_of_integers(field_ring(L)), " +
			"        integer_image(field_ring(L)))) ∧ " +
			"ring_of_integers(field_ring(L)) ⊆ " +
			"trace_dual(L, " +
			"    rational_image(L), " +
			"    ring_of_integers(field_ring(L)), " +
			"    integer_image(field_ring(L))) ∧ " +
			"invertible_fractional(field_ring(L), " +
			"    ring_of_integers(field_ring(L)), " +
			"    trace_dual(L, " +
			"        rational_image(L), " +
			"        ring_of_integers(field_ring(L)), " +
			"        integer_image(field_ring(L)))) ∧ " +
			"ring_ideal(restrict_ring(field_ring(L), ring_of_integers(field_ring(L))), " +
			"    number_different(L)) ∧ " +
			"number_different(L) ≠ {L.zero}",
	},
		"An integral basis is simultaneously an integer basis and rational field "+
			"basis. With trace nondegeneracy and the fraction-field statements, apply "+
			"the common codifferent theorems and number-ring ideal invertibility."),
})}
