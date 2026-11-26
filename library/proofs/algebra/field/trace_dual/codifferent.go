package trace_dual

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/registry"
)

var CodifferentBoundedFractionalIdeal = codifferentBoundedFractionalIdealThm{family.Add(registry.ProofEntry{
	Name: "CodifferentBoundedFractionalIdeal",
	Key:  "prop_611ae91b44d7f3a9",
	Reading: "The common S-basis and K-basis makes every multiplication matrix of an element of B " +
		"integral over S, which gives B⊆D(B,S); integral closedness and monogenicity are not assumed.",
	Deps: []registry.EntryLike{
		TraceDualFreeLattice,
		TraceDualIsFunctionalDual,
		field_trace.FieldTraceInSubring,
		field_trace.FieldTraceLinear,
		functional_dual.FunctionalDualBounded,
		integral_element.FiniteSpanCommonDenominator,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K S B E:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"S ⊆ B",
			"finite(E)",
			"module_basis(«ScalarS», restrict_module(«Regular», B), E)",
			"module_basis(«ScalarK», «Regular», E)",
			"∀x:A. x ∈ L.carrier ∧ x ≠ L.zero ⇒ ∃y:A. y ∈ L.carrier ∧ field_trace(L, K, x * y) ≠ L.zero",
			"fraction_field_carrier(«ScalarK», S)",
			"fraction_field_carrier(field_ring(L), B)",
		},
		Conclusion: "bounded_fractional(field_ring(L), B, trace_dual(L, K, B, S)) ∧ " +
			"B ⊆ trace_dual(L, K, B, S) ∧ " +
			"(∃F:set(A). " +
			"    finite(F) ∧ module_basis(«ScalarS», restrict_module(«Regular», trace_dual(L, K, B, S)), F))",
	},
		"Boundedness is FunctionalDualBounded at the K-linear field trace (FieldTraceLinear, "+
			"TraceDualIsFunctionalDual): nondegeneracy at x = 1 gives the nonzero value, and the "+
			"denominator of the finite dual basis in Frac(B) is FiniteSpanCommonDenominator. "+
			"Integral multiplication matrices put traces of B-products in S (FieldTraceInSubring). "+
			"The common basis has a trace-dual S-basis (TraceDualFreeLattice)."),
})}

var CodifferentInvertible = codifferentInvertibleThm{family.Add(registry.ProofEntry{
	Name: "CodifferentInvertible",
	Key:  "prop_f1c768e87e942dc4",
	Deps: []registry.EntryLike{
		CodifferentBoundedFractionalIdeal,
		ideal_factorization.FractionalIdealInvertibleIffBounded,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀K S B E:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"finite_extension(L, K, L.carrier)",
			"S ⊆ K",
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"S ⊆ B",
			"finite(E)",
			"module_basis(«ScalarS», restrict_module(«Regular», B), E)",
			"module_basis(«ScalarK», «Regular», E)",
			"∀x:A. x ∈ L.carrier ∧ x ≠ L.zero ⇒ ∃y:A. y ∈ L.carrier ∧ field_trace(L, K, x * y) ≠ L.zero",
			"fraction_field_carrier(«ScalarK», S)",
			"fraction_field_carrier(field_ring(L), B)",
			"∀I:set(A). ring_ideal(«ScalarB», I) ∧ I ≠ {L.zero} ⇒ invertible_fractional(field_ring(L), B, I)",
		},
		Conclusion: "invertible_fractional(field_ring(L), B, trace_dual(L, K, B, S)) ∧ " +
			"ring_ideal(«ScalarB», fractional_inverse(field_ring(L), B, trace_dual(L, K, B, S))) ∧ " +
			"fractional_inverse(field_ring(L), B, trace_dual(L, K, B, S)) ≠ {L.zero}",
	},
		"Apply the bounded fractional ideal criterion. Since B lies in the "+
			"codifferent, its inverse lies in B and is a nonzero integral ideal."),
})}
