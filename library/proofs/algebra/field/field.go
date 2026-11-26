// Package field is the aggregator for the field structure, the family
// field/field, and for field theory inside one field on a set: the
// extensions of a subfield and their degree, the algebraic
// elements and their minimal polynomials, finite-extension trace and its
// nondegenerate separable pairing, the norm, the lattice duals and
// codifferents, the automorphisms fixing a subfield,
// the Galois correspondence, the algebraic closure and the splitting
// fields inside it, finite fields with Frobenius and finite linear
// counting, the integer orders of powers and of finite sums, and the
// number fields with their rings of integers, ideals and class numbers. Subfields and automorphism groups remain subsets of
// a fixed carrier or its functions; the one field built in another type
// is the algebraic closure, in a host type fixed by the base field's.
// The trace proof also uses the ordinary polynomial quotient, a set of
// cosets of one polynomial carrier; none of these constructions mints a
// type. Each is one family, the number fields nine of them under
// number_field/.
//
// The ordered fields are here as well: orderings and the sums of squares
// that bound them, order extension, the real closure, and the real
// closed fields, defined by polynomial intermediate values. First-order
// field transfer reads formulas over a ring and over an ordered ring at
// an explicit field carrier: the syntax is integer polynomial while the
// models keep arbitrary carrier types, and the syntax, the coefficient
// encoding and the composition of quantifier elimination are shared.
// Algebraically closed fields and real closed fields have independent
// elimination cores, the real closed one built on sign tables of
// polynomial lists, uniform in the parameters. Their customers are
// Lefschetz's principle, Ax–Grothendieck, the descent of polynomial
// systems along algebraically closed embeddings, polynomial extrema and
// Brouwer's fixed point over a real closed field, and Artin's theorem
// that a nonnegative polynomial is a sum of squares of rational
// functions.
package field

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraically_closed_field_transfer"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraically_closed_quantifier_elimination"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/artin"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ax_grothendieck"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/constant_splitting"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field_norm"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field_ordering"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/functional_dual"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/gauss_sum"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/lefschetz"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/multivariate_rational_function"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/class_number"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/different"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/discriminant"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ideal_norm"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/lattice_determinant"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/number_ideals"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field_polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_ring_formula"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_ring_formula_combinators"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/parametric_sign_table"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/perfect_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_brouwer"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_optimization"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_quotient"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_sign_table"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_system_descent"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/rational_function_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/rational_point_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field_transfer"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_quantifier_elimination"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/real_closure"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/residue_points"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ring_formula_combinators"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/roots_of_unity"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/semialgebraic_properties"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/separating_parameter"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/trace_dual"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/uniform_sign_table"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/valuation_order"
)
