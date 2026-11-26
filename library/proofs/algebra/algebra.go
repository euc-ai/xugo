// Package algebra is the aggregator for the abstract algebraic
// structures: a structure is a predicate over its explicit components
// on a free carrier (registry.DefineStructure), its laws are theorems
// with the predicate as antecedent (Structure.Law), and an instance is
// a theorem of a chapter of the carrier. Concrete number carriers read
// the abstract structures through instances.
//
// The domain is laid out by KIND, one directory per kind and one
// family per structure, so that a tower of structures reads as a
// tower of packages: group/ holds the group-like structures
// (comm_monoid, group, abelian_group, and the symmetric groups as the
// first non-commutative instance), ring/ the ring-like ones (comm_ring,
// integral_domain), module/ modules over a ring and homological algebra,
// field/ the field structure and field theory inside one field,
// cotangent/ the cotangent complex of a ring map. Polish groups read
// topology; polish_cohomology equips existing
// quotient cohomology with Polish covers and regular maps. definable_ext
// and definable_andre_quillen supply the countable models that enter this mechanism.
// borel_subgroup reads Baire category into a Polish group: a Borel subgroup
// has countable index or continuum many cosets, which polish_cohomology
// reads at the coboundaries. derived_limit and milnor_sequence are the
// towers: lim and lim¹ as a two-term Polish complex, and the Milnor
// sequence of a tower of complexes. dyadic_integers is their worked
// example: the 2-adic integers from compatible residues, and lim¹ of the
// integers under doubling as ℤ₂/ℤ.
// A structure's definition is a conjunction of its sub-structures'
// predicates plus its own axioms, so inheritance is a projection and
// the package import graph is the structure tower itself.
package algebra

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/clifford_spin"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_andre_quillen"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_deformation"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/exterior_basis"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/borel_subgroup"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/twisted_counting"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/definable_ext"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/derived_limit"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/dyadic_integers"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/filtered_space"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_determinant"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_pairing"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/milnor_sequence"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/scalar_extension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/good_localization"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_class_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/signed_ideal_power"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/subring_localization"
)
