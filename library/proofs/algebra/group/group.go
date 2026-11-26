// Package group is the aggregator for the group-like structures: the
// commutative monoid (one operation and its identity), the group (an
// associative operation with an identity and inverses), the abelian
// group (a group whose operation commutes), the homomorphisms between
// groups (a map that respects the operation, with its kernel, normal in
// the source, and its image), the quotient groups (the cosets of a
// normal subgroup as a group on a set), the isomorphism theorems and
// the butterfly lemma for groups on sets, the composition series with
// Schreier's and the Jordan–Hölder theorems, the finite groups (their
// order, Lagrange's theorem and p-groups, with the Sylow theorems beside
// them), the symmetric groups (the permutations of a type, the first
// group that does not commute), and the free groups (the words over an
// alphabet modulo cancellation). Each is one family.
package group

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/cyclic_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/sylow"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/free_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group_action"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/primitive_root"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/subnormal_series"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/units_mod"
)
