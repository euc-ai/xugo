// definitions.go — the quotient complex of a sub-pair M' ⊆ M: the
// connecting map δ, the difference c̄ of two chart cosets taken modulo the
// ambient of M', and the kernel of c̄ in the product of the chart quotients.

package lattice_pair_sequence

import (
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// latticePairConnectingDef — `lattice_pair_connecting(V, z)`, written δ:
// the differences x − y of a member x of fst(z) and a member y of
// snd(z). At a pair of cosets (m₀ + M'₀, m₁ + M'₁) of a sub-pair M' it is
// the coset (m₀ − m₁) + (M'₀ + M'₁): the Čech difference read on classes,
// the connecting map of the sub-pair into H¹(M').
var latticePairConnectingDef = latticePairConnectingDefThm{family.Define(registry.DefEntry{
	Name:  "latticePairConnectingDef",
	Key:   "prop_29be5e1615164904",
	Const: "lattice_pair_connecting",
	Type:  "module_ops(A, B) → prod(set(B), set(B)) → set(B)",
	Equations: []string{
		"∀V:module_ops(A, B). ∀z:prod(set(B), set(B)). " +
			"    lattice_pair_connecting(V, z) = set_mul(V.add, fst(z), set_inv(V.neg, snd(z)))",
	},
})}

// latticePairQuotientDifferenceDef — `lattice_pair_quotient_difference(R,
// V, M', z)`, written c̄: the difference map of the quotient of a lattice
// pair by its sub-pair M', a pair of cosets (m₀ + M'₀, m₁ + M'₁) to the
// class (m₀ − m₁) + ambient(M').
var latticePairQuotientDifferenceDef = latticePairQuotientDifferenceDefThm{family.Define(registry.DefEntry{
	Name:  "latticePairQuotientDifferenceDef",
	Key:   "prop_9439857cf6e0d5aa",
	Const: "lattice_pair_quotient_difference",
	Type:  "ring_ops(A) → module_ops(A, B) → prod(set(B), set(B)) → prod(set(B), set(B)) → set(B)",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M':prod(set(B), set(B)). ∀z:prod(set(B), set(B)). " +
			"    lattice_pair_quotient_difference(R, V, M', z) = " +
			"    set_mul(V.add, lattice_pair_connecting(V, z), lattice_pair_ambient(R, V, M'))",
	},
	Deps: []registry.EntryLike{latticePairConnectingDef},
})}

// LatticePairQuotientKernelDef — `lattice_pair_quotient_kernel(R, V, M,
// M')`, written ker c̄: the pairs of a coset of M'₀ in M₀ and a coset of
// M'₁ in M₁ that c̄ sends to zero, as a submodule of the product of the
// two chart quotients.
var LatticePairQuotientKernelDef = latticePairQuotientKernelDefThm{family.Define(registry.DefEntry{
	Name:  "LatticePairQuotientKernelDef",
	Key:   "prop_8733a01af458b377",
	Const: "lattice_pair_quotient_kernel",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"prod(set(B), set(B)) → " +
		"prod(set(B), set(B)) → " +
		"module_ops(A, prod(set(B), set(B)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M M':prod(set(B), set(B)). " +
			"    lattice_pair_quotient_kernel(R, V, M, M') = " +
			"    restrict_module(product_module(quotient_module(restrict_module(V, fst(M)), fst(M')), " +
			"            quotient_module(restrict_module(V, snd(M)), snd(M'))), " +
			"        group_kernel(lattice_pair_ambient(R, V, M'), " +
			"            set_cross(left_cosets(V.add, fst(M), fst(M')), " +
			"                left_cosets(V.add, snd(M), snd(M'))), " +
			"            lattice_pair_quotient_difference(R, V, M')))",
	},
	Deps: []registry.EntryLike{latticePairQuotientDifferenceDef},
})}
