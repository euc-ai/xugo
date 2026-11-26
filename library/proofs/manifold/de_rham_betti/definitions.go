// Betti numbers and their signed finite sum use the existing cohomology dimensions.

package de_rham_betti

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/registry"
)

var BettiDef = bettiDefThm{family.Define(registry.DefEntry{
	Name:       "BettiDef",
	Key:        "prop_8f88e6363e2b0873",
	Const:      "de_rham_betti",
	Type:       "num → set(set(A)) → set(prod(set(A), A → num → real)) → num → num",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{},
	Reading: "This natural number is the dimension of degree-k cohomology when " +
		"that module has a finite basis. On a module with no finite basis, module_dim is " +
		"one fixed unknown number, the same for every such module; an equation of Betti " +
		"numbers says something about dimension only beside a finiteness hypothesis.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num. " +
			"    de_rham_betti⟨n⟩(T, 𝒜, k) = module_dim(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k))",
	},
})}

var EulerDef = eulerDefThm{family.Define(registry.DefEntry{
	Name:       "EulerDef",
	Key:        "prop_7f6bc084252b349c",
	Const:      "de_rham_euler",
	Type:       "num → set(set(A)) → set(prod(set(A), A → num → real)) → real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{BettiDef},
	Reading: "The sum includes degree zero and degree n. Its real value is integer-valued " +
		"and can be compared directly with form integrals. Its interpretation as the ordinary de " +
		"Rham Euler characteristic requires finite-dimensional cohomology in every degree, supplied " +
		"by compactness for compact manifolds. It is not a compact-support Euler characteristic.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    de_rham_euler⟨n⟩(T, 𝒜) = " +
			"    real_sum({q:num | q ≤ n}, λq:num. (-&1) ^ q * &de_rham_betti⟨n⟩(T, 𝒜, q))",
	},
})}
