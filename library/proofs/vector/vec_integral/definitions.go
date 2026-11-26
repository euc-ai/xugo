// definitions.go — the integral of a real function over ℝⁿ, one
// coordinate at a time.

package vec_integral

import (
	_ "github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_integral"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// VecIntegralDef — `vec_integral⟨n⟩(g)`: the integral of g over ℝⁿ, the
// iterated Lebesgue integral over the coordinates, the last one
// outermost. Over ℝ⁰ = {0} it is the value at the zero vector; over ℝⁿ⁺¹
// it integrates over t the integral over ℝⁿ of the slice x ↦ g(x, t), t
// put at coordinate n.
var VecIntegralDef = vecIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "VecIntegralDef",
	Key:   "prop_25a5fde8cd7c3abe",
	Const: "vec_integral",
	Type:  "num → ((num → real) → real) → real",
	Dim:   "n",
	Equations: []string{
		"∀n:num. ∀g:((num → real) → real). " +
			"    vec_integral⟨suc(n)⟩(g) = " +
			"    lebesgue_integral(λt:real. vec_integral⟨n⟩(λx:(num → real). g(«append»(x, t))))",
		"∀g:((num → real) → real). vec_integral⟨0⟩(g) = g(vec_zero)",
	},
	Reading: "g is evaluated only at n-vectors, the zero vector with coordinates put at 0, " +
		"1, …, n − 1. For a g continuous with compact support, the functions of the chapter, " +
		"every slice integral is continuous with compact support and the iterated integral is " +
		"the integral; for others it is whatever lebesgue_integral returns, a number all the same.",
})}
