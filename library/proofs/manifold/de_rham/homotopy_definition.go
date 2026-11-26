// Time contraction in a paired cylinder chart defines the degree-lowering homotopy operator.

package de_rham

import (
	"github.com/euc-ai/xugo/library/registry"
)

var HomotopyDef = homotopyDefThm{family.Define(registry.DefEntry{
	Name:  "HomotopyDef",
	Key:   "prop_6f728ac8d7c4aa1f",
	Const: "manifold_form_homotopy",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(num → real) → " +
		"num → " +
		"(prod(set(prod(A, num → real)), prod(A, num → real) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Reading: "The argument k is the output degree; input forms have degree k+1 on M " +
		"times the open time set J. Time is the last coordinate and the first inserted " +
		"column, inheriting dK+Kd = j1* - j0* from the Euclidean operator. Degree-zero " +
		"input has a separate formula and the operator is normalized at invalid base charts.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀J:set(num → real). " +
			"∀ω:(prod(set(prod(A, num → real)), prod(A, num → real) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"∀c:prod(set(A), A → num → real). " +
			"    manifold_form_homotopy⟨n⟩(T, 𝒜, J, k, ω)(c) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c), " +
			"        vec_form_homotopy⟨n⟩(«chart image»(c), k, ω(«cylinder chart»(c))), " +
			"        «zero»)",
	},
})}
