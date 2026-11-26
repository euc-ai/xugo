// The overlap transition compares two orthonormal frames through the coordinate Jacobian.

package riemannian

import (
	"github.com/euc-ai/xugo/library/registry"
)

var chartFrameChangeDef = chartFrameChangeDefThm{family.Define(registry.DefEntry{
	Name:  "chartFrameChangeDef",
	Key:   "prop_a159603ef691afed",
	Const: "riemannian_chart_frame_change",
	Type: "num → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"((num → real) → num → num → real) → " +
		"(num → num → (num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Reading: "On the source overlap H=(J E)-transpose G_d F, with target fields " +
		"evaluated at the transition image. Thus F=J E H and the pulled-back target coframe " +
		"is H-transpose times the source coframe. The zero-form matrix is normalized on the " +
		"overlap, not on either whole chart image. Arbitrary compatible charts give an " +
		"orthogonal H; determinant one additionally needs positive coordinate transition.",
	Equations: []string{
		"∀n:num. " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c d:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real). " +
			"∀i j:num. " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    riemannian_chart_frame_change⟨n⟩(g, c, d, E, F, i, j, y, P) = " +
			"    COND(i < n ∧ j < n ∧ y ∈ «overlap»(c, d), " +
			"        matrix_product(real_ring, " +
			"            n, " +
			"            transpose(matrix_product(real_ring, " +
			"                    n, " +
			"                    vec_jacobian_matrix⟨n, n⟩(«transition»(c, d), y), " +
			"                    E(y))), " +
			"            matrix_product(real_ring, " +
			"                n, " +
			"                g(d, «transition»(c, d)(y)), " +
			"                F(«transition»(c, d)(y))), " +
			"            i, " +
			"            j), " +
			"        &0)",
	},
})}
