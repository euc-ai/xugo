// The coframe structure coefficients give the skew torsion-free connection explicitly.

package riemannian

import (
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var structureCoefficientsDef = structureCoefficientsDefThm{family.Define(registry.DefEntry{
	Name:  "structureCoefficientsDef",
	Key:   "prop_e8b36b535fc6eb4e",
	Const: "riemannian_structure_coefficients",
	Type: "num → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"(num → real) → " +
		"num → " +
		"num → " +
		"num → " +
		"real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{coframeDef},
	Reading: "The last two indices are the two ordered frame vectors fed into dθ. This fixes the " +
		"sign of the structure coefficients; all inactive indices and points outside the image give zero.",
	Equations: []string{
		"∀n:num. " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀y:(num → real). " +
			"∀a b d:num. " +
			"    riemannian_structure_coefficients⟨n⟩(g, c, E, y, a, b, d) = " +
			"    COND(a < n ∧ b < n ∧ d < n ∧ y ∈ «chart image»(c), " +
			"        vec_exterior_derivative⟨n⟩(«chart image»(c), " +
			"            1, " +
			"            riemannian_coframe⟨n⟩(g, c, E, a, 0), " +
			"            y, " +
			"            «frame pair»(y, b, d)), " +
			"        &0)",
	},
})}

var ConnectionDef = connectionDefThm{family.Define(registry.DefEntry{
	Name:  "ConnectionDef",
	Key:   "prop_63fb485a719230cb",
	Const: "riemannian_connection",
	Type: "num → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"(num → num → (num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{structureCoefficientsDef, coframeDef},
	Reading: "The coefficient of θ^d in A_ab is one half of c^a_bd + c^b_da - c^d_ab. " +
		"This sign gives dθ+A∧θ=0. The connection is a square matrix of one-forms in a positive " +
		"orthonormal frame, rather than a tensor or a chart-compatible family of scalar forms.",
	Equations: []string{
		"∀n:num. " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀a b:num. " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    riemannian_connection⟨n⟩(g, c, E, a, b, y, P) = " +
			"    COND(a < n ∧ b < n ∧ y ∈ «chart image»(c), " +
			"        (&1 / &2) * " +
			"        (Σ_{d<n} (riemannian_structure_coefficients⟨n⟩(g, c, E, y, a, b, d) + riemannian_structure_coefficients⟨n⟩(g, c, E, y, b, d, a) - riemannian_structure_coefficients⟨n⟩(g, c, E, y, d, a, b)) * " +
			"            riemannian_coframe⟨n⟩(g, c, E, d, 0, y, P)), " +
			"        &0)",
	},
})}

var frameChangeDef = frameChangeDefThm{family.Define(registry.DefEntry{
	Name:  "frameChangeDef",
	Key:   "prop_a2f859e1f6cce50f",
	Const: "riemannian_frame_change",
	Type: "num → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"((num → real) → num → num → real) → " +
		"(num → num → (num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Reading: "The zero-form matrix is H=E-transpose G F in one fixed coordinate chart, so F=E " +
		"H and the coframes obey θ_F=H-transpose θ_E. Two positive frames give determinant one on the " +
		"image. It is normalized as a whole zero-form matrix, including arbitrary form-frame arguments.",
	Equations: []string{
		"∀n:num. " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real). " +
			"∀i j:num. " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    riemannian_frame_change⟨n⟩(g, c, E, F, i, j, y, P) = " +
			"    COND(i < n ∧ j < n ∧ y ∈ «chart image»(c), " +
			"        matrix_product(real_ring, n, «dual matrix»(y), F(y), i, j), " +
			"        &0)",
	},
})}
