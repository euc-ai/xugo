// definitions.go — the two maps of the duality between H¹ of a lattice
// pair on the line and its maps into O(−2): the coefficient of t⁻¹, and the
// map a functional on H¹ induces.

package projective_line_duality

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

// ProjectiveLineDualityMapDef — `projective_line_duality_map(L, k, t, V,
// M, φ, X)`: the value at a class X of H¹(M) of the functional a map
// φ : M → O(−2) induces — the coefficient of t⁻¹ in φ at a member of X,
// zero where X is no class.
var ProjectiveLineDualityMapDef = projectiveLineDualityMapDefThm{family.Define(registry.DefEntry{
	Name:  "ProjectiveLineDualityMapDef",
	Key:   "prop_666455712af72482",
	Const: "projective_line_duality_map",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"A → " +
		"module_ops(A, B) → " +
		"prod(set(B), set(B)) → " +
		"(B → A) → " +
		"set(B) → " +
		"A",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀φ:(B → A). " +
			"∀X:set(B). " +
			"    projective_line_duality_map(F, k, t, V, M, φ, X) = " +
			"    COND(X ∈ " +
			"        lattice_pair_h1(restrict_ring(field_ring(F), " +
			"                ring_away(field_ring(F), polynomial_image(field_ring(F), k, t), t)), " +
			"            V, " +
			"            M).carrier, " +
			"        laurent_polynomial_coefficient(F.add, " +
			"            F.zero, " +
			"            F.mul, " +
			"            F.one, " +
			"            F.inv, " +
			"            k, " +
			"            t, " +
			"            φ(εx:B. x ∈ X), " +
			"            -&1), " +
			"        F.zero)",
	},
	Deps: []registry.EntryLike{},
})}

// projectiveLineDualityInverseDef — `projective_line_duality_inverse(L,
// k, t, V, M, u, x)`: the value at x of the map M → O(−2) a functional u
// on H¹(M) induces, Σ u([t^(−m−1) · x]) · tᵐ over the integers m where
// the term is not zero, on the ambient of M and zero off it. The shift is
// −m − 1 because t^(−m−1) moves tᵐ to t⁻¹, the power the functional of a
// map reads, so the map of u is built to have u as its functional.
var projectiveLineDualityInverseDef = projectiveLineDualityInverseDefThm{family.Define(registry.DefEntry{
	Name:  "projectiveLineDualityInverseDef",
	Key:   "prop_d5de045ff4b05e59",
	Const: "projective_line_duality_inverse",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"A → " +
		"module_ops(A, B) → " +
		"prod(set(B), set(B)) → " +
		"(set(B) → A) → " +
		"B → " +
		"A",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)). " +
			"∀u:(set(B) → A). " +
			"∀x:B. " +
			"    projective_line_duality_inverse(F, k, t, V, M, u, x) = " +
			"    COND(x ∈ " +
			"        lattice_pair_ambient(restrict_ring(field_ring(F), " +
			"                ring_away(field_ring(F), polynomial_image(field_ring(F), k, t), t)), " +
			"            V, " +
			"            M), " +
			"        module_sum(F.add, " +
			"            F.zero, " +
			"            fun_support(F.zero, " +
			"                λm:int. " +
			"                    u(left_coset(V.add, " +
			"                            V.smul(laurent_monomial(F.mul, F.one, F.inv, t, -m - &1), x), " +
			"                            set_mul(V.add, fst(M), snd(M))))), " +
			"            λm:int. " +
			"                F.mul(u(left_coset(V.add, " +
			"                            V.smul(laurent_monomial(F.mul, F.one, F.inv, t, -m - &1), x), " +
			"                            set_mul(V.add, fst(M), snd(M)))), " +
			"                    laurent_monomial(F.mul, F.one, F.inv, t, m))), " +
			"        F.zero)",
	},
	Deps: []registry.EntryLike{},
})}
