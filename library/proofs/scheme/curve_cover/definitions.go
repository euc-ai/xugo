// definitions.go — the chapter's definitions statements.

package curve_cover

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/trace_dual"
	"github.com/euc-ai/xugo/library/registry"
)

// CurveCoverDef — A finite free separable covering of two curves over the same line.
var CurveCoverDef = curveCoverDefThm{family.Define(registry.DefEntry{
	Name:  "CurveCoverDef",
	Key:   "prop_6ea352361bb6b605",
	Const: "curve_cover",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"A → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"bool",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "The two curves use the same transcendental coordinate t and constants k. The " +
		"primitive element belongs to the function field only: requiring it on both charts would " +
		"put it in B₀∩B₁=k and force degree one. Dualizing invertibility is not part of a cover.",
	Equations: []string{
		"∀F:field_ops(A). " +
			"∀K:set(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀A₀:set(A). " +
			"∀A₁:set(A). " +
			"∀A₀₁:set(A). " +
			"∀B₀:set(A). " +
			"∀B₁:set(A). " +
			"∀B₀₁:set(A). " +
			"    curve_cover(F, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁) ⇔ " +
			"    subfield(F, K) ∧ " +
			"    curve_over_line(restrict_field(F, K), k, t, A₀, A₁, A₀₁) ∧ " +
			"    curve_over_line(F, k, t, B₀, B₁, B₀₁) ∧ " +
			"    A₀ ⊆ B₀ ∧ " +
			"    A₁ ⊆ B₁ ∧ " +
			"    A₀₁ ⊆ B₀₁ ∧ " +
			"    (∃E₀ E₁:set(A). " +
			"        finite(E₀) ∧ " +
			"        module_basis(restrict_ring(field_ring(F), A₀), " +
			"            restrict_module(regular_module(field_ring(F)), B₀), " +
			"            E₀) ∧ " +
			"        module_basis(restrict_ring(field_ring(F), K), regular_module(field_ring(F)), E₀) ∧ " +
			"        finite(E₁) ∧ " +
			"        module_basis(restrict_ring(field_ring(F), A₁), " +
			"            restrict_module(regular_module(field_ring(F)), B₁), " +
			"            E₁) ∧ " +
			"        module_basis(restrict_ring(field_ring(F), K), regular_module(field_ring(F)), E₁)) ∧ " +
			"    (∃y:A. " +
			"        subfield(F, K) ∧ " +
			"        y ∈ F.carrier ∧ " +
			"        algebraic_over(F, K, y) ∧ " +
			"        field_adjoin(F, K, {y}) = F.carrier ∧ " +
			"        polynomial_separable(restrict_ring(field_ring(F), K), minimal_polynomial(F, K, y)))",
	},
})}

// CoverDegreeDef — The degree of the function-field extension.
var CoverDegreeDef = coverDegreeDefThm{family.Define(registry.DefEntry{
	Name:     "CoverDegreeDef",
	Key:      "prop_7822b8dddcd8b64",
	Const:    "cover_degree",
	Type:     "ring_ops(A) → set(A) → num",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀K:set(A). " +
			"    cover_degree(R, K) = module_dim(restrict_ring(R, K), regular_module(R))",
	},
})}

// CoverPullbackDef — Scalar extension of both chart modules to the source curve.
var CoverPullbackDef = coverPullbackDefThm{family.Define(registry.DefEntry{
	Name:     "CoverPullbackDef",
	Key:      "prop_307585090843602c",
	Const:    "cover_pullback",
	Type:     "ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀B₀:set(A). ∀B₁:set(A). ∀M:prod(set(A), set(A)). " +
			"    cover_pullback(R, B₀, B₁, M) = " +
			"    (fractional_mul(R, B₀, fst(M), B₀), fractional_mul(R, B₁, snd(M), B₁))",
	},
})}

// coverPullbackAmbientDef — Scalar extension of an overlap module.
var coverPullbackAmbientDef = coverPullbackAmbientDefThm{family.Define(registry.DefEntry{
	Name:     "coverPullbackAmbientDef",
	Key:      "prop_214488cb185693b3",
	Const:    "cover_pullback_ambient",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A)",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀B:set(A). ∀N:set(A). " +
			"    cover_pullback_ambient(R, B, N) = fractional_mul(R, B, N, B)",
	},
})}

// InverseDifferentDef — The pair of trace-dual chart rings.
var InverseDifferentDef = inverseDifferentDefThm{family.Define(registry.DefEntry{
	Name:     "InverseDifferentDef",
	Key:      "prop_78156fede3680bb5",
	Const:    "inverse_different",
	Type:     "field_ops(A) → set(A) → set(A) → set(A) → set(A) → set(A) → prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Deps:     []registry.EntryLike{},
	Equations: []string{
		"∀F:field_ops(A). ∀K:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀B₀:set(A). ∀B₁:set(A). " +
			"    inverse_different(F, K, A₀, A₁, B₀, B₁) = " +
			"    (trace_dual(F, K, B₀, A₀), trace_dual(F, K, B₁, A₁))",
	},
})}

// DifferentDef — The inverse lattice pair of the inverse different.
var DifferentDef = differentDefThm{family.Define(registry.DefEntry{
	Name:     "DifferentDef",
	Key:      "prop_ba8a7dea66c84c42",
	Const:    "cover_different",
	Type:     "field_ops(A) → set(A) → set(A) → set(A) → set(A) → set(A) → prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Deps:     []registry.EntryLike{InverseDifferentDef},
	Equations: []string{
		"∀F:field_ops(A). ∀K:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀B₀:set(A). ∀B₁:set(A). " +
			"    cover_different(F, K, A₀, A₁, B₀, B₁) = " +
			"    lattice_pair_inverse(field_ring(F), B₀, B₁, inverse_different(F, K, A₀, A₁, B₀, B₁))",
	},
})}

// coverHomPairDef — The chartwise relative Hom conditions in an overlap coextension.
var coverHomPairDef = coverHomPairDefThm{family.Define(registry.DefEntry{
	Name:  "coverHomPairDef",
	Key:   "prop_a3cf608300495073",
	Const: "cover_hom_pair",
	Type: "ring_ops(A) → " +
		"ring_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"module_ops(A, B) → " +
		"prod(set(B), set(B)) → " +
		"prod(set(A → B), set(A → B))",
	Reading: "These are chartwise Hom conditions inside one coextension on the overlap. " +
		"lattice_pair_maps is instead the set of global maps and cannot be used as this pair constructor.",
	Equations: []string{
		"∀R T:ring_ops(A). ∀B₀ B₁:set(A). ∀V:module_ops(A, B). ∀N:prod(set(B), set(B)). " +
			"    cover_hom_pair(R, T, B₀, B₁, V, N) = " +
			"    ({φ:(A → B) | " +
			"            φ ∈ " +
			"            coextend_scalars(R, " +
			"                T, " +
			"                λa:A. a, " +
			"                restrict_module(V, lattice_pair_ambient(R, V, N))).carrier ∧ " +
			"            image(φ, B₀) ⊆ fst(N)}, " +
			"        {φ:(A → B) | " +
			"            φ ∈ " +
			"            coextend_scalars(R, " +
			"                T, " +
			"                λa:A. a, " +
			"                restrict_module(V, lattice_pair_ambient(R, V, N))).carrier ∧ " +
			"            image(φ, B₁) ⊆ snd(N)})",
	},
})}

// RamificationDegreeDef — The degree of the inverse-different lattice pair.
var RamificationDegreeDef = ramificationDegreeDefThm{family.Define(registry.DefEntry{
	Name:  "RamificationDegreeDef",
	Key:   "prop_691b501518ec0ad5",
	Const: "ramification_degree",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"int",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "Ramification is measured by the inverse-different pair and its integer " +
		"degree. No curve_divisor supported on rational regular points is asserted to represent it.",
	Deps: []registry.EntryLike{InverseDifferentDef},
	Equations: []string{
		"∀F:field_ops(A). " +
			"∀K:set(A). " +
			"∀k:set(A). " +
			"∀A₀:set(A). " +
			"∀A₁:set(A). " +
			"∀A₀₁:set(A). " +
			"∀B₀:set(A). " +
			"∀B₁:set(A). " +
			"∀B₀₁:set(A). " +
			"    ramification_degree(F, K, k, A₀, A₁, A₀₁, B₀, B₁, B₀₁) = " +
			"    curve_degree(field_ring(F), k, B₀, B₁, B₀₁, inverse_different(F, K, A₀, A₁, B₀, B₁))",
	},
})}

// riemannHurwitzDataDef — A covering with invertible dualizing models on both curves.
var riemannHurwitzDataDef = riemannHurwitzDataDefThm{family.Define(registry.DefEntry{
	Name:  "riemannHurwitzDataDef",
	Key:   "prop_ed6e52d40ad49904",
	Const: "riemann_hurwitz_data",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"A → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"bool",
	Implicit: []string{},
	Bundles:  []string{},
	Deps:     []registry.EntryLike{CurveCoverDef},
	Equations: []string{
		"∀F:field_ops(A). " +
			"∀K:set(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀A₀:set(A). " +
			"∀A₁:set(A). " +
			"∀A₀₁:set(A). " +
			"∀B₀:set(A). " +
			"∀B₁:set(A). " +
			"∀B₀₁:set(A). " +
			"    riemann_hurwitz_data(F, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁) ⇔ " +
			"    curve_cover(F, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁) ∧ " +
			"    dualizing_invertible(restrict_field(F, K), k, t, A₀, A₁, A₀₁) ∧ " +
			"    dualizing_invertible(F, k, t, B₀, B₁, B₀₁)",
	},
})}

// MonicCoverDef — Two exact monic chart presentations with their own separable generators.
var MonicCoverDef = monicCoverDefThm{family.Define(registry.DefEntry{
	Name:  "MonicCoverDef",
	Key:   "prop_59b5d995b07707e4",
	Const: "monic_cover",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"A → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"A → " +
		"A → " +
		"(num → A) → " +
		"(num → A) → " +
		"bool",
	Implicit: []string{},
	Bundles:  []string{},
	Reading: "The two generators may differ. Exact evaluation kernels are load-bearing: " +
		"merely F(y)=0, monicity and F′(y)≠0 allow an extraneous factor and do not give a " +
		"quotient presentation. A monic cover does not assume curve_cover or its basis data.",
	Equations: []string{
		"∀F:field_ops(A). " +
			"∀K:set(A). " +
			"∀k:set(A). " +
			"∀t:A. " +
			"∀A₀:set(A). " +
			"∀A₁:set(A). " +
			"∀A₀₁:set(A). " +
			"∀B₀:set(A). " +
			"∀B₁:set(A). " +
			"∀B₀₁:set(A). " +
			"∀y₀:A. " +
			"∀y₁:A. " +
			"∀F₀:(num → A). " +
			"∀F₁:(num → A). " +
			"    monic_cover(F, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁, y₀, y₁, F₀, F₁) ⇔ " +
			"    subfield(F, K) ∧ " +
			"    curve_over_line(restrict_field(F, K), k, t, A₀, A₁, A₀₁) ∧ " +
			"    curve_over_line(F, k, t, B₀, B₁, B₀₁) ∧ " +
			"    A₀ ⊆ B₀ ∧ " +
			"    A₁ ⊆ B₁ ∧ " +
			"    A₀₁ ⊆ B₀₁ ∧ " +
			"    y₀ ∈ F.carrier ∧ " +
			"    polynomial_over(F.zero, A₀, F₀) ∧ " +
			"    polynomial_monic(F.zero, F.one, F₀) ∧ " +
			"    0 < polynomial_degree(F.zero, F₀) ∧ " +
			"    polynomial_eval(F.add, F.zero, F.mul, F.one, F₀, y₀) = F.zero ∧ " +
			"    polynomial_eval(F.add, " +
			"        F.zero, " +
			"        F.mul, " +
			"        F.one, " +
			"        polynomial_derivative(F.add, F.zero, F.mul, F.one, F₀), " +
			"        y₀) ≠ " +
			"    F.zero ∧ " +
			"    B₀ = polynomial_image(field_ring(F), A₀, y₀) ∧ " +
			"    (∀p:(num → A). " +
			"        polynomial_over(F.zero, A₀, p) ⇒ " +
			"        (polynomial_eval(F.add, F.zero, F.mul, F.one, p, y₀) = F.zero ⇔ " +
			"            polynomial_divides(restrict_ring(field_ring(F), A₀), F₀, p))) ∧ " +
			"    y₁ ∈ F.carrier ∧ " +
			"    polynomial_over(F.zero, A₁, F₁) ∧ " +
			"    polynomial_monic(F.zero, F.one, F₁) ∧ " +
			"    0 < polynomial_degree(F.zero, F₁) ∧ " +
			"    polynomial_eval(F.add, F.zero, F.mul, F.one, F₁, y₁) = F.zero ∧ " +
			"    polynomial_eval(F.add, " +
			"        F.zero, " +
			"        F.mul, " +
			"        F.one, " +
			"        polynomial_derivative(F.add, F.zero, F.mul, F.one, F₁), " +
			"        y₁) ≠ " +
			"    F.zero ∧ " +
			"    B₁ = polynomial_image(field_ring(F), A₁, y₁) ∧ " +
			"    (∀p:(num → A). " +
			"        polynomial_over(F.zero, A₁, p) ⇒ " +
			"        (polynomial_eval(F.add, F.zero, F.mul, F.one, p, y₁) = F.zero ⇔ " +
			"            polynomial_divides(restrict_ring(field_ring(F), A₁), F₁, p)))",
	},
})}
