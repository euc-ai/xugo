// The local Euler Pfaffian extends uniquely from positive charts to a normalized manifold form.

package riemannian

import (
	_ "github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

var localEulerDef = localEulerDefThm{family.Define(registry.DefEntry{
	Name:  "localEulerDef",
	Key:   "prop_334b3b60bc0f4815",
	Const: "riemannian_local_euler_form",
	Type: "num → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"prod(set(A), A → num → real) → " +
		"((num → real) → num → num → real) → " +
		"((num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{ConnectionDef},
	Reading: "The matrix order and form degree are n. Each curvature entry is " +
		"multiplied by 1/(2π) before taking the Pfaffian. Thus order 2m contributes " +
		"(2π)^(-m), odd orders give zero, and order zero gives the normalized unit. " +
		"The frame is positive relative to its specified coordinate chart.",
	Equations: []string{
		"∀n:num. " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"    riemannian_local_euler_form⟨n⟩(g, c, E) = " +
			"    vec_form_pfaffian⟨n⟩(«chart image»(c), " +
			"        n, " +
			"        (λi:num. λj:num. λy:(num → real). λP:(num → num → real). " +
			"            (&1 / (&2 * π)) * " +
			"            vec_form_curvature⟨n⟩(«chart image»(c), n, riemannian_connection⟨n⟩(g, c, E))(i, " +
			"                j, " +
			"                y, " +
			"                P)))",
	},
})}

var eulerRepresentativeDef = eulerRepresentativeDefThm{family.Define(registry.DefEntry{
	Name:  "eulerRepresentativeDef",
	Key:   "prop_9f2214636e832e4f",
	Const: "riemannian_euler_representative",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"bool",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{MetricDef, PositiveFrameDef, localEulerDef},
	Reading: "A representative is a normalized n-form on all compatible charts " +
		"whose value on every positive chart equals the local curvature Pfaffian for " +
		"every positive frame. Incompatible charts are zero by the form predicate; " +
		"negatively oriented compatible charts are determined by overlap pullback, not " +
		"forced to zero. The predicate includes the orientation and metric assumptions.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    riemannian_euler_representative⟨n⟩(T, 𝒜, g, ω) ⇔ " +
			"    oriented_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    riemannian_metric⟨n⟩(T, 𝒜, g) ∧ " +
			"    manifold_form_on⟨n⟩(T, 𝒜, n, ω) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀E:((num → real) → num → num → real). " +
			"        positive_manifold_chart⟨n⟩(T, 𝒜, c) ∧ riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E) ⇒ " +
			"        ω(c) = riemannian_local_euler_form⟨n⟩(g, c, E))",
	},
})}

var EulerFormDef = eulerFormDefThm{family.Define(registry.DefEntry{
	Name:  "EulerFormDef",
	Key:   "prop_816da9a87927d477",
	Const: "riemannian_euler_form",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → num → num → real) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{MetricDef, eulerRepresentativeDef},
	Reading: "For an oriented Riemannian manifold this selects the unique Euler representative. " +
		"Invalid orientation or metric inputs give the zero family. The definition requires no " +
		"compactness, and uniqueness makes it independent of every local frame or extension choice.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"    riemannian_euler_form⟨n⟩(T, 𝒜, g) = " +
			"    COND(oriented_manifold⟨n⟩(T, 𝒜) ∧ riemannian_metric⟨n⟩(T, 𝒜, g), " +
			"        (εω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"            riemannian_euler_representative⟨n⟩(T, 𝒜, g, ω)), " +
			"        (λc:prod(set(A), A → num → real). «zero»))",
	},
})}
