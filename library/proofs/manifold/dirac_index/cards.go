package dirac_index

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/clifford_spin"
	"github.com/euc-ai/xugo/library/proofs/manifold/analytic_index"
	"github.com/euc-ai/xugo/library/proofs/manifold/chern_weil"
	"github.com/euc-ai/xugo/library/proofs/manifold/cohomological_index"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	"github.com/euc-ai/xugo/library/proofs/manifold/pseudo_differential"
	"github.com/euc-ai/xugo/library/proofs/manifold/spin_geometry"
	"github.com/euc-ai/xugo/library/registry"
)

var AHatSquare = aHatSquareThm{family.Add(registry.ProofEntry{
	Name: "AHatSquare",
	Key:  "prop_a3c423a80811bdd6",
	Deps: []registry.EntryLike{
		cohomological_index.TangentToddOnEmbedding,
		cohomological_index.ComplexTangent,
		manifold_embedding.CompactSmoothEmbedding,
		chern_weil.GrassmannConnection,
		chern_weil.ToddRecurrence,
		chern_weil.ToddClosed,
		de_rham.ClassMember,
		de_rham_product.WedgeUnit,
		de_rham_product.WedgeBilinear,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
		Conclusion: "a_hat_class(n, T, 𝒜, 0) = de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)) ∧ " +
			"(∀k:num. a_hat_class(n, T, 𝒜, k) ∈ (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).carrier) ∧ " +
			"(∀k:num. " +
			"    module_sum((de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).add, " +
			"        (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).zero, " +
			"        {j:num | j ≤ k}, " +
			"        λj:num. " +
			"            de_rham_wedge⟨n⟩(T, " +
			"                𝒜, " +
			"                2 * j, " +
			"                2 * (k - j), " +
			"                a_hat_class(n, T, 𝒜, j), " +
			"                a_hat_class(n, T, 𝒜, k - j))) = " +
			"    tangent_todd_class(n, T, 𝒜, k)) ∧ " +
			"(∀b:(num → set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
			"    b(0) = de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)) ∧ " +
			"    (∀k:num. b(k) ∈ (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).carrier) ∧ " +
			"    (∀k:num. " +
			"        module_sum((de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).add, " +
			"            (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).zero, " +
			"            {j:num | j ≤ k}, " +
			"            λj:num. de_rham_wedge⟨n⟩(T, 𝒜, 2 * j, 2 * (k - j), b(j), b(k - j))) = " +
			"        tangent_todd_class(n, T, 𝒜, k)) ⇒ " +
			"    b = a_hat_class(n, T, 𝒜))",
	},
		"Compactness gives a Euclidean embedding, so the tangent Todd class is the Todd class of "+
			"an embedded tangent projection: closed in every degree, with the unit in degree zero. By "+
			"the unit law the degree-k equation has leading term twice the unknown coefficient, so "+
			"strong induction solves it uniquely in each degree; the chosen class is that solution."),
})}

var DiracElliptic = diracEllipticThm{family.Add(registry.ProofEntry{
	Name: "DiracElliptic",
	Key:  "prop_304d7aab61278547",
	Deps: []registry.EntryLike{
		clifford_spin.CliffordRelation,
		spin_geometry.GradedSpinorBundles,
		spin_geometry.FrameVector,
		pseudo_differential.FirstOrderPseudoDifferential,
	},
	Build: family.Card(Statement{
		Binders: "∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀S E:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex).",
		Hypotheses: []string{
			"spinor_connection(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ)",
			"projection_connection(2 * m, T, 𝒜, E, Δ)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "pseudo_differential_operator(2 * m, " +
			"    fst(S) * fst(E), " +
			"    fst(S) * fst(E), " +
			"    T, " +
			"    𝒜, " +
			"    snd(projection_tensor(spinor_parity(m, T, L, U, S, W, 0), E)), " +
			"    snd(projection_tensor(spinor_parity(m, T, L, U, S, W, 1), E)), " +
			"    int_of_num(1), " +
			"    spin_dirac_symbol(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ, E, Δ), " +
			"    spin_dirac_operator(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ, E, Δ)) ∧ " +
			"ps_elliptic_symbol(2 * m, " +
			"    fst(S) * fst(E), " +
			"    fst(S) * fst(E), " +
			"    T, " +
			"    𝒜, " +
			"    snd(projection_tensor(spinor_parity(m, T, L, U, S, W, 0), E)), " +
			"    snd(projection_tensor(spinor_parity(m, T, L, U, S, W, 1), E)), " +
			"    int_of_num(1), " +
			"    spin_dirac_symbol(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ, E, Δ))",
	},
		"The Spin transition identity and lifted connection glue the displayed frame "+
			"formula, so in every chart it is a first-order differential operator with smooth "+
			"coefficients and symbol i c(xi sharp); the first-order criterion makes it a "+
			"pseudo-differential operator. The Clifford relation makes the symbol's square the "+
			"squared covector norm, and the connection preserves parity, so it maps even to odd."),
})}

var TwistedDiracIndex = twistedDiracIndexThm{family.Add(registry.ProofEntry{
	Name: "TwistedDiracIndex",
	Key:  "prop_e8a83b5e4b88b871",
	Deps: []registry.EntryLike{
		AHatSquare,
		DiracElliptic,
		analytic_index.OrderReduction,
		analytic_index.SymbolExtensionExists,
		analytic_index.SymbolExtensionIndependent,
		cohomological_index.AtiyahSingerCohomological,
	},
	Build: family.Card(Statement{
		Binders: "∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀S E:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀H:sobolev_localization(A). " +
			"∀s:int.",
		Hypotheses: []string{
			"spinor_connection(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ)",
			"projection_connection(2 * m, T, 𝒜, E, Δ)",
			"compact_in(T, ⋃T)",
			"sobolev_localization_on(2 * m, T, 𝒜, H)",
		},
		Conclusion: "real_of_int(ps_operator_index(2 * m, " +
			"        fst(S) * fst(E), " +
			"        fst(S) * fst(E), " +
			"        T, " +
			"        𝒜, " +
			"        snd(projection_tensor(spinor_parity(m, T, L, U, S, W, 0), E)), " +
			"        snd(projection_tensor(spinor_parity(m, T, L, U, S, W, 1), E)), " +
			"        H, " +
			"        int_of_num(1), " +
			"        s, " +
			"        spin_dirac_operator(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ, E, Δ))) = " +
			"compact_de_rham_integral(2 * m, T, 𝒜, twisted_dirac_character(m, T, 𝒜, E))",
	},
		"Order reduction gives the analytic index of this concrete elliptic symbol at every "+
			"Sobolev order, and a symbol extension puts its class in the compact K-group, where "+
			"the cohomological Atiyah–Singer formula applies. The Spin symbol-character comparison "+
			"then reduces the cotangent integral to the A-hat–Chern integral on the base."),
})}
