package chern_thom

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/chern_weil"
	"github.com/euc-ai/xugo/library/proofs/manifold/compact_chern"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_thom"
	"github.com/euc-ai/xugo/library/proofs/manifold/projective_bundle"
	"github.com/euc-ai/xugo/library/proofs/topology/k_thom"
	"github.com/euc-ai/xugo/library/registry"
)

var InverseTodd = inverseToddThm{family.Add(registry.ProofEntry{
	Name: "InverseTodd",
	Key:  "prop_4281b43c95f60c13",
	Deps: []registry.EntryLike{chern_weil.ToddSeries},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))"},
		Conclusion: "(∀k:num. " +
			"    inverse_todd_class(n, T, 𝒜, P, k) ∈ " +
			"    (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).carrier) ∧ " +
			"(∀k:num. " +
			"    module_sum((de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).add, " +
			"        (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).zero, " +
			"        {j:num | j ≤ k}, " +
			"        λj:num. " +
			"            de_rham_wedge⟨n⟩(T, " +
			"                𝒜, " +
			"                2 * j, " +
			"                2 * (k - j), " +
			"                todd_class(n, T, 𝒜, P, j), " +
			"                inverse_todd_class(n, T, 𝒜, P, k - j))) = " +
			"    COND(k = 0, " +
			"        de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)), " +
			"        (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).zero))",
	},
		"Todd has constant component one. Degree induction uniquely solves "+
			"the finite convolution inverse in the graded de Rham algebra."),
})}

var LineKoszulCharacter = lineKoszulCharacterThm{family.Add(registry.ProofEntry{
	Name: "LineKoszulCharacter",
	Key:  "prop_e09162ecbfe2baf",
	Deps: []registry.EntryLike{
		InverseTodd,
		compact_chern.CharacterOnTriple,
		de_rham_thom.FiberProjectionFormula,
		k_thom.ThomMapDescends,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"r = 1",
			"a ∈ (kc_group(T)).carrier",
		},
		Conclusion: "compact_chern_class(n + 2 * r, " +
			"    projection_total_topology(T, P), " +
			"    projection_total_atlas(n, r, T, 𝒜, P), " +
			"    kc_thom_map(T, P, a), " +
			"    k + r) = " +
			"(compact_de_rham_module(n + 2 * r, " +
			"        projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        2 * (k + r))).smul(real_pow(-&1, r), " +
			"    compact_de_rham_thom(n, r, T, 𝒜, P, 2 * k, thom_corrected_character(n, T, 𝒜, P, a, k)))",
	},
		"On the punctured line choose angular eta with fibre integral one and d eta=-pi*x. For a "+
			"radial cutoff chi from zero to one, the adapted target normalized curvature is "+
			"(1-chi)pi*x+d chi wedge eta. Integrating 1-exp(curvature) gives -sum x^j/(j+1)!, hence "+
			"-Td(L*) inverse. Multiply by the pulled-back compact character to control total support."),
})}

var ChernThom = chernThomThm{family.Add(registry.ProofEntry{
	Name: "ChernThom",
	Reading: "The input is a compactly supported K class. On a noncompact base the bare Koszul " +
		"triple is only fibre-supported, whereas its product with this input has compact total support.",
	Key: "prop_bc052e330677ed37",
	Deps: []registry.EntryLike{
		LineKoszulCharacter,
		InverseTodd,
		projective_bundle.CompactPullbackInjective,
		projective_bundle.TautologicalSplitting,
		chern_weil.ChernTensor,
		chern_weil.ToddDirectSum,
		de_rham_thom.ThomFormIndependent,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"a ∈ (kc_group(T)).carrier",
		},
		Conclusion: "compact_chern_class(n + 2 * r, " +
			"    projection_total_topology(T, P), " +
			"    projection_total_atlas(n, r, T, 𝒜, P), " +
			"    kc_thom_map(T, P, a), " +
			"    k + r) = " +
			"(compact_de_rham_module(n + 2 * r, " +
			"        projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        2 * (k + r))).smul(real_pow(-&1, r), " +
			"    compact_de_rham_thom(n, r, T, 𝒜, P, 2 * k, thom_corrected_character(n, T, 𝒜, P, a, k)))",
	},
		"Rank zero is the unit. For positive rank pull back to the projective bundle, split "+
			"off its tautological line, and use the line calculation with the lower-rank "+
			"induction. The character product and fibre-integration base-change formulas identify "+
			"the pullbacks; proper projective pullback injectivity descends the equality."),
})}
