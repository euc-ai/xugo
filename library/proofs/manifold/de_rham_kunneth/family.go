package de_rham_kunneth

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed de_rham_kunneth.cnf.pb
var familyCNF []byte

// family reads the cover chapter's table and adds the cover of a
// product by cylinders over a two-open cover and the comparison
// statement an induction over box unions carries.
var family = registry.NewFamily("manifold/de_rham_kunneth", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(de_rham_cover.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "product intersection topology", Text: "subtopology(product_topology(T, S), " +
			"    (set_cross(U, ⋃S) ∩ set_cross(V, ⋃S)))"},
		{Name: "product intersection atlas", Text: "open_submanifold_atlas⟨n + m⟩( " +
			"    product_topology(T, S), " +
			"    smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"    (set_cross(U, ⋃S) ∩ set_cross(V, ⋃S)))"},
		{Name: "product cover exact", Text: "short_exact_cochain_complexes(real_ring, " +
			"    de_rham_complex⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ)), " +
			"    de_rham_cover_complex⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        set_cross(U, ⋃S), " +
			"        set_cross(V, ⋃S)), " +
			"    de_rham_complex⟨n + m⟩(«product intersection topology», «product intersection atlas»), " +
			"    (λj:num. " +
			"        de_rham_cover_restriction⟨n + m⟩(product_topology(T, S), " +
			"            smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"            set_cross(U, ⋃S), " +
			"            set_cross(V, ⋃S))), " +
			"    (λj:num. " +
			"        de_rham_cover_difference⟨n + m⟩(product_topology(T, S), " +
			"            smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"            set_cross(U, ⋃S), " +
			"            set_cross(V, ⋃S))))"},
		{Name: "euclidean comparison", Text: "λO:set(num → real). λj:num. " +
			"    module_isomorphism(real_ring, " +
			"        de_rham_kunneth_module⟨n⟩(subtopology(euclidean_topology(n), O), " +
			"            euclidean_atlas(O), " +
			"            j, " +
			"            E), " +
			"        de_rham_cohomology_module⟨n + m⟩( " +
			"            product_topology(subtopology(euclidean_topology(n), O), S), " +
			"            smooth_product_atlas⟨n, m⟩(euclidean_atlas(O), ℬ), " +
			"            j), " +
			"        de_rham_kunneth_map⟨n, m⟩(subtopology(euclidean_topology(n), O), " +
			"            euclidean_atlas(O), " +
			"            S, " +
			"            ℬ, " +
			"            j, " +
			"            E))"},
	})
