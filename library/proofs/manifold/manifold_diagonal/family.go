package manifold_diagonal

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed manifold_diagonal.cnf.pb
var familyCNF []byte

// family reads the tangent chapter's table and adds the notation of a
// diagonal neighbourhood: the embedded tangent disks with their
// topology and atlas, the open target in the product, the coordinate
// fiber disks and maps, and the open time strip of the homotopy.
var family = registry.NewFamily("manifold/manifold_diagonal", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(tangent.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "diagonal fiber disk", Text: "λe:prod(set(A), A → num → real). " +
			"    embedded_tangent_fiber_disk⟨n, N⟩(T, 𝒜, i, e, x, δ)"},
		{Name: "diagonal fiber map", Text: "λe:prod(set(A), A → num → real). " +
			"    diagonal_fiber_map⟨n, N⟩(T, 𝒜, i, r, e, x)"},
		{Name: "diagonal slice", Text: "λa:A. λQ:set(prod(A, A)). {b:A | b ∈ ⋃T ∧ (a, b) ∈ Q}"},
		{Name: "disk topology", Text: "λa:real. " +
			"    subtopology(tangent_topology⟨n⟩(T, 𝒜), embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, a))"},
		{Name: "disk atlas", Text: "λa:real. " +
			"    open_submanifold_atlas⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
			"        tangent_atlas⟨n⟩(T, 𝒜), " +
			"        embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, a))"},
		{Name: "diagonal target topology", Text: "λQ:set(prod(A, A)). " +
			"    subtopology(product_topology(T, T), Q)"},
		{Name: "diagonal target atlas", Text: "λQ:set(prod(A, A)). " +
			"    open_submanifold_atlas⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), Q)"},
		{Name: "diagonal time strip", Text: "{τ:num → real | vec⟨1⟩(τ) ∧ -&1 < τ(0) ∧ τ(0) < &2}"},
		{Name: "inverse disk point", Text: "λw:prod(A, A). " +
			"    inverse_on(embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ), " +
			"        diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r), " +
			"        w)"},
	})
