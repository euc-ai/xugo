package thom_form

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_betti"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_kunneth"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_diagonal"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/riemannian"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed thom_form.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/thom_form", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "punctured topology",

			Text: "subtopology(tangent_topology⟨n⟩(T, 𝒜), tangent_punctured⟨n⟩(T, 𝒜))"},
		{Name: "punctured atlas",

			Text: "open_submanifold_atlas⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
				"    tangent_atlas⟨n⟩(T, 𝒜), " +
				"    tangent_punctured⟨n⟩(T, 𝒜))"},
		{Name: "first coordinates",

			Text: "λz:(num → real). λi:num. COND(i < n, z(i), &0)"},
		{Name: "fiber coordinates",

			Text: "λz:(num → real). λi:num. COND(i < n, z(n + i), &0)"},
	})
