package de_rham_product

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed de_rham_product.cnf.pb
var familyCNF []byte

// family reads the de Rham complex's table and adds the product atlas
// and the closed representative a class product is computed on.
var family = registry.NewFamily("manifold/de_rham_product", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(de_rham.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "closed representative", Text: "λj:num. " +
			"λσ:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"εζ:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_form_on⟨n⟩(T, 𝒜, j, ζ) ∧ " +
			"    manifold_exterior_derivative⟨n⟩(T, 𝒜, j, ζ) = de_rham_complex⟨n⟩(T, 𝒜).zero ∧ " +
			"    de_rham_class⟨n⟩(T, 𝒜, j, ζ) = σ"},
		{Name: "product atlas", Text: "smooth_product_atlas⟨n, m⟩(𝒜, ℬ)"},
	})
