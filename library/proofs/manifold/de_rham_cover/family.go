package de_rham_cover

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed de_rham_cover.cnf.pb
var familyCNF []byte

// family reads the de Rham complex's table and adds the notation of a
// two-open cover: the complexes and classes of an open set, their
// restrictions, and the short exact cover sequence.
var family = registry.NewFamily("manifold/de_rham_cover", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(de_rham.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "open complex", Text: "λO:set(A). " +
			"    de_rham_complex⟨n⟩(subtopology(T, O), open_submanifold_atlas⟨n⟩(T, 𝒜, O))"},
		{Name: "open cohomology", Text: "λO:set(A). λq:num. " +
			"    de_rham_cohomology_module⟨n⟩(subtopology(T, O), open_submanifold_atlas⟨n⟩(T, 𝒜, O), q)"},
		{Name: "open restriction", Text: "λO:set(A). λW:set(A). " +
			"    manifold_form_restrict⟨n⟩(subtopology(T, O), open_submanifold_atlas⟨n⟩(T, 𝒜, O), W)"},
		{Name: "class restriction", Text: "λO:set(A). λW:set(A). λq:num. " +
			"    de_rham_pullback⟨n, n⟩(subtopology(T, W), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, W), " +
			"        subtopology(T, O), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, O), " +
			"        q, " +
			"        identity_map)"},
		{Name: "global class restriction", Text: "λO:set(A). λq:num. " +
			"    de_rham_pullback⟨n, n⟩(subtopology(T, O), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, O), " +
			"        T, " +
			"        𝒜, " +
			"        q, " +
			"        identity_map)"},
		{Name: "cohomology restriction", Text: "λq:num. " +
			"λs:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    («global class restriction»(U, q, s), «global class restriction»(V, q, s))"},
		{Name: "cohomology difference", Text: "λq:num. " +
			"λz:prod(set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real), " +
			"        set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
			"    «open cohomology»(U ∩ V, q).add(«class restriction»(U, U ∩ V, q, fst(z)), " +
			"        «open cohomology»(U ∩ V, q).neg(«class restriction»(V, U ∩ V, q, snd(z))))"},
		{Name: "cover exact", Text: "short_exact_cochain_complexes(real_ring, " +
			"    de_rham_complex⟨n⟩(T, 𝒜), " +
			"    de_rham_cover_complex⟨n⟩(T, 𝒜, U, V), " +
			"    «open complex»(U ∩ V), " +
			"    (λq:num. de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V)), " +
			"    (λq:num. de_rham_cover_difference⟨n⟩(T, 𝒜, U, V)))"},
	})

// ChapterAbbrev supplies the open-set and cover-sequence notation to the
// chapters that compare cohomology across a cover.
var ChapterAbbrev = family.ChapterAbbrev()
