package de_rham

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed de_rham.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/de_rham", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(differential_form.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "time point", Text: "λt:real. λi:num. COND(i = 0, t, &0)"},
		{Name: "cylinder topology", Text: "product_topology(T, subtopology(euclidean_topology(1), J))"},
		{Name: "cylinder atlas", Text: "smooth_product_atlas⟨n, 1⟩(𝒜, euclidean_atlas(J))"},
		{Name: "cylinder chart", Text: "λc:prod(set(A), A → num → real). " +
			"    (set_cross(fst(c), J), " +
			"        λp:prod(A, num → real). λi:num. " +
			"            COND(i < n, snd(c)(fst(p), i), COND(i < n + 1, snd(p)(i - n), &0)))"},
		{Name: "endpoint", Text: "λt:real. λx:A. (x, «time point»(t))"},
		{Name: "euclidean cohomology", Text: "λO:set(num → real). λq:num. " +
			"    de_rham_cohomology_module⟨n⟩(subtopology(euclidean_topology(n), O), euclidean_atlas(O), q)"},
		{Name: "euclidean product topology", Text: "product_topology( " +
			"    subtopology(euclidean_topology(n), U), T)"},
		{Name: "euclidean product atlas", Text: "smooth_product_atlas⟨n, m⟩(euclidean_atlas(U), 𝒜)"},
		{Name: "convex section", Text: "λx:A. (a, x)"},
	})

// ChapterAbbrev supplies the cylinder, endpoint and Euclidean product
// notation to the chapters cut from the de Rham complex.
var ChapterAbbrev = family.ChapterAbbrev()
