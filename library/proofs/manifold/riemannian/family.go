package riemannian

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed riemannian.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/riemannian", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(smooth_manifold.ChapterAbbrev, vec_form.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "chart image", Text: "λc:prod(set(A), A → num → real). image(snd(c), fst(c))"},
		{Name: "zero real matrix", Text: "λi:num. λj:num. &0"},
		{Name: "zero tangent", Text: "λc:prod(set(A), A → num → real). λi:num. &0"},
		{Name: "source chart", Text: "εc:prod(set(A), A → num → real). " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)"},
		{Name: "dual matrix", Text: "λy:(num → real). " +
			"    matrix_product(real_ring, n, transpose(E(y)), g(c, y))"},
		{Name: "frame column", Text: "λy:(num → real). λj:num. λl:num. λt:num. " +
			"    COND(l < n ∧ t = 0, E(y, l, j), &0)"},
		{Name: "frame pair", Text: "λy:(num → real). λj:num. λk:num. λl:num. λt:num. " +
			"    COND(l < n ∧ t = 0, E(y, l, j), COND(l < n ∧ t = 1, E(y, l, k), &0))"},
	})

// ChapterAbbrev supplies local frame and coordinate notation to
// chapters using the Riemannian metric and its connection matrices.
var ChapterAbbrev = family.ChapterAbbrev()
