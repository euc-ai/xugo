package tangent

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed tangent.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/tangent", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(smooth_manifold.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "active", Text: "λc:prod(set(A), A → num → real). " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)"},
		{Name: "zero tangent", Text: "λc:prod(set(A), A → num → real). λi:num. &0"},
		{Name: "Euclidean module", Text: "function_module(regular_module(real_ring), {i:num | i < n})"},
		{Name: "join", Text: "λy:(num → real). λu:(num → real). λi:num. " +
			"    COND(i < n, y(i), COND(i < 2 * n, u(i - n), &0))"},
		{Name: "base block", Text: "λz:(num → real). λi:num. COND(i < n, z(i), &0)"},
		{Name: "fiber block", Text: "λz:(num → real). λi:num. COND(i < n, z(n + i), &0)"},
		{Name: "lift", Text: "λc:prod(set(A), A → num → real). tangent_chart⟨n⟩(T, 𝒜, c)"},
		{Name: "lift transition", Text: "λc:prod(set(A), A → num → real). " +
			"λd:prod(set(A), A → num → real). " +
			"    snd(«lift»(d)) ∘ inverse_on(fst(«lift»(c)), snd(«lift»(c)))"},
		{Name: "source chart", Text: "εc:prod(set(A), A → num → real). " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)"},
	})

// ChapterAbbrev supplies the normalized fiber and block-coordinate
// notation to chapters that use tangent vectors and the tangent bundle.
var ChapterAbbrev = family.ChapterAbbrev()
