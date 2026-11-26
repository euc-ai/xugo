package smooth_manifold

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed smooth_manifold.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/smooth_manifold", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "product chart", Text: "λc:prod(set(A), A → num → real). λd:prod(set(B), B → num → real). " +
			"    (set_cross(fst(c), fst(d)), " +
			"        λp:prod(A, B). λi:num. " +
			"            COND(i < n, snd(c)(fst(p), i), COND(i < n + m, snd(d)(snd(p), i - n), &0)))"},
		{Name: "overlap", Text: "λc:prod(set(A), A → num → real). λd:prod(set(A), A → num → real). " +
			"    image(snd(c), fst(c) ∩ fst(d))"},
		{Name: "transition", Text: "λc:prod(set(A), A → num → real). λd:prod(set(A), A → num → real). " +
			"    snd(d) ∘ inverse_on(fst(c), snd(c))"},
		{Name: "compatible atlas", Text: "{c:prod(set(A), A → num → real) | compatible_chart⟨n⟩(T, 𝒜, c)}"},
		{Name: "map domain", Text: "λc:prod(set(A), A → num → real). " +
			"λd:prod(set(B), B → num → real). " +
			"λf:(A → B). " +
			"    image(snd(c), {x:A | x ∈ fst(c) ∧ f(x) ∈ fst(d)})"},
		{Name: "coordinate map", Text: "λc:prod(set(A), A → num → real). " +
			"λd:prod(set(B), B → num → real). " +
			"λf:(A → B). " +
			"    snd(d) ∘ f ∘ inverse_on(fst(c), snd(c))"},
	})

// ChapterAbbrev supplies the chart overlap and coordinate-map notation
// to chapters whose objects are families over compatible charts.
var ChapterAbbrev = family.ChapterAbbrev()
