package differential_form

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed differential_form.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/differential_form", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(smooth_manifold.ChapterAbbrev, vec_form.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "chart image", Text: "λc:prod(set(A), A → num → real). image(snd(c), fst(c))"},
		{Name: "zero family", Text: "λc:prod(set(A), A → num → real). «zero»"},
		{Name: "target chart", Text: "εd:prod(set(B), B → num → real). " +
			"    compatible_chart⟨m⟩(S, ℬ, d) ∧ f(inverse_on(fst(c), snd(c), y)) ∈ fst(d)"},
	})

// ChapterAbbrev supplies coordinate domains and normalized form families
// to chapters that build operations on manifold differential forms.
var ChapterAbbrev = family.ChapterAbbrev()
