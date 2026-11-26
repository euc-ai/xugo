package form_integral

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed form_integral.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("manifold/form_integral", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithOuterAbbrev(differential_form.ChapterAbbrev).
	WithAbbrev(Abbrev{
		{Name: "product coordinates", Text: "λy:(num → real). λz:(num → real). λi:num. " +
			"    COND(i < n, y(i), COND(i < n + m, z(i - n), &0))"},
		{Name: "fiber frame", Text: "λP:(num → num → real). λQ:(num → num → real). λi:num. λj:num. " +
			"    COND(i < n + m ∧ j < k + m, " +
			"        COND(j < k, COND(i < n, P(i, j), &0), COND(i < n, &0, Q(i - n, j - k))), " +
			"        &0)"},
		{Name: "positive atlas", Text: "{c:prod(set(A), A → num → real) | " +
			"    positive_manifold_chart⟨n⟩(T, 𝒜, c)}"},
		{Name: "positive domains", Text: "{U:set(A) | " +
			"    ∃e:prod(set(A), A → num → real). positive_manifold_chart⟨n⟩(T, 𝒜, e) ∧ U = fst(e)}"},
		{Name: "reflection", Text: "λy:(num → real). λi:num. COND(i = 0, -y(i), y(i))"},
		{Name: "reflected chart", Text: "λc:prod(set(A), A → num → real). (fst(c), «reflection» ∘ snd(c))"},
	})
