// family.go — the path_integral family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=path_integral.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/path_integral go test -run TestRecordFamilyCNF ./library/integrity/gates/

package path_integral

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed path_integral.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `path_integral.<Member>`. The domain is ℂ: `&` of a real is
// complex_of_real, and a bare `&n` is a real. Its table names the integrals
// along the two paths the chapter computes on, the integral along the
// segment from z to w and the integral once round the circle about c of
// radius r, and «closedPathIn»(X, γ, γ', a, b): γ is a closed piecewise
// smooth path on ⟦a, b⟧ with velocity γ' that stays in the set X.
var family = registry.NewFamily("complex/path_integral", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain).
	WithAbbrev(Abbrev{
		{Name: "segInt", Text: "λf:(complex → complex). λz:complex. λw:complex. " +
			"    path_integral(f, segment_path(z, w), λt:real. w - z, &0, &1)"},
		{Name: "circleInt", Text: "λf:(complex → complex). λc:complex. λr:real. " +
			"    path_integral(f, " +
			"        circle_path(c, r), " +
			"        λt:real. complex_i * &r * exp(complex_i * &t), " +
			"        &0, " +
			"        &2 * pi)"},
		{Name: "closedPathIn", Text: "λX:set(complex). " +
			"λγ:(real → complex). " +
			"λγ':(real → complex). " +
			"λa:real. " +
			"λb:real. " +
			"    piecewise_smooth_path(γ, γ', a, b) ∧ γ(b) = γ(a) ∧ ∀t:real. a ≤ t ∧ t ≤ b ⇒ γ(t) ∈ X"},
	})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
