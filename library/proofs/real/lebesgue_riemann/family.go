// family.go — the lebesgue_riemann family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=lebesgue_riemann.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/lebesgue_riemann go test -run TestRecordFamilyCNF ./library/integrity/gates/

package lebesgue_riemann

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lebesgue_riemann.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("real/lebesgue_riemann", familyCNF).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "lebesgueSets", Text: "{s:set(real) | lebesgue_measurable(s)}"},
		{Name: "cut", Text: "λE:set(real). λv:(real → real). λx:real. COND(x ∈ E, v(x), &0)"},
	})
