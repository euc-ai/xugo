// family.go — the ideal_colength family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=ideal_colength.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/ideal_colength go test -run TestRecordFamilyCNF ./library/integrity/gates/

package ideal_colength

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ideal_colength.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// ideal_colength/ideal_colength.cnf.pb from the name's basename, and the
// registered entry prefix is `ideal_colength.<Member>`.
var family = registry.NewFamily("algebra/ring/ideal_colength", familyCNF).WithOuterAbbrev(
	fractional_ideal.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "R", Text: "restrict_ring(field_ring(L), S)"},
	{Name: "V", Text: "regular_module(field_ring(L))"},
	{Name: "mul", Text: "fractional_mul(field_ring(L), S)"},
	{Name: "wfOverK", Text: "restrict_ring(field_ring(L), k)"},
	{Name: "quotient", Text: "λU:set(A). λW:set(A). quotient_module(restrict_module(«wfField», U), W)"},
	{Name: "finiteQuotient", Text: "λU:set(A). λW:set(A). " +
		"    finite_dimensional(«wfOverK», «quotient»(U, W))"},
	{Name: "colength", Text: "λU:set(A). λW:set(A). module_dim(«wfOverK», «quotient»(U, W))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
