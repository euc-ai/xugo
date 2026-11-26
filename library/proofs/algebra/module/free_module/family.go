// family.go — the free_module family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=free_module.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/free_module go test -run TestRecordFamilyCNF ./library/integrity/gates/

package free_module

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed free_module.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// free_module/free_module.cnf.pb from the name's basename, and the
// registered entry prefix is `free_module.<Member>`.
var family = registry.NewFamily("algebra/module/free_module", familyCNF).WithAbbrev(Abbrev{
	{Name: "identityLift", Text: "free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u)"},
	{Name: "transposeFreeMap", Text: "module_homomorphism(R, " +
		"    free_module_record(R, S), " +
		"    free_module_record(R, S'), " +
		"    Φ)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
