// family.go — the hom_module family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=hom_module.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/hom_module go test -run TestRecordFamilyCNF ./library/integrity/gates/

package hom_module

import (
	_ "embed"

	// linear_independence mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed hom_module.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// hom_module/hom_module.cnf.pb from the name's basename, and the
// registered entry prefix is `hom_module.<Member>`.
var family = registry.NewFamily("algebra/module/hom_module", familyCNF).WithAbbrev(Abbrev{
	{Name: "algebraOverR", Text: "scalar_restriction(f, regular_module(T))"},
})
