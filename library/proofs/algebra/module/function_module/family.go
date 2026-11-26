// family.go — the function_module family manifest: the registry
// handle every member registers into, and the family's ONE shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=function_module.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/function_module go test -run TestRecordFamilyCNF ./library/integrity/gates/

package function_module

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed function_module.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// function_module/function_module.cnf.pb from the name's
// basename, and the registered entry prefix is
// `function_module.<Member>`.
var family = registry.NewFamily("algebra/module/function_module", familyCNF)
