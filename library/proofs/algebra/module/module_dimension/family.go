// family.go — the module_dimension family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=module_dimension.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/module/module_dimension go test -run TestRecordFamilyCNF ./library/integrity/gates/

package module_dimension

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed module_dimension.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// module_dimension/module_dimension.cnf.pb from the name's basename, and
// the registered entry prefix is `module_dimension.<Member>`.
var family = registry.NewFamily("algebra/module/module_dimension", familyCNF).WithAbbrev(Abbrev{
	{Name: "quotientUW", Text: "quotient_module(restrict_module(M, U), W)"},
	{Name: "iModJ", Text: "quotient_module(restrict_module(M, I), J)"},
	{Name: "iModIPrime", Text: "quotient_module(restrict_module(M, I), I')"},
	{Name: "iPrimeModJ", Text: "quotient_module(restrict_module(M, I'), J)"},
	{Name: "enlarging", Text: "λx:set(B). set_mul(M.add, x, I')"},
	{Name: "kernelClasses", Text: "group_kernel(I', left_cosets(M.add, I, J), «enlarging»)"},
})
