// family.go — the cohomology_one family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=cohomology_one.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/cohomology_one go test -run TestRecordFamilyCNF ./library/integrity/gates/

package cohomology_one

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cohomology_one.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// cohomology_one/cohomology_one.cnf.pb from the name's basename, and the
// registered entry prefix is `cohomology_one.<Member>`.
var family = registry.NewFamily("algebra/cotangent/cohomology_one", familyCNF).WithAbbrev(Abbrev{
	{Name: "cochains", Text: "cotangent_cochain(R, S, f, S, λy:B. y, N)"},
})
