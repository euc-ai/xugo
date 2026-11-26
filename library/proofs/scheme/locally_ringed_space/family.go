// family.go — the locally_ringed_space family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=locally_ringed_space.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/locally_ringed_space go test -run TestRecordFamilyCNF ./library/integrity/gates/

package locally_ringed_space

import (
	// local_ring mints constants this family's definitions spell, and no
	// other import reaches it: the import initializes those mints
	// before the definitions here are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/local_ring"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed locally_ringed_space.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives locally_ringed_space/locally_ringed_space.cnf.pb
// from the name's basename, and the registered entry prefix is
// `locally_ringed_space.<Member>`.
var family = registry.NewFamily("scheme/locally_ringed_space", familyCNF)
