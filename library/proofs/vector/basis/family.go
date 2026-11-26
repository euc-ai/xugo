// family.go — the basis family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=basis.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/basis go test -run TestRecordFamilyCNF ./library/integrity/gates/

package basis

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed basis.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives basis/basis.cnf.pb
// from the name's basename, and the registered entry prefix is
// `basis.<Member>`. The chapter states its laws over an arbitrary
// commutative ring where the ring suffices and over a field where the
// argument divides, so it binds no instance.
var family = registry.NewFamily("vector/basis", familyCNF)
