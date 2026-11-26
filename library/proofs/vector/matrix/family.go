// family.go — the matrix family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=matrix.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/matrix go test -run TestRecordFamilyCNF ./library/integrity/gates/

package matrix

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed matrix.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// matrix/matrix.cnf.pb from the name's basename, and the registered
// entry prefix is `matrix.<Member>`. The chapter states its laws over
// an arbitrary commutative ring, as vec_space and dot do, so it binds no
// instance: a carrier applies them by citing its own ring.
var family = registry.NewFamily("vector/matrix", familyCNF)
