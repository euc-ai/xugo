// family.go — the simplicial_operator family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=simplicial_operator.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/simplicial_operator go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simplicial_operator

import (
	// The constants this family's statements spell are minted by these
	// families: the imports initialize the mints before the statements
	// are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/list"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simplicial_operator.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// simplicial_operator/simplicial_operator.cnf.pb from the name's basename, and the registered
// entry prefix is `simplicial_operator.<Member>`.
var family = registry.NewFamily("simplicial/simplicial_operator", familyCNF)
