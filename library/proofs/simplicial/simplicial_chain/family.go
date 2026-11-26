// family.go — the simplicial_chain family manifest: the registry
// handle every member registers into, and the family's one shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=simplicial_chain.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/simplicial_chain go test -run TestRecordFamilyCNF ./library/integrity/gates/

package simplicial_chain

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed simplicial_chain.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// simplicial_chain/simplicial_chain.cnf.pb from the name's basename,
// and the registered entry prefix is `simplicial_chain.<Member>`.
var family = registry.NewFamily("simplicial/simplicial_chain", familyCNF)
