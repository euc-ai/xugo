// family.go — the segal family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=segal.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/segal go test -run TestRecordFamilyCNF ./library/integrity/gates/

package segal

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed segal.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// segal/segal.cnf.pb from the name's basename, and the registered entry
// prefix is `segal.<Member>`.
var family = registry.NewFamily("simplicial/segal", familyCNF)
