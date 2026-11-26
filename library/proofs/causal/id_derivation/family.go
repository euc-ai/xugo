// family.go — the id_derivation family manifest: the registry handle
// every member registers into and the family's shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=id_derivation.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=causal/id_derivation go test -run TestRecordFamilyCNF ./library/integrity/gates/

package id_derivation

import (
	_ "embed"

	_ "github.com/euc-ai/xugo/library/proofs/causal/do_derivation"
	_ "github.com/euc-ai/xugo/library/proofs/datatypes/list"
	_ "github.com/euc-ai/xugo/library/proofs/relations/graph/latent_projection"
	_ "github.com/euc-ai/xugo/library/proofs/sets/listing"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed id_derivation.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("causal/id_derivation", familyCNF)
