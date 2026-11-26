// family.go — the prime_spectrum family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=prime_spectrum.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/prime_spectrum go test -run TestRecordFamilyCNF ./library/integrity/gates/

package prime_spectrum

import (
	_ "embed"

	// The chapters whose constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed prime_spectrum.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives prime_spectrum/prime_spectrum.cnf.pb
// from the name's basename, and the registered entry prefix is
// `prime_spectrum.<Member>`.
var family = registry.NewFamily("scheme/prime_spectrum", familyCNF)
