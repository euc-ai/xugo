// family.go — the local_ring family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=local_ring.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/local_ring go test -run TestRecordFamilyCNF ./library/integrity/gates/

package local_ring

import (
	_ "embed"

	// ring_localization mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed local_ring.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives local_ring/local_ring.cnf.pb
// from the name's basename, and the registered entry prefix is
// `local_ring.<Member>`.
var family = registry.NewFamily("algebra/ring/local_ring", familyCNF).WithAbbrev(Abbrev{
	{Name: "nonUnits", Text: "{x:A | x ∈ R.carrier ∧ ¬ring_unit(R, x)}"},
})
