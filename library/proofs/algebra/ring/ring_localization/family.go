// family.go — the ring_localization family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=ring_localization.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/ring_localization go test -run TestRecordFamilyCNF ./library/integrity/gates/

package ring_localization

import (
	_ "embed"

	// The chapter whose constants the definitions spell, initialized
	// before them.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ring_localization.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives ring_localization/ring_localization.cnf.pb
// from the name's basename, and the registered entry prefix is
// `ring_localization.<Member>`.
var family = registry.NewFamily("algebra/ring/ring_localization", familyCNF).WithAbbrev(Abbrev{
	{Name: "nonzero", Text: "λR:ring_ops(A). R.carrier ∖ {R.zero}"},
})
