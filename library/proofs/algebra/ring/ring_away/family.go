// family.go — the ring_away family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=ring_away.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/ring_away go test -run TestRecordFamilyCNF ./library/integrity/gates/

package ring_away

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed ring_away.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// ring_away/ring_away.cnf.pb from the name's basename, and the registered
// entry prefix is `ring_away.<Member>`.
var family = registry.NewFamily("algebra/ring/ring_away", familyCNF).WithOuterAbbrev(
	polynomial_roots.ChapterAbbrev)
