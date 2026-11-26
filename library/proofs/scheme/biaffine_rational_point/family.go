// family.go — the biaffine_rational_point family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=biaffine_rational_point.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/biaffine_rational_point go test -run TestRecordFamilyCNF ./library/integrity/gates/

package biaffine_rational_point

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed biaffine_rational_point.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// biaffine_rational_point/biaffine_rational_point.cnf.pb from the name's basename, and
// the registered entry prefix is `biaffine_rational_point.<Member>`.
var family = registry.NewFamily("scheme/biaffine_rational_point", familyCNF).WithOuterAbbrev(
	lattice_pair.ChapterAbbrev)
