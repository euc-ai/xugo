// family.go — the divisor_lattice_correspondence family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=divisor_lattice_correspondence.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/divisor_lattice_correspondence go test -run TestRecordFamilyCNF ./library/integrity/gates/

package divisor_lattice_correspondence

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed divisor_lattice_correspondence.cnf.pb
var familyCNF []byte

// _IdealPair is the Go type of a pair of subsets of the field: an ideal pair,
// a closed point.
type _IdealPair = Prod[Set[A], Set[A]]

// family is the family handle. The recorder derives
// divisor_lattice_correspondence/divisor_lattice_correspondence.cnf.pb from the name's basename, and
// the registered entry prefix is `divisor_lattice_correspondence.<Member>`.
var family = registry.NewFamily("scheme/divisor_lattice_correspondence", familyCNF).WithOuterAbbrev(
	closed_divisor.ChapterAbbrev)
