// family.go — the lattice_pair_twist family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=lattice_pair_twist.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/lattice_pair_twist go test -run TestRecordFamilyCNF ./library/integrity/gates/

package lattice_pair_twist

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lattice_pair_twist.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// lattice_pair_twist/lattice_pair_twist.cnf.pb from the name's basename, and
// the registered entry prefix is `lattice_pair_twist.<Member>`.
var family = registry.NewFamily("scheme/lattice_pair_twist", familyCNF).WithOuterAbbrev(
	invertible_lattice_pair.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "wbTwist", Text: "lattice_pair_twist(field_ring(L), A₀, A₁)"},
})
