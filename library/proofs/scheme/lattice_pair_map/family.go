// family.go — the lattice_pair_map family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=lattice_pair_map.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/lattice_pair_map go test -run TestRecordFamilyCNF ./library/integrity/gates/

package lattice_pair_map

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lattice_pair_map.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// lattice_pair_map/lattice_pair_map.cnf.pb from the name's basename, and
// the registered entry prefix is `lattice_pair_map.<Member>`.
var family = registry.NewFamily("scheme/lattice_pair_map", familyCNF).WithOuterAbbrev(
	lattice_pair.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "waSource", Text: "lattice_pair(R, A₀, A₁, V, M)"},
	{Name: "waMapsModule", Text: "hom_module(R, restrict_module(V, lattice_pair_ambient(R, V, M)), W)"},
	{Name: "waIsomorphism", Text: "lattice_pair_isomorphism(R, V, M, W, N, f)"},
})
