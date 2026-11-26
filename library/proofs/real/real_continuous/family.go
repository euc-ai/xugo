// family.go — the real_continuous family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_continuous.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_continuous go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path.

package real_continuous

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_continuous.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_continuous/real_continuous.cnf.pb from it,
// and the registered entry prefix is the name's last segment
// (`real_continuous.<Member>`). The chapter has no vocabulary of its
// own: every name a statement spells resolves through its mint.
//
// The chapter works at one topology, the real line's, and binds it once:
// the instance theorem `is_topology(real_topology)` binds the structure's
// component T, so a statement here writes `connected_in(s)`,
// `compact_in(s)` and `subtopology(s)` for `connected_in(real_topology,
// s)` and the rest. A map between two spaces spells both,
// `continuous_map(subtopology(s), real_topology, f)`.
var family = registry.NewFamily("real/real_continuous", familyCNF).WithCoerceDomain(RealDomain).
	WithInstance(topological_space.IsTopology, real_topology.RealTopology).WithAbbrev(Abbrev{
	{Name: "values", Text: "image(f, ⟦a, b⟧)"},
})
