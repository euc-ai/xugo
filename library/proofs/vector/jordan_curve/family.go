// family.go — the jordan_curve family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars; they never call InstallCNFCache — the
// replay harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=jordan_curve.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/jordan_curve go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package jordan_curve

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed jordan_curve.cnf.pb
var familyCNF []byte

// family is the family handle, bound to the real ring as the euclidean
// chapters are, so that its statements spell `vec⟨n⟩(u)` and the norm
// with the ring left implicit; an unanchored numeral `&k` is a real one.
// The chapter's table names «I», the unit interval ⟦0, 1⟧ read as a
// subspace of the line.
var family = registry.NewFamily("vector/jordan_curve", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "I", Text: "subtopology(real_topology, ⟦&0, &1⟧)"},
	})
