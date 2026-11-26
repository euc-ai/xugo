// family.go — the circle family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF cache.
// Proof files carry entry vars; they never call InstallCNFCache — the
// replay harness installs familyCNF env-side before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=circle.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/circle go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package circle

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed circle.cnf.pb
var familyCNF []byte

// family is the family handle, bound to the real ring as the euclidean
// chapters are, so that its statements spell `vec⟨n⟩(u)` and `-x` with
// the ring left implicit; an unanchored numeral `&k` is a real one. The
// chapter's table names «circle»(t), the point (cos 2πt, sin 2πt) of the
// plane, as standard_quotient_spaces writes it, and «D²», the closed unit
// disc as a subspace of the plane; the circle as a space is
// euclidean_topology's euclidean_sphere_topology(1).
var family = registry.NewFamily("vector/circle", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "circle", Text: "λt:real. λi:num. " +
			"    COND(i = 0, cos(&2 * pi * t), COND(i = 1, sin(&2 * pi * t), &0))"},
		{Name: "D²", Text: "subtopology(euclidean_topology(2), euclidean_ball(2))"},
	})
