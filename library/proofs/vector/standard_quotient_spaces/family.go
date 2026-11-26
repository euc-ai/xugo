// family.go — the standard_quotient_spaces family manifest: the registry
// handle every member registers into, and the family's ONE shared
// recorded CNF cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=standard_quotient_spaces.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=vector/standard_quotient_spaces go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package standard_quotient_spaces

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed standard_quotient_spaces.cnf.pb
var familyCNF []byte

// family is the family handle, bound to the real ring as the euclidean
// chapters are, so that its statements spell `vec⟨n⟩(u)` and the norm with
// the ring left implicit; an unanchored numeral `&k` is a real one.
var family = registry.NewFamily("vector/standard_quotient_spaces", familyCNF).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).
	WithCoerceDomain(RealDomain)
