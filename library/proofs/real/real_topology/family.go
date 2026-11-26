// family.go — the real_topology family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call InstallCNFCache
// — the replay harness installs familyCNF env-side before every
// member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=real_topology.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=real/real_topology go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// Note the two spellings: RECORD_CNF takes the registered member name,
// which carries the family's BASE name; CNF_GC takes the family's FULL
// domain path.

package real_topology

import (
	_ "embed"

	// The chapters whose constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	_ "github.com/euc-ai/xugo/library/proofs/topology/connected"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed real_topology.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates real/real_topology/real_topology.cnf.pb from it, and
// the registered entry prefix is the name's last segment
// (`real_topology.<Member>`). The chapter has no vocabulary of its own:
// every name a statement spells — the two constants this chapter mints,
// the topology's constants, real_abs, the order and the field
// operations, real_sequences' `⟶` — resolves through its mint.
//
// The family binds no instance, so its statements spell the family
// (real_continuous binds this one): the instance theorem RealTopology is
// a member of this family, and a handle declared WithInstance(…,
// RealTopology) would need that member before the handle it registers
// into exists.
var family = registry.NewFamily("real/real_topology", familyCNF).WithCoerceDomain(RealDomain)
