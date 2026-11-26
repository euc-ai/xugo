// family.go — the metric_space family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=metric_space.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=topology/metric_space go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package metric_space

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed metric_space.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates topology/metric_space/metric_space.cnf.pb from it, and
// the registered entry prefix is the name's last segment
// (`metric_space.<Member>`). The chapter has no vocabulary of its own:
// every name its statements spell — the set constructors, ℝ's order and
// addition, and the topology chapters' constants — resolves through its
// mint.
// An unanchored numeral `&k` is a real one: the chapter's numbers are
// reals.
var family = registry.NewFamily("topology/metric_space", familyCNF).
	WithCoerceDomain(RealDomain)
