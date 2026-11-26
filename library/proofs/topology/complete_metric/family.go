// family.go — the complete_metric family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=complete_metric.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=topology/complete_metric go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package complete_metric

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complete_metric.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path: the
// recorder locates topology/complete_metric/complete_metric.cnf.pb from it,
// and the registered entry prefix is the name's last segment
// (`complete_metric.<Member>`). The chapter has no vocabulary of its own:
// every name its statements spell — the set constructors, ℝ's order and
// arithmetic, the metric chapter's constants and the topology chapters' —
// resolves through its mint.
// An unanchored numeral `&k` is a real one: the chapter's numbers are
// reals.
var family = registry.NewFamily("topology/complete_metric", familyCNF).
	WithCoerceDomain(RealDomain)
