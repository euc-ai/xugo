// family.go — the homotopy family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=homotopy.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=topology/homotopy go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package homotopy

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed homotopy.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `homotopy.<Member>`. An unanchored numeral `&k` is a real one, the
// homotopy parameter running over the unit interval of the line. The
// chapter's table names «I», the unit interval ⟦0, 1⟧ read as a subspace
// of the line, the domain of every path and the parameter space of every
// homotopy.
var family = registry.NewFamily("topology/homotopy", familyCNF).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "I", Text: "subtopology(real_topology, ⟦&0, &1⟧)"},
	})
