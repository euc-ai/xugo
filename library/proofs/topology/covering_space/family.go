// family.go — the covering_space family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache. Proof files carry entry vars; they never call
// InstallCNFCache — the replay harness installs familyCNF env-side
// before every member's Build.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=covering_space.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=topology/covering_space go test -run TestRecordFamilyCNF ./library/integrity/gates/
//
// The two envs take DIFFERENT forms: RECORD_CNF takes the registered
// member name, which carries the family's BASE name; CNF_GC takes the
// family's FULL domain path.

package covering_space

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed covering_space.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `covering_space.<Member>`. An unanchored numeral `&k` is a real one,
// the lifting theorems lifting paths and squares of the unit interval.
// The chapter's table names «I», the unit interval ⟦0, 1⟧ read as a
// subspace of the line.
var family = registry.NewFamily("topology/covering_space", familyCNF).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "I", Text: "subtopology(real_topology, ⟦&0, &1⟧)"},
	})
