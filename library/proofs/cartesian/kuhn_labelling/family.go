// family.go — the kuhn_labelling family manifest: the registry handle
// every member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=kuhn_labelling.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=cartesian/kuhn_labelling go test -run TestRecordFamilyCNF ./library/integrity/gates/

package kuhn_labelling

import (
	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed kuhn_labelling.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// kuhn_labelling/kuhn_labelling.cnf.pb from the name's basename, and the
// registered entry prefix is `kuhn_labelling.<Member>`. The chapter has no
// vocabulary of its own: its one constant, kuhn_reduced, is spelled as an
// application, and every other name its statements spell — the grid and
// its simplices, the finite sets and their counts, parity — resolves
// through its mint. It has no table either: the terms its statements
// name are each one member's, declared in that member's own.
var family = registry.NewFamily("cartesian/kuhn_labelling", familyCNF)
