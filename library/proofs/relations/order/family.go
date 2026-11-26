// family.go — the order family manifest: the registry handle every
// member registers into, and the family's ONE shared recorded CNF
// cache.
//
// pb maintenance (recipes in gates/record_cnf_test.go's header):
//
//	XUGO_RECORD_FAMILY_CNF=order.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=relations/order go test -run TestRecordFamilyCNF ./library/integrity/gates/

package order

import (
	// equivalence mints reflexive, transitive and the other properties of
	// a relation this family's definitions spell, which no other import
	// reaches.
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"

	_ "embed"

	"github.com/euc-ai/xugo/library/registry"
)

//go:embed order.cnf.pb
var familyCNF []byte

// family is the family handle. Its name is the full domain path; the
// registered entry prefix is the name's last segment
// (`order.<Member>`).
var family = registry.NewFamily("relations/order", familyCNF)
