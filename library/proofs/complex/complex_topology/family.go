// family.go — the complex_topology family manifest: the registry handle
// every member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=complex_topology.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=complex/complex_topology go test -run TestRecordFamilyCNF ./library/integrity/gates/

package complex_topology

import (
	_ "embed"

	// real_continuous mints constants the statements here spell.
	_ "github.com/euc-ai/xugo/library/proofs/real/real_continuous"

	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed complex_topology.cnf.pb
var familyCNF []byte

// family is the family handle; the registered entry prefix is
// `complex_topology.<Member>`. The domain is ℂ: `&` of a real is
// complex_of_real, and a bare `&n` is a real.
var family = registry.NewFamily("complex/complex_topology", familyCNF).WithCoerceDomain(
	complex_field.ComplexDomain)
