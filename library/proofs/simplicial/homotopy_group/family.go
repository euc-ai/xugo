// family.go — the homotopy_group family manifest: the registry handle every
// member registers into, and the family's one shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=homotopy_group.<Member> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=simplicial/homotopy_group go test -run TestRecordFamilyCNF ./library/integrity/gates/

package homotopy_group

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed homotopy_group.cnf.pb
var familyCNF []byte

// family is the family handle; the recorder derives
// homotopy_group/homotopy_group.cnf.pb from the name's basename, and the registered entry
// prefix is `homotopy_group.<Member>`.
var family = registry.NewFamily("simplicial/homotopy_group", familyCNF).WithAbbrev(Abbrev{
	{Name: "inverseFiller", Text: "w ∈ X.simplices(n + 1) ∧ " +
		"(∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
		"X.d(n + 1, n - 1, w) = x ∧ " +
		"X.d(n + 1, n, w) = base_simplex(x₀, n)"},
})
