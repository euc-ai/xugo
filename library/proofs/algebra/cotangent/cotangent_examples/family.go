// family.go — the cotangent_examples family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=cotangent_examples.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/cotangent/cotangent_examples go test -run TestRecordFamilyCNF ./library/integrity/gates/

package cotangent_examples

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed cotangent_examples.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// cotangent_examples/cotangent_examples.cnf.pb from the name's basename, and the
// registered entry prefix is `cotangent_examples.<Member>`.
var family = registry.NewFamily(
	"algebra/cotangent/cotangent_examples", familyCNF).WithAbbrev(Abbrev{
	{Name: "integerRing", Text: "mk_ring(int_add, &0, int_neg, int_mul, &1, int_sub, 𝕌⟨A:int⟩)"},
	{Name: "conormalComplex", Text: "cotangent_complex⟨U:U⟩(R, S, f, S, λy:B. y, regular_module(S))"},
	{Name: "conormalFirst", Text: "cotangent_homology(R, S, f, S, λy:B. y, regular_module(S), 1)"},
})
