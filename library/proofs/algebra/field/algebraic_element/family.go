// family.go — the algebraic_element family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=algebraic_element.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/field/algebraic_element go test -run TestRecordFamilyCNF ./library/integrity/gates/

package algebraic_element

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed algebraic_element.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// algebraic_element/algebraic_element.cnf.pb from the name's basename, and
// the registered entry prefix is `algebraic_element.<Member>`.
var family = registry.NewFamily("algebra/field/algebraic_element", familyCNF).WithOuterAbbrev(
	polynomial_division.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "powerMap", Text: "λi:num. monoid_pow(L.mul, L.one, a, i)"},
	{Name: "scalars", Text: "restrict_ring(field_ring(L), K)"},
	{Name: "adjoinVectors", Text: "restrict_module(regular_module(field_ring(L)), " +
		"    field_adjoin(L, K, {a}))"},
	{Name: "powersBelowDegree", Text: "{monoid_pow(L.mul, L.one, a, i) | " +
		"    i:num | " +
		"    i < polynomial_degree(minimal_polynomial(L, K, a))}"},
})
