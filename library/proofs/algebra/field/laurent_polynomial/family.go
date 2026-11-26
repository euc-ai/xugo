// family.go — the laurent_polynomial family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=laurent_polynomial.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/field/laurent_polynomial go test -run TestRecordFamilyCNF ./library/integrity/gates/

package laurent_polynomial

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed laurent_polynomial.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// laurent_polynomial/laurent_polynomial.cnf.pb from the name's basename, and
// the registered entry prefix is `laurent_polynomial.<Member>`.
var family = registry.NewFamily("algebra/field/laurent_polynomial", familyCNF).WithAbbrev(Abbrev{
	{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
	{Name: "inversePolynomials", Text: "polynomial_image(field_ring(L), k, L.inv(t))"},
	{Name: "laurentRing", Text: "ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)"},
	{Name: "laurentRingOps", Text: "restrict_ring(field_ring(L), «laurentRing»)"},
	{Name: "expansion", Text: "module_sum(L.add, " +
		"    L.zero, " +
		"    fun_support(L.zero, a), " +
		"    λj:int. a(j) * laurent_monomial(t, j))"},
	{Name: "shiftedInversePolynomials", Text: "image(L.mul(laurent_monomial(t, n)), " +
		"    «inversePolynomials»)"},
	{Name: "ownExpansion", Text: "module_sum(L.add, " +
		"    L.zero, " +
		"    fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i)), " +
		"    λi:int. laurent_polynomial_coefficient(k, t, f, i) * laurent_monomial(t, i))"},
})
