// family.go — the projective_line_duality family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=projective_line_duality.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/projective_line_duality go test -run TestRecordFamilyCNF ./library/integrity/gates/

package projective_line_duality

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_line_duality.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// projective_line_duality/projective_line_duality.cnf.pb from the name's basename, and
// the registered entry prefix is `projective_line_duality.<Member>`.
var family = registry.NewFamily("scheme/projective_line_duality", familyCNF).WithOuterAbbrev(
	projective_line.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "plDualizing", Text: "projective_line_pair(L, k, t, -&2)"},
	{Name: "plMaps", Text: "lattice_pair_maps(«plRing», V, M, «plField», «plDualizing»)"},
	{Name: "plH1", Text: "lattice_pair_h1(«plRing», V, M)"},
	{Name: "plModuleK", Text: "restrict_module(regular_module(field_ring(L)), k)"},
	{Name: "plDualSet", Text: "hom_set(«plScalars», «plH1», «plModuleK»)"},
	{Name: "plChartSum", Text: "set_mul(V.add, fst(M), snd(M))"},
	{Name: "plAmbientModule", Text: "restrict_module(V, «plAmbient»)"},
	{Name: "plClass", Text: "left_coset(V.add, x, «plChartSum»)"},
	{Name: "plClasses", Text: "left_cosets(V.add, «plAmbient», «plChartSum»)"},
	{Name: "plDualModule", Text: "hom_module(«plScalars», «plH1», «plModuleK»)"},
	{Name: "plDuality", Text: "λφ:(B → A). λX:set(B). " +
		"    projective_line_duality_map(L, k, t, V, M, φ, X)"},
	{Name: "plShiftedSupport", Text: "fun_support(L.zero, " +
		"    λm:int. u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)))"},
	{Name: "plFunctionalOnAmbient", Text: "λy:B. u(left_coset(V.add, y, «plChartSum»))"},
	{Name: "plShiftedExpansion", Text: "module_sum(L.add, " +
		"    L.zero, " +
		"    «plShiftedSupport», " +
		"    λm:int. " +
		"        u(left_coset(V.add, V.smul(laurent_monomial(t, -m - &1), x), «plChartSum»)) * " +
		"        laurent_monomial(t, m))"},
	{Name: "plInverseAtX", Text: "projective_line_duality_inverse(L, k, t, V, M, u)"},
	{Name: "plInverseOf", Text: "λx:B. projective_line_duality_inverse(L, k, t, V, M, u, x)"},
})
