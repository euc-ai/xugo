// family.go — the projective_line family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=projective_line.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/projective_line go test -run TestRecordFamilyCNF ./library/integrity/gates/

package projective_line

import (
	_ "embed"

	// The chapters whose constants the definitions spell, initialized
	// before them.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed projective_line.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// projective_line/projective_line.cnf.pb from the name's basename, and
// the registered entry prefix is `projective_line.<Member>`.
var family = registry.NewFamily("scheme/projective_line", familyCNF).WithAbbrev(Abbrev{
	{Name: "plChart0", Text: "polynomial_image(field_ring(L), k, t)"},
	{Name: "plChart1", Text: "polynomial_image(field_ring(L), k, L.inv(t))"},
	{Name: "plOverlap", Text: "ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)"},
	{Name: "plRing", Text: "restrict_ring(field_ring(L), «plOverlap»)"},
	{Name: "plField", Text: "regular_module(field_ring(L))"},
	{Name: "plPairOnLine", Text: "lattice_pair(«plRing», «plChart0», «plChart1», V, M)"},
	{Name: "plPairN", Text: "projective_line_pair(L, k, t, n)"},
	{Name: "plAmbient", Text: "lattice_pair_ambient(«plRing», V, M)"},
	{Name: "plScalars", Text: "restrict_ring(«plRing», k)"},
	{Name: "plRingK", Text: "restrict_ring(field_ring(L), k)"},
	{Name: "plOverlapModule", Text: "restrict_module(regular_module(field_ring(L)), «plOverlap»)"},
	{Name: "plRing0", Text: "restrict_ring(field_ring(L), «plChart0»)"},
	{Name: "plRing1", Text: "restrict_ring(field_ring(L), «plChart1»)"},
	{Name: "plSectionsN", Text: "fst(«plPairN») ∩ snd(«plPairN»)"},
	{Name: "plChart1N", Text: "image(L.mul(laurent_monomial(t, n)), «plChart1»)"},
	{Name: "plOwnExpansion", Text: "module_sum(L.add, " +
		"    L.zero, " +
		"    fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i)), " +
		"    λi:int. laurent_polynomial_coefficient(k, t, f, i) * laurent_monomial(t, i))"},
	{Name: "plChartSumN", Text: "set_mul(L.add, fst(«plPairN»), snd(«plPairN»))"},
	{Name: "plExponentsUpToN", Text: "{i:int | &0 ≤ i ∧ i ≤ n}"},
	{Name: "plPowersUpToN", Text: "{laurent_monomial(t, i) | i:int | &0 ≤ i ∧ i ≤ n}"},
	{Name: "plExponentsBelowN", Text: "{i:int | n < i ∧ i < &0}"},
	{Name: "plClassesBelowN", Text: "{left_coset(L.add, laurent_monomial(t, i), «plChartSumN») | " +
		"    i:int | " +
		"    n < i ∧ i < &0}"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
