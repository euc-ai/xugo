// family.go — the algebraic_curve family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=algebraic_curve.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/algebraic_curve go test -run TestRecordFamilyCNF ./library/integrity/gates/

package algebraic_curve

import (
	_ "embed"

	// The chapters whose constants the definitions spell, initialized
	// before them.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed algebraic_curve.cnf.pb
var familyCNF []byte

// _LatticePair is the Go type of a pair of subsets of the field: a lattice
// pair, a divisor's point.
type _LatticePair = Prod[Set[A], Set[A]]

// family is the family handle. The recorder derives
// algebraic_curve/algebraic_curve.cnf.pb from the name's basename, and
// the registered entry prefix is `algebraic_curve.<Member>`.
var family = registry.NewFamily("scheme/algebraic_curve", familyCNF).WithAbbrev(Abbrev{
	{Name: "wdInvertible", Text: "invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁)"},
	{Name: "wcDatum", Text: "curve_over_line(L, k, t, A₀, A₁, A₀₁)"},
	{Name: "wcOverlap", Text: "restrict_ring(field_ring(L), A₀₁)"},
	{Name: "wcField", Text: "regular_module(field_ring(L))"},
	{Name: "wdGenus", Text: "int_of_num(curve_genus(field_ring(L), k, A₀, A₁, A₀₁))"},
	{Name: "wcRing", Text: "restrict_ring(field_ring(L))"},
	{Name: "wcLaurent", Text: "ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)"},
	{Name: "wcVectors", Text: "restrict_module(regular_module(field_ring(L)))"},
	{Name: "wcPolynomials", Text: "polynomial_image(field_ring(L), k, t)"},
	{Name: "wcInversePolynomials", Text: "polynomial_image(field_ring(L), k, L.inv(t))"},
	{Name: "wcBasisOfChart", Text: "module_basis(«wcRing»(«wcPolynomials»), «wcVectors»(A₀))"},
	{Name: "wcBasisOfInverseChart", Text: "module_basis(«wcRing»(«wcInversePolynomials»), " +
		"    «wcVectors»(A₁))"},
	{Name: "wdScalars", Text: "restrict_ring(«wcOverlap», k)"},
	{Name: "wdH1", Text: "lattice_pair_h1(«wcOverlap», «wcField»)"},
	{Name: "ambientOnLine", Text: "lattice_pair_ambient(«wcRing»(«wcLaurent»), «wcField», M)"},
	{Name: "ambientOnCurve", Text: "lattice_pair_ambient(«wcOverlap», «wcField», M)"},
	{Name: "wdH1Dim", Text: "lattice_pair_h1_dim(«wcOverlap», k, «wcField»)"},
	{Name: "wcRationalFunctions", Text: "field_adjoin(L, k, {t})"},
	{Name: "wdEuler", Text: "lattice_pair_euler(«wcOverlap», k, «wcField»)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
