// family.go — the serre_duality family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=serre_duality.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/serre_duality go test -run TestRecordFamilyCNF ./library/integrity/gates/

package serre_duality

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed serre_duality.cnf.pb
var familyCNF []byte

// _LatticePair is the Go type of a pair of subsets of the field: a lattice
// pair, a divisor's point.
type _LatticePair = Prod[Set[A], Set[A]]

// family is the family handle. The recorder derives
// serre_duality/serre_duality.cnf.pb from the name's basename, and
// the registered entry prefix is `serre_duality.<Member>`.
var family = registry.NewFamily("scheme/serre_duality", familyCNF).WithOuterAbbrev(
	curve_degree.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "wdDualizingModule", Text: "curve_dualizing_module(field_ring(L), k, t, A₀₁)"},
	{Name: "wdDualizing", Text: "curve_dualizing_pair(L, k, t, A₀, A₁, A₀₁)"},
	{Name: "lineDualizing", Text: "projective_line_pair(L, k, t, -&2)"},
	{Name: "overlapThroughInclusion", Text: "scalar_restriction(λx:A. x, regular_module(«wcOverlap»))"},
	{Name: "containerMaps", Text: "hom_set(«wcRing»(«wcLaurent»), " +
		"    «overlapThroughInclusion», " +
		"    «wcVectors»(«wcLaurent»))"},
	{Name: "omegaChart0", Text: "{φ:A → A | " +
		"    φ ∈ «containerMaps» ∧ image(φ, A₀) ⊆ fst(«lineDualizing»)}"},
	{Name: "omegaChart1", Text: "{φ:A → A | " +
		"    φ ∈ «containerMaps» ∧ image(φ, A₁) ⊆ snd(«lineDualizing»)}"},
	{Name: "inclusionRingMap", Text: "ring_homomorphism(restrict_ring(field_ring(L), «wcLaurent»), " +
		"    restrict_ring(field_ring(L), A₀₁), " +
		"    λx:A. x)"},
	{Name: "containerSpan", Text: "module_span(«wcOverlap», «wdDualizingModule»)"},
	// The coordinate function of a member of the overlap in a basis of it over k[t, 1/t], at the basis and the member, or at those and a basis member.
	{Name: "overlapCoordinates", Text: "module_basis_coordinates(«wcRing»(«wcLaurent»), " +
		"    «wcVectors»(A₀₁))"},
	// The coordinate functionals e* of E, zero off the overlap, and the set of them.
	{Name: "dualBasisE", Text: "image( " +
		"    λe:A. λx:A. COND(x ∈ A₀₁, «overlapCoordinates»(E, x, e), L.zero), E)"},
	{Name: "wdDualizingMaps", Text: "curve_dualizing_maps(L, k, t, A₀, A₁, A₀₁)"},
	{Name: "linePairMaps", Text: "lattice_pair_maps(«wcRing»(«wcLaurent»), " +
		"    «wcField», " +
		"    M, " +
		"    «wcField», " +
		"    «lineDualizing»)"},
	{Name: "evaluationAtOne", Text: "λψ:(A → A → A). λx:A. ψ(x)(L.one)"},
})
