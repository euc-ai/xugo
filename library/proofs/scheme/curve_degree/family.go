// family.go — the curve_degree family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=curve_degree.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/curve_degree go test -run TestRecordFamilyCNF ./library/integrity/gates/

package curve_degree

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed curve_degree.cnf.pb
var familyCNF []byte

// _LatticePair is the Go type of a pair of subsets of the field: a lattice
// pair, a divisor's point.
type _LatticePair = Prod[Set[A], Set[A]]

// family is the family handle. The recorder derives
// curve_degree/curve_degree.cnf.pb from the name's basename, and
// the registered entry prefix is `curve_degree.<Member>`.
var family = registry.NewFamily("scheme/curve_degree", familyCNF).WithOuterAbbrev(
	algebraic_curve.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "wdDegree", Text: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "wdTwist", Text: "lattice_pair_twist(field_ring(L), A₀, A₁)"},
	{Name: "wdPoint", Text: "biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "wdMul", Text: "lattice_pair_mul(field_ring(L), A₀, A₁)"},
	{Name: "wdDivisor", Text: "curve_divisor(field_ring(L), k, A₀, A₁, A₀₁)"},
	{Name: "wdDivisorPair", Text: "curve_divisor_pair(field_ring(L), A₀, A₁, A₀₁)"},
	{Name: "wdInverse", Text: "lattice_pair_inverse(field_ring(L), A₀, A₁)"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
