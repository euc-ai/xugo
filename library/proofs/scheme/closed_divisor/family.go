// family.go — the closed_divisor family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=closed_divisor.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/closed_divisor go test -run TestRecordFamilyCNF ./library/integrity/gates/

package closed_divisor

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed closed_divisor.cnf.pb
var familyCNF []byte

// _IdealPair is the Go type of a pair of subsets of the field: an ideal pair,
// a closed point.
type _IdealPair = Prod[Set[A], Set[A]]

// family is the family handle. The recorder derives
// closed_divisor/closed_divisor.cnf.pb from the name's basename, and
// the registered entry prefix is `closed_divisor.<Member>`.
var family = registry.NewFamily("scheme/closed_divisor", familyCNF).WithOuterAbbrev(
	smooth_curve.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "scInvertible", Text: "invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁)"},
	{Name: "scDivisor", Text: "closed_divisor(field_ring(L), A₀, A₁, A₀₁)"},
	{Name: "scPair", Text: "closed_divisor_pair(field_ring(L), A₀, A₁, A₀₁)"},
	{Name: "scDegree", Text: "closed_divisor_degree(field_ring(L), k, A₀, A₁)"},
	{Name: "scMul", Text: "lattice_pair_mul(field_ring(L), A₀, A₁)"},
	{Name: "scInverse", Text: "lattice_pair_inverse(field_ring(L), A₀, A₁)"},
	{Name: "scInvertibles", Text: "{N:prod(set(A), set(A)) | «scInvertible»(N)}"},
	{Name: "scPower", Text: "λP:prod(set(A), set(A)). λn:int. " +
		"    COND(&0 ≤ n, " +
		"        monoid_pow(«scMul», (A₀, A₁), «scInverse»(P), num_of_int(n)), " +
		"        monoid_pow(«scMul», (A₀, A₁), P, num_of_int(-n)))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
