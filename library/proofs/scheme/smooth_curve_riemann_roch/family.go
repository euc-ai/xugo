// family.go — the smooth_curve_riemann_roch family manifest: the registry handle
// every member registers into, and the family's ONE shared recorded CNF
// cache.
//
//	XUGO_RECORD_FAMILY_CNF=smooth_curve_riemann_roch.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=scheme/smooth_curve_riemann_roch go test -run TestRecordFamilyCNF ./library/integrity/gates/

package smooth_curve_riemann_roch

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed smooth_curve_riemann_roch.cnf.pb
var familyCNF []byte

// _IdealPair is the Go type of a pair of subsets of the field: an ideal pair,
// a closed point.
type _IdealPair = Prod[Set[A], Set[A]]

// family is the family handle. The recorder derives
// smooth_curve_riemann_roch/smooth_curve_riemann_roch.cnf.pb from the name's basename, and
// the registered entry prefix is `smooth_curve_riemann_roch.<Member>`.
var family = registry.NewFamily("scheme/smooth_curve_riemann_roch", familyCNF).WithOuterAbbrev(
	closed_divisor.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "scSections", Text: "λN:prod(set(A), set(A)). " +
		"    module_dim(restrict_ring(field_ring(L), k), " +
		"        lattice_pair_h0(regular_module(field_ring(L)), N))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
