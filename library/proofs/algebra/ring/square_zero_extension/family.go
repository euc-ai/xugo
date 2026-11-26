// family.go — the square_zero_extension family manifest: the registry
// handle every member registers into, and the family's ONE shared
// recorded CNF cache.
//
//	XUGO_RECORD_FAMILY_CNF=square_zero_extension.<Name> go test -run TestRecordFamilyCNF ./library/integrity/gates/
//	XUGO_FAMILY_CNF_GC=algebra/ring/square_zero_extension go test -run TestRecordFamilyCNF ./library/integrity/gates/

package square_zero_extension

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed square_zero_extension.cnf.pb
var familyCNF []byte

// family is the family handle. The recorder derives
// square_zero_extension/square_zero_extension.cnf.pb from the name's
// basename, and the registered entry prefix is
// `square_zero_extension.<Member>`.
var family = registry.NewFamily("algebra/ring/square_zero_extension", familyCNF).WithAbbrev(Abbrev{
	{Name: "baseLocalization", Text: "is_localization_on(S, monoid_powers(S.mul, S.one, t), S', ρ)"},
	{Name: "coefficientLocalization", Text: "is_module_localization_on(S, " +
		"    monoid_powers(S.mul, S.one, t), " +
		"    S', " +
		"    ρ, " +
		"    N, " +
		"    N', " +
		"    ν)"},
	{Name: "graph", Text: "twisted_graph(N, ring_kernel(S.zero, P.carrier, ε))"},
	{Name: "conormal", Text: "conormal_hom(P, S, ε, N)"},
	{Name: "extension", Text: "square_zero_graph(P, h, S, ε, N)"},
	{Name: "derivation", Text: "derivation_on(R, P, h, scalar_restriction(ε, N))"},
	{Name: "lift", Text: "square_zero_lift(R, P, h, ε, E)"},
	{Name: "extract", Text: "extract_conormal(P, S, ε, N, E)"},
	{Name: "coefficient", Text: "λe:C. inverse_on(N.carrier, E.inclusion, e)"},
	{Name: "split", Text: "λS:ring_ops(B). λf:(A → B). λN:module_ops(B, D). " +
		"    mk_square_zero(split_square_zero(S, λy:B. y, N), " +
		"        λa:A. (f(a), N.zero), " +
		"        λn:D. (S.zero, n), " +
		"        λz:prod(B, D). fst(z))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
