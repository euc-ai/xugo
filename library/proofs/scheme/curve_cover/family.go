// family.go — the curve_cover registry and its shared replay record.

package curve_cover

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed curve_cover.cnf.pb
var familyCNF []byte

var family = registry.NewFamily("scheme/curve_cover", familyCNF).WithAbbrev(Abbrev{
	{Name: "ccData", Text: "riemann_hurwitz_data(L, K, k, t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)"},
	{Name: "ccRamification", Text: "ramification_degree(L, K, k, A₀, A₁, A₀₁, B₀, B₁, B₀₁)"},
	{Name: "ccInverseDifferent", Text: "inverse_different(L, K, A₀, A₁, B₀, B₁)"},
})
