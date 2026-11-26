// family.go — the real_formal_series family manifest: the registry handle
// every member registers into, the chapter's abbreviation table and the
// real ring's instance, and the family's one shared recorded CNF cache.

package real_formal_series

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

//go:embed real_formal_series.cnf.pb
var familyCNF []byte

// family is the family handle. Its members are series over ℝ: they read
// the real ring's instance, which binds the components the series
// operations read (`add ↦ real_add`, `zero ↦ &0`, …), so that a statement
// spells `polynomial_mul(p, q)` and `polynomial_eval(p, &1)`, and a bare
// `&n` reads as a real (the coerce domain).
// The table names the compound terms the chapter's statements share: the
// real polynomials 1 − T and 1 − Tᵈ in the polynomial chapter's basis,
// the geometric sum 1 + T + … + Tᵈ⁻¹ as the indicator of its indices,
// and an integer-indexed sequence read at its natural indices.
var family = registry.NewFamily("real/real_formal_series", familyCNF).WithCoerceDomain(
	proof.RealDomain).
	WithInstance(comm_ring.CommRing, real_ring.CommRing).WithOuterAbbrev(
	formal_series.ChapterAbbrev).WithAbbrev(Abbrev{
	{Name: "1+…+Tᵈ⁻¹", Text: "λd:num. λn:num. COND(n < d, real_of_num(1), real_of_num(0))"},
	{Name: "coefficients", Text: "λa:(int → real). λn:num. a(n)"},
})
