package event_integral

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	_ "github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed event_integral.cnf.pb
var familyCNF []byte

// family is the family handle; an unanchored numeral `&k` is a real one.
// Its table spells the cut every law here reads:
//
//   - `«cutOff»(E, h, x)`: h cut to 0 off E, read at x — the integrand
//     whose integral over the whole carrier is the integral of h over E.
var family = registry.NewFamily("measure/event_integral", familyCNF).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "cutOff", Text: "λE:set(A). λh:(A → real). λx:A. COND(x ∈ E, h(x), &0)"},
	})
