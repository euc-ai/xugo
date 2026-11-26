package lp_space

import (
	_ "embed"
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	_ "github.com/euc-ai/xugo/library/proofs/measure/almost_everywhere_function"
	_ "github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_convex"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed lp_space.cnf.pb
var familyCNF []byte

// family is the family handle; an unanchored numeral `&k` is a real one.
// Its table spells the integral both lp_seminorm and lp_functions are
// defined by:
//
//   - `«absPow»(p, f)`: the function x ↦ |f(x)|^p;
//   - `«absPowIntegral»(Ω, S, μ, p, f)`: its integral in [0, ∞], finite
//     exactly for the functions of Lᵖ.
var family = registry.NewFamily("analysis/lp_space", familyCNF).
	WithCoerceDomain(RealDomain).
	WithAbbrev(Abbrev{
		{Name: "absPow", Text: "λp:real. λf:(A → complex). λx:A. real_rpow(|f(x)|, p)"},
		{Name: "absPowIntegral", Text: "λΩ:set(A). " +
			"λS:set(set(A)). " +
			"λμ:(set(A) → extended_nonneg_real). " +
			"λp:real. " +
			"λf:(A → complex). " +
			"    nonneg_integral(Ω, S, μ, λx:A. extended_of_real(real_rpow(|f(x)|, p)))"},
	})
