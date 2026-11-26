// definitions.go — the Lindeberg sum of a row of random variables, and its sign.

package lindeberg_bound

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/registry"
)

// LindebergSumDef — `lindeberg_sum(Ω, S, μ, n, ξ, ε)` is the sum over
// k < n of the expectation of ξ(k)² on the event where |ξ(k)| exceeds ε:
// the part of the row's second moments carried by its large values.
var LindebergSumDef = lindebergSumDefThm{family.Define(registry.DefEntry{
	Name:  "LindebergSumDef",
	Key:   "prop_89bceb66c59fbc3f",
	Const: "lindeberg_sum",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"num → " +
		"(num → A → real) → " +
		"real → " +
		"real",
	Reading: "The event is strict, ε < |ξ(k, x)|. At n = 0 the sum is 0. Applied up to the " +
		"row, lindeberg_sum(Ω, S, μ, n, ξ) is the function of ε a Lindeberg condition speaks of.",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀n:num. " +
			"∀ξ:(num → A → real). " +
			"∀ε:real. " +
			"    lindeberg_sum(Ω, S, μ, n, ξ, ε) = " +
			"    real_sum({k:num | k < n}, " +
			"        λk:num. event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x)))",
	},
})}

// LindebergSumNonnegative — a Lindeberg sum is nonnegative: each of its terms integrates a
// square over an event.
var LindebergSumNonnegative = lindebergSumNonnegativeThm{family.Add(registry.ProofEntry{
	Name: "LindebergSumNonnegative",
	Key:  "prop_890cf9317fc32d26",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀n:num. " +
			"∀ξ:(num → A → real). " +
			"∀ε:real.",
		Conclusion: "&0 ≤ lindeberg_sum(Ω, S, μ, n, ξ, ε)",
		Abbrev: Abbrev{
			{Name: "tail", Text: "λk:num. {x:A | ε < |ξ(k, x)|}"},
			{Name: "tailSquare", Text: "λk:num. λx:A. COND(x ∈ «tail»(k), ξ(k, x) * ξ(k, x), &0)"},
			{Name: "tailValue", Text: "λk:num. event_integral(Ω, S, μ, «tail»(k), λx:A. ξ(k, x) * ξ(k, x))"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		n *Expr[Nat], ξ *Arrow2[Nat, A, Real], ε *Expr[Real]) {
		terms := a.Have(
			"every squared tail contributes a nonnegative integral",
			"∀k:num. k ∈ {j:num | j < n} ⇒ &0 ≤ «tailValue»(k)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				b.Assume()
				pointwise := b.Have(
					"the event integrand is nonnegative",
					"∀x:A. x ∈ Ω ⇒ &0 ≤ «tailSquare»(k, x)",
					Derive(func(d *Argument) {
						d.FixAs[A]()
						d.Assume()
						d.Cases(d.Term("x ∈ «tail»(k)"))
						d.When(
							"on the tail the integrand is a square",
							func(e *Argument, inTail Fact) {
								e.Show(
									"a square is nonnegative",
									ByArith(inTail))
							})
						d.Otherwise(
							"off the tail the integrand is zero",
							func(e *Argument, offTail Fact) {
								e.Show(
									"zero is nonnegative",
									ByArith(offTail))
							})
					}))
				b.Show(
					"integrate the nonnegative tail integrand",
					Simp(Fwd(event_integral.EventIntegralDef)),
					By(
						pointwise,
						measure_integral.IntegralNonneg.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("«tailSquare»(k)"))))
			}))
		indices := a.TermAs[Set[Nat]]("{j:num | j < n}")
		summand := a.TermAs[Fun[Nat, Real]]("«tailValue»")
		a.Show(
			"the finite sum is nonnegative",
			Simp(Fwd(LindebergSumDef)),
			By(terms, real_sum.Nonneg.At(indices, summand)))
	}),
})}
