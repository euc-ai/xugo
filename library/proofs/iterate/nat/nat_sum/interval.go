// interval.go — Σ read over a segment `m .. n`, the form an indexed
// series is written in.

package nat_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The fold's interval laws, read at natural addition
// ---------------------------------------------------------------------------
//
// Every law here is one of the fold mechanism's interval laws read at
// `+`: unfolding `nat_sum` turns
// the goal into a statement about the fold this one is, and the law
// together with the fact that natural addition folds closes it. What the
// interval itself holds — its recursion on the upper bound, its two ends,
// its image under a shift — is the mechanism's business, not Σ's.

// IntervalClauses — how a sum over an interval computes: against an
// upper bound of 0 the interval holds nothing unless the lower bound is 0,
// and raising the bound by one adds the new point's value, or, where the
// bound has not yet reached the lower one, changes nothing.
var IntervalClauses = intervalClausesThm{family.Add(registry.ProofEntry{
	Name: "IntervalClauses",
	Key:  "prop_5e48236c1b3f11e6",
	Build: family.Theorem(
		"∀m n:num. ∀f:(num → num). "+
			"    sum(m .. 0, f) = COND(m = 0, f(0), 0) ∧ "+
			"    sum(m .. suc(n), f) = COND(m ≤ suc(n), sum(m .. n, f) + f(suc(n)), sum(m .. n, f))",
		func(a *Argument) {
			a.Do(Unfold(NatSumDef),
				By(monoidal.IntervalClauses, MonoidalNatAdd, NeutralNatAdd))
		}),
})}

// IntervalPoint — a sum over an interval whose bounds coincide is the
// summand's value at the point they name.
var IntervalPoint = intervalPointThm{family.Add(registry.ProofEntry{
	Name: "IntervalPoint",
	Key:  "prop_6d2683779dbed87e",
	Build: family.Theorem("∀n:num. ∀f:(num → num). sum(n .. n, f) = f(n)",
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.IntervalPoint, MonoidalNatAdd))
		}),
})}

// PeelLeft — the lowest point of a non-empty interval comes off the
// front of its sum.
var PeelLeft = peelLeftThm{family.Add(registry.ProofEntry{
	Name: "PeelLeft",
	Key:  "prop_c625b1cc75f34f58",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num. ∀f:(num → num).",
			Hypotheses: []string{
				"m ≤ n",
			},
			Conclusion: "sum(m .. n, f) = f(m) + sum(m + 1 .. n, f)",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.PeelLeft, MonoidalNatAdd))
		}),
})}

// PeelRight — and the highest point off the back, once the interval
// reaches past 0.
var PeelRight = peelRightThm{family.Add(registry.ProofEntry{
	Name: "PeelRight",
	Key:  "prop_1e64452b0d99dd83",
	Build: family.Theorem(
		Statement{
			Binders: "∀n m:num. ∀f:(num → num).",
			Hypotheses: []string{
				"0 < n",
				"m ≤ n",
			},
			Conclusion: "sum(m .. n, f) = sum(m .. n - 1, f) + f(n)",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.PeelRight, MonoidalNatAdd))
		}),
})}

// Shift — moving every index of a sum up by p moves its interval up by
// p.
var Shift = shiftThm{family.Add(registry.ProofEntry{
	Name: "Shift",
	Key:  "prop_5ac7debfdc951f48",
	Build: family.Theorem(
		"∀m n p:num. ∀f:(num → num). sum(m .. n, λi:num. f(i + p)) = sum(m + p .. n + p, f)",
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.Shift, MonoidalNatAdd))
		}),
})}

// IntervalCongruence — two summands agreeing between the bounds have the
// same sum.
var IntervalCongruence = intervalCongruenceThm{family.Add(registry.ProofEntry{
	Name: "IntervalCongruence",
	Key:  "prop_a1eac89cf4465801",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num. ∀f g:(num → num).",
			Hypotheses: []string{
				"∀i:num. m ≤ i ∧ i ≤ n ⇒ f(i) = g(i)",
			},
			Conclusion: "sum(m .. n, f) = sum(m .. n, g)",
		},
		func(a *Argument) {
			a.Do(Unfold(NatSumDef), By(monoidal.IntervalCongruence, MonoidalNatAdd))
		}),
})}
