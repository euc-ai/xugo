// definitions.go — the definitional layer: the recurrence T·a′ = m·a
// between a series and its counting sequence, the substitution T ↦ Tᵈ,
// and the formal exponential as the recurrence's chosen solution.

package formal_series

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

// SeriesRecurrenceDef — `series_recurrence(R, a, m)`: the series a and its
// counting sequence m, every term of both in the carrier, satisfy a(0) = 1,
// m(0) = 0 and, for n positive, n·a(n) = Σ_{0<i≤n} m(i)·a(n − i), the
// factor n being n ones summed in the ring. That is T·a′ = m·a: the
// coefficient of Tⁿ on the left is n·a(n), and on the right the
// convolution, whose term at i = 0 is m(0)·a(n) = 0; at n = 0 both sides
// vanish.
var SeriesRecurrenceDef = seriesRecurrenceDefThm{family.Define(registry.DefEntry{
	Name:  "SeriesRecurrenceDef",
	Key:   "prop_f1b3934a1a32321e",
	Deps:  []registry.EntryLike{},
	Const: "series_recurrence",
	Type:  "ring_ops(A) → (num → A) → (num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀a m:(num → A). " +
			"    series_recurrence(R, a, m) ⇔ " +
			"    a(0) = R.one ∧ " +
			"    m(0) = R.zero ∧ " +
			"    (∀n:num. a(n) ∈ R.carrier ∧ m(n) ∈ R.carrier) ∧ " +
			"    (∀n:num. " +
			"        0 < n ⇒ " +
			"        R.mul(monoid_pow(R.add, R.zero, R.one, n), a(n)) = " +
			"        module_sum(R.add, R.zero, {i:num | 0 < i ∧ i ≤ n}, λi:num. R.mul(m(i), a(n - i))))",
	},
})}

// SeriesSubstituteDef — `series_substitute(R, a, d)`: the series a(Tᵈ),
// whose coefficient at the index d·j is a's at j, and zero at an index
// that is no multiple of d. The quotient j is chosen by ε as a solution of
// d·j = n; at d = 0 every j solves 0·j = 0, the chosen quotient is junk,
// and that is why the substitution laws assume 0 < d.
var SeriesSubstituteDef = seriesSubstituteDefThm{family.Define(registry.DefEntry{
	Name:  "SeriesSubstituteDef",
	Key:   "prop_ec305241e94e15f2",
	Deps:  []registry.EntryLike{},
	Const: "series_substitute",
	Type:  "ring_ops(A) → (num → A) → num → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀a:(num → A). ∀d n:num. " +
			"    series_substitute(R, a, d, n) = COND(∃j:num. d * j = n, a(εj:num. d * j = n), R.zero)",
	},
})}

// FormalExpDef — `formal_exp_zero(R, x)`: the formal exponential exp(x) of
// a series x with x(0) = 0 — the "_zero" of the name — chosen by ε as a
// solution of the recurrence with counting sequence m(n) = n·x(n). The
// recurrence then reads T·a′ = (T·x′)·a, and its solution with a(0) = 1 is
// exp(x).
var FormalExpDef = formalExpDefThm{family.Define(registry.DefEntry{
	Name:  "FormalExpDef",
	Key:   "prop_4da848b8ee203f29",
	Deps:  []registry.EntryLike{SeriesRecurrenceDef},
	Const: "formal_exp_zero",
	Type:  "ring_ops(A) → (num → A) → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀x:(num → A). " +
			"    formal_exp_zero(R, x) = " +
			"    εa:(num → A). " +
			"        series_recurrence(R, a, λn:num. R.mul(monoid_pow(R.add, R.zero, R.one, n), x(n)))",
	},
})}
