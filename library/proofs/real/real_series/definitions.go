// definitions.go — the chapter's definitional layer: what it means for
// a series to sum to a number.
//
// A series is its sequence of terms `a : ℕ → ℝ`, and `real_sums(a, s)`
// says its partial sums `Σ_{k∈0 .. n} a(k)` tend to s. As the sequences
// chapter mints no `lim`, this chapter mints no value for the sum of a
// series: a chosen value would mean nothing where the series diverges,
// and every theorem about it would carry a convergence hypothesis that
// the relation carries as its own truth.

package real_series

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealSumsDef — `real_sums(a, s)`: the partial sums of a tend to s.
var RealSumsDef = realSumsDefThm{family.Define(registry.DefEntry{
	Name:      "RealSumsDef",
	Key:       "prop_eb4fb79fc78cbd3e",
	Const:     "real_sums",
	Type:      "(num → real) → real → bool",
	Equations: []string{"∀a:(num → real). ∀s:real. real_sums(a, s) ⇔ (λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s"},
	// The mints of the limit, Σ and the interval.
})}
