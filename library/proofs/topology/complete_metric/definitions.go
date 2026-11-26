// definitions.go — the chapter's definitional layer: a sequence of points
// of M converging to a point of M, a Cauchy sequence of points of M, a
// complete metric space, and a totally bounded subset.
//
// Convergence, Cauchy-ness and total boundedness read the carrier and
// the distance as their first two arguments and declare them implicit,
// as `ball` does: under a law over `metric_space(M, d)` a statement may
// write `metric_cauchy(x)`. Completeness is a property of the pair and
// is asked of subsets with the same distance (`metric_complete(s, d)`),
// so it spells both, as `hausdorff(T)` spells its topology.

package complete_metric

import (
	"github.com/euc-ai/xugo/library/registry"
)

// MetricConvergesToDef — `metric_converges_to(M, d, x, l)`: x is a
// sequence of points of M, l is a point of M, and every positive distance
// about l holds all the terms past some index. The ε-N sentence of
// real_sequences' `a ⟶ l`, with d(x(n), l) for |a(n) − l|.
var MetricConvergesToDef = metricConvergesToDefThm{family.Define(registry.DefEntry{
	Name:     "MetricConvergesToDef",
	Key:      "prop_f95a1f4da0fc47fc",
	Const:    "metric_converges_to",
	Type:     "set(A) → (A → A → real) → (num → A) → A → bool",
	Implicit: []string{"M", "d"},
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). ∀x:(num → A). ∀l:A. " +
			"    metric_converges_to(M, d, x, l) ⇔ " +
			"    l ∈ M ∧ (∀n:num. x(n) ∈ M) ∧ ∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. N ≤ n ⇒ d(x(n), l) < ε",
	},
})}

// MetricCauchyDef — `metric_cauchy(M, d, x)`: x is a sequence of points of
// M whose terms past some index lie within any positive distance of each
// other.
var MetricCauchyDef = metricCauchyDefThm{family.Define(registry.DefEntry{
	Name:     "MetricCauchyDef",
	Key:      "prop_4a76f7bd6e5a26db",
	Const:    "metric_cauchy",
	Type:     "set(A) → (A → A → real) → (num → A) → bool",
	Implicit: []string{"M", "d"},
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). ∀x:(num → A). " +
			"    metric_cauchy(M, d, x) ⇔ " +
			"    (∀n:num. x(n) ∈ M) ∧ ∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ d(x(m), x(n)) < ε",
	},
})}

// MetricCompleteDef — `metric_complete(M, d)`: every Cauchy sequence of
// points of M converges to a point of M.
var MetricCompleteDef = metricCompleteDefThm{family.Define(registry.DefEntry{
	Name:  "MetricCompleteDef",
	Key:   "prop_d681e7266ba6609",
	Const: "metric_complete",
	Type:  "set(A) → (A → A → real) → bool",
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). " +
			"    metric_complete(M, d) ⇔ " +
			"    ∀x:(num → A). metric_cauchy(M, d, x) ⇒ ∃l:A. metric_converges_to(M, d, x, l)",
	},
	Deps: []registry.EntryLike{MetricCauchyDef, MetricConvergesToDef},
})}

// TotallyBoundedDef — `totally_bounded(M, d, s)`: s lies in M, and for
// every positive distance finitely many points of s come within it of
// every point of s.
var TotallyBoundedDef = totallyBoundedDefThm{family.Define(registry.DefEntry{
	Name:     "TotallyBoundedDef",
	Key:      "prop_5ac45b5ada00baa0",
	Const:    "totally_bounded",
	Type:     "set(A) → (A → A → real) → set(A) → bool",
	Implicit: []string{"M", "d"},
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). ∀s:set(A). " +
			"    totally_bounded(M, d, s) ⇔ " +
			"    s ⊆ M ∧ " +
			"    ∀ε:real. &0 < ε ⇒ ∃k:set(A). finite(k) ∧ k ⊆ s ∧ ∀y:A. y ∈ s ⇒ ∃x:A. x ∈ k ∧ d(x, y) < ε",
	},
})}

// UniformlyContinuousMap — `uniformly_continuous_map(M, d, N, e, f)`: f
// carries M into N, and one δ serves every point for each ε. Both spaces
// are spelled.
var UniformlyContinuousMap = uniformlyContinuousMapThm{family.DefineStructure(registry.DefEntry{
	Name:    "UniformlyContinuousMap",
	Key:     "prop_7cd7a62f0d612353",
	Const:   "uniformly_continuous_map",
	Subject: "f",
	Type:    "set(A) → (A → A → real) → set(B) → (B → B → real) → (A → B) → bool",
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real). ∀f:(A → B). " +
			"    uniformly_continuous_map(M, d, N, e, f) ⇔ " +
			"    (∀x:A. x ∈ M ⇒ f(x) ∈ N) ∧ " +
			"    ∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀x y:A. x ∈ M ∧ y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < ε",
	},
})}

// LipschitzMap — `lipschitz_map(M, d, N, e, f)`: f carries M into N and
// stretches no distance by more than a fixed factor.
var LipschitzMap = lipschitzMapThm{family.DefineStructure(registry.DefEntry{
	Name:    "LipschitzMap",
	Key:     "prop_8362a20763df3796",
	Const:   "lipschitz_map",
	Subject: "f",
	Type:    "set(A) → (A → A → real) → set(B) → (B → B → real) → (A → B) → bool",
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real). ∀f:(A → B). " +
			"    lipschitz_map(M, d, N, e, f) ⇔ " +
			"    (∀x:A. x ∈ M ⇒ f(x) ∈ N) ∧ ∃k:real. ∀x y:A. x ∈ M ∧ y ∈ M ⇒ e(f(x), f(y)) ≤ k * d(x, y)",
	},
})}
