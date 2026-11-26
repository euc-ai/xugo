// definitions.go — the chapter's definitional layer beyond the
// structure: the open and the closed ball about a point, and the family
// of open sets the balls determine.
//
// Each constant reads the carrier and the distance as its first two
// arguments and declares them implicit: where binders named `M` and `d`
// are in scope — a law over `metric_space(M, d)` — a statement writes
// `ball(x, r)` or `metric_topology` and the parser completes the two
// from those binders. A statement that uses no axiom spells them, as
// the definitions themselves do.

package metric_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

// BallDef — `ball(M, d, x, r)`: the points of M at distance less than r
// from x. The centre is not asked to lie in M; a law that needs it to
// says so.
var BallDef = ballDefThm{family.Define(registry.DefEntry{
	Name:     "BallDef",
	Key:      "prop_67073150323b7dcd",
	Const:    "ball",
	Type:     "set(A) → (A → A → real) → A → real → set(A)",
	Implicit: []string{"M", "d"},
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). ∀x:A. ∀r:real. ball(M, d, x, r) = {y:A | y ∈ M ∧ d(x, y) < r}",
	},
	// The mints of the comprehension, membership and `<`.
})}

// ClosedBallDef — `closed_ball(M, d, x, r)`: the points of M at distance
// at most r from x.
var ClosedBallDef = closedBallDefThm{family.Define(registry.DefEntry{
	Name:     "ClosedBallDef",
	Key:      "prop_5e773f549330f34d",
	Const:    "closed_ball",
	Type:     "set(A) → (A → A → real) → A → real → set(A)",
	Implicit: []string{"M", "d"},
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). ∀x:A. ∀r:real. " +
			"    closed_ball(M, d, x, r) = {y:A | y ∈ M ∧ d(x, y) ≤ r}",
	},
	// The mints of the comprehension, membership and `≤`.
})}

// MetricTopologyDef — `metric_topology(M, d)`: the subsets u of M each
// of whose points has a ball about it inside u. It is the family of open
// sets itself, so "u is open" is `u ∈ metric_topology(M, d)`, as it is
// in the topology chapters.
var MetricTopologyDef = metricTopologyDefThm{family.Define(registry.DefEntry{
	Name:     "MetricTopologyDef",
	Key:      "prop_459b1f11d161fb12",
	Const:    "metric_topology",
	Type:     "set(A) → (A → A → real) → set(set(A))",
	Implicit: []string{"M", "d"},
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). " +
			"    metric_topology(M, d) = " +
			"    {u:set(A) | u ⊆ M ∧ ∀x:A. x ∈ u ⇒ ∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ u}",
	},
	// The mints of the comprehension, inclusion, membership, `&`, `<`
	// and the ball.
	Deps: []registry.EntryLike{BallDef},
})}

// MetricBoundedDef — `metric_bounded(M, d, s)`: s lies in M and the
// distances between its points are bounded. No centre is named, so the
// empty set is bounded in the empty space too. The carrier and the
// distance are implicit under a law over them.
var MetricBoundedDef = metricBoundedDefThm{family.Define(registry.DefEntry{
	Name: "MetricBoundedDef",
	Key:  "prop_c278a4888a7d6aa8",
	Reading: "No centre is named, so the bound is between points of s and the " +
		"empty set is bounded in the empty space. metric_space(M, d) asks nothing " +
		"of d off M, and a law about a ball carries x ∈ M for the same reason.",
	Const:    "metric_bounded",
	Type:     "set(A) → (A → A → real) → set(A) → bool",
	Implicit: []string{"M", "d"},
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). ∀s:set(A). " +
			"    metric_bounded(M, d, s) ⇔ s ⊆ M ∧ ∃b:real. ∀x y:A. x ∈ s ∧ y ∈ s ⇒ d(x, y) ≤ b",
	},
})}

// MetrizableSpaceDef — `metrizable_space(T)`: the topology is the topology
// of some distance on some set.
var MetrizableSpaceDef = metrizableSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "MetrizableSpaceDef",
	Key:   "prop_4210eaf971842406",
	Const: "metrizable_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    metrizable_space(T) ⇔ " +
			"    ∃M:set(A). ∃d:(A → A → real). metric_space(M, d) ∧ T = metric_topology(M, d)",
	},
	Deps: []registry.EntryLike{MetricSpace, MetricTopologyDef},
})}

// ProductMetricDef — `product_metric(d, e)`: the distance between two pairs
// is the larger of the distances between their components, so a ball of
// the product is the rectangle of the two balls.
var ProductMetricDef = productMetricDefThm{family.Define(registry.DefEntry{
	Name:  "ProductMetricDef",
	Key:   "prop_2eec3296734d8ed8",
	Const: "product_metric",
	Type:  "(A → A → real) → (B → B → real) → prod(A, B) → prod(A, B) → real",
	Equations: []string{
		"∀d:(A → A → real). ∀e:(B → B → real). ∀p q:prod(A, B). " +
			"    product_metric(d, e, p, q) = max(d(fst(p), fst(q)), e(snd(p), snd(q)))",
	},
})}

// CountableProductMetricDef — `countable_product_metric(J, d, h)`: the
// distance between two functions on the index type is the supremum, over
// the places n, of the distance d(h(n)) between their coordinates at h(n),
// clipped at one and weighted by 1/(n + 1), where h(n) is an index of J;
// a place whose index is not in J contributes zero. Every term is at most
// one, so the supremum is of a set bounded above.
var CountableProductMetricDef = countableProductMetricDefThm{family.Define(registry.DefEntry{
	Name:  "CountableProductMetricDef",
	Key:   "prop_8bc0c522aabfc454",
	Const: "countable_product_metric",
	Type:  "set(I) → (I → A → A → real) → (num → I) → (I → A) → (I → A) → real",
	Equations: []string{
		"∀J:set(I). ∀d:(I → A → A → real). ∀h:(num → I). ∀f g:(I → A). " +
			"    countable_product_metric(J, d, h, f, g) = " +
			"    sup(image( " +
			"            λn:num. COND(h(n) ∈ J, min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1), &0), " +
			"            𝕌))",
	},
})}
