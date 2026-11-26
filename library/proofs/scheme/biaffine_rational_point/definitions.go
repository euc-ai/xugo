// definitions.go — the rational points of a biaffine datum, each held by
// its ideal in each chart, and the chart a point lies on with its ideal
// there.

package biaffine_rational_point

import (
	"github.com/euc-ai/xugo/library/registry"
)

// BiaffineRationalPointDef — `biaffine_rational_point(R, k, A₀, A₁, P)`:
// the pair of ideals P = (P₀, P₁) is a k-rational point, given by its
// ideal in each chart — the chart itself where the point lies off it, the
// ideal of a k-rational point of the chart, proper with residues in k,
// where it lies on it. It lies on at
// least one chart, and the two ideals generate the same ideal of the
// overlap R: a point on both charts lies on the overlap and generates a
// proper ideal there, a point on one chart only generates all of R.
var BiaffineRationalPointDef = biaffineRationalPointDefThm{family.Define(registry.DefEntry{
	Name:  "BiaffineRationalPointDef",
	Key:   "prop_28e4367dddd754f3",
	Const: "biaffine_rational_point",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁:set(A). ∀P:prod(set(A), set(A)). " +
			"    biaffine_rational_point(R, k, A₀, A₁, P) ⇔ " +
			"    (fst(P) = A₀ ∨ rational_ideal(R, k, A₀, fst(P))) ∧ " +
			"    (snd(P) = A₁ ∨ rational_ideal(R, k, A₁, snd(P))) ∧ " +
			"    ¬(fst(P) = A₀ ∧ snd(P) = A₁) ∧ " +
			"    ideal_span(R, fst(P)) = ideal_span(R, snd(P)) ∧ " +
			"    (¬(fst(P) = A₀) ∧ ¬(snd(P) = A₁) ⇒ ¬(R.one ∈ ideal_span(R, fst(P))))",
	},
})}

// PointChartDef — `point_chart(A₀, A₁, P)`: the chart a point P lies on, A₀
// unless P's first ideal is the whole of A₀, which says P lies off chart 0.
var PointChartDef = pointChartDefThm{family.Define(registry.DefEntry{
	Name:  "PointChartDef",
	Key:   "prop_10ecf893aac5c16f",
	Const: "point_chart",
	Type:  "set(A) → set(A) → prod(set(A), set(A)) → set(A)",
	Equations: []string{
		"∀A₀ A₁:set(A). ∀P:prod(set(A), set(A)). point_chart(A₀, A₁, P) = COND(fst(P) = A₀, A₁, A₀)",
	},
})}

// PointIdealDef — `point_ideal(A₀, P)`: P's ideal in its chart
// point_chart(A₀, A₁, P), the second component where P lies off chart 0 and
// the first otherwise.
var PointIdealDef = pointIdealDefThm{family.Define(registry.DefEntry{
	Name:  "PointIdealDef",
	Key:   "prop_714b63815099b2ae",
	Const: "point_ideal",
	Type:  "set(A) → prod(set(A), set(A)) → set(A)",
	Equations: []string{
		"∀A₀:set(A). ∀P:prod(set(A), set(A)). point_ideal(A₀, P) = COND(fst(P) = A₀, snd(P), fst(P))",
	},
})}
