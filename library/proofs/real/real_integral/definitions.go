// definitions.go — the chapter's definitional layer: what it means for a
// function to have an integral over a closed interval, and the integral
// as a value of the function and its two bounds.
//
// A tagged partition of ⟦a, b⟧ into n + 1 pieces is a run of points
// a = p(0), p(1), …, p(n + 1) = b with a tag t(k) in each piece,
// p(k) ≤ t(k) ≤ p(k + 1); its Riemann sum for f is
// Σ_{k∈0 .. n} f(t(k)) * (p(k + 1) - p(k)). The partition is fine to δ
// when every piece is shorter than δ, and f has integral I on ⟦a, b⟧ when
// for every ε some δ brings the Riemann sum of every partition fine to δ
// within ε of I.

package real_integral

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealHasIntegralDef — `real_has_integral(f, a, b, I)`: the Riemann sums
// of f over the tagged partitions of ⟦a, b⟧ tend to I as the pieces
// shrink. The bound a ≤ b is part of the definition: a reversed interval
// has no partition, so without it every number would be its integral.
var RealHasIntegralDef = realHasIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "RealHasIntegralDef",
	Key:   "prop_892fb9e1534a13bb",
	Const: "real_has_integral",
	Type:  "(real → real) → real → real → real → bool",
	Equations: []string{
		"∀f:(real → real). ∀a b I:real. " +
			"    real_has_integral(f, a, b, I) ⇔ " +
			"    a ≤ b ∧ " +
			"    (∀ε:real. " +
			"        &0 < ε ⇒ " +
			"        ∃δ:real. " +
			"            &0 < δ ∧ " +
			"            (∀n:num. ∀p t:(num → real). " +
			"                «finePartition»(a, b, δ, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - I| < ε))",
	},
	Reading: "The pieces of a partition are not asked to be non-empty, so a " +
		"partition of ⟦a, a⟧ is a run of points all equal to a, and every function " +
		"has integral 0 there. Only the mesh is bounded, never the number of pieces.",
})}

// RealIntegralDef — `real_integral(f, a, b)`: the oriented integral, the
// integral of f over ⟦a, b⟧ when a ≤ b and the negative of its integral
// over ⟦b, a⟧ otherwise.
var RealIntegralDef = realIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "RealIntegralDef",
	Key:   "prop_e606b43157fe76bf",
	Const: "real_integral",
	Type:  "(real → real) → real → real → real",
	Equations: []string{
		"∀f:(real → real). ∀a b:real. " +
			"    real_integral(f, a, b) = " +
			"    COND(a ≤ b, " +
			"        εI:real. real_has_integral(f, a, b, I), " +
			"        -(εI:real. real_has_integral(f, b, a, I)))",
	},
	Deps: []registry.EntryLike{RealHasIntegralDef},
	Reading: "The value is a choice: where f has no integral over the interval it " +
		"is some real no theorem determines, so a statement about real_integral(f, a, b) " +
		"carries the integral it is about as a hypothesis (HasIntegralValue reads it off).",
})}
