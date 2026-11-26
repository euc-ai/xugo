// definitions.go — the integral of a complex function of a real variable,
// the piecewise smooth paths, the integral along a path, and the two paths
// the theory is computed on: the segment and the circle.

package path_integral

import (
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_integral"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexHasIntegralDef — `complex_has_integral(g, a, b, I)`: the complex
// function g of a real variable has integral I on ⟦a, b⟧, its real and
// imaginary parts having the parts of I as their integrals.
var ComplexHasIntegralDef = complexHasIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexHasIntegralDef",
	Key:   "prop_44125af4639f398b",
	Const: "complex_has_integral",
	Type:  "(real → complex) → real → real → complex → bool",
	Equations: []string{
		"∀g:(real → complex). ∀a b:real. ∀I:complex. " +
			"    complex_has_integral(g, a, b, I) ⇔ " +
			"    real_has_integral(λt:real. re(g(t)), a, b, re(I)) ∧ " +
			"    real_has_integral(λt:real. im(g(t)), a, b, im(I))",
	},
})}

// ComplexIntegralDef — `complex_integral(g, a, b)`: the oriented integral
// of g from a to b, part by part.
var ComplexIntegralDef = complexIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexIntegralDef",
	Key:   "prop_7128958420655796",
	Const: "complex_integral",
	Type:  "(real → complex) → real → real → complex",
	Equations: []string{
		"∀g:(real → complex). ∀a b:real. " +
			"    complex_integral(g, a, b) = " +
			"    complex(real_integral(λt:real. re(g(t)), a, b), real_integral(λt:real. im(g(t)), a, b))",
	},
})}

// PiecewiseSmoothPathDef — `piecewise_smooth_path(γ, γ', a, b)`: a ≤ b,
// γ is continuous on ⟦a, b⟧, and γ' is bounded on ⟦a, b⟧; off a finite set
// k, γ' is the velocity of γ strictly inside the interval and continuous on
// ⟦a, b⟧ ∖ k.
var PiecewiseSmoothPathDef = piecewiseSmoothPathDefThm{family.Define(registry.DefEntry{
	Name:  "PiecewiseSmoothPathDef",
	Key:   "prop_ee9d281fb304dc9e",
	Const: "piecewise_smooth_path",
	Type:  "(real → complex) → (real → complex) → real → real → bool",
	Equations: []string{
		"∀γ γ':(real → complex). ∀a b:real. " +
			"    piecewise_smooth_path(γ, γ', a, b) ⇔ " +
			"    a ≤ b ∧ " +
			"    real_continuous_on(⟦a, b⟧, λt:real. re(γ(t))) ∧ " +
			"    real_continuous_on(⟦a, b⟧, λt:real. im(γ(t))) ∧ " +
			"    ∃k:set(real). " +
			"        finite(k) ∧ " +
			"        (∀t:real. a < t ∧ t < b ∧ t ∉ k ⇒ path_derivative_at(γ, t, γ'(t))) ∧ " +
			"        (∃B:real. ∀t:real. a ≤ t ∧ t ≤ b ⇒ |γ'(t)| ≤ B) ∧ " +
			"        real_continuous_on(⟦a, b⟧ ∖ k, λt:real. re(γ'(t))) ∧ " +
			"        real_continuous_on(⟦a, b⟧ ∖ k, λt:real. im(γ'(t)))",
	},
})}

// PathIntegralDef — `path_integral(f, γ, γ', a, b)`: the integral of f
// along γ, ∫_a^b f(γ(t))·γ'(t) dt.
var PathIntegralDef = pathIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "PathIntegralDef",
	Key:   "prop_2701f2f67d6d8088",
	Const: "path_integral",
	Type:  "(complex → complex) → (real → complex) → (real → complex) → real → real → complex",
	Equations: []string{
		"∀f:(complex → complex). ∀γ γ':(real → complex). ∀a b:real. " +
			"    path_integral(f, γ, γ', a, b) = complex_integral(λt:real. f(γ(t)) * γ'(t), a, b)",
	},
	Deps: []registry.EntryLike{ComplexIntegralDef},
})}

// SegmentPathDef — `segment_path(z, w)`: the path z + t·(w − z), at z when
// t = 0 and at w when t = 1, with the constant velocity w − z; on ⟦0, 1⟧ it
// runs along the segment from z to w.
var SegmentPathDef = segmentPathDefThm{family.Define(registry.DefEntry{
	Name:      "SegmentPathDef",
	Key:       "prop_5e6c2f0e27ef30a7",
	Const:     "segment_path",
	Type:      "complex → complex → real → complex",
	Equations: []string{"∀z w:complex. ∀t:real. segment_path(z, w, t) = z + &t * (w - z)"},
})}

// CirclePathDef — `circle_path(c, r)`: the path c + r·exp(it), with
// velocity i·r·exp(it) of the constant speed |r|; on ⟦0, 2π⟧ it runs once
// counterclockwise round the circle of radius |r| about c.
var CirclePathDef = circlePathDefThm{family.Define(registry.DefEntry{
	Name:      "CirclePathDef",
	Key:       "prop_afe079e93765d292",
	Const:     "circle_path",
	Type:      "complex → real → real → complex",
	Equations: []string{"∀c:complex. ∀r t:real. circle_path(c, r, t) = c + &r * exp(complex_i * &t)"},
})}
