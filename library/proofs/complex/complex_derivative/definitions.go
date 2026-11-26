// definitions.go — the complex derivative at a point, a function
// holomorphic on a set, and the velocity of a path, a complex function of a
// real variable.

package complex_derivative

import (
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexDerivativeAtDef — `complex_derivative_at(f, c, l)`: the
// difference quotient of f at c tends to l. Its value at c itself, a
// division by zero, is not looked at.
var ComplexDerivativeAtDef = complexDerivativeAtDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexDerivativeAtDef",
	Key:   "prop_61375bc93df2e1a0",
	Const: "complex_derivative_at",
	Type:  "(complex → complex) → complex → complex → bool",
	Equations: []string{
		"∀f:(complex → complex). ∀c l:complex. " +
			"    complex_derivative_at(f, c, l) ⇔ (λz:complex. (f(z) - f(c)) / (z - c)) ⟶ l (at c)",
	},
})}

// HolomorphicOnDef — `holomorphic_on(s, f)`: f has a complex derivative at
// every point of s. Whether s is open is the statements' hypothesis.
var HolomorphicOnDef = holomorphicOnDefThm{family.Define(registry.DefEntry{
	Name:  "HolomorphicOnDef",
	Key:   "prop_cc76c3667078cf65",
	Const: "holomorphic_on",
	Type:  "set(complex) → (complex → complex) → bool",
	Equations: []string{
		"∀s:set(complex). ∀f:(complex → complex). " +
			"    holomorphic_on(s, f) ⇔ ∀z:complex. z ∈ s ⇒ ∃l:complex. complex_derivative_at(f, z, l)",
	},
	Deps: []registry.EntryLike{ComplexDerivativeAtDef},
	Reading: "On an open set this is holomorphy. On a set that is not open it " +
		"asks a complex derivative at each of its points, taken in the whole plane — " +
		"pointwise complex differentiability, so holomorphic_on({0}, λz. z·conj(z)) " +
		"holds; the statements that need holomorphy in the usual sense take s open.",
})}

// PathDerivativeAtDef — `path_derivative_at(γ, t, d)`: the path γ has
// velocity d at t, its real and imaginary parts having the parts of d as
// their derivatives.
var PathDerivativeAtDef = pathDerivativeAtDefThm{family.Define(registry.DefEntry{
	Name:  "PathDerivativeAtDef",
	Key:   "prop_2c84ec373c14c3f7",
	Const: "path_derivative_at",
	Type:  "(real → complex) → real → complex → bool",
	Equations: []string{
		"∀γ:(real → complex). ∀t:real. ∀d:complex. " +
			"    path_derivative_at(γ, t, d) ⇔ " +
			"    real_derivative_at(λs:real. re(γ(s)), t, re(d)) ∧ " +
			"    real_derivative_at(λs:real. im(γ(s)), t, im(d))",
	},
})}
