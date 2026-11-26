// definitions.go — the winding index of a path about a point, the residue
// of a function at an isolated singularity, and the orders of a zero and of
// a pole.

package residue

import (
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/registry"
)

// WindingIndexDef — `winding_index(γ, γ', a, b, w)`: (1/2πi)·∮ dz/(z − w)
// along γ on ⟦a, b⟧, which counts the turns of γ about w when γ is a
// closed piecewise smooth path on ⟦a, b⟧ that misses w, with γ' its
// velocity.
var WindingIndexDef = windingIndexDefThm{family.Define(registry.DefEntry{
	Name:  "WindingIndexDef",
	Key:   "prop_c8482c1524c6ee19",
	Const: "winding_index",
	Type:  "(real → complex) → (real → complex) → real → real → complex → complex",
	Equations: []string{
		"∀γ γ':(real → complex). ∀a b:real. ∀w:complex. " +
			"    winding_index(γ, γ', a, b, w) = " +
			"    path_integral(λz:complex. complex_inv(z - w), γ, γ', a, b) / (&(&2 * pi) * complex_i)",
	},
	Reading: "The value counts turns for a closed piecewise smooth path missing w, with " +
		"γ' its velocity; on such a path that is not closed it is the change of a continuous " +
		"logarithm of γ(t) − w from a to b, over 2πi, in general neither an integer nor real. " +
		"On a path through w the integrand need not have an integral, and where it has none the " +
		"value is real_integral's choice, unspecified. γ' is read as written: with a γ' that is " +
		"not γ's velocity the value is (1/2πi)·∫ γ'(t)/(γ(t) − w) dt, which counts nothing.",
})}

// ComplexResidueDef — `complex_residue(f, c)`: (1/2πi) times the integral
// of f round a small circle about c, f holomorphic on a punctured disc
// about c; the circle is the one of half that disc's radius.
var ComplexResidueDef = complexResidueDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexResidueDef",
	Key:   "prop_a08c793a8f9c4b67",
	Const: "complex_residue",
	Type:  "(complex → complex) → complex → complex",
	Equations: []string{
		"∀f:(complex → complex). ∀c:complex. " +
			"    complex_residue(f, c) = " +
			"    εw:complex. ∃r:real. " +
			"        &0 < r ∧ " +
			"        holomorphic_on(«punctured»(c, r), f) ∧ " +
			"        «circleInt»(f, c, r / &2) = &(&2 * pi) * complex_i * w",
	},
	Reading: "The ε picks a w that some radius r gives — f holomorphic on the punctured disc of " +
		"radius r about c, w the integral round the circle of radius r/2 over 2πi — and says nothing of " +
		"which r. Where f has at most a pole at c, being g(z)/(z − c)ᵐ⁺¹ off c near c with g the sum of " +
		"a power series about c, every such r gives the same w, the m-th coefficient of g's series " +
		"(ResidueAtPole): the residue at a pole, and 0 at a removable point, where that coefficient " +
		"vanishes. At any other isolated singularity the ε asks only for some such r and picks the w " +
		"one of them gives. Where f is holomorphic on no punctured disc about c (a non-isolated " +
		"singularity, a point of a cut), nothing satisfies the ε and the value is unspecified, not 0.",
})}

// ComplexZeroOrderDef — `complex_zero_order(f, c)`: the m with
// f(z) = (z − c)ᵐ·g(z) near c, g holomorphic there and g(c) ≠ 0; 0 where
// f is holomorphic near c and f(c) ≠ 0.
var ComplexZeroOrderDef = complexZeroOrderDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexZeroOrderDef",
	Key:   "prop_f0985bbf2e2f3d16",
	Const: "complex_zero_order",
	Type:  "(complex → complex) → complex → num",
	Equations: []string{
		"∀f:(complex → complex). ∀c:complex. complex_zero_order(f, c) = εm:num. «zeroFactor»(f, c, m)",
	},
	Reading: "This is the order of the zero of f at c, 0 where f(c) ≠ 0, for " +
		"f holomorphic on a disc about c and not identically 0 near c. Where f " +
		"vanishes on a disc about c, or is holomorphic on no disc about c (at a " +
		"pole, for one), nothing satisfies the ε and the value is unspecified, not 0.",
})}

// ComplexPoleOrderDef — `complex_pole_order(f, c)`: the m with
// f(z) = g(z)/(z − c)ᵐ on a punctured disc about c, g holomorphic on the
// disc and g(c) ≠ 0; 0 where f extends holomorphically to c without a
// zero there.
var ComplexPoleOrderDef = complexPoleOrderDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexPoleOrderDef",
	Key:   "prop_83bdd78498509ff9",
	Const: "complex_pole_order",
	Type:  "(complex → complex) → complex → num",
	Equations: []string{
		"∀f:(complex → complex). ∀c:complex. complex_pole_order(f, c) = εm:num. «poleFactor»(f, c, m)",
	},
	Reading: "At a pole of f, where f is g(z)/(z − c)ᵐ off c near c with g holomorphic on a " +
		"disc about c, g(c) ≠ 0 and m > 0, the value is the order m of the pole. Where f agrees near " +
		"c, off c, with a holomorphic function that does not vanish at c, as where f is holomorphic " +
		"and f(c) ≠ 0, the value is 0. Elsewhere nothing satisfies the ε and the value is " +
		"unspecified, not 0: at a zero of f (f(c) = 0 with f holomorphic near c, or a removable " +
		"singularity whose limit is 0), where complex_zero_order is the order read; at an essential " +
		"singularity; where f vanishes near c; and where f is holomorphic on no punctured disc about c.",
})}
