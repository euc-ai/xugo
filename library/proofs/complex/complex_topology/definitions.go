// definitions.go — the distance of ℂ and the topology it determines; the
// limit of a sequence and of a function at a point; continuity at a point
// and on a set.

package complex_topology

import (
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	_ "github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexDistDef — `complex_dist(z, w)`, written `dist(z, w)`: the modulus
// of the difference.
var ComplexDistDef = complexDistDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexDistDef",
	Key:       "prop_f5deda4e81fc5c",
	Const:     "complex_dist",
	Type:      "complex → complex → real",
	Overload:  "dist",
	Equations: []string{"∀z w:complex. complex_dist(z, w) = |z - w|"},
})}

// ComplexTopologyDef — `complex_topology`: the open sets of ℂ, the metric
// topology of the whole plane under the distance. "u is open" is
// `u ∈ complex_topology`, as on the line.
var ComplexTopologyDef = complexTopologyDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexTopologyDef",
	Key:       "prop_7b34f0ac04153d6e",
	Const:     "complex_topology",
	Type:      "set(set(complex))",
	Equations: []string{"complex_topology = metric_topology(𝕌, complex_dist)"},
	Deps:      []registry.EntryLike{ComplexDistDef},
})}

// ComplexConvergesToDef — `complex_converges_to(a, l)`, written `a ⟶ l`:
// the sequence a of complex numbers tends to l.
var ComplexConvergesToDef = complexConvergesToDefThm{family.Define(registry.DefEntry{
	Name:     "ComplexConvergesToDef",
	Key:      "prop_ca2fbdd8e66d469d",
	Const:    "complex_converges_to",
	Type:     "(num → complex) → complex → bool",
	Notation: "a ⟶ l",
	Equations: []string{
		"∀a:(num → complex). ∀l:complex. " +
			"    complex_converges_to(a, l) ⇔ ∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε",
	},
})}

// ComplexLimitAtDef — `complex_limit_at(f, c, l)`, written
// `f ⟶ l (at c)`: f(z) tends to l as z tends to c, the value at c itself
// not looked at.
var ComplexLimitAtDef = complexLimitAtDefThm{family.Define(registry.DefEntry{
	Name:     "ComplexLimitAtDef",
	Key:      "prop_8d8dd1710f51aed7",
	Const:    "complex_limit_at",
	Type:     "(complex → complex) → complex → complex → bool",
	Notation: "f ⟶ l (at c)",
	Equations: []string{
		"∀f:(complex → complex). ∀c l:complex. " +
			"    complex_limit_at(f, c, l) ⇔ " +
			"    ∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - l| < ε",
	},
})}

// ComplexContinuousAtDef — `complex_continuous_at(f, c)`: f(z) is near
// f(c) when z is near c.
var ComplexContinuousAtDef = complexContinuousAtDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexContinuousAtDef",
	Key:   "prop_1e33881a2286b5d9",
	Const: "complex_continuous_at",
	Type:  "(complex → complex) → complex → bool",
	Equations: []string{
		"∀f:(complex → complex). ∀c:complex. " +
			"    complex_continuous_at(f, c) ⇔ " +
			"    ∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀z:complex. |z - c| < δ ⇒ |f(z) - f(c)| < ε",
	},
})}

// ComplexContinuousOnDef — `complex_continuous_on(s, f)`: f is continuous
// at each point of s relative to s, what f does off s not read.
var ComplexContinuousOnDef = complexContinuousOnDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexContinuousOnDef",
	Key:   "prop_9444e2116f580a2b",
	Const: "complex_continuous_on",
	Type:  "set(complex) → (complex → complex) → bool",
	Equations: []string{
		"∀s:set(complex). ∀f:(complex → complex). " +
			"    complex_continuous_on(s, f) ⇔ " +
			"    ∀c:complex. " +
			"        c ∈ s ⇒ " +
			"        ∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀z:complex. z ∈ s ∧ |z - c| < δ ⇒ |f(z) - f(c)| < ε",
	},
})}

var CoordinateTopologyDef = coordinateTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "CoordinateTopologyDef",
	Key:   "prop_af65577f43377097",
	Deps:  []registry.EntryLike{ComplexTopologyDef},
	Const: "complex_coordinate_topology",
	Type:  "num → set(set(num → complex))",
	Equations: []string{
		"∀r:num. " +
			"    complex_coordinate_topology(r) = " +
			"    indexed_product_topology({i:num | i < r}, " +
			"        λi:num. complex_of_real(&0), " +
			"        λi:num. complex_topology)",
	},
})}
