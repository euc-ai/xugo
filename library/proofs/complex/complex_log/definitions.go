// definitions.go — the principal argument of a complex number and its
// principal logarithm.

package complex_log

import (
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexArgDef — `complex_arg(z)`: the angle of z in ⟬−π, π⟧, the t with
// z = |z|·exp(it). At z = 0 every t of the interval serves and the choice
// is one of them.
var ComplexArgDef = complexArgDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexArgDef",
	Key:   "prop_a2e5046fd77a88f0",
	Const: "complex_arg",
	Type:  "complex → real",
	Equations: []string{
		"∀z:complex. complex_arg(z) = εt:real. -pi < t ∧ t ≤ pi ∧ z = &(|z|) * exp(complex_i * &t)",
	},
	Reading: "At z = 0 every t of ⟬−π, π⟧ serves, so the value is a choice among them " +
		"that no theorem determines; the range −π < arg z ≤ π holds there as everywhere.",
})}

// ComplexLogDef — `complex_log(z)`, written `log(z)`: the principal
// logarithm, log|z| + i·arg z.
var ComplexLogDef = complexLogDefThm{family.Define(registry.DefEntry{
	Name:      "ComplexLogDef",
	Key:       "prop_464424e959e18714",
	Const:     "complex_log",
	Type:      "complex → complex",
	Overload:  "log",
	Equations: []string{"∀z:complex. complex_log(z) = &(log(|z|)) + complex_i * &(complex_arg(z))"},
	Deps:      []registry.EntryLike{ComplexArgDef},
	Reading: "At z = 0 the value is &(log(0)) + i·complex_arg(0); the " +
		"real log at 0 and the argument of 0 are choices no theorem determines, " +
		"so every statement about log other than its parts (LogParts) asks z ≠ 0.",
})}

// SlitPlaneDef — `slit_plane`: the plane slit along the closed negative
// half-line, the complex numbers that are not a real ≤ 0. The argument
// jumps across the slit and is continuous off it, and so is the logarithm.
var SlitPlaneDef = slitPlaneDefThm{family.Define(registry.DefEntry{
	Name:      "SlitPlaneDef",
	Key:       "prop_48488cdca520a583",
	Const:     "slit_plane",
	Type:      "set(complex)",
	Equations: []string{"slit_plane = {z:complex | ¬(re(z) ≤ &0 ∧ im(z) = &0)}"},
})}
