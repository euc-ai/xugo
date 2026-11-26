// definitions.go — the chapter's definitional layer: the tangent, the
// arctangent and the arcsine.
//
// The tangent is the quotient of the sine by the cosine, a value at every
// point: where the cosine vanishes it is a division by 0, a value no
// theorem of the chapter depends on. The two inverses are choices, as π
// is: arctan y is a point of ⟬−π/2, π/2⟭ where the tangent is y, and
// arcsin y a point of ⟦−π/2, π/2⟧ where the sine is y. The tangent takes
// every value on the open interval and the sine every value of ⟦−1, 1⟧ on
// the closed one, and each is strictly increasing there, so each choice is
// the one such point; outside ⟦−1, 1⟧ the arcsine is a choice from
// nothing, and no theorem reads it there.

package real_inverse_trigonometry

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealTanDef — `real_tan(x)`: the sine over the cosine.
var RealTanDef = realTanDefThm{family.Define(registry.DefEntry{
	Name:      "RealTanDef",
	Key:       "prop_88d01d1501eaf125",
	Const:     "real_tan",
	Overload:  "tan",
	Type:      "real → real",
	Equations: []string{"∀x:real. real_tan(x) = sin(x) / cos(x)"},
})}

// RealArctanDef — `real_arctan(y)`: the point of ⟬−π/2, π/2⟭ where the
// tangent is y.
var RealArctanDef = realArctanDefThm{family.Define(registry.DefEntry{
	Name:      "RealArctanDef",
	Key:       "prop_1f25cf97fe0e3802",
	Const:     "real_arctan",
	Overload:  "arctan",
	Type:      "real → real",
	Equations: []string{"∀y:real. real_arctan(y) = εx:real. -(pi / &2) < x ∧ x < pi / &2 ∧ tan(x) = y"},
	// The tangent; π and ℝ's order are other chapters' mints.
	Deps: []registry.EntryLike{RealTanDef},
})}

// RealArcsinDef — `real_arcsin(y)`: the point of ⟦−π/2, π/2⟧ where the
// sine is y.
var RealArcsinDef = realArcsinDefThm{family.Define(registry.DefEntry{
	Name:      "RealArcsinDef",
	Key:       "prop_93a3d0ada02709b4",
	Const:     "real_arcsin",
	Overload:  "arcsin",
	Type:      "real → real",
	Equations: []string{"∀y:real. real_arcsin(y) = εx:real. -(pi / &2) ≤ x ∧ x ≤ pi / &2 ∧ sin(x) = y"},
})}
