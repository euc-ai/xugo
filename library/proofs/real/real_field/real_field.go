// real_field.go — ℝ as a field: division, and ℝ's instance of the
// abstract field.
//
// The tower delivers the inverse; division is multiplication by it.
// The definition says nothing about the divisor being nonzero — the
// inverse of zero is a value like any other, and a law that needs the
// divisor nonzero says so in its own hypothesis.

package real_field

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// RealDivDef — division is multiplication by the inverse.
var RealDivDef = realDivDefThm{family.Define(registry.DefEntry{
	Name:      "RealDivDef",
	Key:       "prop_d9fb1da318335e25",
	Const:     "real_div",
	Type:      "real → real → real",
	Equations: []string{"∀x y:real. real_div(x, y) = x * real_inv(y)"},
})}

// RealFieldOpsDef — the real field operations and its whole-type carrier.
var RealFieldOpsDef = realFieldOpsDefThm{family.Define(registry.DefEntry{
	Name: "RealFieldOpsDef",
	Key:  "prop_20df85c35d683c95", Const: "real_field_ops", Type: "field_ops(real)",
	Equations: []string{
		"real_field_ops = mk_field(real_add, &0, real_neg, real_mul, &1, real_sub, real_inv, real_div, 𝕌)",
	},
	Deps: []registry.EntryLike{RealDivDef},
})}

// RealFieldRing — the ring of the real field is the real ring: both pack
// the same operations on every real.
var RealFieldRing = realFieldRingThm{family.Add(registry.ProofEntry{
	Name: "RealFieldRing",
	Key:  "prop_176368e8d5ac3adf",
	Build: family.Theorem(
		"field_ring(real_field_ops) = real_ring",
		func(a *Argument) {
			a.Show(
				"both records unfold to the same operations",
				Simp(Fwd(real_ring.RealRingDef), Fwd(RealFieldOpsDef), Fwd(field.FieldRingDef)),
				Basic())
		}),
})}

// Field — ℝ is a field. Each conjunct is a fact already in hand but
// one: ℝ's nontriviality, which comes down from ℕ.
var Field = fieldThm{family.Add(registry.ProofEntry{
	Name: "Field",
	Key:  "prop_38bbac7fe4eb8995",
	Build: family.Instance(field.Field, "field(real_field_ops)",
		Case(
			"the commutative ring: the field's ring is the ring of reals",
			By(real_ring.CommRing, RealFieldRing)),
		Case(
			"one is not zero: the embedding of ℕ is injective, and there 1 ≠ 0",
			By(real_construction.OfNumEq, nat_arith.OneNotZero)),
		Case(
			"a nonzero real has a left inverse",
			Cite(real_construction.MulLeftInverse)),
		Case(
			"the inverse of zero is zero",
			Cite(real_construction.InvZero)),
		Case(
			"division is multiplication by the inverse",
			Cite(RealDivDef))),
})}
