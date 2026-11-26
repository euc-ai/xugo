package number_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// NumberFieldScalars — the two scalar rings of a number field: it has
// characteristic zero, its rational image is a subfield, its integer image
// is a principal ideal domain inside the rational image, and the field is a
// module over each. Characteristic zero comes with the definition; the rest
// is what the characteristic-zero chapter says of the two images.
var NumberFieldScalars = numberFieldScalarsThm{family.Add(registry.ProofEntry{
	Name: "NumberFieldScalars",
	Key:  "prop_6c8e60a417e87705",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A).",
		Hypotheses: []string{"number_field(L)"},
		Conclusion: "characteristic_zero(field_ring(L)) ∧ " +
			"subfield(L, rational_image(L)) ∧ " +
			"integer_image(field_ring(L)) ⊆ rational_image(L) ∧ " +
			"comm_ring_on(«ℤ») ∧ " +
			"principal_ideal_domain(«ℤ») ∧ " +
			"module_on(«ℤ», regular_module(field_ring(L))) ∧ " +
			"module_on(«ℚ», regular_module(field_ring(L)))",
		Abbrev: Abbrev{
			{Name: "ℤ", Text: "restrict_ring(field_ring(L), integer_image(field_ring(L)))"},
			{Name: "ℚ", Text: "restrict_ring(field_ring(L), rational_image(L))"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], numberField Fact) {
		fieldL := a.TermAs[FieldOps[A]]("L")
		characteristic := a.Have(
			"a number field has characteristic zero",
			"characteristic_zero(field_ring(L))",
			By(numberField, NumberFieldDef.At(fieldL)))
		subfield := a.Have(
			"so its rational image is a subfield",
			"subfield(L, rational_image(L))",
			By(characteristic, characteristic_zero.RationalEmbedding.Read(L)))
		integers := a.Conjuncts(
			GroupPremises(L, characteristic, int_lattice.IntegerRationalImagesStructure.At(fieldL)),
			"the integer image lies in the rational image",
			"it is a subring of L",
			"a principal ideal domain",
			"whose fractions are the rational image")
		ringZ := a.Have(
			"so a commutative ring under L's operations",
			"comm_ring_on(«ℤ»)",
			By(
				integers[1],
				comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(
					a.TermAs[Set[A]]("integer_image(field_ring(L))"))))
		modules := a.Conjuncts(
			GroupPremises(L, characteristic, int_lattice.IntegerRationalImageModules.At(fieldL)),
			"L is a module over its integer image",
			"and over its rational image")
		a.Show(
			"the scalar rings of a number field",
			By(characteristic, subfield, integers[0], ringZ, integers[2], modules[0], modules[1]))
	}),
})}
