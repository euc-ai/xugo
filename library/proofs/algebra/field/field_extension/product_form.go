// product_form.go — a linear form on an extension C of F, composed with
// multiplication by an element of C, is a linear form.

package field_extension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ProductFormLinear — a linear form T on C and an element b of C give the
// linear form y ↦ T(b * y): multiplying by b is linear.
var ProductFormLinear = productFormLinearThm{family.Add(registry.ProofEntry{
	Name: "ProductFormLinear",
	Key:  "prop_2b86cd81b8c36a0f",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(M), F)"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)), C)"},
		},
		Binders: "∀M:field_on(A). ∀F C:set(A). ∀T:(A → A). ∀b:A.",
		Hypotheses: []string{
			"subfield(M, F)",
			"subfield(M, C)",
			"F ⊆ C",
			"module_homomorphism(«scalars», «vectors», regular_module(«scalars»), T)",
			"b ∈ C",
		},
		Conclusion: "module_homomorphism(«scalars», «vectors», regular_module(«scalars»), λy:A. T(b * y))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			F, C *Expr[Set[A]],
			T *Arrow[A, A],
			b *Expr[A],
			subF, subC, FInC, linear, bIn Fact,
		) {
			ring := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			scalars := a.TermAs[module_record.RingOps[A]]("«scalars»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»")
			target := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(«scalars»)")
			product := a.TermAs[Fun[A, A]]("λy:A. b * y")
			scaling := a.Have(
				"multiplying by b is linear over F",
				"module_homomorphism(«scalars», «vectors», «vectors», λy:A. b * y)",
				By(
					M,
					subF,
					subC,
					FInC,
					bIn,
					ExtensionModuleOn.Read(M).At(C, C),
					set_order.SubsetRefl.At(C),
					field.SubfieldSubring.Read(M).At(F),
					module_homomorphism.ScalingLinearOverSubring.At(ring, C, F, vectors, b)))
			composite := a.Have(
				"so is the form composed with it",
				"module_homomorphism(«scalars», «vectors», regular_module(«scalars»), T ∘ (λy:A. b * y))",
				By(
					scaling,
					linear,
					module_homomorphism.HomCompose.At(scalars, vectors, vectors, target, product, T)))
			a.Do(composite.Simp(Fwd(functions.ComposeApply)))
			a.Show(
				"the composite is y ↦ T(b * y)",
				By(composite))
		}),
})}
