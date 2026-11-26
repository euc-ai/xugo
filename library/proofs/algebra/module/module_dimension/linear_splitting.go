// linear_splitting.go — linear splittings over a field, which need no
// dimension: every linear map has a linear inner inverse, built on a basis
// of its image extended to a basis of the target, and a surjective linear
// map has a linear section.

package module_dimension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// LinearMapInnerInverse — every linear map over a field has a linear
// inner inverse: prescribe preimages on a basis of the image, extend
// that basis to the target, and extend the prescription linearly. The
// composite with f and the identity are linear and agree on the image
// basis, hence on the image it spans.
var LinearMapInnerInverse = linearMapInnerInverseThm{family.Add(registry.ProofEntry{
	Name: "LinearMapInnerInverse",
	Key:  "prop_4f6052dd44c54569",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(field_ring(K), M, N, f)",
		},
		Conclusion: "∃g:(C → B). " +
			"    module_homomorphism(field_ring(K), N, M, g) ∧ (∀v:B. v ∈ M.carrier ⇒ f(g(f(v))) = f(v))",
		Abbrev: Abbrev{
			{Name: "imageModule", Text: "restrict_module(N, image(f, M.carrier))"},
		},
	}, func(
		a *Argument,
		K field.FieldFact[on.K],
		M *Expr[ModuleOps[A, B]],
		N *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		linear Fact,
	) {
		R := a.TermAs[RingOps[A]]("field_ring(K)")
		inv := a.TermAs[Fun[A, A]]("K.inv")
		carrierM := a.TermAs[Set[B]]("M.carrier")
		image := a.TermAs[Set[C]]("image(f, M.carrier)")
		imageModule := a.TermAs[ModuleOps[A, C]]("«imageModule»")
		source, target :=
			module_homomorphism.HomSource.Read(linear), module_homomorphism.HomTarget.Read(linear)
		scalarsField := field.FieldRingSubfield.Read(K)
		imageSubmodule := a.Have(
			"the image is a submodule of N",
			"submodule(field_ring(K), N, image(f, M.carrier))",
			By(module_homomorphism.ImageSubmodule.Read(linear)))
		E, imageBasis := a.ObtainAs[Set[C]](
			"choose a basis of the image",
			"∃E:set(C). module_basis(field_ring(K), «imageModule», E)",
			By(
				imageSubmodule,
				submodule.SubmoduleModuleOn.Read(target).At(image),
				scalarsField,
				linear_independence.BasisExists.At(R, imageModule, inv)))
		basisFacts := a.Have(
			"E is independent in N and spans the image there",
			"module_independent(field_ring(K), N, E) ∧ module_span(field_ring(K), N, E) = image(f, M.carrier)",
			By(imageBasis, imageSubmodule, linear_independence.BasisRestrict.Read(target).At(image, E)))
		inImage := a.Have(
			"the image basis lies in the image",
			"E ⊆ image(f, M.carrier)",
			By(
				submodule.SubmoduleSubset.Read(imageSubmodule),
				imageBasis,
				linear_independence.ModuleBasisDef.At(R, imageModule, E),
				linear_independence.IndependentRestrict.At(R, N, image, E)))
		H, extendedBasis := a.ObtainAs[Set[C]](
			"extend E to a basis H of N",
			"∃H:set(C). E ⊆ H ∧ module_basis(field_ring(K), N, H)",
			By(target, basisFacts, scalarsField, linear_independence.BasisExtends.Read(target).At(inv, E)))
		φ, prescription := a.LetAs[Fun[C, B]]("φ", "λy:C. COND(y ∈ E, inverse_on(M.carrier, f, y), M.zero)")
		values := a.Have(
			"the prescribed values lie in M",
			"∀e:C. e ∈ H ⇒ φ(e) ∈ M.carrier",
			Derive(func(b *Argument) {
				e := b.FixAs[C]("e")
				b.Assume()
				b.Cases(b.TermAs[Bool]("e ∈ E"))
				b.When(
					"on E use a selected preimage",
					func(c *Argument, eInE Fact) {
						c.Show(
							"the selected preimage lies in M",
							Simp(Fwd(prescription), Fwd(eInE)),
							BySets(eInE, inImage, functions.InverseOnIn.At(carrierM, f, e)))
					})
				b.Otherwise(
					"off E use zero",
					func(c *Argument, eNotInE Fact) {
						c.Show(
							"zero lies in M",
							Simp(Fwd(prescription), Fwd(eNotInE)),
							By(group.OneIn.Read(module.AddGroupOn.Read(source))))
					})
			}))
		g, extension := a.ObtainAs[Fun[C, B]](
			"extend the prescribed basis values to a linear map g",
			"∃g:(C → B). module_homomorphism(field_ring(K), N, M, g) ∧ (∀e:C. e ∈ H ⇒ g(e) = φ(e))",
			By(source, values, extendedBasis, free_module.BasisLinearExtension.Read(target).At(M, H, φ)))
		parts := a.Conjuncts(
			extension,
			"g is linear",
			"g takes the prescribed values on H")
		gLinear, agreement := parts[0], parts[1]
		composite, identity := a.TermAs[Fun[C, C]]("f ∘ g"), a.TermAs[Fun[C, C]]("identity_map")
		endomorphisms := a.Have(
			"the composite f ∘ g and the identity are linear maps of N to itself",
			"module_homomorphism(field_ring(K), N, N, f ∘ g) ∧ "+
				"module_homomorphism(field_ring(K), N, N, identity_map)",
			By(
				linear,
				gLinear,
				module_homomorphism.HomIdentity.Read(target),
				module_homomorphism.HomCompose.At(R, N, M, N, g, f)))
		fixesBasis := a.Have(
			"the composite fixes E",
			"∀e:C. e ∈ E ⇒ (f ∘ g)(e) = identity_map(e)",
			Derive(func(b *Argument) {
				e := b.FixAs[C]("e")
				eInE := b.Assume()
				basisPoint := b.Have(
					"the image-basis point lies in the image and in H",
					"e ∈ image(f, M.carrier) ∧ e ∈ H",
					BySets(eInE, extendedBasis, inImage))
				b.Show(
					"the prescribed preimage maps back to e",
					Simp(
						Fwd(functions.ComposeApply),
						Fwd(functions.IdentityApply),
						Fwd(agreement),
						Fwd(prescription),
						Fwd(eInE),
						Fwd(basisPoint)),
					By(basisPoint, functions.InverseOnRight.At(carrierM, f, e)))
			}))
		a.Take(g)
		a.Show(
			"the linear map g is an inner inverse of f",
			SplitConj(
				Case(
					"the extension g is linear",
					By(gLinear)),
				Case(
					"the composite fixes every image vector",
					Derive(func(b *Argument) {
						v := b.FixAs[B]("v")
						vInM := b.Assume()
						inSpan := b.Have(
							"f(v) lies in the image of f, which E spans",
							"f(v) ∈ module_span(field_ring(K), N, E)",
							BySets(basisFacts, vInM))
						b.Show(
							"the composite and the identity agree on E, so on its span, where f(v) lies",
							By(
								fixesBasis,
								endomorphisms,
								inSpan,
								basisFacts,
								linear_independence.IndependentInCarrier.At(R, N, E),
								functions.ComposeApply.At(f, g),
								functions.IdentityApply,
								linear_independence.HomAgreeOnSpan.At(R, N, N, composite, identity, E, f.Apply(v))))
					}))))
	}),
})}

// LinearMapSection — a surjective linear map over a field admits a linear
// section: the composite with its inner inverse fixes every target point.
var LinearMapSection = linearMapSectionThm{family.Add(registry.ProofEntry{
	Name: "LinearMapSection",
	Key:  "prop_ee59c76b2c444a36",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"module_homomorphism(field_ring(K), M, N, f)",
			"image(f, M.carrier) = N.carrier",
		},
		Conclusion: "∃g:(C → B). " +
			"    module_homomorphism(field_ring(K), N, M, g) ∧ (∀w:C. w ∈ N.carrier ⇒ f(g(w)) = w)",
	}, func(
		a *Argument,
		K field.FieldFact[on.K],
		M *Expr[ModuleOps[A, B]],
		N *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		linearOnto Fact,
	) {
		g, innerInverse := a.ObtainAs[Fun[C, B]](
			"choose a linear inner inverse g",
			"∃g:(C → B). "+
				"    module_homomorphism(field_ring(K), N, M, g) ∧ (∀v:B. v ∈ M.carrier ⇒ f(g(f(v))) = f(v))",
			By(linearOnto, LinearMapInnerInverse.Read(K).At(M, N, f)))
		parts := a.Conjuncts(
			innerInverse,
			"g is linear",
			"the composite fixes the image of f")
		gLinear, fixesImage := parts[0], parts[1]
		a.Take(g)
		a.Show(
			"the inner inverse is a linear section",
			SplitConj(
				Case(
					"the chosen g is linear",
					By(gLinear)),
				Case(
					"the composite fixes every point of N",
					Derive(func(b *Argument) {
						w := b.FixAs[C]("w")
						wInN := b.Assume()
						v, preimage := b.ObtainAs[B](
							"choose a preimage of w in M",
							"∃v:B. v ∈ M.carrier ∧ f(v) = w",
							By(Normalized, wInN, linearOnto, set_basic.InImage.At(f, b.TermAs[Set[B]]("M.carrier"), w)))
						b.Show(
							"the inner-inverse identity at the preimage fixes w",
							By(Normalized, preimage, fixesImage.At(v)))
					}))))
	}),
})}
