// galois.go — the geometric Galois group under an enlargement of the constants.

package constant_galois

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/scalar_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// _Tensor is the type of an element of c ⊗ₗ L, the scalar extension
// «TensorModule» of GeometricGaloisBaseChange: a coset, modulo the tensor
// relations, of the finitely supported coefficient functions on pairs.
type _Tensor = Set[Fun[Prod[A, A], A]]

// GeometricGaloisBaseChange — enlarging the constants of a function field to a
// larger finite field keeps its geometric Galois group. In an algebraically
// closed M, let L be Galois over B = k(t), with k finite and t transcendental
// over k, let l, the elements of L algebraic over k, have |k|^r elements, and
// let c be the field of |k|^R elements, r dividing R. Write D = l(t) and
// E = c(t). Then the compositum N = Lc is Galois over E of degree |Aut(L/D)|,
// an isomorphism ρ of Aut(L/D) onto Aut(N/E) extends each automorphism from
// L, and for k ⊆ K ⊆ L with t ∈ K the fixed field of ρ(Aut(L/Kl)) is Kc. The
// exact constants l are finite and L is regular over them
// (function_field.ExactConstantFieldFinite). Each element of l is fixed by x ↦ x^(|k|^r)
// (finite_field.FiniteFieldFixedByFrobenius), so l lies in c as r divides R,
// and the regular constant extension (constant_composite.RegularConstantExtension) makes
// multiplication c ⊗ₗ L → N an isomorphism, with N separable over E and
// [N : E] = [L : D]; L stays Galois over D (galois_correspondence.GaloisTower).
// An automorphism s of L over D is l-linear, and conjugating its scalar
// extension by multiplication gives a c-linear map of N, multiplicative
// because L spans N over c and bijective because s⁻¹ extends the same way: an
// automorphism ρ(s) of N over E that restricts to s on L, the only one, since
// L spans N. Restriction makes ρ injective, so |Aut(L/D)| ≤ |Aut(N/E)| ≤
// [N : E] = [L : D] = |Aut(L/D)| (field_automorphism.AutomorphismsBound,
// galois_correspondence.GaloisIffCard): ρ is onto and N is Galois over E.
// Uniqueness makes ρ a homomorphism. An extension of an automorphism fixing K
// fixes K and c, and a restriction of one fixing Kc fixes K and l, so ρ carries
// Aut(L/Kl) onto Aut(N/Kc), and Galois correspondence
// (galois_correspondence.CorrespondenceFixed) gives its fixed field Kc.
var GeometricGaloisBaseChange = geometricGaloisBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "GeometricGaloisBaseChange",
	Key:  "prop_ef8f5eb7aed72996",
	Build: family.Sections(Statement{
		Abbrev: Abbrev{
			{Name: "exact", Text: "{x:A | x ∈ L ∧ algebraic_over(M, k, x)}"},
			{Name: "c", Text: "finite_constants(field_ring(M), card(k), R)"},
			{Name: "E", Text: "field_adjoin(M, «c», {t})"},
			{Name: "N", Text: "constant_composite(M, L, «c»)"},
			{Name: "Scalars", Text: "λF:field_ops(A). λS:set(A). restrict_ring(field_ring(F), S)"},
			{Name: "Vectors", Text: "λF:field_ops(A). λS:set(A). " +
				"    restrict_module(regular_module(field_ring(F)), S)"},
			{Name: "TensorModule", Text: "λF:field_ops(A). λl:set(A). λc:set(A). λL:set(A). " +
				"    scalar_extension(«Scalars»(F, l), «Scalars»(F, c), «Vectors»(F, L))"},
			{Name: "PureTensor", Text: "λF:field_ops(A). λl:set(A). λc:set(A). λL:set(A). λa:A. λx:A. " +
				"    tensor(«Scalars»(F, l), «Vectors»(F, c), «Vectors»(F, L), a, x)"},
		},

		Binders: "∀M:field_on(A). ∀k l K L:set(A). ∀t:A. ∀r R:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"l = «exact»",
			"subfield(M, L)",
			"subfield(M, K)",
			"k ⊆ K",
			"K ⊆ L",
			"t ∈ K",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, field_adjoin(M, k, {t}), L)",
			"card(l) = card(k) ^ r",
			"0 < R",
			"r ∣ R",
		},
		Conclusion: "galois_over(M, «E», «N») ∧ " +
			"extension_degree(M, «E», «N») = card(field_automorphisms(M, field_adjoin(M, l, {t}), L)) ∧ " +
			"(∃rho:(permutation(A) → permutation(A)). " +
			"    group_isomorphism(galois_group(M, field_adjoin(M, l, {t}), L), " +
			"        galois_group(M, «E», «N»), " +
			"        rho) ∧ " +
			"    (∀s:permutation(A). " +
			"        s ∈ field_automorphisms(M, field_adjoin(M, l, {t}), L) ⇒ " +
			"        ∀x:A. x ∈ L ⇒ permutation_map(rho(s), x) = permutation_map(s, x)) ∧ " +
			"    fixed_field(«N», image(rho, field_automorphisms(M, constant_composite(M, K, l), L))) = " +
			"    constant_composite(M, K, «c»))",
	},
		func(ctx *Script, headline string) *GoalStackNode {

			// Unfolding the scalar extension exhibits it as the tensor product of two extension fields of l.
			tensorFactors := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀l c L:set(A).",
				Hypotheses: []string{
					"subfield(M, l)",
					"subfield(M, c)",
					"subfield(M, L)",
					"l ⊆ c",
					"l ⊆ L",
				},
				Conclusion: "module_on(«Scalars»(M, l), «Vectors»(M, c)) ∧ " +
					"module_on(«Scalars»(M, l), «Vectors»(M, L)) ∧ " +
					"«TensorModule»(M, l, c, L).add = set_mul(fun_add(«Scalars»(M, l).add)) ∧ " +
					"«TensorModule»(M, l, c, L).zero = " +
					"tensor_relations(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L)) ∧ " +
					"«TensorModule»(M, l, c, L).carrier = " +
					"tensor_product(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L))",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					l, c, L *Expr[Set[A]],
					exactConstantsSubfield, largerConstantsSubfield, originalSubfield, exactInLarger, exactInOriginal Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")

					factorModules := a.Have(
						"both tensor factors are modules over the exact constants",
						"module_on(«Scalars»(M, l), «Vectors»(M, c)) ∧ module_on(«Scalars»(M, l), «Vectors»(M, L))",
						By(
							M,
							originalSubfield,
							largerConstantsSubfield,
							exactConstantsSubfield,
							exactInOriginal,
							exactInLarger,
							field_extension.ExtensionModuleOn.At(m, l, c),
							field_extension.ExtensionModuleOn.At(m, l, L)))
					tensorStructure := a.Have(
						"the scalar extension carries the addition, zero and carrier of the tensor product",
						"«TensorModule»(M, l, c, L).add = set_mul(fun_add(«Scalars»(M, l).add)) ∧ "+
							"«TensorModule»(M, l, c, L).zero = "+
							"tensor_relations(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L)) ∧ "+
							"«TensorModule»(M, l, c, L).carrier = "+
							"tensor_product(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L))",
						Simp(
							Fwd(module_record.RegularModuleDef),
							Fwd(module_record.RestrictRingDef),
							Fwd(field.FieldRingDef),
							Fwd(scalar_extension.ScalarExtensionDef),
							Fwd(module_record.RestrictModuleDef),
							Fwd(tensor_product.TensorProductDef)),
						Basic())
					a.Show(
						"the scalar extension is the tensor product of the two modules",
						By(factorModules, tensorStructure))
				})
			// Conjugating the scalar extension of a linear map by the multiplication isomorphism extends it to the compositum.
			linearTransport := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀l c L N:set(A). ∀f:(set(prod(A, A) → A) → A). ∀s:(A → A).",
				Hypotheses: []string{
					"subfield(M, l)",
					"subfield(M, c)",
					"subfield(M, L)",
					"l ⊆ c",
					"l ⊆ L",
					"module_isomorphism(«Scalars»(M, c), «TensorModule»(M, l, c, L), «Vectors»(M, N), f)",
					"∀a x:A. a ∈ c ∧ x ∈ L ⇒ f(«PureTensor»(M, l, c, L, a, x)) = a * x",
					"module_homomorphism(«Scalars»(M, l), «Vectors»(M, L), «Vectors»(M, L), s)",
				},
				Conclusion: "∃F:(A → A). " +
					"    module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), F) ∧ " +
					"    (∀a x:A. a ∈ c ∧ x ∈ L ⇒ F(a * x) = a * s(x))",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					l, c, L, N *Expr[Set[A]],
					f *Expr[Fun[_Tensor, A]],
					s *Expr[Fun[A, A]],
					exactConstantsSubfield, largerConstantsSubfield, originalSubfield, exactInLarger, exactInOriginal, multiplicationIsomorphism, multiplicationOnPureTensors, sourceLinear Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					exactScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, l)")
					largerScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, c)")
					largerVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, c)")
					originalVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, L)")
					compositumVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, N)")
					tensorModule := a.TermAs[module_record.ModuleOps[A, _Tensor]]("«TensorModule»(M, l, c, L)")

					scalarField := a.Have(
						"the larger constants form a field containing the exact constants",
						"field_on(restrict_field(M, c)) ∧ subfield(restrict_field(M, c), l)",
						By(
							M,
							largerConstantsSubfield,
							exactConstantsSubfield,
							exactInLarger,
							field.SubfieldFieldOn.At(m, c),
							field.SubfieldRestrict.At(m, c, l)))
					restrictionIdentities := a.Have(
						"restricting through the scalar field gives the same ring and module structures",
						"«Scalars»(M, l) = «Scalars»(restrict_field(M, c), l) ∧ "+
							"«Scalars»(M, c) = field_ring(restrict_field(M, c)) ∧ "+
							"«Vectors»(M, c) = regular_module(«Scalars»(M, c))",
						Simp(
							Fwd(field.RestrictFieldDef),
							Fwd(field.FieldRingDef),
							Fwd(module_record.RestrictRingDef),
							Fwd(module_record.RegularModuleDef),
							Fwd(module_record.RestrictModuleDef)),
						Basic())
					scalarLift := a.Have(
						"scalar extension lifts the linear map and gives its pure tensor formula",
						"module_homomorphism(«Scalars»(M, c), "+
							"    «TensorModule»(M, l, c, L), "+
							"    «TensorModule»(M, l, c, L), "+
							"    scalar_extension_map(«Scalars»(M, l), "+
							"        «Scalars»(M, c), "+
							"        «Vectors»(M, L), "+
							"        «Vectors»(M, L), "+
							"        s)) ∧ "+
							"(∀a x:A. "+
							"    a ∈ c ∧ x ∈ L ⇒ "+
							"    scalar_extension_map(«Scalars»(M, l), "+
							"        «Scalars»(M, c), "+
							"        «Vectors»(M, L), "+
							"        «Vectors»(M, L), "+
							"        s, "+
							"        «PureTensor»(M, l, c, L, a, x)) = "+
							"    «PureTensor»(M, l, c, L, a, s(x)))",
						By(
							Normalized,
							scalarField,
							restrictionIdentities,
							sourceLinear,
							field.RingOn.At(a.TermAs[FieldOps[A]]("restrict_field(M, c)")),
							field.SubfieldSubring.At(a.TermAs[FieldOps[A]]("restrict_field(M, c)"), l),
							scalar_extension.ScalarExtensionMapSpec.At(
								a.TermAs[module_record.RingOps[A]]("field_ring(restrict_field(M, c))"),
								l,
								originalVectors,
								originalVectors,
								s)))
					g, gDef := a.LetAs[Fun[A, _Tensor]]("g", "inverse_on(«TensorModule»(M, l, c, L).carrier, f)")
					h, hDef := a.LetAs[Fun[A, A]](
						"h",
						"f ∘ "+
							"(scalar_extension_map(«Scalars»(M, l), «Scalars»(M, c), «Vectors»(M, L), «Vectors»(M, L), s) ∘ g)")
					inverseIsomorphism := a.Have(
						"the inverse multiplication map is a module isomorphism",
						"module_isomorphism(«Scalars»(M, c), «Vectors»(M, N), «TensorModule»(M, l, c, L), g)",
						Derive(func(b *Argument) {
							inverseDefinition := b.Unfolded(gDef, scalar_extension.ScalarExtensionDef)
							b.Show(
								"invert the multiplication isomorphism",
								By(
									Normalized,
									inverseDefinition,
									multiplicationIsomorphism,
									module_homomorphism.IsomorphismInverse.At(largerScalars, tensorModule, compositumVectors, f)))
						}))
					tensorLinearMaps := a.Have(
						"the multiplication isomorphism and its inverse are linear",
						"module_homomorphism(«Scalars»(M, c), «TensorModule»(M, l, c, L), «Vectors»(M, N), f) ∧ "+
							"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «TensorModule»(M, l, c, L), g)",
						By(
							inverseIsomorphism,
							multiplicationIsomorphism,
							module_homomorphism.ModuleIsomorphismDef.At(largerScalars, tensorModule, compositumVectors, f),
							module_homomorphism.ModuleIsomorphismDef.At(largerScalars, compositumVectors, tensorModule, g)))
					liftedInverseLinear := a.Have(
						"the scalar lift composed with the inverse multiplication map is linear",
						"module_homomorphism(«Scalars»(M, c), "+
							"    «Vectors»(M, N), "+
							"    «TensorModule»(M, l, c, L), "+
							"    scalar_extension_map(«Scalars»(M, l), "+
							"        «Scalars»(M, c), "+
							"        «Vectors»(M, L), "+
							"        «Vectors»(M, L), "+
							"        s) ∘ "+
							"    g)",
						By(
							scalarLift,
							tensorLinearMaps,
							module_homomorphism.HomCompose.At(
								largerScalars,
								compositumVectors,
								tensorModule,
								tensorModule,
								g,
								a.TermAs[Fun[_Tensor, _Tensor]](
									"scalar_extension_map(«Scalars»(M, l), «Scalars»(M, c), «Vectors»(M, L), «Vectors»(M, L), s)"))))
					transportedLinear := a.Have(
						"conjugating by multiplication gives a linear map on the compositum",
						"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), h)",
						By(
							hDef,
							tensorLinearMaps,
							liftedInverseLinear,
							module_homomorphism.HomCompose.At(
								largerScalars,
								compositumVectors,
								tensorModule,
								compositumVectors,
								a.TermAs[Fun[A, _Tensor]](
									"scalar_extension_map(«Scalars»(M, l), «Scalars»(M, c), «Vectors»(M, L), «Vectors»(M, L), s) ∘ g"),
								f)))
					tensorProductData := a.Have(
						"the scalar extension is the tensor product of two modules over the exact constants",
						"module_on(«Scalars»(M, l), «Vectors»(M, c)) ∧ "+
							"module_on(«Scalars»(M, l), «Vectors»(M, L)) ∧ "+
							"«TensorModule»(M, l, c, L).add = set_mul(fun_add(«Scalars»(M, l).add)) ∧ "+
							"«TensorModule»(M, l, c, L).zero = "+
							"tensor_relations(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L)) ∧ "+
							"«TensorModule»(M, l, c, L).carrier = "+
							"tensor_product(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L))",
						By(
							M,
							originalSubfield,
							largerConstantsSubfield,
							exactConstantsSubfield,
							exactInOriginal,
							exactInLarger,
							At(tensorFactors, m, l, c, L)))
					multiplicationInjective := a.Have(
						"multiplication is injective on the tensor product",
						"injective_on(«TensorModule»(M, l, c, L).carrier, f)",
						By(
							multiplicationIsomorphism,
							module_homomorphism.ModuleIsomorphismDef.At(largerScalars, tensorModule, compositumVectors, f)))
					inverseOnProducts := a.Have(
						"the inverse multiplication map sends products to pure tensors",
						"∀a x:A. a ∈ c ∧ x ∈ L ⇒ g(a * x) = «PureTensor»(M, l, c, L, a, x)",
						Derive(func(b *Argument) {
							scalar := b.FixAs[A]("a")
							x := b.FixAs[A]("x")
							members := b.Assume()
							pureTensorIn := b.Have(
								"the indicated pure tensor belongs to the tensor product",
								"«PureTensor»(M, l, c, L, a, x) ∈ «TensorModule»(M, l, c, L).carrier",
								By(
									tensorProductData,
									members,
									tensor_product.TensorIn.At(exactScalars, largerVectors, originalVectors, scalar, x)))
							inverseFormula := b.Unfolded(gDef, scalar_extension.ScalarExtensionDef)
							b.Show(
								"invert the pure tensor formula",
								By(
									multiplicationOnPureTensors.At(scalar, x),
									inverseFormula,
									multiplicationInjective,
									pureTensorIn,
									members,
									functions.InverseOnLeft.At(
										b.TermAs[Set[_Tensor]]("«TensorModule»(M, l, c, L).carrier"),
										f,
										b.TermAs[_Tensor]("«PureTensor»(M, l, c, L, a, x)"))))
						}))
					liftOnPureTensors := a.Conjuncts(
						scalarLift,
						"the scalar extension map is linear",
						"the scalar extension map sends pure tensors as required")[1]
					a.Take(h)
					a.Show(
						"use the transported linear map as the extension",
						SplitConj(
							Case(
								"the transported map is linear",
								By(transportedLinear)),
							Case(
								"the transported map has the pure product formula",
								Derive(func(b *Argument) {
									b.FixAs[A]("a")
									x := b.FixAs[A]("x")
									members := b.Assume()
									sourceImage := b.Have(
										"s keeps x in L",
										"s(x) ∈ L",
										By(members, module_homomorphism.HomIn.Read(sourceLinear).AsFact().At(x)))
									b.Show(
										"evaluate the transported map on a pure product",
										Simp(
											Fwd(hDef),
											Fwd(inverseOnProducts),
											Fwd(liftOnPureTensors),
											Fwd(multiplicationOnPureTensors),
											Fwd(functions.ComposeApply),
											Fwd(sourceImage)),
										Refl())
								})),
						))
				})
			// Pure tensors span the tensor product; their images are scalar multiples of elements of the original field.
			sourceSpansComposite := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀l c L N:set(A). ∀f:(set(prod(A, A) → A) → A).",
				Hypotheses: []string{
					"subfield(M, l)",
					"subfield(M, c)",
					"subfield(M, L)",
					"l ⊆ c",
					"l ⊆ L",
					"L ⊆ N",
					"module_isomorphism(«Scalars»(M, c), «TensorModule»(M, l, c, L), «Vectors»(M, N), f)",
					"∀a x:A. a ∈ c ∧ x ∈ L ⇒ f(«PureTensor»(M, l, c, L, a, x)) = a * x",
				},
				Conclusion: "module_span(«Scalars»(M, c), «Vectors»(M, N), L) = N",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					l, c, L, N *Expr[Set[A]],
					f *Expr[Fun[_Tensor, A]],
					exactConstantsSubfield, largerConstantsSubfield, originalSubfield, exactInLarger, exactInOriginal, originalInCompositum, multiplicationIsomorphism, multiplicationOnPureTensors Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					exactScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, l)")
					largerScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, c)")
					largerVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, c)")
					originalVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, L)")
					compositumVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, N)")
					tensorModule := a.TermAs[module_record.ModuleOps[A, _Tensor]]("«TensorModule»(M, l, c, L)")

					multiplicationIsoData := a.Unfolded(
						multiplicationIsomorphism, module_homomorphism.ModuleIsomorphismDef)
					multiplicationData := a.Conjuncts(
						multiplicationIsoData,
						"multiplication is linear",
						"multiplication is injective",
						"multiplication is onto the compositum")
					multiplicationLinear, multiplicationOnto := multiplicationData[0], multiplicationData[2]
					extensionModules := a.Have(
						"the tensor product and the compositum carry the scalar module structures",
						"module_on(«Scalars»(M, c), «TensorModule»(M, l, c, L)) ∧ "+
							"module_on(«Scalars»(M, c), «Vectors»(M, N))",
						By(
							module_homomorphism.HomSource.Read(multiplicationLinear),
							module_homomorphism.HomTarget.Read(multiplicationLinear)))
					Q, qDef := a.LetAs[Set[A]]("Q", "module_span(«Scalars»(M, c), «Vectors»(M, N), L)")
					P, pDef := a.LetAs[Set[_Tensor]]("P", "preimage_on(«TensorModule»(M, l, c, L).carrier, f, Q)")
					generatedSpan := a.Have(
						"the larger constant span of the original field is a submodule",
						"submodule(«Scalars»(M, c), «Vectors»(M, N), Q) ∧ L ⊆ Q ∧ Q ⊆ N",
						By(
							Normalized,
							qDef,
							originalInCompositum,
							extensionModules,
							submodule.SpanSubmodule.At(largerScalars, compositumVectors, L),
							submodule.SubsetSpan.At(largerScalars, compositumVectors, L),
							submodule.CarrierSubmodule.At(largerScalars, compositumVectors),
							submodule.SpanLeast.At(largerScalars, compositumVectors, L, N)))
					preimageDefinition := a.Unfolded(pDef, scalar_extension.ScalarExtensionDef)
					preimageSubmodule := a.Have(
						"the inverse image of the span is a submodule of the tensor product",
						"submodule(«Scalars»(M, c), «TensorModule»(M, l, c, L), P)",
						By(
							Normalized,
							preimageDefinition,
							generatedSpan,
							multiplicationLinear,
							module_homomorphism.HomPreimageSubmodule.At(largerScalars, tensorModule, compositumVectors, f, Q)))
					tensorProductData := a.Have(
						"the scalar extension is the tensor product of two modules over the exact constants",
						"module_on(«Scalars»(M, l), «Vectors»(M, c)) ∧ "+
							"module_on(«Scalars»(M, l), «Vectors»(M, L)) ∧ "+
							"«TensorModule»(M, l, c, L).add = set_mul(fun_add(«Scalars»(M, l).add)) ∧ "+
							"«TensorModule»(M, l, c, L).zero = "+
							"tensor_relations(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L)) ∧ "+
							"«TensorModule»(M, l, c, L).carrier = "+
							"tensor_product(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L))",
						By(
							M,
							originalSubfield,
							largerConstantsSubfield,
							exactConstantsSubfield,
							exactInOriginal,
							exactInLarger,
							At(tensorFactors, m, l, c, L)))
					generatorsInPreimage := a.Have(
						"pure tensors map into the scalar span of the original field",
						"∀a x:A. a ∈ c ∧ x ∈ L ⇒ «PureTensor»(M, l, c, L, a, x) ∈ P",
						Derive(func(b *Argument) {
							scalar := b.FixAs[A]("a")
							x := b.FixAs[A]("x")
							members := b.Assume()
							productInSpan := b.Have(
								"a scalar multiple of an original field element lies in its scalar span",
								"a * x ∈ Q",
								BySets(
									members,
									generatedSpan,
									submodule.SubmoduleSmul.At(largerScalars, compositumVectors, Q, scalar, x)))
							generatorInTensor := b.Have(
								"the pure tensor lies in the tensor product carrier",
								"«PureTensor»(M, l, c, L, a, x) ∈ «TensorModule»(M, l, c, L).carrier",
								By(
									tensorProductData,
									members,
									tensor_product.TensorIn.At(exactScalars, largerVectors, originalVectors, scalar, x)))
							b.Show(
								"pure tensors generate the preimage submodule",
								BySets(multiplicationOnPureTensors.At(scalar, x), pDef, productInSpan, generatorInTensor, members))
						}))
					allTensorsInPreimage := a.Have(
						"every tensor lies in the preimage submodule",
						"∀z:set(prod(A, A) → A). z ∈ «TensorModule»(M, l, c, L).carrier ⇒ z ∈ P",
						Derive(func(b *Argument) {
							z := b.FixAs[_Tensor]("z")
							inCarrier := b.Assume()
							s, _, expansion := b.Obtain2As[Set[Prod[A, A]], Fun[Prod[A, A], A]](
								"write the tensor as a finite sum of scalar multiples of pure tensors",
								"∃s:set(prod(A, A)). ∃a:(prod(A, A) → A). "+
									"    finite(s) ∧ "+
									"    s ⊆ set_cross(«Vectors»(M, c).carrier, «Vectors»(M, L).carrier) ∧ "+
									"    (∀q:prod(A, A). q ∈ s ⇒ a(q) ∈ «Scalars»(M, l).carrier) ∧ "+
									"    z = "+
									"    module_sum(set_mul(fun_add(«Scalars»(M, l).add)), "+
									"        tensor_relations(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L)), "+
									"        s, "+
									"        λq:prod(A, A). "+
									"            quotient_smul(fun_add(«Scalars»(M, l).add), "+
									"                fun_smul, "+
									"                tensor_relations(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L)), "+
									"                a(q), "+
									"                «PureTensor»(M, l, c, L, fst(q), snd(q))))",
								Derive(func(a *Argument) {
									inTensorProduct := a.Have(
										"a scalar tensor is in the tensor carrier",
										"z ∈ tensor_product(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L))",
										By(inCarrier, tensorProductData))
									a.Show(
										"expand the tensor into a finite sum",
										By(
											inTensorProduct,
											tensorProductData,
											tensor_product.TensorSpan.At(exactScalars, largerVectors, originalVectors, z)))
								}),
							)
							w, summandDefinition := b.LetAs[Fun[Prod[A, A], _Tensor]](
								"w",
								"λq:prod(A, A). "+
									"    quotient_smul(fun_add(«Scalars»(M, l).add), "+
									"        fun_smul, "+
									"        tensor_relations(«Scalars»(M, l), «Vectors»(M, c), «Vectors»(M, L)), "+
									"        a(q), "+
									"        «PureTensor»(M, l, c, L, fst(q), snd(q)))")
							summandsInPreimage := b.Have(
								"each summand in the tensor expansion lies in the preimage submodule",
								"∀q:prod(A, A). q ∈ s ⇒ w(q) ∈ P",
								Derive(func(a *Argument) {
									q := a.FixAs[Prod[A, A]]("q")
									inSupport := a.Assume()
									summandFactors := a.Have(
										"the coefficients and tensor factors lie in their required carriers",
										"a(q) ∈ l ∧ fst(q) ∈ c ∧ snd(q) ∈ L",
										BySets(
											inSupport,
											expansion,
											set_product.InCrossProjections.At(
												a.TermAs[Set[A]]("«Vectors»(M, c).carrier"), a.TermAs[Set[A]]("«Vectors»(M, L).carrier"), q)))
									absorbedScalar := a.Have(
										"absorb the exact-constant coefficient into the larger-constant factor",
										"a(q) * fst(q) ∈ c",
										BySets(
											largerConstantsSubfield,
											exactInLarger,
											summandFactors,
											field.SubfieldMul.At(m, c, a.TermAs[A]("a(q)"), a.TermAs[A]("fst(q)"))))
									summandIsPure := a.Have(
										"each scaled tensor is another pure tensor",
										"w(q) = «PureTensor»(M, l, c, L, a(q) * fst(q), snd(q))",
										Derive(func(a *Argument) {
											a.Do(summandDefinition.Rw())
											scalarAddition := a.Have(
												"the restricted scalar addition is ambient addition",
												"«Scalars»(M, l).add = M.add",
												Simp(Fwd(module_record.RestrictRingDef), Fwd(field.FieldRingDef)),
												Refl())
											a.Show(
												"identify the scaled pure tensor",
												By(
													scalarAddition,
													tensorProductData,
													summandFactors,
													tensor_product.TensorSmulLeft.At(
														exactScalars,
														largerVectors,
														originalVectors,
														a.TermAs[A]("a(q)"),
														a.TermAs[A]("fst(q)"),
														a.TermAs[A]("snd(q)"))))
										}))
									a.Show(
										"the scaled pure tensor lies in the preimage submodule",
										By(
											generatorsInPreimage.At(a.TermAs[A]("a(q) * fst(q)"), a.TermAs[A]("snd(q)")),
											summandIsPure,
											absorbedScalar,
											summandFactors))
								}))
							sumInPreimage := b.Have(
								"the finite tensor sum lies in the preimage submodule",
								"module_sum(«TensorModule»(M, l, c, L).add, «TensorModule»(M, l, c, L).zero, s, w) ∈ P",
								By(
									summandsInPreimage,
									extensionModules,
									expansion,
									preimageSubmodule,
									submodule.SubmoduleModuleSum.At(largerScalars, tensorModule, P, s, w)))
							b.Show(
								"the tensor sum lies in the preimage submodule",
								By(sumInPreimage, tensorProductData, expansion))
						}))
					tensorPreimageContainment := a.Unfolded(allTensorsInPreimage, scalar_extension.ScalarExtensionDef)
					a.Show(
						"surjectivity of multiplication identifies the span",
						BySets(tensorPreimageContainment, multiplicationOnto, preimageDefinition, generatedSpan))
				})
			// Fixing one factor makes multiplication a linear map. Uniqueness extends the product law in each factor.
			multiplicationFromGenerators := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀c L N:set(A). ∀h:(A → A).",
				Hypotheses: []string{
					"subfield(M, c)",
					"subfield(M, N)",
					"c ⊆ N",
					"L ⊆ N",
					"module_span(«Scalars»(M, c), «Vectors»(M, N), L) = N",
					"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), h)",
					"∀x y:A. x ∈ L ∧ y ∈ L ⇒ h(x * y) = h(x) * h(y)",
				},
				Conclusion: "∀x y:A. x ∈ N ∧ y ∈ N ⇒ h(x * y) = h(x) * h(y)",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					c, L, N *Expr[Set[A]],
					h *Expr[Fun[A, A]],
					largerConstantsSubfield, compositumSubfield, largerInCompositum, originalInCompositum, originalSpans, mapLinear, mapMultiplicativeOnOriginal Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					largerScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, c)")
					compositumVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, N)")

					scalingSetup := a.Have(
						"the compositum is a module and its constants form a scalar subring",
						"module_on(«Scalars»(M, N), «Vectors»(M, N)) ∧ subring(field_ring(M), c)",
						By(
							M,
							compositumSubfield,
							largerConstantsSubfield,
							field_extension.ExtensionModuleOn.At(m, N, N),
							field.SubfieldSubring.At(m, c),
							set_order.SubsetRefl.At(N)))
					scalingLinear := a.Have(
						"multiplication by a fixed compositum element is linear",
						"∀a:A. a ∈ N ⇒ module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), λu:A. a * u)",
						By(
							largerInCompositum,
							scalingSetup,
							At(
								module_homomorphism.ScalingLinearOverSubring,
								a.TermAs[module_record.RingOps[A]]("field_ring(M)"),
								N,
								c,
								compositumVectors)))
					productComparisonsLinear := a.Have(
						"both comparison maps for multiplication are linear",
						Statement{
							Binders: "∀a:A.",
							Hypotheses: []string{
								"a ∈ N",
							},
							Conclusion: "module_homomorphism(«Scalars»(M, c), " +
								"    «Vectors»(M, N), " +
								"    «Vectors»(M, N), " +
								"    λu:A. h(a * u)) ∧ " +
								"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), λu:A. h(a) * h(u))",
						},
						Derive(func(b *Argument) {
							factor := b.FixAs[A]("a")
							inCompositum := b.Assume()
							valueInCompositum := b.Have(
								"the map value is in the compositum",
								"h(a) ∈ N",
								By(inCompositum, module_homomorphism.HomIn.Read(mapLinear).AsFact().At(factor)))
							b.Show(
								"compose the two linear comparison maps",
								By(
									scalingLinear.At(factor),
									scalingLinear.At(b.TermAs[A]("h(a)")),
									inCompositum,
									valueInCompositum,
									mapLinear,
									module_homomorphism.HomCompose.At(
										largerScalars,
										compositumVectors,
										compositumVectors,
										compositumVectors,
										b.TermAs[Fun[A, A]]("λu:A. a * u"),
										h),
									module_homomorphism.HomCompose.At(
										largerScalars,
										compositumVectors,
										compositumVectors,
										compositumVectors,
										h,
										b.TermAs[Fun[A, A]]("λu:A. h(a) * u")),
									functions.ComposeApply.At(h, b.TermAs[Fun[A, A]]("λu:A. a * u")),
									functions.ComposeApply.At(b.TermAs[Fun[A, A]]("λu:A. h(a) * u"), h)))
						}))
					secondFactorExtension := a.Have(
						"a product law for a fixed first factor extends from the original field to the compositum",
						"∀x:A. x ∈ N ∧ (∀y:A. y ∈ L ⇒ h(x * y) = h(x) * h(y)) ⇒ ∀y:A. y ∈ N ⇒ h(x * y) = h(x) * h(y)",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							productLawOnOriginal := b.Assume()
							b.Show(
								"the two comparison maps agree on the spanning original field",
								By(
									productLawOnOriginal,
									productComparisonsLinear.At(x),
									originalSpans,
									originalInCompositum,
									At(
										linear_independence.HomAgreeOnSpan,
										largerScalars,
										compositumVectors,
										compositumVectors,
										b.TermAs[Fun[A, A]]("λu:A. h(x * u)"),
										b.TermAs[Fun[A, A]]("λu:A. h(x) * h(u)"),
										L)))
						}))
					generatorFactor := a.Have(
						"extend multiplication from the original field in the second factor",
						"∀x:A. x ∈ L ⇒ ∀y:A. y ∈ N ⇒ h(x * y) = h(x) * h(y)",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							inField := b.Assume()
							generatorInCompositum := b.Have(
								"the generator lies in the compositum",
								"x ∈ N",
								BySets(inField, originalInCompositum))
							b.Show(
								"extend the product formula in the second factor",
								By(mapMultiplicativeOnOriginal.At(x), inField, generatorInCompositum, secondFactorExtension.At(x)))
						}))
					compositumField := a.Have(
						"the restricted compositum structure is a field",
						"field_on(restrict_field(M, N))",
						By(M, compositumSubfield, field.SubfieldFieldOn.At(m, N)))
					multiplicationCommutes := a.Have(
						"multiplication commutes in the compositum",
						"∀x y:A. x ∈ N ∧ y ∈ N ⇒ x * y = y * x",
						By(comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(compositumField)))))
					arbitraryFactor := a.Have(
						"commute factors to place the original field element second",
						"∀a x:A. a ∈ N ∧ x ∈ L ⇒ h(a * x) = h(a) * h(x)",
						Derive(func(b *Argument) {
							factor := b.FixAs[A]("a")
							x := b.FixAs[A]("x")
							members := b.Assume()
							originalElementInComposite := b.Have(
								"the original field element lies in the compositum",
								"x ∈ N",
								BySets(originalInCompositum, members))
							valuesInComposite := b.Have(
								"the linear map takes both factors into the compositum",
								"h(a) ∈ N ∧ h(x) ∈ N",
								By(
									originalElementInComposite,
									members,
									module_homomorphism.HomIn.Read(mapLinear).AsFact().At(factor),
									module_homomorphism.HomIn.Read(mapLinear).AsFact().At(x)))
							b.Show(
								"extend the multiplication identity to this pair of factors",
								By(
									Normalized,
									multiplicationCommutes.At(factor, x),
									multiplicationCommutes.At(b.TermAs[A]("h(a)"), b.TermAs[A]("h(x)")),
									generatorFactor.At(x, factor),
									originalElementInComposite,
									members,
									valuesInComposite))
						}))
					x := a.FixAs[A]("x")
					a.FixAs[A]("y")
					members := a.Assume()
					a.Show(
						"linearity in the other factor proves multiplication everywhere",
						By(arbitraryFactor.At(x), members, secondFactorExtension.At(x)))
				})
			// The automorphism fixes each scalar a, so p(a * x) = p(a) * p(x) = a * p(x).
			automorphismIsLinear := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀l D L:set(A). ∀p:permutation(A).",
				Hypotheses: []string{
					"subfield(M, l)",
					"subfield(M, L)",
					"l ⊆ D",
					"l ⊆ L",
					"p ∈ field_automorphisms(M, D, L)",
				},
				Conclusion: "module_homomorphism(«Scalars»(M, l), " +
					"    «Vectors»(M, L), " +
					"    «Vectors»(M, L), " +
					"    permutation_map(p))",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					l, D, L *Expr[Set[A]],
					p *Expr[symmetric_group.Permutation[A]],
					scalarsSubfield, originalSubfield, scalarsInFixedBase, scalarsInOriginal, sourceAutomorphism Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					scalarRing := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, l)")
					originalVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, L)")

					automorphismData := a.Unfolded(sourceAutomorphism, field_automorphism.FieldAutomorphismsDef)
					sourcePermutation := a.Have(
						"the source permutation preserves addition, multiplication, and its base",
						"p ∈ symmetric_group(L) ∧ "+
							"(∀x y:A. "+
							"    x ∈ L ∧ y ∈ L ⇒ "+
							"    permutation_map(p, x + y) = permutation_map(p, x) + permutation_map(p, y)) ∧ "+
							"(∀x y:A. "+
							"    x ∈ L ∧ y ∈ L ⇒ "+
							"    permutation_map(p, x * y) = permutation_map(p, x) * permutation_map(p, y)) ∧ "+
							"(∀x:A. x ∈ D ⇒ permutation_map(p, x) = x)",
						BySets(automorphismData))
					sourceFieldLaws := a.Conjuncts(
						sourcePermutation,
						"the source permutation preserves the carrier",
						"the source permutation preserves addition",
						"the source permutation preserves products",
						"the source permutation fixes its base")
					permutesOriginal, preservesAddition, preservesProducts, fixesBase :=
						sourceFieldLaws[0], sourceFieldLaws[1], sourceFieldLaws[2], sourceFieldLaws[3]
					scalarPreservation := a.Have(
						"fixing the scalars makes the source automorphism linear on products",
						"∀a x:A. a ∈ l ∧ x ∈ L ⇒ permutation_map(p, a * x) = a * permutation_map(p, x)",
						Derive(func(b *Argument) {
							scalar := b.FixAs[A]("a")
							x := b.FixAs[A]("x")
							members := b.Assume()
							scalarInBaseAndField := b.Have(
								"the scalar lies in the fixed base and original field",
								"a ∈ D ∧ a ∈ L",
								BySets(scalarsInFixedBase, scalarsInOriginal, members))
							b.Show(
								"use the fixed scalar in the product law",
								By(
									Normalized,
									preservesProducts.At(scalar, x),
									fixesBase.At(scalar),
									scalarInBaseAndField,
									members))
						}))
					linearityData := a.Have(
						"the source permutation preserves its carrier, addition, and scalar multiplication",
						"module_on(«Scalars»(M, l), «Vectors»(M, L)) ∧ (∀x:A. x ∈ L ⇒ permutation_map(p, x) ∈ L)",
						By(
							M,
							permutesOriginal,
							originalSubfield,
							scalarsSubfield,
							scalarsInOriginal,
							field_extension.ExtensionModuleOn.At(m, l, L),
							At(symmetric_group.SymmetricGroupMapsInto, L, p)))
					a.Show(
						"the source automorphism is linear over the scalars",
						By(
							preservesAddition,
							scalarPreservation,
							linearityData,
							module_homomorphism.ModuleHomomorphismDef.At(
								scalarRing, originalVectors, originalVectors, a.TermAs[Fun[A, A]]("permutation_map(p)"))))
				})
			// Setting either factor of the product formula to one gives the restriction to L and the fixed scalars; the product law then spreads from L, which spans N.
			productFormulaConsequences := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀c D L N:set(A). ∀p:permutation(A). ∀h:(A → A).",
				Hypotheses: []string{
					"subfield(M, c)",
					"subfield(M, L)",
					"subfield(M, N)",
					"c ⊆ N",
					"L ⊆ N",
					"p ∈ field_automorphisms(M, D, L)",
					"module_span(«Scalars»(M, c), «Vectors»(M, N), L) = N",
					"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), h)",
					"∀a x:A. a ∈ c ∧ x ∈ L ⇒ h(a * x) = a * permutation_map(p, x)",
				},
				Conclusion: "(∀x:A. x ∈ L ⇒ h(x) = permutation_map(p, x)) ∧ " +
					"(∀a:A. a ∈ c ⇒ h(a) = a) ∧ " +
					"(∀x y:A. x ∈ N ∧ y ∈ N ⇒ h(x * y) = h(x) * h(y))",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					c, D, L, N *Expr[Set[A]],
					p *Expr[symmetric_group.Permutation[A]],
					h *Expr[Fun[A, A]],
					largerConstantsSubfield, originalSubfield, compositumSubfield, largerInCompositum, originalInCompositum, sourceAutomorphism, originalSpans, extensionLinear, pureProductFormula Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")

					sourceMultiplicative := a.Have(
						"the source automorphism is multiplicative on the original field",
						"p ∈ symmetric_group(L) ∧ "+
							"(∀x y:A. "+
							"    x ∈ L ∧ y ∈ L ⇒ permutation_map(p, x * y) = permutation_map(p, x) * permutation_map(p, y))",
						BySets(sourceAutomorphism, field_automorphism.FieldAutomorphismsDef.At(m, D, L)))
					unitsAndCarriers := a.Have(
						"both fields contain one and the automorphism fixes it",
						"M.one ∈ c ∧ M.one ∈ L ∧ c ⊆ M.carrier ∧ L ⊆ M.carrier ∧ permutation_map(p, M.one) = M.one",
						By(
							M,
							sourceAutomorphism,
							originalSubfield,
							largerConstantsSubfield,
							field.SubfieldOne.At(m, c),
							field.SubfieldOne.At(m, L),
							field.SubfieldSubset.At(m, c),
							field.SubfieldSubset.At(m, L),
							field_automorphism.AutomorphismFixesUnits.At(m, D, L, p)))
					restriction := a.Have(
						"set the scalar factor to one to recover the source automorphism",
						"∀x:A. x ∈ L ⇒ h(x) = permutation_map(p, x)",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							inField := b.Assume()
							bothInAmbient := b.Have(
								"both terms lie in the ambient field",
								"x ∈ M.carrier ∧ permutation_map(p, x) ∈ M.carrier",
								BySets(
									inField,
									sourceMultiplicative,
									unitsAndCarriers,
									symmetric_group.SymmetricGroupMapsInto.At(L, p, x)))
							b.Show(
								"use one as the scalar factor",
								By(
									Normalized,
									pureProductFormula.At(b.TermAs[A]("M.one"), x),
									inField,
									bothInAmbient,
									unitsAndCarriers,
									comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))).AsFact().At(x),
									comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))).AsFact().At(
										b.TermAs[A]("permutation_map(p, x)"))))
						}))
					fixedScalars := a.Have(
						"set the original factor to one to fix the larger constants",
						"∀a:A. a ∈ c ⇒ h(a) = a",
						Derive(func(b *Argument) {
							scalar := b.FixAs[A]("a")
							inConstants := b.Assume()
							b.Show(
								"the product formula with second factor one fixes the scalar",
								BySets(
									pureProductFormula.At(scalar, b.TermAs[A]("M.one")),
									inConstants,
									unitsAndCarriers,
									comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))).AsFact().At(
										scalar)))
						}))
					productsOnOriginal := a.Have(
						"restriction transfers multiplication on the original field",
						"∀x y:A. x ∈ L ∧ y ∈ L ⇒ h(x * y) = h(x) * h(y)",
						By(Normalized, restriction, originalSubfield, sourceMultiplicative, At(field.SubfieldMul, m, L)))
					a.Show(
						"collect restriction, fixed scalars, and multiplication",
						By(
							M,
							productsOnOriginal,
							restriction,
							fixedScalars,
							originalSpans,
							compositumSubfield,
							largerConstantsSubfield,
							originalInCompositum,
							largerInCompositum,
							extensionLinear,
							At(multiplicationFromGenerators, m, c, L, N, h)))
				})
			// Two linear maps inverse on a spanning set are inverse on the whole module.
			inverseFromGenerators := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S:set(B). ∀h j:(B → B).",
				Hypotheses: []string{
					"module_homomorphism(R, M, M, h)",
					"module_homomorphism(R, M, M, j)",
					"module_span(R, M, S) = M.carrier",
					"∀x:B. x ∈ S ⇒ j(h(x)) = x",
					"∀x:B. x ∈ S ⇒ h(j(x)) = x",
				},
				Conclusion: "injective_on(M.carrier, h) ∧ image(h, M.carrier) = M.carrier",
			},
				func(
					a *Argument,
					R *Expr[module_record.RingOps[A]],
					M *Expr[module_record.ModuleOps[A, B]],
					S *Expr[Set[B]],
					h, j *Expr[Fun[B, B]],
					extensionLinear, inverseLinear, generatorsSpan, inverseAfterExtensionOnGenerators, extensionAfterInverseOnGenerators Fact,
				) {
					inverseModule := a.Have(
						"the source module structure is available",
						"module_on(R, M)",
						By(module_homomorphism.HomSource.Read(extensionLinear)))
					inverseComparisonsLinear := a.Have(
						"both compositions and the identity are linear",
						"module_homomorphism(R, M, M, h ∘ j) ∧ "+
							"module_homomorphism(R, M, M, j ∘ h) ∧ "+
							"module_homomorphism(R, M, M, identity_map)",
						By(
							inverseModule,
							extensionLinear,
							inverseLinear,
							module_homomorphism.HomCompose.At(R, M, M, M, j, h),
							module_homomorphism.HomCompose.At(R, M, M, M, h, j),
							module_homomorphism.HomIdentity.At(R, M)))
					generatorsInModule := a.Have(
						"the generators lie in the module they span",
						"S ⊆ M.carrier",
						BySets(generatorsSpan, submodule.SubsetSpan.At(R, M, S)))
					inverseAfterExtension := a.Have(
						"the inverse extension composed after the extension is the identity",
						"∀x:B. x ∈ M.carrier ⇒ j(h(x)) = x",
						Derive(func(b *Argument) {
							onGenerators := b.Have(
								"the inverse composition agrees with identity on generators",
								"∀x:B. x ∈ S ⇒ (j ∘ h)(x) = identity_map(x)",
								By(inverseAfterExtensionOnGenerators, functions.ComposeApply.At(j, h), functions.IdentityApply))
							onSpan := b.Have(
								"extend that agreement by linear uniqueness",
								"∀y:B. y ∈ module_span(R, M, S) ⇒ (j ∘ h)(y) = identity_map(y)",
								By(
									onGenerators,
									generatorsInModule,
									inverseComparisonsLinear,
									At(
										linear_independence.HomAgreeOnSpan,
										R,
										M,
										M,
										b.TermAs[Fun[B, B]]("j ∘ h"),
										b.TermAs[Fun[B, B]]("identity_map"),
										S)))
							x := b.FixAs[B]("x")
							inModule := b.Assume()
							b.Show(
								"the span of the generators is all of M",
								By(
									onSpan.At(x),
									generatorsSpan,
									inModule,
									functions.ComposeApply.At(j, h),
									functions.IdentityApply))
						}))
					extensionAfterInverse := a.Have(
						"the extension composed after its inverse extension is the identity",
						"∀x:B. x ∈ M.carrier ⇒ h(j(x)) = x",
						Derive(func(b *Argument) {
							onGenerators := b.Have(
								"the other composition agrees with identity on generators",
								"∀x:B. x ∈ S ⇒ (h ∘ j)(x) = identity_map(x)",
								By(extensionAfterInverseOnGenerators, functions.ComposeApply.At(h, j), functions.IdentityApply))
							onSpan := b.Have(
								"extend the other agreement by linear uniqueness",
								"∀y:B. y ∈ module_span(R, M, S) ⇒ (h ∘ j)(y) = identity_map(y)",
								By(
									onGenerators,
									generatorsInModule,
									inverseComparisonsLinear,
									At(
										linear_independence.HomAgreeOnSpan,
										R,
										M,
										M,
										b.TermAs[Fun[B, B]]("h ∘ j"),
										b.TermAs[Fun[B, B]]("identity_map"),
										S)))
							x := b.FixAs[B]("x")
							inModule := b.Assume()
							b.Show(
								"and again the span of the generators is all of M",
								By(
									onSpan.At(x),
									generatorsSpan,
									inModule,
									functions.ComposeApply.At(h, j),
									functions.IdentityApply))
						}))
					a.Show(
						"the two extended maps give a carrier bijection",
						By(
							module_homomorphism.HomIn.Read(extensionLinear),
							module_homomorphism.HomIn.Read(inverseLinear),
							extensionAfterInverse,
							inverseAfterExtension,
							functions.TwoSidedInverseBijection.At(
								a.TermAs[Set[B]]("M.carrier"), a.TermAs[Set[B]]("M.carrier"), h, j)))
				})
			// Extend an automorphism and its inverse through the tensor product; uniqueness makes their extensions inverse.
			extendAutomorphismMap := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀l c D L N:set(A). ∀f:(set(prod(A, A) → A) → A).",
				Hypotheses: []string{
					"subfield(M, l)",
					"subfield(M, c)",
					"subfield(M, L)",
					"subfield(M, N)",
					"l ⊆ c",
					"l ⊆ D",
					"l ⊆ L",
					"c ⊆ N",
					"L ⊆ N",
					"module_isomorphism(«Scalars»(M, c), «TensorModule»(M, l, c, L), «Vectors»(M, N), f)",
					"∀a x:A. a ∈ c ∧ x ∈ L ⇒ f(«PureTensor»(M, l, c, L, a, x)) = a * x",
				},
				Conclusion: "∀p:permutation(A). " +
					"    p ∈ field_automorphisms(M, D, L) ⇒ " +
					"    ∃h:(A → A). " +
					"        module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), h) ∧ " +
					"        (∀x:A. x ∈ L ⇒ h(x) = permutation_map(p, x)) ∧ " +
					"        (∀a:A. a ∈ c ⇒ h(a) = a) ∧ " +
					"        (∀x y:A. x ∈ N ∧ y ∈ N ⇒ h(x * y) = h(x) * h(y)) ∧ " +
					"        injective_on(N, h) ∧ " +
					"        image(h, N) = N",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					l, c, D, L, N *Expr[Set[A]],
					f *Expr[Fun[_Tensor, A]],
					exactConstantsSubfield, largerConstantsSubfield, originalSubfield, compositumSubfield, exactInLarger, exactInFixedBase, exactInOriginal, largerInCompositum, originalInCompositum, multiplicationIsomorphism, multiplicationOnPureTensors Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					largerScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, c)")
					compositumVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, N)")
					permutationGroup := a.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("permutation_group")

					originalSpans := a.Have(
						"the original field spans the compositum over the larger constants",
						"module_span(«Scalars»(M, c), «Vectors»(M, N), L) = N",
						By(
							M,
							multiplicationOnPureTensors,
							originalSubfield,
							largerConstantsSubfield,
							exactConstantsSubfield,
							originalInCompositum,
							exactInOriginal,
							exactInLarger,
							multiplicationIsomorphism,
							At(sourceSpansComposite, m, l, c, L, N, f)))
					p := a.FixAs[symmetric_group.Permutation[A]]("p")
					automorphism := a.Assume()
					inverseAutomorphism := a.Have(
						"the inverse source permutation is again a source automorphism",
						"permutation_inverse(p) ∈ field_automorphisms(M, D, L)",
						By(
							M,
							automorphism,
							field_automorphism.AutomorphismsSubgroup.At(m, D, L),
							group.SubgroupInv.At(
								permutationGroup,
								a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, D, L)"),
								p)))
					sourceMapsLinear := a.Have(
						"the source automorphism and its inverse are linear over the exact constants",
						"module_homomorphism(«Scalars»(M, l), «Vectors»(M, L), «Vectors»(M, L), permutation_map(p)) ∧ "+
							"module_homomorphism(«Scalars»(M, l), "+
							"    «Vectors»(M, L), "+
							"    «Vectors»(M, L), "+
							"    permutation_map(permutation_inverse(p)))",
						By(
							M,
							automorphism,
							inverseAutomorphism,
							originalSubfield,
							exactConstantsSubfield,
							exactInFixedBase,
							exactInOriginal,
							At(automorphismIsLinear, m, l, D, L, p),
							At(
								automorphismIsLinear,
								m,
								l,
								D,
								L,
								a.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(p)"))))
					h, forwardLift := a.ObtainAs[Fun[A, A]](
						"extend the source automorphism as a linear map",
						"∃h:(A → A). "+
							"    module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), h) ∧ "+
							"    (∀a x:A. a ∈ c ∧ x ∈ L ⇒ h(a * x) = a * permutation_map(p, x))",
						By(
							M,
							multiplicationOnPureTensors,
							originalSubfield,
							largerConstantsSubfield,
							exactConstantsSubfield,
							exactInOriginal,
							exactInLarger,
							sourceMapsLinear,
							multiplicationIsomorphism,
							At(linearTransport, m, l, c, L, N, f, a.TermAs[Fun[A, A]]("permutation_map(p)"))),
					)
					j, inverseLift := a.ObtainAs[Fun[A, A]](
						"extend the inverse source automorphism as a linear map",
						"∃j:(A → A). "+
							"    module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), j) ∧ "+
							"    (∀a x:A. a ∈ c ∧ x ∈ L ⇒ j(a * x) = a * permutation_map(permutation_inverse(p), x))",
						By(
							M,
							multiplicationOnPureTensors,
							originalSubfield,
							largerConstantsSubfield,
							exactConstantsSubfield,
							exactInOriginal,
							exactInLarger,
							sourceMapsLinear,
							multiplicationIsomorphism,
							At(
								linearTransport, m, l, c, L, N, f, a.TermAs[Fun[A, A]]("permutation_map(permutation_inverse(p))"))),
					)
					extensionProperties := a.Have(
						"the extended map restricts correctly, fixes constants, and preserves products",
						"(∀x:A. x ∈ L ⇒ h(x) = permutation_map(p, x)) ∧ "+
							"(∀a:A. a ∈ c ⇒ h(a) = a) ∧ "+
							"(∀x y:A. x ∈ N ∧ y ∈ N ⇒ h(x * y) = h(x) * h(y)) ∧ "+
							"(∀x:A. x ∈ L ⇒ j(x) = permutation_map(permutation_inverse(p), x))",
						By(
							M,
							originalSpans,
							automorphism,
							inverseAutomorphism,
							originalSubfield,
							compositumSubfield,
							largerConstantsSubfield,
							originalInCompositum,
							largerInCompositum,
							forwardLift,
							inverseLift,
							At(productFormulaConsequences, m, c, D, L, N, p, h),
							At(
								productFormulaConsequences,
								m,
								c,
								D,
								L,
								N,
								a.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(p)"),
								j)))
					inverseInvolution := a.Have(
						"taking the source permutation inverse twice gives the source permutation",
						"permutation_inverse(permutation_inverse(p)) = p",
						By(group.InvInv.Read(symmetric_group.SymmetricGroup).AsFact().At(p)))
					sourceImages := a.Have(
						"both source permutations preserve the original field carrier",
						"∀x:A. x ∈ L ⇒ permutation_map(p, x) ∈ L ∧ permutation_map(permutation_inverse(p), x) ∈ L",
						BySets(
							M,
							automorphism,
							inverseAutomorphism,
							field_automorphism.AutomorphismsSubgroup.At(m, D, L),
							At(symmetric_group.SymmetricGroupMapsInto, L, p),
							At(
								symmetric_group.SymmetricGroupMapsInto,
								L,
								a.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(p)"))))
					forwardProperties := a.Conjuncts(
						extensionProperties,
						"h agrees with p on L",
						"h fixes c",
						"h preserves products in N",
						"j agrees with the inverse of p on L")
					liftRestricts, liftFixesConstants, liftMultiplicative, inverseLiftRestricts :=
						forwardProperties[0], forwardProperties[1], forwardProperties[2], forwardProperties[3]
					inversesOnOriginal := a.Have(
						"the extended maps are inverse on the original field",
						"(∀x:A. x ∈ L ⇒ j(h(x)) = x) ∧ (∀x:A. x ∈ L ⇒ h(j(x)) = x)",
						SplitConj(
							Case(
								"the inverse extension undoes the extension on the original field",
								Derive(func(b *Argument) {
									x := b.FixAs[A]("x")
									inField := b.Assume()
									b.Show(
										"the inverse extension undoes the extension on the original field",
										By(
											Normalized,
											liftRestricts.At(x),
											inverseLiftRestricts.At(b.TermAs[A]("permutation_map(p, x)")),
											sourceImages.At(x),
											inField,
											symmetric_group.MapInverse.At(p, x)))
								})),
							Case(
								"the extension undoes its inverse on the original field",
								Derive(func(b *Argument) {
									x := b.FixAs[A]("x")
									inField := b.Assume()
									b.Show(
										"the extension undoes its inverse on the original field",
										By(
											Normalized,
											liftRestricts.At(b.TermAs[A]("permutation_map(permutation_inverse(p), x)")),
											inverseLiftRestricts.At(x),
											sourceImages.At(x),
											inverseInvolution,
											inField,
											symmetric_group.MapInverse.At(
												b.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(p)"), x)))
								})),
						))
					extendedBijection := a.Have(
						"spanning uniqueness makes the extended map bijective on the compositum",
						"injective_on(N, h) ∧ image(h, N) = N",
						By(
							originalSpans,
							inversesOnOriginal,
							forwardLift,
							inverseLift,
							At(inverseFromGenerators, largerScalars, compositumVectors, L, h, j)))
					a.Take(h)
					a.Show(
						"use the extended map and its extended inverse",
						By(liftMultiplicative, liftRestricts, liftFixesConstants, extendedBijection, forwardLift))
				})
			// A bijection on the carrier extends by the identity outside the carrier and determines a permutation.
			realizeCarrierPermutation := ctx.Lemma(Statement{
				Binders: "∀N:set(A). ∀h:(A → A).",
				Hypotheses: []string{
					"injective_on(N, h)",
					"image(h, N) = N",
				},
				Conclusion: "∃p:permutation(A). " +
					"    p ∈ symmetric_group(N) ∧ (∀x:A. x ∈ N ⇒ permutation_map(p, x) = h(x))",
			},
				func(a *Argument, N *Expr[Set[A]], h *Expr[Fun[A, A]], injective, onto Fact) {
					injectivityData := a.Unfolded(injective, functions.InjectiveOnDef)
					totalBijection := a.Have(
						"extend the carrier bijection by the identity outside its carrier",
						"injective_on(𝕌, λx:A. COND(x ∈ N, h(x), x)) ∧ image(λx:A. COND(x ∈ N, h(x), x), 𝕌) = 𝕌",
						Simp(Fwd(functions.InjectiveOnDef)),
						BySets(injectivityData, onto))
					a.Take(a.TermAs[symmetric_group.Permutation[A]]("permutation_of_map(λx:A. COND(x ∈ N, h(x), x))"))
					a.Show(
						"realize the carrier bijection as a permutation",
						BySets(
							totalBijection,
							At(symmetric_group.MapOfBijection, a.TermAs[Fun[A, A]]("λx:A. COND(x ∈ N, h(x), x)")),
							symmetric_group.InSymmetricGroup.At(
								N, a.TermAs[symmetric_group.Permutation[A]]("permutation_of_map(λx:A. COND(x ∈ N, h(x), x))"))))
				})
			// The fixed field of {p} is a subfield containing both generating sets, so it contains the field they generate.
			fixesAdjoinedField := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀N K S:set(A). ∀p:permutation(A).",
				Hypotheses: []string{
					"subfield(M, N)",
					"K ⊆ N",
					"S ⊆ N",
					"p ∈ field_automorphisms(M, ∅, N)",
					"∀x:A. x ∈ K ⇒ permutation_map(p, x) = x",
					"∀x:A. x ∈ S ⇒ permutation_map(p, x) = x",
				},
				Conclusion: "p ∈ field_automorphisms(M, field_adjoin(M, K, S), N)",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					N, K, S *Expr[Set[A]],
					p *Expr[symmetric_group.Permutation[A]],
					carrierSubfield, firstInCarrier, secondInCarrier, unbasedAutomorphism, fixesFirst, fixesSecond Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")

					generatorsFixed := a.Have(
						"the singleton subgroup fixes both generating sets",
						"{p} ⊆ field_automorphisms(M, ∅, N) ∧ K ⊆ fixed_field(N, {p}) ∧ S ⊆ fixed_field(N, {p})",
						BySets(
							fixesFirst,
							fixesSecond,
							unbasedAutomorphism,
							firstInCarrier,
							secondInCarrier,
							field_automorphism.FixedFieldDef.At(N, a.TermAs[Set[symmetric_group.Permutation[A]]]("{p}"))))
					singletonFixedField := a.Have(
						"the singleton subgroup has a subfield as its fixed field",
						"subfield(M, fixed_field(N, {p}))",
						By(
							M,
							carrierSubfield,
							generatorsFixed,
							field_automorphism.FixedFieldSubfield.At(
								m, N, a.TermAs[Set[symmetric_group.Permutation[A]]]("{p}"))))
					generatedFieldFixed := a.Have(
						"leastness puts the generated field in the singleton fixed field",
						"field_adjoin(M, K, S) ⊆ fixed_field(N, {p})",
						By(
							M,
							singletonFixedField,
							generatorsFixed,
							algebraic_element.AdjoinLeast.At(m, K, S, a.TermAs[Set[A]]("fixed_field(N, {p})"))))
					a.Show(
						"the permutation fixes the field generated by both sets",
						BySets(
							M,
							generatedFieldFixed,
							generatorsFixed,
							field_automorphism.FixedFieldAutomorphisms.At(
								m, N, a.TermAs[Set[symmetric_group.Permutation[A]]]("{p}")),
							field_automorphism.AutomorphismsAntitone.At(
								m, a.TermAs[Set[A]]("field_adjoin(M, K, S)"), a.TermAs[Set[A]]("fixed_field(N, {p})"), N)))
				})
			// The permutation realizing h is additive, h being linear, and multiplicative; fixing c and t, it fixes the field c(t) they generate.
			realizeFieldAutomorphism := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀c N:set(A). ∀t:A. ∀h:(A → A).",
				Hypotheses: []string{
					"subfield(M, N)",
					"c ⊆ N",
					"t ∈ N",
					"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), h)",
					"∀x y:A. x ∈ N ∧ y ∈ N ⇒ h(x * y) = h(x) * h(y)",
					"∀a:A. a ∈ c ⇒ h(a) = a",
					"h(t) = t",
					"injective_on(N, h)",
					"image(h, N) = N",
				},
				Conclusion: "∃q:permutation(A). " +
					"    q ∈ field_automorphisms(M, field_adjoin(M, c, {t}), N) ∧ " +
					"    (∀x:A. x ∈ N ⇒ permutation_map(q, x) = h(x))",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					c, N *Expr[Set[A]],
					t *Expr[A],
					h *Expr[Fun[A, A]],
					compositumSubfield, constantsInCompositum, parameterInCompositum, mapLinear, mapMultiplicative, mapFixesConstants, mapFixesParameter, mapInjective, mapOnto Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					constantScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, c)")
					compositumVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, N)")

					q, realizedPermutation := a.ObtainAs[symmetric_group.Permutation[A]](
						"realize the carrier bijection by a permutation",
						"∃q:permutation(A). q ∈ symmetric_group(N) ∧ (∀x:A. x ∈ N ⇒ permutation_map(q, x) = h(x))",
						By(mapOnto, mapInjective, At(realizeCarrierPermutation, N, h)),
					)
					carrierPermutation := a.Conjuncts(
						realizedPermutation,
						"the realized permutation preserves the carrier",
						"the realized permutation agrees with the carrier map")
					permutesCompositum, agreesWithMap := carrierPermutation[0], carrierPermutation[1]
					permutationLinear := a.Have(
						"agreement with the linear carrier map makes the permutation linear",
						"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), permutation_map(q))",
						By(
							agreesWithMap,
							mapLinear,
							module_homomorphism.HomCongruence.At(
								constantScalars,
								compositumVectors,
								compositumVectors,
								h,
								a.TermAs[Fun[A, A]]("permutation_map(q)"))))
					permutationMultiplicative := a.Have(
						"agreement transfers the product law to the permutation",
						"∀x y:A. x ∈ N ∧ y ∈ N ⇒ permutation_map(q, x * y) = permutation_map(q, x) * permutation_map(q, y)",
						By(Normalized, mapMultiplicative, agreesWithMap, compositumSubfield, At(field.SubfieldMul, m, N)))
					unbasedAutomorphism := a.Have(
						"the realized permutation is a field automorphism of the compositum",
						"q ∈ field_automorphisms(M, ∅, N)",
						BySets(
							module_homomorphism.HomAdd.Read(permutationLinear),
							permutationMultiplicative,
							permutesCompositum,
							field_automorphism.FieldAutomorphismsDef.At(m, a.TermAs[Set[A]]("∅"), N)))
					scalarAndParameterFixed := a.Have(
						"the realized permutation fixes the new constants and the parameter",
						"(∀a:A. a ∈ c ⇒ permutation_map(q, a) = a) ∧ (∀x:A. x ∈ {t} ⇒ permutation_map(q, x) = x) ∧ {t} ⊆ N",
						BySets(
							agreesWithMap,
							mapFixesConstants,
							mapFixesParameter,
							parameterInCompositum,
							constantsInCompositum))
					a.Take(q)
					a.Show(
						"the realized permutation is the required field automorphism",
						By(
							M,
							agreesWithMap,
							unbasedAutomorphism,
							compositumSubfield,
							constantsInCompositum,
							scalarAndParameterFixed,
							At(fixesAdjoinedField, m, N, c, a.TermAs[Set[A]]("{t}"), q)))
				})
			// Both automorphisms are linear over c, so agreement on the spanning set L is agreement on N.
			uniqueAutomorphismExtension := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀c E L N:set(A). ∀p q:permutation(A).",
				Hypotheses: []string{
					"subfield(M, c)",
					"subfield(M, N)",
					"c ⊆ E",
					"c ⊆ N",
					"module_span(«Scalars»(M, c), «Vectors»(M, N), L) = N",
					"p ∈ field_automorphisms(M, E, N)",
					"q ∈ field_automorphisms(M, E, N)",
					"∀x:A. x ∈ L ⇒ permutation_map(p, x) = permutation_map(q, x)",
				},
				Conclusion: "p = q",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					c, E, L, N *Expr[Set[A]],
					p, q *Expr[symmetric_group.Permutation[A]],
					largerConstantsSubfield, compositumSubfield, largerInFixedBase, largerInCompositum, originalSpans, pAutomorphism, qAutomorphism, agreeOnOriginal Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					largerScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, c)")
					compositumVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, N)")

					comparisonMapsLinear := a.Have(
						"both target automorphisms are linear over the larger constants",
						"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), permutation_map(p)) ∧ "+
							"module_homomorphism(«Scalars»(M, c), «Vectors»(M, N), «Vectors»(M, N), permutation_map(q))",
						By(
							M,
							pAutomorphism,
							qAutomorphism,
							compositumSubfield,
							largerConstantsSubfield,
							largerInFixedBase,
							largerInCompositum,
							At(automorphismIsLinear, m, c, E, N, p),
							At(automorphismIsLinear, m, c, E, N, q)))
					originalInCompositum := a.Have(
						"the original field lies in the compositum it spans",
						"L ⊆ N",
						BySets(originalSpans, submodule.SubsetSpan.At(largerScalars, compositumVectors, L)))
					agreementOnComposite := a.Have(
						"agreement on the original spanning field gives agreement on the compositum",
						"∀x:A. x ∈ N ⇒ permutation_map(p, x) = permutation_map(q, x)",
						By(
							Normalized,
							agreeOnOriginal,
							originalSpans,
							originalInCompositum,
							comparisonMapsLinear,
							At(
								linear_independence.HomAgreeOnSpan,
								largerScalars,
								compositumVectors,
								compositumVectors,
								a.TermAs[Fun[A, A]]("permutation_map(p)"),
								a.TermAs[Fun[A, A]]("permutation_map(q)"),
								L)))
					targetPermutations := a.Have(
						"both target automorphisms are permutations of the compositum carrier",
						"p ∈ symmetric_group(N) ∧ q ∈ symmetric_group(N)",
						BySets(M, pAutomorphism, qAutomorphism, field_automorphism.AutomorphismsSubgroup.At(m, E, N)))
					a.Show(
						"agreement everywhere makes the permutations equal",
						By(
							Normalized,
							agreementOnComposite,
							targetPermutations,
							symmetric_group.InSymmetricGroup.At(N, p),
							symmetric_group.InSymmetricGroup.At(N, q),
							symmetric_group.PermutationEq.At(p, q)))
				})
			// Equal extensions restrict to equal maps on L, and a permutation of L is the identity off L.
			extensionInjective := ctx.Lemma(Statement{
				Binders: "∀L:set(A). ∀G:set(permutation(A)). ∀rho:(permutation(A) → permutation(A)).",
				Hypotheses: []string{
					"G ⊆ symmetric_group(L)",
					"∀s:permutation(A). s ∈ G ⇒ ∀x:A. x ∈ L ⇒ permutation_map(rho(s), x) = permutation_map(s, x)",
				},
				Conclusion: "injective_on(G, rho)",
			},
				func(
					a *Argument,
					L *Expr[Set[A]],
					G *Expr[Set[symmetric_group.Permutation[A]]],
					rho *Expr[Fun[symmetric_group.Permutation[A], symmetric_group.Permutation[A]]],
					permutesOriginal, extensionRestricts Fact,
				) {
					a.Do(Unfold(functions.InjectiveOnDef))
					x := a.FixAs[symmetric_group.Permutation[A]]("x")
					y := a.FixAs[symmetric_group.Permutation[A]]("y")
					agreement := a.Assume()
					restrictionAgreement := a.Have(
						"equal extensions give equal source restrictions",
						"∀z:A. z ∈ L ⇒ permutation_map(x, z) = permutation_map(y, z)",
						By(Normalized, extensionRestricts.At(x), extensionRestricts.At(y), agreement))
					sourcePermutations := a.Have(
						"both source automorphisms are permutations of the original field carrier",
						"x ∈ symmetric_group(L) ∧ y ∈ symmetric_group(L)",
						BySets(permutesOriginal, agreement))
					a.Show(
						"compare the source permutations on and outside their carrier",
						By(
							Normalized,
							restrictionAgreement,
							sourcePermutations,
							symmetric_group.InSymmetricGroup.At(L, x),
							symmetric_group.InSymmetricGroup.At(L, y),
							symmetric_group.PermutationEq.At(x, y)))
				})
			return ctx.Theorem(headline,
				func(
					a *Argument,
					M field.FieldFact[on.M],
					k, l, K, L *Expr[Set[A]],
					t *Expr[A],
					r, R *Expr[Nat],
					algebraicallyClosed, baseSubfield, baseFinite, exactConstantsDef, functionFieldSubfield, intermediateSubfield, baseInIntermediate, intermediateInFunctionField, parameterInIntermediate, transcendentalOverBase, galoisOriginal, exactConstantsCard, enlargedExponentPositive, exponentDivides Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					exactScalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, l)")
					permutationGroup := a.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("permutation_group")

					originalGaloisData := a.Unfolded(galoisOriginal, galois_correspondence.GaloisOverDef)
					exactConstants := a.Have(
						"the exact constants form a finite subfield and the function field is regular over them",
						"finite(l) ∧ subfield(M, l) ∧ regular_function_field(M, l, L)",
						By(
							M,
							baseFinite,
							transcendentalOverBase,
							exactConstantsDef,
							parameterInIntermediate,
							functionFieldSubfield,
							baseSubfield,
							intermediateInFunctionField,
							baseInIntermediate,
							originalGaloisData,
							set_order.SubsetTrans,
							set_basic.SubsetDef,
							function_field.ExactConstantFieldFinite.At(m, k, L, t)))
					towerAndParameter := a.Have(
						"k ⊆ l ⊆ L, and t lies in L",
						"k ⊆ l ∧ l ⊆ L ∧ t ∈ L",
						BySets(
							M,
							exactConstantsDef,
							parameterInIntermediate,
							baseSubfield,
							intermediateInFunctionField,
							baseInIntermediate,
							At(algebraic_element.MemberAlgebraic, m, k)))
					c, cDef := a.LetAs[Set[A]]("c", "finite_constants(field_ring(M), card(k), R)")
					largerVectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, c)")
					enlargedConstants := a.Have(
						"the enlarged finite constants contain the original finite base",
						"subfield(M, c) ∧ k ⊆ c ∧ has_size(c, card(k) ^ R)",
						By(
							Normalized,
							algebraicallyClosed,
							M,
							baseFinite,
							enlargedExponentPositive,
							cDef,
							baseSubfield,
							finite_field.FiniteConstantsSubfield.At(m, k, R)))
					exactConstantField := a.Have(
						"the exact constants carry their restricted field structure",
						"l ⊆ M.carrier ∧ field_on(restrict_field(M, l))",
						By(M, exactConstants, field.SubfieldFieldOn.At(m, l)))
					frobeniusConstants := a.Have(
						"the exact constants satisfy the Frobenius equation of their exponent",
						"l ⊆ finite_constants(field_ring(M), card(k), r)",
						BySets(
							exactConstantsCard,
							exactConstantField,
							exactConstants,
							At(finite_field.FiniteFieldFixedByFrobenius, a.TermAs[FieldOps[A]]("restrict_field(M, l)")),
							finite_field.FiniteConstantsDef.At(
								a.TermAs[module_record.RingOps[A]]("field_ring(M)"), a.TermAs[Nat]("card(k)"), r)))
					constantsIncluded := a.Have(
						"divisibility of the exponents includes the exact constants in the enlarged constants",
						"l ⊆ c",
						By(
							Normalized,
							field.RingOn.Read(M),
							cDef,
							exponentDivides,
							frobeniusConstants,
							finite_field.FiniteConstantsMono.At(
								a.TermAs[module_record.RingOps[A]]("field_ring(M)"), a.TermAs[Nat]("card(k)"), r, R),
							set_order.SubsetTrans))
					scalarExtensionModule := a.Have(
						"the enlarged constants form a module over the exact constants",
						"module_on(«Scalars»(M, l), «Vectors»(M, c))",
						By(
							constantsIncluded,
							exactConstants,
							enlargedConstants,
							field_extension.ExtensionModuleOn.Read(M).AsFact().At(l, c)))
					finiteScalarSpan := a.Have(
						"the finite scalar carrier spans itself",
						"∃S:set(A). finite(S) ∧ S ⊆ c ∧ module_span(«Scalars»(M, l), «Vectors»(M, c), S) = c",
						Derive(func(b *Argument) {
							b.Take(c)
							b.Show(
								"a finite carrier submodule is its own span",
								By(
									submodule.CarrierSubmodule.Read(scalarExtensionModule),
									enlargedConstants,
									cardinality.HasSizeDef.At(c, b.TermAs[Nat]("card(k) ^ R")),
									submodule.SpanOfSubmodule.At(exactScalars, largerVectors, c),
									set_order.SubsetRefl))
						}))
					finiteOverExact := a.Have(
						"the enlarged constants are finite over the exact constants",
						"finite_extension(M, l, c)",
						By(
							finiteScalarSpan,
							exactConstants,
							field.SubfieldRingSubfield.Read(M).At(l, l),
							module_dimension.FiniteDimensionalSpanning.Read(scalarExtensionModule).AsFact().At(
								a.TermAs[Fun[A, A]]("M.inv")),
							field_extension.FiniteExtensionDef.At(m, l, c)))
					constantExtension := a.Conjuncts(
						GroupPremises(
							M,
							exactConstants,
							enlargedConstants,
							constantsIncluded,
							finiteOverExact,
							constant_composite.RegularConstantExtension.At(m, l, L, c)),
						"Lc is regular over c",
						"multiplication c ⊗ₗ L → Lc is an isomorphism that "+
							"keeps separability and degree over the rational fields")
					regularComposite, multiplicationExists := constantExtension[0], constantExtension[1]
					parameterTranscendental := a.Have(
						"regularity keeps the parameter transcendental over the exact constants",
						"¬algebraic_over(M, l, t)",
						Derive(func(b *Argument) {
							regularityData := b.Unfolded(exactConstants, function_field.RegularFunctionFieldDef)
							b.Show(
								"an algebraic parameter would lie in the exact constants",
								BySets(transcendentalOverBase, exactConstantsDef, regularityData, towerAndParameter))
						}))
					B, bDef := a.LetAs[Set[A]]("B", "field_adjoin(M, k, {t})")
					D, dDef := a.LetAs[Set[A]]("D", "field_adjoin(M, l, {t})")
					E, eDef := a.LetAs[Set[A]]("E", "field_adjoin(M, c, {t})")
					N, nDef := a.LetAs[Set[A]]("N", "constant_composite(M, L, c)")
					sourceGroup := a.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("galois_group(M, D, L)")
					targetGroup := a.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("galois_group(M, E, N)")
					geometricBase := a.Have(
						"D = l(t) is a subfield between l and L holding t",
						"subfield(M, D) ∧ l ⊆ D ∧ t ∈ D ∧ D ⊆ L",
						By(
							Normalized,
							M,
							dDef,
							exactConstants,
							functionFieldSubfield,
							towerAndParameter,
							At(algebraic_element.AdjoinElementBetween, m, l, L, t)))
					baseInGeometricBase := a.Have(
						"k ⊆ l ⊆ D",
						"k ⊆ D",
						BySets(towerAndParameter, geometricBase))
					rationalBase := a.Have(
						"B = k(t) is a subfield between k and D holding t",
						"subfield(M, B) ∧ k ⊆ B ∧ t ∈ B ∧ B ⊆ D",
						By(
							Normalized,
							M,
							bDef,
							baseSubfield,
							geometricBase,
							baseInGeometricBase,
							At(algebraic_element.AdjoinElementBetween, m, k, D, t)))
					geometricGalois := a.Have(
						"the original function field is Galois over its geometric rational base",
						"galois_over(M, D, L)",
						By(
							M,
							functionFieldSubfield,
							rationalBase,
							geometricBase,
							galoisOriginal,
							galois_correspondence.GaloisTower.At(m, B, D, L)))
					geometricGaloisData := a.Unfolded(geometricGalois, galois_correspondence.GaloisOverDef)
					f, multiplicationIsoData := a.UnpackAs[Fun[_Tensor, A]](multiplicationExists)
					scalarExtensionData := a.Conjuncts(
						multiplicationIsoData,
						"multiplication is a module isomorphism",
						"multiplication sends pure tensors to products",
						"rational base change preserves separability and degree")
					multiplicationIsomorphism, multiplicationOnPureTensors, rationalBaseChange :=
						scalarExtensionData[0], scalarExtensionData[1], scalarExtensionData[2]
					baseChangedDegree := a.Have(
						"regular constant extension preserves finite degree and separability",
						"finite_extension(M, E, N) ∧ "+
							"(∀x:A. x ∈ N ⇒ separable_over(M, E, x)) ∧ "+
							"extension_degree(M, E, N) = extension_degree(M, D, L)",
						By(
							Normalized,
							parameterTranscendental,
							rationalBaseChange.At(t),
							dDef,
							eDef,
							towerAndParameter,
							geometricGaloisData))
					degreeEqualsSourceGroup := a.Have(
						"the new degree equals the order of the geometric automorphism group",
						"extension_degree(M, E, N) = card(field_automorphisms(M, D, L))",
						By(
							Normalized,
							M,
							functionFieldSubfield,
							geometricBase,
							geometricGaloisData,
							baseChangedDegree,
							geometricGalois,
							galois_correspondence.GaloisIffCard.At(m, D, L)))
					compositeField := a.Have(
						"the compositum is a subfield containing the enlarged constants",
						"subfield(M, N) ∧ c ⊆ N",
						By(regularComposite, function_field.RegularFunctionFieldDef.At(m, c, N)))
					originalInComposite := a.Have(
						"the original function field lies in the compositum",
						"L ⊆ N",
						By(
							Normalized,
							M,
							nDef,
							functionFieldSubfield,
							enlargedConstants,
							field.SubfieldSubset.At(m, L),
							field.SubfieldSubset.At(m, c),
							algebraic_element.AdjoinSubfield.At(m, L, c),
							constant_composite.ConstantCompositeDef.At(m, L, c)))
					parameterInN := a.Have(
						"t ∈ L ⊆ N",
						"t ∈ N",
						BySets(towerAndParameter, originalInComposite))
					newBase := a.Have(
						"E = c(t) is a subfield between c and N holding t",
						"subfield(M, E) ∧ c ⊆ E ∧ t ∈ E ∧ E ⊆ N",
						By(
							Normalized,
							M,
							eDef,
							enlargedConstants,
							compositeField,
							parameterInN,
							At(algebraic_element.AdjoinElementBetween, m, c, N, t)))
					originalSpansComposite := a.Have(
						"the original function field spans the compositum over the enlarged constants",
						"module_span(«Scalars»(M, c), «Vectors»(M, N), L) = N",
						By(
							M,
							multiplicationOnPureTensors,
							functionFieldSubfield,
							originalInComposite,
							constantsIncluded,
							exactConstants,
							enlargedConstants,
							towerAndParameter,
							multiplicationIsomorphism,
							At(sourceSpansComposite, m, l, c, L, N, f)))
					permutationExtensions := a.Have(
						"each source automorphism extends to an automorphism over the new rational base",
						Statement{
							Binders: "∀p:permutation(A).",
							Hypotheses: []string{
								"p ∈ field_automorphisms(M, D, L)",
							},
							Conclusion: "∃q:permutation(A). " +
								"    q ∈ field_automorphisms(M, E, N) ∧ " +
								"    (∀x:A. x ∈ L ⇒ permutation_map(q, x) = permutation_map(p, x))",
						},
						Derive(func(b *Argument) {
							p := b.FixAs[symmetric_group.Permutation[A]]("p")
							sourceAutomorphism := b.Assume()
							h, chosenCarrierLift := b.UnpackAs[Fun[A, A]](GroupPremises(
								M,
								exactConstants,
								enlargedConstants,
								functionFieldSubfield,
								compositeField,
								constantsIncluded,
								geometricBase,
								towerAndParameter,
								originalInComposite,
								scalarExtensionData[0],
								scalarExtensionData[1],
								sourceAutomorphism,
								At(extendAutomorphismMap, m, l, c, D, L, N, f, p)))
							carrierExtensionData := b.Conjuncts(
								chosenCarrierLift,
								"the chosen carrier extension is linear",
								"the chosen carrier extension agrees on the original field",
								"the chosen carrier extension fixes constants",
								"the chosen carrier extension preserves products",
								"the chosen carrier extension is injective",
								"the chosen carrier extension is onto")
							liftLinear, liftRestricts, liftFixesConstants :=
								carrierExtensionData[0], carrierExtensionData[1], carrierExtensionData[2]
							liftMultiplicative, liftInjective, liftOnto :=
								carrierExtensionData[3], carrierExtensionData[4], carrierExtensionData[5]
							parameterFixed := b.Have(
								"the extension fixes the parameter and the parameter lies in the compositum",
								"h(t) = t ∧ t ∈ N",
								BySets(
									liftRestricts.At(t),
									sourceAutomorphism,
									parameterInN,
									geometricBase,
									field_automorphism.FieldAutomorphismsDef.At(m, D, L)))
							q, basedPermutation := b.ObtainAs[symmetric_group.Permutation[A]](
								"realize the carrier extension over the new rational base",
								"∃q:permutation(A). "+
									"    q ∈ field_automorphisms(M, E, N) ∧ (∀x:A. x ∈ N ⇒ permutation_map(q, x) = h(x))",
								By(
									M,
									liftMultiplicative,
									liftFixesConstants,
									eDef,
									liftOnto,
									liftInjective,
									parameterFixed,
									compositeField,
									liftLinear,
									At(realizeFieldAutomorphism, m, c, N, t, h)),
							)
							b.Take(q)
							b.Show(
								"the realized automorphism agrees with the source on the original field",
								BySets(liftRestricts, originalInComposite, basedPermutation))
						}))
					rho, rhoDef := a.LetAs[Fun[symmetric_group.Permutation[A], symmetric_group.Permutation[A]]](
						"ρ",
						"λs:permutation(A). εq:permutation(A). "+
							"    q ∈ field_automorphisms(M, E, N) ∧ "+
							"    (∀x:A. x ∈ L ⇒ permutation_map(q, x) = permutation_map(s, x))")
					extensionsUnique := a.Have(
						"target automorphisms agreeing on the original field are equal",
						Statement{
							Binders: "∀p q:permutation(A).",
							Hypotheses: []string{
								"p ∈ field_automorphisms(M, E, N)",
								"q ∈ field_automorphisms(M, E, N)",
								"∀x:A. x ∈ L ⇒ permutation_map(p, x) = permutation_map(q, x)",
							},
							Conclusion: "p = q",
						},
						By(
							M,
							originalSpansComposite,
							compositeField,
							enlargedConstants,
							newBase,
							At(uniqueAutomorphismExtension, m, c, E, L, N)))
					rhoExtends := a.Have(
						"ρ(s) is an automorphism of N over E that restricts to s on L",
						Statement{
							Binders: "∀s:permutation(A).",
							Hypotheses: []string{
								"s ∈ field_automorphisms(M, D, L)",
							},
							Conclusion: "ρ(s) ∈ field_automorphisms(M, E, N) ∧ " +
								"(∀x:A. x ∈ L ⇒ permutation_map(ρ(s), x) = permutation_map(s, x))",
						},
						Derive(func(b *Argument) {
							s := b.FixAs[symmetric_group.Permutation[A]]("s")
							sourceAutomorphism := b.Assume()
							b.Do(rhoDef.Rw())
							b.Show(
								"an extension of s exists, so the choice ρ(s) is one",
								By(permutationExtensions.At(s), sourceAutomorphism))
						}))
					finiteGroupBounds := a.Have(
						"both automorphism groups are finite and the target order is at most the source order",
						"finite(field_automorphisms(M, D, L)) ∧ "+
							"finite(field_automorphisms(M, E, N)) ∧ "+
							"card(field_automorphisms(M, E, N)) ≤ card(field_automorphisms(M, D, L))",
						By(
							Normalized,
							M,
							degreeEqualsSourceGroup,
							functionFieldSubfield,
							compositeField,
							geometricBase,
							newBase,
							geometricGaloisData,
							baseChangedDegree,
							field_automorphism.AutomorphismsBound.At(m, D, L),
							field_automorphism.AutomorphismsBound.At(m, E, N)))
					sourceGroupPermutations := a.Have(
						"source automorphisms lie in the permutation group of the original field",
						"field_automorphisms(M, D, L) ⊆ symmetric_group(L)",
						By(M, field_automorphism.AutomorphismsSubgroup.At(m, D, L)))
					rhoInjective := a.Have(
						"restriction to L makes ρ injective",
						"injective_on(field_automorphisms(M, D, L), ρ)",
						By(
							Normalized,
							rhoExtends,
							sourceGroupPermutations,
							At(
								extensionInjective,
								L,
								a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, D, L)"),
								rho)))
					rhoMapsInto := a.Have(
						"ρ maps Aut(L/D) into Aut(N/E)",
						"image(ρ, field_automorphisms(M, D, L)) ⊆ field_automorphisms(M, E, N)",
						BySets(rhoExtends))
					rhoOnto := a.Have(
						"the order bound and injectivity make ρ onto",
						"image(ρ, field_automorphisms(M, D, L)) = field_automorphisms(M, E, N)",
						By(
							Normalized,
							rhoInjective,
							rhoMapsInto,
							finiteGroupBounds,
							cardinality.CardImageInj.At(
								rho, a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, D, L)")),
							cardinality.CardSubsetLe.At(
								a.TermAs[Set[symmetric_group.Permutation[A]]]("image(ρ, field_automorphisms(M, D, L))"),
								a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, E, N)"))))
					baseChangedGalois := a.Have(
						"the target automorphism order equals the degree, so the base change is Galois",
						"galois_over(M, E, N)",
						By(
							Normalized,
							M,
							rhoOnto,
							degreeEqualsSourceGroup,
							rhoInjective,
							newBase,
							compositeField,
							finiteGroupBounds,
							baseChangedDegree,
							cardinality.CardImageInj.At(
								rho, a.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, D, L)")),
							galois_correspondence.GaloisIffCard.At(m, E, N)))
					rhoMultiplicative := a.Have(
						"uniqueness of extensions makes ρ respect composition",
						Statement{
							Binders: "∀s t:permutation(A).",
							Hypotheses: []string{
								"s ∈ field_automorphisms(M, D, L)",
								"t ∈ field_automorphisms(M, D, L)",
							},
							Conclusion: "ρ(s * t) = ρ(s) * ρ(t)",
						},
						Derive(func(b *Argument) {
							sigma := b.FixAs[symmetric_group.Permutation[A]]("sigma")
							tau := b.FixAs[symmetric_group.Permutation[A]]("tau")
							members := b.Assume()
							sourceProduct := b.Have(
								"the product of two source automorphisms belongs to the source group",
								"sigma * tau ∈ field_automorphisms(M, D, L)",
								By(
									M,
									members,
									field_automorphism.AutomorphismsSubgroup.At(m, D, L),
									group.SubgroupMul.At(
										permutationGroup,
										b.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, D, L)"),
										sigma,
										tau)))
							chosenProductImages := b.Have(
								"ρ(σ), ρ(τ) and ρ(στ) are automorphisms of N over E extending σ, τ and στ",
								"ρ(sigma) ∈ field_automorphisms(M, E, N) ∧ "+
									"ρ(tau) ∈ field_automorphisms(M, E, N) ∧ "+
									"ρ(sigma * tau) ∈ field_automorphisms(M, E, N) ∧ "+
									"(∀x:A. x ∈ L ⇒ permutation_map(ρ(sigma), x) = permutation_map(sigma, x)) ∧ "+
									"(∀x:A. x ∈ L ⇒ permutation_map(ρ(tau), x) = permutation_map(tau, x)) ∧ "+
									"(∀x:A. x ∈ L ⇒ permutation_map(ρ(sigma * tau), x) = permutation_map(sigma * tau, x))",
								By(
									Normalized,
									rhoExtends.At(sigma),
									rhoExtends.At(tau),
									rhoExtends.At(b.TermAs[symmetric_group.Permutation[A]]("sigma * tau")),
									sourceProduct,
									members))
							targetProductMembers := b.Conjuncts(
								chosenProductImages,
								"ρ(σ) is an automorphism of N over E",
								"ρ(τ) is an automorphism of N over E",
								"ρ(στ) is an automorphism of N over E",
								"ρ(σ) agrees with σ on L",
								"ρ(τ) agrees with τ on L",
								"ρ(στ) agrees with στ on L")
							sigmaExtended, tauExtended, productExtended :=
								targetProductMembers[0], targetProductMembers[1], targetProductMembers[2]
							sigmaRestricts, tauRestricts, productRestricts :=
								targetProductMembers[3], targetProductMembers[4], targetProductMembers[5]
							targetProduct := b.Have(
								"ρ(σ)ρ(τ) is an automorphism of N over E",
								"ρ(sigma) * ρ(tau) ∈ field_automorphisms(M, E, N)",
								By(
									M,
									sigmaExtended,
									tauExtended,
									field_automorphism.AutomorphismsSubgroup.At(m, E, N),
									group.SubgroupMul.At(
										permutationGroup,
										b.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, E, N)"),
										b.TermAs[symmetric_group.Permutation[A]]("ρ(sigma)"),
										b.TermAs[symmetric_group.Permutation[A]]("ρ(tau)"))))
							productAgreement := b.Have(
								"ρ(στ) and ρ(σ)ρ(τ) agree on L",
								"∀x:A. x ∈ L ⇒ permutation_map(ρ(sigma * tau), x) = permutation_map(ρ(sigma) * ρ(tau), x)",
								Derive(func(a *Argument) {
									x := a.FixAs[A]("x")
									inField := a.Assume()
									tauImage := a.Have(
										"the second source automorphism preserves the original field",
										"permutation_map(tau, x) ∈ L",
										BySets(
											inField,
											sourceGroupPermutations,
											members,
											symmetric_group.SymmetricGroupMapsInto.At(L, tau, x)))
									a.Show(
										"compare both composite maps at that original field element",
										By(
											Normalized,
											sigmaRestricts.At(a.TermAs[A]("permutation_map(tau, x)")),
											tauRestricts.At(x),
											productRestricts.At(x),
											inField,
											tauImage,
											symmetric_group.MapCompose.At(sigma, tau, x),
											symmetric_group.MapCompose.At(
												a.TermAs[symmetric_group.Permutation[A]]("ρ(sigma)"),
												a.TermAs[symmetric_group.Permutation[A]]("ρ(tau)"),
												x)))
								}))
							b.Show(
								"uniqueness of extensions gives ρ(στ) = ρ(σ)ρ(τ)",
								By(
									productAgreement,
									extensionsUnique.At(
										b.TermAs[symmetric_group.Permutation[A]]("ρ(sigma * tau)"),
										b.TermAs[symmetric_group.Permutation[A]]("ρ(sigma) * ρ(tau)")),
									productExtended,
									targetProduct))
						}))
					automorphismGroups := a.Have(
						"both Galois groups are groups on their sets",
						"group_on(galois_group(M, D, L)) ∧ group_on(galois_group(M, E, N))",
						By(M, field_automorphism.GaloisGroupOn.At(m, D, L), field_automorphism.GaloisGroupOn.At(m, E, N)))
					rhoIsomorphism := a.Have(
						"ρ is a group isomorphism",
						"group_isomorphism(galois_group(M, D, L), galois_group(M, E, N), ρ)",
						By(
							Normalized,
							rhoMultiplicative,
							rhoExtends,
							rhoOnto,
							rhoInjective,
							automorphismGroups,
							group_homomorphism.GroupHomomorphism.At(sourceGroup, targetGroup, rho),
							group_homomorphism.GroupIsomorphismDef.At(sourceGroup, targetGroup, rho)))
					Kl, klDef := a.LetAs[Set[A]]("Kl", "constant_composite(M, K, l)")
					Kc, kcDef := a.LetAs[Set[A]]("Kc", "constant_composite(M, K, c)")
					intermediateGenerators := a.Have(
						"the intermediate generators lie in the ambient field",
						"K ⊆ M.carrier ∧ l ⊆ M.carrier ∧ c ⊆ M.carrier",
						By(
							intermediateSubfield,
							exactConstants,
							enlargedConstants,
							field.SubfieldSubset.At(m, K),
							field.SubfieldSubset.At(m, l),
							field.SubfieldSubset.At(m, c)))
					intermediateComposita := a.Have(
						"both intermediate composita are subfields containing their generators",
						"subfield(M, Kl) ∧ K ⊆ Kl ∧ l ⊆ Kl ∧ subfield(M, Kc) ∧ K ⊆ Kc ∧ c ⊆ Kc",
						By(
							Normalized,
							M,
							kcDef,
							klDef,
							intermediateGenerators,
							algebraic_element.AdjoinSubfield.At(m, K, l),
							algebraic_element.AdjoinSubfield.At(m, K, c),
							constant_composite.ConstantCompositeDef.At(m, K, l),
							constant_composite.ConstantCompositeDef.At(m, K, c)))
					intermediateTower := a.Have(
						"the intermediate composita lie between the relevant rational bases and fields",
						"Kl ⊆ L ∧ Kc ⊆ N ∧ D ⊆ Kl ∧ E ⊆ Kc",
						BySets(
							M,
							dDef,
							eDef,
							kcDef,
							klDef,
							parameterInIntermediate,
							functionFieldSubfield,
							intermediateInFunctionField,
							originalInComposite,
							compositeField,
							intermediateComposita,
							towerAndParameter,
							algebraic_element.AdjoinLeast.At(m, K, l, L),
							algebraic_element.AdjoinLeast.At(m, K, c, N),
							algebraic_element.AdjoinLeast.At(m, l, a.TermAs[Set[A]]("{t}"), Kl),
							algebraic_element.AdjoinLeast.At(m, c, a.TermAs[Set[A]]("{t}"), Kc),
							constant_composite.ConstantCompositeDef.At(m, K, l),
							constant_composite.ConstantCompositeDef.At(m, K, c)))
					intermediateSubgroups := a.Have(
						"the intermediate automorphism groups lie in the respective full Galois groups",
						"field_automorphisms(M, Kl, L) ⊆ field_automorphisms(M, D, L) ∧ "+
							"field_automorphisms(M, Kc, N) ⊆ field_automorphisms(M, E, N)",
						By(
							M,
							intermediateTower,
							field_automorphism.AutomorphismsAntitone.At(m, D, Kl, L),
							field_automorphism.AutomorphismsAntitone.At(m, E, Kc, N)))
					targetFixesConstants := a.Have(
						"target automorphisms fix the enlarged constants",
						Statement{
							Binders: "∀q:permutation(A).",
							Hypotheses: []string{
								"q ∈ field_automorphisms(M, E, N)",
							},
							Conclusion: "q ∈ field_automorphisms(M, ∅, N) ∧ (∀a:A. a ∈ c ⇒ permutation_map(q, a) = a)",
						},
						BySets(
							M,
							newBase,
							field_automorphism.AutomorphismsAntitone.At(m, a.TermAs[Set[A]]("∅"), E, N),
							field_automorphism.FieldAutomorphismsDef.At(m, E, N)))
					sourceFixesConstants := a.Have(
						"source automorphisms fix the exact constants",
						Statement{
							Binders: "∀s:permutation(A).",
							Hypotheses: []string{
								"s ∈ field_automorphisms(M, D, L)",
							},
							Conclusion: "s ∈ field_automorphisms(M, ∅, L) ∧ (∀a:A. a ∈ l ⇒ permutation_map(s, a) = a)",
						},
						BySets(
							M,
							geometricBase,
							field_automorphism.AutomorphismsAntitone.At(m, a.TermAs[Set[A]]("∅"), D, L),
							field_automorphism.FieldAutomorphismsDef.At(m, D, L)))
					intermediateFixesBase := a.Have(
						"each intermediate automorphism fixes the chosen intermediate field",
						"(∀s:permutation(A). "+
							"    s ∈ field_automorphisms(M, Kl, L) ⇒ ∀x:A. x ∈ K ⇒ permutation_map(s, x) = x) ∧ "+
							"(∀q:permutation(A). q ∈ field_automorphisms(M, Kc, N) ⇒ ∀x:A. x ∈ K ⇒ permutation_map(q, x) = x)",
						BySets(
							intermediateComposita,
							field_automorphism.FieldAutomorphismsDef.At(m, Kl, L),
							field_automorphism.FieldAutomorphismsDef.At(m, Kc, N)))
					rhoFixesKc := a.Have(
						"extending an automorphism fixing the intermediate field fixes its enlarged compositum",
						"∀s:permutation(A). s ∈ field_automorphisms(M, Kl, L) ⇒ ρ(s) ∈ field_automorphisms(M, Kc, N)",
						Derive(func(b *Argument) {
							s := b.FixAs[symmetric_group.Permutation[A]]("s")
							inIntermediateGroup := b.Assume()
							rhoFixesK := b.Have(
								"ρ(s) is an automorphism of N over E fixing K, and K ⊆ N",
								"s ∈ field_automorphisms(M, D, L) ∧ "+
									"ρ(s) ∈ field_automorphisms(M, E, N) ∧ "+
									"(∀x:A. x ∈ K ⇒ permutation_map(ρ(s), x) = x) ∧ "+
									"K ⊆ N",
								BySets(
									rhoExtends.At(s),
									inIntermediateGroup,
									intermediateInFunctionField,
									originalInComposite,
									intermediateFixesBase,
									intermediateSubgroups))
							b.Show(
								"leastness makes the intermediate compositum fixed",
								By(
									M,
									targetFixesConstants.At(b.TermAs[symmetric_group.Permutation[A]]("ρ(s)")),
									kcDef,
									compositeField,
									rhoFixesK,
									At(fixesAdjoinedField, m, N, K, c, b.TermAs[symmetric_group.Permutation[A]]("ρ(s)")),
									constant_composite.ConstantCompositeDef.At(m, K, c)))
						}))
					restrictionFixesComposite := a.Have(
						"restriction of an automorphism fixing the enlarged compositum fixes the exact-constant compositum",
						Statement{
							Binders: "∀s:permutation(A).",
							Hypotheses: []string{
								"s ∈ field_automorphisms(M, D, L)",
								"ρ(s) ∈ field_automorphisms(M, Kc, N)",
							},
							Conclusion: "s ∈ field_automorphisms(M, Kl, L)",
						},
						Derive(func(b *Argument) {
							s := b.FixAs[symmetric_group.Permutation[A]]("s")
							memberships := b.Assume()
							restrictionFixesIntermediate := b.Have(
								"restriction fixes the intermediate field",
								"∀x:A. x ∈ K ⇒ permutation_map(s, x) = x",
								BySets(rhoExtends.At(s), intermediateInFunctionField, intermediateFixesBase, memberships))
							b.Show(
								"leastness makes the exact-constant compositum fixed",
								By(
									M,
									restrictionFixesIntermediate,
									sourceFixesConstants.At(s),
									klDef,
									functionFieldSubfield,
									intermediateInFunctionField,
									memberships,
									towerAndParameter,
									At(fixesAdjoinedField, m, L, K, l, s),
									constant_composite.ConstantCompositeDef.At(m, K, l)))
						}))
					intermediateGroupImage := a.Have(
						"ρ carries Aut(L/Kl) onto Aut(N/Kc)",
						"image(ρ, field_automorphisms(M, Kl, L)) = field_automorphisms(M, Kc, N)",
						BySets(rhoFixesKc, restrictionFixesComposite, rhoOnto, intermediateSubgroups))
					intermediateFixedField := a.Have(
						"Galois correspondence identifies the fixed field of the extended subgroup",
						"fixed_field(N, image(ρ, field_automorphisms(M, Kl, L))) = Kc",
						By(
							Normalized,
							M,
							intermediateGroupImage,
							compositeField,
							intermediateTower,
							intermediateComposita,
							newBase,
							baseChangedGalois,
							galois_correspondence.CorrespondenceFixed.At(m, E, Kc, N)))
					a.Show(
						"N is Galois over E of degree |Aut(L/D)|, and ρ is the isomorphism the theorem names",
						SplitConj(
							Case(
								"Galoisness and degree have the required values",
								By(degreeEqualsSourceGroup, baseChangedGalois)),
							Case(
								"ρ is the isomorphism, extending each automorphism, whose image of Aut(L/Kl) fixes Kc",
								Witness(rho),
								By(Normalized, rhoExtends, kcDef, klDef, intermediateFixedField, rhoIsomorphism)),
						))
				})
		}),
})}
