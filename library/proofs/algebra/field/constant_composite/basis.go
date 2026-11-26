// basis.go — a k-basis of l stays a K-basis of the composite K(l), and
// the coordinates of an element along it.

package constant_composite

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/scalar_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ConstantCompositeSubfield — the composite of two subfields is a subfield
// holding both.
var ConstantCompositeSubfield = constantCompositeSubfieldThm{family.Add(registry.ProofEntry{
	Name: "ConstantCompositeSubfield",
	Key:  "prop_cb1820504058a0f7",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K l:set(A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"subfield(M, l)",
		},
		Conclusion: "subfield(M, constant_composite(M, K, l)) ∧ " +
			"K ⊆ constant_composite(M, K, l) ∧ " +
			"l ⊆ constant_composite(M, K, l)",
	},
		func(a *Argument, M field.FieldFact[on.M], K, l *Expr[Set[A]], KSubfield, lSubfield Fact) {
			m := a.TermAs[FieldOps[A]]("M")
			a.Show(
				"the composite is the field the two generate",
				Unfold(ConstantCompositeDef),
				By(
					M,
					KSubfield,
					lSubfield,
					field.SubfieldSubset.At(m, K),
					field.SubfieldSubset.At(m, l),
					algebraic_element.AdjoinSubfield.At(m, K, l)))
		}),
})}

// ConstantCompositeBasis — a k-basis E of l stays a K-basis of the composite
// K(l). Independence: multiplication identifies l ⊗_k K with the composite,
// so a K-relation among E is a vanishing tensor and the basis separates its
// terms. Spanning: multiplication is onto, a tensor is a sum of pure tensors
// a ⊗ x, and a·x is x times a k-combination of E.
var ConstantCompositeBasis = constantCompositeBasisThm{family.Add(registry.ProofEntry{
	Name: "ConstantCompositeBasis",
	Key:  "prop_905d48926b70bce3",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λS:set(A). restrict_ring(field_ring(M), S)"},
			{Name: "vectors", Text: "λS:set(A). restrict_module(regular_module(field_ring(M)), S)"},
			{Name: "extension", Text: "scalar_extension(«scalars»(k), «scalars»(l), «vectors»(K))"},
			{Name: "tensors", Text: "tensor_module(«scalars»(k), «vectors»(l), «vectors»(K))"},
			{Name: "tensorProduct", Text: "tensor_product(«scalars»(k), «vectors»(l), «vectors»(K))"},
			{Name: "pure", Text: "λa:A. λx:A. tensor(«scalars»(k), «vectors»(l), «vectors»(K), a, x)"},
			{Name: "pureSum", Text: "λT:set(A). λc:(A → A). " +
				"    module_sum(«extension».add, «extension».zero, T, λe:A. «pure»(e, c(e)))"},
		},
		Binders: "∀M:field_on(A). ∀K k l E:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
		},
		Conclusion: "module_basis(«scalars»(K), «vectors»(constant_composite(M, K, l)), E)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E *Expr[Set[A]],
			regular, lSubfield, kInL, finiteBasis, basis Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			kRing := a.TermAs[module_record.RingOps[A]]("«scalars»(k)")
			lRing := a.TermAs[module_record.RingOps[A]]("«scalars»(l)")
			KRing := a.TermAs[module_record.RingOps[A]]("«scalars»(K)")
			lVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			KVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(K)")
			extension := a.TermAs[module_record.ModuleOps[A, _Tensor]]("«extension»")
			regularData := a.Conjuncts(
				a.Unfolded(regular, function_field.RegularFunctionFieldDef),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"k is perfect",
				"K is finitely generated over k",
				"K has a parameter over k",
				"k is algebraically closed in K")
			kSubfield, KSubfield, kInK := regularData[0], regularData[1], regularData[2]
			finiteConstants := a.Have(
				"E makes l a finite extension of k",
				"finite_extension(M, k, l)",
				By(M, kSubfield, lSubfield, kInL, finiteBasis, basis, field_extension.BasisDegree.At(m, k, l, E)))
			extended := a.Conjuncts(
				GroupPremises(
					M, regular, lSubfield, kInL, finiteConstants, RegularConstantExtension.At(m, k, K, l)),
				"the composite is a regular function field over l",
				"multiplication identifies l ⊗_k K with the composite")[1]
			f, multiplication := a.UnpackAs[Fun[_Tensor, A]](extended, "f")
			composite, compositeDef := a.LetAs[Set[A]]("C", "constant_composite(M, K, l)")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(C)")
			multiplicationParts := a.Conjuncts(
				multiplication,
				"f is an isomorphism",
				"f multiplies",
				"separability and degree over a parameter are kept")
			isomorphism, fProduct := multiplicationParts[0], multiplicationParts[1]
			compositeData := a.Conjuncts(
				a.Have(
					"C is a subfield holding K and l",
					"subfield(M, C) ∧ K ⊆ C ∧ l ⊆ C",
					compositeDef.Rw(),
					By(M, KSubfield, lSubfield, ConstantCompositeSubfield.At(m, K, l))),
				"C is a subfield",
				"C holds K",
				"C holds l")
			compositeSubfield, KInC, lInC := compositeData[0], compositeData[1], compositeData[2]
			modules := a.Conjuncts(
				a.Have(
					"C is a module over K, and l and K over k",
					"module_on(«scalars»(K), «vectors»(C)) ∧ "+
						"module_on(«scalars»(k), «vectors»(l)) ∧ "+
						"module_on(«scalars»(k), «vectors»(K))",
					By(
						M,
						KSubfield,
						lSubfield,
						kSubfield,
						compositeSubfield,
						KInC,
						kInK,
						kInL,
						field_extension.ExtensionModuleOn.At(m, K, composite),
						field_extension.ExtensionModuleOn.At(m, k, l),
						field_extension.ExtensionModuleOn.At(m, k, K))),
				"C over K",
				"l over k",
				"K over k")
			compositeModule, lModule, KModule := modules[0], modules[1], modules[2]
			extensionOperations := a.Conjuncts(
				a.Have(
					"the scalar extension is the tensor module of l and K over k",
					"«extension».add = «tensors».add ∧ "+
						"«extension».zero = «tensors».zero ∧ "+
						"«extension».carrier = «tensors».carrier",
					Simp(
						Fwd(module_record.RegularModuleDef),
						Fwd(module_record.RestrictRingDef),
						Fwd(field.FieldRingDef),
						Fwd(scalar_extension.ScalarExtensionDef),
						Fwd(module_record.RestrictModuleDef)),
					Basic()),
				"one addition",
				"one zero",
				"one carrier")
			sameAdd, sameZero, sameCarrier :=
				extensionOperations[0], extensionOperations[1], extensionOperations[2]
			cosetOperations := a.Conjuncts(
				a.Have(
					"its addition and zero are those of the cosets of the relations",
					"«extension».add = set_mul(fun_add) ∧ "+
						"«extension».zero = tensor_relations(«scalars»(k), «vectors»(l), «vectors»(K))",
					Simp(
						Fwd(module_record.RegularModuleDef),
						Fwd(module_record.RestrictRingDef),
						Fwd(field.FieldRingDef),
						Fwd(scalar_extension.ScalarExtensionDef),
						Fwd(module_record.RestrictModuleDef),
						Fwd(tensor_product.TensorModuleDef),
						Fwd(submodule.QuotientModuleDef),
						Fwd(free_module.FreeModuleRecordDef)),
					Basic()),
				"the addition of cosets",
				"the zero coset")
			tensorCarrier := a.Have(
				"the tensor module has the tensor product as its carrier",
				"«tensors».carrier = «tensorProduct»",
				By(tensor_product.TensorModuleCarrier))
			extensionCarrier := a.Have(
				"its carrier is the tensor product",
				"«extension».carrier = «tensorProduct»",
				By(sameCarrier, tensorCarrier))
			isoData := a.Conjuncts(
				a.Have(
					"f is linear, injective and onto C",
					"module_homomorphism(«scalars»(l), «extension», «vectors»(C), f) ∧ "+
						"injective_on(«extension».carrier, f) ∧ "+
						"image(f, «extension».carrier) = C",
					By(
						isomorphism,
						module_homomorphism.ModuleIsomorphismDef.At(lRing, extension, compositeVectors, f))),
				"f is linear",
				"f is injective",
				"f is onto")
			fLinear, fInjective, fOnto := isoData[0], isoData[1], isoData[2]
			pureIn := a.Have(
				"a pure tensor of l and K lies in the scalar extension",
				"∀a x:A. a ∈ l ∧ x ∈ K ⇒ «pure»(a, x) ∈ «extension».carrier",
				Derive(func(b *Argument) {
					scalar := b.FixAs[A]("a")
					x := b.FixAs[A]("x")
					members := b.Assume()
					b.Show(
						"a pure tensor of two vectors",
						By(
							extensionCarrier,
							members,
							lModule,
							KModule,
							tensor_product.TensorIn.At(kRing, lVectors, KVectors, scalar, x)))
				}))
			generators := a.Conjuncts(
				a.Have(
					"E lies in l, hence in C",
					"E ⊆ l ∧ E ⊆ C",
					BySets(lInC, basis, linear_independence.BasisInCarrier.At(kRing, lVectors, E))),
				"E lies in l",
				"E lies in C")
			EInL, EInC := generators[0], generators[1]
			relations := a.Have(
				"a K-relation among the elements of E vanishes",
				Statement{
					Binders: "∀T:set(A). ∀c:(A → A).",
					Hypotheses: []string{
						"T ⊆ E",
						"∀x:A. x ∈ T ⇒ c(x) ∈ K",
						"module_sum(M.add, M.zero, T, λx:A. c(x) * x) = M.zero",
					},
					Conclusion: "∀x:A. x ∈ T ⇒ c(x) = M.zero",
				},
				Derive(func(b *Argument) {
					T := b.FixAs[Set[A]]("T")
					c := b.FixAs[Fun[A, A]]("c")
					relation := b.Conjuncts(
						b.Assume(),
						"T lies in E",
						"the coefficients lie in K",
						"the relation")
					inBasis, coefficients, vanishing := relation[0], relation[1], relation[2]
					x := b.FixAs[A]("x")
					xInT := b.Assume()
					finiteT := b.Have(
						"T is finite",
						"finite(T)",
						By(finiteBasis, inBasis, finite_set.FiniteSubset))
					memberships := b.Have(
						"each element of T lies in l and in M, and its coefficient in K and in M",
						"∀e:A. e ∈ T ⇒ e ∈ l ∧ c(e) ∈ K ∧ e ∈ M.carrier ∧ c(e) ∈ M.carrier",
						BySets(
							inBasis,
							EInL,
							coefficients,
							lSubfield,
							KSubfield,
							field.SubfieldSubset.At(m, l),
							field.SubfieldSubset.At(m, K)))
					pures := b.Have(
						"each e ⊗ c(e) lies in the scalar extension",
						"∀e:A. e ∈ T ⇒ «pure»(e, c(e)) ∈ «extension».carrier",
						Derive(func(d *Argument) {
							e := d.FixAs[A]("e")
							inT := d.Assume()
							d.Show(
								"e lies in l and c(e) in K",
								By(pureIn.At(e, d.TermAs[A]("c(e)")), memberships.At(e), inT))
						}))
					summand := b.TermAs[Fun[A, _Tensor]]("λe:A. «pure»(e, c(e))")
					imageSum := b.TermAs[Fun[A, A]]("λe:A. f(«pure»(e, c(e)))")
					summed := b.Have(
						"f carries the sum of tensors to the sum of its values",
						"f(«pureSum»(T, c)) = module_sum(M.add, M.zero, T, λe:A. f(«pure»(e, c(e))))",
						By(
							finiteT,
							fLinear,
							pures,
							module_homomorphism.HomSum.At(lRing, extension, compositeVectors, f, T, summand)))
					products := b.Have(
						"f sends e ⊗ c(e) to c(e) * e",
						"∀e:A. e ∈ T ⇒ f(«pure»(e, c(e))) = c(e) * e",
						Derive(func(d *Argument) {
							e := d.FixAs[A]("e")
							inT := d.Assume()
							swap := d.Have(
								"the product commutes",
								"e * c(e) = c(e) * e",
								ByArith(M, memberships.At(e), inT))
							d.Show(
								"f multiplies",
								By(swap, inT, fProduct.At(e, d.TermAs[A]("c(e)")), memberships.At(e)))
						}))
					vanishes := b.Have(
						"the values sum to the relation, which vanishes",
						"module_sum(M.add, M.zero, T, λe:A. f(«pure»(e, c(e)))) = M.zero",
						By(
							vanishing,
							products,
							module.ModuleSumCongruence.At(
								b.TermAs[Op[A]]("M.add"),
								b.TermAs[A]("M.zero"),
								T,
								imageSum,
								b.TermAs[Fun[A, A]]("λx:A. c(x) * x"))))
					source := module_homomorphism.HomSource.Read(fLinear)
					inExtension := b.Have(
						"the sum of tensors and the zero both lie in the scalar extension",
						"«pureSum»(T, c) ∈ «extension».carrier ∧ «extension».zero ∈ «extension».carrier",
						By(
							finiteT,
							pures,
							source,
							group.OneIn.Read(module.AddGroupOn.Read(source)),
							module.ModuleSumIn.At(lRing, extension, T, summand)))
					fZero := b.Have(
						"f keeps zero",
						"f(«extension».zero) = M.zero",
						By(fLinear, module_homomorphism.HomZero.Read(fLinear)))
					sameImage := b.Have(
						"the sum of tensors has the image of zero",
						"f(«pureSum»(T, c)) = f(«extension».zero)",
						By(summed, vanishes, fZero))
					zeroSum := b.Have(
						"so the sum of tensors is zero, f being injective",
						"«pureSum»(T, c) = «extension».zero",
						By(
							sameImage,
							inExtension,
							fInjective,
							functions.InjectiveOnDef.At(b.TermAs[Set[_Tensor]]("«extension».carrier"), f)))
					inTensors := b.Have(
						"the same sum vanishes in the tensor module",
						"module_sum(«tensors».add, «tensors».zero, T, λe:A. «pure»(e, c(e))) = «tensors».zero",
						sameAdd.RwRev(),
						sameZero.RwRev(),
						By(zeroSum))
					b.Show(
						"a k-basis of l separates the terms",
						By(
							xInT,
							lModule,
							KModule,
							finiteBasis,
							basis,
							inBasis,
							coefficients,
							inTensors,
							tensor_product.TensorBasisSeparates.At(kRing, lVectors, KVectors, E, T, c, x)))
				}))
			independent := a.Have(
				"E is independent over K",
				"module_independent(«scalars»(K), «vectors»(C), E)",
				Unfold(linear_independence.ModuleIndependentDef),
				By(EInC, relations))
			Q, QDef := a.LetAs[Set[A]]("Q", "module_span(«scalars»(K), «vectors»(C), E)")
			spanData := a.Conjuncts(
				a.Have(
					"Q is a K-submodule of C holding E",
					"submodule(«scalars»(K), «vectors»(C), Q) ∧ E ⊆ Q ∧ Q ⊆ C",
					By(
						Normalized,
						QDef,
						EInC,
						compositeModule,
						submodule.SpanSubmodule.At(KRing, compositeVectors, E),
						submodule.SubsetSpan.At(KRing, compositeVectors, E),
						submodule.CarrierSubmodule.At(KRing, compositeVectors),
						submodule.SpanLeast.At(KRing, compositeVectors, E, composite))),
				"Q is a submodule",
				"Q holds E",
				"Q lies in C")
			QSubmodule, QInC := spanData[0], spanData[2]
			kInC := a.Have(
				"C holds k",
				"k ⊆ C",
				BySets(kInL, lInC))
			kSpan := a.Have(
				"over k, E spans l inside C",
				"module_span(«scalars»(k), «vectors»(C), E) = l",
				By(
					M,
					kSubfield,
					lSubfield,
					compositeSubfield,
					kInL,
					lInC,
					kInC,
					basis,
					field_extension.ExtensionModuleOn.At(m, k, composite),
					field_extension.SubfieldSubmodule.At(m, k, l, composite),
					module_record.RestrictModuleTwice.At(
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))"), composite, l),
					linear_independence.BasisRestrict.At(kRing, compositeVectors, l, E)))
			lInQ := a.Have(
				"Q holds l",
				"l ⊆ Q",
				By(
					Normalized,
					QDef,
					kSpan,
					compositeModule,
					kInK,
					EInC,
					submodule.SpanOfSubringSpan.At(KRing, compositeVectors, kRing, E),
					submodule.SubsetSpan.At(KRing, compositeVectors, l)))
			products := a.Have(
				"Q holds the product of l and K",
				"∀a x:A. a ∈ l ∧ x ∈ K ⇒ a * x ∈ Q",
				Derive(func(b *Argument) {
					scalar := b.FixAs[A]("a")
					x := b.FixAs[A]("x")
					members := b.Assume()
					ambient := b.Have(
						"both factors lie in M",
						"a ∈ M.carrier ∧ x ∈ M.carrier",
						BySets(members, lSubfield, KSubfield, field.SubfieldSubset.At(m, l), field.SubfieldSubset.At(m, K)))
					swap := b.Have(
						"the product commutes",
						"a * x = x * a",
						ByArith(M, ambient))
					inQ := b.Have(
						"a lies in Q",
						"a ∈ Q",
						BySets(members, lInQ))
					b.Show(
						"Q is closed under scalars from K",
						swap.Rw(),
						By(members, inQ, QSubmodule, submodule.SubmoduleSmul.At(KRing, compositeVectors, Q, x, scalar)))
				}))
			tensorsInQ := a.Have(
				"f maps every tensor into Q",
				"∀z:set(prod(A, A) → A). z ∈ «tensorProduct» ⇒ f(z) ∈ Q",
				Derive(func(b *Argument) {
					z := b.FixAs[_Tensor]("z")
					zInTensor := b.Assume()
					s, _, expansion := b.Unpack2As[Set[Prod[A, A]], Fun[Prod[A, A], A]](
						GroupPremises(
							modules[1], modules[2], zInTensor, tensor_product.TensorPureSum.At(kRing, lVectors, KVectors, z)),
						"s",
						"g")
					parts := b.Conjuncts(
						expansion,
						"the index set is finite",
						"the indices are pairs",
						"the first factors lie in l",
						"z is the sum")
					finiteIndices, pairs, firsts, zExpansion := parts[0], parts[1], parts[2], parts[3]
					summand := b.TermAs[Fun[Prod[A, A], _Tensor]]("λq:prod(A, A). «pure»(g(q), snd(q))")
					imageSum := b.TermAs[Fun[Prod[A, A], A]]("λq:prod(A, A). f(«pure»(g(q), snd(q)))")
					factors := b.Have(
						"each term is a pure tensor of l and K",
						"∀q:prod(A, A). q ∈ s ⇒ g(q) ∈ l ∧ snd(q) ∈ K",
						Derive(func(c *Argument) {
							q := c.FixAs[Prod[A, A]]("q")
							inIndices := c.Assume()
							c.Show(
								"the second component of a pair of l and K",
								BySets(inIndices, pairs, firsts.At(q), set_product.InCrossProjections.At(l, K, q)))
						}))
					terms := b.Have(
						"the terms lie in the scalar extension and map into Q",
						"∀q:prod(A, A). q ∈ s ⇒ «pure»(g(q), snd(q)) ∈ «extension».carrier ∧ f(«pure»(g(q), snd(q))) ∈ Q",
						Derive(func(c *Argument) {
							q := c.FixAs[Prod[A, A]]("q")
							inIndices := c.Assume()
							first := c.TermAs[A]("g(q)")
							second := c.TermAs[A]("snd(q)")
							c.Show(
								"f multiplies the two factors",
								By(
									inIndices,
									factors.At(q),
									pureIn.At(first, second),
									fProduct.At(first, second),
									products.At(first, second)))
						}))
					summed := b.Have(
						"f carries the sum of tensors to the sum of its values",
						"f(module_sum(«extension».add, «extension».zero, s, λq:prod(A, A). «pure»(g(q), snd(q)))) = "+
							"module_sum(M.add, M.zero, s, λq:prod(A, A). f(«pure»(g(q), snd(q))))",
						By(
							finiteIndices,
							fLinear,
							terms,
							module_homomorphism.HomSum.At(lRing, extension, compositeVectors, f, s, summand)))
					b.Do(zExpansion.Rw(), cosetOperations[0].RwRev(), cosetOperations[1].RwRev(), summed.Rw())
					b.Show(
						"Q is closed under finite sums",
						By(
							finiteIndices,
							terms,
							QSubmodule,
							compositeModule,
							submodule.SubmoduleModuleSum.At(KRing, compositeVectors, Q, s, imageSum)))
				}))
			ontoTensors := a.Have(
				"f maps the tensor product onto C",
				"image(f, «tensorProduct») = C",
				By(extensionCarrier, fOnto))
			imageInQ := a.Have(
				"the image of the tensor product lies in Q",
				"image(f, «tensorProduct») ⊆ Q",
				By(tensorsInQ, set_image.ImageSubsetIff.At(f, a.TermAs[Set[_Tensor]]("«tensorProduct»"), Q)))
			CInQ := a.Have(
				"so C lies in Q",
				"C ⊆ Q",
				By(Normalized, ontoTensors, imageInQ))
			spans := a.Have(
				"E spans C over K",
				"module_span(«scalars»(K), «vectors»(C), E) = C",
				By(Normalized, QDef, QInC, CInQ, set_order.SubsetAntisym.At(Q, composite)))
			a.Show(
				"E is independent and spans",
				Unfold(linear_independence.ModuleBasisDef),
				By(independent, spans))
		}),
})}

// ConstantExtensionData — what a k-basis E of l gives the composite K' of K
// and l: K' is a subfield over K and over l, the basis lies in l, and K' is a
// module over K with basis E.
var ConstantExtensionData = constantExtensionDataThm{family.Add(registry.ProofEntry{
	Name: "ConstantExtensionData",
	Key:  "prop_8aa14951134ad6fa",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λS:set(A). restrict_ring(field_ring(M), S)"},
			{Name: "vectors", Text: "λS:set(A). restrict_module(regular_module(field_ring(M)), S)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E:set(A).",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
		},
		Conclusion: "subfield(M, k) ∧ " +
			"subfield(M, K) ∧ " +
			"k ⊆ K ∧ " +
			"subfield(M, constant_composite(M, K, l)) ∧ " +
			"K ⊆ constant_composite(M, K, l) ∧ " +
			"l ⊆ constant_composite(M, K, l) ∧ " +
			"E ⊆ l ∧ " +
			"module_on(«scalars»(K), «vectors»(constant_composite(M, K, l))) ∧ " +
			"module_basis(«scalars»(K), «vectors»(constant_composite(M, K, l)), E)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E *Expr[Set[A]],
			regular, lSubfield, kInL, finiteBasis, basis Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			regularData := a.Conjuncts(
				a.Unfolded(regular, function_field.RegularFunctionFieldDef),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"k is perfect",
				"K is finitely generated over k",
				"K has a parameter over k",
				"k is algebraically closed in K")
			kSubfield, KSubfield, kInK := regularData[0], regularData[1], regularData[2]
			a.Show(
				"the composite is a subfield, and the basis of l stays a basis over K",
				By(
					M,
					kSubfield,
					KSubfield,
					kInK,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					regular,
					ConstantCompositeSubfield.At(m, K, l),
					ConstantCompositeBasis.At(m, K, k, l, E),
					linear_independence.BasisInCarrier.At(
						a.TermAs[module_record.RingOps[A]]("«scalars»(k)"),
						a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)"),
						E),
					field_extension.ExtensionModuleOn.At(m, K, a.TermAs[Set[A]]("constant_composite(M, K, l)"))))
		}),
})}

// ConstantCoordinateProduct — the coordinates of a member of the composite lie
// in K, and a factor from K comes out of them: the coordinate at e is K-linear.
var ConstantCoordinateProduct = constantCoordinateProductThm{family.Add(registry.ProofEntry{
	Name: "ConstantCoordinateProduct",
	Key:  "prop_b343f9a086ed047a",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λX:set(A). restrict_ring(field_ring(M), X)"},
			{Name: "vectors", Text: "λX:set(A). restrict_module(regular_module(field_ring(M)), X)"},
			{Name: "coordinate", Text: "λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(constant_composite(M, K, l)), E, x, e)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E:set(A). ∀x y e:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
			"x ∈ constant_composite(M, K, l)",
			"y ∈ K",
			"e ∈ E",
		},
		Conclusion: "«coordinate»(x, e) ∈ K ∧ «coordinate»(x * y, e) = «coordinate»(x, e) * y",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, l, E *Expr[Set[A]],
			x, y, e *Expr[A],
			regular, lSubfield, kInL, finiteBasis, basis, xInC, yInK, eInE Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			KScalars := a.TermAs[module_record.RingOps[A]]("«scalars»(K)")
			compositeVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"«vectors»(constant_composite(M, K, l))")
			composite := a.TermAs[Set[A]]("constant_composite(M, K, l)")
			data := a.Conjuncts(
				GroupPremises(
					M, regular, lSubfield, kInL, finiteBasis, basis, ConstantExtensionData.At(ops, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			KSubfield, compositeSubfield, compositeModule, compositeBasis := data[1], data[3], data[7], data[8]
			linear := a.Have(
				"the coordinate at e is K-linear",
				"module_homomorphism(«scalars»(K), "+
					"    «vectors»(constant_composite(M, K, l)), "+
					"    regular_module(«scalars»(K)), "+
					"    λv:A. «coordinate»(v, e))",
				By(
					compositeModule,
					finiteBasis,
					compositeBasis,
					eInE,
					module_dimension.BasisCoordinateLinear.At(KScalars, compositeVectors, E, e)))
			coordinateInK := a.Have(
				"the coordinate lies in K",
				"«coordinate»(x, e) ∈ K",
				By(
					compositeModule,
					finiteBasis,
					compositeBasis,
					xInC,
					eInE,
					module_dimension.BasisCoordinatesSpec.At(KScalars, compositeVectors, E, x)))
			members := a.Have(
				"x, y and the coordinate lie in the field",
				"x ∈ M.carrier ∧ y ∈ M.carrier ∧ «coordinate»(x, e) ∈ M.carrier",
				BySets(
					xInC,
					yInK,
					coordinateInK,
					KSubfield,
					compositeSubfield,
					field.SubfieldSubset.At(ops, K),
					field.SubfieldSubset.At(ops, composite)))
			swap := a.Have(
				"the product commutes",
				"x * y = y * x",
				ByArith(M, members))
			turned := a.Have(
				"and so does the product with the coordinate",
				"y * «coordinate»(x, e) = «coordinate»(x, e) * y",
				ByArith(M, members))
			a.Show(
				"K-linearity moves y out of the coordinate",
				swap.Rw(),
				By(coordinateInK, members, yInK, xInC, turned, At(module_homomorphism.HomSmul.Read(linear), y, x)))
		}),
})}

// ConstantCoordinateScale — the coordinates of an element of l over K are
// its coordinates over k, so they lie in k; and multiplying by y in K
// multiplies each coordinate by y, as for any member of the composite.
var ConstantCoordinateScale = constantCoordinateScaleThm{family.Add(registry.ProofEntry{
	Name: "ConstantCoordinateScale",
	Key:  "prop_8a2f3829851f3e8d",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "λS:set(A). restrict_ring(field_ring(M), S)"},
			{Name: "vectors", Text: "λS:set(A). restrict_module(regular_module(field_ring(M)), S)"},
			{Name: "coordinate", Text: "λx:A. λe:A. " +
				"    module_basis_coordinates(«scalars»(K), «vectors»(constant_composite(M, K, l)), E, x, e)"},
		},
		Binders: "∀M:field_on(A). ∀K k l E:set(A). ∀a y e:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, K)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite(E)",
			"module_basis(«scalars»(k), «vectors»(l), E)",
			"a ∈ l",
			"y ∈ K",
			"e ∈ E",
		},
		Conclusion: "«coordinate»(a, e) ∈ k ∧ «coordinate»(a * y, e) = «coordinate»(a, e) * y",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, l, E *Expr[Set[A]],
			a, y, e *Expr[A],
			regular, lSubfield, kInL, finiteBasis, basis, aInL, yInK, eInE Fact,
		) {
			m := arg.TermAs[FieldOps[A]]("M")
			kScalars := arg.TermAs[module_record.RingOps[A]]("«scalars»(k)")
			KScalars := arg.TermAs[module_record.RingOps[A]]("«scalars»(K)")
			lVectors := arg.TermAs[module_record.ModuleOps[A, A]]("«vectors»(l)")
			compositeVectors := arg.TermAs[module_record.ModuleOps[A, A]](
				"«vectors»(constant_composite(M, K, l))")
			composite := arg.TermAs[Set[A]]("constant_composite(M, K, l)")
			data := arg.Conjuncts(
				GroupPremises(
					M, regular, lSubfield, kInL, finiteBasis, basis, ConstantExtensionData.At(m, K, k, l, E)),
				"k is a subfield",
				"K is a subfield",
				"k lies in K",
				"K' is a subfield",
				"K' holds K",
				"K' holds l",
				"E lies in l",
				"K' is a K-module",
				"E is a K-basis of K'")
			kSubfield, kInK, lInC, compositeModule, compositeBasis :=
				data[0], data[2], data[5], data[7], data[8]
			sameCoordinates := arg.Have(
				"over K and over k, a has one set of coordinates",
				"module_basis_coordinates(«scalars»(K), «vectors»(constant_composite(M, K, l)), E, a) = "+
					"module_basis_coordinates(«scalars»(k), «vectors»(l), E, a)",
				By(
					M,
					kSubfield,
					lSubfield,
					kInL,
					kInK,
					lInC,
					finiteBasis,
					aInL,
					compositeModule,
					compositeBasis,
					basis,
					module_record.RestrictRingTwice.At(arg.TermAs[module_record.RingOps[A]]("field_ring(M)"), K, k),
					module_record.RestrictModuleTwice.At(
						arg.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))"), composite, l),
					field_extension.ExtensionModuleOn.At(m, k, l),
					module_dimension.BasisCoordinatesRestrict.At(KScalars, compositeVectors, k, l, E, a)))
			coordinateInK := arg.Have(
				"so the coordinate lies in k",
				"«coordinate»(a, e) ∈ k",
				sameCoordinates.Rw(),
				By(
					M,
					kSubfield,
					lSubfield,
					kInL,
					finiteBasis,
					aInL,
					eInE,
					basis,
					field_extension.ExtensionModuleOn.At(m, k, l),
					module_dimension.BasisCoordinatesSpec.At(kScalars, lVectors, E, a)))
			aInC := arg.Have(
				"a lies in the composite",
				"a ∈ constant_composite(M, K, l)",
				BySets(aInL, lInC))
			arg.Show(
				"a factor from K comes out of a coordinate",
				By(
					coordinateInK,
					regular,
					lSubfield,
					kInL,
					finiteBasis,
					basis,
					aInC,
					yInK,
					eInE,
					ConstantCoordinateProduct.Read(M).At(K, k, l, E, a, y, e)))
		}),
})}
