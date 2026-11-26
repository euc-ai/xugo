// basis.go — a basis survives scalar extension. The canonical unit v ↦ 1 ⊗ v
// takes an S-spanning set to an R-spanning set and, where one is not zero, a
// basis injectively to a basis, so over a subfield extension keeps dimension.

package scalar_extension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ScalarExtensionSpanning — the unit image of an S-spanning set spans scalar
// extension over R: the R-span is an S-submodule, so it holds the unit image
// of V, its R-multiples the pure tensors, and their combinations every
// tensor.
var ScalarExtensionSpanning = scalarExtensionSpanningThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionSpanning",
	Key:  "prop_91aef4236f1e335f",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B). ∀E:set(B).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_on(restrict_ring(R, S), V)",
			"E ⊆ V.carrier",
			"module_span(restrict_ring(R, S), V, E) = V.carrier",
		},
		Conclusion: "«span» = «extension».carrier",
		Abbrev: Abbrev{
			{Name: "generators", Text: "image(«unitS», E)"},
			{Name: "span", Text: "module_span(R, «extension», «generators»)"},
		},
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		E *Expr[Set[B]],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"V is an S-module",
			"E lies in V",
			"E spans V over S")
		subring, vectors, inV, spansV := given[0], given[1], given[2], given[3]
		products := comm_ring.MulMonoidOn.Read(R)
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		ringOps := p.TermAs[RingOps[A]]("R")
		ringCarrier := p.TermAs[Set[A]]("R.carrier")
		regularR := p.TermAs[ModuleOps[A, A]]("regular_module(R)")
		extension := p.TermAs[ModuleOps[A, _TensorV]]("«extension»")
		unit := p.TermAs[Fun[B, _TensorV]]("«unitS»")
		generators := p.TermAs[Set[_TensorV]]("«generators»")
		span := p.TermAs[Set[_TensorV]]("«span»")
		carrier := p.TermAs[Set[_TensorV]]("«extension».carrier")
		regularOverS := p.Have(
			"R is an S-module under multiplication",
			"module_on(restrict_ring(R, S), regular_module(R))",
			By(subring, module.RegularModuleOverSubring.Read(R).At(S)))
		extended := p.Have(
			"scalar extension is an R-module",
			"module_on(R, «extension»)",
			By(subring, vectors, ScalarExtensionOn.Read(R).At(S, V)))
		unitLinear := p.Have(
			"the canonical unit is S-linear",
			"module_homomorphism(restrict_ring(R, S), V, «extension», «unitS»)",
			By(subring, vectors, ScalarExtensionUnitLinear.Read(R).At(S, V)))
		generatorsCarrier := p.Have(
			"the unit images lie in scalar extension",
			"«generators» ⊆ «extension».carrier",
			By(
				module_homomorphism.HomIn.Read(unitLinear),
				inV,
				set_basic.SubsetDef.At(E, p.TermAs[Set[B]]("V.carrier")),
				set_image.ImageSubsetIff.At(unit, E, carrier)))
		spanOverR := p.Have(
			"the R-span is an R-submodule",
			"submodule(R, «extension», «span»)",
			By(extended, generatorsCarrier, submodule.SpanSubmodule.At(ringOps, extension, generators)))
		spanOverS := p.Have(
			"the R-span is also an S-submodule",
			"submodule(restrict_ring(R, S), «extension», «span»)",
			By(
				comm_ring.SubringSubset.Read(subring),
				spanOverR,
				submodule.SubmoduleRestrictScalars.At(ringOps, extension, span, subringS)))
		unitsInSpan := p.Have(
			"all unit images lie in the R-span of the images of E",
			"image(«unitS», V.carrier) ⊆ «span»",
			By(
				inV,
				spansV,
				spanOverS,
				unitLinear,
				submodule.SubsetSpan.At(ringOps, extension, generators),
				submodule.SpanLeast.At(subringS, extension, generators, span),
				linear_independence.HomSpan.At(subringS, V, extension, unit, E)))
		pureInSpan := p.Have(
			"every pure tensor lies in the R-span",
			"∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ «pureS»(a, v) ∈ «span»",
			Derive(func(q *Argument) {
				a, v := q.FixAs[A]("a"), q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"scaling the unit image by a gives the pure tensor",
					By(
						comm_ring.OneIn.Read(R),
						unitsInSpan,
						vectors,
						subring,
						members,
						set_image.FunInImage.At(unit, q.TermAs[Set[B]]("V.carrier"), v),
						set_basic.SubsetDef.At(q.TermAs[Set[_TensorV]]("image(«unitS», V.carrier)"), span),
						submodule.SubmoduleSmul.Read(spanOverR).AsFact().At(a, q.TermAs[_TensorV]("«unitS»(v)")),
						TensorScalarActionSpec.Read(R).AsFact().At(S, V, a),
						comm_monoid.RightIdentityOn.Read(products).AsFact().At(a)))
			}))
		allInSpan := p.Have(
			"every tensor lies in the R-span",
			"∀t:set(prod(A, B) → A). t ∈ «extension».carrier ⇒ t ∈ «span»",
			Derive(func(b *Argument) {
				t := b.FixAs[_TensorV]("t")
				member := b.Simplified(
					b.Assume(),
					Fwd(ScalarExtensionCarrier),
					Fwd(tensor_product.TensorModuleCarrier))
				s, _, expansion := b.Obtain2As[Set[Prod[A, B]], Fun[Prod[A, B], A]](
					"write the tensor as a finite S-combination of pure tensors",
					"∃s:set(prod(A, B)). ∃coeff:(prod(A, B) → A). "+
						"    finite(s) ∧ "+
						"    s ⊆ set_cross(R.carrier, V.carrier) ∧ "+
						"    (∀q:prod(A, B). q ∈ s ⇒ coeff(q) ∈ S) ∧ "+
						"    t = "+
						"    module_sum(«tensorS».add, "+
						"        «tensorS».zero, "+
						"        s, "+
						"        λq:prod(A, B). «tensorS».smul(coeff(q), «pureS»(fst(q), snd(q))))",
					Named("s", "coeff"),
					By(regularOverS, vectors, member, tensor_product.TensorSpan.At(subringS, regularR, V, t)))
				data := b.Conjuncts(
					expansion,
					"the support is finite",
					"support pairs lie in the factor carriers",
					"coefficients lie in S",
					"the finite combination equals t")
				summandsInSpan := b.Have(
					"each scaled pure tensor lies in the span",
					"∀q:prod(A, B). q ∈ s ⇒ «tensorS».smul(coeff(q), «pureS»(fst(q), snd(q))) ∈ «span»",
					Derive(func(r *Argument) {
						pair := r.FixAs[Prod[A, B]]("q")
						pairIn := r.Assume()
						points := r.Have(
							"the two coordinates lie in their carriers",
							"fst(q) ∈ R.carrier ∧ snd(q) ∈ V.carrier",
							By(
								pairIn,
								data[1],
								set_basic.SubsetDef.At(s, r.TermAs[Set[Prod[A, B]]]("set_cross(R.carrier, V.carrier)")),
								set_product.InCrossProjections.At(ringCarrier, r.TermAs[Set[B]]("V.carrier"), pair)))
						pureMember := r.Have(
							"the pure tensor lies in the tensor carrier",
							"«pureS»(fst(q), snd(q)) ∈ «tensorS».carrier",
							Simp(Fwd(tensor_product.TensorModuleCarrier)),
							By(
								regularOverS,
								vectors,
								points,
								tensor_product.TensorIn.At(subringS, regularR, V, r.TermAs[A]("fst(q)"), r.TermAs[B]("snd(q)"))))
						pure := r.TermAs[_TensorV]("«pureS»(fst(q), snd(q))")
						r.Show(
							"restriction of the ring action agrees with tensor scaling",
							Simp(Fwd(tensor_product.TensorModuleSmul)),
							By(
								pureInSpan.At(r.TermAs[A]("fst(q)"), r.TermAs[B]("snd(q)")),
								data[2].At(pair),
								vectors,
								pureMember,
								pairIn,
								subring,
								points,
								submodule.SubmoduleSmul.Read(spanOverS).AsFact().At(r.TermAs[A]("coeff(q)"), pure),
								TensorScalarActionRestrict.Read(R).At(S, V, r.TermAs[A]("coeff(q)"), pure)))
					}))
				b.Show(
					"the span is closed under the finite combination",
					By(
						data[0],
						b.Simplified(summandsInSpan, Fwd(tensor_product.TensorModuleSmul)),
						b.Simplified(
							data[3],
							Fwd(tensor_product.TensorModuleAdd),
							Fwd(tensor_product.TensorModuleZero),
							Fwd(tensor_product.TensorModuleSmul)),
						extended,
						spanOverR,
						submodule.SubmoduleModuleSum.At(ringOps, extension, span, s,
							b.TermAs[Fun[Prod[A, B], _TensorV]](
								"λq:prod(A, B). «tensorS».smul(coeff(q), «pureS»(fst(q), snd(q)))"))))
			}))
		p.Show(
			"the R-span holds every tensor and lies in scalar extension",
			By(
				submodule.SubmoduleSubset.Read(spanOverR),
				allInSpan,
				set_basic.SubsetDef.At(carrier, span),
				set_order.SubsetAntisym.At(span, carrier)))
	}),
})}

// ScalarExtensionBasis — over a ring whose one is not zero, the image of a
// basis under the canonical unit is an R-basis, and the unit is injective on
// that basis: the image spans, and one R-linear map into the free module on
// the basis, taking the image of each basis vector to its delta function,
// carries the image one to one onto a basis of that module.
var ScalarExtensionBasis = scalarExtensionBasisThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionBasis",
	Key:  "prop_11f33df249586e8e",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B). ∀E:set(B).",
		Hypotheses: []string{
			"subring(R, S)",
			"R.one ≠ R.zero",
			"module_on(restrict_ring(R, S), V)",
			"module_basis(restrict_ring(R, S), V, E)",
		},
		Conclusion: "module_basis(R, «extension», «generators») ∧ injective_on(E, «unitS»)",
		Abbrev: Abbrev{
			{Name: "generators", Text: "image(«unitS», E)"},
		},
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		E *Expr[Set[B]],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"one is not zero in R",
			"V is an S-module",
			"E is an S-basis")
		subring, oneNotZero, vectors, basis := given[0], given[1], given[2], given[3]
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		ringOps := p.TermAs[RingOps[A]]("R")
		extension := p.TermAs[ModuleOps[A, _TensorV]]("«extension»")
		unit := p.TermAs[Fun[B, _TensorV]]("«unitS»")
		generators := p.TermAs[Set[_TensorV]]("«generators»")
		carrier := p.TermAs[Set[_TensorV]]("«extension».carrier")
		free := p.TermAs[ModuleOps[A, Fun[B, A]]]("free_module_record(R, E)")
		delta := p.TermAs[Fun[B, Fun[B, A]]]("delta_at")
		freeOn := p.Have(
			"the free module on E is an R-module",
			"module_on(R, free_module_record(R, E))",
			By(R, free_module.FreeModuleOn.At(ringOps, E)))
		deltasIn := p.Have(
			"the delta function of each basis vector lies in the free module",
			"∀e:B. e ∈ E ⇒ delta_at(e) ∈ free_module_record(R, E).carrier",
			By(free_module.DeltaAtIn.Read(R)))
		g, extended := p.ObtainAs[Fun[B, Fun[B, A]]](
			"prescribe its delta function at each basis vector, over S",
			"∃g:(B → B → A). "+
				"    module_homomorphism(restrict_ring(R, S), V, free_module_record(R, E), g) ∧ "+
				"    (∀e:B. e ∈ E ⇒ g(e) = delta_at(e))",
			Named("g"),
			By(
				subring,
				module.ModuleRestrictScalars.Read(freeOn).At(S),
				basis,
				deltasIn,
				free_module.BasisLinearExtension.Read(vectors).At(free, E, delta)))
		gParts := p.Conjuncts(
			extended,
			"g is S-linear",
			"g takes each basis vector to its delta function")
		ell, lifted := p.ObtainAs[Fun[_TensorV, Fun[B, A]]](
			"extend g to scalar extension, over R",
			"∃ell:(set(prod(A, B) → A) → B → A). "+
				"    module_homomorphism(R, «extension», free_module_record(R, E), ell) ∧ "+
				"    (∀a:A. ∀v:B. "+
				"        a ∈ R.carrier ∧ v ∈ V.carrier ⇒ "+
				"        ell(«pureS»(a, v)) = free_module_record(R, E).smul(a, g(v)))",
			Named("ell"),
			By(subring, freeOn, gParts[0], ScalarExtensionLift.Read(R).At(S, V, free, g)))
		ellParts := p.Conjuncts(
			lifted,
			"ell is R-linear",
			"ell scales the values of g on pure tensors")
		basisCarrier := p.Have(
			"the basis lies in V",
			"E ⊆ V.carrier",
			By(basis, linear_independence.BasisInCarrier.At(subringS, V, E)))
		values := p.Have(
			"ell takes the unit image of each basis vector to its delta function",
			"∀e:B. e ∈ E ⇒ ell(«unitS»(e)) = delta_at(e)",
			p.ForEach(func(e *Expr[B]) Action {
				return By(
					comm_ring.OneIn.Read(R),
					ellParts[1].At(p.TermAs[A]("R.one"), e),
					gParts[1].At(e),
					deltasIn.At(e),
					basisCarrier,
					set_basic.SubsetDef.At(E, p.TermAs[Set[B]]("V.carrier")),
					module.SmulOne.Read(freeOn))
			}))
		deltaOneToOne := p.Have(
			"one not being zero, delta is one-to-one on E",
			"injective_on(E, delta_at)",
			By(oneNotZero, free_module.DeltaAtInjective.At(ringOps, E)))
		separated := p.Unfolded(deltaOneToOne, functions.InjectiveOnDef)
		unitOneToOne := p.Have(
			"so the unit is one-to-one on the basis, ell taking its values to the delta functions",
			"injective_on(E, «unitS»)",
			Simp(Fwd(functions.InjectiveOnDef)),
			By(separated, values))
		ellOneToOne := p.Have(
			"and ell is one-to-one on the unit images",
			"injective_on(«generators», ell)",
			Simp(Fwd(functions.InjectiveOnDef)),
			BySets(separated, values))
		images := p.Have(
			"ell carries the unit images onto the delta functions of E",
			"image(ell, «generators») = image(delta_at, E)",
			BySets(values))
		imageIndependent := p.Have(
			"the delta functions of E, a basis of the free module, are independent",
			"module_independent(R, free_module_record(R, E), image(ell, «generators»))",
			By(
				images,
				free_module.DeltaAtBasis.Read(R).At(E),
				linear_independence.ModuleBasisDef.At(
					ringOps, free, p.TermAs[Set[Fun[B, A]]]("image(delta_at, E)"))))
		unitLinear := p.Have(
			"the canonical unit is S-linear",
			"module_homomorphism(restrict_ring(R, S), V, «extension», «unitS»)",
			By(subring, vectors, ScalarExtensionUnitLinear.Read(R).At(S, V)))
		generatorsCarrier := p.Have(
			"the unit images lie in scalar extension",
			"«generators» ⊆ «extension».carrier",
			By(
				module_homomorphism.HomIn.Read(unitLinear),
				basisCarrier,
				set_basic.SubsetDef.At(E, p.TermAs[Set[B]]("V.carrier")),
				set_image.ImageSubsetIff.At(unit, E, carrier)))
		independent := p.Have(
			"the unit images are R-linearly independent, ell carrying them one to one onto an independent set",
			"module_independent(R, «extension», «generators»)",
			By(
				ellParts[0],
				generatorsCarrier,
				ellOneToOne,
				imageIndependent,
				linear_independence.IndependentFromImage.At(ringOps, extension, free, ell, generators)))
		p.Show(
			"the independent spanning image is a basis and the unit is injective on E",
			By(
				subring,
				vectors,
				basisCarrier,
				basis,
				unitOneToOne,
				independent,
				linear_independence.ModuleBasisDef.At(subringS, V, E),
				ScalarExtensionSpanning.Read(R).At(S, V, E),
				linear_independence.ModuleBasisDef.At(ringOps, extension, generators)))
	}),
})}

// ScalarExtensionFiniteDim — scalar extension preserves finite dimension:
// a finite basis lifts to an equally sized basis by injectivity of the unit.
var ScalarExtensionFiniteDim = scalarExtensionFiniteDimThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionFiniteDim",
	Key:  "prop_b4be767300b1e37b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀V:module_ops(A, B).",
		Hypotheses: []string{
			"subfield(L, k)",
			"module_on(«kRing», V)",
			"finite_dimensional(«kRing», V)",
		},
		Conclusion: "finite_dimensional(field_ring(L), «extendedV») ∧ " +
			"module_dim(field_ring(L), «extendedV») = module_dim(«kRing», V)",
		Abbrev: Abbrev{
			{Name: "unit", Text: "λv:B. tensor(«kRing», regular_module(field_ring(L)), V, L.one, v)"},
		},
	}, func(
		p *Argument,
		L field.FieldFact[on.L],
		k *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"k is a subfield",
			"V is a k-module",
			"V is finite dimensional over k")
		subfield, vectors, finiteV := given[0], given[1], given[2]
		ring := field.RingOn.Read(L)
		subring := p.Have(
			"k is a subring of L",
			"subring(field_ring(L), k)",
			By(subfield, field.SubfieldSubring.Read(L).At(k)))
		kRing := p.TermAs[RingOps[A]]("«kRing»")
		fieldRing := p.TermAs[RingOps[A]]("field_ring(L)")
		inverse := p.TermAs[Fun[A, A]]("L.inv")
		extension := p.TermAs[ModuleOps[A, _TensorV]]("«extendedV»")
		unit := p.TermAs[Fun[B, _TensorV]]("«unit»")
		E, finiteBasis := p.ObtainAs[Set[B]](
			"choose a finite basis of V",
			"∃E:set(B). finite(E) ∧ module_basis(«kRing», V, E)",
			Named("E"),
			By(finiteV, module_dimension.FiniteDimensionalDef.At(kRing, V)))
		basisParts := p.Conjuncts(
			finiteBasis,
			"E is finite",
			"E is a k-basis of V")
		baseField := p.Have(
			"the restricted scalar ring is a field on its carrier",
			"ring_subfield(«kRing», L.inv, «kRing».carrier)",
			Simp(Fwd(module_record.RestrictRingDef)),
			By(
				subfield,
				field.SubfieldRingSubfield.Read(L).At(k, k),
				module_record.RestrictRingDef.At(fieldRing, k)))
		lifted := p.Have(
			"the basis lifts injectively to an L-basis",
			"module_basis(field_ring(L), «extendedV», image(«unit», E)) ∧ injective_on(E, «unit»)",
			By(
				subring,
				field.OneNotZeroOn.Read(L),
				vectors,
				basisParts[1],
				ScalarExtensionBasis.Read(ring).At(k, V, E)))
		liftedParts := p.Conjuncts(
			lifted,
			"the image is an L-basis",
			"the unit is injective on E")
		imageSize := p.Have(
			"the lifted basis is finite and has the same size as E",
			"finite(image(«unit», E)) ∧ card(image(«unit», E)) = card(E)",
			By(
				basisParts[0],
				liftedParts[1],
				finite_set.FiniteImage.At(unit, E),
				cardinality.CardImageInj.At(unit, E)))
		p.Show(
			"both dimensions equal the size of the chosen finite basis",
			By(
				basisParts[0],
				vectors,
				subring,
				ScalarExtensionOn.Read(ring).At(k, V),
				imageSize,
				basisParts[1],
				liftedParts[0],
				field.FieldRingSubfield.Read(L),
				baseField,
				module_dimension.FiniteBasisDim.At(
					fieldRing, extension, inverse, p.TermAs[Set[_TensorV]]("image(«unit», E)")),
				module_dimension.DimBasis.At(kRing, V, inverse, E)))
	}),
})}
