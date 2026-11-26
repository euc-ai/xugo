// exactness.go — extending scalars from a subfield is exact: it commutes with
// the kernel and the cokernel of a linear map, whose splittings over k carry to
// L, and so with both cohomology modules of a two-term complex, preserving each
// finite cohomology dimension.

package scalar_extension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SubfieldLinearInnerInverse — a map linear over a subfield of L has a linear
// inner inverse: k is a field, and its ring is the one L restricts to.
var SubfieldLinearInnerInverse = subfieldLinearInnerInverseThm{family.Add(registry.ProofEntry{
	Name: "SubfieldLinearInnerInverse",
	Key:  "prop_549188e54d4b2ea5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"subfield(L, k)",
			"module_homomorphism(«kRing», V, W, f)",
		},
		Conclusion: "∃g:(C → B). " +
			"    module_homomorphism(«kRing», W, V, g) ∧ (∀v:B. v ∈ V.carrier ⇒ f(g(f(v))) = f(v))",
	}, func(
		p *Argument,
		L field.FieldFact[on.L],
		k *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"k is a subfield",
			"f is k-linear")
		subfield, linear := given[0], given[1]
		fieldOps := p.TermAs[FieldOps[A]]("L")
		kField := p.Have(
			"restricting L to k gives a field",
			"field_on(restrict_field(L, k))",
			By(L, subfield, field.SubfieldFieldOn.At(fieldOps, k)))
		p.Show(
			"the inner inverse over that field is one over k",
			By(
				linear,
				field.RestrictFieldRing.At(fieldOps, k),
				module_dimension.LinearMapInnerInverse.Read(kField).At(V, W, f)))
	}),
})}

// ScalarExtensionKernel — extending scalars from a subfield preserves the
// kernel of a linear map: extend its split kernel inclusion and retraction,
// then use the complementary projection to recover each vector in the new
// kernel.
var ScalarExtensionKernel = scalarExtensionKernelThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionKernel",
	Key:  "prop_378599422da3ed46",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"subfield(L, k)",
			"module_homomorphism(«kRing», V, W, f)",
		},
		Conclusion: "module_isomorphic(field_ring(L), «extendedKernel», «targetKernel»)",
		Abbrev: Abbrev{
			{Name: "mapI", Text: "scalar_extension_map(«kRing», " +
				"    field_ring(L), " +
				"    «kernelModule», " +
				"    V, " +
				"    identity_map)"},
			{Name: "mapR", Text: "scalar_extension_map(«kRing», field_ring(L), V, «kernelModule», r)"},
			{Name: "mapAmbientR", Text: "scalar_extension_map(«kRing», field_ring(L), V, V, r)"},
			{Name: "mapC", Text: "scalar_extension_map(«kRing», field_ring(L), V, V, c)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		hypotheses Fact,
	) {
		given := a.Conjuncts(
			hypotheses,
			"k is a subfield",
			"f is k-linear")
		subfield, linear := given[0], given[1]
		ring := field.RingOn.Read(L)
		subring := a.Have(
			"k is a subring of L",
			"subring(field_ring(L), k)",
			By(subfield, field.SubfieldSubring.Read(L).At(k)))
		kRing := a.TermAs[RingOps[A]]("«kRing»")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		kernelModule := a.TermAs[ModuleOps[A, B]]("«kernelModule»")
		kernel := a.TermAs[Set[B]]("group_kernel(W.zero, V.carrier, f)")
		extendedKernel := a.TermAs[ModuleOps[A, _TensorV]]("«extendedKernel»")
		extendedV := a.TermAs[ModuleOps[A, _TensorV]]("«extendedV»")
		i := a.TermAs[Fun[B, B]]("identity_map")
		extendedI := a.TermAs[Fun[_TensorV, _TensorV]]("«mapI»")
		g, innerInverse := a.ObtainAs[Fun[C, B]](
			"choose a linear inner inverse of f",
			"∃g:(C → B). module_homomorphism(«kRing», W, V, g) ∧ (∀v:B. v ∈ V.carrier ⇒ f(g(f(v))) = f(v))",
			Named("g"),
			By(subfield, linear, SubfieldLinearInnerInverse.Read(L).At(k, V, W, f)))
		inverseFacts := a.Conjuncts(
			innerInverse,
			"g is k-linear",
			"the composite fixes the image of f")
		gLinear, fixesImage := inverseFacts[0], inverseFacts[1]
		r, rDef := a.LetAs[Fun[B, B]]("r", "λv:B. V.add(v, V.neg(g(f(v))))")
		c, cDef := a.LetAs[Fun[B, B]]("c", "g ∘ f")
		overK := a.Conjuncts(
			a.Have(
				"over k, r splits the kernel inclusion off V with "+
					"complement c, and f restricts to zero on the kernel",
				"module_homomorphism(«kRing», «kernelModule», V, identity_map) ∧ "+
					"module_homomorphism(«kRing», V, «kernelModule», r) ∧ "+
					"module_homomorphism(«kRing», V, V, r) ∧ "+
					"module_homomorphism(«kRing», V, V, c) ∧ "+
					"module_homomorphism(«kRing», «kernelModule», W, f) ∧ "+
					"(∀v:B. v ∈ «kernelModule».carrier ⇒ r(identity_map(v)) = v) ∧ "+
					"(∀v:B. v ∈ V.carrier ⇒ V.add(r(v), c(v)) = v) ∧ "+
					"(∀v:B. v ∈ «kernelModule».carrier ⇒ f(v) = W.zero)",
				Derive(func(b *Argument) {
					retraction := b.Have(
						"subtracting the inner inverse gives a retraction onto the kernel",
						"module_homomorphism(«kRing», V, «kernelModule», r) ∧ "+
							"(∀v:B. v ∈ group_kernel(W.zero, V.carrier, f) ⇒ r(v) = v)",
						Simp(Fwd(rDef)),
						By(
							fixesImage,
							linear,
							gLinear,
							module_homomorphism.KernelRetractionFromInnerInverse.At(kRing, V, W, f, g)))
					retractionFacts := b.Conjuncts(
						retraction,
						"r maps V linearly into the kernel",
						"r fixes the kernel")
					rLinear, fixesKernel := retractionFacts[0], retractionFacts[1]
					kernelSubmodule := b.Have(
						"the kernel is a k-submodule",
						"submodule(«kRing», V, group_kernel(W.zero, V.carrier, f))",
						By(module_homomorphism.KernelSubmodule.Read(linear)))
					inclusion := b.Have(
						"the kernel inclusion is k-linear",
						"module_homomorphism(«kRing», «kernelModule», V, identity_map)",
						By(
							module_homomorphism.HomIdentity.Read(module_homomorphism.HomSource.Read(linear)),
							kernelSubmodule,
							module_homomorphism.HomRestrictSource.At(kRing, V, V, i, kernel)))
					ambientR := b.Have(
						"the retraction is also a linear endomorphism of V",
						"module_homomorphism(«kRing», V, V, r)",
						By(
							rLinear,
							inclusion,
							module_homomorphism.HomCompose.At(kRing, V, kernelModule, V, r, i),
							functions.ComposeIdentity.At(r)))
					composite := b.Have(
						"the complementary composite is k-linear",
						"module_homomorphism(«kRing», V, V, c)",
						By(Normalized, cDef, linear, gLinear, module_homomorphism.HomCompose.At(kRing, V, W, V, f, g)))
					compositeIdentity := b.Have(
						"the retraction followed after inclusion is the kernel identity",
						"∀v:B. v ∈ «kernelModule».carrier ⇒ r(identity_map(v)) = v",
						Simp(Fwd(module_record.RestrictModuleDef), Fwd(functions.IdentityApply)),
						By(fixesKernel))
					splitting := b.Have(
						"the two complementary projections sum to the identity",
						"∀v:B. v ∈ V.carrier ⇒ V.add(r(v), c(v)) = v",
						Derive(func(d *Argument) {
							v := d.FixAs[B]("v")
							member := d.Assume()
							additive := module.AddGroupOn.Read(module_homomorphism.HomSource.Read(ambientR))
							d.Show(
								"the negative composite cancels its complementary value",
								By(
									Normalized,
									rDef,
									cDef,
									member,
									functions.ComposeApply.At(g, f),
									module_homomorphism.HomIn.Read(composite).AsFact().At(v),
									group.InvMulCancelRightOn.Read(additive).AsFact().At(d.TermAs[B]("c(v)"), v)))
						}))
					kernelZero := b.Have(
						"f is zero on its kernel",
						"∀v:B. v ∈ «kernelModule».carrier ⇒ f(v) = W.zero",
						BySets(group_homomorphism.InKernel))
					b.Show(
						"the five maps are k-linear and the three identities hold",
						By(
							inclusion,
							rLinear,
							ambientR,
							composite,
							kernelSubmodule,
							linear,
							module_homomorphism.HomRestrictSource.At(kRing, V, W, f, kernel),
							compositeIdentity,
							splitting,
							kernelZero))
				})),
			"the kernel inclusion is k-linear",
			"r maps V linearly into the kernel",
			"r is a linear endomorphism of V",
			"c is k-linear",
			"f restricts to a linear map on its kernel",
			"r undoes the inclusion",
			"r and c sum to the identity",
			"f is zero on its kernel")
		inclusion, rLinear, ambientR, composite := overK[0], overK[1], overK[2], overK[3]
		restrictedF, compositeIdentity, splitting, kernelZero := overK[4], overK[5], overK[6], overK[7]

		inclusionL := a.Have(
			"the extended inclusion is L-linear",
			"module_homomorphism(field_ring(L), «extendedKernel», «extendedV», «mapI»)",
			By(subring, inclusion, ScalarExtensionMapSpec.Read(ring).At(k, kernelModule, V, i)))
		leftInverse := a.Have(
			"the extended retraction is a left inverse to the extended inclusion",
			"∀x:set(prod(A, B) → A). x ∈ «extendedKernel».carrier ⇒ «mapR»(«mapI»(x)) = x",
			a.ForEach(func(x *Expr[_TensorV]) Action {
				return By(
					subring,
					inclusion,
					rLinear,
					compositeIdentity,
					ScalarExtensionMapInverse.Read(ring).At(k, kernelModule, V, i, r, x))
			}))
		injective := a.Have(
			"a left inverse makes the extended inclusion injective",
			"injective_on(«extendedKernel».carrier, «mapI»)",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				x, y := b.FixAs[_TensorV]("x"), b.FixAs[_TensorV]("y")
				equalImages := b.Assume()
				b.Show(
					"apply the left inverse to the equal images",
					By(Normalized, equalImages, leftInverse.At(x), leftInverse.At(y)))
			}))
		image := a.Have(
			"the image of the extended inclusion is precisely the new kernel",
			"image(«mapI», «extendedKernel».carrier) = «kernelOfMapF»",
			Derive(func(b *Argument) {
				imageInKernel := b.Have(
					"the extended inclusion takes values in the new kernel",
					"∀t:set(prod(A, B) → A). t ∈ «extendedKernel».carrier ⇒ «mapI»(t) ∈ «kernelOfMapF»",
					Derive(func(d *Argument) {
						t := d.FixAs[_TensorV]("t")
						assumed := d.Assume()
						extendsZero := d.Simplified(
							d.Have(
								"extending the zero restriction still gives zero",
								"scalar_extension_map(«kRing», field_ring(L), «kernelModule», W, f)(t) = «extendedW».zero",
								By(
									assumed,
									subring,
									restrictedF,
									kernelZero,
									ScalarExtensionMapVanishes.Read(ring).At(k, kernelModule, W, f, t))),
							Fwd(ScalarExtensionZero))
						member := d.Simplified(assumed, Fwd(ScalarExtensionCarrier))
						inclusionMap := d.Simplified(inclusionL, Fwd(functions.IdentityApply))
						d.Show(
							"composition with f extends its zero restriction: identity_map "+
								"unfolded, the composite λv. f(identity_map(v)) collapses to f",
							Simp(Fwd(ScalarExtensionCarrier), Fwd(ScalarExtensionZero), Fwd(functions.IdentityApply)),
							BySets(
								Normalized,
								extendsZero,
								member,
								subring,
								inclusion,
								linear,
								functions.IdentityApply,
								group_homomorphism.InKernel,
								ScalarExtensionMapCompose.Read(ring).At(k, kernelModule, V, W, i, f, t),
								module_homomorphism.HomIn.Read(inclusionMap).AsFact().At(t)))
					}))
				ontoKernel := b.Have(
					"the extended retraction supplies a preimage for every new kernel vector",
					Statement{
						Binders:    "∀x:set(prod(A, B) → A).",
						Hypotheses: []string{"x ∈ «kernelOfMapF»"},
						Conclusion: "«mapR»(x) ∈ «extendedKernel».carrier ∧ «mapI»(«mapR»(x)) = x",
					},
					Derive(func(d *Argument) {
						x := d.FixAs[_TensorV]("x")
						member := d.Assume()
						killed := d.Have(
							"the chosen vector lies in the extended source and is killed by the extension of f",
							"x ∈ «extendedV».carrier ∧ «mapF»(x) = «extendedW».zero",
							BySets(member, group_homomorphism.InKernel))
						decomposition := d.Simplified(
							d.Have(
								"scalar extension preserves the complementary decomposition",
								"«extendedV».add(«mapAmbientR»(x), «mapC»(x)) = x",
								By(
									subring,
									ambientR,
									composite,
									splitting,
									killed,
									ScalarExtensionMapComplement.Read(ring).At(k, V, r, c, x))),
							Fwd(ScalarExtensionAdd),
							Fwd(cDef),
							Fwd(functions.ComposeApply))
						onTensors := d.Simplified(killed, Fwd(ScalarExtensionCarrier), Fwd(ScalarExtensionZero))
						retractionL := d.Have(
							"the extended retraction is L-linear",
							"module_homomorphism(field_ring(L), «extendedV», «extendedKernel», «mapR»)",
							By(subring, rLinear, ScalarExtensionMapSpec.Read(ring).At(k, V, kernelModule, r)))
						inverseL := d.Have(
							"the extended inner inverse is L-linear",
							"module_homomorphism(field_ring(L), "+
								"    «extendedW», "+
								"    «extendedV», "+
								"    scalar_extension_map(«kRing», field_ring(L), W, V, g))",
							By(subring, gLinear, ScalarExtensionMapSpec.Read(ring).At(k, W, V, g)))
						ambientRL := d.Have(
							"the extended ambient retraction is L-linear",
							"module_homomorphism(field_ring(L), «extendedV», «extendedV», «mapAmbientR»)",
							By(subring, ambientR, ScalarExtensionMapSpec.Read(ring).At(k, V, V, r)))
						d.Show(
							"its retraction is a preimage in the extended kernel",
							Simp(Fwd(ScalarExtensionCarrier), Fwd(functions.IdentityApply)),
							SplitConj(
								Case(
									"the retracted vector lies in the extended kernel module",
									By(onTensors, module_homomorphism.HomIn.Read(retractionL).AsFact().At(x))),
								Case(
									"the complementary term vanishes on this kernel vector",
									By(
										module_homomorphism.HomZero.Read(inverseL),
										decomposition,
										subring,
										onTensors,
										rLinear,
										inclusion,
										linear,
										gLinear,
										functions.IdentityApply,
										ScalarExtensionMapCompose.Read(ring).At(k, V, kernelModule, V, r, i, x),
										ScalarExtensionMapCompose.Read(ring).At(k, V, W, V, f, g, x),
										module_homomorphism.HomIn.Read(ambientRL).AsFact().At(x),
										group.RightIdentityOn.Read(
											module.AddGroupOn.Read(module_homomorphism.HomTarget.Read(ambientRL))).AsFact().At(
											d.TermAs[_TensorV]("«mapAmbientR»(x)"))))))
					}))
				b.Show(
					"each set lies in the other",
					BySets(imageInKernel, ontoKernel))
			}))

		a.Show(
			"one-to-one, the extended inclusion is an isomorphism onto its image, the new kernel",
			image.RwRev(),
			By(
				inclusionL,
				injective,
				module_homomorphism.IsomorphismOntoImage.At(fieldRing, extendedKernel, extendedV, extendedI),
				module_homomorphism.IsomorphicOfIsomorphism.At(
					fieldRing,
					extendedKernel,
					a.TermAs[ModuleOps[A, _TensorV]](
						"restrict_module(«extendedV», image(«mapI», «extendedKernel».carrier))"),
					extendedI)))
	}),
})}

// ScalarExtensionCokernel — extending scalars from a subfield preserves the
// cokernel of a linear map: split the quotient, factor its complementary
// projection through f, and extend these split identities.
var ScalarExtensionCokernel = scalarExtensionCokernelThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionCokernel",
	Key:  "prop_886cf1f1c6862069",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"subfield(L, k)",
			"module_homomorphism(«kRing», V, W, f)",
		},
		Conclusion: "module_isomorphic(field_ring(L), «extendedCokernel», «targetCokernel»)",
		Abbrev: Abbrev{
			{Name: "quotientMap", Text: "coset_map(W.add, image(f, V.carrier))"},
			{Name: "mapQ", Text: "scalar_extension_map(«kRing», field_ring(L), W, «cokernel», «quotientMap»)"},
			{Name: "mapS", Text: "scalar_extension_map(«kRing», field_ring(L), «cokernel», W, s)"},
			{Name: "mapH", Text: "scalar_extension_map(«kRing», field_ring(L), W, V, h)"},
			{Name: "mapP", Text: "scalar_extension_map(«kRing», field_ring(L), W, W, p)"},
			{Name: "mapU", Text: "scalar_extension_map(«kRing», field_ring(L), W, W, u)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		hypotheses Fact,
	) {
		given := a.Conjuncts(
			hypotheses,
			"k is a subfield",
			"f is k-linear")
		subfield, linear := given[0], given[1]
		ring := field.RingOn.Read(L)
		subring := a.Have(
			"k is a subring of L",
			"subring(field_ring(L), k)",
			By(subfield, field.SubfieldSubring.Read(L).At(k)))
		fieldOps := a.TermAs[FieldOps[A]]("L")
		kRing := a.TermAs[RingOps[A]]("«kRing»")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		imageF := a.TermAs[Set[C]]("image(f, V.carrier)")
		cokernel := a.TermAs[ModuleOps[A, Set[C]]]("«cokernel»")
		q := a.TermAs[Fun[C, Set[C]]]("«quotientMap»")
		kField := a.Have(
			"restricting L to k gives a field",
			"field_on(restrict_field(L, k))",
			By(L, subfield, field.SubfieldFieldOn.At(fieldOps, k)))
		imageSubmodule := a.Have(
			"the image of f is a k-submodule of W",
			"submodule(«kRing», W, image(f, V.carrier))",
			By(module_homomorphism.ImageSubmodule.Read(linear)))
		qLinear := a.Have(
			"the quotient projection is k-linear",
			"module_homomorphism(«kRing», W, «cokernel», «quotientMap»)",
			By(
				module_homomorphism.HomTarget.Read(linear),
				imageSubmodule,
				module_homomorphism.ProjectionHom.At(kRing, W, imageF)))
		qCarrier := a.Have(
			"the quotient carrier consists of cosets",
			"«cokernel».carrier = left_cosets(W.add, W.carrier, image(f, V.carrier))",
			Simp(Fwd(submodule.QuotientModuleDef)),
			Basic())
		qOnto := a.Have(
			"every quotient vector is represented by a vector of W",
			"image(«quotientMap», W.carrier) = «cokernel».carrier",
			By(
				submodule.SubmoduleSubset.Read(imageSubmodule),
				qCarrier,
				quotient_group.LeftCosetsImage.Read(
					module.AddGroupOn.Read(module_homomorphism.HomTarget.Read(linear))).At(
					imageF)))
		s, sectionFacts := a.ObtainAs[Fun[Set[C], C]](
			"choose a linear section of the quotient map",
			"∃s:(set(C) → C). "+
				"    module_homomorphism(«kRing», «cokernel», W, s) ∧ "+
				"    (∀z:set(C). z ∈ «cokernel».carrier ⇒ «quotientMap»(s(z)) = z)",
			Named("s"),
			Derive(func(b *Argument) {
				onCosets := b.Simplified(qOnto, Fwd(qCarrier))
				linearOverField := b.Simplified(qLinear, Fwd(field.RestrictFieldRing))
				b.Show(
					"the section theorem applies over the restricted field",
					Simp(Fwd(field.RestrictFieldRing), Fwd(qCarrier)),
					By(onCosets, linearOverField, module_dimension.LinearMapSection.Read(kField).At(W, cokernel, q)))
			}))
		sections := a.Conjuncts(
			sectionFacts,
			"s is k-linear",
			"s is a section of the quotient projection")
		sLinear, section := sections[0], sections[1]
		imageKernel := a.Have(
			"the quotient map has the original image as kernel",
			"image(f, V.carrier) = group_kernel(«cokernel».zero, W.carrier, «quotientMap»)",
			Simp(Fwd(submodule.QuotientModuleDef)),
			By(
				module_homomorphism.HomSource.Read(qLinear),
				imageSubmodule,
				module_homomorphism.ProjectionKernel.At(kRing, W, imageF)))
		innerQ := a.Have(
			"the section is an inner inverse of the quotient projection",
			"∀w:C. w ∈ W.carrier ⇒ «quotientMap»(s(«quotientMap»(w))) = «quotientMap»(w)",
			Derive(func(b *Argument) {
				w := b.FixAs[C]("w")
				member := b.Assume()
				b.Show(
					"apply the section identity to the projected vector",
					By(
						section.At(b.TermAs[Set[C]]("«quotientMap»(w)")),
						member,
						module_homomorphism.HomIn.Read(qLinear).AsFact().At(w)))
			}))
		p, pDef := a.LetAs[Fun[C, C]]("p", "λw:C. W.add(w, W.neg(s(«quotientMap»(w))))")
		pImage := a.Have(
			"the complementary projection takes values in the image of f",
			"module_homomorphism(«kRing», W, restrict_module(W, image(f, V.carrier)), p)",
			Derive(func(b *Argument) {
				kernelOfQ := b.Simplified(imageKernel, Fwd(submodule.QuotientModuleDef))
				b.Show(
					"the generic kernel retraction is a projection onto the image",
					Simp(Fwd(pDef)),
					By(
						innerQ,
						kernelOfQ,
						qLinear,
						sLinear,
						module_homomorphism.KernelRetractionFromInnerInverse.At(kRing, W, cokernel, q, s)))
			}))
		identityW := a.TermAs[Fun[C, C]]("identity_map")
		pLinear := a.Have(
			"the complementary projection is a linear endomorphism of W",
			"module_homomorphism(«kRing», W, W, p)",
			By(
				Normalized,
				pImage,
				module_homomorphism.HomIdentity.Read(module_homomorphism.HomSource.Read(qLinear)),
				imageSubmodule,
				module_homomorphism.HomRestrictSource.At(kRing, W, W, identityW, imageF),
				module_homomorphism.HomCompose.At(
					kRing, W, a.TermAs[ModuleOps[A, C]]("restrict_module(W, image(f, V.carrier))"), W, p, identityW),
				functions.ComposeIdentity.At(p)))
		g, inverseFacts := a.ObtainAs[Fun[C, B]](
			"choose a linear inner inverse of f",
			"∃g:(C → B). module_homomorphism(«kRing», W, V, g) ∧ (∀v:B. v ∈ V.carrier ⇒ f(g(f(v))) = f(v))",
			Named("g"),
			By(subfield, linear, SubfieldLinearInnerInverse.Read(L).At(k, V, W, f)))
		inverse := a.Conjuncts(
			inverseFacts,
			"g is k-linear",
			"the composite f ∘ g fixes the image of f")
		gLinear, innerF := inverse[0], inverse[1]
		fixesImage := a.Have(
			"the composite f ∘ g fixes every point of the image",
			"∀y:C. y ∈ image(f, V.carrier) ⇒ f(g(y)) = y",
			Derive(func(b *Argument) {
				y := b.FixAs[C]("y")
				member := b.Assume()
				v, preimage := b.ObtainAs[B](
					"choose a preimage of the image point",
					"∃v:B. v ∈ V.carrier ∧ f(v) = y",
					Named("v"),
					By(Normalized, member, set_basic.InImage.At(f, b.TermAs[Set[B]]("V.carrier"), y)))
				b.Show(
					"the inner-inverse identity at that preimage fixes y",
					By(Normalized, preimage, innerF.At(v)))
			}))
		h, hDef := a.LetAs[Fun[C, B]]("h", "g ∘ p")
		hLinear := a.Have(
			"the complementary projection lifts linearly through f",
			"module_homomorphism(«kRing», W, V, h)",
			By(Normalized, hDef, pLinear, gLinear, module_homomorphism.HomCompose.At(kRing, W, W, V, p, g)))
		u, uDef := a.LetAs[Fun[C, C]]("u", "s ∘ «quotientMap»")
		uLinear := a.Have(
			"the section followed after the quotient is linear",
			"module_homomorphism(«kRing», W, W, u)",
			By(
				Normalized,
				uDef,
				qLinear,
				sLinear,
				module_homomorphism.HomCompose.At(kRing, W, cokernel, W, q, s)))
		factor := a.Have(
			"applying f to the lift recovers the complementary projection",
			"∀w:C. w ∈ W.carrier ⇒ f(h(w)) = p(w)",
			Derive(func(b *Argument) {
				w := b.FixAs[C]("w")
				member := b.Assume()
				b.Show(
					"the projection lies in the image where the inner inverse is exact",
					By(
						Normalized,
						fixesImage.At(b.TermAs[C]("p(w)")),
						hDef,
						member,
						module_homomorphism.HomIn.Read(pImage).AsFact().At(w),
						functions.ComposeApply.At(g, p)))
			}))
		killed := a.Have(
			"the quotient map kills the image of f",
			"∀v:B. v ∈ V.carrier ⇒ «quotientMap»(f(v)) = «cokernel».zero",
			Derive(func(b *Argument) {
				v := b.FixAs[B]("v")
				member := b.Assume()
				kernelOfQ := b.Simplified(imageKernel, Fwd(submodule.QuotientModuleDef))
				b.Show(
					"the image point belongs to the quotient kernel",
					Simp(Fwd(submodule.QuotientModuleDef)),
					BySets(
						Normalized,
						kernelOfQ,
						member,
						module_homomorphism.HomIn.Read(linear).AsFact().At(v),
						group_homomorphism.InKernel))
			}))
		splitting := a.Have(
			"the complementary projections sum to the identity of W",
			"∀w:C. w ∈ W.carrier ⇒ W.add(p(w), u(w)) = w",
			Derive(func(b *Argument) {
				w := b.FixAs[C]("w")
				member := b.Assume()
				additive := module.AddGroupOn.Read(module_homomorphism.HomSource.Read(pLinear))
				b.Show(
					"the negative section value cancels its complementary term",
					By(
						Normalized,
						pDef,
						uDef,
						member,
						functions.ComposeApply.At(s, q),
						module_homomorphism.HomIn.Read(uLinear).AsFact().At(w),
						group.InvMulCancelRightOn.Read(additive).AsFact().At(b.TermAs[C]("u(w)"), w)))
			}))
		compositeQF := a.TermAs[Fun[B, Set[C]]]("λv:B. «quotientMap»(f(v))")
		compositeQFLinear := a.Have(
			"the quotient composed with f is linear",
			"module_homomorphism(«kRing», V, «cokernel», λv:B. «quotientMap»(f(v)))",
			By(
				linear,
				qLinear,
				module_homomorphism.HomCompose.At(kRing, V, W, cokernel, f, q),
				functions.ComposeApply.At(q, f)))

		extendedV := a.TermAs[ModuleOps[A, _TensorV]]("«extendedV»")
		extendedW := a.TermAs[ModuleOps[A, _TensorW]]("«extendedW»")
		extendedCokernel := a.TermAs[ModuleOps[A, _TensorCokernel]]("«extendedCokernel»")
		mapF := a.TermAs[Fun[_TensorV, _TensorW]]("«mapF»")
		mapQ := a.TermAs[Fun[_TensorW, _TensorCokernel]]("«mapQ»")
		mapS := a.TermAs[Fun[_TensorCokernel, _TensorW]]("«mapS»")
		mapH := a.TermAs[Fun[_TensorW, _TensorV]]("«mapH»")
		sectionL := a.Have(
			"extending the quotient section preserves its right-inverse identity",
			"∀t:set(prod(A, set(C)) → A). t ∈ «extendedCokernel».carrier ⇒ «mapQ»(«mapS»(t)) = t",
			a.ForEach(func(t *Expr[_TensorCokernel]) Action {
				return By(
					subring,
					sLinear,
					qLinear,
					section,
					ScalarExtensionMapInverse.Read(ring).At(k, cokernel, W, s, q, t))
			}))
		factorL := a.Have(
			"the extended lift still factors the complementary projection",
			"∀t:set(prod(A, C) → A). t ∈ «extendedW».carrier ⇒ «mapF»(«mapH»(t)) = «mapP»(t)",
			Derive(func(b *Argument) {
				t := b.FixAs[_TensorW]("t")
				member := b.Assume()
				b.Show(
					"composition and agreement transport the factorization",
					By(
						factor,
						subring,
						member,
						hLinear,
						linear,
						pLinear,
						ScalarExtensionMapCompose.Read(ring).At(k, W, V, W, h, f, t),
						ScalarExtensionMapCongruence.Read(ring).At(k, W, W, p, b.TermAs[Fun[C, C]]("λw:C. f(h(w))"), t)))
			}))
		compositeL := a.Have(
			"extending the section composite commutes with composition",
			"∀t:set(prod(A, C) → A). t ∈ «extendedW».carrier ⇒ «mapS»(«mapQ»(t)) = «mapU»(t)",
			Derive(func(b *Argument) {
				t := b.FixAs[_TensorW]("t")
				member := b.Assume()
				b.Show(
					"the induced composite is the composite of the induced maps",
					Simp(Fwd(uDef), Fwd(functions.ComposeApply)),
					By(
						subring,
						member,
						qLinear,
						sLinear,
						ScalarExtensionMapCompose.Read(ring).At(k, W, cokernel, W, q, s, t)))
			}))
		splittingL := a.Have(
			"the extended complementary composites sum to the identity",
			Statement{
				Binders:    "∀t:set(prod(A, C) → A).",
				Hypotheses: []string{"t ∈ «extendedW».carrier"},
				Conclusion: "«extendedW».add(«mapF»(«mapH»(t)), «mapS»(«mapQ»(t))) = t",
			},
			Derive(func(b *Argument) {
				t := b.FixAs[_TensorW]("t")
				member := b.Simplified(b.Assume(), Fwd(ScalarExtensionCarrier))
				b.Show(
					"the sum law transports the complementary decomposition",
					Simp(Fwd(ScalarExtensionAdd)),
					By(
						factorL.At(t),
						compositeL.At(t),
						member,
						subring,
						pLinear,
						uLinear,
						splitting,
						ScalarExtensionMapComplement.Read(ring).At(k, W, p, u, t)))
			}))
		killedL := a.Have(
			"the extended quotient map kills the extension of f",
			"∀t:set(prod(A, B) → A). t ∈ «extendedV».carrier ⇒ «mapQ»(«mapF»(t)) = «extendedCokernel».zero",
			Derive(func(b *Argument) {
				t := b.FixAs[_TensorV]("t")
				member := b.Assume()
				b.Show(
					"the composite vanishes on V, so it extends to zero, and composition carries it over",
					Simp(Fwd(ScalarExtensionZero)),
					By(
						killed,
						member,
						subring,
						linear,
						compositeQFLinear,
						qLinear,
						ScalarExtensionMapVanishes.Read(ring).At(k, V, cokernel, compositeQF, t),
						ScalarExtensionMapCompose.Read(ring).At(k, V, W, cokernel, f, q, t)))
			}))
		mapFLinear := a.Have(
			"the extension of f is L-linear",
			"module_homomorphism(field_ring(L), «extendedV», «extendedW», «mapF»)",
			By(subring, linear, ScalarExtensionMapSpec.Read(ring).At(k, V, W, f)))
		mapHLinear := a.Have(
			"the extended lift is L-linear",
			"module_homomorphism(field_ring(L), «extendedW», «extendedV», «mapH»)",
			By(subring, hLinear, ScalarExtensionMapSpec.Read(ring).At(k, W, V, h)))
		mapQLinear := a.Have(
			"the extended quotient map is L-linear",
			"module_homomorphism(field_ring(L), «extendedW», «extendedCokernel», «mapQ»)",
			By(subring, qLinear, ScalarExtensionMapSpec.Read(ring).At(k, W, cokernel, q)))
		mapSLinear := a.Have(
			"the extended section is L-linear",
			"module_homomorphism(field_ring(L), «extendedCokernel», «extendedW», «mapS»)",
			By(subring, sLinear, ScalarExtensionMapSpec.Read(ring).At(k, cokernel, W, s)))

		a.Show(
			"the transported split identities identify the extended cokernel",
			By(
				killedL,
				splittingL,
				sectionL,
				mapFLinear,
				mapHLinear,
				mapQLinear,
				mapSLinear,
				module_homomorphism.ModuleCokernelOfSplitting.At(
					fieldRing, extendedV, extendedW, extendedCokernel, mapF, mapQ, mapS, mapH)))
	}),
})}

// TwoTermComplexFieldBaseChange — scalar extension commutes with both
// cohomology modules of a two-term complex and preserves each finite
// cohomology dimension through the kernel and cokernel isomorphisms.
var TwoTermComplexFieldBaseChange = twoTermComplexFieldBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "TwoTermComplexFieldBaseChange",
	Key:  "prop_ca8d4bc978e5ce87",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"subfield(L, k)",
			"module_homomorphism(«kRing», V, W, f)",
		},
		Conclusion: "module_isomorphic(field_ring(L), «extendedKernel», «targetKernel») ∧ " +
			"module_isomorphic(field_ring(L), «extendedCokernel», «targetCokernel») ∧ " +
			"(finite_dimensional(«kRing», «kernelModule») ⇒ " +
			"    finite_dimensional(field_ring(L), «targetKernel») ∧ " +
			"    module_dim(field_ring(L), «targetKernel») = module_dim(«kRing», «kernelModule»)) ∧ " +
			"(finite_dimensional(«kRing», «cokernel») ⇒ " +
			"    finite_dimensional(field_ring(L), «targetCokernel») ∧ " +
			"    module_dim(field_ring(L), «targetCokernel») = module_dim(«kRing», «cokernel»))",
		Abbrev: Abbrev{
			{Name: "extendedX", Text: "scalar_extension(«kRing», field_ring(L), X)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		dimensionTransport := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀k:set(A). ∀X:module_ops(A, D). ∀Y:module_ops(A, E).",
			Hypotheses: []string{
				"subfield(L, k)",
				"module_on(«kRing», X)",
				"module_on(field_ring(L), Y)",
				"module_isomorphic(field_ring(L), «extendedX», Y)",
				"finite_dimensional(«kRing», X)",
			},
			Conclusion: "finite_dimensional(field_ring(L), Y) ∧ " +
				"module_dim(field_ring(L), Y) = module_dim(«kRing», X)",
		}, func(
			p *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			X *Expr[ModuleOps[A, D]],
			Y *Expr[ModuleOps[A, E]],
			hypotheses Fact,
		) {
			given := p.Conjuncts(
				hypotheses,
				"k is a subfield",
				"X is a k-module",
				"Y is an L-module",
				"L ⊗ X is isomorphic to Y",
				"X is finite dimensional over k")
			subfield, baseModule, targetModule, isomorphic, finite :=
				given[0], given[1], given[2], given[3], given[4]
			fieldRing := p.TermAs[RingOps[A]]("field_ring(L)")
			extendedX := p.TermAs[ModuleOps[A, Set[Fun[Prod[A, D], A]]]]("«extendedX»")
			extendedDimension := p.Have(
				"L ⊗ X has the dimension of X",
				"finite_dimensional(field_ring(L), «extendedX») ∧ "+
					"module_dim(field_ring(L), «extendedX») = module_dim(«kRing», X)",
				By(baseModule, subfield, finite, ScalarExtensionFiniteDim.Read(L).At(k, X)))
			transported := p.Have(
				"the isomorphism carries that dimension to Y",
				"finite_dimensional(field_ring(L), Y) ∧ "+
					"module_dim(field_ring(L), Y) = module_dim(field_ring(L), «extendedX»)",
				By(
					targetModule,
					baseModule,
					subfield,
					field.SubfieldSubring.Read(L).At(k),
					ScalarExtensionOn.Read(field.RingOn.Read(L)).At(k, X),
					extendedDimension,
					isomorphic,
					field.FieldRingSubfield.Read(L),
					module_dimension.IsomorphicDim.At(fieldRing, extendedX, p.TermAs[Fun[A, A]]("L.inv"), Y)))
			p.Show(
				"so Y is finite dimensional with the dimension of X",
				By(transported, extendedDimension))
		})
		return ctx.Theorem(headline, func(
			p *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hypotheses Fact,
		) {
			given := p.Conjuncts(
				hypotheses,
				"k is a subfield",
				"f is k-linear")
			subfield, linear := given[0], given[1]
			kernelModule := p.TermAs[ModuleOps[A, B]]("«kernelModule»")
			cokernel := p.TermAs[ModuleOps[A, Set[C]]]("«cokernel»")
			kernelIso := p.Have(
				"scalar extension commutes with the kernel",
				"module_isomorphic(field_ring(L), «extendedKernel», «targetKernel»)",
				By(subfield, linear, ScalarExtensionKernel.Read(L).At(k, V, W, f)))
			cokernelIso := p.Have(
				"scalar extension commutes with the cokernel",
				"module_isomorphic(field_ring(L), «extendedCokernel», «targetCokernel»)",
				By(subfield, linear, ScalarExtensionCokernel.Read(L).At(k, V, W, f)))
			linearL := p.Have(
				"the induced map is L-linear",
				"module_homomorphism(field_ring(L), «extendedV», «extendedW», «mapF»)",
				By(
					subfield,
					field.SubfieldSubring.Read(L).At(k),
					linear,
					ScalarExtensionMapSpec.Read(field.RingOn.Read(L)).At(k, V, W, f)))
			p.Show(
				"the cohomology isomorphisms preserve each finite cohomology dimension",
				SplitConjAll(
					Case(
						"the degree-zero cohomology commutes with extension",
						By(kernelIso)),
					Case(
						"the degree-one cohomology commutes with extension",
						By(cokernelIso)),
					Case(
						"finite kernel cohomology retains its dimension",
						By(
							subfield,
							kernelIso,
							module_homomorphism.KernelSubmodule.Read(linear),
							submodule.SubmoduleModuleOn.Read(module_homomorphism.HomSource.Read(linear)).At(
								p.TermAs[Set[B]]("group_kernel(W.zero, V.carrier, f)")),
							module_homomorphism.KernelSubmodule.Read(linearL),
							submodule.SubmoduleModuleOn.Read(module_homomorphism.HomSource.Read(linearL)).At(
								p.TermAs[Set[_TensorV]]("«kernelOfMapF»")),
							Read(dimensionTransport, L).At(
								k, kernelModule, p.TermAs[ModuleOps[A, _TensorV]]("«targetKernel»")))),
					Case(
						"finite cokernel cohomology retains its dimension",
						By(
							subfield,
							cokernelIso,
							module_homomorphism.ImageSubmodule.Read(linear),
							submodule.QuotientModuleOn.Read(module_homomorphism.HomTarget.Read(linear)).At(
								p.TermAs[Set[C]]("image(f, V.carrier)")),
							module_homomorphism.ImageSubmodule.Read(linearL),
							submodule.QuotientModuleOn.Read(module_homomorphism.HomTarget.Read(linearL)).At(
								p.TermAs[Set[_TensorW]]("image(«mapF», «extendedV».carrier)")),
							Read(dimensionTransport, L).At(
								k, cokernel, p.TermAs[ModuleOps[A, Set[_TensorW]]]("«targetCokernel»"))))))
		})
	}),
})}
