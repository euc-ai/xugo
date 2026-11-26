// map_laws.go — scalar extension as a functor. An S-linear map into an R-module
// lifts R-linearly across the tensor quotient, the canonical unit v ↦ 1 ⊗ v is
// S-linear, and the two give the R-linear map an S-linear map induces, specified
// on pure tensors; an induced map is S-linear on the tensor modules, and
// extension preserves composition, the identity, agreement on V, pointwise sums
// and the zero map, and with them a left inverse, a pair of maps summing to the
// identity, and a map vanishing on V.

package scalar_extension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ScalarExtensionLift — an S-linear map into an R-module extends to an
// R-linear map from scalar extension: the tensor lift commutes with every
// ring scalar by uniqueness on pure tensors.
var ScalarExtensionLift = scalarExtensionLiftThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionLift",
	Key:  "prop_edb42ae9d0649fae",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B). ∀N:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_on(R, N)",
			"module_homomorphism(restrict_ring(R, S), V, N, f)",
		},
		Conclusion: "∃h:(set(prod(A, B) → A) → C). " +
			"    module_homomorphism(R, «extension», N, h) ∧ " +
			"    (∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ h(«pureS»(a, v)) = «phi»(a, v))",
		Abbrev: Abbrev{
			{Name: "phi", Text: "λa:A. λv:B. N.smul(a, f(v))"},
		},
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		N *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"N is an R-module",
			"f is S-linear")
		subring, target, linear := given[0], given[1], given[2]
		vectors := module_homomorphism.HomSource.Read(linear)
		products := comm_ring.MulMonoidOn.Read(R)
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		ringOps := p.TermAs[RingOps[A]]("R")
		ringCarrier := p.TermAs[Set[A]]("R.carrier")
		regularR := p.TermAs[ModuleOps[A, A]]("regular_module(R)")
		tensorS := p.TermAs[ModuleOps[A, _TensorV]]("«tensorS»")
		regularOverS := p.Have(
			"R is an S-module under multiplication",
			"module_on(restrict_ring(R, S), regular_module(R))",
			By(subring, module.RegularModuleOverSubring.Read(R).At(S)))
		scaledIn := p.Have(
			"the scaled image lies in N",
			"∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ «phi»(a, v) ∈ N.carrier",
			Derive(func(q *Argument) {
				a, v := q.FixAs[A]("a"), q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"the image lies in N and N is closed under R-scaling",
					By(
						members,
						module_homomorphism.HomIn.Read(linear).AsFact().At(v),
						module.SmulIn.Read(target).AsFact().At(a, f.Apply(v))))
			}))
		scalarsAdd := p.Have(
			"addition of ring scalars is preserved",
			Statement{
				Binders:    "∀a b:A. ∀v:B.",
				Hypotheses: []string{"a ∈ R.carrier", "b ∈ R.carrier", "v ∈ V.carrier"},
				Conclusion: "«phi»(a + b, v) = N.add(«phi»(a, v), «phi»(b, v))",
			},
			Derive(func(q *Argument) {
				a, b, v := q.FixAs[A]("a"), q.FixAs[A]("b"), q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"a sum of scalars distributes over the image of v",
					By(
						members,
						module_homomorphism.HomIn.Read(linear).AsFact().At(v),
						module.SmulAddRight.Read(target).AsFact().At(a, b, f.Apply(v))))
			}))
		vectorsAdd := p.Have(
			"addition of vectors is preserved",
			Statement{
				Binders:    "∀a:A. ∀u v:B.",
				Hypotheses: []string{"a ∈ R.carrier", "u ∈ V.carrier", "v ∈ V.carrier"},
				Conclusion: "«phi»(a, V.add(u, v)) = N.add(«phi»(a, u), «phi»(a, v))",
			},
			Derive(func(q *Argument) {
				a, u, v := q.FixAs[A]("a"), q.FixAs[B]("u"), q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"f preserves the sum and scaling distributes over its images",
					By(
						members,
						module_homomorphism.HomIn.Read(linear).AsFact().At(u),
						module_homomorphism.HomIn.Read(linear).AsFact().At(v),
						module_homomorphism.HomAdd.Read(linear).AsFact().At(u, v),
						module.SmulAddLeft.Read(target).AsFact().At(a, f.Apply(u), f.Apply(v))))
			}))
		scalarOnRing := p.Have(
			"an S-scalar in the ring coordinate factors out",
			"∀c a:A. ∀v:B. c ∈ S ∧ a ∈ R.carrier ∧ v ∈ V.carrier ⇒ «phi»(c * a, v) = N.smul(c, «phi»(a, v))",
			Derive(func(q *Argument) {
				c, a, v := q.FixAs[A]("c"), q.FixAs[A]("a"), q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"S lies in R and successive scalings multiply",
					By(
						comm_ring.SubringSubset.Read(subring),
						members,
						set_basic.SubsetDef.At(S, ringCarrier),
						module_homomorphism.HomIn.Read(linear).AsFact().At(v),
						module.SmulMul.Read(target).AsFact().At(c, a, f.Apply(v))))
			}))
		scalarOnVector := p.Have(
			"an S-scalar in the vector coordinate factors out",
			Statement{
				Binders:    "∀c a:A. ∀v:B.",
				Hypotheses: []string{"c ∈ S", "a ∈ R.carrier", "v ∈ V.carrier"},
				Conclusion: "«phi»(a, V.smul(c, v)) = N.smul(c, «phi»(a, v))",
			},
			Derive(func(q *Argument) {
				c, a, v := q.FixAs[A]("c"), q.FixAs[A]("a"), q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"f preserves the S-scaling and multiplication of scalars commutes",
					By(
						comm_ring.SubringSubset.Read(subring),
						members,
						set_basic.SubsetDef.At(S, ringCarrier),
						module_homomorphism.HomIn.Read(linear).AsFact().At(v),
						module.SmulMul.Read(target).AsFact().At(c, a, f.Apply(v)),
						module_homomorphism.HomSmul.Read(linear).AsFact().At(c, v),
						module.SmulMul.Read(target).AsFact().At(a, c, f.Apply(v)),
						comm_monoid.CommOn.Read(products).AsFact().At(c, a)))
			}))
		rule := p.TermAs[Fun2[A, B, C]]("«phi»")
		bilinear := p.Have(
			"scaling the image of f is bilinear over S",
			"bilinear_map(restrict_ring(R, S), regular_module(R), V, N, «phi»)",
			By(
				regularOverS,
				vectors,
				subring,
				module.ModuleRestrictScalars.Read(target).At(S),
				scaledIn,
				scalarsAdd,
				vectorsAdd,
				scalarOnRing,
				scalarOnVector,
				module_homomorphism.BilinearMapOfClauses.At(subringS, regularR, V, N, rule)))
		h, lift := p.ObtainAs[Fun[_TensorV, C]](
			"the bilinear rule descends to the tensor quotient",
			"∃h:(set(prod(A, B) → A) → C). "+
				"    module_homomorphism(restrict_ring(R, S), «tensorS», N, h) ∧ "+
				"    (∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ h(«pureS»(a, v)) = «phi»(a, v))",
			Named("h"),
			By(bilinear, tensor_product.TensorUniversal.Read(regularOverS).At(V, N, rule)))
		liftParts := p.Conjuncts(
			lift,
			"h is S-linear on the tensor module",
			"h has the required values on pure tensors")
		linearOverS, pureFormula := liftParts[0], liftParts[1]
		p.Take(h)
		p.Show(
			"h is an R-linear extension with the prescribed pure values",
			SplitConj(
				Case(
					"h is R-linear",
					Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)),
					SplitConjAll(
						Case(
							"the source is an R-module",
							By(vectors, subring, ScalarExtensionOn.Read(R).At(S, V))),
						Case(
							"the target is the given R-module",
							By(target)),
						Case(
							"h preserves the carrier",
							Derive(func(q *Argument) {
								u := q.FixAs[_TensorV]("u")
								member := q.Assume()
								q.Show(
									"the S-linear lift already maps into N",
									By(member, module_homomorphism.HomIn.Read(linearOverS).AsFact().At(u)))
							})),
						Case(
							"h preserves tensor addition",
							Derive(func(q *Argument) {
								u, v := q.FixAs[_TensorV]("u"), q.FixAs[_TensorV]("v")
								members := q.Assume()
								q.Show(
									"the underlying addition is the tensor quotient addition",
									By(members, module_homomorphism.HomAdd.Read(linearOverS).AsFact().At(u, v)))
							})),
						Case(
							"h commutes with every scalar of R",
							Derive(func(q *Argument) {
								c, u := q.FixAs[A]("c"), q.FixAs[_TensorV]("u")
								members := q.Assume()
								scalingLinear := q.Have(
									"multiplication by c on N is S-linear: reading R as R restricted "+
										"to its own carrier, c is a scalar there and S a subring inside",
									"module_homomorphism(restrict_ring(R, S), N, N, λz:C. N.smul(c, z))",
									By(
										Normalized,
										comm_ring.SubringSubset.Read(subring),
										target,
										members,
										module_record.RestrictRingCarrier.At(ringOps),
										module_homomorphism.ScalingLinearOverSubring.At(ringOps, ringCarrier, S, N, c)))
								agree := q.Have(
									"h commutes with the ring action on pure tensors",
									Statement{
										Binders:    "∀b:A. ∀v:B.",
										Hypotheses: []string{"b ∈ R.carrier", "v ∈ V.carrier"},
										Conclusion: "h(«actionS»(c, «pureS»(b, v))) = N.smul(c, h(«pureS»(b, v)))",
									},
									Derive(func(r *Argument) {
										b, v := r.FixAs[A]("b"), r.FixAs[B]("v")
										pair := r.Assume()
										r.Show(
											"both values are scaling f(v) by the product c times b",
											By(
												vectors,
												pureFormula.At(b, v),
												pureFormula.At(r.TermAs[A]("c * b"), v),
												subring,
												pair,
												members,
												module_homomorphism.HomIn.Read(linear).AsFact().At(v),
												TensorScalarActionSpec.Read(R).AsFact().At(S, V, c),
												comm_ring.MulIn.Read(R).AsFact().At(c, b),
												module.SmulMul.Read(target).AsFact().At(c, b, f.Apply(v))))
									}))
								action := q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(c)")
								scaling := q.TermAs[Fun[C, C]]("λz:C. N.smul(c, z)")
								q.Show(
									"tensor uniqueness extends commutation to every tensor",
									By(
										vectors,
										agree,
										subring,
										members,
										scalingLinear,
										linearOverS,
										TensorScalarActionSpec.Read(R).AsFact().At(S, V, c),
										module_homomorphism.HomCompose.At(subringS, tensorS, tensorS, N, action, h),
										module_homomorphism.HomCompose.At(subringS, tensorS, N, N, h, scaling),
										functions.ComposeApply.At(h, action),
										functions.ComposeApply.At(scaling, h),
										ScalarExtensionHomUnique.Read(R).At(S, V, N,
											q.TermAs[Fun[_TensorV, C]]("λt:set(prod(A, B) → A). h(«actionS»(c, t))"),
											q.TermAs[Fun[_TensorV, C]]("λt:set(prod(A, B) → A). N.smul(c, h(t))"), u)))
							})))),
				Case(
					"h retains its pure-tensor formula",
					By(pureFormula))))
	}),
})}

// ScalarExtensionUnitLinear — sending v to 1 tensor v is S-linear into
// scalar extension: tensor additivity and balancing give its map laws.
var ScalarExtensionUnitLinear = scalarExtensionUnitLinearThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionUnitLinear",
	Key:  "prop_354b145ccd1815b2",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B).",
		Hypotheses: []string{"subring(R, S)", "module_on(restrict_ring(R, S), V)"},
		Conclusion: "module_homomorphism(restrict_ring(R, S), V, «extension», «unitS»)",
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"V is an S-module")
		subring, vectors := given[0], given[1]
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		regularR := p.TermAs[ModuleOps[A, A]]("regular_module(R)")
		one := p.TermAs[A]("R.one")
		regularOverS := p.Have(
			"R is an S-module under multiplication",
			"module_on(restrict_ring(R, S), regular_module(R))",
			By(subring, module.RegularModuleOverSubring.Read(R).At(S)))
		extended := p.Have(
			"scalar extension is an R-module",
			"module_on(R, «extension»)",
			By(subring, vectors, ScalarExtensionOn.Read(R).At(S, V)))
		p.Show(
			"the canonical unit preserves the carrier, sums and S-scalars",
			Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)),
			SplitConjAll(
				Case(
					"the source is the given S-module",
					By(vectors)),
				Case(
					"the target is an S-module by restriction",
					By(subring, module.ModuleRestrictScalars.Read(extended).At(S))),
				Case(
					"the unit lands in the scalar-extension carrier",
					Derive(func(q *Argument) {
						u := q.FixAs[B]("u")
						member := q.Assume()
						q.Show(
							"one and u give a pure tensor in the quotient",
							By(
								comm_ring.OneIn.Read(R),
								regularOverS,
								vectors,
								member,
								tensor_product.TensorIn.At(subringS, regularR, V, one, u),
								tensor_product.TensorProductDef.At(subringS, regularR, V)))
					})),
				Case(
					"the unit preserves addition",
					Derive(func(q *Argument) {
						u, v := q.FixAs[B]("u"), q.FixAs[B]("v")
						members := q.Assume()
						q.Show(
							"tensoring with one is additive in the vector coordinate",
							By(
								comm_ring.OneIn.Read(R),
								regularOverS,
								vectors,
								members,
								tensor_product.TensorAddRight.At(subringS, regularR, V, one, u, v)))
					})),
				Case(
					"the unit preserves S-scalars",
					Derive(func(q *Argument) {
						c, u := q.FixAs[A]("c"), q.FixAs[B]("u")
						members := q.Assume()
						q.Show(
							"balancing and the ring action give the same first coordinate",
							By(
								comm_ring.OneIn.Read(R),
								comm_ring.SubringSubset.Read(subring),
								regularOverS,
								vectors,
								members,
								set_basic.SubsetDef.At(S, q.TermAs[Set[A]]("R.carrier")),
								tensor_product.TensorBalance.At(subringS, regularR, V, c, one, u),
								TensorScalarActionSpec.Read(R).AsFact().At(S, V, c)))
					}))))
	}),
})}

// ScalarExtensionMapSpec — extending scalars makes an S-linear map R-linear
// and sends a pure tensor to the tensor of its image: compose with the
// target unit, lift R-linearly, then identify the canonical choice.
var ScalarExtensionMapSpec = scalarExtensionMapSpecThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapSpec",
	Key:  "prop_d538e0773223726e",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_homomorphism(restrict_ring(R, S), V, W, f)",
		},
		Conclusion: "module_homomorphism(R, «extension», «extensionW», «mapExtF») ∧ " +
			"(∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ «mapExtF»(«pureS»(a, v)) = «pureSW»(a, f(v)))",
		Abbrev: Abbrev{
			{Name: "unitW", Text: "λw:C. «pureSW»(R.one, w)"},
			{Name: "unitF", Text: "λv:B. «unitW»(f(v))"},
		},
	},
		func(
			p *Argument,
			R comm_ring.CommRingFact[on.R],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			W *Expr[ModuleOps[A, C]],
			f *Arrow[B, C],
			hypotheses Fact,
		) {
			given := p.Conjuncts(
				hypotheses,
				"S is a subring of R",
				"f is S-linear")
			subring, linear := given[0], given[1]
			images := module_homomorphism.HomTarget.Read(linear)
			products := comm_ring.MulMonoidOn.Read(R)
			subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
			target := p.TermAs[ModuleOps[A, _TensorW]]("«extensionW»")
			unitW := p.TermAs[Fun[C, _TensorW]]("«unitW»")
			unitF := p.TermAs[Fun[B, _TensorW]]("«unitF»")
			composite := p.Have(
				"composing f with the target unit is S-linear",
				"module_homomorphism(restrict_ring(R, S), V, «extensionW», «unitF»)",
				By(
					linear,
					images,
					subring,
					ScalarExtensionUnitLinear.Read(R).At(S, W),
					module_homomorphism.HomCompose.At(subringS, V, W, target, f, unitW),
					functions.ComposeApply.At(unitW, f)))
			possible := p.Have(
				"there is an R-linear map with the required values on pure tensors",
				"∃h:(set(prod(A, B) → A) → set(prod(A, C) → A)). "+
					"    module_homomorphism(R, «extension», «extensionW», h) ∧ "+
					"    (∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ h(«pureS»(a, v)) = «pureSW»(a, f(v)))",
				Derive(func(q *Argument) {
					h, lift := q.ObtainAs[Fun[_TensorV, _TensorW]](
						"the composite lifts R-linearly across the tensor quotient",
						"∃h:(set(prod(A, B) → A) → set(prod(A, C) → A)). "+
							"    module_homomorphism(R, «extension», «extensionW», h) ∧ "+
							"    (∀a:A. ∀v:B. "+
							"        a ∈ R.carrier ∧ v ∈ V.carrier ⇒ h(«pureS»(a, v)) = «extensionW».smul(a, «unitF»(v)))",
						Named("h"),
						By(
							subring,
							images,
							ScalarExtensionOn.Read(R).At(S, W),
							composite,
							ScalarExtensionLift.Read(R).At(S, V, target, unitF)))
					liftParts := q.Conjuncts(
						lift,
						"h is R-linear",
						"h scales the target unit images on pure tensors")
					q.Take(h)
					q.Show(
						"h has the R-linear specification",
						SplitConj(
							Case(
								"h is R-linear",
								By(liftParts[0])),
							Case(
								"h has the required pure-tensor formula",
								Derive(func(r *Argument) {
									a, v := r.FixAs[A]("a"), r.FixAs[B]("v")
									members := r.Assume()
									r.Show(
										"scaling the unit image multiplies its first coordinate by a",
										By(
											images,
											comm_ring.OneIn.Read(R),
											liftParts[1].At(a, v),
											subring,
											members,
											module_homomorphism.HomIn.Read(linear).AsFact().At(v),
											TensorScalarActionSpec.Read(R).AsFact().At(S, W, a),
											comm_monoid.RightIdentityOn.Read(products).AsFact().At(a)))
								}))))
				}))
			p.Show(
				"the canonical choice has the required linearity and pure-tensor formula",
				By(
					HilbertDenoted,
					possible,
					ScalarExtensionMapDef.At(subringS, p.TermAs[RingOps[A]]("R"), V, W, f)))
		}),
})}

// ScalarExtensionMapTensorLinear — an induced map is S-linear on the
// underlying tensor modules: its R-linearity restricts through the two
// coincident actions of every scalar in S.
var ScalarExtensionMapTensorLinear = scalarExtensionMapTensorLinearThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapTensorLinear",
	Key:  "prop_f699d91ab644fdf2",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B). ∀W:module_ops(A, C). ∀f:(B → C).",
		Hypotheses: []string{"subring(R, S)", "module_homomorphism(restrict_ring(R, S), V, W, f)"},
		Conclusion: "module_homomorphism(restrict_ring(R, S), «tensorS», «tensorSW», «mapExtF»)",
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"f is S-linear")
		subring, linear := given[0], given[1]
		vectors, images :=
			module_homomorphism.HomSource.Read(linear), module_homomorphism.HomTarget.Read(linear)
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		regularR := p.TermAs[ModuleOps[A, A]]("regular_module(R)")
		regularOverS := p.Have(
			"R is an S-module under multiplication",
			"module_on(restrict_ring(R, S), regular_module(R))",
			By(subring, module.RegularModuleOverSubring.Read(R).At(S)))
		extendedLinear := p.Have(
			"the induced map is R-linear",
			"module_homomorphism(R, «extension», «extensionW», «mapExtF»)",
			By(subring, linear, ScalarExtensionMapSpec.Read(R).At(S, V, W, f)))
		p.Show(
			"the map respects the underlying tensor-module structures",
			Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)),
			SplitConjAll(
				Case(
					"the source tensor quotient is an S-module",
					By(regularOverS, vectors, tensor_product.TensorModuleOn.At(subringS, regularR, V))),
				Case(
					"the target tensor quotient is an S-module",
					By(regularOverS, images, tensor_product.TensorModuleOn.At(subringS, regularR, W))),
				Case(
					"the image stays in the tensor carrier",
					Derive(func(q *Argument) {
						u := q.FixAs[_TensorV]("u")
						member := q.Assume()
						q.Show(
							"the R-linear map has the same carrier property",
							By(member, module_homomorphism.HomIn.Read(extendedLinear).AsFact().At(u)))
					})),
				Case(
					"tensor addition is preserved",
					Derive(func(q *Argument) {
						u, v := q.FixAs[_TensorV]("u"), q.FixAs[_TensorV]("v")
						members := q.Assume()
						q.Show(
							"the two records use the same addition",
							By(members, module_homomorphism.HomAdd.Read(extendedLinear).AsFact().At(u, v)))
					})),
				Case(
					"each S-scalar is preserved",
					Derive(func(q *Argument) {
						c, u := q.FixAs[A]("c"), q.FixAs[_TensorV]("u")
						members := q.Assume()
						inR := q.Have(
							"the S-scalar lies in R",
							"c ∈ R.carrier",
							By(
								members,
								comm_ring.SubringSubset.Read(subring),
								set_basic.SubsetDef.At(S, q.TermAs[Set[A]]("R.carrier"))))
						q.Show(
							"the coincident S-actions transport scalar compatibility",
							By(
								R,
								subring,
								vectors,
								images,
								inR,
								members,
								TensorScalarActionRestrict.Read(R).At(S, V, c, u),
								TensorScalarActionRestrict.Read(R).At(S, W, c, q.TermAs[_TensorW]("«mapExtF»(u)")),
								module_homomorphism.HomIn.Read(extendedLinear).AsFact().At(u),
								module_homomorphism.HomSmul.Read(extendedLinear).AsFact().At(c, u)))
					}))))
	}),
})}

// ScalarExtensionMapCompose — scalar extension preserves composition on
// the tensor carrier: the S-linear maps have the same pure-tensor values.
var ScalarExtensionMapCompose = scalarExtensionMapComposeThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapCompose",
	Key:  "prop_5b1524f427cf800",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀U:module_ops(A, D). " +
			"∀f:(B → C). " +
			"∀g:(C → D). " +
			"∀t:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_homomorphism(restrict_ring(R, S), V, W, f)",
			"module_homomorphism(restrict_ring(R, S), W, U, g)",
			"t ∈ «extension».carrier",
		},
		Conclusion: "«mapGF»(t) = «mapG»(«mapExtF»(t))",
		Abbrev: Abbrev{
			{Name: "tensorU", Text: "tensor_module(restrict_ring(R, S), regular_module(R), U)"},
			{Name: "composite", Text: "λv:B. g(f(v))"},
			{Name: "mapG", Text: "scalar_extension_map(restrict_ring(R, S), R, W, U, g)"},
			{Name: "mapGF", Text: "scalar_extension_map(restrict_ring(R, S), R, V, U, «composite»)"},
		},
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		U *Expr[ModuleOps[A, D]],
		f *Arrow[B, C],
		g *Arrow[C, D],
		t *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"f is S-linear",
			"g is S-linear",
			"t lies in the scalar-extension carrier")
		subring, linearF, linearG, member := given[0], given[1], given[2], given[3]
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		tensorS := p.TermAs[ModuleOps[A, _TensorV]]("«tensorS»")
		tensorSW := p.TermAs[ModuleOps[A, _TensorW]]("«tensorSW»")
		tensorU := p.TermAs[ModuleOps[A, _TensorU]]("«tensorU»")
		composite := p.TermAs[Fun[B, D]]("«composite»")
		compositeLinear := p.Have(
			"the composite is S-linear",
			"module_homomorphism(restrict_ring(R, S), V, U, «composite»)",
			By(
				Normalized,
				linearF,
				linearG,
				module_homomorphism.HomCompose.At(subringS, V, W, U, f, g),
				functions.ComposeApply.At(g, f)))
		agree := p.Have(
			"the induced composite and the composite induced map agree on pure tensors",
			Statement{
				Binders:    "∀a:A. ∀v:B.",
				Hypotheses: []string{"a ∈ R.carrier", "v ∈ V.carrier"},
				Conclusion: "«mapGF»(«pureS»(a, v)) = «mapG»(«mapExtF»(«pureS»(a, v)))",
			},
			Derive(func(q *Argument) {
				q.FixAs[A]("a")
				v := q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"both maps send the pure tensor to the tensor of the composite image",
					By(
						subring,
						linearF,
						linearG,
						compositeLinear,
						members,
						ScalarExtensionMapSpec.Read(R).At(S, V, W, f),
						ScalarExtensionMapSpec.Read(R).At(S, W, U, g),
						ScalarExtensionMapSpec.Read(R).At(S, V, U, composite),
						module_homomorphism.HomIn.Read(linearF).AsFact().At(v)))
			}))
		mapExtF := p.TermAs[Fun[_TensorV, _TensorW]]("«mapExtF»")
		mapG := p.TermAs[Fun[_TensorW, _TensorU]]("«mapG»")
		p.Show(
			"tensor uniqueness extends composition to the whole scalar-extension carrier",
			By(
				subring,
				linearF,
				linearG,
				compositeLinear,
				agree,
				p.Simplified(member, Fwd(ScalarExtensionCarrier)),
				ScalarExtensionMapTensorLinear.Read(R).At(S, V, W, f),
				ScalarExtensionMapTensorLinear.Read(R).At(S, W, U, g),
				ScalarExtensionMapTensorLinear.Read(R).At(S, V, U, composite),
				module_homomorphism.HomSource.Read(linearF),
				module_homomorphism.HomCompose.At(subringS, tensorS, tensorSW, tensorU, mapExtF, mapG),
				functions.ComposeApply.At(mapG, mapExtF),
				ScalarExtensionHomUnique.Read(R).At(S, V, tensorU,
					p.TermAs[Fun[_TensorV, _TensorU]]("«mapGF»"),
					p.TermAs[Fun[_TensorV, _TensorU]]("λu:set(prod(A, B) → A). «mapG»(«mapExtF»(u))"), t)))
	}),
})}

// ScalarExtensionMapCongruence — maps agreeing on the source carrier induce
// the same map after scalar extension: their values agree on pure tensors.
var ScalarExtensionMapCongruence = scalarExtensionMapCongruenceThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapCongruence",
	Key:  "prop_d5f73c4d5aaec20",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀f g:(B → C). " +
			"∀t:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_homomorphism(restrict_ring(R, S), V, W, f)",
			"∀v:B. v ∈ V.carrier ⇒ g(v) = f(v)",
			"t ∈ «extension».carrier",
		},
		Conclusion: "«mapExtG»(t) = «mapExtF»(t)",
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		f, g *Arrow[B, C],
		t *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"f is S-linear",
			"g agrees with f on V",
			"t lies in the scalar-extension carrier")
		subring, linearF, agreement, member := given[0], given[1], given[2], given[3]
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		tensorSW := p.TermAs[ModuleOps[A, _TensorW]]("«tensorSW»")
		mapExtF := p.TermAs[Fun[_TensorV, _TensorW]]("«mapExtF»")
		mapExtG := p.TermAs[Fun[_TensorV, _TensorW]]("«mapExtG»")
		linearG := p.Have(
			"g is S-linear because it agrees with f on V",
			"module_homomorphism(restrict_ring(R, S), V, W, g)",
			By(agreement, linearF, module_homomorphism.HomCongruence.At(subringS, V, W, f, g)))
		agree := p.Have(
			"the induced maps agree on pure tensors",
			"∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ «mapExtG»(«pureS»(a, v)) = «mapExtF»(«pureS»(a, v))",
			Derive(func(q *Argument) {
				q.FixAs[A]("a")
				v := q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"the pure-tensor formulas have equal second coordinates",
					By(
						agreement.At(v),
						subring,
						members,
						linearF,
						linearG,
						ScalarExtensionMapSpec.Read(R).At(S, V, W, g),
						ScalarExtensionMapSpec.Read(R).At(S, V, W, f)))
			}))
		p.Show(
			"tensor uniqueness extends agreement to the scalar-extension carrier",
			By(
				agree,
				p.Simplified(member, Fwd(ScalarExtensionCarrier)),
				subring,
				linearF,
				linearG,
				ScalarExtensionMapTensorLinear.Read(R).At(S, V, W, g),
				ScalarExtensionMapTensorLinear.Read(R).At(S, V, W, f),
				module_homomorphism.HomSource.Read(linearF),
				ScalarExtensionHomUnique.Read(R).At(S, V, tensorSW, mapExtG, mapExtF, t)))
	}),
})}

// ScalarExtensionMapIdentity — the induced identity fixes every vector after
// scalar extension: uniqueness extends agreement on pure tensors.
var ScalarExtensionMapIdentity = scalarExtensionMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapIdentity",
	Key:  "prop_4a42e76de18691e6",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B). ∀t:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_on(restrict_ring(R, S), V)",
			"t ∈ «extension».carrier",
		},
		Conclusion: "«mapId»(t) = t",
		Abbrev: Abbrev{
			{Name: "mapId", Text: "scalar_extension_map(restrict_ring(R, S), R, V, V, identity_map)"},
		},
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		t *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"V is an S-module",
			"t lies in the scalar-extension carrier")
		subring, vectors, member := given[0], given[1], given[2]
		tensorS := p.TermAs[ModuleOps[A, _TensorV]]("«tensorS»")
		identity := p.TermAs[Fun[B, B]]("identity_map")
		mapId := p.TermAs[Fun[_TensorV, _TensorV]]("«mapId»")
		tensorIdentity := p.TermAs[Fun[_TensorV, _TensorV]]("identity_map")
		inducedLinear := p.Have(
			"the induced identity is S-linear on the tensor module",
			"module_homomorphism(restrict_ring(R, S), «tensorS», «tensorS», «mapId»)",
			By(
				module_homomorphism.HomIdentity.Read(vectors),
				subring,
				ScalarExtensionMapTensorLinear.Read(R).At(S, V, V, identity)))
		agree := p.Have(
			"the induced map agrees with the tensor identity on pure tensors",
			"∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ «mapId»(«pureS»(a, v)) = identity_map(«pureS»(a, v))",
			Derive(func(q *Argument) {
				q.FixAs[A]("a")
				q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"both maps fix the two coordinates of the pure tensor",
					By(
						module_homomorphism.HomIdentity.Read(vectors),
						subring,
						members,
						ScalarExtensionMapSpec.Read(R).At(S, V, V, identity),
						functions.IdentityApply.Inst[B](),
						functions.IdentityApply.Inst[_TensorV]()))
			}))
		p.Show(
			"tensor uniqueness identifies the induced map with the identity on the carrier",
			By(
				module_homomorphism.HomIdentity.Read(module_homomorphism.HomSource.Read(inducedLinear)),
				agree,
				subring,
				vectors,
				p.Simplified(member, Fwd(ScalarExtensionCarrier)),
				functions.IdentityApply.Inst[_TensorV](),
				ScalarExtensionHomUnique.Read(R).At(S, V, tensorS, mapId, tensorIdentity, t)))
	}),
})}

// ScalarExtensionMapAdd — extending a pointwise sum of S-linear maps gives
// the sum of the induced maps: the tensor is additive in its vector
// coordinate, so the two maps agree on pure tensors.
var ScalarExtensionMapAdd = scalarExtensionMapAddThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapAdd",
	Key:  "prop_1b873d05be1b5256",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀f g:(B → C). " +
			"∀t:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_homomorphism(restrict_ring(R, S), V, W, f)",
			"module_homomorphism(restrict_ring(R, S), V, W, g)",
			"t ∈ «extension».carrier",
		},
		Conclusion: "«mapSum»(t) = «extensionW».add(«mapExtF»(t), «mapExtG»(t))",
		Abbrev: Abbrev{
			{Name: "sum", Text: "λv:B. W.add(f(v), g(v))"},
			{Name: "mapSum", Text: "scalar_extension_map(restrict_ring(R, S), R, V, W, «sum»)"},
			{Name: "rightMap", Text: "λu:set(prod(A, B) → A). «tensorSW».add(«mapExtF»(u), «mapExtG»(u))"},
		},
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		f, g *Arrow[B, C],
		t *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"f is S-linear",
			"g is S-linear",
			"t lies in the scalar-extension carrier")
		subring, linearF, linearG, member := given[0], given[1], given[2], given[3]
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		regularR := p.TermAs[ModuleOps[A, A]]("regular_module(R)")
		tensorS := p.TermAs[ModuleOps[A, _TensorV]]("«tensorS»")
		tensorSW := p.TermAs[ModuleOps[A, _TensorW]]("«tensorSW»")
		mapExtF := p.TermAs[Fun[_TensorV, _TensorW]]("«mapExtF»")
		mapExtG := p.TermAs[Fun[_TensorV, _TensorW]]("«mapExtG»")
		sum := p.TermAs[Fun[B, C]]("«sum»")
		images := module_homomorphism.HomTarget.Read(linearF)
		sumLinear := p.Have(
			"the pointwise sum of the base maps is S-linear",
			"module_homomorphism(restrict_ring(R, S), V, W, «sum»)",
			By(linearF, linearG, module_homomorphism.HomPointwiseSum.At(subringS, V, W, f, g)))
		rightLinear := p.Have(
			"the pointwise sum of the induced maps is S-linear on the tensor modules",
			"module_homomorphism(restrict_ring(R, S), «tensorS», «tensorSW», «rightMap»)",
			By(
				subring,
				linearF,
				linearG,
				ScalarExtensionMapTensorLinear.Read(R).At(S, V, W, f),
				ScalarExtensionMapTensorLinear.Read(R).At(S, V, W, g),
				module_homomorphism.HomPointwiseSum.At(subringS, tensorS, tensorSW, mapExtF, mapExtG)))
		agree := p.Have(
			"the induced sum agrees with the sum of the induced maps on pure tensors",
			"∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ «mapSum»(«pureS»(a, v)) = «rightMap»(«pureS»(a, v))",
			Derive(func(q *Argument) {
				a, v := q.FixAs[A]("a"), q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"the sum map acts on the vector coordinate, where the tensor is additive",
					CalcEq(
						Leg(
							q.TermAs[_TensorW]("«pureSW»(a, W.add(f(v), g(v)))"),
							"the induced sum sends a ⊗ v to a ⊗ (f(v) + g(v))",
							By(subring, members, sumLinear, ScalarExtensionMapSpec.Read(R).At(S, V, W, sum))),
						Leg(
							q.TermAs[_TensorW]("«tensorSW».add(«pureSW»(a, f(v)), «pureSW»(a, g(v)))"),
							"the tensor is additive in its vector coordinate",
							By(
								images,
								subring,
								module.RegularModuleOverSubring.Read(R).At(S),
								members,
								module_homomorphism.HomIn.Read(linearF).AsFact().At(v),
								module_homomorphism.HomIn.Read(linearG).AsFact().At(v),
								tensor_product.TensorAddRight.At(subringS, regularR, W, a, f.Apply(v), g.Apply(v)))),
						FinalLeg(
							"the induced maps send a ⊗ v to a ⊗ f(v) and a ⊗ g(v)",
							By(
								subring,
								members,
								linearF,
								linearG,
								ScalarExtensionMapSpec.Read(R).At(S, V, W, f),
								ScalarExtensionMapSpec.Read(R).At(S, V, W, g)))))
			}))
		p.Show(
			"the two S-linear maps agree on the scalar-extension carrier",
			Simp(Fwd(ScalarExtensionAdd), Fwd(tensor_product.TensorModuleAdd)),
			By(
				module_homomorphism.HomSource.Read(linearF),
				p.Simplified(agree, Fwd(tensor_product.TensorModuleAdd)),
				p.Simplified(member, Fwd(ScalarExtensionCarrier)),
				subring,
				sumLinear,
				p.Simplified(rightLinear, Fwd(tensor_product.TensorModuleAdd)),
				ScalarExtensionMapTensorLinear.Read(R).At(S, V, W, sum),
				ScalarExtensionHomUnique.Read(R).At(S, V, tensorSW,
					p.TermAs[Fun[_TensorV, _TensorW]]("«mapSum»"),
					p.TermAs[Fun[_TensorV, _TensorW]]("«rightMap»"), t)))
	}),
})}

// ScalarExtensionMapZero — extending the zero map gives zero: the zero map
// is its own pointwise double, so its extension is its own double in the
// additive group of scalar extension.
var ScalarExtensionMapZero = scalarExtensionMapZeroThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapZero",
	Key:  "prop_30deabce3390c573",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀t:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_on(restrict_ring(R, S), V)",
			"module_on(restrict_ring(R, S), W)",
			"t ∈ «extension».carrier",
		},
		Conclusion: "«mapZero»(t) = «extensionW».zero",
		Abbrev: Abbrev{
			{Name: "zeroMap", Text: "λv:B. W.zero"},
			{Name: "mapZero", Text: "scalar_extension_map(restrict_ring(R, S), R, V, W, «zeroMap»)"},
		},
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		t *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"V is an S-module",
			"W is an S-module",
			"t lies in the scalar-extension carrier")
		subring, vectors, images, member := given[0], given[1], given[2], given[3]
		zeroMap := p.TermAs[Fun[B, C]]("«zeroMap»")
		additiveW := module.AddGroupOn.Read(images)
		zeroLinear := p.Have(
			"the zero map is S-linear",
			"module_homomorphism(restrict_ring(R, S), V, W, «zeroMap»)",
			Simp(Fwd(module_homomorphism.ModuleHomomorphismDef)),
			ByChase(Depth(0), vectors, images))
		extendedLinear := p.Have(
			"the induced zero map is R-linear",
			"module_homomorphism(R, «extension», «extensionW», «mapZero»)",
			By(subring, zeroLinear, ScalarExtensionMapSpec.Read(R).At(S, V, W, zeroMap)))
		additive := module.AddGroupOn.Read(module_homomorphism.HomTarget.Read(extendedLinear))
		doubled := p.Have(
			"the induced zero map is its own double",
			"«extensionW».add(«mapZero»(t), «mapZero»(t)) = «mapZero»(t)",
			Simp(Fwd(ScalarExtensionAdd), Fwd(tensor_product.TensorModuleAdd)),
			By(
				subring,
				member,
				zeroLinear,
				group.OneIn.Read(additiveW),
				group.RightIdentityOn.Read(additiveW).AsFact().At(p.TermAs[C]("W.zero")),
				ScalarExtensionMapAdd.Read(R).At(S, V, W, zeroMap, zeroMap, t),
				ScalarExtensionMapCongruence.Read(R).At(
					S, V, W, zeroMap, p.TermAs[Fun[B, C]]("λv:B. W.add(W.zero, W.zero)"), t)))
		p.Show(
			"an element of the additive group equal to its double is zero",
			By(
				doubled,
				member,
				module_homomorphism.HomIn.Read(extendedLinear).AsFact().At(t),
				group.IdempotentIsOneOn.Read(additive).AsFact().At(p.TermAs[_TensorW]("«mapZero»(t)"))))
	}),
})}

// ScalarExtensionMapInverse — a left inverse extends: the extension of a left
// inverse of f undoes the extension of f, since the composite of the extensions
// extends the composite on V, which agrees with the identity.
var ScalarExtensionMapInverse = scalarExtensionMapInverseThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapInverse",
	Key:  "prop_ccb850d777eb88d8",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀g:(C → B). " +
			"∀x:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_homomorphism(restrict_ring(R, S), V, W, f)",
			"module_homomorphism(restrict_ring(R, S), W, V, g)",
			"∀v:B. v ∈ V.carrier ⇒ g(f(v)) = v",
			"x ∈ «extension».carrier",
		},
		Conclusion: "scalar_extension_map(restrict_ring(R, S), R, W, V, g)(«mapExtF»(x)) = x",
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		g *Arrow[C, B],
		x *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"f is S-linear",
			"g is S-linear",
			"g undoes f on V",
			"x lies in the scalar-extension carrier")
		subring, linearF, linearG, undoes, member := given[0], given[1], given[2], given[3], given[4]
		vectors := module_homomorphism.HomSource.Read(linearF)
		agreement := p.Have(
			"g ∘ f agrees with the identity on V",
			"∀v:B. v ∈ V.carrier ⇒ g(f(v)) = identity_map(v)",
			Simp(Fwd(functions.IdentityApply)),
			By(undoes))
		p.Show(
			"the composite of the extensions extends g ∘ f, which is the identity on V",
			By(
				vectors,
				module_homomorphism.HomIdentity.Read(vectors),
				agreement,
				member,
				subring,
				linearF,
				linearG,
				ScalarExtensionMapCompose.Read(R).At(S, V, W, V, f, g, x),
				ScalarExtensionMapCongruence.Read(R).At(
					S, V, V, p.TermAs[Fun[B, B]]("identity_map"), p.TermAs[Fun[B, B]]("λv:B. g(f(v))"), x),
				ScalarExtensionMapIdentity.Read(R).At(S, V, x)))
	}),
})}

// ScalarExtensionMapComplement — maps summing to the identity on V extend to
// maps summing to the identity on the extension, since the sum of the
// extensions extends the pointwise sum, which agrees with the identity.
var ScalarExtensionMapComplement = scalarExtensionMapComplementThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapComplement",
	Key:  "prop_87d08de798333201",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀r c:(B → B). " +
			"∀x:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_homomorphism(restrict_ring(R, S), V, V, r)",
			"module_homomorphism(restrict_ring(R, S), V, V, c)",
			"∀v:B. v ∈ V.carrier ⇒ V.add(r(v), c(v)) = v",
			"x ∈ «extension».carrier",
		},
		Conclusion: "«extension».add(scalar_extension_map(restrict_ring(R, S), R, V, V, r)(x), " +
			"    scalar_extension_map(restrict_ring(R, S), R, V, V, c)(x)) = " +
			"x",
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		r, c *Arrow[B, B],
		x *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"r is S-linear",
			"c is S-linear",
			"r and c sum to the identity on V",
			"x lies in the scalar-extension carrier")
		subring, linearR, linearC, sum, member := given[0], given[1], given[2], given[3], given[4]
		vectors := module_homomorphism.HomSource.Read(linearR)
		agreement := p.Have(
			"r + c agrees with the identity on V",
			"∀v:B. v ∈ V.carrier ⇒ V.add(r(v), c(v)) = identity_map(v)",
			Simp(Fwd(functions.IdentityApply)),
			By(sum))
		p.Show(
			"the sum of the extensions extends r + c, which is the identity on V",
			Simp(Fwd(ScalarExtensionAdd)),
			By(
				vectors,
				module_homomorphism.HomIdentity.Read(vectors),
				agreement,
				member,
				subring,
				linearR,
				linearC,
				ScalarExtensionMapAdd.Read(R).At(S, V, V, r, c, x),
				ScalarExtensionMapCongruence.Read(R).At(
					S, V, V, p.TermAs[Fun[B, B]]("identity_map"), p.TermAs[Fun[B, B]]("λv:B. V.add(r(v), c(v))"), x),
				ScalarExtensionMapIdentity.Read(R).At(S, V, x)))
	}),
})}

// ScalarExtensionMapVanishes — an S-linear map vanishing on V extends to zero:
// it agrees with the zero map, whose extension is zero.
var ScalarExtensionMapVanishes = scalarExtensionMapVanishesThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionMapVanishes",
	Key:  "prop_ae83cdadd3d7019b",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀W:module_ops(A, C). " +
			"∀f:(B → C). " +
			"∀x:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_homomorphism(restrict_ring(R, S), V, W, f)",
			"∀v:B. v ∈ V.carrier ⇒ f(v) = W.zero",
			"x ∈ «extension».carrier",
		},
		Conclusion: "«mapExtF»(x) = «extensionW».zero",
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		W *Expr[ModuleOps[A, C]],
		f *Arrow[B, C],
		x *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"f is S-linear",
			"f vanishes on V",
			"x lies in the scalar-extension carrier")
		subring, linear, vanishes, member := given[0], given[1], given[2], given[3]
		p.Show(
			"f agrees with the zero map, which extends to zero",
			Simp(Fwd(ScalarExtensionZero), Fwd(tensor_product.TensorModuleZero)),
			By(
				vanishes,
				member,
				subring,
				linear,
				module_homomorphism.HomSource.Read(linear),
				module_homomorphism.HomTarget.Read(linear),
				ScalarExtensionMapCongruence.Read(R).At(S, V, W, f, p.TermAs[Fun[B, C]]("λv:B. W.zero"), x),
				ScalarExtensionMapZero.Read(R).At(S, V, W, x)))
	}),
})}
