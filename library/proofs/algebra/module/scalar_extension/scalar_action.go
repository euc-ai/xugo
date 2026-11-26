// scalar_action.go — multiplication on the ring factor descends to the
// tensor quotient and makes scalar extension a module over the ring.

package scalar_extension

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// _TensorV, _TensorW and _TensorU are the types of the points of the tensor
// modules of V, W and U, and _TensorCokernel of the quotient of W: each point a
// coset, modulo the tensor relations, of finitely supported coefficient
// functions on pairs.
type (
	_TensorV        = Set[Fun[Prod[A, B], A]]
	_TensorW        = Set[Fun[Prod[A, C], A]]
	_TensorU        = Set[Fun[Prod[A, D], A]]
	_TensorCokernel = Set[Fun[Prod[A, Set[C]], A]]
)

// TensorScalarActionSpec — a ring scalar acts S-linearly on the tensor
// product, multiplying its first coordinate: that rule is bilinear,
// so the universal property supplies the map chosen by the definition.
var TensorScalarActionSpec = tensorScalarActionSpecThm{family.Add(registry.ProofEntry{
	Name: "TensorScalarActionSpec",
	Key:  "prop_bb46dfd4ab6d3150",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B). ∀a:A.",
		Hypotheses: []string{
			"subring(R, S)",
			"module_on(restrict_ring(R, S), V)",
			"a ∈ R.carrier",
		},
		Conclusion: "module_homomorphism(restrict_ring(R, S), «tensorS», «tensorS», «actionS»(a)) ∧ " +
			"(∀b:A. ∀v:B. b ∈ R.carrier ∧ v ∈ V.carrier ⇒ «actionS»(a, «pureS»(b, v)) = «pureS»(a * b, v))",
	},
		func(
			p *Argument,
			R comm_ring.CommRingFact[on.R],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			a *Member[A, on.R],
			hypotheses Fact,
		) {
			given := p.Conjuncts(
				hypotheses,
				"S is a subring of R",
				"V is an S-module")
			subring, vectors := given[0], given[1]
			products := comm_ring.MulMonoidOn.Read(R)
			subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
			ringOps := p.TermAs[RingOps[A]]("R")
			regularR := p.TermAs[ModuleOps[A, A]]("regular_module(R)")
			tensorS := p.TermAs[ModuleOps[A, _TensorV]]("«tensorS»")
			regularOverS := p.Have(
				"R is an S-module under multiplication",
				"module_on(restrict_ring(R, S), regular_module(R))",
				By(subring, module.RegularModuleOverSubring.Read(R).At(S)))
			possible := p.Have(
				"multiplication on the first factor descends to an S-linear endomorphism",
				"∃h:(set(prod(A, B) → A) → set(prod(A, B) → A)). "+
					"    module_homomorphism(restrict_ring(R, S), «tensorS», «tensorS», h) ∧ "+
					"    (∀b:A. ∀v:B. b ∈ R.carrier ∧ v ∈ V.carrier ⇒ h(«pureS»(b, v)) = «pureS»(a * b, v))",
				Derive(func(q *Argument) {
					multipliedIn := q.Have(
						"the multiplied coordinate still lies in R",
						"∀b:A. ∀v:B. b ∈ R.carrier ∧ v ∈ V.carrier ⇒ «pureS»(a * b, v) ∈ «tensorS».carrier",
						Derive(func(r *Argument) {
							b, v := r.FixAs[A]("b"), r.FixAs[B]("v")
							members := r.Assume()
							r.Show(
								"a product in R and a vector of V give a pure tensor",
								Simp(Fwd(tensor_product.TensorModuleCarrier)),
								By(
									regularOverS,
									vectors,
									a,
									members,
									comm_ring.MulIn.Read(R).AsFact().At(a, b),
									tensor_product.TensorIn.At(subringS, regularR, V, r.TermAs[A]("a * b"), v)))
						}))
					scalarsAdd := q.Have(
						"a distributes over a sum in the first coordinate",
						Statement{
							Binders:    "∀b b':A. ∀v:B.",
							Hypotheses: []string{"b ∈ R.carrier", "b' ∈ R.carrier", "v ∈ V.carrier"},
							Conclusion: "«pureS»(a * (b + b'), v) = «tensorS».add(«pureS»(a * b, v), «pureS»(a * b', v))",
						},
						Derive(func(r *Argument) {
							b, bp, v := r.FixAs[A]("b"), r.FixAs[A]("b'"), r.FixAs[B]("v")
							members := r.Assume()
							r.Show(
								"distribution in R followed by additivity of the tensor",
								Simp(Fwd(comm_ring.LeftDistribOn.Read(R))),
								By(
									regularOverS,
									vectors,
									a,
									members,
									comm_ring.MulIn.Read(R).AsFact().At(a, b),
									comm_ring.MulIn.Read(R).AsFact().At(a, bp),
									tensor_product.TensorAddLeft.At(
										subringS, regularR, V, r.TermAs[A]("a * b"), r.TermAs[A]("a * b'"), v)))
						}))
					vectorsAdd := q.Have(
						"the second coordinate remains additive",
						Statement{
							Binders:    "∀b:A. ∀v v':B.",
							Hypotheses: []string{"b ∈ R.carrier", "v ∈ V.carrier", "v' ∈ V.carrier"},
							Conclusion: "«pureS»(a * b, V.add(v, v')) = «tensorS».add(«pureS»(a * b, v), «pureS»(a * b, v'))",
						},
						Derive(func(r *Argument) {
							b, v, vp := r.FixAs[A]("b"), r.FixAs[B]("v"), r.FixAs[B]("v'")
							members := r.Assume()
							r.Show(
								"the tensor is additive in its second coordinate",
								By(
									regularOverS,
									vectors,
									a,
									members,
									comm_ring.MulIn.Read(R).AsFact().At(a, b),
									tensor_product.TensorAddRight.At(subringS, regularR, V, r.TermAs[A]("a * b"), v, vp)))
						}))
					scalarOnRing := q.Have(
						"a commutes with an S-scalar in the first coordinate",
						Statement{
							Binders:    "∀c b:A. ∀v:B.",
							Hypotheses: []string{"c ∈ S", "b ∈ R.carrier", "v ∈ V.carrier"},
							Conclusion: "«pureS»(a * (c * b), v) = «tensorS».smul(c, «pureS»(a * b, v))",
						},
						Derive(func(r *Argument) {
							c, b, v := r.FixAs[A]("c"), r.FixAs[A]("b"), r.FixAs[B]("v")
							members := r.Assume()
							commuted := r.Have(
								"R is commutative, so a * (c * b) is c * (a * b)",
								"a * (c * b) = c * (a * b)",
								By(
									comm_ring.SubringSubset.Read(subring),
									a,
									members,
									set_basic.SubsetDef.At(S, r.TermAs[Set[A]]("R.carrier")),
									comm_monoid.LeftCommOn.Read(products).AsFact().At(a, c, b)))
							r.Show(
								"c scales the tensor at a * b",
								commuted.Rw(),
								By(
									regularOverS,
									vectors,
									a,
									members,
									comm_ring.MulIn.Read(R).AsFact().At(a, b),
									tensor_product.TensorSmulLeft.At(subringS, regularR, V, c, r.TermAs[A]("a * b"), v)))
						}))
					scalarOnVector := q.Have(
						"an S-scalar in the second coordinate scales the tensor",
						Statement{
							Binders:    "∀c b:A. ∀v:B.",
							Hypotheses: []string{"c ∈ S", "b ∈ R.carrier", "v ∈ V.carrier"},
							Conclusion: "«pureS»(a * b, V.smul(c, v)) = «tensorS».smul(c, «pureS»(a * b, v))",
						},
						Derive(func(r *Argument) {
							c, b, v := r.FixAs[A]("c"), r.FixAs[A]("b"), r.FixAs[B]("v")
							members := r.Assume()
							r.Show(
								"a scalar on the second coordinate scales the tensor",
								By(
									regularOverS,
									vectors,
									a,
									members,
									comm_ring.MulIn.Read(R).AsFact().At(a, b),
									tensor_product.TensorSmulRightFactor.At(subringS, regularR, V, c, r.TermAs[A]("a * b"), v)))
						}))
					rule := q.TermAs[Fun2[A, B, _TensorV]]("λb:A. λv:B. «pureS»(a * b, v)")
					bilinear := q.Have(
						"multiplication on the first coordinate is bilinear over S",
						"bilinear_map(restrict_ring(R, S), regular_module(R), V, «tensorS», λb:A. λv:B. «pureS»(a * b, v))",
						By(
							regularOverS,
							vectors,
							tensor_product.TensorModuleOn.At(subringS, regularR, V),
							multipliedIn,
							scalarsAdd,
							vectorsAdd,
							scalarOnRing,
							scalarOnVector,
							module_homomorphism.BilinearMapOfClauses.At(subringS, regularR, V, tensorS, rule)))
					q.Show(
						"the bilinear map induces a homomorphism out of the tensor product",
						By(bilinear, tensor_product.TensorUniversal.Read(regularOverS).At(V, tensorS, rule)))
				}))
			p.Show(
				"the defining choice selects a homomorphism with this action on pure tensors",
				By(HilbertDenoted, possible, tensorScalarActionDef.At(subringS, ringOps, V, a)))
		}),
})}

// ScalarExtensionCarrier — the scalar extension has the points of the
// tensor module it is built on.
var ScalarExtensionCarrier = scalarExtensionCarrierThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionCarrier",
	Key:  "prop_808e73251d2d134e",
	Build: family.Theorem(Statement{
		Binders:    "∀S R:ring_ops(A). ∀V:module_ops(A, B).",
		Conclusion: "scalar_extension(S, R, V).carrier = tensor_module(S, regular_module(R), V).carrier",
	},
		func(a *Argument, S, R *Expr[RingOps[A]], V *Expr[ModuleOps[A, B]]) {
			a.Show(
				"the extension's record is packed from the tensor module's carrier",
				Simp(Fwd(ScalarExtensionDef)),
				Basic())
		}),
})}

// ScalarExtensionAdd — the scalar extension adds as the tensor module does.
var ScalarExtensionAdd = scalarExtensionAddThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionAdd",
	Key:  "prop_c1f89ed25a0e19c4",
	Build: family.Theorem(Statement{
		Binders:    "∀S R:ring_ops(A). ∀V:module_ops(A, B).",
		Conclusion: "scalar_extension(S, R, V).add = tensor_module(S, regular_module(R), V).add",
	},
		func(a *Argument, S, R *Expr[RingOps[A]], V *Expr[ModuleOps[A, B]]) {
			a.Show(
				"the extension's record is packed from the tensor module's addition",
				Simp(Fwd(ScalarExtensionDef)),
				Basic())
		}),
})}

// ScalarExtensionZero — the zero of the scalar extension is the tensor
// module's.
var ScalarExtensionZero = scalarExtensionZeroThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionZero",
	Key:  "prop_3ff5ffe9bc395073",
	Build: family.Theorem(Statement{
		Binders:    "∀S R:ring_ops(A). ∀V:module_ops(A, B).",
		Conclusion: "scalar_extension(S, R, V).zero = tensor_module(S, regular_module(R), V).zero",
	},
		func(a *Argument, S, R *Expr[RingOps[A]], V *Expr[ModuleOps[A, B]]) {
			a.Show(
				"the extension's record is packed from the tensor module's zero",
				Simp(Fwd(ScalarExtensionDef)),
				Basic())
		}),
})}

// ScalarExtensionSmul — the scalars of the extension act by the chosen
// action on the first coordinate.
var ScalarExtensionSmul = scalarExtensionSmulThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionSmul",
	Key:  "prop_f3c454d03e878a9b",
	Build: family.Theorem(Statement{
		Binders:    "∀S R:ring_ops(A). ∀V:module_ops(A, B).",
		Conclusion: "scalar_extension(S, R, V).smul = tensor_scalar_action(S, R, V)",
	},
		func(a *Argument, S, R *Expr[RingOps[A]], V *Expr[ModuleOps[A, B]]) {
			a.Show(
				"the extension's record is packed from the chosen action",
				Simp(Fwd(ScalarExtensionDef)),
				Basic())
		}),
})}

// ScalarExtensionHomUnique — two S-linear maps out of the tensor module
// «tensorS», not out of the extension's record, agreeing on pure tensors agree
// at every point of scalar extension: such a point lies in the tensor product,
// where uniqueness of maps agreeing on pure tensors is cited.
var ScalarExtensionHomUnique = scalarExtensionHomUniqueThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionHomUnique",
	Key:  "prop_7b158d5076dbfe92",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀m n:(set(prod(A, B) → A) → C). " +
			"∀t:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_on(restrict_ring(R, S), V)",
			"module_homomorphism(restrict_ring(R, S), «tensorS», N, m)",
			"module_homomorphism(restrict_ring(R, S), «tensorS», N, n)",
			"∀a:A. ∀v:B. a ∈ R.carrier ∧ v ∈ V.carrier ⇒ m(«pureS»(a, v)) = n(«pureS»(a, v))",
			"t ∈ «extension».carrier",
		},
		Conclusion: "m(t) = n(t)",
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		N *Expr[ModuleOps[A, C]],
		m, n *Arrow[_TensorV, C],
		t *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"V is an S-module",
			"m is S-linear",
			"n is S-linear",
			"m and n agree on pure tensors",
			"t lies in the scalar-extension carrier")
		subring, vectors, linearM, linearN, agree, member :=
			given[0], given[1], given[2], given[3], given[4], given[5]
		regularOverS := p.Have(
			"R is an S-module under multiplication",
			"module_on(restrict_ring(R, S), regular_module(R))",
			By(subring, module.RegularModuleOverSubring.Read(R).At(S)))
		p.Show(
			"uniqueness on the tensor product extends the agreement to the carrier",
			By(
				vectors,
				linearM,
				linearN,
				agree,
				p.Simplified(member, Fwd(ScalarExtensionCarrier), Fwd(tensor_product.TensorModuleCarrier)),
				tensor_product.TensorUniversalUnique.Read(regularOverS).At(V, N, m, n, t)))
	}),
})}

// TensorScalarActionRestrict — a scalar in S acts by the original tensor
// module scaling: the two S-linear maps agree on pure tensors.
var TensorScalarActionRestrict = tensorScalarActionRestrictThm{family.Add(registry.ProofEntry{
	Name: "TensorScalarActionRestrict",
	Key:  "prop_393b4e1d44976a06",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B). ∀c:A. ∀t:set(prod(A, B) → A).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_on(restrict_ring(R, S), V)",
			"c ∈ S",
			"t ∈ «tensorS».carrier",
		},
		Conclusion: "«actionS»(c, t) = «tensorS».smul(c, t)",
	}, func(
		p *Argument,
		R comm_ring.CommRingFact[on.R],
		S *Expr[Set[A]],
		V *Expr[ModuleOps[A, B]],
		c *Expr[A],
		t *Expr[_TensorV],
		hypotheses Fact,
	) {
		given := p.Conjuncts(
			hypotheses,
			"S is a subring",
			"V is an S-module",
			"c lies in S",
			"t lies in the tensor module")
		subring, vectors, inS, member := given[0], given[1], given[2], given[3]
		subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
		regularR := p.TermAs[ModuleOps[A, A]]("regular_module(R)")
		tensorS := p.TermAs[ModuleOps[A, _TensorV]]("«tensorS»")
		regularOverS := p.Have(
			"R is an S-module under multiplication",
			"module_on(restrict_ring(R, S), regular_module(R))",
			By(subring, module.RegularModuleOverSubring.Read(R).At(S)))
		tensorModule := p.Have(
			"the tensor quotient is an S-module",
			"module_on(restrict_ring(R, S), «tensorS»)",
			By(regularOverS, vectors, tensor_product.TensorModuleOn.At(subringS, regularR, V)))
		inR := p.Have(
			"the base scalar also lies in R",
			"c ∈ R.carrier",
			By(
				comm_ring.SubringSubset.Read(subring),
				inS,
				set_basic.SubsetDef.At(S, p.TermAs[Set[A]]("R.carrier"))))
		tensorModuleLinear := p.Have(
			"multiplication by c is an S-linear tensor endomorphism",
			"module_homomorphism(restrict_ring(R, S), "+
				"    «tensorS», "+
				"    «tensorS», "+
				"    λu:set(prod(A, B) → A). «tensorS».smul(c, u))",
			Simp(Fwd(tensor_product.TensorModuleSmul)),
			By(
				inS,
				module_homomorphism.HomScalarMultiple.Read(
					module_homomorphism.HomIdentity.Read(tensorModule)).AsFact().At(
					c),
				functions.IdentityApply))
		action := p.Have(
			"the chosen action is S-linear and multiplies the first coordinate",
			"module_homomorphism(restrict_ring(R, S), «tensorS», «tensorS», «actionS»(c)) ∧ "+
				"(∀b:A. ∀v:B. b ∈ R.carrier ∧ v ∈ V.carrier ⇒ «actionS»(c, «pureS»(b, v)) = «pureS»(c * b, v))",
			By(subring, vectors, inR, TensorScalarActionSpec.Read(R).AsFact().At(S, V, c)))
		parts := p.Conjuncts(
			action,
			"the action is S-linear",
			"the action formula holds on pure tensors")
		actionLinear, actionFormula := parts[0], parts[1]
		agree := p.Have(
			"both scalar maps agree on pure tensors",
			Statement{
				Binders:    "∀b:A. ∀v:B.",
				Hypotheses: []string{"b ∈ R.carrier", "v ∈ V.carrier"},
				Conclusion: "«actionS»(c, «pureS»(b, v)) = «tensorS».smul(c, «pureS»(b, v))",
			},
			Derive(func(q *Argument) {
				b, v := q.FixAs[A]("b"), q.FixAs[B]("v")
				members := q.Assume()
				q.Show(
					"multiplication in the ring coordinate is the tensor scaling relation",
					CalcEq(
						Leg(
							q.TermAs[_TensorV]("«pureS»(c * b, v)"),
							"the chosen action multiplies the ring coordinate",
							By(members, actionFormula.At(b, v))),
						FinalLeg(
							"c scales the tensor at b",
							By(
								regularOverS,
								vectors,
								inS,
								members,
								tensor_product.TensorSmulLeft.At(subringS, regularR, V, c, b, v)))))
			}))
		p.Show(
			"tensor uniqueness identifies the two actions on the carrier",
			Simp(Fwd(tensor_product.TensorModuleSmul)),
			By(
				subring,
				vectors,
				p.Simplified(tensorModuleLinear, Fwd(tensor_product.TensorModuleSmul)),
				actionLinear,
				p.Simplified(agree, Fwd(tensor_product.TensorModuleSmul)),
				p.Simplified(member, Rev(ScalarExtensionCarrier)),
				ScalarExtensionHomUnique.Read(R).At(S, V, tensorS,
					p.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(c)"),
					p.TermAs[Fun[_TensorV, _TensorV]]("λu:set(prod(A, B) → A). «tensorS».smul(c, u)"), t)))
	}),
})}

// ScalarExtensionOn — the tensor quotient is a module over R: its
// additive group is the tensor module's, and the chosen actions satisfy
// the scalar laws because they agree with those laws on pure tensors.
var ScalarExtensionOn = scalarExtensionOnThm{family.Add(registry.ProofEntry{
	Name: "ScalarExtensionOn",
	Key:  "prop_16914a6e745bd11f",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, B).",
		Hypotheses: []string{
			"subring(R, S)",
			"module_on(restrict_ring(R, S), V)",
		},
		Conclusion: "module_on(R, «extension»)",
	},
		func(
			p *Argument,
			R comm_ring.CommRingFact[on.R],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			hypotheses Fact,
		) {
			given := p.Conjuncts(
				hypotheses,
				"S is a subring of R",
				"V is an S-module")
			subring, vectors := given[0], given[1]
			products := comm_ring.MulMonoidOn.Read(R)
			subringS := p.TermAs[RingOps[A]]("restrict_ring(R, S)")
			regularR := p.TermAs[ModuleOps[A, A]]("regular_module(R)")
			tensorS := p.TermAs[ModuleOps[A, _TensorV]]("«tensorS»")
			one := p.TermAs[A]("R.one")
			regularOverS := p.Have(
				"R is an S-module under multiplication",
				"module_on(restrict_ring(R, S), regular_module(R))",
				By(subring, module.RegularModuleOverSubring.Read(R).At(S)))
			tensorModule := p.Have(
				"the tensor quotient is an S-module",
				"module_on(restrict_ring(R, S), «tensorS»)",
				By(regularOverS, vectors, tensor_product.TensorModuleOn.At(subringS, regularR, V)))
			extensionCarrier := ScalarExtensionCarrier.At(subringS, p.TermAs[RingOps[A]]("R"), V)
			p.Show(
				"the tensor addition and the ring actions satisfy the module axioms",
				Simp(Fwd(ScalarExtensionDef), Fwd(module.ModuleOn), Fwd(module_record.ModuleAdditiveGroupDef)),
				SplitConjAll(
					Case(
						"the scalars form the commutative ring R",
						By(R)),
					Case(
						"the additive group is the tensor module's",
						By(module.AddGroupOn.Read(tensorModule), module_record.ModuleAdditiveGroupDef.At(tensorS))),
					Case(
						"the addition commutes",
						By(module.AddComm.Read(tensorModule))),
					Case(
						"a ring scalar keeps the tensor carrier",
						Derive(func(q *Argument) {
							c, u := q.FixAs[A]("c"), q.FixAs[_TensorV]("u")
							members := q.Assume()
							q.Show(
								"the chosen action is S-linear and therefore preserves its carrier",
								By(
									members,
									subring,
									vectors,
									TensorScalarActionSpec.Read(R).AsFact().At(S, V, c),
									module_homomorphism.HomIn.At(
										subringS, tensorS, tensorS, q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(c)"), u)))
						})),
					Case(
						"each ring scalar distributes over tensor addition",
						Derive(func(q *Argument) {
							c, u, v := q.FixAs[A]("c"), q.FixAs[_TensorV]("u"), q.FixAs[_TensorV]("v")
							members := q.Assume()
							q.Show(
								"the chosen action is additive",
								By(
									subring,
									vectors,
									members,
									TensorScalarActionSpec.Read(R).AsFact().At(S, V, c),
									module_homomorphism.HomAdd.At(
										subringS, tensorS, tensorS, q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(c)"), u, v)))
						})),
					Case(
						"a sum of ring scalars acts as the sum of their actions",
						Derive(func(q *Argument) {
							c, d, u := q.FixAs[A]("c"), q.FixAs[A]("d"), q.FixAs[_TensorV]("u")
							members := q.Assume()
							agree := q.Have(
								"the sum action and the sum of the actions agree on pure tensors",
								Statement{
									Binders:    "∀b:A. ∀v:B.",
									Hypotheses: []string{"b ∈ R.carrier", "v ∈ V.carrier"},
									Conclusion: "«actionS»(c + d, «pureS»(b, v)) = " +
										"«tensorS».add(«actionS»(c, «pureS»(b, v)), «actionS»(d, «pureS»(b, v)))",
								},
								Derive(func(r *Argument) {
									b, v := r.FixAs[A]("b"), r.FixAs[B]("v")
									pair := r.Assume()
									r.Show(
										"distribution in R and additivity of the tensor identify the two values",
										CalcEq(
											Leg(
												r.TermAs[_TensorV]("«pureS»(c * b + d * b, v)"),
												"the action of c + d multiplies the first coordinate, and R distributes",
												By(
													pair,
													subring,
													vectors,
													members,
													comm_ring.AddIn.Read(R).AsFact().At(c, d),
													TensorScalarActionSpec.Read(R).AsFact().At(S, V, r.TermAs[A]("c + d")),
													comm_ring.RightDistribOn.Read(R).AsFact().At(c, d, b))),
											Leg(
												r.TermAs[_TensorV]("«tensorS».add(«pureS»(c * b, v), «pureS»(d * b, v))"),
												"the tensor is additive in its first coordinate",
												By(
													pair,
													members,
													regularOverS,
													vectors,
													comm_ring.MulIn.Read(R).AsFact().At(c, b),
													comm_ring.MulIn.Read(R).AsFact().At(d, b),
													tensor_product.TensorAddLeft.At(
														subringS, regularR, V, r.TermAs[A]("c * b"), r.TermAs[A]("d * b"), v))),
											FinalLeg(
												"the actions of c and d multiply the first coordinate",
												By(
													pair,
													subring,
													vectors,
													members,
													TensorScalarActionSpec.Read(R).AsFact().At(S, V, c),
													TensorScalarActionSpec.Read(R).AsFact().At(S, V, d)))))
								}))
							actionC := q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(c)")
							actionD := q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(d)")
							actionSum := q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(c + d)")
							sumOfActions := q.TermAs[Fun[_TensorV, _TensorV]](
								"λt:set(prod(A, B) → A). «tensorS».add(«actionS»(c, t), «actionS»(d, t))")
							q.Show(
								"the two S-linear endomorphisms agree everywhere by tensor uniqueness",
								By(
									q.Simplified(agree, Fwd(tensor_product.TensorModuleAdd)),
									extensionCarrier,
									subring,
									vectors,
									members,
									comm_ring.AddIn.Read(R).AsFact().At(c, d),
									TensorScalarActionSpec.Read(R).AsFact().At(S, V, c),
									TensorScalarActionSpec.Read(R).AsFact().At(S, V, d),
									TensorScalarActionSpec.Read(R).AsFact().At(S, V, q.TermAs[A]("c + d")),
									module_homomorphism.HomPointwiseSum.At(subringS, tensorS, tensorS, actionC, actionD),
									ScalarExtensionHomUnique.Read(R).At(S, V, tensorS, actionSum, sumOfActions, u)))
						})),
					Case(
						"a product of ring scalars composes their actions",
						Derive(func(q *Argument) {
							c, d, u := q.FixAs[A]("c"), q.FixAs[A]("d"), q.FixAs[_TensorV]("u")
							members := q.Assume()
							agree := q.Have(
								"the product action and the composite agree on pure tensors",
								Statement{
									Binders:    "∀b:A. ∀v:B.",
									Hypotheses: []string{"b ∈ R.carrier", "v ∈ V.carrier"},
									Conclusion: "«actionS»(c * d, «pureS»(b, v)) = «actionS»(c, «actionS»(d, «pureS»(b, v)))",
								},
								Derive(func(r *Argument) {
									b := r.FixAs[A]("b")
									r.FixAs[B]("v")
									pair := r.Assume()
									r.Show(
										"successive multiplication of the first coordinate is multiplication by the product",
										By(
											subring,
											vectors,
											members,
											pair,
											comm_ring.MulIn.Read(R).AsFact().At(c, d),
											comm_ring.MulIn.Read(R).AsFact().At(d, b),
											TensorScalarActionSpec.Read(R).AsFact().At(S, V, c),
											TensorScalarActionSpec.Read(R).AsFact().At(S, V, d),
											TensorScalarActionSpec.Read(R).AsFact().At(S, V, r.TermAs[A]("c * d")),
											comm_monoid.AssocOn.Read(products).AsFact().At(c, d, b)))
								}))
							actionC := q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(c)")
							actionD := q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(d)")
							actionProduct := q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(c * d)")
							composite := q.TermAs[Fun[_TensorV, _TensorV]](
								"λt:set(prod(A, B) → A). «actionS»(c, «actionS»(d, t))")
							q.Show(
								"the two S-linear endomorphisms agree everywhere by tensor uniqueness",
								By(
									agree,
									extensionCarrier,
									subring,
									vectors,
									members,
									comm_ring.MulIn.Read(R).AsFact().At(c, d),
									TensorScalarActionSpec.Read(R).AsFact().At(S, V, c),
									TensorScalarActionSpec.Read(R).AsFact().At(S, V, d),
									TensorScalarActionSpec.Read(R).AsFact().At(S, V, q.TermAs[A]("c * d")),
									module_homomorphism.HomCompose.At(subringS, tensorS, tensorS, tensorS, actionD, actionC),
									functions.ComposeApply.At(actionC, actionD),
									ScalarExtensionHomUnique.Read(R).At(S, V, tensorS, actionProduct, composite, u)))
						})),
					Case(
						"the ring's one acts as the identity",
						Derive(func(q *Argument) {
							u := q.FixAs[_TensorV]("u")
							member := q.Assume()
							agree := q.Have(
								"the action of one and the identity agree on pure tensors",
								Statement{
									Binders:    "∀b:A. ∀v:B.",
									Hypotheses: []string{"b ∈ R.carrier", "v ∈ V.carrier"},
									Conclusion: "«actionS»(R.one, «pureS»(b, v)) = identity_map(«pureS»(b, v))",
								},
								Derive(func(r *Argument) {
									b := r.FixAs[A]("b")
									r.FixAs[B]("v")
									pair := r.Assume()
									r.Show(
										"multiplication by one fixes the first coordinate",
										By(
											comm_ring.OneIn.Read(R),
											subring,
											vectors,
											pair,
											TensorScalarActionSpec.Read(R).AsFact().At(S, V, one),
											comm_monoid.LeftIdentityOn.Read(products).AsFact().At(b),
											functions.IdentityApply))
								}))
							actionOne := q.TermAs[Fun[_TensorV, _TensorV]]("«actionS»(R.one)")
							identity := q.TermAs[Fun[_TensorV, _TensorV]]("identity_map")
							q.Show(
								"tensor uniqueness identifies the action of one with the identity",
								CalcEq(
									Leg(
										q.TermAs[_TensorV]("identity_map(u)"),
										"the two S-linear endomorphisms agree everywhere",
										By(
											comm_ring.OneIn.Read(R),
											module_homomorphism.HomIdentity.Read(tensorModule),
											agree,
											extensionCarrier,
											member,
											subring,
											vectors,
											TensorScalarActionSpec.Read(R).AsFact().At(S, V, one),
											ScalarExtensionHomUnique.Read(R).At(S, V, tensorS, actionOne, identity, u))),
									FinalLeg(
										"the identity map fixes u",
										By(functions.IdentityApply)),
								))
						})),
				))
		}),
})}
