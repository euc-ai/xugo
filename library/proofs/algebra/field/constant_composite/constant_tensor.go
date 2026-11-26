// constant_tensor.go — the tensor clause of a constant extension.

package constant_composite

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/scalar_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// The points of the tensor products the composite is read through: _Tensor,
// a member of a tensor product of two subsets of the ambient field, a coset
// of finitely supported functions on pairs; and M ⊗ N and N ⊗ M of the swap.
type (
	_Tensor   = Set[Fun[Prod[A, A], A]]
	_TensorMN = Set[Fun[Prod[B, C], A]]
	_TensorNM = Set[Fun[Prod[C, B], A]]
	// _ExtensionPoint is a point of a scalar extension of an R-module on B.
	_ExtensionPoint = Set[Fun[Prod[A, B], A]]
)

// ConstantCompositeTensor — when the composite Kl has degree [l : k] over K,
// multiplication is an l-linear isomorphism l ⊗ₖ K ≅ Kl. The composite is the
// K-span of l, since that span is a ring of elements algebraic over K, so a
// field. The scalar extension K ⊗ₖ l has dimension [l : k] over K and
// multiplication carries it K-linearly onto Kl, of that same dimension, so
// bijectively by rank–nullity. Swapping the tensor factors transports this to
// l ⊗ₖ K, where multiplication is the map the l-linear lift of the inclusion
// of K gives, the two agreeing on pure tensors.
var ConstantCompositeTensor = constantCompositeTensorThm{family.Add(registry.ProofEntry{
	Name: "ConstantCompositeTensor",
	Key:  "prop_ea2da6299416ca81",
	Reading: "The degree equation is load-bearing: multiplication is always onto, " +
		"and it is one-to-one exactly when K and l are linearly disjoint over k. " +
		"finite_extension(M, K, constant_composite(M, K, l)) makes every element of the " +
		"composite algebraic over K, which is what turns the K-span of l into a field.",
	Build: family.Sections(Statement{
		Abbrev: Abbrev{
			{Name: "Scalars", Text: "λF:field_ops(A). λS:set(A). restrict_ring(field_ring(F), S)"},
			{Name: "Vectors", Text: "λF:field_ops(A). λS:set(A). " +
				"    restrict_module(regular_module(field_ring(F)), S)"},
			{Name: "BaseChange", Text: "λF:field_ops(A). λk:set(A). λX:set(A). λY:set(A). " +
				"    scalar_extension(«Scalars»(F, k), «Scalars»(F, X), «Vectors»(F, Y))"},
			{Name: "TensorProduct", Text: "λF:field_ops(A). λk:set(A). λX:set(A). λY:set(A). " +
				"    tensor_module(«Scalars»(F, k), «Vectors»(F, X), «Vectors»(F, Y))"},
			{Name: "PureTensor", Text: "λF:field_ops(A). λk:set(A). λX:set(A). λY:set(A). λa:A. λx:A. " +
				"    tensor(«Scalars»(F, k), «Vectors»(F, X), «Vectors»(F, Y), a, x)"},
			{Name: "Kernel", Text: "λF:field_ops(A). " +
				"λk:set(A). " +
				"λX:set(A). " +
				"λY:set(A). " +
				"λC:set(A). " +
				"λf:(set(prod(A, A) → A) → A). " +
				"    group_kernel(«Vectors»(F, C).zero, «BaseChange»(F, k, X, Y).carrier, f)"},
			{Name: "KernelSpace", Text: "λF:field_ops(A). " +
				"λk:set(A). " +
				"λX:set(A). " +
				"λY:set(A). " +
				"λC:set(A). " +
				"λf:(set(prod(A, A) → A) → A). " +
				"    restrict_module(«BaseChange»(F, k, X, Y), «Kernel»(F, k, X, Y, C, f))"},
			{Name: "TensorOver", Text: "λR:ring_ops(A). λS:set(A). λV:module_ops(A, B). " +
				"    tensor_module(restrict_ring(R, S), regular_module(R), V)"},
		},
		Binders: "∀M:field_on(A). ∀k K l:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"subfield(M, l)",
			"k ⊆ K",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"finite_extension(M, K, constant_composite(M, K, l))",
			"extension_degree(M, K, constant_composite(M, K, l)) = extension_degree(M, k, l)",
		},
		Conclusion: "∃f:(set(prod(A, A) → A) → A). " +
			"    module_isomorphism(«Scalars»(M, l), " +
			"        «BaseChange»(M, k, l, K), " +
			"        «Vectors»(M, constant_composite(M, K, l)), " +
			"        f) ∧ " +
			"    (∀a x:A. a ∈ l ∧ x ∈ K ⇒ f(«PureTensor»(M, k, l, K, a, x)) = a * x)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// u ⊗ v ↦ v ⊗ u: the pair (u, v) ↦ v ⊗ u is bilinear because the tensor is
			// bilinear in each slot, and the universal property does the rest.
			tensorSwap := ctx.Lemma(Statement{
				Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
				Hypotheses: []string{"module_on(R, M)", "module_on(R, N)"},
				Conclusion: "∃s:(set(prod(B, C) → A) → set(prod(C, B) → A)). " +
					"    module_homomorphism(R, tensor_module(R, M, N), tensor_module(R, N, M), s) ∧ " +
					"    (∀u:B. ∀v:C. " +
					"        u ∈ M.carrier ∧ v ∈ N.carrier ⇒ s(tensor(R, M, N, u, v)) = tensor(R, N, M, v, u))",
			},
				func(
					a *Argument,
					R *Expr[module_record.RingOps[A]],
					M *Expr[module_record.ModuleOps[A, B]],
					N *Expr[module_record.ModuleOps[A, C]],
					modM module.ModuleFact[on.R, on.M],
					modN module.ModuleFact[on.R, on.N],
				) {
					swapped := a.TermAs[module_record.ModuleOps[A, _TensorNM]]("tensor_module(R, N, M)")
					rule := a.TermAs[Fun2[B, C, _TensorNM]]("λu:B. λv:C. tensor(R, N, M, v, u)")
					into := a.Have(
						"the swapped pure tensors lie in N ⊗ M",
						Statement{
							Binders:    "∀u:B. ∀v:C.",
							Hypotheses: []string{"u ∈ M.carrier", "v ∈ N.carrier"},
							Conclusion: "tensor(R, N, M, v, u) ∈ tensor_module(R, N, M).carrier",
						},
						Derive(func(b *Argument) {
							u, v := b.FixAs[B]("u"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"a pure tensor of two members lies in the tensor product",
								Simp(Fwd(tensor_product.TensorModuleCarrier)),
								By(modM, modN, members, tensor_product.TensorIn.At(R, N, M, v, u)))
						}))
					addFirst := a.Have(
						"the swap is additive in its first argument, the tensor's second slot",
						Statement{
							Binders:    "∀u u':B. ∀v:C.",
							Hypotheses: []string{"u ∈ M.carrier", "u' ∈ M.carrier", "v ∈ N.carrier"},
							Conclusion: "tensor(R, N, M, v, u + u') = " +
								"tensor_module(R, N, M).add(tensor(R, N, M, v, u), tensor(R, N, M, v, u'))",
						},
						Derive(func(b *Argument) {
							u, up, v := b.FixAs[B]("u"), b.FixAs[B]("u'"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"the tensor is additive in its second slot",
								Simp(Fwd(tensor_product.TensorModuleAdd)),
								By(modM, modN, members, tensor_product.TensorAddRight.At(R, N, M, v, u, up)))
						}))
					addSecond := a.Have(
						"the swap is additive in its second argument, the tensor's first slot",
						Statement{
							Binders:    "∀u:B. ∀v v':C.",
							Hypotheses: []string{"u ∈ M.carrier", "v ∈ N.carrier", "v' ∈ N.carrier"},
							Conclusion: "tensor(R, N, M, v + v', u) = " +
								"tensor_module(R, N, M).add(tensor(R, N, M, v, u), tensor(R, N, M, v', u))",
						},
						Derive(func(b *Argument) {
							u, v, vp := b.FixAs[B]("u"), b.FixAs[C]("v"), b.FixAs[C]("v'")
							members := b.Assume()
							b.Show(
								"the tensor is additive in its first slot",
								Simp(Fwd(tensor_product.TensorModuleAdd)),
								By(modM, modN, members, tensor_product.TensorAddLeft.At(R, N, M, v, vp, u)))
						}))
					scaleFirst := a.Have(
						"a scalar on the first argument comes out of the tensor's second slot",
						Statement{
							Binders:    "∀c:A. ∀u:B. ∀v:C.",
							Hypotheses: []string{"c ∈ R.carrier", "u ∈ M.carrier", "v ∈ N.carrier"},
							Conclusion: "tensor(R, N, M, v, c • u) = tensor_module(R, N, M).smul(c, tensor(R, N, M, v, u))",
						},
						Derive(func(b *Argument) {
							c, u, v := b.FixAs[A]("c"), b.FixAs[B]("u"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"a scalar comes out of the tensor's second slot",
								Simp(Fwd(tensor_product.TensorModuleSmul)),
								By(modM, modN, members, tensor_product.TensorSmulRightFactor.At(R, N, M, c, v, u)))
						}))
					scaleSecond := a.Have(
						"a scalar on the second argument comes out of the tensor's first slot",
						Statement{
							Binders:    "∀c:A. ∀u:B. ∀v:C.",
							Hypotheses: []string{"c ∈ R.carrier", "u ∈ M.carrier", "v ∈ N.carrier"},
							Conclusion: "tensor(R, N, M, c • v, u) = tensor_module(R, N, M).smul(c, tensor(R, N, M, v, u))",
						},
						Derive(func(b *Argument) {
							c, u, v := b.FixAs[A]("c"), b.FixAs[B]("u"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"a scalar comes out of the tensor's first slot",
								Simp(Fwd(tensor_product.TensorModuleSmul)),
								By(modM, modN, members, tensor_product.TensorSmulLeft.At(R, N, M, c, v, u)))
						}))
					bilinear := a.Have(
						"so (u, v) ↦ v ⊗ u is bilinear",
						"bilinear_map(R, M, N, tensor_module(R, N, M), λu:B. λv:C. tensor(R, N, M, v, u))",
						By(
							modM,
							modN,
							tensor_product.TensorModuleOn.At(R, N, M),
							into,
							addFirst,
							addSecond,
							scaleFirst,
							scaleSecond,
							module_homomorphism.BilinearMapOfClauses.At(R, M, N, swapped, rule)))
					a.Show(
						"the universal property of M ⊗ N makes it a homomorphism",
						By(bilinear, tensor_product.TensorUniversal.Read(modM).At(N, swapped, rule)))
				})

			// The swaps of M ⊗ N and N ⊗ M undo each other on pure tensors, and so on the
			// whole tensor product, which pure tensors determine.
			swapUndone := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀M:module_ops(A, B). " +
					"∀N:module_ops(A, C). " +
					"∀s:(set(prod(B, C) → A) → set(prod(C, B) → A)). " +
					"∀r:(set(prod(C, B) → A) → set(prod(B, C) → A)). " +
					"∀t:set(prod(B, C) → A).",
				Hypotheses: []string{
					"module_on(R, M)",
					"module_on(R, N)",
					"module_homomorphism(R, tensor_module(R, M, N), tensor_module(R, N, M), s)",
					"module_homomorphism(R, tensor_module(R, N, M), tensor_module(R, M, N), r)",
					"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ s(tensor(R, M, N, u, v)) = tensor(R, N, M, v, u)",
					"∀v:C. ∀u:B. v ∈ N.carrier ∧ u ∈ M.carrier ⇒ r(tensor(R, N, M, v, u)) = tensor(R, M, N, u, v)",
					"t ∈ tensor_module(R, M, N).carrier",
				},
				Conclusion: "r(s(t)) = t",
			},
				func(
					a *Argument,
					R *Expr[module_record.RingOps[A]],
					M *Expr[module_record.ModuleOps[A, B]],
					N *Expr[module_record.ModuleOps[A, C]],
					s *Arrow[_TensorMN, _TensorNM],
					r *Arrow[_TensorNM, _TensorMN],
					t *Expr[_TensorMN],
					modM module.ModuleFact[on.R, on.M],
					modN module.ModuleFact[on.R, on.N],
					linearS, linearR, pureS, pureR, member Fact,
				) {
					forward := a.TermAs[module_record.ModuleOps[A, _TensorMN]]("tensor_module(R, M, N)")
					backward := a.TermAs[module_record.ModuleOps[A, _TensorNM]]("tensor_module(R, N, M)")
					identity := a.TermAs[Fun[_TensorMN, _TensorMN]]("identity_map")
					composite := a.TermAs[Fun[_TensorMN, _TensorMN]]("r ∘ s")
					homomorphisms := a.Have(
						"r ∘ s and the identity are endomorphisms of M ⊗ N",
						"module_homomorphism(R, tensor_module(R, M, N), tensor_module(R, M, N), r ∘ s) ∧ "+
							"module_homomorphism(R, tensor_module(R, M, N), tensor_module(R, M, N), identity_map)",
						By(
							linearS,
							linearR,
							modM,
							modN,
							tensor_product.TensorModuleOn.At(R, M, N),
							module_homomorphism.HomCompose.At(R, forward, backward, forward, s, r),
							module_homomorphism.HomIdentity.At(R, forward)))
					agree := a.Have(
						"they agree on pure tensors",
						Statement{
							Binders:    "∀u:B. ∀v:C.",
							Hypotheses: []string{"u ∈ M.carrier", "v ∈ N.carrier"},
							Conclusion: "(r ∘ s)(tensor(R, M, N, u, v)) = identity_map(tensor(R, M, N, u, v))",
						},
						Derive(func(b *Argument) {
							u, v := b.FixAs[B]("u"), b.FixAs[C]("v")
							members := b.Assume()
							b.Show(
								"swapping twice returns the pure tensor",
								Simp(Fwd(functions.ComposeApply), Fwd(functions.IdentityApply)),
								By(Normalized, members, pureS.At(u, v), pureR.At(v, u)))
						}))
					inProduct := a.Simplified(member, Fwd(tensor_product.TensorModuleCarrier))
					onT := a.Have(
						"so they agree on the whole tensor product",
						"(r ∘ s)(t) = identity_map(t)",
						By(
							modM,
							modN,
							homomorphisms,
							agree,
							inProduct,
							tensor_product.TensorUniversalUnique.Read(modM).At(N, forward, composite, identity, t)))
					a.Show(
						"which at t says r(s(t)) = t",
						By(onT, functions.ComposeApply, functions.IdentityApply))
				})

			// The swap is an isomorphism, the swap the other way being its inverse.
			swapIsomorphism := ctx.Lemma(Statement{
				Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C).",
				Hypotheses: []string{"module_on(R, M)", "module_on(R, N)"},
				Conclusion: "∃s:(set(prod(B, C) → A) → set(prod(C, B) → A)). " +
					"    module_isomorphism(R, tensor_module(R, M, N), tensor_module(R, N, M), s) ∧ " +
					"    (∀u:B. ∀v:C. " +
					"        u ∈ M.carrier ∧ v ∈ N.carrier ⇒ s(tensor(R, M, N, u, v)) = tensor(R, N, M, v, u))",
			},
				func(
					a *Argument,
					R *Expr[module_record.RingOps[A]],
					M *Expr[module_record.ModuleOps[A, B]],
					N *Expr[module_record.ModuleOps[A, C]],
					modM module.ModuleFact[on.R, on.M],
					modN module.ModuleFact[on.R, on.N],
				) {
					forward := a.TermAs[module_record.ModuleOps[A, _TensorMN]]("tensor_module(R, M, N)")
					backward := a.TermAs[module_record.ModuleOps[A, _TensorNM]]("tensor_module(R, N, M)")
					s, forth := a.UnpackAs[Fun[_TensorMN, _TensorNM]](
						GroupPremises(modM, modN, At(tensorSwap, R, M, N)), "s")
					r, back := a.UnpackAs[Fun[_TensorNM, _TensorMN]](
						GroupPremises(modN, modM, At(tensorSwap, R, N, M)), "r")
					forthParts := a.Conjuncts(
						forth,
						"s is a homomorphism",
						"s swaps pure tensors")
					backParts := a.Conjuncts(
						back,
						"r is a homomorphism",
						"r swaps pure tensors")
					linearS, pureS, linearR, pureR := forthParts[0], forthParts[1], backParts[0], backParts[1]
					undoS := a.Have(
						"r undoes s on M ⊗ N",
						"∀t:set(prod(B, C) → A). t ∈ tensor_module(R, M, N).carrier ⇒ r(s(t)) = t",
						Derive(func(b *Argument) {
							t := b.FixAs[_TensorMN]("t")
							member := b.Assume()
							b.Show(
								"the two swaps cancel on M ⊗ N",
								By(modM, modN, linearS, linearR, pureS, pureR, member, At(swapUndone, R, M, N, s, r, t)))
						}))
					undoR := a.Have(
						"s undoes r on N ⊗ M",
						"∀t:set(prod(C, B) → A). t ∈ tensor_module(R, N, M).carrier ⇒ s(r(t)) = t",
						Derive(func(b *Argument) {
							t := b.FixAs[_TensorNM]("t")
							member := b.Assume()
							b.Show(
								"the two swaps cancel on N ⊗ M",
								By(modM, modN, linearS, linearR, pureS, pureR, member, At(swapUndone, R, N, M, r, s, t)))
						}))
					bijective := a.Have(
						"so s is a bijection of M ⊗ N onto N ⊗ M",
						"injective_on(tensor_module(R, M, N).carrier, s) ∧ "+
							"image(s, tensor_module(R, M, N).carrier) = tensor_module(R, N, M).carrier",
						By(
							undoS,
							undoR,
							module_homomorphism.HomIn.Read(linearS),
							module_homomorphism.HomIn.Read(linearR),
							functions.TwoSidedInverseBijection.At(
								a.TermAs[Set[_TensorMN]]("tensor_module(R, M, N).carrier"),
								a.TermAs[Set[_TensorNM]]("tensor_module(R, N, M).carrier"),
								s,
								r)))
					a.Take(s)
					a.Show(
						"a bijective homomorphism is an isomorphism",
						By(linearS, pureS, bijective, module_homomorphism.ModuleIsomorphismDef.At(R, forward, backward, s)))
				})

			// An R-linear map out of the scalar extension is S-linear on the tensor
			// module: the two have one carrier and one addition, and on a scalar of S
			// their actions coincide.
			linearOverSubring := ctx.Lemma(Statement{
				Binders: "∀R:comm_ring_on(A). " +
					"∀S:set(A). " +
					"∀V:module_ops(A, B). " +
					"∀N:module_ops(A, C). " +
					"∀h:(set(prod(A, B) → A) → C).",
				Hypotheses: []string{
					"subring(R, S)",
					"module_on(restrict_ring(R, S), V)",
					"module_homomorphism(R, scalar_extension(restrict_ring(R, S), R, V), N, h)",
				},
				Conclusion: "module_homomorphism(restrict_ring(R, S), «TensorOver»(R, S, V), N, h)",
			},
				func(
					a *Argument,
					R comm_ring.CommRingFact[on.R],
					S *Expr[Set[A]],
					V *Expr[module_record.ModuleOps[A, B]],
					N *Expr[module_record.ModuleOps[A, C]],
					h *Arrow[_ExtensionPoint, C],
					subring, vectors, linear Fact,
				) {
					ring := a.TermAs[module_record.RingOps[A]]("R")
					subringS := a.TermAs[module_record.RingOps[A]]("restrict_ring(R, S)")
					regularR := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(R)")
					extension := a.TermAs[module_record.ModuleOps[A, _ExtensionPoint]](
						"scalar_extension(restrict_ring(R, S), R, V)")
					tensorS := a.TermAs[module_record.ModuleOps[A, _ExtensionPoint]]("«TensorOver»(R, S, V)")
					overS := a.Have(
						"h is linear over the scalars of S",
						"module_homomorphism(restrict_ring(R, S), scalar_extension(restrict_ring(R, S), R, V), N, h)",
						By(subring, linear, module_homomorphism.HomRestrictScalars.At(ring, extension, N, h, S)))
					modules := a.Have(
						"the tensor module and N are S-modules",
						"module_on(restrict_ring(R, S), «TensorOver»(R, S, V)) ∧ module_on(restrict_ring(R, S), N)",
						By(
							subring,
							vectors,
							module.RegularModuleOverSubring.Read(R).At(S),
							tensor_product.TensorModuleOn.At(subringS, regularR, V),
							module_homomorphism.HomTarget.Read(overS)))
					into := a.Have(
						"h carries the tensor module into N, the carrier being the extension's",
						"∀u:set(prod(A, B) → A). u ∈ «TensorOver»(R, S, V).carrier ⇒ h(u) ∈ N.carrier",
						Derive(func(b *Argument) {
							u := b.FixAs[_ExtensionPoint]("u")
							member := b.Assume()
							b.Show(
								"the extension's carrier is the tensor module's",
								By(member, module_homomorphism.HomIn.Read(overS).AsFact().At(u)))
						}))
					additive := a.Have(
						"h is additive on the tensor module, the addition being the extension's",
						Statement{
							Binders:    "∀u v:set(prod(A, B) → A).",
							Hypotheses: []string{"u ∈ «TensorOver»(R, S, V).carrier", "v ∈ «TensorOver»(R, S, V).carrier"},
							Conclusion: "h(«TensorOver»(R, S, V).add(u, v)) = N.add(h(u), h(v))",
						},
						Derive(func(b *Argument) {
							u, v := b.FixAs[_ExtensionPoint]("u"), b.FixAs[_ExtensionPoint]("v")
							members := b.Assume()
							b.Show(
								"the extension's addition is the tensor module's",
								By(members, module_homomorphism.HomAdd.Read(overS).AsFact().At(u, v)))
						}))
					scaling := a.Have(
						"h commutes with the scalars of S, on which the two actions coincide",
						Statement{
							Binders:    "∀c:A. ∀u:set(prod(A, B) → A).",
							Hypotheses: []string{"c ∈ restrict_ring(R, S).carrier", "u ∈ «TensorOver»(R, S, V).carrier"},
							Conclusion: "h(«TensorOver»(R, S, V).smul(c, u)) = N.smul(c, h(u))",
						},
						Derive(func(b *Argument) {
							c, u := b.FixAs[A]("c"), b.FixAs[_ExtensionPoint]("u")
							members := b.Have(
								"c lies in S and in R",
								"c ∈ S ∧ c ∈ R.carrier ∧ u ∈ «TensorOver»(R, S, V).carrier",
								By(
									b.Assume(),
									comm_ring.SubringSubset.Read(subring),
									set_basic.SubsetDef.At(S, b.TermAs[Set[A]]("R.carrier"))))
							b.Show(
								"the action of c on the extension is the tensor module's scaling",
								Simp(Fwd(tensor_product.TensorModuleSmul)),
								By(
									R,
									subring,
									vectors,
									members,
									scalar_extension.TensorScalarActionRestrict.Read(R).At(S, V, c, u),
									module_homomorphism.HomSmul.Read(overS).AsFact().At(c, u)))
						}))
					a.Show(
						"these are the clauses of a homomorphism out of the tensor module",
						By(
							modules,
							into,
							additive,
							scaling,
							module_homomorphism.ModuleHomomorphismDef.At(subringS, tensorS, N, h)))
				})

			// X ⊗ₖ Y as a scalar extension has the points of the tensor module.
			extensionPoints := ctx.Lemma(
				"∀M:field_ops(A). ∀k X Y:set(A). "+
					"    «BaseChange»(M, k, X, Y).carrier = «TensorProduct»(M, k, X, Y).carrier",
				func(a *Argument, M *Expr[FieldOps[A]], k, X, Y *Expr[Set[A]]) {
					a.Show(
						"the scalar extension is a tensor product with X's regular module, and that is X's vectors",
						Simp(
							Fwd(scalar_extension.ScalarExtensionCarrier),
							Fwd(module_record.RestrictRingDef),
							Fwd(module_record.RegularModuleDef),
							Fwd(module_record.RestrictModuleDef),
							Fwd(field.FieldRingDef)),
						Basic())
				})

			// The composite holds K and l.
			compositeHolds := ctx.Lemma(Statement{
				Binders:    "∀M:field_on(A). ∀K l:set(A).",
				Hypotheses: []string{"subfield(M, K)", "subfield(M, l)"},
				Conclusion: "subfield(M, constant_composite(M, K, l)) ∧ " +
					"K ⊆ constant_composite(M, K, l) ∧ " +
					"l ⊆ constant_composite(M, K, l)",
			},
				func(a *Argument, M field.FieldFact[on.M], K, l *Expr[Set[A]], subK, subL Fact) {
					m := a.TermAs[FieldOps[A]]("M")
					a.Show(
						"the composite is the field generated by K and l, which lie in M",
						Simp(Fwd(ConstantCompositeDef)),
						By(
							subK,
							subL,
							field.SubfieldSubset.At(m, K),
							field.SubfieldSubset.At(m, l),
							algebraic_element.AdjoinSubfield.Read(M).At(K, l)))
				})

			// The inclusion of Y in C is k-linear, so it lifts to the X-linear map
			// a ⊗ x ↦ a * x out of X ⊗ₖ Y, which is k-linear on the tensor module.
			multiplication := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀k X Y C:set(A).",
				Hypotheses: []string{
					"subfield(M, k)",
					"subfield(M, X)",
					"subfield(M, Y)",
					"subfield(M, C)",
					"k ⊆ X",
					"k ⊆ Y",
					"X ⊆ C",
					"Y ⊆ C",
				},
				Conclusion: "∃h:(set(prod(A, A) → A) → A). " +
					"    module_homomorphism(«Scalars»(M, X), «BaseChange»(M, k, X, Y), «Vectors»(M, C), h) ∧ " +
					"    module_homomorphism(«Scalars»(M, k), «TensorProduct»(M, k, X, Y), «Vectors»(M, C), h) ∧ " +
					"    (∀a x:A. a ∈ X ∧ x ∈ Y ⇒ h(«PureTensor»(M, k, X, Y, a, x)) = a * x)",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					k, X, Y, C *Expr[Set[A]],
					subk, subX, subY, subC, kInX, kInY, XInC, YInC Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					scalarsX := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, X)")
					scalarsk := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, k)")
					vectorsY := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, Y)")
					vectorsC := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, C)")
					inclusion := a.TermAs[Fun[A, A]]("identity_map")
					sameStructures := a.Have(
						"k's ring read inside X is k's ring, and X's regular module is X's vectors",
						"restrict_ring(«Scalars»(M, X), k) = «Scalars»(M, k) ∧ "+
							"regular_module(«Scalars»(M, X)) = «Vectors»(M, X)",
						Simp(
							Fwd(module_record.RestrictRingDef),
							Fwd(module_record.RegularModuleDef),
							Fwd(module_record.RestrictModuleDef),
							Fwd(field.FieldRingDef)),
						Basic())
					fieldX := a.Have(
						"X is a field with k as a subfield",
						"field_on(restrict_field(M, X)) ∧ subfield(restrict_field(M, X), k)",
						By(subX, subk, kInX, field.SubfieldFieldOn.Read(M).At(X), field.SubfieldRestrict.At(m, X, k)))
					ringFacts := a.Conjuncts(
						a.Have(
							"so X carries a commutative ring with k as a subring",
							"comm_ring_on(«Scalars»(M, X)) ∧ subring(«Scalars»(M, X), k)",
							Simp(Fwd(field.RestrictFieldRing)),
							By(
								fieldX,
								field.RingOn.At(a.TermAs[FieldOps[A]]("restrict_field(M, X)")),
								field.SubfieldSubring.At(a.TermAs[FieldOps[A]]("restrict_field(M, X)"), k))),
						"the ring on X is commutative",
						"k is a subring of it")
					ringX, subringK := ringFacts[0], ringFacts[1]
					modules := a.Have(
						"C is a space over X and over k, and Y one over k",
						"module_on(«Scalars»(M, X), «Vectors»(M, C)) ∧ "+
							"module_on(«Scalars»(M, k), «Vectors»(M, Y)) ∧ "+
							"module_on(«Scalars»(M, k), «Vectors»(M, C))",
						By(
							subX,
							subY,
							subk,
							subC,
							kInY,
							XInC,
							set_order.SubsetTrans.At(k, X, C),
							kInX,
							field_extension.ExtensionModuleOn.Read(M).At(X, C),
							field_extension.ExtensionModuleOn.Read(M).At(k, Y),
							field_extension.ExtensionModuleOn.Read(M).At(k, C)))
					restricted := a.Have(
						"Y restricted from C is Y",
						"restrict_module(«Vectors»(M, C), Y) = «Vectors»(M, Y)",
						Simp(Fwd(module_record.RestrictModuleDef)),
						Basic())
					inclusionLinear := a.Have(
						"the inclusion of Y in C is linear over k",
						"module_homomorphism(restrict_ring(«Scalars»(M, X), k), "+
							"    «Vectors»(M, Y), "+
							"    «Vectors»(M, C), "+
							"    identity_map)",
						restricted.RwRev(),
						By(
							Normalized,
							sameStructures,
							modules,
							subk,
							subY,
							subC,
							kInY,
							YInC,
							field_extension.SubfieldSubmodule.Read(M).At(k, Y, C),
							module_homomorphism.HomIdentity.At(scalarsk, vectorsC),
							module_homomorphism.HomRestrictSource.At(scalarsk, vectorsC, vectorsC, inclusion, Y)))
					h, lifted := a.UnpackAs[Fun[_Tensor, A]](
						GroupPremises(
							ringFacts[1],
							modules,
							inclusionLinear,
							scalar_extension.ScalarExtensionLift.Read(ringX).At(k, vectorsY, vectorsC, inclusion)),
						"h")
					liftParts := a.Conjuncts(
						lifted,
						"h is linear over X",
						"h multiplies on pure tensors")
					linearOverX, pure := liftParts[0], liftParts[1]
					linearOverBase := a.Have(
						"h is linear over k on the tensor module",
						"module_homomorphism(restrict_ring(«Scalars»(M, X), k), "+
							"    tensor_module(restrict_ring(«Scalars»(M, X), k), "+
							"        regular_module(«Scalars»(M, X)), "+
							"        «Vectors»(M, Y)), "+
							"    «Vectors»(M, C), "+
							"    h)",
						By(
							ringX,
							subringK,
							modules,
							sameStructures,
							linearOverX,
							At(linearOverSubring, scalarsX, k, vectorsY, vectorsC, h)))
					a.Take(h)
					homs := a.Have(
						"h is linear over X on the extension and over k on the tensor module",
						"module_homomorphism(«Scalars»(M, X), «BaseChange»(M, k, X, Y), «Vectors»(M, C), h) ∧ "+
							"module_homomorphism(«Scalars»(M, k), «TensorProduct»(M, k, X, Y), «Vectors»(M, C), h)",
						By(Normalized, sameStructures, linearOverX, linearOverBase))
					values := a.Have(
						"on a pure tensor it is the product",
						"∀a x:A. a ∈ X ∧ x ∈ Y ⇒ h(«PureTensor»(M, k, X, Y, a, x)) = a * x",
						Derive(func(b *Argument) {
							scalar, x := b.FixAs[A]("a"), b.FixAs[A]("x")
							members := b.Assume()
							b.Show(
								"scaling in C by a is multiplying by a, and the inclusion fixes x",
								By(sameStructures, members, pure.At(scalar, x), functions.IdentityApply))
						}))
					a.Show(
						"h is the map asked for",
						By(homs, values))
				})

			// The K-span V of l is a ring of elements algebraic over K, so a field, and
			// it holds K and l: it is all of K(l).
			compositeSpan := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀K l:set(A).",
				Hypotheses: []string{
					"subfield(M, K)",
					"subfield(M, l)",
					"finite_extension(M, K, constant_composite(M, K, l))",
				},
				Conclusion: "module_span(«Scalars»(M, K), «Vectors»(M, constant_composite(M, K, l)), l) = " +
					"constant_composite(M, K, l)",
			},
				func(a *Argument, M field.FieldFact[on.M], K, l *Expr[Set[A]], subK, subL, finiteC Fact) {
					m := a.TermAs[FieldOps[A]]("M")
					mulMonoid := comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))
					fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
					scalars := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, K)")
					C, defC := a.LetAs[Set[A]]("C", "constant_composite(M, K, l)")
					vectors := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, C)")
					holds := a.Conjuncts(
						a.Have(
							"C is a subfield holding K and l",
							"subfield(M, C) ∧ K ⊆ C ∧ l ⊆ C",
							By(Normalized, M, defC, subK, subL, At(compositeHolds, m, K, l))),
						"C is a subfield",
						"C holds K",
						"C holds l")
					subC, kInC, lInC := holds[0], holds[1], holds[2]
					space := a.Have(
						"C is a vector space over K",
						"module_on(«Scalars»(M, K), «Vectors»(M, C))",
						By(subK, subC, kInC, field_extension.ExtensionModuleOn.Read(M).At(K, C)))
					V, defV := a.LetAs[Set[A]]("V", "module_span(«Scalars»(M, K), «Vectors»(M, C), l)")
					spanned := a.Conjuncts(
						a.Have(
							"V is a subspace of C holding l",
							"submodule(«Scalars»(M, K), «Vectors»(M, C), V) ∧ l ⊆ V",
							By(
								Normalized,
								defV,
								space,
								lInC,
								submodule.SpanSubmodule.Read(space).At(l),
								submodule.SubsetSpan.At(scalars, vectors, l))),
						"V is a subspace of C",
						"V holds l")
					subspace, lInV := spanned[0], spanned[1]
					vInC := a.Have(
						"V lies in C",
						"V ⊆ C",
						By(subspace, submodule.SubmoduleSubset.At(scalars, vectors, V)))
					overC := a.Have(
						"C is a vector space over itself, and K a subring of M",
						"module_on(«Scalars»(M, C), «Vectors»(M, C)) ∧ subring(field_ring(M), K)",
						By(
							subC,
							subK,
							set_order.SubsetRefl,
							field_extension.ExtensionModuleOn.Read(M).At(C, C),
							field.SubfieldSubring.Read(M).At(K)))
					scaling := a.Have(
						"multiplying by a member of C is K-linear on C",
						"∀z:A. z ∈ C ⇒ module_homomorphism(«Scalars»(M, K), «Vectors»(M, C), «Vectors»(M, C), λu:A. z * u)",
						Derive(func(b *Argument) {
							z := b.FixAs[A]("z")
							member := b.Assume()
							b.Show(
								"scaling by a member of C is linear over the subring K",
								By(
									member,
									overC,
									kInC,
									module_homomorphism.ScalingLinearOverSubring.At(fieldRing, C, K, vectors, z)))
						}))
					spanStep := a.Have(
						"a member of C carrying l into V carries all of V into V",
						"∀z v:A. z ∈ C ∧ (∀a:A. a ∈ l ⇒ z * a ∈ V) ∧ v ∈ V ⇒ z * v ∈ V",
						Derive(func(b *Argument) {
							z := b.FixAs[A]("z")
							b.FixAs[A]("v")
							given := b.Conjuncts(
								b.Assume(),
								"z lies in C",
								"z carries l into V",
								"v lies in V")
							rule := b.TermAs[Fun[A, A]]("λu:A. z * u")
							preimage := b.TermAs[Set[A]]("preimage_on(C, λu:A. z * u, V)")
							preimageSubspace := b.Have(
								"the elements z carries into V form a subspace of C",
								"submodule(«Scalars»(M, K), «Vectors»(M, C), preimage_on(C, λu:A. z * u, V))",
								By(
									given[0],
									subspace,
									scaling.At(z),
									module_homomorphism.HomPreimageSubmodule.At(scalars, vectors, vectors, rule, V)))
							lInPreimage := b.Have(
								"that subspace holds l",
								"l ⊆ preimage_on(C, λu:A. z * u, V)",
								BySets(given[1], lInC))
							vInPreimage := b.Have(
								"so it holds the span of l",
								"V ⊆ preimage_on(C, λu:A. z * u, V)",
								By(defV, preimageSubspace, lInPreimage, submodule.SpanLeast.At(scalars, vectors, l, preimage)))
							b.Show(
								"so z carries v into V",
								BySets(vInPreimage, given[2]))
						}))
					timesL := a.Have(
						"V is closed under multiplication by l",
						"∀a v:A. a ∈ l ∧ v ∈ V ⇒ a * v ∈ V",
						Derive(func(b *Argument) {
							scalar, v := b.FixAs[A]("a"), b.FixAs[A]("v")
							members := b.Assume()
							intoV := b.Have(
								"a carries l into l, which lies in V",
								"∀b:A. b ∈ l ⇒ a * b ∈ V",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("b")
									member := c.Assume()
									c.Show(
										"l is closed under products",
										By(
											member,
											members,
											subL,
											lInV,
											field.SubfieldMul.At(m, l, scalar, x),
											set_basic.SubsetDef.At(l, V)))
								}))
							b.Show(
								"a lies in C and carries l into V",
								By(intoV, members, lInC, set_basic.SubsetDef.At(l, C), spanStep.At(scalar, v)))
						}))
					products := a.Have(
						"V is closed under products",
						"∀v w:A. v ∈ V ∧ w ∈ V ⇒ v * w ∈ V",
						Derive(func(b *Argument) {
							v, w := b.FixAs[A]("v"), b.FixAs[A]("w")
							members := b.Assume()
							intoV := b.Have(
								"v carries l into V, products commuting",
								"∀b:A. b ∈ l ⇒ v * b ∈ V",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("b")
									member := c.Assume()
									inField := c.Have(
										"v and b lie in M",
										"v ∈ M.carrier ∧ b ∈ M.carrier",
										BySets(members, member, vInC, lInC, field.SubfieldSubset.At(m, C), subC))
									c.Show(
										"v * b is b * v, a multiple of v by a member of l",
										By(
											Normalized,
											members,
											member,
											inField,
											timesL.At(x, v),
											comm_monoid.CommOn.Read(mulMonoid).AsFact().At(v, x)))
								}))
							b.Show(
								"v lies in C and carries l into V",
								By(intoV, vInC, members, set_basic.SubsetDef.At(V, C), spanStep.At(v, w)))
						}))
					kInV := a.Have(
						"V holds K, each member of K being a multiple of one",
						"K ⊆ V",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							member := b.Assume()
							inField := b.Have(
								"x lies in M and one in V",
								"x ∈ M.carrier ∧ M.one ∈ V",
								BySets(member, subK, subL, lInV, field.SubfieldSubset.At(m, K), field.SubfieldOne.At(m, l)))
							b.Show(
								"x is x • one, a multiple of a member of V",
								By(
									Normalized,
									member,
									inField,
									subspace,
									submodule.SubmoduleSmul.At(scalars, vectors, V, x, b.TermAs[A]("M.one")),
									comm_monoid.RightIdentityOn.Read(mulMonoid).AsFact().At(x)))
						}))
					additive := a.Have(
						"V holds zero and is closed under sums and negatives",
						"M.zero ∈ V ∧ (∀x y:A. x ∈ V ∧ y ∈ V ⇒ M.add(x, y) ∈ V) ∧ (∀x:A. x ∈ V ⇒ M.neg(x) ∈ V)",
						By(
							subspace,
							submodule.SubmoduleZero.Read(subspace),
							submodule.SubmoduleAdd.Read(subspace),
							submodule.SubmoduleNeg.Read(subspace)))
					inField := a.Have(
						"V lies in M and holds one",
						"V ⊆ M.carrier ∧ M.one ∈ V",
						BySets(vInC, lInV, subC, subL, field.SubfieldSubset.At(m, C), field.SubfieldOne.At(m, l)))
					ring := a.Have(
						"V is a ring under M's operations",
						"comm_ring_on(restrict_ring(field_ring(M), V))",
						By(
							additive,
							inField,
							products,
							comm_ring.SubringDef.At(fieldRing, V),
							comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(V)))
					inverses := a.Have(
						"V is closed under inverses, each member being algebraic over K",
						"∀v:A. v ∈ V ⇒ M.inv(v) ∈ V",
						Derive(func(b *Argument) {
							v := b.FixAs[A]("v")
							member := b.Assume()
							adjoined := b.TermAs[Set[A]]("polynomial_image(field_ring(M), K, v)")
							inC := b.Have(
								"v lies in C and in M",
								"v ∈ C ∧ v ∈ M.carrier",
								BySets(member, vInC, subC, field.SubfieldSubset.At(m, C)))
							algebraic := b.Have(
								"v is algebraic over K, as C is finite over K",
								"algebraic_over(M, K, v)",
								By(
									inC,
									subK,
									subC,
									kInC,
									finiteC,
									algebraic_element.FiniteExtensionAlgebraic.Read(M).AsFact().At(K, C, v)))
							imageInV := b.Have(
								"K[v] lies in the ring V",
								"polynomial_image(field_ring(M), K, v) ⊆ V",
								By(ring, kInV, member, algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(K, V, v)))
							inverseInImage := b.Have(
								"inv(v) lies in the field K(v), which is K[v]",
								"M.inv(v) ∈ polynomial_image(field_ring(M), K, v)",
								By(
									inC,
									subK,
									algebraic,
									algebraic_element.AdjoinEqImage.Read(M).AsFact().At(K, v),
									algebraic_element.AdjoinElementSubfield.Read(M).AsFact().At(K, v),
									field.SubfieldInv.At(m, adjoined, v)))
							b.Show(
								"so inv(v) lies in V",
								BySets(imageInV, inverseInImage))
						}))
					subfieldV := a.Have(
						"so V is a subfield",
						"subfield(M, V)",
						By(additive, inField, products, inverses, field.SubfieldDef.At(m, V)))
					cInV := a.Have(
						"so V holds C, the least subfield holding K and l",
						"C ⊆ V",
						By(
							Normalized,
							defC,
							subfieldV,
							kInV,
							lInV,
							ConstantCompositeDef.At(m, K, l),
							algebraic_element.AdjoinLeast.Read(M).At(K, l, V)))
					a.Show(
						"so V is C",
						By(vInC, cInV, set_order.SubsetAntisym.At(V, C)))
				})

			// K ⊗ₖ l has dimension [l : k] over K and multiplication carries it onto C,
			// the K-span of l, of that dimension: rank–nullity leaves it no kernel.
			baseChange := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀k K l:set(A).",
				Hypotheses: []string{
					"subfield(M, k)",
					"subfield(M, K)",
					"subfield(M, l)",
					"k ⊆ K",
					"k ⊆ l",
					"finite_extension(M, k, l)",
					"finite_extension(M, K, constant_composite(M, K, l))",
					"extension_degree(M, K, constant_composite(M, K, l)) = extension_degree(M, k, l)",
				},
				Conclusion: "∃p:(set(prod(A, A) → A) → A). " +
					"    module_isomorphism(«Scalars»(M, k), " +
					"        «TensorProduct»(M, k, K, l), " +
					"        «Vectors»(M, constant_composite(M, K, l)), " +
					"        p) ∧ " +
					"    (∀x a:A. x ∈ K ∧ a ∈ l ⇒ p(«PureTensor»(M, k, K, l, x, a)) = x * a)",
			},
				func(
					a *Argument,
					M field.FieldFact[on.M],
					k, K, l *Expr[Set[A]],
					subk, subK, subL, kInK, kInL, finiteL, finiteC, degrees Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					mulMonoid := comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))
					scalarsk := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, k)")
					scalarsK := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, K)")
					vectorsK := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, K)")
					vectorsL := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, l)")
					extension := a.TermAs[module_record.ModuleOps[A, _Tensor]]("«BaseChange»(M, k, K, l)")
					tensorKL := a.TermAs[module_record.ModuleOps[A, _Tensor]]("«TensorProduct»(M, k, K, l)")
					carrierKL := a.TermAs[Set[_Tensor]]("«TensorProduct»(M, k, K, l).carrier")
					C, defC := a.LetAs[Set[A]]("C", "constant_composite(M, K, l)")
					vectorsC := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, C)")
					holdsKAndL := a.Have(
						"C is a subfield holding K and l",
						"subfield(M, C) ∧ K ⊆ C ∧ l ⊆ C",
						By(Normalized, M, defC, subK, subL, At(compositeHolds, m, K, l)))
					p, mapped := a.UnpackAs[Fun[_Tensor, A]](
						GroupPremises(M, subk, subK, subL, kInK, kInL, holdsKAndL, At(multiplication, m, k, K, l, C)), "p")
					parts := a.Conjuncts(
						mapped,
						"p is K-linear on the scalar extension",
						"p is k-linear on the tensor module",
						"p multiplies on pure tensors")
					linearOverK, linearOverBase, pure := parts[0], parts[1], parts[2]
					imageSet := a.TermAs[Set[A]]("image(p, «TensorProduct»(M, k, K, l).carrier)")
					sameCarrier := a.Have(
						"the scalar extension has the tensor module's points",
						"«BaseChange»(M, k, K, l).carrier = «TensorProduct»(M, k, K, l).carrier",
						Cite(extensionPoints, m, k, K, l))
					imageSubspace := a.Have(
						"the image of p is a K-subspace of C",
						"submodule(«Scalars»(M, K), «Vectors»(M, C), image(p, «TensorProduct»(M, k, K, l).carrier))",
						sameCarrier.RwRev(),
						By(linearOverK, module_homomorphism.ImageSubmodule.At(scalarsK, extension, vectorsC, p)))
					factors := a.Have(
						"K and l are spaces over k",
						"module_on(«Scalars»(M, k), «Vectors»(M, K)) ∧ module_on(«Scalars»(M, k), «Vectors»(M, l))",
						By(
							subk,
							subK,
							subL,
							kInK,
							kInL,
							field_extension.ExtensionModuleOn.Read(M).At(k, K),
							field_extension.ExtensionModuleOn.Read(M).At(k, l)))
					lInImage := a.Have(
						"the image holds l, each x of l being the value at one ⊗ x",
						"l ⊆ image(p, «TensorProduct»(M, k, K, l).carrier)",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							member := b.Assume()
							one := b.TermAs[A]("M.one")
							unit := b.TermAs[_Tensor]("«PureTensor»(M, k, K, l, M.one, x)")
							inField := b.Have(
								"one lies in K and x in M",
								"M.one ∈ K ∧ x ∈ M.carrier",
								BySets(member, subK, subL, field.SubfieldOne.At(m, K), field.SubfieldSubset.At(m, l)))
							unitIn := b.Have(
								"one ⊗ x is a point of the tensor module",
								"«PureTensor»(M, k, K, l, M.one, x) ∈ «TensorProduct»(M, k, K, l).carrier",
								Simp(Fwd(tensor_product.TensorModuleCarrier)),
								By(factors, inField, member, tensor_product.TensorIn.At(scalarsk, vectorsK, vectorsL, one, x)))
							value := b.Have(
								"p sends it to one * x, which is x",
								"p(«PureTensor»(M, k, K, l, M.one, x)) = x",
								By(inField, member, pure.At(one, x), comm_monoid.LeftIdentityOn.Read(mulMonoid).AsFact().At(x)))
							b.Show(
								"so x is a value of p",
								By(unitIn, value, set_image.FunInImage.At(p, carrierKL, unit)))
						}))
					spanned := a.Have(
						"C is the K-span of l",
						"module_span(«Scalars»(M, K), «Vectors»(M, C), l) = C",
						By(Normalized, M, defC, subK, subL, finiteC, At(compositeSpan, m, K, l)))
					spanInImage := a.Have(
						"the image, a subspace holding l, holds the K-span of l",
						"module_span(«Scalars»(M, K), «Vectors»(M, C), l) ⊆ image(p, «TensorProduct»(M, k, K, l).carrier)",
						By(imageSubspace, lInImage, submodule.SpanLeast.At(scalarsK, vectorsC, l, imageSet)))
					onto := a.Have(
						"so p carries the tensor module onto C",
						"image(p, «TensorProduct»(M, k, K, l).carrier) = C",
						By(
							a.Simplified(spanInImage, Fwd(spanned)),
							imageSubspace,
							submodule.SubmoduleSubset.At(scalarsK, vectorsC, imageSet),
							set_order.SubsetAntisym.At(imageSet, C)))
					fieldKops := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
					fieldK := a.Have(
						"K is a field with k as a subfield",
						"field_on(restrict_field(M, K)) ∧ subfield(restrict_field(M, K), k)",
						By(subK, subk, kInK, field.SubfieldFieldOn.Read(M).At(K), field.SubfieldRestrict.At(m, K, k)))
					sameRings := a.Have(
						"read inside the field K, the rings of K and of k are the restrictions from M",
						"field_ring(restrict_field(M, K)) = «Scalars»(M, K) ∧ "+
							"restrict_ring(field_ring(restrict_field(M, K)), k) = «Scalars»(M, k)",
						Simp(Fwd(field.RestrictFieldDef), Fwd(field.FieldRingDef), Fwd(module_record.RestrictRingDef)),
						Basic())
					finiteDimension := a.Have(
						"K ⊗ₖ l has dimension [l : k] over K",
						"finite_dimensional(«Scalars»(M, K), «BaseChange»(M, k, K, l)) ∧ "+
							"module_dim(«Scalars»(M, K), «BaseChange»(M, k, K, l)) = extension_degree(M, k, l)",
						By(
							Normalized,
							sameRings,
							fieldK,
							factors,
							finiteL,
							field_extension.FiniteExtensionDef.At(m, k, l),
							field_extension.ExtensionDegreeDef.At(m, k, l),
							scalar_extension.ScalarExtensionFiniteDim.At(fieldKops, k, vectorsL)))
					dimensions := a.Conjuncts(
						finiteDimension,
						"K ⊗ₖ l is finite over K",
						"its dimension is [l : k]")
					scalarsField := a.Have(
						"the scalars K form a field",
						"ring_subfield(«Scalars»(M, K), M.inv, «Scalars»(M, K).carrier)",
						By(subK, field.SubfieldRingSubfield.Read(M).At(K, K)))
					inverse := a.TermAs[Fun[A, A]]("M.inv")
					extensionModule := module_homomorphism.HomSource.Read(linearOverK)
					targetModule := module_homomorphism.HomTarget.Read(linearOverK)
					rank := a.Have(
						"rank and nullity add up to [l : k]",
						"module_dim(«Scalars»(M, K), «KernelSpace»(M, k, K, l, C, p)) + "+
							"module_dim(«Scalars»(M, K), "+
							"    restrict_module(«Vectors»(M, C), image(p, «BaseChange»(M, k, K, l).carrier))) = "+
							"module_dim(«Scalars»(M, K), «BaseChange»(M, k, K, l))",
						By(
							scalarsField,
							targetModule,
							linearOverK,
							dimensions[0],
							module_dimension.RankNullity.Read(extensionModule).At(inverse, vectorsC, p)))
					rankIsDegree := a.Have(
						"the image is all of C, of degree [C : K]",
						"module_dim(«Scalars»(M, K), "+
							"    restrict_module(«Vectors»(M, C), image(p, «BaseChange»(M, k, K, l).carrier))) = "+
							"extension_degree(M, K, C)",
						sameCarrier.Rw(),
						onto.Rw(),
						Simp(Fwd(field_extension.ExtensionDegreeDef), Fwd(module_record.RestrictModuleDef)),
						Basic())
					kernelSet := a.TermAs[Set[_Tensor]]("«Kernel»(M, k, K, l, C, p)")
					nullity := a.Have(
						"so the kernel has dimension zero",
						"module_dim(«Scalars»(M, K), «KernelSpace»(M, k, K, l, C, p)) = 0",
						ByArith(rank, rankIsDegree, dimensions[1], degrees))
					kernelSubmodule := a.Have(
						"the kernel is a K-subspace of K ⊗ₖ l",
						"submodule(«Scalars»(M, K), «BaseChange»(M, k, K, l), «Kernel»(M, k, K, l, C, p))",
						By(linearOverK, module_homomorphism.KernelSubmodule.At(scalarsK, extension, vectorsC, p)))
					kernelModule := a.Have(
						"the kernel is a K-module",
						"module_on(«Scalars»(M, K), «KernelSpace»(M, k, K, l, C, p))",
						By(kernelSubmodule, submodule.SubmoduleModuleOn.Read(extensionModule).At(kernelSet)))
					kernelFinite := a.Have(
						"the kernel is finite over K",
						"finite_dimensional(«Scalars»(M, K), «KernelSpace»(M, k, K, l, C, p))",
						By(
							scalarsField,
							dimensions[0],
							kernelSubmodule,
							module_dimension.SubmoduleDim.Read(extensionModule).At(inverse, kernelSet)))
					injective := a.Have(
						"so the kernel is zero and p is one-to-one",
						"injective_on(«TensorProduct»(M, k, K, l).carrier, p)",
						sameCarrier.RwRev(),
						By(
							scalarsField,
							nullity,
							kernelFinite,
							linearOverK,
							module_dimension.DimZero.Read(kernelModule).At(inverse),
							module_homomorphism.KernelTrivialIffInjective.At(scalarsK, extension, vectorsC, p)))
					a.Take(p)
					a.Show(
						"a bijective k-linear map is an isomorphism",
						By(
							linearOverBase,
							injective,
							onto,
							pure,
							module_homomorphism.ModuleIsomorphismDef.At(scalarsk, tensorKL, vectorsC, p)))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					M field.FieldFact[on.M],
					k, K, l *Expr[Set[A]],
					subk, subK, subL, kInK, kInL, finiteL, finiteC, degrees Fact,
				) {
					m := a.TermAs[FieldOps[A]]("M")
					mulMonoid := comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))
					scalarsk := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, k)")
					scalarsL := a.TermAs[module_record.RingOps[A]]("«Scalars»(M, l)")
					vectorsK := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, K)")
					vectorsL := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, l)")
					composite := a.TermAs[Set[A]]("constant_composite(M, K, l)")
					vectorsC := a.TermAs[module_record.ModuleOps[A, A]]("«Vectors»(M, constant_composite(M, K, l))")
					extension := a.TermAs[module_record.ModuleOps[A, _Tensor]]("«BaseChange»(M, k, l, K)")
					tensorLK := a.TermAs[module_record.ModuleOps[A, _Tensor]]("«TensorProduct»(M, k, l, K)")
					tensorKL := a.TermAs[module_record.ModuleOps[A, _Tensor]]("«TensorProduct»(M, k, K, l)")
					holdsKAndL := a.Have(
						"the composite is a subfield holding K and l",
						"subfield(M, constant_composite(M, K, l)) ∧ "+
							"K ⊆ constant_composite(M, K, l) ∧ "+
							"l ⊆ constant_composite(M, K, l)",
						By(M, subK, subL, At(compositeHolds, m, K, l)))
					factors := a.Have(
						"l and K are spaces over k",
						"module_on(«Scalars»(M, k), «Vectors»(M, l)) ∧ module_on(«Scalars»(M, k), «Vectors»(M, K))",
						By(
							subk,
							subK,
							subL,
							kInK,
							kInL,
							field_extension.ExtensionModuleOn.Read(M).At(k, l),
							field_extension.ExtensionModuleOn.Read(M).At(k, K)))
					h, mapped := a.UnpackAs[Fun[_Tensor, A]](
						GroupPremises(
							M, subk, subL, subK, kInL, kInK, holdsKAndL, At(multiplication, m, k, l, K, composite)),
						"h")
					parts := a.Conjuncts(
						mapped,
						"h is l-linear on the scalar extension",
						"h is k-linear on the tensor module",
						"h multiplies on pure tensors")
					linearOverL, linearOverBase, pureH := parts[0], parts[1], parts[2]
					p, mapP := a.UnpackAs[Fun[_Tensor, A]](
						GroupPremises(
							M, subk, subK, subL, kInK, kInL, finiteL, finiteC, degrees, At(baseChange, m, k, K, l)),
						"p")
					partsP := a.Conjuncts(
						mapP,
						"p is an isomorphism over k",
						"p multiplies on pure tensors")
					isoP, pureP := partsP[0], partsP[1]
					s, swap := a.UnpackAs[Fun[_Tensor, _Tensor]](
						GroupPremises(factors, At(swapIsomorphism, scalarsk, vectorsL, vectorsK)), "s")
					partsS := a.Conjuncts(
						swap,
						"s is an isomorphism over k",
						"s swaps pure tensors")
					isoS, pureS := partsS[0], partsS[1]
					composed := a.TermAs[Fun[_Tensor, A]]("p ∘ s")
					isoComposite := a.Have(
						"p ∘ s is an isomorphism of l ⊗ₖ K onto the composite over k",
						"module_isomorphism(«Scalars»(M, k), "+
							"    «TensorProduct»(M, k, l, K), "+
							"    «Vectors»(M, constant_composite(M, K, l)), "+
							"    p ∘ s)",
						By(
							isoS,
							isoP,
							module_homomorphism.IsomorphismCompose.At(scalarsk, tensorLK, tensorKL, vectorsC, s, p)))
					agreePure := a.Have(
						"h and p ∘ s agree on pure tensors, products commuting",
						Statement{
							Binders:    "∀a x:A.",
							Hypotheses: []string{"a ∈ l", "x ∈ K"},
							Conclusion: "h(«PureTensor»(M, k, l, K, a, x)) = (p ∘ s)(«PureTensor»(M, k, l, K, a, x))",
						},
						Derive(func(b *Argument) {
							scalar, x := b.FixAs[A]("a"), b.FixAs[A]("x")
							members := b.Assume()
							inField := b.Have(
								"a and x lie in M",
								"a ∈ M.carrier ∧ x ∈ M.carrier",
								BySets(members, subK, subL, field.SubfieldSubset.At(m, K), field.SubfieldSubset.At(m, l)))
							b.Show(
								"both send a ⊗ x to the product a * x",
								Simp(Fwd(functions.ComposeApply)),
								By(
									members,
									inField,
									pureH.At(scalar, x),
									pureS.At(scalar, x),
									pureP.At(x, scalar),
									comm_monoid.CommOn.Read(mulMonoid).AsFact().At(scalar, x)))
						}))
					agree := a.Have(
						"so h is p ∘ s on the tensor module",
						"∀t:set(prod(A, A) → A). t ∈ «TensorProduct»(M, k, l, K).carrier ⇒ h(t) = (p ∘ s)(t)",
						Derive(func(b *Argument) {
							t := b.FixAs[_Tensor]("t")
							member := b.Simplified(b.Assume(), Fwd(tensor_product.TensorModuleCarrier))
							b.Show(
								"two k-linear maps agreeing on pure tensors agree",
								By(
									factors,
									linearOverBase,
									isoComposite,
									module_homomorphism.ModuleIsomorphismDef.At(scalarsk, tensorLK, vectorsC, composed),
									agreePure,
									member,
									tensor_product.TensorUniversalUnique.At(scalarsk, vectorsL, vectorsK, vectorsC, h, composed, t)))
						}))
					isoH := a.Have(
						"so h is an isomorphism over k",
						"module_isomorphism(«Scalars»(M, k), "+
							"    «TensorProduct»(M, k, l, K), "+
							"    «Vectors»(M, constant_composite(M, K, l)), "+
							"    h)",
						By(
							isoComposite,
							agree,
							module_homomorphism.IsomorphismCongruence.At(scalarsk, tensorLK, vectorsC, composed, h)))
					sameCarrier := a.Have(
						"the scalar extension has the tensor module's points",
						"«BaseChange»(M, k, l, K).carrier = «TensorProduct»(M, k, l, K).carrier",
						Cite(extensionPoints, m, k, l, K))
					bijective := a.Have(
						"so h is a bijection of the scalar extension onto the composite",
						"injective_on(«BaseChange»(M, k, l, K).carrier, h) ∧ "+
							"image(h, «BaseChange»(M, k, l, K).carrier) = «Vectors»(M, constant_composite(M, K, l)).carrier",
						sameCarrier.Rw(),
						By(isoH, module_homomorphism.ModuleIsomorphismDef.At(scalarsk, tensorLK, vectorsC, h)))
					a.Take(h)
					a.Show(
						"a bijective l-linear map is an isomorphism",
						By(
							linearOverL,
							bijective,
							pureH,
							module_homomorphism.ModuleIsomorphismDef.At(scalarsL, extension, vectorsC, h)))
				})
		}),
})}
