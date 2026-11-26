// right_exact.go — right exactness of the tensor product: tensoring with
// M carries an exact sequence N → L → N″ → 0 to an exact sequence
// M ⊗ N → M ⊗ L → M ⊗ N″ → 0.

package tensor_product

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// The right-exactness argument uses the source, middle and target tensor
// types and the quotient type of the middle tensor module.
type _SourceTensor = Set[Fun[Prod[B, C], A]]
type _MiddleTensor = Set[Fun[Prod[B, D], A]]
type _TargetTensor = Set[Fun[Prod[B, E], A]]
type _TensorQuotient = Set[_MiddleTensor]

// TensorRightExact — tensoring with M is right exact in the second
// argument: for modules N, L and N″, a map i: N → L and a homomorphism
// p of L onto N″ with
//
//	N → L → N″
//
// exact at L, the induced maps
//
//	M ⊗ N → M ⊗ L → M ⊗ N″
//
// are exact at M ⊗ L and the second is onto. The induced maps are
// stated through their action on pure tensors. i is any map: exactness
// places its values on N in the kernel of p, inside L.
//
// g ∘ f kills each pure tensor u ⊗ v, p(i(v)) being zero, and the pure
// tensors span M ⊗ N, so the image I of f lies in the kernel of g. For the
// other inclusion, divide M ⊗ L by I, with projection π. The pairing
// (u, w) ↦ π(u ⊗ w) is bilinear, and constant on each fiber of p, since
// each slice w ↦ π(u ⊗ w) is linear on L and kills the image of i; so it
// descends through p to a bilinear map on M × N″, and the universal
// property gives a homomorphism h out of M ⊗ N″ with
// h(u ⊗ p(w)) = π(u ⊗ w). Then h ∘ g agrees with π on the pure tensors,
// so h ∘ g = π, and whatever g kills lies in the kernel I of π. g is onto:
// each pure tensor u ⊗ y of M ⊗ N″ is g(u ⊗ w) for a preimage w of y
// under p, and the pure tensors span.
var TensorRightExact = tensorRightExactThm{family.Add(registry.ProofEntry{
	Name: "TensorRightExact",
	Key:  "prop_93f3b0721301941b",
	Build: family.Sections(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). " +
			"∀L:module_ops(A, D). " +
			"∀i:(C → D). " +
			"∀N'':module_ops(A, E). " +
			"∀p:(D → E). " +
			"∀f:(set(prod(B, C) → A) → set(prod(B, D) → A)). " +
			"∀g:(set(prod(B, D) → A) → set(prod(B, E) → A)).",
		Hypotheses: []string{
			"module_on(R, N)",
			"module_homomorphism(R, L, N'', p)",
			"exact_at(N''.zero, N.carrier, L.carrier, i, p)",
			"image(p, L.carrier) = N''.carrier",
			"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ f(tensor(R, M, N, u, v)) = tensor(R, M, L, u, i(v))",
			"∀u:B. ∀w:D. u ∈ M.carrier ∧ w ∈ L.carrier ⇒ g(tensor(R, M, L, u, w)) = tensor(R, M, N'', u, p(w))",
			"module_homomorphism(R, tensor_module(R, M, N), tensor_module(R, M, L), f)",
			"module_homomorphism(R, tensor_module(R, M, L), tensor_module(R, M, N''), g)",
		},
		Abbrev: Abbrev{
			// pi is the quotient map of M ⊗ L by the image of f, bound at its Let in the proof.
			{Name: "quotientPairing", Text: "λu:B. λw:D. pi(tensor(R, M, L, u, w))"},
		},
		Conclusion: "exact_at(tensor_relations(R, M, N''), " +
			"    tensor_product(R, M, N), " +
			"    tensor_product(R, M, L), " +
			"    f, " +
			"    g) ∧ " +
			"image(g, tensor_product(R, M, L)) = tensor_product(R, M, N'')",
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			// Chosen lifts need not be linear: their discrepancies disappear in phi.
			descendBilinear := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀M:module_ops(A, B). " +
					"∀L:module_ops(A, C). " +
					"∀N'':module_ops(A, D). " +
					"∀Q:module_ops(A, E). " +
					"∀p:(C → D). " +
					"∀phi:(B → C → E).",
				Hypotheses: []string{
					"module_on(R, M)",
					"bilinear_map(R, M, L, Q, phi)",
					"module_homomorphism(R, L, N'', p)",
					"image(p, L.carrier) = N''.carrier",
					"∀u:B. ∀w w':C. " +
						"    u ∈ M.carrier ∧ w ∈ L.carrier ∧ w' ∈ L.carrier ∧ p(w) = p(w') ⇒ phi(u, w) = phi(u, w')",
				},
				Conclusion: "∃psi:(B → D → E). " +
					"    bilinear_map(R, M, N'', Q, psi) ∧ " +
					"    (∀u:B. ∀w:C. u ∈ M.carrier ∧ w ∈ L.carrier ⇒ psi(u, p(w)) = phi(u, w))",
				Abbrev: Abbrev{
					{Name: "descended", Text: "λu:B. λy:D. phi(u, inverse_on(L.carrier, p, y))"},
				},
			}, func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]],
				L *Expr[ModuleOps[A, C]], NPrimePrime *Expr[ModuleOps[A, D]], Q *Expr[ModuleOps[A, E]],
				p *Arrow[C, D], phi *Arrow2[B, C, E],
				mModule module.ModuleFact[on.R, on.M], bilinear, pHom, onto, fiberConstant Fact) {
				lCarrier := a.TermAs[Set[C]]("L.carrier")
				lifts := a.Have(
					"every point of N'' has a chosen preimage in L",
					Statement{
						Binders: "∀y:D.",
						Hypotheses: []string{
							"y ∈ N''.carrier",
						},
						Conclusion: "inverse_on(L.carrier, p, y) ∈ L.carrier ∧ p(inverse_on(L.carrier, p, y)) = y",
					},
					By(
						onto,
						At(functions.InverseOnIn, lCarrier, p),
						At(functions.InverseOnRight, lCarrier, p),
						Normalized))
				clauses := a.Conjuncts(
					GroupPremises(bilinear, At(module_homomorphism.BilinearMapClauses.Read(mModule), L, Q, phi)),
					"L is a module",
					"Q is a module",
					"phi takes values in Q",
					"phi is additive in its first argument",
					"phi is additive in its second argument",
					"phi is homogeneous in its first argument",
					"phi is homogeneous in its second argument")
				lModule, qModule := clauses[0], clauses[1]
				phiIn, phiAddLeft, phiAddRight, phiSmulLeft, phiSmulRight :=
					clauses[2], clauses[3], clauses[4], clauses[5], clauses[6]
				pModule := module_homomorphism.HomTarget.Read(pHom)
				descended := a.TermAs[Fun2[B, D, E]]("«descended»")
				a.Take(descended)
				descendedClauses := a.Have(
					"the chosen-lift formula satisfies the five bilinear clauses",
					"(∀u:B. ∀y:D. u ∈ M.carrier ∧ y ∈ N''.carrier ⇒ «descended»(u, y) ∈ Q.carrier) ∧ "+
						"(∀u u':B. ∀y:D. "+
						"    u ∈ M.carrier ∧ u' ∈ M.carrier ∧ y ∈ N''.carrier ⇒ "+
						"    «descended»(M.add(u, u'), y) = Q.add(«descended»(u, y), «descended»(u', y))) ∧ "+
						"(∀u:B. ∀y y':D. "+
						"    u ∈ M.carrier ∧ y ∈ N''.carrier ∧ y' ∈ N''.carrier ⇒ "+
						"    «descended»(u, N''.add(y, y')) = Q.add(«descended»(u, y), «descended»(u, y'))) ∧ "+
						"(∀c:A. ∀u:B. ∀y:D. "+
						"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ y ∈ N''.carrier ⇒ "+
						"    «descended»(M.smul(c, u), y) = Q.smul(c, «descended»(u, y))) ∧ "+
						"(∀c:A. ∀u:B. ∀y:D. "+
						"    c ∈ R.carrier ∧ u ∈ M.carrier ∧ y ∈ N''.carrier ⇒ "+
						"    «descended»(u, N''.smul(c, y)) = Q.smul(c, «descended»(u, y)))",
					SplitConjAll(
						Case(
							"chosen lifts lie in L, so their phi values lie in Q",
							By(phiIn, lifts)),
						Case(
							"additivity in M uses the same chosen lift",
							By(phiAddLeft, lifts)),
						Case(
							"a lift of a sum and the sum of lifts have the same image",
							Derive(func(b *Argument) {
								u := b.FixAs[B]("u")
								y := b.FixAs[D]("y")
								yPrime := b.FixAs[D]("y'")
								members := b.Assume()
								liftY := b.TermAs[C]("inverse_on(L.carrier, p, y)")
								liftYPrime := b.TermAs[C]("inverse_on(L.carrier, p, y')")
								sum := b.TermAs[D]("N''.add(y, y')")
								liftSum := b.TermAs[C]("inverse_on(L.carrier, p, N''.add(y, y'))")
								sumLifts := b.TermAs[C]("L.add(inverse_on(L.carrier, p, y), inverse_on(L.carrier, p, y'))")
								b.Show(
									"fiber constancy replaces a lift of the sum by the sum of lifts",
									By(
										members,
										lifts.At(y),
										lifts.At(yPrime),
										lifts.At(sum),
										fiberConstant.At(u, liftSum, sumLifts),
										phiAddRight.At(u, liftY, liftYPrime),
										At(module_homomorphism.HomAdd.Read(pHom), liftY, liftYPrime),
										// A module's additive group is read in group vocabulary:
										// MulIn there is the module's sum staying in its carrier.
										At(group.MulIn.Read(module.AddGroupOn.Read(lModule)), liftY, liftYPrime),
										At(group.MulIn.Read(module.AddGroupOn.Read(pModule)), y, yPrime)))
							})),
						Case(
							"homogeneity in M uses the same chosen lift",
							By(phiSmulLeft, lifts)),
						Case(
							"a lift of a scalar multiple and the scaled lift have the same image",
							Derive(func(b *Argument) {
								c := b.FixAs[A]("c")
								u := b.FixAs[B]("u")
								y := b.FixAs[D]("y")
								members := b.Assume()
								liftY := b.TermAs[C]("inverse_on(L.carrier, p, y)")
								scaled := b.TermAs[D]("N''.smul(c, y)")
								liftScaled := b.TermAs[C]("inverse_on(L.carrier, p, N''.smul(c, y))")
								scaledLift := b.TermAs[C]("L.smul(c, inverse_on(L.carrier, p, y))")
								b.Show(
									"fiber constancy replaces a lift of the multiple by the scaled lift",
									By(
										members,
										lifts.At(y),
										lifts.At(scaled),
										fiberConstant.At(u, liftScaled, scaledLift),
										phiSmulRight.At(c, u, liftY),
										At(module_homomorphism.HomSmul.Read(pHom), c, liftY),
										At(module.SmulIn.Read(lModule), c, liftY),
										At(module.SmulIn.Read(pModule), c, y)))
							}))))
				a.Show(
					"the descended map is bilinear and agrees with phi after p",
					SplitConj(
						Case(
							"the five clauses give bilinearity on M × N''",
							By(
								mModule,
								lModule,
								qModule,
								pModule,
								descendedClauses,
								module_homomorphism.BilinearMapOfClauses.At(R, M, NPrimePrime, Q, descended))),
						Case(
							"any chosen lift of p(w) gives phi(u, w)",
							By(module_homomorphism.HomIn.Read(pHom), fiberConstant, lifts))))
			})

			constantOnFibers := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀N:module_ops(A, B). " +
					"∀L:module_ops(A, C). " +
					"∀N'':module_ops(A, D). " +
					"∀Q:module_ops(A, E). " +
					"∀i:(B → C). " +
					"∀p:(C → D). " +
					"∀h:(C → E). " +
					"∀w w':C.",
				Hypotheses: []string{
					"module_homomorphism(R, L, N'', p)",
					"module_homomorphism(R, L, Q, h)",
					"exact_at(N''.zero, N.carrier, L.carrier, i, p)",
					"∀v:B. v ∈ N.carrier ⇒ h(i(v)) = Q.zero",
					"w ∈ L.carrier",
					"w' ∈ L.carrier",
					"p(w) = p(w')",
				},
				Conclusion: "h(w) = h(w')",
			}, func(
				a *Argument,
				R *Expr[RingOps[A]],
				N *Expr[ModuleOps[A, B]],
				L *Expr[ModuleOps[A, C]],
				NPrimePrime *Expr[ModuleOps[A, D]],
				Q *Expr[ModuleOps[A, E]],
				i *Arrow[B, C],
				p *Arrow[C, D],
				h *Arrow[C, E],
				w, wPrime *Expr[C],
				pHom, hHom, exact, kills, wIn, wPrimeIn, sameImage Fact,
			) {
				difference := a.TermAs[C]("L.add(L.neg(w), w')")
				lCarrier, nCarrier := a.TermAs[Set[C]]("L.carrier"), a.TermAs[Set[B]]("N.carrier")
				targetZero, qZero := a.TermAs[D]("N''.zero"), a.TermAs[E]("Q.zero")
				inKernel := a.Have(
					"equal p-images put the difference in the kernel of p",
					"L.add(L.neg(w), w') ∈ group_kernel(N''.zero, L.carrier, p)",
					By(
						wIn,
						wPrimeIn,
						sameImage,
						At(group_homomorphism.EqIffInKernel.Read(module_homomorphism.HomGroup.Read(pHom)), w, wPrime)))
				v, vData := a.ObtainAs[B](
					"exactness expresses the difference as an incoming image",
					"∃v:B. v ∈ N.carrier ∧ L.add(L.neg(w), w') = i(v)",
					By(
						inKernel,
						exact,
						module_homomorphism.ExactAtDef.At(targetZero, nCarrier, lCarrier, i, p),
						set_basic.InImage.At(i, nCarrier, difference)))
				a.Show(
					"h kills that difference, so h takes equal values on w and w'",
					By(
						kills.At(v),
						inKernel,
						vData,
						wIn,
						wPrimeIn,
						sameImage,
						group_homomorphism.InKernel.At(targetZero, lCarrier, p, difference),
						group_homomorphism.InKernel.At(qZero, lCarrier, h, difference),
						At(group_homomorphism.EqIffInKernel.Read(module_homomorphism.HomGroup.Read(hHom)), w, wPrime)))
			})

			return ctx.Theorem(headline, func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]],
				N *Expr[ModuleOps[A, C]], L *Expr[ModuleOps[A, D]], i *Arrow[C, D],
				NPrimePrime *Expr[ModuleOps[A, E]], p *Arrow[D, E],
				f *Arrow[_SourceTensor, _MiddleTensor], g *Arrow[_MiddleTensor, _TargetTensor],
				mModule module.ModuleFact[on.R, on.M], nModule module.ModuleFact[on.R, on.N],
				pHom, exact, onto, fPure, gPure, fHom, gHom Fact) {
				modules := a.Have(
					"N is a module, and p supplies the other two module structures",
					"module_on(R, N) ∧ module_on(R, L) ∧ module_on(R, N'')",
					By(nModule, module_homomorphism.HomSource.Read(pHom), module_homomorphism.HomTarget.Read(pHom)))
				Tn, tnDef := a.LetAs[ModuleOps[A, _SourceTensor]]("Tn", "tensor_module(R, M, N)")
				Tl, tlDef := a.LetAs[ModuleOps[A, _MiddleTensor]]("Tl", "tensor_module(R, M, L)")
				Tp, tpDef := a.LetAs[ModuleOps[A, _TargetTensor]]("Tp", "tensor_module(R, M, N'')")
				tnCarrier := a.TermAs[Set[_SourceTensor]]("Tn.carrier")
				tlCarrier := a.TermAs[Set[_MiddleTensor]]("Tl.carrier")
				tpCarrier := a.TermAs[Set[_TargetTensor]]("Tp.carrier")
				tpZero := a.TermAs[_TargetTensor]("Tp.zero")
				lCarrier := a.TermAs[Set[D]]("L.carrier")
				nCarrier := a.TermAs[Set[C]]("N.carrier")
				targetZero := a.TermAs[E]("N''.zero")
				iInto := a.Have(
					"i maps N into L: exactness places its image in the kernel of p",
					"∀v:C. v ∈ N.carrier ⇒ i(v) ∈ L.carrier",
					a.ForEach(func(v *Expr[C]) Action {
						return By(
							exact,
							module_homomorphism.ExactAtDef.At(targetZero, nCarrier, lCarrier, i, p),
							set_basic.InImage.At(i, nCarrier, i.Apply(v)),
							group_homomorphism.InKernel.At(targetZero, lCarrier, p, i.Apply(v)))
					}))
				carriers := a.Have(
					"the named tensor modules have the tensor carriers and zero",
					"Tn.carrier = tensor_product(R, M, N) ∧ "+
						"Tl.carrier = tensor_product(R, M, L) ∧ "+
						"Tp.carrier = tensor_product(R, M, N'') ∧ "+
						"Tp.zero = tensor_relations(R, M, N'')",
					Simp(Fwd(tnDef), Fwd(tlDef), Fwd(tpDef), Fwd(TensorModuleCarrier), Fwd(TensorModuleZero)),
					Basic())
				carrierParts := a.Conjuncts(
					carriers,
					"the source carrier is M ⊗ N",
					"the middle carrier is M ⊗ L",
					"the target carrier is M ⊗ N''",
					"the target zero is the relations submodule")
				I, iDef := a.LetAs[Set[_MiddleTensor]]("I", "image(f, Tn.carrier)")
				a.Show(
					"tensoring preserves exactness at the middle and surjectivity at the target",
					SplitConj(
						Case(
							"exact at M ⊗ L: the image I of f and the kernel of g contain each other",
							Simp(Fwd(module_homomorphism.ExactAtDef)),
							Simp(Rev(carrierParts[0]), Rev(carrierParts[1]), Rev(carrierParts[3])),
							Simp(Rev(iDef)),
							Simp(Fwd(set_order.SubsetAntisymEq)),
							SplitConj(
								Case(
									"im f ⊆ ker g: g ∘ f kills the pure tensors, which span M ⊗ N",
									Derive(func(b *Argument) {
										gfHom := b.Have(
											"g after f is linear",
											"module_homomorphism(R, Tn, Tp, g ∘ f)",
											By(fHom, gHom, module_homomorphism.HomCompose.At(R, Tn, Tl, Tp, f, g)))
										K, kDef := b.LetAs[Set[_SourceTensor]]("K", "group_kernel(Tp.zero, Tn.carrier, g ∘ f)")
										gAfterF := b.TermAs[Fun[_SourceTensor, _TargetTensor]]("λt:set(prod(B, C) → A). g(f(t))")
										subK := b.Have(
											"the kernel of g after f is a submodule",
											"submodule(R, Tn, K)",
											By(kDef, module_homomorphism.KernelSubmodule.Read(gfHom), Normalized))
										pureCompositeZero := b.Have(
											"g after f kills each pure tensor: p kills i(v), and a tensor with zero second factor is zero",
											Statement{
												Binders: "∀u:B. ∀v:C.",
												Hypotheses: []string{
													"u ∈ M.carrier",
													"v ∈ N.carrier",
												},
												Conclusion: "g(f(tensor(R, M, N, u, v))) = tensor_relations(R, M, N'')",
											},
											b.ForEach(func(u *Expr[B]) Action {
												return b.ForEach(func(v *Expr[C]) Action {
													return By(
														fPure.At(u, v),
														gPure.At(u, i.Apply(v)),
														mModule,
														modules,
														exact,
														iInto.At(v),
														module_homomorphism.ExactComposeZero.At(targetZero, nCarrier, lCarrier, i, p, v),
														TensorZeroRight.At(R, M, NPrimePrime, u))
												})
											}))
										pureInK := b.Have(
											"each pure source tensor belongs to that kernel",
											"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N.carrier ⇒ tensor(R, M, N, u, v) ∈ K",
											Simp(Fwd(kDef), Fwd(functions.ComposeApply)),
											By(
												pureCompositeZero,
												mModule,
												modules,
												carriers,
												At(TensorIn, R, M, N),
												At(group_homomorphism.InKernel, tpZero, tnCarrier, gAfterF)))
										sourceInK := b.Have(
											"the kernel submodule therefore contains the entire source",
											"Tn.carrier ⊆ K",
											Simp(Fwd(tnDef)),
											By(tnDef, mModule, modules, subK, pureInK, TensorInduction.At(R, M, N, K)))
										kPointwise := b.Simplified(kDef, Fwd(functions.ComposeApply))
										b.Show(
											"f carries the source, all of it in the kernel of g ∘ f, into the kernel of g",
											BySets(
												kPointwise,
												iDef,
												sourceInK,
												module_homomorphism.HomIn.Read(fHom),
												At(group_homomorphism.InKernel, tpZero, tnCarrier, gAfterF),
												At(group_homomorphism.InKernel, tpZero, tlCarrier, g)))
									})),
								Case(
									"ker g ⊆ im f: projection to M ⊗ L / I factors as h ∘ g, so what g kills, the projection kills",
									Derive(func(b *Argument) {
										Q, qDef := b.LetAs[ModuleOps[A, _TensorQuotient]]("Q", "quotient_module(Tl, I)")
										pi, piDef := b.LetAs[Fun[_MiddleTensor, _TensorQuotient]]("pi", "coset_map(Tl.add, I)")
										pairing := b.TermAs[Fun2[B, D, _TensorQuotient]]("«quotientPairing»")
										subI := b.Have(
											"the incoming image I is a submodule",
											"submodule(R, Tl, I)",
											By(iDef, module_homomorphism.ImageSubmodule.Read(fHom), Normalized))
										piHom := b.Have(
											"projection to the quotient by I is linear",
											"module_homomorphism(R, Tl, Q, pi)",
											Simp(Fwd(piDef), Fwd(qDef)),
											By(module_homomorphism.HomSource.Read(gHom), subI, module_homomorphism.ProjectionHom.At(R, Tl, I)))
										kernelPi := b.Have(
											"the projection's kernel is exactly I",
											"group_kernel(I, Tl.carrier, pi) = I",
											By(
												piDef,
												subI,
												module_homomorphism.HomSource.Read(gHom),
												module_homomorphism.ProjectionKernel.At(R, Tl, I),
												Normalized))
										quotientZero := b.Have(
											"zero in the quotient is the submodule I",
											"Q.zero = I",
											Simp(Fwd(qDef), Fwd(submodule.QuotientModuleDef), Fwd(module_record.ModZeroDef)),
											Basic())
										projectionKillsImage := b.Have(
											"the quotient projection kills f's image",
											"∀x:set(prod(B, C) → A). x ∈ Tn.carrier ⇒ pi(f(x)) = Q.zero",
											By(
												iDef,
												quotientZero,
												kernelPi,
												At(set_image.FunInImage, f, tnCarrier),
												At(group_homomorphism.InKernel, I, tlCarrier, pi),
												Normalized))
										quotientPairing := b.Have(
											"the tensor pairing followed by projection is bilinear",
											"bilinear_map(R, M, L, Q, «quotientPairing»)",
											By(tlDef, mModule, modules, piHom, TensorLinearBilinear.At(R, M, L, Q, pi)))
										constantOnQ := ctx.AtTypeVars(
											constantOnFibers,
											TypeBinder.BindA[A](),
											TypeBinder.BindB[C](),
											TypeBinder.BindC[D](),
											TypeBinder.BindD[E](),
											TypeBinder.BindE[_TensorQuotient]())
										liftIndependent := b.Have(
											"projected tensors are independent of the chosen p-preimage",
											Statement{
												Binders: "∀u:B. ∀w w':D.",
												Hypotheses: []string{
													"u ∈ M.carrier",
													"w ∈ L.carrier",
													"w' ∈ L.carrier",
													"p(w) = p(w')",
												},
												Conclusion: "pi(tensor(R, M, L, u, w)) = pi(tensor(R, M, L, u, w'))",
											},
											Derive(func(c *Argument) {
												u := c.FixAs[B]("u")
												w := c.FixAs[D]("w")
												wPrime := c.FixAs[D]("w'")
												members := c.Assume()
												slice := c.TermAs[Fun[D, _TensorQuotient]]("«quotientPairing»(u)")
												sliceHom := c.Have(
													"fixing the first argument gives a linear map on L",
													"module_homomorphism(R, L, Q, «quotientPairing»(u))",
													By(members, quotientPairing, module_homomorphism.BilinearMapDef.At(R, M, L, Q, pairing)))
												kills := c.Have(
													"this linear map kills i's image",
													"∀v:C. v ∈ N.carrier ⇒ pi(tensor(R, M, L, u, i(v))) = Q.zero",
													By(
														At(fPure, u),
														projectionKillsImage,
														mModule,
														modules,
														carriers,
														members,
														At(TensorIn, R, M, N, u)))
												c.Show(
													"exactness makes the linear slice constant on each p-fiber",
													By(
														kills,
														members,
														pHom,
														sliceHom,
														exact,
														At(constantOnQ, R, N, L, NPrimePrime, Q, i, p, slice, w, wPrime)))
											}))
										descendToQ := ctx.AtTypeVars(
											descendBilinear,
											TypeBinder.BindA[A](),
											TypeBinder.BindB[B](),
											TypeBinder.BindC[D](),
											TypeBinder.BindD[E](),
											TypeBinder.BindE[_TensorQuotient]())
										psi, psiData := b.UnpackAs[Fun2[B, E, _TensorQuotient]](
											GroupPremises(
												liftIndependent,
												onto,
												mModule,
												pHom,
												quotientPairing,
												At(descendToQ, R, M, L, NPrimePrime, Q, p, pairing)),
											"psi")
										h, hData := b.ObtainAs[Fun[_TargetTensor, _TensorQuotient]](
											"the descended bilinear map induces a linear map from M ⊗ N'' to Q",
											"∃h:(set(prod(B, E) → A) → set(set(prod(B, D) → A))). "+
												"    module_homomorphism(R, Tp, Q, h) ∧ "+
												"    (∀u:B. ∀y:E. u ∈ M.carrier ∧ y ∈ N''.carrier ⇒ h(tensor(R, M, N'', u, y)) = psi(u, y))",
											By(tpDef, mModule, psiData, TensorUniversal.At(R, M, NPrimePrime, Q, psi)))
										hParts := b.Conjuncts(
											hData,
											"h is linear from the target to Q",
											"h takes each pure tensor to psi of its factors")
										hHom, hPure := hParts[0], hParts[1]
										compositeHom := b.Have(
											"h after g is linear",
											"module_homomorphism(R, Tl, Q, h ∘ g)",
											By(gHom, hHom, module_homomorphism.HomCompose.At(R, Tl, Tp, Q, g, h)))
										pointwiseHom := b.Simplified(compositeHom, Fwd(functions.ComposeApply))
										hAfterG := b.TermAs[Fun[_MiddleTensor, _TensorQuotient]]("λt:set(prod(B, D) → A). h(g(t))")
										agreePure := b.Have(
											"h after g agrees with projection on every pure tensor",
											Statement{
												Binders: "∀u:B. ∀w:D.",
												Hypotheses: []string{
													"u ∈ M.carrier",
													"w ∈ L.carrier",
												},
												Conclusion: "h(g(tensor(R, M, L, u, w))) = pi(tensor(R, M, L, u, w))",
											},
											By(module_homomorphism.HomIn.Read(pHom), gPure, hPure, psiData))
										compare := b.Have(
											"uniqueness extends this agreement to all of M ⊗ L",
											"∀t:set(prod(B, D) → A). t ∈ Tl.carrier ⇒ h(g(t)) = pi(t)",
											By(
												agreePure,
												tlDef,
												mModule,
												modules,
												carriers,
												piHom,
												pointwiseHom,
												At(TensorUniversalUnique, R, M, L, Q, hAfterG, pi)))
										b.Show(
											"anything killed by g vanishes under projection, so lies in I",
											Unfold(set_basic.SubsetDef),
											Derive(func(c *Argument) {
												x := c.FixAs[_MiddleTensor]("x")
												inKernel := c.Assume()
												c.Show(
													"h sends g(x) = zero to quotient zero, and projection has kernel I",
													By(
														compare.At(x),
														quotientZero,
														kernelPi,
														inKernel,
														module_homomorphism.HomZero.Read(hHom),
														group_homomorphism.InKernel.At(tpZero, tlCarrier, g, x),
														group_homomorphism.InKernel.At(I, tlCarrier, pi, x)))
											}))
									})))),
						Case(
							"g is onto: its image is a submodule holding every pure tensor of M ⊗ N''",
							Derive(func(b *Argument) {
								J, jDef := b.LetAs[Set[_TargetTensor]]("J", "image(g, Tl.carrier)")
								subJ := b.Have(
									"the image of g is a submodule of the target",
									"submodule(R, Tp, J)",
									By(jDef, module_homomorphism.ImageSubmodule.Read(gHom), Normalized))
								pureTargetInJ := b.Have(
									"surjectivity of p puts every pure target tensor in g's image",
									"∀u:B. ∀y:E. u ∈ M.carrier ∧ y ∈ N''.carrier ⇒ tensor(R, M, N'', u, y) ∈ J",
									Derive(func(c *Argument) {
										u := c.FixAs[B]("u")
										y := c.FixAs[E]("y")
										members := c.Assume()
										w := c.TermAs[D]("inverse_on(L.carrier, p, y)")
										t := c.TermAs[_MiddleTensor]("tensor(R, M, L, u, inverse_on(L.carrier, p, y))")
										c.Show(
											"a chosen preimage w gives g(u ⊗ w) = u ⊗ y",
											By(
												gPure.At(u, w),
												onto,
												jDef,
												mModule,
												members,
												modules,
												carriers,
												functions.InverseOnIn.At(lCarrier, p, y),
												functions.InverseOnRight.At(lCarrier, p, y),
												TensorIn.At(R, M, L, u, w),
												set_image.FunInImage.At(g, tlCarrier, t)))
									}))
								targetInJ := b.Have(
									"the image submodule holds every pure tensor, hence the target",
									"Tp.carrier ⊆ J",
									Simp(Fwd(tpDef)),
									By(tpDef, mModule, modules, subJ, pureTargetInJ, TensorInduction.At(R, M, NPrimePrime, J)))
								imageIsTarget := b.Have(
									"the image is the entire target carrier",
									"J = Tp.carrier",
									By(
										targetInJ,
										subJ,
										submodule.SubmoduleSubset.At(R, Tp, J),
										set_order.SubsetAntisym.At(J, tpCarrier)))
								b.Show(
									"read in the tensor carriers, the image J of g is all of M ⊗ N''",
									Simp(Rev(carrierParts[1]), Rev(carrierParts[2])),
									Simp(Rev(jDef), Fwd(imageIsTarget)),
									Basic())
							}))))
			})
		}),
})}
