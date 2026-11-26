// square_zero_extension.go — square-zero extensions of an algebra S over
// R by a module N over S, read through an algebra P over R with a ring
// map ε onto S: the split extension P ⋉_ε N is a ring; the graph of −γ
// over the kernel I of ε is an ideal for a conormal map γ, and the
// quotient is an extension E_γ in which (x, 0) is (0, γ(x)); a
// derivation d shears P ⋉_ε N by an automorphism carrying the graph of
// −γ₁ to that of −γ₂ when γ₂ − γ₁ is d on I, so that E_{γ₁} ≅ E_{γ₂}.
// In an extension E the inclusion i of N is additive, and its inverse i⁻¹
// on the kernel of the projection recovers N and is additive and linear
// over the projection. Back from an extension E: a lift s of ε to E reads a conormal map γ_s
// on I, (u, n) ↦ s(u) + i(n) maps P ⋉_ε N onto E with kernel the graph
// of −γ_s, so E_{γ_s} ≅ E, and two lifts differ by a derivation whose
// restriction to I is the difference of their conormal maps.

package square_zero_extension

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The clauses of a square-zero extension
// ---------------------------------------------------------------------------

// StructureHomomorphism — the structure map of E is a ring map from R.
var StructureHomomorphism = structureHomomorphismThm{family.Add(registry.ProofEntry{
	Name:  "StructureHomomorphism",
	Key:   "prop_9d7c5eef75faf21f",
	Build: SquareZeroExtension.Axiom("ring_homomorphism(R, E.ring, E.structure)"),
})}

// ProjectionHomomorphism — the projection of E is a ring map to S.
var ProjectionHomomorphism = projectionHomomorphismThm{family.Add(registry.ProofEntry{
	Name:  "ProjectionHomomorphism",
	Key:   "prop_af0310509bd06861",
	Build: SquareZeroExtension.Axiom("ring_homomorphism(E.ring, S, E.projection)"),
})}

// ProjectionOnto — the projection of E is onto S.
var ProjectionOnto = projectionOntoThm{family.Add(registry.ProofEntry{
	Name:  "ProjectionOnto",
	Key:   "prop_6e5fbf80ed344fa4",
	Build: SquareZeroExtension.Axiom("image(E.projection, E.ring.carrier) = S.carrier"),
})}

// ProjectionOverBase — the projection after the structure map is f on
// R's carrier.
var ProjectionOverBase = projectionOverBaseThm{family.Add(registry.ProofEntry{
	Name: "ProjectionOverBase",
	Key:  "prop_d7840fa732ae4955",
	Build: SquareZeroExtension.Axiom(Statement{
		Binders: "∀a:A.",
		Hypotheses: []string{
			"a ∈ R.carrier",
		},
		Conclusion: "E.projection(E.structure(a)) = f(a)",
	}),
})}

// CoefficientModule — N is a module over S.
var CoefficientModule = coefficientModuleThm{family.Add(registry.ProofEntry{
	Name:  "CoefficientModule",
	Key:   "prop_ba9a62f9f4b88742",
	Build: SquareZeroExtension.Axiom("module_on(S, N)"),
})}

// InclusionAdd — the inclusion keeps the sum.
var InclusionAdd = inclusionAddThm{family.Add(registry.ProofEntry{
	Name: "InclusionAdd",
	Key:  "prop_f3b2aa51a88bd117",
	Build: SquareZeroExtension.Axiom(Statement{
		Binders: "∀n m:D.",
		Hypotheses: []string{
			"n ∈ N.carrier",
			"m ∈ N.carrier",
		},
		Conclusion: "E.inclusion(N.add(n, m)) = E.ring.add(E.inclusion(n), E.inclusion(m))",
	}),
})}

// InclusionInjective — the inclusion is one-to-one on N.
var InclusionInjective = inclusionInjectiveThm{family.Add(registry.ProofEntry{
	Name:  "InclusionInjective",
	Key:   "prop_6eb65e64a9563326",
	Build: SquareZeroExtension.Axiom("injective_on(N.carrier, E.inclusion)"),
})}

// InclusionImage — the image of N is the kernel of the projection.
var InclusionImage = inclusionImageThm{family.Add(registry.ProofEntry{
	Name: "InclusionImage",
	Key:  "prop_277adcd6baa4740e",
	Build: SquareZeroExtension.Axiom(
		"image(E.inclusion, N.carrier) = ring_kernel(S.zero, E.ring.carrier, E.projection)"),
})}

// InclusionSquareZero — the image of N has square zero.
var InclusionSquareZero = inclusionSquareZeroThm{family.Add(registry.ProofEntry{
	Name: "InclusionSquareZero",
	Key:  "prop_4204793f8e58223c",
	Build: SquareZeroExtension.Axiom(Statement{
		Binders: "∀n m:D.",
		Hypotheses: []string{
			"n ∈ N.carrier",
			"m ∈ N.carrier",
		},
		Conclusion: "E.ring.mul(E.inclusion(n), E.inclusion(m)) = E.ring.zero",
	}),
})}

// InclusionAction — the ring of E acts on the image of N through the
// projection, as S acts on N.
var InclusionAction = inclusionActionThm{family.Add(registry.ProofEntry{
	Name: "InclusionAction",
	Key:  "prop_6c70ef0b3c8b73f7",
	Build: SquareZeroExtension.Axiom(Statement{
		Binders: "∀e:C. ∀n:D.",
		Hypotheses: []string{
			"e ∈ E.ring.carrier",
			"n ∈ N.carrier",
		},
		Conclusion: "E.ring.mul(e, E.inclusion(n)) = E.inclusion(N.smul(E.projection(e), n))",
	}),
})}

// ---------------------------------------------------------------------------
// The split extension and the graph of a conormal map
// ---------------------------------------------------------------------------

// SplitSquareZeroRing — P ⋉_ε N is a commutative ring; u ↦ (u, 0) and
// (u, n) ↦ ε(u) are ring maps; the pairs (0, n) lie in it, add as N
// does, and a pair acts on them through ε of its first component.
var SplitSquareZeroRing = splitSquareZeroRingThm{family.Add(registry.ProofEntry{
	Name: "SplitSquareZeroRing",
	Key:  "prop_3bb090b49ca2ed39",
	Reading: "No algebra over a base ring is read: the structure map of an " +
		"extension over R is h followed by the section u ↦ (u, 0), a ring map when " +
		"h is. ε a ring map is load-bearing for associativity of the product, " +
		"whose second component reads ε(uv) = ε(u)ε(v), and for the two maps.",
	Build: family.Theorem(Statement{
		Binders: "∀P:ring_ops(U). ∀S:ring_ops(B). ∀ε:(U → B). ∀N:module_ops(B, D).",
		Hypotheses: []string{
			"ring_homomorphism(P, S, ε)",
			"module_on(S, N)",
		},
		Conclusion: "comm_ring_on(split_square_zero(P, ε, N)) ∧ " +
			"ring_homomorphism(P, split_square_zero(P, ε, N), λu:U. (u, N.zero)) ∧ " +
			"ring_homomorphism(split_square_zero(P, ε, N), S, λz:prod(U, D). ε(fst(z))) ∧ " +
			"(∀n m:D. " +
			"    n ∈ N.carrier ∧ m ∈ N.carrier ⇒ " +
			"    (P.zero, n) ∈ split_square_zero(P, ε, N).carrier ∧ " +
			"    split_square_zero(P, ε, N).add((P.zero, n), (P.zero, m)) = (P.zero, N.add(n, m))) ∧ " +
			"(∀z:prod(U, D). ∀n:D. " +
			"    z ∈ split_square_zero(P, ε, N).carrier ∧ n ∈ N.carrier ⇒ " +
			"    split_square_zero(P, ε, N).mul(z, (P.zero, n)) = (P.zero, N.smul(ε(fst(z)), n)))",
		Abbrev: Abbrev{
			{Name: "scalarX", Text: "ε(fst(x))"},
			{Name: "scalarY", Text: "ε(fst(y))"},
			{Name: "scalarZ", Text: "ε(fst(z))"},
			{Name: "productXY", Text: "(«scalarX» * «scalarY») • snd(z)"},
			{Name: "productXZ", Text: "(«scalarX» * «scalarZ») • snd(y)"},
			{Name: "productYZ", Text: "(«scalarY» * «scalarZ») • snd(x)"},
			{Name: "actionXY", Text: "«scalarX» • snd(y)"},
			{Name: "actionXZ", Text: "«scalarX» • snd(z)"},
			{Name: "actionYX", Text: "«scalarY» • snd(x)"},
			{Name: "actionZX", Text: "«scalarZ» • snd(x)"},
		},
	},
		func(
			a *Argument,
			P *Expr[RingOps[U]],
			S *Expr[RingOps[B]],
			ε *Arrow[U, B],
			N *Expr[ModuleOps[B, D]],
			assumptions Fact,
		) {
			parts := a.Conjuncts(
				assumptions,
				"ε is a ring map",
				"N is an S-module")
			hom, coefficients := parts[0], parts[1]
			base := a.Have(
				"the source of ε is a commutative ring",
				"comm_ring_on(P)",
				By(hom, ring_homomorphism.Source))
			scalars := a.Have(
				"the target of ε is a commutative ring",
				"comm_ring_on(S)",
				By(hom, ring_homomorphism.Target))

			// The laws each factor supplies: P's additive group and
			// multiplicative monoid, S's multiplicative monoid, and N's
			// additive group.
			baseAdd := comm_ring.AddGroupOn.Read(base)
			baseGroup := abelian_group.GroupOn.Read(baseAdd)
			baseMul := comm_ring.MulMonoidOn.Read(base)
			baseZeroIn := comm_ring.ZeroIn.Read(base)
			scalarMul := comm_ring.MulMonoidOn.Read(scalars)
			coeffAdd := module.AddMonoidOn.Read(coefficients)
			coeffGroup := module.AddGroupOn.Read(coefficients)
			coeffSumIn := group.MulIn.Read(coeffGroup)
			coeffAssoc := group.AssocOn.Read(coeffGroup)
			coeffComm := module.AddComm.Read(coefficients)
			zeroIn := group.OneIn.Read(coeffGroup)
			zeroLeft := comm_monoid.LeftIdentityOn.Read(coeffAdd)
			zeroRight := comm_monoid.RightIdentityOn.Read(coeffAdd)
			mapIn := ring_homomorphism.MapIn.Read(hom)
			mapAdd := ring_homomorphism.MapAdd.Read(hom)
			mapMul := ring_homomorphism.MapMul.Read(hom)
			mapOne := ring_homomorphism.MapOne.Read(hom)
			smulIn := module.SmulIn.Read(coefficients)

			cross := Fwd(set_product.InCross.Inst(TypeBinder.BindA[U](), TypeBinder.BindB[D]()))
			projections := Fwd(set_product.InCrossProjections)
			fst, snd, pairEq := Fwd(pairs.Fst), Fwd(pairs.Snd), Fwd(pairs.PairEq)
			// A condition on pairs reads as the same condition on their
			// components: every pair is (u, n), membership in the product
			// and equality of pairs go component by component, and fst and
			// snd read the components off. componentwise closes a condition
			// so read by the laws of the factors it names.
			atBase, atCoeff := TypeBinder.BindA[U](), TypeBinder.BindB[D]()
			components := Simp(
				Fwd(pairs.ForallPair.Inst(atBase, atCoeff)),
				Fwd(pairs.Fst.Inst(atBase, atCoeff)),
				Fwd(pairs.Snd.Inst(atBase, atCoeff)),
				Fwd(set_product.InCross.Inst(atBase, atCoeff)),
				Fwd(pairs.PairEq.Inst(atBase, atCoeff)))
			componentwise := func(laws ...any) Action { return Chain(components, By(laws...)) }

			ring := a.Have(
				"the split operations make a commutative ring",
				"comm_ring_on(split_square_zero(P, ε, N))",
				Simp(Fwd(comm_ring.CommRingOn)),
				SplitConjAll(
					Case(
						"the sum gives an abelian group",
						Unfold(abelian_group.AbelianGroupOn),
						SplitConj(
							Case(
								"the sum gives a group",
								Unfold(group.GroupOn),
								SplitConjAll(
									Case(
										"the zero pair lies in the product",
										componentwise(baseZeroIn, zeroIn)),
									Case(
										"a sum of pairs lies in the product",
										componentwise(group.MulIn.Read(baseGroup), coeffSumIn)),
									Case(
										"so does a negative",
										componentwise(group.InvIn.Read(baseGroup), group.InvIn.Read(coeffGroup))),
									Case(
										"the sum associates componentwise",
										componentwise(group.AssocOn.Read(baseGroup), coeffAssoc)),
									Case(
										"the zero pair is a left identity componentwise",
										componentwise(group.LeftIdentityOn.Read(baseGroup), zeroLeft)),
									Case(
										"the negative is a left inverse componentwise",
										componentwise(group.LeftInverseOn.Read(baseGroup), group.LeftInverseOn.Read(coeffGroup))),
								)),
							Case(
								"the sum commutes componentwise",
								componentwise(abelian_group.CommOn.Read(baseAdd), coeffComm)),
						)),
					Case(
						"the product gives a commutative monoid",
						Unfold(comm_monoid.CommMonoidOn),
						SplitConjAll(
							Case(
								"the unit pair lies in the product",
								componentwise(comm_ring.OneIn.Read(base), zeroIn)),
							Case(
								"a product of pairs lies in the product: P is closed under products, N under the action and sums",
								componentwise(comm_monoid.OpIn.Read(baseMul), mapIn, smulIn, coeffSumIn)),
							Case(
								"the product commutes: the factors in P swap, and so do the two action terms in N",
								componentwise(comm_monoid.CommOn.Read(baseMul), mapIn, smulIn, coeffComm)),
							Case(
								"the product associates",
								Simp(projections, fst, snd, pairEq),
								Derive(func(b *Argument) {
									b.Fix("x")
									b.Fix("y")
									b.Fix("z")
									in := b.Assume()
									b.Show(
										"both components agree under reassociation",
										SplitConj(
											Case(
												"the first components associate in P",
												By(in, comm_monoid.AssocOn.Read(baseMul))),
											Case(
												"the action terms expand to a common sum",
												Simp(
													Fwd(mapMul),
													Fwd(module.SmulAddLeft.Read(coefficients)),
													Rev(module.SmulMul.Read(coefficients)),
													Fwd(mapIn),
													Fwd(smulIn)),
												Derive(func(c *Argument) {
													commutes := comm_monoid.CommOn.Read(scalarMul)
													xz := c.Have(
														"the first and third scalars commute",
														"«scalarZ» * «scalarX» = «scalarX» * «scalarZ»",
														By(in, mapIn, commutes))
													yz := c.Have(
														"the second and third scalars commute",
														"«scalarZ» * «scalarY» = «scalarY» * «scalarZ»",
														By(in, mapIn, commutes))
													summands := c.Have(
														"the three product actions lie in N",
														"«productXY» ∈ N.carrier ∧ «productXZ» ∈ N.carrier ∧ «productYZ» ∈ N.carrier",
														By(in, mapIn, comm_monoid.OpIn.Read(scalarMul), smulIn))
													regroup := c.Have(
														"associate the three module summands",
														"(«productXY» + «productXZ») + «productYZ» = «productXY» + («productXZ» + «productYZ»)",
														By(summands, coeffAssoc))
													c.Show(
														"the scalar commutations identify the regrouped sums",
														By(regroup, xz, yz))
												})),
										))
								})),
							Case(
								"the unit pair is a left identity: one acts as the identity, and the other action term is zero",
								componentwise(
									Normalized,
									comm_monoid.LeftIdentityOn.Read(baseMul),
									mapOne,
									mapIn,
									module.SmulOne.Read(coefficients),
									module.SmulZero.Read(coefficients),
									zeroRight)),
						)),
					Case(
						"the product distributes over addition",
						Simp(projections, fst, snd, pairEq),
						Derive(func(b *Argument) {
							b.Fix("x")
							b.Fix("y")
							b.Fix("z")
							in := b.Assume()
							b.Show(
								"both components distribute",
								SplitConj(
									Case(
										"the first components distribute in P",
										By(in, comm_ring.LeftDistribOn.Read(base))),
									Case(
										"both module distributive laws expand the action terms",
										Simp(
											Fwd(mapAdd),
											Fwd(module.SmulAddLeft.Read(coefficients)),
											Fwd(module.SmulAddRight.Read(coefficients)),
											Fwd(mapIn)),
										Derive(func(c *Argument) {
											summands := c.Have(
												"the four actions lie in N",
												"«actionXY» ∈ N.carrier ∧ «actionXZ» ∈ N.carrier ∧ «actionYX» ∈ N.carrier ∧ «actionZX» ∈ N.carrier",
												By(in, mapIn, smulIn))
											exchange := c.Have(
												"the middle summands commute inside the sum",
												"«actionXZ» + («actionYX» + «actionZX») = «actionYX» + («actionXZ» + «actionZX»)",
												By(summands, comm_monoid.LeftCommOn.Read(coeffAdd)))
											c.Show(
												"interchange the middle summands",
												CalcEq(
													Leg(
														c.TermAs[D]("«actionXY» + («actionXZ» + («actionYX» + «actionZX»))"),
														"associate around the first summand",
														By(summands, coeffSumIn, coeffAssoc)),
													Leg(
														c.TermAs[D]("«actionXY» + («actionYX» + («actionXZ» + «actionZX»))"),
														"interchange the middle terms",
														By(exchange)),
													FinalLeg(
														"group the two distributive products",
														By(summands, coeffSumIn, coeffAssoc))))
										})),
								))
						})),
					Case(
						"subtraction is addition of the negative: in P by its law, in N by definition",
						componentwise(comm_ring.SubAddNegOn.Read(base))),
				))

			a.Show(
				"the ring, its section and projection, and the formulas on the module pairs",
				SplitConjAll(
					Case(
						"the split ring is commutative",
						By(ring)),
					Case(
						"the zero-coefficient section is a ring map",
						Simp(Fwd(ring_homomorphism.RingHomomorphism)),
						SplitConjAll(
							Case(
								"the source P is a commutative ring",
								By(base)),
							Case(
								"the target split ring is commutative",
								By(ring)),
							Case(
								"the section lands in the product",
								Simp(cross),
								Derive(func(b *Argument) {
									b.Fix()
									in := b.Assume()
									b.Show(
										"the second component is the module zero",
										By(in, zeroIn))
								})),
							Case(
								"the section preserves sums",
								Simp(fst, snd, pairEq),
								Derive(func(b *Argument) {
									b.Fix()
									b.Fix()
									b.Assume()
									b.Show(
										"the module zeros add to zero",
										By(zeroIn, zeroLeft))
								})),
							Case(
								"the section preserves products",
								Simp(fst, snd, pairEq),
								Derive(func(b *Argument) {
									b.Fix()
									b.Fix()
									in := b.Assume()
									b.Show(
										"both scalar actions on zero vanish",
										By(Normalized, zeroIn, zeroLeft, mapIn, module.SmulZero.Read(coefficients), in))
								})),
							Case(
								"the section sends one to the unit pair",
								Refl()),
						)),
					Case(
						"ε of the first projection is a ring map",
						Simp(Fwd(ring_homomorphism.RingHomomorphism)),
						SplitConjAll(
							Case(
								"the source split ring is commutative",
								By(ring)),
							Case(
								"the target S is a commutative ring",
								By(scalars)),
							Case(
								"ε takes the first component into S",
								Simp(projections),
								Derive(func(b *Argument) {
									b.Fix()
									in := b.Assume()
									b.Show(
										"the first component belongs to P",
										By(mapIn, in))
								})),
							Case(
								"the projection preserves sums by additivity of ε",
								Simp(projections, fst),
								Derive(func(b *Argument) {
									b.Fix()
									b.Fix()
									in := b.Assume()
									b.Show(
										"apply ε to the first-component sum",
										By(mapAdd, in))
								})),
							Case(
								"the projection preserves products by multiplicativity of ε",
								Simp(projections, fst),
								Derive(func(b *Argument) {
									b.Fix()
									b.Fix()
									in := b.Assume()
									b.Show(
										"apply ε to the first-component product",
										By(mapMul, in))
								})),
							Case(
								"the projection sends one to the scalar one",
								Simp(fst),
								By(mapOne)),
						)),
					Case(
						"module pairs lie in the carrier and add by the module sum",
						Simp(
							Fwd(SplitSquareZeroDef),
							Fwd(module_record.RingCarrierDef.Inst[Prod[U, D]]()),
							Fwd(module_record.RingAddDef),
							cross,
							fst,
							snd,
							pairEq),
						StripQuant(),
						By(baseZeroIn, group.LeftIdentityOn.Read(baseGroup))),
					Case(
						"multiplying a module pair acts through ε",
						Simp(
							Fwd(SplitSquareZeroDef),
							Fwd(module_record.RingCarrierDef.Inst[Prod[U, D]]()),
							Fwd(module_record.RingMulDef),
							projections,
							fst,
							snd,
							pairEq),
						StripQuant(),
						By(
							comm_ring.MulRightZeroOn.Read(base),
							ring_homomorphism.MapZero.Read(hom),
							mapIn,
							module.ZeroSmul.Read(coefficients),
							smulIn,
							zeroRight)),
				))
		}),
})}

// TwistedGraphIdeal — for a conormal map γ the graph of −γ over the
// kernel of ε is an ideal of P ⋉_ε N.
var TwistedGraphIdeal = twistedGraphIdealThm{family.Add(registry.ProofEntry{
	Name: "TwistedGraphIdeal",
	Key:  "prop_fb4f830dd858f8cb",
	Reading: "Nothing is asked of ε but a ring map, and no extension is read: the ideal is " +
		"built from γ alone. The linearity γ(u * x) = ε(u) • γ(x) is what makes the graph " +
		"absorb the product, (u, n)(x, −γ(x)) = (ux, −ε(u) • γ(x) + ε(x) • n) with ε(x) = S.zero.",
	Deps: []registry.EntryLike{
		module_extension.TwistedGraphDef,
		SplitSquareZeroDef,
		SplitSquareZeroRing,
		partial_derivative.ConormalHom,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		module.ZeroSmul,
		module.SmulNeg,
		module.AddGroupOn,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(U). ∀S:ring_ops(B). ∀ε:(U → B). ∀N:module_ops(B, D). ∀γ:(U → D).",
		Hypotheses: []string{
			"ring_homomorphism(P, S, ε)",
			"module_on(S, N)",
			"«conormal»(γ)",
		},
		Conclusion: "ring_ideal(split_square_zero(P, ε, N), «graph»(γ))",
	},
		"unfold ring_ideal at TwistedGraphDef: a member is (x, −γ(x)) with x in I, a pair of the "+
			"carrier (KernelIdeal, ConormalHom, InCross). γ(0) = γ(0 + 0) = γ(0) + γ(0) is N.zero, so (0, "+
			"−γ(0)) is the zero pair; (x, −γ(x)) + (y, −γ(y)) = (x + y, −γ(x + y)) by additivity, x + y in "+
			"I. (u, n)(x, −γ(x)) = (ux, ε(u) • −γ(x) + ε(x) • n) (SplitSquareZeroDef), where ε(x) = S.zero "+
			"kills the second term (ZeroSmul) and ε(u) • −γ(x) = −γ(ux) (SmulNeg, ConormalHom), ux in I"),
})}

// GraphQuotientExtension — for ε onto and a conormal map γ, E_γ = (P ⋉_ε
// N)/J_γ is a square-zero extension of S by N over R; its projection
// reads the coset of (u, n) as ε(u), and the coset of (x, 0) for x in the
// kernel is the inclusion of γ(x).
var GraphQuotientExtension = graphQuotientExtensionThm{family.Add(registry.ProofEntry{
	Name: "GraphQuotientExtension",
	Key:  "prop_49c7321be055508e",
	Reading: "ε onto is load-bearing for the projection being onto S. The " +
		"last conjunct is the identity [(x, 0)] = [(0, γ(x))]: their difference " +
		"(x, −γ(x)) is a pair of the graph. It is how the extension reads γ back: " +
		"the lift u ↦ [(u, 0)] carries x in the kernel to the inclusion of γ(x).",
	Deps: []registry.EntryLike{
		SquareZeroGraphDef,
		SquareZeroExtension,
		TwistedGraphIdeal,
		module_extension.TwistedGraphDef,
		SplitSquareZeroRing,
		SplitSquareZeroDef,
		quotient_ring.IdealQuotientProjection,
		quotient_ring.IdealQuotientRingDef,
		quotient_ring.IdealQuotientProjectionDef,
		quotient_ring.CosetEqIff,
		quotient_ring.QuotientMulCoset,
		equivalence.InducedMapDef,
		quotient_group.InLeftCosets,
		partial_derivative.ConormalHom,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		functions.InjectiveOnDef,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀P:ring_ops(U). " +
			"∀h:(A → U). " +
			"∀ε:(U → B). " +
			"∀γ:(U → D).",
		Hypotheses: []string{
			"ring_homomorphism(R, P, h)",
			"ring_homomorphism(P, S, ε)",
			"∀a:A. a ∈ R.carrier ⇒ ε(h(a)) = f(a)",
			"module_on(S, N)",
			"image(ε, P.carrier) = S.carrier",
			"«conormal»(γ)",
		},
		Conclusion: "square_zero_extension(R, S, f, N, «extension»(γ)) ∧ " +
			"(∀u:U. ∀n:D. " +
			"    u ∈ P.carrier ∧ n ∈ N.carrier ⇒ " +
			"    «extension»(γ).projection( " +
			"        ideal_quotient_projection(split_square_zero(P, ε, N), «graph»(γ), (u, n))) = " +
			"    ε(u)) ∧ " +
			"(∀x:U. " +
			"    x ∈ ring_kernel(S.zero, P.carrier, ε) ⇒ " +
			"    ideal_quotient_projection(split_square_zero(P, ε, N), «graph»(γ), (x, N.zero)) = " +
			"    «extension»(γ).inclusion(γ(x)))",
	},
		"J_γ is an ideal (TwistedGraphIdeal), so the cosets are a commutative ring and the "+
			"projection onto them a ring map (IdealQuotientProjection). Two pairs are in one coset when "+
			"they differ by (x, −γ(x)), x in I (CosetEqIff, TwistedGraphDef), so ε of the first "+
			"component is one value on a coset and the chosen member gives it (InducedMapDef): the "+
			"projection is a ring map, onto as ε is, and after the structure map it is ε ∘ h = f. The "+
			"structure map is the projection after the section and h (SplitSquareZeroRing). The "+
			"inclusion is additive; it is injective, (0, n − m) in J_γ forcing x = 0 and n − m = −γ(0) = "+
			"N.zero; its image is the kernel, a coset [(u, n)] with ε(u) = S.zero being [(0, n + γ(u))]. "+
			"[(u, n)][(0, m)] = [(0, ε(u) • m)] (QuotientMulCoset, SplitSquareZeroRing) gives the action "+
			"and the square zero. The last conjunct: (x, 0) − (0, γ(x)) is in J_γ (CosetEqIff)"),
})}

// ---------------------------------------------------------------------------
// The shear by a derivation
// ---------------------------------------------------------------------------

// DerivationShearAutomorphism — for a derivation d of P over R into N
// through ε, the shear (u, n) ↦ (u, n − d(u)) is a ring automorphism of
// P ⋉_ε N with inverse the shear by −d, fixing the structure map
// a ↦ (h(a), 0) and the pairs (0, n).
var DerivationShearAutomorphism = derivationShearAutomorphismThm{family.Add(registry.ProofEntry{
	Name: "DerivationShearAutomorphism",
	Key:  "prop_d9660a23d9450e7a",
	Reading: "The Leibniz rule is exactly the shear keeping products: (uv, ε(u) • " +
		"m + ε(v) • n − d(uv)) against (u, n − d(u))(v, m − d(v)). Zero on the " +
		"constants is the shear fixing the structure map, and d(0) = 0 its fixing the " +
		"pairs (0, n). The first components are untouched, so it lies over P and over S.",
	Deps: []registry.EntryLike{
		module_extension.DerivationShearDef,
		SplitSquareZeroDef,
		SplitSquareZeroRing,
		partial_derivative.DerivationOn,
		ring_homomorphism.RingIsomorphismDef,
		ring_homomorphism.RingHomomorphism,
		module.SmulAddLeft,
		module.SmulNeg,
		module.SmulOne,
		module.AddGroupOn,
		module.AddComm,
		functions.InjectiveOnDef,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:ring_ops(U). " +
			"∀h:(A → U). " +
			"∀S:ring_ops(B). " +
			"∀ε:(U → B). " +
			"∀N:module_ops(B, D). " +
			"∀d:(U → D).",
		Hypotheses: []string{
			"ring_homomorphism(P, S, ε)",
			"module_on(S, N)",
			"«derivation»(d)",
		},
		Conclusion: "ring_isomorphism(split_square_zero(P, ε, N), " +
			"    split_square_zero(P, ε, N), " +
			"    derivation_shear(N, d)) ∧ " +
			"(∀z:prod(U, D). " +
			"    z ∈ split_square_zero(P, ε, N).carrier ⇒ " +
			"    derivation_shear(N, λu:U. N.neg(d(u)), derivation_shear(N, d, z)) = z ∧ " +
			"    derivation_shear(N, d, derivation_shear(N, λu:U. N.neg(d(u)), z)) = z) ∧ " +
			"(∀a:A. a ∈ R.carrier ⇒ derivation_shear(N, d, (h(a), N.zero)) = (h(a), N.zero)) ∧ " +
			"(∀n:D. n ∈ N.carrier ⇒ derivation_shear(N, d, (P.zero, n)) = (P.zero, n))",
	},
		"unfold DerivationShearDef and SplitSquareZeroDef at pairs (Fst, Snd, PairEq). The shear "+
			"keeps the carrier, d landing in N's (DerivationOn, InCross); it keeps sums by additivity "+
			"of d, and products by the Leibniz rule, ε(u) • (m − d(v)) + ε(v) • (n − d(u)) = ε(u) • m "+
			"+ ε(v) • n − d(uv) (SmulAddLeft, SmulNeg, AddGroupOn, AddComm); it keeps one, d(1) = d(1 "+
			"· 1) = 2 d(1) being zero (SmulOne, ε(1) = S.one). The shears by d and −d undo each other, "+
			"n − d(u) + d(u) = n, so it is injective and onto (InjectiveOnDef, RingIsomorphismDef). "+
			"d(h(a)) = N.zero by DerivationOn, and d(0) = d(0 + 0) = d(0) + d(0) is N.zero"),
})}

// ShearGraphExtensionIso — when γ₂ − γ₁ is a derivation d on the kernel,
// the shear by d carries J_{γ₁} onto J_{γ₂}, and the map it induces on
// cosets is an isomorphism of the extensions E_{γ₁} ≅ E_{γ₂}, the coset
// of z going to the coset of the shear of z.
var ShearGraphExtensionIso = shearGraphExtensionIsoThm{family.Add(registry.ProofEntry{
	Name: "ShearGraphExtensionIso",
	Key:  "prop_5d99884c3c0c8958",
	Reading: "No onto is asked: the isomorphism is one of the records whether or not " +
		"they are extensions. The sign: the shear carries (x, −γ₁(x)) to (x, −γ₁(x) − " +
		"d(x)) = (x, −γ₂(x)). The isomorphism is the named map QuotientAutoIso induces " +
		"from the shear followed by the projection, so its value at every coset is known.",
	Deps: []registry.EntryLike{
		DerivationShearAutomorphism,
		TwistedGraphIdeal,
		module_extension.TwistedGraphDef,
		SquareZeroGraphDef,
		SquareZeroIsomorphismDef,
		module_extension.DerivationShearDef,
		quotient_ring.QuotientAutoIso,
		quotient_ring.IdealQuotientProjectionDef,
		equivalence.InducedMapDef,
		quotient_ring.CosetEqIff,
		partial_derivative.ConormalHom,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀N:module_ops(B, D). " +
			"∀P:ring_ops(U). " +
			"∀h:(A → U). " +
			"∀ε:(U → B). " +
			"∀γ₁ γ₂ d:(U → D).",
		Hypotheses: []string{
			"ring_homomorphism(R, P, h)",
			"ring_homomorphism(P, S, ε)",
			"module_on(S, N)",
			"«conormal»(γ₁)",
			"«conormal»(γ₂)",
			"«derivation»(d)",
			"fun_add(γ₂, fun_neg(γ₁)) = λx:U. COND(x ∈ ring_kernel(S.zero, P.carrier, ε), d(x), N.zero)",
		},
		Conclusion: "image(derivation_shear(N, d), «graph»(γ₁)) = «graph»(γ₂) ∧ " +
			"square_zero_isomorphism(R, " +
			"    N, " +
			"    «extension»(γ₁), " +
			"    «extension»(γ₂), " +
			"    induced_map(λz:prod(U, D). " +
			"            ideal_quotient_projection(split_square_zero(P, ε, N), " +
			"                «graph»(γ₂), " +
			"                derivation_shear(N, d, z)))) ∧ " +
			"(∀z:prod(U, D). " +
			"    z ∈ split_square_zero(P, ε, N).carrier ⇒ " +
			"    induced_map(λz':prod(U, D). " +
			"            ideal_quotient_projection(split_square_zero(P, ε, N), " +
			"                «graph»(γ₂), " +
			"                derivation_shear(N, d, z')), " +
			"        ideal_quotient_projection(split_square_zero(P, ε, N), «graph»(γ₁), z)) = " +
			"    ideal_quotient_projection(split_square_zero(P, ε, N), " +
			"        «graph»(γ₂), " +
			"        derivation_shear(N, d, z)))",
	},
		"the image: at x in I the shear of (x, −γ₁(x)) is (x, −γ₁(x) − d(x)) = (x, −γ₂(x)), "+
			"the hypothesis read at x (TwistedGraphDef, DerivationShearDef); both graphs are "+
			"indexed by I, so the image is J_{γ₂}. Both graphs are ideals (TwistedGraphIdeal) and "+
			"the shear an automorphism (DerivationShearAutomorphism), so QuotientAutoIso gives "+
			"the ring isomorphism and its value on cosets. Over R, the identity on N and over S: "+
			"the shear fixes (h(a), 0) and (0, n) (DerivationShearAutomorphism) and the first "+
			"component, which the projection reads (SquareZeroGraphDef, InducedMapDef, CosetEqIff)"),
})}

// ---------------------------------------------------------------------------
// The inclusion of N and its inverse on the kernel
// ---------------------------------------------------------------------------

// InclusionIn — the inclusion carries N into the ring of the extension:
// its image is the kernel of the projection, which lies in that ring.
var InclusionIn = inclusionInThm{family.Add(registry.ProofEntry{
	Name: "InclusionIn",
	Key:  "prop_7bbcfaced9683ccc",
	Build: SquareZeroExtension.Law(Statement{
		Binders: "∀n:D.",
		Hypotheses: []string{
			"n ∈ N.carrier",
		},
		Conclusion: "E.inclusion(n) ∈ E.ring.carrier",
	},
		func(a *Argument, extension Fact, n *Expr[D], nIn Fact) {
			a.Show(
				"the image of N is the kernel of the projection, a subset of the ring",
				BySets(
					InclusionImage.Read(extension),
					nIn,
					ring_homomorphism.RingKernelDef.At(
						a.TermAs[B]("S.zero"),
						a.TermAs[Set[C]]("E.ring.carrier"),
						a.TermAs[Fun[C, B]]("E.projection"))))
		}),
})}

// InclusionAdditive — the inclusion is a homomorphism of the additive
// groups of N and of the ring of the extension: it carries N into the
// ring and keeps the sum.
var InclusionAdditive = inclusionAdditiveThm{family.Add(registry.ProofEntry{
	Name: "InclusionAdditive",
	Key:  "prop_fba8d68cd90daa57",
	Build: SquareZeroExtension.Law("group_homomorphism(module_additive_group(N), "+
		"    additive_group(E.ring), "+
		"    E.inclusion)",
		func(a *Argument, extension Fact) {
			extensionRing := ring_homomorphism.Source.Read(ProjectionHomomorphism.Read(extension))
			a.Show(
				"the vectors of N and the ring are groups under their sums, "+
					"and the inclusion carries one into the other keeping the sum",
				By(
					module.AddGroupOn.Read(CoefficientModule.Read(extension)),
					abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(extensionRing)),
					InclusionIn.Read(extension),
					InclusionAdd.Read(extension),
					group_homomorphism.GroupHomomorphism))
		}),
})}

// InclusionZero — the inclusion keeps the zero: it is a homomorphism of
// the additive groups.
var InclusionZero = inclusionZeroThm{family.Add(registry.ProofEntry{
	Name: "InclusionZero",
	Key:  "prop_30fa35fa0445723b",
	Build: SquareZeroExtension.Law("E.inclusion(N.zero) = E.ring.zero",
		func(a *Argument, extension Fact) {
			a.Show(
				"the inclusion keeps the identity of the additive groups",
				By(group_homomorphism.MapOne.Read(InclusionAdditive.Read(extension))))
		}),
})}

// InclusionNeg — the inclusion keeps the negation: it is a homomorphism
// of the additive groups.
var InclusionNeg = inclusionNegThm{family.Add(registry.ProofEntry{
	Name: "InclusionNeg",
	Key:  "prop_36d6c38e10fbaf1e",
	Build: SquareZeroExtension.Law(Statement{
		Binders: "∀n:D.",
		Hypotheses: []string{
			"n ∈ N.carrier",
		},
		Conclusion: "E.inclusion(N.neg(n)) = E.ring.neg(E.inclusion(n))",
	},
		func(a *Argument, extension Fact, n *Expr[D], nIn Fact) {
			a.Show(
				"the inclusion keeps the inverses of the additive groups",
				By(group_homomorphism.MapInv.Read(InclusionAdditive.Read(extension)), nIn))
		}),
})}

// InclusionInverse — a point e of the kernel of the projection has a
// coefficient i⁻¹(e) in N, which the inclusion sends back to e: the
// kernel is the image of N, and inverse_on chooses a preimage there.
var InclusionInverse = inclusionInverseThm{family.Add(registry.ProofEntry{
	Name: "InclusionInverse",
	Key:  "prop_b7e5818f09c75e93",
	Build: SquareZeroExtension.Law(Statement{
		Binders: "∀e:C.",
		Hypotheses: []string{
			"e ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
		},
		Conclusion: "«coefficient»(e) ∈ N.carrier ∧ E.inclusion(«coefficient»(e)) = e",
	},
		func(a *Argument, extension Fact, e *Expr[C], inKernel Fact) {
			nCarrier, inclusion := a.TermAs[Set[D]]("N.carrier"), a.TermAs[Fun[D, C]]("E.inclusion")
			inImage := a.Have(
				"e lies in the image of N, which is the kernel",
				"e ∈ image(E.inclusion, N.carrier)",
				BySets(InclusionImage.Read(extension), inKernel))
			a.Show(
				"inverse_on chooses a preimage of e in N",
				By(
					inImage,
					functions.InverseOnIn.At(nCarrier, inclusion, e),
					functions.InverseOnRight.At(nCarrier, inclusion, e)))
		}),
})}

// InclusionInverseLeft — the inverse of the inclusion recovers a vector
// of N: the inclusion is one-to-one on N.
var InclusionInverseLeft = inclusionInverseLeftThm{family.Add(registry.ProofEntry{
	Name: "InclusionInverseLeft",
	Key:  "prop_4013ad63195277",
	Build: SquareZeroExtension.Law(Statement{
		Binders: "∀n:D.",
		Hypotheses: []string{
			"n ∈ N.carrier",
		},
		Conclusion: "«coefficient»(E.inclusion(n)) = n",
	},
		func(a *Argument, extension Fact, n *Expr[D], nIn Fact) {
			a.Show(
				"the inclusion is one-to-one on N",
				By(
					InclusionInjective.Read(extension),
					nIn,
					functions.InverseOnLeft.At(a.TermAs[Set[D]]("N.carrier"), a.TermAs[Fun[D, C]]("E.inclusion"), n)))
		}),
})}

// InclusionInverseAdd — the coefficient of a sum of two points of the
// kernel is the sum of their coefficients: the inclusion sends that sum
// to the sum of the points.
var InclusionInverseAdd = inclusionInverseAddThm{family.Add(registry.ProofEntry{
	Name: "InclusionInverseAdd",
	Key:  "prop_31194e5ae62bbedf",
	Build: SquareZeroExtension.Law(Statement{
		Binders: "∀e₁ e₂:C.",
		Hypotheses: []string{
			"e₁ ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
			"e₂ ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
		},
		Conclusion: "«coefficient»(E.ring.add(e₁, e₂)) = N.add(«coefficient»(e₁), «coefficient»(e₂))",
	},
		func(a *Argument, extension Fact, e1, e2 *Expr[C], e1In, e2In Fact) {
			n1, n1Definition := a.LetAs[D]("n₁", "«coefficient»(e₁)")
			n2, n2Definition := a.LetAs[D]("n₂", "«coefficient»(e₂)")
			coefficients := a.Have(
				"the coefficients n₁, n₂ lie in N and the inclusion sends them to e₁, e₂",
				"n₁ ∈ N.carrier ∧ n₂ ∈ N.carrier ∧ E.inclusion(n₁) = e₁ ∧ E.inclusion(n₂) = e₂",
				By(n1Definition, n2Definition, e1In, e2In, InclusionInverse.Read(extension)))
			sumIn := a.Have(
				"n₁ + n₂ lies in N",
				"N.add(n₁, n₂) ∈ N.carrier",
				By(
					coefficients,
					At(group.MulIn.Read(module.AddGroupOn.Read(CoefficientModule.Read(extension))), n1, n2)))
			a.Show(
				"the inclusion sends n₁ + n₂ to e₁ + e₂, and its inverse recovers n₁ + n₂",
				CalcEq(
					Leg(
						a.TermAs[D]("«coefficient»(E.inclusion(N.add(n₁, n₂)))"),
						"e₁ + e₂ is the inclusion of n₁ + n₂",
						By(Normalized, coefficients, At(InclusionAdd.Read(extension), n1, n2))),
					FinalLeg(
						"which the inverse of the inclusion recovers",
						By(
							n1Definition,
							n2Definition,
							sumIn,
							At(InclusionInverseLeft.Read(extension), a.TermAs[D]("N.add(n₁, n₂)")))),
				))
		}),
})}

// InclusionInverseSub — the coefficient of a difference of two points of
// the kernel is the difference of their coefficients: the inclusion
// sends that difference to the difference of the points.
var InclusionInverseSub = inclusionInverseSubThm{family.Add(registry.ProofEntry{
	Name: "InclusionInverseSub",
	Key:  "prop_d1654f0217fed23c",
	Build: SquareZeroExtension.Law(Statement{
		Binders: "∀e₁ e₂:C.",
		Hypotheses: []string{
			"e₁ ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
			"e₂ ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
		},
		Conclusion: "«coefficient»(E.ring.sub(e₁, e₂)) = " +
			"N.add(«coefficient»(e₁), N.neg(«coefficient»(e₂)))",
	},
		func(a *Argument, extension Fact, e1, e2 *Expr[C], e1In, e2In Fact) {
			n1, n1Definition := a.LetAs[D]("n₁", "«coefficient»(e₁)")
			n2, n2Definition := a.LetAs[D]("n₂", "«coefficient»(e₂)")
			coefficients := a.Have(
				"the coefficients n₁, n₂ lie in N and the inclusion sends them to e₁, e₂",
				"n₁ ∈ N.carrier ∧ n₂ ∈ N.carrier ∧ E.inclusion(n₁) = e₁ ∧ E.inclusion(n₂) = e₂",
				By(n1Definition, n2Definition, e1In, e2In, InclusionInverse.Read(extension)))
			additiveGroup := module.AddGroupOn.Read(CoefficientModule.Read(extension))
			negative := a.TermAs[D]("N.neg(n₂)")
			negativeIn := a.Have(
				"−n₂ lies in N",
				"N.neg(n₂) ∈ N.carrier",
				By(coefficients, At(group.InvIn.Read(additiveGroup), n2)))
			differenceIn := a.Have(
				"n₁ − n₂ lies in N",
				"N.add(n₁, N.neg(n₂)) ∈ N.carrier",
				By(coefficients, negativeIn, At(group.MulIn.Read(additiveGroup), n1, negative)))
			points := a.Have(
				"e₁ and e₂ lie in the ring",
				"e₁ ∈ E.ring.carrier ∧ e₂ ∈ E.ring.carrier",
				BySets(
					e1In,
					e2In,
					ring_homomorphism.RingKernelDef.At(
						a.TermAs[B]("S.zero"),
						a.TermAs[Set[C]]("E.ring.carrier"),
						a.TermAs[Fun[C, B]]("E.projection"))))
			a.Show(
				"the inclusion sends n₁ − n₂ to e₁ − e₂, and its inverse recovers n₁ − n₂",
				CalcEq(
					Leg(
						a.TermAs[D]("«coefficient»(E.inclusion(N.add(n₁, N.neg(n₂))))"),
						"e₁ − e₂ is the inclusion of n₁ − n₂",
						By(
							coefficients,
							negativeIn,
							points,
							At(InclusionAdd.Read(extension), n1, negative),
							At(InclusionNeg.Read(extension), n2),
							At(
								comm_ring.SubAddNegOn.Read(ring_homomorphism.Source.Read(ProjectionHomomorphism.Read(extension))),
								e1,
								e2))),
					FinalLeg(
						"which the inverse of the inclusion recovers",
						By(
							n1Definition,
							n2Definition,
							differenceIn,
							At(InclusionInverseLeft.Read(extension), a.TermAs[D]("N.add(n₁, N.neg(n₂))")))),
				))
		}),
})}

// InclusionInverseMul — the coefficient is linear over the projection: a
// point x of the ring acts on the inclusion of n through p(x), so the
// coefficient of x · e is p(x) • i⁻¹(e).
var InclusionInverseMul = inclusionInverseMulThm{family.Add(registry.ProofEntry{
	Name: "InclusionInverseMul",
	Key:  "prop_d64db7c02b33bda7",
	Build: SquareZeroExtension.Law(Statement{
		Binders: "∀x e:C.",
		Hypotheses: []string{
			"x ∈ E.ring.carrier",
			"e ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
		},
		Conclusion: "«coefficient»(E.ring.mul(x, e)) = N.smul(E.projection(x), «coefficient»(e))",
	},
		func(a *Argument, extension Fact, x, e *Expr[C], xIn, inKernel Fact) {
			n, nDefinition := a.LetAs[D]("n", "«coefficient»(e)")
			coefficient := a.Have(
				"the coefficient n lies in N and the inclusion sends it to e",
				"n ∈ N.carrier ∧ E.inclusion(n) = e",
				By(nDefinition, inKernel, InclusionInverse.Read(extension)))
			scaledIn := a.Have(
				"p(x) • n lies in N",
				"N.smul(E.projection(x), n) ∈ N.carrier",
				By(
					CoefficientModule.Read(extension),
					coefficient,
					xIn,
					ring_homomorphism.MapIn.Read(ProjectionHomomorphism.Read(extension)),
					module.SmulIn))
			a.Show(
				"x · e is the inclusion of p(x) • n, which the inverse of the inclusion recovers",
				CalcEq(
					Leg(
						a.TermAs[D]("«coefficient»(E.inclusion(N.smul(E.projection(x), n)))"),
						"x acts on the inclusion of n through the projection",
						By(xIn, coefficient, At(InclusionAction.Read(extension), x, n))),
					FinalLeg(
						"which the inverse of the inclusion recovers",
						By(
							nDefinition,
							scaledIn,
							At(InclusionInverseLeft.Read(extension), a.TermAs[D]("N.smul(E.projection(x), n)")))),
				))
		}),
})}

// ---------------------------------------------------------------------------
// Back from an extension: lifts and the conormal map they read
// ---------------------------------------------------------------------------

// LiftExtractConormal — a lift s of ε to a square-zero extension reads a
// conormal map γ_s(x) = i⁻¹(s(x)) on the kernel of ε.
var LiftExtractConormal = liftExtractConormalThm{family.Add(registry.ProofEntry{
	Name: "LiftExtractConormal",
	Key:  "prop_431f2e4d9eb51db3",
	Reading: "γ_s is linear over P because the lift projects to ε: " +
		"the coefficient of s(u)s(x) is p(s(u)) • γ_s(x) = ε(u) • γ_s(x).",
	Deps: []registry.EntryLike{
		ExtractConormalDef,
		SquareZeroExtension,
		SquareZeroLiftDef,
		partial_derivative.ConormalHom,
		ring_homomorphism.KernelIdeal,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapIn,
		InclusionInverse,
		InclusionInverseAdd,
		InclusionInverseMul,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀P:ring_ops(U). " +
			"∀h:(A → U). " +
			"∀ε:(U → B). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀s:(U → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, P, h)",
			"ring_homomorphism(P, S, ε)",
			"square_zero_extension(R, S, f, N, E)",
			"«lift»(s)",
		},
		Conclusion: "«conormal»(«extract»(s))",
	},
		"for x in I, p(s(x)) = ε(x) = S.zero (SquareZeroLiftDef), so s(x) is in the kernel of the "+
			"projection and γ_s(x) = i⁻¹(s(x)) is its coefficient in N's carrier (InclusionInverse). "+
			"Sums and products u * x stay in I (KernelIdeal), and s(x + y) = s(x) + s(y), s(u * x) = "+
			"s(u) s(x) (MapAdd, MapMul); the coefficient is additive on the kernel and linear over the "+
			"projection, p(s(u)) = ε(u), so γ_s(x + y) = γ_s(x) + γ_s(y) and γ_s(u * x) = ε(u) • γ_s(x) "+
			"(InclusionInverseAdd, InclusionInverseMul). Off I the value is N.zero (ExtractConormalDef)"),
})}

// LiftSumSurjectiveHom — for ε onto and a lift s, (u, n) ↦ s(u) + i(n)
// is an algebra map over R from P ⋉_ε N onto the ring of the extension.
var LiftSumSurjectiveHom = liftSumSurjectiveHomThm{family.Add(registry.ProofEntry{
	Name: "LiftSumSurjectiveHom",
	Key:  "prop_16636b009b7a8452",
	Reading: "The square-zero clause kills the cross term i(n)i(m) of the product, and the " +
		"action of E on N turns s(u)i(m) into i(ε(u) • m). ε onto is load-bearing for onto: e " +
		"− s(u), for u with ε(u) = p(e), lies in the kernel of the projection, the image of N.",
	Deps: []registry.EntryLike{
		SplitSquareZeroDef,
		SplitSquareZeroRing,
		InclusionAdd,
		InclusionSquareZero,
		InclusionAction,
		SquareZeroLiftDef,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapAdd,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		ring_homomorphism.MapIn,
		ring_homomorphism.AdditiveHomomorphism,
		comm_ring.LeftDistribOn,
		comm_ring.RightDistribOn,
		comm_ring.SubAddNegOn,
		InclusionZero,
		InclusionInverse,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀P:ring_ops(U). " +
			"∀h:(A → U). " +
			"∀ε:(U → B). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀s:(U → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, P, h)",
			"ring_homomorphism(P, S, ε)",
			"image(ε, P.carrier) = S.carrier",
			"square_zero_extension(R, S, f, N, E)",
			"«lift»(s)",
		},
		Conclusion: "ring_homomorphism(split_square_zero(P, ε, N), " +
			"    E.ring, " +
			"    λz:prod(U, D). E.ring.add(s(fst(z)), E.inclusion(snd(z)))) ∧ " +
			"image(λz:prod(U, D). E.ring.add(s(fst(z)), E.inclusion(snd(z))), " +
			"    split_square_zero(P, ε, N).carrier) = " +
			"E.ring.carrier ∧ " +
			"(∀a:A. " +
			"    a ∈ R.carrier ⇒ " +
			"    (λz:prod(U, D). E.ring.add(s(fst(z)), E.inclusion(snd(z))))((h(a), N.zero)) = E.structure(a))",
	},
		"P ⋉_ε N is a commutative ring (SplitSquareZeroRing). The map keeps sums (MapAdd for "+
			"s, InclusionAdd) and one (MapOne, InclusionZero); at a product, (s(u) + i(n))(s(v) + "+
			"i(m)) = s(uv) + s(u)i(m) + s(v)i(n) + i(n)i(m) (LeftDistribOn, RightDistribOn, "+
			"MapMul), where i(n)i(m) is zero and s(u)i(m) = i(ε(u) • m) (InclusionSquareZero, "+
			"InclusionAction, SquareZeroLiftDef), the image of the product's second component. "+
			"Onto: for e in E's ring take u in P with ε(u) = p(e) (onto); e − s(u) has projection "+
			"zero, so it is i(n) for its coefficient n in N's carrier (InclusionInverse), and e = "+
			"s(u) + i(n) (SubAddNegOn). At (h(a), 0) the value is s(h(a)) + i(0) = E.structure(a)"),
})}

// LiftSumKernelAndQuotientIso — for ε onto and a lift s, the kernel of
// (u, n) ↦ s(u) + i(n) is the graph of −γ_s, and the map it induces on
// cosets is an isomorphism E_{γ_s} ≅ E of extensions, the coset of (u, n)
// going to s(u) + i(n).
var LiftSumKernelAndQuotientIso = liftSumKernelAndQuotientIsoThm{family.Add(registry.ProofEntry{
	Name: "LiftSumKernelAndQuotientIso",
	Key:  "prop_5e8eeb303c845e1c",
	Reading: "Two exits: the kernel, for a statement that computes with J_{γ_s} " +
		"itself, and the isomorphism with its value on every coset, QuotientFirstIso's " +
		"named induced map. (u, n) is in the kernel exactly when s(u) = i(−n): then " +
		"ε(u) = p(s(u)) = S.zero, u in I, and −n = γ_s(u) by injectivity.",
	Deps: []registry.EntryLike{
		LiftSumSurjectiveHom,
		LiftExtractConormal,
		ExtractConormalDef,
		module_extension.TwistedGraphDef,
		SquareZeroGraphDef,
		SquareZeroIsomorphismDef,
		SquareZeroExtension,
		SquareZeroLiftDef,
		quotient_ring.QuotientFirstIso,
		quotient_ring.IdealQuotientProjectionDef,
		equivalence.InducedMapDef,
		ring_homomorphism.RingKernelDef,
		InclusionInverse,
		InclusionNeg,
		functions.InjectiveOnDef,
		set_product.InCross,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀P:ring_ops(U). " +
			"∀h:(A → U). " +
			"∀ε:(U → B). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀s:(U → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, P, h)",
			"ring_homomorphism(P, S, ε)",
			"image(ε, P.carrier) = S.carrier",
			"square_zero_extension(R, S, f, N, E)",
			"«lift»(s)",
		},
		Conclusion: "ring_kernel(E.ring.zero, " +
			"    split_square_zero(P, ε, N).carrier, " +
			"    λz:prod(U, D). E.ring.add(s(fst(z)), E.inclusion(snd(z)))) = " +
			"«graph»(«extract»(s)) ∧ " +
			"square_zero_isomorphism(R, " +
			"    N, " +
			"    «extension»(«extract»(s)), " +
			"    E, " +
			"    induced_map(λz:prod(U, D). E.ring.add(s(fst(z)), E.inclusion(snd(z))))) ∧ " +
			"(∀z:prod(U, D). " +
			"    z ∈ split_square_zero(P, ε, N).carrier ⇒ " +
			"    induced_map(λz:prod(U, D). E.ring.add(s(fst(z)), E.inclusion(snd(z))), " +
			"        ideal_quotient_projection(split_square_zero(P, ε, N), «graph»(«extract»(s)), z)) = " +
			"    (λz:prod(U, D). E.ring.add(s(fst(z)), E.inclusion(snd(z))))(z))",
	},
		"the kernel: s(u) + i(n) = 0 gives ε(u) = p(s(u)) = −p(i(n)) = S.zero, so u is in I, and "+
			"s(u) = i(γ_s(u)) (ExtractConormalDef, InclusionInverse), so i(γ_s(u) + n) = 0 and n = "+
			"−γ_s(u) by injectivity; conversely s(x) + i(−γ_s(x)) = i(γ_s(x)) − i(γ_s(x)) = 0 "+
			"(InclusionNeg, TwistedGraphDef, RingKernelDef). With LiftSumSurjectiveHom, QuotientFirstIso "+
			"at the kernel gives the ring isomorphism and its value on cosets. Over R: [(h(a), 0)] goes "+
			"to s(h(a)) = E.structure(a); on N: [(0, n)] goes to s(0) + i(n) = i(n); over S: p(s(u) + "+
			"i(n)) = ε(u), the projection of E_{γ_s} at [(u, n)] (SquareZeroGraphDef, InducedMapDef)"),
})}

// LiftDifferenceDerivation — two lifts s₁, s₂ of ε to an extension
// differ by i ∘ d for a derivation d of P over R into N through ε, unique
// on P's carrier, and γ_{s₂} − γ_{s₁} is d on the kernel of ε.
var LiftDifferenceDerivation = liftDifferenceDerivationThm{family.Add(registry.ProofEntry{
	Name: "LiftDifferenceDerivation",
	Key:  "prop_d98d674dee368043",
	Reading: "d(u) = i⁻¹(s₂(u) − s₁(u)): the difference has projection ε(u) − ε(u) = S.zero, so " +
		"it lies in the kernel of the projection. The Leibniz rule is s₂(uv) − s₁(uv) = s₂(u)(s₂(v) " +
		"− s₁(v)) + s₁(v)(s₂(u) − s₁(u)), each term acted on through the projection. Uniqueness is " +
		"on P's carrier only, a derivation being unconstrained off it; no onto is asked.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀P:ring_ops(U). " +
			"∀h:(A → U). " +
			"∀ε:(U → B). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀s₁ s₂:(U → C).",
		Hypotheses: []string{
			"ring_homomorphism(R, P, h)",
			"ring_homomorphism(P, S, ε)",
			"square_zero_extension(R, S, f, N, E)",
			"«lift»(s₁)",
			"«lift»(s₂)",
		},
		Conclusion: "∃d:(U → D). " +
			"    «derivation»(d) ∧ " +
			"    (∀u:U. u ∈ P.carrier ⇒ «δ»(u) = E.inclusion(d(u))) ∧ " +
			"    fun_add(«extract»(s₂), fun_neg(«extract»(s₁))) = " +
			"    (λx:U. COND(x ∈ ring_kernel(S.zero, P.carrier, ε), d(x), N.zero)) ∧ " +
			"    (∀d':(U → D). " +
			"        «derivation»(d') ∧ (∀u:U. u ∈ P.carrier ⇒ «δ»(u) = E.inclusion(d'(u))) ⇒ " +
			"        ∀u:U. u ∈ P.carrier ⇒ d'(u) = d(u))",
		Abbrev: Abbrev{{Name: "δ", Text: "λu:U. E.ring.sub(s₂(u), s₁(u))"}},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[RingOps[B]],
			f *Arrow[A, B],
			N *Expr[ModuleOps[B, D]],
			P *Expr[RingOps[U]],
			h *Arrow[A, U],
			ε *Arrow[U, B],
			E *Expr[SquareZeroOps[A, B, C, D]],
			s1, s2 *Arrow[U, C],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"the presentation is an algebra over R",
				"the augmentation is a ring map",
				"E is the extension",
				"the first map lifts the augmentation",
				"the second map lifts the augmentation")
			projection := ProjectionHomomorphism.Read(given[2])
			coefficientModule := CoefficientModule.Read(given[2])
			extensionRing := ring_homomorphism.Source.Read(projection)
			presentationRing := ring_homomorphism.Source.Read(given[1])
			scalarRing := ring_homomorphism.Target.Read(given[1])
			restricted := a.Have(
				"N is a P-module through the augmentation",
				"module_on(P, scalar_restriction(ε, N))",
				By(given[1], coefficientModule, hom_module.RestrictScalarsModuleOn))
			first := a.Conjuncts(
				a.Unfolded(given[3], SquareZeroLiftDef),
				"the first lift is a ring map",
				"the first lift is over R",
				"the first lift projects to the augmentation")
			second := a.Conjuncts(
				a.Unfolded(given[4], SquareZeroLiftDef),
				"the second lift is a ring map",
				"the second lift is over R",
				"the second lift projects to the augmentation")
			liftValues := a.Have(
				"both lifts take carrier values",
				"∀u:U. u ∈ P.carrier ⇒ s₁(u) ∈ E.ring.carrier ∧ s₂(u) ∈ E.ring.carrier",
				By(first[0], second[0], ring_homomorphism.MapIn))
			kernelEquation := ring_homomorphism.RingKernelDef.At(
				a.TermAs[B]("S.zero"),
				a.TermAs[Set[C]]("E.ring.carrier"),
				a.TermAs[Fun[C, B]]("E.projection"))

			differences := a.Have(
				"the lift difference lies in the kernel of the projection",
				"∀u:U. u ∈ P.carrier ⇒ «δ»(u) ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
				Derive(func(b *Argument) {
					u := b.FixAs[U]("u")
					inP := b.Assume()
					values := b.Have(
						"the two lift values lie in the extension",
						"s₁(u) ∈ E.ring.carrier ∧ s₂(u) ∈ E.ring.carrier",
						By(liftValues.At(u), inP))
					projected := b.Have(
						"projection turns the difference into a self-difference",
						"E.projection(«δ»(u)) = S.sub(ε(u), ε(u))",
						By(projection, values, inP, first[2], second[2], ring_homomorphism.MapSub))
					scalar := b.Have(
						"the augmentation value lies in S",
						"ε(u) ∈ S.carrier",
						By(given[1], inP, ring_homomorphism.MapIn))
					killed := b.Have(
						"the projection kills the difference",
						"E.projection(«δ»(u)) = S.zero",
						ByArith(scalarRing, projected, scalar))
					differenceIn := b.Have(
						"the difference lies in the extension carrier",
						"«δ»(u) ∈ E.ring.carrier",
						By(extensionRing, values, comm_ring.SubIn))
					b.Show(
						"the projection kills the difference, a point of the ring",
						BySets(killed, differenceIn, kernelEquation))
				}))
			d, dDefinition := a.LetAs[Fun[U, D]]("d", "λu:U. «coefficient»(«δ»(u))")
			a.Take(d)
			coefficient := a.Have(
				"d is the coefficient of the lift difference",
				"∀u:U. u ∈ P.carrier ⇒ d(u) ∈ N.carrier ∧ E.inclusion(d(u)) = «δ»(u)",
				By(dDefinition, differences, InclusionInverse.Read(given[2])))
			coefficientGroup := module.AddGroupOn.Read(coefficientModule)

			additive := a.Have(
				"d preserves addition",
				"∀u v:U. u ∈ P.carrier ∧ v ∈ P.carrier ⇒ d(P.add(u, v)) = N.add(d(u), d(v))",
				Derive(func(b *Argument) {
					u := b.FixAs[U]("u")
					v := b.FixAs[U]("v")
					inP := b.Assume()
					sumIn := b.Have(
						"the sum lies in the presentation",
						"P.add(u, v) ∈ P.carrier",
						By(presentationRing, inP, comm_ring.AddIn))
					values := b.Have(
						"the four lift values lie in the extension",
						"s₁(u) ∈ E.ring.carrier ∧ s₂(u) ∈ E.ring.carrier ∧ s₁(v) ∈ E.ring.carrier ∧ s₂(v) ∈ E.ring.carrier",
						By(inP, liftValues))
					liftSums := b.Have(
						"both lifts preserve the sum",
						"s₁(P.add(u, v)) = E.ring.add(s₁(u), s₁(v)) ∧ s₂(P.add(u, v)) = E.ring.add(s₂(u), s₂(v))",
						By(inP, first[0], second[0], ring_homomorphism.MapAdd))
					differenceSum := b.Have(
						"the lift difference distributes over addition",
						"«δ»(P.add(u, v)) = E.ring.add(«δ»(u), «δ»(v))",
						Derive(func(c *Argument) {
							sumValues := c.Have(
								"the lifted sum lies in the extension",
								"s₁(P.add(u, v)) ∈ E.ring.carrier ∧ s₂(P.add(u, v)) ∈ E.ring.carrier",
								By(sumIn, liftValues))
							c.Show(
								"s₂(u + v) − s₁(u + v) regroups as δ(u) + δ(v)",
								ByArith(extensionRing, liftSums, sumValues, values))
						}))
					b.Show(
						"the coefficient of a sum of points of the kernel is the sum of their coefficients",
						CalcEq(
							Leg(
								b.TermAs[D]("«coefficient»(E.ring.add(«δ»(u), «δ»(v)))"),
								"the lift difference distributes over the sum",
								By(dDefinition, differenceSum)),
							FinalLeg(
								"and the coefficient is additive on the kernel",
								By(
									dDefinition,
									inP,
									differences.At(u),
									differences.At(v),
									InclusionInverseAdd.Read(given[2]).At(b.TermAs[C]("«δ»(u)"), b.TermAs[C]("«δ»(v)")))),
						))
				}))
			leibniz := a.Have(
				"d obeys the Leibniz rule through the augmentation",
				Statement{
					Binders: "∀u v:U.",
					Hypotheses: []string{
						"u ∈ P.carrier",
						"v ∈ P.carrier",
					},
					Conclusion: "d(P.mul(u, v)) = N.add(N.smul(ε(u), d(v)), N.smul(ε(v), d(u)))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[U]("u")
					v := b.FixAs[U]("v")
					inP := b.Assume()
					productIn := b.Have(
						"the product lies in the presentation",
						"P.mul(u, v) ∈ P.carrier",
						By(presentationRing, inP, comm_ring.MulIn))
					values := b.Have(
						"the factor and product lifts lie in the extension",
						"s₁(u) ∈ E.ring.carrier ∧ "+
							"s₂(u) ∈ E.ring.carrier ∧ "+
							"s₁(v) ∈ E.ring.carrier ∧ "+
							"s₂(v) ∈ E.ring.carrier ∧ "+
							"s₁(P.mul(u, v)) ∈ E.ring.carrier ∧ "+
							"s₂(P.mul(u, v)) ∈ E.ring.carrier",
						By(inP, productIn, liftValues))
					liftProducts := b.Have(
						"both lifts preserve the product",
						"s₁(P.mul(u, v)) = E.ring.mul(s₁(u), s₁(v)) ∧ s₂(P.mul(u, v)) = E.ring.mul(s₂(u), s₂(v))",
						By(inP, first[0], second[0], ring_homomorphism.MapMul))
					differenceProduct := b.Have(
						"the difference of the lifted products is s₂(u)δ(v) + s₁(v)δ(u)",
						"«δ»(P.mul(u, v)) = E.ring.add(E.ring.mul(s₂(u), «δ»(v)), E.ring.mul(s₁(v), «δ»(u)))",
						ByArith(extensionRing, values, liftProducts))
					s2u, s1v := b.TermAs[C]("s₂(u)"), b.TermAs[C]("s₁(v)")
					δu, δv := b.TermAs[C]("«δ»(u)"), b.TermAs[C]("«δ»(v)")
					firstProduct := b.TermAs[C]("E.ring.mul(s₂(u), «δ»(v))")
					secondProduct := b.TermAs[C]("E.ring.mul(s₁(v), «δ»(u))")
					products := b.Have(
						"s₂(u)δ(v) and s₁(v)δ(u) lie in the kernel, an ideal of the ring",
						"E.ring.mul(s₂(u), «δ»(v)) ∈ ring_kernel(S.zero, E.ring.carrier, E.projection) ∧ "+
							"E.ring.mul(s₁(v), «δ»(u)) ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
						By(
							values,
							inP,
							differences.At(u),
							differences.At(v),
							ring_ideal.IdealMul.Read(ring_homomorphism.KernelIdeal.Read(projection))))
					firstSummand := b.Have(
						"the coefficient of s₂(u)δ(v) is ε(u) • d(v), s₂ projecting to ε",
						"«coefficient»(E.ring.mul(s₂(u), «δ»(v))) = N.smul(ε(u), d(v))",
						By(
							dDefinition,
							values,
							inP,
							differences.At(v),
							second[2].At(u),
							InclusionInverseMul.Read(given[2]).At(s2u, δv)))
					secondSummand := b.Have(
						"the coefficient of s₁(v)δ(u) is ε(v) • d(u), s₁ projecting to ε",
						"«coefficient»(E.ring.mul(s₁(v), «δ»(u))) = N.smul(ε(v), d(u))",
						By(
							dDefinition,
							values,
							inP,
							differences.At(u),
							first[2].At(v),
							InclusionInverseMul.Read(given[2]).At(s1v, δu)))
					b.Show(
						"the coefficient of δ(uv) splits by additivity and by linearity over the projection",
						CalcEq(
							Leg(
								b.TermAs[D]("«coefficient»(E.ring.add(E.ring.mul(s₂(u), «δ»(v)), E.ring.mul(s₁(v), «δ»(u))))"),
								"the difference of the lifted products is s₂(u)δ(v) + s₁(v)δ(u)",
								By(dDefinition, differenceProduct)),
							Leg(
								b.TermAs[D](
									"N.add(«coefficient»(E.ring.mul(s₂(u), «δ»(v))), «coefficient»(E.ring.mul(s₁(v), «δ»(u))))"),
								"the coefficient is additive on the kernel",
								By(products, InclusionInverseAdd.Read(given[2]).At(firstProduct, secondProduct))),
							FinalLeg(
								"and linear over the projection on each summand",
								By(firstSummand, secondSummand)),
						))
				}))
			constants := a.Have(
				"d vanishes on the base algebra",
				"∀r:A. r ∈ R.carrier ⇒ d(h(r)) = N.zero",
				Derive(func(b *Argument) {
					r := b.FixAs[A]("r")
					inR := b.Assume()
					baseIn := b.Have(
						"the base constant lies in the presentation",
						"h(r) ∈ P.carrier",
						By(inR, given[0], ring_homomorphism.MapIn))
					values := b.Have(
						"both lifts of the base constant lie in the extension",
						"s₁(h(r)) ∈ E.ring.carrier ∧ s₂(h(r)) ∈ E.ring.carrier",
						By(baseIn, liftValues))
					agree := b.Have(
						"the two lifts agree on the base constant",
						"s₂(h(r)) = s₁(h(r))",
						By(Normalized, inR, first[1].At(r), second[1].At(r)))
					differenceZero := b.Have(
						"the lift difference vanishes on the base constant",
						"«δ»(h(r)) = E.ring.zero",
						ByArith(extensionRing, values, agree))
					b.Show(
						"the coefficient of zero is zero",
						CalcEq(
							Leg(
								b.TermAs[D]("«coefficient»(E.ring.zero)"),
								"the lift difference vanishes on the base constant",
								By(dDefinition, differenceZero)),
							Leg(
								b.TermAs[D]("«coefficient»(E.inclusion(N.zero))"),
								"the inclusion keeps zero",
								By(Normalized, InclusionZero.Read(given[2]))),
							FinalLeg(
								"which the inverse of the inclusion recovers",
								By(
									group.OneIn.Read(coefficientGroup),
									At(InclusionInverseLeft.Read(given[2]), b.TermAs[D]("N.zero")))),
						))
				}))
			derivation := a.Have(
				"these laws make d a derivation into the restricted module",
				"«derivation»(d)",
				By(
					constants,
					additive,
					leibniz,
					coefficient,
					restricted,
					given[0],
					partial_derivative.DerivationOn))
			extracted := a.Have(
				"the conormal extraction difference is d on the kernel and zero elsewhere",
				"fun_add(«extract»(s₂), fun_neg(«extract»(s₁))) = "+
					"(λx:U. COND(x ∈ ring_kernel(S.zero, P.carrier, ε), d(x), N.zero))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					x := b.FixAs[U]("x")
					pointwiseSum := function_module.FunAddDef.At(
						b.TermAs[Op[D]]("N.add"),
						b.TermAs[Fun[U, D]]("«extract»(s₂)"),
						b.TermAs[Fun[U, D]]("fun_neg(«extract»(s₁))"),
						x)
					pointwiseNeg := function_module.FunNegDef.At(
						b.TermAs[Fun[D, D]]("N.neg"),
						b.TermAs[Fun[U, D]]("«extract»(s₁)"),
						x)
					firstValue := ExtractConormalDef.At(P, S, ε, N, E, s1, x)
					secondValue := ExtractConormalDef.At(P, S, ε, N, E, s2, x)
					b.Cases(b.TermAs[Bool]("x ∈ ring_kernel(S.zero, P.carrier, ε)"))
					b.When(
						"on the kernel, the coefficients of the two lifts subtract to d",
						func(c *Argument, inKernel Fact) {
							kernelValue := c.Have(
								"a kernel point lies in the presentation and has zero augmentation",
								"x ∈ P.carrier ∧ ε(x) = S.zero",
								BySets(
									inKernel,
									ring_homomorphism.RingKernelDef.At(c.TermAs[B]("S.zero"), c.TermAs[Set[U]]("P.carrier"), ε)))
							values := c.Have(
								"both lifted kernel values lie in the extension",
								"s₁(x) ∈ E.ring.carrier ∧ s₂(x) ∈ E.ring.carrier",
								By(kernelValue, liftValues.At(x)))
							projected := c.Have(
								"both lifted kernel values have zero projection",
								"E.projection(s₁(x)) = S.zero ∧ E.projection(s₂(x)) = S.zero",
								By(Normalized, kernelValue, first[2].At(x), second[2].At(x)))
							liftsInKernel := c.Have(
								"both lifted kernel values lie in the kernel of the projection",
								"s₁(x) ∈ ring_kernel(S.zero, E.ring.carrier, E.projection) ∧ "+
									"s₂(x) ∈ ring_kernel(S.zero, E.ring.carrier, E.projection)",
								BySets(values, projected, kernelEquation))
							c.Show(
								"so the extraction difference at x is the coefficient of s₂(x) − s₁(x), which is d(x)",
								CalcEq(
									Leg(
										c.TermAs[D]("N.add(«coefficient»(s₂(x)), N.neg(«coefficient»(s₁(x))))"),
										"at a kernel point the extraction difference is the difference of the coefficients",
										By(inKernel, pointwiseSum, pointwiseNeg, firstValue, secondValue)),
									FinalLeg(
										"the coefficient of a difference is the difference of "+
											"the coefficients, and d(x) is the coefficient of δ(x)",
										By(
											dDefinition,
											inKernel,
											liftsInKernel,
											InclusionInverseSub.Read(given[2]).At(c.TermAs[C]("s₂(x)"), c.TermAs[C]("s₁(x)")))),
								))
						})
					b.Otherwise(
						"outside the kernel, both extraction values are zero",
						func(c *Argument, outside Fact) {
							zeroDifference := c.Have(
								"the difference of two zero coefficients is zero",
								"N.add(N.zero, N.neg(N.zero)) = N.zero",
								By(coefficientGroup, group.OneIn, group.RightInverseOn))
							c.Show(
								"so the extraction difference at x is 0 − 0 = 0",
								By(outside, zeroDifference, pointwiseSum, pointwiseNeg, firstValue, secondValue))
						})
				}))
			unique := a.Have(
				"the derivation is unique on the presentation carrier",
				Statement{
					Binders: "∀d':(U → D).",
					Hypotheses: []string{
						"«derivation»(d')",
						"∀u:U. u ∈ P.carrier ⇒ «δ»(u) = E.inclusion(d'(u))",
					},
					Conclusion: "∀u:U. u ∈ P.carrier ⇒ d'(u) = d(u)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[U, D]]("d'")
					competitor := b.Assume()
					b.FixAs[U]("u")
					inP := b.Assume()
					otherValue := b.Have(
						"d'(u) lies in N and the inclusion sends it to δ(u)",
						"d'(u) ∈ N.carrier ∧ E.inclusion(d'(u)) = «δ»(u)",
						By(inP, competitor, partial_derivative.DerivationOn))
					b.Show(
						"the inverse of the inclusion recovers d'(u) from δ(u), and that is d(u)",
						CalcEq(
							Leg(
								b.TermAs[D]("«coefficient»(E.inclusion(d'(u)))"),
								"the inverse of the inclusion recovers d'(u)",
								By(otherValue, At(InclusionInverseLeft.Read(given[2]), b.TermAs[D]("d'(u)")))),
							FinalLeg(
								"and the inclusion of d'(u) is δ(u), whose coefficient is d(u)",
								By(otherValue, dDefinition)),
						))
				}))
			a.Show(
				"d has the required derivation, extraction, and uniqueness properties",
				By(coefficient, unique, extracted, derivation))
		}),
})}
