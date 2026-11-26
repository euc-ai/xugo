// free.go — freeness and finite generation over a principal ideal
// domain: a linear functional splits a submodule along one scalar, so a
// submodule of a module with a finite basis is free of no larger rank; a
// finitely generated torsion-free module is free, and conversely a module
// with a finite basis is finitely generated; inside a field, finite
// generation passes down a tower of rings R ⊆ S, so a finitely generated
// module over S, S itself finitely generated over the principal ideal
// domain R, is free over R; and a submodule of a finitely generated
// module is finitely generated.

package principal_ideal_domain

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// LinearFunctionalSplit — over a principal ideal domain a linear
// functional φ on M splits a submodule U along one scalar d: φ(U) is the
// ideal d·R; for d = R.zero φ kills U, and otherwise a vector b of U with
// φ(b) = d writes each v of U, in one way only, as a vector of U that φ
// kills plus a multiple a • b. The image of U is an ideal of R, so
// principal; d lies in it, so d = φ(b); φ(v) = d·a puts v + -(a • b) in U
// with φ-value d·a - a·d = R.zero; and a second pair has a'·d = φ(v) =
// d·a, so a' = a, the domain cancelling the nonzero d, and then u' = u.
var LinearFunctionalSplit = linearFunctionalSplitThm{family.Add(registry.ProofEntry{
	Name: "LinearFunctionalSplit",
	Key:  "prop_6af008ed32b8fa71",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀U:set(B). ∀φ:(B → A).",
		Hypotheses: []string{
			"principal_ideal_domain(R)",
			"submodule(R, M, U)",
			"module_homomorphism(R, M, regular_module(R), φ)",
		},
		Conclusion: "∃d:A. " +
			"    d ∈ R.carrier ∧ " +
			"    image(φ, U) = image(R.mul(d), R.carrier) ∧ " +
			"    (d = R.zero ⇒ ∀v:B. v ∈ U ⇒ φ(v) = R.zero) ∧ " +
			"    (d ≠ R.zero ⇒ " +
			"        ∃b:B. " +
			"            b ∈ U ∧ " +
			"            φ(b) = d ∧ " +
			"            (∀v:B. " +
			"                v ∈ U ⇒ " +
			"                ∃u:B. ∃a:A. " +
			"                    u ∈ U ∧ " +
			"                    φ(u) = R.zero ∧ " +
			"                    a ∈ R.carrier ∧ " +
			"                    v = u + a • b ∧ " +
			"                    (∀u':B. ∀a':A. " +
			"                        u' ∈ U ∧ φ(u') = R.zero ∧ a' ∈ R.carrier ∧ v = u' + a' • b ⇒ " +
			"                        u' = u ∧ a' = a)))",
		Abbrev: Abbrev{
			{Name: "liftSplits", Text: "∀v:B. " +
				"    v ∈ U ⇒ " +
				"    ∃u:B. ∃a:A. " +
				"        u ∈ U ∧ " +
				"        φ(u) = R.zero ∧ " +
				"        a ∈ R.carrier ∧ " +
				"        v = u + a • b ∧ " +
				"        (∀u':B. ∀a':A. " +
				"            u' ∈ U ∧ φ(u') = R.zero ∧ a' ∈ R.carrier ∧ v = u' + a' • b ⇒ u' = u ∧ a' = a)"},
		},
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			U *Expr[Set[B]],
			φ *Arrow[B, A],
			hypotheses Fact,
		) {
			given := arg.Conjuncts(
				hypotheses,
				"R is a principal ideal domain",
				"U is a submodule of M",
				"φ is linear")
			pid, sub, linear := given[0], given[1], given[2]
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			regular := arg.TermAs[ModuleOps[A, A]]("regular_module(R)")
			ring, additive := module.RingOn.Read(moduleOn), module.AddGroupOn.Read(moduleOn)
			ofPID := arg.Conjuncts(
				arg.Unfolded(pid, PrincipalIdealDomainDef),
				"R is an integral domain",
				"every ideal of R is principal")
			domain, principal := ofPID[0], ofPID[1]
			uInM := arg.Have(
				"U lies in M",
				"U ⊆ M.carrier",
				By(submodule.SubmoduleSubset.Read(sub)))
			inM := arg.Unfolded(uInM, set_basic.SubsetDef)

			imageSub := arg.Have(
				"φ carries the submodule U to a submodule of R, a module over itself",
				"submodule(R, regular_module(R), image(φ, U))",
				By(linear, sub, module_homomorphism.HomImageSubmodule.At(R, M, regular, φ, U)))
			ideal := arg.Have(
				"so the image of U is an ideal of R",
				"ring_ideal(R, image(φ, U))",
				By(
					imageSub,
					ring_ideal.RingIdealDef,
					submodule.SubmoduleSubset.Read(imageSub),
					submodule.SubmoduleZero.Read(imageSub),
					submodule.SubmoduleAdd.Read(imageSub),
					submodule.SubmoduleSmul.Read(imageSub)))
			d, generated := arg.ObtainAs[A](
				"and so the ideal d·R of one scalar d",
				"∃d:A. d ∈ R.carrier ∧ image(φ, U) = image(R.mul(d), R.carrier)",
				By(ideal, principal.At(arg.TermAs[Set[A]]("image(φ, U)"))))
			generator := arg.Conjuncts(
				generated,
				"d is a scalar",
				"the image of U is d·R")
			dIn, imageIsMultiples := generator[0], generator[1]
			dR := arg.TermAs[Fun[A, A]]("R.mul(d)")
			carrier := arg.TermAs[Set[A]]("R.carrier")

			multiples := arg.Have(
				"φ sends each vector of U to a multiple of d",
				"∀v:B. v ∈ U ⇒ ∃a:A. φ(v) = d * a ∧ a ∈ R.carrier",
				Derive(func(c *Argument) {
					v := c.FixAs[B]("v")
					vIn := c.Assume()
					inImage := c.Have(
						"φ(v) lies in the image of U, which is d·R",
						"φ(v) ∈ image(R.mul(d), R.carrier)",
						By(Normalized, vIn, imageIsMultiples, set_image.FunInImage.At(φ, U, v)))
					c.Show(
						"so φ(v) is d·a for a scalar a",
						By(inImage, set_basic.InImage.At(dR, carrier, φ.Apply(v))))
				}))

			killed := arg.Have(
				"when d is R.zero, φ kills U: each φ(v) is R.zero·a",
				"d = R.zero ⇒ ∀v:B. v ∈ U ⇒ φ(v) = R.zero",
				Derive(func(c *Argument) {
					zero := c.Assume()
					v := c.FixAs[B]("v")
					vInU := c.Assume()
					a, value := c.UnpackAs[A](GroupPremises(vInU, multiples.At(v)), "a")
					parts := c.Conjuncts(
						value,
						"φ(v) is d·a",
						"a is a scalar")
					am := c.MemberOf[on.R](a, parts[1])
					c.Show(
						"and R.zero·a = R.zero",
						By(Normalized, parts[0], zero, comm_ring.MulLeftZeroOn.Read(ring).At(am)))
				}))

			split := arg.Have(
				"when d is not R.zero, a vector b of U with φ(b) = d splits U",
				Statement{
					Hypotheses: []string{
						"d ≠ R.zero",
					},
					Conclusion: "∃b:B. " +
						"    b ∈ U ∧ " +
						"    φ(b) = d ∧ " +
						"    (∀v:B. " +
						"        v ∈ U ⇒ " +
						"        ∃u:B. ∃a:A. " +
						"            u ∈ U ∧ " +
						"            φ(u) = R.zero ∧ " +
						"            a ∈ R.carrier ∧ " +
						"            v = u + a • b ∧ " +
						"            (∀u':B. ∀a':A. " +
						"                u' ∈ U ∧ φ(u') = R.zero ∧ a' ∈ R.carrier ∧ v = u' + a' • b ⇒ u' = u ∧ a' = a))",
				},
				Derive(func(side *Argument) {
					nonzero := side.Assume()
					dm := side.MemberOf[on.R](d, dIn)
					one := comm_ring.OneIn.Read(ring)
					unit := side.Have(
						"d·R.one is d",
						"d * R.one = d",
						ByArith(ring, dIn))
					dInMultiples := side.Have(
						"d = d·R.one lies in d·R",
						"d ∈ image(R.mul(d), R.carrier)",
						By(Normalized, one, unit, set_image.FunInImage.At(dR, carrier, side.TermAs[A]("R.one"))))
					dInImage := side.Have(
						"so d lies in the image of U",
						"d ∈ image(φ, U)",
						By(Normalized, dInMultiples, imageIsMultiples))
					b, lifted := side.UnpackAs[B](side.Simplified(dInImage, Fwd(set_basic.InImage)), "b")
					lift := side.Conjuncts(
						lifted,
						"d is φ(b)",
						"b lies in U")
					bValue, bIn := lift[0], lift[1]
					bm := side.MemberOf[on.M](b, GroupPremises(lift[1], inM.At(b)))

					decomposition := side.Have(
						"each v of U is, in one way, a vector of U that φ kills plus a multiple of b",
						"«liftSplits»",
						Derive(func(c *Argument) {
							v := c.FixAs[B]("v")
							vIn := c.Assume()
							a, value := c.UnpackAs[A](GroupPremises(vIn, multiples.At(v)), "a")
							parts := c.Conjuncts(
								value,
								"φ(v) is d·a",
								"a is a scalar")
							vValue, aIn := parts[0], parts[1]
							am := c.MemberOf[on.R](a, aIn)
							vm := c.MemberOf[on.M](v, GroupPremises(vIn, inM.At(v)))
							multiple := module.SmulIn.Read(moduleOn).At(am, bm)
							negated := group.InvIn.Read(additive).At(multiple)
							u := c.TermAs[B]("v + -(a • b)")
							um := group.MulIn.Read(additive).At(vm, negated)

							uIn := c.Have(
								"u = v + -(a • b) lies in U",
								"v + -(a • b) ∈ U",
								By(vIn, bIn, aIn, submodule.SubmoduleSub.Read(sub), submodule.SubmoduleSmul.Read(sub)))
							scaled := c.Have(
								"φ(a • b) is a·d",
								"φ(a • b) = a * d",
								By(Normalized, bValue, module_homomorphism.HomSmul.Read(linear).AsFact().At(a, b), aIn, bm))
							killsU := c.Have(
								"φ kills u: φ(v) - φ(a • b) = d·a - a·d",
								"φ(v + -(a • b)) = R.zero",
								CalcEq(
									Leg(
										c.TermAs[A]("φ(v) + φ(-(a • b))"),
										"φ is additive",
										By(module_homomorphism.HomAdd.Read(linear).AsFact().At(v, c.TermAs[B]("-(a • b)")), vm, negated)),
									Leg(
										c.TermAs[A]("φ(v) + -φ(a • b)"),
										"and keeps negatives",
										By(
											Normalized,
											linear,
											multiple,
											module_homomorphism.HomNeg.At(R, M, regular, φ, c.TermAs[B]("a • b")))),
									Leg(
										c.TermAs[A]("d * a + -(a * d)"),
										"φ(v) is d·a and φ(a • b) is a·d",
										By(Normalized, vValue, scaled)),
									FinalLeg(
										"which is R.zero in the commutative ring R",
										ByArith(ring, aIn, dIn)),
								))
							recovers := c.Have(
								"and u + a • b is v",
								"v = v + -(a • b) + a • b",
								CalcEq(
									Leg(
										c.TermAs[B]("v + M.zero"),
										"M.zero is the additive identity",
										By(group.RightIdentityOn.Read(additive).At(vm))),
									Leg(
										c.TermAs[B]("v + (-(a • b) + a • b)"),
										"-(a • b) + a • b is M.zero",
										By(group.LeftInverseOn.Read(additive).At(multiple))),
									FinalLeg(
										"regrouping",
										By(group.AssocOn.Read(additive).At(vm, negated, multiple))),
								))

							unique := c.Have(
								"a second such pair is this one",
								Statement{
									Binders: "∀u':B. ∀a':A.",
									Hypotheses: []string{
										"u' ∈ U",
										"φ(u') = R.zero",
										"a' ∈ R.carrier",
										"v = u' + a' • b",
									},
									Conclusion: "u' = v + -(a • b) ∧ a' = a",
								},
								Derive(func(w *Argument) {
									u2 := w.FixAs[B]("u'")
									a2 := w.FixAs[A]("a'")
									other := w.Conjuncts(
										w.Assume(),
										"u' lies in U",
										"φ kills u'",
										"a' is a scalar",
										"v is u' + a' • b")
									a2m := w.MemberOf[on.R](a2, other[2])
									u2m := w.MemberOf[on.M](u2, GroupPremises(other[0], inM.At(u2)))
									multiple2 := module.SmulIn.Read(moduleOn).At(a2m, bm)
									again := w.Have(
										"so φ(v) is a'·d as well",
										"φ(v) = a' * d",
										CalcEq(
											Leg(
												w.TermAs[A]("φ(u' + a' • b)"),
												"v is u' + a' • b",
												By(Normalized, other[3])),
											Leg(
												w.TermAs[A]("φ(u') + φ(a' • b)"),
												"φ is additive",
												By(module_homomorphism.HomAdd.Read(linear).AsFact().At(u2, w.TermAs[B]("a' • b")), u2m, multiple2)),
											Leg(
												w.TermAs[A]("R.zero + a' * d"),
												"φ kills u', and φ(a' • b) is a'·φ(b) = a'·d",
												By(
													Normalized,
													other[1],
													bValue,
													module_homomorphism.HomSmul.Read(linear).AsFact().At(a2, b),
													other[2],
													bm)),
											FinalLeg(
												"R.zero is the additive identity of R",
												ByArith(ring, other[2], dIn)),
										))
									sameProduct := w.Have(
										"so a'·d and d·a are both φ(v)",
										"a' * d = d * a",
										By(Normalized, again, vValue))
									difference := w.Have(
										"then (a' - a)·d = a'·d - d·a = R.zero",
										"(a' - a) * d = R.zero",
										ByArith(ring, sameProduct, other[2], aIn, dIn))
									gap := comm_ring.SubIn.Read(ring).At(a2m, am)
									vanishes := w.Have(
										"so a' - a = R.zero, the domain cancelling the nonzero d",
										"a' - a = R.zero",
										By(
											difference,
											nonzero,
											gap,
											dm,
											integral_domain.NoZeroDivisors.Read(domain).AsFact().At(w.TermAs[A]("a' - a"), d)))
									sameScalar := w.Have(
										"that is, a' = a",
										"a' = a",
										CalcEq(
											Leg(
												w.TermAs[A]("(a' - a) + a"),
												"a' is (a' - a) + a in the ring R",
												ByArith(ring, other[2], aIn)),
											Leg(
												w.TermAs[A]("R.zero + a"),
												"and a' - a is R.zero",
												vanishes.Rw(),
												Basic()),
											FinalLeg(
												"R.zero is the additive identity of R",
												ByArith(ring, aIn)),
										))
									sameSum := w.Have(
										"so u' + a • b and u + a • b are both v",
										"u' + a • b = v + -(a • b) + a • b",
										recovers.RwRev(),
										sameScalar.RwRev(),
										By(other[3]))
									w.Show(
										"and cancelling a • b, the second pair is (u, a)",
										By(sameSum, group.RightCancelOn.Read(additive).At(multiple, u2m, um), sameScalar))
								}))
							c.Take(u)
							c.Take(a)
							c.Show(
								"u and a split v",
								By(uIn, killsU, aIn, recovers, unique))
						}))
					side.Take(b)
					side.Show(
						"b lifts d and splits U",
						By(bIn, bValue, decomposition))
				}))

			arg.Take(d)
			arg.Show(
				"d generates the image, and the two cases are as claimed",
				By(dIn, imageIsMultiples, killed, split))
		}),
})}

// CoordinateProjectionSplit — over a principal ideal domain the last
// coordinate splits a submodule M of the free module on the indices below
// n + 1 along one scalar d: the values v(n) of the vectors of M are the
// multiples of d; for d = R.zero every vector of M vanishes at n, and
// otherwise a vector b of M with b(n) = d writes each v of M, in one way
// only, as a vector of M vanishing at n plus a multiple a·b. Reading a
// vector at n is a linear functional on the free module, so this is the
// split of a submodule along a linear functional, the free module's sum
// and scaling being R's read pointwise.
var CoordinateProjectionSplit = coordinateProjectionSplitThm{family.Add(registry.ProofEntry{
	Name: "CoordinateProjectionSplit",
	Key:  "prop_446e48a85cb2a1b8",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num. ∀M:set(num → A).",
		Hypotheses: []string{
			"principal_ideal_domain(R)",
			"submodule(R, free_module_record(R, {i:num | i < n + 1}), M)",
		},
		Conclusion: "∃d:A. " +
			"    d ∈ R.carrier ∧ " +
			"    image(λv:(num → A). v(n), M) = image(R.mul(d), R.carrier) ∧ " +
			"    (d = R.zero ⇒ ∀v:(num → A). v ∈ M ⇒ v(n) = R.zero) ∧ " +
			"    (d ≠ R.zero ⇒ " +
			"        ∃b:(num → A). " +
			"            b ∈ M ∧ " +
			"            b(n) = d ∧ " +
			"            (∀v:(num → A). " +
			"                v ∈ M ⇒ " +
			"                ∃u:(num → A). ∃a:A. " +
			"                    u ∈ M ∧ " +
			"                    u(n) = R.zero ∧ " +
			"                    a ∈ R.carrier ∧ " +
			"                    v = fun_add(R.add, u, fun_smul(R.mul, a, b)) ∧ " +
			"                    (∀u':(num → A). ∀a':A. " +
			"                        u' ∈ M ∧ " +
			"                        u'(n) = R.zero ∧ " +
			"                        a' ∈ R.carrier ∧ " +
			"                        v = fun_add(R.add, u', fun_smul(R.mul, a', b)) ⇒ " +
			"                        u' = u ∧ a' = a)))",
	},
		func(arg *Argument, R *Expr[RingOps[A]], n *Expr[Nat], M *Expr[Set[Fun[Nat, A]]], hypotheses Fact) {
			given := arg.Conjuncts(
				hypotheses,
				"R is a principal ideal domain",
				"M is a submodule of the free module on the indices below n + 1")
			pid, sub := given[0], given[1]
			domain := arg.Have(
				"R is an integral domain",
				"integral_domain_on(R)",
				By(pid, PrincipalIdealDomainDef))
			ring := integral_domain.Ring.Read(domain)
			indices := arg.TermAs[Set[Nat]]("{i:num | i < n + 1}")
			free := arg.Have(
				"the free module on the indices below n + 1 is a module over R",
				"module_on(R, free_module_record(R, {i:num | i < n + 1}))",
				By(ring, free_module.FreeModuleOn.At(R, indices)))
			coordinate := arg.Have(
				"reading a vector at n is a linear functional on it",
				"module_homomorphism(R, "+
					"    free_module_record(R, {i:num | i < n + 1}), "+
					"    regular_module(R), "+
					"    λv:(num → A). v(n))",
				By(ring, free_module.CoordinateProjectionLinear.At(R, indices, n)))
			arg.Show(
				"so the coordinate at n splits M, as a linear functional on "+
					"a module over a principal ideal domain splits a submodule",
				By(pid, sub, coordinate, LinearFunctionalSplit.Read(free)))
		}),
})}

// SubmoduleFree — over a principal ideal domain, a submodule N of a module
// M with a finite basis E has a finite basis of at most card(E) vectors.
// By induction over the finite parts T of E, a submodule U inside the span
// of T has a finite basis of at most card(T) vectors. Inside the span of ∅,
// which is {M.zero}, ∅ is one. Adding e to T, the coordinate φ at e is a
// linear functional, R.one at e and R.zero on T, so a vector of the span of
// insert(e, T) that φ kills lies in the span of T (SpanInsertKernel), and φ
// splits U along a scalar d (LinearFunctionalSplit). For d = R.zero φ kills
// U, which then lies in the span of T. Otherwise U ∩ ker φ lies there and has
// a basis F of at most card(T) vectors. A lift b of d joins F
// independently: a multiple c • b in the span of F, which φ kills, has
// φ-value c·d = R.zero, so c = R.zero (IndependentInsertNoMultiple). And
// insert(b, F) spans U, each vector of U being a vector of U ∩ ker φ plus a
// multiple of b.
var SubmoduleFree = submoduleFreeThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleFree",
	Key:  "prop_d27095e0cecb9852",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N E:set(B).",
		Hypotheses: []string{
			"principal_ideal_domain(R)",
			"module_on(R, M)",
			"finite(E)",
			"module_basis(R, M, E)",
			"submodule(R, M, N)",
		},
		Conclusion: "∃F:set(B). finite(F) ∧ module_basis(R, restrict_module(M, N), F) ∧ card(F) ≤ card(E)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N, E *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"R is a principal ideal domain",
				"M is a module over R",
				"E is finite",
				"E is a basis of M",
				"N is a submodule of M")
			pid, moduleOn, finiteE, basisE, sub := given[0], given[1], given[2], given[3], given[4]
			domain := a.Conjuncts(
				a.Unfolded(pid, PrincipalIdealDomainDef),
				"R is an integral domain",
				"every ideal of R is principal")[0]
			onE := a.Conjuncts(
				a.Unfolded(basisE, linear_independence.ModuleBasisDef),
				"E is independent",
				"E spans M")
			eSub := a.Have(
				"E lies in M",
				"E ⊆ M.carrier",
				By(linear_independence.IndependentInCarrier.Read(onE[0])))
			eInM := a.Unfolded(eSub, set_basic.SubsetDef)
			regular, carrier := a.TermAs[ModuleOps[A, A]]("regular_module(R)"), a.TermAs[Set[B]]("M.carrier")
			inE := a.TermAs[Set[B]]("λy:B. y ∈ E")

			// The induction runs over the finite sets of members of E; E is one of
			// them, every member of E lying in E.
			bounded := a.TermAs[Set[Set[B]]](
				"λT:set(B). ∀U:set(B). " +
					"    submodule(R, M, U) ∧ U ⊆ module_span(R, M, T) ⇒ " +
					"    ∃F:set(B). finite(F) ∧ module_basis(R, restrict_module(M, U), F) ∧ card(F) ≤ card(T)")
			claim := a.Have(
				"by induction over the finite parts T of E, a submodule "+
					"inside the span of T has a basis of at most card(T) vectors",
				Statement{
					Binders: "∀U:set(B).",
					Hypotheses: []string{
						"submodule(R, M, U)",
						"U ⊆ module_span(R, M, E)",
					},
					Conclusion: "∃F:set(B). finite(F) ∧ module_basis(R, restrict_module(M, U), F) ∧ card(F) ≤ card(E)",
				},
				ByInduction(finite_set.FiniteInductFreshOn.At(bounded, inE, E), Normalized, finiteE,
					Case(
						"inside the span of ∅, which is {M.zero}, a submodule is {M.zero}, and ∅ is a basis of it",
						Derive(func(a *Argument) {
							U := a.FixAs[Set[B]]("U")
							about := a.Conjuncts(
								a.Assume(),
								"U is a submodule of M",
								"U lies in the span of ∅")
							subU, uInSpan := about[0], about[1]
							empty, zeroSet := a.TermAs[Set[B]]("∅"), a.TermAs[Set[B]]("{M.zero}")
							spanZero := a.Have(
								"the span of ∅ lies in the submodule {M.zero}",
								"module_span(R, M, ∅) ⊆ {M.zero}",
								By(
									submodule.ZeroSubmodule.Read(moduleOn),
									set_order.EmptySubset.At(zeroSet),
									submodule.SpanLeast.At(R, M, empty, zeroSet)))
							onlyZero := a.Have(
								"so ∅ spans U, both being {M.zero}",
								"module_span(R, M, ∅) = U",
								BySets(uInSpan, spanZero, submodule.SubmoduleZero.Read(subU)))
							basisEmpty := a.Have(
								"so ∅, independent, is a basis of U",
								"module_basis(R, restrict_module(M, U), ∅)",
								By(
									subU,
									onlyZero,
									linear_independence.IndependentEmpty.At(R, M),
									linear_independence.BasisRestrict.Read(moduleOn).At(U, empty)))
							a.Take(empty)
							a.Show(
								"∅ is finite, a basis of U, and has no more members than itself",
								By(finite_set.FiniteRules, basisEmpty, nat_order.LessEqRefl))
						})),
					Case(
						"adding e to T, the coordinate at e splits off at most one more basis vector",
						Derive(func(a *Argument) {
							e, T := a.FixAs[B]("e"), a.FixAs[Set[B]]("T")
							step := a.Conjuncts(
								a.Assume(),
								"the claim holds inside the span of T",
								"e is not in T",
								"T is finite",
								"e lies in E",
								"T lies in E")
							carried, fresh, finiteT, eIn, tInE := step[0], step[1], step[2], step[3], step[4]
							U := a.FixAs[Set[B]]("U")
							about := a.Conjuncts(
								a.Assume(),
								"U is a submodule of M",
								"U lies in the span of insert(e, T)")
							subU, uInSpan := about[0], about[1]
							uInM := a.Have(
								"U lies in M",
								"U ⊆ M.carrier",
								By(submodule.SubmoduleSubset.Read(subU)))
							tInM := a.Have(
								"T lies in M",
								"T ⊆ M.carrier",
								BySets(tInE, eSub))

							// The coordinate at e of the expansion in E, the functional
							// BasisCoordinateLinear states.
							functional := a.Have(
								"the coordinate at e is a linear functional on M, R.one at e and R.zero on T",
								"∃φ:(B → A). "+
									"    module_homomorphism(R, M, regular_module(R), φ) ∧ "+
									"    φ(e) = R.one ∧ "+
									"    (∀x:B. x ∈ T ⇒ φ(x) = R.zero)",
								Derive(func(a *Argument) {
									a.Take(a.TermAs[Fun[B, A]]("λv:B. module_basis_coordinates(R, M, E, v, e)"))
									linear := a.Have(
										"the coordinate at e is linear",
										"module_homomorphism(R, M, regular_module(R), λv:B. module_basis_coordinates(R, M, E, v, e))",
										By(finiteE, basisE, eIn, module_dimension.BasisCoordinateLinear.Read(moduleOn).At(E, e)))
									delta := a.Have(
										"e has the Kronecker coordinates of e",
										"module_basis_coordinates(R, M, E, e) = λx:B. COND(x = e, R.one, R.zero)",
										By(finiteE, basisE, eIn, module_dimension.BasisCoordinateDelta.Read(moduleOn).At(E, e)))
									atE := a.Have(
										"so the coordinate of e at e is R.one",
										"module_basis_coordinates(R, M, E, e, e) = R.one",
										delta.Rw(),
										Basic())
									offT := a.Have(
										"and a vector x of T, being not e, has coordinate R.zero at e",
										"∀x:B. x ∈ T ⇒ module_basis_coordinates(R, M, E, x, e) = R.zero",
										Derive(func(a *Argument) {
											x := a.FixAs[B]("x")
											xIn := a.Assume()
											deltaX := a.Have(
												"x has the Kronecker coordinates of x",
												"module_basis_coordinates(R, M, E, x) = λy:B. COND(y = x, R.one, R.zero)",
												By(finiteE, basisE, tInE.At(x), xIn, module_dimension.BasisCoordinateDelta.Read(moduleOn).At(E, x)))
											a.Show(
												"and e, outside T, is not x",
												deltaX.Rw(),
												By(xIn, fresh))
										}))
									a.Show(
										"so it is such a functional",
										By(linear, atE, offT))
								}))
							φ, chosen := a.UnpackAs[Fun[B, A]](functional, "φ")
							props := a.Conjuncts(
								chosen,
								"φ is linear",
								"φ(e) is R.one",
								"φ kills T")
							linear, atE, killsT := props[0], props[1], props[2]
							narrows := a.Have(
								"a vector of the span of insert(e, T) that φ kills lies in the span of T",
								"∀v:B. v ∈ module_span(R, M, insert(e, T)) ∧ φ(v) = R.zero ⇒ v ∈ module_span(R, M, T)",
								By(
									tInM,
									eInM.At(e),
									eIn,
									linear,
									atE,
									killsT,
									linear_independence.SpanInsertKernel.Read(moduleOn).AsFact().At(T, e, φ)))
							d, splitting := a.ObtainAs[A](
								"φ splits the submodule U along a scalar d",
								"∃d:A. "+
									"    d ∈ R.carrier ∧ "+
									"    image(φ, U) = image(R.mul(d), R.carrier) ∧ "+
									"    (d = R.zero ⇒ ∀v:B. v ∈ U ⇒ φ(v) = R.zero) ∧ "+
									"    (d ≠ R.zero ⇒ "+
									"        ∃b:B. "+
									"            b ∈ U ∧ "+
									"            φ(b) = d ∧ "+
									"            (∀v:B. "+
									"                v ∈ U ⇒ "+
									"                ∃u:B. ∃a:A. "+
									"                    u ∈ U ∧ "+
									"                    φ(u) = R.zero ∧ "+
									"                    a ∈ R.carrier ∧ "+
									"                    v = u + a • b ∧ "+
									"                    (∀u':B. ∀a':A. "+
									"                        u' ∈ U ∧ φ(u') = R.zero ∧ a' ∈ R.carrier ∧ v = u' + a' • b ⇒ "+
									"                        u' = u ∧ a' = a)))",
								By(pid, subU, linear, LinearFunctionalSplit.Read(moduleOn).At(U, φ)))
							split := a.Conjuncts(
								splitting,
								"d is a scalar",
								"φ carries U onto d·R",
								"if d is R.zero, φ kills U",
								"if d is not R.zero, a lift of d splits U")
							dIn := split[0]
							counted := a.Have(
								"insert(e, T) has one member more than T",
								"card(insert(e, T)) = suc(card(T))",
								By(finiteT, fresh, cardinality.InsertCountsOneMore.At(T, e)))

							a.Cases(a.Term("d = R.zero"))
							a.When(
								"d is R.zero: φ kills U, which so lies in the span of T, where the claim gives the basis",
								func(a *Argument, zero Fact) {
									killsU := a.Simplified(split[2], Fwd(zero))
									uInSpanT := a.Have(
										"U lies in the span of T",
										"U ⊆ module_span(R, M, T)",
										BySets(uInSpan, killsU, narrows))
									F, basisF := a.ObtainAs[Set[B]](
										"so the claim for T gives U a finite basis F of at most card(T) vectors",
										"∃F:set(B). finite(F) ∧ module_basis(R, restrict_module(M, U), F) ∧ card(F) ≤ card(T)",
										By(subU, uInSpanT, carried.At(U)))
									bound := a.Conjuncts(
										basisF,
										"F is finite",
										"F is a basis of U",
										"F has at most card(T) members")
									atMost := a.Have(
										"so F has fewer members than insert(e, T)",
										"card(F) ≤ card(insert(e, T))",
										ByArith(bound[2], counted))
									a.Take(F)
									a.Show(
										"F is a finite basis of U, small enough",
										By(bound[0], bound[1], atMost))
								})
							a.Otherwise(
								"d is not R.zero: a lift b of d joins a basis F of U ∩ ker φ, one vector more than F",
								func(a *Argument, nonzero Fact) {
									b, lifting := a.ObtainAs[B](
										"so a lift b of d writes each vector of U, in one way, as a vector φ kills plus a multiple of b",
										"∃b:B. "+
											"    b ∈ U ∧ "+
											"    φ(b) = d ∧ "+
											"    (∀v:B. "+
											"        v ∈ U ⇒ "+
											"        ∃u:B. ∃a:A. "+
											"            u ∈ U ∧ "+
											"            φ(u) = R.zero ∧ "+
											"            a ∈ R.carrier ∧ "+
											"            v = u + a • b ∧ "+
											"            (∀u':B. ∀a':A. "+
											"                u' ∈ U ∧ φ(u') = R.zero ∧ a' ∈ R.carrier ∧ v = u' + a' • b ⇒ u' = u ∧ a' = a))",
										By(split[3], nonzero))
									lifted := a.Conjuncts(
										lifting,
										"b lies in U",
										"φ(b) is d",
										"b splits U")
									bIn, bValue, splits := lifted[0], lifted[1], lifted[2]
									bInM := a.Have(
										"b lies in M",
										"b ∈ M.carrier",
										BySets(bIn, uInM))
									bm := proof.MemberOf(b, bInM)
									kernelSet := a.TermAs[Set[B]]("group_kernel(R.zero, M.carrier, φ)")
									killed := a.TermAs[Set[B]]("U ∩ group_kernel(R.zero, M.carrier, φ)")
									subKilled := a.Have(
										"U ∩ ker φ is a submodule of M",
										"submodule(R, M, U ∩ group_kernel(R.zero, M.carrier, φ))",
										By(
											subU,
											linear,
											module_homomorphism.KernelSubmodule.At(R, M, regular, φ),
											submodule.SubmoduleInter.At(R, M, U, kernelSet)))
									killedInSpan := a.Have(
										"U ∩ ker φ lies in the span of T",
										"U ∩ group_kernel(R.zero, M.carrier, φ) ⊆ module_span(R, M, T)",
										BySets(uInSpan, narrows, group_homomorphism.InKernel))
									F, basisF := a.ObtainAs[Set[B]](
										"so the claim for T gives U ∩ ker φ a finite basis F of at most card(T) vectors",
										"∃F:set(B). "+
											"    finite(F) ∧ "+
											"    module_basis(R, restrict_module(M, U ∩ group_kernel(R.zero, M.carrier, φ)), F) ∧ "+
											"    card(F) ≤ card(T)",
										By(subKilled, killedInSpan, carried.At(killed)))
									bound := a.Conjuncts(
										basisF,
										"F is finite",
										"F is a basis of U ∩ ker φ",
										"F has at most card(T) members")
									finiteF, basisKilled, cardF := bound[0], bound[1], bound[2]
									inM := a.Have(
										"so F is independent in M and spans U ∩ ker φ there",
										"module_independent(R, M, F) ∧ module_span(R, M, F) = U ∩ group_kernel(R.zero, M.carrier, φ)",
										By(basisKilled, subKilled, linear_independence.BasisRestrict.Read(moduleOn).At(killed, F)))
									ofF := a.Conjuncts(
										inM,
										"F is independent in M",
										"F spans U ∩ ker φ")
									independentF, spanF := ofF[0], ofF[1]
									extended := a.TermAs[Set[B]]("insert(b, F)")
									insertInU := a.Have(
										"insert(b, F) lies in U",
										"insert(b, F) ⊆ U",
										BySets(bIn, spanF, submodule.SubsetSpan.At(R, M, F)))

									// insert(b, F) is independent.
									noMultiple := a.Have(
										"only R.zero scales b into the span of F: φ kills that "+
											"span, and φ(c • b) = c·d vanishes only at c = R.zero",
										"∀c:A. c ∈ R.carrier ∧ c • b ∈ module_span(R, M, F) ⇒ c = R.zero",
										Derive(func(a *Argument) {
											c := a.FixAs[A]("c")
											about := a.Conjuncts(
												a.Assume(),
												"c is a scalar",
												"c • b lies in the span of F")
											cIn, multipleIn := about[0], about[1]
											cm := proof.MemberOf(c, cIn)
											killedMultiple := a.Have(
												"c • b lies in U ∩ ker φ, the span of F, so φ kills it",
												"φ(c • b) = R.zero",
												BySets(multipleIn, spanF, group_homomorphism.InKernel))
											value := a.Have(
												"φ(c • b) is c·φ(b) = c·d",
												"φ(c • b) = c * d",
												By(Normalized, bValue, module_homomorphism.HomSmul.Read(linear).At(cm, bm)))
											vanishes := a.Have(
												"so c·d is R.zero",
												"c * d = R.zero",
												By(Normalized, killedMultiple, value))
											a.Show(
												"d is not R.zero, so c is, R having no zero divisors",
												By(vanishes, nonzero, integral_domain.NoZeroDivisors.Read(domain).At(cm, proof.MemberOf(d, dIn))))
										}))
									independent := a.Have(
										"so b joins the independent F: insert(b, F) is independent in M",
										"module_independent(R, M, insert(b, F))",
										By(
											independentF,
											noMultiple,
											linear_independence.IndependentInsertNoMultiple.Read(moduleOn).At(F, bm)))

									// insert(b, F) spans U.
									extendedInM := a.Have(
										"insert(b, F) lies in M",
										"insert(b, F) ⊆ M.carrier",
										BySets(insertInU, uInM))
									spanSub := a.Have(
										"the span of insert(b, F) is a submodule of M",
										"submodule(R, M, module_span(R, M, insert(b, F)))",
										By(extendedInM, submodule.SpanSubmodule.Read(moduleOn).At(extended)))
									bSpan := a.Have(
										"which holds b",
										"b ∈ module_span(R, M, insert(b, F))",
										BySets(submodule.SubsetSpan.At(R, M, extended)))
									fInExtended := a.Have(
										"F lies in insert(b, F)",
										"F ⊆ insert(b, F)",
										BySets())
									fSpan := a.Have(
										"so the span of insert(b, F) holds the span of F",
										"module_span(R, M, F) ⊆ module_span(R, M, insert(b, F))",
										By(fInExtended, submodule.SpanMono.At(R, M, F, extended)))
									uEach, fSpanEach := a.Unfolded(uInM, set_basic.SubsetDef), a.Unfolded(fSpan, set_basic.SubsetDef)
									covers := a.Have(
										"each vector of U is a vector of U ∩ ker φ plus a "+
											"multiple of b, so lies in the span of insert(b, F)",
										"∀v:B. v ∈ U ⇒ v ∈ module_span(R, M, insert(b, F))",
										Derive(func(a *Argument) {
											v := a.FixAs[B]("v")
											vInU := a.Assume()
											u, _, written := a.Unpack2As[B, A](GroupPremises(vInU, splits.At(v)), "u", "a")
											parts := a.Conjuncts(
												written,
												"u lies in U",
												"φ kills u",
												"a is a scalar",
												"v is u + a • b",
												"and they are the only such pair")
											killedU := a.Have(
												"u lies in U ∩ ker φ",
												"u ∈ U ∩ group_kernel(R.zero, M.carrier, φ)",
												By(
													parts[0],
													parts[1],
													uEach.At(u),
													set_basic.InInter.At(U, kernelSet, u),
													group_homomorphism.InKernel.At(a.TermAs[A]("R.zero"), carrier, φ, u)))
											uInSpanF := a.Simplified(killedU, Rev(spanF))
											uSpan := a.Have(
												"which F spans, inside the span of insert(b, F)",
												"u ∈ module_span(R, M, insert(b, F))",
												By(uInSpanF, fSpanEach.At(u)))
											multiple := a.Have(
												"so does a • b",
												"a • b ∈ module_span(R, M, insert(b, F))",
												By(parts[2], bSpan, submodule.SubmoduleSmul.Read(spanSub)))
											a.Show(
												"and so their sum v",
												parts[3].Rw(),
												By(submodule.SubmoduleAdd.Read(spanSub).At(
													proof.MemberOf(u, uSpan), proof.MemberOf(a.TermAs[B]("a • b"), multiple))))
										}))
									within := a.Have(
										"the span of insert(b, F) lies in the submodule U",
										"module_span(R, M, insert(b, F)) ⊆ U",
										By(subU, insertInU, submodule.SpanLeast.At(R, M, extended, U)))
									spans := a.Have(
										"so insert(b, F) spans U in M",
										"module_span(R, M, insert(b, F)) = U",
										By(
											covers,
											within,
											set_basic.SubsetDef,
											set_order.SubsetAntisym.At(a.TermAs[Set[B]]("module_span(R, M, insert(b, F))"), U)))

									basisU := a.Have(
										"independent in M and spanning U, insert(b, F) is a basis of U",
										"module_basis(R, restrict_module(M, U), insert(b, F))",
										By(independent, spans, subU, linear_independence.BasisRestrict.Read(moduleOn).At(U, extended)))
									size := a.Have(
										"insert(b, F) is finite, with at most card(T) + 1 members",
										"finite(insert(b, F)) ∧ card(insert(b, F)) ≤ suc(card(T))",
										By(finiteF, cardF, cardinality.InsertCountsAtMostOneMore.At(F, b, a.TermAs[Nat]("card(T)"))))
									sized := a.Conjuncts(
										size,
										"insert(b, F) is finite",
										"insert(b, F) has at most suc(card(T)) members")
									atMost := a.Have(
										"so no more than insert(e, T)",
										"card(insert(b, F)) ≤ card(insert(e, T))",
										ByArith(sized[1], counted))
									a.Take(extended)
									a.Show(
										"insert(b, F) is a finite basis of U, small enough",
										By(sized[0], basisU, atMost))
								})
						}))))
			nInSpan := a.Have(
				"N lies in M, which E spans",
				"N ⊆ module_span(R, M, E)",
				By(Normalized, submodule.SubmoduleSubset.Read(sub), onE[1]))
			a.Show(
				"so N, a submodule inside the span of E, has such a basis",
				By(sub, nInSpan, claim.At(N)))
		}),
})}

// FiniteTorsionFreeFree — over a principal ideal domain, a finitely
// generated torsion-free module is free on a finite basis. A finite
// generating set G has an independent part S whose span holds c • g for
// every g of G, for one nonzero scalar c (IndependentPartSpansMultiple);
// scaling by c is then a homomorphism of M, one-to-one since M is torsion
// free, carrying M, the span of G, into the span of S. That span is free
// on the finite S, so its submodule c • M is free on a finite F
// (SubmoduleFree), and F pulls back along the scaling to a finite basis
// of M (BasisPullback).
var FiniteTorsionFreeFree = finiteTorsionFreeFreeThm{family.Add(registry.ProofEntry{
	Name: "FiniteTorsionFreeFree",
	Key:  "prop_43dfbedfa69f82d5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"principal_ideal_domain(R)",
			"module_on(R, M)",
			"module_finitely_generated(R, M)",
			"module_torsion_free(R, M)",
		},
		Conclusion: "∃E:set(B). finite(E) ∧ module_basis(R, M, E)",
	},
		func(arg *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], hypotheses Fact) {
			given := arg.Conjuncts(
				hypotheses,
				"R is a principal ideal domain",
				"M is a module over R",
				"M is finitely generated",
				"M is torsion free")
			principal, moduleOn, generated, torsionFree := given[0], given[1], given[2], given[3]
			domain := arg.Conjuncts(
				arg.Unfolded(principal, PrincipalIdealDomainDef),
				"R is an integral domain",
				"every ideal of R is principal")[0]
			mulMonoid := comm_ring.MulMonoidOn.Read(module.RingOn.Read(moduleOn))
			carrier := arg.TermAs[Set[B]]("M.carrier")

			// The independent part S and the scalar c.
			G, generators := arg.UnpackAs[Set[B]](arg.Unfolded(generated, FinitelyGeneratedDef), "G")
			ofG := arg.Conjuncts(
				generators,
				"G is finite",
				"G lies in M",
				"G spans M")
			finG, gInM, gSpans := ofG[0], ofG[1], ofG[2]
			S, c, chosen := arg.Obtain2As[Set[B], A](
				"over the domain R, G has an independent part S whose "+
					"span holds a nonzero multiple c • g of every g of G",
				"∃S:set(B). ∃c:A. "+
					"    S ⊆ G ∧ "+
					"    module_independent(R, M, S) ∧ "+
					"    c ∈ R.carrier ∧ "+
					"    c ≠ R.zero ∧ "+
					"    (∀g:B. g ∈ G ⇒ c • g ∈ module_span(R, M, S))",
				By(domain, finG, gInM, linear_independence.IndependentPartSpansMultiple.Read(moduleOn).At(G)))
			ofS := arg.Conjuncts(
				chosen,
				"S lies in G",
				"S is independent",
				"c is a scalar",
				"c is not zero",
				"c • g lies in the span of S for every g of G")
			sInG, independent, cIn, cNonzero, multiples := ofS[0], ofS[1], ofS[2], ofS[3], ofS[4]
			cm := proof.MemberOf(c, cIn)
			span := arg.TermAs[Set[B]]("module_span(R, M, S)")
			sInM := arg.Have(
				"S lies in M, as G does",
				"S ⊆ M.carrier",
				By(sInG, gInM, set_order.SubsetTrans.At(S, G, carrier)))
			finS := arg.Have(
				"S is finite, as G is",
				"finite(S)",
				By(finG, sInG, finite_set.FiniteSubset.At(S, G)))
			spanSub := arg.Have(
				"the span of S is a submodule of M",
				"submodule(R, M, module_span(R, M, S))",
				By(sInM, submodule.SpanSubmodule.Read(moduleOn).At(S)))

			// The scaling by c.
			scaling := arg.TermAs[Fun[B, B]]("M.smul(c)")
			keeps := arg.Have(
				"scaling by c keeps M",
				"∀u:B. u ∈ M.carrier ⇒ c • u ∈ M.carrier",
				By(module.SmulIn.Read(moduleOn), cIn))
			distributes := arg.Have(
				"scaling by c distributes over a sum of vectors",
				"∀u v:B. u ∈ M.carrier ∧ v ∈ M.carrier ⇒ c • (u + v) = c • u + c • v",
				By(module.SmulAddLeft.Read(moduleOn), cIn))
			commutes := arg.Have(
				"scaling by c commutes with scaling by any scalar d, the scalars commuting",
				"∀d:A. ∀u:B. d ∈ R.carrier ∧ u ∈ M.carrier ⇒ c • (d • u) = d • (c • u)",
				Derive(func(b *Argument) {
					d := b.FixAs[A]("d")
					u := b.FixAs[B]("u")
					guards := b.Conjuncts(
						b.Assume(),
						"d is a scalar",
						"u is a vector of M")
					dm, um := proof.MemberOf(d, guards[0]), proof.MemberOf(u, guards[1])
					b.Show(
						"both are scaling u by the product of c and d, taken in either order",
						CalcEq(
							Leg(
								b.TermAs[B]("(c * d) • u"),
								"scaling twice is scaling by the product",
								By(module.SmulMul.Read(moduleOn).At(cm, dm, um))),
							Leg(
								b.TermAs[B]("(d * c) • u"),
								"the scalars commute",
								By(Normalized, comm_monoid.CommOn.Read(mulMonoid).At(cm, dm))),
							FinalLeg(
								"and scaling by the product is scaling twice",
								By(module.SmulMul.Read(moduleOn).At(dm, cm, um))),
						))
				}))
			linear := arg.Have(
				"so scaling by c is a homomorphism from M to M",
				"module_homomorphism(R, M, M, M.smul(c))",
				By(
					moduleOn,
					keeps,
					distributes,
					commutes,
					module_homomorphism.ModuleHomomorphismDef.At(R, M, M, scaling)))
			torsion := arg.Unfolded(torsionFree, TorsionFreeDef)
			kernel := arg.Have(
				"M being torsion free and c not zero, scaling by c sends only M.zero to M.zero",
				"group_kernel(M.zero, M.carrier, M.smul(c)) = {M.zero}",
				BySets(
					torsion.At(c),
					cNonzero,
					cIn,
					group.OneIn.Read(module.AddGroupOn.Read(moduleOn)),
					module.SmulZero.Read(moduleOn).At(cm),
					At(group_homomorphism.InKernel, arg.TermAs[B]("M.zero"), carrier, scaling)))
			oneToOne := arg.Have(
				"so scaling by c is one-to-one on M",
				"injective_on(M.carrier, M.smul(c))",
				By(linear, kernel, module_homomorphism.KernelTrivialIffInjective.At(R, M, M, scaling)))

			// Its image c • M, inside the span of S.
			scaledGenerators := arg.Have(
				"scaling by c carries G into the span of S",
				"image(M.smul(c), G) ⊆ module_span(R, M, S)",
				Simp(Fwd(set_basic.SubsetDef), Fwd(set_image.ForallInImage)),
				By(multiples))
			scaled := arg.TermAs[Set[B]]("image(M.smul(c), M.carrier)")
			scaledInSpan := arg.Have(
				"so it carries M, the span of G, onto the span of "+
					"the images of G, which the submodule span of S holds",
				"image(M.smul(c), M.carrier) ⊆ module_span(R, M, S)",
				By(
					Normalized,
					gSpans,
					linear,
					gInM,
					scaledGenerators,
					spanSub,
					linear_independence.HomSpanInSubmodule.At(R, M, M, scaling, G, span)))

			// The span of S, free on S.
			free := arg.TermAs[ModuleOps[A, B]]("restrict_module(M, module_span(R, M, S))")
			sBasis := arg.Have(
				"S, independent in M, is a basis of its span",
				"module_basis(R, restrict_module(M, module_span(R, M, S)), S)",
				By(independent, spanSub, linear_independence.BasisRestrict.Read(moduleOn).At(span, S)))
			scaledInside := arg.Have(
				"c • M, the image of the scaling, is a submodule of the span of S, in which it lies",
				"submodule(R, restrict_module(M, module_span(R, M, S)), image(M.smul(c), M.carrier))",
				By(
					linear,
					module_homomorphism.ImageSubmodule.At(R, M, M, scaling),
					scaledInSpan,
					submodule.SubmoduleRestrict.At(R, M, span, scaled)))

			// The basis F of c • M, pulled back to M.
			F, freeOnF := arg.ObtainAs[Set[B]](
				"over the principal ideal domain R, the submodule c • M of "+
					"the span of S, free on the finite S, is free on a finite F",
				"∃F:set(B). "+
					"    finite(F) ∧ "+
					"    module_basis(R, "+
					"        restrict_module(restrict_module(M, module_span(R, M, S)), image(M.smul(c), M.carrier)), "+
					"        F) ∧ "+
					"    card(F) ≤ card(S)",
				By(
					principal,
					spanSub,
					submodule.SubmoduleModuleOn.Read(moduleOn).At(span),
					finS,
					sBasis,
					scaledInside,
					SubmoduleFree.At(R, free, scaled, S)))
			ofF := arg.Conjuncts(
				freeOnF,
				"F is finite",
				"F is a basis of c • M inside the span of S",
				"F is no larger than S")
			preimage := arg.TermAs[Set[B]]("preimage_on(M.carrier, M.smul(c), F)")
			basis := arg.Have(
				"F, a basis of c • M, pulls back along the one-to-one scaling to a basis of M",
				"module_basis(R, M, preimage_on(M.carrier, M.smul(c), F))",
				By(
					linear,
					oneToOne,
					module_record.RestrictModuleTwice.At(M, span, scaled),
					ofF[1],
					linear_independence.BasisPullback.At(R, M, M, scaling, F)))
			finPreimage := arg.Have(
				"which is finite, F being finite and the scaling one-to-one",
				"finite(preimage_on(M.carrier, M.smul(c), F))",
				By(oneToOne, ofF[0], finite_set.FiniteImageInjGeneral.At(scaling, carrier, F)))
			arg.Take(preimage)
			arg.Show(
				"the preimage of F is a finite basis of M",
				By(finPreimage, basis))
		}),
})}

// FiniteBasisFinitelyGenerated — a module with a finite basis is finitely
// generated: the basis lies in the module, being independent, and spans it.
var FiniteBasisFinitelyGenerated = finiteBasisFinitelyGeneratedThm{family.Add(registry.ProofEntry{
	Name: "FiniteBasisFinitelyGenerated",
	Key:  "prop_7654e8dc51a91e4b",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{"∃E:set(B). finite(E) ∧ module_basis(R, M, E)"},
		Conclusion: "module_finitely_generated(R, M)",
	}, func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], free Fact) {
		E, basis := a.UnpackAs[Set[B]](free, "E")
		a.Show(
			"E lies in M, being independent, and spans it",
			Simp(Fwd(FinitelyGeneratedDef)),
			Witness(E),
			By(
				basis,
				linear_independence.ModuleBasisDef.At(R, M, E),
				linear_independence.IndependentInCarrier.At(R, M, E)))
	}),
})}

// FiniteModuleTower — a finitely generated S-submodule of a field, S finite
// over a subring R, is a finitely generated R-submodule: restricting the
// scalars keeps it a submodule, and pairwise products of the two finite
// generating sets span it over R.
var FiniteModuleTower = finiteModuleTowerThm{family.Add(registry.ProofEntry{
	Name: "FiniteModuleTower",
	Key:  "prop_44659b978fb845c4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀R S I:set(A).",
		Hypotheses: []string{
			"R ⊆ S",
			"subring(field_ring(L), R)",
			"subring(field_ring(L), S)",
			"submodule(«RingS», «Ambient», I)",
			"module_finitely_generated(«RingR», restrict_module(«Ambient», S))",
			"module_finitely_generated(«RingS», restrict_module(«Ambient», I))",
		},
		Conclusion: "submodule(«RingR», «Ambient», I) ∧ " +
			"module_finitely_generated(«RingR», restrict_module(«Ambient», I))",
		Abbrev: Abbrev{
			{Name: "RingR", Text: "restrict_ring(field_ring(L), R)"},
			{Name: "RingS", Text: "restrict_ring(field_ring(L), S)"},
			{Name: "Ambient", Text: "regular_module(field_ring(L))"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], R, S, I *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"R lies in S",
			"R is a subring of the field",
			"S is a subring of the field",
			"I is an S-submodule",
			"S is finite over R",
			"I is finite over S")
		inclusion, subringR, subringS, subS, finiteS, finiteI :=
			parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
		moduleS := a.Have(
			"the field is a module over S",
			"module_on(«RingS», «Ambient»)",
			By(subringS, fractional_ideal.FieldModuleOn.Read(L).At(S)))
		moduleR := a.Have(
			"the field is a module over R",
			"module_on(«RingR», «Ambient»)",
			By(subringR, fractional_ideal.FieldModuleOn.Read(L).At(R)))
		subR := a.Have(
			"I remains a submodule over R",
			"submodule(«RingR», «Ambient», I)",
			By(
				subS,
				inclusion,
				submodule.SubmoduleRestrictScalars.At(
					a.TermAs[RingOps[A]]("«RingS»"),
					a.TermAs[module_record.ModuleOps[A, A]]("«Ambient»"),
					I,
					a.TermAs[RingOps[A]]("«RingR»"))))
		B, generatorsS := a.ObtainAs[Set[A]](
			"choose finite R-generators for S",
			"∃B:set(A). finite(B) ∧ B ⊆ S ∧ module_span(«RingR», restrict_module(«Ambient», S), B) = S",
			By(finiteS, FinitelyGeneratedDef))
		C, generatorsI := a.ObtainAs[Set[A]](
			"choose finite S-generators for I",
			"∃C:set(A). finite(C) ∧ C ⊆ I ∧ module_span(«RingS», restrict_module(«Ambient», I), C) = I",
			By(finiteI, FinitelyGeneratedDef))
		spanC := a.Have(
			"C spans I in the ambient field module",
			"module_span(«RingS», «Ambient», C) = I",
			By(Normalized, generatorsI, subS, linear_independence.SpanRestrict.Read(moduleS).At(I, C)))
		inC := a.Have(
			"C lies in the field",
			"C ⊆ L.carrier",
			BySets(generatorsI, subS, submodule.SubmoduleSubset))
		pairwiseProducts := a.TermAs[Set[A]]("{b * c | b:A, c:A | b ∈ B ∧ c ∈ C}")
		spanProducts := a.Have(
			"the pairwise products span I over R",
			"module_span(«RingR», «Ambient», {b * c | b:A, c:A | b ∈ B ∧ c ∈ C}) = I",
			By(
				generatorsS,
				inclusion,
				subringR,
				subringS,
				inC,
				spanC,
				fractional_ideal.SubringTowerSpan.Read(L).At(R, S, I, B, C)))
		finiteProducts := a.Have(
			"there are finitely many pairwise products",
			"finite({b * c | b:A, c:A | b ∈ B ∧ c ∈ C})",
			By(
				generatorsS,
				generatorsI,
				finite_set.FiniteProductDependent.At(
					a.TermAs[Op[A]]("L.mul"), B, a.TermAs[Fun[A, Set[A]]]("λb:A. C"))))
		productsIn := a.Have(
			"the product generators belong to I",
			"{b * c | b:A, c:A | b ∈ B ∧ c ∈ C} ⊆ I",
			BySets(spanProducts, submodule.SubsetSpan))
		restrictedSpan := a.Have(
			"the product generators span the restricted module",
			"module_span(«RingR», restrict_module(«Ambient», I), {b * c | b:A, c:A | b ∈ B ∧ c ∈ C}) = I",
			By(
				spanProducts,
				productsIn,
				subR,
				linear_independence.SpanRestrict.Read(moduleR).At(I, pairwiseProducts)))
		finiteR := a.Have(
			"the finite product set generates I over R",
			"module_finitely_generated(«RingR», restrict_module(«Ambient», I))",
			Simp(Fwd(FinitelyGeneratedDef)),
			Witness(pairwiseProducts),
			By(finiteProducts, productsIn, restrictedSpan))
		a.Show(
			"I is a finitely generated R-submodule",
			By(subR, finiteR))
	}),
})}

// FinitelyGeneratedFree — inside a field L, let R ⊆ S be rings, R a
// principal ideal domain and S finitely generated as a module over R;
// then a finitely generated S-submodule I of L is free of finite rank
// over R. Finite generation passes down the tower, so I is a finitely
// generated R-submodule (FiniteModuleTower), and I is torsion-free, a
// product of members of the field vanishing only at a zero factor; a
// finitely generated torsion-free module over a principal ideal domain is
// free (FiniteTorsionFreeFree).
var FinitelyGeneratedFree = finitelyGeneratedFreeThm{family.Add(registry.ProofEntry{
	Name: "FinitelyGeneratedFree",
	Key:  "prop_698c4a9219376a30",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀R S I:set(A).",
		Hypotheses: []string{
			"R ⊆ S",
			"subring(field_ring(L), S)",
			"principal_ideal_domain(«fieldRing»(R))",
			"module_finitely_generated(«fieldRing»(R), «fieldModule»(S))",
			"submodule(«fieldRing»(S), regular_module(field_ring(L)), I)",
			"module_finitely_generated(«fieldRing»(S), «fieldModule»(I))",
		},
		Conclusion: "∃F:set(A). finite(F) ∧ module_basis(«fieldRing»(R), «fieldModule»(I), F)",
		Abbrev: Abbrev{
			{Name: "fieldRing", Text: "restrict_ring(field_ring(L))"},
			{Name: "fieldModule", Text: "restrict_module(regular_module(field_ring(L)))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], R, S, I *Expr[Set[A]], given Fact) {
			h := a.Conjuncts(
				given,
				"R lies in S",
				"S is a subring of L",
				"R is a principal ideal domain",
				"S is finitely generated over R",
				"I is an S-submodule of L",
				"finitely generated over S")
			rInS, subringS, principal, iOverS := h[0], h[1], h[2], h[4]
			carrier := a.TermAs[Set[A]]("L.carrier")
			scalars := a.TermAs[RingOps[A]]("«fieldRing»(R)")
			ideal := a.TermAs[ModuleOps[A, A]]("«fieldModule»(I)")

			ringR := a.Have(
				"a principal ideal domain is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), R))",
				By(a.Unfolded(principal, PrincipalIdealDomainDef), integral_domain.Ring))
			rInL := a.Have(
				"R lies in L",
				"R ⊆ L.carrier",
				By(rInS, comm_ring.SubringSubset.Read(subringS), set_order.SubsetTrans.At(R, S, carrier)))
			subringR := a.Have(
				"so R is a subring of L",
				"subring(field_ring(L), R)",
				By(rInL, ringR, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(R)))
			overR := a.Have(
				"L is a module over R",
				"module_on(«fieldRing»(R), regular_module(field_ring(L)))",
				By(subringR, fractional_ideal.FieldModuleOn.Read(L).At(R)))
			tower := a.Conjuncts(
				GroupPremises(h[0], subringR, h[1], h[4], h[3], h[5], FiniteModuleTower.Read(L).At(R, S, I)),
				"R lying in S, I is an R-submodule of L",
				"and, S being finite over R, I is finitely generated over R")
			iOverR, generated := tower[0], tower[1]

			torsionFree := a.Have(
				"I is torsion-free over R: a nonzero c of R kills "+
					"no nonzero v of I, the field having no zero divisors",
				"module_torsion_free(«fieldRing»(R), «fieldModule»(I))",
				Unfold(TorsionFreeDef),
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					v := b.FixAs[A]("v")
					parts := b.Conjuncts(
						b.Assume(),
						"c lies in R",
						"c is not zero",
						"v lies in I",
						"c * v = zero")
					cInL := b.Have(
						"c lies in L",
						"c ∈ L.carrier",
						BySets(parts[0], rInL))
					vInL := b.Have(
						"v lies in L",
						"v ∈ L.carrier",
						BySets(parts[2], submodule.SubmoduleSubset.Read(iOverS)))
					b.Show(
						"so v is zero",
						By(
							parts[1],
							parts[3],
							field.MulEqZeroOn.Read(L).At(b.MemberOf[on.L](c, cInL), b.MemberOf[on.L](v, vInL))))
				}))
			a.Show(
				"a finitely generated torsion-free module over a principal ideal domain is free of finite rank",
				By(
					principal,
					iOverR,
					submodule.SubmoduleModuleOn.Read(overR).At(I),
					generated,
					torsionFree,
					FiniteTorsionFreeFree.At(scalars, ideal)))
		}),
})}

// FinitelyGeneratedSubmodule — a submodule of a finitely generated
// module over a principal ideal domain is finitely generated. Present M
// as the image of the free module on a finite generating set E, whose
// delta functions are a finite basis (free_module.DeltaAtBasis,
// free_module.FreeLiftOntoSpanning); the inverse image of N is a
// submodule of that free module (module_homomorphism.HomPreimageSubmodule),
// so it has a finite basis (SubmoduleFree), whose image generates N.
var FinitelyGeneratedSubmodule = finitelyGeneratedSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "FinitelyGeneratedSubmodule",
	Key:  "prop_3f1a75e487423f3a",
	Build: family.Sections(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:set(B).",
		Hypotheses: []string{
			"principal_ideal_domain(R)",
			"module_on(R, M)",
			"module_finitely_generated(R, M)",
			"submodule(R, M, N)",
		},
		Conclusion: "module_finitely_generated(R, restrict_module(M, N))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		presentation := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀E:set(B).",
			Hypotheses: []string{
				"module_on(R, M)",
				"finite(E)",
				"E ⊆ M.carrier",
				"module_span(R, M, E) = M.carrier",
			},
			Conclusion: "∃F:set(B → A). " +
				"    finite(F) ∧ " +
				"    module_basis(R, free_module_record(R, E), F) ∧ " +
				"    module_homomorphism(R, free_module_record(R, E), M, «lift») ∧ " +
				"    image(«lift», free_module_record(R, E).carrier) = M.carrier",
			Abbrev: Abbrev{
				{Name: "lift", Text: "free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u)"},
			},
		}, func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], E *Expr[Set[B]], given Fact) {
			ofE := a.Conjuncts(
				given,
				"M is a module",
				"E is finite",
				"E lies in M",
				"E spans M")
			moduleOn, finiteE, eInM, spansM := ofE[0], ofE[1], ofE[2], ofE[3]
			ring := module.RingOn.Read(moduleOn)
			delta := a.TermAs[Fun2[B, B, A]]("delta_at")
			identity := a.TermAs[Fun[B, B]]("λu:B. u")
			linear := a.Have(
				"the identity on E extends to a homomorphism into M",
				"module_homomorphism(R, free_module_record(R, E), M, «lift»)",
				By(a.Unfolded(eInM, set_basic.SubsetDef), free_module.FreeLiftHom.Read(moduleOn).At(E, identity)))
			onto := a.Have(
				"and the extension maps the free module onto M, which E spans",
				"image(«lift», free_module_record(R, E).carrier) = M.carrier",
				By(eInM, spansM, free_module.FreeLiftOntoSpanning.Read(moduleOn).At(E)))
			a.Take(a.TermAs[Set[Fun[B, A]]]("image(delta_at, E)"))
			a.Show(
				"the delta functions are a finite basis of the free module, which maps onto M",
				By(
					finiteE,
					finite_set.FiniteImage.At(delta, E),
					free_module.DeltaAtBasis.Read(ring).At(E),
					linear,
					onto))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[Set[B]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"R is a principal ideal domain",
				"M is a module",
				"M is finitely generated",
				"N is a submodule")
			principal, moduleOn, generated, subN := parts[0], parts[1], parts[2], parts[3]
			E, generating := a.UnpackAs[Set[B]](a.Unfolded(generated, FinitelyGeneratedDef), "E")
			ofE := a.Conjuncts(
				generating,
				"E is finite",
				"E lies in M",
				"E spans M")
			freeModule := a.Let("P", a.TermAs[ModuleOps[A, Fun[B, A]]]("free_module_record(R, E)"))
			extension := a.Let(
				"h", a.TermAs[Fun[Fun[B, A], B]]("free_lift(R.zero, M.add, M.zero, M.smul, λu:B. u)"))
			F, presented := a.ObtainAs[Set[Fun[B, A]]](
				"M is the image of a free module with a finite basis",
				"∃F:set(B → A). "+
					"    finite(F) ∧ "+
					"    module_basis(R, P, F) ∧ "+
					"    module_homomorphism(R, P, M, h) ∧ "+
					"    image(h, P.carrier) = M.carrier",
				extension.Rw(),
				freeModule.Rw(),
				By(moduleOn, ofE[0], ofE[1], ofE[2], At(presentation, R, M, E)))
			ofF := a.Conjuncts(
				presented,
				"F is finite",
				"F is a basis of the free module",
				"the lift is a homomorphism",
				"the lift is onto M")
			finiteF, basisF, linear, onto := ofF[0], ofF[1], ofF[2], ofF[3]
			U, preimage := a.LetAs[Set[Fun[B, A]]]("U", "preimage_on(P.carrier, h, N)")
			P, h := a.TermAs[ModuleOps[A, Fun[B, A]]]("P"), a.TermAs[Fun[Fun[B, A], B]]("h")
			moduleP := module_homomorphism.HomSource.Read(linear)
			inU := a.Have(
				"U consists of the vectors of P whose images lie in N",
				"∀v:(B → A). v ∈ U ⇔ v ∈ P.carrier ∧ h(v) ∈ N",
				BySets(preimage))
			subU := a.Have(
				"the inverse image U of the submodule N is a submodule of P",
				"submodule(R, P, U)",
				preimage.Rw(),
				By(linear, subN, module_homomorphism.HomPreimageSubmodule.At(R, P, M, h, N)))
			G, basis := a.ObtainAs[Set[Fun[B, A]]](
				"a submodule of the finite free module has a finite basis",
				"∃G:set(B → A). finite(G) ∧ module_basis(R, restrict_module(P, U), G) ∧ card(G) ≤ card(F)",
				By(principal, moduleP, finiteF, basisF, subU, SubmoduleFree.At(R, P, U, F)))
			ofG := a.Conjuncts(
				basis,
				"G is finite",
				"G is a basis of U",
				"G has at most as many vectors as F")
			ontoN := a.Have(
				"h maps its inverse image of N onto N",
				"image(h, U) = N",
				BySets(onto, inU, submodule.SubmoduleSubset.Read(subN)))
			intoN := a.Have(
				"h carries U into N",
				"∀u:(B → A). u ∈ U ⇒ h(u) ∈ N",
				By(inU))
			restricted := a.Have(
				"h restricts to a homomorphism from U to N",
				"module_homomorphism(R, restrict_module(P, U), restrict_module(M, N), h)",
				By(linear, subU, subN, intoN, module_homomorphism.HomRestrict.At(R, P, M, h, U, N)))
			basisParts := a.Conjuncts(
				a.Unfolded(ofG[1], linear_independence.ModuleBasisDef),
				"G is independent in U",
				"G spans U")
			carrierU := a.Have(
				"the restricted source has carrier U",
				"restrict_module(P, U).carrier = U",
				Simp(Fwd(module_record.RestrictModuleDef), Fwd(module_record.ModCarrierDef)),
				Basic())
			carrierN := a.Have(
				"the restricted target has carrier N",
				"restrict_module(M, N).carrier = N",
				Simp(Fwd(module_record.RestrictModuleDef), Fwd(module_record.ModCarrierDef)),
				Basic())
			gInSource := a.Have(
				"G lies in the restricted source",
				"G ⊆ restrict_module(P, U).carrier",
				By(
					basisParts[0],
					linear_independence.IndependentInCarrier.At(
						R, a.TermAs[ModuleOps[A, Fun[B, A]]]("restrict_module(P, U)"), G),
					carrierU))
			spansN := a.Have(
				"the images of G span N",
				"module_span(R, restrict_module(M, N), image(h, G)) = N",
				By(
					restricted,
					gInSource,
					basisParts[1],
					ontoN,
					linear_independence.HomSpan.At(
						R,
						a.TermAs[ModuleOps[A, Fun[B, A]]]("restrict_module(P, U)"),
						a.TermAs[ModuleOps[A, B]]("restrict_module(M, N)"),
						h,
						G)))
			imagesIn := a.Have(
				"the images lie in the restricted target",
				"image(h, G) ⊆ restrict_module(M, N).carrier",
				BySets(gInSource, carrierU, carrierN, module_homomorphism.HomIn.Read(restricted)))
			a.Show(
				"N is generated by the finite family of images of G",
				Unfold(FinitelyGeneratedDef),
				Witness(a.TermAs[Set[B]]("image(h, G)")),
				By(ofG[0], finite_set.FiniteImage.At(h, G), imagesIn, spansN, carrierN))
		})
	}),
})}
