// submodule.go — submodules of a module on a set, the submodule a set
// spans, the quotient module — the cosets of a submodule, added as sets
// and scaled without choosing a representative — and the annihilator of
// a vector of a simple module.

package submodule

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// records binds a ring and a module over it, for a statement that needs
// no module law: a fact about closed sets.
const records = "∀R:ring_ops(A). ∀M:module_ops(A, B). "

// ---------------------------------------------------------------------------
// Submodules
// ---------------------------------------------------------------------------

// SubmoduleDef — `submodule(R, M, N)`: N is a subgroup of M's carrier
// under the vector addition, closed under scaling by R.
var SubmoduleDef = submoduleDefThm{family.Define(registry.DefEntry{
	Name:  "SubmoduleDef",
	Key:   "prop_4135203534df0e90",
	Const: "submodule",
	Type:  "ring_ops(A) → module_ops(A, B) → set(B) → bool",
	Equations: []string{
		records + "∀N:set(B). submodule(R, M, N) ⇔ subgroup(module_additive_group(M), N) ∧ (∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ N ⇒ c • u ∈ N)",
	},
})}

// SubmoduleSubgroup — a submodule is a subgroup of M's carrier.
var SubmoduleSubgroup = submoduleSubgroupThm{family.Add(registry.ProofEntry{
	Name:  "SubmoduleSubgroup",
	Key:   "prop_c920962b3e477f09",
	Build: SubmoduleDef.Entry().Conjunct("subgroup(module_additive_group(M), N)"),
})}

// SubmoduleSmul — a submodule is closed under scaling.
var SubmoduleSmul = submoduleSmulThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleSmul",
	Key:  "prop_d3f32593518cefac",
	Build: SubmoduleDef.Entry().Conjunct(Statement{
		Binders: "∀c:A. ∀u:B.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"u ∈ N",
		},
		Conclusion: "c • u ∈ N",
	}),
})}

// SubmoduleSubset — a submodule lies in the module's carrier: it is a
// subgroup of that carrier, and a subgroup lies in its carrier.
var SubmoduleSubset = submoduleSubsetThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleSubset",
	Key:  "prop_6c265ce6668a23b9",
	Build: SubmoduleDef.Entry().Law("N ⊆ M.carrier",
		func(a *Argument, isSubmodule Fact) {
			a.Show(
				"N is a subgroup of M's carrier, and a subgroup lies in its carrier",
				By(group.SubgroupSubset.Read(SubmoduleSubgroup.Read(isSubmodule))))
		}),
})}

// SubmoduleZero — a submodule holds the zero vector: it is a subgroup of
// the vectors under the addition, and a subgroup holds the identity.
var SubmoduleZero = submoduleZeroThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleZero",
	Key:  "prop_1d3f27494e189ae2",
	Build: SubmoduleDef.Entry().Law("M.zero ∈ N",
		func(a *Argument, isSubmodule Fact) {
			a.Show(
				"N is a subgroup under the addition, and a subgroup holds its identity, the zero vector",
				By(group.SubgroupOne.Read(SubmoduleSubgroup.Read(isSubmodule))))
		}),
})}

// SubmoduleAdd — a submodule holds the sum of two of its vectors: it is a
// subgroup under the addition, closed under the group's product.
var SubmoduleAdd = submoduleAddThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleAdd",
	Key:  "prop_c39c65f6ba6b009e",
	Build: SubmoduleDef.Entry().Law(Statement{
		Binders: "∀u v:B.",
		Hypotheses: []string{
			"u ∈ N",
			"v ∈ N",
		},
		Conclusion: "u + v ∈ N",
	},
		func(a *Argument, isSubmodule Fact) {
			a.Show(
				"N is a subgroup under the addition, and a subgroup is closed under its product, the sum",
				By(group.SubgroupMul.Read(SubmoduleSubgroup.Read(isSubmodule))))
		}),
})}

// SubmoduleNeg — a submodule holds the negative of each of its vectors:
// it is a subgroup under the addition, closed under the group's inverse.
var SubmoduleNeg = submoduleNegThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleNeg",
	Key:  "prop_c967ddeee7bc9667",
	Build: SubmoduleDef.Entry().Law(Statement{
		Binders: "∀u:B.",
		Hypotheses: []string{
			"u ∈ N",
		},
		Conclusion: "-u ∈ N",
	},
		func(a *Argument, isSubmodule Fact) {
			a.Show(
				"N is a subgroup under the addition, and a subgroup is closed under its inverse, the negative",
				By(group.SubgroupInv.Read(SubmoduleSubgroup.Read(isSubmodule))))
		}),
})}

// SubmoduleSub — a submodule holds the difference of two of its vectors:
// it holds the negative of the second, and the sum.
var SubmoduleSub = submoduleSubThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleSub",
	Key:  "prop_4f9b63d07194ec7f",
	Build: SubmoduleDef.Entry().Law(Statement{
		Binders: "∀u v:B.",
		Hypotheses: []string{
			"u ∈ N",
			"v ∈ N",
		},
		Conclusion: "u + -v ∈ N",
	},
		func(a *Argument, isSubmodule Fact) {
			a.Show(
				"N holds −v, and the sum of u and −v",
				By(SubmoduleAdd.Read(isSubmodule), SubmoduleNeg.Read(isSubmodule)))
		}),
})}

// SubmoduleCriterion — a set of vectors holding the zero vector and
// closed under the sum and under scaling is a submodule: the negative
// of u is (−R.one) • u, a multiple of u, so the set is a subgroup of
// M's carrier under the addition, and it is closed under scaling.
var SubmoduleCriterion = submoduleCriterionThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleCriterion",
	Key:  "prop_6a6395b4744770fa",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N:set(B).",
		Hypotheses: []string{
			"N ⊆ M.carrier",
			"M.zero ∈ N",
			"∀u v:B. u ∈ N ∧ v ∈ N ⇒ u + v ∈ N",
			"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ N ⇒ c • u ∈ N",
		},
		Conclusion: "submodule(R, M, N)",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], N *Expr[Set[B]], given Fact) {
			parts := a.Conjuncts(
				given,
				"N lies in M's carrier",
				"N holds the zero vector",
				"N is closed under +",
				"N is closed under scaling")
			within, zero, sums, scaled := parts[0], parts[1], parts[2], parts[3]
			ring := module.RingOn.Read(ambient)
			one := a.MemberOf[on.R](a.TermAs[A]("R.one"), a.Have(
				"R.one is a scalar",
				"R.one ∈ R.carrier",
				By(comm_ring.OneIn.Read(ring))))
			negOne := comm_ring.NegIn.Read(ring).At(one)
			vectors := a.Unfolded(within, set_basic.SubsetDef)
			negatives := a.Have(
				"N is closed under negation: -u is (-R.one) • u",
				"∀u:B. u ∈ N ⇒ -u ∈ N",
				a.ForEach(func(u *Expr[B]) Action {
					return By(
						Normalized,
						vectors.At(u),
						module.NegOneSmul.Read(ambient).AsFact().At(u),
						scaled.At(negOne, u),
						negOne)
				}))
			subgroup := a.Have(
				"so N is a subgroup of M's carrier under the addition",
				"subgroup(module_additive_group(M), N)",
				By(within, zero, sums, negatives, group.SubgroupDef))
			a.Show(
				"a subgroup closed under scaling is a submodule",
				By(subgroup, scaled, SubmoduleDef))
		}),
})}

// SubmoduleModuleOn — a submodule is a module over the same ring, under
// M's operations on the carrier N: a subgroup of M's carrier is a group
// on its own set, N is closed under scaling, and each other condition is
// M's own law read at vectors of N, which lie in M's carrier.
var SubmoduleModuleOn = submoduleModuleOnThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleModuleOn",
	Key:  "prop_fc835892c5840e01",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
		},
		Conclusion: "module_on(R, restrict_module(M, N))",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], N *Expr[Set[B]], sub Fact) {
			additive := module.AddGroupOn.Read(ambient)
			// The conditions of module_on are proved here, before the
			// unfolding below: it also opens the resident module_on(R, M),
			// so its handles die.
			scalars := a.Have(
				"the scalars are M's ring",
				"comm_ring_on(R)",
				By(module.RingOn.Read(ambient)))
			within := a.Have(
				"N lies in M's carrier",
				"N ⊆ M.carrier",
				By(SubmoduleSubset.Read(sub)))
			vectors := a.Have(
				"N is a group under the vector addition, a subgroup of M's carrier being a group on its own set",
				"group_on(module_additive_group(restrict_module(M, N)))",
				Simp(Fwd(module_record.ModuleAdditiveGroupRestrict)),
				By(group.SubgroupGroupOn.Read(additive).At(N), SubmoduleSubgroup.Read(sub)))
			inclusion := a.Unfolded(within, set_basic.SubsetDef)
			commutes := a.Have(
				"the sum commutes on N, as on M's carrier",
				"∀u v:B. u ∈ N ∧ v ∈ N ⇒ u + v = v + u",
				By(module.AddComm.Read(ambient), inclusion))
			scaled := a.Have(
				"N is closed under scaling, being a submodule",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ N ⇒ c • u ∈ N",
				By(SubmoduleSmul.Read(sub)))
			distributes := a.Have(
				"a scalar distributes over a sum of vectors of N, as on M's carrier",
				"∀c:A. ∀u v:B. c ∈ R.carrier ∧ u ∈ N ∧ v ∈ N ⇒ c • (u + v) = c • u + c • v",
				By(module.SmulAddLeft.Read(ambient), inclusion))
			sums := a.Have(
				"a sum of scalars distributes over a vector of N, as on M's carrier",
				"∀c d:A. ∀u:B. c ∈ R.carrier ∧ d ∈ R.carrier ∧ u ∈ N ⇒ (c + d) • u = c • u + d • u",
				By(module.SmulAddRight.Read(ambient), inclusion))
			products := a.Have(
				"a product of scalars scales a vector of N in turn, as on M's carrier",
				"∀c d:A. ∀u:B. c ∈ R.carrier ∧ d ∈ R.carrier ∧ u ∈ N ⇒ (c * d) • u = c • (d • u)",
				By(module.SmulMul.Read(ambient), inclusion))
			one := a.Have(
				"the ring's one fixes every vector of N, as on M's carrier",
				"∀u:B. u ∈ N ⇒ R.one • u = u",
				By(module.SmulOne.Read(ambient), inclusion))
			a.Show(
				"unfolded, module_on at the restriction is met by the facts above",
				Unfold(module.ModuleOn),
				By(scalars, vectors, commutes, scaled, distributes, sums, products, one))
		}),
})}

// SubmoduleModuleSum — a submodule holds every finite sum of its
// vectors: under M's operations it is a module of its own, and a finite
// sum of vectors of a module is one of them.
var SubmoduleModuleSum = submoduleModuleSumThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleModuleSum",
	Key:  "prop_bda9c95c8fe8d4a1",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N:set(B). ∀s:set(D). ∀F:(D → B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) ∈ N",
		},
		Conclusion: "module_sum(M.add, M.zero, s, F) ∈ N",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			N *Expr[Set[B]],
			s *Expr[Set[D]],
			F *Arrow[D, B],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"N is a submodule",
				"s is finite",
				"F lies in N on s")
			restricted := a.Have(
				"N with M's operations is a module over R",
				"module_on(R, restrict_module(M, N))",
				By(parts[0], SubmoduleModuleOn.Read(ambient).At(N)))
			a.Show(
				"and a finite sum of vectors of that module lies in its carrier, N",
				By(parts[1], parts[2], module.ModuleSumIn.Read(restricted).At(s, F)))
		}),
})}

// CarrierSubmodule — M's carrier is a submodule of M: the carrier of any
// group is a subgroup of itself, here the group of the vectors under the
// addition, and scaling keeps a vector in the carrier.
var CarrierSubmodule = carrierSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "CarrierSubmodule",
	Key:  "prop_ad9d8bfaedec0c8e",
	Build: module.ModuleOn.Law("submodule(R, M, M.carrier)",
		func(a *Argument, ambient module.ModuleFact[on.R, on.M]) {
			additive := module.AddGroupOn.Read(ambient)
			a.Show(
				"the carrier is a subgroup of itself under the addition, and closed under scaling",
				By(group.CarrierSubgroupOn.Read(additive), module.SmulIn.Read(ambient), SubmoduleDef))
		}),
})}

// ZeroSubmodule — the set holding the zero vector alone is a submodule:
// it is the trivial subgroup of the vectors under the addition, and every
// scalar multiple of the zero vector is the zero vector.
var ZeroSubmodule = zeroSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "ZeroSubmodule",
	Key:  "prop_83b53cf09aae0ec4",
	Build: module.ModuleOn.Law("submodule(R, M, {M.zero})",
		func(a *Argument, ambient module.ModuleFact[on.R, on.M]) {
			trivial := a.Have(
				"{M.zero} is the trivial subgroup of the vectors under the addition",
				"subgroup(module_additive_group(M), {M.zero})",
				By(group.TrivialSubgroupOn.Read(module.AddGroupOn.Read(ambient))))
			scaled := a.Have(
				"{M.zero} is closed under scaling: its one vector is M.zero",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ {M.zero} ⇒ c • u ∈ {M.zero}",
				Simp(Fwd(set_basic.InSing)),
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					b.FixAs[B]("u")
					given := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u is M.zero")
					b.Show(
						"so c • u is c • M.zero, which is M.zero",
						given[1].Rw(),
						By(module.SmulZero.Read(ambient).At(b.MemberOf[on.R](c, given[0]))))
				}))
			a.Show(
				"a subgroup closed under scaling is a submodule",
				By(trivial, scaled, SubmoduleDef))
		}),
})}

// SubmoduleInter — two submodules meet in a submodule: the meet is a
// subgroup of the vectors, as the meet of two subgroups, and a multiple
// of a vector lying in both lies in both.
var SubmoduleInter = submoduleInterThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleInter",
	Key:  "prop_4fe57a7a81a6778d",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N N':set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"submodule(R, M, N')",
		},
		Conclusion: "submodule(R, M, N ∩ N')",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N, NPrime *Expr[Set[B]],
			given Fact,
		) {
			submodules := a.Conjuncts(
				given,
				"N is a submodule of M",
				"so is N'")
			sub, subPrime := submodules[0], submodules[1]
			subgroup := a.Have(
				"N ∩ N' is a subgroup of the vectors under the addition, the meet of two subgroups",
				"subgroup(module_additive_group(M), N ∩ N')",
				By(group_isomorphism.SubgroupInter, SubmoduleSubgroup.Read(sub), SubmoduleSubgroup.Read(subPrime)))
			scaled := a.Have(
				"N ∩ N' is closed under scaling: a multiple of a vector of both lies in N and in N'",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ N ∩ N' ⇒ c • u ∈ N ∩ N'",
				By(SubmoduleSmul.Read(sub), SubmoduleSmul.Read(subPrime), set_basic.InInter))
			a.Show(
				"a subgroup closed under scaling is a submodule",
				By(subgroup, scaled, SubmoduleDef))
		}),
})}

// SubmoduleSum — the sum N + N' of two submodules, the set of sums, is
// a submodule: the additive group commutes, so a sum of subgroups is a
// subgroup, and scaling distributes over the sums.
var SubmoduleSum = submoduleSumThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleSum",
	Key:  "prop_471d38862e570a3e",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N N':set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"submodule(R, M, N')",
		},
		Conclusion: "submodule(R, M, set_mul(M.add, N, N'))",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], N, NPrime *Expr[Set[B]], given Fact) {
			submodules := a.Conjuncts(
				given,
				"N is a submodule of M",
				"so is N'")
			sub, subPrime := submodules[0], submodules[1]
			additive := module.AddGroupOn.Read(ambient)
			inN := a.Unfolded(SubmoduleSubset.Read(sub).AsFact(), set_basic.SubsetDef)
			inNPrime := a.Unfolded(SubmoduleSubset.Read(subPrime).AsFact(), set_basic.SubsetDef)
			subgroup := a.Have(
				"N + N' is a subgroup of the vectors: N is a subgroup, and N', as every submodule, a normal one",
				"subgroup(module_additive_group(M), set_mul(M.add, N, N'))",
				By(
					group_isomorphism.SetMulNormal.Read(additive).At(N, NPrime),
					SubmoduleSubgroup.Read(sub),
					SubmoduleNormal.Read(ambient).At(NPrime),
					subPrime))
			scaled := a.Have(
				"N + N' is closed under scaling, a scalar distributing over a sum of vectors",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ set_mul(M.add, N, N') ⇒ c • u ∈ set_mul(M.add, N, N')",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					b.FixAs[B]("u")
					hypotheses := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"u lies in N + N'")
					x, y, sum := b.Unpack2As[B, B](b.Simplified(hypotheses[1], Fwd(quotient_group.InSetMul)), "x", "y")
					parts := b.Conjuncts(
						sum,
						"x lies in N",
						"y lies in N'",
						"u is x + y")
					xM := b.MemberOf[on.M](x, b.Have(
						"x is a vector, N lying in M's carrier",
						"x ∈ M.carrier",
						By(inN, parts[0])))
					yM := b.MemberOf[on.M](y, b.Have(
						"and so is y, N' lying there too",
						"y ∈ M.carrier",
						By(inNPrime, parts[1])))
					cR := b.MemberOf[on.R](c, hypotheses[0])
					b.Do(Simp(Fwd(quotient_group.InSetMul)))
					b.Take(b.TermAs[B]("c • x"))
					b.Take(b.TermAs[B]("c • y"))
					b.Show(
						"c • u is c • (x + y) = c • x + c • y, and c • x lies in N, c • y in N'",
						By(
							parts[2],
							module.SmulAddLeft.Read(ambient).At(cR, xM, yM),
							SubmoduleSmul.Read(sub),
							SubmoduleSmul.Read(subPrime),
							hypotheses[0],
							parts[0],
							parts[1]))
				}))
			a.Show(
				"a subgroup closed under scaling is a submodule",
				By(subgroup, scaled, SubmoduleDef))
		}),
})}

// SumLeast — a submodule holding X and Y holds X + Y: a member of X + Y
// is x + y with x in X and y in Y, both in N, which is closed under sums.
var SumLeast = sumLeastThm{family.Add(registry.ProofEntry{
	Name: "SumLeast",
	Key:  "prop_6e65ddc34fbf4484",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀X Y N:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"X ⊆ N",
			"Y ⊆ N",
		},
		Conclusion: "set_mul(M.add, X, Y) ⊆ N",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			X, Y, N *Expr[Set[B]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"N is a submodule",
				"X lies in N",
				"Y lies in N")
			a.Show(
				"a member x + y of X + Y has both summands in N",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					z := b.FixAs[B]("z")
					_, _, zIs := b.Unpack2As[B, B](b.Have(
						"z is a sum of a member of X and a member of Y",
						"∃x y:B. x ∈ X ∧ y ∈ Y ∧ z = x + y",
						By(b.Assume(), quotient_group.InSetMul.At(b.TermAs[Op[B]]("M.add"), X, Y, z))), "x", "y")
					summands := b.Conjuncts(
						zIs,
						"x lies in X",
						"y lies in Y",
						"z is their sum")
					b.Show(
						"both lie in N, which is closed under sums",
						By(
							Normalized,
							b.Have(
								"x and y lie in N",
								"x ∈ N ∧ y ∈ N",
								BySets(summands[0], summands[1], parts[1], parts[2])),
							summands[2],
							SubmoduleAdd.Read(parts[0])))
				}))
		}),
})}

// SumContainsLeft — a submodule lies in its sum with another: each x of N
// is x + 0, and 0 lies in N'.
var SumContainsLeft = sumContainsLeftThm{family.Add(registry.ProofEntry{
	Name: "SumContainsLeft",
	Key:  "prop_32fa4bec4a854d5b",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N N':set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"submodule(R, M, N')",
		},
		Conclusion: "N ⊆ set_mul(M.add, N, N')",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], N, NPrime *Expr[Set[B]], given Fact) {
			submodules := a.Conjuncts(
				given,
				"N is a submodule",
				"so is N'")
			additive := module.AddGroupOn.Read(ambient)
			inM := a.Unfolded(SubmoduleSubset.Read(submodules[0]).AsFact(), set_basic.SubsetDef)
			zero := a.Have(
				"N' holds zero",
				"M.zero ∈ N'",
				By(SubmoduleZero.Read(submodules[1])))
			a.Show(
				"each x of N is x + 0",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inN := b.Assume()
					xm := b.MemberOf[on.M](x, b.Have(
						"x is a vector, N lying in M's carrier",
						"x ∈ M.carrier",
						By(inM, inN)))
					b.Show(
						"x = x + 0, with x in N and 0 in N'",
						By(
							inN,
							zero,
							group.RightIdentityOn.Read(additive).At(xm),
							quotient_group.InSetMul.At(b.TermAs[Op[B]]("M.add"), N, NPrime, x)))
				}))
		}),
})}

// SumContainsRight — and so does the other: each y of N' is 0 + y, and 0
// lies in N.
var SumContainsRight = sumContainsRightThm{family.Add(registry.ProofEntry{
	Name: "SumContainsRight",
	Key:  "prop_4afa93f9f19477a",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N N':set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"submodule(R, M, N')",
		},
		Conclusion: "N' ⊆ set_mul(M.add, N, N')",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], N, NPrime *Expr[Set[B]], given Fact) {
			submodules := a.Conjuncts(
				given,
				"N is a submodule",
				"so is N'")
			additive := module.AddGroupOn.Read(ambient)
			inM := a.Unfolded(SubmoduleSubset.Read(submodules[1]).AsFact(), set_basic.SubsetDef)
			zero := a.Have(
				"N holds zero",
				"M.zero ∈ N",
				By(SubmoduleZero.Read(submodules[0])))
			a.Show(
				"each y of N' is 0 + y",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					inNPrime := b.Assume()
					ym := b.MemberOf[on.M](y, b.Have(
						"y is a vector, N' lying in M's carrier",
						"y ∈ M.carrier",
						By(inM, inNPrime)))
					b.Show(
						"y = 0 + y, with 0 in N and y in N'",
						By(
							inNPrime,
							zero,
							group.LeftIdentityOn.Read(additive).At(ym),
							quotient_group.InSetMul.At(b.TermAs[Op[B]]("M.add"), N, NPrime, y)))
				}))
		}),
})}

// SubmoduleTrans — a submodule of a submodule is a submodule: K a
// submodule of N with M's operations is one of M. The restriction to N
// keeps M's operations, so K is a subgroup of N under M's addition, and N
// a subgroup of M's carrier, which makes K one of M's carrier; the
// restriction scales as M does, so K is closed under M's scaling.
var SubmoduleTrans = submoduleTransThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleTrans",
	Key:  "prop_fd520974bcc1dffe",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N K:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"submodule(R, restrict_module(M, N), K)",
		},
		Conclusion: "submodule(R, M, K)",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N, K *Expr[Set[B]], given Fact) {
			parts := a.Conjuncts(
				given,
				"N is a submodule of M",
				"K is a submodule of N under M's operations")
			nSub, kSub := parts[0], parts[1]
			subgroup := a.Have(
				"K is a subgroup of M's additive group",
				"subgroup(module_additive_group(M), K)",
				By(
					group_isomorphism.SubgroupTrans.At(a.TermAs[group.GroupOps[B]]("module_additive_group(M)"), N, K),
					SubmoduleSubgroup.Read(nSub),
					module_record.ModuleAdditiveGroupRestrict.At(M, N),
					SubmoduleSubgroup.Read(kSub)))
			a.Show(
				"K is a subgroup of M's carrier closed under scaling, the restriction scaling as M does",
				By(subgroup, SubmoduleSmul.Read(kSub), SubmoduleDef))
		}),
})}

// SubmoduleRestrict — a submodule of M lying in a set N is a submodule
// of M's operations on the carrier N: the restriction keeps M's
// operations, so K, a subgroup of M's carrier lying in N, is a subgroup of
// N, and it is closed under scaling as a submodule of M.
var SubmoduleRestrict = submoduleRestrictThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleRestrict",
	Key:  "prop_c912fc01be6a351",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N K:set(B).",
		Hypotheses: []string{
			"submodule(R, M, K)",
			"K ⊆ N",
		},
		Conclusion: "submodule(R, restrict_module(M, N), K)",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], N, K *Expr[Set[B]], given Fact) {
			parts := a.Conjuncts(
				given,
				"K is a submodule of M",
				"K lies in N")
			sub, inside := parts[0], parts[1]
			subgroup := a.Have(
				"K is a subgroup of M's carrier lying in N, so a subgroup of N under M's addition",
				"subgroup(module_additive_group(restrict_module(M, N)), K)",
				Simp(Fwd(module_record.ModuleAdditiveGroupRestrict)),
				By(group_isomorphism.SubgroupRestrict, SubmoduleSubgroup.Read(sub), inside))
			a.Show(
				"the restriction has M's operations on the carrier N, so K, "+
					"a subgroup of N closed under scaling, is a submodule of it",
				By(subgroup, SubmoduleSmul.Read(sub), SubmoduleDef))
		}),
})}

// IdealIffRegularSubmodule — in a commutative ring R, the ideals are the
// submodules of R as a module over itself: both are the subsets of R
// holding zero, closed under addition and under multiplication by R.
var IdealIffRegularSubmodule = idealIffRegularSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "IdealIffRegularSubmodule",
	Key:  "prop_1a5a91f7156fcc09",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀I:set(A).",
		Hypotheses: []string{"comm_ring_on(R)"},
		Conclusion: "ring_ideal(R, I) ⇔ submodule(R, regular_module(R), I)",
	},
		func(a *Argument, R *Expr[RingOps[A]], I *Expr[Set[A]], ring Fact) {
			V := a.TermAs[ModuleOps[A, A]]("regular_module(R)")
			a.Show(
				"ideals and regular-module submodules have the same closure laws",
				By(
					ring,
					ring_ideal.RingIdealDef.At(R, I),
					module.RegularModuleOn.At(R),
					SubmoduleCriterion.At(R, V, I),
					SubmoduleSubset.At(R, V, I),
					SubmoduleZero.At(R, V, I),
					At(SubmoduleAdd, R, V, I),
					At(SubmoduleSmul, R, V, I),
					module_record.RegularModuleDef.At(R)))
		}),
})}

// ---------------------------------------------------------------------------
// The submodule a set spans
// ---------------------------------------------------------------------------

// SubmoduleRestrictScalars — a submodule for the scalars of R is one for
// any ring R' whose scalars lie among R's: a submodule is a subgroup of
// the vectors closed under scaling, and R' scales by fewer scalars.
var SubmoduleRestrictScalars = submoduleRestrictScalarsThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleRestrictScalars",
	Key:  "prop_af08b3142b01e537",
	Build: SubmoduleDef.Entry().Law(Statement{
		Binders: "∀R':ring_ops(A).",
		Hypotheses: []string{
			"R'.carrier ⊆ R.carrier",
		},
		Conclusion: "submodule(R', M, N)",
	},
		func(a *Argument, sub Fact, RPrime *Expr[RingOps[A]], fewer Fact) {
			a.Show(
				"N is a subgroup of the vectors, and a scalar of R' is one of R, which scales N into itself",
				By(
					SubmoduleSubgroup.Read(sub),
					SubmoduleSmul.Read(sub),
					a.Unfolded(fewer, set_basic.SubsetDef),
					SubmoduleDef))
		}),
})}

// ModuleSpanDef — `module_span(R, M, S)`: the least submodule of M
// holding S, the meet of all of them.
var ModuleSpanDef = moduleSpanDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleSpanDef",
	Key:   "prop_9b9d7be11b23b38b",
	Const: "module_span",
	Type:  "ring_ops(A) → module_ops(A, B) → set(B) → set(B)",
	Equations: []string{
		records + "∀S:set(B). module_span(R, M, S) = ⋂{N:set(B) | submodule(R, M, N) ∧ S ⊆ N}",
	},
	Deps: []registry.EntryLike{SubmoduleDef},
})}

// SpanSubmodule — the span of a set of vectors in M's carrier is a
// submodule: a vector lies in the span exactly when it lies in every
// submodule holding the set, so each closure condition passes from those
// submodules to the span, and M's carrier, one of them, bounds it.
var SpanSubmodule = spanSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "SpanSubmodule",
	Key:  "prop_80c575a5d778b732",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B).",
		Hypotheses: []string{
			"S ⊆ M.carrier",
		},
		Conclusion: "submodule(R, M, module_span(R, M, S))",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], S *Expr[Set[B]], inCarrier Fact) {
			points := a.Have(
				"a vector lies in the span exactly when it lies in every submodule holding S",
				"∀x:B. x ∈ module_span(R, M, S) ⇔ ∀N:set(B). submodule(R, M, N) ∧ S ⊆ N ⇒ x ∈ N",
				Unfold(ModuleSpanDef),
				BySets())
			bounded := a.Have(
				"M's carrier is a submodule holding S, so the span lies inside it",
				"module_span(R, M, S) ⊆ M.carrier",
				By(SpanLeast, CarrierSubmodule.Read(ambient), inCarrier))
			zero := a.Have(
				"the zero vector lies in every submodule, so in the span",
				"M.zero ∈ module_span(R, M, S)",
				By(points, SubmoduleZero))
			sums := a.Have(
				"a submodule holding S holds two vectors of the span, so their sum",
				"∀u v:B. u ∈ module_span(R, M, S) ∧ v ∈ module_span(R, M, S) ⇒ u + v ∈ module_span(R, M, S)",
				By(points, SubmoduleAdd))
			negatives := a.Have(
				"a submodule holding S holds a vector of the span, so its negative",
				"∀u:B. u ∈ module_span(R, M, S) ⇒ -u ∈ module_span(R, M, S)",
				By(points, SubmoduleNeg))
			scaled := a.Have(
				"a submodule holding S holds a vector of the span, so each of its multiples",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ module_span(R, M, S) ⇒ c • u ∈ module_span(R, M, S)",
				By(points, SubmoduleSmul))
			subgroup := a.Have(
				"so the span is a subgroup of M's carrier under the addition",
				"subgroup(module_additive_group(M), module_span(R, M, S))",
				By(bounded, zero, sums, negatives, group.SubgroupDef))
			a.Show(
				"a subgroup closed under scaling is a submodule",
				By(subgroup, scaled, SubmoduleDef))
		}),
})}

// SubsetSpan — a set lies in its span: the span is the meet of the
// submodules holding the set, and each of them holds it.
var SubsetSpan = subsetSpanThm{family.Add(registry.ProofEntry{
	Name: "SubsetSpan",
	Key:  "prop_5c20241d2ff7a2a3",
	Build: family.Theorem("∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S:set(B). S ⊆ module_span(R, M, S)",
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], S *Expr[Set[B]]) {
			a.Show(
				"the span is the meet of the submodules holding S, and each of them holds S",
				Unfold(ModuleSpanDef),
				BySets())
		}),
})}

// SpanLeast — the span of a set lies in every submodule holding the
// set: it is the least such submodule.
var SpanLeast = spanLeastThm{family.Add(registry.ProofEntry{
	Name: "SpanLeast",
	Key:  "prop_49a826f90540d3ea",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S N:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"S ⊆ N",
		},
		Conclusion: "module_span(R, M, S) ⊆ N",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			S, N *Expr[Set[B]],
			hypotheses Fact,
		) {
			member := a.Have(
				"N is a member of the family the span intersects",
				"N ∈ {K:set(B) | submodule(R, M, K) ∧ S ⊆ K}",
				BySets(hypotheses))
			a.Show(
				"and an intersection lies in each of its members",
				Unfold(ModuleSpanDef),
				BySets(member))
		}),
})}

// SpanMono — a larger set spans more: a submodule holding T holds S, so
// the span of S lies in each submodule the span of T is the meet of.
var SpanMono = spanMonoThm{family.Add(registry.ProofEntry{
	Name: "SpanMono",
	Key:  "prop_bb3f176ed305dfe4",
	Reading: "Needs no module law and no hypothesis on T: " +
		"when no submodule of M holds T, its span is ⋂∅ = 𝕌.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀S T:set(B).",
		Hypotheses: []string{
			"S ⊆ T",
		},
		Conclusion: "module_span(R, M, S) ⊆ module_span(R, M, T)",
	},
		func(a *Argument, R *Expr[RingOps[A]], M *Expr[ModuleOps[A, B]], S, T *Expr[Set[B]], below Fact) {
			a.Show(
				"every submodule holding T holds S",
				Unfold(ModuleSpanDef),
				BySets(below))
		}),
})}

// SpanEmpty — the empty set spans the zero vector alone: its span is a
// submodule, so it holds the zero vector, and {M.zero} is a submodule
// holding ∅, so it holds the span.
var SpanEmpty = spanEmptyThm{family.Add(registry.ProofEntry{
	Name: "SpanEmpty",
	Key:  "prop_3e4e12af5fe9f23e",
	Build: module.ModuleOn.Law("module_span(R, M, ∅) = {M.zero}",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			ambient module.ModuleFact[on.R, on.M],
		) {
			empty, zeroSet := a.TermAs[Set[B]]("∅"), a.TermAs[Set[B]]("{M.zero}")
			span := a.TermAs[Set[B]]("module_span(R, M, ∅)")
			spanSubmodule := a.Have(
				"∅ lies in M, so its span is a submodule",
				"submodule(R, M, module_span(R, M, ∅))",
				By(set_order.EmptySubset.At(a.TermAs[Set[B]]("M.carrier")), SpanSubmodule.Read(ambient).At(empty)))
			zeroIn := a.Have(
				"a submodule holds the zero vector",
				"M.zero ∈ module_span(R, M, ∅)",
				By(SubmoduleZero.Read(spanSubmodule)))
			within := a.Have(
				"{M.zero} is a submodule holding ∅, so it holds the span",
				"module_span(R, M, ∅) ⊆ {M.zero}",
				By(
					ZeroSubmodule.Read(ambient),
					set_order.EmptySubset.At(zeroSet),
					SpanLeast.At(R, M, empty, zeroSet)))
			a.Show(
				"so the span is {M.zero}",
				By(
					zeroIn,
					within,
					set_order.SingSubset.At(span, a.TermAs[B]("M.zero")),
					set_order.SubsetAntisym.At(span, zeroSet)))
		}),
})}

// SpanInsert — the span of one more vector: its multiples plus the span
// of the rest. The sums c • v + w, c a scalar and w in the span of S,
// form a submodule holding v = R.one • v + M.zero and each
// s = R.zero • v + s of S, so they hold the span of insert(v, S); and
// each of them lies in that span, which holds c • v and the span of S.
var SpanInsert = spanInsertThm{family.Add(registry.ProofEntry{
	Name: "SpanInsert",
	Key:  "prop_fa4e43f053438b81",
	Reading: "S ⊆ M.carrier and v ∈ M.carrier are both load-bearing: if " +
		"either fails, insert(v, S) leaves M and its span is ⋂∅ = 𝕌. v ∈ S is " +
		"allowed: both sides are then the span of S, c • v already lying in it.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B). ∀v:B.",
		Hypotheses: []string{
			"S ⊆ M.carrier",
			"v ∈ M.carrier",
		},
		Conclusion: "module_span(R, M, insert(v, S)) = " +
			"{c • v + w | c:A, w:B | c ∈ R.carrier ∧ w ∈ module_span(R, M, S)}",
	},
		func(
			arg *Argument,
			moduleOn module.ModuleFact[on.R, on.M],
			S *Expr[Set[B]],
			v *Expr[B],
			hypotheses Fact,
		) {
			R, M := arg.TermAs[RingOps[A]]("R"), arg.TermAs[ModuleOps[A, B]]("M")
			given := arg.Conjuncts(
				hypotheses,
				"S lies in M",
				"v lies in M")
			sInM, vIn := given[0], given[1]
			vM := arg.MemberOf[on.M](v, vIn)
			ring := module.RingOn.Read(moduleOn)
			zeroIn := comm_ring.ZeroIn.Read(ring)
			carrier := arg.TermAs[Set[B]]("M.carrier")
			inserted := arg.TermAs[Set[B]]("insert(v, S)")
			spanInserted := arg.TermAs[Set[B]]("module_span(R, M, insert(v, S))")
			zero := arg.TermAs[B]("M.zero")

			// P, the sums c • v + w, read as a membership.
			P, sumsDef := arg.LetAs[Set[B]](
				"P", "{c • v + w | c:A, w:B | c ∈ R.carrier ∧ w ∈ module_span(R, M, S)}")
			inP := arg.Have(
				"z lies in P exactly when it is c • v + w for a scalar c and a w in the span of S",
				"∀z:B. z ∈ P ⇔ ∃c:A. ∃w:B. c ∈ R.carrier ∧ w ∈ module_span(R, M, S) ∧ z = c • v + w",
				BySets(sumsDef))
			intoP := arg.Have(
				"so a vector that is c • v + w, for a scalar c and a w in the span of S, lies in P",
				"∀z:B. ∀c:A. ∀w:B. c ∈ R.carrier ∧ w ∈ module_span(R, M, S) ∧ z = c • v + w ⇒ z ∈ P",
				BySets(sumsDef))

			// The two spans are submodules.
			spanSubmodule := arg.Have(
				"the span of S is a submodule of M",
				"submodule(R, M, module_span(R, M, S))",
				By(sInM, SpanSubmodule.Read(moduleOn).At(S)))
			inSpanInM := arg.Unfolded(SubmoduleSubset.Read(spanSubmodule).AsFact(), set_basic.SubsetDef)
			insertedInM := arg.Have(
				"insert(v, S) lies in M",
				"insert(v, S) ⊆ M.carrier",
				By(vIn, sInM, set_order.InsertSubset.At(S, carrier, v)))
			insertedSpanSubmodule := arg.Have(
				"and so the span of insert(v, S) is a submodule of M",
				"submodule(R, M, module_span(R, M, insert(v, S)))",
				By(insertedInM, SpanSubmodule.Read(moduleOn).At(inserted)))

			// ⊇: the span of insert(v, S) holds v and the span of S, so P.
			vInSpan := arg.Have(
				"v lies in the span of insert(v, S)",
				"v ∈ module_span(R, M, insert(v, S))",
				BySets(SubsetSpan.At(R, M, inserted)))
			sInInserted := arg.Have(
				"S lies in insert(v, S)",
				"S ⊆ insert(v, S)",
				BySets())
			spanGrows := arg.Have(
				"so the span of S lies in the span of insert(v, S)",
				"module_span(R, M, S) ⊆ module_span(R, M, insert(v, S))",
				By(sInInserted, SpanMono.At(R, M, S, inserted)))
			grows := arg.Unfolded(spanGrows, set_basic.SubsetDef)
			pointwise := arg.Have(
				"each c • v + w of P lies in the span of insert(v, S), which holds c • v and w",
				"∀z:B. z ∈ P ⇒ z ∈ module_span(R, M, insert(v, S))",
				Derive(func(b *Argument) {
					z := b.FixAs[B]("z")
					c, w, zIs := b.Obtain2As[A, B](
						"z is c • v + w for a scalar c and a w in the span of S",
						"∃c:A. ∃w:B. c ∈ R.carrier ∧ w ∈ module_span(R, M, S) ∧ z = c • v + w",
						By(inP.At(z), b.Assume()))
					parts := b.Conjuncts(
						zIs,
						"c is a scalar",
						"w lies in the span of S",
						"z is c • v + w")
					multiple := b.Have(
						"c • v lies in the span of insert(v, S)",
						"c • v ∈ module_span(R, M, insert(v, S))",
						By(SubmoduleSmul.Read(insertedSpanSubmodule).At(
							proof.MemberOf(c, parts[0]), proof.MemberOf(v, vInSpan))))
					b.Show(
						"and so does w, so their sum z does",
						parts[2].Rw(),
						By(
							multiple,
							grows.At(w),
							parts[1],
							SubmoduleAdd.Read(insertedSpanSubmodule).AsFact().At(b.TermAs[B]("c • v"), w)))
				}))
			pInSpan := arg.Have(
				"so P lies in the span of insert(v, S)",
				"P ⊆ module_span(R, M, insert(v, S))",
				BySets(pointwise))
			pInM := arg.Have(
				"and so in M, where that span lies",
				"P ⊆ M.carrier",
				By(
					pInSpan,
					SubmoduleSubset.Read(insertedSpanSubmodule),
					set_order.SubsetTrans.At(P, spanInserted, carrier)))

			// ⊆: P is a submodule holding insert(v, S).
			// A regrouping is a module identity, which the chase normalizer closes.
			zeroSplits := arg.Have(
				"M.zero is R.zero • v + M.zero",
				"M.zero = R.zero • v + M.zero",
				ByChase(Depth(0), moduleOn, vM))
			zeroInP := arg.Have(
				"so M.zero lies in P",
				"M.zero ∈ P",
				By(
					intoP.At(zero, arg.TermAs[A]("R.zero"), zero),
					zeroIn,
					SubmoduleZero.Read(spanSubmodule),
					zeroSplits))
			sums := arg.Have(
				"P is closed under +: (c₁ • v + w₁) + (c₂ • v + w₂) is (c₁ + c₂) • v + (w₁ + w₂)",
				"∀x y:B. x ∈ P ∧ y ∈ P ⇒ x + y ∈ P",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					y := b.FixAs[B]("y")
					assumed := b.Conjuncts(
						b.Assume(),
						"x lies in P",
						"y lies in P")
					c1, w1, xIs := b.Obtain2As[A, B](
						"x is c₁ • v + w₁ for a scalar c₁ and a w₁ in the span of S",
						"∃c₁:A. ∃w₁:B. c₁ ∈ R.carrier ∧ w₁ ∈ module_span(R, M, S) ∧ x = c₁ • v + w₁",
						By(inP.At(x), assumed[0]))
					c2, w2, yIs := b.Obtain2As[A, B](
						"y is c₂ • v + w₂ for a scalar c₂ and a w₂ in the span of S",
						"∃c₂:A. ∃w₂:B. c₂ ∈ R.carrier ∧ w₂ ∈ module_span(R, M, S) ∧ y = c₂ • v + w₂",
						By(inP.At(y), assumed[1]))
					first := b.Conjuncts(
						xIs,
						"c₁ is a scalar",
						"w₁ lies in the span of S",
						"x is c₁ • v + w₁")
					second := b.Conjuncts(
						yIs,
						"c₂ is a scalar",
						"w₂ lies in the span of S",
						"y is c₂ • v + w₂")
					c1R, c2R := b.MemberOf[on.R](c1, first[0]), b.MemberOf[on.R](c2, second[0])
					w1M, w2M :=
						b.MemberOf[on.M](w1, GroupPremises(first[1], inSpanInM.At(w1))),
						b.MemberOf[on.M](w2, GroupPremises(second[1], inSpanInM.At(w2)))
					regroup := b.Have(
						"x + y regroups as (c₁ + c₂) • v + (w₁ + w₂)",
						"x + y = (c₁ + c₂) • v + (w₁ + w₂)",
						ByChase(Depth(0), moduleOn, c1R, c2R, vM, w1M, w2M, first[2], second[2]))
					b.Show(
						"c₁ + c₂ is a scalar and w₁ + w₂ lies in the span of S",
						By(
							intoP.At(b.TermAs[B]("x + y"), b.TermAs[A]("c₁ + c₂"), b.TermAs[B]("w₁ + w₂")),
							comm_ring.AddIn.Read(ring).At(c1R, c2R),
							SubmoduleAdd.Read(spanSubmodule).At(proof.MemberOf(w1, first[1]), proof.MemberOf(w2, second[1])),
							regroup))
				}))
			scalings := arg.Have(
				"P is closed under scaling: a • (c • v + w) is (a * c) • v + a • w",
				"∀a:A. ∀x:B. a ∈ R.carrier ∧ x ∈ P ⇒ a • x ∈ P",
				Derive(func(b *Argument) {
					a := b.FixAs[A]("a")
					x := b.FixAs[B]("x")
					assumed := b.Conjuncts(
						b.Assume(),
						"a is a scalar",
						"x lies in P")
					c, w, xIs := b.Obtain2As[A, B](
						"x is c • v + w for a scalar c and a w in the span of S",
						"∃c:A. ∃w:B. c ∈ R.carrier ∧ w ∈ module_span(R, M, S) ∧ x = c • v + w",
						By(inP.At(x), assumed[1]))
					parts := b.Conjuncts(
						xIs,
						"c is a scalar",
						"w lies in the span of S",
						"x is c • v + w")
					aR, cR := b.MemberOf[on.R](a, assumed[0]), b.MemberOf[on.R](c, parts[0])
					wM := b.MemberOf[on.M](w, GroupPremises(parts[1], inSpanInM.At(w)))
					regroup := b.Have(
						"a • x regroups as (a * c) • v + a • w",
						"a • x = (a * c) • v + a • w",
						ByChase(Depth(0), moduleOn, aR, cR, vM, wM, parts[2]))
					b.Show(
						"a * c is a scalar and a • w lies in the span of S",
						By(
							intoP.At(b.TermAs[B]("a • x"), b.TermAs[A]("a * c"), b.TermAs[B]("a • w")),
							comm_ring.MulIn.Read(ring).At(aR, cR),
							SubmoduleSmul.Read(spanSubmodule).At(proof.MemberOf(a, assumed[0]), proof.MemberOf(w, parts[1])),
							regroup))
				}))
			isSubmodule := arg.Have(
				"P is a submodule of M: it lies in M, holds M.zero, and is closed under + and scaling",
				"submodule(R, M, P)",
				By(pInM, zeroInP, sums, scalings, SubmoduleCriterion.Read(moduleOn).At(P)))
			oneSplits := arg.Have(
				"v is R.one • v + M.zero",
				"v = R.one • v + M.zero",
				ByChase(Depth(0), moduleOn, vM))
			vInP := arg.Have(
				"so v lies in P",
				"v ∈ P",
				By(
					intoP.At(v, arg.TermAs[A]("R.one"), zero),
					comm_ring.OneIn.Read(ring),
					SubmoduleZero.Read(spanSubmodule),
					oneSplits))
			inM := arg.Unfolded(sInM, set_basic.SubsetDef)
			inSpanOfS := arg.Unfolded(SubsetSpan.At(R, M, S), set_basic.SubsetDef)
			eachS := arg.Have(
				"each s of S is R.zero • v + s, with s in the span of S, so it lies in P",
				"∀s:B. s ∈ S ⇒ s ∈ P",
				Derive(func(b *Argument) {
					s := b.FixAs[B]("s")
					memberOfS := b.Assume()
					sM := b.MemberOf[on.M](s, GroupPremises(memberOfS, inM.At(s)))
					splits := b.Have(
						"s is R.zero • v + s",
						"s = R.zero • v + s",
						ByChase(Depth(0), moduleOn, vM, sM))
					b.Show(
						"R.zero is a scalar and s lies in the span of S",
						By(intoP.At(s, b.TermAs[A]("R.zero"), s), zeroIn, inSpanOfS.At(s), memberOfS, splits))
				}))
			sInP := arg.Have(
				"so S lies in P",
				"S ⊆ P",
				BySets(eachS))
			insertedInP := arg.Have(
				"so insert(v, S) lies in P",
				"insert(v, S) ⊆ P",
				By(vInP, sInP, set_order.InsertSubset.At(S, P, v)))
			spanInP := arg.Have(
				"and the span of insert(v, S), the least submodule holding it, lies in P",
				"module_span(R, M, insert(v, S)) ⊆ P",
				By(isSubmodule, insertedInP, SpanLeast.At(R, M, inserted, P)))
			arg.Show(
				"P lies in that span as well, so the two are one set",
				By(spanInP, pInSpan, set_order.SubsetAntisym.At(spanInserted, P)))
		}),
})}

// SpanOfSubmodule — a submodule is its own span: it is the least
// submodule holding itself.
var SpanOfSubmodule = spanOfSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "SpanOfSubmodule",
	Key:  "prop_518e623c048f6c86",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
		},
		Conclusion: "module_span(R, M, N) = N",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[Set[B]],
			isSubmodule Fact,
		) {
			span := a.TermAs[Set[B]]("module_span(R, M, N)")
			within := a.Have(
				"the span is the least submodule holding N, and N is a submodule holding itself",
				"module_span(R, M, N) ⊆ N",
				By(isSubmodule, set_order.SubsetRefl.At(N), SpanLeast.At(R, M, N, N)))
			a.Show(
				"N lies in its span as well, so the two are one set",
				By(within, SubsetSpan.At(R, M, N), set_order.SubsetAntisym.At(span, N)))
		}),
})}

// SpanClosureOperator — span is a closure operator on the subsets of a
// module's carrier: each set has a least submodule above it in the
// powerset order.
var SpanClosureOperator = spanClosureOperatorThm{family.Add(registry.ProofEntry{
	Name: "SpanClosureOperator",
	Key:  "prop_3b8d50982c6017fe",
	Build: module.ModuleOn.Law("closure_operator_on({S:set(B) | S ⊆ M.carrier}, "+
		"    λS:set(B). λT:set(B). S ⊆ T, "+
		"    λS:set(B). module_span(R, M, S))",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			ambient module.ModuleFact[on.R, on.M],
		) {
			powerset := a.Have(
				"the subsets of the module's carrier form a complete lattice",
				"complete_lattice_on({S:set(B) | S ⊆ M.carrier}, "+
					"    λS:set(B). λT:set(B). S ⊆ T, "+
					"    λF:set(set(B)). ⋃F, "+
					"    λF:set(set(B)). M.carrier ∩ ⋂F)",
				By(order.PowersetCompleteLattice))
			submodulesWithin := a.Have(
				"every submodule belongs to this powerset",
				"{N:set(B) | submodule(R, M, N)} ⊆ {S:set(B) | S ⊆ M.carrier}",
				By(At(SubmoduleSubset, R, M), set_basic.SubsetDef))
			least := a.Have(
				"the span is the least submodule containing each set in the carrier",
				Statement{
					Binders: "∀S:set(B).",
					Hypotheses: []string{
						"S ⊆ M.carrier",
					},
					Conclusion: "submodule(R, M, module_span(R, M, S)) ∧ " +
						"S ⊆ module_span(R, M, S) ∧ " +
						"(∀N:set(B). submodule(R, M, N) ∧ S ⊆ N ⇒ module_span(R, M, S) ⊆ N)",
				},
				By(SpanSubmodule.Read(ambient), At(SubsetSpan, R, M), At(SpanLeast, R, M)))
			submodules := a.TermAs[Set[Set[B]]]("{N:set(B) | submodule(R, M, N)}")
			a.Show(
				"least submodules above sets give a closure operator on the powerset",
				By(
					order.CompleteLatticeOnPartialOrder.Read(powerset),
					least,
					submodulesWithin,
					Where(order.ClosureFromLeast, "F", submodules)))
		}),
})}

// SpanOfSubringSpan — over a ring R, spanning the span of X over a ring R₀
// of fewer scalars spans what X spans: the R₀-span lies between X and the
// R-span of X, which is a submodule for R₀ as well as for R.
var SpanOfSubringSpan = spanOfSubringSpanThm{family.Add(registry.ProofEntry{
	Name: "SpanOfSubringSpan",
	Key:  "prop_9a660a86dc0a4576",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀R₀:ring_ops(A). ∀X:set(B).",
		Hypotheses: []string{
			"R₀.carrier ⊆ R.carrier",
			"X ⊆ M.carrier",
		},
		Conclusion: "module_span(R, M, module_span(R₀, M, X)) = module_span(R, M, X)",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			R0 *Expr[module_record.RingOps[A]],
			X *Expr[Set[B]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"R₀'s scalars are scalars of R",
				"X lies in M")
			fewer, inM := given[0], given[1]
			R, M := a.TermAs[module_record.RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			span, smaller := a.TermAs[Set[B]]("module_span(R, M, X)"), a.TermAs[Set[B]]("module_span(R₀, M, X)")
			closed := a.Have(
				"the R-span of X is an R-submodule",
				"submodule(R, M, module_span(R, M, X))",
				By(SpanSubmodule.Read(ambient).At(X), inM))
			inner := a.Have(
				"so an R₀-submodule holding X, which holds the R₀-span",
				"module_span(R₀, M, X) ⊆ module_span(R, M, X)",
				By(
					SpanLeast.At(R0, M, X, span),
					Read(SubmoduleRestrictScalars, closed).At(R0),
					fewer,
					SubsetSpan.At(R, M, X)))
			within := a.Have(
				"so what the R₀-span spans lies in the R-span of X",
				"module_span(R, M, module_span(R₀, M, X)) ⊆ module_span(R, M, X)",
				By(SpanLeast.At(R, M, smaller, span), closed, inner))
			holds := a.Have(
				"and holds it, the R₀-span holding X",
				"module_span(R, M, X) ⊆ module_span(R, M, module_span(R₀, M, X))",
				By(SpanMono.At(R, M, X, smaller), SubsetSpan.At(R0, M, X)))
			a.Show(
				"so the two spans are one",
				By(within, holds, set_order.SubsetAntisym))
		}),
})}

// RegularSpanIsIdealSpan — in a commutative ring R, the submodule a subset
// X of R spans in R as a module over itself is the ideal X generates. The
// ideals are the regular submodules (IdealIffRegularSubmodule), so each
// lies in the other by leastness: the ideal X generates is a submodule
// holding X, so it holds the span; the span is an ideal holding X, so it
// holds the ideal X generates.
var RegularSpanIsIdealSpan = regularSpanIsIdealSpanThm{family.Add(registry.ProofEntry{
	Name: "RegularSpanIsIdealSpan",
	Key:  "prop_76d508999c98822b",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀X:set(A).",
		Hypotheses: []string{"comm_ring_on(R)", "X ⊆ R.carrier"},
		Conclusion: "module_span(R, regular_module(R), X) = ideal_span(R, X)",
	},
		func(a *Argument, R *Expr[RingOps[A]], X *Expr[Set[A]], given Fact) {
			V := a.TermAs[ModuleOps[A, A]]("regular_module(R)")
			linear, ideal :=
				a.TermAs[Set[A]]("module_span(R, regular_module(R), X)"), a.TermAs[Set[A]]("ideal_span(R, X)")
			linearInIdeal := a.Have(
				"the ideal X generates is a submodule holding X, so it holds the span",
				"module_span(R, regular_module(R), X) ⊆ ideal_span(R, X)",
				By(
					given,
					ring_ideal.SpanIdeal.At(R, X),
					ring_ideal.SpanContains.At(R, X),
					IdealIffRegularSubmodule.At(R, ideal),
					SpanLeast.At(R, V, X, ideal)))
			idealInLinear := a.Have(
				"the span is an ideal holding X, so it holds the ideal X generates",
				"ideal_span(R, X) ⊆ module_span(R, regular_module(R), X)",
				By(
					given,
					module.RegularModuleOn.At(R),
					SpanSubmodule.At(R, V, X),
					IdealIffRegularSubmodule.At(R, linear),
					SubsetSpan.At(R, V, X),
					ring_ideal.SpanLeast.At(R, X, linear)))
			a.Show(
				"so the two are one set",
				By(linearInIdeal, idealInLinear, set_order.SubsetAntisym.At(linear, ideal)))
		}),
})}

// SpanFamilyCombinations — in a commutative ring R, the ideal finitely many
// elements P(0), …, P(r − 1) generate consists of their combinations
// Σ_{j<r} P(j)·G(j), the coefficients G(j) in R. By induction on r: below 0
// there is no generator, the span of ∅ is the zero ideal and the empty sum
// is zero. One more generator P(r) adds its multiples to the span
// (ring_ideal.SpanInsert), and a combination below suc(r) is its term at r
// plus a combination below r: a member b·P(r) + t, t a combination
// Σ P(j)·Q(j) by induction, is the combination with Q extended by b at r.
var SpanFamilyCombinations = spanFamilyCombinationsThm{family.Add(registry.ProofEntry{
	Name: "SpanFamilyCombinations",
	Key:  "prop_17e1bde26c97db72",
	Reading: "P(j) ∈ R.carrier below r is load-bearing: a generator outside the " +
		"carrier leaves no ideal of R holding the family, and the span is ⋂∅ = 𝕌. " +
		"At r = 0 the family is empty and its span is the zero ideal, the empty sum.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀P:(num → A). ∀r:num. ∀x:A.",
		Hypotheses: []string{
			"∀j:num. j < r ⇒ P(j) ∈ R.carrier",
		},
		Conclusion: "x ∈ ideal_span(R, image(P, {j:num | j < r})) ⇔ " +
			"∃G:(num → A). " +
			"    (∀j:num. j < r ⇒ G(j) ∈ R.carrier) ∧ " +
			"    x = module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * G(j))",
	},
		func(a *Argument, R *Expr[RingOps[A]], ring comm_ring.CommRingFact[on.R], P *Arrow[Nat, A]) {
			regular := module.RegularModuleOn.Read(ring)
			a.Induct("r")
			a.Base(
				"below 0 there is no generator: the span of ∅ is the zero ideal, and the empty sum is zero",
				func(b *Argument) {
					b.FixAs[A]("x")
					b.Assume()
					b.Do(Simp(
						Fwd(num_segment.BelowStrictClauses),
						Fwd(set_image.ImageClauses),
						Fwd(module.ModuleSumEmpty)))
					empty := b.TermAs[Set[A]]("∅")
					within := b.Have(
						"the span of ∅ lies in the zero ideal",
						"ideal_span(R, ∅) ⊆ {R.zero}",
						By(
							ring_ideal.ZeroIdeal.Read(ring),
							ring_ideal.SpanLeast.At(R, empty, b.TermAs[Set[A]]("{R.zero}")),
							set_order.EmptySubset))
					zeroIn := b.Have(
						"and holds zero, being an ideal",
						"R.zero ∈ ideal_span(R, ∅)",
						By(ring_ideal.SpanIdeal.Read(ring).At(empty), set_order.EmptySubset, ring_ideal.IdealZero))
					b.Show(
						"so zero, the empty combination, is its one member",
						BySets(zeroIn, within, nat_order.LessThanZeroClause))
				})
			a.Step(
				"one more generator P(r) adds its multiples to the span, and adds its term at r to a combination",
				func(b *Argument, ih Fact) {
					b.FixAs[A]("x")
					generators := b.Assume()
					r := b.TermAs[Nat]("r")
					below := b.Have(
						"the generators below r lie in R",
						"∀j:num. j < r ⇒ P(j) ∈ R.carrier",
						ByArith(generators))
					last := b.Have(
						"and so does P(r)",
						"P(r) ∈ R.carrier",
						ByArith(generators.At(r)))
					grown := b.Have(
						"the generators below suc(r) are those below r with P(r)",
						"image(P, {j:num | j < suc(r)}) = insert(P(r), image(P, {j:num | j < r}))",
						Simp(Fwd(num_segment.BelowStrictClauses), Fwd(set_image.ImageClauses)),
						Refl())
					multiples := b.Have(
						"so the span grows by the multiples of P(r)",
						"ideal_span(R, insert(P(r), image(P, {j:num | j < r}))) = "+
							"{b * P(r) + t | b:A, t:A | b ∈ R.carrier ∧ t ∈ ideal_span(R, image(P, {j:num | j < r}))}",
						By(ring_ideal.SpanInsert.Read(ring), last, below, set_image.ImageSubsetIff))
					peel := b.Have(
						"a combination below suc(r) is its term at r plus a combination below r",
						Statement{
							Binders: "∀G:(num → A).",
							Hypotheses: []string{
								"∀j:num. j < suc(r) ⇒ G(j) ∈ R.carrier",
							},
							Conclusion: "module_sum(R.add, R.zero, {j:num | j < suc(r)}, λj:num. P(j) * G(j)) = " +
								"G(r) * P(r) + module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * G(j))",
						},
						Derive(func(c *Argument) {
							c.FixAs[Fun[Nat, A]]("G")
							coefficients := c.Assume()
							terms := c.Have(
								"each term below suc(r) lies in R",
								"∀j:num. j < suc(r) ⇒ P(j) * G(j) ∈ R.carrier",
								By(comm_ring.MulIn.Read(ring), coefficients, generators))
							summands := c.TermAs[Fun[Nat, A]]("λj:num. P(j) * G(j)")
							split := c.Have(
								"the sum below suc(r) is the sum below r plus the term at r",
								"module_sum(R.add, R.zero, {j:num | j < suc(r)}, λj:num. P(j) * G(j)) = "+
									"module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * G(j)) + P(r) * G(r)",
								By(terms, module.ModuleSumBelowClauses.Read(regular).At(summands)))
							rest := c.Have(
								"the sum below r lies in R, its terms do",
								"module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * G(j)) ∈ R.carrier",
								By(
									terms,
									nat_order.LessThanSucClause,
									module.ModuleSumIn.Read(regular).At(c.TermAs[Set[Nat]]("{j:num | j < r}"), summands),
									num_segment.FiniteBelowStrict))
							c.Show(
								"and the term at r commutes past it",
								split.Rw(),
								ByArith(ring, rest, last, coefficients.At(r)))
						}))
					b.Do(grown.Rw(), multiples.Rw())
					b.Iff()
					b.Forward(
						"a member b·P(r) + t, t a combination of the generators "+
							"below r by induction, is the combination extended by b at r",
						func(c *Argument, member Fact) {
							_, _, form := c.Unpack2As[A, A](member, "b", "t")
							pieces := c.Conjuncts(
								form,
								"b lies in R",
								"t lies in the span of the generators below r",
								"x is b·P(r) + t")
							_, combination := c.ObtainAs[Fun[Nat, A]](
								"t is a combination Σ_{j<r} P(j)·Q(j), by induction",
								"∃Q:(num → A). "+
									"    (∀j:num. j < r ⇒ Q(j) ∈ R.carrier) ∧ "+
									"    t = module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * Q(j))",
								By(ih.At(c.TermAs[A]("t")), below, pieces[1]))
							qParts := c.Conjuncts(
								combination,
								"Q lies in R below r",
								"t is Σ_{j<r} P(j)·Q(j)")
							extended := c.TermAs[Fun[Nat, A]]("λj:num. COND(j < r, Q(j), b)")
							c.Take(extended)
							coefficients := c.Have(
								"Q extended by b at r lies in R below suc(r)",
								"∀j:num. j < suc(r) ⇒ COND(j < r, Q(j), b) ∈ R.carrier",
								By(qParts[0], pieces[0]))
							agree := c.Have(
								"below r the extended coefficients are Q's",
								"module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * COND(j < r, Q(j), b)) = "+
									"module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * Q(j))",
								By(module.ModuleSumCongruence.At(
									c.TermAs[Op[A]]("R.add"),
									c.TermAs[A]("R.zero"),
									c.TermAs[Set[Nat]]("{j:num | j < r}"),
									c.TermAs[Fun[Nat, A]]("λj:num. P(j) * COND(j < r, Q(j), b)"),
									c.TermAs[Fun[Nat, A]]("λj:num. P(j) * Q(j)"))))
							extendedSum := c.Have(
								"so the extended combination is b·P(r) plus Σ_{j<r} P(j)·Q(j)",
								"module_sum(R.add, R.zero, {j:num | j < suc(r)}, λj:num. P(j) * COND(j < r, Q(j), b)) = "+
									"b * P(r) + module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * Q(j))",
								GroupPremises(coefficients, peel.At(extended)).Rw(),
								agree.Rw(),
								ByArith())
							c.Show(
								"which is x",
								By(coefficients, qParts[1], pieces[2], extendedSum))
						})
					b.Backward(
						"a combination below suc(r) is G(r)·P(r) plus a combination "+
							"below r, which lies in the span below r by induction",
						func(c *Argument, combination Fact) {
							G, form := c.UnpackAs[Fun[Nat, A]](combination, "G")
							parts := c.Conjuncts(
								form,
								"G lies in R below suc(r)",
								"x is Σ_{j<suc(r)} P(j)·G(j)")
							head := c.Have(
								"G(r) lies in R",
								"G(r) ∈ R.carrier",
								ByArith(parts[0].At(r)))
							earlier := c.Have(
								"and so does G below r",
								"∀j:num. j < r ⇒ G(j) ∈ R.carrier",
								ByArith(parts[0]))
							rest := c.Have(
								"the combination below r lies in the span of the generators below r, by induction",
								"module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * G(j)) ∈ "+
									"ideal_span(R, image(P, {j:num | j < r}))",
								By(
									ih.At(c.TermAs[A]("module_sum(R.add, R.zero, {j:num | j < r}, λj:num. P(j) * G(j))")),
									below,
									earlier))
							c.Show(
								"so x is G(r)·P(r) plus a member of that span",
								By(parts[1], rest, head, parts[0], peel.At(G)))
						})
				})
		}),
})}

// finiteSums is the set of the finite sums of terms of S: the
// statement's right side, and the set its proof calls C.
const finiteSums = "{module_sum(M.add, M.zero, {i:num | i " +
	"< n}, F) | n:num, F:(num → B) | ∀i:num. i < n ⇒ F(i) ∈ S}"

// SpanFiniteSums — the span of a set closed under scaling is the set of
// its finite sums: a multiple of a vector of S is already in S, so no
// coefficients are needed. The span is a submodule holding S, so it
// holds every such sum. Conversely the sums form a submodule holding S —
// a sum with a vector of S laid on is a sum with one more term, so a sum
// plus a sum is a sum, the second's terms laid on one at a time — and
// the span, the least such submodule, lies inside them.
var SpanFiniteSums = spanFiniteSumsThm{family.Add(registry.ProofEntry{
	Name: "SpanFiniteSums",
	Key:  "prop_e5e55c4e38e9bcef",
	Reading: "Closure under scaling is load-bearing: without it the finite sums of S are only " +
		"the additive monoid S generates — for S = {u} the multiples u + … + u, not c • u. S ⊆ " +
		"M.carrier keeps the span the meet of a non-empty family; when S ⊄ M.carrier no submodule " +
		"holds S and the span is ⋂∅ = 𝕌. At S = ∅ both sides are {M.zero}: the empty sum at n = 0, " +
		"and the least submodule. Repeated terms are allowed, since the terms are indexed by i < n.",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B).",
		Hypotheses: []string{
			"S ⊆ M.carrier",
			"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ S ⇒ c • u ∈ S",
		},
		Conclusion: "module_span(R, M, S) = «finiteSums»",
		Abbrev: Abbrev{
			{Name: "sumOfTerms", Text: "∃n:num. ∃F:(num → B). " +
				"    (∀i:num. i < n ⇒ F(i) ∈ S) ∧ w = module_sum(M.add, M.zero, {i:num | i < n}, F)"},
			{Name: "finiteSums", Text: "{module_sum(M.add, M.zero, {i:num | i < n}, F) | " +
				"    n:num, " +
				"    F:(num → B) | " +
				"    ∀i:num. i < n ⇒ F(i) ∈ S}"},
		},
	},
		func(a *Argument, moduleOn module.ModuleFact[on.R, on.M], S *Expr[Set[B]], hypotheses Fact) {
			R, M := a.TermAs[RingOps[A]]("R"), a.TermAs[ModuleOps[A, B]]("M")
			given := a.Conjuncts(
				hypotheses,
				"S lies in M",
				"S is closed under scaling")
			sInM, sScaled := given[0], given[1]
			additive := module.AddGroupOn.Read(moduleOn)
			clauses := module.ModuleSumBelowClauses.Read(moduleOn)
			// recursion opens the sums' recursion at a family G of terms.
			recursion := func(b *Argument, G *Expr[Fun[Nat, B]]) []Fact {
				return b.Conjuncts(
					b.Simplified(clauses.At(G)),
					"below 0 the sum is M.zero",
					"below suc(k) it is the sum below k plus the term at k")
			}
			vecAdd, vecZero := a.TermAs[Op[B]]("M.add"), a.TermAs[B]("M.zero")
			carrier := a.TermAs[Set[B]]("M.carrier")
			span := a.TermAs[Set[B]]("module_span(R, M, S)")
			vectorsOfS := a.Unfolded(sInM, set_basic.SubsetDef)

			C, sumsDef := a.LetAs[Set[B]]("C", finiteSums)
			inC := a.Have(
				"w lies in C exactly when it is a sum of terms of S",
				"∀w:B. "+
					"    w ∈ C ⇔ "+
					"    ∃n:num. ∃F:(num → B). "+
					"        (∀i:num. i < n ⇒ F(i) ∈ S) ∧ w = module_sum(M.add, M.zero, {i:num | i < n}, F)",
				sumsDef.Rw(),
				Unfold(set_basic.SetComprehensionDef),
				Unfold(set_basic.ComprehensionSpecDef),
				Unfold(set_basic.SetMemberDef))
			asSum := func(b *Argument, w *Expr[B], inCw Fact) (*Expr[Nat], *Expr[Fun[Nat, B]], Fact, Fact) {
				n, F, sum := b.Obtain2As[Nat, Fun[Nat, B]](
					"w is the sum of some terms F(i) of S below n",
					"«sumOfTerms»",
					By(inC.At(w), inCw))
				parts := b.Conjuncts(
					sum,
					"every F(i) below n lies in S",
					"w is the sum of F below n")
				return n, F, parts[0], parts[1]
			}
			sumIn := a.Have(
				"so every sum of terms of S lies in C",
				Statement{
					Binders: "∀n:num. ∀F:(num → B).",
					Hypotheses: []string{
						"∀i:num. i < n ⇒ F(i) ∈ S",
					},
					Conclusion: "module_sum(M.add, M.zero, {i:num | i < n}, F) ∈ C",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					F := b.FixAs[Fun[Nat, B]]("F")
					terms := b.Assume()
					witnessed := b.Have(
						"n and F witness it",
						"∃m:num. ∃G:(num → B). "+
							"    (∀i:num. i < m ⇒ G(i) ∈ S) ∧ "+
							"    module_sum(M.add, M.zero, {i:num | i < n}, F) = module_sum(M.add, M.zero, {i:num | i < m}, G)",
						Derive(func(d *Argument) {
							d.Take(n)
							d.Take(F)
							d.Show(
								"the sum of F below n is itself",
								By(terms))
						}))
					b.Show(
						"so it lies in C",
						By(witnessed, inC.At(b.TermAs[B]("module_sum(M.add, M.zero, {i:num | i < n}, F)"))))
				}))

			spanSubmodule := a.Have(
				"the span is a submodule of M",
				"submodule(R, M, module_span(R, M, S))",
				By(SpanSubmodule.Read(moduleOn).At(S), sInM))
			inSpan := a.Unfolded(SubsetSpan.At(R, M, S), set_basic.SubsetDef)
			cInSpan := a.Have(
				"C lies in the span: a member of C is a finite sum of vectors of the span, which a submodule holds",
				"C ⊆ module_span(R, M, S)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					w := b.FixAs[B]("w")
					n, F, terms, wIs := asSum(b, w, b.Assume())
					below := b.TermAs[Set[Nat]]("{i:num | i < n}")
					termsInSpan := b.Have(
						"each F(i) lies in the span, as S does",
						"∀i:num. i ∈ {i:num | i < n} ⇒ F(i) ∈ module_span(R, M, S)",
						By(terms, inSpan))
					b.Show(
						"so their sum, w, lies in the span",
						By(
							wIs,
							spanSubmodule,
							num_segment.FiniteBelowStrict.At(n),
							termsInSpan,
							SubmoduleModuleSum.Read(moduleOn).At(span, below, F)))
				}))
			cInM := a.Have(
				"and C lies in M, as the span does",
				"C ⊆ M.carrier",
				By(cInSpan, SubmoduleSubset.Read(spanSubmodule), set_order.SubsetTrans.At(C, span, carrier)))
			vectorsOfC := a.Unfolded(cInM, set_basic.SubsetDef)

			zeros := a.TermAs[Fun[Nat, B]]("λi:num. M.zero")
			zeroIn := a.Have(
				"M.zero lies in C: it is the empty sum, below 0",
				"M.zero ∈ C",
				By(recursion(a, zeros)[0], sumIn.At(a.TermAs[Nat]("0"), zeros), nat_order.LessThanZeroClause))
			extend := a.Have(
				"a member w of C with a vector s of S laid on stays in C: w + s is the sum with s as one more term",
				"∀w s:B. w ∈ C ∧ s ∈ S ⇒ w + s ∈ C",
				Derive(func(b *Argument) {
					w := b.FixAs[B]("w")
					b.FixAs[B]("s")
					assumed := b.Conjuncts(
						b.Assume(),
						"w lies in C",
						"s lies in S")
					n, F, terms, wIs := asSum(b, w, assumed[0])
					below := b.TermAs[Set[Nat]]("{i:num | i < n}")
					H := b.TermAs[Fun[Nat, B]]("λi:num. COND(i < n, F(i), s)")
					extended := b.Have(
						"F with s put at n has every term below suc(n) in S",
						"∀i:num. i < suc(n) ⇒ COND(i < n, F(i), s) ∈ S",
						b.ForEach(func(i *Expr[Nat]) Action { return By(terms.At(i), assumed[1]) }))
					vectors := b.Have(
						"so its terms below suc(n) are vectors",
						"∀i:num. i < suc(n) ⇒ COND(i < n, F(i), s) ∈ M.carrier",
						By(extended, vectorsOfS))
					top := b.Have(
						"its term at n is s",
						"COND(n < n, F(n), s) = s",
						By(nat_order.LessThanIrrefl.At(n)))
					agree := b.Have(
						"and below n it is F",
						"∀i:num. i ∈ {i:num | i < n} ⇒ COND(i < n, F(i), s) = F(i)",
						BySets())
					same := b.Have(
						"so its sum below n is w",
						"module_sum(M.add, M.zero, {i:num | i < n}, λi:num. COND(i < n, F(i), s)) = w",
						By(wIs, agree, module.ModuleSumCongruence.At(vecAdd, vecZero, below, H, F)))
					peeled := b.Have(
						"its sum below suc(n) is its sum below n plus its term at n",
						"module_sum(M.add, M.zero, {i:num | i < suc(n)}, λi:num. COND(i < n, F(i), s)) = "+
							"module_sum(M.add, M.zero, {i:num | i < n}, λi:num. COND(i < n, F(i), s)) + COND(n < n, F(n), s)",
						By(recursion(b, H)[1].At(n), vectors))
					b.Show(
						"so w + s is its sum below suc(n), which lies in C",
						By(peeled, top, same, extended, sumIn.At(b.TermAs[Nat]("suc(n)"), H)))
				}))
			singles := a.Have(
				"each u of S is u laid onto the empty sum",
				"∀u:B. u ∈ S ⇒ u ∈ C",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					uInS := b.Assume()
					uM := b.MemberOf[on.M](u, b.Have(
						"u is a vector",
						"u ∈ M.carrier",
						By(vectorsOfS.At(u), uInS)))
					b.Show(
						"u is M.zero + u, which lies in C",
						By(Normalized, extend.At(vecZero, u), uInS, zeroIn, group.LeftIdentityOn.Read(additive).At(uM)))
				}))
			sInC := a.Have(
				"so S lies in C",
				"S ⊆ C",
				BySets(singles))

			adds := a.Have(
				"a member of C plus a sum of terms of S lies in C: lay the terms on one at a time",
				"∀m:num. ∀G:(num → B). "+
					"    (∀i:num. i < m ⇒ G(i) ∈ S) ⇒ "+
					"    ∀u:B. u ∈ C ⇒ u + module_sum(M.add, M.zero, {i:num | i < m}, G) ∈ C",
				Derive(func(b *Argument) {
					b.Induct("m")
					b.Base(
						"below 0 the sum is the empty one, M.zero, and u + M.zero is u",
						func(d *Argument) {
							G := d.FixAs[Fun[Nat, B]]("G")
							d.Assume()
							u := d.FixAs[B]("u")
							uInC := d.Assume()
							uM := d.MemberOf[on.M](u, d.Have(
								"u is a vector, C lying in M",
								"u ∈ M.carrier",
								By(vectorsOfC.At(u), uInC)))
							d.Show(
								"so u plus the sum below 0 is u, a member of C",
								By(recursion(d, G)[0], group.RightIdentityOn.Read(additive).At(uM), uInC))
						})
					b.Step(
						"below suc(m) the sum is the sum below m plus G(m): the "+
							"hypothesis puts u plus the sum below m in C, and G(m) is laid on",
						func(d *Argument, ih Fact) {
							G := d.FixAs[Fun[Nat, B]]("G")
							terms := d.Assume()
							u := d.FixAs[B]("u")
							uInC := d.Assume()
							m := d.TermAs[Nat]("m")
							below := d.TermAs[Set[Nat]]("{i:num | i < m}")
							gm := d.TermAs[B]("G(m)")
							Σ := d.TermAs[B]("module_sum(M.add, M.zero, {i:num | i < m}, G)")
							earlier := d.Have(
								"the terms below m lie in S",
								"∀i:num. i < m ⇒ G(i) ∈ S",
								d.ForEach(func(i *Expr[Nat]) Action { return ByArith(terms.At(i)) }))
							last := d.Have(
								"and so does G(m)",
								"G(m) ∈ S",
								ByArith(terms.At(m)))
							rest := d.Have(
								"so u plus the sum below m lies in C",
								"u + module_sum(M.add, M.zero, {i:num | i < m}, G) ∈ C",
								By(ih.At(G), earlier, uInC))
							vectors := d.Have(
								"the terms below suc(m) are vectors",
								"∀i:num. i < suc(m) ⇒ G(i) ∈ M.carrier",
								By(terms, vectorsOfS))
							lower := d.Have(
								"among them those below m",
								"∀i:num. i ∈ {i:num | i < m} ⇒ G(i) ∈ M.carrier",
								By(earlier, vectorsOfS))
							uM := d.MemberOf[on.M](u, d.Have(
								"u is a vector, C lying in M",
								"u ∈ M.carrier",
								By(vectorsOfC.At(u), uInC)))
							ΣM := d.MemberOf[on.M](Σ, d.Have(
								"so is the sum below m",
								"module_sum(M.add, M.zero, {i:num | i < m}, G) ∈ M.carrier",
								By(num_segment.FiniteBelowStrict.At(m), lower, module.ModuleSumIn.Read(moduleOn).At(below, G))))
							gmM := d.MemberOf[on.M](gm, d.Have(
								"and so is G(m)",
								"G(m) ∈ M.carrier",
								By(vectorsOfS.At(gm), last)))
							peeled := d.Have(
								"the sum below suc(m) is Σ + G(m), with Σ the sum below m",
								"module_sum(M.add, M.zero, {i:num | i < suc(m)}, G) = "+
									"module_sum(M.add, M.zero, {i:num | i < m}, G) + G(m)",
								By(recursion(d, G)[1].At(m), vectors))
							regroup := d.Have(
								"so u plus the sum below suc(m) is (u + Σ) + G(m), + being associative",
								"u + module_sum(M.add, M.zero, {i:num | i < suc(m)}, G) = "+
									"u + module_sum(M.add, M.zero, {i:num | i < m}, G) + G(m)",
								By(peeled, group.AssocOn.Read(additive).At(uM, ΣM, gmM)))
							d.Show(
								"so it is a member of C with G(m), a vector of S, laid on",
								By(
									regroup,
									extend.At(d.TermAs[B]("u + module_sum(M.add, M.zero, {i:num | i < m}, G)"), gm),
									rest,
									last))
						})
				}))
			sums := a.Have(
				"so C is closed under +",
				"∀u w:B. u ∈ C ∧ w ∈ C ⇒ u + w ∈ C",
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					w := b.FixAs[B]("w")
					assumed := b.Conjuncts(
						b.Assume(),
						"u lies in C",
						"w lies in C")
					n, F, terms, wIs := asSum(b, w, assumed[1])
					b.Show(
						"w is a sum of terms of S, which added to u stays in C",
						By(wIs, adds.At(n, F, u), terms, assumed[0]))
				}))
			scalings := a.Have(
				"C is closed under scaling: c • w is the sum of the scaled terms c • F(i), each in S",
				"∀c:A. ∀w:B. c ∈ R.carrier ∧ w ∈ C ⇒ c • w ∈ C",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					w := b.FixAs[B]("w")
					assumed := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"w lies in C")
					n, F, terms, wIs := asSum(b, w, assumed[1])
					below := b.TermAs[Set[Nat]]("{i:num | i < n}")
					vectors := b.Have(
						"the terms are vectors",
						"∀i:num. i ∈ {i:num | i < n} ⇒ F(i) ∈ M.carrier",
						By(terms, vectorsOfS))
					scaled := b.Have(
						"c • w is the sum of the c • F(i)",
						"c • w = module_sum(M.add, M.zero, {i:num | i < n}, λi:num. c • F(i))",
						By(
							wIs,
							num_segment.FiniteBelowStrict.At(n),
							vectors,
							module.ModuleSumSmul.Read(moduleOn).At(below, b.MemberOf[on.R](c, assumed[0]), F)))
					stays := b.Have(
						"each c • F(i) lies in S, which scaling keeps",
						"∀i:num. i < n ⇒ c • F(i) ∈ S",
						By(terms, sScaled, assumed[0]))
					b.Show(
						"so c • w lies in C",
						By(scaled, stays, sumIn.At(n, b.TermAs[Fun[Nat, B]]("λi:num. c • F(i)"))))
				}))

			isSubmodule := a.Have(
				"C is a submodule of M: it lies in M, holds M.zero, and is closed under + and scaling",
				"submodule(R, M, C)",
				By(cInM, zeroIn, sums, scalings, SubmoduleCriterion.Read(moduleOn).At(C)))
			spanInC := a.Have(
				"so the span, the least submodule holding S, lies in C",
				"module_span(R, M, S) ⊆ C",
				By(isSubmodule, sInC, SpanLeast.At(R, M, S, C)))
			a.Show(
				"C lies in the span as well, so the two are one set",
				By(spanInC, cInSpan, set_order.SubsetAntisym.At(span, C)))
		}),
})}

// ---------------------------------------------------------------------------
// The quotient module
// ---------------------------------------------------------------------------

// QuotientSmulDef — `quotient_smul(add, smul, N, c, s)`: a coset of N
// under the addition add, scaled by c under smul, without choosing a
// representative: the scaled coset plus N. For s = u + N this is
// c • u + c • N + N = c • u + N.
var QuotientSmulDef = quotientSmulDefThm{family.Define(registry.DefEntry{
	Name:  "QuotientSmulDef",
	Key:   "prop_b0f7990b730eb617",
	Const: "quotient_smul",
	Type:  "(B → B → B) → (A → B → B) → set(B) → A → set(B) → set(B)",
	Equations: []string{
		"∀add:(B → B → B). ∀smul:(A → B → B). ∀N:set(B). ∀c:A. ∀s:set(B). " +
			"    quotient_smul(add, smul, N, c, s) = set_mul(add, image(smul(c), s), N)",
	},
})}

// SubmoduleCosetEq — two vectors have one coset of a submodule exactly
// when their difference lies in it: a submodule is a subgroup of the
// additive group, whose cosets of y and x agree exactly when -y + x lies
// in it, and addition commutes.
var SubmoduleCosetEq = submoduleCosetEqThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleCosetEq",
	Key:  "prop_2b6421be469c09e2",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀S:set(B). ∀x y:B.",
		Hypotheses: []string{
			"submodule(R, M, S)",
			"x ∈ M.carrier",
			"y ∈ M.carrier",
		},
		Conclusion: "left_coset(M.add, x, S) = left_coset(M.add, y, S) ⇔ x + -y ∈ S",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			S *Expr[Set[B]],
			x, y *Member[B, on.M],
			sub Fact,
		) {
			additive := module.AddGroupOn.Read(ambient)
			commute := a.Have(
				"addition commutes, so the difference is -y + x",
				"x + -y = -y + x",
				By(module.AddComm.Read(ambient).At(x, group.InvIn.Read(additive).At(y))))
			a.Show(
				"the cosets of y and x agree exactly when -y + x lies in S",
				commute.Rw(),
				By(SubmoduleSubgroup.Read(sub), group.LeftCosetEqOn.Read(additive).At(y, x, S)))
		}),
})}

// QuotientSmulCoset — scaling the coset of a vector u by a scalar c,
// without choosing a representative, gives the coset of c • u.
var QuotientSmulCoset = quotientSmulCosetThm{family.Add(registry.ProofEntry{
	Name: "QuotientSmulCoset",
	Key:  "prop_12a8b38c8f851921",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N:set(B). ∀c:A. ∀u:B.",
		Hypotheses: []string{
			"submodule(R, M, N)",
			"c ∈ R.carrier",
			"u ∈ M.carrier",
		},
		Conclusion: "quotient_smul(M.add, M.smul, N, c, left_coset(M.add, u, N)) = " +
			"left_coset(M.add, c • u, N)",
	},
		func(
			a *Argument,
			ambient module.ModuleFact[on.R, on.M],
			N *Expr[Set[B]],
			c *Expr[A],
			u *Expr[B],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"N is a submodule of M",
				"c is a scalar",
				"u is a vector")
			sub, scalar, vector := parts[0], parts[1], parts[2]
			cR, uM := a.MemberOf[on.R](c, scalar), a.MemberOf[on.M](u, vector)
			additive := module.AddGroupOn.Read(ambient)
			cu := module.SmulIn.Read(ambient).At(cR, uM)
			within := a.Have(
				"N lies in M's carrier",
				"N ⊆ M.carrier",
				By(SubmoduleSubset.Read(sub)))
			inclusion := a.Unfolded(within, set_basic.SubsetDef)
			pointwise := a.Have(
				"the scaled coset plus N and the coset of c • u have the same points",
				"∀z:B. "+
					"    z ∈ quotient_smul(M.add, M.smul, N, c, left_coset(M.add, u, N)) ⇔ "+
					"    z ∈ left_coset(M.add, c • u, N)",
				Derive(func(b *Argument) {
					b.FixAs[B]("z")
					b.Iff()
					b.Forward(
						"a point of the scaled coset plus N is c • (u + n) + "+
							"n', which is c • u + (c • n + n') with c • n + n' in N",
						func(d *Argument, member Fact) {
							n, nPrime, point := d.Obtain2As[B, B](
								"z is c • (u + n) + n' for some n and n' in N",
								"∃n n':B. n ∈ N ∧ n' ∈ N ∧ z = c • (u + n) + n'",
								member.Simp(
									Fwd(QuotientSmulDef),
									Fwd(quotient_group.InSetMul),
									Fwd(set_basic.InImage),
									Fwd(group.LeftCosetDef)),
								By(member))
							pieces := d.Conjuncts(
								point,
								"n lies in N",
								"so does n'",
								"z is c • (u + n) + n'")
							nM := d.MemberOf[on.M](n, d.Have(
								"n is a vector, N lying in M's carrier",
								"n ∈ M.carrier",
								By(inclusion, pieces[0])))
							nPrimeM := d.MemberOf[on.M](nPrime, d.Have(
								"and so is n'",
								"n' ∈ M.carrier",
								By(inclusion, pieces[1])))
							cn := module.SmulIn.Read(ambient).At(cR, nM)
							inN := d.Have(
								"c • n + n' lies in N, a submodule being closed under scaling and sums",
								"c • n + n' ∈ N",
								By(SubmoduleAdd.Read(sub), SubmoduleSmul.Read(sub), scalar, pieces[0], pieces[1]))
							regroup := d.Have(
								"z regroups as c • u + (c • n + n')",
								"z = c • u + (c • n + n')",
								CalcEq(
									Leg(
										d.TermAs[B]("c • u + c • n + n'"),
										"c distributes over u + n",
										By(pieces[2], module.SmulAddLeft.Read(ambient).At(cR, uM, nM))),
									FinalLeg(
										"and the sum regroups",
										By(group.AssocOn.Read(additive).At(cu, cn, nPrimeM))),
								))
							d.Do(Simp(Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)))
							d.Take(d.TermAs[B]("c • n + n'"))
							d.Show(
								"so z is c • u plus a point of N",
								By(regroup, inN))
						})
					b.Backward(
						"a point c • u + n of the coset of c • u is c • u, the image of u in its own coset, plus n",
						func(d *Argument, member Fact) {
							n, point := d.UnpackAs[B](d.Simplified(
								member,
								Fwd(group.LeftCosetDef),
								Fwd(set_basic.InImage)), "n")
							own := d.Have(
								"u lies in its own coset",
								"u ∈ left_coset(M.add, u, N)",
								By(group.InOwnLeftCosetOn.Read(additive).At(uM, N), SubmoduleSubgroup.Read(sub)))
							scaling := d.TermAs[Fun[B, B]]("M.smul(c)")
							coset := d.TermAs[Set[B]]("left_coset(M.add, u, N)")
							scaled := d.Have(
								"so c • u lies in the scaled coset",
								"c • u ∈ image(M.smul(c), left_coset(M.add, u, N))",
								By(set_image.FunInImage.At(scaling, coset, u), own))
							d.Do(Simp(Fwd(QuotientSmulDef), Fwd(quotient_group.InSetMul)))
							d.Take(cu)
							d.Take(n)
							d.Show(
								"z is c • u, a point of the scaled coset, plus n, a point of N",
								By(scaled, point))
						})
				}))
			a.Show(
				"two sets with the same points are equal",
				By(pointwise, set_basic.Extension))
		}),
})}

// SubmoduleNormal — a submodule is a normal subgroup of the vectors under
// the addition: it is a subgroup, and since the sum commutes on M's
// carrier the conjugate (g + x) + -g of a vector x of N is (x + g) + -g,
// which is x again.
var SubmoduleNormal = submoduleNormalThm{family.Add(registry.ProofEntry{
	Name: "SubmoduleNormal",
	Key:  "prop_3d4b0b4b13688f6f",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
		},
		Conclusion: "normal_subgroup(module_additive_group(M), N)",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], N *Expr[Set[B]], sub Fact) {
			additive := module.AddGroupOn.Read(ambient)
			subgroup := a.Have(
				"N is a subgroup of the vectors under the addition",
				"subgroup(module_additive_group(M), N)",
				By(SubmoduleSubgroup.Read(sub)))
			inN := a.Unfolded(SubmoduleSubset.Read(sub).AsFact(), set_basic.SubsetDef)
			conjugates := a.Have(
				"N holds the conjugate of each of its vectors by any vector",
				"∀g x:B. g ∈ M.carrier ∧ x ∈ N ⇒ g + x + -g ∈ N",
				Derive(func(b *Argument) {
					g := b.FixAs[B]("g")
					x := b.FixAs[B]("x")
					given := b.Conjuncts(
						b.Assume(),
						"g is a vector",
						"x lies in N")
					inCarrier := b.Have(
						"x is a vector too, since N lies in M's carrier",
						"x ∈ M.carrier",
						By(inN, given[1]))
					gM, xM := b.MemberOf[on.M](g, given[0]), b.MemberOf[on.M](x, inCarrier)
					conjugate := b.Have(
						"the conjugate of x by g is x",
						"g + x + -g = x",
						CalcEq(
							Leg(
								b.TermAs[B]("x + g + -g"),
								"g and x commute",
								By(Normalized, module.AddComm.Read(ambient).At(gM, xM))),
							FinalLeg(
								"and -g undoes g",
								By(group.MulInvCancelRightOn.Read(additive).At(gM, xM))),
						))
					b.Show(
						"so the conjugate is x, a vector of N",
						conjugate.Rw(),
						By(given[1]))
				}))
			a.Show(
				"a subgroup holding every conjugate of its vectors is normal",
				By(subgroup, conjugates, group.NormalSubgroupDef))
		}),
})}

// QuotientModuleDef — `quotient_module(M, K)`: the cosets of K in M's
// carrier, added as sets, with K as the zero, the coset inverse, and
// scaled by quotient_smul.
var QuotientModuleDef = quotientModuleDefThm{family.Define(registry.DefEntry{
	Name: "QuotientModuleDef", Const: "quotient_module",
	Key:  "prop_617cf09dbba35523",
	Type: "module_ops(A, B) → set(B) → module_ops(A, set(B))",
	Equations: []string{
		"∀M:module_ops(A, B). ∀K:set(B). " +
			"    quotient_module(M, K) = " +
			"    mk_module(set_mul(M.add), " +
			"        K, " +
			"        set_inv(M.neg), " +
			"        quotient_smul(M.add, M.smul, K), " +
			"        left_cosets(M.add, M.carrier, K))",
	},
	Deps: []registry.EntryLike{QuotientSmulDef},
})}

// QuotientModuleOn — the cosets of a submodule form a module. N is a
// normal subgroup of the vectors, so the cosets are the quotient group
// under the coset sum. Every coset is u + N for a point u of M, the sum
// of two cosets is the coset of the sum and a scaled coset is the coset
// of the scaled point, so each remaining condition is M's own law read
// at representatives.
var QuotientModuleOn = quotientModuleOnThm{family.Add(registry.ProofEntry{
	Name: "QuotientModuleOn",
	Key:  "prop_ace62e7fff1534ac",
	Build: module.ModuleOn.Law(Statement{
		Binders: "∀N:set(B).",
		Hypotheses: []string{
			"submodule(R, M, N)",
		},
		Conclusion: "module_on(R, quotient_module(M, N))",
	},
		func(a *Argument, ambient module.ModuleFact[on.R, on.M], N *Expr[Set[B]], sub Fact) {
			ring := module.RingOn.Read(ambient)
			additive := module.AddGroupOn.Read(ambient)
			normal := a.Have(
				"N is a normal subgroup of the vectors",
				"normal_subgroup(module_additive_group(M), N)",
				By(sub, SubmoduleNormal.Read(ambient)))
			// The two coset laws at N, cited by the cases.
			sumLaw := a.Have(
				"the sum of two cosets is the coset of the sum",
				Statement{
					Binders: "∀u v:B.",
					Hypotheses: []string{
						"u ∈ M.carrier",
						"v ∈ M.carrier",
					},
					Conclusion: "set_mul(M.add, left_coset(M.add, u, N), left_coset(M.add, v, N)) = " +
						"left_coset(M.add, u + v, N)",
				},
				By(normal, quotient_group.LeftCosetMulOn.Read(additive)))
			scaleLaw := a.Have(
				"a scaled coset is the coset of the scaled point",
				Statement{
					Binders: "∀c:A. ∀u:B.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ M.carrier",
					},
					Conclusion: "quotient_smul(M.add, M.smul, N, c, left_coset(M.add, u, N)) = " +
						"left_coset(M.add, c • u, N)",
				},
				By(sub, QuotientSmulCoset.Read(ambient)))
			// The conditions of module_on at the cosets are proved here,
			// before the unfolding below: it also opens the resident
			// module_on(R, M), so its handles die. Each is read from
			// representatives: N lies in M's carrier, so the cosets are the
			// image of the carrier under the coset map. A condition with a
			// scalar guard is stated curried, the scalar first, so that its
			// cosets are read the same way.
			a.Have(
				"N lies in M's carrier",
				"N ⊆ M.carrier",
				By(SubmoduleSubset.Read(sub)))
			scalars := a.Have(
				"the scalars are M's ring",
				"comm_ring_on(R)",
				By(ring))
			cosetGroup := a.Have(
				"the quotient's additive group is the coset sum on the cosets",
				"module_additive_group(quotient_module(M, N)) = quotient_group(module_additive_group(M), N)",
				Simp(
					Fwd(module_record.ModuleAdditiveGroupDef),
					Fwd(QuotientModuleDef),
					Fwd(quotient_group.QuotientGroupDef)),
				Refl())
			cosetsGroup := a.Have(
				"the cosets are the quotient group under the coset sum",
				"group_on(module_additive_group(quotient_module(M, N)))",
				cosetGroup.Rw(),
				By(normal, quotient_group.QuotientGroupOn.Read(additive)))
			commutes := a.Have(
				"the coset sum commutes, because the vector sum does",
				Statement{
					Binders: "∀s t:set(B).",
					Hypotheses: []string{
						"s ∈ left_cosets(M.add, M.carrier, N)",
						"t ∈ left_cosets(M.add, M.carrier, N)",
					},
					Conclusion: "set_mul(M.add, s, t) = set_mul(M.add, t, s)",
				},
				Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(additive))),
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					v := b.FixAs[B]("v")
					members := b.Conjuncts(
						b.Assume(),
						"u lies in M",
						"v lies in M")
					uM, vM := b.MemberOf[on.M](u, members[0]), b.MemberOf[on.M](v, members[1])
					b.Show(
						"(u + N) + (v + N) and (v + N) + (u + N) are the "+
							"cosets of u + v and of v + u, which are one vector",
						By(Normalized, sumLaw.At(u, v), sumLaw.At(v, u), module.AddComm.Read(ambient).At(uM, vM)))
				}))
			scaled := a.Have(
				"a scalar c scales every coset to a coset: the coset of the scaled representative",
				"∀c:A. "+
					"    c ∈ R.carrier ⇒ "+
					"    ∀s:set(B). "+
					"        s ∈ left_cosets(M.add, M.carrier, N) ⇒ "+
					"        quotient_smul(M.add, M.smul, N, c, s) ∈ left_cosets(M.add, M.carrier, N)",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cR := b.MemberOf[on.R](c, b.Assume())
					b.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))))
					u := b.FixAs[B]("u")
					uM := b.MemberOf[on.M](u, b.Assume())
					cu := module.SmulIn.Read(ambient).At(cR, uM)
					b.Do(Simp(Fwd(quotient_group.InLeftCosets.Read(additive))))
					b.Take(cu)
					b.Show(
						"c(u + N) is the coset of c • u, a point of M",
						By(scaleLaw.At(c, u), cu))
				}))
			distributes := a.Have(
				"a scalar c distributes over the coset sum, because it does over the vector sum",
				"∀c:A. "+
					"    c ∈ R.carrier ⇒ "+
					"    ∀s t:set(B). "+
					"        s ∈ left_cosets(M.add, M.carrier, N) ∧ t ∈ left_cosets(M.add, M.carrier, N) ⇒ "+
					"        quotient_smul(M.add, M.smul, N, c, set_mul(M.add, s, t)) = "+
					"        set_mul(M.add, "+
					"            quotient_smul(M.add, M.smul, N, c, s), "+
					"            quotient_smul(M.add, M.smul, N, c, t))",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cR := b.MemberOf[on.R](c, b.Assume())
					b.Do(Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(additive))))
					u := b.FixAs[B]("u")
					v := b.FixAs[B]("v")
					members := b.Conjuncts(
						b.Assume(),
						"u lies in M",
						"v lies in M")
					uM, vM := b.MemberOf[on.M](u, members[0]), b.MemberOf[on.M](v, members[1])
					uv := group.MulIn.Read(additive).At(uM, vM)
					cu, cv := module.SmulIn.Read(ambient).At(cR, uM), module.SmulIn.Read(ambient).At(cR, vM)
					b.Show(
						"c((u + N) + (v + N)) is the coset of c • (u + v) "+
							"= c • u + c • v, the sum of c(u + N) and c(v + N)",
						By(
							sumLaw.At(u, v),
							scaleLaw.At(c, uv),
							module.SmulAddLeft.Read(ambient).At(cR, uM, vM),
							sumLaw.At(cu, cv),
							scaleLaw.At(c, u),
							scaleLaw.At(c, v),
							uv,
							cu,
							cv))
				}))
			sums := a.Have(
				"a sum of scalars c + d distributes over every coset, because it does over a vector",
				"∀c d:A. "+
					"    c ∈ R.carrier ∧ d ∈ R.carrier ⇒ "+
					"    ∀s:set(B). "+
					"        s ∈ left_cosets(M.add, M.carrier, N) ⇒ "+
					"        quotient_smul(M.add, M.smul, N, c + d, s) = "+
					"        set_mul(M.add, "+
					"            quotient_smul(M.add, M.smul, N, c, s), "+
					"            quotient_smul(M.add, M.smul, N, d, s))",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					d := b.FixAs[A]("d")
					scalars := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"d is a scalar")
					cR, dR := b.MemberOf[on.R](c, scalars[0]), b.MemberOf[on.R](d, scalars[1])
					b.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))))
					u := b.FixAs[B]("u")
					uM := b.MemberOf[on.M](u, b.Assume())
					sum := comm_ring.AddIn.Read(ring).At(cR, dR)
					cu, du := module.SmulIn.Read(ambient).At(cR, uM), module.SmulIn.Read(ambient).At(dR, uM)
					b.Show(
						"(c + d)(u + N) is the coset of (c + d) • u = c • u + d • u, the sum of c(u + N) and d(u + N)",
						By(
							scaleLaw.At(sum, u),
							module.SmulAddRight.Read(ambient).At(cR, dR, uM),
							sumLaw.At(cu, du),
							scaleLaw.At(c, u),
							scaleLaw.At(d, u),
							sum,
							cu,
							du))
				}))
			products := a.Have(
				"a product of scalars c * d scales every coset as d and then c do, because it does a vector",
				"∀c d:A. "+
					"    c ∈ R.carrier ∧ d ∈ R.carrier ⇒ "+
					"    ∀s:set(B). "+
					"        s ∈ left_cosets(M.add, M.carrier, N) ⇒ "+
					"        quotient_smul(M.add, M.smul, N, c * d, s) = "+
					"        quotient_smul(M.add, M.smul, N, c, quotient_smul(M.add, M.smul, N, d, s))",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					d := b.FixAs[A]("d")
					scalars := b.Conjuncts(
						b.Assume(),
						"c is a scalar",
						"d is a scalar")
					cR, dR := b.MemberOf[on.R](c, scalars[0]), b.MemberOf[on.R](d, scalars[1])
					b.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))))
					u := b.FixAs[B]("u")
					uM := b.MemberOf[on.M](u, b.Assume())
					product := comm_ring.MulIn.Read(ring).At(cR, dR)
					du := module.SmulIn.Read(ambient).At(dR, uM)
					b.Show(
						"(c * d)(u + N) is the coset of (c * d) • u = c • (d • u), which is c(d(u + N))",
						By(
							Normalized,
							scaleLaw.At(product, u),
							module.SmulMul.Read(ambient).At(cR, dR, uM),
							scaleLaw.At(c, du),
							scaleLaw.At(d, u),
							product,
							du))
				}))
			one := a.Have(
				"the ring's one fixes every coset, because it fixes every vector",
				"∀s:set(B). s ∈ left_cosets(M.add, M.carrier, N) ⇒ quotient_smul(M.add, M.smul, N, R.one, s) = s",
				Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))),
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					uM := b.MemberOf[on.M](u, b.Assume())
					b.Show(
						"one scales u + N to the coset of R.one • u, which is u + N",
						By(
							scaleLaw.At(b.TermAs[A]("R.one"), u),
							module.SmulOne.Read(ambient).At(uM),
							comm_ring.OneIn.Read(ring)))
				}))
			a.Show(
				"unfolded, module_on at the cosets is the facts above, the curried ones with their guards joined",
				Unfold(module.ModuleOn),
				By(scalars, cosetsGroup, commutes, scaled, distributes, sums, products, one))
		}),
})}

// ---------------------------------------------------------------------------
// The annihilator of a vector of a simple module
// ---------------------------------------------------------------------------

// AnnihilatorOfSimpleMaximal — in a module whose only submodules are
// {M.zero} and M itself, the scalars killing a nonzero vector form a
// maximal ideal: an ideal containing the annihilator has multiples of the
// vector either zero, making it the annihilator, or all of M, forcing it to hold one.
var AnnihilatorOfSimpleMaximal = annihilatorOfSimpleMaximalThm{family.Add(registry.ProofEntry{
	Name: "AnnihilatorOfSimpleMaximal",
	Key:  "prop_2ecbf912d21b9e05",
	Reading: "a ≠ M.zero is load-bearing: the annihilator of M.zero is all of R.carrier, " +
		"which holds R.one. The simplicity is spelled as its one use: every submodule is {M.zero} " +
		"or M.carrier; that M.carrier is not {M.zero} is a's own witness. Over the zero ring a = " +
		"R.one • a = R.zero • a = M.zero, so no a qualifies and the theorem is vacuous there.",
	Build: family.Sections(module.ModuleOn.Statement(Statement{
		Binders: "∀a:B.",
		Hypotheses: []string{
			"a ∈ M.carrier",
			"¬(a = M.zero)",
			"∀N:set(B). submodule(R, M, N) ⇒ N = {M.zero} ∨ N = M.carrier",
		},
		Conclusion: "maximal_ideal(R, {r:A | r ∈ R.carrier ∧ r • a = M.zero})",
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			annihilatorIdeal := ctx.Lemma(module.ModuleOn.Statement(Statement{
				Binders: "∀a:B.",
				Hypotheses: []string{
					"a ∈ M.carrier",
				},
				Conclusion: "ring_ideal(R, {r:A | r ∈ R.carrier ∧ r • a = M.zero})",
			}),
				func(
					arg *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					ambient module.ModuleFact[on.R, on.M],
					a *Member[B, on.M],
				) {
					ring := module.RingOn.Read(ambient)
					additive := module.AddGroupOn.Read(ambient)
					zero := arg.TermAs[B]("M.zero")
					arg.Show(
						"the scalars killing a satisfy the ideal conditions",
						Unfold(ring_ideal.RingIdealDef),
						SplitConjAll(
							Case(
								"the annihilator lies in the scalar carrier",
								BySets()),
							Case(
								"the zero scalar kills a",
								By(a, comm_ring.ZeroIn.Read(ring), module.ZeroSmul.Read(ambient))),
							Case(
								"a sum of two scalars killing a also kills a",
								Derive(func(b *Argument) {
									x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
									killed := b.Assume()
									b.Show(
										"distributing the sum gives zero plus zero",
										BySets(
											a,
											killed,
											comm_ring.AddIn.Read(ring).AsFact().At(x, y),
											module.SmulAddRight.Read(ambient).AsFact().At(x, y, a),
											group.LeftIdentityOn.Read(additive).AsFact().At(zero),
											group.OneIn.Read(additive)))
								})),
							Case(
								"a scalar multiple of a scalar killing a also kills a",
								Derive(func(b *Argument) {
									r, x := b.FixAs[A]("r"), b.FixAs[A]("x")
									killed := b.Assume()
									b.Show(
										"successive scaling gives a scalar multiple of zero",
										BySets(
											a,
											killed,
											comm_ring.MulIn.Read(ring).AsFact().At(r, x),
											module.SmulMul.Read(ambient).AsFact().At(r, x, a),
											module.SmulZero.Read(ambient).AsFact().At(r)))
								}))))
				})

			idealImage := ctx.Lemma(module.ModuleOn.Statement(Statement{
				Binders: "∀a:B. ∀J:set(A).",
				Hypotheses: []string{
					"a ∈ M.carrier",
					"ring_ideal(R, J)",
				},
				Conclusion: "submodule(R, M, {s • a | s:A | s ∈ J})",
			}),
				func(
					arg *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					ambient module.ModuleFact[on.R, on.M],
					a *Member[B, on.M],
					J *Expr[Set[A]],
					ideal Fact,
				) {
					within := arg.Have(
						"the ideal's multiples of a are vectors",
						"{s • a | s:A | s ∈ J} ⊆ M.carrier",
						BySets(a, ring_ideal.IdealSubset.Read(ideal), module.SmulIn.Read(ambient)))
					zero := arg.Have(
						"the zero scalar supplies the zero vector",
						"M.zero ∈ {s • a | s:A | s ∈ J}",
						BySets(a, ring_ideal.IdealZero.Read(ideal), module.ZeroSmul.Read(ambient).At(a)))
					sums := arg.Have(
						"adding ideal coefficients adds their multiples of a",
						"∀u v:B. u ∈ {s • a | s:A | s ∈ J} ∧ v ∈ {s • a | s:A | s ∈ J} ⇒ u + v ∈ {s • a | s:A | s ∈ J}",
						Derive(func(b *Argument) {
							b.FixAs[B]("u")
							b.FixAs[B]("v")
							given := b.Assume()
							s, t, coefficients := b.Obtain2As[A, A](
								"choose ideal coefficients for the two vectors",
								"∃s t:A. s ∈ J ∧ t ∈ J ∧ u = s • a ∧ v = t • a",
								Named("s", "t"),
								BySets(given))
							inR := b.Have(
								"both coefficients are scalars",
								"s ∈ R.carrier ∧ t ∈ R.carrier",
								BySets(coefficients, ring_ideal.IdealSubset.Read(ideal)))
							scalars := b.Conjuncts(
								inR,
								"s is a scalar",
								"t is a scalar")
							sm, tm := b.MemberOf[on.R](s, scalars[0]), b.MemberOf[on.R](t, scalars[1])
							// A regrouping is a module identity, which the chase normalizer closes.
							expansion := b.Have(
								"their sum is represented by s + t",
								"(s + t) • a = u + v",
								ByChase(Depth(0), ambient, a, sm, tm, coefficients))
							sumIn := b.Have(
								"s + t remains in the ideal",
								"s + t ∈ J",
								By(coefficients, ring_ideal.IdealAdd.Read(ideal).AsFact().At(s, t)))
							b.Show(
								"the sum has an ideal coefficient",
								BySets(expansion, sumIn))
						}))
					scaled := arg.Have(
						"multiplying an ideal coefficient scales its multiple of a",
						"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ {s • a | s:A | s ∈ J} ⇒ c • u ∈ {s • a | s:A | s ∈ J}",
						Derive(func(b *Argument) {
							c := b.FixAs[A]("c")
							b.FixAs[B]("u")
							given := b.Assume()
							s, coefficient := b.ObtainAs[A](
								"choose an ideal coefficient for u",
								"∃s:A. s ∈ J ∧ u = s • a",
								Named("s"),
								BySets(given))
							inR := b.Have(
								"the coefficient is a scalar",
								"s ∈ R.carrier",
								BySets(coefficient, ring_ideal.IdealSubset.Read(ideal)))
							sm := b.MemberOf[on.R](s, inR)
							expansion := b.Have(
								"the scaled vector is represented by c * s",
								"(c * s) • a = c • u",
								ByChase(Depth(0), ambient, a, sm, given, coefficient))
							productIn := b.Have(
								"c * s remains in the ideal",
								"c * s ∈ J",
								By(given, coefficient, ring_ideal.IdealMul.Read(ideal).AsFact().At(c, s)))
							b.Show(
								"the scaled vector has an ideal coefficient",
								BySets(expansion, productIn))
						}))
					arg.Show(
						"zero, addition and scaling make these multiples a submodule",
						By(within, zero, sums, scaled, SubmoduleCriterion.Read(ambient)))
				})

			return ctx.Theorem(headline,
				func(
					arg *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					ambient module.ModuleFact[on.R, on.M],
					a *Expr[B],
					given Fact,
				) {
					parts := arg.Conjuncts(
						given,
						"a is a vector",
						"a is nonzero",
						"every submodule is zero or the whole carrier")
					am := arg.MemberOf[on.M](a, parts[0])
					nonzero, simple := parts[1], parts[2]
					ring := module.RingOn.Read(ambient)
					annihilator := arg.Let("K", arg.TermAs[Set[A]]("{r:A | r ∈ R.carrier ∧ r • a = M.zero}"))
					isIdeal := arg.Have(
						"K is an ideal",
						"ring_ideal(R, K)",
						annihilator.Rw(),
						By(ambient, am, At(annihilatorIdeal, R, M, a)))
					proper := arg.Have(
						"one cannot kill the nonzero vector a",
						"R.one ∉ K",
						BySets(annihilator, nonzero, am, module.SmulOne.Read(ambient)))
					maximality := arg.Have(
						"every ideal above K is K or holds one",
						"∀J:set(A). ring_ideal(R, J) ∧ K ⊆ J ⇒ J = K ∨ R.one ∈ J",
						Derive(func(b *Argument) {
							J := b.FixAs[Set[A]]("J")
							above := b.Conjuncts(
								b.Assume(),
								"J is an ideal",
								"J contains K")
							jIdeal, jAbove := above[0], above[1]
							image := b.Let("N", b.TermAs[Set[B]]("{s • a | s:A | s ∈ J}"))
							isSubmodule := b.Have(
								"the ideal's multiples of a form a submodule",
								"submodule(R, M, N)",
								image.Rw(),
								By(ambient, am, jIdeal, At(idealImage, R, M, a, J)))
							classification := b.Have(
								"simplicity classifies this image",
								"N = {M.zero} ∨ N = M.carrier",
								By(isSubmodule, simple.At(b.TermAs[Set[B]]("N"))))
							b.Do(classification.SplitDisj(
								LeftHolds(
									"a zero image means every coefficient in J kills a",
									Given(func(c *Argument, zeroImage Fact) {
										c.Show(
											"J is exactly K",
											Left(),
											BySets(annihilator, image, zeroImage, jAbove, ring_ideal.IdealSubset.Read(jIdeal)))
									})),
								RightHolds(
									"a full image provides an ideal coefficient fixing a",
									Given(func(c *Argument, fullImage Fact) {
										s, coefficient := c.ObtainAs[A](
											"write a as an ideal multiple of itself",
											"∃s:A. s ∈ J ∧ a = s • a",
											Named("s"),
											BySets(fullImage, image, am))
										inR := c.Have(
											"s is a scalar",
											"s ∈ R.carrier",
											BySets(coefficient, ring_ideal.IdealSubset.Read(jIdeal)))
										sm := c.MemberOf[on.R](s, inR)
										killed := c.Have(
											"one minus s kills a",
											"(R.one - s) • a = M.zero",
											ByChase(Depth(0), ambient, am, sm, coefficient))
										differenceIn := c.Have(
											"one minus s is a scalar",
											"R.one - s ∈ R.carrier",
											By(sm, comm_ring.SubIn.Read(ring), comm_ring.OneIn.Read(ring)))
										inK := c.Have(
											"one minus s belongs to K",
											"R.one - s ∈ K",
											BySets(annihilator, killed, differenceIn))
										inJ := c.Have(
											"J contains one minus s",
											"R.one - s ∈ J",
											BySets(inK, jAbove))
										reconstruct := c.Have(
											"the two ideal coefficients add to one",
											"(R.one - s) + s = R.one",
											ByArith(ring, sm))
										oneIn := c.Have(
											"their sum lies in J",
											"(R.one - s) + s ∈ J",
											By(inJ, coefficient, ring_ideal.IdealAdd.Read(jIdeal)))
										c.Show(
											"J holds one",
											Right(),
											By(reconstruct, oneIn))
									}))))
						}))
					arg.Show(
						"the proper annihilator ideal is maximal",
						By(isIdeal, proper, maximality, ring_ideal.MaximalIdealDef))
				})
		}),
})}
