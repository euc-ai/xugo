// cohomology.go — the two-term Čech complex of a lattice pair: H⁰ the
// kernel of the Čech difference and H¹ its cokernel; the chart sum and the
// ambient of a sub-pair; the cohomology modules over any subring of both
// charts; and the cohomology of a direct sum, chart quotients that keep
// their dimension on the overlap, and a pair inside a subset read in the
// ring's regular module.

package lattice_pair

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
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The two-term Čech complex
// ---------------------------------------------------------------------------

// H0IsIntersection — the kernel of the Čech difference on M₀ × M₁ is the
// diagonal of H⁰(M): the pairs (v, v) with v on both charts.
var H0IsIntersection = h0IsIntersectionThm{family.Add(registry.ProofEntry{
	Name: "H0IsIntersection",
	Key:  "prop_86a97922d32ee28c",
	Reading: "m₀ + (−m₁) = zero forces m₀ = m₁ only in V's additive group, " +
		"which the lattice pair's module_on(R, V) supplies with both charts inside V.",
	Deps: []registry.EntryLike{
		LatticePairDef,
		LatticePairDifferenceDef,
		LatticePairH0Def,
		group_homomorphism.GroupKernelDef,
		set_product.InCross,
		module.AddGroupOn,
		module_record.RestrictModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"lattice_pair(R, A₀, A₁, V, M)",
		},
		Conclusion: "group_kernel(V.zero, set_cross(fst(M), snd(M)), lattice_pair_difference(V)) = " +
			"image(λv:B. (v, v), lattice_pair_h0(V, M).carrier)",
	},
		"a pair (m₀, m₁) of the two charts has m₀ + (−m₁) = zero exactly when "+
			"m₀ = m₁ (AddGroupOn, both in V's carrier), and then m₀ lies in fst(M) "+
			"∩ snd(M), the carrier of H⁰(M) (LatticePairH0Def, RestrictModuleDef)"),
})}

// H1IsCokernel — the image of the Čech difference on M₀ × M₁ is
// M₀ + M₁, inside the ambient: H¹(M), the ambient modulo M₀ + M₁, is the
// difference's cokernel.
var H1IsCokernel = h1IsCokernelThm{family.Add(registry.ProofEntry{
	Name: "H1IsCokernel",
	Key:  "prop_26ad036e8fefb6c7",
	Reading: "m₀ − m₁ = m₀ + (−m₁) with −m₁ ∈ M₁, the chart being a " +
		"subgroup; both charts lie in the ambient (AmbientContains), a submodule.",
	Deps: []registry.EntryLike{
		LatticePairDef,
		LatticePairDifferenceDef,
		LatticePairH1Def,
		AmbientContains,
		quotient_group.InSetMul,
		set_product.InCross,
		submodule.SubmoduleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waPair»(M)",
		},
		Conclusion: "image(lattice_pair_difference(V), set_cross(fst(M), snd(M))) = " +
			"set_mul(V.add, fst(M), snd(M)) ∧ " +
			"set_mul(V.add, fst(M), snd(M)) ⊆ lattice_pair_ambient(R, V, M)",
	},
		"a difference m₀ + (−m₁) is the sum of m₀ and the member −m₁ of snd(M), and a "+
			"sum m₀ + m₁ is the difference of m₀ and −m₁ (InSetMul, the charts closed under "+
			"negation); both charts lie in the ambient, closed under sums (AmbientContains)"),
})}

// ---------------------------------------------------------------------------
// The chart sum, sub-pairs and smaller scalars
// ---------------------------------------------------------------------------

// ChartSumInAmbient — the sum M₀ + M₁ of the charts of a lattice pair lies
// in its ambient and holds zero: the ambient is a subgroup of V holding
// both charts, and zero is zero + zero.
var ChartSumInAmbient = chartSumInAmbientThm{family.Add(registry.ProofEntry{
	Name: "ChartSumInAmbient",
	Key:  "prop_250fb40f3dab8f00",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waPair»(M)",
		},
		Conclusion: "set_mul(V.add, fst(M), snd(M)) ⊆ lattice_pair_ambient(R, V, M) ∧ " +
			"V.zero ∈ set_mul(V.add, fst(M), snd(M))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			pair Fact,
		) {
			charts := a.Conjuncts(
				a.Unfolded(pair, LatticePairDef),
				"V is an R-module",
				"M₀ is an A₀-submodule of V",
				"M₁ is an A₁-submodule of V",
				"the two charts span one R-submodule")
			vectors, chart0, chart1 := charts[0], charts[1], charts[2]
			additive := module.AddGroupOn.Read(vectors)
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			ambient := a.Conjuncts(
				a.Have(
					"the ambient is an R-submodule of V holding both charts",
					"submodule(R, V, lattice_pair_ambient(R, V, M)) ∧ "+
						"fst(M) ⊆ lattice_pair_ambient(R, V, M) ∧ "+
						"snd(M) ⊆ lattice_pair_ambient(R, V, M)",
					By(AmbientContains.At(R, A0, A1, V, M), pair)),
				"the ambient is an R-submodule of V",
				"holding M₀",
				"and M₁")
			ambientGroup := a.Have(
				"so it is a group under V's addition",
				"group_on(restrict_group(module_additive_group(V), lattice_pair_ambient(R, V, M)))",
				By(
					group.SubgroupGroupOn.Read(additive).At(a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)")),
					submodule.SubmoduleSubgroup.Read(ambient[0])))
			inside := a.Have(
				"which holds every sum of a member of M₀ and a member of M₁",
				"set_mul(V.add, fst(M), snd(M)) ⊆ lattice_pair_ambient(R, V, M)",
				By(quotient_group.SetMulIn.Read(ambientGroup).At(fstM, sndM), ambient[1], ambient[2]))
			zero := proof.MemberOf(a.TermAs[B]("V.zero"), a.Have(
				"zero is a vector",
				"V.zero ∈ V.carrier",
				By(group.OneIn.Read(additive))))
			holdsZero := a.Have(
				"and zero is zero + zero, with zero on each chart",
				"V.zero ∈ set_mul(V.add, fst(M), snd(M))",
				Simp(Fwd(quotient_group.InSetMul)),
				Witness(zero),
				Witness(zero),
				By(
					submodule.SubmoduleZero.Read(chart0),
					submodule.SubmoduleZero.Read(chart1),
					group.LeftIdentityOn.Read(additive).At(zero)))
			a.Show(
				"M₀ + M₁ lies in the ambient and holds zero",
				By(inside, holdsZero))
		}),
})}

// SubpairInclusions — for pairs M' ⊆ M chart by chart, the ambient of M'
// lies in that of M, the span growing with the set spanned, and M'₀ + M'₁
// lies in M₀ + M₁, a sum growing with its terms.
var SubpairInclusions = subpairInclusionsThm{family.Add(registry.ProofEntry{
	Name: "SubpairInclusions",
	Key:  "prop_f1d0fd5aed7095c9",
	Reading: "Neither pair need be a lattice pair, nor V a module: the ambient " +
		"is the span of the first chart, and only the inclusions of the charts enter.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
		},
		Conclusion: "lattice_pair_ambient(R, V, M') ⊆ lattice_pair_ambient(R, V, M) ∧ " +
			"set_mul(V.add, fst(M'), snd(M')) ⊆ set_mul(V.add, fst(M), snd(M))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			inside := a.Conjuncts(
				given,
				"M'₀ lies in M₀",
				"and M'₁ in M₁")
			inside0, inside1 :=
				a.Unfolded(inside[0], set_basic.SubsetDef), a.Unfolded(inside[1], set_basic.SubsetDef)
			ambients := a.Have(
				"the span of M'₀ lies in the span of M₀",
				"lattice_pair_ambient(R, V, M') ⊆ lattice_pair_ambient(R, V, M)",
				Simp(Fwd(LatticePairAmbientDef)),
				By(submodule.SpanMono.At(R, V, a.TermAs[Set[B]]("fst(M')"), a.TermAs[Set[B]]("fst(M)")), inside[0]))
			sums := a.Have(
				"a sum of a member of M'₀ and one of M'₁ is a sum of a member of M₀ and one of M₁",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ set_mul(V.add, fst(M), snd(M))",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					b.FixAs[B]("w")
					x, y, split := b.Obtain2As[B, B](
						"w is x + y for some x in M'₀ and y in M'₁",
						"∃x y:B. x ∈ fst(M') ∧ y ∈ snd(M') ∧ w = x + y",
						By(b.Assume(), quotient_group.InSetMul))
					terms := b.Conjuncts(
						split,
						"x lies in M'₀",
						"y lies in M'₁",
						"w is x + y")
					b.Do(Simp(Fwd(quotient_group.InSetMul)))
					b.Take(x)
					b.Take(y)
					b.Show(
						"x lies in M₀ and y in M₁, M' lying in M",
						By(inside0, inside1, terms[0], terms[1], terms[2]))
				}))
			a.Show(
				"the ambient and the sum of M' lie in those of M",
				By(ambients, sums))
		}),
})}

// PairModuleOn — the V of a lattice pair is a module over its ring R, the
// first clause of the definition.
var PairModuleOn = pairModuleOnThm{family.Add(registry.ProofEntry{
	Name: "PairModuleOn",
	Key:  "prop_2316fe9104269cdd",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waPair»(M)",
		},
		Conclusion: "module_on(R, V)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			pair Fact,
		) {
			a.Show(
				"a lattice pair is first of all a module",
				By(a.Unfolded(pair, LatticePairDef)))
		}),
})}

// PairOverSubring — over any subring S of both charts, read with its
// scalars restricted to S, V is a module and the charts of a lattice pair,
// their sum and its ambient are submodules of V: each is a submodule over
// a ring whose scalars hold S, and a sum of two submodules is one.
var PairOverSubring = pairOverSubringThm{family.Add(registry.ProofEntry{
	Name: "PairOverSubring",
	Key:  "prop_38ef1711f4e20c99",
	Reading: "The datum enters only to put S inside R, through chart 0. S ⊆ A₀ ∩ A₁ is " +
		"load-bearing for the charts and their sum, which are modules over their own chart ring only.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
		},
		Conclusion: "module_on(restrict_ring(R, S), V) ∧ " +
			"submodule(restrict_ring(R, S), V, fst(M)) ∧ " +
			"submodule(restrict_ring(R, S), V, snd(M)) ∧ " +
			"submodule(restrict_ring(R, S), V, set_mul(V.add, fst(M), snd(M))) ∧ " +
			"submodule(restrict_ring(R, S), V, lattice_pair_ambient(R, V, M))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"S is a subring of R",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair")
			datum, subring, inChart0, inChart1, pair :=
				hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3], hypotheses[4]
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			charts := a.Conjuncts(
				a.Unfolded(pair, LatticePairDef),
				"V is an R-module",
				"M₀ is an A₀-submodule of V",
				"M₁ is an A₁-submodule of V",
				"the two charts span one R-submodule")
			vectors, chart0, chart1 := charts[0], charts[1], charts[2]
			inR := a.Have(
				"S lies in R, chart 0 lying there",
				"S ⊆ R.carrier",
				By(ChartSubsetInOverlap.At(R, A0, A1, t, s, S), datum, inChart0))
			moduleS := a.Have(
				"V is a module over S",
				"module_on(restrict_ring(R, S), V)",
				By(module.ModuleRestrictScalars.Read(vectors).At(S), subring, inR))
			chart0OverS := a.Have(
				"M₀ is a submodule over S",
				"submodule(restrict_ring(R, S), V, fst(M))",
				By(submodule.SubmoduleRestrictScalars.Read(chart0).At(ringS), inChart0))
			chart1OverS := a.Have(
				"so is M₁",
				"submodule(restrict_ring(R, S), V, snd(M))",
				By(submodule.SubmoduleRestrictScalars.Read(chart1).At(ringS), inChart1))
			sum := a.Have(
				"so is M₀ + M₁, a sum of two submodules over S",
				"submodule(restrict_ring(R, S), V, set_mul(V.add, fst(M), snd(M)))",
				By(
					submodule.SubmoduleSum.Read(moduleS).At(a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")),
					chart0OverS,
					chart1OverS))
			ambientR := a.Conjuncts(
				GroupPremises(hypotheses[4], AmbientContains.At(R, A0, A1, V, M)),
				"the ambient is an R-submodule of V",
				"holding M₀",
				"and M₁")[0]
			a.Show(
				"V is an S-module, and the charts, their sum and the ambient are S-submodules of it",
				By(
					moduleS,
					chart0OverS,
					chart1OverS,
					sum,
					submodule.SubmoduleRestrictScalars.Read(ambientR).At(ringS),
					inR))
		}),
})}

// H1OverSubring — over any subring S of both charts, H¹ of a lattice pair
// is an S-module, the quotient of the ambient by the chart sum taken over
// S: the ambient is an S-module, M₀ + M₁ an S-submodule of it
// (PairOverSubring, ChartSumInAmbient), a module modulo a submodule is a
// module, and the class map onto the quotient is S-linear.
var H1OverSubring = h1OverSubringThm{family.Add(registry.ProofEntry{
	Name: "H1OverSubring",
	Key:  "prop_2e6adaf8b5291fbc",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waBiaffine»",
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"«waPair»(M)",
		},
		Conclusion: "module_on(restrict_ring(R, S), restrict_module(V, lattice_pair_ambient(R, V, M))) ∧ " +
			"submodule(restrict_ring(R, S), " +
			"    restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"    set_mul(V.add, fst(M), snd(M))) ∧ " +
			"module_on(restrict_ring(R, S), lattice_pair_h1(R, V, M)) ∧ " +
			"module_homomorphism(restrict_ring(R, S), " +
			"    restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"    lattice_pair_h1(R, V, M), " +
			"    coset_map(V.add, set_mul(V.add, fst(M), snd(M))))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			givenParts := a.Conjuncts(
				given,
				"the datum is biaffine",
				"S is a subring of R",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair")
			overS := a.Conjuncts(
				a.Have(
					"over S, V is a module with the charts, their sum and the ambient submodules of it",
					"module_on(restrict_ring(R, S), V) ∧ "+
						"submodule(restrict_ring(R, S), V, fst(M)) ∧ "+
						"submodule(restrict_ring(R, S), V, snd(M)) ∧ "+
						"submodule(restrict_ring(R, S), V, set_mul(V.add, fst(M), snd(M))) ∧ "+
						"submodule(restrict_ring(R, S), V, lattice_pair_ambient(R, V, M))",
					By(PairOverSubring.At(R, A0, A1, t, s, S, V, M), given)),
				"V is an S-module",
				"M₀ is an S-submodule of V",
				"so is M₁",
				"so is M₀ + M₁",
				"and so is the ambient")
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			ambient, sum :=
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"),
				a.TermAs[Set[B]]("set_mul(V.add, fst(M), snd(M))")
			ambientModule := a.TermAs[ModuleOps[A, B]]("restrict_module(V, lattice_pair_ambient(R, V, M))")
			inside := a.Conjuncts(
				GroupPremises(givenParts[4], ChartSumInAmbient.At(R, A0, A1, V, M)),
				"M₀ + M₁ lies in the ambient",
				"and holds zero")[0]
			ambientSpace := a.Have(
				"so the ambient is an S-module in its own right",
				"module_on(restrict_ring(R, S), restrict_module(V, lattice_pair_ambient(R, V, M)))",
				By(overS[4], submodule.SubmoduleModuleOn.Read(overS[0]).At(ambient)))
			sumInAmbient := a.Have(
				"with M₀ + M₁ an S-submodule of it, the ambient holding it",
				"submodule(restrict_ring(R, S), "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    set_mul(V.add, fst(M), snd(M)))",
				By(inside, overS[3], submodule.SubmoduleRestrict.At(ringS, V, ambient, sum)))
			h1Space := a.Have(
				"so H¹(M), the ambient modulo M₀ + M₁, is an S-module",
				"module_on(restrict_ring(R, S), lattice_pair_h1(R, V, M))",
				By(sumInAmbient, submodule.QuotientModuleOn.Read(ambientSpace).At(sum), LatticePairH1Def))
			projection := a.Have(
				"and the class map onto H¹(M) is S-linear",
				"module_homomorphism(restrict_ring(R, S), "+
					"    restrict_module(V, lattice_pair_ambient(R, V, M)), "+
					"    lattice_pair_h1(R, V, M), "+
					"    coset_map(V.add, set_mul(V.add, fst(M), snd(M))))",
				Simp(Fwd(LatticePairH1Def)),
				By(ambientSpace, sumInAmbient, module_homomorphism.ProjectionHom.At(ringS, ambientModule, sum)))
			a.Show(
				"the ambient, M₀ + M₁ inside it, the quotient H¹(M) and the class map, all over S",
				By(ambientSpace, sumInAmbient, h1Space, projection))
		}),
})}

// H0Submodule — H⁰ of a lattice pair is a submodule over any scalars
// lying in both charts: each chart is a submodule over its own ring, so
// over the fewer scalars, and two submodules meet in a submodule.
var H0Submodule = h0SubmoduleThm{family.Add(registry.ProofEntry{
	Name: "H0Submodule",
	Key:  "prop_52bf1021354e6a28",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁ k:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waPair»(M)",
			"k ⊆ A₀",
			"k ⊆ A₁",
		},
		Conclusion: "submodule(restrict_ring(R, k), V, fst(M) ∩ snd(M))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1, k *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"M is a lattice pair",
				"k lies in A₀",
				"k lies in A₁")
			pair := a.Conjuncts(
				a.Unfolded(parts[0], LatticePairDef),
				"V is a module over R",
				"fst(M) is a submodule over A₀",
				"snd(M) is a submodule over A₁",
				"the two span one submodule over R")
			scalars := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			chart0 := a.Have(
				"fst(M) is a submodule over k, whose scalars lie in A₀",
				"submodule(restrict_ring(R, k), V, fst(M))",
				By(parts[1], Read(submodule.SubmoduleRestrictScalars, pair[1]).At(scalars)))
			chart1 := a.Have(
				"snd(M) is a submodule over k, whose scalars lie in A₁",
				"submodule(restrict_ring(R, k), V, snd(M))",
				By(parts[2], Read(submodule.SubmoduleRestrictScalars, pair[2]).At(scalars)))
			a.Show(
				"so is their meet",
				By(
					chart0,
					chart1,
					submodule.SubmoduleInter.At(scalars, V, a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)"))))
		}),
})}

// ---------------------------------------------------------------------------
// Direct sums
// ---------------------------------------------------------------------------

// DirectSumH0 — over a field k inside both charts, H⁰ of a direct sum is
// the direct sum of the H⁰ of the summands, so h⁰ adds. A section x of M
// is a₁ + a₂ on chart 0 and b₁ + b₂ on chart 1, with aᵢ, bᵢ on the charts
// of Mᵢ; then a₁ − b₁ = b₂ − a₂ lies in both ambients, so it is zero, and
// a₁ = b₁, a₂ = b₂ are sections of M₁ and M₂. The sections of the two
// summands meet inside the two ambients, so only in zero.
var DirectSumH0 = directSumH0Thm{family.Add(registry.ProofEntry{
	Name: "DirectSumH0",
	Key:  "prop_99b65d170099a269",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M M₁ M₂:prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M₁)",
			"lattice_pair(R, A₀, A₁, V, M₂)",
			"fst(M) = set_mul(V.add, fst(M₁), fst(M₂))",
			"snd(M) = set_mul(V.add, snd(M₁), snd(M₂))",
			"lattice_pair_ambient(R, V, M₁) ∩ lattice_pair_ambient(R, V, M₂) ⊆ {V.zero}",
			"finite_dimensional(restrict_ring(R, k), lattice_pair_h0(V, M₁))",
			"finite_dimensional(restrict_ring(R, k), lattice_pair_h0(V, M₂))",
		},
		Conclusion: "finite_dimensional(restrict_ring(R, k), lattice_pair_h0(V, M)) ∧ " +
			"lattice_pair_h0_dim(R, k, V, M) = " +
			"lattice_pair_h0_dim(R, k, V, M₁) + lattice_pair_h0_dim(R, k, V, M₂)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[ModuleOps[A, B]],
			M, M1, M2 *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hyp := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0",
				"and in chart 1",
				"so is M₁",
				"so is M₂",
				"chart 0 of M is the sum of those of M₁ and M₂",
				"and so is chart 1",
				"the ambients of M₁ and M₂ meet only in zero",
				"H⁰(M₁) is finite over k",
				"so is H⁰(M₂)")
			datum, subfieldK, kIn0, kIn1, pair1, pair2 := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			sum0, sum1, meet := hyp[6], hyp[7], hyp[8]
			vectors := a.Conjuncts(
				a.Unfolded(pair1, LatticePairDef),
				"V is an R-module",
				"chart 0 of M₁ is an A₀-submodule",
				"chart 1 of M₁ is an A₁-submodule",
				"the two charts of M₁ span one R-submodule")[0]
			ambient1 := a.Conjuncts(
				a.Have(
					"the ambient of M₁ is an R-submodule of V holding both its charts",
					"submodule(R, V, lattice_pair_ambient(R, V, M₁)) ∧ "+
						"fst(M₁) ⊆ lattice_pair_ambient(R, V, M₁) ∧ "+
						"snd(M₁) ⊆ lattice_pair_ambient(R, V, M₁)",
					By(AmbientContains.At(R, A0, A1, V, M1), pair1)),
				"the ambient of M₁ is an R-submodule",
				"holding chart 0 of M₁",
				"and chart 1 of M₁")
			ambient2 := a.Conjuncts(
				a.Have(
					"and so is that of M₂",
					"submodule(R, V, lattice_pair_ambient(R, V, M₂)) ∧ "+
						"fst(M₂) ⊆ lattice_pair_ambient(R, V, M₂) ∧ "+
						"snd(M₂) ⊆ lattice_pair_ambient(R, V, M₂)",
					By(AmbientContains.At(R, A0, A1, V, M2), pair2)),
				"the ambient of M₂ is an R-submodule",
				"holding chart 0 of M₂",
				"and chart 1 of M₂")
			inV := a.Have(
				"both ambients lie in V",
				"lattice_pair_ambient(R, V, M₁) ⊆ V.carrier ∧ lattice_pair_ambient(R, V, M₂) ⊆ V.carrier",
				By(submodule.SubmoduleSubset.Read(ambient1[0]), submodule.SubmoduleSubset.Read(ambient2[0])))
			sections1, sections2 := a.TermAs[Set[B]]("fst(M₁) ∩ snd(M₁)"), a.TermAs[Set[B]]("fst(M₂) ∩ snd(M₂)")

			// A section of M splits into sections of M₁ and M₂.
			splits := a.Have(
				"a section of M is a section of M₁ plus a section of M₂",
				"fst(M) ∩ snd(M) ⊆ set_mul(V.add, fst(M₁) ∩ snd(M₁), fst(M₂) ∩ snd(M₂))",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					b.FixAs[B]("x")
					onCharts := b.Conjuncts(
						b.Have(
							"x lies on chart 0 and on chart 1 of M, sums of the summands' charts",
							"x ∈ set_mul(V.add, fst(M₁), fst(M₂)) ∧ x ∈ set_mul(V.add, snd(M₁), snd(M₂))",
							BySets(b.Assume(), sum0, sum1)),
						"x lies on chart 0 of M",
						"x lies on chart 1 of M")
					a1, a2, first := b.Obtain2As[B, B](
						"x is a₁ + a₂ with aᵢ on chart 0 of Mᵢ",
						"∃a₁ a₂:B. a₁ ∈ fst(M₁) ∧ a₂ ∈ fst(M₂) ∧ x = a₁ + a₂",
						By(onCharts[0], quotient_group.InSetMul))
					b1, b2, second := b.Obtain2As[B, B](
						"and b₁ + b₂ with bᵢ on chart 1 of Mᵢ",
						"∃b₁ b₂:B. b₁ ∈ snd(M₁) ∧ b₂ ∈ snd(M₂) ∧ x = b₁ + b₂",
						By(onCharts[1], quotient_group.InSetMul))
					p := b.Conjuncts(
						first,
						"a₁ lies on chart 0 of M₁",
						"a₂ lies on chart 0 of M₂",
						"x is a₁ + a₂")
					q := b.Conjuncts(
						second,
						"b₁ lies on chart 1 of M₁",
						"b₂ lies on chart 1 of M₂",
						"x is b₁ + b₂")
					within := b.Conjuncts(
						b.Have(
							"a₁ and b₁ lie in the ambient of M₁, a₂ and b₂ in that of M₂",
							"a₁ ∈ lattice_pair_ambient(R, V, M₁) ∧ "+
								"b₁ ∈ lattice_pair_ambient(R, V, M₁) ∧ "+
								"a₂ ∈ lattice_pair_ambient(R, V, M₂) ∧ "+
								"b₂ ∈ lattice_pair_ambient(R, V, M₂)",
							BySets(p[0], q[0], p[1], q[1], ambient1[1], ambient1[2], ambient2[1], ambient2[2])),
						"a₁ lies in the ambient of M₁",
						"b₁ lies in the ambient of M₁",
						"a₂ lies in the ambient of M₂",
						"b₂ lies in the ambient of M₂")
					vectorsIn := b.Conjuncts(
						b.Have(
							"so all four are vectors",
							"a₁ ∈ V.carrier ∧ b₁ ∈ V.carrier ∧ a₂ ∈ V.carrier ∧ b₂ ∈ V.carrier",
							BySets(within[0], within[1], within[2], within[3], inV)),
						"a₁ is a vector",
						"b₁ is a vector",
						"a₂ is a vector",
						"b₂ is a vector")
					a1V, b1V := b.MemberOf[on.V](a1, vectorsIn[0]), b.MemberOf[on.V](b1, vectorsIn[1])
					a2V, b2V := b.MemberOf[on.V](a2, vectorsIn[2]), b.MemberOf[on.V](b2, vectorsIn[3])
					in1 := b.Have(
						"a₁ − b₁ lies in the ambient of M₁",
						"a₁ + -b₁ ∈ lattice_pair_ambient(R, V, M₁)",
						By(within[0], within[1], submodule.SubmoduleSub.Read(ambient1[0])))
					in2 := b.Have(
						"b₂ − a₂ lies in the ambient of M₂",
						"b₂ + -a₂ ∈ lattice_pair_ambient(R, V, M₂)",
						By(within[2], within[3], submodule.SubmoduleSub.Read(ambient2[0])))
					same := b.Have(
						"and the two are one vector, a₁ + a₂ and b₁ + b₂ both being x",
						"a₁ + -b₁ = b₂ + -a₂",
						ByChase(Depth(0), vectors, a1V, b1V, a2V, b2V, p[2], q[2]))
					vanishes := b.Have(
						"so a₁ − b₁ is zero, the ambients meeting only in zero",
						"a₁ + -b₁ = V.zero",
						BySets(in1, in2, same, meet))
					equal1 := b.Have(
						"so a₁ = b₁",
						"a₁ = b₁",
						ByChase(Depth(0), vectors, a1V, b1V, vanishes))
					equal2 := b.Have(
						"and a₂ = b₂",
						"a₂ = b₂",
						ByChase(Depth(0), vectors, a1V, b1V, a2V, b2V, vanishes, same))
					section1 := b.Have(
						"a₁ is a section of M₁",
						"a₁ ∈ fst(M₁) ∩ snd(M₁)",
						BySets(p[0], q[0], equal1))
					section2 := b.Have(
						"a₂ is a section of M₂",
						"a₂ ∈ fst(M₂) ∩ snd(M₂)",
						BySets(p[1], q[1], equal2))
					b.Do(Simp(Fwd(quotient_group.InSetMul)), Witness(a1V), Witness(a2V))
					b.Show(
						"x is a₁ + a₂",
						By(section1, section2, p[2]))
				}))
			joins := a.Have(
				"and a section of M₁ plus a section of M₂ is a section of M",
				"set_mul(V.add, fst(M₁) ∩ snd(M₁), fst(M₂) ∩ snd(M₂)) ⊆ fst(M) ∩ snd(M)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					b.FixAs[B]("x")
					h1, h2, split := b.Obtain2As[B, B](
						"x is h₁ + h₂ with hᵢ a section of Mᵢ",
						"∃h₁ h₂:B. h₁ ∈ fst(M₁) ∩ snd(M₁) ∧ h₂ ∈ fst(M₂) ∩ snd(M₂) ∧ x = h₁ + h₂",
						By(b.Assume(), quotient_group.InSetMul))
					terms := b.Conjuncts(
						split,
						"h₁ is a section of M₁",
						"h₂ is a section of M₂",
						"x is h₁ + h₂")
					onChart0 := b.Have(
						"so x lies on chart 0 of M₁ plus chart 0 of M₂",
						"x ∈ set_mul(V.add, fst(M₁), fst(M₂))",
						Simp(Fwd(quotient_group.InSetMul)),
						Witness(h1),
						Witness(h2),
						BySets(terms[0], terms[1], terms[2]))
					onChart1 := b.Have(
						"and on chart 1 of M₁ plus chart 1 of M₂",
						"x ∈ set_mul(V.add, snd(M₁), snd(M₂))",
						Simp(Fwd(quotient_group.InSetMul)),
						Witness(h1),
						Witness(h2),
						BySets(terms[0], terms[1], terms[2]))
					b.Show(
						"so x lies on both charts of M",
						BySets(onChart0, onChart1, sum0, sum1))
				}))
			sections := a.Have(
				"so H⁰(M) is the sum of H⁰(M₁) and H⁰(M₂)",
				"fst(M) ∩ snd(M) = set_mul(V.add, fst(M₁) ∩ snd(M₁), fst(M₂) ∩ snd(M₂))",
				By(splits, joins, set_order.SubsetAntisym))
			apart := a.Have(
				"which meet only in zero, inside the two ambients",
				"(fst(M₁) ∩ snd(M₁)) ∩ (fst(M₂) ∩ snd(M₂)) ⊆ {V.zero}",
				BySets(ambient1[1], ambient2[1], meet))

			// Over k the dimensions add.
			scalars := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			subringK := a.Have(
				"k is a subring of R",
				"subring(R, k)",
				By(ChartFieldSubring.At(R, A0, A1, t, s, k, inv), datum, subfieldK, kIn0))
			overK := a.Have(
				"V is a vector space over k",
				"module_on(restrict_ring(R, k), V)",
				By(PairOverSubring.At(R, A0, A1, t, s, k, V, M1), datum, subringK, kIn0, kIn1, pair1))
			subspace1 := a.Have(
				"H⁰(M₁) is a subspace over k",
				"submodule(restrict_ring(R, k), V, fst(M₁) ∩ snd(M₁))",
				By(H0Submodule.At(R, A0, A1, k, V, M1), pair1, kIn0, kIn1))
			subspace2 := a.Have(
				"and so is H⁰(M₂)",
				"submodule(restrict_ring(R, k), V, fst(M₂) ∩ snd(M₂))",
				By(H0Submodule.At(R, A0, A1, k, V, M2), pair2, kIn0, kIn1))
			finite1 := a.Have(
				"H⁰(M₁) is finite over k",
				"«waFinite»(restrict_module(V, fst(M₁) ∩ snd(M₁)))",
				Simp(Rev(LatticePairH0Def)),
				By(hyp[9]))
			finite2 := a.Have(
				"and so is H⁰(M₂)",
				"«waFinite»(restrict_module(V, fst(M₂) ∩ snd(M₂)))",
				Simp(Rev(LatticePairH0Def)),
				By(hyp[10]))
			added := a.Have(
				"so their direct sum is finite over k, of the sum of their dimensions",
				"«waFinite»(restrict_module(V, set_mul(V.add, fst(M₁) ∩ snd(M₁), fst(M₂) ∩ snd(M₂)))) ∧ "+
					"«waDim»(restrict_module(V, set_mul(V.add, fst(M₁) ∩ snd(M₁), fst(M₂) ∩ snd(M₂)))) = "+
					"«waDim»(restrict_module(V, fst(M₁) ∩ snd(M₁))) + «waDim»(restrict_module(V, fst(M₂) ∩ snd(M₂)))",
				By(
					module_dimension.DirectSumDim.At(scalars, inv, V, sections1, sections2),
					subfieldK,
					field.RingSubfieldRestrict.At(R, k, inv, k),
					overK,
					subspace1,
					subspace2,
					apart,
					finite1,
					finite2))
			a.Show(
				"so H⁰(M) is finite over k and h⁰(M) = h⁰(M₁) + h⁰(M₂)",
				Simp(Fwd(LatticePairH0DimDef), Fwd(LatticePairH0Def)),
				sections.Rw(),
				By(added))
		}),
})}

// DirectSumH1 — over a field k inside both charts, H¹ of a direct sum is
// the direct sum of the H¹ of the summands, so h¹ adds. The ambient of M
// is the sum of the summands' ambients: that sum is an R-submodule holding
// chart 0 of each summand, so chart 0 of M and its span; and each
// summand's charts lie in M's, so its ambient lies in M's. Likewise
// M₀ + M₁ is the sum of the summands' chart sums, each side a k-subspace
// holding the other's terms. The ambients meet only in zero, so the
// quotients add (QuotientDirectSumDim).
var DirectSumH1 = directSumH1Thm{family.Add(registry.ProofEntry{
	Name: "DirectSumH1",
	Key:  "prop_53a9db52f28ddb28",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M M₁ M₂:prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M₁)",
			"lattice_pair(R, A₀, A₁, V, M₂)",
			"fst(M) = set_mul(V.add, fst(M₁), fst(M₂))",
			"snd(M) = set_mul(V.add, snd(M₁), snd(M₂))",
			"lattice_pair_ambient(R, V, M₁) ∩ lattice_pair_ambient(R, V, M₂) ⊆ {V.zero}",
			"finite_dimensional(restrict_ring(R, k), lattice_pair_h1(R, V, M₁))",
			"finite_dimensional(restrict_ring(R, k), lattice_pair_h1(R, V, M₂))",
		},
		Conclusion: "finite_dimensional(restrict_ring(R, k), lattice_pair_h1(R, V, M)) ∧ " +
			"lattice_pair_h1_dim(R, k, V, M) = " +
			"lattice_pair_h1_dim(R, k, V, M₁) + lattice_pair_h1_dim(R, k, V, M₂)",
		Abbrev: Abbrev{
			{Name: "waAmbientsSum", Text: "set_mul(V.add, " +
				"    lattice_pair_ambient(R, V, M₁), " +
				"    lattice_pair_ambient(R, V, M₂))"},
			{Name: "waChartSumsSum", Text: "set_mul(V.add, " +
				"    set_mul(V.add, fst(M₁), snd(M₁)), " +
				"    set_mul(V.add, fst(M₂), snd(M₂)))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[ModuleOps[A, B]],
			M, M1, M2 *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hyp := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0",
				"and in chart 1",
				"M is a lattice pair",
				"so is M₁",
				"so is M₂",
				"chart 0 of M is the sum of those of M₁ and M₂",
				"and so is chart 1",
				"the ambients of M₁ and M₂ meet only in zero",
				"H¹(M₁) is finite over k",
				"so is H¹(M₂)")
			datum, subfieldK, kIn0, kIn1, pair, pair1, pair2 :=
				hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5], hyp[6]
			sum0, sum1, meet := hyp[7], hyp[8], hyp[9]
			subringK := a.Have(
				"k is a subring of R",
				"subring(R, k)",
				By(ChartFieldSubring.At(R, A0, A1, t, s, k, inv), datum, subfieldK, kIn0))
			scalars := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			vectors := a.Conjuncts(
				a.Unfolded(pair, LatticePairDef),
				"V is an R-module",
				"chart 0 of M is an A₀-submodule",
				"chart 1 of M is an A₁-submodule",
				"the two charts of M span one R-submodule")[0]
			fst, snd := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			fst1, snd1, fst2, snd2 :=
				a.TermAs[Set[B]]("fst(M₁)"),
				a.TermAs[Set[B]]("snd(M₁)"),
				a.TermAs[Set[B]]("fst(M₂)"),
				a.TermAs[Set[B]]("snd(M₂)")
			ambient, ambient1, ambient2 :=
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"),
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M₁)"),
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M₂)")
			chartSum, chartSum1, chartSum2 :=
				a.TermAs[Set[B]]("set_mul(V.add, fst(M), snd(M))"),
				a.TermAs[Set[B]]("set_mul(V.add, fst(M₁), snd(M₁))"),
				a.TermAs[Set[B]]("set_mul(V.add, fst(M₂), snd(M₂))")
			ambientsSum, chartSumsSum :=
				a.TermAs[Set[B]]("«waAmbientsSum»"), a.TermAs[Set[B]]("«waChartSumsSum»")

			// Over k: V a vector space, the charts, chart sums and ambients subspaces.
			spaceK := a.Have(
				"V is a vector space over k",
				"module_on(restrict_ring(R, k), V)",
				By(PairOverSubring.At(R, A0, A1, t, s, k, V, M1), datum, subringK, kIn0, kIn1, pair1))
			overK1 := a.Conjuncts(
				a.Have(
					"the charts of M₁, their sum and its ambient are k-subspaces",
					"submodule(restrict_ring(R, k), V, fst(M₁)) ∧ "+
						"submodule(restrict_ring(R, k), V, snd(M₁)) ∧ "+
						"submodule(restrict_ring(R, k), V, set_mul(V.add, fst(M₁), snd(M₁))) ∧ "+
						"submodule(restrict_ring(R, k), V, lattice_pair_ambient(R, V, M₁))",
					By(PairOverSubring.At(R, A0, A1, t, s, k, V, M1), datum, subringK, kIn0, kIn1, pair1)),
				"chart 0 of M₁ is a k-subspace",
				"chart 1 of M₁ is a k-subspace",
				"the chart sum of M₁ is a k-subspace",
				"the ambient of M₁ is a k-subspace")
			overK2 := a.Conjuncts(
				a.Have(
					"and so for M₂",
					"submodule(restrict_ring(R, k), V, fst(M₂)) ∧ "+
						"submodule(restrict_ring(R, k), V, snd(M₂)) ∧ "+
						"submodule(restrict_ring(R, k), V, set_mul(V.add, fst(M₂), snd(M₂))) ∧ "+
						"submodule(restrict_ring(R, k), V, lattice_pair_ambient(R, V, M₂))",
					By(PairOverSubring.At(R, A0, A1, t, s, k, V, M2), datum, subringK, kIn0, kIn1, pair2)),
				"chart 0 of M₂ is a k-subspace",
				"chart 1 of M₂ is a k-subspace",
				"the chart sum of M₂ is a k-subspace",
				"the ambient of M₂ is a k-subspace")
			chartSumK := a.Have(
				"and the chart sum of M is a k-subspace",
				"submodule(restrict_ring(R, k), V, set_mul(V.add, fst(M), snd(M)))",
				By(PairOverSubring.At(R, A0, A1, t, s, k, V, M), datum, subringK, kIn0, kIn1, pair))

			// Each summand lies in M chart by chart, so its ambient and chart sum lie in M's.
			charts1 := a.Have(
				"the charts of M₁ lie in those of M",
				"fst(M₁) ⊆ fst(M) ∧ snd(M₁) ⊆ snd(M)",
				sum0.Rw(),
				sum1.Rw(),
				By(
					submodule.SumContainsLeft.Read(spaceK).At(fst1, fst2),
					submodule.SumContainsLeft.Read(spaceK).At(snd1, snd2),
					overK1[0],
					overK2[0],
					overK1[1],
					overK2[1]))
			charts2 := a.Have(
				"and so do those of M₂",
				"fst(M₂) ⊆ fst(M) ∧ snd(M₂) ⊆ snd(M)",
				sum0.Rw(),
				sum1.Rw(),
				By(
					submodule.SumContainsRight.Read(spaceK).At(fst1, fst2),
					submodule.SumContainsRight.Read(spaceK).At(snd1, snd2),
					overK1[0],
					overK2[0],
					overK1[1],
					overK2[1]))
			within1 := a.Have(
				"so the ambient and the chart sum of M₁ lie in those of M",
				"lattice_pair_ambient(R, V, M₁) ⊆ lattice_pair_ambient(R, V, M) ∧ "+
					"set_mul(V.add, fst(M₁), snd(M₁)) ⊆ set_mul(V.add, fst(M), snd(M))",
				By(SubpairInclusions.At(R, V, M, M1), charts1))
			within2 := a.Have(
				"and those of M₂",
				"lattice_pair_ambient(R, V, M₂) ⊆ lattice_pair_ambient(R, V, M) ∧ "+
					"set_mul(V.add, fst(M₂), snd(M₂)) ⊆ set_mul(V.add, fst(M), snd(M))",
				By(SubpairInclusions.At(R, V, M, M2), charts2))

			// The ambients add.
			contains := a.Conjuncts(
				a.Have(
					"each ambient is an R-submodule of V holding its chart 0",
					"submodule(R, V, lattice_pair_ambient(R, V, M)) ∧ "+
						"submodule(R, V, lattice_pair_ambient(R, V, M₁)) ∧ "+
						"fst(M₁) ⊆ lattice_pair_ambient(R, V, M₁) ∧ "+
						"submodule(R, V, lattice_pair_ambient(R, V, M₂)) ∧ "+
						"fst(M₂) ⊆ lattice_pair_ambient(R, V, M₂)",
					By(
						AmbientContains.At(R, A0, A1, V, M),
						pair,
						AmbientContains.At(R, A0, A1, V, M1),
						pair1,
						AmbientContains.At(R, A0, A1, V, M2),
						pair2)),
				"the ambient of M is an R-submodule",
				"so is that of M₁",
				"holding chart 0 of M₁",
				"so is that of M₂",
				"holding chart 0 of M₂")
			ambientsSubmodule := a.Have(
				"the sum of the summands' ambients is an R-submodule",
				"submodule(R, V, «waAmbientsSum»)",
				By(submodule.SubmoduleSum.Read(vectors).At(ambient1, ambient2), contains[1], contains[3]))
			ambientsHold := a.Have(
				"holding each of the two ambients",
				"lattice_pair_ambient(R, V, M₁) ⊆ «waAmbientsSum» ∧ "+
					"lattice_pair_ambient(R, V, M₂) ⊆ «waAmbientsSum»",
				By(
					submodule.SumContainsLeft.Read(vectors).At(ambient1, ambient2),
					submodule.SumContainsRight.Read(vectors).At(ambient1, ambient2),
					contains[1],
					contains[3]))
			charts0Hold := a.Have(
				"so it holds chart 0 of each summand",
				"fst(M₁) ⊆ «waAmbientsSum» ∧ fst(M₂) ⊆ «waAmbientsSum»",
				BySets(contains[2], contains[4], ambientsHold))
			chart0In := a.Have(
				"and so chart 0 of M, the sum of the summands' charts 0",
				"fst(M) ⊆ «waAmbientsSum»",
				sum0.Rw(),
				By(submodule.SumLeast.At(R, V, fst1, fst2, ambientsSum), ambientsSubmodule, charts0Hold))
			ambientWithin := a.Have(
				"and with it the ambient of M, its span",
				"lattice_pair_ambient(R, V, M) ⊆ «waAmbientsSum»",
				By(
					LatticePairAmbientDef.At(R, V, M),
					submodule.SpanLeast.At(R, V, fst, ambientsSum),
					ambientsSubmodule,
					chart0In))
			ambientHolds := a.Have(
				"the ambient of M holds the sum of the two ambients",
				"«waAmbientsSum» ⊆ lattice_pair_ambient(R, V, M)",
				By(submodule.SumLeast.At(R, V, ambient1, ambient2, ambient), contains[0], within1, within2))
			ambients := a.Have(
				"so the ambient of M is the sum of the two ambients",
				"lattice_pair_ambient(R, V, M) = «waAmbientsSum»",
				By(ambientWithin, ambientHolds, set_order.SubsetAntisym))

			// The chart sums add.
			sumsSubmodule := a.Have(
				"the sum of the summands' chart sums is a k-subspace",
				"submodule(restrict_ring(R, k), V, «waChartSumsSum»)",
				By(submodule.SubmoduleSum.Read(spaceK).At(chartSum1, chartSum2), overK1[2], overK2[2]))
			sumsHold := a.Have(
				"holding each of the two chart sums",
				"set_mul(V.add, fst(M₁), snd(M₁)) ⊆ «waChartSumsSum» ∧ "+
					"set_mul(V.add, fst(M₂), snd(M₂)) ⊆ «waChartSumsSum»",
				By(
					submodule.SumContainsLeft.Read(spaceK).At(chartSum1, chartSum2),
					submodule.SumContainsRight.Read(spaceK).At(chartSum1, chartSum2),
					overK1[2],
					overK2[2]))
			chartsIn1 := a.Have(
				"each chart of M₁ lies in its chart sum",
				"fst(M₁) ⊆ set_mul(V.add, fst(M₁), snd(M₁)) ∧ snd(M₁) ⊆ set_mul(V.add, fst(M₁), snd(M₁))",
				By(
					submodule.SumContainsLeft.Read(spaceK).At(fst1, snd1),
					submodule.SumContainsRight.Read(spaceK).At(fst1, snd1),
					overK1[0],
					overK1[1]))
			chartsIn2 := a.Have(
				"and each chart of M₂ in its own",
				"fst(M₂) ⊆ set_mul(V.add, fst(M₂), snd(M₂)) ∧ snd(M₂) ⊆ set_mul(V.add, fst(M₂), snd(M₂))",
				By(
					submodule.SumContainsLeft.Read(spaceK).At(fst2, snd2),
					submodule.SumContainsRight.Read(spaceK).At(fst2, snd2),
					overK2[0],
					overK2[1]))
			pieces := a.Have(
				"so every chart of either summand lies in the sum of the chart sums",
				"fst(M₁) ⊆ «waChartSumsSum» ∧ "+
					"snd(M₁) ⊆ «waChartSumsSum» ∧ "+
					"fst(M₂) ⊆ «waChartSumsSum» ∧ "+
					"snd(M₂) ⊆ «waChartSumsSum»",
				BySets(chartsIn1, chartsIn2, sumsHold))
			charts0In := a.Have(
				"so chart 0 of M lies in it",
				"fst(M) ⊆ «waChartSumsSum»",
				sum0.Rw(),
				By(submodule.SumLeast.At(scalars, V, fst1, fst2, chartSumsSum), sumsSubmodule, pieces))
			charts1In := a.Have(
				"and chart 1 of M",
				"snd(M) ⊆ «waChartSumsSum»",
				sum1.Rw(),
				By(submodule.SumLeast.At(scalars, V, snd1, snd2, chartSumsSum), sumsSubmodule, pieces))
			chartSumWithin := a.Have(
				"so the chart sum of M lies in the sum of the chart sums",
				"set_mul(V.add, fst(M), snd(M)) ⊆ «waChartSumsSum»",
				By(submodule.SumLeast.At(scalars, V, fst, snd, chartSumsSum), sumsSubmodule, charts0In, charts1In))
			chartSumHolds := a.Have(
				"and holds it, holding both chart sums",
				"«waChartSumsSum» ⊆ set_mul(V.add, fst(M), snd(M))",
				By(submodule.SumLeast.At(scalars, V, chartSum1, chartSum2, chartSum), chartSumK, within1, within2))
			chartSums := a.Have(
				"so the chart sum of M is the sum of the two chart sums",
				"set_mul(V.add, fst(M), snd(M)) = «waChartSumsSum»",
				By(chartSumWithin, chartSumHolds, set_order.SubsetAntisym))

			// Over k the dimensions add.
			inside1 := a.Conjuncts(
				a.Have(
					"the chart sum of M₁ lies in its ambient",
					"set_mul(V.add, fst(M₁), snd(M₁)) ⊆ lattice_pair_ambient(R, V, M₁) ∧ "+
						"V.zero ∈ set_mul(V.add, fst(M₁), snd(M₁))",
					By(ChartSumInAmbient.At(R, A0, A1, V, M1), pair1)),
				"the chart sum of M₁ lies in its ambient",
				"and holds zero")[0]
			inside2 := a.Conjuncts(
				a.Have(
					"and that of M₂ in its own",
					"set_mul(V.add, fst(M₂), snd(M₂)) ⊆ lattice_pair_ambient(R, V, M₂) ∧ "+
						"V.zero ∈ set_mul(V.add, fst(M₂), snd(M₂))",
					By(ChartSumInAmbient.At(R, A0, A1, V, M2), pair2)),
				"the chart sum of M₂ lies in its ambient",
				"and holds zero")[0]
			finite1 := a.Have(
				"H¹(M₁) is finite over k",
				"«waFinite»(quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M₁)), "+
					"        set_mul(V.add, fst(M₁), snd(M₁))))",
				Simp(Rev(LatticePairH1Def)),
				By(hyp[10]))
			finite2 := a.Have(
				"and so is H¹(M₂)",
				"«waFinite»(quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M₂)), "+
					"        set_mul(V.add, fst(M₂), snd(M₂))))",
				Simp(Rev(LatticePairH1Def)),
				By(hyp[11]))
			added := a.Have(
				"so the sum of the ambients modulo the sum of the chart "+
					"sums is finite over k, of the sum of the two dimensions",
				"«waFinite»(quotient_module(restrict_module(V, «waAmbientsSum»), «waChartSumsSum»)) ∧ "+
					"«waDim»(quotient_module(restrict_module(V, «waAmbientsSum»), «waChartSumsSum»)) = "+
					"«waDim»(quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M₁)), "+
					"        set_mul(V.add, fst(M₁), snd(M₁)))) + "+
					"«waDim»(quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M₂)), "+
					"        set_mul(V.add, fst(M₂), snd(M₂))))",
				By(
					module_dimension.QuotientDirectSumDim.At(scalars, V, inv, ambient1, ambient2, chartSum1, chartSum2),
					spaceK,
					subfieldK,
					field.RingSubfieldRestrict.At(R, k, inv, k),
					overK1[3],
					overK2[3],
					overK1[2],
					overK2[2],
					inside1,
					inside2,
					meet,
					finite1,
					finite2))
			a.Show(
				"so H¹(M) is finite over k and h¹(M) = h¹(M₁) + h¹(M₂)",
				Simp(Fwd(LatticePairH1DimDef), Fwd(LatticePairH1Def)),
				ambients.Rw(),
				chartSums.Rw(),
				By(added))
		}),
})}

// ContractedQuotientDimLocalizes — a chart quotient M₀/N₀ of finite dimension
// keeps its dimension on the overlap when N₀ is contracted from its span:
// span(M₀)/span(N₀) has the dimension of M₀/N₀. QuotientDimLocalizes bounds it
// above, and the contraction makes x + N₀ ↦ x + span(N₀) injective, which
// bounds it below.
var ContractedQuotientDimLocalizes = contractedQuotientDimLocalizesThm{family.Add(registry.ProofEntry{
	Name: "ContractedQuotientDimLocalizes",
	Key:  "prop_b1c71f6b765d18ed",
	Reading: "The contraction is load-bearing: at k[t] ⊆ k[t, 1/t] with M₀ = k[t] " +
		"and N₀ = t · k[t], one lies in M₀ and in the span of N₀ but not in N₀, the " +
		"span of N₀ is everything, and the one-dimensional quotient dies on the overlap.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M₀ N₀:set(B).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"module_on(R, V)",
			"submodule(restrict_ring(R, A₀), V, M₀)",
			"submodule(restrict_ring(R, A₀), V, N₀)",
			"N₀ ⊆ M₀",
			"finite_dimensional(restrict_ring(R, k), «quotient»)",
			"M₀ ∩ module_span(R, V, N₀) ⊆ N₀",
		},
		Conclusion: "module_dim(restrict_ring(R, k), «target») = " +
			"module_dim(restrict_ring(R, k), «quotient»)",
		Abbrev: Abbrev{
			{Name: "quotient", Text: "quotient_module(restrict_module(V, M₀), N₀)"},
			{Name: "target", Text: "quotient_module(restrict_module(V, module_span(R, V, M₀)), " +
				"    module_span(R, V, N₀))"},
			{Name: "enlarging", Text: "λx:set(B). set_mul(V.add, x, module_span(R, V, N₀))"},
			{Name: "values", Text: "image(«enlarging», left_cosets(V.add, M₀, N₀))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[module_record.ModuleOps[A, B]],
			M0, N0 *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"R, A₀ and A₁ form a biaffine datum",
				"k is a field",
				"k lies in A₀",
				"V is a module over R",
				"M₀ is a submodule of V over A₀",
				"so is N₀",
				"N₀ lies in M₀",
				"M₀/N₀ is finite-dimensional over k",
				"N₀ is contracted from its span")
			datum, subfieldK, kInA0, moduleV, subM, subN :=
				given[0], given[1], given[2], given[3], given[4], given[5]
			below, finiteQuotient, contracted := given[6], given[7], given[8]
			scalars := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			spanM, spanN := a.TermAs[Set[B]]("module_span(R, V, M₀)"), a.TermAs[Set[B]]("module_span(R, V, N₀)")
			quotient := a.TermAs[module_record.ModuleOps[A, Set[B]]]("«quotient»")
			target := a.TermAs[module_record.ModuleOps[A, Set[B]]]("«target»")
			values := a.TermAs[Set[Set[B]]]("«values»")
			enlarging := a.TermAs[Fun[Set[B], Set[B]]]("«enlarging»")

			upper := a.Have(
				"span(M₀)/span(N₀) is finite-dimensional, of dimension at most that of M₀/N₀",
				"finite_dimensional(restrict_ring(R, k), «target») ∧ "+
					"module_dim(restrict_ring(R, k), «target») ≤ module_dim(restrict_ring(R, k), «quotient»)",
				By(
					datum,
					subfieldK,
					kInA0,
					moduleV,
					subM,
					subN,
					below,
					finiteQuotient,
					QuotientDimLocalizes.At(R, A0, A1, t, s, k, inv, V, M0, N0)))

			// Everything read over k.
			moduleK := a.Have(
				"k is a subring of R, so V is a module over k",
				"module_on(restrict_ring(R, k), V)",
				By(
					moduleV,
					datum,
					subfieldK,
					kInA0,
					ChartFieldSubring.At(R, A0, A1, t, s, k, inv),
					module.ModuleRestrictScalars.At(R, V, k)))
			mInV := a.Have(
				"M₀ lies in V",
				"M₀ ⊆ V.carrier",
				By(submodule.SubmoduleSubset.Read(subM)))
			spans := a.Have(
				"the two spans are R-submodules of V",
				"submodule(R, V, module_span(R, V, M₀)) ∧ submodule(R, V, module_span(R, V, N₀))",
				By(moduleV, mInV, submodule.SubmoduleSubset.Read(subN), submodule.SpanSubmodule))
			inclusions := a.Have(
				"N₀ lies in its span, M₀ in its span, and the first span in the second",
				"N₀ ⊆ module_span(R, V, N₀) ∧ "+
					"M₀ ⊆ module_span(R, V, M₀) ∧ "+
					"module_span(R, V, N₀) ⊆ module_span(R, V, M₀)",
				By(
					below,
					submodule.SubsetSpan.At(R, V, N0),
					submodule.SubsetSpan.At(R, V, M0),
					submodule.SpanMono.At(R, V, N0, M0)))
			overK := a.Have(
				"over k, M₀, N₀ and the two spans are submodules of V",
				"submodule(restrict_ring(R, k), V, M₀) ∧ "+
					"submodule(restrict_ring(R, k), V, N₀) ∧ "+
					"submodule(restrict_ring(R, k), V, module_span(R, V, M₀)) ∧ "+
					"submodule(restrict_ring(R, k), V, module_span(R, V, N₀))",
				By(
					kInA0,
					datum,
					ChartSubsetInOverlap.At(R, A0, A1, t, s, k),
					subM,
					subN,
					spans,
					submodule.SubmoduleRestrictScalars.Read(subM).At(scalars),
					submodule.SubmoduleRestrictScalars.Read(subN).At(scalars),
					submodule.SubmoduleRestrictScalars.At(R, V, spanM, scalars),
					submodule.SubmoduleRestrictScalars.At(R, V, spanN, scalars)))
			enlargement := a.Have(
				"x + N₀ ↦ x + span(N₀) is k-linear on M₀/N₀",
				"module_homomorphism(restrict_ring(R, k), «quotient», «target», «enlarging»)",
				By(
					moduleK,
					overK,
					below,
					inclusions,
					module_homomorphism.QuotientInclusionHom.At(scalars, V, M0, spanM, N0, spanN)))

			// The map is injective: this is where the contraction is spent.
			additive := module.AddGroupOn.Read(moduleV)
			subgroups := a.Have(
				"N₀ and its span are subgroups of V, and N₀ holds zero",
				"subgroup(module_additive_group(V), module_span(R, V, N₀)) ∧ "+
					"subgroup(module_additive_group(V), N₀) ∧ "+
					"V.zero ∈ N₀",
				By(spans, subN, submodule.SubmoduleSubgroup, submodule.SubmoduleZero))
			moduleM := a.Have(
				"M₀ is a module over k under V's operations",
				"module_on(restrict_ring(R, k), restrict_module(V, M₀))",
				By(moduleK, overK, submodule.SubmoduleModuleOn))
			additiveM := module.AddGroupOn.Read(moduleM)
			value := a.Have(
				"the map sends the class of a vector u to its class modulo the span of N₀",
				Statement{
					Binders: "∀u:B.",
					Hypotheses: []string{
						"u ∈ V.carrier",
					},
					Conclusion: "set_mul(V.add, left_coset(V.add, u, N₀), module_span(R, V, N₀)) = " +
						"left_coset(V.add, u, module_span(R, V, N₀))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					vector := proof.MemberOf(u, b.Assume())
					b.Show(
						"the span, a subgroup holding N₀ and so zero, absorbs N₀",
						By(
							quotient_group.LeftCosetSetMulAbsorb.Read(additive).At(vector, N0, spanN),
							subgroups,
							inclusions))
				}))
			sameClass := a.Have(
				"members of M₀ with one class modulo the span of N₀ have one class modulo N₀",
				Statement{
					Binders: "∀x y:B.",
					Hypotheses: []string{
						"x ∈ M₀",
						"y ∈ M₀",
						"left_coset(V.add, x, module_span(R, V, N₀)) = left_coset(V.add, y, module_span(R, V, N₀))",
					},
					Conclusion: "left_coset(V.add, x, N₀) = left_coset(V.add, y, N₀)",
				},
				Derive(func(b *Argument) {
					x, y := b.FixAs[B]("x"), b.FixAs[B]("y")
					facts := b.Conjuncts(
						b.Assume(),
						"x lies in M₀",
						"y lies in M₀",
						"x and y have one class modulo the span of N₀")
					xm := proof.MemberOf(x, b.Have(
						"x is a vector",
						"x ∈ V.carrier",
						BySets(mInV, facts[0])))
					ym := proof.MemberOf(y, b.Have(
						"so is y",
						"y ∈ V.carrier",
						BySets(mInV, facts[1])))
					inSpan := b.Have(
						"so −x + y lies in the span of N₀",
						"-x + y ∈ module_span(R, V, N₀)",
						By(facts[2], subgroups, group.LeftCosetEqOn.Read(additive).At(xm, ym, spanN)))
					xInM, yInM := proof.MemberOf(x, facts[0]), proof.MemberOf(y, facts[1])
					inM := b.Have(
						"and in M₀, a group under V's addition",
						"-x + y ∈ M₀",
						By(group.MulIn.Read(additiveM).At(group.InvIn.Read(additiveM).At(xInM), yInM)))
					inN := b.Have(
						"so in N₀, N₀ being contracted from its span",
						"-x + y ∈ N₀",
						BySets(contracted, inSpan, inM))
					b.Show(
						"so x and y have one class modulo N₀",
						By(inN, subgroups, group.LeftCosetEqOn.Read(additive).At(xm, ym, N0)))
				}))
			represented := a.Have(
				"a class of M₀/N₀ is the class of a member of M₀",
				"∀X:set(B). X ∈ left_cosets(V.add, M₀, N₀) ⇒ ∃x:B. X = left_coset(V.add, x, N₀) ∧ x ∈ M₀",
				By(below, quotient_group.InLeftCosets.Read(additiveM)))
			injective := a.Have(
				"so the map is injective on the classes of M₀/N₀",
				"injective_on(left_cosets(V.add, M₀, N₀), «enlarging»)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					X, Y := b.FixAs[Set[B]]("X"), b.FixAs[Set[B]]("Y")
					facts := b.Conjuncts(
						b.Assume(),
						"X is a class of M₀/N₀",
						"so is Y",
						"the map agrees on them")
					x, ofX := b.UnpackAs[B](GroupPremises(facts[0], represented.At(X)), "x")
					y, ofY := b.UnpackAs[B](GroupPremises(facts[1], represented.At(Y)), "y")
					first := b.Conjuncts(
						ofX,
						"X is the class of x",
						"x lies in M₀")
					second := b.Conjuncts(
						ofY,
						"Y is the class of y",
						"y lies in M₀")
					vectors := b.Have(
						"x and y are vectors",
						"x ∈ V.carrier ∧ y ∈ V.carrier",
						BySets(mInV, first[1], second[1]))
					b.Show(
						"x and y have one class modulo the span of N₀, so one class modulo N₀",
						By(
							first[0],
							second[0],
							first[1],
							second[1],
							facts[2],
							vectors,
							value.At(x),
							value.At(y),
							sameClass.At(x, y)))
				}))

			// Its image is a subspace of the target with the dimension of M₀/N₀.
			constants := a.Have(
				"k is a field of scalars",
				"ring_subfield(restrict_ring(R, k), inv, k)",
				By(subfieldK, field.RingSubfieldRestrict.At(R, k, inv, k)))
			image := a.Have(
				"an injective linear map keeps the dimension of its source",
				"finite_dimensional(restrict_ring(R, k), restrict_module(«target», «values»)) ∧ "+
					"module_dim(restrict_ring(R, k), restrict_module(«target», «values»)) = "+
					"module_dim(restrict_ring(R, k), «quotient»)",
				By(
					constants,
					enlargement,
					finiteQuotient,
					injective,
					module_dimension.InjectiveImageDim.At(scalars, inv, quotient, target, enlarging)))
			lower := a.Have(
				"the image is a subspace of the target, so no bigger than it",
				"module_dim(restrict_ring(R, k), restrict_module(«target», «values»)) ≤ "+
					"module_dim(restrict_ring(R, k), «target»)",
				By(
					module_homomorphism.HomTarget.Read(enlargement),
					constants,
					upper,
					module_homomorphism.ImageSubmodule.Read(enlargement),
					module_dimension.SubmoduleDim.At(scalars, target, inv, values)))
			a.Show(
				"the two inequalities pin the dimension",
				ByArith(upper, image, lower))
		}),
})}

// RestrictedPairCohomology — the cohomology of a pair inside a subset W of a ring
// R, read in R's regular module: restricting twice restricts to the last set, so
// H⁰ and the ambient's quotient forget W, and the dimension over k is the
// dimension of H¹ with its scalars restricted to k.
var RestrictedPairCohomology = restrictedPairCohomologyThm{family.Add(registry.ProofEntry{
	Name: "RestrictedPairCohomology",
	Key:  "prop_d9aa21509fdafd2",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "vectors", Text: "restrict_module(regular_module(R), W)"},
		},
		Binders: "∀R:ring_ops(A). ∀S k W:set(A). ∀X:prod(set(A), set(A)).",
		Conclusion: "lattice_pair_h0(«vectors», X) = " +
			"restrict_module(regular_module(R), fst(X) ∩ snd(X)) ∧ " +
			"lattice_pair_h1(restrict_ring(R, S), «vectors», X) = " +
			"quotient_module(restrict_module(regular_module(R), " +
			"        lattice_pair_ambient(restrict_ring(R, S), «vectors», X)), " +
			"    set_mul(R.add, fst(X), snd(X))) ∧ " +
			"lattice_pair_h1_dim(restrict_ring(R, S), k, «vectors», X) = " +
			"module_dim(restrict_ring(R, k), lattice_pair_h1(restrict_ring(R, S), «vectors», X))",
	},
		func(a *Argument, R *Expr[RingOps[A]], S, k, W *Expr[Set[A]], X *Expr[Prod[Set[A], Set[A]]]) {
			a.Show(
				"each is its definition, with the two restrictions of a restriction collapsed",
				Simp(
					Fwd(module_record.RestrictRingTwice),
					Fwd(module_record.RegularModuleDef),
					Fwd(LatticePairH0Def),
					Fwd(LatticePairH1Def),
					Fwd(LatticePairH1DimDef),
					Fwd(module_record.RestrictModuleTwice),
					Fwd(module_record.RestrictModuleDef)),
				Basic())
		}),
})}
