// six_term.go — the six-term sequence of a sub-pair, with the three-term
// formula for the Euler characteristic it gives.
//
// For lattice pairs M' ⊆ M chart by chart, the quotient complex is
// Q₀ × Q₁ → Q₀₁, the chart quotients Q₀ = M₀/M'₀ and Q₁ = M₁/M'₁ mapping
// by the difference c̄ to the overlap quotient Q₀₁ = ambient(M)/ambient(M').
// Its classes are cosets, and the maps of the sequence
// 0 → H⁰(M') → H⁰(M) → ker c̄ → H¹(M') → H¹(M) → 0 are read on them: the
// inclusion, v ↦ (v + M'₀, v + M'₁), the connecting map δ, which takes
// two cosets to their difference, and X ↦ X + (M₀ + M₁).

package lattice_pair_sequence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_isomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// A sub-pair: the quotient complex and the six-term sequence
// ---------------------------------------------------------------------------

// QuotientPairCosets — for a lattice pair M and pairs M' inside it chart by
// chart, a point of Q₀ × Q₁ is a pair of cosets (x + M'₀, y + M'₁) with x in
// M₀ and y in M₁: each side is a class of its chart, the chart a group
// under V's addition.
var QuotientPairCosets = quotientPairCosetsThm{family.Add(registry.ProofEntry{
	Name: "QuotientPairCosets",
	Key:  "prop_8f1db88478e55960",
	Reading: "M' need not be a lattice pair: each chart of M is " +
		"a group under V's addition, which is all its classes need.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M M' u:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waPair»(M)",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
			"u ∈ «waQuotientPairs»",
		},
		Conclusion: "∃x y:B. " +
			"    x ∈ fst(M) ∧ y ∈ snd(M) ∧ u = (left_coset(V.add, x, fst(M')), left_coset(V.add, y, snd(M')))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
			u *Expr[Prod[Set[B], Set[B]]],
			inQ Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"M is a lattice pair",
				"M'₀ lies in M₀",
				"and M'₁ in M₁")
			pair, inside0, inside1 := hypotheses[0], hypotheses[1], hypotheses[2]
			charts := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is an R-module",
				"M₀ is an A₀-submodule of V",
				"M₁ is an A₁-submodule of V",
				"the two charts span one R-submodule")
			additive := module.AddGroupOn.Read(charts[0])
			group0 := a.Have(
				"M₀ is a group under V's addition",
				"group_on(restrict_group(module_additive_group(V), fst(M)))",
				By(
					group.SubgroupGroupOn.Read(additive).At(a.TermAs[Set[B]]("fst(M)")),
					submodule.SubmoduleSubgroup.Read(charts[1])))
			group1 := a.Have(
				"and so is M₁",
				"group_on(restrict_group(module_additive_group(V), snd(M)))",
				By(
					group.SubgroupGroupOn.Read(additive).At(a.TermAs[Set[B]]("snd(M)")),
					submodule.SubmoduleSubgroup.Read(charts[2])))
			sides := a.Conjuncts(
				a.Have(
					"the sides of u are classes of Q₀ and of Q₁",
					"fst(u) ∈ left_cosets(V.add, fst(M), fst(M')) ∧ snd(u) ∈ left_cosets(V.add, snd(M), snd(M'))",
					By(
						set_product.InCrossProjections.At(a.TermAs[Set[Set[B]]]("left_cosets(V.add, fst(M), fst(M'))"),
							a.TermAs[Set[Set[B]]]("left_cosets(V.add, snd(M), snd(M'))"), u),
						inQ)),
				"the first side is a class of Q₀",
				"the second a class of Q₁")
			x, first := a.ObtainAs[B](
				"the first is x + M'₀ for some x in M₀",
				"∃x:B. fst(u) = left_coset(V.add, x, fst(M')) ∧ x ∈ fst(M)",
				By(
					quotient_group.InLeftCosets.Read(group0).At(
						a.TermAs[Set[B]]("fst(M')"), a.TermAs[Set[B]]("fst(u)")),
					sides[0],
					inside0))
			y, second := a.ObtainAs[B](
				"the second is y + M'₁ for some y in M₁",
				"∃y:B. snd(u) = left_coset(V.add, y, snd(M')) ∧ y ∈ snd(M)",
				By(
					quotient_group.InLeftCosets.Read(group1).At(
						a.TermAs[Set[B]]("snd(M')"), a.TermAs[Set[B]]("snd(u)")),
					sides[1],
					inside1))
			a.Take(x)
			a.Take(y)
			a.Show(
				"u is the pair of its two sides",
				By(Normalized, first, second, pairs.PairEta.At(u)))
		}),
})}

// ConnectingOfCosets — δ of the cosets x + N₀ and y + N₁ of two
// subgroups of V is the coset of x − y modulo N₀ + N₁: a difference
// (x + a) − (y + b) is (x − y) + (a − b), and N₁ is closed under
// negation.
var ConnectingOfCosets = connectingOfCosetsThm{family.Add(registry.ProofEntry{
	Name: "ConnectingOfCosets",
	Key:  "prop_36cba435aabbb180",
	Reading: "Only V's commutative addition enters: no scalar is used, so N₀ and N₁ " +
		"are subgroups, not submodules over one ring, as the two charts of a pair are not. " +
		"At x = y it says δ of the classes of one vector is N₀ + N₁ itself, the zero of H¹.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀V:module_ops(A, B). ∀N₀ N₁:set(B). ∀x y:B.",
		Hypotheses: []string{
			"module_on(R, V)",
			"subgroup(module_additive_group(V), N₀) ∧ subgroup(module_additive_group(V), N₁)",
			"x ∈ V.carrier",
			"y ∈ V.carrier",
		},
		Conclusion: "lattice_pair_connecting(V, (left_coset(V.add, x, N₀), left_coset(V.add, y, N₁))) = " +
			"left_coset(V.add, x + -y, set_mul(V.add, N₀, N₁))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			V *Expr[ModuleOps[A, B]],
			N0, N1 *Expr[Set[B]],
			x, y *Member[B, on.V],
			moduleV module.ModuleFact[on.R, on.V],
			subgroups Fact,
		) {
			subgroup := a.Conjuncts(
				subgroups,
				"N₀ is a subgroup of V",
				"and so is N₁")
			in0 := a.Unfolded(group.SubgroupSubset.Read(subgroup[0]).AsFact(), set_basic.SubsetDef)
			in1 := a.Unfolded(group.SubgroupSubset.Read(subgroup[1]).AsFact(), set_basic.SubsetDef)
			pointwise := a.Have(
				"the differences of the two cosets and the coset of x − y have the same points",
				"∀w:B. "+
					"    w ∈ set_mul(V.add, left_coset(V.add, x, N₀), set_inv(V.neg, left_coset(V.add, y, N₁))) ⇔ "+
					"    w ∈ left_coset(V.add, x + -y, set_mul(V.add, N₀, N₁))",
				Derive(func(b *Argument) {
					b.FixAs[B]("w")
					b.Iff()
					b.Forward(
						"a difference (x + a) − (y + b) is (x − y) + (a − b), and a − b lies in N₀ + N₁",
						func(d *Argument, member Fact) {
							a0, b1, point := d.Obtain2As[B, B](
								"w is (x + a) − (y + b) for some a in N₀ and b in N₁",
								"∃a b:B. a ∈ N₀ ∧ b ∈ N₁ ∧ w = x + a + -(y + b)",
								member.Simp(
									Fwd(quotient_group.InSetMul),
									Fwd(quotient_group.SetInvDef),
									Fwd(set_basic.InImage),
									Fwd(group.LeftCosetDef)),
								By(member))
							parts := d.Conjuncts(
								point,
								"a lies in N₀",
								"b lies in N₁",
								"w is (x + a) − (y + b)")
							aV := d.MemberOf[on.V](a0, d.Have(
								"a is a vector, N₀ lying in V",
								"a ∈ V.carrier",
								By(in0, parts[0])))
							bV := d.MemberOf[on.V](b1, d.Have(
								"and so is b",
								"b ∈ V.carrier",
								By(in1, parts[1])))
							inSum := d.Have(
								"so a − b lies in N₀ + N₁",
								"a + -b ∈ set_mul(V.add, N₀, N₁)",
								By(
									quotient_group.InSetMul.At(d.TermAs[Op[B]]("V.add"), N0, N1, d.TermAs[B]("a + -b")),
									parts[0],
									group.SubgroupInv.Read(subgroup[1]),
									parts[1]))
							regroup := d.Have(
								"(x + a) − (y + b) regroups as (x − y) + (a − b)",
								"x + a + -(y + b) = x + -y + (a + -b)",
								ByChase(Depth(0), moduleV, x, y, aV, bV))
							d.Do(Simp(Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)))
							d.Take(d.TermAs[B]("a + -b"))
							d.Show(
								"so w is x − y plus a point of N₀ + N₁",
								By(parts[2], regroup, inSum))
						})
					b.Backward(
						"a point (x − y) + (a + b) of the coset is (x + a) − (y + (−b)), with −b in N₁",
						func(d *Argument, member Fact) {
							_, point := d.UnpackAs[B](d.Simplified(
								member,
								Fwd(group.LeftCosetDef),
								Fwd(set_basic.InImage)), "n")
							pieces := d.Conjuncts(
								point,
								"w is x − y plus a point n of N₀ + N₁",
								"n lies in N₀ + N₁")
							a0, b1, split := d.Obtain2As[B, B](
								"n is a + b for some a in N₀ and b in N₁",
								"∃a b:B. a ∈ N₀ ∧ b ∈ N₁ ∧ n = a + b",
								By(pieces[1], quotient_group.InSetMul))
							parts := d.Conjuncts(
								split,
								"a lies in N₀",
								"b lies in N₁",
								"n is a + b")
							aV := d.MemberOf[on.V](a0, d.Have(
								"a is a vector, N₀ lying in V",
								"a ∈ V.carrier",
								By(in0, parts[0])))
							bV := d.MemberOf[on.V](b1, d.Have(
								"and so is b",
								"b ∈ V.carrier",
								By(in1, parts[1])))
							regroup := d.Have(
								"(x − y) + (a + b) regroups as (x + a) − (y + (−b))",
								"x + -y + (a + b) = x + a + -(y + -b)",
								ByChase(Depth(0), moduleV, x, y, aV, bV))
							d.Do(Simp(
								Fwd(quotient_group.InSetMul),
								Fwd(quotient_group.SetInvDef),
								Fwd(set_basic.InImage),
								Fwd(group.LeftCosetDef)))
							d.Show(
								"so w is x + a, a point of x + N₀, plus −(y + (−b)), the negative of a point of y + N₁",
								By(pieces[0], parts[2], regroup, parts[0], group.SubgroupInv.Read(subgroup[1]), parts[1]))
						})
				}))
			a.Show(
				"two sets with the same points are equal",
				Simp(Fwd(latticePairConnectingDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(pointwise, set_basic.Extension))
		}),
})}

// QuotientDifferenceCoset — c̄ of a pair of cosets x + M₀ and y + M₁ is
// the class of x − y modulo the ambient: δ of the pair is the coset of
// x − y by M₀ + M₁ (ConnectingOfCosets), and the ambient, a subgroup of
// V, absorbs M₀ + M₁, which lies in it and holds zero
// (lattice_pair.ChartSumInAmbient).
var QuotientDifferenceCoset = quotientDifferenceCosetThm{family.Add(registry.ProofEntry{
	Name: "QuotientDifferenceCoset",
	Key:  "prop_a0269aa673abd482",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)). ∀x y:B.",
		Hypotheses: []string{
			"«waPair»(M)",
			"x ∈ V.carrier",
			"y ∈ V.carrier",
		},
		Conclusion: "lattice_pair_quotient_difference(R, " +
			"    V, " +
			"    M, " +
			"    (left_coset(V.add, x, fst(M)), left_coset(V.add, y, snd(M)))) = " +
			"left_coset(V.add, x + -y, lattice_pair_ambient(R, V, M))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			x, y *Expr[B],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is a lattice pair",
				"x is a vector",
				"so is y")
			pair := parts[0]
			charts := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is a module over R",
				"M₀ is an A₀-submodule of V",
				"M₁ is an A₁-submodule of V",
				"the two charts span one R-submodule")
			additive := module.AddGroupOn.Read(charts[0])
			xV, yV := proof.MemberOf(x, parts[1]), proof.MemberOf(y, parts[2])
			ambient := a.Have(
				"the ambient of M is an R-submodule of V",
				"submodule(R, V, lattice_pair_ambient(R, V, M))",
				By(lattice_pair.AmbientContains.At(R, A0, A1, V, M), pair))
			difference := group.MulIn.Read(additive).At(xV, group.InvIn.Read(additive).At(yV))
			connecting := a.Have(
				"δ of the two cosets is the coset of x − y by M₀ + M₁",
				"lattice_pair_connecting(V, (left_coset(V.add, x, fst(M)), left_coset(V.add, y, snd(M)))) = "+
					"left_coset(V.add, x + -y, set_mul(V.add, fst(M), snd(M)))",
				By(
					ConnectingOfCosets.Read(charts[0]).AsFact().At(
						a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)"), x, y),
					submodule.SubmoduleSubgroup.Read(charts[1]),
					submodule.SubmoduleSubgroup.Read(charts[2]),
					xV,
					yV))
			a.Do(Simp(Fwd(latticePairQuotientDifferenceDef)), connecting.Rw())
			a.Show(
				"the ambient absorbs M₀ + M₁, which lies in it and holds zero",
				By(
					quotient_group.LeftCosetSetMulAbsorb.Read(additive).At(
						difference,
						a.TermAs[Set[B]]("set_mul(V.add, fst(M), snd(M))"),
						a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)")),
					submodule.SubmoduleSubgroup.Read(ambient),
					lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, M),
					pair))
		}),
})}

// ConnectingLinear — over any subring S of both charts the chart quotients
// Q₀ and Q₁ of a sub-pair are S-modules, and δ is an S-linear map of
// Q₀ × Q₁ to the ambient of M modulo M'₀ + M'₁. A point of Q₀ × Q₁ is a
// pair of cosets (x + M'₀, y + M'₁) (QuotientPairCosets), which δ sends to
// the coset (x − y) + (M'₀ + M'₁) (ConnectingOfCosets); cosets of the
// normal subgroups M'₀, M'₁ and M'₀ + M'₁ add and scale through their
// representatives, and the difference of representatives keeps sums and
// multiples.
var ConnectingLinear = connectingLinearThm{family.Add(registry.ProofEntry{
	Name: "ConnectingLinear",
	Key:  "prop_e68852396155dd46",
	Reading: "δ needs no choice of representatives: it is the set of differences, " +
		"which at a pair of cosets is one coset of M'₀ + M'₁. S ⊆ A₀ ∩ A₁ is " +
		"load-bearing: the chart quotients and M'₀ + M'₁ are modules over S only.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
		},
		Conclusion: "module_on(restrict_ring(R, S), " +
			"    quotient_module(restrict_module(V, fst(M)), fst(M'))) ∧ " +
			"module_on(restrict_ring(R, S), quotient_module(restrict_module(V, snd(M)), snd(M'))) ∧ " +
			"module_homomorphism(restrict_ring(R, S), " +
			"    product_module(quotient_module(restrict_module(V, fst(M)), fst(M')), " +
			"        quotient_module(restrict_module(V, snd(M)), snd(M'))), " +
			"    quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"        set_mul(V.add, fst(M'), snd(M'))), " +
			"    lattice_pair_connecting(V))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"S is a subring of R",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁")
			datum, inChart0, pair, subPair, inside0, inside1 :=
				hypotheses[0], hypotheses[2], hypotheses[4], hypotheses[5], hypotheses[6], hypotheses[7]
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			fstMPrime, sndMPrime := a.TermAs[Set[B]]("fst(M')"), a.TermAs[Set[B]]("snd(M')")
			amb, ambPrime :=
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"),
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M')")
			subSum := a.TermAs[Set[B]]("set_mul(V.add, fst(M'), snd(M'))")

			overM := a.Conjuncts(
				a.Have(
					"over S, V is a module, and M₀, M₁, M₀ + M₁ and the ambient of M are submodules of it",
					"module_on(restrict_ring(R, S), V) ∧ "+
						"submodule(restrict_ring(R, S), V, fst(M)) ∧ "+
						"submodule(restrict_ring(R, S), V, snd(M)) ∧ "+
						"submodule(restrict_ring(R, S), V, set_mul(V.add, fst(M), snd(M))) ∧ "+
						"submodule(restrict_ring(R, S), V, lattice_pair_ambient(R, V, M))",
					By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, M), given)),
				"V is an S-module",
				"M₀ is an S-submodule of V",
				"so is M₁",
				"so is M₀ + M₁",
				"and the ambient of M")
			moduleS, chart0, chart1, ambS := overM[0], overM[1], overM[2], overM[4]
			chart0Prime := a.Have(
				"so are M'₀",
				"submodule(restrict_ring(R, S), V, fst(M'))",
				By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, MPrime), given))
			chart1Prime := a.Have(
				"M'₁",
				"submodule(restrict_ring(R, S), V, snd(M'))",
				By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, MPrime), given))
			subSumS := a.Have(
				"and M'₀ + M'₁",
				"submodule(restrict_ring(R, S), V, set_mul(V.add, fst(M'), snd(M')))",
				By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, MPrime), given))
			ambIn := a.Have(
				"which lies in that of M",
				"lattice_pair_ambient(R, V, M') ⊆ lattice_pair_ambient(R, V, M)",
				By(lattice_pair.SubpairInclusions.At(R, V, M, MPrime), inside0, inside1))
			subSumInAmb := a.Have(
				"so M'₀ + M'₁ lies in the ambient of M",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ lattice_pair_ambient(R, V, M)",
				By(
					set_order.SubsetTrans.At(subSum, ambPrime, amb),
					lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, MPrime),
					subPair,
					ambIn))

			moduleM0 := a.Have(
				"M₀ is an S-module",
				"module_on(restrict_ring(R, S), restrict_module(V, fst(M)))",
				By(submodule.SubmoduleModuleOn.Read(moduleS).At(fstM), chart0))
			moduleM1 := a.Have(
				"so is M₁",
				"module_on(restrict_ring(R, S), restrict_module(V, snd(M)))",
				By(submodule.SubmoduleModuleOn.Read(moduleS).At(sndM), chart1))
			quotient0 := a.Have(
				"Q₀ = M₀/M'₀ is an S-module, M'₀ being an S-submodule of M₀",
				"module_on(restrict_ring(R, S), «waQ0»)",
				By(
					submodule.QuotientModuleOn.Read(moduleM0).At(fstMPrime),
					submodule.SubmoduleRestrict.At(ringS, V, fstM, fstMPrime),
					chart0Prime,
					inside0))
			quotient1 := a.Have(
				"so is Q₁ = M₁/M'₁",
				"module_on(restrict_ring(R, S), «waQ1»)",
				By(
					submodule.QuotientModuleOn.Read(moduleM1).At(sndMPrime),
					submodule.SubmoduleRestrict.At(ringS, V, sndM, sndMPrime),
					chart1Prime,
					inside1))
			Q0, Q1 := a.TermAs[ModuleOps[A, Set[B]]]("«waQ0»"), a.TermAs[ModuleOps[A, Set[B]]]("«waQ1»")
			product := a.Have(
				"and so is Q₀ × Q₁",
				"module_on(restrict_ring(R, S), product_module(«waQ0», «waQ1»))",
				By(module_homomorphism.ProductModuleOn.At(ringS, Q0, Q1), quotient0, quotient1))
			moduleAmb := a.Have(
				"the ambient of M is an S-module",
				"module_on(restrict_ring(R, S), restrict_module(V, lattice_pair_ambient(R, V, M)))",
				By(submodule.SubmoduleModuleOn.Read(moduleS).At(amb), ambS))
			target := a.Have(
				"and so is its quotient by M'₀ + M'₁, an S-submodule lying in it",
				"module_on(restrict_ring(R, S), «waAmbientModSubSum»)",
				By(
					submodule.QuotientModuleOn.Read(moduleAmb).At(subSum),
					submodule.SubmoduleRestrict.At(ringS, V, amb, subSum),
					subSumS,
					subSumInAmb))

			// M'₀, M'₁ and M'₀ + M'₁ are normal in V, its addition commuting, so a
			// sum of classes is the class of the sum of representatives, and a
			// multiple of a class the class of the multiple.
			additive := module.AddGroupOn.Read(moduleS)
			subgroup0 := a.Have(
				"M'₀ is a subgroup of V",
				"subgroup(module_additive_group(V), fst(M'))",
				By(submodule.SubmoduleSubgroup.Read(chart0Prime)))
			subgroup1 := a.Have(
				"M'₁ is a subgroup of V",
				"subgroup(module_additive_group(V), snd(M'))",
				By(submodule.SubmoduleSubgroup.Read(chart1Prime)))
			classSum := quotient_group.LeftCosetMulOn.Read(additive)
			classMultiple := submodule.QuotientSmulCoset.Read(moduleS)
			in0 := a.Unfolded(submodule.SubmoduleSubset.Read(chart0).AsFact(), set_basic.SubsetDef)
			in1 := a.Unfolded(submodule.SubmoduleSubset.Read(chart1).AsFact(), set_basic.SubsetDef)
			toAmb := a.Conjuncts(
				GroupPremises(hypotheses[4], lattice_pair.AmbientContains.At(R, A0, A1, V, M)),
				"the ambient of M is an R-submodule of V",
				"holding M₀",
				"and M₁")
			toAmb0, toAmb1 :=
				a.Unfolded(toAmb[1], set_basic.SubsetDef), a.Unfolded(toAmb[2], set_basic.SubsetDef)
			moduleR := a.Have(
				"V is a module over R",
				"module_on(R, V)",
				By(a.Unfolded(pair, lattice_pair.LatticePairDef)))
			inR := a.Unfolded(a.Have(
				"S lies in R, chart 0 lying there",
				"S ⊆ R.carrier",
				By(lattice_pair.ChartSubsetInOverlap.At(R, A0, A1, t, s, S), datum, inChart0)), set_basic.SubsetDef)
			classesDelta := a.Have(
				"the class of a member of the ambient of M modulo M'₀ + M'₁ is a class there",
				Statement{
					Binders: "∀u:B.",
					Hypotheses: []string{
						"u ∈ lattice_pair_ambient(R, V, M)",
					},
					Conclusion: "left_coset(V.add, u, set_mul(V.add, fst(M'), snd(M'))) ∈ " +
						"left_cosets(V.add, lattice_pair_ambient(R, V, M), set_mul(V.add, fst(M'), snd(M')))",
				},
				Simp(
					Fwd(quotient_group.LeftCosetsImage.Read(module.AddGroupOn.Read(moduleAmb))),
					Fwd(group.CosetMapDef)),
				By(set_image.FunInImage))

			into := a.Have(
				"δ of a pair of cosets is a class of the ambient of M modulo M'₀ + M'₁",
				Statement{
					Binders: "∀u:prod(set(B), set(B)).",
					Hypotheses: []string{
						"u ∈ «waQuotientPairs»",
					},
					Conclusion: "lattice_pair_connecting(V, u) ∈ " +
						"left_cosets(V.add, lattice_pair_ambient(R, V, M), set_mul(V.add, fst(M'), snd(M')))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[Prod[Set[B], Set[B]]]("u")
					inQ := b.Assume()
					x, y, uIs := b.Obtain2As[B, B](
						"u is the pair of cosets of some x in M₀ and y in M₁",
						"∃x y:B. "+
							"    x ∈ fst(M) ∧ y ∈ snd(M) ∧ u = (left_coset(V.add, x, fst(M')), left_coset(V.add, y, snd(M')))",
						By(QuotientPairCosets.At(R, A0, A1, V, M, MPrime, u), pair, inside0, inside1, inQ))
					rep := b.Conjuncts(
						uIs,
						"x lies in M₀",
						"y lies in M₁",
						"u is the pair of their cosets")
					xV := proof.MemberOf(x, b.Have(
						"x is a vector",
						"x ∈ V.carrier",
						By(in0, rep[0])))
					yV := proof.MemberOf(y, b.Have(
						"so is y",
						"y ∈ V.carrier",
						By(in1, rep[1])))
					inAmb := b.Have(
						"x − y lies in the ambient of M, which holds both charts",
						"x + -y ∈ lattice_pair_ambient(R, V, M)",
						By(submodule.SubmoduleSub.Read(toAmb[0]), toAmb0, toAmb1, rep[0], rep[1]))
					value := b.Have(
						"δ(u) is the class of x − y",
						"lattice_pair_connecting(V, u) = left_coset(V.add, x + -y, set_mul(V.add, fst(M'), snd(M')))",
						rep[2].Rw(),
						By(ConnectingOfCosets.Read(moduleS).At(fstMPrime, sndMPrime, xV, yV), subgroup0, subgroup1))
					b.Show(
						"so δ(u) is a class of the ambient of M modulo M'₀ + M'₁",
						value.Rw(),
						By(classesDelta.At(b.TermAs[B]("x + -y")), inAmb))
				}))
			adds := a.Have(
				"δ of a sum of pairs of cosets is the sum of their values",
				Statement{
					Binders: "∀u v:prod(set(B), set(B)).",
					Hypotheses: []string{
						"u ∈ «waQuotientPairs»",
						"v ∈ «waQuotientPairs»",
					},
					Conclusion: "lattice_pair_connecting(V, " +
						"    (set_mul(V.add, fst(u), fst(v)), set_mul(V.add, snd(u), snd(v)))) = " +
						"set_mul(V.add, lattice_pair_connecting(V, u), lattice_pair_connecting(V, v))",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[Prod[Set[B], Set[B]]]("u"), b.FixAs[Prod[Set[B], Set[B]]]("v")
					inQ := b.Conjuncts(
						b.Assume(),
						"u is a pair of cosets",
						"so is v")
					x1, y1, uIs := b.Obtain2As[B, B](
						"u is the pair of cosets of some x₁ in M₀ and y₁ in M₁",
						"∃x₁ y₁:B. "+
							"    x₁ ∈ fst(M) ∧ "+
							"    y₁ ∈ snd(M) ∧ "+
							"    u = (left_coset(V.add, x₁, fst(M')), left_coset(V.add, y₁, snd(M')))",
						By(QuotientPairCosets.At(R, A0, A1, V, M, MPrime, u), pair, inside0, inside1, inQ[0]))
					x2, y2, vIs := b.Obtain2As[B, B](
						"v is the pair of cosets of some x₂ in M₀ and y₂ in M₁",
						"∃x₂ y₂:B. "+
							"    x₂ ∈ fst(M) ∧ "+
							"    y₂ ∈ snd(M) ∧ "+
							"    v = (left_coset(V.add, x₂, fst(M')), left_coset(V.add, y₂, snd(M')))",
						By(QuotientPairCosets.At(R, A0, A1, V, M, MPrime, v), pair, inside0, inside1, inQ[1]))
					first := b.Conjuncts(
						uIs,
						"x₁ lies in M₀",
						"y₁ lies in M₁",
						"u is the pair of their cosets")
					second := b.Conjuncts(
						vIs,
						"x₂ lies in M₀",
						"y₂ lies in M₁",
						"v is the pair of their cosets")
					x1V := proof.MemberOf(x1, b.Have(
						"x₁ is a vector",
						"x₁ ∈ V.carrier",
						By(in0, first[0])))
					y1V := proof.MemberOf(y1, b.Have(
						"so is y₁",
						"y₁ ∈ V.carrier",
						By(in1, first[1])))
					x2V := proof.MemberOf(x2, b.Have(
						"so is x₂",
						"x₂ ∈ V.carrier",
						By(in0, second[0])))
					y2V := proof.MemberOf(y2, b.Have(
						"and y₂",
						"y₂ ∈ V.carrier",
						By(in1, second[1])))
					xSum, ySum := group.MulIn.Read(additive).At(x1V, x2V), group.MulIn.Read(additive).At(y1V, y2V)
					difference1 := group.MulIn.Read(additive).At(x1V, group.InvIn.Read(additive).At(y1V))
					difference2 := group.MulIn.Read(additive).At(x2V, group.InvIn.Read(additive).At(y2V))
					regroup := b.Have(
						"(x₁ + x₂) − (y₁ + y₂) regroups as (x₁ − y₁) + (x₂ − y₂)",
						"x₁ + x₂ + -(y₁ + y₂) = x₁ + -y₁ + (x₂ + -y₂)",
						ByChase(Depth(0), moduleS, x1V, y1V, x2V, y2V))
					b.Show(
						"δ(u + v) and δ(u) + δ(v) are computed on the representatives",
						first[2].Rw(),
						second[2].Rw(),
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("left_coset(V.add, x₁ + x₂ + -(y₁ + y₂), set_mul(V.add, fst(M'), snd(M')))"),
								"u + v is the pair of cosets of x₁ + x₂ and y₁ + y₂, and δ of it the class of their difference",
								By(
									classSum.At(fstMPrime, x1V, x2V),
									classSum.At(sndMPrime, y1V, y2V),
									submodule.SubmoduleNormal.Read(moduleS).At(fstMPrime),
									chart0Prime,
									submodule.SubmoduleNormal.Read(moduleS).At(sndMPrime),
									chart1Prime,
									ConnectingOfCosets.Read(moduleS).At(fstMPrime, sndMPrime, xSum, ySum),
									subgroup0,
									subgroup1)),
							Leg(
								b.TermAs[Set[B]]("left_coset(V.add, x₁ + -y₁ + (x₂ + -y₂), set_mul(V.add, fst(M'), snd(M')))"),
								"regrouped",
								regroup.Rw(),
								Basic()),
							FinalLeg(
								"the sum of the classes of x₁ − y₁ and x₂ − y₂, which are δ(u) and δ(v)",
								By(
									ConnectingOfCosets.Read(moduleS).At(fstMPrime, sndMPrime, x1V, y1V),
									ConnectingOfCosets.Read(moduleS).At(fstMPrime, sndMPrime, x2V, y2V),
									subgroup0,
									subgroup1,
									classSum.At(subSum, difference1, difference2),
									submodule.SubmoduleNormal.Read(moduleS).At(subSum),
									subSumS)),
						))
				}))
			scales := a.Have(
				"δ of a multiple of a pair of cosets is the multiple of its value",
				Statement{
					Binders: "∀c:A. ∀u:prod(set(B), set(B)).",
					Hypotheses: []string{
						"c ∈ S",
						"u ∈ «waQuotientPairs»",
					},
					Conclusion: "lattice_pair_connecting(V, " +
						"    (quotient_smul(V.add, V.smul, fst(M'), c, fst(u)), " +
						"        quotient_smul(V.add, V.smul, snd(M'), c, snd(u)))) = " +
						"quotient_smul(V.add, V.smul, set_mul(V.add, fst(M'), snd(M')), c, lattice_pair_connecting(V, u))",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[Prod[Set[B], Set[B]]]("u")
					scaled := b.Conjuncts(
						b.Assume(),
						"c is a scalar of S",
						"u is a pair of cosets")
					x, y, uIs := b.Obtain2As[B, B](
						"u is the pair of cosets of some x in M₀ and y in M₁",
						"∃x y:B. "+
							"    x ∈ fst(M) ∧ y ∈ snd(M) ∧ u = (left_coset(V.add, x, fst(M')), left_coset(V.add, y, snd(M')))",
						By(QuotientPairCosets.At(R, A0, A1, V, M, MPrime, u), pair, inside0, inside1, scaled[1]))
					rep := b.Conjuncts(
						uIs,
						"x lies in M₀",
						"y lies in M₁",
						"u is the pair of their cosets")
					cS := proof.MemberOf(c, scaled[0])
					xV := proof.MemberOf(x, b.Have(
						"x is a vector",
						"x ∈ V.carrier",
						By(in0, rep[0])))
					yV := proof.MemberOf(y, b.Have(
						"so is y",
						"y ∈ V.carrier",
						By(in1, rep[1])))
					cx, cy := module.SmulIn.Read(moduleS).At(cS, xV), module.SmulIn.Read(moduleS).At(cS, yV)
					negY := group.InvIn.Read(additive).At(yV)
					difference := group.MulIn.Read(additive).At(xV, negY)
					cR := b.Have(
						"c is a scalar of R",
						"c ∈ R.carrier",
						By(inR, scaled[0]))
					distributes := b.Have(
						"c • (x − y) is c • x − c • y",
						"c • (x + -y) = c • x + -(c • y)",
						ByChase(Depth(0), moduleR, cR, xV, yV))
					b.Show(
						"δ(c • u) and c • δ(u) are computed on the representatives",
						rep[2].Rw(),
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("left_coset(V.add, c • x + -(c • y), set_mul(V.add, fst(M'), snd(M')))"),
								"c • u is the pair of cosets of c • x and c • y, and δ of it the class of their difference",
								By(
									classMultiple.At(fstMPrime, cS, xV),
									classMultiple.At(sndMPrime, cS, yV),
									chart0Prime,
									chart1Prime,
									ConnectingOfCosets.Read(moduleS).At(fstMPrime, sndMPrime, cx, cy),
									subgroup0,
									subgroup1)),
							Leg(
								b.TermAs[Set[B]]("left_coset(V.add, c • (x + -y), set_mul(V.add, fst(M'), snd(M')))"),
								"c distributes over x − y",
								distributes.RwRev(),
								Basic()),
							FinalLeg(
								"c times the class of x − y, which is δ(u)",
								By(
									ConnectingOfCosets.Read(moduleS).At(fstMPrime, sndMPrime, xV, yV),
									subgroup0,
									subgroup1,
									classMultiple.At(subSum, cS, difference),
									subSumS)),
						))
				}))
			linear := a.Have(
				"so δ is an S-linear map of Q₀ × Q₁ to the ambient of M modulo M'₀ + M'₁",
				"module_homomorphism(restrict_ring(R, S), "+
					"    product_module(«waQ0», «waQ1»), "+
					"    «waAmbientModSubSum», "+
					"    lattice_pair_connecting(V))",
				By(module_homomorphism.ModuleHomomorphismDef, product, target, into, adds, scales))
			a.Show(
				"Q₀ and Q₁ are S-modules, and δ is S-linear",
				By(quotient0, quotient1, linear))
		}),
})}

// QuotientDifferenceLinear — over any subring S of both charts the chart
// quotients Q₀ and Q₁ of a sub-pair are S-modules, and c̄ is an S-linear
// map of Q₀ × Q₁ to Q₀₁: c̄ is δ, S-linear into the ambient of M modulo
// M'₀ + M'₁ (ConnectingLinear), followed by enlarging a class by the
// ambient of M', an S-linear map of that quotient to Q₀₁
// (module_homomorphism.QuotientInclusionHom).
var QuotientDifferenceLinear = quotientDifferenceLinearThm{family.Add(registry.ProofEntry{
	Name: "QuotientDifferenceLinear",
	Key:  "prop_960f5d505bc6ea8c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
		},
		Conclusion: "module_on(restrict_ring(R, S), " +
			"    quotient_module(restrict_module(V, fst(M)), fst(M'))) ∧ " +
			"module_on(restrict_ring(R, S), quotient_module(restrict_module(V, snd(M)), snd(M'))) ∧ " +
			"module_homomorphism(restrict_ring(R, S), " +
			"    product_module(quotient_module(restrict_module(V, fst(M)), fst(M')), " +
			"        quotient_module(restrict_module(V, snd(M)), snd(M'))), " +
			"    quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"        lattice_pair_ambient(R, V, M')), " +
			"    lattice_pair_quotient_difference(R, V, M'))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"S is a subring of R",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁")
			subPair, inside0, inside1 := hypotheses[5], hypotheses[6], hypotheses[7]
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			amb, ambPrime :=
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"),
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M')")
			subSum := a.TermAs[Set[B]]("set_mul(V.add, fst(M'), snd(M'))")
			connecting := a.Conjuncts(
				a.Have(
					"Q₀ and Q₁ are S-modules, and δ is an S-linear map of Q₀ × Q₁ to the ambient of M modulo M'₀ + M'₁",
					"module_on(restrict_ring(R, S), «waQ0») ∧ "+
						"module_on(restrict_ring(R, S), «waQ1») ∧ "+
						"module_homomorphism(restrict_ring(R, S), "+
						"    product_module(«waQ0», «waQ1»), "+
						"    «waAmbientModSubSum», "+
						"    lattice_pair_connecting(V))",
					By(ConnectingLinear.At(R, A0, A1, t, s, S, V, M, MPrime), given)),
				"Q₀ is an S-module",
				"so is Q₁",
				"δ is S-linear")

			// Enlarging a class by the ambient of M' is S-linear.
			subSumIn := a.Have(
				"M'₀ + M'₁ lies in the ambient of M'",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ lattice_pair_ambient(R, V, M')",
				By(lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, MPrime), subPair))
			ambIn := a.Have(
				"which lies in that of M",
				"lattice_pair_ambient(R, V, M') ⊆ lattice_pair_ambient(R, V, M)",
				By(lattice_pair.SubpairInclusions.At(R, V, M, MPrime), inside0, inside1))
			subSumInAmb := a.Have(
				"so M'₀ + M'₁ lies in the ambient of M",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ lattice_pair_ambient(R, V, M)",
				By(set_order.SubsetTrans.At(subSum, ambPrime, amb), subSumIn, ambIn))
			enlarge := a.Have(
				"enlarging a class by the ambient of M' is S-linear from the ambient of M modulo M'₀ + M'₁ to Q₀₁",
				"module_homomorphism(restrict_ring(R, S), "+
					"    «waAmbientModSubSum», "+
					"    «waQ01», "+
					"    λx:set(B). set_mul(V.add, x, lattice_pair_ambient(R, V, M')))",
				By(
					module_homomorphism.QuotientInclusionHom.At(ringS, V, amb, amb, subSum, ambPrime),
					lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, M),
					given,
					lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, MPrime),
					subSumInAmb,
					ambIn,
					set_order.SubsetRefl.At(amb),
					subSumIn))

			// c̄ is δ followed by that enlargement.
			connectingMap := a.TermAs[Fun[Prod[Set[B], Set[B]], Set[B]]]("lattice_pair_connecting(V)")
			enlargeMap := a.TermAs[Fun[Set[B], Set[B]]](
				"λx:set(B). set_mul(V.add, x, lattice_pair_ambient(R, V, M'))")
			difference := a.Have(
				"so c̄, δ followed by that enlargement, is S-linear on Q₀ × Q₁",
				"module_homomorphism(restrict_ring(R, S), "+
					"    product_module(«waQ0», «waQ1»), "+
					"    «waQ01», "+
					"    lattice_pair_quotient_difference(R, V, M'))",
				Unfold(latticePairQuotientDifferenceDef),
				By(
					connecting[2],
					enlarge,
					module_homomorphism.HomCompose.At(
						ringS,
						a.TermAs[ModuleOps[A, Prod[Set[B], Set[B]]]]("product_module(«waQ0», «waQ1»)"),
						a.TermAs[ModuleOps[A, Set[B]]]("«waAmbientModSubSum»"),
						a.TermAs[ModuleOps[A, Set[B]]]("«waQ01»"),
						connectingMap,
						enlargeMap),
					functions.ComposeApply.At(enlargeMap, connectingMap)))
			a.Show(
				"Q₀ and Q₁ are S-modules, and c̄ is S-linear",
				By(connecting[0], connecting[1], difference))
		}),
})}

// QuotientDifferenceOnto — with M₀/M'₀ finite-dimensional over k, every class
// of Q₀₁ is c̄ of a pair of classes. lattice_pair.QuotientLocalizes writes a
// member v of ambient(M) as m + w with m ∈ M₀ and w ∈ ambient(M'), and c̄(m +
// M'₀, 0 + M'₁) is (m − 0) + ambient(M'), the class of v, since v and m − 0
// differ by w.
var QuotientDifferenceOnto = quotientDifferenceOntoThm{family.Add(registry.ProofEntry{
	Name: "QuotientDifferenceOnto",
	Key:  "prop_10f50fcdd2e28e3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
			"finite_dimensional(restrict_ring(R, k), quotient_module(restrict_module(V, fst(M)), fst(M')))",
		},
		Conclusion: "left_cosets(V.add, lattice_pair_ambient(R, V, M), lattice_pair_ambient(R, V, M')) ⊆ " +
			"image(lattice_pair_quotient_difference(R, V, M'), " +
			"    set_cross(left_cosets(V.add, fst(M), fst(M')), left_cosets(V.add, snd(M), snd(M'))))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0",
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁",
				"M₀/M'₀ is finite over k")
			datum, subfieldK, kIn0, pair, subPair :=
				hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3], hypotheses[4]
			inside0, inside1, finite0 := hypotheses[5], hypotheses[6], hypotheses[7]
			pairM := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is an R-module",
				"M₀ is an A₀-submodule of V",
				"M₁ is an A₁-submodule of V",
				"M₀ and M₁ span one submodule")
			vectors := pairM[0]
			additive := module.AddGroupOn.Read(vectors)
			chartPrime0 := a.Have(
				"M'₀ is an A₀-submodule of V",
				"submodule(restrict_ring(R, A₀), V, fst(M'))",
				By(a.Unfolded(subPair, lattice_pair.LatticePairDef)))
			ambientM := a.Have(
				"the ambient of M is an R-submodule of V",
				"submodule(R, V, lattice_pair_ambient(R, V, M))",
				By(lattice_pair.AmbientContains.At(R, A0, A1, V, M), pair))
			ambientMPrime := a.Have(
				"so is the ambient of M'",
				"submodule(R, V, lattice_pair_ambient(R, V, M'))",
				By(lattice_pair.AmbientContains.At(R, A0, A1, V, MPrime), subPair))
			below := a.Have(
				"the ambient of M' lies in that of M",
				"lattice_pair_ambient(R, V, M') ⊆ lattice_pair_ambient(R, V, M)",
				By(lattice_pair.SubpairInclusions.At(R, V, M, MPrime), inside0, inside1))
			localizes := a.Have(
				"the ambient of M is M₀ plus the ambient of M', M₀/M'₀ being finite over k",
				"lattice_pair_ambient(R, V, M) = set_mul(V.add, fst(M), lattice_pair_ambient(R, V, M'))",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				By(
					lattice_pair.QuotientLocalizes.At(
						R, A0, A1, t, s, k, inv, V, a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("fst(M')")),
					datum,
					subfieldK,
					kIn0,
					vectors,
					pairM[1],
					chartPrime0,
					inside0,
					finite0))
			// M₀, M₁ and the ambient of M are groups under V's addition, their
			// cosets the classes of the quotients.
			group0 := a.Have(
				"M₀ is a group under V's addition",
				"group_on(restrict_group(module_additive_group(V), fst(M)))",
				By(
					group.SubgroupGroupOn.Read(additive).At(a.TermAs[Set[B]]("fst(M)")),
					submodule.SubmoduleSubgroup.Read(pairM[1])))
			group1 := a.Have(
				"so is M₁",
				"group_on(restrict_group(module_additive_group(V), snd(M)))",
				By(
					group.SubgroupGroupOn.Read(additive).At(a.TermAs[Set[B]]("snd(M)")),
					submodule.SubmoduleSubgroup.Read(pairM[2])))
			groupAmbient := a.Have(
				"and the ambient of M",
				"group_on(restrict_group(module_additive_group(V), lattice_pair_ambient(R, V, M)))",
				By(
					group.SubgroupGroupOn.Read(additive).At(a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)")),
					submodule.SubmoduleSubgroup.Read(ambientM)))
			inM0 := a.Unfolded(submodule.SubmoduleSubset.Read(pairM[1]).AsFact(), set_basic.SubsetDef)
			ambientInV := a.Unfolded(
				submodule.SubmoduleSubset.Read(ambientMPrime).AsFact(), set_basic.SubsetDef)
			a.Show(
				"every class of Q₀₁ is c̄ of a pair of classes",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					b.FixAs[Set[B]]("X")
					_, class := b.ObtainAs[B](
						"X is the coset of some v in the ambient of M",
						"∃v:B. "+
							"    X = left_coset(V.add, v, lattice_pair_ambient(R, V, M')) ∧ v ∈ lattice_pair_ambient(R, V, M)",
						By(quotient_group.InLeftCosets.Read(groupAmbient), below, b.Assume()))
					classParts := b.Conjuncts(
						class,
						"X is the coset of v",
						"v lies in the ambient of M")
					split := b.Have(
						"so v lies in M₀ plus the ambient of M'",
						"v ∈ set_mul(V.add, fst(M), lattice_pair_ambient(R, V, M'))",
						By(localizes, classParts[1]))
					m, _, sum := b.Unpack2As[B, B](b.Simplified(split, Fwd(quotient_group.InSetMul)), "m", "w")
					pieces := b.Conjuncts(
						sum,
						"m lies in M₀",
						"w lies in the ambient of M'",
						"v is m + w")
					mV := b.Have(
						"m is a vector",
						"m ∈ V.carrier",
						By(inM0, pieces[0]))
					wV := b.Have(
						"so is w",
						"w ∈ V.carrier",
						By(ambientInV, pieces[1]))
					zeroV := b.Have(
						"and the zero vector",
						"V.zero ∈ V.carrier",
						By(group.OneIn.Read(additive)))
					pair := b.TermAs[Prod[Set[B], Set[B]]](
						"(left_coset(V.add, m, fst(M')), left_coset(V.add, V.zero, snd(M')))")
					class0 := b.Have(
						"the coset of m is a class of Q₀",
						"left_coset(V.add, m, fst(M')) ∈ left_cosets(V.add, fst(M), fst(M'))",
						Simp(Fwd(quotient_group.InLeftCosets.Read(group0))),
						Witness(m),
						By(pieces[0]))
					class1 := b.Have(
						"the coset of the zero vector is a class of Q₁",
						"left_coset(V.add, V.zero, snd(M')) ∈ left_cosets(V.add, snd(M), snd(M'))",
						Simp(Fwd(quotient_group.InLeftCosets.Read(group1))),
						Witness(b.TermAs[B]("V.zero")),
						By(submodule.SubmoduleZero.Read(pairM[2])))
					classes := b.Have(
						"so the two cosets make a point of Q₀ × Q₁",
						"(left_coset(V.add, m, fst(M')), left_coset(V.add, V.zero, snd(M'))) ∈ «waQuotientPairs»",
						By(set_product.InCross, class0, class1))
					gap := b.Have(
						"v differs from m − 0 by w",
						"-(m + -V.zero) + v = w",
						ByChase(Depth(0), vectors, mV, wV, pieces[2]))
					same := b.Have(
						"so the coset of m − 0 is the coset of v",
						"left_coset(V.add, m + -V.zero, lattice_pair_ambient(R, V, M')) = "+
							"left_coset(V.add, v, lattice_pair_ambient(R, V, M'))",
						By(
							group.LeftCosetEqOn.Read(additive),
							submodule.SubmoduleSubgroup.Read(ambientMPrime),
							gap,
							pieces[1],
							pieces[2],
							mV,
							wV,
							zeroV,
							group.MulIn.Read(additive),
							group.InvIn.Read(additive)))
					b.Do(Simp(Fwd(set_basic.InImage)))
					b.Take(pair)
					b.Show(
						"X is the coset of v, which is c̄ at the pair of cosets of m and 0",
						By(
							classParts[0],
							same,
							QuotientDifferenceCoset.At(R, A0, A1, V, MPrime, m, b.TermAs[B]("V.zero")),
							subPair,
							mV,
							zeroV,
							classes))
				}))
		}),
})}

// PairDifferenceQuotient — for a sub-pair with finite-dimensional chart
// quotients, c̄ is a k-linear map of Q₀ × Q₁ onto Q₀₁, and ker c̄ and Q₀₁
// together have the dimension of Q₀ and Q₁ together. c̄ is k-linear by
// QuotientDifferenceLinear at the subring k and onto by QuotientDifferenceOnto;
// Q₀₁ is finite by lattice_pair.QuotientDimLocalizes, and rank–nullity at c̄ on
// the finite product Q₀ × Q₁, whose dimension is dim Q₀ + dim Q₁, gives the
// sum, ker c̄ being a submodule of the product.
var PairDifferenceQuotient = pairDifferenceQuotientThm{family.Add(registry.ProofEntry{
	Name: "PairDifferenceQuotient",
	Key:  "prop_a5bf4fc620f2213f",
	Reading: "Onto needs only Q₀ finite (QuotientDifferenceOnto); Q₁ finite is what makes ker " +
		"c̄ finite. The dimensions are stated as a sum, so that no difference of numbers is asked.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
			"finite_dimensional(restrict_ring(R, k), quotient_module(restrict_module(V, fst(M)), fst(M')))",
			"finite_dimensional(restrict_ring(R, k), quotient_module(restrict_module(V, snd(M)), snd(M')))",
		},
		Conclusion: "module_homomorphism(restrict_ring(R, k), " +
			"    product_module(quotient_module(restrict_module(V, fst(M)), fst(M')), " +
			"        quotient_module(restrict_module(V, snd(M)), snd(M'))), " +
			"    quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"        lattice_pair_ambient(R, V, M')), " +
			"    lattice_pair_quotient_difference(R, V, M')) ∧ " +
			"image(lattice_pair_quotient_difference(R, V, M'), " +
			"    set_cross(left_cosets(V.add, fst(M), fst(M')), left_cosets(V.add, snd(M), snd(M')))) = " +
			"left_cosets(V.add, lattice_pair_ambient(R, V, M), lattice_pair_ambient(R, V, M')) ∧ " +
			"finite_dimensional(restrict_ring(R, k), lattice_pair_quotient_kernel(R, V, M, M')) ∧ " +
			"finite_dimensional(restrict_ring(R, k), " +
			"    quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"        lattice_pair_ambient(R, V, M'))) ∧ " +
			"module_dim(restrict_ring(R, k), lattice_pair_quotient_kernel(R, V, M, M')) + " +
			"module_dim(restrict_ring(R, k), " +
			"    quotient_module(restrict_module(V, lattice_pair_ambient(R, V, M)), " +
			"        lattice_pair_ambient(R, V, M'))) = " +
			"module_dim(restrict_ring(R, k), quotient_module(restrict_module(V, fst(M)), fst(M'))) + " +
			"module_dim(restrict_ring(R, k), quotient_module(restrict_module(V, snd(M)), snd(M')))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0",
				"and in chart 1",
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁",
				"M₀/M'₀ is finite over k",
				"M₁/M'₁ is finite over k")
			datum, subfieldK, kIn0, kIn1, pair, subPair :=
				hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3], hypotheses[4], hypotheses[5]
			inside0, inside1, finite0, finite1 := hypotheses[6], hypotheses[7], hypotheses[8], hypotheses[9]
			// k is a field under the operations of R restricted to it: the scalar
			// field the dimension laws below are read at.
			fieldK := a.Have(
				"k is a field under the operations of R restricted to k, which are R's",
				"ring_subfield(restrict_ring(R, k), inv, k)",
				By(subfieldK, field.RingSubfieldRestrict.At(R, k, inv, k)))
			scalars := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			quotient0 := a.TermAs[ModuleOps[A, Set[B]]]("«waQ0»")
			quotient1 := a.TermAs[ModuleOps[A, Set[B]]]("«waQ1»")
			overlap := a.TermAs[ModuleOps[A, Set[B]]]("«waQ01»")
			product := a.TermAs[ModuleOps[A, Prod[Set[B], Set[B]]]]("product_module(«waQ0», «waQ1»)")
			difference := a.TermAs[Fun[Prod[Set[B], Set[B]], Set[B]]](
				"lattice_pair_quotient_difference(R, V, M')")
			subringK := a.Have(
				"k is a subring of R",
				"subring(R, k)",
				By(lattice_pair.ChartFieldSubring.At(R, A0, A1, t, s, k, inv), datum, subfieldK, kIn0))
			linear := a.Conjuncts(
				a.Have(
					"over k, Q₀ and Q₁ are modules and c̄ is a k-linear map of Q₀ × Q₁ to Q₀₁",
					"module_on(restrict_ring(R, k), «waQ0») ∧ "+
						"module_on(restrict_ring(R, k), «waQ1») ∧ "+
						"module_homomorphism(restrict_ring(R, k), "+
						"    product_module(«waQ0», «waQ1»), "+
						"    «waQ01», "+
						"    lattice_pair_quotient_difference(R, V, M'))",
					By(
						QuotientDifferenceLinear.At(R, A0, A1, t, s, k, V, M, MPrime),
						datum,
						subringK,
						kIn0,
						kIn1,
						pair,
						subPair,
						inside0,
						inside1)),
				"Q₀ is a k-module",
				"so is Q₁",
				"c̄ is k-linear")
			hom := linear[2]
			into := a.Have(
				"c̄ maps Q₀ × Q₁ into Q₀₁",
				"image(lattice_pair_quotient_difference(R, V, M'), «waQuotientPairs») ⊆ «waQ01Carrier»",
				Simp(Fwd(set_image.ImageSubsetIff)),
				By(module_homomorphism.HomIn.Read(hom)))
			reached := a.Have(
				"every class of Q₀₁ is c̄ of a pair of classes, M₀/M'₀ being finite",
				"«waQ01Carrier» ⊆ image(lattice_pair_quotient_difference(R, V, M'), «waQuotientPairs»)",
				By(
					QuotientDifferenceOnto.At(R, A0, A1, t, s, k, inv, V, M, MPrime),
					datum,
					subfieldK,
					kIn0,
					pair,
					subPair,
					inside0,
					inside1,
					finite0))
			onto := a.Have(
				"so c̄ is onto Q₀₁",
				"image(lattice_pair_quotient_difference(R, V, M'), «waQuotientPairs») = «waQ01Carrier»",
				By(set_order.SubsetAntisym, into, reached))
			productDims := a.Conjuncts(
				a.Have(
					"Q₀ × Q₁ is finite over k, of dimension dim Q₀ + dim Q₁",
					"«waFinite»(product_module(«waQ0», «waQ1»)) ∧ "+
						"«waDim»(product_module(«waQ0», «waQ1»)) = «waDim»(«waQ0») + «waDim»(«waQ1»)",
					By(
						module_dimension.DimProduct.At(scalars, quotient0, inv, quotient1),
						linear[0],
						fieldK,
						linear[1],
						finite0,
						finite1)),
				"Q₀ × Q₁ is finite over k",
				"of dimension dim Q₀ + dim Q₁")
			source := a.Have(
				"Q₀ × Q₁ is a k-module",
				"module_on(restrict_ring(R, k), product_module(«waQ0», «waQ1»))",
				By(module_homomorphism.HomSource.Read(hom)))
			kernelFinite := a.Have(
				"ker c̄ is finite over k, a submodule of the finite Q₀ × Q₁",
				"«waFinite»(«waKernelModule»)",
				Simp(Fwd(LatticePairQuotientKernelDef)),
				By(
					module_dimension.SubmoduleDim.At(
						scalars,
						product,
						inv,
						a.TermAs[Set[Prod[Set[B], Set[B]]]](
							"group_kernel(lattice_pair_ambient(R, V, M'), "+
								"    «waQuotientPairs», "+
								"    lattice_pair_quotient_difference(R, V, M'))")),
					source,
					fieldK,
					productDims[0],
					module_homomorphism.KernelSubmodule.At(scalars, product, overlap, difference),
					hom))
			overlapFinite := a.Have(
				"Q₀₁ is finite over k, M₀/M'₀ being finite",
				"«waFinite»(«waQ01»)",
				Simp(Fwd(lattice_pair.LatticePairAmbientDef)),
				By(
					lattice_pair.QuotientDimLocalizes.At(
						R, A0, A1, t, s, k, inv, V, a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("fst(M')")),
					datum,
					subfieldK,
					kIn0,
					a.Unfolded(pair, lattice_pair.LatticePairDef),
					a.Unfolded(subPair, lattice_pair.LatticePairDef),
					inside0,
					finite0))
			rankNullity := a.Have(
				"rank-nullity at c̄: dim ker c̄ + dim of its image = dim Q₀ × Q₁",
				"«waDim»(«waKernelModule») + "+
					"«waDim»(restrict_module(«waQ01», "+
					"        image(lattice_pair_quotient_difference(R, V, M'), «waQuotientPairs»))) = "+
					"«waDim»(product_module(«waQ0», «waQ1»))",
				Simp(Fwd(LatticePairQuotientKernelDef)),
				By(
					module_dimension.RankNullity.At(scalars, product, inv, overlap, difference),
					source,
					fieldK,
					module_homomorphism.HomTarget.Read(hom),
					hom,
					productDims[0]))
			dims := a.Have(
				"the image is Q₀₁, so dim ker c̄ + dim Q₀₁ = dim Q₀ + dim Q₁",
				"«waDim»(«waKernelModule») + «waDim»(«waQ01») = «waDim»(«waQ0») + «waDim»(«waQ1»)",
				By(rankNullity, onto, module_record.RestrictModuleCarrier.At(overlap), productDims[1]))
			a.Show(
				"c̄ is k-linear onto Q₀₁, ker c̄ and Q₀₁ are finite, "+
					"and their dimensions add up to those of Q₀ and Q₁",
				By(hom, onto, kernelFinite, overlapFinite, dims))
		}),
})}

// SixTermMaps — the maps of the six-term sequence of a sub-pair, H⁰(M') ⊆
// H⁰(M), v ↦ (v + M'₀, v + M'₁) into ker c̄, the connecting map δ into H¹(M')
// and X ↦ X + (M₀ + M₁) into H¹(M), are homomorphisms over any subring S of
// both charts. Every module in sight is one over S
// (lattice_pair.PairOverSubring); the inclusion restricts the identity and the
// last map is induced by the inclusions of the ambients and the sums
// (module_homomorphism.QuotientInclusionHom); ker c̄ is a submodule as the
// kernel of the S-linear c̄ (QuotientDifferenceLinear), and v ↦ (v + M'₀, v +
// M'₁) lands in it, c̄ sending the pair to the class of v − v; δ is S-linear on
// Q₀ × Q₁ (ConnectingLinear), and on ker c̄ it lands in H¹(M'), c̄ killing (x +
// M'₀, y + M'₁) exactly when x − y lies in the ambient of M'.
var SixTermMaps = sixTermMapsThm{family.Add(registry.ProofEntry{
	Name: "SixTermMaps",
	Key:  "prop_a3581f9c282397f0",
	Reading: "S ⊆ A₀ ∩ A₁ is load-bearing: M₀ + M₁ and the chart quotients " +
		"are modules over S only; at S = k the four maps are k-linear.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀S:set(A). " +
			"∀V:module_ops(A, B). " +
			"∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"subring(R, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
		},
		Conclusion: "module_homomorphism(restrict_ring(R, S), " +
			"    lattice_pair_h0(V, M'), " +
			"    lattice_pair_h0(V, M), " +
			"    identity_map) ∧ " +
			"module_homomorphism(restrict_ring(R, S), " +
			"    lattice_pair_h0(V, M), " +
			"    lattice_pair_quotient_kernel(R, V, M, M'), " +
			"    λv:B. (left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M')))) ∧ " +
			"module_homomorphism(restrict_ring(R, S), " +
			"    lattice_pair_quotient_kernel(R, V, M, M'), " +
			"    lattice_pair_h1(R, V, M'), " +
			"    lattice_pair_connecting(V)) ∧ " +
			"module_homomorphism(restrict_ring(R, S), " +
			"    lattice_pair_h1(R, V, M'), " +
			"    lattice_pair_h1(R, V, M), " +
			"    λx:set(B). set_mul(V.add, x, set_mul(V.add, fst(M), snd(M))))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			S *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"S is a commutative ring with R's operations",
				"S lies in chart 0",
				"and in chart 1",
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁")
			pair, subPair, inside0, inside1 := hypotheses[4], hypotheses[5], hypotheses[6], hypotheses[7]
			ringS := a.TermAs[RingOps[A]]("restrict_ring(R, S)")
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			fstMPrime, sndMPrime := a.TermAs[Set[B]]("fst(M')"), a.TermAs[Set[B]]("snd(M')")
			amb, ambPrime :=
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"),
				a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M')")
			sum, subSum :=
				a.TermAs[Set[B]]("set_mul(V.add, fst(M), snd(M))"),
				a.TermAs[Set[B]]("set_mul(V.add, fst(M'), snd(M'))")

			overM := a.Conjuncts(
				a.Have(
					"over S, V is a module, and M₀, M₁, M₀ + M₁ and the ambient of M are submodules of it",
					"module_on(restrict_ring(R, S), V) ∧ "+
						"submodule(restrict_ring(R, S), V, fst(M)) ∧ "+
						"submodule(restrict_ring(R, S), V, snd(M)) ∧ "+
						"submodule(restrict_ring(R, S), V, set_mul(V.add, fst(M), snd(M))) ∧ "+
						"submodule(restrict_ring(R, S), V, lattice_pair_ambient(R, V, M))",
					By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, M), given)),
				"V is an S-module",
				"M₀ is an S-submodule of V",
				"so is M₁",
				"so is M₀ + M₁",
				"and the ambient of M")
			moduleS, chart0, chart1, sumS, ambS := overM[0], overM[1], overM[2], overM[3], overM[4]
			chart0Prime := a.Have(
				"so are M'₀",
				"submodule(restrict_ring(R, S), V, fst(M'))",
				By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, MPrime), given))
			chart1Prime := a.Have(
				"M'₁",
				"submodule(restrict_ring(R, S), V, snd(M'))",
				By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, MPrime), given))
			subSumS := a.Have(
				"M'₀ + M'₁",
				"submodule(restrict_ring(R, S), V, set_mul(V.add, fst(M'), snd(M')))",
				By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, MPrime), given))
			ambPrimeS := a.Have(
				"and the ambient of M'",
				"submodule(restrict_ring(R, S), V, lattice_pair_ambient(R, V, M'))",
				By(lattice_pair.PairOverSubring.At(R, A0, A1, t, s, S, V, MPrime), given))
			subSumIn := a.Have(
				"M'₀ + M'₁ lies in the ambient of M'",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ lattice_pair_ambient(R, V, M')",
				By(lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, MPrime), subPair))
			ambIn := a.Have(
				"the ambient of M' lies in that of M",
				"lattice_pair_ambient(R, V, M') ⊆ lattice_pair_ambient(R, V, M)",
				By(lattice_pair.SubpairInclusions.At(R, V, M, MPrime), inside0, inside1))
			subSumInSum := a.Have(
				"M'₀ + M'₁ lies in M₀ + M₁",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ set_mul(V.add, fst(M), snd(M))",
				By(lattice_pair.SubpairInclusions.At(R, V, M, MPrime), inside0, inside1))

			// H¹(M') → H¹(M), u + (M'₀ + M'₁) ↦ u + (M₀ + M₁), is the map of
			// quotients the inclusions of the ambients and of the sums give.
			mapH1 := a.Have(
				"X ↦ X + (M₀ + M₁) is S-linear from H¹(M') to H¹(M)",
				"module_homomorphism(restrict_ring(R, S), "+
					"    lattice_pair_h1(R, V, M'), "+
					"    lattice_pair_h1(R, V, M), "+
					"    «waH1Map»)",
				Unfold(lattice_pair.LatticePairH1Def),
				By(
					module_homomorphism.QuotientInclusionHom.At(ringS, V, ambPrime, amb, subSum, sum),
					moduleS,
					ambPrimeS,
					ambS,
					subSumS,
					sumS,
					subSumIn,
					lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, M),
					pair,
					ambIn,
					subSumInSum))

			// The inclusion H⁰(M') ⊆ H⁰(M) is the identity of V restricted.
			h0Prime := a.Have(
				"H⁰(M') = M'₀ ∩ M'₁ is a submodule over S",
				"submodule(restrict_ring(R, S), V, fst(M') ∩ snd(M'))",
				By(submodule.SubmoduleInter.At(ringS, V, fstMPrime, sndMPrime), chart0Prime, chart1Prime))
			h0 := a.Have(
				"so is H⁰(M) = M₀ ∩ M₁",
				"submodule(restrict_ring(R, S), V, fst(M) ∩ snd(M))",
				By(submodule.SubmoduleInter.At(ringS, V, fstM, sndM), chart0, chart1))
			carried := a.Have(
				"the identity carries H⁰(M') into H⁰(M), M' lying in M",
				"∀u:B. u ∈ fst(M') ∩ snd(M') ⇒ identity_map(u) ∈ fst(M) ∩ snd(M)",
				Simp(Fwd(functions.IdentityApply)),
				BySets(inside0, inside1))
			mapInclusion := a.Have(
				"so its restriction, the inclusion of H⁰(M') in H⁰(M), is S-linear",
				"module_homomorphism(restrict_ring(R, S), "+
					"    lattice_pair_h0(V, M'), "+
					"    lattice_pair_h0(V, M), "+
					"    identity_map)",
				Unfold(lattice_pair.LatticePairH0Def),
				By(
					module_homomorphism.HomRestrict.At(ringS, V, V, a.TermAs[Fun[B, B]]("identity_map"),
						a.TermAs[Set[B]]("fst(M') ∩ snd(M')"), a.TermAs[Set[B]]("fst(M) ∩ snd(M)")),
					module_homomorphism.HomIdentity.At(ringS, V),
					moduleS,
					h0Prime,
					h0,
					carried))

			// c̄ is S-linear, so ker c̄ is an S-submodule of Q₀ × Q₁; δ is S-linear on Q₀ × Q₁.
			difference := a.Have(
				"c̄ is an S-linear map of Q₀ × Q₁ to Q₀₁",
				"module_homomorphism(restrict_ring(R, S), "+
					"    product_module(«waQ0», «waQ1»), "+
					"    «waQ01», "+
					"    lattice_pair_quotient_difference(R, V, M'))",
				By(QuotientDifferenceLinear.At(R, A0, A1, t, s, S, V, M, MPrime), given))
			delta := a.Have(
				"δ is an S-linear map of Q₀ × Q₁ to the ambient of M modulo M'₀ + M'₁",
				"module_homomorphism(restrict_ring(R, S), "+
					"    product_module(«waQ0», «waQ1»), "+
					"    «waAmbientModSubSum», "+
					"    lattice_pair_connecting(V))",
				By(ConnectingLinear.At(R, A0, A1, t, s, S, V, M, MPrime), given))
			moduleKernel := a.Have(
				"so ker c̄ is a module over S",
				"module_on(restrict_ring(R, S), «waKernelModule»)",
				Unfold(LatticePairQuotientKernelDef),
				By(
					submodule.SubmoduleModuleOn.Read(module_homomorphism.HomSource.Read(difference)),
					module_homomorphism.KernelSubmodule.Read(difference)))

			// Classes: M'₀ and M'₁ are normal in V, so the classes of a sum are
			// the sums of the classes, and those of a multiple the multiples.
			additive := module.AddGroupOn.Read(moduleS)
			classSum := quotient_group.LeftCosetMulOn.Read(additive)
			classMultiple := submodule.QuotientSmulCoset.Read(moduleS)
			in0 := a.Unfolded(submodule.SubmoduleSubset.Read(chart0).AsFact(), set_basic.SubsetDef)
			in1 := a.Unfolded(submodule.SubmoduleSubset.Read(chart1).AsFact(), set_basic.SubsetDef)
			moduleM0 := a.Have(
				"M₀ is a module over S",
				"module_on(restrict_ring(R, S), restrict_module(V, fst(M)))",
				By(submodule.SubmoduleModuleOn.Read(moduleS).At(fstM), chart0))
			moduleM1 := a.Have(
				"so is M₁",
				"module_on(restrict_ring(R, S), restrict_module(V, snd(M)))",
				By(submodule.SubmoduleModuleOn.Read(moduleS).At(sndM), chart1))
			moduleAmbPrime := a.Have(
				"and the ambient of M'",
				"module_on(restrict_ring(R, S), restrict_module(V, lattice_pair_ambient(R, V, M')))",
				By(submodule.SubmoduleModuleOn.Read(moduleS).At(ambPrime), ambPrimeS))
			classes0 := a.Have(
				"the class of a member of M₀ is a class of Q₀",
				"∀u:B. u ∈ fst(M) ⇒ left_coset(V.add, u, fst(M')) ∈ left_cosets(V.add, fst(M), fst(M'))",
				Simp(
					Fwd(quotient_group.LeftCosetsImage.Read(module.AddGroupOn.Read(moduleM0))),
					Fwd(group.CosetMapDef)),
				By(set_image.FunInImage))
			classes1 := a.Have(
				"and of a member of M₁ one of Q₁",
				"∀u:B. u ∈ snd(M) ⇒ left_coset(V.add, u, snd(M')) ∈ left_cosets(V.add, snd(M), snd(M'))",
				Simp(
					Fwd(quotient_group.LeftCosetsImage.Read(module.AddGroupOn.Read(moduleM1))),
					Fwd(group.CosetMapDef)),
				By(set_image.FunInImage))
			classesH1 := a.Have(
				"and of a member of the ambient of M' a class of H¹(M')",
				Statement{
					Binders: "∀u:B.",
					Hypotheses: []string{
						"u ∈ lattice_pair_ambient(R, V, M')",
					},
					Conclusion: "left_coset(V.add, u, set_mul(V.add, fst(M'), snd(M'))) ∈ " +
						"left_cosets(V.add, lattice_pair_ambient(R, V, M'), set_mul(V.add, fst(M'), snd(M')))",
				},
				Simp(
					Fwd(quotient_group.LeftCosetsImage.Read(module.AddGroupOn.Read(moduleAmbPrime))),
					Fwd(group.CosetMapDef)),
				By(set_image.FunInImage))

			// v ↦ (v + M'₀, v + M'₁) lands in ker c̄: c̄ of the pair is the class
			// of v − v modulo the ambient of M', the zero class.
			intoKernel := a.Have(
				"the pair of classes of a member of H⁰(M) lies in ker c̄",
				Statement{
					Binders: "∀u:B.",
					Hypotheses: []string{
						"u ∈ fst(M) ∩ snd(M)",
					},
					Conclusion: "(left_coset(V.add, u, fst(M')), left_coset(V.add, u, snd(M'))) ∈ «waKernelPairs»",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[B]("u")
					both := b.Conjuncts(
						b.Have(
							"u lies on both charts",
							"u ∈ fst(M) ∧ u ∈ snd(M)",
							BySets(b.Assume())),
						"u lies in M₀",
						"and in M₁")
					uV := proof.MemberOf(u, b.Have(
						"u is a vector",
						"u ∈ V.carrier",
						By(in0, both[0])))
					zeroClass := b.Have(
						"c̄ sends the pair to (u − u) + ambient(M'), the zero class",
						"lattice_pair_quotient_difference(R, "+
							"    V, "+
							"    M', "+
							"    (left_coset(V.add, u, fst(M')), left_coset(V.add, u, snd(M')))) = "+
							"lattice_pair_ambient(R, V, M')",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("left_coset(V.add, u + -u, lattice_pair_ambient(R, V, M'))"),
								"c̄ of a pair of cosets is the class of the difference",
								By(QuotientDifferenceCoset.At(R, A0, A1, V, MPrime, u, u), subPair, uV)),
							Leg(
								b.TermAs[Set[B]]("left_coset(V.add, V.zero, lattice_pair_ambient(R, V, M'))"),
								"u − u is zero",
								By(Normalized, group.RightInverseOn.Read(additive).At(uV))),
							FinalLeg(
								"the class of zero is the ambient of M' itself",
								By(group.LeftCosetOneOn.Read(additive).At(ambPrime), submodule.SubmoduleSubset.Read(ambPrimeS))),
						))
					classes := b.Have(
						"the pair is a pair of classes",
						"(left_coset(V.add, u, fst(M')), left_coset(V.add, u, snd(M'))) ∈ «waQuotientPairs»",
						By(set_product.InCross, classes0.At(u), classes1.At(u), both[0], both[1]))
					b.Show(
						"a pair of classes c̄ sends to zero lies in its kernel",
						By(group_homomorphism.InKernel, classes, zeroClass))
				}))
			addsToKernel := a.Have(
				"v ↦ (v + M'₀, v + M'₁) keeps sums",
				Statement{
					Binders: "∀u v:B.",
					Hypotheses: []string{
						"u ∈ fst(M) ∩ snd(M)",
						"v ∈ fst(M) ∩ snd(M)",
					},
					Conclusion: "(left_coset(V.add, u + v, fst(M')), left_coset(V.add, u + v, snd(M'))) = " +
						"(set_mul(V.add, left_coset(V.add, u, fst(M')), left_coset(V.add, v, fst(M'))), " +
						"    set_mul(V.add, left_coset(V.add, u, snd(M')), left_coset(V.add, v, snd(M'))))",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[B]("u"), b.FixAs[B]("v")
					inM0 := b.Conjuncts(
						b.Have(
							"u and v lie in M₀",
							"u ∈ fst(M) ∧ v ∈ fst(M)",
							BySets(b.Assume())),
						"u lies in M₀",
						"so does v")
					uV := proof.MemberOf(u, b.Have(
						"u is a vector",
						"u ∈ V.carrier",
						By(in0, inM0[0])))
					vV := proof.MemberOf(v, b.Have(
						"so is v",
						"v ∈ V.carrier",
						By(in0, inM0[1])))
					b.Show(
						"the classes of u + v are the sums of the classes, M'₀ and M'₁ being normal",
						By(
							classSum.AsFact().At(fstMPrime, u, v),
							classSum.AsFact().At(sndMPrime, u, v),
							submodule.SubmoduleNormal.Read(moduleS).At(fstMPrime),
							chart0Prime,
							submodule.SubmoduleNormal.Read(moduleS).At(sndMPrime),
							chart1Prime,
							uV,
							vV))
				}))
			scalesToKernel := a.Have(
				"and multiples",
				Statement{
					Binders: "∀c:A. ∀u:B.",
					Hypotheses: []string{
						"c ∈ S",
						"u ∈ fst(M) ∩ snd(M)",
					},
					Conclusion: "(left_coset(V.add, c • u, fst(M')), left_coset(V.add, c • u, snd(M'))) = " +
						"(quotient_smul(V.add, V.smul, fst(M'), c, left_coset(V.add, u, fst(M'))), " +
						"    quotient_smul(V.add, V.smul, snd(M'), c, left_coset(V.add, u, snd(M'))))",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[B]("u")
					scaled := b.Conjuncts(
						b.Have(
							"c lies in S and u in M₀",
							"c ∈ S ∧ u ∈ fst(M)",
							BySets(b.Assume())),
						"c lies in S",
						"u lies in M₀")
					cS := proof.MemberOf(c, scaled[0])
					uV := proof.MemberOf(u, b.Have(
						"u is a vector",
						"u ∈ V.carrier",
						By(in0, scaled[1])))
					b.Show(
						"the classes of c • u are the multiples of the classes",
						By(
							classMultiple.At(fstMPrime, cS, uV),
							classMultiple.At(sndMPrime, cS, uV),
							chart0Prime,
							chart1Prime))
				}))
			moduleH0 := a.Have(
				"H⁰(M) is a module over S, the target of the inclusion",
				"module_on(restrict_ring(R, S), lattice_pair_h0(V, M))",
				By(module_homomorphism.HomTarget.Read(mapInclusion)))
			toClasses := a.Have(
				"v ↦ (v + M'₀, v + M'₁) is S-linear from H⁰(M) to ker c̄",
				"module_homomorphism(restrict_ring(R, S), "+
					"    lattice_pair_h0(V, M), "+
					"    lattice_pair_quotient_kernel(R, V, M, M'), "+
					"    λv:B.(left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M'))))",
				Unfold(module_homomorphism.ModuleHomomorphismDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(moduleH0, moduleKernel, intoKernel, addsToKernel, scalesToKernel))

			// δ on ker c̄: c̄ kills (x + M'₀, y + M'₁) exactly when x − y lies in
			// the ambient of M', and δ of it, (x − y) + (M'₀ + M'₁), is then a
			// class of H¹(M').
			inKernel := a.Have(
				"a member of ker c̄ is a pair of classes",
				"∀u:prod(set(B), set(B)). u ∈ «waKernelPairs» ⇒ u ∈ «waQuotientPairs»",
				Derive(func(b *Argument) {
					b.FixAs[Prod[Set[B], Set[B]]]("u")
					b.Show(
						"the kernel is cut from the pairs of classes",
						By(b.Simplified(b.Assume(), Fwd(group_homomorphism.InKernel))))
				}))
			intoH1 := a.Have(
				"δ of a member of ker c̄ is a class of H¹(M')",
				Statement{
					Binders: "∀u:prod(set(B), set(B)).",
					Hypotheses: []string{
						"u ∈ «waKernelPairs»",
					},
					Conclusion: "lattice_pair_connecting(V, u) ∈ " +
						"left_cosets(V.add, lattice_pair_ambient(R, V, M'), set_mul(V.add, fst(M'), snd(M')))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[Prod[Set[B], Set[B]]]("u")
					killed := b.Conjuncts(
						b.Simplified(b.Assume(), Fwd(group_homomorphism.InKernel)),
						"u is a pair of classes",
						"c̄ kills u")
					x, y, uIs := b.Obtain2As[B, B](
						"u is the pair of cosets of some x in M₀ and y in M₁",
						"∃x y:B. "+
							"    x ∈ fst(M) ∧ y ∈ snd(M) ∧ u = (left_coset(V.add, x, fst(M')), left_coset(V.add, y, snd(M')))",
						By(QuotientPairCosets.At(R, A0, A1, V, M, MPrime, u), pair, inside0, inside1, killed[0]))
					rep := b.Conjuncts(
						uIs,
						"x lies in M₀",
						"y lies in M₁",
						"u is the pair of their cosets")
					xV := proof.MemberOf(x, b.Have(
						"x is a vector",
						"x ∈ V.carrier",
						By(in0, rep[0])))
					yV := proof.MemberOf(y, b.Have(
						"so is y",
						"y ∈ V.carrier",
						By(in1, rep[1])))
					difference := group.MulIn.Read(additive).At(xV, group.InvIn.Read(additive).At(yV))
					quotient := b.Have(
						"c̄(u) is the class of x − y modulo the ambient of M'",
						"lattice_pair_quotient_difference(R, V, M', u) = "+
							"left_coset(V.add, x + -y, lattice_pair_ambient(R, V, M'))",
						rep[2].Rw(),
						By(QuotientDifferenceCoset.At(R, A0, A1, V, MPrime, x, y), subPair, xV, yV))
					inAmbPrime := b.Have(
						"so x − y lies in the ambient of M', its class being the zero class c̄(u)",
						"x + -y ∈ lattice_pair_ambient(R, V, M')",
						By(
							quotient_group.LeftCosetIsSubgroupIffIn.Read(additive).At(difference, ambPrime),
							submodule.SubmoduleSubgroup.Read(ambPrimeS),
							quotient,
							killed[1]))
					value := b.Have(
						"δ(u) is the class of x − y modulo M'₀ + M'₁",
						"lattice_pair_connecting(V, u) = left_coset(V.add, x + -y, set_mul(V.add, fst(M'), snd(M')))",
						rep[2].Rw(),
						By(
							ConnectingOfCosets.Read(moduleS).AsFact().At(fstMPrime, sndMPrime, x, y),
							submodule.SubmoduleSubgroup.Read(chart0Prime),
							submodule.SubmoduleSubgroup.Read(chart1Prime),
							xV,
							yV))
					b.Show(
						"δ(u), the class of x − y, is a class of H¹(M')",
						value.Rw(),
						By(classesH1.At(b.TermAs[B]("x + -y")), inAmbPrime))
				}))
			connectingMap := a.Have(
				"so δ, S-linear on Q₀ × Q₁, is S-linear from ker c̄ to H¹(M')",
				"module_homomorphism(restrict_ring(R, S), "+
					"    «waKernelModule», "+
					"    lattice_pair_h1(R, V, M'), "+
					"    lattice_pair_connecting(V))",
				By(
					module_homomorphism.ModuleHomomorphismDef,
					moduleKernel,
					module_homomorphism.HomSource.Read(mapH1),
					intoH1,
					module_homomorphism.HomAdd.Read(delta),
					module_homomorphism.HomSmul.Read(delta),
					inKernel))

			a.Show(
				"the four maps of the sequence are S-linear",
				By(mapInclusion, toClasses, connectingMap, mapH1))
		}),
})}

// SixTermH0Exact — the six-term sequence of a sub-pair is exact at H⁰(M):
// the members of H⁰(M) whose classes vanish in both chart quotients are
// H⁰(M').
var SixTermH0Exact = sixTermH0ExactThm{family.Add(registry.ProofEntry{
	Name:    "SixTermH0Exact",
	Key:     "prop_a5c8d6d1e09b6944",
	Reading: "The sequence starts with the inclusion H⁰(M') ⊆ H⁰(M), one-to-one as an inclusion.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
		},
		Conclusion: "exact_at(«waKernelModule».zero, " +
			"    lattice_pair_h0(V, M').carrier, " +
			"    lattice_pair_h0(V, M).carrier, " +
			"    identity_map, " +
			"    «waToClasses»)",
		Abbrev: Abbrev{
			{Name: "waToClasses", Text: "λv:B. (left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M')))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"M is a lattice pair",
				"M' is a lattice pair",
				"M'₀ lies in M₀",
				"and M'₁ lies in M₁")
			pair, subPair, inside0, inside1 := hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3]
			charts := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is an R-module",
				"M₀ is an A₀-submodule of V",
				"M₁ is an A₁-submodule of V",
				"the charts of M span one R-submodule")
			chartsPrime := a.Unfolded(subPair, lattice_pair.LatticePairDef)
			chart0Prime := a.Have(
				"M'₀ is an A₀-submodule of V",
				"submodule(restrict_ring(R, A₀), V, fst(M'))",
				By(chartsPrime))
			chart1Prime := a.Have(
				"and M'₁ an A₁-submodule",
				"submodule(restrict_ring(R, A₁), V, snd(M'))",
				By(chartsPrime))
			additive := module.AddGroupOn.Read(charts[0])
			zero := a.Have(
				"zero in ker c̄ is the pair of zero classes",
				"«waKernelModule».zero = (fst(M'), snd(M'))",
				Simp(
					Fwd(LatticePairQuotientKernelDef),
					Fwd(module_record.RestrictModuleDef),
					Fwd(module_record.ProductModuleDef),
					Fwd(submodule.QuotientModuleDef)),
				Refl())
			vanishes0 := a.Have(
				"the first coset vanishes exactly on M'₀, a subgroup of V",
				"∀v:B. v ∈ V.carrier ⇒ (left_coset(V.add, v, fst(M')) = fst(M') ⇔ v ∈ fst(M'))",
				By(
					quotient_group.LeftCosetIsSubgroupIffIn.Read(additive),
					submodule.SubmoduleSubgroup.Read(chart0Prime)))
			vanishes1 := a.Have(
				"the second coset vanishes exactly on M'₁, a subgroup of V",
				"∀v:B. v ∈ V.carrier ⇒ (left_coset(V.add, v, snd(M')) = snd(M') ⇔ v ∈ snd(M'))",
				By(
					quotient_group.LeftCosetIsSubgroupIffIn.Read(additive),
					submodule.SubmoduleSubgroup.Read(chart1Prime)))
			vanishes := a.Have(
				"both cosets vanish exactly on H⁰(M')",
				Statement{
					Binders:    "∀v:B.",
					Hypotheses: []string{"v ∈ V.carrier"},
					Conclusion: "(left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M'))) = " +
						"«waKernelModule».zero ⇔ " +
						"v ∈ lattice_pair_h0(V, M').carrier",
				},
				Derive(func(b *Argument) {
					b.FixAs[B]("v")
					b.Assume()
					b.Show(
						"the two vanishing conditions say that v lies on both primed charts",
						Simp(
							Fwd(zero),
							Fwd(vanishes0),
							Fwd(vanishes1),
							Fwd(lattice_pair.LatticePairH0Def),
							Fwd(module_record.RestrictModuleDef),
							Fwd(pairs.PairEq),
							Fwd(set_basic.InInter)),
						Basic())
				}))
			intersections := a.Have(
				"H⁰(M'), the intersection of the primed charts, lies "+
					"in H⁰(M), that of the charts of M, which lies in V",
				"fst(M') ∩ snd(M') ⊆ fst(M) ∩ snd(M) ∧ fst(M) ∩ snd(M) ⊆ V.carrier",
				BySets(inside0, submodule.SubmoduleSubset.Read(charts[1]), inside1))
			kernel := a.Have(
				"the kernel of the section-to-classes map is H⁰(M')",
				"group_kernel(«waKernelModule».zero, lattice_pair_h0(V, M).carrier, «waToClasses») = "+
					"lattice_pair_h0(V, M').carrier",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					b.Show(
						"among sections of M, precisely the sections of M' have zero classes",
						Simp(Fwd(group_homomorphism.InKernel)),
						BySets(vanishes.At(v), intersections))
				}))
			inclusionImage := a.Have(
				"the inclusion has image H⁰(M')",
				"image(identity_map, lattice_pair_h0(V, M').carrier) = lattice_pair_h0(V, M').carrier",
				Simp(Fwd(functions.IdentityApply), Fwd(set_image.ImageIdentity)),
				Refl())
			a.Show(
				"the inclusion image equals the kernel",
				By(inclusionImage, kernel, module_homomorphism.ExactAtDef))
		}),
})}

// ConnectingKernel — the six-term sequence of a sub-pair is exact at
// ker c̄: the classes δ sends to zero are those of the members of H⁰(M).
// The classes of a section v are sent by δ to (v − v) + (M'₀ + M'₁), the
// zero of H¹(M'), and by c̄ to (v − v) + ambient(M') (QuotientDifferenceCoset),
// the zero of Q₀₁; a pair (m₀ + M'₀, m₁ + M'₁) that δ kills has
// m₀ − m₁ = p₀ + p₁ with p₀ in M'₀ and p₁ in M'₁, and is the pair of
// classes of the section m₀ − p₀ = m₁ + p₁.
var ConnectingKernel = connectingKernelThm{family.Add(registry.ProofEntry{
	Name: "ConnectingKernel",
	Key:  "prop_6c06c0215e8251db",
	Reading: "The zero of H¹(M') is M'₀ + M'₁. M' inside M is load-bearing: the section " +
		"m₀ − p₀ = m₁ + p₁ lies on both charts of M only because p₀ ∈ M₀ and p₁ ∈ M₁.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
		},
		Conclusion: "exact_at(lattice_pair_h1(R, V, M').zero, " +
			"    lattice_pair_h0(V, M).carrier, " +
			"    lattice_pair_quotient_kernel(R, V, M, M').carrier, " +
			"    λv:B. (left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M'))), " +
			"    lattice_pair_connecting(V))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁")
			pair, subPair, inside0, inside1 := parts[0], parts[1], parts[2], parts[3]
			charts := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is an R-module",
				"M₀ is an A₀-submodule of V",
				"M₁ is an A₁-submodule of V",
				"M₀ and M₁ span one R-submodule")
			moduleV, chart0, chart1 := charts[0], charts[1], charts[2]
			chartsPrime := a.Unfolded(subPair, lattice_pair.LatticePairDef)
			chart0Prime := a.Have(
				"M'₀ is an A₀-submodule of V",
				"submodule(restrict_ring(R, A₀), V, fst(M'))",
				By(chartsPrime))
			chart1Prime := a.Have(
				"M'₁ is an A₁-submodule of V",
				"submodule(restrict_ring(R, A₁), V, snd(M'))",
				By(chartsPrime))
			additive := module.AddGroupOn.Read(moduleV)
			fstM, sndM := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			fstMPrime, sndMPrime := a.TermAs[Set[B]]("fst(M')"), a.TermAs[Set[B]]("snd(M')")
			subSum := a.TermAs[Set[B]]("set_mul(V.add, fst(M'), snd(M'))")
			ambPrime := a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M')")

			// The four charts are subgroups of V under its addition, the two
			// charts of M groups in their own right.
			subgroup0 := a.Have(
				"M₀ is a subgroup of V",
				"subgroup(module_additive_group(V), fst(M))",
				By(submodule.SubmoduleSubgroup.Read(chart0)))
			subgroup1 := a.Have(
				"M₁ is a subgroup of V",
				"subgroup(module_additive_group(V), snd(M))",
				By(submodule.SubmoduleSubgroup.Read(chart1)))
			subgroup0Prime := a.Have(
				"M'₀ is a subgroup of V",
				"subgroup(module_additive_group(V), fst(M'))",
				By(submodule.SubmoduleSubgroup.Read(chart0Prime)))
			subgroup1Prime := a.Have(
				"M'₁ is a subgroup of V",
				"subgroup(module_additive_group(V), snd(M'))",
				By(submodule.SubmoduleSubgroup.Read(chart1Prime)))
			group0 := a.Have(
				"M₀ is a group under V's addition",
				"group_on(restrict_group(module_additive_group(V), fst(M)))",
				By(subgroup0, group.SubgroupGroupOn.Read(additive).At(fstM)))
			group1 := a.Have(
				"and so is M₁",
				"group_on(restrict_group(module_additive_group(V), snd(M)))",
				By(subgroup1, group.SubgroupGroupOn.Read(additive).At(sndM)))
			inV0 := a.Unfolded(group.SubgroupSubset.Read(subgroup0).AsFact(), set_basic.SubsetDef)
			inV1 := a.Unfolded(group.SubgroupSubset.Read(subgroup1).AsFact(), set_basic.SubsetDef)
			into0 := a.Unfolded(inside0, set_basic.SubsetDef)
			into1 := a.Unfolded(inside1, set_basic.SubsetDef)

			// M'₀ + M'₁, the zero of H¹(M'), lies in V and holds zero; the
			// ambient of M', the zero of Q₀₁, lies in V.
			subSumInV := a.Have(
				"M'₀ + M'₁ lies in V",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ V.carrier",
				By(
					quotient_group.SetMulIn.Read(additive).At(fstMPrime, sndMPrime),
					group.SubgroupSubset.Read(subgroup0Prime),
					group.SubgroupSubset.Read(subgroup1Prime)))
			ambPrimeModule := a.Have(
				"the ambient of M' is an R-submodule of V",
				"submodule(R, V, lattice_pair_ambient(R, V, M'))",
				By(lattice_pair.AmbientContains.At(R, A0, A1, V, MPrime), subPair))

			pointwise := a.Have(
				"a pair is the pair of classes of a section of H⁰(M) exactly "+
					"when it lies in ker c̄ and δ sends it to the zero of H¹(M')",
				"∀z:prod(set(B), set(B)). "+
					"    z ∈ "+
					"    image(λv:B.(left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M'))), "+
					"        fst(M) ∩ snd(M)) ⇔ "+
					"    z ∈ "+
					"    group_kernel(set_mul(V.add, fst(M'), snd(M')), "+
					"        group_kernel(lattice_pair_ambient(R, V, M'), "+
					"            set_cross(left_cosets(V.add, fst(M), fst(M')), "+
					"                left_cosets(V.add, snd(M), snd(M'))), "+
					"            lattice_pair_quotient_difference(R, V, M')), "+
					"        lattice_pair_connecting(V))",
				Derive(func(b *Argument) {
					z := b.FixAs[Prod[Set[B], Set[B]]]("z")
					b.Iff()
					b.Forward(
						"the classes of a section v lie in Q₀ × Q₁, and δ "+
							"and c̄ send them to the classes of v − v, both zero",
						func(d *Argument, member Fact) {
							v, section := d.UnpackAs[B](d.Simplified(member, Fwd(set_basic.InImage)), "v")
							image := d.Conjuncts(
								section,
								"z is the pair of classes of a section v",
								"v lies on both charts of M")
							onChart0 := d.Have(
								"v lies on chart 0 of M",
								"v ∈ fst(M)",
								By(image[1], set_basic.InInter.At(fstM, sndM, v)))
							vV := proof.MemberOf(v, d.Have(
								"v is a vector",
								"v ∈ V.carrier",
								By(inV0, onChart0)))
							class0 := d.Have(
								"v + M'₀ is a class of M₀ modulo M'₀, v lying in M₀",
								"left_coset(V.add, v, fst(M')) ∈ left_cosets(V.add, fst(M), fst(M'))",
								Simp(Fwd(quotient_group.InLeftCosets.Read(group0))),
								Witness(v),
								By(onChart0))
							class1 := d.Have(
								"v + M'₁ is a class of M₁ modulo M'₁, v lying in M₁",
								"left_coset(V.add, v, snd(M')) ∈ left_cosets(V.add, snd(M), snd(M'))",
								Simp(Fwd(quotient_group.InLeftCosets.Read(group1))),
								Witness(v),
								By(image[1], set_basic.InInter.At(fstM, sndM, v)))
							vanishes := d.Have(
								"δ sends the classes of v to (v − v) + (M'₀ + M'₁), which is M'₀ + M'₁",
								"lattice_pair_connecting(V, (left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M')))) = "+
									"set_mul(V.add, fst(M'), snd(M'))",
								CalcEq(
									Leg(
										d.TermAs[Set[B]]("left_coset(V.add, v + -v, set_mul(V.add, fst(M'), snd(M')))"),
										"δ of two cosets is the coset of the difference",
										By(
											ConnectingOfCosets.Read(moduleV).AsFact().At(fstMPrime, sndMPrime, v, v),
											subgroup0Prime,
											subgroup1Prime,
											vV)),
									Leg(
										d.TermAs[Set[B]]("left_coset(V.add, V.zero, set_mul(V.add, fst(M'), snd(M')))"),
										"v − v is zero",
										By(Normalized, group.RightInverseOn.Read(additive).At(vV))),
									FinalLeg(
										"and the coset of zero is M'₀ + M'₁ itself",
										By(group.LeftCosetOneOn.Read(additive).At(subSum), subSumInV)),
								))
							inAmbient := d.Have(
								"c̄ sends the classes of v to (v − v) + ambient(M'), which is ambient(M')",
								"lattice_pair_quotient_difference(R, "+
									"    V, "+
									"    M', "+
									"    (left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M')))) = "+
									"lattice_pair_ambient(R, V, M')",
								CalcEq(
									Leg(
										d.TermAs[Set[B]]("left_coset(V.add, v + -v, lattice_pair_ambient(R, V, M'))"),
										"c̄ of two cosets is the class of the difference modulo the ambient",
										By(QuotientDifferenceCoset.At(R, A0, A1, V, MPrime, v, v), subPair, vV)),
									Leg(
										d.TermAs[Set[B]]("left_coset(V.add, V.zero, lattice_pair_ambient(R, V, M'))"),
										"v − v is zero",
										By(Normalized, group.RightInverseOn.Read(additive).At(vV))),
									FinalLeg(
										"and the class of zero is the ambient of M' itself",
										By(
											group.LeftCosetOneOn.Read(additive).At(ambPrime),
											submodule.SubmoduleSubset.Read(ambPrimeModule))),
								))
							d.Show(
								"so the pair of classes of v lies in Q₀ × Q₁, in ker c̄, and in the kernel of δ",
								image[0].Rw(),
								Simp(Fwd(group_homomorphism.InKernel), Fwd(set_product.InCross)),
								By(class0, class1, inAmbient, vanishes))
						})
					b.Backward(
						"a pair (m₀ + M'₀, m₁ + M'₁) that δ kills has m₀ − m₁ = p₀ + p₁ "+
							"in M'₀ + M'₁, and is the pair of classes of m₀ − p₀ = m₁ + p₁",
						func(d *Argument, member Fact) {
							pairsOfClasses := d.TermAs[Set[Prod[Set[B], Set[B]]]]("«waQuotientPairs»")
							kernelOfCBar := d.TermAs[Set[Prod[Set[B], Set[B]]]]("«waKernelPairs»")
							cBar := d.TermAs[Fun[Prod[Set[B], Set[B]], Set[B]]]("lattice_pair_quotient_difference(R, V, M')")
							connecting := d.TermAs[Fun[Prod[Set[B], Set[B]], Set[B]]]("lattice_pair_connecting(V)")
							killed := d.Conjuncts(
								d.Have(
									"z lies in ker c̄, and δ sends it to M'₀ + M'₁",
									"z ∈ «waKernelPairs» ∧ lattice_pair_connecting(V, z) = set_mul(V.add, fst(M'), snd(M'))",
									By(member, group_homomorphism.InKernel.At(subSum, kernelOfCBar, connecting, z))),
								"z lies in ker c̄",
								"δ kills z")
							m0, m1, rep := d.Obtain2As[B, B](
								"z is (m₀ + M'₀, m₁ + M'₁) for some m₀ on chart 0 and m₁ on chart 1 of M",
								"∃m₀ m₁:B. "+
									"    m₀ ∈ fst(M) ∧ "+
									"    m₁ ∈ snd(M) ∧ "+
									"    z = (left_coset(V.add, m₀, fst(M')), left_coset(V.add, m₁, snd(M')))",
								By(
									QuotientPairCosets.At(R, A0, A1, V, M, MPrime, z),
									pair,
									inside0,
									inside1,
									killed[0],
									group_homomorphism.InKernel.At(ambPrime, pairsOfClasses, cBar, z)))
							reps := d.Conjuncts(
								rep,
								"m₀ lies on chart 0 of M",
								"m₁ lies on chart 1 of M",
								"z is the pair of their classes")
							m0V := proof.MemberOf(m0, d.Have(
								"m₀ is a vector",
								"m₀ ∈ V.carrier",
								By(inV0, reps[0])))
							m1V := proof.MemberOf(m1, d.Have(
								"and so is m₁",
								"m₁ ∈ V.carrier",
								By(inV1, reps[1])))
							gap := d.Have(
								"δ of z is (m₀ − m₁) + (M'₀ + M'₁), so that coset is M'₀ + M'₁",
								"left_coset(V.add, m₀ + -m₁, set_mul(V.add, fst(M'), snd(M'))) = set_mul(V.add, fst(M'), snd(M'))",
								By(
									killed[1],
									reps[2],
									ConnectingOfCosets.Read(moduleV).AsFact().At(fstMPrime, sndMPrime, m0, m1),
									subgroup0Prime,
									subgroup1Prime,
									m0V,
									m1V))
							difference := group.MulIn.Read(additive).At(m0V, group.InvIn.Read(additive).At(m1V))
							own := d.Have(
								"m₀ − m₁ lies in its own coset, M'₀ + M'₁ holding zero",
								"m₀ + -m₁ ∈ left_coset(V.add, m₀ + -m₁, set_mul(V.add, fst(M'), snd(M')))",
								By(
									group.InLeftCosetOn.Read(additive).At(difference, difference, subSum),
									subSumInV,
									group.LeftInverseOn.Read(additive).At(difference),
									lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, MPrime),
									subPair))
							p0, p1, split := d.Obtain2As[B, B](
								"m₀ − m₁ is p₀ + p₁ for some p₀ in M'₀ and p₁ in M'₁",
								"∃p₀ p₁:B. p₀ ∈ fst(M') ∧ p₁ ∈ snd(M') ∧ m₀ + -m₁ = p₀ + p₁",
								By(own, gap, quotient_group.InSetMul))
							terms := d.Conjuncts(
								split,
								"p₀ lies in M'₀",
								"p₁ lies in M'₁",
								"m₀ − m₁ is p₀ + p₁")
							p0V := proof.MemberOf(p0, d.Have(
								"p₀ is a vector",
								"p₀ ∈ V.carrier",
								By(inV0, into0, terms[0])))
							p1V := proof.MemberOf(p1, d.Have(
								"and so is p₁",
								"p₁ ∈ V.carrier",
								By(inV1, into1, terms[1])))
							onChart0 := d.Have(
								"m₀ − p₀ lies on chart 0 of M, which holds m₀ and p₀",
								"m₀ + -p₀ ∈ fst(M)",
								By(submodule.SubmoduleSub.Read(chart0), reps[0], into0, terms[0]))
							meet := d.Have(
								"m₀ − p₀ is m₁ + p₁",
								"m₀ + -p₀ = m₁ + p₁",
								ByChase(Depth(0), moduleV, m0V, m1V, p0V, p1V, terms[2]))
							onChart1 := d.Have(
								"m₁ + p₁ lies on chart 1 of M, which holds m₁ and p₁",
								"m₁ + p₁ ∈ snd(M)",
								By(submodule.SubmoduleAdd.Read(chart1), reps[1], into1, terms[1]))
							section1 := d.Have(
								"so m₀ − p₀ lies on chart 1 of M too",
								"m₀ + -p₀ ∈ snd(M)",
								By(Normalized, meet, onChart1))
							v := proof.MemberOf(d.TermAs[B]("m₀ + -p₀"), d.Have(
								"m₀ − p₀ is a vector",
								"m₀ + -p₀ ∈ V.carrier",
								By(inV0, onChart0)))
							back0 := d.Have(
								"−(m₀ − p₀) + m₀ is p₀",
								"-(m₀ + -p₀) + m₀ = p₀",
								ByChase(Depth(0), moduleV, m0V, p0V))
							back1 := d.Have(
								"−m₁ + (m₀ − p₀) is p₁",
								"-m₁ + (m₀ + -p₀) = p₁",
								ByChase(Depth(0), moduleV, m0V, m1V, p0V, p1V, meet))
							coset0 := d.Have(
								"m₀ − p₀ and m₀ have one class modulo M'₀",
								"left_coset(V.add, m₀ + -p₀, fst(M')) = left_coset(V.add, m₀, fst(M'))",
								By(group.LeftCosetEqOn.Read(additive).At(v, m0V, fstMPrime), subgroup0Prime, back0, terms[0]))
							coset1 := d.Have(
								"m₀ − p₀ and m₁ have one class modulo M'₁",
								"left_coset(V.add, m₀ + -p₀, snd(M')) = left_coset(V.add, m₁, snd(M'))",
								By(group.LeftCosetEqOn.Read(additive).At(m1V, v, sndMPrime), subgroup1Prime, back1, terms[1]))
							d.Do(reps[2].Rw(), Simp(Fwd(set_basic.InImage)))
							d.Take(v)
							d.Show(
								"so z is the pair of classes of m₀ − p₀, a section on both charts of M",
								By(pairs.PairEq, coset0, coset1, set_basic.InInter, onChart0, section1))
						})
				}))
			a.Show(
				"exactness at ker c̄ is that equation of sets",
				Simp(
					Fwd(module_homomorphism.ExactAtDef),
					Fwd(lattice_pair.LatticePairH1Def),
					Fwd(lattice_pair.LatticePairH0Def),
					Fwd(LatticePairQuotientKernelDef),
					Fwd(module_record.RestrictModuleDef),
					Fwd(submodule.QuotientModuleDef)),
				By(pointwise, set_basic.Extension))
		}),
})}

// ConnectingCokernel — the six-term sequence of a sub-pair is exact at
// H¹(M'): the classes X ↦ X + (M₀ + M₁) kills are the values of δ; and
// where c̄ is onto, that map is onto H¹(M). Everything is read on
// representatives: a pair of classes is (x + M'₀, y + M'₁)
// (QuotientPairCosets), δ sends it to (x − y) + (M'₀ + M'₁)
// (ConnectingOfCosets) and c̄ to (x − y) + ambient(M')
// (QuotientDifferenceCoset), and X ↦ X + (M₀ + M₁) sends w + (M'₀ + M'₁)
// to w + (M₀ + M₁), which is zero exactly when w lies in M₀ + M₁. Onto: c̄
// reaching v + ambient(M') at (x + M'₀, y + M'₁) puts w = −(x − y) + v in
// the ambient of M', with w + (M₀ + M₁) = v + (M₀ + M₁) since x − y lies in
// M₀ + M₁.
var ConnectingCokernel = connectingCokernelThm{family.Add(registry.ProofEntry{
	Name: "ConnectingCokernel",
	Key:  "prop_28e31123679b873",
	Reading: "The second conjunct is an implication: c̄ onto Q₀₁ makes H¹(M') → H¹(M) onto, " +
		"and no finiteness is assumed; the converse is not stated. The zero of H¹(M) is M₀ + M₁.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waPair»(M)",
			"«waPair»(M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
		},
		Conclusion: "exact_at(lattice_pair_h1(R, V, M).zero, " +
			"    «waKernelModule».carrier, " +
			"    lattice_pair_h1(R, V, M').carrier, " +
			"    lattice_pair_connecting(V), " +
			"    «waH1Map») ∧ " +
			"(image(lattice_pair_quotient_difference(R, V, M'), «waQuotientPairs») = «waQ01Carrier» ⇒ " +
			"    image(«waH1Map», lattice_pair_h1(R, V, M').carrier) = lattice_pair_h1(R, V, M).carrier)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"and M'₁ in M₁")
			pair, subPair, inside0, inside1 := parts[0], parts[1], parts[2], parts[3]
			charts := a.Conjuncts(
				a.Unfolded(pair, lattice_pair.LatticePairDef),
				"V is a module over R",
				"M₀ is an A₀-submodule of V",
				"M₁ is an A₁-submodule of V",
				"the charts of M span one R-submodule")
			vectors, chart0, chart1 := charts[0], charts[1], charts[2]
			chartsPrime := a.Unfolded(subPair, lattice_pair.LatticePairDef)
			chart0Prime := a.Have(
				"M'₀ is an A₀-submodule of V",
				"submodule(restrict_ring(R, A₀), V, fst(M'))",
				By(chartsPrime))
			chart1Prime := a.Have(
				"and M'₁ an A₁-submodule",
				"submodule(restrict_ring(R, A₁), V, snd(M'))",
				By(chartsPrime))
			additive := module.AddGroupOn.Read(vectors)

			// The subgroups of V whose cosets are the classes.
			chart0Subgroup := a.Have(
				"M₀ is a subgroup of V under the addition",
				"subgroup(module_additive_group(V), fst(M))",
				By(submodule.SubmoduleSubgroup.Read(chart0)))
			chart1Subgroup := a.Have(
				"so is M₁",
				"subgroup(module_additive_group(V), snd(M))",
				By(submodule.SubmoduleSubgroup.Read(chart1)))
			fstMPrime, sndMPrime := a.TermAs[Set[B]]("fst(M')"), a.TermAs[Set[B]]("snd(M')")
			subgroup0Prime := a.Have(
				"so is M'₀",
				"subgroup(module_additive_group(V), fst(M'))",
				By(submodule.SubmoduleSubgroup.Read(chart0Prime)))
			subgroup1Prime := a.Have(
				"and M'₁",
				"subgroup(module_additive_group(V), snd(M'))",
				By(submodule.SubmoduleSubgroup.Read(chart1Prime)))
			ambientModule := a.Have(
				"the ambient of M is an R-submodule of V",
				"submodule(R, V, lattice_pair_ambient(R, V, M))",
				By(lattice_pair.AmbientContains.At(R, A0, A1, V, M), pair))
			ambPrimeModule := a.Have(
				"so is the ambient of M'",
				"submodule(R, V, lattice_pair_ambient(R, V, M'))",
				By(lattice_pair.AmbientContains.At(R, A0, A1, V, MPrime), subPair))
			ambPrimeSubgroup := a.Have(
				"and a subgroup of V",
				"subgroup(module_additive_group(V), lattice_pair_ambient(R, V, M'))",
				By(submodule.SubmoduleSubgroup.Read(ambPrimeModule)))
			normalizes := a.Have(
				"M₀ normalizes M₁, the addition being commutative",
				"∀x y:B. x ∈ fst(M) ∧ y ∈ snd(M) ⇒ x + y + -x ∈ snd(M)",
				Derive(func(b *Argument) {
					b.FixAs[B]("x")
					b.FixAs[B]("y")
					points := b.Conjuncts(
						b.Assume(),
						"x lies in M₀",
						"y lies in M₁")
					back := b.Have(
						"(x + y) − x is y",
						"x + y + -x = y",
						ByChase(Depth(0), vectors, chart0, chart1, points[0], points[1]))
					b.Show(
						"so it lies in M₁",
						back.Rw(),
						By(points[1]))
				}))
			sumSubgroup := a.Have(
				"so M₀ + M₁ is a subgroup of V",
				"subgroup(module_additive_group(V), set_mul(V.add, fst(M), snd(M)))",
				By(group_isomorphism.SetMulSubgroup.Read(additive), chart0Subgroup, chart1Subgroup, normalizes))
			asGroup := group.SubgroupGroupOn.Read(additive)
			chart0Group := a.Have(
				"M₀ is a group under the addition",
				"group_on(restrict_group(module_additive_group(V), fst(M)))",
				By(chart0Subgroup, asGroup.At(a.TermAs[Set[B]]("fst(M)"))))
			chart1Group := a.Have(
				"so is M₁",
				"group_on(restrict_group(module_additive_group(V), snd(M)))",
				By(chart1Subgroup, asGroup.At(a.TermAs[Set[B]]("snd(M)"))))
			ambientGroup := a.Have(
				"and the ambient of M",
				"group_on(restrict_group(module_additive_group(V), lattice_pair_ambient(R, V, M)))",
				By(
					submodule.SubmoduleSubgroup.Read(ambientModule),
					asGroup.At(a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M)"))))
			ambPrimeGroup := a.Have(
				"and that of M'",
				"group_on(restrict_group(module_additive_group(V), lattice_pair_ambient(R, V, M')))",
				By(ambPrimeSubgroup, asGroup.At(a.TermAs[Set[B]]("lattice_pair_ambient(R, V, M')"))))

			// The inclusions among them, and the zero of H¹(M').
			sumInAmbient := a.Have(
				"M₀ + M₁ lies in the ambient of M",
				"set_mul(V.add, fst(M), snd(M)) ⊆ lattice_pair_ambient(R, V, M)",
				By(lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, M), pair))
			subSumInAmbient := a.Have(
				"M'₀ + M'₁ in the ambient of M'",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ lattice_pair_ambient(R, V, M')",
				By(lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, MPrime), subPair))
			ambientBelow := a.Have(
				"the ambient of M' lies in that of M",
				"lattice_pair_ambient(R, V, M') ⊆ lattice_pair_ambient(R, V, M)",
				By(lattice_pair.SubpairInclusions.At(R, V, M, MPrime), inside0, inside1))
			sumBelow := a.Have(
				"M'₀ + M'₁ lies in M₀ + M₁",
				"set_mul(V.add, fst(M'), snd(M')) ⊆ set_mul(V.add, fst(M), snd(M))",
				By(lattice_pair.SubpairInclusions.At(R, V, M, MPrime), inside0, inside1))
			toV0 := a.Unfolded(submodule.SubmoduleSubset.Read(chart0).AsFact(), set_basic.SubsetDef)
			toV1 := a.Unfolded(submodule.SubmoduleSubset.Read(chart1).AsFact(), set_basic.SubsetDef)
			ambientInV := a.Unfolded(
				submodule.SubmoduleSubset.Read(ambientModule).AsFact(), set_basic.SubsetDef)
			ambPrimeInV := a.Unfolded(
				submodule.SubmoduleSubset.Read(ambPrimeModule).AsFact(), set_basic.SubsetDef)
			intoAmbient := a.Unfolded(ambientBelow, set_basic.SubsetDef)
			differences := a.Have(
				"a point of M₀ minus a point of M₁ lies in M₀ + M₁, M₁ holding the negative",
				"∀x y:B. x ∈ fst(M) ∧ y ∈ snd(M) ⇒ x + -y ∈ set_mul(V.add, fst(M), snd(M))",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					b.FixAs[B]("y")
					points := b.Conjuncts(
						b.Assume(),
						"x lies in M₀",
						"y lies in M₁")
					b.Do(Simp(Fwd(quotient_group.InSetMul)))
					b.Take(x)
					b.Take(b.TermAs[B]("-y"))
					b.Show(
						"x lies in M₀ and −y in M₁",
						By(points[0], submodule.SubmoduleNeg.Read(chart1), points[1]))
				}))

			// X ↦ X + (M₀ + M₁) adds M₀ + M₁ to the representative, and a class is
			// zero exactly when its representative lies in what it is taken modulo.
			classMap := a.Have(
				"X ↦ X + (M₀ + M₁) sends w + (M'₀ + M'₁) to w + (M₀ + M₁)",
				Statement{
					Binders: "∀w:B.",
					Hypotheses: []string{
						"w ∈ V.carrier",
					},
					Conclusion: "set_mul(V.add, " +
						"    left_coset(V.add, w, set_mul(V.add, fst(M'), snd(M'))), " +
						"    set_mul(V.add, fst(M), snd(M))) = " +
						"left_coset(V.add, w, set_mul(V.add, fst(M), snd(M)))",
				},
				By(
					quotient_group.LeftCosetSetMulAbsorb.Read(additive),
					sumSubgroup,
					sumBelow,
					lattice_pair.ChartSumInAmbient.At(R, A0, A1, V, MPrime),
					subPair))
			zeroClass := a.Have(
				"w + (M₀ + M₁) is the zero class exactly when w lies in M₀ + M₁",
				Statement{
					Binders: "∀w:B.",
					Hypotheses: []string{
						"w ∈ V.carrier",
					},
					Conclusion: "left_coset(V.add, w, set_mul(V.add, fst(M), snd(M))) = " +
						"set_mul(V.add, fst(M), snd(M)) ⇔ " +
						"w ∈ set_mul(V.add, fst(M), snd(M))",
				},
				By(quotient_group.LeftCosetIsSubgroupIffIn.Read(additive), sumSubgroup))
			zeroQuotientClass := a.Have(
				"w + ambient(M') is the zero class exactly when w lies in the ambient of M'",
				Statement{
					Binders: "∀w:B.",
					Hypotheses: []string{
						"w ∈ V.carrier",
					},
					Conclusion: "left_coset(V.add, w, lattice_pair_ambient(R, V, M')) = " +
						"lattice_pair_ambient(R, V, M') ⇔ " +
						"w ∈ lattice_pair_ambient(R, V, M')",
				},
				By(quotient_group.LeftCosetIsSubgroupIffIn.Read(additive), ambPrimeSubgroup))

			a.Do(SplitConj(
				Case(
					"exact at H¹(M'): the classes X ↦ X + (M₀ + M₁) kills are the values of δ on ker c̄",
					Derive(func(b *Argument) {
						b.Do(Unfold(module_homomorphism.ExactAtDef), Simp(Fwd(set_basic.Extension)))
						X := b.FixAs[Set[B]]("X")
						b.Iff()
						b.Forward(
							"X = δ(z) with z = (x + M'₀, y + M'₁) killed by c̄ is (x − y) "+
								"+ (M'₀ + M'₁) with x − y in the ambient of M' and in M₀ + M₁",
							func(c *Argument, member Fact) {
								z, value := c.ObtainAs[Prod[Set[B], Set[B]]](
									"X is δ(z) for a pair z in ker c̄",
									"∃z:prod(set(B), set(B)). X = lattice_pair_connecting(V, z) ∧ z ∈ «waKernelPairs»",
									By(member, set_basic.InImage))
								values := c.Conjuncts(
									value,
									"X is δ(z)",
									"z lies in ker c̄")
								kernel := c.Conjuncts(
									c.Have(
										"z lies in Q and c̄ sends it to zero",
										"z ∈ «waQuotientPairs» ∧ "+
											"lattice_pair_quotient_difference(R, V, M', z) = lattice_pair_ambient(R, V, M')",
										By(
											values[1],
											group_homomorphism.InKernel.At(
												c.TermAs[Set[B]]("lattice_pair_ambient(R, V, M')"),
												c.TermAs[Set[Prod[Set[B], Set[B]]]]("«waQuotientPairs»"),
												c.TermAs[Fun[Prod[Set[B], Set[B]], Set[B]]]("lattice_pair_quotient_difference(R, V, M')"),
												z))),
									"z lies in Q",
									"c̄(z) is zero")
								x, y, rep := c.Obtain2As[B, B](
									"z is (x + M'₀, y + M'₁) for some x in M₀ and y in M₁",
									"∃x y:B. "+
										"    x ∈ fst(M) ∧ y ∈ snd(M) ∧ z = (left_coset(V.add, x, fst(M')), left_coset(V.add, y, snd(M')))",
									By(QuotientPairCosets.At(R, A0, A1, V, M, MPrime, z), pair, inside0, inside1, kernel[0]))
								reps := c.Conjuncts(
									rep,
									"x lies in M₀",
									"y lies in M₁",
									"z is the pair of their cosets")
								xV := c.Have(
									"x is a vector",
									"x ∈ V.carrier",
									By(toV0, reps[0]))
								yV := c.Have(
									"so is y",
									"y ∈ V.carrier",
									By(toV1, reps[1]))
								differenceV := c.Have(
									"and so is x − y",
									"x + -y ∈ V.carrier",
									By(group.MulIn.Read(additive), group.InvIn.Read(additive), xV, yV))
								connecting := c.Have(
									"X is the coset of x − y by M'₀ + M'₁",
									"X = left_coset(V.add, x + -y, set_mul(V.add, fst(M'), snd(M')))",
									By(
										values[0],
										reps[2],
										ConnectingOfCosets.At(R, V, fstMPrime, sndMPrime, x, y),
										vectors,
										subgroup0Prime,
										subgroup1Prime,
										xV,
										yV))
								quotient := c.Have(
									"c̄(z) is the class of x − y modulo the ambient of M'",
									"lattice_pair_quotient_difference(R, V, M', z) = "+
										"left_coset(V.add, x + -y, lattice_pair_ambient(R, V, M'))",
									By(Normalized, reps[2], QuotientDifferenceCoset.At(R, A0, A1, V, MPrime, x, y), subPair, xV, yV))
								inAmbient := c.Have(
									"so x − y lies in the ambient of M', c̄ killing z",
									"x + -y ∈ lattice_pair_ambient(R, V, M')",
									By(zeroQuotientClass.At(c.TermAs[B]("x + -y")), differenceV, quotient, kernel[1]))
								inSum := c.Have(
									"and x − y lies in M₀ + M₁",
									"x + -y ∈ set_mul(V.add, fst(M), snd(M))",
									By(reps[0], reps[1], differences))
								isClass := c.Have(
									"(x − y) + (M'₀ + M'₁) is a class of H¹(M')",
									"left_coset(V.add, x + -y, set_mul(V.add, fst(M'), snd(M'))) ∈ "+
										"left_cosets(V.add, lattice_pair_ambient(R, V, M'), set_mul(V.add, fst(M'), snd(M')))",
									Simp(Fwd(quotient_group.InLeftCosets.Read(ambPrimeGroup))),
									Witness(c.TermAs[B]("x + -y")),
									By(inAmbient))
								killed := c.Have(
									"which X ↦ X + (M₀ + M₁) sends to the zero class, x − y lying in M₀ + M₁",
									"set_mul(V.add, "+
										"    left_coset(V.add, x + -y, set_mul(V.add, fst(M'), snd(M'))), "+
										"    set_mul(V.add, fst(M), snd(M))) = "+
										"set_mul(V.add, fst(M), snd(M))",
									By(classMap.At(c.TermAs[B]("x + -y")), zeroClass.At(c.TermAs[B]("x + -y")), differenceV, inSum))
								c.Do(connecting.Rw())
								c.Show(
									"so X is a class of H¹(M') that X ↦ X + (M₀ + M₁) kills",
									By(group_homomorphism.InKernel, isClass, killed))
							})
						b.Backward(
							"a class w + (M'₀ + M'₁) that X ↦ X + (M₀ + M₁) kills has w = "+
								"x + u in M₀ + M₁, and is δ(x + M'₀, −u + M'₁), a pair c̄ kills",
							func(c *Argument, member Fact) {
								kernel := c.Conjuncts(
									c.Have(
										"X is a class of H¹(M') that X ↦ X + (M₀ + M₁) sends to zero",
										"X ∈ left_cosets(V.add, lattice_pair_ambient(R, V, M'), set_mul(V.add, fst(M'), snd(M'))) ∧ "+
											"set_mul(V.add, X, set_mul(V.add, fst(M), snd(M))) = set_mul(V.add, fst(M), snd(M))",
										By(
											member,
											group_homomorphism.InKernel.At(
												c.TermAs[Set[B]]("set_mul(V.add, fst(M), snd(M))"),
												c.TermAs[Set[Set[B]]](
													"left_cosets(V.add, lattice_pair_ambient(R, V, M'), set_mul(V.add, fst(M'), snd(M')))"),
												c.TermAs[Fun[Set[B], Set[B]]]("«waH1Map»"),
												X))),
									"X is a class of H¹(M')",
									"X + (M₀ + M₁) is zero")
								w, rep := c.ObtainAs[B](
									"X is w + (M'₀ + M'₁) for a point w of the ambient of M'",
									"∃w:B. "+
										"    X = left_coset(V.add, w, set_mul(V.add, fst(M'), snd(M'))) ∧ "+
										"    w ∈ lattice_pair_ambient(R, V, M')",
									By(subSumInAmbient, kernel[0], quotient_group.InLeftCosets.Read(ambPrimeGroup)))
								reps := c.Conjuncts(
									rep,
									"X is w + (M'₀ + M'₁)",
									"w lies in the ambient of M'")
								wV := c.Have(
									"w is a vector",
									"w ∈ V.carrier",
									By(ambPrimeInV, reps[1]))
								inSum := c.Have(
									"w lies in M₀ + M₁, its class w + (M₀ + M₁) being zero",
									"w ∈ set_mul(V.add, fst(M), snd(M))",
									By(Normalized, zeroClass.At(w), wV, classMap.At(w), reps[0], kernel[1]))
								x, _, sum := c.Obtain2As[B, B](
									"w is x + u for some x in M₀ and u in M₁",
									"∃x u:B. x ∈ fst(M) ∧ u ∈ snd(M) ∧ w = x + u",
									By(inSum, quotient_group.InSetMul))
								sums := c.Conjuncts(
									sum,
									"x lies in M₀",
									"u lies in M₁",
									"w is x + u")
								negated := c.Have(
									"M₁ holds −u",
									"-u ∈ snd(M)",
									By(submodule.SubmoduleNeg.Read(chart1), sums[1]))
								xV := c.Have(
									"x is a vector",
									"x ∈ V.carrier",
									By(toV0, sums[0]))
								negV := c.Have(
									"so is −u",
									"-u ∈ V.carrier",
									By(toV1, negated))
								twice := c.Have(
									"x − (−u) is w",
									"x + -(-u) = w",
									ByChase(Depth(0), vectors, chart0, chart1, sums[0], sums[1], sums[2]))
								negU := c.TermAs[B]("-u")
								connecting := c.Have(
									"δ(x + M'₀, −u + M'₁) is (x − (−u)) + (M'₀ + M'₁), which is X",
									"lattice_pair_connecting(V, (left_coset(V.add, x, fst(M')), left_coset(V.add, -u, snd(M')))) = X",
									By(
										ConnectingOfCosets.At(R, V, fstMPrime, sndMPrime, x, negU),
										vectors,
										subgroup0Prime,
										subgroup1Prime,
										xV,
										negV,
										twice,
										reps[0]))
								quotient := c.Have(
									"and c̄ sends the pair to zero, w lying in the ambient of M'",
									"lattice_pair_quotient_difference(R, "+
										"    V, "+
										"    M', "+
										"    (left_coset(V.add, x, fst(M')), left_coset(V.add, -u, snd(M')))) = "+
										"lattice_pair_ambient(R, V, M')",
									By(
										QuotientDifferenceCoset.At(R, A0, A1, V, MPrime, x, negU),
										subPair,
										xV,
										negV,
										twice,
										zeroQuotientClass.At(w),
										wV,
										reps[1]))
								inQ := c.Have(
									"the pair lies in Q",
									"(left_coset(V.add, x, fst(M')), left_coset(V.add, -u, snd(M'))) ∈ «waQuotientPairs»",
									Simp(Fwd(set_product.InCross)),
									SplitConj(
										Case(
											"x + M'₀ is a coset of M'₀ in M₀",
											Simp(Fwd(quotient_group.InLeftCosets.Read(chart0Group))),
											Witness(x),
											By(sums[0])),
										Case(
											"−u + M'₁ is a coset of M'₁ in M₁",
											Simp(Fwd(quotient_group.InLeftCosets.Read(chart1Group))),
											Witness(negU),
											By(negated)),
									))
								inKernel := c.Have(
									"so the pair lies in ker c̄",
									"(left_coset(V.add, x, fst(M')), left_coset(V.add, -u, snd(M'))) ∈ «waKernelPairs»",
									By(group_homomorphism.InKernel, inQ, quotient))
								c.Do(Simp(Fwd(set_basic.InImage)))
								c.Take(
									c.TermAs[Prod[Set[B], Set[B]]]("(left_coset(V.add, x, fst(M')), left_coset(V.add, -u, snd(M')))"))
								c.Show(
									"X is δ of that pair",
									By(connecting, inKernel))
							})
					})),
				Case(
					"onto H¹(M) where c̄ is onto: a class v + (M₀ + M₁) "+
						"is the image of w + (M'₀ + M'₁) with w = −(x − y) + v",
					Derive(func(b *Argument) {
						onto := b.Assume()
						b.Do(Simp(Fwd(set_basic.Extension)))
						b.FixAs[Set[B]]("Y")
						b.Iff()
						b.Forward(
							"Y is w + (M₀ + M₁) for w in the ambient of M', which lies in the ambient of M",
							func(c *Argument, member Fact) {
								_, value := c.ObtainAs[Set[B]](
									"Y is X + (M₀ + M₁) for a class X of H¹(M')",
									"∃X:set(B). "+
										"    Y = set_mul(V.add, X, set_mul(V.add, fst(M), snd(M))) ∧ "+
										"    X ∈ left_cosets(V.add, lattice_pair_ambient(R, V, M'), set_mul(V.add, fst(M'), snd(M')))",
									By(member, set_basic.InImage))
								values := c.Conjuncts(
									value,
									"Y is X + (M₀ + M₁)",
									"X is a class of H¹(M')")
								w, rep := c.ObtainAs[B](
									"X is w + (M'₀ + M'₁) for a point w of the ambient of M'",
									"∃w:B. "+
										"    X = left_coset(V.add, w, set_mul(V.add, fst(M'), snd(M'))) ∧ "+
										"    w ∈ lattice_pair_ambient(R, V, M')",
									By(subSumInAmbient, values[1], quotient_group.InLeftCosets.Read(ambPrimeGroup)))
								reps := c.Conjuncts(
									rep,
									"X is w + (M'₀ + M'₁)",
									"w lies in the ambient of M'")
								image := c.Have(
									"Y is w + (M₀ + M₁)",
									"Y = left_coset(V.add, w, set_mul(V.add, fst(M), snd(M)))",
									By(Normalized, values[0], reps[0], classMap.At(w), ambPrimeInV, reps[1]))
								c.Do(image.Rw(), Simp(Fwd(quotient_group.InLeftCosets.Read(ambientGroup))))
								c.Take(w)
								c.Show(
									"a class of H¹(M)",
									By(intoAmbient, reps[1]))
							})
						b.Backward(
							"v + ambient(M') = c̄(x + M'₀, y + M'₁) puts w = −(x − y) "+
								"+ v in the ambient of M', and w + (M₀ + M₁) = v + (M₀ + M₁)",
							func(c *Argument, member Fact) {
								v, rep := c.ObtainAs[B](
									"Y is v + (M₀ + M₁) for a point v of the ambient of M",
									"∃v:B. "+
										"    Y = left_coset(V.add, v, set_mul(V.add, fst(M), snd(M))) ∧ v ∈ lattice_pair_ambient(R, V, M)",
									By(sumInAmbient, member, quotient_group.InLeftCosets.Read(ambientGroup)))
								reps := c.Conjuncts(
									rep,
									"Y is v + (M₀ + M₁)",
									"v lies in the ambient of M")
								vV := c.Have(
									"v is a vector",
									"v ∈ V.carrier",
									By(ambientInV, reps[1]))
								overlapClass := c.Have(
									"v + ambient(M') is a class of the overlap quotient",
									"left_coset(V.add, v, lattice_pair_ambient(R, V, M')) ∈ "+
										"left_cosets(V.add, lattice_pair_ambient(R, V, M), lattice_pair_ambient(R, V, M'))",
									Simp(Fwd(quotient_group.InLeftCosets.Read(ambientGroup))),
									Witness(v),
									By(reps[1]))
								reached := c.Have(
									"so c̄ reaches it",
									"left_coset(V.add, v, lattice_pair_ambient(R, V, M')) ∈ "+
										"image(lattice_pair_quotient_difference(R, V, M'), «waQuotientPairs»)",
									By(onto, overlapClass))
								z, preimage := c.ObtainAs[Prod[Set[B], Set[B]]](
									"v + ambient(M') is c̄(z) for a pair z in Q",
									"∃z:prod(set(B), set(B)). "+
										"    left_coset(V.add, v, lattice_pair_ambient(R, V, M')) = "+
										"    lattice_pair_quotient_difference(R, V, M', z) ∧ "+
										"    z ∈ «waQuotientPairs»",
									By(reached, set_basic.InImage))
								preimages := c.Conjuncts(
									preimage,
									"v + ambient(M') is c̄(z)",
									"z lies in Q")
								x, y, pairRep := c.Obtain2As[B, B](
									"z is (x + M'₀, y + M'₁) for some x in M₀ and y in M₁",
									"∃x y:B. "+
										"    x ∈ fst(M) ∧ y ∈ snd(M) ∧ z = (left_coset(V.add, x, fst(M')), left_coset(V.add, y, snd(M')))",
									By(QuotientPairCosets.At(R, A0, A1, V, M, MPrime, z), pair, inside0, inside1, preimages[1]))
								pairReps := c.Conjuncts(
									pairRep,
									"x lies in M₀",
									"y lies in M₁",
									"z is the pair of their cosets")
								xV := c.Have(
									"x is a vector",
									"x ∈ V.carrier",
									By(toV0, pairReps[0]))
								yV := c.Have(
									"so is y",
									"y ∈ V.carrier",
									By(toV1, pairReps[1]))
								differenceV := c.Have(
									"and so is x − y",
									"x + -y ∈ V.carrier",
									By(group.MulIn.Read(additive), group.InvIn.Read(additive), xV, yV))
								sameClass := c.Have(
									"so v and x − y have one class modulo the ambient of M'",
									"left_coset(V.add, x + -y, lattice_pair_ambient(R, V, M')) = "+
										"left_coset(V.add, v, lattice_pair_ambient(R, V, M'))",
									By(
										Normalized,
										preimages[0],
										pairReps[2],
										QuotientDifferenceCoset.At(R, A0, A1, V, MPrime, x, y),
										subPair,
										xV,
										yV))
								inAmbient := c.Have(
									"hence w = −(x − y) + v lies in the ambient of M'",
									"-(x + -y) + v ∈ lattice_pair_ambient(R, V, M')",
									By(group.LeftCosetEqOn.Read(additive), differenceV, vV, ambPrimeSubgroup, sameClass))
								wV := c.Have(
									"w is a vector",
									"-(x + -y) + v ∈ V.carrier",
									By(ambPrimeInV, inAmbient))
								inSum := c.Have(
									"x − y lies in M₀ + M₁",
									"x + -y ∈ set_mul(V.add, fst(M), snd(M))",
									By(pairReps[0], pairReps[1], differences))
								shift := c.Have(
									"−w + v is x − y",
									"-(-(x + -y) + v) + v = x + -y",
									ByChase(Depth(0), vectors, xV, yV, vV))
								difference := c.Have(
									"so −w + v lies in M₀ + M₁",
									"-(-(x + -y) + v) + v ∈ set_mul(V.add, fst(M), snd(M))",
									shift.Rw(),
									By(inSum))
								w := c.TermAs[B]("-(x + -y) + v")
								same := c.Have(
									"so w and v have one class modulo M₀ + M₁",
									"left_coset(V.add, -(x + -y) + v, set_mul(V.add, fst(M), snd(M))) = "+
										"left_coset(V.add, v, set_mul(V.add, fst(M), snd(M)))",
									By(
										sumSubgroup,
										difference,
										group.LeftCosetEqOn.Read(additive).At(
											proof.MemberOf(w, wV), proof.MemberOf(v, vV), c.TermAs[Set[B]]("set_mul(V.add, fst(M), snd(M))"))))
								isClass := c.Have(
									"w + (M'₀ + M'₁) is a class of H¹(M')",
									"left_coset(V.add, -(x + -y) + v, set_mul(V.add, fst(M'), snd(M'))) ∈ "+
										"left_cosets(V.add, lattice_pair_ambient(R, V, M'), set_mul(V.add, fst(M'), snd(M')))",
									Simp(Fwd(quotient_group.InLeftCosets.Read(ambPrimeGroup))),
									Witness(w),
									By(inAmbient))
								c.Do(reps[0].Rw(), Simp(Fwd(set_basic.InImage)))
								c.Take(c.TermAs[Set[B]]("left_coset(V.add, -(x + -y) + v, set_mul(V.add, fst(M'), snd(M')))"))
								c.Show(
									"v + (M₀ + M₁) is the image of w + (M'₀ + M'₁)",
									By(classMap.At(w), wV, same, isClass))
							})
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The Euler characteristic of a sub-pair
// ---------------------------------------------------------------------------

// SixTermSequence — the snake lemma's sequence over k, in kernel–image
// form: for a sub-pair M' ⊆ M with finite-dimensional chart quotients, the
// maps H⁰(M) → ker c̄ → H¹(M') → H¹(M) are k-linear, ker c̄ is
// finite-dimensional over k, the kernel of H⁰(M) → ker c̄ is H⁰(M'), the
// kernel of δ is the image of H⁰(M), the kernel of H¹(M') → H¹(M) is the
// image of δ, and H¹(M') maps onto H¹(M). k is a subring of R inside both
// charts, so the maps are k-linear (SixTermMaps); Q₀ and Q₁ finite make
// ker c̄ finite and c̄ onto Q₀₁ (PairDifferenceQuotient), and c̄ onto makes
// H¹(M') → H¹(M) onto (ConnectingCokernel); exactness at H⁰(M)
// (SixTermH0Exact) is read as the kernel of v ↦ (v + M'₀, v + M'₁), and
// exactness at ker c̄ (ConnectingKernel) as the kernel of δ.
var SixTermSequence = sixTermSequenceThm{family.Add(registry.ProofEntry{
	Name: "SixTermSequence",
	Key:  "prop_2bb779c024c2822a",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
			"finite_dimensional(restrict_ring(R, k), «waQ0»)",
			"finite_dimensional(restrict_ring(R, k), «waQ1»)",
		},
		Conclusion: "module_homomorphism(restrict_ring(R, k), " +
			"    lattice_pair_h0(V, M), " +
			"    «waKernelModule», " +
			"    «waToClasses») ∧ " +
			"module_homomorphism(restrict_ring(R, k), " +
			"    «waKernelModule», " +
			"    lattice_pair_h1(R, V, M'), " +
			"    lattice_pair_connecting(V)) ∧ " +
			"module_homomorphism(restrict_ring(R, k), " +
			"    lattice_pair_h1(R, V, M'), " +
			"    lattice_pair_h1(R, V, M), " +
			"    «waH1Map») ∧ " +
			"finite_dimensional(restrict_ring(R, k), «waKernelModule») ∧ " +
			"restrict_module(lattice_pair_h0(V, M), «waH0Kernel») = lattice_pair_h0(V, M') ∧ " +
			"«waKerCBarKernel» = «waH0Image» ∧ " +
			"«waH1Kernel» = «waKerCBarImage» ∧ " +
			"restrict_module(lattice_pair_h1(R, V, M), «waH1Image») = lattice_pair_h1(R, V, M)",
		Abbrev: Abbrev{
			{Name: "waToClasses", Text: "λv:B. (left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M')))"},
			{Name: "waH0Kernel", Text: "group_kernel(«waKernelModule».zero, " +
				"    lattice_pair_h0(V, M).carrier, " +
				"    «waToClasses»)"},
			{Name: "waKerCBarKernel", Text: "group_kernel(lattice_pair_h1(R, V, M').zero, " +
				"    «waKernelModule».carrier, " +
				"    lattice_pair_connecting(V))"},
			{Name: "waH1Kernel", Text: "group_kernel(lattice_pair_h1(R, V, M).zero, " +
				"    lattice_pair_h1(R, V, M').carrier, " +
				"    «waH1Map»)"},
			{Name: "waH0Image", Text: "image(«waToClasses», lattice_pair_h0(V, M).carrier)"},
			{Name: "waKerCBarImage", Text: "image(lattice_pair_connecting(V), «waKernelModule».carrier)"},
			{Name: "waH1Image", Text: "image(«waH1Map», lattice_pair_h1(R, V, M').carrier)"},
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
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0",
				"and in chart 1",
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁",
				"M₀/M'₀ is finite over k",
				"M₁/M'₁ is finite over k")
			datum, subfieldK, kIn0 := hypotheses[0], hypotheses[1], hypotheses[2]
			subringK := a.Have(
				"k is a subring of R",
				"subring(R, k)",
				By(lattice_pair.ChartFieldSubring.At(R, A0, A1, t, s, k, inv), datum, subfieldK, kIn0))
			maps := a.Have(
				"the maps from sections to chart classes, the connecting map, and the map on H¹ are k-linear",
				"module_homomorphism(restrict_ring(R, k), "+
					"    lattice_pair_h0(V, M), "+
					"    «waKernelModule», "+
					"    «waToClasses») ∧ "+
					"module_homomorphism(restrict_ring(R, k), "+
					"    «waKernelModule», "+
					"    lattice_pair_h1(R, V, M'), "+
					"    lattice_pair_connecting(V)) ∧ "+
					"module_homomorphism(restrict_ring(R, k), "+
					"    lattice_pair_h1(R, V, M'), "+
					"    lattice_pair_h1(R, V, M), "+
					"    «waH1Map»)",
				By(given, subringK, SixTermMaps.At(R, A0, A1, t, s, k, V, M, MPrime)))
			finiteKerCBar := a.Have(
				"ker c̄ is finite over k",
				"finite_dimensional(restrict_ring(R, k), «waKernelModule»)",
				By(given, PairDifferenceQuotient.At(R, A0, A1, t, s, k, inv, V, M, MPrime)))
			quotientOnto := a.Have(
				"c̄ reaches every overlap class",
				"image(lattice_pair_quotient_difference(R, V, M'), «waQuotientPairs») = «waQ01Carrier»",
				By(given, PairDifferenceQuotient.At(R, A0, A1, t, s, k, inv, V, M, MPrime)))
			h1Onto := a.Have(
				"H¹(M') maps onto H¹(M)",
				"«waH1Image» = lattice_pair_h1(R, V, M).carrier",
				By(given, quotientOnto, ConnectingCokernel.At(R, A0, A1, V, M, MPrime)))
			kerCBarKernel := a.Have(
				"the kernel of δ on ker c̄ is the image of H⁰(M)",
				"«waKerCBarKernel» = «waH0Image»",
				By(given, ConnectingKernel.At(R, A0, A1, V, M, MPrime), module_homomorphism.ExactAtDef))
			h1Kernel := a.Have(
				"the kernel on H¹ is the image of ker c̄",
				"«waH1Kernel» = «waKerCBarImage»",
				By(given, ConnectingCokernel.At(R, A0, A1, V, M, MPrime), module_homomorphism.ExactAtDef))
			h0Exact := a.Unfolded(a.Have(
				"the sequence is exact at H⁰(M)",
				"exact_at(«waKernelModule».zero, "+
					"    lattice_pair_h0(V, M').carrier, "+
					"    lattice_pair_h0(V, M).carrier, "+
					"    identity_map, "+
					"    «waToClasses»)",
				By(given, SixTermH0Exact.At(R, A0, A1, V, M, MPrime))), module_homomorphism.ExactAtDef)
			h0Kernel := a.Have(
				"the kernel on H⁰ is H⁰(M')",
				"«waH0Kernel» = lattice_pair_h0(V, M').carrier",
				Simp(
					Fwd(lattice_pair.LatticePairH0Def),
					Fwd(LatticePairQuotientKernelDef),
					Fwd(module_record.RestrictModuleDef),
					Fwd(module_record.ProductModuleDef),
					Fwd(submodule.QuotientModuleDef)),
				Simp(Rev(h0Exact), Fwd(functions.IdentityApply), Fwd(set_image.ImageIdentity)),
				Refl())
			h0Restriction := a.Have(
				"H⁰(M') keeps the operations of H⁰(M)",
				"restrict_module(lattice_pair_h0(V, M), lattice_pair_h0(V, M').carrier) = lattice_pair_h0(V, M')",
				Simp(Fwd(lattice_pair.LatticePairH0Def), Fwd(module_record.RestrictModuleDef)),
				Refl())
			h1ImageModule := a.Have(
				"the image module on H¹ is H¹(M)",
				"restrict_module(lattice_pair_h1(R, V, M), «waH1Image») = lattice_pair_h1(R, V, M)",
				Simp(Fwd(h1Onto), Fwd(module_record.RestrictModuleCarrier)),
				Refl())
			a.Show(
				"the three maps are k-linear, ker c̄ is finite, and the "+
					"sequence is exact at H⁰(M), at ker c̄, at H¹(M') and at H¹(M)",
				By(maps, finiteKerCBar, h0Kernel, h0Restriction, kerCBarKernel, h1Kernel, h1ImageModule))
		}),
})}

// EulerSubpairFinite — for a sub-pair with finite-dimensional chart
// quotients, M has finite-dimensional cohomology exactly when M' does.
// The six-term sequence over k (SixTermSequence) carries finiteness
// across in each degree. In degree zero, H⁰(M') is the kernel of
// H⁰(M) → ker c̄: inside a finite H⁰(M) it is finite (SubmoduleDim), and
// a finite H⁰(M') with an image inside the finite ker c̄ (SubmoduleDim)
// makes H⁰(M) finite (DimFiniteOfKernelAndImage). In degree one, H¹(M')
// maps onto H¹(M) with kernel the image of ker c̄ under δ, finite as an
// image of the finite ker c̄ (ImageDim): a finite H¹(M) makes H¹(M') finite
// (DimFiniteOfKernelAndImage), and a finite H¹(M') has the finite image
// H¹(M) (ImageDim).
var EulerSubpairFinite = eulerSubpairFiniteThm{family.Add(registry.ProofEntry{
	Name: "EulerSubpairFinite",
	Key:  "prop_b9db4ba357b2887c",
	Reading: "The chart quotients enter through SixTermSequence: both degrees read ker c̄ finite, " +
		"and degree one reads H¹(M') → H¹(M) onto, which c̄ onto Q₀₁ gives (ConnectingCokernel).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
			"finite_dimensional(restrict_ring(R, k), «waQ0»)",
			"finite_dimensional(restrict_ring(R, k), «waQ1»)",
		},
		Conclusion: "lattice_pair_finite(R, k, V, M) ⇔ lattice_pair_finite(R, k, V, M')",
		Abbrev: Abbrev{
			{Name: "waToClasses", Text: "λv:B. (left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M')))"},
			{Name: "waH0Kernel", Text: "group_kernel(«waKernelModule».zero, " +
				"    lattice_pair_h0(V, M).carrier, " +
				"    «waToClasses»)"},
			{Name: "waH1Kernel", Text: "group_kernel(lattice_pair_h1(R, V, M).zero, " +
				"    lattice_pair_h1(R, V, M').carrier, " +
				"    «waH1Map»)"},
			{Name: "waH0Image", Text: "image(«waToClasses», lattice_pair_h0(V, M).carrier)"},
			{Name: "waKerCBarImage", Text: "image(lattice_pair_connecting(V), «waKernelModule».carrier)"},
			{Name: "waH1Image", Text: "image(«waH1Map», lattice_pair_h1(R, V, M').carrier)"},
			{Name: "waH0KernelModule", Text: "restrict_module(lattice_pair_h0(V, M), «waH0Kernel»)"},
			{Name: "waH1KernelModule", Text: "restrict_module(lattice_pair_h1(R, V, M'), «waH1Kernel»)"},
			{Name: "waH0ImageModule", Text: "restrict_module(«waKernelModule», «waH0Image»)"},
			{Name: "waKerCBarImageModule", Text: "restrict_module(lattice_pair_h1(R, V, M'), " +
				"    «waKerCBarImage»)"},
			{Name: "waH1ImageModule", Text: "restrict_module(lattice_pair_h1(R, V, M), «waH1Image»)"},
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
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0",
				"and in chart 1",
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁",
				"M₀/M'₀ is finite over k",
				"M₁/M'₁ is finite over k")
			// k is a field under the operations of R restricted to it: the scalar
			// field the dimension laws below are read at.
			fieldK := a.Have(
				"k is a field under the operations of R restricted to k, which are R's",
				"ring_subfield(restrict_ring(R, k), inv, k)",
				By(hypotheses[1], field.RingSubfieldRestrict.At(R, k, inv, k)))
			scalars := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			h0 := a.TermAs[ModuleOps[A, B]]("lattice_pair_h0(V, M)")
			kerCBar := a.TermAs[ModuleOps[A, Prod[Set[B], Set[B]]]]("«waKernelModule»")
			h1Prime := a.TermAs[ModuleOps[A, Set[B]]]("lattice_pair_h1(R, V, M')")
			h1 := a.TermAs[ModuleOps[A, Set[B]]]("lattice_pair_h1(R, V, M)")
			toClasses := a.TermAs[Fun[B, Prod[Set[B], Set[B]]]]("«waToClasses»")
			connecting := a.TermAs[Fun[Prod[Set[B], Set[B]], Set[B]]]("lattice_pair_connecting(V)")
			onH1 := a.TermAs[Fun[Set[B], Set[B]]]("«waH1Map»")
			sequence := SixTermSequence.At(R, A0, A1, t, s, k, inv, V, M, MPrime)
			maps := a.Conjuncts(
				a.Have(
					"the maps from sections to chart classes, the connecting map, and the map on H¹ are k-linear",
					"module_homomorphism(restrict_ring(R, k), "+
						"    lattice_pair_h0(V, M), "+
						"    «waKernelModule», "+
						"    «waToClasses») ∧ "+
						"module_homomorphism(restrict_ring(R, k), "+
						"    «waKernelModule», "+
						"    lattice_pair_h1(R, V, M'), "+
						"    lattice_pair_connecting(V)) ∧ "+
						"module_homomorphism(restrict_ring(R, k), "+
						"    lattice_pair_h1(R, V, M'), "+
						"    lattice_pair_h1(R, V, M), "+
						"    «waH1Map»)",
					By(given, sequence)),
				"the map from sections to chart classes is k-linear",
				"the connecting map is k-linear",
				"the map on H¹ is k-linear")
			classesHom, connectingHom, h1Hom := maps[0], maps[1], maps[2]
			finiteKerCBar := a.Have(
				"ker c̄ is finite over k",
				"finite_dimensional(restrict_ring(R, k), «waKernelModule»)",
				By(given, sequence))

			h0KernelModule := a.Have(
				"the kernel module on H⁰ is H⁰(M')",
				"«waH0KernelModule» = lattice_pair_h0(V, M')",
				By(given, sequence))
			h0Finite := a.Have(
				"H⁰(M) is finite exactly when H⁰(M') is finite",
				"finite_dimensional(restrict_ring(R, k), lattice_pair_h0(V, M)) ⇔ "+
					"finite_dimensional(restrict_ring(R, k), lattice_pair_h0(V, M'))",
				Derive(func(b *Argument) {
					kernelSet := b.TermAs[Set[B]]("«waH0Kernel»")
					imageSet := b.TermAs[Set[Prod[Set[B], Set[B]]]]("«waH0Image»")
					b.Iff()
					b.Forward(
						"the kernel in a finite H⁰(M) is finite",
						func(c *Argument, finite Fact) {
							finiteKernel := c.Have(
								"the kernel module on H⁰ is finite",
								"finite_dimensional(restrict_ring(R, k), «waH0KernelModule»)",
								By(
									fieldK,
									finite,
									module_homomorphism.HomSource.Read(classesHom),
									module_homomorphism.KernelSubmodule.Read(classesHom),
									module_dimension.SubmoduleDim.At(scalars, h0, inv, kernelSet)))
							c.Show(
								"that kernel module is H⁰(M')",
								By(finiteKernel, h0KernelModule))
						})
					b.Backward(
						"a finite H⁰(M') and a finite image make H⁰(M) finite",
						func(c *Argument, finite Fact) {
							finiteKernel := c.Have(
								"the kernel module on H⁰ is finite because it is H⁰(M')",
								"finite_dimensional(restrict_ring(R, k), «waH0KernelModule»)",
								By(finite, h0KernelModule))
							finiteImage := c.Have(
								"the image in the finite module ker c̄ is finite",
								"finite_dimensional(restrict_ring(R, k), «waH0ImageModule»)",
								By(
									fieldK,
									finiteKerCBar,
									module_homomorphism.HomTarget.Read(classesHom),
									module_homomorphism.ImageSubmodule.Read(classesHom),
									module_dimension.SubmoduleDim.At(scalars, kerCBar, inv, imageSet)))
							c.Show(
								"the finite kernel and finite image make H⁰(M) finite",
								By(
									fieldK,
									classesHom,
									finiteKernel,
									finiteImage,
									module_dimension.DimFiniteOfKernelAndImage.At(scalars, h0, inv, kerCBar, toClasses)))
						})
				}))

			h1Kernel := a.Have(
				"the kernel on H¹ is the image of ker c̄",
				"«waH1Kernel» = «waKerCBarImage»",
				By(given, sequence))
			h1ImageModule := a.Have(
				"the image module on H¹ is H¹(M)",
				"«waH1ImageModule» = lattice_pair_h1(R, V, M)",
				By(given, sequence))
			finiteKerCBarImage := a.Have(
				"the image of ker c̄ is finite, ker c̄ being finite",
				"finite_dimensional(restrict_ring(R, k), «waKerCBarImageModule»)",
				By(
					fieldK,
					connectingHom,
					finiteKerCBar,
					module_dimension.ImageDim.At(scalars, inv, kerCBar, h1Prime, connecting)))
			finiteH1Kernel := a.Have(
				"so the kernel on H¹ is finite",
				"finite_dimensional(restrict_ring(R, k), «waH1KernelModule»)",
				By(finiteKerCBarImage, h1Kernel))
			h1Finite := a.Have(
				"H¹(M) is finite exactly when H¹(M') is finite",
				"finite_dimensional(restrict_ring(R, k), lattice_pair_h1(R, V, M)) ⇔ "+
					"finite_dimensional(restrict_ring(R, k), lattice_pair_h1(R, V, M'))",
				Derive(func(b *Argument) {
					b.Iff()
					b.Forward(
						"a finite H¹(M) and the finite kernel make H¹(M') finite",
						func(c *Argument, finite Fact) {
							finiteImage := c.Have(
								"the image module on H¹ is finite because it is H¹(M)",
								"finite_dimensional(restrict_ring(R, k), «waH1ImageModule»)",
								By(finite, h1ImageModule))
							c.Show(
								"the finite kernel and finite image make H¹(M') finite",
								By(
									fieldK,
									h1Hom,
									finiteH1Kernel,
									finiteImage,
									module_dimension.DimFiniteOfKernelAndImage.At(scalars, h1Prime, inv, h1, onH1)))
						})
					b.Backward(
						"a finite H¹(M') has the finite image H¹(M)",
						func(c *Argument, finite Fact) {
							finiteImage := c.Have(
								"the image of H¹(M') is finite",
								"finite_dimensional(restrict_ring(R, k), «waH1ImageModule»)",
								By(fieldK, h1Hom, finite, module_dimension.ImageDim.At(scalars, inv, h1Prime, h1, onH1)))
							c.Show(
								"that image is H¹(M)",
								By(finiteImage, h1ImageModule))
						})
				}))
			a.Show(
				"finiteness in both cohomological degrees is unchanged",
				Simp(Fwd(lattice_pair.LatticePairFiniteDef)),
				By(h0Finite, h1Finite))
		}),
})}

// EulerAdditive — the three-term formula: for a sub-pair M' ⊆ M with
// finite-dimensional chart quotients and finite cohomology, M has finite
// cohomology and χ(M) − χ(M') = dim Q₀ + dim Q₁ − dim Q₀₁. M is finite by
// EulerSubpairFinite. Rank–nullity at the three maps
// H⁰(M) → ker c̄ → H¹(M') → H¹(M), the sequence exact at H⁰(M), ker c̄ and
// H¹(M') and onto H¹(M) (SixTermSequence), gives
// dim H⁰(M) = dim H⁰(M') + dim of the image of H⁰(M), dim ker c̄ = that
// dimension + dim δ(ker c̄), and dim H¹(M') = dim δ(ker c̄) + dim H¹(M); the
// image dimensions cancel, so χ(M) − χ(M') = dim ker c̄, which is
// dim Q₀ + dim Q₁ − dim Q₀₁ (PairDifferenceQuotient).
var EulerAdditive = eulerAdditiveThm{family.Add(registry.ProofEntry{
	Name: "EulerAdditive",
	Key:  "prop_db05b4071888b51d",
	Reading: "lattice_pair_finite(M') is load-bearing: without it the dimensions " +
		"are unspecified numbers and the subtraction says nothing. Exactness at H¹(M), " +
		"H¹(M') mapping onto it, comes from c̄ being onto Q₀₁ (ConnectingCokernel).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M M':prod(set(B), set(B)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"lattice_pair(R, A₀, A₁, V, M)",
			"lattice_pair(R, A₀, A₁, V, M')",
			"fst(M') ⊆ fst(M)",
			"snd(M') ⊆ snd(M)",
			"finite_dimensional(restrict_ring(R, k), «waQ0»)",
			"finite_dimensional(restrict_ring(R, k), «waQ1»)",
			"lattice_pair_finite(R, k, V, M')",
		},
		Conclusion: "lattice_pair_finite(R, k, V, M) ∧ " +
			"lattice_pair_euler(R, k, V, M) - lattice_pair_euler(R, k, V, M') = " +
			"int_of_num(module_dim(restrict_ring(R, k), «waQ0»)) + " +
			"int_of_num(module_dim(restrict_ring(R, k), «waQ1»)) - " +
			"int_of_num(module_dim(restrict_ring(R, k), «waQ01»))",
		Abbrev: Abbrev{
			{Name: "waToClasses", Text: "λv:B. (left_coset(V.add, v, fst(M')), left_coset(V.add, v, snd(M')))"},
			{Name: "waH0Kernel", Text: "group_kernel(«waKernelModule».zero, " +
				"    lattice_pair_h0(V, M).carrier, " +
				"    «waToClasses»)"},
			{Name: "waKerCBarKernel", Text: "group_kernel(lattice_pair_h1(R, V, M').zero, " +
				"    «waKernelModule».carrier, " +
				"    lattice_pair_connecting(V))"},
			{Name: "waH1Kernel", Text: "group_kernel(lattice_pair_h1(R, V, M).zero, " +
				"    lattice_pair_h1(R, V, M').carrier, " +
				"    «waH1Map»)"},
			{Name: "waH0Image", Text: "image(«waToClasses», lattice_pair_h0(V, M).carrier)"},
			{Name: "waKerCBarImage", Text: "image(lattice_pair_connecting(V), «waKernelModule».carrier)"},
			{Name: "waH1Image", Text: "image(«waH1Map», lattice_pair_h1(R, V, M').carrier)"},
			{Name: "waH0KernelModule", Text: "restrict_module(lattice_pair_h0(V, M), «waH0Kernel»)"},
			{Name: "waH0ImageModule", Text: "restrict_module(«waKernelModule», «waH0Image»)"},
			{Name: "waKerCBarImageModule", Text: "restrict_module(lattice_pair_h1(R, V, M'), " +
				"    «waKerCBarImage»)"},
			{Name: "waH1ImageModule", Text: "restrict_module(lattice_pair_h1(R, V, M), «waH1Image»)"},
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
			M, MPrime *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in chart 0",
				"and in chart 1",
				"M is a lattice pair",
				"so is M'",
				"M'₀ lies in M₀",
				"M'₁ lies in M₁",
				"M₀/M'₀ is finite over k",
				"M₁/M'₁ is finite over k",
				"M' has finite cohomology")
			finiteMPrime := hypotheses[10]
			// k is a field under the operations of R restricted to it: the scalar
			// field the rank–nullity instances below are read at.
			fieldK := a.Have(
				"k is a field under the operations of R restricted to k, which are R's",
				"ring_subfield(restrict_ring(R, k), inv, k)",
				By(hypotheses[1], field.RingSubfieldRestrict.At(R, k, inv, k)))
			scalars := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			h0 := a.TermAs[ModuleOps[A, B]]("lattice_pair_h0(V, M)")
			kerCBar := a.TermAs[ModuleOps[A, Prod[Set[B], Set[B]]]]("«waKernelModule»")
			h1Prime := a.TermAs[ModuleOps[A, Set[B]]]("lattice_pair_h1(R, V, M')")
			h1 := a.TermAs[ModuleOps[A, Set[B]]]("lattice_pair_h1(R, V, M)")
			toClasses := a.TermAs[Fun[B, Prod[Set[B], Set[B]]]]("«waToClasses»")
			connecting := a.TermAs[Fun[Prod[Set[B], Set[B]], Set[B]]]("lattice_pair_connecting(V)")
			onH1 := a.TermAs[Fun[Set[B], Set[B]]]("«waH1Map»")
			sequence := SixTermSequence.At(R, A0, A1, t, s, k, inv, V, M, MPrime)
			maps := a.Conjuncts(
				a.Have(
					"the maps from sections to chart classes, the connecting map, and the map on H¹ are k-linear",
					"module_homomorphism(restrict_ring(R, k), "+
						"    lattice_pair_h0(V, M), "+
						"    «waKernelModule», "+
						"    «waToClasses») ∧ "+
						"module_homomorphism(restrict_ring(R, k), "+
						"    «waKernelModule», "+
						"    lattice_pair_h1(R, V, M'), "+
						"    lattice_pair_connecting(V)) ∧ "+
						"module_homomorphism(restrict_ring(R, k), "+
						"    lattice_pair_h1(R, V, M'), "+
						"    lattice_pair_h1(R, V, M), "+
						"    «waH1Map»)",
					By(given, sequence)),
				"the map from sections to chart classes is k-linear",
				"the connecting map is k-linear",
				"the map on H¹ is k-linear")
			classesHom, connectingHom, h1Hom := maps[0], maps[1], maps[2]
			finiteKerCBar := a.Have(
				"ker c̄ is finite over k",
				"finite_dimensional(restrict_ring(R, k), «waKernelModule»)",
				By(given, sequence))
			h0KernelModule := a.Have(
				"the kernel module on H⁰ is H⁰(M')",
				"«waH0KernelModule» = lattice_pair_h0(V, M')",
				By(given, sequence))
			kerCBarKernel := a.Have(
				"the kernel of δ on ker c̄ is the image of H⁰(M)",
				"«waKerCBarKernel» = «waH0Image»",
				By(given, sequence))
			h1Kernel := a.Have(
				"the kernel on H¹ is the image of ker c̄",
				"«waH1Kernel» = «waKerCBarImage»",
				By(given, sequence))
			h1ImageModule := a.Have(
				"the image module on H¹ is H¹(M)",
				"«waH1ImageModule» = lattice_pair_h1(R, V, M)",
				By(given, sequence))
			finiteM := a.Have(
				"M has finite cohomology because M' does",
				"lattice_pair_finite(R, k, V, M)",
				By(given, EulerSubpairFinite.At(R, A0, A1, t, s, k, inv, V, M, MPrime)))
			finiteH0 := a.Conjuncts(
				a.Unfolded(finiteM, lattice_pair.LatticePairFiniteDef),
				"H⁰(M) is finite over k",
				"H¹(M) is finite over k")[0]
			finiteH1Prime := a.Conjuncts(
				a.Unfolded(finiteMPrime, lattice_pair.LatticePairFiniteDef),
				"H⁰(M') is finite over k",
				"H¹(M') is finite over k")[1]

			// Rank–nullity at the three consecutive maps identifies the two
			// image dimensions, which cancel in the Euler difference. A
			// RankNullity instance spells the carriers and zeros of H⁰(M), ker c̄
			// and H¹(M') by their parts; the goals and the kernel and image
			// equations taken from the sequence spell them as projections, which
			// the projection equations (ModCarrierDef, ModZeroDef) read at the
			// parts.
			h0KernelParts := a.Simplified(
				h0KernelModule,
				Fwd(module_record.ModCarrierDef),
				Fwd(module_record.ModZeroDef))
			kerCBarKernelParts := a.Simplified(
				kerCBarKernel,
				Fwd(module_record.ModCarrierDef),
				Fwd(module_record.ModZeroDef))
			h1KernelParts := a.Simplified(
				h1Kernel,
				Fwd(module_record.ModCarrierDef),
				Fwd(module_record.ModZeroDef))
			h1ImageParts := a.Simplified(
				h1ImageModule,
				Fwd(module_record.ModCarrierDef),
				Fwd(module_record.ModZeroDef))
			h0Rank := a.Have(
				"rank–nullity at H⁰(M) → ker c̄, whose kernel is H⁰(M'): dim "+
					"H⁰(M') plus the dimension of the image of H⁰(M) is dim H⁰(M)",
				"module_dim(restrict_ring(R, k), lattice_pair_h0(V, M')) + "+
					"module_dim(restrict_ring(R, k), «waH0ImageModule») = "+
					"module_dim(restrict_ring(R, k), lattice_pair_h0(V, M))",
				Simp(Fwd(module_record.ModCarrierDef), Fwd(module_record.ModZeroDef)),
				By(
					fieldK,
					classesHom,
					finiteH0,
					h0KernelParts,
					module_homomorphism.HomSource.Read(classesHom),
					module_homomorphism.HomTarget.Read(classesHom),
					module_dimension.RankNullity.At(scalars, h0, inv, kerCBar, toClasses)))
			kerCBarRank := a.Have(
				"rank–nullity at δ, whose kernel is the image of H⁰(M): the "+
					"dimensions of the images of H⁰(M) and of ker c̄ add up to dim ker c̄",
				"module_dim(restrict_ring(R, k), «waH0ImageModule») + "+
					"module_dim(restrict_ring(R, k), «waKerCBarImageModule») = "+
					"module_dim(restrict_ring(R, k), «waKernelModule»)",
				Simp(Fwd(module_record.ModCarrierDef), Fwd(module_record.ModZeroDef)),
				By(
					fieldK,
					connectingHom,
					finiteKerCBar,
					kerCBarKernelParts,
					module_homomorphism.HomSource.Read(connectingHom),
					module_homomorphism.HomTarget.Read(connectingHom),
					module_dimension.RankNullity.At(scalars, kerCBar, inv, h1Prime, connecting)))
			h1Rank := a.Have(
				"rank–nullity at H¹(M') → H¹(M), onto, whose kernel is the image "+
					"of ker c̄: that image's dimension plus dim H¹(M) is dim H¹(M')",
				"module_dim(restrict_ring(R, k), «waKerCBarImageModule») + "+
					"module_dim(restrict_ring(R, k), lattice_pair_h1(R, V, M)) = "+
					"module_dim(restrict_ring(R, k), lattice_pair_h1(R, V, M'))",
				Simp(Fwd(module_record.ModCarrierDef), Fwd(module_record.ModZeroDef)),
				By(
					fieldK,
					h1Hom,
					finiteH1Prime,
					h1KernelParts,
					h1ImageParts,
					module_homomorphism.HomSource.Read(h1Hom),
					module_homomorphism.HomTarget.Read(h1Hom),
					module_dimension.RankNullity.At(scalars, h1Prime, inv, h1, onH1)))
			quotientDimensions := a.Have(
				"dim ker c̄ plus dim Q₀₁ is dim Q₀ plus dim Q₁",
				"module_dim(restrict_ring(R, k), «waKernelModule») + module_dim(restrict_ring(R, k), «waQ01») = "+
					"module_dim(restrict_ring(R, k), «waQ0») + module_dim(restrict_ring(R, k), «waQ1»)",
				By(given, PairDifferenceQuotient.At(R, A0, A1, t, s, k, inv, V, M, MPrime)))
			eulerKernel := a.Have(
				"the image dimensions cancel, leaving the Euler difference equal to dim ker c̄",
				"lattice_pair_euler(R, k, V, M) - lattice_pair_euler(R, k, V, M') = "+
					"int_of_num(module_dim(restrict_ring(R, k), «waKernelModule»))",
				Simp(
					Fwd(lattice_pair.LatticePairEulerDef),
					Fwd(lattice_pair.LatticePairH0DimDef),
					Fwd(lattice_pair.LatticePairH1DimDef)),
				ByArith(h0Rank, kerCBarRank, h1Rank))
			euler := a.Have(
				"the Euler difference is dim Q₀ plus dim Q₁ minus dim Q₀₁",
				"lattice_pair_euler(R, k, V, M) - lattice_pair_euler(R, k, V, M') = "+
					"int_of_num(module_dim(restrict_ring(R, k), «waQ0»)) + "+
					"int_of_num(module_dim(restrict_ring(R, k), «waQ1»)) - "+
					"int_of_num(module_dim(restrict_ring(R, k), «waQ01»))",
				ByArith(eulerKernel, quotientDimensions))
			a.Show(
				"M has finite cohomology and the three-term Euler difference formula",
				By(finiteM, euler))
		}),
})}
