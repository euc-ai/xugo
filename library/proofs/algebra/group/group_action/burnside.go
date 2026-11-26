// burnside.go — counting by orbits: Burnside's lemma, the subgroups of a
// group of prime order, and the points a group of prime-power order fixes,
// counted mod p over the orbits.

package group_action

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// SumStabilizersOverOrbit — for a finite group, the stabilizers of the
// points of one orbit add up to the order of the group. A point y of the
// orbit of x has the orbit of x (OrbitOfMember), so the orbit–stabilizer
// theorem at y and at x gives the orbit's size times either stabilizer's
// order as the order of the group; the orbit is not empty, so every
// stabilizer on it has the order of x's, and the sum is the orbit's size
// times that order.
var SumStabilizersOverOrbit = sumStabilizersOverOrbitThm{family.Add(registry.ProofEntry{
	Name: "SumStabilizersOverOrbit",
	Key:  "prop_976dc77879dffc1e",
	Build: GroupAction.Law(Statement{
		Binders: "∀x:B.",
		Hypotheses: []string{
			"finite(G.carrier)",
			"x ∈ X",
		},
		Conclusion: "Σ_{y∈group_orbit(G, act, x)} card(group_stabilizer(G, act, y)) = card(G.carrier)",
	},
		func(a *Argument, action, finite Fact, x *Expr[B], xIn Fact) {
			xm := a.MemberOf[on.Any](x, xIn)
			orbit := a.TermAs[Set[B]]("group_orbit(G, act, x)")
			finiteOrbit := a.Have(
				"the orbit is finite, the image of the finite G.carrier",
				"finite(group_orbit(G, act, x))",
				Simp(Fwd(GroupOrbitDef)),
				By(finite, finite_set.FiniteImage))
			count := a.Have(
				"the orbit–stabilizer theorem at x",
				"card(G.carrier) = card(group_orbit(G, act, x)) * card(group_stabilizer(G, act, x))",
				By(OrbitStabilizer.Read(action), finite, xm))
			nonzero := a.Have(
				"the orbit holds x, so its size is not 0",
				"card(group_orbit(G, act, x)) ≠ 0",
				By(
					Normalized,
					finiteOrbit,
					InOwnOrbit.Read(action).At(xm),
					cardinality.CardEqZero.At(orbit),
					set_basic.MemberNotEmpty.At(orbit)))
			sameSize := a.Have(
				"every point y of the orbit has a stabilizer of the order of x's",
				Statement{
					Binders: "∀y:B.",
					Hypotheses: []string{
						"y ∈ group_orbit(G, act, x)",
					},
					Conclusion: "card(group_stabilizer(G, act, y)) = card(group_stabilizer(G, act, x))",
				},
				Derive(func(b *Argument) {
					y := b.FixAs[B]("y")
					yIn := b.Assume()
					yX := b.Have(
						"y lies in X, the orbit of x lying in X",
						"y ∈ X",
						By(OrbitSubset.Read(action).At(xm), yIn, set_basic.SubsetDef))
					ym := b.MemberOf[on.Any](y, yX)
					b.Show(
						"y has the orbit of x, so the orbit's size times either "+
							"stabilizer's order is the group's, and that size is not 0",
						By(
							finite,
							yIn,
							count,
							nonzero,
							OrbitStabilizer.Read(action).At(ym),
							OrbitOfMember.Read(action).At(xm, y),
							nat_arith.MulEqLCancel.At(
								b.TermAs[Nat]("card(group_orbit(G, act, x))"),
								b.TermAs[Nat]("card(group_stabilizer(G, act, y))"),
								b.TermAs[Nat]("card(group_stabilizer(G, act, x))"))))
				}))
			a.Show(
				"so the sum over the orbit is the orbit's size times the order of x's stabilizer",
				CalcEq(
					Leg(
						a.Term("Σ_{y∈group_orbit(G, act, x)} card(group_stabilizer(G, act, x))"),
						"every stabilizer on the orbit has the order of x's",
						By(nat_sum.Congruence, sameSize)),
					Leg(
						a.Term("card(group_orbit(G, act, x)) * card(group_stabilizer(G, act, x))"),
						"a constant summed over the orbit",
						By(nat_sum.SumConst, finiteOrbit)),
					FinalLeg(
						"which is the order of the group",
						By(count)),
				))
		}),
})}

// Burnside — Burnside's lemma: the number of orbits times the order of
// the group is the total number of fixed points. Count the pairs (g, x)
// with g fixing x point by point, grouped by orbit (SumOverOrbits).
var Burnside = burnsideThm{family.Add(registry.ProofEntry{
	Name: "Burnside",
	Key:  "prop_b9c7db220d060505",
	Build: GroupAction.Law(Statement{
		Hypotheses: []string{
			"finite(G.carrier)",
			"finite(X)",
		},
		Conclusion: "card(«orbits») * card(G.carrier) = " +
			"Σ_{g∈G.carrier} card(group_fixed_points(X, act, g))",
	},
		func(a *Argument, action, finiteG, finiteX Fact) {
			perOrbit := a.Have(
				"over each orbit, the orbit of a point of X, the stabilizers add up to the order of the group",
				"∀O:set(B). O ∈ «orbits» ⇒ Σ_{y∈O} card(group_stabilizer(G, act, y)) = card(G.carrier)",
				Simp(Fwd(set_image.ForallInImage)),
				By(finiteG, SumStabilizersOverOrbit.Read(action)))
			a.Show(
				"count the pairs (g, x) with g fixing x orbit by "+
					"orbit, then point by point, then element by element",
				CalcEq(
					Leg(
						a.Term("Σ_{O∈«orbits»} card(G.carrier)"),
						"the order of the group once for each of the finitely many orbits, the image of the finite X",
						By(nat_sum.SumConst, finite_set.FiniteImage, finiteX)),
					Leg(
						a.Term("Σ_{O∈«orbits»} Σ_{y∈O} card(group_stabilizer(G, act, y))"),
						"which over each orbit is the sum of the stabilizers' orders",
						By(nat_sum.Congruence, perOrbit)),
					Leg(
						a.Term("Σ_{x∈X} card(group_stabilizer(G, act, x))"),
						"grouping the points of X by their orbits",
						By(
							finiteX,
							SumOverOrbits.Read(action).At(a.TermAs[Fun[B, Nat]]("λy:B. card(group_stabilizer(G, act, y))")))),
					FinalLeg(
						"the pairs (g, x) with g fixing x counted by x, and so by g",
						Simp(Fwd(GroupStabilizerDef), Fwd(GroupFixedPointsDef)),
						By(nat_sum.DoubleCounting, finiteG, finiteX)),
				))
		}),
})}

// ---------------------------------------------------------------------------
// Groups of prime order
// ---------------------------------------------------------------------------

// PrimeOrderSubgroup — a subgroup of a finite group of prime order is
// trivial or the whole group: its order divides the group's
// (finite_group.LagrangeDividesOn), so it is 1 or the prime, and a subset of a
// finite set of the same size is the set (cardinality.CardSubsetEq),
// {G.one} inside H in the one case and H inside G.carrier in the other.
var PrimeOrderSubgroup = primeOrderSubgroupThm{family.Add(registry.ProofEntry{
	Name: "PrimeOrderSubgroup",
	Key:  "prop_4c1a5c944e2a3c1d",
	Build: group.GroupOn.Law(Statement{
		Binders: "∀H:set(A).",
		Hypotheses: []string{
			"finite(G.carrier)",
			"nat_prime(card(G.carrier))",
			"subgroup(G, H)",
		},
		Conclusion: "H = {G.one} ∨ H = G.carrier",
	},
		func(a *Argument, grp group.GroupFact[on.G], finite, prime Fact, H *Expr[Set[A]], subgroup Fact) {
			G := a.TermAs[GroupOps[A]]("G")
			carrier, trivial := a.TermAs[Set[A]]("G.carrier"), a.TermAs[Set[A]]("{G.one}")
			inside := group.SubgroupSubset.Read(subgroup)
			sizes := a.Have(
				"by Lagrange's theorem the order of H divides the "+
					"prime order of the group, so it is 1 or the prime",
				"card(H) = 1 ∨ card(H) = card(G.carrier)",
				By(prime, subgroup, finite, nat_prime.PrimeDef, finite_group.LagrangeDividesOn.Read(grp).At(H)))
			a.Cases(a.TermAs[Bool]("card(H) = 1"))
			a.When(
				"of order 1, H is the identity alone, which it holds",
				func(b *Argument, single Fact) {
					holdsOne := b.Have(
						"H holds G.one",
						"{G.one} ⊆ H",
						By(subgroup, group.SubgroupOne, set_order.SingSubset))
					b.Show(
						"{G.one} has one point too, inside the finite H",
						By(
							single,
							holdsOne,
							subgroup,
							finite,
							cardinality.CardSing,
							cardinality.CardSubsetEq.At(trivial, H),
							finite_group.SubgroupFinite.At(G, H)))
				})
			a.Otherwise(
				"of the prime order, H is a subset of G.carrier as large as it",
				func(b *Argument, notSingle Fact) {
					b.Show(
						"so H is G.carrier",
						By(notSingle, sizes, inside, finite, cardinality.CardSubsetEq.At(H, carrier)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Groups of prime-power order
// ---------------------------------------------------------------------------

// PrimePowerFixedPoints — a p-group, p a prime, acting on a finite set
// fixes as many points as the set has, mod p. Its order is a power p ^ n,
// and by the orbit–stabilizer theorem the size of each orbit divides it, so
// it is a power p ^ k of p (nat_prime.PrimePowerDivisor). An orbit of size
// p ^ 0 = 1 is a point every element fixes, counted once on each side; a
// larger orbit has a size p divides and holds no point every element fixes.
// So over each orbit the points and the fixed points agree mod p, and
// summing over the orbits (SumOverOrbits) gives the congruence.
var PrimePowerFixedPoints = primePowerFixedPointsThm{family.Add(registry.ProofEntry{
	Name: "PrimePowerFixedPoints",
	Key:  "prop_c74a2ba6b0f8c39d",
	Build: GroupAction.Law(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"finite(X)",
			"nat_prime(p)",
			"p_group(G, p)",
		},
		Conclusion: "card(X) ≡ card(«fixedByAll») (mod p)",
		Abbrev: Abbrev{
			{Name: "fixedByAll", Text: "{x:B | x ∈ X ∧ ∀g:A. g ∈ G.carrier ⇒ act(g, x) = x}"},
			{Name: "indicator", Text: "λy:B. COND(∀g:A. g ∈ G.carrier ⇒ act(g, y) = y, 1, 0)"},
		},
	},
		func(a *Argument, action, finiteX Fact, p *Expr[Nat], prime, pGroup Fact) {
			finiteG := finite_group.PGroupFinite.Read(pGroup)
			n, order := a.UnpackAs[Nat](finite_group.PGroupPowerOrder.Read(pGroup).AsFact(), "n")
			finiteOrbit := a.Have(
				"every orbit is finite, an image of the finite group",
				"∀x:B. finite(group_orbit(G, act, x))",
				Simp(Fwd(GroupOrbitDef)),
				By(finiteG, finite_set.FiniteImage))
			perPoint := a.Have(
				"the orbit of a point of X has, mod p, as many points as points every element fixes",
				"∀x:B. x ∈ X ⇒ card(group_orbit(G, act, x)) ≡ Σ_{y∈group_orbit(G, act, x)} «indicator»(y) (mod p)",
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					xm := b.MemberOf[on.Any](x, xIn)
					orbit := b.TermAs[Set[B]]("group_orbit(G, act, x)")
					size := b.TermAs[Nat]("card(group_orbit(G, act, x))")
					divisor := b.Have(
						"by the orbit–stabilizer theorem the orbit's size divides the group's order, p ^ n",
						"card(group_orbit(G, act, x)) ∣ p ^ n",
						By(
							finiteG,
							order,
							OrbitStabilizer.Read(action).At(xm),
							nat_divides.DividesOwnMultiple.At(size, b.TermAs[Nat]("card(group_stabilizer(G, act, x))"))))
					k, power := b.ObtainAs[Nat](
						"so the orbit's size is a power of p",
						"∃k:num. k ≤ n ∧ card(group_orbit(G, act, x)) = p ^ k",
						By(prime, divisor, nat_prime.PrimePowerDivisor.At(p, n, size)))
					b.Cases(b.TermAs[Bool]("k = 0"))
					b.When(
						"an orbit of size p ^ 0 = 1 is a point every element fixes, counted once on each side",
						func(c *Argument, zero Fact) {
							one := c.Have(
								"the orbit has one point",
								"card(group_orbit(G, act, x)) = 1",
								By(zero, power, nat_arith.NatPow))
							contains := c.Have(
								"the orbit holds x",
								"{x} ⊆ group_orbit(G, act, x)",
								BySets(InOwnOrbit.Read(action).At(xm)))
							singleton := c.Have(
								"so the orbit is {x}, a finite set holding {x} with as many points",
								"group_orbit(G, act, x) = {x}",
								By(
									finiteOrbit.At(x),
									one,
									contains,
									cardinality.CardSubsetEq.At(c.TermAs[Set[B]]("{x}"), orbit),
									cardinality.CardSing.At(x)))
							fixed := c.Have(
								"so every element fixes x",
								"∀g:A. g ∈ G.carrier ⇒ act(g, x) = x",
								By(singleton, FixedIffSingletonOrbit.Read(action).At(xm)))
							c.Show(
								"the indicator summed over {x} is 1, the orbit's size",
								Unfold(nat_sum.NatSumDef),
								By(
									fixed,
									singleton,
									one,
									monoidal.Sing.At(c.TermAs[Op[Nat]]("+"), c.TermAs[Fun[B, Nat]]("«indicator»"), x),
									nat_sum.MonoidalNatAdd,
									nat_congruence.CongDef))
						})
					b.Otherwise(
						"an orbit of size p ^ k with k > 0 has a size p divides and holds no point every element fixes",
						func(c *Argument, nonzero Fact) {
							positive := c.Have(
								"k is at least 1",
								"1 ≤ k",
								ByArith(nonzero))
							multiple := c.Have(
								"so p, which is p ^ 1, divides p ^ k, the orbit's size",
								"p ∣ card(group_orbit(G, act, x))",
								By(
									Normalized,
									power,
									positive,
									nat_arith.PowOne.At(p),
									nat_divides.PowDividesPow.At(p, c.TermAs[Nat]("1"), k)))
							notOne := c.Have(
								"so the orbit's size, a multiple of the prime p, is not 1",
								"¬(card(group_orbit(G, act, x)) = 1)",
								ByArith(multiple, prime, nat_prime.PrimeAtLeastTwo.At(p), nat_divides.DividesOne.At(p)))
							noFixed := c.Have(
								"a point of the orbit every element fixes would make the orbit a singleton",
								"∀y:B. y ∈ group_orbit(G, act, x) ⇒ ¬∀g:A. g ∈ G.carrier ⇒ act(g, y) = y",
								Derive(func(d *Argument) {
									y := d.FixAs[B]("y")
									yIn := d.Assume()
									yX := d.Have(
										"y lies in X, as the orbit does",
										"y ∈ X",
										BySets(yIn, OrbitSubset.Read(action).At(xm)))
									ym := d.MemberOf[on.Any](y, yX)
									d.Show(
										"such a y has the orbit {y}, which is the orbit of x, of size 1",
										By(
											notOne,
											yIn,
											FixedIffSingletonOrbit.Read(action).At(ym),
											OrbitOfMember.Read(action).At(xm, y),
											cardinality.CardSing.At(y)))
								}))
							vanishes := c.Have(
								"so the indicator vanishes on the orbit, and its sum is 0",
								"Σ_{y∈group_orbit(G, act, x)} «indicator»(y) = 0",
								By(finiteOrbit.At(x), noFixed, nat_sum.EqZero))
							c.Show(
								"both sides are 0 mod p",
								By(
									vanishes,
									multiple,
									nat_divides.DividesMod.At(p, size),
									nat_congruence.CongDef,
									nat_div_mod.ZeroMod))
						})
				}))
			perOrbit := a.Have(
				"over each orbit the ones and the indicator have sums congruent mod p",
				"∀O:set(B). O ∈ «orbits» ⇒ Σ_{y∈O} 1 ≡ Σ_{y∈O} «indicator»(y) (mod p)",
				Simp(Fwd(set_image.ForallInImage)),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					xIn := b.Assume()
					b.Show(
						"over the orbit of a point x of X the ones add up to its size",
						By(
							xIn,
							perPoint.At(x),
							finiteOrbit.At(x),
							nat_sum.SumOfOnes.At(b.TermAs[Set[B]]("group_orbit(G, act, x)"))))
				}))
			congruent := a.Have(
				"so are their sums over the orbits, finitely many as the image of the finite X",
				"Σ_{O∈«orbits»} (Σ_{y∈O} 1) ≡ Σ_{O∈«orbits»} (Σ_{y∈O} «indicator»(y)) (mod p)",
				Unfold(nat_sum.NatSumDef),
				By(
					finiteX,
					finite_set.FiniteImage,
					perOrbit,
					Where(monoidal.Related, "R", a.TermAs[Fun2[Nat, Nat, Bool]]("λu:num. λv:num. u ≡ v (mod p)")),
					nat_sum.MonoidalNatAdd,
					nat_congruence.AddCongruent,
					nat_congruence.CongDef))
			X := a.TermAs[Set[B]]("X")
			allPoints := a.Have(
				"summed over the orbits, the ones count the points of X",
				"card(X) = Σ_{O∈«orbits»} Σ_{y∈O} 1",
				By(
					finiteX,
					SumOverOrbits.Read(action).At(a.TermAs[Fun[B, Nat]]("λx:B. 1")),
					nat_sum.SumOfOnes.At(X)))
			fixedPoints := a.Have(
				"and the indicator counts the points every element fixes",
				"card(«fixedByAll») = Σ_{O∈«orbits»} Σ_{y∈O} «indicator»(y)",
				By(
					finiteX,
					SumOverOrbits.Read(action).At(a.TermAs[Fun[B, Nat]]("«indicator»")),
					nat_sum.CountByIndicator.At(
						X, a.TermAs[Fun[B, Bool]]("λy:B. ∀g:A. g ∈ G.carrier ⇒ act(g, y) = y"))))
			a.Show(
				"so the two counts are congruent mod p",
				By(allPoints, fixedPoints, congruent))
		}),
})}
