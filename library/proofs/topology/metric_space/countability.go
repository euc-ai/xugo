// countability.go — the countability properties of the topology of a
// distance. The balls are a base, and so are the balls of radius 1/n about
// the points of a dense set; the balls of radius 1/n about a point are a
// countable base at it, so the space is first countable; and having a
// countable base, a countable dense set, and a countable subcover of every
// open cover are one property.

package metric_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Bases of balls
// ---------------------------------------------------------------------------

// BallsBase — the balls of positive radius about the points of M are a
// base of the metric topology. Each of them is open, and a point x of an
// open set u has a ball about it inside u, which is one of them and holds
// its centre.
var BallsBase = ballsBaseThm{family.Add(registry.ProofEntry{
	Name: "BallsBase",
	Key:  "prop_90564ac7a6109499",
	Build: MetricSpace.Law("topology_base(metric_topology(M, d), "+
		"    {ball(M, d, x, r) | x:A, r:real | x ∈ M ∧ &0 < r})",
		func(a *Argument, metric MetricSpaceFact[on.M]) {
			a.Do(Simp(Fwd(topological_space.TopologyBaseDef)), SplitConj(
				Case(
					"each ball about a point of M is open",
					BySets(BallOpen.Read(metric))),
				Case(
					"a point of an open set has a ball about it inside the set",
					Derive(func(b *Argument) {
						b.FixAs[Set[A]]("u")
						x := b.FixAs[A]("x")
						given := b.Conjuncts(
							b.Assume(),
							"u is open",
							"x lies in u")
						open := b.Conjuncts(
							b.Simplified(given[0], Fwd(OpenIff)),
							"u lies in M",
							"each point of u has a ball about it inside u")
						r, radius := b.ObtainAs[Real](
							"so u gives x a ball of radius r inside it",
							"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ u",
							By(open[1].At(x), given[1]))
						about := b.Conjuncts(
							radius,
							"r is positive",
							"the ball of radius r lies in u")
						xM := b.MemberOf[on.M](x, b.Have(
							"x is a point of M, as u lies in M",
							"x ∈ M",
							BySets(open[0], given[1])))
						b.Take(b.TermAs[Set[A]]("ball(M, d, x, r)"))
						b.Do(SplitConjAll(
							Case(
								"the ball is one of the balls of positive radius about points of M",
								By(xM, about[0])),
							Case(
								"it holds its centre",
								By(CentreInBall.Read(metric).At(xM, r), about[0])),
							Case(
								"and it lies in u",
								By(about[1])),
						))
					})),
			))
		}),
})}

// MetricFirstCountable — the topology of a distance is first countable.
// At a point x of M the balls about x of radius 1/n, one for each
// natural number n, are countably many and open (at n = 0 the radius
// 1/0 is 0 and the ball is empty). An open set about x holds the ball
// about x of some positive radius r, and so the ball of radius 1/n for
// an n with 1/n below r.
var MetricFirstCountable = metricFirstCountableThm{family.Add(registry.ProofEntry{
	Name: "MetricFirstCountable",
	Key:  "prop_1bf1febf1fde2c92",
	Build: MetricSpace.Law(Statement{
		Conclusion: "first_countable_space(metric_topology(M, d))",
		Abbrev: Abbrev{
			// The balls about the point x the proof fixes, of radius 1/n for each n.
			{Name: "balls", Text: "λn:num. ball(M, d, x, real_inv(&n))"},
		},
	},
		func(a *Argument, metric MetricSpaceFact[on.M]) {
			a.Do(Unfold(countability.FirstCountableSpaceDef))
			x := a.FixAs[A]("x")
			xM := a.MemberOf[on.M](x, a.Simplified(a.Assume(), Fwd(MetricTopologySpace)))
			balls := a.TermAs[Fun[Nat, Set[A]]]("«balls»")
			a.Take(a.TermAs[Set[Set[A]]]("image(«balls», 𝕌)"))
			a.Do(SplitConjAll(
				Case(
					"the balls are countably many, an image of the natural numbers",
					By(cardinal.CountableImage, cardinal.NumCountable)),
				Case(
					"each is open, a ball about a point of M",
					By(set_image.ImageSubsetIff, BallOpen.Read(metric), xM)),
				Case(
					"an open set about x holds one of them about x",
					Derive(func(b *Argument) {
						b.FixAs[Set[A]]("u")
						given := b.Conjuncts(
							b.Assume(),
							"u is open",
							"x lies in u")
						_, radius := b.ObtainAs[Real](
							"u gives x a ball of radius r inside it",
							"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ u",
							By(OpenIff, given[0], given[1]))
						about := b.Conjuncts(
							radius,
							"r is positive",
							"the ball of radius r lies in u")
						n, small := b.ObtainAs[Nat](
							"some 1/n is positive and below r",
							"∃n:num. ¬(n = 0) ∧ &0 < real_inv(&n) ∧ real_inv(&n) < r",
							By(real_archimedean.PosIffExistsSmallInv, about[0]))
						below := b.Conjuncts(
							small,
							"n is not zero",
							"1/n is positive",
							"1/n is below r")
						inner := b.Have(
							"so the ball of radius 1/n lies in the ball of radius r",
							"ball(M, d, x, real_inv(&n)) ⊆ ball(M, d, x, r)",
							By(BallConcentric, real_order_ring.LessEqOfLessThan, below[2]))
						b.Take(b.TermAs[Set[A]]("«balls»(n)"))
						b.Do(SplitConjAll(
							Case(
								"it is the ball of the family at n",
								By(set_image.FunInRange.At(balls, n))),
							Case(
								"it holds its centre x",
								By(CentreInBall.Read(metric).At(xM, b.TermAs[Real]("real_inv(&n)")), below[1])),
							Case(
								"and it lies in the ball of radius r, which lies in u",
								BySets(inner, about[1])),
						))
					})),
			))
		}),
})}

// DenseBallsBase — the balls of radius 1/n about the points of a dense
// subset D of M are a base of the metric topology. Each is open, its
// centre lying in M. A point x of an open set u has a ball of some radius
// r about it inside u; take n with 1/n below r/2. The ball of radius 1/n
// about x is open and holds x, so it meets D, at a point c within 1/n of
// x. The ball of radius 1/n about c then holds x, and a point of it is
// within 1/n + 1/n < r of x, by the triangle inequality through c, so it
// lies in u.
var DenseBallsBase = denseBallsBaseThm{family.Add(registry.ProofEntry{
	Name: "DenseBallsBase",
	Key:  "prop_6ed1a2df3b011fba",
	Build: MetricSpace.Law(Statement{
		Binders: "∀D:set(A).",
		Hypotheses: []string{
			"D ⊆ M",
			"closure(metric_topology, D) = M",
		},
		Conclusion: "topology_base(metric_topology, {ball(c, real_inv(&n)) | c:A, n:num | c ∈ D})",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], D *Expr[Set[A]], within, dense Fact) {
			topology := a.Have(
				"the open sets of the distance form a topology",
				"is_topology(metric_topology(M, d))",
				By(MetricTopology))
			meets := a.Have(
				"D, being dense, meets every non-empty open set",
				"∀w:set(A). w ∈ metric_topology(M, d) ∧ ¬(w = ∅) ⇒ ¬(w ∩ D = ∅)",
				By(topological_space.DenseMeetsOpen.Read(topology).At(D), within, dense, MetricTopologySpace))
			a.Do(Simp(Fwd(topological_space.TopologyBaseDef)), SplitConj(
				Case(
					"each ball about a point of D is open, D lying in M",
					BySets(BallOpen.Read(metric), within)),
				Case(
					"a point of an open set has one of the balls about it inside the set",
					Derive(func(b *Argument) {
						b.FixAs[Set[A]]("u")
						x := b.FixAs[A]("x")
						given := b.Conjuncts(
							b.Assume(),
							"u is open",
							"x lies in u")
						open := b.Conjuncts(
							b.Simplified(given[0], Fwd(OpenIff)),
							"u lies in M",
							"each point of u has a ball about it inside u")
						xM := b.MemberOf[on.M](x, b.Have(
							"x is a point of M, as u lies in M",
							"x ∈ M",
							BySets(open[0], given[1])))
						_, radius := b.ObtainAs[Real](
							"u gives x a ball of radius r inside it",
							"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ u",
							By(open[1].At(x), given[1]))
						about := b.Conjuncts(
							radius,
							"r is positive",
							"the ball of radius r lies in u")
						half := b.Have(
							"half of r is positive",
							"&0 < r / &2",
							ByArith(about[0]))
						_, small := b.ObtainAs[Nat](
							"some 1/n is positive and below r/2",
							"∃n:num. ¬(n = 0) ∧ &0 < real_inv(&n) ∧ real_inv(&n) < r / &2",
							By(real_archimedean.PosIffExistsSmallInv, half))
						below := b.Conjuncts(
							small,
							"n is not zero",
							"1/n is positive",
							"1/n is below r/2")
						radiusN := b.TermAs[Real]("real_inv(&n)")
						centred := b.Have(
							"the ball of radius 1/n about x holds x",
							"x ∈ ball(M, d, x, real_inv(&n))",
							By(CentreInBall.Read(metric).At(xM, radiusN), below[1]))
						centre, found := b.ObtainAs[A](
							"that ball is open and non-empty, so it meets D, at a point c",
							"∃c:A. c ∈ D ∧ c ∈ ball(M, d, x, real_inv(&n))",
							BySets(
								meets.At(b.TermAs[Set[A]]("ball(M, d, x, real_inv(&n))")),
								BallOpen.Read(metric).At(xM, radiusN),
								centred))
						inD := b.Conjuncts(
							found,
							"c is a point of D",
							"c lies in the ball of radius 1/n about x")
						near := b.Conjuncts(
							b.Have(
								"so c is a point of M within 1/n of x",
								"c ∈ M ∧ d(x, c) < real_inv(&n)",
								Unfold(BallDef),
								BySets(inD[1])),
							"c is a point of M",
							"c is within 1/n of x")
						cM := b.MemberOf[on.M](centre, near[0])
						shorter := b.Have(
							"a point of M within 1/n of c is within r of x: the way from x through c is shorter than 1/n + 1/n",
							"∀y:A. y ∈ M ∧ d(c, y) < real_inv(&n) ⇒ d(x, y) < r",
							// y's membership is part of the goal, so the triangle
							// inequality is cited untyped and the closer discharges it.
							b.ForEach(func(y *Expr[A]) Action {
								return ByArith(DistTriangle.Read(metric).AsFact().At(x, centre, y), xM, cM, near[1], below[2])
							}))
						inner := b.Have(
							"so the ball of radius 1/n about c lies in the ball of radius r about x",
							"ball(M, d, c, real_inv(&n)) ⊆ ball(M, d, x, r)",
							Unfold(BallDef),
							BySets(shorter))
						b.Take(b.TermAs[Set[A]]("ball(M, d, c, real_inv(&n))"))
						b.Do(SplitConjAll(
							Case(
								"it is the ball of radius 1/n about c, a point of D",
								By(inD[0])),
							Case(
								"it holds x, the distance reading the same both ways",
								Unfold(BallDef),
								BySets(xM, DistSym.Read(metric).At(cM, xM), near[1])),
							Case(
								"and it lies in u, inside the ball of radius r about x",
								BySets(inner, about[1])),
						))
					})),
			))
		}),
})}

// MetricSeparableIffSecondCountable — a metric space is separable
// exactly when its topology has a countable base. A countable base gives
// a countable dense set in any topology. Conversely, the balls of radius
// 1/n about the points of a countable dense set D are a base
// (DenseBallsBase), and they are countably many: each is the ball at a
// pair of a point of D and a natural number.
var MetricSeparableIffSecondCountable = metricSeparableIffSecondCountableThm{family.Add(registry.ProofEntry{
	Name: "MetricSeparableIffSecondCountable",
	Key:  "prop_5941b24af2f42098",
	Build: MetricSpace.Law(Statement{
		Conclusion: "separable_space(metric_topology(M, d)) ⇔ " +
			"second_countable_space(metric_topology(M, d))",
		Abbrev: Abbrev{
			// The balls of radius 1/n about the points of the dense set D the
			// proof takes, and the same balls indexed by the pairs (c, n).
			{Name: "balls", Text: "{ball(M, d, c, real_inv(&n)) | c:A, n:num | c ∈ D}"},
			{Name: "ballAt", Text: "λp:prod(A, num). ball(M, d, fst(p), real_inv(&snd(p)))"},
		},
	},
		func(a *Argument, metric MetricSpaceFact[on.M]) {
			a.Iff()

			a.Forward(
				"the balls of radius 1/n about the points of a countable dense set are countably many, and a base",
				func(b *Argument, separable Fact) {
					D, given := b.UnpackAs[Set[A]](b.Unfolded(separable, countability.SeparableSpaceDef), "D")
					countableDense := b.Conjuncts(
						b.Simplified(given, Fwd(MetricTopologySpace)),
						"D is countable",
						"D lies in M",
						"the closure of D is M")
					b.Do(Unfold(countability.SecondCountableSpaceDef))
					b.Take(b.TermAs[Set[Set[A]]]("«balls»"))
					b.Do(SplitConj(
						Case(
							"the balls are countably many, an image of the pairs of a point of D and a natural number",
							Derive(func(c *Argument) {
								indexes := c.TermAs[Set[Prod[A, Nat]]]("set_cross(D, 𝕌)")
								ballAt := c.TermAs[Fun[Prod[A, Nat], Set[A]]]("«ballAt»")
								indexed := c.Have(
									"each of the balls is the ball at a pair (c, n) of a point of D and a natural number",
									"«balls» ⊆ image(«ballAt», set_cross(D, 𝕌))",
									Simp(Fwd(set_basic.SubsetDef)),
									Derive(func(e *Argument) {
										e.FixAs[Set[A]]("v")
										centre, n, parts := e.Unpack2As[A, Nat](e.Assume(), "c", "n")
										v := e.Conjuncts(
											parts,
											"c is a point of D",
											"v is the ball of radius 1/n about c")
										pair := e.TermAs[Prod[A, Nat]]("(c, n)")
										paired := e.Have(
											"(c, n) pairs a point of D with a natural number",
											"(c, n) ∈ set_cross(D, 𝕌)",
											By(set_product.InCross.At(D, e.TermAs[Set[Nat]]("𝕌"), centre, n), v[0], set_basic.InUniv.At(n)))
										e.Show(
											"so v is the ball at (c, n)",
											By(set_image.FunInImage.At(ballAt, indexes, pair), paired, pairs.Fst, pairs.Snd, v[1]))
									}))
								countablePairs := c.Have(
									"the pairs are countably many, as D and the natural numbers are, and so are the balls at them",
									"countable(image(«ballAt», set_cross(D, 𝕌)))",
									By(cardinal.CountableImage, cardinal.CountableProduct, countableDense[0], cardinal.NumCountable))
								c.Show(
									"so the balls are countably many",
									By(cardinal.CountableSubset, indexed, countablePairs))
							})),
						Case(
							"and they are a base, D being dense",
							By(DenseBallsBase.Read(metric).At(D), countableDense[1], countableDense[2])),
					))
				})

			a.Backward(
				"a countable base gives a countable dense set",
				func(b *Argument, second Fact) {
					b.Show(
						"in any topology",
						By(countability.SecondCountableImpSeparable, MetricTopology, second))
				})
		}),
})}

// LindelofSeparable — a Lindelöf metric space is separable. For each
// ε > 0 the balls of radius ε about the points of M are an open cover,
// so countably many of them cover M; their centres, one to each ball,
// are countably many points with every point of M within ε of one of
// them. Choosing such a set F(n) for each n with 1/n positive, the
// union of the F(n) is countable, and it meets every non-empty open set:
// a point x of one holds a ball of some radius r about it inside it,
// and for 1/m below r, x lies within 1/m of a point of F(m), which then
// lies in the ball of radius r about x.
var LindelofSeparable = lindelofSeparableThm{family.Add(registry.ProofEntry{
	Name: "LindelofSeparable",
	Key:  "prop_e148d29182ce4304",
	Build: MetricSpace.Law(Statement{
		Hypotheses: []string{
			"lindelof_space(metric_topology)",
		},
		Conclusion: "separable_space(metric_topology)",
		Abbrev: Abbrev{
			// The ball of radius r about a point c, as a map of c.
			{Name: "ballsOfRadius", Text: "λr:real. λc:A. ball(M, d, c, r)"},
			// The union of the sets F(n) the proof chooses.
			{Name: "centres", Text: "⋃image(F, {n:num | &0 < real_inv(&n)})"},
		},
	},
		func(a *Argument, metric MetricSpaceFact[on.M], lindelof Fact) {
			cover := a.Unfolded(lindelof, countability.LindelofSpaceDef)
			net := a.Have(
				"for each ε > 0, the balls of radius ε about countably many points of M cover M",
				"∀ε:real. &0 < ε ⇒ ∃C:set(A). countable(C) ∧ C ⊆ M ∧ M ⊆ ⋃image(«ballsOfRadius»(ε), C)",
				Derive(func(b *Argument) {
					b.FixAs[Real]("ε")
					positive := b.Assume()
					open := b.Have(
						"the balls of radius ε about the points of M are open",
						"image(«ballsOfRadius»(ε), M) ⊆ metric_topology(M, d)",
						By(set_image.ImageSubsetIff, BallOpen.Read(metric)))
					covering := b.Have(
						"and they cover M, each holding its centre",
						"⋃metric_topology(M, d) ⊆ ⋃image(«ballsOfRadius»(ε), M)",
						Simp(Fwd(MetricTopologySpace)),
						BySets(CentreInBall.Read(metric), positive))
					e, subcover := b.ObtainAs[Set[Set[A]]](
						"M being Lindelöf, countably many of them, e, cover it",
						"∃e:set(set(A)). e ⊆ image(«ballsOfRadius»(ε), M) ∧ countable(e) ∧ ⋃metric_topology(M, d) ⊆ ⋃e",
						By(cover, open, covering))
					chosen := b.Conjuncts(
						subcover,
						"the balls of e are balls about points of M",
						"e is countable",
						"e covers M")
					centres, named := b.ObtainAs[Set[A]](
						"they are the balls about the points of a set C of points of M, one point to each ball",
						"∃C:set(A). C ⊆ M ∧ e = image(«ballsOfRadius»(ε), C) ∧ injective_on(C, «ballsOfRadius»(ε))",
						By(set_image.SubsetImageInj, chosen[0]))
					centred := b.Conjuncts(
						named,
						"C lies in M",
						"e is the set of balls about the points of C",
						"distinct points of C have distinct balls")
					fewer := b.Have(
						"so C is no larger than e",
						"card_le(C, e)",
						By(cardinal.CardLeDef, set_image.FunInImage, centred[1], centred[2]))
					b.Take(centres)
					b.Do(SplitConjAll(
						Case(
							"C is countable, as e is",
							By(cardinal.CardLeCountable.At(centres, e), fewer, chosen[1])),
						Case(
							"C lies in M",
							By(centred[0])),
						Case(
							"and the balls about its points, the balls of e, cover M",
							By(centred[1], chosen[2], MetricTopologySpace)),
					))
				}))
			_, chosenNets := a.ObtainAs[Fun[Nat, Set[A]]](
				"so choose such a set F(n) for each n with 1/n positive",
				"∃F:num → set(A). ∀n:num. "+
					"    &0 < real_inv(&n) ⇒ "+
					"    countable(F(n)) ∧ F(n) ⊆ M ∧ M ⊆ ⋃image(«ballsOfRadius»(real_inv(&n)), F(n))",
				By(net))
			within := a.Have(
				"the chosen points all lie in M",
				"«centres» ⊆ M",
				BySets(chosenNets))
			centres := a.TermAs[Set[A]]("«centres»")
			a.Do(Unfold(countability.SeparableSpaceDef), Simp(Fwd(MetricTopologySpace)))
			a.Take(centres)
			a.Do(SplitConjAll(
				Case(
					"they are countably many, a countable union of countable sets",
					Derive(func(b *Argument) {
						indexCountable := b.Have(
							"the sets F(n) are countably many, one to each of countably many n",
							"countable(image(F, {n:num | &0 < real_inv(&n)}))",
							By(cardinal.CountableImage, cardinal.CountableSubset, cardinal.NumCountable, set_order.SubsetUniv))
						each := b.Have(
							"and each of them is countable",
							"∀s:set(A). s ∈ image(F, {n:num | &0 < real_inv(&n)}) ⇒ countable(s)",
							By(set_image.ForallInImage, chosenNets))
						b.Show(
							"so their union is countable",
							By(cardinal.CountableUnions, indexCountable, each))
					})),
				Case(
					"they lie in M",
					By(within)),
				Case(
					"and their closure is M, as they meet every non-empty open set",
					Derive(func(b *Argument) {
						topology := b.Have(
							"the open sets of the distance form a topology",
							"is_topology(metric_topology(M, d))",
							By(MetricTopology))
						meets := b.Have(
							"every non-empty open set u meets the chosen points",
							"∀u:set(A). u ∈ metric_topology(M, d) ∧ ¬(u = ∅) ⇒ ¬(u ∩ «centres» = ∅)",
							Derive(func(c *Argument) {
								c.FixAs[Set[A]]("u")
								given := c.Conjuncts(
									c.Assume(),
									"u is open",
									"u is non-empty")
								x, xIn := c.ObtainAs[A](
									"u has a point x",
									"∃x:A. x ∈ u",
									By(set_basic.MemberNotEmpty, given[1]))
								open := c.Conjuncts(
									c.Simplified(given[0], Fwd(OpenIff)),
									"u lies in M",
									"each point of u has a ball about it inside u")
								xM := c.MemberOf[on.M](x, c.Have(
									"x is a point of M, as u lies in M",
									"x ∈ M",
									BySets(open[0], xIn)))
								_, radius := c.ObtainAs[Real](
									"u gives x a ball of radius r inside it",
									"∃r:real. &0 < r ∧ ball(M, d, x, r) ⊆ u",
									By(open[1].At(x), xIn))
								about := c.Conjuncts(
									radius,
									"r is positive",
									"the ball of radius r lies in u")
								m, small := c.ObtainAs[Nat](
									"some 1/m is positive and below r",
									"∃m:num. ¬(m = 0) ∧ &0 < real_inv(&m) ∧ real_inv(&m) < r",
									By(real_archimedean.PosIffExistsSmallInv, about[0]))
								below := c.Conjuncts(
									small,
									"m is not zero",
									"1/m is positive",
									"1/m is below r")
								atM := c.Conjuncts(
									GroupPremises(below[1], chosenNets.At(m)),
									"F(m) is countable",
									"F(m) lies in M",
									"the balls of radius 1/m about the points of F(m) cover M")
								centre, found := c.ObtainAs[A](
									"so x lies in the ball of radius 1/m about some point c of F(m)",
									"∃c:A. c ∈ F(m) ∧ x ∈ ball(M, d, c, real_inv(&m))",
									BySets(atM[2], xM))
								inF := c.Conjuncts(
									found,
									"c is a point of F(m)",
									"x lies in the ball of radius 1/m about c")
								cM := c.MemberOf[on.M](centre, c.Have(
									"c is a point of M, as F(m) lies in M",
									"c ∈ M",
									BySets(atM[1], inF[0])))
								near := c.Have(
									"x is within 1/m of c",
									"d(c, x) < real_inv(&m)",
									Unfold(BallDef),
									BySets(inF[1]))
								far := c.Have(
									"so c is within r of x, the distance reading the same both ways",
									"d(x, c) < r",
									ByArith(DistSym.Read(metric).At(xM, cM), near, below[2]))
								inBall := c.Have(
									"so c lies in the ball of radius r about x",
									"c ∈ ball(M, d, x, r)",
									Unfold(BallDef),
									BySets(cM, far))
								c.Show(
									"which lies in u, so u meets the chosen points at c",
									BySets(inBall, about[1], inF[0], below[1]))
							}))
						b.Show(
							"so the chosen points are dense",
							By(topological_space.DenseMeetsOpen.Read(topology).At(centres), meets, within, MetricTopologySpace))
					})),
			))
		}),
})}

// MetricLindelofIffSecondCountable — a metric space is Lindelöf exactly
// when its topology has a countable base. A countable base gives
// countable subcovers in any topology; conversely a Lindelöf metric
// space is separable (LindelofSeparable), so it has a countable base
// (MetricSeparableIffSecondCountable).
var MetricLindelofIffSecondCountable = metricLindelofIffSecondCountableThm{family.Add(registry.ProofEntry{
	Name: "MetricLindelofIffSecondCountable",
	Key:  "prop_67fe3d34e62bad18",
	Build: MetricSpace.Law("lindelof_space(metric_topology(M, d)) ⇔ "+
		"second_countable_space(metric_topology(M, d))",
		func(a *Argument, metric MetricSpaceFact[on.M]) {
			a.Iff()

			a.Forward(
				"a Lindelöf metric space is separable, so its topology has a countable base",
				func(b *Argument, lindelof Fact) {
					b.Show(
						"by the equivalence of separability and a countable base",
						By(MetricSeparableIffSecondCountable.Read(metric), LindelofSeparable.Read(metric), lindelof))
				})

			a.Backward(
				"a countable base gives countable subcovers",
				func(b *Argument, second Fact) {
					b.Show(
						"in any topology",
						By(countability.SecondCountableImpLindelof, second))
				})
		}),
})}
