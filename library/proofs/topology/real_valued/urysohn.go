// urysohn.go — real-valued continuous functions on a space, and the two
// theorems that produce them in a normal space: Urysohn's lemma, a
// continuous function to ⟦0, 1⟧ separating two disjoint closed sets, and
// Tietze's extension of a continuous function from a closed set to the
// space, within its bounds when it is bounded. The two facts about
// real-valued maps they stand on — continuity read through the rays, and
// continuity of a uniform limit — are stated here for a map from any
// space to the line, and the topology of a distance is shown normal.

package real_valued

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/separation"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// MetricNormal — the topology of a distance is normal. About each point x
// of a closed set some ball misses a disjoint closed set; the balls of half
// those radii, over every such point and radius rather than one chosen per
// point, form an open set holding the first set. The two open sets so built
// about s and about t are disjoint: a common point z would lie within r/2
// of a centre x in s and within q/2 of a centre y in t, so
// d(x, y) < (r + q)/2, while y lies outside the ball of radius r about x
// and x outside the ball of radius q about y.
var MetricNormal = metricNormalThm{family.Add(registry.ProofEntry{
	Name: "MetricNormal",
	Key:  "prop_c4654dbe33c71c33",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real).",
		Hypotheses: []string{
			"metric_space(M, d)",
		},
		Conclusion: "normal_space(metric_topology(M, d))",
		Abbrev: Abbrev{
			{Name: "halfBalls", Text: "λp:set(A). λq:set(A). " +
				"    {ball(M, d, x, r / &2) | x:A, r:real | x ∈ p ∧ &0 < r ∧ ball(M, d, x, r) ∩ q = ∅}"},
			{Name: "halves", Text: "λp:set(A). λq:set(A). ⋃«halfBalls»(p, q)"},
		},
	}, func(
		a *Argument,
		M *Expr[Set[A]],
		d *Arrow2[A, A, Real],
		metric metric_space.MetricSpaceFact[on.M],
	) {
		aboutClosed := a.Have(
			"about the points of a closed set p, the balls of half a radius whose "+
				"full ball misses a disjoint closed set q form an open set holding p",
			Statement{
				Binders: "∀p q:set(A).",
				Hypotheses: []string{
					"closed_in(metric_topology(M, d), p)",
					"closed_in(metric_topology(M, d), q)",
					"p ∩ q = ∅",
				},
				Conclusion: "«halves»(p, q) ∈ metric_topology(M, d) ∧ p ⊆ «halves»(p, q)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Set[A]]("p")
				b.FixAs[Set[A]]("q")
				given := b.Conjuncts(
					b.Assume(),
					"p is closed",
					"q is closed",
					"and the two are disjoint")
				pClosed, qClosed, disjoint := given[0], given[1], given[2]
				pInM := b.Have(
					"p, being closed, lies in M",
					"p ⊆ M",
					By(pClosed, metric_space.ClosedIff))
				b.Do(SplitConj(
					Case(
						"each half ball is open, so their union is",
						Derive(func(c *Argument) {
							balls := c.Have(
								"each half ball is open, its centre lying in p and so in M",
								"«halfBalls»(p, q) ⊆ metric_topology(M, d)",
								Simp(Fwd(set_basic.SubsetDef)),
								Derive(func(e *Argument) {
									e.FixAs[Set[A]]("w")
									x, _, member := e.Unpack2As[A, Real](e.Assume(), "x", "r")
									parts := e.Conjuncts(
										member,
										"x lies in p",
										"r is positive",
										"the ball of radius r about x misses q",
										"and w is the ball of half that radius")
									centre := e.Have(
										"x lies in M",
										"x ∈ M",
										BySets(parts[0], pInM))
									e.Do(parts[3].Rw())
									e.Show(
										"which is open",
										By(metric_space.BallOpen.Read(metric).At(e.MemberOf[on.M](x, centre), e.TermAs[Real]("r / &2"))))
								}))
							c.Show(
								"a union of open sets is open",
								By(balls, metric_space.MetricTopology.At(M, d), topological_space.UnionsOpen))
						})),
					Case(
						"and each point of p lies in the half ball about itself",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							centre := c.Have(
								"x lies in M",
								"x ∈ M",
								BySets(xIn, pInM))
							outside := c.Have(
								"and outside q",
								"x ∉ q",
								BySets(xIn, disjoint))
							_, radius := c.ObtainAs[Real](
								"q being closed, the ball of some radius r about x misses it",
								"∃r:real. &0 < r ∧ ball(M, d, x, r) ∩ q = ∅",
								By(qClosed, centre, outside, metric_space.ClosedIff))
							parts := c.Conjuncts(
								radius,
								"r is positive",
								"the ball of radius r about x misses q")
							half := c.Have(
								"so is half of r",
								"&0 < r / &2",
								ByArith(parts[0]))
							inHalf := c.Have(
								"x lies in the ball of half that radius about itself",
								"x ∈ ball(M, d, x, r / &2)",
								By(
									metric_space.CentreInBall.Read(metric).At(c.MemberOf[on.M](x, centre), c.TermAs[Real]("r / &2")),
									half))
							c.Show(
								"which is one of the half balls",
								BySets(xIn, parts[0], parts[1], inHalf))
						}))))
			}))

		a.Do(Simp(Fwd(separation.NormalSpaceDef)))
		s := a.FixAs[Set[A]]("s")
		t := a.FixAs[Set[A]]("t")
		given := a.Conjuncts(
			a.Assume(),
			"s is closed",
			"t is closed",
			"and the two are disjoint")
		sClosed, tClosed, disjoint := given[0], given[1], given[2]
		swapped := a.Have(
			"t and s are disjoint",
			"t ∩ s = ∅",
			BySets(disjoint))
		aboutS := a.Conjuncts(
			GroupPremises(sClosed, tClosed, disjoint, aboutClosed.At(s, t)),
			"the half balls about s form an open set u",
			"holding s")
		aboutT := a.Conjuncts(
			GroupPremises(tClosed, sClosed, swapped, aboutClosed.At(t, s)),
			"the half balls about t form an open set v",
			"holding t")
		inM := a.Have(
			"both sets, being closed, lie in M",
			"s ⊆ M ∧ t ⊆ M",
			By(sClosed, tClosed, metric_space.ClosedIff))
		a.Take(a.TermAs[Set[A]]("«halves»(s, t)"))
		a.Take(a.TermAs[Set[A]]("«halves»(t, s)"))
		a.Do(SplitConjAll(
			Case(
				"u is open",
				By(aboutS[0])),
			Case(
				"v is open",
				By(aboutT[0])),
			Case(
				"s lies in u",
				By(aboutS[1])),
			Case(
				"t lies in v",
				By(aboutT[1])),
			Case(
				"and u and v are disjoint, by the triangle inequality",
				Derive(func(b *Argument) {
					apart := b.Have(
						"no point lies in both",
						"∀z:A. z ∈ «halves»(s, t) ∧ z ∈ «halves»(t, s) ⇒ ⊥",
						Derive(func(c *Argument) {
							z := c.FixAs[A]("z")
							both := c.Conjuncts(
								c.Assume(),
								"z lies in u",
								"and in v")
							x, _, nearX := c.Obtain2As[A, Real](
								"z lies within r/2 of a point x of s whose ball of radius r misses t",
								"∃x:A. ∃r:real. x ∈ s ∧ &0 < r ∧ ball(M, d, x, r) ∩ t = ∅ ∧ z ∈ ball(M, d, x, r / &2)",
								BySets(both[0]))
							y, _, nearY := c.Obtain2As[A, Real](
								"and within q/2 of a point y of t whose ball of radius q misses s",
								"∃y:A. ∃q:real. y ∈ t ∧ &0 < q ∧ ball(M, d, y, q) ∩ s = ∅ ∧ z ∈ ball(M, d, y, q / &2)",
								BySets(both[1]))
							distances := c.Have(
								"so d(x, y) is at least r and at least q, while z is within r/2 of x and within q/2 of y",
								"x ∈ M ∧ y ∈ M ∧ z ∈ M ∧ ¬(d(x, y) < r) ∧ ¬(d(y, x) < q) ∧ d(x, z) < r / &2 ∧ d(y, z) < q / &2",
								BySets(inM, c.Unfolded(nearX, metric_space.BallDef), c.Unfolded(nearY, metric_space.BallDef)))
							c.Show(
								"but the detour through z makes d(x, y) less than (r + q)/2",
								ByArith(
									metric_space.DistTriangle.Read(metric).AsFact().At(x, z, y),
									metric_space.DistSym.Read(metric).AsFact().At(z, y),
									metric_space.DistSym.Read(metric).AsFact().At(y, x),
									distances))
						}))
					b.Show(
						"so u and v share no point",
						BySets(apart))
				}))))
	}),
})}

// ContinuousIntoRealIff — a real-valued map on a space is continuous
// exactly when the points where it lies below a and where it lies above
// a form open sets, for every a. Those two sets are the preimages of the
// open rays below and above a, so a continuous map has them open.
// Conversely every real is a point of the line, and at a point x of the
// preimage of an open u the interval of some radius δ about f(x) lies in
// u: the points where f lies below f(x) + δ and those where it lies
// above f(x) − δ meet in an open set about x inside the preimage.
var ContinuousIntoRealIff = continuousIntoRealIffThm{family.Add(registry.ProofEntry{
	Name: "ContinuousIntoRealIff",
	Key:  "prop_1bc891946eb5743d",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{
			"is_topology(T)",
		},
		Conclusion: "continuous_map(T, real_topology, f) ⇔ " +
			"∀a:real. {x:A | x ∈ ⋃T ∧ f(x) < a} ∈ T ∧ {x:A | x ∈ ⋃T ∧ a < f(x)} ∈ T",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f *Arrow[A, Real], topology Fact) {
		a.Iff()

		a.Forward(
			"a continuous map pulls the open rays below and above a back to open sets",
			func(b *Argument, continuousMap Fact) {
				level := b.FixAs[Real]("a")
				b.Do(SplitConj(
					Case(
						"the points where f lies below a are the preimage of the ray below a",
						By(
							continuous.PreimageOpen.Read(continuousMap).AsFact().At(b.TermAs[Set[Real]]("{y:real | y < a}")),
							real_topology.RayBelowOpen.At(level),
							functions.PreimageOnDef)),
					Case(
						"the points where f lies above a are the preimage of the ray above a",
						By(
							continuous.PreimageOpen.Read(continuousMap).AsFact().At(b.TermAs[Set[Real]]("{y:real | a < y}")),
							real_topology.RayAboveOpen.At(level),
							functions.PreimageOnDef))))
			})

		a.Backward(
			"open preimages of the rays make f continuous: an interval about a value is the meet of two rays",
			func(b *Argument, rays Fact) {
				b.Show(
					"f is continuous into the line",
					continuous.ContinuousMap.Intro(
						Case(
							"every real is a point of the line",
							By(real_topology.RealSpace, set_basic.InUniv)),
						Case(
							"the preimage of an open u is open, by the pointwise criterion",
							Derive(func(c *Argument) {
								u := c.FixAs[Set[Real]]("u")
								uOpen := c.Assume()
								c.Do(Simp(Fwd(topological_space.OpenPointwise)))
								c.FixAs[A]("x")
								position := c.Have(
									"x is a point of the space whose value lies in u",
									"x ∈ ⋃T ∧ f(x) ∈ u",
									BySets(c.Assume()))
								_, interval := c.ObtainAs[Real](
									"the interval of some radius δ about f(x) lies in u",
									"∃δ:real. &0 < δ ∧ ∀y:real. |y - f(x)| < δ ⇒ y ∈ u",
									By(uOpen, position, real_topology.OpenIff.At(u)))
								parts := c.Conjuncts(
									interval,
									"δ is positive",
									"what lies within δ of f(x) lies in u")
								δPositive, insideU := parts[0], parts[1]
								centre := c.Have(
									"f(x) lies strictly between f(x) − δ and f(x) + δ",
									"f(x) - δ < f(x) ∧ f(x) < f(x) + δ",
									ByArith(δPositive))
								c.Take(c.TermAs[Set[A]]("{y:A | y ∈ ⋃T ∧ f(y) < f(x) + δ} ∩ {y:A | y ∈ ⋃T ∧ f(x) - δ < f(y)}"))
								c.Do(SplitConjAll(
									Case(
										"the meet of the points below f(x) + δ and those above f(x) − δ is open",
										By(
											topological_space.InterOpen.Read(topology),
											rays.At(c.TermAs[Real]("f(x) + δ")),
											rays.At(c.TermAs[Real]("f(x) - δ")))),
									Case(
										"a point y of the meet has its value within δ of f(x), hence in u",
										Simp(Fwd(set_basic.SubsetDef)),
										Derive(func(d *Argument) {
											y := d.FixAs[A]("y")
											between := d.Have(
												"y is a point of the space with f(y) between f(x) − δ and f(x) + δ",
												"y ∈ ⋃T ∧ f(y) < f(x) + δ ∧ f(x) - δ < f(y)",
												BySets(d.Assume()))
											near := d.Have(
												"so f(y) lies within δ of f(x)",
												"|f(y) - f(x)| < δ",
												ByArith(between))
											d.Show(
												"and so in u, which puts y in the preimage",
												BySets(insideU.At(f.Apply(y)), near, between))
										})),
									Case(
										"and x lies in the meet",
										BySets(position, centre))))
							}))))
			})
	}),
})}

// UniformLimitContinuous — a uniform limit of continuous real-valued maps
// is continuous, by the ε/3 argument. At a point x of g's preimage of an
// open u, the interval of some radius ε about g(x) lies in u, and some
// f(N) is within ε/3 of g on the whole space. The points f(N) sends
// within ε/3 of f(N)(x) form an open set about x, and at each of them g
// is within ε/3 + ε/3 + ε/3 of g(x), so in u. Tietze's series converges
// uniformly, so its sum is continuous by this.
var UniformLimitContinuous = uniformLimitContinuousThm{family.Add(registry.ProofEntry{
	Name: "UniformLimitContinuous",
	Key:  "prop_3a4c7c2b0d2f47a5",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f:(num → A → real). ∀g:(A → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"∀n:num. continuous_map(T, real_topology, f(n))",
			"∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. ∀x:A. N ≤ n ∧ x ∈ ⋃T ⇒ |f(n)(x) - g(x)| < ε",
		},
		Conclusion: "continuous_map(T, real_topology, g)",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		f *Arrow2[Nat, A, Real],
		g *Arrow[A, Real],
		topology, continuity, uniform Fact,
	) {
		a.Show(
			"g is continuous into the line",
			continuous.ContinuousMap.Intro(
				Case(
					"every real is a point of the line",
					By(real_topology.RealSpace, set_basic.InUniv)),
				Case(
					"g's preimage of an open u is open, by the pointwise criterion",
					Derive(func(b *Argument) {
						u := b.FixAs[Set[Real]]("u")
						uOpen := b.Assume()
						b.Do(Simp(Fwd(topological_space.OpenPointwise)))
						x := b.FixAs[A]("x")
						position := b.Have(
							"x is a point of the space whose value g(x) lies in u",
							"x ∈ ⋃T ∧ g(x) ∈ u",
							BySets(b.Assume()))
						_, interval := b.ObtainAs[Real](
							"the interval of some radius ε about g(x) lies in u",
							"∃ε:real. &0 < ε ∧ ∀y:real. |y - g(x)| < ε ⇒ y ∈ u",
							By(uOpen, position, real_topology.OpenIff.At(u)))
						parts := b.Conjuncts(
							interval,
							"ε is positive",
							"what lies within ε of g(x) lies in u")
						εPositive, insideU := parts[0], parts[1]
						radius := b.TermAs[Real]("ε / &3")
						third := b.Have(
							"a third of ε is positive",
							"&0 < ε / &3",
							ByArith(εPositive))
						N, tail := b.ObtainAs[Nat](
							"past some index N every f(n) is within ε/3 of g on the whole space",
							"∃N:num. ∀n:num. ∀z:A. N ≤ n ∧ z ∈ ⋃T ⇒ |f(n)(z) - g(z)| < ε / &3",
							By(uniform.At(radius), third))
						centre := b.Have(
							"f(N)(x) lies within ε/3 of itself",
							"|f(N)(x) - f(N)(x)| < ε / &3",
							ByArith(third))
						b.Take(b.TermAs[Set[A]]("preimage_on(⋃T, f(N), {w:real | |w - f(N)(x)| < ε / &3})"))
						b.Do(SplitConjAll(
							Case(
								"the points f(N) sends within ε/3 of f(N)(x) form an open set, f(N) being continuous",
								By(continuity.At(N), continuous.PreimageOpen, real_topology.BallOpen.At(f.Apply(N, x), radius))),
							Case(
								"at a point y of that set g(y) is within ε of g(x), hence in u",
								Simp(Fwd(set_basic.SubsetDef)),
								Derive(func(c *Argument) {
									y := c.FixAs[A]("y")
									near := c.Have(
										"y is a point of the space with f(N)(y) within ε/3 of f(N)(x)",
										"y ∈ ⋃T ∧ |f(N)(y) - f(N)(x)| < ε / &3",
										BySets(c.Assume()))
									estimate := c.Have(
										"so g(y) is within ε of g(x), f(N) being within ε/3 of g at y and at x",
										"|g(y) - g(x)| < ε",
										ByArith(tail.At(N, y), tail.At(N, x), position, near))
									c.Show(
										"and so lies in u, which puts y in g's preimage of u",
										BySets(insideU.At(g.Apply(y)), estimate, near))
								})),
							Case(
								"and x lies in that set",
								BySets(position, centre))))
					}))))
	}),
})}

// DyadicBetween — between two reals of ⟦0, 1⟧ lies a dyadic rational
// k/2ⁿ with k ≤ 2ⁿ. Take N with 2ᴺ·(b − a) past 1, which the Archimedean
// property gives at N·(b − a) and 2ᴺ > N carries over; then m + 1, for m
// the integer part of a·2ᴺ, lies past a·2ᴺ by at most 1, so below b·2ᴺ.
var DyadicBetween = dyadicBetweenThm{family.Add(registry.ProofEntry{
	Name: "DyadicBetween",
	Key:  "prop_9dd58845b8b473b8",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real.",
		Hypotheses: []string{
			"&0 ≤ a",
			"a < b",
			"b ≤ &1",
		},
		Conclusion: "∃n k:num. k ≤ 2 ^ n ∧ a < &k / &2 ^ n ∧ &k / &2 ^ n < b",
	}, func(arg *Argument, a, b *Expr[Real], low, gap, high Fact) {
		width := arg.Have(
			"the gap b − a is positive",
			"&0 < b - a",
			ByArith(gap))
		N, archimedean := arg.ObtainAs[Nat](
			"some N has N·(b − a) past 1",
			"∃N:num. &1 < &N * (b - a)",
			By(real_archimedean.Archimedean.At(arg.TermAs[Real]("b - a"), arg.TermAs[Real]("&1")), width))
		fine := arg.Have(
			"so has 2ᴺ, which exceeds N: the mesh 1/2ᴺ is finer than b − a",
			"&1 < &2 ^ N * (b - a)",
			ByArith(archimedean, width, nat_order.LessThanPowTwoSelf.At(N)))
		gridPositive := real_pow.PowPos.At(arg.TermAs[Real]("&2"), N)
		scaled := arg.Have(
			"a·2ᴺ is nonnegative",
			"&0 ≤ a * &2 ^ N",
			ByArith(low))
		m, part := arg.ObtainAs[Nat](
			"a·2ᴺ lies between an integer m and m + 1",
			"∃m:num. &m ≤ a * &2 ^ N ∧ a * &2 ^ N < &m + &1",
			By(rational.NonnegIntegerPart.At(arg.TermAs[Real]("a * &2 ^ N")), scaled))
		k, next := arg.ObtainAs[Nat](
			"so k = m + 1 lies past a·2ᴺ, by at most 1",
			"∃k:num. a * &2 ^ N < &k ∧ &k ≤ a * &2 ^ N + &1",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Nat]("m + 1"))
				b.Show(
					"m + 1 lies past a·2ᴺ, which lies past m",
					ByArith(part, real_construction.OfNumAdd.At(m, b.TermAs[Nat]("1"))))
			}))
		above := arg.Have(
			"a lies below k/2ᴺ",
			"a < &k / &2 ^ N",
			ByArith(next, gridPositive))
		below := arg.Have(
			"and k/2ᴺ below b, since k ≤ a·2ᴺ + 1 < b·2ᴺ",
			"&k / &2 ^ N < b",
			ByArith(next, fine, gridPositive))
		inRange := arg.Have(
			"so k is at most 2ᴺ, since k < b·2ᴺ and b is at most 1",
			"&k ≤ &(2 ^ N)",
			ByArith(next, fine, high, gridPositive))
		arg.Take(N)
		arg.Take(k)
		arg.Show(
			"the dyadic k/2ᴺ lies in the grid of level N, strictly between a and b",
			By(real_construction.OfNumLessEq.At(k, arg.TermAs[Nat]("2 ^ N")), inRange, above, below))
	}),
})}

// UrysohnChain — in a normal space a closed set s inside an open set u
// starts a dyadic chain of open sets reaching u: sets V(n, k) for k ≤ 2ⁿ,
// each open and holding s, the closure of each inside the next, the last
// of every level u, and level n + 1 refining level n, V(n + 1, 2k) =
// V(n, k). The shrinking that normality gives is chosen once, as a
// function h: for a closed c inside an open w, h(c, w) is open, holds c
// and has its closure inside w. The levels are
// built by recursion: level 0 is h(s, u), u; level n + 1 keeps level n at
// the even indices and puts at 2i + 1 the shrink of closure(V(n, i))
// inside V(n, i + 1). That every level is such a chain passes from n to
// n + 1, the new set at 2i + 1 lying between closure(V(n, i)) and
// V(n, i + 1) with its own closure.
var UrysohnChain = urysohnChainThm{family.Add(registry.ProofEntry{
	Name: "UrysohnChain",
	Key:  "prop_b3ee88417ab1cadb",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s u:set(A).",
		Hypotheses: []string{
			"is_topology(T)",
			"normal_space(T)",
			"closed_in(T, s)",
			"u ∈ T",
			"s ⊆ u",
		},
		Conclusion: "∃V:(num → num → set(A)). " +
			"    (∀n k:num. k ≤ 2 ^ n ⇒ V(n, k) ∈ T ∧ s ⊆ V(n, k)) ∧ " +
			"    (∀n:num. V(n, 2 ^ n) = u) ∧ " +
			"    (∀n k:num. V(n + 1, 2 * k) = V(n, k)) ∧ " +
			"    (∀n k:num. k < 2 ^ n ⇒ closure(T, V(n, k)) ⊆ V(n, k + 1))",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		s, u *Expr[Set[A]],
		topology, normal, sClosed, uOpen, inside Fact,
	) {
		shrinkable := a.Have(
			"normality shrinks a closed c inside an open w",
			"∀c w:set(A). closed_in(T, c) ∧ w ∈ T ∧ c ⊆ w ⇒ ∃v:set(A). v ∈ T ∧ c ⊆ v ∧ closure(T, v) ⊆ w",
			Derive(func(b *Argument) {
				c := b.FixAs[Set[A]]("c")
				w := b.FixAs[Set[A]]("w")
				given := b.Assume()
				b.Show(
					"the space being normal",
					By(separation.NormalShrink.At(T, c, w), normal, given))
			}))
		_, shrink := a.ObtainAs[Fun2[Set[A], Set[A], Set[A]]](
			"one such shrink h(c, w) chosen for every closed c inside an open w",
			"∃h:(set(A) → set(A) → set(A)). ∀c w:set(A). "+
				"    closed_in(T, c) ∧ w ∈ T ∧ c ⊆ w ⇒ h(c, w) ∈ T ∧ c ⊆ h(c, w) ∧ closure(T, h(c, w)) ⊆ w",
			By(shrinkable))
		V, recursion := a.UnpackAs[Fun2[Nat, Nat, Set[A]]](
			nat_arith.PrimRecursion.At(
				a.TermAs[Fun2[Fun[Nat, Set[A]], Nat, Fun[Nat, Set[A]]]](
					"λL:num → set(A). λn:num. λi:num. "+
						"    COND(rem(i, 2) = 0, L(div(i, 2)), h(closure(T, L(div(i, 2))), L(div(i, 2) + 1)))"),
				a.TermAs[Fun[Nat, Set[A]]]("λi:num. COND(i = 0, h(s, u), u)")),
			"V")
		zero := a.Ctx().Nat(0)
		base := a.Have(
			"level 0 is h(s, u) at index 0 and u elsewhere",
			"∀i:num. V(0, i) = COND(i = 0, h(s, u), u)",
			a.ForEach(func(i *Expr[Nat]) Action { return By(recursion.At(zero)) }))
		step := a.Have(
			"level n + 1 at index i is V(n, i/2) when i is even, and "+
				"otherwise the shrink of closure(V(n, ⌊i/2⌋)) inside the next set",
			"∀n i:num. "+
				"    V(suc(n), i) = "+
				"    COND(rem(i, 2) = 0, V(n, div(i, 2)), h(closure(T, V(n, div(i, 2))), V(n, div(i, 2) + 1)))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.FixAs[Nat]("i")
				b.Show(
					"the recursion's step, read at i",
					By(recursion.At(n)))
			}))
		even := a.Have(
			"so level n + 1 keeps level n at the even indices",
			"∀n k:num. V(suc(n), 2 * k) = V(n, k)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				k := b.FixAs[Nat]("k")
				halved := b.Have(
					"2k is even, with half k",
					"div(2 * k, 2) = k ∧ rem(2 * k, 2) = 0",
					ByArith(nat_div_mod.DivModUniq.At(b.TermAs[Nat]("2 * k"), b.TermAs[Nat]("2"), k, zero)))
				b.Show(
					"the recursion's even branch",
					By(Normalized, halved, step.At(n, b.TermAs[Nat]("2 * k"))))
			}))
		odd := a.Have(
			"and puts at 2k + 1 the shrink of closure(V(n, k)) inside V(n, k + 1)",
			"∀n k:num. V(suc(n), 2 * k + 1) = h(closure(T, V(n, k)), V(n, k + 1))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.FixAs[Nat]("k")
				halved := b.Have(
					"2k + 1 is odd, with half k",
					"div(2 * k + 1, 2) = k ∧ rem(2 * k + 1, 2) ≠ 0",
					ByArith())
				b.Show(
					"the recursion's odd branch",
					By(halved, step.At(n, b.TermAs[Nat]("2 * k + 1"))))
			}))
		levelZero := a.Have(
			"so level 0 is h(s, u), then u",
			"V(0, 0) = h(s, u) ∧ V(0, 1) = u",
			By(
				Normalized,
				base.At(zero),
				base.At(a.Ctx().Nat(1)),
				nat_arith.OneIsSucZero,
				peano.SucNotZero.At(zero)))
		first := a.Have(
			"h(s, u) shrinks s inside u",
			"h(s, u) ∈ T ∧ s ⊆ h(s, u) ∧ closure(T, h(s, u)) ⊆ u",
			By(shrink.At(s, u), sClosed, uOpen, inside))
		levels := a.Have(
			"every level is a chain of open sets holding s, each closure inside the next, ending at u",
			"∀n:num. "+
				"    (∀k:num. k ≤ 2 ^ n ⇒ V(n, k) ∈ T ∧ s ⊆ V(n, k)) ∧ "+
				"    V(n, 2 ^ n) = u ∧ "+
				"    (∀k:num. k < 2 ^ n ⇒ closure(T, V(n, k)) ⊆ V(n, k + 1))",
			Derive(func(b *Argument) {
				b.Induct("n")
				b.Base(
					"level 0 is h(s, u) and u, the closure of the first inside the second",
					SplitConjAll(
						Case(
							"both sets of level 0 are open and hold s",
							Derive(func(c *Argument) {
								c.FixAs[Nat]("k")
								low := c.Assume()
								which := c.Have(
									"k is 0 or 1",
									"k = 0 ∨ k = 1",
									ByArith(low))
								c.Show(
									"h(s, u) and u are open and hold s",
									By(which, levelZero, first, uOpen, inside))
							})),
						Case(
							"the last set of level 0 is u",
							By(Normalized, levelZero, nat_arith.NatPow)),
						Case(
							"the closure of h(s, u) lies in u",
							Derive(func(c *Argument) {
								c.FixAs[Nat]("k")
								low := c.Assume()
								only := c.Have(
									"k is 0",
									"k = 0",
									ByArith(low))
								c.Show(
									"and the closure of h(s, u) lies in u",
									only.Rw(),
									By(Normalized, levelZero, first, nat_arith.AddClauses))
							}))))
				b.Step(
					"level n + 1 interleaves level n with the shrinks between neighbours",
					func(c *Argument, ih Fact) {
						n := c.TermAs[Nat]("n")
						parts := c.Conjuncts(
							ih,
							"the sets of level n are open and hold s",
							"the last is u",
							"and each closure lies in the next")
						open, last, chain := parts[0], parts[1], parts[2]
						between := c.Have(
							"for i < 2ⁿ the new set V(n + 1, 2i + 1) is open, holds "+
								"closure(V(n, i)), and has its closure inside V(n, i + 1)",
							Statement{
								Binders: "∀i:num.",
								Hypotheses: []string{
									"i < 2 ^ n",
								},
								Conclusion: "V(suc(n), 2 * i + 1) ∈ T ∧ " +
									"closure(T, V(n, i)) ⊆ V(suc(n), 2 * i + 1) ∧ " +
									"closure(T, V(suc(n), 2 * i + 1)) ⊆ V(n, i + 1)",
							},
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								below := d.Assume()
								neighbours := d.Have(
									"V(n, i) and V(n, i + 1) are open",
									"V(n, i) ∈ T ∧ V(n, i + 1) ∈ T",
									ByArith(open.At(i), open.At(d.TermAs[Nat]("i + 1")), below))
								here := d.TermAs[Set[A]]("V(n, i)")
								closed := d.Have(
									"the closure of V(n, i) is closed, V(n, i) lying in the space",
									"closed_in(T, closure(T, V(n, i)))",
									By(
										topological_space.ClosureClosed.Read(topology).At(here),
										set_order.MemberSubsetUnions.At(T, here),
										neighbours))
								d.Show(
									"V(n + 1, 2i + 1) is the shrink of that closure inside V(n, i + 1)",
									By(
										shrink.At(d.TermAs[Set[A]]("closure(T, V(n, i))"), d.TermAs[Set[A]]("V(n, i + 1)")),
										odd.At(n, i),
										chain.At(i),
										below,
										closed,
										neighbours))
							}))
						c.Do(SplitConjAll(
							Case(
								"every set of level n + 1 is open and holds s",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]("k")
									within := d.Assume()
									halves := d.Have(
										"k is 2i with i ≤ 2ⁿ, or 2i + 1 with i < 2ⁿ",
										"(∃i:num. i ≤ 2 ^ n ∧ k = 2 * i) ∨ (∃i:num. i < 2 ^ n ∧ k = 2 * i + 1)",
										ByArith(
											nat_parity.DoubleOrSucDoubleBelow.At(d.TermAs[Nat]("2 ^ n"), k),
											nat_arith.PowTwoSuc.At(n),
											within))
									d.Do(halves.SplitDisj(
										LeftHolds(
											"at k = 2i the set is V(n, i)",
											Given(func(e *Argument, isEven Fact) {
												i, at := e.UnpackAs[Nat](isEven, "i")
												facts := e.Conjuncts(
													at,
													"i ≤ 2ⁿ",
													"k = 2i")
												e.Show(
													"which is open and holds s",
													facts[1].Rw(),
													By(even.At(n, i), open.At(i), facts[0]))
											})),
										RightHolds(
											"at k = 2i + 1 the set holds the closure of V(n, i), which holds s",
											Given(func(e *Argument, isOdd Fact) {
												i, at := e.UnpackAs[Nat](isOdd, "i")
												facts := e.Conjuncts(
													at,
													"i < 2ⁿ",
													"k = 2i + 1")
												holds := e.Have(
													"V(n, i) holds s",
													"s ⊆ V(n, i)",
													ByArith(open.At(i), facts[0]))
												e.Show(
													"which is open and holds s ⊆ V(n, i) ⊆ closure(V(n, i))",
													facts[1].Rw(),
													BySets(
														between.At(i),
														facts[0],
														holds,
														topological_space.SubsetClosure.At(T, e.TermAs[Set[A]]("V(n, i)"))))
											}))))
								})),
							Case(
								"the last set of level n + 1 is u",
								By(even.At(n, c.TermAs[Nat]("2 ^ n")), last, nat_arith.NatPow)),
							Case(
								"the closure of each set of level n + 1 lies in the next",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]("k")
									below := d.Assume()
									halves := d.Have(
										"k is 2i with i ≤ 2ⁿ, or 2i + 1 with i < 2ⁿ",
										"(∃i:num. i ≤ 2 ^ n ∧ k = 2 * i) ∨ (∃i:num. i < 2 ^ n ∧ k = 2 * i + 1)",
										ByArith(
											nat_parity.DoubleOrSucDoubleBelow.At(d.TermAs[Nat]("2 ^ n"), k),
											nat_arith.PowTwoSuc.At(n),
											below))
									d.Do(halves.SplitDisj(
										LeftHolds(
											"at k = 2i, V(n + 1, k) is V(n, i), whose closure lies in V(n + 1, 2i + 1)",
											Given(func(e *Argument, isEven Fact) {
												i, at := e.UnpackAs[Nat](isEven, "i")
												facts := e.Conjuncts(
													at,
													"i ≤ 2ⁿ",
													"k = 2i")
												strict := e.Have(
													"i < 2ⁿ, since 2i < 2ⁿ⁺¹",
													"i < 2 ^ n",
													ByArith(facts[1], below, nat_arith.PowTwoSuc.At(n)))
												e.Show(
													"so the closure of V(n + 1, 2i) lies in V(n + 1, 2i + 1)",
													facts[1].Rw(),
													By(even.At(n, i), between.At(i), strict))
											})),
										RightHolds(
											"at k = 2i + 1 the closure of V(n + 1, k) lies in V(n, i + 1), which is V(n + 1, 2i + 2)",
											Given(func(e *Argument, isOdd Fact) {
												i, at := e.UnpackAs[Nat](isOdd, "i")
												facts := e.Conjuncts(
													at,
													"i < 2ⁿ",
													"k = 2i + 1")
												next := e.Have(
													"2i + 2 is twice i + 1",
													"2 * i + 1 + 1 = 2 * (i + 1)",
													ByArith())
												e.Show(
													"so the closure of V(n + 1, 2i + 1) lies in V(n + 1, 2i + 2)",
													facts[1].Rw(),
													next.Rw(),
													By(between.At(i), facts[0], even.At(n, e.TermAs[Nat]("i + 1"))))
											}))))
								}))))
					})
			}))
		refines := a.Have(
			"level n + 1, which is level suc(n), keeps level n at the even indices",
			"∀n k:num. V(n + 1, 2 * k) = V(n, k)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				k := b.FixAs[Nat]("k")
				b.Show(
					"n + 1 is suc(n)",
					By(Normalized, even.At(n, k), nat_arith.Add1.At(n)))
			}))
		a.Take(V)
		a.Show(
			"V is such a chain",
			By(levels, refines))
	}),
})}

// UrysohnChainMonotone — in a dyadic chain of sets, refining from level to
// level with each closure inside the next set of its level, the closure of
// the set at k/2ⁿ lies in the set at every later j/2ᵐ; the comparison
// k/2ⁿ < j/2ᵐ is written k·2ᵐ < j·2ⁿ. A set of level p is the set of level
// p + d at the index scaled by 2ᵈ, by refining d times; so the two sets are
// sets of the one level n + m, at k·2ᵐ < j·2ⁿ. Within a level the closure
// of a set lies in every later set: in the next one by the chain, and in
// the one after a later set b through b, inside its closure, inside the
// set after b.
var UrysohnChainMonotone = urysohnChainMonotoneThm{family.Add(registry.ProofEntry{
	Name: "UrysohnChainMonotone",
	Key:  "prop_3933bf487150b14",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀V:(num → num → set(A)). ∀n k m j:num.",
		Hypotheses: []string{
			"∀p i:num. V(p + 1, 2 * i) = V(p, i)",
			"∀p i:num. i < 2 ^ p ⇒ closure(T, V(p, i)) ⊆ V(p, i + 1)",
			"j ≤ 2 ^ m",
			"k * 2 ^ m < j * 2 ^ n",
		},
		Conclusion: "closure(T, V(n, k)) ⊆ V(m, j)",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		V *Arrow2[Nat, Nat, Set[A]],
		n, k, m, j *Expr[Nat],
		refines, nested, last, earlier Fact,
	) {
		lift := a.Have(
			"a set of level p is the set d levels finer at its index scaled by 2ᵈ",
			"∀d p i:num. V(p + d, i * 2 ^ d) = V(p, i)",
			Derive(func(b *Argument) {
				b.Induct("d")
				b.Base(
					"zero levels finer is the same set",
					func(c *Argument) {
						c.FixAs[Nat]("p")
						c.FixAs[Nat]("i")
						same := c.Have(
							"p + 0 is p and i·2⁰ is i",
							"p + 0 = p ∧ i * 2 ^ 0 = i",
							ByArith())
						c.Show(
							"so the two sets are one",
							By(Normalized, same))
					})
				b.Step(
					"one level finer doubles the index",
					func(c *Argument, ih Fact) {
						d := c.TermAs[Nat]("d")
						p := c.FixAs[Nat]("p")
						i := c.FixAs[Nat]("i")
						shift := c.Have(
							"p + suc(d) is (p + d) + 1, and i·2^suc(d) is twice i·2ᵈ",
							"p + suc(d) = (p + d) + 1 ∧ i * 2 ^ suc(d) = 2 * (i * 2 ^ d)",
							ByArith(Scaled(i, nat_arith.PowTwoSuc.At(d))))
						c.Show(
							"the level p + d + 1 refines the level p + d",
							By(shift, refines.At(c.TermAs[Nat]("p + d"), c.TermAs[Nat]("i * 2 ^ d")), ih.At(p, i)))
					})
			}))
		within := a.Have(
			"within one level the closure of a set lies in every later set",
			"∀b p i:num. i < b ∧ b ≤ 2 ^ p ⇒ closure(T, V(p, i)) ⊆ V(p, b)",
			Derive(func(c *Argument) {
				c.Induct("b")
				c.Base(
					"no index lies below 0",
					func(d *Argument) {
						d.FixAs[Nat]("p")
						d.FixAs[Nat]("i")
						d.Show(
							"so there is nothing to show",
							By(d.Assume(), nat_order.LessThan))
					})
				c.Step(
					"the set after b holds the closure of V(p, b), and so the closures of the sets before",
					func(d *Argument, ih Fact) {
						b := d.TermAs[Nat]("b")
						p := d.FixAs[Nat]("p")
						i := d.FixAs[Nat]("i")
						given := d.Conjuncts(
							d.Assume(),
							"i < suc(b)",
							"suc(b) ≤ 2ᵖ")
						room := d.Have(
							"b lies below 2ᵖ",
							"b < 2 ^ p",
							ByArith(given[1]))
						link := d.Have(
							"the closure of V(p, b) lies in V(p, suc(b))",
							"closure(T, V(p, b)) ⊆ V(p, suc(b))",
							By(Normalized, nested.At(p, b), room, nat_arith.Add1.At(b)))
						cases := d.Have(
							"i is b or lies below b",
							"i = b ∨ i < b",
							ByArith(given[0]))
						d.Do(cases.SplitDisj(
							LeftHolds(
								"at i = b this is the link itself",
								Given(func(e *Argument, same Fact) {
									e.Show(
										"the closure of V(p, b) lies in V(p, suc(b))",
										same.Rw(),
										By(link))
								})),
							RightHolds(
								"below b the closure lies in V(p, b), inside its closure, inside V(p, suc(b))",
								Given(func(e *Argument, less Fact) {
									before := e.Have(
										"i < b ≤ 2ᵖ",
										"i < b ∧ b ≤ 2 ^ p",
										ByArith(less, room))
									e.Show(
										"so the closure of V(p, i) lies in V(p, suc(b))",
										BySets(
											GroupPremises(before, ih.At(p, i)),
											link,
											topological_space.SubsetClosure.At(T, e.TermAs[Set[A]]("V(p, b)"))))
								}))))
					})
			}))
		bound := a.Have(
			"j·2ⁿ ≤ 2ⁿ⁺ᵐ, as j ≤ 2ᵐ",
			"j * 2 ^ n ≤ 2 ^ (n + m)",
			ByArith(
				nat_order.LessEqMulMono.At(a.TermAs[Nat]("2 ^ n"), j, a.TermAs[Nat]("2 ^ m")),
				last,
				nat_arith.PowAdd.At(a.TermAs[Nat]("2"), n, m)))
		a.Show(
			"at level n + m the closure of V(n, k) = V(n + m, k·2ᵐ) lies in V(n + m, j·2ⁿ) = V(m, j)",
			By(
				within.At(a.TermAs[Nat]("j * 2 ^ n"), a.TermAs[Nat]("n + m"), a.TermAs[Nat]("k * 2 ^ m")),
				earlier,
				bound,
				lift.At(m, n, k),
				lift.At(n, m, j),
				nat_arith.AddSym.At(n, m)))
	}),
})}

// Urysohn — in a normal space, two disjoint closed sets are separated by a
// continuous function into ⟦0, 1⟧, 0 on the one and 1 on the other. The
// dyadic chain V from s up to the complement u of t gives the function
// f(x) = inf S(x), S(x) being 1 and the dyadics k/2ⁿ of the sets V(n, k)
// holding x. At a point of V(n, k) f is at most k/2ⁿ, and off V(m, j) it
// is at least j/2ᵐ: a member k/2ⁿ of S(x) below j/2ᵐ would put x in the
// closure of V(n, k), so in V(m, j). So f is 0 on s ⊆ V(0, 0) and 1 off
// V(0, 1) = u. Where f lies below a the point lies in some V(n, k) with
// k/2ⁿ < a, on which f stays below a, or else a > 1 and the whole space
// serves; where f lies above a ≥ 0, dyadics a < k/2ⁿ < j/2ᵐ < f(x) give the
// complement of the closure of V(n, k), open, holding x since that closure
// lies in V(m, j), and on which f is at least k/2ⁿ; for a < 0 the whole
// space serves. Both sets are open, so f is continuous.
var Urysohn = urysohnThm{family.Add(registry.ProofEntry{
	Name: "Urysohn",
	Key:  "prop_2bab9d348efe183d",
	Reading: "Normality alone, with no T1: the dyadic construction never separates points. " +
		"is_topology enters for the unions of the U(r), so it is a hypothesis and not a law — the " +
		"statement is about two closed sets, not the space. s and t lie in ⋃T by closed_in; f is read on " +
		"⋃T only, and outside it takes any value. The continuity check through the rays splits at the " +
		"ends of ⟦0, 1⟧: for a > 1 the set below a is the whole space, for a < 0 so is the set above a.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s t:set(A).",
		Hypotheses: []string{
			"is_topology(T)",
			"normal_space(T)",
			"closed_in(T, s)",
			"closed_in(T, t)",
			"s ∩ t = ∅",
		},
		Conclusion: "∃f:(A → real). " +
			"    continuous_map(T, real_topology, f) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ &0 ≤ f(x) ∧ f(x) ≤ &1) ∧ " +
			"    (∀x:A. x ∈ s ⇒ f(x) = &0) ∧ " +
			"    (∀x:A. x ∈ t ⇒ f(x) = &1)",
	}, func(
		arg *Argument,
		T *Expr[Set[Set[A]]],
		s, t *Expr[Set[A]],
		topology, normal, sClosed, tClosed, disjoint Fact,
	) {
		two := arg.TermAs[Real]("&2")
		zero := arg.Ctx().Nat(0)
		sInSpace := arg.Have(
			"s, being closed, lies in the space",
			"s ⊆ ⋃T",
			By(sClosed, topological_space.ClosedInDef))
		away := arg.Have(
			"the complement of t is open",
			"⋃T ∖ t ∈ T",
			By(tClosed, topological_space.ClosedInDef))
		inside := arg.Have(
			"s lies in the complement of t",
			"s ⊆ ⋃T ∖ t",
			BySets(sInSpace, disjoint))
		V, chain := arg.UnpackAs[Fun2[Nat, Nat, Set[A]]](
			GroupPremises(
				topology,
				normal,
				sClosed,
				away,
				inside,
				At(UrysohnChain, T, s, arg.TermAs[Set[A]]("⋃T ∖ t"))),
			"V")
		parts := arg.Conjuncts(
			chain,
			"each V(n, k) is open and holds s",
			"the last set of each level is the complement of t",
			"level n + 1 refines level n",
			"and each closure lies in the next set of its level")
		open, last, refines, nested := parts[0], parts[1], parts[2], parts[3]
		_, SDef := arg.LetAs[Fun[A, Set[Real]]](
			"S",
			"λx:A. {y:real | y = &1 ∨ (∃n k:num. k ≤ 2 ^ n ∧ x ∈ V(n, k) ∧ y = &k / &2 ^ n)}")
		f, fDef := arg.LetAs[Fun[A, Real]]("f", "λx:A. inf(S(x))")
		cross := arg.Have(
			"a dyadic below another, cleared of denominators: k/2ⁿ < j/2ᵐ makes k·2ᵐ < j·2ⁿ",
			"∀n k m j:num. ∀y z:real. y = &k / &2 ^ n ∧ z = &j / &2 ^ m ∧ y < z ⇒ k * 2 ^ m < j * 2 ^ n",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.FixAs[Nat]("k")
				m := b.FixAs[Nat]("m")
				b.FixAs[Nat]("j")
				y := b.FixAs[Real]("y")
				z := b.FixAs[Real]("z")
				given := b.Conjuncts(
					b.Assume(),
					"y is k/2ⁿ",
					"z is j/2ᵐ",
					"and y < z")
				yScaled := b.Have(
					"y·2ⁿ = k",
					"y * &2 ^ n = &k",
					By(
						real_order_field.EqDivMulLeft.At(y, b.TermAs[Real]("&k"), b.TermAs[Real]("&2 ^ n")),
						real_pow.PowPos.At(two, n),
						given[0]))
				zScaled := b.Have(
					"z·2ᵐ = j",
					"z * &2 ^ m = &j",
					By(
						real_order_field.EqDivMulLeft.At(z, b.TermAs[Real]("&j"), b.TermAs[Real]("&2 ^ m")),
						real_pow.PowPos.At(two, m),
						given[1]))
				past := b.Have(
					"k = y·2ⁿ < z·2ⁿ",
					"&k < z * &2 ^ n",
					ByArith(yScaled, given[2], real_pow.PowPos.At(two, n)))
				notLess := b.SupposeNot()
				flipped := b.Have(
					"were it not so, j·2ⁿ ≤ k·2ᵐ",
					"j * 2 ^ n ≤ k * 2 ^ m",
					By(nat_order.NotLessThan.At(b.TermAs[Nat]("k * 2 ^ m"), b.TermAs[Nat]("j * 2 ^ n")), notLess))
				b.Show(
					"but j·2ⁿ = z·2ᵐ·2ⁿ exceeds k·2ᵐ, as z·2ⁿ exceeds k",
					ByArith(Scaled(b.TermAs[Real]("&2 ^ n"), zScaled), past, real_pow.PowPos.At(two, m), flipped))
			}))
		nonempty := arg.Have(
			"each S(x) holds 1",
			"∀x:A. S(x) ≠ ∅",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.Show(
					"1 is a member",
					BySets(SDef))
			}))
		bounded := arg.Have(
			"the members of S(x) lie in ⟦0, 1⟧",
			"∀x:A. ∀y:real. y ∈ S(x) ⇒ &0 ≤ y ∧ y ≤ &1",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				y := b.FixAs[Real]("y")
				which := b.Have(
					"y is 1 or a dyadic k/2ⁿ with k ≤ 2ⁿ",
					"y = &1 ∨ (∃n k:num. k ≤ 2 ^ n ∧ x ∈ V(n, k) ∧ y = &k / &2 ^ n)",
					BySets(b.Assume(), SDef))
				b.Do(which.SplitDisj(
					LeftHolds(
						"1 lies in ⟦0, 1⟧",
						Given(func(c *Argument, one Fact) {
							c.Show(
								"0 ≤ 1 ≤ 1",
								ByArith(one))
						})),
					RightHolds(
						"so does k/2ⁿ, k being at most 2ⁿ",
						Given(func(c *Argument, dyadic Fact) {
							n, _, at := c.Unpack2As[Nat, Nat](dyadic, "n", "k")
							facts := c.Conjuncts(
								at,
								"k ≤ 2ⁿ",
								"x ∈ V(n, k)",
								"y = k/2ⁿ")
							scaled := c.Have(
								"y·2ⁿ = k",
								"y * &2 ^ n = &k",
								By(
									real_order_field.EqDivMulLeft.At(y, c.TermAs[Real]("&k"), c.TermAs[Real]("&2 ^ n")),
									real_pow.PowPos.At(two, n),
									facts[2]))
							c.Show(
								"so 0 ≤ y ≤ 1",
								ByArith(scaled, facts[0], real_pow.PowPos.At(two, n)))
						}))))
			}))
		inRange := arg.Have(
			"f takes values in ⟦0, 1⟧",
			"∀x:A. &0 ≤ f(x) ∧ f(x) ≤ &1",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				b.Show(
					"the infimum of a nonempty set inside ⟦0, 1⟧ lies in ⟦0, 1⟧",
					By(
						Normalized,
						real_sup_inf.InfBetweenBounds.At(
							b.TermAs[Set[Real]]("S(x)"), b.TermAs[Real]("&0"), b.TermAs[Real]("&1")),
						nonempty.At(x),
						bounded.At(x),
						fDef))
			}))
		below := arg.Have(
			"at a point of V(n, k), f is at most k/2ⁿ",
			"∀x:A. ∀n k:num. k ≤ 2 ^ n ∧ x ∈ V(n, k) ⇒ f(x) ≤ &k / &2 ^ n",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				b.FixAs[Nat]("n")
				b.FixAs[Nat]("k")
				given := b.Assume()
				q, qDef := b.LetAs[Real]("q", "&k / &2 ^ n")
				member := b.Have(
					"q = k/2ⁿ is a member of S(x)",
					"q ∈ S(x)",
					BySets(given, qDef, SDef))
				b.Show(
					"so the infimum is at most q",
					By(
						real_sup_inf.InfLessEqMember.At(b.TermAs[Set[Real]]("S(x)"), q),
						bounded.At(x),
						member,
						fDef,
						qDef))
			}))
		above := arg.Have(
			"off V(m, j), f is at least j/2ᵐ",
			"∀x:A. ∀m j:num. j ≤ 2 ^ m ∧ x ∉ V(m, j) ⇒ &j / &2 ^ m ≤ f(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				m := b.FixAs[Nat]("m")
				j := b.FixAs[Nat]("j")
				given := b.Conjuncts(
					b.Assume(),
					"j ≤ 2ᵐ",
					"x lies outside V(m, j)")
				r, rDef := b.LetAs[Real]("r", "&j / &2 ^ m")
				floor := b.Have(
					"r bounds S(x) below",
					"∀y:real. y ∈ S(x) ⇒ r ≤ y",
					Derive(func(c *Argument) {
						y := c.FixAs[Real]("y")
						which := c.Have(
							"y is 1 or a dyadic k/2ⁿ of a set V(n, k) holding x",
							"y = &1 ∨ (∃n k:num. k ≤ 2 ^ n ∧ x ∈ V(n, k) ∧ y = &k / &2 ^ n)",
							BySets(c.Assume(), SDef))
						c.Do(which.SplitDisj(
							LeftHolds(
								"r is at most 1, j being at most 2ᵐ",
								Given(func(d *Argument, one Fact) {
									d.Show(
										"r ≤ 1 = y",
										ByArith(
											real_order_field.EqDivMulLeft.At(r, d.TermAs[Real]("&j"), d.TermAs[Real]("&2 ^ m")),
											real_pow.PowPos.At(two, m),
											rDef,
											given[0],
											one))
								})),
							RightHolds(
								"a dyadic y = k/2ⁿ below r would put x in V(m, j)",
								Given(func(d *Argument, dyadic Fact) {
									n, k, at := d.Unpack2As[Nat, Nat](dyadic, "n", "k")
									facts := d.Conjuncts(
										at,
										"k ≤ 2ⁿ",
										"x ∈ V(n, k)",
										"y = k/2ⁿ")
									notAbove := d.SupposeNot()
									less := d.Have(
										"y < r",
										"y < r",
										ByArith(notAbove))
									order := d.Have(
										"so k·2ᵐ < j·2ⁿ",
										"k * 2 ^ m < j * 2 ^ n",
										By(cross.At(n, k, m, j, y, r), facts[2], rDef, less))
									contained := d.Have(
										"and the closure of V(n, k) lies in V(m, j)",
										"closure(T, V(n, k)) ⊆ V(m, j)",
										By(At(UrysohnChainMonotone, T, V, n, k, m, j), refines, nested, given[0], order))
									d.Show(
										"which puts x, a point of V(n, k), in V(m, j)",
										BySets(
											facts[1],
											contained,
											given[1],
											topological_space.SubsetClosure.At(T, d.TermAs[Set[A]]("V(n, k)"))))
								}))))
					}))
				b.Show(
					"so r is at most the infimum",
					By(
						Normalized,
						real_sup_inf.BoundLessEqInf.At(b.TermAs[Set[Real]]("S(x)"), r),
						nonempty.At(x),
						floor,
						fDef,
						rDef))
			}))
		approach := arg.Have(
			"where f lies below c, either 1 < c or a dyadic k/2ⁿ < c of a set V(n, k) holds the point",
			"∀x:A. ∀c:real. f(x) < c ⇒ &1 < c ∨ (∃n k:num. k ≤ 2 ^ n ∧ x ∈ V(n, k) ∧ &k / &2 ^ n < c)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				c := b.FixAs[Real]("c")
				low := b.Assume()
				_, near := b.ObtainAs[Real](
					"some member y of S(x) lies below c",
					"∃y:real. y ∈ S(x) ∧ y < c",
					By(real_sup_inf.InfApproach.At(b.TermAs[Set[Real]]("S(x)"), c), nonempty.At(x), low, fDef))
				facts := b.Conjuncts(
					near,
					"y ∈ S(x)",
					"y < c")
				which := b.Have(
					"y is 1 or a dyadic k/2ⁿ of a set V(n, k) holding x",
					"y = &1 ∨ (∃n k:num. k ≤ 2 ^ n ∧ x ∈ V(n, k) ∧ y = &k / &2 ^ n)",
					BySets(facts[0], SDef))
				b.Show(
					"and y lies below c",
					By(which, facts[1]))
			}))
		onS := arg.Have(
			"f is 0 on s, which lies in V(0, 0)",
			"∀x:A. x ∈ s ⇒ f(x) = &0",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				first := b.Have(
					"V(0, 0) holds s",
					"s ⊆ V(0, 0)",
					ByArith(open.At(zero, zero)))
				holds := b.Have(
					"so x lies in V(0, 0)",
					"x ∈ V(0, 0)",
					BySets(xIn, first))
				b.Show(
					"0 ≤ f(x) ≤ 0/2⁰",
					ByArith(below.At(x, zero, zero), holds, inRange.At(x)))
			}))
		onT := arg.Have(
			"f is 1 on t, which misses V(0, 1)",
			"∀x:A. x ∈ t ⇒ f(x) = &1",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				outside := b.Have(
					"x lies outside V(0, 2⁰), the complement of t",
					"x ∉ V(0, 2 ^ 0)",
					BySets(xIn, last.At(zero)))
				b.Show(
					"1 = 2⁰/2⁰ ≤ f(x) ≤ 1",
					ByArith(above.At(x, zero, b.TermAs[Nat]("2 ^ 0")), outside, inRange.At(x)))
			}))
		rays := arg.Have(
			"the points where f lies below a, and those where it lies above a, form open sets",
			"∀a:real. {x:A | x ∈ ⋃T ∧ f(x) < a} ∈ T ∧ {x:A | x ∈ ⋃T ∧ a < f(x)} ∈ T",
			Derive(func(b *Argument) {
				level := b.FixAs[Real]("a")
				b.Do(SplitConj(
					Case(
						"below a: about each point a set V(n, k) with k/2ⁿ < a, or the whole space when a > 1",
						Simp(Fwd(topological_space.OpenPointwise)),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							position := c.Have(
								"x is a point of the space where f lies below a",
								"x ∈ ⋃T ∧ f(x) < a",
								BySets(c.Assume()))
							ways := c.Have(
								"so 1 < a, or x lies in some V(n, k) with k/2ⁿ < a",
								"&1 < a ∨ (∃n k:num. k ≤ 2 ^ n ∧ x ∈ V(n, k) ∧ &k / &2 ^ n < a)",
								By(approach.At(x, level), position))
							c.Do(ways.SplitDisj(
								LeftHolds(
									"for a > 1 the whole space, f never exceeding 1",
									Given(func(d *Argument, high Fact) {
										d.Take(d.TermAs[Set[A]]("⋃T"))
										d.Do(SplitConjAll(
											Case(
												"the space is open",
												By(topological_space.SpaceOpen.Read(topology))),
											Case(
												"and f lies below a all over it",
												Simp(Fwd(set_basic.SubsetDef)),
												Derive(func(e *Argument) {
													z := e.FixAs[A]("z")
													zIn := e.Assume()
													value := e.Have(
														"f(z) ≤ 1 < a",
														"f(z) < a",
														ByArith(inRange.At(z), high))
													e.Show(
														"z is a point where f lies below a",
														BySets(zIn, value))
												})),
											Case(
												"and it holds x",
												BySets(position))))
									})),
								RightHolds(
									"else the set V(n, k), on which f is at most k/2ⁿ < a",
									Given(func(d *Argument, set Fact) {
										n, k, at := d.Unpack2As[Nat, Nat](set, "n", "k")
										facts := d.Conjuncts(
											at,
											"k ≤ 2ⁿ",
											"x ∈ V(n, k)",
											"k/2ⁿ < a")
										here := d.TermAs[Set[A]]("V(n, k)")
										isOpen := d.Have(
											"V(n, k) is open",
											"V(n, k) ∈ T",
											ByArith(open.At(n, k), facts[0]))
										d.Take(here)
										d.Do(SplitConjAll(
											Case(
												"V(n, k) is open",
												By(isOpen)),
											Case(
												"and f lies below a all over it",
												Simp(Fwd(set_basic.SubsetDef)),
												Derive(func(e *Argument) {
													z := e.FixAs[A]("z")
													zIn := e.Assume()
													value := e.Have(
														"f(z) ≤ k/2ⁿ < a",
														"f(z) < a",
														ByArith(below.At(z, n, k), facts[0], zIn, facts[2]))
													e.Show(
														"z, a point of the open V(n, k), lies in the space, where f lies below a",
														BySets(zIn, value, isOpen))
												})),
											Case(
												"and it holds x",
												By(facts[1]))))
									}))))
						})),
					Case(
						"above a: about each point the complement of the closure of "+
							"a set V(n, k) with a < k/2ⁿ, or the whole space when a < 0",
						Simp(Fwd(topological_space.OpenPointwise)),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							position := c.Have(
								"x is a point of the space where f lies above a",
								"x ∈ ⋃T ∧ a < f(x)",
								BySets(c.Assume()))
							c.Cases(c.Term("a < &0"))
							c.When(
								"for a < 0 the whole space, f never being negative",
								func(d *Argument, negative Fact) {
									d.Take(d.TermAs[Set[A]]("⋃T"))
									d.Do(SplitConjAll(
										Case(
											"the space is open",
											By(topological_space.SpaceOpen.Read(topology))),
										Case(
											"and f lies above a all over it",
											Simp(Fwd(set_basic.SubsetDef)),
											Derive(func(e *Argument) {
												z := e.FixAs[A]("z")
												zIn := e.Assume()
												value := e.Have(
													"a < 0 ≤ f(z)",
													"a < f(z)",
													ByArith(inRange.At(z), negative))
												e.Show(
													"z is a point where f lies above a",
													BySets(zIn, value))
											})),
										Case(
											"and it holds x",
											BySets(position))))
								})
							c.Otherwise(
								"for a ≥ 0, dyadics a < q < r < f(x), and the complement of the closure of the set at q",
								func(d *Argument, nonnegative Fact) {
									atLeastZero := d.Have(
										"a is nonnegative",
										"&0 ≤ a",
										ByArith(nonnegative))
									r, m, j, outer := d.Obtain3As[Real, Nat, Nat](
										"a dyadic r = j/2ᵐ lies between a and f(x)",
										"∃r:real. ∃m j:num. j ≤ 2 ^ m ∧ r = &j / &2 ^ m ∧ a < r ∧ r < f(x)",
										By(At(DyadicBetween, level, d.TermAs[Real]("f(x)")), atLeastZero, position, inRange.At(x)))
									rFacts := d.Conjuncts(
										outer,
										"j ≤ 2ᵐ",
										"r = j/2ᵐ",
										"a < r",
										"r < f(x)")
									ceiling := d.Have(
										"r is at most 1",
										"r ≤ &1",
										ByArith(rFacts[3], inRange.At(x)))
									q, n, k, inner := d.Obtain3As[Real, Nat, Nat](
										"and a dyadic q = k/2ⁿ between a and r",
										"∃q:real. ∃n k:num. k ≤ 2 ^ n ∧ q = &k / &2 ^ n ∧ a < q ∧ q < r",
										By(At(DyadicBetween, level, r), atLeastZero, rFacts[2], ceiling))
									qFacts := d.Conjuncts(
										inner,
										"k ≤ 2ⁿ",
										"q = k/2ⁿ",
										"a < q",
										"q < r")
									order := d.Have(
										"so k·2ᵐ < j·2ⁿ",
										"k * 2 ^ m < j * 2 ^ n",
										By(cross.At(n, k, m, j, q, r), qFacts[1], rFacts[1], qFacts[3]))
									here := d.TermAs[Set[A]]("V(n, k)")
									contained := d.Have(
										"and the closure of V(n, k) lies in V(m, j)",
										"closure(T, V(n, k)) ⊆ V(m, j)",
										By(At(UrysohnChainMonotone, T, V, n, k, m, j), refines, nested, rFacts[0], order))
									exceeds := d.Have(
										"f(x) exceeds r = j/2ᵐ",
										"¬(f(x) ≤ &j / &2 ^ m)",
										ByArith(rFacts[1], rFacts[3]))
									outside := d.Have(
										"so x lies outside V(m, j)",
										"x ∉ V(m, j)",
										By(below.At(x, m, j), rFacts[0], exceeds))
									isOpen := d.Have(
										"V(n, k) is open",
										"V(n, k) ∈ T",
										ByArith(open.At(n, k), qFacts[0]))
									away := d.Have(
										"the complement of the closure of V(n, k) is open",
										"⋃T ∖ closure(T, V(n, k)) ∈ T",
										By(
											topological_space.ClosureClosed.Read(topology).At(here),
											set_order.MemberSubsetUnions.At(T, here),
											isOpen,
											topological_space.ClosedInDef))
									d.Take(d.TermAs[Set[A]]("⋃T ∖ closure(T, V(n, k))"))
									d.Do(SplitConjAll(
										Case(
											"it is open",
											By(away)),
										Case(
											"and off V(n, k) f is at least q > a",
											Simp(Fwd(set_basic.SubsetDef)),
											Derive(func(e *Argument) {
												z := e.FixAs[A]("z")
												off := e.Have(
													"z is a point of the space outside V(n, k)",
													"z ∈ ⋃T ∧ z ∉ V(n, k)",
													BySets(e.Assume(), topological_space.SubsetClosure.At(T, here)))
												value := e.Have(
													"f(z) ≥ k/2ⁿ = q > a",
													"a < f(z)",
													ByArith(above.At(z, n, k), qFacts[0], off, qFacts[1], qFacts[2]))
												e.Show(
													"z is a point where f lies above a",
													BySets(off, value))
											})),
										Case(
											"and it holds x, the closure of V(n, k) lying in V(m, j), which misses x",
											BySets(position, contained, outside))))
								})
						}))))
			}))
		continuity := arg.Have(
			"f is continuous into the line",
			"continuous_map(T, real_topology, f)",
			By(ContinuousIntoRealIff.At(T, f), topology, rays))
		arg.Take(f)
		arg.Show(
			"f is continuous, takes values in ⟦0, 1⟧, and is 0 on s and 1 on t",
			By(continuity, inRange, onS, onT))
	}),
})}

// ContinuousRealSub — the difference of two continuous real functions is
// continuous: f − g is f plus the negative of g.
var ContinuousRealSub = continuousRealSubThm{family.Add(registry.ProofEntry{
	Name: "ContinuousRealSub",
	Key:  "prop_e6ba12e35a96c38f",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f g:(A → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, real_topology, f)",
			"continuous_map(T, real_topology, g)",
		},
		Conclusion: "continuous_map(T, real_topology, λx:A. f(x) - g(x))",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f, g *Arrow[A, Real], h Fact) {
		a.Do(Simp(Fwd(real_ring.RealSubDef)))
		a.Show(
			"f − g is f plus the negative of g, a sum of continuous functions",
			By(
				h,
				ContinuousRealAdd.At(T, f, a.TermAs[Fun[A, Real]]("λx:A. -g(x)")),
				ContinuousRealNeg.At(T, g)))
	}),
})}

// TietzeStep — one step of Tietze's series: a continuous function h on a
// closed set s, bounded by c, is within 2c/3 on s of a continuous function
// on the whole space bounded by c/3. The points where h lies in ⟦−c, −c/3⟧
// and those where it lies in ⟦c/3, c⟧ are h's preimages of closed
// intervals, closed in s and so in the space, and disjoint. A Urysohn
// function u is 0 on the first set and 1 on the second, so k = (2c/3)·u −
// c/3 lies in ⟦−c/3, c/3⟧ everywhere, is −c/3 where h is low and c/3 where
// h is high: there h − k lies in ⟦−2c/3, 0⟧ or ⟦0, 2c/3⟧, and in between h
// and k both lie in ⟦−c/3, c/3⟧.
var TietzeStep = tietzeStepThm{family.Add(registry.ProofEntry{
	Name: "TietzeStep",
	Key:  "prop_be59d5bed7b9938d",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A). ∀h:(A → real). ∀c:real.",
		Hypotheses: []string{
			"is_topology(T)",
			"normal_space(T)",
			"closed_in(T, s)",
			"&0 < c",
			"continuous_map(subtopology(T, s), real_topology, h)",
			"∀x:A. x ∈ s ⇒ |h(x)| ≤ c",
		},
		Conclusion: "∃k:(A → real). " +
			"    continuous_map(T, real_topology, k) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ |k(x)| ≤ c / &3) ∧ " +
			"    (∀x:A. x ∈ s ⇒ |h(x) - k(x)| ≤ &2 * c / &3)",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		s *Expr[Set[A]],
		h *Arrow[A, Real],
		c *Expr[Real],
		topology, normal, sClosed, cPositive, continuity, bounded Fact,
	) {
		closedPieces := a.Have(
			"h's preimage of a closed interval is closed in s, and so in the space",
			"∀p q:real. closed_in(T, preimage_on(⋃subtopology(T, s), h, ⟦p, q⟧))",
			Derive(func(b *Argument) {
				p := b.FixAs[Real]("p")
				q := b.FixAs[Real]("q")
				inS := b.Have(
					"the preimage of the closed ⟦p, q⟧ is closed in s, h being continuous there",
					"closed_in(subtopology(T, s), preimage_on(⋃subtopology(T, s), h, ⟦p, q⟧))",
					By(continuity, continuous.ClosedPreimage, real_topology.ClosedIntervalClosed.At(p, q)))
				b.Show(
					"and a closed subset of the closed s is closed in the space",
					By(topological_space.ClosedInClosedSubtopology.Read(topology), sClosed, inS))
			}))
		L, lowDef := a.LetAs[Set[A]]("L", "preimage_on(⋃subtopology(T, s), h, ⟦-c, -(c / &3)⟧)")
		U, highDef := a.LetAs[Set[A]]("U", "preimage_on(⋃subtopology(T, s), h, ⟦c / &3, c⟧)")
		lowClosed := a.Have(
			"L, where h lies in ⟦−c, −c/3⟧, is closed",
			"closed_in(T, L)",
			By(closedPieces.At(a.TermAs[Real]("-c"), a.TermAs[Real]("-(c / &3)")), lowDef))
		highClosed := a.Have(
			"U, where h lies in ⟦c/3, c⟧, is closed",
			"closed_in(T, U)",
			By(closedPieces.At(a.TermAs[Real]("c / &3"), c), highDef))
		apart := a.Have(
			"no point lies in both, h being at most −c/3 on L and at least c/3 on U",
			"∀x:A. x ∈ L ∧ x ∈ U ⇒ ⊥",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				values := b.Have(
					"h(x) is at most −c/3 and at least c/3",
					"h(x) ≤ -(c / &3) ∧ c / &3 ≤ h(x)",
					BySets(b.Assume(), lowDef, highDef))
				b.Show(
					"which c > 0 forbids",
					ByArith(values, cPositive))
			}))
		disjoint := a.Have(
			"L and U are disjoint",
			"L ∩ U = ∅",
			BySets(apart))
		u, separating := a.UnpackAs[Fun[A, Real]](
			GroupPremises(topology, normal, lowClosed, highClosed, disjoint, Urysohn.At(T, L, U)),
			"u")
		parts := a.Conjuncts(
			separating,
			"Urysohn's function u is continuous",
			"with values in ⟦0, 1⟧",
			"0 on L",
			"and 1 on U")
		within := a.Have(
			"k = (2c/3)·u − c/3 lies in ⟦−c/3, c/3⟧ on the space, u lying in ⟦0, 1⟧",
			"∀x:A. x ∈ ⋃T ⇒ -(c / &3) ≤ &2 * c / &3 * u(x) - c / &3 ∧ &2 * c / &3 * u(x) - c / &3 ≤ c / &3",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				b.Show(
					"c being positive, (2c/3)·u(x) lies in ⟦0, 2c/3⟧",
					ByArith(parts[1].At(x), b.Assume(), cPositive))
			}))
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		a.Take(a.TermAs[Fun[A, Real]]("λx:A. &2 * c / &3 * u(x) - c / &3"))
		a.Do(SplitConjAll(
			Case(
				"k is continuous: the constant 2c/3 times u, less the constant c/3",
				By(
					topology,
					parts[0],
					At(
						ContinuousRealSub,
						T,
						a.TermAs[Fun[A, Real]]("λx:A. &2 * c / &3 * u(x)"),
						a.TermAs[Fun[A, Real]]("λx:A. c / &3")),
					ContinuousRealMul.At(T, a.TermAs[Fun[A, Real]]("λx:A. &2 * c / &3"), u),
					continuous.Constant.At(T, line, a.TermAs[Real]("&2 * c / &3")),
					continuous.Constant.At(T, line, a.TermAs[Real]("c / &3")),
					real_topology.RealSpace,
					set_basic.InUniv)),
			Case(
				"k is bounded by c/3 on the space",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.Show(
						"k(x) lies in ⟦−c/3, c/3⟧",
						ByArith(within.At(x), b.Assume()))
				})),
			Case(
				"and h − k is bounded by 2c/3 on s",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Assume()
					xInSpace := b.Have(
						"x, a point of the closed s, lies in the space",
						"x ∈ ⋃T",
						BySets(xIn, sClosed, topological_space.ClosedInDef))
					b.Cases(b.Term("h(x) ≤ -(c / &3)"))
					b.When(
						"where h(x) ≤ −c/3, x lies in L, so k(x) = −c/3 and h(x) − k(x) lies in ⟦−2c/3, 0⟧",
						func(d *Argument, low Fact) {
							value := d.Have(
								"h(x) lies in ⟦−c, −c/3⟧",
								"-c ≤ h(x) ∧ h(x) ≤ -(c / &3)",
								ByArith(low, bounded.At(x), xIn))
							inL := d.Have(
								"so x lies in L",
								"x ∈ L",
								BySets(lowDef, xIn, xInSpace, value, topological_space.SubtopologySpace))
							d.Show(
								"u(x) = 0 there",
								ByArith(parts[2].At(x), inL, value, cPositive))
						})
					b.Otherwise(
						"otherwise h(x) is high or in between",
						func(d *Argument, notLow Fact) {
							d.Cases(d.Term("c / &3 ≤ h(x)"))
							d.When(
								"where h(x) ≥ c/3, x lies in U, so k(x) = c/3 and h(x) − k(x) lies in ⟦0, 2c/3⟧",
								func(e *Argument, high Fact) {
									value := e.Have(
										"h(x) lies in ⟦c/3, c⟧",
										"c / &3 ≤ h(x) ∧ h(x) ≤ c",
										ByArith(high, bounded.At(x), xIn))
									inU := e.Have(
										"so x lies in U",
										"x ∈ U",
										BySets(highDef, xIn, xInSpace, value, topological_space.SubtopologySpace))
									e.Show(
										"u(x) = 1 there",
										ByArith(parts[3].At(x), inU, value, cPositive))
								})
							d.Otherwise(
								"in between, h(x) and k(x) both lie in ⟦−c/3, c/3⟧",
								func(e *Argument, notHigh Fact) {
									e.Show(
										"so they differ by at most 2c/3",
										ByArith(notLow, notHigh, within.At(x), xInSpace))
								})
						})
				}))))
	}),
})}

// TietzeApproximation — the iteration of Tietze's step: a continuous
// function f on a closed set s, bounded by c, is approached at the
// geometric rate c·rⁿ, r = 2/3, by continuous functions G(n) on the space
// whose successive steps are bounded by c·rⁿ/3. The step is chosen once,
// as a function K(h, n) of a residual h and an index n: by TietzeStep, for
// h continuous on s and bounded there by c·rⁿ, a continuous function
// bounded by c·rⁿ/3 and within 2c·rⁿ/3 of h on s. The functions are built
// by recursion, G(0) = 0 and G(n + 1) = G(n) + K(f − G(n), n), and by
// induction each G(n) is continuous and within c·rⁿ of f on s: the next
// residual is within 2c·rⁿ/3 = c·rⁿ⁺¹ of 0.
var TietzeApproximation = tietzeApproximationThm{family.Add(registry.ProofEntry{
	Name: "TietzeApproximation",
	Key:  "prop_c6126814cb892b12",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A). ∀f:(A → real). ∀c:real.",
		Hypotheses: []string{
			"is_topology(T)",
			"normal_space(T)",
			"closed_in(T, s)",
			"&0 < c",
			"continuous_map(subtopology(T, s), real_topology, f)",
			"∀x:A. x ∈ s ⇒ |f(x)| ≤ c",
		},
		Conclusion: "∃G:(num → A → real). " +
			"    (∀x:A. G(0)(x) = &0) ∧ " +
			"    (∀n:num. continuous_map(T, real_topology, G(n))) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ ⋃T ⇒ |G(n + 1)(x) - G(n)(x)| ≤ c * (&2 / &3) ^ n / &3) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ s ⇒ |f(x) - G(n)(x)| ≤ c * (&2 / &3) ^ n)",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		s *Expr[Set[A]],
		f *Arrow[A, Real],
		c *Expr[Real],
		topology, normal, sClosed, cPositive, continuity, bounded Fact,
	) {
		r, rDef := a.LetAs[Real]("r", "&2 / &3")
		_, KDef := a.LetAs[Fun2[Fun[A, Real], Nat, Fun[A, Real]]](
			"K",
			"λh:(A → real). λn:num. εk:(A → real). "+
				"    continuous_map(T, real_topology, k) ∧ "+
				"    (∀x:A. x ∈ ⋃T ⇒ |k(x)| ≤ c * r ^ n / &3) ∧ "+
				"    (∀x:A. x ∈ s ⇒ |h(x) - k(x)| ≤ &2 * (c * r ^ n) / &3)")
		stepping := a.Have(
			"K(h, n) is a Tietze step for a residual h continuous on s and bounded there by c·rⁿ",
			Statement{
				Binders: "∀h:(A → real). ∀n:num.",
				Hypotheses: []string{
					"continuous_map(subtopology(T, s), real_topology, h)",
					"∀x:A. x ∈ s ⇒ |h(x)| ≤ c * r ^ n",
				},
				Conclusion: "continuous_map(T, real_topology, K(h, n)) ∧ " +
					"(∀x:A. x ∈ ⋃T ⇒ |K(h, n)(x)| ≤ c * r ^ n / &3) ∧ " +
					"(∀x:A. x ∈ s ⇒ |h(x) - K(h, n)(x)| ≤ &2 * (c * r ^ n) / &3)",
			},
			Derive(func(b *Argument) {
				h := b.FixAs[Fun[A, Real]]("h")
				n := b.FixAs[Nat]("n")
				given := b.Assume()
				positive := b.Have(
					"the bound c·rⁿ is positive",
					"&0 < c * r ^ n",
					ByArith(rDef, cPositive, real_pow.PowPos.At(r, n)))
				possible := b.Have(
					"Tietze's step at the bound c·rⁿ gives such a function",
					"∃k:(A → real). "+
						"    continuous_map(T, real_topology, k) ∧ "+
						"    (∀x:A. x ∈ ⋃T ⇒ |k(x)| ≤ c * r ^ n / &3) ∧ "+
						"    (∀x:A. x ∈ s ⇒ |h(x) - k(x)| ≤ &2 * (c * r ^ n) / &3)",
					By(
						At(TietzeStep, T, s, h, b.TermAs[Real]("c * r ^ n")),
						topology,
						normal,
						sClosed,
						positive,
						given))
				b.Show(
					"so the one K chooses is one",
					KDef.Rw(),
					By(possible))
			}))
		zero := a.Ctx().Nat(0)
		G, recursion := a.UnpackAs[Fun2[Nat, A, Real]](
			nat_arith.PrimRecursion.At(
				a.TermAs[Fun2[Fun[A, Real], Nat, Fun[A, Real]]](
					"λH:(A → real). λn:num. λx:A. H(x) + K(λy:A. f(y) - H(y), n)(x)"),
				a.TermAs[Fun[A, Real]]("λx:A. &0")),
			"G")
		start := a.Have(
			"G(0) is 0",
			"∀x:A. G(0)(x) = &0",
			a.ForEach(func(x *Expr[A]) Action { return By(recursion.At(zero)) }))
		next := a.Have(
			"G(n + 1) adds the n-th step K(f − G(n), n) to G(n)",
			"∀n:num. ∀x:A. G(suc(n))(x) = G(n)(x) + K(λy:A. f(y) - G(n)(y), n)(x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.FixAs[A]("x")
				b.Show(
					"the recursion's step, read at x",
					By(Normalized, recursion.At(n)))
			}))
		steps := a.Have(
			"while G(n) is continuous and within c·rⁿ of f on s, "+
				"the n-th step is a Tietze step for the residual f − G(n)",
			Statement{
				Binders: "∀n:num.",
				Hypotheses: []string{
					"continuous_map(T, real_topology, G(n))",
					"∀x:A. x ∈ s ⇒ |f(x) - G(n)(x)| ≤ c * r ^ n",
				},
				Conclusion: "continuous_map(T, real_topology, K(λy:A. f(y) - G(n)(y), n)) ∧ " +
					"(∀x:A. x ∈ ⋃T ⇒ |K(λy:A. f(y) - G(n)(y), n)(x)| ≤ c * r ^ n / &3) ∧ " +
					"(∀x:A. x ∈ s ⇒ |f(x) - G(n)(x) - K(λy:A. f(y) - G(n)(y), n)(x)| ≤ &2 * (c * r ^ n) / &3)",
			},
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				given := b.Conjuncts(
					b.Assume(),
					"G(n) is continuous",
					"and within c·rⁿ of f on s")
				residual := b.Have(
					"the residual f − G(n) is continuous on s, G(n) being continuous on the space",
					"continuous_map(subtopology(T, s), real_topology, λy:A. f(y) - G(n)(y))",
					By(
						continuity,
						given[0],
						At(
							ContinuousRealSub, b.TermAs[Set[Set[A]]]("subtopology(T, s)"), f, b.TermAs[Fun[A, Real]]("G(n)")),
						topological_space.SubtopologyTopology.Read(topology),
						continuous.FromSubtopology))
				b.Show(
					"so K is a step for it",
					By(Normalized, stepping.At(b.TermAs[Fun[A, Real]]("λy:A. f(y) - G(n)(y)"), n), residual, given[1]))
			}))
		approach := a.Have(
			"by induction each G(n) is continuous and within c·rⁿ of f on s",
			"∀n:num. continuous_map(T, real_topology, G(n)) ∧ (∀x:A. x ∈ s ⇒ |f(x) - G(n)(x)| ≤ c * r ^ n)",
			Derive(func(b *Argument) {
				b.Induct("n")
				b.Base(
					"G(0) is the constant 0, within c of f on s",
					SplitConj(
						Case(
							"the constant 0 is continuous",
							By(
								recursion.At(zero),
								topology,
								continuous.Constant.At(T, b.TermAs[Set[Set[Real]]]("real_topology"), b.TermAs[Real]("&0")),
								real_topology.RealSpace,
								set_basic.InUniv)),
						Case(
							"and f is bounded by c = c·r⁰ on s",
							Derive(func(d *Argument) {
								x := d.FixAs[A]("x")
								d.Show(
									"|f(x) − 0| ≤ c",
									ByArith(start.At(x), bounded.At(x), d.Assume()))
							}))))
				b.Step(
					"G(n + 1) adds the step for the residual f − G(n), which leaves it within 2c·rⁿ/3 = c·rⁿ⁺¹ of f",
					func(d *Argument, ih Fact) {
						n := d.TermAs[Nat]("n")
						previous := d.Conjuncts(
							ih,
							"G(n) is continuous",
							"and within c·rⁿ of f on s")
						parts := d.Conjuncts(
							GroupPremises(ih, steps.At(n)),
							"the n-th step is continuous",
							"bounded by c·rⁿ/3 on the space",
							"and within 2c·rⁿ/3 of the residual on s")
						d.Do(SplitConj(
							Case(
								"G(n + 1) is continuous, a sum of continuous functions",
								By(
									recursion.At(n),
									topology,
									previous[0],
									parts[0],
									ContinuousRealAdd.At(
										T, d.TermAs[Fun[A, Real]]("G(n)"), d.TermAs[Fun[A, Real]]("K(λy:A. f(y) - G(n)(y), n)")))),
							Case(
								"and within c·rⁿ⁺¹ of f on s",
								Derive(func(e *Argument) {
									x := e.FixAs[A]("x")
									xIn := e.Assume()
									ratio := e.Have(
										"c·rⁿ⁺¹ is 2c·rⁿ/3",
										"c * r ^ suc(n) = &2 * (c * r ^ n) / &3",
										ByArith(Scaled(e.TermAs[Real]("c * r ^ n"), rDef), Scaled(c, real_pow.PowExpSucClause.At(r, n))))
									e.Show(
										"f − G(n + 1) is the residual less the step",
										ByArith(next.At(n, x), parts[2].At(x), xIn, ratio))
								}))))
					})
			}))
		stepBound := a.Have(
			"each step is bounded by c·rⁿ/3 on the space",
			"∀n:num. ∀x:A. x ∈ ⋃T ⇒ |G(n + 1)(x) - G(n)(x)| ≤ c * r ^ n / &3",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				small := b.Have(
					"the n-th step is bounded by c·rⁿ/3",
					"∀x:A. x ∈ ⋃T ⇒ |K(λy:A. f(y) - G(n)(y), n)(x)| ≤ c * r ^ n / &3",
					By(Normalized, steps.At(n), approach.At(n)))
				b.Show(
					"G(n + 1) − G(n) is that step",
					ByArith(next.At(n, x), small.At(x), xIn, nat_arith.Add1.At(n)))
			}))
		a.Take(G)
		a.Show(
			"G starts at 0, is continuous, moves by at most "+
				"c·rⁿ/3 at the n-th step and is within c·rⁿ of f on s",
			By(start, stepBound, approach))
	}),
})}

// TelescopingUniformLimit — continuous real functions G(n) whose steps are
// bounded by the drops of a sequence e tending to 0 converge uniformly, at
// rate e, to a continuous function. Adding steps, G(n + j) lies within
// e(n) − e(n + j) of G(n), so at each point the values form a Cauchy
// sequence and converge to some g(x). Were G(n)(x) farther than e(n) from
// g(x), by a margin 2δ, an index n + N past which G is within δ of g(x) and
// e within δ of 0 would put G(n)(x) within e(n) + 2δ of g(x). So G(n) is
// within e(n) of g on the whole space, and g, a uniform limit of
// continuous functions, is continuous.
var TelescopingUniformLimit = telescopingUniformLimitThm{family.Add(registry.ProofEntry{
	Name: "TelescopingUniformLimit",
	Key:  "prop_913de67a7f563194",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀G:(num → A → real). ∀e:(num → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"∀n:num. continuous_map(T, real_topology, G(n))",
			"∀n:num. ∀x:A. x ∈ ⋃T ⇒ |G(n + 1)(x) - G(n)(x)| ≤ e(n) - e(n + 1)",
			"e ⟶ &0",
		},
		Conclusion: "∃g:(A → real). " +
			"    continuous_map(T, real_topology, g) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ (λn:num. G(n)(x)) ⟶ g(x)) ∧ " +
			"    (∀n:num. ∀x:A. x ∈ ⋃T ⇒ |G(n)(x) - g(x)| ≤ e(n))",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		G *Arrow2[Nat, A, Real],
		e *Arrow[Nat, Real],
		topology, continuity, steps, vanishing Fact,
	) {
		telescoping := a.Have(
			"j steps from G(n) cover at most e(n) − e(n + j)",
			"∀n j:num. ∀x:A. x ∈ ⋃T ⇒ |G(n + j)(x) - G(n)(x)| ≤ e(n) - e(n + j)",
			Derive(func(b *Argument) {
				b.Induct("j")
				b.Base(
					"no step covers no distance",
					ByArith())
				b.Step(
					"one more step adds at most e(n + j) − e(n + j + 1), by the triangle inequality",
					func(c *Argument, ih Fact) {
						n := c.FixAs[Nat]("n")
						x := c.FixAs[A]("x")
						xIn := c.Assume()
						c.Do(Simp(Fwd(nat_arith.AddSuc)))
						k := c.TermAs[Nat]("n + j")
						c.Show(
							"G(n + j + 1) is within e(n + j) − e(n + j + 1) of G(n + j)",
							ByArith(ih.At(n, x), steps.At(k, x), nat_arith.Add1.At(k), xIn))
					})
			}))
		cauchy := a.Have(
			"at each point of the space the values G(n)(x) form a Cauchy sequence",
			"∀x:A. x ∈ ⋃T ⇒ real_cauchy(λn:num. G(n)(x))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				b.Do(Unfold(real_sequences.RealCauchyDef))
				b.FixAs[Real]("ε")
				positive := b.Assume()
				N, small := b.ObtainAs[Nat](
					"past some index N, e is within ε/2 of 0",
					"∃N:num. ∀n:num. N ≤ n ⇒ |e(n) - &0| < ε / &2",
					ByArith(
						b.Unfolded(vanishing, real_sequences.RealConvergesToDef).At(b.TermAs[Real]("ε / &2")),
						positive))
				later := b.Have(
					"past N, G(n) is within ε of every later G(n + j)",
					"∀n j:num. N ≤ n ⇒ |G(n + j)(x) - G(n)(x)| < ε",
					Derive(func(c *Argument) {
						n := c.FixAs[Nat]("n")
						j := c.FixAs[Nat]("j")
						past := c.Assume()
						c.Show(
							"G(n + j) is within e(n) − e(n + j) of G(n), and e(n), e(n + j) lie within ε/2 of 0",
							ByArith(telescoping.At(n, j, x), small.At(n), small.At(c.TermAs[Nat]("n + j")), past, xIn))
					}))
				b.Take(N)
				m := b.FixAs[Nat]("m")
				n := b.FixAs[Nat]("n")
				past := b.Assume()
				b.Cases(b.Term("n ≤ m"))
				b.When(
					"G(m) is G(n) some steps on",
					func(c *Argument, order Fact) {
						j, gap := c.ObtainAs[Nat](
							"m is n plus a gap j",
							"∃j:num. m = n + j",
							By(order, nat_order.LessEqExists.At(m, n)))
						c.Do(gap.Rw())
						c.Show(
							"G(n + j) is within ε of G(n), n being past N",
							By(later.At(n, j), past))
					})
				b.Otherwise(
					"G(n) is G(m) some steps on",
					func(c *Argument, order Fact) {
						j, gap := c.ObtainAs[Nat](
							"n is m plus a gap j",
							"∃j:num. n = m + j",
							ByArith(order, nat_order.LessEqExists.At(n, m)))
						c.Do(gap.Rw())
						c.Show(
							"G(m + j) is within ε of G(m), m being past N",
							ByArith(later.At(m, j), past))
					})
			}))
		converges := a.Have(
			"so at each point the values converge, to their upper limit",
			"∀x:A. x ∈ ⋃T ⇒ (λn:num. G(n)(x)) ⟶ real_limsup(λn:num. G(n)(x))",
			By(cauchy, real_sequences.CauchyConverges))
		rate := a.Have(
			"G(n) is within e(n) of the limit",
			"∀n:num. ∀x:A. x ∈ ⋃T ⇒ |G(n)(x) - real_limsup(λm:num. G(m)(x))| ≤ e(n)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				l, lDef := b.LetAs[Real]("l", "real_limsup(λm:num. G(m)(x))")
				farther := b.SupposeNot()
				δ, δDef := b.LetAs[Real]("δ", "(|G(n)(x) - l| - e(n)) / &2")
				margin := b.Have(
					"were G(n)(x) farther than e(n) from the limit l, the margin δ would be positive",
					"&0 < δ",
					ByArith(farther, δDef))
				N, tail := b.ObtainAs[Nat](
					"past some index N, G is within δ of l and e within δ of 0",
					"∃N:num. ∀m:num. N ≤ m ⇒ |G(m)(x) - l| < δ ∧ |e(m) - &0| < δ",
					By(
						real_sequences.LimitCommonIndex.At(
							b.TermAs[Fun[Nat, Real]]("λm:num. G(m)(x)"), e, l, b.TermAs[Real]("&0"), δ),
						converges.At(x),
						xIn,
						lDef,
						vanishing,
						margin))
				b.Show(
					"but G(n + N)(x) lies within e(n) − e(n + N) of G(n)(x) "+
						"and within δ of l, so G(n)(x) lies within e(n) + 2δ of l",
					ByArith(tail.At(b.TermAs[Nat]("n + N")), telescoping.At(n, N, x), xIn, δDef, farther))
			}))
		uniform := a.Have(
			"so G converges to the limit uniformly on the space",
			Statement{
				Binders: "∀ε:real.",
				Hypotheses: []string{
					"&0 < ε",
				},
				Conclusion: "∃N:num. ∀n:num. ∀x:A. N ≤ n ∧ x ∈ ⋃T ⇒ |G(n)(x) - real_limsup(λm:num. G(m)(x))| < ε",
			},
			Derive(func(b *Argument) {
				ε := b.FixAs[Real]("ε")
				positive := b.Assume()
				N, small := b.ObtainAs[Nat](
					"past some index N, e is within ε of 0",
					"∃N:num. ∀n:num. N ≤ n ⇒ |e(n) - &0| < ε",
					By(b.Unfolded(vanishing, real_sequences.RealConvergesToDef).At(ε), positive))
				b.Take(N)
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				b.Show(
					"G(n)(x) is within e(n) < ε of the limit",
					ByArith(rate.At(n, x), small.At(n), b.Assume()))
			}))
		limit := a.TermAs[Fun[A, Real]]("λx:A. real_limsup(λn:num. G(n)(x))")
		a.Take(limit)
		a.Do(SplitConjAll(
			Case(
				"the limit is continuous, a uniform limit of continuous functions",
				By(topology, continuity, uniform, UniformLimitContinuous.At(T, G, limit))),
			Case(
				"G converges to it at each point",
				By(converges)),
			Case(
				"within e(n) at the n-th function",
				By(rate))))
	}),
})}

// Tietze — in a normal space, a continuous function from a closed set
// into ⟦a, b⟧ extends to a continuous function on the space into ⟦a, b⟧.
// For a = b the constant a serves. Otherwise let m be the midpoint and c
// the half-width of ⟦a, b⟧: f − m is continuous on s and bounded there by
// c, so TietzeApproximation gives continuous G(n) on the space, G(0) = 0,
// whose steps are bounded by c·rⁿ/3 = c·rⁿ − c·rⁿ⁺¹ (r = 2/3), within
// c·rⁿ of f − m on s. They converge uniformly to a continuous u within
// c·rⁿ of G(n) (TelescopingUniformLimit): at n = 0, |u| ≤ c; on s, G(n)
// tends both to u and to f − m, so u = f − m. The extension is u + m.
var Tietze = tietzeThm{family.Add(registry.ProofEntry{
	Name: "Tietze",
	Key:  "prop_ebcbd18790912b0c",
	Reading: "a ≤ b is load-bearing when s is empty: the extension must take a value in ⟦a, b⟧ " +
		"somewhere. f is read on s alone; continuity on the subspace asks nothing of f elsewhere.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A). ∀f:(A → real). ∀a b:real.",
		Hypotheses: []string{
			"is_topology(T)",
			"normal_space(T)",
			"closed_in(T, s)",
			"a ≤ b",
			"continuous_map(subtopology(T, s), real_topology, f)",
			"∀x:A. x ∈ s ⇒ a ≤ f(x) ∧ f(x) ≤ b",
		},
		Conclusion: "∃g:(A → real). " +
			"    continuous_map(T, real_topology, g) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ a ≤ g(x) ∧ g(x) ≤ b) ∧ " +
			"    (∀x:A. x ∈ s ⇒ g(x) = f(x))",
	}, func(
		arg *Argument,
		T *Expr[Set[Set[A]]],
		s *Expr[Set[A]],
		f *Arrow[A, Real],
		a, b *Expr[Real],
		topology, normal, sClosed, ordered, continuity, between Fact,
	) {
		line := arg.TermAs[Set[Set[Real]]]("real_topology")
		zero := arg.Ctx().Nat(0)
		arg.Cases(arg.Term("a = b"))
		arg.When(
			"for a = b, f is the constant a on s, and so is its extension",
			func(p *Argument, equal Fact) {
				p.Take(p.TermAs[Fun[A, Real]]("λx:A. a"))
				p.Do(SplitConjAll(
					Case(
						"a constant is continuous",
						By(topology, continuous.Constant.At(T, line, a), real_topology.RealSpace, set_basic.InUniv)),
					Case(
						"it lies in ⟦a, b⟧",
						ByArith(ordered)),
					Case(
						"and agrees with f on s, where a ≤ f ≤ b = a",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							d.Show(
								"f(x) is squeezed to a",
								ByArith(between.At(x), d.Assume(), equal))
						}))))
			})
		arg.Otherwise(
			"for a < b, centre f at the midpoint m and sum Tietze's series for f − m",
			func(p *Argument, unequal Fact) {
				m, mDef := p.LetAs[Real]("m", "(a + b) / &2")
				c, cDef := p.LetAs[Real]("c", "(b - a) / &2")
				positive := p.Have(
					"the half-width c is positive",
					"&0 < c",
					ByArith(unequal, ordered, cDef))
				subspace := p.TermAs[Set[Set[A]]]("subtopology(T, s)")
				centred := p.Have(
					"f − m is continuous on s",
					"continuous_map(subtopology(T, s), real_topology, λx:A. f(x) - m)",
					By(
						continuity,
						At(ContinuousRealSub, subspace, f, p.TermAs[Fun[A, Real]]("λx:A. m")),
						topological_space.SubtopologyTopology.Read(topology),
						continuous.Constant.At(subspace, line, m),
						real_topology.RealSpace,
						set_basic.InUniv))
				small := p.Have(
					"and bounded on s by c, f lying in ⟦a, b⟧ = ⟦m − c, m + c⟧",
					"∀x:A. x ∈ s ⇒ |f(x) - m| ≤ c",
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						d.Show(
							"a ≤ f(x) ≤ b",
							ByArith(between.At(x), d.Assume(), mDef, cDef))
					}))
				G, approximation := p.UnpackAs[Fun2[Nat, A, Real]](
					GroupPremises(
						topology,
						normal,
						sClosed,
						positive,
						centred,
						small,
						At(TietzeApproximation, T, s, p.TermAs[Fun[A, Real]]("λx:A. f(x) - m"), c)),
					"G")
				r, rDef := p.LetAs[Real]("r", "&2 / &3")
				parts := p.Conjuncts(
					approximation,
					"G(0) is 0",
					"each G(n) is continuous",
					"the n-th step is bounded by c·rⁿ/3",
					"and G(n) is within c·rⁿ of f − m on s")
				telescoped := p.Have(
					"the steps are bounded by the drops c·rⁿ − c·rⁿ⁺¹ = c·rⁿ/3",
					"∀n:num. ∀x:A. x ∈ ⋃T ⇒ |G(n + 1)(x) - G(n)(x)| ≤ c * r ^ n - c * r ^ (n + 1)",
					Derive(func(d *Argument) {
						n := d.FixAs[Nat]("n")
						x := d.FixAs[A]("x")
						xIn := d.Assume()
						ratio := d.Have(
							"c·rⁿ⁺¹ is 2c·rⁿ/3",
							"c * r ^ (n + 1) = &2 * (c * r ^ n) / &3",
							ByArith(Scaled(d.TermAs[Real]("c * r ^ n"), rDef), Scaled(c, real_pow.PowAddOne.At(r, n))))
						d.Show(
							"c·rⁿ/3 = c·rⁿ − 2c·rⁿ/3",
							ByArith(parts[2].At(n, x), xIn, ratio))
					}))
				vanishing := p.Have(
					"the bounds c·rⁿ tend to 0, r being below 1",
					"(λn:num. c * r ^ n) ⟶ &0",
					ByArith(
						rDef,
						real_sequences.PowerTendsToZero.At(r),
						real_sequences.LimitScale.At(p.TermAs[Fun[Nat, Real]]("λn:num. r ^ n"), p.TermAs[Real]("&0"), c)))
				u, uniform := p.UnpackAs[Fun[A, Real]](
					GroupPremises(
						topology,
						parts[1],
						telescoped,
						vanishing,
						At(TelescopingUniformLimit, T, G, p.TermAs[Fun[Nat, Real]]("λn:num. c * r ^ n"))),
					"u")
				limit := p.Conjuncts(
					uniform,
					"G converges uniformly to a continuous u",
					"pointwise",
					"within c·rⁿ at the n-th function")
				bound := p.Have(
					"so |u| ≤ c on the space, G(0) being 0",
					"∀x:A. x ∈ ⋃T ⇒ |u(x)| ≤ c",
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						d.Show(
							"|G(0)(x) − u(x)| ≤ c·r⁰",
							ByArith(limit[2].At(zero, x), parts[0].At(x), d.Assume()))
					}))
				agrees := p.Have(
					"on s, u is f − m: G(n) tends to both",
					"∀x:A. x ∈ s ⇒ u(x) = f(x) - m",
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						xIn := d.Assume()
						inSpace := d.Have(
							"x, a point of the closed s, lies in the space",
							"x ∈ ⋃T",
							BySets(xIn, sClosed, topological_space.ClosedInDef))
						near := d.Have(
							"G(n)(x) is within c·rⁿ of f(x) − m",
							"∀n:num. |G(n)(x) - (f(x) - m)| ≤ c * r ^ n",
							d.ForEach(func(n *Expr[Nat]) Action {
								return ByArith(parts[3].At(n, x), xIn)
							}))
						values := d.TermAs[Fun[Nat, Real]]("λn:num. G(n)(x)")
						target := d.TermAs[Real]("f(x) - m")
						toTarget := d.Have(
							"so G(n)(x) tends to f(x) − m",
							"(λn:num. G(n)(x)) ⟶ f(x) - m",
							By(
								real_sequences.LimitSqueezeDistance.At(
									values,
									d.TermAs[Fun[Nat, Real]]("λn:num. f(x) - m"),
									d.TermAs[Fun[Nat, Real]]("λn:num. c * r ^ n"),
									target),
								near,
								vanishing,
								real_sequences.LimitConst.At(target)))
						d.Show(
							"and to u(x), and a limit is unique",
							By(
								real_sequences.LimitUnique.At(values, d.TermAs[Real]("u(x)"), target),
								limit[1].At(x),
								inSpace,
								toTarget))
					}))
				p.Take(p.TermAs[Fun[A, Real]]("λx:A. u(x) + m"))
				p.Do(SplitConjAll(
					Case(
						"u + m is continuous",
						By(
							topology,
							limit[0],
							ContinuousRealAdd.At(T, u, p.TermAs[Fun[A, Real]]("λx:A. m")),
							continuous.Constant.At(T, line, m),
							real_topology.RealSpace,
							set_basic.InUniv)),
					Case(
						"it lies in ⟦m − c, m + c⟧ = ⟦a, b⟧",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							d.Show(
								"|u(x)| ≤ c",
								ByArith(bound.At(x), d.Assume(), mDef, cDef))
						})),
					Case(
						"and on s it is f",
						Derive(func(d *Argument) {
							x := d.FixAs[A]("x")
							d.Show(
								"u(x) + m = f(x)",
								ByArith(agrees.At(x), d.Assume()))
						}))))
			})
	}),
})}

// UrysohnIff — a space is normal exactly when disjoint closed sets are
// separated by continuous functions into ⟦0, 1⟧. Normality gives the
// function by Urysohn's lemma. Conversely the points where such a function
// lies below 1/2 and those where it lies above 1/2 form open sets, by the
// criterion through the rays; the first holds s, where f is 0, the second
// t, where f is 1, and no point lies in both.
var UrysohnIff = urysohnIffThm{family.Add(registry.ProofEntry{
	Name: "UrysohnIff",
	Key:  "prop_5474f783bebae5b0",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)).",
		Hypotheses: []string{
			"is_topology(T)",
		},
		Conclusion: "normal_space(T) ⇔ " +
			"∀s t:set(A). " +
			"    closed_in(T, s) ∧ closed_in(T, t) ∧ s ∩ t = ∅ ⇒ " +
			"    ∃f:(A → real). " +
			"        continuous_map(T, real_topology, f) ∧ " +
			"        (∀x:A. x ∈ ⋃T ⇒ &0 ≤ f(x) ∧ f(x) ≤ &1) ∧ " +
			"        (∀x:A. x ∈ s ⇒ f(x) = &0) ∧ " +
			"        (∀x:A. x ∈ t ⇒ f(x) = &1)",
	}, func(a *Argument, T *Expr[Set[Set[A]]], topology Fact) {
		a.Iff()

		a.Forward(
			"a normal space separates disjoint closed sets by a function, by Urysohn's lemma",
			func(b *Argument, normal Fact) {
				s := b.FixAs[Set[A]]("s")
				t := b.FixAs[Set[A]]("t")
				b.Show(
					"Urysohn's function for s and t",
					By(Urysohn.At(T, s, t), topology, normal, b.Assume()))
			})

		a.Backward(
			"a separating function pulls the halves of its range back to disjoint open sets",
			func(b *Argument, separated Fact) {
				b.Do(Simp(Fwd(separation.NormalSpaceDef)))
				s := b.FixAs[Set[A]]("s")
				t := b.FixAs[Set[A]]("t")
				given := b.Assume()
				_, separating := b.ObtainAs[Fun[A, Real]](
					"some continuous f into ⟦0, 1⟧ is 0 on s and 1 on t",
					"∃f:(A → real). "+
						"    continuous_map(T, real_topology, f) ∧ "+
						"    (∀x:A. x ∈ ⋃T ⇒ &0 ≤ f(x) ∧ f(x) ≤ &1) ∧ "+
						"    (∀x:A. x ∈ s ⇒ f(x) = &0) ∧ "+
						"    (∀x:A. x ∈ t ⇒ f(x) = &1)",
					By(separated.At(s, t), given))
				facts := b.Conjuncts(
					separating,
					"f is continuous",
					"into ⟦0, 1⟧",
					"0 on s",
					"and 1 on t")
				inSpace := b.Have(
					"s and t, being closed, lie in the space",
					"s ⊆ ⋃T ∧ t ⊆ ⋃T",
					By(given, topological_space.ClosedInDef))
				rays := b.Conjuncts(
					b.Simplified(facts[0], Fwd(ContinuousIntoRealIff)),
					"f being continuous, the points where it lies below any a form an open set",
					"and so do those where it lies above a")
				half := b.TermAs[Real]("&1 / &2")
				apart := b.Have(
					"f is not both below and above 1/2",
					"∀x:A. ¬(f(x) < &1 / &2 ∧ &1 / &2 < f(x))",
					b.ForEach(func(x *Expr[A]) Action { return ByArith() }))
				b.Take(b.TermAs[Set[A]]("{x:A | x ∈ ⋃T ∧ f(x) < &1 / &2}"))
				b.Take(b.TermAs[Set[A]]("{x:A | x ∈ ⋃T ∧ &1 / &2 < f(x)}"))
				b.Do(SplitConjAll(
					Case(
						"the points below 1/2 form an open set",
						By(rays[0].At(half))),
					Case(
						"so do the points above 1/2",
						By(rays[1].At(half))),
					Case(
						"s lies below 1/2, f being 0 there",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							value := c.Have(
								"f(x) = 0 < 1/2",
								"f(x) < &1 / &2",
								ByArith(facts[2].At(x), xIn))
							c.Show(
								"x is a point of the space below 1/2",
								BySets(xIn, inSpace, value))
						})),
					Case(
						"t lies above 1/2, f being 1 there",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							xIn := c.Assume()
							value := c.Have(
								"f(x) = 1 > 1/2",
								"&1 / &2 < f(x)",
								ByArith(facts[3].At(x), xIn))
							c.Show(
								"x is a point of the space above 1/2",
								BySets(xIn, inSpace, value))
						})),
					Case(
						"and no point lies both below and above 1/2",
						BySets(apart))))
			})
	}),
})}

// TietzeUnbounded — in a normal space a continuous real function on a
// closed set extends to a continuous real function on the space. The map
// t ↦ t/(1 + |t|) squashes the line into ⟬−1, 1⟭, and y ↦ y/(1 − |y|)
// undoes it. Tietze extends the squashed f to a continuous h into
// ⟦−1, 1⟧. The points where |h| reaches 1 form a closed set missing s, so
// a Urysohn function k is 0 there and 1 on s; then h·k stays inside
// ⟬−1, 1⟭ and is h on s, and unsquashing h·k extends f. An empty s needs
// no case of its own.
var TietzeUnbounded = tietzeUnboundedThm{family.Add(registry.ProofEntry{
	Name: "TietzeUnbounded",
	Key:  "prop_33b6d45ad4605c24",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀s:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"normal_space(T)",
			"closed_in(T, s)",
			"continuous_map(subtopology(T, s), real_topology, f)",
		},
		Conclusion: "∃g:(A → real). continuous_map(T, real_topology, g) ∧ (∀x:A. x ∈ s ⇒ g(x) = f(x))",
	}, func(
		arg *Argument,
		T *Expr[Set[Set[A]]],
		s *Expr[Set[A]],
		f *Arrow[A, Real],
		topology, normal, sClosed, continuity Fact,
	) {
		line := arg.TermAs[Set[Set[Real]]]("real_topology")
		one := arg.TermAs[Real]("&1")
		minusOne := arg.TermAs[Real]("-&1")
		unit := arg.TermAs[Fun[A, Real]]("λx:A. &1")
		denominator := arg.Have(
			"1 + |t| is positive",
			"∀t:real. &0 < &1 + |t|",
			ByArith())
		squashBounds := arg.Have(
			"t/(1 + |t|) lies strictly between −1 and 1",
			"∀t:real. -&1 < t / (&1 + |t|) ∧ t / (&1 + |t|) < &1",
			Derive(func(d *Argument) {
				t := d.FixAs[Real]("t")
				d.Show(
					"cross-multiply by 1 + |t|",
					ByArith(
						denominator.At(t),
						real_order_field.LessThanDivMulLeft.At(minusOne, t, d.TermAs[Real]("&1 + |t|"))))
			}))
		unsquash := arg.Have(
			"y ↦ y/(1 − |y|) undoes the squashing",
			"∀t:real. t / (&1 + |t|) / (&1 - |t / (&1 + |t|)|) = t",
			Derive(func(d *Argument) {
				t := d.FixAs[Real]("t")
				own := d.Have(
					"1 + |t| is its own absolute value",
					"|&1 + |t|| = &1 + |t|",
					ByArith())
				gap := d.Have(
					"so 1 − |t/(1 + |t|)| is 1/(1 + |t|)",
					"&1 - |t / (&1 + |t|)| = &1 / (&1 + |t|)",
					ByArith(denominator.At(t), own))
				positive := d.Have(
					"which is positive",
					"&0 < &1 - |t / (&1 + |t|)|",
					ByArith(denominator.At(t), gap))
				d.Show(
					"and t/(1 + |t|) divided by 1/(1 + |t|) is t",
					ByArith(gap, positive))
			}))
		subspace := arg.TermAs[Set[Set[A]]]("subtopology(T, s)")
		subspaceTopology := topological_space.SubtopologyTopology.Read(topology)
		size := arg.Have(
			"1 + |f| is continuous on s",
			"continuous_map(subtopology(T, s), real_topology, λx:A. &1 + |f(x)|)",
			By(
				subspaceTopology,
				continuity,
				ContinuousRealAdd.At(subspace, unit, arg.TermAs[Fun[A, Real]]("λx:A. |f(x)|")),
				At(ContinuousRealAbs, subspace, f),
				continuous.Constant.At(subspace, line, one),
				real_topology.RealSpace,
				set_basic.InUniv))
		squashedF := arg.TermAs[Fun[A, Real]]("λx:A. f(x) / (&1 + |f(x)|)")
		squashed := arg.Have(
			"so is f squashed, f/(1 + |f|)",
			"continuous_map(subtopology(T, s), real_topology, λx:A. f(x) / (&1 + |f(x)|))",
			By(
				subspaceTopology,
				continuity,
				size,
				denominator,
				At(ContinuousRealDiv, subspace, f, arg.TermAs[Fun[A, Real]]("λx:A. &1 + |f(x)|"))))
		within := arg.Have(
			"the squashed f lies in ⟦−1, 1⟧ on s",
			"∀x:A. x ∈ s ⇒ -&1 ≤ f(x) / (&1 + |f(x)|) ∧ f(x) / (&1 + |f(x)|) ≤ &1",
			arg.ForEach(func(x *Expr[A]) Action {
				return ByArith(squashBounds.At(f.Apply(x)))
			}))
		ordered := arg.Have(
			"−1 lies below 1",
			"-&1 ≤ &1",
			ByArith())
		h, extension := arg.UnpackAs[Fun[A, Real]](
			GroupPremises(
				topology,
				normal,
				sClosed,
				ordered,
				squashed,
				within,
				Tietze.At(T, s, squashedF, minusOne, one)),
			"h")
		hParts := arg.Conjuncts(
			extension,
			"Tietze extends the squashed f to a continuous h",
			"into ⟦−1, 1⟧",
			"which is the squashed f on s")
		hSize := arg.Have(
			"|h| is continuous",
			"continuous_map(T, real_topology, λx:A. |h(x)|)",
			By(topology, hParts[0], At(ContinuousRealAbs, T, h)))
		rays := arg.Conjuncts(
			arg.Simplified(hSize, Fwd(ContinuousIntoRealIff)),
			"the points where |h| lies below a value form an open set",
			"and so do those where it lies above one")
		O, ODef := arg.LetAs[Set[A]]("O", "{x:A | x ∈ ⋃T ∧ |h(x)| < &1}")
		rest := arg.TermAs[Set[A]]("⋃T ∖ O")
		closed := arg.Have(
			"O, where |h| < 1, is open, so the rest of the space, where |h| reaches 1, is closed",
			"closed_in(T, ⋃T ∖ O)",
			By(ODef, rays[0].At(one), topological_space.OpenClosedComplement.At(T, O)))
		inside := arg.Have(
			"on s, h is the squashed f, so |h| < 1",
			"∀x:A. x ∈ s ⇒ |h(x)| < &1",
			Derive(func(d *Argument) {
				x := d.FixAs[A]("x")
				xIn := d.Assume()
				d.Show(
					"t/(1 + |t|) lies strictly between −1 and 1 at t = f(x)",
					ByArith(hParts[2].At(x), squashBounds.At(f.Apply(x)), xIn))
			}))
		apart := arg.Have(
			"so the rest of the space misses s",
			"(⋃T ∖ O) ∩ s = ∅",
			BySets(ODef, inside))
		k, separating := arg.UnpackAs[Fun[A, Real]](
			GroupPremises(
				topology,
				normal,
				closed,
				sClosed,
				apart,
				Urysohn.At(T, rest, s)),
			"k")
		kParts := arg.Conjuncts(
			separating,
			"Urysohn gives a continuous k",
			"into ⟦0, 1⟧",
			"0 where |h| reaches 1",
			"and 1 on s")
		small := arg.Have(
			"1 − |h·k| is positive: h·k stays strictly inside ⟬−1, 1⟭",
			"∀x:A. x ∈ ⋃T ⇒ &0 < &1 - |h(x) * k(x)|",
			Derive(func(d *Argument) {
				x := d.FixAs[A]("x")
				xIn := d.Assume()
				d.Cases(d.Term("x ∈ O"))
				d.When(
					"on O, |h(x)| < 1 and k(x) lies in ⟦0, 1⟧",
					func(b *Argument, inO Fact) {
						below := b.Have(
							"|h(x)| < 1",
							"|h(x)| < &1",
							BySets(ODef, inO))
						b.Show(
							"so |h(x)·k(x)| = |h(x)|·k(x) < 1",
							ByArith(
								below,
								kParts[1].At(x),
								xIn,
								real_sgn_abs.AbsNonneg.At(b.TermAs[Real]("h(x)")),
								real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("k(x)"))))
					})
				d.Otherwise(
					"off O, |h(x)| reaches 1 and k(x) is 0",
					func(b *Argument, outside Fact) {
						reached := b.Have(
							"x lies in the rest of the space",
							"x ∈ ⋃T ∖ O",
							BySets(xIn, outside))
						b.Show(
							"so h(x)·k(x) = 0",
							ByArith(kParts[2].At(x), reached))
					})
			}))
		product := arg.TermAs[Fun[A, Real]]("λx:A. h(x) * k(x)")
		productContinuous := arg.Have(
			"h·k is continuous",
			"continuous_map(T, real_topology, λx:A. h(x) * k(x))",
			By(topology, hParts[0], kParts[0], ContinuousRealMul.At(T, h, k)))
		margin := arg.TermAs[Fun[A, Real]]("λx:A. &1 - |h(x) * k(x)|")
		marginContinuous := arg.Have(
			"so is 1 − |h·k|",
			"continuous_map(T, real_topology, λx:A. &1 - |h(x) * k(x)|)",
			By(
				topology,
				productContinuous,
				ContinuousRealSub.At(T, unit, arg.TermAs[Fun[A, Real]]("λx:A. |h(x) * k(x)|")),
				At(ContinuousRealAbs, T, product),
				continuous.Constant.At(T, line, one),
				real_topology.RealSpace,
				set_basic.InUniv))
		unsquashed := arg.Have(
			"and so is h·k unsquashed, h·k/(1 − |h·k|)",
			"continuous_map(T, real_topology, λx:A. h(x) * k(x) / (&1 - |h(x) * k(x)|))",
			By(topology, productContinuous, marginContinuous, small, At(ContinuousRealDiv, T, product, margin)))
		agrees := arg.Have(
			"on s, k is 1 and h the squashed f, so h·k unsquashed is f",
			"∀x:A. x ∈ s ⇒ h(x) * k(x) / (&1 - |h(x) * k(x)|) = f(x)",
			Derive(func(d *Argument) {
				x := d.FixAs[A]("x")
				xIn := d.Assume()
				d.Show(
					"unsquashing undoes the squashing at f(x)",
					ByArith(hParts[2].At(x), kParts[3].At(x), unsquash.At(f.Apply(x)), xIn))
			}))
		arg.Take(arg.TermAs[Fun[A, Real]]("λx:A. h(x) * k(x) / (&1 - |h(x) * k(x)|)"))
		arg.Show(
			"h·k unsquashed is a continuous extension of f",
			By(unsquashed, agrees))
	}),
})}
