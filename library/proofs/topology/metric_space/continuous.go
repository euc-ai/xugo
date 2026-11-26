// continuous.go — continuity between the topologies of two distances:
// the preimage of every open set open, read as the ε-δ condition.

package metric_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousMapIff — continuity for the metric topologies is continuity
// in the ε-δ sense. The spaces of the two topologies are M and N, so the
// clause that f carries the one into the other is common to both sides.
// If preimages of open sets are open, the preimage of the ball of radius
// ε about f(x) is open and holds x, so some ball about x lies inside it,
// and its radius serves as δ. Conversely, a point x of the preimage of an
// open set v has f(x) in v, so some ball about f(x) lies in v; the ε-δ
// condition at its radius gives a δ, and the ball of radius δ about x lies
// in the preimage. Of the two distances only the target's is asked
// anything: that its balls are open and hold their centres.
var ContinuousMapIff = continuousMapIffThm{family.Add(registry.ProofEntry{
	Name: "ContinuousMapIff",
	Key:  "prop_ff0494738e724feb",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real). ∀f:(A → B).",
		Hypotheses: []string{
			"metric_space(N, e)",
		},
		Conclusion: "continuous_map(metric_topology(M, d), metric_topology(N, e), f) ⇔ " +
			"(∀x:A. x ∈ M ⇒ f(x) ∈ N) ∧ " +
			"(∀x:A. ∀ε:real. " +
			"    x ∈ M ∧ &0 < ε ⇒ ∃δ:real. &0 < δ ∧ (∀y:A. y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < ε))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			f *Arrow[A, B],
			target MetricSpaceFact[on.N],
		) {
			// Continuity: f carries the space of the first topology into
			// the space of the second, and pulls open sets back to open
			// sets. The two spaces are M and N — the law read once at each
			// space's point type, a Simp rule being pinned at a letter other
			// than its own.
			a.Do(Unfold(continuous.ContinuousMap), Simp(
				Fwd(MetricTopologySpace),
				Fwd(MetricTopologySpace.Inst[B]())))
			a.Iff()

			a.Forward(
				"the δ at x for ε is the radius of a ball about x "+
					"inside the preimage of the ball of radius ε about f(x)",
				func(b *Argument, continuous Fact) {
					clauses := b.Conjuncts(
						continuous,
						"f carries M into N",
						"the preimage of an open set of N is open")
					b.Do(SplitConj(
						Case(
							"f carries M into N",
							By(clauses[0])),
						Case(
							"at a point x of M and a radius ε > 0 there is a δ",
							Derive(func(c *Argument) {
								x := c.FixAs[A]("x")
								eps := c.FixAs[Real]("ε")
								point := c.Conjuncts(
									c.Assume(),
									"x lies in M",
									"ε is positive")
								fx := f.Apply(x)
								image := c.Have(
									"f(x) lies in N",
									"f(x) ∈ N",
									By(clauses[0].At(x), point[0]))
								fxN := c.MemberOf[on.N](fx, image)
								centre := c.Have(
									"f(x) lies in the ball of radius ε about itself",
									"f(x) ∈ ball(N, e, f(x), ε)",
									By(CentreInBall.Read(target).At(fxN, eps), point[1]))
								ballOpen := c.Have(
									"the ball of radius ε about f(x) is open",
									"ball(N, e, f(x), ε) ∈ metric_topology(N, e)",
									By(BallOpen.Read(target).At(fxN, eps)))
								preimage := c.Let("U", c.Term("preimage_on(M, f, ball(N, e, f(x), ε))"))
								open := c.Conjuncts(
									c.Have(
										"so its preimage U is open: each point of U has a ball about it inside U",
										"U ⊆ M ∧ ∀z:A. z ∈ U ⇒ ∃r:real. &0 < r ∧ ball(M, d, z, r) ⊆ U",
										Simp(Rev(OpenIff)),
										preimage.Rw(),
										By(clauses[1], ballOpen)),
									"U lies in M",
									"each point of U has a ball about it inside U")
								holds := c.Have(
									"U holds x, as f(x) lies in the ball",
									"x ∈ U",
									BySets(preimage, point[0], centre))
								delta, radius := c.ObtainAs[Real](
									"so a ball about x of some radius δ lies in U",
									"∃δ:real. &0 < δ ∧ ball(M, d, x, δ) ⊆ U",
									By(open[1].At(x), holds))
								about := c.Conjuncts(
									radius,
									"δ is positive",
									"the ball of radius δ about x lies in U")
								within := c.Unfolded(about[1], BallDef)
								sent := c.Have(
									"and f sends each point of U within ε of f(x)",
									"∀y:A. y ∈ U ⇒ e(f(x), f(y)) < ε",
									preimage.Rw(),
									Unfold(BallDef),
									BySets())
								c.Take(delta)
								c.Do(SplitConj(
									Case(
										"δ is positive",
										By(about[0])),
									Case(
										"a point of M within δ of x lies in U, so f sends it within ε of f(x)",
										BySets(within, sent)),
								))
							})),
					))
				})

			a.Backward(
				"a point x of the preimage of an open set v has a ball about f(x) inside "+
					"v, and the δ for its radius gives a ball about x inside the preimage",
				func(b *Argument, epsilonDelta Fact) {
					clauses := b.Conjuncts(
						epsilonDelta,
						"f carries M into N",
						"f is continuous at every point of M")
					b.Do(SplitConj(
						Case(
							"f carries M into N",
							By(clauses[0])),
						Case(
							"the preimage of an open set v of N is open",
							Derive(func(c *Argument) {
								c.FixAs[Set[B]]("v")
								vOpen := c.Assume()
								// The preimage is open when each of its points has a
								// ball about it inside the preimage.
								c.Do(Simp(Fwd(OpenIff)))
								c.Do(SplitConj(
									Case(
										"the preimage lies in M",
										BySets()),
									Case(
										"a point x of the preimage has a ball about it inside the preimage",
										Derive(func(g *Argument) {
											x := g.FixAs[A]("x")
											inPreimage := g.Assume()
											at := g.Conjuncts(
												g.Have(
													"x lies in M and f(x) in v",
													"x ∈ M ∧ f(x) ∈ v",
													BySets(inPreimage)),
												"x lies in M",
												"f(x) lies in v")
											eps, ballInV := g.ObtainAs[Real](
												"v is open, so a ball about f(x) of some radius ε lies in v",
												"∃ε:real. &0 < ε ∧ ball(N, e, f(x), ε) ⊆ v",
												By(vOpen, at[1], OpenIff))
											aboutEps := g.Conjuncts(
												ballInV,
												"ε is positive",
												"the ball of radius ε about f(x) lies in v")
											delta, near := g.ObtainAs[Real](
												"continuity at x gives a δ for this ε",
												"∃δ:real. &0 < δ ∧ ∀y:A. y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < ε",
												By(clauses[1].At(x, eps), at[0], aboutEps[0]))
											aboutDelta := g.Conjuncts(
												near,
												"δ is positive",
												"a point of M within δ of x is sent within ε of f(x)")
											inV := g.Unfolded(aboutEps[1], BallDef)
											g.Take(delta)
											g.Do(SplitConj(
												Case(
													"δ is positive",
													By(aboutDelta[0])),
												Case(
													"a point y of the ball of radius δ about x has f(y) in N within ε of f(x), hence in v",
													Unfold(BallDef),
													BySets(clauses[0], aboutDelta[1], inV)),
											))
										})),
								))
							})),
					))
				})
		}),
})}
