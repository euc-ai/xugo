// open_sets.go — continuity read by open sets: a function continuous on s
// is exactly a continuous map from the subspace s to the line, on the whole
// line a continuous map of the line, and a real polynomial function is a
// continuous map of the line.

package real_continuous

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Two readings of continuity
// ---------------------------------------------------------------------------

// ContinuousOnIffMap — a real function is continuous on s exactly when
// it is a continuous map from the subspace s to the line.
//
// The points of the subspace are the points of the line in s, which are
// the points of s, and its open sets are the traces u ∩ s of the open
// sets u of the line.
//
// Continuity on s gives a continuous map. Every value lies in the line.
// For an open set v, the points of s that f sends into v are the trace
// on s of u, the union of the balls about points c of s on which the
// points of s all land in v. A union of balls is open: each ball is open
// (BallOpen), and a union of open sets is open. A point of u in s lies in
// one of these balls, so f sends it into v. Conversely, at a point y of
// the preimage, v gives f(y) a radius ε inside v, continuity at y
// answers ε with a radius δ, and y lies in u by its own ball of radius δ.
// The trace of the open set u is open in the subspace (TraceOpen).
//
// A continuous map is continuous on s. At a point c of s and a positive
// ε, the ball of radius ε about f(c) is open, so its preimage is open in
// the subspace: the trace u ∩ s of an open set u (OpenInSubtopology).
// The point c lies in it, so u gives c a radius δ inside u, and a point
// of s within δ of c lies in the trace, where f is within ε of f(c).
var ContinuousOnIffMap = continuousOnIffMapThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnIffMap",
	Key:  "prop_aa993a637f739284",
	Build: family.Sections(Statement{
		Binders:    "∀f:(real → real). ∀s:set(real).",
		Conclusion: "real_continuous_on(s, f) ⇔ continuous_map(subtopology(s), real_topology, f)",
		Abbrev: Abbrev{
			{Name: "balls", Text: "{b:set(real) | ∃c r:real. P(c, r) ∧ b = {y:real | |y - c| < r}}"},
			{Name: "unionOfBalls", Text: "{y:real | " +
				"    ∃c r:real. c ∈ s ∧ &0 < r ∧ (∀z:real. z ∈ s ∧ |z - c| < r ⇒ f(z) ∈ v) ∧ |y - c| " +
				"    < r}"},
			{Name: "preimage", Text: "preimage_on(⋃subtopology(s), f, {y:real | |y - f(c)| < ε})"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A union of balls is open, whichever balls it gathers: the
			// balls of radius r about c for the pairs (c, r) with P(c, r).
			// Each ball is open, and a union of open sets is open.
			ballsOpen := ctx.Lemma("∀P:real → real → bool. "+
				"    {y:real | ∃c r:real. P(c, r) ∧ |y - c| < r} ∈ real_topology",
				func(a *Argument, P *Arrow2[Real, Real, Bool]) {
					eachOpen := a.Have(
						"each ball gathered is open",
						"∀b:set(real). (∃c r:real. P(c, r) ∧ b = {y:real | |y - c| < r}) ⇒ b ∈ real_topology",
						Derive(func(b *Argument) {
							b.FixAs[Set[Real]]("b")
							// b is the ball of radius r about some c with P(c, r).
							c, r, gathered := b.Unpack2As[Real, Real](b.Assume(), "c", "r")
							ball := b.Conjuncts(
								gathered,
								"P holds at c and r",
								"b is the ball of radius r about c")
							b.Show(
								"a ball is open",
								ball[1].Rw(),
								By(real_topology.BallOpen.At(c, r)))
						}))
					a.Have(
						"so the balls form a subfamily of the open sets",
						"«balls» ⊆ real_topology",
						BySets(eachOpen))
					a.Have(
						"and their union is open, by the union axiom",
						"⋃«balls» ∈ real_topology",
						Cite(
							topological_space.UnionsOpen.Read(real_topology.RealTopology), a.TermAs[Set[Set[Real]]]("«balls»")))
					union := a.Have(
						"a point lies in their union exactly when it lies within r of c for some pair (c, r) with P(c, r)",
						"⋃«balls» = {y:real | ∃c r:real. P(c, r) ∧ |y - c| < r}",
						BySets())
					a.Show(
						"so the union of balls is open",
						union.RwRev(),
						Assumption())
				})

			return ctx.Theorem(headline, func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]]) {
				line := a.TermAs[Set[Set[Real]]]("real_topology")
				points := a.Have(
					"the points of the subspace are the points of the line in s, that is the points of s",
					"⋃subtopology(s) = s",
					// SubtopologySpace pinned at the reals: Go's Simp does not adapt a
					// rule's type letter.
					Simp(Fwd(topological_space.SubtopologySpace.Inst[Real]()), Fwd(real_topology.RealSpace)),
					BySets())
				a.Iff()

				a.Forward(
					"continuity on s gives a continuous map: the preimage "+
						"of an open set is the trace of a union of balls",
					func(b *Argument, fContinuous Fact) {
						near := b.Unfolded(fContinuous, RealContinuousOnDef)
						// The map's two clauses, read at the points of s: `points`
						// rewrites the subspace's points ⋃subtopology(s) to s.
						b.Do(Unfold(continuous.ContinuousMap), points.Rw(), SplitConj(
							Case(
								"f carries s into the line, whose points are all the reals",
								BySets(real_topology.RealSpace)),
							Case(
								"and the points of s that f sends into an open set v form the trace of an open set",
								Derive(func(d *Argument) {
									d.FixAs[Set[Real]]("v")
									vOpen := d.Assume()
									vBalls := d.Have(
										"v is open: each of its points has a radius inside v",
										"∀x:real. x ∈ v ⇒ ∃ε:real. &0 < ε ∧ (∀w:real. |w - x| < ε ⇒ w ∈ v)",
										Simp(Rev(real_topology.OpenIff)),
										By(vOpen))

									// The balls of u: the ball of radius r about c is one of
									// them when c is a point of s, r is positive, and the
									// points of s within r of c all land in v.
									const ballOfU = "c ∈ s ∧ &0 < r ∧ (∀z:real. z ∈ s ∧ |z - c| < r ⇒ f(z) ∈ v)"
									u := d.TermAs[Set[Real]]("«unionOfBalls»")
									uOpen := d.Have(
										"u is a union of balls, so it is open",
										"«unionOfBalls» ∈ real_topology",
										Cite(
											ballsOpen,
											d.TermAs[Fun2[Real, Real, Bool]](
												"λc:real. λr:real. c ∈ s ∧ &0 < r ∧ (∀z:real. z ∈ s ∧ |z - c| < r ⇒ f(z) ∈ v)")))

									inside := d.Have(
										"a point y of s that f sends into v lies in one of the balls of u",
										Statement{
											Binders: "∀y:real.",
											Hypotheses: []string{
												"y ∈ s",
												"f(y) ∈ v",
											},
											Conclusion: "∃c r:real. c ∈ s ∧ &0 < r ∧ (∀z:real. z ∈ s ∧ |z - c| < r ⇒ f(z) ∈ v) ∧ |y - c| < r",
										},
										Derive(func(e *Argument) {
											y := e.FixAs[Real]("y")
											inPreimage := e.Conjuncts(
												e.Assume(),
												"y lies in s",
												"and f sends it into v")
											eps, vRadius := e.ObtainAs[Real](
												"v, being open, gives f(y) a radius ε inside v",
												"∃ε:real. &0 < ε ∧ ∀w:real. |w - f(y)| < ε ⇒ w ∈ v",
												By(vBalls.At(f.Apply(y)), inPreimage[1]))
											aboutV := e.Conjuncts(
												vRadius,
												"ε is positive",
												"the reals within ε of f(y) lie in v")
											delta, yRadius := e.ObtainAs[Real](
												"continuity at y answers ε with a radius δ",
												"∃δ:real. &0 < δ ∧ ∀z:real. z ∈ s ∧ |z - y| < δ ⇒ |f(z) - f(y)| < ε",
												By(near.At(y, eps), inPreimage[0], aboutV[0]))
											aboutY := e.Conjuncts(
												yRadius,
												"δ is positive",
												"the points of s within δ of y land within ε of f(y)")
											nearYIntoV := e.Have(
												"so the points of s within δ of y land in v",
												"∀z:real. z ∈ s ∧ |z - y| < δ ⇒ f(z) ∈ v",
												By(aboutY[1], aboutV[1]))
											atCentre := e.Have(
												"and y lies within δ of itself",
												"|y - y| < δ",
												ByArith(aboutY[0]))
											e.Take(y)
											e.Take(delta)
											e.Show(
												"the ball of radius δ about y is one of u's, and it holds y",
												By(inPreimage[0], aboutY[0], nearYIntoV, atCentre))
										}))
									trace := d.Have(
										"a point of u in s lies in a ball whose points of "+
											"s land in v, so the preimage of v is the trace of u",
										"preimage_on(s, f, v) = «unionOfBalls» ∩ s",
										BySets(inside))
									d.Have(
										"and the trace of the open set u is open in the subspace",
										"«unionOfBalls» ∩ s ∈ subtopology(s)",
										By(topological_space.TraceOpen.At(line, s, u), uOpen))
									d.Show(
										"hence the preimage of v is open in the subspace",
										trace.Rw(),
										Assumption())
								})),
						))
					})

				a.Backward(
					"a continuous map is continuous on s: the preimage of "+
						"a ball about f(c) is the trace of an open set about c",
					func(b *Argument, continuousMap Fact) {
						b.Do(Unfold(RealContinuousOnDef))
						clauses := b.Conjuncts(
							b.Unfolded(continuousMap, continuous.ContinuousMap),
							"f carries the subspace into the line",
							"and the preimage of an open set is open in the subspace")
						c := b.FixAs[Real]()
						cIn := b.Assume()
						eps := b.FixAs[Real]()
						positive := b.Assume()

						// The points of the subspace that f sends within ε of f(c).
						const preimage = "preimage_on(⋃subtopology(s), f, {y:real | |y - f(c)| < ε})"
						ball := b.TermAs[Set[Real]]("{y:real | |y - f(c)| < ε}")
						preimageOpen := b.Have(
							"the ball of radius ε about f(c) is open, so its preimage is open in the subspace",
							"«preimage» ∈ subtopology(s)",
							By(clauses[1].At(ball), real_topology.BallOpen.At(f.Apply(c), eps)))
						_, isTrace := b.ObtainAs[Set[Real]](
							"so the preimage is the trace u ∩ s of an open set u",
							"∃u:set(real). «preimage» = u ∩ s ∧ u ∈ real_topology",
							// OpenInSubtopology pinned at the reals: Go's Simp does not
							// adapt a rule's type letter.
							Simp(Rev(topological_space.OpenInSubtopology.Inst[Real]())),
							By(preimageOpen))
						trace := b.Conjuncts(
							isTrace,
							"the preimage is the trace of u",
							"u is open")
						atCentre := b.Have(
							"f(c) lies within ε of itself",
							"|f(c) - f(c)| < ε",
							ByArith(positive))
						cInSpace := b.Have(
							"c is a point of the subspace",
							"c ∈ ⋃subtopology(s)",
							By(Normalized, points, cIn))
						cInU := b.Have(
							"so c lies in the preimage, hence in u",
							"c ∈ u",
							BySets(trace[0], cInSpace, atCentre))
						uBalls := b.Have(
							"u is open: each of its points has a radius inside u",
							"∀x:real. x ∈ u ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∈ u",
							Simp(Rev(real_topology.OpenIff)),
							By(trace[1]))
						delta, radius := b.ObtainAs[Real](
							"so u gives c a radius δ inside u",
							"∃δ:real. &0 < δ ∧ ∀y:real. |y - c| < δ ⇒ y ∈ u",
							By(uBalls.At(c), cInU))
						b.Take(delta)
						b.Show(
							"a point of s within δ of c lies in u ∩ s, the preimage, so f sends it within ε of f(c)",
							BySets(radius, trace[0]))
					})
			})
		}),
})}

// ContinuousOnUnivIffMap — a real function is continuous on the whole
// line exactly when it is a continuous map of the line to itself:
// ContinuousOnIffMap above at s = 𝕌, where the subspace the whole line
// carries is the line itself, a space being its own subspace.
var ContinuousOnUnivIffMap = continuousOnUnivIffMapThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnUnivIffMap",
	Key:  "prop_6ffa9e39ce0acd",
	Build: family.Theorem("∀f:(real → real). "+
		"    real_continuous_on(𝕌, f) ⇔ continuous_map(real_topology, real_topology, f)",
		func(a *Argument, f *Arrow[Real, Real]) {
			a.Show(
				"the subspace on all the points of the line is the line, so the two readings agree on it",
				By(
					Normalized,
					real_topology.RealSpace,
					topological_space.SubtopologySelf.At(a.TermAs[Set[Set[Real]]]("real_topology")),
					ContinuousOnIffMap.At(f, a.TermAs[Set[Real]]("𝕌"))))
		}),
})}

// ContinuousMapIffPointwise — a real function is a continuous map of the
// line to itself exactly when it is continuous at every point.
//
// The points of the line's space are all the reals, so a map of the line
// to itself carries its points into the space, and continuity as a map
// asks only that the points f sends into an open set form an open set.
//
// A continuous map is continuous at every point. At c and a positive ε,
// the ball of radius ε about f(c) is open, so the points f sends into it
// form an open set. That set holds c, so it gives c a radius δ inside
// it, and f sends every point within δ of c to within ε of f(c).
//
// Continuity at every point gives a continuous map. At a point x that f
// sends into an open set v, v gives f(x) a radius ε inside v, and
// continuity at x answers ε with a radius δ: the points within δ of x
// land within ε of f(x), so in v, and the ball of radius δ about x lies
// among the points f sends into v.
var ContinuousMapIffPointwise = continuousMapIffPointwiseThm{family.Add(registry.ProofEntry{
	Name: "ContinuousMapIffPointwise",
	Key:  "prop_2ef3b7b94e1e709a",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(real → real).",
		Conclusion: "continuous_map(real_topology, real_topology, f) ⇔ ∀c:real. real_continuous_at(f, c)",
		Abbrev: Abbrev{
			{Name: "preimage", Text: "preimage_on(⋃real_topology, f, {w:real | |w - f(c)| < ε})"},
		},
	},
		func(a *Argument, f *Arrow[Real, Real]) {
			a.Iff()

			a.Forward(
				"a continuous map is continuous at every point: the "+
					"preimage of a ball about f(c) is open and holds c",
				func(b *Argument, continuousMap Fact) {
					clauses := b.Conjuncts(
						b.Unfolded(continuousMap, continuous.ContinuousMap),
						"f carries the line into itself",
						"and the preimage of an open set is open")
					c := b.FixAs[Real]()
					b.Do(Unfold(RealContinuousAtDef))
					eps := b.FixAs[Real]()
					positive := b.Assume()

					// The points of the line that f sends within ε of f(c).
					const preimage = "preimage_on(⋃real_topology, f, {w:real | |w - f(c)| < ε})"
					ball := b.TermAs[Set[Real]]("{w:real | |w - f(c)| < ε}")
					preimageOpen := b.Have(
						"the ball of radius ε about f(c) is open, so its preimage is open",
						"«preimage» ∈ real_topology",
						By(clauses[1].At(ball), real_topology.BallOpen.At(f.Apply(c), eps)))
					preimageBalls := b.Have(
						"the preimage is open: each of its points has a radius inside it",
						"∀z:real. z ∈ «preimage» ⇒ ∃δ:real. &0 < δ ∧ (∀y:real. |y - z| < δ ⇒ y ∈ «preimage»)",
						Simp(Rev(real_topology.OpenIff)),
						By(preimageOpen))
					atCentre := b.Have(
						"f(c) lies within ε of itself",
						"|f(c) - f(c)| < ε",
						ByArith(positive))
					cIn := b.Have(
						"so c, a point of the line, lies in the preimage",
						"c ∈ «preimage»",
						BySets(real_topology.RealSpace, atCentre))
					delta, radius := b.ObtainAs[Real](
						"so the preimage gives c a radius δ inside it",
						"∃δ:real. &0 < δ ∧ ∀y:real. |y - c| < δ ⇒ y ∈ «preimage»",
						By(preimageBalls.At(c), cIn))
					held := b.Conjuncts(
						radius,
						"δ is positive",
						"the points within δ of c lie in the preimage")
					b.Take(delta)
					b.Do(SplitConj(
						Case(
							"the radius δ is positive",
							By(held[0])),
						Case(
							"and a point within δ of c is sent within ε of f(c)",
							Derive(func(d *Argument) {
								x := d.FixAs[Real]()
								closeToC := d.Assume()
								inPreimage := d.Have(
									"x lies in the preimage",
									"x ∈ «preimage»",
									By(held[1].At(x), closeToC))
								d.Show(
									"so f sends it within ε of f(c)",
									BySets(inPreimage))
							})),
					))
				})

			a.Backward(
				"continuity at every point gives a continuous map: the "+
					"preimage of an open set holds a ball about each of its points",
				func(b *Argument, pointwise Fact) {
					near := b.Unfolded(pointwise, RealContinuousAtDef)
					// The map's two clauses, the points of the line's space read as all the reals.
					b.Do(Unfold(continuous.ContinuousMap), Simp(Fwd(real_topology.RealSpace)), SplitConj(
						Case(
							"f carries every real to a real",
							BySets()),
						Case(
							"and the points f sends into an open set v form an open set",
							Derive(func(d *Argument) {
								d.FixAs[Set[Real]]()
								vOpen := d.Assume()
								vBalls := d.Have(
									"v is open: each of its points has a radius inside v",
									"∀y:real. y ∈ v ⇒ ∃ε:real. &0 < ε ∧ (∀w:real. |w - y| < ε ⇒ w ∈ v)",
									Simp(Rev(real_topology.OpenIff)),
									By(vOpen))

								// Openness of the preimage read pointwise: each of its points needs a radius.
								d.Do(Simp(Fwd(real_topology.OpenIff)))
								x := d.FixAs[Real]()
								inPreimage := d.Assume()
								fxInV := d.Have(
									"f sends x into v",
									"f(x) ∈ v",
									BySets(inPreimage))
								eps, vRadius := d.ObtainAs[Real](
									"v, being open, gives f(x) a radius ε inside v",
									"∃ε:real. &0 < ε ∧ ∀w:real. |w - f(x)| < ε ⇒ w ∈ v",
									By(vBalls.At(f.Apply(x)), fxInV))
								aboutV := d.Conjuncts(
									vRadius,
									"ε is positive",
									"the reals within ε of f(x) lie in v")
								delta, xRadius := d.ObtainAs[Real](
									"continuity at x answers ε with a radius δ",
									"∃δ:real. &0 < δ ∧ ∀z:real. |z - x| < δ ⇒ |f(z) - f(x)| < ε",
									By(near.At(x, eps), aboutV[0]))
								aboutX := d.Conjuncts(
									xRadius,
									"δ is positive",
									"the points within δ of x land within ε of f(x)")
								d.Take(delta)
								d.Do(SplitConj(
									Case(
										"the radius δ is positive",
										By(aboutX[0])),
									Case(
										"and a point within δ of x lies in the preimage",
										Derive(func(e *Argument) {
											y := e.FixAs[Real]()
											closeToX := e.Assume()
											nearFx := e.Have(
												"f(y) lies within ε of f(x)",
												"|f(y) - f(x)| < ε",
												By(aboutX[1].At(y), closeToX))
											inV := e.Have(
												"so f(y) lies in v",
												"f(y) ∈ v",
												By(aboutV[1].At(f.Apply(y)), nearFx))
											e.Show(
												"so f sends y into v",
												BySets(inV))
										})),
								))
							})),
					))
				})
		}),
})}

// PolynomialFunctionContinuous — a real polynomial function is continuous on the
// real line. Polynomial functions are generated from the identity and the
// constants by sums and products, and each of these is continuous.
var PolynomialFunctionContinuous = polynomialFunctionContinuousThm{family.Add(registry.ProofEntry{
	Name: "PolynomialFunctionContinuous",
	Key:  "prop_58122bab270d30ee",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(real → real).",
		Hypotheses: []string{"polynomial_function(f)"},
		Conclusion: "continuous_map(real_topology, real_topology, f)",
	}, func(a *Argument, f *Arrow[Real, Real], polynomial Fact) {
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		a.Show(
			"induct over the polynomial functions",
			ByInduction(real_polynomial.Induction, polynomial,
				Case(
					"the identity is continuous",
					By(continuous.Identity.At(line), functions.IdentityApply)),
				Case(
					"every constant is continuous",
					a.ForEach(func(c *Expr[Real]) Action {
						return By(
							continuous.Constant.At(line, line, c),
							real_topology.RealTopology,
							real_topology.RealSpace,
							set_basic.InUniv)
					})),
				Case(
					"a sum of continuous maps is continuous",
					By(real_valued.ContinuousRealAdd, real_topology.RealTopology)),
				Case(
					"a product of continuous maps is continuous",
					By(real_valued.ContinuousRealMul, real_topology.RealTopology))))
	}),
})}
