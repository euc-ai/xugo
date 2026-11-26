// uniform.go — uniformly continuous and Lipschitz maps between metric
// spaces. A Lipschitz map is uniformly continuous and a uniformly
// continuous map is continuous; uniformly continuous maps compose and
// carry Cauchy sequences to Cauchy sequences, which is what lets one
// defined on a dense subset extend to the whole space when the target is
// complete.

package complete_metric

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Uniform continuity
// ---------------------------------------------------------------------------

// UniformlyContinuousMapsInto — a uniformly continuous map carries M into N.
var UniformlyContinuousMapsInto = uniformlyContinuousMapsIntoThm{family.Add(registry.ProofEntry{
	Name: "UniformlyContinuousMapsInto",
	Key:  "prop_27526082e588f096",
	Build: UniformlyContinuousMap.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ M",
		},
		Conclusion: "f(x) ∈ N",
	}),
})}

// UniformlyContinuousDelta — one δ serves every point of M for each ε.
var UniformlyContinuousDelta = uniformlyContinuousDeltaThm{family.Add(registry.ProofEntry{
	Name: "UniformlyContinuousDelta",
	Key:  "prop_ecd05fa9c6a0ba5",
	Build: UniformlyContinuousMap.Axiom(Statement{
		Binders: "∀ε:real.",
		Hypotheses: []string{
			"&0 < ε",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ (∀x y:A. x ∈ M ∧ y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < ε)",
	}),
})}

// LipschitzMapsInto — a Lipschitz map carries M into N.
var LipschitzMapsInto = lipschitzMapsIntoThm{family.Add(registry.ProofEntry{
	Name: "LipschitzMapsInto",
	Key:  "prop_379fb4321fa0a2d6",
	Build: LipschitzMap.Axiom(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ M",
		},
		Conclusion: "f(x) ∈ N",
	}),
})}

// LipschitzBound — a Lipschitz map stretches no distance by more than some
// fixed factor.
var LipschitzBound = lipschitzBoundThm{family.Add(registry.ProofEntry{
	Name:  "LipschitzBound",
	Key:   "prop_f9ff1f6912e6075d",
	Build: LipschitzMap.Axiom("∃k:real. ∀x y:A. x ∈ M ∧ y ∈ M ⇒ e(f(x), f(y)) ≤ k * d(x, y)"),
})}

// LipschitzImpUniformlyContinuous — a Lipschitz map is uniformly
// continuous.
//
// If f stretches no distance by more than a factor k, then δ = ε/(|k| + 1)
// serves every ε at once: a distance is never negative, so k times it is
// at most |k| times it, and two points within δ of each other have values
// within |k|·δ < ε of each other.
var LipschitzImpUniformlyContinuous = lipschitzImpUniformlyContinuousThm{family.Add(registry.ProofEntry{
	Name: "LipschitzImpUniformlyContinuous",
	Key:  "prop_418671a05d4c7959",
	Reading: "Only the source is asked to be a metric space: nothing " +
		"is needed of e, and the Lipschitz factor may be negative or zero.",
	Build: LipschitzMap.Law(Statement{
		Hypotheses: []string{
			"metric_space(M, d)",
		},
		Conclusion: "uniformly_continuous_map(M, d, N, e, f)",
	},
		func(
			a *Argument,
			lipschitz LipschitzMapFact[on.M, on.N],
			metric metric_space.MetricSpaceFact[on.M],
		) {
			k, bound := a.UnpackAs[Real](LipschitzBound.Read(lipschitz), "k")
			widen := a.Have(
				"|k| + 1 is positive",
				"&0 < |k| + &1",
				ByArith())

			a.Do(Unfold(UniformlyContinuousMap))
			a.Do(SplitConj(
				Case(
					"f carries M into N",
					By(LipschitzMapsInto.Read(lipschitz))),
				Case(
					"δ = ε/(|k| + 1) serves every ε",
					Derive(func(b *Argument) {
						b.FixAs[Real]()
						pos := b.Assume()
						b.Take(b.TermAs[Real]("ε / (|k| + &1)"))
						b.Do(SplitConj(
							Case(
								"ε/(|k| + 1) is positive",
								ByArith(pos, widen)),
							Case(
								"two points of M within ε/(|k| + 1) of each other have values within ε",
								Derive(func(c *Argument) {
									x := c.FixAs[A]()
									y := c.FixAs[A]()
									near := c.Conjuncts(
										c.Assume(),
										"x is a point of M",
										"y is a point of M",
										"x and y are within ε/(|k| + 1) of each other")
									xm := c.MemberOf[on.M](x, near[0])
									ym := c.MemberOf[on.M](y, near[1])
									c.Show(
										"e(f(x), f(y)) ≤ k·d(x, y) ≤ |k|·d(x, y), and d(x, y)·(|k| + 1) < ε",
										ByArith(
											bound.At(x, y),
											xm,
											ym,
											near[2],
											widen,
											metric_space.DistNonneg.Read(metric).At(xm, ym),
											real_sgn_abs.AbsDominates.At(k)))
								})),
						))
					})),
			))
		}),
})}

// UniformlyContinuousImpContinuous — a uniformly continuous map is
// continuous.
//
// Continuity for the metric topologies is continuity in the ε-δ sense
// (metric_space.ContinuousMapIff), where δ may depend on the point; the δ
// that uniform continuity hands over for ε serves every point of M at
// once, so in particular each one.
var UniformlyContinuousImpContinuous = uniformlyContinuousImpContinuousThm{family.Add(registry.ProofEntry{
	Name: "UniformlyContinuousImpContinuous",
	Key:  "prop_ecf8f53f20454c10",
	Build: UniformlyContinuousMap.Law(Statement{
		Hypotheses: []string{
			"metric_space(N, e)",
		},
		Conclusion: "continuous_map(metric_topology(M, d), metric_topology(N, e), f)",
	},
		func(
			a *Argument,
			uniform UniformlyContinuousMapFact[on.M, on.N],
			target metric_space.MetricSpaceFact[on.N],
		) {
			// Continuity read in the ε-δ sense.
			a.Do(Simp(Fwd(metric_space.ContinuousMapIff)))
			a.Do(SplitConj(
				Case(
					"f carries M into N",
					By(UniformlyContinuousMapsInto.Read(uniform))),
				Case(
					"at each point of M the δ that serves ε everywhere serves it there",
					Derive(func(b *Argument) {
						b.FixAs[A]()
						eps := b.FixAs[Real]()
						given := b.Conjuncts(
							b.Assume(),
							"x is a point of M",
							"ε is positive")
						δ, everywhere := b.ObtainAs[Real](
							"uniform continuity hands over a δ for ε that serves every pair of points of M",
							"∃δ:real. &0 < δ ∧ ∀x y:A. x ∈ M ∧ y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < ε",
							By(UniformlyContinuousDelta.Read(uniform).At(eps), given[1]))
						b.Take(δ)
						b.Show(
							"so it serves the pairs with x as one point",
							By(everywhere, given[0]))
					})),
			))
		}),
})}

// UniformlyContinuousCompose — uniformly continuous maps compose.
//
// Given ε, the uniform continuity of g hands over an η: points of N within
// η of each other have values within ε. That of f hands over a δ for η:
// points of M within δ of each other have values within η. So two points
// of M within δ of each other are carried by f to points of N within η,
// and by g ∘ f to points of L within ε.
var UniformlyContinuousCompose = uniformlyContinuousComposeThm{family.Add(registry.ProofEntry{
	Name: "UniformlyContinuousCompose",
	Key:  "prop_18f4cc10934ca55f",
	Build: UniformlyContinuousMap.Law(Statement{
		Binders: "∀L:set(C). ∀h:(C → C → real). ∀g:(B → C).",
		Hypotheses: []string{
			"uniformly_continuous_map(N, e, L, h, g)",
		},
		Conclusion: "uniformly_continuous_map(M, d, L, h, g ∘ f)",
	},
		func(
			a *Argument,
			inner UniformlyContinuousMapFact[on.M, on.N],
			L *Expr[Set[C]],
			h *Arrow2[C, C, Real],
			g *Arrow[B, C],
			outer UniformlyContinuousMapFact[on.N, on.L],
		) {
			// Uniform continuity of g ∘ f read as its sentence; `o` is the
			// constant behind `∘`: unfolded, the value at x is g(f(x)).
			a.Do(Simp(Fwd(UniformlyContinuousMap)), Unfold(functions.ComposeApply))
			a.Do(SplitConj(
				Case(
					"g ∘ f carries M into L, f carrying M into N and g carrying N into L",
					By(UniformlyContinuousMapsInto.Read(inner), UniformlyContinuousMapsInto.Read(outer))),
				Case(
					"the δ that f hands over for the η that g hands over for ε serves g ∘ f at ε",
					Derive(func(b *Argument) {
						eps := b.FixAs[Real]()
						pos := b.Assume()
						η, forG := b.ObtainAs[Real](
							"g hands over an η for ε: points of N within η of each other have values within ε",
							"∃η:real. &0 < η ∧ ∀u v:B. u ∈ N ∧ v ∈ N ∧ e(u, v) < η ⇒ h(g(u), g(v)) < ε",
							By(UniformlyContinuousDelta.Read(outer).At(eps), pos))
						nearG := b.Conjuncts(
							forG,
							"η is positive",
							"points of N within η of each other have values under g within ε")
						δ, forF := b.ObtainAs[Real](
							"f hands over a δ for η: points of M within δ of each other have values within η",
							"∃δ:real. &0 < δ ∧ ∀x y:A. x ∈ M ∧ y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < η",
							By(UniformlyContinuousDelta.Read(inner).At(η), nearG[0]))
						nearF := b.Conjuncts(
							forF,
							"δ is positive",
							"points of M within δ of each other have values under f within η")
						b.Take(δ)
						b.Do(SplitConj(
							Case(
								"δ is positive",
								By(nearF[0])),
							Case(
								"two points of M within δ of each other have values under g ∘ f within ε",
								Derive(func(c *Argument) {
									x := c.FixAs[A]()
									y := c.FixAs[A]()
									near := c.Conjuncts(
										c.Assume(),
										"x is a point of M",
										"y is a point of M",
										"x and y are within δ of each other")
									xm := c.MemberOf[on.M](x, near[0])
									ym := c.MemberOf[on.M](y, near[1])
									fx := c.MemberOf[on.N](c.TermAs[B]("f(x)"), UniformlyContinuousMapsInto.Read(inner).At(xm))
									fy := c.MemberOf[on.N](c.TermAs[B]("f(y)"), UniformlyContinuousMapsInto.Read(inner).At(ym))
									c.Show(
										"f(x) and f(y) are points of N within η of each other, so their values under g are within ε",
										By(nearG[1].At(fx, fy), fx, fy, nearF[1].At(xm, ym), xm, ym, near[2]))
								})),
						))
					})),
			))
		}),
})}

// UniformlyContinuousCauchy — a uniformly continuous map carries Cauchy
// sequences to Cauchy sequences.
//
// Given ε, uniform continuity hands over a δ that serves every pair of
// points of M at once, and the Cauchy sequence an index K past which any
// two of its terms are within δ of each other. Past K any two values are
// then within ε of each other.
var UniformlyContinuousCauchy = uniformlyContinuousCauchyThm{family.Add(registry.ProofEntry{
	Name: "UniformlyContinuousCauchy",
	Key:  "prop_e14065b2f009534",
	Build: UniformlyContinuousMap.Law(Statement{
		Binders: "∀x:(num → A).",
		Hypotheses: []string{
			"metric_cauchy(M, d, x)",
		},
		Conclusion: "metric_cauchy(N, e, f ∘ x)",
	},
		func(a *Argument, uniform UniformlyContinuousMapFact[on.M, on.N], x *Arrow[Nat, A], cauchy Fact) {
			together := a.Conjuncts(
				a.Unfolded(cauchy, MetricCauchyDef),
				"every term is a point of M",
				"every positive distance holds any two terms past some index")

			a.Do(Unfold(MetricCauchyDef), Unfold(functions.ComposeApply))
			a.Do(SplitConj(
				Case(
					"every value f(x(n)) is a point of N",
					By(together[0], UniformlyContinuousMapsInto.Read(uniform))),
				Case(
					"past the index for the δ that serves ε any two values are within ε of each other",
					Derive(func(b *Argument) {
						eps := b.FixAs[Real]()
						pos := b.Assume()
						δ, serves := b.ObtainAs[Real](
							"uniform continuity hands over a δ for ε that serves every pair of points of M",
							"∃δ:real. &0 < δ ∧ ∀u v:A. u ∈ M ∧ v ∈ M ∧ d(u, v) < δ ⇒ e(f(u), f(v)) < ε",
							By(UniformlyContinuousDelta.Read(uniform).At(eps), pos))
						near := b.Conjuncts(
							serves,
							"δ is positive",
							"points of M within δ of each other have values within ε")
						K, pairs := b.ObtainAs[Nat](
							"x being Cauchy, past some index K any two terms are within δ of each other",
							"∃K:num. ∀m n:num. K ≤ m ∧ K ≤ n ⇒ d(x(m), x(n)) < δ",
							By(together[1].At(δ), near[0]))
						b.Take(K)
						m := b.FixAs[Nat]()
						n := b.FixAs[Nat]()
						past := b.Assume()
						xm := b.MemberOf[on.M](x.Apply(m), together[0].At(m))
						xn := b.MemberOf[on.M](x.Apply(n), together[0].At(n))
						b.Show(
							"x(m) and x(n) are points of M within δ of each other, so their values are within ε",
							By(near[1].At(xm, xn), xm, xn, pairs.At(m, n), past))
					})),
			))
		}),
})}

// UniformlyContinuousSameLimit — two sequences of s converging to one point
// of M have images under a uniformly continuous map on s converging to one
// limit.
//
// Were the limits l and m of the images distinct, they would lie a
// positive distance e(l, m) apart. Uniform continuity hands over a δ for
// a third of it. Past some index both sequences lie within δ/2 of their
// common limit p, so within δ of each other, and their images within a
// third of e(l, m) of each other; past some index the images lie within
// a third of e(l, m) of l and of m. At an index past all four, the detour
// from l to m through the two images is shorter than e(l, m).
var UniformlyContinuousSameLimit = uniformlyContinuousSameLimitThm{family.Add(registry.ProofEntry{
	Name: "UniformlyContinuousSameLimit",
	Key:  "prop_8c1b9a4906cd4e39",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). " +
			"∀d:(A → A → real). " +
			"∀N:set(B). " +
			"∀e:(B → B → real). " +
			"∀s:set(A). " +
			"∀f:(A → B). " +
			"∀x y:(num → A). " +
			"∀p:A. " +
			"∀l m:B.",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_space(N, e)",
			"uniformly_continuous_map(s, d, N, e, f)",
			"∀n:num. x(n) ∈ s ∧ y(n) ∈ s",
			"metric_converges_to(M, d, x, p)",
			"metric_converges_to(M, d, y, p)",
			"metric_converges_to(N, e, f ∘ x, l)",
			"metric_converges_to(N, e, f ∘ y, m)",
		},
		Conclusion: "l = m",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			source metric_space.MetricSpaceFact[on.M],
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			target metric_space.MetricSpaceFact[on.N],
			s *Expr[Set[A]],
			f *Arrow[A, B],
			uniform Fact,
			x, y *Arrow[Nat, A],
			inS Fact,
			p *Expr[A],
			xToP, yToP Fact,
			l, m *Expr[B],
			xImages, yImages Fact,
		) {
			nearX := a.Conjuncts(
				a.Unfolded(xToP, MetricConvergesToDef),
				"p is a point of M",
				"every term of x is a point of M",
				"every positive distance about p holds a tail of x")
			nearY := a.Conjuncts(
				a.Unfolded(yToP, MetricConvergesToDef),
				"p is a point of M",
				"every term of y is a point of M",
				"every positive distance about p holds a tail of y")
			imagesX := a.Conjuncts(
				a.Unfolded(a.Unfolded(xImages, MetricConvergesToDef), functions.ComposeApply),
				"l is a point of N",
				"every image f(x(n)) is a point of N",
				"every positive distance about l holds a tail of the images f(x(n))")
			imagesY := a.Conjuncts(
				a.Unfolded(a.Unfolded(yImages, MetricConvergesToDef), functions.ComposeApply),
				"m is a point of N",
				"every image f(y(n)) is a point of N",
				"every positive distance about m holds a tail of the images f(y(n))")
			pM := a.MemberOf[on.M](p, nearX[0])
			lN := a.MemberOf[on.N](l, imagesX[0])
			mN := a.MemberOf[on.N](m, imagesY[0])

			distinct := a.SupposeNot()
			apart := a.Have(
				"two distinct points of N lie a positive distance apart",
				"&0 < e(l, m)",
				ByArith(
					distinct,
					metric_space.DistZeroIff.Read(target).At(lN, mN),
					metric_space.DistNonneg.Read(target).At(lN, mN)))
			third := a.TermAs[Real]("e(l, m) / &3")
			_, serves := a.ObtainAs[Real](
				"uniform continuity hands over a δ for a third of e(l, m) that serves every pair of points of s",
				"∃δ:real. &0 < δ ∧ ∀u v:A. u ∈ s ∧ v ∈ s ∧ d(u, v) < δ ⇒ e(f(u), f(v)) < e(l, m) / &3",
				ByArith(apart, UniformlyContinuousDelta.Read(uniform).At(third)))
			near := a.Conjuncts(
				serves,
				"δ is positive",
				"points of s within δ of each other have images within a third of e(l, m)")
			half := a.TermAs[Real]("δ / &2")
			_, tailX := a.ObtainAs[Nat](
				"past some index K₀ the terms of x lie within δ/2 of p",
				"∃K:num. ∀n:num. K ≤ n ⇒ d(x(n), p) < δ / &2",
				ByArith(nearX[2].At(half), near[0]),
				Named("K₀"))
			_, tailY := a.ObtainAs[Nat](
				"past some index K₁ the terms of y do",
				"∃K:num. ∀n:num. K ≤ n ⇒ d(y(n), p) < δ / &2",
				ByArith(nearY[2].At(half), near[0]),
				Named("K₁"))
			_, tailFX := a.ObtainAs[Nat](
				"past some index K₂ the images f(x(n)) lie within a third of e(l, m) of l",
				"∃K:num. ∀n:num. K ≤ n ⇒ e(f(x(n)), l) < e(l, m) / &3",
				ByArith(imagesX[2].At(third), apart),
				Named("K₂"))
			_, tailFY := a.ObtainAs[Nat](
				"past some index K₃ the images f(y(n)) lie within a third of e(l, m) of m",
				"∃K:num. ∀n:num. K ≤ n ⇒ e(f(y(n)), m) < e(l, m) / &3",
				ByArith(imagesY[2].At(third), apart),
				Named("K₃"))
			n := a.TermAs[Nat]("K₀ + K₁ + K₂ + K₃")
			xn := a.MemberOf[on.M](x.Apply(n), nearX[1].At(n))
			yn := a.MemberOf[on.M](y.Apply(n), nearY[1].At(n))
			fxn := a.MemberOf[on.N](f.Apply(x.Apply(n)), imagesX[1].At(n))
			fyn := a.MemberOf[on.N](f.Apply(y.Apply(n)), imagesY[1].At(n))
			together := a.Have(
				"x(n) and y(n), both within δ/2 of p, lie within δ of each other",
				"d(x(K₀ + K₁ + K₂ + K₃), y(K₀ + K₁ + K₂ + K₃)) < δ",
				ByArith(
					tailX.At(n),
					tailY.At(n),
					metric_space.DistTriangle.Read(source).At(xn, pM, yn),
					metric_space.DistSym.Read(source).At(pM, yn)))
			a.Show(
				"so their images lie within a third of e(l, m) of each other, "+
					"and the detour from l to m through them is shorter than e(l, m)",
				ByArith(
					tailFX.At(n),
					tailFY.At(n),
					inS.At(n),
					together,
					near[1].At(x.Apply(n), y.Apply(n)),
					metric_space.DistTriangle.Read(target).At(lN, fxn, mN),
					metric_space.DistTriangle.Read(target).At(fxn, fyn, mN),
					metric_space.DistSym.Read(target).At(lN, fxn)))
		}),
})}

// UniformContinuousExtension — a uniformly continuous map from a dense
// subset into a complete space extends to the whole space.
//
// Every point p of M is the limit of a sequence of s (ClosureIffSequential).
// Such a sequence is Cauchy, so are its images (UniformlyContinuousCauchy),
// and N being complete they converge. Let g(p) be the limit of the images
// along a sequence of s converging to p, one chosen: along every such
// sequence the images converge to g(p), two sequences to p giving their
// images one limit (UniformlyContinuousSameLimit). Along a constant
// sequence the images are constant, so g is f on s. For ε > 0 the δ of f
// at ε/3 serves g at ε: for points p and q of M within δ of each other,
// sequences of s converging to them have terms within δ of each other
// from some index on, so images within ε/3, and at an index where the
// images are also within ε/3 of g(p) and of g(q), the detour from g(p) to
// g(q) through them is shorter than ε.
var UniformContinuousExtension = uniformContinuousExtensionThm{family.Add(registry.ProofEntry{
	Name: "UniformContinuousExtension",
	Key:  "prop_ca2ffdec22aa032f",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real). ∀s:set(A). ∀f:(A → B).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_space(N, e)",
			"metric_complete(N, e)",
			"s ⊆ M",
			"closure(metric_topology(M, d), s) = M",
			"uniformly_continuous_map(s, d, N, e, f)",
		},
		Conclusion: "∃g:(A → B). uniformly_continuous_map(M, d, N, e, g) ∧ (∀x:A. x ∈ s ⇒ g(x) = f(x))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			source metric_space.MetricSpaceFact[on.M],
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			target metric_space.MetricSpaceFact[on.N],
			complete Fact,
			s *Expr[Set[A]],
			within, dense Fact,
			f *Arrow[A, B],
			uniform Fact,
		) {
			approach := a.Have(
				"every point of M, lying in the closure of s, is the limit of a sequence of points of s",
				"∀p:A. p ∈ M ⇒ ∃z:(num → A). (∀n:num. z(n) ∈ s) ∧ metric_converges_to(M, d, z, p)",
				a.ForEach(func(p *Expr[A]) Action {
					return By(dense, within, ClosureIffSequential.Read(source).At(s, p))
				}))
			converge := a.Have(
				"the images of a sequence of s converging in M converge in N",
				Statement{
					Binders: "∀z:(num → A). ∀p:A.",
					Hypotheses: []string{
						"∀n:num. z(n) ∈ s",
						"metric_converges_to(M, d, z, p)",
					},
					Conclusion: "∃l:B. metric_converges_to(N, e, f ∘ z, l)",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Fun[Nat, A]]()
					p := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"every term is a point of s",
						"z converges to p in M")
					cauchy := b.Conjuncts(
						b.Unfolded(GroupPremises(source, given[1], ConvergentImpCauchy.At(M, d, z, p)), MetricCauchyDef),
						"every term is a point of M",
						"every positive distance holds any two terms past some index")
					cauchyS := b.Have(
						"so z is a Cauchy sequence of s, the distance being the same",
						"metric_cauchy(s, d, z)",
						By(given[0], cauchy[1], MetricCauchyDef))
					b.Show(
						"its images are Cauchy, f being uniformly continuous, and N is complete",
						By(complete, cauchyS, UniformlyContinuousCauchy.Read(uniform).At(z), MetricCompleteDef))
				}))

			// g(p) is the limit of the images f ∘ z along a sequence z of s
			// converging to p, one such sequence and limit chosen.
			g, gDef := a.LetAs[Fun[A, B]](
				"g",
				"λp:A. εl:B. ∃z:(num → A). "+
					"    (∀n:num. z(n) ∈ s) ∧ metric_converges_to(M, d, z, p) ∧ metric_converges_to(N, e, f ∘ z, l)")
			limit := a.Have(
				"along every sequence of s converging to p the images converge to g(p)",
				Statement{
					Binders: "∀z:(num → A). ∀p:A.",
					Hypotheses: []string{
						"∀n:num. z(n) ∈ s",
						"metric_converges_to(M, d, z, p)",
					},
					Conclusion: "metric_converges_to(N, e, f ∘ z, g(p))",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Fun[Nat, A]]()
					p := b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"every term is a point of s",
						"z converges to p in M")
					l, toL := b.ObtainAs[B](
						"the images along z converge to some l",
						"∃l:B. metric_converges_to(N, e, f ∘ z, l)",
						By(given[0], given[1], converge.At(z, p)))
					w, chosen := b.ObtainAs[Fun[Nat, A]](
						"so the chosen g(p) is the limit of the images along some sequence w of s converging to p",
						"∃w:(num → A). "+
							"    (∀n:num. w(n) ∈ s) ∧ metric_converges_to(M, d, w, p) ∧ metric_converges_to(N, e, f ∘ w, g(p))",
						gDef.Rw(),
						By(given[0], given[1], toL))
					along := b.Conjuncts(
						chosen,
						"every term of w is a point of s",
						"w converges to p in M",
						"the images along w converge to g(p)")
					same := b.Have(
						"l is g(p): z and w are sequences of s converging to p",
						"l = g(p)",
						By(
							source,
							target,
							uniform,
							given[0],
							along[0],
							given[1],
							along[1],
							toL,
							along[2],
							UniformlyContinuousSameLimit.At(M, d, N, e, s, f, z, w, p, l, b.TermAs[B]("g(p)"))))
					b.Show(
						"so the images along z converge to g(p)",
						By(Normalized, toL, same))
				}))

			a.Take(g)
			a.Do(SplitConj(
				Case(
					"g is uniformly continuous",
					UniformlyContinuousMap.Intro(
						Case(
							"g carries M into N, g(x) being the limit of images in N",
							Derive(func(b *Argument) {
								x := b.FixAs[A]()
								inM := b.Assume()
								z, toX := b.UnpackAs[Fun[Nat, A]](GroupPremises(inM, approach.At(x)), "z")
								sequence := b.Conjuncts(
									toX,
									"every term of z is a point of s",
									"z converges to x")
								b.Show(
									"the images along z converge to g(x), so g(x) is a point of N",
									By(b.Unfolded(GroupPremises(sequence[0], sequence[1], limit.At(z, x)), MetricConvergesToDef)))
							})),
						Case(
							"the δ of f at ε/3 serves g at ε",
							Derive(func(b *Argument) {
								b.FixAs[Real]()
								positive := b.Assume()
								third := b.TermAs[Real]("ε / &3")
								δ, serves := b.ObtainAs[Real](
									"f hands over a δ for ε/3 that serves every pair of points of s",
									"∃δ:real. &0 < δ ∧ ∀u v:A. u ∈ s ∧ v ∈ s ∧ d(u, v) < δ ⇒ e(f(u), f(v)) < ε / &3",
									ByArith(positive, UniformlyContinuousDelta.Read(uniform).At(third)))
								near := b.Conjuncts(
									serves,
									"δ is positive",
									"points of s within δ of each other have images within ε/3 of each other")
								b.Take(δ)
								b.Do(SplitConj(
									Case(
										"δ is positive",
										By(near[0])),
									Case(
										"two points of M within δ of each other have values under g within ε of each other",
										Derive(func(c *Argument) {
											p := c.FixAs[A]("p")
											q := c.FixAs[A]("q")
											points := c.Conjuncts(
												c.Assume(),
												"p is a point of M",
												"q is a point of M",
												"p and q lie within δ of each other")
											z, toP := c.UnpackAs[Fun[Nat, A]](GroupPremises(points[0], approach.At(p)), "z")
											w, toQ := c.UnpackAs[Fun[Nat, A]](GroupPremises(points[1], approach.At(q)), "w")
											alongZ := c.Conjuncts(
												toP,
												"every term of z is a point of s",
												"z converges to p")
											alongW := c.Conjuncts(
												toQ,
												"every term of w is a point of s",
												"w converges to q")
											nearP := c.Conjuncts(
												c.Unfolded(alongZ[1], MetricConvergesToDef),
												"p is a point of M",
												"every term of z is a point of M",
												"every positive distance about p holds a tail of z")
											nearQ := c.Conjuncts(
												c.Unfolded(alongW[1], MetricConvergesToDef),
												"q is a point of M",
												"every term of w is a point of M",
												"every positive distance about q holds a tail of w")
											valueP := c.Conjuncts(
												c.Unfolded(
													c.Unfolded(GroupPremises(alongZ[0], alongZ[1], limit.At(z, p)), MetricConvergesToDef),
													functions.ComposeApply),
												"g(p) is a point of N",
												"every image f(z(n)) is a point of N",
												"every positive distance about g(p) holds a tail of the images f(z(n))")
											valueQ := c.Conjuncts(
												c.Unfolded(
													c.Unfolded(GroupPremises(alongW[0], alongW[1], limit.At(w, q)), MetricConvergesToDef),
													functions.ComposeApply),
												"g(q) is a point of N",
												"every image f(w(n)) is a point of N",
												"every positive distance about g(q) holds a tail of the images f(w(n))")
											room := c.TermAs[Real]("(δ - d(p, q)) / &2")
											_, tailZ := c.ObtainAs[Nat](
												"past some index K₀ the terms of z lie within (δ − d(p, q))/2 of p",
												"∃K:num. ∀n:num. K ≤ n ⇒ d(z(n), p) < (δ - d(p, q)) / &2",
												ByArith(nearP[2].At(room), points[2]),
												Named("K₀"))
											_, tailW := c.ObtainAs[Nat](
												"past some index K₁ the terms of w lie within (δ − d(p, q))/2 of q",
												"∃K:num. ∀n:num. K ≤ n ⇒ d(w(n), q) < (δ - d(p, q)) / &2",
												ByArith(nearQ[2].At(room), points[2]),
												Named("K₁"))
											_, tailFZ := c.ObtainAs[Nat](
												"past some index K₂ the images f(z(n)) lie within ε/3 of g(p)",
												"∃K:num. ∀n:num. K ≤ n ⇒ e(f(z(n)), g(p)) < ε / &3",
												ByArith(valueP[2].At(third), positive),
												Named("K₂"))
											_, tailFW := c.ObtainAs[Nat](
												"past some index K₃ the images f(w(n)) lie within ε/3 of g(q)",
												"∃K:num. ∀n:num. K ≤ n ⇒ e(f(w(n)), g(q)) < ε / &3",
												ByArith(valueQ[2].At(third), positive),
												Named("K₃"))
											n := c.TermAs[Nat]("K₀ + K₁ + K₂ + K₃")
											pM := c.MemberOf[on.M](p, points[0])
											qM := c.MemberOf[on.M](q, points[1])
											zn := c.MemberOf[on.M](c.TermAs[A]("z(K₀ + K₁ + K₂ + K₃)"), nearP[1].At(n))
											wn := c.MemberOf[on.M](c.TermAs[A]("w(K₀ + K₁ + K₂ + K₃)"), nearQ[1].At(n))
											gp := c.MemberOf[on.N](c.TermAs[B]("g(p)"), valueP[0])
											gq := c.MemberOf[on.N](c.TermAs[B]("g(q)"), valueQ[0])
											fzn := c.MemberOf[on.N](c.TermAs[B]("f(z(K₀ + K₁ + K₂ + K₃))"), valueP[1].At(n))
											fwn := c.MemberOf[on.N](c.TermAs[B]("f(w(K₀ + K₁ + K₂ + K₃))"), valueQ[1].At(n))
											together := c.Have(
												"z(n) and w(n) lie within δ of each other, by the detour through p and q",
												"d(z(K₀ + K₁ + K₂ + K₃), w(K₀ + K₁ + K₂ + K₃)) < δ",
												ByArith(
													tailZ.At(n),
													tailW.At(n),
													points[2],
													metric_space.DistTriangle.Read(source).At(zn, pM, wn),
													metric_space.DistTriangle.Read(source).At(pM, qM, wn),
													metric_space.DistSym.Read(source).At(qM, wn)))
											c.Show(
												"so their images lie within ε/3 of each other, and the "+
													"detour from g(p) to g(q) through them is shorter than ε",
												ByArith(
													tailFZ.At(n),
													tailFW.At(n),
													alongZ[0].At(n),
													alongW[0].At(n),
													together,
													near[1].At(zn, wn),
													metric_space.DistTriangle.Read(target).At(gp, fzn, gq),
													metric_space.DistTriangle.Read(target).At(fzn, fwn, gq),
													metric_space.DistSym.Read(target).At(gp, fzn)))
										})),
								))
							})),
					)),
				Case(
					"g is f on s: along a constant sequence the images are constant",
					Derive(func(b *Argument) {
						x := b.FixAs[A]()
						inS := b.Assume()
						xM := b.MemberOf[on.M](x, b.Have(
							"x is a point of M, s lying in M",
							"x ∈ M",
							BySets(inS, within)))
						// s has no carrier phantom: the fact on s is read at on.Any, and x is a member there.
						fx := b.MemberOf[on.N](
							f.Apply(x), UniformlyContinuousMapsInto.Read(uniform).At(b.MemberOf[on.Any](x, inS)))
						constant := b.TermAs[Fun[Nat, A]]("λn:num. x")
						still := b.Have(
							"the constant sequence x, x, … converges to x in M",
							"metric_converges_to(M, d, λn:num. x, x)",
							Unfold(MetricConvergesToDef),
							By(Normalized, xM, metric_space.DistSelf.Read(source).At(xM)))
						stillImages := b.Have(
							"its images, all f(x), converge to f(x) in N",
							"metric_converges_to(N, e, f ∘ (λn:num. x), f(x))",
							Unfold(MetricConvergesToDef),
							Unfold(functions.ComposeApply),
							By(Normalized, fx, metric_space.DistSelf.Read(target).At(fx)))
						b.Show(
							"they converge to g(x) as well, and a limit is unique",
							By(
								target,
								inS,
								still,
								limit.At(constant, x),
								stillImages,
								LimitUnique.At(N, e, b.TermAs[Fun[Nat, B]]("f ∘ (λn:num. x)"), b.TermAs[B]("g(x)"), f.Apply(x))))
					})),
			))
		}),
})}
