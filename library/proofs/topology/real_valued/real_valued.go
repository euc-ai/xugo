// real_valued.go — continuous real functions on a space, combined: a
// jointly continuous function of two reals carries two continuous real
// functions to a continuous one, so their sum and their product are
// continuous, and by induction so is a finite sum; the negative of one is
// its product with −1. The distance from a fixed point of a metric space
// is continuous. What composing with a continuous function of the line
// gives — the absolute value — is continuous.Compose after
// real_continuous's laws. On a nonempty compact set such a function
// attains a least value and a greatest one.

package real_valued

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Combining continuous real functions
// ---------------------------------------------------------------------------

// ContinuousRealJoint — a function of two reals, jointly continuous,
// carries two continuous real functions to a continuous one. Every real
// is a point of the line, so what is asked is that the preimage of an
// open u is open, which the pointwise criterion reads at a point x of
// it: an interval of radius ε about the value at x lies in u, joint
// continuity gives a radius δ for ε at (f(x), g(x)), and the preimages
// under f and g of the intervals of radius δ about f(x) and g(x) meet in
// an open set about x inside the preimage.
var ContinuousRealJoint = continuousRealJointThm{family.Add(registry.ProofEntry{
	Name: "ContinuousRealJoint",
	Key:  "prop_1649d24f310906fb",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f g:(A → real). ∀F:(real → real → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, real_topology, f)",
			"continuous_map(T, real_topology, g)",
			"∀a b ε:real. " +
				"    &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀c d:real. |c - a| < δ ∧ |d - b| < δ ⇒ |F(c, d) - F(a, b)| < ε",
		},
		Conclusion: "continuous_map(T, real_topology, λx:A. F(f(x), g(x)))",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		f, g *Arrow[A, Real],
		F *Arrow2[Real, Real, Real],
		topology, fContinuous, gContinuous, joint Fact,
	) {
		a.Do(Simp(Fwd(continuous.ContinuousMap)))
		a.Do(SplitConj(
			Case(
				"every real is a point of the line",
				By(real_topology.RealSpace, set_basic.InUniv)),
			Case(
				"the preimage of an open u is open, by the pointwise criterion",
				Derive(func(b *Argument) {
					u := b.FixAs[Set[Real]]("u")
					uOpen := b.Assume()
					b.Do(Simp(Fwd(topological_space.OpenPointwise)))
					x := b.FixAs[A]("x")
					position := b.Have(
						"x is a point of the space whose value lies in u",
						"x ∈ ⋃T ∧ F(f(x), g(x)) ∈ u",
						BySets(b.Assume()))
					ε, interval := b.ObtainAs[Real](
						"the interval of some radius ε about that value lies in u",
						"∃ε:real. &0 < ε ∧ ∀y:real. |y - F(f(x), g(x))| < ε ⇒ y ∈ u",
						By(uOpen, position, real_topology.OpenIff.At(u)))
					parts := b.Conjuncts(
						interval,
						"ε is positive",
						"what lies within ε of the value lies in u")
					εPositive, insideU := parts[0], parts[1]
					δ, radius := b.ObtainAs[Real](
						"joint continuity at (f(x), g(x)) gives a radius δ for ε",
						"∃δ:real. &0 < δ ∧ ∀c d:real. |c - f(x)| < δ ∧ |d - g(x)| < δ ⇒ |F(c, d) - F(f(x), g(x))| < ε",
						By(joint.At(f.Apply(x), g.Apply(x), ε), εPositive))
					clauses := b.Conjuncts(
						radius,
						"δ is positive",
						"arguments within δ of f(x) and g(x) keep F within ε of the value")
					δPositive, keepsF := clauses[0], clauses[1]
					_, UEq := b.LetAs[Set[A]]("U", "preimage_on(⋃T, f, {y:real | |y - f(x)| < δ})")
					_, VEq := b.LetAs[Set[A]]("V", "preimage_on(⋃T, g, {y:real | |y - g(x)| < δ})")
					UInT := b.Have(
						"U is open, the preimage under f of an interval about f(x)",
						"U ∈ T",
						UEq.Rw(),
						By(continuous.PreimageOpen.Read(fContinuous), real_topology.BallOpen.At(f.Apply(x), δ)))
					VInT := b.Have(
						"V is open, the preimage under g of an interval about g(x)",
						"V ∈ T",
						VEq.Rw(),
						By(continuous.PreimageOpen.Read(gContinuous), real_topology.BallOpen.At(g.Apply(x), δ)))
					atCentre := b.Have(
						"x lies within δ of its own values",
						"|f(x) - f(x)| < δ ∧ |g(x) - g(x)| < δ",
						ByArith(δPositive))
					b.Take(b.TermAs[Set[A]]("U ∩ V"))
					b.Do(SplitConjAll(
						Case(
							"the meet of U and V is open",
							By(topological_space.InterOpen.Read(topology), UInT, VInT)),
						Case(
							"a point y of the meet has its value within ε of the value at x, hence in u",
							Simp(Fwd(set_basic.SubsetDef)),
							Derive(func(c *Argument) {
								y := c.FixAs[A]("y")
								near := c.Have(
									"y is a point of the space with f(y) and g(y) within δ of f(x) and g(x)",
									"y ∈ ⋃T ∧ |f(y) - f(x)| < δ ∧ |g(y) - g(x)| < δ",
									BySets(UEq, VEq, c.Assume()))
								value := c.Have(
									"so the value at y is within ε of the value at x, and lies in u",
									"F(f(y), g(y)) ∈ u",
									By(insideU.At(F.Apply(f.Apply(y), g.Apply(y))), keepsF.At(f.Apply(y), g.Apply(y)), near))
								c.Show(
									"which puts y in the preimage",
									BySets(value, near))
							})),
						Case(
							"and x lies in the meet",
							BySets(UEq, VEq, atCentre, position))))
				}))))
	}),
})}

// ContinuousRealAdd — the sum of two continuous real functions is
// continuous: addition is jointly continuous, since moving each term by
// less than ε/2 moves the sum by less than ε.
var ContinuousRealAdd = continuousRealAddThm{family.Add(registry.ProofEntry{
	Name: "ContinuousRealAdd",
	Key:  "prop_48f21bf73b873814",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f g:(A → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, real_topology, f)",
			"continuous_map(T, real_topology, g)",
		},
		Conclusion: "continuous_map(T, real_topology, λx:A. f(x) + g(x))",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f, g *Arrow[A, Real], h Fact) {
		estimate := a.Have(
			"moving each term by less than ε/2 moves the sum by less than ε",
			Statement{
				Binders: "∀a b ε:real.",
				Hypotheses: []string{
					"&0 < ε",
				},
				Conclusion: "∃δ:real. &0 < δ ∧ (∀c d:real. |c - a| < δ ∧ |d - b| < δ ⇒ |c + d - (a + b)| < ε)",
			},
			Derive(func(arg *Argument) {
				arg.FixAs[Real]("a")
				arg.FixAs[Real]("b")
				arg.FixAs[Real]("ε")
				positive := arg.Assume()
				arg.Take(arg.TermAs[Real]("ε / &2"))
				arg.Show(
					"half of ε serves, by the triangle inequality",
					ByArith(positive))
			}))
		a.Show(
			"the sum is addition carried along f and g",
			By(h, estimate, ContinuousRealJoint.At(T, f, g, a.TermAs[Op[Real]]("λa:real. λb:real. a + b"))))
	}),
})}

// ContinuousRealMul — the product of two continuous real functions is
// continuous: multiplication is jointly continuous. About a and b, with
// M = |a| + |b| + 1, the radius δ = ε / (ε + M) is at most 1 and has
// δ·M < ε, and for c within δ of a and d within δ of b the difference of
// the products splits as (c − a)·d + a·(d − b), of size at most
// δ·(|b| + 1) + |a|·δ = δ·M.
var ContinuousRealMul = continuousRealMulThm{family.Add(registry.ProofEntry{
	Name: "ContinuousRealMul",
	Key:  "prop_1f0af980a9562425",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f g:(A → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, real_topology, f)",
			"continuous_map(T, real_topology, g)",
		},
		Conclusion: "continuous_map(T, real_topology, λx:A. f(x) * g(x))",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f, g *Arrow[A, Real], h Fact) {
		estimate := a.Have(
			"moving each factor by less than a radius read off "+
				"the two factors moves the product by less than ε",
			Statement{
				Binders: "∀a b ε:real.",
				Hypotheses: []string{
					"&0 < ε",
				},
				Conclusion: "∃δ:real. &0 < δ ∧ (∀c d:real. |c - a| < δ ∧ |d - b| < δ ⇒ |c * d - a * b| < ε)",
			},
			Derive(func(arg *Argument) {
				arg.FixAs[Real]("a")
				arg.FixAs[Real]("b")
				arg.FixAs[Real]("ε")
				positive := arg.Assume()
				_, MEq := arg.LetAs[Real]("M", "|a| + |b| + &1")
				large := arg.Have(
					"M is at least 1",
					"&1 ≤ M",
					ByArith(MEq))
				δ, δEq := arg.LetAs[Real]("δ", "ε / (ε + M)")
				radius := arg.Have(
					"δ is positive and at most 1, and δ·M < δ·(ε + M) = ε",
					"&0 < δ ∧ δ ≤ &1 ∧ δ * M < ε",
					ByArith(δEq, large, positive))
				arg.Take(δ)
				arg.Do(SplitConj(
					Case(
						"the radius δ is positive",
						By(radius)),
					Case(
						"and within it the products differ by at most δ·M",
						Derive(func(inner *Argument) {
							inner.FixAs[Real]("c")
							inner.FixAs[Real]("d")
							near := inner.Assume()
							bounded := inner.Have(
								"d stays within 1 of b, δ being at most 1",
								"|d| ≤ |b| + &1",
								ByArith(near, radius))
							firstTerm := inner.Have(
								"the first term: |c − a| is below δ and |d| at most |b| + 1",
								"|c - a| * |d| ≤ δ * (|b| + &1)",
								ByArith(
									near,
									bounded,
									radius,
									real_sgn_abs.AbsNonneg.At(inner.TermAs[Real]("c - a")),
									real_sgn_abs.AbsNonneg.At(inner.TermAs[Real]("d"))))
							secondTerm := inner.Have(
								"the second term: |d − b| is below δ",
								"|a| * |d - b| ≤ |a| * δ",
								ByArith(near, real_sgn_abs.AbsNonneg.At(inner.TermAs[Real]("a"))))
							chain := inner.CalcLeibniz(real_order_ring.OrderCalc(
								inner.Ctx()), inner.TermAs[Real]("|c * d - a * b|"),
								LeLeg(
									inner.TermAs[Real]("|(c - a) * d| + |a * (d - b)|"),
									"c·d − a·b = (c − a)·d + a·(d − b), and the triangle inequality",
									ByArith()),
								EqLeg(
									inner.TermAs[Real]("|c - a| * |d| + |a| * |d - b|"),
									"the absolute value of a product is the product of the absolute values",
									ByArith()),
								LeLeg(
									inner.TermAs[Real]("δ * (|b| + &1) + |a| * δ"),
									"the two bounds add",
									ByArith(firstTerm, secondTerm)),
								EqLeg(
									inner.TermAs[Real]("δ * M"),
									"and δ·(|b| + 1) + |a|·δ is δ·M",
									ByArith(Scaled(δ, MEq))))
							inner.Show(
								"which is below ε",
								ByArith(chain, radius))
						}))))
			}))
		a.Show(
			"the product is multiplication carried along f and g",
			By(h, estimate, ContinuousRealJoint.At(T, f, g, a.TermAs[Op[Real]]("λa:real. λb:real. a * b"))))
	}),
})}

// ContinuousRealSum — a finite sum of continuous real functions on a
// space is continuous. By induction on the number of terms: the sum of
// none is the constant 0, and the sum of one more term is a continuous
// partial sum plus a continuous summand.
var ContinuousRealSum = continuousRealSumThm{family.Add(registry.ProofEntry{
	Name: "ContinuousRealSum",
	Key:  "prop_7b4264dc2750b413",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀F:(num → A → real). ∀k:num.",
		Hypotheses: []string{
			"is_topology(T)",
			"∀j:num. j < k ⇒ continuous_map(T, real_topology, F(j))",
		},
		Conclusion: "continuous_map(T, real_topology, λx:A. Σ_{j<k} F(j, x))",
	}, func(a *Argument, T *Expr[Set[Set[A]]], F *Arrow2[Nat, A, Real], topology Fact) {
		a.Induct("k")
		a.Base(
			"the sum of no terms is the constant 0",
			Simp(Fwd(real_sum.BelowClauses)),
			By(
				topology,
				continuous.Constant.At(T, a.TermAs[Set[Set[Real]]]("real_topology"), a.TermAs[Real]("&0")),
				real_topology.RealSpace,
				set_basic.InUniv))
		a.Step(
			"one more term adds a continuous summand to the continuous partial sum",
			func(b *Argument, partial Fact) {
				terms := b.Assume()
				b.Show(
					"the sum below suc(k) is the sum below k plus the k-th term",
					Simp(Fwd(real_sum.BelowClauses)),
					By(
						partial,
						terms,
						topology,
						nat_order.LessThanSucClause,
						ContinuousRealAdd.At(
							T,
							b.TermAs[Fun[A, Real]]("λx:A. Σ_{j<k} F(j, x)"),
							b.TermAs[Fun[A, Real]]("F(k)"))))
			})
	}),
})}

// ContinuousRealNeg — the negative of a continuous real function is
// continuous: it is the function's product with the constant −1.
var ContinuousRealNeg = continuousRealNegThm{family.Add(registry.ProofEntry{
	Name: "ContinuousRealNeg",
	Key:  "prop_877bce1b624a8561",
	Build: family.Theorem(Statement{
		Binders:    "∀T:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{"is_topology(T)", "continuous_map(T, real_topology, f)"},
		Conclusion: "continuous_map(T, real_topology, λx:A. -f(x))",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f *Arrow[A, Real], h Fact) {
		constant := a.Have(
			"minus one is a constant continuous map",
			"continuous_map(T, real_topology, λx:A. -&1)",
			By(h, continuous.Constant, real_topology.RealSpace, set_basic.InUniv))
		negative := a.Have(
			"multiplication by minus one preserves continuity",
			"continuous_map(T, real_topology, λx:A. -&1 * f(x))",
			By(h, constant, ContinuousRealMul))
		a.Do(negative.Simp(Fwd(real_ring.NegMinusOne)))
		a.Show(
			"multiplication by minus one is negation",
			By(negative))
	}),
})}

// MetricDistanceContinuous — the distance from a fixed point a of a metric
// space is continuous. The line's topology is the topology of its own
// distance, so continuity is the ε-δ property between two metric spaces,
// and δ = ε serves: by the triangle inequality both ways, the distances
// from a to x and to y differ by at most d(x, y). It lives here because
// the metric chapter sits below the line's topology.
var MetricDistanceContinuous = metricDistanceContinuousThm{family.Add(registry.ProofEntry{
	Name: "MetricDistanceContinuous",
	Key:  "prop_e8e4077b8d8683b9",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀a:A.",
		Hypotheses: []string{
			"metric_space(M, d)",
			"a ∈ M",
		},
		Conclusion: "continuous_map(metric_topology(M, d), real_topology, λx:A. d(a, x))",
	}, func(
		arg *Argument,
		M *Expr[Set[A]],
		d *Arrow2[A, A, Real],
		a *Expr[A],
		metric metric_space.MetricSpaceFact[on.M],
		aIn Fact,
	) {
		aM := arg.MemberOf[on.M](a, aIn)
		// The line's topology read as the topology of its distance, and
		// continuity between two metric spaces read as ε-δ.
		arg.Do(
			Simp(Fwd(real_topology.RealTopologyMetric)),
			Simp(Fwd(real_topology.RealMetric), Fwd(metric_space.ContinuousMapIff)))
		arg.Do(SplitConj(
			Case(
				"every distance is a real",
				By(set_basic.InUniv)),
			Case(
				"at every point x of M, δ = ε serves",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					ε := b.FixAs[Real]("ε")
					given := b.Conjuncts(
						b.Assume(),
						"x is a point of M",
						"and ε is positive")
					xM := b.MemberOf[on.M](x, given[0])
					b.Take(ε)
					b.Do(SplitConj(
						Case(
							"ε is positive",
							By(given[1])),
						Case(
							"a point y of M within ε of x has its distance from a within ε of x's",
							Derive(func(c *Argument) {
								y := c.FixAs[A]("y")
								near := c.Conjuncts(
									c.Assume(),
									"y is a point of M",
									"within ε of x")
								yM := c.MemberOf[on.M](y, near[0])
								c.Do(Unfold(real_sgn_abs.RealDistDef))
								c.Show(
									"by the triangle inequality both ways, the two distances from a differ by at most d(x, y)",
									ByArith(
										metric_space.DistTriangle.Read(metric).At(aM, xM, yM),
										metric_space.DistTriangle.Read(metric).At(aM, yM, xM),
										metric_space.DistSym.Read(metric).At(xM, yM),
										near[1]))
							}))))
				}))))
	}),
})}

// ---------------------------------------------------------------------------
// The extreme value argument
// ---------------------------------------------------------------------------

// ContinuousCompactMinimum — a continuous real function attains a least
// value on a nonempty compact set: its values there form a compact,
// nonempty set of reals, which holds its infimum.
var ContinuousCompactMinimum = continuousCompactMinimumThm{family.Add(registry.ProofEntry{
	Name: "ContinuousCompactMinimum",
	Key:  "prop_61ae0361e09c3b2c",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f:(A → real). ∀K:set(A).",
		Hypotheses: []string{
			"continuous_map(T, real_topology, f)",
			"compact_in(T, K)",
			"K ≠ ∅",
		},
		Conclusion: "∃u:A. u ∈ K ∧ (∀v:A. v ∈ K ⇒ f(u) ≤ f(v))",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f *Arrow[A, Real], K *Expr[Set[A]], h Fact) {
		compactRange := a.Have(
			"the values of f on K form a compact real set",
			"compact_in(real_topology, image(f, K))",
			By(h, continuous.ImageCompact.At(T, a.TermAs[Set[Set[Real]]]("real_topology"), f, K)))
		nonempty := a.Have(
			"K holding a point, the value range is nonempty",
			"image(f, K) ≠ ∅",
			BySets(h))
		least := a.Have(
			"the infimum belongs to the value range and bounds it below",
			"inf(image(f, K)) ∈ image(f, K) ∧ (∀q:real. q ∈ image(f, K) ⇒ inf(image(f, K)) ≤ q)",
			By(nonempty, compactRange, real_topology.InfCompactAttained.At(a.TermAs[Set[Real]]("image(f, K)"))))
		u, attained := a.ObtainAs[A](
			"choose a point attaining that infimum",
			"∃u:A. u ∈ K ∧ f(u) = inf(image(f, K))",
			By(least, set_basic.InImage.At(f, K, a.TermAs[Real]("inf(image(f, K))"))),
			Named("u"))
		a.Take(u)
		a.Show(
			"the attaining point is a least point of K",
			SplitConj(
				Case(
					"it lies in K",
					By(attained)),
				Case(
					"every other point of K has at least the infimum as its value",
					Derive(func(b *Argument) {
						b.FixAs[A]("v")
						inK := b.Assume()
						inRange := b.Have(
							"the value at the other point belongs to the range",
							"f(v) ∈ image(f, K)",
							BySets(inK))
						b.Show(
							"the attaining value is the range infimum",
							By(inRange, attained, least))
					}))))
	}),
})}

// ContinuousCompactMaximum — a continuous real function attains a
// greatest value on a nonempty compact set: its values there form a
// compact, nonempty set of reals, which holds its supremum.
var ContinuousCompactMaximum = continuousCompactMaximumThm{family.Add(registry.ProofEntry{
	Name: "ContinuousCompactMaximum",
	Key:  "prop_902ad49f4557efe1",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f:(A → real). ∀K:set(A).",
		Hypotheses: []string{
			"continuous_map(T, real_topology, f)",
			"compact_in(T, K)",
			"K ≠ ∅",
		},
		Conclusion: "∃u:A. u ∈ K ∧ (∀v:A. v ∈ K ⇒ f(v) ≤ f(u))",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f *Arrow[A, Real], K *Expr[Set[A]], h Fact) {
		compactRange := a.Have(
			"the values of f on K form a compact real set",
			"compact_in(real_topology, image(f, K))",
			By(h, continuous.ImageCompact.At(T, a.TermAs[Set[Set[Real]]]("real_topology"), f, K)))
		nonempty := a.Have(
			"K holding a point, the value range is nonempty",
			"image(f, K) ≠ ∅",
			BySets(h))
		greatest := a.Have(
			"the supremum belongs to the value range and bounds it above",
			"sup(image(f, K)) ∈ image(f, K) ∧ (∀q:real. q ∈ image(f, K) ⇒ q ≤ sup(image(f, K)))",
			By(nonempty, compactRange, real_topology.SupCompactAttained.At(a.TermAs[Set[Real]]("image(f, K)"))))
		u, attained := a.ObtainAs[A](
			"choose a point attaining that supremum",
			"∃u:A. u ∈ K ∧ f(u) = sup(image(f, K))",
			By(greatest, set_basic.InImage.At(f, K, a.TermAs[Real]("sup(image(f, K))"))),
			Named("u"))
		a.Take(u)
		a.Show(
			"the attaining point is a greatest point of K",
			SplitConj(
				Case(
					"it lies in K",
					By(attained)),
				Case(
					"every other point of K has at most the supremum as its value",
					Derive(func(b *Argument) {
						b.FixAs[A]("v")
						inK := b.Assume()
						inRange := b.Have(
							"the value at the other point belongs to the range",
							"f(v) ∈ image(f, K)",
							BySets(inK))
						b.Show(
							"the attaining value is the range supremum",
							By(inRange, attained, greatest))
					}))))
	}),
})}
