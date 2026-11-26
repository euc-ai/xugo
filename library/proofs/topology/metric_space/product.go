// product.go — products of metric spaces. The distance between two pairs
// is the larger of the distances between their components; a ball of the
// product is then the rectangle of the two balls, and a closed ball the
// rectangle of the two closed balls, so the topology of the product
// distance is the product of the two metric topologies. On a countable
// product of functions the distance, `countable_product_metric(J, d, h)`,
// is the supremum of the coordinate distances, clipped at one and weighted
// by 1/(n + 1) along a sequence h running through the active indices; it
// controls each coordinate uniformly, finitely many coordinates control
// it, and its topology is the product topology.

package metric_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The product metric
// ---------------------------------------------------------------------------

// ProductMetric — the product of two metric spaces is a metric space
// under the larger of the two coordinate distances. Each axiom is read
// coordinatewise, a pair lying in the product exactly when its
// coordinates lie in M and N: the larger of two distances, neither
// negative, vanishes exactly when both do, that is when the pairs agree in
// each coordinate; it is symmetric as each is; and each coordinate's
// detour bound is at most the sum of the two larger distances.
var ProductMetric = productMetricThm{family.Add(registry.ProofEntry{
	Name: "ProductMetric",
	Key:  "prop_fcb7993f1f17864f",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_space(N, e)",
		},
		Conclusion: "metric_space(set_cross(M, N), product_metric(d, e))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			left MetricSpaceFact[on.M],
			right MetricSpaceFact[on.N],
		) {
			// The coordinates of a point of the product are points of M and
			// N only through the product's membership, so the axioms of the
			// two spaces are cited untyped at the coordinates and the
			// closers discharge their memberships by InCrossProjections.
			a.Do(Simp(Fwd(MetricSpace)), SplitConjAll(
				Case(
					"the product distance vanishes exactly between equal pairs",
					Derive(func(b *Argument) {
						p := b.FixAs[Prod[A, B]]("p")
						q := b.FixAs[Prod[A, B]]("q")
						points := b.Assume()
						fp, fq := b.TermAs[A]("fst(p)"), b.TermAs[A]("fst(q)")
						sp, sq := b.TermAs[B]("snd(p)"), b.TermAs[B]("snd(q)")
						b.Iff()
						b.Forward(
							"if the larger distance is zero, so are both, and the pairs agree in each coordinate",
							func(c *Argument, zero Fact) {
								both := c.Have(
									"both coordinate distances are zero, being at most the larger and never negative",
									"d(fst(p), fst(q)) = &0 ∧ e(snd(p), snd(q)) = &0",
									ByArith(
										zero,
										points,
										DistNonneg.Read(left).AsFact().At(fp, fq),
										DistNonneg.Read(right).AsFact().At(sp, sq),
										real_sup_inf.MaxUpperBound.At(
											c.TermAs[Real]("d(fst(p), fst(q))"), c.TermAs[Real]("e(snd(p), snd(q))")),
										set_product.InCrossProjections,
										ProductMetricDef))
								c.Show(
									"so the coordinates agree, and a pair is the pair of its coordinates",
									By(
										both,
										points,
										DistZeroIff.Read(left).AsFact().At(fp, fq),
										DistZeroIff.Read(right).AsFact().At(sp, sq),
										pairs.PairEta.At(p),
										pairs.PairEta.At(q),
										set_product.InCrossProjections))
							})
						b.Backward(
							"a pair is at distance zero from itself in each coordinate",
							func(c *Argument, same Fact) {
								zero := c.TermAs[Real]("&0")
								c.Show(
									"and the larger of two zeros is zero",
									By(
										same,
										points,
										DistSelf.Read(left).AsFact().At(fq),
										DistSelf.Read(right).AsFact().At(sq),
										real_sup_inf.MaxIsArgument.At(zero, zero),
										set_product.InCrossProjections,
										ProductMetricDef))
							})
					})),
				Case(
					"the product distance is symmetric, as each coordinate distance is",
					Derive(func(b *Argument) {
						b.FixAs[Prod[A, B]]("p")
						b.FixAs[Prod[A, B]]("q")
						points := b.Assume()
						b.Show(
							"each coordinate distance reads the same both ways",
							By(
								points,
								DistSym.Read(left).AsFact().At(b.TermAs[A]("fst(p)"), b.TermAs[A]("fst(q)")),
								DistSym.Read(right).AsFact().At(b.TermAs[B]("snd(p)"), b.TermAs[B]("snd(q)")),
								set_product.InCrossProjections,
								ProductMetricDef))
					})),
				Case(
					"the product distance obeys the triangle inequality, coordinate by coordinate",
					Derive(func(b *Argument) {
						b.FixAs[Prod[A, B]]("p")
						b.FixAs[Prod[A, B]]("q")
						b.FixAs[Prod[A, B]]("r")
						points := b.Assume()
						// The larger distance from p to r is at most the bound when
						// each coordinate distance is.
						b.Do(Simp(Fwd(ProductMetricDef), Fwd(real_sup_inf.MaxLessEq)))
						b.Show(
							"each coordinate's detour through q is at most the sum of the two larger distances",
							ByArith(
								points,
								DistTriangle.Read(left).AsFact().At(
									b.TermAs[A]("fst(p)"), b.TermAs[A]("fst(q)"), b.TermAs[A]("fst(r)")),
								DistTriangle.Read(right).AsFact().At(
									b.TermAs[B]("snd(p)"), b.TermAs[B]("snd(q)"), b.TermAs[B]("snd(r)")),
								real_sup_inf.MaxUpperBound.At(
									b.TermAs[Real]("d(fst(p), fst(q))"), b.TermAs[Real]("e(snd(p), snd(q))")),
								real_sup_inf.MaxUpperBound.At(
									b.TermAs[Real]("d(fst(q), fst(r))"), b.TermAs[Real]("e(snd(q), snd(r))")),
								set_product.InCrossProjections))
					})),
			))
		}),
})}

// ProductBall — a ball of the product is the rectangle of the two
// balls of the same radius about the coordinates of its centre: the
// larger of two distances is below r exactly when both are, and a pair
// lies in the product exactly when its coordinates lie in M and N. No
// axiom enters.
var ProductBall = productBallThm{family.Add(registry.ProofEntry{
	Name: "ProductBall",
	Key:  "prop_54675a299d83dacc",
	Build: family.Theorem("∀M:set(A). "+
		"∀d:(A → A → real). "+
		"∀N:set(B). "+
		"∀e:(B → B → real). "+
		"∀p:prod(A, B). "+
		"∀r:real. "+
		"    ball(set_cross(M, N), product_metric(d, e), p, r) = "+
		"    set_cross(ball(M, d, fst(p), r), ball(N, e, snd(p), r))",
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			p *Expr[Prod[A, B]],
			r *Expr[Real],
		) {
			below := a.Have(
				"the larger of the two coordinate distances is below r exactly when both are",
				"∀q:prod(A, B). product_metric(d, e, p, q) < r ⇔ d(fst(p), fst(q)) < r ∧ e(snd(p), snd(q)) < r",
				Derive(func(b *Argument) {
					b.FixAs[Prod[A, B]]("q")
					b.Show(
						"the larger of two reals is below r exactly when each is",
						By(
							ProductMetricDef,
							real_sup_inf.MaxLessThan.At(
								b.TermAs[Real]("d(fst(p), fst(q))"), b.TermAs[Real]("e(snd(p), snd(q))"), r)))
				}))
			a.Show(
				"so a pair lies in the ball of the product exactly when each coordinate lies in its ball",
				Unfold(BallDef),
				Simp(Fwd(set_basic.Extension), Fwd(set_product.InCrossProjections), Fwd(below)),
				BySets())
		}),
})}

// ProductClosedBall — a closed ball of the product is the rectangle of
// the two closed balls of the same radius about the coordinates of its
// centre: the larger of two distances is at most r exactly when both
// are. No axiom enters.
var ProductClosedBall = productClosedBallThm{family.Add(registry.ProofEntry{
	Name: "ProductClosedBall",
	Key:  "prop_781924a45a0edbd",
	Build: family.Theorem("∀M:set(A). "+
		"∀d:(A → A → real). "+
		"∀N:set(B). "+
		"∀e:(B → B → real). "+
		"∀p:prod(A, B). "+
		"∀r:real. "+
		"    closed_ball(set_cross(M, N), product_metric(d, e), p, r) = "+
		"    set_cross(closed_ball(M, d, fst(p), r), closed_ball(N, e, snd(p), r))",
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			p *Expr[Prod[A, B]],
			r *Expr[Real],
		) {
			within := a.Have(
				"the larger of the two coordinate distances is at most r exactly when both are",
				"∀q:prod(A, B). product_metric(d, e, p, q) ≤ r ⇔ d(fst(p), fst(q)) ≤ r ∧ e(snd(p), snd(q)) ≤ r",
				Derive(func(b *Argument) {
					b.FixAs[Prod[A, B]]("q")
					b.Show(
						"the larger of two reals is at most r exactly when each is",
						By(
							ProductMetricDef,
							real_sup_inf.MaxLessEq.At(
								b.TermAs[Real]("d(fst(p), fst(q))"), b.TermAs[Real]("e(snd(p), snd(q))"), r)))
				}))
			a.Show(
				"so a pair lies in the closed ball of the product "+
					"exactly when each coordinate lies in its closed ball",
				Unfold(ClosedBallDef),
				Simp(Fwd(set_basic.Extension), Fwd(set_product.InCrossProjections), Fwd(within)),
				BySets())
		}),
})}

// ProductMetricTopology — the topology of the product distance is the
// product of the two metric topologies. A ball of the product is the
// rectangle of the two balls about the coordinates of its centre
// (ProductBall), so a set open for the product distance holds, about
// each of its points, a rectangle of two open balls holding the point.
// Conversely a point of a set open in the product lies in a rectangle of
// open sets inside it; balls about its coordinates inside the two sides,
// cut to the smaller of their radii, make a ball of the product inside
// the rectangle.
var ProductMetricTopology = productMetricTopologyThm{family.Add(registry.ProofEntry{
	Name: "ProductMetricTopology",
	Key:  "prop_b45937620f8ebfed",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_space(N, e)",
		},
		Conclusion: "metric_topology(set_cross(M, N), product_metric(d, e)) = " +
			"product_topology(metric_topology(M, d), metric_topology(N, e))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			left MetricSpaceFact[on.M],
			right MetricSpaceFact[on.N],
		) {
			// Two families are equal when they have the same members, and a
			// member of the product topology holds a rectangle of open sets
			// about each of its points.
			a.Do(Simp(Fwd(set_basic.Extension.Inst[Set[Prod[A, B]]]()), Fwd(product_topology.ProductOpenIff)))
			a.FixAs[Set[Prod[A, B]]]("w")
			a.Iff()

			a.Forward(
				"about a point of w, a ball of the product inside w "+
					"is a rectangle of two open balls holding the point",
				func(b *Argument, open Fact) {
					wOpen := b.Conjuncts(
						b.Simplified(open, Fwd(OpenIff)),
						"w lies in the product of M and N",
						"each point of w has a ball of the product about it inside w")
					p := b.FixAs[Prod[A, B]]("p")
					inW := b.Assume()
					r, radius := b.ObtainAs[Real](
						"w gives p a ball of the product of radius r inside it",
						"∃r:real. &0 < r ∧ ball(set_cross(M, N), product_metric(d, e), p, r) ⊆ w",
						By(wOpen[1].At(p), inW))
					about := b.Conjuncts(
						radius,
						"r is positive",
						"the ball of radius r lies in w")
					coords := b.Conjuncts(
						b.Have(
							"the coordinates of p lie in M and N, p lying in w",
							"fst(p) ∈ M ∧ snd(p) ∈ N",
							BySets(inW, wOpen[0], set_product.InCrossProjections)),
						"fst(p) lies in M",
						"snd(p) lies in N")
					first := b.MemberOf[on.M](b.TermAs[A]("fst(p)"), coords[0])
					second := b.MemberOf[on.N](b.TermAs[B]("snd(p)"), coords[1])
					b.Take(b.TermAs[Set[A]]("ball(M, d, fst(p), r)"))
					b.Take(b.TermAs[Set[B]]("ball(N, e, snd(p), r)"))
					b.Do(SplitConjAll(
						Case(
							"the ball about fst(p) is open in M",
							By(BallOpen.Read(left).At(first, r))),
						Case(
							"the ball about snd(p) is open in N",
							By(BallOpen.Read(right).At(second, r))),
						Case(
							"p lies in the rectangle, each coordinate in the ball about it",
							By(
								CentreInBall.Read(left).At(first, r),
								CentreInBall.Read(right).At(second, r),
								about[0],
								set_product.InCrossProjections)),
						Case(
							"and the rectangle is the ball of the product, which lies in w",
							By(ProductBall.At(M, d, N, e, p, r), about[1])),
					))
				})

			a.Backward(
				"about a point of a rectangle of open sets inside w, the ball "+
					"of the product of the smaller of two radii lies in the rectangle",
				func(b *Argument, rect Fact) {
					each := b.Have(
						"each point p of w lies in the product, with a ball of the product about it inside w",
						Statement{
							Binders: "∀p:prod(A, B).",
							Hypotheses: []string{
								"p ∈ w",
							},
							Conclusion: "p ∈ set_cross(M, N) ∧ " +
								"(∃r:real. &0 < r ∧ ball(set_cross(M, N), product_metric(d, e), p, r) ⊆ w)",
						},
						Derive(func(c *Argument) {
							p := c.FixAs[Prod[A, B]]("p")
							inW := c.Assume()
							_, _, box := c.Unpack2As[Set[A], Set[B]](GroupPremises(inW, rect.At(p)), "u", "v")
							parts := c.Conjuncts(
								box,
								"u is open in M",
								"v is open in N",
								"p lies in the rectangle u × v",
								"the rectangle lies in w")
							uOpen := c.Conjuncts(
								c.Simplified(parts[0], Fwd(OpenIff)),
								"u lies in M",
								"each point of u has a ball about it inside u")
							vOpen := c.Conjuncts(
								c.Simplified(parts[1], Fwd(OpenIff)),
								"v lies in N",
								"each point of v has a ball about it inside v")
							coords := c.Conjuncts(
								c.Simplified(parts[2], Fwd(set_product.InCrossProjections)),
								"fst(p) lies in u",
								"snd(p) lies in v")
							first, second := c.TermAs[A]("fst(p)"), c.TermAs[B]("snd(p)")
							r1, ballU := c.ObtainAs[Real](
								"u gives fst(p) a ball of radius r₁ inside it",
								"∃r₁:real. &0 < r₁ ∧ ball(M, d, fst(p), r₁) ⊆ u",
								By(uOpen[1].At(first), coords[0]))
							r2, ballV := c.ObtainAs[Real](
								"and v gives snd(p) one of radius r₂",
								"∃r₂:real. &0 < r₂ ∧ ball(N, e, snd(p), r₂) ⊆ v",
								By(vOpen[1].At(second), coords[1]))
							aboutU := c.Conjuncts(
								ballU,
								"r₁ is positive",
								"the ball of radius r₁ about fst(p) lies in u")
							aboutV := c.Conjuncts(
								ballV,
								"r₂ is positive",
								"the ball of radius r₂ about snd(p) lies in v")
							smaller := c.TermAs[Real]("min(r₁, r₂)")
							rectangle := c.Have(
								"the balls of the smaller radius about the coordinates "+
									"lie in u and v, so their rectangle lies in w",
								"set_cross(ball(M, d, fst(p), min(r₁, r₂)), ball(N, e, snd(p), min(r₁, r₂))) ⊆ w",
								BySets(
									aboutU[1],
									aboutV[1],
									parts[3],
									BallConcentric.At(M, d, first, smaller, r1),
									BallConcentric.At(N, e, second, smaller, r2),
									real_sup_inf.MinLowerBound.At(r1, r2),
									set_product.InCrossProjections))
							c.Do(SplitConj(
								Case(
									"p lies in the product, its coordinates lying in u ⊆ M and v ⊆ N",
									BySets(coords[0], coords[1], uOpen[0], vOpen[0], set_product.InCrossProjections)),
								Case(
									"and the ball of the product of the smaller radius about p is that rectangle",
									Derive(func(f *Argument) {
										f.Take(smaller)
										f.Do(SplitConj(
											Case(
												"the smaller radius is positive, both being positive",
												By(real_sup_inf.LessThanMin.At(r1, r2, f.TermAs[Real]("&0")), aboutU[0], aboutV[0])),
											Case(
												"and the ball is the rectangle, which lies in w",
												By(ProductBall.At(M, d, N, e, p, smaller), rectangle)),
										))
									})),
							))
						}))
					b.Show(
						"so w lies in the product, and each of its points has a ball of the product about it inside w",
						Simp(Fwd(OpenIff)),
						BySets(each))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The countable product metric
// ---------------------------------------------------------------------------

// The three laws below are how the countable product distance is used: it
// dominates the clipped weighted distance at every place whose index is
// in J, it lies below every nonnegative bound of those, and it is not
// negative when the coordinate distances at those places are not. A place
// whose index is not in J contributes zero to the supremum; the laws
// absorb that case, and the members after them cite the laws, not the
// definition.

// CountableProductCoordinateBelow — at a place n whose index h(n) lies in
// J, the distance of the coordinates at h(n), clipped at one and weighted
// by 1/(n + 1), is at most the countable product distance. No axiom of
// the factors enters: every term of the supremum is at most one, and the
// term at n is this one.
var CountableProductCoordinateBelow = countableProductCoordinateBelowThm{family.Add(registry.ProofEntry{
	Name: "CountableProductCoordinateBelow",
	Key:  "prop_7ba8a0f68643086",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀d:(I → A → A → real). ∀h:(num → I). ∀f g:(I → A). ∀n:num.",
		Hypotheses: []string{
			"h(n) ∈ J",
		},
		Conclusion: "min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1) ≤ " +
			"countable_product_metric(J, d, h, f, g)",
	}, func(
		a *Argument,
		J *Expr[Set[I]],
		d *Expr[Fun3[I, A, A, Real]],
		h *Arrow[Nat, I],
		f, g *Arrow[I, A],
		n *Expr[Nat],
		active Fact,
	) {
		one := a.TermAs[Real]("&1")
		bounded := a.Have(
			"every term of the supremum is at most one",
			"∀m:num. COND(h(m) ∈ J, min(d(h(m), f(h(m)), g(h(m))), &1) * real_inv(&m + &1), &0) ≤ &1",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("m")
				b.Cases(b.TermAs[Bool]("h(m) ∈ J"))
				b.When(
					"at a place in J the clipped distance and the weight are at most one",
					func(c *Argument, inJ Fact) {
						weight := c.Have(
							"the weight 1/(m + 1) lies in (0, 1]",
							"&0 < real_inv(&m + &1) ∧ real_inv(&m + &1) ≤ &1",
							ByArith())
						c.Show(
							"so is their product",
							ByArith(
								inJ,
								weight,
								real_sup_inf.MinLowerBound.At(c.TermAs[Real]("d(h(m), f(h(m)), g(h(m)))"), one),
								real_order_ring.LessEqMulRight.At(
									c.TermAs[Real]("min(d(h(m), f(h(m)), g(h(m))), &1)"), one, c.TermAs[Real]("real_inv(&m + &1)"))))
					})
				b.Otherwise(
					"elsewhere the term is zero",
					func(c *Argument, outside Fact) {
						c.Show(
							"zero is at most one",
							ByArith(outside))
					})
			}))
		a.Do(Simp(Fwd(CountableProductMetricDef)))
		a.Show(
			"the term at n is the clipped weighted distance at h(n)",
			By(
				active,
				bounded,
				real_sup_inf.TermLessEqSequenceSup.At(
					a.TermAs[Fun[Nat, Real]](
						"λm:num. COND(h(m) ∈ J, min(d(h(m), f(h(m)), g(h(m))), &1) * real_inv(&m + &1), &0)"),
					one,
					n)))
	}),
})}

// CountableProductLeastBound — a nonnegative bound of the clipped weighted
// distances at the places whose index lies in J bounds the countable
// product distance: it bounds every term of the supremum, the others
// being zero.
var CountableProductLeastBound = countableProductLeastBoundThm{family.Add(registry.ProofEntry{
	Name: "CountableProductLeastBound",
	Key:  "prop_dcc3f9e53ac38ac1",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀d:(I → A → A → real). ∀h:(num → I). ∀f g:(I → A). ∀b:real.",
		Hypotheses: []string{
			"&0 ≤ b",
			"∀n:num. h(n) ∈ J ⇒ min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1) ≤ b",
		},
		Conclusion: "countable_product_metric(J, d, h, f, g) ≤ b",
	}, func(
		a *Argument,
		J *Expr[Set[I]],
		d *Expr[Fun3[I, A, A, Real]],
		h *Arrow[Nat, I],
		f, g *Arrow[I, A],
		b *Expr[Real],
		nonnegative, bounds Fact,
	) {
		every := a.Have(
			"b bounds every term of the supremum",
			"∀n:num. COND(h(n) ∈ J, min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1), &0) ≤ b",
			Derive(func(c *Argument) {
				n := c.FixAs[Nat]("n")
				c.Cases(c.TermAs[Bool]("h(n) ∈ J"))
				c.When(
					"at a place in J the term is the clipped weighted distance",
					func(e *Argument, inJ Fact) {
						e.Show(
							"which b bounds",
							ByArith(inJ, bounds.At(n)))
					})
				c.Otherwise(
					"elsewhere the term is zero",
					func(e *Argument, outside Fact) {
						e.Show(
							"which b bounds",
							ByArith(outside, nonnegative))
					})
			}))
		a.Do(Simp(Fwd(CountableProductMetricDef)))
		a.Show(
			"so b bounds the supremum",
			By(
				every,
				real_sup_inf.SequenceSupLessEqBound.At(
					a.TermAs[Fun[Nat, Real]](
						"λn:num. COND(h(n) ∈ J, min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1), &0)"),
					b)))
	}),
})}

// CountableProductNonneg — the countable product distance between two
// functions is not negative when their coordinates at the indices of J
// are at nonnegative distances: every term of the supremum then lies
// between zero and one, and the supremum is at least the first.
var CountableProductNonneg = countableProductNonnegThm{family.Add(registry.ProofEntry{
	Name: "CountableProductNonneg",
	Key:  "prop_2b7a0431874c7617",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀d:(I → A → A → real). ∀h:(num → I). ∀f g:(I → A).",
		Hypotheses: []string{
			"∀n:num. h(n) ∈ J ⇒ &0 ≤ d(h(n), f(h(n)), g(h(n)))",
		},
		Conclusion: "&0 ≤ countable_product_metric(J, d, h, f, g)",
	}, func(
		a *Argument,
		J *Expr[Set[I]],
		d *Expr[Fun3[I, A, A, Real]],
		h *Arrow[Nat, I],
		f, g *Arrow[I, A],
		nonnegative Fact,
	) {
		one := a.TermAs[Real]("&1")
		between := a.Have(
			"every term of the supremum lies between zero and one",
			"∀m:num. "+
				"    &0 ≤ COND(h(m) ∈ J, min(d(h(m), f(h(m)), g(h(m))), &1) * real_inv(&m + &1), &0) ∧ "+
				"    COND(h(m) ∈ J, min(d(h(m), f(h(m)), g(h(m))), &1) * real_inv(&m + &1), &0) ≤ &1",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				b.Cases(b.TermAs[Bool]("h(m) ∈ J"))
				b.When(
					"at a place in J it is a nonnegative distance clipped at one, times a weight in (0, 1]",
					func(c *Argument, inJ Fact) {
						distance := c.TermAs[Real]("d(h(m), f(h(m)), g(h(m)))")
						weight := c.Have(
							"the weight 1/(m + 1) lies in (0, 1]",
							"&0 < real_inv(&m + &1) ∧ real_inv(&m + &1) ≤ &1",
							ByArith())
						c.Show(
							"so it lies between zero and one",
							ByArith(
								inJ,
								weight,
								nonnegative.At(m),
								real_sup_inf.MinIsArgument.At(distance, one),
								real_sup_inf.MinLowerBound.At(distance, one),
								real_order_ring.LessEqMulRight.At(
									c.TermAs[Real]("min(d(h(m), f(h(m)), g(h(m))), &1)"), one, c.TermAs[Real]("real_inv(&m + &1)"))))
					})
				b.Otherwise(
					"elsewhere the term is zero",
					func(c *Argument, outside Fact) {
						c.Show(
							"which lies between zero and one",
							ByArith(outside))
					})
			}))
		a.Do(Simp(Fwd(CountableProductMetricDef)))
		a.Show(
			"the supremum is at least the term at the first place",
			ByArith(
				between,
				real_sup_inf.TermLessEqSequenceSup.At(
					a.TermAs[Fun[Nat, Real]](
						"λm:num. COND(h(m) ∈ J, min(d(h(m), f(h(m)), g(h(m))), &1) * real_inv(&m + &1), &0)"),
					one,
					a.TermAs[Nat]("0"))))
	}),
})}

// CountableProductMetric — the functions that lie in metric factors at the
// indices of J and take prescribed values elsewhere form a metric space
// under the countable product distance along a sequence h that runs
// through J — h may repeat an index, and may take indices outside J,
// which contribute nothing.
//
// Each axiom passes from the factors through the three laws of the
// distance. At a place whose index lies in J the clipped weighted
// distances between points of the product are nonnegative, vanish on
// equal points, are symmetric and obey the triangle inequality, clipping
// at one and a positive weight keeping each axiom of the factor, and the
// distance dominates each of them and lies below every nonnegative bound
// of them. A zero distance squeezes the clipped weighted distance at
// every place to zero, a positive weight then detects a zero factor
// distance, every index of J is taken somewhere, and two points of the
// product agree outside J.
var CountableProductMetric = countableProductMetricThm{family.Add(registry.ProofEntry{
	Name: "CountableProductMetric",
	Key:  "prop_1aa933123b1126e",
	Build: family.Sections(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)). ∀d:(I → A → A → real). ∀h:(num → I).",
		Hypotheses: []string{
			"J ⊆ image(h, 𝕌)",
			"∀i:I. i ∈ J ⇒ metric_space(X(i), d(i))",
		},
		Conclusion: "metric_space(indexed_functions(J, z, X), countable_product_metric(J, d, h))",
		Abbrev: Abbrev{
			{Name: "WeightedDistance", Text: "λn:num. λf:(I → A). λg:(I → A). " +
				"    min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			clippedTriangle := ctx.Lemma(Statement{
				Binders: "∀a b c:real.",
				Hypotheses: []string{
					"&0 ≤ b",
					"&0 ≤ c",
					"a ≤ b + c",
				},
				Conclusion: "min(a, &1) ≤ min(b, &1) + min(c, &1)",
			}, func(p *Argument, a, b, c *Expr[Real], given Fact) {
				p.Show(
					"clipping a triangle with nonnegative sides preserves its inequality",
					ByArith(given))
			})
			reciprocalWeights := ctx.Lemma("∀n:num. "+
				"    &0 < real_inv(&n + &1) ∧ real_inv(&n + &1) ≤ &1", func(a *Argument) {
				a.Show(
					"reciprocal weights are positive and at most one",
					ByArith())
			})
			return ctx.Theorem(headline, func(
				a *Argument,
				J *Expr[Set[I]],
				z *Arrow[I, A],
				X *Arrow[I, Set[A]],
				d *Expr[Fun3[I, A, A, Real]],
				h *Arrow[Nat, I],
				cover, factors Fact,
			) {
				coordinates := a.Have(
					"at a place whose index lies in J the factor is a metric "+
						"space holding the coordinate of a point of the product",
					Statement{
						Binders: "∀n:num. ∀f:(I → A).",
						Hypotheses: []string{
							"h(n) ∈ J",
							"f ∈ indexed_functions(J, z, X)",
						},
						Conclusion: "metric_space(X(h(n)), d(h(n))) ∧ f(h(n)) ∈ X(h(n))",
					},
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]()
						f := b.FixAs[Fun[I, A]]()
						data := b.Assume()
						b.Show(
							"the factor at an index of J is a metric space, and it holds the coordinate there",
							By(
								factors.At(h.Apply(n)),
								data,
								indexed_functions.IndexedFunctionsCoordinate.At(J, z, X, h.Apply(n), f)))
					}))
				nonneg := a.Have(
					"the distance between two points of the product is not negative",
					Statement{
						Binders: "∀f g:(I → A).",
						Hypotheses: []string{
							"f ∈ indexed_functions(J, z, X)",
							"g ∈ indexed_functions(J, z, X)",
						},
						Conclusion: "&0 ≤ countable_product_metric(J, d, h, f, g)",
					},
					Derive(func(b *Argument) {
						f := b.FixAs[Fun[I, A]]()
						g := b.FixAs[Fun[I, A]]()
						members := b.Assume()
						coordinateNonneg := b.Have(
							"their coordinates at the indices of J are at nonnegative distances",
							"∀n:num. h(n) ∈ J ⇒ &0 ≤ d(h(n), f(h(n)), g(h(n)))",
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]()
								inJ := c.Assume()
								c.Show(
									"a distance of the factor is never negative",
									By(
										inJ,
										members,
										coordinates.At(n, f),
										coordinates.At(n, g),
										DistNonneg.At(
											c.TermAs[Set[A]]("X(h(n))"),
											c.TermAs[Fun2[A, A, Real]]("d(h(n))"),
											c.TermAs[A]("f(h(n))"),
											c.TermAs[A]("g(h(n))"))))
							}))
						b.Show(
							"so is the countable product distance",
							By(coordinateNonneg, CountableProductNonneg.At(J, d, h, f, g)))
					}))
				dominated := a.Have(
					"the distance from one point of the product to another is at most the distance back",
					Statement{
						Binders: "∀f g:(I → A).",
						Hypotheses: []string{
							"f ∈ indexed_functions(J, z, X)",
							"g ∈ indexed_functions(J, z, X)",
						},
						Conclusion: "countable_product_metric(J, d, h, f, g) ≤ countable_product_metric(J, d, h, g, f)",
					},
					Derive(func(b *Argument) {
						f := b.FixAs[Fun[I, A]]()
						g := b.FixAs[Fun[I, A]]()
						members := b.Assume()
						each := b.Have(
							"at every index of J the clipped weighted distance "+
								"is the one back, which the distance back dominates",
							"∀n:num. h(n) ∈ J ⇒ «WeightedDistance»(n, f, g) ≤ countable_product_metric(J, d, h, g, f)",
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]()
								inJ := c.Assume()
								c.Show(
									"the factor distance is symmetric",
									By(
										inJ,
										members,
										coordinates.At(n, f),
										coordinates.At(n, g),
										DistSym.At(
											c.TermAs[Set[A]]("X(h(n))"),
											c.TermAs[Fun2[A, A, Real]]("d(h(n))"),
											c.TermAs[A]("f(h(n))"),
											c.TermAs[A]("g(h(n))")),
										CountableProductCoordinateBelow.At(J, d, h, g, f, n)))
							}))
						b.Show(
							"the distance back is a nonnegative bound of them all",
							By(
								each,
								members,
								nonneg.At(g, f),
								CountableProductLeastBound.At(
									J, d, h, f, g, b.TermAs[Real]("countable_product_metric(J, d, h, g, f)"))))
					}))
				definite := a.Have(
					"the distance vanishes exactly between equal points",
					Statement{
						Binders: "∀f g:(I → A).",
						Hypotheses: []string{
							"f ∈ indexed_functions(J, z, X)",
							"g ∈ indexed_functions(J, z, X)",
						},
						Conclusion: "countable_product_metric(J, d, h, f, g) = &0 ⇔ f = g",
					},
					Derive(func(b *Argument) {
						f := b.FixAs[Fun[I, A]]()
						g := b.FixAs[Fun[I, A]]()
						members := b.Assume()
						b.Iff()
						b.Forward(
							"at distance zero the coordinates agree at every index of J",
							func(c *Argument, zero Fact) {
								agree := c.Have(
									"every index of J is taken by h at a place where the coordinates are at distance zero",
									"∀i:I. i ∈ J ⇒ f(i) = g(i)",
									Derive(func(e *Argument) {
										i := e.FixAs[I]()
										active := e.Assume()
										n, enumerated := e.ObtainAs[Nat](
											"h takes this index at some place",
											"∃n:num. h(n) = i",
											BySets(cover, active))
										distance := e.TermAs[Real]("d(i, f(i), g(i))")
										vanishing := e.Have(
											"a positive weight and clipping at one reflect zero",
											"d(i, f(i), g(i)) = &0",
											ByArith(
												zero,
												enumerated,
												active,
												CountableProductCoordinateBelow.At(J, d, h, f, g, n),
												DistNonneg.At(
													e.TermAs[Set[A]]("X(i)"),
													e.TermAs[Fun2[A, A, Real]]("d(i)"),
													e.TermAs[A]("f(i)"),
													e.TermAs[A]("g(i)")),
												factors.At(i),
												members,
												indexed_functions.IndexedFunctionsCoordinate.At(J, z, X, i, f),
												indexed_functions.IndexedFunctionsCoordinate.At(J, z, X, i, g),
												real_sup_inf.MinIsArgument.At(distance, e.TermAs[Real]("&1")),
												At(reciprocalWeights, n)))
										e.Show(
											"the factor metric identifies the coordinates",
											By(
												factors.At(i),
												vanishing,
												active,
												members,
												indexed_functions.IndexedFunctionsCoordinate.At(J, z, X, i, f),
												indexed_functions.IndexedFunctionsCoordinate.At(J, z, X, i, g),
												DistZeroIff.At(
													e.TermAs[Set[A]]("X(i)"),
													e.TermAs[Fun2[A, A, Real]]("d(i)"),
													e.TermAs[A]("f(i)"),
													e.TermAs[A]("g(i)"))))
									}))
								c.Show(
									"and points of the product agree outside J",
									By(agree, members, indexed_functions.IndexedFunctionsExtensional.At(J, z, X, f, g)))
							})
						b.Backward(
							"a point is at distance zero from itself",
							func(c *Argument, equal Fact) {
								c.Do(equal.Rw())
								vanishing := c.Have(
									"every clipped weighted distance from g to itself is zero",
									"∀n:num. h(n) ∈ J ⇒ «WeightedDistance»(n, g, g) ≤ &0",
									Derive(func(e *Argument) {
										n := e.FixAs[Nat]()
										inJ := e.Assume()
										e.Show(
											"the factor distance from a point to itself is zero",
											ByArith(
												inJ,
												members,
												coordinates.At(n, g),
												DistSelf.At(
													e.TermAs[Set[A]]("X(h(n))"), e.TermAs[Fun2[A, A, Real]]("d(h(n))"), e.TermAs[A]("g(h(n))")),
												real_sup_inf.MinIsArgument.At(e.TermAs[Real]("&0"), e.TermAs[Real]("&1"))))
									}))
								below := c.Have(
									"so zero bounds the distance from g to itself",
									"countable_product_metric(J, d, h, g, g) ≤ &0",
									By(
										vanishing,
										real_order_ring.LessEqRefl.At(c.TermAs[Real]("&0")),
										CountableProductLeastBound.At(J, d, h, g, g, c.TermAs[Real]("&0"))))
								c.Show(
									"which is not negative",
									ByArith(members, below, nonneg.At(g, g)))
							})
					}))
				symmetric := a.Have(
					"the distance reads the same both ways",
					Statement{
						Binders: "∀f g:(I → A).",
						Hypotheses: []string{
							"f ∈ indexed_functions(J, z, X)",
							"g ∈ indexed_functions(J, z, X)",
						},
						Conclusion: "countable_product_metric(J, d, h, f, g) = countable_product_metric(J, d, h, g, f)",
					},
					Derive(func(b *Argument) {
						f := b.FixAs[Fun[I, A]]()
						g := b.FixAs[Fun[I, A]]()
						members := b.Assume()
						b.Show(
							"each way is at most the other",
							ByArith(members, dominated.At(f, g), dominated.At(g, f)))
					}))
				triangle := a.Have(
					"a detour through a third point is never shorter",
					Statement{
						Binders: "∀u v w:(I → A).",
						Hypotheses: []string{
							"u ∈ indexed_functions(J, z, X)",
							"v ∈ indexed_functions(J, z, X)",
							"w ∈ indexed_functions(J, z, X)",
						},
						Conclusion: "countable_product_metric(J, d, h, u, w) ≤ " +
							"countable_product_metric(J, d, h, u, v) + countable_product_metric(J, d, h, v, w)",
					},
					Derive(func(b *Argument) {
						u := b.FixAs[Fun[I, A]]()
						v := b.FixAs[Fun[I, A]]()
						w := b.FixAs[Fun[I, A]]()
						members := b.Assume()
						each := b.Have(
							"at every index of J the clipped weighted triangle holds, and the distances dominate its two sides",
							Statement{
								Binders: "∀n:num.",
								Hypotheses: []string{
									"h(n) ∈ J",
								},
								Conclusion: "«WeightedDistance»(n, u, w) ≤ " +
									"countable_product_metric(J, d, h, u, v) + countable_product_metric(J, d, h, v, w)",
							},
							Derive(func(c *Argument) {
								n := c.FixAs[Nat]()
								inJ := c.Assume()
								factor := c.TermAs[Set[A]]("X(h(n))")
								distance := c.TermAs[Fun2[A, A, Real]]("d(h(n))")
								ui := c.TermAs[A]("u(h(n))")
								vi := c.TermAs[A]("v(h(n))")
								wi := c.TermAs[A]("w(h(n))")
								sides := c.Have(
									"the factor triangle at h(n) has nonnegative sides",
									"&0 ≤ d(h(n), u(h(n)), v(h(n))) ∧ "+
										"&0 ≤ d(h(n), v(h(n)), w(h(n))) ∧ "+
										"d(h(n), u(h(n)), w(h(n))) ≤ d(h(n), u(h(n)), v(h(n))) + d(h(n), v(h(n)), w(h(n)))",
									By(
										inJ,
										members,
										coordinates.At(n, u),
										coordinates.At(n, v),
										coordinates.At(n, w),
										DistNonneg.At(factor, distance, ui, vi),
										DistNonneg.At(factor, distance, vi, wi),
										DistTriangle.At(factor, distance, ui, vi, wi)))
								c.Show(
									"clipping and the positive weight keep it, and each side is at most its distance",
									ByArith(
										inJ,
										sides,
										At(
											clippedTriangle,
											c.TermAs[Real]("d(h(n), u(h(n)), w(h(n)))"),
											c.TermAs[Real]("d(h(n), u(h(n)), v(h(n)))"),
											c.TermAs[Real]("d(h(n), v(h(n)), w(h(n)))")),
										At(reciprocalWeights, n),
										real_order_ring.LessEqMulRight.At(
											c.TermAs[Real]("min(d(h(n), u(h(n)), w(h(n))), &1)"),
											c.TermAs[Real]("min(d(h(n), u(h(n)), v(h(n))), &1) + min(d(h(n), v(h(n)), w(h(n))), &1)"),
											c.TermAs[Real]("real_inv(&n + &1)")),
										CountableProductCoordinateBelow.At(J, d, h, u, v, n),
										CountableProductCoordinateBelow.At(J, d, h, v, w, n)))
							}))
						detour := b.Have(
							"the sum of the two distances is not negative",
							"&0 ≤ countable_product_metric(J, d, h, u, v) + countable_product_metric(J, d, h, v, w)",
							ByArith(members, nonneg.At(u, v), nonneg.At(v, w)))
						b.Show(
							"so it bounds the distance from u to w",
							By(
								each,
								detour,
								CountableProductLeastBound.At(
									J,
									d,
									h,
									u,
									w,
									b.TermAs[Real](
										"countable_product_metric(J, d, h, u, v) + countable_product_metric(J, d, h, v, w)"))))
					}))
				a.Show(
					"which are the axioms of a metric on the product",
					Unfold(MetricSpace),
					By(definite, symmetric, triangle))
			})
		}),
})}

// CountableProductProjectionUniform — under the countable product
// distance, the coordinate at an index of J that h takes depends
// uniformly continuously on the point: for every ε > 0 some δ > 0 keeps
// the distance of that coordinate below ε wherever the product distance
// is below δ. No axiom of the factors enters.
//
// Where h takes i at the place n, δ = min(ε, 1)/(n + 1) serves: the
// clipped weighted distance at n is at most the product distance
// (CountableProductCoordinateBelow), so below min(ε, 1)/(n + 1); the
// clipped distance of i is then below min(ε, 1) ≤ 1, and below the
// clipping level it is the distance itself.
var CountableProductProjectionUniform = countableProductProjectionUniformThm{family.Add(registry.ProofEntry{
	Name: "CountableProductProjectionUniform",
	Key:  "prop_76c7326d2e0faff1",
	Build: family.Sections(Statement{
		Binders: "∀J:set(I). ∀d:(I → A → A → real). ∀h:(num → I). ∀i:I. ∀ε:real.",
		Hypotheses: []string{
			"i ∈ image(h, 𝕌)",
			"i ∈ J",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ ∀f g:(I → A). countable_product_metric(J, d, h, f, g) < δ ⇒ d(i, f(i), g(i)) < ε",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			reciprocalWeights := ctx.Lemma("∀n:num. "+
				"    &0 < real_inv(&n + &1) ∧ real_inv(&n + &1) ≤ &1", func(a *Argument) {
				a.Show(
					"reciprocal weights are positive and at most one",
					ByArith())
			})
			clippedReflection := ctx.Lemma(Statement{
				Binders: "∀a w ε:real.",
				Hypotheses: []string{
					"&0 < w",
					"ε ≤ &1",
					"min(a, &1) * w < ε * w",
				},
				Conclusion: "a < ε",
			}, func(p *Argument, a, w, ε *Expr[Real], given Fact) {
				p.Show(
					"below the clipping level a weighted bound reflects to the original distance",
					ByArith(given, real_sup_inf.MinIsArgument.At(a, p.TermAs[Real]("&1"))))
			})
			return ctx.Theorem(headline, func(
				a *Argument,
				J *Expr[Set[I]],
				d *Expr[Fun3[I, A, A, Real]],
				h *Arrow[Nat, I],
				i *Expr[I],
				taken, active Fact,
				ε *Expr[Real],
				positive Fact,
			) {
				n, listed := a.ObtainAs[Nat](
					"h takes the coordinate i at some place n",
					"∃n:num. h(n) = i",
					BySets(taken))
				weight := a.TermAs[Real]("real_inv(&n + &1)")
				clippedRadius := a.TermAs[Real]("min(ε, &1)")
				reflection := a.Have(
					"a product distance below the clipped radius weighted at n keeps that coordinate within ε",
					Statement{
						Binders: "∀f g:(I → A).",
						Hypotheses: []string{
							"countable_product_metric(J, d, h, f, g) < min(ε, &1) * real_inv(&n + &1)",
						},
						Conclusion: "d(h(n), f(h(n)), g(h(n))) < ε",
					},
					Derive(func(b *Argument) {
						f := b.FixAs[Fun[I, A]]()
						g := b.FixAs[Fun[I, A]]()
						small := b.Assume()
						b.Show(
							"the clipped weighted distance at n lies below the "+
								"product distance, and clipping below one reflects",
							ByArith(
								CountableProductCoordinateBelow.At(J, d, h, f, g, n),
								small,
								listed,
								active,
								At(clippedReflection, b.TermAs[Real]("d(h(n), f(h(n)), g(h(n)))"), weight, clippedRadius),
								At(reciprocalWeights, n),
								real_sup_inf.MinLowerBound.At(ε, b.TermAs[Real]("&1"))))
					}))
				a.Take(a.TermAs[Real]("min(ε, &1) * real_inv(&n + &1)"))
				a.Do(SplitConj(
					Case(
						"the clipped radius weighted at n is positive",
						ByArith(
							positive,
							real_sup_inf.MinIsArgument.At(ε, a.TermAs[Real]("&1")),
							At(reciprocalWeights, n))),
					Case(
						"and it keeps the coordinate i within ε",
						By(reflection, listed)),
				))
			})
		}),
})}

// CountableProductHeadBound — under the countable product distance,
// finitely many coordinates control the rest: for every ε > 0 there is
// a place N such that any two functions whose distances are below ε at
// the indices of J that h takes up to N are at most ε apart. No axiom of
// the factors enters, and the functions need not lie in the product.
//
// The distance lies below every nonnegative bound of the clipped weighted
// distances at the indices of J (CountableProductLeastBound), and ε
// bounds each of them. Past the place where 1/(n + 1) falls below ε,
// each is at most its weight. Up to it, each is a distance below ε
// clipped at one and scaled by a weight in (0, 1]: a nonnegative clipped
// distance only decreases, and a negative one stays negative.
var CountableProductHeadBound = countableProductHeadBoundThm{family.Add(registry.ProofEntry{
	Name: "CountableProductHeadBound",
	Key:  "prop_16856d136f77d315",
	Build: family.Sections(Statement{
		Binders: "∀J:set(I). ∀d:(I → A → A → real). ∀h:(num → I). ∀ε:real.",
		Hypotheses: []string{
			"&0 < ε",
		},
		Conclusion: "∃N:num. ∀f g:(I → A). " +
			"    (∀n:num. n ≤ N ∧ h(n) ∈ J ⇒ d(h(n), f(h(n)), g(h(n))) < ε) ⇒ " +
			"    countable_product_metric(J, d, h, f, g) ≤ ε",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			reciprocalWeights := ctx.Lemma("∀n:num. "+
				"    &0 < real_inv(&n + &1) ∧ real_inv(&n + &1) ≤ &1", func(a *Argument) {
				a.Show(
					"reciprocal weights are positive and at most one",
					ByArith())
			})
			reciprocalTail := ctx.Lemma(Statement{
				Binders: "∀ε:real.",
				Hypotheses: []string{
					"&0 < ε",
				},
				Conclusion: "∃N:num. ∀n:num. N < n ⇒ real_inv(&n + &1) < ε",
			}, func(a *Argument, ε *Expr[Real], positive Fact) {
				N, small := a.ObtainAs[Nat](
					"some reciprocal weight is below the radius",
					"∃N:num. real_inv(&N + &1) < ε",
					By(real_archimedean.ExistsReciprocalBelow.At(ε), positive))
				a.Take(N)
				n := a.FixAs[Nat]()
				later := a.Assume()
				a.Show(
					"later reciprocal weights are smaller still",
					ByArith(
						small,
						later,
						real_order_ring.OfNumLessThan.At(N, n),
						real_order_field.InvAntitone.At(a.TermAs[Real]("&N + &1"), a.TermAs[Real]("&n + &1"))))
			})
			clippedBelow := ctx.Lemma(Statement{
				Binders: "∀a w ε:real.",
				Hypotheses: []string{
					"&0 < w",
					"w ≤ &1",
					"&0 < ε",
					"a < ε",
				},
				Conclusion: "min(a, &1) * w < ε",
			}, func(p *Argument, a, w, ε *Expr[Real], given Fact) {
				clipped := p.TermAs[Real]("min(a, &1)")
				one := p.TermAs[Real]("&1")
				p.Cases(p.TermAs[Bool]("&0 ≤ a"))
				p.When(
					"a nonnegative distance clipped at one and scaled by a weight at most one only decreases",
					func(c *Argument, nonnegative Fact) {
						c.Show(
							"the clipped distance is at most the distance, and the weight at most one",
							ByArith(
								given,
								nonnegative,
								real_sup_inf.MinIsArgument.At(a, one),
								real_sup_inf.MinLowerBound.At(a, one),
								real_order_ring.LessEqMulRight.At(w, one, clipped)))
					})
				p.Otherwise(
					"a negative distance clipped at one and scaled by a positive weight stays negative",
					func(c *Argument, negative Fact) {
						c.Show(
							"the clipped distance is at most the negative distance",
							ByArith(
								given,
								negative,
								real_sup_inf.MinLowerBound.At(a, one),
								real_order_ring.LessEqMulRight.At(clipped, c.TermAs[Real]("&0"), w)))
					})
			})
			return ctx.Theorem(headline, func(
				a *Argument,
				J *Expr[Set[I]],
				d *Expr[Fun3[I, A, A, Real]],
				h *Arrow[Nat, I],
				ε *Expr[Real],
				positive Fact,
			) {
				N, tail := a.ObtainAs[Nat](
					"past some place N every weight is below ε",
					"∃N:num. ∀n:num. N < n ⇒ real_inv(&n + &1) < ε",
					By(At(reciprocalTail, ε), positive))
				a.Take(N)
				f := a.FixAs[Fun[I, A]]()
				g := a.FixAs[Fun[I, A]]()
				head := a.Assume()
				bound := a.Have(
					"ε bounds the clipped weighted distance at every index of J",
					"∀n:num. h(n) ∈ J ⇒ min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1) ≤ ε",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]()
						inJ := b.Assume()
						distance := b.TermAs[Real]("d(h(n), f(h(n)), g(h(n)))")
						weight := b.TermAs[Real]("real_inv(&n + &1)")
						b.Cases(b.TermAs[Bool]("n ≤ N"))
						b.When(
							"up to N it is a distance below ε, clipped and weighted",
							func(c *Argument, inHead Fact) {
								c.Show(
									"clipping and a weight in (0, 1] keep it below ε",
									ByArith(
										inJ,
										inHead,
										head.At(n),
										positive,
										At(reciprocalWeights, n),
										At(clippedBelow, distance, weight, ε)))
							})
						b.Otherwise(
							"past N it is at most its weight, which is below ε",
							func(c *Argument, beyond Fact) {
								one := c.TermAs[Real]("&1")
								c.Show(
									"clipping at one bounds it by its weight",
									ByArith(
										beyond,
										tail.At(n),
										At(reciprocalWeights, n),
										real_sup_inf.MinLowerBound.At(distance, one),
										real_order_ring.LessEqMulRight.At(
											c.TermAs[Real]("min(d(h(n), f(h(n)), g(h(n))), &1)"), one, weight)))
							})
					}))
				a.Show(
					"so ε, being positive, bounds the product distance",
					By(
						bound,
						real_order_ring.LessEqOfLessThan.At(a.TermAs[Real]("&0"), ε),
						positive,
						CountableProductLeastBound.At(J, d, h, f, g, ε)))
			})
		}),
})}

// CountableProductMetricTopology — the countable product distance induces
// the product of the factor metric topologies.
//
// Both inclusions are read pointwise. Each active projection is continuous
// for the product distance, which controls it uniformly
// (CountableProductProjectionUniform), so the identity is continuous into
// the product topology (product_topology.IndexedContinuousIff): every
// product-open set is open for the product distance. Conversely, about a
// point f of a metric-open set lies a ball of some radius r inside it; the
// cylinders over the factor balls of radius r/2 about the coordinates of f
// that h takes up to the place CountableProductHeadBound gives for r/2 are
// finitely many open sets, and their intersection is a product-open
// neighbourhood of f inside the ball.
var CountableProductMetricTopology = countableProductMetricTopologyThm{family.Add(registry.ProofEntry{
	Name: "CountableProductMetricTopology",
	Key:  "prop_d0af4efef08593b0",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀X:(I → set(A)). ∀d:(I → A → A → real). ∀h:(num → I).",
		Hypotheses: []string{
			"J ⊆ image(h, 𝕌)",
			"∀i:I. i ∈ J ⇒ metric_space(X(i), d(i))",
		},
		Conclusion: "«DistanceTopology» = «ProductTopology»",
		Abbrev: Abbrev{
			{Name: "DistanceTopology", Text: "metric_topology(indexed_functions(J, z, X), " +
				"    countable_product_metric(J, d, h))"},
			{Name: "ProductTopology", Text: "indexed_product_topology(J, " +
				"    z, " +
				"    λi:I. metric_topology(X(i), d(i)))"},
		},
	},
		func(
			a *Argument,
			J *Expr[Set[I]],
			z *Arrow[I, A],
			X *Arrow[I, Set[A]],
			d *Expr[Fun3[I, A, A, Real]],
			h *Arrow[Nat, I],
			cover, factors Fact,
		) {
			C := a.TermAs[Set[Fun[I, A]]]("indexed_functions(J, z, X)")
			D := a.TermAs[Fun2[Fun[I, A], Fun[I, A], Real]]("countable_product_metric(J, d, h)")
			M := a.TermAs[Set[Set[Fun[I, A]]]]("«DistanceTopology»")
			P := a.TermAs[Set[Set[Fun[I, A]]]]("«ProductTopology»")
			factorTopologies := a.TermAs[Fun[I, Set[Set[A]]]]("λi:I. metric_topology(X(i), d(i))")
			identity := a.TermAs[Fun[Fun[I, A], Fun[I, A]]]("λf:(I → A). f")
			carrierNormalization := a.Have(
				"factor metric topologies have their stated carriers",
				"indexed_functions(J, z, λi:I. ⋃metric_topology(X(i), d(i))) = indexed_functions(J, z, X)",
				Simp(Fwd(MetricTopologySpace)),
				Basic())
			productData := a.Have(
				"the indexed product is a topology on the normalized product carrier",
				"⋃«ProductTopology» = indexed_functions(J, z, X) ∧ is_topology(«ProductTopology»)",
				SplitConj(
					Case(
						"the product carrier is the product of the factor carriers",
						By(carrierNormalization, product_topology.IndexedProductCarrier.At(J, z, factorTopologies))),
					Case(
						"the product topology is generated on its carrier",
						By(product_topology.IndexedProductTopology.At(J, z, factorTopologies))),
				))
			continuousProjections := a.Have(
				"each active coordinate projection is continuous for the product distance",
				"∀i:I. i ∈ J ⇒ continuous_map(«DistanceTopology», metric_topology(X(i), d(i)), λf:(I → A). f(i))",
				Derive(func(b *Argument) {
					i := b.FixAs[I]()
					active := b.Assume()
					taken := b.Have(
						"h takes the index i",
						"i ∈ image(h, 𝕌)",
						BySets(cover, active))
					uniform := b.Have(
						"the product distance controls the coordinate i uniformly",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃δ:real. " +
								"    &0 < δ ∧ ∀f g:(I → A). countable_product_metric(J, d, h, f, g) < δ ⇒ d(i, f(i), g(i)) < ε",
						},
						By(taken, active, CountableProductProjectionUniform))
					b.Show(
						"the projection maps the product into the factor and satisfies the ε-δ condition",
						By(
							factors.At(i),
							active,
							uniform,
							At(indexed_functions.IndexedFunctionsCoordinate, J, z, X, i),
							ContinuousMapIff.At(
								C,
								D,
								b.TermAs[Set[A]]("X(i)"),
								b.TermAs[Fun2[A, A, Real]]("d(i)"),
								b.TermAs[Fun[Fun[I, A], A]]("λf:(I → A). f(i)"))))
				}))
			identityContinuous := a.Have(
				"continuous projections make the identity into the product continuous",
				"continuous_map(«DistanceTopology», «ProductTopology», λf:(I → A). f)",
				By(
					continuousProjections,
					carrierNormalization,
					MetricTopology.Inst[Fun[I, A]]().At(C, D),
					MetricTopologySpace.Inst[Fun[I, A]]().At(C, D),
					product_topology.IndexedContinuousIff.At(J, z, factorTopologies, M, identity)))
			productInMetric := a.Have(
				"every product-open set is open for the product distance",
				"«ProductTopology» ⊆ «DistanceTopology»",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(set_basic.SubsetDef)))
					b.FixAs[Set[Fun[I, A]]]("u")
					open := b.Assume()
					trace := b.Have(
						"the identity preimage of a product-open set is itself",
						"preimage_on(indexed_functions(J, z, X), λf:(I → A). f, u) = u",
						BySets(productData, open))
					b.Show(
						"continuity of the identity makes that preimage metric-open",
						By(
							trace,
							open,
							identityContinuous,
							continuous.ContinuousMap.At(M, P, identity),
							MetricTopologySpace.Inst[Fun[I, A]]().At(C, D)))
				}))
			neighborhood := a.Have(
				"every positive ball about a point of the product holds a product-open neighborhood of its center",
				Statement{
					Binders: "∀f:(I → A). ∀r:real.",
					Hypotheses: []string{
						"f ∈ indexed_functions(J, z, X)",
						"&0 < r",
					},
					Conclusion: "∃V:set(I → A). " +
						"    V ∈ «ProductTopology» ∧ " +
						"    f ∈ V ∧ " +
						"    V ⊆ ball(indexed_functions(J, z, X), countable_product_metric(J, d, h), f, r)",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[Fun[I, A]]()
					r := b.FixAs[Real]()
					center := b.Assume()
					halfPositive := b.Have(
						"half the radius is positive",
						"&0 < r / &2",
						ByArith(center))
					N, head := b.ObtainAs[Nat](
						"the coordinates h takes up to some place N control the product distance to within half the radius",
						"∃N:num. ∀u v:(I → A). "+
							"    (∀n:num. n ≤ N ∧ h(n) ∈ J ⇒ d(h(n), u(h(n)), v(h(n))) < r / &2) ⇒ "+
							"    countable_product_metric(J, d, h, u, v) ≤ r / &2",
						By(halfPositive, CountableProductHeadBound.At(J, d, h, b.TermAs[Real]("r / &2"))))
					B, Bdef := b.LetAs[Fun[Nat, Set[Fun[I, A]]]](
						"B",
						"λn:num. "+
							"    {g:(I → A) | "+
							"        g ∈ indexed_functions(J, z, X) ∧ (h(n) ∈ J ⇒ d(h(n), f(h(n)), g(h(n))) < r / &2)}")
					cylinders := b.Have(
						"each coordinate restriction is a product-open neighborhood of the center",
						"∀n:num. B(n) ∈ «ProductTopology» ∧ f ∈ B(n)",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]()
							c.Cases(c.TermAs[Bool]("h(n) ∈ J"))
							c.When(
								"an active restriction is the cylinder over a factor ball",
								func(e *Argument, active Fact) {
									factorSpace := e.TermAs[Set[A]]("X(h(n))")
									factorDistance := e.TermAs[Fun2[A, A, Real]]("d(h(n))")
									centerCoordinate := e.TermAs[A]("f(h(n))")
									halfRadius := e.TermAs[Real]("r / &2")
									factorData := e.Have(
										"the factor metric is based at the center coordinate",
										"metric_space(X(h(n)), d(h(n))) ∧ f(h(n)) ∈ X(h(n))",
										By(
											factors.At(h.Apply(n)),
											active,
											center,
											indexed_functions.IndexedFunctionsCoordinate.At(J, z, X, h.Apply(n), f)))
									cylinder := e.Have(
										"the coordinate restriction is precisely the normalized factor-ball cylinder",
										"B(n) = "+
											"{g:(I → A) | "+
											"    g ∈ indexed_functions(J, z, λi:I. ⋃metric_topology(X(i), d(i))) ∧ "+
											"    g(h(n)) ∈ ball(X(h(n)), d(h(n)), f(h(n)), r / &2)}",
										Simp(Fwd(set_basic.Extension)),
										Derive(func(q *Argument) {
											g := q.FixAs[Fun[I, A]]("g")
											q.Do(Bdef.Rw(), carrierNormalization.Rw(), Simp(Fwd(BallDef)))
											q.Show(
												"membership in the ball is the coordinate inequality",
												BySets(active, indexed_functions.IndexedFunctionsCoordinate.At(J, z, X, h.Apply(n), g)))
										}))
									e.Do(SplitConj(
										Case(
											"the factor ball gives an open cylinder",
											By(
												cylinder,
												active,
												factorData,
												BallOpen.At(factorSpace, factorDistance, centerCoordinate, halfRadius),
												product_topology.IndexedCylinderOpen.At(
													J, z, factorTopologies, h.Apply(n), e.TermAs[Set[A]]("ball(X(h(n)), d(h(n)), f(h(n)), r / &2)")))),
										Case(
											"the center lies in the cylinder",
											BySets(
												cylinder,
												carrierNormalization,
												factorData,
												center,
												halfPositive,
												CentreInBall.At(factorSpace, factorDistance, centerCoordinate, halfRadius))),
									))
								})
							c.Otherwise(
								"an inactive restriction is the entire product carrier",
								func(e *Argument, inactive Fact) {
									whole := e.Have(
										"the inactive condition imposes no restriction",
										"B(n) = indexed_functions(J, z, X)",
										BySets(inactive, Bdef))
									e.Show(
										"the whole carrier is product-open and holds the center",
										By(whole, center, productData, topological_space.SpaceOpen.Inst[Fun[I, A]]().At(P)))
								})
						}))
					F, Fdef := b.LetAs[Set[Set[Fun[I, A]]]]("F", "image(B, 0 .. N)")
					V, Vdef := b.LetAs[Set[Fun[I, A]]]("V", "⋂F")
					finiteFamily := b.Have(
						"the finite nonempty family consists of product neighborhoods of the center",
						"finite(F) ∧ F ≠ ∅ ∧ F ⊆ «ProductTopology» ∧ f ∈ V",
						Derive(func(c *Argument) {
							c.Do(Vdef.Rw(), Fdef.Rw())
							first := c.Have(
								"the family contains the zeroth coordinate neighborhood",
								"B(0) ∈ image(B, 0 .. N)",
								BySets(nat_order.ZeroLessEq.At(N), num_segment.MembershipFromZero.At(c.TermAs[Nat]("0"), N)))
							finite := c.Have(
								"the image of the initial segment is finite",
								"finite(image(B, 0 .. N))",
								By(
									num_segment.Finite.At(c.TermAs[Nat]("0"), N),
									finite_set.FiniteImage.At(B, c.TermAs[Set[Nat]]("0 .. N"))))
							nonempty := c.Have(
								"the zeroth neighborhood makes the family nonempty",
								"image(B, 0 .. N) ≠ ∅",
								BySets(first))
							subset := c.Have(
								"every image member is product-open",
								"image(B, 0 .. N) ⊆ «ProductTopology»",
								By(cylinders, set_image.ImageSubsetIff.At(B, c.TermAs[Set[Nat]]("0 .. N"), P)))
							centerInside := c.Have(
								"the center lies in the intersection",
								"f ∈ ⋂image(B, 0 .. N)",
								BySets(cylinders))
							c.Show(
								"the family is finite, nonempty and consists of neighborhoods",
								By(finite, nonempty, subset, centerInside))
						}))
					open := b.Have(
						"their finite intersection is product-open",
						"V ∈ «ProductTopology»",
						By(Vdef, productData, finiteFamily, topological_space.IntersOpen.Inst[Fun[I, A]]().At(P, F)))
					pointBounds := b.Have(
						"a point of the intersection is a point of the product within "+
							"half the radius at the active coordinates taken up to N",
						Statement{
							Binders: "∀g:(I → A).",
							Hypotheses: []string{
								"g ∈ V",
							},
							Conclusion: "g ∈ indexed_functions(J, z, X) ∧ " +
								"(∀n:num. n ≤ N ∧ h(n) ∈ J ⇒ d(h(n), f(h(n)), g(h(n))) < r / &2)",
						},
						Derive(func(c *Argument) {
							c.FixAs[Fun[I, A]]()
							inside := c.Assume()
							cylindersAbout := c.Have(
								"a point of the intersection lies in each of the finitely many cylinders",
								"∀n:num. n ≤ N ⇒ g ∈ B(n)",
								Derive(func(e *Argument) {
									n := e.FixAs[Nat]()
									inHead := e.Assume()
									e.Show(
										"membership in the intersection applies to this image member",
										BySets(Vdef, Fdef, inside, inHead, num_segment.MembershipFromZero.At(n, N)))
								}))
							c.Do(SplitConj(
								Case(
									"the zeroth cylinder makes it a point of the product",
									BySets(cylindersAbout, Bdef, nat_order.ZeroLessEq.At(N))),
								Case(
									"the cylinders up to N bound its coordinates",
									BySets(cylindersAbout, Bdef)),
							))
						}))
					b.Take(V)
					b.Do(SplitConjAll(
						Case(
							"the finite intersection is open",
							By(open)),
						Case(
							"the center belongs to the intersection",
							By(finiteFamily)),
						Case(
							"the intersection lies in the ball",
							Derive(func(c *Argument) {
								c.Do(Simp(Fwd(set_basic.SubsetDef)))
								g := c.FixAs[Fun[I, A]]("g")
								inside := c.Assume()
								near := c.Have(
									"the product distance from the center is at most half the radius",
									"countable_product_metric(J, d, h, f, g) ≤ r / &2",
									By(head.At(f, g), pointBounds.At(g), inside))
								strict := c.Have(
									"so it is below the radius",
									"countable_product_metric(J, d, h, f, g) < r",
									ByArith(near, center))
								c.Show(
									"product membership and the distance inequality give ball membership",
									BySets(pointBounds.At(g), inside, strict, BallDef.Inst[Fun[I, A]]().At(C, D, f, r)))
							})),
					))
				}))
			metricInProduct := a.Have(
				"every set open for the product distance is product-open",
				"«DistanceTopology» ⊆ «ProductTopology»",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(set_basic.SubsetDef)))
					u := b.FixAs[Set[Fun[I, A]]]("u")
					open := b.Assume()
					local := b.Have(
						"each point has a product-open neighborhood contained in the set",
						"∀f:(I → A). f ∈ u ⇒ ∃V:set(I → A). V ∈ «ProductTopology» ∧ V ⊆ u ∧ f ∈ V",
						Derive(func(c *Argument) {
							f := c.FixAs[Fun[I, A]]()
							inside := c.Assume()
							r, ball := c.ObtainAs[Real](
								"openness for the product distance supplies a positive ball about this point",
								"∃r:real. "+
									"    &0 < r ∧ "+
									"    f ∈ indexed_functions(J, z, X) ∧ "+
									"    ball(indexed_functions(J, z, X), countable_product_metric(J, d, h), f, r) ⊆ u",
								BySets(inside, open, OpenIff.Inst[Fun[I, A]]().At(C, D, u)))
							c.Show(
								"the product neighborhood inside the ball lies in the set",
								BySets(neighborhood.At(f, r), ball))
						}))
					b.Show(
						"a set with a product-open neighborhood at each point is open",
						By(productData, local, topological_space.OpenPointwise.Inst[Fun[I, A]]().At(P, u)))
				}))
			a.Show(
				"the two topologies contain each other",
				By(productInMetric, metricInProduct, set_order.SubsetAntisym.Inst[Set[Fun[I, A]]]().At(M, P)))
		}),
})}
