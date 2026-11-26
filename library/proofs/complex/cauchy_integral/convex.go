// convex.go — Cauchy's theorem on a convex open set. A disc is convex, and
// so connected, and a convex set holds every triangle whose vertices it
// holds; the integral of f
// along a segment differs from f(z) times the step by at most the step times
// f's distance from f(z) along it. So for f continuous on a convex open set
// and holomorphic there except at one point, the integral from a fixed point
// along segments is a primitive: by Goursat with an exceptional point its
// increment from z to w is the integral along the segment from z to w.
// Through the primitive the integral round every closed path in the set is
// zero.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/registry"
)

// TriangleInConvex — a convex set holds every triangle whose vertices it
// holds. The point at coordinates (σ, τ) along the sides from a is a when
// σ + τ is 0; otherwise it is the point at time σ + τ of the segment from a to
// the point q at time τ/(σ + τ) of the side from b to c, and q lies in the set
// as b and c do, and then so does the point, as a and q do.
var TriangleInConvex = triangleInConvexThm{family.Add(registry.ProofEntry{
	Name: "TriangleInConvex",
	Key:  "prop_ecb75bb295d73d1a",
	Build: family.Theorem(Statement{
		Binders: "∀K:set(complex). ∀a b c:complex.",
		Hypotheses: []string{
			"«convex»(K)",
			"a ∈ K",
			"b ∈ K",
			"c ∈ K",
		},
		Conclusion: "«triangle»(a, b, c) ⊆ K",
	},
		func(arg *Argument, K *Expr[Set[Complex]], a, b, c *Expr[Complex], convex, aIn, bIn, cIn Fact) {
			arg.Show(
				"every point of the triangle lies in K",
				Unfold(set_basic.SubsetDef),
				Derive(func(d *Argument) {
					d.FixAs[Complex]("x")
					inside := d.Assume()
					σ, τ, at := d.Unpack2As[Real, Real](inside, "σ", "τ")
					coordinates := d.Conjuncts(
						at,
						"σ is at least 0",
						"τ is at least 0",
						"σ + τ is at most 1",
						"x is the point at (σ, τ) along the sides from a")
					d.Cases(d.Term("σ + τ = &0"))
					d.When(
						"if σ + τ is 0, x is a",
						func(e *Argument, vanish Fact) {
							zeros := e.Conjuncts(
								e.Have(
									"σ and τ are 0",
									"σ = &0 ∧ τ = &0",
									ByArith(coordinates[0], coordinates[1], vanish)),
								"σ is 0",
								"τ is 0")
							point := e.Have(
								"so x is a",
								"x = a",
								coordinates[3].Rw(),
								zeros[0].Rw(),
								zeros[1].Rw(),
								ByArith())
							e.Show(
								"which lies in K",
								point.Rw(),
								By(aIn))
						})
					d.Otherwise(
						"otherwise x lies on the segment from a to a point q of the side from b to c",
						func(e *Argument, positive Fact) {
							sum := e.TermAs[Real]("σ + τ")
							time := e.TermAs[Real]("τ / (σ + τ)")
							ratio := e.Have(
								"τ/(σ + τ) and σ + τ lie in ⟦0, 1⟧, and (σ + τ)·(τ/(σ + τ)) is τ",
								"&0 ≤ τ / (σ + τ) ∧ τ / (σ + τ) ≤ &1 ∧ (σ + τ) * (τ / (σ + τ)) = τ ∧ &0 ≤ σ + τ ∧ σ + τ ≤ &1",
								ByArith(positive, coordinates[0], coordinates[1], coordinates[2]))
							qIn := e.Have(
								"the point q at time τ/(σ + τ) of the segment from b to c lies in K",
								"segment_path(b, c, τ / (σ + τ)) ∈ K",
								By(convex, bIn, cIn, ratio))
							casts := e.Conjuncts(
								e.Have(
									"read in ℂ, (σ + τ)·(τ/(σ + τ)) is τ and σ + τ is σ plus τ",
									"&(σ + τ) * &(τ / (σ + τ)) = &τ ∧ &(σ + τ) = &σ + &τ",
									By(ratio, complex_field.OfRealMul.At(sum, time), complex_field.OfRealAdd.At(σ, τ))),
								"(σ + τ)·(τ/(σ + τ)) is τ in ℂ",
								"σ + τ is σ plus τ in ℂ")
							point := e.Have(
								"x is the point at time σ + τ of the segment from a to q",
								"x = segment_path(a, segment_path(b, c, τ / (σ + τ)), σ + τ)",
								Simp(Fwd(path_integral.SegmentPathDef)),
								ByArith(
									coordinates[3],
									Scaled(e.TermAs[Complex]("c - b"), casts[0]),
									Scaled(e.TermAs[Complex]("b - a"), casts[1])))
							e.Show(
								"so x lies in K, as a and q do",
								point.Rw(),
								By(convex, aIn, qIn, ratio))
						})
				}))
		}),
})}

// DiscConvex — a disc is convex. The point at time t of the segment from z to
// w is c plus (1 − t)·(z − c) + t·(w − c), so at most (1 − t)·|z − c| +
// t·|w − c| from c; that is at most the larger of |z − c| and |w − c|, below
// R.
var DiscConvex = discConvexThm{family.Add(registry.ProofEntry{
	Name: "DiscConvex",
	Key:  "prop_a444dc10f3eba14a",
	Build: family.Theorem("∀c:complex. ∀R:real. «convex»(«disc»(c, R))",
		func(arg *Argument, c *Expr[Complex], R *Expr[Real]) {
			arg.Show(
				"a point of a segment between two points of the disc lies in the disc",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("z")
					d.FixAs[Complex]("w")
					t := d.FixAs[Real]("t")
					given := d.Assume()
					where := d.Conjuncts(
						given,
						"z lies in the disc",
						"so does w",
						"t is at least 0",
						"t is at most 1")
					inside := d.Have(
						"both are within R of c",
						"|z - c| < R ∧ |w - c| < R",
						By(where[0], where[1]))
					rest := d.TermAs[Real]("&1 - t")
					fromZ, fromW := d.TermAs[Complex]("z - c"), d.TermAs[Complex]("w - c")
					sizeZ, sizeW := d.TermAs[Real]("|z - c|"), d.TermAs[Real]("|w - c|")
					split := d.Have(
						"the point at time t, less c, is (1 − t)·(z − c) + t·(w − c)",
						"segment_path(z, w, t) - c = &(&1 - t) * (z - c) + &t * (w - c)",
						Simp(Fwd(path_integral.SegmentPathDef), Fwd(complex_field.OfRealSub)),
						ByArith())
					weights := d.Conjuncts(
						d.Have(
							"|1 − t| is 1 − t and |t| is t",
							"|&(&1 - t)| = &1 - t ∧ |&t| = t",
							ByArith(
								where[2],
								where[3],
								complex_abs.AbsOfNonnegReal.At(rest),
								complex_abs.AbsOfNonnegReal.At(t))),
						"|1 − t| is 1 − t",
						"|t| is t")
					bound := d.Have(
						"so the point is at most (1 − t)·|z − c| + t·|w − c| from c",
						"|segment_path(z, w, t) - c| ≤ (&1 - t) * |z - c| + t * |w - c|",
						split.Rw(),
						ByArith(
							complex_abs.AbsTriangle.At(
								d.TermAs[Complex]("&(&1 - t) * (z - c)"), d.TermAs[Complex]("&t * (w - c)")),
							complex_abs.AbsMul.At(d.TermAs[Complex]("&(&1 - t)"), fromZ),
							complex_abs.AbsMul.At(d.TermAs[Complex]("&t"), fromW),
							Scaled(sizeZ, weights[0]),
							Scaled(sizeW, weights[1])))
					near := d.Have(
						"which is below R",
						"|segment_path(z, w, t) - c| < R",
						Derive(func(e *Argument) {
							e.Cases(e.Term("|z - c| ≤ |w - c|"))
							e.When(
								"if w is the farther, the weights put the point at most |w − c| from c",
								func(g *Argument, farther Fact) {
									g.Show(
										"(1 − t)·|z − c| ≤ (1 − t)·|w − c|",
										ByArith(bound, inside, farther, where[3], real_order_ring.LessEqMulLeft.At(rest, sizeZ, sizeW)))
								})
							e.Otherwise(
								"otherwise at most |z − c| from c",
								func(g *Argument, nearer Fact) {
									g.Show(
										"t·|w − c| ≤ t·|z − c|",
										ByArith(bound, inside, nearer, where[2], real_order_ring.LessEqMulLeft.At(t, sizeW, sizeZ)))
								})
						}))
					d.Show(
						"so it lies in the disc",
						By(near))
				}))
		}),
})}

// DiscConnected — a disc is connected: a set open in the plane that holds
// each point of the disc it comes arbitrarily near, and holds one point q of
// the disc, holds every point w of it. Along the segment from q to w, inside
// the disc as the disc is convex, the times whose point lies in the set form
// an open set, and so do the times near which no point does; every time in
// ⟦0, 1⟧ is of one kind or the other, the set holding each point of the
// disc it comes near, and none is of both. Time 0 is of the first kind, so
// were w outside the set, time 1 would be of the second, and the two open
// sets would split ⟦0, 1⟧, which is connected.
var DiscConnected = discConnectedThm{family.Add(registry.ProofEntry{
	Name: "DiscConnected",
	Key:  "prop_b067d7b8a5cbe8bb",
	Build: family.Theorem(Statement{
		Binders: "∀c:complex. ∀R:real. ∀A:set(complex). ∀q w:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ A ⇒ ∃ρ:real. &0 < ρ ∧ ∀x:complex. |x - z| < ρ ⇒ x ∈ A",
			"∀z:complex. |z - c| < R ∧ (∀δ:real. &0 < δ ⇒ ∃x:complex. x ∈ A ∧ |x - z| < δ) ⇒ z ∈ A",
			"|q - c| < R",
			"q ∈ A",
			"|w - c| < R",
		},
		Conclusion: "w ∈ A",
		Abbrev: Abbrev{
			{Name: "I", Text: "{t:real | &0 ≤ t ∧ t ≤ &1}"},
			{Name: "U", Text: "{t:real | segment_path(q, w, t) ∈ A}"},
			{Name: "V", Text: "{t:real | ∃ε:real. &0 < ε ∧ ∀s:real. |s - t| < ε ⇒ segment_path(q, w, s) ∉ A}"},
		},
	},
		func(
			arg *Argument,
			c *Expr[Complex],
			R *Expr[Real],
			A *Expr[Set[Complex]],
			q, w *Expr[Complex],
			open, closedIn, qInside, qIn, wInside Fact,
		) {
			missing := arg.SupposeNot()
			gap := arg.TermAs[Complex]("w - q")
			slope := arg.TermAs[Real]("|w - q| + &1")
			slopePositive := arg.Have(
				"|w − q| + 1 is positive",
				"&0 < |w - q| + &1",
				ByArith(complex_abs.AbsNonneg.At(gap)))
			near := arg.Have(
				"points of the segment at times less than ε/(|w − q| + 1) apart lie less than ε apart",
				Statement{
					Binders: "∀t s ε:real.",
					Hypotheses: []string{
						"&0 < ε",
						"|t - s| < ε / (|w - q| + &1)",
					},
					Conclusion: "|segment_path(q, w, t) - segment_path(q, w, s)| < ε",
				},
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					s := d.FixAs[Real]("s")
					ε := d.FixAs[Real]("ε")
					given := d.Conjuncts(
						d.Assume(),
						"ε is positive",
						"t and s are less than ε/(|w − q| + 1) apart")
					difference := d.Have(
						"the two points differ by (t − s)·(w − q)",
						"segment_path(q, w, t) - segment_path(q, w, s) = (&t - &s) * (w - q)",
						Simp(Fwd(path_integral.SegmentPathDef)),
						ByArith())
					d.Show(
						"whose modulus |t − s|·|w − q| is at most |t − s|·(|w − q| + 1), below ε",
						difference.Rw(),
						ByArith(
							given[1],
							slopePositive,
							complex_abs.AbsMul.At(d.TermAs[Complex]("&t - &s"), gap),
							complex_abs.AbsOfRealSub.At(t, s),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("t - s")),
							real_order_field.LessThanDivMulLeft.At(d.TermAs[Real]("|t - s|"), ε, slope)))
				}))
			onSegment := arg.Have(
				"the segment from q to w lies in the disc, the disc being convex",
				"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ |segment_path(q, w, t) - c| < R",
				By(qInside, wInside, At(DiscConvex, c, R)))
			uOpen := arg.Have(
				"the times whose point lies in A form an open set, A being open",
				"«U» ∈ real_topology",
				Simp(Fwd(real_topology.OpenIff)),
				Derive(func(d *Argument) {
					d.FixAs[Real]("τ")
					in := d.Assume()
					point := d.TermAs[Complex]("segment_path(q, w, τ)")
					ρ, ball := d.UnpackAs[Real](GroupPremises(in, open.At(point)), "ρ")
					around := d.Conjuncts(
						ball,
						"ρ is positive",
						"A holds every point within ρ of the point at time τ")
					d.Take(d.TermAs[Real]("ρ / (|w - q| + &1)"))
					d.Show(
						"a time within ρ/(|w − q| + 1) of τ has its point within ρ of the point at τ, so in A",
						By(around[0], around[1], slopePositive, near, real_order_field.DivPos.At(ρ, slope)))
				}))
			vOpen := arg.Have(
				"the times near which no point lies in A form an open set",
				"«V» ∈ real_topology",
				Simp(Fwd(real_topology.OpenIff)),
				Derive(func(d *Argument) {
					d.FixAs[Real]("τ")
					in := d.Assume()
					_, clear := d.UnpackAs[Real](in, "ε")
					around := d.Conjuncts(
						clear,
						"ε is positive",
						"no time within ε of τ has its point in A")
					half := d.Have(
						"ε/2 is positive",
						"&0 < ε / &2",
						ByArith(around[0]))
					inner := d.Have(
						"each time t within ε/2 of τ is of the second kind, no time within ε/2 of t having its point in A",
						"∀t:real. |t - τ| < ε / &2 ⇒ ∃η:real. &0 < η ∧ (∀s:real. |s - t| < η ⇒ segment_path(q, w, s) ∉ A)",
						Derive(func(e *Argument) {
							e.FixAs[Real]("t")
							close := e.Assume()
							far := e.Have(
								"a time within ε/2 of t lies within ε of τ",
								"∀s:real. |s - t| < ε / &2 ⇒ |s - τ| < ε",
								e.ForEach(func(s *Expr[Real]) Action {
									return ByArith(close)
								}))
							e.Take(e.TermAs[Real]("ε / &2"))
							e.Show(
								"so its point lies outside A",
								By(half, far, around[1]))
						}))
					d.Take(d.TermAs[Real]("ε / &2"))
					d.Show(
						"so the times within ε/2 of τ are of the second kind",
						BySets(half, inner))
				}))
			covered := arg.Have(
				"every time in ⟦0, 1⟧ is of one kind or the other",
				"∀τ:real. τ ∈ «I» ⇒ τ ∈ «U» ∨ τ ∈ «V»",
				Derive(func(d *Argument) {
					τ := d.FixAs[Real]("τ")
					within := d.Assume()
					point := d.TermAs[Complex]("segment_path(q, w, τ)")
					d.Cases(d.TermAs[Bool]("segment_path(q, w, τ) ∈ A"))
					d.When(
						"a time whose point lies in A is of the first kind",
						func(b *Argument, inA Fact) {
							b.Show(
								"τ lies in U",
								BySets(inA))
						})
					d.Otherwise(
						"a time whose point lies outside A has no time near it whose point lies in A",
						func(b *Argument, outside Fact) {
							notV := b.SupposeNot()
							approached := b.Have(
								"else A comes arbitrarily near the point at time τ",
								"∀δ:real. &0 < δ ⇒ ∃x:complex. x ∈ A ∧ |x - segment_path(q, w, τ)| < δ",
								Derive(func(e *Argument) {
									δ := e.FixAs[Real]("δ")
									positive := e.Assume()
									s, found := e.ObtainAs[Real](
										"some time within δ/(|w − q| + 1) of τ has its point in A, τ not being of the second kind",
										"∃s:real. |s - τ| < δ / (|w - q| + &1) ∧ segment_path(q, w, s) ∈ A",
										By(notV, positive, slopePositive, real_order_field.DivPos.At(δ, slope)),
										Named("s"))
									e.Take(e.TermAs[Complex]("segment_path(q, w, s)"))
									e.Show(
										"that point lies in A, within δ of the point at time τ",
										By(found, positive, near.At(s, τ, δ)))
								}))
							b.Show(
								"so A holds the point at time τ, which lies in the disc",
								By(outside, approached, GroupPremises(within, onSegment.At(τ)), closedIn.At(point)))
						})
				}))
			exclusive := arg.Have(
				"no time is of both kinds: a time of the second kind "+
					"lies within ε of itself, so its point lies outside A",
				Statement{
					Binders: "∀τ ε:real.",
					Hypotheses: []string{
						"&0 < ε",
						"∀s:real. |s - τ| < ε ⇒ segment_path(q, w, s) ∉ A",
					},
					Conclusion: "segment_path(q, w, τ) ∉ A",
				},
				Derive(func(d *Argument) {
					τ := d.FixAs[Real]("τ")
					d.FixAs[Real]("ε")
					given := d.Conjuncts(
						d.Assume(),
						"ε is positive",
						"no time within ε of τ has its point in A")
					d.Show(
						"|τ − τ| = 0 < ε",
						ByArith(given[0], given[1].At(τ)))
				}))
			apart := arg.Have(
				"so the two kinds do not meet on ⟦0, 1⟧",
				"«I» ∩ «U» ∩ «V» = ∅",
				BySets(exclusive))
			ends := arg.Conjuncts(
				arg.Have(
					"the segment runs from q at time 0 to w at time 1, both times lying in ⟦0, 1⟧",
					"segment_path(q, w, &0) = q ∧ segment_path(q, w, &1) = w ∧ &0 ≤ &0 ∧ &0 ≤ &1 ∧ &1 ≤ &1",
					Simp(Fwd(path_integral.SegmentPathDef)),
					ByArith()),
				"the point at time 0 is q",
				"the point at time 1 is w",
				"0 is at least 0",
				"0 is at most 1",
				"1 is at most 1")
			atZero := arg.Have(
				"so the point at time 0 lies in A",
				"segment_path(q, w, &0) ∈ A",
				ends[0].Rw(),
				By(qIn))
			atOne := arg.Have(
				"and the point at time 1 does not",
				"segment_path(q, w, &1) ∉ A",
				ends[1].Rw(),
				By(missing))
			cover := arg.Have(
				"so the two kinds cover ⟦0, 1⟧",
				"«I» ⊆ «U» ∪ «V»",
				BySets(covered))
			meetsU := arg.Have(
				"time 0 lies in ⟦0, 1⟧ and is of the first kind",
				"«I» ∩ «U» ≠ ∅",
				BySets(ends[2], ends[3], atZero))
			meetsV := arg.Have(
				"time 1 lies in ⟦0, 1⟧ and is not of the first kind, so it is of the second",
				"«I» ∩ «V» ≠ ∅",
				BySets(ends[3], ends[4], atOne, covered))
			interval := arg.Have(
				"⟦0, 1⟧ is an interval: a real between two of its points lies between 0 and 1",
				"real_interval(«I»)",
				Unfold(real_topology.RealIntervalDef),
				Derive(func(d *Argument) {
					d.FixAs[Real]("x")
					d.FixAs[Real]("y")
					d.FixAs[Real]("z")
					d.Show(
						"0 ≤ x ≤ y ≤ z ≤ 1",
						ByArith(Normalized))
				}))
			parts := arg.Conjuncts(
				arg.Unfolded(
					GroupPremises(interval, real_topology.IntervalConnected.At(arg.TermAs[Set[Real]]("«I»"))),
					connected.ConnectedInDef),
				"⟦0, 1⟧ lies in the line",
				"two open sets covering it, each meeting it, meet on it")
			arg.Show(
				"so the times of the first kind and those of the second, "+
					"covering ⟦0, 1⟧ and each meeting it, would meet on it",
				By(
					uOpen,
					vOpen,
					cover,
					meetsU,
					meetsV,
					apart,
					parts[1].At(arg.TermAs[Set[Real]]("«U»"), arg.TermAs[Set[Real]]("«V»"))))
		}),
})}

// SegmentIntegralDeviation — along a segment from z to w where f is
// continuous and within M of f(z), the integral of f is within M·|w − z| of
// f(z)·(w − z). The constant f(z) has primitive f(z)·u, so its integral is
// f(z)·(w − z); the integral of f minus it is that of f − f(z), at most
// M·|w − z| by the estimate along a segment.
var SegmentIntegralDeviation = segmentIntegralDeviationThm{family.Add(registry.ProofEntry{
	Name: "SegmentIntegralDeviation",
	Key:  "prop_643f60fea6ca578e",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀z w:complex. ∀M:real.",
		Hypotheses: []string{
			"∀t:real. " +
				"    &0 ≤ t ∧ t ≤ &1 ⇒ " +
				"    complex_continuous_at(f, segment_path(z, w, t)) ∧ |f(segment_path(z, w, t)) - f(z)| ≤ M",
		},
		Conclusion: "|«segInt»(f, z, w) - f(z) * (w - z)| ≤ M * |w - z|",
	},
		func(arg *Argument, f *Arrow[Complex, Complex], z, w *Expr[Complex], M *Expr[Real], near Fact) {
			value := arg.TermAs[Complex]("f(z)")
			one := arg.TermAs[Complex]("&1")
			identity := arg.TermAs[Fun[Complex, Complex]]("λu:complex. u")
			constant := arg.TermAs[Fun[Complex, Complex]]("λu:complex. f(z)")
			unit := arg.Have(
				"f(z)·1 is f(z)",
				"f(z) * &1 = f(z)",
				ByArith())
			slope := arg.Have(
				"f(z)·u has derivative f(z) at every point",
				"∀v:complex. complex_derivative_at(λu:complex. f(z) * u, v, f(z))",
				arg.ForEach(func(v *Expr[Complex]) Action {
					return By(
						Normalized,
						unit,
						complex_derivative.DerivativeId.At(v),
						complex_derivative.DerivativeScale.At(identity, v, one, value))
				}))
			flat := arg.Have(
				"the constant f(z) is continuous everywhere",
				"∀v:complex. complex_continuous_at(λu:complex. f(z), v)",
				arg.ForEach(func(v *Expr[Complex]) Action {
					return By(complex_topology.ContinuousAtConst.At(v, value))
				}))
			continuousAlong := arg.Have(
				"f is continuous along the segment",
				"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
				By(near))
			constantIntegral := arg.Have(
				"so the integral of the constant f(z) along the segment is f(z)·w − f(z)·z",
				"«segInt»(λu:complex. f(z), z, w) = f(z) * w - f(z) * z",
				By(
					slope,
					flat,
					SegmentIntegralPrimitive.At(
						arg.TermAs[Fun[Complex, Complex]]("λu:complex. f(z) * u"), constant, z, w)))
			difference := arg.Have(
				"f − f(z) is continuous along the segment and at most M there",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"&0 ≤ t",
						"t ≤ &1",
					},
					Conclusion: "complex_continuous_at(λu:complex. f(u) - f(z), segment_path(z, w, t)) ∧ " +
						"|f(segment_path(z, w, t)) - f(z)| ≤ M",
				},
				Derive(func(d *Argument) {
					t := d.FixAs[Real]("t")
					inUnit := d.Assume()
					point := d.TermAs[Complex]("segment_path(z, w, t)")
					here := d.Conjuncts(
						GroupPremises(inUnit, near.At(t)),
						"f is continuous at the point at time t",
						"and within M of f(z) there")
					d.Show(
						"a difference of continuous functions is continuous",
						By(
							here[0],
							here[1],
							complex_topology.ContinuousAtConst.At(point, value),
							complex_topology.ContinuousAtSub.At(f, constant, point)))
				}))
			rewritten := arg.Have(
				"the integral of f less f(z)·(w − z) is the integral of f − f(z)",
				"«segInt»(f, z, w) - f(z) * (w - z) = «segInt»(λu:complex. f(u) - f(z), z, w)",
				ByArith(continuousAlong, flat, constantIntegral, SegmentIntegralSub.At(f, constant, z, w)))
			arg.Show(
				"which is at most M·|w − z| by the estimate along a segment",
				rewritten.Rw(),
				By(
					difference,
					SegmentIntegralBound.At(arg.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) - f(z)"), z, w, M)))
		}),
})}

// ConvexPrimitive — a function continuous on a convex open set s and
// holomorphic there except at one point p has a primitive on s. With s empty
// any function will do. Otherwise fix a in s and let F(z) be the integral of
// f along the segment from a to z. For z in s, s holds a disc of radius r about
// z, and f is within ε/2 of f(z) within δ of z. For w within min(r, δ) of z
// the triangle a z w lies in s, so by Goursat with an exceptional point its
// boundary integral is 0 and F(w) − F(z) is the integral along the segment
// from z to w, within ε/2·|w − z| of f(z)·(w − z): F has derivative f(z).
var ConvexPrimitive = convexPrimitiveThm{family.Add(registry.ProofEntry{
	Name: "ConvexPrimitive",
	Key:  "prop_3989c17631fbc034",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex). ∀p:complex.",
		Hypotheses: []string{
			"s ∈ complex_topology",
			"«convex»(s)",
			"complex_continuous_on(s, f)",
			"holomorphic_on(s ∖ {p}, f)",
		},
		Conclusion: "∃F:complex → complex. ∀z:complex. z ∈ s ⇒ complex_derivative_at(F, z, f(z))",
	},
		func(
			arg *Argument,
			s *Expr[Set[Complex]],
			f *Arrow[Complex, Complex],
			p *Expr[Complex],
			open, convex, continuousOn, holomorphic Fact,
		) {
			zero := arg.TermAs[Real]("&0")
			punctured := arg.TermAs[Set[Complex]]("s ∖ {p}")
			continuous := arg.Have(
				"s being open, f is continuous at each of its points",
				"∀z:complex. z ∈ s ⇒ complex_continuous_at(f, z)",
				By(open, continuousOn, complex_topology.ContinuousOnOpenIff.At(s, f)))
			along := arg.Have(
				"f is continuous along a segment between two points of s, s being convex",
				Statement{
					Binders: "∀z w:complex.",
					Hypotheses: []string{
						"z ∈ s",
						"w ∈ s",
					},
					Conclusion: "∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
				},
				By(convex, continuous, At(ContinuousAlongSegment, s, f)))
			arg.Cases(arg.Term("∃a:complex. a ∈ s"))
			arg.When(
				"if s has a point a, integrate along the segments from a",
				func(d *Argument, nonempty Fact) {
					a, aIn := d.UnpackAs[Complex](nonempty, "a")
					primitive := d.TermAs[Fun[Complex, Complex]]("λz:complex. «segInt»(f, a, z)")
					d.Take(primitive)
					d.Show(
						"F has derivative f(z) at each point z of s",
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("z")
							zIn := e.Assume()
							r, ball := e.ObtainAs[Real](
								"s holds a disc of radius r about z",
								"∃r:real. &0 < r ∧ ∀w:complex. |w - z| < r ⇒ w ∈ s",
								By(open, zIn, complex_topology.ComplexOpenIff.At(s)))
							disc := e.Conjuncts(
								ball,
								"r is positive",
								"the disc of radius r about z lies in s")
							atZ := e.Have(
								"f is continuous at z",
								"complex_continuous_at(f, z)",
								By(zIn, continuous))
							nearZ := e.Unfolded(atZ, complex_topology.ComplexContinuousAtDef)
							increments := e.Have(
								"for every ε > 0, near z the increment of F is within ε·|w − z| of f(z)·(w − z)",
								Statement{
									Binders: "∀ε:real.",
									Hypotheses: []string{
										"&0 < ε",
									},
									Conclusion: "∃δ:real. " +
										"    &0 < δ ∧ " +
										"    ∀w:complex. " +
										"        &0 < |w - z| ∧ |w - z| < δ ⇒ " +
										"        |«segInt»(f, a, w) - «segInt»(f, a, z) - f(z) * (w - z)| < ε * |w - z|",
								},
								Derive(func(g *Argument) {
									g.FixAs[Real]("ε")
									positive := g.Assume()
									half := g.TermAs[Real]("ε / &2")
									halfPositive := g.Have(
										"ε/2 is positive",
										"&0 < ε / &2",
										ByArith(positive))
									δ, near := g.ObtainAs[Real](
										"within some δ of z, f is within ε/2 of f(z)",
										"∃δ:real. &0 < δ ∧ ∀w:complex. |w - z| < δ ⇒ |f(w) - f(z)| < ε / &2",
										By(halfPositive, nearZ.At(half)))
									close := g.Conjuncts(
										near,
										"δ is positive",
										"within δ of z, f is within ε/2 of f(z)")
									radius := g.TermAs[Real]("min(r, δ)")
									radiusPositive := g.Have(
										"min(r, δ) is positive",
										"&0 < min(r, δ)",
										By(disc[0], close[0], real_sup_inf.LessThanMin.At(r, δ, zero)))
									estimate := g.Have(
										"within min(r, δ) of z the increment of F is within ε·|w − z| of f(z)·(w − z)",
										Statement{
											Binders: "∀w:complex.",
											Hypotheses: []string{
												"&0 < |w - z|",
												"|w - z| < min(r, δ)",
											},
											Conclusion: "|«segInt»(f, a, w) - «segInt»(f, a, z) - f(z) * (w - z)| < ε * |w - z|",
										},
										Derive(func(h *Argument) {
											w := h.FixAs[Complex]("w")
											given := h.Assume()
											bounds := h.Conjuncts(
												given,
												"w is not z",
												"w is within min(r, δ) of z")
											distance := h.TermAs[Real]("|w - z|")
											within := h.Have(
												"w is within r and within δ of z",
												"|w - z| < r ∧ |w - z| < δ",
												By(bounds[1], real_sup_inf.LessThanMin.At(r, δ, distance)))
											wIn := h.Have(
												"so w lies in s",
												"w ∈ s",
												By(within, disc[1].At(w)))
											triangle := h.Have(
												"the triangle a z w lies in s, s being convex",
												"«triangle»(a, z, w) ⊆ s",
												By(convex, aIn, zIn, wIn, TriangleInConvex.At(s, a, z, w)))
											continuousThere := h.Have(
												"f is continuous on it",
												"∀u:complex. u ∈ «triangle»(a, z, w) ⇒ complex_continuous_at(f, u)",
												By(h.Unfolded(triangle, set_basic.SubsetDef), continuous))
											off := h.Have(
												"without p it lies in s without p",
												"«triangle»(a, z, w) ∖ {p} ⊆ s ∖ {p}",
												BySets(triangle))
											holomorphicThere := h.Have(
												"so f is holomorphic on it except at p",
												"holomorphic_on(«triangle»(a, z, w) ∖ {p}, f)",
												By(
													holomorphic,
													off,
													complex_derivative.HolomorphicOnSubset.At(
														punctured,
														h.TermAs[Set[Complex]]("«triangle»(a, z, w) ∖ {p}"),
														f)))
											round := h.Have(
												"by Goursat with an exceptional point the integral round it is 0",
												"«boundaryInt»(f, a, z, w) = &0",
												By(continuousThere, holomorphicThere, GoursatExceptPoint.At(f, a, z, w, p)))
											change := h.Have(
												"so F(w) − F(z) is the integral along the segment from z to w",
												"«segInt»(f, a, w) - «segInt»(f, a, z) - f(z) * (w - z) = «segInt»(f, z, w) - f(z) * (w - z)",
												ByArith(round, aIn, wIn, along.At(a, w), path_integral.SegmentReverse.At(f, a, w)))
											nearSegment := h.Have(
												"along the segment from z to w, f is continuous and within ε/2 of f(z)",
												Statement{
													Binders: "∀t:real.",
													Hypotheses: []string{
														"&0 ≤ t",
														"t ≤ &1",
													},
													Conclusion: "complex_continuous_at(f, segment_path(z, w, t)) ∧ " +
														"|f(segment_path(z, w, t)) - f(z)| ≤ ε / &2",
												},
												Derive(func(k *Argument) {
													t := k.FixAs[Real]("t")
													inUnit := k.Assume()
													times := k.Conjuncts(
														inUnit,
														"t is at least 0",
														"t is at most 1")
													point := k.TermAs[Complex]("segment_path(z, w, t)")
													offset := k.Have(
														"the point at time t is z plus t·(w − z)",
														"segment_path(z, w, t) - z = &t * (w - z)",
														Simp(Fwd(path_integral.SegmentPathDef)),
														ByArith())
													size := k.Have(
														"|t| is t",
														"|&t| = t",
														By(times[0], complex_abs.AbsOfNonnegReal.At(t)))
													step := k.Have(
														"it is t·|w − z| from z, so within δ",
														"|segment_path(z, w, t) - z| < δ",
														offset.Rw(),
														ByArith(
															within,
															times[1],
															complex_abs.AbsMul.At(k.TermAs[Complex]("&t"), k.TermAs[Complex]("w - z")),
															Scaled(distance, size),
															real_order_ring.LessEqMulLeft.At(distance, t, k.TermAs[Real]("&1")),
															complex_abs.AbsNonneg.At(k.TermAs[Complex]("w - z"))))
													there := k.Have(
														"f is continuous there, the segment lying in s",
														"complex_continuous_at(f, segment_path(z, w, t))",
														By(zIn, wIn, inUnit, along.At(z, w)))
													small := k.Have(
														"and f there is within ε/2 of f(z)",
														"|f(segment_path(z, w, t)) - f(z)| ≤ ε / &2",
														ByArith(step, close[1].At(point)))
													k.Show(
														"both hold at the point at time t",
														By(there, small))
												}))
											deviation := h.Have(
												"so the integral along it is within ε/2·|w − z| of f(z)·(w − z)",
												"|«segInt»(f, z, w) - f(z) * (w - z)| ≤ ε / &2 * |w - z|",
												By(nearSegment, SegmentIntegralDeviation.At(f, z, w, half)))
											h.Show(
												"and ε/2·|w − z| is below ε·|w − z|, w not being z",
												change.Rw(),
												ByArith(deviation, bounds[0], positive))
										}))
									g.Take(radius)
									g.Show(
										"min(r, δ) will do",
										By(radiusPositive, estimate))
								}))
							e.Show(
								"that is, F has derivative f(z) at z",
								By(increments, complex_derivative.DerivativeIncrement.At(primitive, z, e.TermAs[Complex]("f(z)"))))
						}))
				})
			arg.Otherwise(
				"if s is empty any function will do",
				func(d *Argument, empty Fact) {
					d.Take(d.TermAs[Fun[Complex, Complex]]("λz:complex. z"))
					d.Show(
						"s has no point to check",
						By(Normalized, empty))
				})
		}),
})}

// CauchyConvex — Cauchy's theorem on a convex open set: the integral of a
// function holomorphic on the set round a closed piecewise smooth path in it
// is zero. The function is continuous on the set and holomorphic off any
// point, so it has a primitive F there; the integral along the path is the
// change of F between its ends, which agree.
var CauchyConvex = cauchyConvexThm{family.Add(registry.ProofEntry{
	Name: "CauchyConvex",
	Key:  "prop_bd88f4fe83d5e140",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex). ∀γ γ':(real → complex). ∀a b:real.",
		Hypotheses: []string{
			"s ∈ complex_topology",
			"«convex»(s)",
			"holomorphic_on(s, f)",
			"«closedPathIn»(s, γ, γ', a, b)",
		},
		Conclusion: "path_integral(f, γ, γ', a, b) = &0",
	},
		func(
			arg *Argument,
			s *Expr[Set[Complex]],
			f *Arrow[Complex, Complex],
			γ, γPrime *Arrow[Real, Complex],
			a, b *Expr[Real],
			open, convex, holomorphic, closedPath Fact,
		) {
			loop := arg.Conjuncts(
				closedPath,
				"γ is a piecewise smooth path on ⟦a, b⟧",
				"it is closed",
				"it stays in s")
			path, closed, inside := loop[0], loop[1], loop[2]
			start := arg.TermAs[Complex]("γ(a)")
			continuousOn := arg.Have(
				"f is continuous on s, having a derivative at each of its points",
				"complex_continuous_on(s, f)",
				By(holomorphic, complex_derivative.HolomorphicOnContinuous.At(s, f)))
			minus := arg.Have(
				"s without γ(a) lies in s",
				"s ∖ {γ(a)} ⊆ s",
				BySets())
			off := arg.Have(
				"so f is holomorphic on s without γ(a)",
				"holomorphic_on(s ∖ {γ(a)}, f)",
				By(
					holomorphic,
					minus,
					complex_derivative.HolomorphicOnSubset.At(s, arg.TermAs[Set[Complex]]("s ∖ {γ(a)}"), f)))
			F, primitive := arg.ObtainAs[Fun[Complex, Complex]](
				"so f has a primitive F on s",
				"∃F:complex → complex. ∀z:complex. z ∈ s ⇒ complex_derivative_at(F, z, f(z))",
				By(open, convex, continuousOn, off, ConvexPrimitive.At(s, f, start)))
			continuous := arg.Have(
				"s being open, f is continuous at each of its points",
				"∀z:complex. z ∈ s ⇒ complex_continuous_at(f, z)",
				By(open, continuousOn, complex_topology.ContinuousOnOpenIff.At(s, f)))
			slopes := arg.Have(
				"along the path F has derivative f, the path lying in s",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_derivative_at(F, γ(t), f(γ(t)))",
				By(inside, primitive))
			alongPath := arg.Have(
				"and f is continuous along it",
				"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))",
				By(inside, continuous))
			change := arg.Have(
				"so the integral along the path is the change of F between its ends",
				"path_integral(f, γ, γ', a, b) = F(γ(b)) - F(γ(a))",
				By(path, slopes, alongPath, path_integral.PathIntegralPrimitive.At(F, f, γ, γPrime, a, b)))
			arg.Show(
				"and the ends agree",
				change.Rw(),
				closed.Rw(),
				ByArith())
		}),
})}
