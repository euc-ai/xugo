// metric.go — ℂ as a metric space: the modulus of the difference is a
// distance, and its open sets are a Hausdorff topology on the whole plane
// in which a set is open when each of its points has a disc about it
// inside the set; a disc, a punctured disc and a right half-plane are
// open, the points of a finite set other than p keep a positive distance
// from p, and an open set less finitely many points is open. A sequence
// converges for the distance exactly when it converges, and the plane is
// complete. Each topological fact is the metric chapter's theorem read at
// the instance.

package complex_topology

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/separation"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexMetric — the complex numbers with the distance |z − w| form a
// metric space on the whole plane. The modulus of a difference vanishes
// only where the difference does; |z − w| is |w − z|; and the triangle
// inequality of the modulus between three points bounds |x − z| by
// |x − y| + |y − z|.
var ComplexMetric = complexMetricThm{family.Add(registry.ProofEntry{
	Name: "ComplexMetric",
	Key:  "prop_cc9fe5f3c91942a1",
	Build: family.Instance(metric_space.MetricSpace, "metric_space(𝕌, complex_dist)",
		Case(
			"the distance vanishes exactly between equal numbers",
			Derive(func(a *Argument) {
				a.FixAs[Complex]("x")
				a.FixAs[Complex]("y")
				a.Assume()
				a.Do(Simp(Fwd(ComplexDistDef), Fwd(complex_abs.AbsEqZero)))
				a.Iff()
				a.Forward(
					"a zero difference makes the two numbers equal",
					func(b *Argument, zero Fact) {
						b.Show(
							"x is y",
							ByArith(zero))
					})
				a.Backward(
					"and equal numbers differ by zero",
					func(b *Argument, equal Fact) {
						b.Show(
							"x − y vanishes",
							ByArith(equal))
					})
			})),
		Case(
			"the distance reads the same both ways",
			Derive(func(a *Argument) {
				x := a.FixAs[Complex]("x")
				y := a.FixAs[Complex]("y")
				a.Assume()
				a.Show(
					"the modulus of x − y is that of y − x",
					Simp(Fwd(ComplexDistDef)),
					By(complex_abs.AbsSubComm.At(x, y)))
			})),
		Case(
			"the triangle inequality",
			Derive(func(a *Argument) {
				x := a.FixAs[Complex]("x")
				y := a.FixAs[Complex]("y")
				z := a.FixAs[Complex]("z")
				a.Assume()
				a.Show(
					"the triangle inequality of the modulus between the three points",
					Simp(Fwd(ComplexDistDef)),
					By(complex_abs.AbsSubTriangle.At(x, y, z)))
			})),
	),
})}

// ComplexBall — a ball of the distance is the set of complex numbers
// within its radius of its centre: the distance is |c − w|, which is
// |w − c|. Every reading of the plane's open sets in its own terms goes
// through it.
var ComplexBall = complexBallThm{family.Add(registry.ProofEntry{
	Name: "ComplexBall",
	Key:  "prop_4e3c0b88191e985e",
	Build: family.Theorem("∀c:complex. ∀r:real. ∀w:complex. "+
		"    w ∈ ball(𝕌, complex_dist, c, r) ⇔ |w - c| < r",
		func(a *Argument, c *Expr[Complex], r *Expr[Real], w *Expr[Complex]) {
			a.Show(
				"the ball holds the w with |c − w| < r, that is |w − c| < r",
				Simp(Fwd(metric_space.BallDef.Inst[Complex]()), Fwd(ComplexDistDef)),
				By(Normalized, complex_abs.AbsSubComm.At(c, w), set_basic.InUniv.At(w)))
		}),
})}

// ComplexTopology — the open sets of ℂ form a topology: the metric
// topology of any distance does.
var ComplexTopology = complexTopologyThm{family.Add(registry.ProofEntry{
	Name: "ComplexTopology",
	Key:  "prop_6b13b84f75b577dd",
	Build: family.Theorem("is_topology(complex_topology)",
		func(a *Argument) {
			a.Show(
				"the metric topology of any distance is a topology",
				Unfold(ComplexTopologyDef),
				By(metric_space.MetricTopology))
		}),
})}

// ComplexTopologySpace — the points of the topology are all of ℂ: the
// space of a metric topology is its carrier, here the whole plane.
var ComplexTopologySpace = complexTopologySpaceThm{family.Add(registry.ProofEntry{
	Name: "ComplexTopologySpace",
	Key:  "prop_9e59d25eb861849",
	Build: family.Theorem("⋃complex_topology = 𝕌",
		func(a *Argument) {
			a.Show(
				"the space of a metric topology is its carrier",
				Unfold(ComplexTopologyDef),
				By(metric_space.MetricTopologySpace))
		}),
})}

// ComplexOpenIff — a set of complex numbers is open exactly when each of
// its points has a radius about it inside the set: the metric chapter's
// reading of openness, every set of complex numbers lying in the plane and
// the ball about z being the points within r of z.
var ComplexOpenIff = complexOpenIffThm{family.Add(registry.ProofEntry{
	Name: "ComplexOpenIff",
	Key:  "prop_3cc527d7acc05ded",
	Build: family.Theorem(
		"∀u:set(complex). "+
			"    u ∈ complex_topology ⇔ ∀z:complex. z ∈ u ⇒ ∃r:real. &0 < r ∧ ∀w:complex. |w - z| < r ⇒ w ∈ u",
		func(a *Argument, u *Expr[Set[Complex]]) {
			a.Show(
				"open for the distance, read in the plane, is the radius condition",
				Unfold(ComplexTopologyDef),
				Simp(Fwd(metric_space.OpenIff.Inst[Complex]()), Fwd(set_order.SubsetUniv.Inst[Complex]())),
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(ComplexBall)),
				TrivialNormalized())
		}),
})}

// DiscOpen — the complex numbers within r of c form an open set: they
// are the ball of the distance about c, and a ball about a point of a
// metric space is open.
var DiscOpen = discOpenThm{family.Add(registry.ProofEntry{
	Name: "DiscOpen",
	Key:  "prop_18562bd28386b95f",
	Build: family.Theorem("∀c:complex. ∀r:real. {w:complex | |w - c| < r} ∈ complex_topology",
		func(a *Argument, c *Expr[Complex], r *Expr[Real]) {
			centre := a.MemberOf[on.Any](c, set_basic.InUniv.At(c))
			disc := a.Have(
				"the complex numbers within r of c are the ball of the distance about c",
				"{w:complex | |w - c| < r} = ball(𝕌, complex_dist, c, r)",
				Simp(Fwd(set_basic.Extension.Inst[Complex]()), Fwd(ComplexBall)),
				BySets())
			a.Show(
				"and a ball about a point of the carrier is open",
				Unfold(ComplexTopologyDef),
				disc.Rw(),
				By(metric_space.BallOpen.Read(ComplexMetric).At(centre, r)))
		}),
})}

// PuncturedDiscOpen — a punctured disc is open: a point z of it, at distance
// d from the centre, keeps the disc about it of radius min(d, r − d) inside
// it, by the triangle inequality on either side.
var PuncturedDiscOpen = puncturedDiscOpenThm{family.Add(registry.ProofEntry{
	Name: "PuncturedDiscOpen",
	Key:  "prop_d2f4f46cd4397dbf",
	Build: family.Theorem("∀c:complex. ∀r:real. "+
		"    {z:complex | &0 < |z - c| ∧ |z - c| < r} ∈ complex_topology",
		func(a *Argument, c *Expr[Complex], r *Expr[Real]) {
			a.Do(Simp(Fwd(ComplexOpenIff)))
			z := a.FixAs[Complex]("z")
			inside := a.Assume()
			parts := a.Conjuncts(
				inside,
				"z is off the centre",
				"z is inside the radius")
			distance := a.TermAs[Real]("|z - c|")
			gap := a.TermAs[Real]("r - |z - c|")
			a.Take(a.TermAs[Real]("min(|z - c|, r - |z - c|)"))
			positive := a.Have(
				"the radius min(|z − c|, r − |z − c|) is positive",
				"&0 < min(|z - c|, r - |z - c|)",
				ByArith(parts[0], parts[1], real_sup_inf.LessThanMin.At(distance, gap, a.TermAs[Real]("&0"))))
			near := a.Have(
				"a point w within that radius of z is off c and inside r, by the triangle inequality through z",
				"∀w:complex. |w - z| < min(|z - c|, r - |z - c|) ⇒ w ∈ {u:complex | &0 < |u - c| ∧ |u - c| < r}",
				Derive(func(b *Argument) {
					w := b.FixAs[Complex]("w")
					within := b.Assume()
					distances := metric_space.DistTriangle.Read(ComplexMetric)
					b.Show(
						"|w − c| ≤ |w − z| + |z − c| < r, and |z − c| ≤ |z − w| + |w − c| with |z − w| < |z − c|",
						ByArith(
							within,
							parts[0],
							parts[1],
							real_sup_inf.LessThanMin.At(distance, gap, b.TermAs[Real]("|w - z|")),
							At(distances, w, z, c),
							At(distances, z, w, c),
							At(metric_space.DistSym.Read(ComplexMetric), z, w),
							ComplexDistDef,
							set_basic.InUniv))
				}))
			a.Show(
				"so that disc about z lies in the punctured disc",
				By(positive, near))
		}),
})}

// RightHalfPlaneOpen — the half-plane to the right of the line re = c is
// open: a point w of it keeps the disc of radius re(w) − c about it inside
// it, the real part moving no further than the point moves.
var RightHalfPlaneOpen = rightHalfPlaneOpenThm{family.Add(registry.ProofEntry{
	Name: "RightHalfPlaneOpen",
	Key:  "prop_1cf8b592a5cab44a",
	Build: family.Theorem("∀c:real. {z:complex | c < re(z)} ∈ complex_topology",
		func(a *Argument, c *Expr[Real]) {
			a.Do(Simp(Fwd(ComplexOpenIff)))
			w := a.FixAs[Complex]("w")
			inside := a.Assume()
			right := a.Have(
				"w lies to the right of the line",
				"c < re(w)",
				BySets(inside))
			a.Take(a.TermAs[Real]("re(w) - c"))
			near := a.Have(
				"a point z within re(w) − c of w lies to the right "+
					"of the line too, re(w) − re(z) being at most |z − w|",
				"∀z:complex. |z - w| < re(w) - c ⇒ z ∈ {u:complex | c < re(u)}",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					within := b.Assume()
					above := b.Have(
						"its real part is above c",
						"c < re(z)",
						ByArith(within, complex_abs.PartsNonexpanding.At(z, w)))
					b.Show(
						"so z lies in the half-plane",
						BySets(above))
				}))
			a.Show(
				"so the disc of positive radius re(w) − c about w lies in the half-plane",
				ByArith(right, near))
		}),
})}

// FinitePointsIsolated — the points of a finite set other than p keep a
// positive distance from p. By induction on the set: ∅ has no points, and a
// new point x other than p brings the distance down to the smaller of the old
// one and |x − p|, which is still positive.
var FinitePointsIsolated = finitePointsIsolatedThm{family.Add(registry.ProofEntry{
	Name: "FinitePointsIsolated",
	Key:  "prop_25f6510e313cb750",
	Build: family.Theorem(Statement{
		Binders: "∀P:set(complex). ∀p:complex.",
		Hypotheses: []string{
			"finite(P)",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ ∀q:complex. q ∈ P ∧ |q - p| < δ ⇒ q = p",
	},
		func(a *Argument, P *Expr[Set[Complex]], p *Expr[Complex], finite Fact) {
			a.Show(
				"by induction on the finite set",
				ByInduction(finite_set.FiniteInduct, finite,
					Case(
						"∅ has no point near p, so the distance 1 serves",
						Derive(func(b *Argument) {
							b.Take(b.TermAs[Real]("&1"))
							b.Show(
								"1 is positive and nothing is in ∅",
								By(set_basic.NotInEmpty))
						})),
					Case(
						"a new point x keeps the distance, or brings it down to min(δ, |x − p|) when x is not p",
						Derive(func(b *Argument) {
							b.FixAs[Complex]("x")
							b.FixAs[Set[Complex]]("J")
							δ, near := b.UnpackAs[Real](b.Assume(), "δ")
							parts := b.Conjuncts(
								near,
								"δ is positive",
								"no point of J other than p is within δ of p")
							b.Cases(b.TermAs[Bool]("x = p"))
							b.When(
								"when x is p, δ still serves",
								func(c *Argument, same Fact) {
									c.Take(δ)
									c.Show(
										"a point of J with x put in is x, which is p, or a point of J",
										By(Normalized, same, near, set_basic.InInsert))
								})
							b.Otherwise(
								"when x is not p, the smaller of δ and |x − p| serves",
								func(c *Argument, apart Fact) {
									gap := c.TermAs[Real]("|x - p|")
									c.Take(c.TermAs[Real]("min(δ, |x - p|)"))
									positive := c.Have(
										"min(δ, |x − p|) is positive, x being apart from p",
										"&0 < min(δ, |x - p|)",
										ByArith(
											apart,
											parts[0],
											real_sup_inf.LessThanMin.At(δ, gap, c.TermAs[Real]("&0")),
											complex_abs.AbsPosIffNonzero.At(c.TermAs[Complex]("x - p"))))
									c.Show(
										"x itself is |x − p| from p, and a point of J nearer than δ is p",
										By(
											positive,
											parts[1],
											set_basic.InInsert,
											real_sup_inf.LessThanMin,
											real_order_ring.LessThanIrrefl))
								})
						}))))
		}),
})}

// ComplexHausdorff — two distinct complex numbers lie in disjoint open
// sets: the metric topology of a metric space is Hausdorff, and ℂ with
// its distance is one.
var ComplexHausdorff = complexHausdorffThm{family.Add(registry.ProofEntry{
	Name: "ComplexHausdorff",
	Key:  "prop_a95d41b796382e53",
	Build: family.Theorem("hausdorff(complex_topology)",
		func(a *Argument) {
			a.Show(
				"the metric topology of a metric space is Hausdorff",
				Unfold(ComplexTopologyDef),
				By(metric_space.MetricHausdorff.Read(ComplexMetric)))
		}),
})}

// OpenDiffFinite — an open set of the plane less finitely many points is
// open: the plane is Hausdorff, so its finite sets are closed, and S ∖ P is S
// met with the open complement of P.
var OpenDiffFinite = openDiffFiniteThm{family.Add(registry.ProofEntry{
	Name: "OpenDiffFinite",
	Key:  "prop_4b09ab362a3d5d2b",
	Build: family.Theorem(Statement{
		Binders: "∀S P:set(complex).",
		Hypotheses: []string{
			"S ∈ complex_topology",
			"finite(P)",
		},
		Conclusion: "S ∖ P ∈ complex_topology",
	},
		func(a *Argument, S, P *Expr[Set[Complex]], open, finite Fact) {
			plane := a.TermAs[Set[Set[Complex]]]("complex_topology")
			complement := a.TermAs[Set[Complex]]("𝕌 ∖ P")
			closed := a.Have(
				"P is closed, a finite set of the plane, which is Hausdorff and so T1",
				"closed_in(complex_topology, P)",
				By(
					Normalized,
					ComplexHausdorff,
					finite,
					ComplexTopologySpace,
					set_order.SubsetUniv.At(P),
					separation.HausdorffImpT1.At(plane),
					separation.T1FiniteClosed.Read(ComplexTopology).At(P)))
			outside := a.Have(
				"so its complement in the plane is open",
				"𝕌 ∖ P ∈ complex_topology",
				By(Normalized, closed, ComplexTopologySpace, topological_space.ClosedInDef.At(plane, P)))
			meet := a.Have(
				"S ∖ P is S met with the complement of P",
				"S ∖ P = S ∩ (𝕌 ∖ P)",
				BySets())
			a.Show(
				"and two open sets meet in an open set",
				meet.Rw(),
				By(open, outside, topological_space.InterOpen.Read(ComplexTopology).AsFact().At(S, complement)))
		}),
})}

// ComplexTopologySubspace — a set of complex numbers under the same
// distance carries the subspace topology: the metric chapter's theorem
// read at the plane, every set of complex numbers lying in it.
var ComplexTopologySubspace = complexTopologySubspaceThm{family.Add(registry.ProofEntry{
	Name: "ComplexTopologySubspace",
	Key:  "prop_550362ebca145740",
	Build: family.Theorem("∀s:set(complex). "+
		"    metric_topology(s, complex_dist) = subtopology(complex_topology, s)",
		func(a *Argument, s *Expr[Set[Complex]]) {
			a.Show(
				"a subset of a metric space, measured with the same distance, carries the subspace topology",
				Unfold(ComplexTopologyDef),
				By(metric_space.MetricTopologySubspace.Read(ComplexMetric).At(s), set_order.SubsetUniv.At(s)))
		}),
})}

// ConvergesIffMetric — a sequence of complex numbers tends to l exactly
// when it converges to l in the metric space: every term and the limit
// lie in the plane, and the distance from a(n) to l is |a(n) − l|, so the
// two ε-N sentences are one.
var ConvergesIffMetric = convergesIffMetricThm{family.Add(registry.ProofEntry{
	Name: "ConvergesIffMetric",
	Key:  "prop_10a810a92fcea6cb",
	Build: family.Theorem("∀a:(num → complex). ∀l:complex. "+
		"    a ⟶ l ⇔ metric_converges_to(𝕌, complex_dist, a, l)",
		func(arg *Argument, a *Arrow[Nat, Complex], l *Expr[Complex]) {
			arg.Show(
				"the two ε-N sentences, the memberships in the plane holding and the distance unfolded",
				Unfold(ComplexConvergesToDef),
				Unfold(complete_metric.MetricConvergesToDef),
				Simp(Fwd(ComplexDistDef), Fwd(set_basic.InUniv.Inst[Complex]())),
				TrivialNormalized())
		}),
})}

// ComplexComplete — the plane with its distance is complete. Read with the
// distance |x(m) − x(n)|, a Cauchy sequence of the metric space draws
// together in modulus, so it converges by Cauchy's criterion
// (CauchyIffConvergent), and converging is converging for the distance
// (ConvergesIffMetric).
var ComplexComplete = complexCompleteThm{family.Add(registry.ProofEntry{
	Name: "ComplexComplete",
	Key:  "prop_3254d66cd193c50d",
	Build: family.Theorem("metric_complete(𝕌, complex_dist)",
		func(a *Argument) {
			a.Do(Unfold(complete_metric.MetricCompleteDef))
			x := a.FixAs[Fun[Nat, Complex]]("x")
			cauchy := a.Assume()
			together := a.Have(
				"the terms draw together in modulus, the distance "+
					"of two terms being the modulus of their difference",
				"∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ |x(m) - x(n)| < ε",
				Simp(Rev(ComplexDistDef)),
				By(a.Unfolded(cauchy, complete_metric.MetricCauchyDef)))
			l, limit := a.ObtainAs[Complex](
				"so x converges, by Cauchy's criterion, to some l",
				"∃l:complex. x ⟶ l",
				By(together, CauchyIffConvergent.At(x)),
				Named("l"))
			a.Take(l)
			a.Show(
				"and converging to l is converging to l for the distance",
				By(limit, ConvergesIffMetric.At(x, l)))
		}),
})}
