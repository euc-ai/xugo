// compact.go — compact sets of the plane: Heine–Borel, the closed discs and
// circles, and a function continuous on a compact set, which is bounded,
// attains a largest modulus and is uniformly continuous there; and the tube
// about a compact segment: an open set containing the closed half-plane
// Re s ≥ 1 contains, at each height R, a strip 1 − δ < Re s, |Im s| ≤ R.

package complex_topology

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosedBoundedSequentiallyCompact — a closed set of complex numbers
// bounded in modulus is sequentially compact: every sequence of its points
// has a subsequence converging, in the distance of the plane, to a point of
// the set.
//
// The terms have modulus at most B, so by Bolzano–Weierstrass a
// subsequence tends to some l, which is convergence for the distance; the
// closed set keeps the limit of a sequence of its points.
var ClosedBoundedSequentiallyCompact = closedBoundedSequentiallyCompactThm{family.Add(registry.ProofEntry{
	Name: "ClosedBoundedSequentiallyCompact",
	Key:  "prop_6e7a18d1473b1a7c",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(complex). ∀B:real. ∀x:(num → complex).",
		Hypotheses: []string{
			"closed_in(complex_topology, k)",
			"∀z:complex. z ∈ k ⇒ |z| ≤ B",
			"∀n:num. x(n) ∈ k",
		},
		Conclusion: "∃σ:(num → num). ∃l:complex. " +
			"    (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(𝕌, complex_dist, x ∘ σ, l)",
	},
		func(
			a *Argument,
			k *Expr[Set[Complex]],
			B *Expr[Real],
			closed, bound Fact,
			x *Arrow[Nat, Complex],
			inK Fact,
		) {
			metricClosed := a.Unfolded(closed, ComplexTopologyDef)
			sigma, l, sub := a.Obtain2As[Fun[Nat, Nat], Complex](
				"the terms have modulus at most B, so by Bolzano–Weierstrass a subsequence x ∘ σ tends to some l",
				"∃σ:(num → num). ∃l:complex. (∀j:num. σ(j) < σ(j + 1)) ∧ x ∘ σ ⟶ l",
				By(BolzanoWeierstrass.At(x, B), bound, inK),
				Named("σ", "l"))
			subParts := a.Conjuncts(
				sub,
				"σ is strictly increasing",
				"and x ∘ σ tends to l")
			subsequence := a.TermAs[Fun[Nat, Complex]]("x ∘ σ")
			metric := a.Have(
				"which is convergence for the distance",
				"metric_converges_to(𝕌, complex_dist, x ∘ σ, l)",
				By(subParts[1], ConvergesIffMetric.At(subsequence, l)))
			terms := a.Have(
				"the terms of the subsequence are terms of x, so points of k",
				"∀n:num. (x ∘ σ)(n) ∈ k",
				// `o` is function composition: unfolded, (x ∘ σ)(n) is x(σ(n)).
				Unfold(functions.ComposeApply),
				By(inK))
			limit := a.Have(
				"k is closed, so it keeps the limit of a sequence of its points",
				"l ∈ k",
				By(complete_metric.ClosedIffSequential.Read(ComplexMetric).At(k), metricClosed, terms, metric))
			a.Take(sigma)
			a.Take(l)
			a.Show(
				"σ and l are the subsequence and the limit asked for",
				By(subParts[0], limit, metric))
		}),
})}

// ComplexCompactIff — Heine–Borel in the plane: a set of complex numbers
// is compact exactly when it is closed and its moduli are bounded.
//
// A compact set is closed, the plane being Hausdorff, and its moduli are
// the image of a compact set under the continuous modulus, a compact set
// of reals, which is bounded. Conversely, a closed set bounded in modulus
// is sequentially compact (ClosedBoundedSequentiallyCompact above), and in
// a metric space a set whose sequences have subsequences converging in it
// is compact.
var ComplexCompactIff = complexCompactIffThm{family.Add(registry.ProofEntry{
	Name: "ComplexCompactIff",
	Key:  "prop_771232f715f99dd",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(complex).",
		Conclusion: "compact_in(complex_topology, k) ⇔ " +
			"closed_in(complex_topology, k) ∧ ∃B:real. ∀z:complex. z ∈ k ⇒ |z| ≤ B",
		Abbrev: Abbrev{
			{Name: "moduli", Text: "image(λz:complex. |z|, k)"},
		},
	},
		func(a *Argument, k *Expr[Set[Complex]]) {
			a.Iff()
			a.Forward(
				"a compact set is closed, and its moduli are bounded",
				func(b *Argument, isCompact Fact) {
					closed := b.Have(
						"k is closed, a compact set of the Hausdorff plane",
						"closed_in(complex_topology, k)",
						By(compact.CompactClosed.Read(ComplexTopology).At(k), ComplexHausdorff, isCompact))
					moduli := b.Have(
						"the moduli of the points of k form a compact set of "+
							"reals, the image of k under the continuous modulus",
						"compact_in(real_topology, «moduli»)",
						By(continuous.ImageCompact.Read(ModulusContinuous).At(k), isCompact))
					_, bound := b.ObtainAs[Real](
						"a compact set of reals is bounded, by some B",
						"∃B:real. ∀x:real. x ∈ «moduli» ⇒ |x| ≤ B",
						By(real_topology.CompactBounded.At(b.TermAs[Set[Real]]("«moduli»")), moduli),
						Named("B"))
					within := b.Have(
						"so every point of k has modulus at most B",
						"∀z:complex. z ∈ k ⇒ |z| ≤ B",
						Derive(func(c *Argument) {
							z := c.FixAs[Complex]("z")
							inK := c.Assume()
							size := c.TermAs[Real]("|z|")
							c.Show(
								"|z| is among the moduli, and no real exceeds its absolute value",
								ByArith(
									bound.At(size),
									set_image.FunInImage.At(c.TermAs[Fun[Complex, Real]]("complex_abs"), k, z),
									inK,
									real_sgn_abs.AbsDominates.At(size)))
						}))
					b.Show(
						"k is closed and bounded in modulus",
						By(closed, within))
				})
			a.Backward(
				"a closed set bounded in modulus is sequentially compact, so compact",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"k is closed",
						"and its moduli are bounded")
					B, bound := b.UnpackAs[Real](parts[1], "B")
					b.Show(
						"its sequences have subsequences converging in it, and in a metric space such a set is compact",
						Simp(Fwd(ComplexTopologyDef)),
						By(
							complete_metric.SequentialImpCompact.Read(ComplexMetric).At(k),
							set_order.SubsetUniv.At(k),
							At(ClosedBoundedSequentiallyCompact, k, B),
							parts[0],
							bound))
				})
		}),
})}

// ClosedDiscCompact — a closed disc of the plane is compact.
//
// It is the closed ball of the distance about its centre, which is
// closed, and a point within r of c has modulus at most |c| + r; closed
// and bounded in modulus, it is compact by Heine–Borel.
var ClosedDiscCompact = closedDiscCompactThm{family.Add(registry.ProofEntry{
	Name: "ClosedDiscCompact",
	Key:  "prop_9c4053cc9d347ba9",
	Build: family.Theorem(Statement{
		Binders:    "∀c:complex. ∀r:real.",
		Conclusion: "compact_in(complex_topology, «disc»)",
		Abbrev: Abbrev{
			{Name: "disc", Text: "{z:complex | |z - c| ≤ r}"},
		},
	},
		func(a *Argument, c *Expr[Complex], r *Expr[Real]) {
			ball := a.Have(
				"the closed disc is the closed ball of the distance about c",
				"«disc» = closed_ball(𝕌, complex_dist, c, r)",
				Simp(
					Fwd(set_basic.Extension.Inst[Complex]()),
					Fwd(metric_space.ClosedBallDef.Inst[Complex]()),
					Fwd(ComplexDistDef),
					Fwd(set_basic.InUniv.Inst[Complex]())),
				Derive(func(b *Argument) {
					x := b.FixAs[Complex]("x")
					b.Show(
						"and the distance from c to x is |c − x|, which is |x − c|",
						By(Normalized, complex_abs.AbsSubComm.At(c, x)))
				}))
			closed := a.Have(
				"a closed ball of a metric space is closed",
				"closed_in(complex_topology, closed_ball(𝕌, complex_dist, c, r))",
				Unfold(ComplexTopologyDef),
				By(metric_space.ClosedBallClosed.Read(ComplexMetric).At(
					a.MemberOf[on.Any](c, set_basic.InUniv.At(c)), r)))
			bounded := a.Have(
				"a point within r of c has modulus at most |c| + r",
				"∀z:complex. |z - c| ≤ r ⇒ |z| ≤ |c| + r",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]("z")
					near := b.Assume()
					b.Show(
						"|z| − |c| is at most |z − c|, by the reverse triangle inequality",
						ByArith(complex_abs.AbsTriangleReverse.At(z, c), near))
				}))
			a.Show(
				"closed and bounded in modulus, the disc is compact by Heine–Borel",
				By(ComplexCompactIff.At(a.TermAs[Set[Complex]]("«disc»")), ball, closed, bounded))
		}),
})}

// CircleCompact — a circle of the plane is compact.
//
// The circle about c of radius r is the closed disc with the open disc
// taken out. The closed disc is compact, the points at distance at least
// r from c form the complement of an open set and so a closed one, and a
// compact set meets a closed set in a compact set.
var CircleCompact = circleCompactThm{family.Add(registry.ProofEntry{
	Name: "CircleCompact",
	Key:  "prop_93879e9f9c745f08",
	Build: family.Theorem(Statement{
		Binders:    "∀c:complex. ∀r:real.",
		Conclusion: "compact_in(complex_topology, «circle»)",
		Abbrev: Abbrev{
			{Name: "circle", Text: "{z:complex | |z - c| = r}"},
			{Name: "disc", Text: "{z:complex | |z - c| ≤ r}"},
			{Name: "inside", Text: "{w:complex | |w - c| < r}"},
			{Name: "outside", Text: "𝕌 ∖ «inside»"},
		},
	},
		func(a *Argument, c *Expr[Complex], r *Expr[Real]) {
			outside := a.Have(
				"the points at distance at least r from c form a closed set, the complement of the open disc",
				"closed_in(complex_topology, «outside»)",
				By(
					topological_space.OpenClosedComplement.At(
						a.TermAs[Set[Set[Complex]]]("complex_topology"),
						a.TermAs[Set[Complex]]("«inside»")),
					DiscOpen.At(c, r),
					ComplexTopologySpace))
			ring := a.Have(
				"the closed disc is compact, so it meets that closed set in a compact set",
				"compact_in(complex_topology, «disc» ∩ «outside»)",
				By(compact.CompactInterClosed, ClosedDiscCompact.At(c, r), outside))
			circle := a.Have(
				"which is the circle: a point within r of c and not nearer than r lies at distance r",
				"«circle» = «disc» ∩ «outside»",
				Simp(
					Fwd(set_basic.Extension.Inst[Complex]()),
					Fwd(set_basic.InInter.Inst[Complex]()),
					Fwd(set_basic.InDiff.Inst[Complex]()),
					Fwd(set_basic.InUniv.Inst[Complex]())),
				ByArith())
			a.Show(
				"so the circle is compact",
				circle.Rw(),
				By(ring))
		}),
})}

// ModulusAttainsMax — on a non-empty compact set, the modulus of a
// continuous function attains a largest value.
//
// Read as a continuous map from the subspace k, f composed with the
// continuous modulus is a continuous real function |f| on k, and a
// continuous real function on a non-empty compact set attains a largest
// value.
var ModulusAttainsMax = modulusAttainsMaxThm{family.Add(registry.ProofEntry{
	Name: "ModulusAttainsMax",
	Key:  "prop_640c9e5e3cb0251d",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"compact_in(complex_topology, k)",
			"k ≠ ∅",
			"complex_continuous_on(k, f)",
		},
		Conclusion: "∃z:complex. z ∈ k ∧ ∀w:complex. w ∈ k ⇒ |f(w)| ≤ |f(z)|",
	},
		func(
			a *Argument,
			k *Expr[Set[Complex]],
			f *Arrow[Complex, Complex],
			isCompact, nonempty, onK Fact,
		) {
			isMap := a.Have(
				"f is a continuous map from the subspace k to the plane",
				"continuous_map(subtopology(complex_topology, k), complex_topology, f)",
				By(ContinuousOnIffMap.At(k, f), onK))
			composite := a.Have(
				"followed by the continuous modulus, it is a continuous real function on k",
				"continuous_map(subtopology(complex_topology, k), real_topology, (λz:complex. |z|) ∘ f)",
				By(
					continuous.Compose.Read(isMap).At(
						a.TermAs[Set[Set[Real]]]("real_topology"),
						a.TermAs[Fun[Complex, Real]]("λz:complex. |z|")),
					ModulusContinuous))
			// `o` is function composition: unfolded, the composite's value at w is |f(w)|.
			sizes := a.Unfolded(composite, functions.ComposeApply)
			a.Show(
				"k is compact in its own subspace and not empty, so there |f| attains a largest value",
				By(
					real_valued.ContinuousCompactMaximum,
					sizes,
					compact.CompactInOwnSubtopology.At(a.TermAs[Set[Set[Complex]]]("complex_topology"), k),
					isCompact,
					nonempty))
		}),
})}

// ContinuousOnCompactBounded — a function continuous on a compact set is
// bounded there.
//
// Read as a continuous map from the subspace k, f carries the compact set
// k to a compact set f(k), whose moduli are bounded by Heine–Borel; every
// value f(w) with w in k lies in f(k).
var ContinuousOnCompactBounded = continuousOnCompactBoundedThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnCompactBounded",
	Key:  "prop_600d797ffa798cf7",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(complex). ∀f:(complex → complex).",
		Hypotheses: []string{
			"compact_in(complex_topology, k)",
			"complex_continuous_on(k, f)",
		},
		Conclusion: "∃B:real. ∀w:complex. w ∈ k ⇒ |f(w)| ≤ B",
	},
		func(a *Argument, k *Expr[Set[Complex]], f *Arrow[Complex, Complex], isCompact, onK Fact) {
			isMap := a.Have(
				"f is a continuous map from the subspace k to the plane",
				"continuous_map(subtopology(complex_topology, k), complex_topology, f)",
				By(ContinuousOnIffMap.At(k, f), onK))
			values := a.Have(
				"so it carries k, compact in its own subspace, to a compact set",
				"compact_in(complex_topology, image(f, k))",
				By(
					continuous.ImageCompact.Read(isMap).At(k),
					compact.CompactInOwnSubtopology.At(a.TermAs[Set[Set[Complex]]]("complex_topology"), k),
					isCompact))
			B, bound := a.ObtainAs[Real](
				"whose moduli are bounded by Heine–Borel, by some B",
				"∃B:real. ∀u:complex. u ∈ image(f, k) ⇒ |u| ≤ B",
				By(ComplexCompactIff.At(a.TermAs[Set[Complex]]("image(f, k)")), values))
			a.Take(B)
			w := a.FixAs[Complex]("w")
			inK := a.Assume()
			a.Show(
				"f(w) lies in f(k), so its modulus is at most B",
				By(bound.At(f.Apply(w)), set_image.FunInImage.At(f, k, w), inK))
		}),
})}

// ContinuousOnCompactUniform — a function continuous on a compact set is
// uniformly continuous there: for each ε one δ serves every pair of points
// of the set.
//
// The set with the same distance is a metric space whose open sets are
// those of its subspace (ComplexTopologySubspace), so it is a compact
// metric space and f is a continuous map from it to the plane.
// Heine–Cantor makes f uniformly continuous, which, the distance being the
// modulus of the difference, is the ε–δ sentence asked for.
var ContinuousOnCompactUniform = continuousOnCompactUniformThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnCompactUniform",
	Key:  "prop_6139bb030bc43979",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(complex). ∀f:(complex → complex). ∀ε:real.",
		Hypotheses: []string{
			"compact_in(complex_topology, k)",
			"complex_continuous_on(k, f)",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ ∀z w:complex. z ∈ k ∧ w ∈ k ∧ |z - w| < δ ⇒ |f(z) - f(w)| < ε",
	},
		func(a *Argument, k *Expr[Set[Complex]], f *Arrow[Complex, Complex], isCompact, onK Fact) {
			// ε and &0 < ε stay in the goal: the closing reading answers every ε.
			restricted := a.Have(
				"k with the same distance is a metric space",
				"metric_space(k, complex_dist)",
				By(metric_space.SubMetricSpace.Read(ComplexMetric).At(k), set_order.SubsetUniv.At(k)))
			compactSpace := a.Have(
				"it is compact, k being compact in its own subspace",
				"compact_in(metric_topology(k, complex_dist), k)",
				Simp(Fwd(ComplexTopologySubspace)),
				By(
					compact.CompactInOwnSubtopology.At(a.TermAs[Set[Set[Complex]]]("complex_topology"), k),
					isCompact))
			isMap := a.Have(
				"and f is a continuous map from it to the plane",
				"continuous_map(metric_topology(k, complex_dist), metric_topology(𝕌, complex_dist), f)",
				Simp(Rev(ComplexTopologyDef)),
				Simp(Fwd(ComplexTopologySubspace)),
				By(ContinuousOnIffMap.At(k, f), onK))
			uniform := a.Have(
				"so f is uniformly continuous on k, by Heine–Cantor",
				"uniformly_continuous_map(k, complex_dist, 𝕌, complex_dist, f)",
				By(
					complete_metric.HeineCantor.Read(restricted).At(
						a.TermAs[Set[Complex]]("𝕌"),
						a.TermAs[Fun2[Complex, Complex, Real]]("complex_dist"),
						f),
					ComplexMetric,
					compactSpace,
					isMap))
			a.Show(
				"one δ serves every pair of points of k, the distance being the modulus of the difference",
				Simp(Rev(ComplexDistDef)),
				By(complete_metric.UniformlyContinuousDelta.Read(uniform)))
		}),
})}

// StripInsideOpen — an open set containing the closed half-plane Re s ≥ 1
// contains, for every height R, a strip of some width δ to its left: the
// segment of the points 1 + it, |t| ≤ R, is closed and bounded, so
// sequentially compact, and its one-set cover {U} has a Lebesgue number δ;
// a point of the strip left of the line Re s = 1 is within δ of the point
// of the segment at its height.
var StripInsideOpen = stripInsideOpenThm{family.Add(registry.ProofEntry{
	Name: "StripInsideOpen",
	Key:  "prop_bd3b02acc04de768",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(complex). ∀R:real.",
		Hypotheses: []string{
			"U ∈ complex_topology",
			"∀s:complex. &1 ≤ re(s) ⇒ s ∈ U",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ ∀s:complex. &1 - δ < re(s) ∧ |im(s)| ≤ R ⇒ s ∈ U",
		Abbrev: Abbrev{
			{Name: "line", Text: "preimage_on(𝕌, λz:complex. re(z), ⟦&1, &1⟧)"},
			{Name: "band", Text: "preimage_on(𝕌, λz:complex. im(z), ⟦-R, R⟧)"},
		},
	},
		func(a *Argument, U *Expr[Set[Complex]], R *Expr[Real], open, inside Fact) {
			k, kDef := a.LetAs[Set[Complex]]("k", "{z:complex | re(z) = &1 ∧ |im(z)| ≤ R}")
			onK := a.Have(
				"k is the segment of the points of real part 1 and imaginary part at most R in modulus",
				"∀z:complex. z ∈ k ⇔ re(z) = &1 ∧ |im(z)| ≤ R",
				BySets(kDef))
			plane := a.TermAs[Set[Set[Complex]]]("complex_topology")
			reals := a.TermAs[Set[Set[Real]]]("real_topology")
			one := a.TermAs[Real]("&1")
			lineClosed := a.Have(
				"the line of the points of real part 1 is closed, "+
					"the preimage of ⟦1, 1⟧ under the continuous real part",
				"closed_in(complex_topology, «line»)",
				By(
					continuous.ClosedPreimage.At(plane, reals, a.TermAs[Fun[Complex, Real]]("λz:complex. re(z)")),
					PartsContinuous,
					real_topology.ClosedIntervalClosed.At(one, one),
					ComplexTopologySpace))
			bandClosed := a.Have(
				"and so is the band of imaginary part in ⟦−R, R⟧, its preimage under the continuous imaginary part",
				"closed_in(complex_topology, «band»)",
				By(
					continuous.ClosedPreimage.At(plane, reals, a.TermAs[Fun[Complex, Real]]("λz:complex. im(z)")),
					PartsContinuous,
					real_topology.ClosedIntervalClosed.At(a.TermAs[Real]("-R"), R),
					ComplexTopologySpace))
			segment := a.Have(
				"k is where the line meets the band, |im(z)| ≤ R saying that im(z) lies in ⟦−R, R⟧",
				"k = «line» ∩ «band»",
				Simp(
					Fwd(set_basic.Extension.Inst[Complex]()),
					Fwd(set_basic.InInter.Inst[Complex]()),
					Fwd(functions.PreimageOnDef),
					Fwd(set_basic.InUniv.Inst[Complex]()),
					Fwd(real_topology.ClosedIntervalMembership),
					Fwd(onK)),
				ByArith())
			closed := a.Have(
				"so k is closed, an intersection of two closed sets",
				"closed_in(complex_topology, k)",
				segment.Rw(),
				By(
					topological_space.InterClosed.Read(ComplexTopology).At(
						a.TermAs[Set[Complex]]("«line»"),
						a.TermAs[Set[Complex]]("«band»")),
					lineClosed,
					bandClosed))
			bounded := a.Have(
				"and bounded: a point of k has modulus at most the sum of the moduli of its parts, 1 and at most R",
				"∀z:complex. z ∈ k ⇒ |z| ≤ &1 + R",
				a.ForEach(func(z *Expr[Complex]) Action {
					return ByArith(onK.At(z), complex_abs.AbsLeParts.At(z))
				}))
			metricOpen := a.Unfolded(open, ComplexTopologyDef)
			coverOpen := a.Have(
				"so the one-set cover {U} is open in the distance of ℂ",
				"{U} ⊆ metric_topology(𝕌, complex_dist)",
				By(metricOpen, set_order.SingSubset))
			covers := a.Have(
				"and it covers k: a point of real part 1 lies in the half-plane, so in U",
				"k ⊆ ⋃{U}",
				Simp(Fwd(set_algebra.UnionsSing), Fwd(set_basic.SubsetDef)),
				a.ForEach(func(z *Expr[Complex]) Action {
					return ByArith(onK.At(z), inside.At(z))
				}))
			lebesgue := a.Have(
				"closed and bounded, k is sequentially compact, and its cover by open sets has a Lebesgue number",
				"∃δ:real. &0 < δ ∧ ∀z:complex. z ∈ k ⇒ ∃u:set(complex). u ∈ {U} ∧ ball(𝕌, complex_dist, z, δ) ⊆ u",
				By(
					At(ClosedBoundedSequentiallyCompact, k, a.TermAs[Real]("&1 + R")),
					closed,
					bounded,
					coverOpen,
					covers,
					ComplexMetric,
					set_order.SubsetUniv.At(k),
					complete_metric.SequentialLebesgue.At(
						a.TermAs[Set[Complex]]("𝕌"),
						a.TermAs[Fun2[Complex, Complex, Real]]("complex_dist"),
						k,
						a.TermAs[Set[Set[Complex]]]("{U}"))))
			delta, number := a.ObtainAs[Real](
				"the one member of the cover is U, so every ball of radius δ about a point of k lies in U",
				"∃δ:real. &0 < δ ∧ ∀z:complex. z ∈ k ⇒ ball(𝕌, complex_dist, z, δ) ⊆ U",
				By(a.Simplified(lebesgue, Fwd(set_basic.InSing))),
				Named("δ"))
			radius := a.Conjuncts(
				number,
				"δ is positive",
				"and the ball of radius δ about each point of k lies in U")
			a.Take(delta)
			strip := a.Have(
				"every point s with 1 − δ < re(s) and |im(s)| ≤ R lies in U",
				"∀s:complex. &1 - δ < re(s) ∧ |im(s)| ≤ R ⇒ s ∈ U",
				Derive(func(b *Argument) {
					s := b.FixAs[Complex]("s")
					near := b.Assume()
					below := b.Assuming(
						b.TermAs[Bool]("re(s) < &1"),
						"a point with re(s) ≥ 1 lies in U by hypothesis",
						Given(func(c *Argument, atLeast Fact) {
							c.Show(
								"1 ≤ re(s): s is in the half-plane",
								ByArith(atLeast, inside.At(s)))
						}))
					w := b.TermAs[Complex]("complex(&1, im(s))")
					wOnK := b.Have(
						"the point w = 1 + i·im(s) at the height of s lies on k",
						"complex(&1, im(s)) ∈ k",
						By(near, onK.At(w)))
					inBall := b.Have(
						"s is within δ of w: |s − w| is at most |re(s) − 1| + |im(s) − im(s)| = 1 − re(s) < δ",
						"s ∈ ball(𝕌, complex_dist, complex(&1, im(s)), δ)",
						ByArith(
							below,
							near,
							ComplexBall.At(w, delta, s),
							complex_abs.AbsLeParts.At(b.TermAs[Complex]("s - complex(&1, im(s))")),
							complex_field.PartsSub.At(s, w)))
					b.Show(
						"so s lies in the ball of radius δ about w, which lies in U",
						BySets(wOnK, inBall, radius[1].At(w)))
				}))
			a.Show(
				"δ is the width asked for",
				By(radius[0], strip))
		}),
	Reading: "δ depends on R: an open set containing the " +
		"closed half-plane need contain no strip of uniform width.",
})}
