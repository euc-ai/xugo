// local_order.go — the order of a function at a closed point. The local ring at
// a closed point is its chart with the complement of its maximal ideal inverted.
// Extending fractional ideals to that ring is multiplicative, takes every other
// closed point to the ring itself and this one to the maximal ideal, so the pair
// of a closed divisor extends to a signed power of that ideal, and the
// coefficient of a principal divisor is the power that f generates. A generator
// of the ideal of a point whose partner is its multiple by a unit of the local
// ring generates the maximal ideal, and so has order one.

package divisor_lattice_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/signed_ideal_power"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/subring_localization"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/regular_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PointComponent — reading a pair at the chart a point lies in: the component of
// a pair in the point's chart takes the structure pair to the chart, products
// and inverses of pairs to products and inverses of fractional ideals, and an
// invertible pair to an invertible fractional ideal.
var PointComponent = pointComponentThm{family.Add(registry.ProofEntry{
	Name: "PointComponent",
	Key:  "prop_63f8dea67b670cc5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁ A₀₁:set(A). ∀P X Y:prod(set(A), set(A)).",
		Conclusion: "«component»((A₀, A₁)) = point_chart(A₀, A₁, P) ∧ " +
			"«component»(lattice_pair_mul(R, A₀, A₁, X, Y)) = " +
			"fractional_mul(R, point_chart(A₀, A₁, P), «component»(X), «component»(Y)) ∧ " +
			"«component»(lattice_pair_inverse(R, A₀, A₁, X)) = " +
			"fractional_inverse(R, point_chart(A₀, A₁, P), «component»(X)) ∧ " +
			"(invertible_lattice_pair(R, A₀, A₁, A₀₁, X) ⇒ " +
			"    invertible_fractional(R, point_chart(A₀, A₁, P), «component»(X)))",
		Abbrev: Abbrev{
			{Name: "component", Text: "λZ:prod(set(A), set(A)). COND(fst(P) = A₀, snd(Z), fst(Z))"},
		},
	},
		func(a *Argument, R *Expr[RingOps[A]], A0, A1, A01 *Expr[Set[A]], P, X, Y *Expr[_IdealPair]) {
			a.Do(Simp(
				Fwd(biaffine_rational_point.PointChartDef),
				Fwd(invertible_lattice_pair.LatticePairMulDef),
				Fwd(invertible_lattice_pair.LatticePairInverseDef),
				Fwd(invertible_lattice_pair.InvertibleLatticePairDef),
				Fwd(pairs.Fst),
				Fwd(pairs.Snd)))
			a.Cases(a.Term("fst(P) = A₀"))
			a.When(
				"at a point off chart 0 the component is the second",
				func(b *Argument, whole Fact) {
					b.Show(
						"each clause is read at A₁",
						By(whole))
				})
			a.Otherwise(
				"at a point of chart 0 the component is the first",
				func(b *Argument, proper Fact) {
					b.Show(
						"each clause is read at A₀",
						By(proper))
				})
		}),
})}

// ChartPointsSeparate — two closed points on chart 0 are told apart there: the
// component of the second in the chart holds a function off the first, one if
// it is the whole chart, and otherwise since two maximal ideals are comparable
// only when equal, and a maximal ideal is the first component of one point.
var ChartPointsSeparate = chartPointsSeparateThm{family.Add(registry.ProofEntry{
	Name: "ChartPointsSeparate",
	Key:  "prop_8d03a0b02dc1a061",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P Q:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(P)",
			"«scPoint»(Q)",
			"fst(P) ≠ A₀",
			"Q ≠ P",
		},
		Conclusion: "fst(Q) ⊆ A₀ ∧ (∃u:A. u ∈ fst(Q) ∧ u ∉ fst(P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P, Q *Expr[_IdealPair],
			curve, pointP, pointQ, proper, distinct Fact,
		) {
			ops := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀)")
			first, second := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("fst(Q)")
			clausesP := a.Unfolded(pointP, smooth_curve.CurveClosedPointDef)
			clausesQ := a.Unfolded(pointQ, smooth_curve.CurveClosedPointDef)
			maximalP := a.Have(
				"fst(P), a proper component, is maximal in chart 0",
				"maximal_ideal(restrict_ring(field_ring(L), A₀), fst(P))",
				By(Normalized, proper, clausesP))
			idealP := a.Have(
				"so it is an ideal missing one",
				"ring_ideal(restrict_ring(field_ring(L), A₀), fst(P)) ∧ L.one ∉ fst(P)",
				By(maximalP, ring_ideal.MaximalIdealDef.At(ops, first)))
			unique := a.Have(
				"fst(P) is the first component of one closed point",
				"∃!R:prod(set(A), set(A)). «scPoint»(R) ∧ fst(R) = fst(P)",
				By(curve, maximalP, smooth_curve.ChartMaximalClosedPoint.Read(L).At(k, A0, A1, A01, t, first)))
			differ := a.Have(
				"so Q, another closed point, has another first component",
				"fst(Q) ≠ fst(P)",
				Derive(func(b *Argument) {
					same := b.SupposeNot()
					_, center := b.UnpackAs[_IdealPair](unique, "c")
					b.Show(
						"both would be its center",
						By(Normalized, center.At(P), center.At(Q), pointP, pointQ, same, distinct))
				}))
			a.Cases(a.Term("fst(Q) = A₀"))
			a.When(
				"the whole chart holds one, which lies off fst(P)",
				func(b *Argument, whole Fact) {
					oneIn := b.Have(
						"one lies in the chart",
						"L.one ∈ fst(Q)",
						whole.Rw(),
						By(
							curve,
							smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t),
							comm_ring.SubringOne.At(b.TermAs[RingOps[A]]("field_ring(L)"), A0)))
					b.Show(
						"take one",
						Derive(func(c *Argument) {
							inside := c.Have(
								"fst(Q) is the chart",
								"fst(Q) ⊆ A₀",
								whole.Rw(),
								By(set_order.SubsetRefl))
							separated := c.Have(
								"one separates",
								"∃u:A. u ∈ fst(Q) ∧ u ∉ fst(P)",
								Derive(func(e *Argument) {
									e.Take(e.TermAs[A]("L.one"))
									e.Show(
										"it lies in fst(Q) and off fst(P)",
										By(oneIn, idealP))
								}))
							c.Show(
								"fst(Q) lies in the chart, and holds a function off fst(P)",
								By(inside, separated))
						}))
				})
			a.Otherwise(
				"a maximal ideal not inside fst(P) holds a function off it",
				func(b *Argument, notWhole Fact) {
					maximalQ := b.Have(
						"fst(Q), a proper component, is maximal in chart 0",
						"maximal_ideal(restrict_ring(field_ring(L), A₀), fst(Q))",
						By(Normalized, notWhole, clausesQ))
					idealQ := b.Have(
						"so it is an ideal",
						"ring_ideal(restrict_ring(field_ring(L), A₀), fst(Q))",
						By(maximalQ, ring_ideal.MaximalIdealDef.At(ops, second)))
					inside := b.Have(
						"which lies in the chart",
						"fst(Q) ⊆ A₀",
						By(idealQ, ring_ideal.RingIdealDef.At(ops, second)))
					notInside := b.Have(
						"and not inside fst(P), which misses one",
						"¬(fst(Q) ⊆ fst(P))",
						Derive(func(c *Argument) {
							contained := c.SupposeNot()
							c.Show(
								"a maximal ideal inside a proper ideal is that ideal",
								By(maximalQ, idealP, contained, differ, ring_ideal.MaximalIdealMaximal.At(ops, second, first)))
						}))
					separated := b.Have(
						"so it holds a function off fst(P)",
						"∃u:A. u ∈ fst(Q) ∧ u ∉ fst(P)",
						BySets(notInside))
					b.Show(
						"fst(Q) lies in the chart, and holds a function off fst(P)",
						By(inside, separated))
				})
		}),
})}

// PointsSeparate — another closed point is told apart from P on P's chart: its
// component there lies in the chart and holds a function off P's ideal. Off
// chart 0 this is ChartPointsSeparate read from the other chart.
var PointsSeparate = pointsSeparateThm{family.Add(registry.ProofEntry{
	Name: "PointsSeparate",
	Key:  "prop_6f8e6395e37e3cd6",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P Q:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(P)",
			"«scPoint»(Q)",
			"Q ≠ P",
		},
		Conclusion: "COND(fst(P) = A₀, snd(Q), fst(Q)) ⊆ point_chart(A₀, A₁, P) ∧ " +
			"(∃u:A. u ∈ COND(fst(P) = A₀, snd(Q), fst(Q)) ∧ u ∉ point_ideal(A₀, P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P, Q *Expr[_IdealPair],
			curve, pointP, pointQ, distinct Fact,
		) {
			a.Do(Simp(Fwd(biaffine_rational_point.PointChartDef), Fwd(biaffine_rational_point.PointIdealDef)))
			a.Cases(a.Term("fst(P) = A₀"))
			a.When(
				"off chart 0 the two points are told apart on chart 1",
				func(b *Argument, whole Fact) {
					swappedCurve := b.Have(
						"the curve read from its other chart",
						"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
						By(curve, smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
					pairP, pairQ := b.TermAs[_IdealPair]("(snd(P), fst(P))"), b.TermAs[_IdealPair]("(snd(Q), fst(Q))")
					ring := b.TermAs[RingOps[A]]("field_ring(L)")
					swappedP := b.Have(
						"P read from the other chart",
						"curve_closed_point(field_ring(L), A₁, A₀, A₀₁, (snd(P), fst(P)))",
						By(pointP, smooth_curve.ClosedPointSwap.At(ring, A0, A1, A01, P)))
					swappedQ := b.Have(
						"Q read from the other chart",
						"curve_closed_point(field_ring(L), A₁, A₀, A₀₁, (snd(Q), fst(Q)))",
						By(pointQ, smooth_curve.ClosedPointSwap.At(ring, A0, A1, A01, Q)))
					properP := b.Have(
						"P is proper in chart 1",
						"snd(P) ≠ A₁",
						By(Normalized, whole, b.Unfolded(pointP, smooth_curve.CurveClosedPointDef)))
					differ := b.Have(
						"and the swapped points differ",
						"(snd(Q), fst(Q)) ≠ (snd(P), fst(P))",
						Derive(func(c *Argument) {
							same := c.SupposeNot()
							parts := c.Have(
								"the components would agree",
								"snd(Q) = snd(P) ∧ fst(Q) = fst(P)",
								By(same, pairs.PairEq))
							c.Show(
								"so would the points",
								By(Normalized, parts, distinct, pairs.PairEta.At(P), pairs.PairEta.At(Q)))
						}))
					separated := b.Have(
						"so Q's second component lies in chart 1 and holds a function off snd(P)",
						"snd(Q) ⊆ A₁ ∧ (∃u:A. u ∈ snd(Q) ∧ u ∉ snd(P))",
						By(
							swappedCurve,
							swappedP,
							swappedQ,
							properP,
							differ,
							pairs.Fst,
							pairs.Snd,
							ChartPointsSeparate.Read(L).At(k, A1, A0, A01, b.TermAs[A]("L.inv(t)"), pairP, pairQ)))
					b.Show(
						"which is the component at P",
						By(Normalized, whole, separated))
				})
			a.Otherwise(
				"on chart 0 the two points are told apart there",
				func(b *Argument, proper Fact) {
					separated := b.Have(
						"Q's first component lies in chart 0 and holds a function off fst(P)",
						"fst(Q) ⊆ A₀ ∧ (∃u:A. u ∈ fst(Q) ∧ u ∉ fst(P))",
						By(
							curve,
							pointP,
							pointQ,
							proper,
							distinct,
							ChartPointsSeparate.Read(L).At(k, A0, A1, A01, t, P, Q)))
					b.Show(
						"which is the component at P",
						By(Normalized, proper, separated))
				})
		}),
})}

// LocalExtension — extension to the local ring at a closed point P, read on
// pairs through the component in P's chart: it takes the structure pair to the
// local ring, is multiplicative on invertible pairs and keeps their inverses,
// takes P to the maximal ideal, a proper ideal of the local ring, and takes any
// other closed point to the local ring itself.
var LocalExtension = localExtensionThm{family.Add(registry.ProofEntry{
	Name: "LocalExtension",
	Key:  "prop_7445b8ef2f0ba77b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(P)",
		},
		Conclusion: "subring(field_ring(L), «local») ∧ " +
			"«extended»((A₀, A₁)) = «local» ∧ " +
			"(∀X Y:prod(set(A), set(A)). " +
			"    «scInvertible»(X) ∧ «scInvertible»(Y) ⇒ " +
			"    «extended»(lattice_pair_mul(field_ring(L), A₀, A₁, X, Y)) = " +
			"    fractional_mul(field_ring(L), «local», «extended»(X), «extended»(Y))) ∧ " +
			"(∀X:prod(set(A), set(A)). " +
			"    «scInvertible»(X) ⇒ " +
			"    invertible_fractional(field_ring(L), «local», «extended»(X)) ∧ " +
			"    «extended»(lattice_pair_inverse(field_ring(L), A₀, A₁, X)) = " +
			"    fractional_inverse(field_ring(L), «local», «extended»(X))) ∧ " +
			"«extended»(P) = «maximal» ∧ " +
			"«maximal» ⊆ «local» ∧ " +
			"L.one ∉ «maximal» ∧ " +
			"(∀Q:prod(set(A), set(A)). «scPoint»(Q) ∧ Q ≠ P ⇒ «extended»(Q) = «local») ∧ " +
			"point_chart(A₀, A₁, P) ⊆ L.carrier",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "extended", Text: "λZ:prod(set(A), set(A)). " +
				"    module_span(restrict_ring(field_ring(L), «local»), " +
				"        regular_module(field_ring(L)), " +
				"        COND(fst(P) = A₀, snd(Z), fst(Z)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			curve, point Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			chart, ideal := a.TermAs[Set[A]]("point_chart(A₀, A₁, P)"), a.TermAs[Set[A]]("point_ideal(A₀, P)")
			charts := a.Have(
				"the charts are subrings of L",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁)",
				By(
					curve,
					smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			subringChart := a.Have(
				"so P's chart is one",
				"subring(field_ring(L), point_chart(A₀, A₁, P))",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(biaffine_rational_point.PointChartDef)))
					b.Cases(b.Term("fst(P) = A₀"))
					b.When(
						"chart 1",
						func(c *Argument, whole Fact) {
							c.Show(
								"a chart of the curve",
								By(whole, charts))
						})
					b.Otherwise(
						"chart 0",
						func(c *Argument, proper Fact) {
							c.Show(
								"a chart of the curve",
								By(proper, charts))
						})
				}))
			ringOn := a.Have(
				"the chart is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)))",
				By(subringChart, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(chart)))
			maximal := a.Have(
				"P is a maximal ideal of its chart",
				"maximal_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
				By(point, smooth_curve.ClosedPointMaximal.At(ring, A0, A1, A01, P)))
			primeIdeal := a.Have(
				"so a prime",
				"prime_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
				By(maximal, ring_ideal.MaximalIsPrime.Read(ringOn).At(ideal)))
			fractions := a.Have(
				"the local ring is the localization of the chart at P",
				"«local» = subring_localization(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P))",
				Simp(Fwd(regular_point.PointLocalRingDef)),
				Basic())
			laws := a.Conjuncts(
				a.Simplified(
					GroupPremises(
						subringChart, primeIdeal, subring_localization.LocalExtensionLaws.Read(L).At(chart, ideal)),
					Rev(fractions)),
				"the local ring is a subring",
				"the chart extends to it",
				"extension is multiplicative on invertible ideals",
				"extension keeps invertible ideals and their inverses",
				"P's ideal extends to the maximal ideal",
				"which lies in the local ring",
				"and misses one",
				"an ideal holding a function off P extends to the local ring")
			subringLocal, wholeChart, products, inverses, extendedPoint, insideLocal, proper, unitIdeals :=
				laws[0], laws[1], laws[2], laws[3], laws[4], laws[5], laws[6], laws[7]
			structure := a.Have(
				"the structure pair extends to the local ring",
				"«extended»((A₀, A₁)) = «local»",
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(wholeChart, biaffine_rational_point.PointChartDef.At(A0, A1, P)))
			multiplicative := a.Have(
				"on invertible pairs the extension is multiplicative",
				Statement{
					Binders:    "∀X Y:prod(set(A), set(A)).",
					Hypotheses: []string{"«scInvertible»(X)", "«scInvertible»(Y)"},
					Conclusion: "«extended»(lattice_pair_mul(field_ring(L), A₀, A₁, X, Y)) = " +
						"fractional_mul(field_ring(L), «local», «extended»(X), «extended»(Y))",
				},
				Derive(func(b *Argument) {
					X, Y := b.FixAs[_IdealPair]("X"), b.FixAs[_IdealPair]("Y")
					parts := b.Conjuncts(
						b.Assume(),
						"X is invertible",
						"Y is invertible")
					first := b.Conjuncts(
						PointComponent.At(ring, A0, A1, A01, P, X, Y),
						"the structure pair",
						"the product",
						"the inverse",
						"the invertible X")
					invertibleY := b.Have(
						"the component of Y is invertible",
						"invertible_fractional(field_ring(L), point_chart(A₀, A₁, P), COND(fst(P) = A₀, snd(Y), fst(Y)))",
						By(parts[1], PointComponent.At(ring, A0, A1, A01, P, Y, X)))
					b.Show(
						"the component of a product is the product of the components",
						first[1].Rw(),
						By(
							parts[0],
							first[3],
							invertibleY,
							products.At(
								b.TermAs[Set[A]]("COND(fst(P) = A₀, snd(X), fst(X))"),
								b.TermAs[Set[A]]("COND(fst(P) = A₀, snd(Y), fst(Y))"))))
				}))
			invertibles := a.Have(
				"an invertible pair extends to an invertible ideal, and its inverse to the inverse",
				Statement{
					Binders:    "∀X:prod(set(A), set(A)).",
					Hypotheses: []string{"«scInvertible»(X)"},
					Conclusion: "invertible_fractional(field_ring(L), «local», «extended»(X)) ∧ " +
						"«extended»(lattice_pair_inverse(field_ring(L), A₀, A₁, X)) = " +
						"fractional_inverse(field_ring(L), «local», «extended»(X))",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[_IdealPair]("X")
					invertible := b.Assume()
					read := b.Conjuncts(
						PointComponent.At(ring, A0, A1, A01, P, X, X),
						"the structure pair",
						"the product",
						"the inverse",
						"the invertible X")
					b.Show(
						"the component of an inverse is the inverse of the component",
						read[2].Rw(),
						By(invertible, read[3], inverses.At(b.TermAs[Set[A]]("COND(fst(P) = A₀, snd(X), fst(X))"))))
				}))
			others := a.Have(
				"another closed point extends to the local ring",
				"∀Q:prod(set(A), set(A)). «scPoint»(Q) ∧ Q ≠ P ⇒ «extended»(Q) = «local»",
				Derive(func(b *Argument) {
					Q := b.FixAs[_IdealPair]("Q")
					parts := b.Conjuncts(
						b.Assume(),
						"Q is a closed point",
						"it is not P")
					separated := b.Conjuncts(
						GroupPremises(curve, point, parts[0], parts[1], PointsSeparate.Read(L).At(k, A0, A1, A01, t, P, Q)),
						"its component lies in the chart",
						"and holds a function off P")
					u, witness := b.UnpackAs[A](separated[1], "u")
					holds := b.Conjuncts(
						witness,
						"the component holds u",
						"u lies off P")
					b.Show(
						"that function is a unit of the local ring",
						By(
							parts[0],
							parts[1],
							separated[0],
							holds[0],
							holds[1],
							unitIdeals.At(b.TermAs[Set[A]]("COND(fst(P) = A₀, snd(Q), fst(Q))"), u)))
				}))
			chartInL := a.Have(
				"and the chart lies in L",
				"point_chart(A₀, A₁, P) ⊆ L.carrier",
				By(subringChart, comm_ring.SubringSubset.At(ring, chart)))
			a.Show(
				"the laws of the extension",
				By(
					subringLocal,
					structure,
					multiplicative,
					invertibles,
					extendedPoint,
					insideLocal,
					proper,
					others,
					chartInL,
					biaffine_rational_point.PointIdealDef.At(A0, P)))
		}),
})}

// LocalPowerInjective — distinct integers give distinct powers of the maximal
// ideal at a closed point: it is invertible and proper in the local ring.
var LocalPowerInjective = localPowerInjectiveThm{family.Add(registry.ProofEntry{
	Name: "LocalPowerInjective",
	Key:  "prop_2c20057cfff0f8df",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀m n:int.",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(P)",
			"signed_ideal_power(field_ring(L), «local», «maximal», m) = " +
				"signed_ideal_power(field_ring(L), «local», «maximal», n)",
		},
		Conclusion: "m = n",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			m, n *Expr[Int],
			curve, point, equal Fact,
		) {
			local := a.Conjuncts(
				GroupPremises(curve, point, LocalExtension.Read(L).At(k, A0, A1, A01, t, P)),
				"the local ring is a subring",
				"the structure pair extends to it",
				"extension is multiplicative on invertible pairs",
				"it keeps invertible pairs",
				"P extends to the maximal ideal",
				"which lies in the local ring",
				"and misses one",
				"other closed points extend to the local ring",
				"the chart lies in L")
			invertible := a.Have(
				"the maximal ideal, the extension of the invertible P, is invertible",
				"invertible_fractional(field_ring(L), «local», «maximal»)",
				local[4].RwRev(),
				By(
					curve,
					point,
					closed_divisor.ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P),
					local[3].At(P)))
			a.Show(
				"the powers of a proper invertible ideal are distinct",
				By(
					local[0],
					invertible,
					local[5],
					local[6],
					equal,
					signed_ideal_power.SignedPowerInjective.Read(L).At(
						a.TermAs[Set[A]]("«local»"), a.TermAs[Set[A]]("«maximal»"), m, n)))
		}),
})}

// SignedPowerMap — a map multiplicative on c carries the integer powers of a
// pair of members of c to the integer powers of the images.
var SignedPowerMap = signedPowerMapThm{family.Add(registry.ProofEntry{
	Name: "SignedPowerMap",
	Key:  "prop_cc99a85b16866719",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀op₂:(B → B → B). ∀e₂:B. ∀h:(A → B). ∀x y:A. ∀n:int.",
		Hypotheses: []string{
			"h(e) = e₂",
			"∀u v:A. u ∈ c ∧ v ∈ c ⇒ h(op(u, v)) = op₂(h(u), h(v))",
			"x ∈ c ∧ y ∈ c",
		},
		Conclusion: "h(COND(&0 ≤ n, y ^ num_of_int(n), x ^ num_of_int(-n))) = " +
			"COND(&0 ≤ n, monoid_pow(op₂, e₂, h(y), num_of_int(n)), monoid_pow(op₂, e₂, h(x), num_of_int(-n)))",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			op2 *Arrow2[B, B, B],
			e2 *Expr[B],
			h *Arrow[A, B],
			x, y *Expr[A],
			n *Expr[Int],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"h keeps the identity",
				"h carries op to op₂ on c",
				"x lies in c",
				"y lies in c")
			identity, carries, xIn, yIn := parts[0], parts[1], parts[2], parts[3]
			powers := a.Have(
				"h carries powers of a member of c to powers",
				"∀z:A. z ∈ c ⇒ ∀k:num. h(z ^ k) = monoid_pow(op₂, e₂, h(z), k)",
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					zIn := b.Assume()
					member := b.MemberOf[on.C](z, zIn)
					b.Induct("k")
					b.Base(
						"both zeroth powers are identities",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(identity))
					b.Step(
						"h carries the one more factor of z to one more factor of h(z)",
						func(c *Argument, ih Fact) {
							power := c.TermAs[A]("z ^ k")
							source := c.Have(
								"z ^ suc(k) is z combined with z ^ k",
								"z ^ suc(k) = op(z, z ^ k)",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								Refl())
							target := c.Have(
								"and likewise on the second carrier",
								"monoid_pow(op₂, e₂, h(z), suc(k)) = op₂(h(z), monoid_pow(op₂, e₂, h(z), k))",
								Simp(Fwd(comm_monoid.MonoidPowDef.Inst[B]())),
								Refl())
							product := c.Have(
								"h carries this product",
								"h(op(z, z ^ k)) = op₂(h(z), h(z ^ k))",
								By(zIn, carries.At(z, power), comm_monoid.PowIn.Read(monoid).At(member, c.TermAs[Nat]("k"))))
							c.Show(
								"z ^ suc(k) goes to h(z) combined with h(z ^ k), which is one more factor of h(z)",
								CalcEq(
									Leg(
										c.TermAs[B]("h(op(z, z ^ k))"),
										"z ^ suc(k) is z combined with z ^ k",
										By(Normalized, source)),
									Leg(
										c.TermAs[B]("op₂(h(z), h(z ^ k))"),
										"h carries this product",
										By(product)),
									Leg(
										c.TermAs[B]("op₂(h(z), monoid_pow(op₂, e₂, h(z), k))"),
										"h carries the shorter power",
										By(Normalized, ih)),
									FinalLeg(
										"which is one more factor of h(z)",
										By(target))))
						})
				}))
			a.Cases(a.TermAs[Bool]("&0 ≤ n"))
			a.When(
				"at a nonnegative n the power is a power of y",
				func(b *Argument, nonnegative Fact) {
					b.Show(
						"and h carries it",
						By(Normalized, nonnegative, yIn, powers.At(y)))
				})
			a.Otherwise(
				"at a negative n it is a power of x",
				func(b *Argument, negative Fact) {
					b.Show(
						"and h carries it",
						By(Normalized, negative, xIn, powers.At(x)))
				})
		}),
})}

// LocalDivisorPower — the pair of a closed divisor extends to the signed power
// of the maximal ideal at minus its coefficient at P: extension is a homomorphism
// of the monoids, so it carries the product of the powers of the divisor's
// points to the product of their extensions, every factor off P is the unit, and
// the factor at P is the signed power.
var LocalDivisorPower = localDivisorPowerThm{family.Add(registry.ProofEntry{
	Name: "LocalDivisorPower",
	Key:  "prop_8b4194b095e785cf",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀E:(prod(set(A), set(A)) → int). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(E)",
			"«scPoint»(P)",
		},
		Conclusion: "«extended»(«scPair»(E)) = " +
			"signed_ideal_power(field_ring(L), «local», «maximal», -E(P))",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "extended", Text: "λZ:prod(set(A), set(A)). " +
				"    module_span(restrict_ring(field_ring(L), «local»), " +
				"        regular_module(field_ring(L)), " +
				"        COND(fst(P) = A₀, snd(Z), fst(Z)))"},
			{Name: "product", Text: "fractional_mul(field_ring(L), «local»)"},
			{Name: "ideals", Text: "{X:set(A) | " +
				"    submodule(restrict_ring(field_ring(L), «local»), regular_module(field_ring(L)), X)}"},
			{Name: "support", Text: "fun_support(int_of_num(0), E)"},
			{Name: "factor", Text: "λQ:prod(set(A), set(A)). «extended»(«scPower»(Q, E(Q)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E *Arrow[_IdealPair, Int],
			P *Expr[_IdealPair],
			curve, divisor, point Fact,
		) {
			local := a.TermAs[Set[A]]("«local»")
			products := a.Conjuncts(
				GroupPremises(curve, closed_divisor.ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")
			monoid, powers, pairOf := products[0], products[2], products[3]
			extension := a.Conjuncts(
				GroupPremises(curve, point, LocalExtension.Read(L).At(k, A0, A1, A01, t, P)),
				"the local ring is a subring",
				"the structure pair extends to it",
				"extension is multiplicative on invertible pairs",
				"it keeps invertible pairs and their inverses",
				"P extends to the maximal ideal",
				"which lies in the local ring",
				"and misses one",
				"other closed points extend to the local ring",
				"the chart lies in L")
			subringLocal, structure, multiplicative, invertibles, atPoint, others :=
				extension[0], extension[1], extension[2], extension[3], extension[4], extension[7]
			target := a.Have(
				"the fractional ideals of the local ring are a commutative monoid",
				"comm_monoid_on(«ideals», «product», «local»)",
				By(subringLocal, fractional_ideal.FractionalIdealsCommMonoid.Read(L).At(local)))
			openDivisor := a.Conjuncts(
				a.Unfolded(divisor, closed_divisor.ClosedDivisorDef),
				"the support of E is finite",
				"its pairs are closed points")
			finite, closed := openDivisor[0], openDivisor[1]
			overLine := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			data := a.Conjuncts(
				GroupPremises(overLine, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in L",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field",
				"the constants lie in both charts")
			inverseInvertible := a.Have(
				"the inverse of an invertible pair is invertible",
				"∀X:prod(set(A), set(A)). «scInvertible»(X) ⇒ «scInvertible»(«scInverse»(X))",
				Derive(func(b *Argument) {
					X := b.FixAs[_IdealPair]("X")
					invertible := b.Assume()
					b.Show(
						"the invertible pairs of the curve have inverses",
						By(
							data[0],
							data[1],
							invertible,
							invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, X)))
				}))
			carried := a.Have(
				"extension carries the product of invertible pairs",
				Statement{
					Binders:    "∀u v:prod(set(A), set(A)).",
					Hypotheses: []string{"u ∈ «scInvertibles»", "v ∈ «scInvertibles»"},
					Conclusion: "«extended»(«scMul»(u, v)) = «product»(«extended»(u), «extended»(v))",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[_IdealPair]("u"), b.FixAs[_IdealPair]("v")
					parts := b.Conjuncts(
						b.Assume(),
						"u is invertible",
						"v is invertible")
					b.Show(
						"multiplicative on invertible pairs",
						By(parts[0], parts[1], multiplicative.At(u, v)))
				}))
			extended := a.TermAs[Fun[_IdealPair, Set[A]]]("«extended»")
			product := a.TermAs[Fun2[Set[A], Set[A], Set[A]]]("«product»")
			values := a.Have(
				"extension carries the integer powers of an invertible pair to those of its extension",
				Statement{
					Binders:    "∀Q:prod(set(A), set(A)). ∀n:int.",
					Hypotheses: []string{"«scInvertible»(Q)"},
					Conclusion: "«extended»(«scPower»(Q, n)) = " +
						"COND(&0 ≤ n, " +
						"    monoid_pow(«product», " +
						"        «local», " +
						"        fractional_inverse(field_ring(L), «local», «extended»(Q)), " +
						"        num_of_int(n)), " +
						"    monoid_pow(«product», «local», «extended»(Q), num_of_int(-n)))",
				},
				Derive(func(b *Argument) {
					Q, n := b.FixAs[_IdealPair]("Q"), b.FixAs[Int]("n")
					invertible := b.Assume()
					keeps := b.Have(
						"the inverse extends to the inverse",
						"«extended»(«scInverse»(Q)) = fractional_inverse(field_ring(L), «local», «extended»(Q))",
						By(invertible, invertibles.At(Q)))
					memberships := b.Have(
						"Q and its inverse lie in the monoid",
						"Q ∈ «scInvertibles» ∧ «scInverse»(Q) ∈ «scInvertibles»",
						By(invertible, inverseInvertible.At(Q)))
					b.Show(
						"a homomorphism carries signed powers",
						keeps.RwRev(),
						By(
							structure,
							carried,
							memberships,
							Read(SignedPowerMap, monoid).At(
								product, local, extended, Q, b.TermAs[_IdealPair]("«scInverse»(Q)"), n)))
				}))
			localInverse := a.Have(
				"the local ring is its own inverse",
				"fractional_inverse(field_ring(L), «local», «local») = «local»",
				By(subringLocal, fractional_ideal.SubringInvertible.Read(L).At(local)))
			units := a.Have(
				"every power of another closed point extends to the local ring",
				"∀Q:prod(set(A), set(A)). ∀n:int. «scPoint»(Q) ∧ Q ≠ P ⇒ «extended»(«scPower»(Q, n)) = «local»",
				Derive(func(b *Argument) {
					Q, n := b.FixAs[_IdealPair]("Q"), b.FixAs[Int]("n")
					parts := b.Conjuncts(
						b.Assume(),
						"Q is a closed point",
						"it is not P")
					invertible := b.Have(
						"Q is invertible",
						"«scInvertible»(Q)",
						By(curve, parts[0], closed_divisor.ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, Q)))
					unit := b.Have(
						"Q extends to the local ring",
						"«extended»(Q) = «local»",
						By(parts[0], parts[1], others.At(Q)))
					value := b.Have(
						"so its powers are those of the unit",
						"«extended»(«scPower»(Q, n)) = "+
							"COND(&0 ≤ n, "+
							"    monoid_pow(«product», "+
							"        «local», "+
							"        fractional_inverse(field_ring(L), «local», «extended»(Q)), "+
							"        num_of_int(n)), "+
							"    monoid_pow(«product», «local», «extended»(Q), num_of_int(-n)))",
						By(invertible, values.At(Q, n)))
					b.Do(value.Rw(), unit.Rw(), localInverse.Rw())
					b.Show(
						"and every power of the unit is the unit",
						Simp(Fwd(Read(comm_monoid.IdentityPowOn, target))),
						Basic())
				}))
			pointInvertible := a.Have(
				"P is invertible",
				"«scInvertible»(P)",
				By(curve, point, closed_divisor.ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P)))
			pointPowers := a.Have(
				"the power of P at n extends to the signed power at −n",
				"∀n:int. «extended»(«scPower»(P, n)) = signed_ideal_power(field_ring(L), «local», «maximal», -n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Int]("n")
					value := b.Have(
						"the extension of the power is a power of the extension",
						"«extended»(«scPower»(P, n)) = "+
							"COND(&0 ≤ n, "+
							"    monoid_pow(«product», "+
							"        «local», "+
							"        fractional_inverse(field_ring(L), «local», «extended»(P)), "+
							"        num_of_int(n)), "+
							"    monoid_pow(«product», «local», «extended»(P), num_of_int(-n)))",
						By(pointInvertible, values.At(P, n)))
					b.Do(
						value.Rw(),
						atPoint.Rw(),
						Simp(Fwd(signed_ideal_power.SignedIdealPowerDef)))
					b.Cases(b.TermAs[Bool]("&0 < n"))
					b.When(
						"at a positive n both sides are the power of the inverse",
						func(c *Argument, positive Fact) {
							signs := c.Have(
								"the signs of n and −n",
								"&0 ≤ n ∧ ¬(&0 ≤ -n) ∧ --n = n",
								ByArith(positive))
							c.Show(
								"each side reads its branch",
								By(signs))
						})
					b.Otherwise(
						"at n ≤ 0",
						func(c *Argument, notPositive Fact) {
							c.Cases(c.TermAs[Bool]("n = int_of_num(0)"))
							c.When(
								"at 0 both sides are the zeroth power",
								func(d *Argument, zero Fact) {
									negation := d.Have(
										"−0 = 0",
										"-0 = int_of_num(0)",
										ByArith())
									d.Do(zero.Rw(), negation.Rw())
									d.Show(
										"the zeroth power is the local ring",
										Simp(Fwd(int_embed.OfNumRetract), Fwd(comm_monoid.MonoidPowDef)),
										Basic())
								})
							c.Otherwise(
								"at a negative n both sides are the power of the maximal ideal",
								func(d *Argument, nonzero Fact) {
									signs := d.Have(
										"the signs of n and −n",
										"¬(&0 ≤ n) ∧ &0 ≤ -n",
										ByArith(notPositive, nonzero))
									d.Show(
										"each side reads its branch",
										By(signs))
								})
						})
				}))
			closedPowers := a.Have(
				"a power of a closed point is an invertible pair, extending to a fractional ideal",
				Statement{
					Binders:    "∀Q:prod(set(A), set(A)). ∀n:int.",
					Hypotheses: []string{"«scPoint»(Q)"},
					Conclusion: "«scPower»(Q, n) ∈ «scInvertibles» ∧ «extended»(«scPower»(Q, n)) ∈ «ideals»",
				},
				Derive(func(b *Argument) {
					Q := b.FixAs[_IdealPair]("Q")
					b.FixAs[Int]("n")
					closedQ := b.Assume()
					inMonoid := b.Have(
						"the power is invertible",
						"«scPower»(Q, n) ∈ «scInvertibles»",
						By(closedQ, powers.At(Q)))
					power := b.TermAs[_IdealPair]("«scPower»(Q, n)")
					extendedInvertible := b.Have(
						"so its extension is invertible",
						"invertible_fractional(field_ring(L), «local», «extended»(«scPower»(Q, n)))",
						By(inMonoid, invertibles.At(power)))
					opened := b.Conjuncts(
						b.Unfolded(extendedInvertible, fractional_ideal.InvertibleFractionalDef),
						"it is a fractional ideal",
						"it multiplies with its inverse to the local ring")
					b.Show(
						"the power is invertible, and its extension is a fractional ideal of the local ring",
						By(inMonoid, opened[0]))
				}))
			onSupport := a.Have(
				"the support consists of closed points",
				"∀Q:prod(set(A), set(A)). Q ∈ «support» ⇒ «scPoint»(Q)",
				a.ForEach(func(Q *Expr[_IdealPair]) Action { return BySets(closed.At(Q)) }))
			termsIn := a.Have(
				"the terms of the product are invertible pairs",
				"∀Q:prod(set(A), set(A)). Q ∈ «support» ⇒ «scPower»(Q, E(Q)) ∈ «scInvertibles»",
				Derive(func(b *Argument) {
					Q := b.FixAs[_IdealPair]("Q")
					inSupport := b.Assume()
					b.Show(
						"a power of a closed point",
						By(inSupport, onSupport.At(Q), closedPowers.At(Q, E.Apply(Q))))
				}))
			factorsIn := a.Have(
				"the factors are fractional ideals",
				"∀Q:prod(set(A), set(A)). Q ∈ «support» ⇒ «factor»(Q) ∈ «ideals»",
				Derive(func(b *Argument) {
					Q := b.FixAs[_IdealPair]("Q")
					inSupport := b.Assume()
					b.Show(
						"extensions of powers of a closed point",
						By(inSupport, onSupport.At(Q), closedPowers.At(Q, E.Apply(Q))))
				}))
			offP := a.Have(
				"the factors off P are the unit",
				"∀Q:prod(set(A), set(A)). Q ∈ «support» ∧ Q ∉ «support» ∩ {P} ⇒ «factor»(Q) = «local»",
				Derive(func(b *Argument) {
					Q := b.FixAs[_IdealPair]("Q")
					parts := b.Conjuncts(
						b.Assume(),
						"Q lies on the support",
						"and off its part at P")
					notP := b.Have(
						"so Q is not P",
						"Q ≠ P",
						BySets(parts[0], parts[1]))
					b.Show(
						"a power of another closed point extends to the local ring",
						By(parts[0], notP, onSupport.At(Q), units.At(Q, E.Apply(Q))))
				}))
			pairFacts := a.Conjuncts(
				GroupPremises(divisor, pairOf.At(E)),
				"the pair is invertible",
				"the pair is the product of the powers")
			support := a.TermAs[Set[_IdealPair]]("«support»")
			near := a.TermAs[Set[_IdealPair]]("«support» ∩ {P}")
			factor := a.TermAs[Fun[_IdealPair, Set[A]]]("«factor»")
			carriedFold := a.Have(
				"extension carries the product of the powers to the product of the factors",
				"«extended»(«scPair»(E)) = module_sum(«product», «local», «support», «factor»)",
				pairFacts[1].Rw(),
				By(
					structure,
					carried,
					finite,
					termsIn,
					module.ModuleSumMonoidHomomorphism.Read(monoid).At(
						product,
						local,
						extended,
						support,
						a.TermAs[Fun[_IdealPair, _IdealPair]]("λQ:prod(set(A), set(A)). «scPower»(Q, E(Q))"))))
			part := a.Have(
				"the part of the support at P lies in the support",
				"«support» ∩ {P} ⊆ «support»",
				BySets())
			narrowed := a.Have(
				"the factors off P drop out of the product",
				"module_sum(«product», «local», «support», «factor») = "+
					"module_sum(«product», «local», «support» ∩ {P}, «factor»)",
				By(
					finite,
					part,
					factorsIn,
					offP,
					module.ModuleSumSupportMonoid.Read(target).At(support, near, factor)))
			single := a.Have(
				"that part lies in {P}",
				"«support» ∩ {P} ⊆ {P}",
				BySets())
			factorAtP := a.Have(
				"the factor at P is a fractional ideal",
				"«factor»(P) ∈ «ideals»",
				By(point, closedPowers.At(P, E.Apply(P))))
			offSupport := a.Have(
				"and the unit should P lie off the support",
				"P ∉ «support» ∩ {P} ⇒ «factor»(P) = «local»",
				Derive(func(b *Argument) {
					off := b.Assume()
					zero := b.Have(
						"E vanishes at P",
						"E(P) = int_of_num(0)",
						BySets(off))
					atZero := b.Have(
						"and the power of P at 0 is the structure pair",
						"«scPower»(P, int_of_num(0)) = (A₀, A₁)",
						By(point, powers.At(P)))
					b.Show(
						"which extends to the local ring",
						zero.Rw(),
						atZero.Rw(),
						By(structure))
				}))
			one := a.Have(
				"so the product over that part is the factor at P",
				"module_sum(«product», «local», «support» ∩ {P}, «factor») = «factor»(P)",
				By(single, factorAtP, offSupport, module.ModuleSumSingleMonoid.Read(target).At(near, P, factor)))
			a.Show(
				"the pair extends to the factor at P, a signed power",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("module_sum(«product», «local», «support», «factor»)"),
						"extension carries the product of the powers",
						By(carriedFold)),
					Leg(
						a.TermAs[Set[A]]("module_sum(«product», «local», «support» ∩ {P}, «factor»)"),
						"only the part at P remains",
						By(narrowed)),
					Leg(
						a.TermAs[Set[A]]("«factor»(P)"),
						"which is the factor at P",
						By(one)),
					FinalLeg(
						"the signed power at −E(P)",
						By(pointPowers.At(E.Apply(P))))))
		}),
})}

// ClosedDivisorLocalPower — the coefficient of a principal divisor at a closed
// point is the order there: when the pair of D is f⁻¹ times the structure pair,
// f times the local ring is the signed power of the maximal ideal at D(P). The
// pair of D extends to f⁻¹ times the local ring, so the pair of −D, its inverse,
// extends to f times the local ring, and LocalDivisorPower reads that at −D.
var ClosedDivisorLocalPower = closedDivisorLocalPowerThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorLocalPower",
	Key:  "prop_31f14128f0d3253b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t f:A. " +
			"∀D:(prod(set(A), set(A)) → int). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
			"«scPoint»(P)",
			"f ∈ L.carrier",
			"f ≠ L.zero",
			"«scPair»(D) = lattice_pair_scale(L.inv(f), (A₀, A₁))",
		},
		Conclusion: "image(L.mul(f), «local») = " +
			"signed_ideal_power(field_ring(L), «local», «maximal», D(P))",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "extended", Text: "λZ:prod(set(A), set(A)). " +
				"    module_span(restrict_ring(field_ring(L), «local»), " +
				"        regular_module(field_ring(L)), " +
				"        COND(fst(P) = A₀, snd(Z), fst(Z)))"},
			{Name: "scaled", Text: "lattice_pair_scale(L.inv(f), (A₀, A₁))"},
			{Name: "negative", Text: "λQ:prod(set(A), set(A)). -D(Q)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t, f *Expr[A],
			D *Arrow[_IdealPair, Int],
			P *Expr[_IdealPair],
			curve, divisor, point, fInL, nonzero, principal Fact,
		) {
			local := a.TermAs[Set[A]]("«local»")
			extension := a.Conjuncts(
				GroupPremises(curve, point, LocalExtension.Read(L).At(k, A0, A1, A01, t, P)),
				"the local ring is a subring",
				"the structure pair extends to it",
				"extension is multiplicative on invertible pairs",
				"it keeps invertible pairs and their inverses",
				"P extends to the maximal ideal",
				"which lies in the local ring",
				"and misses one",
				"other closed points extend to the local ring",
				"the chart lies in L")
			subringLocal, structure, invertibles, chartInL :=
				extension[0], extension[1], extension[3], extension[8]
			negation := a.Conjuncts(
				GroupPremises(curve, divisor, closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, D)),
				"−D is a closed divisor",
				"the pair of D is invertible",
				"the pair of −D is its inverse",
				"the degree of −D is the opposite")
			negative, invertiblePair, inversePair := negation[0], negation[1], negation[2]
			opposite := a.Have(
				"the negative of −D(P) is D(P)",
				"--D(P) = D(P)",
				ByArith())
			atNegative := a.Simplified(
				GroupPremises(
					negation[0],
					curve,
					point,
					LocalDivisorPower.Read(L).At(k, A0, A1, A01, t, a.TermAs[Fun[_IdealPair, Int]]("«negative»"), P)),
				Fwd(opposite))
			fIn := a.MemberOf[on.L](f, fInL)
			inverse := field.InvIn.Read(L).At(fIn)
			inverseFacts := a.Conjuncts(
				a.Have(
					"f⁻¹ is nonzero, with inverse f",
					"L.inv(f) ≠ L.zero ∧ L.inv(L.inv(f)) = f",
					By(nonzero, field.InvEqZeroOn.Read(L).At(fIn), field.InvInvOn.Read(L).At(fIn))),
				"f⁻¹ is nonzero",
				"its inverse is f")
			inverseNonzero, inverseInverse := inverseFacts[0], inverseFacts[1]
			component := a.Have(
				"the component of the scaled pair at P is the scaled chart",
				"COND(fst(P) = A₀, snd(«scaled»), fst(«scaled»)) = image(L.mul(L.inv(f)), point_chart(A₀, A₁, P))",
				Simp(
					Fwd(biaffine_rational_point.PointChartDef),
					Fwd(invertible_lattice_pair.LatticePairScaleDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				Derive(func(b *Argument) {
					b.Cases(b.Term("fst(P) = A₀"))
					b.When(
						"off chart 0 it is the second",
						func(c *Argument, whole Fact) {
							c.Show(
								"read at A₁",
								By(whole))
						})
					b.Otherwise(
						"on chart 0 it is the first",
						func(c *Argument, proper Fact) {
							c.Show(
								"read at A₀",
								By(proper))
						})
				}))
			linear := a.Have(
				"multiplying by f⁻¹ is linear over the local ring",
				"module_homomorphism(restrict_ring(field_ring(L), «local»), "+
					"    regular_module(field_ring(L)), "+
					"    regular_module(field_ring(L)), "+
					"    L.mul(L.inv(f)))",
				By(subringLocal, field_extension.ScaleLinear.Read(L).At(local, inverse)))
			scalars := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), «local»)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			spansChart := a.Simplified(
				structure,
				Fwd(pairs.Fst),
				Fwd(pairs.Snd),
				Rev(biaffine_rational_point.PointChartDef))
			scaledSpan := a.Simplified(
				GroupPremises(
					linear,
					extension[8],
					linear_independence.HomSpan.At(
						scalars,
						vectors,
						vectors,
						a.TermAs[Fun[A, A]]("L.mul(L.inv(f))"),
						a.TermAs[Set[A]]("point_chart(A₀, A₁, P)"))),
				Fwd(spansChart))
			extendedPair := a.Have(
				"the pair of D extends to f⁻¹ times the local ring",
				"«extended»(«scPair»(D)) = image(L.mul(L.inv(f)), «local»)",
				principal.Rw(),
				component.Rw(),
				By(linear, chartInL, scaledSpan))
			localInL := a.Have(
				"the local ring lies in L",
				"«local» ⊆ L.carrier",
				By(subringLocal, comm_ring.SubringSubset.At(a.TermAs[RingOps[A]]("field_ring(L)"), local)))
			localInverse := a.Have(
				"the local ring is its own inverse",
				"fractional_inverse(field_ring(L), «local», «local») = «local»",
				By(subringLocal, fractional_ideal.SubringInvertible.Read(L).At(local)))
			scaleInverse := a.Have(
				"so the inverse of f⁻¹ times the local ring is f times it",
				"fractional_inverse(field_ring(L), «local», image(L.mul(L.inv(f)), «local»)) = "+
					"image(L.mul(f), «local»)",
				By(
					inverseNonzero,
					inverseInverse,
					localInL,
					localInverse,
					fractional_ideal.FractionalInverseScale.Read(L).At(local, local, inverse)))
			a.Show(
				"f times the local ring is the extension of the pair of −D",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("fractional_inverse(field_ring(L), «local», image(L.mul(L.inv(f)), «local»))"),
						"it is the inverse of f⁻¹ times the local ring",
						By(scaleInverse)),
					Leg(
						a.TermAs[Set[A]]("fractional_inverse(field_ring(L), «local», «extended»(«scPair»(D)))"),
						"which the pair of D extends to",
						extendedPair.Rw(),
						Basic()),
					Leg(
						a.TermAs[Set[A]]("«extended»(lattice_pair_inverse(field_ring(L), A₀, A₁, «scPair»(D)))"),
						"extension keeps inverses",
						By(invertiblePair, invertibles.At(a.TermAs[_IdealPair]("«scPair»(D)")))),
					Leg(
						a.TermAs[Set[A]]("«extended»(«scPair»(«negative»))"),
						"the pair of −D is that inverse",
						inversePair.Rw(),
						Basic()),
					FinalLeg(
						"and it extends to the signed power at D(P)",
						By(curve, divisor, negative, point, atNegative))))
		}),
})}

// GeneratorOrderOne — at a point whose ideal on chart zero is a prime generated
// by u and v, with v·g = u·h for some g off the point, u has order one: g is a
// unit of the local ring, so v is a multiple of u there and the ideal of the
// local ring is u times the local ring, the first of its distinct powers.
var GeneratorOrderOne = generatorOrderOneThm{family.Add(registry.ProofEntry{
	Name: "GeneratorOrderOne",
	Key:  "prop_3d409ef196571e84",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀A₀ A₁:set(A). ∀P:prod(set(A), set(A)). ∀u v g h:A.",
		Hypotheses: []string{
			"subring(field_ring(L), A₀)",
			"prime_ideal(restrict_ring(field_ring(L), A₀), fst(P))",
			"fst(P) = ideal_span(restrict_ring(field_ring(L), A₀), {u, v})",
			"u ∈ A₀",
			"v ∈ A₀",
			"g ∈ A₀",
			"h ∈ A₀",
			"v * g = u * h",
			"g ∉ fst(P)",
			"u ≠ L.zero",
		},
		Conclusion: "regular_point_order(field_ring(L), A₀, A₁, P, u) = &1",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			A0, A1 *Expr[Set[A]],
			P *Expr[Prod[Set[A], Set[A]]],
			u, v, g, h *Expr[A],
			subringA0, prime, generated, uIn, vIn, gIn, hIn, related, gOff, uNonzero Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			chartRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀)")
			point := a.TermAs[Set[A]]("fst(P)")
			scale := a.TermAs[Fun[A, A]]("L.mul(u)")
			pointIdeal := a.Have(
				"the point's ideal is an ideal of A₀ missing one",
				"ring_ideal(restrict_ring(field_ring(L), A₀), fst(P)) ∧ L.one ∉ fst(P)",
				By(
					prime,
					ring_ideal.PrimeIdealIdeal.At(chartRing, point),
					ring_ideal.PrimeIdealProper.At(chartRing, point)))
			proper := a.Have(
				"so it is not all of A₀",
				"fst(P) ≠ A₀",
				By(Normalized, pointIdeal, subringA0, comm_ring.SubringOne.At(ring, A0)))
			localData := a.Conjuncts(
				GroupPremises(subringA0, prime, subring_localization.LocalRingSubring.Read(L).At(A0, point)),
				"the local ring is a subring of L",
				"holding A₀",
				"in which every element of A₀ off the point is a unit")
			subringLocal, chartInLocal, units := localData[0], localData[1], localData[2]
			O, localDef := a.LetAs[Set[A]]("O", "subring_localization(field_ring(L), A₀, fst(P))")
			localRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), O)")
			maximal := a.TermAs[Set[A]]("ideal_span(restrict_ring(field_ring(L), O), fst(P))")
			multiples := a.TermAs[Set[A]]("ideal_span(restrict_ring(field_ring(L), O), {u})")
			image := a.TermAs[Set[A]]("image(L.mul(u), O)")
			localRingOn := a.Have(
				"the local ring is a ring under the operations of L",
				"comm_ring_on(restrict_ring(field_ring(L), O))",
				By(subringLocal, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(O)))
			pointInChart := a.Have(
				"the point lies in A₀",
				"fst(P) ⊆ A₀",
				By(pointIdeal, ring_ideal.IdealSubset.At(chartRing, point)))
			members := a.Have(
				"u, v, g and h lie in the local ring and in L, and so does the point",
				"u ∈ O ∧ "+
					"v ∈ O ∧ "+
					"g ∈ O ∧ "+
					"h ∈ O ∧ "+
					"u ∈ L.carrier ∧ "+
					"v ∈ L.carrier ∧ "+
					"g ∈ L.carrier ∧ "+
					"h ∈ L.carrier ∧ "+
					"fst(P) ⊆ O ∧ "+
					"O ⊆ L.carrier",
				BySets(
					uIn,
					vIn,
					gIn,
					hIn,
					chartInLocal,
					pointInChart,
					subringLocal,
					comm_ring.SubringSubset.At(ring, O)))
			generators := a.Have(
				"u and v lie on the point",
				"u ∈ fst(P) ∧ v ∈ fst(P)",
				BySets(generated, ring_ideal.SpanContains.At(chartRing, a.TermAs[Set[A]]("{u, v}"))))
			maximalIdeal := a.Have(
				"the point spans an ideal of the local ring holding it",
				"ring_ideal(restrict_ring(field_ring(L), O), "+
					"    ideal_span(restrict_ring(field_ring(L), O), fst(P))) ∧ "+
					"fst(P) ⊆ ideal_span(restrict_ring(field_ring(L), O), fst(P))",
				By(
					members,
					ring_ideal.SpanIdeal.Read(localRingOn).At(point),
					ring_ideal.SpanContains.At(localRing, point)))
			uInMaximal := a.Have(
				"so u lies in it",
				"u ∈ ideal_span(restrict_ring(field_ring(L), O), fst(P))",
				BySets(generators, maximalIdeal))
			multiplesIn := a.Have(
				"each multiple of u by the local ring lies in it",
				"∀o:A. o ∈ O ⇒ u * o ∈ ideal_span(restrict_ring(field_ring(L), O), fst(P))",
				Derive(func(b *Argument) {
					o := b.FixAs[A]("o")
					inLocal := b.Assume()
					inField := b.Have(
						"o lies in L",
						"o ∈ L.carrier",
						BySets(inLocal, members))
					commute := b.Have(
						"the product commutes",
						"u * o = o * u",
						ByArith(L, inField, members))
					b.Show(
						"an ideal absorbs multiples",
						By(
							Normalized,
							commute,
							inLocal,
							uInMaximal,
							maximalIdeal,
							ring_ideal.IdealMul.At(localRing, maximal, o, u)))
				}))
			imageIn := a.Have(
				"so u times the local ring lies in the ideal of the point",
				"image(L.mul(u), O) ⊆ ideal_span(restrict_ring(field_ring(L), O), fst(P))",
				By(multiplesIn, set_image.ImageSubsetIff.At(scale, O, maximal)))
			gUnit := a.Have(
				"g is a unit of the local ring",
				"L.inv(g) ∈ O ∧ g * L.inv(g) = L.one",
				By(gIn, gOff, units.At(g)))
			unitParts := a.Conjuncts(
				gUnit,
				"the inverse of g lies in the local ring",
				"g times its inverse is one")
			quotient := a.TermAs[A]("h * L.inv(g)")
			quotientIn := a.Have(
				"h over g lies in the local ring",
				"h * L.inv(g) ∈ O",
				By(members, gUnit, subringLocal, comm_ring.SubringMul.At(ring, O, h, a.TermAs[A]("L.inv(g)"))))
			inverseInField := a.Have(
				"the inverse of g lies in L",
				"L.inv(g) ∈ L.carrier",
				BySets(gUnit, members))
			vMultiple := a.Have(
				"v is h over g times u",
				"v = h * L.inv(g) * u",
				ByArith(
					L,
					Scaled(a.TermAs[A]("L.inv(g)"), related),
					Scaled(v, unitParts[1]),
					members,
					inverseInField))
			singleton := a.Have(
				"u lies in the local ring",
				"{u} ⊆ O",
				BySets(members))
			multiplesIdeal := a.Have(
				"the multiples of u form an ideal of the local ring",
				"ring_ideal(restrict_ring(field_ring(L), O), ideal_span(restrict_ring(field_ring(L), O), {u}))",
				By(singleton, ring_ideal.SpanIdeal.Read(localRingOn).At(a.TermAs[Set[A]]("{u}"))))
			uInMultiples := a.Have(
				"holding u",
				"u ∈ ideal_span(restrict_ring(field_ring(L), O), {u})",
				BySets(ring_ideal.SpanContains.At(localRing, a.TermAs[Set[A]]("{u}"))))
			vInMultiples := a.Have(
				"which holds v",
				"v ∈ ideal_span(restrict_ring(field_ring(L), O), {u})",
				By(
					vMultiple,
					quotientIn,
					multiplesIdeal,
					uInMultiples,
					ring_ideal.IdealMul.At(localRing, multiples, quotient, u)))
			contraction := a.Have(
				"its part in A₀ is an ideal of A₀",
				"ring_ideal(restrict_ring(field_ring(L), A₀), "+
					"    A₀ ∩ ideal_span(restrict_ring(field_ring(L), O), {u}))",
				By(
					L,
					subringA0,
					chartInLocal,
					multiplesIdeal,
					ring_ideal.IdealContraction.At(ring, A0, O, multiples)))
			contractionHolds := a.Have(
				"holding u and v",
				"{u, v} ⊆ A₀ ∩ ideal_span(restrict_ring(field_ring(L), O), {u})",
				BySets(uIn, vIn, uInMultiples, vInMultiples))
			spanIn := a.Have(
				"so holding the ideal they generate in A₀",
				"ideal_span(restrict_ring(field_ring(L), A₀), {u, v}) ⊆ "+
					"A₀ ∩ ideal_span(restrict_ring(field_ring(L), O), {u})",
				By(
					contraction,
					contractionHolds,
					ring_ideal.SpanLeast.At(
						chartRing,
						a.TermAs[Set[A]]("{u, v}"),
						a.TermAs[Set[A]]("A₀ ∩ ideal_span(restrict_ring(field_ring(L), O), {u})"))))
			pointInMultiples := a.Have(
				"which is the point",
				"fst(P) ⊆ ideal_span(restrict_ring(field_ring(L), O), {u})",
				BySets(generated, spanIn))
			maximalInMultiples := a.Have(
				"and so the ideal of the point in the local ring",
				"ideal_span(restrict_ring(field_ring(L), O), fst(P)) ⊆ "+
					"ideal_span(restrict_ring(field_ring(L), O), {u})",
				By(multiplesIdeal, pointInMultiples, ring_ideal.SpanLeast.At(localRing, point, multiples)))
			multiplesForm := a.Have(
				"the multiples of u are its products with the local ring",
				"ideal_span(restrict_ring(field_ring(L), O), {u}) = {q:A | ∃r:A. r ∈ O ∧ q = r * u}",
				By(members, ring_ideal.PrincipalIdealMultiples.Read(localRingOn).AsFact().At(u)))
			multiplesInImage := a.Have(
				"each of them is u times an element of the local ring",
				"∀q:A. q ∈ ideal_span(restrict_ring(field_ring(L), O), {u}) ⇒ q ∈ image(L.mul(u), O)",
				Derive(func(b *Argument) {
					b.FixAs[A]("q")
					inMultiples := b.Assume()
					product := b.Have(
						"q is a product with u",
						"∃r:A. r ∈ O ∧ q = r * u",
						BySets(inMultiples, multiplesForm))
					r, rData := b.UnpackAs[A](product, "r")
					inField := b.Have(
						"r lies in L",
						"r ∈ L.carrier",
						BySets(rData, members))
					commute := b.Have(
						"the product commutes",
						"r * u = u * r",
						ByArith(L, inField, members))
					b.Show(
						"so q is the image of r",
						By(Normalized, rData, commute, set_image.FunInImage.At(scale, O, r)))
				}))
			reverse := a.Have(
				"and u times the local ring holds it",
				"ideal_span(restrict_ring(field_ring(L), O), fst(P)) ⊆ image(L.mul(u), O)",
				BySets(maximalInMultiples, multiplesInImage))
			equal := a.Have(
				"so the ideal of the point in the local ring is u times the local ring",
				"ideal_span(restrict_ring(field_ring(L), O), fst(P)) = image(L.mul(u), O)",
				By(imageIn, reverse, set_order.SubsetAntisym.At(maximal, image)))
			invertible := a.Have(
				"which is invertible, u being nonzero",
				"invertible_fractional(field_ring(L), O, ideal_span(restrict_ring(field_ring(L), O), fst(P)))",
				By(
					equal,
					subringLocal,
					members,
					uNonzero,
					fractional_ideal.InvertibleScale.Read(L).AsFact().At(O, O, u)))
			properMaximal := a.Have(
				"and proper",
				"L.one ∉ ideal_span(restrict_ring(field_ring(L), O), fst(P))",
				By(
					Normalized,
					L,
					subringA0,
					prime,
					localDef,
					subring_localization.LocalIdealProper.Read(L).At(A0, point)))
			maximalInLocal := a.Have(
				"lying in the local ring",
				"ideal_span(restrict_ring(field_ring(L), O), fst(P)) ⊆ O ∧ "+
					"ideal_span(restrict_ring(field_ring(L), O), fst(P)) ⊆ L.carrier",
				BySets(maximalIdeal, ring_ideal.IdealSubset.At(localRing, maximal), members))
			fractional := a.Have(
				"so a fractional ideal of the local ring",
				"submodule(restrict_ring(field_ring(L), O), "+
					"    regular_module(field_ring(L)), "+
					"    ideal_span(restrict_ring(field_ring(L), O), fst(P)))",
				By(
					subringLocal,
					maximalIdeal,
					maximalInLocal,
					fractional_ideal.IntegralIdealFractional.Read(L).At(O, maximal)))
			powerOne := a.Have(
				"the first power under the product of fractional ideals is the product with the unit ideal",
				"monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), O, X, Y), "+
					"    O, "+
					"    ideal_span(restrict_ring(field_ring(L), O), fst(P)), "+
					"    1) = "+
					"fractional_mul(field_ring(L), O, ideal_span(restrict_ring(field_ring(L), O), fst(P)), O)",
				Simp(Fwd(nat_arith.OneIsSucZero), Fwd(comm_monoid.MonoidPowDef)),
				Basic())
			positive := a.Have(
				"one is not negative",
				"0 ≤ int_of_num(1)",
				ByArith())
			firstPower := a.Have(
				"so the first signed power is the ideal itself",
				"signed_ideal_power(field_ring(L), O, ideal_span(restrict_ring(field_ring(L), O), fst(P)), &1) = "+
					"ideal_span(restrict_ring(field_ring(L), O), fst(P))",
				Simp(Fwd(signed_ideal_power.SignedIdealPowerDef), Fwd(int_embed.OfNumRetract)),
				By(
					L,
					powerOne,
					positive,
					subringLocal,
					fractional,
					maximalInLocal,
					members,
					fractional_ideal.FractionalMulComm.Read(L).At(O, maximal, O),
					fractional_ideal.FractionalMulOne.Read(L).At(O, maximal)))
			localForm := a.Have(
				"the local ring of the point is the local ring at its ideal on chart zero",
				"point_local_ring(field_ring(L), A₀, A₁, P) = O ∧ point_ideal(A₀, P) = fst(P)",
				By(
					Normalized,
					proper,
					localDef,
					regular_point.PointLocalRingDef.At(ring, A0, A1, P),
					biaffine_rational_point.PointOnChartZero.At(A0, A1, P)))
			orderChoice := a.Have(
				"the order is the choice of a power of the ideal of the point that u times the local ring is",
				"regular_point_order(field_ring(L), A₀, A₁, P, u) = "+
					"(εn:int. "+
					"    image(L.mul(u), O) = "+
					"    signed_ideal_power(field_ring(L), O, ideal_span(restrict_ring(field_ring(L), O), fst(P)), n))",
				By(Normalized, localForm, regular_point.RegularPointOrderDef.At(ring, A0, A1, P, u)))
			firstPowerImage := a.Have(
				"u times the local ring is the first power",
				"image(L.mul(u), O) = "+
					"signed_ideal_power(field_ring(L), O, ideal_span(restrict_ring(field_ring(L), O), fst(P)), 1)",
				By(equal, firstPower))
			chosen := a.Have(
				"so the chosen power is one u times the local ring is",
				"image(L.mul(u), O) = "+
					"signed_ideal_power(field_ring(L), "+
					"    O, "+
					"    ideal_span(restrict_ring(field_ring(L), O), fst(P)), "+
					"    regular_point_order(field_ring(L), A₀, A₁, P, u))",
				By(orderChoice, firstPowerImage))
			order := a.TermAs[Int]("regular_point_order(field_ring(L), A₀, A₁, P, u)")
			a.Show(
				"the powers of an invertible proper ideal are distinct",
				By(
					subringLocal,
					invertible,
					maximalInLocal,
					properMaximal,
					chosen,
					equal,
					firstPower,
					signed_ideal_power.SignedPowerInjective.Read(L).At(O, maximal, order, a.TermAs[Int]("&1"))))
		}),
})}
