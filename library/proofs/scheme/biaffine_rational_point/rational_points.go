// rational_points.go — the rational points of a biaffine datum. Over a
// subfield k a point on chart 0 is a k-algebra map A₀ → k, its chart sets
// are ideals and the proper ones maximal, it lies on both charts exactly
// when t does not vanish at it, and its ideal pair is a lattice pair inside
// the structure pair, of colength one on each chart the point lies on. A
// point's chart and its ideal there are read off whether its first
// component is all of A₀, and at a rational point inside a field the chart
// is a subring holding k where the ideal is that of a k-rational point.

package biaffine_rational_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Points and k-algebra maps
// ---------------------------------------------------------------------------

// RationalPointMaximal — each chart ideal of a rational point is either
// the chart or a maximal ideal of it.
var RationalPointMaximal = rationalPointMaximalThm{family.Add(registry.ProofEntry{
	Name: "RationalPointMaximal",
	Key:  "prop_5583c4293134d073",
	Reading: "A proper chart ideal has residue field k: every member of the chart is a member of k " +
		"modulo it. k ⊆ A₀ is load-bearing: the residue y of an element outside the ideal is a nonzero " +
		"member of k, and its inverse must lie in the chart for one to fall into the larger ideal. " +
		"Only with k a field inside the chart does the clause mean residue field k: the datum A₀ = " +
		"ℤ₍ₚ₎, t = p, R = A₁ = ℚ, s = 1/p with k = ℚ, which is not inside A₀, has the rational point " +
		"(p²ℤ₍ₚ₎, ℚ), each member of ℤ₍ₚ₎ being its own residue, and p²ℤ₍ₚ₎ is proper but not maximal.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"biaffine_rational_point(R, k, A₀, A₁, P)",
		},
		Conclusion: "(¬(fst(P) = A₀) ⇒ maximal_ideal(restrict_ring(R, A₀), fst(P))) ∧ " +
			"(¬(snd(P) = A₁) ⇒ maximal_ideal(restrict_ring(R, A₁), snd(P)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			assumptions := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in A₀",
				"k lies in A₁",
				"P is a rational point")
			datum, subfieldK, kIn0, kIn1, point :=
				assumptions[0], assumptions[1], assumptions[2], assumptions[3], assumptions[4]
			charts := a.Conjuncts(
				a.Unfolded(datum, lattice_pair.BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring, subring0, subring1 := charts[0], charts[1], charts[2]
			pointClauses := a.Conjuncts(
				a.Unfolded(point, BiaffineRationalPointDef),
				"the chart-0 ideal is the whole chart, or the ideal of a k-rational point of it",
				"the chart-1 ideal is the whole chart, or the ideal of a k-rational point of it",
				"the point lies on some chart",
				"the two chart ideals generate the same ideal of R",
				"on both charts the generated ideal is proper")
			a.Do(SplitConj(
				Case(
					"a proper chart-0 ideal is maximal",
					Derive(func(b *Argument) {
						proper := b.Assume()
						b.Show(
							"being proper, it is the ideal of a k-rational point of the "+
								"chart, and residues in a field inside the chart make it maximal",
							By(
								Normalized,
								ring,
								subfieldK,
								subring0,
								kIn0,
								proper,
								pointClauses[0],
								quotient_ring.FieldResiduesMaximal.At(R, k, inv, A0, b.TermAs[Set[A]]("fst(P)"))))
					})),
				Case(
					"a proper chart-1 ideal is maximal",
					Derive(func(b *Argument) {
						proper := b.Assume()
						b.Show(
							"being proper, it is the ideal of a k-rational point of the "+
								"chart, and residues in a field inside the chart make it maximal",
							By(
								Normalized,
								ring,
								subfieldK,
								subring1,
								kIn1,
								proper,
								pointClauses[1],
								quotient_ring.FieldResiduesMaximal.At(R, k, inv, A1, b.TermAs[Set[A]]("snd(P)"))))
					}))))
		}),
})}

// RationalPointHomomorphism — the rational points on chart 0 are the
// k-algebra maps φ : A₀ → k: the point of φ is its kernel in chart 0 and,
// in chart 1, the members of A₁ in the ideal that kernel generates in R.
// A proper chart-0 ideal with residues in k is the kernel of its residue
// map (FieldResiduesHomomorphism), and the chart-1 ideal is the meet of
// A₁ with the ideal it generates: a whole chart 1 puts one in that ideal,
// and a proper chart-1 ideal is maximal (RationalPointMaximal) inside the
// meet, which excludes one. Conversely the kernel of φ is proper with
// residues in k (KernelFieldResidues), and its meet with A₁ generates the
// same ideal of R (RingAwaySpanOfContraction). The meet is all of A₁ when
// φ(t) = zero, t then a unit of R inside that ideal; otherwise the ideal
// the kernel generates in A₀[1/t] = R is proper with residues in k
// (KernelSpanAwayFieldResidues), and the meet inherits both.
var RationalPointHomomorphism = rationalPointHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "RationalPointHomomorphism",
	Key:  "prop_80a5882db9708960",
	Reading: "Both k ⊆ A₀ and k ⊆ A₁ are load-bearing: φ is the identity on k, and the residue " +
		"of a member of A₁ is its value, which must lie in A₁. ⇐ also uses R = ring_away(R, A₁, " +
		"s): it is what makes the chart-1 ideal A₁ ∩ ⟨ker φ⟩ generate the same ideal of R as ker φ.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
		},
		Conclusion: "biaffine_rational_point(R, k, A₀, A₁, P) ∧ ¬(fst(P) = A₀) ⇔ " +
			"∃φ:(A → A). " +
			"    ring_homomorphism(restrict_ring(R, A₀), restrict_ring(R, k), φ) ∧ " +
			"    (∀c:A. c ∈ k ⇒ φ(c) = c) ∧ " +
			"    P = (ring_kernel(R.zero, A₀, φ), A₁ ∩ ideal_span(R, ring_kernel(R.zero, A₀, φ)))",
		Abbrev: Abbrev{
			{Name: "E", Text: "ideal_span(R, ring_kernel(R.zero, A₀, φ))"},
			{Name: "J", Text: "A₁ ∩ «E»"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			assumptions := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in A₀",
				"k lies in A₁")
			datum, subfieldK, kIn0, kIn1 := assumptions[0], assumptions[1], assumptions[2], assumptions[3]
			charts := a.Conjuncts(
				a.Unfolded(datum, lattice_pair.BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring, subring0, subring1, tIn0, sIn1, inverse, away0, away1 :=
				charts[0], charts[1], charts[2], charts[3], charts[4], charts[5], charts[6], charts[7]
			R0, R1 := a.TermAs[RingOps[A]]("restrict_ring(R, A₀)"), a.TermAs[RingOps[A]]("restrict_ring(R, A₁)")
			powersOfS := a.TermAs[Set[A]]("monoid_powers(R.mul, R.one, s)")
			inclusion := a.TermAs[Fun[A, A]]("λx:A. x")
			localizations := a.Have(
				"both chart inclusions present R as their localization",
				"is_localization_on(restrict_ring(R, A₀), monoid_powers(R.mul, R.one, t), R, λx:A. x) ∧ "+
					"is_localization_on(restrict_ring(R, A₁), monoid_powers(R.mul, R.one, s), R, λx:A. x)",
				By(datum, lattice_pair.BiaffineChartLocalization.At(R, A0, A1, t, s)))
			secondInclusion := a.Have(
				"so the inclusion of A₁ into R is a ring homomorphism",
				"ring_homomorphism(restrict_ring(R, A₁), R, λx:A. x)",
				By(localizations, ring_localization.IsLocalizationOnDef.At(R1, powersOfS, R, inclusion)))
			meetsChart1 := a.Have(
				"an ideal of R meets A₁ in an ideal of A₁",
				"∀X:set(A). ring_ideal(R, X) ⇒ ring_ideal(restrict_ring(R, A₁), A₁ ∩ X)",
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]()
					ideal := b.Assume()
					preimageIdeal := b.Have(
						"its preimage under the inclusion is an ideal of A₁",
						"ring_ideal(restrict_ring(R, A₁), preimage_on(A₁, λx:A. x, X))",
						By(ideal, ring_homomorphism.PreimageIdeal.Read(secondInclusion).At(X)))
					preimage := b.Have(
						"and that preimage is A₁ ∩ X",
						"preimage_on(A₁, λx:A. x, X) = A₁ ∩ X",
						Simp(Fwd(functions.PreimageOnDef)),
						BySets())
					b.Show(
						"so A₁ ∩ X is an ideal of A₁",
						By(Normalized, preimageIdeal, preimage))
				}))
			a.Iff()
			a.Forward(
				"unique residues give the map, which determines the chart-1 ideal",
				func(b *Argument, h Fact) {
					onChart0 := b.Conjuncts(
						h,
						"P is a rational point",
						"its chart-0 ideal is proper")
					point, proper0 := onChart0[0], onChart0[1]
					pointClauses := b.Conjuncts(
						b.Unfolded(point, BiaffineRationalPointDef),
						"the chart-0 ideal is the whole chart, or the ideal of a k-rational point of it",
						"the chart-1 ideal is the whole chart, or the ideal of a k-rational point of it",
						"the point lies on some chart",
						"the two chart ideals generate the same ideal of R",
						"on both charts the generated ideal is proper")
					I0, I1 := b.TermAs[Set[A]]("fst(P)"), b.TermAs[Set[A]]("snd(P)")
					span := b.TermAs[Set[A]]("ideal_span(R, fst(P))")
					meet := b.TermAs[Set[A]]("A₁ ∩ ideal_span(R, fst(P))")
					rational0 := b.Have(
						"being proper, the chart-0 ideal is the ideal of a k-rational point of A₀",
						"rational_ideal(R, k, A₀, fst(P))",
						By(Normalized, proper0, pointClauses[0]))
					residues0 := b.Conjuncts(
						b.Unfolded(rational0, quotient_ring.RationalIdealDef),
						"the chart-0 ideal is an ideal of A₀",
						"it excludes one",
						"it has residues in k")
					φ, residueMap := b.ObtainAs[Fun[A, A]](
						"choose the residue map on chart 0",
						"∃φ:(A → A). "+
							"    ring_homomorphism(restrict_ring(R, A₀), restrict_ring(R, k), φ) ∧ "+
							"    (∀c:A. c ∈ k ⇒ φ(c) = c) ∧ "+
							"    fst(P) = ring_kernel(R.zero, A₀, φ)",
						By(
							ring,
							subfieldK,
							subring0,
							kIn0,
							rational0,
							quotient_ring.FieldResiduesHomomorphism.At(R, k, inv, A0, I0)))
					chosenMap := b.Conjuncts(
						residueMap,
						"the residue map is a ring homomorphism",
						"it fixes k",
						"its kernel is the chart-0 ideal")
					firstIdealInR := b.Have(
						"the chart-0 ideal lies in R",
						"fst(P) ⊆ R.carrier",
						BySets(residues0[0], ring_ideal.IdealSubset.At(R0, I0), comm_ring.SubringSubset.Read(subring0)))
					ambientIdeal := b.Have(
						"it generates an ideal of R",
						"ring_ideal(R, ideal_span(R, fst(P)))",
						By(firstIdealInR, ring_ideal.SpanIdeal.Read(ring).At(I0)))
					secondIdealIdentification := b.Have(
						"the chart-1 ideal is the meet of A₁ with the ideal of R the chart-0 ideal generates",
						"snd(P) = A₁ ∩ ideal_span(R, fst(P))",
						Derive(func(c *Argument) {
							c.Cases(c.TermAs[Bool]("snd(P) = A₁"))
							c.When(
								"a whole chart-1 ideal makes the generated ideal all of R",
								func(d *Argument, whole1 Fact) {
									secondHoldsOne := d.Have(
										"the whole chart holds one",
										"R.one ∈ snd(P)",
										By(Normalized, comm_ring.SubringOne.Read(subring1), whole1))
									secondSpanHoldsOne := d.Have(
										"so does the ideal it generates",
										"R.one ∈ ideal_span(R, snd(P))",
										BySets(secondHoldsOne, ring_ideal.SpanContains.At(R, I1)))
									firstSpanHoldsOne := d.Have(
										"which the chart-0 ideal generates too",
										"R.one ∈ ideal_span(R, fst(P))",
										By(Normalized, secondSpanHoldsOne, pointClauses[3]))
									fullAmbientIdeal := d.Have(
										"an ideal of R holding one is all of R",
										"ideal_span(R, fst(P)) = R.carrier",
										By(firstSpanHoldsOne, ambientIdeal, ring_ideal.IdealOneIff.Read(ring).At(span)))
									fullIntersection := d.Have(
										"so its meet with A₁ is A₁",
										"A₁ ∩ ideal_span(R, fst(P)) = A₁",
										BySets(comm_ring.SubringSubset.Read(subring1), fullAmbientIdeal))
									d.Show(
										"the whole chart-1 ideal is that meet",
										By(Normalized, whole1, fullIntersection))
								})
							c.Otherwise(
								"maximality identifies a proper chart-1 ideal",
								func(d *Argument, proper1 Fact) {
									rational1 := d.Have(
										"being proper, the chart-1 ideal is the ideal of a k-rational point of A₁",
										"rational_ideal(R, k, A₁, snd(P))",
										By(Normalized, proper1, pointClauses[1]))
									secondIdeal := d.Conjuncts(
										d.Unfolded(rational1, quotient_ring.RationalIdealDef),
										"the chart-1 ideal is an ideal of A₁",
										"it excludes one",
										"it has residues in k")[0]
									secondSubsetAmbient := d.Have(
										"it lies in the ideal it generates, which the chart-0 ideal generates too",
										"snd(P) ⊆ ideal_span(R, fst(P))",
										BySets(pointClauses[3], ring_ideal.SpanContains.At(R, I1)))
									secondSubsetIntersection := d.Have(
										"and in A₁, so in the meet",
										"snd(P) ⊆ A₁ ∩ ideal_span(R, fst(P))",
										BySets(secondIdeal, ring_ideal.IdealSubset.At(R1, I1), secondSubsetAmbient))
									secondMaximal := d.Have(
										"a proper chart-1 ideal is maximal",
										"maximal_ideal(restrict_ring(R, A₁), snd(P))",
										By(given, point, proper1, RationalPointMaximal.At(R, A0, A1, t, s, k, inv, P)))
									ambientExcludesOne := d.Have(
										"on both charts the generated ideal excludes one",
										"R.one ∉ ideal_span(R, fst(P))",
										By(proper0, proper1, pointClauses[4]))
									intersectionExcludesOne := d.Have(
										"and so does the meet",
										"R.one ∉ A₁ ∩ ideal_span(R, fst(P))",
										BySets(ambientExcludesOne))
									maximalAlternative := d.Have(
										"maximality makes the meet the chart-1 ideal or puts one in it",
										"A₁ ∩ ideal_span(R, fst(P)) = snd(P) ∨ R.one ∈ A₁ ∩ ideal_span(R, fst(P))",
										By(
											ambientIdeal,
											meetsChart1.At(span),
											secondSubsetIntersection,
											ring_ideal.MaximalIdealMaximal.Read(secondMaximal).At(meet)))
									d.Show(
										"one lying outside the meet, the meet is the chart-1 ideal",
										By(maximalAlternative, intersectionExcludesOne))
								})
						}))
					pairIdentification := b.Have(
						"the two chart ideals determine P",
						"P = (ring_kernel(R.zero, A₀, φ), «J»)",
						By(chosenMap[2], secondIdealIdentification, pairs.PairEta))
					b.Show(
						"the residue map gives the stated pair",
						Witness(φ),
						By(chosenMap[0], chosenMap[1], pairIdentification))
				})
			a.Backward(
				"a map to k fixing k gives a rational point by its kernel pair",
				func(b *Argument, mapExists Fact) {
					φ, mapData := b.UnpackAs[Fun[A, A]](mapExists, "φ")
					chartMap := b.Conjuncts(
						mapData,
						"φ is a ring homomorphism",
						"it fixes k",
						"P is its kernel pair")
					kernel, span, meet :=
						b.TermAs[Set[A]]("ring_kernel(R.zero, A₀, φ)"), b.TermAs[Set[A]]("«E»"), b.TermAs[Set[A]]("«J»")
					firstKernelRational := b.Have(
						"the kernel of φ is the ideal of a k-rational point of A₀",
						"rational_ideal(R, k, A₀, ring_kernel(R.zero, A₀, φ))",
						By(
							subfieldK,
							chartMap[0],
							kIn0,
							chartMap[1],
							quotient_ring.KernelFieldResidues.At(R, k, inv, A0, φ)))
					firstKernelData := b.Unfolded(firstKernelRational, quotient_ring.RationalIdealDef)
					firstKernel := b.Conjuncts(
						firstKernelData,
						"the kernel is an ideal of A₀",
						"it excludes one",
						"it has residues in k")
					firstKernelNotFull := b.Have(
						"excluding one, the kernel is not all of A₀",
						"ring_kernel(R.zero, A₀, φ) ≠ A₀",
						BySets(comm_ring.SubringOne.Read(subring0), firstKernel[1]))
					firstKernelInR := b.Have(
						"the kernel lies in R through A₀",
						"ring_kernel(R.zero, A₀, φ) ⊆ R.carrier",
						BySets(ring_ideal.IdealSubset.Read(firstKernel[0]), comm_ring.SubringSubset.Read(subring0)))
					kernelSpanIdeal := b.Have(
						"it generates an ideal of R",
						"ring_ideal(R, «E»)",
						By(firstKernelInR, ring_ideal.SpanIdeal.Read(ring).At(kernel)))
					parametersInR := b.Have(
						"t and s lie in R",
						"t ∈ R.carrier ∧ s ∈ R.carrier",
						BySets(comm_ring.SubringSubset.Read(subring0), comm_ring.SubringSubset.Read(subring1), tIn0, sIn1))
					reversedInverse := b.Have(
						"so s · t = one, R being commutative",
						"s * t = R.one",
						ByArith(ring, parametersInR, inverse))
					secondSpanEquality := b.Have(
						"R being A₁ with s inverted, the meet with A₁ generates the same ideal of R",
						"ideal_span(R, «J») = «E»",
						By(
							ring,
							subring1,
							sIn1,
							parametersInR,
							reversedInverse,
							away1,
							kernelSpanIdeal,
							ring_away.RingAwaySpanOfContraction.At(R, A1, s, t, span)))
					secondKernelData := b.Have(
						"the meet is the whole chart or the ideal of a k-rational "+
							"point of A₁, and when it is proper so is the generated ideal",
						"(«J» = A₁ ∨ rational_ideal(R, k, A₁, «J»)) ∧ («J» ≠ A₁ ⇒ R.one ∉ «E»)",
						Derive(func(c *Argument) {
							c.Cases(c.TermAs[Bool]("φ(t) = R.zero"))
							c.When(
								"a vanishing φ(t) puts the unit t in the kernel, and the meet is the whole chart",
								func(d *Argument, vanishes Fact) {
									parameterInKernel := d.Have(
										"t lies in the kernel",
										"t ∈ ring_kernel(R.zero, A₀, φ)",
										BySets(tIn0, vanishes, ring_homomorphism.RingKernelDef.At(d.TermAs[A]("R.zero"), A0, φ)))
									parameterInSpan := d.Have(
										"so in the ideal it generates",
										"t ∈ «E»",
										BySets(parameterInKernel, ring_ideal.SpanContains.At(R, kernel)))
									parameterInverse := d.Have(
										"s inverts t in R",
										"∃w:A. w ∈ R.carrier ∧ t * w = R.one",
										Witness(s),
										By(parametersInR, inverse))
									parameterUnit := d.Have(
										"so t is a unit of R",
										"ring_unit(R, t)",
										By(parametersInR, parameterInverse, ring_ideal.RingUnitDef.At(R, t)))
									spanHoldsOne := d.Have(
										"the generated ideal holds one, since an ideal without one holds no unit",
										"R.one ∈ «E»",
										By(
											kernelSpanIdeal,
											parameterUnit,
											parameterInSpan,
											ring_ideal.UnitNotInProperIdeal.Read(ring).At(span, t)))
									spanIsR := d.Have(
										"an ideal of R holding one is all of R",
										"«E» = R.carrier",
										By(kernelSpanIdeal, spanHoldsOne, ring_ideal.IdealOneIff.Read(ring).At(span)))
									secondIsFull := d.Have(
										"so the meet is all of A₁",
										"«J» = A₁",
										BySets(comm_ring.SubringSubset.Read(subring1), spanIsR))
									d.Show(
										"the meet is the whole chart",
										By(Normalized, secondIsFull))
								})
							c.Otherwise(
								"a nonvanishing φ(t) makes the ideal the kernel "+
									"generates in A₀[1/t] = R proper, with residues in k",
								func(d *Argument, nonvanishing Fact) {
									spanRational := d.Have(
										"the ideal the kernel of φ generates in R is the ideal of a k-rational point of R",
										"rational_ideal(R, k, R.carrier, «E»)",
										By(
											ring,
											subfieldK,
											subring0,
											kIn0,
											tIn0,
											parametersInR,
											inverse,
											away0,
											chartMap[0],
											chartMap[1],
											nonvanishing,
											ring_away.KernelSpanAwayFieldResidues.At(R, k, inv, A0, t, s, φ)))
									kernelSpan := d.Conjuncts(
										d.Unfolded(spanRational, quotient_ring.RationalIdealDef),
										"it is an ideal of R",
										"it excludes one",
										"it has residues in k")
									secondKernelProper := d.Have(
										"so the meet excludes one",
										"R.one ∉ «J»",
										BySets(kernelSpan[1]))
									secondKernelResidues := d.Have(
										"residues modulo the generated ideal are residues modulo the meet",
										"∀x:A. x ∈ A₁ ⇒ ∃y:A. y ∈ k ∧ x + -y ∈ «J»",
										Derive(func(e *Argument) {
											x := e.FixAs[A]()
											inChart1 := e.Assume()
											xInR := e.Have(
												"x lies in R",
												"x ∈ R.carrier",
												BySets(comm_ring.SubringSubset.Read(subring1), inChart1))
											y, ambientResidue := e.ObtainAs[A](
												"choose its residue in k modulo the generated ideal",
												"∃y:A. y ∈ k ∧ x + -y ∈ «E»",
												By(xInR, kernelSpan[2].At(x)))
											residue := e.Conjuncts(
												ambientResidue,
												"the residue lies in k",
												"x minus it lies in the generated ideal")
											residueIn1 := e.Have(
												"the residue lies in A₁, as k does",
												"y ∈ A₁",
												BySets(residue[0], kIn1))
											differenceIn1 := e.Have(
												"and x minus it",
												"x + -y ∈ A₁",
												By(
													inChart1,
													residueIn1,
													comm_ring.SubringNeg.Read(subring1).AsFact().At(y),
													comm_ring.SubringAdd.Read(subring1).AsFact().At(x, e.TermAs[A]("-y"))))
											differenceInMeet := e.Have(
												"so x minus it lies in the meet",
												"x + -y ∈ «J»",
												BySets(differenceIn1, residue[1]))
											e.Show(
												"the residue serves modulo the meet",
												Witness(y),
												By(residue[0], differenceInMeet))
										}))
									meetRational := d.Have(
										"the meet is the ideal of a k-rational point of A₁",
										"rational_ideal(R, k, A₁, «J»)",
										Simp(Fwd(quotient_ring.RationalIdealDef)),
										By(kernelSpanIdeal, meetsChart1.At(span), secondKernelProper, secondKernelResidues))
									d.Show(
										"and the generated ideal is proper",
										By(meetRational, kernelSpan[1]))
								})
						}))
					firstProjection := b.Have(
						"the chart-0 ideal of P is the kernel",
						"fst(P) = ring_kernel(R.zero, A₀, φ)",
						By(Normalized, chartMap[2], pairs.Fst.At(kernel, meet)))
					secondProjection := b.Have(
						"its chart-1 ideal is the meet",
						"snd(P) = «J»",
						By(chartMap[2], pairs.Snd.At(kernel, meet)))
					firstPointClause := b.Have(
						"the chart-0 ideal is the ideal of a k-rational point of A₀",
						"rational_ideal(R, k, A₀, fst(P))",
						By(Normalized, firstKernelRational, firstProjection))
					secondPointClause := b.Have(
						"the chart-1 ideal is the whole chart, or the ideal of a k-rational point of it",
						"snd(P) = A₁ ∨ rational_ideal(R, k, A₁, snd(P))",
						By(secondKernelData, secondProjection))
					pointNotBothFull := b.Have(
						"the point lies on some chart, chart 0",
						"¬(fst(P) = A₀ ∧ snd(P) = A₁)",
						By(Normalized, firstKernelNotFull, firstProjection))
					pointSpansEqual := b.Have(
						"the two chart ideals generate the same ideal of R",
						"ideal_span(R, fst(P)) = ideal_span(R, snd(P))",
						By(secondSpanEquality, firstProjection, secondProjection))
					pointAmbientProper := b.Have(
						"on both charts the generated ideal is proper",
						"fst(P) ≠ A₀ ∧ snd(P) ≠ A₁ ⇒ R.one ∉ ideal_span(R, fst(P))",
						By(secondKernelData, firstProjection, secondProjection))
					resultingPoint := b.Have(
						"these clauses make P a rational point",
						"biaffine_rational_point(R, k, A₀, A₁, P)",
						Derive(func(c *Argument) {
							firstAlternative := c.Have(
								"the chart-0 ideal is the whole chart, or the ideal of a k-rational point of it",
								"fst(P) = A₀ ∨ rational_ideal(R, k, A₀, fst(P))",
								By(firstPointClause))
							c.Show(
								"the five clauses are the definition",
								By(
									firstAlternative,
									secondPointClause,
									pointNotBothFull,
									pointSpansEqual,
									pointAmbientProper,
									BiaffineRationalPointDef.At(R, k, A0, A1, P)))
						}))
					b.Show(
						"P is a rational point with a proper chart-0 ideal",
						By(Normalized, resultingPoint, firstKernelNotFull, firstProjection))
				})
		}),
})}

// RationalPointOverlap — a rational point lies on both charts exactly
// when t is not in its chart-0 ideal; then the ideal it generates in R is
// maximal, and each chart ideal is that ideal met with its chart. With t
// outside fst(P), the k-point of chart 0, a map φ : A₀ → k
// (RationalPointHomomorphism), does not vanish at t, so the ideal fst(P)
// generates in A₀[1/t] = R is proper with residues in k and meets A₀ in
// fst(P) (KernelSpanAwayFieldResidues), and it is maximal by
// FieldResiduesMaximal at R. Conversely, on both charts the definition's
// last clause makes the generated ideal proper, so it holds no unit of R,
// t among them.
var RationalPointOverlap = rationalPointOverlapThm{family.Add(registry.ProofEntry{
	Name: "RationalPointOverlap",
	Key:  "prop_29ca2cc6ec175436",
	Reading: "t ∈ A₀ makes t ∉ fst(P) force fst(P) ≠ A₀. The guard t ∉ " +
		"fst(P) of the second conjunct is load-bearing: a point on chart 0 alone " +
		"has t in fst(P), so it generates R, which meets A₀ in A₀, not in fst(P).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"biaffine_rational_point(R, k, A₀, A₁, P)",
		},
		Conclusion: "(¬(fst(P) = A₀) ∧ ¬(snd(P) = A₁) ⇔ t ∉ fst(P)) ∧ " +
			"(t ∉ fst(P) ⇒ " +
			"    maximal_ideal(R, ideal_span(R, fst(P))) ∧ " +
			"    fst(P) = A₀ ∩ ideal_span(R, fst(P)) ∧ " +
			"    snd(P) = A₁ ∩ ideal_span(R, fst(P)))",
		Abbrev: Abbrev{
			{Name: "E", Text: "ideal_span(R, ring_kernel(R.zero, A₀, φ))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			assumptions := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in A₀",
				"k lies in A₁",
				"P is a rational point")
			datum, subfieldK, kIn0, point := assumptions[0], assumptions[1], assumptions[2], assumptions[4]
			charts := a.Conjuncts(
				a.Unfolded(datum, lattice_pair.BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring, subring0, subring1, tIn0, sIn1, inverse, away0 :=
				charts[0], charts[1], charts[2], charts[3], charts[4], charts[5], charts[6]
			pointClauses := a.Conjuncts(
				a.Unfolded(point, BiaffineRationalPointDef),
				"the chart-0 ideal is the whole chart, or the ideal of a k-rational point of it",
				"the chart-1 ideal is the whole chart, or the ideal of a k-rational point of it",
				"the point lies on some chart",
				"the two chart ideals generate the same ideal of R",
				"on both charts the generated ideal is proper")
			parametersInR := a.Have(
				"t and s lie in R",
				"t ∈ R.carrier ∧ s ∈ R.carrier",
				BySets(tIn0, sIn1, comm_ring.SubringSubset.Read(subring0), comm_ring.SubringSubset.Read(subring1)))
			nonzeroConsequences := a.Have(
				"t outside the chart-0 ideal puts the point on both charts, its "+
					"generated ideal maximal and meeting each chart in its chart ideal",
				Statement{
					Hypotheses: []string{
						"t ∉ fst(P)",
					},
					Conclusion: "fst(P) ≠ A₀ ∧ " +
						"snd(P) ≠ A₁ ∧ " +
						"maximal_ideal(R, ideal_span(R, fst(P))) ∧ " +
						"fst(P) = A₀ ∩ ideal_span(R, fst(P)) ∧ " +
						"snd(P) = A₁ ∩ ideal_span(R, fst(P))",
				},
				Derive(func(b *Argument) {
					outside := b.Assume()
					firstProper := b.Have(
						"t witnesses that the chart-0 ideal is proper",
						"fst(P) ≠ A₀",
						By(Normalized, outside, tIn0))
					φ, mapData := b.ObtainAs[Fun[A, A]](
						"the point is the kernel pair of a map φ : A₀ → k fixing k",
						"∃φ:(A → A). "+
							"    ring_homomorphism(restrict_ring(R, A₀), restrict_ring(R, k), φ) ∧ "+
							"    (∀c:A. c ∈ k ⇒ φ(c) = c) ∧ "+
							"    P = (ring_kernel(R.zero, A₀, φ), A₁ ∩ ideal_span(R, ring_kernel(R.zero, A₀, φ)))",
						By(given, firstProper, RationalPointHomomorphism.At(R, A0, A1, t, s, k, inv, P)))
					chartMap := b.Conjuncts(
						mapData,
						"φ is a ring homomorphism",
						"it fixes k",
						"P is its kernel pair")
					firstProjection := b.Have(
						"the chart-0 ideal is the kernel of φ",
						"fst(P) = ring_kernel(R.zero, A₀, φ)",
						By(Normalized, chartMap[2], pairs.Fst))
					secondProjection := b.Have(
						"the chart-1 ideal is the meet of A₁ with the ideal that kernel generates",
						"snd(P) = A₁ ∩ «E»",
						By(Normalized, chartMap[2], pairs.Snd))
					nonvanishing := b.Have(
						"φ does not vanish at t",
						"φ(t) ≠ R.zero",
						BySets(
							outside,
							tIn0,
							firstProjection,
							ring_homomorphism.RingKernelDef.At(b.TermAs[A]("R.zero"), A0, φ)))
					kernelSpan := b.Conjuncts(
						b.Have(
							"so the ideal the kernel of φ generates in A₀[1/t] = R is the "+
								"ideal of a k-rational point of R, and meets A₀ in that kernel",
							"rational_ideal(R, k, R.carrier, «E») ∧ A₀ ∩ «E» = ring_kernel(R.zero, A₀, φ)",
							By(
								ring,
								subfieldK,
								subring0,
								kIn0,
								tIn0,
								parametersInR,
								inverse,
								away0,
								chartMap[0],
								chartMap[1],
								nonvanishing,
								ring_away.KernelSpanAwayFieldResidues.At(R, k, inv, A0, t, s, φ))),
						"it is the ideal of a k-rational point of R",
						"it meets A₀ in the kernel of φ")
					spanProper := b.Conjuncts(
						b.Unfolded(kernelSpan[0], quotient_ring.RationalIdealDef),
						"it is an ideal of R",
						"it excludes one",
						"it has residues in k")[1]
					carrier := b.TermAs[Set[A]]("R.carrier")
					span := b.TermAs[Set[A]]("«E»")
					kInR := b.Have(
						"k lies in R through A₀",
						"k ⊆ R.carrier",
						BySets(comm_ring.SubringSubset.Read(subring0), kIn0))
					ambientMaximalRestricted := b.Have(
						"residues in the field k make that ideal maximal",
						"maximal_ideal(restrict_ring(R, R.carrier), «E»)",
						By(
							ring,
							subfieldK,
							comm_ring.CarrierSubring.Read(ring),
							kInR,
							kernelSpan[0],
							quotient_ring.FieldResiduesMaximal.At(R, k, inv, carrier, span)))
					firstContraction := b.Have(
						"the ideal the point generates meets A₀ in the chart-0 ideal",
						"fst(P) = A₀ ∩ ideal_span(R, fst(P))",
						By(Normalized, firstProjection, kernelSpan[1]))
					secondContraction := b.Have(
						"the chart-1 ideal is its meet with A₁",
						"snd(P) = A₁ ∩ ideal_span(R, fst(P))",
						By(Normalized, firstProjection, secondProjection))
					secondExcludesOne := b.Have(
						"which excludes one",
						"R.one ∉ snd(P)",
						BySets(secondProjection, spanProper))
					secondProper := b.Have(
						"so the chart-1 ideal, holding no one, is not A₁",
						"snd(P) ≠ A₁",
						By(Normalized, secondExcludesOne, comm_ring.SubringOne.Read(subring1)))
					spanMaximal := b.Have(
						"the ideal the point generates is maximal",
						"maximal_ideal(R, ideal_span(R, fst(P)))",
						By(firstProjection, ambientMaximalRestricted, module_record.RestrictRingCarrier))
					b.Show(
						"both chart ideals are proper, and the generated ideal "+
							"is maximal and meets each chart in its chart ideal",
						By(firstProper, secondProper, spanMaximal, firstContraction, secondContraction))
				}))
			bothChartsNonvanishing := a.Have(
				"on both charts the chart-0 ideal excludes the unit t",
				"fst(P) ≠ A₀ ∧ snd(P) ≠ A₁ ⇒ t ∉ fst(P)",
				Derive(func(b *Argument) {
					bothProper := b.Assume()
					firstRational := b.Have(
						"the proper chart-0 ideal is the ideal of a k-rational point of A₀",
						"rational_ideal(R, k, A₀, fst(P))",
						By(Normalized, bothProper, pointClauses[0]))
					firstIdeal := b.Conjuncts(
						b.Unfolded(firstRational, quotient_ring.RationalIdealDef),
						"it is an ideal of A₀",
						"it excludes one",
						"it has residues in k")[0]
					firstInR := b.Have(
						"it lies in R through A₀",
						"fst(P) ⊆ R.carrier",
						BySets(ring_ideal.IdealSubset.Read(firstIdeal), comm_ring.SubringSubset.Read(subring0)))
					parameterInFirst := b.SupposeNot()
					parameterInSpan := b.Have(
						"t in the chart-0 ideal lies in the ideal it generates",
						"t ∈ ideal_span(R, fst(P))",
						BySets(parameterInFirst, ring_ideal.SpanContains.At(R, b.TermAs[Set[A]]("fst(P)"))))
					parameterInverse := b.Have(
						"s inverts t in R",
						"∃w:A. w ∈ R.carrier ∧ t * w = R.one",
						Witness(s),
						By(parametersInR, inverse))
					parameterUnit := b.Have(
						"so t is a unit of R",
						"ring_unit(R, t)",
						By(parametersInR, parameterInverse, ring_ideal.RingUnitDef.At(R, t)))
					b.Show(
						"a unit in the generated ideal contradicts its properness",
						By(
							firstInR,
							ring_ideal.SpanIdeal.Read(ring).At(b.TermAs[Set[A]]("fst(P)")),
							bothProper,
							pointClauses[4],
							parameterUnit,
							parameterInSpan,
							ring_ideal.UnitNotInProperIdeal.Read(ring).At(b.TermAs[Set[A]]("ideal_span(R, fst(P))"), t)))
				}))
			a.Show(
				"the two implications give the equivalence and the assertions about the generated ideal",
				By(bothChartsNonvanishing, nonzeroConsequences))
		}),
})}

// ---------------------------------------------------------------------------
// The ideal pair of a point
// ---------------------------------------------------------------------------

// RationalPointChartIdeals — each chart set of a rational point is an
// ideal of its chart: a proper one as the ideal of a k-rational point of
// the chart, and a whole chart as the carrier ideal of the chart's ring,
// which it inherits from R.
var RationalPointChartIdeals = rationalPointChartIdealsThm{family.Add(registry.ProofEntry{
	Name: "RationalPointChartIdeals",
	Key:  "prop_f4fdb700192da78c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀k:set(A). ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"biaffine_rational_point(R, k, A₀, A₁, P)",
		},
		Conclusion: "ring_ideal(restrict_ring(R, A₀), fst(P)) ∧ ring_ideal(restrict_ring(R, A₁), snd(P))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			assumptions := a.Conjuncts(
				given,
				"the datum is biaffine",
				"P is a rational point")
			datum, point := assumptions[0], assumptions[1]
			charts := a.Conjuncts(
				a.Unfolded(datum, lattice_pair.BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring, subring0, subring1 := charts[0], charts[1], charts[2]
			chartRings := a.Conjuncts(
				a.Have(
					"each chart inherits its ring structure",
					"comm_ring_on(restrict_ring(R, A₀)) ∧ comm_ring_on(restrict_ring(R, A₁))",
					By(
						subring0,
						subring1,
						comm_ring.SubringRingOn.Read(ring).At(A0),
						comm_ring.SubringRingOn.Read(ring).At(A1))),
				"the chart-zero ring",
				"the chart-one ring")
			pointClauses := a.Conjuncts(
				a.Unfolded(point, BiaffineRationalPointDef),
				"the chart-0 ideal is the whole chart, or the ideal of a k-rational point of it",
				"the chart-1 ideal is the whole chart, or the ideal of a k-rational point of it",
				"the point lies on some chart",
				"the two chart ideals generate the same ideal of R",
				"on both charts the generated ideal is proper")
			I0, I1 := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			a.Show(
				"a whole chart is the carrier ideal of its ring, and the "+
					"ideal of a k-rational point of a chart is an ideal of it",
				By(
					ring_ideal.CarrierIdeal.Read(chartRings[0]),
					ring_ideal.CarrierIdeal.Read(chartRings[1]),
					pointClauses[0],
					pointClauses[1],
					quotient_ring.RationalIdealDef.At(R, k, A0, I0),
					quotient_ring.RationalIdealDef.At(R, k, A1, I1),
					module_record.RestrictRingDef.At(R, A0),
					module_record.RestrictRingDef.At(R, A1)))
		}),
})}

// PointIdealLattice — the ideal pair of a rational point is a lattice
// pair in R as a module over itself, inside the structure pair. Each chart
// set is an ideal of its chart (RationalPointChartIdeals), so a submodule
// of R over the chart lying in it; and the two generate one ideal of R,
// which is the span of each in R (RegularSpanIsIdealSpan).
var PointIdealLattice = pointIdealLatticeThm{family.Add(registry.ProofEntry{
	Name: "PointIdealLattice",
	Key:  "prop_ee9c516d17b87c53",
	Reading: "Nothing of k is used, nor properness: a chart set enters only as an " +
		"ideal of its chart, and the pair only through the one ideal of R the two generate.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀k:set(A). ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«waBiaffine»",
			"biaffine_rational_point(R, k, A₀, A₁, P)",
		},
		Conclusion: "lattice_pair(R, A₀, A₁, regular_module(R), P) ∧ fst(P) ⊆ A₀ ∧ snd(P) ⊆ A₁",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			assumptions := a.Conjuncts(
				given,
				"the datum is biaffine",
				"P is a rational point")
			datum, point := assumptions[0], assumptions[1]
			charts := a.Conjuncts(
				a.Unfolded(datum, lattice_pair.BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring, subring0, subring1 := charts[0], charts[1], charts[2]
			V := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(R)")
			I0, I1 := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			regularModule := a.Have(
				"R is a module over itself",
				"module_on(R, regular_module(R))",
				By(module.RegularModuleOn.Read(ring)))
			chartIdeals := a.Have(
				"the chart sets of P are ideals of their charts, a whole chart included",
				"ring_ideal(restrict_ring(R, A₀), fst(P)) ∧ ring_ideal(restrict_ring(R, A₁), snd(P))",
				By(given, RationalPointChartIdeals.At(R, A0, A1, t, s, k, P)))
			chartSubmodule := a.Have(
				"an ideal of a chart is a submodule of R over the chart",
				Statement{
					Binders:    "∀S I:set(A).",
					Hypotheses: []string{"subring(R, S)", "ring_ideal(restrict_ring(R, S), I)"},
					Conclusion: "submodule(restrict_ring(R, S), regular_module(R), I) ∧ I ⊆ S ∧ I ⊆ R.carrier",
				},
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]()
					I := b.FixAs[Set[A]]()
					chart := b.Conjuncts(
						b.Assume(),
						"S is a subring",
						"I is an ideal of S")
					RS := b.TermAs[RingOps[A]]("restrict_ring(R, S)")
					inside := b.Have(
						"I lies in S and so in R",
						"I ⊆ S ∧ I ⊆ R.carrier",
						BySets(comm_ring.SubringSubset.Read(chart[0]), chart[1], ring_ideal.IdealSubset.At(RS, I)))
					b.Show(
						"the ideal laws over S are the submodule laws over S",
						By(
							chart[0],
							chart[1],
							inside,
							module.RegularModuleOverSubring.Read(ring).At(S),
							submodule.SubmoduleCriterion.At(RS, V, I),
							ring_ideal.RingIdealDef.At(RS, I),
							module_record.RegularModuleDef.At(R),
							module_record.RestrictRingDef.At(R, S)))
				}))
			first := a.Conjuncts(
				a.Have(
					"so the chart-zero set is a submodule over chart zero",
					"submodule(restrict_ring(R, A₀), regular_module(R), fst(P)) ∧ fst(P) ⊆ A₀ ∧ fst(P) ⊆ R.carrier",
					By(subring0, chartIdeals, chartSubmodule.At(A0, I0))),
				"fst(P) is a submodule over chart zero",
				"it lies in chart zero",
				"it lies in R")
			second := a.Conjuncts(
				a.Have(
					"and the chart-one set a submodule over chart one",
					"submodule(restrict_ring(R, A₁), regular_module(R), snd(P)) ∧ snd(P) ⊆ A₁ ∧ snd(P) ⊆ R.carrier",
					By(subring1, chartIdeals, chartSubmodule.At(A1, I1))),
				"snd(P) is a submodule over chart one",
				"it lies in chart one",
				"it lies in R")
			sameIdeal := a.Have(
				"the two chart sets generate the same ideal of R",
				"ideal_span(R, fst(P)) = ideal_span(R, snd(P))",
				By(point, BiaffineRationalPointDef.At(R, k, A0, A1, P)))
			sameSpan := a.Have(
				"so they span the same submodule of R, the span of a set being the ideal it generates",
				"module_span(R, regular_module(R), fst(P)) = module_span(R, regular_module(R), snd(P))",
				By(
					Normalized,
					ring,
					first[2],
					second[2],
					sameIdeal,
					submodule.RegularSpanIsIdealSpan.At(R, I0),
					submodule.RegularSpanIsIdealSpan.At(R, I1)))
			a.Show(
				"the two chart submodules with one span make a lattice pair inside the structure pair",
				By(
					regularModule,
					first[0],
					second[0],
					sameSpan,
					first[1],
					second[1],
					lattice_pair.LatticePairDef.At(R, A0, A1, V, P)))
		}),
})}

// RationalPointColengths — a rational point's colengths over k: a chart modulo
// the point's ideal in it has dimension one where the point lies on the chart
// and zero where it does not, and R modulo the ideal the point generates has
// dimension one exactly when the point lies on both charts. Where the point
// lies on a chart its residues in k make the chart quotient one-dimensional,
// and where it does not the whole chart gives the zero quotient
// (FieldResiduesColength). The overlap quotient is bounded by the chart-0
// colength (lattice_pair.QuotientDimLocalizes), hence by one; on both charts
// the generated ideal is proper, so its class of one is nonzero and DimZero
// excludes dimension zero, and otherwise a whole chart puts one in the
// generated ideal and the overlap quotient is zero.
var RationalPointColengths = rationalPointColengthsThm{family.Add(registry.ProofEntry{
	Name: "RationalPointColengths",
	Key:  "prop_8389e76edc75922e",
	Reading: "The dimensions are over k read in R's operations, restrict_ring(R, " +
		"k): k ⊆ A₀ and k ⊆ A₁ are what make the chart quotients k-modules.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"biaffine_rational_point(R, k, A₀, A₁, P)",
		},
		Conclusion: "finite_dimensional(restrict_ring(R, k), «Q₀») ∧ " +
			"finite_dimensional(restrict_ring(R, k), «Q₁») ∧ " +
			"finite_dimensional(restrict_ring(R, k), «Q₀₁») ∧ " +
			"module_dim(restrict_ring(R, k), «Q₀») = COND(fst(P) = A₀, 0, 1) ∧ " +
			"module_dim(restrict_ring(R, k), «Q₁») = COND(snd(P) = A₁, 0, 1) ∧ " +
			"module_dim(restrict_ring(R, k), «Q₀₁») = COND(¬(fst(P) = A₀) ∧ ¬(snd(P) = A₁), 1, 0)",
		Abbrev: Abbrev{
			{Name: "E", Text: "ideal_span(R, fst(P))"},
			{Name: "Q₀", Text: "quotient_module(restrict_module(regular_module(R), A₀), fst(P))"},
			{Name: "Q₁", Text: "quotient_module(restrict_module(regular_module(R), A₁), snd(P))"},
			{Name: "Q₀₁", Text: "quotient_module(restrict_module(regular_module(R), R.carrier), «E»)"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			P *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			assumptions := a.Conjuncts(
				given,
				"the datum is biaffine",
				"k is a field under R's operations",
				"k lies in A₀",
				"k lies in A₁",
				"P is a rational point")
			datum, subfieldK, kIn0, kIn1, point :=
				assumptions[0], assumptions[1], assumptions[2], assumptions[3], assumptions[4]
			charts := a.Conjuncts(
				a.Unfolded(datum, lattice_pair.BiaffineDef),
				"R is a commutative ring",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring, subring0, subring1 := charts[0], charts[1], charts[2]
			K, V :=
				a.TermAs[RingOps[A]]("restrict_ring(R, k)"),
				a.TermAs[module_record.ModuleOps[A, A]]("regular_module(R)")
			R0, R1 := a.TermAs[RingOps[A]]("restrict_ring(R, A₀)"), a.TermAs[RingOps[A]]("restrict_ring(R, A₁)")
			I0, I1, E := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)"), a.TermAs[Set[A]]("«E»")
			Q01 := a.TermAs[module_record.ModuleOps[A, Set[A]]]("«Q₀₁»")
			chartRings := a.Conjuncts(
				a.Have(
					"each chart inherits its ring structure",
					"comm_ring_on(restrict_ring(R, A₀)) ∧ comm_ring_on(restrict_ring(R, A₁))",
					By(
						subring0,
						subring1,
						comm_ring.SubringRingOn.Read(ring).At(A0),
						comm_ring.SubringRingOn.Read(ring).At(A1))),
				"the chart-zero ring",
				"the chart-one ring")
			chartIdeals := a.Have(
				"the chart sets of P are ideals of their charts, a whole chart included",
				"ring_ideal(restrict_ring(R, A₀), fst(P)) ∧ ring_ideal(restrict_ring(R, A₁), snd(P))",
				By(datum, point, RationalPointChartIdeals.At(R, A0, A1, t, s, k, P)))
			pointClauses := a.Conjuncts(
				a.Unfolded(point, BiaffineRationalPointDef),
				"the chart-0 ideal is the whole chart, or the ideal of a k-rational point of it",
				"the chart-1 ideal is the whole chart, or the ideal of a k-rational point of it",
				"the point lies on some chart",
				"the two chart ideals generate the same ideal of R",
				"on both charts the generated ideal is proper")
			residues0 := a.Have(
				"read in chart zero's own ring, the point's set is "+
					"the chart, or the ideal of a k-rational point of it",
				"fst(P) = restrict_ring(R, A₀).carrier ∨ "+
					"rational_ideal(restrict_ring(R, A₀), k, restrict_ring(R, A₀).carrier, fst(P))",
				Simp(Fwd(quotient_ring.RationalIdealDef), Fwd(module_record.RestrictRingDef)),
				By(a.Simplified(
					pointClauses[0],
					Fwd(quotient_ring.RationalIdealDef),
					Fwd(module_record.RestrictRingDef))))
			colength0 := a.Have(
				"chart zero has colength zero or one according to the point's chart membership",
				"finite_dimensional(restrict_ring(R, k), «Q₀») ∧ "+
					"module_dim(restrict_ring(R, k), «Q₀») = COND(fst(P) = A₀, 0, 1)",
				By(
					Normalized,
					chartRings[0],
					subfieldK,
					field.RingSubfieldRestrict.At(R, A0, inv, k),
					kIn0,
					module_record.RegularModuleRestrict.At(R, A0),
					chartIdeals,
					residues0,
					module_dimension.FieldResiduesColength.At(R0, k, inv, I0),
					module_record.RestrictRingDef.At(R, A0),
					module_record.RestrictRingTwice.At(R, A0, k)))
			residues1 := a.Have(
				"and read in chart one's own ring, likewise",
				"snd(P) = restrict_ring(R, A₁).carrier ∨ "+
					"rational_ideal(restrict_ring(R, A₁), k, restrict_ring(R, A₁).carrier, snd(P))",
				Simp(Fwd(quotient_ring.RationalIdealDef), Fwd(module_record.RestrictRingDef)),
				By(a.Simplified(
					pointClauses[1],
					Fwd(quotient_ring.RationalIdealDef),
					Fwd(module_record.RestrictRingDef))))
			colength1 := a.Have(
				"the same residue argument gives the chart-one colength",
				"finite_dimensional(restrict_ring(R, k), «Q₁») ∧ "+
					"module_dim(restrict_ring(R, k), «Q₁») = COND(snd(P) = A₁, 0, 1)",
				By(
					Normalized,
					chartRings[1],
					subfieldK,
					field.RingSubfieldRestrict.At(R, A1, inv, k),
					kIn1,
					module_record.RegularModuleRestrict.At(R, A1),
					chartIdeals,
					residues1,
					module_dimension.FieldResiduesColength.At(R1, k, inv, I1),
					module_record.RestrictRingDef.At(R, A1),
					module_record.RestrictRingTwice.At(R, A1, k)))
			structure := a.Have(
				"the structure chart is a submodule and spans the overlap",
				"module_on(R, regular_module(R)) ∧ "+
					"submodule(restrict_ring(R, A₀), regular_module(R), A₀) ∧ "+
					"module_span(R, regular_module(R), A₀) = R.carrier",
				By(
					datum,
					lattice_pair.StructurePairLattice.At(R, A0, A1, t, s),
					lattice_pair.LatticePairDef.At(R, A0, A1, V, a.TermAs[Prod[Set[A], Set[A]]]("(A₀, A₁)")),
					lattice_pair.LatticePairAmbientDef.At(R, V, a.TermAs[Prod[Set[A], Set[A]]]("(A₀, A₁)")),
					pairs.Fst.At(A0, A1),
					pairs.Snd.At(A0, A1)))
			pointLattice := a.Conjuncts(
				a.Have(
					"the point's ideal pair is a lattice pair inside the structure pair",
					"lattice_pair(R, A₀, A₁, regular_module(R), P) ∧ fst(P) ⊆ A₀ ∧ snd(P) ⊆ A₁",
					By(datum, point, PointIdealLattice.At(R, A0, A1, t, s, k, P))),
				"the ideal pair is a lattice pair",
				"the chart-zero ideal lies in chart zero",
				"the chart-one ideal lies in chart one")
			pointSubmodule := a.Have(
				"so the ideal is a submodule of the ambient regular "+
					"module over chart zero, inside chart zero and R",
				"submodule(restrict_ring(R, A₀), regular_module(R), fst(P)) ∧ fst(P) ⊆ A₀ ∧ fst(P) ⊆ R.carrier",
				BySets(
					pointLattice[0],
					pointLattice[1],
					comm_ring.SubringSubset.Read(subring0),
					lattice_pair.LatticePairDef.At(R, A0, A1, V, P)))
			generated := a.Have(
				"the generated regular submodule is the generated ideal",
				"module_span(R, regular_module(R), fst(P)) = «E»",
				By(ring, pointSubmodule, submodule.RegularSpanIsIdealSpan.At(R, I0)))
			localized := a.Have(
				"localization gives a finite overlap quotient no larger than the chart-zero quotient",
				"finite_dimensional(restrict_ring(R, k), «Q₀₁») ∧ "+
					"module_dim(restrict_ring(R, k), «Q₀₁») ≤ module_dim(restrict_ring(R, k), «Q₀»)",
				By(
					subfieldK,
					generated,
					kIn0,
					colength0,
					structure,
					pointSubmodule,
					datum,
					lattice_pair.QuotientDimLocalizes.At(R, A0, A1, t, s, k, inv, V, A0, I0)))
			atMostOne := a.Have(
				"the overlap dimension is at most one",
				"module_dim(restrict_ring(R, k), «Q₀₁») ≤ 1",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("fst(P) = A₀"))
					b.When(
						"a zero chart quotient bounds the overlap by zero",
						func(c *Argument, whole Fact) {
							c.Show(
								"hence by one",
								ByArith(whole, colength0, localized))
						})
					b.Otherwise(
						"a proper chart quotient has dimension one",
						func(c *Argument, proper Fact) {
							c.Show(
								"and bounds the overlap",
								ByArith(proper, colength0, localized))
						})
				}))
			overlapIdeal := a.Have(
				"the point generates an ideal of R",
				"ring_ideal(R, «E»)",
				By(pointSubmodule, ring_ideal.SpanIdeal.Read(ring).At(I0)))
			kInR := a.Have(
				"k lies in R through A₀",
				"k ⊆ R.carrier",
				BySets(comm_ring.SubringSubset.Read(subring0), kIn0))
			fullRestriction := a.Have(
				"restricting the overlap to its carrier changes nothing",
				"restrict_module(regular_module(R), R.carrier) = regular_module(R)",
				Simp(Fwd(module_record.RegularModuleDef), Fwd(module_record.RestrictModuleDef)),
				Basic())
			quotientOn := a.Have(
				"the overlap quotient is a k-module",
				"module_on(restrict_ring(R, k), «Q₀₁»)",
				By(
					Normalized,
					fullRestriction,
					ring,
					subfieldK,
					kInR,
					overlapIdeal,
					module_dimension.IdealQuotientModuleOn.At(R, k, inv, E)))
			overlapColength := a.Have(
				"the overlap has colength one exactly when the point lies on both charts",
				"module_dim(restrict_ring(R, k), «Q₀₁») = COND(fst(P) ≠ A₀ ∧ snd(P) ≠ A₁, 1, 0)",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("fst(P) ≠ A₀ ∧ snd(P) ≠ A₁"))
					b.When(
						"on both charts the generated ideal is proper",
						func(c *Argument, both Fact) {
							nonzero := c.Have(
								"the quotient has a nonzero class of one",
								"left_coset(R.add, R.one, «E») ∈ quotient_module(regular_module(R), «E»).carrier ∧ "+
									"left_coset(R.add, R.one, «E») ≠ quotient_module(regular_module(R), «E»).zero",
								By(ring, overlapIdeal, pointClauses[4], both, module_dimension.QuotientOneNonzero.At(R, E)))
							nonzeroDimension := c.Have(
								"so its finite dimension cannot be zero",
								"module_dim(restrict_ring(R, k), «Q₀₁») ≠ 0",
								Derive(func(d *Argument) {
									notSingleton := d.Have(
										"its carrier is larger than the zero singleton",
										"left_cosets(R.add, R.carrier, «E») ≠ {«E»}",
										BySets(d.Simplified(
											nonzero,
											Fwd(module_record.RegularModuleDef),
											Fwd(submodule.QuotientModuleDef))))
									d.Show(
										"the zero-space criterion excludes dimension zero",
										By(
											subfieldK,
											field.RingSubfieldRestrict.At(R, k, inv, k),
											notSingleton,
											quotientOn,
											localized,
											module_dimension.DimZero.At(K, Q01, inv),
											module_record.RestrictRingDef.At(R, k)))
								}))
							c.Show(
								"a nonzero dimension bounded by one is one",
								ByArith(nonzeroDimension, atMostOne, both))
						})
					b.Otherwise(
						"off the overlap a whole chart makes the generated ideal all of R",
						func(c *Argument, off Fact) {
							oneIn := c.Have(
								"one lies in the ideal generated by the whole chart",
								"R.one ∈ «E»",
								BySets(
									comm_ring.SubringOne.Read(subring0),
									comm_ring.SubringOne.Read(subring1),
									off,
									pointClauses[3],
									ring_ideal.SpanContains.At(R, I0),
									ring_ideal.SpanContains.At(R, I1)))
							whole := c.Have(
								"an ideal containing one is all of R",
								"«E» = R.carrier",
								By(oneIn, overlapIdeal, ring_ideal.IdealOneIff.Read(ring).At(E)))
							c.Show(
								"the whole-ideal quotient has dimension zero",
								By(
									ring,
									subfieldK,
									kInR,
									off,
									whole,
									fullRestriction,
									overlapIdeal,
									module_dimension.FieldResiduesColength.At(R, k, inv, E)))
						})
				}))
			a.Show(
				"the two chart colengths and the overlap colength have the stated values",
				By(overlapColength, colength0, colength1, localized))
		}),
})}

// RationalPointSwap — a rational point read from the other chart: the definition
// is symmetric in the two charts once the two components span one ideal.
var RationalPointSwap = rationalPointSwapThm{family.Add(registry.ProofEntry{
	Name: "RationalPointSwap",
	Key:  "prop_ea5fea5721674c3e",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀k A₀ A₁:set(A). ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"biaffine_rational_point(R, k, A₀, A₁, P)"},
		Conclusion: "biaffine_rational_point(R, k, A₁, A₀, (snd(P), fst(P)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			k, A0, A1 *Expr[Set[A]],
			P *Expr[Prod[Set[A], Set[A]]],
			point Fact,
		) {
			clauses := a.Unfolded(point, BiaffineRationalPointDef)
			a.Show(
				"each clause reads at the swapped pair, the two components spanning one ideal",
				Simp(Fwd(BiaffineRationalPointDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(Normalized, Broadcast, clauses))
		}),
})}

// RationalChartSeparate — a rational point is told from another on a chart where
// it is proper: were the ideal of the other inside it, both would be maximal there
// and so equal, and a point is determined by a proper chart ideal, since its other
// component is the whole chart or the contraction of the ideal this one spans.
var RationalChartSeparate = rationalChartSeparateThm{family.Add(registry.ProofEntry{
	Name: "RationalChartSeparate",
	Key:  "prop_3edb301c0039ac26",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀P Q:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"biaffine_rational_point(R, k, A₀, A₁, P)",
			"biaffine_rational_point(R, k, A₀, A₁, Q)",
			"Q ≠ P",
			"fst(P) ≠ A₀",
		},
		Conclusion: "¬(fst(Q) ⊆ fst(P))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Expr[Fun[A, A]],
			P, Q *Expr[Prod[Set[A], Set[A]]],
			datum, constants, in0, in1, pointP, pointQ, distinct, proper Fact,
		) {
			chart := a.TermAs[RingOps[A]]("restrict_ring(R, A₀)")
			firstP, firstQ := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("fst(Q)")
			maximalP := a.Have(
				"fst(P), a proper component, is maximal in chart 0",
				"maximal_ideal(restrict_ring(R, A₀), fst(P))",
				By(proper, in0, in1, constants, datum, pointP, RationalPointMaximal.At(R, A0, A1, t, s, k, inv, P)))
			idealP := a.Have(
				"so it is an ideal missing one",
				"ring_ideal(restrict_ring(R, A₀), fst(P)) ∧ R.one ∉ fst(P)",
				By(maximalP, ring_ideal.MaximalIdealDef.At(chart, firstP)))
			oneIn := a.Have(
				"one lies in chart 0",
				"R.one ∈ A₀",
				By(datum, lattice_pair.BiaffineDef.At(R, A0, A1, t, s), comm_ring.SubringOne.At(R, A0)))
			contained := a.SupposeNot()
			properQ := a.Have(
				"fst(Q) is proper too, since chart 0 holds one and fst(P) does not",
				"fst(Q) ≠ A₀",
				BySets(contained, oneIn, idealP))
			maximalQ := a.Have(
				"so it is maximal in chart 0",
				"maximal_ideal(restrict_ring(R, A₀), fst(Q))",
				By(
					properQ,
					in0,
					in1,
					constants,
					datum,
					pointQ,
					RationalPointMaximal.At(R, A0, A1, t, s, k, inv, Q)))
			same := a.Have(
				"a maximal ideal inside a proper ideal is that ideal",
				"fst(P) = fst(Q)",
				By(maximalQ, contained, idealP, ring_ideal.MaximalIdealMaximal.At(chart, firstQ, firstP)))
			locateP := a.Conjuncts(
				GroupPremises(
					datum, constants, in0, in1, pointP, RationalPointOverlap.At(R, A0, A1, t, s, k, inv, P)),
				"P is proper on both charts exactly off t",
				"and then its components are contractions of one span")
			locateQ := a.Conjuncts(
				GroupPremises(
					datum, constants, in0, in1, pointQ, RationalPointOverlap.At(R, A0, A1, t, s, k, inv, Q)),
				"Q is proper on both charts exactly off t",
				"and then its components are contractions of one span")
			seconds := a.Have(
				"the second component is the whole chart, or the contraction of one span",
				"snd(P) = snd(Q)",
				Derive(func(b *Argument) {
					b.Cases(b.Term("t ∈ fst(P)"))
					b.When(
						"at a zero of t neither point lies on chart 1",
						func(c *Argument, zero Fact) {
							c.Show(
								"both second components are the chart",
								By(zero, same, properQ, proper, locateP[0], locateQ[0]))
						})
					b.Otherwise(
						"off the zeros of t both are the contraction of what fst(P) spans",
						func(c *Argument, nonzero Fact) {
							contractionP := c.Have(
								"snd(P) is the contraction of what fst(P) spans",
								"snd(P) = A₁ ∩ ideal_span(R, fst(P))",
								By(nonzero, locateP[1]))
							contractionQ := c.Have(
								"snd(Q) is the contraction of what fst(Q) spans",
								"snd(Q) = A₁ ∩ ideal_span(R, fst(Q))",
								By(nonzero, same, locateQ[1]))
							c.Do(contractionP.Rw(), contractionQ.Rw(), same.Rw())
							c.Do(Basic())
						})
				}))
			a.Show(
				"so Q would be P",
				By(distinct, same, seconds, pairs.PairEta.At(P), pairs.PairEta.At(Q)))
		}),
})}

// RationalPointsSeparate — a rational point Q other than P lies inside P on no chart
// where P is proper. On chart 1 this is RationalChartSeparate read from the other
// chart.
var RationalPointsSeparate = rationalPointsSeparateThm{family.Add(registry.ProofEntry{
	Name: "RationalPointsSeparate",
	Key:  "prop_489a78bb80b622ce",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀P Q:prod(set(A), set(A)).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"biaffine_rational_point(R, k, A₀, A₁, P)",
			"biaffine_rational_point(R, k, A₀, A₁, Q)",
			"Q ≠ P",
		},
		Conclusion: "(fst(P) ≠ A₀ ⇒ ¬(fst(Q) ⊆ fst(P))) ∧ (snd(P) ≠ A₁ ⇒ ¬(snd(Q) ⊆ snd(P)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Expr[Fun[A, A]],
			P, Q *Expr[Prod[Set[A], Set[A]]],
			datum, constants, in0, in1, pointP, pointQ, distinct Fact,
		) {
			firstP, secondP := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			firstQ, secondQ := a.TermAs[Set[A]]("fst(Q)"), a.TermAs[Set[A]]("snd(Q)")
			swappedP, swappedQ :=
				a.TermAs[Prod[Set[A], Set[A]]]("(snd(P), fst(P))"),
				a.TermAs[Prod[Set[A], Set[A]]]("(snd(Q), fst(Q))")
			otherDatum := a.Have(
				"the datum read from its other chart",
				"biaffine(R, A₁, A₀, s, t)",
				By(datum, lattice_pair.BiaffineSwap.At(R, A0, A1, t, s)))
			differ := a.Have(
				"the points read from the other chart differ",
				"(snd(Q), fst(Q)) ≠ (snd(P), fst(P))",
				Derive(func(b *Argument) {
					same := b.SupposeNot()
					components := b.Have(
						"the components would agree",
						"snd(Q) = snd(P) ∧ fst(Q) = fst(P)",
						By(same, pairs.PairEq.At(secondQ, firstQ, secondP, firstP)))
					b.Show(
						"so would the points",
						By(Normalized, distinct, components, pairs.PairEta.At(P), pairs.PairEta.At(Q)))
				}))
			rationals := a.Have(
				"both are rational points read from the other chart",
				"biaffine_rational_point(R, k, A₁, A₀, (snd(P), fst(P))) ∧ "+
					"biaffine_rational_point(R, k, A₁, A₀, (snd(Q), fst(Q)))",
				By(pointP, pointQ, RationalPointSwap.At(R, k, A0, A1, P), RationalPointSwap.At(R, k, A0, A1, Q)))
			onFirst := a.Have(
				"on chart 0 they are told apart there",
				"fst(P) ≠ A₀ ⇒ ¬(fst(Q) ⊆ fst(P))",
				Derive(func(b *Argument) {
					proper := b.Assume()
					b.Show(
						"fst(Q) does not lie inside the proper fst(P)",
						By(
							distinct,
							in0,
							in1,
							constants,
							datum,
							pointP,
							pointQ,
							proper,
							RationalChartSeparate.At(R, A0, A1, t, s, k, inv, P, Q)))
				}))
			onSecond := a.Have(
				"on chart 1 they are told apart there, read from the other chart",
				"snd(P) ≠ A₁ ⇒ ¬(snd(Q) ⊆ snd(P))",
				Derive(func(b *Argument) {
					proper := b.Assume()
					b.Show(
						"snd(Q) does not lie inside the proper snd(P)",
						By(
							differ,
							in0,
							in1,
							constants,
							otherDatum,
							rationals,
							proper,
							b.Simplified(
								RationalChartSeparate.At(R, A1, A0, s, t, k, inv, swappedP, swappedQ),
								Fwd(pairs.Fst))))
				}))
			a.Show(
				"Q lies inside P on no chart where P is proper",
				By(onFirst, onSecond))
		}),
})}

// ---------------------------------------------------------------------------
// The chart of a point
// ---------------------------------------------------------------------------

// PointOffChartZero — a point whose first ideal is all of A₀ lies off chart 0:
// its chart is A₁ and its ideal there is its second component. Both
// conditionals take their first branch.
var PointOffChartZero = pointOffChartZeroThm{family.Add(registry.ProofEntry{
	Name: "PointOffChartZero",
	Key:  "prop_b0368d948e2ab48a",
	Build: family.Theorem(Statement{
		Binders:    "∀A₀ A₁:set(A). ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"fst(P) = A₀"},
		Conclusion: "point_chart(A₀, A₁, P) = A₁ ∧ point_ideal(A₀, P) = snd(P)",
	},
		func(a *Argument, A0, A1 *Expr[Set[A]], P *Expr[Prod[Set[A], Set[A]]], off Fact) {
			a.Show(
				"both conditionals take their first branch",
				By(Normalized, off, PointChartDef.At(A0, A1, P), PointIdealDef.At(A0, P)))
		}),
})}

// PointOnChartZero — a point whose first ideal is not all of A₀ lies on chart
// 0: its chart is A₀ and its ideal there is its first component. Both
// conditionals take their second branch.
var PointOnChartZero = pointOnChartZeroThm{family.Add(registry.ProofEntry{
	Name: "PointOnChartZero",
	Key:  "prop_ac51f7fc991b285f",
	Build: family.Theorem(Statement{
		Binders:    "∀A₀ A₁:set(A). ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"fst(P) ≠ A₀"},
		Conclusion: "point_chart(A₀, A₁, P) = A₀ ∧ point_ideal(A₀, P) = fst(P)",
	},
		func(a *Argument, A0, A1 *Expr[Set[A]], P *Expr[Prod[Set[A], Set[A]]], on0 Fact) {
			a.Show(
				"both conditionals take their second branch",
				By(Normalized, on0, PointChartDef.At(A0, A1, P), PointIdealDef.At(A0, P)))
		}),
})}

// RationalPointChart — at a rational point P of the datum inside a field L
// whose charts are subrings holding k, P's chart is a subring of L holding k
// and P's ideal is the ideal of a k-rational point of it. Off chart 0 the
// point's second component is not all of A₁, so it is the ideal of a rational
// point of A₁; on chart 0 its first component is one of A₀. An ideal rational
// under the overlap's operations is rational under L's, which are the same.
var RationalPointChart = rationalPointChartThm{family.Add(registry.ProofEntry{
	Name: "RationalPointChart",
	Key:  "prop_7c192e7f0836cdc7",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"subring(field_ring(L), A₀)",
			"subring(field_ring(L), A₁)",
			"k ⊆ A₀",
			"k ⊆ A₁",
			"biaffine_rational_point(restrict_ring(field_ring(L), A₀₁), k, A₀, A₁, P)",
		},
		Conclusion: "subring(field_ring(L), point_chart(A₀, A₁, P)) ∧ " +
			"k ⊆ point_chart(A₀, A₁, P) ∧ " +
			"rational_ideal(field_ring(L), k, point_chart(A₀, A₁, P), point_ideal(A₀, P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			P *Expr[Prod[Set[A], Set[A]]],
			ring0, ring1, k0, k1, point Fact,
		) {
			ringOps := a.TermAs[RingOps[A]]("field_ring(L)")
			overlapOps := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀₁)")
			rational := a.Conjuncts(
				a.Unfolded(point, BiaffineRationalPointDef),
				"fst(P) is A₀ or the ideal of a rational point of A₀",
				"snd(P) is A₁ or the ideal of a rational point of A₁",
				"P is not the pair of charts",
				"the two ideals span one ideal of the overlap",
				"ideals off both charts span a proper ideal of the overlap")
			a.Cases(a.Term("fst(P) = A₀"))
			a.When(
				"P lies off chart 0, so its chart is A₁ and its ideal snd(P), which is not all of A₁",
				func(b *Argument, off Fact) {
					second := b.TermAs[Set[A]]("snd(P)")
					overlapRational := b.Have(
						"snd(P) is the ideal of a rational point of A₁",
						"rational_ideal(restrict_ring(field_ring(L), A₀₁), k, A₁, snd(P))",
						By(off, rational[1], rational[2]))
					b.Show(
						"A₁ is a subring of L holding k, and snd(P) is rational under L's operations, the overlap's",
						By(
							off,
							PointOffChartZero.At(A0, A1, P),
							ring1,
							k1,
							overlapRational,
							quotient_ring.RationalIdealDef.At(overlapOps, k, A1, second),
							quotient_ring.RationalIdealDef.At(ringOps, k, A1, second),
							module_record.RestrictRingTwice.At(ringOps, A01, A1)))
				})
			a.Otherwise(
				"P lies on chart 0, so its chart is A₀ and its ideal fst(P)",
				func(b *Argument, on0 Fact) {
					first := b.TermAs[Set[A]]("fst(P)")
					overlapRational := b.Have(
						"fst(P) is the ideal of a rational point of A₀",
						"rational_ideal(restrict_ring(field_ring(L), A₀₁), k, A₀, fst(P))",
						By(on0, rational[0]))
					b.Show(
						"A₀ is a subring of L holding k, and fst(P) is rational under L's operations, the overlap's",
						By(
							on0,
							PointOnChartZero.At(A0, A1, P),
							ring0,
							k0,
							overlapRational,
							quotient_ring.RationalIdealDef.At(overlapOps, k, A0, first),
							quotient_ring.RationalIdealDef.At(ringOps, k, A0, first),
							module_record.RestrictRingTwice.At(ringOps, A01, A0)))
				})
		}),
})}
