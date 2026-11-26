// evaluation.go — the residue field at a rational point: every
// function regular at P differs from exactly one constant by a member of the
// maximal ideal, and taking that constant is a ring map onto k.

package regular_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/subring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// EvaluationAtRationalPoint — the local ring at a rational point has residue
// field k: each function regular at P differs from one constant of k by a
// member of the maximal ideal 𝔪, and taking that constant is a ring map onto k
// fixing k whose kernel is 𝔪. P's ideal is the ideal of a k-rational point of
// P's chart (biaffine_rational_point.RationalPointChart), so maximal there. 𝔪,
// which P's ideal generates in the local ring, is the set of members of L that
// a denominator off P's ideal brings into it
// (subring_localization.LocalExtensionCleared); a fraction a / b with b off P's
// ideal is congruent to α / β, α and β the constants of a and b, b bringing the
// difference into P's ideal, so 𝔪 is rational over k too. The residue map onto
// k with kernel 𝔪 then exists, and the evaluation, choosing a constant
// congruent to f, agrees with it on the local ring.
var EvaluationAtRationalPoint = evaluationAtRationalPointThm{family.Add(registry.ProofEntry{
	Name: "EvaluationAtRationalPoint",
	Reading: "Rationality of P's ideal, with k inside both charts, is load-bearing; " +
		"regularity is not asked: a singular rational point has residue field k too.",
	Key: "prop_d10aea6eb6de138f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_rational_point(restrict_ring(field_ring(L), A₀₁), k, A₀, A₁, P)",
		},
		Conclusion: "(∀f:A. f ∈ «local» ⇒ «evaluation»(f) ∈ k ∧ f - «evaluation»(f) ∈ «maximal») ∧ " +
			"ring_homomorphism(restrict_ring(field_ring(L), «local»), " +
			"    restrict_ring(field_ring(L), k), " +
			"    «evaluation») ∧ " +
			"(∀a:A. a ∈ k ⇒ «evaluation»(a) = a) ∧ " +
			"{a:A | a ∈ «local» ∧ «evaluation»(a) = L.zero} = «maximal»",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "evaluation", Text: "regular_point_evaluation(field_ring(L), k, A₀, A₁, P)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, point Fact,
		) {
			fieldOps := a.TermAs[FieldOps[A]]("L")
			ringOps := a.TermAs[RingOps[A]]("field_ring(L)")
			ring := field.RingOn.Read(L)
			charts := a.Have(
				"the charts are subrings of L holding the subfield k",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁) ∧ k ⊆ A₀ ∧ k ⊆ A₁ ∧ subfield(L, k)",
				BySets(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			// P's chart and its ideal there.
			chart, ideal := a.TermAs[Set[A]]("point_chart(A₀, A₁, P)"), a.TermAs[Set[A]]("point_ideal(A₀, P)")
			onChart := a.Conjuncts(
				GroupPremises(
					charts, point, biaffine_rational_point.RationalPointChart.Read(L).At(k, A0, A1, A01, P)),
				"P's chart is a subring of L",
				"k lies in it",
				"P's ideal is the ideal of a k-rational point of it")
			subringChart, kInChart, rationalChart := onChart[0], onChart[1], onChart[2]
			invOp := a.TermAs[Fun[A, A]]("L.inv")
			maximalChart := a.Have(
				"so P's ideal is maximal in its chart, its residues being the field k",
				"maximal_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
				By(
					subringChart,
					kInChart,
					charts,
					rationalChart,
					quotient_ring.FieldResiduesMaximal.At(ringOps, k, invOp, chart, ideal),
					ring,
					field.SubfieldRingSubfield.Read(L).At(k, chart),
					field.RingSubfieldRestrict.At(ringOps, chart, invOp, k)))
			chartOps := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), point_chart(A₀, A₁, P))")
			prime := a.Have(
				"hence prime",
				"prime_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
				By(
					maximalChart,
					subringChart,
					ring_ideal.MaximalIsPrime.At(chartOps, ideal),
					comm_ring.SubringRingOn.Read(ring).At(chart)))
			idealParts := a.Conjuncts(
				a.Have(
					"P's ideal lies in its chart and is closed under sums and under multiples from the chart",
					"point_ideal(A₀, P) ⊆ point_chart(A₀, A₁, P) ∧ "+
						"(∀x y:A. x ∈ point_ideal(A₀, P) ∧ y ∈ point_ideal(A₀, P) ⇒ x + y ∈ point_ideal(A₀, P)) ∧ "+
						"(∀r x:A. r ∈ point_chart(A₀, A₁, P) ∧ x ∈ point_ideal(A₀, P) ⇒ r * x ∈ point_ideal(A₀, P))",
					By(
						prime,
						ring_ideal.PrimeIdealIdeal.At(chartOps, ideal),
						ring_ideal.RingIdealDef.At(chartOps, ideal))),
				"P's ideal lies in its chart",
				"it is closed under sums",
				"and under multiples from the chart")
			idealInChart, idealSums, idealMultiples := idealParts[0], idealParts[1], idealParts[2]
			residues := a.Have(
				"each member of the chart is a constant of k modulo P's ideal",
				"∀x:A. x ∈ point_chart(A₀, A₁, P) ⇒ ∃y:A. y ∈ k ∧ x + -y ∈ point_ideal(A₀, P)",
				By(rationalChart, quotient_ring.RationalIdealDef.At(ringOps, k, chart, ideal)))
			// The local ring at P, and its maximal ideal 𝔪, which P's ideal generates.
			fractions := a.Have(
				"the local ring is the localization of P's chart at P's ideal",
				"«local» = subring_localization(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P))",
				By(PointLocalRingDef.At(ringOps, A0, A1, P)))
			local := a.Conjuncts(
				a.Have(
					"the local ring is a subring of L holding the chart, in which each denominator is a unit",
					"subring(field_ring(L), «local») ∧ "+
						"point_chart(A₀, A₁, P) ⊆ «local» ∧ "+
						"(∀u:A. "+
						"    u ∈ point_chart(A₀, A₁, P) ∧ u ∉ point_ideal(A₀, P) ⇒ "+
						"    L.inv(u) ∈ «local» ∧ u * L.inv(u) = L.one)",
					fractions.Rw(),
					By(prime, subringChart, subring_localization.LocalRingSubring.Read(L).At(chart, ideal))),
				"the local ring is a subring of L",
				"it holds the chart",
				"it inverts the denominators")
			localSet := a.TermAs[Set[A]]("«local»")
			maximalIdeal := a.TermAs[Set[A]]("«maximal»")
			proper := a.Have(
				"𝔪 is proper",
				"L.one ∉ «maximal»",
				fractions.Rw(),
				By(prime, subringChart, subring_localization.LocalIdealProper.Read(L).At(chart, ideal)))
			localRing := a.Have(
				"so it is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «local»))",
				By(local[0], comm_ring.SubringRingOn.Read(ring).At(localSet)))
			localOps := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), «local»)")
			idealL := a.Have(
				"𝔪 is an ideal of the local ring holding P's ideal",
				"ring_ideal(restrict_ring(field_ring(L), «local»), «maximal») ∧ point_ideal(A₀, P) ⊆ «maximal»",
				By(
					local[1],
					idealInChart,
					ring_ideal.SpanIdeal.Read(localRing).At(ideal),
					ring_ideal.SpanContains.At(localOps, ideal),
					set_order.SubsetTrans.At(ideal, chart, localSet)))
			inL := a.Have(
				"the local ring lies in L",
				"«local» ⊆ L.carrier",
				By(local[0], comm_ring.SubringSubset.At(ringOps, localSet)))
			extension := a.Have(
				"𝔪 is the extension of P's ideal to the local ring: the "+
					"members of L that a denominator off P's ideal brings into it",
				"«maximal» = "+
					"{y:A | "+
					"    y ∈ L.carrier ∧ "+
					"    (∃b:A. b ∈ point_chart(A₀, A₁, P) ∧ b ∉ point_ideal(A₀, P) ∧ b * y ∈ point_ideal(A₀, P))}",
				fractions.Rw(),
				By(
					subringChart,
					prime,
					ring_ideal.PrimeIdealIdeal.At(chartOps, ideal),
					fractional_ideal.IntegralIdealFractional.Read(L).At(chart, ideal),
					subring_localization.LocalExtensionLaws.Read(L).At(chart, ideal),
					subring_localization.LocalExtensionCleared.Read(L).At(chart, ideal, ideal)))
			// 𝔪 is rational over k: f = a / b is congruent to α / β modulo 𝔪.
			constant := a.Have(
				"each function regular at P is a constant of k modulo 𝔪",
				"∀f:A. f ∈ «local» ⇒ ∃c:A. c ∈ k ∧ f + -c ∈ «maximal»",
				Derive(func(b *Argument) {
					b.FixAs[A]("f")
					fIn := b.Assume()
					num, den, fraction := b.Obtain2As[A, A](
						"f is a fraction a / b of P's chart with b off P's ideal",
						"∃a b:A. "+
							"    a ∈ point_chart(A₀, A₁, P) ∧ b ∈ point_chart(A₀, A₁, P) ∧ b ∉ point_ideal(A₀, P) ∧ f * b = a",
						BySets(fractions, fIn, subring_localization.SubringLocalizationDef.At(ringOps, chart, ideal)))
					parts := b.Conjuncts(
						fraction,
						"a lies in the chart",
						"b lies in the chart",
						"b lies off P's ideal",
						"f · b = a")
					alpha, alphaFacts := b.UnpackAs[A](GroupPremises(parts[0], residues.At(num)), "α")
					beta, betaFacts := b.UnpackAs[A](GroupPremises(parts[1], residues.At(den)), "β")
					alphaParts := b.Conjuncts(
						alphaFacts,
						"α lies in k",
						"a - α lies in P's ideal")
					betaParts := b.Conjuncts(
						betaFacts,
						"β lies in k",
						"b - β lies in P's ideal")
					members := b.Have(
						"f, a, b, α and β lie in L",
						"f ∈ L.carrier ∧ a ∈ L.carrier ∧ b ∈ L.carrier ∧ α ∈ L.carrier ∧ β ∈ L.carrier",
						BySets(fIn, inL, kInChart, local[1], parts[0], parts[1], alphaParts[0], betaParts[0]))
					nonzero := b.Have(
						"β is not zero, b lying off P's ideal",
						"β ≠ L.zero",
						Derive(func(c *Argument) {
							zero := c.SupposeNot()
							same := c.Have(
								"so b - β is b",
								"b + -β = b",
								ByArith(L, zero, members))
							c.Show(
								"and b would lie in P's ideal",
								By(Normalized, parts[2], same, betaParts[1]))
						}))
					quotient := b.TermAs[A]("α * L.inv(β)")
					inverse := b.Conjuncts(
						b.Have(
							"β⁻¹ inverts β in L, and c = α / β and -c lie in k",
							"β * L.inv(β) = L.one ∧ L.inv(β) ∈ L.carrier ∧ α * L.inv(β) ∈ k ∧ -(α * L.inv(β)) ∈ k",
							By(
								nonzero,
								charts,
								alphaParts[0],
								betaParts[0],
								members,
								field.MulRightInverseOn.Read(L).AsFact().At(beta),
								field.InvIn.Read(L).AsFact().At(beta),
								field.SubfieldInv.At(fieldOps, k, beta),
								field.SubfieldMul.At(fieldOps, k, alpha, b.TermAs[A]("L.inv(β)")),
								field.SubfieldNeg.At(fieldOps, k, quotient))),
						"β · β⁻¹ = 1",
						"β⁻¹ lies in L",
						"c lies in k",
						"-c lies in k")
					numerator := b.Have(
						"b · (f - c) = (a - α) - c · (b - β), as c · β = α",
						"b * (f + -(α * L.inv(β))) = (a + -α) + -(α * L.inv(β)) * (b + -β)",
						ByArith(L, parts[3], Scaled(alpha, inverse[0]), inverse[1], members))
					differenceIn := b.Have(
						"f - c lies in L",
						"f + -(α * L.inv(β)) ∈ L.carrier",
						By(
							inverse[1],
							members,
							comm_ring.AddIn.Read(ring),
							comm_ring.NegIn.Read(ring),
							comm_ring.MulIn.Read(ring)))
					numeratorIn := b.Have(
						"the numerator (a - α) - c · (b - β) lies in P's ideal",
						"(a + -α) + -(α * L.inv(β)) * (b + -β) ∈ point_ideal(A₀, P)",
						BySets(inverse[3], alphaParts[1], betaParts[1], kInChart, idealSums, idealMultiples))
					inMaximal := b.Have(
						"b brings f - c into P's ideal, so f - c lies in 𝔪",
						"f + -(α * L.inv(β)) ∈ «maximal»",
						BySets(extension, differenceIn, parts[1], parts[2], numerator, numeratorIn))
					b.Take(quotient)
					b.Show(
						"so c is a constant of k congruent to f modulo 𝔪",
						By(inverse[2], inMaximal))
				}))
			rational := a.Have(
				"so 𝔪 is a rational ideal of the local ring over k",
				"rational_ideal(field_ring(L), k, «local», «maximal»)",
				By(proper, constant, idealL, quotient_ring.RationalIdealDef.At(ringOps, k, localSet, maximalIdeal)))
			// The residue map of 𝔪, and the evaluation read through it.
			phi, residue := a.ObtainAs[Fun[A, A]](
				"the residue map φ of the local ring onto k, the identity on k with kernel 𝔪",
				"∃φ:A → A. "+
					"    ring_homomorphism(restrict_ring(field_ring(L), «local»), "+
					"        restrict_ring(field_ring(L), k), "+
					"        φ) ∧ "+
					"    (∀c:A. c ∈ k ⇒ φ(c) = c) ∧ "+
					"    «maximal» = ring_kernel(L.zero, «local», φ)",
				By(
					charts,
					local[0],
					kInChart,
					local[1],
					rational,
					quotient_ring.FieldResiduesHomomorphism.At(ringOps, k, invOp, localSet, maximalIdeal),
					ring,
					field.SubfieldRingSubfield.Read(L).At(k, k),
					field.RingSubfieldRestrict.At(ringOps, k, invOp, k),
					set_order.SubsetTrans.At(k, chart, localSet)))
			residueParts := a.Conjuncts(
				residue,
				"φ is a ring map onto k",
				"φ fixes k",
				"φ's kernel is 𝔪")
			hom, fixed, kernel := residueParts[0], residueParts[1], residueParts[2]
			evaluates := a.Have(
				"each f in the local ring is congruent modulo 𝔪 to its evaluation, a constant of k",
				"∀f:A. f ∈ «local» ⇒ «evaluation»(f) ∈ k ∧ f - «evaluation»(f) ∈ «maximal»",
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					fIn := b.Assume()
					c, cFacts := b.UnpackAs[A](GroupPremises(fIn, constant.At(f)), "c")
					members := b.Have(
						"f and c lie in L",
						"f ∈ L.carrier ∧ c ∈ L.carrier",
						BySets(fIn, inL, kInChart, local[1], cFacts))
					congruent := b.Have(
						"so f - c lies in 𝔪",
						"∃c:A. c ∈ k ∧ f - c ∈ «maximal»",
						Derive(func(d *Argument) {
							d.Take(c)
							d.Show(
								"f - c is f + -c",
								By(cFacts, members, comm_ring.SubAddNegOn.Read(ring).AsFact().At(f, c)))
						}))
					choice := b.Have(
						"the evaluation of f chooses a constant of k congruent to f modulo 𝔪",
						"«evaluation»(f) = εc:A. c ∈ k ∧ f - c ∈ «maximal»",
						Unfold(RegularPointEvaluationDef))
					b.Show(
						"and it chooses one",
						By(congruent, choice))
				}))
			kOps := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), k)")
			agree := a.Have(
				"the evaluation is φ on the local ring",
				"∀f:A. f ∈ «local» ⇒ «evaluation»(f) = φ(f)",
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					fIn := b.Assume()
					value := b.TermAs[A]("«evaluation»(f)")
					valueIn := b.Have(
						"the evaluation of f lies in k and in the local ring",
						"«evaluation»(f) ∈ k ∧ «evaluation»(f) ∈ «local»",
						BySets(evaluates.At(f), fIn, kInChart, local[1]))
					killed := b.Have(
						"φ kills f minus its evaluation, a member of 𝔪",
						"φ(f - «evaluation»(f)) = L.zero",
						BySets(
							evaluates.At(f),
							kernel,
							fIn,
							ring_homomorphism.RingKernelDef.At(b.TermAs[A]("L.zero"), localSet, phi)))
					difference := b.Have(
						"so φ(f) - «evaluation»(f) = 0, φ fixing the evaluation",
						"φ(f) - «evaluation»(f) = L.zero",
						By(
							hom,
							fixed.At(value),
							killed,
							fIn,
							valueIn,
							ring_homomorphism.MapSub.At(localOps, kOps, phi, f, value)))
					members := b.Have(
						"φ(f) and the evaluation of f lie in L",
						"φ(f) ∈ L.carrier ∧ «evaluation»(f) ∈ L.carrier",
						BySets(
							fIn,
							inL,
							kInChart,
							local[1],
							valueIn,
							hom,
							ring_homomorphism.MapIn.At(localOps, kOps, phi, f)))
					b.Show(
						"so the two agree",
						ByArith(L, difference, members))
				}))
			evaluation := a.TermAs[Fun[A, A]]("«evaluation»")
			homomorphism := a.Have(
				"so the evaluation is a ring map onto k, as φ is",
				"ring_homomorphism(restrict_ring(field_ring(L), «local»), "+
					"    restrict_ring(field_ring(L), k), "+
					"    «evaluation»)",
				By(agree, hom, ring_homomorphism.RingHomCongruence.At(localOps, kOps, phi, evaluation)))
			fixes := a.Have(
				"it fixes k, as φ does",
				"∀a:A. a ∈ k ⇒ «evaluation»(a) = a",
				BySets(agree, fixed, kInChart, local[1]))
			kernelEq := a.Have(
				"its kernel is φ's, which is 𝔪",
				"{a:A | a ∈ «local» ∧ «evaluation»(a) = L.zero} = «maximal»",
				BySets(agree, kernel, ring_homomorphism.RingKernelDef.At(a.TermAs[A]("L.zero"), localSet, phi)))
			a.Show(
				"the evaluation is the residue map of the local ring onto k",
				By(evaluates, homomorphism, fixes, kernelEq))
		}),
})}
