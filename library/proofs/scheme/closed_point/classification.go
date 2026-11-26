// classification.go — the maximal ideals of a quadratic ring k[t] + k[t]·w
// inside a field, w² in k[t], read over the prime p(t)·k[t] each contracts
// to: the first kind (p(t), w − r(t)) for a square root r of w² modulo p,
// or the inert p(t)·S where w² has none; and chart one of a Weierstrass
// curve as its instance.

package closed_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// QuadraticMaximalIdealClassification — a maximal ideal m of the ring
// S = k[t] + k[t]·w inside a field, w² in k[t], meeting k[t] in p(t)·k[t]
// for an irreducible p over k, is (p(t), w − r(t)) for a square root r of
// w² modulo p of degree below p's, or else w² has no square root modulo p
// and m is p(t)·S. A root r₁ makes (w − r₁(t))(w + r₁(t)) a member of the
// prime m, so w − σ lies in m for σ = ±r₁(t), and dividing σ's polynomial
// by p leaves the remainder r with w − r(t) in m; a member c + d·w of m is
// then d·(w − r(t)) plus c + d·r(t), a member of m ∩ k[t] = p(t)·k[t]. With
// no root, a member c + d·w has d = b(t) with p dividing b: else a Bezout
// inverse v(t) of d modulo p(t) puts w + c·v(t) in m, a root; so d·w lies
// in m, c in p(t)·k[t], and the member in p(t)·S.
var QuadraticMaximalIdealClassification = quadraticMaximalIdealClassificationThm{family.Add(registry.ProofEntry{
	Name: "QuadraticMaximalIdealClassification",
	Key:  "prop_dc486074de50e632",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S:set(A). ∀t w:A. ∀m:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"w ∈ L.carrier",
			"w * w ∈ «polynomials»",
			"S = {c + d * w:A | c:A, d:A | c ∈ «polynomials» ∧ d ∈ «polynomials»}",
			"maximal_ideal(«ringS», m)",
			"polynomial_irreducible(restrict_ring(field_ring(L), k), p)",
			"m ∩ «polynomials» = «pIdeal»",
		},
		Conclusion: "(∃r:(num → A). " +
			"    polynomial_over(k, r) ∧ " +
			"    polynomial_degree(r) < polynomial_degree(p) ∧ " +
			"    w * w - polynomial_eval(r, t) * polynomial_eval(r, t) ∈ «pIdeal» ∧ " +
			"    m = ideal_span(«ringS», {polynomial_eval(p, t), w - polynomial_eval(r, t)})) ∨ " +
			"(m = ideal_span(«ringS», {polynomial_eval(p, t)}) ∧ " +
			"    ¬∃r:(num → A). " +
			"        polynomial_over(k, r) ∧ w * w - polynomial_eval(r, t) * polynomial_eval(r, t) ∈ «pIdeal»)",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
			{Name: "pIdeal", Text: "ideal_span(restrict_ring(field_ring(L), «polynomials»), " +
				"    {polynomial_eval(p, t)})"},
			{Name: "ringS", Text: "restrict_ring(field_ring(L), S)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, S *Expr[Set[A]],
			t, w *Expr[A],
			m *Expr[Set[A]],
			p *Arrow[Nat, A],
			h Fact,
		) {
			hyp := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"w lies in L",
				"w² lies in k[t]",
				"S is k[t] + k[t]·w",
				"m is a maximal ideal of S",
				"p is irreducible over k",
				"m meets k[t] in p(t)·k[t]")
			subK, square, chart, maximal, contraction := hyp[0], hyp[3], hyp[4], hyp[5], hyp[7]
			ring := field.RingOn.Read(L)
			tM, wM := a.MemberOf[on.L](t, hyp[1]), a.MemberOf[on.L](w, hyp[2])
			polynomials, ringS := a.TermAs[Set[A]]("«polynomials»"), a.TermAs[RingOps[A]]("«ringS»")
			pValue := a.TermAs[A]("polynomial_eval(p, t)")

			// k[t] and S are subrings of L, S holding k[t] and w; both are rings on their sets.
			kt := a.Conjuncts(
				GroupPremises(subK, algebraic_element.PolynomialImageRing.Read(L).At(k, tM)),
				"k[t] is a subring of L",
				"holding k",
				"and t",
				"inside k(t)")
			inS := a.Conjuncts(
				a.Have(
					"S is a subring of L holding k[t] and w, w² lying in k[t]",
					"subring(field_ring(L), S) ∧ «polynomials» ⊆ S ∧ w ∈ S",
					chart.Rw(),
					By(kt[0], square, fractional_ideal.RingOneAndElement.Read(L).At(polynomials, wM))),
				"S is a subring of L",
				"holding k[t]",
				"and w")
			ringOnS := a.Have(
				"so S is a ring on its set",
				"comm_ring_on(«ringS»)",
				By(inS[0], comm_ring.SubringRingOn.Read(ring).At(S)))
			ringOnKt := a.Have(
				"and so is k[t]",
				"comm_ring_on(restrict_ring(field_ring(L), «polynomials»))",
				By(kt[0], comm_ring.SubringRingOn.Read(ring).At(polynomials)))
			ideal := a.Have(
				"m is an ideal of S",
				"ring_ideal(«ringS», m)",
				By(maximal, ring_ideal.MaximalIdealIdeal))
			irreducible := a.Conjuncts(
				a.Unfolded(hyp[6], polynomial_division.PolynomialIrreducibleDef),
				"p is a polynomial over k",
				"of positive degree",
				"with no factorization into two of positive degree")
			pOver, positive := irreducible[0], irreducible[1]
			fieldK := a.Have(
				"k is a field",
				"field_on(restrict_field(L, k))",
				By(subK, field.SubfieldFieldOn.Read(L).At(k)))

			// The members of k[t] are the values at t of the polynomials over k; they lie in S and in L.
			inImage := a.Have(
				"k[t] is the set of the values at t of the polynomials over k",
				"∀x:A. x ∈ «polynomials» ⇔ ∃q:(num → A). polynomial_over(k, q) ∧ x = polynomial_eval(q, t)",
				Unfold(algebraic_element.PolynomialImageDef),
				SetTac())
			lift := a.Have(
				"k[t] lies in S, and S in L",
				"∀x:A. x ∈ «polynomials» ⇒ x ∈ S ∧ x ∈ L.carrier",
				BySets(inS[0], inS[1], comm_ring.SubringSubset))
			values := a.Have(
				"the value at t of a polynomial over k lies in k[t], so in S and in L",
				Statement{
					Binders: "∀f:(num → A).",
					Hypotheses: []string{
						"polynomial_over(k, f)",
					},
					Conclusion: "polynomial_eval(f, t) ∈ «polynomials» ∧ " +
						"polynomial_eval(f, t) ∈ S ∧ " +
						"polynomial_eval(f, t) ∈ L.carrier",
				},
				Derive(func(sub *Argument) {
					sub.FixAs[Fun[Nat, A]]("f")
					fOver := sub.Assume()
					value := sub.TermAs[A]("polynomial_eval(f, t)")
					inKt := sub.Have(
						"f(t), the value at t of f, lies in k[t]",
						"polynomial_eval(f, t) ∈ «polynomials»",
						By(fOver, inImage.At(value)))
					sub.Show(
						"so in S and in L",
						By(inKt, lift.At(value)))
				}))
			overL := a.Have(
				"a polynomial over k is one over L",
				"∀f:(num → A). polynomial_over(k, f) ⇒ polynomial_over(L.carrier, f)",
				By(subK, field.SubfieldSubset, polynomial.PolynomialOverMono))
			pMem := a.Conjuncts(
				GroupPremises(pOver, values.At(p)),
				"p(t) lies in k[t]",
				"in S",
				"and in L")
			pInM := a.Have(
				"p(t) lies in m, a member of p(t)·k[t] = m ∩ k[t]",
				"polynomial_eval(p, t) ∈ m",
				BySets(contraction, ring_ideal.SpanContains))
			coordinates := a.Have(
				"a member of m is c + d·w with c and d in k[t]",
				"∀z:A. z ∈ m ⇒ ∃c d:A. c ∈ «polynomials» ∧ d ∈ «polynomials» ∧ z = c + d * w",
				BySets(chart, ideal, ring_ideal.IdealSubset))

			// A root w − σ of w² in m, σ in k[t], squares into p(t)·k[t].
			rootSquares := a.Have(
				"a root w − σ in m with σ in k[t] squares into p(t)·k[t]",
				"∀σ:A. σ ∈ «polynomials» ∧ w - σ ∈ m ⇒ w * w - σ * σ ∈ «pIdeal»",
				Derive(func(sub *Argument) {
					σ := sub.FixAs[A]("σ")
					given := sub.Conjuncts(
						sub.Assume(),
						"σ lies in k[t]",
						"w − σ lies in m")
					σMem := sub.Conjuncts(
						GroupPremises(given[0], lift.At(σ)),
						"σ lies in S",
						"and in L")
					factored := sub.Have(
						"w² − σ² = (w + σ)(w − σ)",
						"w * w - σ * σ = (w + σ) * (w - σ)",
						ByArith(ring, wM, σMem[1]))
					inM := sub.Have(
						"which lies in m, a multiple of w − σ by a member of S",
						"w * w - σ * σ ∈ m",
						factored.Rw(),
						By(
							ideal,
							given[1],
							inS[2],
							σMem[0],
							comm_ring.AddIn.Read(ringOnS),
							ring_ideal.IdealMul.At(ringS, m, sub.TermAs[A]("w + σ"), sub.TermAs[A]("w - σ"))))
					inKt := sub.Have(
						"and in k[t], w² and σ lying there",
						"w * w - σ * σ ∈ «polynomials»",
						By(square, given[0], comm_ring.SubIn.Read(ringOnKt), comm_ring.MulIn.Read(ringOnKt)))
					sub.Show(
						"so in m ∩ k[t] = p(t)·k[t]",
						BySets(inM, inKt, contraction))
				}))

			a.Cases(a.Term(
				"∃r:(num → A). " +
					"    polynomial_over(k, r) ∧ w * w - polynomial_eval(r, t) * polynomial_eval(r, t) ∈ «pIdeal»"))
			a.When(
				"w² is a square r₁(t)² modulo p(t): m is (p(t), w − r(t)) for the remainder r of ±r₁ by p",
				func(b *Argument, hasRoot Fact) {
					r1, r1Facts := b.UnpackAs[Fun[Nat, A]](hasRoot, "r₁")
					r1Parts := b.Conjuncts(
						r1Facts,
						"r₁ is a polynomial over k",
						"w² − r₁(t)² lies in p(t)·k[t]")
					r1Value := b.TermAs[A]("polynomial_eval(r₁, t)")
					r1Mem := b.Conjuncts(
						GroupPremises(r1Parts[0], values.At(r1)),
						"r₁(t) lies in k[t]",
						"in S",
						"and in L")
					difference := b.Have(
						"(w − r₁(t))(w + r₁(t)) = w² − r₁(t)²",
						"(w - polynomial_eval(r₁, t)) * (w + polynomial_eval(r₁, t)) = "+
							"w * w - polynomial_eval(r₁, t) * polynomial_eval(r₁, t)",
						ByArith(ring, wM, r1Mem[2]))
					product := b.Have(
						"which lies in p(t)·k[t] ⊆ m",
						"(w - polynomial_eval(r₁, t)) * (w + polynomial_eval(r₁, t)) ∈ m",
						difference.Rw(),
						BySets(r1Parts[1], contraction))
					factorIn := b.Have(
						"m, maximal and so prime, holds w − r₁(t) or w + r₁(t)",
						"w - polynomial_eval(r₁, t) ∈ m ∨ w + polynomial_eval(r₁, t) ∈ m",
						By(
							maximal,
							ring_ideal.MaximalIsPrime.Read(ringOnS),
							product,
							inS[2],
							r1Mem[1],
							comm_ring.SubIn.Read(ringOnS),
							comm_ring.AddIn.Read(ringOnS),
							ring_ideal.PrimeIdealPrime.At(
								ringS, m, b.TermAs[A]("w - polynomial_eval(r₁, t)"), b.TermAs[A]("w + polynomial_eval(r₁, t)"))))
					root := b.Have(
						"so w − σ lies in m for σ = r₁(t) or σ = −r₁(t), a member of k[t] either way",
						"∃σ:A. σ ∈ «polynomials» ∧ w - σ ∈ m",
						Derive(func(sub *Argument) {
							sub.Do(factorIn.SplitDisj(
								LeftHolds(
									"w − r₁(t) lies in m: σ = r₁(t)",
									Given(func(br *Argument, minus Fact) {
										br.Take(r1Value)
										br.Show(
											"r₁(t) is such a σ",
											By(r1Mem[0], minus))
									})),
								RightHolds(
									"w + r₁(t) lies in m: σ = −r₁(t)",
									Given(func(br *Argument, plus Fact) {
										br.Take(br.TermAs[A]("-polynomial_eval(r₁, t)"))
										negated := br.Have(
											"w − (−r₁(t)) = w + r₁(t)",
											"w - -polynomial_eval(r₁, t) = w + polynomial_eval(r₁, t)",
											ByArith(ring, wM, r1Mem[2]))
										br.Show(
											"−r₁(t) is such a σ, k[t] being closed under negation",
											negated.Rw(),
											By(plus, r1Mem[0], comm_ring.NegIn.Read(ringOnKt)))
									}))))
						}))
					σ, σFacts := b.UnpackAs[A](root, "σ")
					σParts := b.Conjuncts(
						σFacts,
						"σ lies in k[t]",
						"w − σ lies in m")

					// Reduce σ's polynomial modulo p.
					q, qFacts := b.ObtainAs[Fun[Nat, A]](
						"σ is the value at t of a polynomial q over k",
						"∃q:(num → A). polynomial_over(k, q) ∧ σ = polynomial_eval(q, t)",
						By(inImage.At(σ), σParts[0]))
					qParts := b.Conjuncts(
						qFacts,
						"q is a polynomial over k",
						"whose value at t is σ")
					zero := b.TermAs[A]("L.zero")
					nonzero := b.Have(
						"p is not the zero polynomial, whose degree is zero",
						"p ≠ vec_zero",
						By(positive, polynomial.DegreeVecZero.At(zero), nat_order.LessThanIrrefl))
					s, r, divided := b.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
						"dividing q by p over the field k leaves a quotient "+
							"s and a remainder r vanishing from p's degree on",
						"∃s r:(num → A). «division»(k, q, p, s, r)",
						By(qParts[0], pOver, nonzero, polynomial_division.DivisionExists.Read(fieldK).At(q, p)))
					division := b.Conjuncts(
						divided,
						"s is a polynomial over k",
						"so is r",
						"r vanishes from p's degree on",
						"q = p s + r")
					sOver, rOver, rShort, decomposition := division[0], division[1], division[2], division[3]
					sMem := b.Conjuncts(
						GroupPremises(sOver, values.At(s)),
						"s(t) lies in k[t]",
						"in S",
						"and in L")
					rMem := b.Conjuncts(
						GroupPremises(rOver, values.At(r)),
						"r(t) lies in k[t]",
						"in S",
						"and in L")
					split := b.Have(
						"evaluated at t, q = p s + r gives σ = q(t) = p(t)·s(t) + r(t)",
						"σ = polynomial_eval(p, t) * polynomial_eval(s, t) + polynomial_eval(r, t)",
						By(
							qParts[1],
							decomposition,
							overL.At(p),
							overL.At(s),
							overL.At(r),
							pOver,
							sOver,
							rOver,
							polynomial_evaluation.DivisionValue.Read(ring).At(q, p, s, r, tM)))
					shifted := b.Have(
						"w − r(t) = (w − σ) + s(t)·p(t)",
						"w - polynomial_eval(r, t) = w - σ + polynomial_eval(s, t) * polynomial_eval(p, t)",
						split.Rw(),
						ByArith(ring, wM, pMem[2], sMem[2], rMem[2]))
					reduced := b.Have(
						"so w − r(t) lies in m, a sum of members of m",
						"w - polynomial_eval(r, t) ∈ m",
						shifted.Rw(),
						By(
							ideal,
							σParts[1],
							pInM,
							sMem[1],
							ring_ideal.IdealMul.At(ringS, m, b.TermAs[A]("polynomial_eval(s, t)"), pValue),
							ring_ideal.IdealAdd.At(
								ringS, m, b.TermAs[A]("w - σ"), b.TermAs[A]("polynomial_eval(s, t) * polynomial_eval(p, t)"))))

					// m is the ideal of S that p(t) and w − r(t) span.
					rootR := b.TermAs[A]("w - polynomial_eval(r, t)")
					span := b.TermAs[Set[A]]("ideal_span(«ringS», {polynomial_eval(p, t), w - polynomial_eval(r, t)})")
					generatorsIn := b.Have(
						"p(t) and w − r(t) lie in S",
						"polynomial_eval(p, t) ∈ S ∧ w - polynomial_eval(r, t) ∈ S",
						By(pMem[1], inS[2], rMem[1], comm_ring.SubIn.Read(ringOnS)))
					spanned := b.Conjuncts(
						b.Have(
							"their span is an ideal of S holding both",
							"ring_ideal(«ringS», ideal_span(«ringS», {polynomial_eval(p, t), w - polynomial_eval(r, t)})) ∧ "+
								"polynomial_eval(p, t) ∈ "+
								"ideal_span(«ringS», {polynomial_eval(p, t), w - polynomial_eval(r, t)}) ∧ "+
								"w - polynomial_eval(r, t) ∈ "+
								"ideal_span(«ringS», {polynomial_eval(p, t), w - polynomial_eval(r, t)})",
							BySets(generatorsIn, ring_ideal.SpanIdeal.Read(ringOnS), ring_ideal.SpanContains)),
						"the span is an ideal of S",
						"holding p(t)",
						"and w − r(t)")
					cover := b.Have(
						"each member z = c + d·w of m lies in the span: c + "+
							"d·r(t) = z − d·(w − r(t)) lies in m ∩ k[t] = p(t)·k[t]",
						"∀z:A. z ∈ m ⇒ z ∈ ideal_span(«ringS», {polynomial_eval(p, t), w - polynomial_eval(r, t)})",
						Derive(func(sub *Argument) {
							z := sub.FixAs[A]("z")
							zIn := sub.Assume()
							c, d, coords := sub.Unpack2As[A, A](GroupPremises(zIn, coordinates.At(z)), "c", "d")
							parts := sub.Conjuncts(
								coords,
								"c lies in k[t]",
								"so does d",
								"z = c + d·w")
							cMem := sub.Conjuncts(
								GroupPremises(parts[0], lift.At(c)),
								"c lies in S",
								"and in L")
							dMem := sub.Conjuncts(
								GroupPremises(parts[1], lift.At(d)),
								"d lies in S",
								"and in L")
							dShift := sub.TermAs[A]("d * (w - polynomial_eval(r, t))")
							shiftedC := sub.Have(
								"c + d·r(t) = z − d·(w − r(t))",
								"c + d * polynomial_eval(r, t) = z + -(d * (w - polynomial_eval(r, t)))",
								parts[2].Rw(),
								ByArith(ring, cMem[1], dMem[1], wM, rMem[2]))
							inM := sub.Have(
								"which lies in m, z and w − r(t) lying there",
								"c + d * polynomial_eval(r, t) ∈ m",
								shiftedC.Rw(),
								By(
									ideal,
									zIn,
									reduced,
									dMem[0],
									ring_ideal.IdealMul.At(ringS, m, d, rootR),
									ring_ideal.IdealSub.Read(ringOnS).At(m, z, dShift)))
							inKt := sub.Have(
								"and in k[t]",
								"c + d * polynomial_eval(r, t) ∈ «polynomials»",
								By(parts[0], parts[1], rMem[0], comm_ring.AddIn.Read(ringOnKt), comm_ring.MulIn.Read(ringOnKt)))
							e, multiple := sub.ObtainAs[A](
								"so it lies in m ∩ k[t] = p(t)·k[t]: it is e·p(t) with e in k[t]",
								"∃e:A. e ∈ «polynomials» ∧ c + d * polynomial_eval(r, t) = e * polynomial_eval(p, t)",
								BySets(
									contraction,
									inM,
									inKt,
									ring_ideal.PrincipalIdealMultiples.Read(ringOnKt).At(proof.MemberOf(pValue, pMem[0]))))
							eParts := sub.Conjuncts(
								multiple,
								"e lies in k[t]",
								"c + d·r(t) = e·p(t)")
							eMem := sub.Conjuncts(
								GroupPremises(eParts[0], lift.At(e)),
								"e lies in S",
								"and in L")
							combination := sub.Have(
								"z = c + d·w = e·p(t) + d·(w − r(t))",
								"z = e * polynomial_eval(p, t) + d * (w - polynomial_eval(r, t))",
								parts[2].Rw(),
								ByArith(ring, eParts[1], cMem[1], dMem[1], eMem[1], wM, pMem[2], rMem[2]))
							sub.Show(
								"a combination of the two generators by members of S",
								combination.Rw(),
								By(
									spanned[0],
									spanned[1],
									spanned[2],
									eMem[0],
									dMem[0],
									ring_ideal.IdealMul.At(ringS, span, e, pValue),
									ring_ideal.IdealMul.At(ringS, span, d, rootR),
									ring_ideal.IdealAdd.At(ringS, span, sub.TermAs[A]("e * polynomial_eval(p, t)"), dShift)))
						}))
					firstKind := b.Have(
						"so m is the span of p(t) and w − r(t), the span lying in m",
						"m = ideal_span(«ringS», {polynomial_eval(p, t), w - polynomial_eval(r, t)})",
						BySets(
							cover,
							ideal,
							pInM,
							reduced,
							ring_ideal.SpanLeast.At(
								ringS, b.TermAs[Set[A]]("{polynomial_eval(p, t), w - polynomial_eval(r, t)}"), m)))
					b.Do(Left())
					b.Take(r)
					b.Show(
						"r is a square root of w² modulo p(t) of degree below p's, and m = (p(t), w − r(t))",
						By(
							rOver,
							polynomial.DegreeBelow.At(zero, proof.InhabitFrom(r, rShort)),
							positive,
							polynomial.DegreeVecZero.At(zero),
							rMem[0],
							reduced,
							rootSquares.At(b.TermAs[A]("polynomial_eval(r, t)")),
							firstKind))
				})
			a.Otherwise(
				"w² is no square modulo p(t): m is the inert p(t)·S",
				func(b *Argument, noRoot Fact) {
					inert := b.Have(
						"each member z = c + d·w of m is a multiple of p(t) in S",
						"∀z:A. z ∈ m ⇒ z ∈ ideal_span(«ringS», {polynomial_eval(p, t)})",
						Derive(func(sub *Argument) {
							z := sub.FixAs[A]("z")
							zIn := sub.Assume()
							c, d, coords := sub.Unpack2As[A, A](GroupPremises(zIn, coordinates.At(z)), "c", "d")
							parts := sub.Conjuncts(
								coords,
								"c lies in k[t]",
								"so does d",
								"z = c + d·w")
							cMem := sub.Conjuncts(
								GroupPremises(parts[0], lift.At(c)),
								"c lies in S",
								"and in L")
							dPolynomial, bFacts := sub.ObtainAs[Fun[Nat, A]](
								"d is the value at t of a polynomial b over k",
								"∃b:(num → A). polynomial_over(k, b) ∧ d = polynomial_eval(b, t)",
								By(inImage.At(d), parts[1]))
							bParts := sub.Conjuncts(
								bFacts,
								"b is a polynomial over k",
								"whose value at t is d")
							bMem := sub.Conjuncts(
								GroupPremises(bParts[0], values.At(dPolynomial)),
								"b(t) lies in k[t]",
								"in S",
								"and in L")
							sub.Cases(sub.Term("polynomial_divides(field_ring(restrict_field(L, k)), p, b)"))
							sub.When(
								"p divides b: d = p(t)·e(t), so c = z − e(t)·w·p(t) lies in m ∩ k[t] = p(t)·k[t]",
								func(br *Argument, divides Fact) {
									e, eFacts := br.UnpackAs[Fun[Nat, A]](
										br.Unfolded(divides, polynomial_division.PolynomialDividesDef), "e")
									eParts := br.Conjuncts(
										eFacts,
										"e is a polynomial over k",
										"b = p·e")
									eMem := br.Conjuncts(
										GroupPremises(eParts[0], values.At(e)),
										"e(t) lies in k[t]",
										"in S",
										"and in L")
									factor := br.Have(
										"d = b(t) = p(t)·e(t), evaluation multiplying",
										"d = polynomial_eval(p, t) * polynomial_eval(e, t)",
										By(
											bParts[1],
											eParts[1],
											overL.At(p),
											overL.At(e),
											pOver,
											eParts[0],
											polynomial_evaluation.EvalMul.Read(ring).At(p, e, tM)))
									rest := br.Have(
										"c = z − e(t)·w·p(t)",
										"c = z + -(polynomial_eval(e, t) * w * polynomial_eval(p, t))",
										parts[2].Rw(),
										factor.Rw(),
										ByArith(ring, cMem[1], wM, pMem[2], eMem[2]))
									ew := br.TermAs[A]("polynomial_eval(e, t) * w")
									ewp := br.TermAs[A]("polynomial_eval(e, t) * w * polynomial_eval(p, t)")
									cInM := br.Have(
										"which lies in m, z and p(t) lying there",
										"c ∈ m",
										rest.Rw(),
										By(
											ideal,
											zIn,
											pInM,
											eMem[1],
											inS[2],
											comm_ring.MulIn.Read(ringOnS),
											ring_ideal.IdealMul.At(ringS, m, ew, pValue),
											ring_ideal.IdealSub.Read(ringOnS).At(m, z, ewp)))
									γ, multiple := br.ObtainAs[A](
										"so c lies in m ∩ k[t] = p(t)·k[t]: c = γ·p(t) with γ in k[t]",
										"∃γ:A. γ ∈ «polynomials» ∧ c = γ * polynomial_eval(p, t)",
										BySets(
											contraction,
											cInM,
											parts[0],
											ring_ideal.PrincipalIdealMultiples.Read(ringOnKt).At(proof.MemberOf(pValue, pMem[0]))))
									γParts := br.Conjuncts(
										multiple,
										"γ lies in k[t]",
										"c = γ·p(t)")
									γMem := br.Conjuncts(
										GroupPremises(γParts[0], lift.At(γ)),
										"γ lies in S",
										"and in L")
									multipleOfP := br.Have(
										"z = c + d·w = (γ + e(t)·w)·p(t)",
										"z = (γ + polynomial_eval(e, t) * w) * polynomial_eval(p, t)",
										parts[2].Rw(),
										γParts[1].Rw(),
										factor.Rw(),
										ByArith(ring, γMem[1], wM, pMem[2], eMem[2]))
									br.Show(
										"a multiple of p(t) by the member γ + e(t)·w of S",
										BySets(
											multipleOfP,
											inS[2],
											γMem[0],
											eMem[1],
											ring_ideal.PrincipalIdealMultiples.Read(ringOnS).At(proof.MemberOf(pValue, pMem[1])),
											comm_ring.AddIn.Read(ringOnS).At(
												proof.MemberOf(γ, γMem[0]),
												comm_ring.MulIn.Read(ringOnS).At(
													proof.MemberOf(br.TermAs[A]("polynomial_eval(e, t)"), eMem[1]), proof.MemberOf(w, inS[2])))))
								})
							sub.Otherwise(
								"p does not divide b: a Bezout inverse v(t) of d modulo p(t) makes w + c·v(t) a root of w² in m",
								func(br *Argument, coprime Fact) {
									// IrreducibleCoprime, read at the field k, asks irreducibility over k's own field ring, not L's restricted to k.
									irreducibleK := br.Have(
										"p is irreducible over the field k",
										"polynomial_irreducible(field_ring(restrict_field(L, k)), p)",
										Unfold(polynomial_division.PolynomialIrreducibleDef))
									bezoutU, bezoutV, bezout := br.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
										"p, irreducible, and b are coprime: u·p + v·b = 1 over k",
										"∃u v:(num → A). "+
											"    polynomial_over(k, u) ∧ "+
											"    polynomial_over(k, v) ∧ "+
											"    polynomial_mul(u, p) + polynomial_mul(v, b) = basis_vector(0)",
										By(
											coprime,
											irreducibleK,
											bParts[0],
											polynomial_division.IrreducibleCoprime.Read(fieldK).At(p, dPolynomial)))
									bez := br.Conjuncts(
										bezout,
										"u is a polynomial over k",
										"so is v",
										"u·p + v·b = 1")
									bezoutUMem := br.Conjuncts(
										GroupPremises(bez[0], values.At(bezoutU)),
										"u(t) lies in k[t]",
										"in S",
										"and in L")
									bezoutVMem := br.Conjuncts(
										GroupPremises(bez[1], values.At(bezoutV)),
										"v(t) lies in k[t]",
										"in S",
										"and in L")
									inverse := br.Have(
										"evaluated at t: u(t)·p(t) + v(t)·b(t) = 1",
										"polynomial_eval(u, t) * polynomial_eval(p, t) + polynomial_eval(v, t) * polynomial_eval(b, t) = "+
											"L.one",
										By(
											bez[2],
											overL.At(bezoutU),
											overL.At(p),
											overL.At(bezoutV),
											overL.At(dPolynomial),
											bez[0],
											pOver,
											bez[1],
											bParts[0],
											polynomial.PolynomialMulOver.Read(ring).At(bezoutU, p),
											polynomial.PolynomialMulOver.Read(ring).At(bezoutV, dPolynomial),
											polynomial_evaluation.EvalAdd.Read(ring).At(
												br.TermAs[Fun[Nat, A]]("polynomial_mul(u, p)"), br.TermAs[Fun[Nat, A]]("polynomial_mul(v, b)"), tM),
											polynomial_evaluation.EvalMul.Read(ring).At(bezoutU, p, tM),
											polynomial_evaluation.EvalMul.Read(ring).At(bezoutV, dPolynomial, tM),
											polynomial_evaluation.EvalBasisVector.Read(ring).At(br.TermAs[Nat]("0"), tM),
											comm_monoid.MonoidPowDef))
									rearranged := br.Have(
										"w + c·v(t) = v(t)·z + u(t)·w·p(t), as v(t)·d = 1 − u(t)·p(t)",
										"w + c * polynomial_eval(v, t) = "+
											"polynomial_eval(v, t) * z + polynomial_eval(u, t) * w * polynomial_eval(p, t)",
										parts[2].Rw(),
										bParts[1].Rw(),
										ByArith(ring, Scaled(w, inverse), wM, cMem[1], pMem[2], bezoutUMem[2], bezoutVMem[2], bMem[2]))
									vt := br.TermAs[A]("polynomial_eval(v, t)")
									uw := br.TermAs[A]("polynomial_eval(u, t) * w")
									rootIn := br.Have(
										"which lies in m, z and p(t) lying there",
										"w + c * polynomial_eval(v, t) ∈ m",
										rearranged.Rw(),
										By(
											ideal,
											zIn,
											pInM,
											bezoutVMem[1],
											bezoutUMem[1],
											inS[2],
											comm_ring.MulIn.Read(ringOnS),
											ring_ideal.IdealMul.At(ringS, m, vt, z),
											ring_ideal.IdealMul.At(ringS, m, uw, pValue),
											ring_ideal.IdealAdd.At(
												ringS,
												m,
												br.TermAs[A]("polynomial_eval(v, t) * z"),
												br.TermAs[A]("polynomial_eval(u, t) * w * polynomial_eval(p, t)"))))
									σ := br.TermAs[A]("-(c * polynomial_eval(v, t))")
									negated := br.Have(
										"w − σ = w + c·v(t)",
										"w - -(c * polynomial_eval(v, t)) = w + c * polynomial_eval(v, t)",
										ByArith(ring, wM, cMem[1], bezoutVMem[2]))
									br.Show(
										"then w − σ lies in m, so w² ≡ σ² modulo p(t) with "+
											"σ a value at t of a polynomial over k: there is none",
										By(
											noRoot,
											parts[0],
											bezoutVMem[0],
											comm_ring.NegIn.Read(ringOnKt),
											comm_ring.MulIn.Read(ringOnKt),
											inImage.At(σ),
											negated,
											rootIn,
											rootSquares.At(σ)))
								})
						}))
					inertSpan := b.Have(
						"so m is p(t)·S, the span lying in m",
						"m = ideal_span(«ringS», {polynomial_eval(p, t)})",
						BySets(
							inert,
							ideal,
							pInM,
							ring_ideal.SpanLeast.At(ringS, b.TermAs[Set[A]]("{polynomial_eval(p, t)}"), m)))
					b.Show(
						"m is the inert p(t)·S, w² having no square root modulo p(t)",
						By(inertSpan, noRoot))
				})
		}),
})}

// ChartOneMaximalIdealClassification — the maximal ideals of chart one of
// a Weierstrass curve, by the classification of a quadratic ring at
// k[s] + k[s]·u with s = 1/x and u = y/x²: u² = s(1 + as² + bs³) lies in
// k[s], and m meets k[s] in p(s)·k[s] for a monic irreducible p over k
// (ChartOneContractsToPrime).
var ChartOneMaximalIdealClassification = chartOneMaximalIdealClassificationThm{family.Add(registry.ProofEntry{
	Name: "ChartOneMaximalIdealClassification",
	Key:  "prop_864997061992095a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀m:set(A).",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"maximal_ideal(«chartOneRing», m)",
		},
		Conclusion: "∃p:(num → A). " +
			"    polynomial_irreducible(restrict_ring(field_ring(L), k), p) ∧ " +
			"    polynomial_monic(p) ∧ " +
			"    ((∃r:(num → A). " +
			"            polynomial_over(k, r) ∧ " +
			"            polynomial_degree(r) < polynomial_degree(p) ∧ " +
			"            «u» * «u» - polynomial_eval(r, L.inv(x)) * polynomial_eval(r, L.inv(x)) ∈ " +
			"            «pIdeal»(p) ∧ " +
			"            m = " +
			"            ideal_span(«chartOneRing», " +
			"                {polynomial_eval(p, L.inv(x)), «u» - polynomial_eval(r, L.inv(x))})) ∨ " +
			"        (m = ideal_span(«chartOneRing», {polynomial_eval(p, L.inv(x))}) ∧ " +
			"            ¬∃r:(num → A). " +
			"                polynomial_over(k, r) ∧ " +
			"                «u» * «u» - polynomial_eval(r, L.inv(x)) * polynomial_eval(r, L.inv(x)) ∈ " +
			"                «pIdeal»(p)))",
		Abbrev: Abbrev{
			{Name: "u", Text: "(y * (L.inv(x) * L.inv(x)))"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, L.inv(x))"},
			{Name: "pIdeal", Text: "λp:(num → A). " +
				"    ideal_span(restrict_ring(field_ring(L), «polynomials»), {polynomial_eval(p, L.inv(x))})"},
			{Name: "chartOneRing", Text: "restrict_ring(field_ring(L), «curveChart1»)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			datum Fact,
			m *Expr[Set[A]],
			maximal Fact,
		) {
			ring := field.RingOn.Read(L)
			kSubfield := elliptic_curve.WeierstrassSubfield.Read(datum)
			unit := arg.Conjuncts(
				GroupPremises(datum, elliptic_curve.WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"s = inv(x) lies in L",
				"x · s = one",
				"s · x = one")
			sm := arg.MemberOf[on.L](arg.TermAs[A]("L.inv(x)"), unit[1])
			ym := arg.MemberOf[on.L](y, elliptic_curve.WeierstrassYInField.Read(datum).AsFact())
			um := comm_ring.MulIn.Read(ring).At(ym, comm_ring.MulIn.Read(ring).At(sm, sm))

			ks := arg.Conjuncts(
				GroupPremises(kSubfield, algebraic_element.PolynomialImageRing.Read(L).At(k, sm)),
				"k[s] is a subring of L",
				"holding k",
				"and s",
				"inside k(s)")
			coefficients := arg.Have(
				"a and b lie in k[s], as k does",
				"a ∈ «polynomials» ∧ b ∈ «polynomials»",
				BySets(
					ks[1],
					elliptic_curve.WeierstrassCoefficientA.Read(datum),
					elliptic_curve.WeierstrassCoefficientB.Read(datum)))
			square := arg.Have(
				"u² = s · (one + a · s² + b · s³) lies in k[s]",
				"«u» * «u» ∈ «polynomials»",
				GroupPremises(datum, elliptic_curve.WeierstrassChartOneEquation.Read(L).At(k, x, y, a, b)).Rw(),
				By(
					ks[2],
					coefficients,
					comm_ring.SubringOne.Read(ks[0]),
					comm_ring.SubringAdd.Read(ks[0]),
					comm_ring.SubringMul.Read(ks[0])))
			chart := arg.Have(
				"chart one is k[s] + k[s]·u",
				"weierstrass_chart_one(L, k, x, y) = "+
					"{c + d * «u»:A | c:A, d:A | c ∈ «polynomials» ∧ d ∈ «polynomials»}",
				Unfold(elliptic_curve.WeierstrassChartOneDef))

			p, contracted := arg.UnpackAs[Fun[Nat, A]](
				GroupPremises(datum, maximal, ChartOneContractsToPrime.Read(L).At(k, x, y, a, b, m)),
				"p")
			parts := arg.Conjuncts(
				contracted,
				"p is irreducible over k",
				"and monic",
				"m meets k[s] in p(s)·k[s]")
			arg.Take(p)
			arg.Show(
				"p classifies m, by the classification of the quadratic ring k[s] + k[s]·u",
				By(
					parts[0],
					parts[1],
					kSubfield,
					sm,
					um,
					square,
					chart,
					maximal,
					parts[2],
					QuadraticMaximalIdealClassification.Read(L).At(
						k, arg.TermAs[Set[A]]("weierstrass_chart_one(L, k, x, y)"), sm, um, m, p)))
		}),
})}
