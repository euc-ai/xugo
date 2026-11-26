package ideal_factorization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// IdealInductionByFiniteQuotient — induction from larger nonzero ideals reaches
// every nonzero ideal when nonzero ideals have finite quotient: strong
// induction on the index of the ideal, which strict enlargement lowers.
var IdealInductionByFiniteQuotient = idealInductionByFiniteQuotientThm{family.Add(registry.ProofEntry{
	Name: "IdealInductionByFiniteQuotient",
	Key:  "prop_d09171a07178f54",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀P:(set(A) → bool). ∀I:set(A).",
		Hypotheses: []string{
			"∀H:set(A). ring_ideal(R, H) ∧ H ≠ {R.zero} ⇒ finite(left_cosets(R.add, R.carrier, H))",
			"P(R.carrier)",
			"∀H:set(A). " +
				"    ring_ideal(R, H) ∧ " +
				"    H ≠ {R.zero} ∧ " +
				"    H ≠ R.carrier ∧ " +
				"    (∀J:set(A). ring_ideal(R, J) ∧ J ≠ {R.zero} ∧ H ⊆ J ∧ H ≠ J ⇒ P(J)) ⇒ " +
				"    P(H)",
			"ring_ideal(R, I)",
			"I ≠ {R.zero}",
		},
		Conclusion: "P(I)",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], P *Arrow[Set[A], Bool], hypotheses Fact) {
		parts := a.Conjuncts(
			hypotheses,
			"every nonzero ideal has finite quotient",
			"P holds at the unit ideal",
			"P descends from strict larger nonzero ideals")
		finite, unit, descend := parts[0], parts[1], parts[2]
		indexed := a.Have(
			"P holds at every index",
			"∀n:num. ∀I:set(A). ring_ideal(R, I) ∧ I ≠ {R.zero} ∧ ideal_index(R, I) = n ⇒ P(I)",
			ByInduction(nat_order.StrongInduction,
				Case(
					"smaller indices supply the larger ideals",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("n")
						ih := b.Assume()
						I := b.FixAs[Set[A]]("I")
						datum := b.Assume()
						b.Do(Unless(
							b.Term("I = R.carrier"),
							"the unit ideal already satisfies P",
							Given(func(c *Argument, equal Fact) {
								c.Show(
									"P holds at the unit ideal",
									equal.Rw(),
									By(unit))
							})))
						proper := b.Hyp("I ≠ R.carrier")
						larger := b.Have(
							"every strict larger nonzero ideal satisfies P",
							"∀J:set(A). ring_ideal(R, J) ∧ J ≠ {R.zero} ∧ I ⊆ J ∧ I ≠ J ⇒ P(J)",
							Derive(func(c *Argument) {
								J := c.FixAs[Set[A]]("J")
								above := c.Assume()
								smaller := c.Have(
									"strict enlargement lowers the index",
									"ideal_index(R, J) < ideal_index(R, I)",
									By(finite.At(I), datum, above, quotient_ring.StrictIdealInclusionLowersIndex.Read(R).At(I, J)))
								c.Show(
									"the smaller index supplies P at J",
									By(Normalized, datum, above, smaller, ih.At(c.TermAs[Nat]("ideal_index(R, J)"), J)))
							}))
						b.Show(
							"P descends to I",
							By(datum, proper, larger, descend.At(I)))
					}))))
		a.Show(
			"every nonzero ideal satisfies P",
			Derive(func(b *Argument) {
				I := b.FixAs[Set[A]]("I")
				nonzero := b.Assume()
				b.Show(
					"apply the indexed result at the index of I",
					By(nonzero, indexed.At(b.TermAs[Nat]("ideal_index(R, I)"), I)))
			}))
	}),
})}

// AlmostIntegralIsIntegral — bounded denominators give a monic relation when
// nonzero ideals have finite quotient: bounded polynomial values form a stabilizing
// ideal chain, and cancellation removes the common denominator.
var AlmostIntegralIsIntegral = almostIntegralIsIntegralThm{family.Add(registry.ProofEntry{
	Name: "AlmostIntegralIsIntegral",
	Key:  "prop_b56aebc278cb41a4",
	Reading: "The finite-quotient hypothesis is essential; bounded " +
		"denominators alone do not imply integrality in an arbitrary domain.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x c:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"∀H:set(A). ring_ideal(«R», H) ∧ H ≠ {L.zero} ⇒ finite(left_cosets(L.add, S, H))",
			"x ∈ L.carrier",
			"c ∈ S",
			"c ≠ L.zero",
			"∀j:num. c * monoid_pow(L.mul, L.one, x, j) ∈ S",
		},
		Conclusion: "integral_over(«R», x)",
		Abbrev: Abbrev{
			{Name: "Eval", Text: "λp:(num → A). polynomial_eval(p, x)"},
			{Name: "Represented", Text: "λn:num. λy:A. ∃p:(num → A). " +
				"    polynomial_over(S, p) ∧ vec⟨n + 1⟩(p) ∧ y = c * polynomial_eval(p, x)"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], x, c *Expr[A], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a subring of L",
			"nonzero ideals have finite quotient",
			"x lies in the field",
			"c lies in the subring",
			"c is nonzero",
			"c clears every power into the subring")
		subringS, quotients, xIn, cIn, nonzero, powers :=
			parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
		fieldRing := field.RingOn.Read(L)
		inField := a.Have(
			"the subring lies in the field",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subringS)))
		ring := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(«R»)",
			By(subringS, comm_ring.SubringRingOn.Read(fieldRing).At(S)))
		fieldMonoid := comm_ring.MulMonoidOn.Read(fieldRing)
		polynomialRing := polynomial.PolynomialRingOn.Read(ring)
		polynomialModule := polynomial.PolynomialModuleOn.Read(ring)
		C, chainDefinition := a.LetAs[Fun[Nat, Set[A]]]("C", "λn:num. {y:A | y ∈ S ∧ «Represented»(n, y)}")
		zeroEvaluation := a.Have(
			"the zero polynomial evaluates to zero",
			"«Eval»(vec_zero) = L.zero",
			Simp(Fwd(polynomial_evaluation.PolynomialEvalDef), Fwd(vec_space.VecZeroDef)),
			Derive(func(b *Argument) {
				emptySupport := b.Have(
					"the zero polynomial has empty support",
					"fun_support(L.zero, λi:num. L.zero) = ∅",
					BySets())
				b.Do(emptySupport.Rw())
				b.Show(
					"the empty sum is zero",
					By(module.ModuleSumEmpty))
			}))
		cField := a.Have(
			"the denominator lies in the field",
			"c ∈ L.carrier",
			BySets(cIn, inField))
		representations := a.Have(
			"read ideal membership as a bounded polynomial representation",
			Statement{
				Binders: "∀n:num. ∀y:A.",
				Hypotheses: []string{
					"y ∈ C(n)",
				},
				Conclusion: "∃p:(num → A). polynomial_over(S, p) ∧ vec⟨n + 1⟩(p) ∧ y = c * «Eval»(p) ∧ y ∈ S",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.FixAs[A]("y")
				member := b.Assume()
				b.Show(
					"membership supplies the bounded representative",
					BySets(Normalized, chainDefinition, member))
			}))

		ideals := a.Have(
			"bounded polynomial values inside S form ideals",
			"∀n:num. ring_ideal(«R», C(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Do(Simp(Fwd(ring_ideal.RingIdealDef)), SplitConjAll(
					Case(
						"the bounded values lie in S",
						BySets(Normalized, chainDefinition)),
					Case(
						"the bounded values contain zero",
						Derive(func(d *Argument) {
							zeroValue := d.Have(
								"zero is represented by the zero polynomial",
								"L.zero = c * «Eval»(vec_zero)",
								zeroEvaluation.Rw(),
								By(cField, comm_ring.MulRightZeroOn.Read(fieldRing)))
							represented := d.Have(
								"the zero representative satisfies the support bound",
								"∃p:(num → A). polynomial_over(S, p) ∧ vec⟨n + 1⟩(p) ∧ L.zero = c * polynomial_eval(p, x)",
								Derive(func(e *Argument) {
									e.Take(e.TermAs[Fun[Nat, A]]("vec_zero"))
									e.Show(
										"the zero polynomial is bounded and represents zero",
										By(zeroValue, polynomial.VecZeroOver.Read(ring), vec_space.VecZero))
								}))
							d.Show(
								"zero belongs to the bounded values",
								BySets(Normalized, chainDefinition, represented, comm_ring.ZeroIn.Read(ring)))
						})),
					Case(
						"the bounded values are closed under addition",
						Derive(func(d *Argument) {
							u := d.FixAs[A]("u")
							v := d.FixAs[A]("v")
							bothInC := d.Assume()
							_, left := d.UnpackAs[Fun[Nat, A]](GroupPremises(bothInC, representations.At(n, u)), "p₁")
							_, right := d.UnpackAs[Fun[Nat, A]](GroupPremises(bothInC, representations.At(n, v)), "p₂")
							leftAmbient := d.Have(
								"the first representative has field coefficients",
								"polynomial_over(L.carrier, p₁)",
								By(left, inField, polynomial.PolynomialOverMono))
							rightAmbient := d.Have(
								"the second representative has field coefficients",
								"polynomial_over(L.carrier, p₂)",
								By(right, inField, polynomial.PolynomialOverMono))
							sumOver := d.Have(
								"the sum has coefficients in S",
								"polynomial_over(S, vec_add(p₁, p₂))",
								By(left, right, comm_ring.AddIn.Read(polynomialRing)))
							sumBound := d.Have(
								"the sum has the same support bound",
								"vec⟨n + 1⟩(vec_add(p₁, p₂))",
								By(left, right, vec_space.VecAddOn.Read(fieldRing)))
							evaluation := d.Have(
								"evaluation preserves addition",
								"«Eval»(vec_add(p₁, p₂)) = «Eval»(p₁) + «Eval»(p₂)",
								By(leftAmbient, rightAmbient, xIn, polynomial_evaluation.EvalAdd.Read(fieldRing)))
							leftValueIn := d.Have(
								"the first value lies in the field",
								"«Eval»(p₁) ∈ L.carrier",
								By(leftAmbient, xIn, polynomial_evaluation.EvalIn.Read(fieldRing)))
							rightValueIn := d.Have(
								"the second value lies in the field",
								"«Eval»(p₂) ∈ L.carrier",
								By(rightAmbient, xIn, polynomial_evaluation.EvalIn.Read(fieldRing)))
							sumInS := d.Have(
								"the sum belongs to S",
								"u + v ∈ S",
								By(left, right, comm_ring.AddIn.Read(ring)))
							leftParts := d.Conjuncts(
								left,
								"the first polynomial is over S",
								"the first polynomial is bounded",
								"the first polynomial represents u",
								"u belongs to S")
							rightParts := d.Conjuncts(
								right,
								"the second polynomial is over S",
								"the second polynomial is bounded",
								"the second polynomial represents v",
								"v belongs to S")
							sumValue := d.Have(
								"the polynomial sum represents the ideal sum",
								"u + v = c * «Eval»(vec_add(p₁, p₂))",
								leftParts[2].Rw(),
								rightParts[2].Rw(),
								evaluation.Rw(),
								ByArith(fieldRing, cField, leftValueIn, rightValueIn))
							represented := d.Have(
								"the sum has a bounded representative",
								"∃p:(num → A). polynomial_over(S, p) ∧ vec⟨n + 1⟩(p) ∧ u + v = c * polynomial_eval(p, x)",
								Derive(func(e *Argument) {
									e.Take(e.TermAs[Fun[Nat, A]]("vec_add(p₁, p₂)"))
									e.Show(
										"the polynomial sum is the required representative",
										By(sumOver, sumBound, sumValue))
								}))
							d.Show(
								"the sum belongs to the bounded values",
								BySets(Normalized, chainDefinition, represented, sumInS))
						})),
					Case(
						"the bounded values absorb multiplication by S",
						Derive(func(d *Argument) {
							d.FixAs[A]("r")
							u := d.FixAs[A]("u")
							members := d.Assume()
							_, representative := d.UnpackAs[Fun[Nat, A]](GroupPremises(members, representations.At(n, u)), "p")
							rField := d.Have(
								"the scalar lies in the field",
								"r ∈ L.carrier",
								BySets(members, inField))
							ambient := d.Have(
								"the representative has field coefficients",
								"polynomial_over(L.carrier, p)",
								By(representative, inField, polynomial.PolynomialOverMono))
							scaledOver := d.Have(
								"the scaled polynomial has coefficients in S",
								"polynomial_over(S, vec_scalar_mul(r, p))",
								By(members, representative, module.SmulIn.Read(polynomialModule)))
							scaledBound := d.Have(
								"scaling preserves the support bound",
								"vec⟨n + 1⟩(vec_scalar_mul(r, p))",
								By(rField, representative, vec_space.VecSmulOn.Read(fieldRing)))
							evaluation := d.Have(
								"evaluation preserves scaling",
								"«Eval»(vec_scalar_mul(r, p)) = r * «Eval»(p)",
								By(rField, xIn, ambient, polynomial_evaluation.EvalScalar.Read(fieldRing)))
							valueIn := d.Have(
								"the polynomial value lies in the field",
								"«Eval»(p) ∈ L.carrier",
								By(ambient, xIn, polynomial_evaluation.EvalIn.Read(fieldRing)))
							productInS := d.Have(
								"the product belongs to S",
								"r * u ∈ S",
								By(members, representative, comm_ring.MulIn.Read(ring)))
							representation := d.Conjuncts(
								representative,
								"the polynomial is over S",
								"the polynomial is bounded",
								"the polynomial represents u",
								"u belongs to S")
							productValue := d.Have(
								"the scaled polynomial represents the product",
								"r * u = c * «Eval»(vec_scalar_mul(r, p))",
								representation[2].Rw(),
								evaluation.Rw(),
								ByArith(fieldRing, rField, cField, valueIn))
							represented := d.Have(
								"the product has a bounded representative",
								"∃p:(num → A). polynomial_over(S, p) ∧ vec⟨n + 1⟩(p) ∧ r * u = c * polynomial_eval(p, x)",
								Derive(func(e *Argument) {
									e.Take(e.TermAs[Fun[Nat, A]]("vec_scalar_mul(r, p)"))
									e.Show(
										"the scaled polynomial is the required representative",
										By(scaledOver, scaledBound, productValue))
								}))
							d.Show(
								"the product belongs to the bounded values",
								BySets(Normalized, chainDefinition, represented, productInS))
						})),
				))
			}))
		constantValue := a.Have(
			"the constant-one polynomial represents c",
			"c = c * «Eval»(basis_vector(0))",
			Simp(
				Fwd(polynomial_evaluation.EvalBasisVector.Read(fieldRing)),
				Fwd(comm_monoid.MonoidPowDef),
				Fwd(comm_monoid.RightIdentityOn.Read(fieldMonoid))),
			Basic())
		containsC := a.Have(
			"every chain ideal contains c",
			"∀n:num. c ∈ C(n)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				positive := b.Have(
					"the constant coefficient is inside the support bound",
					"0 < n + 1",
					ByArith())
				represented := b.Have(
					"c has a bounded polynomial representative",
					"∃p:(num → A). polynomial_over(S, p) ∧ vec⟨n + 1⟩(p) ∧ c = c * polynomial_eval(p, x)",
					Derive(func(d *Argument) {
						d.Take(d.TermAs[Fun[Nat, A]]("basis_vector(0)"))
						d.Show(
							"the constant-one polynomial gives c",
							By(constantValue, positive, vec_space.VecBasisVector, polynomial.BasisVectorOver.Read(ring)))
					}))
				b.Show(
					"c belongs to the bounded values",
					BySets(Normalized, chainDefinition, represented, cIn))
			}))
		increasing := a.Have(
			"the chain increases as the support bound grows",
			"∀n:num. C(n) ⊆ C(n + 1)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				u := b.FixAs[A]("u")
				xInC := b.Assume()
				p, representative := b.UnpackAs[Fun[Nat, A]](GroupPremises(xInC, representations.At(n, u)), "p")
				ordered := b.Have(
					"the next support bound is larger",
					"n + 1 ≤ n + 1 + 1",
					ByArith())
				bound := b.Have(
					"the representative fits the next bound",
					"vec⟨n + 1 + 1⟩(p)",
					By(representative, ordered, vec_space.VecMono))
				represented := b.Have(
					"the same polynomial represents u at the next bound",
					"∃p:(num → A). polynomial_over(S, p) ∧ vec⟨n + 1 + 1⟩(p) ∧ u = c * polynomial_eval(p, x)",
					Derive(func(d *Argument) {
						d.Take(p)
						d.Show(
							"the retained polynomial gives the inclusion",
							By(representative, bound))
					}))
				b.Show(
					"u belongs to the next ideal",
					BySets(Normalized, chainDefinition, representative, represented))
			}))
		singletonInS := a.Have(
			"the generator singleton lies in S",
			"{c} ⊆ S",
			BySets(cIn))
		principalIdeal := a.Have(
			"the principal span is an ideal",
			"ring_ideal(«R», ideal_span(«R», {c}))",
			By(ring, singletonInS, ring_ideal.SpanIdeal))
		cInPrincipal := a.Have(
			"the principal span contains its generator",
			"c ∈ ideal_span(«R», {c})",
			BySets(ring_ideal.SpanContains))
		principalNonzero := a.Have(
			"the principal ideal is nonzero",
			"ideal_span(«R», {c}) ≠ {L.zero}",
			BySets(cInPrincipal, nonzero))
		principal := a.TermAs[Set[A]]("ideal_span(«R», {c})")
		finitePrincipal := a.Have(
			"the principal quotient is finite",
			"finite(left_cosets(L.add, S, ideal_span(«R», {c})))",
			By(principalIdeal, principalNonzero, quotients.At(principal)))
		firstIndex := a.TermAs[Nat]("0")
		first := a.TermAs[Set[A]]("C(0)")
		singletonInFirst := a.Have(
			"the generator singleton lies in the first ideal",
			"{c} ⊆ C(0)",
			BySets(containsC.At(firstIndex)))
		principalInFirst := a.Have(
			"the principal ideal lies in the first ideal",
			"ideal_span(«R», {c}) ⊆ C(0)",
			By(
				ideals.At(firstIndex),
				singletonInFirst,
				ring_ideal.SpanLeast.At(a.TermAs[RingOps[A]]("«R»"), a.TermAs[Set[A]]("{c}"), first)))
		_, stabilizes := a.ObtainAs[Nat](
			"the bounded-value ideal chain stabilizes",
			"∃N:num. ∀n:num. N ≤ n ⇒ C(n) = C(N)",
			By(
				principalIdeal,
				finitePrincipal,
				principalInFirst,
				ideals,
				increasing,
				quotient_ring.FiniteIndexChainStabilizes.Read(ring).At(principal, C)),
			Named("N"))
		next := a.TermAs[Nat]("N + 1")
		monomialEvaluation := a.Have(
			"the next monomial evaluates to the next power",
			"«Eval»(basis_vector(N + 1)) = monoid_pow(L.mul, L.one, x, N + 1)",
			By(xIn, polynomial_evaluation.EvalBasisVector.Read(fieldRing)))
		monomialFits := a.Have(
			"the next monomial fits the next support bound",
			"N + 1 < N + 1 + 1",
			ByArith())
		nextRepresented := a.Have(
			"the cleared next power has a monomial representative",
			"∃p:(num → A). "+
				"    polynomial_over(S, p) ∧ "+
				"    vec⟨N + 1 + 1⟩(p) ∧ "+
				"    c * monoid_pow(L.mul, L.one, x, N + 1) = c * polynomial_eval(p, x)",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Fun[Nat, A]]("basis_vector(N + 1)"))
				b.Show(
					"the monomial gives the cleared next power",
					By(
						monomialEvaluation,
						monomialFits,
						vec_space.VecBasisVector,
						polynomial.BasisVectorOver.Read(ring)))
			}))
		inNext := a.Have(
			"the cleared next power lies in the next ideal",
			"c * monoid_pow(L.mul, L.one, x, N + 1) ∈ C(N + 1)",
			BySets(Normalized, chainDefinition, powers.At(next), nextRepresented))
		after := a.Have(
			"the successor index is after stabilization",
			"N ≤ N + 1",
			ByArith())
		inStable := a.Have(
			"stabilization puts the next power in the stable ideal",
			"c * monoid_pow(L.mul, L.one, x, N + 1) ∈ C(N)",
			By(inNext, after, stabilizes.At(next)))
		_, bounded := a.ObtainAs[Fun[Nat, A]](
			"choose the bounded polynomial relation",
			"∃p:(num → A). "+
				"    polynomial_over(S, p) ∧ "+
				"    vec⟨N + 1⟩(p) ∧ "+
				"    c * monoid_pow(L.mul, L.one, x, N + 1) = c * polynomial_eval(p, x)",
			BySets(Normalized, chainDefinition, inStable),
			Named("p"))
		ambient := a.Have(
			"the bounded polynomial has field coefficients",
			"polynomial_over(L.carrier, p)",
			By(bounded, inField, polynomial.PolynomialOverMono))
		valueIn := a.Have(
			"the bounded polynomial value lies in the field",
			"«Eval»(p) ∈ L.carrier",
			By(ambient, xIn, polynomial_evaluation.EvalIn.Read(fieldRing)))
		cancelled := a.Have(
			"cancel the common nonzero denominator",
			"monoid_pow(L.mul, L.one, x, N + 1) = «Eval»(p)",
			By(
				nonzero,
				cField,
				xIn,
				comm_monoid.PowIn.Read(fieldMonoid),
				valueIn,
				bounded,
				integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(L))))

		q, polynomialDefinition := a.LetAs[Fun[Nat, A]](
			"q", "vec_add(basis_vector(N + 1), vec_scalar_mul(-L.one, p))")
		negativeOneInS := a.Have(
			"negative one belongs to S",
			"-L.one ∈ S",
			By(comm_ring.OneIn.Read(ring), comm_ring.NegIn.Read(ring)))
		negativeOneField := a.Have(
			"negative one lies in the field",
			"-L.one ∈ L.carrier",
			BySets(negativeOneInS, inField))
		negativeOver := a.Have(
			"the negative lower terms have coefficients in S",
			"polynomial_over(S, vec_scalar_mul(-L.one, p))",
			By(negativeOneInS, bounded, module.SmulIn.Read(polynomialModule)))
		monomialOver := a.Have(
			"the leading monomial has coefficients in S",
			"polynomial_over(S, basis_vector(N + 1))",
			By(polynomial.BasisVectorOver.Read(ring)))
		qOver := a.Have(
			"the monic candidate has coefficients in S",
			"polynomial_over(S, q)",
			polynomialDefinition.Rw(),
			By(negativeOver, monomialOver, comm_ring.AddIn.Read(polynomialRing)))
		wider := a.Have(
			"the lower support bound fits the candidate bound",
			"N + 1 ≤ suc(N + 1)",
			ByArith())
		lowerBound := a.Have(
			"the lower polynomial fits the candidate bound",
			"vec⟨suc(N + 1)⟩(p)",
			By(bounded, wider, vec_space.VecMono))
		leadingFits := a.Have(
			"the leading term fits the candidate bound",
			"N + 1 < suc(N + 1)",
			ByArith())
		negativeBound := a.Have(
			"the negative lower terms fit the candidate bound",
			"vec⟨suc(N + 1)⟩(vec_scalar_mul(-L.one, p))",
			By(negativeOneField, lowerBound, vec_space.VecSmulOn.Read(fieldRing)))
		qBound := a.Have(
			"the candidate has no coefficients above N+1",
			"vec⟨suc(N + 1)⟩(q)",
			polynomialDefinition.Rw(),
			By(leadingFits, vec_space.VecBasisVector, negativeBound, vec_space.VecAddOn.Read(fieldRing)))
		atBound := a.Have(
			"N+1 is at the lower polynomial's support bound",
			"N + 1 ≤ N + 1",
			ByArith())
		lowerVanishes := a.Have(
			"the lower polynomial vanishes at N+1",
			"p(N + 1) = L.zero",
			By(bounded, atBound, vec_space.VecDef))
		leadingCoefficient := a.Have(
			"the leading coefficient is one",
			"q(N + 1) = L.one",
			polynomialDefinition.Rw(),
			Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
			lowerVanishes.Rw(),
			ByArith(fieldRing, negativeOneField))
		degreeBound := a.Have(
			"the degree is at most N+1",
			"polynomial_degree(q) ≤ N + 1",
			By(qBound, polynomial.DegreeLeast))
		degree := a.Have(
			"the candidate has exact degree N+1",
			"polynomial_degree(q) = N + 1",
			Derive(func(b *Argument) {
				different := b.SupposeNot()
				below := b.Have(
					"a smaller degree would omit the leading coefficient",
					"suc(polynomial_degree(q)) ≤ N + 1",
					ByArith(degreeBound, different))
				vanishes := b.Have(
					"the leading coefficient would vanish",
					"q(N + 1) = L.zero",
					By(qOver, polynomial.DegreeVec, below, vec_space.VecDef))
				b.Show(
					"one cannot equal zero",
					By(Normalized, leadingCoefficient, vanishes, field.OneNotZeroOn.Read(L)))
			}))
		monic := a.Have(
			"the candidate is monic",
			"polynomial_monic(q)",
			Simp(Fwd(polynomial.PolynomialMonicDef)),
			degree.Rw(),
			By(leadingCoefficient))
		positiveDegree := a.Have(
			"the monic relation has positive degree",
			"0 < polynomial_degree(q)",
			ByArith(degree))
		negativeAmbient := a.Have(
			"the negative lower terms have field coefficients",
			"polynomial_over(L.carrier, vec_scalar_mul(-L.one, p))",
			By(negativeOver, inField, polynomial.PolynomialOverMono))
		monomialAmbient := a.Have(
			"the leading monomial has field coefficients",
			"polynomial_over(L.carrier, basis_vector(N + 1))",
			By(monomialOver, inField, polynomial.PolynomialOverMono))
		negativeEvaluation := a.Have(
			"evaluation preserves the negative scalar",
			"«Eval»(vec_scalar_mul(-L.one, p)) = -L.one * «Eval»(p)",
			By(negativeOneField, xIn, ambient, polynomial_evaluation.EvalScalar.Read(fieldRing)))
		sumEvaluation := a.Have(
			"evaluation adds the leading and lower terms",
			"«Eval»(vec_add(basis_vector(N + 1), vec_scalar_mul(-L.one, p))) = "+
				"«Eval»(basis_vector(N + 1)) + «Eval»(vec_scalar_mul(-L.one, p))",
			By(negativeAmbient, monomialAmbient, xIn, polynomial_evaluation.EvalAdd.Read(fieldRing)))
		vanishes := a.Have(
			"the candidate evaluates to zero at x",
			"«Eval»(q) = L.zero",
			polynomialDefinition.Rw(),
			sumEvaluation.Rw(),
			negativeEvaluation.Rw(),
			monomialEvaluation.Rw(),
			cancelled.Rw(),
			ByArith(fieldRing, negativeOneField, valueIn))
		a.Do(Unfold(integral_element.IntegralOverDef))
		a.Take(q)
		a.Show(
			"the explicit monic positive-degree relation proves integrality",
			By(qOver, monic, positiveDegree, vanishes))
	}),
})}

// QuotientByMaximalStep — dividing an invertible maximal ideal m out of a
// nonzero ideal I of finite index that it contains splits the index: the
// index of I is the index of m times the index of the quotient I m⁻¹.
var QuotientByMaximalStep = quotientByMaximalStepThm{family.Add(registry.ProofEntry{
	Name: "QuotientByMaximalStep",
	Key:  "prop_8fc9189562548ab6",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S I m:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"ring_ideal(«R», I)",
			"I ≠ {L.zero}",
			"maximal_ideal(«R», m)",
			"I ⊆ m",
			"invertible_fractional(field_ring(L), S, m)",
			"finite(left_cosets(L.add, S, I))",
		},
		Conclusion: "ideal_index(«R», I) = " +
			"ideal_index(«R», m) * " +
			"ideal_index(«R», fractional_mul(field_ring(L), S, I, fractional_inverse(field_ring(L), S, m)))",
	}, func(a *Argument, L field.FieldFact[on.L], S, I, m *Expr[Set[A]], h Fact) {
		p := a.Conjuncts(
			h,
			"S is a subring of L",
			"I is an ideal",
			"I is nonzero",
			"m is maximal",
			"I lies in m",
			"m is invertible",
			"S/I is finite")
		subringS, idealI, nonzero, maximal, iInM, invertible, finiteI :=
			p[0], p[1], p[2], p[3], p[4], p[5], p[6]
		R := a.TermAs[RingOps[A]]("«R»")
		J, jDef := a.LetAs[Set[A]](
			"J", "fractional_mul(field_ring(L), S, I, fractional_inverse(field_ring(L), S, m))")
		indexJ := a.TermAs[Nat]("ideal_index(«R», J)")
		indexM := a.TermAs[Nat]("ideal_index(«R», m)")
		idealM := a.Have(
			"the maximal ideal m is an ideal",
			"ring_ideal(«R», m)",
			By(ring_ideal.MaximalIdealIdeal.Read(maximal)))
		divided := a.Have(
			"dividing I by the invertible m gives an ideal J above I with m · J = I",
			"ring_ideal(«R», J) ∧ I = fractional_mul(field_ring(L), S, m, J) ∧ I ⊆ J",
			By(
				Normalized,
				subringS,
				idealI,
				nonzero,
				idealM,
				iInM,
				invertible,
				jDef,
				DivideByInvertibleIdeal.Read(L).At(S, I, m)))
		d := a.Conjuncts(
			divided,
			"J is an ideal",
			"m · J is I",
			"J lies above I")
		idealJ, product, iInJ := d[0], d[1], d[2]
		finite := a.Have(
			"S/J and S/m are finite, both ideals lying above I",
			"finite(left_cosets(L.add, S, J)) ∧ finite(left_cosets(L.add, S, m))",
			By(
				subringS,
				comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S),
				idealI,
				idealJ,
				idealM,
				iInJ,
				iInM,
				finiteI,
				quotient_ring.FiniteQuotientAboveIdeal.At(R, I, J),
				quotient_ring.FiniteQuotientAboveIdeal.At(R, I, m)))
		inL := a.Have(
			"J and m lie in S, and so in L",
			"J ⊆ L.carrier ∧ m ⊆ L.carrier",
			BySets(
				ring_ideal.IdealSubset.Read(idealJ),
				ring_ideal.IdealSubset.Read(idealM),
				comm_ring.SubringSubset.Read(subringS)))
		commuted := a.Have(
			"the product commutes, so J · m is I",
			"fractional_mul(field_ring(L), S, J, m) = I",
			By(Normalized, inL, product, fractional_ideal.FractionalMulComm.Read(L).At(S, J, m)))
		indices := a.Have(
			"the index of J · m is the index of J times the index of m",
			"ideal_index(«R», fractional_mul(field_ring(L), S, J, m)) = "+
				"ideal_index(«R», J) * ideal_index(«R», m)",
			By(
				subringS,
				idealJ,
				idealM,
				invertible,
				finite,
				ideal_colength.IdealIndexMultiplicative.Read(L).At(S, J, m)))
		a.Show(
			"J · m is I, and the two indices commute",
			By(indices, commuted, nat_arith.MulSym.At(indexJ, indexM)))
	}),
})}
