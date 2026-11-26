// division.go — division: pseudo-division over any commutative ring, by a
// monic polynomial over any commutative ring, which is pseudo-division at
// leading coefficient one, and by a nonzero polynomial over a field, which
// is monic division after scaling; divisibility: reflexive and transitive
// over any ring, Bézout's identity, the irreducible polynomials and an
// irreducible factor of each polynomial of positive degree over a field,
// and the coprime polynomials; and the divisibility the pseudo-remainder
// decides over a field.

package polynomial_division

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Pseudo-division over rings
// ---------------------------------------------------------------------------

// LeadingTermCancel — a monomial multiple of a polynomial cancels the
// highest coefficient of the dividend scaled by the polynomial's leading
// coefficient: the step of pseudo-division. Multiplication by the monomial
// shifts the divisor's coefficients, so at m the difference is
// g(k) f(m) − f(m) g(k) with k the degree of g, zero in a commutative ring,
// and past m both the dividend and the shifted divisor vanish.
var LeadingTermCancel = leadingTermCancelThm{family.Add(registry.ProofEntry{
	Name: "LeadingTermCancel",
	Key:  "prop_d8a15bf0c9cb6300",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:num. ∀f g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, f)",
			"polynomial_over(R.carrier, g)",
			"polynomial_degree(g) ≤ m",
			"vec⟨suc(m)⟩(f)",
		},
		Conclusion: "vec⟨m⟩(g(polynomial_degree(g)) • f - " +
			"    polynomial_mul(g, f(m) • basis_vector(m - polynomial_degree(g))))",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			m *Expr[Nat],
			f, g *Arrow[Nat, A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f has coefficients in the ring",
				"g has coefficients in the ring",
				"g's degree is at most m",
				"f vanishes past m")
			fOver, gOver, degreeBound, fPast := parts[0], parts[1], parts[2], parts[3]
			degree := a.Let("k", a.Term("polynomial_degree(g)"))
			k, shift := a.TermAs[Nat]("k"), a.TermAs[Nat]("m - k")
			coefficients := a.Have(
				"every coefficient of f and g lies in the ring",
				"∀i:num. f(i) ∈ R.carrier ∧ g(i) ∈ R.carrier",
				By(fOver, gOver, polynomial.PolynomialOverDef))
			gPast := a.Have(
				"g vanishes past its degree k",
				"vec⟨suc(k)⟩(g)",
				By(Normalized, degree, gOver, polynomial.DegreeVec))
			monomialCoefficients := a.Have(
				"x ^ (m - k) is a polynomial over the ring, so every coefficient of it lies in the ring",
				"∀i:num. basis_vector(m - k, i) ∈ R.carrier",
				By(polynomial.BasisVectorOver.Read(ring).At(shift), polynomial.PolynomialOverDef))
			scalarOut := a.Have(
				"the scalar passes out of multiplication by g",
				"polynomial_mul(g, f(m) • basis_vector(m - k)) = f(m) • polynomial_mul(g, basis_vector(m - k))",
				By(
					coefficients,
					monomialCoefficients,
					polynomial.PolynomialMulScalar.Read(ring).AsFact().At(
						f.Apply(m), g, a.TermAs[Fun[Nat, A]]("basis_vector(m - k)"))))
			a.Do(scalarOut.Rw(), Simp(
				Fwd(vec_space.VecDef),
				Fwd(vec_space.VecSubDef),
				Fwd(vec_space.VecScalarMulDef)))
			i := a.FixAs[Nat]("i")
			past := a.Assume()
			reached := a.Have(
				"the monomial's shift has been reached",
				"m - k ≤ i",
				ByArith(past))
			shifted := a.Have(
				"multiplication by the monomial shifts g's coefficient",
				"polynomial_mul(g, basis_vector(m - k), i) = g(i - (m - k))",
				By(reached, coefficients, polynomial.PolynomialMulBasisVector.Read(ring).At(g, shift, i)))
			a.Do(shifted.Rw())
			a.Cases(a.Term("i = m"))
			a.When(
				"at m the shifted coefficient is g's leading coefficient, and the two products commute",
				func(b *Argument, atM Fact) {
					back := b.Have(
						"the shift returns to index k",
						"i - (m - k) = k",
						ByArith(degreeBound, atM))
					b.Show(
						"g(k) f(m) − f(m) g(k) is zero",
						ByArith(ring, back, atM, coefficients.At(m), coefficients.At(k)))
				})
			a.Otherwise(
				"past m both the dividend and the shifted divisor vanish",
				func(b *Argument, beyond Fact) {
					vanish := b.Conjuncts(
						b.Have(
							"both coefficients are zero",
							"f(i) = R.zero ∧ g(i - (m - k)) = R.zero",
							ByArith(beyond, degreeBound, past, gPast, fPast, vec_space.VecDef)),
						"f vanishes at i",
						"g vanishes at i - (m - k)")
					b.Show(
						"g(k) times zero less f(m) times zero is zero",
						ByArith(
							ring,
							coefficients.At(m),
							coefficients.At(k),
							coefficients.At(i),
							Scaled(b.TermAs[A]("g(k)"), vanish[0]),
							vanish[1]))
				})
		}),
})}

// PseudoDivision — over a commutative ring, a power of the divisor's
// leading coefficient times the dividend is a multiple of the divisor plus
// a remainder vanishing from the divisor's degree on. With a the leading
// coefficient and d the degree of g, induction on a support bound n shows
// that a polynomial p vanishing from n on has a ^ (n − d) • p = g s + r
// with r vanishing from d on. Below d, p itself vanishes from d on, and so
// does any scalar multiple of it, which is then its own remainder. From d
// on, a • p − g h with h = p(n) x ^ (n − d) vanishes from n on
// (LeadingTermCancel); its division a ^ (n − d) • (a • p − g h) = g s + r
// gives a ^ (n + 1 − d) • p = g (s + a ^ (n − d) • h) + r, scaling by a
// constant being multiplying by the constant polynomial
// (polynomial.PolynomialMulConstant). f vanishes from deg f + 1 on.
var PseudoDivision = pseudoDivisionThm{family.Add(registry.ProofEntry{
	Name: "PseudoDivision",
	Key:  "prop_9254a8c2f141061d",
	Reading: "The exponent suc(deg f) − deg g is fixed by the two degrees, so a " +
		"parametric divisor gets one exponent in every specialization. When deg f < deg " +
		"g it is zero, and f itself is the remainder. The zero divisor is not excluded: " +
		"its leading coefficient is zero, so the scaled dividend and the remainder are " +
		"both zero. No coefficient inverse is used, so the ring may have zero divisors.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, f)",
			"polynomial_over(R.carrier, g)",
		},
		Conclusion: "∃s r:(num → A). " +
			"    «division»(R.carrier, " +
			"        monoid_pow(R.mul, " +
			"            R.one, " +
			"            g(polynomial_degree(g)), " +
			"            suc(polynomial_degree(f)) - polynomial_degree(g)) • " +
			"        f, " +
			"        g, " +
			"        s, " +
			"        r)",
	}, func(arg *Argument, ring comm_ring.CommRingFact[on.R], f, g *Arrow[Nat, A], over Fact) {
		parts := arg.Conjuncts(
			over,
			"f is over the ring",
			"g is over the ring")
		fOver, gOver := parts[0], parts[1]
		polynomialRing := polynomial.PolynomialRingOn.Read(ring)
		polynomialModule := polynomial.PolynomialModuleOn.Read(ring)
		powers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))
		zero, carrier := arg.TermAs[A]("R.zero"), arg.TermAs[Set[A]]("R.carrier")
		degree := arg.Let("d", arg.Term("polynomial_degree(g)"))
		lead := arg.Let("a", arg.Term("g(d)"))
		aIn := arg.Have(
			"g's leading coefficient a lies in the ring",
			"a ∈ R.carrier",
			lead.Rw(),
			By(gOver, polynomial.PolynomialOverDef.At(zero, carrier, g)))
		aMember := arg.MemberOf[on.R](arg.TermAs[A]("a"), aIn)
		ownRemainder := arg.Have(
			"a polynomial vanishing from d on, scaled by any power of a, is its own remainder",
			Statement{
				Binders: "∀k:num. ∀p:(num → A).",
				Hypotheses: []string{
					"polynomial_over(R.carrier, p)",
					"vec⟨d⟩(p)",
				},
				Conclusion: "∃s r:(num → A). " +
					"    polynomial_over(R.carrier, s) ∧ " +
					"    polynomial_over(R.carrier, r) ∧ " +
					"    vec⟨d⟩(r) ∧ " +
					"    monoid_pow(R.mul, R.one, a, k) • p = polynomial_mul(g, s) + r",
			},
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				b.FixAs[Fun[Nat, A]]("p")
				short := b.Assume()
				power := powers.At(aMember, k)
				members := b.Have(
					"g and the scaled p belong to the polynomial ring",
					"g ∈ «polynomialRingCarrier» ∧ monoid_pow(R.mul, R.one, a, k) • p ∈ «polynomialRingCarrier»",
					BySets(power, short, gOver, module.SmulIn.Read(polynomialModule)))
				equation := b.Have(
					"g times zero plus the scaled p is the scaled p",
					"monoid_pow(R.mul, R.one, a, k) • p = "+
						"polynomial_mul(g, vec_zero) + monoid_pow(R.mul, R.one, a, k) • p",
					ByArith(polynomialRing, members))
				b.Take(b.TermAs[Fun[Nat, A]]("vec_zero"))
				b.Take(b.TermAs[Fun[Nat, A]]("monoid_pow(R.mul, R.one, a, k) • p"))
				b.Show(
					"quotient zero and the scaled p as remainder, which vanishes from d on as p does",
					By(
						polynomial.VecZeroOver.Read(ring),
						members,
						equation,
						power,
						short,
						vec_space.VecSmulOn.Read(ring)))
			}))
		division := arg.Have(
			"a polynomial vanishing from n on divides by g at the power n − d of a",
			Statement{
				Binders: "∀n:num. ∀p:(num → A).",
				Hypotheses: []string{
					"polynomial_over(R.carrier, p)",
					"vec⟨n⟩(p)",
				},
				Conclusion: "∃s r:(num → A). " +
					"    polynomial_over(R.carrier, s) ∧ " +
					"    polynomial_over(R.carrier, r) ∧ " +
					"    vec⟨d⟩(r) ∧ " +
					"    monoid_pow(R.mul, R.one, a, n - d) • p = polynomial_mul(g, s) + r",
			},
			Derive(func(b *Argument) {
				b.Induct("n")
				b.Base(
					"a polynomial vanishing from zero on vanishes from d on",
					func(base *Argument) {
						p := base.FixAs[Fun[Nat, A]]("p")
						given := base.Assume()
						short := base.Have(
							"p vanishes from d on",
							"vec⟨d⟩(p)",
							ByArith(given, vec_space.VecDef))
						base.Show(
							"so it is its own remainder",
							By(ownRemainder.At(base.TermAs[Nat]("0 - d"), p), given, short))
					})
				b.Step(
					"from d on one cancellation of the coefficient at n costs one factor of a",
					func(step *Argument, ih Fact) {
						p := step.FixAs[Fun[Nat, A]]("p")
						given := step.Assume()
						n := step.TermAs[Nat]("n")
						notBelow := step.Unless(
							step.Term("n < d"),
							"below d the dividend vanishes from d on and is its own remainder",
							Given(func(e *Argument, below Fact) {
								short := e.Have(
									"p vanishes from d on",
									"vec⟨d⟩(p)",
									ByArith(below, given, vec_space.VecDef))
								e.Show(
									"so it is its own remainder",
									By(ownRemainder.At(e.TermAs[Nat]("suc(n) - d"), p), given, short))
							}))
						monomial := step.Let("h", step.Term("p(n) • basis_vector(n - d)"))
						hOver := step.Have(
							"the scalar monomial h is a polynomial over the ring, p's coefficient at n belonging to it",
							"polynomial_over(R.carrier, h)",
							monomial.Rw(),
							BySets(
								given,
								polynomial.PolynomialOverDef,
								polynomial.BasisVectorOver.Read(ring),
								module.SmulIn.Read(polynomialModule)))
						cancels := step.Have(
							"a • p − g h vanishes from n on",
							"vec⟨n⟩(a • p - polynomial_mul(g, h))",
							By(
								Normalized,
								notBelow,
								monomial,
								lead,
								degree,
								given,
								gOver,
								nat_order.NotLessThan,
								LeadingTermCancel.Read(ring).At(n, p, g)))
						restOver := step.Have(
							"a • p − g h is a polynomial over the ring",
							"polynomial_over(R.carrier, a • p - polynomial_mul(g, h))",
							BySets(
								aIn,
								given,
								gOver,
								hOver,
								comm_ring.SubIn.Read(polynomialRing),
								comm_ring.MulIn.Read(polynomialRing),
								module.SmulIn.Read(polynomialModule)))
						reduced := step.TermAs[Fun[Nat, A]]("a • p - polynomial_mul(g, h)")
						_, r, divided := step.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
							"divide a • p − g h at the bound n",
							"∃s r:(num → A). "+
								"    polynomial_over(R.carrier, s) ∧ "+
								"    polynomial_over(R.carrier, r) ∧ "+
								"    vec⟨d⟩(r) ∧ "+
								"    monoid_pow(R.mul, R.one, a, n - d) • (a • p - polynomial_mul(g, h)) = "+
								"    polynomial_mul(g, s) + r",
							By(ih.At(reduced), restOver, cancels))
						scale, scaleDef := step.LetAs[A]("c", "monoid_pow(R.mul, R.one, a, n - d)")
						cIn := step.Have(
							"the power c of a lies in the ring",
							"c ∈ R.carrier",
							By(Normalized, scaleDef, powers.At(aMember, step.TermAs[Nat]("n - d"))))
						cMember := step.MemberOf[on.R](scale, cIn)
						exponent := step.Have(
							"the exponent grows by one",
							"suc(n) - d = suc(n - d)",
							ByArith(notBelow))
						power := step.Have(
							"one more factor of a",
							"monoid_pow(R.mul, R.one, a, suc(n) - d) = c * a",
							exponent.Rw(),
							Simp(Fwd(comm_monoid.MonoidPowDef)),
							scaleDef.RwRev(),
							ByArith(ring, aIn, cIn))
						members := step.Have(
							"the polynomials of the step belong to the polynomial ring",
							"p ∈ «polynomialRingCarrier» ∧ "+
								"g ∈ «polynomialRingCarrier» ∧ "+
								"h ∈ «polynomialRingCarrier» ∧ "+
								"s ∈ «polynomialRingCarrier» ∧ "+
								"r ∈ «polynomialRingCarrier» ∧ "+
								"a • p ∈ «polynomialRingCarrier» ∧ "+
								"c • basis_vector(0) ∈ «polynomialRingCarrier» ∧ "+
								"c • h ∈ «polynomialRingCarrier» ∧ "+
								"c • (a • p) ∈ «polynomialRingCarrier» ∧ "+
								"c • (a • p - polynomial_mul(g, h)) ∈ «polynomialRingCarrier»",
							BySets(
								aIn,
								cIn,
								divided,
								given,
								gOver,
								hOver,
								restOver,
								polynomial.BasisVectorOver.Read(ring),
								module.SmulIn.Read(polynomialModule)))
						scaled := step.Have(
							"a ^ (n + 1 − d) • p is c • (a • p)",
							"monoid_pow(R.mul, R.one, a, suc(n) - d) • p = c • (a • p)",
							By(
								power,
								aIn,
								cIn,
								members,
								module.SmulMul.Read(polynomialModule).AsFact().At(scale, step.TermAs[A]("a"), p)))
						constant := polynomial.PolynomialMulConstant.Read(ring)
						equation := step.Have(
							"scaling by c is multiplying by the constant c, so c • (a • p) = g (s + c • h) + r",
							"c • (a • p) = polynomial_mul(g, s + c • h) + r",
							ByArith(
								polynomialRing,
								members,
								divided,
								hOver,
								restOver,
								constant.At(cMember, step.TermAs[Fun[Nat, A]]("a • p")),
								constant.At(cMember, reduced),
								Scaled(g, constant.At(cMember, step.TermAs[Fun[Nat, A]]("h")))))
						quotientOver := step.Have(
							"s + c • h is a polynomial over the ring",
							"polynomial_over(R.carrier, s + c • h)",
							BySets(comm_ring.AddIn.Read(polynomialRing), members))
						step.Take(step.TermAs[Fun[Nat, A]]("s + c • h"))
						step.Take(r)
						step.Show(
							"the enlarged quotient and the same remainder divide a ^ (n + 1 − d) • p",
							By(quotientOver, divided, scaled, equation))
					})
			}))
		arg.Show(
			"f vanishes past its degree, so it divides at the power suc(deg f) − d",
			By(
				division.At(arg.TermAs[Nat]("suc(polynomial_degree(f))"), f),
				fOver,
				polynomial.DegreeVec.At(zero, carrier, f)))
	}),
})}

// ---------------------------------------------------------------------------
// Monic division over rings
// ---------------------------------------------------------------------------

// MonicLeadingTermCancel — a monomial multiple of a monic polynomial
// cancels the highest coefficient of a dividend: LeadingTermCancel at a
// divisor whose leading coefficient is one, which scales the dividend to
// itself.
var MonicLeadingTermCancel = monicLeadingTermCancelThm{family.Add(registry.ProofEntry{
	Name: "MonicLeadingTermCancel",
	Key:  "prop_dbb84b0cc88bd892",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:num. ∀f g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, f)",
			"polynomial_over(R.carrier, g)",
			"polynomial_monic(g)",
			"polynomial_degree(g) ≤ m",
			"vec⟨suc(m)⟩(f)",
		},
		Conclusion: "vec⟨m⟩(f - polynomial_mul(g, f(m) • basis_vector(m - polynomial_degree(g))))",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			m *Expr[Nat],
			f, g *Arrow[Nat, A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f has coefficients in the ring",
				"g has coefficients in the ring",
				"g is monic",
				"g's degree is at most m",
				"f vanishes past m")
			cancels := a.Have(
				"the monomial multiple of g cancels f scaled by g's leading coefficient from m on",
				"vec⟨m⟩(g(polynomial_degree(g)) • f - "+
					"    polynomial_mul(g, f(m) • basis_vector(m - polynomial_degree(g))))",
				By(parts[0], parts[1], parts[3], parts[4], LeadingTermCancel.Read(ring).At(m, f, g)))
			unscaled := a.Have(
				"g is monic, so its leading coefficient is one, which scales f to itself",
				"g(polynomial_degree(g)) • f = f",
				By(
					parts[0],
					parts[2],
					polynomial.PolynomialMonicDef,
					module.SmulOne.Read(polynomial.PolynomialModuleOn.Read(ring)).AsFact().At(f)))
			a.Show(
				"so the multiple cancels f itself from m on",
				By(cancels, unscaled))
		}),
})}

// MonicDivisionExists — division by a monic polynomial leaves a remainder
// vanishing from its degree on: PseudoDivision at a divisor whose leading
// coefficient is one, every power of which scales the dividend to itself.
var MonicDivisionExists = monicDivisionExistsThm{family.Add(registry.ProofEntry{
	Name: "MonicDivisionExists",
	Key:  "prop_e20f1db91d81bda1",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, f)",
			"polynomial_over(R.carrier, g)",
			"polynomial_monic(g)",
		},
		Conclusion: "∃q r:(num → A). «division»(R.carrier, f, g, q, r)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], f, g *Arrow[Nat, A], over Fact) {
			parts := a.Conjuncts(
				over,
				"f has coefficients in the ring",
				"g has coefficients in the ring",
				"g is monic")
			fOver, gOver, monic := parts[0], parts[1], parts[2]
			s, r, divided := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				GroupPremises(fOver, gOver, PseudoDivision.Read(ring).At(f, g)),
				"s",
				"r")
			lead := a.Have(
				"g is monic: its leading coefficient is one",
				"g(polynomial_degree(g)) = R.one",
				By(monic, polynomial.PolynomialMonicDef))
			unscaled := a.Have(
				"so the power of the leading coefficient is one, which scales f to itself",
				"monoid_pow(R.mul, "+
					"    R.one, "+
					"    g(polynomial_degree(g)), "+
					"    suc(polynomial_degree(f)) - polynomial_degree(g)) • "+
					"f = "+
					"f",
				lead.Rw(),
				By(
					fOver,
					comm_monoid.IdentityPowOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(
						a.TermAs[Nat]("suc(polynomial_degree(f)) - polynomial_degree(g)")),
					module.SmulOne.Read(polynomial.PolynomialModuleOn.Read(ring)).AsFact().At(f)))
			a.Take(s)
			a.Take(r)
			a.Show(
				"so f is g s + r, s and r dividing f by g",
				By(Normalized, divided, unscaled))
		}),
})}

// MonicDivisionUnique — two decompositions by a monic divisor, with
// remainders vanishing from its degree on, have the same quotient and
// remainder. The product of the divisor with the quotient difference is the
// difference of the remainders, so it vanishes from the divisor's degree
// on; but were the quotient difference nonzero, its leading coefficient
// would be the product's coefficient at the sum of the two degrees.
var MonicDivisionUnique = monicDivisionUniqueThm{family.Add(registry.ProofEntry{
	Name: "MonicDivisionUnique",
	Key:  "prop_36b539182d4631cb",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀g q r q₂ r₂:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, g)",
			"polynomial_monic(g)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, q₂)",
			"polynomial_over(R.carrier, r)",
			"polynomial_over(R.carrier, r₂)",
			"vec⟨polynomial_degree(g)⟩(r)",
			"vec⟨polynomial_degree(g)⟩(r₂)",
			"polynomial_mul(g, q) + r = polynomial_mul(g, q₂) + r₂",
		},
		Conclusion: "q = q₂ ∧ r = r₂",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], g, q, r, q2, r2 *Arrow[Nat, A], given Fact) {
			polynomialRing := polynomial.PolynomialRingOn.Read(ring)
			zero, carrier := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			parts := a.Conjuncts(
				given,
				"g is a polynomial over the ring",
				"g is monic",
				"q is over the ring",
				"q₂ is over the ring",
				"r is over the ring",
				"r₂ is over the ring",
				"r vanishes from g's degree on",
				"so does r₂",
				"the decompositions agree")
			gOver, monic, shortR, shortR2, equation := parts[0], parts[1], parts[6], parts[7], parts[8]
			members := a.Have(
				"the divisor, quotients and remainders belong to the polynomial ring",
				"g ∈ «polynomialRingCarrier» ∧ "+
					"q ∈ «polynomialRingCarrier» ∧ "+
					"q₂ ∈ «polynomialRingCarrier» ∧ "+
					"r ∈ «polynomialRingCarrier» ∧ "+
					"r₂ ∈ «polynomialRingCarrier»",
				BySets(given))
			productDifference := a.Have(
				"the product of the quotient difference is the remainder difference",
				"polynomial_mul(g, q - q₂) = r₂ - r",
				ByArith(polynomialRing, equation, members))
			differenceOver := a.Have(
				"the quotient difference is a polynomial over the ring",
				"polynomial_over(R.carrier, q - q₂)",
				BySets(comm_ring.SubIn.Read(polynomialRing), members))
			v, differenceDefinition := a.LetAs[Fun[Nat, A]]("v", "q - q₂")
			productShort := a.Have(
				"so does the product, the difference of the remainders",
				"vec⟨polynomial_degree(g)⟩(polynomial_mul(g, v))",
				Derive(func(b *Argument) {
					b.Do(productDifference.Rw(), Simp(Fwd(vec_space.VecDef)), Simp(Fwd(vec_space.VecSubDef)))
					b.FixAs[Nat]("i")
					past := b.Assume()
					vanish := b.Have(
						"both remainder coefficients vanish here",
						"r₂(i) = R.zero ∧ r(i) = R.zero",
						By(past, shortR, shortR2, vec_space.VecDef))
					zeros := b.Conjuncts(
						vanish,
						"r₂ vanishes here",
						"r vanishes here")
					b.Show(
						"their difference is zero",
						zeros[1].Rw(),
						zeros[0].Rw(),
						ByArith(ring))
				}))
			vZero := a.Have(
				"the quotient difference must be zero",
				"v = vec_zero",
				Derive(func(b *Argument) {
					nonzero := b.SupposeNot()
					leading := b.Have(
						"v, a nonzero polynomial over the ring, has its leading coefficient in the ring and nonzero",
						"v(polynomial_degree(v)) ∈ R.carrier ∧ v(polynomial_degree(v)) ≠ R.zero",
						By(differenceOver, nonzero, polynomial.LeadingCoefficientNonzero.At(zero, carrier, v)))
					monicLeading := b.Have(
						"g's leading coefficient is one",
						"g(polynomial_degree(g)) = R.one",
						By(monic, polynomial.PolynomialMonicDef))
					productLeading := b.Have(
						"the coefficient at the sum of the degrees is the product of the leading coefficients",
						"polynomial_mul(g, v, polynomial_degree(g) + polynomial_degree(v)) = "+
							"g(polynomial_degree(g)) * v(polynomial_degree(v))",
						By(gOver, differenceOver, polynomial.LeadingCoefficientMul.Read(ring).At(g, v)))
					productIsLeading := b.Have(
						"monicity makes that coefficient v's leading coefficient",
						"polynomial_mul(g, v, polynomial_degree(g) + polynomial_degree(v)) = v(polynomial_degree(v))",
						productLeading.Rw(),
						monicLeading.Rw(),
						ByArith(ring, leading))
					productZero := b.Have(
						"the product vanishing from g's degree on, that coefficient is zero",
						"polynomial_mul(g, v, polynomial_degree(g) + polynomial_degree(v)) = R.zero",
						ByArith(productShort, vec_space.VecDef))
					b.Show(
						"this contradicts v's nonzero leading coefficient",
						By(leading, productIsLeading, productZero))
				}))
			zeroDifference := a.Have(
				"the quotient difference vanishes",
				"q - q₂ = vec_zero",
				differenceDefinition.RwRev(),
				By(vZero))
			quotientsEqual := a.Have(
				"the quotients are equal",
				"q = q₂",
				ByArith(polynomialRing, zeroDifference, members))
			remaindersEqual := a.Have(
				"equal quotients leave equal remainders",
				"r = r₂",
				ByArith(polynomialRing, members, equation, Scaled(g, quotientsEqual)))
			a.Show(
				"both parts of the decomposition are unique",
				By(quotientsEqual, remaindersEqual))
		}),
})}

// MonicDivisionAlgorithm — a monic divisor over a commutative ring has a
// unique quotient and a unique remainder vanishing from its degree on. The
// division is MonicDivisionExists; any other such decomposition has the
// same quotient and remainder (MonicDivisionUnique).
var MonicDivisionAlgorithm = monicDivisionAlgorithmThm{family.Add(registry.ProofEntry{
	Name: "MonicDivisionAlgorithm",
	Key:  "prop_adf3e19af757498a",
	Reading: "Only the divisor is monic. No coefficient inverse is used, so the coefficient ring " +
		"may have zero divisors; neither a nonzero ring nor a positive divisor degree is assumed.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, f)",
			"polynomial_over(R.carrier, g)",
			"polynomial_monic(g)",
		},
		Conclusion: "∃q r:(num → A). " +
			"    «division»(R.carrier, f, g, q, r) ∧ " +
			"    (∀q₂ r₂:(num → A). «division»(R.carrier, f, g, q₂, r₂) ⇒ q₂ = q ∧ r₂ = r)",
	}, func(a *Argument, ring comm_ring.CommRingFact[on.R], f, g *Arrow[Nat, A], given Fact) {
		q, r, divided := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
			GroupPremises(given, MonicDivisionExists.Read(ring).At(f, g)),
			"q",
			"r")
		unique := a.Have(
			"every decomposition with a remainder vanishing from g's degree on has this quotient and remainder",
			"∀q₂ r₂:(num → A). «division»(R.carrier, f, g, q₂, r₂) ⇒ q₂ = q ∧ r₂ = r",
			Derive(func(b *Argument) {
				q2, r2 := b.FixAs[Fun[Nat, A]]("q₂"), b.FixAs[Fun[Nat, A]]("r₂")
				alternative := b.Assume()
				b.Show(
					"monic division has only one such decomposition",
					By(Normalized, given, divided, alternative, MonicDivisionUnique.Read(ring).At(g, q2, r2, q, r)))
			}))
		a.Take(q)
		a.Take(r)
		a.Show(
			"the quotient and remainder satisfy existence and uniqueness",
			By(unique, divided))
	}),
})}

// ---------------------------------------------------------------------------
// Division over a field
// ---------------------------------------------------------------------------

// MonicAssociate — over a field a nonzero polynomial is a unit times a monic
// polynomial of its degree: its leading coefficient is a nonzero member of c,
// so is the inverse a of that coefficient, and a • g is monic of g's degree
// (polynomial.MonicMultiple).
var MonicAssociate = monicAssociateThm{family.Add(registry.ProofEntry{
	Name: "MonicAssociate",
	Key:  "prop_960ed8f0864c8a70",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, g)",
			"g ≠ vec_zero",
		},
		Conclusion: "∃a:A. " +
			"    a ∈ F.carrier ∧ " +
			"    a ≠ F.zero ∧ " +
			"    polynomial_over(F.carrier, a • g) ∧ " +
			"    polynomial_monic(a • g) ∧ " +
			"    polynomial_degree(a • g) = polynomial_degree(g)",
	},
		func(arg *Argument, fieldOn field.FieldFact[on.F], g *Arrow[Nat, A], hypotheses Fact) {
			zero, c := arg.TermAs[A]("F.zero"), arg.TermAs[Set[A]]("F.carrier")
			leading := arg.Conjuncts(
				GroupPremises(hypotheses, polynomial.LeadingCoefficientNonzero.At(zero, c, g)),
				"g's leading coefficient lies in c",
				"and is not zero")
			lead := arg.MemberOf[on.F](arg.TermAs[A]("g(polynomial_degree(g))"), leading[0])
			arg.Take(arg.TermAs[A]("F.inv(g(polynomial_degree(g)))"))
			arg.Show(
				"its inverse a is a nonzero member of c, and a • g is monic of g's degree",
				By(
					hypotheses,
					leading[1],
					field.InvIn.Read(fieldOn).At(lead),
					field.InvEqZeroOn.Read(fieldOn).At(lead),
					polynomial.MonicMultiple.Read(fieldOn).At(g)))
		}),
})}

// DivisionExists — over a field, a polynomial divides by a nonzero
// one with a remainder vanishing from the divisor's degree on. A nonzero
// scalar a scales g to a monic polynomial of its degree (MonicAssociate),
// and dividing f by the monic a • g (MonicDivisionExists) leaves
// f = (a • g) q + u with u vanishing from g's degree on. Scaling by a is
// multiplying by the constant polynomial a (polynomial.PolynomialMulConstant),
// so f = g (a • q) + u.
var DivisionExists = divisionExistsThm{family.Add(registry.ProofEntry{
	Name: "DivisionExists",
	Key:  "prop_a9d2410d0aa6f77d",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀f g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, f)",
			"polynomial_over(F.carrier, g)",
			"g ≠ vec_zero",
		},
		Conclusion: "∃q r:(num → A). «division»(F.carrier, f, g, q, r)",
	},
		func(arg *Argument, fieldOn field.FieldFact[on.F], f, g *Arrow[Nat, A], hypotheses Fact) {
			ring := field.RingOn.Read(fieldOn)
			smulIn := module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))
			parts := arg.Conjuncts(
				hypotheses,
				"f is a polynomial over c",
				"so is g",
				"g is not zero")
			fOver, gOver, gNonzero := parts[0], parts[1], parts[2]
			a, associate := arg.UnpackAs[A](
				GroupPremises(gOver, gNonzero, MonicAssociate.Read(fieldOn).At(g)), "a")
			scaled := arg.Conjuncts(
				associate,
				"a lies in c",
				"a is not zero",
				"a • g is a polynomial over c",
				"monic",
				"of g's degree")
			aIn, scaledOver, monic, sameDegree := scaled[0], scaled[2], scaled[3], scaled[4]
			aMember, monicMultiple := arg.MemberOf[on.F](a, aIn), arg.TermAs[Fun[Nat, A]]("a • g")
			q, u, division := arg.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
				"dividing f by the monic a • g leaves a quotient q and a remainder u vanishing from g's degree on",
				"∃q u:(num → A). "+
					"    polynomial_over(F.carrier, q) ∧ "+
					"    polynomial_over(F.carrier, u) ∧ "+
					"    vec⟨polynomial_degree(g)⟩(u) ∧ "+
					"    f = polynomial_mul(a • g, q) + u",
				By(fOver, scaledOver, monic, sameDegree, MonicDivisionExists.Read(ring).At(f, monicMultiple)))
			divided := arg.Conjuncts(
				division,
				"q is a polynomial over c",
				"so is u",
				"u vanishes from g's degree on",
				"f = (a • g) q + u")
			qOver, uOver, uShort, fDivided := divided[0], divided[1], divided[2], divided[3]
			members := arg.Have(
				"f, g, q, u, a • g, a • q and the constant polynomial a lie in the ring of polynomials over c",
				"f ∈ «fieldPolynomials» ∧ "+
					"g ∈ «fieldPolynomials» ∧ "+
					"q ∈ «fieldPolynomials» ∧ "+
					"u ∈ «fieldPolynomials» ∧ "+
					"a • g ∈ «fieldPolynomials» ∧ "+
					"a • q ∈ «fieldPolynomials» ∧ "+
					"a • basis_vector(0) ∈ «fieldPolynomials»",
				BySets(fOver, gOver, qOver, uOver, aIn, polynomial.BasisVectorOver.Read(ring), smulIn))
			gScaled := arg.Have(
				"g times the constant polynomial a is a • g",
				"polynomial_mul(g, a • basis_vector(0)) = a • g",
				By(gOver, polynomial.PolynomialMulConstant.Read(ring).At(aMember, g)))
			qScaled := arg.Have(
				"and q times it is a • q",
				"polynomial_mul(q, a • basis_vector(0)) = a • q",
				By(qOver, polynomial.PolynomialMulConstant.Read(ring).At(aMember, q)))
			equation := arg.Have(
				"so (a • g) q = g (a • q), and f = g (a • q) + u",
				"f = polynomial_mul(g, a • q) + u",
				ByArith(
					polynomial.PolynomialRingOn.Read(ring),
					members,
					fDivided,
					Scaled(g, qScaled),
					Scaled(q, gScaled)))
			arg.Take(arg.TermAs[Fun[Nat, A]]("a • q"))
			arg.Take(u)
			arg.Show(
				"so the quotient a • q and the remainder u divide f by g",
				By(members, uOver, uShort, equation))
		}),
})}

// DivisionUnique — over a field the quotient and the remainder are
// unique. Scaled by a nonzero a that makes a • g monic of g's degree
// (MonicAssociate), the two decompositions g q + r = g q₂ + r₂ become
// (a • g) q + a • r = (a • g) q₂ + a • r₂ by the monic a • g, whose
// remainders a • r and a • r₂ vanish from that degree on as r and r₂ do.
// Monic division has only one such decomposition (MonicDivisionUnique), so
// q = q₂, and then r = r₂.
var DivisionUnique = divisionUniqueThm{family.Add(registry.ProofEntry{
	Name: "DivisionUnique",
	Key:  "prop_640c6b4abf0da25c",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀f g q r q₂ r₂:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, g)",
			"polynomial_over(F.carrier, q)",
			"polynomial_over(F.carrier, r)",
			"polynomial_over(F.carrier, q₂)",
			"polynomial_over(F.carrier, r₂)",
			"g ≠ vec_zero",
			"f = polynomial_mul(g, q) + r",
			"f = polynomial_mul(g, q₂) + r₂",
			"vec⟨polynomial_degree(g)⟩(r)",
			"vec⟨polynomial_degree(g)⟩(r₂)",
		},
		Conclusion: "q = q₂ ∧ r = r₂",
	},
		func(
			arg *Argument,
			fieldOn field.FieldFact[on.F],
			f, g, q, r, q2, r2 *Arrow[Nat, A],
			hypotheses Fact,
		) {
			ring := field.RingOn.Read(fieldOn)
			polynomialRing := polynomial.PolynomialRingOn.Read(ring)
			parts := arg.Conjuncts(
				hypotheses,
				"g is a polynomial over c",
				"so is q",
				"and r",
				"and q₂",
				"and r₂",
				"g is not zero",
				"f = g q + r",
				"f = g q₂ + r₂",
				"r vanishes from g's degree on",
				"so does r₂")
			gOver, qOver, rOver, q2Over, r2Over, gNonzero :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			divided, divided2, rShort, r2Short := parts[6], parts[7], parts[8], parts[9]
			sameDivision := arg.Have(
				"so g q + r = g q₂ + r₂, both being f",
				"polynomial_mul(g, q) + r = polynomial_mul(g, q₂) + r₂",
				By(Normalized, divided, divided2))

			a, associate := arg.UnpackAs[A](
				GroupPremises(gOver, gNonzero, MonicAssociate.Read(fieldOn).At(g)), "a")
			scaled := arg.Conjuncts(
				associate,
				"a lies in c",
				"a is not zero",
				"a • g is a polynomial over c",
				"monic",
				"of g's degree")
			aIn, scaledOver, monic, sameDegree := scaled[0], scaled[2], scaled[3], scaled[4]
			aMember, monicMultiple := arg.MemberOf[on.F](a, aIn), arg.TermAs[Fun[Nat, A]]("a • g")
			scaledShort := arg.Have(
				"a • r and a • r₂ vanish from the degree of a • g on, as r and r₂ vanish from g's",
				"vec⟨polynomial_degree(a • g)⟩(a • r) ∧ vec⟨polynomial_degree(a • g)⟩(a • r₂)",
				By(
					sameDegree,
					vec_space.VecSmulOn.Read(ring).At(aMember, proof.InhabitFrom(r, rShort)),
					vec_space.VecSmulOn.Read(ring).At(aMember, proof.InhabitFrom(r2, r2Short))))

			constant := arg.TermAs[Fun[Nat, A]]("a • basis_vector(0)")
			members := arg.Have(
				"g, q, q₂, r, r₂, their multiples a • g, a • r, a • r₂ and the "+
					"constant polynomial a lie in the ring of polynomials over c",
				"g ∈ «fieldPolynomials» ∧ "+
					"q ∈ «fieldPolynomials» ∧ "+
					"q₂ ∈ «fieldPolynomials» ∧ "+
					"r ∈ «fieldPolynomials» ∧ "+
					"r₂ ∈ «fieldPolynomials» ∧ "+
					"a • g ∈ «fieldPolynomials» ∧ "+
					"a • r ∈ «fieldPolynomials» ∧ "+
					"a • r₂ ∈ «fieldPolynomials» ∧ "+
					"a • basis_vector(0) ∈ «fieldPolynomials»",
				BySets(
					gOver,
					qOver,
					q2Over,
					rOver,
					r2Over,
					aIn,
					polynomial.BasisVectorOver.Read(ring),
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))))
			gScaled := arg.Have(
				"g times the constant polynomial a is a • g",
				"polynomial_mul(g, a • basis_vector(0)) = a • g",
				By(gOver, polynomial.PolynomialMulConstant.Read(ring).At(aMember, g)))
			monicDivision := arg.Have(
				"multiplied by the constant a, which scales r and r₂ "+
					"too, the two decompositions are decompositions by a • g",
				"polynomial_mul(a • g, q) + a • r = polynomial_mul(a • g, q₂) + a • r₂",
				ByArith(
					polynomialRing,
					members,
					Scaled(constant, sameDivision),
					Scaled(q, gScaled),
					Scaled(q2, gScaled),
					rOver,
					r2Over,
					polynomial.PolynomialMulConstant.Read(ring).At(aMember, r),
					polynomial.PolynomialMulConstant.Read(ring).At(aMember, r2)))
			quotientsEqual := arg.Have(
				"monic division has only one decomposition with remainders "+
					"vanishing from the divisor's degree on, so q = q₂",
				"q = q₂",
				By(
					scaledOver,
					monic,
					members,
					scaledShort,
					monicDivision,
					MonicDivisionUnique.Read(ring).At(
						monicMultiple, q, arg.TermAs[Fun[Nat, A]]("a • r"), q2, arg.TermAs[Fun[Nat, A]]("a • r₂"))))
			remaindersEqual := arg.Have(
				"equal quotients leave equal remainders",
				"r = r₂",
				ByArith(polynomialRing, members, sameDivision, Scaled(g, quotientsEqual)))
			arg.Show(
				"both the quotient and the remainder are unique",
				By(quotientsEqual, remaindersEqual))
		}),
})}

// ---------------------------------------------------------------------------
// Divisibility over any ring
// ---------------------------------------------------------------------------

// DividesTrans — divisibility is transitive: with q = p s and r = q t
// for s and t over c, r = (p s) t = p (s t), the product of polynomials
// over c being associative, and s t is a polynomial over c.
var DividesTrans = dividesTransThm{family.Add(registry.ProofEntry{
	Name: "DividesTrans",
	Key:  "prop_5884fcb8813ef2cc",
	Reading: "polynomial_over(R.carrier, p) is load-bearing: " +
		"the convolution associates only for coefficients in c.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q r:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_divides(R, p, q)",
			"polynomial_divides(R, q, r)",
		},
		Conclusion: "polynomial_divides(R, p, r)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"p divides q",
				"q divides r")
			pOver, pDividesQ, qDividesR := given[0], given[1], given[2]
			s, sFactor := a.UnpackAs[Fun[Nat, A]](a.Unfolded(pDividesQ, PolynomialDividesDef), "s")
			t, tFactor := a.UnpackAs[Fun[Nat, A]](a.Unfolded(qDividesR, PolynomialDividesDef), "t")
			sParts := a.Conjuncts(
				sFactor,
				"s is a polynomial over c",
				"q is p times s")
			tParts := a.Conjuncts(
				tFactor,
				"t is a polynomial over c",
				"r is q times t")
			sOver, qIsPs, tOver, rIsQt := sParts[0], sParts[1], tParts[0], tParts[1]
			quotientOver := a.Have(
				"s t is a polynomial over c, a product of two",
				"polynomial_over(R.carrier, polynomial_mul(s, t))",
				By(sOver, tOver, polynomial.PolynomialMulOver.Read(ring).At(s, t)))
			regroup := a.Have(
				"r = q t = (p s) t = p(s t), the product of polynomials over R.carrier associating",
				"r = polynomial_mul(p, polynomial_mul(s, t))",
				rIsQt.Rw(),
				qIsPs.Rw(),
				By(
					pOver,
					sOver,
					tOver,
					polynomial.PolynomialOverDef,
					polynomial.PolynomialMulAssoc.Read(ring).At(p, s, t)))
			a.Show(
				"so p divides r, with the quotient s t",
				Unfold(PolynomialDividesDef),
				Witness(a.TermAs[Fun[Nat, A]]("polynomial_mul(s, t)")),
				By(quotientOver, regroup))
		}),
})}

// DividesRefl — a polynomial over c divides itself: the quotient is the
// one polynomial basis_vector(0), a polynomial over c and the identity of
// the product.
var DividesRefl = dividesReflThm{family.Add(registry.ProofEntry{
	Name: "DividesRefl",
	Key:  "prop_d0ed2a9f37cecdbf",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_divides(R, p, p)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], over Fact) {
			one := a.TermAs[Fun[Nat, A]]("basis_vector(0)")
			oneOver := polynomial.BasisVectorOver.Read(ring).At(a.TermAs[Nat]("0"))
			coefficients := a.Have(
				"every coefficient of p and of the one polynomial lies in c",
				"∀i:num. p(i) ∈ R.carrier ∧ basis_vector(0, i) ∈ R.carrier",
				By(over, oneOver, polynomial.PolynomialOverDef))
			a.Show(
				"the quotient is the one polynomial, over c, and multiplying by it fixes p",
				Unfold(PolynomialDividesDef),
				Witness(one),
				By(
					oneOver,
					coefficients,
					polynomial.PolynomialOneMul.Read(ring).At(p),
					polynomial.PolynomialMulComm.Read(ring).At(p, one)))
		}),
})}

// DividesMono — a divisor over a subset of the ring's carrier is a divisor
// over the ring: the restriction keeps R's operations, so the quotient over
// K is a quotient over R, its coefficients in the larger carrier
// (polynomial.PolynomialOverMono).
var DividesMono = dividesMonoThm{family.Add(registry.ProofEntry{
	Name: "DividesMono",
	Key:  "prop_87812a03347f945",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀K:set(A). ∀q p:(num → A).",
		Hypotheses: []string{
			"K ⊆ R.carrier",
			"polynomial_divides(restrict_ring(R, K), q, p)",
		},
		Conclusion: "polynomial_divides(R, q, p)",
	},
		func(a *Argument, _ *Expr[RingOps[A]], K *Expr[Set[A]], q, p *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"K lies in the ring's carrier",
				"q divides p over K")
			w, quotient := a.UnpackAs[Fun[Nat, A]](a.Unfolded(given[1], PolynomialDividesDef), "w")
			zero, carrier := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			a.Show(
				"the same quotient, over the larger carrier, witnesses divisibility over R",
				Simp(Fwd(PolynomialDividesDef)),
				Witness(w),
				By(given[0], quotient, polynomial.PolynomialOverMono.At(zero, K, carrier, w)))
		}),
})}

// ---------------------------------------------------------------------------
// Divisibility over a field
// ---------------------------------------------------------------------------

// DividesDegree — over a field a divisor of a nonzero polynomial has at
// most its degree: both factors in the divisibility equation are nonzero,
// so their degrees add to the dividend's degree.
var DividesDegree = dividesDegreeThm{family.Add(registry.ProofEntry{
	Name:    "DividesDegree",
	Key:     "prop_20056d2b15aa821",
	Reading: "q ≠ vec_zero is load-bearing: every polynomial divides vec_zero.",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"q ≠ vec_zero",
			"polynomial_divides(field_ring(F), p, q)",
		},
		Conclusion: "polynomial_degree(p) ≤ polynomial_degree(q)",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p, q *Arrow[Nat, A], hypotheses Fact) {
			polynomialRing := polynomial.PolynomialRingOn.Read(field.RingOn.Read(fieldOn))
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over the field",
				"q is nonzero",
				"p divides q")
			pOver, qNonzero, divides := parts[0], parts[1], parts[2]
			r, divided := a.UnpackAs[Fun[Nat, A]](a.Unfolded(divides, PolynomialDividesDef), "r")
			pNonzero := a.Have(
				"p cannot be zero, since zero times r would make q zero",
				"p ≠ vec_zero",
				By(Normalized, qNonzero, divided, comm_ring.MulLeftZeroOn.Read(polynomialRing).AsFact().At(r)))
			rNonzero := a.Have(
				"r cannot be zero, since p times zero would make q zero",
				"r ≠ vec_zero",
				By(
					Normalized,
					qNonzero,
					divided,
					pOver,
					comm_ring.MulRightZeroOn.Read(polynomialRing).AsFact().At(p)))
			degrees := a.Have(
				"the degrees of the nonzero factors add to the degree of q",
				"polynomial_degree(q) = polynomial_degree(p) + polynomial_degree(r)",
				By(
					pNonzero,
					rNonzero,
					divided,
					pOver,
					polynomial.DegreeMul.Read(integral_domain.FieldIntegralDomain.Read(fieldOn)).At(p, r)))
			a.Show(
				"the degree of p is at most that sum",
				By(
					degrees,
					nat_order.LessEqAdd.At(
						a.TermAs[Nat]("polynomial_degree(p)"), a.TermAs[Nat]("polynomial_degree(r)"))))
		}),
})}

// PolynomialBezout — over a field two polynomials not both zero have a
// monic common divisor that is a combination of them: their greatest
// common divisor. Among the nonzero combinations of f and g by
// polynomials over c, well-ordering gives one, h = u₀ f + v₀ g, of least
// degree n. Scaled by a nonzero a it is monic of degree n (MonicAssociate),
// and a • h = (a • u₀) f + (a • v₀) g, scaling by a being multiplication by
// the constant polynomial a (polynomial.PolynomialMulConstant). Dividing a
// combination p of f and g by the monic a • h (MonicDivisionExists) leaves a
// remainder that is again a combination, of degree below n, so zero: a • h
// divides p, and f and g are combinations.
var PolynomialBezout = polynomialBezoutThm{family.Add(registry.ProofEntry{
	Name: "PolynomialBezout",
	Key:  "prop_c2a07a7aefa66f30",
	Reading: "Every common divisor of f and g divides d = u * f + v * " +
		"g, so d is a greatest common divisor; it is monic, so it is unique.",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀f g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, f)",
			"polynomial_over(F.carrier, g)",
			"¬(f = vec_zero ∧ g = vec_zero)",
		},
		Conclusion: "∃d u v:(num → A). " +
			"    polynomial_over(F.carrier, d) ∧ " +
			"    polynomial_monic(d) ∧ " +
			"    polynomial_divides(field_ring(F), d, f) ∧ " +
			"    polynomial_divides(field_ring(F), d, g) ∧ " +
			"    polynomial_over(F.carrier, u) ∧ " +
			"    polynomial_over(F.carrier, v) ∧ " +
			"    d = polynomial_mul(u, f) + polynomial_mul(v, g)",
	},
		func(arg *Argument, fieldOn field.FieldFact[on.F], f, g *Arrow[Nat, A], hypotheses Fact) {
			ring := field.RingOn.Read(fieldOn)
			polynomialRing := polynomial.PolynomialRingOn.Read(ring)
			smulIn := module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring))
			zero := arg.TermAs[A]("F.zero")
			onePolynomial, zeroPolynomial :=
				arg.TermAs[Fun[Nat, A]]("basis_vector(0)"), arg.TermAs[Fun[Nat, A]]("vec_zero")
			oneOver, zeroOver :=
				polynomial.BasisVectorOver.Read(ring).At(arg.TermAs[Nat]("0")), polynomial.VecZeroOver.Read(ring)
			parts := arg.Conjuncts(
				hypotheses,
				"f is a polynomial over c",
				"so is g",
				"f and g are not both zero")
			fOver, gOver, notBothZero := parts[0], parts[1], parts[2]
			fgMembers := arg.Have(
				"f and g lie in the ring of polynomials over c",
				"f ∈ «fieldPolynomials» ∧ g ∈ «fieldPolynomials»",
				BySets(fOver, gOver))
			fCombination := arg.Have(
				"f is 1 f + 0 g",
				"f = polynomial_mul(basis_vector(0), f) + polynomial_mul(vec_zero, g)",
				ByArith(polynomialRing, fgMembers))
			gCombination := arg.Have(
				"g is 0 f + 1 g",
				"g = polynomial_mul(vec_zero, f) + polynomial_mul(basis_vector(0), g)",
				ByArith(polynomialRing, fgMembers))

			attained := arg.Have(
				"some nonzero combination of f and g has a degree: "+
					"f = 1 f + 0 g, or g = 0 f + 1 g where f is F.zero",
				"∃n:num. ∃p u v:(num → A). "+
					"    polynomial_over(F.carrier, p) ∧ "+
					"    polynomial_over(F.carrier, u) ∧ "+
					"    polynomial_over(F.carrier, v) ∧ "+
					"    p = polynomial_mul(u, f) + polynomial_mul(v, g) ∧ "+
					"    p ≠ vec_zero ∧ "+
					"    polynomial_degree(p) = n",
				Derive(func(b *Argument) {
					fNonzero := b.Unless(
						b.Term("f = vec_zero"),
						"where f is F.zero, g is not, and g = 0 f + 1 g is a nonzero combination of g's degree",
						Given(func(e *Argument, fZero Fact) {
							e.Take(e.TermAs[Nat]("polynomial_degree(g)"))
							e.Take(g)
							e.Take(zeroPolynomial)
							e.Take(onePolynomial)
							e.Show(
								"g, not zero as f is, is the combination 0 f + 1 g",
								By(Normalized, gOver, zeroOver, oneOver, gCombination, fZero, notBothZero))
						}))
					b.Take(b.TermAs[Nat]("polynomial_degree(f)"))
					b.Take(f)
					b.Take(onePolynomial)
					b.Take(zeroPolynomial)
					b.Show(
						"f, not zero, is the combination 1 f + 0 g",
						By(fOver, oneOver, zeroOver, fCombination, fNonzero))
				}))
			least := arg.Have(
				"by well-ordering some such degree n is least",
				"∃n:num. "+
					"    (∃p u v:(num → A). "+
					"        polynomial_over(F.carrier, p) ∧ "+
					"        polynomial_over(F.carrier, u) ∧ "+
					"        polynomial_over(F.carrier, v) ∧ "+
					"        p = polynomial_mul(u, f) + polynomial_mul(v, g) ∧ "+
					"        p ≠ vec_zero ∧ "+
					"        polynomial_degree(p) = n) ∧ "+
					"    (∀m:num. "+
					"        m < n ⇒ "+
					"        ¬(∃p u v:(num → A). "+
					"                polynomial_over(F.carrier, p) ∧ "+
					"                polynomial_over(F.carrier, u) ∧ "+
					"                polynomial_over(F.carrier, v) ∧ "+
					"                p = polynomial_mul(u, f) + polynomial_mul(v, g) ∧ "+
					"                p ≠ vec_zero ∧ "+
					"                polynomial_degree(p) = m))",
				By(
					attained,
					nat_order.WellOrdering.At(arg.TermAs[Set[Nat]](
						"λn:num. ∃p u v:(num → A). "+
							"    polynomial_over(F.carrier, p) ∧ "+
							"    polynomial_over(F.carrier, u) ∧ "+
							"    polynomial_over(F.carrier, v) ∧ "+
							"    p = polynomial_mul(u, f) + polynomial_mul(v, g) ∧ "+
							"    p ≠ vec_zero ∧ "+
							"    polynomial_degree(p) = n"))))
			n, leastFacts := arg.UnpackAs[Nat](least)
			leastParts := arg.Conjuncts(
				leastFacts,
				"some nonzero combination of f and g has degree n",
				"none has a smaller degree")
			attainedAtN, noneBelow := leastParts[0], leastParts[1]
			h, u0, v0, hFacts := arg.Unpack3As[Fun[Nat, A], Fun[Nat, A], Fun[Nat, A]](
				attainedAtN, "h", "u₀", "v₀")
			hParts := arg.Conjuncts(
				hFacts,
				"h is a polynomial over c",
				"so is u₀",
				"and v₀",
				"h = u₀ f + v₀ g",
				"h is not zero",
				"h has degree n")
			hOver, u0Over, v0Over, hCombination, hNonzero, hDegree :=
				hParts[0], hParts[1], hParts[2], hParts[3], hParts[4], hParts[5]
			minimal := arg.Have(
				"so every nonzero combination of f and g has degree at least n",
				Statement{
					Binders: "∀p u v:(num → A).",
					Hypotheses: []string{
						"polynomial_over(F.carrier, p)",
						"polynomial_over(F.carrier, u)",
						"polynomial_over(F.carrier, v)",
						"p = polynomial_mul(u, f) + polynomial_mul(v, g)",
						"p ≠ vec_zero",
					},
					Conclusion: "n ≤ polynomial_degree(p)",
				},
				Derive(func(b *Argument) {
					p1 := b.FixAs[Fun[Nat, A]]("p₁")
					u1 := b.FixAs[Fun[Nat, A]]("u₁")
					v1 := b.FixAs[Fun[Nat, A]]("v₁")
					nonzeroCombination := b.Assume()
					degree := b.TermAs[Nat]("polynomial_degree(p₁)")
					attainedThere := b.Have(
						"p₁'s degree is that of a nonzero combination, p₁ itself",
						"∃p u v:(num → A). "+
							"    polynomial_over(F.carrier, p) ∧ "+
							"    polynomial_over(F.carrier, u) ∧ "+
							"    polynomial_over(F.carrier, v) ∧ "+
							"    p = polynomial_mul(u, f) + polynomial_mul(v, g) ∧ "+
							"    p ≠ vec_zero ∧ "+
							"    polynomial_degree(p) = polynomial_degree(p₁)",
						Derive(func(e *Argument) {
							e.Take(p1)
							e.Take(u1)
							e.Take(v1)
							e.Show(
								"p₁ = u₁ f + v₁ g is not F.zero",
								By(nonzeroCombination))
						}))
					b.Show(
						"and no nonzero combination has a degree below n",
						By(attainedThere, noneBelow.At(degree), nat_order.NotLessThan.At(degree, n)))
				}))

			a, associate := arg.UnpackAs[A](
				GroupPremises(hOver, hNonzero, MonicAssociate.Read(fieldOn).At(h)), "a")
			scaled := arg.Conjuncts(
				associate,
				"a lies in c",
				"a is not zero",
				"a • h is a polynomial over c",
				"monic",
				"of h's degree")
			aIn, scaledOver, monic, sameDegree := scaled[0], scaled[2], scaled[3], scaled[4]
			aMember, monicMultiple := arg.MemberOf[on.F](a, aIn), arg.TermAs[Fun[Nat, A]]("a • h")
			cofactorsOver := arg.Have(
				"a • u₀ and a • v₀ are polynomials over c, which form a module over the field",
				"polynomial_over(F.carrier, a • u₀) ∧ polynomial_over(F.carrier, a • v₀)",
				BySets(aIn, u0Over, v0Over, smulIn))

			constant := arg.TermAs[Fun[Nat, A]]("a • basis_vector(0)")
			members := arg.Have(
				"f, g, h, u₀, v₀, their multiples by a and the constant "+
					"polynomial a lie in the ring of polynomials over c",
				"f ∈ «fieldPolynomials» ∧ "+
					"g ∈ «fieldPolynomials» ∧ "+
					"h ∈ «fieldPolynomials» ∧ "+
					"u₀ ∈ «fieldPolynomials» ∧ "+
					"v₀ ∈ «fieldPolynomials» ∧ "+
					"a • h ∈ «fieldPolynomials» ∧ "+
					"a • u₀ ∈ «fieldPolynomials» ∧ "+
					"a • v₀ ∈ «fieldPolynomials» ∧ "+
					"a • basis_vector(0) ∈ «fieldPolynomials»",
				BySets(fOver, gOver, hOver, u0Over, v0Over, aIn, oneOver, smulIn))
			u0Scaled := arg.Have(
				"u₀ times the constant polynomial a is a • u₀",
				"polynomial_mul(u₀, a • basis_vector(0)) = a • u₀",
				By(u0Over, polynomial.PolynomialMulConstant.Read(ring).At(aMember, u0)))
			v0Scaled := arg.Have(
				"v₀ times it is a • v₀",
				"polynomial_mul(v₀, a • basis_vector(0)) = a • v₀",
				By(v0Over, polynomial.PolynomialMulConstant.Read(ring).At(aMember, v0)))
			monicCombination := arg.Have(
				"so a • h, the constant a times u₀ f + v₀ g, is the combination (a • u₀) f + (a • v₀) g",
				"a • h = polynomial_mul(a • u₀, f) + polynomial_mul(a • v₀, g)",
				ByArith(
					polynomialRing,
					members,
					hOver,
					polynomial.PolynomialMulConstant.Read(ring).At(aMember, h),
					Scaled(f, u0Scaled),
					Scaled(g, v0Scaled),
					Scaled(constant, hCombination)))

			divides := arg.Have(
				"a • h divides every combination of f and g",
				Statement{
					Binders: "∀p u v:(num → A).",
					Hypotheses: []string{
						"polynomial_over(F.carrier, p)",
						"polynomial_over(F.carrier, u)",
						"polynomial_over(F.carrier, v)",
						"p = polynomial_mul(u, f) + polynomial_mul(v, g)",
					},
					Conclusion: "polynomial_divides(field_ring(F), a • h, p)",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[Fun[Nat, A]]("p")
					b.FixAs[Fun[Nat, A]]("u")
					b.FixAs[Fun[Nat, A]]("v")
					given := b.Conjuncts(
						b.Assume(),
						"p is a polynomial over c",
						"so is u",
						"and v",
						"p = u f + v g")
					pOver, uOver, vOver, pCombination := given[0], given[1], given[2], given[3]
					q, r, division := b.Obtain2As[Fun[Nat, A], Fun[Nat, A]](
						"dividing p by the monic a • h leaves a quotient q and "+
							"a remainder r vanishing from the degree of a • h on",
						"∃q r:(num → A). «division»(F.carrier, p, a • h, q, r)",
						By(pOver, scaledOver, monic, MonicDivisionExists.Read(ring).At(p, monicMultiple)))
					divided := b.Conjuncts(
						division,
						"q is a polynomial over c",
						"so is r",
						"r vanishes from the degree of a • h on",
						"p = (a • h) q + r")
					qOver, rOver, rShort, pDivided := divided[0], divided[1], divided[2], divided[3]
					inRing := b.Have(
						"p, u, v, q and r lie in the ring of polynomials over c",
						"p ∈ «fieldPolynomials» ∧ "+
							"u ∈ «fieldPolynomials» ∧ "+
							"v ∈ «fieldPolynomials» ∧ "+
							"q ∈ «fieldPolynomials» ∧ "+
							"r ∈ «fieldPolynomials»",
						BySets(pOver, uOver, vOver, qOver, rOver))
					remainderZero := b.Have(
						"the remainder r is zero",
						"r = vec_zero",
						Derive(func(e *Argument) {
							nonzero := e.SupposeNot()
							below := e.Have(
								"else r has degree below that of a • h, which is n",
								"polynomial_degree(r) < n",
								By(nonzero, sameDegree, hDegree, polynomial.DegreeBelow.At(zero, proof.InhabitFrom(r, rShort))))
							sCofactor := e.Let("s", e.Term("u - polynomial_mul(q, a • u₀)"))
							tCofactor := e.Let("t", e.Term("v - polynomial_mul(q, a • v₀)"))
							stOver := e.Have(
								"s and t are polynomials over c",
								"polynomial_over(F.carrier, s) ∧ polynomial_over(F.carrier, t)",
								sCofactor.Rw(),
								tCofactor.Rw(),
								BySets(members, inRing, comm_ring.SubIn.Read(polynomialRing), comm_ring.MulIn.Read(polynomialRing)))
							rCombination := e.Have(
								"r = p - (a • h) q is the combination s f + t g",
								"r = polynomial_mul(s, f) + polynomial_mul(t, g)",
								sCofactor.Rw(),
								tCofactor.Rw(),
								ByArith(polynomialRing, members, inRing, pDivided, pCombination, Scaled(q, monicCombination)))
							atLeast := e.Have(
								"so r, a nonzero combination of f and g, has degree at least n",
								"n ≤ polynomial_degree(r)",
								By(
									rOver,
									stOver,
									rCombination,
									nonzero,
									minimal.At(r, e.TermAs[Fun[Nat, A]]("s"), e.TermAs[Fun[Nat, A]]("t"))))
							e.Show(
								"which is not below n",
								ByArith(below, atLeast))
						}))
					quotient := b.Have(
						"so p = (a • h) q",
						"p = polynomial_mul(a • h, q)",
						ByArith(polynomialRing, members, inRing, pDivided, remainderZero))
					b.Show(
						"q is the quotient of p by a • h",
						Unfold(PolynomialDividesDef),
						Witness(q),
						By(qOver, quotient))
				}))
			dividesF := arg.Have(
				"a • h divides f, the combination 1 f + 0 g",
				"polynomial_divides(field_ring(F), a • h, f)",
				By(fOver, oneOver, zeroOver, fCombination, divides.At(f, onePolynomial, zeroPolynomial)))
			dividesG := arg.Have(
				"and g, the combination 0 f + 1 g",
				"polynomial_divides(field_ring(F), a • h, g)",
				By(gOver, zeroOver, oneOver, gCombination, divides.At(g, zeroPolynomial, onePolynomial)))
			arg.Take(monicMultiple)
			arg.Take(arg.TermAs[Fun[Nat, A]]("a • u₀"))
			arg.Take(arg.TermAs[Fun[Nat, A]]("a • v₀"))
			arg.Show(
				"so a • h, monic and the combination (a • u₀) f + (a • v₀) g, is a common divisor of f and g",
				By(scaledOver, monic, dividesF, dividesG, cofactorsOver, monicCombination))
		}),
})}

// IrreducibleCoprime — over a field an irreducible polynomial that does
// not divide f is coprime to it: some combination of the two is the one
// polynomial. Bézout's identity gives a monic common divisor d of p and f
// that is a combination of them, and d is the one polynomial. With
// p = d r, irreducibility makes d or r of degree zero. Were it r, r would
// be a nonzero constant k • basis_vector(0) (polynomial.DegreeZeroConstant), the
// constant w = inv(k) • basis_vector(0) would invert it
// (polynomial.PolynomialMulConstant), and d = d r w = p w: p would divide d, and so f
// (DividesTrans). So d has degree zero, and a monic polynomial of degree
// zero is the one polynomial (polynomial.MonicDegreeZero).
var IrreducibleCoprime = irreducibleCoprimeThm{family.Add(registry.ProofEntry{
	Name: "IrreducibleCoprime",
	Key:  "prop_7dbdf96cc6419d6b",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p f:(num → A).",
		Hypotheses: []string{
			"polynomial_irreducible(field_ring(F), p)",
			"polynomial_over(F.carrier, f)",
			"¬polynomial_divides(field_ring(F), p, f)",
		},
		Conclusion: "∃u v:(num → A). " +
			"    polynomial_over(F.carrier, u) ∧ " +
			"    polynomial_over(F.carrier, v) ∧ " +
			"    polynomial_mul(u, p) + polynomial_mul(v, f) = basis_vector(0)",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p, f *Arrow[Nat, A], given Fact) {
			ring := field.RingOn.Read(fieldOn)
			polynomialRing := polynomial.PolynomialRingOn.Read(ring)
			zero, c := a.TermAs[A]("F.zero"), a.TermAs[Set[A]]("F.carrier")
			onePolynomial := a.TermAs[Fun[Nat, A]]("basis_vector(0)")
			parts := a.Conjuncts(
				given,
				"p is irreducible",
				"f is a polynomial over c",
				"p does not divide f")
			fOver, notDivides := parts[1], parts[2]
			irreducible := a.Conjuncts(
				a.Unfolded(parts[0], PolynomialIrreducibleDef),
				"p is a polynomial over c",
				"of positive degree",
				"and has a factor of degree zero in every factorization over c")
			pOver, positive, factorizations := irreducible[0], irreducible[1], irreducible[2]
			pNonzero := a.Unless(
				a.Term("p = vec_zero"),
				"were p zero, its degree would be zero, not positive",
				Given(func(b *Argument, isZero Fact) {
					zeroDegree := b.Have(
						"p, the zero polynomial, has degree zero",
						"polynomial_degree(p) = 0",
						isZero.Rw(),
						By(polynomial.DegreeVecZero.At(zero)))
					b.Show(
						"against the positive degree of p",
						ByArith(positive, zeroDegree))
				}))
			notBoth := a.Have(
				"so p and f are not both zero",
				"¬(p = vec_zero ∧ f = vec_zero)",
				By(Normalized, pNonzero))

			d, u, v, bezout := a.Obtain3As[Fun[Nat, A], Fun[Nat, A], Fun[Nat, A]](
				"Bézout's identity gives a monic common divisor d = u p + v f of p and f",
				"∃d u v:(num → A). "+
					"    polynomial_over(F.carrier, d) ∧ "+
					"    polynomial_monic(d) ∧ "+
					"    polynomial_divides(field_ring(F), d, p) ∧ "+
					"    polynomial_divides(field_ring(F), d, f) ∧ "+
					"    polynomial_over(F.carrier, u) ∧ "+
					"    polynomial_over(F.carrier, v) ∧ "+
					"    d = polynomial_mul(u, p) + polynomial_mul(v, f)",
				By(pOver, fOver, notBoth, PolynomialBezout.Read(fieldOn).At(p, f)))
			common := a.Conjuncts(
				bezout,
				"d is a polynomial over c",
				"monic",
				"d divides p",
				"d divides f",
				"u is a polynomial over c",
				"so is v",
				"d = u p + v f")
			dOver, monic, dDividesP, dDividesF, uOver, vOver, dCombination :=
				common[0], common[1], common[2], common[3], common[4], common[5], common[6]

			degreeZero := a.Have(
				"d has degree zero: were its degree positive, its cofactor r in "+
					"p = d r would have degree zero, and p would divide d and so f",
				"polynomial_degree(d) = 0",
				Derive(func(b *Argument) {
					notConstant := b.SupposeNot()
					r, pFactored := b.UnpackAs[Fun[Nat, A]](b.Unfolded(dDividesP, PolynomialDividesDef), "r")
					pFactors := b.Conjuncts(
						pFactored,
						"r is a polynomial over c",
						"p = d r")
					rOver, pEq := pFactors[0], pFactors[1]
					rConstant := b.Have(
						"then r has degree zero, p being irreducible",
						"polynomial_degree(r) = 0",
						By(factorizations.At(d, r), dOver, rOver, pEq, notConstant))
					rNonzero := b.Unless(
						b.Term("r = vec_zero"),
						"were r zero, so would be p = d r",
						Given(func(e *Argument, rZero Fact) {
							dMember := e.Have(
								"d is a polynomial over c",
								"d ∈ «fieldPolynomials»",
								BySets(dOver))
							pZero := e.Have(
								"so p = d 0 = 0 in the ring of polynomials",
								"p = vec_zero",
								pEq.Rw(),
								rZero.Rw(),
								ByArith(polynomialRing, dMember))
							e.Show(
								"against p being nonzero",
								By(Normalized, pNonzero, pZero))
						}))
					kDef := b.Let("k", b.Term("r(0)"))
					leading := b.Conjuncts(
						b.Have(
							"so r's coefficient k at its degree 0 lies in c and is not zero",
							"k ∈ F.carrier ∧ k ≠ F.zero",
							By(
								Normalized,
								kDef,
								rNonzero,
								rOver,
								rConstant,
								polynomial.LeadingCoefficientNonzero.At(zero, c, r))),
						"k lies in c",
						"k is not zero")
					kIn, kNonzero := leading[0], leading[1]
					k := b.MemberOf[on.F](b.TermAs[A]("k"), kIn)
					inverseIn := b.Have(
						"and so does its inverse",
						"F.inv(k) ∈ F.carrier",
						By(field.InvIn.Read(fieldOn).At(k)))
					inverse := b.MemberOf[on.F](b.TermAs[A]("F.inv(k)"), inverseIn)
					rForm := b.Have(
						"r is the constant polynomial of k",
						"r = k • basis_vector(0)",
						By(Normalized, kDef, rOver, rConstant, polynomial.DegreeZeroConstant.Read(ring).At(r)))
					w, wDef := b.LetAs[Fun[Nat, A]]("w", "F.inv(k) • basis_vector(0)")
					wOver := b.Have(
						"the constant w is a polynomial over c",
						"polynomial_over(F.carrier, w)",
						wDef.Rw(),
						BySets(
							module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
							polynomial.BasisVectorOver.Read(ring),
							inverseIn))
					oneCoefficients := b.Have(
						"every coefficient of the one polynomial lies in c",
						"∀i:num. basis_vector(0, i) ∈ F.carrier",
						By(
							polynomial.BasisVectorOver.Read(ring).At(b.TermAs[Nat]("0")),
							polynomial.PolynomialOverDef.At(zero, c, onePolynomial)))
					rUnit := b.Have(
						"so r w is the one polynomial",
						"polynomial_mul(r, w) = basis_vector(0)",
						CalcEq(
							Leg(
								b.TermAs[Fun[Nat, A]]("F.inv(k) • r"),
								"multiplying by the constant w is scaling by F.inv(k)",
								wDef.Rw(),
								By(rOver, polynomial.PolynomialMulConstant.Read(ring).At(inverse, r))),
							Leg(
								b.TermAs[Fun[Nat, A]]("F.inv(k) • k • basis_vector(0)"),
								"r is the constant polynomial of k",
								rForm.Rw(),
								Basic()),
							Leg(
								b.TermAs[Fun[Nat, A]]("F.inv(k) * k • basis_vector(0)"),
								"scaling by k and then by F.inv(k) is scaling by their product",
								By(oneCoefficients, vec_space.SmulMulOn.Read(ring).At(inverse, k, onePolynomial))),
							Leg(
								b.TermAs[Fun[Nat, A]]("F.one • basis_vector(0)"),
								"F.inv(k) inverts k",
								By(Normalized, kNonzero, field.MulLeftInverseOn.Read(fieldOn).At(k))),
							FinalLeg(
								"and one scales nothing",
								By(oneCoefficients, vec_space.SmulOneOn.Read(ring).At(onePolynomial))),
						))
					members := b.Have(
						"p, d, r and w are polynomials over c",
						"p ∈ «fieldPolynomials» ∧ d ∈ «fieldPolynomials» ∧ r ∈ «fieldPolynomials» ∧ w ∈ «fieldPolynomials»",
						BySets(pOver, dOver, rOver, wOver))
					dIsPW := b.Have(
						"d = d r w = p w",
						"d = polynomial_mul(p, w)",
						ByArith(polynomialRing, members, Scaled(w, pEq), Scaled(d, rUnit)))
					pDividesD := b.Have(
						"so p divides d, with the quotient w",
						"polynomial_divides(field_ring(F), p, d)",
						Unfold(PolynomialDividesDef),
						Witness(w),
						By(wOver, dIsPW))
					b.Show(
						"and so f, which d divides, against the hypothesis that it does not",
						By(notDivides, pOver, pDividesD, dDividesF, DividesTrans.Read(ring).At(p, d, f)))
				}))
			isOne := a.Have(
				"so d, monic of degree zero, is the one polynomial",
				"d = basis_vector(0)",
				By(dOver, monic, degreeZero, polynomial.MonicDegreeZero.Read(ring).At(d)))
			a.Take(u)
			a.Take(v)
			a.Show(
				"so u p + v f = d is the one polynomial",
				By(Normalized, uOver, vOver, dCombination, isOne))
		}),
})}

// IrreducibleDividesProduct — Euclid's lemma: over a field an irreducible
// polynomial dividing a product divides a factor: when p does not divide f
// it is coprime to f (IrreducibleCoprime), and a divisor of f g coprime to f
// divides g (CoprimeDividesProduct).
var IrreducibleDividesProduct = irreducibleDividesProductThm{family.Add(registry.ProofEntry{
	Name: "IrreducibleDividesProduct",
	Key:  "prop_134830993b3220b2",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p f g:(num → A).",
		Hypotheses: []string{
			"polynomial_irreducible(field_ring(F), p)",
			"polynomial_over(F.carrier, f)",
			"polynomial_over(F.carrier, g)",
			"polynomial_divides(field_ring(F), p, polynomial_mul(f, g))",
		},
		Conclusion: "polynomial_divides(field_ring(F), p, f) ∨ polynomial_divides(field_ring(F), p, g)",
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p, f, g *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"p is irreducible",
				"f is over the field",
				"g is over the field",
				"p divides f g")
			notDivides := a.Unless(
				a.Term("polynomial_divides(field_ring(F), p, f)"),
				"if p divides f, it divides a factor of f g",
				Given(func(b *Argument, divides Fact) {
					b.Show(
						"p divides the first factor",
						By(divides))
				}))
			a.Do(Right())
			coprime := a.Have(
				"p, irreducible and not dividing f, is coprime to f",
				"polynomial_coprime(field_ring(F), p, f)",
				Simp(Fwd(PolynomialCoprimeDef)),
				By(notDivides, hypotheses, IrreducibleCoprime.Read(fieldOn).At(p, f)))
			fieldRing := a.TermAs[RingOps[A]]("field_ring(F)")
			a.Show(
				"so p, coprime to f and dividing f g, divides g",
				By(
					given[0],
					coprime,
					hypotheses,
					PolynomialIrreducibleDef.At(fieldRing, p),
					CoprimeDividesProduct.Read(field.RingOn.Read(fieldOn)).At(p, f, g)))
		}),
})}

// IrreducibleFactorExists — over a field a polynomial of positive degree
// has an irreducible factor: choose a positive-degree divisor of least
// degree. A factorization into two nonconstant factors would give a
// positive-degree divisor of smaller degree.
var IrreducibleFactorExists = irreducibleFactorExistsThm{family.Add(registry.ProofEntry{
	Name: "IrreducibleFactorExists",
	Key:  "prop_4a03438bb98ab8b8",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"0 < polynomial_degree(p)",
		},
		Conclusion: "∃q:(num → A). " +
			"    polynomial_irreducible(field_ring(F), q) ∧ polynomial_divides(field_ring(F), q, p)",
		Abbrev: Abbrev{
			{Name: "divisorDegree", Text: "λd:num. ∃f:(num → A). " +
				"    polynomial_over(F.carrier, f) ∧ " +
				"    0 < polynomial_degree(f) ∧ " +
				"    polynomial_divides(field_ring(F), f, p) ∧ " +
				"    polynomial_degree(f) = d"},
		},
	},
		func(a *Argument, fieldOn field.FieldFact[on.F], p *Arrow[Nat, A], hypotheses Fact) {
			ring := field.RingOn.Read(fieldOn)
			zero, fieldRing := a.TermAs[A]("F.zero"), a.TermAs[RingOps[A]]("field_ring(F)")
			pOver := a.Conjuncts(
				hypotheses,
				"p is a polynomial over the field",
				"p has positive degree")[0]
			attained := a.Have(
				"the positive-degree divisors have an attained degree, since p is one",
				"∃d:num. «divisorDegree»(d)",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Nat]("polynomial_degree(p)"))
					b.Take(p)
					b.Show(
						"p divides itself, so it attains its own positive degree",
						By(hypotheses, pOver, DividesRefl.Read(ring).At(p)))
				}))
			_, least := a.ObtainAs[Nat](
				"well-ordering gives a least positive degree n attained by a divisor of p",
				"∃n:num. «divisorDegree»(n) ∧ (∀m:num. m < n ⇒ ¬«divisorDegree»(m))",
				By(attained, nat_order.WellOrdering.At(a.TermAs[Set[Nat]]("«divisorDegree»"))))
			leastParts := a.Conjuncts(
				least,
				"some positive-degree divisor attains n",
				"no positive-degree divisor has degree below n")
			q, selected := a.UnpackAs[Fun[Nat, A]](leastParts[0], "q")
			constantFactor := a.Have(
				"every factorization of q over the field has a factor of degree zero",
				Statement{
					Binders: "∀u v:(num → A).",
					Hypotheses: []string{
						"polynomial_over(F.carrier, u)",
						"polynomial_over(F.carrier, v)",
						"q = polynomial_mul(u, v)",
					},
					Conclusion: "polynomial_degree(u) = 0 ∨ polynomial_degree(v) = 0",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[Fun[Nat, A]]("u"), b.FixAs[Fun[Nat, A]]("v")
					factored := b.Assume()
					nonconstant := b.SupposeNot()
					nonzero := b.Have(
						"neither nonconstant factor is the zero polynomial",
						"u ≠ vec_zero ∧ v ≠ vec_zero",
						By(Normalized, nonconstant, polynomial.DegreeVecZero.At(zero)))
					degrees := b.Have(
						"the degrees of the two nonzero factors add to q's degree",
						"polynomial_degree(q) = polynomial_degree(u) + polynomial_degree(v)",
						By(
							nonzero,
							factored,
							polynomial.DegreeMul.Read(integral_domain.FieldIntegralDomain.Read(fieldOn)).At(u, v)))
					smaller := b.Have(
						"both degrees are positive, so u has positive degree below n",
						"0 < polynomial_degree(u) ∧ polynomial_degree(u) < n",
						ByArith(nonconstant, degrees, selected))
					uDividesQ := b.Have(
						"u divides q with quotient v",
						"polynomial_divides(field_ring(F), u, q)",
						Derive(func(c *Argument) {
							c.Do(Simp(Fwd(PolynomialDividesDef)))
							c.Take(v)
							c.Show(
								"v is over the field and q is the product u v",
								By(factored))
						}))
					uDividesP := b.Have(
						"u is over the field and divides q, which divides p, so u divides p",
						"polynomial_divides(field_ring(F), u, p)",
						By(factored, uDividesQ, selected, DividesTrans.Read(ring).At(u, q, p)))
					attainsSmaller := b.Have(
						"u attains a smaller positive divisor degree",
						"«divisorDegree»(polynomial_degree(u))",
						Derive(func(c *Argument) {
							c.Take(u)
							c.Show(
								"u is that positive-degree divisor of p",
								By(factored, smaller, uDividesP))
						}))
					b.Show(
						"this contradicts the choice of n as the least such degree",
						By(smaller, attainsSmaller, leastParts[1].At(b.TermAs[Nat]("polynomial_degree(u)"))))
				}))
			a.Take(q)
			a.Show(
				"q is an irreducible divisor of p",
				By(selected, constantFactor, PolynomialIrreducibleDef.At(fieldRing, q)))
		}),
})}

// ---------------------------------------------------------------------------
// Coprime polynomials
// ---------------------------------------------------------------------------

// CoprimeSymm — coprimality is symmetric: swap the Bézout coefficients
// and commute the two products in their sum.
var CoprimeSymm = coprimeSymmThm{family.Add(registry.ProofEntry{
	Name: "CoprimeSymm",
	Key:  "prop_b09af707455d34db",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_coprime(R, p, q)",
		},
		Conclusion: "polynomial_coprime(R, q, p)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"p is over the carrier",
				"q is over the carrier",
				"p and q are coprime")
			u, v, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(given[2], PolynomialCoprimeDef), "u", "v")
			atoms := a.Have(
				"the four polynomials lie in the polynomial ring",
				"u ∈ «polynomialRingCarrier» ∧ "+
					"p ∈ «polynomialRingCarrier» ∧ "+
					"v ∈ «polynomialRingCarrier» ∧ "+
					"q ∈ «polynomialRingCarrier»",
				By(hypotheses, bezout))
			commute := a.Have(
				"addition interchanges the two Bézout products",
				"polynomial_mul(v, q) + polynomial_mul(u, p) = polynomial_mul(u, p) + polynomial_mul(v, q)",
				ByArith(polynomial.PolynomialRingOn.Read(ring), atoms))
			a.Do(Simp(Fwd(PolynomialCoprimeDef)))
			a.Take(v)
			a.Take(u)
			a.Show(
				"the swapped coefficients prove coprimality of q and p",
				By(commute, bezout))
		}),
})}

// CoprimeDividesProduct — Euclid's lemma for a coprime factor: a
// polynomial that divides a product and is coprime to one factor divides
// the other. With u p + v q = 1 and q r = p s, r is r (u p + v q) =
// u p r + v (p s) = p (u r + v s), so u r + v s is the quotient.
var CoprimeDividesProduct = coprimeDividesProductThm{family.Add(registry.ProofEntry{
	Name: "CoprimeDividesProduct",
	Key:  "prop_693b8cd8d3b4e1dd",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q r:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, r)",
			"polynomial_coprime(R, p, q)",
			"polynomial_divides(R, p, polynomial_mul(q, r))",
		},
		Conclusion: "polynomial_divides(R, p, r)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"p is over the carrier",
				"q is over the carrier",
				"r is over the carrier",
				"p and q are coprime",
				"p divides q r")
			_, v, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(given[3], PolynomialCoprimeDef), "u", "v")
			_, sFactor := a.UnpackAs[Fun[Nat, A]](a.Unfolded(given[4], PolynomialDividesDef), "s")
			bezoutParts := a.Conjuncts(
				bezout,
				"u is over the carrier",
				"v is over the carrier",
				"u p plus v q is the one polynomial")
			sParts := a.Conjuncts(
				sFactor,
				"s is over the carrier",
				"q r = p s")
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			atoms := a.Have(
				"p, q, r, u, v and s lie in the polynomial ring",
				"p ∈ «polynomialRingCarrier» ∧ "+
					"q ∈ «polynomialRingCarrier» ∧ "+
					"r ∈ «polynomialRingCarrier» ∧ "+
					"u ∈ «polynomialRingCarrier» ∧ "+
					"v ∈ «polynomialRingCarrier» ∧ "+
					"s ∈ «polynomialRingCarrier»",
				By(hypotheses, bezout, sFactor))
			quotient := a.Have(
				"r is r times u p + v q, and with q r = p s that is p times u r + v s",
				"r = polynomial_mul(p, polynomial_mul(u, r) + polynomial_mul(v, s))",
				ByArith(polynomials, atoms, Scaled(r, bezoutParts[2]), Scaled(v, sParts[1])))
			a.Show(
				"the quotient u r + v s is a polynomial over the carrier, so p divides r",
				Simp(Fwd(PolynomialDividesDef)),
				Witness(a.TermAs[Fun[Nat, A]]("polynomial_mul(u, r) + polynomial_mul(v, s)")),
				By(quotient, atoms, comm_ring.AddIn.Read(polynomials), comm_ring.MulIn.Read(polynomials)))
		}),
})}

// CoprimeProductDivides — two coprime divisors of a polynomial have
// their product dividing it. With u p + v q = 1, w = p s and w = q t,
// w is w (u p + v q) = u p (q t) + v q (p s) = p q (u t + v s), so
// u t + v s is the quotient.
var CoprimeProductDivides = coprimeProductDividesThm{family.Add(registry.ProofEntry{
	Name: "CoprimeProductDivides",
	Key:  "prop_77734c1f8d64e510",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q w:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, w)",
			"polynomial_coprime(R, p, q)",
			"polynomial_divides(R, p, w)",
			"polynomial_divides(R, q, w)",
		},
		Conclusion: "polynomial_divides(R, polynomial_mul(p, q), w)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q, w *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"p is over the carrier",
				"q is over the carrier",
				"w is over the carrier",
				"p and q are coprime",
				"p divides w",
				"q divides w")
			_, _, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(given[3], PolynomialCoprimeDef), "u", "v")
			_, sFactor := a.UnpackAs[Fun[Nat, A]](a.Unfolded(given[4], PolynomialDividesDef), "s")
			_, tFactor := a.UnpackAs[Fun[Nat, A]](a.Unfolded(given[5], PolynomialDividesDef), "t")
			bezoutParts := a.Conjuncts(
				bezout,
				"u is over the carrier",
				"v is over the carrier",
				"u p plus v q is the one polynomial")
			sParts := a.Conjuncts(
				sFactor,
				"s is over the carrier",
				"w = p s")
			tParts := a.Conjuncts(
				tFactor,
				"t is over the carrier",
				"w = q t")
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			atoms := a.Have(
				"p, q, w, u, v, s and t lie in the polynomial ring",
				"p ∈ «polynomialRingCarrier» ∧ "+
					"q ∈ «polynomialRingCarrier» ∧ "+
					"w ∈ «polynomialRingCarrier» ∧ "+
					"u ∈ «polynomialRingCarrier» ∧ "+
					"v ∈ «polynomialRingCarrier» ∧ "+
					"s ∈ «polynomialRingCarrier» ∧ "+
					"t ∈ «polynomialRingCarrier»",
				By(hypotheses, bezout, sFactor, tFactor))
			quotient := a.Have(
				"w is w times u p + v q, which is u p times q t plus v q times p s, so p q times u t + v s",
				"w = polynomial_mul(polynomial_mul(p, q), polynomial_mul(u, t) + polynomial_mul(v, s))",
				ByArith(
					polynomials,
					atoms,
					Scaled(w, bezoutParts[2]),
					Scaled(a.TermAs[Fun[Nat, A]]("polynomial_mul(u, p)"), tParts[1]),
					Scaled(a.TermAs[Fun[Nat, A]]("polynomial_mul(v, q)"), sParts[1])))
			a.Show(
				"the quotient u t + v s is a polynomial over the carrier, so p q divides w",
				Simp(Fwd(PolynomialDividesDef)),
				Witness(a.TermAs[Fun[Nat, A]]("polynomial_mul(u, t) + polynomial_mul(v, s)")),
				By(quotient, atoms, comm_ring.AddIn.Read(polynomials), comm_ring.MulIn.Read(polynomials)))
		}),
})}

// CoprimeDivisor — divisors of two coprime polynomials are coprime.
var CoprimeDivisor = coprimeDivisorThm{family.Add(registry.ProofEntry{
	Name: "CoprimeDivisor",
	Key:  "prop_35f3ce881eff9f5e",
	Deps: []registry.EntryLike{
		PolynomialCoprimeDef,
		PolynomialDividesDef,
		polynomial.PolynomialRingOn,
		polynomial.PolynomialMulOver,
	},
	Build: family.Card(comm_ring.CommRingOn.Statement(Statement{
		Binders: "∀p q d e:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, d)",
			"polynomial_over(R.carrier, e)",
			"polynomial_coprime(R, p, q)",
			"polynomial_divides(R, d, p)",
			"polynomial_divides(R, e, q)",
		},
		Conclusion: "polynomial_coprime(R, d, e)",
	}),
		"with p = polynomial_mul(d, r) and q = polynomial_mul(e, s), the combination "+
			"polynomial_mul(u, p) + polynomial_mul(v, q) is "+
			"polynomial_mul(polynomial_mul(u, r), d) + polynomial_mul(polynomial_mul(v, "+
			"s), e), its coefficients over R.carrier (PolynomialMulOver, PolynomialRingOn)"),
})}

// CoprimeSum — p is coprime to q exactly when it is coprime to p + q: each
// of q and p + q is the other with a multiple of p added, by the unit one
// way and by its negative the other.
var CoprimeSum = coprimeSumThm{family.Add(registry.ProofEntry{
	Name: "CoprimeSum",
	Key:  "prop_99e4587ed24258c1",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
		},
		Conclusion: "polynomial_coprime(R, p, q) ⇔ polynomial_coprime(R, p, p + q)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q *Arrow[Nat, A], hypotheses Fact) {
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			atoms := a.Have(
				"p and q lie in the polynomial ring",
				"p ∈ «polynomialRingCarrier» ∧ q ∈ «polynomialRingCarrier»",
				By(hypotheses))
			unit := a.TermAs[Fun[Nat, A]]("basis_vector(0)")
			negativeUnit := a.TermAs[Fun[Nat, A]]("vec_neg(basis_vector(0))")
			sum := a.TermAs[Fun[Nat, A]]("p + q")
			over := a.Have(
				"the unit, its negative and p + q are polynomials over the carrier",
				"polynomial_over(R.carrier, basis_vector(0)) ∧ "+
					"polynomial_over(R.carrier, vec_neg(basis_vector(0))) ∧ "+
					"polynomial_over(R.carrier, p + q)",
				By(
					atoms,
					polynomial.BasisVectorOver.Read(ring),
					comm_ring.NegIn.Read(polynomials),
					comm_ring.AddIn.Read(polynomials)))
			addP := a.Have(
				"adding p to q is adding the multiple of p by the unit",
				"q + polynomial_mul(p, basis_vector(0)) = p + q",
				ByArith(polynomials, atoms))
			takeP := a.Have(
				"taking p back is adding the multiple of p by the negative unit",
				"p + q + polynomial_mul(p, vec_neg(basis_vector(0))) = q",
				ByArith(polynomials, atoms))
			a.Iff()
			a.Forward(
				"coprime to q, p is coprime to q plus a multiple of p",
				func(b *Argument, coprime Fact) {
					b.Show(
						"the multiple by the unit gives p + q",
						By(hypotheses, over, addP, coprime, CoprimeAddMultiple.Read(ring).At(p, q, unit)))
				})
			a.Backward(
				"coprime to p + q, p is coprime to p + q plus a multiple of p",
				func(b *Argument, coprime Fact) {
					b.Show(
						"the multiple by the negative unit gives q",
						By(
							Normalized,
							hypotheses,
							over,
							takeP,
							coprime,
							CoprimeAddMultiple.Read(ring).At(p, sum, negativeUnit)))
				})
		}),
})}

// CoprimeAddMultiple — adding a multiple of p keeps a polynomial coprime
// to p: the added p s is taken back out of the coefficient of p, so a
// Bézout identity u p + v r = 1 becomes (u − v s) p + v (r + p s) = 1.
var CoprimeAddMultiple = coprimeAddMultipleThm{family.Add(registry.ProofEntry{
	Name: "CoprimeAddMultiple",
	Key:  "prop_a98a2f08d0d9bb96",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p r s:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, r)",
			"polynomial_over(R.carrier, s)",
			"polynomial_coprime(R, p, r)",
		},
		Conclusion: "polynomial_coprime(R, p, r + polynomial_mul(p, s))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, r, s *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"p is over the carrier",
				"r is over the carrier",
				"s is over the carrier",
				"p and r are coprime")
			_, v, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(given[3], PolynomialCoprimeDef), "u", "v")
			atoms := a.Have(
				"the polynomials in the Bézout identity lie in the polynomial ring",
				"p ∈ «polynomialRingCarrier» ∧ "+
					"r ∈ «polynomialRingCarrier» ∧ "+
					"s ∈ «polynomialRingCarrier» ∧ "+
					"u ∈ «polynomialRingCarrier» ∧ "+
					"v ∈ «polynomialRingCarrier»",
				By(hypotheses, bezout))
			identity := a.Have(
				"subtracting the added multiple from the first coefficient preserves the Bézout identity",
				"polynomial_mul(u - polynomial_mul(v, s), p) + polynomial_mul(v, r + polynomial_mul(p, s)) = "+
					"basis_vector(0)",
				ByArith(polynomial.PolynomialRingOn.Read(ring), atoms, bezout))
			coefficient := a.Have(
				"the adjusted coefficient is a polynomial over the carrier",
				"polynomial_over(R.carrier, u - polynomial_mul(v, s))",
				By(
					comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring)),
					atoms,
					hypotheses,
					polynomial.PolynomialMulOver.Read(ring).At(v, s)))
			a.Do(Simp(Fwd(PolynomialCoprimeDef)))
			a.Take(a.TermAs[Fun[Nat, A]]("u - polynomial_mul(v, s)"))
			a.Take(v)
			a.Show(
				"the adjusted coefficients prove coprimality after adding the multiple",
				By(identity, bezout, coefficient))
		}),
})}

// CoprimeMono — polynomials coprime over a subset of the ring's carrier are
// coprime over the ring: the restriction keeps R's operations, so the Bézout
// identity over K is one over R, its coefficients in the larger carrier
// (polynomial.PolynomialOverMono).
var CoprimeMono = coprimeMonoThm{family.Add(registry.ProofEntry{
	Name: "CoprimeMono",
	Key:  "prop_d863d25e7f5e61b2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀K:set(A). ∀p q:(num → A).",
		Hypotheses: []string{
			"K ⊆ R.carrier",
			"polynomial_coprime(restrict_ring(R, K), p, q)",
		},
		Conclusion: "polynomial_coprime(R, p, q)",
	},
		func(a *Argument, _ *Expr[RingOps[A]], K *Expr[Set[A]], p, q *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"K lies in the ring's carrier",
				"p and q are coprime over K")
			u, v, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(given[1], PolynomialCoprimeDef), "u", "v")
			zero, carrier := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			a.Show(
				"the same Bézout identity, its coefficients over the larger carrier, proves coprimality over R",
				Simp(Fwd(PolynomialCoprimeDef)),
				Witness(u),
				Witness(v),
				By(
					given[0],
					bezout,
					polynomial.PolynomialOverMono.At(zero, K, carrier, u),
					polynomial.PolynomialOverMono.At(zero, K, carrier, v)))
		}),
})}

// CoprimeMul — a product of two polynomials coprime to r is coprime to r:
// scaling the first Bézout identity by s q and using the second gives
// coefficients u s and v s q + t for p q and r.
var CoprimeMul = coprimeMulThm{family.Add(registry.ProofEntry{
	Name: "CoprimeMul",
	Key:  "prop_8f89ea978b936b00",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q r:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, r)",
			"polynomial_coprime(R, p, r)",
			"polynomial_coprime(R, q, r)",
		},
		Conclusion: "polynomial_coprime(R, polynomial_mul(p, q), r)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p, q, r *Arrow[Nat, A], hypotheses Fact) {
			given := a.Conjuncts(
				hypotheses,
				"p is over the carrier",
				"q is over the carrier",
				"r is over the carrier",
				"p and r are coprime",
				"q and r are coprime")
			_, _, bezoutP := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(given[3], PolynomialCoprimeDef), "u", "v")
			_, _, bezoutQ := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(given[4], PolynomialCoprimeDef), "s", "t")
			first := a.Conjuncts(
				bezoutP,
				"u is over the carrier",
				"v is over the carrier",
				"u p plus v r is the one polynomial")
			atoms := a.Have(
				"the polynomials in both Bézout identities lie in the polynomial ring",
				"p ∈ «polynomialRingCarrier» ∧ "+
					"q ∈ «polynomialRingCarrier» ∧ "+
					"r ∈ «polynomialRingCarrier» ∧ "+
					"u ∈ «polynomialRingCarrier» ∧ "+
					"v ∈ «polynomialRingCarrier» ∧ "+
					"s ∈ «polynomialRingCarrier» ∧ "+
					"t ∈ «polynomialRingCarrier»",
				By(hypotheses, bezoutP, bezoutQ))
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			sq := a.TermAs[Fun[Nat, A]]("polynomial_mul(s, q)")
			identity := a.Have(
				"scaling the first identity by s q and combining "+
					"with the second gives a Bézout identity for p q and r",
				"polynomial_mul(polynomial_mul(u, s), polynomial_mul(p, q)) + "+
					"polynomial_mul(polynomial_mul(polynomial_mul(v, s), q) + t, r) = "+
					"basis_vector(0)",
				ByArith(polynomials, atoms, Scaled(sq, first[2]), bezoutQ))
			a.Do(Simp(Fwd(PolynomialCoprimeDef)))
			a.Take(a.TermAs[Fun[Nat, A]]("polynomial_mul(u, s)"))
			a.Take(a.TermAs[Fun[Nat, A]]("polynomial_mul(polynomial_mul(v, s), q) + t"))
			a.Show(
				"the constructed polynomial coefficients prove coprimality of p q and r",
				By(comm_ring.MulIn.Read(polynomials), comm_ring.AddIn.Read(polynomials), identity, atoms))
		}),
})}

// CoprimePow — powers of coprime polynomials are coprime.
var CoprimePow = coprimePowThm{family.Add(registry.ProofEntry{
	Name: "CoprimePow",
	Key:  "prop_d1673a4d56a8243",
	Deps: []registry.EntryLike{
		CoprimeMul,
		CoprimeSymm,
		polynomial.PolynomialPowZero,
		polynomial.PolynomialPowSuc,
		polynomial.PolynomialPowOver,
		polynomial.BasisVectorOver,
		polynomial.PolynomialOneMul,
	},
	Build: family.Card(comm_ring.CommRingOn.Statement(Statement{
		Binders: "∀m n:num. ∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_coprime(R, p, q)",
		},
		Conclusion: "polynomial_coprime(R, polynomial_pow(p, m), polynomial_pow(q, n))",
	}),
		"the one polynomial, the zeroth power (PolynomialPowZero), is coprime to every q, "+
			"by polynomial_mul(basis_vector(0), basis_vector(0)) + polynomial_mul(vec_zero, "+
			"q); induction on m by CoprimeMul, polynomial_pow(p, suc(m)) being "+
			"polynomial_mul(p, polynomial_pow(p, m)) (PolynomialPowSuc), makes "+
			"polynomial_pow(p, m) coprime to q; then the same induction on n after CoprimeSymm"),
})}

// ---------------------------------------------------------------------------
// The pseudo-remainder over a field
// ---------------------------------------------------------------------------

// PseudoRemainderDivides — over a field, when cᵏ f = g·s + r for a nonzero
// c and a remainder r vanishing from the degree of g on, g divides f
// exactly when r is zero: a quotient q of f by g makes r = g·(cᵏ q − s), a
// multiple of g below its degree, so zero (DividesDegree); and with r
// zero, f is g times c⁻ᵏ s, c⁻ᵏ cᵏ being one.
var PseudoRemainderDivides = pseudoRemainderDividesThm{family.Add(registry.ProofEntry{
	Name: "PseudoRemainderDivides",
	Key:  "prop_8ff7ca1701d123e9",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀c:A. ∀k:num. ∀f g s r:(num → A).",
		Hypotheses: []string{
			"c ∈ F.carrier",
			"c ≠ F.zero",
			"polynomial_over(F.carrier, f)",
			"polynomial_over(F.carrier, g)",
			"polynomial_over(F.carrier, s)",
			"polynomial_over(F.carrier, r)",
			"monoid_pow(F.mul, F.one, c, k) • f = polynomial_mul(g, s) + r",
			"vec⟨polynomial_degree(g)⟩(r)",
		},
		Conclusion: "polynomial_divides(field_ring(F), g, f) ⇔ r = vec_zero",
	}, func(
		a *Argument,
		fieldOn field.FieldFact[on.F],
		c *Expr[A],
		k *Expr[Nat],
		f, g, s, r *Arrow[Nat, A],
		hypotheses Fact,
	) {
		given := a.Conjuncts(
			hypotheses,
			"c lies in F",
			"c is not zero",
			"f is a polynomial over F",
			"so is g",
			"so is s",
			"so is r",
			"cᵏ f is g·s plus r",
			"r vanishes from the degree of g on")
		cIn, cNonzero, fOver, gOver, sOver, rOver, pseudo, below :=
			given[0], given[1], given[2], given[3], given[4], given[5], given[6], given[7]
		ring := field.RingOn.Read(fieldOn)
		polynomialRing := polynomial.PolynomialRingOn.Read(ring)
		polynomialModule := polynomial.PolynomialModuleOn.Read(ring)
		scalar := a.TermAs[A]("monoid_pow(F.mul, F.one, c, k)")
		power := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).At(a.MemberOf[on.F](c, cIn), k)
		a.Iff()
		a.Forward(
			"a quotient of f by g makes r a multiple of g of degree below g, so zero",
			func(b *Argument, divides Fact) {
				q, quotient := b.UnpackAs[Fun[Nat, A]](b.Unfolded(divides, PolynomialDividesDef), "q")
				parts := b.Conjuncts(
					quotient,
					"q is a polynomial over F",
					"f is g·q")
				scaled := b.Have(
					"so cᵏ f is g·(cᵏ q), the scalar passing through the product",
					"monoid_pow(F.mul, F.one, c, k) • f = polynomial_mul(g, monoid_pow(F.mul, F.one, c, k) • q)",
					By(
						parts[1],
						power,
						gOver,
						parts[0],
						polynomial.PolynomialMulScalar.Read(ring).AsFact().At(scalar, g, q),
						polynomial.PolynomialOverDef))
				members := b.Have(
					"g, r, s and the scaled q and f lie in the ring of polynomials over F",
					"g ∈ «fieldPolynomials» ∧ "+
						"r ∈ «fieldPolynomials» ∧ "+
						"s ∈ «fieldPolynomials» ∧ "+
						"monoid_pow(F.mul, F.one, c, k) • q ∈ «fieldPolynomials» ∧ "+
						"monoid_pow(F.mul, F.one, c, k) • f ∈ «fieldPolynomials»",
					By(power, fOver, gOver, rOver, sOver, parts[0], module.SmulIn.Read(polynomialModule)))
				multiple := b.Have(
					"so r = cᵏ f − g·s = g·(cᵏ q − s)",
					"r = polynomial_mul(g, monoid_pow(F.mul, F.one, c, k) • q - s)",
					ByArith(polynomialRing, pseudo, scaled, members))
				dividesR := b.Have(
					"g divides r, with the quotient cᵏ q − s",
					"polynomial_divides(field_ring(F), g, r)",
					Unfold(PolynomialDividesDef),
					Witness(b.TermAs[Fun[Nat, A]]("monoid_pow(F.mul, F.one, c, k) • q - s")),
					By(
						multiple,
						power,
						parts[0],
						sOver,
						comm_ring.SubIn.Read(polynomialRing),
						module.SmulIn.Read(polynomialModule)))
				b.Show(
					"a nonzero multiple of g has degree at least that of g, and r has degree below it",
					By(
						dividesR,
						gOver,
						below,
						DividesDegree.Read(fieldOn).AsFact().At(g, r),
						polynomial.DegreeBelow.At(b.TermAs[A]("F.zero"), proof.InhabitFrom(r, below)),
						nat_order.NotLessEq))
			})
		a.Backward(
			"with r zero, cᵏ f is g·s, and f is g times c⁻ᵏ s",
			func(b *Argument, zero Fact) {
				nonzero := b.Have(
					"a power of the nonzero c is not zero",
					"monoid_pow(F.mul, F.one, c, k) ≠ F.zero",
					By(cNonzero, field.PowEqZeroOn.Read(fieldOn).At(b.MemberOf[on.F](c, cIn), k)))
				members := b.Have(
					"g, s, r and cᵏ f lie in the ring of polynomials over F",
					"g ∈ «fieldPolynomials» ∧ "+
						"s ∈ «fieldPolynomials» ∧ "+
						"r ∈ «fieldPolynomials» ∧ "+
						"monoid_pow(F.mul, F.one, c, k) • f ∈ «fieldPolynomials»",
					By(power, fOver, gOver, rOver, sOver, module.SmulIn.Read(polynomialModule)))
				scaled := b.Have(
					"the remainder being zero, cᵏ f is g·s",
					"monoid_pow(F.mul, F.one, c, k) • f = polynomial_mul(g, s)",
					ByArith(polynomialRing, pseudo, zero, members))
				inverse := b.TermAs[A]("F.inv(monoid_pow(F.mul, F.one, c, k))")
				b.Show(
					"so f = (c⁻ᵏ cᵏ) f = c⁻ᵏ (g·s) = g·(c⁻ᵏ s)",
					Unfold(PolynomialDividesDef),
					Witness(b.TermAs[Fun[Nat, A]]("F.inv(monoid_pow(F.mul, F.one, c, k)) • s")),
					SplitConj(
						Case(
							"c⁻ᵏ s is a polynomial over F",
							By(power, sOver, module.SmulIn.Read(polynomialModule), field.InvIn.Read(fieldOn))),
						Case(
							"f = (c⁻ᵏ cᵏ) f = c⁻ᵏ (cᵏ f) = c⁻ᵏ (g·s) = g·(c⁻ᵏ s)",
							CalcEq(
								Leg(
									b.TermAs[Fun[Nat, A]]("F.inv(monoid_pow(F.mul, F.one, c, k)) * monoid_pow(F.mul, F.one, c, k) • f"),
									"c⁻ᵏ cᵏ is one, which scales f to itself",
									By(
										power,
										nonzero,
										fOver,
										field.MulLeftInverseOn.Read(fieldOn).AsFact().At(scalar),
										module.SmulOne.Read(polynomialModule).AsFact().At(f))),
								Leg(
									b.TermAs[Fun[Nat, A]]("F.inv(monoid_pow(F.mul, F.one, c, k)) • monoid_pow(F.mul, F.one, c, k) • f"),
									"scaling by a product is scaling twice",
									By(
										power,
										nonzero,
										fOver,
										field.InvIn.Read(fieldOn),
										module.SmulMul.Read(polynomialModule).AsFact().At(inverse, scalar, f))),
								Leg(
									b.TermAs[Fun[Nat, A]]("F.inv(monoid_pow(F.mul, F.one, c, k)) • polynomial_mul(g, s)"),
									"cᵏ f is g·s",
									By(scaled)),
								FinalLeg(
									"and the scalar passes into the product",
									By(
										power,
										nonzero,
										gOver,
										sOver,
										field.InvIn.Read(fieldOn),
										polynomial.PolynomialMulScalar.Read(ring).AsFact().At(inverse, g, s),
										polynomial.PolynomialOverDef))))))
			})
	}),
})}
