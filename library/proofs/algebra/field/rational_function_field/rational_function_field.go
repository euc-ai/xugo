// rational_function_field.go — rational functions in one variable, and the algebraic closure of K(x) for any field K.

package rational_function_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// FractionVariableTranscendental — in the fractions of the polynomials
// over a field, the variable is transcendental over the constants. A
// nonzero relation q over the constants vanishing at the fraction of X
// pulls back to a polynomial p over F. Read with constant coefficients, p
// is its own value at X (polynomial_evaluation.EvalAtVar), and taking fractions
// commutes with evaluation (polynomial_evaluation.EvalAlongHomomorphism), so the
// fraction of p is the value of q, zero. Taking fractions is injective on
// the polynomials, a domain (ring_localization.ToFractionInjective), so p
// is zero, and q with it.
var FractionVariableTranscendental = fractionVariableTranscendentalThm{family.Add(registry.ProofEntry{
	Name: "FractionVariableTranscendental",
	Key:  "prop_9aea4a1d2c77fe3f",
	Reading: "The constants are the fractions of the constant polynomials, a copy of F, the " +
		"fraction of the zero polynomial among them; the variable is the fraction of basis_vector(1).",
	Build: family.Sections(Statement{
		Binders: "∀F:field_on(A).",
		Conclusion: "¬algebraic_over(fraction_field_record(«polynomialsOverF»), " +
			"    image(λa:A. «fractionOf»(a • basis_vector(F.zero, F.one, 0)), F.carrier), " +
			"    «fractionOf»(basis_vector(F.zero, F.one, 1)))",
		Abbrev: Abbrev{
			{Name: "polynomialsOverF", Text: "polynomial_ring(field_ring(F))"},
			{Name: "fractionOf", Text: "to_fraction(«polynomialsOverF».mul, " +
				"    «polynomialsOverF».one, " +
				"    «polynomialsOverF».carrier, " +
				"    «polynomialsOverF».carrier ∖ {«polynomialsOverF».zero})"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// A polynomial over the image of c pulls back to one over c: a
		// preimage for each coefficient, zero over zero, so the support
		// stays finite.
		pullbackCoefficients := ctx.Lemma(Statement{
			Binders:    "∀zero:A. ∀z:B. ∀c:set(A). ∀f:(A → B). ∀q:(num → B).",
			Hypotheses: []string{"zero ∈ c", "f(zero) = z", "polynomial_over(z, image(f, c), q)"},
			Conclusion: "∃p:(num → A). polynomial_over(zero, c, p) ∧ (∀i:num. f(p(i)) = q(i))",
		}, func(
			a *Argument,
			zero *Expr[A],
			z *Expr[B],
			c *Expr[Set[A]],
			f *Arrow[A, B],
			q *Arrow[Nat, B],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"zero belongs to c",
				"f preserves zero",
				"q has coefficients in the image")
			definition := a.Conjuncts(
				a.Unfolded(given[2], polynomial.PolynomialOverDef),
				"q has a finite support bound",
				"each coefficient is an image")
			preimages := a.Have(
				"each coefficient has a preimage, choosing zero above zero",
				"∀i:num. ∃a:A. a ∈ c ∧ f(a) = q(i) ∧ (q(i) = z ⇒ a = zero)",
				By(definition[1], given[1], given[0], At(set_basic.InImage, f, c)))
			p, chosen := a.ObtainAs[Fun[Nat, A]](
				"choose all coefficient preimages together",
				"∃p:(num → A). ∀i:num. p(i) ∈ c ∧ f(p(i)) = q(i) ∧ (q(i) = z ⇒ p(i) = zero)",
				By(preimages))
			n, qVec := a.UnpackAs[Nat](definition[0], "n")
			pVec := a.Have(
				"the chosen preimages vanish past the support of q",
				"vec⟨n⟩(zero, p)",
				By(
					Normalized,
					chosen,
					qVec,
					vec_space.VecDef.At(z, a.VecAt[B](n, "q")),
					vec_space.VecDef.At(zero, a.VecAt[A](n, "p"))))
			a.Take(p)
			a.Show(
				"the chosen coefficients form the required polynomial",
				By(Normalized, chosen, pVec, polynomial.PolynomialOverDef.At(zero, c, p)))
		})
		return ctx.Theorem(headline, func(a *Argument, F field.FieldFact[on.F]) {
			fieldRing := field.RingOn.Read(F)
			c, cDef := a.LetAs[Fun[A, Fun[Nat, A]]]("c", "λa:A. a • basis_vector(F.zero, F.one, 0)")
			j, jDef := a.LetAs[Fun[Fun[Nat, A], Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]]("j", "«fractionOf»")
			P, pDef := a.LetAs[comm_ring.RingOps[Fun[Nat, A]]]("P", "«polynomialsOverF»")
			_, qDef := a.LetAs[FieldOps[Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]]("Q", "fraction_field_record(P)")
			e, eDef := a.LetAs[Fun[A, Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]]("e", "λa:A. j(c(a))")
			X, variableDef := a.LetAs[Fun[Nat, A]]("X", "basis_vector(F.zero, F.one, 1)")
			domain := a.Have(
				"the polynomials over F form an integral domain",
				"integral_domain_on(P)",
				By(Normalized, polynomial.PolynomialDomain.Read(integral_domain.FieldIntegralDomain.Read(F)), pDef))
			fractionMap := a.Have(
				"the fraction map j is a ring homomorphism",
				"ring_homomorphism(P, field_ring(Q), j)",
				Simp(
					Fwd(qDef),
					Fwd(ring_localization.FractionFieldRecordDef),
					Fwd(field.FieldRingDef),
					Fwd(ring_localization.FractionFieldDef)),
				By(
					ring_localization.NonzeroMultiplicative.Read(domain),
					jDef,
					ring_localization.ToFractionHomomorphism.Read(integral_domain.Ring.Read(domain)).At(
						a.TermAs[Set[Fun[Nat, A]]]("P.carrier ∖ {P.zero}"))))
			fractionInjective := a.Have(
				"the fraction map is injective",
				"injective_on(P.carrier, j)",
				By(Normalized, ring_localization.ToFractionInjective.Read(domain), jDef))
			constantPolynomials := a.Have(
				"the constant polynomials embed F in P",
				"ring_homomorphism(field_ring(F), P, c)",
				By(cDef, pDef, polynomial.ConstantPolynomialHomomorphism.Read(fieldRing)))
			zeroPolynomial := a.Have(
				"the constant zero is the zero polynomial",
				"c(F.zero) = P.zero",
				By(ring_homomorphism.MapZero.Read(constantPolynomials)))
			eZero := a.Have(
				"the embedded constant zero is zero in Q",
				"e(F.zero) = Q.zero",
				Simp(Fwd(eDef), Fwd(zeroPolynomial)),
				By(Normalized, ring_homomorphism.MapZero.Read(fractionMap)))
			variablePolynomial := a.Have(
				"the variable X is a polynomial",
				"X ∈ P.carrier",
				Simp(Fwd(variableDef), Fwd(pDef), Fwd(polynomial.PolynomialRingDef), Fwd(field.FieldRingDef)),
				BySets(polynomial.BasisVectorOver.Read(fieldRing).At(a.TermAs[Nat]("1"))))
			notTranscendental := a.SupposeNot()
			relation := a.Unfolded(notTranscendental, algebraic_element.AlgebraicOverDef)
			q, qFacts := a.ObtainAs[Fun[Nat, Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]](
				"take a nonzero polynomial relation over the constants",
				"∃q:(num → set(prod(num → A, num → A))). "+
					"    polynomial_over(image(e, F.carrier), q) ∧ "+
					"    q ≠ vec_zero(Q.zero) ∧ "+
					"    polynomial_eval(q, j(X)) = Q.zero",
				By(relation))
			qParts := a.Conjuncts(
				qFacts,
				"q has coefficients among the constants",
				"q is nonzero",
				"q vanishes at the fraction of X")
			p, pFacts := a.ObtainAs[Fun[Nat, A]](
				"pull the coefficients back to F",
				"∃p:(num → A). polynomial_over(F.carrier, p) ∧ (∀i:num. e(p(i)) = q(i))",
				By(
					comm_ring.ZeroIn.Read(fieldRing),
					eZero,
					qParts[0],
					At(
						pullbackCoefficients,
						a.TermAs[A]("F.zero"),
						a.TermAs[Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]("Q.zero"),
						a.TermAs[Set[A]]("F.carrier"),
						e,
						q)))
			pParts := a.Conjuncts(
				pFacts,
				"p is a polynomial over F",
				"its embedded coefficients are those of q")
			r, rDef := a.LetAs[Fun[Nat, Fun[Nat, A]]]("r", "λi:num. c(p(i))")
			rOver := a.Have(
				"the constant polynomial lifts of p form a polynomial over P",
				"polynomial_over(P.carrier, r)",
				By(
					Normalized,
					ring_homomorphism.MapIn.Read(constantPolynomials),
					zeroPolynomial,
					rDef,
					pParts[0],
					polynomial.PolynomialOverMap.At(
						c,
						a.TermAs[A]("F.zero"),
						a.TermAs[Fun[Nat, A]]("P.zero"),
						a.TermAs[Set[A]]("F.carrier"),
						a.TermAs[Set[Fun[Nat, A]]]("P.carrier"),
						p)))
			evaluatesToP := a.Have(
				"evaluation of those coefficients at X recovers p",
				"polynomial_eval(r, X) = p",
				Simp(Fwd(rDef), Fwd(cDef), Fwd(pDef), Fwd(polynomial.PolynomialRingDef), Fwd(field.FieldRingDef)),
				By(variableDef, pParts[0], polynomial_evaluation.EvalAtVar.Read(fieldRing).At(p)))
			mappedCoefficients := a.Have(
				"mapping the lifted coefficient sequence to fractions gives q",
				"(λi:num. j(r(i))) = q",
				Simp(Fwd(rDef)),
				Funext(),
				By(Normalized, pParts[1], eDef))
			mappedValue := a.Have(
				"evaluation commutes with the fraction map",
				"j(p) = polynomial_eval(q, j(X))",
				By(
					Normalized,
					evaluatesToP,
					mappedCoefficients,
					variablePolynomial,
					rOver,
					fractionMap,
					polynomial_evaluation.EvalAlongHomomorphism.At(
						P, a.TermAs[comm_ring.RingOps[Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]]("field_ring(Q)"), j, r, X)))
			pIn := a.Have(
				"p lies in P's carrier",
				"p ∈ P.carrier",
				Simp(Fwd(pDef), Fwd(polynomial.PolynomialRingDef), Fwd(field.FieldRingDef)),
				BySets(pParts[0]))
			pZero := a.Have(
				"injectivity forces p to be the zero polynomial",
				"p = P.zero",
				By(
					Normalized,
					comm_ring.ZeroIn.Read(integral_domain.Ring.Read(domain)),
					ring_homomorphism.MapZero.Read(fractionMap),
					mappedValue,
					qParts[2],
					fractionInjective,
					pIn,
					functions.InjectiveOnDef.At(a.TermAs[Set[Fun[Nat, A]]]("P.carrier"), j)))
			pZeroVector := a.Simplified(
				pZero,
				Fwd(pDef),
				Fwd(polynomial.PolynomialRingDef),
				Fwd(field.FieldRingDef))
			coefficientsZero := a.Simplified(pParts[1], Fwd(pZeroVector), Fwd(vec_space.VecZeroDef), Fwd(eZero))
			qZero := a.Have(
				"every coefficient of q is zero",
				"q = vec_zero(Q.zero)",
				By(
					Normalized,
					coefficientsZero,
					vec_space.VecZeroDef.Inst[Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]().At(
						a.TermAs[Set[Prod[Fun[Nat, A], Fun[Nat, A]]]]("Q.zero"))))
			a.Show(
				"this contradicts the nonzero relation",
				By(Normalized, qParts[1], qZero))
		})
	}),
})}

type (
	// _Polynomial is a polynomial over a field on A, its sequence of coefficients.
	_Polynomial = Fun[Nat, A]
	// _Fraction is a rational function over a field on A, a class of pairs of polynomials.
	_Fraction = Set[Prod[_Polynomial, _Polynomial]]
	// _ClosurePoint is a point of the algebraic closure's host over those rational functions.
	_ClosurePoint = Set[Prod[Nat, Fun[Nat, _Fraction]]]
)

// FunctionFieldClosure — every field K embeds, by a ring homomorphism ι,
// into an algebraically closed field M holding a point t transcendental
// over the image of K: the algebraic closure of the rational functions
// K(x). The polynomials P over K are a domain, whose fractions Q are a
// field holding the constant fractions C, a ring image of K, and the
// fraction x of the variable, transcendental over C
// (FractionVariableTranscendental). The closure M of Q extends its
// transport T into the host (algebraic_closure.AlgebraicClosureInHost), so
// K enters M as a ring through Q, T and the inclusion of T in M: that
// composite is ι, and its image is the transport of C. The transport of x
// stays transcendental over it in T
// (algebraic_closure.AlgebraicOverTransport) and in M
// (algebraic_closure.FieldExtendsEval).
var FunctionFieldClosure = functionFieldClosureThm{family.Add(registry.ProofEntry{
	Name: "FunctionFieldClosure",
	Key:  "prop_916cc4b94f519ff2",
	Reading: "The type of M is the closure host over the type of the " +
		"fractions of polynomials over K; nothing reads it but the binder.",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A).",
		Conclusion: "∃M:field_ops(set(prod(num, num → set(prod(num → A, num → A))))). " +
			"∃ι:(A → set(prod(num, num → set(prod(num → A, num → A))))). " +
			"∃t:set(prod(num, num → set(prod(num → A, num → A)))). " +
			"    field_on(M) ∧ " +
			"    algebraically_closed_field(M) ∧ " +
			"    ring_homomorphism(field_ring(K), field_ring(M), ι) ∧ " +
			"    t ∈ M.carrier ∧ " +
			"    ¬algebraic_over(M, image(ι, K.carrier), t)",
	}, func(a *Argument, K field.FieldFact[on.K]) {
		c, cDef := a.LetAs[Fun[A, _Polynomial]]("c", "λa:A. a • basis_vector(K.zero, K.one, 0)")
		P, pDef := a.LetAs[comm_ring.RingOps[_Polynomial]]("P", "polynomial_ring(field_ring(K))")
		Q, qDef := a.LetAs[FieldOps[_Fraction]]("Q", "fraction_field_record(P)")
		j, jDef := a.LetAs[Fun[_Polynomial, _Fraction]]("j", "to_fraction(P.carrier, P.carrier ∖ {P.zero})")
		e, eDef := a.LetAs[Fun[A, _Fraction]]("e", "λa:A. j(c(a))")
		C, constantsDef := a.LetAs[Set[_Fraction]]("C", "image(e, K.carrier)")
		X, variableDef := a.LetAs[_Polynomial]("X", "basis_vector(K.zero, K.one, 1)")
		x, xDef := a.LetAs[_Fraction]("x", "j(X)")
		// σ is the encoding a ↦ {(0, λn. a)} of Q into the host, the one
		// algebraic_closure.AlgebraicClosureInHost's statement uses.
		σ, sigmaDef := a.LetAs[Fun[_Fraction, _ClosurePoint]](
			"σ", "λa:set(prod(num → A, num → A)). {(0, λn:num. a)}")
		kRing := a.TermAs[comm_ring.RingOps[A]]("field_ring(K)")
		qRing := a.TermAs[comm_ring.RingOps[_Fraction]]("field_ring(Q)")
		fieldRing := field.RingOn.Read(K)

		rational := a.Conjuncts(
			a.Have(
				"Q is a field holding the constants, a ring image of K, and the variable",
				"field_on(Q) ∧ ring_homomorphism(field_ring(K), field_ring(Q), e) ∧ C ⊆ Q.carrier ∧ x ∈ Q.carrier",
				Derive(func(b *Argument) {
					domain := b.Have(
						"the polynomials over K form an integral domain",
						"integral_domain_on(P)",
						By(Normalized, integral_domain.FieldIntegralDomain.Read(K), pDef, polynomial.PolynomialDomain))
					fractions := b.Have(
						"the fractions Q of P form a field",
						"field_on(Q)",
						By(Normalized, ring_localization.FractionField.Read(domain), qDef))
					fractionMap := b.Have(
						"the fraction map j is a ring homomorphism",
						"ring_homomorphism(P, field_ring(Q), j)",
						Simp(
							Fwd(qDef),
							Fwd(ring_localization.FractionFieldRecordDef),
							Fwd(ring_localization.FractionFieldDef),
							Fwd(field.FieldRingDef)),
						By(
							ring_localization.NonzeroMultiplicative.Read(domain),
							jDef,
							ring_localization.ToFractionHomomorphism.Read(integral_domain.Ring.Read(domain)).At(
								b.TermAs[Set[_Polynomial]]("P.carrier ∖ {P.zero}"))))
					constantPolynomials := b.Have(
						"the constant polynomials embed K in P",
						"ring_homomorphism(field_ring(K), P, c)",
						By(cDef, pDef, polynomial.ConstantPolynomialHomomorphism.Read(fieldRing)))
					constantFractions := b.Have(
						"the constant fractions embed K in Q",
						"ring_homomorphism(field_ring(K), field_ring(Q), e)",
						By(
							Normalized,
							eDef,
							constantPolynomials,
							fractionMap,
							ring_homomorphism.RingHomCompose.At(kRing, P, qRing, c, j)))
					variablePolynomial := b.Have(
						"the variable X is a polynomial",
						"X ∈ P.carrier",
						Simp(Fwd(variableDef), Fwd(pDef), Fwd(polynomial.PolynomialRingDef), Fwd(field.FieldRingDef)),
						BySets(polynomial.BasisVectorOver.Read(fieldRing).At(b.TermAs[Nat]("1"))))
					b.Show(
						"Q is a field into which e embeds K, and j carries X into it",
						SplitConjAll(
							Case(
								"Q is a field",
								By(fractions)),
							Case(
								"K enters Q along e",
								By(constantFractions)),
							Case(
								"e carries K into Q",
								BySets(ring_homomorphism.MapIn.Read(constantFractions), constantsDef)),
							Case(
								"j carries the polynomial X into Q",
								By(
									Normalized,
									xDef,
									variablePolynomial,
									ring_homomorphism.MapIn.Read(fractionMap).AsFact().At(X)))))
				})),
			"Q is a field",
			"the constant fractions embed K in Q",
			"the constants lie in Q",
			"the variable lies in Q")
		fractions, constantFractions, constantsInQ, variableFraction :=
			rational[0], rational[1], rational[2], rational[3]

		// The definitions unfold in four staged Simps: a single stage unfolding all
		// seven overruns the replay's divergence-whistle budget for one stage.
		transcendental := a.Have(
			"x is transcendental over C",
			"¬algebraic_over(Q, C, x)",
			Simp(Fwd(qDef), Fwd(constantsDef), Fwd(xDef)),
			Simp(Fwd(eDef), Fwd(variableDef)),
			Simp(Fwd(cDef), Fwd(jDef)),
			Simp(Fwd(pDef)),
			By(FractionVariableTranscendental.Read(K)))

		M, closure := a.UnpackAs[FieldOps[_ClosurePoint]](
			algebraic_closure.AlgebraicClosureInHost.Read(fractions), "M")
		T, transportDef := a.LetAs[FieldOps[_ClosurePoint]]("T", "transport_field(σ, Q)")
		ι := a.TermAs[Fun[A, _ClosurePoint]]("λa:A. σ(e(a))")
		a.Take(M)
		a.Take(ι)
		a.Take(a.TermAs[_ClosurePoint]("σ(x)"))
		k, kDef := a.LetAs[Set[_ClosurePoint]]("k", "image(σ, C)")
		t, tDef := a.LetAs[_ClosurePoint]("t", "σ(x)")
		closureFacts := a.Simplified(closure, Rev(sigmaDef), Rev(transportDef))
		// Folded, the closure's statement is a prenex ∀ over its clauses; read at t it is their conjunction.
		closed := a.Conjuncts(
			a.Have(
				"the algebraic closure is a closed field extending T",
				"field_on(M) ∧ algebraically_closed_field(M) ∧ field_extends(T, M)",
				By(closureFacts.At(t))),
			"M is a field",
			"M is algebraically closed",
			"M extends T")
		tRing := a.TermAs[comm_ring.RingOps[_ClosurePoint]]("field_ring(T)")
		mRing := a.TermAs[comm_ring.RingOps[_ClosurePoint]]("field_ring(M)")
		embedding := a.Conjuncts(
			a.Have(
				"σ is injective on Q, so its transport T is a field, and σ carries Q into M as rings",
				"injective_on(Q.carrier, σ) ∧ field_on(T) ∧ ring_homomorphism(field_ring(Q), field_ring(M), σ)",
				Derive(func(b *Argument) {
					encodingInjective := b.Have(
						"the closure encoding is injective",
						"injective_on(Q.carrier, σ)",
						Simp(Fwd(sigmaDef)),
						By(algebraic_closure.ClosureEmbeddingInjective.At(b.TermAs[Set[_Fraction]]("Q.carrier"))))
					transported := b.Have(
						"the transported rational-function field is a field",
						"field_on(T)",
						By(
							Normalized,
							transportDef,
							encodingInjective,
							ring_transport.TransportFieldOn.Read(fractions).AsFact().At(σ)))
					transportHom := b.Have(
						"transport keeps the ring operations of Q",
						"ring_homomorphism(field_ring(Q), field_ring(T), σ)",
						By(
							Normalized,
							fractions,
							transportDef,
							encodingInjective,
							ring_transport.TransportFieldHomomorphism.At(σ, Q)))
					inclusion := b.Have(
						"M extends T, so including T in M keeps the ring operations",
						"ring_homomorphism(field_ring(T), field_ring(M), λy. y)",
						By(transported, closed[0], closed[2], At(algebraic_closure.FieldExtendsHomomorphism, T, M)))
					b.Show(
						"σ is injective, T a field, and σ followed by the inclusion carries Q into M",
						SplitConjAll(
							Case(
								"a singleton code determines its point",
								By(encodingInjective)),
							Case(
								"T is a field",
								By(transported)),
							Case(
								"compose the transport with the inclusion",
								By(
									transportHom,
									inclusion,
									ring_homomorphism.RingHomCompose.At(
										qRing, tRing, mRing, σ, b.TermAs[Fun[_ClosurePoint, _ClosurePoint]]("λy. y"))))))
				})),
			"σ is injective on Q",
			"T is a field",
			"σ carries Q into M as rings")
		encodingInjective, transported, transportIntoM := embedding[0], embedding[1], embedding[2]
		intoM := a.Have(
			"K enters M through Q",
			"ring_homomorphism(field_ring(K), field_ring(M), λa:A. σ(e(a)))",
			By(
				constantFractions,
				transportIntoM,
				ring_homomorphism.RingHomCompose.At(kRing, qRing, mRing, e, σ)))
		sameImage := a.Have(
			"the image of K through e then σ is the image of C under σ",
			"image(λa:A. σ(e(a)), K.carrier) = k",
			Simp(Fwd(kDef), Fwd(constantsDef), Rev(set_image.ImageCompose)),
			Simp(Fwd(functions.ComposeApply)),
			Basic())
		pointInM := a.Have(
			"t lies in M, transcendental over k",
			"t ∈ M.carrier ∧ ¬algebraic_over(M, k, t)",
			Derive(func(b *Argument) {
				transportCarrier := b.Have(
					"the carrier of T is the image of Q",
					"T.carrier = image(σ, Q.carrier)",
					Simp(Fwd(transportDef), Fwd(ring_transport.TransportFieldDef)),
					Refl())
				transportedPoints := b.Have(
					"k and t lie in the transported field",
					"k ⊆ T.carrier ∧ t ∈ T.carrier",
					Simp(Fwd(kDef), Fwd(transportCarrier), Fwd(tDef)),
					BySets(constantsInQ, variableFraction))
				transportedTranscendental := b.Have(
					"t stays transcendental over k in T",
					"¬algebraic_over(T, k, t)",
					Simp(Fwd(transportDef), Fwd(kDef), Fwd(tDef)),
					By(
						encodingInjective,
						constantsInQ,
						variableFraction,
						transcendental,
						algebraic_closure.AlgebraicOverTransport.Read(fractions).AsFact().At(σ, C, x)))
				b.Show(
					"σ carries x into M, and M evaluates polynomials over k at t as T does",
					SplitConj(
						Case(
							"σ carries x into M",
							By(
								Normalized,
								tDef,
								variableFraction,
								ring_homomorphism.MapIn.Read(transportIntoM).AsFact().At(x))),
						Case(
							"M extends T, which holds k and t",
							By(
								closed[2],
								transportedPoints,
								transportedTranscendental,
								algebraic_closure.FieldExtendsEval.Read(transported).AsFact().At(M, k, t)))))
			}))
		a.Show(
			"M is a closed field which K enters along ι, holding t transcendental over the image k",
			sameImage.Rw(),
			By(closed[0], closed[1], intoM, pointInM))
	}),
})}
