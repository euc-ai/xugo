// generic.go — the generic point of a smooth projective equation curve: a
// point of a field with the ideal as its vanishing forms has one
// transcendental coordinate with the rest algebraic over it, the curve has
// such a point in an algebraically closed field holding a transcendental,
// and its field is a regular function field over k.

package projective_generic_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/perfect_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// _Polynomial is a polynomial in the variables num with coefficients in A:
// its coefficient at each exponent vector.
type _Polynomial = Fun[Fun[Nat, Nat], A]

// _Fraction is a member of the fraction field of a quotient of the
// polynomials: a class of pairs of cosets.
type _Fraction = Set[Prod[Set[_Polynomial], Set[_Polynomial]]]

// TranscendenceAtGenericPoint — a point y of a field L, read along a
// coefficient map σ from k, with y(j) = one and the forms vanishing at it
// exactly the ideal of E, has a coordinate transcendental over σ(k) over
// which every coordinate is algebraic, when the Hilbert function of E over
// k is eventually linear of positive slope. Were every coordinate algebraic
// over σ(k), h would be bounded by [σ(k)(y) : σ(k)] (projective_curve.AlgebraicCoordinatesBound);
// were some y(b) transcendental over σ(k)(y(a)), h(d) would grow faster than
// e·d (projective_curve.TranscendentalPairBound). Both contradict h(d) + g = e·d + 1.
var TranscendenceAtGenericPoint = transcendenceAtGenericPointThm{family.Add(registry.ProofEntry{
	Name: "TranscendenceAtGenericPoint",
	Key:  "prop_8d44bc77632a37e4",
	Reading: "Stated along a coefficient map σ so that it reads at the fraction field of M[X] " +
		"modulo the ideal, where GenericPointExists needs it before any point lies in M; at σ the " +
		"identity and L = M it is the generic field's own transcendence. The coordinates up to n " +
		"must lie in L's carrier, and y(j) = one fixes the scaling the generic clause is read at.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀L:field_on(B). " +
			"∀k:set(A). " +
			"∀n:num. " +
			"∀E:set((num → num) → A). " +
			"∀σ:(A → B). " +
			"∀y:(num → B).",
		Hypotheses: []string{
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀i:num. i ≤ n ⇒ y(i) ∈ L.carrier",
			"∃j:num. j ≤ n ∧ y(j) = L.one",
			"∀P:((num → num) → A). " +
				"    (∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)) ⇒ " +
				"    (polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero ⇔ " +
				"        P ∈ ideal_span(«polynomials», E))",
			"∃g e N:num. " +
				"    0 < e ∧ " +
				"    (∀d:num. N ≤ d ⇒ projective_hilbert_function(field_ring(M), k, n, E, d) + g = e * d + 1)",
		},
		Conclusion: "∃a:num. " +
			"    a ≤ n ∧ " +
			"    ¬algebraic_over(L, image(σ, k), y(a)) ∧ " +
			"    (∀i:num. i ≤ n ⇒ algebraic_over(L, field_adjoin(L, image(σ, k), {y(a)}), y(i)))",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			kSubfield, coefficientMap, coordinates, normalized, generic, linearGrowth Fact,
		) {
			m, l := arg.TermAs[FieldOps[A]]("M"), arg.TermAs[FieldOps[B]]("L")
			j, scaled := arg.UnpackAs[Nat](normalized, "j")
			scaling := arg.Conjuncts(
				scaled,
				"j is a coordinate index",
				"y(j) is one")
			_, e, _, growth := arg.Unpack3As[Nat, Nat, Nat](linearGrowth, "g", "e", "N")
			slope := arg.Conjuncts(
				growth,
				"the slope e is positive",
				"h(d) + g = e·d + 1 from N on")
			degreewise := arg.Have(
				"a form of each degree vanishes at y exactly when it lies in the ideal",
				Statement{
					Binders: "∀d:num. ∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					},
					Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero ⇔ " +
						"P ∈ ideal_span(«polynomials», E)",
				},
				By(generic))
			a, transcendental := arg.ObtainAs[Nat](
				"some coordinate is transcendental over σ(k): else the Hilbert function would be bounded",
				"∃a:num. a ≤ n ∧ ¬algebraic_over(L, image(σ, k), y(a))",
				Derive(func(h *Argument) {
					allAlgebraic := h.SupposeNot()
					_, degreeDef := h.LetAs[Nat](
						"D", "extension_degree(L, image(σ, k), field_adjoin(L, image(σ, k), {y(i) | i:num | i ≤ n}))")
					degree := h.TermAs[Nat]("N + D + g")
					bounded := h.Have(
						"the degree N + D + g is past N and makes e·(N + D + g) "+
							"+ 1 − g exceed D: there the Hilbert function is at most D",
						"projective_hilbert_function(field_ring(M), k, n, E, N + D + g) ≤ D",
						By(
							M,
							L,
							allAlgebraic,
							coordinates,
							degreeDef,
							kSubfield,
							coefficientMap,
							degreewise.At(degree),
							projective_curve.AlgebraicCoordinatesBound.At(m, l, k, n, degree, E, σ, y)))
					h.Show(
						"while there it is e·(N + D + g) + 1 − g, more than D",
						ByArith(slope[1].At(degree), slope[0], bounded, nat_order.LessEqMulNonzero.At(degree, e)))
				}),
				Named("a"))
			arg.Take(a)
			algebraicOverIt := arg.Have(
				"every coordinate is algebraic over σ(k)(y(a)): else h(d) would outgrow e·d",
				"∀i:num. i ≤ n ⇒ algebraic_over(L, field_adjoin(L, image(σ, k), {y(a)}), y(i))",
				Derive(func(h *Argument) {
					i := h.FixAs[Nat]("i")
					iIn := h.Assume()
					transcendentalOverIt := h.SupposeNot()
					degree := h.TermAs[Nat]("N + e * e + e")
					topExponent := h.TermAs[Nat]("N + e * e")
					lower := h.Have(
						"p = N + e² puts p + e past N and above e² − g: at the degree p + "+
							"e the (p + 1)(e + 1) products y(a)^s·y(i)^t are independent values",
						"(N + e * e + 1) * (e + 1) ≤ projective_hilbert_function(field_ring(M), k, n, E, N + e * e + e)",
						By(
							M,
							L,
							transcendentalOverIt,
							transcendental,
							coordinates,
							iIn,
							scaling[0],
							scaling[1],
							kSubfield,
							coefficientMap,
							degreewise.At(degree),
							nat_order.LessEqRefl.At(degree),
							projective_curve.TranscendentalPairBound.At(m, l, k, n, degree, E, σ, y, j, a, i, topExponent, e)))
					h.Show(
						"while there it is e·(p + e) + 1 − g, fewer than (p + 1)(e + 1)",
						ByArith(slope[1].At(degree), slope[0], lower))
				}))
			arg.Show(
				"y(a) is transcendental over σ(k) and every coordinate algebraic over σ(k)(y(a))",
				By(transcendental, algebraicOverIt))
		}),
})}

// PrimeIdealGenericPoint — a prime ideal p of the polynomials over R in the
// variables 0, …, n that misses Xⱼ has a generic point in the fraction field
// L of the quotient, normalized at j: the classes y(i) = [Xᵢ]/[Xⱼ], at which
// a form vanishes exactly when it lies in p. A form P of degree d takes
// there [Xⱼ]^(−d) times the fraction of its class (homogeneous_polynomial.FormScaling), and the
// class of P is zero exactly when P ∈ p.
var PrimeIdealGenericPoint = primeIdealGenericPointThm{family.Add(registry.ProofEntry{
	Name: "PrimeIdealGenericPoint",
	Key:  "prop_8a0530715039d6ca",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀n j:num. ∀p:set((num → num) → A).",
		Hypotheses: []string{
			"prime_ideal(«polynomialRing», p)",
			"j ≤ n",
			"polynomial_algebra_var(R, j) ∉ p",
		},
		Conclusion: "field_on(«fractions») ∧ " +
			"(∃σ:(A → set(prod(set((num → num) → A), set((num → num) → A)))). " +
			"∃y:(num → set(prod(set((num → num) → A), set((num → num) → A)))). " +
			"    ring_homomorphism(R, field_ring(«fractions»), σ) ∧ " +
			"    (∀i:num. y(i) ∈ «fractions».carrier) ∧ " +
			"    y(j) = «fractions».one ∧ " +
			"    (∀i:num. i ≤ n ⇒ (y(i) = «fractions».zero ⇔ polynomial_algebra_var(R, i) ∈ p)) ∧ " +
			"    (∀i:num. n < i ⇒ y(i) = «fractions».zero) ∧ " +
			"    (∀P:((num → num) → A). " +
			"        (∃d:num. homogeneous_polynomial(R, n, d, P)) ⇒ " +
			"        (polynomial_algebra_eval(R, field_ring(«fractions»), σ, y, P) = «fractions».zero ⇔ " +
			"            P ∈ p)))",
		Abbrev: Abbrev{
			{Name: "polynomialRing", Text: "polynomial_algebra_ring(R, {i:num | i ≤ n})"},
			{Name: "fractions", Text: "fraction_field_record(ideal_quotient_ring(«polynomialRing», p))"},
		},
	},
		func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			n, j *Expr[Nat],
			p *Expr[Set[_Polynomial]],
			prime, jIndex, jOutside Fact,
		) {
			coefficients := a.TermAs[RingOps[A]]("R")
			polynomials := a.TermAs[RingOps[_Polynomial]]("«polynomialRing»")
			quotient := a.TermAs[RingOps[Set[_Polynomial]]]("ideal_quotient_ring(«polynomialRing», p)")
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			structure := a.Conjuncts(
				a.Have(
					"the polynomials over R are a commutative ring with p an ideal of it",
					"comm_ring_on(«polynomialRing») ∧ ring_ideal(«polynomialRing», p)",
					By(R, prime, polynomial_algebra.PolynomialAlgebraCommRingOn, ring_ideal.PrimeIdealIdeal)),
				"the polynomials are a commutative ring",
				"p is an ideal of it")
			polynomialRing, ideal := structure[0], structure[1]
			domain := a.Have(
				"the quotient by the prime ideal p is an integral domain",
				"integral_domain_on(ideal_quotient_ring(«polynomialRing», p))",
				By(quotient_ring.QuotientDomain.Read(polynomialRing), prime))
			fractions := a.Have(
				"so its fractions form a field",
				"field_on(«fractions»)",
				By(ring_localization.FractionField.Read(domain)))
			_, lDef := a.LetAs[FieldOps[_Fraction]]("L", "«fractions»")
			ringL := a.TermAs[RingOps[_Fraction]]("field_ring(L)")
			projection := a.Have(
				"the projection onto the quotient is a ring homomorphism",
				"ring_homomorphism(«polynomialRing», "+
					"    ideal_quotient_ring(«polynomialRing», p), "+
					"    ideal_quotient_projection(«polynomialRing», p))",
				By(ideal, quotient_ring.IdealQuotientProjection.Read(polynomialRing).At(p)))
			ι, ιDef := a.LetAs[Fun[Set[_Polynomial], _Fraction]](
				"ι",
				"to_fraction(ideal_quotient_ring(«polynomialRing», p).mul, "+
					"    ideal_quotient_ring(«polynomialRing», p).one, "+
					"    ideal_quotient_ring(«polynomialRing», p).carrier, "+
					"    ideal_quotient_ring(«polynomialRing», p).carrier ∖ "+
					"    {ideal_quotient_ring(«polynomialRing», p).zero})")
			inclusion := a.Have(
				"ι, a class to its fraction over one, is a ring homomorphism into L",
				"ring_homomorphism(ideal_quotient_ring(«polynomialRing», p), field_ring(L), ι)",
				Simp(
					Fwd(lDef),
					Fwd(ιDef),
					Fwd(ring_localization.FractionFieldRecordDef),
					Fwd(field.FieldRingDef),
					Fwd(ring_localization.FractionFieldDef)),
				By(
					ring_localization.NonzeroMultiplicative.Read(domain),
					ring_localization.ToFractionHomomorphism.Read(integral_domain.Ring.Read(domain)).At(
						a.TermAs[Set[Set[_Polynomial]]](
							"ideal_quotient_ring(«polynomialRing», p).carrier ∖ "+
								"{ideal_quotient_ring(«polynomialRing», p).zero}"))))
			ψ, ψDef := a.LetAs[Fun[_Polynomial, _Fraction]](
				"ψ", "λP:((num → num) → A). ι(ideal_quotient_projection(«polynomialRing», p, P))")
			classMap := a.Have(
				"ψ, a polynomial to the fraction of its class, is a ring homomorphism into L",
				"ring_homomorphism(«polynomialRing», field_ring(L), ψ)",
				By(
					ψDef,
					inclusion,
					projection,
					ring_homomorphism.RingHomCompose.At(
						polynomials,
						quotient,
						ringL,
						a.TermAs[Fun[_Polynomial, Set[_Polynomial]]]("ideal_quotient_projection(«polynomialRing», p)"),
						ι)))
			injective := a.Have(
				"ι is one-to-one on the classes",
				"injective_on(ideal_quotient_ring(«polynomialRing», p).carrier, ι)",
				Simp(Fwd(ιDef), Fwd(quotient_ring.IdealQuotientRingDef)),
				By(ring_localization.ToFractionInjective.Read(domain)))
			zeroClass := a.Have(
				"ι keeps zero",
				"ι(ideal_quotient_ring(«polynomialRing», p).zero) = L.zero",
				By(ring_homomorphism.MapZero.Read(inclusion)))
			kernel := a.Have(
				"ψ sends a polynomial to zero exactly when it lies in p",
				"∀P:((num → num) → A). P ∈ «polynomialRing».carrier ⇒ (ψ(P) = L.zero ⇔ P ∈ p)",
				Derive(func(b *Argument) {
					P := b.FixAs[_Polynomial]("P")
					isPolynomial := b.Assume()
					class := b.Have(
						"its class is zero exactly when it lies in p",
						"ideal_quotient_projection(«polynomialRing», p, P) = "+
							"ideal_quotient_ring(«polynomialRing», p).zero ⇔ "+
							"P ∈ p",
						Simp(Fwd(quotient_ring.IdealQuotientProjectionDef), Fwd(quotient_ring.IdealQuotientRingDef)),
						By(ideal, isPolynomial, quotient_ring.CosetEqIdealIff.Read(polynomialRing).AsFact().At(p, P)))
					classes := b.Have(
						"its class and zero are classes",
						"ideal_quotient_projection(«polynomialRing», p, P) ∈ "+
							"ideal_quotient_ring(«polynomialRing», p).carrier ∧ "+
							"ideal_quotient_ring(«polynomialRing», p).zero ∈ ideal_quotient_ring(«polynomialRing», p).carrier",
						By(
							comm_ring.ZeroIn.Read(integral_domain.Ring.Read(domain)),
							isPolynomial,
							ring_homomorphism.MapIn.Read(projection).AsFact().At(P)))
					separated := b.Have(
						"ι sends the class to zero only if it is zero",
						Statement{
							Hypotheses: []string{
								"ι(ideal_quotient_projection(«polynomialRing», p, P)) = " +
									"ι(ideal_quotient_ring(«polynomialRing», p).zero)",
							},
							Conclusion: "ideal_quotient_projection(«polynomialRing», p, P) = " +
								"ideal_quotient_ring(«polynomialRing», p).zero",
						},
						By(injective, classes, functions.InjectiveOnDef))
					b.Show(
						"so ψ(P) is zero exactly when P ∈ p",
						By(class, ψDef, zeroClass, separated))
				}))
			σ, σDef := a.LetAs[Fun[A, _Fraction]]("σ", "λa:A. ψ(polynomial_algebra_const(R, a))")
			constants := a.Have(
				"σ, a coefficient to the fraction of its constant, is a ring homomorphism",
				"ring_homomorphism(R, field_ring(L), σ)",
				By(
					R,
					σDef,
					classMap,
					polynomial_algebra.PolynomialAlgebraConstHom.At(coefficients, variables),
					ring_homomorphism.RingHomCompose.At(
						coefficients,
						polynomials,
						ringL,
						a.TermAs[Fun[A, _Polynomial]]("polynomial_algebra_const(R)"),
						ψ)))
			variablesIn := a.Have(
				"the variables 0, …, n are polynomials",
				"∀i:num. i ≤ n ⇒ polynomial_algebra_var(R, i) ∈ «polynomialRing».carrier",
				By(R, polynomial_algebra.PolynomialAlgebraVarIn))
			θ, θDef := a.LetAs[Fun[Nat, _Fraction]](
				"θ", "λi:num. COND(i ≤ n, ψ(polynomial_algebra_var(R, i)), L.zero)")
			classesIn := a.Have(
				"each θ(i), the fraction of the class of Xᵢ up to n and zero past it, lies in L",
				"∀i:num. θ(i) ∈ L.carrier",
				By(
					ring_homomorphism.MapIn.Read(classMap),
					comm_ring.ZeroIn.Read(field.RingOn.Read(fractions)),
					variablesIn,
					θDef))
			evaluation := a.Have(
				"evaluation along σ at θ is a ring homomorphism",
				"ring_homomorphism(«polynomialRing», "+
					"    field_ring(L), "+
					"    polynomial_algebra_eval(R, field_ring(L), σ, θ))",
				By(classesIn, constants, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
			onConstants := a.Have(
				"it agrees with ψ on the constants",
				Statement{
					Binders:    "∀a:A.",
					Hypotheses: []string{"a ∈ R.carrier"},
					Conclusion: "polynomial_algebra_eval(R, field_ring(L), σ, θ, polynomial_algebra_const(R, a)) = " +
						"ψ(polynomial_algebra_const(R, a))",
				},
				By(σDef, constants, polynomial_algebra_evaluation.PolynomialAlgebraEvalConst))
			onVariables := a.Have(
				"and on the variables 0, …, n",
				Statement{
					Binders:    "∀v:num.",
					Hypotheses: []string{"v ∈ {i:num | i ≤ n}"},
					Conclusion: "polynomial_algebra_eval(R, field_ring(L), σ, θ, polynomial_algebra_var(R, v)) = " +
						"ψ(polynomial_algebra_var(R, v))",
				},
				By(classesIn, θDef, constants, polynomial_algebra_evaluation.PolynomialAlgebraEvalVar))
			evaluationIsψ := a.Have(
				"so evaluation at θ is ψ on the polynomials",
				Statement{
					Binders:    "∀P:((num → num) → A).",
					Hypotheses: []string{"P ∈ polynomial_algebra(R, {i:num | i ≤ n})"},
					Conclusion: "polynomial_algebra_eval(R, field_ring(L), σ, θ, P) = ψ(P)",
				},
				By(
					R,
					onConstants,
					onVariables,
					classMap,
					evaluation,
					At(
						polynomial_algebra_evaluation.PolynomialAlgebraEvalUnique,
						coefficients,
						ringL,
						variables,
						a.TermAs[Fun[_Polynomial, _Fraction]]("polynomial_algebra_eval(R, field_ring(L), σ, θ)"),
						ψ)))
			θj := a.TermAs[_Fraction]("θ(j)")
			jNonzero := a.Have(
				"θ(j) is not zero: Xⱼ is not in p",
				"θ(j) ≠ L.zero",
				By(
					jOutside,
					kernel.At(a.TermAs[_Polynomial]("polynomial_algebra_var(R, j)")),
					variablesIn.At(j),
					jIndex,
					θDef))
			c, cDef := a.LetAs[_Fraction]("c", "L.inv(θ(j))")
			inverse := a.Have(
				"c, the inverse of θ(j), is a nonzero member of L",
				"c ∈ L.carrier ∧ c ≠ L.zero ∧ L.mul(θ(j), c) = L.one",
				By(
					Normalized,
					jNonzero,
					classesIn.At(j),
					cDef,
					field.InvIn.Read(fractions).AsFact().At(θj),
					field.InvEqZeroOn.Read(fractions).AsFact().At(θj),
					field.MulRightInverseOn.Read(fractions).AsFact().At(θj)))
			scaledIn := a.Have(
				"each θ(i)·c lies in L",
				"∀i:num. L.mul(θ(i), c) ∈ L.carrier",
				By(comm_ring.MulIn.Read(field.RingOn.Read(fractions)), inverse, classesIn))
			zeroAt := a.Have(
				"up to n, θ(i)·c is zero exactly when Xᵢ lies in p",
				"∀i:num. i ≤ n ⇒ (L.mul(θ(i), c) = L.zero ⇔ polynomial_algebra_var(R, i) ∈ p)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					index := b.Assume()
					b.Show(
						"c is not zero, and θ(i) is the fraction of the class of Xᵢ",
						By(
							index,
							θDef,
							inverse,
							classesIn.At(i),
							variablesIn.At(i),
							kernel.At(b.TermAs[_Polynomial]("polynomial_algebra_var(R, i)")),
							field.MulEqZeroOn.Read(fractions).AsFact().At(b.TermAs[_Fraction]("θ(i)"), c)))
				}))
			pastN := a.Have(
				"past n, θ(i)·c is zero",
				"∀i:num. n < i ⇒ L.mul(θ(i), c) = L.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					past := b.Assume()
					zero := b.Have(
						"θ(i) is zero past n",
						"θ(i) = L.zero",
						By(past, θDef, nat_order.NotLessEq.At(i, n)))
					b.Show(
						"and zero times c is zero",
						By(
							Normalized,
							zero,
							inverse,
							comm_ring.MulLeftZeroOn.Read(field.RingOn.Read(fractions)).AsFact().At(c)))
				}))
			generic := a.Have(
				"a form vanishes at θ·c exactly when it lies in p",
				Statement{
					Binders: "∀P:((num → num) → A).",
					Hypotheses: []string{
						"∃d:num. homogeneous_polynomial(R, n, d, P)",
					},
					Conclusion: "polynomial_algebra_eval(R, field_ring(L), σ, λi:num. L.mul(θ(i), c), P) = L.zero ⇔ " +
						"P ∈ p",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_Polynomial]("P")
					d, form := b.UnpackAs[Nat](b.Assume(), "d")
					scaling := b.Have(
						"P at θ·c is c^d times P at θ",
						"polynomial_algebra_eval(R, field_ring(L), σ, λi:num. L.mul(θ(i), c), P) = "+
							"L.mul(monoid_pow(L.mul, L.one, c, d), polynomial_algebra_eval(R, field_ring(L), σ, θ, P))",
						By(
							constants,
							form,
							classesIn,
							inverse,
							homogeneous_polynomial.FormScaling.At(coefficients, ringL, σ, n, d, θ, c, P)))
					isPolynomial := b.Have(
						"a form is a polynomial",
						"P ∈ polynomial_algebra(R, {i:num | i ≤ n}) ∧ P ∈ «polynomialRing».carrier",
						By(homogeneous_polynomial.FormPolynomial.Read(form)))
					power := b.Have(
						"c^d is a nonzero member of L",
						"monoid_pow(L.mul, L.one, c, d) ∈ L.carrier ∧ monoid_pow(L.mul, L.one, c, d) ≠ L.zero",
						By(
							inverse,
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(fractions))).AsFact().At(c, d),
							field.PowEqZeroOn.Read(fractions).AsFact().At(c, d)))
					b.Show(
						"so P vanishes there exactly when ψ(P) is zero, that is when P ∈ p",
						By(
							scaling,
							isPolynomial,
							power,
							kernel.At(P),
							evaluationIsψ.At(P),
							ring_homomorphism.MapIn.Read(classMap).AsFact().At(P),
							field.MulEqZeroOn.Read(fractions).AsFact().At(
								b.TermAs[_Fraction]("monoid_pow(L.mul, L.one, c, d)"),
								b.TermAs[_Fraction]("ψ(P)"))))
				}))
			a.Show(
				"L is a field, and σ with the point θ·c is the generic point of p normalized at j",
				SplitConj(
					Case(
						"L is a field",
						By(fractions)),
					Case(
						"σ with y(i) = θ(i)·c is a generic point of p, normalized at j",
						Witness(σ),
						Witness(a.TermAs[Fun[Nat, _Fraction]]("λi:num. L.mul(θ(i), c)")),
						By(constants, scaledIn, inverse, zeroAt, pastN, generic))))
		}),
})}

// CurveGenericPoint — the function field of a smooth projective equation
// curve over M, the fractions of the polynomials over M modulo the ideal
// its equations generate, holds a generic point over k: a coefficient map σ
// from k and a point y with first nonzero coordinate one at which a form
// over k vanishes exactly when it lies in the ideal over k. The point of
// the curve keeps some variable out of the ideal over M; the least such j
// normalizes the generic point of that prime ideal (PrimeIdealGenericPoint),
// and a form over k in the ideal over M lies in the ideal over k
// (IdealDescent).
var CurveGenericPoint = curveGenericPointThm{family.Add(registry.ProofEntry{
	Name: "CurveGenericPoint",
	Key:  "prop_d55d02e0dad1fa2a",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{"smooth_projective_equation_curve(M, k, n, E)"},
		Conclusion: "field_on(«functionsOfCurve») ∧ " +
			"(∃σ:(A → set(prod(set((num → num) → A), set((num → num) → A)))). " +
			"∃y:(num → set(prod(set((num → num) → A), set((num → num) → A)))). " +
			"    ring_homomorphism(«hilbertCoefficients», field_ring(«functionsOfCurve»), σ) ∧ " +
			"    (∀i:num. y(i) ∈ «functionsOfCurve».carrier) ∧ " +
			"    (∃j:num. " +
			"        j ≤ n ∧ " +
			"        y(j) = «functionsOfCurve».one ∧ " +
			"        (∀i:num. i < j ⇒ y(i) = «functionsOfCurve».zero)) ∧ " +
			"    (∀i:num. n < i ⇒ y(i) = «functionsOfCurve».zero) ∧ " +
			"    (∀P:((num → num) → A). " +
			"        (∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)) ⇒ " +
			"        (polynomial_algebra_eval(«hilbertCoefficients», " +
			"                field_ring(«functionsOfCurve»), " +
			"                σ, " +
			"                y, " +
			"                P) = " +
			"            «functionsOfCurve».zero ⇔ " +
			"            P ∈ ideal_span(«polynomials», E))))",
		Abbrev: Abbrev{
			{Name: "polynomialsOverM", Text: "polynomial_algebra_ring(field_ring(M), {i:num | i ≤ n})"},
			{Name: "functionsOfCurve", Text: "fraction_field_record( " +
				"    ideal_quotient_ring(«polynomialsOverM», ideal_span(«polynomialsOverM», E)))"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[_Polynomial]],
			curve Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			ringM := a.TermAs[RingOps[A]]("field_ring(M)")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			kSubfield := projective_curve.CurveConstantsSubfield.Read(curve)
			forms := projective_curve.CurveEquationsForms.Read(curve)
			prime := projective_curve.CurveIdealGeometricallyPrime.Read(curve)
			x, onCurve := a.UnpackAs[Fun[Nat, A]](projective_curve.CurveHasPoint.Read(curve), "x")
			point := a.Conjuncts(
				a.Unfolded(onCurve, projective_curve.ProjectiveEquationPointsDef),
				"the coordinates 0, …, n of x lie in M",
				"the rest are zero",
				"its first nonzero coordinate is one",
				"the equations vanish at it")
			overM := a.Have(
				"a form over k is a form over M, a polynomial over k and one over M",
				Statement{
					Binders:    "∀d:num. ∀P:((num → num) → A).",
					Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, P)"},
					Conclusion: "homogeneous_polynomial(field_ring(M), n, d, P) ∧ " +
						"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ " +
						"P ∈ «polynomialsOverM».carrier",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("d")
					b.FixAs[_Polynomial]("P")
					form := b.Assume()
					b.Show(
						"so P, with its degrees, is a form over M: k lies in M, so a polynomial over k is one over M",
						Simp(Fwd(homogeneous_polynomial.HomogeneousPolynomialDef)),
						BySets(
							homogeneous_polynomial.FormDegree.Read(form),
							homogeneous_polynomial.FormPolynomial.Read(form),
							field.SubfieldSubset.Read(kSubfield),
							polynomial_algebra.PolynomialAlgebraOverMono.At(ringM, k, variables)))
				}))
			atPoint := a.Have(
				"evaluation at x is a ring homomorphism",
				"ring_homomorphism(«polynomialsOverM», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(field_ring(M), field_ring(M), λa:A. a, x))",
				By(
					point[0],
					ring_homomorphism.RingHomIdentity.Read(field.RingOn.Read(M)),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
			equationsAtX := a.Have(
				"each equation is a polynomial over M vanishing at x",
				Statement{
					Binders:    "∀P:((num → num) → A).",
					Hypotheses: []string{"P ∈ E"},
					Conclusion: "P ∈ «polynomialsOverM».carrier ∧ " +
						"polynomial_algebra_eval(field_ring(M), field_ring(M), λa:A. a, x, P) = M.zero",
				},
				By(
					forms,
					point[3],
					overM,
					At(
						polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictCoefficients,
						ringM,
						k,
						ringM,
						identity,
						x)))
			idealAtX := a.Have(
				"so evaluation at x kills the ideal the equations generate over M",
				"ideal_span(«polynomialsOverM», E) ⊆ "+
					"ring_kernel(M.zero, "+
					"    «polynomialsOverM».carrier, "+
					"    polynomial_algebra_eval(field_ring(M), field_ring(M), λa:A. a, x))",
				BySets(equationsAtX, ring_homomorphism.IdealSpanInKernel.Read(atPoint).At(E)))
			missing := a.Have(
				"some variable lies outside the ideal over M: the one at which x is one",
				"∃j:num. j ≤ n ∧ polynomial_algebra_var(field_ring(M), j) ∉ ideal_span(«polynomialsOverM», E)",
				Derive(func(b *Argument) {
					j, normalized := b.UnpackAs[Nat](point[2], "j")
					scaling := b.Conjuncts(
						normalized,
						"j is a coordinate index",
						"x(j) is one",
						"the coordinates before it are zero")
					b.Take(j)
					value := b.Have(
						"Xⱼ takes the value one at x",
						"polynomial_algebra_eval(field_ring(M), "+
							"    field_ring(M), "+
							"    λa:A. a, "+
							"    x, "+
							"    polynomial_algebra_var(field_ring(M), j)) = "+
							"M.one",
						By(
							ring_homomorphism.RingHomIdentity.Read(field.RingOn.Read(M)),
							scaling[0],
							scaling[1],
							point[0].At(j),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(ringM, ringM, identity, x, j)))
					vanishing := b.Unfolded(b.Unfolded(idealAtX, ring_homomorphism.RingKernelDef), set_basic.SubsetDef)
					b.Show(
						"and one is not zero, so Xⱼ is not in the ideal",
						By(
							field.OneNotZeroOn.Read(M),
							vanishing.At(b.TermAs[_Polynomial]("polynomial_algebra_var(field_ring(M), j)")),
							scaling[0],
							value))
				}))
			j, least := a.ObtainAs[Nat](
				"take the least such j",
				"∃j:num. "+
					"    j ≤ n ∧ "+
					"    polynomial_algebra_var(field_ring(M), j) ∉ ideal_span(«polynomialsOverM», E) ∧ "+
					"    (∀m:num. "+
					"        m < j ⇒ "+
					"        ¬(m ≤ n ∧ polynomial_algebra_var(field_ring(M), m) ∉ ideal_span(«polynomialsOverM», E)))",
				By(
					missing,
					nat_order.WellOrdering.At(a.TermAs[Set[Nat]](
						"λj:num. j ≤ n ∧ polynomial_algebra_var(field_ring(M), j) ∉ ideal_span(«polynomialsOverM», E)"))),
				Named("j"))
			minimal := a.Conjuncts(
				least,
				"j is a coordinate index",
				"Xⱼ lies outside the ideal over M",
				"the variables before it lie inside")
			normalizedPoint := a.Conjuncts(
				a.Have(
					"the generic point of the prime ideal over M, normalized at j",
					"field_on(«functionsOfCurve») ∧ "+
						"(∃σ:(A → set(prod(set((num → num) → A), set((num → num) → A)))). "+
						"∃y:(num → set(prod(set((num → num) → A), set((num → num) → A)))). "+
						"    ring_homomorphism(field_ring(M), field_ring(«functionsOfCurve»), σ) ∧ "+
						"    (∀i:num. y(i) ∈ «functionsOfCurve».carrier) ∧ "+
						"    y(j) = «functionsOfCurve».one ∧ "+
						"    (∀i:num. "+
						"        i ≤ n ⇒ "+
						"        (y(i) = «functionsOfCurve».zero ⇔ "+
						"            polynomial_algebra_var(field_ring(M), i) ∈ ideal_span(«polynomialsOverM», E))) ∧ "+
						"    (∀i:num. n < i ⇒ y(i) = «functionsOfCurve».zero) ∧ "+
						"    (∀P:((num → num) → A). "+
						"        (∃d:num. homogeneous_polynomial(field_ring(M), n, d, P)) ⇒ "+
						"        (polynomial_algebra_eval(field_ring(M), field_ring(«functionsOfCurve»), σ, y, P) = "+
						"            «functionsOfCurve».zero ⇔ "+
						"            P ∈ ideal_span(«polynomialsOverM», E))))",
					By(
						field.RingOn.Read(M),
						minimal[0],
						minimal[1],
						prime,
						PrimeIdealGenericPoint.At(
							ringM, n, j, a.TermAs[Set[_Polynomial]]("ideal_span(«polynomialsOverM», E)")))),
				"the function field is a field",
				"it holds that point")
			σ, y, overMPoint := a.Unpack2As[Fun[A, _Fraction], Fun[Nat, _Fraction]](
				normalizedPoint[1], "σ", "y")
			over := a.Conjuncts(
				overMPoint,
				"σ is a ring homomorphism from M",
				"y lies in the function field",
				"y(j) is one",
				"up to n, y(i) is zero exactly when Xᵢ is in the ideal over M",
				"the coordinates past n are zero",
				"a form over M vanishes at y exactly when it lies in the ideal over M")
			a.LetAs[FieldOps[_Fraction]]("L", "«functionsOfCurve»")
			ringL := a.TermAs[RingOps[_Fraction]]("field_ring(L)")
			coefficientMap := a.Have(
				"σ restricted to k is a ring homomorphism from k",
				"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
				By(
					kSubfield,
					over[0],
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.RingHomRestrictSource))
			evaluation := a.Have(
				"evaluation along σ at y is a ring homomorphism out of the polynomials over k",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(L), "+
					"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y))",
				By(over[1], coefficientMap, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
			equationsAtY := a.Have(
				"each equation is a polynomial over k vanishing at y",
				Statement{
					Binders:    "∀P:((num → num) → A).",
					Hypotheses: []string{"P ∈ E"},
					Conclusion: "P ∈ «polynomials».carrier ∧ " +
						"polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_Polynomial]("P")
					equation := b.Assume()
					d, form := b.ObtainAs[Nat](
						"it is a form over k",
						"∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
						By(forms.At(b.MemberOf[on.Any](P, equation))),
						Named("d"))
					spanned := b.Have(
						"it lies in the ideal over M",
						"P ∈ ideal_span(«polynomialsOverM», E)",
						BySets(
							equation,
							ring_ideal.SpanContains.At(b.TermAs[RingOps[_Polynomial]]("«polynomialsOverM»"), E)))
					b.Show(
						"so it vanishes at y",
						By(
							over[5].At(P),
							overM.At(d, P),
							spanned,
							form,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictCoefficients.At(
								ringM, k, ringL, σ, y, P)))
				}))
			overk := a.Have(
				"the equations are polynomials over k",
				"E ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
				BySets(equationsAtY))
			idealAtY := a.Have(
				"so evaluation at y kills the ideal the equations generate over k",
				"ideal_span(«polynomials», E) ⊆ "+
					"ring_kernel(L.zero, "+
					"    «polynomials».carrier, "+
					"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y))",
				By(overk, equationsAtY, ring_homomorphism.IdealSpanInKernel.Read(evaluation).At(E)))
			genericOverk := a.Have(
				"a form over k vanishes at y exactly when it lies in the ideal over k",
				Statement{
					Binders:    "∀P:((num → num) → A).",
					Hypotheses: []string{"∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)"},
					Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero ⇔ " +
						"P ∈ ideal_span(«polynomials», E)",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_Polynomial]("P")
					d, form := b.UnpackAs[Nat](b.Assume(), "d")
					vanishing := b.Unfolded(b.Unfolded(idealAtY, ring_homomorphism.RingKernelDef), set_basic.SubsetDef)
					b.Show(
						"in the ideal over k it vanishes; vanishing, it lies in the ideal "+
							"over M, and a polynomial over k there lies in the ideal over k",
						By(
							M,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictCoefficients.At(
								ringM, k, ringL, σ, y, P),
							over[5].At(P),
							vanishing.At(P),
							overM.At(d, P),
							kSubfield,
							overk,
							form,
							polynomial_algebra.IdealDescent.At(m, k, variables, E, P)))
				}))
			before := a.Have(
				"the coordinates of y before j are zero: the variables before j lie in the ideal over M",
				"∀i:num. i < j ⇒ y(i) = L.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					earlier := b.Assume()
					index := b.Have(
						"i is a coordinate index",
						"i ≤ n",
						ByArith(earlier, minimal[0]))
					b.Show(
						"Xᵢ lies in the ideal over M",
						By(minimal[2].At(i), over[3].At(i), earlier, index))
				}))
			firstNonzero := a.Have(
				"so y(j) = one is the first nonzero coordinate of y",
				"∃j:num. j ≤ n ∧ y(j) = L.one ∧ (∀i:num. i < j ⇒ y(i) = L.zero)",
				Witness(j),
				By(minimal[0], over[2], before))
			a.Show(
				"the function field is a field, and σ with y is a generic point over k normalized at j",
				SplitConj(
					Case(
						"the function field is a field",
						By(normalizedPoint[0])),
					Case(
						"σ with y is a generic point over k, its first nonzero coordinate one",
						Witness(σ),
						Witness(y),
						By(coefficientMap, over[1], firstNonzero, over[4], genericOverk))))
		}),
})}

// GenericPointIntoAmbient — a point y of a field L, read along a coefficient
// map σ from k, with y(a) transcendental over σ(k) and every coordinate
// algebraic over σ(k)(y(a)), has an image x in an algebraically closed M
// holding a transcendental u over k: a point of M with zero and one where
// y has them, at which a polynomial over k vanishes exactly when it
// vanishes at y. σ is an isomorphism of k onto σ(k), K = σ(k)(y) is a
// function field over σ(k), and its embedding τ into M over the inverse of
// σ sending y(a) to u (FunctionFieldEmbedding) is one-to-one and carries
// values of polynomials at y to values at x = τ∘y.
var GenericPointIntoAmbient = genericPointIntoAmbientThm{family.Add(registry.ProofEntry{
	Name: "GenericPointIntoAmbient",
	Key:  "prop_ee94c4a5afc63897",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀L:field_on(B). ∀k:set(A). ∀n a:num. ∀σ:(A → B). ∀y:(num → B). ∀u:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀i:num. y(i) ∈ L.carrier",
			"∀i:num. n < i ⇒ y(i) = L.zero",
			"a ≤ n",
			"¬algebraic_over(L, image(σ, k), y(a))",
			"∀i:num. i ≤ n ⇒ algebraic_over(L, field_adjoin(L, image(σ, k), {y(a)}), y(i))",
			"u ∈ M.carrier",
			"¬algebraic_over(M, k, u)",
		},
		Conclusion: "∃x:(num → A). " +
			"    (∀i:num. x(i) ∈ M.carrier) ∧ " +
			"    (∀i:num. y(i) = L.zero ⇒ x(i) = M.zero) ∧ " +
			"    (∀i:num. y(i) = L.one ⇒ x(i) = M.one) ∧ " +
			"    (∀P:((num → num) → A). " +
			"        P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ⇒ " +
			"        (polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λc:A. c, x, P) = " +
			"            M.zero ⇔ " +
			"            polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero))",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n, a *Expr[Nat],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			u *Expr[A],
			closed, kSubfield, coefficientMap, coordinates, beyond, aIndex, transcendental, algebraic, uIn, uTranscendental Fact,
		) {
			m := arg.TermAs[FieldOps[A]]("M")
			l := arg.TermAs[FieldOps[B]]("L")
			ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
			ringL := arg.TermAs[RingOps[B]]("field_ring(L)")
			coefficients := arg.TermAs[RingOps[A]]("«hilbertCoefficients»")
			image := arg.TermAs[Set[B]]("image(σ, k)")
			imageRing := arg.TermAs[RingOps[B]]("restrict_ring(field_ring(L), image(σ, k))")
			inverse := arg.TermAs[Fun[B, A]]("inverse_on(k, σ)")
			identity := arg.TermAs[Fun[A, A]]("λc:A. c")
			variables := arg.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			embedded := arg.Conjuncts(
				GroupPremises(
					L, kSubfield, coefficientMap, ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(l, k, σ)),
				"σ(k) is a subfield of L",
				"σ is one-to-one on k")
			rings := arg.Conjuncts(
				arg.Have(
					"k and σ(k) are commutative rings, σ(k) a subring of L",
					"comm_ring_on(«hilbertCoefficients») ∧ "+
						"comm_ring_on(restrict_ring(field_ring(L), image(σ, k))) ∧ "+
						"subring(field_ring(L), image(σ, k))",
					By(
						ring_homomorphism.Source.Read(coefficientMap),
						embedded[0],
						field.SubfieldCommRing.Read(L).At(image),
						field.SubfieldSubring.Read(L).At(image))),
				"k is a commutative ring",
				"so is σ(k)",
				"σ(k) is a subring of L")
			onto := arg.Have(
				"σ maps k onto σ(k)",
				"ring_homomorphism(«hilbertCoefficients», restrict_ring(field_ring(L), image(σ, k)), σ)",
				By(
					rings[2],
					coefficientMap,
					set_basic.InImage,
					ring_homomorphism.RingHomCorestrict.At(coefficients, ringL, σ, image)))
			isomorphism := arg.Have(
				"so σ is an isomorphism of k onto σ(k)",
				"ring_isomorphism(«hilbertCoefficients», restrict_ring(field_ring(L), image(σ, k)), σ)",
				By(embedded[1], onto, ring_homomorphism.RingIsomorphismDef))
			inverseIsomorphism := arg.Have(
				"its inverse is an isomorphism back",
				"ring_isomorphism(restrict_ring(field_ring(L), image(σ, k)), "+
					"    «hilbertCoefficients», "+
					"    inverse_on(k, σ))",
				By(isomorphism, ring_homomorphism.IsomorphismInverse.At(coefficients, imageRing, σ)))
			back := arg.Have(
				"which leads σ(k) back to k inside M",
				"ring_homomorphism(restrict_ring(field_ring(L), image(σ, k)), field_ring(M), inverse_on(k, σ)) ∧ "+
					"image(inverse_on(k, σ), image(σ, k)) = k",
				By(
					field.RingOn.Read(M),
					embedded[1],
					kSubfield,
					inverseIsomorphism,
					ring_homomorphism.RingIsomorphismDef,
					field.SubfieldSubset,
					ring_homomorphism.RingHomExtendTarget.At(imageRing, ringM, inverse, k),
					functions.InverseOnImage.At(k, σ)))
			Y, YDef := arg.LetAs[Set[B]]("Y", "{y(i) | i:num | i ≤ n}")
			K, KDef := arg.LetAs[Set[B]]("K", "field_adjoin(L, image(σ, k), Y)")
			asImage := arg.Have(
				"Y is the image of the indices 0, …, n under y",
				"Y = image(y, {i:num | i ≤ n})",
				BySets(YDef))
			generators := arg.Have(
				"so Y is finite and lies in L",
				"finite(Y) ∧ Y ⊆ L.carrier",
				asImage.Rw(),
				BySets(coordinates, finite_set.FiniteImage.At(y, variables), num_segment.FiniteBelow.At(n)))
			adjoined := arg.Have(
				"K = σ(k)(Y) is a subfield holding σ(k) and Y",
				"subfield(L, K) ∧ image(σ, k) ⊆ K ∧ Y ⊆ K",
				By(
					KDef,
					embedded[0],
					generators,
					field.SubfieldSubset,
					algebraic_element.AdjoinSubfield.Read(L).At(image, Y)))
			rational := arg.TermAs[Set[B]]("field_adjoin(L, image(σ, k), {y(a)})")
			simple := arg.Have(
				"σ(k)(y(a)) is a subfield holding σ(k)",
				"subfield(L, field_adjoin(L, image(σ, k), {y(a)})) ∧ "+
					"image(σ, k) ⊆ field_adjoin(L, image(σ, k), {y(a)})",
				By(
					coordinates.At(a),
					embedded[0],
					algebraic_element.AdjoinElementSubfield.Read(L).AsFact().At(image, arg.TermAs[B]("y(a)"))))
			algebraicY := arg.Have(
				"every member of Y is algebraic over σ(k)(y(a))",
				"∀s:B. s ∈ Y ⇒ algebraic_over(L, field_adjoin(L, image(σ, k), {y(a)}), s)",
				BySets(algebraic, YDef))
			algebraicK := arg.Have(
				"so is every member of K",
				"∀z:B. z ∈ K ⇒ algebraic_over(L, field_adjoin(L, image(σ, k), {y(a)}), z)",
				By(
					L,
					algebraicY,
					KDef,
					generators,
					simple,
					At(algebraic_element.AdjoinAlgebraicOver, l, image, rational, Y)))
			functionField := arg.Have(
				"K is finitely generated over σ(k) and holds every coordinate of y",
				"(∃E:set(B). finite(E) ∧ E ⊆ K ∧ field_adjoin(L, image(σ, k), E) = K) ∧ (∀i:num. y(i) ∈ K)",
				SplitConj(
					Case(
						"K is generated over σ(k) by the finite set Y",
						By(KDef, generators, adjoined)),
					Case(
						"the coordinates up to n lie in Y, the rest are zero",
						StripQuant(),
						BySets(beyond, YDef, adjoined, nat_order.NotLessEq, field.SubfieldZero))))
			transcendentalBack := arg.Have(
				"u is transcendental over the field the inverse of σ leads σ(k) back to, which is k",
				"¬algebraic_over(M, image(inverse_on(k, σ), image(σ, k)), u)",
				By(Normalized, uTranscendental, back))
			generatorInK := arg.Have(
				"y(a) lies in K",
				"y(a) ∈ K",
				By(functionField))
			τ, embedding := arg.UnpackAs[Fun[B, A]](
				GroupPremises(
					closed,
					M,
					L,
					transcendentalBack,
					transcendental,
					algebraicK,
					uIn,
					embedded[0],
					functionField,
					generatorInK,
					adjoined,
					back,
					function_field.FunctionFieldEmbedding.At(l, m, image, K, arg.TermAs[B]("y(a)"), inverse, u)),
				"τ")
			maps := arg.Conjuncts(
				embedding,
				"τ is a ring homomorphism from K into M",
				"τ inverts σ on σ(k)",
				"τ sends y(a) to u")
			subringK := arg.Have(
				"K is a subring of L",
				"subring(field_ring(L), K)",
				By(adjoined, field.SubfieldSubring.Read(L).At(K)))
			kept := arg.Conjuncts(
				arg.Have(
					"τ is one-to-one on K, keeps zero and one, and undoes σ on k",
					"injective_on(K, τ) ∧ τ(L.zero) = M.zero ∧ τ(L.one) = M.one ∧ (∀c:A. c ∈ k ⇒ τ(σ(c)) = c)",
					SplitConj(
						Case(
							"a ring homomorphism out of the subfield K is one-to-one, and keeps zero and one",
							By(
								ring_homomorphism.MapZero.Read(maps[0]),
								ring_homomorphism.MapOne.Read(maps[0]),
								M,
								adjoined,
								maps[0],
								ring_homomorphism.SubfieldHomomorphismEmbedding.Read(L).At(m, K, τ))),
						Case(
							"τ inverts σ on σ(k)",
							By(maps[1], embedded[1], set_basic.InImage, At(functions.InverseOnLeft, k, σ))))),
				"τ is one-to-one on K",
				"it keeps zero",
				"it keeps one",
				"it undoes σ on k")
			identityOnk := arg.Have(
				"the identity of M restricts to k",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λc:A. c)",
				By(
					kSubfield,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
			intoK := arg.Have(
				"σ maps k into K",
				"∀c:A. c ∈ k ⇒ σ(c) ∈ K",
				BySets(adjoined))
			ringK := arg.TermAs[RingOps[B]]("restrict_ring(field_ring(L), K)")
			coefficientsInK := arg.Have(
				"so σ is a ring homomorphism from k into K",
				"ring_homomorphism(«hilbertCoefficients», restrict_ring(field_ring(L), K), σ)",
				By(
					subringK,
					intoK,
					coefficientMap,
					ring_homomorphism.RingHomCorestrict.At(coefficients, ringL, σ, K)))
			x := arg.TermAs[Fun[Nat, A]]("λi:num. τ(y(i))")
			xIn := arg.Have(
				"the coordinates τ(y(i)) lie in M",
				"∀i:num. τ(y(i)) ∈ M.carrier",
				By(ring_homomorphism.MapIn.Read(maps[0]), functionField))
			commute := arg.Have(
				"so evaluation at x is τ after evaluation at y, on the polynomials over k: τ undoes σ on k",
				Statement{
					Binders:    "∀P:((num → num) → A).",
					Hypotheses: []string{"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
					Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», " +
						"    field_ring(M), " +
						"    λc:A. c, " +
						"    λi:num. τ(y(i)), " +
						"    P) = " +
						"τ(polynomial_algebra_eval(«hilbertCoefficients», restrict_ring(field_ring(L), K), σ, y, P))",
				},
				By(
					coefficientsInK,
					maps[0],
					identityOnk,
					kept[3],
					functionField,
					At(
						polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural,
						coefficients,
						ringK,
						ringM,
						σ,
						τ,
						identity,
						variables,
						y)))
			valuesInK := arg.Have(
				"the value at y of a polynomial over k lies in K",
				Statement{
					Binders:    "∀P:((num → num) → A).",
					Hypotheses: []string{"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
					Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) ∈ K",
				},
				By(
					subringK,
					intoK,
					functionField,
					coefficientMap,
					polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring))
			arg.Show(
				"x = τ∘y is the point: τ keeps zero and one, and is one-to-one on K, where the values at y lie",
				Witness(x),
				SplitConj(
					Case(
						"its coordinates lie in M and are zero or one where y's are",
						By(Normalized, xIn, kept[1], kept[2])),
					Case(
						"a polynomial over k vanishes at x exactly when it vanishes at y",
						Derive(func(b *Argument) {
							P := b.FixAs[_Polynomial]("P")
							isPolynomial := b.Assume()
							separated := b.Have(
								"τ sends the value at y to zero only if it is zero",
								Statement{
									Hypotheses: []string{
										"τ(polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P)) = τ(L.zero)",
									},
									Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero",
								},
								By(kept[0], isPolynomial, valuesInK, adjoined, functions.InjectiveOnDef, field.SubfieldZero))
							b.Show(
								"the value at x is τ of the value at y, read in K as in L",
								By(
									isPolynomial,
									commute,
									kept[1],
									separated,
									polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictTarget.At(
										coefficients, ringL, K, σ, y, P)))
						}))))
		}),
})}

// AlgebraicPointIntoAmbient — a point y of a field L, read along a
// coefficient map σ from k, with every coordinate algebraic over σ(k), has an
// image x in an algebraically closed M: a point of M with zero and one where
// y has them, at which a polynomial over k vanishes exactly when it vanishes
// at y. σ is an isomorphism of k onto σ(k), K = σ(k)(y) is a finite
// algebraic extension of σ(k), and its embedding τ into M over the inverse
// of σ (FiniteAdjoinEmbedding) is one-to-one and carries values of
// polynomials at y to values at x = τ∘y.
var AlgebraicPointIntoAmbient = algebraicPointIntoAmbientThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicPointIntoAmbient",
	Key:  "prop_78996cd476fbb69f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀L:field_on(B). ∀k:set(A). ∀n:num. ∀σ:(A → B). ∀y:(num → B).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"ring_homomorphism(«hilbertCoefficients», field_ring(L), σ)",
			"∀i:num. y(i) ∈ L.carrier",
			"∀i:num. n < i ⇒ y(i) = L.zero",
			"∀i:num. i ≤ n ⇒ algebraic_over(L, image(σ, k), y(i))",
		},
		Conclusion: "∃x:(num → A). " +
			"    (∀i:num. x(i) ∈ M.carrier) ∧ " +
			"    (∀i:num. y(i) = L.zero ⇒ x(i) = M.zero) ∧ " +
			"    (∀i:num. y(i) = L.one ⇒ x(i) = M.one) ∧ " +
			"    (∀P:((num → num) → A). " +
			"        P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ⇒ " +
			"        (polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λc:A. c, x, P) = " +
			"            M.zero ⇔ " +
			"            polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero))",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			n *Expr[Nat],
			σ *Arrow[A, B],
			y *Arrow[Nat, B],
			closed, kSubfield, coefficientMap, coordinates, beyond, algebraic Fact,
		) {
			m := arg.TermAs[FieldOps[A]]("M")
			l := arg.TermAs[FieldOps[B]]("L")
			ringM := arg.TermAs[RingOps[A]]("field_ring(M)")
			ringL := arg.TermAs[RingOps[B]]("field_ring(L)")
			coefficients := arg.TermAs[RingOps[A]]("«hilbertCoefficients»")
			image := arg.TermAs[Set[B]]("image(σ, k)")
			imageRing := arg.TermAs[RingOps[B]]("restrict_ring(field_ring(L), image(σ, k))")
			inverse := arg.TermAs[Fun[B, A]]("inverse_on(k, σ)")
			identity := arg.TermAs[Fun[A, A]]("λc:A. c")
			variables := arg.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			embedded := arg.Conjuncts(
				GroupPremises(
					L, kSubfield, coefficientMap, ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(l, k, σ)),
				"σ(k) is a subfield of L",
				"σ is one-to-one on k")
			rings := arg.Conjuncts(
				arg.Have(
					"k and σ(k) are commutative rings, σ(k) a subring of L",
					"comm_ring_on(«hilbertCoefficients») ∧ "+
						"comm_ring_on(restrict_ring(field_ring(L), image(σ, k))) ∧ "+
						"subring(field_ring(L), image(σ, k))",
					By(
						ring_homomorphism.Source.Read(coefficientMap),
						embedded[0],
						field.SubfieldCommRing.Read(L).At(image),
						field.SubfieldSubring.Read(L).At(image))),
				"k is a commutative ring",
				"so is σ(k)",
				"σ(k) is a subring of L")
			onto := arg.Have(
				"σ maps k onto σ(k)",
				"ring_homomorphism(«hilbertCoefficients», restrict_ring(field_ring(L), image(σ, k)), σ)",
				By(
					rings[2],
					coefficientMap,
					set_basic.InImage,
					ring_homomorphism.RingHomCorestrict.At(coefficients, ringL, σ, image)))
			isomorphism := arg.Have(
				"so σ is an isomorphism of k onto σ(k)",
				"ring_isomorphism(«hilbertCoefficients», restrict_ring(field_ring(L), image(σ, k)), σ)",
				By(embedded[1], onto, ring_homomorphism.RingIsomorphismDef))
			inverseIsomorphism := arg.Have(
				"its inverse is an isomorphism back",
				"ring_isomorphism(restrict_ring(field_ring(L), image(σ, k)), "+
					"    «hilbertCoefficients», "+
					"    inverse_on(k, σ))",
				By(isomorphism, ring_homomorphism.IsomorphismInverse.At(coefficients, imageRing, σ)))
			back := arg.Have(
				"which leads σ(k) back to k inside M",
				"ring_homomorphism(restrict_ring(field_ring(L), image(σ, k)), field_ring(M), inverse_on(k, σ)) ∧ "+
					"image(inverse_on(k, σ), image(σ, k)) = k",
				By(
					field.RingOn.Read(M),
					embedded[1],
					kSubfield,
					inverseIsomorphism,
					ring_homomorphism.RingIsomorphismDef,
					field.SubfieldSubset,
					ring_homomorphism.RingHomExtendTarget.At(imageRing, ringM, inverse, k),
					functions.InverseOnImage.At(k, σ)))
			Y, YDef := arg.LetAs[Set[B]]("Y", "{y(i) | i:num | i ≤ n}")
			K, KDef := arg.LetAs[Set[B]]("K", "field_adjoin(L, image(σ, k), Y)")
			asImage := arg.Have(
				"Y is the image of the indices 0, …, n under y",
				"Y = image(y, {i:num | i ≤ n})",
				BySets(YDef))
			generators := arg.Have(
				"so Y is finite and lies in L",
				"finite(Y) ∧ Y ⊆ L.carrier",
				asImage.Rw(),
				BySets(coordinates, finite_set.FiniteImage.At(y, variables), num_segment.FiniteBelow.At(n)))
			adjoined := arg.Have(
				"K = σ(k)(Y) is a subfield holding σ(k) and Y",
				"subfield(L, K) ∧ image(σ, k) ⊆ K ∧ Y ⊆ K",
				By(
					KDef,
					embedded[0],
					generators,
					field.SubfieldSubset,
					algebraic_element.AdjoinSubfield.Read(L).At(image, Y)))
			algebraicY := arg.Have(
				"every member of Y is algebraic over σ(k)",
				"∀s:B. s ∈ Y ⇒ algebraic_over(L, image(σ, k), s)",
				BySets(algebraic, YDef))
			inK := arg.Have(
				"K holds every coordinate of y: those up to n lie in Y, the rest are zero",
				"∀i:num. y(i) ∈ K",
				StripQuant(),
				BySets(beyond, YDef, adjoined, nat_order.NotLessEq, field.SubfieldZero))
			τ, embedding := arg.ObtainAs[Fun[B, A]](
				"K embeds in M over the inverse of σ",
				"∃τ:(B → A). "+
					"    ring_homomorphism(restrict_ring(field_ring(L), K), field_ring(M), τ) ∧ "+
					"    (∀x:B. x ∈ image(σ, k) ⇒ τ(x) = inverse_on(k, σ, x))",
				By(
					closed,
					M,
					L,
					KDef,
					embedded[0],
					generators,
					algebraicY,
					back,
					algebraic_closure.FiniteAdjoinEmbedding.At(l, m, image, Y, inverse)),
				Named("τ"))
			maps := arg.Conjuncts(
				embedding,
				"τ is a ring homomorphism from K into M",
				"τ inverts σ on σ(k)")
			subringK := arg.Have(
				"K is a subring of L",
				"subring(field_ring(L), K)",
				By(adjoined, field.SubfieldSubring.Read(L).At(K)))
			kept := arg.Conjuncts(
				arg.Have(
					"τ is one-to-one on K, keeps zero and one, and undoes σ on k",
					"injective_on(K, τ) ∧ τ(L.zero) = M.zero ∧ τ(L.one) = M.one ∧ (∀c:A. c ∈ k ⇒ τ(σ(c)) = c)",
					SplitConj(
						Case(
							"a ring homomorphism out of the subfield K is one-to-one, and keeps zero and one",
							By(
								ring_homomorphism.MapZero.Read(maps[0]),
								ring_homomorphism.MapOne.Read(maps[0]),
								M,
								adjoined,
								maps[0],
								ring_homomorphism.SubfieldHomomorphismEmbedding.Read(L).At(m, K, τ))),
						Case(
							"τ inverts σ on σ(k)",
							By(maps[1], embedded[1], set_basic.InImage, At(functions.InverseOnLeft, k, σ))))),
				"τ is one-to-one on K",
				"it keeps zero",
				"it keeps one",
				"it undoes σ on k")
			identityOnk := arg.Have(
				"the identity of M restricts to k",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λc:A. c)",
				By(
					kSubfield,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
			intoK := arg.Have(
				"σ maps k into K",
				"∀c:A. c ∈ k ⇒ σ(c) ∈ K",
				BySets(adjoined))
			ringK := arg.TermAs[RingOps[B]]("restrict_ring(field_ring(L), K)")
			coefficientsInK := arg.Have(
				"so σ is a ring homomorphism from k into K",
				"ring_homomorphism(«hilbertCoefficients», restrict_ring(field_ring(L), K), σ)",
				By(
					subringK,
					intoK,
					coefficientMap,
					ring_homomorphism.RingHomCorestrict.At(coefficients, ringL, σ, K)))
			x := arg.TermAs[Fun[Nat, A]]("λi:num. τ(y(i))")
			xIn := arg.Have(
				"the coordinates τ(y(i)) lie in M",
				"∀i:num. τ(y(i)) ∈ M.carrier",
				By(ring_homomorphism.MapIn.Read(maps[0]), inK))
			commute := arg.Have(
				"so evaluation at x is τ after evaluation at y, on the polynomials over k: τ undoes σ on k",
				Statement{
					Binders:    "∀P:((num → num) → A).",
					Hypotheses: []string{"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
					Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», " +
						"    field_ring(M), " +
						"    λc:A. c, " +
						"    λi:num. τ(y(i)), " +
						"    P) = " +
						"τ(polynomial_algebra_eval(«hilbertCoefficients», restrict_ring(field_ring(L), K), σ, y, P))",
				},
				By(
					coefficientsInK,
					maps[0],
					identityOnk,
					kept[3],
					inK,
					At(
						polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural,
						coefficients,
						ringK,
						ringM,
						σ,
						τ,
						identity,
						variables,
						y)))
			valuesInK := arg.Have(
				"the value at y of a polynomial over k lies in K",
				Statement{
					Binders:    "∀P:((num → num) → A).",
					Hypotheses: []string{"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"},
					Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) ∈ K",
				},
				By(
					subringK,
					intoK,
					inK,
					coefficientMap,
					polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring))
			arg.Show(
				"x = τ∘y is the point: τ keeps zero and one, and is one-to-one on K, where the values at y lie",
				Witness(x),
				SplitConj(
					Case(
						"its coordinates lie in M and are zero or one where y's are",
						By(Normalized, xIn, kept[1], kept[2])),
					Case(
						"a polynomial over k vanishes at x exactly when it vanishes at y",
						Derive(func(b *Argument) {
							P := b.FixAs[_Polynomial]("P")
							polynomial := b.Assume()
							separated := b.Have(
								"τ sends the value at y to zero only if it is zero",
								Statement{
									Hypotheses: []string{
										"τ(polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P)) = τ(L.zero)",
									},
									Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(L), σ, y, P) = L.zero",
								},
								By(kept[0], polynomial, valuesInK, adjoined, functions.InjectiveOnDef, field.SubfieldZero))
							b.Show(
								"the value at x is τ of the value at y, read in K as in L",
								By(
									polynomial,
									commute,
									kept[1],
									separated,
									polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictTarget.At(
										coefficients, ringL, K, σ, y, P)))
						}))))
		}),
})}

// GenericFieldRegular — the field K of a generic point x of a smooth
// projective equation curve over k in an algebraically closed M is a
// regular function field over k: K is generated over k by the finitely
// many coordinates of x, some coordinate x(b) is transcendental over k with
// every coordinate algebraic over k(x(b)) (TranscendenceAtGenericPoint at
// L = M along the identity), so all of K is algebraic over k(x(b))
// (AdjoinAlgebraicOver); k, a finite field, is perfect, and the members of
// K algebraic over k lie in k (GenericFieldExactConstants).
var GenericFieldRegular = genericFieldRegularThm{family.Add(registry.ProofEntry{
	Name: "GenericFieldRegular",
	Key:  "prop_298f03b3c54fd86",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"projective_generic_field(M, k, n, E, K)",
		},
		Conclusion: "regular_function_field(M, k, K)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[_Polynomial]],
			closed, curve, kSubfieldK, generic Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			ringM := a.TermAs[RingOps[A]]("field_ring(M)")
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			kSubfield := projective_curve.CurveConstantsSubfield.Read(curve)
			x, ofPoint := a.UnpackAs[Fun[Nat, A]](
				a.Unfolded(generic, projective_curve.ProjectiveGenericFieldDef), "x")
			genericPoint := a.Conjuncts(
				ofPoint,
				"x is a point of the curve with coordinates in K",
				"its coordinates generate K over k",
				"a form over k vanishes at x exactly when it lies in the ideal")
			coordinatesInK := a.Have(
				"the coordinates 0, …, n of x lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(genericPoint[0], projective_curve.PointCoordinatesIn))
			inM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinatesInK, kSubfieldK, field.SubfieldSubset))
			identityOnk := a.Have(
				"the identity of M restricts to k",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSubfield,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
			fixed := a.Have(
				"and leaves k in place",
				"image(λa:A. a, k) = k",
				BySets())
			normalized := a.Have(
				"some coordinate of x is one",
				"∃j:num. j ≤ n ∧ x(j) = M.one",
				By(genericPoint[0], projective_curve.PointLeadingOne.At(ringM, k, K, n, E, x)))
			bIndex, transcendence := a.ObtainAs[Nat](
				"some coordinate x(b) is transcendental over k with every coordinate algebraic over k(x(b))",
				"∃b:num. "+
					"    b ≤ n ∧ "+
					"    ¬algebraic_over(M, k, x(b)) ∧ "+
					"    (∀i:num. i ≤ n ⇒ algebraic_over(M, field_adjoin(M, k, {x(b)}), x(i)))",
				By(
					M,
					kSubfield,
					identityOnk,
					inM,
					normalized,
					genericPoint[2],
					projective_curve.CurveHilbertEventuallyLinear.Read(curve),
					fixed,
					TranscendenceAtGenericPoint.At(m, m, k, n, E, a.TermAs[Fun[A, A]]("λa:A. a"), x)),
				Named("b"))
			separating := a.Conjuncts(
				transcendence,
				"b is a coordinate index",
				"x(b) is transcendental over k",
				"every coordinate is algebraic over k(x(b))")
			coordinatesSet := a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}")
			asImage := a.Have(
				"the coordinates 0, …, n are the image of the indices under x",
				"{x(i) | i:num | i ≤ n} = image(x, {i:num | i ≤ n})",
				BySets())
			finitelyMany := a.Have(
				"so they are finitely many members of M",
				"finite({x(i) | i:num | i ≤ n}) ∧ {x(i) | i:num | i ≤ n} ⊆ M.carrier",
				asImage.Rw(),
				BySets(inM, finite_set.FiniteImage.At(x, variables), num_segment.FiniteBelow.At(n)))
			inK := a.Have(
				"K = k(x) holds k and the coordinates",
				"k ⊆ K ∧ {x(i) | i:num | i ≤ n} ⊆ K",
				By(
					genericPoint[1],
					kSubfield,
					finitelyMany,
					field.SubfieldSubset,
					algebraic_element.AdjoinSubfield.Read(M).At(k, coordinatesSet)))
			perfect := a.Have(
				"k, a finite field, is perfect",
				"perfect_field(restrict_field(M, k))",
				By(
					kSubfield,
					projective_curve.CurveConstantsFinite.Read(curve),
					field.SubfieldFieldOn.Read(M).At(k),
					field.RestrictFieldDef,
					perfect_field.FiniteFieldIsPerfect.At(a.TermAs[FieldOps[A]]("restrict_field(M, k)"))))
			finitelyGenerated := a.Have(
				"K is generated over k by finitely many of its members",
				"∃F:set(A). finite(F) ∧ F ⊆ K ∧ field_adjoin(M, k, F) = K",
				By(finitelyMany, inK, genericPoint[1]))
			xb := a.TermAs[A]("x(b)")
			rational := a.TermAs[Set[A]]("field_adjoin(M, k, {x(b)})")
			simple := a.Have(
				"k(x(b)) is a subfield holding k",
				"subfield(M, field_adjoin(M, k, {x(b)})) ∧ k ⊆ field_adjoin(M, k, {x(b)})",
				By(
					separating[0],
					inM.At(bIndex),
					kSubfield,
					algebraic_element.AdjoinElementSubfield.Read(M).AsFact().At(k, xb)))
			algebraicCoordinates := a.Have(
				"every coordinate is algebraic over k(x(b))",
				"∀s:A. s ∈ {x(i) | i:num | i ≤ n} ⇒ algebraic_over(M, field_adjoin(M, k, {x(b)}), s)",
				BySets(separating[2]))
			transcendentalBase := a.Have(
				"x(b) is a member of K transcendental over k over which all of K is algebraic",
				"x(b) ∈ K ∧ "+
					"¬algebraic_over(M, k, x(b)) ∧ "+
					"(∀z:A. z ∈ K ⇒ algebraic_over(M, field_adjoin(M, k, {x(b)}), z))",
				By(
					M,
					separating[0],
					separating[1],
					inK,
					genericPoint[1],
					simple,
					finitelyMany,
					algebraicCoordinates,
					set_basic.SubsetDef,
					At(algebraic_element.AdjoinAlgebraicOver, m, k, rational, coordinatesSet)))
			exact := a.Have(
				"the members of K algebraic over k lie in k",
				"∀z:A. z ∈ K ∧ algebraic_over(M, k, z) ⇒ z ∈ k",
				By(M, closed, curve, kSubfieldK, generic, At(GenericFieldExactConstants, m, k, K, n, E)))
			a.Show(
				"so K is a regular function field over k",
				Simp(Fwd(function_field.RegularFunctionFieldDef)),
				By(kSubfield, kSubfieldK, inK, perfect, finitelyGenerated, transcendentalBase, exact))
		}),
})}

// GenericPointExists — a smooth projective equation curve over k has a
// generic point in an algebraically closed field M that holds a
// transcendental over k, and the field of that point is a regular function
// field over k. The function field of the curve over M holds a generic
// point y over k (CurveGenericPoint); y has a coordinate transcendental over
// k with every coordinate algebraic over it (TranscendenceAtGenericPoint), so
// it has an image x in M at which the same polynomials vanish
// (GenericPointIntoAmbient); K = k(x) is the field of the generic point x,
// and a regular function field (GenericFieldRegular).
var GenericPointExists = genericPointExistsThm{family.Add(registry.ProofEntry{
	Name: "GenericPointExists",
	Key:  "prop_92a26c75d7fed643",
	Reading: "The transcendental u in M is load-bearing: without it M is algebraic over k " +
		"and a field of transcendence degree one cannot embed. Primality over M is read twice, " +
		"inside the curve hypothesis: it makes the function field of the curve over M a field " +
		"holding the generic point y (CurveGenericPoint), and it leaves k algebraically closed " +
		"in K (GenericFieldRegular), the exact-constants clause of regularity.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀E:set((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"∃u:A. u ∈ M.carrier ∧ ¬algebraic_over(M, k, u)",
			"smooth_projective_equation_curve(M, k, n, E)",
		},
		Conclusion: "∃K:set(A). " +
			"    subfield(M, K) ∧ projective_generic_field(M, k, n, E, K) ∧ regular_function_field(M, k, K)",
		Abbrev: Abbrev{
			{Name: "polynomialsOverM", Text: "polynomial_algebra_ring(field_ring(M), {i:num | i ≤ n})"},
			{Name: "functionsOfCurve", Text: "fraction_field_record( " +
				"    ideal_quotient_ring(«polynomialsOverM», ideal_span(«polynomialsOverM», E)))"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[_Polynomial]],
			closed, transcendentalExists, curve Fact,
		) {
			m := arg.TermAs[FieldOps[A]]("M")
			u, transcendental := arg.UnpackAs[A](transcendentalExists, "u")
			chosen := arg.Conjuncts(
				transcendental,
				"u lies in M",
				"u is transcendental over k")
			kSubfield := arg.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			forms := projective_curve.CurveEquationsForms.Read(curve)
			linearGrowth := projective_curve.CurveHilbertEventuallyLinear.Read(curve)
			ofCurve := arg.Conjuncts(
				arg.Have(
					"the function field of the curve over M holds a generic point over k",
					"field_on(«functionsOfCurve») ∧ "+
						"(∃σ:(A → set(prod(set((num → num) → A), set((num → num) → A)))). "+
						"∃y:(num → set(prod(set((num → num) → A), set((num → num) → A)))). "+
						"    ring_homomorphism(«hilbertCoefficients», field_ring(«functionsOfCurve»), σ) ∧ "+
						"    (∀i:num. y(i) ∈ «functionsOfCurve».carrier) ∧ "+
						"    (∃j:num. "+
						"        j ≤ n ∧ "+
						"        y(j) = «functionsOfCurve».one ∧ "+
						"        (∀i:num. i < j ⇒ y(i) = «functionsOfCurve».zero)) ∧ "+
						"    (∀i:num. n < i ⇒ y(i) = «functionsOfCurve».zero) ∧ "+
						"    (∀P:((num → num) → A). "+
						"        (∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)) ⇒ "+
						"        (polynomial_algebra_eval(«hilbertCoefficients», "+
						"                field_ring(«functionsOfCurve»), "+
						"                σ, "+
						"                y, "+
						"                P) = "+
						"            «functionsOfCurve».zero ⇔ "+
						"            P ∈ ideal_span(«polynomials», E))))",
					By(M, curve, CurveGenericPoint.At(m, k, n, E))),
				"the function field is a field",
				"it holds a generic point over k")
			L, _ := arg.LetAs[FieldOps[_Fraction]]("L", "«functionsOfCurve»")
			σ, y, overk := arg.Unpack2As[Fun[A, _Fraction], Fun[Nat, _Fraction]](ofCurve[1], "σ", "y")
			point := arg.Conjuncts(
				overk,
				"σ is a ring homomorphism from k",
				"y lies in L",
				"its first nonzero coordinate is one",
				"its coordinates past n are zero",
				"a form over k vanishes at y exactly when it lies in the ideal over k")
			j, first := arg.UnpackAs[Nat](point[2], "j")
			normalized := arg.Conjuncts(
				first,
				"j is a coordinate index",
				"y(j) is one",
				"the coordinates before it are zero")
			a, separating := arg.UnpackAs[Nat](
				GroupPremises(
					M,
					ofCurve[0],
					kSubfield,
					point[0],
					arg.Have(
						"the coordinates of y up to n lie in L",
						"∀i:num. i ≤ n ⇒ y(i) ∈ L.carrier",
						By(point[1])),
					arg.Have(
						"some coordinate of y is one",
						"∃j:num. j ≤ n ∧ y(j) = L.one",
						Witness(j),
						By(normalized[0], normalized[1])),
					point[4],
					linearGrowth,
					TranscendenceAtGenericPoint.At(m, L, k, n, E, σ, y)),
				"a")
			base := arg.Conjuncts(
				separating,
				"a is a coordinate index",
				"y(a) is transcendental over σ(k)",
				"every coordinate is algebraic over σ(k)(y(a))")
			x, transported := arg.UnpackAs[Fun[Nat, A]](
				GroupPremises(
					M,
					ofCurve[0],
					closed,
					kSubfield,
					point[0],
					point[1],
					point[3],
					base[0],
					base[1],
					base[2],
					chosen[0],
					chosen[1],
					GenericPointIntoAmbient.At(m, L, k, n, a, σ, y, u)),
				"x")
			ofX := arg.Conjuncts(
				transported,
				"x lies in M",
				"x is zero where y is",
				"x is one where y is",
				"a polynomial over k vanishes at x exactly when it vanishes at y")
			genericAtX := arg.Have(
				"a form over k vanishes at x exactly when it lies in the ideal over k",
				Statement{
					Binders: "∀P:((num → num) → A).",
					Hypotheses: []string{
						"∃d:num. homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
					},
					Conclusion: "«at»(P) = M.zero ⇔ P ∈ ideal_span(«polynomials», E)",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_Polynomial]("P")
					degree := b.Assume()
					_, form := b.UnpackAs[Nat](degree, "d")
					b.Show(
						"a form is a polynomial over k, and vanishes at y exactly when it lies in the ideal",
						By(degree, homogeneous_polynomial.FormPolynomial.Read(form), point[4].At(P), ofX[3].At(P)))
				}))
			coordinates := arg.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}")
			inM := arg.Have(
				"the coordinates 0, …, n of x lie in M",
				"{x(i) | i:num | i ≤ n} ⊆ M.carrier",
				BySets(ofX[0]))
			K, KDef := arg.LetAs[Set[A]]("K", "field_adjoin(M, k, {x(i) | i:num | i ≤ n})")
			adjoined := arg.Conjuncts(
				arg.Have(
					"K = k(x) is a subfield of M holding k and the coordinates of x",
					"subfield(M, K) ∧ k ⊆ K ∧ {x(i) | i:num | i ≤ n} ⊆ K",
					By(
						M,
						kSubfield,
						inM,
						KDef,
						field.SubfieldSubset,
						algebraic_element.AdjoinSubfield.Read(M).At(k, coordinates))),
				"K is a subfield of M",
				"it holds k",
				"it holds the coordinates of x")
			conditions := arg.Have(
				"x has its coordinates 0, …, n in K and the rest zero, its "+
					"first nonzero coordinate one, and the equations vanish at it",
				"(∀i:num. i ≤ n ⇒ x(i) ∈ K) ∧ "+
					"(∀i:num. n < i ⇒ x(i) = M.zero) ∧ "+
					"(∃j:num. j ≤ n ∧ x(j) = M.one ∧ (∀i:num. i < j ⇒ x(i) = M.zero)) ∧ "+
					"(∀P:((num → num) → A). P ∈ E ⇒ «at»(P) = M.zero)",
				SplitConjAll(
					Case(
						"the coordinates up to n lie in K",
						BySets(adjoined[2])),
					Case(
						"the coordinates past n are zero, as y's are",
						By(point[3], ofX[1])),
					Case(
						"x(j) is one and the coordinates before it zero, as for y",
						Witness(j),
						By(normalized[0], normalized[1], normalized[2], ofX[1], ofX[2])),
					Case(
						"each equation lies in the ideal it helps generate, so vanishes at x",
						By(
							forms,
							genericAtX,
							ring_ideal.SpanContains.At(arg.TermAs[RingOps[_Polynomial]]("«polynomials»"), E),
							set_basic.SubsetDef))))
			onCurve := arg.Have(
				"so x is a point of the curve with coordinates in K",
				"x ∈ projective_equation_points(field_ring(M), k, K, n, E)",
				Simp(Fwd(projective_curve.ProjectiveEquationPointsDef)),
				BySets(conditions))
			genericField := arg.Have(
				"and K is the field of the generic point x",
				"projective_generic_field(M, k, n, E, K)",
				Simp(Fwd(projective_curve.ProjectiveGenericFieldDef)),
				Witness(x),
				By(onCurve, KDef, genericAtX))
			arg.Show(
				"K is a subfield of M, the field of a generic point "+
					"of the curve, and a regular function field over k",
				Witness(K),
				By(closed, M, adjoined[0], genericField, curve, GenericFieldRegular.At(m, k, K, n, E)))
		}),
})}

// HomogenizationInIdeal — when the forms over k vanishing at x lie in the
// ideal of E, and z = F(x)/G(x) for forms F, G over k of one degree is a root
// of a polynomial f over k, the homogenization of f at F over G lies in the
// ideal of E over M: it is a form over k (HomogenizedForm) whose value at x
// is G(x)^m·f(z) = 0 (EvalRescaled), so it lies in the ideal over k, hence in
// the ideal over M (IdealExtension), where it is spelled with the operations
// of M.
var HomogenizationInIdeal = homogenizationInIdealThm{family.Add(registry.ProofEntry{
	Name: "HomogenizationInIdeal",
	Key:  "prop_6e47d101d1f9db10",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀d:num. " +
			"∀F G:((num → num) → A). " +
			"∀z:A. " +
			"∀f:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			"E ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			"∀e:num. ∀P:((num → num) → A). " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, e, P) ∧ «at»(P) = M.zero ⇒ " +
				"    P ∈ ideal_span(«polynomials», E)",
			"homogeneous_polynomial(«hilbertCoefficients», n, d, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, d, G)",
			"z ∈ M.carrier",
			"z * «at»(G) = «at»(F)",
			"polynomial_over(k, f)",
			"polynomial_eval(f, z) = M.zero",
		},
		Conclusion: "«homogenizedMAtF» ∈ ideal_span(«overM», E)",
		Abbrev: Abbrev{
			{Name: "overM", Text: "polynomial_algebra_ring(field_ring(M), {i:num | i ≤ n})"},
			{Name: "powerG", Text: "λj:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        G, " +
				"        j)"},
			{Name: "homogenized", Text: "λi:num. " +
				"    COND(i ≤ polynomial_degree(f), " +
				"        polynomial_algebra_mul(«hilbertCoefficients», " +
				"            «powerG»(polynomial_degree(f) - i), " +
				"            polynomial_algebra_const(«hilbertCoefficients», f(i))), " +
				"        fun_zero)"},
			{Name: "homogenizedAtF", Text: "polynomial_eval(fun_add, " +
				"    fun_zero, " +
				"    polynomial_algebra_mul(«hilbertCoefficients»), " +
				"    polynomial_algebra_one(«hilbertCoefficients»), " +
				"    «homogenized», " +
				"    F)"},
			{Name: "homogenizedM", Text: "λi:num. " +
				"    COND(i ≤ polynomial_degree(f), " +
				"        polynomial_algebra_mul(field_ring(M), " +
				"            monoid_pow(polynomial_algebra_mul(field_ring(M)), " +
				"                polynomial_algebra_one(field_ring(M)), " +
				"                G, " +
				"                polynomial_degree(f) - i), " +
				"            polynomial_algebra_const(field_ring(M), f(i))), " +
				"        fun_zero)"},
			{Name: "homogenizedMAtF", Text: "polynomial_eval(fun_add, " +
				"    fun_zero, " +
				"    polynomial_algebra_mul(field_ring(M)), " +
				"    polynomial_algebra_one(field_ring(M)), " +
				"    «homogenizedM», " +
				"    F)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[_Polynomial]],
			x *Arrow[Nat, A],
			d *Expr[Nat],
			F, G *Arrow[Fun[Nat, Nat], A],
			z *Expr[A],
			f *Arrow[Nat, A],
			subk, coordinates, eOverk, vanishing, fForm, gForm, zIn, ratio, fOverk, fRoot Fact,
		) {
			fieldRing := field.RingOn.Read(M)
			coefficients := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
			ringM := a.TermAs[RingOps[A]]("field_ring(M)")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			evaluationAtX := a.TermAs[Fun[_Polynomial, A]](
				"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x)")
			ringk := a.Have(
				"k, a subfield of M, is a commutative ring",
				"comm_ring_on(«hilbertCoefficients»)",
				By(subk, field.SubfieldCommRing.Read(M).At(k)))
			kInM := a.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(subk, field.SubfieldSubset))
			inclusion := a.Have(
				"k includes into M",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					subk,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(fieldRing).At(k)))
			evaluation := a.Have(
				"evaluation at x is a ring map of the polynomials over k into M",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x))",
				By(inclusion, coordinates, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
			formsk := a.Have(
				"the forms are polynomials over k",
				"F ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
					"G ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
				By(
					homogeneous_polynomial.FormPolynomial.Read(fForm),
					homogeneous_polynomial.FormPolynomial.Read(gForm)))
			formsParts := a.Conjuncts(
				formsk,
				"F is a polynomial over k",
				"G is a polynomial over k")
			values := a.Have(
				"F(x) and G(x) lie in M",
				"«at»(F) ∈ M.carrier ∧ «at»(G) ∈ M.carrier",
				By(formsk, ring_homomorphism.MapIn.Read(evaluation)))
			degree := a.TermAs[Nat]("polynomial_degree(f)")
			fOverM := a.Have(
				"f is a polynomial over M",
				"polynomial_over(M.carrier, f)",
				By(kInM, fOverk, polynomial.PolynomialOverMono))
			homogenizedAtFForm := a.Have(
				"the homogenization Σ f(i)·Fⁱ·G^(m−i) is a form of degree d·m over k",
				"homogeneous_polynomial(«hilbertCoefficients», n, d * polynomial_degree(f), «homogenizedAtF»)",
				By(
					ringk,
					fOverk,
					fForm,
					gForm,
					homogeneous_polynomial.HomogenizedForm.Read(ringk).At(n, d, f, F, G)))
			ringPolys := a.Have(
				"the polynomials over k are a commutative ring",
				"comm_ring_on(«polynomials»)",
				By(ringk, polynomial_algebra.PolynomialAlgebraCommRingOn))
			polyMonoid := comm_ring.MulMonoidOn.Read(ringPolys)
			constantsk := a.Have(
				"the constants over k are a ring map",
				"ring_homomorphism(«hilbertCoefficients», "+
					"    «polynomials», "+
					"    polynomial_algebra_const(«hilbertCoefficients»))",
				By(ringk, polynomial_algebra.PolynomialAlgebraConstHom))
			fIn := a.Have(
				"the coefficients of f lie in k",
				"∀i:num. f(i) ∈ k",
				By(fOverk, polynomial.PolynomialOverDef))
			homogenizedShape := a.Have(
				"the coefficients G^(m−i)·f(i) of the homogenization in F are polynomials over k, zero past m",
				"vec⟨suc(polynomial_degree(f))⟩(fun_zero, «homogenized») ∧ "+
					"(∀i:num. «homogenized»(i) ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}))",
				SplitConj(
					Case(
						"they vanish past m",
						Unfold(vec_space.VecDef),
						Derive(func(b *Argument) {
							b.FixAs[Nat]("i")
							past := b.Assume()
							beyond := b.Have(
								"i is past m",
								"¬(i ≤ polynomial_degree(f))",
								ByArith(past))
							b.Show(
								"so the coefficient is zero",
								By(beyond))
						})),
					Case(
						"each is a product of members, or zero",
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]("i")
							b.Cases(b.TermAs[Bool]("i ≤ polynomial_degree(f)"))
							b.When(
								"up to m it is G^(m−i) times the constant f(i)",
								func(c *Argument, below Fact) {
									power := c.TermAs[_Polynomial]("«powerG»(polynomial_degree(f) - i)")
									constant := c.TermAs[_Polynomial]("polynomial_algebra_const(«hilbertCoefficients», f(i))")
									c.Show(
										"a product of two members",
										By(
											below,
											formsParts[1],
											fIn.At(i),
											ring_homomorphism.MapIn.Read(constantsk).AsFact().At(c.TermAs[A]("f(i)")),
											comm_monoid.PowIn.Read(polyMonoid).AsFact().At(G, c.TermAs[Nat]("polynomial_degree(f) - i")),
											comm_ring.MulIn.Read(ringPolys).AsFact().At(power, constant)))
								})
							b.Otherwise(
								"past m it is zero",
								func(c *Argument, past Fact) {
									c.Show(
										"zero is a member",
										By(past, comm_ring.ZeroIn.Read(ringPolys)))
								})
						}))))
			homogenizedOver := a.Have(
				"so they are a polynomial over the polynomials over k",
				"polynomial_over(fun_zero, "+
					"    polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}), "+
					"    «homogenized»)",
				By(homogenizedShape, polynomial.PolynomialOverDef))
			along := a.Have(
				"evaluation at x, a ring map, carries the homogenization "+
					"to its evaluated coefficients taken at F(x)",
				"«at»(«homogenizedAtF») = polynomial_eval(λi:num. «at»(«homogenized»(i)), «at»(F))",
				By(
					evaluation,
					homogenizedOver,
					formsParts[0],
					polynomial_evaluation.EvalAlongHomomorphism.At(
						a.TermAs[RingOps[_Polynomial]]("«polynomials»"),
						ringM,
						evaluationAtX,
						a.TermAs[Fun[Nat, _Polynomial]]("«homogenized»"),
						F)))
			pointwise := a.Have(
				"the evaluated coefficients are G(x)^(m−i)·f(i) up to m",
				"(λi:num. «at»(«homogenized»(i))) = "+
					"λi:num. "+
					"    COND(i ≤ polynomial_degree(f), "+
					"        monoid_pow(M.mul, M.one, «at»(G), 1 * (polynomial_degree(f) - i)) * f(i), "+
					"        M.zero)",
				Funext(),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Cases(b.TermAs[Bool]("i ≤ polynomial_degree(f)"))
					b.When(
						"up to m evaluation keeps the product, the power and the constant",
						func(c *Argument, below Fact) {
							power := c.TermAs[_Polynomial]("«powerG»(polynomial_degree(f) - i)")
							constant := c.TermAs[_Polynomial]("polynomial_algebra_const(«hilbertCoefficients», f(i))")
							exponent := c.TermAs[Nat]("polynomial_degree(f) - i")
							unit := c.Have(
								"1·(m − i) is m − i",
								"1 * (polynomial_degree(f) - i) = polynomial_degree(f) - i",
								ByArith())
							c.Show(
								"G^(m−i)·f(i) evaluates to G(x)^(m−i)·f(i)",
								By(
									below,
									unit,
									formsParts[1],
									fIn.At(i),
									inclusion,
									ring_homomorphism.MapIn.Read(constantsk).AsFact().At(c.TermAs[A]("f(i)")),
									comm_monoid.PowIn.Read(polyMonoid).AsFact().At(G, exponent),
									ring_homomorphism.MapMul.Read(evaluation).AsFact().At(power, constant),
									ring_homomorphism.RingMapPower.Read(evaluation).AsFact().At(exponent, G),
									polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
										coefficients, ringM, identity, x, c.TermAs[A]("f(i)"))))
						})
					b.Otherwise(
						"past m both are zero",
						func(c *Argument, past Fact) {
							c.Show(
								"evaluation keeps zero",
								By(past, ring_homomorphism.MapZero.Read(evaluation)))
						})
				}))
			mulMonoid := comm_ring.MulMonoidOn.Read(fieldRing)
			powerOne := a.Have(
				"G(x)¹ is G(x)",
				"monoid_pow(M.mul, M.one, «at»(G), 1) = «at»(G)",
				By(values, comm_monoid.PowOneOn.Read(mulMonoid)))
			numerator := a.Have(
				"F(x) = G(x)¹·z",
				"«at»(F) = monoid_pow(M.mul, M.one, «at»(G), 1) * z",
				powerOne.Rw(),
				ByArith(M, values, zIn, ratio))
			valueGX := a.TermAs[A]("«at»(G)")
			valueZero := a.Have(
				"so the homogenization vanishes at x: its value is G(x)^m·f(z) = 0",
				"«at»(«homogenizedAtF») = M.zero",
				along.Rw(),
				pointwise.Rw(),
				numerator.Rw(),
				By(
					fOverM,
					nat_order.LessEqRefl.At(degree),
					fRoot,
					values,
					zIn,
					polynomial_evaluation.EvalRescaled.Read(fieldRing).AsFact().At(
						f, degree, a.TermAs[Nat]("1"), valueGX, z),
					comm_monoid.PowIn.Read(mulMonoid).AsFact().At(valueGX, a.TermAs[Nat]("1 * polynomial_degree(f)")),
					comm_ring.MulRightZeroOn.Read(fieldRing).AsFact().At(
						a.TermAs[A]("monoid_pow(M.mul, M.one, «at»(G), 1 * polynomial_degree(f))"))))
			inIdealk := a.Have(
				"a form over k vanishing at the generic point lies in the ideal over k",
				"«homogenizedAtF» ∈ ideal_span(«polynomials», E)",
				By(vanishing, homogenizedAtFForm, valueZero))
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			inIdealM := a.Have(
				"so it lies in the ideal over M",
				"«homogenizedAtF» ∈ ideal_span(«overM», E)",
				By(
					inIdealk,
					subk,
					eOverk,
					set_basic.SubsetDef,
					polynomial_algebra.IdealExtension.Read(M).At(k, variables, E)))
			sameMul := a.Have(
				"the polynomials over k multiply as they do over M",
				"polynomial_algebra_mul⟨D:num⟩(«hilbertCoefficients») = "+
					"polynomial_algebra_mul⟨D:num⟩(field_ring(M))",
				Funext(),
				By(polynomial_algebra.PolynomialAlgebraMulRestrict.Inst(
					TypeBinder.BindA[A](), TypeBinder.BindD[Nat]()).At(
					ringM, k)))
			sameOne := a.Have(
				"and have the same one",
				"polynomial_algebra_one⟨D:num⟩(«hilbertCoefficients») = "+
					"polynomial_algebra_one⟨D:num⟩(field_ring(M))",
				By(polynomial_algebra.PolynomialAlgebraOneRestrict.At[A, Nat](ringM, k)))
			sameConst := a.Have(
				"and the same constants",
				"polynomial_algebra_const⟨D:num⟩(«hilbertCoefficients») = "+
					"polynomial_algebra_const⟨D:num⟩(field_ring(M))",
				Funext(),
				By(polynomial_algebra.PolynomialAlgebraConstRestrict.Inst(
					TypeBinder.BindA[A](), TypeBinder.BindD[Nat]()).At(
					ringM, k)))
			a.Show(
				"so the homogenization over M lies in the ideal over M",
				sameMul.RwRev(),
				sameOne.RwRev(),
				sameConst.RwRev(),
				By(inIdealM))
		}),
})}

// GenericFieldExactConstants — on a curve whose equations generate a prime
// ideal over the algebraically closed M, the members of the generic field
// algebraic over k lie in k. Such a z is F(x)/G(x) for forms F, G over k of
// one degree (FormQuotients), and for a nonzero f over k with f(z) = 0 the
// homogenization Σ f(i)·Fⁱ·G^(m−i), a form over k vanishing at the generic
// point x, lies in the ideal over M (HomogenizationInIdeal). Primality over M
// puts a linear factor F − β·G in it (PrimeHoldsLinearFactor); a k-linear
// retraction π of M onto k carries F − β·G into the ideal over k as
// F − π(β)·G (IdealLinearDescent, RetractionLinearFactor), which vanishes at
// x, and G(x) ≠ 0 leaves z = π(β), a member of k.
var GenericFieldExactConstants = genericFieldExactConstantsThm{family.Add(registry.ProofEntry{
	Name: "GenericFieldExactConstants",
	Reading: "subfield(M, K) is load-bearing: without it the coordinates of a generic " +
		"point may lie off M's carrier, field_adjoin is then ⋂∅, the whole type, and K holds " +
		"values on which M's operations are arbitrary. Primality over M, not over k, is what " +
		"makes the curve geometrically integral and leaves k algebraically closed in K.",
	Key: "prop_795df460e6a10bcd",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n:num. ∀E:set((num → num) → A). ∀z:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"projective_generic_field(M, k, n, E, K)",
			"z ∈ K",
			"algebraic_over(M, k, z)",
		},
		Conclusion: "z ∈ k",
		Abbrev: Abbrev{
			{Name: "overM", Text: "polynomial_algebra_ring(field_ring(M), {i:num | i ≤ n})"},
			{Name: "homogenizedM", Text: "λi:num. " +
				"    COND(i ≤ polynomial_degree(f), " +
				"        polynomial_algebra_mul(field_ring(M), " +
				"            monoid_pow(polynomial_algebra_mul(field_ring(M)), " +
				"                polynomial_algebra_one(field_ring(M)), " +
				"                G, " +
				"                polynomial_degree(f) - i), " +
				"            polynomial_algebra_const(field_ring(M), f(i))), " +
				"        fun_zero)"},
			{Name: "homogenizedMAtF", Text: "polynomial_eval(fun_add, " +
				"    fun_zero, " +
				"    polynomial_algebra_mul(field_ring(M)), " +
				"    polynomial_algebra_one(field_ring(M)), " +
				"    «homogenizedM», " +
				"    F)"},
			{Name: "βG", Text: "polynomial_algebra_mul(field_ring(M), " +
				"    polynomial_algebra_const(field_ring(M), β), " +
				"    G)"},
			{Name: "πβG", Text: "polynomial_algebra_mul(«hilbertCoefficients», " +
				"    polynomial_algebra_const(«hilbertCoefficients», π(β)), " +
				"    G)"},
			{Name: "retractedFactor", Text: "λm:(num → num). π(F(m) - «βG»(m))"},
			{Name: "descendedFactor", Text: "λm:(num → num). F(m) - «πβG»(m)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			z *Expr[A],
			closed, curve, subK, generic, zK, algebraic Fact,
		) {
			subk := a.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			eForms := projective_curve.CurveEquationsForms.Read(curve)
			prime := projective_curve.CurveIdealGeometricallyPrime.Read(curve)
			x, point := a.UnpackAs[Fun[Nat, A]](
				a.Unfolded(generic, projective_curve.ProjectiveGenericFieldDef), "x")
			pointParts := a.Conjuncts(
				point,
				"x is a point of the curve with coordinates in K",
				"K is k(x)",
				"the forms over k vanishing at x are the ideal of E")
			coordinatesK, adjoin, vanishing := pointParts[0], pointParts[1], pointParts[2]
			pointDef := a.Conjuncts(
				a.Unfolded(coordinatesK, projective_curve.ProjectiveEquationPointsDef),
				"the coordinates up to n lie in K",
				"the coordinates past n are zero",
				"the first nonzero coordinate is one",
				"E vanishes at x")
			coordinates := a.Have(
				"the coordinates lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(pointDef[0], subK, field.SubfieldSubset))
			normalized := a.Have(
				"some coordinate is one",
				"∃j:num. j ≤ n ∧ x(j) = M.one",
				By(pointDef[2]))
			zAdjoin := a.Have(
				"z lies in k(x)",
				"z ∈ field_adjoin(M, k, {x(i) | i:num | i ≤ n})",
				By(zK, adjoin))
			d, F, G, quotient := a.Unpack3As[Nat, _Polynomial, _Polynomial](
				GroupPremises(subk, coordinates, normalized, zAdjoin, FormQuotients.Read(M).At(k, n, x, z)),
				"d",
				"F",
				"G")
			quotientParts := a.Conjuncts(
				quotient,
				"F is a form of degree d",
				"G is a form of degree d",
				"G(x) is not zero",
				"z·G(x) = F(x)")
			fForm, gForm, gNonzero, ratio :=
				quotientParts[0], quotientParts[1], quotientParts[2], quotientParts[3]
			f, root := a.UnpackAs[Fun[Nat, A]](a.Unfolded(algebraic, algebraic_element.AlgebraicOverDef), "f")
			rootParts := a.Conjuncts(
				root,
				"f is a polynomial over k",
				"f is not zero",
				"z is a root of f")
			fOverk, fNonzero, fRoot := rootParts[0], rootParts[1], rootParts[2]
			fieldRing := field.RingOn.Read(M)
			coefficients := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
			ringM := a.TermAs[RingOps[A]]("field_ring(M)")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			evaluationAtX := a.TermAs[Fun[_Polynomial, A]](
				"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x)")
			ringk := a.Have(
				"k, a subfield of M, is a commutative ring",
				"comm_ring_on(«hilbertCoefficients»)",
				By(subk, field.SubfieldCommRing.Read(M).At(k)))
			kInM := a.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(subk, field.SubfieldSubset))
			inclusion := a.Have(
				"k includes into M",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					subk,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(fieldRing).At(k)))
			evaluation := a.Have(
				"evaluation at x is a ring map of the polynomials over k into M",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x))",
				By(inclusion, coordinates, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
			formsk := a.Have(
				"the forms are polynomials over k",
				"F ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ∧ "+
					"G ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
				By(
					homogeneous_polynomial.FormPolynomial.Read(fForm),
					homogeneous_polynomial.FormPolynomial.Read(gForm)))
			formsParts := a.Conjuncts(
				formsk,
				"F is a polynomial over k",
				"G is a polynomial over k")
			values := a.Have(
				"F(x) and G(x) lie in M",
				"«at»(F) ∈ M.carrier ∧ «at»(G) ∈ M.carrier",
				By(formsk, ring_homomorphism.MapIn.Read(evaluation)))
			fOverM := a.Have(
				"f is a polynomial over M",
				"polynomial_over(M.carrier, f)",
				By(kInM, fOverk, polynomial.PolynomialOverMono))
			ringPolys := a.Have(
				"the polynomials over k are a commutative ring",
				"comm_ring_on(«polynomials»)",
				By(ringk, polynomial_algebra.PolynomialAlgebraCommRingOn))
			constantsk := a.Have(
				"the constants over k are a ring map",
				"ring_homomorphism(«hilbertCoefficients», "+
					"    «polynomials», "+
					"    polynomial_algebra_const(«hilbertCoefficients»))",
				By(ringk, polynomial_algebra.PolynomialAlgebraConstHom))
			zIn := a.Have(
				"z lies in M",
				"z ∈ M.carrier",
				BySets(zK, field.SubfieldSubset.Read(subK)))
			eOverk := a.Have(
				"E consists of polynomials over k",
				"E ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
				BySets(a.Have(
					"each member of E, a form over k, is a polynomial over k",
					"∀P:((num → num) → A). P ∈ E ⇒ P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					Derive(func(b *Argument) {
						P := b.FixAs[_Polynomial]("P")
						_, form := b.UnpackAs[Nat](eForms.At(b.MemberOf[on.Any](P, b.Assume())), "e")
						b.Show(
							"a form is a polynomial",
							By(homogeneous_polynomial.FormPolynomial.Read(form)))
					}))))
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			vanishingForms := a.Have(
				"a form over k vanishing at the generic point lies in the ideal over k",
				Statement{
					Binders: "∀e:num. ∀P:((num → num) → A).",
					Hypotheses: []string{
						"homogeneous_polynomial(«hilbertCoefficients», n, e, P)",
						"«at»(P) = M.zero",
					},
					Conclusion: "P ∈ ideal_span(«polynomials», E)",
				},
				By(vanishing))
			homogenizedInIdeal := a.Have(
				"the homogenization of f at F over G lies in the ideal over M",
				"«homogenizedMAtF» ∈ ideal_span(«overM», E)",
				By(
					subk,
					coordinates,
					eOverk,
					vanishingForms,
					fForm,
					gForm,
					zIn,
					ratio,
					fOverk,
					fRoot,
					HomogenizationInIdeal.Read(M).AsFact().At(k, n, E, x, d, F, G, z, f)))
			overMOn := a.Have(
				"the polynomials over M are a commutative ring",
				"comm_ring_on(«overM»)",
				By(fieldRing, polynomial_algebra.PolynomialAlgebraCommRingOn))
			constantsM := a.Have(
				"the constants over M are a ring map",
				"ring_homomorphism(field_ring(M), «overM», polynomial_algebra_const(field_ring(M)))",
				By(fieldRing, polynomial_algebra.PolynomialAlgebraConstHom))
			formsM := a.Conjuncts(
				a.Have(
					"F and G are polynomials over M, as every polynomial over k is",
					"F ∈ polynomial_algebra(field_ring(M), {i:num | i ≤ n}) ∧ "+
						"G ∈ polynomial_algebra(field_ring(M), {i:num | i ≤ n})",
					BySets(formsk, kInM, polynomial_algebra.PolynomialAlgebraOverMono.At(ringM, k, variables))),
				"F is a polynomial over M",
				"G is a polynomial over M")
			β, factor := a.UnpackAs[A](
				GroupPremises(
					closed,
					constantsM,
					prime,
					fOverM,
					fNonzero,
					formsM[0],
					formsM[1],
					homogenizedInIdeal,
					Read(algebraic_closure.PrimeHoldsLinearFactor, M, overMOn).AsFact().At(
						a.TermAs[Fun[A, _Polynomial]]("polynomial_algebra_const(field_ring(M))"),
						a.TermAs[Set[_Polynomial]]("ideal_span(«overM», E)"),
						f,
						F,
						G)),
				"β")
			factorParts := a.Conjuncts(
				factor,
				"β lies in M",
				"F − β·G lies in the ideal over M")
			betaIn, linearInIdeal := factorParts[0], factorParts[1]
			π, retraction := a.UnpackAs[Fun[A, A]](
				GroupPremises(subk, field_extension.SubfieldRetraction.Read(M).At(k)),
				"π")
			retractionParts := a.Conjuncts(
				retraction,
				"π is k-linear",
				"π fixes k")
			linear, fixesk := retractionParts[0], retractionParts[1]
			linearFactor := a.TermAs[_Polynomial]("λm:(num → num). F(m) - «βG»(m)")
			retractedInIdeal := a.Have(
				"π carries F − β·G into the ideal over k",
				"«retractedFactor» ∈ ideal_span(«polynomials», E)",
				By(
					subk,
					linear,
					eOverk,
					linearInIdeal,
					polynomial_algebra.IdealLinearDescent.Read(M).At(k, π, variables, E, linearFactor)))
			piBeta := a.Have(
				"π(β) lies in k, so in M",
				"π(β) ∈ k ∧ π(β) ∈ M.carrier",
				By(betaIn, kInM, set_basic.SubsetDef, module_homomorphism.HomIn.Read(linear).AsFact().At(β)))
			kernelSpan := a.Have(
				"the ideal over k vanishes at x, as E does",
				"ideal_span(«polynomials», E) ⊆ "+
					"ring_kernel(M.zero, "+
					"    polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}), "+
					"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x))",
				By(eOverk, pointDef[3], ring_homomorphism.IdealSpanInKernel.Read(evaluation).At(E)))
			retractedVanishes := a.Have(
				"so π(F − β·G) vanishes at x",
				"«at»(«retractedFactor») = M.zero",
				BySets(
					retractedInIdeal,
					kernelSpan,
					ring_homomorphism.RingKernelDef.At(
						a.TermAs[A]("M.zero"),
						a.TermAs[Set[_Polynomial]]("polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"),
						evaluationAtX)))
			retractedIsDescended := a.Have(
				"π(F − β·G) is F − π(β)·G, π being a k-linear retraction onto k and F, G polynomials over k",
				"«retractedFactor» = «descendedFactor»",
				By(
					subk,
					linear,
					fixesk,
					formsParts[0],
					formsParts[1],
					polynomial_algebra.RetractionLinearFactor.Read(M).At(
						k, π, variables, a.MemberOf[on.M](β, betaIn), F, G)))
			constantPiBeta := a.TermAs[_Polynomial]("polynomial_algebra_const(«hilbertCoefficients», π(β))")
			constantPiBetaIn := a.Have(
				"the constant π(β) is a polynomial over k",
				"polynomial_algebra_const(«hilbertCoefficients», π(β)) ∈ "+
					"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
				By(piBeta, ring_homomorphism.MapIn.Read(constantsk).AsFact().At(a.TermAs[A]("π(β)"))))
			productk := a.TermAs[_Polynomial]("«πβG»")
			valueRelation := a.Have(
				"so F(x) − π(β)·G(x) = 0",
				"«at»(F) - π(β) * «at»(G) = M.zero",
				By(
					a.Have(
						"F − π(β)·G vanishes at x",
						"«at»(«descendedFactor») = M.zero",
						retractedIsDescended.RwRev(),
						By(retractedVanishes)),
					formsParts[0],
					formsParts[1],
					piBeta,
					inclusion,
					constantPiBetaIn,
					comm_ring.MulIn.Read(ringPolys).AsFact().At(constantPiBeta, G),
					ring_homomorphism.MapSub.Read(evaluation).AsFact().At(F, productk),
					ring_homomorphism.MapMul.Read(evaluation).AsFact().At(constantPiBeta, G),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
						coefficients, ringM, identity, x, a.TermAs[A]("π(β)"))))
			excess := a.TermAs[A]("z - π(β)")
			valueGX := a.TermAs[A]("«at»(G)")
			product := a.Have(
				"(z − π(β))·G(x) = z·G(x) − π(β)·G(x) = F(x) − π(β)·G(x) = 0",
				"(z - π(β)) * «at»(G) = M.zero",
				ByArith(M, valueRelation, ratio, zIn, piBeta, values))
			differenceIn := a.Have(
				"z − π(β) lies in M",
				"z - π(β) ∈ M.carrier",
				By(zIn, piBeta, comm_ring.SubIn.Read(fieldRing).AsFact().At(z, a.TermAs[A]("π(β)"))))
			cancelled := a.Have(
				"G(x) ≠ 0, so z − π(β) = 0",
				"z - π(β) = M.zero",
				By(product, gNonzero, differenceIn, values, field.MulEqZeroOn.Read(M).AsFact().At(excess, valueGX)))
			equal := a.Have(
				"so z = π(β)",
				"z = π(β)",
				ByArith(M, cancelled, zIn, piBeta))
			a.Show(
				"which lies in k",
				By(Normalized, equal, piBeta))
		}),
})}

// FormQuotients — every member z of the field k(x) generated by the
// coordinates of a point x with x(j) = one is a quotient F(x)/G(x) of two
// forms over k of one degree, G(x) ≠ 0: such quotients are a subfield of M
// holding k (constants over one) and the coordinates (Xᵢ over Xⱼ), since
// F₁/G₁ + F₂/G₂ = (F₁G₂ + G₁F₂)/(G₁G₂), the product is (F₁F₂)/(G₁G₂), the
// negative is (−F)/G and the inverse G/F.
var FormQuotients = formQuotientsThm{family.Add(registry.ProofEntry{
	Name: "FormQuotients",
	Key:  "prop_2f5184f8907022ce",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n:num. ∀x:(num → A). ∀z:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
			"∃j:num. j ≤ n ∧ x(j) = M.one",
			"z ∈ field_adjoin(M, k, {x(i) | i:num | i ≤ n})",
		},
		Conclusion: "∃d:num. ∃F G:((num → num) → A). " +
			"    homogeneous_polynomial(«hilbertCoefficients», n, d, F) ∧ " +
			"    homogeneous_polynomial(«hilbertCoefficients», n, d, G) ∧ " +
			"    «at»(G) ≠ M.zero ∧ " +
			"    z * «at»(G) = «at»(F)",
		Abbrev: Abbrev{
			{Name: "quotients", Text: "{w:A | " +
				"    w ∈ M.carrier ∧ " +
				"    ∃d:num. ∃F G:((num → num) → A). " +
				"        homogeneous_polynomial(«hilbertCoefficients», n, d, F) ∧ " +
				"        homogeneous_polynomial(«hilbertCoefficients», n, d, G) ∧ " +
				"        «at»(G) ≠ M.zero ∧ " +
				"        w * «at»(G) = «at»(F)}"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			n *Expr[Nat],
			x *Arrow[Nat, A],
			z *Expr[A],
			subk, coordinates, normalized, zIn Fact,
		) {
			j, unit := a.UnpackAs[Nat](normalized, "j")
			unitParts := a.Conjuncts(
				unit,
				"j indexes a coordinate",
				"x(j) is one")
			fieldRing := field.RingOn.Read(M)
			coefficients := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
			ringM := a.TermAs[RingOps[A]]("field_ring(M)")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			ringk := a.Have(
				"k, a subfield of M, is a commutative ring",
				"comm_ring_on(«hilbertCoefficients»)",
				By(subk, field.SubfieldCommRing.Read(M).At(k)))
			kInM := a.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(subk, field.SubfieldSubset))
			inclusion := a.Have(
				"k includes into M",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					subk,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(fieldRing).At(k)))
			evaluation := a.Have(
				"evaluation at x is a ring map of the polynomials over k into M",
				"ring_homomorphism(«polynomials», "+
					"    field_ring(M), "+
					"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x))",
				By(inclusion, coordinates, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
			formsArePolynomials := a.Have(
				"a form is a polynomial over k",
				Statement{
					Binders:    "∀d:num. ∀P:((num → num) → A).",
					Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, P)"},
					Conclusion: "P ∈ «polynomials».carrier",
				},
				By(homogeneous_polynomial.FormPolynomial))
			values := a.Have(
				"a form takes its value at x in M",
				Statement{
					Binders:    "∀d:num. ∀P:((num → num) → A).",
					Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d, P)"},
					Conclusion: "«at»(P) ∈ M.carrier",
				},
				By(formsArePolynomials, ring_homomorphism.MapIn.Read(evaluation)))
			intro := a.Have(
				"w is a quotient once w·G(x) = F(x) for forms F, G of one degree with G(x) ≠ 0",
				Statement{
					Binders: "∀w:A. ∀d:num. ∀F G:((num → num) → A).",
					Hypotheses: []string{
						"w ∈ M.carrier",
						"homogeneous_polynomial(«hilbertCoefficients», n, d, F)",
						"homogeneous_polynomial(«hilbertCoefficients», n, d, G)",
						"«at»(G) ≠ M.zero",
						"w * «at»(G) = «at»(F)",
					},
					Conclusion: "w ∈ «quotients»",
				},
				BySets())
			asQuotient := a.Have(
				"a quotient w is F(x)/G(x) for forms F, G of one degree with G(x) ≠ 0, w, F(x) and G(x) lying in M",
				Statement{
					Binders:    "∀w:A.",
					Hypotheses: []string{"w ∈ «quotients»"},
					Conclusion: "∃d:num. ∃F G:((num → num) → A). " +
						"    homogeneous_polynomial(«hilbertCoefficients», n, d, F) ∧ " +
						"    homogeneous_polynomial(«hilbertCoefficients», n, d, G) ∧ " +
						"    «at»(G) ≠ M.zero ∧ " +
						"    w * «at»(G) = «at»(F) ∧ " +
						"    w ∈ M.carrier ∧ " +
						"    «at»(F) ∈ M.carrier ∧ " +
						"    «at»(G) ∈ M.carrier",
				},
				By(values))
			one := a.TermAs[_Polynomial]("polynomial_algebra_const(«hilbertCoefficients», M.one)")
			oneIn := a.Have(
				"one lies in k",
				"M.one ∈ k",
				By(subk, field.SubfieldOne))
			oneForm := a.Have(
				"the constant one is a form of degree zero with value one",
				"homogeneous_polynomial(«hilbertCoefficients», "+
					"    n, "+
					"    0, "+
					"    polynomial_algebra_const(«hilbertCoefficients», M.one)) ∧ "+
					"«at»(polynomial_algebra_const(«hilbertCoefficients», M.one)) = M.one",
				By(
					ringk,
					oneIn,
					inclusion,
					homogeneous_polynomial.FormConstant.At(coefficients, n, a.TermAs[A]("M.one")),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
						coefficients, ringM, identity, x, a.TermAs[A]("M.one"))))
			constantQuotients := a.Have(
				"a member c of k is the quotient of the constants c and one",
				"∀c:A. c ∈ k ⇒ c ∈ «quotients»",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					cIn := b.Assume()
					cM := b.Have(
						"c lies in M",
						"c ∈ M.carrier",
						By(cIn, kInM, set_basic.SubsetDef))
					b.Show(
						"c·1 = c",
						By(
							cIn,
							cM,
							oneForm,
							inclusion,
							field.OneNotZeroOn.Read(M),
							ringk,
							homogeneous_polynomial.FormConstant.At(coefficients, n, c),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(coefficients, ringM, identity, x, c),
							comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(fieldRing)).AsFact().At(c),
							intro.At(
								c,
								b.TermAs[Nat]("0"),
								b.TermAs[_Polynomial]("polynomial_algebra_const(«hilbertCoefficients», c)"),
								one)))
				}))
			coordinateQuotients := a.Have(
				"a coordinate x(i) is the quotient of the variables Xᵢ and Xⱼ, x(j) being one",
				"∀w:A. w ∈ {x(i) | i:num | i ≤ n} ⇒ w ∈ «quotients»",
				Derive(func(b *Argument) {
					b.FixAs[A]("w")
					i, at := b.UnpackAs[Nat](b.Assume(), "i")
					atParts := b.Conjuncts(
						at,
						"i indexes a coordinate",
						"w is x(i)")
					xi := b.TermAs[A]("x(i)")
					xiM := b.Have(
						"x(i) lies in M",
						"x(i) ∈ M.carrier",
						By(atParts[0], coordinates.At(i)))
					b.Show(
						"x(i)·x(j) = x(i)",
						By(
							atParts[0],
							atParts[1],
							unitParts[0],
							unitParts[1],
							xiM,
							coordinates.At(j),
							inclusion,
							field.OneNotZeroOn.Read(M),
							ringk,
							homogeneous_polynomial.FormVariable.At(coefficients, n, i),
							homogeneous_polynomial.FormVariable.At(coefficients, n, j),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(coefficients, ringM, identity, x, i),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(coefficients, ringM, identity, x, j),
							comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(fieldRing)).AsFact().At(xi),
							intro.At(
								xi,
								b.TermAs[Nat]("1"),
								b.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», i)"),
								b.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», j)"))))
				}))
			inCarrier := a.Have(
				"the quotients lie in M",
				"«quotients» ⊆ M.carrier",
				By(set_basic.SubsetDef))
			zeroQ := a.Have(
				"zero is a quotient",
				"M.zero ∈ «quotients»",
				By(subk, field.SubfieldZero, constantQuotients))
			oneQ := a.Have(
				"so is one",
				"M.one ∈ «quotients»",
				By(oneIn, constantQuotients))
			sums := a.Have(
				"F₁/G₁ + F₂/G₂ is (F₁G₂ + G₁F₂)/(G₁G₂)",
				"∀u v:A. u ∈ «quotients» ∧ v ∈ «quotients» ⇒ u + v ∈ «quotients»",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					v := b.FixAs[A]("v")
					both := b.Conjuncts(
						b.Assume(),
						"u is a quotient",
						"v is a quotient")
					d1, F1, G1, uq := b.Unpack3As[Nat, _Polynomial, _Polynomial](
						GroupPremises(both[0], asQuotient.At(u)), "d₁", "F₁", "G₁")
					d2, F2, G2, vq := b.Unpack3As[Nat, _Polynomial, _Polynomial](
						GroupPremises(both[1], asQuotient.At(v)), "d₂", "F₂", "G₂")
					uf := b.Conjuncts(
						uq,
						"F₁ is a form",
						"G₁ is a form",
						"G₁(x) is not zero",
						"u·G₁(x) = F₁(x)",
						"u lies in M",
						"F₁(x) lies in M",
						"G₁(x) lies in M")
					vf := b.Conjuncts(
						vq,
						"F₂ is a form",
						"G₂ is a form",
						"G₂(x) is not zero",
						"v·G₂(x) = F₂(x)",
						"v lies in M",
						"F₂(x) lies in M",
						"G₂(x) lies in M")
					d := b.TermAs[Nat]("d₁ + d₂")
					f1g2 := b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», F₁, G₂)")
					g1f2 := b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», G₁, F₂)")
					g1g2 := b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», G₁, G₂)")
					products := b.Have(
						"F₁G₂, G₁F₂ and G₁G₂ are forms of degree d₁ + d₂",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d₁ + d₂, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», F₁, G₂)) ∧ "+
							"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d₁ + d₂, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», G₁, F₂)) ∧ "+
							"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d₁ + d₂, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», G₁, G₂))",
						By(
							uf[0],
							uf[1],
							vf[0],
							vf[1],
							ringk,
							homogeneous_polynomial.FormProduct.At(coefficients, n, d1, d2, F1, G2),
							homogeneous_polynomial.FormProduct.At(coefficients, n, d1, d2, G1, F2),
							homogeneous_polynomial.FormProduct.At(coefficients, n, d1, d2, G1, G2)))
					pf := b.Conjuncts(
						products,
						"F₁G₂ is a form",
						"G₁F₂ is a form",
						"G₁G₂ is a form")
					evaluated := b.Have(
						"their values at x",
						"«at»(polynomial_algebra_mul(«hilbertCoefficients», G₁, G₂)) = «at»(G₁) * «at»(G₂) ∧ "+
							"«at»(fun_add(polynomial_algebra_mul(«hilbertCoefficients», F₁, G₂), "+
							"        polynomial_algebra_mul(«hilbertCoefficients», G₁, F₂))) = "+
							"«at»(F₁) * «at»(G₂) + «at»(G₁) * «at»(F₂)",
						By(
							formsArePolynomials.At(d1, F1),
							formsArePolynomials.At(d1, G1),
							formsArePolynomials.At(d2, F2),
							formsArePolynomials.At(d2, G2),
							formsArePolynomials.At(d, f1g2),
							formsArePolynomials.At(d, g1f2),
							uf[0],
							uf[1],
							vf[0],
							vf[1],
							pf[0],
							pf[1],
							ring_homomorphism.MapMul.Read(evaluation).AsFact().At(G1, G2),
							ring_homomorphism.MapMul.Read(evaluation).AsFact().At(F1, G2),
							ring_homomorphism.MapMul.Read(evaluation).AsFact().At(G1, F2),
							ring_homomorphism.MapAdd.Read(evaluation).AsFact().At(f1g2, g1f2)))
					nonzero := b.Have(
						"G₁(x)G₂(x) is not zero",
						"«at»(G₁) * «at»(G₂) ≠ M.zero",
						By(uf[6], vf[6], uf[2], vf[2], field.MulEqZeroOn.Read(M)))
					valueParts := b.Conjuncts(
						evaluated,
						"the value of G₁G₂",
						"the value of F₁G₂ + G₁F₂")
					sumRelation := b.Have(
						"(u + v)·G₁(x)G₂(x) = F₁(x)G₂(x) + G₁(x)F₂(x)",
						"(u + v) * «at»(polynomial_algebra_mul(«hilbertCoefficients», G₁, G₂)) = "+
							"«at»(fun_add(polynomial_algebra_mul(«hilbertCoefficients», F₁, G₂), "+
							"        polynomial_algebra_mul(«hilbertCoefficients», G₁, F₂)))",
						valueParts[0].Rw(),
						valueParts[1].Rw(),
						ByArith(
							M,
							uf[4],
							vf[4],
							uf[5],
							uf[6],
							vf[5],
							vf[6],
							Scaled(b.TermAs[A]("«at»(G₂)"), uf[3]),
							Scaled(b.TermAs[A]("«at»(G₁)"), vf[3])))
					b.Show(
						"so u + v is a quotient, F₁G₂ + G₁F₂ being a form of degree d₁ + d₂",
						By(
							uf[4],
							vf[4],
							ringk,
							pf[0],
							pf[1],
							homogeneous_polynomial.FormSum.At(coefficients, n, d, f1g2, g1f2),
							pf[2],
							nonzero,
							valueParts[0],
							sumRelation,
							comm_ring.AddIn.Read(fieldRing),
							intro.At(
								b.TermAs[A]("u + v"),
								d,
								b.TermAs[_Polynomial](
									"fun_add(polynomial_algebra_mul(«hilbertCoefficients», F₁, G₂), "+
										"    polynomial_algebra_mul(«hilbertCoefficients», G₁, F₂))"),
								g1g2)))
				}))
			products := a.Have(
				"F₁/G₁ · F₂/G₂ is (F₁F₂)/(G₁G₂)",
				"∀u v:A. u ∈ «quotients» ∧ v ∈ «quotients» ⇒ u * v ∈ «quotients»",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					v := b.FixAs[A]("v")
					both := b.Conjuncts(
						b.Assume(),
						"u is a quotient",
						"v is a quotient")
					d1, F1, G1, uq := b.Unpack3As[Nat, _Polynomial, _Polynomial](
						GroupPremises(both[0], asQuotient.At(u)), "d₁", "F₁", "G₁")
					d2, F2, G2, vq := b.Unpack3As[Nat, _Polynomial, _Polynomial](
						GroupPremises(both[1], asQuotient.At(v)), "d₂", "F₂", "G₂")
					uf := b.Conjuncts(
						uq,
						"F₁ is a form",
						"G₁ is a form",
						"G₁(x) is not zero",
						"u·G₁(x) = F₁(x)",
						"u lies in M",
						"F₁(x) lies in M",
						"G₁(x) lies in M")
					vf := b.Conjuncts(
						vq,
						"F₂ is a form",
						"G₂ is a form",
						"G₂(x) is not zero",
						"v·G₂(x) = F₂(x)",
						"v lies in M",
						"F₂(x) lies in M",
						"G₂(x) lies in M")
					d := b.TermAs[Nat]("d₁ + d₂")
					f1f2 := b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», F₁, F₂)")
					g1g2 := b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», G₁, G₂)")
					forms := b.Have(
						"F₁F₂ and G₁G₂ are forms of degree d₁ + d₂",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d₁ + d₂, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», F₁, F₂)) ∧ "+
							"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d₁ + d₂, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», G₁, G₂))",
						By(
							uf[0],
							uf[1],
							vf[0],
							vf[1],
							ringk,
							homogeneous_polynomial.FormProduct.At(coefficients, n, d1, d2, F1, F2),
							homogeneous_polynomial.FormProduct.At(coefficients, n, d1, d2, G1, G2)))
					evaluated := b.Have(
						"their values at x are the products of the values",
						"«at»(polynomial_algebra_mul(«hilbertCoefficients», F₁, F₂)) = «at»(F₁) * «at»(F₂) ∧ "+
							"«at»(polynomial_algebra_mul(«hilbertCoefficients», G₁, G₂)) = «at»(G₁) * «at»(G₂)",
						By(
							formsArePolynomials.At(d1, F1),
							formsArePolynomials.At(d1, G1),
							formsArePolynomials.At(d2, F2),
							formsArePolynomials.At(d2, G2),
							uf[0],
							uf[1],
							vf[0],
							vf[1],
							ring_homomorphism.MapMul.Read(evaluation).AsFact().At(F1, F2),
							ring_homomorphism.MapMul.Read(evaluation).AsFact().At(G1, G2)))
					valueParts := b.Conjuncts(
						evaluated,
						"the value of F₁F₂",
						"the value of G₁G₂")
					nonzero := b.Have(
						"G₁(x)G₂(x) is not zero",
						"«at»(G₁) * «at»(G₂) ≠ M.zero",
						By(uf[6], vf[6], uf[2], vf[2], field.MulEqZeroOn.Read(M)))
					productRelation := b.Have(
						"u·v·G₁(x)G₂(x) = F₁(x)F₂(x)",
						"u * v * «at»(polynomial_algebra_mul(«hilbertCoefficients», G₁, G₂)) = "+
							"«at»(polynomial_algebra_mul(«hilbertCoefficients», F₁, F₂))",
						valueParts[0].Rw(),
						valueParts[1].Rw(),
						ByArith(
							M,
							uf[4],
							vf[4],
							uf[5],
							uf[6],
							vf[5],
							vf[6],
							Scaled(b.TermAs[A]("v * «at»(G₂)"), uf[3]),
							Scaled(b.TermAs[A]("«at»(F₁)"), vf[3])))
					formParts := b.Conjuncts(
						forms,
						"F₁F₂ is a form",
						"G₁G₂ is a form")
					b.Show(
						"so u·v is a quotient",
						By(
							uf[4],
							vf[4],
							formParts[0],
							formParts[1],
							nonzero,
							valueParts[1],
							productRelation,
							comm_ring.MulIn.Read(fieldRing),
							intro.At(b.TermAs[A]("u * v"), d, f1f2, g1g2)))
				}))
			negatives := a.Have(
				"−(F/G) is (−F)/G, −F being a form of the degree of F",
				"∀u:A. u ∈ «quotients» ⇒ M.neg(u) ∈ «quotients»",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					d1, F1, G1, uq := b.Unpack3As[Nat, _Polynomial, _Polynomial](
						GroupPremises(b.Assume(), asQuotient.At(u)), "d", "F", "G")
					uf := b.Conjuncts(
						uq,
						"F is a form",
						"G is a form",
						"G(x) is not zero",
						"u·G(x) = F(x)",
						"u lies in M",
						"F(x) lies in M",
						"G(x) lies in M")
					negF := b.TermAs[_Polynomial]("fun_neg(F)")
					value := b.Have(
						"the value of −F at x is −F(x)",
						"«at»(fun_neg(F)) = M.neg(«at»(F))",
						By(
							uf[0],
							formsArePolynomials.At(d1, F1),
							ring_homomorphism.MapNeg.Read(evaluation).AsFact().At(F1)))
					negativeRelation := b.Have(
						"(−u)·G(x) = −F(x)",
						"M.neg(u) * «at»(G) = «at»(fun_neg(F))",
						value.Rw(),
						ByArith(M, uf[4], uf[5], uf[6], uf[3]))
					b.Show(
						"so −u is a quotient",
						By(
							uf[4],
							uf[0],
							uf[1],
							uf[2],
							ringk,
							homogeneous_polynomial.FormNeg.At(coefficients, n, d1, F1),
							negativeRelation,
							comm_ring.NegIn.Read(fieldRing),
							intro.At(b.TermAs[A]("M.neg(u)"), d1, negF, G1)))
				}))
			inverses := a.Have(
				"the inverse of F/G is G/F, and that of zero is zero",
				"∀u:A. u ∈ «quotients» ⇒ M.inv(u) ∈ «quotients»",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					uIn := b.Assume()
					b.Cases(b.TermAs[Bool]("u = M.zero"))
					b.When(
						"the inverse of zero is zero",
						func(c *Argument, zero Fact) {
							c.Show(
								"a quotient",
								By(zero, zeroQ, field.InvZeroOn.Read(M)))
						})
					b.Otherwise(
						"otherwise F(x) is not zero either",
						func(c *Argument, nonzeroU Fact) {
							d1, F1, G1, uq := c.Unpack3As[Nat, _Polynomial, _Polynomial](
								GroupPremises(uIn, asQuotient.At(u)), "d", "F", "G")
							uf := c.Conjuncts(
								uq,
								"F is a form",
								"G is a form",
								"G(x) is not zero",
								"u·G(x) = F(x)",
								"u lies in M",
								"F(x) lies in M",
								"G(x) lies in M")
							inverseIn := c.Have(
								"u⁻¹ lies in M",
								"M.inv(u) ∈ M.carrier",
								By(uf[4], field.InvIn.Read(M)))
							numeratorNonzero := c.Have(
								"F(x) = u·G(x) is not zero",
								"«at»(F) ≠ M.zero",
								By(uf[4], uf[6], uf[2], uf[3], nonzeroU, field.MulEqZeroOn.Read(M)))
							inverse := c.Have(
								"u⁻¹·u is one",
								"M.inv(u) * u = M.one",
								By(uf[4], nonzeroU, field.MulLeftInverseOn.Read(M)))
							inverseRelation := c.Have(
								"u⁻¹·F(x) = u⁻¹·u·G(x) = G(x)",
								"M.inv(u) * «at»(F) = «at»(G)",
								ByArith(
									M,
									uf[4],
									uf[5],
									uf[6],
									inverseIn,
									Scaled(c.TermAs[A]("M.inv(u)"), uf[3]),
									Scaled(c.TermAs[A]("«at»(G)"), inverse)))
							c.Show(
								"so u⁻¹ is G(x)/F(x)",
								By(
									inverseIn,
									uf[0],
									uf[1],
									numeratorNonzero,
									inverseRelation,
									intro.At(c.TermAs[A]("M.inv(u)"), d1, G1, F1)))
						})
				}))
			subfield := a.Have(
				"the quotients are a subfield of M",
				"subfield(M, «quotients»)",
				By(field.SubfieldDef, inCarrier, zeroQ, oneQ, sums, negatives, products, inverses))
			kQ := a.Have(
				"they hold k",
				"k ⊆ «quotients»",
				By(constantQuotients, set_basic.SubsetDef))
			xQ := a.Have(
				"and the coordinates",
				"{x(i) | i:num | i ≤ n} ⊆ «quotients»",
				By(coordinateQuotients, set_basic.SubsetDef))
			within := a.Have(
				"so they hold k(x)",
				"field_adjoin(M, k, {x(i) | i:num | i ≤ n}) ⊆ «quotients»",
				By(
					subfield,
					kQ,
					xQ,
					algebraic_element.AdjoinLeast.Read(M).AsFact().At(
						k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"), a.TermAs[Set[A]]("«quotients»"))))
			a.Show(
				"so z, lying in k(x), is a quotient",
				By(zIn, within, set_basic.SubsetDef))
		}),
})}
