// binary_form.go — a binary form over an algebraically closed field factors
// into linear forms, so a prime ideal holding its value at a pair (a, b) of a
// commutative ring holds one of the linear factors a − β·b.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PrimeHoldsLinearFactor — for f over an algebraically closed field M of
// degree m and a ring map ι of M into R, a prime ideal of R holding the
// binary form Σ ι(f(i))·aⁱ·b^(m−i) holds a − ι(β)·b for some β in M: by
// induction on the degree, f has a root β in M and is (x − β)·q, the form of
// f is (a − ι(β)·b) times the form of q, and primality puts one factor in
// the ideal; a nonzero constant maps to a unit, which no prime ideal holds.
var PrimeHoldsLinearFactor = primeHoldsLinearFactorThm{family.Add(registry.ProofEntry{
	Name: "PrimeHoldsLinearFactor",
	Key:  "prop_aad633f23bda439a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀R:comm_ring_on(B). ∀ι:(A → B). ∀P:set(B). ∀f:(num → A). ∀a b:B.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"ring_homomorphism(field_ring(M), R, ι)",
			"prime_ideal(R, P)",
			"polynomial_over(M.carrier, f)",
			"f ≠ vec_zero(M.zero)",
			"a ∈ R.carrier",
			"b ∈ R.carrier",
			"polynomial_eval(«homogenized», a) ∈ P",
		},
		Conclusion: "∃β:A. β ∈ M.carrier ∧ a - ι(β) * b ∈ P",
		Abbrev: Abbrev{
			{Name: "homogenized", Text: "λi:num. " +
				"    COND(i ≤ polynomial_degree(f), " +
				"        monoid_pow(R.mul, R.one, b, polynomial_degree(f) - i) * ι(f(i)), " +
				"        R.zero)"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			R comm_ring.CommRingFact[on.R],
			ι *Arrow[A, B],
			P *Expr[Set[B]],
			f *Arrow[Nat, A],
			a, b *Expr[B],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"M is algebraically closed",
				"ι is a ring map",
				"P is prime",
				"f is a polynomial over M",
				"f is not zero",
				"a lies in R",
				"b lies in R",
				"P holds the binary form of f at (a, b)")
			closed, hom, prime, fOver, fNonzero, aIn, bIn, value :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], parts[6], parts[7]
			ringM := field.RingOn.Read(M)
			mulMonoid := comm_ring.MulMonoidOn.Read(R)
			domain := integral_domain.FieldIntegralDomain.Read(M)
			ringRTerm := arg.Term("R")
			byDegree := arg.Have(
				"by induction on the degree m, a nonzero polynomial over M of "+
					"degree m whose binary form lies in P gives a linear factor in P",
				Statement{
					Binders: "∀m:num. ∀h:(num → A).",
					Hypotheses: []string{
						"polynomial_over(M.carrier, h)",
						"h ≠ vec_zero(M.zero)",
						"polynomial_degree(h) = m",
						"polynomial_eval(λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(h(i)), R.zero), a) ∈ P",
					},
					Conclusion: "∃β:A. β ∈ M.carrier ∧ a - ι(β) * b ∈ P",
				},
				Derive(func(c *Argument) {
					c.Induct("m")
					c.Base(
						"a nonzero constant maps to a unit, which the proper ideal P does not hold",
						func(d *Argument) {
							d.FixAs[Fun[Nat, A]]("h")
							given := d.Conjuncts(
								d.Assume(),
								"h is a polynomial over M",
								"h is not zero",
								"h has degree zero",
								"P holds its binary form")
							hOver, hNonzero, hDegree, hValue := given[0], given[1], given[2], given[3]
							leading := d.Have(
								"so its constant coefficient is not zero",
								"h(0) ≠ M.zero",
								By(hOver, hNonzero, hDegree, polynomial.DegreeLeading))
							weights := d.Have(
								"its weighted coefficients lie in R and vanish from 1 on",
								"∀i:num. "+
									"    COND(i ≤ 0, monoid_pow(R.mul, R.one, b, 0 - i) * ι(h(i)), R.zero) ∈ R.carrier ∧ "+
									"    (1 ≤ i ⇒ COND(i ≤ 0, monoid_pow(R.mul, R.one, b, 0 - i) * ι(h(i)), R.zero) = R.zero)",
								Derive(func(e *Argument) {
									e.FixAs[Nat]("i")
									coefficient := e.Have(
										"h(i) lies in M",
										"h(i) ∈ M.carrier",
										By(hOver, polynomial.PolynomialOverDef))
									e.Show(
										"a power of b times the image of h(i), or zero",
										SplitConj(
											Case(
												"in R",
												By(
													coefficient,
													bIn,
													ring_homomorphism.MapIn.Read(hom),
													comm_monoid.PowIn.Read(mulMonoid),
													comm_ring.MulIn.Read(R),
													comm_ring.ZeroIn.Read(R))),
											Case(
												"and zero from 1 on",
												ByArith())))
								}))
							constantVec := d.Have(
								"so the weighted polynomial is a constant",
								"vec⟨1⟩(λi:num. COND(i ≤ 0, monoid_pow(R.mul, R.one, b, 0 - i) * ι(h(i)), R.zero))",
								By(weights, vec_space.VecDef))
							constantOver := d.Have(
								"a polynomial over R",
								"polynomial_over(R.carrier, "+
									"    λi:num. COND(i ≤ 0, monoid_pow(R.mul, R.one, b, 0 - i) * ι(h(i)), R.zero))",
								By(weights, constantVec, polynomial.PolynomialOverDef))
							evaluated := d.Have(
								"whose value at a is its constant coefficient",
								"polynomial_eval(λi:num. COND(i ≤ 0, monoid_pow(R.mul, R.one, b, 0 - i) * ι(h(i)), R.zero), a) = "+
									"COND(0 ≤ 0, monoid_pow(R.mul, R.one, b, 0 - 0) * ι(h(0)), R.zero)",
								By(
									constantOver,
									constantVec,
									aIn,
									polynomial.DegreeZeroIff,
									polynomial_evaluation.DegreeZeroEval.Read(R)))
							members := d.Have(
								"h(0), its image and the image of its inverse lie where they should",
								"h(0) ∈ M.carrier ∧ ι(h(0)) ∈ R.carrier ∧ ι(M.inv(h(0))) ∈ R.carrier",
								By(hOver, polynomial.PolynomialOverDef, field.InvIn.Read(M), ring_homomorphism.MapIn.Read(hom)))
							constant := d.Have(
								"the constant coefficient is ι(h(0)), b⁰ being one",
								"COND(0 ≤ 0, monoid_pow(R.mul, R.one, b, 0 - 0) * ι(h(0)), R.zero) = ι(h(0))",
								ByArith(R, members, comm_monoid.MonoidPowDef))
							inP := d.Have(
								"so P holds ι(h(0))",
								"ι(h(0)) ∈ P",
								By(hValue, evaluated, constant))
							h0 := d.TermAs[A]("h(0)")
							one := d.Have(
								"and one is ι(h(0)⁻¹)·ι(h(0))",
								"R.one = ι(M.inv(h(0))) * ι(h(0))",
								By(
									members,
									leading,
									ring_homomorphism.MapOne.Read(hom),
									ring_homomorphism.MapMul.Read(hom).AsFact().At(d.TermAs[A]("M.inv(h(0))"), h0),
									field.MulLeftInverseOn.Read(M).AsFact().At(h0),
									field.InvIn.Read(M).AsFact().At(h0)))
							d.Show(
								"which would put one in the proper ideal P",
								By(
									inP,
									one,
									members,
									prime,
									ring_ideal.PrimeIdealIdeal,
									ring_ideal.PrimeIdealProper,
									At(ring_ideal.IdealMul, ringRTerm, P, d.TermAs[B]("ι(M.inv(h(0)))"), d.TermAs[B]("ι(h(0))"))))
						})
					c.Step(
						"a polynomial of positive degree has a root β in M; "+
							"its form is (a − ι(β)·b) times that of the cofactor",
						func(d *Argument, ih Fact) {
							d.FixAs[Fun[Nat, A]]("h")
							given := d.Conjuncts(
								d.Assume(),
								"h is a polynomial over M",
								"h is not zero",
								"h has degree m + 1",
								"P holds its binary form")
							hOver, hNonzero, hDegree, hValue := given[0], given[1], given[2], given[3]
							r, root := d.ObtainAs[A](
								"M being algebraically closed, h has a root r in M",
								"∃r:A. r ∈ M.carrier ∧ polynomial_eval(h, r) = M.zero",
								ByArith(closed, hOver, hDegree, AlgebraicallyClosedDef))
							rootParts := d.Conjuncts(
								root,
								"r lies in M",
								"r is a root of h")
							rIn := rootParts[0]
							rMember := d.MemberOf[on.M](r, rIn)
							q, quotient := d.ObtainAs[Fun[Nat, A]](
								"so h is (x − r)·q for a nonzero q over M one degree lower",
								"∃q:(num → A). "+
									"    polynomial_over(M.carrier, q) ∧ "+
									"    q ≠ vec_zero(M.zero) ∧ "+
									"    h = "+
									"    polynomial_mul(vec_sub(basis_vector(M.zero, M.one, 1), "+
									"            vec_scalar_mul(r, basis_vector(M.zero, M.one, 0))), "+
									"        q) ∧ "+
									"    polynomial_degree(h) = suc(polynomial_degree(q))",
								By(
									hOver,
									hNonzero,
									rootParts[1],
									polynomial_roots.RootFactorization.Read(domain).At(d.TermAs[Fun[Nat, A]]("h"), rMember)))
							qParts := d.Conjuncts(
								quotient,
								"q is a polynomial over M",
								"q is not zero",
								"h is (x − r)·q",
								"h is one degree above q")
							qOver, qNonzero, hIsProduct, degreeStep := qParts[0], qParts[1], qParts[2], qParts[3]
							linearM := d.TermAs[Fun[Nat, A]](
								"vec_sub(basis_vector(M.zero, M.one, 1), vec_scalar_mul(r, basis_vector(M.zero, M.one, 0)))")
							mapsIn := ring_homomorphism.MapIn.Read(hom)
							factorsIn := d.Have(
								"the coefficients of x − r and of q lie in M",
								"∀n:num. "+
									"    vec_sub(basis_vector(M.zero, M.one, 1), "+
									"        vec_scalar_mul(r, basis_vector(M.zero, M.one, 0)), "+
									"        n) ∈ "+
									"    M.carrier ∧ "+
									"    q(n) ∈ M.carrier",
								By(rIn, qOver, polynomial.PolynomialOverDef, polynomial_roots.LinearFactor.Read(ringM).At(rMember)))
							convolution := d.Have(
								"ι, a ring map, carries the product (x − r)·q coefficientwise to the product of the images",
								"(λn:num. "+
									"    ι(polynomial_mul(vec_sub(basis_vector(M.zero, M.one, 1), "+
									"                vec_scalar_mul(r, basis_vector(M.zero, M.one, 0))), "+
									"            q, "+
									"            n))) = "+
									"polynomial_mul(λi:num. "+
									"        ι(vec_sub(basis_vector(M.zero, M.one, 1), "+
									"                vec_scalar_mul(r, basis_vector(M.zero, M.one, 0)), "+
									"                i)), "+
									"    λi:num. ι(q(i)))",
								By(
									R,
									ringM,
									hom,
									factorsIn,
									At(polynomial.ConvolutionRingMap, d.Term("field_ring(M)"), ringRTerm, ι, linearM, q)))
							imageOfH := d.Have(
								"so the image of h is (x − ι(r)) times the image of q, ι carrying x − r to x − ι(r)",
								"(λi:num. ι(h(i))) = "+
									"polynomial_mul(vec_sub(basis_vector(R.zero, R.one, 1), "+
									"        vec_scalar_mul(ι(r), basis_vector(R.zero, R.one, 0))), "+
									"    λi:num. ι(q(i)))",
								hIsProduct.Rw(),
								convolution.Rw(),
								By(
									hom,
									rIn,
									polynomial_roots.LinearFactorMap.At(
										d.TermAs[RingOps[A]]("field_ring(M)"), d.TermAs[RingOps[B]]("R"), ι, r)))
							facts := d.Conjuncts(
								d.Have(
									"q has degree m, and ι keeps zero and maps M into R",
									"polynomial_degree(q) = m ∧ "+
										"ι(M.zero) = R.zero ∧ "+
										"(∀x:A. x ∈ M.carrier ⇒ ι(x) ∈ R.carrier) ∧ "+
										"ι(r) ∈ R.carrier",
									ByArith(hDegree, degreeStep, rIn, ring_homomorphism.MapZero.Read(hom), mapsIn)),
								"q has degree m",
								"ι keeps zero",
								"ι maps M into R",
								"ι(r) lies in R")
							qDegree, keepsZero, mapsInto, rImage := facts[0], facts[1], facts[2], facts[3]
							imageQ := d.TermAs[Fun[Nat, B]]("λi:num. ι(q(i))")
							mappedOver := d.Have(
								"the image of q is a polynomial over R",
								"polynomial_over(R.carrier, λi:num. ι(q(i)))",
								By(
									qOver,
									keepsZero,
									mapsInto,
									polynomial.PolynomialOverMap.At(
										ι,
										d.TermAs[A]("M.zero"),
										d.TermAs[B]("R.zero"),
										d.TermAs[Set[A]]("M.carrier"),
										d.TermAs[Set[B]]("R.carrier"),
										q)))
							qPast := d.Have(
								"q vanishes past m",
								"vec⟨suc(m)⟩(q)",
								By(
									Normalized,
									qOver,
									qDegree,
									polynomial.DegreeVec.At(d.TermAs[A]("M.zero"), d.TermAs[Set[A]]("M.carrier"), q)))
							mappedPast := d.Have(
								"and so does its image",
								"vec⟨suc(m)⟩(λi:num. ι(q(i)))",
								Simp(Fwd(vec_space.VecDef)),
								Derive(func(e *Argument) {
									e.FixAs[Nat]("i")
									past := e.Assume()
									e.Show(
										"ι keeps zero",
										By(qPast, keepsZero, past, vec_space.VecDef))
								}))
							mappedDegree := d.Have(
								"so the image of q has degree at most m",
								"polynomial_degree(λi:num. ι(q(i))) ≤ m",
								By(mappedPast, polynomial.DegreeLeast))
							rescaled := d.Have(
								"weighting the coefficients by the powers of b turns x − ι(r) into x − ι(r)·b",
								"(λi:num. "+
									"    COND(i ≤ suc(m), "+
									"        monoid_pow(R.mul, R.one, b, suc(m) - i) * "+
									"        polynomial_mul(vec_sub(basis_vector(R.zero, R.one, 1), "+
									"                vec_scalar_mul(ι(r), basis_vector(R.zero, R.one, 0))), "+
									"            λi:num. ι(q(i)), "+
									"            i), "+
									"        R.zero)) = "+
									"polynomial_mul(vec_sub(basis_vector(R.zero, R.one, 1), "+
									"        vec_scalar_mul(ι(r) * b, basis_vector(R.zero, R.one, 0))), "+
									"    λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero))",
								By(
									R,
									bIn,
									rImage,
									mappedOver,
									mappedDegree,
									Read(polynomial_roots.RescaledLinearFactor, R).AsFact().At(
										b, d.TermAs[B]("ι(r)"), d.TermAs[Nat]("m"), imageQ)))
							weightedH := d.Have(
								"the weighted coefficients of h are those of (x − ι(r)) times the image of q",
								"(λi:num. COND(i ≤ suc(m), monoid_pow(R.mul, R.one, b, suc(m) - i) * ι(h(i)), R.zero)) = "+
									"(λi:num. "+
									"    COND(i ≤ suc(m), "+
									"        monoid_pow(R.mul, R.one, b, suc(m) - i) * "+
									"        polynomial_mul(vec_sub(basis_vector(R.zero, R.one, 1), "+
									"                vec_scalar_mul(ι(r), basis_vector(R.zero, R.one, 0))), "+
									"            λi:num. ι(q(i)), "+
									"            i), "+
									"        R.zero))",
								Funext(),
								d.ForEach(func(_ *Expr[Nat]) Action { return By(imageOfH) }))
							cofactor := d.TermAs[Fun[Nat, B]](
								"λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero)")
							linearR := d.TermAs[Fun[Nat, B]](
								"vec_sub(basis_vector(R.zero, R.one, 1), vec_scalar_mul(ι(r) * b, basis_vector(R.zero, R.one, 0)))")
							shifted := d.Have(
								"ι(r)·b lies in R",
								"ι(r) * b ∈ R.carrier",
								By(rImage, bIn, comm_ring.MulIn.Read(R)))
							cofactorShape := d.Have(
								"the weighted coefficients of q vanish past m and lie in R",
								"vec⟨suc(m)⟩(λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero)) ∧ "+
									"(∀i:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero) ∈ R.carrier)",
								SplitConj(
									Case(
										"they vanish past m",
										ByArith(vec_space.VecDef)),
									Case(
										"each is a power of b times the image of a coefficient of q, or zero",
										Derive(func(e *Argument) {
											e.FixAs[Nat]("i")
											e.Show(
												"in R",
												By(
													mappedOver,
													bIn,
													polynomial.PolynomialOverDef,
													comm_monoid.PowIn.Read(mulMonoid).AsFact().At(b, e.TermAs[Nat]("m - i")),
													comm_ring.MulIn.Read(R),
													comm_ring.ZeroIn.Read(R)))
										}))))
							cofactorOver := d.Have(
								"so they are a polynomial over R",
								"polynomial_over(R.carrier, "+
									"    λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero))",
								By(cofactorShape, polynomial.PolynomialOverDef))
							split := d.Have(
								"the value at a of the product is (a − ι(r)·b) times the value of the cofactor",
								"polynomial_eval(polynomial_mul(vec_sub(basis_vector(R.zero, R.one, 1), "+
									"            vec_scalar_mul(ι(r) * b, basis_vector(R.zero, R.one, 0))), "+
									"        λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero)), "+
									"    a) = "+
									"(a - ι(r) * b) * "+
									"polynomial_eval(λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero), a)",
								By(
									shifted,
									cofactorOver,
									aIn,
									polynomial_evaluation.EvalMul.Read(R).AsFact().At(linearR, cofactor, a),
									polynomial_roots.LinearFactor.Read(R).AsFact().At(d.TermAs[B]("ι(r) * b"))))
							product := d.Have(
								"so P holds (a − ι(r)·b) times the binary form of q",
								"(a - ι(r) * b) * "+
									"polynomial_eval(λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero), a) ∈ "+
									"P",
								split.RwRev(),
								rescaled.RwRev(),
								weightedH.RwRev(),
								By(hValue))
							factors := d.Have(
								"both factors lie in R",
								"a - ι(r) * b ∈ R.carrier ∧ "+
									"polynomial_eval(λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero), a) ∈ "+
									"R.carrier",
								By(aIn, shifted, cofactorOver, comm_ring.SubIn.Read(R), polynomial_evaluation.EvalIn.Read(R)))
							d.Show(
								"P being prime holds a − ι(r)·b, or the binary form of q, which gives a linear factor by induction",
								By(
									product,
									factors,
									prime,
									rIn,
									ih.At(q),
									qOver,
									qNonzero,
									qDegree,
									At(
										ring_ideal.PrimeIdealPrime,
										ringRTerm,
										P,
										d.TermAs[B]("a - ι(r) * b"),
										d.TermAs[B](
											"polynomial_eval(λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * ι(q(i)), R.zero), a)"))))
						})
				}))
			arg.Show(
				"apply it at f, of degree deg f",
				By(byDegree.At(arg.TermAs[Nat]("polynomial_degree(f)"), f), fOver, fNonzero, value))
		}),
})}
