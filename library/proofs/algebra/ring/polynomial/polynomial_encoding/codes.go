// codes.go — the polynomial code of dimension n and degree d, an integer
// polynomial in the variables of a coefficient block and a coordinate
// block, the variables it reads, and its evaluation in two stages: the
// coefficients, then the coordinates.

package polynomial_encoding

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// integerPolynomialsInSlots is the step both support members open with: the integer polynomials
// in the variables of «U» form a commutative ring, where the code and its pieces are formed.
func integerPolynomialsInSlots(a *Argument) Fact {
	return a.Have(
		"the integer polynomials in the variables of «U» form a commutative ring",
		"comm_ring_on(polynomial_algebra_ring(int_ring, «U»))",
		By(
			int_real_lift.CommRingOn,
			polynomial_algebra.PolynomialAlgebraCommRingOn.At(
				a.TermAs[RingOps[Int]]("int_ring"), a.TermAs[Set[Nat]]("«U»"))))
}

// CodeTermsInSlots — the pieces a polynomial code is built from are integer polynomials in the
// variables of its slots «U»: the coordinate variables and the coefficient variables of the bounded
// monomials, whose slots lie in «U», and with them, in the commutative ring of the integer
// polynomials in those variables, the powers of the coordinate variables, their products, and
// each term, a coefficient variable times a product.
var CodeTermsInSlots = codeTermsInSlotsThm{family.Add(registry.ProofEntry{
	Name: "CodeTermsInSlots",
	Key:  "prop_22487375cd7adb",
	Build: family.Theorem(Statement{
		Binders: "∀n d c x:num.",
		Conclusion: "(∀i:num. " +
			"    i < n ⇒ polynomial_algebra_var(int_ring, x + i) ∈ polynomial_algebra(int_ring, «U»)) ∧ " +
			"(∀m:(num → num). " +
			"    m ∈ bounded_monomials(n, d) ⇒ " +
			"    polynomial_algebra_var(int_ring, c + monomial_slot(n, d, m)) ∈ " +
			"    polynomial_algebra(int_ring, «U»)) ∧ " +
			"(∀m:(num → num). ∀i:num. i < n ⇒ «power»(m)(i) ∈ polynomial_algebra(int_ring, «U»)) ∧ " +
			"(∀m:(num → num). «product»(m) ∈ polynomial_algebra(int_ring, «U»)) ∧ " +
			"(∀m:(num → num). m ∈ bounded_monomials(n, d) ⇒ «term»(m) ∈ polynomial_algebra(int_ring, «U»))",
	},
		func(a *Argument, n, d, c, x *Expr[Nat]) {
			ring := integerPolynomialsInSlots(a)
			products := comm_ring.MulMonoidOn.Read(ring)
			coordinates := a.Have(
				"the coordinate slots lie in «U», so the coordinate variables are polynomials in the slots",
				"∀i:num. i < n ⇒ polynomial_algebra_var(int_ring, x + i) ∈ polynomial_algebra(int_ring, «U»)",
				ByArith(polynomial_algebra.PolynomialAlgebraVarIn, int_real_lift.CommRingOn, set_basic.InUnion))
			slots := a.Have(
				"a bounded monomial's slot lies below the coefficient count, "+
					"so its coefficient variable is a polynomial in the slots",
				Statement{
					Binders: "∀m:(num → num).",
					Hypotheses: []string{
						"m ∈ bounded_monomials(n, d)",
					},
					Conclusion: "polynomial_algebra_var(int_ring, c + monomial_slot(n, d, m)) ∈ " +
						"polynomial_algebra(int_ring, «U»)",
				},
				ByArith(
					polynomial_algebra.PolynomialAlgebraVarIn,
					int_real_lift.CommRingOn,
					MonomialSlots.At(n, d),
					set_basic.InUnion))
			powers := a.Have(
				"the powers of the coordinate variables are polynomials in the slots",
				"∀m:(num → num). ∀i:num. i < n ⇒ «power»(m)(i) ∈ polynomial_algebra(int_ring, «U»)",
				By(coordinates, comm_monoid.PowIn.Read(products)))
			productsIn := a.Have(
				"the monomials' products of powers are polynomials in the slots",
				"∀m:(num → num). «product»(m) ∈ polynomial_algebra(int_ring, «U»)",
				By(powers, module.ModuleSumInMonoid.Read(products), num_segment.FiniteBelowStrict))
			termsIn := a.Have(
				"each term of the code is a polynomial in the slots",
				"∀m:(num → num). m ∈ bounded_monomials(n, d) ⇒ «term»(m) ∈ polynomial_algebra(int_ring, «U»)",
				By(slots, productsIn, comm_ring.MulIn.Read(ring)))
			a.Show(
				"so every piece of the code is a polynomial in the slots",
				By(coordinates, slots, powers, productsIn, termsIn))
		}),
})}

// PolynomialCodeSupport — a polynomial code is an integer polynomial whose variables lie in its
// coefficient and coordinate blocks: the integer polynomials in the variables of the two blocks
// form a commutative ring, which holds every term of the code (CodeTermsInSlots) and so their sum
// over the finitely many bounded monomials.
var PolynomialCodeSupport = polynomialCodeSupportThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCodeSupport",
	Key:  "prop_6d0dd03760327664",
	Build: family.Theorem(Statement{
		Binders: "∀n d c x:num.",
		Conclusion: "integer_polynomial(polynomial_code(n, d, c, x)) ∧ " +
			"integer_polynomial_vars(polynomial_code(n, d, c, x)) ⊆ «U»",
	},
		func(a *Argument, n, d, c, x *Expr[Nat]) {
			slotsOf := a.TermAs[Set[Nat]]("«U»")
			code := a.TermAs[IntegerPolynomial]("polynomial_code(n, d, c, x)")
			sums := comm_ring.AddMonoidOn.Read(integerPolynomialsInSlots(a))
			termsIn := a.Conjuncts(
				CodeTermsInSlots.At(n, d, c, x),
				"the coordinate variables are polynomials in the slots",
				"so are the coefficient variables of the bounded monomials",
				"the powers of the coordinate variables",
				"their products",
				"and the code's terms")[4]
			inSlots := a.Have(
				"so is the code, the sum of its terms over the finitely many bounded monomials",
				"polynomial_code(n, d, c, x) ∈ polynomial_algebra(int_ring, «U»)",
				Simp(Fwd(polynomialCodeDef)),
				By(termsIn, module.ModuleSumInMonoid.Read(sums), BoundedMonomialsFinite))
			a.Show(
				"a polynomial in the variables of «U» is an integer polynomial whose variables lie in «U»",
				By(inSlots, polynomial_formula.PolynomialOnVariables.At(slotsOf, code)))
		}),
})}

// CodeSupportBelow — a polynomial code reads only its coefficient block and its coordinate
// block, so its variables lie below any k both blocks end by.
var CodeSupportBelow = codeSupportBelowThm{family.Add(registry.ProofEntry{
	Name: "CodeSupportBelow",
	Key:  "prop_fbaedde30a2a5dd8",
	Build: family.Theorem(Statement{
		Binders: "∀n d c x k:num.",
		Hypotheses: []string{
			"c + coefficient_count(n, d) ≤ k",
			"x + n ≤ k",
		},
		Conclusion: "integer_polynomial_vars(polynomial_code(n, d, c, x)) ⊆ {v:num | v < k}",
	}, func(a *Argument, n, d, c, x, k *Expr[Nat], ends Fact) {
		blocks := a.Have(
			"a name of either block lies below k",
			"(∀v:num. c ≤ v ∧ v < c + coefficient_count(n, d) ⇒ v < k) ∧ (∀v:num. x ≤ v ∧ v < x + n ⇒ v < k)",
			ByArith(ends))
		a.Show(
			"the code's variables lie in its two blocks",
			BySets(blocks, PolynomialCodeSupport.At(n, d, c, x)))
	}),
})}

// TwoStageEvaluation — substituting coefficients then coordinates equals evaluating the integer
// code: evaluation at ρ is a ring homomorphism on the integer polynomials in the slots, so the
// code, a sum over the bounded monomials of a coefficient variable times a product of powers of
// coordinate variables, evaluates term by term to ρ at the coefficient slot times the monomial's
// value at the coordinates; the decoded polynomial is supported in the bounded monomials and reads
// ρ at the coefficient slot, and the decoded tuple reads ρ at the coordinate slots, so its value is
// the same sum.
var TwoStageEvaluation = twoStageEvaluationThm{family.Add(registry.ProofEntry{
	Name: "TwoStageEvaluation",
	Key:  "prop_1626dccce7ef929",
	Reading: "Coefficient and coordinate blocks may overlap here because both sides read the same " +
		"environment. The guard covers their union; the formulas built from codes place every coordinate " +
		"block past the coefficient blocks, so quantifying the coordinates binds no coefficient.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n d c x:num. ∀ρ:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, «U», ρ)",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, polynomial_code(n, d, c, x)) = " +
			"polynomial_value(R, decode_polynomial(R, n, d, c, ρ), decode_tuple(R, n, x, ρ))",
		Abbrev: Abbrev{
			{Name: "value", Text: "λm:(num → num). " +
				"    module_sum(R.mul, R.one, {i:num | i < n}, λi:num. monoid_pow(R.mul, R.one, ρ(x + i), m(i)))"},
		},
	},
		func(a *Argument, R *Expr[RingOps[A]], n, d, c, x *Expr[Nat], ρ *Arrow[Nat, A], ring, env Fact) {
			bounded := a.TermAs[Set[_Monomial]]("bounded_monomials(n, d)")
			below := a.TermAs[Set[Nat]]("{i:num | i < n}")
			slotsOf := a.TermAs[Set[Nat]]("«U»")
			coefficientBlock := a.TermAs[Set[Nat]]("«block»")
			coordinateBlock := a.TermAs[Set[Nat]]("{j:num | x ≤ j ∧ j < x + n}")
			carrier := a.TermAs[Set[A]]("R.carrier")
			eval := a.TermAs[Fun[IntegerPolynomial, A]](
				"λq:((num → num) → int). integer_polynomial_eval(R, ρ, q)")
			decoded := a.TermAs[Fun[_Monomial, A]]("decode_polynomial(R, n, d, c, ρ)")
			tuple := a.TermAs[Fun[Nat, A]]("decode_tuple(R, n, x, ρ)")
			addR := a.TermAs[Op[A]]("R.add")
			zeroR := a.TermAs[A]("R.zero")
			mulR := a.TermAs[Op[A]]("R.mul")
			oneR := a.TermAs[A]("R.one")
			values := a.Unfolded(env, first_order.EnvOKDef)
			pieces := a.Conjuncts(
				CodeTermsInSlots.At(n, d, c, x),
				"the coordinate variables are polynomials in the slots",
				"so are the coefficient variables of the bounded monomials",
				"the powers of the coordinate variables",
				"their products",
				"and the code's terms")
			coordinateIn, slotIn, powers, productsIn, termsIn :=
				pieces[0], pieces[1], pieces[2], pieces[3], pieces[4]

			hom := a.Have(
				"evaluating at ρ is a ring homomorphism from the "+
					"integer polynomials in the variables of «U» into R",
				"ring_homomorphism(restrict_ring(integer_polynomial_ring, polynomial_algebra(int_ring, «U»)), "+
					"    R, "+
					"    λq:((num → num) → int). integer_polynomial_eval(R, ρ, q))",
				By(ring, env, polynomial_formula.IntegerPolynomialEvalHom.At(R, slotsOf, ρ)))
			source := ring_homomorphism.Source.Read(hom)
			products := comm_ring.MulMonoidOn.Read(source)
			sums := comm_ring.AddMonoidOn.Read(source)

			coordinates := a.Have(
				"the coordinate slots lie in «U»",
				"∀i:num. i < n ⇒ x + i ∈ «U»",
				ByArith(set_basic.InUnion))
			slots := a.Have(
				"the coefficient slots of the bounded monomials lie in «U»",
				"∀m:(num → num). m ∈ bounded_monomials(n, d) ⇒ c + monomial_slot(n, d, m) ∈ «U»",
				ByArith(MonomialSlots.At(n, d), set_basic.InUnion))
			coordinateValues := a.Have(
				"ρ takes carrier values at the coordinate slots",
				"∀i:num. i < n ⇒ ρ(x + i) ∈ R.carrier",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					under := b.Assume()
					b.Show(
						"x + i lies in «U»",
						By(coordinates.At(i), under, values.At(b.TermAs[Nat]("x + i"))))
				}))

			coordinateVariables := a.Have(
				"a coordinate variable evaluates to the coordinate's value",
				"∀i:num. i < n ⇒ integer_polynomial_eval(R, ρ, polynomial_algebra_var(int_ring, x + i)) = ρ(x + i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					under := b.Assume()
					b.Show(
						"ρ takes a carrier value at the slot x + i",
						By(
							coordinateValues.At(i),
							under,
							ring,
							polynomial_formula.VariableValue.At(R, ρ, b.TermAs[Nat]("x + i"))))
				}))
			slotVariables := a.Have(
				"a coefficient variable evaluates to the coefficient slot's value",
				Statement{
					Binders: "∀m:(num → num).",
					Hypotheses: []string{
						"m ∈ bounded_monomials(n, d)",
					},
					Conclusion: "integer_polynomial_eval(R, " +
						"    ρ, " +
						"    polynomial_algebra_var(int_ring, c + monomial_slot(n, d, m))) = " +
						"ρ(c + monomial_slot(n, d, m))",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[_Monomial]("m")
					inBounded := b.Assume()
					slot := b.TermAs[Nat]("c + monomial_slot(n, d, m)")
					b.Show(
						"the slot lies in «U», where ρ takes a carrier value",
						By(slots.At(m), inBounded, values.At(slot), ring, polynomial_formula.VariableValue.At(R, ρ, slot)))
				}))

			powerValues := a.Have(
				"the powers of the coordinate variables evaluate to the powers of the coordinates' values",
				Statement{
					Binders: "∀m:(num → num). ∀i:num.",
					Hypotheses: []string{
						"i < n",
					},
					Conclusion: "integer_polynomial_eval(R, ρ, «power»(m)(i)) = " +
						"monoid_pow(R.mul, R.one, ρ(x + i), m(i))",
				},
				Derive(func(b *Argument) {
					b.FixAs[_Monomial]("m")
					i := b.FixAs[Nat]("i")
					under := b.Assume()
					carried := b.Have(
						"the homomorphism carries the power of the variable to the power of its value",
						"integer_polynomial_eval(R, ρ, «power»(m)(i)) = "+
							"monoid_pow(R.mul, "+
							"    R.one, "+
							"    integer_polynomial_eval(R, ρ, polynomial_algebra_var(int_ring, x + i)), "+
							"    m(i))",
						By(
							under,
							coordinateIn.At(i),
							ring_homomorphism.RingMapPower.Read(hom).AsFact().At(
								b.TermAs[Nat]("m(i)"),
								b.TermAs[IntegerPolynomial]("polynomial_algebra_var(int_ring, x + i)"))))
					b.Show(
						"and the variable's value is the coordinate's",
						By(carried, under, coordinateVariables.At(i)))
				}))
			productValues := a.Have(
				"the monomials' products of powers evaluate to the monomials' values at the coordinates",
				"∀m:(num → num). integer_polynomial_eval(R, ρ, «product»(m)) = «value»(m)",
				Derive(func(b *Argument) {
					m := b.FixAs[_Monomial]("m")
					power := b.TermAs[Fun[Nat, IntegerPolynomial]]("«power»(m)")
					agree := b.Have(
						"below n each power evaluates to the power of the coordinate's value",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"i ∈ {i:num | i < n}",
							},
							Conclusion: "integer_polynomial_eval(R, ρ, «power»(m)(i)) = " +
								"monoid_pow(R.mul, R.one, ρ(x + i), m(i))",
						},
						By(powerValues.At(m)))
					b.Show(
						"the homomorphism carries the product to the product of "+
							"the images, which are the powers of the coordinates' values",
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(R.mul, R.one, {i:num | i < n}, λi:num. integer_polynomial_eval(R, ρ, «power»(m)(i)))"),
								"a ring homomorphism carries a finite product to the product of the images",
								By(
									powers.At(m),
									module.ModuleSumMonoidHomomorphism.Read(products).At(mulR, oneR, eval, below, power),
									ring_homomorphism.MapOne.Read(hom),
									ring_homomorphism.MapMul.Read(hom),
									num_segment.FiniteBelowStrict.At(n))),
							FinalLeg(
								"and the images agree with the powers of the coordinates' values",
								By(
									agree,
									module.ModuleSumCongruence.At(
										mulR,
										oneR,
										below,
										b.TermAs[Fun[Nat, A]]("λi:num. integer_polynomial_eval(R, ρ, «power»(m)(i))"),
										b.TermAs[Fun[Nat, A]]("λi:num. monoid_pow(R.mul, R.one, ρ(x + i), m(i))"))))))
				}))
			termValues := a.Have(
				"each term of the code evaluates to the coefficient slot's value times the monomial's value",
				Statement{
					Binders: "∀m:(num → num).",
					Hypotheses: []string{
						"m ∈ bounded_monomials(n, d)",
					},
					Conclusion: "integer_polynomial_eval(R, ρ, «term»(m)) = ρ(c + monomial_slot(n, d, m)) * «value»(m)",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[_Monomial]("m")
					inBounded := b.Assume()
					b.Show(
						"the homomorphism splits the term into the coefficient variable's value times the product's",
						CalcEq(
							Leg(
								b.TermAs[A](
									"integer_polynomial_eval(R, ρ, polynomial_algebra_var(int_ring, c + monomial_slot(n, d, m))) * "+
										"integer_polynomial_eval(R, ρ, «product»(m))"),
								"a ring homomorphism carries a product to the product of the images",
								By(
									inBounded,
									slotIn.At(m),
									productsIn.At(m),
									ring_homomorphism.MapMul.Read(hom).AsFact().At(
										b.TermAs[IntegerPolynomial]("polynomial_algebra_var(int_ring, c + monomial_slot(n, d, m))"),
										b.TermAs[IntegerPolynomial]("«product»(m)")))),
							Leg(
								b.TermAs[A]("ρ(c + monomial_slot(n, d, m)) * integer_polynomial_eval(R, ρ, «product»(m))"),
								"the coefficient variable evaluates to the coefficient slot's value",
								By(inBounded, slotVariables.At(m))),
							FinalLeg(
								"and the product to the monomial's value",
								By(productValues.At(m)))))
				}))

			codeValue := a.Have(
				"the code evaluates to the sum of its terms' values",
				"integer_polynomial_eval(R, ρ, polynomial_code(n, d, c, x)) = "+
					"module_sum(R.add, "+
					"    R.zero, "+
					"    bounded_monomials(n, d), "+
					"    λm:(num → num). integer_polynomial_eval(R, ρ, «term»(m)))",
				Simp(Fwd(polynomialCodeDef)),
				By(
					termsIn,
					module.ModuleSumMonoidHomomorphism.Read(sums).At(
						addR, zeroR, eval, bounded, a.TermAs[Fun[_Monomial, IntegerPolynomial]]("«term»")),
					ring_homomorphism.MapZero.Read(hom),
					ring_homomorphism.MapAdd.Read(hom),
					BoundedMonomialsFinite.At(n, d)))

			decodedBound := a.Conjuncts(
				a.Unfolded(
					a.Have(
						"ρ is carrier-valued on the coefficient block, so the decoded polynomial has degree at most d",
						"polynomial_bound(R, n, d, decode_polynomial(R, n, d, c, ρ))",
						By(
							ring,
							env,
							first_order.EnvOKUnion.At(carrier, coefficientBlock, coordinateBlock, ρ),
							DecodePolynomialBound.At(R, n, d, c, ρ))),
					PolynomialBoundDef),
				"the decoded polynomial is a polynomial in the variables below n",
				"supported in the bounded monomials")
			decodedIn := a.Conjuncts(
				a.Simplified(decodedBound[0], Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"it is nonzero at finitely many monomials",
				"each a monomial of the variables below n",
				"and its coefficients lie in the carrier")
			tupleIn := a.Have(
				"the decoded tuple takes carrier values at the coordinates below n",
				"∀i:num. i ∈ {i:num | i < n} ⇒ decode_tuple(R, n, x, ρ, i) ∈ R.carrier",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					inBelow := b.Assume()
					b.Show(
						"below n the tuple reads ρ at the coordinate slot",
						By(Normalized, coordinateValues.At(i), inBelow, DecodeTupleDef.At(R, n, x, ρ, i)))
				}))
			polynomialValue := a.Have(
				"the value of the decoded polynomial at the decoded tuple is its sum over the bounded monomials",
				"polynomial_value(R, decode_polynomial(R, n, d, c, ρ), decode_tuple(R, n, x, ρ)) = "+
					"module_sum(R.add, "+
					"    R.zero, "+
					"    bounded_monomials(n, d), "+
					"    λm:(num → num). "+
					"        decode_polynomial(R, n, d, c, ρ, m) * monomial_eval(R, decode_tuple(R, n, x, ρ), m))",
				Simp(Fwd(PolynomialValueDef)),
				By(
					ring_homomorphism.RingHomIdentity.Read(ring),
					tupleIn,
					decodedIn[2],
					decodedBound[1],
					polynomial_algebra_evaluation.PolynomialAlgebraEvalOver.At(
						R, R, a.TermAs[Fun[A, A]]("λa:A. a"), tuple, below, bounded, decoded),
					BoundedMonomialsFinite.At(n, d),
					BoundedMonomialsAreMonomials.At(n, d)))
			termsAgree := a.Have(
				"at a bounded monomial the code's term and the decoded polynomial's term have one value",
				Statement{
					Binders: "∀m:(num → num).",
					Hypotheses: []string{
						"m ∈ bounded_monomials(n, d)",
					},
					Conclusion: "ρ(c + monomial_slot(n, d, m)) * «value»(m) = " +
						"decode_polynomial(R, n, d, c, ρ, m) * monomial_eval(R, decode_tuple(R, n, x, ρ), m)",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[_Monomial]("m")
					inBounded := b.Assume()
					b.Show(
						"the decoded polynomial reads ρ at the coefficient slot, and the "+
							"monomial's value at the decoded tuple is its value at the coordinates",
						By(
							inBounded,
							coordinateValues,
							ring,
							decodePolynomialDef.At(R, n, d, c, ρ, m),
							DecodeTupleMonomialValue.At(R, n, d, x, ρ, m)))
				}))
			a.Show(
				"both sides are the sum over the bounded monomials of "+
					"the coefficient slot's value times the monomial's value",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    bounded_monomials(n, d), "+
								"    λm:(num → num). integer_polynomial_eval(R, ρ, «term»(m)))"),
						"the code evaluates term by term",
						By(codeValue)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    bounded_monomials(n, d), "+
								"    λm:(num → num). ρ(c + monomial_slot(n, d, m)) * «value»(m))"),
						"each term to its coefficient slot's value times the monomial's value",
						By(
							termValues,
							module.ModuleSumCongruence.At(
								addR,
								zeroR,
								bounded,
								a.TermAs[Fun[_Monomial, A]]("λm:(num → num). integer_polynomial_eval(R, ρ, «term»(m))"),
								a.TermAs[Fun[_Monomial, A]]("λm:(num → num). ρ(c + monomial_slot(n, d, m)) * «value»(m)")))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    bounded_monomials(n, d), "+
								"    λm:(num → num). "+
								"        decode_polynomial(R, n, d, c, ρ, m) * monomial_eval(R, decode_tuple(R, n, x, ρ), m))"),
						"which is the decoded polynomial's term at the decoded tuple",
						By(
							termsAgree,
							module.ModuleSumCongruence.At(
								addR,
								zeroR,
								bounded,
								a.TermAs[Fun[_Monomial, A]]("λm:(num → num). ρ(c + monomial_slot(n, d, m)) * «value»(m)"),
								a.TermAs[Fun[_Monomial, A]](
									"λm:(num → num). "+
										"    decode_polynomial(R, n, d, c, ρ, m) * monomial_eval(R, decode_tuple(R, n, x, ρ), m)")))),
					FinalLeg(
						"and that sum is the value of the decoded polynomial at the decoded tuple",
						By(polynomialValue))))
		}),
})}

// UnivariateCodeSupport — a univariate code is an integer polynomial in its coefficient block and
// its coordinate slot: the integer polynomials in the variables of the block and the slot form a
// commutative ring, which holds the coefficient variables and the powers of the coordinate
// variable, so each term of the code, a product of the two, and so the sum of the terms below n.
var UnivariateCodeSupport = univariateCodeSupportThm{family.Add(registry.ProofEntry{
	Name: "UnivariateCodeSupport",
	Key:  "prop_3f15d3fb2b1fe890",
	Build: family.Theorem(Statement{
		Binders: "∀n c x:num.",
		Conclusion: "integer_polynomial(univariate_code(n, c, x)) ∧ " +
			"integer_polynomial_vars(univariate_code(n, c, x)) ⊆ «slots»",
		Abbrev: Abbrev{
			{Name: "slots", Text: "{j:num | c ≤ j ∧ j < c + n} ∪ {x}"},
			{Name: "coordinatePower", Text: "λi:num. " +
				"    monoid_pow(polynomial_algebra_mul(int_ring), " +
				"        polynomial_algebra_one(int_ring), " +
				"        polynomial_algebra_var(int_ring, x), " +
				"        i)"},
		},
	},
		func(a *Argument, n, c, x *Expr[Nat]) {
			intRing := a.TermAs[RingOps[Int]]("int_ring")
			slotsOf := a.TermAs[Set[Nat]]("«slots»")
			code := a.TermAs[IntegerPolynomial]("univariate_code(n, c, x)")
			ring := a.Have(
				"the integer polynomials in the variables of «slots» form a commutative ring",
				"comm_ring_on(polynomial_algebra_ring(int_ring, «slots»))",
				By(int_real_lift.CommRingOn, polynomial_algebra.PolynomialAlgebraCommRingOn.At(intRing, slotsOf)))
			coefficients := a.Have(
				"the coefficient slots lie in the block, so the coefficient variables are polynomials in the slots",
				"∀i:num. i < n ⇒ polynomial_algebra_var(int_ring, c + i) ∈ polynomial_algebra(int_ring, «slots»)",
				ByArith(polynomial_algebra.PolynomialAlgebraVarIn, int_real_lift.CommRingOn, set_basic.InUnion))
			powers := a.Have(
				"the coordinate slot x lies in «slots», so its variable is "+
					"a polynomial in the slots, and so are the variable's powers",
				"∀i:num. «coordinatePower»(i) ∈ polynomial_algebra(int_ring, «slots»)",
				By(
					polynomial_algebra.PolynomialAlgebraVarIn.At(intRing, slotsOf, x),
					int_real_lift.CommRingOn,
					set_basic.InUnion,
					set_basic.InSing,
					comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
			terms := a.Have(
				"each term of the code, a coefficient variable times a power "+
					"of the coordinate variable, is a polynomial in the slots",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i < n",
					},
					Conclusion: "polynomial_algebra_mul(int_ring, " +
						"    polynomial_algebra_var(int_ring, c + i), " +
						"    «coordinatePower»(i)) ∈ " +
						"polynomial_algebra(int_ring, «slots»)",
				},
				By(coefficients, powers, comm_ring.MulIn.Read(ring)))
			inSlots := a.Have(
				"so is the code, the sum of its terms below n",
				"univariate_code(n, c, x) ∈ polynomial_algebra(int_ring, «slots»)",
				Simp(Fwd(univariateCodeDef)),
				By(
					terms,
					module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(ring)),
					num_segment.FiniteBelowStrict))
			a.Show(
				"a polynomial in the variables of «slots» is an integer polynomial whose variables lie in «slots»",
				By(inSlots, polynomial_formula.PolynomialOnVariables.At(slotsOf, code)))
		}),
})}

// UnivariateCodeBelow — a univariate code's variables lie below any k its coefficient block and
// its coordinate slot lie below: both lie below k, and UnivariateCodeSupport places the variables
// in them.
var UnivariateCodeBelow = univariateCodeBelowThm{family.Add(registry.ProofEntry{
	Name: "UnivariateCodeBelow",
	Key:  "prop_e7f569ba83fc4a8e",
	Build: family.Theorem(Statement{
		Binders: "∀n c x k:num.",
		Hypotheses: []string{
			"c + n ≤ k",
			"x < k",
		},
		Conclusion: "integer_polynomial_vars(univariate_code(n, c, x)) ⊆ {v:num | v < k}",
	}, func(a *Argument, n, c, x, k *Expr[Nat], blockEnds, slotBelow Fact) {
		below := a.Have(
			"a name of the block lies below k, and so does the slot",
			"(∀v:num. c ≤ v ∧ v < c + n ⇒ v < k) ∧ x < k",
			ByArith(blockEnds, slotBelow))
		a.Show(
			"the code's variables lie in its block and its slot",
			BySets(below, UnivariateCodeSupport.At(n, c, x)))
	}),
})}

// UnivariateCodeEvaluation — evaluating a univariate code substitutes the coefficients and the
// coordinate: it is the polynomial in one variable decoded from the coefficient block, as a tuple,
// evaluated at the coordinate slot's value. Evaluation at ρ is a ring homomorphism on the integer
// polynomials in the variables of «slots», so the code, the sum below n of the coefficient
// variables times the powers of the coordinate variable, evaluates term by term to the sum below n
// of ρ(c + i), the decoded tuple's entry, times ρ(x) to the power i; the decoded tuple vanishes
// from n on, so that sum is its value at ρ(x).
var UnivariateCodeEvaluation = univariateCodeEvaluationThm{family.Add(registry.ProofEntry{
	Name: "UnivariateCodeEvaluation",
	Key:  "prop_355c3789e1b9145b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀n c x:num. ∀ρ:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, «slots», ρ)",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, univariate_code(n, c, x)) = " +
			"polynomial_eval(decode_tuple(R, n, c, ρ), ρ(x))",
		Abbrev: Abbrev{
			{Name: "slots", Text: "{j:num | c ≤ j ∧ j < c + n} ∪ {x}"},
			{Name: "coordinatePower", Text: "λi:num. " +
				"    monoid_pow(polynomial_algebra_mul(int_ring), " +
				"        polynomial_algebra_one(int_ring), " +
				"        polynomial_algebra_var(int_ring, x), " +
				"        i)"},
			{Name: "univariateTerm", Text: "λi:num. " +
				"    polynomial_algebra_mul(int_ring, " +
				"        polynomial_algebra_var(int_ring, c + i), " +
				"        «coordinatePower»(i))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n, c, x *Expr[Nat],
			ρ *Arrow[Nat, A],
			ring comm_ring.CommRingFact[on.R],
			env Fact,
		) {
			intRing := a.TermAs[RingOps[Int]]("int_ring")
			below := a.TermAs[Set[Nat]]("{i:num | i < n}")
			slotsOf := a.TermAs[Set[Nat]]("«slots»")
			eval := a.TermAs[Fun[IntegerPolynomial, A]](
				"λq:((num → num) → int). integer_polynomial_eval(R, ρ, q)")
			tuple := a.VecAs[A, DimN]("decode_tuple(R, n, c, ρ)")
			addR := a.TermAs[Op[A]]("R.add")
			zeroR := a.TermAs[A]("R.zero")
			values := a.Unfolded(env, first_order.EnvOKDef)

			hom := a.Have(
				"evaluating at ρ is a ring homomorphism from the "+
					"integer polynomials in the variables of «slots» into R",
				"ring_homomorphism( "+
					"    restrict_ring(integer_polynomial_ring, polynomial_algebra(int_ring, «slots»)), "+
					"    R, "+
					"    λq:((num → num) → int). integer_polynomial_eval(R, ρ, q))",
				By(ring, env, polynomial_formula.IntegerPolynomialEvalHom.At(R, slotsOf, ρ)))
			source := ring_homomorphism.Source.Read(hom)

			blockValues := a.Have(
				"ρ takes carrier values on the coefficient block",
				"∀i:num. i < n ⇒ ρ(c + i) ∈ R.carrier",
				ByArith(values, set_basic.InUnion))
			coordinateValue := a.Have(
				"and at the coordinate slot",
				"ρ(x) ∈ R.carrier",
				By(values.At(x), set_basic.InUnion, set_basic.InSing))

			coefficients := a.Have(
				"the coefficient slots lie in «slots», so the coefficient variables are polynomials in the slots",
				"∀i:num. i < n ⇒ polynomial_algebra_var(int_ring, c + i) ∈ polynomial_algebra(int_ring, «slots»)",
				ByArith(polynomial_algebra.PolynomialAlgebraVarIn, int_real_lift.CommRingOn, set_basic.InUnion))
			variable := a.Have(
				"so is the variable of the coordinate slot x",
				"polynomial_algebra_var(int_ring, x) ∈ polynomial_algebra(int_ring, «slots»)",
				By(
					polynomial_algebra.PolynomialAlgebraVarIn.At(intRing, slotsOf, x),
					int_real_lift.CommRingOn,
					set_basic.InUnion,
					set_basic.InSing))
			powers := a.Have(
				"and so are its powers",
				"∀i:num. «coordinatePower»(i) ∈ polynomial_algebra(int_ring, «slots»)",
				By(variable, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(source))))
			terms := a.Have(
				"each term of the code, a coefficient variable times a power "+
					"of the coordinate variable, is a polynomial in the slots",
				"∀i:num. i < n ⇒ «univariateTerm»(i) ∈ polynomial_algebra(int_ring, «slots»)",
				By(coefficients, powers, comm_ring.MulIn.Read(source)))

			powerValues := a.Have(
				"the powers of the coordinate variable evaluate to the powers of ρ(x)",
				"∀i:num. integer_polynomial_eval(R, ρ, «coordinatePower»(i)) = monoid_pow(R.mul, R.one, ρ(x), i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"the homomorphism carries the power of the variable to "+
							"the power of its value, and the variable's value is ρ(x)",
						By(
							ring,
							coordinateValue,
							variable,
							ring_homomorphism.RingMapPower.Read(hom).AsFact().At(
								i,
								b.TermAs[IntegerPolynomial]("polynomial_algebra_var(int_ring, x)")),
							polynomial_formula.VariableValue.At(R, ρ, x)))
				}))
			termValues := a.Have(
				"below n each term evaluates to the decoded tuple's entry times the power of ρ(x)",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i < n",
					},
					Conclusion: "integer_polynomial_eval(R, ρ, «univariateTerm»(i)) = " +
						"decode_tuple(R, n, c, ρ, i) * monoid_pow(R.mul, R.one, ρ(x), i)",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					under := b.Assume()
					slot := b.TermAs[Nat]("c + i")
					b.Show(
						"the homomorphism splits the term into the values of its two factors",
						CalcEq(
							Leg(
								b.TermAs[A](
									"integer_polynomial_eval(R, ρ, polynomial_algebra_var(int_ring, c + i)) * "+
										"integer_polynomial_eval(R, ρ, «coordinatePower»(i))"),
								"a ring homomorphism carries a product to the product of the images",
								By(
									under,
									coefficients.At(i),
									powers.At(i),
									ring_homomorphism.MapMul.Read(hom).AsFact().At(
										b.TermAs[IntegerPolynomial]("polynomial_algebra_var(int_ring, c + i)"),
										b.TermAs[IntegerPolynomial]("«coordinatePower»(i)")))),
							FinalLeg(
								"the coefficient variable evaluates to ρ(c + i), the decoded "+
									"tuple's entry below n, and the power to the power of ρ(x)",
								By(
									under,
									ring,
									blockValues.At(i),
									powerValues.At(i),
									polynomial_formula.VariableValue.At(R, ρ, slot),
									DecodeTupleDef.At(R, n, c, ρ, i)))))
				}))

			vanishes := a.Have(
				"the decoded tuple vanishes from n on",
				"vec⟨n⟩(decode_tuple(R, n, c, ρ))",
				Unfold(vec_space.VecDef),
				Simp(Fwd(DecodeTupleDef)),
				By(nat_order.NotLessThan))
			entries := a.Have(
				"its entries lie in the carrier: ρ's values on the block below n, and zero from n on",
				"∀i:num. decode_tuple(R, n, c, ρ, i) ∈ R.carrier",
				Simp(Fwd(DecodeTupleDef)),
				By(blockValues, comm_ring.ZeroIn.Read(ring)))

			a.Show(
				"both sides are the sum below n of the decoded tuple's entries times the powers of ρ(x)",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < n}, "+
								"    λi:num. integer_polynomial_eval(R, ρ, «univariateTerm»(i)))"),
						"the code is the sum of its terms below n, which "+
							"the homomorphism carries to the sum of their values",
						Simp(Fwd(univariateCodeDef)),
						By(
							terms,
							module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(source)).At(
								addR,
								zeroR,
								eval,
								below,
								a.TermAs[Fun[Nat, IntegerPolynomial]]("«univariateTerm»")),
							ring_homomorphism.MapZero.Read(hom),
							ring_homomorphism.MapAdd.Read(hom),
							num_segment.FiniteBelowStrict.At(n))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < n}, "+
								"    λi:num. decode_tuple(R, n, c, ρ, i) * monoid_pow(R.mul, R.one, ρ(x), i))"),
						"each term to the decoded tuple's entry times the power of ρ(x)",
						By(
							termValues,
							module.ModuleSumCongruence.At(
								addR,
								zeroR,
								below,
								a.TermAs[Fun[Nat, A]]("λi:num. integer_polynomial_eval(R, ρ, «univariateTerm»(i))"),
								a.TermAs[Fun[Nat, A]]("λi:num. decode_tuple(R, n, c, ρ, i) * monoid_pow(R.mul, R.one, ρ(x), i)")))),
					FinalLeg(
						"the decoded tuple, carrier-valued and vanishing from n on, "+
							"is a polynomial over R, and that sum is its value at ρ(x)",
						By(
							entries,
							polynomial.PolynomialOverDef,
							polynomial_evaluation.EvalBelow.Read(ring).At(
								proof.Inhabit(tuple, vanishes),
								a.MemberOf[on.R](a.TermAs[A]("ρ(x)"), coordinateValue))))))
		}),
})}
