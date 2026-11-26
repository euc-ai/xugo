// zeros.go — the zeros on the curve of a form over k outside the ideal lie
// in one finite subfield of M, and over such a subfield a form over k has no
// zero but the origin. At such a zero the values of the forms of degree d
// span at most h(d) − h(d − r) dimensions over k, and with one coordinate one
// they hold the powers of every other coordinate, so each coordinate has
// bounded degree over k. Over the field of q^s elements a form over k built
// from the (q^s − 1)-th powers of the variables takes the value one at every
// point with a nonzero coordinate.

package projective_form_pair

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// FormValuesBound — at a zero z on the curve of a form F of degree r ≤ d
// over k outside the ideal, the values at z of the forms of degree d are a
// k-subspace of M of dimension at most h(d) − h(d − r). Evaluation at z is
// linear on the forms of degree d, and its kernel holds the forms of degree
// d in the ideal, which vanish at the curve's points, and F times every
// form of degree d − r; so the kernel's codimension, the dimension of the
// values (module_dimension.RankNullity), is at most h(d) − h(d − r)
// (projective_curve.HyperplaneSectionBound).
var FormValuesBound = formValuesBoundThm{family.Add(registry.ProofEntry{
	Name: "FormValuesBound",
	Key:  "prop_140393da8e050283",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k:set(A). " +
			"∀n r d:num. " +
			"∀E:set((num → num) → A). " +
			"∀F:((num → num) → A). " +
			"∀z:(num → A).",
		Hypotheses: []string{
			"smooth_projective_equation_curve(M, k, n, E)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"F ∉ ideal_span(«polynomials», E)",
			"r ≤ d",
			"z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E)",
			"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, F) = M.zero",
		},
		Conclusion: "submodule(«hilbertCoefficients», regular_module(field_ring(M)), «values»(d)) ∧ " +
			"finite_dimensional(«hilbertCoefficients», «valueSpace»(d)) ∧ " +
			"module_dim(«hilbertCoefficients», «valueSpace»(d)) + " +
			"projective_hilbert_function(field_ring(M), k, n, E, d - r) ≤ " +
			"projective_hilbert_function(field_ring(M), k, n, E, d)",
		Abbrev: Abbrev{
			{Name: "forms", Text: "λd:num. " +
				"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"},
			{Name: "formSpace", Text: "λd:num. " +
				"    mk_module(fun_add, " +
				"        fun_zero, " +
				"        fun_neg, " +
				"        λa:A. λP:((num → num) → A). λm:(num → num). a * P(m), " +
				"        «forms»(d))"},
			{Name: "values", Text: "λd:num. " +
				"    image(polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z), " +
				"        «forms»(d))"},
			{Name: "valueSpace", Text: "λd:num. restrict_module(regular_module(field_ring(M)), «values»(d))"},
			{Name: "vanishing", Text: "group_kernel(M.zero, " +
				"    «forms»(d), " +
				"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, r, d *Expr[Nat],
		E *Expr[Set[_Polynomial]],
		F *Arrow[Fun[Nat, Nat], A],
		z *Arrow[Nat, A],
		curve, form, outside, below, point, zero Fact,
	) {
		K := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		identityMap := a.TermAs[Fun[A, A]]("λa:A. a")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		spaceD := a.TermAs[module_record.ModuleOps[A, _Polynomial]]("«formSpace»(d)")
		regularM := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
		evaluate := a.TermAs[Fun[_Polynomial, A]](
			"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z)")
		vanishing := a.TermAs[Set[_Polynomial]]("«vanishing»")
		zeroM := a.TermAs[A]("M.zero")
		polynomialsK := a.TermAs[Set[_Polynomial]](
			"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})")
		formsD := a.TermAs[Set[_Polynomial]]("«forms»(d)")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		carrier := a.TermAs[Set[A]]("M.carrier")
		subK := a.Have(
			"k is a subfield of M",
			"subfield(M, k)",
			By(projective_curve.CurveConstantsSubfield.Read(curve)))
		equations := projective_curve.CurveEquationsForms.Read(curve)
		inM := a.Have(
			"the coordinates of z up to n lie in M",
			"∀i:num. i ≤ n ⇒ z(i) ∈ M.carrier",
			By(point, projective_curve.PointCoordinatesIn))
		vanishes := a.Have(
			"every equation vanishes at z",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ E"},
				Conclusion: "polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, P) = " +
					"M.zero",
			},
			By(point, At(projective_curve.PointEquationsVanish, fieldRing, k, carrier, n, E, z)))
		prime := a.Have(
			"the ideal over k is prime",
			"prime_ideal(«polynomials», ideal_span(«polynomials», E))",
			By(curve, Read(projective_curve.CurveIdealPrime, M).At(k, n, E)))
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		kField := a.Have(
			"k is a field",
			"ring_subfield(«hilbertCoefficients», M.inv, k)",
			By(subK, field.SubfieldRingSubfield.Read(M).At(k, k)))
		inK := a.Have(
			"the equations are polynomials over k",
			"E ⊆ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			BySets(equations, homogeneous_polynomial.FormPolynomial))
		polynomialF := a.Have(
			"F is a polynomial over k",
			"F ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			By(homogeneous_polynomial.FormPolynomial.Read(form)))
		identity := a.Have(
			"k includes into M as a ring homomorphism",
			"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
			By(
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k)))
		evaluation := a.Have(
			"evaluation at z is a ring map from the polynomials over k into M",
			"ring_homomorphism(«polynomials», "+
				"    field_ring(M), "+
				"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, z))",
			By(subK, inM, Read(homogeneous_polynomial.EvaluationRingHom, M).At(k, n, z)))
		regular := a.Have(
			"M is a vector space over k",
			"module_on(«hilbertCoefficients», regular_module(field_ring(M)))",
			By(
				subK,
				field.SubfieldSubring.Read(M),
				module.RegularModuleOverSubring.Read(field.RingOn.Read(M)).At(k)))
		space := a.Conjuncts(
			GroupPremises(subK, Read(projective_curve.FormsSubspace, M).At(k, n, d)),
			"the forms of degree d are a vector space",
			"meeting every ideal in a subspace")
		moduleD := space[0]
		dimension := a.Conjuncts(
			GroupPremises(subK, projective_curve.FormsDimension.Read(M).At(k, n, d)),
			"the forms of degree d are finite-dimensional",
			"of dimension binomial(d + n, n)")
		finiteD := dimension[0]
		linear := a.Have(
			"evaluation at z is a linear map from the forms of degree d "+
				"to M, M over k through the inclusion being M's regular module",
			"module_homomorphism(«hilbertCoefficients», "+
				"    «formSpace»(d), "+
				"    regular_module(field_ring(M)), "+
				"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z))",
			By(
				M,
				subK,
				identity,
				inM,
				module_record.ScalarRestrictionIdentity.At(regularM),
				projective_curve.EvaluationLinear.At(
					a.TermAs[FieldOps[A]]("M"), a.TermAs[FieldOps[A]]("M"), k, n, d, identityMap, z)))
		idealVanishes := a.Have(
			"the ideal vanishes at z: its generators, the equations, vanish at the points of the curve",
			"ideal_span(«polynomials», E) ⊆ "+
				"ring_kernel(M.zero, "+
				"    polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}), "+
				"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z))",
			By(inK, vanishes, ring_homomorphism.IdealSpanInKernel.Read(evaluation).At(E)))
		kernel := a.Have(
			"the forms of degree d vanishing at z are a subspace",
			"submodule(«hilbertCoefficients», «formSpace»(d), «vanishing»)",
			By(module_homomorphism.KernelSubmodule.Read(linear)))
		holdsIdeal := a.Have(
			"holding the forms of degree d in the ideal",
			"«forms»(d) ∩ ideal_span(«polynomials», E) ⊆ «vanishing»",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(set_basic.SubsetDef)))
				u := b.FixAs[_Polynomial]("u")
				given := b.Assume()
				inside := b.Have(
					"u is a form of degree d in the ideal",
					"u ∈ «forms»(d) ∧ u ∈ ideal_span(«polynomials», E)",
					BySets(given))
				value := b.Have(
					"so u vanishes at z",
					"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, u) = M.zero",
					BySets(inside, idealVanishes, ring_homomorphism.RingKernelDef.At(zeroM, polynomialsK, evaluate)))
				b.Show(
					"a form of degree d vanishing at z is in the kernel",
					By(inside, value, group_homomorphism.InKernel.At(zeroM, formsD, evaluate, u)))
			}))
		holdsMultiples := a.Have(
			"and F times every form of degree d − r, F vanishing at z",
			Statement{
				Binders:    "∀Q:((num → num) → A).",
				Hypotheses: []string{"homogeneous_polynomial(«hilbertCoefficients», n, d - r, Q)"},
				Conclusion: "polynomial_algebra_mul(«hilbertCoefficients», F, Q) ∈ «vanishing»",
			},
			Derive(func(b *Argument) {
				Q := b.FixAs[_Polynomial]("Q")
				given := b.Assume()
				degree := b.Have(
					"r + (d − r) is d",
					"r + (d - r) = d",
					ByArith(below))
				product := b.Simplified(
					b.Have(
						"F·Q is a form of degree r + (d − r)",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    r + (d - r), "+
							"    polynomial_algebra_mul(«hilbertCoefficients», F, Q))",
						By(
							form,
							given,
							scalars,
							At(homogeneous_polynomial.FormProduct, K, n, r, b.TermAs[Nat]("d - r"), F, Q))),
					Fwd(degree))
				polynomialQ := b.Have(
					"Q is a polynomial over k",
					"Q ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					By(given, homogeneous_polynomial.FormPolynomial.At(K, n, b.TermAs[Nat]("d - r"), Q)))
				valueQ := b.TermAs[A](
					"polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, Q)")
				b.Show(
					"F·Q is a form of degree d whose value at z is F(z)·Q(z) = 0",
					By(
						product,
						zero,
						polynomialF,
						polynomialQ,
						ring_homomorphism.MapMul.Read(evaluation).AsFact().At(F, Q),
						ring_homomorphism.MapIn.Read(evaluation).AsFact().At(Q),
						comm_ring.MulLeftZeroOn.Read(field.RingOn.Read(M)).AsFact().At(valueQ),
						group_homomorphism.InKernel.At(
							b.TermAs[A]("M.zero"),
							b.TermAs[Set[_Polynomial]]("«forms»(d)"),
							evaluate,
							b.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», F, Q)"))))
			}))
		codimension := a.Have(
			"so the kernel has codimension at most h(d) − h(d − r)",
			"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), «vanishing»)) + "+
				"projective_hilbert_function(field_ring(M), k, n, E, d - r) ≤ "+
				"projective_hilbert_function(field_ring(M), k, n, E, d)",
			By(
				subK,
				prime,
				polynomialF,
				outside,
				kernel,
				holdsIdeal,
				holdsMultiples,
				Read(projective_curve.HyperplaneSectionBound, M).At(
					k, n, d, a.TermAs[Nat]("d - r"), E, vanishing, F)))
		rank := a.Have(
			"by rank and nullity the values have the dimension of the forms of degree d less the kernel's",
			"module_dim(«hilbertCoefficients», restrict_module(«formSpace»(d), «vanishing»)) + "+
				"module_dim(«hilbertCoefficients», «valueSpace»(d)) = "+
				"module_dim(«hilbertCoefficients», «formSpace»(d))",
			By(
				moduleD,
				kField,
				regular,
				linear,
				finiteD,
				module_dimension.RankNullity.At(K, spaceD, inv, regularM, evaluate)))
		quotient := a.Have(
			"which is the kernel's codimension",
			"module_dim(«hilbertCoefficients», restrict_module(«formSpace»(d), «vanishing»)) + "+
				"module_dim(«hilbertCoefficients», quotient_module(«formSpace»(d), «vanishing»)) = "+
				"module_dim(«hilbertCoefficients», «formSpace»(d))",
			By(moduleD, kField, finiteD, kernel, module_dimension.QuotientDim.At(K, spaceD, inv, vanishing)))
		a.Show(
			"the values are a finite-dimensional subspace of M of dimension at most h(d) − h(d − r)",
			SplitConj(
				Case(
					"the values are a finite-dimensional subspace of M",
					By(
						module_homomorphism.ImageSubmodule.Read(linear),
						kField,
						linear,
						finiteD,
						module_dimension.ImageDim.At(K, inv, spaceD, regularM, evaluate))),
				Case(
					"of dimension at most h(d) − h(d − r)",
					ByArith(codimension, rank, quotient)),
			))
	}),
})}

// FormZerosRational — the zeros on a smooth projective equation curve of a
// form over k outside the ideal have their coordinates in one finite
// subfield of M. With h(d) + g = e·d + 1 from N on, take s divisible by
// every positive m ≤ e·r. At a zero z of F on the curve, with z(j) = 1, the
// values at z of the forms of degree d = N + e·r + r span at most
// h(d) − h(d − r) = e·r dimensions over k (FormValuesBound), and they hold
// the powers z(i)ᵗ, t ≤ e·r (projective_curve.CoordinatePowerValue); so
// z(i) has degree at most e·r over k (algebraic_element.BoundedPowersDegree)
// and lies in the field of q^s elements
// (finite_field.BoundedDegreeInConstants). The coordinates beyond n are zero.
var FormZerosRational = formZerosRationalThm{family.Add(registry.ProofEntry{
	Name: "FormZerosRational",
	Key:  "prop_97ff1abafa9969d1",
	Reading: "F outside the ideal is load-bearing: a form in the ideal vanishes at the generic " +
		"point, whose coordinates are transcendental. The s found depends on E and r only through " +
		"the slope e of the Hilbert function, not on F, and the coordinates beyond n are zero, " +
		"which every finite subfield holds. Neither an algebraically closed M nor a positive r is " +
		"needed: the field of q^s elements is read as the points of M fixed by the q^s-th power, " +
		"and a form of degree zero outside the ideal is a nonzero constant, with no zeros.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n r:num. ∀E:set((num → num) → A). ∀F:((num → num) → A).",
		Hypotheses: []string{
			"smooth_projective_equation_curve(M, k, n, E)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"F ∉ ideal_span(«polynomials», E)",
		},
		Conclusion: "∃s:num. " +
			"    0 < s ∧ " +
			"    (∀z:(num → A). " +
			"        z ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E) ∧ " +
			"        polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, F) = " +
			"        M.zero ⇒ " +
			"        (∀i:num. z(i) ∈ finite_constants(field_ring(M), card(k), s)))",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, r *Expr[Nat],
		E *Expr[Set[_Polynomial]],
		F *Arrow[Fun[Nat, Nat], A],
		curve, form, outside Fact,
	) {
		subK := projective_curve.CurveConstantsSubfield.Read(curve)
		finiteK := projective_curve.CurveConstantsFinite.Read(curve)
		_, e, _, linear := a.Unpack3As[Nat, Nat, Nat](
			projective_curve.CurveHilbertEventuallyLinear.Read(curve), "g", "e", "N")
		growth := a.Conjuncts(
			linear,
			"the slope e is positive",
			"and h(d) + g = e·d + 1 from N on")
		bound := a.TermAs[Nat]("e * r")
		s, common := a.UnpackAs[Nat](
			GroupPremises(
				num_segment.FiniteBelow.At(bound),
				nat_sum.FinitePositiveCommonMultiple.At(a.TermAs[Set[Nat]]("{m:num | m ≤ e * r}"))),
			"s")
		multiple := a.Conjuncts(
			common,
			"s is positive",
			"and a multiple of every positive m ≤ e·r")
		divides := a.Have(
			"every positive m ≤ e·r divides s",
			"∀m:num. 0 < m ∧ m ≤ e * r ⇒ m ∣ s",
			BySets(multiple[1]))
		a.Take(s)
		a.Show(
			"s is positive, and the field of q^s elements holds "+
				"the coordinates of every zero of F on the curve",
			SplitConj(
				Case(
					"s is positive",
					By(multiple[0])),
				Case(
					"the field of q^s elements holds the coordinates of every zero of F on the curve",
					Derive(func(b *Argument) {
						z := b.FixAs[Fun[Nat, A]]("z")
						given := b.Assume()
						zeroOfF := b.Conjuncts(
							given,
							"z is a point of the curve",
							"at which F vanishes")
						point, zero := zeroOfF[0], zeroOfF[1]
						coordinates := b.Conjuncts(
							b.Unfolded(point, projective_curve.ProjectiveEquationPointsDef),
							"the coordinates of z up to n lie in M",
							"those beyond n are zero",
							"one of them is one, the earlier ones zero",
							"and every equation vanishes at z")
						inM, beyond := coordinates[0], coordinates[1]
						j, normalized := b.UnpackAs[Nat](coordinates[2], "j")
						unit := b.Conjuncts(
							normalized,
							"j ≤ n",
							"z(j) = 1",
							"and the coordinates before j are zero")
						d := b.TermAs[Nat]("N + e * r + r")
						values := b.TermAs[Set[A]](
							"image(polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z), " +
								"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, N + e * r + r, P)})")
						degreeBelow := b.Have(
							"r ≤ d, as d = N + e·r + r",
							"r ≤ N + e * r + r",
							ByArith())
						span := b.Conjuncts(
							GroupPremises(
								curve, form, outside, degreeBelow, point, zero, Read(FormValuesBound, M).At(k, n, r, d, E, F, z)),
							"the values at z of the forms of degree d are a subspace of M",
							"finite-dimensional",
							"of dimension at most h(d) − h(d − r)")
						shift := b.Have(
							"d − r is N + e·r",
							"(N + e * r + r) - r = N + e * r",
							ByArith())
						atD := b.Have(
							"h(d) + g = e·d + 1",
							"projective_hilbert_function(field_ring(M), k, n, E, N + e * r + r) + g = e * (N + e * r + r) + 1",
							ByArith(growth[1].At(d)))
						atShift := b.Have(
							"h(d − r) + g = e·(d − r) + 1",
							"projective_hilbert_function(field_ring(M), k, n, E, N + e * r) + g = e * (N + e * r) + 1",
							ByArith(growth[1].At(b.TermAs[Nat]("N + e * r"))))
						dimension := b.Have(
							"so the values span at most e·r dimensions",
							"module_dim(«hilbertCoefficients», "+
								"    restrict_module(regular_module(field_ring(M)), "+
								"        image(polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z), "+
								"            {P:(num → num) → A | "+
								"                homogeneous_polynomial(«hilbertCoefficients», n, N + e * r + r, P)}))) ≤ "+
								"e * r",
							ByArith(
								b.Simplified(span[2], Fwd(shift)),
								atD,
								atShift,
								nat_arith.LeftAddDistrib.At(e, b.TermAs[Nat]("N + e * r"), r)))
						i := b.FixAs[Nat]("i")
						b.Cases(b.TermAs[Bool]("i ≤ n"))
						b.When(
							"a coordinate up to n has its powers up to e·r among the values, so degree at most e·r over k",
							func(c *Argument, within Fact) {
								y := c.TermAs[A]("z(i)")
								yIn := c.Have(
									"z(i) lies in M",
									"z(i) ∈ M.carrier",
									By(within, inM.At(i)))
								powers := c.Have(
									"its powers up to e·r are values at z of forms of degree d",
									Statement{
										Binders:    "∀t:num.",
										Hypotheses: []string{"t ≤ e * r"},
										Conclusion: "monoid_pow(M.mul, M.one, z(i), t) ∈ " +
											"image(polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z), " +
											"    {P:(num → num) → A | homogeneous_polynomial(«hilbertCoefficients», n, N + e * r + r, P)})",
									},
									Derive(func(x *Argument) {
										t := x.FixAs[Nat]("t")
										small := x.Assume()
										tBelow := x.Have(
											"t ≤ d, as t ≤ e·r and d = N + e·r + r",
											"t ≤ N + e * r + r",
											ByArith(small))
										x.Show(
											"z(i)ᵗ is the value of the monomial Xᵢᵗ·Xⱼᵈ⁻ᵗ",
											By(
												M,
												subK,
												field.SubfieldSubring.Read(M).At(k),
												ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(M)).At(k),
												within,
												unit[0],
												tBelow,
												inM,
												unit[1],
												projective_curve.CoordinatePowerValue.At(
													x.TermAs[FieldOps[A]]("M"),
													x.TermAs[FieldOps[A]]("M"),
													k,
													n,
													d,
													x.TermAs[Fun[A, A]]("λa:A. a"),
													z,
													i,
													j,
													t)))
									}))
								algebraic := c.Have(
									"so z(i) is algebraic over k of degree at most e·r",
									"algebraic_over(M, k, z(i)) ∧ extension_degree(M, k, field_adjoin(M, k, {z(i)})) ≤ e * r",
									By(
										subK,
										yIn,
										span[0],
										span[1],
										dimension,
										powers,
										Read(algebraic_element.BoundedPowersDegree, M).At(k, values, bound, y)))
								c.Show(
									"and lies in the field of q^s elements",
									By(
										subK,
										finiteK,
										yIn,
										algebraic,
										divides,
										Read(finite_field.BoundedDegreeInConstants, M).At(k, bound, s, y)))
							})
						b.Otherwise(
							"a coordinate beyond n is zero, which the field of q^s elements holds",
							func(c *Argument, past Fact) {
								one := c.TermAs[Nat]("1")
								q := c.TermAs[Nat]("card(k)")
								after := c.Have(
									"n < i, as i is not at most n",
									"n < i",
									ByArith(past))
								zeroInK := c.Have(
									"zero lies in k",
									"M.zero ∈ k",
									By(subK, field.SubfieldZero.At(c.TermAs[FieldOps[A]]("M"), k)))
								kConstants := c.Have(
									"k, of q elements, is the field of q¹ elements",
									"k ⊆ finite_constants(field_ring(M), card(k), 1)",
									By(
										subK,
										finiteK,
										nat_arith.PowOne.At(q),
										finite_field.FiniteSubfieldInConstants.Read(M).At(k, q, one)))
								grows := c.Have(
									"which lies in the field of q^s elements, 1 dividing s",
									"finite_constants(field_ring(M), card(k), 1) ⊆ finite_constants(field_ring(M), card(k), s)",
									By(
										nat_divides.OneDivides.At(s),
										finite_field.FiniteConstantsMono.Read(field.RingOn.Read(M)).At(q, one, s)))
								c.Show(
									"so it holds the zero coordinate z(i)",
									By(after, beyond.At(i), zeroInK, kConstants, grows, set_basic.SubsetDef))
							})
					})),
			))
	}),
})}

// AnisotropicForm — over a finite subfield k of a field M, for every s > 0
// there is a form over k of positive degree with no zero among the nonzero
// points of n + 1 coordinates over the field of q^s elements, q = card(k):
// with Q = q^s, a point c of that field has c^((Q − 1)·t) equal to one or
// zero as c is nonzero or zero, so X₀^(Q − 1) is the indicator of a nonzero
// first coordinate, and G·G + Y·(Y − G) with Y = X_(m+1)^(deg G) is the
// indicator of a nonzero coordinate among the first m + 2, since a·a +
// b·(b − a) is the indicator of a ∨ b at the indicators a and b.
var AnisotropicForm = anisotropicFormThm{family.Add(registry.ProofEntry{
	Name: "AnisotropicForm",
	Key:  "prop_7693abf868ef6280",
	Reading: "No closure of M is read: only x^Q = x on the coordinates, Q = card(k)^s, enters, and " +
		"the form found takes the value one at every point with a nonzero coordinate. Its degree is (Q " +
		"− 1)·2^n, set by k, s and n alone. k finite and 0 < s are load-bearing: they make Q at least " +
		"two, so that Q − 1 is a positive degree; at s = 0 the field of q^0 elements is the whole of M.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n s:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"0 < s",
		},
		Conclusion: "∃r:num. ∃G:((num → num) → A). " +
			"    0 < r ∧ " +
			"    homogeneous_polynomial(«hilbertCoefficients», n, r, G) ∧ " +
			"    (∀z:(num → A). " +
			"        (∀i:num. i ≤ n ⇒ z(i) ∈ finite_constants(field_ring(M), card(k), s)) ∧ " +
			"        (∃i:num. i ≤ n ∧ z(i) ≠ M.zero) ⇒ " +
			"        polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), z, G) ≠ M.zero)",
		Abbrev: Abbrev{
			{Name: "value", Text: "λy:(num → A). λP:((num → num) → A). " +
				"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), (λa:A. a), y, P)"},
			{Name: "indicator", Text: "λb:bool. COND(b, M.one, M.zero)"},
			{Name: "varPower", Text: "λj:num. λt:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», j), " +
				"        (card(k) ^ s - 1) * t)"},
			{Name: "minus", Text: "λP:((num → num) → A). λQ:((num → num) → A). " +
				"    fun_add(«hilbertCoefficients».add, P, fun_neg(«hilbertCoefficients».neg, Q))"},
			{Name: "either", Text: "λP:((num → num) → A). λQ:((num → num) → A). " +
				"    fun_add(«hilbertCoefficients».add, " +
				"        polynomial_algebra_mul(«hilbertCoefficients», P, P), " +
				"        polynomial_algebra_mul(«hilbertCoefficients», Q, «minus»(Q, P)))"},
			{Name: "indicatorForm", Text: "λm:num. ∃t:num. ∃G:((num → num) → A). " +
				"    0 < t ∧ " +
				"    homogeneous_polynomial(«hilbertCoefficients», n, (card(k) ^ s - 1) * t, G) ∧ " +
				"    (∀z:(num → A). " +
				"        (∀i:num. i ≤ n ⇒ z(i) ∈ finite_constants(field_ring(M), card(k), s)) ⇒ " +
				"        «value»(z, G) = «indicator»(∃i:num. i ≤ m ∧ z(i) ≠ M.zero))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, s *Expr[Nat],
		subfieldK, finiteK, positiveS Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		coefficients := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		q := a.TermAs[Nat]("card(k)")
		unitExponent := a.TermAs[Nat]("card(k) ^ s - 1")
		large := a.Have(
			"the field of q^s elements has more than one",
			"1 < card(k) ^ s",
			By(M, subfieldK, finiteK, positiveS, finite_field.FiniteSubfieldPowerEndomorphism.At(fieldM, k, s)))
		inclusion := a.Have(
			"the inclusion of k into M is a ring map",
			"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
			By(
				subfieldK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
		coefficientRing := ring_homomorphism.Source.Read(inclusion)
		powers := a.Have(
			"the (q^s − 1)·t-th power of a variable is a form of degree (q^s − 1)·t",
			Statement{
				Binders:    "∀j t:num.",
				Hypotheses: []string{"j ≤ n"},
				Conclusion: "homogeneous_polynomial(«hilbertCoefficients», " +
					"    n, " +
					"    (card(k) ^ s - 1) * t, " +
					"    «varPower»(j, t))",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				b.FixAs[Nat]("t")
				inRange := b.Assume()
				exponent := b.TermAs[Nat]("(card(k) ^ s - 1) * t")
				b.Show(
					"a power of the variable Xⱼ, a form of degree one",
					By(
						inRange,
						coefficientRing,
						homogeneous_polynomial.FormVariable.At(coefficients, n, j),
						homogeneous_polynomial.FormPower.At(
							coefficients,
							n,
							b.TermAs[Nat]("1"),
							b.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», j)"),
							exponent),
						nat_arith.OneMul.At(exponent)))
			}))
		values := a.Have(
			"at a point over the field of q^s elements that "+
				"power is the indicator of a nonzero coordinate at j",
			Statement{
				Binders: "∀j t:num. ∀z:(num → A).",
				Hypotheses: []string{
					"j ≤ n",
					"0 < t",
					"∀i:num. i ≤ n ⇒ z(i) ∈ finite_constants(field_ring(M), card(k), s)",
				},
				Conclusion: "«value»(z, «varPower»(j, t)) = «indicator»(z(j) ≠ M.zero)",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				t := b.FixAs[Nat]("t")
				z := b.FixAs[Fun[Nat, A]]("z")
				given := b.Conjuncts(
					b.Assume(),
					"Xⱼ is a variable",
					"t is positive",
					"the coordinates lie in the field of q^s elements")
				inM := b.Have(
					"so they lie in M",
					"∀i:num. i ≤ n ⇒ z(i) ∈ M.carrier",
					BySets(given[2], finite_field.FiniteConstantsDef.At(fieldRing, q, s)))
				evaluation := b.Have(
					"evaluation at z is a ring map out of the polynomials over k",
					"ring_homomorphism(«polynomials», "+
						"    field_ring(M), "+
						"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, z))",
					By(inM, inclusion, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
				exponent := b.TermAs[Nat]("(card(k) ^ s - 1) * t")
				power := b.Have(
					"it takes the power of Xⱼ to the power of z(j)",
					"«value»(z, «varPower»(j, t)) = monoid_pow(M.mul, M.one, z(j), (card(k) ^ s - 1) * t)",
					By(
						given[0],
						inM,
						inclusion,
						coefficientRing,
						homogeneous_polynomial.FormVariable.At(coefficients, n, j),
						homogeneous_polynomial.FormPolynomial,
						polynomial_algebra.PolynomialAlgebraRingDef,
						ring_homomorphism.RingMapPower.Read(evaluation).AsFact().At(
							exponent, b.TermAs[_Polynomial]("polynomial_algebra_var(«hilbertCoefficients», j)")),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(coefficients, fieldRing, identity, z, j)))
				b.Show(
					"a positive multiple of q^s − 1 as exponent is one off zero and zero at zero",
					power.Rw(),
					By(
						Normalized,
						M,
						large,
						given[0],
						given[1],
						given[2],
						At(finite_field.FiniteConstantsFermat, fieldM, q, s, t, b.TermAs[A]("z(j)"))))
			}))
		disjunction := a.Have(
			"at the indicators x and y of u and v, x·x + y·(y − x) is the indicator of u ∨ v",
			"∀u v:bool. "+
				"    «indicator»(u) * «indicator»(u) + «indicator»(v) * («indicator»(v) + -«indicator»(u)) = "+
				"    «indicator»(u ∨ v)",
			Derive(func(b *Argument) {
				u := b.FixAs[Bool]("u")
				v := b.FixAs[Bool]("v")
				b.Cases(u)
				b.When(
					"where u holds the left indicator is one",
					func(c *Argument, holds Fact) {
						c.Cases(v)
						c.When(
							"one·one + one·(one − one) is one",
							func(d *Argument, also Fact) {
								d.Show(
									"by ring arithmetic in M",
									ByArith(holds, also, M, comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
							})
						c.Otherwise(
							"one·one + zero·(zero − one) is one",
							func(d *Argument, fails Fact) {
								d.Show(
									"by ring arithmetic in M",
									ByArith(holds, fails, M, comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
							})
					})
				b.Otherwise(
					"where u fails the left indicator is zero",
					func(c *Argument, fails Fact) {
						c.Cases(v)
						c.When(
							"zero·zero + one·(one − zero) is one",
							func(d *Argument, holds Fact) {
								d.Show(
									"by ring arithmetic in M",
									ByArith(fails, holds, M, comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
							})
						c.Otherwise(
							"zero·zero + zero·(zero − zero) is zero",
							func(d *Argument, neither Fact) {
								d.Show(
									"by ring arithmetic in M",
									ByArith(fails, neither, M, comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
							})
					})
			}))
		tower := a.Have(
			"for each m up to n some form over k is the indicator "+
				"of a nonzero coordinate among the first m + 1",
			"∀m:num. m ≤ n ⇒ «indicatorForm»(m)",
			Derive(func(b *Argument) {
				b.Induct("m")
				b.Base(
					"X₀^(q^s − 1) is the indicator of a nonzero first coordinate",
					func(c *Argument) {
						zeroIn := c.Assume()
						c.Take(c.TermAs[Nat]("1"))
						c.Take(c.TermAs[_Polynomial]("«varPower»(0, 1)"))
						first := c.Have(
							"its value is the indicator of a nonzero coordinate at 0",
							Statement{
								Binders:    "∀z:(num → A).",
								Hypotheses: []string{"∀i:num. i ≤ n ⇒ z(i) ∈ finite_constants(field_ring(M), card(k), s)"},
								Conclusion: "«value»(z, «varPower»(0, 1)) = «indicator»(∃i:num. i ≤ 0 ∧ z(i) ≠ M.zero)",
							},
							Derive(func(d *Argument) {
								z := d.FixAs[Fun[Nat, A]]("z")
								coordinates := d.Assume()
								atZero := d.Have(
									"the only coordinate up to 0 is the one at 0",
									"(∃i:num. i ≤ 0 ∧ z(i) ≠ M.zero) ⇔ z(0) ≠ M.zero",
									By(nat_order.LessEqZeroClause))
								d.Show(
									"the power of X₀ is the indicator of z(0) ≠ 0",
									atZero.Rw(),
									By(zeroIn, coordinates, values.At(c.TermAs[Nat]("0"), c.TermAs[Nat]("1"), z)))
							}))
						c.Show(
							"X₀^(q^s − 1) is a form of degree q^s − 1 with that value",
							By(zeroIn, powers.At(c.TermAs[Nat]("0"), c.TermAs[Nat]("1")), first))
					})
				b.Step(
					"G·G + Y·(Y − G), Y = X_(m+1)^(deg G), is the "+
						"indicator one coordinate further, of twice the degree",
					func(c *Argument, ih Fact) {
						inRange := c.Assume()
						below := c.Have(
							"m lies below n too",
							"m ≤ n",
							ByArith(inRange))
						t, G, data := c.Obtain2As[Nat, _Polynomial](
							"so the hypothesis gives a form G of degree (q^s − 1)·t for m",
							"«indicatorForm»(m)",
							By(below, ih),
							Named("t", "G"))
						parts := c.Conjuncts(
							data,
							"t is positive",
							"G is a form of degree (q^s − 1)·t",
							"G is the indicator of a nonzero coordinate up to m")
						next := c.TermAs[Nat]("suc(m)")
						degree := c.TermAs[Nat]("(card(k) ^ s - 1) * t")
						doubled := c.TermAs[Nat]("(card(k) ^ s - 1) * t + (card(k) ^ s - 1) * t")
						Y := c.TermAs[_Polynomial]("«varPower»(suc(m), t)")
						negated := c.TermAs[_Polynomial]("fun_neg(«hilbertCoefficients».neg, G)")
						difference := c.TermAs[_Polynomial]("«minus»(«varPower»(suc(m), t), G)")
						square := c.TermAs[_Polynomial]("polynomial_algebra_mul(«hilbertCoefficients», G, G)")
						cross := c.TermAs[_Polynomial](
							"polynomial_algebra_mul(«hilbertCoefficients», " +
								"    «varPower»(suc(m), t), " +
								"    «minus»(«varPower»(suc(m), t), G))")
						yForm := c.Have(
							"Y is a form of degree (q^s − 1)·t",
							"homogeneous_polynomial(«hilbertCoefficients», n, (card(k) ^ s - 1) * t, «varPower»(suc(m), t))",
							By(inRange, powers.At(next, t)))
						negatedForm := c.Have(
							"so is −G",
							"homogeneous_polynomial(«hilbertCoefficients», "+
								"    n, "+
								"    (card(k) ^ s - 1) * t, "+
								"    fun_neg(«hilbertCoefficients».neg, G))",
							By(coefficientRing, parts[1], homogeneous_polynomial.FormNeg.At(coefficients, n, degree, G)))
						differenceForm := c.Have(
							"and so is Y − G",
							"homogeneous_polynomial(«hilbertCoefficients», "+
								"    n, "+
								"    (card(k) ^ s - 1) * t, "+
								"    «minus»(«varPower»(suc(m), t), G))",
							By(
								coefficientRing,
								yForm,
								negatedForm,
								homogeneous_polynomial.FormSum.At(coefficients, n, degree, Y, negated)))
						productForms := c.Have(
							"G·G and Y·(Y − G) are forms of twice that degree",
							"homogeneous_polynomial(«hilbertCoefficients», "+
								"    n, "+
								"    (card(k) ^ s - 1) * t + (card(k) ^ s - 1) * t, "+
								"    polynomial_algebra_mul(«hilbertCoefficients», G, G)) ∧ "+
								"homogeneous_polynomial(«hilbertCoefficients», "+
								"    n, "+
								"    (card(k) ^ s - 1) * t + (card(k) ^ s - 1) * t, "+
								"    polynomial_algebra_mul(«hilbertCoefficients», "+
								"        «varPower»(suc(m), t), "+
								"        «minus»(«varPower»(suc(m), t), G)))",
							By(
								coefficientRing,
								parts[1],
								yForm,
								differenceForm,
								homogeneous_polynomial.FormProduct.At(coefficients, n, degree, degree, G, G),
								homogeneous_polynomial.FormProduct.At(coefficients, n, degree, degree, Y, difference)))
						sumForm := c.Have(
							"so is their sum",
							"homogeneous_polynomial(«hilbertCoefficients», "+
								"    n, "+
								"    (card(k) ^ s - 1) * t + (card(k) ^ s - 1) * t, "+
								"    «either»(G, «varPower»(suc(m), t)))",
							By(
								coefficientRing,
								productForms,
								homogeneous_polynomial.FormSum.At(coefficients, n, doubled, square, cross)))
						stepValue := c.Have(
							"its value is the indicator of a nonzero coordinate up to m + 1",
							Statement{
								Binders:    "∀z:(num → A).",
								Hypotheses: []string{"∀i:num. i ≤ n ⇒ z(i) ∈ finite_constants(field_ring(M), card(k), s)"},
								Conclusion: "«value»(z, «either»(G, «varPower»(suc(m), t))) = " +
									"«indicator»(∃i:num. i ≤ suc(m) ∧ z(i) ≠ M.zero)",
							},
							Derive(func(d *Argument) {
								z := d.FixAs[Fun[Nat, A]]("z")
								coordinates := d.Assume()
								inM := d.Have(
									"the coordinates lie in M",
									"∀i:num. i ≤ n ⇒ z(i) ∈ M.carrier",
									BySets(coordinates, finite_field.FiniteConstantsDef.At(fieldRing, q, s)))
								evaluation := d.Have(
									"evaluation at z is a ring map out of the polynomials over k",
									"ring_homomorphism(«polynomials», "+
										"    field_ring(M), "+
										"    polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, z))",
									By(inM, inclusion, polynomial_algebra_evaluation.PolynomialAlgebraEvalHom))
								members := d.Have(
									"G, Y, −G, Y − G, G·G and Y·(Y − G) are polynomials over k",
									"G ∈ «polynomials».carrier ∧ "+
										"«varPower»(suc(m), t) ∈ «polynomials».carrier ∧ "+
										"fun_neg(«hilbertCoefficients».neg, G) ∈ «polynomials».carrier ∧ "+
										"«minus»(«varPower»(suc(m), t), G) ∈ «polynomials».carrier ∧ "+
										"polynomial_algebra_mul(«hilbertCoefficients», G, G) ∈ «polynomials».carrier ∧ "+
										"polynomial_algebra_mul(«hilbertCoefficients», "+
										"    «varPower»(suc(m), t), "+
										"    «minus»(«varPower»(suc(m), t), G)) ∈ "+
										"«polynomials».carrier",
									By(
										parts[1],
										yForm,
										negatedForm,
										differenceForm,
										productForms,
										homogeneous_polynomial.FormPolynomial))
								expanded := d.Have(
									"evaluation keeps the sums, products and negative",
									"«value»(z, «either»(G, «varPower»(suc(m), t))) = "+
										"«value»(z, G) * «value»(z, G) + "+
										"«value»(z, «varPower»(suc(m), t)) * («value»(z, «varPower»(suc(m), t)) + -«value»(z, G))",
									By(
										members,
										polynomial_algebra.PolynomialAlgebraRingDef,
										ring_homomorphism.MapAdd.Read(evaluation).AsFact().At(square, cross),
										ring_homomorphism.MapMul.Read(evaluation).AsFact().At(G, G),
										ring_homomorphism.MapMul.Read(evaluation).AsFact().At(Y, difference),
										ring_homomorphism.MapAdd.Read(evaluation).AsFact().At(Y, negated),
										ring_homomorphism.MapNeg.Read(evaluation).AsFact().At(G)))
								gValue := d.Have(
									"G(z) is the indicator of a nonzero coordinate up to m",
									"«value»(z, G) = «indicator»(∃i:num. i ≤ m ∧ z(i) ≠ M.zero)",
									By(coordinates, parts[2].At(z)))
								yValue := d.Have(
									"Y(z) is the indicator of a nonzero coordinate at m + 1",
									"«value»(z, «varPower»(suc(m), t)) = «indicator»(z(suc(m)) ≠ M.zero)",
									By(inRange, parts[0], coordinates, values.At(next, t, z)))
								further := d.Have(
									"a nonzero coordinate up to m + 1 is one up to m or the one at m + 1",
									"(∃i:num. i ≤ suc(m) ∧ z(i) ≠ M.zero) ⇔ (∃i:num. i ≤ m ∧ z(i) ≠ M.zero) ∨ z(suc(m)) ≠ M.zero",
									By(nat_order.LessEqSucClause))
								d.Show(
									"so G·G + Y·(Y − G) at z is the indicator of the disjunction",
									expanded.Rw(),
									gValue.Rw(),
									yValue.Rw(),
									further.Rw(),
									By(disjunction.At(
										d.TermAs[Bool]("∃i:num. i ≤ m ∧ z(i) ≠ M.zero"), d.TermAs[Bool]("z(suc(m)) ≠ M.zero"))))
							}))
						positive := c.Have(
							"t + t is positive",
							"0 < t + t",
							ByArith(parts[0]))
						c.Take(c.TermAs[Nat]("t + t"))
						c.Take(c.TermAs[_Polynomial]("«either»(G, «varPower»(suc(m), t))"))
						c.Show(
							"a form of degree (q^s − 1)·(t + t) with that value",
							By(positive, sumForm, stepValue, nat_arith.LeftAddDistrib.At(unitExponent, t, t)))
					})
			}))
		t, G, data := a.Unpack2As[Nat, _Polynomial](
			GroupPremises(nat_order.LessEqRefl.At(n), tower.At(n)), "t", "G")
		parts := a.Conjuncts(
			data,
			"t is positive",
			"G is a form of degree (q^s − 1)·t",
			"G is the indicator of a nonzero coordinate up to n")
		positive := a.Have(
			"so (q^s − 1)·t is positive",
			"0 < (card(k) ^ s - 1) * t",
			ByArith(large, parts[0], nat_arith.MulEqZero.At(unitExponent, t)))
		nonzero := a.Have(
			"G is one at every point with a nonzero coordinate",
			Statement{
				Binders: "∀z:(num → A).",
				Hypotheses: []string{
					"∀i:num. i ≤ n ⇒ z(i) ∈ finite_constants(field_ring(M), card(k), s)",
					"∃i:num. i ≤ n ∧ z(i) ≠ M.zero",
				},
				Conclusion: "«value»(z, G) ≠ M.zero",
			},
			Derive(func(b *Argument) {
				z := b.FixAs[Fun[Nat, A]]("z")
				given := b.Assume()
				b.Show(
					"one is not zero in a field",
					By(given, parts[2].At(z), field.OneNotZeroOn.Read(M)))
			}))
		a.Take(a.TermAs[Nat]("(card(k) ^ s - 1) * t"))
		a.Take(G)
		a.Show(
			"a form of the positive degree (q^s − 1)·t with no zero at a nonzero point",
			By(positive, parts[1], nonzero))
	}),
})}
