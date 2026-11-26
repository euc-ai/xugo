// line.go — the line X₂ = 0 of the projective plane as a smooth projective
// equation curve of genus zero.

package projective_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PlaneLineCurve — the line X₂ = 0 in the projective plane, over a finite
// field k inside any field M, is a smooth projective equation curve of
// genus zero. Its ideal over M is prime, X₂ being a variable
// (polynomial_algebra_evaluation.VariableIdealPrime); (1 : 0 : 0) is a point of it; as
// the plane curve of degree one its Hilbert function is d + 1 from degree one on
// (PlaneCurveHilbertFunction), so along the multiples of 1 the genus is zero
// (GenusAlongMultiples); and at every point the gradient of X₂ is the
// coordinate vector of 2, which spans a line, of dimension 1 = 2 − 1.
var PlaneLineCurve = planeLineCurveThm{family.Add(registry.ProofEntry{
	Name: "PlaneLineCurve",
	Key:  "prop_64b3768887c088cb",
	Reading: "The line exercises every conjunct of smooth_projective_equation_curve: k a finite " +
		"subfield of M, n = 2 > 0, the one equation X₂, a form of degree one, its ideal over M " +
		"prime, the point (1 : 0 : 0) over M, the Hilbert function d + 1 from degree one on, and at " +
		"every point one gradient, the coordinate vector of 2, spanning a line of dimension n − 1. " +
		"M need not be algebraically closed: each conjunct holds over any field M, the ideal of a " +
		"variable being prime over every domain and the gradient of X₂ the same at every point. " +
		"finite(k) is asked only because the predicate states it; no other conjunct reads it.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
		},
		Conclusion: "smooth_projective_equation_curve(M, k, 2, «lineEquation») ∧ " +
			"projective_equation_genus(field_ring(M), k, 2, «lineEquation») = 0",
		Abbrev: Abbrev{
			{Name: "lineEquation", Text: "{polynomial_algebra_var(«hilbertCoefficients», 2)}"},
			{Name: "coordinates", Text: "free_module_record(field_ring(M), {i:num | i ≤ 2})"},
			// the line the coordinate vector of 2 spans
			{Name: "gradientLine", Text: "module_span(field_ring(M), «coordinates», {delta_at(2)})"},
		},
	}, func(a *Argument, M field.FieldFact[on.M], k *Expr[Set[A]], subK, finiteK Fact) {
		type polynomial = Fun[Fun[Nat, Nat], A]
		type vector = Fun[Nat, A]
		K := a.TermAs[RingOps[A]]("«hilbertCoefficients»")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(M)")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		inv := a.TermAs[Fun[A, A]]("M.inv")
		zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
		indices := a.TermAs[Set[Nat]]("{i:num | i ≤ 2}")
		variable := a.TermAs[polynomial]("polynomial_algebra_var(«hilbertCoefficients», 2)")
		equations := a.TermAs[Set[polynomial]]("«lineEquation»")
		origin := a.TermAs[vector]("λi:num. COND(i = 0, M.one, M.zero)")
		delta := a.TermAs[vector]("delta_at(2)")
		coordinates := a.TermAs[module_record.ModuleOps[A, vector]]("«coordinates»")
		ringM := field.RingOn.Read(M)
		oneNotZero := integral_domain.OneNotZero.Read(integral_domain.FieldIntegralDomain.Read(M))
		scalars := a.Have(
			"k is a commutative ring",
			"comm_ring_on(«hilbertCoefficients»)",
			By(subK, field.SubfieldCommRing.Read(M).At(k)))
		inclusion := a.Have(
			"k includes into M as a ring map",
			"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
			By(
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.SubringInclusionHom.Read(ringM).At(k)))
		form := a.Have(
			"X₂ is a form of degree one over k",
			"homogeneous_polynomial(«hilbertCoefficients», "+
				"    2, "+
				"    1, "+
				"    polynomial_algebra_var(«hilbertCoefficients», 2))",
			By(scalars, homogeneous_polynomial.FormVariable.At(K, two, two), nat_order.LessEqRefl.At(two)))

		// The ideal over M.
		sameVariable := a.Have(
			"X₂ over k is X₂ over M, k's ring having M's zero and one",
			"polynomial_algebra_var(«hilbertCoefficients», 2) = polynomial_algebra_var(field_ring(M), 2)",
			Simp(Fwd(polynomial_algebra.PolynomialAlgebraVarDef)),
			Refl())
		prime := a.Have(
			"the ideal X₂ generates over M is prime, the polynomials over the field M being a domain",
			"prime_ideal(polynomial_algebra_ring(field_ring(M), {i:num | i ≤ 2}), "+
				"    ideal_span(polynomial_algebra_ring(field_ring(M), {i:num | i ≤ 2}), «lineEquation»))",
			sameVariable.Rw(),
			By(
				integral_domain.FieldIntegralDomain.Read(M),
				polynomial_algebra_evaluation.VariableIdealPrime.At(fieldRing, indices, two),
				nat_order.LessEqRefl.At(two)))

		// A point over M.
		coordinatesIn := a.Have(
			"the coordinates of (1 : 0 : 0) lie in M",
			"∀i:num. i ≤ 2 ⇒ COND(i = 0, M.one, M.zero) ∈ M.carrier",
			By(comm_ring.OneIn.Read(ringM), comm_ring.ZeroIn.Read(ringM)))
		pastTwo := a.Have(
			"and vanish past 2",
			"∀i:num. 2 < i ⇒ COND(i = 0, M.one, M.zero) = M.zero",
			ByArith())
		leading := a.Have(
			"the first, the leading coordinate, is one",
			"∃j:num. "+
				"    j ≤ 2 ∧ "+
				"    COND(j = 0, M.one, M.zero) = M.one ∧ "+
				"    (∀i:num. i < j ⇒ COND(i = 0, M.one, M.zero) = M.zero)",
			Witness(zero),
			ByArith())
		vanishes := a.Have(
			"X₂ vanishes there: its value is the coordinate at 2, zero since 2 ≠ 0",
			Statement{
				Binders:    "∀P:((num → num) → A).",
				Hypotheses: []string{"P ∈ «lineEquation»"},
				Conclusion: "«valueAt»(λi:num. COND(i = 0, M.one, M.zero), P) = M.zero",
			},
			ByArith(
				inclusion,
				coordinatesIn.At(two),
				polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(K, fieldRing, identity, origin, two),
				set_basic.InSing.Inst[polynomial]()))
		point := a.Have(
			"so (1 : 0 : 0) is a point of the line over M",
			"(λi:num. COND(i = 0, M.one, M.zero)) ∈ "+
				"projective_equation_points(field_ring(M), k, M.carrier, 2, «lineEquation»)",
			Unfold(ProjectiveEquationPointsDef),
			By(coordinatesIn, pastTwo, leading, vanishes))

		// The Hilbert function and the genus.
		nonzero := a.Have(
			"X₂ is not the zero polynomial: its coefficient at the monomial of 2 is one",
			"polynomial_algebra_var(«hilbertCoefficients», 2) ≠ fun_zero(M.zero)",
			By(
				oneNotZero,
				polynomial_algebra.PolynomialAlgebraVarDef,
				free_module.DeltaAtDef,
				function_module.FunZeroDef))
		hilbert := a.Have(
			"from degree one on, the line, a plane curve of degree one, has Hilbert function d + 1",
			"∀d:num. 1 ≤ d ⇒ projective_hilbert_function(field_ring(M), k, 2, «lineEquation», d) = d + 1",
			a.ForEach(func(d *Expr[Nat]) Action {
				return ByArith(subK, form, nonzero, PlaneCurveHilbertFunction.Read(M).At(k, one, d, variable))
			}))
		eventuallyLinear := a.Have(
			"so the Hilbert function is eventually d + 1 − 0, of positive slope one",
			"∃g e N:num. "+
				"    0 < e ∧ "+
				"    (∀d:num. "+
				"        N ≤ d ⇒ "+
				"        projective_hilbert_function(field_ring(M), k, 2, «lineEquation», d) + g = e * d + 1)",
			Witness(zero),
			Witness(one),
			Witness(one),
			ByArith(hilbert))
		alongMultiples := a.Have(
			"and along the multiples of 1 it is j + 1 − 0",
			"∃c N:num. ∀j:num. "+
				"    N ≤ j ⇒ "+
				"    projective_hilbert_function(field_ring(M), k, 2, «lineEquation», 1 * j) + 0 = c * j + 1",
			Witness(one),
			Witness(one),
			ByArith(hilbert))

		// The Jacobian: the gradient of X₂ spans a line in the coordinate vectors.
		gradient := a.Have(
			"at every point the gradient of X₂ is the coordinate vector "+
				"of 2, the partial of X₂ in X_i being the constant δᵢ₂",
			"∀y:(num → A). "+
				"    (λi:num. "+
				"        COND(i ≤ 2, "+
				"            «valueAt»(y, "+
				"                polynomial_algebra_partial(«hilbertCoefficients», "+
				"                    i, "+
				"                    polynomial_algebra_var(«hilbertCoefficients», 2))), "+
				"            M.zero)) = "+
				"    delta_at(2)",
			Derive(func(b *Argument) {
				y := b.FixAs[vector]("y")
				b.Do(Funext())
				i := b.FixAs[Nat]("i")
				b.Show(
					"δᵢ₂ evaluates to itself, and vanishes past 2",
					By(
						scalars,
						subK,
						inclusion,
						partial_derivative.PolynomialPartialVar.At(K, i, two),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
							K, fieldRing, identity, y, b.TermAs[A]("COND(i = 2, M.one, M.zero)")),
						free_module.DeltaAtDef,
						field.SubfieldOne,
						field.SubfieldZero,
						nat_order.LessEqRefl.At(two)))
			}))
		gradients := a.Have(
			"so at every point the gradients of the equations are the coordinate vector of 2 alone",
			"∀y:(num → A). "+
				"    {λi:num. "+
				"        COND(i ≤ 2, "+
				"            «valueAt»(y, polynomial_algebra_partial(«hilbertCoefficients», i, P)), "+
				"            M.zero) | "+
				"    P:((num → num) → A) | "+
				"    P ∈ «lineEquation»} = "+
				"    {delta_at(2)}",
			BySets(gradient))
		coordinateSpace := free_module.FreeModuleOn.Read(ringM).At(indices)
		deltaIn := a.Have(
			"the coordinate vector of 2 lies among the vectors on the indices up to 2",
			"delta_at(2) ∈ finite_supp(M.zero, M.carrier, {i:num | i ≤ 2})",
			By(free_module.DeltaAtIn.Read(ringM).At(indices, two), nat_order.LessEqRefl.At(two)))
		deltaNonzero := a.Have(
			"and not zero, its entry at 2 being one",
			"delta_at(2) ≠ fun_zero(M.zero)",
			By(oneNotZero, free_module.DeltaAtDef, function_module.FunZeroDef))
		independent := a.Have(
			"so it is independent, lying outside the span {0} of ∅",
			"module_independent(field_ring(M), «coordinates», {delta_at(2)})",
			BySets(
				deltaNonzero,
				coordinateSpace,
				deltaIn,
				field.FieldRingSubfield.Read(M),
				submodule.SpanEmpty.At(fieldRing, coordinates),
				linear_independence.IndependentInsertIff.At(
					fieldRing, coordinates, inv, a.TermAs[Set[vector]]("∅"), delta),
				linear_independence.IndependentEmpty.At(fieldRing, coordinates)))
		lineSubspace := a.Have(
			"its span is a subspace",
			"submodule(field_ring(M), «coordinates», «gradientLine»)",
			By(
				coordinateSpace,
				deltaIn,
				submodule.SpanSubmodule.At(fieldRing, coordinates, a.TermAs[Set[vector]]("{delta_at(2)}")),
				set_order.SingSubset))
		lineDimension := a.Have(
			"a line, with the coordinate vector of 2 as basis",
			"module_dim(field_ring(M), restrict_module(«coordinates», «gradientLine»)) = 1",
			By(
				coordinateSpace,
				independent,
				lineSubspace,
				field.FieldRingSubfield.Read(M),
				submodule.SubmoduleModuleOn,
				linear_independence.BasisRestrict.At(
					fieldRing,
					coordinates,
					a.TermAs[Set[vector]]("«gradientLine»"),
					a.TermAs[Set[vector]]("{delta_at(2)}")),
				module_dimension.FiniteBasisDim.At(
					fieldRing,
					a.TermAs[module_record.ModuleOps[A, vector]]("restrict_module(«coordinates», «gradientLine»)"),
					inv,
					a.TermAs[Set[vector]]("{delta_at(2)}")),
				finite_set.FiniteSing.At(delta),
				cardinality.CardSing.At(delta)))

		a.Show(
			"the line is a smooth projective equation curve, of genus zero",
			SplitConj(
				Case(
					"it is a smooth projective equation curve",
					Simp(Fwd(SmoothProjectiveEquationCurveDef)),
					SplitConjAll(
						Case(
							"k is a subfield of M",
							By(subK)),
						Case(
							"k is finite",
							By(finiteK)),
						Case(
							"the plane has positive dimension",
							ByArith()),
						Case(
							"the equations, X₂ alone, are finitely many",
							By(finite_set.FiniteSing.At(variable))),
						Case(
							"X₂ is a form",
							By(form, set_basic.InSing.Inst[polynomial]())),
						Case(
							"its ideal over M is prime",
							By(prime)),
						Case(
							"the line has a point over M",
							By(point)),
						Case(
							"its Hilbert function is eventually linear",
							By(eventuallyLinear)),
						Case(
							"at every point the gradients span a line, of dimension 2 − 1",
							Derive(func(b *Argument) {
								x := b.FixAs[vector]("x")
								b.Assume()
								b.Do(gradients.At(x).Rw())
								b.Show(
									"the line has dimension one",
									ByArith(lineDimension))
							})))),
				Case(
					"its genus is zero, read along the multiples of 1",
					By(
						eventuallyLinear,
						alongMultiples,
						GenusAlongMultiples.At(fieldRing, k, two, equations, one, zero)))))
	}),
})}
