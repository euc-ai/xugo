// polynomials.go — the polynomial X^Q − X and the irreducible polynomials
// over a finite field: where Q annihilates one, X^Q − X has derivative minus
// one and is separable; its value at a point is the point's Q-th power less
// the point, so for Q above one that power fixes at most Q points; and an
// irreducible polynomial over a finite field divides it, the quotient by that
// polynomial being a finite field, and so is separable.

package finite_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_quotient"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// XPowerMinusXCoefficient — each coefficient of X^Q − X is the coefficient of
// X^Q less that of X: the two basis vectors are read at the index.
var XPowerMinusXCoefficient = xPowerMinusXCoefficientThm{family.Add(registry.ProofEntry{
	Name: "XPowerMinusXCoefficient",
	Key:  "prop_5ac9ed651f88b69f",
	Build: family.Theorem(
		"∀F:field_ops(A). ∀Q i:num. "+
			"    «xPowerMinusX»(F, Q, i) = F.sub(COND(i = Q, F.one, F.zero), COND(i = 1, F.one, F.zero))",
		func(a *Argument, F *Expr[FieldOps[A]], Q, i *Expr[Nat]) {
			zero := a.TermAs[A]("F.zero")
			one := a.TermAs[A]("F.one")
			sub := a.TermAs[Op[A]]("F.sub")
			exponentOne := a.TermAs[Nat]("1")
			basisQ := a.TermAs[Fun[Nat, A]]("basis_vector(Q)")
			basis1 := a.TermAs[Fun[Nat, A]]("basis_vector(1)")
			a.Show(
				"each coefficient is that of X^Q minus that of X",
				By(
					vec_space.VecSubDef.Inst[A]().At(sub, basisQ, basis1),
					vec_space.BasisVectorDef.Inst[A]().At(zero, one, Q),
					vec_space.BasisVectorDef.Inst[A]().At(zero, one, exponentOne)))
		}),
})}

// XPowerMinusXOver — X^Q − X is a polynomial over a commutative ring: a
// difference of two basis vectors.
var XPowerMinusXOver = xPowerMinusXOverThm{family.Add(registry.ProofEntry{
	Name: "XPowerMinusXOver",
	Key:  "prop_65a8dda170d9ee7c",
	Build: family.Theorem(
		"∀R:comm_ring_on(A). ∀Q:num. polynomial_over(R.carrier, basis_vector(Q) - basis_vector(1))",
		func(a *Argument, R comm_ring.CommRingFact[on.R], Q *Expr[Nat]) {
			polynomials := polynomial.PolynomialRingOn.Read(R)
			exponentOne := a.TermAs[Nat]("1")
			basisQ := a.TermAs[Fun[Nat, A]]("basis_vector(Q)")
			basis1 := a.TermAs[Fun[Nat, A]]("basis_vector(1)")
			a.Show(
				"a difference of two basis vectors is a polynomial over R",
				By(
					polynomial.BasisVectorOver.Read(R).At(Q),
					polynomial.BasisVectorOver.Read(R).At(exponentOne),
					comm_ring.SubIn.Read(polynomials).AsFact().At(basisQ, basis1)))
		}),
})}

// XPowerMinusXDerivative — where Q annihilates one, the derivative of X^Q − X
// is the constant minus one: the factor Q·1 kills the coefficient at Q − 1,
// and only −X is left.
var XPowerMinusXDerivative = xPowerMinusXDerivativeThm{family.Add(registry.ProofEntry{
	Name: "XPowerMinusXDerivative",
	Key:  "prop_c7e0948cbfbfc44b",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀Q:num.",
		Hypotheses: []string{
			"«numeral»(F, Q) = F.zero",
		},
		Conclusion: "polynomial_derivative(«xPowerMinusX»(F, Q)) = vec_neg(basis_vector(0))",
	}, func(a *Argument, F field.FieldFact[on.F], Q *Expr[Nat], vanishing Fact) {
		fieldF := a.TermAs[FieldOps[A]]("F")
		one := a.TermAs[A]("F.one")
		ring := field.RingOn.Read(F)
		additive := comm_ring.AddMonoidOn.Read(ring)
		notOne := a.Have(
			"Q is not one, since one is not zero",
			"Q ≠ 1",
			By(
				vanishing,
				comm_ring.OneIn.Read(ring),
				comm_monoid.PowOneOn.Read(additive).AsFact().At(one),
				field.OneNotZeroOn.At(fieldF)))
		a.Do(Funext())
		a.FixAs[Nat]("t")
		a.Do(Simp(
			Fwd(polynomial.PolynomialDerivativeDef),
			Fwd(XPowerMinusXCoefficient),
			Fwd(vec_space.VecNegDef),
			Fwd(vec_space.BasisVectorDef)))
		a.Cases(a.TermAs[Bool]("t = 0"))
		a.When(
			"at position zero the derivative's coefficient is minus one",
			func(b *Argument, isZero Fact) {
				notTop := b.Have(
					"the position one is not Q",
					"suc(t) ≠ Q",
					ByArith(isZero, notOne))
				b.Show(
					"only −X contributes, with coefficient minus one",
					Simp(
						Fwd(notTop),
						Fwd(isZero),
						Fwd(comm_ring.OneIn.Read(ring)),
						Fwd(comm_monoid.PowOneOn.Read(additive))),
					Simp(Fwd(comm_monoid.MonoidPowDef)),
					ByArith(Normalized, F))
			})
		a.Otherwise(
			"every coefficient of the derivative past zero vanishes",
			func(b *Argument, notZero Fact) {
				b.Cases(b.TermAs[Bool]("suc(t) = Q"))
				b.When(
					"at Q − 1 the coefficient carries the factor Q·1",
					func(c *Argument, isTop Fact) {
						c.Show(
							"the factor Q·1 vanishes",
							ByArith(Normalized, F, notZero, isTop, vanishing))
					})
				b.Otherwise(
					"elsewhere neither monomial contributes",
					func(c *Argument, notTop Fact) {
						c.Show(
							"the coefficient is a carrier element times zero",
							ByArith(
								Normalized,
								comm_ring.OneIn.Read(ring),
								notZero,
								notTop,
								comm_monoid.PowIn.Read(additive).AsFact().At(one, c.TermAs[Nat]("suc(t)"))))
					})
			})
	}),
})}

// XPowerMinusXSeparable — where Q annihilates one, X^Q − X is separable: its
// derivative is the constant minus one, so zero and minus one are the
// coefficients of a Bezout identity with it.
var XPowerMinusXSeparable = xPowerMinusXSeparableThm{family.Add(registry.ProofEntry{
	Name: "XPowerMinusXSeparable",
	Key:  "prop_66cc01abd04b2df9",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀Q:num.",
		Hypotheses: []string{
			"«numeral»(F, Q) = F.zero",
		},
		Conclusion: "polynomial_separable(field_ring(F), «xPowerMinusX»(F, Q))",
	}, func(a *Argument, F field.FieldFact[on.F], Q *Expr[Nat], vanishing Fact) {
		fieldF := a.TermAs[FieldOps[A]]("F")
		ring := field.RingOn.Read(F)
		polynomials := polynomial.PolynomialRingOn.Read(ring)
		H := a.TermAs[Fun[Nat, A]]("«xPowerMinusX»(F, Q)")
		basis0 := a.TermAs[Fun[Nat, A]]("basis_vector(0)")
		minusOne := a.Have(
			"the derivative is the constant minus one",
			"polynomial_derivative(«xPowerMinusX»(F, Q)) = vec_neg(basis_vector(0))",
			By(F, vanishing, XPowerMinusXDerivative.At(fieldF, Q)))
		a.Show(
			"zero and minus one give a Bezout identity with the derivative",
			Simp(Fwd(separable_polynomial.PolynomialSeparableDef)),
			Witness(a.TermAs[Fun[Nat, A]]("vec_zero")),
			Witness(a.TermAs[Fun[Nat, A]]("vec_neg(basis_vector(0))")),
			SplitConjAll(
				Case(
					"zero is a polynomial",
					By(polynomial.VecZeroOver.Read(ring))),
				Case(
					"minus one is a polynomial",
					By(comm_ring.OneIn.Read(polynomials), comm_ring.NegIn.Read(polynomials).AsFact().At(basis0))),
				Case(
					"zero times X^Q − X plus minus one times the derivative is one",
					Simp(Fwd(minusOne)),
					By(
						F,
						comm_ring.OneIn.Read(polynomials),
						XPowerMinusXOver.Read(ring).At(Q),
						comm_ring.MulLeftZeroOn.Read(polynomials).AsFact().At(H),
						comm_ring.MulNegNegOn.Read(polynomials).AsFact().At(basis0, basis0),
						comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(polynomials)).AsFact().At(basis0),
						comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(polynomials)).AsFact().At(basis0)))))
	}),
})}

// XPowerMinusXEval — the value of X^Q − X at a point is the point's Q-th
// power less the point: the value of a difference is the difference of the
// values, X^Q takes the point to its power and X to itself.
var XPowerMinusXEval = xPowerMinusXEvalThm{family.Add(registry.ProofEntry{
	Name: "XPowerMinusXEval",
	Key:  "prop_96312a41ad9b2b51",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀Q:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(basis_vector(Q) - basis_vector(1), x) = " +
			"monoid_pow(R.mul, R.one, x, Q) - x",
	}, func(a *Argument, R comm_ring.CommRingFact[on.R], Q *Expr[Nat], x *Expr[A], inR Fact) {
		exponentOne := a.TermAs[Nat]("1")
		basisQ := a.TermAs[Fun[Nat, A]]("basis_vector(Q)")
		basis1 := a.TermAs[Fun[Nat, A]]("basis_vector(1)")
		a.Show(
			"the value of the difference is the difference of the values",
			By(
				inR,
				polynomial.BasisVectorOver.Read(R).At(Q),
				polynomial.BasisVectorOver.Read(R).At(exponentOne),
				polynomial_evaluation.EvalSub.Read(R).AsFact().At(basisQ, basis1, x),
				polynomial_evaluation.EvalBasisVector.Read(R).AsFact().At(Q, x),
				polynomial_evaluation.EvalBasisVector.Read(R).AsFact().At(exponentOne, x),
				comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(R)).AsFact().At(x)))
	}),
})}

// XPowerMinusXDegree — above one, X^Q − X has degree Q with leading coefficient
// one: its coefficients vanish past Q and the coefficient at Q is one, so the
// degree is exactly Q.
var XPowerMinusXDegree = xPowerMinusXDegreeThm{family.Add(registry.ProofEntry{
	Name: "XPowerMinusXDegree",
	Key:  "prop_87fd56c7d2583805",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀Q:num.",
		Hypotheses: []string{
			"1 < Q",
		},
		Conclusion: "polynomial_degree(«xPowerMinusX»(M, Q)) = Q ∧ «xPowerMinusX»(M, Q, Q) = M.one",
	}, func(a *Argument, M field.FieldFact[on.M], Q *Expr[Nat], large Fact) {
		fieldM := a.TermAs[FieldOps[A]]("M")
		zero := a.TermAs[A]("M.zero")
		H := a.TermAs[Fun[Nat, A]]("«xPowerMinusX»(M, Q)")
		leading := a.Have(
			"the support ends at Q with coefficient one",
			"vec⟨suc(Q)⟩(«xPowerMinusX»(M, Q)) ∧ «xPowerMinusX»(M, Q, Q) = M.one",
			SplitConj(
				Case(
					"every coefficient past Q vanishes",
					Derive(func(b *Argument) {
						b.Do(Simp(Fwd(vec_space.VecDef)))
						b.FixAs[Nat]("i")
						beyond := b.Assume()
						offSupport := b.Have(
							"the index is neither Q nor one",
							"Q ≠ i ∧ i ≠ 1",
							ByArith(beyond, large))
						b.Show(
							"both monomial coefficients vanish there",
							Simp(Fwd(XPowerMinusXCoefficient), Fwd(offSupport)),
							ByArith(Normalized, M))
					})),
				Case(
					"the coefficient at Q is one",
					Derive(func(b *Argument) {
						distinct := b.Have(
							"the two support positions are distinct",
							"Q ≠ 1",
							ByArith(large))
						b.Show(
							"at Q only the coefficient of X^Q remains",
							Simp(Fwd(XPowerMinusXCoefficient), Fwd(distinct)),
							ByArith(Normalized, M))
					}))))
		a.Show(
			"the coefficients stop at Q with a nonzero one, so the degree is Q",
			By(
				M,
				leading,
				XPowerMinusXOver.Read(field.RingOn.Read(M)).At(Q),
				field.OneNotZeroOn.At(fieldM),
				polynomial.DegreeExact.At(zero, a.TermAs[Set[A]]("M.carrier"), H, Q)))
	}),
})}

// XPowerMinusXRoots — the points fixed by the q^m-th power are the roots of
// X^(q^m) − X: at a point of the carrier the value is the point's power less
// the point, zero exactly when the power fixes the point.
var XPowerMinusXRoots = xPowerMinusXRootsThm{family.Add(registry.ProofEntry{
	Name: "XPowerMinusXRoots",
	Key:  "prop_dc265af893439de3",
	Build: family.Theorem(
		"∀M:field_on(A). ∀q m:num. "+
			"    finite_constants(field_ring(M), q, m) = polynomial_roots(M.carrier, «xPowerMinusX»(M, q ^ m))",
		func(a *Argument, M field.FieldFact[on.M], q, m *Expr[Nat]) {
			Q := a.TermAs[Nat]("q ^ m")
			multiplicative := comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))
			pointwise := a.Have(
				"a carrier point is a root exactly when the Q-power fixes it",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ M.carrier"},
					Conclusion: "polynomial_eval(«xPowerMinusX»(M, q ^ m), x) = M.zero ⇔ " +
						"monoid_pow(M.mul, M.one, x, q ^ m) = x",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inM := b.Assume()
					b.Do(Simp(Fwd(XPowerMinusXEval.Read(field.RingOn.Read(M)))))
					b.Iff()
					b.Forward(
						"a vanishing difference gives a fixed point",
						func(c *Argument, differenceZero Fact) {
							c.Show(
								"x^Q − x = 0 gives x^Q = x",
								ByArith(M, differenceZero, inM, comm_monoid.PowIn.Read(multiplicative).AsFact().At(x, Q)))
						})
					b.Backward(
						"a fixed point gives a vanishing difference",
						func(c *Argument, fixed Fact) {
							c.Show(
								"x^Q = x gives x^Q − x = 0",
								ByArith(M, fixed, inM, comm_monoid.PowIn.Read(multiplicative).AsFact().At(x, Q)))
						})
				}))
			a.Do(Simp(
				Fwd(FiniteConstantsDef),
				Fwd(polynomial_roots.PolynomialRootsDef),
				Fwd(set_basic.Extension)))
			x := a.FixAs[A]("x")
			a.Show(
				"the two membership conditions agree",
				BySets(pointwise.At(x)))
		}),
})}

// FiniteConstantsBound — a power above the first fixes few points of a
// field: the points the q^m-th power fixes are the roots of X^(q^m) − X, a
// nonzero polynomial of degree q^m.
var FiniteConstantsBound = finiteConstantsBoundThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsBound",
	Key:  "prop_6e7bb45e2b371f90",
	Reading: "1 < q^m is load-bearing: at q^m = 1 the power is the first " +
		"and the set is all of M, and at q^m = 0 the zeroth power fixes the one " +
		"point one, which exceeds the stated bound. No finiteness of M is read.",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀q m:num.",
		Hypotheses: []string{"1 < q ^ m"},
		Conclusion: "finite(finite_constants(field_ring(M), q, m)) ∧ " +
			"card(finite_constants(field_ring(M), q, m)) ≤ q ^ m",
	}, func(a *Argument, M field.FieldFact[on.M], q, m *Expr[Nat], large Fact) {
		exponent := a.TermAs[Nat]("q ^ m")
		H := a.TermAs[Fun[Nat, A]]("«xPowerMinusX»(M, q ^ m)")
		degree := a.Have(
			"X^(q^m) − X has degree q^m, with leading coefficient one",
			"polynomial_degree(«xPowerMinusX»(M, q ^ m)) = q ^ m ∧ «xPowerMinusX»(M, q ^ m, q ^ m) = M.one",
			By(large, XPowerMinusXDegree.Read(M).At(exponent)))
		nonzero := a.Have(
			"so it is not zero, one not being zero",
			"«xPowerMinusX»(M, q ^ m) ≠ vec_zero",
			By(degree, field.OneNotZeroOn.Read(M), vec_space.VecZeroDef.At(a.TermAs[A]("M.zero"), exponent)))
		a.Show(
			"the fixed points are its roots, which number at most its degree",
			XPowerMinusXRoots.Read(M).At(q, m).Rw(),
			By(
				degree,
				nonzero,
				XPowerMinusXOver.Read(field.RingOn.Read(M)).At(exponent),
				polynomial_roots.RootBound.Read(integral_domain.FieldIntegralDomain.Read(M)).At(H)))
	}),
})}

// IrreducibleOverFiniteFieldSeparable — an irreducible polynomial over a finite
// field is separable with nonzero derivative: the quotient by it is a finite
// field of Q points, Q a positive power of the characteristic, and the class
// of X is fixed by the Q-th power, so the polynomial divides X^Q − X, which is
// separable.
var IrreducibleOverFiniteFieldSeparable = irreducibleOverFiniteFieldSeparableThm{family.Add(registry.ProofEntry{
	Name: "IrreducibleOverFiniteFieldSeparable",
	Key:  "prop_75826c844725a9eb",
	Reading: "Irreducibility includes positive degree and coefficients in k. " +
		"finite(k.carrier) is load-bearing: X^p − t over 𝔽_p(t) is irreducible and not separable.",
	Build: family.Sections(Statement{
		Binders: "∀k:field_on(A). ∀f:(num → A).",
		Hypotheses: []string{
			"finite(k.carrier)",
			"polynomial_irreducible(field_ring(k), f)",
		},
		Conclusion: "polynomial_derivative(f) ≠ vec_zero(k.zero) ∧ polynomial_separable(field_ring(k), f)",
		Abbrev: Abbrev{
			{Name: "polynomialRing", Text: "λF:field_ops(A). polynomial_ring(field_ring(F))"},
			{Name: "principalIdeal", Text: "λF:field_ops(A). λf:(num → A). " +
				"    ideal_span(«polynomialRing»(F), {f})"},
			{Name: "rootField", Text: "λF:field_ops(A). λf:(num → A). " +
				"    ideal_quotient_field(«polynomialRing»(F), «principalIdeal»(F, f))"},
			{Name: "embedding", Text: "λF:field_ops(A). λf:(num → A). λa:A. " +
				"    ideal_quotient_projection(«polynomialRing»(F), " +
				"        «principalIdeal»(F, f), " +
				"        vec_scalar_mul(F.mul, a, basis_vector(F.zero, F.one, 0)))"},
			{Name: "root", Text: "λF:field_ops(A). λf:(num → A). " +
				"    ideal_quotient_projection(«polynomialRing»(F), " +
				"        «principalIdeal»(F, f), " +
				"        basis_vector(F.zero, F.one, 1))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// mapXPowerMinusX carries X^Q − X along a ring homomorphism, coefficient
		// by coefficient.
		mapXPowerMinusX := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀G:field_on(B). ∀ι:(A → B). ∀Q:num.",
			Hypotheses: []string{
				"ring_homomorphism(field_ring(F), field_ring(G), ι)",
			},
			Conclusion: "(λn:num. ι(«xPowerMinusX»(F, Q, n))) = " +
				"vec_sub(basis_vector(G.zero, G.one, Q), basis_vector(G.zero, G.one, 1))",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			G field.FieldFact[on.G],
			ι *Arrow[A, B],
			Q *Expr[Nat],
			hom Fact,
		) {
			ring := field.RingOn.Read(F)
			a.Do(Funext())
			a.FixAs[Nat]("n")
			a.Do(Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.BasisVectorDef)))
			a.Show(
				"zero and one coefficients are preserved",
				By(
					F,
					G,
					hom,
					ring_homomorphism.MapSub.Read(hom).AsFact().At(
						a.TermAs[A]("COND(n = Q, F.one, F.zero)"), a.TermAs[A]("COND(n = 1, F.one, F.zero)")),
					ring_homomorphism.MapZero.Read(hom),
					ring_homomorphism.MapOne.Read(hom),
					comm_ring.OneIn.Read(ring),
					comm_ring.ZeroIn.Read(ring)))
		})
		// classDivides translates a zero residue class into a polynomial factor.
		classDivides := ctx.Lemma(Statement{
			Binders: "∀F:field_on(A). ∀f h:(num → A).",
			Hypotheses: []string{
				"ring_ideal(«polynomialRing»(F), «principalIdeal»(F, f))",
				"polynomial_over(F.carrier, f)",
				"polynomial_over(F.carrier, h)",
				"ideal_quotient_projection(«polynomialRing»(F), «principalIdeal»(F, f), h) = " +
					"«principalIdeal»(F, f)",
			},
			Conclusion: "polynomial_divides(field_ring(F), f, h)",
		}, func(
			a *Argument,
			F field.FieldFact[on.F],
			f, h *Arrow[Nat, A],
			isIdeal, overF, overH, zeroClass Fact,
		) {
			ring := field.RingOn.Read(F)
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			P := a.TermAs[RingOps[Fun[Nat, A]]]("«polynomialRing»(F)")
			I := a.TermAs[Set[Fun[Nat, A]]]("«principalIdeal»(F, f)")
			inIdeal := a.Have(
				"a polynomial with zero residue class lies in the ideal",
				"h ∈ «principalIdeal»(F, f)",
				By(
					isIdeal,
					overH,
					zeroClass,
					quotient_ring.CosetEqIdealIff.Read(polynomials).AsFact().At(I, h),
					quotient_ring.IdealQuotientProjectionDef.Inst[Fun[Nat, A]]().At(P, I, h)))
			a.Show(
				"membership in the principal ideal is divisibility",
				By(
					F,
					inIdeal,
					overF,
					overH,
					polynomial_quotient.PolynomialPrincipalIdealDivides.At(a.TermAs[FieldOps[A]]("F"), f, h)))
		})
		return ctx.Theorem(headline, func(a *Argument, k Fact, f *Arrow[Nat, A], finite, irreducible Fact) {
			fieldK := a.TermAs[FieldOps[A]]("k")
			ring := field.RingOn.Read(k)
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			I := a.TermAs[Set[Fun[Nat, A]]]("«principalIdeal»(k, f)")
			G, Gdef := a.LetAs[FieldOps[Set[Fun[Nat, A]]]]("G", "«rootField»(k, f)")
			ι, ιDef := a.LetAs[Fun[A, Set[Fun[Nat, A]]]]("ι", "«embedding»(k, f)")
			x, xDef := a.LetAs[Set[Fun[Nat, A]]]("x", "«root»(k, f)")
			Q, Qdef := a.LetAs[Nat]("Q", "card(G.carrier)")
			d := a.TermAs[Nat]("polynomial_degree(f)")
			H := a.TermAs[Fun[Nat, A]]("«xPowerMinusX»(k, Q)")
			rootData := a.Have(
				"the quotient by f is a field holding k and the class of X",
				"field_on(G) ∧ ring_homomorphism(field_ring(k), field_ring(G), ι) ∧ x ∈ G.carrier",
				Simp(Fwd(Gdef), Fwd(ιDef), Fwd(xDef)),
				By(k, irreducible, polynomial_quotient.QuotientAlgebraicExtension.At(fieldK, f)))
			parts := a.Conjuncts(
				rootData,
				"the quotient is a field",
				"the constants embed k in it",
				"the class of X lies in it")
			extensionField, embedding, rootInExtension := parts[0], parts[1], parts[2]
			quotientSize := a.Have(
				"the quotient is finite with card(k)^d points",
				"finite(G.carrier) ∧ Q = card(k.carrier) ^ polynomial_degree(f)",
				Simp(Fwd(Qdef), Fwd(Gdef)),
				By(
					k,
					finite,
					irreducible,
					QuotientByIrreducibleIsFiniteField.At(fieldK, f),
					FiniteFieldDef,
					cardinality.HasSizeDef))
			p, characteristic := a.ObtainAs[Nat](
				"a finite field has prime characteristic",
				"∃p:num. ring_prime_characteristic(field_ring(k), p)",
				By(k, finite, FiniteFieldCharacteristic.At(fieldK)))
			e, powerData := a.ObtainAs[Nat](
				"its size is a positive power of the characteristic",
				"∃e:num. 0 < e ∧ card(k.carrier) = p ^ e",
				By(k, finite, characteristic, FiniteFieldSizePower.At(fieldK, p)))
			characteristicPower := a.Have(
				"so Q is the power p^(e·d) of the characteristic",
				"Q = p ^ (e * polynomial_degree(f))",
				By(Normalized, quotientSize, powerData, nat_arith.PowPow.At(p, e, d)))
			polynomialF := a.Have(
				"f is a polynomial over k of positive degree",
				"polynomial_over(k.carrier, f) ∧ 0 < polynomial_degree(f)",
				By(
					irreducible,
					polynomial_division.PolynomialIrreducibleDef.At(a.TermAs[RingOps[A]]("field_ring(k)"), f)))
			positive := a.Have(
				"the exponent e·d is positive",
				"0 < e * polynomial_degree(f)",
				ByArith(powerData, polynomialF, nat_order.LessEqSelfMul.At(e, d)))
			exponentData := a.Have(
				"Q is a positive power of the characteristic, so it exceeds one and annihilates one",
				"1 < Q ∧ «numeral»(k, Q) = k.zero",
				By(
					Normalized,
					k,
					characteristic,
					characteristicPower,
					positive,
					PrimePowerVanishes.Read(ring).At(p, a.TermAs[Nat]("e * polynomial_degree(f)"))))
			rootFixed := a.Have(
				"the power of the finite field's size fixes the root",
				"monoid_pow(G.mul, G.one, x, Q) = x",
				By(
					Normalized,
					Qdef,
					extensionField,
					rootInExtension,
					quotientSize,
					FiniteFieldFixedByFrobenius.At(G, x)))
			mappedRootZero := a.Have(
				"the embedded X^Q − X vanishes at the root",
				"polynomial_eval(λn:num. ι(«xPowerMinusX»(k, Q, n)), x) = G.zero",
				Derive(func(b *Argument) {
					mappedPower := b.Have(
						"the embedding carries X^Q − X over k to X^Q − X over G",
						"(λn:num. ι(«xPowerMinusX»(k, Q, n))) = "+
							"vec_sub(basis_vector(G.zero, G.one, Q), basis_vector(G.zero, G.one, 1))",
						By(k, extensionField, embedding, At(mapXPowerMinusX, fieldK, G, ι, Q)))
					b.Show(
						"the value is the vanishing difference x^Q − x",
						Simp(Fwd(mappedPower)),
						ByArith(
							extensionField,
							rootInExtension,
							rootFixed,
							XPowerMinusXEval.Read(field.RingOn.Read(extensionField)).AsFact().At(Q, x)))
				}))
			isIdeal := a.Have(
				"the principal span is an ideal",
				"ring_ideal(«polynomialRing»(k), «principalIdeal»(k, f))",
				BySets(polynomialF, ring_ideal.SpanIdeal.Read(polynomials).At(a.TermAs[Set[Fun[Nat, A]]]("{f}"))))
			powerOver := XPowerMinusXOver.Read(ring).At(Q)
			projectedEvaluation := a.Have(
				"the residue class equals evaluation at the quotient root",
				"ideal_quotient_projection(«polynomialRing»(k), «principalIdeal»(k, f), «xPowerMinusX»(k, Q)) = "+
					"polynomial_eval(λn:num. ι(«xPowerMinusX»(k, Q, n)), x)",
				Simp(Fwd(Gdef), Fwd(ιDef), Fwd(xDef), Fwd(quotient_ring.IdealQuotientFieldDef.Inst[Fun[Nat, A]]())),
				By(
					k,
					isIdeal,
					powerOver,
					polynomial_quotient.QuotientClassIsEvaluation.Read(ring).AsFact().At(I, H)))
			zeroClass := a.Have(
				"X^Q − X has zero residue class",
				"ideal_quotient_projection(«polynomialRing»(k), «principalIdeal»(k, f), «xPowerMinusX»(k, Q)) = "+
					"«principalIdeal»(k, f)",
				Derive(func(b *Argument) {
					quotientZero := b.Have(
						"the quotient zero is the ideal itself",
						"G.zero = «principalIdeal»(k, f)",
						Simp(
							Fwd(Gdef),
							Fwd(quotient_ring.IdealQuotientFieldDef.Inst[Fun[Nat, A]]()),
							Fwd(field.FieldZeroDef.Inst[Set[Fun[Nat, A]]]())),
						Basic())
					b.Show(
						"its evaluated value is the quotient zero",
						By(quotientZero, projectedEvaluation, mappedRootZero))
				}))
			divides := a.Have(
				"the irreducible polynomial divides X^Q − X",
				"polynomial_divides(field_ring(k), f, «xPowerMinusX»(k, Q))",
				By(k, isIdeal, polynomialF, powerOver, zeroClass, At(classDivides, fieldK, f, H)))
			separable := a.Have(
				"a divisor of this separable polynomial is separable",
				"polynomial_separable(field_ring(k), f)",
				By(
					k,
					exponentData,
					polynomialF,
					divides,
					XPowerMinusXSeparable.At(fieldK, Q),
					separable_polynomial.SeparableDivisor.Read(ring).AsFact().At(f, H)))
			a.Show(
				"irreducibility and separability give the nonzero derivative",
				By(k, separable, irreducible, separable_polynomial.SeparableIffDerivative.At(fieldK, f)))
		})
	}),
})}

// QuotientByIrreducibleIsFiniteField — modulo an irreducible polynomial f, the
// polynomials over a finite field k are a finite field with card(k) to the
// degree of f points: the ideal of f is maximal, so the quotient is a field,
// and the remainders of division by f, the polynomials vanishing from the
// degree of f on, hold exactly one point of each class and are counted by
// their coefficients.
var QuotientByIrreducibleIsFiniteField = quotientByIrreducibleIsFiniteFieldThm{family.Add(registry.ProofEntry{
	Name: "QuotientByIrreducibleIsFiniteField",
	Key:  "prop_7960249837398fce",
	Reading: "The positive degree of an irreducible polynomial makes the quotient " +
		"proper. Its elements are cosets, not elements of the original coefficient type.",
	Build: family.Sections(Statement{
		Binders: "∀k:field_on(A). ∀f:(num → A).",
		Hypotheses: []string{
			"finite(k.carrier)",
			"polynomial_irreducible(field_ring(k), f)",
		},
		Conclusion: "finite_field(«quotientByF») ∧ " +
			"has_size(«quotientByF».carrier, card(k.carrier) ^ polynomial_degree(f))",
		Abbrev: Abbrev{
			{Name: "polynomialRingOverK", Text: "polynomial_ring(field_ring(k))"},
			{Name: "quotientByF", Text: "ideal_quotient_field(«polynomialRingOverK», " +
				"    ideal_span(«polynomialRingOverK», {f}))"},
			{Name: "idealOfF", Text: "ideal_span(«polynomialRingOverK», {f})"},
			{Name: "classOf", Text: "ideal_quotient_projection(«polynomialRingOverK», «idealOfF»)"},
			{Name: "polynomialsOverK", Text: "{p:(num → A) | polynomial_over(k.carrier, p)}"},
			{Name: "polynomialsBelow", Text: "λn:num. " +
				"    {r:(num → A) | polynomial_over(k.carrier, r) ∧ vec⟨n⟩(r)}"},
			{Name: "remainders", Text: "«polynomialsBelow»(polynomial_degree(f))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// polynomialsBelowSize counts the polynomials vanishing from n on: a
		// coefficient in k at each of the n positions below n, and zero after.
		polynomialsBelowSize := ctx.Lemma(Statement{
			Binders:    "∀k:field_on(A). ∀n:num.",
			Hypotheses: []string{"finite(k.carrier)"},
			Conclusion: "has_size(«polynomialsBelow»(n), card(k.carrier) ^ n)",
		}, func(a *Argument, k Fact, n *Expr[Nat], finite Fact) {
			carrier := a.TermAs[Set[A]]("k.carrier")
			coefficients := a.Have(
				"a polynomial vanishing from n on takes values in k below n and zero after",
				"∀h:(num → A). "+
					"    polynomial_over(k.carrier, h) ∧ vec⟨n⟩(h) ⇔ "+
					"    (∀x:num. x < n ⇒ h(x) ∈ k.carrier) ∧ (∀x:num. ¬(x < n) ⇒ h(x) = k.zero)",
				By(
					k,
					polynomial.PolynomialOverDef,
					vec_space.VecDef,
					comm_ring.ZeroIn.Read(field.RingOn.Read(k)),
					nat_order.NotLessThan))
			functionSpace := a.Have(
				"so these polynomials are the functions from the residues into k, zero off them",
				"«polynomialsBelow»(n) = "+
					"{h:(num → A) | "+
					"    (∀x:num. x ∈ «residues»(n) ⇒ h(x) ∈ k.carrier) ∧ (∀x:num. x ∉ «residues»(n) ⇒ h(x) = k.zero)}",
				BySets(coefficients))
			a.Show(
				"there are card(k) choices at each of the n residues",
				By(
					finite,
					functionSpace,
					num_segment.HasSizeBelowStrict.At(n),
					cardinality.FiniteHasSize.At(carrier),
					cardinality.HasSizeFunspace.At(
						a.TermAs[Set[Nat]]("«residues»(n)"),
						carrier,
						n,
						a.TermAs[Nat]("card(k.carrier)"),
						a.TermAs[A]("k.zero"))))
		})
		// remaindersTransversal reads polynomial_quotient.PolynomialQuotientRemainder
		// at the classes: every class is the class of a polynomial and so holds a
		// remainder, and two remainders in one class are its one short
		// representative.
		remaindersTransversal := ctx.Lemma(Statement{
			Binders:    "∀k:field_on(A). ∀f:(num → A).",
			Hypotheses: []string{"polynomial_irreducible(field_ring(k), f)"},
			Conclusion: "injective_on(«remainders», «classOf») ∧ " +
				"image(«classOf», «remainders») = «quotientByF».carrier",
		}, func(a *Argument, k Fact, f *Arrow[Nat, A], irreducible Fact) {
			fieldK := a.TermAs[FieldOps[A]]("k")
			coefficientRing := a.TermAs[RingOps[A]]("field_ring(k)")
			zero := a.TermAs[A]("k.zero")
			P := a.TermAs[RingOps[Fun[Nat, A]]]("«polynomialRingOverK»")
			I := a.TermAs[Set[Fun[Nat, A]]]("«idealOfF»")
			polynomials := polynomial.PolynomialRingOn.Read(field.RingOn.Read(k))
			irreducibleData := a.Conjuncts(
				a.Have(
					"an irreducible polynomial is a polynomial of positive degree",
					"polynomial_over(k.carrier, f) ∧ 0 < polynomial_degree(f)",
					By(irreducible, polynomial_division.PolynomialIrreducibleDef.At(coefficientRing, f))),
				"f is a polynomial over k",
				"f has positive degree")
			fOver, positive := irreducibleData[0], irreducibleData[1]
			fNonzero := a.Have(
				"a polynomial of positive degree is nonzero",
				"f ≠ vec_zero",
				By(positive, polynomial.DegreeVecZero.At(zero), nat_order.LessThanIrrefl))
			representative := a.Have(
				"modulo the nonzero f the class of a polynomial has one short representative",
				Statement{
					Binders:    "∀g:(num → A).",
					Hypotheses: []string{"polynomial_over(k.carrier, g)"},
					Conclusion: "∃u:(num → A). " +
						"    polynomial_over(k.carrier, u) ∧ " +
						"    vec⟨polynomial_degree(f)⟩(u) ∧ " +
						"    «classOf»(g) = «classOf»(u) ∧ " +
						"    (∀v:(num → A). " +
						"        polynomial_over(k.carrier, v) ∧ " +
						"        vec⟨polynomial_degree(f)⟩(v) ∧ " +
						"        «classOf»(g) = «classOf»(v) ⇒ " +
						"        v = u)",
				},
				Derive(func(b *Argument) {
					g := b.FixAs[Fun[Nat, A]]("g")
					gOver := b.Assume()
					b.Show(
						"f is a nonzero polynomial over the field k",
						By(k, fOver, fNonzero, gOver, polynomial_quotient.PolynomialQuotientRemainder.At(fieldK, f, g)))
				}))
			injective := a.Have(
				"two remainders in one class are its one short representative",
				"injective_on(«remainders», «classOf»)",
				Derive(func(b *Argument) {
					b.Do(Unfold(functions.InjectiveOnDef))
					x := b.FixAs[Fun[Nat, A]]("x")
					y := b.FixAs[Fun[Nat, A]]("y")
					given := b.Assume()
					remainders := b.Have(
						"x and y are polynomials vanishing from the degree of f on",
						"polynomial_over(k.carrier, x) ∧ "+
							"vec⟨polynomial_degree(f)⟩(x) ∧ "+
							"polynomial_over(k.carrier, y) ∧ "+
							"vec⟨polynomial_degree(f)⟩(y)",
						BySets(given))
					_, ofX := b.UnpackAs[Fun[Nat, A]](GroupPremises(remainders, representative.At(x)), "u")
					unique := b.Conjuncts(
						ofX,
						"u is a polynomial",
						"u vanishes from the degree of f on",
						"u lies in the class of x",
						"u is the only short polynomial in the class of x")[3]
					b.Show(
						"x and y are both the representative of the class of x",
						By(remainders, given, unique.At(x), unique.At(y)))
				}))
			isIdeal := a.Have(
				"the principal span is an ideal",
				"ring_ideal(«polynomialRingOverK», «idealOfF»)",
				BySets(fOver, ring_ideal.SpanIdeal.Read(polynomials).At(a.TermAs[Set[Fun[Nat, A]]]("{f}"))))
			covered := a.Have(
				"the classes of the polynomials are the points of the quotient",
				"image(«classOf», «polynomialsOverK») = «quotientByF».carrier",
				By(
					isIdeal,
					quotient_ring.IdealQuotientProjection.Read(polynomials).AsFact().At(I),
					quotient_ring.IdealQuotientFieldDef.At(P, I),
					quotient_ring.IdealQuotientRingDef.At(P, I)))
			everyClass := a.Have(
				"each class holds a remainder, so the classes of the remainders are all of them",
				"image(«classOf», «remainders») = «quotientByF».carrier",
				Derive(func(b *Argument) {
					b.Do(covered.RwRev(), Simp(Fwd(set_basic.Extension)))
					b.FixAs[Set[Fun[Nat, A]]]("c")
					b.Iff()
					b.Forward(
						"the class of a remainder is the class of a polynomial",
						func(c *Argument, ofRemainder Fact) {
							c.Show(
								"a remainder is a polynomial",
								BySets(ofRemainder))
						})
					b.Backward(
						"the class of a polynomial is the class of its representative",
						func(c *Argument, ofPolynomial Fact) {
							g, source := c.ObtainAs[Fun[Nat, A]](
								"c is the class of a polynomial g",
								"∃g:(num → A). polynomial_over(k.carrier, g) ∧ c = «classOf»(g)",
								BySets(ofPolynomial))
							_, ofG := c.UnpackAs[Fun[Nat, A]](GroupPremises(source, representative.At(g)), "u")
							parts := c.Conjuncts(
								ofG,
								"u is a polynomial",
								"u vanishes from the degree of f on",
								"u lies in the class of g",
								"u is the only short polynomial in the class of g")
							c.Show(
								"the representative of g lies in c",
								BySets(source, parts[0], parts[1], parts[2]))
						})
				}))
			a.Show(
				"the class map is one-to-one on the remainders and onto the quotient",
				By(injective, everyClass))
		})
		return ctx.Theorem(headline, func(a *Argument, k Fact, f *Arrow[Nat, A], finite, irreducible Fact) {
			fieldK := a.TermAs[FieldOps[A]]("k")
			polynomials := polynomial.PolynomialRingOn.Read(field.RingOn.Read(k))
			degree := a.TermAs[Nat]("polynomial_degree(f)")
			fieldOn := a.Have(
				"the ideal of an irreducible polynomial is maximal, so the quotient is a field",
				"field_on(«quotientByF»)",
				By(
					irreducible,
					polynomial_quotient.IrreduciblePrincipalMaximal.Read(k).At(f),
					quotient_ring.QuotientFieldOn.Read(polynomials).AsFact().At(
						a.TermAs[Set[Fun[Nat, A]]]("«idealOfF»"))))
			classes := a.Conjuncts(
				a.Have(
					"the remainders are a transversal of the classes",
					"injective_on(«remainders», «classOf») ∧ image(«classOf», «remainders») = «quotientByF».carrier",
					By(k, irreducible, At(remaindersTransversal, fieldK, f))),
				"the class map is one-to-one on the remainders",
				"the remainders meet every class")
			size := a.Have(
				"the quotient has as many points as there are remainders",
				"has_size(«quotientByF».carrier, card(k.carrier) ^ polynomial_degree(f))",
				classes[1].RwRev(),
				By(
					k,
					finite,
					classes[0],
					At(polynomialsBelowSize, fieldK, degree),
					cardinality.HasSizeImageInj.At(
						a.TermAs[Fun[Fun[Nat, A], Set[Fun[Nat, A]]]]("«classOf»"),
						a.TermAs[Set[Fun[Nat, A]]]("«remainders»"),
						a.TermAs[Nat]("card(k.carrier) ^ polynomial_degree(f)"))))
			a.Show(
				"a field with a finite carrier is a finite field",
				By(fieldOn, size, FiniteFieldDef, cardinality.HasSizeDef))
		})
	}),
})}

// FiniteConstantsRootPolynomial — X^(q^m) − X is a polynomial over every
// subfield, and its roots in M are the points the q^m-th power fixes.
var FiniteConstantsRootPolynomial = finiteConstantsRootPolynomialThm{family.Add(registry.ProofEntry{
	Name: "FiniteConstantsRootPolynomial",
	Key:  "prop_42543638fd546ab",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K:set(A). ∀q m:num.",
		Hypotheses: []string{
			"subfield(M, K)",
		},
		Conclusion: "polynomial_over(K, basis_vector(q ^ m) - basis_vector(1)) ∧ " +
			"(∀x:A. " +
			"    x ∈ M.carrier ⇒ " +
			"    (polynomial_eval(basis_vector(q ^ m) - basis_vector(1), x) = M.zero ⇔ " +
			"        x ∈ finite_constants(field_ring(M), q, m)))",
	},
		func(a *Argument, M field.FieldFact[on.M], K *Expr[Set[A]], q, m *Expr[Nat], subK Fact) {
			ring := field.RingOn.Read(M)
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			baseRing := a.Have(
				"K is a ring under the operations of M",
				"comm_ring_on(restrict_ring(field_ring(M), K))",
				By(subK, field.SubfieldCommRing.Read(M).At(K)))
			exponent := a.TermAs[Nat]("q ^ m")
			linear := a.TermAs[Nat]("1")
			power := a.TermAs[Fun[Nat, A]]("basis_vector(q ^ m)")
			variable := a.TermAs[Fun[Nat, A]]("basis_vector(1)")
			overK := a.Have(
				"a difference of two basis vectors is a polynomial over K",
				"polynomial_over(K, basis_vector(q ^ m) - basis_vector(1))",
				By(
					polynomial.BasisVectorOver.Read(baseRing).At(exponent),
					polynomial.BasisVectorOver.Read(baseRing).At(linear),
					comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(baseRing)).AsFact().At(power, variable)))
			roots := a.Have(
				"a point of M is a root exactly when its q^m-th power is itself",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ M.carrier",
					},
					Conclusion: "polynomial_eval(basis_vector(q ^ m) - basis_vector(1), x) = M.zero ⇔ " +
						"x ∈ finite_constants(field_ring(M), q, m)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inM := b.Assume()
					value := b.Have(
						"the value at x is x^(q^m) − x",
						"polynomial_eval(basis_vector(q ^ m) - basis_vector(1), x) = "+
							"M.sub(monoid_pow(M.mul, M.one, x, q ^ m), x)",
						By(
							inM,
							polynomial.BasisVectorOver.Read(ring).At(exponent),
							polynomial.BasisVectorOver.Read(ring).At(linear),
							polynomial_evaluation.EvalSub.Read(ring).AsFact().At(power, variable, x),
							polynomial_evaluation.EvalBasisVector.Read(ring).AsFact().At(exponent, x),
							polynomial_evaluation.EvalBasisVector.Read(ring).AsFact().At(linear, x),
							comm_monoid.PowOneOn.Read(multiplicative).AsFact().At(x)))
					membership := b.Have(
						"x is fixed exactly when it lies among the constants",
						"x ∈ finite_constants(field_ring(M), q, m) ⇔ monoid_pow(M.mul, M.one, x, q ^ m) = x",
						BySets(inM, FiniteConstantsDef.At(b.TermAs[RingOps[A]]("field_ring(M)"), q, m)))
					powerIn := comm_monoid.PowIn.Read(multiplicative).AsFact().At(x, exponent)
					b.Do(membership.Rw(), value.Rw())
					b.Iff()
					b.Forward(
						"a vanishing difference gives a fixed point",
						func(c *Argument, difference Fact) {
							c.Show(
								"x^(q^m) − x = 0 gives x^(q^m) = x",
								ByArith(M, difference, inM, powerIn))
						})
					b.Backward(
						"a fixed point gives a vanishing difference",
						func(c *Argument, fixed Fact) {
							c.Show(
								"x^(q^m) = x gives x^(q^m) − x = 0",
								ByArith(M, fixed, inM, powerIn))
						})
				}))
			a.Show(
				"the polynomial and its roots",
				By(overK, roots))
		}),
})}
