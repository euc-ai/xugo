package finite_spectrum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_polynomial"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexPolynomialReciprocalFactorization — a complex polynomial with nonzero
// constant term is that constant times a reciprocal product of nonzero
// reciprocal roots: the fundamental theorem gives a root, division removes it,
// and induction on the degree retains multiplicity.
var ComplexPolynomialReciprocalFactorization = complexPolynomialReciprocalFactorizationThm{family.Add(registry.ProofEntry{
	Name: "ComplexPolynomialReciprocalFactorization",
	Key:  "prop_faeeac41c52b716e",
	Build: family.Sections(Statement{
		Binders: "∀P:(num → complex).",
		Hypotheses: []string{
			"polynomial_over(𝕌, P)",
			"P(0) ≠ &0",
		},
		Conclusion: "∃a:(num → complex). " +
			"    (∀i:num. i < polynomial_degree(P) ⇒ a(i) ≠ &0) ∧ " +
			"    (∀n:num. P(n) = P(0) * reciprocal_product(polynomial_degree(P), a, n))",
		Abbrev: Abbrev{
			{Name: "monicLinear", Text: "λz:complex. " +
				"    basis_vector(1) - vec_scalar_mul(complex_mul, z, basis_vector(0))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		linearScale := ctx.Lemma(Statement{
			Binders:    "∀z:complex.",
			Hypotheses: []string{"z ≠ &0"},
			Conclusion: "«monicLinear»(z) = vec_scalar_mul(complex_mul, -z, «linearFactor»(complex_inv(z)))",
		}, func(arg *Argument, z *Expr[Complex], nonzero Fact) {
			arg.Do(Funext())
			arg.FixAs[Nat]("j")
			arg.Do(Simp(
				Fwd(vec_space.VecSubDef),
				Fwd(vec_space.VecScalarMulDef),
				Fwd(vec_space.BasisVectorDef)))
			arg.Cases(arg.TermAs[Bool]("j = 0"))
			arg.When(
				"the constant coefficients agree",
				func(b *Argument, zero Fact) {
					b.Show(
						"compute the constant term",
						ByArith(Normalized, zero, complex_field.CommRing))
				})
			arg.Otherwise(
				"compare the linear and higher coefficients",
				func(b *Argument, notZero Fact) {
					b.Cases(b.TermAs[Bool]("j = 1"))
					b.When(
						"the inverse law gives the linear coefficient",
						func(c *Argument, one Fact) {
							c.Show(
								"the root times its reciprocal is one",
								ByArith(
									Normalized,
									notZero,
									one,
									nonzero,
									complex_field.CommRing,
									field.MulRightInverse.Read(complex_field.Field).At(z)))
						})
					b.Otherwise(
						"higher coefficients vanish",
						func(c *Argument, notOne Fact) {
							c.Show(
								"both coefficients are zero",
								ByArith(Normalized, notZero, notOne, complex_field.CommRing))
						})
				})
		})
		byDegree := ctx.Lemma(Statement{
			Binders:    "∀d:num. ∀Q:(num → complex).",
			Hypotheses: []string{"polynomial_over(𝕌, Q)", "Q(0) ≠ &0", "polynomial_degree(Q) = d"},
			Conclusion: "∃a:(num → complex). " +
				"    (∀i:num. i < d ⇒ a(i) ≠ &0) ∧ (∀n:num. Q(n) = Q(0) * reciprocal_product(d, a, n))",
		}, func(arg *Argument, d *Expr[Nat]) {
			arg.Induct(d)
			arg.Base(
				"a degree-zero polynomial is its constant coefficient",
				func(base *Argument) {
					Q := base.FixAs[Fun[Nat, Complex]]("Q")
					current := base.Assume()
					ones := base.TermAs[Fun[Nat, Complex]]("λi:num. complex_of_real(&1)")
					base.Take(ones)
					constant := base.Have(
						"the polynomial is its constant multiple of the unit polynomial",
						"Q = vec_scalar_mul(complex_mul, Q(0), basis_vector(0))",
						By(
							current,
							polynomial.DegreeZeroConstant.Read(complex_field.CommRingOn).At(Q),
							complex_field.ComplexRingDef))
					base.Show(
						"the empty reciprocal product gives this constant polynomial",
						ByArith(
							Normalized,
							constant,
							ReciprocalProductClauses.At(base.TermAs[Nat]("0"), ones),
							At(
								vec_space.VecScalarMulDef.Inst[Complex](),
								base.TermAs[Op[Complex]]("complex_mul"),
								base.TermAs[Complex]("Q(0)"),
								base.TermAs[Fun[Nat, Complex]]("basis_vector(0)"))))
				})
			arg.Step(
				"a root divides out one degree",
				func(step *Argument, ih Fact) {
					Q := step.FixAs[Fun[Nat, Complex]]("Q")
					current := step.Assume()
					positive := step.Have(
						"the current polynomial has positive degree",
						"0 < polynomial_degree(Q)",
						ByArith(current))
					z, root := step.ObtainAs[Complex](
						"the fundamental theorem gives a root",
						"∃z:complex. polynomial_eval(Q, z) = &0",
						By(current, positive, complex_polynomial.PolynomialHasRoot.At(Q)))
					nonzero := step.Have(
						"the root and the polynomial are nonzero",
						"z ≠ &0 ∧ Q ≠ vec_zero(complex_of_real(&0))",
						By(
							Normalized,
							root,
							current,
							polynomial_evaluation.EvalAtZero.Read(complex_field.CommRingOn).At(Q),
							complex_field.ComplexRingDef,
							set_basic.InUniv.Inst[Complex](),
							vec_space.VecZeroDef.At(step.TermAs[Complex]("complex_of_real(&0)"), step.TermAs[Nat]("0"))))
					linear, linearDef := step.LetAs[Fun[Nat, Complex]]("linear", "«monicLinear»(z)")
					q, quotient := step.ObtainAs[Fun[Nat, Complex]](
						"divide out the root and lower the degree",
						"∃q:(num → complex). "+
							"    polynomial_over(𝕌, q) ∧ "+
							"    polynomial_degree(Q) = suc(polynomial_degree(q)) ∧ "+
							"    Q = polynomial_mul(linear, q)",
						By(
							root,
							nonzero,
							current,
							linearDef,
							polynomial_roots.RootFactorization.Read(complex_field.ComplexIntegralDomain).AsFact().At(Q, z),
							complex_field.ComplexRingDef,
							set_basic.InUniv.Inst[Complex]()))
					linearZero := step.Have(
						"the removed linear factor has constant coefficient minus the root",
						"linear(0) = -z",
						linearDef.Rw(),
						Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
						ByArith(complex_field.CommRing))
					constantTerm := step.Have(
						"the constant coefficients multiply",
						"Q(0) = -z * q(0)",
						By(
							linearZero,
							quotient,
							polynomial.PolynomialMulAtZero.Read(complex_field.CommRingOn).At(linear, q),
							complex_field.ComplexRingDef,
							set_basic.InUniv.Inst[Complex]()))
					quotientNonzero := step.Have(
						"a zero quotient constant would make the original constant zero",
						"q(0) ≠ &0",
						By(
							Normalized,
							constantTerm,
							current,
							comm_ring.MulRightZero.Read(complex_field.CommRing).At(step.TermAs[Complex]("-z"))))
					quotientDegree := step.Have(
						"the quotient degree is the predecessor of the current degree",
						"polynomial_degree(q) = d",
						ByArith(current, quotient))
					a, factored := step.ObtainAs[Fun[Nat, Complex]](
						"factor the quotient by induction",
						"∃a:(num → complex). "+
							"    (∀i:num. i < d ⇒ a(i) ≠ &0) ∧ (∀n:num. q(n) = q(0) * reciprocal_product(d, a, n))",
						By(ih.At(q), quotientDegree, quotientNonzero, quotient))
					_, reciprocalDef := step.LetAs[Complex]("r", "complex_inv(z)")
					A, appendDef := step.LetAs[Fun[Nat, Complex]]("A", "λi:num. COND(i < d, a(i), r)")
					product, productDef := step.LetAs[Fun[Nat, Complex]]("product", "reciprocal_product(d, a)")
					factor, factorDef := step.LetAs[Fun[Nat, Complex]]("factor", "«linearFactor»(r)")
					scale, quotientConstant := step.TermAs[Complex]("-z"), step.TermAs[Complex]("q(0)")
					linearScaled := step.Have(
						"the monic linear factor is minus the root times the reciprocal factor",
						"linear = vec_scalar_mul(complex_mul, -z, factor)",
						By(Normalized, linearDef, factorDef, reciprocalDef, nonzero, At(linearScale, z)))
					quotientScale := step.Have(
						"the quotient is its constant times the smaller reciprocal product",
						"q = vec_scalar_mul(complex_mul, q(0), product)",
						Funext(),
						Simp(Fwd(vec_space.VecScalarMulDef)),
						By(factored))
					pulled := step.Have(
						"pull the quotient constant out of multiplication",
						"Q = vec_scalar_mul(complex_mul, q(0), polynomial_mul(linear, product))",
						By(
							quotientScale,
							quotient,
							polynomial.PolynomialMulScalar.Read(complex_field.CommRingOn).AsFact().At(
								quotientConstant, linear, product),
							complex_field.ComplexRingDef,
							set_basic.InUniv.Inst[Complex]()))
					linearOut := step.Have(
						"pull out the scalar of the reciprocal linear factor",
						"polynomial_mul(linear, product) = "+
							"vec_scalar_mul(complex_mul, -z, polynomial_mul(factor, product))",
						By(
							linearScaled,
							polynomial.PolynomialMulComm.Read(complex_field.CommRingOn).At(linear, product),
							polynomial.PolynomialMulScalar.Read(complex_field.CommRingOn).AsFact().At(scale, product, factor),
							polynomial.PolynomialMulComm.Read(complex_field.CommRingOn).At(factor, product),
							complex_field.ComplexRingDef,
							set_basic.InUniv.Inst[Complex]()))
					full := step.TermAs[Fun[Nat, Complex]]("polynomial_mul(factor, product)")
					normalized := step.Have(
						"the original constant term is the total scalar",
						"Q = vec_scalar_mul(complex_mul, Q(0), polynomial_mul(factor, product))",
						By(
							pulled,
							linearOut,
							constantTerm,
							comm_monoid.Comm.Read(comm_ring.MulMonoid.Read(complex_field.CommRing)).At(scale, quotientConstant),
							vec_space.SmulMul.Read(complex_field.CommRing).At(quotientConstant, scale, full)))
					prefix := step.Have(
						"the appended sequence preserves the prefix and adds the reciprocal root",
						"(∀i:num. i < d ⇒ A(i) = a(i)) ∧ A(d) = r",
						appendDef.Rw(),
						ByArith(Normalized))
					prefixProduct := step.Have(
						"the preserved prefix has the smaller reciprocal product",
						"reciprocal_product(d, A) = product",
						By(Normalized, productDef, prefix, ReciprocalProductCongruence.At(d, A, a)))
					fullProduct := step.Have(
						"the appended factor gives the full reciprocal product",
						"reciprocal_product(suc(d), A) = polynomial_mul(factor, product)",
						Simp(Fwd(ReciprocalProductClauses)),
						By(Normalized, factorDef, prefixProduct, prefix))
					reciprocalNonzero := step.Have(
						"the reciprocal root is nonzero",
						"r ≠ &0",
						By(Normalized, reciprocalDef, nonzero, field.InvEqZero.Read(complex_field.Field).At(z)))
					step.Take(A)
					step.Show(
						"the appended list has the required nonzero entries and coefficients",
						SplitConj(
							Case(
								"every entry is an old nonzero entry or the new reciprocal root",
								appendDef.Rw(),
								By(Normalized, reciprocalNonzero, factored)),
							Case(
								"read the normalized polynomial identity at each coefficient",
								By(
									normalized,
									fullProduct,
									At(
										vec_space.VecScalarMulDef.Inst[Complex](),
										step.TermAs[Op[Complex]]("complex_mul"),
										step.TermAs[Complex]("Q(0)"),
										full)))))
				})
		})
		return ctx.Theorem(headline, func(arg *Argument, P *Arrow[Nat, Complex], given Fact) {
			arg.Show(
				"specialize the degree induction to the given polynomial",
				By(At(byDegree, arg.TermAs[Nat]("polynomial_degree(P)"), P), given))
		})
	}),
})}

// ComplexPolynomialSplitting — every nonconstant complex polynomial has a
// root, and a nonzero constant term gives its reciprocal-root factorization.
var ComplexPolynomialSplitting = complexPolynomialSplittingThm{family.Add(registry.ProofEntry{
	Name: "ComplexPolynomialSplitting",
	Key:  "prop_cf174ea1940eac17",
	Build: family.Theorem(Statement{
		Binders: "∀P:(num → complex).",
		Hypotheses: []string{
			"polynomial_over(𝕌, P)",
			"0 < polynomial_degree(P)",
		},
		Conclusion: "(∃z:complex. polynomial_eval(P, z) = &0) ∧ " +
			"(P(0) ≠ &0 ⇒ " +
			"    ∃a:(num → complex). " +
			"        (∀i:num. i < polynomial_degree(P) ⇒ a(i) ≠ &0) ∧ " +
			"        (∀n:num. P(n) = P(0) * reciprocal_product(polynomial_degree(P), a, n)))",
	}, func(arg *Argument, P *Arrow[Nat, Complex], over Fact) {
		arg.Show(
			"combine root existence with reciprocal-root factorization",
			SplitConj(
				Case(
					"the nonconstant polynomial has a root",
					By(over, complex_polynomial.PolynomialHasRoot.At(P))),
				Case(
					"a nonzero constant term admits reciprocal factors",
					Derive(func(b *Argument) {
						nonzero := b.Assume()
						b.Show(
							"apply the factorization theorem",
							By(over, nonzero, ComplexPolynomialReciprocalFactorization.At(P)))
					}))))
	}),
})}
