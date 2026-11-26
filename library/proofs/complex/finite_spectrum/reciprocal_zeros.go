// reciprocal_zeros.go — a reciprocal product as a polynomial: the value of a linear
// factor at a point, that a product of them is a polynomial, zero only at the
// reciprocal of a reciprocal root, its top coefficient, and that each reciprocal
// root is a root of the reversed product.

package finite_spectrum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ReciprocalLinearValue — the reciprocal linear factor 1 − rT is a polynomial, and
// its value at z is 1 − rz: past T it has no coefficient, so evaluation reads two.
var ReciprocalLinearValue = reciprocalLinearValueThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalLinearValue",
	Key:  "prop_3ba3c4aa8a54a544",
	Build: family.Theorem(
		"∀r z:complex. "+
			"    polynomial_over(𝕌, «linearFactor»(r)) ∧ polynomial_eval(«linearFactor»(r), z) = &1 - r * z",
		func(arg *Argument, r, z *Expr[Complex]) {
			linear := arg.TermAs[Fun[Nat, Complex]]("«linearFactor»(r)")
			length := arg.Have(
				"the factor has no coefficient past T",
				"vec⟨suc(1)⟩(«linearFactor»(r))",
				Unfold(vec_space.VecDef),
				ByArith())
			over := arg.Have(
				"so it is a polynomial",
				"polynomial_over(𝕌, «linearFactor»(r))",
				Unfold(polynomial.PolynomialOverDef),
				By(length, set_basic.InUniv))
			arg.Show(
				"and its value is its constant term plus its linear term at z",
				ByArith(
					over,
					length,
					At(polynomial_evaluation.EvalVecTwo.Read(complex_field.CommRingOn), linear, z),
					set_basic.InUniv.At(z)))
		}),
})}

// ReciprocalProductOver — a reciprocal product is a polynomial: the unit is one,
// and a linear factor times a polynomial is another.
var ReciprocalProductOver = reciprocalProductOverThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalProductOver",
	Key:  "prop_6bcf381ef7b2169f",
	Build: family.Theorem(
		"∀s:num. ∀a:(num → complex). polynomial_over(𝕌, reciprocal_product(s, a))",
		func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex]) {
			arg.Induct(s)
			arg.Base(
				"the empty product is the unit polynomial",
				Simp(Fwd(ReciprocalProductClauses)),
				By(polynomial.BasisVectorOver.Read(complex_field.CommRingOn)))
			arg.Step(
				"the next product is a linear factor times the product below",
				func(step *Argument, ih Fact) {
					step.Do(Simp(Fwd(ReciprocalProductClauses)))
					step.Show(
						"polynomials multiply to a polynomial",
						By(
							ih,
							ReciprocalLinearValue,
							polynomial.PolynomialMulOver.Read(complex_field.CommRingOn),
							complex_field.ComplexRingDef))
				})
		}),
})}

// ReciprocalProductZero — a zero of a reciprocal product is the reciprocal of one
// of its reciprocal roots. The empty product is one, which does not vanish; the value of the
// next product is 1 − a(s)z times the value below, and ℂ has no zero divisors, so
// either a(s)z = 1 or the zero is one of the product below.
var ReciprocalProductZero = reciprocalProductZeroThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalProductZero",
	Key:  "prop_d0b7dd96234328bf",
	Build: family.Theorem(Statement{
		Binders:    "∀s:num. ∀a:(num → complex). ∀z:complex.",
		Hypotheses: []string{"polynomial_eval(reciprocal_product(s, a), z) = &0"},
		Conclusion: "∃i:num. i < s ∧ a(i) * z = &1",
	}, func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex], z *Expr[Complex]) {
		arg.Induct(s)
		arg.Base(
			"the empty product is the unit polynomial, whose value is one",
			func(base *Argument) {
				base.Do(Simp(Fwd(ReciprocalProductClauses)))
				zero := base.Assume()
				base.Show(
					"one is no zero of ℂ",
					ByArith(
						zero,
						At(polynomial_evaluation.EvalBasisVector.Read(complex_field.CommRingOn), base.TermAs[Nat]("0"), z),
						set_basic.InUniv.At(z),
						comm_monoid.MonoidPowDef,
						complex_field.OfRealInjective.At(base.TermAs[Real]("&1"), base.TermAs[Real]("&0"))))
			})
		arg.Step(
			"the next value is the factor's times the value below",
			func(step *Argument, ih Fact) {
				step.Do(Simp(Fwd(ReciprocalProductClauses)))
				zero := step.Assume()
				factor := step.TermAs[Fun[Nat, Complex]]("«linearFactor»(a(s))")
				product := step.TermAs[Fun[Nat, Complex]]("reciprocal_product(s, a)")
				value := step.TermAs[Complex]("polynomial_eval(reciprocal_product(s, a), z)")
				split := step.Have(
					"the value of a product is the product of the values",
					"(&1 - a(s) * z) * polynomial_eval(reciprocal_product(s, a), z) = &0",
					By(
						zero,
						At(polynomial_evaluation.EvalMul.Read(complex_field.CommRingOn), factor, product, z),
						ReciprocalLinearValue.At(step.TermAs[Complex]("a(s)"), z),
						ReciprocalProductOver.At(s, a),
						set_basic.InUniv.At(z)))
				step.Cases(step.TermAs[Bool]("&1 - a(s) * z = &0"))
				step.When(
					"the new factor vanishes at z: s is the index",
					func(hit *Argument, vanishes Fact) {
						hit.Take(s)
						hit.Show(
							"s lies below suc(s), and a(s)z is one",
							ByArith(vanishes))
					})
				step.Otherwise(
					"otherwise the value below vanishes, and the induction finds the index",
					func(miss *Argument, nonzero Fact) {
						below := miss.Have(
							"ℂ has no zero divisors",
							"polynomial_eval(reciprocal_product(s, a), z) = &0",
							By(
								split,
								nonzero,
								field.MulEqZero.Read(complex_field.Field).At(miss.TermAs[Complex]("&1 - a(s) * z"), value)))
						miss.Show(
							"an index below s lies below suc(s)",
							By(ih, below, nat_order.LessThanSucClause))
					})
			})
	}),
})}

// ReciprocalProductTop — a reciprocal product of s factors is a polynomial of degree
// at most s, its degree-s coefficient (−1)^s times the product of the reciprocal
// roots. Each factor 1 − a(s)T raises the degree by one: past suc(s) the coefficient
// combines two that lie past s, and at suc(s) it is −a(s) times the top coefficient
// below.
var ReciprocalProductTop = reciprocalProductTopThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalProductTop",
	Key:  "prop_6077123cd93a0e57",
	Build: family.Theorem(
		"∀s:num. ∀a:(num → complex). "+
			"    (∀n:num. s < n ⇒ reciprocal_product(s, a, n) = complex_of_real(&0)) ∧ "+
			"    reciprocal_product(s, a, s) = (-complex_of_real(&1)) ^ s * product({i:num | i < s}, a)",
		func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex]) {
			fold := arg.Have(
				"below a bound the product of the reciprocal roots is the module chapter's fold",
				"∀t:num. "+
					"    module_sum(complex_mul, complex_of_real(&1), {i:num | i < t}, a) = "+
					"    product({i:num | i < t}, a)",
				Derive(func(b *Argument) {
					t := b.FixAs[Nat]("t")
					b.Show(
						"a segment is finite",
						By(
							num_segment.FiniteBelowStrict.At(t),
							complex_field.ComplexProductModuleSum.At(a, b.TermAs[Set[Nat]]("{i:num | i < t}"))))
				}))
			arg.Do(Simp(Rev(fold)))
			arg.Induct(s)
			arg.Base(
				"the unit has no coefficient past zero, and at zero the empty product is one",
				Simp(
					Fwd(ReciprocalProductClauses),
					Fwd(vec_space.BasisVectorDef),
					Fwd(num_segment.BelowStrictClauses),
					Fwd(module.ModuleSumEmpty),
					Fwd(comm_monoid.MonoidPowDef)),
				ByArith())
			arg.Step(
				"the next factor raises the degree by one and multiplies the top coefficient by −a(s)",
				func(step *Argument, ih Fact) {
					parts := step.Conjuncts(
						ih,
						"the product below vanishes past s",
						"and has the claimed coefficient at s")
					vanishes, top := parts[0], parts[1]
					root := step.TermAs[Complex]("a(s)")
					below := step.TermAs[Fun[Nat, Complex]]("reciprocal_product(s, a)")
					segment := step.TermAs[Set[Nat]]("{i:num | i < s}")
					next := step.TermAs[Nat]("suc(s)")
					product := step.Have(
						"the product of the reciprocal roots gains the factor a(s)",
						"module_sum(complex_mul, &1, {i:num | i < suc(s)}, a) = "+
							"a(s) * module_sum(complex_mul, &1, {i:num | i < s}, a)",
						Simp(Fwd(num_segment.BelowStrictClauses)),
						By(
							set_basic.InUniv,
							num_segment.FiniteBelowStrict.At(s),
							nat_order.LessThanIrrefl.At(s),
							module.ModuleSumInsertMonoid.Read(comm_ring.MulMonoidOn.Read(complex_field.CommRingOn)).AsFact().At(
								segment, s, a)))
					step.Do(Simp(Fwd(ReciprocalProductClauses)))
					step.Do(SplitConj(
						Case(
							"past suc(s) both coefficients of the convolution lie past s",
							Derive(func(arg *Argument) {
								n := arg.FixAs[Nat]("n")
								past := arg.Assume()
								arg.Show(
									"the convolution with the factor is zero",
									ByArith(
										past,
										vanishes.At(n),
										vanishes.At(arg.TermAs[Nat]("n - 1")),
										ReciprocalLinearConvolution.At(root, below, n)))
							})),
						Case(
							"at suc(s) the top coefficient below is multiplied by −a(s)",
							Derive(func(arg *Argument) {
								coefficient := arg.Have(
									"the coefficient at suc(s) is −a(s) times the coefficient at s",
									"polynomial_mul(«linearFactor»(a(s)), reciprocal_product(s, a), suc(s)) = "+
										"-(a(s) * reciprocal_product(s, a, s))",
									ByArith(vanishes.At(next), ReciprocalLinearConvolution.At(root, below, next)))
								arg.Do(
									Simp(Fwd(comm_monoid.MonoidPowDef)),
									coefficient.Rw(),
									product.Rw(),
									top.Rw())
								arg.Show(
									"one more sign and one more reciprocal root",
									ByArith())
							})),
					))
				})
		}),
})}

// ReciprocalReverseRoot — reversing the coefficients of the reciprocal product of
// the a(i) gives a polynomial with each a(i) among its roots. The reversal of s + 1
// factors is the reversal of s factors times T − a(s): coefficient by coefficient it
// is the coefficient recursion of the product read backwards, with the top coefficient
// of the product below supplying the constant term. So its value at z is z − a(s)
// times the value below, which vanishes at z = a(s) and, by induction, at the earlier
// a(i).
var ReciprocalReverseRoot = reciprocalReverseRootThm{family.Add(registry.ProofEntry{
	Name: "ReciprocalReverseRoot",
	Key:  "prop_3a7a8661c50c74d5",
	Build: family.Sections(Statement{
		Binders:    "∀s i:num. ∀a:(num → complex).",
		Hypotheses: []string{"i < s"},
		Conclusion: "polynomial_eval(«reversed»(s, a), a(i)) = &0",
		Abbrev: Abbrev{
			{Name: "reversed", Text: "λs:num. λa:(num → complex). λn:num. " +
				"    COND(n ≤ s, reciprocal_product(s, a, s - n), complex_of_real(&0))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		over := ctx.Lemma(
			"∀s:num. ∀a:(num → complex). polynomial_over(𝕌, «reversed»(s, a))",
			func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex]) {
				length := arg.Have(
					"the reversal has no coefficient past s",
					"vec⟨suc(s)⟩(«reversed»(s, a))",
					Unfold(vec_space.VecDef),
					ByArith())
				arg.Show(
					"so it is a polynomial",
					Unfold(polynomial.PolynomialOverDef),
					By(length, set_basic.InUniv))
			})
		coefficient := ctx.Lemma(
			"∀s:num. ∀a:(num → complex). ∀n:num. "+
				"    «reversed»(suc(s), a, n) = "+
				"    polynomial_mul(«reversed»(s, a), basis_vector(1), n) - a(s) * «reversed»(s, a, n)",
			func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex], n *Expr[Nat]) {
				reversal := arg.TermAs[Fun[Nat, Complex]]("«reversed»(s, a)")
				shifted := arg.Have(
					"multiplication by T shifts the reversal once",
					"polynomial_mul(«reversed»(s, a), basis_vector(1), n) = COND(1 ≤ n, «reversed»(s, a, n - 1), &0)",
					By(
						set_basic.InUniv.Inst[Complex](),
						polynomial.PolynomialMulBasisVector.Read(complex_field.CommRingOn).At(
							reversal, arg.TermAs[Nat]("1"), n)))
				arg.Do(shifted.Rw())
				recursion := arg.Have(
					"the coefficients of the next product recur through a(s)",
					"∀m:num. "+
						"    reciprocal_product(suc(s), a, m) = "+
						"    reciprocal_product(s, a, m) + COND(1 ≤ m, -(a(s) * reciprocal_product(s, a, m - 1)), &0)",
					By(ReciprocalProductClauses, ReciprocalLinearConvolution))
				nonzero := arg.Unless(
					arg.TermAs[Bool]("n = 0"),
					"the constant term is −a(s) times the top coefficient below, the product below stopping at s",
					Given(func(arg *Argument, isZero Fact) {
						indices := arg.Have(
							"at n = 0 the reversal reads the two top coefficients",
							"suc(s) - n = suc(s) ∧ s - n = s",
							ByArith(isZero))
						arg.Do(ByArith(
							recursion.At(arg.TermAs[Nat]("suc(s)")),
							ReciprocalProductTop.At(s, a),
							isZero,
							indices))
					}))
				bounded := arg.Unless(
					arg.TermAs[Bool]("suc(s) < n"),
					"past suc(s) both reversals vanish",
					Given(func(arg *Argument, beyond Fact) {
						arg.Do(ByArith(beyond, nonzero))
					}))
				indices := arg.Have(
					"a positive index reflects through suc(s) as its predecessor does through s",
					"suc(s) - n - 1 = s - n ∧ s - (n - 1) = suc(s) - n",
					ByArith(nonzero))
				arg.Cases(arg.TermAs[Bool]("n ≤ s"))
				arg.When(
					"below the top the recursion is the difference of the two reversal coefficients",
					func(arg *Argument, within Fact) {
						arg.Do(ByArith(nonzero, recursion.At(arg.TermAs[Nat]("suc(s) - n")), within, indices))
					})
				arg.Otherwise(
					"at n = suc(s) both sides are the constant term of the product",
					func(arg *Argument, above Fact) {
						ends := arg.Have(
							"both reflections land on zero",
							"suc(s) - n = 0 ∧ s - (n - 1) = 0",
							ByArith(above, bounded))
						arg.Do(ByArith(above, nonzero, recursion.At(arg.TermAs[Nat]("0")), bounded, ends))
					})
			})
		value := ctx.Lemma(
			"∀s:num. ∀a:(num → complex). ∀z:complex. "+
				"    polynomial_eval(«reversed»(suc(s), a), z) = (z - a(s)) * polynomial_eval(«reversed»(s, a), z)",
			func(arg *Argument, s *Expr[Nat], a *Arrow[Nat, Complex], z *Expr[Complex]) {
				reversal := arg.TermAs[Fun[Nat, Complex]]("«reversed»(s, a)")
				variable := arg.TermAs[Fun[Nat, Complex]]("basis_vector(1)")
				shifted := arg.TermAs[Fun[Nat, Complex]]("polynomial_mul(«reversed»(s, a), basis_vector(1))")
				scaled := arg.TermAs[Fun[Nat, Complex]]("vec_scalar_mul(complex_mul, a(s), «reversed»(s, a))")
				root := arg.TermAs[Complex]("a(s)")
				degree := arg.TermAs[Nat]("1")
				factored := arg.Have(
					"the next reversal is the reversal times T, less a(s) times the reversal",
					"«reversed»(suc(s), a) = "+
						"polynomial_mul(«reversed»(s, a), basis_vector(1)) - "+
						"vec_scalar_mul(complex_mul, a(s), «reversed»(s, a))",
					Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef)),
					Funext(),
					By(coefficient))
				arg.Do(factored.Rw())
				arg.Show(
					"evaluation takes the difference to the difference of the values and lets T and the scalar out",
					ByArith(
						At(over, s, a),
						polynomial.BasisVectorOver.Read(complex_field.CommRingOn).At(degree),
						polynomial.PolynomialMulOver.Read(complex_field.CommRingOn).At(reversal, variable),
						set_basic.InUniv.At(z),
						set_basic.InUniv.At(root),
						At(
							module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(complex_field.CommRingOn)), root, reversal),
						At(polynomial_evaluation.EvalSub.Read(complex_field.CommRingOn), shifted, scaled, z),
						At(polynomial_evaluation.EvalMul.Read(complex_field.CommRingOn), reversal, variable, z),
						At(polynomial_evaluation.EvalScalar.Read(complex_field.CommRingOn), root, z, reversal),
						At(polynomial_evaluation.EvalBasisVector.Read(complex_field.CommRingOn), degree, z)))
			})
		return ctx.Theorem(headline, func(arg *Argument, s, i *Expr[Nat], a *Arrow[Nat, Complex]) {
			arg.Induct(s)
			arg.Base(
				"no index lies below zero",
				func(base *Argument) {
					below := base.Assume()
					base.Show(
						"the hypothesis is absurd",
						ByArith(below))
				})
			arg.Step(
				"the next value is a(i) − a(s) times the value below",
				func(step *Argument, ih Fact) {
					below := step.Assume()
					recursion := At(value, s, a, a.Apply(i))
					step.Cases(step.TermAs[Bool]("i = s"))
					step.When(
						"the new factor vanishes at a(s)",
						func(hit *Argument, last Fact) {
							hit.Show(
								"a(s) − a(s) is zero",
								ByArith(last, recursion))
						})
					step.Otherwise(
						"an earlier a(i) is a root of the reversal below",
						func(miss *Argument, earlier Fact) {
							miss.Show(
								"the induction hypothesis applies below s",
								ByArith(earlier, ih, below, recursion))
						})
				})
		})
	}),
})}
