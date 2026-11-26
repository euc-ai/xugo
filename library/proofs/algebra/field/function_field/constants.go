// constants.go — the field of constants of a regular function field.

package function_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/perfect_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ExactConstantFieldFinite — the algebraic constants form a finite exact constant
// field: independence survives adjoining the transcendental parameter, bounding
// the constant-field degree by the function-field degree.
var ExactConstantFieldFinite = exactConstantFieldFiniteThm{family.Add(registry.ProofEntry{
	Name: "ExactConstantFieldFinite",
	Key:  "prop_7febf9ea324cde53",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, L)",
			"finite(k)",
			"k ⊆ L",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"finite_extension(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "finite(«constants») ∧ " +
			"subfield(M, «constants») ∧ " +
			"regular_function_field(M, «constants», L) ∧ " +
			"(∃r:num. 0 < r ∧ card(«constants») = card(k) ^ r ∧ extension_degree(M, k, «constants») = r)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The constants are L cut with the subfield of elements algebraic over k, and algebraicity over them descends to k by transitivity.
			constantField := ctx.Lemma(Statement{
				Binders:    "∀M:field_on(A). ∀k L:set(A).",
				Hypotheses: []string{"subfield(M, k)", "subfield(M, L)", "k ⊆ L"},
				Conclusion: "subfield(M, «constants») ∧ " +
					"k ⊆ «constants» ∧ " +
					"«constants» ⊆ L ∧ " +
					"(∀x:A. x ∈ L ∧ algebraic_over(M, «constants», x) ⇒ x ∈ «constants»)",
			}, func(a *Argument, M field.FieldFact[on.M], k, L *Expr[Set[A]], subfieldK, subfieldL, kInL Fact) {
				m := a.TermAs[FieldOps[A]]("M")
				elements := algebraic_element.AlgebraicElementsDef.At(m, k)
				algebraic := a.Have(
					"the ambient algebraic elements form a subfield containing k",
					"subfield(M, algebraic_elements(M, k)) ∧ k ⊆ algebraic_elements(M, k)",
					By(subfieldK, algebraic_element.AlgebraicElementsSubfield.Read(M).At(k)))
				intersection := a.Have(
					"the constants of L are its intersection with the ambient algebraic elements",
					"«constants» = L ∩ algebraic_elements(M, k)",
					BySets(subfieldL, field.SubfieldSubset.At(m, L), elements))
				between := a.Have(
					"the intersection is a subfield containing k",
					"subfield(M, «constants») ∧ k ⊆ «constants»",
					SplitConj(
						Case(
							"intersect the two subfields",
							By(
								intersection,
								algebraic,
								subfieldL,
								field.SubfieldInter.At(m, L, a.TermAs[Set[A]]("algebraic_elements(M, k)")))),
						Case(
							"both fields contain k",
							BySets(algebraic, kInL, elements))))
				a.Show(
					"the constants form a relatively algebraically closed subfield",
					SplitConj(
						Case(
							"the constant subfield lies between k and L",
							BySets(between)),
						Case(
							"algebraicity over the constants descends to k",
							Derive(func(b *Argument) {
								x := b.FixAs[A]("x")
								algebraic := b.Assume()
								coefficients := b.Have(
									"the constants and x lie in the ambient field",
									"«constants» ⊆ M.carrier ∧ (∀y:A. y ∈ «constants» ⇒ algebraic_over(M, k, y)) ∧ x ∈ M.carrier",
									BySets(algebraic, subfieldL, field.SubfieldSubset.At(m, L)))
								b.Show(
									"transitivity puts x in the constant subfield",
									BySets(
										algebraic,
										subfieldK,
										coefficients,
										algebraic_element.AlgebraicOverTrans.Read(M).AsFact().At(k, b.TermAs[Set[A]]("«constants»"), x)))
							}))))
			})

			// Regroup Σ_u p_u(t)·u = 0 as Σ_i (Σ_u p_{u,i}·u)·t^i: transcendence of t over C kills each inner sum, then k-independence of E kills each p_{u,i}.
			polynomialRelation := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀k C E T:set(A). ∀t:A. ∀p:(A → num → A). ∀x:A.",
				Hypotheses: []string{
					"subfield(M, C)",
					"k ⊆ C",
					"E ⊆ C",
					"finite(T)",
					"T ⊆ E",
					"module_independent(restrict_ring(field_ring(M), k), regular_module(field_ring(M)), E)",
					"t ∈ M.carrier",
					"¬algebraic_over(M, C, t)",
					"∀u:A. u ∈ T ⇒ polynomial_over(M.zero, k, p(u))",
					"module_sum(M.add, M.zero, T, λu:A. polynomial_eval(M.add, M.zero, M.mul, M.one, p(u), t) * u) = " +
						"M.zero",
					"x ∈ T",
				}, Conclusion: "p(x) = vec_zero(M.zero)",
			}, func(
				a *Argument,
				M field.FieldFact[on.M],
				k, C, E, T *Expr[Set[A]],
				t *Expr[A],
				p *Arrow[A, Fun[Nat, A]],
				x *Expr[A],
				subC, kInC, eInC, finiteT, supportInE, independent, tInM, transcendentalOverC, overK, relation, xInT Fact,
			) {
				m := a.TermAs[FieldOps[A]]("M")
				_, rDef := a.LetAs[module_record.RingOps[A]]("R", "restrict_ring(field_ring(M), C)")
				_, pDef := a.LetAs[module_record.ModuleOps[A, Fun[Nat, A]]](
					"P",
					"mk_module(vec_add(M.add), "+
						"    vec_zero(M.zero), "+
						"    vec_neg(M.neg), "+
						"    vec_scalar_mul(M.mul), "+
						"    {q:num → A | polynomial_over(M.zero, C, q)})")
				_, qDef := a.LetAs[Fun[Nat, A]](
					"Q", "module_sum(vec_add(M.add), vec_zero(M.zero), T, λu:A. vec_scalar_mul(M.mul, u, p(u)))")
				scalarsC := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), C)")
				polynomialsC := a.TermAs[module_record.ModuleOps[A, Fun[Nat, A]]](
					"mk_module(vec_add(M.add), " +
						"    vec_zero(M.zero), " +
						"    vec_neg(M.neg), " +
						"    vec_scalar_mul(M.mul), " +
						"    {q:num → A | polynomial_over(M.zero, C, q)})")
				scaled := a.TermAs[Fun[A, Fun[Nat, A]]]("λu:A. vec_scalar_mul(M.mul, u, p(u))")
				fieldC := a.Have(
					"C carries its restricted field",
					"field_on(restrict_field(M, C))",
					By(subC, field.SubfieldFieldOn.Read(M).At(C)))
				ringC := a.Have(
					"C carries its restricted ring",
					"comm_ring_on(R)",
					By(Normalized, field.RingOn.Read(fieldC), rDef, field.RestrictFieldRing.At(m, C)))
				polynomials := a.Have(
					"the polynomials over C form a C-module",
					"module_on(R, P)",
					By(ringC, pDef, rDef, polynomial.PolynomialModuleOn.At(scalarsC)))
				coefficients := a.Have(
					"the support lies in C and its polynomial coefficients extend from k to C",
					"∀u:A. u ∈ T ⇒ u ∈ C ∧ polynomial_over(M.zero, C, p(u))",
					BySets(
						overK,
						eInC,
						supportInE,
						kInC,
						At(polynomial.PolynomialOverMono, a.TermAs[A]("M.zero"), k, C)))
				summands := a.Have(
					"each scaled coefficient polynomial is over C",
					"∀u:A. u ∈ T ⇒ polynomial_over(M.zero, C, vec_scalar_mul(M.mul, u, p(u)))",
					BySets(coefficients, pDef, rDef, polynomials, At(module.SmulIn, scalarsC, polynomialsC)))
				collected := a.Have(
					"the collected relation is a polynomial over C",
					"polynomial_over(M.zero, C, Q)",
					BySets(
						finiteT,
						summands,
						qDef,
						pDef,
						rDef,
						polynomials,
						module.ModuleSumIn.At(
							scalarsC, polynomialsC, T,
							scaled)))
				evaluation := a.Have(
					"evaluation at t is a ring homomorphism",
					"ring_homomorphism(polynomial_ring(field_ring(M)), "+
						"    field_ring(M), "+
						"    λq:(num → A). polynomial_eval(M.add, M.zero, M.mul, M.one, q, t))",
					By(tInM, polynomial_evaluation.EvalHomomorphism.Read(field.RingOn.Read(M)).AsFact().At(t)))
				ambientSummands := a.Have(
					"the scaled polynomials are also over M",
					"∀u:A. u ∈ T ⇒ polynomial_over(M.zero, M.carrier, vec_scalar_mul(M.mul, u, p(u)))",
					BySets(
						summands,
						subC,
						field.SubfieldSubset.At(m, C),
						At(polynomial.PolynomialOverMono, a.TermAs[A]("M.zero"), C, a.TermAs[Set[A]]("M.carrier"))))
				evaluated := a.Have(
					"evaluation maps the finite polynomial sum to the sum of its values",
					"polynomial_eval(M.add, M.zero, M.mul, M.one, Q, t) = "+
						"module_sum(M.add, "+
						"    M.zero, "+
						"    T, "+
						"    λu:A. polynomial_eval(M.add, M.zero, M.mul, M.one, vec_scalar_mul(M.mul, u, p(u)), t))",
					By(
						ring_homomorphism.MapZero.Read(evaluation),
						ring_homomorphism.MapAdd.Read(evaluation),
						finiteT,
						ambientSummands,
						qDef,
						module.ModuleSumMonoidHomomorphism.Read(
							module.AddMonoidOn.Read(polynomial.PolynomialModuleOn.Read(field.RingOn.Read(M)))).AsFact().At(
							a.TermAs[Op[A]]("M.add"), a.TermAs[A]("M.zero"), a.TermAs[Fun[Fun[Nat, A], A]](
								"λq:(num → A). polynomial_eval(M.add, M.zero, M.mul, M.one, q, t)"), T,
							scaled)))
				ambient := a.Have(
					"the support, polynomials, and their values lie in M",
					Statement{
						Binders:    "∀u:A.",
						Hypotheses: []string{"u ∈ T"},
						Conclusion: "u ∈ M.carrier ∧ " +
							"polynomial_over(M.zero, M.carrier, p(u)) ∧ " +
							"polynomial_eval(M.add, M.zero, M.mul, M.one, p(u), t) ∈ M.carrier",
					},
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						uInT := b.Assume()
						b.Show(
							"extend coefficients and evaluate in M",
							BySets(
								coefficients.At(u),
								tInM,
								subC,
								uInT,
								field.SubfieldSubset.At(m, C),
								polynomial.PolynomialOverMono.At(
									b.TermAs[A]("M.zero"), C, b.TermAs[Set[A]]("M.carrier"), p.Apply(u)),
								polynomial_evaluation.EvalIn.Read(field.RingOn.Read(M)).AsFact().At(p.Apply(u), t)))
					}))
				values := a.Have(
					"a scaled coefficient polynomial gives its original relation summand",
					Statement{
						Binders:    "∀u:A.",
						Hypotheses: []string{"u ∈ T"},
						Conclusion: "polynomial_eval(M.add, M.zero, M.mul, M.one, vec_scalar_mul(M.mul, u, p(u)), t) = " +
							"M.mul(polynomial_eval(M.add, M.zero, M.mul, M.one, p(u), t), u)",
					},
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						uInT := b.Assume()
						b.Show(
							"evaluate scalar multiplication and commute the product",
							ByArith(
								M,
								tInM,
								uInT,
								ambient.At(u),
								polynomial_evaluation.EvalScalar.Read(field.RingOn.Read(M)).AsFact().At(u, t, p.Apply(u))))
					}))
				vanishes := a.Have(
					"the collected polynomial vanishes at t",
					"polynomial_eval(M.add, M.zero, M.mul, M.one, Q, t) = M.zero",
					By(
						values,
						relation,
						evaluated,
						module.ModuleSumCongruence.At(a.TermAs[Op[A]]("M.add"), a.TermAs[A]("M.zero"), T,
							a.TermAs[Fun[A, A]](
								"λu:A. polynomial_eval(M.add, M.zero, M.mul, M.one, vec_scalar_mul(M.mul, u, p(u)), t)"),
							a.TermAs[Fun[A, A]]("λu:A. M.mul(polynomial_eval(M.add, M.zero, M.mul, M.one, p(u), t), u)"))))
				zero := a.Have(
					"transcendence makes the collected polynomial zero",
					"Q = vec_zero(M.zero)",
					By(transcendentalOverC, collected, vanishes, algebraic_element.AlgebraicOverDef.At(m, C, t)))
				coefficientSum := a.Have(
					"coefficient evaluation maps the collected finite sum coefficientwise",
					"∀i:num. Q(i) = module_sum(M.add, M.zero, T, λu:A. vec_scalar_mul(M.mul, u, p(u), i))",
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						b.Show(
							"take the coefficient of the finite sum",
							By(
								Normalized,
								finiteT,
								qDef,
								ambientSummands,
								vec_space.VecZeroDef.At(b.TermAs[A]("M.zero"), i),
								At(vec_space.VecAddDef, b.TermAs[Op[A]]("M.add")),
								module.ModuleSumMonoidHomomorphism.Read(
									module.AddMonoidOn.Read(polynomial.PolynomialModuleOn.Read(field.RingOn.Read(M)))).AsFact().At(
									b.TermAs[Op[A]](
										"M.add"), b.TermAs[A]("M.zero"), b.TermAs[Fun[Fun[Nat, A], A]]("λq:(num → A). q(i)"), T,
									scaled)))
					}))
				coefficientFields := a.Have(
					"each coefficient lies in k and in the ambient field",
					"∀u:A. ∀i:num. u ∈ T ⇒ u ∈ M.carrier ∧ p(u, i) ∈ k ∧ p(u, i) ∈ M.carrier",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						b.FixAs[Nat]("i")
						uInT := b.Assume()
						b.Show(
							"read the coefficient membership of both polynomial structures",
							By(
								uInT,
								ambient.At(u),
								overK.At(u),
								polynomial.PolynomialOverDef.At(b.TermAs[A]("M.zero"), k, p.Apply(u)),
								polynomial.PolynomialOverDef.At(b.TermAs[A]("M.zero"), b.TermAs[Set[A]]("M.carrier"), p.Apply(u))))
					}))
				commuted := a.Have(
					"the coefficient products have the orientation of a linear relation",
					"∀u:A. ∀i:num. u ∈ T ⇒ vec_scalar_mul(M.mul, u, p(u), i) = M.mul(p(u, i), u)",
					Derive(func(b *Argument) {
						u := b.FixAs[A]("u")
						i := b.FixAs[Nat]("i")
						uInT := b.Assume()
						b.Show(
							"commute the coefficient product",
							ByArith(
								M,
								uInT,
								coefficientFields.At(u, i),
								vec_space.VecScalarMulDef.At(b.TermAs[Op[A]]("M.mul"), u, p.Apply(u), i)))
					}))
				coefficientRelation := a.Have(
					"every coefficient is a vanishing k-linear relation",
					"∀i:num. module_sum(M.add, M.zero, T, λu:A. M.mul(p(u, i), u)) = M.zero",
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						b.Show(
							"read a zero coefficient of the collected polynomial",
							By(
								commuted,
								coefficientSum.At(i),
								zero,
								vec_space.VecZeroDef.At(b.TermAs[A]("M.zero"), i),
								module.ModuleSumCongruence.At(
									b.TermAs[Op[A]]("M.add"),
									b.TermAs[A]("M.zero"),
									T,
									b.TermAs[Fun[A, A]]("λu:A. vec_scalar_mul(M.mul, u, p(u), i)"),
									b.TermAs[Fun[A, A]]("λu:A. M.mul(p(u, i), u)"))))
					}))
				a.Do(Funext())
				i := a.FixAs[Nat]("i")
				a.Show(
					"independence over k kills the coefficient of p(x)",
					By(
						Normalized,
						finiteT,
						coefficientFields,
						coefficientRelation.At(i),
						xInT,
						supportInE,
						independent,
						vec_space.VecZeroDef.At(a.TermAs[A]("M.zero"), i),
						linear_independence.IndependentVanishingCombination.At(
							a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)"),
							a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))"),
							E,
							T,
							a.TermAs[Fun[A, A]]("λu:A. p(u, i)"),
							x)))
			})

			// A relation over k[t] takes a polynomial over k for each coefficient, and polynomialRelation makes every one of them zero.
			polynomialIndependence := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀k C E:set(A). ∀t:A.",
				Hypotheses: []string{
					"subfield(M, C)",
					"k ⊆ C",
					"E ⊆ C",
					"t ∈ M.carrier",
					"¬algebraic_over(M, C, t)",
					"module_independent(restrict_ring(field_ring(M), k), regular_module(field_ring(M)), E)",
				},
				Conclusion: "module_independent( " +
					"    restrict_ring(field_ring(M), polynomial_image(field_ring(M), k, t)), " +
					"    regular_module(field_ring(M)), " +
					"    E)",
			}, func(
				a *Argument,
				M field.FieldFact[on.M],
				k, C, E *Expr[Set[A]],
				t *Expr[A],
				subfieldC, kInC, eInC, tInM, transcendentalOverC, independent Fact,
			) {
				m := a.TermAs[FieldOps[A]]("M")
				a.Show(
					"independence over k extends to polynomial scalars",
					Simp(Fwd(linear_independence.ModuleIndependentDef)),
					SplitConj(
						Case(
							"the independent set lies in the ambient field",
							By(
								independent,
								linear_independence.IndependentInCarrier.At(
									a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)"),
									a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))"),
									E))),
						Case(
							"a finite polynomial relation has zero coefficients",
							Derive(func(b *Argument) {
								T := b.FixAs[Set[A]]("T")
								b.FixAs[Fun[A, A]]("c")
								relation := b.Assume()
								representatives := b.Have(
									"each coefficient has a polynomial representative on the support",
									"∀u:A. ∃q:(num → A). "+
										"    u ∈ T ⇒ "+
										"    polynomial_over(M.zero, k, q) ∧ polynomial_eval(M.add, M.zero, M.mul, M.one, q, t) = c(u)",
									BySets(
										relation,
										algebraic_element.PolynomialImageDef.At(b.TermAs[module_record.RingOps[A]]("field_ring(M)"), k, t)))
								p, represented := b.ObtainAs[Fun[A, Fun[Nat, A]]](
									"choose the coefficient polynomials together",
									"∃p:(A → num → A). ∀u:A. "+
										"    u ∈ T ⇒ "+
										"    polynomial_over(M.zero, k, p(u)) ∧ "+
										"    polynomial_eval(M.add, M.zero, M.mul, M.one, p(u), t) = c(u)",
									By(representatives),
									Named("p"))
								vanishes := b.Have(
									"the polynomial representatives satisfy the same vanishing relation",
									"module_sum(M.add, "+
										"    M.zero, "+
										"    T, "+
										"    λu:A. M.mul(polynomial_eval(M.add, M.zero, M.mul, M.one, p(u), t), u)) = "+
										"M.zero",
									By(
										Normalized,
										represented,
										relation,
										module.ModuleSumCongruence.At(
											b.TermAs[Op[A]]("M.add"),
											b.TermAs[A]("M.zero"),
											T,
											b.TermAs[Fun[A, A]]("λu:A. M.mul(polynomial_eval(M.add, M.zero, M.mul, M.one, p(u), t), u)"),
											b.TermAs[Fun[A, A]]("λu:A. M.mul(c(u), u)"))))
								zero := b.Have(
									"all coefficient polynomials are zero",
									"∀u:A. u ∈ T ⇒ p(u) = vec_zero(M.zero)",
									By(
										M,
										represented,
										vanishes,
										relation,
										subfieldC,
										kInC,
										eInC,
										tInM,
										transcendentalOverC,
										independent,
										At(polynomialRelation, m, k, C, E, T, t, p)))
								evaluation := b.Have(
									"evaluation at t is a ring homomorphism",
									"ring_homomorphism(polynomial_ring(field_ring(M)), "+
										"    field_ring(M), "+
										"    λq:(num → A). polynomial_eval(M.add, M.zero, M.mul, M.one, q, t))",
									By(tInM, polynomial_evaluation.EvalHomomorphism.Read(field.RingOn.Read(M)).AsFact().At(t)))
								u := b.FixAs[A]("u")
								uInT := b.Assume()
								b.Show(
									"the original coefficient is the value of a zero polynomial",
									By(Normalized, zero.At(u), represented.At(u), uInT, ring_homomorphism.MapZero.Read(evaluation)))
							}))))
			})

			// A basis of the constants over k stays independent over k[t], then over its fraction field B = k(t), so inside L it has at most [L : B] elements.
			degreeBound := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A.",
				Hypotheses: []string{
					"subfield(M, k)",
					"subfield(M, L)",
					"k ⊆ L",
					"t ∈ L",
					"¬algebraic_over(M, k, t)",
					"finite_extension(M, field_adjoin(M, k, {t}), L)",
				},
				Conclusion: "finite_extension(M, k, «constants») ∧ " +
					"extension_degree(M, k, «constants») ≤ extension_degree(M, field_adjoin(M, k, {t}), L)",
			}, func(
				a *Argument,
				M field.FieldFact[on.M],
				k, L *Expr[Set[A]],
				t *Expr[A],
				subfieldK, subfieldL, kInL, tInL, transcendental, finiteOverB Fact,
			) {
				m := a.TermAs[FieldOps[A]]("M")
				C, cDef := a.LetAs[Set[A]]("C", "«constants»")
				B, bDef := a.LetAs[Set[A]]("B", "field_adjoin(M, k, {t})")
				scalarsK := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)")
				inverse := a.TermAs[Fun[A, A]]("M.inv")
				ambientVectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
				constants := a.Have(
					"the constant subfield contains k and keeps t transcendental",
					"subfield(M, C) ∧ k ⊆ C ∧ C ⊆ L ∧ ¬algebraic_over(M, C, t)",
					Simp(Fwd(cDef)),
					BySets(M, subfieldK, subfieldL, kInL, tInL, transcendental, At(constantField, m, k, L)))
				rational := a.Have(
					"t lies in M and the rational field lies between k and L",
					"t ∈ M.carrier ∧ subfield(M, B) ∧ k ⊆ B ∧ B ⊆ L",
					Simp(Fwd(bDef)),
					BySets(
						M,
						subfieldK,
						subfieldL,
						kInL,
						tInL,
						field.SubfieldSubset.At(m, L),
						At(algebraic_element.AdjoinElementBetween, m, k, L, t)))
				constantSpace := a.Have(
					"C is a vector space over k",
					"module_on(restrict_ring(field_ring(M), k), restrict_module(regular_module(field_ring(M)), C))",
					By(constants, subfieldK, field_extension.ExtensionModuleOn.Read(M).At(k, C)))
				E, basisOfC := a.ObtainAs[Set[A]](
					"choose a basis E of the constants over k",
					"∃E:set(A). "+
						"    module_basis(restrict_ring(field_ring(M), k), "+
						"        restrict_module(regular_module(field_ring(M)), C), "+
						"        E)",
					By(
						subfieldK,
						field.SubfieldRingSubfield.Read(M).At(k, k),
						linear_independence.BasisExists.Read(constantSpace).At(inverse)),
					Named("E"))
				independent := a.Have(
					"the constant-field basis is independent in the ambient field",
					"E ⊆ C ∧ module_independent(restrict_ring(field_ring(M), k), regular_module(field_ring(M)), E)",
					By(
						constants,
						basisOfC,
						field.SubfieldSubset.At(m, C),
						linear_independence.ModuleBasisDef.At(
							scalarsK,
							a.TermAs[module_record.ModuleOps[A, A]]("restrict_module(regular_module(field_ring(M)), C)"),
							E),
						linear_independence.IndependentRestrict.At(scalarsK, ambientVectors, C, E)))
				polynomialScalars := a.Have(
					"the basis remains independent over k[t]",
					"module_independent(restrict_ring(field_ring(M), polynomial_image(field_ring(M), k, t)), "+
						"    regular_module(field_ring(M)), "+
						"    E)",
					By(M, rational, constants, independent, At(polynomialIndependence, m, k, C, E, t)))
				fractions := a.Have(
					"B is the fraction field of k[t]",
					"fraction_field_carrier(restrict_ring(field_ring(M), B), polynomial_image(field_ring(M), k, t))",
					Simp(Fwd(bDef)),
					By(rational, subfieldK, integral_element.RationalFunctionsFractionField.Read(M).AsFact().At(k, t)))
				rationalScalars := a.Have(
					"clearing denominators preserves independence over B",
					"module_independent(restrict_ring(field_ring(M), B), regular_module(field_ring(M)), E)",
					By(
						rational,
						subfieldK,
						fractions,
						polynomialScalars,
						algebraic_element.PolynomialImageRing.Read(M).AsFact().At(k, t),
						integral_element.IndependentOverFractionField.Read(M).At(
							a.TermAs[Set[A]]("polynomial_image(field_ring(M), k, t)"), B, E)))
				spaceL := a.Have(
					"L is a vector space over B",
					"module_on(restrict_ring(field_ring(M), B), restrict_module(regular_module(field_ring(M)), L))",
					By(rational, subfieldL, field_extension.ExtensionModuleOn.Read(M).At(B, L)))
				finiteL := a.Have(
					"L is finite dimensional over B",
					"finite_dimensional(restrict_ring(field_ring(M), B), "+
						"    restrict_module(regular_module(field_ring(M)), L))",
					By(finiteOverB, field_extension.FiniteExtensionDef.At(m, B, L)))
				inL := a.Have(
					"the independent constant-field basis lies in L",
					"module_independent(restrict_ring(field_ring(M), B), "+
						"    restrict_module(regular_module(field_ring(M)), L), "+
						"    E)",
					BySets(
						independent,
						constants,
						subfieldL,
						rationalScalars,
						field.SubfieldSubset.At(m, L),
						linear_independence.IndependentRestrict.At(
							a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), B)"), ambientVectors, L, E)))
				small := a.Have(
					"the basis is finite and bounded by the dimension of L over B",
					"finite(E) ∧ "+
						"card(E) ≤ "+
						"module_dim(restrict_ring(field_ring(M), B), restrict_module(regular_module(field_ring(M)), L))",
					By(
						rational,
						finiteL,
						inL,
						field.SubfieldRingSubfield.Read(M).At(B, B),
						module_dimension.IndependentBound.Read(spaceL).At(inverse, E)))
				degree := a.Have(
					"the finite basis computes the constant-field degree",
					"finite_extension(M, k, C) ∧ extension_degree(M, k, C) = card(E)",
					By(small, constants, subfieldK, basisOfC, field_extension.BasisDegree.Read(M).At(k, C, E)))
				a.Show(
					"the constants have degree at most the function-field degree",
					By(small, degree, field_extension.ExtensionDegreeDef.At(m, B, L)))
			})

			// t with a basis of L over B = k(t) generates a field holding B and the basis, hence its B-span L.
			finiteGeneration := ctx.Lemma(Statement{
				Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A.",
				Hypotheses: []string{
					"subfield(M, k)",
					"subfield(M, L)",
					"k ⊆ L",
					"t ∈ L",
					"finite_extension(M, field_adjoin(M, k, {t}), L)",
				},
				Conclusion: "∃E:set(A). finite(E) ∧ E ⊆ L ∧ field_adjoin(M, k, E) = L",
			}, func(
				a *Argument,
				M field.FieldFact[on.M],
				k, L *Expr[Set[A]],
				t *Expr[A],
				subfieldK, subfieldL, kInL, tInL, finiteOverB Fact,
			) {
				m := a.TermAs[FieldOps[A]]("M")
				B, bDef := a.LetAs[Set[A]]("B", "field_adjoin(M, k, {t})")
				scalarsB := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), B)")
				ambientVectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
				vectorsL := a.TermAs[module_record.ModuleOps[A, A]](
					"restrict_module(regular_module(field_ring(M)), L)")
				rational := a.Have(
					"the rational field lies between k and L",
					"subfield(M, B) ∧ k ⊆ B ∧ B ⊆ L",
					Simp(Fwd(bDef)),
					BySets(M, subfieldK, subfieldL, kInL, tInL, At(algebraic_element.AdjoinElementBetween, m, k, L, t)))
				ambient := a.Have(
					"the ambient field is a B-module",
					"module_on(restrict_ring(field_ring(M), B), regular_module(field_ring(M)))",
					By(rational, field_extension.SubfieldScalars.Read(M).At(B)))
				F, basisOfL := a.ObtainAs[Set[A]](
					"choose a finite basis of L over B",
					"∃F:set(A). "+
						"    finite(F) ∧ "+
						"    module_basis(restrict_ring(field_ring(M), B), "+
						"        restrict_module(regular_module(field_ring(M)), L), "+
						"        F)",
					By(
						finiteOverB,
						field_extension.FiniteExtensionDef.At(m, B, L),
						module_dimension.FiniteDimensionalDef.At(scalarsB, vectorsL)),
					Named("F"))
				subfieldsAreModules := a.Have(
					"every intermediate subfield is a B-submodule",
					Statement{
						Binders:    "∀N:set(A).",
						Hypotheses: []string{"subfield(M, N)", "B ⊆ N"},
						Conclusion: "submodule(restrict_ring(field_ring(M), B), regular_module(field_ring(M)), N)",
					},
					Derive(func(b *Argument) {
						N := b.FixAs[Set[A]]("N")
						between := b.Assume()
						b.Show(
							"subfield closure gives the submodule criterion",
							BySets(
								ambient,
								between,
								field.SubfieldSubset.At(m, N),
								field.SubfieldZero.At(m, N),
								At(field.SubfieldAdd, m, N),
								At(field.SubfieldMul, m, N),
								submodule.SubmoduleCriterion.At(scalarsB, ambientVectors, N)))
					}))
				moduleL := a.Have(
					"L is a submodule of the ambient B-module",
					"submodule(restrict_ring(field_ring(M), B), regular_module(field_ring(M)), L)",
					By(subfieldsAreModules.At(L), rational, subfieldL))
				spanning := a.Have(
					"the finite basis spans L in the ambient module",
					"finite(F) ∧ "+
						"F ⊆ L ∧ "+
						"module_span(restrict_ring(field_ring(M), B), regular_module(field_ring(M)), F) = L",
					By(
						Normalized,
						basisOfL,
						ambient,
						moduleL,
						linear_independence.ModuleBasisDef.At(scalarsB, vectorsL, F),
						linear_independence.IndependentInCarrier.At(scalarsB, vectorsL, F),
						linear_independence.SpanRestrict.At(scalarsB, ambientVectors, L, F)))
				G, gDef := a.LetAs[Set[A]]("G", "insert(t, F)")
				D, dDef := a.LetAs[Set[A]]("D", "field_adjoin(M, k, G)")
				generators := a.Have(
					"the parameter and basis form a finite subset of L",
					"finite(G) ∧ G ⊆ L",
					Simp(Fwd(gDef)),
					BySets(spanning, tInL, finite_set.FiniteInsert.At(t, F)))
				generated := a.Have(
					"the generated field lies in L and contains k and the generators",
					"subfield(M, D) ∧ k ⊆ D ∧ G ⊆ D ∧ D ⊆ L",
					Simp(Fwd(dDef)),
					BySets(
						generators,
						subfieldL,
						kInL,
						field.SubfieldSubset.At(m, L),
						algebraic_element.AdjoinSubfield.Read(M).At(k, G),
						algebraic_element.AdjoinLeast.Read(M).At(k, G, L)))
				contains := a.Have(
					"the generated field contains B and the basis",
					"B ⊆ D ∧ F ⊆ D",
					Simp(Fwd(bDef)),
					BySets(gDef, generated, algebraic_element.AdjoinLeast.Read(M).At(k, a.TermAs[Set[A]]("{t}"), D)))
				moduleD := a.Have(
					"the generated field is a B-submodule",
					"submodule(restrict_ring(field_ring(M), B), regular_module(field_ring(M)), D)",
					By(subfieldsAreModules.At(D), contains, generated))
				containsSpan := a.Have(
					"the generated field contains the B-span of the basis",
					"module_span(restrict_ring(field_ring(M), B), regular_module(field_ring(M)), F) ⊆ D",
					By(contains, moduleD, submodule.SpanLeast.At(scalarsB, ambientVectors, F, D)))
				equality := a.Have(
					"the generated field is all of L",
					"D = L",
					BySets(containsSpan, spanning, generated))
				a.Take(G)
				a.Show(
					"G is a finite field-generating set",
					By(Normalized, dDef, equality, generators))
			})

			// The constants C are finite over the finite k, so finite and perfect, and L is regular over C: finitely generated, and algebraic over C(t).
			return ctx.Theorem(headline, func(
				a *Argument,
				M field.FieldFact[on.M],
				k, L *Expr[Set[A]],
				t *Expr[A],
				subfieldK, subfieldL, finiteK, kInL, tInL, transcendental, finiteOverB Fact,
			) {
				m := a.TermAs[FieldOps[A]]("M")
				C, cDef := a.LetAs[Set[A]]("C", "«constants»")
				B, bDef := a.LetAs[Set[A]]("B", "field_adjoin(M, k, {t})")
				constants := a.Have(
					"C is the exact constant subfield and t remains transcendental over it",
					"subfield(M, C) ∧ "+
						"k ⊆ C ∧ "+
						"C ⊆ L ∧ "+
						"¬algebraic_over(M, C, t) ∧ "+
						"(∀x:A. x ∈ L ∧ algebraic_over(M, C, x) ⇒ x ∈ C)",
					Simp(Fwd(cDef)),
					BySets(M, subfieldK, subfieldL, kInL, tInL, transcendental, At(constantField, m, k, L)))
				finiteExtension := a.Have(
					"C is finite over k",
					"finite_extension(M, k, C)",
					Simp(Fwd(cDef)),
					By(
						M,
						bDef,
						subfieldK,
						subfieldL,
						kInL,
						tInL,
						transcendental,
						finiteOverB,
						At(degreeBound, m, k, L, t)))
				spaceC := a.Have(
					"C is a vector space over k",
					"module_on(restrict_ring(field_ring(M), k), restrict_module(regular_module(field_ring(M)), C))",
					By(constants, subfieldK, field_extension.ExtensionModuleOn.Read(M).At(k, C)))
				finiteC := a.Have(
					"C is finite dimensional over k",
					"finite_dimensional(restrict_ring(field_ring(M), k), "+
						"    restrict_module(regular_module(field_ring(M)), C))",
					By(finiteExtension, field_extension.FiniteExtensionDef.At(m, k, C)))
				fieldC := a.Have(
					"C carries its restricted field",
					"field_on(restrict_field(M, C))",
					By(constants, field.SubfieldFieldOn.Read(M).At(C)))
				cardinalityC := a.Have(
					"C is finite and its cardinality is the corresponding power of card(k)",
					"finite(C) ∧ card(C) = card(k) ^ extension_degree(M, k, C)",
					By(
						subfieldK,
						constants,
						finiteK,
						finiteExtension,
						finite_field.FiniteExtensionSize.Read(M).At(k, C),
						cardinality.HasSizeDef.At(C, a.TermAs[Nat]("card(k) ^ extension_degree(M, k, C)"))))
				nontrivial := a.Have(
					"the constant subfield contains a nonzero unit",
					"C ≠ {M.zero}",
					BySets(field.OneNotZeroOn.Read(M), constants, field.SubfieldOne.At(m, C)))
				positive := a.Have(
					"the constant extension has positive degree",
					"0 < extension_degree(M, k, C)",
					ByArith(
						nontrivial,
						subfieldK,
						finiteC,
						field.SubfieldRingSubfield.Read(M).At(k, k),
						module_dimension.DimZero.Read(spaceC).At(a.TermAs[Fun[A, A]]("M.inv")),
						field_extension.ExtensionDegreeDef.At(m, k, C)))
				perfect := a.Have(
					"the finite constant field is perfect",
					"perfect_field(restrict_field(M, C))",
					By(cardinalityC, perfect_field.FiniteFieldIsPerfect.Read(fieldC)))
				D, dDef := a.LetAs[Set[A]]("D", "field_adjoin(M, C, {t})")
				rational := a.Have(
					"B is a subfield",
					"subfield(M, B)",
					Simp(Fwd(bDef)),
					BySets(M, subfieldK, subfieldL, kInL, tInL, At(algebraic_element.AdjoinElementBetween, m, k, L, t)))
				largerRational := a.Have(
					"C(t) lies between C and L",
					"subfield(M, D) ∧ C ⊆ D ∧ t ∈ D ∧ D ⊆ L",
					Simp(Fwd(dDef)),
					BySets(M, constants, subfieldL, tInL, At(algebraic_element.AdjoinElementBetween, m, C, L, t)))
				baseInD := a.Have(
					"enlarging constants enlarges the rational subfield",
					"B ⊆ D",
					Simp(Fwd(bDef)),
					BySets(
						largerRational,
						constants,
						algebraic_element.AdjoinLeast.Read(M).At(k, a.TermAs[Set[A]]("{t}"), D)))
				finiteD := a.Have(
					"L remains finite over C(t)",
					"finite_extension(M, D, L)",
					By(
						rational,
						baseInD,
						largerRational,
						subfieldL,
						finiteOverB,
						field_extension.TowerFinite.Read(M).At(B, D, L)))
				generators := a.Have(
					"L is finitely generated over C",
					"∃E:set(A). finite(E) ∧ E ⊆ L ∧ field_adjoin(M, C, E) = L",
					By(M, finiteD, dDef, constants, subfieldL, tInL, At(finiteGeneration, m, C, L, t)))
				algebraic := a.Have(
					"every element of L is algebraic over C(t)",
					"∀x:A. x ∈ L ⇒ algebraic_over(M, D, x)",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						xInL := b.Assume()
						b.Show(
							"finite extensions are algebraic",
							By(
								xInL,
								finiteD,
								largerRational,
								subfieldL,
								algebraic_element.FiniteExtensionAlgebraic.Read(M).AsFact().At(D, L, x)))
					}))
				parameter := a.Have(
					"t gives transcendence degree one over C",
					"∃s:A. "+
						"    s ∈ L ∧ "+
						"    ¬algebraic_over(M, C, s) ∧ "+
						"    (∀x:A. x ∈ L ⇒ algebraic_over(M, field_adjoin(M, C, {s}), x))",
					Witness(t),
					Simp(Rev(dDef)),
					By(algebraic, constants, tInL))
				regular := a.Have(
					"L is a regular function field over C",
					"regular_function_field(M, C, L)",
					Simp(Fwd(RegularFunctionFieldDef)),
					By(perfect, parameter, generators, constants, subfieldL))
				degree := a.Have(
					"use the positive extension degree as r",
					"∃r:num. 0 < r ∧ card(C) = card(k) ^ r ∧ extension_degree(M, k, C) = r",
					Witness(a.TermAs[Nat]("extension_degree(M, k, C)")),
					By(positive, cardinalityC))
				a.Show(
					"C is the finite exact constant field with the stated cardinality and degree",
					By(cardinalityC, constants, regular, degree))
			})
		}),
})}
