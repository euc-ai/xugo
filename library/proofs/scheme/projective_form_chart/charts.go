// charts.go — the chart of a form F over k on a projective equation curve:
// the ring of the values P(x)/F(x)^a at the generic point x of the forms P
// of degree r·a. It and the affine piece of each nonzero coordinate lie in
// the other with one element inverted, so on a smooth curve it is integrally
// closed, and K is its field of fractions. The charts of two forms F, G of one
// degree glue along t = G(x)/F(x) into a biaffine datum; when F and G have no
// common zero on the curve, each chart is free of finite rank over its line,
// the two meet in k and t is transcendental over k, so they are a curve over
// the line.

package projective_form_chart

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_affine_piece"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_form_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_generic_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_sections"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartQuotientsGenerate — the quotients g_i = x(i)^r/F(x) lie in the chart
// of F and generate its unit ideal. Each is the value of the form X_i^r over
// F(x). A maximal ideal m holding them all would hold every u_α = x^α/F(x)
// for the monomials α of F: u_α^r is the product of the g_i^α(i), α having
// degree r and so a positive exponent, and m is prime. Then m would hold
// Σ F(α)·u_α = F(x)/F(x) = 1.
var ChartQuotientsGenerate = chartQuotientsGenerateThm{family.Add(registry.ProofEntry{
	Name: "ChartQuotientsGenerate",
	Key:  "prop_7c2071fa44e35de4",
	Reading: "0 < r is what gives each monomial of F a " +
		"positive exponent, so a factor g_j in the product u_α^r.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r:num. ∀x:(num → A). ∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"0 < r",
			"«at»(F) ≠ M.zero",
		},
		Conclusion: "«quotients» ⊆ «chart»(F) ∧ M.one ∈ ideal_span(«chartRing», «quotients»)",
		Abbrev: Abbrev{
			{Name: "quotients", Text: "{monoid_pow(M.mul, M.one, x(i), r) * M.inv(«at»(F)) | i:num | i ≤ n}"},
			{Name: "chartRing", Text: "restrict_ring(field_ring(M), «chart»(F))"},
			{Name: "monomialQuotient", Text: "λα:(num → num). " +
				"    monomial_eval(field_ring(M), x, α) * M.inv(«at»(F))"},
			{Name: "g", Text: "λi:num. monoid_pow(M.mul, M.one, x(i), r) * M.inv(«at»(F))"},
			{Name: "rthPower", Text: "λi:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», i), " +
				"        r)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			x *Arrow[Nat, A],
			F *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, kInK, coordinates, form, positive, nonzero Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			powIn := comm_monoid.PowIn.Read(monoid)
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			coefficients := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			chart := a.TermAs[Set[A]]("«chart»(F)")
			chartOps := a.TermAs[module_record.RingOps[A]]("«chartRing»")
			quotients := a.TermAs[Set[A]]("«quotients»")
			support := a.TermAs[Set[Fun[Nat, Nat]]]("fun_support(M.zero, F)")
			inverseF := a.TermAs[A]("M.inv(«at»(F))")
			one := a.TermAs[Nat]("1")
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInM := a.Have(
				"and so does k",
				"k ⊆ M.carrier",
				By(kSub, field.SubfieldSubset))
			coordinatesInM := a.Have(
				"the coordinates up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			atX := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			fPolynomial, fDegree :=
				homogeneous_polynomial.FormPolynomial.Read(form), homogeneous_polynomial.FormDegree.Read(form)
			values := a.Conjuncts(
				a.Have(
					"F(x) and its inverse lie in M",
					"«at»(F) ∈ M.carrier ∧ M.inv(«at»(F)) ∈ M.carrier",
					BySets(fPolynomial, atX[1], KInM, field.InvIn.Read(M))),
				"F(x) lies in M",
				"and so does its inverse")
			coefficientsF := a.Conjuncts(
				a.Simplified(fPolynomial.AsFact(), Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"F is nonzero at finitely many monomials",
				"every monomial where F is nonzero is a monomial of the variables up to n",
				"every coefficient of F lies in k")
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			coefficientRing := ring_homomorphism.Source.Read(inclusion)
			chartRing := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinatesInM, form, projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
				"the chart is a subring of M",
				"holding k")
			ringC := a.Have(
				"so it is a ring under the operations of M",
				"comm_ring_on(«chartRing»)",
				By(chartRing[0], comm_ring.SubringRingOn.Read(ring).At(chart)))
			inverseOne := a.Have(
				"the first power of F(x)^(−1) is itself",
				"monoid_pow(M.mul, M.one, M.inv(«at»(F)), 1) = M.inv(«at»(F))",
				By(values[1], comm_monoid.PowOneOn.Read(monoid)))
			degreeOne := a.Have(
				"r·1 = 1·r",
				"r * 1 = 1 * r",
				ByArith())
			// The quotients lie in the chart.
			inChart := a.Have(
				"each g_i is the value of the form X_i^r over F(x), in the chart",
				"∀i:num. i ≤ n ⇒ «g»(i) ∈ «chart»(F)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					iInRange := b.Assume()
					varI := b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_var(«hilbertCoefficients», i)")
					xiInM := b.Have(
						"x(i) lies in M",
						"x(i) ∈ M.carrier",
						By(iInRange, coordinatesInM))
					varIForm := b.Have(
						"X_i is a form of degree 1",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    1, "+
							"    polynomial_algebra_var(«hilbertCoefficients», i))",
						By(iInRange, coefficientRing, homogeneous_polynomial.FormVariable.At(coefficients, n, i)))
					varIValue := b.Have(
						"evaluating to x(i)",
						"«at»(polynomial_algebra_var(«hilbertCoefficients», i)) = x(i)",
						By(
							inclusion,
							xiInM,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(coefficients, fieldRing, identity, x, i)))
					powerForm := b.Have(
						"so X_i^r is a form of degree r·1",
						"homogeneous_polynomial(«hilbertCoefficients», n, r * 1, «rthPower»(i))",
						degreeOne.Rw(),
						By(coefficientRing, varIForm, homogeneous_polynomial.FormPower.At(coefficients, n, one, varI, r)))
					powerValue := b.Have(
						"evaluating to x(i)^r, evaluation keeping powers",
						"«at»(«rthPower»(i)) = monoid_pow(M.mul, M.one, x(i), r)",
						By(
							homogeneous_polynomial.FormPolynomial.Read(varIForm),
							varIValue,
							polynomial_algebra.PolynomialAlgebraRingDef,
							ring_homomorphism.RingMapPower.Read(atX[0])))
					b.Show(
						"so x(i)^r/F(x) lies in the chart",
						By(
							powerValue,
							inverseOne,
							GroupPremises(
								kSub,
								KSub,
								kInK,
								coordinates,
								form,
								nonzero,
								powerForm,
								projective_curve.ChartQuotient.Read(M).At(
									k, K, n, r, one, x, F, b.TermAs[Fun[Fun[Nat, Nat], A]]("«rthPower»(i)")))))
				}))
			quotientsInChart := a.Have(
				"so the quotients lie in the chart",
				"«quotients» ⊆ «chart»(F)",
				BySets(inChart))
			// The monomials of F.
			monomialFacts := a.Have(
				"a monomial α at which F is nonzero is a monomial of "+
					"the variables up to n of degree r, whose value lies in M",
				Statement{
					Binders:    "∀α:(num → num).",
					Hypotheses: []string{"F(α) ≠ M.zero"},
					Conclusion: "α ∈ monomials({i:num | i ≤ n}) ∧ " +
						"sum({i:num | i ≤ n}, α) = r ∧ " +
						"sum(fun_support(0, α), α) = r ∧ " +
						"monomial_eval(field_ring(M), x, α) ∈ M.carrier",
				},
				Derive(func(b *Argument) {
					α := b.FixAs[Fun[Nat, Nat]]("α")
					nonzeroAt := b.Assume()
					monomial := b.Have(
						"α is a monomial of the variables up to n, F being nonzero there",
						"α ∈ monomials({i:num | i ≤ n})",
						BySets(coefficientsF[1], nonzeroAt))
					onVariables := b.Have(
						"the support of α lies among the variables up to n, and α is zero off it",
						"fun_support(0, α) ⊆ {i:num | i ≤ n} ∧ "+
							"(∀y:num. y ∈ {i:num | i ≤ n} ∧ y ∉ fun_support(0, α) ⇒ α(y) = 0)",
						BySets(monomial, polynomial_algebra.MonomialsMember.At(variables, α)))
					degree := b.Have(
						"α has degree r, F being a form of degree r",
						"sum({i:num | i ≤ n}, α) = r",
						By(nonzeroAt, fDegree.At(α)))
					b.Show(
						"over its support too, and its value is a product of members of M",
						By(
							monomial,
							degree,
							onVariables,
							ring,
							coordinatesInM,
							nat_sum.Superset.At(b.TermAs[Set[Nat]]("fun_support(0, α)"), variables, α),
							polynomial_algebra_evaluation.MonomialEvalIn.At(fieldRing, variables, x, α)))
				}))
			monomialsInChart := a.Have(
				"each u_α, x^α/F(x) for a monomial α of F, is the "+
					"value of the monomial form X^α over F(x), in the chart",
				"∀α:(num → num). F(α) ≠ M.zero ⇒ «monomialQuotient»(α) ∈ «chart»(F)",
				Derive(func(b *Argument) {
					α := b.FixAs[Fun[Nat, Nat]]("α")
					nonzeroAt := b.Assume()
					facts := b.Conjuncts(
						GroupPremises(nonzeroAt, monomialFacts.At(α)),
						"α is a monomial",
						"of degree r",
						"over its support too",
						"whose value lies in M")
					delta := b.TermAs[Fun[Fun[Nat, Nat], A]]("delta_at(α)")
					deltaForm := b.Have(
						"the coefficient one at α is a form of degree r·1",
						"homogeneous_polynomial(«hilbertCoefficients», n, r * 1, delta_at(α))",
						By(
							coefficientRing,
							comm_ring.OneIn.Read(coefficientRing),
							facts[0],
							facts[1],
							b.Have(
								"r·1 = r",
								"r * 1 = r",
								ByArith()),
							homogeneous_polynomial.FormMonomial.At(coefficients, n, b.TermAs[A]("M.one"), α)))
					deltaValue := b.Have(
						"evaluating to x^α",
						"«at»(delta_at(α)) = monomial_eval(field_ring(M), x, α)",
						By(
							inclusion,
							field.OneNotZeroOn.Read(M),
							facts[3],
							polynomial_algebra_evaluation.PolynomialAlgebraEvalMonomial.At(
								coefficients, fieldRing, identity, x, α)))
					b.Show(
						"so x^α/F(x) lies in the chart",
						By(
							deltaValue,
							inverseOne,
							GroupPremises(
								kSub,
								KSub,
								kInK,
								coordinates,
								form,
								nonzero,
								deltaForm,
								projective_curve.ChartQuotient.Read(M).At(k, K, n, r, one, x, F, delta))))
				}))
			// One is Σ F(α)·u_α.
			terms := a.TermAs[Fun[Fun[Nat, Nat], A]](
				"λα:(num → num). F(α) * monomial_eval(field_ring(M), x, α)")
			termsInM := a.Have(
				"each term F(α)·x^α lies in M",
				Statement{
					Binders:    "∀α:(num → num).",
					Hypotheses: []string{"α ∈ fun_support(M.zero, F)"},
					Conclusion: "F(α) * monomial_eval(field_ring(M), x, α) ∈ M.carrier",
				},
				Derive(func(b *Argument) {
					α := b.FixAs[Fun[Nat, Nat]]("α")
					nonzeroAt := b.Have(
						"F is nonzero at α",
						"F(α) ≠ M.zero",
						BySets(b.Assume()))
					facts := b.Conjuncts(
						GroupPremises(nonzeroAt, monomialFacts.At(α)),
						"α is a monomial",
						"of degree r",
						"over its support too",
						"whose value lies in M")
					b.Show(
						"a coefficient in k times the value of α",
						By(facts[3], coefficientsF[2].At(α), kInM, set_basic.SubsetDef, comm_ring.MulIn.Read(ring)))
				}))
			expansion := a.Have(
				"F(x) is the sum of the terms F(α)·x^α",
				"«at»(F) = "+
					"module_sum(M.add, "+
					"    M.zero, "+
					"    fun_support(M.zero, F), "+
					"    λα:(num → num). F(α) * monomial_eval(field_ring(M), x, α))",
				By(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef))
			scaled := a.Have(
				"F(x)^(−1) times the sum is the sum of the terms times F(x)^(−1)",
				"M.inv(«at»(F)) * "+
					"module_sum(M.add, "+
					"    M.zero, "+
					"    fun_support(M.zero, F), "+
					"    λα:(num → num). F(α) * monomial_eval(field_ring(M), x, α)) = "+
					"module_sum(M.add, "+
					"    M.zero, "+
					"    fun_support(M.zero, F), "+
					"    λα:(num → num). M.inv(«at»(F)) * (F(α) * monomial_eval(field_ring(M), x, α)))",
				By(
					coefficientsF[0],
					termsInM,
					values[1],
					module.ModuleSumSmul.Read(module.RegularModuleOn.Read(ring)).AsFact().At(support, inverseF, terms)))
			regrouped := a.Have(
				"each scaled term is F(α)·u_α",
				Statement{
					Binders:    "∀α:(num → num).",
					Hypotheses: []string{"α ∈ fun_support(M.zero, F)"},
					Conclusion: "M.inv(«at»(F)) * (F(α) * monomial_eval(field_ring(M), x, α)) = " +
						"F(α) * «monomialQuotient»(α)",
				},
				Derive(func(b *Argument) {
					α := b.FixAs[Fun[Nat, Nat]]("α")
					nonzeroAt := b.Have(
						"F is nonzero at α",
						"F(α) ≠ M.zero",
						BySets(b.Assume()))
					facts := b.Conjuncts(
						GroupPremises(nonzeroAt, monomialFacts.At(α)),
						"α is a monomial",
						"of degree r",
						"over its support too",
						"whose value lies in M")
					coefficient := b.Have(
						"F(α) lies in M",
						"F(α) ∈ M.carrier",
						By(coefficientsF[2].At(α), kInM, set_basic.SubsetDef))
					b.Show(
						"the product regroups",
						ByArith(M, coefficient, facts[3], values[1]))
				}))
			inverse := a.Have(
				"F(x)^(−1)·F(x) = 1, F(x) being nonzero",
				"M.inv(«at»(F)) * «at»(F) = M.one",
				By(nonzero, values[0], field.MulLeftInverseOn.Read(M)))
			congruent := a.Have(
				"so the sum of the scaled terms is the sum of the F(α)·u_α",
				"module_sum(M.add, "+
					"    M.zero, "+
					"    fun_support(M.zero, F), "+
					"    λα:(num → num). M.inv(«at»(F)) * (F(α) * monomial_eval(field_ring(M), x, α))) = "+
					"module_sum(M.add, M.zero, fun_support(M.zero, F), λα:(num → num). F(α) * «monomialQuotient»(α))",
				By(
					regrouped,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("M.add"),
						a.TermAs[A]("M.zero"),
						support,
						a.TermAs[Fun[Fun[Nat, Nat], A]](
							"λα:(num → num). M.inv(«at»(F)) * (F(α) * monomial_eval(field_ring(M), x, α))"),
						a.TermAs[Fun[Fun[Nat, Nat], A]]("λα:(num → num). F(α) * «monomialQuotient»(α)"))))
			unitSum := a.Have(
				"so one, F(x)^(−1)·F(x), is the sum of the F(α)·u_α over the monomials of F",
				"M.one = "+
					"module_sum(M.add, M.zero, fun_support(M.zero, F), λα:(num → num). F(α) * «monomialQuotient»(α))",
				By(inverse, expansion, scaled, congruent))
			// A maximal ideal holding the quotients would hold one.
			unit := a.Have(
				"so the quotients generate the unit ideal of the chart",
				"M.one ∈ ideal_span(«chartRing», «quotients»)",
				Derive(func(b *Argument) {
					outside := b.SupposeNot()
					span := b.TermAs[Set[A]]("ideal_span(«chartRing», «quotients»)")
					spanIdeal := b.Have(
						"the quotients span an ideal of the chart",
						"ring_ideal(«chartRing», ideal_span(«chartRing», «quotients»))",
						By(quotientsInChart, ring_ideal.SpanIdeal.Read(ringC).AsFact().At(quotients)))
					p, maximal := b.ObtainAs[Set[A]](
						"else it lies in a maximal ideal m of the chart",
						"∃m:set(A). maximal_ideal(«chartRing», m) ∧ ideal_span(«chartRing», «quotients») ⊆ m",
						By(spanIdeal, outside, ringC, ring_ideal.ExistsMaximalAbove.Read(ringC).At(span)),
						Named("m"))
					parts := b.Conjuncts(
						maximal,
						"m is maximal",
						"and holds the span of the quotients")
					prime := b.Have(
						"m is prime",
						"prime_ideal(«chartRing», m)",
						By(parts[0], ring_ideal.MaximalIsPrime.Read(ringC)))
					idealM := b.Have(
						"and an ideal of the chart",
						"ring_ideal(«chartRing», m)",
						By(parts[0], ring_ideal.MaximalIdealIdeal.At(chartOps, p)))
					quotientsInM := b.Have(
						"m holds every quotient g_i",
						"∀i:num. i ≤ n ⇒ «g»(i) ∈ m",
						Derive(func(c *Argument) {
							c.FixAs[Nat]("i")
							member := c.Have(
								"g_i is one of the quotients",
								"«g»(i) ∈ «quotients»",
								BySets(c.Assume()))
							c.Show(
								"so it lies in their span, inside m",
								By(member, parts[1], ring_ideal.SpanContains.At(chartOps, quotients), set_basic.SubsetDef))
						}))
					monomialsInM := b.Have(
						"m holds each u_α: u_α^r is the product of the g_i^α(i), with a factor g_j, and m is prime",
						"∀α:(num → num). F(α) ≠ M.zero ⇒ «monomialQuotient»(α) ∈ m",
						Derive(func(c *Argument) {
							α := c.FixAs[Fun[Nat, Nat]]("α")
							nonzeroAt := c.Assume()
							facts := c.Conjuncts(
								GroupPremises(nonzeroAt, monomialFacts.At(α)),
								"α is a monomial",
								"of degree r",
								"over its support too",
								"whose value lies in M")
							powers := c.Have(
								"the powers x(i)^r lie in M",
								"∀i:num. i ≤ n ⇒ monoid_pow(M.mul, M.one, x(i), r) ∈ M.carrier",
								BySets(coordinatesInM, powIn))
							product := c.Have(
								"the product of the g_i^α(i) is (x^α)^r·F(x)^(−r)",
								"monomial_eval(field_ring(M), «g», α) = "+
									"monoid_pow(M.mul, M.one, monomial_eval(field_ring(M), x, α), r) * "+
									"monoid_pow(M.mul, M.one, M.inv(«at»(F)), r)",
								By(
									ring,
									powers,
									coordinatesInM,
									values[1],
									facts[0],
									facts[2],
									polynomial_algebra_evaluation.MonomialEvalScale.At(
										fieldRing,
										variables,
										c.TermAs[Fun[Nat, A]]("λi:num. monoid_pow(M.mul, M.one, x(i), r)"),
										inverseF,
										α),
									polynomial_algebra_evaluation.MonomialEvalPow.At(fieldRing, variables, x, r, α)))
							power := c.Have(
								"which is u_α^r",
								"monoid_pow(M.mul, M.one, «monomialQuotient»(α), r) = monomial_eval(field_ring(M), «g», α)",
								By(
									product,
									facts[3],
									values[1],
									comm_monoid.MulPowOn.Read(monoid).AsFact().At(
										c.TermAs[A]("monomial_eval(field_ring(M), x, α)"), inverseF, r)))
							positiveAt := c.Have(
								"α has a positive exponent at some j up to n, its degree r being positive",
								"∃j:num. j ≤ n ∧ α(j) ≠ 0",
								By(
									facts[1],
									c.Have(
										"r ≠ 0",
										"r ≠ 0",
										ByArith(positive)),
									nat_sum.EqZero.At(variables, α),
									num_segment.FiniteBelow.At(n)))
							j, jParts := c.UnpackAs[Nat](positiveAt, "j")
							at := c.Conjuncts(
								jParts,
								"j is a variable up to n",
								"where α is positive")
							sameValue := c.Have(
								"the value of α at the quotients is the same in the chart as in M",
								"monomial_eval(«chartRing», «g», α) = monomial_eval(field_ring(M), «g», α)",
								Simp(Fwd(polynomial_algebra_evaluation.MonomialEvalDef)),
								Refl())
							productInM := c.Have(
								"so the product lies in m, which holds g_j",
								"monomial_eval(«chartRing», «g», α) ∈ m",
								By(
									ringC,
									idealM,
									inChart,
									facts[0],
									at[1],
									quotientsInM.At(j),
									at[0],
									polynomial_algebra_evaluation.MonomialEvalInIdeal.At(
										chartOps, variables, p, c.TermAs[Fun[Nat, A]]("«g»"), α, j)))
							c.Show(
								"so u_α lies in m, a prime holding its r-th power",
								By(
									prime,
									GroupPremises(nonzeroAt, monomialsInChart.At(α)),
									power,
									sameValue,
									productInM,
									ring_ideal.PrimeIdealPow.Read(ringC).AsFact().At(p, c.TermAs[A]("«monomialQuotient»(α)"), r)))
						}))
					subspace := b.Have(
						"m is a submodule of the chart over itself",
						"submodule(«chartRing», regular_module(«chartRing»), m)",
						By(idealM, ringC, submodule.IdealIffRegularSubmodule.At(chartOps, p)))
					termsInM := b.Have(
						"each F(α)·u_α lies in m, F(α) lying in k and so in the chart",
						"∀α:(num → num). α ∈ fun_support(M.zero, F) ⇒ F(α) * «monomialQuotient»(α) ∈ m",
						Derive(func(c *Argument) {
							α := c.FixAs[Fun[Nat, Nat]]("α")
							nonzeroAt := c.Have(
								"F is nonzero at α",
								"F(α) ≠ M.zero",
								BySets(c.Assume()))
							coefficient := c.Have(
								"F(α) lies in the chart",
								"F(α) ∈ «chart»(F)",
								By(coefficientsF[2].At(α), chartRing[1], set_basic.SubsetDef))
							c.Show(
								"an ideal absorbs a multiple of its member",
								By(
									coefficient,
									GroupPremises(nonzeroAt, monomialsInM.At(α)),
									ring_ideal.IdealMul.Read(idealM).AsFact().At(
										c.TermAs[A]("F(α)"), c.TermAs[A]("«monomialQuotient»(α)"))))
						}))
					sumInM := b.Have(
						"so m holds their sum, which is one",
						"M.one ∈ m",
						unitSum.Rw(),
						By(
							subspace,
							coefficientsF[0],
							termsInM,
							submodule.SubmoduleModuleSum.Read(module.RegularModuleOn.Read(ringC)).AsFact().At(
								p, support, a.TermAs[Fun[Fun[Nat, Nat], A]]("λα:(num → num). F(α) * «monomialQuotient»(α)"))))
					b.Show(
						"which a maximal ideal does not hold",
						By(sumInM, parts[0], ring_ideal.MaximalIdealProper.At(chartOps, p)))
				}))
			a.Show(
				"the quotients lie in the chart and generate its unit ideal",
				By(quotientsInChart, unit))
		}),
})}

// ChartPieceAways — the chart of F and the affine piece where the j-th
// coordinate is not zero lie each inside the other with one element
// inverted. The piece is a subring of K holding h = F(x/x(j)) = F(x)/x(j)^r,
// the inverse of g = x(j)^r/F(x). A member y of the chart with y·F(x)^a =
// P(x) has h^a·y = P(x/x(j)), in the piece; and g times an affine
// coordinate x(i)/x(j) is x(i)·x(j)^(r−1)/F(x), the value of the form
// X_i·X_j^(r−1) (homogeneous_polynomial.MixedMonomialForm) over F(x), in the
// chart, so the piece, generated over k by the affine coordinates, lies in
// the chart with g inverted.
var ChartPieceAways = chartPieceAwaysThm{family.Add(registry.ProofEntry{
	Name: "ChartPieceAways",
	Key:  "prop_e5f22bcb9ba6cdd4",
	Reading: "x(j) ≠ zero makes the affine coordinates and h defined, F(x) ≠ zero makes " +
		"g·h one, and 0 < r lets g·x(i)/x(j) be the value of the form X_i·X_j^(r−1) over F(x).",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r j:num. ∀x:(num → A). ∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"j ≤ n",
			"x(j) ≠ M.zero",
		},
		Conclusion: "subring(field_ring(M), «piece»(j)) ∧ " +
			"«piece»(j) ⊆ K ∧ " +
			"«h»(j) ∈ «piece»(j) ∧ " +
			"«g»(j) * «h»(j) = M.one ∧ " +
			"«chart»(F) ⊆ ring_away(restrict_ring(field_ring(M), K), «piece»(j), «h»(j)) ∧ " +
			"«piece»(j) ⊆ ring_away(field_ring(M), «chart»(F), «g»(j))",
		Abbrev: Abbrev{
			{Name: "affine", Text: "λP:((num → num) → A). " +
				"    polynomial_algebra_eval(«hilbertCoefficients», " +
				"        field_ring(M), " +
				"        (λa:A. a), " +
				"        (λi:num. x(i) * M.inv(x(j))), " +
				"        P)"},
			{Name: "piece", Text: "λj:num. " +
				"    {polynomial_algebra_eval(restrict_ring(field_ring(M), k), " +
				"            field_ring(M), " +
				"            (λa:A. a), " +
				"            (λi:num. x(i) * M.inv(x(j))), " +
				"            P) | " +
				"        P:((num → num) → A) | " +
				"        P ∈ polynomial_algebra(restrict_ring(field_ring(M), k), {i:num | i ≤ n})}"},
			{Name: "g", Text: "λi:num. monoid_pow(M.mul, M.one, x(i), r) * M.inv(«at»(F))"},
			{Name: "h", Text: "λj:num. " +
				"    polynomial_algebra_eval(«hilbertCoefficients», " +
				"        field_ring(M), " +
				"        (λa:A. a), " +
				"        (λi:num. x(i) * M.inv(x(j))), " +
				"        F)"},
			{Name: "varPower", Text: "λb:num. " +
				"    monoid_pow(polynomial_algebra_mul(«hilbertCoefficients»), " +
				"        polynomial_algebra_one(«hilbertCoefficients»), " +
				"        polynomial_algebra_var(«hilbertCoefficients», j), " +
				"        b)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r, j *Expr[Nat],
			x *Arrow[Nat, A],
			F *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, kInK, coordinates, form, positive, nonzero, jInRange, xjNonzero Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			powIn := comm_monoid.PowIn.Read(monoid)
			fieldOps := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			coefficients := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			polynomials := a.TermAs[module_record.RingOps[Fun[Fun[Nat, Nat], A]]]("«polynomials»")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
			affinePoint := a.TermAs[Fun[Nat, A]]("λi:num. x(i) * M.inv(x(j))")
			affineEval := a.TermAs[Fun[Fun[Fun[Nat, Nat], A], A]](
				"polynomial_algebra_eval(«hilbertCoefficients», " +
					"    field_ring(M), " +
					"    λa:A. a, " +
					"    λi:num. x(i) * M.inv(x(j)))")
			xj := a.TermAs[A]("x(j)")
			inverseXj := a.TermAs[A]("M.inv(x(j))")
			one := a.TermAs[Nat]("1")
			piece := a.TermAs[Set[A]]("«piece»(j)")
			chart := a.TermAs[Set[A]]("«chart»(F)")
			g := a.TermAs[A]("«g»(j)")
			h := a.TermAs[A]("«h»(j)")
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			xjParts := a.Conjuncts(
				a.Have(
					"x(j) and its inverse lie in K",
					"x(j) ∈ K ∧ M.inv(x(j)) ∈ K",
					By(jInRange, coordinates, KSub, field.SubfieldInv.At(fieldOps, K, xj))),
				"x(j) lies in K",
				"and so does its inverse")
			affineInK := a.Have(
				"so the affine coordinates x(i)·x(j)^(−1) lie in K",
				"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ K",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					b.Show(
						"a product in the subfield K",
						By(
							b.Assume(),
							coordinates,
							xjParts[1],
							KSub,
							field.SubfieldMul.At(fieldOps, K, b.TermAs[A]("x(i)"), inverseXj)))
				}))
			atX := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			atAffine := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, affineInK, projective_curve.PointEvaluation.Read(M).At(k, K, n, affinePoint)),
				"evaluation at the affine coordinates is a ring map",
				"with values in K")
			fPolynomial := homogeneous_polynomial.FormPolynomial.Read(form)
			coordinatesInM := a.Have(
				"the coordinates up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			valuesInM := a.Conjuncts(
				a.Have(
					"x(j), its inverse, F(x) and its inverse lie in M",
					"x(j) ∈ M.carrier ∧ M.inv(x(j)) ∈ M.carrier ∧ «at»(F) ∈ M.carrier ∧ M.inv(«at»(F)) ∈ M.carrier",
					BySets(xjParts[0], KInM, fPolynomial, atX[1], field.InvIn.Read(M))),
				"x(j) lies in M",
				"so does its inverse",
				"F(x) does",
				"and its inverse")
			xjm, inverseXjm := a.MemberOf[on.M](xj, valuesInM[0]), a.MemberOf[on.M](inverseXj, valuesInM[1])
			fm := a.MemberOf[on.M](a.TermAs[A]("«at»(F)"), valuesInM[2])
			inclusion := a.Have(
				"the inclusion of k into M is a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			scaledF := a.Have(
				"h, F at the affine coordinates, is x(j)^(−r)·F(x), F being a form of degree r",
				"«h»(j) = monoid_pow(M.mul, M.one, M.inv(x(j)), r) * «at»(F)",
				By(
					inclusion,
					form,
					coordinatesInM,
					valuesInM[1],
					homogeneous_polynomial.FormScaling.At(coefficients, fieldRing, identity, n, r, x, inverseXj, F)))
			// The piece: a subring of K holding h.
			image := a.Have(
				"the piece is the image of the polynomials under evaluation at the affine coordinates",
				"«piece»(j) = "+
					"image(polynomial_algebra_eval(«hilbertCoefficients», "+
					"        field_ring(M), "+
					"        λa:A. a, "+
					"        λi:num. x(i) * M.inv(x(j))), "+
					"    «polynomials».carrier)",
				By(
					polynomial_algebra.PolynomialAlgebraRingDef,
					set_image.SimpleImage.At(
						affineEval,
						a.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
							"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"))))
			subringPiece := a.Have(
				"so it is a subring of M, the image of a ring map",
				"subring(field_ring(M), «piece»(j))",
				image.Rw(),
				By(atAffine[0], ring_homomorphism.ImageSubring.At(polynomials, fieldRing, affineEval)))
			pieceInK := a.Have(
				"its members are values of polynomials at points of K, so lie in K",
				"«piece»(j) ⊆ K",
				BySets(atAffine[1]))
			hInPiece := a.Have(
				"h lies in the piece, F being a polynomial",
				"«h»(j) ∈ «piece»(j)",
				BySets(fPolynomial))
			// g·h = 1.
			inverses := a.Conjuncts(
				a.Have(
					"x(j)·x(j)^(−1) = 1 and F(x)^(−1)·F(x) = 1",
					"x(j) * M.inv(x(j)) = M.one ∧ M.inv(«at»(F)) * «at»(F) = M.one",
					By(
						xjNonzero,
						nonzero,
						valuesInM[0],
						valuesInM[2],
						field.MulRightInverseOn.Read(M),
						field.MulLeftInverseOn.Read(M))),
				"x(j) times its inverse is one",
				"the inverse of F(x) times F(x) is one")
			powersCancel := a.Have(
				"so x(j)^r·x(j)^(−r) = 1",
				"monoid_pow(M.mul, M.one, x(j), r) * monoid_pow(M.mul, M.one, M.inv(x(j)), r) = M.one",
				By(inverses[0], comm_monoid.PowInverseOn.Read(monoid).At(xjm, inverseXjm, r)))
			inverse := a.Have(
				"g·h = x(j)^r·F(x)^(−1)·x(j)^(−r)·F(x) = 1",
				"«g»(j) * «h»(j) = M.one",
				scaledF.Rw(),
				ByArith(
					M,
					valuesInM[2],
					valuesInM[3],
					inverses[1],
					Scaled(a.TermAs[A]("M.inv(«at»(F)) * «at»(F)"), powersCancel),
					powIn.At(xjm, r),
					powIn.At(inverseXjm, r)))
			// The chart lies in the piece with h inverted.
			chartInPiece := a.Have(
				"a member y of the chart with y·F(x)^a = P(x) has h^a·y = P(x/x(j)), in the piece",
				"∀y:A. y ∈ «chart»(F) ⇒ y ∈ ring_away(restrict_ring(field_ring(M), K), «piece»(j), «h»(j))",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yParts := b.Conjuncts(
						b.Assume(),
						"y lies in K",
						"y·F(x)^a is the value of a form of degree r·a")
					ya, P, yForm := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](yParts[1], "a", "P")
					yData := b.Conjuncts(
						yForm,
						"P is a form of degree r·a",
						"y·F(x)^a = P(x)")
					yInM := b.Have(
						"y lies in M",
						"y ∈ M.carrier",
						BySets(yParts[0], KInM))
					scaledP := b.Have(
						"P at the affine coordinates is x(j)^(−r·a)·P(x)",
						"«affine»(P) = monoid_pow(M.mul, M.one, M.inv(x(j)), r * a) * «at»(P)",
						By(
							inclusion,
							yData[0],
							coordinatesInM,
							valuesInM[1],
							homogeneous_polynomial.FormScaling.At(
								coefficients, fieldRing, identity, n, b.TermAs[Nat]("r * a"), x, inverseXj, P)))
					hPower := b.Have(
						"h^a = x(j)^(−r·a)·F(x)^a",
						"monoid_pow(M.mul, M.one, «h»(j), a) = "+
							"monoid_pow(M.mul, M.one, M.inv(x(j)), r * a) * monoid_pow(M.mul, M.one, «at»(F), a)",
						scaledF.Rw(),
						By(
							valuesInM[1],
							valuesInM[2],
							powIn.At(inverseXjm, r),
							comm_monoid.MulPowOn.Read(monoid).AsFact().At(
								b.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(x(j)), r)"), b.TermAs[A]("«at»(F)"), ya),
							comm_monoid.PowPowOn.Read(monoid).AsFact().At(inverseXj, r, ya)))
					value := b.Have(
						"so h^a·y is P at the affine coordinates",
						"monoid_pow(M.mul, M.one, «h»(j), a) * y = «affine»(P)",
						hPower.Rw(),
						scaledP.Rw(),
						yData[1].RwRev(),
						ByArith(M, yInM, powIn.At(inverseXjm, b.TermAs[Nat]("r * a")), powIn.At(fm, ya)))
					inPiece := b.Have(
						"which lies in the piece, P being a polynomial",
						"«affine»(P) ∈ «piece»(j)",
						BySets(homogeneous_polynomial.FormPolynomial.Read(yData[0])))
					b.Show(
						"so y lies in the piece with h inverted",
						By(
							yParts[0],
							value,
							inPiece,
							ring_away.RingAwayMember.At(
								a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), K)"), piece, h, y)))
				}))
			// The piece lies in the chart with g inverted.
			chartRing := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinatesInM, form, projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
				"the chart is a subring of M",
				"holding k")
			powerOnes := a.Conjuncts(
				a.Have(
					"a first power is the element itself",
					"monoid_pow(M.mul, M.one, M.inv(«at»(F)), 1) = M.inv(«at»(F)) ∧ "+
						"monoid_pow(M.mul, M.one, «g»(j), 1) = «g»(j)",
					By(valuesInM[3], powIn.At(xjm, r), comm_monoid.PowOneOn.Read(monoid), comm_ring.MulIn.Read(ring))),
				"the first power of F(x)^(−1) is itself",
				"and so is that of g")
			quotients := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					form,
					positive,
					nonzero,
					ChartQuotientsGenerate.Read(M).At(k, K, n, r, x, F)),
				"the quotients x(i)^r/F(x) lie in the chart",
				"and generate its unit ideal")
			gInChart := a.Have(
				"so g, the quotient at j, lies in the chart",
				"«g»(j) ∈ «chart»(F)",
				BySets(jInRange, quotients[0]))
			away := a.Conjuncts(
				GroupPremises(ring, chartRing[0], gInChart, ring_away.RingAwaySubring.At(fieldRing, chart, g)),
				"the chart lies in itself with g inverted",
				"which is a subring of M",
				"holding the inverses of g")
			ratios := a.Have(
				"g times an affine coordinate x(i)/x(j) is x(i)·x(j)^(r−1)/F(x), in "+
					"the chart, so the affine coordinates lie in the chart with g inverted",
				"∀i:num. i ≤ n ⇒ x(i) * M.inv(x(j)) ∈ ring_away(field_ring(M), «chart»(F), «g»(j))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					iInRange := b.Assume()
					lower := b.TermAs[Nat]("r - 1")
					mixed := b.Conjuncts(
						GroupPremises(
							kSub,
							positive,
							iInRange,
							jInRange,
							coordinatesInM,
							homogeneous_polynomial.MixedMonomialForm.Read(M).At(k, n, r, i, j, x)),
						"X_i·X_j^(r−1) is a form of degree r",
						"evaluating to x(i)·x(j)^(r−1)")
					productForm := b.Have(
						"so it is a form of degree r·1",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    r * 1, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», "+
							"        polynomial_algebra_var(«hilbertCoefficients», i), "+
							"        «varPower»(r - 1)))",
						By(mixed[0], nat_arith.MulOne.At(r)))
					xiInM := b.Have(
						"x(i) lies in M",
						"x(i) ∈ M.carrier",
						By(iInRange, coordinatesInM))
					quotient := b.Have(
						"so x(i)·x(j)^(r−1)/F(x) lies in the chart",
						"x(i) * monoid_pow(M.mul, M.one, x(j), r - 1) * M.inv(«at»(F)) ∈ «chart»(F)",
						By(
							mixed[1],
							powerOnes[0],
							GroupPremises(
								kSub,
								KSub,
								kInK,
								coordinates,
								form,
								nonzero,
								productForm,
								projective_curve.ChartQuotient.Read(M).At(
									k,
									K,
									n,
									r,
									one,
									x,
									F,
									b.TermAs[Fun[Fun[Nat, Nat], A]](
										"polynomial_algebra_mul(«hilbertCoefficients», "+
											"    polynomial_algebra_var(«hilbertCoefficients», i), "+
											"    «varPower»(r - 1))")))))
					exponent := b.Have(
						"r − 1 + 1 = r, r being positive",
						"r - 1 + 1 = r",
						ByArith(positive))
					split := b.Have(
						"so x(j)^r = x(j)^(r−1)·x(j)",
						"monoid_pow(M.mul, M.one, x(j), r) = monoid_pow(M.mul, M.one, x(j), r - 1) * x(j)",
						By(
							exponent,
							valuesInM[0],
							comm_monoid.PowAddOn.Read(monoid).AsFact().At(xj, lower, one),
							comm_monoid.PowOneOn.Read(monoid).AsFact().At(xj)))
					ratioInM := b.Have(
						"x(i)·x(j)^(−1) lies in M",
						"x(i) * M.inv(x(j)) ∈ M.carrier",
						By(xiInM, valuesInM[1], comm_ring.MulIn.Read(ring)))
					product := b.Have(
						"g·x(i)/x(j) = x(i)·x(j)^(r−1)/F(x), x(j)·x(j)^(−1) being one",
						"«g»(j) * (x(i) * M.inv(x(j))) = x(i) * monoid_pow(M.mul, M.one, x(j), r - 1) * M.inv(«at»(F))",
						split.Rw(),
						ByArith(
							M,
							xiInM,
							valuesInM[0],
							valuesInM[1],
							valuesInM[3],
							powIn.At(xjm, lower),
							Scaled(b.TermAs[A]("x(i) * monoid_pow(M.mul, M.one, x(j), r - 1) * M.inv(«at»(F))"), inverses[0])))
					carried := b.Have(
						"so the first power of g carries x(i)/x(j) into the chart",
						"monoid_pow(M.mul, M.one, «g»(j), 1) * (x(i) * M.inv(x(j))) ∈ «chart»(F)",
						powerOnes[1].Rw(),
						product.Rw(),
						By(quotient))
					raised := b.Have(
						"a power of g carries x(i)/x(j) into the chart",
						"∃e:num. monoid_pow(M.mul, M.one, «g»(j), e) * (x(i) * M.inv(x(j))) ∈ «chart»(F)",
						Witness(one),
						By(carried))
					b.Show(
						"so x(i)/x(j) lies in the chart with g inverted",
						By(
							ratioInM,
							raised,
							ring_away.RingAwayMember.At(fieldRing, chart, g, b.TermAs[A]("x(i) * M.inv(x(j))"))))
				}))
			constantsIn := a.Have(
				"k lies in the chart, so in the chart with g inverted",
				"∀c:A. c ∈ k ⇒ c ∈ ring_away(field_ring(M), «chart»(F), «g»(j))",
				BySets(chartRing[1], away[0]))
			pieceInChart := a.Have(
				"so a member of the piece, a polynomial over k at the "+
					"affine coordinates, lies in the chart with g inverted",
				Statement{
					Binders: "∀P:((num → num) → A).",
					Hypotheses: []string{
						"P ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
					},
					Conclusion: "«affine»(P) ∈ ring_away(field_ring(M), «chart»(F), «g»(j))",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[Fun[Fun[Nat, Nat], A]]("P")
					b.Show(
						"evaluation lands in the subring, the chart with g inverted",
						By(
							b.Assume(),
							inclusion,
							away[1],
							constantsIn,
							ratios,
							polynomial_algebra_evaluation.PolynomialAlgebraEvalInSubring.At(
								coefficients,
								fieldRing,
								identity,
								affinePoint,
								variables,
								b.TermAs[Set[A]]("ring_away(field_ring(M), «chart»(F), «g»(j))"),
								P)))
				}))
			chartSubset := a.Have(
				"so the chart lies in the piece with h inverted",
				"«chart»(F) ⊆ ring_away(restrict_ring(field_ring(M), K), «piece»(j), «h»(j))",
				By(chartInPiece, set_basic.SubsetDef))
			pieceSubset := a.Have(
				"and the piece in the chart with g inverted",
				"«piece»(j) ⊆ ring_away(field_ring(M), «chart»(F), «g»(j))",
				image.Rw(),
				By(
					pieceInChart,
					polynomial_algebra.PolynomialAlgebraRingDef,
					set_image.ImageSubsetIff.At(
						affineEval,
						a.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("«polynomials».carrier"),
						a.TermAs[Set[A]]("ring_away(field_ring(M), «chart»(F), «g»(j))"))))
			a.Show(
				"the piece is a subring of M inside K holding h, g·h = 1, and the "+
					"chart and the piece each lie in the other with one element inverted",
				By(subringPiece, pieceInK, hInPiece, inverse, chartSubset, pieceSubset))
		}),
})}

// FormChartIntegrallyClosed — the ring of the open set of a smooth
// projective equation curve where a form F over k, nonzero at the generic
// point, does not vanish — the values P(x)/F(x)^a of the forms P of degree
// r·a — is integrally closed in the generic field: a member z of K integral
// over the chart is, for each nonzero coordinate x(i), integral over the
// affine piece at i with h_i = F(x)/x(i)^r inverted, so h_i^N·z lies in the
// piece, integrally closed, and g_i^L·z in the chart, g_i = x(i)^r/F(x)
// being the inverse of h_i; and z lies in the chart because the g_i
// generate its unit ideal.
var FormChartIntegrallyClosed = formChartIntegrallyClosedThm{family.Add(registry.ProofEntry{
	Name: "FormChartIntegrallyClosed",
	Key:  "prop_b44dd629fdd5f7ea",
	Reading: "F(x) ≠ zero says F is outside the ideal, so the chart is a ring of functions " +
		"and not all of K, which the set-builder gives at F(x) = zero. The chart is covered by " +
		"the coordinate pieces, and its integral closedness is theirs; a coordinate x(i) that is " +
		"zero gives g_i = zero, which carries every z into the chart, 0 < r making x(i)^r zero.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"0 < r",
			"«at»(F) ≠ M.zero",
		},
		Conclusion: "integrally_closed_in(restrict_ring(field_ring(M), «chart»(F)), K)",
		Abbrev: Abbrev{
			{Name: "g", Text: "λi:num. monoid_pow(M.mul, M.one, x(i), r) * M.inv(«at»(F))"},
			{Name: "quotients", Text: "{monoid_pow(M.mul, M.one, x(i), r) * M.inv(«at»(F)) | i:num | i ≤ n}"},
			{Name: "piece", Text: "λj:num. " +
				"    {polynomial_algebra_eval(restrict_ring(field_ring(M), k), " +
				"            field_ring(M), " +
				"            (λa:A. a), " +
				"            (λi:num. x(i) * M.inv(x(j))), " +
				"            P) | " +
				"        P:((num → num) → A) | " +
				"        P ∈ polynomial_algebra(restrict_ring(field_ring(M), k), {i:num | i ≤ n})}"},
			{Name: "h", Text: "λj:num. " +
				"    polynomial_algebra_eval(«hilbertCoefficients», " +
				"        field_ring(M), " +
				"        (λa:A. a), " +
				"        (λi:num. x(i) * M.inv(x(j))), " +
				"        F)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F *Arrow[Fun[Nat, Nat], A],
			closed, curve, KSub, generic, form, positive, nonzero Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			powIn := comm_monoid.PowIn.Read(monoid)
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			chart := a.TermAs[Set[A]]("«chart»(F)")
			quotients := a.TermAs[Set[A]]("«quotients»")
			one := a.TermAs[Nat]("1")
			kSub := a.Have(
				"k is a subfield of M, the curve's field of definition",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			point := a.Conjuncts(
				generic,
				"x is a point of the curve with coordinates in K",
				"whose coordinates generate K over k",
				"at which a form vanishes exactly when it lies in the ideal")
			coordinates := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates generate over k",
				"k ⊆ K",
				By(
					point[1],
					a.Have(
						"k lies in M",
						"k ⊆ M.carrier",
						By(kSub, field.SubfieldSubset)),
					a.Have(
						"and so do the coordinates",
						"{x(i) | i:num | i ≤ n} ⊆ M.carrier",
						BySets(coordinates, KInM)),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			coordinatesInM := a.Have(
				"so the coordinates lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			chartRing := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinatesInM, form, projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
				"the chart is a subring of M",
				"holding k")
			ringC := a.Have(
				"so it is a ring under the operations of M",
				"comm_ring_on(restrict_ring(field_ring(M), «chart»(F)))",
				By(chartRing[0], comm_ring.SubringRingOn.Read(ring).At(chart)))
			generated := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					form,
					positive,
					nonzero,
					ChartQuotientsGenerate.Read(M).At(k, K, n, r, x, F)),
				"the quotients g_i lie in the chart",
				"and generate its unit ideal")
			atX := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			inverseF := a.Have(
				"F(x) lies in K, so its inverse lies in M",
				"M.inv(«at»(F)) ∈ M.carrier",
				BySets(homogeneous_polynomial.FormPolynomial.Read(form), atX[1], KInM, field.InvIn.Read(M)))
			a.Show(
				"a member z of K integral over the chart lies in it",
				Simp(Fwd(integral_element.IntegrallyClosedDef)),
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					zParts := b.Conjuncts(
						b.Assume(),
						"z lies in K",
						"and is integral over the chart")
					zInM := b.Have(
						"z lies in M",
						"z ∈ M.carrier",
						BySets(zParts[0], KInM))
					local := b.Have(
						"a power of each g_i carries z into the chart",
						"∀i:num. i ≤ n ⇒ ∃N:num. monoid_pow(M.mul, M.one, «g»(i), N) * z ∈ «chart»(F)",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							iInRange := c.Assume()
							xiInM := c.Have(
								"x(i) lies in M",
								"x(i) ∈ M.carrier",
								By(iInRange, coordinatesInM))
							c.Cases(c.TermAs[Bool]("x(i) = M.zero"))
							c.When(
								"x(i) is zero: then g_i is zero, and carries z to zero",
								func(d *Argument, zero Fact) {
									lower := d.TermAs[Nat]("r - 1")
									xi := d.TermAs[A]("x(i)")
									split := d.Have(
										"x(i)^r = x(i)^(r−1)·x(i), r being positive",
										"monoid_pow(M.mul, M.one, x(i), r) = monoid_pow(M.mul, M.one, x(i), r - 1) * x(i)",
										By(
											d.Have(
												"r − 1 + 1 = r",
												"r - 1 + 1 = r",
												ByArith(positive)),
											xiInM,
											comm_monoid.PowAddOn.Read(monoid).AsFact().At(xi, lower, one),
											comm_monoid.PowOneOn.Read(monoid).AsFact().At(xi)))
									quotientZero := d.Have(
										"so g_i is zero",
										"«g»(i) = M.zero",
										split.Rw(),
										zero.Rw(),
										ByArith(
											M,
											inverseF,
											powIn.At(d.MemberOf[on.M](d.TermAs[A]("M.zero"), comm_ring.ZeroIn.Read(ring)), lower)))
									powerOne := d.Have(
										"the first power of zero is zero",
										"monoid_pow(M.mul, M.one, M.zero, 1) = M.zero",
										By(
											comm_ring.ZeroIn.Read(ring),
											comm_monoid.PowOneOn.Read(monoid).AsFact().At(d.TermAs[A]("M.zero"))))
									vanishing := d.Have(
										"and carries z to zero",
										"monoid_pow(M.mul, M.one, «g»(i), 1) * z = M.zero",
										quotientZero.Rw(),
										powerOne.Rw(),
										ByArith(M, zInM))
									d.Show(
										"the first power carries z to zero, in the chart",
										Witness(one),
										vanishing.Rw(),
										By(comm_ring.SubringZero.Read(chartRing[0])))
								})
							c.Otherwise(
								"x(i) is not zero: its affine piece is integrally closed, and "+
									"it and the chart lie each in the other with one element inverted",
								func(d *Argument, xiNonzero Fact) {
									away := d.Conjuncts(
										GroupPremises(
											kSub,
											KSub,
											kInK,
											coordinates,
											form,
											positive,
											nonzero,
											iInRange,
											xiNonzero,
											ChartPieceAways.Read(M).At(k, K, n, r, i, x, F)),
										"the piece is a subring of M",
										"inside K",
										"holding h",
										"g·h = 1",
										"the chart lies in the piece with h inverted",
										"the piece lies in the chart with g inverted")
									piece := d.TermAs[Set[A]]("«piece»(i)")
									h := d.TermAs[A]("«h»(i)")
									g := d.TermAs[A]("«g»(i)")
									kRing := d.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), K)")
									integral := d.Have(
										"z is integral over the piece with h inverted, which holds the chart",
										"integral_over(restrict_ring(field_ring(M), "+
											"        ring_away(restrict_ring(field_ring(M), K), «piece»(i), «h»(i))), "+
											"    z)",
										By(
											zParts[1],
											away[4],
											integral_element.IntegralOverMono.At(
												fieldRing,
												chart,
												d.TermAs[Set[A]]("ring_away(restrict_ring(field_ring(M), K), «piece»(i), «h»(i))"),
												z)))
									closureMember := d.Have(
										"so z lies in the integral closure of the piece with h inverted",
										"z ∈ "+
											"integral_closure(restrict_ring(field_ring(M), "+
											"        ring_away(restrict_ring(field_ring(M), K), «piece»(i), «h»(i))), "+
											"    K)",
										BySets(zParts[0], integral, integral_element.IntegralClosureDef))
									closure := d.Have(
										"which is the closure of the piece with h inverted",
										"z ∈ "+
											"ring_away(restrict_ring(field_ring(M), K), "+
											"    integral_closure(restrict_ring(field_ring(M), «piece»(i)), K), "+
											"    «h»(i))",
										By(
											closureMember,
											away[0],
											KSub,
											away[1],
											away[2],
											ring_away.IntegralClosureAway.Read(M).At(piece, K, h)))
									N, cleared := d.ObtainAs[Nat](
										"so a power h^N carries z into the closure of the piece",
										"∃N:num. "+
											"    monoid_pow(M.mul, M.one, «h»(i), N) * z ∈ "+
											"    integral_closure(restrict_ring(field_ring(M), «piece»(i)), K)",
										By(
											closure,
											ring_away.RingAwayMember.At(
												kRing, d.TermAs[Set[A]]("integral_closure(restrict_ring(field_ring(M), «piece»(i)), K)"), h, z)),
										Named("N"))
									pieceClosed := d.Unfolded(
										d.Have(
											"the piece is integrally closed in K, the curve being smooth",
											"integrally_closed_in(restrict_ring(field_ring(M), «piece»(i)), K)",
											By(
												closed,
												curve,
												KSub,
												point[0],
												point[1],
												iInRange,
												xiNonzero,
												projective_affine_piece.AffinePiecesIntegrallyClosed.Read(M).At(k, K, n, i, E, x))),
										integral_element.IntegrallyClosedDef)
									closureParts := d.Conjuncts(
										d.Have(
											"h^N·z lies in K and is integral over the piece",
											"monoid_pow(M.mul, M.one, «h»(i), N) * z ∈ K ∧ "+
												"integral_over(restrict_ring(field_ring(M), «piece»(i)), monoid_pow(M.mul, M.one, «h»(i), N) * z)",
											BySets(cleared, integral_element.IntegralClosureDef)),
										"h^N·z lies in K",
										"and is integral over the piece")
									inPiece := d.Have(
										"which is the piece itself, integrally closed in K",
										"monoid_pow(M.mul, M.one, «h»(i), N) * z ∈ «piece»(i)",
										By(
											closureParts[0],
											closureParts[1],
											pieceClosed.At(d.TermAs[A]("monoid_pow(M.mul, M.one, «h»(i), N) * z"))))
									L, raised := d.ObtainAs[Nat](
										"the piece lies in the chart with g inverted, so a power g^L carries h^N·z into the chart",
										"∃L:num. "+
											"    monoid_pow(M.mul, M.one, «g»(i), L) * (monoid_pow(M.mul, M.one, «h»(i), N) * z) ∈ «chart»(F)",
										By(
											inPiece,
											away[5],
											set_basic.SubsetDef,
											ring_away.RingAwayMember.At(
												fieldRing, chart, g, d.TermAs[A]("monoid_pow(M.mul, M.one, «h»(i), N) * z"))),
										Named("L"))
									gInChart := d.Have(
										"g lies in the chart",
										"«g»(i) ∈ «chart»(F)",
										BySets(generated[0], iInRange))
									members := d.Conjuncts(
										d.Have(
											"g and h lie in M",
											"«g»(i) ∈ M.carrier ∧ «h»(i) ∈ M.carrier",
											BySets(away[1], away[2], KInM, gInChart)),
										"g lies in M",
										"and so does h")
									gm, hm := d.MemberOf[on.M](g, members[0]), d.MemberOf[on.M](h, members[1])
									cancel := d.Have(
										"g^N·h^N = 1, g·h being one",
										"monoid_pow(M.mul, M.one, «g»(i), N) * monoid_pow(M.mul, M.one, «h»(i), N) = M.one",
										By(away[3], comm_monoid.PowInverseOn.Read(monoid).At(gm, hm, N)))
									product := d.Have(
										"so g^N times g^L·h^N·z is g^L·z",
										"monoid_pow(M.mul, M.one, «g»(i), N) * "+
											"(monoid_pow(M.mul, M.one, «g»(i), L) * (monoid_pow(M.mul, M.one, «h»(i), N) * z)) = "+
											"monoid_pow(M.mul, M.one, «g»(i), L) * z",
										ByArith(
											M,
											zInM,
											powIn.At(gm, N),
											powIn.At(gm, L),
											powIn.At(hm, N),
											Scaled(d.TermAs[A]("monoid_pow(M.mul, M.one, «g»(i), L) * z"), cancel)))
									gPower := d.Have(
										"g^N lies in the chart, g lying in it",
										"monoid_pow(M.mul, M.one, «g»(i), N) ∈ «chart»(F)",
										By(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringC)).At(
											d.MemberOf[on.Any](g, gInChart), N)))
									d.Show(
										"so the power g^L carries z into the chart",
										Witness(L),
										product.RwRev(),
										By(gPower, raised, comm_ring.SubringMul.Read(chartRing[0])))
								})
						}))
					carried := b.Have(
						"so a power of each quotient carries z into the chart",
						"∀g:A. g ∈ «quotients» ⇒ ∃N:num. monoid_pow(M.mul, M.one, g, N) * z ∈ «chart»(F)",
						BySets(local))
					b.Show(
						"and the quotients generate the unit ideal of the chart, so z lies in it",
						By(
							chartRing[0],
							generated[0],
							generated[1],
							carried,
							ring_away.AwayCoverMember.Read(M).At(chart, quotients, b.MemberOf[on.M](z, zInM))))
				}))
		}),
})}

// ChartInOtherAway — the chart of F lies in the chart of G with F(x)/G(x)
// inverted: a member y with y·F(x)^a = P(x) has (F(x)/G(x))^a·y·G(x)^a =
// y·F(x)^a = P(x), so (F(x)/G(x))^a·y lies in the chart of G, by the same
// form P.
var ChartInOtherAway = chartInOtherAwayThm{family.Add(registry.ProofEntry{
	Name: "ChartInOtherAway",
	Key:  "prop_47fe840d797ce30a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r:num. ∀x:(num → A). ∀F G:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"«at»(G) ≠ M.zero",
		},
		Conclusion: "«chart»(F) ⊆ ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G)))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, kInK, coordinates, fForm, gForm, nonzero Fact,
		) {
			evaluation := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			values := a.Have(
				"F(x) and G(x) lie in K",
				"«at»(F) ∈ K ∧ «at»(G) ∈ K",
				By(
					homogeneous_polynomial.FormPolynomial.Read(fForm),
					homogeneous_polynomial.FormPolynomial.Read(gForm),
					evaluation[1]))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			inM := a.Have(
				"F(x), G(x) and the inverse of G(x) lie in M",
				"«at»(F) ∈ M.carrier ∧ «at»(G) ∈ M.carrier ∧ M.inv(«at»(G)) ∈ M.carrier",
				BySets(values, KInM, field.InvIn.Read(M)))
			members := a.Conjuncts(
				inM,
				"F(x) lies in M",
				"so does G(x)",
				"and its inverse")
			cancel := a.Have(
				"G(x)^(−1)·G(x) = 1, G(x) being nonzero",
				"M.inv(«at»(G)) * «at»(G) = M.one",
				By(nonzero, members[1], field.MulLeftInverseOn.Read(M)))
			fieldOps := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			f, g, gInverse := a.TermAs[A]("«at»(F)"), a.TermAs[A]("«at»(G)"), a.TermAs[A]("M.inv(«at»(G))")
			fm, gm, gInverseM :=
				a.MemberOf[on.M](f, members[0]),
				a.MemberOf[on.M](g, members[1]),
				a.MemberOf[on.M](gInverse, members[2])
			ratio := a.TermAs[A]("«at»(F) * M.inv(«at»(G))")
			chartG := a.TermAs[Set[A]]("«chart»(G)")
			monoid := comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))
			ratioInK := a.Have(
				"F(x)/G(x) lies in K, a subfield",
				"«at»(F) * M.inv(«at»(G)) ∈ K",
				By(
					KSub,
					values,
					field.SubfieldInv.At(fieldOps, K, g),
					field.SubfieldMul.At(fieldOps, K, f, gInverse)))
			shift := a.Have(
				"a power of F(x)/G(x) carries each member of the chart of F into the chart of G",
				"∀y:A. y ∈ «chart»(F) ⇒ y ∈ ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G)))",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					member := b.Conjuncts(
						b.Assume(),
						"y lies in K",
						"y·F(x)^a is the value of a form of degree r·a")
					d, _, rep := b.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](member[1], "a", "P")
					form := b.Conjuncts(
						rep,
						"P is a form of degree r·a",
						"y·F(x)^a = P(x)")
					yInM := b.Have(
						"y lies in M",
						"y ∈ M.carrier",
						BySets(member[0], KInM))
					powers := b.Have(
						"G(x)^(−a)·G(x)^a = 1",
						"monoid_pow(M.mul, M.one, M.inv(«at»(G)), a) * monoid_pow(M.mul, M.one, «at»(G), a) = M.one",
						By(cancel, comm_monoid.PowInverseOn.Read(monoid).At(gInverseM, gm, d)))
					value := b.Have(
						"(F(x)/G(x))^a·y·G(x)^a = y·F(x)^a",
						"monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), a) * "+
							"y * "+
							"monoid_pow(M.mul, M.one, «at»(G), a) = "+
							"y * monoid_pow(M.mul, M.one, «at»(F), a)",
						ByArith(
							M,
							inM,
							yInM,
							Scaled(b.TermAs[A]("y * monoid_pow(M.mul, M.one, «at»(F), a)"), powers),
							Scaled(
								b.TermAs[A]("y * monoid_pow(M.mul, M.one, «at»(G), a)"),
								comm_monoid.MulPowOn.Read(monoid).AsFact().At(f, gInverse, d)),
							comm_monoid.PowIn.Read(monoid).At(fm, d),
							comm_monoid.PowIn.Read(monoid).At(gm, d),
							comm_monoid.PowIn.Read(monoid).At(gInverseM, d),
							comm_monoid.PowIn.Read(monoid).At(comm_ring.MulIn.Read(field.RingOn.Read(M)).At(fm, gInverseM), d)))
					inK := b.Have(
						"(F(x)/G(x))^a·y lies in K",
						"monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), a) * y ∈ K",
						By(
							KSub,
							ratioInK,
							member[0],
							field.SubfieldPowerIn.Read(M).AsFact().At(K, ratio, d),
							field.SubfieldMul.At(
								fieldOps, K, b.TermAs[A]("monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), a)"), y)))
					carried := b.Have(
						"so some power of F(x)/G(x) carries y into the chart of G, by the same form P",
						"∃c:num. monoid_pow(M.mul, M.one, «at»(F) * M.inv(«at»(G)), c) * y ∈ «chart»(G)",
						BySets(value, inK, form[0], form[1]))
					b.Show(
						"so y lies in the chart of G with F(x)/G(x) inverted",
						By(carried, yInM, ring_away.RingAwayMember.At(fieldRing, chartG, ratio, y)))
				}))
			a.Show(
				"so the chart of F lies there",
				BySets(shift))
		}),
})}

// ParameterInChart — t = G(x)/F(x) lies in the chart of F: G, a form of
// degree r = r·1, has the value G(x) = t·F(x)¹.
var ParameterInChart = parameterInChartThm{family.Add(registry.ProofEntry{
	Name: "ParameterInChart",
	Key:  "prop_d2706ddcce821524",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r:num. ∀x:(num → A). ∀F G:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"«at»(F) ≠ M.zero",
		},
		Conclusion: "«parameter» ∈ «chart»(F)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, kInK, coordinates, fForm, gForm, nonzero Fact,
		) {
			evaluation := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			degree := a.Have(
				"G is a form of degree r·1",
				"homogeneous_polynomial(«hilbertCoefficients», n, r * 1, G)",
				a.Have(
					"r·1 = r",
					"r * 1 = r",
					ByArith()).Rw(),
				By(gForm))
			inverse := a.Have(
				"F(x) lies in K, so its inverse lies in M",
				"M.inv(«at»(F)) ∈ M.carrier",
				BySets(
					homogeneous_polynomial.FormPolynomial.Read(fForm),
					evaluation[1],
					KSub,
					field.SubfieldSubset,
					field.InvIn.Read(M)))
			a.Show(
				"so t, the value G(x) of the form G of degree r·1 over the first power of F(x), lies in the chart",
				By(
					GroupPremises(
						kSub,
						KSub,
						kInK,
						coordinates,
						fForm,
						nonzero,
						degree,
						projective_curve.ChartQuotient.Read(M).At(k, K, n, r, a.TermAs[Nat]("1"), x, F, G)),
					inverse,
					comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(M)))))
		}),
})}

// ParameterInverse — the inverse of t = G(x)/F(x) is F(x)/G(x): F(x) and
// G(x) lie in M, and the inverse of a quotient of members is the quotient
// reversed (field.InvDivOn).
var ParameterInverse = parameterInverseThm{family.Add(registry.ProofEntry{
	Name: "ParameterInverse",
	Key:  "prop_dd3c8d3d7a61436d",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r:num. ∀x:(num → A). ∀F G:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
		},
		Conclusion: "M.inv(«parameter») = «at»(F) * M.inv(«at»(G))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, kInK, coordinates, fForm, gForm Fact,
		) {
			evaluation := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			values := a.Conjuncts(
				a.Have(
					"F(x) and G(x) lie in K, so in M",
					"«at»(F) ∈ M.carrier ∧ «at»(G) ∈ M.carrier",
					BySets(
						homogeneous_polynomial.FormPolynomial.Read(fForm),
						homogeneous_polynomial.FormPolynomial.Read(gForm),
						evaluation[1],
						KSub,
						field.SubfieldSubset)),
				"F(x) lies in M",
				"so does G(x)")
			f, g :=
				a.MemberOf[on.M](a.TermAs[A]("«at»(F)"), values[0]),
				a.MemberOf[on.M](a.TermAs[A]("«at»(G)"), values[1])
			a.Show(
				"the inverse of the quotient G(x)/F(x) is the quotient reversed",
				By(field.InvDivOn.Read(M).At(g, f), field.DivMulInvOn.Read(M)))
		}),
})}

// ChartsBiaffine — glued along the overlap, the charts of F and G are a
// biaffine datum with t = G(x)/F(x) and its inverse F(x)/G(x)
// (ParameterInverse): t lies in the chart of F and 1/t in the chart of G
// (ParameterInChart, read both ways), each chart lies in the other with
// its element inverted (ChartInOtherAway, read both ways), so the least
// ring holding the chart of F and 1/t and the least ring holding the chart
// of G and t contain each other: the overlap A₀[1/t] is A₁[t].
var ChartsBiaffine = chartsBiaffineThm{family.Add(registry.ProofEntry{
	Name: "ChartsBiaffine",
	Key:  "prop_6c738b4ed41589f5",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r:num. ∀x:(num → A). ∀F G:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"k ⊆ K",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"«at»(F) ≠ M.zero",
			"«at»(G) ≠ M.zero",
		},
		Conclusion: "biaffine(restrict_ring(field_ring(M), «overlap»), " +
			"    «chart»(F), " +
			"    «chart»(G), " +
			"    «parameter», " +
			"    M.inv(«parameter»))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, kInK, coordinates, fForm, gForm, fNonzero, gNonzero Fact,
		) {
			ring := field.RingOn.Read(M)
			fieldOps := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			f, g := a.TermAs[A]("«at»(F)"), a.TermAs[A]("«at»(G)")
			t, u := a.TermAs[A]("«parameter»"), a.TermAs[A]("«at»(F) * M.inv(«at»(G))")
			chartF, chartG := a.TermAs[Set[A]]("«chart»(F)"), a.TermAs[Set[A]]("«chart»(G)")
			away0 := a.TermAs[Set[A]]("ring_away(field_ring(M), «chart»(F), «parameter»)")
			away1 := a.TermAs[Set[A]]("ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G)))")
			evaluation := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			values := a.Have(
				"F(x) and G(x) lie in K",
				"«at»(F) ∈ K ∧ «at»(G) ∈ K",
				By(
					homogeneous_polynomial.FormPolynomial.Read(fForm),
					homogeneous_polynomial.FormPolynomial.Read(gForm),
					evaluation[1]))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			inM := a.Have(
				"F(x), G(x) and their inverses lie in M",
				"«at»(F) ∈ M.carrier ∧ "+
					"«at»(G) ∈ M.carrier ∧ "+
					"M.inv(«at»(F)) ∈ M.carrier ∧ "+
					"M.inv(«at»(G)) ∈ M.carrier",
				BySets(values, KInM, field.InvIn.Read(M)))
			coordinatesInM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))

			// The charts, t in the first and 1/t in the second.
			chartParts := a.Conjuncts(
				a.Have(
					"the charts of F and G are subrings of M",
					"subring(field_ring(M), «chart»(F)) ∧ subring(field_ring(M), «chart»(G))",
					By(
						GroupPremises(
							kSub,
							KSub,
							kInK,
							coordinatesInM,
							fForm,
							projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
						GroupPremises(
							kSub,
							KSub,
							kInK,
							coordinatesInM,
							gForm,
							projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, G)))),
				"the chart of F is a subring of M",
				"so is the chart of G")
			units := a.Have(
				"t lies in the chart of F and F(x)/G(x) in the chart of G",
				"«parameter» ∈ «chart»(F) ∧ «at»(F) * M.inv(«at»(G)) ∈ «chart»(G)",
				By(
					GroupPremises(
						kSub,
						KSub,
						kInK,
						coordinates,
						fForm,
						gForm,
						fNonzero,
						ParameterInChart.Read(M).At(k, K, n, r, x, F, G)),
					GroupPremises(
						kSub,
						KSub,
						kInK,
						coordinates,
						gForm,
						fForm,
						gNonzero,
						ParameterInChart.Read(M).At(k, K, n, r, x, G, F))))
			members := a.Conjuncts(
				inM,
				"F(x) lies in M",
				"so does G(x)",
				"the inverse of F(x) lies in M",
				"and so does that of G(x)")
			fInverse, gInverse := a.TermAs[A]("M.inv(«at»(F))"), a.TermAs[A]("M.inv(«at»(G))")
			ratios := a.Have(
				"t and F(x)/G(x) lie in M",
				"«parameter» ∈ M.carrier ∧ «at»(F) * M.inv(«at»(G)) ∈ M.carrier",
				By(inM, comm_ring.MulIn.Read(ring)))
			ratioParts := a.Conjuncts(
				ratios,
				"t lies in M",
				"so does F(x)/G(x)")
			tm := a.MemberOf[on.M](t, ratioParts[0])
			um := a.MemberOf[on.M](u, ratioParts[1])
			cancelParts := a.Conjuncts(
				a.Have(
					"F(x)^(−1)·F(x) = 1 and G(x)^(−1)·G(x) = 1, neither being zero",
					"M.inv(«at»(F)) * «at»(F) = M.one ∧ M.inv(«at»(G)) * «at»(G) = M.one",
					By(fNonzero, gNonzero, members[0], members[1], field.MulLeftInverseOn.Read(M))),
				"F(x)^(−1)·F(x) = 1",
				"G(x)^(−1)·G(x) = 1")
			product := a.Have(
				"t·F(x)/G(x) = 1",
				"«parameter» * («at»(F) * M.inv(«at»(G))) = M.one",
				ByArith(M, inM, Scaled(a.TermAs[A]("«at»(G) * M.inv(«at»(G))"), cancelParts[0]), cancelParts[1]))
			inverseOfT := a.Have(
				"so F(x)/G(x) is the inverse of t",
				"M.inv(«parameter») = «at»(F) * M.inv(«at»(G))",
				By(GroupPremises(
					kSub, KSub, kInK, coordinates, fForm, gForm, ParameterInverse.Read(M).At(k, K, n, r, x, F, G))))
			inverseOfU := a.Have(
				"and t the inverse of F(x)/G(x)",
				"M.inv(«at»(F) * M.inv(«at»(G))) = «parameter»",
				inverseOfT.RwRev(),
				By(ratios, field.InvInvOn.Read(M)))
			nonzeroParts := a.Conjuncts(
				a.Have(
					"neither t nor F(x)/G(x) is zero",
					"«parameter» ≠ M.zero ∧ «at»(F) * M.inv(«at»(G)) ≠ M.zero",
					By(inM, fNonzero, gNonzero, field.InvEqZeroOn.Read(M), field.MulEqZeroOn.Read(M))),
				"t is not zero",
				"nor is F(x)/G(x)")

			// The two overlaps, A₀ with t inverted and A₁ with 1/t inverted.
			unitParts := a.Conjuncts(
				units,
				"t lies in the chart of F",
				"F(x)/G(x) lies in the chart of G")
			parts0 := a.Conjuncts(
				a.Have(
					"A₀[1/t] is a subring of M holding A₀ and 1/t",
					"«chart»(F) ⊆ ring_away(field_ring(M), «chart»(F), «parameter») ∧ "+
						"subring(field_ring(M), ring_away(field_ring(M), «chart»(F), «parameter»)) ∧ "+
						"«at»(F) * M.inv(«at»(G)) ∈ ring_away(field_ring(M), «chart»(F), «parameter»)",
					By(
						ring,
						chartParts[0],
						unitParts[0],
						ratios,
						product,
						ring_away.RingAwaySubring.At(fieldRing, chartF, t))),
				"A₀ lies in A₀[1/t]",
				"A₀[1/t] is a subring of M",
				"1/t lies in A₀[1/t]")
			parts1 := a.Conjuncts(
				a.Have(
					"A₁[t] is a subring of M holding A₁ and t",
					"«chart»(G) ⊆ ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G))) ∧ "+
						"subring(field_ring(M), ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G)))) ∧ "+
						"«parameter» ∈ ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G)))",
					By(
						ring,
						chartParts[1],
						unitParts[1],
						ratios,
						product,
						comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)),
						ring_away.RingAwaySubring.At(fieldRing, chartG, u))),
				"A₁ lies in A₁[t]",
				"A₁[t] is a subring of M",
				"t lies in A₁[t]")
			intoAway1 := a.Have(
				"the chart of F lies in A₁[t]",
				"«chart»(F) ⊆ ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G)))",
				By(GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					fForm,
					gForm,
					gNonzero,
					ChartInOtherAway.Read(M).At(k, K, n, r, x, F, G))))
			intoAway0 := a.Have(
				"and the chart of G in A₀[1/t]",
				"«chart»(G) ⊆ ring_away(field_ring(M), «chart»(F), «parameter»)",
				By(GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					gForm,
					fForm,
					fNonzero,
					ChartInOtherAway.Read(M).At(k, K, n, r, x, G, F))))
			inverseParts := a.Conjuncts(
				a.Have(
					"1/t lies in A₁[t] and the inverse of F(x)/G(x), t itself, in A₀[1/t]",
					"M.inv(«parameter») ∈ ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G))) ∧ "+
						"M.inv(«at»(F) * M.inv(«at»(G))) ∈ ring_away(field_ring(M), «chart»(F), «parameter»)",
					inverseOfT.Rw(),
					inverseOfU.Rw(),
					BySets(parts0[0], parts1[0], unitParts[0], unitParts[1])),
				"1/t lies in A₁[t]",
				"t lies in A₀[1/t]")
			forward := a.Have(
				"so A₀[1/t] ⊆ A₁[t], A₀[1/t] being the least ring holding A₀ and 1/t",
				"ring_away(field_ring(M), «chart»(F), «parameter») ⊆ "+
					"ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G)))",
				By(
					parts1[1],
					intoAway1,
					nonzeroParts[0],
					inverseParts[0],
					ring_away.RingAwayLeast.Read(M).At(chartF, away1, tm)))
			backward := a.Have(
				"and A₁[t] ⊆ A₀[1/t], A₁[t] being the least ring holding A₁ and t",
				"ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G))) ⊆ "+
					"ring_away(field_ring(M), «chart»(F), «parameter»)",
				By(
					parts0[1],
					intoAway0,
					nonzeroParts[1],
					inverseParts[1],
					ring_away.RingAwayLeast.Read(M).At(chartG, away0, um)))
			glued := a.Have(
				"the overlaps agree: A₀[1/t] = A₁[t]",
				"ring_away(field_ring(M), «chart»(F), «parameter») = "+
					"ring_away(field_ring(M), «chart»(G), «at»(F) * M.inv(«at»(G)))",
				By(forward, backward, set_order.SubsetAntisym))

			// The overlap read in K is A₀[1/t], and inside its ring each chart inverts its element.
			KSubring := a.Have(
				"K is a subring of M",
				"subring(field_ring(M), K)",
				By(KSub, field.SubfieldSubring.Read(M)))
			chartInK := a.Have(
				"the chart of F, t and F(x)/G(x) lie in K",
				"«chart»(F) ⊆ K ∧ «parameter» ∈ K ∧ «at»(F) * M.inv(«at»(G)) ∈ K",
				By(
					values,
					KSub,
					field.SubfieldInv.At(fieldOps, K, f),
					field.SubfieldInv.At(fieldOps, K, g),
					field.SubfieldMul.At(fieldOps, K, g, fInverse),
					field.SubfieldMul.At(fieldOps, K, f, gInverse),
					set_basic.SubsetDef))
			overlapIs := a.Have(
				"the overlap, A₀ with t inverted inside K, is A₀[1/t]",
				"«overlap» = ring_away(field_ring(M), «chart»(F), «parameter»)",
				By(ring, KSubring, chartInK, product, ring_away.RingAwayInSubring.At(fieldRing, K, chartF, t, u)))
			subrings := a.Have(
				"each chart, a subring of M inside A₀[1/t], is a subring of its ring",
				"subring(restrict_ring(field_ring(M), ring_away(field_ring(M), «chart»(F), «parameter»)), "+
					"    «chart»(F)) ∧ "+
					"subring(restrict_ring(field_ring(M), ring_away(field_ring(M), «chart»(F), «parameter»)), "+
					"    «chart»(G))",
				By(chartParts[0], chartParts[1], parts0[0], intoAway0, comm_ring.SubringRestrict))
			inOverlap := a.Have(
				"t and F(x)/G(x) lie in A₀[1/t], t through the chart of F",
				"«parameter» ∈ ring_away(field_ring(M), «chart»(F), «parameter») ∧ "+
					"«at»(F) * M.inv(«at»(G)) ∈ ring_away(field_ring(M), «chart»(F), «parameter»)",
				BySets(parts0[0], parts0[2], unitParts[0]))
			swapped := a.Have(
				"F(x)/G(x)·t = 1",
				"«at»(F) * M.inv(«at»(G)) * «parameter» = M.one",
				ByArith(M, inM, product))
			awayFromT := a.Have(
				"computed in the ring of A₀[1/t], A₀ with t inverted is A₀[1/t]",
				"ring_away(restrict_ring(field_ring(M), ring_away(field_ring(M), «chart»(F), «parameter»)), "+
					"    «chart»(F), "+
					"    «parameter») = "+
					"ring_away(field_ring(M), «chart»(F), «parameter»)",
				By(
					ring,
					parts0[1],
					parts0[0],
					inOverlap,
					product,
					ring_away.RingAwayInSubring.At(fieldRing, away0, chartF, t, u)))
			awayFromU := a.Have(
				"and A₁ with F(x)/G(x) inverted is A₁[t], which is A₀[1/t]",
				"ring_away(restrict_ring(field_ring(M), ring_away(field_ring(M), «chart»(F), «parameter»)), "+
					"    «chart»(G), "+
					"    «at»(F) * M.inv(«at»(G))) = "+
					"ring_away(field_ring(M), «chart»(F), «parameter»)",
				By(
					ring,
					parts0[1],
					intoAway0,
					inOverlap,
					swapped,
					glued,
					ring_away.RingAwayInSubring.At(fieldRing, away0, chartG, u, t)))
			overlapRing := a.Have(
				"A₀[1/t] is a ring under M's operations",
				"comm_ring_on(restrict_ring(field_ring(M), ring_away(field_ring(M), «chart»(F), «parameter»)))",
				By(parts0[1], comm_ring.SubringRingOn.Read(ring).At(away0)))
			a.Show(
				"so the ring of the overlap, the two charts, t and 1/t form a biaffine datum",
				overlapIs.Rw(),
				inverseOfT.Rw(),
				By(
					overlapRing,
					subrings,
					units,
					product,
					awayFromT,
					awayFromU,
					lattice_pair.BiaffineDef.At(
						a.TermAs[module_record.RingOps[A]](
							"restrict_ring(field_ring(M), ring_away(field_ring(M), «chart»(F), «parameter»))"),
						chartF,
						chartG,
						t,
						u)))
		}),
})}

// ChartFractionField — K is the field of fractions of the chart of F. With
// x(j) = one, K is the field of fractions of the affine piece where x(j) is
// not zero (projective_affine_piece.AffinePieceFractionField), and the piece lies in the chart with
// g = x(j)^r/F(x) inverted (ChartPieceAways): powers gᵐ and gˡ carry the
// numerator p and the denominator q of a fraction p/q of the piece into the
// chart, and multiplying both by gᵐ·gˡ gives a fraction of the chart whose
// denominator stays nonzero, g being a unit.
var ChartFractionField = chartFractionFieldThm{family.Add(registry.ProofEntry{
	Name: "ChartFractionField",
	Key:  "prop_f45d0cd158d66416",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K:set(A). ∀n r:num. ∀x:(num → A). ∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"∀i:num. i ≤ n ⇒ x(i) ∈ K",
			"∃i:num. i ≤ n ∧ x(i) = M.one",
			"field_adjoin(M, k, {x(i) | i:num | i ≤ n}) = K",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"0 < r",
			"«at»(F) ≠ M.zero",
		},
		Conclusion: "fraction_field_carrier(restrict_ring(field_ring(M), K), «chart»(F))",
		Abbrev: Abbrev{
			{Name: "piece", Text: "λj:num. " +
				"    {polynomial_algebra_eval(restrict_ring(field_ring(M), k), " +
				"            field_ring(M), " +
				"            (λa:A. a), " +
				"            (λi:num. x(i) * M.inv(x(j))), " +
				"            P) | " +
				"        P:((num → num) → A) | " +
				"        P ∈ polynomial_algebra(restrict_ring(field_ring(M), k), {i:num | i ≤ n})}"},
			{Name: "g", Text: "λi:num. monoid_pow(M.mul, M.one, x(i), r) * M.inv(«at»(F))"},
			{Name: "h", Text: "λj:num. " +
				"    polynomial_algebra_eval(«hilbertCoefficients», " +
				"        field_ring(M), " +
				"        (λa:A. a), " +
				"        (λi:num. x(i) * M.inv(x(j))), " +
				"        F)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			x *Arrow[Nat, A],
			F *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, coordinates, normalized, generated, fForm, positive, nonzero Fact,
		) {
			ring := field.RingOn.Read(M)
			ops := a.TermAs[FieldOps[A]]("M")
			kRing := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), K)")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			chartF := a.TermAs[Set[A]]("«chart»(F)")
			j, xjIsOne := a.UnpackAs[Nat](a.Have(
				"some coordinate x(j) is one, so not zero",
				"∃j:num. j ≤ n ∧ x(j) = M.one ∧ x(j) ≠ M.zero",
				By(normalized, field.OneNotZeroOn.Read(M))), "j")
			xjParts := a.Conjuncts(
				xjIsOne,
				"j indexes a coordinate",
				"x(j) = one",
				"x(j) is not zero")
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field its coordinates generate over k",
				"k ⊆ K",
				BySets(
					generated,
					kSub,
					coordinates,
					KInM,
					field.SubfieldSubset.At(ops, k),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			coordinatesInM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			xjNonzero := xjParts[2]

			// The affine piece where x(j) is not zero, and its place against the chart.
			aways := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					fForm,
					positive,
					nonzero,
					xjParts[0],
					xjNonzero,
					ChartPieceAways.Read(M).At(k, K, n, r, j, x, F)),
				"the piece is a subring of M",
				"inside K",
				"holding h = F(x)/x(j)^r",
				"inverse to g = x(j)^r/F(x)",
				"the chart lies in the piece with h inverted",
				"the piece lies in the chart with g inverted")
			fractions := a.Have(
				"each member of K is a fraction of the piece, K being its field of fractions",
				"∀z:A. z ∈ K ⇒ ∃p q:A. p ∈ «piece»(j) ∧ q ∈ «piece»(j) ∧ q ≠ M.zero ∧ z * q = p",
				By(
					GroupPremises(
						kSub,
						KSub,
						coordinates,
						normalized,
						generated,
						xjParts[0],
						xjNonzero,
						projective_affine_piece.AffinePieceFractionField.Read(M).At(k, K, n, j, x)),
					field.FractionFieldCarrierDef.At(kRing, a.TermAs[Set[A]]("«piece»(j)"))))
			quotients := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					fForm,
					positive,
					nonzero,
					ChartQuotientsGenerate.Read(M).At(k, K, n, r, x, F)),
				"the quotients x(i)^r/F(x) lie in the chart",
				"and generate its unit ideal")
			g := a.TermAs[A]("«g»(j)")
			gInChart := a.Have(
				"g = x(j)^r/F(x) lies in the chart, one of its quotients",
				"«g»(j) ∈ «chart»(F)",
				BySets(quotients[0], xjParts[0]))
			chartInK := a.Have(
				"the chart lies in K",
				"«chart»(F) ⊆ K",
				BySets())
			chartRing := a.Have(
				"the chart, a subring of M, is a ring under M's operations",
				"comm_ring_on(restrict_ring(field_ring(M), «chart»(F)))",
				By(
					GroupPremises(
						kSub,
						KSub,
						kInK,
						coordinatesInM,
						fForm,
						projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
					comm_ring.SubringRingOn.Read(ring).At(chartF)))
			ghInM := a.Conjuncts(
				a.Have(
					"g and h lie in M",
					"«g»(j) ∈ M.carrier ∧ «h»(j) ∈ M.carrier",
					BySets(gInChart, aways[1], aways[2], KInM)),
				"g lies in M",
				"h lies in M")
			gm := a.MemberOf[on.M](g, ghInM[0])
			hm := a.MemberOf[on.M](a.TermAs[A]("«h»(j)"), ghInM[1])
			monoid := comm_ring.MulMonoidOn.Read(ring)
			nonzeroPowers := a.Have(
				"no power of g is zero: gᵐ·hᵐ is one, as g·h is, and one is not zero",
				"∀m:num. monoid_pow(M.mul, M.one, «g»(j), m) ≠ M.zero",
				a.ForEach(func(m *Expr[Nat]) Action {
					return By(
						aways[3],
						field.OneNotZeroOn.Read(M),
						comm_monoid.PowInverseOn.Read(monoid).At(gm, hm, m),
						comm_ring.MulLeftZeroOn.Read(ring).At(comm_monoid.PowIn.Read(monoid).At(hm, m)))
				}))
			clears := a.Have(
				"a power of g carries each member of the piece into the chart",
				"∀p:A. p ∈ «piece»(j) ⇒ ∃c:num. monoid_pow(M.mul, M.one, «g»(j), c) * p ∈ «chart»(F)",
				Derive(func(b *Argument) {
					p := b.FixAs[A]("p")
					inAway := b.Have(
						"p lies in the chart with g inverted, as the piece does",
						"p ∈ ring_away(field_ring(M), «chart»(F), «g»(j))",
						BySets(b.Assume(), aways[5]))
					b.Show(
						"so a power of g carries p into the chart",
						By(inAway, ring_away.RingAwayMember.At(fieldRing, chartF, g, p)))
				}))
			chartPowers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(chartRing))
			everyFraction := a.Have(
				"over the chart a fraction p/q of the piece serves once p and q are both multiplied by gᵐ·gˡ",
				"∀z:A. z ∈ K ⇒ ∃u v:A. u ∈ «chart»(F) ∧ v ∈ «chart»(F) ∧ v ≠ M.zero ∧ z * v = u",
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					zIn := b.Assume()
					p, q, fraction := b.Unpack2As[A, A](GroupPremises(zIn, fractions.At(z)), "p", "q")
					parts := b.Conjuncts(
						fraction,
						"p lies in the piece",
						"so does q",
						"q is not zero",
						"z·q = p")
					m, pCleared := b.UnpackAs[Nat](GroupPremises(parts[0], clears.At(p)), "m")
					l, qCleared := b.UnpackAs[Nat](GroupPremises(parts[1], clears.At(q)), "l")
					inM := b.Have(
						"z, p and q lie in M",
						"z ∈ M.carrier ∧ p ∈ M.carrier ∧ q ∈ M.carrier",
						BySets(zIn, parts[0], parts[1], aways[1], KInM))
					memberParts := b.Conjuncts(
						inM,
						"z lies in M",
						"p lies in M",
						"q lies in M")
					zm, qm := b.MemberOf[on.M](z, memberParts[0]), b.MemberOf[on.M](q, memberParts[2])
					powerM, powerL := comm_monoid.PowIn.Read(monoid).At(gm, m), comm_monoid.PowIn.Read(monoid).At(gm, l)
					numeratorIn := b.Have(
						"gˡ·(gᵐ·p) lies in the chart, a product of members of it",
						"monoid_pow(M.mul, M.one, «g»(j), l) * (monoid_pow(M.mul, M.one, «g»(j), m) * p) ∈ «chart»(F)",
						By(comm_ring.MulIn.Read(chartRing), chartPowers, gInChart, pCleared))
					denominatorIn := b.Have(
						"and so does gᵐ·(gˡ·q)",
						"monoid_pow(M.mul, M.one, «g»(j), m) * (monoid_pow(M.mul, M.one, «g»(j), l) * q) ∈ «chart»(F)",
						By(comm_ring.MulIn.Read(chartRing), chartPowers, gInChart, qCleared))
					denominatorNonzero := b.Have(
						"which is not zero, a product of nonzero members of M",
						"monoid_pow(M.mul, M.one, «g»(j), m) * (monoid_pow(M.mul, M.one, «g»(j), l) * q) ≠ M.zero",
						By(
							parts[2],
							nonzeroPowers.At(m),
							nonzeroPowers.At(l),
							field.MulEqZeroOn.Read(M).At(powerM, comm_ring.MulIn.Read(ring).At(powerL, qm)),
							field.MulEqZeroOn.Read(M).At(powerL, qm)))
					cleared := b.Have(
						"z·q = p multiplied by gᵐ·gˡ",
						"z * (monoid_pow(M.mul, M.one, «g»(j), m) * (monoid_pow(M.mul, M.one, «g»(j), l) * q)) = "+
							"monoid_pow(M.mul, M.one, «g»(j), l) * (monoid_pow(M.mul, M.one, «g»(j), m) * p)",
						ByArith(
							ring,
							zm,
							inM,
							powerM,
							powerL,
							Scaled(
								b.TermAs[A]("monoid_pow(M.mul, M.one, «g»(j), m) * monoid_pow(M.mul, M.one, «g»(j), l)"),
								parts[3])))
					b.Take(
						b.TermAs[A]("monoid_pow(M.mul, M.one, «g»(j), l) * (monoid_pow(M.mul, M.one, «g»(j), m) * p)"))
					b.Take(
						b.TermAs[A]("monoid_pow(M.mul, M.one, «g»(j), m) * (monoid_pow(M.mul, M.one, «g»(j), l) * q)"))
					b.Show(
						"so z is the fraction of these two members of the chart",
						By(numeratorIn, denominatorIn, denominatorNonzero, cleared))
				}))
			a.Show(
				"the chart lies in K, and every member of K is a fraction of it",
				By(chartInK, everyFraction, field.FractionFieldCarrierDef.At(kRing, chartF)))
		}),
})}

// FormsOverSubspace — the values of the forms of degree r·j over F(x)ʲ are
// the values of the forms of degree r·j times F(x)^(−j), and so a k-subspace
// of M of dimension h(r·j): multiplication by F(x)^(−j), linear over k and
// one to one, carries the values of the forms of degree r·j
// (projective_curve.FormValuesSubspace) onto them, the value H(x) going to H(x)/F(x)ʲ.
var FormsOverSubspace = formsOverSubspaceThm{family.Add(registry.ProofEntry{
	Name: "FormsOverSubspace",
	Key:  "prop_98199f298ba1eff9",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r j:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F:((num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"«at»(F) ≠ M.zero",
		},
		Conclusion: "«formsOver»(j) = image(M.mul(«scale»), «values»(r * j)) ∧ " +
			"submodule(«hilbertCoefficients», regular_module(field_ring(M)), «formsOver»(j)) ∧ " +
			"finite_dimensional(«hilbertCoefficients», «vectors»(«formsOver»(j))) ∧ " +
			"«dim»(«vectors»(«formsOver»(j))) = projective_hilbert_function(field_ring(M), k, n, E, r * j)",
		Abbrev: Abbrev{
			{Name: "values", Text: "λd:num. " +
				"    image(«at», {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)))"},
			{Name: "dim", Text: "module_dim(«hilbertCoefficients»)"},
			{Name: "scale", Text: "monoid_pow(M.mul, M.one, M.inv(«at»(F)), j)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r, j *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F *Arrow[Fun[Nat, Nat], A],
			kSub, KSub, generic, fForm, nonzero Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			ops := a.TermAs[FieldOps[A]]("M")
			scalars := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
			inv := a.TermAs[Fun[A, A]]("M.inv")
			at := a.TermAs[Fun[Fun[Fun[Nat, Nat], A], A]]("«at»")
			forms := a.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
				"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r * j, P)}")
			values := a.TermAs[Set[A]]("«values»(r * j)")
			valuesModule := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(«values»(r * j))")
			scaling := a.TermAs[Fun[A, A]]("M.mul(«scale»)")
			f, fInverse := a.TermAs[A]("«at»(F)"), a.TermAs[A]("M.inv(«at»(F))")
			subspace := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					generic,
					projective_curve.FormValuesSubspace.Read(M).At(k, K, n, a.TermAs[Nat]("r * j"), E, x)),
				"the values of the forms of degree r·j are a k-subspace of M",
				"inside K",
				"finite-dimensional",
				"of dimension h(r·j)")
			point := a.Conjuncts(
				generic,
				"x is a point of the curve over K",
				"whose coordinates generate K over k",
				"where a form vanishes exactly when it lies in the ideal")
			coordinates := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates generate over k",
				"k ⊆ K",
				BySets(
					point[1],
					kSub,
					coordinates,
					KInM,
					field.SubfieldSubset.At(ops, k),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			evaluation := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			fInK := a.Have(
				"F(x) lies in K",
				"«at»(F) ∈ K",
				By(homogeneous_polynomial.FormPolynomial.Read(fForm), evaluation[1]))
			scaleInK := a.Have(
				"so does F(x)^(−j), K being a subfield",
				"«scale» ∈ K",
				By(
					KSub,
					fInK,
					field.SubfieldInv.At(ops, K, f),
					field.SubfieldPowerIn.Read(M).AsFact().At(K, fInverse, j)))
			inM := a.Have(
				"F(x), its inverse and F(x)^(−j) lie in M",
				"«at»(F) ∈ M.carrier ∧ M.inv(«at»(F)) ∈ M.carrier ∧ «scale» ∈ M.carrier",
				BySets(fInK, scaleInK, KInM, field.InvIn.Read(M)))
			members := a.Conjuncts(
				inM,
				"F(x) lies in M",
				"its inverse lies in M",
				"F(x)^(−j) lies in M")
			fm, fInverseM := a.MemberOf[on.M](f, members[0]), a.MemberOf[on.M](fInverse, members[1])
			cancel := a.Have(
				"F(x)^(−1)·F(x) = 1, F(x) being nonzero",
				"M.inv(«at»(F)) * «at»(F) = M.one",
				By(nonzero, members[0], field.MulLeftInverseOn.Read(M)))
			powers := a.Have(
				"so F(x)^(−j)·F(x)^j = 1",
				"«scale» * monoid_pow(M.mul, M.one, «at»(F), j) = M.one",
				By(cancel, comm_monoid.PowInverseOn.Read(monoid).At(fInverseM, fm, j)))
			fPower := comm_monoid.PowIn.Read(monoid).At(fm, j)
			scaleMember := a.MemberOf[on.M](a.TermAs[A]("«scale»"), members[2])
			scaleNonzero := a.Have(
				"F(x)^(−j) is not zero, its product with F(x)ʲ being one",
				"«scale» ≠ M.zero",
				By(powers, field.OneNotZeroOn.Read(M), comm_ring.MulLeftZeroOn.Read(ring).At(fPower)))

			// Multiplication by F(x)^(−j) is k-linear, so it carries the subspace of values onto a finite-dimensional subspace.
			linear := a.Have(
				"multiplication by F(x)^(−j) is k-linear on the values of the forms of degree r·j",
				"module_homomorphism(«hilbertCoefficients», "+
					"    «vectors»(«values»(r * j)), "+
					"    regular_module(field_ring(M)), "+
					"    M.mul(«scale»))",
				By(
					subspace[0],
					kSub,
					field_extension.MultiplicationLinear.Read(M).At(k, scaleMember),
					module_homomorphism.HomRestrictSource.At(scalars, regular, regular, scaling, values)))
			kField := a.Have(
				"k is a field under M's operations",
				"ring_subfield(«hilbertCoefficients», M.inv, k)",
				By(kSub, field.SubfieldRingSubfield.Read(M).AsFact().At(k, k)))
			valuesInM := a.Have(
				"the values of degree r·j lie in M",
				"«values»(r * j) ⊆ M.carrier",
				BySets(subspace[1], KInM))
			oneToOne := a.Have(
				"and multiplication by F(x)^(−j) is one to one on them, F(x)^(−j) being nonzero",
				"injective_on(«values»(r * j), M.mul(«scale»))",
				By(
					scaleNonzero,
					valuesInM,
					field.MulBijective.Read(M).At(scaleMember),
					functions.InjectiveOnSubset.At(scaling, values, a.TermAs[Set[A]]("M.carrier"))))
			image := a.Have(
				"so the image of the values is a k-subspace of M of their dimension",
				"submodule(«hilbertCoefficients», "+
					"    regular_module(field_ring(M)), "+
					"    image(M.mul(«scale»), «values»(r * j))) ∧ "+
					"finite_dimensional(«hilbertCoefficients», «vectors»(image(M.mul(«scale»), «values»(r * j)))) ∧ "+
					"«dim»(«vectors»(image(M.mul(«scale»), «values»(r * j)))) = «dim»(«vectors»(«values»(r * j)))",
				By(
					kField,
					linear,
					oneToOne,
					subspace[2],
					module_dimension.InjectiveImageDim.At(scalars, inv, valuesModule, regular, scaling),
					module_homomorphism.ImageSubmodule.At(scalars, valuesModule, regular, scaling)))

			// The image is the forms over F(x)ʲ: H(x) goes to H(x)/F(x)ʲ.
			into := a.Have(
				"F(x)^(−j)·H(x) is the value of the form H over F(x)ʲ",
				"∀v:A. v ∈ «values»(r * j) ⇒ «scale» * v ∈ «formsOver»(j)",
				Derive(func(b *Argument) {
					v := b.FixAs[A]("v")
					vIn := b.Assume()
					_, form := b.UnpackAs[Fun[Fun[Nat, Nat], A]](b.Have(
						"v is the value at x of a form H of degree r·j",
						"∃H:((num → num) → A). "+
							"    v = «at»(H) ∧ "+
							"    H ∈ {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r * j, P)}",
						By(vIn, set_basic.InImage.At(at, forms, v))), "H")
					vInK := b.Have(
						"v lies in K, and so in M",
						"v ∈ K ∧ v ∈ M.carrier",
						BySets(vIn, subspace[1], KInM))
					quotientInK := b.Have(
						"F(x)^(−j)·v lies in K",
						"«scale» * v ∈ K",
						By(KSub, scaleInK, vInK, field.SubfieldMul.At(ops, K, a.TermAs[A]("«scale»"), v)))
					value := b.Have(
						"F(x)^(−j)·v·F(x)ʲ = v",
						"«scale» * v * monoid_pow(M.mul, M.one, «at»(F), j) = v",
						ByArith(M, inM, vInK, fPower, Scaled(v, powers)))
					b.Show(
						"so it lies over F(x)ʲ, by the form H",
						BySets(form, quotientInK, value))
				}))
			onto := a.Have(
				"each value of a form of degree r·j over F(x)ʲ is such a quotient",
				"∀y:A. y ∈ «formsOver»(j) ⇒ y ∈ image(M.mul(«scale»), «values»(r * j))",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					member := b.Conjuncts(
						b.Assume(),
						"y lies in K",
						"y·F(x)ʲ is the value of a form of degree r·j")
					H, rep := b.UnpackAs[Fun[Fun[Nat, Nat], A]](member[1], "H")
					repParts := b.Conjuncts(
						rep,
						"H is a form of degree r·j",
						"y·F(x)ʲ = H(x)")
					valueIn := b.Have(
						"H(x) is a value of degree r·j",
						"«at»(H) ∈ «values»(r * j)",
						By(repParts[0], set_image.FunInImage.At(at, forms, H)))
					yInM := b.Have(
						"y lies in M",
						"y ∈ M.carrier",
						BySets(member[0], KInM))
					recovered := b.Have(
						"y = F(x)^(−j)·H(x)",
						"y = «scale» * «at»(H)",
						repParts[1].RwRev(),
						ByArith(M, inM, yInM, fPower, Scaled(y, powers)))
					b.Show(
						"so y is the image of H(x)",
						By(recovered, valueIn, set_basic.InImage.At(scaling, values, y)))
				}))
			same := a.Have(
				"so the image is the values of the forms of degree r·j over F(x)ʲ",
				"image(M.mul(«scale»), «values»(r * j)) = «formsOver»(j)",
				BySets(
					into,
					onto,
					set_image.ImageSubsetIff.At(scaling, values, a.TermAs[Set[A]]("«formsOver»(j)"))))
			a.Show(
				"the image of the values under F(x)^(−j), a k-subspace of M of dimension h(r·j)",
				same.RwRev(),
				By(image, subspace[3]))
		}),
})}

// ChartsMeetInConstants — the two charts meet in k. The chart of G lies in
// tᴺ times itself for every N, 1/t lying in it, so the meet lies in the
// forms of degree r·N over F(x)ᴺ for the N of projective_sections.SectionsAreForms, a
// finite-dimensional k-space (FormsOverSubspace). The meet, a subring of M
// holding k, is then finitely generated over k, so each of its members is
// integral over k (principal_ideal_domain.FiniteSubringIntegral), algebraic,
// and in k (projective_generic_point.GenericFieldExactConstants).
var ChartsMeetInConstants = chartsMeetInConstantsThm{family.Add(registry.ProofEntry{
	Name: "ChartsMeetInConstants",
	Key:  "prop_8bfaa57145905fa1",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"«at»(G) ≠ M.zero",
			"«noCommonZero»",
		},
		Conclusion: "«chart»(F) ∩ «chart»(G) = k",
		Abbrev: Abbrev{
			{Name: "meet", Text: "«chart»(F) ∩ «chart»(G)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			closed, curve, KSub, generic, fForm, gForm, positive, fNonzero, gNonzero, noCommonZero Fact,
		) {
			ring := field.RingOn.Read(M)
			ops := a.TermAs[FieldOps[A]]("M")
			scalars := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
			inv := a.TermAs[Fun[A, A]]("M.inv")
			meet := a.TermAs[Set[A]]("«meet»")
			kSub := a.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			point := a.Conjuncts(
				generic,
				"x is a point of the curve over K",
				"whose coordinates generate K over k",
				"where a form vanishes exactly when it lies in the ideal")
			coordinates := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates generate over k",
				"k ⊆ K",
				BySets(
					point[1],
					kSub,
					coordinates,
					KInM,
					field.SubfieldSubset.At(ops, k),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			coordinatesInM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			genericField := a.Have(
				"K is the generic field of the curve, at x",
				"projective_generic_field(M, k, n, E, K)",
				Simp(Fwd(projective_curve.ProjectiveGenericFieldDef)),
				Witness(x),
				By(generic))
			chartF := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinatesInM,
					fForm,
					projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
				"the chart of F is a subring of M",
				"holding k")
			chartG := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinatesInM,
					gForm,
					projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, G)),
				"the chart of G is a subring of M",
				"holding k")
			datum := a.Have(
				"t lies in the chart of F, its inverse in the chart of G, and t·(1/t) = 1",
				"«parameter» ∈ «chart»(F) ∧ "+
					"M.inv(«parameter») ∈ «chart»(G) ∧ "+
					"«parameter» * M.inv(«parameter») = M.one",
				By(
					GroupPremises(
						kSub,
						KSub,
						kInK,
						coordinates,
						fForm,
						gForm,
						fNonzero,
						gNonzero,
						ChartsBiaffine.Read(M).At(k, K, n, r, x, F, G)),
					lattice_pair.BiaffineDef))
			datumParts := a.Conjuncts(
				datum,
				"t lies in the chart of F",
				"1/t lies in the chart of G",
				"t·(1/t) = 1")

			// The meet lies in the forms over F(x)ᴺ, a finite-dimensional k-space.
			N, sections := a.UnpackAs[Nat](GroupPremises(
				closed, curve, KSub, generic, fForm, gForm, positive, fNonzero, gNonzero, noCommonZero,
				projective_sections.SectionsAreForms.Read(M).At(k, K, n, r, E, x, F, G)), "N")
			atN := a.Have(
				"at N the chart of F meets tᴺ times the chart of G in the forms over F(x)ᴺ",
				"«chart»(F) ∩ «scaled»(N) = «formsOver»(N)",
				By(sections.At(N), nat_order.LessEqRefl))
			chartGRing := a.Have(
				"the chart of G, a subring of M, is a ring under M's operations",
				"comm_ring_on(restrict_ring(field_ring(M), «chart»(G)))",
				By(chartG[0], comm_ring.SubringRingOn.Read(ring).At(a.TermAs[Set[A]]("«chart»(G)"))))
			chartsInM := a.Have(
				"the charts lie in M",
				"«chart»(F) ⊆ M.carrier ∧ «chart»(G) ⊆ M.carrier",
				By(chartF[0], chartG[0], comm_ring.SubringSubset))
			unitsInM := a.Have(
				"t and 1/t lie in M",
				"«parameter» ∈ M.carrier ∧ M.inv(«parameter») ∈ M.carrier",
				BySets(datumParts[0], datumParts[1], chartsInM))
			unitMembers := a.Conjuncts(
				unitsInM,
				"t lies in M",
				"1/t lies in M")
			tm, um :=
				a.MemberOf[on.M](a.TermAs[A]("«parameter»"), unitMembers[0]),
				a.MemberOf[on.M](a.TermAs[A]("M.inv(«parameter»)"), unitMembers[1])
			monoid := comm_ring.MulMonoidOn.Read(ring)
			cancelPowers := a.Have(
				"tᴺ·(1/t)ᴺ = 1",
				"monoid_pow(M.mul, M.one, «parameter», N) * monoid_pow(M.mul, M.one, M.inv(«parameter»), N) = "+
					"M.one",
				By(datumParts[2], comm_monoid.PowInverseOn.Read(monoid).At(tm, um, N)))
			scaledG := a.Have(
				"the chart of G lies in tᴺ times itself: y = tᴺ·((1/t)ᴺ·y)",
				"∀y:A. y ∈ «chart»(G) ⇒ y ∈ «scaled»(N)",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yIn := b.Assume()
					yInM := b.Have(
						"y lies in M",
						"y ∈ M.carrier",
						BySets(yIn, chartsInM))
					lowered := b.Have(
						"(1/t)ᴺ·y lies in the chart of G, a ring holding 1/t",
						"monoid_pow(M.mul, M.one, M.inv(«parameter»), N) * y ∈ «chart»(G)",
						By(
							comm_ring.MulIn.Read(chartGRing),
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(chartGRing)),
							datumParts[1],
							yIn))
					back := b.Have(
						"and tᴺ times it is y",
						"y = "+
							"monoid_pow(M.mul, M.one, «parameter», N) * (monoid_pow(M.mul, M.one, M.inv(«parameter»), N) * y)",
						ByArith(
							M,
							yInM,
							comm_monoid.PowIn.Read(monoid).At(tm, N),
							comm_monoid.PowIn.Read(monoid).At(um, N),
							Scaled(y, cancelPowers)))
					image := b.Have(
						"tᴺ·((1/t)ᴺ·y) lies in tᴺ times the chart of G",
						"monoid_pow(M.mul, M.one, «parameter», N) * "+
							"(monoid_pow(M.mul, M.one, M.inv(«parameter»), N) * y) ∈ "+
							"«scaled»(N)",
						By(
							lowered,
							set_image.FunInImage.At(
								b.TermAs[Fun[A, A]]("M.mul(monoid_pow(M.mul, M.one, «parameter», N))"),
								b.TermAs[Set[A]]("«chart»(G)"),
								b.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(«parameter»), N) * y"))))
					b.Show(
						"and that is y",
						By(back, image))
				}))
			meetInForms := a.Have(
				"so the meet of the charts lies in the forms over F(x)ᴺ",
				"«meet» ⊆ «formsOver»(N)",
				BySets(scaledG, atN))
			forms := a.Conjuncts(
				GroupPremises(
					kSub, KSub, generic, fForm, fNonzero, FormsOverSubspace.Read(M).At(k, K, n, r, N, E, x, F)),
				"the forms over F(x)ᴺ are the values of degree r·N over F(x)ᴺ",
				"a k-subspace of M",
				"of finite dimension",
				"namely h(r·N)")

			// The meet is a subring holding k, so a k-subspace, finite-dimensional inside the forms.
			meetSubring := a.Have(
				"the meet of the charts is a subring of M",
				"subring(field_ring(M), «meet»)",
				Simp(Fwd(comm_ring.SubringDef)),
				BySets(a.Unfolded(chartF[0], comm_ring.SubringDef), a.Unfolded(chartG[0], comm_ring.SubringDef)))
			kInMeet := a.Have(
				"holding k",
				"k ⊆ «meet»",
				BySets(chartF[1], chartG[1]))
			kField := a.Have(
				"k is a field under M's operations, and M a k-vector space",
				"ring_subfield(«hilbertCoefficients», M.inv, k) ∧ "+
					"module_on(«hilbertCoefficients», regular_module(field_ring(M)))",
				By(
					kSub,
					field.SubfieldRingSubfield.Read(M).AsFact().At(k, k),
					field_extension.SubfieldScalars.At(ops, k)))
			kFieldParts := a.Conjuncts(
				kField,
				"k is a field under M's operations",
				"M is a k-vector space")
			meetSubspace := a.Have(
				"so the meet is a k-subspace of M, and of the forms over F(x)ᴺ",
				"submodule(«hilbertCoefficients», regular_module(field_ring(M)), «meet») ∧ "+
					"submodule(«hilbertCoefficients», "+
					"    restrict_module(regular_module(field_ring(M)), «formsOver»(N)), "+
					"    «meet»)",
				By(
					meetSubring,
					kInMeet,
					forms[1],
					meetInForms,
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(k, meet),
					submodule.SubmoduleRestrict.At(scalars, regular, a.TermAs[Set[A]]("«formsOver»(N)"), meet)))
			subspaceParts := a.Conjuncts(
				meetSubspace,
				"the meet is a k-subspace of M",
				"and of the forms over F(x)ᴺ")
			meetVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(M)), «meet»)")
			formsOver := a.TermAs[Set[A]]("«formsOver»(N)")
			formsVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(M)), «formsOver»(N))")
			formsSpace := a.Have(
				"the forms over F(x)ᴺ are a k-vector space",
				"module_on(«hilbertCoefficients», restrict_module(regular_module(field_ring(M)), «formsOver»(N)))",
				By(kFieldParts[1], forms[1], submodule.SubmoduleModuleOn.At(scalars, regular, formsOver)))
			finiteMeet := a.Have(
				"the meet is finite-dimensional, inside a finite-dimensional space",
				"finite_dimensional(«hilbertCoefficients», restrict_module(regular_module(field_ring(M)), «meet»))",
				By(
					formsSpace,
					kFieldParts[0],
					forms[2],
					subspaceParts[1],
					module_dimension.SubmoduleDim.At(scalars, formsVectors, inv, meet),
					module_record.RestrictModuleTwice.At(regular, formsOver, meet)))
			generatedMeet := a.Have(
				"so finitely generated over k",
				"module_finitely_generated(«hilbertCoefficients», "+
					"    restrict_module(regular_module(field_ring(M)), «meet»))",
				By(
					kFieldParts[0],
					finiteMeet,
					submodule.SubmoduleModuleOn.At(scalars, regular, meet),
					kFieldParts[1],
					subspaceParts[0],
					module_dimension.FiniteDimensionalSpanning.At(scalars, meetVectors, inv),
					principal_ideal_domain.FinitelyGeneratedDef.At(scalars, meetVectors)))
			kSubring := a.Have(
				"k is a subring of M",
				"subring(field_ring(M), k)",
				By(kSub, field.SubfieldSubring.Read(M)))

			// Each member of the meet is integral, so algebraic, over k, so lies in k.
			inConstants := a.Have(
				"each member of the meet lies in k",
				"∀f:A. f ∈ «meet» ⇒ f ∈ k",
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					fIn := b.Assume()
					integral := b.Have(
						"f is integral over k, the meet being a finite k-algebra",
						"integral_over(«hilbertCoefficients», f)",
						By(
							kSubring,
							meetSubring,
							kInMeet,
							generatedMeet,
							fIn,
							principal_ideal_domain.FiniteSubringIntegral.Read(M).At(k, meet, f)))
					p, relation := b.UnpackAs[Fun[Nat, A]](b.Unfolded(integral, integral_element.IntegralOverDef), "p")
					relationParts := b.Conjuncts(
						relation,
						"p is a polynomial over k",
						"monic",
						"of positive degree",
						"vanishing at f")
					algebraic := b.Have(
						"so f is algebraic over k: p is not zero, being monic",
						"algebraic_over(M, k, f)",
						Unfold(algebraic_element.AlgebraicOverDef),
						Derive(func(c *Argument) {
							c.Take(p)
							c.Show(
								"the monic p vanishes at f",
								By(
									relationParts[0],
									relationParts[3],
									polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(M)).At(p),
									relationParts[1]))
						}))
					fInK := b.Have(
						"f lies in K, as the chart of F does",
						"f ∈ K",
						BySets(fIn))
					b.Show(
						"so f lies in k, k being algebraically closed in K",
						By(
							closed,
							curve,
							KSub,
							genericField,
							fInK,
							algebraic,
							projective_generic_point.GenericFieldExactConstants.Read(M).At(k, K, n, E, f)))
				}))
			a.Show(
				"the meet is k: it lies in k and holds k",
				BySets(inConstants, kInMeet))
		}),
})}

// ParameterTranscendental — t = G(x)/F(x) is transcendental over k. Were it
// algebraic it would lie in k (projective_generic_point.GenericFieldExactConstants), and with it 1/t;
// the chart of G, which lies in the chart of F with t inverted
// (ChartInOtherAway), would then lie in the chart of F, so in the meet of the
// charts, which is k (ChartsMeetInConstants). K, the field of fractions of
// the chart of G (ChartFractionField), would be k, and every coordinate of x
// algebraic over k, against the one projective_generic_point.TranscendenceAtGenericPoint finds
// transcendental.
var ParameterTranscendental = parameterTranscendentalThm{family.Add(registry.ProofEntry{
	Name: "ParameterTranscendental",
	Key:  "prop_882052e656612d",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"«at»(G) ≠ M.zero",
			"«noCommonZero»",
		},
		Conclusion: "¬algebraic_over(M, k, «parameter»)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			closed, curve, KSub, generic, fForm, gForm, positive, fNonzero, gNonzero, noCommonZero Fact,
		) {
			ring := field.RingOn.Read(M)
			ops := a.TermAs[FieldOps[A]]("M")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			identity := a.TermAs[Fun[A, A]]("λa:A. a")
			t := a.TermAs[A]("«parameter»")
			chartF, chartG := a.TermAs[Set[A]]("«chart»(F)"), a.TermAs[Set[A]]("«chart»(G)")
			kSub := a.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			point := a.Conjuncts(
				generic,
				"x is a point of the curve over K",
				"whose coordinates generate K over k",
				"where a form vanishes exactly when it lies in the ideal")
			coordinates := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates generate over k",
				"k ⊆ K",
				BySets(
					point[1],
					kSub,
					coordinates,
					KInM,
					field.SubfieldSubset.At(ops, k),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			coordinatesInM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			genericField := a.Have(
				"K is the generic field of the curve, at x",
				"projective_generic_field(M, k, n, E, K)",
				Simp(Fwd(projective_curve.ProjectiveGenericFieldDef)),
				Witness(x),
				By(generic))

			// The coordinate of x transcendental over k.
			hasOne := a.Have(
				"some coordinate up to n is one",
				"∃j:num. j ≤ n ∧ x(j) = M.one",
				By(point[0], projective_curve.PointLeadingOne.At(fieldRing, k, K, n, E, x)))
			inclusion := a.Have(
				"k includes into M as a ring map",
				"ring_homomorphism(«hilbertCoefficients», field_ring(M), λa:A. a)",
				By(
					kSub,
					field.SubfieldSubring.Read(M).At(k),
					ring_homomorphism.SubringInclusionHom.Read(ring).At(k)))
			c, found := a.UnpackAs[Nat](GroupPremises(
				kSub,
				inclusion,
				coordinatesInM,
				hasOne,
				point[2],
				projective_curve.CurveHilbertEventuallyLinear.Read(curve),
				projective_generic_point.TranscendenceAtGenericPoint.Read(M).At(ops, k, n, E, identity, x)), "c")
			foundParts := a.Conjuncts(
				found,
				"c indexes a coordinate",
				"x(c) is transcendental over k",
				"and every coordinate is algebraic over k(x(c))")
			transcendental := a.Have(
				"x(c) is transcendental over k",
				"¬algebraic_over(M, k, x(c))",
				By(Normalized, foundParts[1], set_image.ImageIdentity.At(k)))

			// Were t algebraic, K would be k.
			algebraic := a.SupposeNot()
			datum := a.Conjuncts(
				a.Have(
					"t lies in the chart of F, and t·(1/t) = 1",
					"«parameter» ∈ «chart»(F) ∧ «parameter» * M.inv(«parameter») = M.one",
					By(
						GroupPremises(
							kSub,
							KSub,
							kInK,
							coordinates,
							fForm,
							gForm,
							fNonzero,
							gNonzero,
							ChartsBiaffine.Read(M).At(k, K, n, r, x, F, G)),
						lattice_pair.BiaffineDef)),
				"t lies in the chart of F",
				"t·(1/t) = 1")
			tInK := a.Have(
				"so t lies in K, as the chart of F does",
				"«parameter» ∈ K",
				BySets(datum[0]))
			tInConstants := a.Have(
				"so t, algebraic over k, lies in k",
				"«parameter» ∈ k",
				By(
					closed,
					curve,
					KSub,
					genericField,
					tInK,
					algebraic,
					projective_generic_point.GenericFieldExactConstants.Read(M).At(k, K, n, E, t)))
			inverseInConstants := a.Have(
				"and so does 1/t",
				"M.inv(«parameter») ∈ k",
				By(kSub, tInConstants, field.SubfieldInv.At(ops, k, t)))
			chartFacts := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinatesInM,
					fForm,
					projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
				"the chart of F is a subring of M",
				"holding k")
			chartRing := a.Have(
				"the chart of F is a ring under M's operations",
				"comm_ring_on(restrict_ring(field_ring(M), «chart»(F)))",
				By(chartFacts[0], comm_ring.SubringRingOn.Read(ring).At(chartF)))
			inverseInChart := a.Have(
				"1/t lies in the chart of F, which holds k",
				"M.inv(«parameter») ∈ «chart»(F)",
				BySets(inverseInConstants, chartFacts[1]))
			intoAway := a.Have(
				"the chart of G lies in the chart of F with t inverted",
				"«chart»(G) ⊆ ring_away(field_ring(M), «chart»(F), «parameter»)",
				By(GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					gForm,
					fForm,
					fNonzero,
					ChartInOtherAway.Read(M).At(k, K, n, r, x, G, F))))
			tm := a.MemberOf[on.M](t, a.Have(
				"t lies in M",
				"«parameter» ∈ M.carrier",
				BySets(tInK, KInM)))
			um := field.InvIn.Read(M).At(tm)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			chartGInF := a.Have(
				"so the chart of G lies in the chart of F: 1/t, a constant, clears the powers of t",
				"∀y:A. y ∈ «chart»(G) ⇒ y ∈ «chart»(F)",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yIn := b.Assume()
					away := b.Have(
						"y lies in the chart of F with t inverted",
						"y ∈ ring_away(field_ring(M), «chart»(F), «parameter»)",
						BySets(yIn, intoAway))
					d, cleared := b.UnpackAs[Nat](b.Have(
						"so a power tᵈ carries y into the chart of F",
						"∃d:num. monoid_pow(M.mul, M.one, «parameter», d) * y ∈ «chart»(F)",
						By(away, ring_away.RingAwayMember.At(fieldRing, chartF, t, y))), "d")
					yInM := b.Have(
						"y lies in M",
						"y ∈ M.carrier",
						By(away, ring_away.RingAwayMember.At(fieldRing, chartF, t, y)))
					back := b.Have(
						"and (1/t)ᵈ·tᵈ·y = y",
						"monoid_pow(M.mul, M.one, M.inv(«parameter»), d) * "+
							"(monoid_pow(M.mul, M.one, «parameter», d) * y) = "+
							"y",
						ByArith(
							M,
							yInM,
							comm_monoid.PowIn.Read(monoid).At(tm, d),
							comm_monoid.PowIn.Read(monoid).At(um, d),
							datum[1],
							Scaled(y, comm_monoid.PowInverseOn.Read(monoid).At(tm, um, d))))
					inChart := b.Have(
						"(1/t)ᵈ·(tᵈ·y) lies in the chart of F, a ring holding 1/t",
						"monoid_pow(M.mul, M.one, M.inv(«parameter»), d) * "+
							"(monoid_pow(M.mul, M.one, «parameter», d) * y) ∈ "+
							"«chart»(F)",
						By(
							comm_ring.MulIn.Read(chartRing),
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(chartRing)),
							inverseInChart,
							cleared))
					b.Show(
						"so y does",
						By(Normalized, back, inChart))
				}))
			meet := a.Have(
				"the charts meet in k",
				"«chart»(F) ∩ «chart»(G) = k",
				By(GroupPremises(
					closed,
					curve,
					KSub,
					generic,
					fForm,
					gForm,
					positive,
					fNonzero,
					gNonzero,
					noCommonZero,
					ChartsMeetInConstants.Read(M).At(k, K, n, r, E, x, F, G))))
			chartGConstant := a.Have(
				"so the chart of G lies in k",
				"«chart»(G) ⊆ k",
				BySets(chartGInF, meet))
			fractions := a.Have(
				"each member of K is a fraction of the chart of G",
				"∀z:A. z ∈ K ⇒ ∃u v:A. u ∈ «chart»(G) ∧ v ∈ «chart»(G) ∧ v ≠ M.zero ∧ z * v = u",
				By(
					GroupPremises(
						kSub,
						KSub,
						coordinates,
						hasOne,
						point[1],
						gForm,
						positive,
						gNonzero,
						ChartFractionField.Read(M).At(k, K, n, r, x, G)),
					field.FractionFieldCarrierDef.At(
						a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), K)"), chartG)))
			constants := a.Have(
				"so every member of K lies in k, a quotient of two constants",
				"∀z:A. z ∈ K ⇒ z ∈ k",
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					zIn := b.Assume()
					u, v, fraction := b.Unpack2As[A, A](GroupPremises(zIn, fractions.At(z)), "u", "v")
					parts := b.Conjuncts(
						fraction,
						"u lies in the chart of G",
						"so does v",
						"v is not zero",
						"z·v = u")
					inConstants := b.Have(
						"u and v are constants",
						"u ∈ k ∧ v ∈ k",
						BySets(parts[0], parts[1], chartGConstant))
					members := b.Have(
						"z, u and v lie in M",
						"z ∈ M.carrier ∧ u ∈ M.carrier ∧ v ∈ M.carrier",
						BySets(zIn, inConstants, kInK, KInM))
					memberParts := b.Conjuncts(
						members,
						"z lies in M",
						"u lies in M",
						"v lies in M")
					vm := b.MemberOf[on.M](v, memberParts[2])
					quotient := b.Have(
						"z = u/v",
						"z = u * M.inv(v)",
						ByArith(
							M,
							memberParts[0],
							memberParts[1],
							vm,
							field.InvIn.Read(M).At(vm),
							parts[2],
							Scaled(b.TermAs[A]("M.inv(v)"), parts[3]),
							Scaled(z, field.MulRightInverseOn.Read(M).At(vm))))
					b.Show(
						"which lies in k, a subfield",
						By(
							Normalized,
							quotient,
							kSub,
							inConstants,
							field.SubfieldInv.At(ops, k, v),
							field.SubfieldMul.At(ops, k, u, b.TermAs[A]("M.inv(v)"))))
				}))
			coordinateConstant := a.Have(
				"so x(c), a member of K, would lie in k",
				"x(c) ∈ k",
				By(constants.At(a.TermAs[A]("x(c)")), coordinates.At(c), foundParts[0]))
			a.Show(
				"and be algebraic over k",
				By(
					transcendental,
					kSub,
					coordinateConstant,
					algebraic_element.MemberAlgebraic.Read(M).AsFact().At(k, a.TermAs[A]("x(c)"))))
		}),
})}

// ChartFinitelyGenerated — the chart of F is finitely generated over k[t],
// t = G(x)/F(x), by a finite k-spanning set S₀ of the forms of degree r·N
// over F(x)ᴺ, a finite-dimensional k-space (FormsOverSubspace), for the N of
// projective_form_pair.CoprimeValuesGenerate. The chart is the union of the forms over F(x)^a,
// each lying in all the later ones; and from N on a member H(x)/F(x)^(a+1)
// is p/F(x)^a + t·q/F(x)^a for the values p, q of degree r·a with
// H(x) = F(x)·p + G(x)·q, so by induction the forms over F(x)^(N+c) lie in
// the k[t]-span of S₀ for every c.
var ChartFinitelyGenerated = chartFinitelyGeneratedThm{family.Add(registry.ProofEntry{
	Name: "ChartFinitelyGenerated",
	Key:  "prop_3dac078d99f57b7c",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"«noCommonZero»",
		},
		Conclusion: "module_finitely_generated( " +
			"    restrict_ring(field_ring(M), polynomial_image(field_ring(M), k, «parameter»)), " +
			"    restrict_module(regular_module(field_ring(M)), «chart»(F)))",
		Abbrev: Abbrev{
			{Name: "values", Text: "λd:num. " +
				"    image(«at», {P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)})"},
			{Name: "line", Text: "polynomial_image(field_ring(M), k, «parameter»)"},
			{Name: "lineRing", Text: "restrict_ring(field_ring(M), «line»)"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(M)))"},
			{Name: "span", Text: "module_span(«lineRing», «vectors»(«chart»(F)), S₀)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			closed, curve, KSub, generic, fForm, gForm, positive, fNonzero, noCommonZero Fact,
		) {
			ring := field.RingOn.Read(M)
			monoid := comm_ring.MulMonoidOn.Read(ring)
			ops := a.TermAs[FieldOps[A]]("M")
			scalars := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
			lineRing := a.TermAs[module_record.RingOps[A]]("«lineRing»")
			regular := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(M))")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«vectors»(«chart»(F))")
			inv := a.TermAs[Fun[A, A]]("M.inv")
			at := a.TermAs[Fun[Fun[Fun[Nat, Nat], A], A]]("«at»")
			values := a.TermAs[Fun[Nat, Set[A]]]("«values»")
			chartF := a.TermAs[Set[A]]("«chart»(F)")
			line := a.TermAs[Set[A]]("«line»")
			f, t := a.TermAs[A]("«at»(F)"), a.TermAs[A]("«parameter»")
			kSub := a.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			point := a.Conjuncts(
				generic,
				"x is a point of the curve over K",
				"whose coordinates generate K over k",
				"where a form vanishes exactly when it lies in the ideal")
			coordinates := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates generate over k",
				"k ⊆ K",
				BySets(
					point[1],
					kSub,
					coordinates,
					KInM,
					field.SubfieldSubset.At(ops, k),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			coordinatesInM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			evaluation := a.Conjuncts(
				GroupPremises(
					kSub, KSub, kInK, coordinates, projective_curve.PointEvaluation.Read(M).At(k, K, n, x)),
				"evaluation at x is a ring map",
				"with values in K")
			members := a.Conjuncts(
				a.Have(
					"F(x), G(x) and the inverse of F(x) lie in M",
					"«at»(F) ∈ M.carrier ∧ «at»(G) ∈ M.carrier ∧ M.inv(«at»(F)) ∈ M.carrier",
					BySets(
						a.Have(
							"F(x) and G(x) lie in K",
							"«at»(F) ∈ K ∧ «at»(G) ∈ K",
							By(
								homogeneous_polynomial.FormPolynomial.Read(fForm),
								homogeneous_polynomial.FormPolynomial.Read(gForm),
								evaluation[1])),
						KInM,
						field.InvIn.Read(M))),
				"F(x) lies in M",
				"so does G(x)",
				"and the inverse of F(x)")
			fm, fInverse :=
				a.MemberOf[on.M](f, members[0]), a.MemberOf[on.M](a.TermAs[A]("M.inv(«at»(F))"), members[2])
			cancel := a.Have(
				"F(x)^(−1)·F(x) = 1, F(x) being nonzero",
				"M.inv(«at»(F)) * «at»(F) = M.one",
				By(fNonzero, members[0], field.MulLeftInverseOn.Read(M)))

			// The chart, k[t] inside it, and the chart as a module over k[t] and over k.
			chart := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinatesInM,
					fForm,
					projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
				"the chart of F is a subring of M",
				"holding k")
			tInChart := a.Have(
				"t lies in the chart of F",
				"«parameter» ∈ «chart»(F)",
				By(GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					fForm,
					gForm,
					fNonzero,
					ParameterInChart.Read(M).At(k, K, n, r, x, F, G))))
			chartInM := a.Have(
				"the chart lies in M",
				"«chart»(F) ⊆ M.carrier",
				By(chart[0], comm_ring.SubringSubset))
			tm := a.MemberOf[on.M](t, a.Have(
				"so t lies in M",
				"«parameter» ∈ M.carrier",
				BySets(tInChart, chartInM)))
			lineFacts := a.Conjuncts(
				GroupPremises(kSub, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)),
				"k[t] is a subring of M",
				"holding k",
				"and t",
				"inside the field k(t)")
			lineInChart := a.Have(
				"k[t] lies in the chart, a ring holding k and t",
				"«line» ⊆ «chart»(F)",
				By(
					comm_ring.SubringRingOn.Read(ring).At(chartF),
					chart[0],
					chart[1],
					tInChart,
					algebraic_element.PolynomialImageLeast.Read(M).At(k, chartF, t)))
			chartOverLine := a.Have(
				"the chart is a module over k[t]",
				"module_on(«lineRing», «vectors»(«chart»(F)))",
				By(
					lineFacts[0],
					chart[0],
					lineInChart,
					fractional_ideal.FieldModuleOn.Read(M).At(line),
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(line, chartF),
					submodule.SubmoduleModuleOn.At(lineRing, regular, chartF)))
			kField := a.Conjuncts(
				a.Have(
					"k is a field under M's operations, and M a k-vector space",
					"ring_subfield(«hilbertCoefficients», M.inv, k) ∧ "+
						"module_on(«hilbertCoefficients», regular_module(field_ring(M)))",
					By(
						kSub,
						field.SubfieldRingSubfield.Read(M).AsFact().At(k, k),
						field_extension.SubfieldScalars.At(ops, k))),
				"k is a field under M's operations",
				"M is a k-vector space")
			chartOverK := a.Have(
				"the chart is a k-vector space",
				"module_on(«hilbertCoefficients», «vectors»(«chart»(F)))",
				By(
					chart[0],
					chart[1],
					kField[1],
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(k, chartF),
					submodule.SubmoduleModuleOn.At(scalars, regular, chartF)))

			// The bound N, and a finite k-spanning set S₀ of the forms over F(x)ᴺ.
			N, generate := a.UnpackAs[Nat](GroupPremises(
				closed, curve, KSub, point[0], fForm, gForm, noCommonZero,
				projective_form_pair.CoprimeValuesGenerate.Read(M).At(k, K, n, r, E, x, F, G)), "N")
			formsN := a.TermAs[Set[A]]("«formsOver»(N)")
			forms := a.Conjuncts(
				GroupPremises(
					kSub, KSub, generic, fForm, fNonzero, FormsOverSubspace.Read(M).At(k, K, n, r, N, E, x, F)),
				"the forms over F(x)ᴺ are the values of degree r·N over F(x)ᴺ",
				"a k-subspace of M",
				"of finite dimension",
				"namely h(r·N)")
			formsVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(M)), «formsOver»(N))")
			S0, spanning := a.UnpackAs[Set[A]](a.Have(
				"a finite set S₀ inside the forms over F(x)ᴺ spans them over k",
				"∃S:set(A). "+
					"    finite(S) ∧ "+
					"    S ⊆ «formsOver»(N) ∧ "+
					"    module_span(«hilbertCoefficients», "+
					"        restrict_module(regular_module(field_ring(M)), «formsOver»(N)), "+
					"        S) = "+
					"    «formsOver»(N)",
				By(
					kField[0],
					kField[1],
					forms[1],
					forms[2],
					submodule.SubmoduleModuleOn.At(scalars, regular, formsN),
					module_dimension.FiniteDimensionalSpanning.At(scalars, formsVectors, inv))), "S₀")
			spanParts := a.Conjuncts(
				spanning,
				"S₀ is finite",
				"inside the forms over F(x)ᴺ",
				"spanning them over k")
			formsInChart := a.Have(
				"the forms over F(x)ᴺ lie in the chart",
				"«formsOver»(N) ⊆ «chart»(F)",
				BySets())
			S0InChart := a.Have(
				"so S₀ lies in the chart",
				"S₀ ⊆ «chart»(F)",
				BySets(spanParts[1]))

			// The k[t]-span of S₀: a k[t]-submodule of the chart, so a k-submodule, holding the forms over F(x)ᴺ.
			spanFacts := a.Conjuncts(
				a.Have(
					"the k[t]-span of S₀ is a k[t]-submodule of the chart holding S₀",
					"submodule(«lineRing», «vectors»(«chart»(F)), «span») ∧ S₀ ⊆ «span»",
					By(
						chartOverLine,
						S0InChart,
						submodule.SpanSubmodule.At(lineRing, vectors, S0),
						submodule.SubsetSpan.At(lineRing, vectors, S0))),
				"the span is a k[t]-submodule of the chart",
				"holding S₀")
			spanOverK := a.Have(
				"so a k-submodule, k lying in k[t]",
				"submodule(«hilbertCoefficients», «vectors»(«chart»(F)), «span»)",
				By(lineFacts[1], submodule.SubmoduleRestrictScalars.Read(spanFacts[0]).At(scalars)))
			formsInVectors := a.Have(
				"the forms over F(x)ᴺ, a k-submodule of the chart, are spanned by S₀ there",
				"module_span(«hilbertCoefficients», «vectors»(«chart»(F)), S₀) = «formsOver»(N)",
				By(
					chartOverK,
					spanParts[1],
					spanParts[2],
					forms[1],
					formsInChart,
					submodule.SubmoduleRestrict.At(scalars, regular, chartF, formsN),
					module_record.RestrictModuleTwice.At(regular, chartF, formsN),
					linear_independence.SpanningRestrict.At(scalars, vectors, formsN, S0)))
			formsInSpan := a.Have(
				"so the forms over F(x)ᴺ lie in the k[t]-span of S₀",
				"«formsOver»(N) ⊆ «span»",
				formsInVectors.RwRev(),
				By(
					spanOverK,
					spanFacts[1],
					submodule.SpanLeast.At(scalars, vectors, S0, a.TermAs[Set[A]]("«span»"))))

			// Multiplying by a power of F(x) moves forms over F(x)^a to forms over F(x)^(a+c).
			valuesInM := a.Have(
				"the values of forms lie in M",
				"∀d:num. «values»(d) ⊆ M.carrier",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					inK := b.Conjuncts(
						GroupPremises(
							kSub, KSub, generic, projective_curve.FormValuesSubspace.Read(M).At(k, K, n, d, E, x)),
						"the values of the forms of degree d are a k-subspace of M",
						"inside K",
						"finite-dimensional",
						"of dimension h(d)")
					b.Show(
						"and K lies in M",
						BySets(inK[1], KInM))
				}))
			ringK := a.Have(
				"k is a commutative ring under M's operations",
				"comm_ring_on(«hilbertCoefficients»)",
				By(kSub, field.SubfieldCommRing.Read(M).At(k)))
			raise := a.Have(
				"F(x)·v is a value of degree d + r when v is one of degree d",
				"∀d:num. ∀v:A. v ∈ «values»(d) ⇒ «at»(F) * v ∈ «values»(d + r)",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					v := b.FixAs[A]("v")
					vIn := b.Assume()
					P, form := b.UnpackAs[Fun[Fun[Nat, Nat], A]](b.Have(
						"v is the value at x of a form P of degree d",
						"∃P:((num → num) → A). v = «at»(P) ∧ homogeneous_polynomial(«hilbertCoefficients», n, d, P)",
						By(
							vIn,
							set_basic.InImage.At(
								at,
								b.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
									"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d, P)}"),
								v))),
						"P")
					formParts := b.Conjuncts(
						form,
						"v = P(x)",
						"P is a form of degree d")
					product := b.Have(
						"P·F is a form of degree d + r",
						"homogeneous_polynomial(«hilbertCoefficients», "+
							"    n, "+
							"    d + r, "+
							"    polynomial_algebra_mul(«hilbertCoefficients», P, F))",
						By(homogeneous_polynomial.FormProduct.At(scalars, n, d, r, P, F), ringK, formParts[1], fForm))
					productParts := b.Conjuncts(
						b.Have(
							"its value is P(x)·F(x)",
							"«at»(polynomial_algebra_mul(«hilbertCoefficients», P, F)) = «at»(P) * «at»(F) ∧ "+
								"«at»(P) ∈ M.carrier",
							By(
								homogeneous_polynomial.FormPolynomial.Read(formParts[1]),
								homogeneous_polynomial.FormPolynomial.Read(fForm),
								ring_homomorphism.MapMul.Read(evaluation[0]).AsFact().At(P, F),
								ring_homomorphism.MapIn.Read(evaluation[0]))),
						"P·F has the value P(x)·F(x)",
						"P(x) lies in M")
					swapped := b.Have(
						"so F(x)·v is that value",
						"«at»(F) * v = «at»(polynomial_algebra_mul(«hilbertCoefficients», P, F))",
						formParts[0].Rw(),
						productParts[0].Rw(),
						ByArith(M, productParts[1], members[0]))
					b.Show(
						"a value of degree d + r",
						swapped.Rw(),
						By(
							product,
							set_image.FunInImage.At(
								at,
								b.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
									"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, d + r, P)}"),
								b.TermAs[Fun[Fun[Nat, Nat], A]]("polynomial_algebra_mul(«hilbertCoefficients», P, F)"))))
				}))
			shift := a.Have(
				"the forms over F(x)^a lie in the forms over F(x)^(a+c)",
				"∀a c:num. ∀y:A. y ∈ «formsOver»(a) ⇒ y ∈ «formsOver»(a + c)",
				Derive(func(b *Argument) {
					e := b.FixAs[Nat]("a")
					c := b.FixAs[Nat]("c")
					y := b.FixAs[A]("y")
					member := b.Conjuncts(
						b.Assume(),
						"y lies in K",
						"y·F(x)^a is the value of a form of degree r·a")
					_, rep := b.UnpackAs[Fun[Fun[Nat, Nat], A]](member[1], "H")
					repParts := b.Conjuncts(
						rep,
						"H is a form of degree r·a",
						"y·F(x)^a = H(x)")
					H := b.TermAs[Fun[Fun[Nat, Nat], A]]("H")
					valueIn := b.Have(
						"H(x) is a value of degree r·a",
						"«at»(H) ∈ «values»(r * a)",
						By(
							repParts[0],
							set_image.FunInImage.At(
								at,
								b.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
									"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r * a, P)}"),
								H)))
					shifted := b.Have(
						"so F(x)^c·H(x) is a value of degree r·a + r·c",
						"monoid_pow(M.mul, M.one, «at»(F), c) * «at»(H) ∈ «values»(r * a + r * c)",
						By(
							projective_sections.PowerShiftsGrade.At(
								ops, values, f, b.TermAs[A]("«at»(H)"), r, b.TermAs[Nat]("r * a"), c),
							M,
							members[0],
							valuesInM,
							raise,
							valueIn))
					yInM := b.Have(
						"y lies in M",
						"y ∈ M.carrier",
						BySets(member[0], KInM))
					regroup := b.Have(
						"y·F(x)^(a+c) = F(x)^c·H(x)",
						"y * monoid_pow(M.mul, M.one, «at»(F), a + c) = monoid_pow(M.mul, M.one, «at»(F), c) * «at»(H)",
						repParts[1].RwRev(),
						ByArith(
							M,
							yInM,
							comm_monoid.PowIn.Read(monoid).At(fm, e),
							comm_monoid.PowIn.Read(monoid).At(fm, c),
							Scaled(y, comm_monoid.PowAddOn.Read(monoid).At(fm, e, c))))
					degrees := b.Have(
						"r·a + r·c = r·(a + c)",
						"r * a + r * c = r * (a + c)",
						ByArith())
					_, raised := b.UnpackAs[Fun[Fun[Nat, Nat], A]](b.Have(
						"so y·F(x)^(a+c) is the value of a form of degree r·(a + c)",
						"∃Q:((num → num) → A). "+
							"    y * monoid_pow(M.mul, M.one, «at»(F), a + c) = «at»(Q) ∧ "+
							"    homogeneous_polynomial(«hilbertCoefficients», n, r * (a + c), Q)",
						regroup.Rw(),
						degrees.RwRev(),
						By(
							shifted,
							set_basic.InImage.At(
								at,
								b.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
									"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r * a + r * c, P)}"),
								b.TermAs[A]("monoid_pow(M.mul, M.one, «at»(F), c) * «at»(H)")))), "Q")
					b.Show(
						"so y lies in the forms over F(x)^(a+c)",
						BySets(member[0], raised))
				}))

			// From N on, one step up stays in the span: H(x)/F(x)^(a+1) = p/F(x)^a + t·q/F(x)^a.
			descend := a.Have(
				"from N on, the forms over F(x)^(a+1) lie in the span once the forms over F(x)^a do",
				"∀a:num. N ≤ a ∧ «formsOver»(a) ⊆ «span» ⇒ «formsOver»(suc(a)) ⊆ «span»",
				Derive(func(b *Argument) {
					e := b.FixAs[Nat]("a")
					assumed := b.Conjuncts(
						b.Assume(),
						"a is past N",
						"the forms over F(x)^a lie in the span")
					formsA := b.Conjuncts(
						GroupPremises(
							kSub, KSub, generic, fForm, fNonzero, FormsOverSubspace.Read(M).At(k, K, n, r, e, E, x, F)),
						"the forms over F(x)^a are the values of degree r·a over F(x)^a",
						"a k-subspace of M",
						"of finite dimension",
						"namely h(r·a)")
					up := b.Have(
						"each member of the forms over F(x)^(a+1) lies in the span",
						"∀y:A. y ∈ «formsOver»(suc(a)) ⇒ y ∈ «span»",
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							member := c.Conjuncts(
								c.Assume(),
								"y lies in K",
								"y·F(x)^(a+1) is the value of a form of degree r·(a + 1)")
							_, rep := c.UnpackAs[Fun[Fun[Nat, Nat], A]](member[1], "H")
							repParts := c.Conjuncts(
								rep,
								"H is a form of degree r·(a + 1)",
								"y·F(x)^(a+1) = H(x)")
							H := c.TermAs[Fun[Fun[Nat, Nat], A]]("H")
							degrees := c.Conjuncts(
								c.Have(
									"r·(a + 1) = r·a + r, and N ≤ r·a",
									"r * suc(a) = r * a + r ∧ N ≤ r * a",
									ByArith(positive, assumed[0], nat_order.LessEqSelfMul.At(e, r))),
								"r·(a + 1) = r·a + r",
								"N ≤ r·a")
							valueIn := c.Have(
								"H(x) is a value of degree r·a + r",
								"«at»(H) ∈ «values»(r * a + r)",
								degrees[0].RwRev(),
								By(
									repParts[0],
									set_image.FunInImage.At(
										at,
										c.TermAs[Set[Fun[Fun[Nat, Nat], A]]](
											"{P:((num → num) → A) | homogeneous_polynomial(«hilbertCoefficients», n, r * suc(a), P)}"),
										H)))
							p, q, split := c.Unpack2As[A, A](
								GroupPremises(degrees[1], valueIn, generate.At(c.TermAs[Nat]("r * a"), c.TermAs[A]("«at»(H)"))),
								"p",
								"q")
							splitParts := c.Conjuncts(
								split,
								"p is a value of degree r·a",
								"so is q",
								"H(x) = F(x)·p + G(x)·q")
							scale := c.TermAs[Fun[A, A]]("M.mul(monoid_pow(M.mul, M.one, M.inv(«at»(F)), a))")
							valuesA := c.TermAs[Set[A]]("«values»(r * a)")
							lowered := c.Conjuncts(
								c.Have(
									"p/F(x)^a and q/F(x)^a lie in the forms over F(x)^a, so in the span",
									"monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * p ∈ «span» ∧ "+
										"monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * q ∈ «span»",
									BySets(
										formsA[0],
										assumed[1],
										splitParts[0],
										splitParts[1],
										set_image.FunInImage.At(scale, valuesA, p),
										set_image.FunInImage.At(scale, valuesA, q))),
								"p/F(x)^a lies in the span",
								"so does q/F(x)^a")
							pqInM := c.Have(
								"y, p and q lie in M",
								"y ∈ M.carrier ∧ p ∈ M.carrier ∧ q ∈ M.carrier",
								BySets(member[0], KInM, splitParts[0], splitParts[1], valuesInM))
							powerA := comm_monoid.PowIn.Read(monoid).At(fm, e)
							powersCancel := c.Have(
								"F(x)^(−a)·F(x)^a = 1",
								"monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * monoid_pow(M.mul, M.one, «at»(F), a) = M.one",
								By(cancel, comm_monoid.PowInverseOn.Read(monoid).At(fInverse, fm, e)))
							successor := c.Have(
								"F(x)^(a+1) = F(x)·F(x)^a",
								"monoid_pow(M.mul, M.one, «at»(F), suc(a)) = «at»(F) * monoid_pow(M.mul, M.one, «at»(F), a)",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								ByArith(M, members[0], powerA))
							cleared := c.Have(
								"y·F(x)·F(x)^a = F(x)·p + G(x)·q",
								"y * («at»(F) * monoid_pow(M.mul, M.one, «at»(F), a)) = «at»(F) * p + «at»(G) * q",
								successor.RwRev(),
								By(repParts[1], splitParts[2]))
							recovered := c.Have(
								"so y = p/F(x)^a + t·q/F(x)^a",
								"y = "+
									"monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * p + "+
									"«parameter» * (monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * q)",
								ByArith(
									M,
									members[0],
									members[1],
									members[2],
									pqInM,
									comm_monoid.PowIn.Read(monoid).At(fInverse, e),
									powerA,
									Scaled(c.TermAs[A]("y * M.inv(«at»(F)) * «at»(F)"), powersCancel),
									Scaled(y, cancel),
									Scaled(c.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * M.inv(«at»(F))"), cleared),
									Scaled(c.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * p"), cancel)))
							pLowered := c.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * p")
							qLowered := c.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * q")
							scaled := c.Have(
								"t·q/F(x)^a lies in the span, t being a member of k[t]",
								"«parameter» * (monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * q) ∈ «span»",
								By(lineFacts[2], lowered[1], submodule.SubmoduleSmul.Read(spanFacts[0]).AsFact().At(t, qLowered)))
							c.Show(
								"so y, the sum of two members of the span, lies in it",
								By(
									recovered,
									lowered[0],
									scaled,
									submodule.SubmoduleAdd.Read(spanFacts[0]).AsFact().At(
										pLowered, c.TermAs[A]("«parameter» * (monoid_pow(M.mul, M.one, M.inv(«at»(F)), a) * q)"))))
						}))
					b.Show(
						"so the forms over F(x)^(a+1) lie in the span",
						BySets(up))
				}))
			upper := a.Have(
				"so the forms over F(x)^(N+c) lie in the span for every c",
				"∀c:num. «formsOver»(N + c) ⊆ «span»",
				Derive(func(b *Argument) {
					b.Induct("c")
					b.Base(
						"at c = 0 they are the forms over F(x)ᴺ",
						func(c *Argument) {
							c.Show(
								"which lie in the span",
								c.Have(
									"N + 0 = N",
									"N + 0 = N",
									ByArith()).Rw(),
								By(formsInSpan))
						})
					b.Step(
						"one step past N + c stays in the span",
						func(c *Argument, ih Fact) {
							c.Show(
								"N + (c + 1) is the successor of N + c, past N",
								c.Have(
									"N + suc(c) = suc(N + c)",
									"N + suc(c) = suc(N + c)",
									ByArith()).Rw(),
								By(ih, nat_order.LessEqAdd, descend))
						})
				}))
			inSpan := a.Have(
				"each member of the chart lies in the span: a member over F(x)^a lies over F(x)^(N+a)",
				"∀y:A. y ∈ «chart»(F) ⇒ y ∈ «span»",
				Derive(func(c *Argument) {
					y := c.FixAs[A]("y")
					member := c.Conjuncts(
						c.Assume(),
						"y lies in K",
						"y·F(x)^a is the value of a form of degree r·a")
					e, _, rep := c.Unpack2As[Nat, Fun[Fun[Nat, Nat], A]](member[1], "a", "P")
					over := c.Have(
						"so y lies in the forms over F(x)^a",
						"y ∈ «formsOver»(a)",
						BySets(member[0], rep))
					later := c.Have(
						"and in those over F(x)^(a+N), which are those over F(x)^(N+a)",
						"y ∈ «formsOver»(N + a)",
						c.Have(
							"a + N = N + a",
							"a + N = N + a",
							ByArith()).RwRev(),
						By(over, shift.At(e, N, y)))
					c.Show(
						"which lie in the span",
						BySets(later, upper.At(e)))
				}))
			spanInChart := a.Have(
				"and the span lies in the chart",
				"«span» ⊆ «chart»(F)",
				By(spanFacts[0], submodule.SubmoduleSubset))
			chartInSpan := a.Have(
				"so the chart lies in the span",
				"«chart»(F) ⊆ «span»",
				BySets(inSpan))
			spanIsChart := a.Have(
				"so the span is the chart",
				"«span» = «chart»(F)",
				By(spanInChart, chartInSpan, set_order.SubsetAntisym))
			a.Show(
				"so S₀, finite and inside the chart, generates it over k[t]",
				Unfold(principal_ideal_domain.FinitelyGeneratedDef),
				Witness(S0),
				By(spanParts[0], S0InChart, spanIsChart))
		}),
})}

// ChartFreeOverLine — the chart of F is free of finite rank over k[t],
// t = G(x)/F(x): it holds k[t], a principal ideal domain
// (principal_ideal_domain.PolynomialImagePrincipalIdealDomain) and finite
// over itself, so it is a k[t]-submodule of the field M, finitely generated
// over k[t] (ChartFinitelyGenerated); such a submodule of a field is free of
// finite rank (principal_ideal_domain.FinitelyGeneratedFree).
var ChartFreeOverLine = chartFreeOverLineThm{family.Add(registry.ProofEntry{
	Name: "ChartFreeOverLine",
	Key:  "prop_4afe267b6992a175",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"«noCommonZero»",
		},
		Conclusion: "∃B:set(A). " +
			"    finite(B) ∧ " +
			"    module_basis(restrict_ring(field_ring(M), «line»), " +
			"        restrict_module(regular_module(field_ring(M)), «chart»(F)), " +
			"        B)",
		Abbrev: Abbrev{
			{Name: "line", Text: "polynomial_image(field_ring(M), k, «parameter»)"},
		},
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			closed, curve, KSub, generic, fForm, gForm, positive, fNonzero, noCommonZero Fact,
		) {
			ring := field.RingOn.Read(M)
			ops := a.TermAs[FieldOps[A]]("M")
			line := a.TermAs[Set[A]]("«line»")
			chartF := a.TermAs[Set[A]]("«chart»(F)")
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			scalars := a.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «line»)")
			lineVectors := a.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(M)), «line»)")
			kSub := a.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			point := a.Conjuncts(
				generic,
				"x is a point of the curve over K",
				"whose coordinates generate K over k",
				"where a form vanishes exactly when it lies in the ideal")
			coordinates := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates generate over k",
				"k ⊆ K",
				BySets(
					point[1],
					kSub,
					coordinates,
					KInM,
					field.SubfieldSubset.At(ops, k),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			coordinatesInM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			chart := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinatesInM,
					fForm,
					projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
				"the chart of F is a subring of M",
				"holding k")
			tInChart := a.Have(
				"t lies in the chart of F",
				"«parameter» ∈ «chart»(F)",
				By(GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					fForm,
					gForm,
					fNonzero,
					ParameterInChart.Read(M).At(k, K, n, r, x, F, G))))
			chartInM := a.Have(
				"the chart lies in M",
				"«chart»(F) ⊆ M.carrier",
				By(chart[0], comm_ring.SubringSubset))
			tm := a.MemberOf[on.M](a.TermAs[A]("«parameter»"), a.Have(
				"so t lies in M",
				"«parameter» ∈ M.carrier",
				BySets(tInChart, chartInM)))
			lineFacts := a.Conjuncts(
				GroupPremises(kSub, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)),
				"k[t] is a subring of M",
				"holding k",
				"and t",
				"inside the field k(t)")
			chartRing := a.Have(
				"the chart of F is a ring under M's operations",
				"comm_ring_on(restrict_ring(field_ring(M), «chart»(F)))",
				By(chart[0], comm_ring.SubringRingOn.Read(ring).At(chartF)))
			lineInChart := a.Have(
				"k[t] lies in the chart, a ring holding k and t",
				"«line» ⊆ «chart»(F)",
				By(
					chartRing,
					chart[1],
					tInChart,
					algebraic_element.PolynomialImageLeast.Read(M).At(k, chartF, a.TermAs[A]("«parameter»"))))
			principal := a.Have(
				"k[t] is a principal ideal domain",
				"principal_ideal_domain(restrict_ring(field_ring(M), «line»))",
				By(kSub, principal_ideal_domain.PolynomialImagePrincipalIdealDomain.Read(M).At(k, tm)))
			generated := a.Have(
				"the chart is finitely generated over k[t]",
				"module_finitely_generated(restrict_ring(field_ring(M), «line»), "+
					"    restrict_module(regular_module(field_ring(M)), «chart»(F)))",
				By(GroupPremises(
					closed,
					curve,
					KSub,
					generic,
					fForm,
					gForm,
					positive,
					fNonzero,
					noCommonZero,
					ChartFinitelyGenerated.Read(M).At(k, K, n, r, E, x, F, G))))
			finiteBasis := a.Have(
				"{1} is a finite basis of k[t] over itself",
				"∃B:set(A). "+
					"    finite(B) ∧ "+
					"    module_basis(restrict_ring(field_ring(M), «line»), "+
					"        restrict_module(regular_module(field_ring(M)), «line»), "+
					"        B)",
				Witness(a.TermAs[Set[A]]("{M.one}")),
				By(
					lineFacts[0],
					comm_ring.SubringRingOn.Read(ring).At(line),
					linear_independence.RegularModuleBasis.At(scalars),
					module_record.RegularModuleRestrict.At(fieldRing, line),
					finite_set.FiniteSing.At(a.TermAs[A]("M.one"))))
			a.Show(
				"so the chart, a finitely generated k[t]-submodule of the field "+
					"M, is free of finite rank over the principal ideal domain k[t]",
				By(
					set_order.SubsetRefl.At(line),
					lineFacts[0],
					principal,
					finiteBasis,
					principal_ideal_domain.FiniteBasisFinitelyGenerated.At(scalars, lineVectors),
					chart[0],
					lineInChart,
					principal_ideal_domain.ConstantSubringSubmodule.Read(M).At(line, chartF),
					generated,
					principal_ideal_domain.FinitelyGeneratedFree.Read(M).At(line, line, chartF)))
		}),
})}

// FormChartsAreCurve — two forms F, G of one positive degree over k, nonzero
// at the generic point and without a common zero on the curve, give a curve
// over the line: the charts are the rings of the open sets where F and
// where G does not vanish, the coordinate t = G(x)/F(x), and the overlap
// the first chart with t inverted. Each clause of the datum is one of the
// parts: k is a subfield of K, t a member of K transcendental over k
// (ParameterTranscendental), the overlap a part of K along which the charts
// glue (ChartsBiaffine), each chart holds and is free over its line
// (ChartFreeOverLine, read at F, G and at G, F, where the coordinate
// F(x)/G(x) is 1/t by ParameterInverse), the charts meet in k
// (ChartsMeetInConstants), and K is the field of fractions of the first
// (ChartFractionField).
var FormChartsAreCurve = formChartsAreCurveThm{family.Add(registry.ProofEntry{
	Name: "FormChartsAreCurve",
	Key:  "prop_3d076da11b6e77d8",
	Reading: "The charts are the curve's own, not a normalization: nothing here asks them to " +
		"be integrally closed. The no-common-zero hypothesis is what makes them cover the curve: " +
		"through projective_form_pair.CoprimeValuesGenerate each chart is finite over its line " +
		"(ChartFreeOverLine), so the chart of F misses no point over the line, and through " +
		"projective_sections.SectionsAreForms the two charts meet in k (ChartsMeetInConstants).",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K:set(A). " +
			"∀n r:num. " +
			"∀E:set((num → num) → A). " +
			"∀x:(num → A). " +
			"∀F G:((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"smooth_projective_equation_curve(M, k, n, E)",
			"subfield(M, K)",
			"«genericPoint»(x)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, F)",
			"homogeneous_polynomial(«hilbertCoefficients», n, r, G)",
			"0 < r",
			"«at»(F) ≠ M.zero",
			"«at»(G) ≠ M.zero",
			"«noCommonZero»",
		},
		Conclusion: "curve_over_line(restrict_field(M, K), " +
			"    k, " +
			"    «parameter», " +
			"    «chart»(F), " +
			"    «chart»(G), " +
			"    «overlap»)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, K *Expr[Set[A]],
			n, r *Expr[Nat],
			E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
			x *Arrow[Nat, A],
			F, G *Arrow[Fun[Nat, Nat], A],
			closed, curve, KSub, generic, fForm, gForm, positive, fNonzero, gNonzero, noCommonZero Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("M")
			ring := field.RingOn.Read(M)
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			chartF, chartG := a.TermAs[Set[A]]("«chart»(F)"), a.TermAs[Set[A]]("«chart»(G)")
			t, inverse := a.TermAs[A]("«parameter»"), a.TermAs[A]("M.inv(«parameter»)")
			kSub := a.Have(
				"k is a subfield of M",
				"subfield(M, k)",
				By(projective_curve.CurveConstantsSubfield.Read(curve)))
			point := a.Conjuncts(
				generic,
				"x is a point of the curve over K",
				"whose coordinates generate K over k",
				"where a form vanishes exactly when it lies in the ideal")
			coordinates := a.Have(
				"the coordinates of x up to n lie in K",
				"∀i:num. i ≤ n ⇒ x(i) ∈ K",
				By(point[0], projective_curve.PointCoordinatesIn))
			KInM := a.Have(
				"K lies in M",
				"K ⊆ M.carrier",
				By(KSub, field.SubfieldSubset))
			kInK := a.Have(
				"k lies in K, the field the coordinates generate over k",
				"k ⊆ K",
				BySets(
					point[1],
					kSub,
					coordinates,
					KInM,
					field.SubfieldSubset.At(ops, k),
					algebraic_element.AdjoinSubfield.Read(M).At(k, a.TermAs[Set[A]]("{x(i) | i:num | i ≤ n}"))))
			coordinatesInM := a.Have(
				"the coordinates of x up to n lie in M",
				"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
				BySets(coordinates, KInM))
			constants := a.Have(
				"so k is a subfield of K",
				"subfield(restrict_field(M, K), k)",
				By(kSub, kInK, field.SubfieldRestrict.At(ops, K, k)))

			// The parameter and the gluing.
			biaffine := a.Have(
				"glued along the overlap the charts are biaffine",
				"biaffine(restrict_ring(field_ring(M), «overlap»), "+
					"    «chart»(F), "+
					"    «chart»(G), "+
					"    «parameter», "+
					"    M.inv(«parameter»))",
				By(GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinates,
					fForm,
					gForm,
					fNonzero,
					gNonzero,
					ChartsBiaffine.Read(M).At(k, K, n, r, x, F, G))))
			units := a.Conjuncts(
				a.Have(
					"t lies in the chart of F and 1/t in the chart of G",
					"«parameter» ∈ «chart»(F) ∧ M.inv(«parameter») ∈ «chart»(G)",
					By(biaffine, lattice_pair.BiaffineDef)),
				"t lies in the chart of F",
				"1/t lies in the chart of G")
			tInK := a.Have(
				"t lies in K, as the chart of F does",
				"«parameter» ∈ K",
				BySets(units[0]))
			transcendental := a.Have(
				"t is transcendental over k",
				"¬algebraic_over(M, k, «parameter»)",
				By(GroupPremises(
					closed,
					curve,
					KSub,
					generic,
					fForm,
					gForm,
					positive,
					fNonzero,
					gNonzero,
					noCommonZero,
					ParameterTranscendental.Read(M).At(k, K, n, r, E, x, F, G))))
			overlapInK := a.Have(
				"the overlap lies in K, its members being members of K",
				"«overlap» ⊆ K",
				Unfold(ring_away.RingAwayDef),
				BySets())

			// Each chart holds its line and is free of finite rank over it.
			chartsF := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinatesInM,
					fForm,
					projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, F)),
				"the chart of F is a subring of M",
				"holding k")
			chartsG := a.Conjuncts(
				GroupPremises(
					kSub,
					KSub,
					kInK,
					coordinatesInM,
					gForm,
					projective_curve.ChartSubring.Read(M).At(k, K, n, r, x, G)),
				"the chart of G is a subring of M",
				"holding k")
			ringF, ringG :=
				comm_ring.SubringRingOn.Read(ring).At(chartF), comm_ring.SubringRingOn.Read(ring).At(chartG)
			lineInF := a.Have(
				"the chart of F holds k[t], a ring holding k and t",
				"polynomial_image(field_ring(M), k, «parameter») ⊆ «chart»(F)",
				By(
					chartsF[0],
					ringF,
					chartsF[1],
					units[0],
					algebraic_element.PolynomialImageLeast.Read(M).At(k, chartF, t)))
			lineInG := a.Have(
				"and the chart of G holds k[1/t], a ring holding k and 1/t",
				"polynomial_image(field_ring(M), k, M.inv(«parameter»)) ⊆ «chart»(G)",
				By(
					chartsG[0],
					ringG,
					chartsG[1],
					units[1],
					algebraic_element.PolynomialImageLeast.Read(M).At(k, chartG, inverse)))
			freeF := a.Have(
				"the chart of F is free of finite rank over k[t]",
				"∃B:set(A). "+
					"    finite(B) ∧ "+
					"    module_basis(restrict_ring(field_ring(M), polynomial_image(field_ring(M), k, «parameter»)), "+
					"        restrict_module(regular_module(field_ring(M)), «chart»(F)), "+
					"        B)",
				By(GroupPremises(
					closed,
					curve,
					KSub,
					generic,
					fForm,
					gForm,
					positive,
					fNonzero,
					noCommonZero,
					ChartFreeOverLine.Read(M).At(k, K, n, r, E, x, F, G))))
			inverseIs := a.Have(
				"1/t is F(x)/G(x)",
				"M.inv(«parameter») = «at»(F) * M.inv(«at»(G))",
				By(GroupPremises(
					kSub, KSub, kInK, coordinates, fForm, gForm, ParameterInverse.Read(M).At(k, K, n, r, x, F, G))))
			freeG := a.Have(
				"and the chart of G over k[1/t], 1/t being F(x)/G(x)",
				"∃B:set(A). "+
					"    finite(B) ∧ "+
					"    module_basis( "+
					"        restrict_ring(field_ring(M), polynomial_image(field_ring(M), k, M.inv(«parameter»))), "+
					"        restrict_module(regular_module(field_ring(M)), «chart»(G)), "+
					"        B)",
				inverseIs.Rw(),
				By(
					closed,
					curve,
					KSub,
					generic,
					gForm,
					fForm,
					positive,
					gNonzero,
					noCommonZero,
					ChartFreeOverLine.Read(M).At(k, K, n, r, E, x, G, F)))

			// The charts meet in k, and K is the field of fractions of the first.
			meet := a.Have(
				"the charts meet in k",
				"«chart»(F) ∩ «chart»(G) = k",
				By(GroupPremises(
					closed,
					curve,
					KSub,
					generic,
					fForm,
					gForm,
					positive,
					fNonzero,
					gNonzero,
					noCommonZero,
					ChartsMeetInConstants.Read(M).At(k, K, n, r, E, x, F, G))))
			hasOne := a.Have(
				"some coordinate up to n is one",
				"∃j:num. j ≤ n ∧ x(j) = M.one",
				By(point[0], projective_curve.PointLeadingOne.At(fieldRing, k, K, n, E, x)))
			fractions := a.Have(
				"K is the field of fractions of the chart of F",
				"fraction_field_carrier(restrict_ring(field_ring(M), K), «chart»(F))",
				By(GroupPremises(
					kSub,
					KSub,
					coordinates,
					hasOne,
					point[1],
					fForm,
					positive,
					fNonzero,
					ChartFractionField.Read(M).At(k, K, n, r, x, F))))
			overlap := a.TermAs[Set[A]]("«overlap»")
			lineF := a.TermAs[Set[A]]("polynomial_image(field_ring(M), k, «parameter»)")
			lineG := a.TermAs[Set[A]]("polynomial_image(field_ring(M), k, M.inv(«parameter»))")
			a.Show(
				"read in K, whose operations are M's, each clause of the curve over the line is one of these",
				Unfold(algebraic_curve.CurveOverLineDef),
				SplitConjAll(
					Case(
						"k is a subfield of K",
						By(constants)),
					Case(
						"t lies in K",
						By(tInK)),
					Case(
						"t is transcendental over k",
						By(transcendental, algebraic_element.RestrictFieldReadings.At(ops, K, k, t))),
					Case(
						"the overlap lies in K",
						By(overlapInK)),
					Case(
						"the charts are biaffine, glued along the overlap",
						By(biaffine, field.RestrictFieldRecords.At(ops, K, overlap))),
					Case(
						"k[t] lies in the chart of F",
						By(lineInF, algebraic_element.RestrictFieldReadings.At(ops, K, k, t))),
					Case(
						"k[1/t] lies in the chart of G",
						By(lineInG, algebraic_element.RestrictFieldReadings.At(ops, K, k, inverse))),
					Case(
						"the chart of F has a finite basis over k[t]",
						By(
							freeF,
							algebraic_element.RestrictFieldReadings.At(ops, K, k, t),
							field.RestrictFieldRecords.At(ops, K, lineF),
							field.RestrictFieldRecords.At(ops, K, chartF))),
					Case(
						"the chart of G has a finite basis over k[1/t]",
						By(
							freeG,
							algebraic_element.RestrictFieldReadings.At(ops, K, k, inverse),
							field.RestrictFieldRecords.At(ops, K, lineG),
							field.RestrictFieldRecords.At(ops, K, chartG))),
					Case(
						"the charts meet in k",
						By(meet)),
					Case(
						"K is the field of fractions of the chart of F",
						By(fractions, field.RestrictFieldRing.At(ops, K)))))
		}),
})}
