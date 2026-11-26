// signs_at_infinity.go — the signs of a polynomial far out on either side.
// These members assume only an ordered field: past some positive bound a
// monic polynomial is at least one, and a nonzero polynomial has the sign of
// its leading coefficient at x and, times (−1)^deg, at −x.

package ordered_field_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// MonicEventuallyAtLeastOne — past some positive bound a monic polynomial
// over an ordered field takes values at least one. By induction on the
// degree: a monic p of degree d + 1 is p(0) + x·q(x) with q(i) = p(i + 1)
// monic of degree d, and once x lies past q's bound and past 1 − p(0), the
// value x·q(x) + p(0) is at least x + p(0), which exceeds one.
var MonicEventuallyAtLeastOne = monicEventuallyAtLeastOneThm{family.Add(registry.ProofEntry{
	Name: "MonicEventuallyAtLeastOne",
	Key:  "prop_999ea8dfc3a92656",
	Build: ordered_field.OrderedFieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_monic(p)",
		},
		Conclusion: "∃b:A. " +
			"    b ∈ F.carrier ∧ " +
			"    lt(F.zero, b) ∧ " +
			"    (∀x:A. x ∈ F.carrier ∧ lt(b, x) ⇒ ordered_le(lt, F.one, polynomial_eval(p, x)))",
	}, func(
		arg *Argument,
		ordered ordered_field.OrderedFieldFact[on.F],
		p *Arrow[Nat, A],
		over, monic Fact,
	) {
		lt := arg.TermAs[Fun2[A, A, Bool]]("lt")
		transitive := ordered_field.Transitive.Read(ordered)
		comparable := ordered_field.Trichotomy.Read(ordered)
		translation := ordered_field.AddPreservesOrder.Read(ordered)
		fieldF := ordered_field.FieldOn.Read(ordered)
		ring := field.RingOn.Read(fieldF)
		zero := arg.MemberOf[on.F](arg.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		one := arg.MemberOf[on.F](arg.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		carrier := arg.TermAs[Set[A]]("F.carrier")
		onePositive := ordered_field.OnePositive.Read(ordered)
		growth := arg.Have(
			"by induction on d, a monic polynomial of degree d is at least one past some positive bound",
			Statement{
				Binders: "∀d:num. ∀f:(num → A).",
				Hypotheses: []string{
					"polynomial_over(F.carrier, f)",
					"polynomial_monic(f)",
					"polynomial_degree(f) = d",
				},
				Conclusion: "∃b:A. " +
					"    b ∈ F.carrier ∧ " +
					"    lt(F.zero, b) ∧ " +
					"    (∀x:A. x ∈ F.carrier ∧ lt(b, x) ⇒ ordered_le(lt, F.one, polynomial_eval(f, x)))",
			},
			Derive(func(a *Argument) {
				degree := a.FixAs[Nat]("d")
				a.Induct(degree)
				a.Base(
					"a monic polynomial of degree zero is the constant one, at least one everywhere",
					func(b *Argument) {
						b.FixAs[Fun[Nat, A]]("f")
						given := b.Conjuncts(
							b.Assume(),
							"f is a polynomial over F",
							"f is monic",
							"f has degree zero")
						value := b.Have(
							"f takes its constant coefficient, one, at every point of F",
							"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(f, x) = F.one",
							By(
								given[0],
								given[1],
								given[2],
								polynomial.PolynomialMonicDef,
								polynomial_evaluation.DegreeZeroEval.Read(ring)))
						b.Take(one)
						b.Show(
							"one is a positive point of F, and every value of f is one",
							By(value, onePositive, ordered, one, ordered_field.OrderedLeDef))
					})
				a.Step(
					"a monic polynomial of degree d + 1 is f(0) + x·q(x), with q monic of degree d",
					func(b *Argument, ih Fact) {
						f := b.FixAs[Fun[Nat, A]]("f")
						given := b.Conjuncts(
							b.Assume(),
							"f is a polynomial over F",
							"f is monic",
							"f has degree d + 1")
						fOver, fMonic, fDegree := given[0], given[1], given[2]
						coefficients := polynomial.CoefficientIn.Read(fOver)
						f0 := b.MemberOf[on.F](b.TermAs[A]("f(0)"), coefficients.At(b.TermAs[Nat]("0")))
						lead := b.Have(
							"f is monic of degree d + 1, so its coefficient there is one",
							"f(suc(d)) = F.one",
							By(Normalized, fDegree, fMonic, polynomial.PolynomialMonicDef))
						past := b.Unfolded(
							b.Have(
								"f vanishes past its degree d + 1",
								"vec⟨suc(suc(d))⟩(f)",
								By(Normalized, fDegree, fOver, polynomial.DegreeVec.At(zero, carrier, f))),
							vec_space.VecDef)
						q, qDef := b.LetAs[Fun[Nat, A]]("q", "λi:num. f(suc(i))")
						qVec := b.Have(
							"q vanishes past d",
							"vec⟨suc(d)⟩(q)",
							Simp(Fwd(vec_space.VecDef)),
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								beyond := d.Assume()
								d.Show(
									"q(i) is f(i + 1), and i + 1 lies past d + 1",
									By(
										Normalized,
										qDef,
										beyond,
										past.At(d.TermAs[Nat]("suc(i)")),
										nat_order.SucLessEqSucIff.At(d.TermAs[Nat]("suc(d)"), i)))
							}))
						qCoefficients := b.Have(
							"each coefficient of q is a coefficient of f, so lies in F",
							"∀i:num. q(i) ∈ F.carrier",
							By(qDef, coefficients))
						qOver := b.Have(
							"so q is a polynomial over F",
							"polynomial_over(F.carrier, q)",
							By(Normalized, qVec, qCoefficients, polynomial.PolynomialOverDef.At(zero, carrier, q)))
						qDegree := b.Have(
							"q has degree d: it vanishes past d, and q(d) = f(d + 1) = 1 is not zero",
							"polynomial_degree(q) = d",
							By(
								qOver,
								qVec,
								qDef,
								lead,
								field.OneNotZeroOn.Read(fieldF),
								polynomial.DegreeExact.At(zero, carrier, q, degree)))
						qMonic := b.Have(
							"and q is monic, its coefficient at d being f(d + 1) = 1",
							"polynomial_monic(q)",
							By(Normalized, qDegree, qDef, lead, polynomial.PolynomialMonicDef))
						c, bounded := b.UnpackAs[A](GroupPremises(qOver, qMonic, qDegree, ih.At(q)), "c")
						qFar := b.Conjuncts(
							bounded,
							"c lies in F",
							"c is positive",
							"past c, q is at least one")
						cIn, cPositive, qAtLeast := qFar[0], qFar[1], qFar[2]
						cm := b.MemberOf[on.F](c, cIn)
						horner := b.Have(
							"f is its constant term plus q times the variable",
							"f = f(0) • basis_vector(0) + polynomial_mul(q, basis_vector(1))",
							Funext(),
							Derive(func(d *Argument) {
								j := d.FixAs[Nat]("j")
								d.Do(
									Simp(Fwd(vec_space.VecAddDef), Fwd(polynomial.PolynomialMulBasisVector.Read(ring))),
									Simp(Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)))
								d.Cases(d.TermAs[Bool]("j = 0"))
								d.When(
									"at index zero only the constant term contributes",
									func(e *Argument, isZero Fact) {
										e.Show(
											"f(0) = f(0)·1 + 0",
											ByArith(ring, isZero, f0))
									})
								d.Otherwise(
									"past index zero only q times the variable contributes",
									func(e *Argument, nonzero Fact) {
										previous := e.TermAs[Nat]("j - 1")
										shift := e.Have(
											"q(j − 1) is f(j)",
											"q(j - 1) = f(j)",
											By(nonzero, qDef, nat_monus.SucOfSubOne.At(j)))
										e.Show(
											"f(j) = f(0)·0 + q(j − 1)",
											ByArith(ring, nonzero, shift, f0, qCoefficients.At(previous)))
									})
							}))
						variable := b.TermAs[Fun[Nat, A]]("basis_vector(1)")
						pieces := b.Have(
							"the constant term and q times the variable are polynomials over F",
							"polynomial_over(F.carrier, f(0) • basis_vector(0)) ∧ "+
								"polynomial_over(F.carrier, polynomial_mul(q, basis_vector(1)))",
							BySets(
								f0,
								qOver,
								polynomial.BasisVectorOver.Read(ring),
								module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
								polynomial.PolynomialMulOver.Read(ring)))
						value := b.Have(
							"so f takes the value x·q(x) + f(0) at every point x of F",
							"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(f, x) = x * polynomial_eval(q, x) + f(0)",
							Derive(func(d *Argument) {
								x := d.FixAs[A]("x")
								xIn := d.MemberOf[on.F](x, d.Assume())
								qValue := d.Have(
									"q takes a value in F at x",
									"polynomial_eval(q, x) ∈ F.carrier",
									By(qOver, polynomial_evaluation.EvalIn.Read(ring).At(q, xIn)))
								d.Show(
									"evaluation at x adds the value f(0) of the constant term to q(x) times x",
									CalcEq(
										Leg(
											d.TermAs[A]("polynomial_eval(f(0) • basis_vector(0) + polynomial_mul(q, basis_vector(1)), x)"),
											"write f as its constant term plus q times the variable",
											By(Normalized, horner)),
										Leg(
											d.TermAs[A]("f(0) + polynomial_eval(q, x) * monoid_pow(F.mul, F.one, x, 1)"),
											"evaluation takes the sum and the product to the values' sum and product",
											By(
												pieces,
												qOver,
												polynomial_evaluation.EvalAdd.Read(ring).At(
													d.TermAs[Fun[Nat, A]]("f(0) • basis_vector(0)"),
													d.TermAs[Fun[Nat, A]]("polynomial_mul(q, basis_vector(1))"),
													xIn),
												polynomial_evaluation.EvalConstant.Read(ring).At(f0, xIn),
												polynomial_evaluation.EvalMul.Read(ring).At(q, variable, xIn),
												polynomial_evaluation.EvalBasisVector.Read(ring).At(d.TermAs[Nat]("1"), xIn),
												polynomial.BasisVectorOver.Read(ring).At(d.TermAs[Nat]("1")))),
										FinalLeg(
											"x¹ is x, and the sum and the product reorder",
											ByArith(ring, xIn, qValue, f0))))
							}))
						s := comm_ring.SubIn.Read(ring).At(one, f0)
						m, above := b.ObtainAs[A](
							"some point m of F lies past both c and 1 − f(0)",
							"∃m:A. m ∈ F.carrier ∧ lt(c, m) ∧ lt(F.one - f(0), m)",
							Derive(func(d *Argument) {
								d.Cases(d.TermAs[Bool]("lt(c, F.one - f(0))"))
								d.When(
									"1 − f(0) lies past c, and 1 + (1 − f(0)) past both",
									func(e *Argument, below Fact) {
										beyond := comm_ring.AddIn.Read(ring).At(one, s)
										e.Take(beyond)
										e.Show(
											"one is positive, so 1 + (1 − f(0)) lies past 1 − f(0), and so past c",
											By(
												below,
												onePositive,
												ordered_field.LessThanSelfAddLeft.Read(ordered).At(one, s),
												transitive.At(cm, s, beyond)))
									})
								d.Otherwise(
									"1 − f(0) lies at or below c, and 1 + c past both",
									func(e *Argument, notBelow Fact) {
										beyond := comm_ring.AddIn.Read(ring).At(one, cm)
										e.Take(beyond)
										e.Show(
											"one is positive, so 1 + c lies past c, and so past 1 − f(0)",
											By(
												notBelow,
												onePositive,
												ordered_field.LessThanSelfAddLeft.Read(ordered).At(one, cm),
												comparable.At(cm, s),
												transitive.At(s, cm, beyond)))
									})
							}))
						mParts := b.Conjuncts(
							above,
							"m lies in F",
							"m lies past c",
							"m lies past 1 − f(0)")
						mIn, pastC, pastS := mParts[0], mParts[1], mParts[2]
						mm := b.MemberOf[on.F](m, mIn)
						farValues := b.Have(
							"past m, f is at least one",
							"∀x:A. x ∈ F.carrier ∧ lt(m, x) ⇒ ordered_le(lt, F.one, polynomial_eval(f, x))",
							Derive(func(d *Argument) {
								x := d.FixAs[A]("x")
								xFacts := d.Conjuncts(
									d.Assume(),
									"x lies in F",
									"x lies past m")
								xIn, xPast := xFacts[0], xFacts[1]
								xm := d.MemberOf[on.F](x, xIn)
								qx := d.TermAs[A]("polynomial_eval(q, x)")
								qxIn := d.Have(
									"q takes a value in F at x",
									"polynomial_eval(q, x) ∈ F.carrier",
									By(qOver, xIn, polynomial_evaluation.EvalIn.Read(ring)))
								qxm := d.MemberOf[on.F](qx, qxIn)
								scaledX := comm_ring.MulIn.Read(ring).At(xm, qxm)
								arithmetic := d.Have(
									"the ring arithmetic of the comparison",
									"F.one * x = x ∧ "+
										"polynomial_eval(q, x) * x = x * polynomial_eval(q, x) ∧ "+
										"F.one - f(0) + f(0) = F.one",
									ByArith(ring, xIn, qxIn, f0))
								positions := d.Have(
									"x lies past c and past 1 − f(0), and so above zero",
									"lt(c, x) ∧ lt(F.one - f(0), x) ∧ lt(F.zero, x)",
									By(
										xPast,
										pastC,
										pastS,
										cPositive,
										transitive.At(cm, mm, xm),
										transitive.At(s, mm, xm),
										transitive.At(zero, cm, xm)))
								scaled := d.Have(
									"q(x) is at least one and x is positive, so x·q(x) is at least x",
									"ordered_le(lt, x, x * polynomial_eval(q, x))",
									By(
										qAtLeast.At(x),
										xm,
										xPast,
										positions,
										arithmetic,
										qxm,
										ordered_field.PositiveMulOrderIff.Read(ordered).At(one, qxm, xm),
										ordered_field.OrderedLeDef.At(lt, one, qx),
										ordered_field.OrderedLeDef.At(lt, x, scaledX)))
								shifted := d.Have(
									"translating 1 − f(0) < x by f(0) puts x + f(0) above one",
									"lt(F.one, x + f(0))",
									By(positions, arithmetic, translation.At(s, xm, f0)))
								d.Show(
									"so f(x) = x·q(x) + f(0) is at least x + f(0), which lies above one",
									By(
										value.At(x),
										scaled,
										shifted,
										xm,
										translation.At(xm, scaledX, f0),
										transitive.At(
											one, comm_ring.AddIn.Read(ring).At(xm, f0), comm_ring.AddIn.Read(ring).At(scaledX, f0)),
										ordered_field.OrderedLeDef.At(lt, x, scaledX),
										ordered_field.OrderedLeDef.At(lt, one, d.TermAs[A]("polynomial_eval(f, x)"))))
							}))
						b.Take(m)
						b.Show(
							"m lies in F and past the positive c, and past m f is at least one",
							By(pastC, cPositive, farValues, transitive.At(zero, cm, mm)))
					})
			}))
		arg.Show(
			"at its own degree, p is at least one past some positive bound",
			By(growth.At(arg.TermAs[Nat]("polynomial_degree(p)"), p), over, monic))
	}),
})}

// SignAtPositiveInfinity — past some positive bound a nonzero polynomial over
// an ordered field has the sign of its leading coefficient c: c⁻¹·p is monic,
// so past some positive bound its value c⁻¹·p(x) is at least one, and p(x) is
// c times that positive value.
var SignAtPositiveInfinity = signAtPositiveInfinityThm{family.Add(registry.ProofEntry{
	Name: "SignAtPositiveInfinity",
	Key:  "prop_dc5a3ba5520ff230",
	Build: ordered_field.OrderedFieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"p ≠ vec_zero",
		},
		Conclusion: "∃b:A. " +
			"    b ∈ F.carrier ∧ " +
			"    lt(F.zero, b) ∧ " +
			"    (∀x:A. " +
			"        x ∈ F.carrier ∧ lt(b, x) ⇒ " +
			"        ordered_sign(F, lt, polynomial_eval(p, x)) = " +
			"        ordered_sign(F, lt, p(polynomial_degree(p))))",
		Abbrev: Abbrev{
			{Name: "monic", Text: "F.inv(p(polynomial_degree(p))) • p"},
		},
	}, func(
		arg *Argument,
		ordered ordered_field.OrderedFieldFact[on.F],
		p *Arrow[Nat, A],
		poly, nonzero Fact,
	) {
		lt := arg.TermAs[Fun2[A, A, Bool]]("lt")
		transitive := ordered_field.Transitive.Read(ordered)
		fieldF := ordered_field.FieldOn.Read(ordered)
		ring := field.RingOn.Read(fieldF)
		zero := arg.MemberOf[on.F](arg.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		one := arg.MemberOf[on.F](arg.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		carrier := arg.TermAs[Set[A]]("F.carrier")
		leading := arg.Conjuncts(
			GroupPremises(poly, nonzero, polynomial.LeadingCoefficientNonzero.At(zero, carrier, p)),
			"the leading coefficient c of p lies in F",
			"c is not zero")
		lead := arg.MemberOf[on.F](arg.TermAs[A]("p(polynomial_degree(p))"), leading[0])
		inverse := arg.MemberOf[on.F](
			arg.TermAs[A]("F.inv(p(polynomial_degree(p)))"), field.InvIn.Read(fieldF).At(lead))
		normalized := arg.Conjuncts(
			GroupPremises(poly, nonzero, polynomial.MonicMultiple.Read(fieldF).At(p)),
			"c⁻¹·p is a polynomial over F",
			"c⁻¹·p is monic",
			"c⁻¹·p has the degree of p")
		b, far := arg.UnpackAs[A](
			GroupPremises(
				normalized[0],
				normalized[1],
				MonicEventuallyAtLeastOne.Read(ordered).At(arg.TermAs[Fun[Nat, A]]("«monic»"))),
			"b")
		bounds := arg.Conjuncts(
			far,
			"b lies in F",
			"b is positive",
			"past b, c⁻¹·p is at least one")
		signsPast := arg.Have(
			"past b, p(x) is c times the positive value c⁻¹·p(x)",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ F.carrier",
					"lt(b, x)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(p, x)) = " +
					"ordered_sign(F, lt, p(polynomial_degree(p)))",
			},
			Derive(func(c *Argument) {
				x := c.FixAs[A]("x")
				xFacts := c.Conjuncts(
					c.Assume(),
					"x lies in F",
					"x lies past b")
				xIn := c.MemberOf[on.F](x, xFacts[0])
				value := c.MemberOf[on.F](
					c.TermAs[A]("polynomial_eval(p, x)"),
					GroupPremises(poly, polynomial_evaluation.EvalIn.Read(ring).At(p, xIn)))
				scaledValue := comm_ring.MulIn.Read(ring).At(inverse, value)
				values := c.Have(
					"p takes a value in F at x, and c⁻¹·p the value c⁻¹·p(x)",
					"polynomial_eval(p, x) ∈ F.carrier ∧ "+
						"polynomial_eval(«monic», x) = F.inv(p(polynomial_degree(p))) * polynomial_eval(p, x)",
					By(
						poly,
						polynomial_evaluation.EvalIn.Read(ring).At(p, xIn),
						polynomial_evaluation.EvalScalar.Read(ring).At(inverse, xIn, p)))
				positive := c.Have(
					"c⁻¹·p(x) is at least one, so positive",
					"lt(F.zero, F.inv(p(polynomial_degree(p))) * polynomial_eval(p, x))",
					By(
						bounds[2].At(x),
						xIn,
						xFacts[1],
						values,
						ordered_field.OnePositive.Read(ordered),
						ordered_field.OrderedLeDef.At(lt, one, scaledValue),
						transitive.At(zero, one, scaledValue)))
				back := c.Have(
					"c times c⁻¹·p(x) is p(x)",
					"p(polynomial_degree(p)) * (F.inv(p(polynomial_degree(p))) * polynomial_eval(p, x)) = "+
						"polynomial_eval(p, x)",
					ByArith(
						ring,
						lead,
						inverse,
						values,
						leading[1],
						Scaled(value, field.MulLeftInverseOn.Read(fieldF).At(lead))))
				unit := c.Have(
					"the sign of c times 1 is the sign of c",
					"ordered_sign(F, lt, p(polynomial_degree(p))) * 1 = ordered_sign(F, lt, p(polynomial_degree(p)))",
					ByArith())
				c.Show(
					"so p(x) has the sign of c times the sign 1 of the positive c⁻¹·p(x)",
					By(
						back,
						positive,
						unit,
						ordered_field.SignMul.Read(ordered).At(lead, scaledValue),
						ordered_field.SignValues.Read(ordered).At(scaledValue)))
			}))
		arg.Take(b)
		arg.Show(
			"b is a positive point of F, and past it p has the sign of c",
			By(bounds[0], bounds[1], signsPast))
	}),
})}

// SignsAtInfinity — past some positive bound a nonzero polynomial over an
// ordered field has the sign of its leading coefficient c at x, and the sign
// of c·(−1)^deg at −x: p(−x) is the value at x of the alternating polynomial
// with coefficients p(i)·(−1)ⁱ, which keeps p's degree and has leading
// coefficient c·(−1)^deg, and past the sum of the two polynomials' bounds
// both signs hold.
var SignsAtInfinity = signsAtInfinityThm{family.Add(registry.ProofEntry{
	Name: "SignsAtInfinity",
	Key:  "prop_658718c15c27bcc5",
	Reading: "The bound uses finitely many coefficient ratios and does not require " +
		"an Archimedean field. Nonzero constant polynomials are included with degree zero.",
	Build: ordered_field.OrderedFieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"p ≠ vec_zero",
		},
		Conclusion: "∃b:A. " +
			"    b ∈ F.carrier ∧ " +
			"    lt(F.zero, b) ∧ " +
			"    (∀x:A. " +
			"        x ∈ F.carrier ∧ lt(b, x) ⇒ " +
			"        ordered_sign(F, lt, polynomial_eval(p, x)) = " +
			"        ordered_sign(F, lt, p(polynomial_degree(p))) ∧ " +
			"        ordered_sign(F, lt, polynomial_eval(p, -x)) = " +
			"        ordered_sign(F, " +
			"            lt, " +
			"            p(polynomial_degree(p)) * monoid_pow(F.mul, F.one, -F.one, polynomial_degree(p))))",
		Abbrev: Abbrev{
			{Name: "alternating", Text: "λi:num. p(i) * monoid_pow(F.mul, F.one, -F.one, i)"},
		},
	}, func(
		arg *Argument,
		ordered ordered_field.OrderedFieldFact[on.F],
		p *Arrow[Nat, A],
		poly, nonzero Fact,
	) {
		transitive := ordered_field.Transitive.Read(ordered)
		fieldF := ordered_field.FieldOn.Read(ordered)
		ring := field.RingOn.Read(fieldF)
		powers := comm_ring.MulMonoidOn.Read(ring)
		zero := arg.MemberOf[on.F](arg.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		carrier := arg.TermAs[Set[A]]("F.carrier")
		degree := arg.TermAs[Nat]("polynomial_degree(p)")
		one := arg.MemberOf[on.F](arg.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		minusOne := arg.MemberOf[on.F](arg.TermAs[A]("-F.one"), comm_ring.NegIn.Read(ring).At(one))
		alternating := arg.TermAs[Fun[Nat, A]]("«alternating»")
		coefficients := polynomial.CoefficientIn.Read(poly)
		leading := arg.Conjuncts(
			GroupPremises(poly, nonzero, polynomial.LeadingCoefficientNonzero.At(zero, carrier, p)),
			"the leading coefficient c of p lies in F",
			"c is not zero")
		lead := arg.MemberOf[on.F](arg.TermAs[A]("p(polynomial_degree(p))"), leading[0])
		b1, right := arg.UnpackAs[A](
			GroupPremises(poly, nonzero, SignAtPositiveInfinity.Read(ordered).At(p)), "b₁")
		past := arg.Unfolded(
			arg.Have(
				"p vanishes past its degree",
				"vec⟨suc(polynomial_degree(p))⟩(p)",
				By(poly, polynomial.DegreeVec.At(zero, carrier, p))),
			vec_space.VecDef)
		alternatingPast := arg.Have(
			"so does the alternating polynomial, a power of −1 times zero being zero",
			"vec⟨suc(polynomial_degree(p))⟩(«alternating»)",
			Simp(Fwd(vec_space.VecDef)),
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				beyond := b.Assume()
				vanishes := b.Have(
					"p vanishes at i",
					"p(i) = F.zero",
					By(beyond, past.At(i)))
				b.Show(
					"so the alternating coefficient is zero times a power of −1",
					ByArith(
						ring,
						Scaled(b.TermAs[A]("monoid_pow(F.mul, F.one, -F.one, i)"), vanishes),
						coefficients.At(i),
						comm_monoid.PowIn.Read(powers).At(minusOne, i)))
			}))
		alternatingCoefficients := arg.Have(
			"its coefficients lie in F, each a coefficient of p times a power of −1",
			"∀i:num. «alternating»(i) ∈ F.carrier",
			By(coefficients, minusOne, comm_monoid.PowIn.Read(powers), comm_ring.MulIn.Read(ring)))
		alternatingOver := arg.Have(
			"so it is a polynomial over F",
			"polynomial_over(F.carrier, «alternating»)",
			By(
				alternatingPast,
				alternatingCoefficients,
				polynomial.PolynomialOverDef.At(zero, carrier, alternating)))
		negatives := arg.Have(
			"−(−1) is 1 and −0 is 0",
			"-(-F.one) = F.one ∧ -F.zero = F.zero",
			ByArith(ring))
		minusOneNonzero := arg.Have(
			"so −1 is not zero, for 1 is not",
			"-F.one ≠ F.zero",
			By(Normalized, negatives, field.OneNotZeroOn.Read(fieldF)))
		power := arg.MemberOf[on.F](
			arg.TermAs[A]("monoid_pow(F.mul, F.one, -F.one, polynomial_degree(p))"),
			comm_monoid.PowIn.Read(powers).At(minusOne, degree))
		alternatingLead := arg.Have(
			"its coefficient c·(−1)^deg at the degree of p is not zero, neither factor being zero",
			"p(polynomial_degree(p)) * monoid_pow(F.mul, F.one, -F.one, polynomial_degree(p)) ≠ F.zero",
			By(
				leading[1],
				minusOneNonzero,
				field.PowEqZeroOn.Read(fieldF).At(minusOne, degree),
				field.MulEqZeroOn.Read(fieldF).At(lead, power)))
		alternatingDegree := arg.Have(
			"so the alternating polynomial has the degree of p",
			"polynomial_degree(«alternating») = polynomial_degree(p)",
			By(
				alternatingOver,
				alternatingPast,
				alternatingLead,
				polynomial.DegreeExact.At(zero, carrier, alternating, degree)))
		alternatingNonzero := arg.Have(
			"and is not the zero polynomial",
			"«alternating» ≠ vec_zero",
			By(Normalized, alternatingLead, vec_space.VecZeroDef.At(zero, degree)))
		b2, left := arg.UnpackAs[A](
			GroupPremises(
				alternatingOver, alternatingNonzero, SignAtPositiveInfinity.Read(ordered).At(alternating)),
			"b₂")
		reflect := arg.Have(
			"the alternating polynomial takes at x the value of p at −x",
			"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(«alternating», x) = polynomial_eval(p, -x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.MemberOf[on.F](x, b.Assume())
				sign := b.Have(
					"−1 times x is −x",
					"-F.one * x = -x",
					ByArith(ring, xIn))
				b.Show(
					"evaluating p at (−1)·x weights its i-th coefficient by (−1)ⁱ",
					By(sign, poly, polynomial_evaluation.EvalAtScaledPoint.Read(ring).At(p, minusOne, xIn)))
			}))
		rightParts := arg.Conjuncts(
			right,
			"b₁ lies in F",
			"b₁ is positive",
			"past b₁, p has the sign of c")
		leftParts := arg.Conjuncts(
			left,
			"b₂ lies in F",
			"b₂ is positive",
			"past b₂, the alternating polynomial has the sign of c·(−1)^deg")
		b1m, b2m := arg.MemberOf[on.F](b1, rightParts[0]), arg.MemberOf[on.F](b2, leftParts[0])
		sum := comm_ring.AddIn.Read(ring).At(b1m, b2m)
		commuted := arg.Have(
			"b₂ + b₁ is b₁ + b₂",
			"b₂ + b₁ = b₁ + b₂",
			ByArith(ring, b1m, b2m))
		sumPast := arg.Have(
			"b₂ and b₁ are positive, so b₁ + b₂ lies past both",
			"lt(b₁, b₁ + b₂) ∧ lt(b₂, b₁ + b₂)",
			By(
				Normalized,
				commuted,
				ordered_field.LessThanSelfAddLeft.Read(ordered).At(b2m, b1m),
				ordered_field.LessThanSelfAddLeft.Read(ordered).At(b1m, b2m),
				rightParts[1],
				leftParts[1]))
		farSigns := arg.Have(
			"past b₁ + b₂ both signs hold",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ F.carrier",
					"lt(b₁ + b₂, x)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(p, x)) = " +
					"ordered_sign(F, lt, p(polynomial_degree(p))) ∧ " +
					"ordered_sign(F, lt, polynomial_eval(p, -x)) = " +
					"ordered_sign(F, " +
					"    lt, " +
					"    p(polynomial_degree(p)) * monoid_pow(F.mul, F.one, -F.one, polynomial_degree(p)))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xFacts := b.Conjuncts(
					b.Assume(),
					"x lies in F",
					"x lies past b₁ + b₂")
				xm := b.MemberOf[on.F](x, xFacts[0])
				beyond := b.Have(
					"x lies past b₁ and past b₂",
					"lt(b₁, x) ∧ lt(b₂, x)",
					By(xFacts[1], sumPast, transitive.At(b1m, sum, xm), transitive.At(b2m, sum, xm)))
				b.Show(
					"p has the sign of c at x, and at −x the sign the alternating polynomial has at x",
					By(rightParts[2].At(x), leftParts[2].At(x), reflect.At(x), alternatingDegree, beyond, xFacts[0]))
			}))
		arg.Take(sum)
		arg.Show(
			"b₁ + b₂ lies in F past the positive b₁, and past it both signs hold",
			By(farSigns, sumPast, rightParts[1], transitive.At(zero, b1m, sum)))
	}),
})}

// SignsAtBothEnds — a nonzero polynomial over an ordered field has, past
// some point, the sign of its leading coefficient, and, before some point,
// that sign times (−1)^deg: SignsAtInfinity gives both past a bound b, read
// at x and at −x; the sign of a product is the product of the signs, and the
// sign of (−1)^deg is the sign of −1, which is −1, to the power deg.
var SignsAtBothEnds = signsAtBothEndsThm{family.Add(registry.ProofEntry{
	Name: "SignsAtBothEnds",
	Key:  "prop_df403528a6d80d81",
	Build: ordered_field.OrderedFieldOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"p ≠ vec_zero",
		},
		Conclusion: "(∃b:A. " +
			"    b ∈ F.carrier ∧ " +
			"    (∀x:A. " +
			"        x ∈ F.carrier ∧ lt(b, x) ⇒ " +
			"        ordered_sign(F, lt, polynomial_eval(p, x)) = " +
			"        ordered_sign(F, lt, p(polynomial_degree(p))))) ∧ " +
			"(∃b:A. " +
			"    b ∈ F.carrier ∧ " +
			"    (∀x:A. " +
			"        x ∈ F.carrier ∧ lt(x, b) ⇒ " +
			"        ordered_sign(F, lt, polynomial_eval(p, x)) = " +
			"        ordered_sign(F, lt, p(polynomial_degree(p))) * (-&1) ^ polynomial_degree(p)))",
	}, func(
		arg *Argument,
		ordered ordered_field.OrderedFieldFact[on.F],
		p *Arrow[Nat, A],
		poly, nonzero Fact,
	) {
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		one := arg.MemberOf[on.F](arg.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
		minusOne := arg.MemberOf[on.F](arg.TermAs[A]("-F.one"), comm_ring.NegIn.Read(ring).At(one))
		powers := comm_ring.MulMonoidOn.Read(ring)
		b, far := arg.UnpackAs[A](GroupPremises(poly, nonzero, SignsAtInfinity.Read(ordered).At(p)), "b")
		bounds := arg.Conjuncts(
			far,
			"b lies in F",
			"b is positive",
			"past b, p has the sign of c at x and of c·(−1)^deg at −x")
		bm := arg.MemberOf[on.F](b, bounds[0])
		degree := arg.TermAs[Nat]("polynomial_degree(p)")
		lead := arg.MemberOf[on.F](
			arg.TermAs[A]("p(polynomial_degree(p))"), polynomial.CoefficientIn.Read(poly).At(degree))
		alternation := arg.MemberOf[on.F](
			arg.TermAs[A]("monoid_pow(F.mul, F.one, -F.one, polynomial_degree(p))"),
			comm_monoid.PowIn.Read(powers).At(minusOne, degree))
		right := arg.Have(
			"past b, p has the sign of its leading coefficient",
			"∃b:A. "+
				"    b ∈ F.carrier ∧ "+
				"    (∀x:A. "+
				"        x ∈ F.carrier ∧ lt(b, x) ⇒ "+
				"        ordered_sign(F, lt, polynomial_eval(p, x)) = "+
				"        ordered_sign(F, lt, p(polynomial_degree(p))))",
			Derive(func(c *Argument) {
				c.Take(b)
				c.Show(
					"SignsAtInfinity at x",
					By(bounds[0], bounds[2]))
			}))
		left := arg.Have(
			"before −b, p has the sign of its leading coefficient times (−1)^deg",
			"∃b:A. "+
				"    b ∈ F.carrier ∧ "+
				"    (∀x:A. "+
				"        x ∈ F.carrier ∧ lt(x, b) ⇒ "+
				"        ordered_sign(F, lt, polynomial_eval(p, x)) = "+
				"        ordered_sign(F, lt, p(polynomial_degree(p))) * (-&1) ^ polynomial_degree(p))",
			Derive(func(c *Argument) {
				before := c.Have(
					"a point x below −b is −y for the point y = −x past b",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ F.carrier",
							"lt(x, -b)",
						},
						Conclusion: "ordered_sign(F, lt, polynomial_eval(p, x)) = " +
							"ordered_sign(F, lt, p(polynomial_degree(p))) * (-&1) ^ polynomial_degree(p)",
					},
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						given := d.Conjuncts(
							d.Assume(),
							"x lies in F",
							"x lies below −b")
						xm := d.MemberOf[on.F](x, given[0])
						negated := d.MemberOf[on.F](d.TermAs[A]("-x"), comm_ring.NegIn.Read(ring).At(xm))
						shift := d.MemberOf[on.F](d.TermAs[A]("b - x"), comm_ring.SubIn.Read(ring).At(bm, xm))
						algebra := d.Have(
							"x + (b − x) = b, −b + (b − x) = −x and −(−x) = x",
							"x + (b - x) = b ∧ -b + (b - x) = -x ∧ -(-x) = x",
							ByArith(ring, xm, bm))
						reflected := d.Have(
							"adding b − x to x < −b gives b < −x",
							"lt(b, -x)",
							By(
								given[1],
								algebra,
								ordered_field.AddPreservesOrder.Read(ordered).At(
									xm, d.MemberOf[on.F](d.TermAs[A]("-b"), comm_ring.NegIn.Read(ring).At(bm)), shift)))
						d.Show(
							"so p(x) = p(−(−x)) has the sign of c·(−1)^deg, which is sign(c)·sign(−1)^deg",
							By(
								bounds[2].At(negated),
								negated,
								reflected,
								algebra,
								ordered_field.SignMul.Read(ordered).At(lead, alternation),
								ordered_field.SignPow.Read(ordered).At(minusOne, degree),
								ordered_field.SignNegOne.Read(ordered)))
					}))
				c.Take(c.TermAs[A]("-b"))
				c.Show(
					"−b lies in F",
					By(before, comm_ring.NegIn.Read(ring).At(bm)))
			}))
		arg.Show(
			"both ends",
			By(right, left))
	}),
})}
