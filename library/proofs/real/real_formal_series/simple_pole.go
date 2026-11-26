// simple_pole.go — a simple pole at one over ℝ: substituting Tᵈ keeps it,
// and a substitution b(Tᵈ) = a(T)ᵈ between two series with one forces
// d = 1.

package real_formal_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// SimplePoleSubstitute — substituting Tᵈ, d positive, into a series with a
// simple pole at one gives a series with a simple pole at one. Substitution
// is multiplicative and takes 1 − T to 1 − Tᵈ (SeriesSubstituteMul,
// SeriesSubstituteLinearFactor), so (1 − T)·Q·b = P becomes
// (1 − Tᵈ)·Q(Tᵈ)·b(Tᵈ) = P(Tᵈ); 1 − Tᵈ is 1 − T times the geometric sum S
// (GeometricFactorization), so P(Tᵈ) and S·Q(Tᵈ) witness the pole.
// Substitution keeps polynomials, their values at one and their constant
// coefficients (SeriesSubstitutePolynomial, SeriesSubstituteAtMultiple); S
// starts with one and takes the value d at one, so S·Q(Tᵈ) starts with Q(0)
// (PolynomialMulAtZero) and takes the value d·Q(1) at one.
var SimplePoleSubstitute = simplePoleSubstituteThm{family.Add(registry.ProofEntry{
	Name: "SimplePoleSubstitute",
	Key:  "prop_6068b6b6a56861c5",
	Build: family.Theorem(Statement{
		Binders: "∀b:(num → real). ∀d:num.",
		Hypotheses: []string{
			"0 < d",
			"series_simple_pole_one(b)",
		},
		Conclusion: "series_simple_pole_one(series_substitute(real_ring, b, d))",
	},
		func(arg *Argument, b *Arrow[Nat, Real], d *Expr[Nat], positive, pole Fact) {
			ring := real_ring.CommRingOn
			P, Q, fraction := arg.Unpack2As[Fun[Nat, Real], Fun[Nat, Real]](
				arg.Unfolded(pole, SeriesSimplePoleDef), "P", "Q")
			parts := arg.Conjuncts(
				fraction,
				"P is a real polynomial",
				"so is Q",
				"Q starts with a nonzero coefficient",
				"P is nonzero at one",
				"so is Q",
				"and (1 − T)·Q·b is P")
			one, zeroIndex := arg.TermAs[Real]("&1"), arg.TermAs[Nat]("0")
			linear := arg.TermAs[Fun[Nat, Real]]("«1−T»")
			S, Sdef := arg.LetAs[Fun[Nat, Real]]("S", "«1+…+Tᵈ⁻¹»(d)")
			dilatedQ := arg.TermAs[Fun[Nat, Real]]("series_substitute(real_ring, Q, d)")
			carried := arg.Have(
				"substitution is multiplicative and takes 1 − T to 1 − Tᵈ, "+
					"so it carries (1 − T)·Q·b = P to (1 − Tᵈ)·Q(Tᵈ)·b(Tᵈ) = P(Tᵈ)",
				"polynomial_mul(polynomial_mul(«1−Tᵈ»(d), series_substitute(real_ring, Q, d)), "+
					"    series_substitute(real_ring, b, d)) = "+
					"series_substitute(real_ring, P, d)",
				By(
					positive,
					parts[5],
					set_basic.InUniv.Inst[Real](),
					formal_series.SeriesSubstituteLinearFactor.Read(ring).At(d),
					formal_series.SeriesSubstituteMul.Read(ring).At(
						arg.TermAs[Fun[Nat, Real]]("polynomial_mul(«1−T», Q)"), b, d),
					formal_series.SeriesSubstituteMul.Read(ring).At(linear, Q, d)))
			geometric := arg.Simplified(
				GroupPremises(positive, polynomial_evaluation.GeometricFactorization.Read(ring).At(d)),
				Fwd(real_ring.AddPowOne),
				Rev(Sdef))
			kept := arg.Have(
				"P(Tᵈ) and Q(Tᵈ) are real polynomials with the values of P and Q at one",
				"polynomial_over(𝕌, series_substitute(real_ring, P, d)) ∧ "+
					"polynomial_eval(series_substitute(real_ring, P, d), &1) = polynomial_eval(P, &1) ∧ "+
					"polynomial_over(𝕌, series_substitute(real_ring, Q, d)) ∧ "+
					"polynomial_eval(series_substitute(real_ring, Q, d), &1) = polynomial_eval(Q, &1)",
				By(
					positive,
					parts[0],
					parts[1],
					formal_series.SeriesSubstitutePolynomial.Read(ring).At(P, d),
					formal_series.SeriesSubstitutePolynomial.Read(ring).At(Q, d)))
			start := arg.Have(
				"S starts with one",
				"S(0) = &1",
				Sdef.Rw(),
				ByArith(positive))
			constant := arg.Have(
				"S·Q(Tᵈ) starts with S(0)·Q(0), which is Q(0)",
				"polynomial_mul(S, series_substitute(real_ring, Q, d), 0) = Q(0)",
				ByArith(
					positive,
					start,
					set_basic.InUniv.Inst[Real](),
					polynomial.PolynomialMulAtZero.Read(ring).At(S, dilatedQ),
					formal_series.SeriesSubstituteAtMultiple.At(
						arg.TermAs[module_record.RingOps[Real]]("real_ring"), Q, d, zeroIndex)))
			denominator := arg.Have(
				"S·Q(Tᵈ) is a real polynomial taking at one d times the value of Q",
				"polynomial_over(𝕌, polynomial_mul(S, series_substitute(real_ring, Q, d))) ∧ "+
					"polynomial_eval(polynomial_mul(S, series_substitute(real_ring, Q, d)), &1) = "+
					"&d * polynomial_eval(Q, &1)",
				By(
					kept,
					positive,
					geometric,
					set_basic.InUniv.Inst[Real](),
					polynomial.PolynomialMulOver.Read(ring).At(S, dilatedQ),
					polynomial_evaluation.EvalMul.Read(ring).AsFact().At(S, dilatedQ, one)))
			identity := arg.Have(
				"so (1 − T)·(S·Q(Tᵈ))·b(Tᵈ) is P(Tᵈ)",
				"polynomial_mul(polynomial_mul(«1−T», polynomial_mul(S, series_substitute(real_ring, Q, d))), "+
					"    series_substitute(real_ring, b, d)) = "+
					"series_substitute(real_ring, P, d)",
				CalcEq(
					Leg(
						arg.TermAs[Fun[Nat, Real]](
							"polynomial_mul(polynomial_mul(polynomial_mul(«1−T», S), series_substitute(real_ring, Q, d)), "+
								"    series_substitute(real_ring, b, d))"),
						"the product associates",
						By(
							set_basic.InUniv.Inst[Real](),
							polynomial.PolynomialMulAssoc.Read(ring).At(linear, S, dilatedQ))),
					Leg(
						arg.TermAs[Fun[Nat, Real]](
							"polynomial_mul(polynomial_mul(«1−Tᵈ»(d), series_substitute(real_ring, Q, d)), "+
								"    series_substitute(real_ring, b, d))"),
						"(1 − T)·S is 1 − Tᵈ",
						By(positive, geometric)),
					FinalLeg(
						"which the carried equation turns into P(Tᵈ)",
						By(carried))))
			value := arg.Have(
				"d times the nonzero value of Q at one is nonzero",
				"&d * polynomial_eval(Q, &1) ≠ &0",
				ByArith(
					positive,
					parts[4],
					real_ring.MulEqZero.At(arg.TermAs[Real]("&d"), arg.TermAs[Real]("polynomial_eval(Q, &1)")),
					real_construction.OfNumEq.At(d, zeroIndex)))
			arg.Do(Simp(Fwd(SeriesSimplePoleDef)))
			arg.Take(arg.TermAs[Fun[Nat, Real]]("series_substitute(real_ring, P, d)"))
			arg.Take(arg.TermAs[Fun[Nat, Real]]("polynomial_mul(S, series_substitute(real_ring, Q, d))"))
			arg.Show(
				"P(Tᵈ) and S·Q(Tᵈ) witness the simple pole",
				By(Normalized, parts[2], parts[3], kept, constant, denominator, identity, value))
		}),
})}

// SimplePolePowerSubstitution — when substituting Tᵈ into one series with a
// simple pole at one gives the dth power of another series with a simple
// pole at one, d is one. Suppose d > 1.
// Clearing the denominators of the two rational series and cross-multiplying
// leaves a polynomial identity with the linear factor 1 − T on both sides;
// cancelling it in the integral domain of real polynomials and evaluating at
// one, the left side vanishes with the remaining power of a's denominator,
// while the right side is d times two nonzero values.
var SimplePolePowerSubstitution = simplePolePowerSubstitutionThm{family.Add(registry.ProofEntry{
	Name: "SimplePolePowerSubstitution",
	Key:  "prop_da3d3a7a770cb43b",
	Build: family.Sections(Statement{
		Binders: "∀a b:(num → real). ∀d:num.",
		Hypotheses: []string{
			"0 < d",
			"series_simple_pole_one(a)",
			"series_simple_pole_one(b)",
			"series_substitute(real_ring, b, d) = polynomial_pow(a, d)",
		},
		Conclusion: "d = 1",
		Abbrev: Abbrev{
			{Name: "ℝ[T]", Text: "{p:num → real | polynomial_over(𝕌, p)}"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			realConvolutionMonoid := ctx.Lemma("comm_monoid(polynomial_mul, "+
				"    basis_vector(0))", func(arg *Argument) {
				arg.Show(
					"convolution is commutative, associative and unital",
					Unfold(comm_monoid.CommMonoid),
					SplitConjAll(
						Case(
							"convolution commutes",
							Derive(func(arg *Argument) {
								x := arg.FixAs[Fun[Nat, Real]]("x")
								y := arg.FixAs[Fun[Nat, Real]]("y")
								arg.Show(
									"the polynomial law holds for any two real sequences",
									By(set_basic.InUniv.Inst[Real](), polynomial.PolynomialMulComm.Read(real_ring.CommRingOn).At(x, y)))
							})),
						Case(
							"convolution associates",
							Derive(func(arg *Argument) {
								x := arg.FixAs[Fun[Nat, Real]]("x")
								y := arg.FixAs[Fun[Nat, Real]]("y")
								z := arg.FixAs[Fun[Nat, Real]]("z")
								arg.Show(
									"the polynomial law holds for any three real sequences",
									By(
										set_basic.InUniv.Inst[Real](),
										polynomial.PolynomialMulAssoc.Read(real_ring.CommRingOn).At(x, y, z)))
							})),
						Case(
							"the constant polynomial one is a convolution identity",
							Derive(func(arg *Argument) {
								x := arg.FixAs[Fun[Nat, Real]]("x")
								arg.Show(
									"the polynomial law holds for any real sequence",
									By(set_basic.InUniv.Inst[Real](), polynomial.PolynomialOneMul.Read(real_ring.CommRingOn).At(x)))
							})),
					))
			})
			powerProduct := ctx.Lemma("∀a b:(num → real). ∀n:num. "+
				"    polynomial_pow(polynomial_mul(a, b), n) = "+
				"    polynomial_mul(polynomial_pow(a, n), polynomial_pow(b, n))", func(arg *Argument) {
				arg.Show(
					"powers distribute over convolution",
					Simp(Fwd(polynomial.PolynomialPowDef)),
					By(
						realConvolutionMonoid,
						At(
							comm_monoid.MulPow.Inst[Fun[Nat, Real]](),
							arg.TermAs[Op[Fun[Nat, Real]]]("polynomial_mul"),
							arg.TermAs[Fun[Nat, Real]]("basis_vector(0)"))))
			})
			crossMultiply := ctx.Lemma(Statement{
				Binders:    "∀op:(A → A → A). ∀e u v x p q:A.",
				Hypotheses: []string{"comm_monoid(op, e)", "op(u, x) = p", "op(v, x) = q"},
				Conclusion: "op(u, q) = op(v, p)",
			}, func(arg *Argument, op *Arrow2[A, A, A], e, u, v, x, p, q *Expr[A], given Fact) {
				arg.Show(
					"multiply the two equations by their opposite factors",
					By(Normalized, given, comm_monoid.LeftComm.At(op, e, u, v, x)))
			})
			nonzeroPower := ctx.Lemma(Statement{
				Binders: "∀x:real. ∀n:num.", Hypotheses: []string{"x ≠ &0"},
				Conclusion: "monoid_pow(real_mul, &1, x, n) ≠ &0",
			}, func(arg *Argument, x *Expr[Real], n *Expr[Nat], nonzero Fact) {
				arg.Induct(n)
				arg.Base(
					"the zeroth power is nonzero",
					Simp(Fwd(comm_monoid.MonoidPowDef)),
					ByArith())
				arg.Step(
					"a nonzero factor preserves a nonzero power",
					func(arg *Argument, ih Fact) {
						arg.Show(
							"the successor power is a product of nonzero reals",
							Simp(Fwd(comm_monoid.MonoidPowDef)),
							By(nonzero, ih, real_ring.MulEqZero.At(x, arg.TermAs[Real]("monoid_pow(real_mul, &1, x, n)"))))
					})
			})
			return ctx.Theorem(headline, func(
				arg *Argument,
				a, b *Arrow[Nat, Real],
				d *Expr[Nat],
				positive, poleA, poleB, substitution Fact,
			) {
				different := arg.SupposeNot()
				degree := arg.Have(
					"a different positive degree is greater than one",
					"1 < d ∧ 0 < d - 1 ∧ suc(d - 1) = d",
					ByArith(different, positive))
				P1, Q1, fractionA := arg.Unpack2As[Fun[Nat, Real], Fun[Nat, Real]](
					arg.Unfolded(poleA, SeriesSimplePoleDef), "P₁", "Q₁")
				P2, Q2, fractionB := arg.Unpack2As[Fun[Nat, Real], Fun[Nat, Real]](
					arg.Unfolded(poleB, SeriesSimplePoleDef), "P₂", "Q₂")
				ring := real_ring.CommRingOn
				one, predecessor := arg.TermAs[Real]("&1"), arg.TermAs[Nat]("d - 1")
				linear, geometricSum :=
					arg.TermAs[Fun[Nat, Real]]("«1−T»"), arg.TermAs[Fun[Nat, Real]]("«1+…+Tᵈ⁻¹»(d)")
				geometric := arg.Simplified(
					GroupPremises(positive, polynomial_evaluation.GeometricFactorization.Read(ring).At(d)),
					Fwd(real_ring.AddPowOne))
				partsA := arg.Conjuncts(
					fractionA,
					"P₁ is a real polynomial",
					"so is Q₁",
					"Q₁ starts with a nonzero coefficient",
					"P₁ is nonzero at one",
					"so is Q₁",
					"and (1 − T)·Q₁·a is P₁")
				partsB := arg.Conjuncts(
					fractionB,
					"P₂ is a real polynomial",
					"so is Q₂",
					"Q₂ starts with a nonzero coefficient",
					"P₂ is nonzero at one",
					"so is Q₂",
					"and (1 − T)·Q₂·b is P₂")
				D, Ddef := arg.LetAs[Fun[Nat, Real]]("D", "polynomial_mul(«1−T», Q₁)")
				L, Ldef := arg.LetAs[Fun[Nat, Real]]("L", "polynomial_pow(D, d - 1)")
				E, Edef := arg.LetAs[Fun[Nat, Real]]("E", "series_substitute(real_ring, P₂, d)")
				F, Fdef := arg.LetAs[Fun[Nat, Real]]("F", "series_substitute(real_ring, Q₂, d)")
				V, Vdef := arg.LetAs[Fun[Nat, Real]]("V", "polynomial_pow(P₁, d)")
				factored := arg.Have(
					"clear the denominators: cross-multiplying the dth power of "+
						"a's equation and b's substituted one leaves 1 − T on both sides",
					"polynomial_mul(polynomial_mul(polynomial_mul(«1−T», Q₁), L), E) = "+
						"polynomial_mul(polynomial_mul(polynomial_mul(«1−T», «1+…+Tᵈ⁻¹»(d)), F), V)",
					Derive(func(arg *Argument) {
						powerEquation := arg.Have(
							"raise the cleared equation for a to the dth power",
							"polynomial_mul(polynomial_pow(D, d), polynomial_pow(a, d)) = polynomial_pow(P₁, d)",
							By(partsA[5], At(powerProduct, D, a, d)))
						substituteEquation := arg.Have(
							"substitute into the cleared equation for b",
							"polynomial_mul(series_substitute(real_ring, polynomial_mul(«1−T», Q₂), d), "+
								"    polynomial_pow(a, d)) = "+
								"series_substitute(real_ring, P₂, d)",
							By(
								positive,
								partsB[5],
								substitution,
								set_basic.InUniv.Inst[Real](),
								formal_series.SeriesSubstituteMul.Read(ring).At(
									arg.TermAs[Fun[Nat, Real]]("polynomial_mul(«1−T», Q₂)"), b, d)))
						crossEquation := arg.Have(
							"eliminate the common power of a from the two cleared equations",
							"polynomial_mul(polynomial_pow(D, d), series_substitute(real_ring, P₂, d)) = "+
								"polynomial_mul(series_substitute(real_ring, polynomial_mul(«1−T», Q₂), d), polynomial_pow(P₁, d))",
							By(
								powerEquation,
								substituteEquation,
								realConvolutionMonoid,
								At(crossMultiply,
									arg.TermAs[Op[Fun[Nat, Real]]]("polynomial_mul"),
									arg.TermAs[Fun[Nat, Real]]("basis_vector(0)"),
									arg.TermAs[Fun[Nat, Real]]("polynomial_pow(D, d)"),
									arg.TermAs[Fun[Nat, Real]]("series_substitute(real_ring, polynomial_mul(«1−T», Q₂), d)"),
									arg.TermAs[Fun[Nat, Real]]("polynomial_pow(a, d)"),
									arg.TermAs[Fun[Nat, Real]]("polynomial_pow(P₁, d)"),
									arg.TermAs[Fun[Nat, Real]]("series_substitute(real_ring, P₂, d)"))))
						substitutedDenominator := arg.Have(
							"the substituted denominator contains the dilated linear factor",
							"series_substitute(real_ring, polynomial_mul(«1−T», Q₂), d) = "+
								"polynomial_mul(«1−Tᵈ»(d), series_substitute(real_ring, Q₂, d))",
							By(
								positive,
								set_basic.InUniv.Inst[Real](),
								formal_series.SeriesSubstituteMul.Read(ring).At(linear, Q2, d),
								formal_series.SeriesSubstituteLinearFactor.Read(ring).At(d)))
						powerStep := arg.Have(
							"separate one copy of the denominator from its power",
							"polynomial_pow(D, d) = polynomial_mul(D, polynomial_pow(D, d - 1))",
							By(degree, polynomial.PolynomialPowSuc.Read(ring).At(predecessor, D)))
						arg.Show(
							"the dth power of D is (1 − T) Q₁ L, and the dilated "+
								"factor 1 − Tᵈ is 1 − T times the geometric sum",
							By(Ddef, Ldef, Edef, Fdef, Vdef, powerStep, substitutedDenominator, crossEquation, geometric))
					}))
				polynomialD := arg.Have(
					"the full denominator of a is a polynomial",
					"polynomial_over(𝕌, D)",
					By(Ddef, partsA[1], geometric, polynomial.PolynomialMulOver.Read(ring).At(linear, Q1)))
				powerData := arg.Have(
					"the remaining denominator power and numerator power are polynomials",
					"polynomial_over(𝕌, L) ∧ "+
						"polynomial_over(𝕌, V) ∧ "+
						"polynomial_eval(L, &1) = monoid_pow(real_mul, &1, polynomial_eval(D, &1), d - 1) ∧ "+
						"polynomial_eval(V, &1) = monoid_pow(real_mul, &1, polynomial_eval(P₁, &1), d)",
					Ldef.Rw(),
					Vdef.Rw(),
					By(
						partsA[0],
						polynomialD,
						set_basic.InUniv.Inst[Real](),
						polynomial.PolynomialPowOver.Read(ring).At(predecessor, D),
						polynomial.PolynomialPowOver.Read(ring).At(d, P1),
						polynomial_evaluation.EvalPow.Read(ring).AsFact().At(predecessor, D, one),
						polynomial_evaluation.EvalPow.Read(ring).AsFact().At(d, P1, one)))
				substituteData := arg.Have(
					"the substituted numerator and denominator are polynomials with the same value at one",
					"polynomial_over(𝕌, E) ∧ polynomial_over(𝕌, F) ∧ polynomial_eval(F, &1) = polynomial_eval(Q₂, &1)",
					By(
						Normalized,
						positive,
						Edef,
						Fdef,
						partsB[0],
						partsB[1],
						formal_series.SeriesSubstitutePolynomial.Read(ring).At(P2, d),
						formal_series.SeriesSubstitutePolynomial.Read(ring).At(Q2, d)))
				members := arg.Have(
					"the factors and T lie in the carrier of real polynomials, "+
						"T because the ring closer reads 1 − T as one less the atom T",
					"«1−T» ∈ «ℝ[T]» ∧ "+
						"basis_vector(1) ∈ «ℝ[T]» ∧ "+
						"Q₁ ∈ «ℝ[T]» ∧ "+
						"L ∈ «ℝ[T]» ∧ "+
						"E ∈ «ℝ[T]» ∧ "+
						"«1+…+Tᵈ⁻¹»(d) ∈ «ℝ[T]» ∧ "+
						"F ∈ «ℝ[T]» ∧ "+
						"V ∈ «ℝ[T]»",
					BySets(
						geometric,
						partsA[1],
						powerData,
						substituteData,
						polynomial.BasisVectorOver.Read(ring).At(arg.TermAs[Nat]("1"))))
				// The ring closer reads the polynomial ring's operations off its record.
				polynomialRing := arg.Simplified(
					polynomial.PolynomialRingOn.Read(ring),
					Fwd(polynomial.PolynomialRingDef))
				leftProduct := arg.TermAs[Fun[Nat, Real]]("polynomial_mul(polynomial_mul(Q₁, L), E)")
				rightProduct := arg.TermAs[Fun[Nat, Real]]("polynomial_mul(polynomial_mul(«1+…+Tᵈ⁻¹»(d), F), V)")
				cancelled := arg.Have(
					"cancel the linear factor 1 − T, a nonzero polynomial, in the polynomial integral domain",
					"polynomial_mul(polynomial_mul(Q₁, L), E) = polynomial_mul(polynomial_mul(«1+…+Tᵈ⁻¹»(d), F), V)",
					Derive(func(arg *Argument) {
						commonFactor := arg.Have(
							"associate the common linear factor to the outside",
							"polynomial_mul(«1−T», polynomial_mul(polynomial_mul(Q₁, L), E)) = "+
								"polynomial_mul(«1−T», polynomial_mul(polynomial_mul(«1+…+Tᵈ⁻¹»(d), F), V))",
							ByArith(polynomialRing, members, factored))
						constantNonzero := arg.Have(
							"the linear factor has nonzero constant coefficient",
							"«1−T»(0) ≠ &0",
							Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.BasisVectorDef)),
							ByArith())
						factorNonzero := arg.Have(
							"the linear factor is a nonzero polynomial",
							"«1−T» ≠ vec_zero(&0)",
							By(constantNonzero, vec_space.VecZeroDef))
						productsIn := arg.Have(
							"both products remaining after cancellation are polynomials",
							"polynomial_mul(polynomial_mul(Q₁, L), E) ∈ «ℝ[T]» ∧ "+
								"polynomial_mul(polynomial_mul(«1+…+Tᵈ⁻¹»(d), F), V) ∈ «ℝ[T]»",
							By(comm_ring.MulIn.Read(polynomialRing), members))
						arg.Show(
							"a nonzero factor cancels in the polynomials over the real integral domain",
							By(
								factorNonzero,
								members,
								productsIn,
								commonFactor,
								integral_domain.MulCancelLeft.Read(
									polynomial.PolynomialDomain.Read(RealIntegralDomain)).AsFact().At(
									linear, leftProduct, rightProduct)))
					}))
				zeroProduct := arg.Have(
					"evaluate at one: the left side vanishes with the remaining power "+
						"of a's denominator, the right side is d times the values of F and V",
					"&0 = &d * polynomial_eval(F, &1) * polynomial_eval(V, &1)",
					Derive(func(arg *Argument) {
						first := arg.TermAs[Nat]("1")
						factorRoot := arg.Have(
							"1 − T, the binomial at c = 1 and shift one, vanishes at one, "+
								"its value there being one less one times the first power of one",
							"polynomial_eval(«1−T», &1) = &0",
							ByArith(
								set_basic.InUniv.Inst[Real](),
								vec_space.SmulOne.Read(real_ring.CommRing).At(arg.TermAs[Fun[Nat, Real]]("basis_vector(1)")),
								comm_monoid.IdentityPowOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(first),
								polynomial_evaluation.BinomialValue.Read(ring).AsFact().At(one, one, first)))
						denominatorRoot := arg.Have(
							"the denominator of a vanishes at one",
							"polynomial_eval(D, &1) = &0",
							By(
								comm_ring.OneIn.Read(ring),
								Ddef,
								factorRoot,
								geometric,
								partsA[1],
								polynomial_evaluation.EvalMulRoot.Read(ring).AsFact().At(linear, Q1, one)))
						positiveExponent := arg.Have(
							"the remaining denominator power has positive exponent",
							"d - 1 ≠ 0",
							ByArith(degree))
						remainingRoot := arg.Have(
							"the remaining denominator power vanishes at one",
							"polynomial_eval(L, &1) = &0",
							By(
								denominatorRoot,
								positiveExponent,
								powerData,
								real_pow.MonoidPow.At(arg.TermAs[Real]("&0"), predecessor),
								real_pow.ZeroPow.At(predecessor)))
						innerProducts := arg.Have(
							"the inner convolution products are polynomials",
							"polynomial_over(𝕌, polynomial_mul(Q₁, L)) ∧ polynomial_over(𝕌, polynomial_mul(«1+…+Tᵈ⁻¹»(d), F))",
							By(comm_ring.MulIn.Read(polynomialRing), members))
						innerLeft := arg.TermAs[Fun[Nat, Real]]("polynomial_mul(Q₁, L)")
						innerRight := arg.TermAs[Fun[Nat, Real]]("polynomial_mul(«1+…+Tᵈ⁻¹»(d), F)")
						productValues := arg.Have(
							"evaluation multiplies the values of all three factors",
							"polynomial_eval(polynomial_mul(polynomial_mul(Q₁, L), E), &1) = "+
								"polynomial_eval(Q₁, &1) * polynomial_eval(L, &1) * polynomial_eval(E, &1) ∧ "+
								"polynomial_eval(polynomial_mul(polynomial_mul(«1+…+Tᵈ⁻¹»(d), F), V), &1) = "+
								"polynomial_eval(«1+…+Tᵈ⁻¹»(d), &1) * polynomial_eval(F, &1) * polynomial_eval(V, &1)",
							BySets(
								members,
								innerProducts,
								polynomial_evaluation.EvalMul.Read(ring).AsFact().At(Q1, L, one),
								polynomial_evaluation.EvalMul.Read(ring).AsFact().At(innerLeft, E, one),
								polynomial_evaluation.EvalMul.Read(ring).AsFact().At(geometricSum, F, one),
								polynomial_evaluation.EvalMul.Read(ring).AsFact().At(innerRight, V, one)))
						evaluated := arg.Have(
							"evaluate both sides at one",
							"polynomial_eval(polynomial_mul(polynomial_mul(Q₁, L), E), &1) = "+
								"polynomial_eval(polynomial_mul(polynomial_mul(«1+…+Tᵈ⁻¹»(d), F), V), &1)",
							By(cancelled))
						arg.Show(
							"so the value of the left side, zero, is d times the values of F and V",
							ByArith(evaluated, productValues, remainingRoot, geometric))
					}))
				nonzeroDegree := arg.Have(
					"the substitution degree is nonzero",
					"d ≠ 0",
					ByArith(degree))
				nonzeroValues := arg.Have(
					"every factor on the right has nonzero value at one",
					"polynomial_eval(V, &1) ≠ &0 ∧ polynomial_eval(F, &1) ≠ &0 ∧ &d ≠ &0",
					By(
						nonzeroDegree,
						powerData,
						substituteData,
						partsA[3],
						partsB[4],
						At(nonzeroPower, arg.TermAs[Real]("polynomial_eval(P₁, &1)"), d),
						real_construction.OfNumEq.At(d, arg.TermAs[Nat]("0"))))
				degreeValue, valueF := arg.TermAs[Real]("&d"), arg.TermAs[Real]("polynomial_eval(F, &1)")
				arg.Show(
					"a product of the three nonzero values cannot vanish",
					By(
						zeroProduct,
						nonzeroValues,
						real_ring.MulEqZero.At(degreeValue, valueF),
						real_ring.MulEqZero.At(
							arg.TermAs[Real]("&d * polynomial_eval(F, &1)"), arg.TermAs[Real]("polynomial_eval(V, &1)"))))
			})
		}),
})}
