// rescaling.go — multiplying by a linear factor x − c shifts the coefficients
// up by one and subtracts c times them, and rescaling the coefficients of a
// polynomial of degree at most m by the powers of b, b^(m−i) at i, carries the
// factor x − c of a product to the factor x − c·b.

package polynomial_roots

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// LinearConvolution — the coefficient of (x − c)·p at n is p(n − 1) − c·p(n),
// the first term absent at n = 0: the product commutes, distributes over the
// difference, multiplying by x shifts the coefficients up by one, and
// multiplying by the constant c scales them.
var LinearConvolution = linearConvolutionThm{family.Add(registry.ProofEntry{
	Name: "LinearConvolution",
	Key:  "prop_dfe22301c524c6f5",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀c:A. ∀p:(num → A). ∀n:num.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_mul(«linear»(c), p, n) = COND(1 ≤ n, p(n - 1), R.zero) - c * p(n)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			c *Member[A, on.R],
			p *Arrow[Nat, A],
			n *Expr[Nat],
			pOver Fact,
		) {
			linear := arg.TermAs[Fun[Nat, A]]("«linear»(c)")
			shift := arg.TermAs[Fun[Nat, A]]("basis_vector(1)")
			scaled := arg.TermAs[Fun[Nat, A]]("c • basis_vector(0)")
			linearOver := arg.Have(
				"x − c is a polynomial over R",
				"polynomial_over(R.carrier, «linear»(c))",
				By(LinearFactor.Read(ring).At(c)))
			commuted := arg.Have(
				"the product commutes",
				"polynomial_mul(«linear»(c), p) = polynomial_mul(p, «linear»(c))",
				By(
					pOver,
					linearOver,
					polynomial.PolynomialOverDef,
					polynomial.PolynomialMulComm.Read(ring).At(linear, p)))
			coefficients := arg.Have(
				"the coefficients of p, of x and of c lie in R",
				"∀i:num. p(i) ∈ R.carrier ∧ basis_vector(1, i) ∈ R.carrier ∧ (c • basis_vector(0))(i) ∈ R.carrier",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					b.Show(
						"each is a coefficient of p, a one or a zero, or c times one of them",
						SplitConj(
							Case(
								"the coefficient of p and that of x",
								SplitConj(
									Case(
										"p is a polynomial over R",
										By(pOver, polynomial.PolynomialOverDef)),
									Case(
										"x has the coefficients one and zero",
										By(vec_space.BasisVectorDef, comm_ring.ZeroIn.Read(ring), comm_ring.OneIn.Read(ring))))),
							Case(
								"c times a coefficient of the constant one",
								By(
									c,
									vec_space.VecScalarMulDef,
									vec_space.BasisVectorDef,
									comm_ring.ZeroIn.Read(ring),
									comm_ring.OneIn.Read(ring),
									comm_ring.MulIn.Read(ring)))))
				}))
			distributed := arg.Have(
				"p times x − c is p times x less c times p",
				"polynomial_mul(p, «linear»(c)) = polynomial_mul(p, basis_vector(1)) - c • p",
				By(
					coefficients,
					c,
					pOver,
					polynomial.PolynomialMulSub.Read(ring).At(p, shift, scaled),
					polynomial.PolynomialMulConstant.Read(ring).At(c, p)))
			arg.Show(
				"and multiplying by x shifts the coefficients up by one",
				commuted.Rw(),
				distributed.Rw(),
				By(
					pOver,
					vec_space.VecSubDef,
					vec_space.VecScalarMulDef,
					polynomial.PolynomialOverDef,
					polynomial.PolynomialMulBasisVector.Read(ring).At(p, arg.TermAs[Nat]("1"), n)))
		}),
})}

// RescaledLinearFactor — weighting the coefficients of a polynomial p of
// degree at most m by the powers of b, b^(m−i) at i, turns the factor x − c
// of (x − c)·p, weighted the same way to degree m + 1, into the factor
// x − c·b: coefficient by coefficient both sides are b^(m+1−i)·p(i − 1) −
// c·b·b^(m−i)·p(i), the first term absent at i = 0 and the second past m.
var RescaledLinearFactor = rescaledLinearFactorThm{family.Add(registry.ProofEntry{
	Name: "RescaledLinearFactor",
	Key:  "prop_8737a6fb7abd74cc",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀b c:A. ∀m:num. ∀p:(num → A).",
		Hypotheses: []string{
			"b ∈ R.carrier",
			"c ∈ R.carrier",
			"polynomial_over(R.carrier, p)",
			"polynomial_degree(p) ≤ m",
		},
		Conclusion: "(λi:num. " +
			"    COND(i ≤ suc(m), " +
			"        monoid_pow(R.mul, R.one, b, suc(m) - i) * polynomial_mul(«linear»(c), p, i), " +
			"        R.zero)) = " +
			"polynomial_mul(«linear»(c * b), «weighted»)",
		Abbrev: Abbrev{
			{Name: "weighted", Text: "λi:num. COND(i ≤ m, monoid_pow(R.mul, R.one, b, m - i) * p(i), R.zero)"},
		},
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			b, c *Member[A, on.R],
			m *Expr[Nat],
			p *Arrow[Nat, A],
			hypotheses Fact,
		) {
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			parts := arg.Conjuncts(
				hypotheses,
				"p is a polynomial over R",
				"p has degree at most m")
			pOver, bounded := parts[0], parts[1]
			weighted := arg.TermAs[Fun[Nat, A]]("«weighted»")
			coefficients := arg.Have(
				"the coefficients of p lie in R",
				"∀j:num. p(j) ∈ R.carrier",
				By(pOver, polynomial.PolynomialOverDef))
			pastDegree := arg.Have(
				"p vanishes past its degree",
				"vec⟨suc(polynomial_degree(p))⟩(p)",
				By(pOver, polynomial.DegreeVec))
			vanishing := arg.Have(
				"so p vanishes past m",
				"∀j:num. m < j ⇒ p(j) = R.zero",
				Derive(func(d *Argument) {
					d.FixAs[Nat]("j")
					past := d.Assume()
					beyond := d.Have(
						"j lies past the degree of p",
						"suc(polynomial_degree(p)) ≤ j",
						ByArith(past, bounded))
					d.Show(
						"where p is zero",
						By(beyond, pastDegree, vec_space.VecDef))
				}))
			weightedPast := arg.Have(
				"the weighted coefficients vanish past m",
				"vec⟨suc(m)⟩(«weighted»)",
				ByArith(vec_space.VecDef))
			weightedIn := arg.Have(
				"and lie in R, each a power of b times a coefficient of p",
				"∀i:num. «weighted»(i) ∈ R.carrier",
				Derive(func(d *Argument) {
					i := d.FixAs[Nat]("i")
					d.Show(
						"b^(m−i) and p(i) lie in R",
						By(
							coefficients.At(i),
							b,
							comm_monoid.PowIn.Read(mulMonoid).AsFact().At(b, d.TermAs[Nat]("m - i")),
							comm_ring.MulIn.Read(ring),
							comm_ring.ZeroIn.Read(ring)))
				}))
			weightedOver := arg.Have(
				"so the weighted coefficients are a polynomial over R",
				"polynomial_over(R.carrier, «weighted»)",
				By(weightedIn, weightedPast, polynomial.PolynomialOverDef))
			cb := arg.MemberOf[on.R](arg.TermAs[A]("c * b"), arg.Have(
				"c·b lies in R",
				"c * b ∈ R.carrier",
				By(c, b, comm_ring.MulIn.Read(ring))))
			arg.Show(
				"coefficient by coefficient",
				Funext(),
				Derive(func(d *Argument) {
					j := d.FixAs[Nat]("j")
					left := d.Have(
						"the coefficient of (x − c)·p at j is p(j − 1) − c·p(j)",
						"polynomial_mul(«linear»(c), p, j) = COND(1 ≤ j, p(j - 1), R.zero) - c * p(j)",
						By(c, pOver, Read(LinearConvolution, ring).At(c, p, j)))
					right := d.Have(
						"and that of (x − c·b) times the weighted p is the "+
							"weighted p(j − 1) less c·b times the weighted p(j)",
						"polynomial_mul(«linear»(c * b), «weighted», j) = "+
							"COND(1 ≤ j, "+
							"    COND(j - 1 ≤ m, monoid_pow(R.mul, R.one, b, m - (j - 1)) * p(j - 1), R.zero), "+
							"    R.zero) - "+
							"c * b * COND(j ≤ m, monoid_pow(R.mul, R.one, b, m - j) * p(j), R.zero)",
						By(cb, weightedOver, Read(LinearConvolution, ring).At(cb, weighted, j)))
					d.Do(left.Rw(), right.Rw())
					d.Cases(d.TermAs[Bool]("j = 0"))
					d.When(
						"at the constant coefficient the shifted term is absent",
						func(e *Argument, zero Fact) {
							guards := e.Have(
								"0 is at most m and below 1",
								"j ≤ suc(m) ∧ ¬(1 ≤ j) ∧ j ≤ m ∧ suc(m) - j = suc(m - j)",
								ByArith(zero))
							lhs := e.Have(
								"the left coefficient is b^(m+1)·(0 − c·p(0))",
								"COND(j ≤ suc(m), "+
									"    monoid_pow(R.mul, R.one, b, suc(m) - j) * (COND(1 ≤ j, p(j - 1), R.zero) - c * p(j)), "+
									"    R.zero) = "+
									"monoid_pow(R.mul, R.one, b, suc(m) - j) * (R.zero - c * p(j))",
								By(guards))
							rhs := e.Have(
								"the right one is 0 − c·b·b^m·p(0)",
								"COND(1 ≤ j, "+
									"    COND(j - 1 ≤ m, monoid_pow(R.mul, R.one, b, m - (j - 1)) * p(j - 1), R.zero), "+
									"    R.zero) - "+
									"c * b * COND(j ≤ m, monoid_pow(R.mul, R.one, b, m - j) * p(j), R.zero) = "+
									"R.zero - c * b * (monoid_pow(R.mul, R.one, b, m - j) * p(j))",
								By(guards))
							exponents := e.Conjuncts(
								guards,
								"j ≤ m + 1",
								"1 > j",
								"j ≤ m",
								"m + 1 − j is suc(m − j)")
							power := e.Have(
								"b^(m+1) is b·b^m",
								"monoid_pow(R.mul, R.one, b, suc(m - j)) = b * monoid_pow(R.mul, R.one, b, m - j)",
								By(comm_monoid.MonoidPowDef))
							e.Show(
								"which agree",
								lhs.Rw(),
								rhs.Rw(),
								exponents[3].Rw(),
								power.Rw(),
								ByArith(
									ring,
									b,
									c,
									coefficients.At(j),
									comm_monoid.PowIn.Read(mulMonoid).AsFact().At(b, e.TermAs[Nat]("m - j"))))
						})
					d.Otherwise(
						"past the constant coefficient",
						func(e *Argument, nonzero Fact) {
							e.Cases(e.TermAs[Bool]("j ≤ m"))
							e.When(
								"up to m both terms are present",
								func(f *Argument, within Fact) {
									guards := f.Have(
										"j lies between 1 and m",
										"j ≤ suc(m) ∧ 1 ≤ j ∧ j - 1 ≤ m ∧ suc(m) - j = suc(m - j) ∧ m - (j - 1) = suc(m - j)",
										ByArith(nonzero, within))
									lhs := f.Have(
										"the left coefficient is b^(m+1−j)·(p(j − 1) − c·p(j))",
										"COND(j ≤ suc(m), "+
											"    monoid_pow(R.mul, R.one, b, suc(m) - j) * (COND(1 ≤ j, p(j - 1), R.zero) - c * p(j)), "+
											"    R.zero) = "+
											"monoid_pow(R.mul, R.one, b, suc(m) - j) * (p(j - 1) - c * p(j))",
										By(guards))
									rhs := f.Have(
										"the right one is b^(m−(j−1))·p(j − 1) − c·b·b^(m−j)·p(j)",
										"COND(1 ≤ j, "+
											"    COND(j - 1 ≤ m, monoid_pow(R.mul, R.one, b, m - (j - 1)) * p(j - 1), R.zero), "+
											"    R.zero) - "+
											"c * b * COND(j ≤ m, monoid_pow(R.mul, R.one, b, m - j) * p(j), R.zero) = "+
											"monoid_pow(R.mul, R.one, b, m - (j - 1)) * p(j - 1) - "+
											"c * b * (monoid_pow(R.mul, R.one, b, m - j) * p(j))",
										By(guards, within))
									exponents := f.Conjuncts(
										guards,
										"j ≤ m + 1",
										"1 ≤ j",
										"j − 1 ≤ m",
										"m + 1 − j is suc(m − j)",
										"m − (j − 1) is suc(m − j)")
									power := f.Have(
										"b^(m+1−j) is b·b^(m−j)",
										"monoid_pow(R.mul, R.one, b, suc(m - j)) = b * monoid_pow(R.mul, R.one, b, m - j)",
										By(comm_monoid.MonoidPowDef))
									f.Show(
										"which agree",
										lhs.Rw(),
										rhs.Rw(),
										exponents[3].Rw(),
										exponents[4].Rw(),
										power.Rw(),
										ByArith(
											ring,
											b,
											c,
											coefficients.At(j),
											coefficients.At(f.TermAs[Nat]("j - 1")),
											comm_monoid.PowIn.Read(mulMonoid).AsFact().At(b, f.TermAs[Nat]("m - j"))))
								})
							e.Otherwise(
								"past m",
								func(f *Argument, past Fact) {
									f.Cases(f.TermAs[Bool]("j = suc(m)"))
									f.When(
										"at m + 1 only the shifted term is left, with weight one",
										func(g *Argument, top Fact) {
											guards := g.Have(
												"j is m + 1",
												"j ≤ suc(m) ∧ 1 ≤ j ∧ j - 1 ≤ m ∧ m < j ∧ suc(m) - j = 0 ∧ m - (j - 1) = 0",
												ByArith(top))
											lhs := g.Have(
												"the left coefficient is b^0·(p(m) − c·p(m + 1))",
												"COND(j ≤ suc(m), "+
													"    monoid_pow(R.mul, R.one, b, suc(m) - j) * (COND(1 ≤ j, p(j - 1), R.zero) - c * p(j)), "+
													"    R.zero) = "+
													"monoid_pow(R.mul, R.one, b, suc(m) - j) * (p(j - 1) - c * p(j))",
												By(guards))
											rhs := g.Have(
												"the right one is b^0·p(m) − c·b·0",
												"COND(1 ≤ j, "+
													"    COND(j - 1 ≤ m, monoid_pow(R.mul, R.one, b, m - (j - 1)) * p(j - 1), R.zero), "+
													"    R.zero) - "+
													"c * b * COND(j ≤ m, monoid_pow(R.mul, R.one, b, m - j) * p(j), R.zero) = "+
													"monoid_pow(R.mul, R.one, b, m - (j - 1)) * p(j - 1) - c * b * R.zero",
												By(guards, past))
											exponents := g.Conjuncts(
												guards,
												"j ≤ m + 1",
												"1 ≤ j",
												"j − 1 ≤ m",
												"j lies past m",
												"m + 1 − j is zero",
												"m − (j − 1) is zero")
											ends := g.Conjuncts(
												g.Have(
													"p(m + 1) is zero and b^0 is one",
													"p(j) = R.zero ∧ monoid_pow(R.mul, R.one, b, 0) = R.one",
													By(vanishing.At(j), exponents[3], comm_monoid.MonoidPowDef)),
												"p vanishes at m + 1",
												"b^0 is one")
											g.Show(
												"which agree",
												lhs.Rw(),
												rhs.Rw(),
												exponents[4].Rw(),
												exponents[5].Rw(),
												ends[1].Rw(),
												ends[0].Rw(),
												ByArith(ring, b, c, coefficients.At(g.TermAs[Nat]("j - 1"))))
										})
									f.Otherwise(
										"beyond m + 1 both coefficients vanish",
										func(g *Argument, beyond Fact) {
											guards := g.Have(
												"j lies past m + 1",
												"¬(j ≤ suc(m)) ∧ 1 ≤ j ∧ ¬(j - 1 ≤ m)",
												ByArith(past, beyond))
											lhs := g.Have(
												"the left coefficient is zero",
												"COND(j ≤ suc(m), "+
													"    monoid_pow(R.mul, R.one, b, suc(m) - j) * (COND(1 ≤ j, p(j - 1), R.zero) - c * p(j)), "+
													"    R.zero) = "+
													"R.zero",
												By(guards))
											rhs := g.Have(
												"and so is the right one",
												"COND(1 ≤ j, "+
													"    COND(j - 1 ≤ m, monoid_pow(R.mul, R.one, b, m - (j - 1)) * p(j - 1), R.zero), "+
													"    R.zero) - "+
													"c * b * COND(j ≤ m, monoid_pow(R.mul, R.one, b, m - j) * p(j), R.zero) = "+
													"R.zero - c * b * R.zero",
												By(guards, past))
											g.Show(
												"zero is zero less c·b·0",
												lhs.Rw(),
												rhs.Rw(),
												ByArith(ring, b, c))
										})
								})
						})
				}))
		}),
})}
