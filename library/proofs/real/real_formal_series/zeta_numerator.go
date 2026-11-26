// zeta_numerator.go — the zeta numerator (1 − T)(1 − qT)·A of a
// Riemann–Roch count A: a series on the multiples of d with such a tail has
// a simple pole at one, the numerator's support through degree 2g, its
// constant coefficient and value at one, and the reciprocity of its
// coefficients.

package real_formal_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_zpow"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// EventuallyConstantDifference — for a real series f that is the constant C
// from M on, (1 − T)·f vanishes from M + 1 on, so is a polynomial, and takes
// the value C at one. Multiplying by 1 − T takes the first difference
// f(n) − f(n − 1) (BinomialConvolution at c = 1 and shift one), whose two
// terms are both C from M + 1 on; at one the polynomial takes the sum of its
// coefficients below M + 1 (EvalOneBelow), and those first differences
// telescope to f(M), which is C.
var EventuallyConstantDifference = eventuallyConstantDifferenceThm{family.Add(registry.ProofEntry{
	Name: "EventuallyConstantDifference",
	Key:  "prop_bec96ce457b7e4cc",
	Build: family.Sections(Statement{
		Binders: "∀f:(num → real). ∀C:real. ∀M:num.",
		Hypotheses: []string{
			"∀i:num. M ≤ i ⇒ f(i) = C",
		},
		Conclusion: "vec⟨suc(M)⟩(polynomial_mul(«1−T», f)) ∧ " +
			"polynomial_over(𝕌, polynomial_mul(«1−T», f)) ∧ " +
			"polynomial_eval(polynomial_mul(«1−T», f), &1) = C",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			ring := real_ring.CommRingOn
			regular := module.RegularModuleOn.Read(ring)

			sumBelow := ctx.Lemma("∀f:(num → real). "+
				"    module_sum(real_add, &0, {i:num | i < 0}, f) = &0 ∧ "+
				"    (∀k:num. "+
				"        module_sum(real_add, &0, {i:num | i < suc(k)}, f) = "+
				"        module_sum(real_add, &0, {i:num | i < k}, f) + f(k))",
				func(arg *Argument, f *Arrow[Nat, Real]) {
					arg.Show(
						"the finite sum starts at zero and adds its last term",
						By(set_basic.InUniv.Inst[Real](), module.ModuleSumBelowClauses.Read(regular).At(f)))
				})

			telescope := ctx.Lemma("∀b:(num → real). ∀k:num. "+
				"    module_sum(real_add, &0, {j:num | j < suc(k)}, λj:num. b(j) + COND(1 ≤ j, -b(j - 1), &0)) = "+
				"    b(k)",
				func(arg *Argument, b *Arrow[Nat, Real], k *Expr[Nat]) {
					arg.Induct(k)
					arg.Base(
						"the first difference starts at b of zero",
						Simp(Fwd(sumBelow)),
						ByArith())
					arg.Step(
						"the next two endpoint terms cancel",
						func(arg *Argument, ih Fact) {
							arg.Show(
								"retain only the new endpoint",
								Simp(Fwd(sumBelow)),
								ByArith(ih, At(sumBelow, arg.TermAs[Fun[Nat, Real]]("λj:num. b(j) + COND(1 ≤ j, -b(j - 1), &0)"))))
						})
				})

			return ctx.Theorem(headline, func(
				arg *Argument,
				f *Arrow[Nat, Real],
				C *Expr[Real],
				M *Expr[Nat],
				tail Fact,
			) {
				difference := arg.Have(
					"multiplying by 1 − T, which is 1 − 1·T, takes the first difference",
					"∀n:num. polynomial_mul(«1−T», f, n) = f(n) + COND(1 ≤ n, -f(n - 1), &0)",
					Derive(func(arg *Argument) {
						n := arg.FixAs[Nat]("n")
						arg.Show(
							"the binomial law at c = 1 and shift one, every real "+
								"lying in the carrier, one times f(n − 1) being f(n − 1)",
							ByArith(
								set_basic.InUniv.Inst[Real](),
								vec_space.SmulOne.Read(real_ring.CommRing).At(arg.TermAs[Fun[Nat, Real]]("basis_vector(1)")),
								polynomial.BinomialConvolution.Read(ring).AsFact().At(
									arg.TermAs[Real]("&1"), arg.TermAs[Nat]("1"), n, f)))
					}))
				support := arg.Have(
					"from suc(M) on, f(n) and f(n − 1) are both C, so the difference vanishes",
					"vec⟨suc(M)⟩(polynomial_mul(«1−T», f))",
					Derive(func(arg *Argument) {
						arg.Do(Unfold(vec_space.VecDef))
						i := arg.FixAs[Nat]("i")
						beyond := arg.Assume()
						arg.Show(
							"the two values cancel",
							ByArith(beyond, difference.At(i), tail.At(i), tail.At(arg.TermAs[Nat]("i - 1"))))
					}))
				isPolynomial := arg.Have(
					"so the difference is a real polynomial",
					"polynomial_over(𝕌, polynomial_mul(«1−T», f))",
					By(support, polynomial.PolynomialOverDef, set_basic.InUniv.Inst[Real]()))
				successor := arg.TermAs[Nat]("suc(M)")
				value := arg.Have(
					"its value at one telescopes to f(M), which is C",
					"polynomial_eval(polynomial_mul(«1−T», f), &1) = C",
					CalcEq(
						Leg(
							arg.TermAs[Real]("module_sum(real_add, &0, {i:num | i < suc(M)}, polynomial_mul(«1−T», f))"),
							"at one, a polynomial takes the sum of its coefficients below its support bound",
							By(
								isPolynomial,
								support,
								polynomial_evaluation.EvalOneBelow.Read(ring).AsFact().At(
									successor, arg.TermAs[Fun[Nat, Real]]("polynomial_mul(«1−T», f)")))),
						Leg(
							arg.TermAs[Real](
								"module_sum(real_add, &0, {j:num | j < suc(M)}, λj:num. f(j) + COND(1 ≤ j, -f(j - 1), &0))"),
							"each coefficient is a first difference",
							By(difference, module.ModuleSumCongruence)),
						Leg(
							arg.TermAs[Real]("f(M)"),
							"the first differences telescope",
							Cite(telescope)),
						FinalLeg(
							"and f is C from M on",
							ByArith(tail.At(M)))))
				arg.Show(
					"the difference vanishes from suc(M) on, is a polynomial and takes the value C at one",
					By(support, isPolynomial, value))
			})
		}),
})}

// PeriodicTailRationality — a series A, zero off the multiples of d and on
// them eventually (q − 1)·A(n) = h·(q^(n+1−g) − 1), is cleared to a
// polynomial by the two d-step factors 1 − Tᵈ and 1 − qᵈTᵈ and has a simple
// pole at one. A is the series B, B(j) = A(d·j), with Tᵈ substituted for T,
// and on B the d-steps are single steps: the tail of B is geometric with
// ratio qᵈ, so U = (1 − qᵈT)·B is eventually the constant
// C = h·(qᵈ − 1)/(q − 1), which is not zero; (1 − T)·U is then a polynomial
// with value C at one, and with 1 − qᵈT, whose value 1 − qᵈ at one is not
// zero, it witnesses the simple pole of B. Substituting Tᵈ carries
// (1 − T)(1 − qᵈT)·B to (1 − Tᵈ)(1 − qᵈTᵈ)·A (SeriesSubstituteMul,
// SeriesSubstituteLinearFactor, SeriesSubstituteBinomial), a polynomial again
// (SeriesSubstitutePolynomial), and the simple pole of B to that of A
// (SimplePoleSubstitute). The sequence a is indexed by the integers because
// it is RiemannRochNumerator's, whose genus-zero tail reads a(−1); here only
// its values at the naturals enter.
var PeriodicTailRationality = periodicTailRationalityThm{family.Add(registry.ProofEntry{
	Name: "PeriodicTailRationality",
	Key:  "prop_6d87b1c43b46c0d2",
	Build: family.Sections(Statement{
		Binders: "∀q g h d:num. ∀a:(int → real).",
		Hypotheses: []string{
			"1 < q",
			"0 < h",
			"0 < d",
			"∀n:num. ¬(d ∣ n) ⇒ a(int_of_num(n)) = &0",
			"∃N:num. ∀n:num. " +
				"    N ≤ n ∧ d ∣ n ⇒ " +
				"    &(q - 1) * a(int_of_num(n)) = " +
				"    &h * (real_zpow(&q, int_of_num(n) + int_of_num(1) - int_of_num(g)) - &1)",
		},
		Conclusion: "polynomial_over(𝕌, " +
			"    polynomial_mul(polynomial_mul(«1−Tᵈ»(d), «1−qᵈTᵈ»(q, d)), «coefficients»(a))) ∧ " +
			"series_simple_pole_one(«coefficients»(a))",
		Abbrev: Abbrev{
			{Name: "1−qᵈTᵈ", Text: "λq:num. λd:num. basis_vector(0) - &q ^ d • basis_vector(d)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			ring := real_ring.CommRingOn

			linearProduct := ctx.Lemma("∀c:real. ∀f:(num → real). ∀n:num. "+
				"    polynomial_mul(basis_vector(0) - c • basis_vector(1), f, n) = "+
				"    f(n) + COND(1 ≤ n, -(c * f(n - 1)), &0)",
				func(arg *Argument, c *Expr[Real], f *Arrow[Nat, Real], n *Expr[Nat]) {
					arg.Show(
						"the binomial law at shift one, read at the real ring, every real lying in its carrier",
						By(
							set_basic.InUniv.Inst[Real](),
							polynomial.BinomialConvolution.Read(ring).AsFact().At(c, arg.TermAs[Nat]("1"), n, f)))
				})

			tailCoefficient := ctx.Lemma(Statement{
				Binders: "∀q g h d N:num. ∀a:(int → real). ∀j:num.",
				Hypotheses: []string{
					"1 < q",
					"0 < d",
					"suc(N) ≤ j",
					"∀m:num. " +
						"    N ≤ m ∧ d ∣ m ⇒ " +
						"    &(q - 1) * a(m) = &h * (real_zpow(&q, int_of_num(m) + int_of_num(1) - int_of_num(g)) - &1)",
				},
				Conclusion: "polynomial_mul(basis_vector(0) - &q ^ d • basis_vector(1), " +
					"    λi:num. a(int_of_num(d * i)), " +
					"    j) = " +
					"&h * (&q ^ d - &1) / &(q - 1)",
			},
				func(
					arg *Argument,
					q, g, h, d, N *Expr[Nat],
					a *Arrow[Int, Real],
					j *Expr[Nat],
					larger, positive, later, tail Fact,
				) {
					difference := arg.Have(
						"the scaled tail difference: (q − 1)·(B(j) − qᵈ·B(j − 1)) is h·(qᵈ − 1)",
						"&(q - 1) * (a(int_of_num(d * j)) - &q ^ d * a(int_of_num(d * (j - 1)))) = &h * (&q ^ d - &1)",
						Derive(func(arg *Argument) {
							current, previous := arg.TermAs[Nat]("d * j"), arg.TermAs[Nat]("d * (j - 1)")
							step := arg.Have(
								"d·j is d·(j − 1) plus d, and both are multiples of d in the tail",
								"d * j = d * (j - 1) + d ∧ N ≤ d * (j - 1) ∧ N ≤ d * j ∧ d ∣ d * j ∧ d ∣ d * (j - 1)",
								ByArith(
									positive,
									later,
									nat_order.LessEqSelfMul.At(d, j),
									nat_order.LessEqSelfMul.At(arg.TermAs[Nat]("j - 1"), d),
									nat_monus.LeftSubDistrib.At(d, j, arg.TermAs[Nat]("1")),
									nat_divides.DividesOwnMultiple.At(d, j),
									nat_divides.DividesOwnMultiple.At(d, arg.TermAs[Nat]("j - 1"))))
							base := arg.Have(
								"the base q is nonzero",
								"&q ≠ &0",
								ByArith(larger, real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("1"), q)))
							embedded := arg.Have(
								"as integers too, d·j is d·(j − 1) plus d",
								"d * j = d * (j - 1) + int_of_num(d)",
								By(step, int_embed.OfNumAdd.At(previous, d)))
							exponent := arg.Have(
								"so the exponent at d·j is d more than the exponent at d·(j − 1)",
								"d * (j - 1) + &1 - g + d = d * j + &1 - int_of_num(g)",
								ByArith(embedded))
							equations := arg.Have(
								"read the two tail equations through the d-step power law",
								"&(q - 1) * a(int_of_num(d * j)) = "+
									"&h * (real_zpow(&q, int_of_num(d * (j - 1)) + int_of_num(1) - int_of_num(g)) * &q ^ d - &1) ∧ "+
									"&(q - 1) * a(int_of_num(d * (j - 1))) = "+
									"&h * (real_zpow(&q, int_of_num(d * (j - 1)) + int_of_num(1) - int_of_num(g)) - &1)",
								By(
									step,
									base,
									exponent,
									tail.At(current),
									tail.At(previous),
									real_zpow.ZpowAdd.At(
										arg.TermAs[Real]("&q"), arg.TermAs[Int]("d * (j - 1) + &1 - &g"), arg.TermAs[Int]("d")),
									real_zpow.ZpowOfNum.At(arg.TermAs[Real]("&q"), d)))
							parts := arg.Conjuncts(
								equations,
								"the later tail coefficient",
								"the earlier tail coefficient")
							arg.Show(
								"the geometric terms cancel in the scaled difference",
								ByArith(parts[0], Scaled(arg.TermAs[Real]("-&q ^ d"), parts[1])))
						}))
					scaled := arg.Have(
						"(1 − qᵈT)·B at j is B(j) less qᵈ·B(j − 1), constant after scaling by q − 1",
						"&(q - 1) * "+
							"polynomial_mul(basis_vector(0) - &q ^ d • basis_vector(1), λi:num. a(int_of_num(d * i)), j) = "+
							"&h * (&q ^ d - &1)",
						ByArith(
							larger,
							positive,
							later,
							tail,
							difference,
							At(
								linearProduct,
								arg.TermAs[Real]("&q ^ d"),
								arg.TermAs[Fun[Nat, Real]]("λi:num. a(int_of_num(d * i))"),
								j)))
					denominatorPositive := arg.Have(
						"q minus one is positive",
						"&0 < &(q - 1)",
						ByArith(larger, real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), arg.TermAs[Nat]("q - 1"))))
					arg.Show(
						"divide by the positive common factor",
						ByArith(Scaled(arg.TermAs[Real]("real_inv(&(q - 1))"), scaled), denominatorPositive))
				})

			simplePoleCore := ctx.Lemma(Statement{
				Binders: "∀c C:real. ∀b:(num → real). ∀M:num.",
				Hypotheses: []string{
					"c ≠ &1",
					"C ≠ &0",
					"∀j:num. M ≤ j ⇒ polynomial_mul(basis_vector(0) - c • basis_vector(1), b, j) = C",
				},
				Conclusion: "polynomial_over(𝕌, " +
					"    polynomial_mul(polynomial_mul(«1−T», basis_vector(0) - c • basis_vector(1)), b)) ∧ " +
					"series_simple_pole_one(b)",
			},
				func(
					arg *Argument,
					c, C *Expr[Real],
					b *Arrow[Nat, Real],
					M *Expr[Nat],
					notOne, nonzero, tail Fact,
				) {
					linear := arg.TermAs[Fun[Nat, Real]]("basis_vector(0) - c • basis_vector(1)")
					one, first := arg.TermAs[Real]("&1"), arg.TermAs[Nat]("1")
					numerator := arg.Have(
						"(1 − c·T)·b is eventually C, so 1 − T times it is a polynomial with value C at one",
						"polynomial_over(𝕌, "+
							"    polynomial_mul(«1−T», polynomial_mul(basis_vector(0) - c • basis_vector(1), b))) ∧ "+
							"polynomial_eval( "+
							"    polynomial_mul(«1−T», polynomial_mul(basis_vector(0) - c • basis_vector(1), b)), &1) = "+
							"C",
						By(
							tail,
							EventuallyConstantDifference.At(
								arg.TermAs[Fun[Nat, Real]]("polynomial_mul(basis_vector(0) - c • basis_vector(1), b)"), C, M)))
					regroup := arg.Have(
						"which is (1 − T)(1 − c·T)·b",
						"polynomial_mul(polynomial_mul(«1−T», basis_vector(0) - c • basis_vector(1)), b) = "+
							"polynomial_mul(«1−T», polynomial_mul(basis_vector(0) - c • basis_vector(1), b))",
						By(
							set_basic.InUniv.Inst[Real](),
							polynomial.PolynomialMulAssoc.Read(ring).At(arg.TermAs[Fun[Nat, Real]]("«1−T»"), linear, b)))
					denominator := arg.Have(
						"1 − c·T is a real polynomial",
						"polynomial_over(𝕌, basis_vector(0) - c • basis_vector(1))",
						By(
							set_basic.InUniv.Inst[Real](),
							module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
							comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring)),
							polynomial.BasisVectorOver.Read(ring).At(arg.TermAs[Nat]("0")),
							polynomial.BasisVectorOver.Read(ring).At(first)))
					constant := arg.Have(
						"starting with one",
						"(basis_vector(0) - c • basis_vector(1))(0) = &1",
						Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)),
						ByArith())
					value := arg.Have(
						"and taking at one the value 1 − c, which is not zero",
						"polynomial_eval(basis_vector(0) - c • basis_vector(1), &1) ≠ &0",
						ByArith(
							notOne,
							set_basic.InUniv.Inst[Real](),
							comm_monoid.IdentityPowOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(first),
							polynomial_evaluation.BinomialValue.Read(ring).AsFact().At(c, one, first)))
					arg.Show(
						"(1 − T)(1 − c·T)·b is a polynomial, and with 1 − c·T it witnesses the simple pole",
						SplitConj(
							Case(
								"the cleared series is the polynomial (1 − T)·(1 − c·T)·b",
								By(numerator, regroup)),
							Case(
								"(1 − T)·(1 − c·T)·b and 1 − c·T witness the simple pole",
								Derive(func(arg *Argument) {
									arg.Do(Simp(Fwd(SeriesSimplePoleDef)))
									arg.Take(arg.TermAs[Fun[Nat, Real]](
										"polynomial_mul(«1−T», polynomial_mul(basis_vector(0) - c • basis_vector(1), b))"))
									arg.Take(linear)
									arg.Show(
										"the witnesses are polynomials with the required values",
										ByArith(nonzero, numerator, regroup, denominator, constant, value))
								}))))
				})

			nonzeroValues := ctx.Lemma(Statement{
				Binders: "∀q h d:num.",
				Hypotheses: []string{
					"1 < q",
					"0 < h",
					"0 < d",
				},
				Conclusion: "&h * (&q ^ d - &1) / &(q - 1) ≠ &0 ∧ &q ^ d ≠ &1",
			},
				func(arg *Argument, q, h, d *Expr[Nat], larger, heightPositive, periodPositive Fact) {
					signs := arg.Have(
						"as reals, q exceeds one and h and q − 1 are positive; d is nonzero",
						"&1 < &q ∧ &0 < &h ∧ &0 < &(q - 1) ∧ d ≠ 0",
						ByArith(
							larger,
							heightPositive,
							periodPositive,
							real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("1"), q),
							real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), arg.TermAs[Nat]("q - 1")),
							real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), h)))
					power := arg.Have(
						"the d-th power of q is greater than one",
						"&1 < &q ^ d",
						ByArith(
							signs,
							real_pow.OnePow.At(d),
							real_pow.PowMonoBaseStrict.At(arg.TermAs[Real]("&1"), arg.TermAs[Real]("&q"), d)))
					ratio := arg.Have(
						"the scaled height is positive",
						"&0 < &h / &(q - 1)",
						ByArith(signs))
					positive := arg.Have(
						"so the tail value is positive",
						"&0 < &h * (&q ^ d - &1) / &(q - 1)",
						ByArith(ratio, power, signs))
					arg.Show(
						"a positive tail value is not zero, and qᵈ exceeds one",
						ByArith(positive, power))
				})

			return ctx.Theorem(headline, func(
				arg *Argument,
				q, g, h, d *Expr[Nat],
				a *Arrow[Int, Real],
				larger, heightPositive, periodPositive, sparse, eventually Fact,
			) {
				N, tail := arg.UnpackAs[Nat](eventually, "N")
				realRing := arg.TermAs[module_record.RingOps[Real]]("real_ring")
				B, Bdef := arg.LetAs[Fun[Nat, Real]]("B", "λj:num. a(int_of_num(d * j))")
				C, Cdef := arg.LetAs[Real]("C", "&h * (&q ^ d - &1) / &(q - 1)")
				ratio := arg.TermAs[Real]("&q ^ d")
				linear, ratioFactor :=
					arg.TermAs[Fun[Nat, Real]]("«1−T»"),
					arg.TermAs[Fun[Nat, Real]]("basis_vector(0) - &q ^ d • basis_vector(1)")
				expanded := arg.Have(
					"A is B with Tᵈ substituted for T",
					"«coefficients»(a) = series_substitute(real_ring, B, d)",
					Derive(func(arg *Argument) {
						arg.Do(Funext())
						n := arg.FixAs[Nat]("n")
						arg.Cases(arg.TermAs[Bool]("∃j:num. d * j = n"))
						arg.When(
							"at a multiple d·j both are A(d·j)",
							func(arg *Argument, multiple Fact) {
								j, index := arg.UnpackAs[Nat](multiple, "j")
								arg.Show(
									"substitution puts B(j), which is A(d·j), at the index d·j",
									Simp(Rev(index)),
									By(
										Normalized,
										periodPositive,
										Bdef,
										formal_series.SeriesSubstituteAtMultiple.At(realRing, B, d, j)))
							})
						arg.Otherwise(
							"off the multiples of d both vanish",
							func(arg *Argument, absent Fact) {
								arg.Show(
									"n is no multiple of d, where A is zero, and the substituted series is zero there",
									By(
										absent,
										sparse.At(n),
										nat_divides.DividesFactor.At(d, n),
										formal_series.SeriesSubstituteOffMultiples.At(realRing, B, d, n)))
							})
					}))
				constant := arg.Have(
					"from suc(N) on, (1 − qᵈT)·B is the constant C",
					"∀j:num. suc(N) ≤ j ⇒ polynomial_mul(basis_vector(0) - &q ^ d • basis_vector(1), B, j) = C",
					Bdef.Rw(),
					Cdef.Rw(),
					By(larger, periodPositive, tail, At(tailCoefficient, q, g, h, d, N, a)))
				values := arg.Have(
					"C is not zero and qᵈ is not one",
					"C ≠ &0 ∧ &q ^ d ≠ &1",
					Cdef.Rw(),
					By(larger, heightPositive, periodPositive, At(nonzeroValues, q, h, d)))
				compressedPole := arg.Have(
					"so (1 − T)(1 − qᵈT)·B is a polynomial and B has a simple pole at one",
					"polynomial_over(𝕌, "+
						"    polynomial_mul(polynomial_mul(«1−T», basis_vector(0) - &q ^ d • basis_vector(1)), B)) ∧ "+
						"series_simple_pole_one(B)",
					By(values, constant, At(simplePoleCore, ratio, C, B, arg.TermAs[Nat]("suc(N)"))))
				substitutedFactors := arg.Have(
					"substituting Tᵈ takes 1 − T to 1 − Tᵈ, and 1 − qᵈT to 1 − qᵈTᵈ",
					"series_substitute(real_ring, «1−T», d) = «1−Tᵈ»(d) ∧ "+
						"series_substitute(real_ring, basis_vector(0) - &q ^ d • basis_vector(1), d) = «1−qᵈTᵈ»(q, d)",
					By(
						periodPositive,
						set_basic.InUniv.Inst[Real](),
						formal_series.SeriesSubstituteLinearFactor.Read(ring).At(d),
						formal_series.SeriesSubstituteBinomial.Read(ring).AsFact().At(ratio, d)))
				clearedB := arg.TermAs[Fun[Nat, Real]](
					"polynomial_mul(polynomial_mul(«1−T», basis_vector(0) - &q ^ d • basis_vector(1)), B)")
				cleared := arg.Have(
					"substitution is multiplicative, so it carries (1 − T)(1 − qᵈT)·B to (1 − Tᵈ)(1 − qᵈTᵈ)·A",
					"polynomial_mul(polynomial_mul(«1−Tᵈ»(d), «1−qᵈTᵈ»(q, d)), «coefficients»(a)) = "+
						"series_substitute(real_ring, "+
						"    polynomial_mul(polynomial_mul(«1−T», basis_vector(0) - &q ^ d • basis_vector(1)), B), "+
						"    d)",
					By(
						periodPositive,
						expanded,
						substitutedFactors,
						set_basic.InUniv.Inst[Real](),
						formal_series.SeriesSubstituteMul.Read(ring).At(
							arg.TermAs[Fun[Nat, Real]]("polynomial_mul(«1−T», basis_vector(0) - &q ^ d • basis_vector(1))"),
							B,
							d),
						formal_series.SeriesSubstituteMul.Read(ring).At(linear, ratioFactor, d)))
				arg.Show(
					"the cleared series is a polynomial, and A has a simple pole at one",
					SplitConj(
						Case(
							"substituting Tᵈ into a polynomial gives a polynomial",
							By(
								periodPositive,
								cleared,
								compressedPole,
								formal_series.SeriesSubstitutePolynomial.Read(ring).At(clearedB, d))),
						Case(
							"and keeps the simple pole at one",
							By(periodPositive, expanded, compressedPole, SimplePoleSubstitute.At(B, d)))))
			})
		}),
})}

// RiemannRochNumerator — for a sequence on the integers that vanishes below
// zero, starts at one and follows the Riemann–Roch tail beyond 2g − 2, the
// numerator (1 − T)(1 − qT)·a vanishes beyond degree 2g, has constant
// coefficient one and takes the value h at one. The numerator is 1 − T times
// the first difference (1 − qT)·a, which is a(n) − q·a(n − 1) by zero
// extension and the constant h from 2g on, where the tail holds at n and at
// n − 1; so the numerator vanishes from 2g + 1 on and takes the value h at one
// (EventuallyConstantDifference), and zero extension makes its constant
// coefficient a(0).
var RiemannRochNumerator = riemannRochNumeratorThm{family.Add(registry.ProofEntry{
	Name: "RiemannRochNumerator",
	Key:  "prop_14ab52024bb70571",
	Build: family.Sections(Statement{
		Binders: "∀q g h:num. ∀a:(int → real).",
		Hypotheses: []string{
			"1 < q",
			"a(0) = &1",
			"∀n:int. n < 0 ⇒ a(n) = &0",
			"∀n:int. int_of_num(2 * g) - 2 < n ⇒ &(q - 1) * a(n) = &h * (real_zpow(&q, n + 1 - g) - &1)",
		},
		Conclusion: "(∀n:num. 2 * g < n ⇒ zeta_numerator_coefficient(q, a, n) = &0) ∧ " +
			"polynomial_mul(polynomial_mul(«1−T», «1−qT»(q)), «coefficients»(a)) = " +
			"zeta_numerator_coefficient(q, a) ∧ " +
			"zeta_numerator_coefficient(q, a, 0) = &1 ∧ " +
			"polynomial_eval(zeta_numerator_coefficient(q, a), &1) = &h",
		Abbrev: Abbrev{
			{Name: "1−qT", Text: "λq:num. basis_vector(0) - &q • basis_vector(1)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		shift := ctx.Lemma("∀z:int. "+
			"    z + 1 - 1 = z ∧ z + 1 - 2 = z - 1 ∧ z - 1 - 1 = z - 2", func(arg *Argument) {
			arg.Show(
				"an added integer unit cancels, and two predecessor steps subtract two",
				ByArith())
		})

		tailDifference := ctx.Lemma(Statement{
			Binders: "∀q g h:num. ∀a:(int → real). ∀z:int.",
			Hypotheses: []string{
				"1 < q",
				"2 * g - int_of_num(1) < z",
				"∀n:int. " +
					"    int_of_num(2 * g) - int_of_num(2) < n ⇒ " +
					"    &(q - 1) * a(n) = &h * (real_zpow(&q, n + int_of_num(1) - int_of_num(g)) - &1)",
			},
			Conclusion: "a(z) - &q * a(z - int_of_num(1)) = &h",
		}, func(
			arg *Argument,
			q, g, h *Expr[Nat],
			a *Arrow[Int, Real],
			z *Expr[Int],
			largerThanOne, cutoff, tail Fact,
		) {
			predecessor := arg.Have(
				"the natural denominator has predecessor q minus one",
				"q - 1 + 1 = q",
				ByArith(largerThanOne))
			image := arg.Have(
				"the real image of q − 1 is q less one",
				"&(q - 1) = &q - &1",
				ByArith(predecessor, real_construction.OfNumAdd.At(arg.TermAs[Nat]("q - 1"), arg.TermAs[Nat]("1"))))
			positive := arg.Have(
				"the denominator q − 1 is positive",
				"&0 < &(q - 1)",
				ByArith(
					largerThanOne,
					real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), arg.TermAs[Nat]("q - 1"))))
			base := arg.Have(
				"the base q is nonzero",
				"&q ≠ &0",
				ByArith(image, positive))
			inTail := arg.Have(
				"z and z − 1 lie in the tail",
				"2 * g - int_of_num(2) < z ∧ 2 * g - &2 < z - 1",
				ByArith(cutoff))
			exponents := arg.Have(
				"the exponent at z − 1 is z − g, and the exponent at z one more",
				"z - int_of_num(1) + 1 - g = z - g ∧ z - g + 1 = z + 1 - int_of_num(g)",
				ByArith())
			equations := arg.Have(
				"read the two tail equations through the one-step power law",
				"&(q - 1) * a(z) = &h * (real_zpow(&q, z - int_of_num(g)) * &q - &1) ∧ "+
					"&(q - 1) * a(z - int_of_num(1)) = &h * (real_zpow(&q, z - int_of_num(g)) - &1)",
				By(
					inTail,
					base,
					exponents,
					tail.At(z),
					tail.At(arg.TermAs[Int]("z - &1")),
					real_zpow.ZpowAdd.At(arg.TermAs[Real]("&q"), arg.TermAs[Int]("z - &g"), arg.TermAs[Int]("1")),
					real_zpow.ZpowOne.At(arg.TermAs[Real]("&q"))))
			parts := arg.Conjuncts(
				equations,
				"the tail value at z",
				"the preceding tail value")
			scaled := arg.Have(
				"the geometric terms cancel in the scaled difference",
				"&(q - 1) * (a(z) - &q * a(z - int_of_num(1))) = &(q - 1) * &h",
				ByArith(parts[0], Scaled(arg.TermAs[Real]("-&q"), parts[1]), Scaled(arg.TermAs[Real]("&h"), image)))
			arg.Show(
				"cancel the positive denominator",
				ByArith(scaled, positive))
		})

		linearExtended := ctx.Lemma(Statement{
			Binders:    "∀c:real. ∀a:(int → real). ∀n:num.",
			Hypotheses: []string{"∀z:int. z < 0 ⇒ a(z) = &0"},
			Conclusion: "polynomial_mul(basis_vector(0) - c • basis_vector(1), «coefficients»(a), n) = " +
				"a(n) - c * a(int_of_num(n) - int_of_num(1))",
		}, func(arg *Argument, c *Expr[Real], a *Arrow[Int, Real], n *Expr[Nat], negativeZero Fact) {
			binomial := arg.Have(
				"(1 − c·T)·a at n is a(n) less c·a(n − 1), the subtracted term present from n = 1 on",
				"polynomial_mul(basis_vector(0) - c • basis_vector(1), «coefficients»(a), n) = "+
					"a(int_of_num(n)) + COND(1 ≤ n, -(c * a(int_of_num(n - 1))), &0)",
				By(
					set_basic.InUniv.Inst[Real](),
					polynomial.BinomialConvolution.Read(real_ring.CommRingOn).AsFact().At(
						c, arg.TermAs[Nat]("1"), n, arg.TermAs[Fun[Nat, Real]]("«coefficients»(a)"))))
			arg.Do(binomial.Rw(), Unless(
				arg.Term("n = 0"),
				"zero extension supplies the missing predecessor",
				Given(func(arg *Argument, zeroIndex Fact) {
					arg.Show(
						"the predecessor coefficient is zero",
						ByArith(zeroIndex, negativeZero.At(arg.TermAs[Int]("&n - 1"))))
				})))
			nonzero := arg.Hyp("n ≠ 0")
			positiveIndex := arg.Have(
				"positive indices have a natural predecessor",
				"1 ≤ n",
				ByArith(nonzero))
			arg.Show(
				"the natural and integer predecessors agree",
				Simp(Fwd(positiveIndex), Fwd(int_embed.OfNumSub)),
				ByArith())
		})

		return ctx.Theorem(headline, func(
			arg *Argument,
			q, g, h *Expr[Nat],
			a *Arrow[Int, Real],
			largerThanOne, initialOne, negativeZero, tail Fact,
		) {
			firstDifference := arg.TermAs[Fun[Nat, Real]]("polynomial_mul(«1−qT»(q), «coefficients»(a))")
			constantTail := arg.Have(
				"from 2g on, the first difference (1 − qT)·A is the constant h",
				"∀i:num. 2 * g ≤ i ⇒ polynomial_mul(«1−qT»(q), «coefficients»(a), i) = &h",
				Derive(func(arg *Argument) {
					i := arg.FixAs[Nat]("i")
					reached := arg.Assume()
					inTail := arg.Have(
						"i lies beyond 2g − 1",
						"2 * g - &1 < int_of_num(i)",
						ByArith(reached, int_embed.OfNumLe.At(arg.TermAs[Nat]("2 * g"), i)))
					arg.Show(
						"where A(i) − q·A(i − 1) is h",
						By(
							negativeZero,
							largerThanOne,
							tail,
							inTail,
							At(linearExtended, arg.TermAs[Real]("&q"), a, i),
							At(tailDifference, q, g, h, a, arg.TermAs[Int]("i"))))
				}))
			numerator := arg.Have(
				"1 − T times the first difference is the numerator",
				"polynomial_mul(«1−T», polynomial_mul(«1−qT»(q), «coefficients»(a))) = "+
					"zeta_numerator_coefficient(q, a)",
				Derive(func(arg *Argument) {
					inner := arg.Have(
						"the q-factor gives the first difference",
						"polynomial_mul(«1−qT»(q), «coefficients»(a)) = "+
							"λi:num. a(i) - &q * a(int_of_num(i) - int_of_num(1))",
						By(negativeZero, At(linearExtended, arg.TermAs[Real]("&q"), a)))
					differenceZero := arg.Have(
						"the first difference also vanishes at negative indices",
						"∀z:int. z < int_of_num(0) ⇒ a(z) - &q * a(z - int_of_num(1)) = &0",
						Derive(func(arg *Argument) {
							z := arg.FixAs[Int]("z")
							negative := arg.Assume()
							previous := arg.Have(
								"the preceding index remains negative",
								"z - int_of_num(1) < 0",
								ByArith(negative))
							arg.Show(
								"both coefficients vanish",
								ByArith(negative, previous, negativeZero.At(z), negativeZero.At(arg.TermAs[Int]("z - &1"))))
						}))
					arg.Do(inner.Rw(), Funext())
					n := arg.FixAs[Nat]("n")
					arg.Do(Simp(Fwd(ZetaNumeratorCoefficientDef), Fwd(real_construction.OfNumAdd)))
					outer := arg.Have(
						"the remaining factor subtracts adjacent first differences",
						"polynomial_mul(«1−T», λi:num. a(i) - &q * a(int_of_num(i) - int_of_num(1)), n) = "+
							"a(n) - "+
							"&q * a(int_of_num(n) - int_of_num(1)) - "+
							"(a(int_of_num(n) - int_of_num(1)) - &q * a(int_of_num(n) - int_of_num(1) - int_of_num(1)))",
						ByArith(
							differenceZero,
							vec_space.SmulOne.Read(real_ring.CommRing).At(arg.TermAs[Fun[Nat, Real]]("basis_vector(1)")),
							At(
								linearExtended,
								arg.TermAs[Real]("&1"),
								arg.TermAs[Fun[Int, Real]]("λz:int. a(z) - &q * a(z - int_of_num(1))"),
								n)))
					arg.Show(
						"collect the three coefficients",
						Simp(Fwd(outer), Fwd(shift)),
						ByArith())
				}))
			cleared := arg.Have(
				"so the numerator vanishes from 2g + 1 on and takes the value h at one",
				"vec⟨suc(2 * g)⟩(zeta_numerator_coefficient(q, a)) ∧ "+
					"polynomial_eval(zeta_numerator_coefficient(q, a), &1) = &h",
				By(
					constantTail,
					numerator,
					EventuallyConstantDifference.At(firstDifference, arg.TermAs[Real]("&h"), arg.TermAs[Nat]("2 * g"))))
			parts := arg.Conjuncts(
				cleared,
				"the numerator vanishes from 2g + 1 on",
				"and takes the value h at one")
			vanishing := arg.Unfolded(parts[0], vec_space.VecDef)
			arg.Show(
				"the four numerator properties",
				SplitConjAll(
					Case(
						"coefficients above twice the genus vanish",
						Derive(func(arg *Argument) {
							n := arg.FixAs[Nat]("n")
							beyond := arg.Assume()
							arg.Show(
								"n is at least 2g + 1, where the numerator vanishes",
								ByArith(beyond, vanishing.At(n)))
						})),
					Case(
						"the two linear factors, associated, give the numerator",
						By(
							numerator,
							set_basic.InUniv.Inst[Real](),
							polynomial.PolynomialMulAssoc.Read(real_ring.CommRingOn).At(
								arg.TermAs[Fun[Nat, Real]]("«1−T»"),
								arg.TermAs[Fun[Nat, Real]]("«1−qT»(q)"),
								arg.TermAs[Fun[Nat, Real]]("«coefficients»(a)")))),
					Case(
						"zero extension preserves the constant coefficient",
						Simp(Fwd(ZetaNumeratorCoefficientDef)),
						ByArith(
							initialOne,
							negativeZero.At(arg.TermAs[Int]("0 - &1")),
							negativeZero.At(arg.TermAs[Int]("0 - &2")))),
					Case(
						"the numerator takes the value h at one",
						By(parts[1]))))
		})
	}),
})}

// RiemannRochReciprocity — under the functional equation of the zeta tail,
// the numerator coefficients pair across twice the genus, the one at n being
// q^(n−g) times the one at 2g − n: the functional equation at n, n − 1 and
// n − 2, weighted 1, −(q + 1) and q, cancels the constant and the geometric
// terms and leaves q − 1 times the difference of the two sides, which is
// therefore zero; multiplying by q^g turns q^(n−g) into q^n.
var RiemannRochReciprocity = riemannRochReciprocityThm{family.Add(registry.ProofEntry{
	Name: "RiemannRochReciprocity",
	Key:  "prop_b15b0015a80be69f",
	Build: family.Sections(Statement{
		Binders: "∀q g h:num. ∀a:(int → real). ∀n:num.",
		Hypotheses: []string{
			"1 < q",
			"∀z:int. " +
				"    &(q - 1) * " +
				"    (a(z) - " +
				"        real_zpow(&q, z + int_of_num(1) - int_of_num(g)) * " +
				"        a(int_of_num(2 * g) - int_of_num(2) - z)) = " +
				"    &h * (real_zpow(&q, z + int_of_num(1) - int_of_num(g)) - &1)",
			"n ≤ 2 * g",
		},
		Conclusion: "&q ^ g * zeta_numerator_coefficient(q, a, n) = " +
			"&q ^ n * zeta_numerator_coefficient(q, a, 2 * g - n)",
		Abbrev: Abbrev{
			{Name: "qⁿ⁻ᵍ", Text: "real_zpow(&q, int_of_num(n) - int_of_num(g))"},
			{Name: "2g−n", Text: "int_of_num(2 * g - n)"},
			{Name: "qⁿ⁻¹⁻ᵍ", Text: "real_zpow(&q, int_of_num(n) - int_of_num(1) - int_of_num(g))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		powerScale := ctx.Lemma(Statement{
			Binders:    "∀q:real. ∀n g:num.",
			Hypotheses: []string{"q ≠ &0"},
			Conclusion: "q ^ g * real_zpow(q, &n - g) = q ^ n",
		}, func(arg *Argument, q *Expr[Real], n, g *Expr[Nat], nonzero Fact) {
			exponentSum := arg.Have(
				"the genus power restores the natural exponent",
				"g + (n - int_of_num(g)) = int_of_num(n)",
				ByArith())
			arg.Show(
				"add the integer exponents and read the natural powers",
				By(
					nonzero,
					exponentSum,
					real_zpow.ZpowAdd.At(q, arg.TermAs[Int]("g"), arg.TermAs[Int]("&n - &g")),
					real_zpow.ZpowOfNum))
		})

		return ctx.Theorem(headline,
			func(
				arg *Argument,
				q, g, h *Expr[Nat],
				a *Arrow[Int, Real],
				n *Expr[Nat],
				largerThanOne, symmetry, degreeBound Fact,
			) {
				predecessor := arg.Have(
					"the natural denominator is a positive predecessor of q",
					"q - 1 + 1 = q ∧ 0 < q - 1",
					ByArith(largerThanOne))
				signs := arg.Have(
					"the base is nonzero and the denominator is positive",
					"&q ≠ &0 ∧ &0 < &(q - 1)",
					ByArith(
						largerThanOne,
						predecessor,
						real_construction.OfNumAdd.At(arg.TermAs[Nat]("q - 1"), arg.TermAs[Nat]("1")),
						real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), arg.TermAs[Nat]("q - 1"))))
				coefficients := arg.Have(
					"the unscaled coefficients differ by the factor q^(n−g)",
					"zeta_numerator_coefficient(q, a, n) = «qⁿ⁻ᵍ» * zeta_numerator_coefficient(q, a, 2 * g - n)",
					Derive(func(arg *Argument) {
						reflection := arg.Have(
							"the reflected natural index agrees with integer subtraction",
							"«2g−n» = int_of_num(2 * g) - int_of_num(n)",
							By(degreeBound, int_embed.OfNumSub.At(n, arg.TermAs[Nat]("2 * g"))))
						reflected := arg.Have(
							"reflection carries n, n − 1 and n − 2 to 2g − n − 2, 2g − n − 1 and 2g − n",
							"int_of_num(2 * g) - int_of_num(2) - int_of_num(n) = «2g−n» - int_of_num(2) ∧ "+
								"int_of_num(2 * g) - int_of_num(2) - (int_of_num(n) - int_of_num(1)) = «2g−n» - int_of_num(1) ∧ "+
								"int_of_num(2 * g) - int_of_num(2) - (int_of_num(n) - int_of_num(2)) = «2g−n»",
							ByArith(reflection))
						followingExponent := arg.Have(
							"the exponent at n is one more than n − g",
							"n + &1 - g = int_of_num(n) - int_of_num(g) + 1",
							ByArith())
						following := arg.Have(
							"the geometric factor at n is q^(n−g) times q",
							"real_zpow(&q, int_of_num(n) + int_of_num(1) - int_of_num(g)) = «qⁿ⁻ᵍ» * &q",
							By(
								signs,
								followingExponent,
								real_zpow.ZpowAdd.At(arg.TermAs[Real]("&q"), arg.TermAs[Int]("&n - &g"), arg.TermAs[Int]("1")),
								real_zpow.ZpowOne.At(arg.TermAs[Real]("&q"))))
						middleExponent := arg.Have(
							"the exponent at n − 1 is n − g",
							"n - &1 + 1 - g = int_of_num(n) - int_of_num(g)",
							ByArith())
						precedingExponent := arg.Have(
							"the exponent at n − 2 is n − 1 − g",
							"n - &2 + 1 - g = int_of_num(n) - 1 - int_of_num(g)",
							ByArith())
						equations := arg.Have(
							"read symmetry at n and its two integer predecessors",
							"&(q - 1) * (a(int_of_num(n)) - «qⁿ⁻ᵍ» * &q * a(«2g−n» - int_of_num(2))) = "+
								"&h * («qⁿ⁻ᵍ» * &q - &1) ∧ "+
								"&(q - 1) * (a(int_of_num(n) - int_of_num(1)) - «qⁿ⁻ᵍ» * a(«2g−n» - int_of_num(1))) = "+
								"&h * («qⁿ⁻ᵍ» - &1) ∧ "+
								"&(q - 1) * (a(int_of_num(n) - int_of_num(2)) - «qⁿ⁻¹⁻ᵍ» * a(«2g−n»)) = &h * («qⁿ⁻¹⁻ᵍ» - &1)",
							By(
								reflected,
								following,
								middleExponent,
								precedingExponent,
								symmetry.At(arg.TermAs[Int]("n")),
								symmetry.At(arg.TermAs[Int]("&n - 1")),
								symmetry.At(arg.TermAs[Int]("&n - 2"))))
						values := arg.Conjuncts(
							equations,
							"symmetry at n",
							"symmetry at n minus one",
							"symmetry at n minus two")
						precedingStep := arg.Have(
							"one more than n − 1 − g is n − g",
							"n - &1 - g + 1 = int_of_num(n) - int_of_num(g)",
							ByArith())
						preceding := arg.Have(
							"the geometric factor at n − 2, times q, is q^(n−g)",
							"«qⁿ⁻¹⁻ᵍ» * &q = «qⁿ⁻ᵍ»",
							By(
								signs,
								precedingStep,
								real_zpow.ZpowAdd.At(arg.TermAs[Real]("&q"), arg.TermAs[Int]("&n - 1 - &g"), arg.TermAs[Int]("1")),
								real_zpow.ZpowOne.At(arg.TermAs[Real]("&q"))))
						weightedThird := arg.Have(
							"multiply the earliest equation by q and restore the middle geometric factor",
							"&(q - 1) * (&q * a(int_of_num(n) - int_of_num(2)) - «qⁿ⁻ᵍ» * a(«2g−n»)) = &h * («qⁿ⁻ᵍ» - &q)",
							ByArith(
								Scaled(arg.TermAs[Real]("&q"), values[2]),
								Scaled(arg.TermAs[Real]("&(q - 1) * a(«2g−n») + &h"), preceding)))
						cancelled := arg.Have(
							"the weights 1, -(q+1), q cancel the constant and geometric terms",
							"&(q - 1) * "+
								"(zeta_numerator_coefficient(q, a, n) - «qⁿ⁻ᵍ» * zeta_numerator_coefficient(q, a, 2 * g - n)) = "+
								"&0",
							Simp(Fwd(ZetaNumeratorCoefficientDef), Fwd(real_construction.OfNumAdd)),
							ByArith(values[0], Scaled(arg.TermAs[Real]("-(&q + &1)"), values[1]), weightedThird))
						arg.Show(
							"cancel the positive denominator",
							ByArith(cancelled, signs))
					}))
				scale := arg.Have(
					"the genus power turns q^(n−g) into q^n",
					"&q ^ g * «qⁿ⁻ᵍ» = &q ^ n",
					By(signs, At(powerScale, arg.TermAs[Real]("&q"), n, g)))
				arg.Show(
					"multiply coefficient symmetry by the genus power",
					ByArith(
						Scaled(arg.TermAs[Real]("&q ^ g"), coefficients),
						Scaled(arg.TermAs[Real]("zeta_numerator_coefficient(q, a, 2 * g - n)"), scale)))
			})
	}),
})}
