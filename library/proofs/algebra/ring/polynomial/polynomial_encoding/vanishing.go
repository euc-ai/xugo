// vanishing.go — over an infinite domain a polynomial in finitely many variables is determined by
// its values: fixing the last variable at a value of the ring gives a polynomial in the others, a
// polynomial all of whose substitutions of a constant for one variable vanish is zero, and by
// induction on the number of variables a polynomial vanishing at every tuple is zero, so two
// polynomials taking the same values are equal.

package polynomial_encoding

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// SubstituteLastVariable — fixing the last of N + 1 variables at a value t of the ring gives a
// polynomial in the first N variables, whose value at an N-tuple x is the value of p at x with t
// put in the last place. The substitution is evaluation along the constants at the variables sent
// to t and to themselves, all of them polynomials in the first N variables, so its value is one of
// them; computed among all polynomials it is the same polynomial, the operations not reading the
// variables. Evaluation at x after it is evaluation of p along the identity at the images of the
// variables (polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural), and those images are t for the
// last variable and the coordinates of x for the others.
var SubstituteLastVariable = substituteLastVariableThm{family.Add(registry.ProofEntry{
	Name: "SubstituteLastVariable",
	Key:  "prop_da758e9aa56dad93",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀N:num. ∀t:A. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"t ∈ R.carrier",
			"p ∈ polynomial_algebra(R, {i:num | i < suc(N)})",
		},
		Conclusion: "«substituted» ∈ polynomial_algebra(R, {i:num | i < N}) ∧ " +
			"(∀x:(num → A). " +
			"    ring_tuple(R, N, x) ⇒ " +
			"    polynomial_value(R, «substituted», x) = polynomial_value(R, p, λi:num. COND(i = N, t, x(i))))",
		Abbrev: Abbrev{
			{Name: "images", Text: "λi:num. " +
				"    COND(i = N, polynomial_algebra_const(R, t), polynomial_algebra_var(R, i))"},
			{Name: "substituted", Text: "polynomial_algebra_eval(R, " +
				"    polynomial_algebra_ring(R, 𝕌), " +
				"    polynomial_algebra_const(R), " +
				"    «images», " +
				"    p)"},
			{Name: "firstN", Text: "polynomial_algebra_eval(R, " +
				"    polynomial_algebra_ring(R, {i:num | i < N}), " +
				"    polynomial_algebra_const(R), " +
				"    «images», " +
				"    p)"},
		},
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		N *Expr[Nat],
		t *Expr[A],
		p *Arrow[_Monomial, A],
		tIn, pIn Fact,
	) {
		type multivariate = Fun[_Monomial, A]
		ringR := a.TermAs[RingOps[A]]("R")
		below := a.TermAs[Set[Nat]]("{i:num | i < N}")
		belowSuc := a.TermAs[Set[Nat]]("{i:num | i < suc(N)}")
		firstN := a.TermAs[RingOps[multivariate]]("polynomial_algebra_ring(R, {i:num | i < N})")
		constant := a.TermAs[Fun[A, multivariate]]("polynomial_algebra_const(R)")
		images := a.TermAs[Fun[Nat, multivariate]]("«images»")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		constants := a.Have(
			"the constants are a ring homomorphism into the polynomials in the first N variables",
			"ring_homomorphism(R, polynomial_algebra_ring(R, {i:num | i < N}), polynomial_algebra_const(R))",
			By(R, polynomial_algebra.PolynomialAlgebraConstHom))
		imagesIn := a.Have(
			"the last variable goes to the constant t and every "+
				"other one below N + 1 to itself, all in the first N",
			"∀i:num. i < suc(N) ⇒ «images»(i) ∈ polynomial_algebra(R, {j:num | j < N})",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				inRange := b.Assume()
				b.Cases(b.Term("i = N"))
				b.When(
					"the last variable goes to the constant t",
					func(c *Argument, last Fact) {
						c.Show(
							"a constant of R is a polynomial in the first N variables",
							By(last, tIn, ring_homomorphism.MapIn.Read(constants)))
					})
				b.Otherwise(
					"a variable below N stays itself",
					func(c *Argument, other Fact) {
						lower := c.Have(
							"i is below N",
							"i < N",
							ByArith(other, inRange))
						c.Show(
							"a variable below N is a polynomial in the first N variables",
							By(R, other, lower, polynomial_algebra.PolynomialAlgebraVarIn.At(ringR, below, i)))
					})
			}))
		inFirstN := a.Have(
			"so p, its last variable fixed at t, computed among the "+
				"polynomials in the first N variables, is one of them",
			"«firstN» ∈ polynomial_algebra(R, {i:num | i < N})",
			By(
				imagesIn,
				pIn,
				constants,
				polynomial_algebra_evaluation.PolynomialAlgebraEvalIn.At(
					ringR, firstN, constant, images, belowSuc, p)))
		same := a.Have(
			"computed among all polynomials it is the same "+
				"polynomial: the operations do not read the variables",
			"«firstN» = «substituted»",
			By(
				polynomial_algebra.PolynomialAlgebraRingRestrictVariables.At(ringR, below),
				polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictTarget.At(
					ringR,
					a.TermAs[RingOps[multivariate]]("polynomial_algebra_ring(R, 𝕌)"),
					a.TermAs[Set[multivariate]]("polynomial_algebra(R, {i:num | i < N})"),
					constant,
					images,
					p)))
		values := a.Have(
			"at an N-tuple x it takes the value of p at x with t in the last place",
			Statement{
				Binders: "∀x:(num → A).",
				Hypotheses: []string{
					"ring_tuple(R, N, x)",
				},
				Conclusion: "polynomial_value(R, «substituted», x) = " +
					"polynomial_value(R, p, λi:num. COND(i = N, t, x(i)))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, A]]("x")
				tuple := b.Conjuncts(
					b.Unfolded(b.Assume(), RingTupleDef),
					"x vanishes from N on",
					"and its first N coordinates lie in R")
				coordinates := b.Have(
					"every coordinate of x lies in R: the first N by the tuple, the others are zero",
					"∀i:num. x(i) ∈ R.carrier",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						c.Cases(c.Term("i < N"))
						c.When(
							"a coordinate below N lies in R",
							func(d *Argument, lower Fact) {
								d.Show(
									"by the tuple",
									By(lower, tuple[1].At(i)))
							})
						c.Otherwise(
							"a coordinate from N on is zero, which lies in R",
							func(d *Argument, notLower Fact) {
								d.Show(
									"x vanishes there",
									By(comm_ring.ZeroIn.Read(R), notLower, tuple[0], vec_space.VecDef, nat_order.NotLessThan))
							})
					}))
				evaluation := b.Have(
					"evaluation at x is a ring homomorphism from the polynomials in the first N variables",
					"ring_homomorphism(polynomial_algebra_ring(R, {i:num | i < N}), "+
						"    R, "+
						"    polynomial_algebra_eval(R, R, λa:A. a, x))",
					By(
						ring_homomorphism.RingHomIdentity.Read(R),
						tuple[1],
						polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(ringR, ringR, identity, x, below)))
				fixed := b.Have(
					"evaluation at x sends a constant to itself",
					Statement{
						Binders: "∀c:A.",
						Hypotheses: []string{
							"c ∈ R.carrier",
						},
						Conclusion: "polynomial_algebra_eval(R, R, λa:A. a, x, polynomial_algebra_const(R, c)) = c",
					},
					b.ForEach(func(c *Expr[A]) Action {
						return By(
							ring_homomorphism.RingHomIdentity.Read(R),
							polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(ringR, ringR, identity, x, c))
					}))
				natural := b.Have(
					"evaluation at x after the substitution evaluates p at the images of the variables",
					"polynomial_algebra_eval(R, R, λa:A. a, x, «firstN») = "+
						"polynomial_algebra_eval(R, "+
						"    R, "+
						"    λa:A. a, "+
						"    λi:num. polynomial_algebra_eval(R, R, λa:A. a, x, «images»(i)), "+
						"    p)",
					By(
						ring_homomorphism.RingHomIdentity.Read(R),
						fixed,
						imagesIn,
						pIn,
						constants,
						evaluation,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural.At(
							ringR,
							firstN,
							ringR,
							constant,
							b.TermAs[Fun[multivariate, A]]("polynomial_algebra_eval(R, R, λa:A. a, x)"),
							identity,
							belowSuc,
							images,
							p)))
				imagesAtX := b.Have(
					"those images are t for the last variable and the coordinates of x for the others",
					"(λi:num. polynomial_algebra_eval(R, R, λa:A. a, x, «images»(i))) = (λi:num. COND(i = N, t, x(i)))",
					Funext(),
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						c.Cases(c.Term("i = N"))
						c.When(
							"the last variable goes to the constant t, which evaluation fixes",
							func(d *Argument, last Fact) {
								d.Show(
									"its image is t",
									By(fixed.At(t), last, tIn))
							})
						c.Otherwise(
							"another variable goes to itself, which evaluation reads at x",
							func(d *Argument, other Fact) {
								d.Show(
									"its image is the coordinate of x",
									By(
										ring_homomorphism.RingHomIdentity.Read(R),
										other,
										coordinates.At(i),
										polynomial_algebra_evaluation.PolynomialAlgebraEvalVar.At(ringR, ringR, identity, x, i)))
							})
					}))
				b.Show(
					"so the substituted polynomial takes at x the value of p at x with t in the last place",
					By(natural, imagesAtX, same, PolynomialValueDef))
			}))
		a.Show(
			"the substituted polynomial lies in the first N variables "+
				"and takes the values of p with t in the last place",
			By(inFirstN, same, values))
	}),
})}

// ZeroAfterEverySubstitution — a polynomial over an infinite domain that vanishes whenever one of
// its variables y is fixed at a value of the domain is zero. Read p as a polynomial in a new
// variable X over the polynomials, y going to X and every other variable to its constant: this
// expansion is a ring homomorphism into the polynomials over the polynomials, and evaluated at a
// polynomial s it is p with s put for y (polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural). At
// the constant of a t in R that is zero by hypothesis, so the constants, as many as the elements of
// R and so infinitely many, are roots of the expansion; over the domain of polynomials a nonzero
// polynomial has finitely many roots (polynomial_roots.RootBound), so the expansion is zero. At the
// variable y it gives p back, since putting y for y fixes the constants and the variables
// (polynomial_algebra_evaluation.PolynomialAlgebraEvalUnique); so p is the value of zero, zero.
var ZeroAfterEverySubstitution = zeroAfterEverySubstitutionThm{family.Add(registry.ProofEntry{
	Name: "ZeroAfterEverySubstitution",
	Key:  "prop_77c7d8e74f3d5e1e",
	Reading: "The infinite carrier is load-bearing: over a field with q elements " +
		"the polynomial y^q − y in the one variable y vanishes at every value of y " +
		"and is not zero. p may involve any variables besides y; only y is fixed.",
	Build: family.Theorem(Statement{
		Binders: "∀R:integral_domain_on(A). ∀y:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"infinite(R.carrier)",
			"p ∈ polynomial_algebra(R, 𝕌)",
			"∀t:A. " +
				"    t ∈ R.carrier ⇒ «substitution»(polynomial_algebra_const(R, t), p) = (λm:(num → num). R.zero)",
		},
		Conclusion: "p = (λm:(num → num). R.zero)",
		Abbrev: Abbrev{
			{Name: "substitution", Text: "λs:((num → num) → A). λf:((num → num) → A). " +
				"    polynomial_algebra_eval(R, " +
				"        polynomial_algebra_ring(R, 𝕌), " +
				"        polynomial_algebra_const(R), " +
				"        λi:num. COND(i = y, s, polynomial_algebra_var(R, i)), " +
				"        f)"},
			{Name: "constant", Text: "λf:((num → num) → A). " +
				"    vec_scalar_mul(polynomial_algebra_mul(R), " +
				"        f, " +
				"        basis_vector(fun_zero(R.zero), polynomial_algebra_one(R), 0))"},
			{Name: "X", Text: "basis_vector(fun_zero(R.zero), polynomial_algebra_one⟨D:num⟩(R), 1)"},
			{Name: "image", Text: "λi:num. COND(i = y, «X», «constant»(polynomial_algebra_var(R, i)))"},
			{Name: "expansion", Text: "polynomial_algebra_eval(R, " +
				"    polynomial_ring(polynomial_algebra_ring(R, 𝕌⟨A:num⟩)), " +
				"    λa:A. «constant»(polynomial_algebra_const(R, a)), " +
				"    «image»)"},
			{Name: "valueAt", Text: "λq:(num → (num → num) → A). λs:((num → num) → A). " +
				"    polynomial_eval(fun_add(R.add), " +
				"        fun_zero(R.zero), " +
				"        polynomial_algebra_mul(R), " +
				"        polynomial_algebra_one(R), " +
				"        q, " +
				"        s)"},
			{Name: "roots", Text: "polynomial_roots(fun_add(R.add), " +
				"    fun_zero(R.zero), " +
				"    polynomial_algebra_mul(R), " +
				"    polynomial_algebra_one(R), " +
				"    polynomial_algebra(R, 𝕌⟨A:num⟩), " +
				"    «expansion»(p))"},
		},
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		y *Expr[Nat],
		p *Arrow[_Monomial, A],
		infinite, pIn, vanishes Fact,
	) {
		type multivariate = Fun[_Monomial, A]
		type overPolynomials = Fun[Nat, multivariate]
		ringR := a.TermAs[RingOps[A]]("R")
		variablesAll := a.TermAs[Set[Nat]]("𝕌")
		polynomials := a.TermAs[RingOps[multivariate]]("polynomial_algebra_ring(R, 𝕌)")
		overRing := a.TermAs[RingOps[overPolynomials]]("polynomial_ring(polynomial_algebra_ring(R, 𝕌))")
		constant := a.TermAs[Fun[A, multivariate]]("polynomial_algebra_const(R)")
		coefficients := a.TermAs[Fun[A, overPolynomials]](
			"λa:A. «constant»(polynomial_algebra_const(R, a))")
		image := a.TermAs[Fun[Nat, overPolynomials]]("«image»")
		variableY := a.TermAs[multivariate]("polynomial_algebra_var(R, y)")
		ring := integral_domain.Ring.Read(R)
		domain := a.Have(
			"the polynomials over the domain R are a domain",
			"integral_domain_on(polynomial_algebra_ring(R, 𝕌⟨A:num⟩))",
			By(polynomial_algebra.PolynomialAlgebraDomain.Read(R).At(variablesAll)))
		polynomialRing := integral_domain.Ring.Read(domain)
		variables := a.Have(
			"every variable is a polynomial",
			"∀i:num. polynomial_algebra_var(R, i) ∈ polynomial_algebra(R, 𝕌⟨A:num⟩)",
			By(ring, polynomial_algebra.PolynomialAlgebraVarIn, set_basic.InUniv))
		constants := a.Have(
			"the constants are a ring homomorphism from R into the polynomials",
			"ring_homomorphism(R, polynomial_algebra_ring(R, 𝕌⟨A:num⟩), polynomial_algebra_const(R))",
			By(ring, polynomial_algebra.PolynomialAlgebraConstHom))
		constantsOver := a.Have(
			"so are their constants among the polynomials over the polynomials",
			"ring_homomorphism(R, "+
				"    polynomial_ring(polynomial_algebra_ring(R, 𝕌⟨A:num⟩)), "+
				"    λa:A. «constant»(polynomial_algebra_const(R, a)))",
			By(
				constants,
				polynomial.ConstantPolynomialHomomorphism.Read(polynomialRing),
				ring_homomorphism.RingHomCompose.At(
					ringR,
					polynomials,
					overRing,
					constant,
					a.TermAs[Fun[multivariate, overPolynomials]]("«constant»"))))
		imagesOver := a.Have(
			"y goes to X and every other variable to its "+
				"constant, all of them polynomials over the polynomials",
			"∀i:num. polynomial_over(fun_zero(R.zero), polynomial_algebra(R, 𝕌⟨A:num⟩), «image»(i))",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Cases(b.Term("i = y"))
				b.When(
					"y goes to X",
					func(c *Argument, isY Fact) {
						c.Show(
							"X is a polynomial over the polynomials",
							By(isY, polynomial.BasisVectorOver.Read(polynomialRing).At(c.TermAs[Nat]("1"))))
					})
				b.Otherwise(
					"another variable goes to its constant",
					func(c *Argument, other Fact) {
						c.Show(
							"the constant of a polynomial is a polynomial over the polynomials",
							By(
								other,
								variables.At(i),
								ring_homomorphism.MapIn.Read(polynomial.ConstantPolynomialHomomorphism.Read(polynomialRing))))
					})
			}))
		expansionHom := a.Have(
			"so the expansion, y going to X, is a ring homomorphism into the polynomials over the polynomials",
			"ring_homomorphism(polynomial_algebra_ring(R, 𝕌⟨A:num⟩), "+
				"    polynomial_ring(polynomial_algebra_ring(R, 𝕌⟨A:num⟩)), "+
				"    «expansion»)",
			By(
				imagesOver,
				constantsOver,
				polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(
					ringR, overRing, coefficients, image, variablesAll)))
		expansionOver := a.Have(
			"the expansion of p is a polynomial over the polynomials",
			"polynomial_over(fun_zero(R.zero), polynomial_algebra(R, 𝕌⟨A:num⟩), «expansion»(p))",
			By(pIn, ring_homomorphism.MapIn.Read(expansionHom)))
		atPoint := a.Have(
			"evaluated at a polynomial s, the expansion of p is p with s put for y",
			Statement{
				Binders: "∀s:((num → num) → A).",
				Hypotheses: []string{
					"s ∈ polynomial_algebra(R, 𝕌⟨A:num⟩)",
				},
				Conclusion: "«valueAt»(«expansion»(p), s) = «substitution»(s, p)",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[multivariate]("s")
				sIn := b.Assume()
				evaluation := b.Have(
					"evaluation at s is a ring homomorphism from the polynomials over the polynomials",
					"ring_homomorphism(polynomial_ring(polynomial_algebra_ring(R, 𝕌⟨A:num⟩)), "+
						"    polynomial_algebra_ring(R, 𝕌⟨A:num⟩), "+
						"    λq:(num → (num → num) → A). «valueAt»(q, s))",
					By(sIn, polynomial_evaluation.EvalHomomorphism.Read(polynomialRing).AsFact().At(s)))
				fixed := b.Have(
					"it sends the constant of the constant of c back to the constant of c",
					Statement{
						Binders: "∀c:A.",
						Hypotheses: []string{
							"c ∈ R.carrier",
						},
						Conclusion: "«valueAt»(«constant»(polynomial_algebra_const(R, c)), s) = " +
							"polynomial_algebra_const(R, c)",
					},
					Derive(func(c *Argument) {
						k := c.FixAs[A]("c")
						kIn := c.Assume()
						c.Show(
							"the constant of c is a polynomial, and evaluation keeps constants",
							By(
								sIn,
								kIn,
								ring_homomorphism.MapIn.Read(constants).AsFact().At(k),
								polynomial_evaluation.EvalConstant.Read(polynomialRing).AsFact().At(
									c.TermAs[multivariate]("polynomial_algebra_const(R, c)"), s)))
					}))
				natural := b.Have(
					"evaluation at s after the expansion evaluates p at the images of the variables",
					"«valueAt»(«expansion»(p), s) = "+
						"polynomial_algebra_eval(R, "+
						"    polynomial_algebra_ring(R, 𝕌⟨A:num⟩), "+
						"    polynomial_algebra_const(R), "+
						"    λi:num. «valueAt»(«image»(i), s), "+
						"    p)",
					By(
						ring,
						fixed,
						imagesOver,
						pIn,
						constantsOver,
						evaluation,
						constants,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural.At(
							ringR,
							overRing,
							polynomials,
							coefficients,
							b.TermAs[Fun[overPolynomials, multivariate]]("λq:(num → (num → num) → A). «valueAt»(q, s)"),
							constant,
							variablesAll,
							image,
							p)))
				imagesAtS := b.Have(
					"evaluation at s sends X to s and the constant of every other variable to that variable",
					"∀i:num. «valueAt»(«image»(i), s) = COND(i = y, s, polynomial_algebra_var(R, i))",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						c.Cases(c.Term("i = y"))
						c.When(
							"X goes to s",
							func(d *Argument, isY Fact) {
								d.Show(
									"the value of X at s is s to the first power, which is s",
									By(
										isY,
										sIn,
										polynomial_evaluation.EvalBasisVector.Read(polynomialRing).AsFact().At(d.TermAs[Nat]("1"), s),
										comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(polynomialRing)).AsFact().At(s)))
							})
						c.Otherwise(
							"the constant of another variable goes to that variable",
							func(d *Argument, other Fact) {
								d.Show(
									"evaluation keeps constants",
									By(
										other,
										sIn,
										variables.At(i),
										polynomial_evaluation.EvalConstant.Read(polynomialRing).AsFact().At(
											d.TermAs[multivariate]("polynomial_algebra_var(R, i)"), s)))
							})
					}))
				b.Show(
					"so the value at s is p with s put for y",
					By(natural, imagesAtS))
			}))
		roots := a.Have(
			"every constant of R is a root of the expansion of p: p with it put for y vanishes",
			"∀t:A. t ∈ R.carrier ⇒ polynomial_algebra_const(R, t) ∈ «roots»",
			Derive(func(b *Argument) {
				t := b.FixAs[A]("t")
				tIn := b.Assume()
				constantIn := b.Have(
					"the constant t is a polynomial",
					"polynomial_algebra_const(R, t) ∈ polynomial_algebra(R, 𝕌⟨A:num⟩)",
					By(tIn, ring_homomorphism.MapIn.Read(constants).AsFact().At(t)))
				vanishesAtT := b.Have(
					"the expansion of p vanishes at the constant t",
					"«valueAt»(«expansion»(p), polynomial_algebra_const(R, t)) = (λm:(num → num). R.zero)",
					By(
						tIn,
						constantIn,
						vanishes.At(t),
						atPoint.At(b.TermAs[multivariate]("polynomial_algebra_const(R, t)"))))
				b.Show(
					"so the constant t is a root",
					BySets(
						constantIn,
						vanishesAtT,
						polynomial_roots.PolynomialRootsDef.At(
							b.TermAs[Op[multivariate]]("fun_add(R.add)"),
							b.TermAs[multivariate]("fun_zero(R.zero)"),
							b.TermAs[Op[multivariate]]("polynomial_algebra_mul(R)"),
							b.TermAs[multivariate]("polynomial_algebra_one(R)"),
							b.TermAs[Set[multivariate]]("polynomial_algebra(R, 𝕌)"),
							b.TermAs[overPolynomials]("«expansion»(p)")),
						function_module.FunZeroDef))
			}))
		injective := a.Have(
			"distinct elements of R have distinct constants",
			"injective_on(R.carrier, polynomial_algebra_const⟨D:num⟩(R))",
			By(functions.InjectiveOnDef, polynomial_algebra.PolynomialAlgebraConstDef, free_module.DeltaAtDef))
		amongRoots := a.Have(
			"so the constants of R lie among the roots",
			"image(polynomial_algebra_const⟨D:num⟩(R), R.carrier) ⊆ «roots»",
			BySets(roots))
		expansionZero := a.Have(
			"the constants are infinitely many and a nonzero polynomial over a domain has finitely many roots",
			"«expansion»(p) = vec_zero(fun_zero(R.zero))",
			By(
				infinite,
				injective,
				amongRoots,
				expansionOver,
				finite_set.InfiniteImage.At(constant, a.TermAs[Set[A]]("R.carrier")),
				polynomial_roots.RootBound.Read(domain).AsFact().At(a.TermAs[overPolynomials]("«expansion»(p)")),
				finite_set.FiniteSubset,
				finite_set.InfiniteDef.At(
					a.TermAs[Set[multivariate]]("image(polynomial_algebra_const(R), R.carrier)"))))
		selfValue := a.Have(
			"putting the variable y for y gives p back",
			"«substitution»(polynomial_algebra_var(R, y), p) = p",
			Derive(func(b *Argument) {
				renaming := b.Have(
					"putting y for y is a ring homomorphism of the polynomials",
					"ring_homomorphism(polynomial_algebra_ring(R, 𝕌⟨A:num⟩), "+
						"    polynomial_algebra_ring(R, 𝕌⟨A:num⟩), "+
						"    «substitution»(polynomial_algebra_var(R, y)))",
					By(
						variables,
						constants,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(
							ringR,
							polynomials,
							constant,
							b.TermAs[Fun[Nat, multivariate]](
								"λi:num. COND(i = y, polynomial_algebra_var(R, y), polynomial_algebra_var(R, i))"),
							variablesAll)))
				onConstants := b.Have(
					"it fixes the constants",
					Statement{
						Binders: "∀c:A.",
						Hypotheses: []string{
							"c ∈ R.carrier",
						},
						Conclusion: "«substitution»(polynomial_algebra_var(R, y), polynomial_algebra_const(R, c)) = " +
							"polynomial_algebra_const(R, c)",
					},
					By(constants, polynomial_algebra_evaluation.PolynomialAlgebraEvalConst))
				onVariables := b.Have(
					"and the variables, y included",
					"∀i:num. "+
						"    «substitution»(polynomial_algebra_var(R, y), polynomial_algebra_var(R, i)) = "+
						"    polynomial_algebra_var(R, i)",
					By(variables, constants, polynomial_algebra_evaluation.PolynomialAlgebraEvalVar))
				b.Show(
					"so it agrees with the identity on the polynomials, p among them",
					By(
						ring,
						onConstants,
						onVariables,
						pIn,
						renaming,
						ring_homomorphism.RingHomIdentity.Read(polynomialRing),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalUnique.At(
							ringR,
							polynomials,
							variablesAll,
							b.TermAs[Fun[multivariate, multivariate]]("«substitution»(polynomial_algebra_var(R, y))"),
							b.TermAs[Fun[multivariate, multivariate]]("λf:((num → num) → A). f"),
							p)))
			}))
		a.Show(
			"so p is the value of the zero expansion at y, which is zero",
			By(
				selfValue,
				atPoint.At(variableY),
				variables.At(y),
				expansionZero,
				polynomial_evaluation.EvalVecZero.Read(polynomialRing).AsFact().At(variableY),
				function_module.FunZeroDef))
	}),
})}

// PolynomialVanishingIsZero — a polynomial in finitely many variables over an infinite integral
// domain that vanishes at every point is the zero polynomial. By induction on the number N of
// variables, p general in the hypothesis of induction. In no variables p is the constant of its
// value at the zero tuple: evaluating there and taking the constant is a ring homomorphism of the
// polynomials in no variables that fixes the constants, so it is the identity
// (polynomial_algebra_evaluation.PolynomialAlgebraEvalUnique), and that value is zero. In N + 1 variables,
// fixing the last one at any t of R gives a polynomial in the first N whose value at an N-tuple is
// the value of p with t put last (SubstituteLastVariable), zero; by the hypothesis of induction it
// is zero, and a polynomial all of whose substitutions of a constant for one variable vanish is
// zero (ZeroAfterEverySubstitution).
var PolynomialVanishingIsZero = polynomialVanishingIsZeroThm{family.Add(registry.ProofEntry{
	Name: "PolynomialVanishingIsZero",
	Key:  "prop_ca5a44febd17d691",
	Reading: "The infinite carrier is load-bearing: over a field with q elements, x^q − x in " +
		"one variable vanishes at every point and is not zero. The points are the ring tuples of " +
		"length N, zero from N on, so at N = 0 the one point is the zero tuple and p is a constant.",
	Build: family.Theorem(Statement{
		Binders: "∀R:integral_domain_on(A). ∀N:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"infinite(R.carrier)",
			"p ∈ polynomial_algebra(R, {i:num | i < N})",
			"∀x:(num → A). ring_tuple(R, N, x) ⇒ polynomial_value(R, p, x) = R.zero",
		},
		Conclusion: "p = (λm:(num → num). R.zero)",
		Abbrev: Abbrev{
			{Name: "substitution", Text: "λs:((num → num) → A). λf:((num → num) → A). " +
				"    polynomial_algebra_eval(R, " +
				"        polynomial_algebra_ring(R, 𝕌), " +
				"        polynomial_algebra_const(R), " +
				"        λi:num. COND(i = N, s, polynomial_algebra_var(R, i)), " +
				"        f)"},
			{Name: "atZero", Text: "polynomial_algebra_eval(R, R, λa:A. a, λi:num. R.zero)"},
		},
	}, func(a *Argument, R integral_domain.IntegralDomainFact[on.R]) {
		type multivariate = Fun[_Monomial, A]
		ringR := a.TermAs[RingOps[A]]("R")
		identity := a.TermAs[Fun[A, A]]("λa:A. a")
		ring := integral_domain.Ring.Read(R)
		a.Induct("N")
		a.Base(
			"in no variables p is the constant of its value at the zero tuple, and that value is zero",
			func(b *Argument) {
				p := b.FixAs[multivariate]("p")
				given := b.Conjuncts(
					b.Assume(),
					"R is infinite",
					"p is a polynomial in no variables",
					"and it vanishes at the ring tuples of length 0")
				noVariables := b.TermAs[Set[Nat]]("{i:num | i < 0}")
				constantsRing := b.TermAs[RingOps[multivariate]]("polynomial_algebra_ring(R, {i:num | i < 0})")
				zeroValue := b.Have(
					"the zero tuple is a ring tuple of length 0, so p vanishes there",
					"«atZero»(p) = R.zero",
					By(
						given[2].At(b.TermAs[Fun[Nat, A]]("λi:num. R.zero")),
						RingTupleDef,
						PolynomialValueDef,
						vec_space.VecDef,
						nat_order.LessThanZeroClause))
				polynomials := b.Have(
					"the polynomials in no variables form a commutative ring",
					"comm_ring_on(polynomial_algebra_ring(R, {i:num | i < 0}))",
					By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn))
				constants := b.Have(
					"the constants are a ring homomorphism from R into them",
					"ring_homomorphism(R, polynomial_algebra_ring(R, {i:num | i < 0}), polynomial_algebra_const(R))",
					By(ring, polynomial_algebra.PolynomialAlgebraConstHom))
				evaluation := b.Have(
					"evaluation at the zero tuple is a ring homomorphism from them to R",
					"ring_homomorphism(polynomial_algebra_ring(R, {i:num | i < 0}), R, «atZero»)",
					By(
						ring_homomorphism.RingHomIdentity.Read(ring),
						comm_ring.ZeroIn.Read(ring),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(
							ringR,
							ringR,
							identity,
							b.TermAs[Fun[Nat, A]]("λi:num. R.zero"),
							noVariables)))
				fixed := b.Have(
					"it sends a constant to itself",
					"∀c:A. c ∈ R.carrier ⇒ «atZero»(polynomial_algebra_const(R, c)) = c",
					By(
						ring_homomorphism.RingHomIdentity.Read(ring),
						polynomial_algebra_evaluation.PolynomialAlgebraEvalConst))
				composite := b.Have(
					"so evaluating at the zero tuple and taking the constant "+
						"is a ring homomorphism of the polynomials in no variables",
					"ring_homomorphism(polynomial_algebra_ring(R, {i:num | i < 0}), "+
						"    polynomial_algebra_ring(R, {i:num | i < 0}), "+
						"    λf:((num → num) → A). polynomial_algebra_const(R, «atZero»(f)))",
					By(constants, evaluation, ring_homomorphism.RingHomCompose))
				constantOfValue := b.Have(
					"it fixes the constants and there are no variables, "+
						"so it is the identity: p is the constant of its value",
					"polynomial_algebra_const(R, «atZero»(p)) = p",
					By(
						ring,
						fixed,
						given[1],
						composite,
						ring_homomorphism.RingHomIdentity.Read(polynomials),
						nat_order.LessThanZeroClause,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalUnique.At(
							ringR,
							constantsRing,
							noVariables,
							b.TermAs[Fun[multivariate, multivariate]](
								"λf:((num → num) → A). polynomial_algebra_const(R, «atZero»(f))"),
							b.TermAs[Fun[multivariate, multivariate]]("λf:((num → num) → A). f"),
							p)))
				b.Show(
					"so p is the constant zero, the zero polynomial",
					By(
						zeroValue,
						constantOfValue,
						ring_homomorphism.MapZero.Read(constants),
						function_module.FunZeroDef))
			})
		a.Step(
			"fixing the last variable gives polynomials in the first "+
				"N vanishing everywhere, zero by induction, so p is zero",
			func(b *Argument, induction Fact) {
				p := b.FixAs[multivariate]("p")
				given := b.Conjuncts(
					b.Assume(),
					"R is infinite",
					"p is a polynomial in the first N + 1 variables",
					"and it vanishes at the ring tuples of length N + 1")
				firstVariables := b.TermAs[Set[Nat]]("{i:num | i < suc(N)}")
				substitutions := b.Have(
					"fixing the last variable at any t of R gives zero",
					"∀t:A. t ∈ R.carrier ⇒ «substitution»(polynomial_algebra_const(R, t), p) = λm:(num → num). R.zero",
					Derive(func(c *Argument) {
						t := c.FixAs[A]("t")
						tIn := c.Assume()
						substituted := c.Conjuncts(
							GroupPremises(
								given[1], SubstituteLastVariable.Read(ring).At(c.TermAs[Nat]("N"), c.MemberOf[on.R](t, tIn), p)),
							"p with t in the last place is a polynomial in the first N variables",
							"whose value at an N-tuple is the value of p at it with t put last")
						extended := c.Have(
							"putting t last turns an N-tuple into a ring tuple of length N + 1",
							"∀x:(num → A). ring_tuple(R, N, x) ⇒ ring_tuple(R, suc(N), λi:num. COND(i = N, t, x(i)))",
							Derive(func(d *Argument) {
								d.FixAs[Fun[Nat, A]]("x")
								tuple := d.Conjuncts(
									d.Unfolded(d.Assume(), RingTupleDef),
									"x vanishes from N on",
									"and its first N coordinates lie in R")
								padded := d.Have(
									"from N + 1 on its coordinates are those of x, zero",
									"∀i:num. suc(N) ≤ i ⇒ COND(i = N, t, x(i)) = R.zero",
									Derive(func(e *Argument) {
										e.FixAs[Nat]("i")
										beyond := e.Assume()
										past := e.Have(
											"i is past N and is not N",
											"N ≤ i ∧ ¬(i = N)",
											ByArith(beyond))
										e.Show(
											"so the coordinate at i is x's, zero",
											By(past, tuple[0], vec_space.VecDef))
									}))
								inside := d.Have(
									"below N + 1 its coordinates lie in R: t last, those of x before it",
									"∀i:num. i < suc(N) ⇒ COND(i = N, t, x(i)) ∈ R.carrier",
									Derive(func(e *Argument) {
										i := e.FixAs[Nat]("i")
										inRange := e.Assume()
										e.Cases(e.Term("i = N"))
										e.When(
											"the last coordinate is t",
											func(f *Argument, last Fact) {
												f.Show(
													"which lies in R",
													By(last, tIn))
											})
										e.Otherwise(
											"an earlier coordinate is one of x below N",
											func(f *Argument, other Fact) {
												lower := f.Have(
													"i is below N",
													"i < N",
													ByArith(other, inRange))
												f.Show(
													"which lies in R",
													By(other, lower, tuple[1].At(i)))
											})
									}))
								d.Show(
									"so it is a ring tuple of length N + 1",
									By(padded, inside, RingTupleDef, vec_space.VecDef))
							}))
						vanishing := c.Have(
							"so p with t in the last place vanishes at every ring tuple of length N",
							Statement{
								Binders: "∀x:(num → A).",
								Hypotheses: []string{
									"ring_tuple(R, N, x)",
								},
								Conclusion: "polynomial_value(R, «substitution»(polynomial_algebra_const(R, t), p), x) = R.zero",
							},
							By(substituted[1], extended, given[2]))
						c.Show(
							"and by the hypothesis of induction it is zero",
							By(
								given[0],
								substituted[0],
								vanishing,
								induction.At(c.TermAs[multivariate]("«substitution»(polynomial_algebra_const(R, t), p)"))))
					}))
				inAll := b.Have(
					"p is a polynomial in all the variables",
					"p ∈ polynomial_algebra(R, 𝕌⟨A:num⟩)",
					By(
						given[1],
						polynomial_algebra.PolynomialAlgebraSubset.At(ringR, firstVariables, b.TermAs[Set[Nat]]("𝕌")),
						set_order.SubsetUniv.At(firstVariables),
						set_basic.SubsetDef))
				b.Show(
					"a polynomial all of whose substitutions of a constant for the last variable vanish is zero",
					By(given[0], inAll, substitutions, ZeroAfterEverySubstitution.Read(R).At(b.TermAs[Nat]("N"), p)))
			})
	}),
})}

// PolynomialDeterminedByValues — over an infinite integral domain, two polynomials in N variables
// that take the same value at every ring tuple of length N are equal. Their difference p − q is a
// polynomial in the N variables, and evaluation at a tuple, a ring homomorphism, takes it to the
// difference of the values, zero; so p − q is the zero polynomial (PolynomialVanishingIsZero), and
// p and q agree coefficient by coefficient.
var PolynomialDeterminedByValues = polynomialDeterminedByValuesThm{family.Add(registry.ProofEntry{
	Name: "PolynomialDeterminedByValues",
	Key:  "prop_61a7ce97cc011044",
	Reading: "The infinite carrier is load-bearing, as for PolynomialVanishingIsZero: over a " +
		"field with q elements the polynomials x^q and x in one variable take the same value at " +
		"every point. Only the ring tuples of length N are compared, the points zero from N on.",
	Build: family.Theorem(Statement{
		Binders: "∀R:integral_domain_on(A). ∀N:num. ∀p q:((num → num) → A).",
		Hypotheses: []string{
			"infinite(R.carrier)",
			"p ∈ polynomial_algebra(R, {i:num | i < N})",
			"q ∈ polynomial_algebra(R, {i:num | i < N})",
			"∀x:(num → A). ring_tuple(R, N, x) ⇒ polynomial_value(R, p, x) = polynomial_value(R, q, x)",
		},
		Conclusion: "p = q",
	}, func(
		a *Argument,
		R integral_domain.IntegralDomainFact[on.R],
		N *Expr[Nat],
		p, q *Arrow[_Monomial, A],
		infinite, pIn, qIn, sameValues Fact,
	) {
		type multivariate = Fun[_Monomial, A]
		ringR := a.TermAs[RingOps[A]]("R")
		ring := integral_domain.Ring.Read(R)
		pMember := a.MemberOf[on.Any](a.TermAs[multivariate]("p"), pIn)
		qMember := a.MemberOf[on.Any](a.TermAs[multivariate]("q"), qIn)
		polynomials := a.Have(
			"the polynomials in the N variables form a commutative ring",
			"comm_ring_on(polynomial_algebra_ring(R, {i:num | i < N}))",
			By(ring, polynomial_algebra.PolynomialAlgebraCommRingOn))
		difference := a.Have(
			"p − q is a polynomial in the N variables",
			"(λm:(num → num). p(m) - q(m)) ∈ polynomial_algebra(R, {i:num | i < N})",
			By(pIn, qIn, comm_ring.SubIn.Read(polynomials)))
		vanishes := a.Have(
			"p − q vanishes at every ring tuple of length N",
			"∀x:(num → A). ring_tuple(R, N, x) ⇒ polynomial_value(R, λm:(num → num). p(m) - q(m), x) = R.zero",
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, A]]("x")
				tuple := b.Assume()
				evaluation := b.Have(
					"evaluation at x is a ring homomorphism from the polynomials in the N variables",
					"ring_homomorphism(polynomial_algebra_ring(R, {i:num | i < N}), "+
						"    R, "+
						"    polynomial_algebra_eval(R, R, λa:A. a, x))",
					By(
						ring_homomorphism.RingHomIdentity.Read(ring),
						tuple,
						RingTupleDef,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(
							ringR,
							ringR,
							b.TermAs[Fun[A, A]]("λa:A. a"),
							x,
							b.TermAs[Set[Nat]]("{i:num | i < N}"))))
				values := b.Have(
					"the values of p and q at x lie in R",
					"polynomial_value(R, p, x) ∈ R.carrier ∧ polynomial_value(R, q, x) ∈ R.carrier",
					By(
						ring_homomorphism.MapIn.Read(evaluation).At(pMember),
						ring_homomorphism.MapIn.Read(evaluation).At(qMember),
						PolynomialValueDef))
				split := b.Have(
					"the value of p − q is the difference of the values",
					"polynomial_value(R, λm:(num → num). p(m) - q(m), x) = "+
						"polynomial_value(R, p, x) - polynomial_value(R, q, x)",
					By(ring_homomorphism.MapSub.Read(evaluation).At(pMember, qMember), PolynomialValueDef))
				b.Show(
					"and the two values agree",
					split.Rw(),
					ByArith(ring, values, tuple, sameValues.At(x)))
			}))
		zero := a.Have(
			"so p − q is the zero polynomial",
			"∀m:(num → num). p(m) - q(m) = R.zero",
			By(infinite, difference, vanishes, PolynomialVanishingIsZero.Read(R)))
		a.Show(
			"p and q agree at every monomial, their coefficients lying in R",
			Funext(),
			Derive(func(b *Argument) {
				m := b.FixAs[_Monomial]("m")
				coefficients := b.Have(
					"the coefficients of p and q at m lie in R",
					"p(m) ∈ R.carrier ∧ q(m) ∈ R.carrier",
					By(pIn, qIn, polynomial_algebra.PolynomialAlgebraMember))
				b.Show(
					"their difference is zero",
					ByArith(ring, coefficients, zero.At(m)))
			}))
	}),
})}
