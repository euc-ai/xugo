// roots.go — the linear factor x − a; the factor theorem over any
// commutative ring and, over a domain, the splitting off of a root and the
// bound of the roots by the degree; coprime polynomials share no root;
// finitely many polynomials over a subfield have a common multiple at a
// point; and the monic polynomial vanishing on a finite set, unique and
// fixed by every endomorphism permuting the set.

package polynomial_roots

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// LinearFactor — x − a is a monic polynomial over c of degree at most one,
// whose value at y is y − a, so that a is a root of it, and of degree one
// when one is not zero: its coefficients are −a at zero, one at one and
// zero from two on, so its value is −a + one * y
// (polynomial_evaluation.EvalVecTwo); degree zero would make its coefficient at
// one, the ring one, zero, and in the zero ring every coefficient is one.
var LinearFactor = linearFactorThm{family.Add(registry.ProofEntry{
	Name: "LinearFactor",
	Key:  "prop_6f82f44a48f6683",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a:A.",
		Hypotheses: []string{
			"a ∈ R.carrier",
		},
		Conclusion: "polynomial_over(R.carrier, «linear»(a)) ∧ " +
			"polynomial_monic(«linear»(a)) ∧ " +
			"polynomial_degree(«linear»(a)) ≤ 1 ∧ " +
			"(∀y:A. y ∈ R.carrier ⇒ polynomial_eval(«linear»(a), y) = y - a) ∧ " +
			"polynomial_eval(«linear»(a), a) = R.zero ∧ " +
			"(R.one ≠ R.zero ⇒ polynomial_degree(«linear»(a)) = 1)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], a *Member[A, on.R]) {
			zero, carrier := arg.TermAs[A]("R.zero"), arg.TermAs[Set[A]]("R.carrier")
			zeroth, first := arg.TermAs[Nat]("0"), arg.TermAs[Nat]("1")
			g, gDef := arg.LetAs[Fun[Nat, A]]("g", "«linear»(a)")
			gOver := arg.Have(
				"the variable minus a is a polynomial over c",
				"polynomial_over(R.carrier, g)",
				gDef.Rw(),
				By(
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
					comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring)),
					a,
					polynomial.BasisVectorOver.Read(ring).At(first),
					polynomial.BasisVectorOver.Read(ring).At(zeroth)))
			coefficients := arg.Have(
				"the coefficients of g are -a at zero, one at one, and zero from two on",
				"g(0) = -a ∧ g(1) = R.one ∧ vec⟨suc(1)⟩(g)",
				gDef.Rw(),
				Simp(
					Fwd(vec_space.VecDef),
					Fwd(vec_space.VecSubDef),
					Fwd(vec_space.VecScalarMulDef),
					Fwd(vec_space.BasisVectorDef)),
				ByArith(ring, a))
			degreeBound := arg.Have(
				"g has degree at most one",
				"polynomial_degree(g) ≤ 1",
				By(coefficients, polynomial.DegreeLeast.At(zero, g, first)))
			nonzeroDegreeOne := arg.Have(
				"a nonzero degree at most one is one",
				"polynomial_degree(g) ≠ 0 ⇒ polynomial_degree(g) = 1",
				ByArith(degreeBound))
			degreeZeroTrivial := arg.Have(
				"at degree zero g vanishes from index one on, so its coefficient there, the ring one, is zero",
				"polynomial_degree(g) = 0 ⇒ R.one = R.zero",
				Derive(func(b *Argument) {
					degreeZero := b.Assume()
					short := b.Have(
						"at degree zero g vanishes from one on",
						"vec⟨1⟩(g)",
						By(gOver, degreeZero, polynomial.DegreeZeroIff.At(zero, carrier, g)))
					firstZero := b.Have(
						"its coefficient at one is then zero",
						"g(1) = R.zero",
						By(short, vec_space.VecDef.At(zero, b.VecAt[A](first, "g")), nat_order.LessEqRefl))
					b.Show(
						"and that coefficient is the ring one",
						By(Normalized, coefficients, firstZero))
				}))
			monic := arg.Have(
				"g is monic, including when the ring is zero",
				"polynomial_monic(g)",
				Simp(Fwd(polynomial.PolynomialMonicDef)),
				Derive(func(b *Argument) {
					b.Cases(b.Term("polynomial_degree(g) = 0"))
					b.When(
						"degree zero forces the ring one to equal zero",
						func(c *Argument, degreeZero Fact) {
							oneZero := c.Have(
								"the ring one equals zero",
								"R.one = R.zero",
								By(degreeZero, degreeZeroTrivial))
							leading := c.MemberOf[on.R](
								c.TermAs[A]("g(polynomial_degree(g))"),
								polynomial.CoefficientIn.Read(gOver).At(c.TermAs[Nat]("polynomial_degree(g)")))
							c.Show(
								"in the zero ring the leading coefficient is one",
								CalcEq(
									Leg(
										c.TermAs[A]("g(polynomial_degree(g)) * R.one"),
										"multiplying by one fixes the coefficient",
										By(comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(leading))),
									Leg(
										c.TermAs[A]("g(polynomial_degree(g)) * R.zero"),
										"one is zero in this ring",
										By(Normalized, oneZero)),
									Leg(
										zero,
										"multiplication by zero gives zero",
										By(comm_ring.MulRightZeroOn.Read(ring).At(leading))),
									FinalLeg(
										"zero is the ring one",
										By(oneZero))))
						})
					b.Otherwise(
						"a nonzero degree is one, where the coefficient of g is the ring one",
						func(c *Argument, degreeNonzero Fact) {
							c.Show(
								"the degree is one, so the leading coefficient is g(1), the ring one",
								By(Normalized, degreeNonzero, nonzeroDegreeOne, coefficients))
						})
				}))
			value := arg.Have(
				"at every point y of c, g takes the value y - a",
				"∀y:A. y ∈ R.carrier ⇒ polynomial_eval(g, y) = y - a",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yMember := b.MemberOf[on.R](y, b.Assume())
					b.Show(
						"its value is g(0) + g(1) * y, whose coefficients are -a and one",
						GroupPremises(
							gOver, coefficients, yMember, polynomial_evaluation.EvalVecTwo.Read(ring).AsFact().At(g, y)).Rw(),
						Simp(Fwd(coefficients)),
						ByArith(ring, a, yMember))
				}))
			root := arg.Have(
				"g vanishes at a, its value there being a - a",
				"polynomial_eval(g, a) = R.zero",
				GroupPremises(a, value.At(a)).Rw(),
				ByArith(ring, a))
			degreeOne := arg.Have(
				"degree zero would make one zero, so when one is not zero, g has degree one",
				"R.one ≠ R.zero ⇒ polynomial_degree(g) = 1",
				By(degreeZeroTrivial, nonzeroDegreeOne))
			arg.Show(
				"g, which is x - a, has all six properties",
				By(gOver, monic, degreeBound, value, root, degreeOne))
		}),
})}

// LinearFactorMap — a ring map ι, applied to the coefficients, carries the
// linear factor x − a to x − ι(a): coefficient by coefficient, ι keeps the
// one at x, the zero elsewhere, and the difference and product that put −a
// at the constant term.
var LinearFactorMap = linearFactorMapThm{family.Add(registry.ProofEntry{
	Name: "LinearFactorMap",
	Key:  "prop_bacb34ab4d891b15",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(B). ∀ι:(A → B). ∀a:A.",
		Hypotheses: []string{
			"ring_homomorphism(R, T, ι)",
			"a ∈ R.carrier",
		},
		Conclusion: "(λi:num. " +
			"    ι(vec_sub(basis_vector(R.zero, R.one, 1), " +
			"            vec_scalar_mul(a, basis_vector(R.zero, R.one, 0)), " +
			"            i))) = " +
			"vec_sub(basis_vector(T.zero, T.one, 1), vec_scalar_mul(ι(a), basis_vector(T.zero, T.one, 0)))",
	},
		func(
			arg *Argument,
			R *Expr[RingOps[A]],
			T *Expr[RingOps[B]],
			ι *Arrow[A, B],
			a *Expr[A],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
			aIn Fact,
		) {
			source := ring_homomorphism.Source.Read(hom)
			arg.Do(Funext())
			arg.FixAs[Nat]("i")
			arg.Do(Simp(
				Fwd(vec_space.VecSubDef),
				Fwd(vec_space.VecScalarMulDef),
				Fwd(vec_space.BasisVectorDef)))
			images := []any{
				aIn,
				ring_homomorphism.MapSub.Read(hom),
				ring_homomorphism.MapMul.Read(hom),
				ring_homomorphism.MapOne.Read(hom),
				ring_homomorphism.MapZero.Read(hom),
				comm_ring.ZeroIn.Read(source),
				comm_ring.OneIn.Read(source),
				comm_ring.MulIn.Read(source),
			}
			arg.Cases(arg.TermAs[Bool]("i = 1"))
			arg.When(
				"at the coefficient of x both are one",
				func(b *Argument, atOne Fact) {
					cases := b.Conjuncts(
						b.Have(
							"the basis coefficients at 1",
							"COND(i = 1, R.one, R.zero) = R.one ∧ "+
								"COND(i = 0, R.one, R.zero) = R.zero ∧ "+
								"COND(i = 1, T.one, T.zero) = T.one ∧ "+
								"COND(i = 0, T.one, T.zero) = T.zero",
							ByArith(atOne)),
						"x has coefficient one in R",
						"the constant has coefficient zero in R",
						"x has coefficient one in T",
						"the constant has coefficient zero in T")
					b.Show(
						"ι keeps one less a times zero",
						cases[0].Rw(),
						cases[1].Rw(),
						cases[2].Rw(),
						cases[3].Rw(),
						By(images...))
				})
			arg.Otherwise(
				"away from the coefficient of x",
				func(b *Argument, notOne Fact) {
					b.Cases(b.TermAs[Bool]("i = 0"))
					b.When(
						"at the constant coefficient both are minus a",
						func(c *Argument, atZero Fact) {
							cases := c.Conjuncts(
								c.Have(
									"the basis coefficients at 0",
									"COND(i = 1, R.one, R.zero) = R.zero ∧ "+
										"COND(i = 0, R.one, R.zero) = R.one ∧ "+
										"COND(i = 1, T.one, T.zero) = T.zero ∧ "+
										"COND(i = 0, T.one, T.zero) = T.one",
									ByArith(atZero)),
								"x has coefficient zero in R",
								"the constant has coefficient one in R",
								"x has coefficient zero in T",
								"the constant has coefficient one in T")
							c.Show(
								"ι keeps zero less a times one",
								cases[0].Rw(),
								cases[1].Rw(),
								cases[2].Rw(),
								cases[3].Rw(),
								By(images...))
						})
					b.Otherwise(
						"elsewhere both are zero",
						func(c *Argument, notZero Fact) {
							cases := c.Conjuncts(
								c.Have(
									"the basis coefficients elsewhere",
									"COND(i = 1, R.one, R.zero) = R.zero ∧ "+
										"COND(i = 0, R.one, R.zero) = R.zero ∧ "+
										"COND(i = 1, T.one, T.zero) = T.zero ∧ "+
										"COND(i = 0, T.one, T.zero) = T.zero",
									ByArith(notZero, notOne)),
								"x has coefficient zero in R",
								"the constant has coefficient zero in R",
								"x has coefficient zero in T",
								"the constant has coefficient zero in T")
							c.Show(
								"ι keeps zero less a times zero",
								cases[0].Rw(),
								cases[1].Rw(),
								cases[2].Rw(),
								cases[3].Rw(),
								By(
									aIn,
									ring_homomorphism.MapSub.Read(hom),
									ring_homomorphism.MapMul.Read(hom),
									ring_homomorphism.MapZero.Read(hom),
									comm_ring.ZeroIn.Read(source),
									comm_ring.MulIn.Read(source)))
						})
				})
		}),
})}

// FactorTheorem — a polynomial vanishes at a point of the carrier exactly
// when the variable minus that point divides it. Division by the monic
// linear factor leaves a constant remainder, whose value must be zero.
var FactorTheorem = factorTheoremThm{family.Add(registry.ProofEntry{
	Name: "FactorTheorem",
	Key:  "prop_a762463ddcbc4ece",
	Reading: "No field or domain is needed: dividing by the monic x - a needs no " +
		"inverse. In the zero ring every polynomial is vec_zero and both sides hold.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀a:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"a ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, a) = R.zero ⇔ polynomial_divides(R, «linear»(a), p)",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		p *Arrow[Nat, A],
		a *Member[A, on.R],
		poly Fact,
	) {
		zero, carrier := arg.TermAs[A]("R.zero"), arg.TermAs[Set[A]]("R.carrier")
		zeroth, first := arg.TermAs[Nat]("0"), arg.TermAs[Nat]("1")
		polynomialRing := polynomial.PolynomialRingOn.Read(ring)
		polynomialModule := polynomial.PolynomialModuleOn.Read(ring)
		linear := arg.Conjuncts(
			LinearFactor.Read(ring).At(a),
			"x - a is a polynomial over the ring",
			"it is monic",
			"it has degree at most one",
			"its value at each point y of the ring is y - a",
			"it vanishes at a",
			"and its degree is one when one is not zero")
		g, _ := arg.LetAs[Fun[Nat, A]]("g", "«linear»(a)")
		gOver, degreeBound, gRoot := linear[0], linear[2], linear[4]
		arg.Iff()
		arg.Forward(
			"division by g leaves a constant remainder whose value is zero",
			func(b *Argument, root Fact) {
				q, u, divided := b.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
					GroupPremises(poly, gOver, linear[1], polynomial_division.MonicDivisionExists.Read(ring).At(p, g)),
					"q",
					"u")
				parts := b.Conjuncts(
					divided,
					"the quotient is over the ring",
					"the remainder is over the ring",
					"the remainder vanishes from the degree of g on",
					"p is g times the quotient plus the remainder")
				qOver, uOver, uShort, decomposition := parts[0], parts[1], parts[2], parts[3]
				uConstant := b.Have(
					"g has degree at most one, so the remainder is a constant: its coefficient at zero",
					"u = u(0) • basis_vector(0)",
					Derive(func(c *Argument) {
						uConstantSupport := c.Have(
							"the remainder vanishes from one on",
							"vec⟨1⟩(u)",
							By(
								degreeBound,
								uShort,
								vec_space.VecMono.At(zero, c.TermAs[Nat]("polynomial_degree(g)"), first, u)))
						uDegreeZero := c.Have(
							"the remainder has degree zero",
							"polynomial_degree(u) = 0",
							By(uOver, uConstantSupport, polynomial.DegreeZeroIff.At(zero, carrier, u)))
						c.Show(
							"a polynomial of degree zero is its coefficient at zero as a constant polynomial",
							By(uOver, uDegreeZero, polynomial.DegreeZeroConstant.Read(ring).At(u)))
					}))
				coefficient, coefficientDef := b.LetAs[A]("k", "u(0)")
				coefficientZero := b.Have(
					"k is zero: evaluate the division identity at a, where g vanishes",
					"k = R.zero",
					Derive(func(c *Argument) {
						coefficientIn := c.Have(
							"the constant coefficient belongs to the carrier",
							"k ∈ R.carrier",
							coefficientDef.Rw(),
							By(polynomial.CoefficientIn.Read(uOver).At(c.TermAs[Nat]("0"))))
						coefficientMember := c.MemberOf[on.R](coefficient, coefficientIn)
						uValue := c.Have(
							"the constant remainder evaluates to its coefficient",
							"polynomial_eval(u, a) = k",
							uConstant.Rw(),
							By(polynomial_evaluation.EvalConstant.Read(ring).At(coefficientMember, a)))
						c.Show(
							"k is the remainder's value at a, which at this root of g is p's value, zero",
							By(
								uValue,
								root,
								gOver,
								qOver,
								uOver,
								decomposition,
								gRoot,
								polynomial_evaluation.DivisionValueAtRoot.Read(ring).At(p, g, q, u, a)))
					}))
				uZero := b.Have(
					"the constant remainder is the zero polynomial",
					"u = vec_zero",
					coefficientZero.Rw(),
					uConstant.Rw(),
					By(module.ZeroSmul.Read(polynomialModule), polynomial.BasisVectorOver.Read(ring).At(zeroth)))
				factorization := b.Have(
					"removing the zero remainder gives a factorization of p",
					"p = polynomial_mul(g, q)",
					decomposition.Rw(),
					uZero.Rw(),
					By(
						comm_monoid.RightIdentityOn.Read(comm_ring.AddMonoidOn.Read(polynomialRing)),
						gOver,
						qOver,
						polynomial.PolynomialMulOver.Read(ring).At(g, q)))
				b.Show(
					"the quotient witnesses divisibility by g",
					Unfold(polynomial_division.PolynomialDividesDef),
					Witness(q),
					By(qOver, factorization))
			})
		arg.Backward(
			"every multiple of g vanishes at its root a",
			func(b *Argument, divides Fact) {
				r, factor := b.UnpackAs[Fun[Nat, A]](
					b.Unfolded(divides, polynomial_division.PolynomialDividesDef), "r")
				parts := b.Conjuncts(
					factor,
					"the quotient is over the ring",
					"p is g times this quotient")
				b.Show(
					"evaluate the factorization at the root of g",
					parts[1].Rw(),
					By(gOver, parts[0], gRoot, polynomial_evaluation.EvalMulRoot.Read(ring).At(g, r, a)))
			})
	}),
})}

// DegreeZeroNoRoots — a nonzero polynomial of degree zero has no roots in
// c: it is the constant p(0) • basis_vector(0) with p(0) nonzero, and its
// value at every point of c is p(0).
var DegreeZeroNoRoots = degreeZeroNoRootsThm{family.Add(registry.ProofEntry{
	Name: "DegreeZeroNoRoots",
	Key:  "prop_4e07ec7b777590df",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"p ≠ vec_zero",
			"polynomial_degree(p) = 0",
		},
		Conclusion: "polynomial_roots(R.carrier, p) = ∅",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], given Fact) {
			zero, carrier := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			constant := a.TermAs[A]("p(0)")
			coefficient := a.Have(
				"the constant coefficient, the one at the degree, lies in c and is nonzero",
				"p(0) ∈ R.carrier ∧ p(0) ≠ R.zero",
				By(Normalized, given, polynomial.LeadingCoefficientNonzero.At(zero, carrier, p)))
			values := a.Have(
				"p takes its constant coefficient as its value at every point of c",
				"∀x:A. x ∈ R.carrier ⇒ polynomial_eval(p, x) = p(0)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.Show(
						"p is its constant coefficient times the one polynomial",
						By(
							Normalized,
							coefficient,
							given,
							polynomial.DegreeZeroConstant.Read(ring).At(p),
							polynomial_evaluation.EvalConstant.Read(ring).AsFact().At(constant, x)))
				}))
			a.Show(
				"a nonzero value is never zero",
				Simp(Fwd(PolynomialRootsDef)),
				BySets(Normalized, values, coefficient))
		}),
})}

// RootFactorization — over a domain, a root a of a nonzero polynomial p
// splits off the factor x − a: the quotient q is nonzero and one lower in
// degree, and the roots of p are a with the roots of q, since a product
// of domain elements vanishes only where a factor does.
var RootFactorization = rootFactorizationThm{family.Add(registry.ProofEntry{
	Name: "RootFactorization",
	Key:  "prop_aadffda2e0d07639",
	Reading: "The quotient may still vanish at a. Inserting a describes the root " +
		"set and adds at most one root; distinctness requires an additional hypothesis.",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀p:(num → A). ∀a:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"p ≠ vec_zero",
			"a ∈ R.carrier",
			"polynomial_eval(p, a) = R.zero",
		},
		Conclusion: "∃q:(num → A). " +
			"    polynomial_over(R.carrier, q) ∧ " +
			"    q ≠ vec_zero ∧ " +
			"    p = polynomial_mul(«linear»(a), q) ∧ " +
			"    polynomial_degree(p) = suc(polynomial_degree(q)) ∧ " +
			"    polynomial_roots(R.carrier, p) = insert(a, polynomial_roots(R.carrier, q))",
	}, func(
		arg *Argument,
		domain integral_domain.IntegralDomainFact[on.R],
		p *Arrow[Nat, A],
		a *Expr[A],
		given Fact,
	) {
		parts := arg.Conjuncts(
			given,
			"p is over the domain",
			"p is nonzero",
			"a lies in the carrier",
			"a is a root of p")
		pOver, pNonzero, aIn, pRoot := parts[0], parts[1], parts[2], parts[3]
		aMember := arg.MemberOf[on.R](a, aIn)
		ring := integral_domain.Ring.Read(domain)
		polynomialRing := polynomial.PolynomialRingOn.Read(ring)
		linear := arg.Conjuncts(
			LinearFactor.Read(ring).At(aMember),
			"x - a is a polynomial over the domain",
			"it is monic",
			"it has degree at most one",
			"its value at each point y of the domain is y - a",
			"it vanishes at a",
			"and its degree is one when one is not zero")
		g, gDef := arg.LetAs[Fun[Nat, A]]("g", "«linear»(a)")
		gOver, gMonic, values, gDegree := linear[0], linear[1], linear[3], linear[5]
		gDividesP := arg.Have(
			"a root gives a linear divisor",
			"polynomial_divides(R, g, p)",
			gDef.Rw(),
			By(pOver, aMember, pRoot, FactorTheorem.Read(ring).At(p, aMember)))
		q, factor := arg.UnpackAs[Fun[Nat, A]](
			arg.Unfolded(gDividesP, polynomial_division.PolynomialDividesDef), "q")
		factorParts := arg.Conjuncts(
			factor,
			"q is over the domain",
			"p is g times q")
		qOver, factorEquation := factorParts[0], factorParts[1]
		qNonzero := arg.Have(
			"the quotient is nonzero because p is",
			"q ≠ vec_zero",
			Derive(func(b *Argument) {
				denial := b.SupposeNot()
				qZero := b.Have(
					"otherwise q is zero",
					"q = vec_zero",
					By(Normalized, denial))
				pZero := b.Have(
					"then p is zero",
					"p = vec_zero",
					factorEquation.Rw(),
					qZero.Rw(),
					By(gOver, comm_ring.MulRightZeroOn.Read(polynomialRing)))
				b.Show(
					"this contradicts the choice of p",
					By(Normalized, pNonzero, pZero))
			}))
		productDegree := arg.Have(
			"degrees add for these nonzero factors over a domain, g being monic",
			"polynomial_degree(p) = polynomial_degree(g) + polynomial_degree(q)",
			factorEquation.Rw(),
			By(
				gOver,
				qOver,
				gMonic,
				polynomial.MonicNonzero.Read(domain).At(g),
				qNonzero,
				polynomial.DegreeMul.Read(domain).At(g, q)))
		degreeStep := arg.Have(
			"g has degree one, one and zero being distinct in a "+
				"domain, so removing the root lowers the degree by one",
			"polynomial_degree(p) = suc(polynomial_degree(q))",
			ByArith(productDegree, integral_domain.OneNotZero.Read(domain), gDegree))
		rootForced := arg.Have(
			"a root of p is a or a root of q",
			"∀x:A. x ∈ R.carrier ∧ polynomial_eval(p, x) = R.zero ⇒ x = a ∨ polynomial_eval(q, x) = R.zero",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				atRoot := b.Conjuncts(
					b.Assume(),
					"x lies in the carrier",
					"p vanishes at x")
				xMember := b.MemberOf[on.R](x, atRoot[0])
				gValueIn := b.Have(
					"g evaluates into the carrier",
					"polynomial_eval(g, x) ∈ R.carrier",
					By(gOver, polynomial_evaluation.EvalIn.Read(ring).At(g, xMember)))
				qValueIn := b.Have(
					"q evaluates into the carrier",
					"polynomial_eval(q, x) ∈ R.carrier",
					By(qOver, polynomial_evaluation.EvalIn.Read(ring).At(q, xMember)))
				gValue := b.MemberOf[on.R](b.TermAs[A]("polynomial_eval(g, x)"), gValueIn)
				qValue := b.MemberOf[on.R](b.TermAs[A]("polynomial_eval(q, x)"), qValueIn)
				productValue := b.Have(
					"evaluation multiplies the factor values",
					"polynomial_eval(p, x) = polynomial_eval(g, x) * polynomial_eval(q, x)",
					factorEquation.Rw(),
					By(gOver, qOver, polynomial_evaluation.EvalMul.Read(ring).At(g, q, xMember)))
				gNotZero := b.Unless(
					b.Term("polynomial_eval(g, x) = R.zero"),
					"a root of g is a",
					Given(func(c *Argument, gZero Fact) {
						c.Show(
							"g(x) is x - a, so x - a is zero and x is a",
							ByArith(ring, aMember, xMember, gValueIn, gZero, values.At(x)))
					}))
				qZero := b.Have(
					"the product of the factor values vanishes, and the "+
						"nonzero value of g forces the value of q to be zero",
					"polynomial_eval(q, x) = R.zero",
					By(
						gNotZero,
						atRoot[1],
						productValue,
						integral_domain.NoZeroDivisors.Read(domain).At(gValue, qValue)))
				b.Show(
					"so x is a root of q",
					By(qZero))
			}))
		rootsPreserved := arg.Have(
			"each root of q remains a root of p",
			"∀x:A. x ∈ R.carrier ∧ polynomial_eval(q, x) = R.zero ⇒ polynomial_eval(p, x) = R.zero",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				atRoot := b.Conjuncts(
					b.Assume(),
					"x lies in the carrier",
					"q vanishes at x")
				xMember := b.MemberOf[on.R](x, atRoot[0])
				b.Show(
					"a vanishing factor makes the product vanish",
					factorEquation.Rw(),
					By(atRoot[1], gOver, qOver, polynomial_evaluation.EvalMulRoot.Read(ring).At(q, g, xMember)))
			}))
		rootsEquation := arg.Have(
			"the root set is obtained by inserting a into that of q",
			"polynomial_roots(R.carrier, p) = insert(a, polynomial_roots(R.carrier, q))",
			Simp(Fwd(PolynomialRootsDef)),
			BySets(aMember, pRoot, rootForced, rootsPreserved))
		arg.Take(q)
		arg.Show(
			"q has the required factorization, degree, and roots",
			By(qOver, qNonzero, factorEquation, degreeStep, rootsEquation))
	}),
})}

// IrreducibleRootLinear — an irreducible polynomial over a domain with a
// root in its carrier has degree one: factoring out the root leaves a
// constant cofactor.
var IrreducibleRootLinear = irreducibleRootLinearThm{family.Add(registry.ProofEntry{
	Name: "IrreducibleRootLinear",
	Key:  "prop_7e74087d21c10b19",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_irreducible(R, p)",
			"x ∈ R.carrier",
			"polynomial_eval(p, x) = R.zero",
		},
		Conclusion: "polynomial_degree(p) = 1",
	}, func(
		a *Argument,
		domain integral_domain.IntegralDomainFact[on.R],
		p *Arrow[Nat, A],
		x *Expr[A],
		given Fact,
	) {
		premises := a.Conjuncts(
			given,
			"p is irreducible",
			"the root lies in the domain",
			"p vanishes at the root")
		irreducible, xIn, root := premises[0], premises[1], premises[2]
		xMember := a.MemberOf[on.R](x, xIn)
		irreducibility := a.Conjuncts(
			a.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
			"p is over the domain",
			"its degree is positive",
			"in every factorization one factor is constant")
		over, positive, constantFactor := irreducibility[0], irreducibility[1], irreducibility[2]
		nonzero := a.Have(
			"a polynomial of positive degree is nonzero",
			"p ≠ vec_zero",
			By(
				Normalized,
				over,
				positive,
				polynomial.DegreeVecZero.At(a.TermAs[A]("R.zero")),
				nat_order.LessThanIrrefl.At(a.TermAs[Nat]("0"))))
		q, factorization := a.ObtainAs[Fun[Nat, A]](
			"factor out the root",
			"∃q:(num → A). "+
				"    polynomial_over(R.carrier, q) ∧ "+
				"    p = polynomial_mul(«linear»(x), q) ∧ "+
				"    polynomial_degree(p) = suc(polynomial_degree(q))",
			By(nonzero, root, over, positive, RootFactorization.Read(domain).At(p, xMember)))
		linearData := a.Have(
			"the root factor has degree one",
			"polynomial_over(R.carrier, «linear»(x)) ∧ polynomial_degree(«linear»(x)) = 1",
			By(
				integral_domain.OneNotZero.Read(domain),
				LinearFactor.Read(integral_domain.Ring.Read(domain)).At(xMember)))
		constant := a.Have(
			"irreducibility makes the cofactor constant",
			"polynomial_degree(q) = 0",
			ByArith(constantFactor.At(a.TermAs[Fun[Nat, A]]("«linear»(x)"), q), factorization, linearData))
		a.Show(
			"the polynomial has degree one",
			ByArith(constant, factorization))
	}),
})}

// RootBound — over a domain, a nonzero polynomial has at most its degree
// many roots: strong induction on the degree, the polynomial quantified in
// the hypothesis. An empty root set is bounded outright; otherwise a root
// splits off its factor (RootFactorization), whose quotient is one lower
// in degree and has at most one root fewer.
var RootBound = rootBoundThm{family.Add(registry.ProofEntry{
	Name:    "RootBound",
	Key:     "prop_e821827f6d6b360a",
	Reading: "The domain is load-bearing: over ℤ/8, x² - 1 has the four roots 1, 3, 5, 7.",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"p ≠ vec_zero",
		},
		Conclusion: "finite(polynomial_roots(R.carrier, p)) ∧ " +
			"card(polynomial_roots(R.carrier, p)) ≤ polynomial_degree(p)",
	},
		func(
			arg *Argument,
			domain integral_domain.IntegralDomainFact[on.R],
			p *Arrow[Nat, A],
			poly, nonzero Fact,
		) {
			bound := arg.TermAs[Fun[Nat, Bool]](
				"λn:num. ∀f:(num → A). " +
					"    polynomial_over(R.carrier, f) ∧ f ≠ vec_zero ∧ polynomial_degree(f) = n ⇒ " +
					"    finite(polynomial_roots(R.carrier, f)) ∧ card(polynomial_roots(R.carrier, f)) ≤ n")
			arg.Show(
				"strong induction on the degree bounds the roots of "+
					"every nonzero polynomial over the domain, p among them",
				ByInduction(At(
					nat_order.StrongInduction, bound, arg.TermAs[Nat]("polynomial_degree(p)")), poly, nonzero,
					Case(
						"granted the bound below degree n, a nonzero polynomial of degree n has at most n roots",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							smaller := b.Assume()
							f := b.FixAs[Fun[Nat, A]]("f")
							given := b.Conjuncts(
								b.Assume(),
								"f is over the domain",
								"f is nonzero",
								"f has degree n")
							degree := given[2]
							nonempty := b.Unless(
								b.Term("polynomial_roots(R.carrier, f) = ∅"),
								"set an empty root set aside",
								Given(func(c *Argument, empty Fact) {
									c.Show(
										"the empty root set is finite, and its cardinality, zero, is at most n",
										empty.Rw(),
										SplitConj(
											Case(
												"the empty set is finite",
												By(finite_set.FiniteRules)),
											Case(
												"the cardinality of the empty set, zero, is at most n",
												Simp(Fwd(cardinality.CardClauses)),
												ByArith())))
								}))
							rootSet := b.TermAs[Set[A]]("polynomial_roots(R.carrier, f)")
							a, aRoot := b.ObtainAs[A](
								"a nonempty root set contains a root",
								"∃a:A. a ∈ polynomial_roots(R.carrier, f)",
								By(nonempty, set_basic.MemberNotEmpty.At(rootSet)))
							aFacts := b.Conjuncts(
								b.Have(
									"a is a carrier element where f vanishes",
									"a ∈ R.carrier ∧ polynomial_eval(f, a) = R.zero",
									BySets(b.Unfolded(aRoot, PolynomialRootsDef))),
								"a lies in the carrier",
								"f vanishes at a")
							aIn, fVanishesAtA := aFacts[0], aFacts[1]
							aMember := b.MemberOf[on.R](a, aIn)
							q, reduced := b.UnpackAs[Fun[Nat, A]](
								GroupPremises(given[0], given[1], fVanishesAtA, RootFactorization.Read(domain).At(f, aMember)), "q")
							parts := b.Conjuncts(
								reduced,
								"q is over the domain",
								"q is nonzero",
								"f is the linear factor times q",
								"the degree drops by one",
								"a is inserted into the roots of q")
							qOver, qNonzero, degreeStep, rootsEquation := parts[0], parts[1], parts[3], parts[4]
							degreeQ := b.TermAs[Nat]("polynomial_degree(q)")
							quotientSmaller := b.Have(
								"the quotient's degree lies below n",
								"polynomial_degree(q) < n",
								ByArith(degree, degreeStep))
							quotientRoots := b.Have(
								"the hypothesis below n counts the quotient's roots",
								"finite(polynomial_roots(R.carrier, q)) ∧ "+
									"card(polynomial_roots(R.carrier, q)) ≤ polynomial_degree(q)",
								By(qOver, qNonzero, quotientSmaller, smaller.At(degreeQ, q)))
							insertBound := b.Have(
								"inserting a adds at most one root",
								"finite(insert(a, polynomial_roots(R.carrier, q))) ∧ "+
									"card(insert(a, polynomial_roots(R.carrier, q))) ≤ suc(polynomial_degree(q))",
								By(
									quotientRoots,
									cardinality.InsertCountsAtMostOneMore.At(
										b.TermAs[Set[A]]("polynomial_roots(R.carrier, q)"), a, degreeQ)))
							b.Show(
								"n is the degree of f, one more than that of q, so this bounds the root set of f by n",
								rootsEquation.Rw(),
								degree.RwRev(),
								degreeStep.Rw(),
								By(insertBound))
						}))))
		}),
})}

// PolynomialCommonMultiple — finitely many nonzero polynomials p(s), s ∈ E,
// over k have a nonzero common multiple at t: a nonzero c over k with
// c(t) = p(s)(t) · q(t) for some q over k, at each s. Start from the nonzero a
// and multiply the p(s) in one at a time.
var PolynomialCommonMultiple = polynomialCommonMultipleThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCommonMultiple",
	Key:  "prop_856500d0b4da5fcf",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "value", Text: "λf:(num → A). polynomial_eval(f, t)"},
			{Name: "multiple", Text: "λS:set(B). ∃c:(num → A). " +
				"    polynomial_over(k, c) ∧ " +
				"    c ≠ vec_zero ∧ " +
				"    (∀s:B. " +
				"        s ∈ S ⇒ ∃q:(num → A). polynomial_over(k, q) ∧ «value»(c) = «value»(p(s)) * «value»(q))"},
			{Name: "good", Text: "λs:B. polynomial_over(k, p(s)) ∧ p(s) ≠ vec_zero"},
		},
		Binders: "∀M:field_on(A). ∀k:set(A). ∀t:A. ∀E:set(B). ∀p:(B → num → A). ∀a:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"t ∈ M.carrier",
			"finite(E)",
			"∀s:B. s ∈ E ⇒ «good»(s)",
			"polynomial_over(k, a)",
			"a ≠ vec_zero",
		},
		Conclusion: "«multiple»(E)",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		t *Expr[A],
		E *Expr[Set[B]],
		p *Arrow[B, Fun[Nat, A]],
		a *Arrow[Nat, A],
		subfieldK, tInField, finiteE, allGood, overA, nonzeroA Fact,
	) {
		ring := field.RingOn.Read(M)
		tm := arg.MemberOf[on.M](t, tInField)
		overField := arg.Have(
			"A polynomial over k takes its values at t in M",
			"∀f:(num → A). polynomial_over(k, f) ⇒ «value»(f) ∈ M.carrier",
			Derive(func(b *Argument) {
				f := b.FixAs[Fun[Nat, A]]("f")
				over := b.Assume()
				onField := b.Have(
					"it is a polynomial over M",
					"polynomial_over(M.carrier, f)",
					By(
						over,
						subfieldK,
						field.SubfieldSubset.At(b.TermAs[FieldOps[A]]("M"), k),
						polynomial.PolynomialOverMono.At(b.TermAs[A]("M.zero"), k, b.TermAs[Set[A]]("M.carrier"), f)))
				b.Show(
					"so its value lies in M",
					By(onField, tm, polynomial_evaluation.EvalIn.Read(ring).AsFact().At(f, t)))
			}))
		arg.Show(
			"a nonzero common multiple grows with the set",
			ByInduction(
				finite_set.FiniteInductFreshOn,
				arg.Have(
					"E is finite and all its polynomials are good",
					"finite(E) ∧ (∀y:B. y ∈ E ⇒ «good»(y))",
					By(finiteE, allGood)),
				Case(
					"over no polynomial, a itself serves",
					Derive(func(b *Argument) {
						b.Take(a)
						b.Show(
							"nothing is asked of it",
							BySets(overA, nonzeroA))
					})),
				Case(
					"multiply in one more polynomial",
					Derive(func(b *Argument) {
						b.FixAs[B]("x")
						b.FixAs[Set[B]]("T")
						given := b.Conjuncts(
							b.Assume(),
							"T has a common multiple",
							"x is fresh",
							"T is finite",
							"p(x) is a polynomial over k",
							"p(x) is nonzero",
							"each member of T is good")
						c, chosen := b.UnpackAs[Fun[Nat, A]](given[0], "c")
						cData := b.Conjuncts(
							chosen,
							"c is a polynomial over k",
							"c is nonzero",
							"c is a multiple over T")
						px := b.TermAs[Fun[Nat, A]]("p(x)")
						pxData := given[3:5]
						product := b.TermAs[Fun[Nat, A]]("polynomial_mul(c, p(x))")
						data := b.Conjuncts(
							GroupPremises(
								subfieldK, cData[0], given[3], At(Read(polynomial_evaluation.PolynomialProductData, M), k, c, px)),
							"the product is a polynomial over k",
							"the product is nonzero",
							"it evaluates to the product of the values")
						nonzero := b.Have(
							"The product is nonzero",
							"polynomial_mul(c, p(x)) ≠ vec_zero",
							By(data[1], cData[1], pxData[1]))
						valueOf := b.Have(
							"The product evaluates to the product of the values at t",
							"«value»(polynomial_mul(c, p(x))) = «value»(c) * «value»(p(x))",
							By(data[2].At(t), tInField))
						b.Take(product)
						multiples := b.Have(
							"The product is a multiple of each polynomial",
							Statement{
								Binders: "∀s:B.",
								Hypotheses: []string{
									"s ∈ insert(x, T)",
								},
								Conclusion: "∃q:(num → A). " +
									"    polynomial_over(k, q) ∧ «value»(polynomial_mul(c, p(x))) = «value»(p(s)) * «value»(q)",
							},
							Derive(func(d *Argument) {
								s := d.FixAs[B]("s")
								member := d.Assume()
								d.Cases(d.Term("s = x"))
								d.When(
									"the new polynomial divides the product, the cofactor c",
									func(e *Argument, same Fact) {
										e.Take(c)
										flipped := e.Have(
											"The two factors commute",
											"«value»(c) * «value»(p(x)) = «value»(p(x)) * «value»(c)",
											ByArith(ring, overField.At(c), overField.At(px), cData[0], pxData[0]))
										e.Show(
											"s is x",
											By(cData[0], valueOf, flipped, same))
									})
								d.Otherwise(
									"an old polynomial divides c",
									func(e *Argument, other Fact) {
										inT := e.Have(
											"s lies in T",
											"s ∈ T",
											BySets(member, other))
										q, qData := e.UnpackAs[Fun[Nat, A]](GroupPremises(inT, cData[2].At(s)), "q")
										qParts := e.Conjuncts(
											qData,
											"q is a polynomial over k",
											"c(t) is p(s)(t) · q(t)")
										cofactor := e.Conjuncts(
											GroupPremises(
												subfieldK, qParts[0], given[3], At(Read(polynomial_evaluation.PolynomialProductData, M), k, q, px)),
											"q · p(x) is a polynomial over k",
											"it is nonzero with its factors",
											"it evaluates to the product of the values")
										ps := e.TermAs[Fun[Nat, A]]("p(s)")
										overPs := e.Have(
											"p(s) is a polynomial over k",
											"polynomial_over(k, p(s))",
											By(inT, given[5].At(s)))
										e.Take(e.TermAs[Fun[Nat, A]]("polynomial_mul(q, p(x))"))
										cofactorValue := e.Have(
											"The cofactor evaluates to the product of the values",
											"«value»(polynomial_mul(q, p(x))) = «value»(q) * «value»(p(x))",
											By(cofactor[2].At(t), tInField))
										regroup := e.Have(
											"so the values regroup",
											"(«value»(p(s)) * «value»(q)) * «value»(p(x)) = «value»(p(s)) * («value»(q) * «value»(p(x)))",
											ByArith(ring, overField.At(ps), overField.At(q), overField.At(px), overPs, qParts[0], pxData[0]))
										e.Show(
											"the product is p(s) times the larger cofactor",
											By(cofactor[0], valueOf, qParts[1], cofactorValue, regroup))
									})
							}))
						b.Show(
							"the product has the three properties",
							By(data[0], nonzero, multiples))
					})),
			))
	}),
})}

// CoprimeNoCommonRoot — coprime polynomials over a field share no root: at
// a common root both summands of a Bézout identity vanish, while their sum
// is one.
var CoprimeNoCommonRoot = coprimeNoCommonRootThm{family.Add(registry.ProofEntry{
	Name: "CoprimeNoCommonRoot",
	Key:  "prop_9fe238ec9112e07c",
	Build: field.FieldOn.Law(Statement{
		Binders: "∀p q:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_over(F.carrier, q)",
			"polynomial_coprime(field_ring(F), p, q)",
			"x ∈ F.carrier",
		},
		Conclusion: "¬(polynomial_eval(p, x) = F.zero ∧ polynomial_eval(q, x) = F.zero)",
	},
		func(
			a *Argument,
			fieldOn field.FieldFact[on.F],
			p, q *Arrow[Nat, A],
			x *Member[A, on.F],
			given Fact,
		) {
			ring := field.RingOn.Read(fieldOn)
			parts := a.Conjuncts(
				given,
				"p is over the field",
				"q is over the field",
				"p and q are coprime")
			u, v, bezout := a.Unpack2As[Fun[Nat, A], Fun[Nat, A]](
				a.Unfolded(parts[2], polynomial_division.PolynomialCoprimeDef), "u", "v")
			commonRoot := a.SupposeNot()
			up, vq :=
				a.TermAs[Fun[Nat, A]]("polynomial_mul(u, p)"), a.TermAs[Fun[Nat, A]]("polynomial_mul(v, q)")
			productsOver := a.Have(
				"the two Bézout summands are over the field",
				"polynomial_over(F.carrier, polynomial_mul(u, p)) ∧ "+
					"polynomial_over(F.carrier, polynomial_mul(v, q))",
				By(
					bezout,
					parts[0],
					parts[1],
					polynomial.PolynomialMulOver.Read(ring).At(u, p),
					polynomial.PolynomialMulOver.Read(ring).At(v, q)))
			productsVanish := a.Have(
				"both Bézout summands vanish at the common root",
				"polynomial_eval(polynomial_mul(u, p), x) = F.zero ∧ "+
					"polynomial_eval(polynomial_mul(v, q), x) = F.zero",
				By(
					commonRoot,
					bezout,
					parts[0],
					parts[1],
					x,
					polynomial_evaluation.EvalMulRoot.Read(ring).At(p, u, x),
					polynomial_evaluation.EvalMulRoot.Read(ring).At(q, v, x)))
			evaluatesZero := a.Have(
				"the Bézout sum evaluates to zero",
				"polynomial_eval(polynomial_mul(u, p) + polynomial_mul(v, q), x) = F.zero",
				By(
					comm_ring.ZeroIn.Read(ring),
					comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)),
					productsOver,
					productsVanish,
					x,
					polynomial_evaluation.EvalAdd.Read(ring).At(up, vq, x)))
			evaluatesOne := a.Have(
				"the Bézout identity makes that same sum evaluate to one",
				"polynomial_eval(polynomial_mul(u, p) + polynomial_mul(v, q), x) = F.one",
				By(
					bezout,
					x,
					polynomial_evaluation.EvalBasisVector.Read(ring).At(a.TermAs[Nat]("0"), x),
					comm_monoid.MonoidPowDef))
			a.Show(
				"a common root would make one equal zero",
				By(field.OneNotZeroOn.Read(fieldOn), evaluatesZero, evaluatesOne))
		}),
})}

// MonicVanishingPolynomial — over a domain a finite set S of points is the
// zero set of a monic polynomial of degree card(S), the product of the linear
// factors at its points, built one point at a time.
var MonicVanishingPolynomial = monicVanishingPolynomialThm{family.Add(registry.ProofEntry{
	Name: "MonicVanishingPolynomial",
	Key:  "prop_8ef34dcd29cc2e04",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀S:set(A).",
		Hypotheses: []string{
			"finite(S)",
			"S ⊆ R.carrier",
		},
		Conclusion: "∃g:(num → A). " +
			"    polynomial_over(R.carrier, g) ∧ " +
			"    polynomial_monic(g) ∧ " +
			"    polynomial_degree(g) = card(S) ∧ " +
			"    (∀r:A. r ∈ S ⇒ polynomial_eval(g, r) = R.zero)",
	}, func(
		arg *Argument,
		domain integral_domain.IntegralDomainFact[on.R],
		S *Expr[Set[A]],
		hypotheses Fact,
	) {
		ring := integral_domain.Ring.Read(domain)
		elements := arg.Have(
			"every point of S lies in R",
			"∀a:A. a ∈ S ⇒ a ∈ R.carrier",
			BySets(hypotheses))
		arg.Show(
			"induction on the finite set S",
			ByInduction(finite_set.FiniteInductFreshOn, elements, hypotheses,
				Case(
					"on the empty set the polynomial one has nothing to vanish on",
					Derive(func(b *Argument) {
						unit := b.TermAs[Fun[Nat, A]]("basis_vector(0)")
						degreeZero := b.Have(
							"the polynomial one has degree zero",
							"polynomial_degree(basis_vector(0)) = 0",
							By(
								integral_domain.OneNotZero.Read(domain),
								polynomial.DegreeBasisVector.Read(ring).At(b.TermAs[Nat]("0"))))
						monic := b.Have(
							"its coefficient at degree zero is one",
							"polynomial_monic(basis_vector(0))",
							Unfold(polynomial.PolynomialMonicDef),
							degreeZero.Rw(),
							Simp(Fwd(vec_space.BasisVectorDef)),
							Basic())
						b.Take(unit)
						b.Do(Simp(Fwd(cardinality.CardClauses)))
						b.Show(
							"one is a monic polynomial of degree zero",
							By(
								degreeZero,
								monic,
								polynomial.BasisVectorOver.Read(ring).At(b.TermAs[Nat]("0")),
								set_basic.NotInEmpty))
					})),
				Case(
					"a new point multiplies the polynomial by its linear factor",
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						c.FixAs[Set[A]]("t")
						given := c.Conjuncts(
							c.Assume(),
							"a monic polynomial vanishes on t",
							"x is new",
							"t is finite",
							"x lies in R",
							"t lies in R")
						g, gFacts := c.UnpackAs[Fun[Nat, A]](given[0], "g")
						parts := c.Conjuncts(
							gFacts,
							"g is over R",
							"g is monic",
							"g has degree card(t)",
							"g vanishes on t")
						gOver, gMonic, gDegree, gVanishes := parts[0], parts[1], parts[2], parts[3]
						xm := c.MemberOf[on.R](x, given[3])
						line := c.Conjuncts(
							LinearFactor.Read(ring).At(xm),
							"f is over R",
							"f is monic",
							"f has degree at most one",
							"f evaluates to the difference",
							"f vanishes at x",
							"f has degree one in a nontrivial ring")
						f, _ := c.LetAs[Fun[Nat, A]]("f", "«linear»(x)")
						fOver, fMonic, fVanishes := line[0], line[1], line[4]
						fDegree := c.Have(
							"f has degree one",
							"polynomial_degree(f) = 1",
							By(line[5], integral_domain.OneNotZero.Read(domain)))
						_, hDef := c.LetAs[Fun[Nat, A]]("h", "polynomial_mul(f, g)")
						hDegree := c.Have(
							"the degree of h is one more than that of g",
							"polynomial_degree(h) = 1 + card(t)",
							hDef.Rw(),
							fDegree.RwRev(),
							gDegree.RwRev(),
							By(
								fOver,
								gOver,
								polynomial.MonicNonzero.Read(domain).At(f),
								polynomial.MonicNonzero.Read(domain).At(g),
								fMonic,
								gMonic,
								polynomial.DegreeMul.Read(domain).At(f, g)))
						hLeading := c.Have(
							"the leading coefficient of h is the product of those of f and g",
							"h(polynomial_degree(f) + polynomial_degree(g)) = "+
								"f(polynomial_degree(f)) * g(polynomial_degree(g))",
							By(fOver, gOver, hDef, polynomial.LeadingCoefficientMul.Read(ring).At(f, g)))
						c.Take(c.TermAs[Fun[Nat, A]]("h"))
						c.Do(SplitConjAll(
							Case(
								"h is a polynomial over R",
								By(Normalized, fOver, gOver, hDef, polynomial.PolynomialMulOver.Read(ring).At(f, g))),
							Case(
								"h is monic",
								Derive(func(d *Argument) {
									degrees := d.Have(
										"the degree of h is the sum of the degrees of f and g",
										"polynomial_degree(h) = polynomial_degree(f) + polynomial_degree(g)",
										ByArith(hDegree, fDegree, gDegree))
									one := d.Have(
										"one times one is one",
										"f(polynomial_degree(f)) * g(polynomial_degree(g)) = R.one",
										d.Unfolded(fMonic, polynomial.PolynomialMonicDef).Rw(),
										d.Unfolded(gMonic, polynomial.PolynomialMonicDef).Rw(),
										ByArith(ring, comm_ring.OneIn.Read(ring)))
									d.Show(
										"its leading coefficient is one",
										Simp(Fwd(polynomial.PolynomialMonicDef)),
										degrees.Rw(),
										By(hLeading, one))
								})),
							Case(
								"h has degree card(insert(x, t))",
								Simp(Fwd(cardinality.CardClauses)),
								ByArith(given[1], given[2], hDegree)),
							Case(
								"h vanishes on t and at x",
								Derive(func(d *Argument) {
									r := d.FixAs[A]("r")
									rIn := d.Assume()
									cases := d.Have(
										"r is x, or lies in t",
										"r = x ∨ r ∈ t",
										BySets(rIn))
									rInR := d.Have(
										"r lies in R",
										"r ∈ R.carrier",
										By(Normalized, cases, given[3], given[4]))
									rm := d.MemberOf[on.R](r, rInR)
									d.Cases(d.Term("r = x"))
									d.When(
										"at x the factor f vanishes",
										func(e *Argument, atX Fact) {
											e.Show(
												"f vanishes there",
												hDef.Rw(),
												atX.Rw(),
												By(fOver, gOver, fVanishes, xm, polynomial_evaluation.EvalMulRoot.Read(ring).At(f, g, xm)))
										})
									d.Otherwise(
										"at a point of t the factor g vanishes",
										func(e *Argument, away Fact) {
											e.Show(
												"g vanishes there",
												hDef.Rw(),
												By(
													fOver,
													gOver,
													gVanishes.At(r),
													cases,
													away,
													rm,
													polynomial_evaluation.EvalMulRoot.Read(ring).At(g, f, rm)))
										})
								}))))
					}))))
	}),
})}

// MonicVanishingUnique — two monic polynomials of degree card(S) over a domain
// that vanish on the finite set S are equal: their difference has degree below
// card(S) and vanishes on S, more points than a nonzero polynomial of that degree
// has roots.
var MonicVanishingUnique = monicVanishingUniqueThm{family.Add(registry.ProofEntry{
	Name: "MonicVanishingUnique",
	Key:  "prop_22a93171707b4fb6",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀S:set(A). ∀p q:(num → A).",
		Hypotheses: []string{
			"finite(S)",
			"S ⊆ R.carrier",
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_monic(p)",
			"polynomial_monic(q)",
			"polynomial_degree(p) = card(S)",
			"polynomial_degree(q) = card(S)",
			"∀r:A. r ∈ S ⇒ polynomial_eval(p, r) = R.zero",
			"∀r:A. r ∈ S ⇒ polynomial_eval(q, r) = R.zero",
		},
		Conclusion: "p = q",
	}, func(
		arg *Argument,
		domain integral_domain.IntegralDomainFact[on.R],
		S *Expr[Set[A]],
		p, q *Arrow[Nat, A],
		finiteS, inR, pOver, qOver, pMonic, qMonic, pDegree, qDegree, pVanishes, qVanishes Fact,
	) {
		ring := integral_domain.Ring.Read(domain)
		zero := arg.TermAs[A]("R.zero")
		carrier := arg.TermAs[Set[A]]("R.carrier")
		d, dDef := arg.LetAs[Fun[Nat, A]]("d", "p - q")
		dOver := arg.Have(
			"the difference is a polynomial over R",
			"polynomial_over(R.carrier, d)",
			dDef.Rw(),
			By(pOver, qOver, comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring))))
		dBelow := arg.Have(
			"the difference has no coefficient at or past card(S)",
			"vec⟨card(S)⟩(d)",
			Simp(Fwd(vec_space.VecDef), Fwd(dDef), Fwd(vec_space.VecSubDef)),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				past := b.Assume()
				b.Cases(b.TermAs[Bool]("i = card(S)"))
				b.When(
					"at card(S) both leading coefficients are one",
					func(c *Argument, atTop Fact) {
						c.Show(
							"one minus one is zero",
							atTop.Rw(),
							Derive(func(e *Argument) {
								pTop := e.Have(
									"the top coefficient of p is one",
									"p(card(S)) = R.one",
									pDegree.RwRev(),
									By(e.Unfolded(pMonic, polynomial.PolynomialMonicDef)))
								qTop := e.Have(
									"the top coefficient of q is one",
									"q(card(S)) = R.one",
									qDegree.RwRev(),
									By(e.Unfolded(qMonic, polynomial.PolynomialMonicDef)))
								e.Show(
									"one minus one is zero",
									pTop.Rw(),
									qTop.Rw(),
									ByArith(ring, comm_ring.OneIn.Read(ring)))
							}))
					})
				b.Otherwise(
					"past card(S) both coefficients vanish",
					func(c *Argument, away Fact) {
						beyond := c.Have(
							"i is past the degree of each",
							"suc(card(S)) ≤ i",
							ByArith(past, away))
						pGone := c.Have(
							"the coefficient of p vanishes",
							"p(i) = R.zero",
							By(
								beyond,
								pDegree,
								polynomial.DegreeVec.At(zero, carrier, p),
								pOver,
								At(vec_space.VecDef, zero, c.TermAs[Nat]("suc(polynomial_degree(p))"), p)))
						qGone := c.Have(
							"the coefficient of q vanishes",
							"q(i) = R.zero",
							By(
								beyond,
								qDegree,
								polynomial.DegreeVec.At(zero, carrier, q),
								qOver,
								At(vec_space.VecDef, zero, c.TermAs[Nat]("suc(polynomial_degree(q))"), q)))
						c.Show(
							"zero minus zero is zero",
							pGone.Rw(),
							qGone.Rw(),
							ByArith(ring, comm_ring.ZeroIn.Read(ring)))
					})
			}))
		differenceZero := arg.Have(
			"the difference vanishes",
			"d = vec_zero",
			Derive(func(b *Argument) {
				nonzero := b.SupposeNot()
				degreeBelow := b.Have(
					"so its degree is below card(S)",
					"polynomial_degree(d) < card(S)",
					By(dBelow, nonzero, At(polynomial.DegreeBelow, zero, d, b.TermAs[Nat]("card(S)"))))
				bound := b.Have(
					"the roots of the difference are finite and at most its degree",
					"finite(polynomial_roots(R.carrier, d)) ∧ "+
						"card(polynomial_roots(R.carrier, d)) ≤ polynomial_degree(d)",
					By(dOver, nonzero, RootBound.Read(domain).AsFact().At(d)))
				rootsCover := b.Have(
					"S lies among the roots of the difference",
					"S ⊆ polynomial_roots(R.carrier, d)",
					Derive(func(c *Argument) {
						c.Do(Simp(Fwd(PolynomialRootsDef)))
						c.Do(Unfold(set_basic.SubsetDef))
						r := c.FixAs[A]("r")
						rIn := c.Assume()
						rInR := c.Have(
							"r lies in R",
							"r ∈ R.carrier",
							BySets(rIn, inR))
						value := c.Have(
							"the difference vanishes at r",
							"polynomial_eval(d, r) = R.zero",
							dDef.Rw(),
							GroupPremises(
								pOver, qOver, rInR, polynomial_evaluation.EvalSub.Read(ring).AsFact().At(p, q, r)).Rw(),
							GroupPremises(rIn, pVanishes.At(r)).Rw(),
							GroupPremises(rIn, qVanishes.At(r)).Rw(),
							ByArith(ring, comm_ring.ZeroIn.Read(ring)))
						c.Show(
							"p and q agree at r",
							By(rInR, value))
					}))
				count := b.Have(
					"so card(S) is at most the number of those roots",
					"card(S) ≤ card(polynomial_roots(R.carrier, d))",
					By(
						bound,
						rootsCover,
						cardinality.CardSubset.At(S, b.TermAs[Set[A]]("polynomial_roots(R.carrier, d)"))))
				b.Show(
					"which is at most the degree of d, below card(S)",
					ByArith(degreeBelow, bound, count))
			}))
		arg.Do(Funext())
		i := arg.FixAs[Nat]("i")
		coefficients := arg.Have(
			"the coefficients of p and q at i lie in R",
			"p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
			By(polynomial.CoefficientIn.Read(pOver).At(i), polynomial.CoefficientIn.Read(qOver).At(i)))
		difference := arg.Have(
			"their difference at i is zero",
			"p(i) - q(i) = R.zero",
			Derive(func(b *Argument) {
				atI := b.Have(
					"read the difference at i",
					"d(i) = R.zero",
					differenceZero.Rw(),
					Simp(Fwd(vec_space.VecZeroDef)),
					Basic())
				b.Show(
					"d is the coefficientwise difference",
					By(atI, dDef, vec_space.VecSubDef))
			}))
		arg.Show(
			"so p and q have one coefficient at i",
			ByArith(ring, coefficients, difference))
	}),
})}

// MonicVanishingFixed — an endomorphism e of a domain that maps the finite
// set S onto itself fixes the monic polynomial g of degree card(S)
// vanishing on S: moved along e, g is again monic of that degree and
// vanishes on S, and such a polynomial is unique.
var MonicVanishingFixed = monicVanishingFixedThm{family.Add(registry.ProofEntry{
	Name: "MonicVanishingFixed",
	Key:  "prop_e2f2619b065b501b",
	Build: integral_domain.IntegralDomainOn.Law(Statement{
		Binders: "∀S:set(A). ∀e:(A → A). ∀g:(num → A).",
		Hypotheses: []string{
			"ring_homomorphism(R, R, e)",
			"finite(S)",
			"S ⊆ R.carrier",
			"∀r:A. r ∈ S ⇒ ∃y:A. y ∈ S ∧ e(y) = r",
			"polynomial_over(R.carrier, g)",
			"polynomial_monic(g)",
			"polynomial_degree(g) = card(S)",
			"∀r:A. r ∈ S ⇒ polynomial_eval(g, r) = R.zero",
		},
		Conclusion: "(λi:num. e(g(i))) = g",
	}, func(
		arg *Argument,
		domain integral_domain.IntegralDomainFact[on.R],
		S *Expr[Set[A]],
		e *Arrow[A, A],
		g *Arrow[Nat, A],
		hom, finiteS, inR, onto, over, monic, degree, vanishes Fact,
	) {
		zero := arg.TermAs[A]("R.zero")
		carrier := arg.TermAs[Set[A]]("R.carrier")
		R := arg.TermAs[RingOps[A]]("R")
		moved := arg.TermAs[Fun[Nat, A]]("λi:num. e(g(i))")
		n := arg.TermAs[Nat]("polynomial_degree(g)")
		keepsZero := ring_homomorphism.MapZero.Read(hom)
		movedOver := arg.Have(
			"the moved polynomial is over R",
			"polynomial_over(R.carrier, λi:num. e(g(i)))",
			By(
				over,
				keepsZero,
				ring_homomorphism.MapIn.Read(hom),
				polynomial.PolynomialOverMap.At(e, zero, zero, carrier, carrier, g)))
		leading := arg.Have(
			"its coefficient at the degree of g is one",
			"e(g(polynomial_degree(g))) = R.one",
			arg.Unfolded(monic, polynomial.PolynomialMonicDef).Rw(),
			By(ring_homomorphism.MapOne.Read(hom)))
		movedDegree := arg.Have(
			"so it has the degree of g",
			"polynomial_degree(λi:num. e(g(i))) = polynomial_degree(g)",
			By(
				movedOver,
				over,
				keepsZero,
				leading,
				integral_domain.OneNotZero.Read(domain),
				polynomial.DegreeVec.At(zero, carrier, g),
				At(polynomial.VecMap, e, zero, zero, arg.TermAs[Nat]("suc(polynomial_degree(g))"), g),
				polynomial.DegreeExact.At(zero, carrier, moved, n)))
		movedMonic := arg.Have(
			"and it is monic",
			"polynomial_monic(λi:num. e(g(i)))",
			Unfold(polynomial.PolynomialMonicDef),
			movedDegree.Rw(),
			By(leading))
		movedVanishes := arg.Have(
			"it vanishes on S, each point of S being a moved point of S",
			"∀r:A. r ∈ S ⇒ polynomial_eval(λi:num. e(g(i)), r) = R.zero",
			Derive(func(b *Argument) {
				r := b.FixAs[A]("r")
				rInS := b.Assume()
				y, preimage := b.UnpackAs[A](GroupPremises(rInS, onto.At(r)), "y")
				parts := b.Conjuncts(
					preimage,
					"y lies in S",
					"e moves y to r")
				yIn := b.Have(
					"y lies in R",
					"y ∈ R.carrier",
					BySets(parts[0], inR))
				along := b.Have(
					"e moves the value of g at y to the value of the moved polynomial at r",
					"e(polynomial_eval(g, y)) = polynomial_eval(λi:num. e(g(i)), e(y))",
					By(hom, over, yIn, polynomial_evaluation.EvalAlongHomomorphism.At(R, R, e, g, y)))
				b.Show(
					"and g vanishes at y",
					parts[1].RwRev(),
					along.RwRev(),
					GroupPremises(parts[0], vanishes.At(y)).Rw(),
					By(keepsZero))
			}))
		arg.Show(
			"such a polynomial is unique",
			By(
				finiteS,
				inR,
				movedOver,
				over,
				movedMonic,
				monic,
				degree,
				movedDegree,
				movedVanishes,
				vanishes,
				At(Read(MonicVanishingUnique, domain), S, moved, g)))
	}),
})}
