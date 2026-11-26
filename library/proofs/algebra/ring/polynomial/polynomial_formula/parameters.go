// parameters.go — the ring of integer polynomials and its operations; the
// parameter ring, the polynomials on U, a subring and the polynomial algebra
// on U; and their specialization at an environment of a commutative ring,
// which carries a univariate polynomial over the parameters to one over the
// ring, coefficient by coefficient through the homomorphism
// IntegerPolynomialEvalHom.

package polynomial_formula

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// IntegerPolynomialRingOperations — the integer polynomial ring operates as
// the polynomial algebra over the integers: it adds coefficientwise, its zero
// is the zero function, and its product and one are those of the polynomial
// algebra; it is that algebra on all the variables.
var IntegerPolynomialRingOperations = integerPolynomialRingOperationsThm{family.Add(registry.ProofEntry{
	Name: "IntegerPolynomialRingOperations",
	Key:  "prop_f535ad37ea8b041d",
	Build: family.Theorem("integer_polynomial_ring.add = fun_add(int_add) ∧ "+
		"integer_polynomial_ring.zero = fun_zero(int_of_num(0)) ∧ "+
		"integer_polynomial_ring.mul = polynomial_algebra_mul(int_ring) ∧ "+
		"integer_polynomial_ring.one = polynomial_algebra_one(int_ring)",
		func(a *Argument) {
			a.Show(
				"the integer polynomial ring is the polynomial "+
					"algebra over the integers, whose operations these are",
				Simp(Fwd(IntegerPolynomialRingDef), Fwd(polynomial_algebra.PolynomialAlgebraRingDef)),
				Basic())
		}),
})}

// ParameterRing — the ring of integer polynomials restricted to the
// polynomials on U is the polynomial algebra on U: the integer polynomial
// ring is the polynomial algebra on all the variables, and restricting it to
// the polynomials on U keeps its operations.
var ParameterRing = parameterRingThm{family.Add(registry.ProofEntry{
	Name: "ParameterRing",
	Key:  "prop_18882ec01c095217",
	Build: family.Theorem("∀U:set(num). «parameterRing»(U) = polynomial_algebra_ring(int_ring, U)",
		func(a *Argument, U *Expr[Set[Nat]]) {
			a.Show(
				"the integer polynomial ring is the polynomial algebra "+
					"on all the variables, which restricts to the algebra on U",
				Simp(Fwd(IntegerPolynomialRingDef)),
				By(polynomial_algebra.PolynomialAlgebraRingRestrictVariables.At(
					a.TermAs[RingOps[Int]]("int_ring"), U)))
		}),
})}

// ParameterRingCommutative — the parameter ring is a commutative ring, the
// polynomial algebra on U over the integers.
var ParameterRingCommutative = parameterRingCommutativeThm{family.Add(registry.ProofEntry{
	Name: "ParameterRingCommutative",
	Key:  "prop_9417947fdd15bfd9",
	Build: family.Theorem("∀U:set(num). comm_ring_on(«parameterRing»(U))",
		func(a *Argument, U *Expr[Set[Nat]]) {
			a.Show(
				"the polynomial algebra over the commutative ring of the integers is commutative",
				By(ParameterRing, polynomial_algebra.PolynomialAlgebraCommRingOn, int_real_lift.CommRingOn))
		}),
})}

// ParameterPolynomialsSubring — the polynomials on U form a subring of the
// integer polynomials: they lie among the polynomials on all the variables,
// and the ring of all integer polynomials restricted to them is the
// parameter ring, a commutative one.
var ParameterPolynomialsSubring = parameterPolynomialsSubringThm{family.Add(registry.ProofEntry{
	Name: "ParameterPolynomialsSubring",
	Key:  "prop_7e1a55c18d0c58c1",
	Reading: "U may be empty, which leaves the constant integer polynomials, or infinite. The " +
		"polynomials on U are the integer polynomials whose variables lie in U (PolynomialOnVariables).",
	Build: family.Theorem("∀U:set(num). "+
		"    subring(integer_polynomial_ring, polynomial_algebra(int_ring, U))",
		func(a *Argument, U *Expr[Set[Nat]]) {
			integers := a.TermAs[RingOps[Int]]("int_ring")
			everywhere := a.TermAs[Set[Nat]]("𝕌")
			ring := a.Have(
				"the integer polynomials form a commutative ring",
				"comm_ring_on(integer_polynomial_ring)",
				Simp(Fwd(IntegerPolynomialRingDef)),
				By(
					int_real_lift.CommRingOn,
					polynomial_algebra.PolynomialAlgebraCommRingOn.At(integers, everywhere)))
			inside := a.Have(
				"the polynomials on U are among those on all the variables",
				"polynomial_algebra(int_ring, U) ⊆ integer_polynomial_ring.carrier",
				Simp(Fwd(IntegerPolynomialRingDef)),
				By(polynomial_algebra.PolynomialAlgebraSubset.At(integers, U, everywhere), set_order.SubsetUniv))
			a.Show(
				"a part of the carrier on which the ring restricts to a commutative ring is a subring",
				By(
					inside,
					ParameterRingCommutative.At(U),
					comm_ring.SubringRingOn.Read(ring).At(
						a.TermAs[Set[IntegerPolynomial]]("polynomial_algebra(int_ring, U)"))))
		}),
})}

// ParameterPolynomialsSumIn — a finite sum of polynomials on U is a
// polynomial on U: the polynomials on U are a commutative ring under the
// integer polynomials' addition and zero, and a fold of members of its
// additive monoid over a finite index set is a member.
var ParameterPolynomialsSumIn = parameterPolynomialsSumInThm{family.Add(registry.ProofEntry{
	Name: "ParameterPolynomialsSumIn",
	Key:  "prop_fa235f218a08052c",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀s:set(D). ∀p:(D → ((num → num) → int)).",
		Hypotheses: []string{
			"finite(s)",
			"∀j:D. j ∈ s ⇒ p(j) ∈ polynomial_algebra(int_ring, U)",
		},
		Conclusion: "module_sum(integer_polynomial_ring.add, integer_polynomial_ring.zero, s, p) ∈ " +
			"polynomial_algebra(int_ring, U)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		s *Expr[Set[D]],
		p *Arrow[D, IntegerPolynomial],
		finiteIndex, members Fact,
	) {
		parameters := a.Have(
			"the polynomials on U form a commutative ring",
			"comm_ring_on(«parameterRing»(U))",
			Cite(ParameterRingCommutative, U))
		a.Show(
			"its addition and zero are the integer polynomials', and "+
				"a fold of its members over a finite index set is a member",
			By(
				finiteIndex,
				members,
				module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(parameters)).At(s, p)))
	}),
})}

// SpecializedPolynomial — a univariate polynomial over the parameters
// specializes, coefficient by coefficient, to a polynomial over the ring:
// the specialization keeps zero and sends parameters into the ring.
var SpecializedPolynomial = specializedPolynomialThm{family.Add(registry.ProofEntry{
	Name: "SpecializedPolynomial",
	Key:  "prop_a01d39f6ca627863",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀R:ring_ops(A). ∀ρ:(num → A). ∀g:(num → ((num → num) → int)).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, U, ρ)",
			"«overParameters»(g)",
		},
		Conclusion: "polynomial_over(R.carrier, «specialized»(R, ρ, g))",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		R *Expr[RingOps[A]],
		ring comm_ring.CommRingFact[on.R],
		ρ *Arrow[Nat, A],
		g *Arrow[Nat, IntegerPolynomial],
		environment, over Fact,
	) {
		specialization := a.Have(
			"specialization at ρ is a ring homomorphism",
			"ring_homomorphism(«parameterRing»(U), "+
				"    R, "+
				"    λq:((num → num) → int). integer_polynomial_eval(R, ρ, q))",
			By(environment, IntegerPolynomialEvalHom.Read(ring).At(U, ρ)))
		a.Show(
			"it keeps zero and sends parameters into R, so it maps g to a polynomial over R",
			By(
				over,
				polynomial.PolynomialOverMap,
				ring_homomorphism.MapZero.Read(specialization),
				ring_homomorphism.MapIn.Read(specialization)))
	}),
})}

// SpecializedDerivative — specializing the parameters commutes with the
// formal derivative: coefficient by coefficient, the derivative's
// coefficient at j is the numeral j + 1 times g(j + 1), and specialization
// is a ring homomorphism, which keeps the product and sends the numeral to
// the same numeral of R.
var SpecializedDerivative = specializedDerivativeThm{family.Add(registry.ProofEntry{
	Name: "SpecializedDerivative",
	Key:  "prop_6d7dc1c9ead04d04",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀R:ring_ops(A). ∀ρ:(num → A). ∀g:(num → ((num → num) → int)).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, U, ρ)",
			"«overParameters»(g)",
		},
		Conclusion: "«specialized»(R, " +
			"    ρ, " +
			"    polynomial_derivative(integer_polynomial_ring.add, " +
			"        integer_polynomial_ring.zero, " +
			"        integer_polynomial_ring.mul, " +
			"        integer_polynomial_ring.one, " +
			"        g)) = " +
			"polynomial_derivative(«specialized»(R, ρ, g))",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		R *Expr[RingOps[A]],
		ring comm_ring.CommRingFact[on.R],
		ρ *Arrow[Nat, A],
		g *Arrow[Nat, IntegerPolynomial],
		environment, over Fact,
	) {
		specialization := a.Have(
			"specialization at ρ is a ring homomorphism",
			"ring_homomorphism(«parameterRing»(U), "+
				"    R, "+
				"    λq:((num → num) → int). integer_polynomial_eval(R, ρ, q))",
			By(environment, IntegerPolynomialEvalHom.Read(ring).At(U, ρ)))
		parameters := a.Have(
			"the parameter polynomials form a commutative ring",
			"comm_ring_on(«parameterRing»(U))",
			Cite(ParameterRingCommutative, U))
		a.Do(Funext())
		a.FixAs[Nat]("j")
		next := a.TermAs[Nat]("suc(j)")
		numeral := a.TermAs[IntegerPolynomial](
			"monoid_pow(integer_polynomial_ring.add, " +
				"    integer_polynomial_ring.zero, " +
				"    integer_polynomial_ring.one, " +
				"    suc(j))")
		inParameters := a.Have(
			"the numeral j + 1 and the coefficient g(j + 1) are parameter polynomials",
			"monoid_pow(integer_polynomial_ring.add, "+
				"    integer_polynomial_ring.zero, "+
				"    integer_polynomial_ring.one, "+
				"    suc(j)) ∈ "+
				"polynomial_algebra(int_ring, U) ∧ "+
				"g(suc(j)) ∈ polynomial_algebra(int_ring, U)",
			By(
				polynomial.CoefficientIn.Read(over).At(next),
				comm_ring.OneIn.Read(parameters),
				comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(parameters)).AsFact().At(
					a.TermAs[IntegerPolynomial]("integer_polynomial_ring.one"), next)))
		a.Show(
			"the derivative's coefficient at j is the numeral j + 1 times g(j "+
				"+ 1), and specialization keeps both the product and the numeral",
			Simp(Fwd(polynomial.PolynomialDerivativeDef)),
			By(
				inParameters,
				ring_homomorphism.MapMul.Read(specialization).AsFact().At(numeral, g.Apply(next)),
				ring_homomorphism.RingMapNumeral.Read(specialization).At(next)))
	}),
})}

// SpecializedDegree — where the leading coefficient of a univariate
// polynomial over the parameters specializes to a nonzero element, the
// specialized polynomial keeps the degree: it is a polynomial over the
// ring, it vanishes past the degree of g, as g does and the specialization
// keeps zero, and it is nonzero there.
var SpecializedDegree = specializedDegreeThm{family.Add(registry.ProofEntry{
	Name: "SpecializedDegree",
	Key:  "prop_513bfe4077d818bc",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀R:ring_ops(A). ∀ρ:(num → A). ∀g:(num → ((num → num) → int)).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, U, ρ)",
			"«overParameters»(g)",
			"integer_polynomial_eval(R, ρ, g(polynomial_degree(integer_polynomial_ring.zero, g))) ≠ R.zero",
		},
		Conclusion: "polynomial_degree(«specialized»(R, ρ, g)) = " +
			"polynomial_degree(integer_polynomial_ring.zero, g)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		R *Expr[RingOps[A]],
		ring comm_ring.CommRingFact[on.R],
		ρ *Arrow[Nat, A],
		g *Arrow[Nat, IntegerPolynomial],
		environment, over, leading Fact,
	) {
		specialization := a.Have(
			"specialization at ρ is a ring homomorphism",
			"ring_homomorphism(«parameterRing»(U), "+
				"    R, "+
				"    λq:((num → num) → int). integer_polynomial_eval(R, ρ, q))",
			By(environment, IntegerPolynomialEvalHom.Read(ring).At(U, ρ)))
		zero := a.TermAs[IntegerPolynomial]("integer_polynomial_ring.zero")
		evaluation := a.TermAs[Fun[IntegerPolynomial, A]](
			"λq:((num → num) → int). integer_polynomial_eval(R, ρ, q)")
		degreeVec := a.Have(
			"g vanishes past its degree",
			"vec⟨suc(polynomial_degree(integer_polynomial_ring.zero, g))⟩(integer_polynomial_ring.zero, g)",
			By(
				over,
				polynomial.DegreeVec.At(
					zero, a.TermAs[Set[IntegerPolynomial]]("polynomial_algebra(int_ring, U)"), g)))
		// VecMap reads g as a vector of length suc(deg g), the length its vanishing fact holds it at.
		vanishes := a.Have(
			"so does its specialization, which keeps zero",
			"vec⟨suc(polynomial_degree(integer_polynomial_ring.zero, g))⟩(R.zero, «specialized»(R, ρ, g))",
			By(
				ring_homomorphism.MapZero.Read(specialization),
				polynomial.VecMap.At(evaluation, zero, a.TermAs[A]("R.zero"), proof.InhabitFrom(g, degreeVec))))
		specialized := a.Have(
			"and the specialization is a polynomial over R",
			"polynomial_over(R.zero, R.carrier, «specialized»(R, ρ, g))",
			By(environment, over, SpecializedPolynomial.Read(ring).At(U, ρ, g)))
		a.Show(
			"nonzero at the degree of g, it has the degree of g",
			By(
				specialized,
				vanishes,
				leading,
				polynomial.DegreeExact.At(
					a.TermAs[A]("R.zero"),
					a.TermAs[Set[A]]("R.carrier"),
					a.TermAs[Fun[Nat, A]]("«specialized»(R, ρ, g)"),
					a.TermAs[Nat]("polynomial_degree(integer_polynomial_ring.zero, g)"))))
	}),
})}

// SpecializedTruncation — where the leading coefficient of a univariate
// polynomial g over the parameters specializes to zero, g specializes as its
// truncation below its degree, which keeps every coefficient of g below the
// degree and puts zero at the degree and past it: there the specialization
// sends g to zero, the leading coefficient by hypothesis and the rest as the
// zero it keeps.
var SpecializedTruncation = specializedTruncationThm{family.Add(registry.ProofEntry{
	Name: "SpecializedTruncation",
	Key:  "prop_2075d996b118396e",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀R:ring_ops(A). ∀ρ:(num → A). ∀g:(num → ((num → num) → int)).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, U, ρ)",
			"«overParameters»(g)",
			"integer_polynomial_eval(R, ρ, g(polynomial_degree(integer_polynomial_ring.zero, g))) = R.zero",
		},
		Conclusion: "«specialized»(R, " +
			"    ρ, " +
			"    λi:num. " +
			"        COND(i < polynomial_degree(integer_polynomial_ring.zero, g), " +
			"            g(i), " +
			"            integer_polynomial_ring.zero)) = " +
			"«specialized»(R, ρ, g)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		R *Expr[RingOps[A]],
		ring comm_ring.CommRingFact[on.R],
		ρ *Arrow[Nat, A],
		g *Arrow[Nat, IntegerPolynomial],
		environment, over, leading Fact,
	) {
		specialization := a.Have(
			"specialization at ρ is a ring homomorphism",
			"ring_homomorphism(«parameterRing»(U), "+
				"    R, "+
				"    λq:((num → num) → int). integer_polynomial_eval(R, ρ, q))",
			By(environment, IntegerPolynomialEvalHom.Read(ring).At(U, ρ)))
		a.Show(
			"below the degree the truncation is g, and from the degree on both specialize to zero",
			By(
				Where(
					polynomial.TruncationImage,
					"σ",
					a.TermAs[Fun[IntegerPolynomial, A]]("λu:((num → num) → int). integer_polynomial_eval(R, ρ, u)")),
				over,
				ring_homomorphism.MapZero.Read(specialization),
				leading))
	}),
})}
