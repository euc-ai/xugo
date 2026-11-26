package multilinear_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// SquarefreeExponentSupport recovers a set of variables from its zero-one exponent vector.
var SquarefreeExponentSupport = squarefreeExponentSupportThm{family.Add(registry.ProofEntry{
	Name: "SquarefreeExponentSupport",
	Key:  "prop_87019a390e1d790",
	Build: family.Theorem("∀T:set(B). fun_support(0, squarefree_exponent(T)) = T",
		Chain(Unfold(squarefreeExponentDef), BySets(nat_arith.OneNotZero))),
})}

// SquarefreeMonomialEval computes a squarefree monomial at a Boolean cube point.
// If one of its variables is missing the product lies in the zero ideal.
var SquarefreeMonomialEval = squarefreeMonomialEvalThm{family.Add(registry.ProofEntry{
	Name: "SquarefreeMonomialEval",
	Key:  "prop_5df5af27f0422473",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀T X:set(B).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite(T)",
		},
		Conclusion: "monomial_eval(R, cube_ring_point(R, X), squarefree_exponent(T)) = " +
			"COND(T ⊆ X, R.one, R.zero)",
		Abbrev: Abbrev{
			{Name: "powers", Text: "λy:B. " +
				"    monoid_pow(R.mul, R.one, cube_ring_point(R, X, y), squarefree_exponent(T, y))"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T, X *Expr[Set[B]],
		ring comm_ring.CommRingFact[on.R],
		finite Fact,
	) {
		point := a.TermAs[Fun[B, A]]("cube_ring_point(R, X)")
		exponent := a.TermAs[Fun[B, Nat]]("squarefree_exponent(T)")
		values := a.Have(
			"each coordinate of the cube point lies in the carrier",
			"∀y:B. cube_ring_point(R, X, y) ∈ R.carrier",
			By(At(cubeRingPointDef, R, X), comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
		a.Cases(a.Term("T ⊆ X"))
		a.When(
			"all variables in the monomial are present",
			func(b *Argument, inside Fact) {
				ones := b.Have(
					"both the coordinate and its exponent equal one on T",
					"∀y:B. y ∈ T ⇒ cube_ring_point(R, X, y) = R.one ∧ squarefree_exponent(T, y) = 1",
					BySets(inside, At(cubeRingPointDef, R, X), At(squarefreeExponentDef, T)))
				factors := b.Have(
					"each factor is one",
					"∀y:B. y ∈ T ⇒ «powers»(y) = R.one",
					By(
						Normalized,
						ones,
						comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(
							b.MemberOf[on.R](b.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring)))))
				product := b.Have(
					"a finite product of ones is one",
					"module_sum(R.mul, R.one, T, «powers») = R.one",
					By(
						finite,
						factors,
						module.ModuleSumIdentityMonoid.Read(comm_ring.MulMonoidOn.Read(ring)).At(
							T, b.TermAs[Fun[B, A]]("«powers»"))))
				b.Do(Unfold(polynomial_algebra_evaluation.MonomialEvalDef), By(
					inside,
					SquarefreeExponentSupport.At(T),
					product))
			})
		a.Otherwise(
			"a missing variable supplies a zero factor",
			func(b *Argument, outside Fact) {
				monomial := b.Have(
					"the exponent is a monomial in the variables of T",
					"squarefree_exponent(T) ∈ monomials(T)",
					By(
						Normalized,
						finite,
						SquarefreeExponentSupport.At(T),
						polynomial_algebra.MonomialsMember.At(T, exponent),
						set_order.SubsetRefl.At(T)))
				y, missing := b.ObtainAs[B](
					"a variable of T missing from X",
					"∃y:B. y ∈ T ∧ y ∉ X",
					BySets(outside))
				zeroFactor := b.Have(
					"its exponent is nonzero and its coordinate belongs to the zero ideal",
					"squarefree_exponent(T, y) ≠ 0 ∧ cube_ring_point(R, X, y) ∈ {R.zero}",
					BySets(missing, cubeRingPointDef.At(R, X, y), squarefreeExponentDef.At(T, y), nat_arith.OneNotZero))
				zero := b.Have(
					"the entire monomial belongs to the zero ideal",
					"monomial_eval(R, cube_ring_point(R, X), squarefree_exponent(T)) ∈ {R.zero}",
					By(
						ring,
						values,
						monomial,
						zeroFactor,
						ring_ideal.ZeroIdeal.Read(ring),
						polynomial_algebra_evaluation.MonomialEvalInIdeal.At(
							R, T, b.TermAs[Set[A]]("{R.zero}"), point, exponent, y)))
				b.Show(
					"membership in the zero ideal gives the required value",
					BySets(outside, zero))
			})
	}),
})}

// SquarefreePolynomialCoefficient reads the original coefficient at its exponent vector.
var SquarefreePolynomialCoefficient = squarefreePolynomialCoefficientThm{family.Add(registry.ProofEntry{
	Name: "SquarefreePolynomialCoefficient",
	Key:  "prop_e986566101d60a05",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀U T:set(B). ∀c:(set(B) → A).",
		Hypotheses: []string{"T ⊆ U"},
		Conclusion: "squarefree_polynomial(R, U, c, squarefree_exponent(T)) = c(T)",
	}, func(a *Argument, R *Expr[RingOps[A]], U, T *Expr[Set[B]], c *Arrow[Set[B], A], within Fact) {
		indexed := a.Have(
			"T indexes one of the squarefree monomials",
			"squarefree_exponent(T) ∈ image(squarefree_exponent, {Y:set(B) | Y ⊆ U})",
			BySets(within))
		a.Do(Unfold(SquarefreePolynomialDef), By(indexed, SquarefreeExponentSupport.At(T)))
	}),
})}

// SquarefreePolynomialSupport confines every nonzero coefficient to a squarefree monomial of U.
var SquarefreePolynomialSupport = squarefreePolynomialSupportThm{family.Add(registry.ProofEntry{
	Name: "SquarefreePolynomialSupport",
	Key:  "prop_de188d176a5e448e",
	Build: family.Theorem(
		"∀R:ring_ops(A). ∀U:set(B). ∀c:(set(B) → A). "+
			"    fun_support(R.zero, squarefree_polynomial(R, U, c)) ⊆ "+
			"    image(squarefree_exponent, {T:set(B) | T ⊆ U})",
		Chain(Unfold(SquarefreePolynomialDef), BySets())),
})}

// SquarefreeMonomials embeds the subsets of a finite variable set into its monomials.
var SquarefreeMonomials = squarefreeMonomialsThm{family.Add(registry.ProofEntry{
	Name: "SquarefreeMonomials",
	Key:  "prop_186a9d3011cdf862",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(B).",
		Hypotheses: []string{"finite(U)"},
		Conclusion: "image(squarefree_exponent, {T:set(B) | T ⊆ U}) ⊆ monomials(U)",
	},
		func(a *Argument, U *Expr[Set[B]], finite Fact) {
			indexed := a.Have(
				"the exponent is supported on the finite subset that indexes it",
				"∀T:set(B). T ⊆ U ⇒ squarefree_exponent(T) ∈ monomials(U)",
				By(finite, finite_set.FiniteSubset, SquarefreeExponentSupport, polynomial_algebra.MonomialsMember))
			a.Do(BySets(indexed))
		}),
})}

// SquarefreePolynomialIn places the subset-indexed coefficients in the ordinary polynomial algebra.
var SquarefreePolynomialIn = squarefreePolynomialInThm{family.Add(registry.ProofEntry{
	Name: "SquarefreePolynomialIn",
	Key:  "prop_9c094362cde0d2f5",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀U:set(B). ∀c:(set(B) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite(U)",
			"∀T:set(B). T ⊆ U ⇒ c(T) ∈ R.carrier",
		},
		Conclusion: "squarefree_polynomial(R, U, c) ∈ polynomial_algebra(R, U)",
		Abbrev: Abbrev{
			{Name: "indices", Text: "image(squarefree_exponent, {T:set(B) | T ⊆ U})"},
			{Name: "support", Text: "fun_support(R.zero, squarefree_polynomial(R, U, c))"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			U *Expr[Set[B]],
			c *Arrow[Set[B], A],
			ring comm_ring.CommRingFact[on.R],
			finite, values Fact,
		) {
			indices := a.TermAs[Set[Fun[B, Nat]]]("«indices»")
			supportInIndices := SquarefreePolynomialSupport.At(R, U, c)
			finiteIndices := a.Have(
				"there are finitely many squarefree indices",
				"finite(«indices»)",
				By(
					finite,
					finite_set.FinitePowerset.At(U),
					finite_set.FiniteImage.At(
						a.TermAs[Fun[Set[B], Fun[B, Nat]]]("squarefree_exponent"),
						a.TermAs[Set[Set[B]]]("{T:set(B) | T ⊆ U}"))))
			finiteSupport := a.Have(
				"the polynomial has finite support",
				"finite(«support»)",
				By(
					finiteIndices,
					supportInIndices,
					finite_set.FiniteSubset.At(a.TermAs[Set[Fun[B, Nat]]]("«support»"), indices)))
			monomials := a.Have(
				"all nonzero coefficients index monomials of U",
				"«support» ⊆ monomials(U)",
				By(finite, supportInIndices, SquarefreeMonomials.At(U), set_order.SubsetTrans))
			variables := a.Have(
				"the variables of every squarefree index lie in U",
				"∀m:(B → num). m ∈ «indices» ⇒ fun_support(0, m) ⊆ U",
				BySets(SquarefreeExponentSupport))
			coeff := a.Have(
				"each coefficient is either a specified ring value or zero",
				"∀m:(B → num). squarefree_polynomial(R, U, c, m) ∈ R.carrier",
				Derive(func(b *Argument) {
					b.FixAs[Fun[B, Nat]]("m")
					b.Do(Unfold(SquarefreePolynomialDef), By(values, variables, comm_ring.ZeroIn.Read(ring)))
				}))
			a.Do(By(
				finiteSupport,
				coeff,
				monomials,
				polynomial_algebra.PolynomialAlgebraMember.At(
					R, U, a.TermAs[Fun[Fun[B, Nat], A]]("squarefree_polynomial(R, U, c)"))))
		}),
})}

// SquarefreePolynomialEval identifies the ordinary polynomial evaluation at the
// indicator of X with the subset sum. Reindex by variable sets and remove the
// monomials containing a variable outside X, whose value is zero.
var SquarefreePolynomialEval = squarefreePolynomialEvalThm{family.Add(registry.ProofEntry{
	Name: "SquarefreePolynomialEval",
	Key:  "prop_a3082621532ca323",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀U X:set(B). ∀c:(set(B) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite(U)",
			"X ⊆ U",
			"∀T:set(B). T ⊆ U ⇒ c(T) ∈ R.carrier",
		},
		Conclusion: "polynomial_algebra_eval(R, " +
			"    R, " +
			"    λv:A. v, " +
			"    cube_ring_point(R, X), " +
			"    squarefree_polynomial(R, U, c)) = " +
			"multilinear_eval(R, c, X)",
		Abbrev: Abbrev{
			{Name: "subsetsOf", Text: "λV:set(B). {T:set(B) | T ⊆ V}"},
			{Name: "indices", Text: "image(squarefree_exponent, «subsetsOf»(U))"},
			{Name: "termAt", Text: "λm:(B → num). " +
				"    squarefree_polynomial(R, U, c, m) * monomial_eval(R, cube_ring_point(R, X), m)"},
			{Name: "termOn", Text: "λT:set(B). «termAt»(squarefree_exponent(T))"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		U, X *Expr[Set[B]],
		c *Arrow[Set[B], A],
		ring comm_ring.CommRingFact[on.R],
		finite, within, values Fact,
	) {
		exponent := a.TermAs[Fun[Set[B], Fun[B, Nat]]]("squarefree_exponent")
		point := a.TermAs[Fun[B, A]]("cube_ring_point(R, X)")
		poly := a.TermAs[Fun[Fun[B, Nat], A]]("squarefree_polynomial(R, U, c)")
		indices := a.TermAs[Set[Fun[B, Nat]]]("«indices»")
		subsets := a.TermAs[Set[Set[B]]]("«subsetsOf»(U)")
		active := a.TermAs[Set[Set[B]]]("«subsetsOf»(X)")
		term := a.TermAs[Fun[Fun[B, Nat], A]]("«termAt»")
		onSet := a.TermAs[Fun[Set[B], A]]("«termOn»")
		finiteSubsets := a.Have(
			"the variable subsets form a finite index set",
			"finite(«subsetsOf»(U))",
			By(finite, finite_set.FinitePowerset.At(U)))
		finiteIndices := a.Have(
			"their exponent vectors form a finite set of monomials",
			"finite(«indices»)",
			By(finiteSubsets, finite_set.FiniteImage.At(exponent, subsets)))
		coords := a.Have(
			"the zero-one point takes ring values",
			"∀y:B. cube_ring_point(R, X, y) ∈ R.carrier",
			By(At(cubeRingPointDef, R, X), comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
		coeffs := a.Have(
			"all coefficients of the ordinary polynomial are ring values",
			"∀m:(B → num). squarefree_polynomial(R, U, c, m) ∈ R.carrier",
			By(
				ring,
				finite,
				values,
				SquarefreePolynomialIn.At(R, U, c),
				polynomial_algebra.PolynomialAlgebraMember.At(R, U, poly)))
		expansion := a.Have(
			"expand the polynomial over the squarefree monomials of U",
			"polynomial_algebra_eval(R, R, λv:A. v, cube_ring_point(R, X), squarefree_polynomial(R, U, c)) = "+
				"module_sum(R.add, R.zero, «indices», «termAt»)",
			By(
				finite,
				finiteIndices,
				coords,
				coeffs,
				SquarefreePolynomialSupport.At(R, U, c),
				SquarefreeMonomials.At(U),
				ring_homomorphism.RingHomIdentity.Read(ring),
				polynomial_algebra_evaluation.PolynomialAlgebraEvalOver.At(
					R, R, a.TermAs[Fun[A, A]]("λv:A. v"), point, U, indices, poly)))
		injection := a.Have(
			"a squarefree exponent vector determines its set of variables",
			"injective_on(«subsetsOf»(U), squarefree_exponent)",
			Derive(func(b *Argument) {
				b.Do(Unfold(functions.InjectiveOnDef))
				V := b.FixAs[Set[B]]("V")
				W := b.FixAs[Set[B]]("W")
				same := b.Assume()
				b.Do(By(same, SquarefreeExponentSupport.At(V), SquarefreeExponentSupport.At(W)))
			}))
		mask := a.Have(
			"only the monomials contained in X contribute their coefficients",
			"∀T:set(B). T ⊆ U ⇒ «termOn»(T) = COND(T ⊆ X, c(T), R.zero)",
			Derive(func(b *Argument) {
				T := b.FixAs[Set[B]]("T")
				inU := b.Assume()
				atPoint := b.Have(
					"the monomial evaluates to the subset test",
					"monomial_eval(R, cube_ring_point(R, X), squarefree_exponent(T)) = COND(T ⊆ X, R.one, R.zero)",
					By(ring, finite, inU, finite_set.FiniteSubset.At(T, U), SquarefreeMonomialEval.At(R, T, X)))
				atIndex := b.Have(
					"the coefficient of this exponent is c(T)",
					"squarefree_polynomial(R, U, c, squarefree_exponent(T)) = c(T)",
					By(inU, SquarefreePolynomialCoefficient.At(R, U, T, c)))
				b.Cases(b.Term("T ⊆ X"))
				b.When(
					"the coefficient is multiplied by one",
					func(d *Argument, inside Fact) {
						d.Do(ByArith(ring, values, inU, atPoint, atIndex, inside))
					})
				b.Otherwise(
					"the coefficient is multiplied by zero",
					func(d *Argument, outside Fact) {
						d.Do(ByArith(ring, values, inU, atPoint, atIndex, outside))
					})
			}))
		termsIn := a.Have(
			"each contribution lies in the ring",
			"∀T:set(B). T ∈ «subsetsOf»(U) ⇒ «termOn»(T) ∈ R.carrier",
			By(values, mask, comm_ring.ZeroIn.Read(ring)))
		reindex := a.Have(
			"sum by the set of variables of each monomial",
			"module_sum(R.add, R.zero, «indices», «termAt») = "+
				"module_sum(R.add, R.zero, «subsetsOf»(U), «termOn»)",
			By(
				finiteSubsets,
				injection,
				termsIn,
				module.ModuleSumImageMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(subsets, exponent, term)))
		withinU := a.Have(
			"every subset of X is a subset of U",
			"«subsetsOf»(X) ⊆ «subsetsOf»(U)",
			BySets(within))
		silent := a.Have(
			"the discarded terms vanish",
			"∀T:set(B). T ∈ «subsetsOf»(U) ∧ T ∉ «subsetsOf»(X) ⇒ «termOn»(T) = R.zero",
			BySets(mask))
		restrict := a.Have(
			"restrict the sum to subsets of X",
			"module_sum(R.add, R.zero, «subsetsOf»(U), «termOn») = "+
				"module_sum(R.add, R.zero, «subsetsOf»(X), «termOn»)",
			By(
				finiteSubsets,
				withinU,
				termsIn,
				silent,
				module.ModuleSumSupportMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(subsets, active, onSet)))
		retained := a.Have(
			"the surviving terms are the original coefficients",
			"∀T:set(B). T ∈ «subsetsOf»(X) ⇒ «termOn»(T) = c(T)",
			BySets(withinU, mask))
		sum := a.Have(
			"the restricted sum is the sum of those coefficients",
			"module_sum(R.add, R.zero, «subsetsOf»(X), «termOn») = "+
				"module_sum(R.add, R.zero, «subsetsOf»(X), c)",
			By(
				retained,
				module.ModuleSumCongruence.At(a.TermAs[Op[A]]("R.add"), a.TermAs[A]("R.zero"), active, onSet, c)))
		a.Do(Unfold(MultilinearEvalDef), By(restrict, reindex, expansion, sum))
	}),
})}
