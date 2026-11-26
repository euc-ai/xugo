// evaluation.go — evaluation at a point of the ring, a ring homomorphism
// from the polynomials over c to c, the values on the two sides of a
// division f = g q + r, the value of the binomial 1 - c x ^ d,
// the value at a scaled point read off the weighted coefficients,
// evaluation carried along a ring homomorphism, every polynomial as its
// own value at the variable, and the two orders of evaluating a polynomial
// in two variables; 1 - x times the geometric sum 1 + x + … + x ^ (d - 1)
// is 1 - x ^ d, the sum taking the value d at one; and a product of
// polynomials over a subfield is over it, nonzero with its factors, and
// takes the product of their values.

package polynomial_evaluation

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// EvalBelow — evaluation reads any segment past the support. The value
// is the sum of p(i) * x ^ i over the support of p, which for an
// n-vector lies among the indices below n; every term lies in c, and off
// the support a term is zero * x ^ i = zero, so the sum over the indices
// below n shrinks to the support.
var EvalBelow = evalBelowThm{family.Add(registry.ProofEntry{
	Name: "EvalBelow",
	Key:  "prop_325fc65e098f2d55",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"vec⟨n⟩(p)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, x) = " +
			"module_sum(R.add, R.zero, {i:num | i < n}, λi:num. p(i) * monoid_pow(R.mul, R.one, x, i))",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			n *Expr[Nat],
			p *Vec[A, DimN],
			x *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"vanishing from n on",
				"and x lies in c")
			over, vanishes, xIn := parts[0], parts[1], parts[2]
			coefficients := a.Have(
				"every coefficient of p lies in c",
				"∀i:num. p(i) ∈ R.carrier",
				By(over, polynomial.PolynomialOverDef))
			powers := a.Have(
				"and every power of x",
				"∀i:num. monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(xIn, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
			terms := a.Have(
				"so every term p(i) x ^ i lies in c",
				"∀i:num. p(i) * monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(coefficients, powers, comm_ring.MulIn.Read(ring)))
			pastN := a.Have(
				"p is zero at every index from n on",
				"∀i:num. n ≤ i ⇒ p(i) = R.zero",
				By(vanishes, vec_space.VecDef))
			nonzeroBelow := a.Have(
				"so p(i) ≠ zero only below n",
				"∀i:num. p(i) ≠ R.zero ⇒ i < n",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					nonzero := b.Assume()
					b.Show(
						"were n ≤ i, p(i) would be zero",
						By(nonzero, pastN.At(i), nat_order.NotLessEq.At(n, i)))
				}))
			inside := a.Have(
				"the support of p lies below n",
				"fun_support(R.zero, p) ⊆ {i:num | i < n}",
				BySets(nonzeroBelow))
			offSupport := a.Have(
				"off the support a term is zero",
				"∀i:num. i ∉ fun_support(R.zero, p) ⇒ p(i) * monoid_pow(R.mul, R.one, x, i) = R.zero",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					off := b.Assume()
					pZero := b.Have(
						"p vanishes at i",
						"p(i) = R.zero",
						BySets(off))
					b.Show(
						"and zero times the power x ^ i, a member of c, is zero",
						pZero.Rw(),
						By(comm_ring.MulLeftZeroOn.Read(ring), powers))
				}))
			below, support :=
				a.TermAs[Set[Nat]]("{i:num | i < n}"), a.TermAs[Set[Nat]]("fun_support(R.zero, p)")
			term := a.TermAs[Fun[Nat, A]]("λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)")
			a.Show(
				"the value is the sum over the support, which the "+
					"sum below n shrinks to, the ring a module over itself",
				Simp(Fwd(PolynomialEvalDef)),
				By(
					terms,
					offSupport,
					inside,
					module.ModuleSumSupport.Read(module.RegularModuleOn.Read(ring)).At(below, support, term),
					num_segment.FiniteBelowStrict.At(n)))
		}),
})}

// EvalBelowDegree — a polynomial's value is the sum of its terms through
// its degree: it vanishes past the degree (polynomial.DegreeVec), so the indices
// below the degree's successor are a segment past its support (EvalBelow).
var EvalBelowDegree = evalBelowDegreeThm{family.Add(registry.ProofEntry{
	Name: "EvalBelowDegree",
	Key:  "prop_5e0dd8fb52e09dbb",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, x) = " +
			"module_sum(R.add, " +
			"    R.zero, " +
			"    {i:num | i < suc(polynomial_degree(p))}, " +
			"    λi:num. p(i) * monoid_pow(R.mul, R.one, x, i))",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			over Fact,
			x *Member[A, on.R],
		) {
			// No dimension phantom spells the degree's successor, so EvalBelow is read at p untyped.
			a.Show(
				"p vanishes past its degree, so its value is its sum below the degree's successor",
				By(
					over,
					x,
					polynomial.DegreeVec.At(a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier"), p),
					At(Read(EvalBelow, ring), a.TermAs[Nat]("suc(polynomial_degree(p))"), p, x)))
		}),
})}

// EvalAtZero — at zero a polynomial takes its constant coefficient. Its
// value is the sum of its terms through its degree (EvalBelowDegree), and
// a positive power of zero is zero, so the sum is its term at 0, which is
// p(0) * one.
var EvalAtZero = evalAtZeroThm{family.Add(registry.ProofEntry{
	Name: "EvalAtZero",
	Key:  "prop_1c90b5b8010db92e",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_eval(p, R.zero) = p(0)",
		Abbrev: Abbrev{
			{Name: "indices", Text: "{i:num | i < suc(polynomial_degree(p))}"},
			{Name: "terms", Text: "λi:num. p(i) * monoid_pow(R.mul, R.one, R.zero, i)"},
		},
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], over Fact) {
			zero := a.MemberOf[on.R](a.TermAs[A]("R.zero"), comm_ring.ZeroIn.Read(ring))
			coefficients := a.Have(
				"every coefficient of p lies in c",
				"∀i:num. p(i) ∈ R.carrier",
				By(over, polynomial.PolynomialOverDef))
			powers := a.Have(
				"and every power of zero",
				"∀i:num. monoid_pow(R.mul, R.one, R.zero, i) ∈ R.carrier",
				By(zero, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
			terms := a.Have(
				"so every term lies in c",
				"∀i:num. «terms»(i) ∈ R.carrier",
				By(coefficients, powers, comm_ring.MulIn.Read(ring)))
			zeroPower := a.Have(
				"a positive power of zero is zero",
				"∀n:num. n ≠ 0 ⇒ monoid_pow(R.mul, R.one, R.zero, n) = R.zero",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					positive := b.Assume()
					m, isSuc := b.ObtainAs[Nat](
						"n is the successor of some m",
						"∃m:num. n = suc(m)",
						By(Normalized, positive, peano.Cases.At(n)))
					b.Show(
						"so it is zero times the m-th power of zero, which zero absorbs",
						isSuc.Rw(),
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(powers.At(m), comm_ring.MulLeftZeroOn.Read(ring)))
				}))
			vanishes := a.Have(
				"all nonconstant terms vanish at zero",
				"∀i:num. i ≠ 0 ⇒ «terms»(i) = R.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Assume()
					b.Show(
						"the zero power annihilates the term",
						Simp(Fwd(zeroPower)),
						By(coefficients.At(i), comm_ring.MulRightZeroOn.Read(ring)))
				}))
			conditions := a.Have(
				"the constant index is the only possible nonzero summand",
				"finite(«indices») ∧ "+
					"0 ∈ «indices» ∧ "+
					"(∀y:num. y ∈ «indices» ⇒ «terms»(y) ∈ R.carrier) ∧ "+
					"(∀y:num. y ∈ «indices» ∧ y ≠ 0 ⇒ «terms»(y) = R.zero)",
				ByArith(
					terms,
					vanishes,
					num_segment.FiniteBelowStrict.At(a.TermAs[Nat]("suc(polynomial_degree(p))"))))
			single := a.Have(
				"the sum is its constant-index term",
				"module_sum(R.add, R.zero, «indices», «terms») = «terms»(0)",
				By(
					conditions,
					module.ModuleSumSingle.Read(module.RegularModuleOn.Read(ring)).At(
						a.TermAs[Set[Nat]]("«indices»"), a.TermAs[Nat]("0"), a.TermAs[Fun[Nat, A]]("«terms»"))))
			constantTerm := a.Simplified(single, Fwd(comm_monoid.MonoidPowDef))
			sumValue := a.Have(
				"the constant-index term equals the constant coefficient",
				"module_sum(R.add, R.zero, «indices», «terms») = p(0)",
				ByArith(constantTerm, ring, coefficients.At(a.TermAs[Nat]("0"))))
			a.Show(
				"evaluation at zero is the constant coefficient",
				By(sumValue, over, EvalBelowDegree.Read(ring).At(p, zero)))
		}),
})}

// EvalFirstTermExpansion — a polynomial whose coefficients between 0 and k
// vanish, with p(k) nonzero, takes at z its constant coefficient, plus its
// term at k, plus the sum of its terms past k. Its value is the sum of its
// terms through its degree (EvalBelowDegree), of which k is one; the
// constant and k-th terms split off, and minimality kills every
// intervening term.
var EvalFirstTermExpansion = evalFirstTermExpansionThm{family.Add(registry.ProofEntry{
	Name: "EvalFirstTermExpansion",
	Key:  "prop_1ae95b1865823988",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀k:num. ∀z:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"0 < k",
			"p(k) ≠ R.zero",
			"∀i:num. 0 < i ∧ i < k ⇒ p(i) = R.zero",
			"z ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, z) = " +
			"p(0) + («terms»(k) + module_sum(R.add, R.zero, «tail», «terms»))",
		Abbrev: Abbrev{
			{Name: "indices", Text: "{i:num | i < suc(polynomial_degree(p))}"},
			{Name: "terms", Text: "λi:num. p(i) * monoid_pow(R.mul, R.one, z, i)"},
			{Name: "tail", Text: "{i:num | k < i ∧ i ≤ polynomial_degree(p)}"},
			{Name: "remaining", Text: "delete(delete(«indices», 0), k)"},
		},
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			k *Expr[Nat],
			given Fact,
			z *Member[A, on.R],
		) {
			regular := module.RegularModuleOn.Read(ring)
			zero, c, zeroth := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier"), a.TermAs[Nat]("0")
			successor := a.TermAs[Nat]("suc(polynomial_degree(p))")
			below, term := a.TermAs[Set[Nat]]("«indices»"), a.TermAs[Fun[Nat, A]]("«terms»")
			coefficients := a.Have(
				"every coefficient of p lies in c",
				"∀i:num. p(i) ∈ R.carrier",
				By(given, polynomial.PolynomialOverDef))
			powers := a.Have(
				"and every power of z",
				"∀i:num. monoid_pow(R.mul, R.one, z, i) ∈ R.carrier",
				By(z, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
			terms := a.Have(
				"so every term lies in c",
				"∀i:num. «terms»(i) ∈ R.carrier",
				By(coefficients, powers, comm_ring.MulIn.Read(ring)))
			degreeBound := a.Have(
				"a nonzero coefficient lies below the degree bound",
				"k ≤ polynomial_degree(p)",
				ByArith(given, polynomial.DegreeVec.At(zero, c, p), At(vec_space.VecDef, zero, successor, p)))
			indices := a.Have(
				"both selected indices occur in the finite sum",
				"finite(«indices») ∧ 0 ∈ «indices» ∧ k ∈ delete(«indices», 0) ∧ (∀i:num. «terms»(i) ∈ R.carrier)",
				Simp(Fwd(set_basic.DeleteDef.Inst[Nat]())),
				ByArith(degreeBound, given, terms, num_segment.FiniteBelowStrict.At(successor)))
			constantSplit := a.Have(
				"split off the constant-index term",
				"module_sum(R.add, R.zero, «indices», «terms») = "+
					"«terms»(0) + module_sum(R.add, R.zero, delete(«indices», 0), «terms»)",
				By(indices, module.ModuleSumDelete.Read(regular).At(below, zeroth, term)))
			firstSplit := a.Have(
				"split off the first nonconstant term",
				"module_sum(R.add, R.zero, delete(«indices», 0), «terms») = "+
					"«terms»(k) + module_sum(R.add, R.zero, «remaining», «terms»)",
				By(
					indices,
					finite_set.FiniteDeleteImp.At(below, zeroth),
					module.ModuleSumDelete.Read(regular).At(a.TermAs[Set[Nat]]("delete(«indices», 0)"), k, term)))
			vanishes := a.Have(
				"remaining indices outside the tail have zero coefficients",
				"∀i:num. i ∈ «remaining» ∧ i ∉ «tail» ⇒ «terms»(i) = R.zero",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(set_basic.DeleteDef.Inst[Nat]())))
					i := b.FixAs[Nat]("i")
					membership := b.Assume()
					middle := b.Have(
						"this is an intervening positive index",
						"0 < i ∧ i < k",
						ByArith(membership))
					coefficientZero := b.Have(
						"minimality makes its coefficient zero",
						"p(i) = R.zero",
						By(middle, given))
					b.Show(
						"the intervening term is zero times a power of z, a member of c",
						coefficientZero.Rw(),
						By(comm_ring.MulLeftZeroOn.Read(ring), powers.At(i)))
				}))
			restriction := a.Have(
				"the higher tail is a subset of the finite remainder",
				"finite(«remaining») ∧ «tail» ⊆ «remaining»",
				SplitConj(
					Case(
						"deleting two indices preserves finiteness",
						By(
							indices,
							finite_set.FiniteDeleteImp.At(below, zeroth),
							finite_set.FiniteDeleteImp.At(a.TermAs[Set[Nat]]("delete(«indices», 0)"), k))),
					Case(
						"higher indices avoid zero and k",
						Simp(Fwd(set_basic.DeleteDef.Inst[Nat]()), Fwd(set_basic.SubsetDef.Inst[Nat]())),
						ByArith())))
			tailSum := a.Have(
				"support restriction removes the zero middle terms",
				"module_sum(R.add, R.zero, «remaining», «terms») = module_sum(R.add, R.zero, «tail», «terms»)",
				By(
					vanishes,
					restriction,
					indices,
					module.ModuleSumSupport.Read(regular).At(
						a.TermAs[Set[Nat]]("«remaining»"), a.TermAs[Set[Nat]]("«tail»"), term)))
			constant := a.Have(
				"the constant-index term is the constant coefficient",
				"«terms»(0) = p(0)",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				ByArith(ring, coefficients.At(zeroth)))
			a.Show(
				"the two selected coefficients and the tail give the evaluation",
				By(constant, constantSplit, firstSplit, tailSum, given, EvalBelowDegree.Read(ring).At(p, z)))
		}),
})}

// EvalOneBelow — at one, a polynomial vanishing from n on takes the sum of
// its coefficients below n. Its value at one is the sum of p(i) * one ^ i
// over the indices below n (EvalBelow), and every power of one is one,
// which leaves each coefficient as it is.
var EvalOneBelow = evalOneBelowThm{family.Add(registry.ProofEntry{
	Name: "EvalOneBelow",
	Key:  "prop_d4821498a73c908e",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"vec⟨n⟩(p)",
		},
		Conclusion: "polynomial_eval(p, R.one) = module_sum(R.add, R.zero, {i:num | i < n}, p)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			n *Expr[Nat],
			p *Vec[A, DimN],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"vanishing from n on")
			over, vanishes := parts[0], parts[1]
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			one := a.MemberOf[on.R](a.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			coefficients := a.Have(
				"every coefficient of p lies in c",
				"∀i:num. p(i) ∈ R.carrier",
				By(over, polynomial.PolynomialOverDef))
			terms := a.Have(
				"a coefficient times a power of one is the coefficient",
				"∀i:num. p(i) * monoid_pow(R.mul, R.one, R.one, i) = p(i)",
				By(
					coefficients,
					comm_monoid.IdentityPowOn.Read(multiplicative),
					comm_monoid.RightIdentityOn.Read(multiplicative)))
			a.Show(
				"the value at one is the sum of the terms below n, each its coefficient",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, {i:num | i < n}, λi:num. p(i) * monoid_pow(R.mul, R.one, R.one, i))"),
						"the value at one is the sum of p(i) * one ^ i below n",
						By(over, EvalBelow.Read(ring).At(proof.Inhabit(p, vanishes), one))),
					FinalLeg(
						"and each of those terms is its coefficient",
						By(terms, module.ModuleSumCongruence))))
		}),
})}

// EvalOneSupport — at one, a sequence with every term in c takes the sum
// of its terms over its support: its value is the sum of p(i) * one ^ i
// over the support, and every power of one is one, which leaves each term
// as it is.
var EvalOneSupport = evalOneSupportThm{family.Add(registry.ProofEntry{
	Name: "EvalOneSupport",
	Key:  "prop_602ac106ac2f67aa",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀p:(num → A).",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier"},
		Conclusion: "polynomial_eval(p, R.one) = module_sum(R.add, R.zero, fun_support(R.zero, p), p)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Arrow[Nat, A], coefficients Fact) {
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			terms := a.Have(
				"a coefficient times a power of one is the coefficient",
				"∀i:num. p(i) * monoid_pow(R.mul, R.one, R.one, i) = p(i)",
				By(
					coefficients,
					comm_monoid.IdentityPowOn.Read(multiplicative),
					comm_monoid.RightIdentityOn.Read(multiplicative)))
			a.Show(
				"the value at one is the sum over the support of the terms, each its coefficient",
				Simp(Fwd(PolynomialEvalDef), Fwd(terms)),
				Basic())
		}),
})}

// EvalVecTwo — a polynomial vanishing from index two on takes the value
// p(0) + p(1) * x at every point x of c: its value is the sum of its
// terms below two (EvalBelow), which the sum's clauses read as the term
// at zero plus the term at one.
var EvalVecTwo = evalVecTwoThm{family.Add(registry.ProofEntry{
	Name:    "EvalVecTwo",
	Key:     "prop_c9f59a3cb2321ccd",
	Reading: "vec⟨suc(1)⟩(p) is how DegreeVec gives a polynomial of degree at most one.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"vec⟨suc(1)⟩(p)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, x) = p(0) + p(1) * x",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			given Fact,
			x *Member[A, on.R],
		) {
			parts := a.Conjuncts(
				given,
				"p is a polynomial over the ring",
				"p vanishes from index two on")
			over, short := parts[0], parts[1]
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			coefficients := a.Have(
				"every coefficient lies in the ring",
				"∀i:num. p(i) ∈ R.carrier",
				By(over, polynomial.CoefficientIn))
			term, termDef := a.LetAs[Fun[Nat, A]]("term", "λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)")
			termsIn := a.Have(
				"each coefficient times the corresponding power lies in the ring",
				"∀i:num. term(i) ∈ R.carrier",
				termDef.Rw(),
				By(coefficients, x, comm_monoid.PowIn.Read(multiplicative), comm_ring.MulIn.Read(ring)))
			asSum := a.Have(
				"the value is the sum of the two terms",
				"polynomial_eval(p, x) = module_sum(R.add, R.zero, {i:num | i < suc(1)}, term)",
				termDef.Rw(),
				By(over, EvalBelow.Read(ring).At(proof.InhabitFrom(p, short), x)))
			clauses := a.Conjuncts(
				module.ModuleSumBelowClauses.Read(module.RegularModuleOn.Read(ring)).At(term),
				"the empty sum is zero",
				"raising the bound by one adds the next term")
			second := a.Have(
				"the second term extends the sum below one",
				"module_sum(R.add, R.zero, {i:num | i < suc(1)}, term) = "+
					"module_sum(R.add, R.zero, {i:num | i < 1}, term) + term(1)",
				By(termsIn, clauses[1].At(a.TermAs[Nat]("1"))))
			first := a.Have(
				"the first term extends the empty sum",
				"module_sum(R.add, R.zero, {i:num | i < 1}, term) = "+
					"module_sum(R.add, R.zero, {i:num | i < 0}, term) + term(0)",
				Simp(Fwd(nat_arith.OneIsSucZero)),
				By(termsIn, clauses[1].At(a.TermAs[Nat]("0"))))
			power := a.Have(
				"the first power of x is x",
				"monoid_pow(R.mul, R.one, x, 1) = x",
				By(comm_monoid.PowOneOn.Read(multiplicative).At(x)))
			a.Show(
				"the two terms are p(0) and p(1) times x",
				asSum.Rw(),
				second.Rw(),
				first.Rw(),
				clauses[0].Rw(),
				termDef.Rw(),
				Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(power)),
				ByArith(ring, coefficients.At(a.TermAs[Nat]("0")), coefficients.At(a.TermAs[Nat]("1")), x))
		}),
})}

// EvalVecThree — a polynomial vanishing from index three on is the sum
// of its constant, linear and quadratic terms: expand the sum below
// three and simplify the first three powers.
var EvalVecThree = evalVecThreeThm{family.Add(registry.ProofEntry{
	Name:    "EvalVecThree",
	Key:     "prop_44309a92cd0c111e",
	Reading: "vec⟨suc(2)⟩(p) is how DegreeVec gives a polynomial of degree at most two.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"vec⟨suc(2)⟩(p)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, x) = p(0) + p(1) * x + p(2) * (x * x)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			given Fact,
			x *Member[A, on.R],
		) {
			parts := a.Conjuncts(
				given,
				"p is a polynomial over the ring",
				"p vanishes from index three on")
			over, short := parts[0], parts[1]
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			coefficients := a.Have(
				"every coefficient lies in the ring",
				"∀i:num. p(i) ∈ R.carrier",
				By(over, polynomial.CoefficientIn))
			term, termDef := a.LetAs[Fun[Nat, A]]("term", "λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)")
			termsIn := a.Have(
				"each coefficient times the corresponding power lies in the ring",
				"∀i:num. term(i) ∈ R.carrier",
				termDef.Rw(),
				By(coefficients, x, comm_monoid.PowIn.Read(multiplicative), comm_ring.MulIn.Read(ring)))
			asSum := a.Have(
				"the value is the sum of the three terms",
				"polynomial_eval(p, x) = module_sum(R.add, R.zero, {i:num | i < suc(2)}, term)",
				termDef.Rw(),
				By(over, EvalBelow.Read(ring).At(proof.InhabitFrom(p, short), x)))
			clauses := a.Conjuncts(
				module.ModuleSumBelowClauses.Read(module.RegularModuleOn.Read(ring)).At(term),
				"the empty sum is zero",
				"raising the bound by one adds the next term")
			third := a.Have(
				"the third term extends the sum below two",
				"module_sum(R.add, R.zero, {i:num | i < suc(2)}, term) = "+
					"module_sum(R.add, R.zero, {i:num | i < 2}, term) + term(2)",
				By(termsIn, clauses[1].At(a.TermAs[Nat]("2"))))
			second := a.Have(
				"the second term extends the sum below one",
				"module_sum(R.add, R.zero, {i:num | i < 2}, term) = "+
					"module_sum(R.add, R.zero, {i:num | i < 1}, term) + term(1)",
				Simp(Fwd(nat_arith.Two)),
				By(termsIn, clauses[1].At(a.TermAs[Nat]("1"))))
			first := a.Have(
				"the first term extends the empty sum",
				"module_sum(R.add, R.zero, {i:num | i < 1}, term) = "+
					"module_sum(R.add, R.zero, {i:num | i < 0}, term) + term(0)",
				Simp(Fwd(nat_arith.OneIsSucZero)),
				By(termsIn, clauses[1].At(a.TermAs[Nat]("0"))))
			powers := a.Have(
				"the first and second powers of x are x and x * x",
				"monoid_pow(R.mul, R.one, x, 1) = x ∧ monoid_pow(R.mul, R.one, x, 2) = x * x",
				By(
					comm_monoid.PowOneOn.Read(multiplicative).At(x),
					comm_monoid.PowTwoOn.Read(multiplicative).At(x)))
			a.Show(
				"expand the three terms and their powers",
				asSum.Rw(),
				third.Rw(),
				second.Rw(),
				first.Rw(),
				clauses[0].Rw(),
				termDef.Rw(),
				Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(powers)),
				ByArith(
					ring,
					coefficients.At(a.TermAs[Nat]("0")),
					coefficients.At(a.TermAs[Nat]("1")),
					coefficients.At(a.TermAs[Nat]("2")),
					x))
		}),
})}

// EvalAdd —evaluation at a point of c takes a sum of polynomials to the
// sum of their values. With p an m-vector and q an n-vector, all three of
// p, q and p + q vanish from m + n on, so each value is its sum below
// m + n (EvalBelow). There each term (p(i) + q(i)) * x ^ i splits by
// distributivity, and the sum of the split terms is the sum of the two
// sums.
var EvalAdd = evalAddThm{family.Add(registry.ProofEntry{
	Name: "EvalAdd",
	Key:  "prop_b3c67e98a60e3b5a",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p + q, x) = polynomial_eval(p, x) + polynomial_eval(q, x)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p, q *Arrow[Nat, A],
			x *Expr[A],
			hypotheses Fact,
		) {
			regular := module.RegularModuleOn.Read(ring)
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"so is q",
				"x lies in c")
			pOver, qOver, xIn := parts[0], parts[1], parts[2]
			xM := a.MemberOf[on.R](x, xIn)
			coefficients := a.Have(
				"every coefficient of p and of q lies in c",
				"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
				By(pOver, qOver, polynomial.PolynomialOverDef))
			powers := a.Have(
				"and so does every power of x",
				"∀i:num. monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(xIn, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
			m, pVec := a.ObtainAs[Nat](
				"p vanishes from some index m on",
				"∃m:num. vec⟨m⟩(p)",
				By(pOver, polynomial.PolynomialOverDef.At(zero, c, p)))
			n, qVec := a.ObtainAs[Nat](
				"and q from some index n on",
				"∃n:num. vec⟨n⟩(q)",
				By(qOver, polynomial.PolynomialOverDef.At(zero, c, q)))
			mn := a.TermAs[Nat]("m + n")
			pPast := a.Have(
				"so p vanishes from m + n on",
				"vec⟨m + n⟩(p)",
				By(pVec, nat_order.LessEqAdd.At(m, n), vec_space.VecMono.At(zero, m, mn, p)))
			qPast := a.Have(
				"and so does q",
				"vec⟨m + n⟩(q)",
				By(qVec, nat_order.LessEqAddLeft.At(m, n), vec_space.VecMono.At(zero, n, mn, q)))
			pBelow := proof.InhabitFrom(p, pPast)
			qBelow := proof.InhabitFrom(q, qPast)
			sumPast := a.Have(
				"and so does p + q, a sum of two (m + n)-vectors",
				"vec⟨m + n⟩(p + q)",
				By(vec_space.VecAddOn.Read(ring).At(pBelow, qBelow)))
			sumIn := a.Have(
				"each coefficient p(i) + q(i) of p + q lies in c",
				"∀i:num.(p + q)(i) ∈ R.carrier",
				Simp(Fwd(vec_space.VecAddDef)),
				By(coefficients, comm_ring.AddIn.Read(ring)))
			sum := a.TermAs[Fun[Nat, A]]("p + q")
			sumOver := a.Have(
				"so p + q is a polynomial over c",
				"polynomial_over(R.carrier, p + q)",
				By(sumIn, sumPast, polynomial.PolynomialOverDef.At(zero, c, sum)))
			sumBelow := proof.InhabitFrom(sum, sumPast)
			splits := a.Have(
				"each term (p + q)(i) * x ^ i splits, as the ring's product distributes over its sum",
				"∀i:num.(p + q)(i) * monoid_pow(R.mul, R.one, x, i) = "+
					"p(i) * monoid_pow(R.mul, R.one, x, i) + q(i) * monoid_pow(R.mul, R.one, x, i)",
				Simp(Fwd(vec_space.VecAddDef)),
				By(coefficients, powers, comm_ring.RightDistribOn.Read(ring)))
			termsIn := a.Have(
				"the terms of p and of q lie in c",
				"∀i:num. "+
					"    p(i) * monoid_pow(R.mul, R.one, x, i) ∈ R.carrier ∧ "+
					"    q(i) * monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(coefficients, powers, comm_ring.MulIn.Read(ring)))
			a.Show(
				"all three values are sums over the indices below m + n",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < m + n}, "+
								"    λi:num.(p + q)(i) * monoid_pow(R.mul, R.one, x, i))"),
						"p + q is a polynomial over c vanishing from m + n on",
						By(sumOver, EvalBelow.Read(ring).At(sumBelow, xM))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < m + n}, "+
								"    λi:num. p(i) * monoid_pow(R.mul, R.one, x, i) + q(i) * monoid_pow(R.mul, R.one, x, i))"),
						"split each term",
						By(splits, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, {i:num | i < m + n}, λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)) + "+
								"module_sum(R.add, R.zero, {i:num | i < m + n}, λi:num. q(i) * monoid_pow(R.mul, R.one, x, i))"),
						"a finite sum of sums is the sum of the two sums, the ring a module over itself",
						By(
							termsIn,
							num_segment.FiniteBelowStrict.At(mn),
							module.ModuleSumAdd.Read(regular).At(
								a.TermAs[Set[Nat]]("{i:num | i < m + n}"),
								a.TermAs[Fun[Nat, A]]("λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)"),
								a.TermAs[Fun[Nat, A]]("λi:num. q(i) * monoid_pow(R.mul, R.one, x, i)")))),
					FinalLeg(
						"and so are p and q",
						By(pOver, qOver, EvalBelow.Read(ring).At(pBelow, xM), EvalBelow.Read(ring).At(qBelow, xM))),
				))
		}),
})}

// EvalMul — evaluation at a point of c takes a product of polynomials to
// the product of their values. With p an m-vector and q an n-vector the
// product vanishes past m + n (polynomial.PolynomialMulVec), and its value is the sum
// of p(i) q(k - i) x ^ k over the triangle i ≤ k ≤ m + n. Regrouped by i
// with k = i + j (ModuleSumTriangleSwap, the ring a module over itself)
// and cut to i < m and j < n, where the other terms vanish, it is the
// double sum of p(i) q(j) x ^ (i + j) — which is the product of the two
// values multiplied out.
var EvalMul = evalMulThm{family.Add(registry.ProofEntry{
	Name: "EvalMul",
	Key:  "prop_4fdcd3e92b2e48c4",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(polynomial_mul(p, q), x) = " +
			"polynomial_eval(p, x) * polynomial_eval(q, x)",
		Abbrev: Abbrev{
			{Name: "productDoubleSum", Text: "module_sum(R.add, " +
				"    R.zero, " +
				"    {i:num | i < m}, " +
				"    λi:num. " +
				"        module_sum(R.add, " +
				"            R.zero, " +
				"            {j:num | j < n}, " +
				"            λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)))"},
		},
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p, q *Arrow[Nat, A],
			x *Expr[A],
			hypotheses Fact,
		) {
			// The double sum of p(i) q(j) x ^ (i + j) over i < m and j < n that
			// both sides reach, and the column at i of the regrouped triangle,
			// over j ≤ m + n - i.
			regular := module.RegularModuleOn.Read(ring)
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			leftZero, rightZero := comm_ring.MulLeftZeroOn.Read(ring), comm_ring.MulRightZeroOn.Read(ring)
			zero, c := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"so is q",
				"x lies in c")
			pOver, qOver, xIn := parts[0], parts[1], parts[2]
			xM := a.MemberOf[on.R](x, xIn)
			// The definition supplies the existential half for p and for q.
			m, pVec := a.ObtainAs[Nat](
				"p vanishes from some index m on",
				"∃m:num. vec⟨m⟩(p)",
				By(pOver, polynomial.PolynomialOverDef.At(zero, c, p)))
			n, qVec := a.ObtainAs[Nat](
				"and q from some index n on",
				"∃n:num. vec⟨n⟩(q)",
				By(qOver, polynomial.PolynomialOverDef.At(zero, c, q)))
			pIn := a.Have(
				"every coefficient of p lies in c",
				"∀i:num. p(i) ∈ R.carrier",
				By(pOver, polynomial.PolynomialOverDef))
			qIn := a.Have(
				"and every coefficient of q",
				"∀j:num. q(j) ∈ R.carrier",
				By(qOver, polynomial.PolynomialOverDef))
			powersIn := a.Have(
				"and every power of x",
				"∀k:num. monoid_pow(R.mul, R.one, x, k) ∈ R.carrier",
				By(xIn, comm_monoid.PowIn.Read(mulMonoid)))

			belowM, belowN := a.TermAs[Set[Nat]]("{i:num | i < m}"), a.TermAs[Set[Nat]]("{j:num | j < n}")
			termP, termQ :=
				a.TermAs[Fun[Nat, A]]("λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)"),
				a.TermAs[Fun[Nat, A]]("λj:num. q(j) * monoid_pow(R.mul, R.one, x, j)")
			valueP := a.Have(
				"p's value is its sum below m",
				"polynomial_eval(p, x) = "+
					"module_sum(R.add, R.zero, {i:num | i < m}, λi:num. p(i) * monoid_pow(R.mul, R.one, x, i))",
				By(pOver, EvalBelow.Read(ring).At(proof.InhabitFrom(p, pVec), xM)))
			valueQ := a.Have(
				"and q's its sum below n",
				"polynomial_eval(q, x) = "+
					"module_sum(R.add, R.zero, {j:num | j < n}, λj:num. q(j) * monoid_pow(R.mul, R.one, x, j))",
				By(qOver, EvalBelow.Read(ring).At(proof.InhabitFrom(q, qVec), xM)))
			termsP := a.Have(
				"each term p(i) x ^ i lies in c",
				"∀i:num. p(i) * monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(pIn, powersIn, comm_ring.MulIn.Read(ring)))
			termsQ := a.Have(
				"and each term q(j) x ^ j",
				"∀j:num. q(j) * monoid_pow(R.mul, R.one, x, j) ∈ R.carrier",
				By(qIn, powersIn, comm_ring.MulIn.Read(ring)))
			sumQ := a.TermAs[A](
				"module_sum(R.add, R.zero, {j:num | j < n}, λj:num. q(j) * monoid_pow(R.mul, R.one, x, j))")
			sumQIn := a.Have(
				"so q's sum, a finite sum of members of c, lies in c",
				"module_sum(R.add, R.zero, {j:num | j < n}, λj:num. q(j) * monoid_pow(R.mul, R.one, x, j)) ∈ "+
					"R.carrier",
				By(termsQ, module.ModuleSumIn.Read(regular).At(belowN, termQ), num_segment.FiniteBelowStrict.At(n)))
			regroup := a.Have(
				"p(i) x ^ i times q(j) x ^ j is p(i) q(j) x ^ (i + j)",
				"∀i j:num. "+
					"    p(i) * monoid_pow(R.mul, R.one, x, i) * (q(j) * monoid_pow(R.mul, R.one, x, j)) = "+
					"    p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					j := b.FixAs[Nat]()
					b.Do(Simp(Fwd(comm_monoid.PowAddOn.Read(mulMonoid))))
					b.Show(
						"x ^ (i + j) is x ^ i * x ^ j, and the ring regroups the factors",
						ByArith(ring, pIn.At(i), qIn.At(j), powersIn.At(i), powersIn.At(j)))
				}))
			columns := a.Have(
				"p(i) x ^ i times q's sum is the column of p(i) q(j) x ^ (i + j) over j < n",
				"∀i:num. "+
					"    p(i) * "+
					"    monoid_pow(R.mul, R.one, x, i) * "+
					"    module_sum(R.add, R.zero, {j:num | j < n}, λj:num. q(j) * monoid_pow(R.mul, R.one, x, j)) = "+
					"    module_sum(R.add, "+
					"        R.zero, "+
					"        {j:num | j < n}, "+
					"        λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					b.Show(
						"the factor passes into the sum, and the terms regroup",
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(R.add, "+
										"    R.zero, "+
										"    {j:num | j < n}, "+
										"    λj:num. p(i) * monoid_pow(R.mul, R.one, x, i) * (q(j) * monoid_pow(R.mul, R.one, x, j)))"),
								"a factor in c passes into a finite sum",
								By(
									termsP.At(i),
									termsQ,
									module.ModuleSumSmul.Read(regular).AsFact().At(
										belowN, b.TermAs[A]("p(i) * monoid_pow(R.mul, R.one, x, i)"), termQ),
									num_segment.FiniteBelowStrict.At(n))),
							FinalLeg(
								"term by term the factors regroup",
								By(regroup, module.ModuleSumCongruence)),
						))
				}))
			product := a.Have(
				"so the product of the two values is the double sum of p(i) q(j) x ^ (i + j) over i < m and j < n",
				"polynomial_eval(p, x) * polynomial_eval(q, x) = «productDoubleSum»",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, R.zero, {i:num | i < m}, λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)) * "+
								"module_sum(R.add, R.zero, {j:num | j < n}, λj:num. q(j) * monoid_pow(R.mul, R.one, x, j))"),
						"both values as their sums",
						By(valueP, valueQ)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < m}, "+
								"    λi:num. "+
								"        p(i) * "+
								"        monoid_pow(R.mul, R.one, x, i) * "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:num | j < n}, "+
								"            λj:num. q(j) * monoid_pow(R.mul, R.one, x, j)))"),
						"q's sum, a member of c, passes into p's",
						By(
							termsP,
							module.ModuleSumSmulRight.Read(regular).At(belowM, termP, a.MemberOf[on.R](sumQ, sumQIn)),
							num_segment.FiniteBelowStrict.At(m))),
					FinalLeg(
						"column by column",
						By(columns, module.ModuleSumCongruence)),
				))

			mn := a.TermAs[Nat]("m + n")
			pq := a.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)")
			pPast := a.Have(
				"p vanishes from m on, so past m",
				"vec⟨suc(m)⟩(p)",
				By(
					pVec,
					vec_space.VecMono.At(zero, m, a.TermAs[Nat]("suc(m)"), p),
					nat_order.LessEqSucClause.At(m, m),
					nat_order.LessEqRefl.At(m)))
			qPast := a.Have(
				"and q past n",
				"vec⟨suc(n)⟩(q)",
				By(
					qVec,
					vec_space.VecMono.At(zero, n, a.TermAs[Nat]("suc(n)"), q),
					nat_order.LessEqSucClause.At(n, n),
					nat_order.LessEqRefl.At(n)))
			productPast := a.Have(
				"so the product vanishes past m + n",
				"vec⟨suc(m + n)⟩(polynomial_mul(p, q))",
				By(pOver, qOver, pPast, qPast, polynomial.PolynomialMulVec.Read(ring).At(m, n, p, q)))
			upTo := a.Have(
				"the indices below suc(m + n) are those up to m + n",
				"{k:num | k < suc(m + n)} = {k:num | k ≤ m + n}",
				BySets(nat_order.LessThanSucIffLessEq))
			rows := a.Have(
				"each coefficient of the product times x ^ k is its convolution sum, x ^ k carried inside",
				"∀k:num. "+
					"    polynomial_mul(p, q, k) * monoid_pow(R.mul, R.one, x, k) = "+
					"    module_sum(R.add, "+
					"        R.zero, "+
					"        {i:num | i ≤ k}, "+
					"        λi:num. p(i) * q(k - i) * monoid_pow(R.mul, R.one, x, k))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(Simp(Fwd(polynomial.PolynomialMulDef)))
					b.Show(
						"x ^ k, a member of c, passes into the sum over i ≤ k",
						By(
							pIn,
							qIn,
							powersIn.At(k),
							comm_ring.MulIn.Read(ring),
							module.ModuleSumSmulRight.Read(regular).AsFact().At(
								b.TermAs[Set[Nat]]("{i:num | i ≤ k}"),
								b.TermAs[Fun[Nat, A]]("λi:num. p(i) * q(k - i)"),
								b.TermAs[A]("monoid_pow(R.mul, R.one, x, k)")),
							num_segment.FiniteBelow.At(k)))
				}))
			triangleTermsIn := a.Have(
				"every term p(i) q(k - i) x ^ k lies in c",
				"∀i k:num. p(i) * q(k - i) * monoid_pow(R.mul, R.one, x, k) ∈ R.carrier",
				By(pIn, qIn, powersIn, comm_ring.MulIn.Read(ring)))
			termsIn := a.Have(
				"and so does every term p(i) q(j) x ^ (i + j)",
				"∀i j:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j) ∈ R.carrier",
				By(pIn, qIn, powersIn, comm_ring.MulIn.Read(ring)))
			pastM := a.Have(
				"a term with m ≤ i is zero, as p(i) is",
				"∀i j:num. m ≤ i ⇒ p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j) = R.zero",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					j := b.FixAs[Nat]()
					bound := b.Assume()
					pZero := b.Have(
						"p(i) = R.zero, as m ≤ i",
						"p(i) = R.zero",
						By(bound, pVec, vec_space.VecDef))
					power, ij := b.TermAs[A]("monoid_pow(R.mul, R.one, x, i + j)"), b.TermAs[Nat]("i + j")
					b.Show(
						"so the term is zero times q(j) x ^ (i + j), and zero absorbs each factor",
						pZero.Rw(),
						By(
							leftZero.At(b.MemberOf[on.R](q.Apply(j), qIn.At(j))),
							leftZero.At(b.MemberOf[on.R](power, powersIn.At(ij)))))
				}))
			pastN := a.Have(
				"and a term with n ≤ j is zero, as q(j) is",
				"∀i j:num. n ≤ j ⇒ p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j) = R.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					b.FixAs[Nat]()
					bound := b.Assume()
					qZero := b.Have(
						"q(j) = R.zero, as n ≤ j",
						"q(j) = R.zero",
						By(bound, qVec, vec_space.VecDef))
					power, ij := b.TermAs[A]("monoid_pow(R.mul, R.one, x, i + j)"), b.TermAs[Nat]("i + j")
					b.Show(
						"so the term is p(i) times zero times x ^ (i + j), and zero absorbs each factor",
						qZero.Rw(),
						By(
							rightZero.At(b.MemberOf[on.R](p.Apply(i), pIn.At(i))),
							leftZero.At(b.MemberOf[on.R](power, powersIn.At(ij)))))
				}))
			columnsIn := a.Have(
				"each column of the regrouped triangle lies in c",
				"∀i:num. "+
					"    module_sum(R.add, "+
					"        R.zero, "+
					"        {j:num | j ≤ m + n - i}, "+
					"        λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)) ∈ "+
					"    R.carrier",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					b.Show(
						"a finite sum of members of c",
						By(
							termsIn,
							module.ModuleSumIn.Read(regular).At(
								b.TermAs[Set[Nat]]("{j:num | j ≤ m + n - i}"),
								b.TermAs[Fun[Nat, A]]("λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)")),
							num_segment.FiniteBelow.At(b.TermAs[Nat]("m + n - i"))))
				}))
			columnsPastM := a.Have(
				"and a column with m ≤ i is zero, every term of it being",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"m ≤ i",
					},
					Conclusion: "module_sum(R.add, " +
						"    R.zero, " +
						"    {j:num | j ≤ m + n - i}, " +
						"    λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)) = " +
						"R.zero",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					bound := b.Assume()
					b.Show(
						"a sum of zeros",
						By(
							pastM,
							bound,
							module.ModuleSumZero.Read(regular).At(
								b.TermAs[Set[Nat]]("{j:num | j ≤ m + n - i}"),
								b.TermAs[Fun[Nat, A]]("λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)")),
							num_segment.FiniteBelow.At(b.TermAs[Nat]("m + n - i"))))
				}))
			inside := a.Have(
				"an index below m is at most m + n",
				"∀i:num. i < m ⇒ i ≤ m + n",
				ByArith())
			columnsCut := a.Have(
				"a column with i < m is its part below n, the terms from n on vanishing",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i ∈ {i:num | i < m}",
					},
					Conclusion: "module_sum(R.add, " +
						"    R.zero, " +
						"    {j:num | j ≤ m + n - i}, " +
						"    λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)) = " +
						"module_sum(R.add, " +
						"    R.zero, " +
						"    {j:num | j < n}, " +
						"    λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					among := b.Assume()
					below := b.Have(
						"i lies below m",
						"i < m",
						BySets(among))
					shorter := b.Have(
						"an index below n is at most m + n - i, as i < m",
						"∀j:num. j < n ⇒ j ≤ m + n - i",
						ByArith(below))
					b.Show(
						"the terms from n on are zero",
						BySets(
							shorter,
							termsIn,
							pastN,
							module.ModuleSumSupport.Read(regular).At(
								b.TermAs[Set[Nat]]("{j:num | j ≤ m + n - i}"),
								belowN,
								b.TermAs[Fun[Nat, A]]("λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)")),
							num_segment.FiniteBelow.At(b.TermAs[Nat]("m + n - i")),
							nat_order.NotLessThan))
				}))
			column := a.TermAs[Fun[Nat, A]](
				"λi:num. " +
					"    module_sum(R.add, " +
					"        R.zero, " +
					"        {j:num | j ≤ m + n - i}, " +
					"        λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j))")
			a.Show(
				"the product's value, summed over the triangle and regrouped by i, is the double sum",
				CalcEq(
					// No dimension phantom spells suc(m + n), so EvalBelow is read at the product untyped.
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {k:num | k ≤ m + n}, "+
								"    λk:num. polynomial_mul(p, q, k) * monoid_pow(R.mul, R.one, x, k))"),
						"the product's value is its sum up to m + n",
						By(
							pOver,
							qOver,
							xIn,
							productPast,
							upTo,
							At(Read(EvalBelow, ring), a.TermAs[Nat]("suc(m + n)"), pq, x),
							polynomial.PolynomialMulOver.Read(ring))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {k:num | k ≤ m + n}, "+
								"    λk:num. "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {i:num | i ≤ k}, "+
								"            λi:num. p(i) * q(k - i) * monoid_pow(R.mul, R.one, x, k)))"),
						"each coefficient times x ^ k is its convolution sum",
						By(rows, module.ModuleSumCongruence)),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i ≤ m + n}, "+
								"    λi:num. "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:num | j ≤ m + n - i}, "+
								"            λj:num. p(i) * q(i + j - i) * monoid_pow(R.mul, R.one, x, i + j)))"),
						"the triangle i ≤ k ≤ m + n, regrouped by i with k = i + j, the ring a module over itself",
						By(
							triangleTermsIn,
							module.ModuleSumTriangleSwap.Read(regular).At(
								mn,
								a.TermAs[Fun2[Nat, Nat, A]]("λi:num. λk:num. p(i) * q(k - i) * monoid_pow(R.mul, R.one, x, k)")))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i ≤ m + n}, "+
								"    λi:num. "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:num | j ≤ m + n - i}, "+
								"            λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)))"),
						"(i + j) - i is j",
						Simp(Fwd(nat_monus.AddSubLeftCancel)),
						Refl()),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < m}, "+
								"    λi:num. "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:num | j ≤ m + n - i}, "+
								"            λj:num. p(i) * q(j) * monoid_pow(R.mul, R.one, x, i + j)))"),
						"the columns from m on vanish",
						BySets(
							inside,
							columnsIn,
							columnsPastM,
							module.ModuleSumSupport.Read(regular).At(a.TermAs[Set[Nat]]("{i:num | i ≤ m + n}"), belowM, column),
							num_segment.FiniteBelow.At(mn),
							nat_order.NotLessThan)),
					Leg(
						a.TermAs[A]("«productDoubleSum»"),
						"in each column below m the terms from n on vanish",
						By(columnsCut, module.ModuleSumCongruence)),
					FinalLeg(
						"which is the product of the two values",
						By(product)),
				))
		}),
})}

// EvalBasisVector — the k-th power of the variable evaluates to x ^ k.
// basis_vector(k) is a polynomial over c vanishing from suc(k) on, so its
// value is its sum below suc(k) (EvalBelow); off the index k each term is
// zero times a power of x, so the sum is its term at k (ModuleSumSingle),
// basis_vector(k, k) * x ^ k = one * x ^ k. No case on one = zero is
// needed: the basis vector vanishes from suc(k) on whatever one is, and
// the sum keeps its term at k without asking that it be nonzero.
var EvalBasisVector = evalBasisVectorThm{family.Add(registry.ProofEntry{
	Name: "EvalBasisVector",
	Key:  "prop_b329aacb153dc549",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀k:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(basis_vector(k), x) = monoid_pow(R.mul, R.one, x, k)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], k *Expr[Nat], x *Member[A, on.R]) {
			regular := module.RegularModuleOn.Read(ring)
			zero, one, c := a.TermAs[A]("R.zero"), a.TermAs[A]("R.one"), a.TermAs[Set[A]]("R.carrier")
			basis, successor := a.TermAs[Fun[Nat, A]]("basis_vector(k)"), a.TermAs[Nat]("suc(k)")
			over := polynomial.BasisVectorOver.Read(ring).At(k)
			powers := a.Have(
				"every power of x lies in c",
				"∀i:num. monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(x, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
			coefficients := a.Have(
				"basis_vector(k) is a polynomial over c, so every coefficient of it lies in c",
				"∀i:num. basis_vector(k, i) ∈ R.carrier",
				By(over, polynomial.PolynomialOverDef.At(zero, c, basis)))
			terms := a.Have(
				"so every term basis_vector(k, i) * x ^ i lies in c",
				"∀i:num. basis_vector(k, i) * monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(coefficients, powers, comm_ring.MulIn.Read(ring)))
			kBelow := a.Have(
				"k lies below suc(k)",
				"k < suc(k)",
				By(nat_order.LessThanSucIffLessEq.At(k, k), nat_order.LessEqRefl))
			offIndex := a.Have(
				"off the index k a term is zero times a power of x, which is zero",
				"∀i:num. i ≠ k ⇒ basis_vector(k, i) * monoid_pow(R.mul, R.one, x, i) = R.zero",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					off := b.Assume()
					power := b.TermAs[A]("monoid_pow(R.mul, R.one, x, i)")
					b.Show(
						"basis_vector(k, i) is zero, and zero times x ^ i, a member of c, is zero",
						By(
							Normalized,
							off,
							vec_space.BasisVectorDef.At(zero, one, k, i),
							powers.At(i),
							comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(power)))
				}))
			among := a.Have(
				"k is one of the indices below suc(k)",
				"k ∈ {i:num | i < suc(k)}",
				BySets(kBelow))
			below := a.TermAs[Set[Nat]]("{i:num | i < suc(k)}")
			term := a.TermAs[Fun[Nat, A]]("λi:num. basis_vector(k, i) * monoid_pow(R.mul, R.one, x, i)")
			power := a.TermAs[A]("monoid_pow(R.mul, R.one, x, k)")
			a.Show(
				"the value is the sum below suc(k), which is its term at k",
				CalcEq(
					// No dimension phantom spells suc(k), so EvalBelow is read at basis_vector(k) untyped.
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < suc(k)}, "+
								"    λi:num. basis_vector(k, i) * monoid_pow(R.mul, R.one, x, i))"),
						"basis_vector(k), zero off k, is a polynomial over c vanishing from suc(k) on",
						By(
							over,
							kBelow,
							vec_space.VecBasisVector.At(zero, one, successor, k),
							x,
							At(Read(EvalBelow, ring), successor, basis, x))),
					Leg(
						a.TermAs[A]("basis_vector(k, k) * monoid_pow(R.mul, R.one, x, k)"),
						"the terms off k vanish, so the sum is its term at k, the ring a module over itself",
						By(
							terms,
							offIndex,
							among,
							num_segment.FiniteBelowStrict.At(successor),
							module.ModuleSumSingle.Read(regular).At(below, k, term))),
					Leg(
						a.TermAs[A]("R.one * monoid_pow(R.mul, R.one, x, k)"),
						"the basis vector is one at k",
						By(Normalized, vec_space.BasisVectorDef.At(zero, one, k, k))),
					FinalLeg(
						"one is the unit of the product",
						By(powers, comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(power))),
				))
		}),
})}

// BinomialValue — the binomial 1 - c Tᵈ takes at a point x of the ring the
// value one less c times the d-th power of x. Evaluation takes the
// difference to the difference of the values (EvalSub) and lets the scalar
// c out (EvalScalar), and Tᵏ takes at x the k-th power of x
// (EvalBasisVector), the zeroth power being one.
var BinomialValue = binomialValueThm{family.Add(registry.ProofEntry{
	Name: "BinomialValue",
	Key:  "prop_f3014657bcbcd226",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀c x:A. ∀d:num.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(basis_vector(0) - c • basis_vector(d), x) = " +
			"R.one - c * monoid_pow(R.mul, R.one, x, d)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], c, x *Member[A, on.R], d *Expr[Nat]) {
			zeroIndex := arg.TermAs[Nat]("0")
			unit, basis :=
				arg.TermAs[Fun[Nat, A]]("basis_vector(0)"), arg.TermAs[Fun[Nat, A]]("basis_vector(d)")
			scaled := arg.TermAs[Fun[Nat, A]]("c • basis_vector(d)")
			over := arg.Have(
				"1 and c times Tᵈ are polynomials over the ring",
				"polynomial_over(R.carrier, basis_vector(0)) ∧ polynomial_over(R.carrier, c • basis_vector(d))",
				By(
					c,
					module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)),
					polynomial.BasisVectorOver.Read(ring).At(zeroIndex),
					polynomial.BasisVectorOver.Read(ring).At(d)))
			arg.Show(
				"evaluation subtracts the values of the two terms and lets the scalar out",
				CalcEq(
					Leg(
						arg.TermAs[A]("polynomial_eval(basis_vector(0), x) - polynomial_eval(c • basis_vector(d), x)"),
						"evaluation takes the difference to the difference of the values",
						By(over, EvalSub.Read(ring).At(unit, scaled, x))),
					FinalLeg(
						"1 takes the value one and Tᵈ the d-th power of x, and c passes out",
						By(
							polynomial.BasisVectorOver.Read(ring).At(d),
							comm_monoid.MonoidPowDef,
							EvalBasisVector.Read(ring).At(zeroIndex, x),
							EvalBasisVector.Read(ring).At(d, x),
							EvalScalar.Read(ring).At(c, x, basis))),
				))
		}),
})}

// EvalPow — evaluation at a point of c takes the n-th power of a
// polynomial over c to the n-th power of its value. By induction on n:
// the zeroth power is the one polynomial (polynomial.PolynomialPowZero), whose value
// is x ^ 0, which is one; the next power is p times the last one
// (polynomial.PolynomialPowSuc), a product of two polynomials over c
// (polynomial.PolynomialPowOver), whose value is the product of the values (EvalMul).
var EvalPow = evalPowThm{family.Add(registry.ProofEntry{
	Name: "EvalPow",
	Key:  "prop_d0c0dabc3d8634a5",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀n:num. ∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(polynomial_pow(p, n), x) = " +
			"monoid_pow(R.mul, R.one, polynomial_eval(p, x), n)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			n *Expr[Nat],
			p *Arrow[Nat, A],
			x *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"and x lies in c")
			pOver, xM := parts[0], a.MemberOf[on.R](x, parts[1])
			a.Induct(n)
			a.Base(
				"the zeroth power is the one polynomial, whose value is x ^ 0, which is one",
				Simp(Fwd(polynomial.PolynomialPowZero.Read(ring)), Fwd(comm_monoid.MonoidPowDef)),
				By(Normalized, EvalBasisVector.Read(ring).At(a.TermAs[Nat]("0"), xM), comm_monoid.MonoidPowDef))
			a.Step(
				"the next power is p times the last one",
				func(b *Argument, previous Fact) {
					power := b.TermAs[Fun[Nat, A]]("polynomial_pow(p, n)")
					b.Show(
						"whose value is the value of p times that of the last power",
						Simp(Fwd(polynomial.PolynomialPowSuc.Read(ring)), Fwd(comm_monoid.MonoidPowDef)),
						By(
							pOver,
							previous,
							polynomial.PolynomialPowOver.Read(ring).At(n, p),
							EvalMul.Read(ring).At(p, power, xM)))
				})
		}),
})}

// EvalScalar — evaluation commutes with scaling. With p an n-vector, a • p
// is one too (VecSmulOn) and a polynomial over c, the polynomials over c a
// module over the ring on c, so both values are their sums below n
// (EvalBelow). Each term (a * p(i)) x ^ i regroups to a (p(i) x ^ i), and
// the factor a, a member of c, passes out of the finite sum.
var EvalScalar = evalScalarThm{family.Add(registry.ProofEntry{
	Name: "EvalScalar",
	Key:  "prop_98f8a9484c6181a8",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀a x:A. ∀p:(num → A).",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"x ∈ R.carrier",
			"polynomial_over(R.carrier, p)",
		},
		Conclusion: "polynomial_eval(a • p, x) = a * polynomial_eval(p, x)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			a, x *Expr[A],
			p *Arrow[Nat, A],
			hypotheses Fact,
		) {
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			parts := arg.Conjuncts(
				hypotheses,
				"a lies in c",
				"so does x",
				"and p is a polynomial over c")
			aIn, xIn, pOver := parts[0], parts[1], parts[2]
			aM, xM := arg.MemberOf[on.R](a, aIn), arg.MemberOf[on.R](x, xIn)
			definition := arg.Conjuncts(
				arg.Unfolded(pOver, polynomial.PolynomialOverDef),
				"p vanishes from some index on",
				"and every coefficient of p lies in c")
			n, pVec := arg.UnpackAs[Nat](definition[0])
			coefficients := definition[1]
			powers := arg.Have(
				"every power of x lies in c",
				"∀i:num. monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(xIn, comm_monoid.PowIn.Read(mulMonoid)))
			pBelow := proof.InhabitFrom(p, pVec)
			scaledPast := arg.Have(
				"a • p vanishes from n on as well, a lying in c",
				"vec⟨n⟩(a • p)",
				By(vec_space.VecSmulOn.Read(ring).At(aM, pBelow)))
			scaledOver := arg.Have(
				"and it is a polynomial over c, the polynomials over c a module over the ring on c",
				"polynomial_over(R.carrier, a • p)",
				BySets(module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ring)), aIn, pOver))
			regroup := arg.Have(
				"each term (a * p(i)) x ^ i regroups to a (p(i) x ^ i)",
				"∀i:num.(a • p)(i) * monoid_pow(R.mul, R.one, x, i) = a * (p(i) * monoid_pow(R.mul, R.one, x, i))",
				Simp(Fwd(vec_space.VecScalarMulDef)),
				By(aIn, coefficients, powers, comm_monoid.AssocOn.Read(mulMonoid)))
			terms := arg.Have(
				"the terms p(i) x ^ i lie in c",
				"∀i:num. p(i) * monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(coefficients, powers, comm_ring.MulIn.Read(ring)))
			below := arg.TermAs[Set[Nat]]("{i:num | i < n}")
			term := arg.TermAs[Fun[Nat, A]]("λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)")
			arg.Show(
				"both values are sums below n, and a passes out of the second",
				CalcEq(
					Leg(
						arg.TermAs[A](
							"module_sum(R.add, R.zero, {i:num | i < n}, λi:num.(a • p)(i) * monoid_pow(R.mul, R.one, x, i))"),
						"a • p is a polynomial over c vanishing from n on",
						By(
							scaledOver,
							EvalBelow.Read(ring).At(proof.InhabitFrom(arg.TermAs[Fun[Nat, A]]("a • p"), scaledPast), xM))),
					Leg(
						arg.TermAs[A](
							"module_sum(R.add, R.zero, {i:num | i < n}, λi:num. a * (p(i) * monoid_pow(R.mul, R.one, x, i)))"),
						"regroup each term",
						By(regroup, module.ModuleSumCongruence)),
					Leg(
						arg.TermAs[A](
							"a * module_sum(R.add, R.zero, {i:num | i < n}, λi:num. p(i) * monoid_pow(R.mul, R.one, x, i))"),
						"a factor in c passes out of a finite sum, the ring a module over itself",
						By(
							terms,
							num_segment.FiniteBelowStrict.At(n),
							module.ModuleSumSmul.Read(module.RegularModuleOn.Read(ring)).At(
								below, arg.MemberOf[on.R](a, aIn), term))),
					FinalLeg(
						"which is a times the value of p, its sum below n",
						By(pOver, EvalBelow.Read(ring).At(pBelow, xM))),
				))
		}),
})}

// EvalAtScaledPoint — p(s·x) is the value at x of the polynomial with
// coefficients p(i)·sⁱ. Both values are sums below deg p + 1, the weighted
// polynomial vanishing where p does, and term by term p(i)·(s·x)ⁱ is
// p(i)·sⁱ·xⁱ.
var EvalAtScaledPoint = evalAtScaledPointThm{family.Add(registry.ProofEntry{
	Name: "EvalAtScaledPoint",
	Key:  "prop_a0780c91ac015775",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p:(num → A). ∀s x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"s ∈ R.carrier",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, s * x) = polynomial_eval(«weighted», x)",
		Abbrev: Abbrev{
			{Name: "weighted", Text: "λi:num. p(i) * monoid_pow(R.mul, R.one, s, i)"},
		},
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			s, x *Expr[A],
			hypotheses Fact,
		) {
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			parts := arg.Conjuncts(
				hypotheses,
				"p is a polynomial over the carrier",
				"s lies in it",
				"and so does x")
			pOver, sIn, xIn := parts[0], parts[1], parts[2]
			xM := arg.MemberOf[on.R](x, xIn)
			zero := arg.TermAs[A]("R.zero")
			carrier := arg.TermAs[Set[A]]("R.carrier")
			weighted := arg.TermAs[Fun[Nat, A]]("«weighted»")
			coefficients := polynomial.CoefficientIn.Read(pOver)
			pPast := arg.Have(
				"p vanishes past its degree",
				"vec⟨suc(polynomial_degree(p))⟩(p)",
				By(pOver, polynomial.DegreeVec.At(zero, carrier, p)))
			pastValues := arg.Unfolded(pPast, vec_space.VecDef)
			weightedPast := arg.Have(
				"so does the weighted polynomial, a weight times zero being zero",
				"vec⟨suc(polynomial_degree(p))⟩(«weighted»)",
				Simp(Fwd(vec_space.VecDef)),
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					past := b.Assume()
					vanishes := b.Have(
						"p vanishes at i",
						"p(i) = R.zero",
						By(past, pastValues.At(i)))
					b.Show(
						"so the weighted coefficient is zero times a power of s",
						ByArith(
							ring,
							sIn,
							Scaled(b.TermAs[A]("monoid_pow(R.mul, R.one, s, i)"), vanishes),
							coefficients.At(i),
							comm_monoid.PowIn.Read(mulMonoid).AsFact().At(s, i)))
				}))
			weightedCoefficients := arg.Have(
				"its coefficients lie in the carrier, each a coefficient of p times a power of s",
				"∀i:num. «weighted»(i) ∈ R.carrier",
				By(sIn, coefficients, comm_monoid.PowIn.Read(mulMonoid), comm_ring.MulIn.Read(ring)))
			weightedOver := arg.Have(
				"so it is a polynomial over the carrier",
				"polynomial_over(R.carrier, «weighted»)",
				By(weightedPast, weightedCoefficients, polynomial.PolynomialOverDef))
			scaled := arg.MemberOf[on.R](
				arg.TermAs[A]("s * x"),
				arg.Have(
					"s·x lies in the carrier",
					"s * x ∈ R.carrier",
					By(sIn, xIn, comm_ring.MulIn.Read(ring))))
			regroup := arg.Have(
				"each term of p at s·x is the weighted term at x, (s·x)ⁱ being sⁱ·xⁱ",
				"∀i:num. "+
					"    p(i) * monoid_pow(R.mul, R.one, s * x, i) = «weighted»(i) * monoid_pow(R.mul, R.one, x, i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"(s·x)ⁱ = sⁱ·xⁱ, then regroup",
						ByArith(
							ring,
							sIn,
							xIn,
							coefficients.At(i),
							Scaled(b.TermAs[A]("p(i)"), comm_monoid.MulPowOn.Read(mulMonoid).AsFact().At(s, x, i))))
				}))
			arg.Show(
				"both values are sums below deg p + 1 that agree term by term",
				CalcEq(
					Leg(
						arg.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < suc(polynomial_degree(p))}, "+
								"    λi:num. p(i) * monoid_pow(R.mul, R.one, s * x, i))"),
						"p vanishes past its degree",
						By(pOver, EvalBelow.Read(ring).At(proof.InhabitFrom(p, pPast), scaled))),
					Leg(
						arg.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < suc(polynomial_degree(p))}, "+
								"    λi:num. «weighted»(i) * monoid_pow(R.mul, R.one, x, i))"),
						"regroup each term",
						By(regroup, module.ModuleSumCongruence)),
					FinalLeg(
						"which is the value of the weighted polynomial, a sum below deg p + 1",
						By(weightedOver, EvalBelow.Read(ring).At(proof.InhabitFrom(weighted, weightedPast), xM))),
				))
		}),
})}

// EvalRescaled — for p of degree at most n, the polynomial whose i-th
// coefficient is s^(e(n−i))·p(i) up to n takes at s^e·x the value
// s^(en)·p(x). Its value at s^e·x is the value at x of the polynomial with
// coefficients weighted by the powers of s^e (EvalAtScaledPoint), and the
// weighted coefficients are s^(en)·p(i): up to n the powers of s add up to
// s^(en), and past n both vanish. So the value is that of s^(en)·p at x,
// which is s^(en)·p(x) (EvalScalar).
var EvalRescaled = evalRescaledThm{family.Add(registry.ProofEntry{
	Name: "EvalRescaled",
	Key:  "prop_12e62c4d92f8d0",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀n e:num. ∀s x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_degree(p) ≤ n",
			"s ∈ R.carrier",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(«rescaled», monoid_pow(R.mul, R.one, s, e) * x) = " +
			"monoid_pow(R.mul, R.one, s, e * n) * polynomial_eval(p, x)",
		Abbrev: Abbrev{
			{Name: "rescaled", Text: "λi:num. " +
				"    COND(i ≤ n, monoid_pow(R.mul, R.one, s, e * (n - i)) * p(i), R.zero)"},
		},
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			n, e *Expr[Nat],
			s, x *Expr[A],
			hypotheses Fact,
		) {
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			parts := arg.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"of degree at most n",
				"s lies in c",
				"and so does x")
			pOver, degree, sIn, xIn := parts[0], parts[1], parts[2], parts[3]
			sM, xM := arg.MemberOf[on.R](s, sIn), arg.MemberOf[on.R](x, xIn)
			zero := arg.TermAs[A]("R.zero")
			carrier := arg.TermAs[Set[A]]("R.carrier")
			rescaled := arg.TermAs[Fun[Nat, A]]("«rescaled»")
			coefficients := polynomial.CoefficientIn.Read(pOver)
			pastValues := arg.Unfolded(
				arg.Have(
					"p vanishes past n, its degree being at most n",
					"vec⟨suc(n)⟩(p)",
					By(
						pOver,
						degree,
						polynomial.DegreeVec.At(zero, carrier, p),
						vec_space.VecMono.At(
							zero, arg.TermAs[Nat]("suc(polynomial_degree(p))"), arg.TermAs[Nat]("suc(n)"), p),
						nat_order.SucLessEqSucIff)),
				vec_space.VecDef)
			rescaledPast := arg.Have(
				"so does the rescaled polynomial, its condition failing there",
				"vec⟨suc(n)⟩(«rescaled»)",
				ByArith(vec_space.VecDef))
			rescaledCoefficients := arg.Have(
				"its coefficients lie in c, each a power of s times a coefficient of p, or zero",
				"∀i:num. «rescaled»(i) ∈ R.carrier",
				By(
					sIn,
					coefficients,
					comm_monoid.PowIn.Read(mulMonoid),
					comm_ring.MulIn.Read(ring),
					comm_ring.ZeroIn.Read(ring)))
			rescaledOver := arg.Have(
				"so it is a polynomial over c",
				"polynomial_over(R.carrier, «rescaled»)",
				By(rescaledPast, rescaledCoefficients, polynomial.PolynomialOverDef))
			weights := arg.Have(
				"weighted by the powers of s^e, the rescaled coefficients are s^(en)·p(i)",
				"∀i:num. "+
					"    «rescaled»(i) * monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, s, e), i) = "+
					"    monoid_pow(R.mul, R.one, s, e * n) * p(i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Cases(b.TermAs[Bool]("i ≤ n"))
					b.When(
						"up to n the powers of s add up to s^(en)",
						func(c *Argument, atMost Fact) {
							exponents := c.Have(
								"the exponents of s add up to e·n",
								"e * (n - i) + e * i = e * n",
								ByArith(atMost, Scaled(e, nat_monus.SubAddCancel.At(n, i))))
							c.Show(
								"the condition holds, (s^e)^i is s^(ei), and s^(e(n−i))·s^(ei) is s^(en)",
								CalcEq(
									Leg(
										c.TermAs[A](
											"(monoid_pow(R.mul, R.one, s, e * (n - i)) * p(i)) * monoid_pow(R.mul, R.one, s, e * i)"),
										"i is at most n, and a power of a power multiplies the exponents",
										By(atMost, sIn, comm_monoid.PowPowOn.Read(mulMonoid).AsFact().At(s, e, i))),
									Leg(
										c.TermAs[A](
											"(monoid_pow(R.mul, R.one, s, e * (n - i)) * monoid_pow(R.mul, R.one, s, e * i)) * p(i)"),
										"regroup the three factors",
										ByArith(ring, sIn, coefficients.At(i))),
									FinalLeg(
										"the powers of s multiply to s^(en)",
										By(
											exponents,
											sIn,
											comm_monoid.PowAddOn.Read(mulMonoid).AsFact().At(
												s, c.TermAs[Nat]("e * (n - i)"), c.TermAs[Nat]("e * i")))),
								))
						})
					b.Otherwise(
						"past n both coefficients vanish",
						func(c *Argument, notAtMost Fact) {
							beyond := c.Have(
								"i lies past n",
								"suc(n) ≤ i",
								ByArith(notAtMost))
							vanishes := c.Have(
								"p vanishes at i",
								"p(i) = R.zero",
								By(beyond, pastValues.At(i)))
							c.Show(
								"the rescaled coefficient is zero by its condition, and s^(en) times zero is zero",
								ByArith(
									ring,
									sIn,
									coefficients.At(i),
									notAtMost,
									Scaled(c.TermAs[A]("monoid_pow(R.mul, R.one, s, e * n)"), vanishes)))
						})
				}))
			arg.Show(
				"evaluated at s^e·x, the rescaled polynomial is weighted into s^(en)·p",
				CalcEq(
					Leg(
						arg.TermAs[A](
							"polynomial_eval( "+
								"    λi:num. «rescaled»(i) * monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, s, e), i), x)"),
						"its value at s^e·x is the value at x with the i-th coefficient weighted by (s^e)^i",
						By(
							rescaledOver,
							EvalAtScaledPoint.Read(ring).At(rescaled, comm_monoid.PowIn.Read(mulMonoid).At(sM, e), xM))),
					Leg(
						arg.TermAs[A]("polynomial_eval(monoid_pow(R.mul, R.one, s, e * n) • p, x)"),
						"the weighted coefficients are s^(en)·p(i)",
						By(weights, vec_space.VecScalarMulDef)),
					FinalLeg(
						"and s^(en) passes out of the value",
						By(
							pOver,
							EvalScalar.Read(ring).At(
								comm_monoid.PowIn.Read(mulMonoid).At(sM, arg.TermAs[Nat]("e * n")), xM, p))),
				))
		}),
})}

// EvalSub — evaluation at a point of the ring takes a difference of
// polynomials to the difference of their values. The polynomials form a
// ring, so p − q is a polynomial; p is p − q plus q, and evaluation takes
// that sum to the sum of the values (EvalAdd), so the value of p − q is the
// value of p less that of q.
var EvalSub = evalSubThm{family.Add(registry.ProofEntry{
	Name: "EvalSub",
	Key:  "prop_43465d834eefbdd0",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p - q, x) = polynomial_eval(p, x) - polynomial_eval(q, x)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			p, q *Arrow[Nat, A],
			x *Expr[A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"p is a polynomial over the ring",
				"so is q",
				"and x lies in the ring")
			pOver, qOver, xIn := parts[0], parts[1], parts[2]
			xM := arg.MemberOf[on.R](x, xIn)
			difference := arg.TermAs[Fun[Nat, A]]("p - q")
			coefficients := arg.Have(
				"every coefficient of p and of q lies in the ring",
				"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier",
				By(pOver, qOver, polynomial.PolynomialOverDef))
			differenceOver := arg.Have(
				"p − q is a polynomial over the ring, the polynomials forming a ring",
				"polynomial_over(R.carrier, p - q)",
				By(pOver, qOver, comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring))))
			regroup := arg.Have(
				"p is p − q plus q, coefficient by coefficient",
				"p - q + q = p",
				Derive(func(arg *Argument) {
					arg.Do(Funext())
					i := arg.FixAs[Nat]("i")
					arg.Show(
						"a less b, plus b, is a",
						Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecSubDef)),
						ByArith(ring, coefficients.At(i)))
				}))
			split := arg.Have(
				"so the value of p is the value of p − q plus that of q",
				"polynomial_eval(p, x) = polynomial_eval(p - q, x) + polynomial_eval(q, x)",
				By(regroup, differenceOver, qOver, EvalAdd.Read(ring).At(difference, q, xM)))
			values := arg.Have(
				"the three values lie in the ring",
				"polynomial_eval(p, x) ∈ R.carrier ∧ "+
					"polynomial_eval(p - q, x) ∈ R.carrier ∧ "+
					"polynomial_eval(q, x) ∈ R.carrier",
				By(pOver, qOver, differenceOver, xIn, EvalIn.Read(ring)))
			arg.Show(
				"which makes the value of p − q the difference of the values",
				ByArith(ring, split, values))
		}),
})}

// EvalConstant — a constant polynomial takes its constant as its value
// everywhere: k • basis_vector(0) evaluates to k times the value of the
// one polynomial (EvalScalar), which is x ^ 0 = one (EvalBasisVector).
var EvalConstant = evalConstantThm{family.Add(registry.ProofEntry{
	Name: "EvalConstant",
	Key:  "prop_60b6cef4d9e68ff9",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀k x:A.",
		Hypotheses: []string{
			"k ∈ R.carrier",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(k • basis_vector(0), x) = k",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], k, x *Member[A, on.R]) {
			zeroth, onePolynomial := a.TermAs[Nat]("0"), a.TermAs[Fun[Nat, A]]("basis_vector(0)")
			a.Show(
				"the value is k times that of the one polynomial, x ^ 0 = R.one",
				CalcEq(
					Leg(
						a.TermAs[A]("k * polynomial_eval(basis_vector(0), x)"),
						"k passes out of the value",
						By(
							polynomial.BasisVectorOver.Read(ring).At(zeroth),
							EvalScalar.Read(ring).At(k, x, onePolynomial))),
					Leg(
						a.TermAs[A]("k * R.one"),
						"the one polynomial evaluates to x ^ 0, which is one",
						Simp(Fwd(EvalBasisVector.Read(ring)), Fwd(comm_monoid.MonoidPowDef)),
						Basic()),
					FinalLeg(
						"and one is the unit of the product",
						ByArith(ring, k)),
				))
		}),
})}

// DegreeZeroEval — a polynomial of degree 0 takes its constant coefficient
// as its value at every point: it is the constant polynomial of p(0)
// (polynomial.DegreeZeroConstant), and a constant polynomial takes its constant as
// its value (EvalConstant).
var DegreeZeroEval = degreeZeroEvalThm{family.Add(registry.ProofEntry{
	Name: "DegreeZeroEval",
	Key:  "prop_9662ef8ea8c28bca",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_degree(p) = 0",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, x) = p(0)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			over, degreeZero Fact,
			x *Member[A, on.R],
		) {
			coefficientIn := a.Have(
				"its constant coefficient p(0) lies in c",
				"p(0) ∈ R.carrier",
				By(over, polynomial.PolynomialOverDef))
			coefficient := a.MemberOf[on.R](p.Apply(a.TermAs[Nat]("0")), coefficientIn)
			a.Show(
				"p is the constant polynomial of p(0), and that polynomial takes the value p(0)",
				By(
					Normalized,
					over,
					degreeZero,
					polynomial.DegreeZeroConstant.Read(ring).At(p),
					EvalConstant.Read(ring).At(coefficient, x)))
		}),
})}

// EvalVecZero — the zero polynomial takes the value zero at every point
// of c: evaluation at x is a ring homomorphism (EvalHomomorphism), and a
// ring homomorphism keeps the zero.
var EvalVecZero = evalVecZeroThm{family.Add(registry.ProofEntry{
	Name: "EvalVecZero",
	Key:  "prop_f93224f9e770508a",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(vec_zero, x) = R.zero",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], x *Member[A, on.R]) {
			evaluation := a.Have(
				"evaluation at x is a ring homomorphism",
				"ring_homomorphism(polynomial_ring(R), R, λq:(num → A). polynomial_eval(q, x))",
				By(x, EvalHomomorphism.Read(ring).At(x)))
			a.Show(
				"which sends the zero polynomial to zero",
				By(ring_homomorphism.MapZero.Read(evaluation)))
		}),
})}

// EvalMulRoot — a root of p is a root of each multiple of p, on either
// side: the value of a product is the product of the values (EvalMul),
// and one factor of it is zero.
var EvalMulRoot = evalMulRootThm{family.Add(registry.ProofEntry{
	Name: "EvalMulRoot",
	Key:  "prop_9f49f30356fce9bb",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p q:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"x ∈ R.carrier",
			"polynomial_eval(p, x) = R.zero",
		},
		Conclusion: "polynomial_eval(polynomial_mul(p, q), x) = R.zero ∧ " +
			"polynomial_eval(polynomial_mul(q, p), x) = R.zero",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p, q *Arrow[Nat, A],
			x *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"so is q",
				"x lies in c",
				"and p vanishes at x")
			pOver, qOver, xIn, root := parts[0], parts[1], parts[2], parts[3]
			xM := a.MemberOf[on.R](x, xIn)
			valueIn := a.Have(
				"q's value at x lies in c",
				"polynomial_eval(q, x) ∈ R.carrier",
				By(qOver, EvalIn.Read(ring).At(q, xM)))
			pTimesQ := a.Have(
				"the value of p q at x is p(x) q(x)",
				"polynomial_eval(polynomial_mul(p, q), x) = polynomial_eval(p, x) * polynomial_eval(q, x)",
				By(pOver, qOver, EvalMul.Read(ring).At(p, q, xM)))
			qTimesP := a.Have(
				"and that of q p is q(x) p(x)",
				"polynomial_eval(polynomial_mul(q, p), x) = polynomial_eval(q, x) * polynomial_eval(p, x)",
				By(pOver, qOver, EvalMul.Read(ring).At(q, p, xM)))
			qValue := a.MemberOf[on.R](a.TermAs[A]("polynomial_eval(q, x)"), valueIn)
			a.Show(
				"each is a product with the factor p(x), which is zero",
				SplitConj(
					Case(
						"zero times q(x) is zero",
						By(root, pTimesQ, comm_ring.MulLeftZeroOn.Read(ring).At(qValue))),
					Case(
						"and so is q(x) times zero",
						By(root, qTimesP, comm_ring.MulRightZeroOn.Read(ring).At(qValue))),
				))
		}),
})}

// DivisionValue — evaluation at a point of the ring turns a division into an
// identity between values: f = g q + r gives f(x) = g(x) q(x) + r(x), since
// evaluation at x adds and multiplies.
var DivisionValue = divisionValueThm{family.Add(registry.ProofEntry{
	Name: "DivisionValue",
	Key:  "prop_edf509971b75bacc",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f g q r:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, g)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, r)",
			"x ∈ R.carrier",
			"f = polynomial_mul(g, q) + r",
		},
		Conclusion: "polynomial_eval(f, x) = " +
			"polynomial_eval(g, x) * polynomial_eval(q, x) + polynomial_eval(r, x)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			f, g, q, r *Arrow[Nat, A],
			x *Member[A, on.R],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"g is a polynomial over the ring",
				"so is q",
				"and r",
				"f = g q + r")
			gOver, qOver, rOver, divided := parts[0], parts[1], parts[2], parts[3]
			a.Show(
				"evaluation at x adds and multiplies",
				divided.Rw(),
				By(
					gOver,
					qOver,
					rOver,
					polynomial.PolynomialMulOver.Read(ring).At(g, q),
					EvalAdd.Read(ring).At(a.TermAs[Fun[Nat, A]]("polynomial_mul(g, q)"), r, x),
					EvalMul.Read(ring).At(g, q, x)))
		}),
})}

// DivisionValueAtRoot — at a root of the divisor the dividend takes the
// remainder's value: f = g q + r and g(x) = zero give f(x) = r(x), the
// value of g q vanishing there (DivisionValue).
var DivisionValueAtRoot = divisionValueAtRootThm{family.Add(registry.ProofEntry{
	Name: "DivisionValueAtRoot",
	Key:  "prop_7122896c0a757b1b",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f g q r:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, g)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, r)",
			"x ∈ R.carrier",
			"f = polynomial_mul(g, q) + r",
			"polynomial_eval(g, x) = R.zero",
		},
		Conclusion: "polynomial_eval(f, x) = polynomial_eval(r, x)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			f, g, q, r *Arrow[Nat, A],
			x *Member[A, on.R],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"g is a polynomial over the ring",
				"so is q",
				"and r",
				"f = g q + r",
				"x is a root of g")
			gOver, qOver, rOver, divided, root := parts[0], parts[1], parts[2], parts[3], parts[4]
			value := a.Have(
				"f(x) = g(x) q(x) + r(x)",
				"polynomial_eval(f, x) = polynomial_eval(g, x) * polynomial_eval(q, x) + polynomial_eval(r, x)",
				By(gOver, qOver, rOver, divided, DivisionValue.Read(ring).At(f, g, q, r, x)))
			a.Show(
				"g(x) being zero, that is zero times q(x) plus r(x), which is r(x)",
				value.Rw(),
				root.Rw(),
				ByArith(ring, EvalIn.Read(ring).At(q, x), EvalIn.Read(ring).At(r, x), qOver, rOver))
		}),
})}

// EvalIn — a polynomial over c takes its values at points of c in c.
// With p vanishing from n on, its value is the sum of p(i) * x ^ i over
// the indices below n (EvalBelow); each term lies in c, as its
// coefficient and the power of x do and c is closed under the product,
// and a finite sum of members of c lies in c, the ring a module over
// itself.
var EvalIn = evalInThm{family.Add(registry.ProofEntry{
	Name: "EvalIn",
	Key:  "prop_e79fea3acae870fb",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(p, x) ∈ R.carrier",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			x *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"p is a polynomial over c",
				"and x lies in c")
			pOver, xIn := parts[0], parts[1]
			definition := a.Conjuncts(
				a.Unfolded(pOver, polynomial.PolynomialOverDef),
				"p vanishes from some index on",
				"and every coefficient of p lies in c")
			n, pVec := a.UnpackAs[Nat](definition[0])
			coefficients := definition[1]
			powers := a.Have(
				"every power of x lies in c",
				"∀i:num. monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(xIn, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
			terms := a.Have(
				"so every term p(i) x ^ i lies in c, a product of two members of c",
				"∀i:num. p(i) * monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(coefficients, powers, comm_ring.MulIn.Read(ring)))
			value := a.Have(
				"the value of p is its sum below n",
				"polynomial_eval(p, x) = "+
					"module_sum(R.add, R.zero, {i:num | i < n}, λi:num. p(i) * monoid_pow(R.mul, R.one, x, i))",
				By(pOver, EvalBelow.Read(ring).At(proof.InhabitFrom(p, pVec), a.MemberOf[on.R](x, xIn))))
			a.Show(
				"a finite sum of members of c lies in c, the ring a module over itself",
				value.Rw(),
				By(
					terms,
					module.ModuleSumIn.Read(module.RegularModuleOn.Read(ring)).At(a.TermAs[Set[Nat]]("{i:num | i < n}"),
						a.TermAs[Fun[Nat, A]]("λi:num. p(i) * monoid_pow(R.mul, R.one, x, i)")),
					num_segment.FiniteBelowStrict.At(n)))
		}),
})}

// EvalHomomorphism — evaluation at a point of c is a ring homomorphism
// from the polynomials over c to c. Of its six conditions the ring on c is
// the hypothesis; the others: the polynomials over c form a ring, the
// values lie in c, evaluation is additive and multiplicative, and the one
// polynomial — the zeroth power of the variable — evaluates to x ^ 0 = one.
var EvalHomomorphism = evalHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "EvalHomomorphism",
	Key:  "prop_c9e42d8387e26c9e",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "ring_homomorphism(polynomial_ring(R), R, λp:(num → A). polynomial_eval(p, x))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], x *Member[A, on.R]) {
			a.Show(
				"evaluation keeps the carrier, sums, products and one",
				Unfold(ring_homomorphism.RingHomomorphism),
				SplitConjAll(
					Case(
						"the polynomials over c form a ring",
						By(polynomial.PolynomialRingOn.Read(ring))),
					Case(
						"c is a ring, the hypothesis",
						By(ring)),
					Case(
						"a polynomial over c takes its value at x in c",
						BySets(EvalIn.Read(ring), x)),
					Case(
						"evaluation is additive",
						BySets(EvalAdd.Read(ring), x)),
					Case(
						"evaluation is multiplicative",
						BySets(EvalMul.Read(ring), x)),
					Case(
						"the one polynomial evaluates to x ^ 0, which is one",
						Simp(Fwd(EvalBasisVector.Read(ring)), Fwd(comm_monoid.MonoidPowDef)),
						Basic()),
				))
		}),
})}

// EvalAlongHomomorphism — a ring homomorphism carries the value of a
// polynomial at a point to the value, at the image of the point, of the
// polynomial whose coefficients are the images of the coefficients. Both
// values are sums below one length n past which p vanishes, and f carries
// the first sum term by term onto the second, so a coefficient that f
// sends to S.zero needs no case of its own.
var EvalAlongHomomorphism = evalAlongHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "EvalAlongHomomorphism",
	Key:  "prop_19f81d2518fe07c3",
	Reading: "The mapped coefficients are again a vector: " +
		"past p's length they are f(R.zero), which is S.zero.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀p:(num → A). ∀x:A.",
		Hypotheses: []string{
			"ring_homomorphism(R, S, f)",
			"polynomial_over(R.carrier, p)",
			"x ∈ R.carrier",
		},
		Conclusion: "f(polynomial_eval(p, x)) = polynomial_eval(λi:num. f(p(i)), f(x))",
		Abbrev: Abbrev{
			{Name: "targetPowers", Text: "monoid_pow(S.mul, S.one, f(x))"},
			{Name: "mappedCoefficients", Text: "λi:num. f(p(i))"},
			{Name: "sourceTerms", Text: "λi:num. R.mul(p(i), monoid_pow(R.mul, R.one, x, i))"},
			{Name: "imageTerms", Text: "λi:num. f(«sourceTerms»(i))"},
			{Name: "targetTerms", Text: "λi:num. S.mul(«mappedCoefficients»(i), «targetPowers»(i))"},
			{Name: "below", Text: "λn:num. {i:num | i < n}"},
		},
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Expr[RingOps[B]],
			f *Arrow[A, B],
			p *Arrow[Nat, A],
			x *Expr[A],
			hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
			pOver, xIn Fact,
		) {
			source, target := ring_homomorphism.Source.Read(hom), ring_homomorphism.Target.Read(hom)
			xM := a.MemberOf[on.R](x, xIn)
			zeroImage := a.Have(
				"f sends zero to zero",
				"f(R.zero) = S.zero",
				By(ring_homomorphism.MapZero.Read(hom)))
			powersIn := a.Have(
				"every power of x lies in the source carrier",
				"∀i:num. monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(xIn, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(source))))
			powerImages := a.Have(
				"f carries each power of x to the corresponding power of f(x)",
				"∀i:num. f(monoid_pow(R.mul, R.one, x, i)) = «targetPowers»(i)",
				Derive(func(b *Argument) {
					b.Induct("i")
					b.Base(
						"the zeroth powers are the identities, which f preserves",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(ring_homomorphism.MapOne.Read(hom)))
					b.Step(
						"one more factor is carried through the product by multiplicativity",
						func(c *Argument, ih Fact) {
							i := c.TermAs[Nat]("i")
							c.Show(
								"the homomorphism keeps the successor power",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								By(powersIn.At(i), ih, xIn, ring_homomorphism.MapMul.Read(hom)))
						})
				}))
			overParts := a.Conjuncts(
				a.Unfolded(pOver, polynomial.PolynomialOverDef),
				"p vanishes from some index on",
				"and every coefficient lies in the source carrier")
			n, pVec := a.UnpackAs[Nat](overParts[0])
			coefficients := overParts[1]
			mappedSupport := a.Have(
				"the mapped coefficients vanish from the same index on",
				"vec⟨n⟩(«mappedCoefficients»)",
				By(
					zeroImage,
					polynomial.VecMap.At(f, a.TermAs[A]("R.zero"), a.TermAs[B]("S.zero"), proof.InhabitFrom(p, pVec))))
			mappedIn := a.Have(
				"each mapped coefficient lies in the target carrier",
				"∀i:num. «mappedCoefficients»(i) ∈ S.carrier",
				By(coefficients, ring_homomorphism.MapIn.Read(hom)))
			mapped := a.TermAs[Fun[Nat, B]]("«mappedCoefficients»")
			mappedOver := a.Have(
				"finite support and target coefficients make the image a polynomial over S",
				"polynomial_over(S.carrier, «mappedCoefficients»)",
				By(
					mappedIn,
					mappedSupport,
					polynomial.PolynomialOverDef.At(a.TermAs[B]("S.zero"), a.TermAs[Set[B]]("S.carrier"), mapped)))
			summandsIn := a.Have(
				"each evaluation summand lies in the source carrier",
				"∀i:num. «sourceTerms»(i) ∈ R.carrier",
				By(coefficients, powersIn, comm_ring.MulIn.Read(source)))
			termImages := a.Have(
				"f carries each evaluation summand to its target summand",
				"∀i:num. «imageTerms»(i) = «targetTerms»(i)",
				a.ForEach(func(i *Expr[Nat]) Action {
					return By(powerImages.At(i), coefficients.At(i), powersIn.At(i), ring_homomorphism.MapMul.Read(hom))
				}))
			xImageIn := a.Have(
				"the evaluation point maps into the target carrier",
				"f(x) ∈ S.carrier",
				By(ring_homomorphism.MapIn.Read(hom).At(xM)))
			indices := a.TermAs[Set[Nat]]("«below»(n)")
			sourceTerms := a.TermAs[Fun[Nat, A]]("«sourceTerms»")
			imageTerms, targetTerms :=
				a.TermAs[Fun[Nat, B]]("«imageTerms»"), a.TermAs[Fun[Nat, B]]("«targetTerms»")
			targetAdd, targetZero := a.TermAs[Op[B]]("S.add"), a.TermAs[B]("S.zero")
			a.Show(
				"the two finite evaluation sums correspond under f",
				CalcEq(
					Leg(
						a.TermAs[B]("f(module_sum(R.add, R.zero, «below»(n), «sourceTerms»))"),
						"evaluation in R is the sum below n",
						By(pOver, EvalBelow.Read(source).At(proof.InhabitFrom(p, pVec), xM))),
					Leg(
						a.TermAs[B]("module_sum(S.add, S.zero, «below»(n), «imageTerms»)"),
						"f carries the finite sum through its additive monoid homomorphism",
						By(
							summandsIn,
							zeroImage,
							ring_homomorphism.MapAdd.Read(hom),
							num_segment.FiniteBelowStrict.At(n),
							module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(source)).At(
								targetAdd, targetZero, f, indices, sourceTerms))),
					Leg(
						a.TermAs[B]("module_sum(S.add, S.zero, «below»(n), «targetTerms»)"),
						"the transported sum agrees term by term with the summands of evaluation in S",
						By(
							termImages,
							module.ModuleSumCongruence.At(targetAdd, targetZero, indices, imageTerms, targetTerms))),
					FinalLeg(
						"evaluation in S is the sum over the same segment",
						By(
							mappedOver,
							EvalBelow.Read(target).At(
								proof.InhabitFrom(mapped, mappedSupport), a.MemberOf[on.S](f.Apply(x), xImageIn)))),
				))
		}),
})}

// MappedEvaluationHomomorphism — moving the coefficients of a polynomial along f and
// evaluating at a point y of T is a ring homomorphism out of the polynomial ring, the
// coefficient map followed by evaluation at y, and it extends f and sends the variable
// to y.
var MappedEvaluationHomomorphism = mappedEvaluationHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "MappedEvaluationHomomorphism",
	Key:  "prop_c526ab142dc1df14",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀T:ring_ops(B). ∀f:(A → B). ∀y:B.",
		Hypotheses: []string{"ring_homomorphism(R, T, f)", "y ∈ T.carrier"},
		Conclusion: "ring_homomorphism(polynomial_ring(R), T, «value») ∧ " +
			"(∀c:A. c ∈ R.carrier ⇒ «value»(vec_scalar_mul(c, basis_vector(R.zero, R.one, 0))) = f(c)) ∧ " +
			"«value»(basis_vector(R.zero, R.one, 1)) = y",
		Abbrev: Abbrev{
			{Name: "value", Text: "λp:(num → A). polynomial_eval(λi:num. f(p(i)), y)"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T *Expr[RingOps[B]],
		f *Arrow[A, B],
		y *Expr[B],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.T],
		yIn Fact,
	) {
		source, target := ring_homomorphism.Source.Read(hom), ring_homomorphism.Target.Read(hom)
		yT := a.MemberOf[on.T](y, yIn)
		units := a.Have(
			"f keeps zero and one",
			"f(R.zero) = T.zero ∧ f(R.one) = T.one",
			By(ring_homomorphism.MapZero.Read(hom), ring_homomorphism.MapOne.Read(hom)))
		evaluation := a.Have(
			"move the coefficients, then evaluate at y",
			"ring_homomorphism(polynomial_ring(R), T, «value»)",
			By(
				CoefficientMapHomomorphism.At(R, T, f),
				EvalHomomorphism.Read(target).At(yT),
				ring_homomorphism.RingHomCompose.At(
					a.TermAs[RingOps[Fun[Nat, A]]]("polynomial_ring(R)"),
					a.TermAs[RingOps[Fun[Nat, B]]]("polynomial_ring(T)"),
					T,
					a.TermAs[Fun[Fun[Nat, A], Fun[Nat, B]]]("λp:(num → A). λi:num. f(p(i))"),
					a.TermAs[Fun[Fun[Nat, B], B]]("λp:(num → B). polynomial_eval(p, y)"))))
		basisMoves := a.Have(
			"f moves a basis polynomial to the basis polynomial of T",
			"∀k i:num. f(basis_vector(R.zero, R.one, k, i)) = basis_vector(T.zero, T.one, k, i)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("k")
				b.FixAs[Nat]("i")
				b.Show(
					"each coefficient is zero or one",
					Simp(Fwd(vec_space.BasisVectorDef)),
					By(units))
			}))
		zeroth := a.TermAs[Nat]("0")
		constants := a.Have(
			"a constant polynomial has the value f(c)",
			"∀c:A. c ∈ R.carrier ⇒ «value»(vec_scalar_mul(c, basis_vector(R.zero, R.one, 0))) = f(c)",
			Derive(func(b *Argument) {
				c := b.FixAs[A]("c")
				cIn := b.Assume()
				moved := b.Have(
					"its coefficients move to those of the constant polynomial f(c)",
					"(λi:num. f(vec_scalar_mul(c, basis_vector(R.zero, R.one, 0), i))) = "+
						"vec_scalar_mul(f(c), basis_vector(T.zero, T.one, 0))",
					Derive(func(d *Argument) {
						d.Do(Funext())
						i := d.FixAs[Nat]("i")
						coefficient := d.TermAs[A]("basis_vector(R.zero, R.one, 0, i)")
						d.Show(
							"f is multiplicative at c and the coefficient",
							Simp(Fwd(vec_space.VecScalarMulDef)),
							By(
								cIn,
								basisMoves.At(zeroth, i),
								polynomial.BasisVectorOver.Read(source),
								polynomial.PolynomialOverDef.At(
									a.TermAs[A]("R.zero"),
									a.TermAs[Set[A]]("R.carrier"),
									d.TermAs[Fun[Nat, A]]("basis_vector(R.zero, R.one, 0)")),
								ring_homomorphism.MapMul.Read(hom).AsFact().At(c, coefficient)))
					}))
				image := b.TermAs[B]("f(c)")
				b.Show(
					"a constant polynomial evaluates to its constant",
					By(
						moved,
						cIn,
						yIn,
						ring_homomorphism.MapIn.Read(hom),
						EvalConstant.Read(target).AsFact().At(image, y)))
			}))
		variable := a.Have(
			"the variable has the value y",
			"«value»(basis_vector(R.zero, R.one, 1)) = y",
			Derive(func(b *Argument) {
				first := b.TermAs[Nat]("1")
				moved := b.Have(
					"its coefficients move to those of the variable of T",
					"(λi:num. f(basis_vector(R.zero, R.one, 1, i))) = basis_vector(T.zero, T.one, 1)",
					Derive(func(d *Argument) {
						d.Do(Funext())
						i := d.FixAs[Nat]("i")
						d.Show(
							"coefficient by coefficient",
							By(basisMoves.At(first, i)))
					}))
				b.Show(
					"the variable evaluates to y to the first",
					By(
						moved,
						EvalBasisVector.Read(target).At(first, yT),
						comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(target)).At(yT)))
			}))
		a.Show(
			"a ring map extending f and sending the variable to y",
			By(evaluation, constants, variable))
	}),
})}

// EvalTranslate — translating the argument of a polynomial gives another
// polynomial: evaluate the coefficient polynomial in the polynomial ring at
// the variable plus a, then commute evaluation with evaluation.
var EvalTranslate = evalTranslateThm{family.Add(registry.ProofEntry{
	Name: "EvalTranslate",
	Key:  "prop_8448e58139912bb2",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:(num → A). ∀a:A.",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"a ∈ R.carrier",
		},
		Conclusion: "∃q:(num → A). " +
			"    polynomial_over(R.carrier, q) ∧ " +
			"    (∀w:A. w ∈ R.carrier ⇒ polynomial_eval(q, w) = polynomial_eval(p, a + w))",
		Abbrev: Abbrev{
			{Name: "constant", Text: "λc:A. c • basis_vector(0)"},
			{Name: "lift", Text: "λi:num. «constant»(p(i))"},
			{Name: "affine", Text: "basis_vector(1) + a • basis_vector(0)"},
		},
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			p *Arrow[Nat, A],
			a *Expr[A],
			hypotheses Fact,
		) {
			constants := arg.Have(
				"constant polynomials give a ring homomorphism",
				"ring_homomorphism(R, polynomial_ring(R), «constant»)",
				Cite(polynomial.ConstantPolynomialHomomorphism.Read(ring)))
			lifted := arg.Have(
				"lifting each coefficient keeps finite support",
				"polynomial_over(polynomial_ring(R).zero, polynomial_ring(R).carrier, «lift»)",
				By(
					hypotheses,
					polynomial.PolynomialOverMap.At(arg.TermAs[Fun[A, Fun[Nat, A]]]("«constant»"),
						arg.TermAs[A]("R.zero"), arg.TermAs[Fun[Nat, A]]("polynomial_ring(R).zero"),
						arg.TermAs[Set[A]]("R.carrier"), arg.TermAs[Set[Fun[Nat, A]]]("polynomial_ring(R).carrier"), p),
					ring_homomorphism.MapZero.Read(constants),
					ring_homomorphism.MapIn.Read(constants)))
			affine := arg.Have(
				"the variable plus a constant is in the polynomial ring",
				"«affine» ∈ polynomial_ring(R).carrier",
				By(
					hypotheses,
					polynomial.BasisVectorOver.Read(ring).At(arg.TermAs[Nat]("1")),
					At(ring_homomorphism.MapIn.Read(constants), a),
					At(comm_ring.AddIn.Read(polynomial.PolynomialRingOn.Read(ring)),
						arg.TermAs[Fun[Nat, A]]("basis_vector(1)"), arg.TermAs[Fun[Nat, A]]("a • basis_vector(0)"))))
			translated, definition := arg.LetAs[Fun[Nat, A]]("translated",
				"polynomial_eval(polynomial_ring(R).add, "+
					"    polynomial_ring(R).zero, "+
					"    polynomial_ring(R).mul, "+
					"    polynomial_ring(R).one, "+
					"    «lift», "+
					"    «affine»)")
			arg.Take(translated)
			arg.Show(
				"evaluation at the affine polynomial translates the argument",
				SplitConj(
					Case(
						"the translated coefficient sequence is a polynomial",
						Derive(func(b *Argument) {
							concrete := b.Simplified(definition, Fwd(polynomial.PolynomialRingDef))
							b.Show(
								"the polynomial ring is closed under polynomial evaluation",
								By(
									Normalized,
									concrete,
									affine,
									lifted,
									At(EvalIn.Read(polynomial.PolynomialRingOn.Read(ring)),
										b.TermAs[Fun[Nat, Fun[Nat, A]]]("«lift»"), b.TermAs[Fun[Nat, A]]("«affine»"))))
						})),
					Case(
						"evaluation agrees with the original polynomial at the translated point",
						Derive(func(b *Argument) {
							w := b.FixAs[A]("w")
							inCarrier := b.Assume()
							evaluation := b.Have(
								"evaluation at the chosen point is a ring homomorphism",
								"ring_homomorphism(polynomial_ring(R), R, λq:(num → A). polynomial_eval(q, w))",
								By(inCarrier, At(EvalHomomorphism.Read(ring), w)))
							affineValue := b.Have(
								"the affine polynomial takes the translated value",
								"polynomial_eval(«affine», w) = a + w",
								Derive(func(c *Argument) {
									c.Have(
										"the variable and constant are both polynomials",
										"polynomial_over(R.carrier, basis_vector(1)) ∧ polynomial_over(R.carrier, a • basis_vector(0))",
										By(
											hypotheses,
											polynomial.BasisVectorOver.Read(ring).At(c.TermAs[Nat]("1")),
											At(ring_homomorphism.MapIn.Read(constants), a)))
									c.Do(Simp(
										Fwd(EvalAdd.Read(ring)),
										Fwd(EvalBasisVector.Read(ring)),
										Fwd(EvalConstant.Read(ring)),
										Fwd(comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)))))
									c.Show(
										"addition is commutative",
										ByArith(ring, inCarrier, hypotheses))
								}))
							coefficientValues := b.Have(
								"evaluating a constant coefficient recovers the coefficient",
								"∀i:num. polynomial_eval(p(i) • basis_vector(0), w) = p(i)",
								Derive(func(c *Argument) {
									i := c.FixAs[Nat]("i")
									c.Show(
										"each coefficient belongs to the original ring",
										By(
											inCarrier,
											hypotheses,
											polynomial.PolynomialOverDef.At(c.TermAs[A]("R.zero"), c.TermAs[Set[A]]("R.carrier"), p),
											At(EvalConstant.Read(ring), p.Apply(i), w)))
								}))
							concrete := b.Simplified(definition, Fwd(polynomial.PolynomialRingDef))
							transport := b.Have(
								"evaluation commutes with evaluating the coefficient polynomial",
								"polynomial_eval(translated, w) = "+
									"polynomial_eval(λi:num. polynomial_eval(p(i) • basis_vector(0), w), polynomial_eval(«affine», w))",
								By(
									concrete,
									affine,
									lifted,
									At(EvalAlongHomomorphism.Read(evaluation),
										b.TermAs[Fun[Nat, Fun[Nat, A]]]("«lift»"), b.TermAs[Fun[Nat, A]]("«affine»"))))
							b.Do(transport.Simp(Fwd(coefficientValues), Fwd(affineValue)))
							b.Show(
								"the coefficient and affine evaluations give the claimed translation",
								By(transport))
						}))))
		}),
})}

// EvalAtVar — every polynomial is its own value at the variable: its
// coefficients read as constant polynomials, evaluated in the ring of
// polynomials at x. With f vanishing from N on, the value is the sum
// below N of f(i) times x ^ i (EvalBelow, polynomial.VarPow), and that sum is f's
// expansion in the powers of x (polynomial.PolynomialExpansion).
var EvalAtVar = evalAtVarThm{family.Add(registry.ProofEntry{
	Name: "EvalAtVar",
	Key:  "prop_33960693834841bc",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀f:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, f)",
		},
		Conclusion: "polynomial_eval(polynomial_ring(R).add, " +
			"    polynomial_ring(R).zero, " +
			"    polynomial_ring(R).mul, " +
			"    polynomial_ring(R).one, " +
			"    «constantCoefficients», " +
			"    basis_vector(1)) = " +
			"f",
		Abbrev: Abbrev{
			{Name: "constantCoefficients", Text: "λi:num. f(i) • basis_vector(0)"},
		},
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], f *Arrow[Nat, A], polynomialF Fact) {
			polynomials := polynomial.PolynomialRingOn.Read(ring)
			constants := polynomial.ConstantPolynomialHomomorphism.Read(ring)
			lifted := a.TermAs[Fun[Nat, Fun[Nat, A]]]("«constantCoefficients»")
			variable := a.TermAs[Fun[Nat, A]]("basis_vector(1)")
			data := a.Conjuncts(
				a.Unfolded(polynomialF, polynomial.PolynomialOverDef),
				"f vanishes from some index on",
				"and every coefficient of f lies in R")
			N, support := a.UnpackAs[Nat](data[0], "N")
			coefficientsIn := data[1]
			constant := a.TermAs[Fun[A, Fun[Nat, A]]]("λa:A. a • basis_vector(0)")
			polynomialZero := a.TermAs[Fun[Nat, A]]("polynomial_ring(R).zero")
			liftedSupport := a.Have(
				"the constant coefficients vanish from the same index on",
				"vec⟨N⟩(polynomial_ring(R).zero, «constantCoefficients»)",
				By(
					ring_homomorphism.MapZero.Read(constants),
					polynomial.VecMap.At(
						constant, a.TermAs[A]("R.zero"), polynomialZero, proof.InhabitFrom(f, support))))
			liftedPolynomial := a.Have(
				"the constant coefficients form a polynomial over the polynomials",
				"polynomial_over(polynomial_ring(R).zero, polynomial_ring(R).carrier, «constantCoefficients»)",
				By(
					polynomialF,
					ring_homomorphism.MapZero.Read(constants),
					ring_homomorphism.MapIn.Read(constants),
					polynomial.PolynomialOverMap.At(
						constant,
						a.TermAs[A]("R.zero"),
						polynomialZero,
						a.TermAs[Set[A]]("R.carrier"),
						a.TermAs[Set[Fun[Nat, A]]]("polynomial_ring(R).carrier"),
						f)))
			monomials := a.Have(
				"a constant coefficient times a power of the variable is that power scaled by the coefficient",
				"∀i:num. polynomial_mul(f(i) • basis_vector(0), basis_vector(i)) = f(i) • basis_vector(i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					basis := b.TermAs[Fun[Nat, A]]("basis_vector(i)")
					coefficient := b.MemberOf[on.R](f.Apply(i), coefficientsIn.At(i))
					constantPolynomial := b.TermAs[Fun[Nat, A]]("f(i) • basis_vector(0)")
					basisOver := polynomial.BasisVectorOver.Read(ring).At(i)
					factorCoefficients := b.Have(
						"the constant polynomial and the power are polynomials "+
							"over c, so every coefficient of either lies in c",
						"∀k:num. (f(i) • basis_vector(0))(k) ∈ R.carrier ∧ basis_vector(i, k) ∈ R.carrier",
						By(
							coefficient,
							basisOver,
							ring_homomorphism.MapIn.Read(constants).AsFact().At(coefficient),
							polynomial.PolynomialOverDef))
					b.Show(
						"the product commutes, and multiplying by a constant is scaling",
						By(
							coefficient,
							basisOver,
							factorCoefficients,
							polynomial.PolynomialMulComm.Read(ring).At(constantPolynomial, basis),
							polynomial.PolynomialMulConstant.Read(ring).At(coefficient, basis)))
				}))
			a.Do(Simp(Fwd(polynomial.PolynomialRingDef)))
			finiteEvaluation := a.Have(
				"the variable lying in the polynomial carrier, the "+
					"value is the sum of the coefficient monomials below N",
				"polynomial_eval(vec_add, "+
					"    vec_zero, "+
					"    polynomial_mul, "+
					"    basis_vector(0), "+
					"    «constantCoefficients», "+
					"    basis_vector(1)) = "+
					"module_sum(vec_add, "+
					"    vec_zero, "+
					"    {i:num | i < N}, "+
					"    λi:num. "+
					"        polynomial_mul(f(i) • basis_vector(0), "+
					"            monoid_pow(polynomial_mul, basis_vector(0), basis_vector(1), i)))",
				By(
					liftedPolynomial,
					liftedSupport,
					ring,
					polynomial.BasisVectorOver.Read(ring).At(a.TermAs[Nat]("1")),
					EvalBelow.Read(polynomials).AsFact().At(N, lifted, variable)))
			a.Do(Simp(
				Fwd(finiteEvaluation),
				Rev(polynomial.PolynomialPowDef),
				Fwd(polynomial.VarPow.Read(ring)),
				Fwd(monomials)))
			a.Show(
				"this is the expansion of f in the powers of the variable",
				By(polynomialF, support, polynomial.PolynomialExpansion.Read(ring).AsFact().At(N, f)))
		}),
})}

// EvalTwoVariables — the coefficients c(i, j) of a polynomial in two
// variables, zero from row m and from column n on, give one value at (x, y)
// in either order of evaluation: the rows c(i) read as polynomials in y and
// their values evaluated at x, or the columns read as polynomials in x and
// their values evaluated at y. Each order is the finite double sum of the
// terms c(i, j)·yʲ·xⁱ, and the two double sums differ by the order of
// summation and of the factors in a term.
var EvalTwoVariables = evalTwoVariablesThm{family.Add(registry.ProofEntry{
	Name: "EvalTwoVariables",
	Key:  "prop_149883cecb27720c",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀m n:num. ∀c:(num → num → A). ∀x y:A.",
		Hypotheses: []string{
			"∀i j:num. c(i, j) ∈ R.carrier",
			"∀i j:num. m ≤ i ⇒ c(i, j) = R.zero",
			"∀i j:num. n ≤ j ⇒ c(i, j) = R.zero",
			"x ∈ R.carrier",
			"y ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(λi:num. polynomial_eval(c(i), y), x) = " +
			"polynomial_eval(λj:num. polynomial_eval(λi:num. c(i, j), x), y)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Evaluating the rows at y and their values at x sums the terms
		// c(i, j)·yʲ·xⁱ over i < m and j < n.
		doubleSum := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀m n:num. ∀c:(num → num → A). ∀x y:A.",
			Hypotheses: []string{
				"∀i j:num. c(i, j) ∈ R.carrier",
				"∀i j:num. m ≤ i ⇒ c(i, j) = R.zero",
				"∀i j:num. n ≤ j ⇒ c(i, j) = R.zero",
				"x ∈ R.carrier",
				"y ∈ R.carrier",
			},
			Conclusion: "polynomial_eval(λi:num. polynomial_eval(c(i), y), x) = " +
				"module_sum(R.add, " +
				"    R.zero, " +
				"    {i:num | i < m}, " +
				"    λi:num. " +
				"        module_sum(R.add, " +
				"            R.zero, " +
				"            {j:num | j < n}, " +
				"            λj:num. c(i, j) * monoid_pow(R.mul, R.one, y, j) * monoid_pow(R.mul, R.one, x, i)))",
		}, func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			m, n *Expr[Nat],
			c *Arrow2[Nat, Nat, A],
			x, y *Expr[A],
			inR, pastRow, pastColumn, xIn, yIn Fact,
		) {
			powers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))
			rowsVanish := a.Have(
				"each row c(i) vanishes from n on",
				"∀i:num. vec⟨n⟩(c(i))",
				By(pastColumn, vec_space.VecDef))
			rows := a.Have(
				"so each row is a polynomial over R",
				"∀i:num. polynomial_over(R.carrier, c(i))",
				By(Normalized, inR, rowsVanish, polynomial.PolynomialOverDef))
			rowValues := a.Have(
				"the value of the row c(i) at y is its sum below n",
				"∀i:num. "+
					"    polynomial_eval(c(i), y) = "+
					"    module_sum(R.add, R.zero, {j:num | j < n}, λj:num. c(i, j) * monoid_pow(R.mul, R.one, y, j))",
				By(rows, rowsVanish, yIn, EvalBelow.Read(ring)))
			zeroRows := a.Have(
				"from m on the rows are zero",
				"∀i:num. m ≤ i ⇒ c(i) = vec_zero",
				By(pastRow, vec_space.VecZeroDef))
			valuesVanish := a.Have(
				"so the values of the rows at y vanish from m on",
				"vec⟨m⟩(λi:num. polynomial_eval(c(i), y))",
				By(zeroRows, yIn, vec_space.VecDef, EvalVecZero.Read(ring)))
			values := a.Have(
				"and they are the coefficients of a polynomial over R",
				"polynomial_over(R.carrier, λi:num. polynomial_eval(c(i), y))",
				By(rows, yIn, valuesVanish, polynomial.PolynomialOverDef, EvalIn.Read(ring)))
			rowTerms := a.Have(
				"every term c(i, j)·yʲ of a row's value lies in R",
				"∀i j:num. c(i, j) * monoid_pow(R.mul, R.one, y, j) ∈ R.carrier",
				By(inR, yIn, comm_ring.MulIn.Read(ring), powers))
			regular := module.RegularModuleOn.Read(ring)
			distributed := a.Have(
				"xⁱ multiplies through the sum that is the value of the row c(i)",
				"∀i:num. "+
					"    polynomial_eval(c(i), y) * monoid_pow(R.mul, R.one, x, i) = "+
					"    module_sum(R.add, "+
					"        R.zero, "+
					"        {j:num | j < n}, "+
					"        λj:num. c(i, j) * monoid_pow(R.mul, R.one, y, j) * monoid_pow(R.mul, R.one, x, i))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"the sum is finite and its terms lie in R",
						By(
							rowValues.At(i),
							rowTerms,
							xIn,
							powers,
							At(
								module.ModuleSumSmulRight.Read(regular),
								b.TermAs[Set[Nat]]("{j:num | j < n}"),
								b.TermAs[Fun[Nat, A]]("λj:num. c(i, j) * monoid_pow(R.mul, R.one, y, j)"),
								b.TermAs[A]("monoid_pow(R.mul, R.one, x, i)")),
							num_segment.FiniteBelowStrict.At(n)))
				}))
			a.Show(
				"the value at x of the row values is their sum below m against the powers of x",
				By(
					distributed,
					xIn,
					values,
					valuesVanish,
					At(EvalBelow.Read(ring), m, a.TermAs[Fun[Nat, A]]("λi:num. polynomial_eval(c(i), y)"), x),
					module.ModuleSumCongruence))
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			m, n *Expr[Nat],
			c *Arrow2[Nat, Nat, A],
			x, y *Expr[A],
			inR, pastRow, pastColumn, xIn, yIn Fact,
		) {
			powers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))
			terms := a.Have(
				"every term c(i, j)·yʲ·xⁱ lies in R",
				"∀i j:num. c(i, j) * monoid_pow(R.mul, R.one, y, j) * monoid_pow(R.mul, R.one, x, i) ∈ R.carrier",
				By(inR, xIn, yIn, comm_ring.MulIn.Read(ring), powers))
			regroup := a.Have(
				"and its factors regroup as c(i, j)·xⁱ·yʲ",
				"∀i j:num. "+
					"    c(i, j) * monoid_pow(R.mul, R.one, y, j) * monoid_pow(R.mul, R.one, x, i) = "+
					"    c(i, j) * monoid_pow(R.mul, R.one, x, i) * monoid_pow(R.mul, R.one, y, j)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					j := b.FixAs[Nat]("j")
					b.Show(
						"R is commutative",
						ByArith(ring, inR.At(i, j), xIn, yIn, powers.AsFact().At(x, i), powers.AsFact().At(y, j)))
				}))
			regular := module.RegularModuleOn.Read(ring)
			a.Show(
				"both orders of evaluation sum the same terms",
				CalcEq(
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {i:num | i < m}, "+
								"    λi:num. "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {j:num | j < n}, "+
								"            λj:num. c(i, j) * monoid_pow(R.mul, R.one, y, j) * monoid_pow(R.mul, R.one, x, i)))"),
						"evaluating the rows first sums the terms row by row",
						By(
							ring,
							inR,
							pastRow,
							pastColumn,
							xIn,
							yIn,
							At(doubleSum, a.TermAs[RingOps[A]]("R"), m, n, c, x, y))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {j:num | j < n}, "+
								"    λj:num. "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {i:num | i < m}, "+
								"            λi:num. c(i, j) * monoid_pow(R.mul, R.one, y, j) * monoid_pow(R.mul, R.one, x, i)))"),
						"exchange the two finite sums",
						By(
							terms,
							module.ModuleSumSwap.Read(regular).At(
								a.TermAs[Set[Nat]]("{i:num | i < m}"),
								a.TermAs[Set[Nat]]("{j:num | j < n}"),
								a.TermAs[Fun2[Nat, Nat, A]](
									"λi:num. λj:num. c(i, j) * monoid_pow(R.mul, R.one, y, j) * monoid_pow(R.mul, R.one, x, i)")),
							num_segment.FiniteBelowStrict.At(m),
							num_segment.FiniteBelowStrict.At(n))),
					Leg(
						a.TermAs[A](
							"module_sum(R.add, "+
								"    R.zero, "+
								"    {j:num | j < n}, "+
								"    λj:num. "+
								"        module_sum(R.add, "+
								"            R.zero, "+
								"            {i:num | i < m}, "+
								"            λi:num. c(i, j) * monoid_pow(R.mul, R.one, x, i) * monoid_pow(R.mul, R.one, y, j)))"),
						"regroup each term",
						Simp(Fwd(regroup)),
						Refl()),
					FinalLeg(
						"which is evaluating the columns at x first, the transposed "+
							"coefficients vanishing from row n and column m on",
						By(
							ring,
							inR,
							pastRow,
							pastColumn,
							xIn,
							yIn,
							At(
								doubleSum,
								a.TermAs[RingOps[A]]("R"),
								n,
								m,
								a.TermAs[Fun2[Nat, Nat, A]]("λj:num. λi:num. c(i, j)"),
								y,
								x)))))
		})
	}),
})}

// GeometricFactorization — for d positive, the linear factor 1 − T and the
// geometric sum 1 + T + … + Tᵈ⁻¹ are polynomials over the ring, their
// product is 1 − Tᵈ, and the geometric sum takes at one the value d, the sum
// of d ones. 1 − T is the difference of the basis polynomials 1 and T.
// Multiplying by 1 − T, which is 1 − 1 • T, takes the first difference of
// the geometric sum (polynomial.BinomialConvolution at c = 1 and the shift one), whose
// adjacent ones cancel inside the interval and leave 1 at the index 0 and −1
// at d; at one, the geometric sum takes the sum of its coefficients below d
// (EvalOneBelow), each of them one.
var GeometricFactorization = geometricFactorizationThm{family.Add(registry.ProofEntry{
	Name: "GeometricFactorization",
	Key:  "prop_83814659ae6b6952",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀d:num.",
		Hypotheses: []string{"0 < d"},
		Conclusion: "polynomial_over(R.carrier, «1−T») ∧ " +
			"polynomial_over(R.carrier, «1+…+Tᵈ⁻¹»(d)) ∧ " +
			"polynomial_mul(«1−T», «1+…+Tᵈ⁻¹»(d)) = basis_vector(0) - basis_vector(d) ∧ " +
			"polynomial_eval(«1+…+Tᵈ⁻¹»(d), R.one) = «numeral»(d)",
		Abbrev: Abbrev{
			{Name: "1−T", Text: "basis_vector(0) - basis_vector(1)"},
			{Name: "1+…+Tᵈ⁻¹", Text: "λd:num. λn:num. COND(n < d, R.one, R.zero)"},
		},
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], d *Expr[Nat], positive Fact) {
			zeroth, first := arg.TermAs[Nat]("0"), arg.TermAs[Nat]("1")
			one := arg.MemberOf[on.R](arg.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			geometricSum := arg.TermAs[Fun[Nat, A]]("«1+…+Tᵈ⁻¹»(d)")
			below := arg.TermAs[Set[Nat]]("{i:num | i < d}")
			linearOver := arg.Have(
				"1 − T is the difference of the basis polynomials 1 and T, so a polynomial over the ring",
				"polynomial_over(R.carrier, «1−T»)",
				By(
					comm_ring.SubIn.Read(polynomial.PolynomialRingOn.Read(ring)),
					polynomial.BasisVectorOver.Read(ring).At(zeroth),
					polynomial.BasisVectorOver.Read(ring).At(first)))
			coefficients := arg.Have(
				"the coefficients of the geometric sum are one and zero, members of the ring",
				"∀n:num. «1+…+Tᵈ⁻¹»(d, n) ∈ R.carrier",
				By(comm_ring.OneIn.Read(ring), comm_ring.ZeroIn.Read(ring)))
			support := arg.Have(
				"the geometric sum vanishes from d on",
				"vec⟨d⟩(«1+…+Tᵈ⁻¹»(d))",
				ByArith(vec_space.VecDef))
			geometricOver := arg.Have(
				"so it is a polynomial over the ring",
				"polynomial_over(R.carrier, «1+…+Tᵈ⁻¹»(d))",
				By(
					coefficients,
					support,
					polynomial.PolynomialOverDef.At(
						arg.TermAs[A]("R.zero"), arg.TermAs[Set[A]]("R.carrier"), geometricSum)))
			variable := arg.Have(
				"T is a polynomial over the ring, so every coefficient of it lies in it",
				"∀i:num. basis_vector(1, i) ∈ R.carrier",
				By(polynomial.BasisVectorOver.Read(ring).At(first), polynomial.PolynomialOverDef))
			factorization := arg.Have(
				"the product is 1 − Tᵈ, coefficient by coefficient",
				"polynomial_mul(«1−T», «1+…+Tᵈ⁻¹»(d)) = basis_vector(0) - basis_vector(d)",
				Derive(func(arg *Argument) {
					arg.Do(Funext())
					n := arg.FixAs[Nat]("n")
					difference := arg.Have(
						"multiplying by 1 − T, which is 1 − 1 • T, takes the first difference of the geometric sum",
						"polynomial_mul(«1−T», «1+…+Tᵈ⁻¹»(d), n) = "+
							"«1+…+Tᵈ⁻¹»(d, n) + COND(1 ≤ n, -(R.one * «1+…+Tᵈ⁻¹»(d, n - 1)), R.zero)",
						By(
							coefficients,
							variable,
							vec_space.SmulOneOn.Read(ring).At(arg.TermAs[Fun[Nat, A]]("basis_vector(1)")),
							polynomial.BinomialConvolution.Read(ring).At(one, first, n, geometricSum)))
					arg.Do(difference.Rw(), Simp(Fwd(vec_space.VecSubDef), Fwd(vec_space.BasisVectorDef)))
					zero := comm_ring.ZeroIn.Read(ring)
					started := arg.Unless(
						arg.Term("n = 0"),
						"at 0 only the leading one stands",
						Given(func(arg *Argument, start Fact) {
							arg.Show(
								"one plus zero is one less zero",
								ByArith(ring, positive, start, one, zero))
						}))
					offEnd := arg.Unless(
						arg.Term("n = d"),
						"at d only the trailing −1 stands",
						Given(func(arg *Argument, end Fact) {
							arg.Show(
								"zero less one times one is zero less one",
								ByArith(ring, positive, end, one, zero))
						}))
					arg.Cases(arg.Term("n < d"))
					arg.When(
						"inside the interval two adjacent ones cancel",
						func(arg *Argument, inside Fact) {
							arg.Show(
								"one less one times one is zero less zero",
								ByArith(ring, positive, started, inside, one, zero))
						})
					arg.Otherwise(
						"past d both terms of the difference vanish",
						func(arg *Argument, past Fact) {
							arg.Show(
								"zero less one times zero is zero less zero",
								ByArith(ring, positive, offEnd, past, one, zero))
						})
				}))
			value := arg.Have(
				"the geometric sum takes at one the sum of d ones, the numeral d",
				"polynomial_eval(«1+…+Tᵈ⁻¹»(d), R.one) = «numeral»(d)",
				CalcEq(
					Leg(
						arg.TermAs[A]("module_sum(R.add, R.zero, {i:num | i < d}, «1+…+Tᵈ⁻¹»(d))"),
						"at one, the geometric sum takes the sum of its coefficients below the support bound d",
						By(geometricOver, support, EvalOneBelow.Read(ring).AsFact().At(d, geometricSum))),
					Leg(
						arg.TermAs[A]("module_sum(R.add, R.zero, {i:num | i < d}, λi:num. R.one)"),
						"each of those coefficients is one",
						BySets(module.ModuleSumCongruence.At(
							arg.TermAs[Op[A]]("R.add"),
							arg.TermAs[A]("R.zero"),
							below,
							geometricSum,
							arg.TermAs[Fun[Nat, A]]("λi:num. R.one")))),
					FinalLeg(
						"and d ones sum to the numeral d, the indices below d being d in number",
						By(
							num_segment.HasSizeBelowStrict.At(d),
							cardinality.CardOfSized.At(below, d),
							module.ModuleSumConstantMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(below, one),
							num_segment.FiniteBelowStrict.At(d))),
				))
			arg.Show(
				"the two polynomials, their product and the value at one",
				By(linearOver, geometricOver, factorization, value))
		}),
})}

// PolynomialProductData — the product of two polynomials over a subfield k is
// a polynomial over k, nonzero with its factors, and it evaluates to the product
// of the values.
var PolynomialProductData = polynomialProductDataThm{family.Add(registry.ProofEntry{
	Name: "PolynomialProductData",
	Key:  "prop_8c4051cafd7f9aff",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀a c:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"polynomial_over(k, a)",
			"polynomial_over(k, c)",
		},
		Conclusion: "polynomial_over(k, polynomial_mul(a, c)) ∧ " +
			"(a ≠ vec_zero ∧ c ≠ vec_zero ⇒ polynomial_mul(a, c) ≠ vec_zero) ∧ " +
			"(∀x:A. " +
			"    x ∈ M.carrier ⇒ " +
			"    polynomial_eval(polynomial_mul(a, c), x) = polynomial_eval(a, x) * polynomial_eval(c, x))",
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		a, c *Arrow[Nat, A],
		subfieldK, overA, overC Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		ring := field.RingOn.Read(M)
		zero := arg.TermAs[A]("M.zero")
		carrier := arg.TermAs[Set[A]]("M.carrier")
		kInField := arg.Have(
			"k lies in M",
			"k ⊆ M.carrier",
			By(subfieldK, field.SubfieldSubset.At(ops, k)))
		onK := arg.Have(
			"k is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(M), k))",
			By(subfieldK, field.SubfieldCommRing.Read(M).At(k)))
		overField := arg.Have(
			"a and c are polynomials over M",
			"polynomial_over(M.carrier, a) ∧ polynomial_over(M.carrier, c)",
			By(
				kInField,
				overA,
				overC,
				polynomial.PolynomialOverMono.At(zero, k, carrier, a),
				polynomial.PolynomialOverMono.At(zero, k, carrier, c)))
		productOver := arg.Have(
			"a · c is a polynomial over k",
			"polynomial_over(k, polynomial_mul(a, c))",
			By(overA, overC, polynomial.PolynomialMulOver.Read(onK).AsFact().At(a, c)))
		domain := integral_domain.FieldIntegralDomain.Read(M)
		productNonzero := arg.Have(
			"a · c is nonzero, by its leading coefficient",
			"a ≠ vec_zero ∧ c ≠ vec_zero ⇒ polynomial_mul(a, c) ≠ vec_zero",
			Derive(func(b *Argument) {
				nonzero := b.Conjuncts(
					b.Assume(),
					"a is nonzero",
					"c is nonzero")
				vanishing := b.SupposeNot()
				top := b.TermAs[Nat]("polynomial_degree(a) + polynomial_degree(c)")
				leading := b.Have(
					"The leading coefficient of a · c is nonzero",
					"polynomial_mul(a, c, polynomial_degree(a) + polynomial_degree(c)) ≠ M.zero",
					By(
						overField,
						nonzero[0],
						nonzero[1],
						polynomial.LeadingCoefficientMulNonzero.Read(domain).AsFact().At(a, c)))
				b.Show(
					"which the zero vector does not have",
					By(leading, vanishing, vec_space.VecZeroDef.At(zero, top)))
			}))
		values := arg.Have(
			"a · c evaluates to the product of the values",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ M.carrier",
				},
				Conclusion: "polynomial_eval(polynomial_mul(a, c), x) = " +
					"polynomial_eval(a, x) * polynomial_eval(c, x)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inField := b.Assume()
				b.Show(
					"polynomials multiply pointwise",
					By(overField, inField, EvalMul.Read(ring).AsFact().At(a, c, x)))
			}))
		arg.Show(
			"the three facts",
			By(productOver, productNonzero, values))
	}),
})}
