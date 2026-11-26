// int_product.go — products of integers, where the fold at ℤ's
// multiplication meets integer arithmetic.
//
// Each member unfolds `int_product` to the fold and reads a law of the
// mechanism there beside ℤ's fold facts, as the recursion
// (IntProductClauses) does; what sets these apart is the fact of integer arithmetic each law is
// met with. A product does not see points added to its index set at which
// the factor is 1, the neutral element. A product of one integer c is c to
// the number of factors, powers of c adding their exponents. And a product
// of signs is −1 to the number of minus signs: it splits over the points
// with a minus sign and the rest, and the rest contribute 1. And a product
// of natural numbers read in ℤ is the product of their readings.

package int_product

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The recursion at ℤ's multiplication
// ---------------------------------------------------------------------------
//
// The empty fold returns the operation's neutral element, and inserting
// a point either changes nothing, because the point was already there,
// or contributes its own value.

// IntProductClauses — the recursion at ℤ's multiplication.
var IntProductClauses = intProductClausesThm{family.Add(registry.ProofEntry{
	Name: "IntProductClauses",
	Key:  "prop_9020ab8a1099fabd",
	Build: family.Theorem(
		"(∀f:(A → int). product(∅, f) = &1) ∧ "+
			"(∀g:(C → int). ∀x:C. ∀s:set(C). "+
			"    finite(s) ⇒ product(insert(x, s), g) = COND(x ∈ s, product(s, g), g(x) * product(s, g)))",
		func(a *Argument) {
			a.Do(Unfold(IntProductDef), By(
				monoidal.Clauses,
				int_real_lift.MonoidalMul,
				int_real_lift.NeutralMul))
		}),
})}

// IntProductSuperset — an integer product does not see points added to its
// index set at which the factor is 1: the fold law at ℤ's multiplication,
// whose neutral element is 1.
var IntProductSuperset = intProductSupersetThm{family.Add(registry.ProofEntry{
	Name: "IntProductSuperset",
	Key:  "prop_6c3365148c778846",
	Build: family.Theorem(Statement{
		Binders: "∀u v:set(A). ∀f:(A → int).",
		Hypotheses: []string{
			"u ⊆ v",
			"∀x:A. x ∈ v ∧ x ∉ u ⇒ f(x) = 1",
		},
		Conclusion: "product(u, f) = product(v, f)",
	}, Opening(Unfold(IntProductDef), By(monoidal.Superset, int_real_lift.NeutralMul))),
})}

// IntProductConst — a finite product of one integer c is c raised to the
// number of factors: n ↦ cⁿ carries addition to multiplication, so it
// carries the sum of ones, the count, to the product of c¹ = c.
var IntProductConst = intProductConstThm{family.Add(registry.ProofEntry{
	Name: "IntProductConst",
	Key:  "prop_2f5e9dd95597a592",
	Build: family.Theorem(Statement{
		Binders: "∀c:int. ∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "Π_{x∈s} c = c ^ card(s)",
	}, func(a *Argument, c *Expr[Int], s *Expr[Set[A]], finite Fact) {
		keepsOne := a.Have(
			"c⁰ = 1 is the element the product starts from",
			"c ^ neutral_elem(+) = neutral_elem(int_mul)",
			ByArith(nat_sum.NeutralNatAdd, int_real_lift.NeutralMul, int_pow.PowClauses.At(c)))
		powers := a.Have(
			"so n ↦ cⁿ carries the sum of ones to the product of c¹",
			"c ^ (Σ_{x∈s} 1) = Π_{x∈s} c ^ 1",
			Unfold(IntProductDef),
			Unfold(nat_sum.NatSumDef),
			By(
				finite,
				int_pow.PowAdd,
				keepsOne,
				nat_sum.MonoidalNatAdd,
				int_real_lift.MonoidalMul,
				Where(monoidal.Homomorphic, "h", a.TermAs[Fun[Nat, Int]]("λn:num. c ^ n"))))
		first := a.Have(
			"c¹ = c",
			"c ^ 1 = c",
			ByArith())
		a.Show(
			"a sum of ones counts the set",
			By(Normalized, finite, first, powers, nat_sum.SumOfOnes.At(s)))
	}),
})}

// IntProductSigns — a finite product of signs, −1 where P holds and 1
// elsewhere, is −1 raised to the number of points where P holds: the product
// splits over the points where P holds and the rest, the rest contribute 1,
// and the minus signs are a product of one integer.
var IntProductSigns = intProductSignsThm{family.Add(registry.ProofEntry{
	Name: "IntProductSigns",
	Key:  "prop_e877f118d8becc62",
	Build: family.Theorem(Statement{
		Binders: "∀P:(A → bool). ∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "Π_{x∈s} COND(P(x), -int_of_num(1), int_of_num(1)) = " +
			"(-int_of_num(1)) ^ card({x:A | x ∈ s ∧ P(x)})",
	}, func(a *Argument, P *Arrow[A, Bool], s *Expr[Set[A]], finite Fact) {
		minusOne := a.TermAs[Int]("-1")
		minusSigns := a.TermAs[Set[A]]("{x:A | x ∈ s ∧ P(x)}")
		ones := a.Have(
			"the points where P fails contribute 1",
			"Π_{x∈{y:A | y ∈ s ∧ ¬P(y)}} int_of_num(1) = int_of_num(1)",
			Unfold(IntProductDef),
			By(int_real_lift.MonoidalMul, int_real_lift.NeutralMul, monoidal.EqNeutral))
		halves := a.Have(
			"the product splits over the points where P holds and the rest",
			"Π_{x∈s} COND(P(x), -int_of_num(1), int_of_num(1)) = Π_{x∈{y:A | y ∈ s ∧ P(y)}} -int_of_num(1)",
			Unfold(IntProductDef),
			ByArith(
				finite,
				ones,
				int_real_lift.MonoidalMul,
				monoidal.Split.Read(int_real_lift.MonoidalMul).At(
					s,
					P,
					a.TermAs[Fun[A, Int]]("λx:A. -int_of_num(1)"),
					a.TermAs[Fun[A, Int]]("λx:A. 1"))))
		a.Show(
			"and the minus signs are a product of −1",
			By(halves, finite, finite_set.FiniteRestrict.At(s, P), IntProductConst.At(minusOne, minusSigns)))
	}),
})}

// ---------------------------------------------------------------------------
// The cast from ℕ
// ---------------------------------------------------------------------------

// IntOfNatProduct — the cast of a finite product of natural numbers is the
// product of the casts: the transfer law for folds, read at the embedding of
// ℕ's multiplication into ℤ's, which keeps the unit and is multiplicative.
var IntOfNatProduct = intOfNatProductThm{family.Add(registry.ProofEntry{
	Name: "IntOfNatProduct",
	Key:  "prop_af99871b6e8cbdec",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f:(A → num).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "int_of_num(product(s, f)) = product(s, λx:A. int_of_num(f(x)))",
	}, func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Nat], finite Fact) {
		// Each product is the fold at its carrier's multiplication.
		a.Do(Unfold(nat_product.NatProductDef), Unfold(IntProductDef))
		fixesUnit := a.Have(
			"the cast fixes the unit",
			"int_of_num(neutral_elem(λx:num. λy:num. x * y)) = neutral_elem(int_mul)",
			Simp(Fwd(nat_product.NeutralNatMul), Fwd(int_real_lift.NeutralMul)),
			Refl())
		a.Show(
			"so the transfer law carries the fold across the cast, which crosses multiplication",
			By(
				finite,
				fixesUnit,
				monoidal.Homomorphic,
				nat_product.MonoidalNatMul,
				int_real_lift.MonoidalMul,
				int_embed.OfNumMul))
	}),
})}
