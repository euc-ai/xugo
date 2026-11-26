// nat_product.go — products of naturals, where the fold at ℕ's
// multiplication meets natural arithmetic.
//
// A product of one number c is c to the number of factors: each fresh point
// contributes one factor c and adds one to the count. A product grows
// with its factors: the order survives multiplication and holds of the empty
// product, so the fold carries it (monoidal.Related). And n! is the product
// of 1, …, n.

package nat_product

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The fold facts ℕ's multiplication was missing
// ---------------------------------------------------------------------------
//
// Of the two facts the neutral element comes first: `monoidal_op(op)`'s
// identity conjunct speaks of `neutral_elem(op)`, the element the fold
// actually starts from, and not of any numeral, so ℕ's unit laws cannot
// engage it until the element the choice names is known to be 1.

// NeutralNatMul — the element multiplication folds from is one.
//
// `neutral_elem op` is a Hilbert choice: it names SOME two-sided identity
// for op and says nothing about which. Nothing more is needed, because
// an identity is unique. Write z for the element chosen. Both z and 1
// are two-sided identities — z by the definition, 1 by ℕ's two unit
// laws, which are also what makes the choice well posed — so reading
// the two against each other at z * 1 gives z = z * 1 = 1.
var NeutralNatMul = neutralNatMulThm{family.Add(registry.ProofEntry{
	Name: "NeutralNatMul",
	Key:  "prop_8d80f7f279534ab1",
	Build: family.Theorem("neutral_elem(*) = 1",
		func(a *Argument) {
			// Unfolding leaves the ε-term itself on the goal's left.
			// Its defining predicate demands an identity on both sides,
			// and the two unit laws supply exactly that at 1.
			a.Do(Unfold(monoidal.NeutralElemDef), By(nat_arith.OneMul, nat_arith.MulOne))
		}),
})}

// MonoidalNatMul — natural multiplication folds: it commutes, it
// associates, and one is its neutral element.
//
// The first two conjuncts are ℕ's multiplicative laws verbatim,
// bracketing included, so each cite lands on its case whole. The
// third is stated about `neutral_elem(*)` rather than about 1, which is
// why computing the neutral above had to come first.
var MonoidalNatMul = monoidalNatMulThm{family.Add(registry.ProofEntry{
	Name: "MonoidalNatMul",
	Key:  "prop_356093777c33b6c0",
	Build: family.Theorem("monoidal_op(*)",
		func(a *Argument) {
			a.Do(Unfold(monoidal.MonoidalOpDef), SplitConjAll(
				Case(
					"multiplication commutes",
					Cite(nat_arith.MulSym)),
				Case(
					"multiplication associates",
					Cite(nat_arith.MulAssoc)),
				// The identity conjunct is stated at `neutral_elem(*)`, so the
				// neutral is REWRITTEN to 1 and the unit law then reads the
				// conjunct whole.
				Case(
					"the neutral element is a left identity",
					Simp(Fwd(NeutralNatMul)),
					Cite(nat_arith.OneMul)),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The recursion at ℕ's multiplication
// ---------------------------------------------------------------------------
//
// The empty fold returns the operation's neutral element, and inserting
// a point either changes nothing, because the point was already there,
// or contributes its own value.

// NatProductClauses — the recursion at ℕ's multiplication, the one
// carrier whose fold facts are proved above.
var NatProductClauses = natProductClausesThm{family.Add(registry.ProofEntry{
	Name: "NatProductClauses",
	Key:  "prop_f24a803e20e6b814",
	Build: family.Theorem(
		"(∀f:(A → num). product(∅, f) = 1) ∧ "+
			"(∀g:(C → num). ∀x:C. ∀s:set(C). "+
			"    finite(s) ⇒ product(insert(x, s), g) = COND(x ∈ s, product(s, g), g(x) * product(s, g)))",
		func(a *Argument) {
			a.Do(Unfold(NatProductDef), By(monoidal.Clauses, MonoidalNatMul, NeutralNatMul))
		}),
})}

// NatProductConst — the product of a constant c over a finite set is c to
// the set's size: by induction on the set, each fresh point contributes one
// factor c and raises the size by one.
var NatProductConst = natProductConstThm{family.Add(registry.ProofEntry{
	Name: "NatProductConst",
	Key:  "prop_339696dd37e0e10e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀c:num.",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "product(s, λx:A. c) = c ^ card(s)",
	},
		func(a *Argument, s *Expr[Set[A]], c *Expr[Nat], finite Fact) {
			a.Show(
				"by induction on the finite set s",
				ByInduction(finite_set.FiniteInductFresh, finite,
					Case(
						"the empty product is 1 = c⁰",
						By(NatProductClauses, cardinality.CardClauses, nat_arith.NatPow)),
					Case(
						"a fresh point x contributes one factor c and one to the size",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							b.FixAs[Set[A]]("t")
							grown := b.Assume()
							b.Show(
								"the product over insert(x, t) is c·c^card(t) = c^card(insert(x, t))",
								By(grown, NatProductClauses, cardinality.CardClauses, nat_arith.NatPow))
						}))))
		}),
})}

// NatProductMonotone — a product of naturals grows with its factors: the order
// survives multiplication and holds of the empty product, so it passes
// through the fold (monoidal.Related).
var NatProductMonotone = natProductMonotoneThm{family.Add(registry.ProofEntry{
	Name: "NatProductMonotone",
	Key:  "prop_e598a8f1db863a3e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f g:(A → num).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ f(x) ≤ g(x)",
		},
		Conclusion: "product(s, f) ≤ product(s, g)",
	},
		func(a *Argument, s *Expr[Set[A]], f, g *Arrow[A, Nat], finite, pointwise Fact) {
			a.Do(Unfold(NatProductDef))
			respects := a.Have(
				"the order survives multiplication",
				"∀x₁ y₁ x₂ y₂:num. x₁ ≤ x₂ ∧ y₁ ≤ y₂ ⇒ x₁ * y₁ ≤ x₂ * y₂",
				By(nat_order.LessEqMul2))
			fixesNeutral := a.Have(
				"and holds of the element the fold starts from",
				"neutral_elem(*) ≤ neutral_elem(*)",
				By(nat_order.LessEqRefl))
			a.Show(
				"so it reaches the two folds",
				By(finite, pointwise, respects, fixesNeutral, MonoidalNatMul, monoidal.Related))
		}),
})}

// NatProductUpperBound — a product of naturals, each factor at most c, is at
// most c to the number of factors: it is at most the product of the constant c
// (NatProductMonotone), which is c ^ card(s) (NatProductConst).
var NatProductUpperBound = natProductUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "NatProductUpperBound",
	Key:  "prop_45681ce6fc156d21",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f:(A → num). ∀c:num.",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ f(x) ≤ c",
		},
		Conclusion: "product(s, f) ≤ c ^ card(s)",
	},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Nat], c *Expr[Nat], finite, bounded Fact) {
			a.Show(
				"the product is at most that of the constant c, c ^ card(s)",
				By(
					Normalized,
					finite,
					bounded,
					NatProductMonotone.At(s, f, a.TermAs[Fun[A, Nat]]("λx:A. c")),
					NatProductConst.At(s, c)))
		}),
})}

// NatProductLowerBound — a product of naturals, each factor at least c, is at
// least c to the number of factors: the product of the constant c, c ^ card(s)
// (NatProductConst), is at most it (NatProductMonotone).
var NatProductLowerBound = natProductLowerBoundThm{family.Add(registry.ProofEntry{
	Name: "NatProductLowerBound",
	Key:  "prop_b058705ba09b4552",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(A). ∀f:(A → num). ∀c:num.",
		Hypotheses: []string{
			"finite(s)",
			"∀x:A. x ∈ s ⇒ c ≤ f(x)",
		},
		Conclusion: "c ^ card(s) ≤ product(s, f)",
	},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Nat], c *Expr[Nat], finite, bounded Fact) {
			a.Show(
				"the product of the constant c, c ^ card(s), is at most it",
				By(
					Normalized,
					finite,
					bounded,
					NatProductMonotone.At(s, a.TermAs[Fun[A, Nat]]("λx:A. c"), f),
					NatProductConst.At(s, c)))
		}),
})}

// FactorialProduct — n! is the product of 1, …, n. By induction on n: the
// range 1 .. 0 is empty and its product is 1 = 0!, and the range up to
// n + 1 is the range up to n with the new top factor n + 1 put in.
var FactorialProduct = factorialProductThm{family.Add(registry.ProofEntry{
	Name: "FactorialProduct",
	Key:  "prop_d0317ed80994129d",
	Build: family.Theorem("∀n:num. factorial(n) = Π_{i∈1 .. n} i",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"the range 1 .. 0 is empty, and the empty product is 1 = 0!",
				func(b *Argument) {
					empty := b.Have(
						"no number lies between 1 and 0",
						"1 .. 0 = ∅",
						By(num_segment.Empty.At(b.Ctx().Nat(1), b.Ctx().Nat(0))))
					b.Show(
						"so both sides are 1",
						By(Normalized, empty, nat_arith.Factorial, NatProductClauses))
				})
			a.Step(
				"the range up to n + 1 adds the top factor n + 1, as (n + 1)! does",
				func(b *Argument, ih Fact) {
					n := b.TermAs[Nat]("n")
					grow := b.Have(
						"the range up to n + 1 is the range up to n with n + 1 put in",
						"1 .. suc(n) = insert(suc(n), 1 .. n)",
						ByArith(num_segment.Rec.At(b.Ctx().Nat(1), n)))
					fresh := b.Have(
						"n + 1 is not in the range up to n",
						"suc(n) ∉ 1 .. n",
						ByArith())
					b.Show(
						"so the product over 1 .. n + 1 is (n + 1) times the product over 1 .. n, which is n!",
						By(
							ih,
							grow,
							fresh,
							nat_arith.Factorial,
							NatProductClauses,
							num_segment.Finite.At(b.Ctx().Nat(1), n)))
				})
		}),
})}
