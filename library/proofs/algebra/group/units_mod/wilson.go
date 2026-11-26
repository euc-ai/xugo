// wilson.go — Wilson's theorem, (p − 1)! + 1 ≡ 0 (mod p) for a prime p, and
// its converse; and −1 a square mod a prime p ≡ 1 (mod 4), by complements to p.

package units_mod

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Products over ℕ
// ---------------------------------------------------------------------------

// ProductPairedInverses — a finite set of numbers that a map σ pairs off,
// each x with a partner σ(x) ≠ x in the set, σ(σ(x)) = x, and
// x · σ(x) ≡ 1 (mod n), has product ≡ 1 (mod n). By strong induction on
// the size: the empty set has product 1; otherwise take a point y out
// together with its partner σ(y). σ still pairs off what is left, which is
// smaller, so its product is ≡ 1, and the whole product is y · σ(y) ≡ 1
// times it.
var ProductPairedInverses = productPairedInversesThm{family.Add(registry.ProofEntry{
	Name: "ProductPairedInverses",
	Key:  "prop_313913a28f067fe",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀σ:(num → num). ∀s:set(num).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:num. x ∈ s ⇒ σ(x) ∈ s ∧ σ(σ(x)) = x ∧ σ(x) ≠ x ∧ x * σ(x) ≡ 1 (mod n)",
		},
		Conclusion: "Π_{x∈s} x ≡ 1 (mod n)",
		Abbrev: Abbrev{
			{Name: "pairsOff", Text: "λt:set(num). ∀x:num. " +
				"    x ∈ t ⇒ σ(x) ∈ t ∧ σ(σ(x)) = x ∧ σ(x) ≠ x ∧ x * σ(x) ≡ 1 (mod n)"},
			{Name: "claimAtSize", Text: "λk:num. ∀t:set(num). " +
				"    finite(t) ∧ card(t) = k ∧ «pairsOff»(t) ⇒ Π_{x∈t} x ≡ 1 (mod n)"},
			{Name: "rest", Text: "delete(delete(t, y), σ(y))"},
		},
	}, func(a *Argument, n *Expr[Nat], σ *Arrow[Nat, Nat], s *Expr[Set[Nat]], pairing Fact) {
		bySize := a.Have(
			"every finite set σ pairs off has product ≡ 1, by strong induction on its size",
			"∀k:num. «claimAtSize»(k)",
			ByInduction(nat_order.StrongInduction,
				Case(
					"granted the claim below size k, a set of size k loses a pair and keeps the rest's product",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("k")
						below := b.Assume()
						t := b.FixAs[Set[Nat]]("t")
						given := b.Conjuncts(
							b.Assume(),
							"t is finite",
							"t has k points",
							"σ pairs off t")
						finite, size, pairs := given[0], given[1], given[2]
						b.Cases(b.Term("t = ∅"))
						b.When(
							"the empty product is 1",
							func(c *Argument, empty Fact) {
								c.Show(
									"the product over ∅ is 1, and 1 ≡ 1: it leaves its own remainder",
									empty.Rw(),
									Simp(Fwd(nat_product.NatProductClauses)),
									Unfold(nat_congruence.CongDef))
							})
						b.Otherwise(
							"take a point y of t and its partner σ(y) out",
							func(c *Argument, nonempty Fact) {
								y, inT := c.ObtainAs[Nat](
									"t has a point y",
									"∃y:num. y ∈ t",
									By(nonempty, set_basic.MemberNotEmpty.At(t)))
								σy := σ.Apply(y)
								withoutY := c.TermAs[Set[Nat]]("delete(t, y)")
								rest := c.TermAs[Set[Nat]]("«rest»")
								restTotal := c.TermAs[Nat]("Π_{x∈«rest»} x")
								partner := c.Have(
									"σ(y) is still there once y is taken out",
									"σ(y) ∈ delete(t, y)",
									BySets(inT, pairs.At(y)))
								identity := c.TermAs[Fun[Nat, Nat]]("λx:num. x")
								takeY := c.Have(
									"the product over t is y times the product without y",
									"y * (Π_{x∈delete(t, y)} x) = Π_{x∈t} x",
									By(
										finite,
										inT,
										monoidal.Delete.Read(nat_product.MonoidalNatMul).At(t, identity, y),
										nat_product.NatProductDef))
								takeσy := c.Have(
									"and that is σ(y) times the product over the rest",
									"σ(y) * (Π_{x∈«rest»} x) = Π_{x∈delete(t, y)} x",
									By(
										finite,
										partner,
										finite_set.FiniteDelete.At(t, y),
										monoidal.Delete.Read(nat_product.MonoidalNatMul).At(withoutY, identity, σy),
										nat_product.NatProductDef))
								shrink := c.Have(
									"taking the two out leaves two points fewer",
									"card(t) = suc(suc(card(«rest»)))",
									By(
										finite,
										inT,
										partner,
										finite_set.FiniteDelete.At(t, y),
										cardinality.CountsOneMore.At(t, y),
										cardinality.CountsOneMore.At(withoutY, σy)))
								smaller := c.Have(
									"so the rest is smaller than t",
									"card(«rest») < k",
									ByArith(size, shrink))
								restPairs := c.Have(
									"σ still pairs off the rest: a partner of a point there is neither y nor σ(y)",
									"«pairsOff»(«rest»)",
									Derive(func(d *Argument) {
										x := d.FixAs[Nat]("x")
										inRest := d.Assume()
										d.Show(
											"σ(x) = y would give x = σ(y), and σ(x) = σ(y) would give x = y",
											BySets(inRest, inT, pairs.At(x), pairs.At(y)))
									}))
								restProduct := c.Have(
									"by the claim at the rest's size, its product is ≡ 1",
									"Π_{x∈«rest»} x ≡ 1 (mod n)",
									By(
										finite,
										smaller,
										restPairs,
										below.At(c.TermAs[Nat]("card(«rest»)"), rest),
										finite_set.FiniteDelete.At(t, y),
										finite_set.FiniteDelete.At(withoutY, σy)))
								c.Show(
									"so the product over t is y·σ(y) ≡ 1 times a product ≡ 1",
									By(
										inT,
										pairs.At(y),
										takeY,
										takeσy,
										restProduct,
										nat_congruence.MulCongruent.At(
											c.TermAs[Nat]("y * σ(y)"), c.Ctx().Nat(1), restTotal, c.Ctx().Nat(1), n),
										nat_arith.MulAssoc.At(y, σy, restTotal),
										nat_arith.MulOne.At(c.Ctx().Nat(1))))
							})
					}))))
		a.Show(
			"s is such a set, at its own size",
			By(pairing, bySize.At(a.TermAs[Nat]("card(s)"), s)))
	}),
})}

// ---------------------------------------------------------------------------
// Wilson's theorem
// ---------------------------------------------------------------------------

// Wilson — for a prime p, (p − 1)! ≡ −1 (mod p), written over ℕ as
// (p − 1)! + 1 ≡ 0 (mod p). At p = 2 it is 1! + 1 = 2. For p ≥ 3 the units
// mod p are 1, …, p − 1 (UnitsModPrime), and the group inverse σ pairs off
// the residues other than 1 and p − 1: σ is an involution of the units
// with x · σ(x) ≡ 1, it fixes no such residue since only 1 and p − 1 are
// their own inverses (nat_prime.SelfInverse), and so it does not send one
// to 1 or to p − 1 either. Their product is ≡ 1 (ProductPairedInverses), so
// (p − 1)! = (p − 1) times it is ≡ p − 1, and (p − 1)! + 1 ≡ p ≡ 0.
var Wilson = wilsonThm{family.Add(registry.ProofEntry{
	Name: "Wilson",
	Key:  "prop_9a10b0a78a302e3f",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "factorial(p - 1) + 1 ≡ 0 (mod p)",
		Abbrev: Abbrev{
			{Name: "rest", Text: "delete(delete(1 .. p - 1, 1), p - 1)"},
		},
	}, func(a *Argument, p *Expr[Nat], prime Fact) {
		atLeastTwo := a.Have(
			"a prime is at least 2",
			"2 ≤ p",
			By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
		vanishes := a.Have(
			"p ≡ 0: p and 0 both leave the remainder 0 mod p",
			"p ≡ 0 (mod p)",
			By(
				Normalized,
				nat_congruence.CongDef.At(p, a.Ctx().Nat(0), p),
				nat_div_mod.ModRefl.At(p),
				nat_div_mod.ZeroMod.At(p)))
		a.Cases(a.Term("p = 2"))
		a.When(
			"p = 2: 1! + 1 = 2, which 2 divides",
			func(b *Argument, two Fact) {
				sum := b.Have(
					"1! + 1 = 2",
					"factorial(p - 1) + 1 = p",
					ByArith(two, nat_arith.Factorial, nat_arith.OneIsSucZero))
				b.Show(
					"so (p − 1)! + 1 is p, and p ≡ 0",
					By(Normalized, sum, vanishes))
			})
		a.Otherwise(
			"p ≥ 3: the residues other than 1 and p − 1 pair off with their inverses",
			func(b *Argument, notTwo Fact) {
				units := b.Have(
					"the units mod p form an abelian group",
					"abelian_group_on(units_mod(p))",
					ByArith(atLeastTwo, AbelianGroupOn.At(p)))
				unitGroup := abelian_group.GroupOn.Read(units)
				residues := b.Have(
					"mod the prime p the units are the residues 1, …, p − 1",
					"units_mod(p).carrier = 1 .. p - 1",
					By(prime, UnitsModPrime.At(p)))
				σ, σDef := b.LetAs[Fun[Nat, Nat]]("σ", "units_mod(p).inv")
				pairs := b.Have(
					"σ pairs off the residues other than 1 and p − 1, each with its inverse",
					"∀x:num. x ∈ «rest» ⇒ σ(x) ∈ «rest» ∧ σ(σ(x)) = x ∧ σ(x) ≠ x ∧ x * σ(x) ≡ 1 (mod p)",
					Derive(func(c *Argument) {
						x := c.FixAs[Nat]("x")
						inRest := c.Assume()
						σx := c.TermAs[Nat]("σ(x)")
						unit := c.Have(
							"x is a unit",
							"x ∈ units_mod(p).carrier",
							BySets(residues, inRest))
						partnerUnit := c.Have(
							"so is its inverse σ(x)",
							"σ(x) ∈ units_mod(p).carrier",
							σDef.Rw(),
							By(unit, group.InvIn.Read(unitGroup)))
						involution := c.Have(
							"the inverse of the inverse is x",
							"σ(σ(x)) = x",
							σDef.Rw(),
							By(unit, group.InvInvOn.Read(unitGroup)))
						inverse := c.Have(
							"x times its inverse is the identity, the residue of 1",
							"x * σ(x) ≡ 1 (mod p)",
							σDef.Rw(),
							By(unit, group.RightInverseOn.Read(unitGroup), MulEqOne))
						bounds := c.Have(
							"x lies in 1 .. p − 1 and is neither 1 nor p − 1",
							"x ≠ 1 ∧ x ≠ p - 1 ∧ 1 ≤ x ∧ x ≤ p - 1",
							BySets(inRest, num_segment.IntervalDef))
						nonzero := c.Have(
							"x is a nonzero residue",
							"0 < x ∧ x < p",
							ByArith(atLeastTwo, bounds))
						unfixed := c.Have(
							"σ fixes no x: only 1 and p − 1 are their own inverses",
							"σ(x) ≠ x",
							By(Normalized, prime, nonzero, bounds, inverse, nat_prime.SelfInverse.At(p, x)))
						partnerRange := c.Have(
							"σ(x) lies in 1 .. p − 1",
							"σ(x) ∈ 1 .. p - 1",
							BySets(residues, partnerUnit))
						partnerNonzero := c.Have(
							"σ(x) is a nonzero residue",
							"0 < σ(x) ∧ σ(x) < p",
							ByArith(atLeastTwo, partnerRange))
						selfPaired := c.Have(
							"if σ(x) were its own inverse, it would be the inverse of σ(x), which is x",
							"σ(x) * σ(x) ≡ 1 (mod p) ⇒ σ(x) = x",
							σDef.Rw(),
							Derive(func(d *Argument) {
								square := d.Assume()
								d.Show(
									"σ(x)·σ(x) is the identity, so σ(x) = x",
									By(square, unit, partnerUnit, σDef, MulEqOne, group.InvMulEqOneOn.Read(unitGroup)))
							}))
						notEnds := c.Have(
							"so σ(x) is neither 1 nor p − 1, which are their own inverses",
							"σ(x) ≠ 1 ∧ σ(x) ≠ p - 1",
							By(prime, unfixed, selfPaired, partnerNonzero, nat_prime.SelfInverse.At(p, σx)))
						c.Show(
							"σ(x) is another residue of «rest», paired back to x",
							BySets(residues, partnerUnit, notEnds, involution, unfixed, inverse))
					}))
				rest := b.TermAs[Set[Nat]]("«rest»")
				segment := b.TermAs[Set[Nat]]("1 .. p - 1")
				top := b.TermAs[Nat]("p - 1")
				one := b.Ctx().Nat(1)
				finiteRest := b.Have(
					"«rest» is finite",
					"finite(«rest»)",
					By(
						finite_set.FiniteDelete.At(b.TermAs[Set[Nat]]("delete(1 .. p - 1, 1)"), top),
						finite_set.FiniteDelete.At(segment, one),
						num_segment.Finite.At(one, top)))
				paired := b.Have(
					"so the product over «rest» is ≡ 1",
					"Π_{x∈«rest»} x ≡ 1 (mod p)",
					By(finiteRest, pairs, ProductPairedInverses.At(p, σ, rest)))
				ends := b.Have(
					"1 and p − 1 are two different residues of 1 .. p − 1",
					"1 ∈ 1 .. p - 1 ∧ p - 1 ∈ delete(1 .. p - 1, 1)",
					ByArith(notTwo, atLeastTwo, set_basic.InDelete.At(segment, top, one)))
				identity := b.TermAs[Fun[Nat, Nat]]("λx:num. x")
				split := b.Have(
					"(p − 1)! is 1 · (p − 1) times the product over «rest»",
					"factorial(p - 1) = (p - 1) * Π_{x∈«rest»} x",
					By(
						ends,
						nat_product.FactorialProduct.At(top),
						monoidal.Delete.Read(nat_product.MonoidalNatMul).At(segment, identity, one),
						monoidal.Delete.Read(nat_product.MonoidalNatMul).At(
							b.TermAs[Set[Nat]]("delete(1 .. p - 1, 1)"), identity, top),
						nat_product.NatProductDef,
						num_segment.Finite.At(one, top),
						finite_set.FiniteDelete.At(segment, one),
						nat_arith.OneMul))
				residue := b.Have(
					"so (p − 1)! ≡ p − 1",
					"factorial(p - 1) ≡ p - 1 (mod p)",
					By(
						split,
						paired,
						nat_congruence.MulCongruent.At(top, top, b.TermAs[Nat]("Π_{x∈«rest»} x"), one, p),
						nat_congruence.CongDef.At(top, top, p),
						nat_arith.MulOne.At(top)))
				carry := b.Have(
					"p − 1 + 1 = p",
					"p - 1 + 1 = p",
					ByArith(atLeastTwo))
				successor := b.TermAs[Nat]("factorial(p - 1) + 1")
				shifted := b.Have(
					"adding 1 to both sides, (p − 1)! + 1 ≡ p − 1 + 1, which is p",
					"factorial(p - 1) + 1 ≡ p (mod p)",
					By(
						carry,
						residue,
						nat_congruence.AddCongruent.At(b.TermAs[Nat]("factorial(p - 1)"), top, one, one, p),
						nat_congruence.CongDef.At(one, one, p)))
				b.Show(
					"so (p − 1)! + 1 ≡ p ≡ 0",
					By(
						shifted,
						vanishes,
						nat_congruence.CongDef.At(successor, p, p),
						nat_congruence.CongDef.At(p, b.Ctx().Nat(0), p),
						nat_congruence.CongDef.At(successor, b.Ctx().Nat(0), p)))
			})
	}),
})}

// WilsonConverse — the converse of Wilson's theorem: a number n > 1 with
// (n − 1)! + 1 ≡ 0 (mod n) is prime. The congruence says n divides
// (n − 1)! + 1. A divisor d of n other than n lies between 1 and n − 1, so
// it divides (n − 1)! (nat_divides.DividesFactorial); dividing n, it divides
// (n − 1)! + 1 as well, hence it divides 1, and d = 1.
var WilsonConverse = wilsonConverseThm{family.Add(registry.ProofEntry{
	Name: "WilsonConverse",
	Key:  "prop_b13fcc3686d65dfd",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"1 < n",
			"factorial(n - 1) + 1 ≡ 0 (mod n)",
		},
		Conclusion: "nat_prime(n)",
	}, func(a *Argument, n *Expr[Nat], large, wilson Fact) {
		factorial := a.TermAs[Nat]("factorial(n - 1)")
		successor := a.TermAs[Nat]("factorial(n - 1) + 1")
		remainder := a.Have(
			"the congruence says (n − 1)! + 1 leaves the remainder 0 mod n, as 0 does",
			"rem(factorial(n - 1) + 1, n) = 0",
			By(wilson, nat_congruence.CongDef.At(successor, a.Ctx().Nat(0), n), nat_div_mod.ZeroMod.At(n)))
		multiple := a.Have(
			"so n divides (n − 1)! + 1",
			"n ∣ factorial(n - 1) + 1",
			By(remainder, nat_divides.DividesMod.At(n, successor)))
		divisors := a.Have(
			"every divisor of n is 1 or n",
			"∀d:num. d ∣ n ⇒ d = 1 ∨ d = n",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				divides := b.Assume()
				proper := b.Unless(
					b.TermAs[Bool]("d = n"),
					"d = n is the second alternative",
					Given(func(c *Argument, whole Fact) {
						c.Show(
							"d is n",
							By(whole))
					}))
				bounds := b.Have(
					"a divisor of n other than n lies between 1 and n − 1",
					"1 ≤ d ∧ d ≤ n - 1",
					ByArith(proper, large, divides, nat_divides.DividesLessEqStrong.At(d, n)))
				b.Show(
					"so d divides (n − 1)! and (n − 1)! + 1, hence 1, and d = 1",
					By(
						divides,
						multiple,
						bounds,
						nat_divides.DividesFactorial.At(d, b.TermAs[Nat]("n - 1")),
						nat_divides.DividesTrans.At(d, n, successor),
						nat_divides.DividesAddCancel.At(d, factorial, b.Ctx().Nat(1)),
						nat_divides.DividesOne.At(d)))
			}))
		a.Show(
			"n is not 1, and its only divisors are 1 and n",
			ByArith(large, divisors, nat_prime.PrimeDef.At(n)))
	}),
})}

// ---------------------------------------------------------------------------
// −1 is a square mod a prime p ≡ 1 (mod 4)
// ---------------------------------------------------------------------------

// MinusOneSquare — for a prime p ≡ 1 (mod 4), p divides h!² + 1 where
// h = (p − 1)/2: −1 is the square of h! mod p. As p leaves 1 mod 4, h is
// the even number 2·div(p, 4), so the h factors of (p − 1)! above h pair
// off against 1, …, h (nat_congruence.FactorialSplitMod) and (p − 1)! ≡ h!²;
// Wilson's theorem makes (p − 1)! + 1 ≡ 0.
var MinusOneSquare = minusOneSquareThm{family.Add(registry.ProofEntry{
	Name: "MinusOneSquare",
	Key:  "prop_a4c6810db284544a",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"rem(p, 4) = 1",
		},
		Conclusion: "p ∣ factorial(«h») * factorial(«h») + 1",
		Abbrev: Abbrev{
			{Name: "h", Text: "div(p - 1, 2)"},
		},
	}, func(a *Argument, p *Expr[Nat], prime, oneModFour Fact) {
		quarter := a.TermAs[Nat]("div(p, 4)")
		twice := a.TermAs[Nat]("2 * div(p, 4)")
		square := a.TermAs[Nat]("factorial(«h») * factorial(«h»)")
		four := a.Have(
			"p leaves 1 mod 4: with q = div(p, 4), p − 1 = 2·(2q), and 2q "+
				"+ 2q + 1 = p is FactorialSplitMod's hypothesis at k = q, m = 2q",
			"p - 1 = 2 * (2 * div(p, 4)) ∧ 2 * div(p, 4) + 2 * div(p, 4) + 1 = p",
			ByArith(oneModFour, nat_div_mod.Division.At(p, a.Ctx().Nat(4))))
		even := a.Have(
			"so h is the even number 2·div(p, 4)",
			"«h» = 2 * div(p, 4)",
			By(four, nat_div_mod.DivMult.At(a.Ctx().Nat(2), twice)))
		split := a.Have(
			"the h factors of (p − 1)! above h pair off against 1, …, h, so (p − 1)! ≡ h!²",
			"factorial(p - 1) ≡ factorial(«h») * factorial(«h») (mod p)",
			By(four, even, nat_congruence.FactorialSplitMod.At(p, quarter, twice)))
		one, zero := a.Ctx().Nat(1), a.Ctx().Nat(0)
		factorialPlusOne := a.TermAs[Nat]("factorial(p - 1) + 1")
		squarePlusOne := a.TermAs[Nat]("factorial(«h») * factorial(«h») + 1")
		shifted := a.Have(
			"adding 1 to both sides, (p − 1)! + 1 ≡ h!² + 1",
			"factorial(p - 1) + 1 ≡ factorial(«h») * factorial(«h») + 1 (mod p)",
			By(
				split,
				nat_congruence.AddCongruent.At(a.TermAs[Nat]("factorial(p - 1)"), square, one, one, p),
				nat_congruence.CongDef.At(one, one, p)))
		vanishes := a.Have(
			"Wilson's theorem makes (p − 1)! + 1 ≡ 0, so h!² + 1 ≡ 0",
			"factorial(«h») * factorial(«h») + 1 ≡ 0 (mod p)",
			By(
				prime,
				shifted,
				Wilson.At(p),
				nat_congruence.CongDef.At(factorialPlusOne, squarePlusOne, p),
				nat_congruence.CongDef.At(factorialPlusOne, zero, p),
				nat_congruence.CongDef.At(squarePlusOne, zero, p)))
		remainder := a.Have(
			"so h!² + 1 leaves the remainder 0 mod p, as 0 does",
			"rem(factorial(«h») * factorial(«h») + 1, p) = 0",
			By(vanishes, nat_congruence.CongDef.At(squarePlusOne, zero, p), nat_div_mod.ZeroMod.At(p)))
		a.Show(
			"and p divides it",
			By(remainder, nat_divides.DividesMod.At(p, squarePlusOne)))
	}),
})}

// MinusOneSquareExists — mod a prime p ≡ 1 (mod 4), −1 is a square: some
// m has p ∣ m² + 1, namely m = ((p − 1)/2)! (MinusOneSquare).
var MinusOneSquareExists = minusOneSquareExistsThm{family.Add(registry.ProofEntry{
	Name: "MinusOneSquareExists",
	Key:  "prop_c5aa42fafb569e87",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"rem(p, 4) = 1",
		},
		Conclusion: "∃m:num. p ∣ m * m + 1",
	}, func(a *Argument, p *Expr[Nat], prime, oneModFour Fact) {
		a.Take(a.TermAs[Nat]("factorial(div(p - 1, 2))"))
		a.Show(
			"((p − 1)/2)! is such an m",
			By(prime, oneModFour, MinusOneSquare.At(p)))
	}),
})}
