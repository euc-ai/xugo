// gauss_lemma.go — Gauss's lemma, (a/p) = (−1)^μ for μ the number of k·a,
// 1 ≤ k ≤ (p−1)/2, whose residue mod p passes (p−1)/2; and from it (2/p).

package quadratic_residue

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// LeastResiduesPermute — for an odd prime p = 2h + 1 and a not divisible by
// p, the absolute least residues of a, 2a, …, h·a are 1, …, h in some order: the
// residue r of k·a is not 0, and s(k) is r or p − r, whichever lies in
// 1 .. h. If s(x) = s(y), either the residues of x·a and y·a agree, and then
// x ≡ y, a cancelling, so x = y; or they add up to p, and then p divides
// (x + y)·a and so x + y, which lies between 2 and 2h < p.
var LeastResiduesPermute = leastResiduesPermuteThm{family.Add(registry.ProofEntry{
	Name: "LeastResiduesPermute",
	Key:  "prop_f0e952a9260be094",
	Build: family.Theorem(Statement{
		Binders: "∀p a:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"¬(p ∣ a)",
		},
		Conclusion: "(∀k:num. k ∈ 1 .. «h»(p) ⇒ «s»(p, a, k) ∈ 1 .. «h»(p)) ∧ " +
			"injective_on(1 .. «h»(p), «s»(p, a))",
	}, func(arg *Argument, p, a *Expr[Nat], prime, odd, notDivides Fact) {
		oddPrime := arg.Have(
			"p is odd, so p = 2h + 1",
			"p = 2 * «h»(p) + 1",
			By(prime, odd, nat_prime.OddPrimeHalf.At(p)))
		coprime := arg.Have(
			"a is prime to p",
			"nat_coprime(a, p)",
			By(
				Normalized,
				prime,
				notDivides,
				nat_prime.PrimeCoprimeIffNotDivides.At(p),
				nat_gcd.CoprimeSym.At(a, p)))
		into := arg.Have(
			"each s(k) lies in 1 .. h",
			"∀k:num. k ∈ 1 .. «h»(p) ⇒ «s»(p, a, k) ∈ 1 .. «h»(p)",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				inRange := b.Assume()
				ka := b.TermAs[Nat]("k * a")
				nonzero := b.Have(
					"p divides neither k, which lies below it, nor a, so not k·a: its residue is not 0",
					"0 < rem(k * a, p)",
					ByArith(
						prime,
						notDivides,
						oddPrime,
						inRange,
						nat_divides.DividesMod.At(p, ka),
						nat_prime.EuclidLemma.At(p, k, a),
						nat_divides.DividesLessEq.At(p, k)))
				b.Show(
					"a residue r with 0 < r < p = 2h + 1 has r or p − r in 1 .. h",
					ByArith(nonzero, oddPrime, prime, nat_prime.PrimeAtLeastTwo.At(p), nat_div_mod.Division.At(ka, p)))
			}))
		injective := arg.Have(
			"and no two of them coincide",
			"injective_on(1 .. «h»(p), «s»(p, a))",
			Derive(func(b *Argument) {
				b.Do(Unfold(functions.InjectiveOnDef))
				x, y := b.FixAs[Nat]("x"), b.FixAs[Nat]("y")
				given := b.Assume()
				parts := b.Conjuncts(
					given,
					"x lies in 1 .. h",
					"y lies in 1 .. h",
					"s(x) = s(y)")
				xa, ya := b.TermAs[Nat]("x * a"), b.TermAs[Nat]("y * a")
				b.Cases(b.TermAs[Bool]("rem(x * a, p) = rem(y * a, p)"))
				b.When(
					"when x·a and y·a leave one residue, a cancels and x ≡ y, two numbers below p",
					func(c *Argument, sameResidue Fact) {
						congruent := c.Have(
							"a, prime to p, cancels from x·a ≡ y·a",
							"x ≡ y (mod p)",
							By(
								sameResidue,
								coprime,
								nat_congruence.CongDef.At(xa, ya, p),
								nat_congruence.MulCancel.At(a, x, y, p),
								nat_arith.MulSym.At(x, a),
								nat_arith.MulSym.At(y, a)))
						c.Show(
							"two numbers below p with one residue are equal",
							ByArith(
								oddPrime,
								parts[0],
								parts[1],
								congruent,
								nat_congruence.CongDef.At(x, y, p),
								nat_div_mod.ModInjectiveBelow.At(x, y, p)))
					})
				b.Otherwise(
					"otherwise the residues are r and p − r, so p divides (x + y)·a, which cannot be",
					func(c *Argument, differentResidues Fact) {
						sum := c.TermAs[Nat]("x + y")
						complementary := c.Have(
							"s(x) = s(y) with different residues makes them add up to p",
							"rem(x * a, p) + rem(y * a, p) = p",
							ByArith(
								prime,
								differentResidues,
								parts[2],
								nat_prime.PrimeAtLeastTwo.At(p),
								nat_div_mod.Division.At(xa, p),
								nat_div_mod.Division.At(ya, p)))
						divides := c.Have(
							"so x·a + y·a leaves residue 0",
							"p ∣ (x + y) * a",
							By(
								Normalized,
								complementary,
								nat_divides.DividesMod.At(p, c.TermAs[Nat]("(x + y) * a")),
								nat_arith.RightAddDistrib.At(x, y, a),
								nat_div_mod.ModAddMod.At(xa, ya, p),
								nat_div_mod.ModRefl.At(p)))
						c.Show(
							"p does not divide a, so it divides x + y, which lies between 2 and 2h < p",
							ByArith(
								prime,
								notDivides,
								oddPrime,
								divides,
								parts[0],
								parts[1],
								nat_prime.EuclidLemma.At(p, sum, a),
								nat_divides.DividesLessEq.At(p, sum)))
					})
			}))
		arg.Show(
			"s maps 1 .. h into itself, one to one",
			By(into, injective))
	}),
})}

// GaussLemma — Gauss's lemma: for an odd prime p = 2h + 1 and a not divisible
// by p, (a/p) = (−1)^μ, where μ counts the k in 1 .. h whose residue k·a mod p
// lies above h. The product R of the residues of a, 2a, …, h·a is a^h·h!
// mod p, each residue being congruent to k·a; and it is (−1)^μ·h!, since each
// residue is ± its absolute least residue s(k), with the minus sign exactly
// for the μ residues above h, and the s(k) are 1, …, h in some order. p does
// not divide h!, so a^h ≡ (−1)^μ, and Euler's criterion turns a^h into
// (a/p); both lie between −1 and 1, so they are equal.
var GaussLemma = gaussLemmaThm{family.Add(registry.ProofEntry{
	Name: "GaussLemma",
	Key:  "prop_48a87271d6840117",
	Build: family.Theorem(Statement{
		Binders: "∀p a:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"¬(p ∣ a)",
		},
		Conclusion: "legendre_symbol(a, p) = (-int_of_num(1)) ^ card(«above»)",
		Abbrev: Abbrev{
			{Name: "ε", Text: "λk:num. COND(«h»(p) < rem(k * a, p), -int_of_num(1), int_of_num(1))"},
			{Name: "R", Text: "Π_{k∈1 .. «h»(p)} int_of_num(rem(k * a, p))"},
			{Name: "above", Text: "{k:num | 1 ≤ k ∧ k ≤ «h»(p) ∧ «h»(p) < rem(k * a, p)}"},
			{Name: "aboveSegment", Text: "{k:num | k ∈ 1 .. «h»(p) ∧ «h»(p) < rem(k * a, p)}"},
		},
	}, func(arg *Argument, p, a *Expr[Nat], prime, odd, notDivides Fact) {
		half := arg.TermAs[Nat]("«h»(p)")
		range_ := arg.TermAs[Set[Nat]]("1 .. «h»(p)")
		modulus := arg.TermAs[Int]("p")
		residue := arg.TermAs[Fun[Nat, Int]]("λk:num. rem(k * a, p)")
		symbol := arg.TermAs[Int]("legendre_symbol(a, p)")
		sign := arg.TermAs[Int]("(-&1) ^ card(«above»)")
		embedding := arg.TermAs[Fun[Nat, Int]]("int_of_num")
		leastResidue := arg.TermAs[Fun[Nat, Nat]]("«s»(p, a)")
		finite := num_segment.Finite.At(arg.TermAs[Nat]("1"), half)
		factorials := arg.Have(
			"h! read in ℤ is the product of 1, …, h read there, casting a product factor by factor",
			"Π_{k∈1 .. «h»(p)} int_of_num(k) = int_of_num(Π_{k∈1 .. «h»(p)} k)",
			By(finite, int_product.IntOfNatProduct.At(range_, arg.TermAs[Fun[Nat, Nat]]("λk:num. k"))))
		permutation := arg.Conjuncts(
			GroupPremises(prime, odd, notDivides, LeastResiduesPermute.At(p, a)),
			"s maps 1 .. h into itself",
			"one to one")
		signs := arg.Have(
			"each residue is its least residue s(k), with a minus sign when it lies above h",
			"∀k:num. rem(k * a, p) ≡ «ε»(k) * int_of_num(«s»(p, a, k)) (mod int_of_num(p))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("k")
				r := b.TermAs[Int]("rem(k * a, p)")
				signed := b.TermAs[Int]("«ε»(k) * int_of_num(«s»(p, a, k))")
				b.Cases(b.TermAs[Bool]("«h»(p) < rem(k * a, p)"))
				b.When(
					"above h, the residue r is −(p − r) up to p",
					func(c *Argument, above Fact) {
						difference := c.Have(
							"r − (−(p − r)) = p",
							"rem(k * a, p) - «ε»(k) * int_of_num(«s»(p, a, k)) = int_of_num(1) * p",
							ByArith(
								prime,
								above,
								nat_prime.PrimeAtLeastTwo.At(p),
								nat_div_mod.Division.At(c.TermAs[Nat]("k * a"), p),
								int_embed.OfNumSub.At(c.TermAs[Nat]("rem(k * a, p)"), p)))
						c.Show(
							"a difference that is a multiple of p is a congruence mod p",
							By(
								difference,
								int_congruence.IntCongDef.At(r, signed, modulus),
								int_divides.DividesOwnMultiple.At(modulus, c.TermAs[Int]("1"))))
					})
				b.Otherwise(
					"at most h, the residue is its own least residue",
					func(c *Argument, below Fact) {
						difference := c.Have(
							"r − r = 0",
							"rem(k * a, p) - «ε»(k) * int_of_num(«s»(p, a, k)) = int_of_num(0) * p",
							ByArith(below))
						c.Show(
							"a difference that is a multiple of p is a congruence mod p",
							By(
								difference,
								int_congruence.IntCongDef.At(r, signed, modulus),
								int_divides.DividesOwnMultiple.At(modulus, c.TermAs[Int]("0"))))
					})
			}))
		signedFactor := arg.TermAs[Fun[Nat, Int]]("λk:num. «ε»(k) * int_of_num(«s»(p, a, k))")
		signProduct := arg.Have(
			"Π ε(k)·s(k) = (−1)^μ·h!, the s(k) running over 1 .. h",
			"Π_{k∈1 .. «h»(p)} «ε»(k) * int_of_num(«s»(p, a, k)) = "+
				"(-int_of_num(1)) ^ card(«aboveSegment») * factorial(«h»(p))",
			CalcEq(
				Leg(
					arg.TermAs[Int]("(Π_{k∈1 .. «h»(p)} «ε»(k)) * Π_{k∈1 .. «h»(p)} int_of_num(«s»(p, a, k))"),
					"a product of products over a finite set is the product of the two products",
					Unfold(int_product.IntProductDef),
					By(finite, monoidal.Pointwise, int_real_lift.MonoidalMul)),
				Leg(
					arg.TermAs[Int]("(-&1) ^ card(«aboveSegment») * Π_{k∈1 .. «h»(p)} int_of_num(«s»(p, a, k))"),
					"the signs multiply to (−1)^μ, one −1 for each residue above h",
					By(
						finite,
						int_product.IntProductSigns.At(
							arg.TermAs[Fun[Nat, Bool]]("λk:num. «h»(p) < rem(k * a, p)"), range_))),
				Leg(
					arg.TermAs[Int]("(-&1) ^ card(«aboveSegment») * Π_{k∈1 .. «h»(p)} &k"),
					"s permutes 1 .. h, so the s(k) have the product of 1, …, h",
					By(
						permutation[0],
						permutation[1],
						finite,
						monoidal.Injection.Read(int_real_lift.MonoidalMul).At(embedding, leastResidue, range_),
						functions.ComposeApply.At(embedding, leastResidue),
						int_product.IntProductDef)),
				FinalLeg(
					"which is h! read in ℤ",
					By(factorials, nat_product.FactorialProduct.At(half)))))
		signSide := arg.Have(
			"so R ≡ (−1)^μ·h!, its factors congruent one by one to the ε(k)·s(k)",
			"«R» ≡ (-int_of_num(1)) ^ card(«aboveSegment») * factorial(«h»(p)) (mod int_of_num(p))",
			signProduct.RwRev(),
			By(finite, signs, int_congruence.ProductCongruent.At(modulus, residue, signedFactor, range_)))
		residues := arg.Have(
			"each residue is congruent to k·a",
			"∀k:num. rem(k * a, p) ≡ k * &a (mod int_of_num(p))",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				ka := b.TermAs[Nat]("k * a")
				b.Show(
					"k·a is congruent to its residue, read in ℤ",
					By(
						nat_congruence.ResidueCongruent.At(ka, p),
						int_congruence.OfNumCongruent.At(b.TermAs[Nat]("rem(k * a, p)"), ka, p),
						int_embed.OfNumMul.At(k, a)))
			}))
		multiple := arg.TermAs[Fun[Nat, Int]]("λk:num. k * int_of_num(a)")
		powerProduct := arg.Have(
			"Π k·a = h!·a^h",
			"Π_{k∈1 .. «h»(p)} int_of_num(k) * int_of_num(a) = factorial(«h»(p)) * int_of_num(a) ^ «h»(p)",
			CalcEq(
				Leg(
					arg.TermAs[Int]("(Π_{k∈1 .. «h»(p)} &k) * Π_{k∈1 .. «h»(p)} &a"),
					"a product of products over a finite set is the product of the two products",
					Unfold(int_product.IntProductDef),
					By(finite, monoidal.Pointwise, int_real_lift.MonoidalMul)),
				Leg(
					arg.TermAs[Int]("factorial(«h»(p)) * Π_{k∈1 .. «h»(p)} &a"),
					"the product of 1, …, h is h! read in ℤ",
					By(factorials, nat_product.FactorialProduct.At(half))),
				FinalLeg(
					"and a, taken once for each of the h numbers, is a^h",
					By(
						finite,
						num_segment.CardFromOne.At(half),
						int_product.IntProductConst.At(arg.TermAs[Int]("a"), range_)))))
		powerSide := arg.Have(
			"so R ≡ h!·a^h, its factors congruent one by one to the k·a",
			"«R» ≡ factorial(«h»(p)) * int_of_num(a) ^ «h»(p) (mod int_of_num(p))",
			powerProduct.RwRev(),
			By(finite, residues, int_congruence.ProductCongruent.At(modulus, residue, multiple, range_)))
		factorialPrime := arg.Have(
			"p does not divide h!, h being below p",
			"¬(int_of_num(p) ∣ factorial(«h»(p)))",
			ByArith(
				prime,
				nat_prime.PrimeAtLeastTwo.At(p),
				nat_div_mod.DivLessEq.At(arg.TermAs[Nat]("p - 1"), arg.TermAs[Nat]("2")),
				int_divides.OfNumDivides.At(p, arg.TermAs[Nat]("factorial(«h»(p))")),
				nat_prime.PrimeDividesFactorial.At(p, half)))
		minusOnes := arg.TermAs[Int]("(-&1) ^ card(«aboveSegment»)")
		factorial := arg.TermAs[Int]("factorial(«h»(p))")
		cancelled := arg.Have(
			"h! cancels from h!·a^h ≡ R ≡ (−1)^μ·h!",
			"int_of_num(a) ^ «h»(p) ≡ (-int_of_num(1)) ^ card(«aboveSegment») (mod int_of_num(p))",
			By(
				prime,
				factorialPrime,
				powerSide,
				signSide,
				int_congruence.CongruentIffSameRem,
				int_real_lift.MulSym.At(minusOnes, factorial),
				finite_field.CongruenceCancel.At(p, factorial, arg.TermAs[Int]("&a ^ «h»(p)"), minusOnes)))
		counted := arg.Have(
			"μ counts the k in 1 .. h above h: the products run over the segment, "+
				"the headline bounds 1 ≤ k ≤ h as UpperHalfCount reads it at a = 2",
			"«aboveSegment» = «above»",
			BySets())
		congruent := arg.Have(
			"Euler's criterion: a^h ≡ (a/p), so (a/p) ≡ (−1)^μ",
			"legendre_symbol(a, p) ≡ (-int_of_num(1)) ^ card(«above») (mod int_of_num(p))",
			By(
				prime,
				odd,
				counted,
				cancelled,
				EulerCriterion.At(p, arg.TermAs[Int]("a")),
				int_congruence.CongruentIffSameRem))
		arg.Show(
			"two values between −1 and 1 congruent modulo p are equal",
			ByArith(
				prime,
				odd,
				congruent,
				LegendreValues.At(arg.TermAs[Int]("a"), p),
				int_pow.NegOnePowValues.At(arg.TermAs[Nat]("card(«above»)")),
				int_congruence.EqOfCongruentSigns.At(p, symbol, sign)))
	}),
})}

// LegendreTwo — the second supplement: for an odd prime p, (2/p) = 1
// exactly when p ≡ ±1 (mod 8). Gauss's lemma at a = 2: the doubles 2k of
// k ≤ h stay below p, so μ counts the k ≤ h with 2k > h, which number
// h − ⌊h/2⌋; (−1)^μ = 1 exactly when that count is even, which is exactly
// when p = 2h + 1 ≡ ±1 (mod 8).
var LegendreTwo = legendreTwoThm{family.Add(registry.ProofEntry{
	Name: "LegendreTwo",
	Key:  "prop_7e935c94aebc638e",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "legendre_symbol(2, p) = 1 ⇔ rem(p, 8) = 1 ∨ rem(p, 8) = 7",
	}, func(arg *Argument, p *Expr[Nat], prime, odd Fact) {
		two := arg.TermAs[Nat]("2")
		half := arg.TermAs[Nat]("«h»(p)")
		count := arg.TermAs[Nat]("«h»(p) - div(«h»(p), 2)")
		oddPrime := arg.Have(
			"p = 2h + 1",
			"p = 2 * «h»(p) + 1",
			By(prime, odd, nat_prime.OddPrimeHalf.At(p)))
		gauss := arg.Have(
			"Gauss's lemma at 2, which p does not divide",
			"legendre_symbol(2, p) = (-1) ^ card({k:num | 1 ≤ k ∧ k ≤ «h»(p) ∧ «h»(p) < rem(k * 2, p)})",
			ByArith(
				prime,
				odd,
				nat_prime.PrimeDividesPrime.At(p, two),
				nat_prime.PrimeTwo,
				GaussLemma.At(p, two)))
		doubles := arg.Have(
			"for k ≤ h the double 2k ≤ 2h stays below p and is its own residue",
			"∀k:num. k ≤ «h»(p) ⇒ rem(k * 2, p) = 2 * k",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("k")
				bounded := b.Assume()
				b.Show(
					"2k < p",
					ByArith(bounded, oddPrime, nat_div_mod.ModLessThan.At(b.TermAs[Nat]("k * 2"), p)))
			}))
		counted := arg.Have(
			"so μ counts the k ≤ h with 2k > h",
			"{k:num | 1 ≤ k ∧ k ≤ «h»(p) ∧ «h»(p) < rem(k * 2, p)} = "+
				"{k:num | 1 ≤ k ∧ k ≤ «h»(p) ∧ «h»(p) < 2 * k}",
			BySets(doubles))
		power := arg.Have(
			"which number h − ⌊h/2⌋",
			"legendre_symbol(2, p) = (-1) ^ («h»(p) - div(«h»(p), 2))",
			By(counted, gauss, num_segment.UpperHalfCount.At(half)))
		parity := int_pow.NegOnePowParity.At(count)
		even := nat_parity.UpperHalfCountEven.At(half)
		arg.Cases(arg.TermAs[Bool]("nat_even(«h»(p) - div(«h»(p), 2))"))
		arg.When(
			"an even count makes (2/p) = 1, and p = 2h + 1 ≡ ±1 (mod 8)",
			func(b *Argument, evenCount Fact) {
				b.Show(
					"both sides hold",
					ByArith(evenCount, power, oddPrime, parity, even))
			})
		arg.Otherwise(
			"an odd count makes (2/p) = −1, and p ≢ ±1 (mod 8)",
			func(b *Argument, oddCount Fact) {
				b.Show(
					"both sides fail",
					ByArith(oddCount, power, oddPrime, parity, even))
			})
	}),
})}

// LegendreTwoSign — the second supplement for the Legendre symbol, as a
// sign: for an odd prime p, (2/p) = (−1)^((p² − 1)/8). The symbol (2/p) is 1
// or −1, p not dividing 2; it is 1 exactly when p ≡ ±1 (mod 8), and that is
// exactly when (p² − 1)/8 is even, which makes the power of −1 one.
var LegendreTwoSign = legendreTwoSignThm{family.Add(registry.ProofEntry{
	Name: "LegendreTwoSign",
	Key:  "prop_3cb7a4e95bffad77",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "legendre_symbol(2, p) = (-1) ^ div(p * p - 1, 8)",
	}, func(arg *Argument, p *Expr[Nat], prime, odd Fact) {
		two := arg.Ctx().Nat(2)
		signs := arg.Have(
			"p does not divide 2, so (2/p) is 1 or −1",
			"legendre_symbol(2, p) = 1 ∨ legendre_symbol(2, p) = -1",
			By(
				prime,
				odd,
				int_divides.OfNumDivides.At(p, two),
				nat_prime.PrimeDividesPrime.At(p, two),
				nat_prime.PrimeTwo,
				LegendreSymbolDef.At(arg.TermAs[Int]("2"), p)))
		oddP := arg.Have(
			"p is odd, a prime other than 2",
			"nat_odd(p)",
			By(prime, odd, nat_prime.PrimeOddUnlessTwo.At(p)))
		arg.Show(
			"(2/p) = 1 exactly when p ≡ ±1 (mod 8), exactly when (p² − 1)/8 is even",
			By(
				prime,
				odd,
				oddP,
				signs,
				LegendreTwo.At(p),
				nat_parity.OddSquareEighthEven.At(p),
				int_pow.NegOnePowParity.At(arg.TermAs[Nat]("div(p * p - 1, 8)"))))
	}),
})}
