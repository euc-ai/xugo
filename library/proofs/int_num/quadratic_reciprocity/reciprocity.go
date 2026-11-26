// reciprocity.go — the law of quadratic reciprocity: for distinct odd
// primes p and q, (p/q)(q/p) = (−1)^((p−1)/2 · (q−1)/2).
//
// The proof computes in an algebraically closed field M of characteristic
// q, which holds a p-th root of unity ζ ≠ 1. There the Gauss sum g has
// square p* = (−1/p)·p, read in M through the integers' map, and p* is
// not divisible by q, so g ≠ 0. The q-th power of g is computed twice:
// the q-th power map is additive in characteristic q and sends g to
// (q/p)·g; and g^q = (g²)^((q−1)/2)·g, where (p*)^((q−1)/2) is (p*/q)
// mod q by Euler's criterion. Cancelling g leaves (q/p) ≡ (p*/q) mod q,
// and two symbols congruent mod q are equal. The law itself is then sign
// bookkeeping: (p*/q) = ((−1/p)/q)·(p/q), the first factor is
// (−1)^((p−1)/2 · (q−1)/2) because the symbol of a power is the power of
// the symbol, and (p/q)² = 1.
//
// The law carries to Jacobi symbols: for odd m and n prime to each other,
// (m/n)(n/m) = (−1)^((m−1)/2 · (n−1)/2). Both symbols are multiplicative in
// each argument, and so is the sign on odd numbers, so the law at m and n
// follows from the law at their prime factors, two strong inductions
// splitting off one odd prime at a time: first m against an odd prime p,
// then m against any odd n.

package quadratic_reciprocity

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/gauss_sum"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/roots_of_unity"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/quadratic_residue"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// _ClosurePoint is the type of the points of the algebraically closed
// field the proof computes in, the type roots_of_unity.ClosedFieldOfCharacteristic
// builds that field on.
type _ClosurePoint = Set[Prod[Nat, Fun[Nat, Set[Int]]]]

// PrimeNotDividesPStar — a prime q other than the odd prime p does not divide
// p* = (−1/p)·p: (−1/p) = (−1)^((p−1)/2) squares to 1, so p*·(−1/p) = p, and
// q dividing p* would divide p, which of two distinct primes it does not.
var PrimeNotDividesPStar = primeNotDividesPStarThm{family.Add(registry.ProofEntry{
	Name: "PrimeNotDividesPStar",
	Key:  "prop_50dd0d94c6c58d10",
	Build: family.Theorem(Statement{
		Binders: "∀p q:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"nat_prime(q)",
			"p ≠ 2",
			"p ≠ q",
		},
		Conclusion: "¬(q ∣ «p*»(p))",
	}, func(arg *Argument, p, q *Expr[Nat], primeP, primeQ, oddP, distinct Fact) {
		half := arg.TermAs[Nat]("«h»(p)")
		minusOne := arg.TermAs[Int]("-1")
		sign := arg.TermAs[Int]("legendre_symbol(-1, p)")
		negSquare := arg.Have(
			"(−1)·(−1) = 1",
			"-1 * -1 = int_of_num(1)",
			ByArith())
		signSquare := arg.Have(
			"(−1/p) = (−1)^((p−1)/2) squares to ((−1)·(−1))^((p−1)/2) = 1",
			"legendre_symbol(-1, p) * legendre_symbol(-1, p) = 1",
			By(
				primeP,
				oddP,
				negSquare,
				quadratic_residue.LegendreMinusOne.At(p),
				int_pow.MulPow.At(minusOne, minusOne, half),
				int_pow.OnePow.At(half)))
		recovered := arg.Have(
			"so p*·(−1/p) = p",
			"«p*»(p) * legendre_symbol(-1, p) = p",
			ByArith(Scaled(arg.TermAs[Int]("p"), signSquare)))
		arg.Show(
			"q dividing p* would divide p*·(−1/p) = p, and of two distinct primes neither divides the other",
			By(
				primeP,
				primeQ,
				distinct,
				recovered,
				nat_prime.PrimeDividesPrime.At(q, p),
				int_divides.OfNumDivides.At(q, p),
				int_divides.DividesProduct.At(arg.TermAs[Int]("q"), arg.TermAs[Int]("«p*»(p)"), sign)))
	}),
})}

// QuadraticCharacterOfPStar — for distinct odd primes p and q, (q/p) =
// (p*/q), where p* = (−1/p)·p. In an algebraically closed field M of
// characteristic q holding a p-th root of unity ζ ≠ 1, the Gauss sum g has
// g² = p*, which is not zero there because q does not divide p*. The q-th
// power of g is (q/p)·g, since the q-th power map is additive and fixes
// the integers; it is also (g²)^((q−1)/2)·g, which Euler's criterion mod q
// reads as (p*/q)·g. Cancelling g, the two symbols have one image in M,
// so they are congruent mod q, and two symbols congruent mod q are equal.
var QuadraticCharacterOfPStar = quadraticCharacterOfPStarThm{family.Add(registry.ProofEntry{
	Name: "QuadraticCharacterOfPStar",
	Key:  "prop_ee65730eb157a84f",
	Build: family.Theorem(Statement{
		Binders: "∀p q:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"nat_prime(q)",
			"p ≠ 2",
			"q ≠ 2",
			"p ≠ q",
		},
		Conclusion: "legendre_symbol(&q, p) = legendre_symbol(«p*»(p), q)",
	}, func(arg *Argument, p, q *Expr[Nat], primeP, primeQ, oddP, oddQ, distinct Fact) {
		halfQ := arg.TermAs[Nat]("«h»(q)")
		pStar := arg.TermAs[Int]("«p*»(p)")
		symbolQ := arg.TermAs[Int]("legendre_symbol(q, p)")
		symbolStar := arg.TermAs[Int]("legendre_symbol(«p*»(p), q)")

		// In the integers: q does not divide p*.
		starNotDivides := arg.Simplified(
			GroupPremises(primeP, primeQ, oddP, distinct, PrimeNotDividesPStar.At(p, q)))

		// In a field M of characteristic q holding a p-th root of unity
		// ζ ≠ 1: the Gauss sum g, its square p*, and g ≠ 0.
		M, closedField := arg.UnpackAs[field.FieldOps[_ClosurePoint]](
			GroupPremises(primeQ, roots_of_unity.ClosedFieldOfCharacteristic.At(q)),
			"M")
		fieldParts := arg.Conjuncts(
			closedField,
			"M is a field",
			"algebraically closed",
			"of characteristic q",
			"q is the prime characteristic of its ring")
		fieldM, closed, characteristicQ, characteristic :=
			fieldParts[0], fieldParts[1], fieldParts[2], fieldParts[3]
		ring := field.RingOn.Read(fieldM)
		powers := comm_ring.MulMonoidOn.Read(ring)
		ζ, root := arg.UnpackAs[_ClosurePoint](
			GroupPremises(
				closed,
				characteristic,
				primeP,
				distinct,
				roots_of_unity.RootOfUnityInClosedField.Read(fieldM).At(p, q)),
			"ζ")
		rootParts := arg.Conjuncts(
			root,
			"ζ lies in M",
			"ζ is not one",
			"ζ is a p-th root of unity")
		ζm := arg.MemberOf[on.Any](ζ, rootParts[0])
		g, gDef := arg.LetAs[_ClosurePoint]("g", "gauss_sum(M, ζ, p)")

		termIn := arg.Have(
			"each term (a/p)·ζᵃ of g lies in M",
			"∀a:num. "+
				"    integer_map(field_ring(M), legendre_symbol(a, p)) * monoid_pow(M.mul, M.one, ζ, a) ∈ "+
				"    M.carrier",
			By(
				comm_ring.MulIn.Read(ring),
				characteristic_zero.IntegerMapInCarrier.Read(ring),
				comm_monoid.PowIn.Read(powers),
				ζm))
		gm := arg.MemberOf[on.Any](g, arg.Have(
			"so does g, a finite sum of them",
			"g ∈ M.carrier",
			By(
				gDef,
				termIn,
				gauss_sum.GaussSumDef.At(M, ζ, p),
				module.ModuleSumIn.Read(module.RegularModuleOn.Read(ring)).At(
					arg.TermAs[Set[Nat]]("{a:num | a < p}"),
					arg.TermAs[Fun[Nat, _ClosurePoint]](
						"λa:num. integer_map(field_ring(M), legendre_symbol(a, p)) * monoid_pow(M.mul, M.one, ζ, a)")),
				num_segment.FiniteBelowStrict.At(p))))
		square := arg.Have(
			"g² = p*, the square of the Gauss sum",
			"g * g = integer_map(field_ring(M), «p*»(p))",
			By(primeP, oddP, rootParts[1], rootParts[2], gDef, gauss_sum.GaussSumSquare.Read(fieldM).At(ζm, p)))
		zero := arg.MemberOf[on.Any](arg.TermAs[_ClosurePoint]("M.zero"), comm_ring.ZeroIn.Read(ring))
		nonzero := arg.Have(
			"g is not zero: its square p* is not, q not dividing p*",
			"g ≠ M.zero",
			By(
				square,
				characteristicQ,
				starNotDivides,
				finite_field.IntegerMapKernel.Read(fieldM).At(q, pStar),
				comm_ring.MulLeftZeroOn.Read(ring).At(zero)))

		// The q-th power of g, computed two ways.
		frobenius := arg.Have(
			"in characteristic q the q-th power map sends g to (q/p)·g",
			"monoid_pow(M.mul, M.one, g, q) = integer_map(field_ring(M), legendre_symbol(q, p)) * g",
			By(
				Normalized,
				primeP,
				oddP,
				characteristic,
				rootParts[2],
				gDef,
				gauss_sum.GaussSumFrobenius.Read(fieldM).At(ζm, p, q)))
		eulerImage := arg.Have(
			"Euler's criterion mod q, read in M: p* to the power (q − 1)/2 has the image of (p*/q)",
			"integer_map(field_ring(M), «p*»(p) ^ «h»(q)) = "+
				"integer_map(field_ring(M), legendre_symbol(«p*»(p), q))",
			By(
				primeQ,
				oddQ,
				characteristicQ,
				quadratic_residue.EulerCriterion.At(q, pStar),
				finite_field.IntegerMapEqIff.Read(fieldM).At(q, arg.TermAs[Int]("«p*»(p) ^ «h»(q)"), symbolStar)))
		euler := arg.Have(
			"g^q is also (g²)^((q−1)/2)·g, which is (p*/q)·g",
			"monoid_pow(M.mul, M.one, g, q) = integer_map(field_ring(M), legendre_symbol(«p*»(p), q)) * g",
			CalcEq(
				Leg(
					arg.TermAs[_ClosurePoint]("monoid_pow(M.mul, M.one, g * g, «h»(q)) * g"),
					"q = 2·((q − 1)/2) + 1",
					By(
						primeQ,
						oddQ,
						nat_prime.OddPrimeHalf.At(q),
						comm_monoid.PowAddOn.Read(powers).At(gm, arg.TermAs[Nat]("2 * «h»(q)"), arg.TermAs[Nat]("1")),
						comm_monoid.PowPowOn.Read(powers).At(gm, arg.TermAs[Nat]("2"), halfQ),
						comm_monoid.PowOneOn.Read(powers).At(gm),
						comm_monoid.PowTwoOn.Read(powers).At(gm))),
				Leg(
					arg.TermAs[_ClosurePoint](
						"monoid_pow(M.mul, M.one, integer_map(field_ring(M), «p*»(p)), «h»(q)) * g"),
					"g² = p*",
					square.Rw(),
					Basic()),
				Leg(
					arg.TermAs[_ClosurePoint]("integer_map(field_ring(M), «p*»(p) ^ «h»(q)) * g"),
					"the integers' map takes a power to the power of the image",
					By(characteristic_zero.IntegerMapPow.Read(ring).At(pStar, halfQ))),
				FinalLeg(
					"Euler's criterion mod q",
					eulerImage.Rw(),
					Basic())))

		// Cancel g, and read the equation of images back in the integers.
		symbolQm := arg.MemberOf[on.Any](
			arg.TermAs[_ClosurePoint]("integer_map(field_ring(M), legendre_symbol(q, p))"),
			characteristic_zero.IntegerMapInCarrier.Read(ring).At(symbolQ))
		symbolStarm := arg.MemberOf[on.Any](
			arg.TermAs[_ClosurePoint]("integer_map(field_ring(M), legendre_symbol(«p*»(p), q))"),
			characteristic_zero.IntegerMapInCarrier.Read(ring).At(symbolStar))
		images := arg.Have(
			"cancelling g ≠ 0, (q/p) and (p*/q) have one image in M",
			"integer_map(field_ring(M), legendre_symbol(&q, p)) = "+
				"integer_map(field_ring(M), legendre_symbol(«p*»(p), q))",
			By(
				frobenius,
				euler,
				nonzero,
				integral_domain.MulCancelRight.Read(integral_domain.FieldIntegralDomain.Read(fieldM)).At(
					gm, symbolQm, symbolStarm)))
		congruent := arg.Have(
			"so (q/p) ≡ (p*/q) mod q, M having characteristic q",
			"legendre_symbol(&q, p) ≡ legendre_symbol(«p*»(p), q) (mod q)",
			By(images, characteristicQ, finite_field.IntegerMapEqIff.Read(fieldM).At(q, symbolQ, symbolStar)))
		bounds := arg.Have(
			"both symbols lie between −1 and 1",
			"-1 ≤ legendre_symbol(q, p) ∧ "+
				"legendre_symbol(q, p) ≤ 1 ∧ "+
				"-1 ≤ legendre_symbol(«p*»(p), q) ∧ "+
				"legendre_symbol(«p*»(p), q) ≤ 1",
			ByArith(
				quadratic_residue.LegendreValues.At(arg.TermAs[Int]("q"), p),
				quadratic_residue.LegendreValues.At(pStar, q)))
		arg.Show(
			"two symbols between −1 and 1 congruent modulo the odd prime q are equal",
			By(primeQ, oddQ, bounds, congruent, int_congruence.EqOfCongruentSigns.At(q, symbolQ, symbolStar)))
	}),
})}

// QuadraticReciprocity — the law of quadratic reciprocity: for distinct odd
// primes p and q, (p/q)(q/p) = (−1)^((p−1)/2 · (q−1)/2). Gauss's computation
// gives (q/p) = (p*/q) with p* = (−1/p)·p, and (p*/q) = ((−1/p)/q)·(p/q).
// The first factor is a sign: (−1/p) = (−1)^((p−1)/2), the symbol of that
// power is the power of (−1/q) = (−1)^((q−1)/2), and the exponents
// multiply. And (p/q) is 1 or −1, q not dividing p, so its square is 1.
var QuadraticReciprocity = quadraticReciprocityThm{family.Add(registry.ProofEntry{
	Name: "QuadraticReciprocity",
	Key:  "prop_aaaf90ce4c183146",
	Build: family.Theorem(Statement{
		Binders: "∀p q:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"nat_prime(q)",
			"p ≠ 2",
			"q ≠ 2",
			"p ≠ q",
		},
		Conclusion: "legendre_symbol(&p, q) * legendre_symbol(q, p) = (-1) ^ («h»(p) * «h»(q))",
	}, func(arg *Argument, p, q *Expr[Nat], primeP, primeQ, oddP, oddQ, distinct Fact) {
		halfP, halfQ := arg.TermAs[Nat]("«h»(p)"), arg.TermAs[Nat]("«h»(q)")
		minusOne := arg.TermAs[Int]("-1")
		signValue := arg.Have(
			"((−1/p)/q) = (−1)^((p−1)/2 · (q−1)/2)",
			"legendre_symbol(legendre_symbol(-1, p), q) = (-1) ^ («h»(p) * «h»(q))",
			CalcEq(
				Leg(
					arg.TermAs[Int]("legendre_symbol((-&1) ^ «h»(p), q)"),
					"(−1/p) = (−1)^((p−1)/2)",
					By(primeP, oddP, quadratic_residue.LegendreMinusOne.At(p))),
				Leg(
					arg.TermAs[Int]("legendre_symbol(-&1, q) ^ «h»(p)"),
					"the symbol of a power is the power of the symbol",
					By(primeQ, oddQ, quadratic_residue.LegendrePow.At(minusOne, q, halfP))),
				Leg(
					arg.TermAs[Int]("((-&1) ^ «h»(q)) ^ «h»(p)"),
					"(−1/q) = (−1)^((q−1)/2)",
					By(primeQ, oddQ, quadratic_residue.LegendreMinusOne.At(q))),
				FinalLeg(
					"a power of a power multiplies the exponents",
					By(int_pow.PowPow.At(minusOne, halfQ, halfP), nat_arith.MulSym.At(halfQ, halfP)))))
		isSign := arg.Have(
			"q does not divide p, the two being distinct primes, so (p/q) is 1 or −1",
			"legendre_symbol(&p, q) = 1 ∨ legendre_symbol(p, q) = -1",
			By(
				primeP,
				primeQ,
				distinct,
				nat_prime.PrimeDividesPrime.At(q, p),
				int_divides.OfNumDivides.At(q, p),
				quadratic_residue.LegendreSymbolDef.At(arg.TermAs[Int]("p"), q)))
		unit := arg.Have(
			"and its square is 1",
			"legendre_symbol(&p, q) * legendre_symbol(p, q) = 1",
			isSign.SplitDisj(
				LeftHolds(
					"(p/q) = 1",
					Given(func(b *Argument, one Fact) {
						b.Show(
							"1·1 = 1",
							ByArith(one))
					})),
				RightHolds(
					"(p/q) = −1",
					Given(func(b *Argument, minus Fact) {
						b.Show(
							"(−1)·(−1) = 1",
							ByArith(minus))
					}))))
		arg.Show(
			"(p/q)(q/p) = (p/q)·((−1/p)/q)·(p/q), a sign times a square",
			CalcEq(
				Leg(
					arg.TermAs[Int]("legendre_symbol(&p, q) * legendre_symbol(legendre_symbol(-1, p) * p, q)"),
					"(q/p) = (p*/q), by the Gauss sum",
					By(primeP, primeQ, oddP, oddQ, distinct, QuadraticCharacterOfPStar.At(p, q))),
				Leg(
					arg.TermAs[Int](
						"legendre_symbol(&p, q) * (legendre_symbol(legendre_symbol(-1, p), q) * legendre_symbol(p, q))"),
					"the symbol mod q is multiplicative",
					By(
						primeQ,
						oddQ,
						quadratic_residue.LegendreMul.At(
							arg.TermAs[Int]("legendre_symbol(-1, p)"), arg.TermAs[Int]("p"), q))),
				FinalLeg(
					"((−1/p)/q) is the sign, and (p/q)² = 1",
					ByArith(signValue, Scaled(arg.TermAs[Int]("legendre_symbol(legendre_symbol(-1, p), q)"), unit)))))
	}),
})}

// HalfOddSignPowMul — on odd numbers the sign (−1)^((n−1)/2 · k) is
// multiplicative in n, at every k: it is the k-th power of (−1)^((n−1)/2),
// which is multiplicative on odd numbers, and the k-th power of a product is
// the product of the k-th powers.
var HalfOddSignPowMul = halfOddSignPowMulThm{family.Add(registry.ProofEntry{
	Name: "HalfOddSignPowMul",
	Key:  "prop_7df62297b39da4ec",
	Build: family.Theorem(Statement{
		Binders: "∀m n k:num.",
		Hypotheses: []string{
			"nat_odd(m)",
			"nat_odd(n)",
		},
		Conclusion: "(-int_of_num(1)) ^ («h»(m * n) * k) = " +
			"(-int_of_num(1)) ^ («h»(m) * k) * (-int_of_num(1)) ^ («h»(n) * k)",
	}, func(a *Argument, m, n, k *Expr[Nat], mOdd, nOdd Fact) {
		minusOne := a.TermAs[Int]("-1")
		halfM, halfN := a.TermAs[Nat]("«h»(m)"), a.TermAs[Nat]("«h»(n)")
		a.Show(
			"the k-th power of the sign at m·n, which is the product of the signs at m and at n",
			CalcEq(
				Leg(
					a.TermAs[Int]("((-&1) ^ «h»(m * n)) ^ k"),
					"a power of a power multiplies the exponents",
					By(int_pow.PowPow.At(minusOne, a.TermAs[Nat]("«h»(m * n)"), k))),
				Leg(
					a.TermAs[Int]("((-&1) ^ «h»(m) * (-&1) ^ «h»(n)) ^ k"),
					"the sign (−1)^((n−1)/2) is multiplicative on odd numbers",
					By(mOdd, nOdd, HalfOddSignMul.At(m, n))),
				Leg(
					a.TermAs[Int]("((-&1) ^ «h»(m)) ^ k * ((-&1) ^ «h»(n)) ^ k"),
					"the k-th power of a product is the product of the k-th powers",
					By(int_pow.MulPow.At(a.TermAs[Int]("(-&1) ^ «h»(m)"), a.TermAs[Int]("(-&1) ^ «h»(n)"), k))),
				FinalLeg(
					"and a power of a power multiplies the exponents",
					By(int_pow.PowPow.At(minusOne, halfM, k), int_pow.PowPow.At(minusOne, halfN, k)))))
	}),
})}

// JacobiReciprocityPrime — the law of reciprocity between an odd number and
// an odd prime: for an odd prime p not dividing an odd m,
// (m/p)(p/m) = (−1)^((m−1)/2 · (p−1)/2). By strong induction on m: at m = 1
// both symbols are 1 and the exponent is 0. Past 1, m = q·k with q an odd
// prime and k odd and below m, and q is not p and p does not divide k, since
// either would make p divide m. Both symbols split over the factors, the
// prime p being odd; (q/p)(p/q) is quadratic reciprocity for the distinct odd
// primes q and p, (k/p)(p/k) is the law below m, and the two signs multiply
// to the sign at q·k.
var JacobiReciprocityPrime = jacobiReciprocityPrimeThm{family.Add(registry.ProofEntry{
	Name: "JacobiReciprocityPrime",
	Key:  "prop_78e6713fed0b2e75",
	Build: family.Theorem(Statement{
		Binders: "∀p m:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
			"nat_odd(m)",
			"¬(p ∣ m)",
		},
		Conclusion: "jacobi_symbol(m, p) * jacobi_symbol(p, m) = (-1) ^ («h»(m) * «h»(p))",
	}, func(a *Argument, p *Expr[Nat], prime, notTwo Fact) {
		two := a.Ctx().Nat(2)
		oddP := a.Have(
			"p is odd, a prime other than 2",
			"nat_odd(p)",
			By(prime, notTwo, nat_prime.PrimeOddUnlessTwo.At(p)))
		a.Show(
			"strong induction on m, splitting off one prime factor",
			ByInduction(nat_order.StrongInduction,
				Case(
					"granted the law at every odd number below m that p does not divide, it holds at m",
					Derive(func(b *Argument) {
						m := b.FixAs[Nat]("m")
						below := b.Assume()
						onM := b.Conjuncts(
							b.Assume(),
							"m is odd",
							"p does not divide m")
						odd, notDivides := onM[0], onM[1]
						b.Cases(b.Term("m = 1"))
						b.When(
							"m = 1: (1/p) = 1 = (p/1), and the exponent is 0",
							func(c *Argument, isOne Fact) {
								zero := c.Ctx().Nat(0)
								c.Show(
									"(1 − 1)/2 = 0",
									ByArith(
										isOne,
										JacobiOne.At(p),
										JacobiAtOne.At(c.TermAs[Int]("p")),
										nat_div_mod.DivUniq.At(c.TermAs[Nat]("m - 1"), two, zero, zero)))
							})
						b.Otherwise(
							"m > 1: split off an odd prime factor q, m = q·k",
							func(c *Argument, notOne Fact) {
								q, k, split := c.Unpack2As[Nat, Nat](
									GroupPremises(odd, notOne, nat_prime.OddPrimeSplit.At(m)), "q", "k")
								factors := c.Conjuncts(
									split,
									"q is prime",
									"q is not 2",
									"q is odd",
									"k is odd",
									"m = q·k",
									"k < m")
								primeQ, notTwoQ, oddQ, oddK, mIs, kBelow :=
									factors[0], factors[1], factors[2], factors[3], factors[4], factors[5]
								apart := c.Have(
									"q is not p and p does not divide k: either would make p divide m = q·k",
									"q ≠ p ∧ ¬(p ∣ k)",
									By(
										Normalized,
										notDivides,
										mIs,
										nat_divides.DividesMul.At(p, p, k),
										nat_divides.DividesRefl.At(p),
										nat_divides.DividesMul.At(p, k, q),
										nat_arith.MulSym.At(k, q)))
								nonzero := c.Have(
									"q and k are odd, so neither is 0",
									"q ≠ 0 ∧ k ≠ 0",
									By(oddQ, oddK, nat_parity.NatOdd))
								c.Show(
									"(m/p)(p/m) = (q/p)(p/q)·(k/p)(p/k): reciprocity for the primes q and p times the law below m at k",
									CalcEq(
										Leg(
											c.TermAs[Int]("jacobi_symbol(&q * &k, p) * jacobi_symbol(p, q * k)"),
											"m = q·k",
											By(Normalized, mIs, int_embed.OfNumMul.At(q, k))),
										Leg(
											c.TermAs[Int]("jacobi_symbol(q, p) * "+
												"jacobi_symbol(k, p) * "+
												"(jacobi_symbol(&p, q) * jacobi_symbol(p, k))"),
											"the symbol is multiplicative in each argument, p being odd and q and k not 0",
											By(
												oddP,
												nonzero,
												JacobiMulLeft.At(c.TermAs[Int]("q"), c.TermAs[Int]("k"), p),
												JacobiMulRight.At(c.TermAs[Int]("p"), q, k))),
										Leg(
											c.TermAs[Int]("jacobi_symbol(q, p) * "+
												"jacobi_symbol(p, q) * "+
												"(jacobi_symbol(&k, p) * jacobi_symbol(p, k))"),
											"regroup the four factors",
											ByArith()),
										Leg(
											c.TermAs[Int]("(-&1) ^ («h»(q) * «h»(p)) * (-1) ^ («h»(k) * «h»(p))"),
											"at the primes the symbols are Legendre symbols, "+
												"which reciprocity relates, and the law below m at k",
											By(
												prime,
												notTwo,
												primeQ,
												notTwoQ,
												apart,
												oddK,
												kBelow,
												below.At(k),
												JacobiPrime.At(c.TermAs[Int]("q"), p),
												JacobiPrime.At(c.TermAs[Int]("p"), q),
												QuadraticReciprocity.At(q, p))),
										Leg(
											c.TermAs[Int]("(-&1) ^ («h»(q * k) * «h»(p))"),
											"the sign is multiplicative in odd numbers",
											By(oddQ, oddK, HalfOddSignPowMul.At(q, k, c.TermAs[Nat]("«h»(p)")))),
										FinalLeg(
											"q·k = m",
											By(mIs))))
							})
					}))))
	}),
})}

// JacobiReciprocity — the law of reciprocity for Jacobi symbols: for odd m and
// n prime to each other, (m/n)(n/m) = (−1)^((m−1)/2 · (n−1)/2). By strong
// induction on n, for the m given: at n = 1 both symbols are 1 and the
// exponent is 0. Past 1, n = p·k with p an odd prime and k odd and below n.
// The prime p does not divide m, a common divisor of m and n being 1, and m is
// prime to k. Both symbols split over the factors, m being odd; (m/p)(p/m) is
// the law against the odd prime p, (m/k)(k/m) is the law below n, and the two
// signs multiply to the sign at p·k.
var JacobiReciprocity = jacobiReciprocityThm{family.Add(registry.ProofEntry{
	Name: "JacobiReciprocity",
	Key:  "prop_57d9d4024875e97d",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"nat_odd(m)",
			"nat_odd(n)",
			"nat_coprime(m, n)",
		},
		Conclusion: "jacobi_symbol(m, n) * jacobi_symbol(n, m) = (-1) ^ («h»(m) * «h»(n))",
	}, func(a *Argument, m *Expr[Nat], oddM Fact) {
		a.Show(
			"strong induction on n, splitting off one prime factor",
			ByInduction(nat_order.StrongInduction,
				Case(
					"granted the law at every odd number below n prime to m, it holds at n",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						below := b.Assume()
						onN := b.Conjuncts(
							b.Assume(),
							"n is odd",
							"m is prime to n")
						odd, coprime := onN[0], onN[1]
						b.Cases(b.Term("n = 1"))
						b.When(
							"n = 1: (m/1) = 1 = (1/m), and the exponent is 0",
							func(c *Argument, isOne Fact) {
								two, zero := c.Ctx().Nat(2), c.Ctx().Nat(0)
								c.Show(
									"(1 − 1)/2 = 0",
									ByArith(
										isOne,
										JacobiAtOne.At(c.TermAs[Int]("m")),
										JacobiOne.At(m),
										nat_div_mod.DivUniq.At(c.TermAs[Nat]("n - 1"), two, zero, zero)))
							})
						b.Otherwise(
							"n > 1: split off an odd prime factor p, n = p·k",
							func(c *Argument, notOne Fact) {
								p, k, split := c.Unpack2As[Nat, Nat](
									GroupPremises(odd, notOne, nat_prime.OddPrimeSplit.At(n)), "p", "k")
								factors := c.Conjuncts(
									split,
									"p is prime",
									"p is not 2",
									"p is odd",
									"k is odd",
									"n = p·k",
									"k < n")
								prime, notTwo, oddP, oddK, nIs, kBelow :=
									factors[0], factors[1], factors[2], factors[3], factors[4], factors[5]
								notDivides := c.Have(
									"p does not divide m: a common divisor of m and n = p·k is 1, and the prime p is not",
									"¬(p ∣ m)",
									By(
										prime,
										nIs,
										coprime,
										nat_gcd.Coprime.At(m, n),
										nat_divides.DividesMul.At(p, p, k),
										nat_divides.DividesRefl.At(p),
										nat_prime.PrimeDef.At(p)))
								coprimeK := c.Have(
									"m is prime to k: a common divisor of m and k divides n = k·p",
									"nat_coprime(m, k)",
									By(
										nIs,
										coprime,
										nat_gcd.Coprime.At(m, n),
										nat_gcd.Coprime.At(m, k),
										nat_divides.DividesMul,
										nat_arith.MulSym.At(p, k)))
								nonzero := c.Have(
									"p and k are odd, so neither is 0",
									"p ≠ 0 ∧ k ≠ 0",
									By(oddP, oddK, nat_parity.NatOdd))
								halfM := c.TermAs[Nat]("«h»(m)")
								c.Show(
									"(m/n)(n/m) = (m/p)(p/m)·(m/k)(k/m): the law against the prime p times the law below n at k",
									CalcEq(
										Leg(
											c.TermAs[Int]("jacobi_symbol(&m, p * k) * jacobi_symbol(p * &k, m)"),
											"n = p·k",
											By(Normalized, nIs, int_embed.OfNumMul.At(p, k))),
										Leg(
											c.TermAs[Int]("jacobi_symbol(m, p) * "+
												"jacobi_symbol(m, k) * "+
												"(jacobi_symbol(p, m) * jacobi_symbol(k, m))"),
											"the symbol is multiplicative in each argument, m being odd and p and k not 0",
											By(
												oddM,
												nonzero,
												JacobiMulRight.At(c.TermAs[Int]("m"), p, k),
												JacobiMulLeft.At(c.TermAs[Int]("p"), c.TermAs[Int]("k"), m))),
										Leg(
											c.TermAs[Int]("jacobi_symbol(m, p) * "+
												"jacobi_symbol(p, m) * "+
												"(jacobi_symbol(&m, k) * jacobi_symbol(k, m))"),
											"regroup the four factors",
											ByArith()),
										Leg(
											c.TermAs[Int]("(-&1) ^ («h»(m) * «h»(p)) * (-1) ^ («h»(m) * «h»(k))"),
											"the law against the odd prime p, which does not "+
												"divide m, and the law below n at the odd k prime to m",
											By(
												oddM,
												prime,
												notTwo,
												notDivides,
												oddK,
												kBelow,
												coprimeK,
												below.At(k),
												JacobiReciprocityPrime.At(p, m))),
										Leg(
											c.TermAs[Int]("(-&1) ^ («h»(m) * «h»(p * k))"),
											"the sign is multiplicative in odd numbers",
											By(
												oddP,
												oddK,
												HalfOddSignPowMul.At(p, k, halfM),
												nat_arith.MulSym.At(halfM, c.TermAs[Nat]("«h»(p)")),
												nat_arith.MulSym.At(halfM, c.TermAs[Nat]("«h»(k)")),
												nat_arith.MulSym.At(halfM, c.TermAs[Nat]("«h»(p * k)")))),
										FinalLeg(
											"p·k = n",
											By(nIs))))
							})
					}))))
	}),
})}
