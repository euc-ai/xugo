// pow.go — ℤ's power, read in definition order: the transfer theorem
// that makes the transported operation well-formed, the recursion
// equations that say what it computes, the law that it agrees with
// ℕ's power on the embedded naturals, and a first consequence read
// back across that law. Then the laws of exponents — a sum of
// exponents, a power of a power and the powers of 1, each ℝ's law
// carried across the embedding, and a power of a product, by induction
// on the exponent — and the powers of −1, which alternate with the
// parity of the exponent.

package int_pow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/registry"
)

// PowBridge — a power of an integer represents that power of its
// representative.
//
// Like every ℤ operation, int_pow is DEFINED by transport: it is the
// integer representing `real_pow(real_of_int(x), n)`, so unfolding that
// definition turns the statement into TypeBijection's round-trip at the
// ℝ-side answer, and what is left is the whole of the theorem's own
// mathematics: the argument that the answer is again an integer.
//
// That argument is an induction — an exponent is a natural, so
// `real_pow` is defined by recursion on it and there is no closed form
// to read a membership off. The two cases are the two defining
// equations. The empty product is &1, which is a natural on its face;
// one more factor multiplies the representative into the power already
// known to be an integer, which is the multiplicative closure law at
// those two.
//
// The exponent is a NATURAL, so it never crosses the bijection and is
// never anybody's representative: despite taking two arguments this is
// a one-argument bridge, and the induction runs on the side that stays
// put. A power is a repeated product and nothing else, so the additive
// and negation closure laws have no part in it.
var PowBridge = powBridgeThm{family.Add(registry.ProofEntry{
	Name: "PowBridge",
	Key:  "prop_7048e408785b4063",
	Build: family.Theorem("∀x:int. ∀n:num. real_of_int(int_pow(x, n)) = real_pow(real_of_int(x), n)",
		func(a *Argument, x, n Term) {
			v := ops(a.Ctx())
			rx := v.RealOfInt.Apply(x)     // real_of_int(x₀)
			powN := v.RealPow.Apply(rx, n) // real_of_int(x₀)^n₀

			// ↦ real_of_int(int_of_real(real_pow(real_of_int(x₀), n₀)))
			// = real_pow(real_of_int(x₀), n₀)
			a.Do(Unfold(IntPowDef))

			powerIsInteger := a.Have(
				"every power of a representative is an integer, by induction on the exponent",
				MakeProp(v.Integer.Apply(powN)),
				Derive(func(a *Argument) {
					a.Induct(n)
					a.Base(
						"n₀ = 0 — the empty product is &1, a natural on its face",
						// `real_pow` is cited bare in both cases: the row is
						// the two defining equations under one shared ∀, and
						// each case reads a different one, so there is no
						// single instance to name. Here it supplies
						// real_pow(r, 0) = &1.
						By(Normalized, real_pow.Pow, int_construction.IntegerOfNum.At(a.Ctx().Nat(1)))) // integer(&1)
					a.Step(
						"n₀ → suc n₀ — one more factor of the representative",
						func(a *Argument, ih Fact) {
							a.Show(
								"r^suc n₀ is r · r^n₀, an integer times an integer",
								By(
									Normalized,
									ih,
									// real_pow(r, suc n₀) = r · real_pow(r, n₀).
									real_pow.Pow,
									// integer(real_of_int(x₀)) — the new factor.
									At(int_construction.RepresentativeIsInteger, x),
									// integer(r) ⇒ integer(s) ⇒ integer(r · s),
									// at that factor and the power the
									// hypothesis is about.
									At(int_construction.IntegerClosedUnderMul, rx, powN),
								))
						})
				}))

			a.Show(
				"being an integer, the power comes back unchanged",
				By(powerIsInteger, int_construction.TypeBijection))
		}),
})}

// PowClauses — the empty product is &1, and each further factor is one
// more multiplication by the base. Everything an exponent means at ℤ is
// these two clauses; a consumer reasoning about a power reaches for them
// and then for the ring. They are not proved by recursion at ℤ — they
// are the image of ℝ's recursion, one transport step along the
// embedding, exactly the mechanism the ring laws arrive by.
var PowClauses = powClausesThm{family.Add(registry.ProofEntry{
	Name: "PowClauses",
	Key:  "prop_6bcc5b24205310d7",
	Build: family.Lifted(
		"∀x:int. int_pow(x, 0) = &1 ∧ ∀n:num. int_pow(x, suc(n)) = x * int_pow(x, n)", real_pow.Pow),
})}

// OfNumPow — & commutes with iterating a product. Only the base is
// embedded: the exponent is an ℕ index and stays one on both sides.
var OfNumPow = ofNumPowThm{family.Add(registry.ProofEntry{
	Name:  "OfNumPow",
	Key:   "prop_9adcc8681aa13d3c",
	Build: family.Lifted("∀x n:num. &(nat_pow(x, n)) = int_pow(&x, n)", real_pow.OfNumPow),
})}

// PowTwoNonzero — nat_arith.PowTwoNonzero carried into ℤ: OfNumPow above
// reads the power of the embedded base as an embedded power, so the ℕ
// fact plus the embedding's injectivity (int_embed.OfNumEq) refute the
// vanishing.
var PowTwoNonzero = powTwoNonzeroThm{family.Add(registry.ProofEntry{
	Name: "PowTwoNonzero",
	Key:  "prop_1b7ffe08494da1ae",
	Build: family.Theorem("∀n:num. int_pow(&2, n) ≠ &0",
		func(a *Argument) {
			a.Show(
				"read the power through & — nonzero there — and & is injective",
				By(OfNumPow, nat_arith.PowTwoNonzero, int_embed.OfNumEq))
		}),
})}

// PowAdd — a power of an integer splits over a sum of exponents: ℝ's law,
// carried across the embedding.
var PowAdd = powAddThm{family.Add(registry.ProofEntry{
	Name:  "PowAdd",
	Key:   "prop_351fee3da345962f",
	Build: family.Lifted("∀x:int. ∀m n:num. x ^ (m + n) = x ^ m * x ^ n", real_pow.PowAdd),
})}

// PowPow — a power of a power of an integer is the power at the product
// of the exponents: ℝ's law, carried across the embedding.
var PowPow = powPowThm{family.Add(registry.ProofEntry{
	Name:  "PowPow",
	Key:   "prop_777cb928122a2f8d",
	Build: family.Lifted("∀x:int. ∀m n:num. (x ^ m) ^ n = x ^ (m * n)", real_pow.PowPow),
})}

// OnePow — every power of 1 is 1: ℝ's law, carried across the embedding.
var OnePow = onePowThm{family.Add(registry.ProofEntry{
	Name:  "OnePow",
	Key:   "prop_f7d6b4145abc0920",
	Build: family.Lifted("∀n:num. &1 ^ n = int_of_num(1)", real_pow.OnePow),
})}

// MulPow — a power of a product of integers is the product of the
// powers: by induction, (xy)^(n+1) = xy·(xy)ⁿ = xy·xⁿyⁿ = x^(n+1)·y^(n+1).
var MulPow = mulPowThm{family.Add(registry.ProofEntry{
	Name: "MulPow",
	Key:  "prop_d393e42af5cabad6",
	Build: family.Theorem("∀x y:int. ∀n:num. (x * y) ^ n = x ^ n * y ^ n",
		func(arg *Argument, x, y *Expr[Int]) {
			arg.Induct("n")
			arg.Base(
				"each power at zero is one",
				ByArith(PowClauses))
			arg.Step(
				"one more factor xy on the left is one more x and one more y on the right",
				func(b *Argument, power Fact) {
					b.Show(
						"multiply the inductive hypothesis by xy",
						Simp(Fwd(PowClauses)),
						ByArith(Scaled(b.TermAs[Int]("x * y"), power)))
				})
		}),
})}

// NegOnePowParity — (−1)ⁿ is 1 for even n and −1 for odd n: by induction,
// each further factor −1 changes the sign and the parity.
var NegOnePowParity = negOnePowParityThm{family.Add(registry.ProofEntry{
	Name: "NegOnePowParity",
	Key:  "prop_44bd1ce73249f50f",
	Build: family.Theorem("∀n:num. (-1) ^ n = COND(nat_even(n), int_of_num(1), -1)",
		func(arg *Argument) {
			arg.Induct("n")
			arg.Base(
				"(−1)⁰ = 1, and 0 is even",
				ByArith(nat_parity.NatEven, PowClauses.At(arg.TermAs[Int]("-1"))))
			arg.Step(
				"one more factor −1 flips both the sign and the parity",
				func(b *Argument, ih Fact) {
					b.Do(Simp(Fwd(PowClauses), Fwd(nat_parity.NatEven)))
					b.Cases(b.TermAs[Bool]("nat_even(n)"))
					b.When(
						"n even: (−1)ⁿ = 1, and n + 1 is odd",
						func(c *Argument, even Fact) {
							c.Show(
								"so (−1)ⁿ⁺¹ = −1",
								ByArith(even, ih))
						})
					b.Otherwise(
						"n odd: (−1)ⁿ = −1, and n + 1 is even",
						func(c *Argument, oddN Fact) {
							c.Show(
								"so (−1)ⁿ⁺¹ = 1",
								ByArith(oddN, ih))
						})
				})
		}),
})}

// NegOnePowValues — every power of −1 is 1 or −1, as the parity formula shows.
var NegOnePowValues = negOnePowValuesThm{family.Add(registry.ProofEntry{
	Name: "NegOnePowValues",
	Key:  "prop_f3cee7cde05661",
	Build: family.Theorem("∀n:num. (-1) ^ n = int_of_num(1) ∨ (-1) ^ n = -int_of_num(1)",
		func(arg *Argument, n *Expr[Nat]) {
			arg.Show(
				"the parity formula takes one of its two values",
				By(NegOnePowParity.At(n)))
		}),
})}
