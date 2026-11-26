// two_squares.go — Fermat's theorem on the primes that are sums of two squares.

package sum_of_squares

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/units_mod"
	"github.com/euc-ai/xugo/library/proofs/complex/gaussian_integer"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/registry"
)

// FermatTwoSquares — Fermat's two-squares theorem: a prime is a sum of two
// squares exactly when it is 2 or leaves remainder 1 on division by 4. A
// prime p ≡ 1 (mod 4) divides some m² + 1, and a prime that does is a sum
// of two squares. An odd prime a² + b² has a and b of opposite parities, so
// one square leaves 0 and the other 1 mod 4.
var FermatTwoSquares = fermatTwoSquaresThm{family.Add(registry.ProofEntry{
	Name: "FermatTwoSquares",
	Key:  "prop_9740eea1a1df7553",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:num.",
			Hypotheses: []string{
				"nat_prime(p)",
			},
			Conclusion: "(∃a b:num. p = a * a + b * b) ⇔ p = 2 ∨ rem(p, 4) = 1",
		},
		func(arg *Argument, p *Expr[Nat], prime Fact) {
			one, two, four := arg.Ctx().Nat(1), arg.Ctx().Nat(2), arg.Ctx().Nat(4)
			arg.Iff()
			arg.Forward(
				"a prime p = a² + b² is 2, or odd and then 1 mod 4",
				func(br *Argument, sum Fact) {
					a, b, sumOfSquares := br.Unpack2As[Nat, Nat](sum, "a", "b")
					notTwo := br.Unless(
						br.TermAs[Bool]("p = 2"),
						"p = 2 is the first alternative",
						Given(func(cr *Argument, isTwo Fact) {
							cr.Show(
								"p = 2",
								By(isTwo))
						}))
					odd := br.Have(
						"an even prime is 2, so p is odd",
						"¬nat_even(p)",
						By(
							prime,
							notTwo,
							nat_parity.EvenIffDouble.At(p),
							nat_divides.DividesFactor.At(two, p),
							nat_prime.PrimeDividesPrime.At(two, p),
							nat_prime.PrimeTwo))
					aSquare, bSquare := br.TermAs[Nat]("a * a"), br.TermAs[Nat]("b * b")
					opposite := br.Have(
						"an odd sum of two squares has one odd square: a and b have opposite parities",
						"¬(nat_even(a) ⇔ nat_even(b))",
						By(
							Normalized,
							odd,
							sumOfSquares,
							nat_parity.EvenAdd.At(aSquare, bSquare),
							nat_parity.EvenMul.At(a, a),
							nat_parity.EvenMul.At(b, b)))
					residues := br.Have(
						"the even square leaves 0 mod 4 and the odd one 1, "+
							"so the residues add up to 0 + 1 or 1 + 0, which is 1",
						"rem(a * a, 4) + rem(b * b, 4) = 1",
						By(
							opposite,
							nat_parity.SquareModFour.At(a),
							nat_parity.SquareModFour.At(b),
							nat_parity.OddIffNotEven.At(a),
							nat_parity.OddIffNotEven.At(b),
							nat_arith.AddZero,
							nat_arith.Add))
					br.Show(
						"rem(p, 4) = rem(rem(a², 4) + rem(b², 4), 4) = rem(1, 4) = 1",
						ByArith(
							sumOfSquares,
							residues,
							nat_div_mod.ModAddMod.At(aSquare, bSquare, four),
							nat_div_mod.ModLessThan.At(one, four)))
				})
			arg.Backward(
				"2 = 1² + 1², and a prime that is 1 mod 4 divides some m² + 1",
				func(br *Argument, form Fact) {
					br.Show(
						"by the two forms of p",
						form.SplitDisj(
							LeftHolds(
								"p = 2 = 1² + 1²",
								Given(func(cr *Argument, isTwo Fact) {
									cr.Take(one)
									cr.Take(one)
									cr.Show(
										"1 + 1 = 2",
										By(isTwo))
								})),
							RightHolds(
								"rem(p, 4) = 1: p divides some m² + 1, and a prime that does is a sum of two squares",
								Given(func(cr *Argument, oneModFour Fact) {
									cr.Show(
										"a prime dividing some m² + 1 is a sum of two squares",
										By(
											prime,
											oneModFour,
											units_mod.MinusOneSquareExists.At(p),
											gaussian_integer.PrimeDividingSquarePlusOne))
								}))))
				})
		}),
})}
