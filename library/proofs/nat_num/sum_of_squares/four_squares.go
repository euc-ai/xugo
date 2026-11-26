// four_squares.go — Lagrange's four-square theorem and the steps of its proof.

package sum_of_squares

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Euler's identity: sums of four squares are closed under products
// ---------------------------------------------------------------------------
//
// The identity is a polynomial identity over ℤ, where its cross terms can
// be negative. Each of its four squares is the square of a natural number,
// so a natural number that is a sum of four integer squares is a sum of
// four natural squares, and the product of two sums of four squares in ℕ is
// one again.

// FourSquareIdentity — Euler's four-square identity: the product of two
// sums of four squares is the sum of the four squares z₁, …, z₄ of the
// bilinear forms below. Both sides multiply out to the same polynomial.
var FourSquareIdentity = fourSquareIdentityThm{family.Add(registry.ProofEntry{
	Name: "FourSquareIdentity",
	Key:  "prop_c4c7d943d2ae9d59",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b c d e f g h:int.",
			Conclusion: "(a * a + b * b + c * c + d * d) * (e * e + f * f + g * g + h * h) = " +
				"«z₁» * «z₁» + «z₂» * «z₂» + «z₃» * «z₃» + «z₄» * «z₄»",
			Abbrev: Abbrev{
				{Name: "z₁", Text: "a * e + b * f + c * g + d * h"},
				{Name: "z₂", Text: "a * f - b * e + c * h - d * g"},
				{Name: "z₃", Text: "a * g - b * h - c * e + d * f"},
				{Name: "z₄", Text: "a * h + b * g - c * f - d * e"},
			},
		},
		func(arg *Argument) {
			arg.Show(
				"both sides multiply out to one polynomial",
				ByArith())
		}),
})}

// FourIntegerSquaresNatural — a natural number that is a sum of four
// integer squares is a sum of four natural squares: an integer is a natural
// number k or its negative, and its square is k² either way.
var FourIntegerSquaresNatural = fourIntegerSquaresNaturalThm{family.Add(registry.ProofEntry{
	Name: "FourIntegerSquaresNatural",
	Key:  "prop_beaa334b418da952",
	Build: family.Sections(
		Statement{
			Binders: "∀n:num. ∀x y z w:int.",
			Hypotheses: []string{
				"&n = x * x + y * y + z * z + w * w",
			},
			Conclusion: "∃a b c d:num. n = a * a + b * b + c * c + d * d",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			naturalSquare := ctx.Lemma(
				"∀x:int. ∃k:num. x * x = &k * &k",
				func(a *Argument, x *Expr[Int]) {
					a.Show(
						"x is a natural number k or its negative",
						int_embed.Image.At(x).SplitDisj(
							LeftHolds(
								"x = k: x² − k² = (x − k)(x + k) vanishes",
								Given(func(b *Argument, natural Fact) {
									k, isK := b.UnpackAs[Nat](natural, "k")
									b.Take(k)
									b.Show(
										"x = k, scaled by x + k",
										ByArith(Scaled(b.TermAs[Int]("x + &k"), isK)))
								})),
							RightHolds(
								"x = −k: x² − k² = (x + k)(x − k) vanishes",
								Given(func(b *Argument, negative Fact) {
									k, isMinusK := b.UnpackAs[Nat](negative, "k")
									b.Take(k)
									b.Show(
										"x = −k, scaled by x − k",
										ByArith(Scaled(b.TermAs[Int]("x - &k"), isMinusK)))
								}))))
				})

			return ctx.Theorem(headline,
				func(arg *Argument, n *Expr[Nat], x, y, z, w *Expr[Int], sum Fact) {
					a, aSquare := arg.UnpackAs[Nat](At(naturalSquare, x), "a")
					b, bSquare := arg.UnpackAs[Nat](At(naturalSquare, y), "b")
					c, cSquare := arg.UnpackAs[Nat](At(naturalSquare, z), "c")
					d, dSquare := arg.UnpackAs[Nat](At(naturalSquare, w), "d")
					arg.Take(a)
					arg.Take(b)
					arg.Take(c)
					arg.Take(d)
					inIntegers := arg.Have(
						"in ℤ, n is the sum of the four natural squares",
						"n = int_of_num(a * a + b * b + c * c + d * d)",
						Simp(Fwd(int_embed.OfNumAdd), Fwd(int_embed.OfNumMul)),
						ByArith(sum, aSquare, bSquare, cSquare, dSquare))
					arg.Show(
						"and ℕ embeds in ℤ one-to-one",
						By(inIntegers, int_embed.OfNumEq))
				})
		}),
})}

// SumFourSquaresMul — a product of two sums of four squares is a sum of
// four squares: read in ℤ, the product is Euler's sum of the four squares
// z₁, …, z₄, and a natural number that is a sum of four integer squares is
// one of four natural squares.
var SumFourSquaresMul = sumFourSquaresMulThm{family.Add(registry.ProofEntry{
	Name: "SumFourSquaresMul",
	Key:  "prop_22158bf5e4b1d838",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n a b c d e f g h:num.",
			Hypotheses: []string{
				"m = a * a + b * b + c * c + d * d",
				"n = e * e + f * f + g * g + h * h",
			},
			Conclusion: "∃x y z w:num. m * n = x * x + y * y + z * z + w * w",
			Abbrev: Abbrev{
				{Name: "z₁", Text: "&a * &e + &b * &f + &c * &g + &d * &h"},
				{Name: "z₂", Text: "&a * &f - &b * &e + &c * &h - &d * &g"},
				{Name: "z₃", Text: "&a * &g - &b * &h - &c * &e + &d * &f"},
				{Name: "z₄", Text: "&a * &h + &b * &g - &c * &f - &d * &e"},
			},
		},
		func(arg *Argument, m, n, a, b, c, d, e, f, g, h *Expr[Nat], mSum, nSum Fact) {
			euler := arg.Have(
				"read in ℤ, m·n is Euler's sum of four squares",
				"int_of_num(m * n) = «z₁» * «z₁» + «z₂» * «z₂» + «z₃» * «z₃» + «z₄» * «z₄»",
				mSum.Rw(),
				nSum.Rw(),
				Simp(Fwd(int_embed.OfNumMul), Fwd(int_embed.OfNumAdd)),
				Cite(FourSquareIdentity))
			arg.Show(
				"a natural number that is a sum of four integer squares is a sum of four natural ones",
				By(euler, FourIntegerSquaresNatural))
		}),
})}

// ---------------------------------------------------------------------------
// A prime divides some x² + y² + 1
// ---------------------------------------------------------------------------
//
// For an odd prime p = 2k + 1 the k + 1 squares 0², 1², …, k² leave
// distinct residues mod p, and so do the k + 1 numbers −1 − y²: together
// p + 1 residues among p classes, so one x² meets one −1 − y², and p
// divides x² + y² + 1. The prime 2 divides 1² + 0² + 1.

// PrimeDividesTwoSquaresPlusOne — every prime p divides x² + y² + 1 for
// some x, y with 2x ≤ p and 2y ≤ p. For p = 2 take 1 and 0. An odd prime
// is 2k + 1, and among the residues of x² and of −1 − y² for x, y ≤ k —
// two sets of k + 1 residues each — one is common: p classes cannot hold
// p + 1 distinct residues.
var PrimeDividesTwoSquaresPlusOne = primeDividesTwoSquaresPlusOneThm{family.Add(registry.ProofEntry{
	Name: "PrimeDividesTwoSquaresPlusOne",
	Key:  "prop_ed75024aca91840c",
	Build: family.Sections(
		Statement{
			Binders: "∀p:num.",
			Hypotheses: []string{
				"nat_prime(p)",
			},
			Conclusion: "∃x y:num. 2 * x ≤ p ∧ 2 * y ≤ p ∧ p ∣ x * x + y * y + 1",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			overlap := ctx.Lemma(
				Statement{
					Binders: "∀p k:num.",
					Hypotheses: []string{
						"nat_prime(p)",
						"p = 2 * k + 1",
					},
					Conclusion: "∃x y:num. x ≤ k ∧ y ≤ k ∧ rem(x * x, p) = p - 1 - rem(y * y, p)",
				},
				func(a *Argument, p, k *Expr[Nat], prime, odd Fact) {
					half := a.TermAs[Set[Nat]]("{x:num | x ≤ k}")
					square := a.TermAs[Fun[Nat, Nat]]("λx:num. rem(x * x, p)")
					complement := a.TermAs[Fun[Nat, Nat]]("λy:num. p - 1 - rem(y * y, p)")
					residues := a.TermAs[Set[Nat]]("{i:num | i < p}")
					size := a.TermAs[Nat]("k + 1")

					distinct := a.Have(
						"the squares of 0, …, k leave distinct residues mod p",
						"∀x y:num. x ≤ k ∧ y ≤ k ∧ rem(x * x, p) = rem(y * y, p) ⇒ x = y",
						Derive(func(b *Argument) {
							x, y := b.FixAs[Nat]("x"), b.FixAs[Nat]("y")
							same := b.Assume()
							small := b.Have(
								"both lie below p/2",
								"2 * x < p ∧ 2 * y < p",
								ByArith(odd, same))
							b.Show(
								"SquaresDistinctModPrime, the congruence read as equal residues",
								By(
									prime,
									small,
									same,
									nat_prime.SquaresDistinctModPrime.At(p, x, y),
									nat_congruence.CongDef.At(b.TermAs[Nat]("x * x"), b.TermAs[Nat]("y * y"), p)))
						}))
					squaresInjective := a.Have(
						"x ↦ rem(x², p) is one-to-one on 0, …, k",
						"injective_on({x:num | x ≤ k}, λx:num. rem(x * x, p))",
						Unfold(functions.InjectiveOnDef),
						By(distinct))
					complementsInjective := a.Have(
						"so is y ↦ p − 1 − rem(y², p), the residues lying below p",
						"injective_on({x:num | x ≤ k}, λy:num. p - 1 - rem(y * y, p))",
						Unfold(functions.InjectiveOnDef),
						Derive(func(b *Argument) {
							x, y := b.FixAs[Nat]("x"), b.FixAs[Nat]("y")
							same := b.Assume()
							equalResidues := b.Have(
								"the residues agree, both lying below p",
								"rem(x * x, p) = rem(y * y, p)",
								ByArith(
									odd,
									same,
									nat_div_mod.Division.At(b.TermAs[Nat]("x * x"), p),
									nat_div_mod.Division.At(b.TermAs[Nat]("y * y"), p)))
							b.Show(
								"and the squares are distinct",
								By(same, equalResidues, distinct.At(x, y)))
						}))

					squares, squaresDef := a.LetAs[Set[Nat]]("A", "image(λx:num. rem(x * x, p), {x:num | x ≤ k})")
					complements, complementsDef := a.LetAs[Set[Nat]](
						"B", "image(λy:num. p - 1 - rem(y * y, p), {x:num | x ≤ k})")
					sizeA := a.Have(
						"A has k + 1 elements",
						"has_size(A, k + 1)",
						By(
							squaresDef,
							squaresInjective,
							cardinality.HasSizeImageInj.At(square, half, size),
							num_segment.HasSizeBelow.At(k)))
					sizeB := a.Have(
						"B has k + 1 elements",
						"has_size(B, k + 1)",
						By(
							complementsDef,
							complementsInjective,
							cardinality.HasSizeImageInj.At(complement, half, size),
							num_segment.HasSizeBelow.At(k)))
					belowP := a.Have(
						"every square residue and every complement of one lies below p",
						"∀x:num. rem(x * x, p) < p ∧ p - 1 - rem(x * x, p) < p",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("x")
							b.Show(
								"a residue mod p is below p",
								ByArith(odd, nat_div_mod.Division.At(b.TermAs[Nat]("x * x"), p)))
						}))
					inResidues := a.Have(
						"A and B consist of residues mod p",
						"A ∪ B ⊆ {i:num | i < p}",
						BySets(squaresDef, complementsDef, belowP))
					union := a.TermAs[Set[Nat]]("A ∪ B")
					atMostP := a.Have(
						"so their union has at most p elements",
						"card(A ∪ B) ≤ p",
						By(
							inResidues,
							cardinality.CardSubset.At(union, residues),
							num_segment.FiniteBelowStrict.At(p),
							cardinality.CardOfSized.At(residues, p),
							num_segment.HasSizeBelowStrict.At(p)))
					meet := a.Have(
						"(k + 1) + (k + 1) = p + 1 exceeds p, so A and B meet",
						"¬(A ∩ B = ∅)",
						ByArith(
							atMostP,
							sizeA,
							sizeB,
							odd,
							cardinality.OverlapOfShortUnion.At(squares, complements),
							cardinality.HasSizeDef.At(squares, size),
							cardinality.HasSizeDef.At(complements, size)))
					a.Show(
						"a common element is a square residue and the complement of another",
						BySets(squaresDef, complementsDef, meet))
				})

			return ctx.Theorem(headline,
				func(a *Argument, p *Expr[Nat], prime Fact) {
					zero, one, two := a.Ctx().Nat(0), a.Ctx().Nat(1), a.Ctx().Nat(2)
					oddPrime := a.Unless(
						a.TermAs[Bool]("p = 2"),
						"p = 2 divides 1² + 0² + 1",
						Given(func(b *Argument, isTwo Fact) {
							b.Take(one)
							b.Take(zero)
							b.Show(
								"1 + 0 + 1 = 2",
								ByArith(isTwo, nat_divides.DividesRefl.At(two)))
						}))
					notEven := a.Have(
						"an even prime would be 2",
						"¬nat_even(p)",
						By(
							prime,
							oddPrime,
							nat_parity.EvenIffDouble.At(p),
							nat_divides.DividesFactor.At(two, p),
							nat_prime.PrimeDividesPrime.At(two, p),
							nat_prime.PrimeTwo))
					k, odd := a.ObtainAs[Nat](
						"so p = 2k + 1",
						"∃k:num. p = 2 * k + 1",
						By(notEven, nat_parity.OddIffSucDouble.At(p), nat_parity.OddIffNotEven.At(p), nat_arith.Add1))
					x, y, meet := a.Unpack2As[Nat, Nat](GroupPremises(prime, odd, At(overlap, p, k)), "x", "y")
					parts := a.Conjuncts(
						meet,
						"x lies in 0, …, k",
						"y lies in 0, …, k",
						"the residue of x² is p − 1 minus that of y²")
					xSquare, ySquare := a.TermAs[Nat]("x * x"), a.TermAs[Nat]("y * y")
					quotient := a.Have(
						"the residues of x² and y² add up to p − 1",
						"x * x + y * y + 1 = p * (div(x * x, p) + div(y * y, p) + 1)",
						ByArith(odd, parts[2], nat_div_mod.Division.At(xSquare, p), nat_div_mod.Division.At(ySquare, p)))
					divides := a.Have(
						"so p divides x² + y² + 1",
						"p ∣ x * x + y * y + 1",
						By(quotient, nat_divides.DividesFactor.At(p, a.TermAs[Nat]("x * x + y * y + 1"))))
					a.Take(x)
					a.Take(y)
					a.Show(
						"x, y ≤ k give 2x, 2y < p",
						ByArith(odd, parts[0], parts[1], divides))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The descent: an odd or even multiple of p comes down
// ---------------------------------------------------------------------------
//
// Let m·p = a² + b² + c² + d² with 1 < m. If m is even, the four
// squares pair off by parity and (m/2)·p is a sum of four squares. If m is
// odd and does not divide p, shifting a, b, c, d by multiples m·t₁, …, m·t₄
// into ⟦−(m − 1)/2, (m − 1)/2⟧ gives four squares that add up to m·r with
// 0 < r < m. Euler's identity at (a, b, c, d) and (t₁, …, t₄), its first
// square completed by p, writes r·p as (p + z₁)² + z₂² + z₃² + z₄².

// HalfOfFourSquares — when 2n is a sum of four squares, so is n: an even
// sum of four squares pairs its terms by parity, and two numbers x, y of
// one parity give x² + y² = 2(u² + v²) with u = (x + y)/2, v = |x − y|/2.
var HalfOfFourSquares = halfOfFourSquaresThm{family.Add(registry.ProofEntry{
	Name: "HalfOfFourSquares",
	Key:  "prop_7b9e20a7d1bf7232",
	Build: family.Sections(
		Statement{
			Binders: "∀n a b c d:num.",
			Hypotheses: []string{
				"a * a + b * b + c * c + d * d = 2 * n",
			},
			Conclusion: "∃e f g h:num. n = e * e + f * f + g * g + h * h",
			Abbrev: Abbrev{
				{Name: "paired", Text: "λw:num. λx:num. λy:num. λz:num. " +
					"    (nat_even(w) ⇔ nat_even(x)) ∧ (nat_even(y) ⇔ nat_even(z))"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			pairHalves := ctx.Lemma(
				Statement{
					Binders: "∀x y:num.",
					Hypotheses: []string{
						"nat_even(x) ⇔ nat_even(y)",
					},
					Conclusion: "∃u v:num. x * x + y * y = 2 * (u * u + v * v)",
				},
				func(a *Argument, x, y *Expr[Nat], sameParity Fact) {
					u, half := a.ObtainAs[Nat](
						"x + y is even: write it 2u",
						"∃u:num. x + y = 2 * u",
						By(sameParity, nat_parity.EvenAdd.At(x, y), nat_parity.EvenIffDouble.At(a.TermAs[Nat]("x + y"))))
					a.Cases(a.TermAs[Bool]("y ≤ u"))
					a.When(
						"y ≤ u: x = u + v and y = u − v",
						func(b *Argument, below Fact) {
							v, gap := b.ObtainAs[Nat](
								"u exceeds y by some v",
								"∃v:num. u = y + v",
								By(below, nat_order.LessEqExists.At(u, y)))
							xForm := b.Have(
								"then x = u + v",
								"x = u + v",
								ByArith(gap, half))
							b.Take(u)
							b.Take(v)
							b.Show(
								"(u + v)² + (u − v)² = 2(u² + v²)",
								xForm.Rw(),
								gap.Rw(),
								ByArith())
						})
					a.Otherwise(
						"u < y: y = u + v and x = u − v",
						func(b *Argument, above Fact) {
							v, gap := b.ObtainAs[Nat](
								"y exceeds u by some v",
								"∃v:num. y = u + v",
								By(
									above,
									nat_order.LessEqExists.At(y, u),
									nat_order.NotLessEq.At(y, u),
									nat_order.LessEqOfLessThan.At(u, y)))
							uForm := b.Have(
								"then u = x + v",
								"u = x + v",
								ByArith(gap, half))
							b.Take(u)
							b.Take(v)
							b.Show(
								"(u − v)² + (u + v)² = 2(u² + v²)",
								gap.Rw(),
								uForm.Rw(),
								ByArith())
						})
				})

			return ctx.Theorem(headline,
				func(arg *Argument, n, a, b, c, d *Expr[Nat], twice Fact) {
					pairing := arg.Have(
						"an even sum of four squares pairs its terms by parity",
						"«paired»(a, b, c, d) ∨ «paired»(a, c, b, d) ∨ «paired»(a, d, b, c)",
						By(
							Normalized,
							twice,
							nat_parity.EvenDouble.At(n),
							nat_parity.EvenAdd.At(arg.TermAs[Nat]("a * a + b * b + c * c"), arg.TermAs[Nat]("d * d")),
							nat_parity.EvenAdd.At(arg.TermAs[Nat]("a * a + b * b"), arg.TermAs[Nat]("c * c")),
							nat_parity.EvenAdd.At(arg.TermAs[Nat]("a * a"), arg.TermAs[Nat]("b * b")),
							nat_parity.EvenMul.At(a, a),
							nat_parity.EvenMul.At(b, b),
							nat_parity.EvenMul.At(c, c),
							nat_parity.EvenMul.At(d, d)))

					// Two pairs of one parity each halve; their halves are n's four squares.
					halve := func(br *Argument, pairs Fact, w, x, y, z *Expr[Nat]) {
						u1, v1, first := br.Unpack2As[Nat, Nat](GroupPremises(pairs, At(pairHalves, w, x)), "u₁", "v₁")
						u2, v2, second := br.Unpack2As[Nat, Nat](GroupPremises(pairs, At(pairHalves, y, z)), "u₂", "v₂")
						br.Take(u1)
						br.Take(v1)
						br.Take(u2)
						br.Take(v2)
						br.Show(
							"2n = 2(u₁² + v₁²) + 2(u₂² + v₂²)",
							ByArith(twice, first, second))
					}
					arg.Show(
						"each pairing halves",
						pairing.SplitDisj(
							LeftHolds(
								"a pairs with b or with c",
								Given(func(br *Argument, firstTwo Fact) {
									br.Show(
										"either way the two pairs halve",
										firstTwo.SplitDisj(
											LeftHolds(
												"a, b and c, d share parities",
												Given(func(cr *Argument, pairs Fact) { halve(cr, pairs, a, b, c, d) })),
											RightHolds(
												"a, c and b, d share parities",
												Given(func(cr *Argument, pairs Fact) { halve(cr, pairs, a, c, b, d) }))))
								})),
							RightHolds(
								"a, d and b, c share parities",
								Given(func(br *Argument, pairs Fact) { halve(br, pairs, a, d, b, c) }))))
				})
		}),
})}

// EvenMultipleHalves — if m is even and positive and m·p is a sum of four
// squares, so is r·p for some 0 < r < m, namely r = m/2: m·p = 2·(r·p), and
// half of a sum of four squares is one.
var EvenMultipleHalves = evenMultipleHalvesThm{family.Add(registry.ProofEntry{
	Name: "EvenMultipleHalves",
	Key:  "prop_24ee839eca20af45",
	Build: family.Theorem(
		Statement{
			Binders: "∀m p a b c d:num.",
			Hypotheses: []string{
				"nat_even(m)",
				"0 < m",
				"m * p = a * a + b * b + c * c + d * d",
			},
			Conclusion: "∃r e f g h:num. 0 < r ∧ r < m ∧ r * p = e * e + f * f + g * g + h * h",
		},
		func(arg *Argument, m, p, a, b, c, d *Expr[Nat], even, positive, sum Fact) {
			r, half := arg.ObtainAs[Nat](
				"m = 2r",
				"∃r:num. m = 2 * r",
				By(even, nat_parity.EvenIffDouble.At(m)))
			twice := arg.Have(
				"the four squares add up to twice r·p",
				"a * a + b * b + c * c + d * d = 2 * (r * p)",
				ByArith(Scaled(p, half), sum))
			bounds := arg.Have(
				"0 < r < m",
				"0 < r ∧ r < m",
				ByArith(half, positive))
			arg.Take(r)
			arg.Show(
				"r·p is half a sum of four squares",
				By(twice, bounds, HalfOfFourSquares.At(arg.TermAs[Nat]("r * p"), a, b, c, d)))
		}),
})}

// OddMultipleDescends — if m is odd, does not divide p, and m·p is a sum of
// four squares a² + b² + c² + d², then so is r·p for some 0 < r < m.
// Write m = 2k + 1 and shift each of a, b, c, d by a multiple of m into
// ⟦−k, k⟧: y₁ = a + m·t₁, …, y₄ = d + m·t₄. Then y₁² + … + y₄² = m·R for
// R = p + 2·a·t + m·|t|², with a·t = a·t₁ + … + d·t₄ and |t|² = t₁² + … + t₄²,
// and 0 ≤ R < m since the shifted squares add up to at most 4k² < m².
// R = 0 would make every yᵢ vanish and p = m·|t|². Euler's identity at
// (a, b, c, d) and (t₁, …, t₄), its first square completed by p, gives
// p·R = w₁² + w₂² + w₃² + w₄², the wⱼ below. The table is spelled over the
// shifts t₁, …, t₄, which the proof obtains.
var OddMultipleDescends = oddMultipleDescendsThm{family.Add(registry.ProofEntry{
	Name: "OddMultipleDescends",
	Key:  "prop_7d5b9e9df17ec556",
	Build: family.Sections(
		Statement{
			Binders: "∀m p a b c d:num.",
			Hypotheses: []string{
				"nat_odd(m)",
				"¬(m ∣ p)",
				"m * p = a * a + b * b + c * c + d * d",
			},
			Conclusion: "∃r e f g h:num. 0 < r ∧ r < m ∧ r * p = e * e + f * f + g * g + h * h",
			Abbrev: Abbrev{
				{Name: "w₁", Text: "&p + &a * t₁ + &b * t₂ + &c * t₃ + &d * t₄"},
				{Name: "w₂", Text: "&a * t₂ - &b * t₁ + &c * t₄ - &d * t₃"},
				{Name: "w₃", Text: "&a * t₃ - &b * t₄ - &c * t₁ + &d * t₂"},
				{Name: "w₄", Text: "&a * t₄ + &b * t₃ - &c * t₂ - &d * t₁"},
				{Name: "a·t", Text: "&a * t₁ + &b * t₂ + &c * t₃ + &d * t₄"},
				{Name: "|t|²", Text: "t₁ * t₁ + t₂ * t₂ + t₃ * t₃ + t₄ * t₄"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			balanced := ctx.Lemma(
				Statement{
					Binders: "∀m k x:num.",
					Hypotheses: []string{
						"m = 2 * k + 1",
					},
					Conclusion: "∃t:int. -&k ≤ &x + &m * t ∧ &x + &m * t ≤ &k",
				},
				func(a *Argument, m, k, x *Expr[Nat], odd Fact) {
					a.Take(a.TermAs[Int]("-div(&x + &k, &m)"))
					a.Show(
						"t = −q, q = div(x + k, m): x + k = q·m + ρ with 0 "+
							"≤ ρ < |m| = m, so x − q·m = ρ − k lies in ⟦−k, k⟧",
						ByArith(
							odd,
							int_div_rem.DivisionAlgorithm.At(a.TermAs[Int]("&x + &k"), a.TermAs[Int]("m")),
							int_embed.OfNumAbs.At(m)))
				})

			return ctx.Theorem(headline,
				func(arg *Argument, m, p, a, b, c, d *Expr[Nat], odd, notDividing, sum Fact) {
					k, oddForm := arg.ObtainAs[Nat](
						"m = 2k + 1",
						"∃k:num. m = 2 * k + 1",
						By(odd, nat_parity.OddIffSucDouble.At(m), nat_arith.Add1))
					t1, shift1 := arg.UnpackAs[Int](GroupPremises(oddForm, At(balanced, m, k, a)), "t₁")
					t2, shift2 := arg.UnpackAs[Int](GroupPremises(oddForm, At(balanced, m, k, b)), "t₂")
					t3, shift3 := arg.UnpackAs[Int](GroupPremises(oddForm, At(balanced, m, k, c)), "t₃")
					t4, shift4 := arg.UnpackAs[Int](GroupPremises(oddForm, At(balanced, m, k, d)), "t₄")
					_, y1Def := arg.LetAs[Int]("y₁", "&a + &m * t₁")
					_, y2Def := arg.LetAs[Int]("y₂", "&b + &m * t₂")
					_, y3Def := arg.LetAs[Int]("y₃", "&c + &m * t₃")
					_, y4Def := arg.LetAs[Int]("y₄", "&d + &m * t₄")
					R, RDef := arg.LetAs[Int]("R", "&p + &2 * «a·t» + &m * «|t|²»")
					modulus := arg.TermAs[Int]("m")

					reduced := arg.Have(
						"the shifted squares add up to m·R",
						"&m * R = y₁ * y₁ + y₂ * y₂ + y₃ * y₃ + y₄ * y₄",
						y1Def.Rw(),
						y2Def.Rw(),
						y3Def.Rw(),
						y4Def.Rw(),
						ByArith(Scaled(modulus, RDef), sum))
					positive := arg.Have(
						"m is positive",
						"int_of_num(0) < &m",
						ByArith(oddForm))
					squaresBound := arg.Have(
						"each shifted value lies in ⟦−k, k⟧, so its square is at most k²",
						"y₁ * y₁ + y₂ * y₂ + y₃ * y₃ + y₄ * y₄ ≤ &4 * (&k * &k)",
						ByArith(shift1, shift2, shift3, shift4))
					inRange := arg.Have(
						"so 0 ≤ R < m: m·R is a sum of squares, at most 4k² < m²",
						"int_of_num(0) ≤ R ∧ R < &m",
						ByArith(reduced, oddForm, squaresBound, positive))
					nonzero := arg.Have(
						"R ≠ 0, or m would divide p",
						"¬(R = int_of_num(0))",
						Derive(func(e *Argument) {
							zero := e.SupposeNot()
							vanish := e.Have(
								"the squares of the shifted values add up to 0, so each vanishes",
								"y₁ = &0 ∧ y₂ = &0 ∧ y₃ = &0 ∧ y₄ = &0",
								ByArith(reduced, zero))
							shifts := e.Have(
								"that is, a, b, c, d are the multiples −m·t₁, …, −m·t₄",
								"&a + &m * t₁ = &0 ∧ &b + &m * t₂ = &0 ∧ &c + &m * t₃ = &0 ∧ &d + &m * t₄ = &0",
								ByArith(vanish, y1Def, y2Def, y3Def, y4Def))
							multiples := e.Conjuncts(
								shifts,
								"a = −m·t₁",
								"b = −m·t₂",
								"c = −m·t₃",
								"d = −m·t₄")
							factored := e.Have(
								"so p = m·(t₁² + t₂² + t₃² + t₄²)",
								"&p = &m * «|t|²»",
								ByArith(
									zero,
									RDef,
									Scaled(t1, multiples[0]),
									Scaled(t2, multiples[1]),
									Scaled(t3, multiples[2]),
									Scaled(t4, multiples[3])))
							e.Show(
								"which makes m a divisor of p",
								By(
									Normalized,
									notDividing,
									factored,
									int_divides.OfNumDivides.At(m, p),
									int_divides.IntDividesDef.At(modulus, e.TermAs[Int]("p"))))
						}))
					r, rForm := arg.ObtainAs[Nat](
						"R is a natural number r",
						"∃r:num. R = &r",
						By(inRange, int_embed.OfNumExists.At(R)))
					bounds := arg.Have(
						"0 < r < m",
						"0 < r ∧ r < m",
						ByArith(
							nonzero,
							rForm,
							inRange,
							int_embed.OfNumLt.At(arg.Ctx().Nat(0), r),
							int_embed.OfNumLt.At(r, m)))
					inIntegers := arg.Have(
						"m·p, read in ℤ",
						"int_of_num(m) * &p = &a * &a + &b * &b + &c * &c + &d * &d",
						ByArith(sum))
					euler := arg.Have(
						"Euler's identity at (a, b, c, d) and (t₁, …, t₄), a "+
							"square completed: p·R = (p + z₁)² + z₂² + z₃² + z₄²",
						"&p * R = «w₁» * «w₁» + «w₂» * «w₂» + «w₃» * «w₃» + «w₄» * «w₄»",
						ByArith(
							Scaled(arg.TermAs[Int]("p"), RDef),
							Scaled(arg.TermAs[Int]("«|t|²»"), inIntegers),
							FourSquareIdentity.At(
								arg.TermAs[Int]("a"),
								arg.TermAs[Int]("b"),
								arg.TermAs[Int]("c"),
								arg.TermAs[Int]("d"),
								t1,
								t2,
								t3,
								t4)))
					smallerMultiple := arg.Have(
						"so r·p is the sum of the four integer squares w₁², …, w₄²",
						"int_of_num(r * p) = «w₁» * «w₁» + «w₂» * «w₂» + «w₃» * «w₃» + «w₄» * «w₄»",
						Simp(Fwd(int_embed.OfNumMul)),
						ByArith(rForm, euler))
					arg.Take(r)
					arg.Show(
						"r·p is a sum of four integer squares, so of four natural ones",
						By(
							bounds,
							smallerMultiple,
							FourIntegerSquaresNatural.At(
								arg.TermAs[Nat]("r * p"),
								arg.TermAs[Int]("«w₁»"),
								arg.TermAs[Int]("«w₂»"),
								arg.TermAs[Int]("«w₃»"),
								arg.TermAs[Int]("«w₄»"))))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Every prime, and then every number
// ---------------------------------------------------------------------------

// PrimeFourSquares — every prime is a sum of four squares. Some multiple
// n·p = x² + y² + 1² + 0² with 0 < n < p; take the least positive m with
// m·p a sum of four squares. If m = 1 we are done. Otherwise 1 < m < p, so m
// does not divide p, and an even m halves and an odd m descends to a smaller
// such multiple — against the choice of m.
var PrimeFourSquares = primeFourSquaresThm{family.Add(registry.ProofEntry{
	Name: "PrimeFourSquares",
	Key:  "prop_8a4d1e66d13cef65",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:num.",
			Hypotheses: []string{
				"nat_prime(p)",
			},
			Conclusion: "∃a b c d:num. p = a * a + b * b + c * c + d * d",
			Abbrev: Abbrev{
				{Name: "multiple", Text: "λj:num. 0 < j ∧ ∃a b c d:num. j * p = a * a + b * b + c * c + d * d"},
			},
		},
		func(arg *Argument, p *Expr[Nat], prime Fact) {
			zero, one, two := arg.Ctx().Nat(0), arg.Ctx().Nat(1), arg.Ctx().Nat(2)
			x, y, near := arg.Unpack2As[Nat, Nat](
				GroupPremises(prime, PrimeDividesTwoSquaresPlusOne.At(p)), "x", "y")
			parts := arg.Conjuncts(
				near,
				"2x ≤ p",
				"2y ≤ p",
				"p divides x² + y² + 1")
			doubleX, doubleY := arg.TermAs[Nat]("2 * x"), arg.TermAs[Nat]("2 * y")
			n, first := arg.ObtainAs[Nat](
				"x² + y² + 1 is a multiple n of p",
				"∃n:num. x * x + y * y + 1 = p * n",
				By(parts[2], nat_divides.DividesFactor.At(p, arg.TermAs[Nat]("x * x + y * y + 1"))))
			firstBounds := arg.Have(
				"0 < n < p: x² + y² + 1 ≤ p²/2 + 1 < p²",
				"0 < n ∧ n < p",
				ByArith(
					prime,
					parts[0],
					parts[1],
					first,
					nat_prime.PrimeAtLeastTwo.At(p),
					nat_order.LessEqMul2.At(doubleX, p, doubleX, p),
					nat_order.LessEqMul2.At(doubleY, p, doubleY, p),
					nat_order.LessEqMul2.At(two, p, two, p),
					nat_order.LessThanMulCancel.At(p, n, p),
					nat_arith.MulEqZero.At(p, n)))
			firstSquares := arg.Have(
				"n·p = x² + y² + 1² + 0²",
				"∃a b c d:num. n * p = a * a + b * b + c * c + d * d",
				Derive(func(b *Argument) {
					b.Take(x)
					b.Take(y)
					b.Take(one)
					b.Take(zero)
					b.Show(
						"the multiple as it stands",
						ByArith(first))
				}))
			m, least := arg.ObtainAs[Nat](
				"take the least positive m with m·p a sum of four squares",
				"∃m:num. «multiple»(m) ∧ ∀k:num. k < m ⇒ ¬«multiple»(k)",
				By(firstSquares, firstBounds, nat_order.WellOrdering.At(arg.TermAs[Fun[Nat, Bool]]("«multiple»"))))
			mParts := arg.Conjuncts(
				least,
				"m is positive",
				"m·p is a sum of four squares",
				"no smaller positive multiple of p is")
			notAbove := arg.Have(
				"n is no smaller than m",
				"¬(n < m)",
				By(mParts[2].At(n), firstSquares, firstBounds))
			belowP := arg.Have(
				"so m ≤ n < p",
				"m < p",
				ByArith(notAbove, firstBounds))
			notOne := arg.Unless(
				arg.TermAs[Bool]("m = 1"),
				"m = 1: p itself is the sum of four squares",
				Given(func(b *Argument, isOne Fact) {
					b.Show(
						"1·p = p",
						By(mParts[1], isOne, nat_arith.OneMul.At(p)))
				}))
			notDividing := arg.Have(
				"1 < m < p, so m does not divide the prime p",
				"¬(m ∣ p)",
				By(prime, notOne, belowP, nat_prime.PrimeDef.At(p), nat_order.LessThanIrrefl.At(p)))
			arg.Cases(arg.TermAs[Bool]("nat_even(m)"))
			arg.When(
				"m even: half of m is a smaller such multiple",
				func(b *Argument, even Fact) {
					b.Show(
						"against the choice of m",
						By(even, mParts[0], mParts[1], mParts[2], At(EvenMultipleHalves, m, p)))
				})
			arg.Otherwise(
				"m odd: the descent gives a smaller such multiple",
				func(b *Argument, notEven Fact) {
					b.Show(
						"against the choice of m",
						By(
							notEven,
							notDividing,
							mParts[1],
							mParts[2],
							At(OddMultipleDescends, m, p),
							nat_parity.OddIffNotEven.At(m)))
				})
		}),
})}

// LagrangeFourSquares — every natural number is a sum of four squares. By
// strong induction: 0 and 1 are their own squares, and a larger n is p·q
// for a prime p, with q < n; p is a sum of four squares, q is by
// induction, and so is their product.
var LagrangeFourSquares = lagrangeFourSquaresThm{family.Add(registry.ProofEntry{
	Name: "LagrangeFourSquares",
	Key:  "prop_1fe85aff97c10805",
	Build: family.Theorem(
		"∀n:num. ∃a b c d:num. n = a * a + b * b + c * c + d * d",
		func(arg *Argument) {
			arg.Show(
				"strong induction on n",
				ByInduction(nat_order.StrongInduction,
					Case(
						"granted for every m < n, so for n",
						Derive(func(step *Argument) {
							zero, two := step.Ctx().Nat(0), step.Ctx().Nat(2)
							n := step.FixAs[Nat]()
							smaller := step.Assume()
							large := step.Assuming(
								step.TermAs[Bool]("1 < n"),
								"n ≤ 1: n = n² + 0² + 0² + 0²",
								Given(func(b *Argument, small Fact) {
									b.Take(n)
									b.Take(zero)
									b.Take(zero)
									b.Take(zero)
									b.Show(
										"n is 0 or 1, its own square",
										ByArith(small))
								}))
							p, factor := step.ObtainAs[Nat](
								"a prime p divides n",
								"∃p:num. nat_prime(p) ∧ p ∣ n",
								By(large, nat_prime.PrimeFactor.At(n)))
							parts := step.Conjuncts(
								factor,
								"p is prime",
								"p divides n")
							q, cofactor := step.ObtainAs[Nat](
								"n = p·q",
								"∃q:num. n = p * q",
								By(parts[1], nat_divides.DividesFactor.At(p, n)))
							below := step.Have(
								"q < n, as p ≥ 2",
								"q < n",
								ByArith(
									parts[0],
									large,
									cofactor,
									nat_prime.PrimeAtLeastTwo.At(p),
									nat_order.LessEqMul2.At(two, p, q, q)))
							step.Show(
								"p and q are sums of four squares, and so is their product",
								By(parts[0], smaller.At(q), below, cofactor, PrimeFourSquares.At(p), At(SumFourSquaresMul, p, q)))
						}))))
		}),
})}
