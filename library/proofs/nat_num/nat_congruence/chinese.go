// chinese.go — the Chinese remainder theorem: congruences modulo two
// coprime numbers are one congruence modulo their product, and any pair
// of residues is attained.
//
// A file of its own: the theorem the chapter's other laws serve.

package nat_congruence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Two coprime moduli
// ---------------------------------------------------------------------------
//
// Two statements make the theorem. Uniqueness: modulo coprime a and b a
// congruence is exactly a congruence modulo a·b, so two solutions of the
// same pair of congruences agree modulo a·b. Existence: every pair of
// residues is attained. The existence proof writes down no solution. It
// counts: the numbers u, u + a, u + 2a, … below u + a·b are already
// congruent to u modulo a, and the b of them leave b different
// remainders modulo b — so between them every remainder below b, v's
// among them.

// Chinese — modulo coprime a and b, congruence modulo a·b is congruence
// modulo both. The distance between x and y is divisible by a·b exactly
// when it is divisible by each: a·b's divisors a and b divide whatever it
// divides, and two coprime divisors divide together.
var Chinese = chineseThm{family.Add(registry.ProofEntry{
	Name: "Chinese",
	Key:  "prop_e38b5823cc581675",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b x y:num.",
			Hypotheses: []string{
				"nat_coprime(a, b)",
			},
			Conclusion: "x ≡ y (mod a * b) ⇔ x ≡ y (mod a) ∧ x ≡ y (mod b)",
		},
		func(arg *Argument, a, b, x, y *Expr[Nat], coprime Fact) {
			distance := arg.TermAs[Nat]("dist((x, y))")
			product := arg.TermAs[Nat]("a * b")
			// each congruence read as a divisibility of the distance between x and y
			onProduct := DistIffDivides.At(x, y, product)
			onA, onB := DistIffDivides.At(x, y, a), DistIffDivides.At(x, y, b)
			arg.Iff()
			arg.Forward(
				"a divisor of a·b divides what a·b divides",
				func(c *Argument, both Fact) {
					aDivides := c.Have(
						"a divides a·b",
						"a ∣ a * b",
						By(nat_divides.DividesOwnMultiple.At(a, b)))
					bDivides := c.Have(
						"and so does b",
						"b ∣ a * b",
						By(nat_divides.DividesOwnMultiple.At(b, a)))
					c.Show(
						"so a and b each divide the distance",
						By(
							both,
							onProduct,
							onA,
							onB,
							aDivides,
							bDivides,
							nat_divides.DividesTrans.At(a, product, distance),
							nat_divides.DividesTrans.At(b, product, distance)))
				})
			arg.Backward(
				"two coprime divisors of the distance divide it together",
				func(c *Argument, each Fact) {
					c.Show(
						"so a·b divides it",
						By(each, onProduct, onA, onB, coprime, nat_gcd.CoprimeProductDivides.At(a, b, distance)))
				})
		}),
})}

// ChineseRemainder — modulo coprime a and b any pair of residues is
// attained. When b is 0, a is 1 and v itself is a solution. Otherwise
// the numbers u + a·i for i below b are all congruent to u modulo a, and
// no two of them share a remainder modulo b: two that did would differ
// by a multiple of b, and cancelling u and then a — coprime to b —
// leaves two numbers below b with one remainder, which are equal. So
// their b remainders are all b remainders below b, and one of them is
// v's.
var ChineseRemainder = chineseRemainderThm{family.Add(registry.ProofEntry{
	Name: "ChineseRemainder",
	Key:  "prop_e4911c2565d5dbef",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b u v:num.",
			Hypotheses: []string{
				"nat_coprime(a, b)",
			},
			Conclusion: "∃x:num. x ≡ u (mod a) ∧ x ≡ v (mod b)",
		},
		func(arg *Argument, a, b, u, v *Expr[Nat], coprime Fact) {
			arg.Cases(arg.Term("b = 0"))
			arg.When(
				"modulo 0 the second congruence pins x to v, and a, coprime to 0, is 1",
				func(c *Argument, isZero Fact) {
					one := c.Have(
						"a divides a and 0, and a common divisor of a and 0 is 1",
						"a = 1",
						By(
							Normalized,
							coprime,
							isZero,
							nat_divides.DividesZero.At(a),
							nat_gcd.Coprime.At(a, b),
							nat_divides.DividesRefl.At(a)))
					c.Do(one.Rw(), isZero.Rw())
					c.Take(v)
					c.Show(
						"everything leaves remainder 0 modulo 1, and v leaves v's",
						Derive(func(d *Argument) {
							// ↦ nat_mod(v₀, 1) = nat_mod(u₀, 1): the congruence modulo 0
							// is v's with itself, and drops out
							d.Do(Unfold(CongDef))
							d.Show(
								"both remainders are 0",
								By(Normalized, nat_div_mod.ModOne.At(u), nat_div_mod.ModOne.At(v)))
						}))
				})
			arg.Otherwise(
				"a nonzero b leaves remainders below b",
				func(c *Argument, nonzero Fact) {
					remainderAt := c.TermAs[Fun[Nat, Nat]]("λi:num. rem(u + a * i, b)")
					into := c.Have(
						"each of them lies below b",
						"∀i:num. i < b ⇒ rem(u + a * i, b) < b",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("i")
							d.Assume()
							d.Show(
								"a remainder lies below the divisor",
								By(nonzero, nat_div_mod.Division.At(d.TermAs[Nat]("u + a * i"), b)))
						}))
					apart := c.Have(
						"and no two of the first b coincide",
						"∀i j:num. i < b ∧ j < b ∧ rem(u + a * i, b) = rem(u + a * j, b) ⇒ i = j",
						Derive(func(d *Argument) {
							i, j := d.FixAs[Nat]("i"), d.FixAs[Nat]("j")
							given := d.Assume()
							congruence := d.Ctx().ConstDefNormalized("nat_cong") // a congruence is equality of remainders
							same := d.Have(
								"one remainder is one class",
								"u + a * i ≡ u + a * j (mod b)",
								By(given, congruence))
							scaled := d.Have(
								"u cancels",
								"a * i ≡ a * j (mod b)",
								By(same, AddCancel.At(u, d.TermAs[Nat]("a * i"), d.TermAs[Nat]("a * j"), b)))
							plain := d.Have(
								"and so does a, being coprime to b",
								"i ≡ j (mod b)",
								By(scaled, coprime, MulCancel.At(a, i, j, b)))
							d.Show(
								"two numbers below b with one remainder are equal",
								By(given, plain, congruence, nat_div_mod.ModInjectiveBelow.At(i, j, b)))
						}))
					target := c.TermAs[Nat]("rem(v, b)")
					reachable := c.Have(
						"v's remainder lies below b too",
						"rem(v, b) < b",
						By(nonzero, nat_div_mod.Division.At(v, b)))
					i, lands := c.ObtainAs[Nat](
						"so one of them is v's remainder",
						"∃i:num. i < b ∧ rem(u + a * i, b) = rem(v, b)",
						By(into, apart, reachable, num_segment.BelowStrictInjectiveOnto.At(b, remainderAt, target)))
					solution := c.TermAs[Nat]("u + a * i")
					c.Take(solution)
					c.Do(SplitConjAll(
						Case(
							"u + a·i is u moved by a multiple of a",
							Derive(func(d *Argument) {
								d.Show(
									"a divides a·i, and a·i is the distance from u",
									By(
										nat_divides.DividesOwnMultiple.At(a, i),
										DistIffDivides.At(solution, u, a),
										nat_monus.DistLeftAdd.At(u, d.TermAs[Nat]("a * i"))))
							})),
						Case(
							"and it leaves v's remainder modulo b, which is how it was chosen",
							Derive(func(d *Argument) {
								d.Show(
									"the congruence is the remainder equation i was chosen by",
									By(lands, d.Ctx().ConstDefNormalized("nat_cong")))
							})),
					))
				})
		}),
})}
