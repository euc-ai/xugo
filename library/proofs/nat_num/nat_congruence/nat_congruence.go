// nat_congruence.go — the chapter: congruence, defined in ℕ.
//
// Five parts, marked by banners:
//
// - Reducing one argument of a congruence
// - A number is congruent to its own residue
// - Congruence respects the arithmetic
// - Congruence and divisibility
// - An inverse modulo n

package nat_congruence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Reducing one argument of a congruence
// ---------------------------------------------------------------------------
//
// Replacing either side by its remainder leaves the congruence
// unchanged. Stated over `nat_cong` both members are arithmetic rather
// than transport: the definition turns each into an equation between
// remainders, and what the reduced side asks for is that taking a
// remainder twice by the same modulus is taking it once —
// nat_div_mod.ModModRefl. So each proof is the unfold followed by that one
// equation, and the two are mirrors of one another.
//
// The cites are bare because ModModRefl arrives as a goal REWRITE
// rather than as a premise: rewriting the doubled reduction away makes
// the two sides of the ⇔ one equation, so the cite closes the section
// and has no leaf left to take witnesses for.

// ---------------------------------------------------------------------------
// ModLeft — reducing the left argument
// ---------------------------------------------------------------------------

// ModLeft — reducing x by the modulus before comparing changes nothing,
// because the comparison was already a comparison of remainders. Open
// the definition and the two sides of the ⇔ differ by one redundant
// reduction, which is all ModModRefl has to remove.
var ModLeft = modLeftThm{family.Add(registry.ProofEntry{
	Name: "ModLeft",
	Key:  "prop_c17b1eca79b2eb63",
	Build: family.Theorem(
		"∀x y n:num. x ≡ y (mod n) ⇔ rem(x, n) ≡ y (mod n)",
		func(a *Argument, x, y, n Term) {
			a.Do(
				// ↦ nat_mod(x₀, n₀) = nat_mod(y₀, n₀) ⇔ nat_mod(nat_mod(x₀, n₀), n₀) = nat_mod(y₀, n₀)
				Unfold(CongDef),
				// the doubled reduction on the left is nat_mod(x₀, n₀) — the two
				// sides become one equation, and the section closes
				Cite(nat_div_mod.ModModRefl),
			)
		}),
})}

// ---------------------------------------------------------------------------
// ModRight — reducing the right argument
// ---------------------------------------------------------------------------

// ModRight — ModLeft with the sides exchanged, and the same one
// equation: the redundant reduction is now on y.
var ModRight = modRightThm{family.Add(registry.ProofEntry{
	Name: "ModRight",
	Key:  "prop_1f30d771824d2ba8",
	Build: family.Theorem(
		"∀x y n:num. x ≡ y (mod n) ⇔ x ≡ rem(y, n) (mod n)",
		func(a *Argument, x, y, n Term) {
			a.Do(
				// ↦ nat_mod(x₀, n₀) = nat_mod(y₀, n₀) ⇔ nat_mod(x₀, n₀) = nat_mod(nat_mod(y₀, n₀), n₀)
				Unfold(CongDef),
				// the doubled reduction on the right is nat_mod(y₀, n₀) — the two
				// sides become one equation, and the section closes
				Cite(nat_div_mod.ModModRefl),
			)
		}),
})}

// ---------------------------------------------------------------------------
// A number is congruent to its own residue
// ---------------------------------------------------------------------------

// ResidueCongruent — reducing x by the modulus leaves a number congruent
// to x. The joint where a law that answers with a remainder meets a
// claim stated as a congruence: whenever a headline reads a value back
// as its residue and the claim wants the congruence instead, this is
// the step between them. Unfolded it is ModLeft's equation at y := x —
// the doubled reduction against the single one — and ModModRefl closes
// it.
//
// The words chapters are the consumers.
var ResidueCongruent = residueCongruentThm{family.Add(registry.ProofEntry{
	Name: "ResidueCongruent",
	Key:  "prop_bca64087a9529247",
	Build: family.Theorem(
		"∀x n:num. rem(x, n) ≡ x (mod n)",
		func(a *Argument, x, n Term) {
			a.Do(
				// ↦ nat_mod(nat_mod(x₀, n₀), n₀) = nat_mod(x₀, n₀)
				Unfold(CongDef),
				// the doubled reduction on the left is nat_mod(x₀, n₀) — the two
				// sides become one equation, and the section closes
				Cite(nat_div_mod.ModModRefl),
			)
		}),
})}

// ---------------------------------------------------------------------------
// Congruence respects the arithmetic
// ---------------------------------------------------------------------------
//
// Congruence mod n is an equivalence, and one that addition and
// multiplication respect: replacing a summand or a factor by a congruent
// one leaves the result's class unchanged. Over ℕ each of these is a
// statement about remainders. The equivalence is equality's own three
// properties; for the two operations, a sum's or a product's remainder
// depends only on the remainders of its parts, so each proof is the
// unfold and the residue law that says so.

// CongruenceEquivalence — congruence mod n is an equivalence relation.
// Unfolded, each of the three properties is a statement about equality
// of remainders, and equality has all three.
var CongruenceEquivalence = congruenceEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "CongruenceEquivalence",
	Key:  "prop_41824749b738ec9c",
	Build: family.Theorem("∀n:num. equivalence(λx:num. λy:num. x ≡ y (mod n))",
		func(a *Argument, n *Expr[Nat]) {
			a.Do(
				// ↦ reflexivity drops out as an identity; symmetry and
				// transitivity of equality between remainders are left
				Unfold(equivalence.Equivalence), Unfold(
					equivalence.ReflexiveDef), Unfold(equivalence.SymmetricDef), Unfold(equivalence.TransitiveDef),
				Unfold(CongDef),
				SplitConjAll(
					Case(
						"symmetric: equal remainders read backwards",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("x")
							b.FixAs[Nat]("y")
							same := b.Assume()
							b.Show(
								"an equation read backwards",
								By(same))
						})),
					Case(
						"transitive: equal remainders chain",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("x")
							b.FixAs[Nat]("y")
							b.FixAs[Nat]("z")
							both := b.Assume()
							b.Show(
								"two equations through a common remainder",
								By(both))
						})),
				))
		}),
})}

// AddCongruent — congruences add. A sum's remainder is the remainder of
// the sum of its summands' remainders (nat_div_mod.ModAddMod), so summands
// with equal remainders give sums with equal remainders.
var AddCongruent = addCongruentThm{family.Add(registry.ProofEntry{
	Name: "AddCongruent",
	Key:  "prop_b4cecd59fb71aac7",
	Build: family.Theorem(Statement{
		Binders: "∀x y u v n:num.",
		Hypotheses: []string{
			"x ≡ y (mod n)",
			"u ≡ v (mod n)",
		},
		Conclusion: "x + u ≡ y + v (mod n)",
	},
		func(a *Argument) {
			a.Do(Unfold(CongDef))
			x, y := a.FixAs[Nat]("x"), a.FixAs[Nat]("y")
			u, v := a.FixAs[Nat]("u"), a.FixAs[Nat]("v")
			n := a.FixAs[Nat]("n")
			congruent := a.Conjuncts(
				a.Assume(),
				"x and y leave one remainder mod n",
				"u and v leave one remainder mod n")
			first, second := congruent[0], congruent[1]
			a.Show(
				"each sum's remainder is read off its summands' remainders, and those agree",
				By(first, second, nat_div_mod.ModAddMod.At(x, u, n), nat_div_mod.ModAddMod.At(y, v, n)))
		}),
})}

// MulCongruent — congruences multiply, for the same reason: a product's
// remainder is read off its factors' remainders (nat_div_mod.ModMulMod).
var MulCongruent = mulCongruentThm{family.Add(registry.ProofEntry{
	Name: "MulCongruent",
	Key:  "prop_a8587e8fe011ee49",
	Build: family.Theorem(Statement{
		Binders: "∀x y u v n:num.",
		Hypotheses: []string{
			"x ≡ y (mod n)",
			"u ≡ v (mod n)",
		},
		Conclusion: "x * u ≡ y * v (mod n)",
	},
		func(a *Argument) {
			a.Do(Unfold(CongDef))
			x, y := a.FixAs[Nat]("x"), a.FixAs[Nat]("y")
			u, v := a.FixAs[Nat]("u"), a.FixAs[Nat]("v")
			n := a.FixAs[Nat]("n")
			congruent := a.Conjuncts(
				a.Assume(),
				"x and y leave one remainder mod n",
				"u and v leave one remainder mod n")
			first, second := congruent[0], congruent[1]
			a.Show(
				"each product's remainder is read off its factors' remainders, and those agree",
				By(first, second, nat_div_mod.ModMulMod.At(x, u, n), nat_div_mod.ModMulMod.At(y, v, n)))
		}),
})}

// PowCongruent — powers of congruent numbers are congruent. By induction
// on the exponent: x⁰ and y⁰ are both 1, and x^(k+1) = x · x^k is
// congruent to y · y^k = y^(k+1), since congruences multiply.
var PowCongruent = powCongruentThm{family.Add(registry.ProofEntry{
	Name: "PowCongruent",
	Key:  "prop_21fc31de3b8174d2",
	Build: family.Theorem(Statement{
		Binders: "∀x y n k:num.",
		Hypotheses: []string{
			"x ≡ y (mod n)",
		},
		Conclusion: "x ^ k ≡ y ^ k (mod n)",
	}, func(a *Argument, x, y, n *Expr[Nat], congruent Fact) {
		a.Induct("k")
		a.Base(
			"x⁰ and y⁰ are both 1",
			By(nat_arith.NatPow, CongDef))
		a.Step(
			"one more factor on each side, x and y, which are congruent",
			func(b *Argument, ih Fact) {
				b.Show(
					"x · x^k ≡ y · y^k, from x ≡ y and x^k ≡ y^k",
					Simp(Fwd(nat_arith.NatPow)),
					By(congruent, ih, MulCongruent))
			})
	}),
})}

// ---------------------------------------------------------------------------
// Congruence and divisibility
// ---------------------------------------------------------------------------
//
// Over ℤ a congruence is divisibility of a difference. ℕ has no
// difference to speak of, so the bridge is stated where ℕ can state it:
// x and x + d are congruent exactly when the modulus divides d. Read
// with the distance between two numbers — ℕ's own |x - y|, nat_monus's
// `dist` — it is symmetric: two numbers are congruent exactly when the
// modulus divides the distance between them, and every law after it is
// a fact about that distance.

// OffsetIffDivides — moving a number by d keeps its class mod n exactly
// when n divides d. Modulo 0 a class is a single number, and the claim is
// that d = 0 exactly when 0 divides d. Otherwise, if x and x + d leave
// the same remainder, the two divisions by n differ only in their
// quotients, so d is a multiple of n; and a multiple of n added to x
// changes the quotient and leaves the remainder alone.
var OffsetIffDivides = offsetIffDividesThm{family.Add(registry.ProofEntry{
	Name: "OffsetIffDivides",
	Key:  "prop_6f3d36b6467c5594",
	Build: family.Theorem("∀x d n:num. x ≡ x + d (mod n) ⇔ n ∣ d",
		func(a *Argument) {
			a.Do(Unfold(CongDef))
			x, d, n := a.FixAs[Nat]("x"), a.FixAs[Nat]("d"), a.FixAs[Nat]("n")
			zero := a.Ctx().Nat(0)

			a.Cases(a.Term("n = 0"))
			a.When(
				"modulo 0 a class is a single number",
				func(b *Argument, isZero Fact) {
					b.Do(isZero.Rw())
					fixed := b.Have(
						"x + d is x exactly when d is 0",
						"x = x + d ⇔ d = 0",
						ByArith())
					b.Show(
						"and 0 divides d exactly when d is 0",
						By(fixed, nat_div_mod.ModZero, nat_divides.ZeroDivides.At(d), nat_divides.DividesRefl.At(zero)))
				})
			a.Otherwise(
				"a nonzero modulus divides both numbers with a remainder",
				func(b *Argument, nonzero Fact) {
					moved := b.TermAs[Nat]("x + d")
					b.Iff()
					b.Forward(
						"equal remainders leave d as the difference of two multiples of n",
						func(c *Argument, same Fact) {
							first := c.Have(
								"x is its quotient's multiple of n plus its remainder",
								"x = div(x, n) * n + rem(x, n)",
								By(nonzero, nat_div_mod.Division.At(x, n)))
							second := c.Have(
								"and so is x + d",
								"x + d = div(x + d, n) * n + rem(x + d, n)",
								By(nonzero, nat_div_mod.Division.At(moved, n)))
							quotients := c.Have(
								"the two divisions differ only in their quotients",
								"div(x, n) * n + d = div(x + d, n) * n",
								ByArith(same, first, second))
							quotient, movedQuotient := c.TermAs[Nat]("div(x, n)"), c.TermAs[Nat]("div(x + d, n)")
							low := c.Have(
								"n divides the first multiple",
								"n ∣ div(x, n) * n",
								By(nat_divides.DividesOwnMultiple.At(n, quotient)))
							high := c.Have(
								"and the second",
								"n ∣ div(x + d, n) * n",
								By(nat_divides.DividesOwnMultiple.At(n, movedQuotient)))
							c.Show(
								"so it divides what the first falls short of the second by",
								By(quotients, low, high, nat_divides.DividesAddCancel.At(n, c.TermAs[Nat]("div(x, n) * n"), d)))
						})
					b.Backward(
						"a multiple of n added to x leaves the remainder alone",
						func(c *Argument, divides Fact) {
							k, factor := c.ObtainAs[Nat](
								"d is n taken some number of times",
								"∃k:num. d = n * k",
								By(divides, nat_divides.DividesFactor.At(n, d)))
							c.Show(
								"so x + d is x plus k copies of n",
								By(Normalized, factor, nat_arith.MulSym.At(n, k), nat_div_mod.ModEq.At(moved, x, n, k)))
						})
				})
		}),
})}

// DistIffDivides — two numbers are congruent mod n exactly when n divides
// the distance between them. Whichever is the larger is the smaller plus
// that distance, and OffsetIffDivides reads the congruence there.
var DistIffDivides = distIffDividesThm{family.Add(registry.ProofEntry{
	Name: "DistIffDivides",
	Key:  "prop_f38d578f1178498a",
	Build: family.Theorem("∀x y n:num. x ≡ y (mod n) ⇔ n ∣ dist((x, y))",
		func(a *Argument, x, y, n *Expr[Nat]) {
			a.Cases(a.Term("x ≤ y"))
			a.When(
				"y lies past x",
				func(b *Argument, below Fact) {
					d, past := b.ObtainAs[Nat](
						"y is x plus the distance",
						"∃d:num. y = x + d",
						By(below, nat_order.LessEqExists.At(y, x)))
					b.Do(past.Rw())
					b.Show(
						"which OffsetIffDivides reads",
						By(Normalized, OffsetIffDivides.At(x, d, n), nat_monus.DistRightAdd.At(x, d)))
				})
			a.Otherwise(
				"x lies past y",
				func(b *Argument, above Fact) {
					d, past := b.ObtainAs[Nat](
						"x is y plus the distance",
						"∃d:num. x = y + d",
						By(Normalized, above, nat_order.LessEqTotal.At(x, y), nat_order.LessEqExists.At(x, y)))
					b.Do(past.Rw())
					offset := b.Have(
						"y and y + d are congruent exactly when n divides d",
						"y ≡ y + d (mod n) ⇔ n ∣ d",
						By(OffsetIffDivides.At(y, d, n)))
					b.Show(
						"congruence is equality of remainders, which reads either "+
							"way round, and the distance from y + d back to y is d",
						By(Normalized, offset, b.Ctx().ConstDefNormalized("nat_cong"), nat_monus.DistLeftAdd.At(y, d)))
				})
		}),
})}

// AddCancel — a common summand cancels from a congruence. Moving both
// numbers by the same x does not change the distance between them.
var AddCancel = addCancelThm{family.Add(registry.ProofEntry{
	Name: "AddCancel",
	Key:  "prop_489e71cda8ff1613",
	Build: family.Theorem("∀x y z n:num. x + y ≡ x + z (mod n) ⇔ y ≡ z (mod n)",
		func(a *Argument, x, y, z, n *Expr[Nat]) {
			movedY, movedZ := a.TermAs[Nat]("x + y"), a.TermAs[Nat]("x + z")
			shifted := a.Have(
				"moving both by x keeps their distance",
				"dist((x + y, x + z)) = dist((y, z))",
				Derive(func(b *Argument) {
					b.Do(Cite(nat_monus.Dist, movedY, movedZ), Cite(nat_monus.Dist, y, z))
					b.Show(
						"the two truncated differences are unchanged",
						ByArith())
				}))
			a.Show(
				"so the two congruences say the same about n",
				By(shifted, DistIffDivides.At(movedY, movedZ, n), DistIffDivides.At(y, z, n)))
		}),
})}

// MulCancel — a factor coprime to the modulus cancels from a congruence.
// Multiplying two numbers by c multiplies the distance between them by
// c, and a modulus coprime to c that divides c times the distance
// divides the distance itself (nat_gcd.CoprimeCancel).
var MulCancel = mulCancelThm{family.Add(registry.ProofEntry{
	Name: "MulCancel",
	Key:  "prop_d9a9ec82403a2adc",
	Build: family.Theorem(Statement{
		Binders: "∀c x y n:num.",
		Hypotheses: []string{
			"nat_coprime(c, n)",
		},
		Conclusion: "c * x ≡ c * y (mod n) ⇔ x ≡ y (mod n)",
	},
		func(a *Argument, c, x, y, n *Expr[Nat], coprime Fact) {
			distance := a.TermAs[Nat]("dist((x, y))")
			flipped := a.Have(
				"the modulus is coprime to c",
				"nat_coprime(n, c)",
				By(coprime, nat_gcd.CoprimeSym.At(c, n)))
			scaled := a.Have(
				"c·x ≡ c·y exactly when n divides the distance between "+
					"them, which is c times the distance between x and y",
				"c * x ≡ c * y (mod n) ⇔ n ∣ c * dist((x, y))",
				By(
					DistIffDivides.At(a.TermAs[Nat]("c * x"), a.TermAs[Nat]("c * y"), n),
					nat_monus.DistLeftMul.At(c, x, y)))
			a.Iff()
			a.Forward(
				"n, coprime to c, sheds c from what it divides",
				func(b *Argument, congruent Fact) {
					b.Show(
						"so it divides the distance itself",
						By(
							congruent,
							scaled,
							flipped,
							DistIffDivides.At(x, y, n),
							nat_arith.MulSym.At(c, distance),
							nat_gcd.CoprimeCancel.At(n, distance, c)))
				})
			a.Backward(
				"a divisor of the distance divides every multiple of it",
				func(b *Argument, congruent Fact) {
					b.Show(
						"so it divides c times the distance",
						By(
							congruent,
							scaled,
							DistIffDivides.At(x, y, n),
							nat_arith.MulSym.At(c, distance),
							nat_divides.DividesMul.At(n, distance, c)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// An inverse modulo n
// ---------------------------------------------------------------------------

// InverseExists — for n > 0, a number coprime to n has an inverse mod n
// below n. Multiplying by a and reducing mod n maps the residues below n
// into themselves, and one-to-one: a, coprime to n, cancels from a
// congruence (MulCancel), and two congruent residues below n are equal. A
// one-to-one map of the residues below n into themselves is onto them
// (num_segment.BelowStrictInjectiveOnto), and the residue of 1 is one of
// them.
var InverseExists = inverseExistsThm{family.Add(registry.ProofEntry{
	Name: "InverseExists",
	Key:  "prop_b38be3c69fe7f4a3",
	Build: family.Theorem(Statement{
		Binders: "∀n a:num.",
		Hypotheses: []string{
			"0 < n",
			"nat_coprime(a, n)",
		},
		Conclusion: "∃b:num. b < n ∧ a * b ≡ 1 (mod n)",
	}, func(arg *Argument, n *Expr[Nat], positive Fact, a *Expr[Nat], coprime Fact) {
		below := arg.Have(
			"every remainder mod n lies below n",
			"∀m:num. rem(m, n) < n",
			arg.ForEach(func(m *Expr[Nat]) Action {
				return By(positive, nat_order.PosIffNonzero.At(n), nat_div_mod.Division.At(m, n))
			}))
		oneToOne := arg.Have(
			"multiplying by a and reducing mod n is one-to-one on the residues below n",
			"∀i j:num. i < n ∧ j < n ∧ rem(a * i, n) = rem(a * j, n) ⇒ i = j",
			Derive(func(b *Argument) {
				i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
				same := b.Assume()
				b.Show(
					"a cancels from a·i ≡ a·j, and two congruent residues below n are equal",
					By(
						coprime,
						same,
						MulCancel.At(a, i, j, n),
						CongDef.At(b.TermAs[Nat]("a * i"), b.TermAs[Nat]("a * j"), n),
						CongDef.At(i, j, n),
						nat_div_mod.ModInjectiveBelow.At(i, j, n)))
			}))
		arg.Show(
			"so it is onto them, and the residue of 1 is one of them",
			By(
				below,
				oneToOne,
				num_segment.BelowStrictInjectiveOnto.At(
					n,
					arg.TermAs[Fun[Nat, Nat]]("λx:num. rem(a * x, n)"),
					arg.TermAs[Nat]("rem(1, n)")),
				CongDef))
	}),
})}
