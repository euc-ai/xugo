// encoding.go — the injective encodings the universe is built from: the
// two pairing functions on ℕ, the projections that undo them, and the
// injections of a number, an atom, a family and a pair into predicates
// on (num, A). The constants are the chapter's own definitions
// (definitions.go).

package datatype_universe

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The pairing functions on ℕ
// ---------------------------------------------------------------------------

// NumPairInjective — num_pair(x, y) = 2^x · (2y + 1) is injective. The
// exponent is read off parity: 2y + 1 is odd, so x is exactly the power
// of 2 dividing the value — if x1 ≤ x2 and the values agree, cancelling
// 2^x1 leaves the odd number 2y1 + 1 equal to 2^(x2 − x1) · (2y2 + 1),
// which is even unless the gap is 0. With the exponents equal the odd
// cofactors agree, and 2y + 1 determines y.
var NumPairInjective = numPairInjectiveThm{family.Add(registry.ProofEntry{
	Name: "NumPairInjective",
	Key:  "prop_1da30d340287e79e",
	Build: family.Sections(
		"∀x₁ y₁ x₂ y₂:num. num_pair(x₁, y₁) = num_pair(x₂, y₂) ⇔ x₁ = x₂ ∧ y₁ = y₂",
		func(ctx *Script, headline string) *GoalStackNode {
			// exponentsAgree — the one-sided half of the exponent argument:
			// the smaller exponent cannot be strictly smaller. The top
			// reads it in both directions through the totality of ≤.
			exponentsAgree := ctx.Lemma(
				"∀x₁ y₁ x₂ y₂:num. "+
					"    x₁ ≤ x₂ ⇒ nat_pow(2, x₁) * (2 * y₁ + 1) = nat_pow(2, x₂) * (2 * y₂ + 1) ⇒ x₁ = x₂",
				func(a *Argument, x1, y1, x2, y2 Term, le, eq Fact) {
					two, one := a.Ctx().Numeral(2), a.Ctx().Numeral(1)
					d, gap := a.Obtain(
						"write the larger exponent as x₁ + d",
						"∃d:num. x₂ = x₁ + d",
						By(le, At(nat_order.LessEqExists, x2, x1))) // x1 ≤ x2 ⇔ ∃d. x2 = x1 + d

					pow1, powD := a.Term("nat_pow(2, x₁)"), a.Term("nat_pow(2, d)")
					odd1, odd2 := a.Term("2 * y₁ + 1"), a.Term("2 * y₂ + 1")
					cancel := a.Have(
						"split 2^(x₁ + d) into 2^x₁ · 2^d and cancel the nonzero factor 2^x₁",
						"2 * y₁ + 1 = nat_pow(2, d) * (2 * y₂ + 1)",
						By(
							eq,
							gap,
							At(nat_arith.PowAdd, two, x1, d),         // 2^(x1 + d) = 2^x1 · 2^d
							At(nat_arith.MulAssoc, pow1, powD, odd2), // 2^x1 · (2^d · (2y2 + 1)) = 2^x1 · 2^d · (2y2 + 1)
							// cancel 2^x1 unless it is 0
							At(nat_arith.MulEqLCancel, pow1, odd1, a.Term("nat_pow(2, d) * (2 * y₂ + 1)")),
							At(nat_arith.PowTwoNonzero, x1))) // 2^x1 ≠ 0

					dZero := a.Have(
						"d = 0: for d ≠ 0 the right side is even, but the left side is odd",
						"d = 0",
						By(
							cancel,
							At(nat_parity.EvenMul, powD, odd2), // nat_even(2^d · (2y2 + 1)) ⇔ nat_even(2^d) ∨ nat_even(2y2 + 1)
							At(nat_parity.EvenPow, two, d),     // nat_even(2^d) ⇔ nat_even(2) ∧ d ≠ 0
							At(nat_parity.EvenAdd, a.Term("2 * y₁"), one), // nat_even(2y1 + 1) ⇔ (nat_even(2y1) ⇔ nat_even(1))
							At(nat_parity.EvenDouble, y1),                 // nat_even(2y1)
							nat_parity.NatEven,
							nat_arith.Two,
							nat_arith.OneIsSucZero, // 2 = suc(suc(0)), and nat_even flips at each suc
						))

					a.Show(
						"so x₂ = x₁ + 0 = x₁",
						By(gap, dZero, At(nat_arith.AddZero, x1)))
				})

			return ctx.Theorem(headline, func(a *Argument, x1, y1, x2, y2 Term) {
				a.Do(Unfold(numPairDef))
				a.Iff()
				a.Forward(
					"the exponents agree, then the odd cofactors agree, then the y's",
					func(b *Argument, eq Fact) {
						two, one := b.Ctx().Numeral(2), b.Ctx().Numeral(1)
						double1, double2 := b.Term("2 * y₁"), b.Term("2 * y₂")

						xEq := b.Have(
							"x₁ = x₂: one exponent is at most the other, and exponentsAgree reads that way",
							"x₁ = x₂",
							By(
								eq,
								At(nat_order.LessEqTotal, x1, x2), // x1 ≤ x2 ∨ x2 ≤ x1
								At(exponentsAgree, x1, y1, x2, y2),
								At(exponentsAgree, x2, y2, x1, y1)))

						oddEq := b.Have(
							"cancel the common nonzero factor 2^x₁",
							"2 * y₁ + 1 = 2 * y₂ + 1",
							By(
								eq,
								xEq,
								At(nat_arith.MulEqLCancel, b.Term("nat_pow(2, x₁)"), b.Term("2 * y₁ + 1"), b.Term("2 * y₂ + 1")),
								At(nat_arith.PowTwoNonzero, x1)))

						b.Show(
							"cancel the + 1, then the factor 2 ≠ 0",
							By(
								xEq,
								oddEq,
								At(nat_arith.AddSym, double1, one),
								At(nat_arith.AddSym, double2, one), // 2y + 1 = 1 + 2y
								At(nat_arith.AddEqLCancel, one, double1, double2), // 1 + 2y1 = 1 + 2y2 ⇔ 2y1 = 2y2
								At(nat_arith.MulEqLCancel, two, y1, y2),           // 2y1 = 2y2 ⇔ 2 = 0 ∨ y1 = y2
								nat_arith.Two,
								At(peano.SucNotZero, one))) // 2 = suc(1) ≠ 0
					})
				a.Backward(
					"equal arguments give equal values",
					func(b *Argument, same Fact) {
						b.Show(
							"substitute x₁ = x₂ and y₁ = y₂",
							By(same))
					})
			})
		}),
})}

// NumTagInjective — num_tag(b, x), which is suc(2x) when b holds and 2x
// otherwise, is injective in the pair (b, x). Two values with the same
// tag agree exactly when the x's do (suc and the factor 2 ≠ 0 cancel);
// two values with different tags never agree, one being odd and the
// other even.
var NumTagInjective = numTagInjectiveThm{family.Add(registry.ProofEntry{
	Name: "NumTagInjective",
	Key:  "prop_586ca18b519dfad4",
	Build: family.Sections(
		"∀b₁ b₂:bool. ∀x₁ x₂:num. num_tag(b₁, x₁) = num_tag(b₂, x₂) ⇔ (b₁ ⇔ b₂) ∧ x₁ = x₂",
		func(ctx *Script, headline string) *GoalStackNode {
			// oddNotEven — the two shapes a num_tag value can take never meet.
			oddNotEven := ctx.Lemma("∀m n:num. suc(2 * m) ≠ 2 * n",
				func(a *Argument, m, n Term) {
					a.Show(
						"suc(2m) is odd and 2n is even, and no number is both",
						By(
							Normalized,
							At(nat_parity.OddSucDouble, m),
							At(nat_parity.EvenDouble, n),
							At(nat_parity.NotEvenAndOdd, a.Term("2 * n"))))
				})

			return ctx.Theorem(headline, func(a *Argument, b1, b2, x1, x2 Term) {
				a.Do(Unfold(numTagDef))
				two, one := a.Ctx().Numeral(2), a.Ctx().Numeral(1)

				a.Cases(b1)
				a.When(
					"b₁: the left value is suc(2x1)",
					func(b *Argument, hb1 Fact) {
						b.Cases(b2)
						b.When(
							"b₂: suc(2x1) = suc(2x2) ⇔ x₁ = x₂ — suc cancels, then 2 cancels",
							func(c *Argument, hb2 Fact) {
								c.Show(
									"both tags hold, so the tags agree and the equation is suc(2x1) = suc(2x2)",
									By(
										hb1,
										hb2,
										At(peano.SucInjective, c.Term("2 * x₁"), c.Term("2 * x₂")), // suc(2x1) = suc(2x2) ⇔ 2x1 = 2x2
										At(nat_arith.MulEqLCancel, two, x1, x2),                    // 2x1 = 2x2 ⇔ 2 = 0 ∨ x1 = x2
										nat_arith.Two,
										At(peano.SucNotZero, one))) // 2 = suc(1) ≠ 0
							})
						b.Otherwise(
							"¬b₂: suc(2x1) ≠ 2x2 by parity, and the tags disagree",
							func(c *Argument, nb2 Fact) {
								c.Show(
									"both sides of the ⇔ fail",
									By(hb1, nb2, At(oddNotEven, x1, x2)))
							})
					})
				a.Otherwise(
					"¬b₁: the left value is 2x1",
					func(b *Argument, nb1 Fact) {
						b.Cases(b2)
						b.When(
							"b₂: 2x1 ≠ suc(2x2) by parity, and the tags disagree",
							func(c *Argument, hb2 Fact) {
								c.Show(
									"both sides of the ⇔ fail",
									By(nb1, hb2, At(oddNotEven, x2, x1)))
							})
						b.Otherwise(
							"¬b₂: 2x1 = 2x2 ⇔ x₁ = x₂ — the factor 2 cancels",
							func(c *Argument, nb2 Fact) {
								c.Show(
									"neither tag holds, so the tags agree and the equation is 2x1 = 2x2",
									By(
										nb1,
										nb2,
										At(nat_arith.MulEqLCancel, two, x1, x2), // 2x1 = 2x2 ⇔ 2 = 0 ∨ x1 = x2
										nat_arith.Two,
										At(peano.SucNotZero, one))) // 2 = suc(1) ≠ 0
							})
					})
			})
		}),
})}

// ---------------------------------------------------------------------------
// The injections into predicates on (num, A)
// ---------------------------------------------------------------------------

// InjectNumInjective — inject_num(n), the predicate λ(m, a). m = n, determines n:
// two such predicates agree exactly when their indices do.
var InjectNumInjective = injectNumInjectiveThm{family.Add(registry.ProofEntry{
	Name: "InjectNumInjective",
	Key:  "prop_1694fcc43cc21e24",
	Build: family.Theorem("∀n₁ n₂:num. inject_num⟨A:A⟩(n₁) = inject_num⟨A:A⟩(n₂) ⇔ n₁ = n₂",
		func(a *Argument, n1, n2 Term) {
			a.Do(Unfold(injectNumDef))
			a.Iff()
			a.Forward(
				"equal predicates hold at the same points, and inject_num(n) holds exactly at index n",
				func(b *Argument, pointwise Fact) {
					b.Show(
						"read the predicate equation pointwise",
						By(pointwise))
				})
			a.Backward(
				"equal indices give the same predicate",
				func(b *Argument, same Fact) {
					b.Show(
						"substitute n₁ = n₂",
						By(Normalized, same))
				})
		}),
})}

// InjectAtomInjective — inject_atom(a), the predicate λ(m, b). b = a, determines a:
// two such predicates agree exactly when their atoms do.
var InjectAtomInjective = injectAtomInjectiveThm{family.Add(registry.ProofEntry{
	Name: "InjectAtomInjective",
	Key:  "prop_343a3405e5e9048d",
	Build: family.Theorem("∀a₁ a₂:A. inject_atom(a₁) = inject_atom(a₂) ⇔ a₁ = a₂",
		func(a *Argument, a1, a2 Term) {
			a.Do(Unfold(injectAtomDef))
			a.Iff()
			a.Forward(
				"equal predicates hold at the same points, and inject_atom(a) holds exactly at atom a",
				func(b *Argument, pointwise Fact) {
					b.Show(
						"read the predicate equation pointwise",
						By(pointwise))
				})
			a.Backward(
				"equal atoms give the same predicate",
				func(b *Argument, same Fact) {
					b.Show(
						"substitute a₁ = a₂",
						By(Normalized, same))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The injections of a two-argument predicate and of a pair of predicates
// ---------------------------------------------------------------------------
//
// inject_family and inject_pair read their argument predicates through the two pairing
// functions above, so both injectivity laws come down to the PROJECTIONS
// of those pairings: num_pair_fst/num_pair_snd for num_pair, num_tag_bit/num_tag_value for
// num_tag. Each pair of projections is a specification
// — a Hilbert choice from "a left inverse and a right inverse exist",
// which is what the pairing's injectivity buys. The members below mint
// them that way: an existence lemma with the ε-witnesses, then the
// nested choice steps that name the constants (peano's indSucSpec is the
// model), and the injectivity law reads the encoding at a pair.

// ---------------------------------------------------------------------------
// The projections
// ---------------------------------------------------------------------------

// NumPairProjections — num_pair_fst and num_pair_snd undo num_pair. Each is by
// definition a component of SOME pair encoding the number; at
// num_pair(x, y) injectivity makes that component x (y).
var NumPairProjections = numPairProjectionsThm{family.Add(registry.ProofEntry{
	Name: "NumPairProjections",
	Key:  "prop_c34e1622895b6765",
	Build: family.Theorem(
		"∀x y:num. num_pair_fst(num_pair(x, y)) = x ∧ num_pair_snd(num_pair(x, y)) = y",
		func(a *Argument, x, y Term) {
			a.Do(Unfold(numPairFstDef), Unfold(numPairSndDef), SplitConj(
				Case(
					"the chosen first component pairs with something to num_pair(x, y), so it is x",
					By(NumPairInjective)),
				Case(
					"the chosen second component is paired by something to num_pair(x, y), so it is y",
					By(NumPairInjective)),
			))
		}),
})}

// NumTagProjections — num_tag_bit and num_tag_value undo num_tag: the tag and
// the value of some pair encoding the number, which injectivity makes
// b and x at num_tag(b, x).
var NumTagProjections = numTagProjectionsThm{family.Add(registry.ProofEntry{
	Name: "NumTagProjections",
	Key:  "prop_e043356ef4442805",
	Build: family.Theorem(
		"∀b:bool. ∀x:num. (num_tag_bit(num_tag(b, x)) ⇔ b) ∧ num_tag_value(num_tag(b, x)) = x",
		func(a *Argument, b, x Term) {
			a.Do(Unfold(numTagBitDef), Unfold(numTagValueDef), SplitConj(
				Case(
					"the chosen tag heads some pair encoding num_tag(b, x), so it is b",
					By(HilbertDenoted, Broadcast, NumTagInjective)),
				Case(
					"the chosen value ends some pair encoding num_tag(b, x), so it is x",
					By(NumTagInjective)),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The injections into predicates on (num, A)
// ---------------------------------------------------------------------------

// InjectFamilyInjective — inject_family(f), the predicate λ(n, a). f(num_pair_fst(n), num_pair_snd(n), a),
// determines f: reading it at n = num_pair(x, y) recovers f(x, y, a).
var InjectFamilyInjective = injectFamilyInjectiveThm{family.Add(registry.ProofEntry{
	Name: "InjectFamilyInjective",
	Key:  "prop_7e9415be24b86830",
	Build: family.Theorem(
		"∀f g:(num → num → A → bool). inject_family(f) = inject_family(g) ⇔ f = g",
		func(a *Argument, f, g Term) {
			a.Do(Unfold(injectFamilyDef))
			a.Iff()
			a.Forward(
				"equal encodings agree at (num_pair(x, y), a), where the projections return x and y",
				func(b *Argument, encodingsEq Fact) {
					b.Do(Funext()) // f = g ↦ ∀x y a. f(x, y, a) ⇔ g(x, y, a)
					x, y := b.Fix(), b.Fix()
					b.Fix() // the atom a
					b.Show(
						"read the encodings at n = num_pair(x, y) and project",
						By(Normalized, Broadcast, encodingsEq, At(NumPairProjections, x, y)))
				})
			a.Backward(
				"equal predicates give equal encodings",
				func(b *Argument, same Fact) {
					b.Show(
						"substitute f = g",
						By(Normalized, same))
				})
		}),
})}

// InjectPairInjective — inject_pair(f1, f2), the predicate λ(n, a). if num_tag_bit(n) then
// f1(num_tag_value(n), a) else f2(num_tag_value(n), a), determines the pair:
// reading it at n = num_tag(⊤, x) recovers f1(x, a), at n = num_tag(⊥, x)
// recovers f2(x, a).
var InjectPairInjective = injectPairInjectiveThm{family.Add(registry.ProofEntry{
	Name: "InjectPairInjective",
	Key:  "prop_7baffcc7641f02cd",
	Build: family.Theorem(
		"∀f₁ f₂ g₁ g₂:(num → A → bool). inject_pair(f₁, f₂) = inject_pair(g₁, g₂) ⇔ f₁ = g₁ ∧ f₂ = g₂",
		func(a *Argument, f1, f2, g1, g2 Term) {
			a.Do(Unfold(injectPairDef))
			a.Iff()
			a.Forward(
				"equal encodings agree at (num_tag(t, x), a): the "+
					"tag t selects the component, num_tag_value returns x",
				func(b *Argument, encodingsEq Fact) {
					// readAt — the component selected by `tag` agrees
					// pointwise: at n = num_tag(tag, x) both encodings
					// reduce to that component at (x, a).
					readAt := func(tag Term) Action {
						return Derive(func(c *Argument) {
							c.Do(Funext()) // f = g ↦ ∀x a. f(x, a) ⇔ g(x, a)
							x := c.Fix()
							c.Fix() // the atom a
							c.Show(
								"read the encodings at n = num_tag(tag, x) and project",
								By(Normalized, Broadcast, encodingsEq, At(NumTagProjections, tag, x)))
						})
					}
					b.Do(SplitConj(
						Case(
							"f₁ = g₁: read the encodings at tag ⊤",
							readAt(True)),
						Case(
							"f₂ = g₂: read the encodings at tag ⊥",
							readAt(False)),
					))
				})
			a.Backward(
				"equal pairs give equal encodings",
				func(b *Argument, same Fact) {
					b.Show(
						"substitute f₁ = g₁ and f₂ = g₂",
						By(Normalized, same))
				})
		}),
})}
