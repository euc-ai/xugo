// nat_divides.go — the chapter: divisibility, defined in ℕ.
//
// Three parts, marked by banners:
//
// - The elementary laws of `nat_divides`
// - How `nat_divides` interacts with nat_div
// - The multiple behind the relation, read as a theorem

package nat_divides

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The elementary laws of `nat_divides`
// ---------------------------------------------------------------------------
//
// The elementary laws of `nat_divides`: its bridge to the
// remainder, its order facts, and how the relation meets addition.
//
// Everything here argues in ℕ and in ℕ alone. The chapter OWNS its
// predicate, so a member of this part that needs the multiple behind the
// relation unfolds the definition — `Unfold(DividesFactor)` — instead
// of citing a characterization theorem for it.
//
// The unfold has one shape consequence, and it is why two closure forms
// appear side by side below. The unfold trivially-simplifies its
// own residual, and that simplify moves a goal's leading antecedent into
// the hypotheses. A member stated as `d ∣ n ⇒ …` therefore
// unfolds BEFORE it strips — the zero-parameter closure, taking its
// binders with `a.FixAs[Nat]` and its antecedent with `a.Assume`, so the
// factorization arrives as a named premise rather than as an anonymous
// resident hypothesis. Members with no leading implication keep the
// ordinary binder-parameter closure.

// DividesMod is the bridge between this chapter's predicate and nat_arith's
// remainder: divisibility is exactly a vanishing remainder.
//
// Both sides say n₀ is a whole number of m₀'s and differ only in which
// side of the product the count sits on — the definition writes n = m·x,
// nat_div_mod.ModEqZero writes n = q·m — so commutativity identifies them
// outright, in both directions at once.
var DividesMod = dividesModThm{family.Add(registry.ProofEntry{
	Name: "DividesMod",
	Key:  "prop_93f533c93a503e0",
	Build: family.Theorem(
		"∀m n:num. m ∣ n ⇔ rem(n, m) = 0",
		func(a *Argument, m, n *Expr[Nat]) {
			// ↦ (∃x. n₀ = m₀ · x) ⇔ nat_mod(n₀, m₀) = 0
			a.Do(Unfold(DividesFactor))

			a.Show(
				"the two factorizations are the same product read from opposite sides",
				By(nat_arith.MulSym, nat_div_mod.ModEqZero))
		}),
})}

// DividesOne pins the bottom of the divisibility order: 1 is divisible
// by itself and by nothing else. It is what the gcd tier reaches for
// whenever a common divisor has been squeezed down to a divisor of 1.
//
// The whole content is a single factorization, `∃x. 1 = n₀·x`, which
// each direction of the ⇔ crosses exactly once. Only the ⇒ direction
// needs nat_arith.MulEqOne (a product of naturals is 1 only when both factors
// are); ⇐ exhibits the factorization from the unit law.
var DividesOne = dividesOneThm{family.Add(registry.ProofEntry{
	Name: "DividesOne",
	Key:  "prop_9320652c939b871b",
	Build: family.Theorem(
		"∀n:num. n ∣ 1 ⇔ n = 1",
		func(a *Argument, n *Expr[Nat]) {
			one := a.Ctx().Nat(1)

			// ↦ (∃x. 1 = n₀ · x) ⇔ n₀ = 1
			a.Do(Unfold(DividesFactor))

			a.Iff()
			a.Forward(
				"1 = n₀·x₀ for some x₀, and a product of naturals is 1 only when both factors are",
				func(b *Argument, factored Fact) {
					// 1 = n₀·x₀
					x, factor := b.UnpackAs[Nat](factored)

					b.Show(
						"MulEqOne at (n₀, x₀) reads n₀ = 1 off that factorization",
						// n₀·x₀ = 1 ⇔ n₀ = 1 ∧ x₀ = 1
						By(factor, nat_arith.MulEqOne.At(n, x)))
				})
			a.Backward(
				"n₀ = 1, so 1 = n₀·1 exhibits 1 as a multiple of n₀",
				func(b *Argument, isOne Fact) {
					b.Take(one) // x := 1
					b.Show(
						"n₀·1 is n₀, which the case makes 1",
						By(isOne, nat_arith.MulOne))
				})
		}),
})}

// DividesLessEq is the order fact of the chapter: a divisor is at most its
// multiple. The exception is the one every multiplicative bound on ℕ
// carries — 0 is a multiple of everything, and bounds nothing.
//
// The whole proof is the cofactor, whose two cases are exactly the two
// disjuncts of the conclusion.
var DividesLessEq = dividesLessEqThm{family.Add(registry.ProofEntry{
	Name: "DividesLessEq",
	Key:  "prop_fe1d8803b9f13ea4",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num.",
			Hypotheses: []string{
				"m ∣ n",
			},
			Conclusion: "m ≤ n ∨ n = 0",
		},
		// Unfold-before-strip (file header): the antecedent is wanted as a
		// named premise, so it is taken with Assume after the unfold.
		func(a *Argument) {
			// ↦ ∀m n. (∃x. n = m · x) ⇒ m ≤ n ∨ n = 0
			a.Do(Unfold(DividesFactor))

			m := a.FixAs[Nat]()
			a.FixAs[Nat]() // n₀, the multiple — only the labels below name it
			zero := a.Ctx().Nat(0)

			// The divisibility names a cofactor: n₀ = m₀·x₀.
			x, factor := a.UnpackAs[Nat](a.Assume())

			nonzero := a.Unless(
				Equal(x, zero),
				"a cofactor of 0 collapses the multiple — the right disjunct",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"at x₀ = 0 the factorization reads n₀ = m₀·0",
						By(isZero, factor, nat_arith.MulZero.At(m))) // m₀·0 = 0
				}))

			a.Show(
				"a nonzero cofactor cannot shrink m₀, and m₀·x₀ is n₀ — the left disjunct",
				By(Normalized, nonzero, factor, nat_order.LessEqMulNonzero.At(m, x))) // x₀ = 0 ∨ m₀ ≤ m₀·x₀
		}),
})}

// ZeroDivides — 0 divides nothing but 0. Promoted to an entry because
// both DividesLessEqStrong and DividesAntisym need it, each at the moment a
// resident equation has just turned a divisibility into one by 0.
//
// The observation is chapter machinery, not chapter API.
var ZeroDivides = zeroDividesThm{family.Add(registry.ProofEntry{
	Name: "ZeroDivides",
	Key:  "prop_e48f2d17e45b62d3",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num.",
			Hypotheses: []string{
				"0 ∣ n",
			},
			Conclusion: "n = 0",
		},
		// Unfold-before-strip — see the file header.
		func(a *Argument) {
			// ↦ ∀n. (∃x. n = 0 · x) ⇒ n = 0
			a.Do(Unfold(DividesFactor))

			a.FixAs[Nat]() // n₀, the multiple — only the label below names it

			// The divisibility names a cofactor: n₀ = 0·x₀.
			_, factor := a.Unpack(a.Assume())

			a.Show(
				"the factorization reads n₀ = 0·x₀, and 0 annihilates",
				By(factor, nat_arith.MulLeftZeroClause))
		}),
})}

// DividesLessEqStrong closes a divisor in from both sides: a divisor of a
// nonzero number is at least 1 and at most that number. DividesLessEq
// already supplies the upper bound, so the sharpening is the lower one,
// and it rests on a single observation — 0 divides nothing but 0.
//
// That observation is ZeroDivides, and it is what rules m₀ = 0 out: a
// zero divisor would force n₀ = 0, which the other degenerate case has
// already conceded. A divisor that is not 0 is, on ℕ, one that is at
// least 1.
//
// Nothing here opens the definition: every divisibility is consumed by
// a sibling stated over the same predicate, so the relation stays
// folded throughout.
var DividesLessEqStrong = dividesLessEqStrongThm{family.Add(registry.ProofEntry{
	Name: "DividesLessEqStrong",
	Key:  "prop_9ce5bd9d959e47f9",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num.",
			Hypotheses: []string{
				"m ∣ n",
			},
			Conclusion: "1 ≤ m ∧ m ≤ n ∨ n = 0",
		},
		func(a *Argument, m, n *Expr[Nat], div Fact) {
			zero := a.Ctx().Nat(0)

			nonzeroN := a.Unless(
				Equal(n, zero),
				"n₀ = 0 is the right disjunct itself",
				TrivialNormalized())

			nonzeroM := a.Unless(
				Equal(m, zero),
				"0 as the divisor would force n₀ = 0, which n₀ ≠ 0 forbids",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"at m₀ = 0 the hypothesis makes 0 the divisor, and 0 divides nothing but 0",
						By(isZero, div, ZeroDivides.At(n), nonzeroN))
				}))

			atLeastOne := a.Have(
				"nonzero means positive, positive means suc(0) ≤ m, and ONE spells suc(0) as 1",
				"1 ≤ m",
				By(
					nonzeroM,
					nat_order.PosIffNonzero.At(m), // m₀ ≠ 0 ⇔ 0 < m₀
					nat_order.SucLessEqIffLessThan.At(zero, m), // 0 < m₀ ⇔ suc(0) ≤ m₀
					nat_arith.OneIsSucZero))                    // 1 = suc(0)

			bound := a.Have(
				"DividesLessEq at the same pair, with n ≠ 0 already excluding its other disjunct",
				"m ≤ n",
				By(div, nonzeroN, DividesLessEq.At(m, n))) // m₀ ≤ n₀ ∨ n₀ = 0

			a.Show(
				"the two bounds are the left disjunct",
				By(atLeastOne, bound))
		}),
})}

// DividesRefl — every number divides itself. The relation asks for
// nothing but a factorization and n = n·1 is one, so the proof is the
// unfold together with the unit law.
//
// Promoted because two consumers reached for it by different routes:
// DividesAntisym below takes the factorization, while the prime tier
// reads DividesAntisym ITSELF at a repeated argument, where the equation
// side is free and both conjuncts are the one fact wanted. That route
// pays a whole antisymmetry squeeze for a unit law.
var DividesRefl = dividesReflThm{family.Add(registry.ProofEntry{
	Name: "DividesRefl",
	Key:  "prop_4b38ff3371a2c0b1",
	Build: family.Theorem(
		"∀n:num. n ∣ n",
		func(a *Argument, n *Expr[Nat]) {
			one := a.Ctx().Nat(1)

			// ↦ ∃x. n₀ = n₀ · x
			a.Do(Unfold(DividesFactor))

			a.Take(one) // x := 1
			a.Show(
				"n₀·1 is n₀, so 1 is the cofactor",
				By(nat_arith.MulOne))
		}),
})}

// DividesZero — every number divides 0: 0 is d taken no times.
var DividesZero = dividesZeroThm{family.Add(registry.ProofEntry{
	Name: "DividesZero",
	Key:  "prop_c45095d1fc9dcc34",
	Build: family.Theorem(
		"∀d:num. d ∣ 0",
		func(a *Argument, d *Expr[Nat]) {
			zero := a.Ctx().Nat(0)

			// ↦ ∃x. 0 = d₀ · x
			a.Do(Unfold(DividesFactor))

			a.Take(zero) // x := 0
			a.Show(
				"d₀·0 is 0, so 0 is the cofactor",
				By(nat_arith.MulZero))
		}),
})}

// OneDivides — 1 divides every number: n is 1 taken n times.
var OneDivides = oneDividesThm{family.Add(registry.ProofEntry{
	Name: "OneDivides",
	Key:  "prop_b996651abeb74fc",
	Build: family.Theorem(
		"∀n:num. 1 ∣ n",
		func(a *Argument, n *Expr[Nat]) {
			// ↦ ∃x. n₀ = 1 · x
			a.Do(Unfold(DividesFactor))

			a.Take(n) // x := n
			a.Show(
				"1·n₀ is n₀, so n₀ is the cofactor",
				By(nat_arith.OneMul))
		}),
})}

// DividesOwnMultiple — a number divides its multiples, the multiplier
// written on either side: c is the cofactor, commuted where the
// definition writes the divisor first.
var DividesOwnMultiple = dividesOwnMultipleThm{family.Add(registry.ProofEntry{
	Name: "DividesOwnMultiple",
	Key:  "prop_19e4ba4640fa03b6",
	Build: family.Theorem(
		"∀d c:num. d ∣ c * d ∧ d ∣ d * c",
		func(a *Argument, d, c *Expr[Nat]) {
			// ↦ (∃x. c₀ · d₀ = d₀ · x) ∧ (∃x. d₀ · c₀ = d₀ · x)
			a.Do(Unfold(DividesFactor))
			a.Do(SplitConjAll(
				Case(
					"c·d is d taken c times",
					Derive(func(b *Argument) {
						b.Take(c)
						b.Show(
							"c₀·d₀ is d₀·c₀, so c₀ is the cofactor",
							By(nat_arith.MulSym.At(c, d)))
					})),
				Case(
					"and so is d·c",
					Derive(func(b *Argument) {
						b.Take(c)
						b.Show(
							"d₀·c₀ is d₀ taken c₀ times as it stands",
							Basic())
					})),
			))
		}),
})}

// PowDividesPow — a power of p divides every higher power of p: when
// m ≤ n, write n = m + d, and pⁿ is pᵐ · pᵈ.
var PowDividesPow = powDividesPowThm{family.Add(registry.ProofEntry{
	Name: "PowDividesPow",
	Key:  "prop_5439ef2eb61d026e",
	Build: family.Theorem(Statement{
		Binders: "∀p m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "p ^ m ∣ p ^ n",
	}, func(a *Argument, p, m, n *Expr[Nat], le Fact) {
		d, split := a.ObtainAs[Nat](
			"n exceeds m by some d",
			"∃d:num. n = m + d",
			By(le, nat_order.LessEqExists.At(n, m)))
		a.Show(
			"pⁿ = pᵐ · pᵈ is a multiple of pᵐ",
			By(
				Normalized,
				split,
				nat_arith.PowAdd.At(p, m, d),
				DividesOwnMultiple.At(a.TermAs[Nat]("p ^ m"), a.TermAs[Nat]("p ^ d"))))
	}),
})}

// DividesTrans — the relation is transitive. Each divisibility names a
// cofactor, b = a·x and c = b·y, and the product x·y is the cofactor
// for a ∣ c. The whole proof is naming the two and taking their product.
//
// Cited outside the chapter: nat_prime.PrimeFactor walks a divisor
// chain through it.
var DividesTrans = dividesTransThm{family.Add(registry.ProofEntry{
	Name: "DividesTrans",
	Key:  "prop_d92bbbb9698ad32",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b c:num.",
			Hypotheses: []string{
				"a ∣ b",
				"b ∣ c",
			},
			Conclusion: "a ∣ c",
		},
		// Unfold-before-strip — see the file header. The context is `arg`
		// because the statement itself binds `a`.
		func(arg *Argument) {
			// ↦ ∀a b c. (∃x. b = a · x) ∧ (∃x. c = b · x) ⇒ ∃x. c = a · x
			arg.Do(Unfold(DividesFactor))

			a := arg.FixAs[Nat]()
			arg.FixAs[Nat]() // b₀, the middle term — only the claims below name it
			arg.FixAs[Nat]() // c₀, the multiple — likewise
			both := arg.Assume()

			x, viaB := arg.ObtainAs[Nat](
				"the first conjunct is a₀ ∣ b₀, unfolded",
				"∃x:num. b = a * x",
				By(both))
			y, viaC := arg.ObtainAs[Nat](
				"the second conjunct is b₀ ∣ c₀, unfolded",
				"∃y:num. c = b * y",
				By(both))

			arg.Take(arg.Term("x * y")) // the cofactor for a₀ ∣ c₀
			arg.Show(
				"c₀ is (a₀·x₀)·y₀, and regrouping the product reads it as a₀·(x₀·y₀)",
				By(Normalized, viaB, viaC, nat_arith.MulAssoc.At(a, x, y))) // a₀·(x₀·y₀) = (a₀·x₀)·y₀
		}),
})}

// DividesAntisym is the antisymmetry of the relation — two naturals that
// divide each other are the same natural — stated as a biconditional, so
// its easy direction is reflexivity: DividesRefl at n₀, which the
// equation carries to both conjuncts.
//
// Antisymmetry proper squeezes. DividesLessEq turns each divisibility into
// an upper bound, and two naturals each at most the other are equal by
// nat_order.LessEqAntisym. DividesLessEq concedes one degenerate case —
// the multiple may be 0 — and that is where the argument's only real
// content sits: ZeroDivides says a zero on either side drags the other
// down to 0, so both corners prove m₀ = n₀ outright rather than being
// contradictions.
//
// The cite is DividesLessEq rather than the stronger DividesLessEqStrong
// because only the upper bound is used; the `1 ≤ m` conjunct would be
// discarded at both sites.
//
// Like DividesLessEqStrong, this member never opens the definition: every
// divisibility it handles is passed straight to a sibling.
var DividesAntisym = dividesAntisymThm{family.Add(registry.ProofEntry{
	Name: "DividesAntisym",
	Key:  "prop_7148736fae374c1d",
	Build: family.Theorem(
		"∀m n:num. m ∣ n ∧ n ∣ m ⇔ m = n",
		func(a *Argument, m, n *Expr[Nat]) {
			zero := a.Ctx().Nat(0)

			a.Iff()
			a.Forward(
				"each divisibility bounds one side by the other, once neither side is 0",
				func(b *Argument, both Fact) {
					// The two corners DividesLessEq concedes, taken first.
					// Neither is a contradiction: a zero on one side
					// sends the other to 0 through ZeroDivides, so each
					// corner proves m₀ = n₀ on the spot.
					nonzeroN := b.Unless(
						Equal(n, zero),
						"n₀ = 0 makes the second conjunct a divisibility by 0",
						Given(func(c *Argument, isZero Fact) {
							c.Show(
								"ZeroDivides sends m₀ to 0, where the case has already put n₀",
								By(isZero, both, ZeroDivides.At(m)))
						}))

					nonzeroM := b.Unless(
						Equal(m, zero),
						"m₀ = 0 mirrors it, on the first conjunct",
						Given(func(c *Argument, isZero Fact) {
							c.Show(
								"ZeroDivides sends n₀ to 0, where the case has already put m₀",
								By(isZero, both, ZeroDivides.At(n)))
						}))

					upper := b.Have(
						"DividesLessEq at (m₀, n₀), with n₀ ≠ 0 excluding its other disjunct",
						"m₀ ≤ n₀",
						By(both, nonzeroN, DividesLessEq.At(m, n)))

					lower := b.Have(
						"the same at (n₀, m₀), where m₀ ≠ 0 is the exclusion",
						"n₀ ≤ m₀",
						By(both, nonzeroM, DividesLessEq.At(n, m)))

					b.Show(
						"each at most the other, which on ℕ leaves them equal",
						By(upper, lower, nat_order.LessEqAntisym.At(m, n)))
				})
			a.Backward(
				"m₀ = n₀, so one fact — n₀ divides n₀ — is both conjuncts",
				func(b *Argument, isEq Fact) {
					b.Show(
						"m₀ = n₀ makes each conjunct that one fact",
						By(isEq, DividesRefl))
				})
		}),
})}

// DividesAddCancel — a divisor of one summand divides the sum exactly
// when it divides the other summand. The argument runs through the
// remainder rather than the definition, because the definition route
// would recover b's cofactor as d·y − d·x, a subtraction ℕ lacks, while
// remainders never subtract: d ∣ a says the remainder of a vanishes, and reducing the left summand before adding changes no
// remainder (nat_div_mod.ModAddModLeft), so the sum's remainder is
// nat_mod(0 + b, d), which is b's own. Each side of the biconditional is a
// vanishing remainder through DividesMod, and the two remainders are
// one — so they vanish together.
//
// No case on d = 0 is needed: every law cited is stated for all moduli.
//
// Cited outside the chapter: nat_prime.EuclidBound cancels n! out of a
// prime's divisibility of n! + 1 with it.
var DividesAddCancel = dividesAddCancelThm{family.Add(registry.ProofEntry{
	Name: "DividesAddCancel",
	Key:  "prop_6122cf4eda4673b4",
	Build: family.Theorem(
		Statement{
			Binders: "∀d a b:num.",
			Hypotheses: []string{
				"d ∣ a",
			},
			Conclusion: "d ∣ a + b ⇔ d ∣ b",
		},
		// The context is `arg` because the statement itself binds `a`.
		func(arg *Argument, d, a, b *Expr[Nat], div Fact) {
			sumRemainder := arg.Have(
				"the remainder of a₀ vanishes, so reducing it before "+
					"adding leaves rem(0 + b₀, d₀), and 0 + b₀ is b₀",
				"rem(a + b, d) = rem(b, d)",
				By(
					Normalized,
					div,
					DividesMod.At(d, a),                   // d₀ ∣ a₀ ⇔ nat_mod(a₀, d₀) = 0
					nat_div_mod.ModAddModLeft.At(a, b, d), // nat_mod(nat_mod(a₀, d₀) + b₀, d₀) = nat_mod(a₀ + b₀, d₀)
					nat_arith.AddLeftZeroClause.At(b)))    // 0 + b₀ = b₀

			arg.Show(
				"each divisibility is its remainder vanishing, and the two remainders are one",
				By(
					Normalized,
					sumRemainder,
					DividesMod.At(d, arg.TermAs[Nat]("a + b")), // d₀ ∣ a₀ + b₀ ⇔ nat_mod(a₀ + b₀, d₀) = 0
					DividesMod.At(d, b)))                       // d₀ ∣ b₀ ⇔ nat_mod(b₀, d₀) = 0
		}),
})}

// ---------------------------------------------------------------------------
// How `nat_divides` interacts with nat_div
// ---------------------------------------------------------------------------
//
// How `nat_divides` interacts with nat_div: what divisibility of one
// operand lets you do to a quotient.
//
// DivAdd and MultDiv argue entirely in ℕ. A divisibility is opened once,
// by unfolding the chapter's definition, to name the cofactor it asserts,
// and from there the argument is arithmetic on that factorization. The
// unfold-before-strip form both use is explained in the elementary laws'
// opening note. DivSucIndicator, the step of a quotient from n to n + 1,
// and DivisorQuotient, a divisor times its quotient, read divisibility
// through the remainder (DividesMod) instead.

// DivAdd — division distributes over a sum as soon as the divisor
// divides ONE of the summands. It need not divide both: the divided
// summand contributes its exact cofactor, and the other summand's
// remainder is simply carried along untouched, which is what makes the
// two quotients add.
//
// So the whole proof is: name the cofactor of whichever summand is
// divisible, and take its copies of the divisor out of the dividend.
// The two disjuncts are mirror images — the copies sit on the left of
// the sum or on the right — and nat_div_mod.DivMultAdd already states both
// shapes.
//
// The degenerate case is the one every nat_div law carries: at divisor 0
// the convention sends all three quotients to 0, and the identity holds
// for a reason that has nothing to do with divisibility. Taking it
// first, before the disjunction is split, is what keeps it from
// appearing once per branch.
var DivAdd = divAddThm{family.Add(registry.ProofEntry{
	Name: "DivAdd",
	Key:  "prop_1f54c1fc1e7a179f",
	Build: family.Sections(
		Statement{
			Binders: "∀d a b:num.",
			Hypotheses: []string{
				"d ∣ a ∨ d ∣ b",
			},
			Conclusion: "div(a + b, d) = div(a, d) + div(b, d)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// nat_div_mod.DivMultAdd is a four-clause pack over nine binders, and a
			// bare cite of it cannot be refuted against a goal that also has a
			// factorization to chain through. So each clause this proof uses is
			// projected out first, at the shape the headline meets it in; there
			// the pack is the whole content and a single cite settles it.

			// copiesFirst — the divisor's copies lead the dividend.
			copiesFirst := ctx.Lemma(Statement{
				Binders: "∀d x b:num.",
				Hypotheses: []string{
					"d ≠ 0",
				},
				Conclusion: "div(d * x + b, d) = x + div(b, d)",
			},
				func(a *Argument, d, x, b *Expr[Nat], nonzero Fact) {
					a.Show(
						"x₀ copies of d₀ contribute exactly x₀ to the quotient and leave b₀'s own quotient beside it",
						By(nonzero, nat_div_mod.DivMultAdd))
				})

			// copiesLast — the mirror shape: the copies trail the dividend, so
			// the count comes out on the right of the quotient sum.
			copiesLast := ctx.Lemma(Statement{
				Binders: "∀d x b:num.",
				Hypotheses: []string{
					"d ≠ 0",
				},
				Conclusion: "div(b + d * x, d) = div(b, d) + x",
			},
				func(a *Argument, d, x, b *Expr[Nat], nonzero Fact) {
					a.Show(
						"the same count, read off the other end of the sum",
						By(nonzero, nat_div_mod.DivMultAdd))
				})

			// The context is `arg` because the statement itself binds `a`.
			return ctx.Theorem(headline,
				func(arg *Argument) {
					// ↦ ∀d a b. (∃x. a = d · x) ∨ (∃x. b = d · x) ⇒ …
					arg.Do(Unfold(DividesFactor))

					d, a, b := arg.FixAs[Nat](), arg.FixAs[Nat](), arg.FixAs[Nat]()
					guard := arg.Assume()
					zero := arg.Ctx().Nat(0)

					nonzero := arg.Unless(
						Equal(d, zero),
						"a zero divisor settles the identity without the divisibility: every quotient is 0",
						Given(func(c *Argument, isZero Fact) {
							c.Show(
								"the convention sends all three quotients to 0, and 0 = 0 + 0",
								By(
									isZero,
									nat_div_mod.DivZero.At(c.TermAs[Nat]("a + b")), // nat_div(a₀ + b₀, 0) = 0
									nat_div_mod.DivZero.At(a),                      // nat_div(a₀, 0) = 0
									nat_div_mod.DivZero.At(b),                      // nat_div(b₀, 0) = 0
									nat_arith.AddZero.At(zero)))                    // 0 + 0 = 0
						}))

					arg.Do(guard.SplitDisj(
						LeftHolds(
							"a₀ is the divisible summand — the copies of d₀ lead "+
								"the dividend, so its cofactor leads the quotient sum",
							Given(func(c *Argument, factored Fact) {
								// a₀ = d₀·x₀
								x, factor := c.UnpackAs[Nat](factored)

								c.Show(
									"x₀ is a₀'s own quotient, and taking its copies out of the sum leaves b₀'s",
									By(
										Normalized,
										nonzero,
										factor,
										nat_div_mod.DivMult.At(d, x), // nat_div(d₀·x₀, d₀) = x₀
										At(copiesFirst, d, x, b),     // nat_div(d₀·x₀ + b₀, d₀) = x₀ + nat_div(b₀, d₀)
									))
							})),

						RightHolds(
							"b₀ is the divisible summand — mirror: the copies trail "+
								"the dividend, so the cofactor trails the quotient sum",
							Given(func(c *Argument, factored Fact) {
								// b₀ = d₀·x₀
								x, factor := c.UnpackAs[Nat](factored)

								c.Show(
									"x₀ is b₀'s own quotient, and taking its copies out of the sum leaves a₀'s",
									By(
										Normalized,
										nonzero,
										factor,
										nat_div_mod.DivMult.At(d, x), // nat_div(d₀·x₀, d₀) = x₀
										At(copiesLast, d, x, a),      // nat_div(a₀ + d₀·x₀, d₀) = nat_div(a₀, d₀) + x₀
									))
							})),
					))
				})
		}),
})}

// MultDiv — a divisor of one factor of a product can be divided out of
// that factor alone, leaving the other factor beside the quotient. The
// theorem states it for each factor in turn, so it is a two-conjunct
// bundle, and the two conjuncts are mirror images across commutativity.
//
// The content is entirely in the first: a divisible factor m is p·x, so
// the product is p taken x·n times, and a product's quotient by one of
// its own factors is the other. The second conjunct then needs no new
// mathematics — it is the first at the swapped pair, with both products
// turned round — which is why it is a section citing leftFactor rather
// than a repeat of its argument.
//
// The divisor may still be 0, and there the identity holds for the
// unrelated reason that both quotients are 0 by convention. That case is
// taken before the cofactor is ever named: it does not use the
// divisibility, and taking it first is what leaves the main line
// unconditional.
var MultDiv = multDivThm{family.Add(registry.ProofEntry{
	Name: "MultDiv",
	Key:  "prop_d355602dc96e7508",
	Build: family.Sections(
		"(∀m n p:num. p ∣ m ⇒ div(m * n, p) = div(m, p) * n) ∧ "+
			"(∀m n p:num. p ∣ n ⇒ div(m * n, p) = m * div(n, p))",
		func(ctx *Script, headline string) *GoalStackNode {
			// leftFactor — the bundle's first conjunct, and the whole argument.
			leftFactor := ctx.Lemma(Statement{
				Binders: "∀m n p:num.",
				Hypotheses: []string{
					"p ∣ m",
				},
				Conclusion: "div(m * n, p) = div(m, p) * n",
			},
				func(a *Argument) {
					// ↦ ∀m n p. (∃x. m = p · x) ⇒ nat_div(m·n, p) = nat_div(m, p)·n
					a.Do(Unfold(DividesFactor))

					m, n, p := a.FixAs[Nat](), a.FixAs[Nat](), a.FixAs[Nat]()
					factored := a.Assume()
					zero := a.Ctx().Nat(0)

					nonzero := a.Unless(
						Equal(p, zero),
						"a zero divisor settles the identity without the divisibility: both quotients are 0",
						Given(func(c *Argument, isZero Fact) {
							c.Show(
								"the convention sends both quotients to 0, and 0 annihilates the spare factor",
								By(
									isZero,
									nat_div_mod.DivZero.At(c.TermAs[Nat]("m * n")), // nat_div(m₀·n₀, 0) = 0
									nat_div_mod.DivZero.At(m),                      // nat_div(m₀, 0) = 0
									nat_arith.MulLeftZeroClause.At(n)))             // 0·n₀ = 0
						}))

					// m₀ = p₀·x₀
					x, factor := a.UnpackAs[Nat](factored)

					a.Show(
						"m₀·n₀ is p₀ taken x₀·n₀ times, so its quotient by p₀ is x₀·n₀ — and x₀ is m₀'s own quotient",
						By(
							Normalized,
							nonzero,
							factor,
							nat_arith.MulAssoc.At(p, x, n), // p₀·(x₀·n₀) = (p₀·x₀)·n₀ — regroup the copies
							nat_div_mod.DivMult.At(p, x),   // nat_div(p₀·x₀, p₀) = x₀
							nat_div_mod.DivMult.At(p, a.TermAs[Nat]("x * n")), // nat_div(p₀·(x₀·n₀), p₀) = x₀·n₀
						))
				})

			// rightFactor — the mirror conjunct. No new mathematics: the product
			// and the quotient sum both turn round, and leftFactor does the rest.
			// The divisibility is passed straight through, so this section never
			// opens the definition.
			rightFactor := ctx.Lemma(Statement{
				Binders: "∀m n p:num.",
				Hypotheses: []string{
					"p ∣ n",
				},
				Conclusion: "div(m * n, p) = m * div(n, p)",
			},
				func(a *Argument, m, n, p *Expr[Nat], div Fact) {
					a.Show(
						"leftFactor divides p₀ out of n₀ instead, and commutativity carries the result across",
						By(
							Normalized,
							div,
							At(leftFactor, n, m, p),   // nat_div(n₀·m₀, p₀) = nat_div(n₀, p₀)·m₀
							nat_arith.MulSym.At(m, n), // m₀·n₀ = n₀·m₀
							nat_arith.MulSym.At(a.TermAs[Nat]("div(n, p)"), m), // nat_div(n₀, p₀)·m₀ = m₀·nat_div(n₀, p₀)
						))
				})

			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(SplitConj(
						Case(
							"divide out of the left factor — this conjunct IS leftFactor",
							Cite(leftFactor)),
						Case(
							"divide out of the right factor — and that is rightFactor",
							Cite(rightFactor)),
					))
				})
		}),
})}

// DivSucIndicator — the quotient of n + 1 by d ≠ 0 is the quotient of n,
// plus one exactly when d divides n + 1. With n = q·d + r and r < d: if
// r + 1 < d then n + 1 = q·d + (r + 1) keeps the quotient q and leaves the
// nonzero remainder r + 1; otherwise r + 1 = d and n + 1 = (q + 1)·d.
var DivSucIndicator = divSucIndicatorThm{family.Add(registry.ProofEntry{
	Name: "DivSucIndicator",
	Key:  "prop_4f0face376afdef2",
	Build: family.Theorem(Statement{
		Binders: "∀n d:num.",
		Hypotheses: []string{
			"d ≠ 0",
		},
		Conclusion: "div(n + 1, d) = div(n, d) + COND(d ∣ n + 1, 1, 0)",
	}, func(a *Argument, n, d *Expr[Nat], nonzero Fact) {
		q := a.TermAs[Nat]("div(n, d)")
		next := a.TermAs[Nat]("n + 1")
		parts := a.Conjuncts(
			GroupPremises(nonzero, nat_div_mod.Division.At(n, d)),
			"n = q·d + r",
			"r < d")
		split, below := parts[0], parts[1]
		a.Cases(a.Term("rem(n, d) + 1 < d"))
		a.When(
			"r + 1 < d: the quotient stays q and the remainder becomes r + 1",
			func(b *Argument, grows Fact) {
				r1 := b.TermAs[Nat]("rem(n, d) + 1")
				shifted := b.Have(
					"n + 1 = q·d + (r + 1)",
					"n + 1 = div(n, d) * d + (rem(n, d) + 1)",
					ByArith(split))
				notDivides := b.Have(
					"d ∤ n + 1, its remainder r + 1 being nonzero",
					"¬(d ∣ n + 1)",
					ByArith(grows, shifted, nat_div_mod.ModUniq.At(next, d, q, r1), DividesMod.At(d, next)))
				b.Show(
					"div(n + 1, d) = q, and the indicator is 0",
					ByArith(notDivides, grows, shifted, nat_div_mod.DivUniq.At(next, d, q, r1)))
			})
		a.Otherwise(
			"r + 1 = d: n + 1 is exactly (q + 1)·d",
			func(b *Argument, full Fact) {
				exact := b.Have(
					"n + 1 = (q + 1)·d + 0",
					"n + 1 = (div(n, d) + 1) * d + 0",
					ByArith(full, below, split))
				b.Show(
					"div(n + 1, d) = q + 1, and d divides n + 1",
					ByArith(
						nonzero,
						exact,
						nat_div_mod.DivModUniq.At(next, d, b.TermAs[Nat]("div(n, d) + 1"), b.TermAs[Nat]("0")),
						DividesMod.At(d, next)))
			})
	}),
})}

// DivisorQuotient — a divisor d of a positive n and its quotient div(n, d)
// are positive, and their product is n: the remainder of n by d is 0.
var DivisorQuotient = divisorQuotientThm{family.Add(registry.ProofEntry{
	Name: "DivisorQuotient",
	Key:  "prop_ff2655a9f114c618",
	Build: family.Theorem(Statement{
		Binders:    "∀d n:num.",
		Hypotheses: []string{"0 < n", "d ∣ n"},
		Conclusion: "0 < d ∧ d * div(n, d) = n ∧ 0 < div(n, d)",
	}, func(arg *Argument, d, n *Expr[Nat], positive, divides Fact) {
		divisorPositive := arg.Have(
			"a divisor of a positive number is positive",
			"0 < d",
			ByArith(positive, divides, DividesLessEqStrong.At(d, n)))
		exact := arg.Have(
			"the remainder is zero, so the divisor and its quotient multiply to n",
			"d * div(n, d) = n",
			ByArith(divisorPositive, divides, DividesMod.At(d, n), nat_div_mod.Division.At(n, d)))
		arg.Show(
			"the quotient is positive since the product is",
			ByArith(positive, divisorPositive, exact, nat_arith.MulEqZero.At(d, arg.TermAs[Nat]("div(n, d)"))))
	}),
})}

// ---------------------------------------------------------------------------
// The multiple behind the relation, read as a theorem
// ---------------------------------------------------------------------------
//
// The elementary laws reach the multiple behind `d ∣ n` by unfolding the
// definition (the opening banner). A chapter that argues with
// divisibility without owning it cites the definition entry instead —
// `DividesFactor` (definitions.go), the relation read as the existence
// of its cofactor — and the three laws below, a divisor of one factor
// divides the product, a common nonzero factor cancels from both sides
// and a common factor multiplies into both, are written the way such a
// chapter writes, through it.

// DividesMul carries a divisor across a product: whatever divides one
// factor divides the whole. The cofactor simply picks up the other
// factor, and associativity is what regroups the three.
var DividesMul = dividesMulThm{family.Add(registry.ProofEntry{
	Name: "DividesMul",
	Key:  "prop_2fbe297e0eaecbd0",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n k:num.",
			Hypotheses: []string{
				"m ∣ n",
			},
			Conclusion: "m ∣ n * k",
		},
		func(a *Argument, m, n, k *Expr[Nat], div Fact) {
			product := a.TermAs[Nat]("n * k") // n₀·k₀

			x, factor := a.ObtainAs[Nat](
				"n is m taken x₀ times",
				"∃x:num. n = m * x",
				By(div, DividesFactor))

			a.Show(
				"so n₀·k₀ is m₀ taken x₀·k₀ times",
				By(
					factor,
					nat_arith.MulAssoc.At(m, x, k), // m₀·(x₀·k₀) = m₀·x₀·k₀
					DividesFactor.At(m, product)))  // m₀ ∣ n₀·k₀ ⇔ ∃x. n₀·k₀ = m₀·x
		}),
})}

// MulDividesLCancel cancels a factor common to both sides of a
// divisibility, and is the exact divisibility twin of nat_arith's
// MulEqLCancel — which is also what proves it, once the cofactor has
// been regrouped onto the divisor.
//
// The nonzero hypothesis is the same one the equation law carries, and
// for the same reason: everything divides 0·n.
var MulDividesLCancel = mulDividesLCancelThm{family.Add(registry.ProofEntry{
	Name: "MulDividesLCancel",
	Key:  "prop_1c6f7906f2ed2468",
	Build: family.Theorem(
		Statement{
			Binders: "∀c m n:num.",
			Hypotheses: []string{
				"c ≠ 0",
				"c * m ∣ c * n",
			},
			Conclusion: "m ∣ n",
		},
		func(a *Argument, c, m, n *Expr[Nat], hyp Fact) {
			x, factor := a.ObtainAs[Nat](
				"c·n is c·m taken x₀ times",
				"∃x:num. c * n = c * m * x",
				By(hyp, DividesFactor))

			a.Show(
				"regroup that cofactor onto m₀, and a nonzero c₀ cancels out "+
					"of the two sides — what is left is n₀ as a multiple of m₀",
				By(
					Normalized,
					hyp,
					factor,
					nat_arith.MulAssoc.At(c, m, x), // c₀·(m₀·x₀) = c₀·m₀·x₀
					nat_arith.MulEqLCancel.At(c, n, a.TermAs[Nat]("m * x")), // c₀·n₀ = c₀·(m₀·x₀) ⇔ c₀ = 0 ∨ n₀ = m₀·x₀
					DividesFactor.At(m, n))) // m₀ ∣ n₀ ⇔ ∃x. n₀ = m₀·x
		}),
})}

// MulDividesMulLeft — a common factor multiplies into both sides of a
// divisibility: n is m taken some number of times, and c·n is c·m taken as
// many.
var MulDividesMulLeft = mulDividesMulLeftThm{family.Add(registry.ProofEntry{
	Name: "MulDividesMulLeft",
	Key:  "prop_d26a89ea2f5b49b6",
	Build: family.Theorem(Statement{
		Binders: "∀c m n:num.",
		Hypotheses: []string{
			"m ∣ n",
		},
		Conclusion: "c * m ∣ c * n",
	}, func(a *Argument, c, m, n *Expr[Nat], divides Fact) {
		x, factor := a.ObtainAs[Nat](
			"n is m taken x times",
			"∃x:num. n = m * x",
			By(divides, DividesFactor.At(m, n)))
		a.Show(
			"so c·n is c·m taken x times",
			By(
				Normalized,
				factor,
				nat_arith.MulAssoc.At(c, m, x),
				DividesFactor.At(a.TermAs[Nat]("c * m"), a.TermAs[Nat]("c * n"))))
	}),
})}
