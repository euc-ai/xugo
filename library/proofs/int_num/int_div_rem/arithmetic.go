// arithmetic.go — the chapter, part two: division against the rest of ℤ's arithmetic.
//
// Six parts, marked by banners:
//
// - How a quotient sits in the order
// - How the division pair answers a change of sign
// - Dividing by a product, in two steps
// - Dividing by a fixed &2, and the chapter's one numeral tower
// - What an EXACT division is
// - The least common multiple, which is a quotient

package int_div_rem

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// How a quotient sits in the order
// ---------------------------------------------------------------------------
//
// Three questions: where does int_div(b, a) fall relative to a given c,
// what is its sign, and how large can it get. The first takes most of
// the file and the third is its first consumer — a bound on the SIZE of
// a quotient is a pair of bounds on the quotient, which is what the
// adjunction converts. Only the sign law stands apart, being about the
// embedding rather than the order, and it reads as a closing paragraph
// for that reason.
//
// # Division by a positive divisor, as an adjunction
//
// Fix a divisor a > &0. Dividing by a is adjoint to multiplying by it:
// int_div(b, a) is the LARGEST c for which a * c still fits under b, which
// is exactly
//
// 	a * c ≤ b ⇔ c ≤ int_div(b, a).
//
// Read left to right this says the quotient is an upper bound for such
// integers; read right to left, that it is one of them. Every statement
// down to `DivNonneg` is that one fact, wearing a different relation.
//
// The file carries four faces, and two moves generate them from one.
// Which side of int_div(b, a) a face bounds, and whether it bounds it
// strictly, are INDEPENDENT bits. Negating both sides flips them
// together, since `¬(u < v)` is `v ≤ u`; ℤ's discreteness,
// `x < y ⇔ x + &1 ≤ y`, flips only the second, at the cost of the
// correction c ↦ c + &1 — which is why half the faces mention it.
//
// `DivLessIff` is the display negated. `DivLessEqIff` is `DivLessIff`
// shifted, and `LessDivIff` is both. Each of those three is a single
// `Show`: the face it comes from, plus the one or two order rows that
// perform the move. Only the display's own member, `LessEqDivIff`,
// states the equivalence in the orientation shown above; the rest read
// it with int_div(b, a) on the left.
//
// The one real argument is `DivLessIff`'s, and it is about a window.
// The division algorithm places b in the half-open interval
//
// 	⟦int_div(b, a) * a, int_div(b, a) * a + a⟭
//
// — the multiple the quotient carries off never overshoots b, and one
// further step of a always would. That is nothing but the remainder
// bound &0 ≤ int_rem(b, a) < a, read as a position for b rather than as a
// fact about what is left over, once the identity
// int_div(b, a) * a + int_rem(b, a) = b is put beside it. The window's two ends
// are separate propositions and so separate claims below; what makes
// neither of them redundant is that the biconditional's two directions
// consume one end each.

// DivLessIff is the mirror of `LessEqDivIff`, this file's display, in
// strict form: a quotient falls short of c exactly when the dividend
// falls short of a * c — the display read through both negations. The
// split into two arms is not decoration: the directions consume
// opposite ends of the window
// that `int_div` picks out, and neither end proves the other's direction.
// ⇐ uses only that the quotient's multiple REACHES b (the remainder is
// not negative) and then cancels the positive a; ⇒ uses only that one
// further step of a OVERSHOOTS b (the remainder falls short of a), and
// then needs discreteness to know a whole such step is available.
var DivLessIff = divLessIffThm{family.Add(registry.ProofEntry{
	Name: "DivLessIff",
	Key:  "prop_29e942759f8aa92",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b c:int.",
			Hypotheses: []string{
				"&0 < a",
			},
			Conclusion: "div(b, a) < c ⇔ b < a * c",
		},
		func(arg *Argument, a, b, c Term, positive Fact) {
			v := ops(arg.Ctx())
			zero, one := v.Zero, v.One

			quot := v.IntDiv.Apply(b, a)      // int_div(b, a)
			rest := v.IntRem.Apply(b, a)      // int_rem(b, a)
			carried := v.Mul.Apply(quot, a)   // int_div(b, a) * a  — the window's near end
			beyond := v.Add.Apply(carried, a) // ... + a         — its far end
			next := v.Add.Apply(quot, one)    // int_div(b, a) + &1  — the next quotient up
			scaled := v.Mul.Apply(c, a)       // c * a

			// The headline says a * c while both scaling laws are stated on
			// the RIGHT factor. One commutation reconciles them, and both
			// arms need it.
			commuted := At(int_real_lift.MulSym, a, c) // a * c = c * a

			// The window, one end at a time. Both ends are the division
			// identity read against one half of the remainder bound.
			reaches := arg.Have(
				"what the quotient carries off never overshoots b, "+
					"since the remainder it leaves behind is not negative",
				MakeProp(v.Le.Apply(carried, b)),
				By(
					Normalized,
					positive,
					At(DivisionIdentity, b, a), // int_div(b, a) * a + int_rem(b, a) = b
					At(RemNonneg, b, a),        // a ≠ &0 ⇒ &0 ≤ int_rem(b, a)
					At(int_real_lift.NotEqualOfLessThan, zero, a), // &0 < a ⇒ &0 ≠ a
					// int_div(b, a) * a ≤ int_div(b, a) * a + int_rem(b, a) ⇔ &0 ≤ int_rem(b, a)
					At(int_real_lift.LessEqSelfAddRight, carried, rest)))

			overshoots := arg.Have(
				"but one further step of a does overshoot it, since the remainder falls short of the divisor",
				MakeProp(v.Lt.Apply(b, beyond)),
				By(
					Normalized,
					positive,
					At(DivisionIdentity, b, a), // int_div(b, a) * a + int_rem(b, a) = b
					At(RemBelowDivisor, b, a),  // &0 < a ⇒ int_rem(b, a) < a
					// int_div(b, a) * a + int_rem(b, a) < int_div(b, a) * a + a ⇔ int_rem(b, a) < a
					At(int_real_lift.LessThanAddLeft, carried, rest, a)))

			arg.Iff()
			arg.Forward(
				"a quotient under c leaves a whole further step to spare, and the far end is where that step lands",
				func(scale *Argument, underC Fact) {
					// Discreteness is the only place ℤ is used rather than an
					// ordered ring: over ℚ there would be no next quotient up.
					step := scale.Have(
						"between integers, below c means a whole step below it",
						MakeProp(v.Le.Apply(next, c)),
						By(underC, int_embed.Discrete))

					reached := scale.Have(
						"and a whole step of quotient is a whole a of "+
							"dividend, so the window's far end is itself under c * a",
						MakeProp(v.Le.Apply(beyond, scaled)),
						By(
							step,
							positive,
							// int_div(b, a) + &1 ≤ c and &0 ≤ a give (int_div(b, a) + &1) * a ≤ c * a
							At(int_real_lift.LessEqMulRight, next, c, a),
							At(int_real_lift.LessEqOfLessThan, zero, a), // &0 < a ⇒ &0 ≤ a
							// (int_div(b, a) + &1) * a = int_div(b, a) * a + &1 * a
							At(int_real_lift.RightDistrib, quot, one, a),
							int_real_lift.MulLeftIdentity))

					scale.Show(
						"b is under that far end, which is under c * a",
						By(
							Normalized,
							reached,
							overshoots,
							commuted,
							// b < int_div(b, a) * a + a ≤ c * a gives b < c * a
							At(int_real_lift.LessThanLessEqTrans, b, beyond, scaled)))
				})
			arg.Backward(
				"the near end already reaches b, so it too stays under "+
					"a * c — and a positive factor cancels off both sides",
				func(cancel *Argument, underMultiple Fact) {
					cancel.Show(
						"div(b, a) * a < c * a, and a is a positive right factor of both",
						By(
							Normalized,
							underMultiple,
							positive,
							reaches,
							commuted,
							// int_div(b, a) * a ≤ b and b < c * a give int_div(b, a) * a < c * a
							At(int_real_lift.LessEqLessThanTrans, carried, b, scaled),
							// &0 < a ⇒ (int_div(b, a) * a < c * a ⇔ int_div(b, a) < c)
							At(int_real_lift.LessThanMulRightEq, quot, c, a)))
				})
		}),
})}

// DivLessEqIff is the same face with the relations exchanged, and it
// needs no argument of its own: on ℤ a quotient is at most c exactly
// when it is below c + &1, so this IS `DivLessIff` one step up. The
// correction lands on the right-hand side as a * (c + &1), which is
// what makes the two statements look different when they are not.
var DivLessEqIff = divLessEqIffThm{family.Add(registry.ProofEntry{
	Name: "DivLessEqIff",
	Key:  "prop_81c3c66262339444",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b c:int.",
			Hypotheses: []string{
				"&0 < a",
			},
			Conclusion: "div(b, a) ≤ c ⇔ b < a * (c + &1)",
		},
		func(arg *Argument, a, b, c Term, positive Fact) {
			v := ops(arg.Ctx())
			one := v.One

			quot := v.IntDiv.Apply(b, a) // int_div(b, a)
			next := v.Add.Apply(c, one)  // c + &1 — the bound one step up

			arg.Show(
				"adding &1 to both sides of div(b, a) ≤ c makes it the "+
					"strict statement at c + &1, which is the previous face",
				By(
					positive,
					// int_div(b, a) ≤ c ⇔ int_div(b, a) + &1 ≤ c + &1
					At(int_real_lift.LessEqAddRight, quot, c, one),
					// int_div(b, a) + &1 ≤ c + &1 ⇔ int_div(b, a) < c + &1
					At(int_embed.Discrete, quot, next),
					// &0 < a ⇒ (int_div(b, a) < c + &1 ⇔ b < a * (c + &1))
					At(DivLessIff, a, b, next)))
		}),
})}

// LessEqDivIff is the adjunction itself, and the only one of the four
// faces written the way the word "adjoint" usually is: multiplying by a
// on one side of ≤, dividing by a on the other. It needs no argument.
// `DivLessIff` says when the quotient FAILS to reach c, and in a linear
// order failing to fall short is exactly reaching, so one negation on
// each side is the whole of it.
var LessEqDivIff = lessEqDivIffThm{family.Add(registry.ProofEntry{
	Name: "LessEqDivIff",
	Key:  "prop_e0acf5e9df8c90d0",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b c:int.",
			Hypotheses: []string{
				"&0 < a",
			},
			Conclusion: "c ≤ div(b, a) ⇔ a * c ≤ b",
		},
		func(arg *Argument, a, b, c Term, positive Fact) {
			v := ops(arg.Ctx())

			quot := v.IntDiv.Apply(b, a)  // int_div(b, a)
			multiple := v.Mul.Apply(a, c) // a * c — the multiple c would have to reach

			arg.Show(
				"negating both sides of the strict face turns each ¬(u < v) into "+
					"v ≤ u, which swaps the relation and the side div(b, a) sits on",
				By(
					Normalized,
					positive,
					// &0 < a ⇒ (int_div(b, a) < c ⇔ b < a * c)
					At(DivLessIff, a, b, c),
					// c ≤ int_div(b, a) ⇔ ¬(int_div(b, a) < c)
					At(int_real_lift.NotLessThan, quot, c),
					// a * c ≤ b ⇔ ¬(b < a * c)
					At(int_real_lift.NotLessThan, b, multiple)))
		}),
})}

// LessDivIff is the last face, and the only one citing the definitional
// equation `x < y ⇔ ¬(y ≤ x)` in BOTH polarities. That is a fact about
// rewriting rather than about the order: `DivLessEqIff` is mixed, `≤` on
// the quotient side and `<` on the dividend side, so negating it needs
// the same equation read each way round. It stands to `DivLessEqIff` as
// `LessEqDivIff` stands to `DivLessIff` — a pure negation, no
// discreteness — so the correction c ↦ c + &1 is inherited rather than
// derived again, on the multiple, the side `DivLessEqIff` carries it.
var LessDivIff = lessDivIffThm{family.Add(registry.ProofEntry{
	Name: "LessDivIff",
	Key:  "prop_bddef163d214e34f",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b c:int.",
			Hypotheses: []string{
				"&0 < a",
			},
			Conclusion: "c < div(b, a) ⇔ a * (c + &1) ≤ b",
		},
		func(arg *Argument, a, b, c Term, positive Fact) {
			v := ops(arg.Ctx())

			quot := v.IntDiv.Apply(b, a)     // int_div(b, a)
			next := v.Add.Apply(c, v.One)    // c + &1 — the bound one step up
			multiple := v.Mul.Apply(a, next) // a * (c + &1)

			arg.Show(
				"negating the weak face: ¬(u ≤ v) is v < u on the quotient, ¬(u "+
					"< v) is v ≤ u on the dividend — one equation, both polarities",
				By(
					positive,
					// &0 < a ⇒ (int_div(b, a) ≤ c ⇔ b < a * (c + &1))
					At(DivLessEqIff, a, b, c),
					// c < int_div(b, a) ⇔ ¬(int_div(b, a) ≤ c)
					At(int_real_lift.NotLessEq, quot, c),
					// a * (c + &1) ≤ b ⇔ ¬(b < a * (c + &1))
					At(int_real_lift.NotLessThan, b, multiple)))
		}),
})}

// DivNonneg is a sign law: a nonnegative dividend and a nonnegative
// divisor leave a nonnegative quotient.
//
// The argument runs through the embedding instead of the division
// algorithm. Pull `m` and `n` back along `&`, divide among the naturals,
// push the result forward — nothing is checked about the quotient itself,
// only about where it lives.
//
// `OfNumExists` carries both sign steps on its own, because it is an
// equivalence and both of its directions are wanted: read forwards it
// turns the two hypotheses into preimages, read backwards it turns the
// quotient's preimage into the sign asked for. A separate lemma putting
// `&`'s image above `&0` would be that second reading under another name,
// which is why none appears.
var DivNonneg = divNonnegThm{family.Add(registry.ProofEntry{
	Name: "DivNonneg",
	Key:  "prop_52b82d86e4a3dace",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:int.",
			Hypotheses: []string{
				"&0 ≤ m",
				"&0 ≤ n",
			},
			Conclusion: "&0 ≤ div(m, n)",
		},
		func(a *Argument, m, n Term, nonneg Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			embed := intvocab.Term(ctx, "int_of_num")
			// ℕ's own division, declared here rather than in `vocab.go`
			// because it belongs to the ℕ domain's table. The chapter's
			// alphabet is ℤ's and stops at `int_div`; `nat_div` enters at this one
			// site, so that the natural the quotient turns out to be the
			// image of can be named rather than merely asserted to exist.
			natDiv := ctx.Const("nat_div", MakeFun(NumType, MakeFun(NumType, NumType)))

			quotient := v.IntDiv.Apply(m, n)

			i, mImage := a.Obtain(
				"a nonnegative dividend is the image of a natural",
				"∃i:num. m₀ = &i",
				By(nonneg, int_embed.OfNumExists))

			j, nImage := a.Obtain(
				"and a nonnegative divisor is the image of one too",
				"∃j:num. n₀ = &j",
				By(nonneg, int_embed.OfNumExists))

			// Dividing the two preimages in ℕ and pushing the result forward
			// lands on the very quotient asked about, so it too is an image.
			quotImage := a.Have(
				"then so is the quotient, and div(i₀, j₀) is the natural it is the image of",
				MakeProp(quotient.Eq(embed.Apply(natDiv.Apply(i, j)))),
				By(Normalized, mImage, nImage, At(OfNumDiv, i, j))) // &(nat_div(i₀, j₀)) = int_div(&i₀, &j₀)

			a.Show(
				"and being an image is what being nonnegative means — the same equivalence, read the other way",
				By(
					Normalized,
					quotImage,
					At(int_embed.OfNumExists, quotient))) // (∃k. int_div(m₀, n₀) = &k) ⇔ &0 ≤ int_div(m₀, n₀)
		}),
})}

// DivNoLarger — dividing never makes a number bigger. Unlike the four
// faces above this asks nothing of the divisor: it holds at &0, where
// the convention answers &0 and no size falls below that, and at every
// other divisor because every other divisor has size &1 at least, and
// multiplying by such a factor can only carry a nonnegative quantity
// further from &0.
//
// That single scaling fact is the whole argument, spent twice. The
// adjunction turns `|int_div(m, n)| ≤ |m|` into a pair of bounds on the
// quotient, one on each side of &0, and each bound turns back into a
// statement about where a MULTIPLE of n sits relative to m: the
// quotient is at most |m| because m never reaches n·(|m| + &1), and at
// least -|m| because n·(-|m|) never reaches m. Both hold for the same
// reason and neither looks at m's sign, m being trapped between -|m|
// and |m| whatever that sign is.
//
// Only a POSITIVE divisor has an adjunction, so the sub-lemma assumes
// one and the top section supplies it: at a negative divisor it divides
// by -n instead, which `DivRightNeg` says changes only the quotient's
// sign — and a sign is exactly what the size does not see.
var DivNoLarger = divNoLargerThm{family.Add(registry.ProofEntry{
	Name: "DivNoLarger",
	Key:  "prop_d1e18bde505c6b24",
	Build: family.Sections(
		"∀m n:int. |div(m, n)| ≤ |m|",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zero, one := v.Zero, v.One

			// The bound where the adjunction is available. Both of its ends
			// come out of the same scaling, so they are proved side by side
			// and the size law puts them back together at the close.
			atPositive := ctx.Lemma(Statement{
				Binders: "∀m n:int.",
				Hypotheses: []string{
					"&0 < n",
				},
				Conclusion: "|div(m, n)| ≤ |m|",
			},
				func(a *Argument, m, n Term, positive Fact) {
					absM := v.Abs.Apply(m)         // |m|
					negAbsM := v.Neg.Apply(absM)   // -|m|
					room := v.Add.Apply(absM, one) // |m| + &1 — one past the size
					scaledSize := v.Mul.Apply(n, absM)
					quot := v.IntDiv.Apply(m, n)

					unit := a.Have(
						"a divisor above &0 is at least &1 — between integers there is no room for anything less",
						MakeProp(v.Le.Apply(one, n)),
						By(
							positive,
							At(int_embed.Discrete, zero, n), // &0 < n ⇔ &0 + &1 ≤ n
							int_real_lift.AddLeftIdentity))

					within := a.Have(
						"and m lies between the two ends of its own size, whichever sign it has",
						MakeProp(v.Le.Apply(negAbsM, m).And(v.Le.Apply(m, absM))),
						By(
							At(int_real_lift.AbsBounds, m, absM), // |m| ≤ |m| ⇔ -|m| ≤ m ∧ m ≤ |m|
							int_real_lift.LessEqRefl))

					// The one scaling fact this proof runs on, and it is spent
					// at both ends of the window: a factor of &1 or more only
					// carries a nonnegative quantity further from &0.
					carriedOut := func(label string, t Term, nonneg Fact) Fact {
						return a.Have(
							label,
							MakeProp(v.Le.Apply(t, v.Mul.Apply(n, t))),
							By(
								unit,
								nonneg,
								At(int_real_lift.LessEqMulRight, one, n, t), // &1 ≤ n ∧ &0 ≤ t ⇒ &1 * t ≤ n * t
								int_real_lift.MulLeftIdentity))
					}

					// The upper end: m stops short of |m| + &1, and scaling put
					// n·(|m| + &1) further out still.
					roomNonneg := a.Have(
						"|m| + &1 is nonnegative, both of its parts being so",
						MakeProp(v.Le.Apply(zero, room)),
						By(
							At(int_real_lift.AbsNonneg, m),          // &0 ≤ |m|
							int_real_lift.ZeroLessEqOne,             // &0 ≤ &1
							At(int_real_lift.AddNonneg, absM, one))) // &0 ≤ |m| ∧ &0 ≤ &1 ⇒ &0 ≤ |m| + &1

					roomCarried := carriedOut("scaling carries |m| + &1 out to n·(|m| + &1)", room, roomNonneg)

					short := a.Have(
						"m falls short of |m| + &1, being at or below |m| to start with",
						MakeProp(v.Lt.Apply(m, room)),
						By(
							within,
							At(int_real_lift.LessThanSelfAddRight, absM, one), // |m| < |m| + &1 ⇔ &0 < &1
							int_real_lift.ZeroLessThanOne,                     // &0 < &1
							// m ≤ |m| and |m| < |m| + &1 give m < |m| + &1
							At(int_real_lift.LessEqLessThanTrans, m, absM, room)))

					under := a.Have(
						"and so falls short of the scaled bound as well",
						MakeProp(v.Lt.Apply(m, v.Mul.Apply(n, room))),
						By(
							short,
							roomCarried,
							// |m| + &1 ≤ n·(|m| + &1) and m < |m| + &1 give m < n·(|m| + &1)
							At(int_real_lift.LessThanLessEqTrans, m, room, v.Mul.Apply(n, room))))

					upper := a.Have(
						"which is precisely the adjunction's condition for the quotient to stop at |m|",
						MakeProp(v.Le.Apply(quot, absM)),
						By(
							positive,
							under,
							// &0 < n ⇒ (int_div(m, n) ≤ |m| ⇔ m < n * (|m| + &1))
							At(DivLessEqIff, n, m, absM)))

					// The lower end: the same scaling, reflected. Carrying |m|
					// out and then negating carries -|m| in, and m was already
					// above -|m|.
					sizeCarried := carriedOut(
						"scaling carries |m| itself out to n·|m|", absM, At(int_real_lift.AbsNonneg, m))

					// The sign is pulled out of the product first, as a
					// rewrite: what is asked about is n·(-|m|), what the
					// scaling produced is -(n·|m|), and the order laws below
					// only ever speak of the second.
					pullSign := a.Have(
						"a sign inside the product is a sign outside it",
						MakeProp(v.Mul.Apply(n, negAbsM).Eq(v.Neg.Apply(scaledSize))),
						Cite(int_real_lift.MulRightNeg)) // bare: the claim above IS the row at (n, |m|)

					above := a.Have(
						"and n·(-|m|), which is that same -(n·|m|), sits at or below -|m| — which m in turn is above",
						MakeProp(v.Le.Apply(v.Mul.Apply(n, negAbsM), m)),
						pullSign.Rw(), // ↦ the goal becomes -(n·|m|) ≤ m
						By(
							sizeCarried,
							within,
							At(int_real_lift.LessEqNeg2, scaledSize, absM), // -(n·|m|) ≤ -|m| ⇔ |m| ≤ n·|m|
							// -(n·|m|) ≤ -|m| and -|m| ≤ m give -(n·|m|) ≤ m
							At(int_real_lift.LessEqTrans, v.Neg.Apply(scaledSize), negAbsM, m)))

					lower := a.Have(
						"which is the adjunction's condition for the quotient to stop at -|m| going the other way",
						MakeProp(v.Le.Apply(negAbsM, quot)),
						By(
							positive,
							above,
							// &0 < n ⇒ (-|m| ≤ int_div(m, n) ⇔ n * -|m| ≤ m)
							At(LessEqDivIff, n, m, negAbsM)))

					a.Show(
						"a quotient caught between -|m| and |m| has size at most |m| — "+
							"the two-sided reading again, now from the bounds back to the size",
						By(
							lower,
							upper,
							// |int_div(m, n)| ≤ |m| ⇔ -|m| ≤ int_div(m, n) ∧ int_div(m, n) ≤ |m|
							At(int_real_lift.AbsBounds, quot, absM)))
				})

			return ctx.Theorem(headline, func(a *Argument, m Term, n *TermWrapper) {
				negDivisor := v.Neg.Apply(n)
				quot := v.IntDiv.Apply(m, n)

				nonZero := a.Unless(
					n.Eq(zero),
					"n = &0: the convention fixes the quotient at &0, and no size falls below the size of &0",
					Given(func(z *Argument, isZero Fact) {
						z.Show(
							"|&0| is &0, which every absolute value is at or above",
							By(
								isZero,
								At(DivByZero, m),        // int_div(m, &0) = &0
								int_real_lift.AbsOfZero, // |&0| = &0
								int_real_lift.AbsNonneg))
					}))

				a.Cases(v.Lt.Apply(zero, n))
				a.When(
					"a positive divisor: the adjunction is available at this very pair",
					func(p *Argument, positive Fact) {
						p.Show(
							"so the sub-lemma is the claim",
							By(positive, At(atPositive, m, n)))
					})
				a.Otherwise(
					"a negative one: divide by -n instead — that changes "+
						"only the quotient's sign, and a size does not see a sign",
					func(g *Argument, notPositive Fact) {
						flipped := g.Have(
							"-n is the positive divisor this branch really has, n being neither &0 nor above it",
							MakeProp(v.Lt.Apply(zero, negDivisor)),
							By(nonZero, notPositive, At(int_real_lift.LessThanNegTotal, n))) // n = &0 ∨ &0 < n ∨ &0 < -n

						bounded := g.Have(
							"and by it the dividend is not made any bigger",
							MakeProp(v.Le.Apply(v.Abs.Apply(v.IntDiv.Apply(m, negDivisor)), v.Abs.Apply(m))),
							By(flipped, At(atPositive, m, negDivisor)))

						// What remains is not an argument but a change of
						// spelling, so it is run on the goal as one: the two
						// equations rewrite the quotient asked about into the
						// quotient just bounded.
						sizeBlind := g.Have(
							"a size does not see a sign",
							MakeProp(v.Abs.Apply(v.Neg.Apply(quot)).Eq(v.Abs.Apply(quot))),
							Cite(int_real_lift.AbsEven)) // bare: the claim IS the row at int_div(m, n)

						signOnly := g.Have(
							"and the divisor's sign reaches the quotient as nothing more than a sign",
							MakeProp(v.IntDiv.Apply(m, negDivisor).Eq(v.Neg.Apply(quot))),
							Cite(DivRightNeg)) // bare: the claim IS DivRightNeg at (m, n), read backwards

						g.Show(
							"so the two quotients are of one size, and the bound already proved is this one",
							sizeBlind.RwRev(), // ↦ |int_div(m, n)| ≤ |m| becomes |-int_div(m, n)| ≤ |m|
							signOnly.RwRev(),  // ↦ and that is |int_div(m, -n)| ≤ |m|
							By(bounded))       // which is the bound just proved
					})
			})
		}),
})}

// ---------------------------------------------------------------------------
// How the division pair answers a change of sign
// ---------------------------------------------------------------------------
//
// how the division pair answers a change of sign, and why the two sides of
// it are not the same problem.
//
// Negating the DIVISOR costs nothing. A decomposition `m = q·n + r`
// read against `-n` is `m = (-q)·(-n) + r`: the two sign changes cancel
// inside the product, so the remainder is not touched at all, and since
// `-n` has the same size as `n` that untouched remainder still falls in
// the interval the uniqueness demands. The pair `(-q, r)` therefore IS
// the decomposition by `-n`. The QUOTIENT law is read off the
// uniqueness there; the remainder law is then arithmetic off `remDiv`,
// which carries no guard and so needs no case analysis of its own.
//
// Negating the DIVIDEND is a different matter, and the difference is
// the whole reason this file has two halves. `-m = -(q·n + r)` is
// `(-q)·n - r`, and `-r` is not a legal remainder: remainders are never
// negative. So unless `r` is already `&0` the quotient has to absorb
// one further step of the divisor and hand `|n| - r` to the remainder
// — and WHICH WAY it steps depends on the sign of the divisor, since
// stepping is by `n` while the remainder bound is stated in `|n|`. That
// is why both left-hand laws carry a conditional where the right-hand
// pair does not — and why only the QUOTIENT one carries `int_sgn`. The
// remainder's correction is measured against `|n|` and so is
// sign-blind; the quotient's is a step by `n` and is not.
//
// The right-hand pair comes first below, then the left-hand pair, and
// last the two composites that negate both arguments at once. Negating
// both is negating each in turn, and taking the CHEAP one first leaves
// exactly the problem the left-hand pair already solved — so
// `RemBothNeg` is a two-step chain with nothing left to prove. The
// quotient composite is not quite free: one sign still has to be
// distributed over a conditional, and deciding an equality of two
// conditionals under one condition is a case analysis, which is why
// `DivBothNeg` carries this file's only refutation.
//
// The left-hand pair is one argument read twice, and the file is
// arranged to say so: `correctedPair` establishes that
//
// 	(-int_div(m, n) - int_sgn(n), |n| - int_rem(m, n))
//
// is an admissible decomposition of -m by n, and each member reads off
// the half of the uniqueness it is about. The exact case is shared the
// same way, through `negatedMultiple`. Both members split the zero
// divisor off first — there the convention answers outright and no
// decomposition exists to correct — and what remains is the genuine
// alternative the conditional names: the division came out even, or it
// did not.

// DivRightNeg — negating the divisor flips the quotient's sign. This is
// the member that does the strand's work: it exhibits the candidate
// pair, and `RemRightNeg` below is then a computation off it.
//
// The zero divisor is split off first, as everywhere else in the
// chapter, and here it is genuinely different mathematics: at `&0`
// there is no decomposition to compare, only the convention — and
// `-&0 = &0` is what makes the two sides of the equation speak about
// the same divisor. Splitting it also opens the nonzero-divisor guards
// on the division algorithm and on the uniqueness before either is put
// to work, which is what keeps the main branch to a single step.
var DivRightNeg = divRightNegThm{family.Add(registry.ProofEntry{
	Name: "DivRightNeg",
	Key:  "prop_c5bacaa766b775cd",
	Build: family.Theorem(
		"∀m n:int. div(m, -n) = -div(m, n)",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			zero := v.Zero
			negDivisor := v.Neg.Apply(n)
			quot, rest := v.IntDiv.Apply(m, n), v.IntRem.Apply(m, n)

			nonZero := a.Unless(
				n.Eq(zero),
				"n = &0: negating the zero divisor gives it back, so both sides "+
					"are the convention's own quotient — and &0 is its own negation too",
				Given(func(z *Argument, isZero Fact) {
					z.Show(
						"the convention at this branch's divisor, on both sides at once",
						By(
							isZero,
							At(DivByZero, m),       // int_div(m, &0) = &0
							int_real_lift.NegZero)) // -&0 = &0
				}))

			a.Show(
				"(-div(m, n), rem(m, n)) decomposes m by -n: the sign changes "+
					"cancel in the product, and -n leaves the remainder the same room",
				By(
					nonZero,
					// m = -int_div(m, n) * -n + int_rem(m, n) ∧ &0 ≤ int_rem(m, n) ∧ int_rem(m, n) < |-n| ⇒ int_div(m, -n) = -int_div(m, n)
					At(DivUnique, m, negDivisor, v.Neg.Apply(quot), rest),
					// n ≠ &0 ⇒ int_div(m, n) * n + int_rem(m, n) = m ∧ &0 ≤ int_rem(m, n) ∧ int_rem(m, n) < |n|
					At(DivisionAlgorithm, m, n),
					At(int_real_lift.MulNegNeg, quot, n), // -int_div(m, n) * -n = int_div(m, n) * n
					int_real_lift.AbsEven))
		}),
})}

// RemRightNeg — negating the divisor leaves the remainder alone. It is
// the chapter's usual second-of-a-pair: the quotient is known already,
// so the remainder is arithmetic off `remDiv`, which holds at every
// divisor and hands this member its zero case for free — no split, no
// guard, one equation chain.
var RemRightNeg = remRightNegThm{family.Add(registry.ProofEntry{
	Name: "RemRightNeg",
	Key:  "prop_75424cff302ae501",
	Build: family.Theorem(
		"∀m n:int. rem(m, -n) = rem(m, n)",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			negDivisor := v.Neg.Apply(n)
			quot := v.IntDiv.Apply(m, n)

			// The three waypoints between the two remainders: what -n takes
			// out of m, that amount with the quotient's sign made explicit,
			// and the same amount with both sign changes cancelled.
			takenByNeg := v.Sub.Apply(m, v.Mul.Apply(v.IntDiv.Apply(m, negDivisor), negDivisor))
			signsApart := v.Sub.Apply(m, v.Mul.Apply(v.Neg.Apply(quot), negDivisor))
			signsCancelled := v.Sub.Apply(m, v.Mul.Apply(quot, n))

			a.Do(CalcEq(
				Leg(
					takenByNeg,
					"what is left over is the dividend less what its own quotient carries off",
					Cite(remDiv)), // closes the leg: it IS remDiv at (m, -n)
				Leg(
					signsApart,
					"and that quotient is the quotient by n with its sign flipped",
					Cite(DivRightNeg)), // ↦ substitutes -int_div(m, n) for int_div(m, -n)
				Leg(
					signsCancelled,
					"so both sign changes now sit inside one product, where they cancel",
					Cite(int_real_lift.MulNegNeg)), // ↦ contracts -int_div(m, n) * -n to int_div(m, n) * n
				FinalLeg(
					"leaving precisely what n itself takes out of m",
					Cite(remDiv)), // closes the leg: it IS remDiv at (m, n), read backwards
			))
		}),
})}

// negatedMultiple — the exact case, shared. When nothing was left over
// the dividend IS int_div(m, n)·n, so negating it moves the sign onto the
// quotient and the product stays a product.
//
// It holds at EVERY divisor, the zero one included: `DivisionIdentity`
// carries no guard, and neither does the arithmetic done to it here.
func negatedMultiple(a *Argument, m, n Term, isExact Fact) Fact {
	v := ops(a.Ctx())
	quot := v.IntDiv.Apply(m, n)

	return a.Have(
		"with nothing left over the dividend is div(m, n)·n exactly, and -(div(m, n)·n) is (-div(m, n))·n",
		MakeProp(v.Neg.Apply(m).Eq(v.Mul.Apply(v.Neg.Apply(quot), n))),
		By(
			Normalized,
			isExact,
			At(DivisionIdentity, m, n), // int_div(m, n) * n + int_rem(m, n) = m
			// int_div(m, n) * n + &0 = int_div(m, n) * n
			At(int_real_lift.AddRightIdentity, v.Mul.Apply(quot, n)),
			// -int_div(m, n) * n = -(int_div(m, n) * n)
			At(int_real_lift.MulLeftNeg, quot, n)))
}

// correctedPair — the inexact case, shared. It returns the two premises
// the uniqueness asks for: the equation exhibiting
//
//	(-int_div(m, n) - int_sgn(n), |n| - int_rem(m, n))
//
// as a decomposition of -m by n, and the bound making its second
// component an admissible remainder.
//
// The equation is a ring identity and needs no divisor hypothesis — the
// division algorithm enters it only through `int_div`/`int_rem` naming the pair
// they name. The BOUND is where `n ≠ &0` and the branch hypothesis are
// spent, one on each side of the interval.
func correctedPair(a *Argument, m, n Term, nonZero, notExact Fact) (Fact, Fact) {
	v := ops(a.Ctx())
	zero := v.Zero
	quot, rest := v.IntDiv.Apply(m, n), v.IntRem.Apply(m, n)
	absN := v.Abs.Apply(n)
	carried := v.Mul.Apply(quot, n)                        // int_div(m, n) · n
	step := v.Sub.Apply(v.Neg.Apply(quot), v.Sgn.Apply(n)) // -int_div(m, n) - int_sgn(n)
	reflected := v.Sub.Apply(absN, rest)                   // |n| - int_rem(m, n)

	positive := a.Have(
		"a remainder that is not &0 is strictly positive, "+
			"the algorithm having already put it at or above &0",
		MakeProp(v.Lt.Apply(zero, rest)),
		By(
			nonZero,
			notExact,
			At(RemNonneg, m, n), // n ≠ &0 ⇒ &0 ≤ int_rem(m, n)
			// &0 < int_rem(m, n) ⇔ &0 ≤ int_rem(m, n) ∧ &0 ≠ int_rem(m, n)
			At(int_real_lift.LessThanSplit, zero, rest)))

	// The extra step costs the quotient int_sgn(n)·n, and that product IS
	// |n| — which is precisely what the reflected remainder hands back, so
	// the two corrections cancel and the sum is still -m.
	decomposes := a.Have(
		"the corrected pair still adds up to -m: the step "+
			"costs sgn(n)·n = |n|, and the reflection returns it",
		MakeProp(v.Neg.Apply(m).Eq(v.Add.Apply(v.Mul.Apply(step, n), reflected))),
		By(
			Normalized,
			// (-int_div(m, n) - int_sgn(n)) * n = (-int_div(m, n)) * n - int_sgn(n) * n
			At(int_real_lift.SubRightDistrib, v.Neg.Apply(quot), v.Sgn.Apply(n), n),
			At(int_real_lift.MulLeftNeg, quot, n), // -int_div(m, n) * n = -(int_div(m, n) * n)
			At(int_real_lift.SgnMulSelfIsAbs, n),  // int_sgn(n) * n = int_abs(n)
			// (-(int_div(m, n)·n) - |n|) + (|n| - int_rem(m, n)) = -(int_div(m, n)·n) - int_rem(m, n)
			At(int_real_lift.SubTriangle, v.Neg.Apply(carried), absN, rest),
			// -(int_div(m, n)·n + int_rem(m, n)) = -(int_div(m, n)·n) - int_rem(m, n)
			At(int_real_lift.SubLeftNeg, carried, rest),
			At(DivisionIdentity, m, n))) // int_div(m, n) * n + int_rem(m, n) = m

	// Reflecting about |n| exchanges the two ends of the interval, so the
	// bound that was strict becomes the weak one and vice versa.
	admissible := a.Have(
		"and reflecting a remainder about |n| lands inside ⟦&0, |n|⟭ again",
		MakeProp(v.Le.Apply(zero, reflected).And(v.Lt.Apply(reflected, absN))),
		By(
			nonZero,
			positive,
			// n ≠ &0 ⇒ … ∧ &0 ≤ int_rem(m, n) ∧ int_rem(m, n) < |n| — the upper half is what is wanted
			At(DivisionAlgorithm, m, n),
			// &0 ≤ |n| - int_rem(m, n) ⇔ int_rem(m, n) ≤ |n|
			At(int_real_lift.SubNonneg, absN, rest),
			// int_rem(m, n) < |n| ⇒ int_rem(m, n) ≤ |n|
			At(int_real_lift.LessEqOfLessThan, rest, absN),
			// |n| - int_rem(m, n) < |n| ⇔ |n| < |n| + int_rem(m, n)
			At(int_real_lift.LessThanSubAddRight, absN, rest, absN),
			int_real_lift.LessThanSelfAddRight))

	return decomposes, admissible
}

// RemLeftNeg — what a negated dividend leaves over. Nothing, if nothing
// was left over before; otherwise the remainder reflects about the
// divisor's size. The correction is measured against |n| and so does not
// depend on the divisor's sign — which is what separates this member
// from `DivLeftNeg` below.
var RemLeftNeg = remLeftNegThm{family.Add(registry.ProofEntry{
	Name: "RemLeftNeg",
	Key:  "prop_c133777f2b766863",
	// The conditional's `&0` arm is spelled unsugared. `&` takes its target
	// type from the surrounding context and a bare COND arm offers none; the
	// int-typed sibling arm does not reach across to pin it either, so the
	// branches would type as REAL and the equation be rejected. The
	// condition keeps `&0`, which `int_rem(m, n)` pins.
	Build: family.Theorem(
		"∀m n:int. rem(-m, n) = COND(rem(m, n) = &0, int_of_num(0), |n| - rem(m, n))",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			zero := v.Zero
			negM, rest := v.Neg.Apply(m), v.IntRem.Apply(m, n)
			step := v.Sub.Apply(v.Neg.Apply(v.IntDiv.Apply(m, n)), v.Sgn.Apply(n))
			reflected := v.Sub.Apply(v.Abs.Apply(n), rest)

			nonZero := a.Unless(
				n.Eq(zero),
				"n = &0: the convention leaves both dividends over whole, so the claim is about -m and m alone",
				Given(func(a *Argument, isZero Fact) {
					a.Show(
						"the second arm reads |&0| - m, which is &0 - m, "+
							"which is -m; and where m is &0 the first arm agrees",
						By(
							Normalized,
							isZero,
							At(RemByZero, negM),                 // int_rem(-m, &0) = -m
							At(RemByZero, m),                    // int_rem(m, &0) = m
							At(int_real_lift.AbsVanishes, zero), // |&0| = &0 ⇔ &0 = &0
							At(int_real_lift.SubLeftZero, m),    // &0 - m = -m
							int_real_lift.NegZero))              // -&0 = &0
				}))

			a.Cases(rest.Eq(zero))
			a.When(
				"the division came out even: -m is then an exact multiple of n, and a multiple leaves nothing over",
				func(a *Argument, isExact Fact) {
					multiple := negatedMultiple(a, m, n, isExact)

					// `RemMul` carries no divisor hypothesis — at a zero divisor
					// the product is itself &0 and the whole of it is left over,
					// which is nothing — so `nonZero` is not spent here.
					a.Show(
						"rem(-m, n) is what (-div(m, n))·n leaves over, and a product leaves its own factor nothing",
						By(Normalized, isExact, multiple, RemMul))
				})
			a.Otherwise(
				"something was left over: it reflects to |n| - rem(m, n), the arm this branch selects",
				func(a *Argument, notExact Fact) {
					decomposes, admissible := correctedPair(a, m, n, nonZero, notExact)

					a.Show(
						"the corrected pair decomposes -m and meets every condition, "+
							"so it IS the pair, and its remainder half is the claim",
						By(
							notExact,
							decomposes,
							admissible,
							// -m = q·n + r ∧ &0 ≤ r ∧ r < |n| ⇒ int_rem(-m, n) = r, at that pair
							At(RemUnique, negM, n, step, reflected)))
				})
		}),
})}

// DivLeftNeg — where a negated dividend's quotient lands. Sign-swapped
// when the division was exact; one step further when it was not, because
// the leftover has to be absorbed. `int_sgn(n)` is which way that step
// goes: towards zero for a positive divisor, away from it for a negative
// one, so that the corrected remainder stays nonnegative either way.
var DivLeftNeg = divLeftNegThm{family.Add(registry.ProofEntry{
	Name: "DivLeftNeg",
	Key:  "prop_a30ae973d9425031",
	// Both arms here are int-typed already — `int_div` and `int_sgn` pin them —
	// so unlike `RemLeftNeg` above this statement needs no unsugared `&0`.
	Build: family.Theorem(
		"∀m n:int. div(-m, n) = COND(rem(m, n) = &0, -div(m, n), -div(m, n) - sgn(n))",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			zero := v.Zero
			negM, rest := v.Neg.Apply(m), v.IntRem.Apply(m, n)
			step := v.Sub.Apply(v.Neg.Apply(v.IntDiv.Apply(m, n)), v.Sgn.Apply(n))
			reflected := v.Sub.Apply(v.Abs.Apply(n), rest)

			nonZero := a.Unless(
				n.Eq(zero),
				"n = &0: the convention fixes every quotient at &0, and both "+
					"arms evaluate to &0 — so the conditional is never decided",
				Given(func(a *Argument, isZero Fact) {
					a.Show(
						"-&0 is &0, and -&0 - int_sgn(&0) is &0 - &0, which is &0 again",
						By(
							isZero,
							At(DivByZero, negM),     // int_div(-m, &0) = &0
							At(DivByZero, m),        // int_div(m, &0) = &0
							int_real_lift.NegZero,   // -&0 = &0
							int_real_lift.SgnOfZero, // int_sgn(&0) = &0
							int_real_lift.SubRefl))
				}))

			a.Cases(rest.Eq(zero))
			a.When(
				"the division came out even: -m is an exact multiple of n, so the quotient only changes sign",
				func(a *Argument, isExact Fact) {
					multiple := negatedMultiple(a, m, n, isExact)

					// Unlike its remainder twin this branch does spend `nonZero`:
					// at a zero divisor the convention hands back &0 rather than
					// the surviving factor, which is `DivMul`'s own hypothesis.
					a.Show(
						"dividing (-div(m, n))·n by n returns the other factor, which is the arm this branch selects",
						By(Normalized, isExact, nonZero, multiple, DivMul))
				})
			a.Otherwise(
				"something was left over: absorbing it costs one step, and sgn(n) is which way the step goes",
				func(a *Argument, notExact Fact) {
					decomposes, admissible := correctedPair(a, m, n, nonZero, notExact)

					a.Show(
						"the corrected pair decomposes -m and meets every condition, "+
							"so it IS the pair, and its quotient half is the claim",
						By(
							notExact,
							decomposes,
							admissible,
							// -m = q·n + r ∧ &0 ≤ r ∧ r < |n| ⇒ int_div(-m, n) = q, at that pair
							At(DivUnique, negM, n, step, reflected)))
				})
		}),
})}

// RemBothNeg — what a doubly negated division leaves over. Its
// right-hand side is `RemLeftNeg`'s unchanged, and that is the whole
// content: the divisor's sign never reaches the remainder, so removing
// it leaves the left-hand law facing precisely the problem it already
// answered.
//
// The ORDER of the two steps is what keeps this to two legs, and to
// two deps. Removing the divisor's sign FIRST leaves a correction
// already stated in |n|; taken the other way round the correction would
// arrive stated in |-n| and need the absolute value's own sign law to
// be read back.
var RemBothNeg = remBothNegThm{family.Add(registry.ProofEntry{
	Name: "RemBothNeg",
	Key:  "prop_6d49caa28fede34c",
	Build: family.Theorem(
		"∀m n:int. rem(-m, -n) = COND(rem(m, n) = 0, int_of_num(0), |n| - rem(m, n))",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())

			a.Do(CalcEq(
				Leg(
					v.IntRem.Apply(v.Neg.Apply(m), n),
					"the divisor's sign goes first, because it never reached the remainder at all",
					Cite(RemRightNeg)), // closes the leg: it IS RemRightNeg at (-m, n)
				FinalLeg(
					"and what is left is a negated dividend at an untouched divisor, which is the left-hand law",
					Cite(RemLeftNeg)), // closes the leg: it IS RemLeftNeg at (m, n)
			))
		}),
})}

// DivBothNeg — where a doubly negated division's quotient lands. Read
// beside `DivLeftNeg` the only difference is the sign of the
// correction, `+ int_sgn(n)` here against `- int_sgn(n)` there, and
// that difference is one sign change applied to the whole conditional:
// the right-hand law hands the quotient a bare minus, and the last leg
// carries it into the two arms.
//
// The exact arm loses a double negation. The corrected arm is a
// difference, so the minus has to be folded through the subtraction
// before it can be cancelled the same way — one row, and the reason
// this member cites `int_real_lift.SubLeftNeg` where its remainder twin cites
// nothing at all.
var DivBothNeg = divBothNegThm{family.Add(registry.ProofEntry{
	Name: "DivBothNeg",
	Key:  "prop_de6d2becb50bb583",
	Build: family.Theorem(
		"∀m n:int. div(-m, -n) = COND(rem(m, n) = 0, div(m, n), div(m, n) + sgn(n))",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			quot := v.IntDiv.Apply(m, n)

			// `DivLeftNeg`'s own right-hand side, still standing under the
			// sign the right-hand law left outside it.
			negatedArms := v.Neg.Apply(Cond(
				v.IntRem.Apply(m, n).Eq(v.Zero),
				v.Neg.Apply(quot),
				v.Sub.Apply(v.Neg.Apply(quot), v.Sgn.Apply(n))))

			a.Do(CalcEq(
				Leg(
					v.Neg.Apply(v.IntDiv.Apply(v.Neg.Apply(m), n)),
					"the divisor's sign comes off the pair and reappears on the quotient",
					Cite(DivRightNeg)), // closes the leg: it IS DivRightNeg at (-m, n)
				Leg(
					negatedArms,
					"and underneath that sign stands the negated dividend's quotient, conditional and all",
					Cite(DivLeftNeg)), // closes the leg: it is DivLeftNeg at (m, n) under a common minus
				FinalLeg(
					"only the outer sign is left, and each arm answers it alike: "+
						"fold the difference into a sum, then cancel the double negation",
					By(
						Normalized,
						int_real_lift.SubLeftNeg, // -x - y = -(x + y), which the corrected arm needs first
						int_real_lift.NegNeg)),   // --x = x, which then finishes both arms
			))
		}),
})}

// ---------------------------------------------------------------------------
// Dividing by a product, in two steps
// ---------------------------------------------------------------------------
//
// Fix a nonnegative divisor n. There are two ways to take m apart by
// n · p: in one go, or by dividing by n first and then dividing the
// quotient by p. This section says they agree, and says it three times —
// once for what is left over, once for the quotient, and once for the
// digit in between.
//
// The two-step reading writes m in mixed radix, with places
//
// 	…, n · p, n, 1
//
// and three digits to read off: `int_rem(m, n)` at the units place,
// `int_rem(int_div(m, n), p)` at the n place, and `int_div(int_div(m, n), p)` carrying
// everything above. What n · p leaves over is then everything BELOW its
// own place, which is the middle digit weighted by n plus the low one:
//
// 	int_rem(m, n · p) = n · int_rem(int_div(m, n), p) + int_rem(m, n)
//
// `divRemByProductPair` proves the quotient and remainder formulas together.
// `RemByProduct` and `DivByProduct` read its two halves. `RemDivExchange`
// reads the middle digit back out by dividing the leftover by n.
//
// The pair meets the division algorithm's equation and two remainder bounds.
//
// The EQUATION is not a deduction but a regrouping, and it is separated
// out as the local `reassemble` lemma. Substituting a two-step
// decomposition into a one-step one has to move `int_div(int_div(m, n), p)`
// across a product, and the closer meets `int_div(int_div(m, n), p) · (n · p)`
// and `int_rem(int_div(m, n), p) · n` as unrelated opaque atoms — so no
// quantity of ring laws offered as PREMISES will identify them. Stated
// over plain variables instead, with the decomposition as a hypothesis,
// the substitution is one the closer makes freely. That is
// `reassemble`, and it is what makes the equation a one-liner at the
// point of use.
//
// Its own proof is then a change of spelling and is written as one. The
// mixed-radix reading puts each weight on the LEFT of what it weights,
// while the ring laws all multiply on the right; the commutations that
// reconcile them have to fire underneath another operation, so they are
// run on the goal as rewrites rather than offered as premises. That
// distinction recurs in this argument where an equation has to
// reach inside a product or a sum.
//
// The LOWER bound is a sum of nonnegatives.
//
// The UPPER bound is the one real estimate, and it is where a
// nonnegative divisor is finally needed: the middle digit is short of
// |p|, hence — between integers — a whole step short, and n scales that
// whole step into a whole n of room underneath n · |p|, which is room
// enough for the low digit because the low digit is short of n. A
// nonnegative n is also its own size, which is what turns n · |p| back
// into |n · p|.

// divRemByProductPair identifies the two-step quotient and the two lower
// mixed-radix digits together, by uniqueness of the division pair.
var divRemByProductPair = divRemByProductPairThm{family.Add(registry.ProofEntry{
	Name: "divRemByProductPair",
	Key:  "prop_9a016f0085cae218",
	Build: family.Sections(
		Statement{
			Binders: "∀m n p:int.",
			Hypotheses: []string{
				"&0 ≤ n",
			},
			Conclusion: "div(m, n * p) = div(div(m, n), p) ∧ rem(m, n * p) = n * rem(div(m, n), p) + rem(m, n)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zero, one := v.Zero, v.One

			// The regrouping, over plain variables and with no division in
			// it. `d` is a quantity already known to decompose by p; the
			// conclusion re-reads `d · n + r` as a decomposition by n · p.
			// Keeping `d` a VARIABLE is the whole point: at the point of
			// use it stands for int_div(m, n), and substituting that into a
			// product is what the closer will not do from an equation.
			reassemble := ctx.Lemma(Statement{
				Binders: "∀d e s r n p:int.",
				Hypotheses: []string{
					"d = e * p + s",
				},
				Conclusion: "d * n + r = e * (n * p) + (n * s + r)",
			},
				func(a *Argument, d, e, s, r, n, p Term, splits Fact) {
					// Both weights are written with n on the LEFT, that being
					// the side the mixed-radix reading puts it on, while every
					// law below multiplies on the right. The two commutations
					// are run on the GOAL rather than offered as premises:
					// each has to fire underneath another operation — one
					// inside e · _, one inside _ + r — which is a rewrite and
					// not something a premise list can ask for.
					weight := a.Have(
						"the place's weight, written the other way round",
						MakeProp(v.Mul.Apply(n, p).Eq(v.Mul.Apply(p, n))),
						Cite(int_real_lift.MulSym))

					scaled := a.Have(
						"and likewise the scaled digit",
						MakeProp(v.Mul.Apply(n, s).Eq(v.Mul.Apply(s, n))),
						Cite(int_real_lift.MulSym))

					// e's contribution is a multiple of the whole weight; the
					// laws below want it as a multiple of p, taken n at a time.
					// This too fires under e · _, so it joins the rewrites.
					regroup := a.Have(
						"and e's multiple of the weight is its multiple of p, taken n at a time",
						MakeProp(v.Mul.Apply(e, v.Mul.Apply(p, n)).Eq(v.Mul.Apply(v.Mul.Apply(e, p), n))),
						Cite(int_real_lift.MulAssoc))

					a.Show(
						"what is left is the split substituted for d and distributed, which is the claimed sum rebracketed",
						weight.Rw(),  // ↦ the goal's e * (n * p) becomes e * (p * n)
						scaled.Rw(),  // ↦ and its n * s becomes s * n
						regroup.Rw(), // ↦ and its e * (p * n) becomes e * p * n
						By(
							splits,
							// (e * p + s) * n = e * p * n + s * n
							At(int_real_lift.RightDistrib, v.Mul.Apply(e, p), s, n),
							// e * p * n + (s * n + r) = (e * p * n + s * n) + r
							At(int_real_lift.AddAssoc, v.Mul.Apply(v.Mul.Apply(e, p), n), v.Mul.Apply(s, n), r)))
				})

			return ctx.Theorem(headline, func(a *Argument, m, n, p *TermWrapper, nonneg Fact) {
				// The three digits, and the two composite quantities the
				// uniqueness is handed.
				quot, rest := v.IntDiv.Apply(m, n), v.IntRem.Apply(m, n) // int_div(m, n) and the units digit
				// int_div(int_div(m, n), p) — everything above n · p
				top := v.IntDiv.Apply(quot, p)
				// int_rem(int_div(m, n), p) — the digit at the n place
				middle := v.IntRem.Apply(quot, p)
				divisor := v.Mul.Apply(n, p)
				scaledMiddle := v.Mul.Apply(n, middle)
				below := v.Add.Apply(scaledMiddle, rest) // the claimed leftover

				nonZeroN := a.Unless(
					n.Eq(zero),
					"n = &0: both quotients vanish and both remainders are m",
					Given(func(z *Argument, isZero Fact) {
						z.Do(SplitConj(
							Case(
								"the first division by zero makes the iterated quotient zero",
								By(isZero, At(int_real_lift.MulLeftZero, p), At(DivByZero, m), ZeroDiv)),
							Case(
								"the middle digit has zero weight, leaving m",
								By(
									isZero,
									At(int_real_lift.MulLeftZero, p),
									At(int_real_lift.MulLeftZero, middle),
									At(RemByZero, m),
									int_real_lift.AddLeftIdentity))))
					}))

				nonZeroP := a.Unless(
					p.Eq(zero),
					"p = &0: the second division has zero quotient and leaves its dividend",
					Given(func(z *Argument, isZero Fact) {
						z.Do(SplitConj(
							Case(
								"both quotients are zero by the convention",
								By(isZero, At(int_real_lift.MulRightZero, n), DivByZero)),
							Case(
								"the two lower digits reassemble m by the division identity",
								By(
									Normalized,
									isZero,
									At(int_real_lift.MulSym, n, zero),
									At(int_real_lift.MulLeftZero, n),
									At(RemByZero, m),
									At(RemByZero, quot),
									At(DivisionIdentity, m, n),
									At(int_real_lift.MulSym, n, quot)))))
					}))

				positive := a.Have(
					"a nonzero divisor that is not negative is positive",
					MakeProp(v.Lt.Apply(zero, n)),
					By(nonneg, nonZeroN, At(int_real_lift.LessThanSplit, zero, n))) // &0 < n ⇔ &0 ≤ n ∧ &0 ≠ n

				// Condition one: the pair really does add up to m.
				decomposes := a.Have(
					"m is what the top digit carries off in units of n · p, plus the two digits below",
					MakeProp(m.Eq(v.Add.Apply(v.Mul.Apply(top, divisor), below))),
					By(
						At(DivisionIdentity, m, n), // int_div(m, n) * n + int_rem(m, n) = m
						// int_div(int_div(m, n), p) * p + int_rem(int_div(m, n), p) = int_div(m, n)
						At(DivisionIdentity, quot, p),
						// d = e * p + s ⇒ d * n + r = e * (n * p) + (n * s + r), at that split
						At(reassemble, quot, top, middle, rest, n, p)))

				// Condition two: it is not negative. The scaling law is used
				// twice, here at the bottom of the middle digit's range and
				// below at the top.
				weighted := a.Have(
					"the middle digit is not negative, and scaling by a nonnegative n cannot carry it below &0",
					MakeProp(v.Le.Apply(zero, scaledMiddle)),
					By(
						nonneg,
						nonZeroP,
						At(RemNonneg, quot, p), // p ≠ &0 ⇒ &0 ≤ int_rem(int_div(m, n), p)
						// &0 ≤ n ∧ &0 ≤ int_rem(…) ⇒ n * &0 ≤ n * int_rem(…)
						At(int_real_lift.LessEqMulLeft, n, zero, middle),
						At(int_real_lift.MulSym, n, zero), // n * &0 = &0 * n
						int_real_lift.MulLeftZero))

				notNegative := a.Have(
					"and neither is the low digit, so neither is their sum",
					MakeProp(v.Le.Apply(zero, below)),
					By(
						nonZeroN,
						weighted,
						At(RemNonneg, m, n), // n ≠ &0 ⇒ &0 ≤ int_rem(m, n)
						// &0 ≤ n * int_rem(…) ∧ &0 ≤ int_rem(m, n) ⇒ &0 ≤ their sum
						At(int_real_lift.AddNonneg, scaledMiddle, rest)))

				// Condition three, in four steps: what the divisor's size
				// is, how much room the middle digit leaves, how much that
				// room becomes once scaled, and that the low digit fits.
				sized := a.Have(
					"the product's size is n's own times p's — and a nonnegative n is its own size",
					MakeProp(v.Abs.Apply(divisor).Eq(v.Mul.Apply(n, v.Abs.Apply(p)))),
					By(
						Normalized,
						nonneg,
						At(int_real_lift.AbsMul, n, p),          // |n * p| = |n| * |p|
						At(int_real_lift.AbsFixedIffNonneg, n))) // |n| = n ⇔ &0 ≤ n

				stepShort := a.Have(
					"the middle digit falls short of |p|, so between integers it falls a whole step short",
					MakeProp(v.Le.Apply(v.Add.Apply(middle, one), v.Abs.Apply(p))),
					By(
						nonZeroP,
						At(DivisionAlgorithm, quot, p), // p ≠ &0 ⇒ … ∧ int_rem(int_div(m, n), p) < |p|
						int_embed.Discrete))

				roomBelow := a.Have(
					"scaled by n that whole step becomes a whole n of room under n · |p|",
					MakeProp(v.Le.Apply(v.Add.Apply(scaledMiddle, n), v.Mul.Apply(n, v.Abs.Apply(p)))),
					By(
						nonneg,
						stepShort,
						// &0 ≤ n ∧ int_rem(…) + &1 ≤ |p| ⇒ n * (int_rem(…) + &1) ≤ n * |p|
						At(int_real_lift.LessEqMulLeft, n, v.Add.Apply(middle, one), v.Abs.Apply(p)),
						// n * (int_rem(…) + &1) = n * int_rem(…) + n * &1
						At(int_real_lift.LeftDistrib, n, middle, one),
						int_real_lift.MulRightIdentity))

				fits := a.Have(
					"and the low digit fits in that room, being itself short of n",
					MakeProp(v.Lt.Apply(below, v.Abs.Apply(divisor))),
					By(
						positive,
						sized,
						roomBelow,
						At(RemBelowDivisor, m, n), // &0 < n ⇒ int_rem(m, n) < n
						// n * int_rem(…) + int_rem(m, n) < n * int_rem(…) + n ⇔ int_rem(m, n) < n
						At(int_real_lift.LessThanAddLeft, scaledMiddle, rest, n),
						// that, with the room above, gives the strict bound
						At(int_real_lift.LessThanLessEqTrans, below,
							v.Add.Apply(scaledMiddle, n), v.Mul.Apply(n, v.Abs.Apply(p)))))

				a.Show(
					"the pair meets all three conditions, so uniqueness identifies both quotient and remainder",
					By(decomposes, notNegative, fits, At(DivModUnique, m, divisor, top, below)))
			})
		}),
})}

// RemByProduct — the remainder is the sum of the two lower mixed-radix digits.
// Nonnegativity of n lets it scale the middle digit's bound without reversing
// the inequality, and identifies n with its absolute value.
var RemByProduct = remByProductThm{family.Add(registry.ProofEntry{
	Name: "RemByProduct",
	Key:  "prop_ae11332912775441",
	Build: family.Theorem(Statement{
		Binders:    "∀m n p:int.",
		Hypotheses: []string{"&0 ≤ n"},
		Conclusion: "rem(m, n * p) = n * rem(div(m, n), p) + rem(m, n)",
	}, func(a *Argument, m, n, p Term, nonneg Fact) {
		a.Show(
			"the remainder half of the product division pair",
			By(nonneg, At(divRemByProductPair, m, n, p)))
	}),
})}

// DivByProduct — division by a product is division by its factors in turn.
var DivByProduct = divByProductThm{family.Add(registry.ProofEntry{
	Name: "DivByProduct",
	Key:  "prop_2239d688c1e11db5",
	Build: family.Theorem(Statement{
		Binders:    "∀m n p:int.",
		Hypotheses: []string{"&0 ≤ n"},
		Conclusion: "div(m, n * p) = div(div(m, n), p)",
	}, func(a *Argument, m, n, p Term, nonneg Fact) {
		a.Show(
			"the quotient half of the product division pair",
			By(nonneg, At(divRemByProductPair, m, n, p)))
	}),
})}

// RemDivExchange — the middle digit read back out. Taking a remainder
// by p after dividing by n gives the same digit as dividing by n after
// taking a remainder by n · p, so the two operations may be exchanged.
//
// It is `RemByProduct` divided by n. What n · p leaves over is the
// middle digit's multiple of n plus the low digit; dividing that by n
// returns the multiple, because the low digit is too small to
// contribute another one. Nothing is asked of p: at p = &0 both sides
// are int_div(m, n), and the argument covers that case without noticing it.
var RemDivExchange = remDivExchangeThm{family.Add(registry.ProofEntry{
	Name: "RemDivExchange",
	Key:  "prop_758dd26d6ca9e415",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p:int.",
			Hypotheses: []string{
				"&0 ≤ n",
			},
			Conclusion: "rem(div(m, n), p) = div(rem(m, n * p), n)",
		},
		func(a *Argument, m Term, n *TermWrapper, p Term, nonneg Fact) {
			v := ops(a.Ctx())
			zero := v.Zero
			quot, rest := v.IntDiv.Apply(m, n), v.IntRem.Apply(m, n)
			middle := v.IntRem.Apply(quot, p) // int_rem(int_div(m, n), p) — the digit both sides name
			leftover := v.IntRem.Apply(m, v.Mul.Apply(n, p))

			nonZero := a.Unless(
				n.Eq(zero),
				"n = &0: the convention answers &0 for every quotient, so there is no digit to exchange",
				Given(func(z *Argument, isZero Fact) {
					z.Show(
						"dividing by &0 first leaves &0, which leaves nothing over "+
							"— and dividing by &0 last answers &0 whatever it is handed",
						By(
							isZero,
							DivByZero, // int_div(·, &0) = &0 — at m on the left, at the remainder on the right
							ZeroRem))
				}))

			// The mixed-radix reading writes the middle digit's weight on
			// the left, while the division law below reads a multiple of n
			// with n on the right. The one commutation between them has to
			// fire underneath the sum, so it is run on the goal.
			weightOrder := a.Have(
				"the weighted middle digit, with n on the side the division law reads it",
				MakeProp(v.Mul.Apply(middle, n).Eq(v.Mul.Apply(n, middle))),
				Cite(int_real_lift.MulSym))

			lowDigits := a.Have(
				"what n · p leaves over is that weighted digit, with the low digit riding on it",
				MakeProp(leftover.Eq(v.Add.Apply(v.Mul.Apply(middle, n), rest))),
				weightOrder.Rw(), // ↦ the claim's int_rem(…) * n becomes n * int_rem(…)
				By(
					nonneg,
					At(RemByProduct, m, n, p))) // int_rem(m, n * p) = n * int_rem(int_div(m, n), p) + int_rem(m, n)

			noFurther := a.Have(
				"and the low digit adds no further multiple of n, being nonnegative and short of n",
				MakeProp(v.IntDiv.Apply(rest, n).Eq(zero)),
				By(
					nonneg,
					nonZero,
					// (n ≠ &0 ⇒ &0 ≤ int_rem(m, n)) ∧ int_rem(m, n) < n ⇒ int_div(int_rem(m, n), n) = &0
					At(DivOfSmall, rest, n),
					At(RemNonneg, m, n),                       // n ≠ &0 ⇒ &0 ≤ int_rem(m, n)
					At(RemBelowDivisor, m, n),                 // &0 < n ⇒ int_rem(m, n) < n
					At(int_real_lift.LessThanSplit, zero, n))) // &0 < n ⇔ &0 ≤ n ∧ &0 ≠ n

			a.Show(
				"so dividing that leftover by n hands the middle digit straight "+
					"back: its multiple comes off as itself, and the low digit as nothing",
				By(
					nonZero,
					lowDigits,
					noFurther,
					// n ≠ &0 ⇒ int_div(int_rem(int_div(m, n), p) * n + int_rem(m, n), n) = int_rem(int_div(m, n), p) + int_div(int_rem(m, n), n)
					At(DivMulAdd, middle, n, rest),
					int_real_lift.AddRightIdentity))
		}),
})}

// ---------------------------------------------------------------------------
// Dividing by a fixed &2, and the chapter's one numeral tower
// ---------------------------------------------------------------------------
//
// Everywhere else this chapter divides by an arbitrary divisor and says
// what it can about the answer. Here the divisor is pinned at &2, and
// that single choice turns the remainder BOUND into a remainder LIST:
// the division algorithm puts int_rem(n, &2) in the half-open interval
// ⟦&0, &2⟭, and over ℤ that interval holds exactly two integers.
//
// What makes it exactly two is discreteness, `x < y ⇔ x + &1 ≤ y`, and
// the file spends it twice on the same remainder. Read downwards it
// turns `rem < &2` into `rem ≤ &1`; read upwards it turns `rem ≠ &0`
// into `&1 ≤ rem`. An integer meeting both is &1; one meeting only the
// first is &0. Over an ordered field neither reading survives and there
// is no such theorem. Discreteness is spent across the chapter, but
// this is the one place that reads it in BOTH directions against a
// single quantity.
//
// Why these two stand apart from the computation laws. It is not that
// the divisor is fixed — `DivByOne` and `RemByOne` are stated at &1 and
// live beside the rest. It is that these two reach a vocabulary nothing
// else here does (the ℕ numeral tower, below), and that they exhibit no
// candidate pair: `RemTwoCases` cites neither the uniqueness nor
// `remDiv`, so it is not a computation at all but a classification of
// what the remainder interval can hold.
//
// About the numeral. `&2` is a ℕ literal carried across the embedding,
// and a literal is opaque to the order laws — nothing in ℤ's
// ordered-ring theory knows how far &2 stands from &0. So the file
// SPENDS the numeral once, in `twoTakenApart`, and never looks at it
// again. Everything after that is ordered-ring algebra over &1, which
// is why the members about the number two rest on a single ℕ fact.
//
// # Parity as divisibility
//
// `TwoDividesIffRemZero` is where the file stops talking about `int_rem`
// and starts talking about `∣`, and everything after it is arithmetic
// of even and odd: a product, a difference, a power. Nothing in that
// half looks at the remainder interval again — it uses the two values
// only through that one bridge, and otherwise argues by exhibiting
// cofactors.
//
// Two shapes recur there and are worth naming in advance, because each
// member is one or the other and neither is about &2 in particular.
// EXHIBIT a cofactor and the number is even
// (`int_divides.DividesOwnMultiple` finishes it); or write one number
// as `q · &2 + r` and read another's remainder off it (`RemMulAdd`
// finishes it).

// twoTakenApart — the numeral &2, taken apart once: it is a sum of two
// units, and it stands strictly above &1.
//
// The sum comes out of ℕ's `2 = suc(1)` and the embedding's successor
// law; the bound is then one step of order algebra, since adding a
// unit to &1 moves it strictly up. The two conjuncts are one
// derivation spent two ways — `RemTwoCases` reads both, cancelling a
// unit under discreteness and placing the divisor above &0, while
// `TwoDividesPower` reads the bound alone.
//
// Internal, and unexported: it is the file's numeral bookkeeping, not
// a statement about `int_div` or `int_rem` at all.
var twoTakenApart = twoTakenApartThm{family.Add(registry.ProofEntry{
	Name: "twoTakenApart",
	Key:  "prop_d5e130345e2cf844",
	Build: family.Theorem(
		"2 = 1 + int_of_num(1) ∧ 1 < int_of_num(2)",
		func(a *Argument) {
			v := ops(a.Ctx())
			one := v.One
			two := a.Ctx().TermText("int_of_num(2)")

			unitSum := a.Have(
				"&2 is a sum of two units — ℕ's successor form of 2, carried across the embedding",
				MakeProp(two.Eq(v.Add.Apply(one, one))),
				By(
					int_embed.OfNumSuc, // & carries ℕ's successor to adding a unit
					nat_arith.Two))     // 2 = suc(1)

			a.Show(
				"and a sum adding a unit to &1 stands strictly above &1",
				By(
					unitSum,
					At(int_real_lift.LessThanSelfAddRight, one, one), // &1 < &1 + &1 ⇔ &0 < &1
					int_real_lift.ZeroLessThanOne))                   // &0 < &1
		}),
})}

// RemTwoCases — a remainder mod &2 is &0 or &1, with no third
// possibility.
//
// The two cases are asymmetric in effort, not in status: `rem = &0` is
// the disjunction's own left half and needs no argument at all, while
// `rem ≠ &0` is where the second reading of discreteness is spent and
// antisymmetry finishes.
var RemTwoCases = remTwoCasesThm{family.Add(registry.ProofEntry{
	Name: "RemTwoCases",
	Key:  "prop_627d7c43d91452a0",
	Build: family.Theorem(
		"∀n:int. rem(n, 2) = 0 ∨ rem(n, 2) = 1",
		func(a *Argument, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero, one := v.Zero, v.One
			two := ctx.TermText("int_of_num(2)") // the divisor, and the file's one literal
			rest := v.IntRem.Apply(n, two)       // int_rem(n, &2)

			positive := a.Have(
				"&2 is a positive divisor: it stands above &1, which is itself above &0",
				MakeProp(v.Lt.Apply(zero, two)),
				By(
					twoTakenApart,               // &1 < &2, among the pack
					int_real_lift.ZeroLessEqOne, // &0 ≤ &1
					// &0 ≤ &1 ∧ &1 < &2 ⇒ &0 < &2
					At(int_real_lift.LessEqLessThanTrans, zero, one, two)))

			lower := a.Have(
				"a remainder is never negative",
				MakeProp(v.Le.Apply(zero, rest)),
				By(
					positive,
					At(RemNonneg, n, two), // &2 ≠ &0 ⇒ &0 ≤ int_rem(n, &2)
					At(int_real_lift.NotEqualOfLessThan, zero, two))) // &0 < &2 ⇒ &0 ≠ &2

			upper := a.Have(
				"and it falls short of the divisor",
				MakeProp(v.Lt.Apply(rest, two)),
				By(positive, At(RemBelowDivisor, n, two))) // &0 < &2 ⇒ int_rem(n, &2) < &2

			// Discreteness read downwards. The unit it introduces on the left
			// is the one &1 + &1 has to spare, so it cancels.
			atMostOne := a.Have(
				"so the remainder is at most &1: below &1 + &1 means a whole unit below it",
				MakeProp(v.Le.Apply(rest, one)),
				By(
					upper,
					twoTakenApart, // &2 = &1 + &1, among the pack
					// int_rem(n, &2) < &2 ⇔ int_rem(n, &2) + &1 ≤ &2
					At(int_embed.Discrete, rest, two),
					// int_rem(n, &2) + &1 ≤ &1 + &1 ⇔ int_rem(n, &2) ≤ &1
					At(int_real_lift.LessEqAddRight, rest, one, one)))

			a.Cases(rest.Eq(zero))
			a.When(
				"rem(n, &2) = &0: this branch's hypothesis is the disjunction's own left half",
				TrivialNormalized())
			a.Otherwise(
				"rem(n, &2) ≠ &0: discreteness read upwards this time, and then a squeeze",
				func(b *Argument, nonZero Fact) {
					atLeastOne := b.Have(
						"a remainder that is neither negative nor &0 stands above "+
							"&0 — and between integers that already puts it at &1",
						MakeProp(v.Le.Apply(one, rest)),
						By(
							nonZero,
							lower,
							// &0 < int_rem(n, &2) ⇔ &0 ≤ int_rem(n, &2) ∧ &0 ≠ int_rem(n, &2)
							At(int_real_lift.LessThanSplit, zero, rest),
							// &0 < int_rem(n, &2) ⇔ &0 + &1 ≤ int_rem(n, &2)
							At(int_embed.Discrete, zero, rest),
							int_real_lift.AddLeftIdentity))

					b.Show(
						"at most &1 and at least &1 leaves only &1, which is the disjunction's right half",
						By(
							atLeastOne,
							atMostOne,
							// int_rem(n, &2) = &1 ⇔ int_rem(n, &2) ≤ &1 ∧ &1 ≤ int_rem(n, &2)
							At(int_real_lift.LessEqAntisym, rest, one)))
				})
		}),
})}

// RemTwoIff is `RemTwoCases` sharpened to a pair of biconditionals: not
// only is the remainder one of &0 and &1, each of the two is exactly
// the failure of the other. Exhaustiveness is what `RemTwoCases`
// already says; what turns it into an equivalence is that the two
// values are DISTINCT, and the order supplies that in one step.
var RemTwoIff = remTwoIffThm{family.Add(registry.ProofEntry{
	Name: "RemTwoIff",
	Key:  "prop_e1d04c1a33da84d7",
	Build: family.Theorem(
		"∀n:int. (rem(n, 2) ≠ 0 ⇔ rem(n, 2) = 1) ∧ (rem(n, 2) ≠ 1 ⇔ rem(n, 2) = 0)",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			zero, one := v.Zero, v.One

			a.Show(
				"&0 and &1 are distinct, so the two alternatives exclude each "+
					"other as well as exhaust — and each becomes the other's failure",
				By(
					At(RemTwoCases, n),                               // int_rem(n, &2) = &0 ∨ int_rem(n, &2) = &1
					int_real_lift.ZeroLessThanOne,                    // &0 < &1
					At(int_real_lift.NotEqualOfLessThan, zero, one))) // &0 < &1 ⇒ &0 ≠ &1
		}),
})}

// TwoDividesIffRemZero carries the two remainder values over to
// divisibility: an even integer is one the division by &2 comes out
// even on, and an odd one is one it leaves &1 on.
//
// It is where this file stops being about `int_rem` and starts being about
// `∣`, and it costs almost nothing to cross. The first half is
// `DividesIffRemZero` read at the divisor &2 and nothing else. The
// second half is that same equivalence composed with `RemTwoIff` —
// failing to be &0 IS being &1 here, because those are the only two
// values available.
//
// The two halves are argued separately rather than together: stated as
// one conjunction the first is an instance the goal already contains,
// so the premise closes it rather than installing, and the second half
// is then left with nothing to compose against.
var TwoDividesIffRemZero = twoDividesIffRemZeroThm{family.Add(registry.ProofEntry{
	Name: "TwoDividesIffRemZero",
	Key:  "prop_8a15136323efda77",
	Build: family.Theorem(
		"∀n:int. (rem(n, 2) = 0 ⇔ 2 ∣ n) ∧ (rem(n, 2) = 1 ⇔ ¬(2 ∣ n))",
		func(a *Argument, n Term) {
			two := a.Ctx().TermText("int_of_num(2)")

			a.Do(SplitConj(
				Case(
					"even: the division by &2 comes out even exactly when &2 divides",
					By(DividesIffRemZero)),

				Case(
					"odd: and the only other remainder is &1, so leaving &1 is failing to divide",
					By(
						At(DividesIffRemZero, n, two), // int_rem(n, &2) = &0 ⇔ &2 ∣ n
						// int_rem(n, &2) ≠ &0 ⇔ int_rem(n, &2) = &1, and its mirror
						At(RemTwoIff, n))),
			))
		}),
})}

// oddDecomposition — an odd integer is its own half doubled, with a
// unit left over.
//
// It is what knowing a number to be odd amounts to, and it is the
// division algorithm at the divisor &2 with the remainder already
// identified: `DivisionIdentity` writes any m as
// `int_div(m, &2) · &2 + int_rem(m, &2)`, and being odd is exactly
// `int_rem(m, &2) = &1`, so the general equation becomes this particular
// one with no further work.
//
// The even twin needs no member of its own — `DividesIffQuotientExact`
// already says `int_div(m, &2) · &2 = m` there — which is why only the odd
// case is named. Both write the even part as quotient TIMES divisor,
// the order this chapter states every division in.
var oddDecomposition = oddDecompositionThm{family.Add(registry.ProofEntry{
	Name: "oddDecomposition",
	Key:  "prop_1310027b7c8c245d",
	Build: family.Theorem(
		Statement{
			Binders: "∀m:int.",
			Hypotheses: []string{
				"¬(2 ∣ m)",
			},
			Conclusion: "m = div(m, 2) * 2 + 1",
		},
		func(a *Argument, m Term, odd Fact) {
			two := a.Ctx().TermText("int_of_num(2)")

			a.Show(
				"failing to divide by &2 pins the remainder at &1, "+
					"and the division algorithm then reads as claimed",
				By(
					odd,
					// int_rem(m, &2) = &1 ⇔ ¬(&2 ∣ m), and its even half
					At(TwoDividesIffRemZero, m),
					At(DivisionIdentity, m, two))) // int_div(m, &2) * &2 + int_rem(m, &2) = m
		}),
})}

// TwoDividesProduct — a product is even exactly when one of its
// factors is.
//
// The easy half is that an even factor carries: `d ∣ m` already gives
// `d ∣ m · n` for any divisor, so each disjunct is one citation and the
// two differ only by which way the product is written.
//
// The other half is the one real argument in this strand, and it is
// the statement that an odd number multiplies parity through
// unchanged. Write m as `q · &2 + &1`; then
//
//	m · n = (q · n) · &2 + n
//
// so m · n and n are the same dividend as far as division by &2 can
// tell, and `RemMulAdd` says exactly that — their remainders agree. An
// even product therefore has an even n. Note what this does NOT need:
// n's own decomposition never appears, because n is carried along
// whole rather than taken apart.
var TwoDividesProduct = twoDividesProductThm{family.Add(registry.ProofEntry{
	Name: "TwoDividesProduct",
	Key:  "prop_5249d48ba82556dc",
	Build: family.Theorem(
		"∀m n:int. 2 ∣ m * n ⇔ 2 ∣ m ∨ 2 ∣ n",
		func(a *Argument, m *TermWrapper, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := v.One
			two := ctx.TermText("int_of_num(2)")
			product := v.Mul.Apply(m, n)
			half := v.IntDiv.Apply(m, two)   // int_div(m, &2) — m's half, whatever m's parity
			multiple := v.Mul.Apply(half, n) // the quotient the product's own division by &2 turns out to have

			a.Do(SplitIff(
				Forward(
					"an odd m leaves n's parity alone, so an even product needs an even n",
					Given(func(b *Argument, evenProduct Fact) {
						odd := b.Unless(
							v.Divides.Apply(two, m),
							"&2 ∣ m: that is the disjunction's own left half, with nothing to prove",
							TrivialNormalized())

						oddM := b.Have(
							"m is odd, so it is its half doubled with a unit over",
							MakeProp(m.Eq(v.Add.Apply(v.Mul.Apply(half, two), one))),
							By(odd, At(oddDecomposition, m)))

						expand := b.Have(
							"multiplying that through by n leaves n itself over: the "+
								"product's own division by &2 has quotient div(m, &2) · n",
							MakeProp(product.Eq(v.Add.Apply(v.Mul.Apply(multiple, two), n))),
							By(
								Normalized,
								oddM,
								// (int_div(m, &2) * &2 + &1) * n = (int_div(m, &2) * &2) * n + &1 * n
								At(int_real_lift.RightDistrib, v.Mul.Apply(half, two), one, n),
								At(int_real_lift.MulAssoc, half, two, n), // int_div(m, &2) * (&2 * n) = (int_div(m, &2) * &2) * n
								At(int_real_lift.MulSym, two, n),         // &2 * n = n * &2
								At(int_real_lift.MulAssoc, half, n, two), // int_div(m, &2) * (n * &2) = (int_div(m, &2) * n) * &2
								At(int_real_lift.MulLeftIdentity, n)))    // &1 * n = n

						b.Show(
							"a dividend of that form leaves what n leaves, so the product and n are even together",
							By(
								evenProduct,
								expand,
								At(RemMulAdd, multiple, two, n), // int_rem((int_div(m, &2) * n) * &2 + n, &2) = int_rem(n, &2)
								// int_rem(n, &2) = &0 ⇔ &2 ∣ n, and its odd half
								At(TwoDividesIffRemZero, n),
								At(TwoDividesIffRemZero, product))) // and the same at the product
					})),

				Backward(
					"an even factor carries into the product, whichever of the two it is",
					Given(func(b *Argument, either Fact) {
						b.Show(
							"either way the even factor carries, the second "+
								"disjunct at the product written the other way round",
							By(
								either,
								At(int_divides.DividesProduct, two, m, n), // &2 ∣ m ⇒ &2 ∣ m * n
								At(int_divides.DividesProduct, two, n, m), // &2 ∣ n ⇒ &2 ∣ n * m
								At(int_real_lift.MulSym, n, m)))           // n * m = m * n
					})),
			))
		}),
})}

// TwoDividesDifference — two integers have the same parity exactly when
// their difference is even.
//
// Both halves are the same observation read in two directions: every
// number here is its half doubled plus its remainder, and the halves
// subtract cleanly. Going one way, equal remainders cancel out of the
// difference and leave `(int_div(m, &2) - int_div(n, &2)) · &2`. Going the
// other, an even difference and an even one of the two make the third
// number a multiple as well — `m` is `(m - n) + n` and `n` is
// `m - (m - n)`, each a sum or difference of two multiples of &2.
//
// So no case analysis on parity appears at all, and in particular the
// odd case is not argued separately: `DivisionIdentity` carries the
// remainder along as a term, and the only thing asked of it is that
// m's and n's agree.
var TwoDividesDifference = twoDividesDifferenceThm{family.Add(registry.ProofEntry{
	Name: "TwoDividesDifference",
	Key:  "prop_4c68057aeab47f2f",
	Build: family.Theorem(
		"∀m n:int. 2 ∣ m - n ⇔ (2 ∣ m ⇔ 2 ∣ n)",
		func(a *Argument, m, n *TermWrapper) {
			ctx := a.Ctx()
			v := ops(ctx)
			two := ctx.TermText("int_of_num(2)")
			difference := v.Sub.Apply(m, n)
			// the three halves the argument names, the two remainders that
			// ride along beside the first two, and each half doubled —
			// the even part of the number it came from
			halfM, halfN := v.IntDiv.Apply(m, two), v.IntDiv.Apply(n, two)
			halfDiff := v.IntDiv.Apply(difference, two)
			restM, restN := v.IntRem.Apply(m, two), v.IntRem.Apply(n, two)
			doubledM, doubledN := v.Mul.Apply(halfM, two), v.Mul.Apply(halfN, two)
			doubledDiff := v.Mul.Apply(halfDiff, two)

			a.Do(SplitIff(
				Forward(
					"an even difference makes each of the two even as soon as the other is",
					Given(func(b *Argument, evenDiff Fact) {
						b.Iff()
						b.Forward(
							"m even: n is m less the difference, so it is a difference of two multiples of &2",
							func(c *Argument, evenM Fact) {
								asMultiple := c.Have(
									"n is m less the difference, and each of those is &2 times its own half",
									MakeProp(n.Eq(v.Mul.Apply(v.Sub.Apply(halfM, halfDiff), two))),
									By(
										evenM,
										evenDiff,
										// int_div(m, &2) * &2 = m ⇔ &2 ∣ m, and its other factor order
										At(DividesIffQuotientExact, m, two),
										// int_div(m - n, &2) * &2 = m - n ⇔ &2 ∣ m - n, and its other factor order
										At(DividesIffQuotientExact, difference, two),
										// m - n = int_div(m - n, &2) * &2 ⇔ m = int_div(m - n, &2) * &2 + n
										At(int_real_lift.EqSubRightAdd, m, n, doubledDiff),
										// int_div(m, &2) * &2 - int_div(m - n, &2) * &2 = n ⇔ int_div(m, &2) * &2 = n + int_div(m - n, &2) * &2
										At(int_real_lift.EqSubRightAdd, doubledM, doubledDiff, n),
										// int_div(m - n, &2) * &2 + n = n + int_div(m - n, &2) * &2
										At(int_real_lift.AddSym, doubledDiff, n),
										int_real_lift.SubRightDistrib))

								c.Show(
									"so n is even too",
									By(
										Normalized,
										asMultiple,
										// &2 ∣ (int_div(m, &2) - int_div(m - n, &2)) * &2
										At(int_divides.DividesOwnMultiple, two, v.Sub.Apply(halfM, halfDiff))))
							})
						b.Backward(
							"n even: m is the difference plus n, so it is a sum of two multiples of &2",
							func(c *Argument, evenN Fact) {
								asMultiple := c.Have(
									"m is the difference plus n, and each of those is &2 times its own half",
									MakeProp(m.Eq(v.Mul.Apply(v.Add.Apply(halfDiff, halfN), two))),
									By(
										evenN,
										evenDiff,
										// int_div(n, &2) * &2 = n ⇔ &2 ∣ n, and its other factor order
										At(DividesIffQuotientExact, n, two),
										// int_div(m - n, &2) * &2 = m - n ⇔ &2 ∣ m - n, and its other factor order
										At(DividesIffQuotientExact, difference, two),
										// m - n = int_div(m - n, &2) * &2 ⇔ m = int_div(m - n, &2) * &2 + n
										At(int_real_lift.EqSubRightAdd, m, n, doubledDiff),
										// (int_div(m - n, &2) + int_div(n, &2)) * &2 = int_div(m - n, &2) * &2 + int_div(n, &2) * &2
										At(int_real_lift.RightDistrib, halfDiff, halfN, two)))

								c.Show(
									"so m is even too",
									By(
										Normalized,
										asMultiple,
										// &2 ∣ (int_div(m - n, &2) + int_div(n, &2)) * &2
										At(int_divides.DividesOwnMultiple, two, v.Add.Apply(halfDiff, halfN))))
							})
					})),

				Backward(
					"equal parities leave equal remainders, which then cancel out of the difference",
					Given(func(b *Argument, sameParity Fact) {
						sameRem := b.Have(
							"&0 and &1 are the only remainders available, so agreeing on evenness is agreeing outright",
							MakeProp(restM.Eq(restN)),
							By(
								Normalized,
								sameParity,
								At(TwoDividesIffRemZero, m),  // int_rem(m, &2) = &0 ⇔ &2 ∣ m, and its odd half
								At(TwoDividesIffRemZero, n))) // and the same at n

						asMultiple := b.Have(
							"so the difference is the two halves' difference, doubled",
							MakeProp(difference.Eq(v.Mul.Apply(v.Sub.Apply(halfM, halfN), two))),
							By(
								sameRem,
								At(DivisionIdentity, m, two), // int_div(m, &2) * &2 + int_rem(m, &2) = m
								At(DivisionIdentity, n, two), // and the same at n
								// (int_div(m, &2) * &2 + int_rem(m, &2)) - (int_div(n, &2) * &2 + int_rem(n, &2))
								// = (int_div(m, &2) * &2 - int_div(n, &2) * &2) + (int_rem(m, &2) - int_rem(n, &2))
								At(int_real_lift.SubAddPairwise, doubledM, restM, doubledN, restN),
								At(int_real_lift.SubEqZero, restM, restN), // int_rem(m, &2) - int_rem(n, &2) = &0 ⇔ the two agree
								// (int_div(m, &2) * &2 - int_div(n, &2) * &2) + &0 = int_div(m, &2) * &2 - int_div(n, &2) * &2
								At(int_real_lift.AddRightIdentity, v.Sub.Apply(doubledM, doubledN)),
								// (int_div(m, &2) - int_div(n, &2)) * &2 = int_div(m, &2) * &2 - int_div(n, &2) * &2
								At(int_real_lift.SubRightDistrib, halfM, halfN, two)))

						b.Show(
							"and a difference of that form is even",
							By(
								asMultiple,
								// &2 ∣ (int_div(m, &2) - int_div(n, &2)) * &2
								At(int_divides.DividesOwnMultiple, two, v.Sub.Apply(halfM, halfN))))
					})),
			))
		}),
})}

// TwoDividesPower — a power is even exactly when its base is and its
// exponent is not zero.
//
// The exponent is a NATURAL, so the induction is ℕ-structural and each
// step multiplies in one more copy of the base. That makes the step a
// single application of `TwoDividesProduct`: the power at `suc(k)` is
// the base times the power at `k`, so it is even when either factor is
// — and the induction hypothesis says the tail is even only when the
// base is, which is already covered by the other disjunct. The exponent
// condition takes care of itself, since `suc(k)` is never zero.
//
// The zero exponent is where the two sides come apart, and the whole of
// the base case is that they still agree: the empty product is &1, the
// right side fails on `0 ≠ 0`, and &1 is odd. The last of those is the
// one thing this file's earlier members do not already supply, and it
// is the bound `twoTakenApart` carries — &1 falls short of &2, so &2
// leaves it whole.
var TwoDividesPower = twoDividesPowerThm{family.Add(registry.ProofEntry{
	Name: "TwoDividesPower",
	Key:  "prop_46058ac4e34d3c4e",
	Build: family.Theorem(
		"∀n:int. ∀k:num. 2 ∣ int_pow(n, k) ⇔ 2 ∣ n ∧ k ≠ 0",
		func(a *Argument, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := v.One
			two := ctx.TermText("int_of_num(2)")
			// The exponent stays bound — it is what the induction runs on.
			// Stripping the leading `n` α-renames the binder it substitutes
			// under, so the goal spells it k₀; Binder takes the statement's
			// name and reads through the rename.
			k := a.Binder("k")

			a.Induct(k)
			a.Base(
				"no factors at all, and the empty product &1 is odd — which is "+
					"what the right side says too, its exponent condition failing at 0",
				func(b *Argument) {
					// The cite is split rather than handed over whole: the
					// closer would otherwise carry the pack's sum conjunct,
					// which this leaf never uses.
					belowTwo := b.Have(
						"&1 falls short of &2 — the bound half of `twoTakenApart`",
						MakeProp(v.Lt.Apply(one, two)),
						By(twoTakenApart))

					b.Show(
						"so &2 leaves &1 whole, and a remainder of &1 is exactly failing to divide",
						By(
							Normalized,
							belowTwo,
							// int_pow(n, 0) = &1. `PowClauses` packs the zero clause
							// together with the successor one, and only the zero
							// clause is wanted here, so the exponent slot is idle
							// and any term fills it.
							At(int_pow.PowClauses, n, ctx.Numeral(0)),
							// (&2 ≠ &0 ⇒ &0 ≤ &1) ∧ &1 < &2 ⇒ int_rem(&1, &2) = &1
							At(RemOfSmall, one, two),
							// int_rem(&1, &2) = &1 ⇔ ¬(&2 ∣ &1), and its even half
							At(TwoDividesIffRemZero, one),
							int_real_lift.ZeroLessEqOne)) // &0 ≤ &1
				})
			a.Step(
				"one more factor of n, and a product is even exactly when a "+
					"factor is — which for these two factors is the base either way",
				func(b *Argument, tail Fact) {
					b.Show(
						"either factor being even makes the power even, and the "+
							"hypothesis says the tail can only be even by the base being so",
						By(
							tail,
							// int_pow(n, suc(k)) = n * int_pow(n, k) — the pack's other clause
							At(int_pow.PowClauses, n, k),
							// &2 ∣ n * int_pow(n, k) ⇔ &2 ∣ n ∨ &2 ∣ int_pow(n, k)
							At(TwoDividesProduct, n, v.Pow.Apply(n, k)),
							At(peano.SucNotZero, k))) // suc(k) ≠ 0
				})
		}),
})}

// ---------------------------------------------------------------------------
// What an EXACT division is
// ---------------------------------------------------------------------------
//
// Everything below this file is about division in general: a dividend
// splits as a quotient times the divisor plus a remainder, and the
// remainder is what does not fit. Here the remainder is &0, and the
// three ways of saying so turn out to be one statement — `n` divides
// `m`, `int_rem(m, n)` vanishes, and `m` is exactly `n` times its own
// quotient.
//
// That identification is why divisibility is this chapter's material
// and not the ∣-chapter's. `int_num/int_divides` proves what can be
// proved about `∣` in ring vocabulary alone — the size and sign laws,
// gcd, Bézout — and sits below the division algorithm because
// `int_embed` reads its gcd specification. A theorem that mentions
// `int_div` or `int_rem` cannot live there, and does not want to: its content
// is a fact about the ALGORITHM.

// DividesIffRemZero — a division comes out even exactly when the
// divisor divides the dividend. It is the chapter's bridge to `∣`, and
// each direction uses a different half of the division algorithm.
//
// Left to right is the substantial one: a vanishing remainder makes the
// specification's equation `m = int_div(m,n)·n + int_rem(m,n)` read `m =
// int_div(m,n)·n`, which exhibits the quotient as the cofactor `∣` asks
// for. Right to left is a computation — a product of `n` with anything
// leaves nothing over `n`.
//
// No guard on `n`. At the zero divisor the convention is that the whole
// dividend is left over, so `int_rem(m, &0) = &0` says `m = &0`, and `&0`
// is exactly what `&0` divides.
var DividesIffRemZero = dividesIffRemZeroThm{family.Add(registry.ProofEntry{
	Name: "DividesIffRemZero",
	Key:  "prop_8b1933c2e596b35a",
	Build: family.Theorem("∀m n:int. rem(m, n) = &0 ⇔ n ∣ m",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			quotient := v.IntDiv.Apply(m, n)

			a.Iff()
			a.Forward(
				"a vanishing remainder leaves the specification's equation exhibiting the quotient as the cofactor",
				func(b *Argument, vanishes Fact) {
					b.Do(Unfold(int_divides.IntDividesDef))
					// The quotient IS the cofactor; that is the whole content.
					b.Take(quotient)
					// Normalized, for the same reason as the other arm: the
					// three equations have to be run into each other before
					// the closer sees them.
					b.Show(
						"what the specification leaves is the whole dividend, written as n times its quotient",
						By(
							Normalized,
							vanishes,
							At(DivisionIdentity, m, n), // int_div(m,n) * n + int_rem(m,n) = m
							At(int_real_lift.AddRightIdentity, v.Mul.Apply(quotient, n)), // … + &0 = …
							At(int_real_lift.MulSym, n, quotient)))                       // n * int_div(m,n) = int_div(m,n) * n
				})
			a.Backward(
				"what n divides is a multiple of n, and a multiple of n leaves nothing over it",
				func(b *Argument, divides Fact) {
					multiple := b.Have(
						"unfold the divisibility to the multiple it is defined to be",
						"∃k:int. m = n * k",
						Unfold(int_divides.IntDividesDef))
					cofactor, decomposes := b.Unpack(multiple) // m = n * k₀

					// Normalized — the cited pack carries both of its
					// conjuncts and the dividend has to be rewritten into
					// the product before they meet the closer; engine
					// shaping, not part of the argument.
					b.Show(
						"and n leaves nothing over any of its own multiples",
						By(Normalized, decomposes, At(RemMul, n, cofactor))) // int_rem(n * k₀, n) = &0
				})
		}),
})}

// DividesIffQuotientExact — the same fact read off the quotient rather
// than off the remainder: `n` divides `m` exactly when multiplying the
// quotient back recovers the dividend.
//
// It says more than it looks like it says. `int_div(m, n)` is TOTAL — every
// pair has a quotient, whether or not the division comes out even — so
// "the quotient multiplies back" is not a triviality but the condition
// under which the quotient loses nothing.
//
// It is stated in both factor orders, and the two are one
// statement: the second is the first commuted. Only the first is
// argued, and even there only one direction has content — reading the
// equation as the cofactor `∣` asks for is immediate, while producing
// it needs the remainder to vanish first, which is the member above.
var DividesIffQuotientExact = dividesIffQuotientExactThm{family.Add(registry.ProofEntry{
	Name: "DividesIffQuotientExact",
	Key:  "prop_17704d80ad718aa6",
	Build: family.Theorem(
		"∀m n:int. (n * div(m, n) = m ⇔ n ∣ m) ∧ (div(m, n) * n = m ⇔ n ∣ m)",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			quotient := v.IntDiv.Apply(m, n)

			exact := a.Have(
				"the divisor times the quotient recovers the dividend exactly when it divides it",
				"n * div(m, n) = m ⇔ n ∣ m",
				SplitIff(
					Forward(
						"the equation IS the cofactor, so exhibiting the quotient is the whole proof",
						Unfold(int_divides.IntDividesDef),
						Witness(quotient),
						TrivialNormalized()),

					Backward(
						"a divisor leaves no remainder, and the specification then has nothing but the product left",
						By(
							Normalized,
							ResidentHyp(a.Ctx().MakePropText("n₀ ∣ m₀")),
							At(DividesIffRemZero, m, n),                                  // int_rem(m,n) = &0 ⇔ n ∣ m
							At(DivisionIdentity, m, n),                                   // int_div(m,n) * n + int_rem(m,n) = m
							At(int_real_lift.AddRightIdentity, v.Mul.Apply(quotient, n)), // … + &0 = …
							At(int_real_lift.MulSym, n, quotient)))))                     // n * int_div(m,n) = int_div(m,n) * n

			a.Show(
				"and the commuted spelling is the same statement",
				By(Normalized, exact, At(int_real_lift.MulSym, n, quotient)))
		}),
})}

// DividesQuotient — once d divides n, dividing the quotient is the same
// as dividing n by the product: `e ∣ int_div(n,d) ⇔ d·e ∣ n`.
//
// It is the statement that division by a divisor loses nothing. Both
// directions rest on one equation — `d · int_div(n,d) = n`, which the
// hypothesis buys through the member above — and after that each is a
// reassociation: `d·(e·k)` and `(d·e)·k` are the same number, so a
// cofactor for one side is a cofactor for the other.
//
// The two directions are nonetheless not symmetric, and the asymmetry
// is where `int_div` being TOTAL shows through. Going up, the cofactor
// carries over untouched. Coming down, the shared factor `d` has to be
// cancelled — and at `d = &0` there is nothing to cancel, so that
// branch is settled by the convention instead: `int_div(n, &0)` is `&0`,
// which everything divides.
var DividesQuotient = dividesQuotientThm{family.Add(registry.ProofEntry{
	Name: "DividesQuotient",
	Key:  "prop_62ec71394ade3a13",
	Build: family.Theorem(Statement{
		Binders: "∀d n e:int.",
		Hypotheses: []string{
			"d ∣ n",
		},
		Conclusion: "e ∣ div(n, d) ⇔ d * e ∣ n",
	},
		// d arrives as a wrapper rather than a bare Term: the ⇒ branch
		// BUILDS the proposition d = &0 to split on, and Eq lives on the
		// wrapper.
		func(a *Argument, d *TermWrapper, n, e Term, divides Fact) {
			v := ops(a.Ctx())
			quotient := v.IntDiv.Apply(n, d)

			exact := a.Have(
				"a divisor's quotient multiplies back to the dividend",
				"d * div(n, d) = n",
				By(divides, At(DividesIffQuotientExact, n, d)))

			// Each arm names its hypothesis's unfolded form as a fact BEFORE
			// touching the goal's own `∣`: one DefExpand rewrites every
			// divisibility in sight, and a handle held across it loses track
			// of which hypothesis it became.
			a.Iff()
			a.Forward(
				"a cofactor of the quotient is a cofactor of n once d is folded back in",
				func(b *Argument, dividesQuotient Fact) {
					splitsQuotient := b.Have(
						"the quotient's own cofactor",
						"∃k:int. div(n, d) = e * k",
						Unfold(int_divides.IntDividesDef))
					k, splits := b.Unpack(splitsQuotient) // int_div(n, d) = e * k₀

					b.Do(Unfold(int_divides.IntDividesDef))
					b.Take(k)
					b.Show(
						"d · (e · k₀) regrouped is (d · e) · k₀, and d · div(n,d) is n",
						By(Normalized, splits, exact, At(int_real_lift.MulAssoc, d, e, k))) // d * (e * k₀) = d * e * k₀
				})
			a.Backward(
				"what divides n through the product also divides the quotient, once the shared d is cancelled",
				func(b *Argument, dividesProduct Fact) {
					splitsProduct := b.Have(
						"n's cofactor over the product",
						"∃k:int. n = d * e * k",
						Unfold(int_divides.IntDividesDef))
					k, splits := b.Unpack(splitsProduct) // n = (d * e) * k₀

					nonZero := b.Unless(
						d.Eq(v.Zero),
						"d = &0: the quotient is the convention's &0, and every integer divides &0",
						Given(func(c *Argument, isZero Fact) {
							c.Do(Unfold(int_divides.IntDividesDef))
							c.Take(v.Zero)
							c.Show(
								"&0 is what &0 divides, and e · &0 is &0",
								By(
									isZero,
									At(DivByZero, n), // int_div(n, &0) = &0
									int_real_lift.MulRightZero))
						}))

					b.Do(Unfold(int_divides.IntDividesDef))
					b.Take(k)
					b.Show(
						"both sides are d times something, and away from &0 that d cancels",
						By(
							Normalized,
							nonZero,
							splits,
							exact,
							At(int_real_lift.MulAssoc, d, e, k), // d * (e * k₀) = d * e * k₀
							// d * int_div(n,d) = d * (e * k₀) ⇔ d = &0 ∨ int_div(n,d) = e * k₀
							At(int_real_lift.MulLeftCancel, d, quotient, v.Mul.Apply(e, k))))
				})
		}),
})}

// QuotientDivides — the mirror of the member above, read the other way
// round: `int_div(n,d) ∣ e ⇔ n ∣ d·e`. Where that one asks what divides the
// quotient, this asks what the quotient divides.
//
// Its second hypothesis is the price of `int_div` being total. At `d = &0`
// the quotient is the convention's `&0`, which divides nothing but `&0`
// — while the right-hand side `n ∣ d·e` reads `&0 ∣ &0` and holds. The
// `n = &0 ⇒ e = &0` guard is exactly what closes that gap, and it is
// doing nothing anywhere else: away from the zero divisor the argument
// never looks at it.
//
// Everything else is the same two moves as above, in the same two
// directions. Going up is a regrouping. Coming down is the same
// regrouping plus a cancellation of the shared `d`.
var QuotientDivides = quotientDividesThm{family.Add(registry.ProofEntry{
	Name: "QuotientDivides",
	Key:  "prop_dfa7700494a99e9a",
	Build: family.Theorem(
		Statement{
			Binders: "∀d n e:int.",
			Hypotheses: []string{
				"d ∣ n",
				"n = &0 ⇒ e = &0",
			},
			Conclusion: "div(n, d) ∣ e ⇔ n ∣ d * e",
		},
		// The closure parameters follow the STATEMENT's binder order,
		// ∀d n e — a permutation here silently permutes every witness
		// tuple below. d is a wrapper because the ⇐ branch BUILDS d = &0
		// to split on.
		func(a *Argument, d *TermWrapper, n, e Term, hyps Fact) {
			v := ops(a.Ctx())
			quotient := v.IntDiv.Apply(n, d)

			exact := a.Have(
				"a divisor's quotient multiplies back to the dividend",
				"d * div(n, d) = n",
				By(hyps, At(DividesIffQuotientExact, n, d)))

			// The guard is pulled out here, before any unfolding: one
			// DefExpand rewrites every divisibility in sight, and the
			// conjunctive antecedent's handle does not survive it.
			guard := a.Have(
				"the degenerate case's guard, on its own",
				"n = &0 ⇒ e = &0",
				By(hyps))

			a.Iff()
			a.Forward(
				"a multiple of the quotient becomes a multiple of n once d is folded back in",
				func(b *Argument, quotientDivides Fact) {
					splitsE := b.Have(
						"e as a multiple of the quotient",
						"∃k:int. e = div(n, d) * k",
						Unfold(int_divides.IntDividesDef))
					k, splits := b.Unpack(splitsE) // e = int_div(n, d) * k₀

					b.Do(Unfold(int_divides.IntDividesDef))
					b.Take(k)
					b.Show(
						"d · (div(n,d) · k₀) regrouped is n · k₀",
						By(Normalized, splits, exact, At(int_real_lift.MulAssoc, d, quotient, k)))
				})
			a.Backward(
				"what n divides through d also divides the quotient, once the shared d is cancelled",
				func(b *Argument, dividesProduct Fact) {
					splitsProduct := b.Have(
						"d·e as a multiple of n",
						"∃k:int. d * e = n * k",
						Unfold(int_divides.IntDividesDef))
					k, splits := b.Unpack(splitsProduct) // d * e = n * k₀

					nonZero := b.Unless(
						d.Eq(v.Zero),
						"d = &0: the dividend is &0 too, so the guard forces e to be &0, which the &0 quotient divides",
						Given(func(c *Argument, isZero Fact) {
							// e is settled before the unfolding, from the guard and
							// the exact quotient as they stand.
							eZero := c.Have(
								"a &0 divisor makes the dividend &0, and the guard then makes e &0 too",
								"e = &0",
								By(isZero, guard, exact, int_real_lift.MulLeftZero))

							c.Do(Unfold(int_divides.IntDividesDef))
							c.Take(v.Zero)
							c.Show(
								"and &0 is the quotient taken &0 times",
								By(eZero, int_real_lift.MulRightZero))
						}))

					b.Do(Unfold(int_divides.IntDividesDef))
					b.Take(k)
					b.Show(
						"both sides are d times something, and away from &0 that d cancels",
						By(
							Normalized,
							nonZero,
							splits,
							exact,
							At(int_real_lift.MulAssoc, d, quotient, k), // d * (int_div(n,d) * k₀) = d * int_div(n,d) * k₀
							// d * e = d * (int_div(n,d) * k₀) ⇔ d = &0 ∨ e = int_div(n,d) * k₀
							At(int_real_lift.MulLeftCancel, d, e, v.Mul.Apply(quotient, k))))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The least common multiple, which is a quotient
// ---------------------------------------------------------------------------
//
// None of the five theorems this file exports mentions `int_div`, and the
// strand is nonetheless this chapter's, because `int_lcm` is DEFINED
// by a division. `lcmAsQuotient` opens the file by freeing that
// definition of its case split, and the first three members are then
// one sentence each about the quotient it leaves.
//
// The last two are about what the lcm DIVIDES, and there the quotient
// alone does not finish: `QuotientDivides` carries the question back to
// `m · n ∣ gcd · d`, and that is a fact about the gcd rather than about
// division — Bézout one way, cancelling the gcd the other. It is proved
// once, as `LcmDividesIffBoth`'s own first section, and the file's last
// member is that theorem repackaged as the phrase it earns: the lcm IS
// a least common multiple.
//
// Everything reached from outside the definition is the gcd's own
// specification — that it is nonnegative, that it divides each of the
// two arguments, and that Bézout reaches it — together with the one
// consequence drawn from it here, `gcdDividesSize`.
//
// One close below carries `Normalized`, where the vanishing product
// runs through `lcmAsQuotient`'s equation before the closer sees a
// clause. It is engine shaping, not part of the argument.

// lcmTerms are the terms `int_lcm`'s definition is written in, at one
// pair of integers. They are collected because `int_gcd` and `int_lcm`
// take their two arguments as ONE pair, so every mention of either has
// to build it first, and because every member below grounds the two
// shared entries over the same four.
type lcmTerms struct {
	pair    Term         // (m, n) — the single argument the two constants take
	product *TermWrapper // m * n
	size    Term         // |m * n| — the dividend the definition divides
	gcd     Term         // int_gcd((m, n)) — the divisor it divides by
}

// lcmAt builds those terms at one pair. A statement gets `(m, n)` from
// the text-DSL for free; a body has to build the pairing, which is what
// `pairs.PairAt` is for.
func lcmAt(ctx *Script, m, n Term) lcmTerms {
	v := ops(ctx)
	pair := pairs.PairAt(ctx, intType, intType).Apply(m, n)
	product := v.Mul.Apply(m, n)
	return lcmTerms{
		pair:    pair,
		product: product,
		size:    v.Abs.Apply(product),
		gcd:     v.IntGcd.Apply(pair),
	}
}

// lcmAsQuotient — the file's opening sentence: the lcm IS
// `int_div(|m · n|, gcd(m, n))`, with no case on the product.
//
// The definition guards that quotient,
//
//	lcm(m, n) = COND(m · n = &0, &0, int_div(|m · n|, gcd(m, n)))
//
// and the guard is redundant; saying so once is what this entry is.
// Where it fires, m · n is &0, so the dividend |m · n| is &0 too, and
// dividing &0 by anything gives &0 back — the very value the guard
// supplies. The two branches agree, and the COND goes.
//
// `pairs.Fst` and `pairs.Snd` are read here and nowhere else in the
// file, through pairs.Collapse: `int_lcm` is defined over the pair's PROJECTIONS, so
// unfolding it at a literal pair leaves `fst((m, n))` and `snd((m, n))`
// standing, and collapsing those is the definition's bookkeeping
// rather than any part of the argument.
//
// Internal, and unexported: every member below reads the lcm through
// this equation, but it is the definition with its case removed, not
// a law about `int_div` a reader would look up.
var lcmAsQuotient = lcmAsQuotientThm{family.Add(registry.ProofEntry{
	Name: "lcmAsQuotient",
	Key:  "prop_fb2605d7c06e90e7",
	Build: family.Theorem("∀m n:int. int_lcm((m, n)) = div(|m * n|, int_gcd((m, n)))",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()
			t := lcmAt(ctx, m, n)

			a.Show(
				"the zero guard is redundant — where it fires the dividend is &0, and &0 divided by anything is &0",
				Unfold(IntLcmDef),
				pairs.Collapse(ctx),
				// Comparing the two branches runs the guard's equation into
				// the size and the size's into the division.
				By(
					At(ZeroDiv, t.gcd),                        // int_div(&0, gcd((m, n))) = &0
					At(int_real_lift.AbsVanishes, t.product))) // |m · n| = &0 ⇔ m · n = &0
		}),
})}

// gcdDividesSize — the gcd of a pair divides the size of the pair's
// product: the one consequence of the gcd's specification this file
// draws for itself.
//
// Three links, one named citation each. The gcd divides m, by its own
// specification; a divisor of a factor divides the product; and a
// divisor does not see the sign of what it divides.
//
// Internal, and unexported: it is the exactness hypothesis the
// division laws below keep asking of the lcm's dividend, not a
// statement a reader would look up.
var gcdDividesSize = gcdDividesSizeThm{family.Add(registry.ProofEntry{
	Name: "gcdDividesSize",
	Key:  "prop_3cc662a1940817e8",
	Build: family.Theorem("∀m n:int. int_gcd((m, n)) ∣ |m * n|",
		func(a *Argument, m, n Term) {
			t := lcmAt(a.Ctx(), m, n)

			a.Show(
				"the gcd divides m, so it divides the product, so it divides the product's size",
				By(
					At(int_divides.IntGcdSpec, m, n),            // gcd((m, n)) ∣ m, among the rest of the specification
					At(int_divides.DividesProduct, t.gcd, m, n), // gcd((m, n)) ∣ m ⇒ gcd((m, n)) ∣ m · n
					int_divides.AbsDividend))
		}),
})}

// mulRegroup closes a leaf whose goal is a pure ×-rearrangement — the
// products the last two members shuffle.
//
// The rearrangement is derived from ℤ's associativity and commutativity
// as a kernel composition rather than searched for, so it costs no
// refutation and no cache key; the alternative is half a dozen ground
// `MulAssoc` instances handed to the closer, which is the same argument
// with the bookkeeping left in.
func mulRegroup(ctx *Script) Action {
	return ACRegroup(ctx.DepNormalized(int_real_lift.MulAssoc),
		ctx.DepNormalized(int_real_lift.MulSym))
}

// LcmNonneg — a least common multiple is never negative.
//
// Nothing about multiples is involved. The lcm is a size divided by a
// gcd, both of which are nonnegative by their own specifications, and
// `DivNonneg` says a quotient of nonnegatives is nonnegative.
var LcmNonneg = lcmNonnegThm{family.Add(registry.ProofEntry{
	Name: "LcmNonneg",
	Key:  "prop_3c74c34f4bcb5ec9",
	Build: family.Theorem("∀m n:int. &0 ≤ int_lcm((m, n))",
		func(a *Argument, m, n Term) {
			t := lcmAt(a.Ctx(), m, n)

			a.Show(
				"a size over a gcd: dividing one nonnegative by another leaves a nonnegative",
				By(
					At(lcmAsQuotient, m, n), // int_lcm((m, n)) = int_div(|m · n|, gcd((m, n)))
					// &0 ≤ |m · n| ∧ &0 ≤ gcd((m, n)) ⇒ &0 ≤ int_div(|m · n|, gcd((m, n)))
					At(DivNonneg, t.size, t.gcd),
					At(int_real_lift.AbsNonneg, t.product), // &0 ≤ |m · n|
					At(int_divides.IntGcdSpec, m, n)))      // &0 ≤ gcd((m, n)), among the rest of the specification
		}),
})}

// GcdTimesLcm — the gcd times the lcm is the size of the product.
//
// Read through the quotient the lcm is, the statement says that the
// gcd's quotient of |m · n| multiplies back to |m · n| — which is
// exactly what it means for the gcd to divide |m · n| exactly, and it
// does, because it divides m.
//
// The sizes are not decoration: `m · n` itself is recovered only up to
// sign, since the lcm is nonnegative and the product need not be.
var GcdTimesLcm = gcdTimesLcmThm{family.Add(registry.ProofEntry{
	Name: "GcdTimesLcm",
	Key:  "prop_c319690431ed5748",
	Build: family.Theorem("∀m n:int. int_gcd((m, n)) * int_lcm((m, n)) = |m * n|",
		func(a *Argument, m, n Term) {
			t := lcmAt(a.Ctx(), m, n)

			a.Show(
				"the lcm is the gcd's own quotient of |m · n|, and an "+
					"exact division is one whose quotient multiplies back",
				By(
					At(lcmAsQuotient, m, n),  // int_lcm((m, n)) = int_div(|m · n|, gcd((m, n)))
					At(gcdDividesSize, m, n), // gcd((m, n)) ∣ |m · n|
					// gcd((m, n)) · int_div(|m · n|, gcd((m, n))) = |m · n| ⇔ gcd((m, n)) ∣ |m · n|,
					// and its other factor order
					At(DividesIffQuotientExact, t.size, t.gcd)))
		}),
})}

// DividesLcmIff — what divides the lcm, and it is not what one first
// guesses: `d ∣ lcm(m, n)` is not `d ∣ m · n` but the weaker demand
// that `d` together with the gcd divide the product.
//
// The lcm is `|m · n|` divided by the gcd, and `DividesQuotient` says
// what happens to divisibility under such a division: dividing by a
// divisor loses nothing, so `d` divides the quotient exactly when the
// gcd and `d` together divide the dividend. That IS the statement, once
// the gcd's own divisibility of `|m · n|` is in hand — and sizes drop
// out on the right because a divisor does not see a sign.
var DividesLcmIff = dividesLcmIffThm{family.Add(registry.ProofEntry{
	Name: "DividesLcmIff",
	Key:  "prop_b1f663ee880f33d",
	Build: family.Theorem("∀d m n:int. d ∣ int_lcm((m, n)) ⇔ d * int_gcd((m, n)) ∣ m * n",
		func(a *Argument, d, m, n Term) {
			v := ops(a.Ctx())
			t := lcmAt(a.Ctx(), m, n)

			// The headline writes the compound divisor with `d` in front
			// while the division law produces it gcd-first. They are one
			// number, and the goal is put into the law's order here rather
			// than the equation being offered as a premise: a product is
			// opaque to the closer, which keeps the two orders apart as
			// distinct atoms.
			commuted := a.Have(
				"the compound divisor, in the order the division law produces it",
				MakeProp(v.Mul.Apply(d, t.gcd).Eq(v.Mul.Apply(t.gcd, d))),
				Cite(int_real_lift.MulSym)) // bare: the claim IS the row at (d, gcd((m, n)))
			a.Do(commuted.Rw()) // d · gcd((m, n)) ↦ gcd((m, n)) · d, in the goal

			a.Show(
				"dividing by a divisor loses nothing: what divides the "+
					"quotient is what divides the dividend through the gcd",
				By(
					At(lcmAsQuotient, m, n),  // int_lcm((m, n)) = int_div(|m · n|, gcd((m, n)))
					At(gcdDividesSize, m, n), // gcd((m, n)) ∣ |m · n|
					// gcd ∣ |m · n| ⇒ (d ∣ int_div(|m · n|, gcd) ⇔ gcd · d ∣ |m · n|)
					At(DividesQuotient, t.gcd, t.size, d),
					int_divides.AbsDividend))
		}),
})}

// LcmDividesIffBoth — the lcm's UNIVERSAL PROPERTY: what it divides is
// exactly what m and n both divide.
//
// Read it against `DividesLcmIff`, whose name differs from this one by
// word order alone: that member says what DIVIDES the lcm, this one
// says what the lcm DIVIDES, and the `…Both` is there so the two are
// told apart at a glance rather than at a second reading.
//
// Away from the degenerate product the lcm's own definition carries the
// question two steps and then hands it over. The lcm is |m · n| divided
// by the gcd, so what it divides is what |m · n| divides once the gcd
// is folded back into the divisor, and the size drops out because a
// divisor does not see a sign. What is left — `common` below — is not
// about division at all: it says that m · n divides gcd · d exactly
// when d is a common multiple, and it is the one genuine argument here.
//
// Where m · n IS &0 the lcm is &0 as well and both sides say d = &0,
// the right-hand one because a vanishing product leaves m or n at &0.
var LcmDividesIffBoth = lcmDividesIffBothThm{family.Add(registry.ProofEntry{
	Name: "LcmDividesIffBoth",
	Key:  "prop_f2c0d84fdb0d4c15",
	Build: family.Sections("∀m n d:int. int_lcm((m, n)) ∣ d ⇔ m ∣ d ∧ n ∣ d",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			mul := v.Mul.Apply

			// common — the arithmetic behind the lcm, with no `int_div` and
			// no `int_lcm` left in it: m · n divides gcd · d exactly when
			// d is a common multiple of m and n.
			//
			// Both directions turn on the gcd, and on nothing else. Down,
			// Bézout supplies coefficients; up, m and n each carry a copy
			// of the gcd that has to be cancelled — which is where the
			// nonvanishing product is spent, since at m · n = &0 the gcd
			// may be &0 and cancel nothing.
			common := ctx.Lemma(Statement{
				Binders: "∀m n d:int.",
				Hypotheses: []string{
					"m * n ≠ &0",
				},
				Conclusion: "m * n ∣ int_gcd((m, n)) * d ⇔ m ∣ d ∧ n ∣ d",
			},
				func(a *Argument, m, n, d Term, nonZero Fact) {
					t := lcmAt(ctx, m, n)

					a.Iff()
					a.Forward(
						"m·n carries the gcd twice and gcd·d carries it once, "+
							"so cancelling one copy leaves d a multiple of each",
						func(b *Argument) {
							b.Have(
								"the gcd divides each of m and n, by its own specification",
								"int_gcd((m, n)) ∣ m ∧ int_gcd((m, n)) ∣ n",
								By(At(int_divides.IntGcdSpec, m, n)))

							// One unfolding again, taking those two apart
							// alongside the hypothesis and the goal.
							b.Do(Unfold(int_divides.IntDividesDef))
							mp, mOverGcd := b.Unpack(b.Hyp("∃k:int. m = int_gcd((m, n)) * k"))        // m = gcd · mp
							np, nOverGcd := b.Unpack(b.Hyp("∃k:int. n = int_gcd((m, n)) * k"))        // n = gcd · np
							cof, splits := b.Unpack(b.Hyp("∃k:int. int_gcd((m, n)) * d = m * n * k")) // gcd · d = m·n · cof

							gcdNonZero := b.Have(
								"the gcd does not vanish — m is one of its multiples, and m·n does not vanish",
								"int_gcd((m, n)) ≠ &0",
								By(nonZero, mOverGcd, int_real_lift.MulLeftZero))

							// The two halves are one argument with m and n
							// exchanged: each cancels the copy of the gcd
							// that the OTHER factor contributes.
							b.Do(SplitConj(
								Case(
									"m ∣ d: n contributes the gcd, and m·(np·cof) is what survives the cancellation",
									Derive(func(c *Argument) {
										share := mul(m, mul(np, cof))
										regrouped := c.Have(
											"m·n·cof, with n written as the gcd's own multiple, is the gcd taken m·(np·cof) times",
											MakeProp(mul(mul(m, mul(t.gcd, np)), cof).Eq(mul(t.gcd, share))),
											mulRegroup(ctx))
										c.Take(mul(np, cof))
										c.Show(
											"and a gcd that does not vanish cancels",
											By(
												gcdNonZero,
												splits,
												nOverGcd,
												regrouped,
												// gcd·d = gcd·(m·(np·cof)) ⇔ gcd = &0 ∨ d = m·(np·cof)
												At(int_real_lift.MulLeftCancel, t.gcd, d, share)))
									})),

								Case(
									"n ∣ d: the mirror, with m contributing the gcd",
									Derive(func(c *Argument) {
										share := mul(n, mul(mp, cof))
										regrouped := c.Have(
											"m·n·cof, with m written as the gcd's own multiple, is the gcd taken n·(mp·cof) times",
											MakeProp(mul(mul(mul(t.gcd, mp), n), cof).Eq(mul(t.gcd, share))),
											mulRegroup(ctx))
										c.Take(mul(mp, cof))
										c.Show(
											"and the same cancellation finishes",
											By(
												gcdNonZero,
												splits,
												mOverGcd,
												regrouped,
												// gcd·d = gcd·(n·(mp·cof)) ⇔ gcd = &0 ∨ d = n·(mp·cof)
												At(int_real_lift.MulLeftCancel, t.gcd, d, share)))
									})),
							))
						})
					a.Backward(
						"Bézout writes the gcd as m·x + n·y, and each of the two halves of "+
							"gcd·d absorbs the decomposition of d that the OTHER factor supplies",
						func(b *Argument) {
							// One unfolding takes both hypotheses and the
							// goal apart together: `∣` IS the existence of
							// a cofactor, and this direction builds one out
							// of the two it is handed.
							b.Do(Unfold(int_divides.IntDividesDef))
							mCof, overM := b.Unpack(b.Hyp("∃k:int. d = m * k")) // d = m · mCof
							nCof, overN := b.Unpack(b.Hyp("∃k:int. d = n * k")) // d = n · nCof

							x, y, bezout := b.Obtain2(
								"the gcd is an integer combination of m and n — its specification says so",
								"∃x y:int. int_gcd((m, n)) = m * x + n * y",
								By(At(int_divides.IntGcdSpec, m, n)))

							xShare := b.Have(
								"the m·x half of gcd·d is a multiple of m·n — read ITS d through n",
								MakeProp(mul(mul(m, x), d).Eq(mul(t.product, mul(x, nCof)))),
								overN.Rw(),      // d ↦ n · nCof
								mulRegroup(ctx)) // (m·x)·(n·nCof) = (m·n)·(x·nCof)

							yShare := b.Have(
								"and the n·y half likewise, with ITS d read through m",
								MakeProp(mul(mul(n, y), d).Eq(mul(t.product, mul(y, mCof)))),
								overM.Rw(),      // d ↦ m · mCof
								mulRegroup(ctx)) // (n·y)·(m·mCof) = (m·n)·(y·mCof)

							b.Take(v.Add.Apply(mul(x, nCof), mul(y, mCof)))
							b.Show(
								"so gcd·d is m·n taken x·nCof + y·mCof times, and that sum is the cofactor asked for",
								By(
									bezout,
									xShare,
									yShare,
									// (m·x + n·y)·d = m·x·d + n·y·d
									At(int_real_lift.RightDistrib, mul(m, x), mul(n, y), d),
									// (m·n)·(x·nCof + y·mCof)
									// = (m·n)·(x·nCof) + (m·n)·(y·mCof)
									At(int_real_lift.LeftDistrib, t.product, mul(x, nCof), mul(y, mCof))))
						})
				})

			return ctx.Theorem(headline, func(a *Argument, m, n, d Term) {
				t := lcmAt(ctx, m, n)

				nonZero := a.Unless(
					t.product.Eq(v.Zero),
					"m · n = &0: the lcm vanishes with the product, and both sides then say d = &0",
					Given(func(b *Argument, isZero Fact) {
						lcmZero := b.Have(
							"where the product vanishes so does the lcm — it is &0 divided by the gcd",
							MakeProp(v.IntLcm.Apply(t.pair).Eq(v.Zero)),
							By(
								Normalized,
								isZero,
								At(lcmAsQuotient, m, n),                   // int_lcm((m, n)) = int_div(|m · n|, gcd((m, n)))
								At(ZeroDiv, t.gcd),                        // int_div(&0, gcd((m, n))) = &0
								At(int_real_lift.AbsVanishes, t.product))) // |m · n| = &0 ⇔ m · n = &0

						// The unfolding opens the three divisibilities, and
						// the equation puts &0 for the lcm in the first.
						b.Do(Unfold(int_divides.IntDividesDef), lcmZero.Rw())
						b.Show(
							"&0's multiples are &0 alone, and a vanishing product "+
								"leaves m or n at &0 — whose multiples are &0 too",
							By(
								isZero,
								At(int_real_lift.MulEqZero, m, n), // m · n = &0 ⇔ m = &0 ∨ n = &0
								// Both stay unground: which factor vanishes and
								// which cofactor witnesses it is what this leaf
								// is deciding.
								int_real_lift.MulLeftZero,   // &0 · x = &0
								int_real_lift.MulRightZero)) // x · &0 = &0
					}))

				guard := a.Have(
					"away from &0 the size cannot vanish either, so "+
						"the quotient law's degenerate guard is vacuous here",
					"|m * n| = &0 ⇒ d = &0",
					By(nonZero, int_real_lift.AbsVanishes))

				a.Show(
					"dividing by a divisor loses nothing, so what the quotient divides is "+
						"what |m·n| divides through the gcd — a common multiple, by `common`",
					By(
						guard,
						nonZero,
						At(lcmAsQuotient, m, n),  // int_lcm((m, n)) = int_div(|m · n|, gcd((m, n)))
						At(gcdDividesSize, m, n), // gcd((m, n)) ∣ |m · n|
						// gcd ∣ |m·n| ∧ (|m·n| = &0 ⇒ d = &0) ⇒
						// (int_div(|m·n|, gcd) ∣ d ⇔ |m·n| ∣ gcd·d)
						At(QuotientDivides, t.gcd, t.size, d),
						// m·n ∣ gcd·d ⇔ |m·n| ∣ gcd·d
						At(int_divides.AbsDivisor, t.product, mul(t.gcd, d)),
						// m·n ≠ &0 ⇒ (m·n ∣ gcd·d ⇔ m ∣ d ∧ n ∣ d)
						At(common, m, n, d)))
			})
		}),
})}

// LcmIsLeastCommonMultiple — the phrase `int_lcm` is named for, proved:
// it is a common multiple of m and n, and it divides every common
// multiple. That is what makes it LEAST, and it is the last thing the
// definition owes the name.
//
// Nothing new is argued here. The third conjunct is
// `LcmDividesIffBoth` read right to left. The first two are
// `DividesLcmIff` at d := m and again at d := n, which trades each for
// a statement about the product alone — and there the gcd the OTHER
// factor carries is exactly the cofactor wanted, one rearrangement
// each.
var LcmIsLeastCommonMultiple = lcmIsLeastCommonMultipleThm{family.Add(registry.ProofEntry{
	Name: "LcmIsLeastCommonMultiple",
	Key:  "prop_dcfb7c0308d92a21",
	Build: family.Theorem(
		"∀m n:int. "+
			"    m ∣ int_lcm((m, n)) ∧ n ∣ int_lcm((m, n)) ∧ (∀d:int. m ∣ d ∧ n ∣ d ⇒ int_lcm((m, n)) ∣ d)",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			mul := v.Mul.Apply
			t := lcmAt(ctx, m, n)

			// Each of the two product facts is argued inside its own
			// claim rather than out here, because unfolding `∣` rewrites
			// every divisibility in sight — including the three the
			// headline is made of.
			mSide := a.Have(
				"m·gcd divides m·n: the gcd that n carries is the cofactor it is short of",
				"m * int_gcd((m, n)) ∣ m * n",
				Derive(func(b *Argument) {
					b.Have(
						"the gcd divides n, by its own specification",
						"int_gcd((m, n)) ∣ n",
						By(At(int_divides.IntGcdSpec, m, n)))

					b.Do(Unfold(int_divides.IntDividesDef))
					np, nOverGcd := b.Unpack(b.Hyp("∃k:int. n = int_gcd((m, n)) * k")) // n = gcd · np
					b.Take(np)
					b.Show(
						"and m·(gcd·np) re-associated is (m·gcd)·np",
						By(nOverGcd, At(int_real_lift.MulAssoc, m, t.gcd, np))) // m·(gcd·np) = (m·gcd)·np
				}))

			nSide := a.Have(
				"n·gcd divides m·n: the mirror, with m carrying the gcd",
				"n * int_gcd((m, n)) ∣ m * n",
				Derive(func(b *Argument) {
					b.Have(
						"the gcd divides m, by its own specification",
						"int_gcd((m, n)) ∣ m",
						By(At(int_divides.IntGcdSpec, m, n)))

					b.Do(Unfold(int_divides.IntDividesDef))
					mp, mOverGcd := b.Unpack(b.Hyp("∃k:int. m = int_gcd((m, n)) * k")) // m = gcd · mp
					// A shuffle rather than a re-association this time: the
					// gcd has to cross n to join it on the left.
					regrouped := b.Have(
						"(gcd·mp)·n rearranged is (n·gcd)·mp",
						MakeProp(mul(mul(t.gcd, mp), n).Eq(mul(mul(n, t.gcd), mp))),
						mulRegroup(ctx))
					b.Take(mp)
					b.Show(
						"which is m·n once m is read back as the gcd's multiple",
						By(mOverGcd, regrouped))
				}))

			a.Do(SplitConjAll(
				Case(
					"m divides the lcm, because m·gcd divides m·n",
					By(mSide, DividesLcmIff)),

				Case(
					"n divides the lcm, for the mirror reason",
					By(nSide, DividesLcmIff)),

				Case(
					"and it divides every common multiple — the universal property, read right to left",
					Derive(func(b *Argument) {
						b.Fix()
						both := b.Assume()
						b.Show(
							"which is exactly what the lcm's multiples were shown to be",
							By(both, LcmDividesIffBoth))
					})),
			))
		}),
})}
