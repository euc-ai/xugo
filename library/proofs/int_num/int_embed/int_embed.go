// int_embed.go — the chapter: the ℕ↔ℤ boundary.
//
// Four parts, marked by banners:
//
// - Which integers & reaches
// - What ℤ inherits from ℕ through the boundary
// - Num_of_int, the one-sided inverse of &
// - & is a homomorphism

package int_embed

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/int_num/internal/intvocab"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Which integers & reaches
// ---------------------------------------------------------------------------
//
// which integers & reaches: the image of & is exactly the nonnegatives,
// and every integer is ±a natural.
//
// One inclusion is free: & is an order embedding and 0 ≤ n holds of
// every natural, so no image can be negative. The other is the
// chapter's ± analysis, and this file is the one place it is done —
// `Image` offers each integer as ±&n, and the minus branch has to be
// argued away before the plus branch can be read off.
//
// The rest of the chapter's positivity talk reads off that ⇔ instead of
// repeating the ± analysis: the two quantifier exchanges below —
// ForallNonneg cites it, ExistsNonneg cites ForallNonneg — and the
// section of num_of_int below.

// Image — every integer is a natural or the negation of one.
//
// The one member of the transport group that is not a lift, because it
// cannot be: its content is exactly what ℤ has and ℝ lacks. int is
// carved out of ℝ by the predicate "x is &n or -&n for some n", and
// this theorem is that predicate read back through the type bijection —
// the surjectivity clause of the sentence the transport group states,
// ℤ = &ℕ ∪ -&ℕ.
//
// The headline splits the existential across the disjunction —
// (∃n. x = &n) ∨ (∃n. x = -&n) — rather than the prenex
// ∃n. (x = -&n ∨ x = &n). Same proposition; this is the form that says
// "every integer is a natural or minus one".
//
// The argument is one sentence: the real representing x is ±&n, and
// either way the equation transports back into ℤ because `real_of_int`
// is injective. Both facts come from int_construction, the chapter that
// carves ℤ out of ℝ. The two directions differ only in which bridge
// carries the right-hand side across, so each is a section here and the
// top is their disjunction.
var Image = imageThm{family.Add(registry.ProofEntry{
	Name: "Image",
	Key:  "prop_a05e38db1893a235",
	Build: family.Sections("∀x:int. (∃n:num. x = &n) ∨ (∃n:num. x = int_neg(&n))",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			realT := MakeType("real")
			intT := MakeType("int")
			ctx.Const("real_of_int", MakeFun(intT, realT))
			ctx.Const("real_neg", MakeFun(realT, realT))
			ctx.Const("real_of_num", MakeFun(NumType, realT))

			// Each bridge reads its representative equation back through
			// injectivity, using the embedding and negation bridges.
			minus := ctx.Lemma(Statement{
				Binders: "∀x:int. ∀n:num.",
				Hypotheses: []string{
					"real_of_int(x) = real_neg(real_of_num(n))",
				},
				Conclusion: "x = int_neg(&n)",
			},
				func(a *Argument, x, n Term, representative Fact) {
					embedN := v.Embed(n)
					a.Show(
						"x = -&n: both bridges rewrite -&n's representative, leaving an "+
							"equation between representatives that injectivity reads back in ℤ",
						By(
							representative,
							At(int_construction.OfNumBridge, n),
							At(int_construction.NegBridge, embedN),
							int_construction.RepresentativeInjective),
					)
				})

			plus := ctx.Lemma(Statement{
				Binders: "∀x:int. ∀n:num.",
				Hypotheses: []string{
					"real_of_int(x) = real_of_num(n)",
				},
				Conclusion: "x = &n",
			},
				func(a *Argument, x, n Term, representative Fact) {
					a.Show(
						"x = &n: one bridge suffices, &n being its own representative",
						By(representative, At(int_construction.OfNumBridge, n), int_construction.RepresentativeInjective),
					)
				})

			return ctx.Theorem(headline, func(a *Argument, x Term) {
				a.Show(
					"x's representative is ±&n for some n, and whichever "+
						"it is, the matching bridge hands back that disjunct",
					By(At(int_construction.RepresentativeIsPlusMinusNat, x), minus, plus))
			})
		}),
})}

// EmbedNonneg — the image of & is nonnegative.
//
// Two steps, neither deep: 0 ≤ n holds of every natural, and & reflects
// the order. It is a member rather than two inline cites because four
// sites across three members need it — both halves of OfNumExists,
// ForallNonneg's ⇒ arm, and int_div_rem's divRemPair remainder
// bound — and a fact stated once is a fact a reader can look up.
//
// `int_le` is written longhand because the statement's only other
// content is two `&`-terms: with nothing int-typed beside them the DSL
// would read the whole thing in ℝ.
var EmbedNonneg = embedNonnegThm{family.Add(registry.ProofEntry{
	Name: "EmbedNonneg",
	Key:  "prop_a98754f9d036c7f5",
	Build: family.Theorem("∀n:num. int_le(&0, &n)",
		func(a *Argument, n Term) {
			a.Show(
				"& reflects the order, and ℕ's own bottom element is free",
				Cite(OfNumLe),
				Cite(nat_order.ZeroLessEq))
		}),
})}

// OfNumExists — an integer is a natural exactly when it is nonnegative.
//
// ⇐ carries the content. `Image` says every integer is ±&n, and the
// minus branch survives only where it agrees with the plus branch:
// &0 ≤ -&n forces &n ≤ &0, which against the always-available &0 ≤ &n
// pins n's image at &0, where -&0 = &0 and the two branches name the
// same integer. ⇒ is that always-available bound on its own.
var OfNumExists = ofNumExistsThm{family.Add(registry.ProofEntry{
	Name: "OfNumExists",
	Key:  "prop_9369343dd6970be3",
	Build: family.Sections("∀x:int. (∃n:num. x = &n) ⇔ &0 ≤ x",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			intT := MakeType("int")
			intLe := ctx.Const("int_le", MakeFun(intT, MakeFun(intT, TypeBool)))

			// The ± analysis is four inequalities between two ℤ-terms: ℕ's
			// zero embedded, and the image of the natural `Image` hands back.
			// Both are built rather than written, so the claims are ordered in
			// ℤ by construction — an all-`&` text with nothing int-typed
			// beside it is a statement about ℝ.
			embedZero := v.Embed(ctx.Const("_0", NumType))
			le := func(lhs, rhs Term) Prop { return MakeProp(intLe.Apply(lhs, rhs)) }

			imageSection := ctx.Lemma(Statement{
				Binders: "∀x:int.",
				Hypotheses: []string{
					"&0 ≤ x",
				},
				Conclusion: "∃n:num. x = &n",
			}, func(a *Argument, x Term, nonneg Fact) {
				// pm is the ± alternative `Image` offers at x; n is the
				// natural it is stated over, and the same n witnesses the
				// goal whichever branch turns out to hold.
				n, pm := a.Unpack(At(Image, x))
				embedN := v.Embed(n)
				a.Take(n) // ⊢ x = &n

				a.Do(pm.DismissRight(
					"x = +&n is already the equation to prove",
					TrivialNormalized()))
				// pm now names the surviving branch, x = -&n.

				below := a.Have(
					"&n ≤ &0 — x = -&n is nonnegative, so &n is nonpositive",
					le(embedN, embedZero),
					By(Normalized, pm, nonneg, At(int_real_lift.NegNonneg, embedN)))

				// &0 ≤ &n at this n. A premise, not a step: EmbedNonneg is
				// already proved, so grounding it is a value operation.
				above := At(EmbedNonneg, n)

				atZero := a.Have(
					"antisymmetry against those two bounds pins n's image at &0",
					MakeProp(embedN.Eq(embedZero)),
					By(below, above, At(int_real_lift.LessEqAntisym, embedN, embedZero)))

				// The minus branch has run out of room: with n's image at &0
				// the two branches name the same integer, and what is left is
				// computation with the equations already established.
				a.Show(
					"so the branches coincide: x = -&n = -&0 = &0 = &n",
					Cite(int_real_lift.NegZero),
					pm.Rw(),     // ⊢ x = &n  ↦  -&n = &n
					atZero.Rw(), // ↦ -&0 = &0, which is the cited fact
					TrivialNormalized())
			})

			return ctx.Theorem(headline, func(a *Argument, x Term) {
				a.Iff()
				// CiteNode, not Cite: the section is a ∀-implication that
				// must be APPLIED to the resident premise, and Cite's
				// stronger-than test runs before instantiation, so it
				// installs and leaves the arm open.
				a.Forward(
					"an image is nonnegative, and no ± analysis is needed for that",
					func(a *Argument, isImage Fact) {
						_, eq := a.Unpack(isImage)
						a.Show(
							"under x₀ = &n₀ the goal is that an image is nonnegative",
							eq.Rw(), // ⊢ &0 ≤ x₀  ↦  &0 ≤ &n₀
							By(EmbedNonneg))
					})
				a.Backward(
					"the nonnegative half is reached — the section above, at x₀",
					CiteNode(imageSection))
			})
		}),
})}

// ForallNonneg — to quantify over the nonnegative integers is to
// quantify over ℕ through &.
//
// The two directions want different halves of "the nonnegatives are
// exactly the image of &", and only one of them is deep. ⇐ needs that
// every nonnegative IS some &n — OfNumExists, where the ± analysis
// lives. ⇒ needs only that every &n is nonnegative: the order embedding
// read against ℕ's own bottom element, the free half OfNumExists leans
// on as well.
var ForallNonneg = forallNonnegThm{family.Add(registry.ProofEntry{
	Name: "ForallNonneg",
	Key:  "prop_38148da4d2851200",
	Build: family.Theorem("∀P:(int → bool). (∀i:int. &0 ≤ i ⇒ P(i)) ⇔ ∀n:num. P(&n)",
		func(a *Argument, P Term) {
			v := ops(a.Ctx())

			a.Iff()
			a.Forward(
				"an image is nonnegative, so a hypothesis guarded by nonnegativity is unguarded on the images",
				func(a *Argument, nonnegs Fact) {
					n := a.Fix()
					embedN := v.Embed(n)

					above := At(EmbedNonneg, n) // &0 ≤ &n₀

					a.Show(
						"the hypothesis at &n₀, whose guard that bound discharges",
						By(above, nonnegs.At(embedN)))
				})
			a.Backward(
				"a nonnegative is an image, so a hypothesis about every image already speaks about it",
				func(a *Argument, images Fact) {
					a.Fix() // let i₀ be an integer — the claim below names it
					nonneg := a.Assume()

					n, eq := a.Obtain(
						"i₀ names a natural — OfNumExists reads nonnegativity back as an existence",
						"∃n:num. i₀ = &n",
						// The cite lands ON the goal: ⊢ ∃n. i₀ = &n ↦ &0 ≤ i₀,
						// which is the assumption just made.
						By(nonneg, OfNumExists))

					a.Show(
						"P holds at every image, n₀'s among them, and i₀ IS that image",
						eq.Rw(), // ⊢ P₀(i₀)  ↦  P₀(&n₀)
						By(images.At(n)))
				})
		}),
})}

// ExistsNonneg — some nonnegative integer satisfies P exactly when some
// &n does.
//
// No new mathematics: this is ForallNonneg read through negation. "Some
// nonnegative satisfies P" denies "every nonnegative satisfies ¬P",
// "some image satisfies P" denies "every image satisfies ¬P", and
// ForallNonneg at ¬P equates the two denied statements.
var ExistsNonneg = existsNonnegThm{family.Add(registry.ProofEntry{
	Name: "ExistsNonneg",
	Key:  "prop_82498aef5d623afc",
	Build: family.Theorem("∀P:(int → bool). (∃i:int. &0 ≤ i ∧ P(i)) ⇔ ∃n:num. P(&n)",
		func(a *Argument, P Term) {
			// The instance is stated rather than passed as a witness tuple:
			// ForallNonneg binds a PREDICATE, and at the ∃-goal below the
			// cite is consumed against the conclusion, leaving no installed
			// ∀-hypothesis for a witness to ground. Stating it keeps ¬P₀ in
			// the checked layer instead of in this comment.
			negated := a.Have(
				"ForallNonneg at ¬P — no nonnegative satisfies ¬P exactly when no image does",
				"(∀i:int. &0 ≤ i ⇒ ¬P(i)) ⇔ ∀n:num. ¬P(&n)",
				Cite(ForallNonneg)) // the claim IS that instance, so the cite closes it

			a.Show(
				"denying each side turns those two ∀-statements into this ⇔'s two ∃-statements",
				By(Normalized, negated))
		}),
})}

// ---------------------------------------------------------------------------
// What ℤ inherits from ℕ through the boundary
// ---------------------------------------------------------------------------
//
// The part above says WHICH integers & reaches; this one says what ℤ keeps
// BECAUSE of it. Four inheritances, in increasing depth — the first
// carried in two spellings and the last in one- and two-variable
// forms, so six members:
//
// - Discreteness. Between an integer and its successor there is
// nothing: a strict inequality is a whole step. The gap y - x of a
// strict pair is a nonzero natural, and ℕ's least nonzero natural
// is 1.
// - The Archimedean property. The image of ℕ is COFINAL in ℤ — every
// integer sits below some &n — so the multiples of any nonzero d
// climb past everything. No descent to ℝ is needed: discreteness
// itself supplies the step 1 ≤ ±d that scales the climb.
// - Well-ordering below. The nonnegative integers ARE ℕ through &
// (the quantifier transports above), so a nonempty set of them
// has a least member because its preimage in ℕ does.
// - Well-founded induction on a nonnegative measure. Any map into
// the nonnegative integers carries induction back to its domain:
// were P to fail anywhere, the measures of its counterexamples
// would have a least member, and descent would go below it.
//
// The first three proofs run the same loop: push the question through
// & into ℕ, answer it with ℕ's own order theory, and carry the answer
// back along the transport laws. The fourth spends an answer already
// carried — it descends against WellOrderedBelow and never recrosses
// the boundary.

// Discrete — ℤ's order is discrete: strictly above x, nothing comes
// before x + 1.
//
// One direction is pure order algebra: x sits below x + 1, so anything
// at or above x + 1 is strictly above x. The other is the inheritance:
// a strict pair's gap y - x is nonnegative, hence the image of a
// natural n (OfNumExists, where the ± analysis lives); the gap is not
// zero, so n is positive, and ℕ's least positive natural is 1
// (OneLessEqIffPos). Adding x back to 1 ≤ n lands exactly on the
// claim.
var Discrete = discreteThm{family.Add(registry.ProofEntry{
	Name: "Discrete",
	Key:  "prop_99009321da9d07f",
	Build: family.Theorem("∀x y:int. x < y ⇔ x + &1 ≤ y",
		func(a *Argument, x Term, y *TermWrapper) {
			ctx := a.Ctx()
			v := ops(ctx)
			sub := intvocab.Term(ctx, "int_sub")
			intLe := intvocab.Term(ctx, "int_le")

			oneNat := ctx.Numeral(1)
			zero, one := v.Embed(ctx.Numeral(0)), v.Embed(oneNat)
			diff := sub.Apply(y, x)          // y - x, the gap
			xNext := v.IntPlus.Apply(x, one) // x + &1

			a.Iff()
			a.Forward(
				"the gap y - x is a natural, it is not zero, and ℕ has no natural strictly between 0 and 1",
				func(a *Argument, lt Fact) {
					nonneg := a.Have(
						"the gap of a strict pair is nonnegative",
						MakeProp(intLe.Apply(zero, diff)),
						By(
							lt,
							At(int_real_lift.LessEqOfLessThan, x, y), // x < y ⇒ x ≤ y
							int_real_lift.SubNonneg))

					n, gap := a.Obtain(
						"so it is the image of a natural",
						"∃n:num. int_sub(y, x) = &n",
						By(nonneg, OfNumExists))
					eN := v.Embed(n)

					sum := a.Have(
						"y sits &n₀ above x",
						MakeProp(y.Eq(v.IntPlus.Apply(eN, x))),
						By(gap, At(int_real_lift.EqSubRightAdd, y, x, eN))) // y - x = &n₀ ⇔ y = &n₀ + x

					pos := a.Have(
						"and n₀ is positive — a zero gap would refute the strict pair",
						"0 < n₀",
						By(
							lt,
							sum,
							At(int_real_lift.AddSym, eN, x), // &n₀ + x = x + &n₀
							At(int_real_lift.LessThanSelfAddRight, x, eN), // x < x + &n₀ ⇔ &0 < &n₀
							OfNumLt))

					a.Show(
						"so 1 ≤ n₀ in ℕ, and adding x to its image is the claim",
						By(
							pos,
							sum,
							At(nat_order.OneLessEqIffPos, n), // 1 ≤ n₀ ⇔ 0 < n₀
							At(OfNumLe, oneNat, n),           // &1 ≤ &n₀ ⇔ 1 ≤ n₀
							At(int_real_lift.LessEqAddRight, one, eN, x), // &1 + x ≤ &n₀ + x ⇔ &1 ≤ &n₀
							At(int_real_lift.AddSym, x, one)))            // x + &1 = &1 + x
				})
			a.Backward(
				"x is strictly below x + &1, and y is at or beyond it",
				func(a *Argument, reaches Fact) {
					a.Show(
						"chain x < x + &1 ≤ y",
						By(
							reaches,
							At(int_real_lift.LessThanSelfAddRight, x, one), // x < x + &1 ⇔ &0 < &1
							int_real_lift.ZeroLessThanOne,
							At(int_real_lift.LessThanLessEqTrans, x, xNext, y)))
				})
		}),
})}

// DiscreteFlipped — the same law in the flipped vocabulary. `>` and
// `≥` are defined as the flips of `<` and `≤`, so this row is Discrete
// at (y, x) read through the two defining readings GreaterIffLess and
// GreaterEqIffLessEq.
var DiscreteFlipped = discreteFlippedThm{family.Add(registry.ProofEntry{
	Name: "DiscreteFlipped",
	Key:  "prop_9f9010803037338e",
	Build: family.Theorem("∀x y:int. x > y ⇔ x ≥ y + &1",
		func(a *Argument, x, y Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			yNext := v.IntPlus.Apply(y, v.Embed(ctx.Numeral(1))) // y + &1

			a.Show(
				"unflip both comparisons; what remains is Discrete",
				By(
					At(int_construction.GreaterIffLess, x, y),         // x > y ⇔ y < x
					At(int_construction.GreaterEqIffLessEq, x, yNext), // x ≥ y + &1 ⇔ y + &1 ≤ x
					Discrete))
		}),
})}

// Archimedean — the multiples of any nonzero integer climb past
// everything.
//
// ℤ inherits this from ℕ, not from ℝ: the image of ℕ is cofinal
// (every integer is ±&n, and both signs sit below a natural — the
// section below), and discreteness turns "d is nonzero of known sign"
// into the scaling step &1 ≤ ±d. The climb x < &n then scales to
// x < &n · (±d) = (±&n) · d, and ±&n is the multiplier asked for.
// The seed descended to ℝ and cited its Archimedean axiom; nothing
// here leaves ℤ.
var Archimedean = archimedeanThm{family.Add(registry.ProofEntry{
	Name: "Archimedean",
	Key:  "prop_eeb65672302868ff",
	Build: family.Sections(Statement{
		Binders: "∀d x:int.",
		Hypotheses: []string{
			"d ≠ &0",
		},
		Conclusion: "∃c:int. x < c * d",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			neg := intvocab.Term(ctx, "int_neg")
			intLt := intvocab.Term(ctx, "int_lt")
			intLe := intvocab.Term(ctx, "int_le")
			suc := ctx.Const("suc", MakeFun(NumType, NumType))
			zero, one := v.Embed(ctx.Numeral(0)), v.Embed(ctx.Numeral(1))

			// The image of ℕ is cofinal: a natural strictly above any
			// integer. The ± analysis decides which natural: above &n
			// the next one serves, and above -&n the very first does.
			cofinal := ctx.Lemma("∀x:int. ∃n:num. x < &n",
				func(a *Argument, x Term) {
					n, pm := a.Unpack(At(Image, x)) // x = &n₀ ∨ x = -&n₀
					eN := v.Embed(n)
					negEN := neg.Apply(eN)

					a.Do(pm.SplitDisj(
						LeftHolds(
							"x = -&n₀: nonpositive, so already below &1",
							Given(func(a *Argument, isMinus Fact) {
								a.Take(ctx.Numeral(1))
								a.Show(
									"chain -&n₀ ≤ &0 < &1",
									By(
										isMinus,
										At(int_real_lift.NegNonneg, negEN), // -&n₀ ≤ &0 ⇔ &0 ≤ --&n₀
										At(int_real_lift.NegNeg, eN),       // --&n₀ = &n₀
										At(EmbedNonneg, n),                 // &0 ≤ &n₀
										int_real_lift.ZeroLessThanOne,
										At(int_real_lift.LessEqLessThanTrans, negEN, zero, one)))
							})),
						RightHolds(
							"x = &n₀: the next natural is strictly above it",
							Given(func(a *Argument, isPlus Fact) {
								a.Take(suc.Apply(n))
								a.Show(
									"n₀ < suc(n₀) in ℕ, embedded",
									By(
										Normalized,
										isPlus,
										At(OfNumLt, n, suc.Apply(n)),           // &n₀ < &suc(n₀) ⇔ n₀ < suc(n₀)
										At(nat_order.LessThanSucClause, n, n))) // n₀ < suc(n₀) ⇔ n₀ < n₀ ∨ n₀ = n₀
							})),
					))
				})

			return ctx.Theorem(headline,
				func(a *Argument, d, x Term, nonzero Fact) {
					n, above := a.Obtain(
						"some natural is strictly above x",
						"∃n:num. x < &n",
						By(cofinal))
					eN := v.Embed(n)

					a.Cases(intLt.Apply(zero, d))
					a.When(
						"d positive: discreteness makes it a whole step, and scaling the climb by it keeps climbing",
						func(a *Argument, pos Fact) {
							oneLe := a.Have(
								"&1 ≤ d — a positive integer clears a whole step",
								MakeProp(intLe.Apply(one, d)),
								By(
									pos,
									At(Discrete, zero, d), // &0 < d ⇔ &0 + &1 ≤ d
									int_real_lift.AddLeftIdentity))

							scaled := a.Have(
								"so multiplying the bound &n₀ by d does not shrink it",
								MakeProp(intLe.Apply(eN, v.IntMul(eN, d))),
								By(
									oneLe,
									At(EmbedNonneg, n), // &0 ≤ &n₀
									At(int_real_lift.LessEqMulLeft, eN, one, d), // &0 ≤ &n₀ ∧ &1 ≤ d ⇒ &n₀ * &1 ≤ &n₀ * d
									int_real_lift.MulRightIdentity))

							a.Take(eN)
							a.Show(
								"chain x < &n₀ ≤ &n₀ * d",
								By(above, scaled, At(int_real_lift.LessThanLessEqTrans, x, eN, v.IntMul(eN, d))))
						})
					a.Otherwise(
						"d negative: the same climb, scaled by -d and paid for with a negated multiplier",
						func(a *Argument, notPos Fact) {
							negD := neg.Apply(d)

							negPos := a.Have(
								"-d is positive — the sign trichotomy has nowhere else to go",
								MakeProp(intLt.Apply(zero, negD)),
								By(notPos, nonzero, At(int_real_lift.LessThanNegTotal, d)))

							oneLe := a.Have(
								"&1 ≤ -d, by the same discreteness step",
								MakeProp(intLe.Apply(one, negD)),
								By(negPos, At(Discrete, zero, negD), int_real_lift.AddLeftIdentity))

							scaled := a.Have(
								"so &n₀ ≤ &n₀ * -d",
								MakeProp(intLe.Apply(eN, v.IntMul(eN, negD))),
								By(
									oneLe,
									At(EmbedNonneg, n),
									At(int_real_lift.LessEqMulLeft, eN, one, negD),
									int_real_lift.MulRightIdentity))

							a.Take(neg.Apply(eN))
							a.Show(
								"and &n₀ * -d is (-&n₀) * d — the negation crosses the product",
								By(
									above,
									scaled,
									At(int_real_lift.MulRightNeg, eN, d), // &n₀ * -d = -(&n₀ * d)
									At(int_real_lift.MulLeftNeg, eN, d),  // -&n₀ * d = -(&n₀ * d)
									At(int_real_lift.LessThanLessEqTrans, x, eN, v.IntMul(neg.Apply(eN), d))))
						})
				})
		}),
})}

// WellOrderedBelow — the nonnegative integers are well-ordered: a
// predicate with a nonnegative point has a LEAST nonnegative point.
//
// The nonnegatives are exactly the image of ℕ (above), so the
// question transports whole: ExistsNonneg carries the point across,
// ℕ's own well-ordering picks the least preimage n₀, and the returned
// witness is &n₀. Its minimality transports back one nonnegative y at
// a time — y is itself an image &m, m cannot be below n₀, and the
// order embedding reads n₀ ≤ m as &n₀ ≤ y.
var WellOrderedBelow = wellOrderedBelowThm{family.Add(registry.ProofEntry{
	Name: "WellOrderedBelow",
	Key:  "prop_6dfebcdd99369de2",
	Build: family.Theorem("∀P:(int → bool). "+
		"    (∃x:int. &0 ≤ x ∧ P(x)) ⇔ ∃x:int. &0 ≤ x ∧ P(x) ∧ (∀y:int. &0 ≤ y ∧ P(y) ⇒ x ≤ y)",
		func(a *Argument, P *TermWrapper) {
			ctx := a.Ctx()
			v := ops(ctx)

			a.Iff()
			a.Forward(
				"transport the point to ℕ, take the least preimage, and carry its minimality back",
				func(b *Argument, somePoint Fact) {
					// The point, made concrete — Obtain's quantifier
					// bookkeeping below must not meet a second
					// strippable ∃ in the context.
					_, pt := b.Unpack(somePoint) // &0 ≤ x₀ ∧ P(x₀)

					// λn. P(&n) — the predicate pulled back along &,
					// which is what ℕ's well-ordering is applied to.
					nv := Var("n", NumType)
					pulledBack := nv.To(P.Apply(v.Embed(nv)))

					n, leastN := b.Obtain(
						"the point reaches ℕ through ExistsNonneg, and ℕ's "+
							"well-ordering picks the least natural satisfying P through &",
						"∃n:num. P(&n) ∧ (∀m:num. m < n ⇒ ¬P(&m))",
						By(pt, ExistsNonneg, At(nat_order.WellOrdering, pulledBack)))
					eN := v.Embed(n)

					least := b.Conjuncts(
						leastN,
						"P holds at its image",
						"and no natural below n₀ satisfies it")

					minimal := b.Have(
						"so &n₀ bounds every nonnegative P-point from below",
						"∀y:int. &0 ≤ y ∧ P(y) ⇒ &n₀ ≤ y",
						Derive(func(b *Argument) {
							b.Fix()
							guard := b.Assume() // &0 ≤ y₀ ∧ P(y₀)
							m, eq := b.Obtain(
								"a nonnegative point is itself an image",
								"∃m:num. y₀ = &m",
								By(guard, OfNumExists))
							b.Show(
								"its natural is not below n₀, and & carries n₀ ≤ m back to the integers",
								By(
									Normalized,
									guard,
									eq,
									least[1].At(m),                  // m₀ < n₀ ⇒ ¬P(&m₀)
									At(nat_order.NotLessThan, m, n), // ¬(m₀ < n₀) ⇔ n₀ ≤ m₀
									At(OfNumLe, n, m)))              // &n₀ ≤ &m₀ ⇔ n₀ ≤ m₀
						}))

					b.Take(eN)
					b.Show(
						"&n₀ is the least nonnegative P-point",
						By(least[0], minimal, EmbedNonneg))
				})
			a.Backward(
				"a least nonnegative P-point is in particular a nonnegative P-point",
				func(b *Argument, leastPoint Fact) {
					b.Show(
						"drop the minimality conjunct",
						By(leastPoint))
				})
		}),
})}

// MeasureInduction — well-founded induction on a nonnegative integer
// measure: to prove P at every point of A, it is enough to prove it at
// each point granted it at all points of strictly smaller measure.
//
// The measure turns well-ordering below into descent. Were P to fail,
// the measures of its counterexamples would form a nonempty set of
// nonnegative integers, and WellOrderedBelow — read at the predicate
// "v is the measure of a counterexample" — would pick a least one,
// v₀ = m(z₀). The descent hypothesis at z₀, contraposed against
// ¬P(z₀), hands a counterexample y₀ of strictly smaller measure; m(y₀)
// is then a counterexample measure below the least one, which
// int_real_lift.NotLessThan refuses. The seed transported the question to ℕ's
// well-founded induction; this proof never leaves ℤ.
var MeasureInduction = measureInductionThm{family.Add(registry.ProofEntry{
	Name: "MeasureInduction",
	Key:  "prop_e0f641f501a84948",
	Build: family.Theorem(Statement{
		Binders: "∀P:(A → bool). ∀m:(A → int). ∀x:A.",
		Hypotheses: []string{
			"∀x:A. &0 ≤ m(x)",
			"∀x:A. (∀y:A. m(y) < m(x) ⇒ P(y)) ⇒ P(x)",
		},
		Conclusion: "P(x)",
	},
		func(a *Argument, P, m *TermWrapper, bound, descent Fact) {
			// Q := λv. ∃x. v = m(x) ∧ ¬P(x) — "v is the measure of a
			// counterexample", the predicate WellOrderedBelow is read at.
			vInt := Var("v", MakeType("int"))
			xA := Var("x", MakeVarType("A"))
			counterMeasure := vInt.To(Exists(xA)(vInt.Eq(m.Apply(xA)).And(Not(P.Apply(xA)))))

			notAll := a.SupposeNot() // ¬(∀x. P(x))
			x0, notP0 := a.Obtain(
				"some x₀ refutes P — pure normalization of the supposition",
				"∃x:A. ¬P(x)",
				By(Normalized, notAll))

			v0, least := a.Obtain(
				"m(x₀) witnesses that some counterexample measure is "+
					"nonnegative, so WellOrderedBelow at Q hands a least one",
				"∃v:int. (&0 ≤ v ∧ (∃x:A. v = m(x) ∧ ¬P(x))) ∧ (∀w:int. &0 ≤ w ∧ (∃x:A. w = m(x) ∧ ¬P(x)) ⇒ v ≤ w)",
				// Normalized β-reduces the instance before the close.
				By(
					Normalized,
					notP0,
					bound.At(x0), // &0 ≤ m(x₀)
					At(WellOrderedBelow, counterMeasure)))

			z0, attains := a.Obtain(
				"v₀ is the measure of a counterexample z₀",
				"∃z:A. v₀ = m(z) ∧ ¬P(z)",
				By(least))
			minimal := a.Have(
				"and no counterexample measures below v₀",
				"∀w:int. &0 ≤ w ∧ (∃x:A. w = m(x) ∧ ¬P(x)) ⇒ v₀ ≤ w",
				By(least))

			y0, lower := a.Obtain(
				"the descent hypothesis at z₀, contraposed against "+
					"¬P(z₀): some y₀ of strictly smaller measure also refutes P",
				"∃y:A. m(y) < m(z₀) ∧ ¬P(y)",
				By(
					Normalized,
					descent.At(z0), // (∀y. m(y) < m(z₀) ⇒ P(y)) ⇒ P(z₀)
					attains))

			a.Show(
				"m(y₀) is a counterexample measure strictly below the least one — a contradiction",
				By(
					bound.At(y0),            // &0 ≤ m(y₀)
					minimal.At(m.Apply(y0)), // … ⇒ v₀ ≤ m(y₀)
					attains,
					lower,
					At(int_real_lift.NotLessThan, m.Apply(y0), v0))) // ¬(m(y₀) < v₀) ⇔ v₀ ≤ m(y₀)
		}),
})}

// PairMeasureInduction — the same induction for a measure of two
// arguments.
//
// No new mathematics: this is MeasureInduction read at the pair type
// A × B. Pull P and m back along the projections (λp. P(fst(p), snd(p))
// and likewise for m), hand the sibling the pulled-back bound and
// descent, and collapse fst/snd at literal pairs to read its conclusion
// back in two variables.
var PairMeasureInduction = pairMeasureInductionThm{family.Add(registry.ProofEntry{
	Name: "PairMeasureInduction",
	Key:  "prop_bccf04aeae1a3620",
	Build: family.Theorem(Statement{
		Binders: "∀P:(A → B → bool). ∀m:(A → B → int). ∀x:A. ∀y:B.",
		Hypotheses: []string{
			"∀x:A. ∀y:B. &0 ≤ m(x, y)",
			"∀x:A. ∀y:B. (∀x':A. ∀y':B. m(x', y') < m(x, y) ⇒ P(x', y')) ⇒ P(x, y)",
		},
		Conclusion: "P(x, y)",
	},
		func(a *Argument, P, m *TermWrapper, bound, descent Fact) {
			ctx := a.Ctx()
			tyA, tyB := MakeVarType("A"), MakeVarType("B")
			fst, snd := pairs.ProjectionsAt(ctx, tyA, tyB)
			pv := Var("p", pairs.ProdType(tyA, tyB))
			// P and m pulled back along the projections — what the
			// sibling is read at.
			pulledP := pv.To(P.Apply(fst.Apply(pv), snd.Apply(pv)))
			pulledM := pv.To(m.Apply(fst.Apply(pv), snd.Apply(pv)))

			pairBound := a.Have(
				"the pulled-back measure is nonnegative at every pair",
				"∀p:prod(A, B). &0 ≤ m(fst(p), snd(p))",
				By(bound))
			pairDescent := a.Have(
				"and the pulled-back P descends — collapsing the projections "+
					"at (x', y') turns the given descent into the pair form",
				Statement{
					Binders: "∀p:prod(A, B).",
					Hypotheses: []string{
						"∀q:prod(A, B). m(fst(q), snd(q)) < m(fst(p), snd(p)) ⇒ P(fst(q), snd(q))",
					},
					Conclusion: "P(fst(p), snd(p))",
				},
				By(descent, pairs.Fst, pairs.Snd))

			allPairs := a.Have(
				"so the sibling at A × B concludes the pulled-back P at every pair",
				"∀p:prod(A, B). P(fst(p), snd(p))",
				// The witness tuple is PARTIAL (the sibling's install form
				// prenexes a third binder), so it reads positionally
				// against the install prefix ∀m.∀P — measure first; the
				// instance lands with λ-redexes, which Normalized reduces.
				By(Normalized, pairBound, pairDescent, MeasureInduction.Inst[Prod[A, B]]().At(pulledM, pulledP)))

			a.Show(
				"at the literal pair (x, y) the projections collapse to the claim",
				By(allPairs, pairs.Fst, pairs.Snd))
		}),
})}

// ---------------------------------------------------------------------------
// Num_of_int, the one-sided inverse of &
// ---------------------------------------------------------------------------
//
// `num_of_int` is Hilbert-defined: num_of_int(x) = εn. &n = x. Choice
// makes it total, so it names SOME natural for every integer; it names
// the right one exactly where the ε has something to choose from, i.e.
// where x really is in the image of &. On ℤ that is the nonnegative
// half — the chapter settles that above — and what is left
// here is reading the ε off it: that num_of_int is a section of & there,
// that being there is not merely sufficient for that but necessary, and
// that composing the other way round needs no guard at all, a natural's
// image being in range by construction.

// NumOfIntSection — & has a section on the nonnegatives, and it is
// num_of_int.
//
// Unfolding num_of_int leaves the claim that the ε-choice satisfies the
// very property it chose against: &(εn. &n = x) = x says no more and no
// less than that some natural has x for its image. Where x is
// nonnegative, OfNumExists says one does.
var NumOfIntSection = numOfIntSectionThm{family.Add(registry.ProofEntry{
	Name: "NumOfIntSection",
	Key:  "prop_a5e8d063337cfafc",
	Build: family.Theorem(Statement{
		Binders: "∀x:int.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "&num_of_int(x) = x",
	},
		func(a *Argument, x Term, _ Fact) {
			a.Show(
				"unfolded, the goal is the existence claim itself, and x₀ is nonnegative",
				Unfold(int_construction.NumOfIntDef), // ⊢ &(num_of_int(x₀)) = x₀  ↦  &(εn. &n = x₀) = x₀
				Cite(OfNumExists))
		}),
})}

// NumOfInt — num_of_int inverts & on the nonnegatives and nowhere else.
//
// The ⇔ sharpens NumOfIntSection, which gives it in one direction. The
// other says that succeeding at all is already the guard: an x its own
// num_of_int is carried back to is an image of &, and being an image is
// what OfNumExists reads as lying at &0 or above.
var NumOfInt = numOfIntThm{family.Add(registry.ProofEntry{
	Name: "NumOfInt",
	Key:  "prop_6eb634489fe3b8d",
	Build: family.Theorem("∀x:int. &num_of_int(x) = x ⇔ &0 ≤ x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())

			a.Iff()
			a.Forward(
				"an integer num_of_int carries back to itself is an image of &, and images are nonnegative",
				func(a *Argument) {
					inImage := a.Have(
						"x₀ is in the image of &, num_of_int(x₀) being the natural sent to it",
						"∃n:num. x₀ = &n",
						Witness(v.OfInt(x)), // ↦ x₀ = &(num_of_int(x₀)), the arm's own equation
						TrivialNormalized())

					// Bare rather than ground at x₀: the goal IS the
					// equivalence's other side, so the cite matches it and
					// closes rather than installing a ∀-hyp to specialize.
					a.Show(
						"and image membership is what OfNumExists reads as nonnegativity",
						By(inImage, OfNumExists))
				})
			a.Backward(
				"nonnegativity is the side condition NumOfIntSection already carries, and this is it at x₀",
				func(b *Argument, nonneg Fact) {
					// the arm's own &0 ≤ x₀ is what discharges that condition
					b.Show(
						"the section's own side condition is this arm's hypothesis",
						By(nonneg, At(NumOfIntSection, x)))
				})
		}),
})}

// OfNumRetract — the composite in the other order, and it holds
// everywhere: a natural's image is in range by construction, so the ε
// has the right natural among its candidates, and injectivity of & —
// which leaves it no other candidate — is what stops choice from
// wandering off it.
var OfNumRetract = ofNumRetractThm{family.Add(registry.ProofEntry{
	Name: "OfNumRetract",
	Key:  "prop_928d7e1d9d9d1221",
	Build: family.Theorem("∀n:num. num_of_int(&n) = n",
		func(a *Argument, n Term) {
			a.Show(
				"the ε chooses among the naturals & sends to &n₀, and injectivity leaves only n₀ there",
				Unfold(int_construction.NumOfIntDef), // ⊢ num_of_int(&n₀) = n₀  ↦  n₀ = (εk. &k = &n₀)
				Cite(OfNumEq))
		}),
})}

// ---------------------------------------------------------------------------
// & is a homomorphism
// ---------------------------------------------------------------------------
//
// & is a homomorphism: the laws that carry an ℕ computation into ℤ
// unchanged.
//
// Each is inherited. ℤ is carved out of ℝ and `int_of_num` factors
// through `real_of_num`, so ℕ ↪ ℤ transports exactly what ℕ ↪ ℝ
// already did, and the proof of each member is that one lift step.
// All of them are unconditional except the last, OfNumSub, which is
// where ℕ's truncated difference forces a hypothesis.
//
// Every member below lifts from a CURATED ℝ twin it names
// (`family.Lifted(…, real_construction.X)`, or any other ℝ chapter —
// OfNumLt's twin is `real_order_ring.OfNumLessThan`, OfNumSuc's is
// `real_ring.OfNumSuc`). One spelling varies, for a reason outside the
// mathematics:
//
// - A statement says `int_of_num(n)` longhand wherever no ℤ constant
// appears beside it, and `&n` where one does. The DSL's `&` is a
// type-directed coercion: with nothing int-typed in the term it
// resolves in ℝ, so `&(suc n) = &n + &1` would be a statement about
// the reals while `&(nat_max(m, n)) = int_max(&m, &n)` is anchored by
// `int_max` and is not.

// OfNumEq — & is injective, which is what lets an equation be argued in
// ℤ and read back in ℕ.
var OfNumEq = ofNumEqThm{family.Add(registry.ProofEntry{
	Name:  "OfNumEq",
	Key:   "prop_19e269c50de147ac",
	Build: family.Lifted("∀m n:num. m = int_of_num(n) ⇔ m = n", real_construction.OfNumEq),
})}

// OfNumAdd — & is additive.
var OfNumAdd = ofNumAddThm{family.Add(registry.ProofEntry{
	Name:  "OfNumAdd",
	Key:   "prop_5ee340e41582c165",
	Build: family.Lifted("∀m n:num. m + n = m + int_of_num(n)", real_construction.OfNumAdd),
})}

// OfNumMul — & is multiplicative.
var OfNumMul = ofNumMulThm{family.Add(registry.ProofEntry{
	Name:  "OfNumMul",
	Key:   "prop_bc89cb72235ad308",
	Build: family.Lifted("∀m n:num. m * n = m * int_of_num(n)", real_construction.OfNumMul),
})}

// OfNumLe — & is an order embedding, so an inequality may be argued on
// either side and read on the other.
var OfNumLe = ofNumLeThm{family.Add(registry.ProofEntry{
	Name:  "OfNumLe",
	Key:   "prop_860193d7397b2c74",
	Build: family.Lifted("∀m n:num. m ≤ int_of_num(n) ⇔ m ≤ n", real_construction.OfNumLessEq),
})}

// OfNumLt — the strict half of the order embedding.
var OfNumLt = ofNumLtThm{family.Add(registry.ProofEntry{
	Name:  "OfNumLt",
	Key:   "prop_b429e324367922ed",
	Build: family.Lifted("∀m n:num. m < int_of_num(n) ⇔ m < n", real_order_ring.OfNumLessThan),
})}

// OfNumAbs — naturals are their own absolute values: the image of & is
// where |·| acts trivially.
var OfNumAbs = ofNumAbsThm{family.Add(registry.ProofEntry{
	Name:  "OfNumAbs",
	Key:   "prop_748d93bceeeabcbe",
	Build: family.Lifted("∀n:num. int_abs(&n) = &n", real_sgn_abs.AbsOfNum),
})}

// OfNumSuc — & takes ℕ's successor to adding one, which is what lets an
// induction be run in ℕ and its conclusion read as ℤ arithmetic.
var OfNumSuc = ofNumSucThm{family.Add(registry.ProofEntry{
	Name:  "OfNumSuc",
	Key:   "prop_193ecec55c16e072",
	Build: family.Lifted("∀n:num. suc(n) = n + int_of_num(1)", real_ring.OfNumSuc),
})}

// OfNumMax — & commutes with taking the larger of two naturals, the
// two-argument face of its being an order embedding.
var OfNumMax = ofNumMaxThm{family.Add(registry.ProofEntry{
	Name:  "OfNumMax",
	Key:   "prop_ed5b44724627ed30",
	Build: family.Lifted("∀m n:num. &(max(m, n)) = int_max(&m, &n)", real_sup_inf.OfNumMax),
})}

// OfNumMin — and the smaller: ℤ's two order selectors restrict to ℕ's
// along &.
var OfNumMin = ofNumMinThm{family.Add(registry.ProofEntry{
	Name:  "OfNumMin",
	Key:   "prop_6b88c01b4a97289f",
	Build: family.Lifted("∀m n:num. &(min(m, n)) = int_min(&m, &n)", real_sup_inf.OfNumMin),
})}

// OfNumSub — & carries a difference exactly where ℕ did not truncate
// one. The one transport law in this chapter that carries a
// hypothesis.
//
// Every other law here is unconditional because & meets an operation ℕ
// and ℤ compute the same way. Subtraction is the exception: ℕ's
// difference is truncated at 0 and ℤ's is not, so `n - m` in ℕ is only
// the honest difference where nothing had to be thrown away. The
// hypothesis `m ≤ n` names exactly that region, and inside it the two
// subtractions agree.
//
// So the proof has to spend the hypothesis somewhere, and the place it
// spends it is a sum. ℤ's difference is unconditional, so a difference
// equation there is a sum equation; and a sum is where the truncation
// declares itself, since putting m back recovers n exactly when the
// difference kept everything.
//
// `int_real_lift.EqSubRightAdd` turns the goal into a sum equation,
// `OfNumAdd` reads that sum back in ℕ, and `nat_monus.SubAddCancel` is
// where the hypothesis is spent: it is the ℕ fact that adding m₀ back
// undoes n₀ - m₀, and it holds only under m₀ ≤ n₀.
var OfNumSub = ofNumSubThm{family.Add(registry.ProofEntry{
	Name: "OfNumSub",
	Key:  "prop_9ff8009bc02d4f2e",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "int_sub(&n, &m) = &(n - m)",
	},
		func(a *Argument, m, n Term, guard Fact) {
			ctx := a.Ctx()
			v := ops(ctx)

			// ℕ's difference as a builder. The text-DSL's default scope
			// supplies `-` for PARSING, which is all a claim text needs;
			// the ℤ claim and the witness tuple below need it as a Go term.
			// Script.Const is idempotent, so re-declaring it is free.
			natSub := ctx.Const("-", MakeFun(NumType, MakeFun(NumType, NumType)))
			diff := natSub.Apply(n, m)
			em, en, eDiff := v.Embed(m), v.Embed(n), v.Embed(diff)

			restored := a.Have(
				"under m ≤ n the difference threw nothing away, so adding m back recovers n",
				"n - m + m = n",
				By(guard, At(nat_monus.SubAddCancel, n, m))) // m₀ ≤ n₀ ⇒ n₀ - m₀ + m₀ = n₀

			// The claim is assembled rather than written: an all-& term with
			// nothing int-typed beside it is a statement about ℝ. The
			// OfNumAdd cite is bare because it fires as a goal rewrite
			// rather than installing — ↦ &(n₀ - m₀ + m₀) = &n₀, which is
			// `restored` read through &.
			sum := a.Have(
				"& is additive, so the ℤ sum of the two pieces is the embedded ℕ sum — and that sum is n₀",
				MakeProp(v.IntPlus.Apply(eDiff, em).Eq(en)),
				By(restored, OfNumAdd))

			a.Show(
				"ℤ subtracts unconditionally, and its adjunction states the goal as exactly that sum equation",
				By(
					sum,
					// &n₀ - &m₀ = &(n₀ - m₀) ⇔ &n₀ = &(n₀ - m₀) + &m₀
					At(int_real_lift.EqSubRightAdd, en, em, eDiff)))
		}),
})}
