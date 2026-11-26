// int_construction.go — the chapter: how ℤ is built out of ℝ.
//
// Five parts, marked by banners:
//
// - The predicate ℤ is carved by, and the type carved with it
// - Reading an integer through the real it was carved from
// - What the carved set is closed under
// - `real_of_int` carries each ℤ operation to its ℝ counterpart
// - The comparisons and the absolute value, read back on ℤ

package int_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The predicate ℤ is carved by, and the type carved with it
// ---------------------------------------------------------------------------
//
// Three statements, in the only order they can come in: what `integer`
// says once its definition is unpacked, that every natural satisfies it,
// and then the type definition that predicate is stamped against.
// Everything else in the chapter reads one of them at a representative.

// IntegerIffPlusMinusNat — a real is an integer exactly when it is a
// natural or the negation of one.
//
// `integer` is defined by the absolute-value form, which is compact but
// says nothing usable: no later proof reasons about |x|. This member is
// the translation into the ± form, and every subsequent statement in
// the chapter — the type's inhabitant, what a representative looks
// like, and each operation's closure argument — reads it rather than
// the definition.
//
// The two directions are different in kind, and the ⇒ one is why
// signSplitsAbs exists: opening the conditional inside `real_abs` is
// the whole cost of this member, so it is paid once, in a lemma, and
// the direction that needs it becomes a substitution.
var IntegerIffPlusMinusNat = integerIffPlusMinusNatThm{family.Add(registry.ProofEntry{
	Name: "IntegerIffPlusMinusNat",
	Key:  "prop_f989ae50ffba0b38",
	Build: family.Sections("∀x:real. integer(x) ⇔ ∃n:num. x = &n ∨ x = -&n",
		func(ctx *Script, headline string) *GoalStackNode {
			signSplitsAbs := ctx.Lemma("∀x:real. x = |x| ∨ x = -|x|", func(a *Argument) {
				// Unfolding leaves `x = COND(&0 ≤ x, x, -x) ∨ x = -COND(…)`:
				// whichever branch the sign takes, one disjunct is x = x and
				// the other needs only that negating twice returns x.
				a.Do(
					Unfold(real_sgn_abs.RealAbsDef),
					By(real_ring.NegNeg),
				)
			})

			absIsNat := ctx.Lemma("∀x:real. ∀n:num. |x| = &n ⇔ x = &n ∨ x = -&n", func(a *Argument, x, n Term) {
				a.Iff()
				a.Forward(
					"x₀ is ±|x₀|, and |x₀| is &n₀",
					func(a *Argument, absIsN Fact) {
						a.Show(
							"substituting &n₀ for |x₀| in the sign split is the disjunction",
							By(absIsN, At(signSplitsAbs, x)))
					})
				a.Backward(
					"both of ±&n₀ have absolute value &n₀",
					func(a *Argument, isPlusMinus Fact) {
						a.Do(isPlusMinus.SplitDisj(
							LeftHolds(
								"x₀ = &n₀ — a natural is its own absolute value",
								Given(func(a *Argument, isNat Fact) {
									a.Show(
										"|&n₀| = &n₀ outright",
										By(Normalized, isNat, real_sgn_abs.AbsOfNum))
								})),
							RightHolds(
								"x₀ = -&n₀ — the sign comes off first, and the same law finishes",
								Given(func(a *Argument, isNegNat Fact) {
									a.Show(
										"|-&n₀| is |&n₀|, which is &n₀",
										By(Normalized, isNegNat, real_sgn_abs.AbsOfNum, real_sgn_abs.AbsEven))
								})),
						))
					})
			})

			return ctx.Theorem(headline, func(a *Argument) {
				// `integer x` abbreviates `∃n. |x| = &n`, so the headline is
				// absIsNat under that existential — the same n on both sides.
				a.Do(
					Unfold(IntegerDef),
					By(absIsNat),
				)
			})
		}),
})}

// IntegerOfNum — every natural, seen in ℝ, is an integer: its absolute
// value is itself, a natural.
//
// The one integrality fact every chapter above this one wants on sight,
// so it is stated once rather than read out of the ± characterization at
// each use.
var IntegerOfNum = integerOfNumThm{family.Add(registry.ProofEntry{
	Name: "IntegerOfNum",
	Key:  "prop_53a14c071cc5a916",
	Build: family.Theorem("∀n:num. integer(&n)",
		func(a *Argument, n *Expr[Nat]) {
			a.Do(Unfold(IntegerDef))
			a.Take(n)
			a.Show(
				"|&n| = &n",
				By(real_sgn_abs.AbsOfNum.At(n)))
		}),
})}

// TypeBijection — the two axioms `int` was stamped with.
//
// `int` is declared to be in bijection with the reals satisfying
// `integer`, via the pair real_of_int / int_of_real. The two halves say
// so from the two sides: every integer survives the round trip down to
// ℝ and back, and a real survives the round trip up and back exactly
// when it is one of the reals being carved out. Together they make ℤ
// that subset rather than a quotient of it, which is what lets the rest
// of the chapter argue about an integer by arguing about its
// representative.
//
// A type may only be stamped against a non-empty subset; that
// inhabitant is IntegerInhabited (definitions.go), and everything here
// is the type definition's own output.
var TypeBijection = typeBijectionThm{family.Add(registry.ProofEntry{
	Name: "TypeBijection",
	Key:  "prop_b5dee65a4ca6998",
	Build: family.Theorem("(∀a:int. int_of_real(real_of_int(a)) = a) ∧ "+
		"(∀r:real. integer(r) ⇔ real_of_int(int_of_real(r)) = r)",
		func(a *Argument) {
			// The two axioms the type's definition comes with, assembled
			// into the conjunction the rest of the chapter cites; no
			// consumer needs either half separately.
			a.Show(
				"the headline is those two axioms, one conjunct each",
				By(a.Ctx().Dep(IntDef.Retraction), a.Ctx().Dep(IntDef.Membership)))
		}),
})}

// ---------------------------------------------------------------------------
// Reading an integer through the real it was carved from
// ---------------------------------------------------------------------------
//
// `real_of_int` sends an integer to its representative, and these three
// statements are everything the rest of the corpus needs to know about
// that real: it satisfies the predicate ℤ was carved by, it is a natural
// or the negation of one, and it determines the integer it came from.
// Together they are the translation an argument about ℤ passes through on
// its way down to ℝ.
//
// Each is a single citation of the carving part above, and each is cheap for the
// same reason: the type definition is already a member there, so nothing
// here has to rebuild it out of its inhabitant before it can start on
// its own statement.

// RepresentativeIsInteger — a representative lands inside the subset ℤ
// was carved from.
//
// TypeBijection's membership half tests a real by sending it up into ℤ and
// back down and asking whether it returns unchanged. A representative
// makes that trip starting from an integer, and its first leg is exactly
// what the retraction half settles: going up from x's representative
// returns x itself, so coming back down returns the representative. The
// test passes, and it took both halves of the one cited fact to see it.
//
// Its role in this file is to be the first premise of the statement
// below, which is where the predicate it establishes gets discharged
// again — on its own it says only that the carving predicate is true
// somewhere it was always going to be true.
var RepresentativeIsInteger = representativeIsIntegerThm{family.Add(registry.ProofEntry{
	Name: "RepresentativeIsInteger",
	Key:  "prop_534ca9ae91f85a15",
	Build: family.Theorem("∀x:int. integer(real_of_int(x))",
		func(a *Argument) {
			a.Show(
				"x's representative comes back from ℤ unchanged, which is what membership asks of it",
				By(Normalized, TypeBijection))
		}),
})}

// RepresentativeIsPlusMinusNat — a representative is a natural or the
// negation of one.
//
// One sentence composed from the two facts above it: a representative
// satisfies the carving predicate, and a real satisfying that predicate is
// ±a natural. Neither premise mentions the type definition, so neither
// does this proof.
//
// What the composition buys is that the predicate is gone. `integer` has
// been discharged and what is left is an equation in ordinary ℝ
// arithmetic, which is the form `int_embed` reaches down here for when it
// asks which integers `&` reaches.
var RepresentativeIsPlusMinusNat = representativeIsPlusMinusNatThm{family.Add(registry.ProofEntry{
	Name: "RepresentativeIsPlusMinusNat",
	Key:  "prop_7c24ad0c705e2728",
	Build: family.Theorem("∀i:int. ∃n:num. real_of_int(i) = &n ∨ real_of_int(i) = -&n",
		func(a *Argument) {
			a.Show(
				"a representative is an integer, and an integer is ±a natural",
				By(RepresentativeIsInteger, IntegerIffPlusMinusNat))
		}),
})}

// RepresentativeInjective — integers with the same representative are the
// same integer.
//
// ⇒ is congruence and costs nothing. ⇐ is TypeBijection's retraction half:
// `int_of_real` undoes `real_of_int`, so applying it to an equation
// between two representatives hands back the equation between the two
// integers.
//
// This is what makes ℤ a SUBSET of ℝ rather than a quotient of one — an
// integer is recoverable from its representative, so nothing is lost on
// the way down. It is the step an argument closes on whenever it states
// something about ℤ, proves it about representatives, and reads the result
// back.
var RepresentativeInjective = representativeInjectiveThm{family.Add(registry.ProofEntry{
	Name: "RepresentativeInjective",
	Key:  "prop_9f155c9c70300e52",
	Build: family.Theorem("∀x y:int. x = y ⇔ real_of_int(x) = real_of_int(y)",
		func(a *Argument) {
			a.Show(
				"the retraction undoes an equation between representatives; the converse is congruence",
				By(TypeBijection))
		}),
})}

// ---------------------------------------------------------------------------
// What the carved set is closed under
// ---------------------------------------------------------------------------
//
// `integer` cuts a subset out of ℝ, and the three statements here say
// that subset is a SUBRING of it: negation, multiplication and addition
// all keep a real inside. Nothing below mentions ℤ, `real_of_int` or a
// representative — each is an ordinary fact about reals, proved by
// reading the ± characterization at the operands and again at the
// answer, with ℝ's own algebra in between.
//
// These are the facts the operation bridges spend. A bridge's ℝ-side
// answer is built out of its representatives, and the argument that
// THAT answer is again an integer is the bridge's whole own
// mathematics; where the answer negates one representative, or combines
// two, that argument is one of the three below and the bridge is a
// citation. The chapter therefore reads carving → representative →
// closure → bridges.
//
// They are stated here rather than inside a bridge for two reasons that
// agree. What a carved set is closed under is a statement about the
// carving, which is this chapter's subject rather than a step in
// somebody's proof; and a bridge is the wrong home for an argument that
// never mentions the thing the bridge is about — the ℤ operation, or the
// integer whose representative it acts on.

// IntegerClosedUnderNeg — the negation of an integer is an integer.
//
// The shortest of the three, and the only one where the answer's natural
// is the operand's own: r₀ is &n₀ or -&n₀, so -r₀ is -&n₀ or &n₀, and n₀
// witnesses the characterization on either branch. The two branches swap
// places, which is all a negation does to a ± form; the branch that
// arrives already negated is the only one that costs anything, and it
// costs one cancellation.
var IntegerClosedUnderNeg = integerClosedUnderNegThm{family.Add(registry.ProofEntry{
	Name: "IntegerClosedUnderNeg",
	Key:  "prop_52fbc5fa64736afa",
	Build: family.Theorem(Statement{
		Binders: "∀r:real.",
		Hypotheses: []string{
			"integer(r)",
		},
		Conclusion: "integer(-r)",
	},
		func(a *Argument, r Term, rIsInteger Fact) {
			v := ops(a.Ctx())
			negR := v.RealNeg.Apply(r) // -r₀, the answer

			n, rIsPlusMinus := a.Obtain(
				"r is ±&n₀ for some natural n₀",
				"∃n:num. r = &n ∨ r = -&n",
				By(rIsInteger, IntegerIffPlusMinusNat))

			negIsPlusMinus := a.Have(
				"negating exchanges the two branches and keeps the natural",
				"-r = &n ∨ -r = -&n",
				// Normalized: both branches are the operand's own equation with
				// a sign written on it, so the two premises meet the goal by
				// rewriting rather than by refutation, and no key is recorded.
				By(
					Normalized,
					rIsPlusMinus,
					// --&n₀ = &n₀, which turns the already-negated branch back
					// into the plus one. The other branch is its equation
					// negated as it stands.
					At(real_ring.NegNeg, v.RealOfNum.Apply(n)),
				))

			a.Show(
				"and being ±a natural is what being an integer means",
				By(negIsPlusMinus, At(IntegerIffPlusMinusNat, negR)))
		}),
})}

// IntegerClosedUnderMul — the product of two integers is an integer.
//
// The schoolbook sign rule. Both factors are ±a natural, so the product
// is ± the product of those two naturals — and the witness m₀ · n₀ is the
// SAME whichever way the four sign patterns fall, which is why no case
// split appears. The patterns are instead the ground instances in the
// claim's premise list, read in order: both plus, one minus each way, and
// both minus, that last one taking two lines because its two minus signs
// come off one at a time.
var IntegerClosedUnderMul = integerClosedUnderMulThm{family.Add(registry.ProofEntry{
	Name: "IntegerClosedUnderMul",
	Key:  "prop_ed6519845daa1595",
	Build: family.Theorem(Statement{
		Binders: "∀r s:real.",
		Hypotheses: []string{
			"integer(r)",
			"integer(s)",
		},
		Conclusion: "integer(r * s)",
	},
		func(a *Argument, r, s Term, rIsInteger, sIsInteger Fact) {
			v := ops(a.Ctx())

			m, rIsPlusMinus := a.Obtain(
				"r is ±&m₀ for some natural m₀",
				"∃m:num. r = &m ∨ r = -&m",
				By(rIsInteger, IntegerIffPlusMinusNat))
			n, sIsPlusMinus := a.Obtain(
				"and s is ±&n₀ for some natural n₀",
				"∃n:num. s = &n ∨ s = -&n",
				By(sIsInteger, IntegerIffPlusMinusNat))

			rm := v.RealOfNum.Apply(m)            // &m₀
			rn := v.RealOfNum.Apply(n)            // &n₀
			natProduct := v.RealMul.Apply(rm, rn) // &m₀ * &n₀

			productIsPlusMinus := a.Have(
				"however the two signs fall, the product is ±&(m · n) — one witness serves all four",
				"r * s = &(m * n) ∨ r * s = -&(m * n)",
				By(
					rIsPlusMinus,
					sIsPlusMinus,
					// &(m₀ · n₀) = &m₀ · &n₀ — both signs +, and the
					// natural the other three patterns are measured against.
					At(real_construction.OfNumMul, m, n),
					// &m₀ · -&n₀ = -(&m₀ · &n₀) — one sign negative.
					At(real_ring.MulRightNeg, rm, rn),
					// -&m₀ · &n₀ = -(&m₀ · &n₀) — the mirror of it.
					At(real_ring.MulLeftNeg, rm, rn),
					// -&m₀ · -&n₀ = -(&m₀ · -&n₀), which the premise above
					// rewrites to --(&m₀ · &n₀) …
					At(real_ring.MulLeftNeg, rm, v.RealNeg.Apply(rn)),
					// … and --(&m₀ · &n₀) = &m₀ · &n₀ turns both-negative
					// back into the positive disjunct.
					At(real_ring.NegNeg, natProduct),
				))

			a.Show(
				"and being ±a natural is what being an integer means",
				By(productIsPlusMinus, At(IntegerIffPlusMinusNat, v.RealMul.Apply(r, s))))
		}),
})}

// IntegerClosedUnderAdd — the sum of two integers is an integer.
//
// Stated like its multiplicative twin and proved completely differently,
// because addition has no single witness. Both summands are ±a natural,
// and the four sign patterns do NOT share an answer: like signs give
// ±&(m₀ + n₀), unlike signs give a DIFFERENCE of naturals, whose sign is
// whichever of the two is larger. So the four patterns are four cases
// here, and two of them route through the fact below.
//
// That fact — a difference of naturals is an integer — is where the ℕ
// order enters the chapter, and it is the only place it does: comparing
// m₀ and n₀ is what names the gap d₀ that the difference turns out to be
// ∓. Above the gap the argument is pure additive-group rearrangement, one
// axiom per step.
var IntegerClosedUnderAdd = integerClosedUnderAddThm{family.Add(registry.ProofEntry{
	Name: "IntegerClosedUnderAdd",
	Key:  "prop_a693395240aacc1d",
	Build: family.Sections(Statement{
		Binders: "∀r s:real.",
		Hypotheses: []string{
			"integer(r)",
			"integer(s)",
		},
		Conclusion: "integer(r + s)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			natDifferenceIsInteger := ctx.Lemma("∀m n:num. integer(&m + -&n)",
				func(a *Argument, m, n Term) {
					rm := v.RealOfNum.Apply(m)               // &m₀
					rn := v.RealOfNum.Apply(n)               // &n₀
					negRm := v.RealNeg.Apply(rm)             // -&m₀
					negRn := v.RealNeg.Apply(rn)             // -&n₀
					difference := v.RealAdd.Apply(rm, negRn) // &m₀ + -&n₀

					differenceIsPlusMinus := a.Have(
						"the smaller cancels off entirely, leaving ∓ the gap between them",
						"∃k:num. &m + -&n = &k ∨ &m + -&n = -&k",
						Derive(func(a *Argument) {
							// Cited bare: the claim IS totality at (m₀, n₀), so
							// the cite closes on it outright and has no witness
							// slot left over.
							comparable := a.Have(
								"one of m, n is at most the other",
								"m ≤ n ∨ n ≤ m",
								Cite(nat_order.LessEqTotal))

							a.Do(comparable.SplitDisj(
								LeftHolds(
									"m₀ ≤ n₀ — n₀ is m₀ plus a gap d₀, and the difference is -&d₀",
									Given(func(a *Argument, mAtMostN Fact) {
										d, gap := a.Obtain(
											"name the gap up from m₀ to n₀",
											"∃d:num. n₀ = m₀ + d",
											By(mAtMostN, nat_order.LessEqExists))
										negRd := v.RealNeg.Apply(v.RealOfNum.Apply(d)) // -&d₀

										a.Take(d)
										a.Show(
											"&m₀ + -(&m₀ + &d₀) regroups to (&m₀ + -&m₀) + -&d₀, and the unit falls away",
											By(
												gap,
												At(real_construction.OfNumAdd, m, d), // &(m₀ + d₀) = &m₀ + &d₀
												At(real_ring.NegAdd, rm, v.RealOfNum.Apply(d)),   // -(&m₀ + &d₀) = -&m₀ + -&d₀
												At(real_construction.AddAssoc, rm, negRm, negRd), // &m₀ + (-&m₀ + -&d₀) = &m₀ + -&m₀ + -&d₀
												At(real_construction.AddSym, rm, negRm),          // &m₀ + -&m₀ = -&m₀ + &m₀
												At(real_construction.AddLeftInv, rm),             // -&m₀ + &m₀ = &0
												real_construction.AddLeftId,
											))
									})),

								RightHolds(
									"n₀ ≤ m₀ — m₀ is n₀ plus a gap d₀, and the difference is &d₀ itself",
									Given(func(a *Argument, nAtMostM Fact) {
										d, gap := a.Obtain(
											"name the gap up from n₀ to m₀",
											"∃d:num. m₀ = n₀ + d",
											By(nAtMostM, nat_order.LessEqExists))
										rd := v.RealOfNum.Apply(d)         // &d₀
										shifted := v.RealAdd.Apply(rn, rd) // &n₀ + &d₀

										a.Take(d)
										a.Show(
											"(&n₀ + &d₀) + -&n₀ commutes the -&n₀ to the front, where it cancels &n₀",
											By(
												gap,
												At(real_construction.OfNumAdd, n, d), // &(n₀ + d₀) = &n₀ + &d₀
												At(real_construction.AddSym, shifted, negRn),  // (&n₀ + &d₀) + -&n₀ = -&n₀ + (&n₀ + &d₀)
												At(real_construction.AddAssoc, negRn, rn, rd), // -&n₀ + (&n₀ + &d₀) = -&n₀ + &n₀ + &d₀
												At(real_construction.AddLeftInv, rn),          // -&n₀ + &n₀ = &0
												real_construction.AddLeftId,
											))
									})),
							))
						}))

					a.Show(
						"and being ±a natural is what being an integer means",
						By(differenceIsPlusMinus, At(IntegerIffPlusMinusNat, difference)))
				})

			return ctx.Theorem(headline,
				func(a *Argument, r, s Term, rIsInteger, sIsInteger Fact) {
					m, rIsPlusMinus := a.Obtain(
						"r is ±&m₀ for some natural m₀",
						"∃m:num. r = &m ∨ r = -&m",
						By(rIsInteger, IntegerIffPlusMinusNat))
					n, sIsPlusMinus := a.Obtain(
						"and s is ±&n₀ for some natural n₀",
						"∃n:num. s = &n ∨ s = -&n",
						By(sIsInteger, IntegerIffPlusMinusNat))

					rm := v.RealOfNum.Apply(m)   // &m₀
					rn := v.RealOfNum.Apply(n)   // &n₀
					sum := v.RealAdd.Apply(r, s) // r₀ + s₀

					a.Do(rIsPlusMinus.SplitDisj(
						LeftHolds(
							"r₀ = &m₀ — the first summand is a natural, and s₀'s sign decides sum or difference",
							Given(func(a *Argument, rIsNat Fact) {
								a.Do(sIsPlusMinus.SplitDisj(
									LeftHolds(
										"s₀ = &n₀ — like signs: the sum is the natural &(m₀ + n₀)",
										Given(func(a *Argument, sIsNat Fact) {
											a.Show(
												"&m₀ + &n₀ IS &(m₀ + n₀), which the ± characterization accepts on its first disjunct",
												By(
													rIsNat,
													sIsNat,
													At(real_construction.OfNumAdd, m, n), // &(m₀ + n₀) = &m₀ + &n₀
													At(IntegerIffPlusMinusNat, sum)))
										})),
									RightHolds(
										"s₀ = -&n₀ — unlike signs: the sum is the difference &m₀ - &n₀",
										Given(func(a *Argument, sIsNegNat Fact) {
											a.Show(
												"a difference of naturals is an integer, at (m₀, n₀)",
												By(Normalized, rIsNat, sIsNegNat, At(natDifferenceIsInteger, m, n))) // integer(&m₀ + -&n₀)
										})),
								))
							})),

						RightHolds(
							"r₀ = -&m₀ — the first summand is a negated natural, and the two sub-cases swap roles",
							Given(func(a *Argument, rIsNegNat Fact) {
								a.Do(sIsPlusMinus.SplitDisj(
									LeftHolds(
										"s₀ = &n₀ — unlike signs the other way round: the difference &n₀ - &m₀",
										Given(func(a *Argument, sIsNat Fact) {
											a.Show(
												"commuting the summands puts it in the shape the difference fact is stated in",
												By(
													rIsNegNat,
													sIsNat,
													At(natDifferenceIsInteger, n, m), // integer(&n₀ + -&m₀)
													At(real_construction.AddSym, v.RealNeg.Apply(rm), rn))) // -&m₀ + &n₀ = &n₀ + -&m₀
										})),
									RightHolds(
										"s₀ = -&n₀ — like signs again, both negative: the sum is -&(m₀ + n₀)",
										Given(func(a *Argument, sIsNegNat Fact) {
											a.Show(
												"the two minus signs come out together, leaving -&(m₀ + n₀)",
												By(
													rIsNegNat,
													sIsNegNat,
													At(real_ring.NegAdd, rm, rn),         // -(&m₀ + &n₀) = -&m₀ + -&n₀
													At(real_construction.OfNumAdd, m, n), // &(m₀ + n₀) = &m₀ + &n₀
													At(IntegerIffPlusMinusNat, sum)))
										})),
								))
							})),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// `real_of_int` carries each ℤ operation to its ℝ counterpart
// ---------------------------------------------------------------------------
//
// A bridge is not a computation. Every operation on ℤ is *defined* by
// transport — `int_neg(x)` IS the integer representing `-real_of_int(x)`,
// `int_of_num(n)` the one representing `&n` — so unfolding that
// definition turns the homomorphism law into
// `real_of_int(int_of_real(t)) = t` for the operation's ℝ-side answer
// `t`, and that equation is TypeBijection's membership half read at `t`.
//
// What is left over is the whole of a bridge's own mathematics: the
// argument that `t` is again an integer. Each member below is that
// argument, then one citation of TypeBijection. Where `t` is built by
// combining or negating representatives rather than selecting one, that
// argument is not about representatives at all and is stated in
// the closure part above; the bridge then cites it and the member is two lines.
// Nothing here realizes a typedef axiom or rebuilds the type: that
// happens once in the chapter, inside TypeBijection, and every member
// below reads it from there.
//
// All nine are stated in ONE orientation, `real_of_int(<the ℤ operation>)
// = <the ℝ operation of the representatives>`. Which side of the equation
// is written first is free — `Normalize` canonicalizes `=` by a term
// ordering — and BINDER ORDER is free the same way. A headline here is
// written the way it should be read.
//
// The bridge for ℤ's POWER is not here: int_pow is a derived operation
// rather than construction material — nothing below needs it — so its
// transfer theorem lives with the rest of the power chapter,
// int_num/int_pow, which imports this chapter's closure laws.

// OfNumBridge — the two `&`s agree: the integer named by a natural
// represents that natural's real.
//
// The shortest closure argument the chapter has, because there is no
// representative in it. The ℝ-side answer is `&n`, which is an integer
// for the most direct reason available — the ± characterization is
// satisfied by its first disjunct, at that very n — so the argument that
// the answer is an integer collapses into the membership step and the
// member is a single close. Neither premise can be dropped, and
// RepresentativeIsInteger cannot serve here: `&n` is nobody's
// representative until this very theorem says whose.
var OfNumBridge = ofNumBridgeThm{family.Add(registry.ProofEntry{
	Name: "OfNumBridge",
	Key:  "prop_37449bb5e7f8370b",
	Build: family.Theorem("∀n:num. real_of_int(n) = &n",
		func(a *Argument) {
			// ↦ ∀n. real_of_int(int_of_real(&n)) = &n
			a.Do(Unfold(IntOfNumDef))

			a.Show(
				"&n is an integer, so it survives the trip up into ℤ and back",
				By(TypeBijection, IntegerIffPlusMinusNat))
		}),
})}

// NegBridge — negating an integer negates its representative.
//
// The first bridge that needs a closure law: the ℝ-side answer is
// `-real_of_int(x)`, and there is no reading of a representative's own
// shape that says a negation is an integer — that is a statement about
// what ℤ is closed under, and the closure part above states it. So the argument here
// is the representative's membership, handed to that law.
var NegBridge = negBridgeThm{family.Add(registry.ProofEntry{
	Name: "NegBridge",
	Key:  "prop_d0f5e19673fe725d",
	Build: family.Theorem("∀x:int. real_of_int(int_neg(x)) = -real_of_int(x)",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			rep := v.RealOfInt.Apply(x) // real_of_int(x₀)

			// ↦ real_of_int(int_of_real(-real_of_int(x₀))) = -real_of_int(x₀)
			a.Do(Unfold(IntNegDef))

			negIsInteger := a.Have(
				"the representative is an integer, and integers negate to integers",
				MakeProp(v.Integer.Apply(v.RealNeg.Apply(rep))),
				By(
					At(RepresentativeIsInteger, x), // integer(real_of_int(x₀))
					// integer(r) ⇒ integer(-r), at that representative.
					At(IntegerClosedUnderNeg, rep),
				))

			a.Show(
				"being an integer, the negated representative comes back unchanged",
				By(negIsInteger, TypeBijection))
		}),
})}

// MaxBridge — the larger of two integers represents the larger of their
// representatives.
//
// The cheapest closure argument the chapter has where a representative
// appears at all: `real_max` is a conditional that SELECTS one of its two
// arguments, so the ℝ-side answer is one of the two representatives
// themselves, and a representative is an integer. Which comparison holds
// is never decided, and never needs to be — both candidates are cited, so
// either branch of the conditional is covered.
var MaxBridge = maxBridgeThm{family.Add(registry.ProofEntry{
	Name: "MaxBridge",
	Key:  "prop_ea2df5c851b11098",
	Build: family.Theorem("∀x y:int. real_of_int(max(x, y)) = max(real_of_int(x), real_of_int(y))",
		func(a *Argument, x, y Term) {
			// ↦ real_of_int(int_of_real(real_max(real_of_int(x₀), real_of_int(y₀))))
			// = real_max(real_of_int(x₀), real_of_int(y₀))
			a.Do(Unfold(IntMaxDef))

			maxIsInteger := a.Have(
				"whichever of the two representatives real_max selects is an integer",
				"integer(max(real_of_int(x), real_of_int(y)))",
				// ↦ integer(COND(real_of_int(x₀) ≤ real_of_int(y₀), real_of_int(y₀), real_of_int(x₀))) —
				// the two candidates the premises are read at.
				Unfold(real_sup_inf.RealMaxDef),
				By(
					At(RepresentativeIsInteger, x), // integer(real_of_int(x₀))
					At(RepresentativeIsInteger, y), // integer(real_of_int(y₀))
				))

			a.Show(
				"being an integer, the selected representative comes back unchanged",
				By(maxIsInteger, TypeBijection))
		}),
})}

// MinBridge — the smaller of two integers represents the smaller of their
// representatives.
//
// `real_min` is the same conditional on the same comparison, reading off
// the other branch, so the argument above applies unchanged: the answer is
// again one of the two representatives, and the proof does not care which.
var MinBridge = minBridgeThm{family.Add(registry.ProofEntry{
	Name: "MinBridge",
	Key:  "prop_68e0ef04200866f6",
	Build: family.Theorem("∀x y:int. real_of_int(min(x, y)) = min(real_of_int(x), real_of_int(y))",
		func(a *Argument, x, y Term) {
			// ↦ real_of_int(int_of_real(real_min(real_of_int(x₀), real_of_int(y₀))))
			// = real_min(real_of_int(x₀), real_of_int(y₀))
			a.Do(Unfold(IntMinDef))

			minIsInteger := a.Have(
				"whichever of the two representatives real_min selects is an integer",
				"integer(min(real_of_int(x), real_of_int(y)))",
				// ↦ integer(COND(real_of_int(x₀) ≤ real_of_int(y₀), real_of_int(x₀), real_of_int(y₀)))
				Unfold(real_sup_inf.RealMinDef),
				By(
					At(RepresentativeIsInteger, x), // integer(real_of_int(x₀))
					At(RepresentativeIsInteger, y), // integer(real_of_int(y₀))
				))

			a.Show(
				"being an integer, the selected representative comes back unchanged",
				By(minIsInteger, TypeBijection))
		}),
})}

// SgnBridge — the sign of an integer represents the sign of its
// representative.
//
// The one bridge whose answer is chosen from a fixed set of constants
// rather than computed: a sign is -&1, &0 or &1, which is exactly what
// `real_sgn_abs.SgnTrichotomy` says. So the closure argument does not
// mention the representative either — the trichotomy names the three
// candidates, and the ± characterization read once at each of them says
// every candidate is a natural or the negation of one on its face.
// `real_sgn` itself is never unfolded: opening the definition's own
// guards here would repeat the trichotomy's analysis, which is done
// once where it belongs.
var SgnBridge = sgnBridgeThm{family.Add(registry.ProofEntry{
	Name: "SgnBridge",
	Key:  "prop_8e8f3b8f2d2953a1",
	Build: family.Theorem("∀x:int. real_of_int(sgn(x)) = sgn(real_of_int(x))",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())

			// The three values a sign can take.
			one := v.RealOfNum.Apply(a.Ctx().Numeral(1))  // &1
			negOne := v.RealNeg.Apply(one)                // -&1
			zero := v.RealOfNum.Apply(a.Ctx().Numeral(0)) // &0
			rep := v.RealOfInt.Apply(x)                   // real_of_int(x₀)

			// ↦ real_of_int(int_of_real(real_sgn(real_of_int(x₀))))
			// = real_sgn(real_of_int(x₀))
			a.Do(Unfold(IntSgnDef))

			sgnIsInteger := a.Have(
				"the sign takes one of three values, each ±a natural",
				"integer(sgn(real_of_int(x)))",
				By(
					At(real_sgn_abs.SgnTrichotomy, rep), // sgn(real_of_int(x₀)) = -&1 ∨ &0 ∨ &1
					At(IntegerIffPlusMinusNat, one),     // integer(&1) ⇔ &1 is ±a natural
					At(IntegerIffPlusMinusNat, negOne),  // integer(-&1) ⇔ -&1 is ±a natural
					At(IntegerIffPlusMinusNat, zero),    // integer(&0) ⇔ &0 is ±a natural
				))

			a.Show(
				"being an integer, the sign comes back unchanged",
				By(sgnIsInteger, TypeBijection))
		}),
})}

// AbsBridge — the absolute value of an integer represents the absolute
// value of its representative.
//
// MaxBridge and MinBridge read their answer off one of the
// representatives, and SgnBridge's is a constant; an absolute value is
// neither, so this is the one bridge that has to open the
// representative's own ± form: the representative is &n or -&n, and
// taking absolute values sends both to the same &n — the first because a
// natural is its own absolute value, the second because the sign comes
// off first. That &n is then a natural, which is the ± characterization's
// first disjunct, read at the absolute value.
//
// `real_abs` is not unfolded anywhere: the two ℝ laws say everything this
// argument needs about it, and its conditional never has to be opened.
var AbsBridge = absBridgeThm{family.Add(registry.ProofEntry{
	Name: "AbsBridge",
	Key:  "prop_9d0a6876782c49c0",
	Build: family.Theorem("∀x:int. real_of_int(|x|) = |real_of_int(x)|",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())

			// |real_of_int(x)|: the ℝ-side answer, and the term the claim and
			// its first premise are both read at.
			absRep := v.RealAbs.Apply(v.RealOfInt.Apply(x))

			// ↦ real_of_int(int_of_real(real_abs(real_of_int(x₀))))
			// = real_abs(real_of_int(x₀))
			a.Do(Unfold(IntAbsDef))

			absIsInteger := a.Have(
				"x's representative is ±a natural, and its absolute value IS that natural",
				MakeProp(v.Integer.Apply(absRep)),
				By(
					// integer(|real_of_int(x₀)|) ⇔ |real_of_int(x₀)| is ±a natural
					At(IntegerIffPlusMinusNat, absRep),
					// real_of_int(x₀) = &n or -&n, for some n
					At(RepresentativeIsPlusMinusNat, x),
					// |&n| = &n and |-&n| = |&n|, which is what makes the two
					// disjuncts give the same absolute value. Cited bare: the n
					// they are needed at is the witness of the premise above, so
					// there is no term here to ground them with.
					real_sgn_abs.AbsOfNum,
					real_sgn_abs.AbsEven,
				))

			a.Show(
				"being an integer, the absolute value comes back unchanged",
				By(absIsInteger, TypeBijection))
		}),
})}

// MulBridge — the product of two integers represents the product of their
// representatives.
//
// The first bridge whose ℝ answer needs BOTH representatives at once, so
// the first whose closure argument cannot look at either one's shape: what
// it needs is that ℤ, as a subset of ℝ, is closed under multiplication.
// With that stated above the bridge reads it at the two
// representatives and discharges its two guards with the fact that a
// representative is an integer.
var MulBridge = mulBridgeThm{family.Add(registry.ProofEntry{
	Name: "MulBridge",
	Key:  "prop_ad59b3567ce07c64",
	Build: family.Theorem("∀x y:int. "+
		"    real_of_int(int_mul(x, y)) = real_mul(real_of_int(x), real_of_int(y))",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			rx := v.RealOfInt.Apply(x)
			ry := v.RealOfInt.Apply(y)

			// ↦ real_of_int(int_of_real(real_of_int(x₀) * real_of_int(y₀)))
			// = real_of_int(x₀) * real_of_int(y₀)
			a.Do(Unfold(IntMulDef))

			productIsInteger := a.Have(
				"both representatives are integers, and integers multiply to integers",
				MakeProp(v.Integer.Apply(v.RealMul.Apply(rx, ry))),
				By(
					// integer(real_of_int(x₀)) and integer(real_of_int(y₀)):
					// one lemma, read at each of the two arguments, so it is
					// cited bare — a ground instance would name only one of
					// the two places it is needed.
					RepresentativeIsInteger,
					// integer(r) ⇒ integer(s) ⇒ integer(r · s), at those two
					// representatives.
					At(IntegerClosedUnderMul, rx, ry),
				))

			a.Show(
				"being an integer, the product comes back unchanged",
				By(productIsInteger, TypeBijection))
		}),
})}

// AddBridge — the sum of two integers represents the sum of their
// representatives.
//
// Shaped exactly like MulBridge, and for the same reason: the ℝ answer
// combines both representatives, so the argument that it is again an
// integer is the additive closure law rather than anything about either
// representative. That the two laws are proved completely differently —
// multiplication has one witness for all four sign patterns, addition has
// four — is invisible from here, which is the point of stating them
// separately.
var AddBridge = addBridgeThm{family.Add(registry.ProofEntry{
	Name: "AddBridge",
	Key:  "prop_c190d9ea28e4b90c",
	Build: family.Theorem("∀x y:int. "+
		"    real_of_int(int_add(x, y)) = real_add(real_of_int(x), real_of_int(y))",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			rx := v.RealOfInt.Apply(x)
			ry := v.RealOfInt.Apply(y)

			// ↦ real_of_int(int_of_real(real_of_int(x₀) + real_of_int(y₀)))
			// = real_of_int(x₀) + real_of_int(y₀)
			a.Do(Unfold(IntAddDef))

			sumIsInteger := a.Have(
				"both representatives are integers, and integers add to integers",
				MakeProp(v.Integer.Apply(v.RealAdd.Apply(rx, ry))),
				By(
					// integer(real_of_int(x₀)) and integer(real_of_int(y₀)):
					// one lemma read at each argument, so cited bare rather
					// than ground at one of the two places it is needed.
					RepresentativeIsInteger,
					// integer(r) ⇒ integer(s) ⇒ integer(r + s), at those two
					// representatives.
					At(IntegerClosedUnderAdd, rx, ry),
				))

			a.Show(
				"being an integer, the sum comes back unchanged",
				By(sumIsInteger, TypeBijection))
		}),
})}

// SubBridge — the difference of two integers represents the difference of
// their representatives.
//
// The only bridge that spends TWO closure laws, and the ℝ side is what
// makes it so: a difference is a sum with a negation, so unfolding
// `real_sub` turns the answer into `r₁ + -r₂` and the additive law is read
// there. Its second guard is then about `-r₂` rather than about a
// representative, and that is the one the negation law supplies.
//
// AddBridge is useless here despite the shape, and that is the clearest
// case for stating the closure laws separately: the ℤ answer is an
// `int_sub`, not an `int_add` of anything, so what this member needs is
// the ℝ-side statement rather than the bridge that also happens to use it.
var SubBridge = subBridgeThm{family.Add(registry.ProofEntry{
	Name: "SubBridge",
	Key:  "prop_6d80e15c8fad3994",
	Build: family.Theorem("∀x y:int. "+
		"    real_of_int(int_sub(x, y)) = real_sub(real_of_int(x), real_of_int(y))",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			rx := v.RealOfInt.Apply(x)   // real_of_int(x₀)
			ry := v.RealOfInt.Apply(y)   // real_of_int(y₀)
			negRy := v.RealNeg.Apply(ry) // -real_of_int(y₀)

			// ↦ real_of_int(int_of_real(real_of_int(x₀) - real_of_int(y₀)))
			// = real_of_int(x₀) - real_of_int(y₀)
			a.Do(Unfold(IntSubDef))

			differenceIsInteger := a.Have(
				"negating the second representative keeps it an integer, and integers add to integers",
				MakeProp(v.Integer.Apply(v.RealSub.Apply(rx, ry))),
				// ↦ integer(real_of_int(x₀) + -real_of_int(y₀)) — a difference
				// is a sum with a negation, and that is the shape both laws
				// below are stated in.
				Unfold(real_ring.RealSubDef),
				By(
					// integer(real_of_int(x₀)) — the additive law's first guard.
					At(RepresentativeIsInteger, x),
					// integer(real_of_int(y₀)) — the negation law's guard.
					At(RepresentativeIsInteger, y),
					// integer(r) ⇒ integer(-r), at the second representative:
					// the additive law's second guard is about -r₂, which is
					// not a statement about any representative.
					At(IntegerClosedUnderNeg, ry),
					// integer(r) ⇒ integer(s) ⇒ integer(r + s), at the first
					// representative and the negation of the second.
					At(IntegerClosedUnderAdd, rx, negRy),
				))

			a.Show(
				"being an integer, the difference comes back unchanged",
				By(differenceIsInteger, TypeBijection))
		}),
})}

// ---------------------------------------------------------------------------
// The comparisons and the absolute value, read back on ℤ
// ---------------------------------------------------------------------------
//
// The bridges carry ℤ's operations DOWN to ℝ. The members here read
// ℝ's definitions BACK on ℤ. A comparison of two integers is, by
// definition, the comparison of their representatives — `x > y` unfolds
// to `real_of_int(x) > real_of_int(y)`, and `≥`, `<`, `≤` likewise — so
// an ℝ definition that reads one comparison symbol as another (`>` as
// `<` reversed, `≥` as `≤` reversed) holds on ℤ verbatim: unfold the ℤ
// symbols and then the ℝ one, and the two sides coincide, with nothing
// left to argue. The absolute value is the one member that needs the
// bridges: `int_abs` is defined by transport, so the conditional that
// characterizes it on ℤ is `real_abs`'s own conditional, read through
// AbsBridge on the left and through NegBridge on the negative arm.

// GreaterIffLess — `x > y` is `y < x`.
//
// Both comparisons are defined through the representatives, and on ℝ
// `>` is `<` read backwards by definition, so the three unfoldings
// leave the two sides identical and the leaf closes at the last one.
var GreaterIffLess = greaterIffLessThm{family.Add(registry.ProofEntry{
	Name: "GreaterIffLess",
	Key:  "prop_d6e853921662c36d",
	Build: family.Theorem("∀x y:int. x > y ⇔ y < x",
		func(a *Argument, x, y Term) {
			a.Do(
				// ↦ real_of_int(x₀) > real_of_int(y₀) ⇔ y₀ < x₀
				Unfold(IntGtDef),
				// ↦ real_of_int(y₀) < real_of_int(x₀) ⇔ y₀ < x₀
				Unfold(real_order_ring.RealGtDef),
				// ↦ real_of_int(y₀) < real_of_int(x₀) on both sides — an
				// identity; the leaf closes here.
				Unfold(IntLtDef),
			)
		}),
})}

// GreaterEqIffLessEq — `x ≥ y` is `y ≤ x`.
//
// GreaterIffLess with the weak comparisons in place of the strict ones,
// and the same proof: the three unfoldings leave the two sides
// identical.
var GreaterEqIffLessEq = greaterEqIffLessEqThm{family.Add(registry.ProofEntry{
	Name: "GreaterEqIffLessEq",
	Key:  "prop_8c7b3b1fffdbf754",
	Build: family.Theorem("∀x y:int. x ≥ y ⇔ y ≤ x",
		func(a *Argument, x, y Term) {
			a.Do(
				Unfold(IntGeDef),
				Unfold(real_order_ring.RealGeDef),
				Unfold(IntLeDef), // ↦ real_of_int(y₀) ≤ real_of_int(x₀) on both sides; the leaf closes here
			)
		}),
})}

// AbsBySign — the absolute value of an integer is the integer itself when
// it is nonnegative, and its negation otherwise.
//
// `int_abs` is defined by transport, so this is `real_abs`'s own
// conditional read back on ℤ. Unfold the ℤ `≤` and read `&0`'s
// representative, and the ℤ conditional on the right is guarded by the
// very sign test `real_abs` opens into; injectivity of the
// representative then moves the equation to ℝ, where AbsBridge reads
// the left side as the representative's absolute value. The two
// conditionals split on that one test: the nonnegative arm is an
// identity, and the negative arm is NegBridge.
var AbsBySign = absBySignThm{family.Add(registry.ProofEntry{
	Name: "AbsBySign",
	Key:  "prop_2c8bf2ad4e7654e5",
	Build: family.Theorem("∀x:int. |x| = COND(&0 ≤ x, x, int_neg(x))",
		func(a *Argument, x Term) {
			a.Do(
				// ↦ int_abs(x₀) = COND(real_of_int(&0) ≤ real_of_int(x₀), x₀, int_neg(x₀)):
				// the ℤ guard is a comparison of representatives.
				Unfold(IntLeDef),
				// Three rewrites, jointly: the representative of ℤ's `&0` is
				// ℝ's `&0`; an equation between integers is the equation between
				// their representatives; the representative of |x₀| is
				// |real_of_int(x₀)|.
				// ↦ real_abs(real_of_int(x₀))
				// = real_of_int(COND(&0 ≤ real_of_int(x₀), x₀, int_neg(x₀)))
				Simp(
					Fwd(OfNumBridge),
					Fwd(RepresentativeInjective),
					// AbsBridge reads the ℤ side, real_of_int(int_abs(x₀)),
					// as the ℝ side.
					Fwd(AbsBridge)),
				// ↦ COND(&0 ≤ r, r, -r) = real_of_int(COND(&0 ≤ r, x₀, int_neg(x₀)))
				// for r = real_of_int(x₀): the two conditionals share one guard.
				Unfold(real_sgn_abs.RealAbsDef),
				// ↦ ¬(&0 ≤ r) ⇒ -r = real_of_int(int_neg(x₀)). The nonnegative
				// arm, r = r, closed itself.
				CondRewrite(),
				// ↦ ¬(&0 ≤ r) ⇒ -r = -r, NegBridge reading the ℤ side as the ℝ side.
				Simp(Fwd(NegBridge)),
				TrivialNormalized(),
			)
		}),
})}
