// division.go — the chapter, part one: the algorithm and what it computes.
//
// Seven parts, marked by banners:
//
// - What integer division and remainder ARE
// - Every dividend has a quotient and a remainder
// - What the specification says
// - The subgroups of ℤ
// - The division algorithm's answer is the only answer
// - Where the chapter starts paying
// - Division survives the embedding

package int_div_rem

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// What integer division and remainder ARE
// ---------------------------------------------------------------------------
//
// `int_div` and `int_rem` arrive by CHOICE, not by construction: the division
// algorithm hands out a quotient and a remainder at every point, and
// the two constants name one such assignment. This file is the step
// between those two sentences — turning a per-point existence
// statement that mentions no constant into the ε-free specification
// the constants satisfy everywhere, which is what the rest of the
// chapter reads.
//
// It stands alone deliberately: a constant introduction is the one
// definitional act in the chapter, and keeping it apart from the
// statements it enables keeps the reading order honest — first what
// the constants ARE, then what follows from that.

// divRemSpec is the division algorithm stated as a property of `int_div`
// and `int_rem`. At a nonzero divisor it is the classical statement: the
// quotient/remainder equation together with the bound that pins the
// pair uniquely. At the zero divisor no such pair exists, so the other
// branch records the convention the constants were chosen under
// instead — which is what makes the specification TOTAL, and why the
// chapter's laws can be stated without a nonzero-divisor guard.
//
// The two constants arrive through the define door's spec shape: the
// author's surfaces are the specification and the pointwise existence
// it rests on (divModExists, one cite); the ε-witness packaging, the
// name-tag conditioning and the two nested definitional bridges run
// inside the composite.
//
// The divisor leads the binder prefix because the specification
// branches on it.
//
// Chapter machinery.
var divRemSpec = divRemSpecThm{family.DefineSpec(registry.SpecEntry{
	Name: "divRemSpec",
	Key:  "prop_b1c2d05d5806f0f0",
	Consts: []registry.SpecConst{
		{Const: "int_div", Type: "int → int → int", Overload: "div"},
		{Const: "int_rem", Type: "int → int → int", Overload: "rem"},
	},
	Spec: "∀n m:int. COND(n = &0, m = int_rem(m, n) ∧ int_div(m, n) = &0, m = " +
		"int_div(m, n) * n + int_rem(m, n) ∧ &0 ≤ int_rem(m, n) ∧ int_rem(m, n) < |n|)",
	Deps: []registry.EntryLike{divModExists},
	// The obligation IS divModExists' statement.
	Existence: []Action{Cite(divModExists)},
})}

// ---------------------------------------------------------------------------
// Every dividend has a quotient and a remainder
// ---------------------------------------------------------------------------
//
// Dividing m by a nonzero n means writing m as a multiple of n plus a
// leftover that is neither negative nor as big as |n|. That such a
// leftover EXISTS is the one genuinely infinitary step of the division
// algorithm, and it rests on two properties of ℤ. Multiples of a
// nonzero n reach arbitrarily far, so SOME nonnegative leftover is
// available at all; and every nonempty set of nonnegative integers has
// a least member, so a SMALLEST one can be picked. The smallest one is
// automatically small enough: otherwise one more |n| could come off it
// and it would not have been smallest.
//
// At a zero divisor there is no such leftover, and the statement
// records the convention chosen there instead — which is what makes it
// hold at every point, and what the rest of the chapter reads.
//
// It stands alone deliberately: this is the chapter's one analytic
// argument, the only place `int_embed.Archimedean` and
// `int_embed.WellOrderedBelow` are used and the only proof here that
// is not a few lines read off something below it. Every other member
// of the chapter is finite algebra.

// divModExists is the division algorithm before any constant names its
// answer: a quotient and a remainder are asserted to exist at every
// point, and nothing yet picks one out.
//
// Internal to the chapter: its only consumers are the constant
// introduction that reads a choice function off it and, through that,
// everything downstream.
var divModExists = divModExistsThm{family.Add(registry.ProofEntry{
	Name: "divModExists",
	Key:  "prop_bbb1df60f11bb98e",
	// The divisor leads the binder prefix, as it does in the specification
	// this theorem is consumed by: everything below branches on it.
	Build: family.Sections(
		"∀n m:int. ∃q r:int. COND(n = &0, m = r ∧ q = &0, m = q * n + r ∧ &0 ≤ r ∧ r < |n|)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			intT := MakeType("int")
			// Negation, subtraction, and the two literals: the argument
			// compares a leftover with the one a divisor below it, reaches
			// for the far side of &0 to start, and moves the quotient by
			// one copy either way.
			neg, sub := v.Neg, v.Sub
			zero, one := v.Zero, v.One

			add := func(a, b Term) *TermWrapper { return v.Add.Apply(a, b) }
			mul := func(a, b Term) Term { return v.Mul.Apply(a, b) }
			le := func(a, b Term) Term { return v.Le.Apply(a, b) }
			lt := func(a, b Term) Term { return v.Lt.Apply(a, b) }
			abs := func(a Term) Term { return v.Abs.Apply(a) }

			// Bound variables for the claims built below; the argument's own
			// quantities all arrive as closure parameters instead.
			qv := ctx.Var("q", intT)
			sv := ctx.Var("s", intT)
			xv := ctx.Var("x", intT)
			yv := ctx.Var("y", intT)

			// isLeftover(m, n, t) — "t is what m leaves over n", i.e. m sits
			// t above some multiple of n. This is the predicate the whole
			// argument is about: the existence claim asks for one of these
			// that is also nonnegative and small, and well-ordering is
			// applied to exactly this set.
			isLeftover := func(m *TermWrapper, n, t Term) *TermWrapper {
				return Exists(qv)(m.Eq(add(mul(n, qv), t)))
			}

			// A leftover survives being decreased by the divisor's size:
			// take |n| off it, and pay for it in the quotient. Which way the
			// quotient moves is the only thing the divisor's sign decides,
			// and it is the only place in this file that a sign is examined.
			shiftDown := ctx.Lemma(
				Statement{
					Binders: "∀n m x:int.",
					Hypotheses: []string{
						"∃q:int. m = n * q + x",
					},
					Conclusion: "∃q:int. m = n * q + (x - |n|)",
				},
				func(a *Argument, n, m, x Term, leftover Fact) {
					q, decomp := a.Unpack(leftover) // m = n * q₀ + x
					nq := mul(n, q)

					a.Cases(le(zero, n))
					a.When(
						"n nonnegative: |n| is n itself, and the quotient takes one more copy of it",
						func(a *Argument, nonneg Fact) {
							a.Take(add(q, one))
							a.Show(
								"n * (q₀ + &1) + (x - n) collapses to n * q₀ + x",
								By(
									decomp,
									nonneg,
									At(int_construction.AbsBySign, n),        // int_abs(n) = COND(&0 ≤ n, n, -n)
									At(int_real_lift.LeftDistrib, n, q, one), // n * (q₀ + &1) = n * q₀ + n * &1
									At(int_real_lift.MulRightIdentity, n),    // n * &1 = n
									// (n * q₀ + n) + (x - n) = n * q₀ + (n + (x - n))
									At(int_real_lift.AddAssoc, nq, n, sub.Apply(x, n)),
									int_real_lift.SubAddLeft))
						})
					a.Otherwise(
						"n negative: |n| is -n, so the shift adds n — still downward — and the quotient gives one copy up",
						func(a *Argument, negative Fact) {
							a.Take(sub.Apply(q, one))
							a.Show(
								"n * (q₀ - &1) + (x + n) collapses to n * q₀ + x",
								By(
									decomp,
									negative,
									At(int_construction.AbsBySign, n),   // int_abs(n) = COND(&0 ≤ n, n, -n)
									At(int_real_lift.SubRightNeg, x, n), // x - -n = x + n
									At(int_real_lift.SubLeftDistrib, n, q, one), // n * (q₀ - &1) = n * q₀ - n * &1
									At(int_real_lift.MulRightIdentity, n),       // n * &1 = n
									At(int_real_lift.AddSym, x, n),              // x + n = n + x
									// ((n * q₀ - n) + n) + x = (n * q₀ - n) + (n + x)
									At(int_real_lift.AddAssoc, sub.Apply(nq, n), n, x),
									At(int_real_lift.SubAddRight, nq, n))) // (n * q₀ - n) + n = n * q₀
						})
				})

			// There is a nonnegative leftover to begin with. Multiples of a
			// nonzero n climb past any bound, so one of them climbs past -m;
			// adding m back to that multiple lands at or above &0, and the
			// multiple's own negative is the quotient that puts it there.
			inhabited := ctx.Lemma(
				Statement{
					Binders: "∀n m:int.",
					Hypotheses: []string{
						"n ≠ &0",
					},
					Conclusion: "∃r:int. (∃q:int. m = n * q + r) ∧ &0 ≤ r",
				},
				func(a *Argument, n Term, m *TermWrapper, nonZero Fact) {
					negM := neg.Apply(m)

					s, overshoot := a.Obtain(
						"some multiple of n climbs past -m",
						MakeProp(Exists(sv)(lt(negM, mul(sv, n)))),
						By(nonZero, At(int_embed.Archimedean, n, negM))) // n ≠ &0 ⇒ ∃c. -m < c * n

					sn := mul(s, n)
					rest := add(m, sn)           // the leftover m + s₀ * n
					undo := mul(n, neg.Apply(s)) // the multiple m sits that leftover above

					nonneg := a.Have(
						"adding m back to that multiple lands at or above &0",
						MakeProp(le(zero, rest)),
						By(
							overshoot,
							At(int_real_lift.LessThanAddLeftImp, m, negM, sn), // -m < s₀ * n ⇒ m + -m < m + s₀ * n
							At(int_real_lift.AddRightInverse, m),              // m + -m = &0
							At(int_real_lift.LessEqOfLessThan, zero, rest)))   // &0 < m + s₀ * n ⇒ &0 ≤ m + s₀ * n

					cancels := a.Have(
						"and -s₀ is the quotient that undoes the climb exactly",
						MakeProp(add(undo, sn).Eq(zero)),
						By(
							At(int_real_lift.MulRightNeg, n, s),   // n * -s₀ = -(n * s₀)
							At(int_real_lift.MulSym, n, s),        // n * s₀ = s₀ * n
							At(int_real_lift.AddLeftInverse, sn))) // -(s₀ * n) + s₀ * n = &0

					decomp := a.Have(
						"so m sits that leftover above the multiple n * -s₀",
						MakeProp(m.Eq(add(undo, rest))),
						By(
							cancels,
							At(int_real_lift.AddAssoc, undo, m, sn), // (n * -s₀ + m) + s₀ * n = n * -s₀ + (m + s₀ * n)
							At(int_real_lift.AddSym, undo, m),       // n * -s₀ + m = m + n * -s₀
							At(int_real_lift.AddAssoc, m, undo, sn), // (m + n * -s₀) + s₀ * n = m + (n * -s₀ + s₀ * n)
							At(int_real_lift.AddRightIdentity, m)))  // m + &0 = m

					a.Show(
						"m + s₀ * n is the leftover asked for",
						By(decomp, nonneg))
				})

			// The LEAST nonnegative leftover is already below |n|. If it
			// were not, shiftDown would hand back another nonnegative
			// leftover, |n| lower — so |n| would have to come out at or
			// below &0, which at a nonzero divisor it does not.
			small := ctx.Lemma(
				"∀n m x:int. "+
					"    n ≠ &0 ⇒ "+
					"    (∃q:int. m = n * q + x) ⇒ "+
					"    (∀y:int. (∃q:int. m = n * q + y) ∧ &0 ≤ y ⇒ x ≤ y) ⇒ "+
					"    x < |n|",
				func(a *Argument, n Term, m *TermWrapper, x Term, nonZero, leftover, least Fact) {
					absN := abs(n)
					lower := sub.Apply(x, absN) // the leftover one |n| below x

					notSmall := a.SupposeNot() // ¬(x < int_abs(n))

					reaches := a.Have(
						"x would then reach |n|",
						MakeProp(le(absN, x)),
						By(notSmall, int_real_lift.NotLessThan))

					stillNonneg := a.Have(
						"so x - |n| is still nonnegative",
						MakeProp(le(zero, lower)),
						By(reaches, int_real_lift.SubNonneg))

					stillLeftover := a.Have(
						"and still a leftover of m over n",
						MakeProp(isLeftover(m, n, lower)),
						By(leftover, At(shiftDown, n, m, x)))

					notLeast := a.Have(
						"which x, being least, would have to sit at or below",
						MakeProp(le(x, lower)),
						By(stillNonneg, stillLeftover, least.At(lower)))

					vanishes := a.Have(
						"but a step down that does not go down is a step of size at most &0",
						MakeProp(le(absN, zero)),
						By(
							notLeast,
							At(int_real_lift.LessEqSubAddLeft, x, x, absN), // x ≤ x - int_abs(n) ⇔ x + int_abs(n) ≤ x
							At(int_real_lift.AddSym, x, absN),              // x + int_abs(n) = int_abs(n) + x
							At(int_real_lift.LessEqSubAddLeft, absN, x, x), // int_abs(n) ≤ x - x ⇔ int_abs(n) + x ≤ x
							At(int_real_lift.SubRefl, x)))                  // x - x = &0

					a.Show(
						"and a nonzero divisor's size is positive, which a size at most &0 is not",
						By(
							vanishes,
							nonZero,
							At(int_real_lift.AbsPosIffNonzero, n), // n ≠ &0 ⇔ &0 < int_abs(n)
							At(int_real_lift.NotLessThan, zero, absN))) // ¬(&0 < int_abs(n)) ⇔ int_abs(n) ≤ &0
				})

			return ctx.Theorem(headline,
				func(a *Argument, n, m *TermWrapper) {
					a.Cases(n.Eq(zero))
					a.When(
						"a zero divisor admits no leftover at all, and the convention answers for it",
						func(a *Argument, isZero Fact) {
							a.Show(
								"the pair (&0, m) is what the convention names",
								By(isZero))
						})
					a.Otherwise(
						"a nonzero divisor: the least nonnegative leftover, and a quotient realizing it",
						func(a *Argument, nonZero Fact) {
							// The leftovers of m over n, as a predicate — the set
							// well-ordering is applied to. Nonnegativity is NOT
							// part of it: well-ordering restricts to the
							// nonnegatives itself, which is what its statement
							// is about.
							leftovers := sv.To(isLeftover(m, n, sv))

							// Well-ordering hands its two conclusions back under one
							// ∀y — that x is a nonnegative leftover, and that no
							// nonnegative leftover is below it — so the claim is
							// stated the way it arrives and taken apart afterwards.
							x, wop := a.Obtain(
								"well-ordering picks a least nonnegative leftover",
								MakeProp(Exists(xv)(ForAll(yv)(
									isLeftover(m, n, xv).And(le(zero, xv)).And(
										isLeftover(m, n, yv).And(le(zero, yv)).Imply(le(xv, yv)))))),
								// Normalized: well-ordering arrives with its predicate
								// still applied as a λ, and the β-reduction is what
								// lines it up with the claim.
								By(Normalized, nonZero, At(inhabited, n, m), At(int_embed.WellOrderedBelow, leftovers)))

							here := a.Have(
								"x₀ is itself a leftover, and not a negative one",
								MakeProp(isLeftover(m, n, x).And(le(zero, x))),
								By(wop.At(x)))

							least := a.Have(
								"and no nonnegative leftover is below it",
								MakeProp(ForAll(yv)(isLeftover(m, n, yv).And(le(zero, yv)).Imply(le(x, yv)))),
								By(wop))

							below := a.Have(
								"least is what puts it below |n|",
								MakeProp(lt(x, abs(n))),
								By(nonZero, here, least, small))

							q, decomp := a.Obtain(
								"and being a leftover is what gives it a quotient",
								MakeProp(isLeftover(m, n, x)),
								By(here))

							a.Take(q)
							a.Take(x)
							a.Show(
								"the pair (q₀, x₀) meets all three conditions",
								By(nonZero, decomp, below, here, At(int_real_lift.MulSym, n, q))) // n * q₀ = q₀ * n
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// What the specification says
// ---------------------------------------------------------------------------
//
// what the specification says, unpacked, and how far the remainder can
// reach.
//
// The specification branches on the divisor, and the members that open
// the file are its two branches read out, one instance of `divRemSpec`
// and one line of proof apiece: away from zero, the quotient/remainder
// equation together with the bound that pins the pair down — never
// negative, too small to take one more step; at zero, the convention
// the constants were chosen under, since nothing divides by zero and
// the algorithm has nothing to say there.
//
// That bound is then sharpened and made exact. `RemBelowDivisor` drops
// the absolute value where the divisor is positive. The two `…Iff`
// members then replace a guard with the condition genuinely equivalent
// to what it protects: `RemNonnegIff` drops `RemNonneg`'s nonzero
// divisor, `RemBelowDivisorIff` drops `RemBelowDivisor`'s positive one.
// Both conditions turn on the zero divisor, where the whole dividend is
// what is left over and the bound becomes a statement about its sign.
//
// The equation survives the zero divisor even though the bound does
// not, which is why `DivisionIdentity` needs no guard where
// `DivisionAlgorithm` does — and `remDiv` is that same equation solved
// for the remainder instead of the dividend.

// DivisionAlgorithm is what "dividing with remainder" means once the
// divisor is not zero, and the statement a reader has in mind on
// hearing the chapter's name.
var DivisionAlgorithm = divisionAlgorithmThm{family.Add(registry.ProofEntry{
	Name: "DivisionAlgorithm",
	Key:  "prop_46260312e4f7c4af",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:int.",
			Hypotheses: []string{
				"n ≠ &0",
			},
			Conclusion: "div(m, n) * n + rem(m, n) = m ∧ &0 ≤ rem(m, n) ∧ rem(m, n) < |n|",
		},
		func(a *Argument, m, n Term, nonZero Fact) {
			a.Show(
				"the divisor being nonzero rules out the specification's zero branch, leaving exactly this",
				By(nonZero, At(divRemSpec, n, m)))
		}),
})}

// RemNonneg is the lower half of that bound on its own: a remainder is
// never negative. Many arguments want only that much, the quotient
// playing no part in them.
var RemNonneg = remNonnegThm{family.Add(registry.ProofEntry{
	Name: "RemNonneg",
	Key:  "prop_48a46423910ca90f",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:int.",
			Hypotheses: []string{
				"n ≠ &0",
			},
			Conclusion: "&0 ≤ rem(m, n)",
		},
		func(a *Argument, m, n Term, nonZero Fact) {
			a.Show(
				"the divisor being nonzero leaves the specification's other branch, of which this is one conjunct",
				By(nonZero, At(divRemSpec, n, m)))
		}),
})}

// DivByZero is the quotient half of the convention: nothing is taken
// out.
var DivByZero = divByZeroThm{family.Add(registry.ProofEntry{
	Name: "DivByZero",
	Key:  "prop_9bf1425c82c38217",
	Build: family.Theorem(
		"∀m:int. div(m, &0) = &0",
		func(a *Argument, m Term) {
			v := ops(a.Ctx())
			zero := v.Zero

			a.Show(
				"the zero divisor meets the specification's condition, "+
					"and the branch that opens fixes the quotient",
				By(At(divRemSpec, zero, m)))
		}),
})}

// RemByZero is the remainder half: everything is left over.
var RemByZero = remByZeroThm{family.Add(registry.ProofEntry{
	Name: "RemByZero",
	Key:  "prop_10ee2c428d2ca9b9",
	Build: family.Theorem(
		"∀m:int. rem(m, &0) = m",
		func(a *Argument, m Term) {
			v := ops(a.Ctx())
			zero := v.Zero

			a.Show(
				"the zero divisor meets the specification's condition, "+
					"and the branch that opens fixes the remainder",
				By(At(divRemSpec, zero, m)))
		}),
})}

// RemBelowDivisor sharpens the algorithm's upper bound wherever the
// divisor is positive: there the divisor is its own absolute value, so
// the remainder falls short of the divisor itself and not merely of its
// size. Together with `RemNonneg` it traps a remainder between &0 and a
// positive divisor, which is the form most arguments want it in.
var RemBelowDivisor = remBelowDivisorThm{family.Add(registry.ProofEntry{
	Name: "RemBelowDivisor",
	Key:  "prop_e909b10c9d1553c9",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:int.",
			Hypotheses: []string{
				"&0 < n",
			},
			Conclusion: "rem(m, n) < n",
		},
		func(a *Argument, m, n Term, positive Fact) {
			v := ops(a.Ctx())
			zero := v.Zero

			a.Show(
				"positivity does both jobs: it clears the algorithm's guard, and "+
					"it collapses the absolute value the algorithm's bound is stated in",
				By(
					Normalized,
					positive,
					At(DivisionAlgorithm, m, n),            // n ≠ &0 ⇒ … ∧ int_rem(m, n) < int_abs(n)
					At(int_real_lift.AbsFixedIffNonneg, n), // int_abs(n) = n ⇔ &0 ≤ n
					At(int_real_lift.LessEqOfLessThan, zero, n),    // &0 < n ⇒ &0 ≤ n
					At(int_real_lift.NotEqualOfLessThan, zero, n))) // &0 < n ⇒ &0 ≠ n
		}),
})}

// RemNonnegIff is `RemNonneg` with the guard replaced by the condition
// that is actually equivalent to it. The lower bound can fail only at
// the zero divisor, where nothing is taken out and the remainder is
// handed the dividend's sign; away from &0 the algorithm supplies the
// bound and the condition asks nothing.
var RemNonnegIff = remNonnegIffThm{family.Add(registry.ProofEntry{
	Name: "RemNonnegIff",
	Key:  "prop_c0e646392a9a2cd2",
	Build: family.Theorem(
		"∀m n:int. &0 ≤ rem(m, n) ⇔ n = &0 ⇒ &0 ≤ m",
		func(a *Argument, m, n Term) {
			a.Show(
				"away from &0 the algorithm gives the bound and the condition asks "+
					"nothing; at &0 the remainder is the dividend and the two sides coincide",
				By(
					Normalized,
					At(RemNonneg, m, n), // n ≠ &0 ⇒ &0 ≤ int_rem(m, n)
					At(RemByZero, m)))   // int_rem(m, &0) = m
		}),
})}

// RemBelowDivisorIff does the same for the upper bound, and its answer
// has a case the lower bound's has not. `RemBelowDivisor` covers the
// positive divisor; at &0 the whole dividend is left over, so the
// condition survives there as a real one on the dividend rather than a
// vacuous one. Below &0 nothing works at all — a remainder is never
// negative, so none can lie strictly under a negative divisor, and that
// is why the disjunction stops at two cases.
//
// It is stated as two arms where `RemNonnegIff` above is one `Show`,
// and the reason is which bound each direction consumes rather than
// which premises it names: ⇐ reads the upper bound off
// `RemBelowDivisor`, while ⇒ runs the other way through the LOWER one —
// a remainder is never negative, so a divisor strictly above it is
// positive. The union of the two arms does close in one step; it just
// does not say that.
var RemBelowDivisorIff = remBelowDivisorIffThm{family.Add(registry.ProofEntry{
	Name: "RemBelowDivisorIff",
	Key:  "prop_7d77d9192814e65d",
	Build: family.Theorem(
		"∀m n:int. rem(m, n) < n ⇔ &0 < n ∨ (n = &0 ∧ m < &0)",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			zero := v.Zero
			rest := v.IntRem.Apply(m, n)

			a.Iff()
			a.Forward(
				"away from &0 a remainder is never negative, so a divisor "+
					"strictly above it is positive; at &0 the remainder is the dividend",
				func(below *Argument, lt Fact) {
					below.Show(
						"the two bounds on rem(m, n) compose",
						By(
							Normalized,
							lt,
							At(RemByZero, m),    // int_rem(m, &0) = m
							At(RemNonneg, m, n), // n ≠ &0 ⇒ &0 ≤ int_rem(m, n)
							// &0 ≤ int_rem(m, n) ∧ int_rem(m, n) < n ⇒ &0 < n
							At(int_real_lift.LessEqLessThanTrans, zero, rest, n)))
				})
			a.Backward(
				"a positive divisor bounds its remainder outright; at &0 the "+
					"remainder is the dividend, which the other disjunct puts below &0",
				func(holds *Argument, cond Fact) {
					holds.Show(
						"one fact to each disjunct",
						By(
							cond,
							At(RemBelowDivisor, m, n), // &0 < n ⇒ int_rem(m, n) < n
							RemByZero))
				})
		}),
})}

// DivisionIdentity reads the division algorithm left to right: the
// specification's equation, freed of the nonzero-divisor guard that
// its remainder bound needs and the equation does not.
var DivisionIdentity = divisionIdentityThm{family.Add(registry.ProofEntry{
	Name: "DivisionIdentity",
	Key:  "prop_f07636d48b48cadc",
	Build: family.Theorem(
		"∀m n:int. div(m, n) * n + rem(m, n) = m",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			zero := v.Zero

			// The specification at this pair — divisor first, dividend second.
			spec := At(divRemSpec, n, m)

			a.Cases(n.Eq(zero))
			a.When(
				"n = 0: the specification degenerates to div(m, n) = 0 "+
					"and rem(m, n) = m, so the equation reads 0 · n + m = m",
				func(deg *Argument, isZero Fact) {
					deg.Show(
						"the two zero laws finish it",
						By(
							isZero,
							spec,
							At(int_real_lift.MulLeftZero, n), // 0 · n = 0
							int_real_lift.AddLeftIdentity))
				})
			a.Otherwise(
				"n ≠ 0: the equation is the specification's own first conjunct here",
				func(main *Argument, nonZero Fact) {
					main.Show(
						"read it off the specification",
						By(nonZero, spec))
				})
		}),
})}

// remDiv is the same equation solved for the remainder: what is left
// over is the dividend less the part the quotient carries off. Every
// member that computes a quotient gets its remainder from this without
// touching the division algorithm again.
//
// It is the remainder-side counterpart of `divExact`, and the reason
// there is no guarded `remExact` beside it: `remDiv` holds at EVERY
// pair, the zero divisor included, so a member that has its quotient
// gets its remainder with no case analysis. A guarded twin would hand
// the zero-divisor split back to exactly the members that currently do
// not need one.
var remDiv = remDivThm{family.Add(registry.ProofEntry{
	Name: "remDiv",
	Key:  "prop_b3d39d999b9631b7",
	Build: family.Theorem(
		"∀m n:int. rem(m, n) = m - div(m, n) * n",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			carried := v.Mul.Apply(v.IntDiv.Apply(m, n), n)
			rest := v.IntRem.Apply(m, n)

			a.Show(
				"a summand moves across the identity and comes back as a subtraction",
				By(
					At(DivisionIdentity, m, n), // int_div(m, n) * n + int_rem(m, n) = m
					// m - int_div(m, n) * n = int_rem(m, n) ⇔ m = int_rem(m, n) + int_div(m, n) * n
					At(int_real_lift.EqSubRightAdd, m, carried, rest),
					// int_rem(m, n) + int_div(m, n) * n = int_div(m, n) * n + int_rem(m, n)
					At(int_real_lift.AddSym, rest, carried)))
		}),
})}

// ---------------------------------------------------------------------------
// The subgroups of ℤ
// ---------------------------------------------------------------------------
//
// The algorithm's first consequence is about a set of integers rather
// than a pair: an additive subgroup of ℤ is the multiples of its least
// positive member, or {&0} when it has none. Dividing a member by that
// least one leaves a remainder that is in the subgroup and below it, so
// the remainder is &0.

// IntegerSubgroupPrincipal — every additive subgroup of the integers has
// a unique nonnegative generator. A least positive member leaves no
// nonzero remainder; mutual divisibility gives uniqueness.
var IntegerSubgroupPrincipal = integerSubgroupPrincipalThm{family.Add(registry.ProofEntry{
	Name: "IntegerSubgroupPrincipal",
	Key:  "prop_b3147b31e5c0cfa7",
	Build: family.Sections(Statement{
		Binders: "∀H:set(int).",
		Hypotheses: []string{
			"subgroup(additive_group(int_ring), H)",
		},
		Conclusion: "∃d:num. H = image(λz:int. d * z, 𝕌) ∧ (∀e:num. H = image(λz:int. e * z, 𝕌) ⇒ e = d)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		naturalMultiples := ctx.Lemma(Statement{
			Binders:    "∀H:set(int).",
			Hypotheses: []string{"subgroup(additive_group(int_ring), H)"},
			Conclusion: "∀d:int. d ∈ H ⇒ ∀n:num. d * n ∈ H",
		},
			func(a *Argument, H *Expr[Set[Int]], subgroup Fact, d *Expr[Int], dIn Fact, n *Expr[Nat]) {
				integers := a.TermAs[group.GroupOps[Int]]("additive_group(int_ring)")
				a.Induct(n)
				a.Base(
					"zero copies give the subgroup zero",
					By(subgroup, group.SubgroupOne.At(integers, H), int_real_lift.MulRightZero))
				a.Step(
					"one more copy uses addition closure",
					func(b *Argument, ih Fact) {
						b.Show(
							"the successor multiple is the previous multiple plus the generator",
							Simp(Fwd(int_embed.OfNumSuc), Fwd(int_real_lift.LeftDistrib), Fwd(int_real_lift.MulRightIdentity)),
							By(dIn, ih, subgroup, group.SubgroupMul.At(integers, H, b.TermAs[Int]("d * &n"), d)))
					})
			})

		multiples := ctx.Lemma(Statement{
			Binders:    "∀H:set(int).",
			Hypotheses: []string{"subgroup(additive_group(int_ring), H)"},
			Conclusion: "∀d:int. d ∈ H ⇒ ∀z:int. d * z ∈ H",
		},
			func(a *Argument, H *Expr[Set[Int]], subgroup Fact, d *Expr[Int], dIn Fact, z *Expr[Int]) {
				n, signs := a.ObtainAs[Nat](
					"write the multiplier with a natural magnitude",
					"∃n:num. z = n ∨ z = -n",
					By(int_embed.Image.At(z)))
				a.Do(signs.SplitDisj(
					LeftHolds(
						"a natural multiplier gives repeated addition",
						Given(func(b *Argument, positive Fact) {
							b.Show(
								"use the natural multiple formula",
								By(Normalized, positive, dIn, subgroup, At(naturalMultiples, H, d, n)))
						})),
					RightHolds(
						"a negative multiplier gives the opposite multiple",
						Given(func(b *Argument, negative Fact) {
							b.Show(
								"negation closure supplies the negative multiple",
								negative.Rw(),
								Simp(Fwd(int_real_lift.MulRightNeg)),
								By(
									dIn,
									subgroup,
									At(naturalMultiples, H, d, n),
									group.SubgroupInv.At(
										b.TermAs[group.GroupOps[Int]]("additive_group(int_ring)"), H, b.TermAs[Int]("d * &n"))))
						})),
				))
			})

		unique := ctx.Lemma(Statement{
			Binders:    "∀d e:num.",
			Hypotheses: []string{"image(λz:int. d * z, 𝕌) = image(λz:int. e * z, 𝕌)"},
			Conclusion: "d = e",
		}, func(a *Argument, d, e *Expr[Nat], equalImages Fact) {
			generatorsIn := a.Have(
				"each generator belongs to the other image",
				"int_of_num(d) ∈ image(λz:int. e * z, 𝕌) ∧ int_of_num(e) ∈ image(λz:int. d * z, 𝕌)",
				BySets(equalImages, int_real_lift.MulRightIdentity))
			divides := a.Have(
				"each integer generator divides the other",
				"d ∣ int_of_num(e) ∧ e ∣ int_of_num(d)",
				BySets(generatorsIn, int_divides.IntDividesDef))
			a.Show(
				"natural divisibility is antisymmetric",
				By(
					divides,
					int_divides.OfNumDivides.At(d, e),
					int_divides.OfNumDivides.At(e, d),
					nat_divides.DividesAntisym))
		})

		exists := ctx.Lemma(Statement{
			Binders:    "∀H:set(int).",
			Hypotheses: []string{"subgroup(additive_group(int_ring), H)"},
			Conclusion: "∃d:num. H = image(λz:int. d * z, 𝕌)",
		}, func(a *Argument, H *Expr[Set[Int]], subgroup Fact) {
			closed := a.Have(
				"the subgroup contains zero and is closed under addition and negation",
				"int_of_num(0) ∈ H ∧ (∀x y:int. x ∈ H ∧ y ∈ H ⇒ x + y ∈ H) ∧ (∀x:int. x ∈ H ⇒ -x ∈ H)",
				By(subgroup, group.SubgroupDef.At(a.TermAs[group.GroupOps[Int]]("additive_group(int_ring)"), H)))
			a.Cases(a.TermAs[Bool]("∃p:int. p ∈ H ∧ 0 < p"))
			a.When(
				"a positive element gives a least positive member",
				func(b *Argument, positiveExists Fact) {
					p, least := b.ObtainAs[Int](
						"a positive member is nonnegative, so well-ordering from zero gives a least positive member",
						"∃p:int. 0 ≤ p ∧ (p ∈ H ∧ 0 < p) ∧ (∀y:int. 0 ≤ y ∧ (y ∈ H ∧ 0 < y) ⇒ p ≤ y)",
						By(
							positiveExists,
							int_real_lift.LessEqOfLessThan,
							int_embed.WellOrderedBelow.At(b.TermAs[Set[Int]]("λp:int. p ∈ H ∧ 0 < p"))))
					d, magnitude := b.ObtainAs[Nat](
						"represent the positive generator by a natural number",
						"∃d:num. p = d",
						By(least, int_embed.OfNumExists.At(p)))
					b.Take(d)
					quotients := b.Have(
						"every subgroup member has zero remainder",
						"∀z:int. z ∈ H ⇒ ∃q:int. z = d * q",
						Derive(func(c *Argument) {
							z := c.FixAs[Int]("z")
							zIn := c.Assume()
							parts := c.Conjuncts(
								least,
								"the generator is nonnegative",
								"the generator belongs to the subgroup",
								"the generator is positive",
								"every positive subgroup member bounds the generator")
							pIn, positive, minimal := parts[1], parts[2], parts[3]
							nonzero := c.Have(
								"a positive divisor is nonzero",
								"p ≠ 0",
								ByArith(positive))
							division := c.Have(
								"divide with a remainder below the generator",
								"div(z, p) * p + rem(z, p) = z ∧ 0 ≤ rem(z, p) ∧ rem(z, p) < p",
								By(nonzero, positive, DivisionAlgorithm.At(z, p), RemBelowDivisor.At(z, p)))
							multiple := c.Have(
								"the quotient multiple remains in the subgroup",
								"p * div(z, p) ∈ H",
								By(pIn, subgroup, At(multiples, H, p, c.TermAs[Int]("div(z, p)"))))
							difference := c.Have(
								"the remainder is the difference from that multiple",
								"rem(z, p) = z + -(p * div(z, p))",
								ByArith(division))
							remainderIn := c.Have(
								"addition and negation put the remainder in the subgroup",
								"rem(z, p) ∈ H",
								By(zIn, multiple, difference, closed))
							remainderZero := c.Have(
								"a nonzero remainder would contradict minimality",
								"rem(z, p) = 0",
								Derive(func(e *Argument) {
									nonzeroRemainder := e.SupposeNot()
									r := e.TermAs[Int]("rem(z, p)")
									positiveRemainder := e.Have(
										"a nonnegative nonzero remainder is positive",
										"0 < rem(z, p)",
										By(nonzeroRemainder, division, int_real_lift.LessThanSplit.At(e.TermAs[Int]("0"), r)))
									lowerBound := e.Have(
										"minimality bounds the positive remainder below",
										"p ≤ rem(z, p)",
										By(minimal.At(r), remainderIn, positiveRemainder, division))
									e.Show(
										"the two remainder bounds contradict one another",
										ByArith(lowerBound, division))
								}))
							c.Take(c.TermAs[Int]("div(z, p)"))
							c.Show(
								"with no remainder, the division identity makes z the quotient multiple",
								By(magnitude, remainderZero, division, int_real_lift.AddRightIdentity, int_real_lift.MulSym))
						}))
					b.Show(
						"the quotient representation and multiple closure give equality",
						BySets(quotients, subgroup, magnitude, least, At(multiples, H, b.TermAs[Int]("d"))))
				})
			a.Otherwise(
				"a subgroup with no positive element is zero",
				func(b *Argument, noPositive Fact) {
					zeroOnly := b.Have(
						"every subgroup member must vanish",
						"∀z:int. z ∈ H ⇒ z = 0",
						Derive(func(c *Argument) {
							c.FixAs[Int]("z")
							zIn := c.Assume()
							negativeIn := c.Have(
								"the opposite is also in the subgroup",
								"-z ∈ H",
								By(zIn, closed))
							neitherPositive := c.Have(
								"neither sign can be positive",
								"¬(0 < z) ∧ ¬(0 < -z)",
								By(noPositive, zIn, negativeIn))
							c.Show(
								"the integer is zero",
								ByArith(neitherPositive))
						}))
					b.Take(b.TermAs[Nat]("0"))
					b.Show(
						"zero generates exactly the zero subgroup",
						Simp(Fwd(int_real_lift.MulLeftZero)),
						BySets(zeroOnly, closed))
				})
		})

		return ctx.Theorem(headline, func(a *Argument, H *Expr[Set[Int]], subgroup Fact) {
			d, generated := a.ObtainAs[Nat](
				"choose a natural generator",
				"∃d:num. H = image(λz:int. d * z, 𝕌)",
				By(subgroup, At(exists, H)))
			a.Take(d)
			a.Show(
				"the generator exists and is unique",
				SplitConj(
					Case(
						"the chosen generator has the required image",
						By(generated)),
					Case(
						"any other natural generator is equal to it",
						Derive(func(b *Argument) {
							e := b.FixAs[Nat]("e")
							other := b.Assume()
							b.Show(
								"equal images have equal nonnegative generators",
								By(Normalized, generated, other, At(unique, e, d)))
						})),
				))
		})
	}),
})}

// ---------------------------------------------------------------------------
// The division algorithm's answer is the only answer
// ---------------------------------------------------------------------------
//
// Three conditions pin a quotient and a remainder down completely: the
// quotient/remainder equation, a remainder that is not negative, and a
// remainder that falls short of the divisor. Any pair meeting all three
// IS the pair `int_div` and `int_rem` hand out, so exhibiting a candidate is a
// way of COMPUTING them.
//
// Why the conditions leave no room. Two candidate decompositions of the
// same dividend differ, in their quotients, by an integer multiple of
// the divisor; and in their remainders by less than the divisor's size,
// both remainders lying in the same half-open interval. So that
// multiple has size below |n| — and the only such multiple is the zero
// one, which is the single lemma this file rests on.
//
// The file also carries `divExact`, at the bottom: the uniqueness
// specialized to an exact division, which is the form the chapter's
// computation laws actually reach it through.

// DivModUnique reads `int_div` and `int_rem` off any candidate pair meeting the
// division algorithm's conditions — the chapter's computation rule, and
// the reason a nonzero divisor's quotient and remainder are worth
// naming at all.
var DivModUnique = divModUniqueThm{family.Add(registry.ProofEntry{
	Name: "DivModUnique",
	Key:  "prop_81ef98291a25ffa8",
	Build: family.Sections(
		Statement{
			Binders: "∀m n q r:int.",
			Hypotheses: []string{
				"m = q * n + r",
				"&0 ≤ r",
				"r < |n|",
			},
			Conclusion: "div(m, n) = q ∧ rem(m, n) = r",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			// Subtraction is what this argument is written in: the two
			// candidate decompositions are compared by difference.
			sub := v.Sub
			// &0 and &1. The chapter alphabet carries ℕ's zero — the thing
			// the spelling `&0` applies the embedding to — and no other
			// numeral, so ℕ's one arrives by name.
			zero := v.Zero
			one := v.One

			// The lemma the uniqueness rests on: a multiple of n cannot be
			// smaller than n itself without being the zero multiple. It is
			// the one place the argument uses that ℤ is discrete — over ℚ
			// the same three conditions would pin nothing down.
			vanishes := ctx.Lemma(Statement{
				Binders: "∀a n:int.",
				Hypotheses: []string{
					"|a * n| < |n|",
				},
				Conclusion: "a = &0",
			},
				func(arg *Argument, a, n Term, small Fact) {
					absA, absN := v.Abs.Apply(a), v.Abs.Apply(n)
					absAN := v.Abs.Apply(v.Mul.Apply(a, n))

					positive := arg.Have(
						"n has positive size: a size is never negative, and |a·n| stays below |n|",
						MakeProp(v.Lt.Apply(zero, absN)),
						By(
							small,
							At(int_real_lift.AbsNonneg, v.Mul.Apply(a, n)), // &0 ≤ |a * n|
							// &0 ≤ |a * n| ∧ |a * n| < |n| ⇒ &0 < |n|
							At(int_real_lift.LessEqLessThanTrans, zero, absAN, absN)))

					below := arg.Have(
						"scaling by a positive |n| preserves strict order, and |a| scales to |a·n|",
						MakeProp(v.Lt.Apply(absA, one)),
						By(
							Normalized,
							small,
							positive,
							At(int_real_lift.AbsMul, a, n),          // |a * n| = |a| * |n|
							At(int_real_lift.MulLeftIdentity, absN), // &1 * |n| = |n|
							At(int_real_lift.LessThanMulRightEq, absA, one, absN))) // |a| * |n| < &1 * |n| ⇔ |a| < &1

					flat := arg.Have(
						"no integer lies between &0 and &1, and a size is not negative",
						MakeProp(absA.Eq(zero)),
						By(
							Normalized,
							below,
							At(int_embed.Discrete, absA, one),      // |a| < &1 ⇔ |a| + &1 ≤ &1
							At(int_real_lift.AddLeftIdentity, one), // &0 + &1 = &1
							At(int_real_lift.LessEqAddRight, absA, zero, one), // |a| + &1 ≤ &0 + &1 ⇔ |a| ≤ &0
							At(int_real_lift.AbsNonneg, a),                    // &0 ≤ |a|
							At(int_real_lift.LessEqAntisym, absA, zero)))      // |a| = &0 ⇔ |a| ≤ &0 ∧ &0 ≤ |a|

					arg.Show(
						"and only &0 has size &0",
						By(flat, int_real_lift.AbsVanishes))
				})

			return ctx.Theorem(headline,
				func(a *Argument, m Term, n *TermWrapper, q, r Term, candidate Fact) {
					quot, rest := v.IntDiv.Apply(m, n), v.IntRem.Apply(m, n)
					absN := v.Abs.Apply(n)
					quotDiff := sub.Apply(q, quot) // q − int_div(m, n)
					remDiff := sub.Apply(rest, r)  // int_rem(m, n) − r

					// The chapter's own decomposition of m by n. It is stated
					// under a nonzero divisor, which `nonZero` supplies at each
					// of the two places below that use it.
					algorithm := At(DivisionAlgorithm, m, n)

					nonZero := a.Have(
						"a zero divisor has size &0, which the candidate's "+
							"remainder would have to be both below and not below",
						MakeProp(n.Neq(zero)),
						By(
							Normalized,
							candidate,
							At(int_real_lift.AbsVanishes, n),        // |n| = &0 ⇔ n = &0
							At(int_real_lift.NotLessThan, r, zero))) // ¬(r < &0) ⇔ &0 ≤ r

					gap := a.Have(
						"both decompositions add up to m, so the quotients differ by exactly as much as the remainders do",
						MakeProp(v.Mul.Apply(quotDiff, n).Eq(remDiff)),
						By(
							candidate,
							nonZero,
							algorithm,
							// (q·n + r) − (int_div(m,n)·n + int_rem(m,n)) = (q·n − int_div(m,n)·n) + (r − int_rem(m,n))
							At(int_real_lift.SubAddPairwise, v.Mul.Apply(q, n), r, v.Mul.Apply(quot, n), rest),
							At(int_real_lift.SubRefl, m), // m − m = &0
							// x + y = &0 ⇔ x = −y, at x = q·n − int_div(m,n)·n and y = r − int_rem(m,n)
							At(
								int_real_lift.NegLeftUnique,
								sub.Apply(v.Mul.Apply(q, n), v.Mul.Apply(quot, n)),
								sub.Apply(r, rest)),
							At(int_real_lift.NegSub, r, rest), // −(r − int_rem(m, n)) = int_rem(m, n) − r
							int_real_lift.SubRightDistrib))

					small := a.Have(
						"two remainders drawn from ⟦&0, |n|⟭ are less than |n| apart",
						MakeProp(v.Lt.Apply(v.Abs.Apply(remDiff), absN)),
						By(
							candidate,
							nonZero,
							algorithm,
							// |rem − r| < |n| ⇔ r − |n| < rem ∧ rem < r + |n| ∧ &0 < |n|
							At(int_real_lift.AbsBetween, r, rest, absN),
							// &0 ≤ r ∧ r < |n| ⇒ &0 < |n|
							At(int_real_lift.LessEqLessThanTrans, zero, r, absN),
							// r − |n| < int_rem(m, n) ⇔ r < int_rem(m, n) + |n|
							At(int_real_lift.LessThanSubAddRight, r, absN, rest),
							// |n| ≤ int_rem(m, n) + |n| ⇔ &0 ≤ int_rem(m, n)
							At(int_real_lift.LessEqSelfAddLeft, rest, absN),
							// |n| ≤ r + |n| ⇔ &0 ≤ r
							At(int_real_lift.LessEqSelfAddLeft, r, absN),
							// r < |n| ≤ int_rem(m, n) + |n|
							At(int_real_lift.LessThanLessEqTrans, r, absN, v.Add.Apply(rest, absN)),
							// int_rem(m, n) < |n| ≤ r + |n|
							At(int_real_lift.LessThanLessEqTrans, rest, absN, v.Add.Apply(r, absN))))

					agree := a.Have(
						"so that quotient difference is a multiple of n too small to be anything but &0",
						MakeProp(quotDiff.Eq(zero)),
						By(gap, small, vanishes))

					a.Show(
						"and with the quotients equal the remainders have nothing left to differ by",
						By(
							Normalized,
							gap,
							agree,
							At(int_real_lift.MulLeftZero, n), // &0 * n = &0
							// each gap read as the equality its vanishing means,
							// at the two differences the facts above are stated in
							At(int_real_lift.SubEqZero, q, quot),  // q − int_div(m, n) = &0 ⇔ q = int_div(m, n)
							At(int_real_lift.SubEqZero, rest, r))) // int_rem(m, n) − r = &0 ⇔ int_rem(m, n) = r
				})
		}),
})}

// DivUnique is DivModUnique's quotient half, for the arguments that
// produce a candidate pair but only care what the quotient turned out
// to be.
var DivUnique = divUniqueThm{family.Add(registry.ProofEntry{
	Name: "DivUnique",
	Key:  "prop_dc5318d88006892f",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n q r:int.",
			Hypotheses: []string{
				"m = q * n + r",
				"&0 ≤ r",
				"r < |n|",
			},
			Conclusion: "div(m, n) = q",
		},
		func(a *Argument, m, n, q, r Term, candidate Fact) {
			a.Show(
				"the quotient conjunct of the pair the candidate pins down",
				By(candidate, At(DivModUnique, m, n, q, r)))
		}),
})}

// RemUnique is DivModUnique's remainder half — the same identification
// read the other way.
var RemUnique = remUniqueThm{family.Add(registry.ProofEntry{
	Name: "RemUnique",
	Key:  "prop_b59f17ca03a3e499",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n q r:int.",
			Hypotheses: []string{
				"m = q * n + r",
				"&0 ≤ r",
				"r < |n|",
			},
			Conclusion: "rem(m, n) = r",
		},
		func(a *Argument, m, n, q, r Term, candidate Fact) {
			a.Show(
				"the remainder conjunct of the pair the candidate pins down",
				By(candidate, At(DivModUnique, m, n, q, r)))
		}),
})}

// divExact is DivUnique where the division comes out even: a divisor
// that goes into the dividend a whole number of times has that number
// for its quotient, and nothing else has to be checked.
//
// Taking the remainder to be &0 is what shrinks the uniqueness's three
// conditions down. The lower bound stops saying anything, &0 not being
// negative; the upper one stops mentioning the dividend and becomes
// just "the divisor is not zero". What is left for a caller to supply
// is the factorisation.
//
// The hypothesis is stated as `n ≠ &0` rather than as `&0 < |n|`
// because that is the form the callers hold: four of the five arrive
// with the divisor's nonzeroness in hand and only the unit divisor
// arrives with its size, which is why that one site cites the
// uniqueness directly instead.
//
// Internal, and unexported: this is how the chapter's computation laws
// reach the uniqueness, not a statement about `int_div` a reader looks up.
var divExact = divExactThm{family.Add(registry.ProofEntry{
	Name: "divExact",
	Key:  "prop_c4d5f34f4417ddaa",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n q:int.",
			Hypotheses: []string{
				"n ≠ &0",
				"m = q * n",
			},
			Conclusion: "div(m, n) = q",
		},
		func(a *Argument, m, n, q Term, exact Fact) {
			v := ops(a.Ctx())
			zero := v.Zero

			a.Show(
				"(q, &0) is a decomposition of m by n: its equation is the hypothesis "+
					"with nothing added on, and both remainder bounds hold of &0 outright",
				By(
					Normalized,
					exact,
					// m = q * n + &0 ∧ &0 ≤ &0 ∧ &0 < |n| ⇒ int_div(m, n) = q
					At(DivUnique, m, n, q, zero),
					At(int_real_lift.AddRightIdentity, v.Mul.Apply(q, n)), // q * n + &0 = q * n
					At(int_real_lift.LessEqRefl, zero),                    // &0 ≤ &0
					At(int_real_lift.AbsPosIffNonzero, n)))                // n ≠ &0 ⇔ &0 < |n|
		}),
})}

// ---------------------------------------------------------------------------
// Where the chapter starts paying
// ---------------------------------------------------------------------------
//
// Uniqueness is not the end of the chapter but the point of it. Below
// this file the statements are read off the specification; here they
// are COMPUTED — to know a quotient, exhibit a candidate pair and check
// the three conditions against it, which is what `divExact` does once
// so that these members need not.
//
// The shape recurs and is worth naming. Only the QUOTIENT half of a
// int_div/int_rem pair needs the candidate argument; with the quotient known
// the remainder is arithmetic off `remDiv`, which carries no guard, so
// the second member of each pair is one line. `ZeroRem`, `RemByOne`
// and `RemMul` are all that line.
//
// Two members break the pairing and mark the chapter's other shapes.
// `DivSelf` has no partner — `int_rem(n, n) = &0` is `RemMul` at the
// product `&1 · n` — and shows instead the zero divisor being split off
// first, the remainder bound being the one condition it cannot meet.
// `RemEqSelf` has a partner but is not a computation off it: its two
// directions are different arguments, and only the easier one goes
// through `DivEqZero`.
//
// `DivOfSmall`/`RemOfSmall` are a further shape, and they separate the
// recurring pattern from its stated mechanism. Neither computes: they
// are `DivEqZero`/`RemEqSelf` read in the sufficient direction. The
// remainder member is still one line off the quotient member — but
// through the shared CONDITION rather than through `remDiv`, there
// being no arithmetic left for `remDiv` to do.
//
// The file closes on the widest of these laws, `DivMulAdd`/`RemMulAdd`
// — what a multiple of the divisor does to a division — of which
// `DivMul`/`RemMul` above are the case `p = &0`. They break the
// pairing a second way, and in the opposite direction to `RemEqSelf`:
// the two halves are the SAME candidate argument, run once through
// `DivUnique` and once through `RemUnique`. Reading the remainder off
// the quotient the usual way would import the quotient law's guard
// into a statement that has none.
//
// Each is then packed with its rearrangements — four ways over — and
// the packing repeats no mathematics: every conjunct rearranges its own
// spelling into the law's, then cites the law.

// ZeroDiv — no divisor takes anything out of &0. Away from zero the
// division is exact, with &0 for its quotient.
var ZeroDiv = zeroDivThm{family.Add(registry.ProofEntry{
	Name: "ZeroDiv",
	Key:  "prop_8d3244ae9136ee93",
	Build: family.Theorem(
		"∀n:int. div(&0, n) = &0",
		func(a *Argument, n *TermWrapper) {
			v := ops(a.Ctx())
			zero := v.Zero

			nonZero := a.Unless(
				n.Eq(zero),
				"n = &0: a zero divisor's quotient is fixed by convention, and the convention is &0",
				Cite(DivByZero)) // closes: int_div(&0, &0) = &0, the convention at this branch's divisor

			a.Show(
				"away from zero the division comes out even — &0 is n taken &0 times — so the quotient is &0",
				By(
					nonZero,
					// n ≠ &0 ∧ &0 = &0 * n ⇒ int_div(&0, n) = &0
					At(divExact, zero, n, zero),
					int_real_lift.MulLeftZero))
		}),
})}

// ZeroRem says nothing is left over when &0 is divided. It needs no
// case analysis of its own: with the quotient already known, the
// remainder is a computation.
var ZeroRem = zeroRemThm{family.Add(registry.ProofEntry{
	Name: "ZeroRem",
	Key:  "prop_3bc7143f8c561c1",
	Build: family.Theorem(
		"∀n:int. rem(&0, n) = &0",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			zero := v.Zero

			a.Show(
				"&0 less what the quotient carries off, and a quotient of &0 carries off nothing",
				By(
					At(remDiv, zero, n),              // int_rem(&0, n) = &0 - int_div(&0, n) * n
					At(ZeroDiv, n),                   // int_div(&0, n) = &0
					At(int_real_lift.MulLeftZero, n), // &0 * n = &0
					int_real_lift.SubRefl))
		}),
})}

// DivByOne — the unit divisor takes the whole dividend out. The pair
// (n, &0) is exhibited as the decomposition of n by &1, and the
// quotient is read off the uniqueness DIRECTLY rather than through
// `divExact` — this is the one site in the chapter where that is the
// shorter route, for the reason the file header gives.
var DivByOne = divByOneThm{family.Add(registry.ProofEntry{
	Name: "DivByOne",
	Key:  "prop_beb748b4078ce8bb",
	Build: family.Theorem(
		"∀n:int. div(n, &1) = n",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			zero, one := v.Zero, v.One

			unitSize := a.Have(
				"the unit divisor has a size for the remainder to fall below, that size being &1",
				MakeProp(v.Lt.Apply(zero, v.Abs.Apply(one))),
				Cite(int_embed.OfNumAbs),            // ↦ &0 < &1: |·| is inert on the image of &
				Cite(int_real_lift.ZeroLessThanOne)) // &0 < &1

			a.Show(
				"n = n · &1 + &0, with the remainder &0 inside ⟦&0, |&1|⟭, so n is the quotient",
				By(
					unitSize,
					// n = n * &1 + &0 ∧ &0 ≤ &0 ∧ &0 < |&1| ⇒ int_div(n, &1) = n
					At(DivUnique, n, one, n, zero),
					At(int_real_lift.MulRightIdentity, n), // n * &1 = n
					At(int_real_lift.AddRightIdentity, n), // n + &0 = n
					int_real_lift.LessEqRefl))
		}),
})}

// RemByOne — the unit divisor leaves nothing over. It needs no case
// analysis and no second visit to the division algorithm: the quotient
// is already known, so the remainder is a computation.
var RemByOne = remByOneThm{family.Add(registry.ProofEntry{
	Name: "RemByOne",
	Key:  "prop_8c700c93b8df318f",
	Build: family.Theorem(
		"∀n:int. rem(n, &1) = &0",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			one := v.One

			a.Show(
				"n less what the quotient carries off, and at the divisor &1 the quotient carries off all of n",
				By(
					At(remDiv, n, one),                    // int_rem(n, &1) = n - int_div(n, &1) * &1
					At(DivByOne, n),                       // int_div(n, &1) = n
					At(int_real_lift.MulRightIdentity, n), // n * &1 = n
					int_real_lift.SubRefl))
		}),
})}

// DivSelf is not a reflexivity law, and the conditional is why: an
// integer goes into itself once, but the zero divisor has no quotient
// to compute and keeps the chapter's convention instead. The two
// branches are exactly those two sentences.
var DivSelf = divSelfThm{family.Add(registry.ProofEntry{
	Name: "DivSelf",
	Key:  "prop_2b4b8673c871979b",
	// The two branch values are spelled unsugared. `&` resolves its target
	// type from the surrounding context, and a COND branch has none to
	// offer — `COND(n = &0, &0, &1)` types its branches as REAL and the
	// equation is then rejected. The condition keeps the chapter's `n = &0`,
	// which the equality does pin.
	Build: family.Theorem(
		"∀n:int. div(n, n) = COND(n = &0, int_of_num(0), 1)",
		func(a *Argument, n *TermWrapper) {
			v := ops(a.Ctx())
			zero, one := v.Zero, v.One

			a.Cases(n.Eq(zero))
			a.When(
				"n = &0: the branch hypothesis selects the conditional's own zero arm, "+
					"and the convention the constants were chosen under supplies its value",
				Cite(DivByZero)) // closes: int_div(&0, &0) = &0, at this branch's own divisor
			a.Otherwise(
				"n ≠ &0: n goes into itself once exactly — n = &1 · n",
				func(main *Argument, nonZero Fact) {
					main.Show(
						"the division comes out even, so the quotient is &1 — the value the "+
							"conditional's other branch names, which the same hypothesis selects",
						By(
							nonZero,
							// n ≠ &0 ∧ n = &1 * n ⇒ int_div(n, n) = &1
							At(divExact, n, n, one),
							int_real_lift.MulLeftIdentity))
				})
		}),
})}

// DivMul — dividing a product by one of its factors returns the other.
// The hypothesis falls on whichever factor is doing the dividing: at a
// zero divisor the chapter's convention hands back &0 rather than the
// surviving factor, so the statement would be false without it.
var DivMul = divMulThm{family.Add(registry.ProofEntry{
	Name: "DivMul",
	Key:  "prop_13c82005380c5b91",
	Build: family.Theorem(
		"(∀m n:int. n ≠ &0 ⇒ div(m * n, n) = m) ∧ (∀m n:int. m ≠ &0 ⇒ div(m * n, m) = n)",
		func(a *Argument) {
			v := ops(a.Ctx())

			a.Do(SplitConj(
				Case(
					"dividing by the right factor: the quotient is m",
					Derive(func(d *Argument) {
						m, n := d.Fix(), d.Fix()
						nonZero := d.Assume()

						d.Show(
							"the factorisation an exact division asks for is the product as it already stands",
							By(
								nonZero,
								// n ≠ &0 ∧ m * n = m * n ⇒ int_div(m * n, n) = m
								At(divExact, v.Mul.Apply(m, n), n, m)))
					})),
				Case(
					"dividing by the left factor: the quotient is n",
					Derive(func(d *Argument) {
						m, n := d.Fix(), d.Fix()
						nonZero := d.Assume()

						d.Show(
							"the same factorisation, read with the divisor on the right",
							By(
								nonZero,
								// m ≠ &0 ∧ m * n = n * m ⇒ int_div(m * n, m) = n
								At(divExact, v.Mul.Apply(m, n), m, n),
								At(int_real_lift.MulSym, m, n))) // m * n = n * m
					})),
			))
		}),
})}

// RemMul — a product divided by either of its factors leaves nothing
// over. Unlike the quotient this needs no hypothesis, and for a reason
// of its own: at a zero divisor the dividend m · &0 is itself &0, and
// the convention leaves the whole of it over — which is nothing.
var RemMul = remMulThm{family.Add(registry.ProofEntry{
	Name: "RemMul",
	Key:  "prop_381710b107e1a174",
	Build: family.Sections(
		"(∀m n:int. rem(m * n, n) = &0) ∧ (∀m n:int. rem(m * n, m) = &0)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zero := v.Zero

			// One of the two conjuncts carries the whole argument; the other
			// is it at the transposed product. Naming it is what lets the
			// second conjunct be one line rather than a second case analysis.
			atRightFactor := ctx.Lemma("∀m n:int. rem(m * n, n) = &0",
				func(a *Argument, m Term, n *TermWrapper) {
					product := v.Mul.Apply(m, n)

					nonZero := a.Unless(
						n.Eq(zero),
						"n = &0: a zero divisor leaves the whole dividend over",
						Given(func(z *Argument, isZero Fact) {
							z.Show(
								"and that dividend is m * &0, which is &0",
								By(
									isZero,
									At(RemByZero, product), // int_rem(m * n, &0) = m * n
									int_real_lift.MulRightZero))
						}))

					a.Show(
						"away from zero the quotient is m, which carries the whole product off",
						By(
							nonZero,
							At(remDiv, product, n), // int_rem(m * n, n) = m * n - int_div(m * n, n) * n
							// n ≠ &0 ∧ m * n = m * n ⇒ int_div(m * n, n) = m
							At(divExact, product, n, m),
							int_real_lift.SubRefl))
				})

			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(SplitConj(
						Case(
							"dividing by the right factor: the statement just proved",
							Cite(atRightFactor)),
						Case(
							"dividing by the left factor: the same statement, at the product taken the other way round",
							Derive(func(d *Argument) {
								m, n := d.Fix(), d.Fix()

								// Here the commutation has to reach INSIDE int_rem(_, m), so it
								// moves the goal rather than sitting beside the cite. Where
								// such an equation feeds a cited lemma's own hypothesis slot
								// it CAN stand as a premise — DivMul's second conjunct above
								// does exactly that.
								transposeProduct(d, m, n) // ↦ int_rem(n * m, m) = &0

								d.Show(
									"and m is the right-hand factor of that product",
									By(atRightFactor))
							})),
					))
				})
		}),
})}

// DivEqZero — nothing comes out of a division exactly when there was
// nothing to come out. The pair exhibited is (&0, m): a quotient that
// takes nothing, and the dividend left over whole.
var DivEqZero = divEqZeroThm{family.Add(registry.ProofEntry{
	Name: "DivEqZero",
	Key:  "prop_e4ac55904de6ec26",
	Build: family.Theorem(
		"∀m n:int. div(m, n) = &0 ⇔ n = &0 ∨ (&0 ≤ m ∧ m < |n|)",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			zero := v.Zero

			nonZero := a.Unless(
				n.Eq(zero),
				"n = &0: both sides hold outright — the convention fixes the "+
					"quotient at &0, and n = &0 is the right-hand side's own left disjunct",
				Cite(DivByZero)) // closes: int_div(m, &0) = &0
			// Away from &0 that disjunct is dead, so what is left of the
			// right-hand side is the size condition alone.
			a.Do(TrivialSimplify())

			a.Iff()
			a.Forward(
				"a quotient of &0 carries nothing off, so the dividend IS the remainder",
				func(vanishes *Argument, quotZero Fact) {
					vanishes.Show(
						"and away from &0 the algorithm puts every remainder inside ⟦&0, |n|⟭",
						By(
							nonZero,
							quotZero,
							// n ≠ &0 ⇒ int_div(m, n) * n + int_rem(m, n) = m ∧ &0 ≤ int_rem(m, n) ∧ int_rem(m, n) < |n|
							At(DivisionAlgorithm, m, n),
							At(int_real_lift.MulLeftZero, n), // &0 * n = &0
							int_real_lift.AddLeftIdentity))
				})
			a.Backward(
				"a dividend already inside ⟦&0, |n|⟭ is its own remainder",
				func(fits *Argument, bound Fact) {
					fits.Show(
						"(&0, m) is a decomposition of m by n, and the bound "+
							"is precisely what makes m an admissible remainder",
						By(
							bound,
							// m = &0 * n + m ∧ &0 ≤ m ∧ m < |n| ⇒ int_div(m, n) = &0
							At(DivUnique, m, n, zero, m),
							At(int_real_lift.MulLeftZero, n), // &0 * n = &0
							int_real_lift.AddLeftIdentity))
				})
		}),
})}

// RemEqSelf is the same condition read on the remainder rather than the
// quotient. Only one of its two directions is new: under the condition
// `DivEqZero` has already named the quotient &0, and a quotient of &0
// carries nothing off, so the division identity hands the dividend back.
// The other direction never mentions the quotient at all — it is the
// remainder bound, transported along `int_rem(m, n) = m`.
var RemEqSelf = remEqSelfThm{family.Add(registry.ProofEntry{
	Name: "RemEqSelf",
	Key:  "prop_aa036dcb21ea12ee",
	Build: family.Theorem(
		"∀m n:int. rem(m, n) = m ⇔ n = &0 ∨ (&0 ≤ m ∧ m < |n|)",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			zero := v.Zero

			nonZero := a.Unless(
				n.Eq(zero),
				"n = &0: both sides hold outright — the convention leaves the whole "+
					"dividend over, and n = &0 is the right-hand side's own left disjunct",
				Cite(RemByZero)) // closes: int_rem(m, &0) = m
			// The same dead disjunct as above, dropped for the same reason.
			a.Do(TrivialSimplify())

			a.Iff()
			a.Forward(
				"if all of m stays behind then m is a remainder, and remainders are bounded",
				func(whole *Argument, selfRem Fact) {
					whole.Show(
						"the bound the algorithm puts on rem(m, n), carried over to m by the hypothesis",
						By(
							Normalized,
							nonZero,
							selfRem,
							// n ≠ &0 ⇒ … ∧ &0 ≤ int_rem(m, n) ∧ int_rem(m, n) < |n| — only the bound is wanted here
							At(DivisionAlgorithm, m, n)))
				})
			a.Backward(
				"under this same condition the quotient is &0, and a quotient of &0 takes nothing out",
				func(fits *Argument, bound Fact) {
					fits.Show(
						"so the division identity reads &0 + rem(m, n) = m",
						By(
							bound,
							// int_div(m, n) = &0 ⇔ n = &0 ∨ (&0 ≤ m ∧ m < |n|)
							At(DivEqZero, m, n),
							At(DivisionIdentity, m, n),       // int_div(m, n) * n + int_rem(m, n) = m
							At(int_real_lift.MulLeftZero, n), // &0 * n = &0
							int_real_lift.AddLeftIdentity))
				})
		}),
})}

// DivOfSmall — a dividend already small enough has nothing to take out.
// It is `DivEqZero`'s sufficient direction, restated on the hypothesis a
// caller holds: the dividend below the DIVISOR, where the biconditional
// asks for it below the divisor's SIZE. Closing that gap is the whole
// proof.
//
// The sign hypothesis is guarded by `n ≠ &0`, and the guard is not a
// hedge: at a zero divisor the convention fixes the quotient with no
// bound needed at all, which is the condition's own left disjunct. Away
// from zero the guard opens and supplies the condition's lower bound.
var DivOfSmall = divOfSmallThm{family.Add(registry.ProofEntry{
	Name: "DivOfSmall",
	Key:  "prop_e922ffa0a97bfd77",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:int.",
			Hypotheses: []string{
				"n ≠ &0 ⇒ &0 ≤ m",
				"m < n",
			},
			Conclusion: "div(m, n) = &0",
		},
		func(a *Argument, m, n Term, small Fact) {
			v := ops(a.Ctx())
			zero := v.Zero

			a.Show(
				"away from &0 the dividend is nonnegative, so the divisor is "+
					"positive and is its own size — which is the bound the condition wants",
				By(
					Normalized,
					small,
					// int_div(m, n) = &0 ⇔ n = &0 ∨ (&0 ≤ m ∧ m < |n|)
					At(DivEqZero, m, n),
					At(int_real_lift.LessEqLessThanTrans, zero, m, n), // &0 ≤ m ∧ m < n ⇒ &0 < n
					At(int_real_lift.LessEqOfLessThan, zero, n),       // &0 < n ⇒ &0 ≤ n
					At(int_construction.AbsBySign, n)))                // int_abs(n) = COND(&0 ≤ n, n, -n)
		}),
})}

// RemOfSmall — that same small dividend stays behind whole. It proves
// nothing new: `DivEqZero` and `RemEqSelf` are stated against the SAME
// condition, so a vanishing quotient and a self-remainder are one fact,
// and `DivOfSmall` has settled it already.
var RemOfSmall = remOfSmallThm{family.Add(registry.ProofEntry{
	Name: "RemOfSmall",
	Key:  "prop_3d895f9e6f8b817b",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:int.",
			Hypotheses: []string{
				"n ≠ &0 ⇒ &0 ≤ m",
				"m < n",
			},
			Conclusion: "rem(m, n) = m",
		},
		func(a *Argument, m, n Term, small Fact) {
			a.Show(
				"the quotient already vanishes under this hypothesis, and the two "+
					"biconditionals carry that across to the dividend staying whole",
				By(
					small,
					At(DivOfSmall, m, n), // the quotient, at this same hypothesis
					At(DivEqZero, m, n),  // int_div(m, n) = &0 ⇔ n = &0 ∨ (&0 ≤ m ∧ m < |n|)
					At(RemEqSelf, m, n))) // int_rem(m, n) = m ⇔ n = &0 ∨ (&0 ≤ m ∧ m < |n|)
		}),
})}

// RemRem — taking a remainder twice is taking it once. Away from &0
// what the algorithm leaves over is not negative and falls short of the
// divisor's size, which is `RemEqSelf`'s condition on the nose; at &0
// that condition's other disjunct is what holds. Either way the second
// division has nothing left to do.
var RemRem = remRemThm{family.Add(registry.ProofEntry{
	Name: "RemRem",
	Key:  "prop_3449816fefcbeccf",
	Build: family.Theorem(
		"∀m n:int. rem(rem(m, n), n) = rem(m, n)",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			rest := v.IntRem.Apply(m, n)

			a.Show(
				"rem(m, n) meets the condition already: away from &0 the algorithm "+
					"bounds it, and at &0 the condition's other disjunct is what holds",
				By(
					// int_rem(int_rem(m, n), n) = int_rem(m, n) ⇔ n = &0 ∨ (&0 ≤ int_rem(m, n) ∧ int_rem(m, n) < |n|)
					At(RemEqSelf, rest, n),
					// n ≠ &0 ⇒ … ∧ &0 ≤ int_rem(m, n) ∧ int_rem(m, n) < |n| — the right-hand disjunct, exactly
					At(DivisionAlgorithm, m, n)))
		}),
})}

// DivMulAdd — a multiple of the divisor added to the dividend adds its
// coefficient to the quotient. The candidate to exhibit is the obvious
// one: m·n is already n taken m times, so it goes straight onto the
// quotient and the remainder p brought with it is untouched. `DivMul`
// above is this law at p = &0.
//
// The guard is the divisor's, as everywhere in this chapter: at a zero
// divisor the convention fixes both quotients at &0, so the equation
// would read &0 = m.
//
// Exported on its own beside the four-way packing
// (`DivMulAddClauses` below): a reader asking what
// `int_div(m·n + p, n)` is should meet the law and not the pack.
var DivMulAdd = divMulAddThm{family.Add(registry.ProofEntry{
	Name: "DivMulAdd",
	Key:  "prop_c030121b4e6befa7",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p:int.",
			Hypotheses: []string{
				"n ≠ &0",
			},
			Conclusion: "div(m * n + p, n) = m + div(p, n)",
		},
		func(a *Argument, m, n, p Term, nonZero Fact) {
			v := ops(a.Ctx())
			dividend := v.Add.Apply(v.Mul.Apply(m, n), p)
			quot, rest := v.IntDiv.Apply(p, n), v.IntRem.Apply(p, n)

			a.Show(
				"(m + div(p, n), rem(p, n)) decomposes m·n + p by n: the added "+
					"multiple joins the quotient, p's remainder stays, bound and all",
				By(
					nonZero,
					// m*n + p = (m + int_div(p, n)) * n + int_rem(p, n) ∧ &0 ≤ int_rem(p, n) ∧ int_rem(p, n) < |n|
					// ⇒ int_div(m*n + p, n) = m + int_div(p, n)
					At(DivUnique, dividend, n, v.Add.Apply(m, quot), rest),
					// n ≠ &0 ⇒ int_div(p, n) * n + int_rem(p, n) = p ∧ &0 ≤ int_rem(p, n) ∧ int_rem(p, n) < |n|
					At(DivisionAlgorithm, p, n),
					// (m + int_div(p, n)) * n = m*n + int_div(p, n)*n
					At(int_real_lift.RightDistrib, m, quot, n),
					// (m*n + int_div(p, n)*n) + int_rem(p, n) = m*n + (int_div(p, n)*n + int_rem(p, n))
					At(int_real_lift.AddAssoc, v.Mul.Apply(m, n), v.Mul.Apply(quot, n), rest)))
		}),
})}

// RemMulAdd — that same multiple leaves the remainder alone, and needs
// no guard to say so: at a zero divisor both sides hand their whole
// dividends back, and the two dividends differ by m · &0.
//
// This is the chapter's one remainder member that is not read off its
// quotient partner. Going through `remDiv` would put `DivMulAdd`'s
// guard inside a statement that has none, leaving the zero case to be
// settled here anyway and the difference of two `int_sub` terms to be
// rearranged on top of it. The uniqueness at the same exhibited pair
// costs one case split and no subtraction at all, so the two members
// come out as the same argument twice, differing only in which of
// `DivUnique` and `RemUnique` they take.
//
// Exported on its own, for `DivMulAdd`'s reason.
var RemMulAdd = remMulAddThm{family.Add(registry.ProofEntry{
	Name: "RemMulAdd",
	Key:  "prop_b6de4a907271bb37",
	Build: family.Theorem(
		"∀m n p:int. rem(m * n + p, n) = rem(p, n)",
		func(a *Argument, m Term, n *TermWrapper, p Term) {
			v := ops(a.Ctx())
			zero := v.Zero
			dividend := v.Add.Apply(v.Mul.Apply(m, n), p)
			quot, rest := v.IntDiv.Apply(p, n), v.IntRem.Apply(p, n)

			nonZero := a.Unless(
				n.Eq(zero),
				"n = &0: a zero divisor leaves every dividend over whole, so each side is its own dividend",
				Given(func(z *Argument, isZero Fact) {
					z.Show(
						"and the two dividends differ by m · &0, which is &0",
						By(
							isZero,
							At(RemByZero, dividend),           // int_rem(m*n + p, &0) = m*n + p
							At(RemByZero, p),                  // int_rem(p, &0) = p
							At(int_real_lift.MulRightZero, m), // m * &0 = &0
							int_real_lift.AddLeftIdentity))
				}))

			a.Show(
				"away from &0 the pair (m + div(p, n), rem(p, n)) "+
					"decomposes m·n + p, and its remainder is the one p had",
				By(
					nonZero,
					// m*n + p = (m + int_div(p, n)) * n + int_rem(p, n) ∧ &0 ≤ int_rem(p, n) ∧ int_rem(p, n) < |n|
					// ⇒ int_rem(m*n + p, n) = int_rem(p, n)
					At(RemUnique, dividend, n, v.Add.Apply(m, quot), rest),
					// n ≠ &0 ⇒ int_div(p, n) * n + int_rem(p, n) = p ∧ &0 ≤ int_rem(p, n) ∧ int_rem(p, n) < |n|
					At(DivisionAlgorithm, p, n),
					// (m + int_div(p, n)) * n = m*n + int_div(p, n)*n
					At(int_real_lift.RightDistrib, m, quot, n),
					// (m*n + int_div(p, n)*n) + int_rem(p, n) = m*n + (int_div(p, n)*n + int_rem(p, n))
					At(int_real_lift.AddAssoc, v.Mul.Apply(m, n), v.Mul.Apply(quot, n), rest)))
		}),
})}

// transposeProduct and commuteSum are the two moves both packings below
// are built out of, and each is the same shape: state the rearrangement
// as the ground equation it is, then spend it on the goal.
//
// Spending it on the goal rather than beside the cite is `RemMul`'s
// point above: a commutation reaching inside `int_div(_, n)` or `int_rem(_, n)`
// is rewriting the statement into the law's, which is what these
// conjuncts do, and not a further fact the law's conclusion needs.
func transposeProduct(d *Argument, x, y Term) {
	v := ops(d.Ctx())

	flip := d.Have(
		"a product reads either way round",
		MakeProp(v.Mul.Apply(x, y).Eq(v.Mul.Apply(y, x))),
		Cite(int_real_lift.MulSym))
	d.Do(flip.Rw()) // ↦ x·y becomes y·x wherever the goal has it
}

// commuteSum is transposeProduct's additive twin.
func commuteSum(d *Argument, x, y Term) {
	v := ops(d.Ctx())

	flip := d.Have(
		"a sum reads either way round",
		MakeProp(v.Add.Apply(x, y).Eq(v.Add.Apply(y, x))),
		Cite(int_real_lift.AddSym))
	d.Do(flip.Rw()) // ↦ x + y becomes y + x wherever the goal has it
}

// DivMulAddClauses is the four-way packing of `DivMulAdd`: the law and
// its three rearrangements — the multiple's factors transposed, the
// multiple added on the right, and both at once. It proves no
// arithmetic of its own. Each conjunct rearranges its own statement
// into the law's and then cites the law, so the three differ only in
// how many rearrangements that takes: one, two, three.
var DivMulAddClauses = divMulAddClausesThm{family.Add(registry.ProofEntry{
	Name: "DivMulAddClauses",
	Key:  "prop_35d336d471edb8a1",
	Build: family.Theorem(
		"(∀m n p:int. n ≠ &0 ⇒ div(m * n + p, n) = m + div(p, n)) ∧ "+
			"((∀m n p:int. n ≠ &0 ⇒ div(n * m + p, n) = m + div(p, n)) ∧ "+
			"    ((∀m n p:int. n ≠ &0 ⇒ div(p + m * n, n) = div(p, n) + m) ∧ "+
			"        (∀m n p:int. n ≠ &0 ⇒ div(p + n * m, n) = div(p, n) + m)))",
		func(a *Argument) {
			v := ops(a.Ctx())

			a.Do(SplitConjAll(
				Case(
					"the law as it stands",
					Cite(DivMulAdd)),
				Case(
					"the multiple with its factors transposed",
					Derive(func(d *Argument) {
						m, n, p := d.Fix(), d.Fix(), d.Fix()
						nonZero := d.Assume()

						transposeProduct(d, n, m) // ↦ int_div(m*n + p, n) = m + int_div(p, n)

						d.Show(
							"and that dividend is the law's",
							By(nonZero, At(DivMulAdd, m, n, p)))
					})),
				Case(
					"the multiple added on the right instead",
					Derive(func(d *Argument) {
						m, n, p := d.Fix(), d.Fix(), d.Fix()
						nonZero := d.Assume()

						commuteSum(d, p, v.Mul.Apply(m, n))    // ↦ int_div(m*n + p, n) = int_div(p, n) + m
						commuteSum(d, v.IntDiv.Apply(p, n), m) // ↦ int_div(m*n + p, n) = m + int_div(p, n)

						d.Show(
							"and both sides now read as the law states them",
							By(nonZero, At(DivMulAdd, m, n, p)))
					})),
				Case(
					"transposed and added on the right: both rearrangements at once",
					Derive(func(d *Argument) {
						m, n, p := d.Fix(), d.Fix(), d.Fix()
						nonZero := d.Assume()

						transposeProduct(d, n, m)              // ↦ int_div(p + m*n, n) = int_div(p, n) + m
						commuteSum(d, p, v.Mul.Apply(m, n))    // ↦ int_div(m*n + p, n) = int_div(p, n) + m
						commuteSum(d, v.IntDiv.Apply(p, n), m) // ↦ int_div(m*n + p, n) = m + int_div(p, n)

						d.Show(
							"and both sides now read as the law states them",
							By(nonZero, At(DivMulAdd, m, n, p)))
					})),
			))
		}),
})}

// RemMulAddClauses is the same packing on the remainder side. Its
// right-hand side is already int_rem(p, n) whatever the dividend looks
// like, so only the dividend is ever moved — which makes the two
// conjuncts that reorder the SUM one rearrangement shorter here than
// their `int_div` counterparts.
var RemMulAddClauses = remMulAddClausesThm{family.Add(registry.ProofEntry{
	Name: "RemMulAddClauses",
	Key:  "prop_d93216a6021be594",
	Build: family.Theorem(
		"(∀m n p:int. rem(m * n + p, n) = rem(p, n)) ∧ "+
			"((∀m n p:int. rem(n * m + p, n) = rem(p, n)) ∧ "+
			"    ((∀m n p:int. rem(p + m * n, n) = rem(p, n)) ∧ (∀m n p:int. rem(p + n * m, n) = rem(p, n))))",
		func(a *Argument) {
			v := ops(a.Ctx())

			a.Do(SplitConjAll(
				Case(
					"the law as it stands",
					Cite(RemMulAdd)),
				Case(
					"the multiple with its factors transposed",
					Derive(func(d *Argument) {
						m, n := d.Fix(), d.Fix()
						d.Fix()

						transposeProduct(d, n, m) // ↦ int_rem(m*n + p, n) = int_rem(p, n)

						d.Show(
							"and that dividend is the law's",
							By(RemMulAdd))
					})),
				Case(
					"the multiple added on the right instead",
					Derive(func(d *Argument) {
						m, n, p := d.Fix(), d.Fix(), d.Fix()

						commuteSum(d, p, v.Mul.Apply(m, n)) // ↦ int_rem(m*n + p, n) = int_rem(p, n)

						d.Show(
							"and that dividend is the law's",
							By(RemMulAdd))
					})),
				Case(
					"transposed and added on the right: both rearrangements at once",
					Derive(func(d *Argument) {
						m, n, p := d.Fix(), d.Fix(), d.Fix()

						transposeProduct(d, n, m)           // ↦ int_rem(p + m*n, n) = int_rem(p, n)
						commuteSum(d, p, v.Mul.Apply(m, n)) // ↦ int_rem(m*n + p, n) = int_rem(p, n)

						d.Show(
							"and that dividend is the law's",
							By(RemMulAdd))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Division survives the embedding
// ---------------------------------------------------------------------------
//
// division survives the embedding: dividing in ℕ and dividing in ℤ are the
// same computation, read across &.
//
// ℤ's `int_div`/`int_rem` are pinned by the uniqueness law `DivModUnique`: a
// candidate quotient-remainder pair meeting its three conditions is THE
// pair. So the transport is not an induction but an exhibition — hand
// that law the pair ℕ already computed, embedded, having checked its
// three conditions one `Have` at a time. It answers for quotient and
// remainder together, which is why the work is one lemma about both and
// each transport law is one of its halves.

// divRemPair — both transport laws at once, because uniqueness delivers
// them at once.
//
// At a nonzero divisor `nat_div_mod.Division`'s equation and remainder bound
// cross into ℤ on `int_embed.OfNumMul` and `OfNumAdd` (& is a ring
// map), `OfNumLt` (& is an order embedding) and `OfNumAbs` (|·| is
// inert on the image of &); nonnegativity is `EmbedNonneg` at the ℕ
// remainder. At a zero divisor there is no equation to read and the two
// conventions are simply compared.
var divRemPair = divRemPairThm{family.Add(registry.ProofEntry{
	Name: "divRemPair",
	Key:  "prop_b23b2063d41b0abb",
	Build: family.Theorem("∀m n:num. &div(m, n) = div(&m, &n) ∧ &rem(m, n) = rem(&m, &n)",
		func(a *Argument, m Term, n *TermWrapper) {
			ctx := a.Ctx()
			v := ops(ctx)
			numBinOp := MakeFun(NumType, MakeFun(NumType, NumType))

			// ℕ's division operators as builders. Declared here rather than
			// in `vocab.go` because they belong to the ℕ domain's table —
			// the chapter's alphabet is ℤ's — and this file is where the
			// naturals a ℤ-division agrees with are named.
			natDiv := ctx.Const("nat_div", numBinOp)
			natMod := ctx.Const("nat_mod", numBinOp)
			zero := ctx.Const("_0", NumType)

			quot, rest := natDiv.Apply(m, n), natMod.Apply(m, n)
			em, en := v.OfNum.Apply(m), v.OfNum.Apply(n)
			eQuot, eRest := v.OfNum.Apply(quot), v.OfNum.Apply(rest)

			// &(nat_div(m₀, n₀))·&n₀ + &(nat_mod(m₀, n₀)) — the division equation's
			// right-hand side, read in ℤ. Built, not written: an all-`&`
			// term with nothing int-typed beside it is a statement about ℝ.
			zRight := v.Add.Apply(v.Mul.Apply(eQuot, en), eRest)

			a.Cases(n.Eq(zero))
			a.When(
				"n₀ = 0: no division to do — each side answers with its own convention, and the two agree",
				func(b *Argument, isZero Fact) {
					b.Do(
						isZero.Rw(), // n₀ ↦ 0: both sides now sit at the zero divisor
						SplitConj(
							Case(
								"quotient: ℕ hands back 0, ℤ hands back &0",
								Cite(nat_div_mod.DivZero, m), // nat_div(m₀, 0) = 0
								Cite(DivByZero),              // ↦ &(nat_div(m₀, 0)) = &0
							),
							Case(
								"remainder: ℕ hands back m₀, ℤ hands back &m₀",
								Cite(nat_div_mod.ModZero, m), // nat_mod(m₀, 0) = m₀
								Cite(RemByZero),              // ↦ &(nat_mod(m₀, 0)) = &m₀
							),
						),
					)
				})
			a.Otherwise(
				"n₀ ≠ 0: ℕ's quotient and remainder, embedded, meet ℤ's division spec — so they are ℤ's",
				func(b *Argument, nonzero Fact) {
					spec := b.Have(
						"ℕ divides m₀ by n₀: div(m₀, n₀) copies of n₀ with rem(m₀, n₀) left over, that remainder below n₀",
						"m₀ = div(m₀, n₀) * n₀ + rem(m₀, n₀) ∧ rem(m₀, n₀) < n₀",
						By(nonzero, At(nat_div_mod.Division, m, n)))

					equation := b.Have(
						"& carries the equation across, being multiplicative and additive",
						MakeProp(em.Eq(zRight)),
						By(spec, int_embed.OfNumMul, int_embed.OfNumAdd))

					below := b.Have(
						"… and the bound across: & is an order embedding, and |·| acts trivially on its image",
						MakeProp(v.Lt.Apply(eRest, v.Abs.Apply(en))),
						By(spec, int_embed.OfNumLt, int_embed.OfNumAbs))

					// The embedded remainder is nonnegative. A premise, not a
					// step: EmbedNonneg says every image is, and rest is one.
					nonneg := At(int_embed.EmbedNonneg, rest)

					// One deduction, two conjuncts: the law names the
					// quotient and the remainder in the same breath, so
					// the goal's halves close together.
					b.Show(
						"uniqueness at (&m₀, &n₀): the pair (&(div(m₀, n₀)), "+
							"&(rem(m₀, n₀))) satisfying those three IS (div, rem)",
						By(equation, nonneg, below, At(DivModUnique, em, en, eQuot, eRest)))
				})
		}),
})}

// OfNumRem — the remainder half of `divRemPair`.
var OfNumRem = ofNumRemThm{family.Add(registry.ProofEntry{
	Name: "OfNumRem",
	Key:  "prop_218865c9d6fb5a86",
	Build: family.Theorem("∀m n:num. &rem(m, n) = rem(&m, &n)",
		func(a *Argument, m, n Term) {
			a.Show(
				"the remainder half of the pair at (m₀, n₀)",
				By(At(divRemPair, m, n)))
		}),
})}

// OfNumDiv — the quotient half of `divRemPair`.
var OfNumDiv = ofNumDivThm{family.Add(registry.ProofEntry{
	Name: "OfNumDiv",
	Key:  "prop_fefd80eda66203e2",
	Build: family.Theorem("∀m n:num. &div(m, n) = div(&m, &n)",
		func(a *Argument, m, n Term) {
			a.Show(
				"the quotient half of the pair at (m₀, n₀)",
				By(At(divRemPair, m, n)))
		}),
})}
