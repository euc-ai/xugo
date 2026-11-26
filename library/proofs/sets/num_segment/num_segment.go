// num_segment.go — the chapter: the interval `m .. n`.
//
// Five parts, marked by banners:
//
// - The unfolding law, and its corollaries at a zero lower bound
// - What an interval IS
// - The one-sided forms
// - Every interval is finite
// - How many numbers an interval holds

package num_segment

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The unfolding law, and its corollaries at a zero lower bound
// ---------------------------------------------------------------------------
//
// `m .. n` is defined as a comprehension over ℕ,
//
// 	m .. n = {x | m ≤ x ∧ x ≤ n}
//
// and membership in a comprehension is the comprehension's own
// condition, read at the point. That single observation is `Membership`;
// the definition declares it (MembershipRead), so the closers read
// `x ∈ m .. n` as the bounds by themselves, and the members ABOUT `..`
// argue about `≤` on the bounds, citing `Membership` where a rewrite
// needs it as a statement. The one-sided forms below
// are the exception that fixes the scope — two of them mention `..`
// nowhere and reach `<` directly.
//
// The first corollary puts the lower bound at 0, where it stops
// constraining anything: no natural is below 0. The two after it read
// that through a map normalized on `0 .. n` (functions' `normalize_on`):
// at a coordinate the bound alone decides the value, the map's own up to
// n and the default past it.

// IntervalDef — the interval defined: the numbers between the bounds,
// as a comprehension. Spelled `numseg` in the equation, the operator
// `..` having no head-position spelling.
var IntervalDef = intervalDefThm{family.Define(registry.DefEntry{
	Name:      "IntervalDef",
	Key:       "prop_8cbe5809ca46a45d",
	Const:     "..",
	Spelled:   "numseg",
	Type:      "num → num → set(num)",
	Equations: []string{"∀m n:num. numseg(m, n) = {x:num | m ≤ x ∧ x ≤ n}"},
	// The closers read x ∈ m .. n as m ≤ x ∧ x ≤ n.
	MembershipRead: true,
})}

// Membership — a number lies in `m .. n` exactly when it lies between
// the bounds.
//
// Two moves and no premises.
var Membership = membershipThm{family.Add(registry.ProofEntry{
	Name: "Membership",
	Key:  "prop_5fd79860cdebab4e",
	Build: family.Theorem(
		"∀x m n:num. x ∈ m .. n ⇔ m ≤ x ∧ x ≤ n",
		func(a *Argument, x, m, n Term) {
			// ↦ x₀ ∈ {x | m₀ ≤ x ∧ x ≤ n₀} ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀ — the
			// chapter's one unfolding, on the left side only.
			a.Do(Unfold(IntervalDef))

			a.Show(
				"membership in a comprehension is its condition, read at x₀",
				BySets())
		}),
})}

// MembershipFromZero — from a zero lower bound, the interval is
// everything up to n.
var MembershipFromZero = membershipFromZeroThm{family.Add(registry.ProofEntry{
	Name: "MembershipFromZero",
	Key:  "prop_3acffc18280b302e",
	Build: family.Theorem("∀m n:num. m ∈ 0 .. n ⇔ m ≤ n",
		func(a *Argument, m, n Term) {
			zero := a.Ctx().Numeral(0)
			a.Show(
				"0 ≤ m₀ is free, so what is left of membership is the upper bound",
				By(
					At(Membership, m, zero, n), // m₀ ∈ 0 .. n₀ ⇔ 0 ≤ m₀ ∧ m₀ ≤ n₀
					nat_order.ZeroLessEq))
		}),
})}

// NormalizeOnSegmentIn — a map normalized on the interval from 0 to n
// keeps its own value at every coordinate up to n: the bound alone puts
// the coordinate in the interval, and there normalizing changes nothing.
var NormalizeOnSegmentIn = normalizeOnSegmentInThm{family.Add(registry.ProofEntry{
	Name: "NormalizeOnSegmentIn",
	Key:  "prop_32ab511dabfed93f",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀z:A. ∀f:(num → A). ∀j:num.",
		Hypotheses: []string{
			"j ≤ n",
		},
		Conclusion: "normalize_on(0 .. n, z, f, j) = f(j)",
	},
		func(a *Argument, n *Expr[Nat], z *Expr[A], f *Arrow[Nat, A], j *Expr[Nat], bounded Fact) {
			segment := a.TermAs[Set[Nat]]("0 .. n")
			inSegment := a.Have(
				"from 0 the interval asks only the upper bound, so j lies in it",
				"j ∈ 0 .. n",
				By(bounded, MembershipFromZero.At(j, n)))
			a.Show(
				"and on the interval the normalized map is f itself",
				By(inSegment, functions.NormalizeOnIn.At(segment, z, f, j)))
		}),
})}

// NormalizeOnSegmentOut — a map normalized on the interval from 0 to n
// takes the default at every coordinate past n: such a coordinate fails
// the one bound the interval asks, and off the interval normalizing
// leaves only the default.
var NormalizeOnSegmentOut = normalizeOnSegmentOutThm{family.Add(registry.ProofEntry{
	Name: "NormalizeOnSegmentOut",
	Key:  "prop_3a3c20c783fe61e4",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀z:A. ∀f:(num → A). ∀j:num.",
		Hypotheses: []string{
			"n < j",
		},
		Conclusion: "normalize_on(0 .. n, z, f, j) = z",
	},
		func(a *Argument, n *Expr[Nat], z *Expr[A], f *Arrow[Nat, A], j *Expr[Nat], beyond Fact) {
			segment := a.TermAs[Set[Nat]]("0 .. n")
			offSegment := a.Have(
				"past n, j is not bounded by n, the one bound the interval from 0 asks",
				"j ∉ 0 .. n",
				By(beyond, nat_order.NotLessEq.At(j, n)))
			a.Show(
				"and off the interval the normalized map is the default",
				By(offSegment, functions.NormalizeOnOut.At(segment, z, f, j)))
		}),
})}

// ---------------------------------------------------------------------------
// What an interval IS
// ---------------------------------------------------------------------------
//
// what an interval IS: when it is empty, when it is a singleton, how it
// meets ⊆ ∩ and disjoint, how it shifts, how it recurses at each end, and
// how it cuts in two.
//
// One method runs through the whole file. A set equation is settled one
// point at a time: `set_basic.Extension` turns it into a question about
// membership, `Membership` turns membership into a pair of inequalities,
// and what is left is a fact about `≤` on the bounds. Each member names
// the order facts it ends at, and that is the only thing they do not
// share. Four members never reach a point through `Extension` — `Rec`
// discharges a conditional, `Subset` tests the inclusion at just the two
// endpoints, `Disjoint` goes through `Inter` and `Empty`, and `AddSplit`
// renames a cut `CombineRight` has already made — but they end in the
// same place.
//
// Three strands, in the order they appear below. (The chapter's four
// MOVEMENTS are the README's; this whole file is its second one.)
//
// The RECURSION is the interval read at a bound that has just moved by
// one. The bound step is:
//
// - at the top, the successor clause of `≤` read at the point
// (nat_order.LessEqSucClause), and its zero clause where the bound
// is 0 (nat_order.LessEqZeroClause);
// - at the bottom, `≤` split into equality and strict order, the
// strict order rewritten as a successor, and the successor as
// `+ 1` (nat_order.LessEqSplit, nat_order.SucLessEqIffLessThan,
// nat_arith.Add1);
// - at the top again, written with truncated subtraction, where the
// bound is a successor only away from 0. `RecRight` states the fact
// it needs once and proves it in those two cases — its own godoc
// says which laws carry each.
//
// The SHAPE is the interval at large: when it collapses to one point or
// to none, when one interval sits inside another, where two of them
// meet, when they miss each other entirely, and what shifting both
// bounds does. Its order facts are the ordinary ones — transitivity,
// antisymmetry, reflexivity, the duality between `≤` and `<`, and, for
// the shift, the laws that add a common summand to a comparison and
// cancel it again. There is one gap: ℕ's `nat_max` and `nat_min` are pure
// definitions and nat_order states no order law about them, so the two
// the overlap needs are derived in place, inside `Inter` and `Disjoint`
// (the comment above `Inter` says how).
//
// The CUT is the recursion at an interior point instead of at an end:
// an interval broken into the part below a chosen point and the part
// from it on. Its order content is that every point lies on one side of
// the cut — the duality between `≤` and `<`, plus the step from `<` to
// the successor. Only `CombineRight` argues that; the other two name
// the same cut by a different point, and each says which instance it is.

// Clauses is the recursion of `m .. n` on its upper bound: what the
// interval is when that bound is 0, and what it becomes when the bound
// grows by one. Both right-hand sides are conditionals because both
// bounds can leave the interval empty — at 0 unless the lower bound is
// 0 as well, and at suc n unless the lower bound has been reached.
//
// The two clauses are quantified separately, which is not decoration:
// the first mentions no upper bound at all, and folding them under one
// prefix would bind a variable it does not use.
var Clauses = clausesThm{family.Add(registry.ProofEntry{
	Name: "Clauses",
	Key:  "prop_bf8762f8bd7e1b89",
	Build: family.Theorem(
		"(∀m:num. m .. 0 = COND(m = 0, {0}, ∅)) ∧ "+
			"(∀m n:num. m .. suc(n) = COND(m ≤ suc(n), insert(suc(n), m .. n), m .. n))",
		func(a *Argument) {
			v := ops(a.Ctx())
			inInsert := set_basic.InInsert.Inst[Nat]()

			a.Do(SplitConj(
				Case(
					"at the bound 0 the only candidate point is 0 itself, "+
						"and it is admitted exactly when the lower bound is 0 too",
					Derive(func(a *Argument) {
						m := a.Fix()
						zero := a.Ctx().Numeral(0)
						x := samePoints(a, "∀x:num. x ∈ m₀ .. 0 ⇔ x ∈ COND(m₀ = 0, {0}, ∅)")
						a.Show(
							"x₀ ≤ 0 pins x₀ to 0, and m₀ ≤ 0 pins m₀ to 0 — which is the conditional's own guard",
							By(
								At(Membership, x, m, zero),         // x₀ ∈ m₀ .. 0 ⇔ m₀ ≤ x₀ ∧ x₀ ≤ 0
								At(inInsert, v.EmptySet, zero, x),  // x₀ ∈ {0} ⇔ x₀ = 0 ∨ x₀ ∈ ∅
								At(set_basic.NotInEmpty, x),        // x₀ ∉ ∅
								At(nat_order.LessEqZeroClause, x),  // x₀ ≤ 0 ⇔ x₀ = 0
								At(nat_order.LessEqZeroClause, m))) // m₀ ≤ 0 ⇔ m₀ = 0
					})),
				Case(
					"raising the bound to suc n₀ admits one further point, "+
						"suc n₀ itself, and only if the lower bound reaches it",
					Derive(func(a *Argument) {
						m := a.Fix()
						n := a.Fix()
						top := v.Suc(n)
						x := samePoints(
							a, "∀x:num. x ∈ m₀ .. suc(n₀) ⇔ x ∈ COND(m₀ ≤ suc(n₀), insert(suc(n₀), m₀ .. n₀), m₀ .. n₀)")
						a.Show(
							"the successor clause of ≤ splits the upper bound into the old "+
								"one and the new top; the lower bound is untouched either way",
							By(
								At(Membership, x, m, top), // x₀ ∈ m₀ .. suc(n₀) ⇔ m₀ ≤ x₀ ∧ x₀ ≤ suc(n₀)
								At(Membership, x, m, n),   // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
								// x₀ ∈ insert(suc(n₀), m₀ .. n₀) ⇔ x₀ = suc(n₀) ∨ x₀ ∈ m₀ .. n₀
								At(inInsert, v.Seg(m, n), top, x),
								At(nat_order.LessEqSucClause, x, n))) // x₀ ≤ suc(n₀) ⇔ x₀ ≤ n₀ ∨ x₀ = suc(n₀)
					})),
			))
		}),
})}

// Rec is Clauses' successor clause read under its guard: once the
// lower bound is known to reach the new top, the conditional is
// settled and the interval simply gains that point.
//
// It can also be proved independently of the clauses, from membership
// again. Both routes close in a single premise-list
// step, so the choice is which reads better — and a corollary that
// only has to discharge a conditional is the shorter thing to read.
var Rec = recThm{family.Add(registry.ProofEntry{
	Name: "Rec",
	Key:  "prop_6a66c2b3a4ae95a7",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ suc(n)",
		},
		Conclusion: "m .. suc(n) = insert(suc(n), m .. n)",
	},
		func(a *Argument, m, n Term, reaches Fact) {
			a.Show(
				"the guard holds, so the successor clause's conditional takes its insert branch",
				By(reaches, Clauses))
		}),
})}

// RecLeft peels the lower bound off a non-empty interval: `m` is its
// least point, and what remains starts one higher.
var RecLeft = recLeftThm{family.Add(registry.ProofEntry{
	Name: "RecLeft",
	Key:  "prop_e87ec2ecb76738e3",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "m .. n = insert(m, m + 1 .. n)",
	},
		func(a *Argument, m, n Term, nonEmpty Fact) {
			v := ops(a.Ctx())
			inInsert := set_basic.InInsert.Inst[Nat]()
			up := v.Add(m, a.Ctx().Numeral(1)) // m₀ + 1, the raised lower bound
			x := samePoints(a, "∀x:num. x ∈ m₀ .. n₀ ⇔ x ∈ insert(m₀, (m₀ + 1) .. n₀)")

			aboveLower := a.Have(
				"a point reaching m₀ either is m₀ or already reaches m₀ + 1",
				"m₀ ≤ x₀ ⇔ x₀ = m₀ ∨ m₀ + 1 ≤ x₀",
				By(
					At(nat_order.LessEqSplit, m, x),          // m₀ ≤ x₀ ⇔ m₀ < x₀ ∨ m₀ = x₀
					At(nat_order.SucLessEqIffLessThan, m, x), // m₀ < x₀ ⇔ suc(m₀) ≤ x₀
					nat_arith.Add1))

			a.Show(
				"both sides then ask the same of the upper bound, and "+
					"m₀ itself is admitted because the interval is non-empty",
				By(
					nonEmpty,
					aboveLower,
					At(Membership, x, m, n),  // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
					At(Membership, x, up, n), // x₀ ∈ (m₀ + 1) .. n₀ ⇔ m₀ + 1 ≤ x₀ ∧ x₀ ≤ n₀
					// x₀ ∈ insert(m₀, (m₀ + 1) .. n₀) ⇔ x₀ = m₀ ∨ x₀ ∈ (m₀ + 1) .. n₀
					At(inInsert, v.Seg(up, n), m, x)))
		}),
})}

// RecRight peels the upper bound off a non-empty interval — the mirror
// of RecLeft, and the one member here whose bound step is written with
// truncated subtraction.
//
// That is the whole difference. The bound step holds for every n,
// including 0, where the subtraction truncates back to 0 and the two
// alternatives collapse into one — so it is not an instance of any
// successor law, and it is proved in two cases: away from 0 the bound
// IS a successor and `nat_order.LessEqSucClause` says exactly this, and
// at 0 both sides come to x = 0. It remains ONE fact, stated once and
// used once; the split is inside its proof, not in the member's.
var RecRight = recRightThm{family.Add(registry.ProofEntry{
	Name: "RecRight",
	Key:  "prop_92bcc3b2713424ad",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "m .. n = insert(n, m .. n - 1)",
	},
		func(a *Argument, m Term, n *TermWrapper, nonEmpty Fact) {
			v := ops(a.Ctx())
			inInsert := set_basic.InInsert.Inst[Nat]()
			zero, one := a.Ctx().Numeral(0), a.Ctx().Numeral(1)
			down := v.Sub(n, one) // n₀ - 1, the lowered upper bound
			x := samePoints(a, "∀x:num. x ∈ m₀ .. n₀ ⇔ x ∈ insert(n₀, m₀ .. (n₀ - 1))")

			belowUpper := a.Have(
				"a point bounded by n₀ either is n₀ or is already bounded by n₀ - 1",
				"x₀ ≤ n₀ ⇔ x₀ = n₀ ∨ x₀ ≤ n₀ - 1",
				Derive(func(a *Argument) {
					nonZero := a.Unless(
						n.Eq(zero),
						"n₀ = 0: the lowered bound truncates back to 0, so the two alternatives coincide",
						Given(func(a *Argument, isZero Fact) { // isZero: n₀ = 0
							a.Show(
								"and both then come to x₀ = 0, which is all a bound of 0 admits",
								By(
									isZero,
									At(nat_monus.SubEqZero, n, one),    // n₀ - 1 = 0 ⇔ n₀ ≤ 1
									At(nat_order.ZeroLessEq, one),      // 0 ≤ 1
									At(nat_order.LessEqZeroClause, x))) // x₀ ≤ 0 ⇔ x₀ = 0
						}))

					succeeds := a.Have(
						"away from 0 the bound is a successor, and n₀ - 1 is what it succeeds",
						"suc(n₀ - 1) = n₀",
						By(nonZero, At(nat_monus.SucOfSubOne, n))) // n₀ ≠ 0 ⇒ suc(n₀ - 1) = n₀

					a.Show(
						"so the claim is the successor clause of ≤ read at that predecessor",
						By(
							succeeds,
							At(nat_order.LessEqSucClause, x, down))) // x₀ ≤ suc(n₀ - 1) ⇔ x₀ ≤ n₀ - 1 ∨ x₀ = suc(n₀ - 1)
				}))

			a.Show(
				"both sides then ask the same of the lower bound, and "+
					"n₀ itself is admitted because the interval is non-empty",
				By(
					nonEmpty,
					belowUpper,
					At(Membership, x, m, n),    // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
					At(Membership, x, m, down), // x₀ ∈ m₀ .. (n₀ - 1) ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀ - 1
					// x₀ ∈ insert(n₀, m₀ .. (n₀ - 1)) ⇔ x₀ = n₀ ∨ x₀ ∈ m₀ .. (n₀ - 1)
					At(inInsert, v.Seg(m, down), n, x)))
		}),
})}

// Sing — an interval whose two bounds coincide is the single point they
// both name.
//
// Antisymmetry is the entire content: the points between n₀ and n₀ are
// the x with n₀ ≤ x and x ≤ n₀, and that pair of inequalities IS x = n₀.
var Sing = singThm{family.Add(registry.ProofEntry{
	Name: "Sing",
	Key:  "prop_e4fb50a91d6cf7cd",
	Build: family.Theorem("∀n:num. n .. n = {n}",
		func(a *Argument, n Term) {
			x := samePoints(a, "∀x:num. x ∈ n₀ .. n₀ ⇔ x ∈ {n₀}")
			// `reading` rather than a cite of `set_basic.InSing`: that row will
			// not ground at witnesses in either binder order, and naming the
			// membership as a fact sidesteps the question instead of
			// documenting it. It is the last rung of the ladder, not a blanket
			// replacement for a ground cite — see `atNum`.
			inSingleton := reading(a, "x₀ ∈ {n₀} ⇔ x₀ = n₀")
			a.Show(
				"both bounds are n₀, so both sides say the two inequalities that pin x₀ to n₀",
				By(
					At(Membership, x, n, n), // x₀ ∈ n₀ .. n₀ ⇔ n₀ ≤ x₀ ∧ x₀ ≤ n₀
					inSingleton,
					nat_order.LessEqAntisym))
		}),
})}

// Empty — an interval is empty exactly when its bounds are out of
// order, and each direction is one endpoint's story.
//
// Left to right the interval's own lower bound is the witness: if the
// bounds WERE in order, m₀ would be a point of the interval, and an
// empty set has none. Right to left there can be no point at all, since
// any would sit between the bounds and so put them back in order.
//
// The chapter carries only the biconditional; a consumer that wants one
// implication takes the arm it needs.
var Empty = emptyThm{family.Add(registry.ProofEntry{
	Name: "Empty",
	Key:  "prop_e3a81db160b2e573",
	Build: family.Theorem("∀m n:num. m .. n = ∅ ⇔ n < m",
		func(a *Argument, m, n Term) {
			a.Iff()
			a.Forward(
				"an empty interval cannot hold m₀, which it would if the bounds were in order",
				func(a *Argument, empty Fact) { // empty: m₀ .. n₀ = ∅
					a.Show(
						"m₀ ≤ m₀ is free, so m₀ ≤ n₀ alone would put m₀ in the interval — that is, in ∅",
						By(
							empty,
							At(Membership, m, m, n),     // m₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ m₀ ∧ m₀ ≤ n₀
							At(set_basic.NotInEmpty, m), // m₀ ∉ ∅
							At(nat_order.LessEqRefl, m), // m₀ ≤ m₀
							nat_order.NotLessEq))
				})
			a.Backward(
				"past the upper bound no point is left: one would sit between the bounds and so put them in order",
				func(a *Argument, crossed Fact) { // crossed: n₀ < m₀
					x := samePoints(a, "∀x:num. x ∈ m₀ .. n₀ ⇔ x ∈ ∅")
					a.Show(
						"m₀ ≤ x₀ and x₀ ≤ n₀ compose to m₀ ≤ n₀, which n₀ < m₀ denies",
						By(
							crossed,
							At(Membership, x, m, n),            // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
							At(set_basic.NotInEmpty, x),        // x₀ ∉ ∅
							At(nat_order.LessEqTrans, m, x, n), // m₀ ≤ x₀ ∧ x₀ ≤ n₀ ⇒ m₀ ≤ n₀
							At(nat_order.NotLessEq, m, n)))     // ¬(m₀ ≤ n₀) ⇔ n₀ < m₀
				})
		}),
})}

// Subset — one interval sits inside another exactly when it is empty,
// or when the outer one's bounds are at least as generous at both ends.
//
// The ⇒ direction is where the shape of the argument shows: an
// inclusion is a statement about every point, and it is tested at just
// two — the endpoints m₀ and n₀, which a non-empty interval contains and
// which pin p₀ ≤ m₀ and n₀ ≤ q₀ between them.
var Subset = subsetThm{family.Add(registry.ProofEntry{
	Name: "Subset",
	Key:  "prop_253b72da28489c75",
	Build: family.Theorem("∀m n p q:num. m .. n ⊆ p .. q ⇔ n < m ∨ n ≤ q ∧ p ≤ m",
		// ↦ ∀m n p q. (∀x. x ∈ m .. n ⇒ x ∈ p .. q) ⇔ … — an inclusion IS a
		// pointwise implication by subset's defining equation, so it is
		// unfolded and not cited.
		Opening(Unfold(set_basic.SubsetDef), func(a *Argument, m, n, p, q *Expr[Nat]) {
			a.Iff()
			a.Forward(
				"test the inclusion at the two endpoints: unless the "+
					"interval is empty it holds both, so the outer one does",
				func(a *Argument, inside Fact) { // inside: ∀x. x ∈ m₀ .. n₀ ⇒ x ∈ p₀ .. q₀
					a.Show(
						"m₀ lands in p₀ .. q₀, giving p₀ ≤ m₀; n₀ lands there too, giving n₀ ≤ q₀",
						By(
							inside.At(m),                   // m₀ ∈ m₀ .. n₀ ⇒ m₀ ∈ p₀ .. q₀
							inside.At(n),                   // n₀ ∈ m₀ .. n₀ ⇒ n₀ ∈ p₀ .. q₀
							At(Membership, m, m, n),        // m₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ m₀ ∧ m₀ ≤ n₀
							At(Membership, n, m, n),        // n₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ n₀ ∧ n₀ ≤ n₀
							At(Membership, m, p, q),        // m₀ ∈ p₀ .. q₀ ⇔ p₀ ≤ m₀ ∧ m₀ ≤ q₀
							At(Membership, n, p, q),        // n₀ ∈ p₀ .. q₀ ⇔ p₀ ≤ n₀ ∧ n₀ ≤ q₀
							At(nat_order.LessEqRefl, m),    // m₀ ≤ m₀
							At(nat_order.LessEqRefl, n),    // n₀ ≤ n₀
							At(nat_order.NotLessEq, m, n))) // ¬(m₀ ≤ n₀) ⇔ n₀ < m₀
				})
			a.Backward(
				"two readings: n₀ < m₀ leaves no point to place, "+
					"and otherwise p₀ ≤ m₀ ≤ x₀ and x₀ ≤ n₀ ≤ q₀ place it",
				func(a *Argument, why Fact) { // why: n₀ < m₀ ∨ n₀ ≤ q₀ ∧ p₀ ≤ m₀
					x := a.Fix()
					a.Show(
						"each disjunct is enough: the first contradicts x₀'s own bounds, the second widens them",
						By(
							why,
							At(Membership, x, m, n),            // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
							At(Membership, x, p, q),            // x₀ ∈ p₀ .. q₀ ⇔ p₀ ≤ x₀ ∧ x₀ ≤ q₀
							At(nat_order.LessEqTrans, m, x, n), // m₀ ≤ x₀ ∧ x₀ ≤ n₀ ⇒ m₀ ≤ n₀
							At(nat_order.LessEqTrans, p, m, x), // p₀ ≤ m₀ ∧ m₀ ≤ x₀ ⇒ p₀ ≤ x₀
							At(nat_order.LessEqTrans, x, n, q), // x₀ ≤ n₀ ∧ n₀ ≤ q₀ ⇒ x₀ ≤ q₀
							At(nat_order.NotLessEq, m, n)))     // ¬(m₀ ≤ n₀) ⇔ n₀ < m₀
				})
		})),
})}

// ℕ's nat_max and nat_min have no order laws in nat_order, only their
// definitions — `nat_max(m, p) = COND(m ≤ p, p, m)` — so `Inter` and
// `Disjoint` below derive the nat_max-below and above-nat_min facts
// they need in place.
//
// Each derivation is the definition plus transitivity: the conditional
// picks one of the two arguments, and whichever it picks the other
// reaches it, so a bound on the chosen one is a bound on both. Where
// the guard fails, `NotLessEq` and `LessEqOfLessThan` turn that
// failure back into the inequality the other way round, which is what
// transitivity needs — the two readings of a failed guard: `x` not
// reaching `y` IS `y` strictly below `x` (nat_order.NotLessEq), and that strict
// comparison is the weak one transitivity takes (nat_order.LessEqOfLessThan). Both
// readings are stated first, each in a leaf of its own, rather than
// brought into the nat_max/nat_min closes: those goals carry the conditional
// the close has to split, and a law arriving against that shape is
// simplified on the way in rather than left as the ∀-statement a
// witness grounds.

// Inter — two intervals meet in an interval, whose lower bound is the
// larger of the two lower bounds and whose upper bound is the smaller of
// the two upper ones.
//
// Nothing here is about intersection as such: a point is in both
// intervals when it satisfies all four inequalities, and nat_max and nat_min are
// exactly the two ways of saying "both" — one about lower bounds, one
// about upper.
var Inter = interThm{family.Add(registry.ProofEntry{
	Name: "Inter",
	Key:  "prop_a9ef7cd39b46486a",
	Build: family.Theorem("∀m n p q:num. max(m, p) .. min(n, q) = intersection(m .. n, p .. q)",
		func(a *Argument, m, n, p, q Term) {
			v := ops(a.Ctx())
			inInter := set_basic.InInter.Inst[Nat]()
			lo, hi := v.Larger(m, p), v.Smaller(n, q) // the shared interval's own bounds
			x := samePoints(a, "∀x:num. x ∈ max(m₀, p₀) .. min(n₀, q₀) ⇔ x ∈ intersection(m₀ .. n₀, p₀ .. q₀)")

			// The failed-guard readings at each pair of bounds — the file
			// comment above says why each is a leaf of its own.
			loFailed := a.Have(
				"m₀ failing to reach p₀ puts p₀ strictly below it",
				"¬(m₀ ≤ p₀) ⇔ p₀ < m₀",
				By(nat_order.NotLessEq))
			loWeaker := a.Have(
				"and p₀ strictly below m₀ is p₀ at or below m₀",
				"p₀ < m₀ ⇒ p₀ ≤ m₀",
				By(At(nat_order.LessEqOfLessThan, p, m)))
			hiFailed := a.Have(
				"n₀ failing to reach q₀ puts q₀ strictly below it",
				"¬(n₀ ≤ q₀) ⇔ q₀ < n₀",
				By(nat_order.NotLessEq))
			hiWeaker := a.Have(
				"and q₀ strictly below n₀ is q₀ at or below n₀",
				"q₀ < n₀ ⇒ q₀ ≤ n₀",
				By(At(nat_order.LessEqOfLessThan, q, n)))

			fromBelow := a.Have(
				"reaching max(m₀, p₀) is reaching both of them",
				"max(m₀, p₀) ≤ x₀ ⇔ m₀ ≤ x₀ ∧ p₀ ≤ x₀",
				// ↦ COND(m₀ ≤ p₀, p₀, m₀) ≤ x₀ ⇔ … — nat_max's definition is
				// all nat_order says about it.
				Unfold(nat_order.NatMaxDef),
				By(
					Normalized,
					At(nat_order.LessEqTrans, m, p, x), // m₀ ≤ p₀ ∧ p₀ ≤ x₀ ⇒ m₀ ≤ x₀
					At(nat_order.LessEqTrans, p, m, x), // p₀ ≤ m₀ ∧ m₀ ≤ x₀ ⇒ p₀ ≤ x₀
					loFailed,
					loWeaker))
			fromAbove := a.Have(
				"staying under min(n₀, q₀) is staying under both of them",
				"x₀ ≤ min(n₀, q₀) ⇔ x₀ ≤ n₀ ∧ x₀ ≤ q₀",
				// ↦ x₀ ≤ COND(n₀ ≤ q₀, n₀, q₀) ⇔ …
				Unfold(nat_order.NatMinDef),
				By(
					Normalized,
					At(nat_order.LessEqTrans, x, n, q), // x₀ ≤ n₀ ∧ n₀ ≤ q₀ ⇒ x₀ ≤ q₀
					At(nat_order.LessEqTrans, x, q, n), // x₀ ≤ q₀ ∧ q₀ ≤ n₀ ⇒ x₀ ≤ n₀
					hiFailed,
					hiWeaker))

			a.Show(
				"so the shared interval admits x₀ under the same "+
					"four inequalities the two intervals together impose",
				By(
					fromBelow,
					fromAbove,
					// x₀ ∈ nat_max(m₀, p₀) .. nat_min(n₀, q₀) ⇔ nat_max(m₀, p₀) ≤ x₀ ∧ x₀ ≤ nat_min(n₀, q₀)
					At(Membership, x, lo, hi),
					At(Membership, x, m, n), // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
					At(Membership, x, p, q), // x₀ ∈ p₀ .. q₀ ⇔ p₀ ≤ x₀ ∧ x₀ ≤ q₀
					// x₀ ∈ m₀ .. n₀ ∩ p₀ .. q₀ ⇔ x₀ ∈ m₀ .. n₀ ∧ x₀ ∈ p₀ .. q₀
					At(inInter, v.Seg(m, n), v.Seg(p, q), x)))
		}),
})}

// Disjoint — two intervals miss each other exactly when one of the four
// cross comparisons between a lower bound and an upper bound fails.
//
// Being disjoint is having an empty overlap, `Inter` says what that
// overlap is, and `Empty` says when an interval is empty. What
// is left is bookkeeping about the crossed bounds: nat_max(m₀, p₀) is under
// nat_min(n₀, q₀) exactly when all four of m₀ ≤ n₀, m₀ ≤ q₀, p₀ ≤ n₀,
// p₀ ≤ q₀ hold, so the bounds cross exactly when one of the four fails —
// and a failed `≤` is the matching `<` the other way round.
var Disjoint = disjointThm{family.Add(registry.ProofEntry{
	Name: "Disjoint",
	Key:  "prop_e3964ae16ab95776",
	Build: family.Theorem("∀m n p q:num. disjoint(m .. n, p .. q) ⇔ n < m ∨ n < p ∨ q < m ∨ q < p",
		func(a *Argument, m, n, p, q Term) {
			v := ops(a.Ctx())
			lo, hi := v.Larger(m, p), v.Smaller(n, q) // the overlap's bounds

			// The two guards the overlap's nat_max and nat_min turn on, each in the
			// two failed-guard readings the file comment above `Inter`
			// explains. The upper pair's is read by both of the nat_min claims
			// below, so it is stated once.
			loFailed := a.Have(
				"m₀ failing to reach p₀ puts p₀ strictly below it",
				"¬(m₀ ≤ p₀) ⇔ p₀ < m₀",
				By(nat_order.NotLessEq))
			loWeaker := a.Have(
				"and p₀ strictly below m₀ is p₀ at or below m₀",
				"p₀ < m₀ ⇒ p₀ ≤ m₀",
				By(At(nat_order.LessEqOfLessThan, p, m)))
			hiFailed := a.Have(
				"n₀ failing to reach q₀ puts q₀ strictly below it",
				"¬(n₀ ≤ q₀) ⇔ q₀ < n₀",
				By(nat_order.NotLessEq))
			hiWeaker := a.Have(
				"and q₀ strictly below n₀ is q₀ at or below n₀",
				"q₀ < n₀ ⇒ q₀ ≤ n₀",
				By(At(nat_order.LessEqOfLessThan, q, n)))

			// ↦ m₀ .. n₀ ∩ p₀ .. q₀ = ∅ ⇔ … — being disjoint IS having an
			// empty intersection, by disjoint's defining equation.
			a.Do(Unfold(set_basic.DisjointDef))

			// Both are stated at these four bounds and each lemma is cited
			// bare: what each says here is one instance, and an instance
			// written out is matched against the law itself rather than
			// built by a witness tuple read against its ∀-prefix.
			shared := a.Have(
				"the intersection IS an interval — between the larger lower bound and the smaller upper one",
				"max(m, p) .. min(n, q) = (m .. n) ∩ (p .. q)",
				By(Inter))

			crossed := a.Have(
				"and that interval is empty exactly when its own bounds cross",
				"max(m, p) .. min(n, q) = ∅ ⇔ min(n, q) < max(m, p)",
				By(Empty))

			overlap := a.Have(
				"so the intersection is empty exactly when the two intervals' bounds cross",
				"(m .. n) ∩ (p .. q) = ∅ ⇔ min(n, q) < max(m, p)",
				By(Normalized, shared, crossed))

			bothLow := a.Have(
				"reaching max(m₀, p₀) is reaching both of them",
				"max(m₀, p₀) ≤ min(n₀, q₀) ⇔ m₀ ≤ min(n₀, q₀) ∧ p₀ ≤ min(n₀, q₀)",
				// ↦ COND(m₀ ≤ p₀, p₀, m₀) ≤ nat_min(n₀, q₀) ⇔ … — nat_max's
				// definition is all nat_order says about it.
				Unfold(nat_order.NatMaxDef),
				By(
					Normalized,
					At(nat_order.LessEqTrans, m, p, hi), // m₀ ≤ p₀ ∧ p₀ ≤ nat_min(n₀, q₀) ⇒ m₀ ≤ nat_min(n₀, q₀)
					At(nat_order.LessEqTrans, p, m, hi), // p₀ ≤ m₀ ∧ m₀ ≤ nat_min(n₀, q₀) ⇒ p₀ ≤ nat_min(n₀, q₀)
					loFailed,
					loWeaker))
			fromM := a.Have(
				"staying under min(n₀, q₀) is staying under both of them",
				"m₀ ≤ min(n₀, q₀) ⇔ m₀ ≤ n₀ ∧ m₀ ≤ q₀",
				// ↦ m₀ ≤ COND(n₀ ≤ q₀, n₀, q₀) ⇔ …
				Unfold(nat_order.NatMinDef),
				By(
					Normalized,
					At(nat_order.LessEqTrans, m, n, q), // m₀ ≤ n₀ ∧ n₀ ≤ q₀ ⇒ m₀ ≤ q₀
					At(nat_order.LessEqTrans, m, q, n), // m₀ ≤ q₀ ∧ q₀ ≤ n₀ ⇒ m₀ ≤ n₀
					hiFailed,
					hiWeaker))
			fromP := a.Have(
				"staying under min(n₀, q₀) is staying under both of them",
				"p₀ ≤ min(n₀, q₀) ⇔ p₀ ≤ n₀ ∧ p₀ ≤ q₀",
				Unfold(nat_order.NatMinDef),
				By(
					Normalized,
					At(nat_order.LessEqTrans, p, n, q), // p₀ ≤ n₀ ∧ n₀ ≤ q₀ ⇒ p₀ ≤ q₀
					At(nat_order.LessEqTrans, p, q, n), // p₀ ≤ q₀ ∧ q₀ ≤ n₀ ⇒ p₀ ≤ n₀
					hiFailed,
					hiWeaker))

			a.Show(
				"the bounds cross exactly when one of the four comparisons "+
					"fails, and each failure IS one of the four disjuncts",
				By(
					overlap,
					bothLow,
					fromM,
					fromP,
					// ¬(nat_max(m₀, p₀) ≤ nat_min(n₀, q₀)) ⇔ nat_min(n₀, q₀) < nat_max(m₀, p₀)
					At(nat_order.NotLessEq, lo, hi),
					At(nat_order.NotLessEq, m, n),  // ¬(m₀ ≤ n₀) ⇔ n₀ < m₀
					At(nat_order.NotLessEq, p, n),  // ¬(p₀ ≤ n₀) ⇔ n₀ < p₀
					At(nat_order.NotLessEq, m, q),  // ¬(m₀ ≤ q₀) ⇔ q₀ < m₀
					At(nat_order.NotLessEq, p, q))) // ¬(p₀ ≤ q₀) ⇔ q₀ < p₀
		}),
})}

// OffsetImage — shifting both bounds by p₀ shifts the interval: it is
// the image of the original under i ↦ i + p₀.
//
// One direction is cancellation — adding p₀ to both sides of m₀ ≤ i and
// i ≤ n₀ is what makes a shifted point land between the shifted bounds.
// The other has to produce the point it came from, and does so from the
// gap: x₀ stands some d₀ above m₀ + p₀, and the point that shifts to it
// is m₀ + d₀ — the same gap taken before the shift instead of after.
var OffsetImage = offsetImageThm{family.Add(registry.ProofEntry{
	Name: "OffsetImage",
	Key:  "prop_eee5df7c70273472",
	Build: family.Theorem("∀m n p:num. m + p .. n + p = image(λi:num. i + p, m .. n)",
		func(a *Argument, m, n, p Term) {
			v := ops(a.Ctx())
			shift := a.Ctx().TermText("λi:num. i + p₀") // the map i ↦ i + p₀
			// image's membership law carries two element types — a map need
			// not be an endofunction — and both are `num` here.
			inImage := set_basic.InImage.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())
			seg := v.Seg(m, n)
			lo, hi := v.Add(m, p), v.Add(n, p) // the shifted bounds
			x := samePoints(a, "∀x:num. x ∈ (m₀ + p₀) .. (n₀ + p₀) ⇔ x ∈ image(λi:num. i + p₀, m₀ .. n₀)")

			a.Iff()
			a.Forward(
				"a point between the shifted bounds is the shift of "+
					"one below: take the gap above m₀ + p₀ above m₀ instead",
				func(a *Argument, between Fact) { // between: x₀ ∈ (m₀ + p₀) .. (n₀ + p₀)
					bounds := a.Have(
						"x₀ lies between the shifted bounds",
						"m₀ + p₀ ≤ x₀ ∧ x₀ ≤ n₀ + p₀",
						By(between))

					d, gap := a.Obtain(
						"x₀ stands a gap d₀ above the lower bound",
						"∃d:num. x₀ = m₀ + p₀ + d",
						By(bounds, nat_order.LessEqExists))

					preShift := v.Add(m, d) // m₀ + d₀ — the same gap taken above m₀
					shifted := a.Have(
						"that gap may be taken before the shift rather than after it",
						"x₀ = m₀ + d₀ + p₀",
						By(
							gap,
							At(nat_arith.AddAssoc, m, p, d),  // m₀ + (p₀ + d₀) = m₀ + p₀ + d₀
							At(nat_arith.AddSym, p, d),       // p₀ + d₀ = d₀ + p₀
							At(nat_arith.AddAssoc, m, d, p))) // m₀ + (d₀ + p₀) = m₀ + d₀ + p₀

					a.Show(
						"m₀ + d₀ is a point of m₀ .. n₀: above m₀ by "+
							"construction, below n₀ because its shift is below n₀ + p₀",
						By(
							shifted,
							bounds,
							At(inImage, shift, seg, x),     // x₀ ∈ image(λi. i + p₀, m₀ .. n₀) ⇔ ∃i. x₀ = i + p₀ ∧ i ∈ m₀ .. n₀
							At(Membership, preShift, m, n), // m₀ + d₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ m₀ + d₀ ∧ m₀ + d₀ ≤ n₀
							At(nat_order.LessEqAdd, m, d),  // m₀ ≤ m₀ + d₀
							At(nat_order.LessEqAddRightCancel, preShift, n, p))) // m₀ + d₀ + p₀ ≤ n₀ + p₀ ⇔ m₀ + d₀ ≤ n₀
				})
			a.Backward(
				"a shifted point of m₀ .. n₀ lands between the shifted "+
					"bounds — the common p₀ cancels from each comparison",
				func(a *Argument, isShift Fact) { // isShift: x₀ ∈ image(λi. i + p₀, m₀ .. n₀)
					i, comesFrom := a.Obtain(
						"x₀ is i₀ + p₀ for some point i₀ of m₀ .. n₀",
						"∃i:num. x₀ = i + p₀ ∧ i ∈ m₀ .. n₀",
						By(isShift, inImage))
					a.Show(
						"m₀ ≤ i₀ and i₀ ≤ n₀ become m₀ + p₀ ≤ x₀ and x₀ ≤ n₀ + p₀",
						By(
							comesFrom,
							At(Membership, x, lo, hi), // x₀ ∈ (m₀ + p₀) .. (n₀ + p₀) ⇔ m₀ + p₀ ≤ x₀ ∧ x₀ ≤ n₀ + p₀
							At(Membership, i, m, n),   // i₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ i₀ ∧ i₀ ≤ n₀
							At(nat_order.LessEqAddRightCancel, m, i, p),  // m₀ + p₀ ≤ i₀ + p₀ ⇔ m₀ ≤ i₀
							At(nat_order.LessEqAddRightCancel, i, n, p))) // i₀ + p₀ ≤ n₀ + p₀ ⇔ i₀ ≤ n₀
				})
		}),
})}

// CombineRight — an interval cut just above p: the points that stop at
// p, and the points that start at p + 1.
//
// The cut itself is the whole content, and it is `≤`'s totality read
// through the duality with `<`: a point that does not stop at p has
// passed it, and passing p is reaching p + 1. The two pieces stay
// inside `m .. n` because the hypotheses put the cut inside it — the
// left piece ends at p, which n bounds, and the right piece starts at
// p + 1, which m does not exceed.
//
// Those hypotheses are the weakest that admit the degenerate cuts: at
// p + 1 = m the left piece is empty and at p = n the right one is, and
// both are still cuts.
//
// This is the primitive of the cut strand: `AddSplit` and `CombineLeft`
// below are this same cut named by a different point.
var CombineRight = combineRightThm{family.Add(registry.ProofEntry{
	Name: "CombineRight",
	Key:  "prop_217a2e6ff3464a2e",
	Build: family.Theorem(
		Statement{
			Binders: "∀m p n:num.",
			Hypotheses: []string{
				"m ≤ p + 1",
				"p ≤ n",
			},
			Conclusion: "m .. n = union(m .. p, p + 1 .. n)",
		},
		func(a *Argument, m, p, n Term, insideCut Fact) {
			v := ops(a.Ctx())
			inUnion := set_basic.InUnion.Inst[Nat]()
			up := v.Add(p, a.Ctx().Numeral(1)) // p₀ + 1, where the right piece starts
			x := samePoints(a, "∀x:num. x ∈ m₀ .. n₀ ⇔ x ∈ union(m₀ .. p₀, (p₀ + 1) .. n₀)")

			passing := a.Have(
				"passing p₀ is reaching p₀ + 1: the next point above p₀ is its successor",
				"p₀ < x₀ ⇔ p₀ + 1 ≤ x₀",
				By(
					At(nat_order.SucLessEqIffLessThan, p, x), // p₀ < x₀ ⇔ suc(p₀) ≤ x₀
					nat_arith.Add1))

			a.Show(
				"each point lands in the piece its side of the cut names, and "+
					"both pieces lie back inside — by p₀ ≤ n₀ and by m₀ ≤ p₀ + 1",
				By(
					insideCut,
					passing,
					At(nat_order.NotLessEq, x, p), // ¬(x₀ ≤ p₀) ⇔ p₀ < x₀
					At(Membership, x, m, n),       // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
					At(Membership, x, m, p),       // x₀ ∈ m₀ .. p₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ p₀
					At(Membership, x, up, n),      // x₀ ∈ (p₀ + 1) .. n₀ ⇔ p₀ + 1 ≤ x₀ ∧ x₀ ≤ n₀
					// x₀ ∈ m₀ .. p₀ ∪ (p₀ + 1) .. n₀ ⇔ x₀ ∈ m₀ .. p₀ ∨ x₀ ∈ (p₀ + 1) .. n₀
					At(inUnion, v.Seg(m, p), v.Seg(up, n), x),
					At(nat_order.LessEqTrans, x, p, n),   // x₀ ≤ p₀ ∧ p₀ ≤ n₀ ⇒ x₀ ≤ n₀
					At(nat_order.LessEqTrans, m, up, x))) // m₀ ≤ p₀ + 1 ∧ p₀ + 1 ≤ x₀ ⇒ m₀ ≤ x₀
		}),
})}

// AddSplit — extending an interval's upper bound by p splits it at the
// old bound: what was already there, and the p further points.
//
// The cut of `CombineRight` taken at n, where the second hypothesis
// costs nothing: the new bound n + p is above n whatever p is.
var AddSplit = addSplitThm{family.Add(registry.ProofEntry{
	Name: "AddSplit",
	Key:  "prop_fa4235646d403360",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p:num.",
			Hypotheses: []string{
				"m ≤ n + 1",
			},
			Conclusion: "m .. n + p = union(m .. n, n + 1 .. n + p)",
		},
		func(a *Argument, m, n, p Term, reachesCut Fact) {
			v := ops(a.Ctx())
			top := v.Add(n, p) // n₀ + p₀, the extended upper bound
			a.Show(
				"this is the cut at n₀ of the extended interval, "+
					"and extending is exactly what puts the cut inside it",
				By(
					reachesCut,
					// m₀ ≤ n₀ + 1 ∧ n₀ ≤ n₀ + p₀ ⇒ m₀ .. (n₀ + p₀) = union(m₀ .. n₀, (n₀ + 1) .. (n₀ + p₀))
					At(CombineRight, m, n, top),
					nat_order.LessEqAdd))
		}),
})}

// CombineLeft — the same cut named by where the SECOND piece starts
// rather than where the first one ends.
//
// Away from 0 that is a change of name only: p is the successor of
// p - 1, so this is `CombineRight` cut just above p - 1, and the
// hypothesis p ≤ n + 1 is p - 1 ≤ n with the common 1 still attached.
//
// At p = 0 it is not, because ℕ subtraction truncates and 0 has no
// predecessor: `m .. (p - 1)` is `0 .. 0` rather than an empty piece,
// and the identity holds for a different reason — the hypothesis
// m ≤ p forces m to be 0 as well, so the right piece is already the
// whole interval and the left one contributes its single point 0. That
// branch is discharged first, and the main line runs with p ≠ 0.
var CombineLeft = combineLeftThm{family.Add(registry.ProofEntry{
	Name: "CombineLeft",
	Key:  "prop_199f2cc92ab413f",
	Build: family.Theorem(
		Statement{
			Binders: "∀m p n:num.",
			Hypotheses: []string{
				"m ≤ p",
				"p ≤ n + 1",
			},
			Conclusion: "m .. n = union(m .. p - 1, p .. n)",
		},
		func(a *Argument, m Term, p *TermWrapper, n Term, insideCut Fact) {
			v := ops(a.Ctx())
			inUnion := set_basic.InUnion.Inst[Nat]()
			zero, one := a.Ctx().Numeral(0), a.Ctx().Numeral(1)
			pred := v.Sub(p, one) // p₀ - 1, where the left piece ends

			nonZero := a.Unless(
				p.Eq(zero),
				"p₀ = 0: the left piece is the single point 0 and the right one is already the whole interval",
				Given(func(a *Argument, isZero Fact) { // isZero: p₀ = 0
					atBottom := a.Have(
						"the interval starts at 0 too, since its lower bound is caught under p₀",
						"m₀ = 0",
						By(isZero, insideCut, At(nat_order.LessEqZeroClause, m))) // m₀ ≤ 0 ⇔ m₀ = 0

					// ↦ p₀ ≤ 1 — SubEqZero fires as a goal rewrite, so it is
					// cited bare: a difference vanishes exactly when the
					// subtrahend dominates, and at p₀ = 0 it does.
					truncated := a.Have(
						"and 0 - 1 truncates back to 0, so the left piece is 0 .. 0",
						"p₀ - 1 = 0",
						By(isZero, nat_monus.SubEqZero, At(nat_order.ZeroLessEq, one))) // 0 ≤ 1

					x := samePoints(a, "∀x:num. x ∈ m₀ .. n₀ ⇔ x ∈ union(m₀ .. (p₀ - 1), p₀ .. n₀)")
					a.Show(
						"both sides then say x₀ ≤ n₀: a lower bound of 0 constrains "+
							"nothing, and the left piece admits only 0, which n₀ bounds",
						By(
							isZero,
							atBottom,
							truncated,
							At(Membership, x, m, n),    // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
							At(Membership, x, m, pred), // x₀ ∈ m₀ .. (p₀ - 1) ⇔ m₀ ≤ x₀ ∧ x₀ ≤ p₀ - 1
							At(Membership, x, p, n),    // x₀ ∈ p₀ .. n₀ ⇔ p₀ ≤ x₀ ∧ x₀ ≤ n₀
							// x₀ ∈ m₀ .. (p₀ - 1) ∪ p₀ .. n₀ ⇔ x₀ ∈ m₀ .. (p₀ - 1) ∨ x₀ ∈ p₀ .. n₀
							At(inUnion, v.Seg(m, pred), v.Seg(p, n), x),
							At(nat_order.LessEqZeroClause, x), // x₀ ≤ 0 ⇔ x₀ = 0
							At(nat_order.ZeroLessEq, x),       // 0 ≤ x₀
							At(nat_order.ZeroLessEq, n)))      // 0 ≤ n₀
				}))

			succeeds := a.Have(
				"away from 0 the cut point has a predecessor, and p₀ - 1 is it",
				"p₀ - 1 + 1 = p₀",
				By(
					nonZero,
					At(nat_monus.SucOfSubOne, p), // p₀ ≠ 0 ⇒ suc(p₀ - 1) = p₀
					nat_arith.Add1))

			// `Normalized`: the instantiated cut still reads
			// `((p₀ - 1) + 1) .. n₀`, which `succeeds` rewrites to `p₀ .. n₀`.
			a.Show(
				"so this is the cut just above p₀ - 1, whose two "+
					"hypotheses are the two given here with that same 1 attached",
				By(
					Normalized,
					insideCut,
					succeeds,
					// m₀ ≤ (p₀ - 1) + 1 ∧ p₀ - 1 ≤ n₀ ⇒ m₀ .. n₀ = union(m₀ .. (p₀ - 1), ((p₀ - 1) + 1) .. n₀)
					At(CombineRight, m, pred, n),
					At(nat_order.LessEqAddRightCancel, pred, n, one))) // (p₀ - 1) + 1 ≤ n₀ + 1 ⇔ p₀ - 1 ≤ n₀
		}),
})}

// ---------------------------------------------------------------------------
// An interval cut by a bound
// ---------------------------------------------------------------------------
//
// an interval cut by a bound: keeping only the points of `m .. n` that
// stand on one side of a third number k leaves an interval again, whose
// bound on the cut side is k moved by one.
//
// These are the same kind of fact as the laws just above, one step
// further on: there both sides were intervals, here the left one is a
// set-builder. So the proofs are those proofs plus a single move — the
// set driver reads the builder as its own condition — and what is left
// over is again arithmetic on the bounds.
//
// Both turn on `<` against `≤` shifted by one, taken at the end being
// cut: below the cut it is `i < k ⇔ i ≤ k - 1`, above it `k < i ⇔
// k + 1 ≤ i`. The two are not mirror images, and the asymmetry is ℕ
// subtraction's alone — `k + 1` is a sum and needs nothing, while
// `k - 1` is a predecessor only where there is one to be had. That is
// the whole reason the first carries one guard more than the second.

// RestrictBelow — the points of `m .. n` strictly below k are the
// interval that ends one below k.
//
// The side that survives is the LOWER one: m stays the lower bound and
// the cut becomes the upper. Both guards are about the cut point.
// `1 ≤ k` is what makes `k - 1` the predecessor of k rather than
// monus's floor at 0: at k = 0 nothing stands below the cut, but the
// truncated `k - 1` is 0 again, so the right side is `m .. 0` — which
// holds the point 0 whenever m is 0 too. And `k ≤ n + 1` puts the cut
// inside the interval: past that the new upper bound would stand clear
// of n and the right side would admit points the original never had.
var RestrictBelow = restrictBelowThm{family.Add(registry.ProofEntry{
	Name: "RestrictBelow",
	Key:  "prop_4f603fc906d74900",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n k:num.",
			Hypotheses: []string{
				"1 ≤ k",
				"k ≤ n + 1",
			},
			Conclusion: "{i:num | i ∈ m .. n ∧ i < k} = m .. k - 1",
		},
		func(a *Argument, m, n, k Term, insideCut Fact) {
			v := ops(a.Ctx())
			one := a.Ctx().Numeral(1)
			pred := v.Sub(k, one) // k₀ - 1, the upper bound the cut leaves

			x := samePoints(a, "∀x:num. x ∈ {i:num | i ∈ m₀ .. n₀ ∧ i < k₀} ⇔ x ∈ m₀ .. (k₀ - 1)")
			member := reading(a, "x₀ ∈ {i:num | i ∈ m₀ .. n₀ ∧ i < k₀} ⇔ x₀ ∈ m₀ .. n₀ ∧ x₀ < k₀")

			predecessor := a.Have(
				"1 ≤ k₀ is exactly what makes k₀ - 1 a predecessor: putting the 1 back returns k₀",
				"k₀ - 1 + 1 = k₀",
				By(insideCut, At(nat_monus.SubAddCancel, k, one))) // 1 ≤ k₀ ⇒ k₀ - 1 + 1 = k₀

			cut := a.Have(
				"so standing strictly below k₀ is being bounded by that predecessor",
				"x₀ < k₀ ⇔ x₀ ≤ k₀ - 1",
				By(
					Normalized,
					predecessor,
					At(nat_order.LessThanSucIffLessEq, x, pred), // x₀ < suc(k₀ - 1) ⇔ x₀ ≤ k₀ - 1
					At(nat_arith.Add1, pred)))                   // suc(k₀ - 1) = k₀ - 1 + 1

			inside := a.Have(
				"and the second guard is that same predecessor caught under n₀, with the common 1 still attached",
				"k₀ - 1 ≤ n₀",
				By(
					Normalized,
					predecessor,
					insideCut,
					At(nat_order.LessEqAddRightCancel, pred, n, one))) // k₀ - 1 + 1 ≤ n₀ + 1 ⇔ k₀ - 1 ≤ n₀

			a.Show(
				"so the two upper bounds on x₀ collapse to one: n₀ is implied by "+
					"the tighter k₀ - 1 the cut imposes, and the lower bound is untouched",
				By(
					member,
					cut,
					inside,
					At(Membership, x, m, n),                // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
					At(Membership, x, m, pred),             // x₀ ∈ m₀ .. (k₀ - 1) ⇔ m₀ ≤ x₀ ∧ x₀ ≤ k₀ - 1
					At(nat_order.LessEqTrans, x, pred, n))) // x₀ ≤ k₀ - 1 ∧ k₀ - 1 ≤ n₀ ⇒ x₀ ≤ n₀
		}),
})}

// RestrictAbove — the points of `m .. n` strictly above k are the
// interval that starts one above k.
//
// The side that survives is the UPPER one: n stays the upper bound and
// the cut becomes the lower. One guard is enough, and it is the mirror
// of the second one above — `m ≤ k + 1` says the new lower bound does
// not fall below the old one, which is what puts the cut inside. There
// is nothing here answering to `1 ≤ k`: `k + 1` is a sum, so it is the
// successor of k wherever k stands.
var RestrictAbove = restrictAboveThm{family.Add(registry.ProofEntry{
	Name: "RestrictAbove",
	Key:  "prop_f7f3e92d47781539",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n k:num.",
			Hypotheses: []string{
				"m ≤ k + 1",
			},
			Conclusion: "{i:num | i ∈ m .. n ∧ k < i} = k + 1 .. n",
		},
		func(a *Argument, m, n, k Term, reachesCut Fact) {
			v := ops(a.Ctx())
			one := a.Ctx().Numeral(1)
			up := v.Add(k, one) // k₀ + 1, the lower bound the cut leaves

			x := samePoints(a, "∀x:num. x ∈ {i:num | i ∈ m₀ .. n₀ ∧ k₀ < i} ⇔ x ∈ (k₀ + 1) .. n₀")
			member := reading(a, "x₀ ∈ {i:num | i ∈ m₀ .. n₀ ∧ k₀ < i} ⇔ x₀ ∈ m₀ .. n₀ ∧ k₀ < x₀")

			cut := a.Have(
				"standing strictly above k₀ is reaching the next number up, and k₀ + 1 is it",
				"k₀ < x₀ ⇔ k₀ + 1 ≤ x₀",
				By(
					Normalized,
					At(nat_order.SucLessEqIffLessThan, k, x), // k₀ < x₀ ⇔ suc(k₀) ≤ x₀
					At(nat_arith.Add1, k)))                   // suc(k₀) = k₀ + 1

			a.Show(
				"so the two lower bounds on x₀ collapse to one: m₀ is implied by "+
					"the tighter k₀ + 1 the cut imposes, and the upper bound is untouched",
				By(
					reachesCut,
					member,
					cut,
					At(Membership, x, m, n),              // x₀ ∈ m₀ .. n₀ ⇔ m₀ ≤ x₀ ∧ x₀ ≤ n₀
					At(Membership, x, up, n),             // x₀ ∈ (k₀ + 1) .. n₀ ⇔ k₀ + 1 ≤ x₀ ∧ x₀ ≤ n₀
					At(nat_order.LessEqTrans, m, up, x))) // m₀ ≤ k₀ + 1 ∧ k₀ + 1 ≤ x₀ ⇒ m₀ ≤ x₀
		}),
})}

// ---------------------------------------------------------------------------
// The one-sided forms
// ---------------------------------------------------------------------------
//
// the one-sided forms: the numbers up to a bound, and the numbers strictly
// below one.
//
// `{x | x ≤ n}` and `{x | x < n}` are set-builders rather than
// intervals, which is why they are here and not with the interval shapes above — three of
// the five members below mention `..` nowhere at all.
//
// The method is the shape part's, split in two at the point. `samePoints`
// turns each set equation into a question about an arbitrary point;
// what that question comes to on each side falls into two kinds, and
// each kind has its own closer:
//
// - the SET side — membership in a builder, in `{0}`, in `∅`, in an
// insert — is plumbing, and the set driver settles it. `reading`
// below is that move, and together with `Membership` it is the
// whole of the chapter's use of the driver;
// - what is LEFT is one named fact about `≤` or `<`, read at the
// point.
//
// So every proof here is: bridge, read, cite. What distinguishes the
// members is the fact each ends at.
//
// The two `*Clauses` members end at the defining clause of their own
// order relation, and that is all they are: those clauses transcribed
// from points to sets. Raising the bound by one admits exactly one
// further number, so the builder gains exactly that one point.
//
// `Below` ends at `MembershipFromZero` — a lower bound of 0 constrains
// nothing, so the interval from 0 asks precisely the upper bound the
// builder asks. `BelowStrict` is the same identification for `<` and
// pays for the shift by one: away from 0 the bound `n` is the successor
// of `n - 1`, so being strictly below `n` is being bounded by `n - 1`.
// At `n = 0` there is no predecessor and the set is empty, which is
// `BelowStrictClauses`' first clause.
//
// The last places a set inside the strict side, with no bridge to
// cross: the numbers below a bound no larger (`BelowStrictMono`).
//
// The arbitrary point is called `y` throughout, because the builders
// have already bound `x`.

// Below — the numbers up to n are exactly the interval from 0 to n.
var Below = belowThm{family.Add(registry.ProofEntry{
	Name: "Below",
	Key:  "prop_3b0ac79c72ebedb5",
	Build: family.Theorem("∀n:num. {x:num | x ≤ n} = 0 .. n",
		func(a *Argument, n Term) {
			samePoints(a, "∀y:num. y ∈ {x:num | x ≤ n₀} ⇔ y ∈ 0 .. n₀")
			below := reading(a, "y₀ ∈ {x:num | x ≤ n₀} ⇔ y₀ ≤ n₀")

			a.Show(
				"and an interval starting at 0 imposes only that same upper bound",
				By(below, MembershipFromZero))
		}),
})}

// BelowStrict — the numbers strictly below n are the interval from 0 to
// n - 1, except that below 0 there is nothing at all.
//
// The conditional is not a case the statement could avoid: `n - 1`
// truncates, so at n = 0 the interval `0 .. (n - 1)` is `0 .. 0`, which
// holds the point 0 that no set of numbers below 0 may hold.
var BelowStrict = belowStrictThm{family.Add(registry.ProofEntry{
	Name: "BelowStrict",
	Key:  "prop_54c081ed3107cba7",
	// `∅⟨A:num⟩` because vocab.go's pin on the empty set does not reach a
	// COND branch; `A` there is empty_set's own type-variable name.
	Build: family.Theorem(
		"∀n:num. {x:num | x < n} = COND(n = 0, ∅⟨A:num⟩, 0 .. n - 1)",
		func(a *Argument, n *TermWrapper) {
			v := ops(a.Ctx())
			zero, one := a.Ctx().Numeral(0), a.Ctx().Numeral(1)
			pred := v.Sub(n, one) // n₀ - 1, the interval's upper bound away from 0

			nonZero := a.Unless(
				n.Eq(zero),
				"n₀ = 0: the conditional takes its empty branch, and nothing is below 0",
				Given(func(a *Argument, isZero Fact) { // isZero: n₀ = 0
					a.Show(
						"which is the zero clause of the strict form",
						By(Normalized, isZero, BelowStrictClauses))
				}))

			// The surviving branch still carries the conditional, so choosing
			// its arm is a step of its own.
			interval := a.Ctx().MakePropText("{x:num | x < n₀} = 0 .. n₀ - 1")
			a.Do(Suffices(interval, "and a failing guard sends the conditional to its interval arm",
				By(ResidentHyp(interval), nonZero)))

			top := a.Have(
				"away from 0 the bound is a successor, and n - 1 is what it succeeds",
				"suc(n - 1) = n",
				By(nonZero, At(nat_monus.SucOfSubOne, n))) // n₀ ≠ 0 ⇒ suc(n₀ - 1) = n₀

			y := samePoints(a, "∀y:num. y ∈ {x:num | x < n₀} ⇔ y ∈ 0 .. (n₀ - 1)")
			strictlyBelow := reading(a, "y₀ ∈ {x:num | x < n₀} ⇔ y₀ < n₀")

			a.Show(
				"so standing below n₀ is being bounded by its predecessor, which is what that interval says",
				By(
					strictlyBelow,
					top,
					At(nat_order.LessThanSucIffLessEq, y, pred), // y₀ < suc(n₀ - 1) ⇔ y₀ ≤ n₀ - 1
					MembershipFromZero))
		}),
})}

// BelowClauses — how the numbers up to a bound grow with the bound: at
// 0 only 0 is left, and each further bound contributes itself.
//
// This is `≤`'s own recursion, said about sets instead of about points.
// The two clauses are quantified separately because the first mentions
// no bound to quantify over.
var BelowClauses = belowClausesThm{family.Add(registry.ProofEntry{
	Name: "BelowClauses",
	Key:  "prop_853469774ecb37d8",
	Build: family.Theorem(
		"{x:num | x ≤ 0} = {0} ∧ (∀k:num. {x:num | x ≤ suc(k)} = insert(suc(k), {x:num | x ≤ k}))",
		func(a *Argument) {
			a.Do(SplitConj(
				Case(
					"at the bound 0 the only number left is 0 itself",
					Derive(func(a *Argument) {
						samePoints(a, "∀y:num. y ∈ {x:num | x ≤ 0} ⇔ y ∈ {0}")
						sides := reading(a, "(y₀ ∈ {x:num | x ≤ 0} ⇔ y₀ ≤ 0) ∧ (y₀ ∈ {0} ⇔ y₀ = 0)")

						a.Show(
							"and 0 bounds only itself — the zero clause of ≤",
							By(sides, nat_order.LessEqZeroClause))
					})),
				Case(
					"raising the bound to suc k₀ admits one further number, suc k₀ itself",
					Derive(func(a *Argument) {
						a.Fix()
						samePoints(a, "∀y:num. y ∈ {x:num | x ≤ suc(k₀)} ⇔ y ∈ insert(suc(k₀), {x:num | x ≤ k₀})")
						sides := reading(
							a,
							"(y₀ ∈ {x:num | x ≤ suc(k₀)} ⇔ y₀ ≤ suc(k₀)) ∧ (y₀ ∈ "+
								"insert(suc(k₀), {x:num | x ≤ k₀}) ⇔ y₀ = suc(k₀) ∨ y₀ ≤ k₀)")

						a.Show(
							"and admitting exactly that one further number is the successor clause of ≤",
							By(sides, nat_order.LessEqSucClause))
					})),
			))
		}),
})}

// BelowStrictClauses — the same recursion for the strict bound, and the
// two differences are the whole content: below 0 there is nothing, and
// the number a raised bound contributes is the OLD bound, since a bound
// never lies strictly below itself.
var BelowStrictClauses = belowStrictClausesThm{family.Add(registry.ProofEntry{
	Name: "BelowStrictClauses",
	Key:  "prop_7ed80366a2774865",
	Build: family.Theorem(
		"{x:num | x < 0} = ∅ ∧ (∀k:num. {x:num | x < suc(k)} = insert(k, {x:num | x < k}))",
		func(a *Argument) {
			a.Do(SplitConj(
				Case(
					"no number stands below 0",
					Derive(func(a *Argument) {
						samePoints(a, "∀y:num. y ∈ {x:num | x < 0} ⇔ y ∈ ∅")
						sides := reading(a, "(y₀ ∈ {x:num | x < 0} ⇔ y₀ < 0) ∧ y₀ ∉ ∅")

						a.Show(
							"and that is the zero clause of <",
							By(sides, nat_order.LessThanZeroClause))
					})),
				Case(
					"raising the bound to suc k₀ admits one further number, the old bound k₀",
					Derive(func(a *Argument) {
						k := a.Fix()
						y := samePoints(a, "∀y:num. y ∈ {x:num | x < suc(k₀)} ⇔ y ∈ insert(k₀, {x:num | x < k₀})")
						sides := reading(
							a,
							"(y₀ ∈ {x:num | x < suc(k₀)} ⇔ y₀ < suc(k₀)) ∧ (y₀ "+
								"∈ insert(k₀, {x:num | x < k₀}) ⇔ y₀ = k₀ ∨ y₀ < k₀)")

						a.Show(
							"and admitting exactly the old bound is the successor clause of <",
							By(sides, At(nat_order.LessThanSucClause, y, k))) // y₀ < suc(k₀) ⇔ y₀ < k₀ ∨ y₀ = k₀
					})),
			))
		}),
})}

// BelowStrictMono — the numbers below k lie below every m ≥ k.
var BelowStrictMono = belowStrictMonoThm{family.Add(registry.ProofEntry{
	Name: "BelowStrictMono",
	Key:  "prop_42a3c2d80c21210a",
	Build: family.Theorem(Statement{
		Binders: "∀k m:num.",
		Hypotheses: []string{
			"k ≤ m",
		},
		Conclusion: "{x:num | x < k} ⊆ {x:num | x < m}",
	}, func(a *Argument, k, m *Expr[Nat], order Fact) {
		below := a.Have(
			"a number below k lies below m",
			"∀y:num. y < k ⇒ y < m",
			ByArith(order))
		a.Show(
			"so the first set lies in the second",
			BySets(below))
	}),
})}

// ---------------------------------------------------------------------------
// Every interval is finite
// ---------------------------------------------------------------------------
//
// every interval is finite, and so is each set of numbers bounded on one
// side; and a set of numbers is finite exactly when some interval holds
// it.
//
// An interval is finite because of how it is BUILT. Start from the empty
// set and add one point at a time: `0 .. 0` is `{0}`, and each further
// bound contributes exactly its own successor, so `0 .. k` is reached
// from ∅ by k+1 insertions. That is `finite_set`'s two introduction
// rules — no counting, and no cardinality anywhere in this file.
// Whatever the lower bound, the interval sits inside the one that starts
// at 0 with the same top, and a subset of a finite set is finite; so the
// general statement needs no second induction and no case analysis of
// the degenerate intervals.
//
// The one-sided sets are then read off the identifications the one-sided part
// already made: `{x | x ≤ n}` IS `0 .. n`, and `{x | x < n}` IS
// `0 .. (n - 1)` except below 0, where it is empty.
//
// The next-to-last member turns all of that around into a
// characterisation: being finite IS being held by some interval. The
// last reads it at the whole of ℕ, which no interval holds: the numbers
// are not a finite set.
//
// Finiteness is a property of a SET, and so is the count the last part
// takes next. So wherever a member here or there identifies its set
// with another, that equation rewrites the goal rather than joining a
// premise list, and each such site carries only the goal it lands on.

// Finite — an interval holds finitely many numbers.
var Finite = finiteThm{family.Add(registry.ProofEntry{
	Name: "Finite",
	Key:  "prop_e1b3d42652183df5",
	Build: family.Theorem("∀m n:num. finite(m .. n)",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			zero := a.Ctx().Numeral(0)

			fromZero := a.Have(
				"an interval that starts at 0 is reached from ∅ one point at a time",
				"∀k:num. finite(0 .. k)",
				Derive(func(a *Argument) {
					k := a.Binder("k")
					a.Induct(k)
					a.Base(
						"at the bound 0 the interval is the single point 0",
						// Sing normalizes to the applied, pointwise form
						// `∀ẋ. (0 .. 0)(ẋ) ⇔ {0}(ẋ)` rather than to the set
						// equation it states, so this leaf stands one
						// extensionality fold away from its premises, and that
						// fold is what it spends a refute on.
						By(
							At(Sing, zero),                   // 0 .. 0 = {0}
							At(finite_set.FiniteSing, zero))) // finite({0})
					a.Step(
						"raising the bound lays suc k on top of an interval already finite",
						func(a *Argument, sofar Fact) { // finite(0 .. k)
							grow := a.Have(
								"0 is below every bound, so the higher interval really is the lower one with suc k added",
								"0 .. suc(k) = insert(suc(k), 0 .. k)",
								By(
									At(Rec, zero, k), // 0 ≤ suc(k) ⇒ 0 .. suc(k) = insert(suc(k), 0 .. k)
									nat_order.ZeroLessEq))
							// ↦ finite(insert(suc(k), 0 .. k))
							a.Do(grow.Rw())
							a.Show(
								"and laying one point on a finite set is finite's own second rule",
								// FiniteRules at (point, set) — its stated order.
								By(sofar, finite_set.FiniteRules.Inst[Nat]().At(v.Suc(k), v.Seg(zero, k))))
						})
				}))

			inside := a.Have(
				"and any interval sits inside the one that starts at 0 with the same top",
				"m₀ .. n₀ ⊆ 0 .. n₀",
				By(
					At(Subset, m, n, zero, n),   // m₀ .. n₀ ⊆ 0 .. n₀ ⇔ n₀ < m₀ ∨ n₀ ≤ n₀ ∧ 0 ≤ m₀
					At(nat_order.LessEqRefl, n), // n₀ ≤ n₀
					nat_order.ZeroLessEq))

			a.Show(
				"so it is a subset of a finite set",
				By(inside, fromZero.At(n), At(finite_set.FiniteSubset, v.Seg(m, n), v.Seg(zero, n))))
		}),
})}

// FiniteBelow — finitely many numbers stand at or below a bound.
var FiniteBelow = finiteBelowThm{family.Add(registry.ProofEntry{
	Name: "FiniteBelow",
	Key:  "prop_7e3749f63895674e",
	Build: family.Theorem("∀n:num. finite({x:num | x ≤ n})",
		func(a *Argument, n Term) {
			a.Show(
				"the numbers up to n₀ ARE the interval from 0 to n₀, and an interval is finite",
				// Below is cited bare because it fires as a rewrite of the
				// goal's set: ↦ finite(0 .. n₀).
				By(Below, Finite))
		}),
})}

// FiniteBelowStrict — and finitely many stand strictly below one.
//
// The strict form is an interval only away from 0. Below 0 there is
// nothing at all, and that branch is settled first so the predecessor
// `n - 1` never has to be reasoned about.
var FiniteBelowStrict = finiteBelowStrictThm{family.Add(registry.ProofEntry{
	Name: "FiniteBelowStrict",
	Key:  "prop_835653bcc990062f",
	Build: family.Theorem("∀n:num. finite({x:num | x < n})",
		func(a *Argument, n *TermWrapper) {
			zero := a.Ctx().Numeral(0)

			nonZero := a.Unless(
				n.Eq(zero),
				"n₀ = 0: no number stands below 0, so the set is empty",
				Given(func(a *Argument, isZero Fact) { // isZero: n₀ = 0
					noMembers := a.Have(
						"so the set has no members at all",
						"{x:num | x < n₀} = ∅",
						By(isZero, At(BelowStrict, n))) // {x | x < n₀} = COND(n₀ = 0, ∅, 0 .. n₀ - 1)
					a.Show(
						"and ∅ is finite outright — finite's first rule",
						// No witnesses: the rule used is the nullary one, finite(∅).
						By(noMembers, finite_set.FiniteRules.Inst[Nat]()))
				}))

			a.Show(
				"away from 0 the set IS the interval up to n₀'s predecessor, and an interval is finite",
				By(
					nonZero,
					At(BelowStrict, n), // {x | x < n₀} = COND(n₀ = 0, ∅, 0 .. n₀ - 1)
					Finite))
		}),
})}

// FiniteIffBounded — a set of numbers is finite exactly when some
// interval starting at 0 holds all of it.
//
// Backwards this is Finite plus the fact that finiteness descends to
// subsets. Forwards it is an induction over the finite set that carries
// a bound along: at each insertion the sum of the new point and the old
// bound is above both, so it bounds the enlarged set.
var FiniteIffBounded = finiteIffBoundedThm{family.Add(registry.ProofEntry{
	Name: "FiniteIffBounded",
	Key:  "prop_db88a2c6786239b",
	Build: family.Theorem("∀s:set(num). finite(s) ⇔ ∃n:num. s ⊆ 0 .. n",
		func(a *Argument, s Term) {
			v := ops(a.Ctx())
			zero := a.Ctx().Numeral(0)
			// The property the induction proves: "some interval from 0 holds
			// this set". Written once, here.
			isBounded := a.Ctx().TermText("λu:set(num). ∃n:num. u ⊆ 0 .. n")

			a.Iff()
			a.Forward(
				"a finite set is reached by insertions, and a bound can be carried along each one",
				func(a *Argument, isFinite Fact) { // finite(s₀)
					// The two clauses below are FiniteInduct's own, read at that
					// property and each stated one step short of it: `atEmpty`
					// names the witness 0 where the clause asks only for some n,
					// and `oneMore` takes the old bound as a ∀-parameter where the
					// clause has `∃n. u ⊆ 0 .. n` as its antecedent — the same
					// statement, since an antecedent's ∃ is a ∀ over the rest.
					atEmpty := a.Have(
						"∅ asks for no room at all — the shortest interval of all already holds it",
						"∅ ⊆ 0 .. 0",
						By(set_order.EmptySubset))

					oneMore := a.Have(
						"and a set that gains a point is still held, by the sum of that point and the old bound",
						"∀x:num. ∀u:set(num). ∀n:num. u ⊆ 0 .. n ⇒ ∃k:num. insert(x, u) ⊆ 0 .. k",
						Derive(func(a *Argument) {
							x, u, n := a.Fix(), a.Fix(), a.Fix()
							held := a.Assume() // u ⊆ 0 .. n
							top := v.Add(x, n)
							a.Take(top)

							// The next three claims ARE instances of the laws named,
							// so each cite closes at the claim and carries no
							// witnesses of its own.
							pointUnder := a.Have(
								"the new point is under the sum",
								"x₀ ≤ x₀ + n₀",
								Cite(nat_order.LessEqAdd))
							flipped := a.Have(
								"and the sum reads the same either way round",
								"x₀ + n₀ = n₀ + x₀",
								Cite(nat_arith.AddSym))
							oldUnder := a.Have(
								"so the old bound is under it as well",
								"n₀ ≤ x₀ + n₀",
								flipped.Rw(), // ↦ n₀ ≤ n₀ + x₀, which is that same growth law
								Cite(nat_order.LessEqAdd))

							widened := a.Have(
								"so the old interval sits inside the new one",
								"0 .. n₀ ⊆ 0 .. x₀ + n₀",
								By(
									oldUnder,
									At(Subset, zero, n, zero, top), // 0 .. n₀ ⊆ 0 .. (x₀ + n₀) ⇔ n₀ < 0 ∨ n₀ ≤ x₀ + n₀ ∧ 0 ≤ 0
									nat_order.ZeroLessEq))
							stillHeld := a.Have(
								"and with it everything the old bound held",
								"u₀ ⊆ 0 .. x₀ + n₀",
								By(held, widened, At(set_order.SubsetTrans, u, v.Seg(zero, n), v.Seg(zero, top))))
							pointHeld := a.Have(
								"the new point is held too, being under the bound",
								"x₀ ∈ 0 .. x₀ + n₀",
								By(pointUnder, MembershipFromZero))

							a.Show(
								"and holding an enlarged set is holding the point and holding the rest",
								By(stillHeld, pointHeld, set_order.InsertSubset.Inst[Nat]().At(u, v.Seg(zero, top), x)))
						}))

					a.Show(
						"and those are the two clauses finite induction asks for, so it carries the bound to s₀",
						By(isFinite, atEmpty, oneMore, finite_set.FiniteInduct.Inst[Nat]().At(isBounded)))
				})
			a.Backward(
				"whatever interval holds the set is finite, and finiteness descends to what it holds",
				func(a *Argument, someInterval Fact) { // ∃n. s₀ ⊆ 0 .. n
					n, held := a.Unpack(someInterval) // s₀ ⊆ 0 .. n
					a.Show(
						"so s₀ is a subset of a finite set",
						By(held, At(Finite, zero, n), At(finite_set.FiniteSubset, s, v.Seg(zero, n))))
				})
		}),
})}

// Infinite — the numbers themselves are not a finite set.
//
// The characterisation above, read at the whole of ℕ. Were the numbers
// finite, some interval 0 .. n would hold them all — suc n among them,
// which Membership puts at or below n. That is n < n, and no number is
// below itself.
var Infinite = infiniteThm{family.Add(registry.ProofEntry{
	Name: "Infinite",
	Key:  "prop_21e2b7e42cb778f",
	// `𝕌⟨A:num⟩` because the universe is nullary and takes its element
	// type from the annotation, as `∅⟨A:num⟩` does in BelowStrict.
	//
	// Neither deductive close runs a refutation: at each, the named
	// premises meet the goal by simplification.
	// The one refutation in the member is the set driver's, reading the
	// inclusion at a point.
	Build: family.Theorem("infinite(𝕌⟨A:num⟩)",
		func(a *Argument) {
			v := ops(a.Ctx())
			zero := a.Ctx().Numeral(0)
			numbers := a.Ctx().TermText("𝕌⟨A:num⟩") // the set of all numbers

			a.Do(Unfold(finite_set.InfiniteDef)) // ↦ ¬finite(𝕌)
			isFinite := a.SupposeNot()

			n, held := a.Obtain(
				"a finite set of numbers is held by some interval from 0",
				"∃n:num. 𝕌⟨A:num⟩ ⊆ 0 .. n",
				By(Normalized, isFinite, At(FiniteIffBounded, numbers))) // finite(𝕌) ⇔ ∃n. 𝕌 ⊆ 0 .. n
			next := v.Suc(n)

			above := a.Have(
				"so suc n₀, a number like any other, lies in that interval",
				"suc(n₀) ∈ 0 .. n₀",
				BySets(held))

			a.Show(
				"which puts suc n₀ at or below n₀ — that is n₀ < n₀, and no number is below itself",
				By(
					above,
					At(Membership, next, zero, n),            // suc(n₀) ∈ 0 .. n₀ ⇔ 0 ≤ suc(n₀) ∧ suc(n₀) ≤ n₀
					At(nat_order.SucLessEqIffLessThan, n, n), // n₀ < n₀ ⇔ suc(n₀) ≤ n₀
					At(nat_order.LessThanIrrefl, n)))         // ¬(n₀ < n₀)
		}),
})}

// ---------------------------------------------------------------------------
// How many numbers an interval holds
// ---------------------------------------------------------------------------
//
// The count is settled by list_length, not by bounds. An interval only ever
// grows in one direction: fix the lower bound and let the upper one run
// up from it, and each further step contributes exactly one new number,
// its own top. So the primitive here is the count of `m .. (m + d)`,
// which is `d + 1` — one induction on `d`, with `m` a spectator that
// never has to be reasoned about, and no degenerate interval anywhere in
// the argument, since `m .. (m + d)` is never empty.
//
// The familiar form in terms of the two bounds is then a corollary, and
// its content is entirely the empty case: where the bounds cross there
// is nothing to count and truncated subtraction sends the width to 0
// too, and where they do not, writing the upper bound as `m + d` reduces
// it to the primitive. Counting from 1 is that corollary read at the one
// bound where the width is the upper bound itself, and the numbers of
// 1 .. n whose double exceeds n are counted by it too, once they are seen
// to be the interval from ⌊n/2⌋ + 1 to n.
//
// Having a SIZE adds nothing to any of that: it is defined as being
// finite and counting that much, so each of the four size members opens
// the definition and reads off the finiteness and the count already
// proved. The two one-sided forms identify their set with an interval
// first, and then say what an interval from 0 holds — its top, plus one
// — which needs no subtraction at all, so the width form never enters
// them.
//
// The last member turns counting around into a characterisation, and it
// is the only place in the chapter where the points being counted are
// not numbers: a set of anything is finite exactly when an interval
// indexes it.
//
// This is the first file in the chapter to mention a count at all: the
// members above it — membership, shape, and finiteness — reach no
// cardinality row.

// counting is the counting rule — the empty set counts nothing, and
// laying a point on a finite set raises its count by one unless the
// point was already there — pinned at the type an interval's points
// have.
//
// It is stated over an arbitrary element type and read here at num —
// the wrapper's explicit instance, like every other row this chapter
// has to pin. Witnesses go in the entry's own STATED order — (point,
// set), the order its binders read; every call below passes (point,
// set).
func counting() Fact {
	return cardinality.CardClauses.Inst[Nat]()
}

// countsNothing is the counting rule's nullary half, read as a fact —
// so the cite is bare, there being no instance to ask for. Both
// degenerate cases below meet it once their goal's set has been
// rewritten to ∅: an interval whose bounds cross, and the numbers
// strictly below 0.
func countsNothing(a *Argument) Fact {
	return a.Have(
		"and the empty set counts nothing",
		"card(∅) = 0",
		By(counting()))
}

// CardOfLength — an interval counts its length, plus the point it starts
// from.
//
// Induction on the length. At length 0 the interval is one point, and a
// point counts one because laying it on the empty set is the counting
// rule's own step. Each further step adds the successor of the old top,
// which was not in the interval before — nothing above the old top is —
// so the count goes up by exactly one.
var CardOfLength = cardOfLengthThm{family.Add(registry.ProofEntry{
	Name: "CardOfLength",
	Key:  "prop_2b1cf1eba59a770f",
	Build: family.Theorem("∀m d:num. card(m .. m + d) = d + 1",
		func(a *Argument, m, d Term) {
			v := ops(a.Ctx())

			a.Induct(d)
			a.Base(
				"length 0: the interval is the single point m₀, and a point counts one",
				func(a *Argument) {
					countsOne := a.Have(
						"laying m₀ on the empty set raises the empty count to one",
						"card({m₀}) = 1",
						By(
							Normalized,
							// card({m₀}) = suc(card(∅)) once the membership test below fails, and card(∅) = 0
							At(counting(), m, v.EmptySet),
							finite_set.FiniteRules.Inst[Nat](), // finite(∅) — the rule's hypothesis
							At(set_basic.NotInEmpty, m),        // m₀ ∉ ∅ — that test
							nat_arith.OneIsSucZero))            // 1 = suc(0)
					a.Show(
						"and an interval of length 0 IS that point",
						By(
							countsOne,
							nat_arith.AddZero,            // ↦ card(m₀ .. m₀) = 0 + 1
							At(Sing, m),                  // m₀ .. m₀ = {m₀}
							nat_arith.AddLeftZeroClause)) // ↦ 1
				})
			a.Step(
				"length d₀ → suc d₀: one more step lays one new point on an interval already counted",
				func(a *Argument, counted Fact) { // counted: card(m₀ .. (m₀ + d₀)) = d₀ + 1
					oldTop := v.Add(m, d)   // m₀ + d₀ — where the counted interval ends
					newTop := v.Suc(oldTop) // suc(m₀ + d₀) — the point the longer one adds
					countedSeg := v.Seg(m, oldTop)

					grow := a.Have(
						"the longer interval is the counted one with suc(m₀ + d₀) laid on top",
						"m₀ .. suc(m₀ + d₀) = insert(suc(m₀ + d₀), m₀ .. m₀ + d₀)",
						By(
							// m₀ ≤ suc(m₀ + d₀) ⇒ m₀ .. suc(m₀ + d₀) = insert(suc(m₀ + d₀), m₀ .. (m₀ + d₀))
							At(Rec, m, oldTop),
							At(nat_order.LessEqSucClause, m, oldTop), // m₀ ≤ suc(m₀ + d₀) ⇔ m₀ ≤ m₀ + d₀ ∨ m₀ = suc(m₀ + d₀)
							nat_order.LessEqAdd))                     // the left disjunct, so the guard is free

					fresh := a.Have(
						"and that point was not there before: nothing above the old top is",
						"suc(m₀ + d₀) ∉ m₀ .. m₀ + d₀",
						By(
							// suc(m₀ + d₀) ∈ m₀ .. (m₀ + d₀) ⇔ m₀ ≤ suc(m₀ + d₀) ∧ suc(m₀ + d₀) ≤ m₀ + d₀
							At(Membership, newTop, m, oldTop),
							At(nat_order.SucLessEqIffLessThan, oldTop, oldTop), // m₀ + d₀ < m₀ + d₀ ⇔ suc(m₀ + d₀) ≤ m₀ + d₀
							nat_order.LessThanIrrefl))                          // so the upper condition fails

					a.Show(
						"so the count goes up by exactly one, and so does the length",
						By(
							counted,
							grow,
							fresh,
							At(Finite, m, oldTop), // finite(m₀ .. (m₀ + d₀)) — the rule's hypothesis
							// card(insert(suc(m₀ + d₀), m₀ .. (m₀ + d₀))) = suc(card(m₀ .. (m₀ + d₀))) once `fresh` fails the membership test
							At(counting(), newTop, countedSeg),
							nat_arith.AddClauses)) // m₀ + suc(d₀) = suc(m₀ + d₀), and suc(d₀) + 1 = suc(d₀ + 1)
				})
		}),
})}

// Card — the count read off the two bounds.
//
// Where the bounds cross the interval is empty, and truncated
// subtraction sends the width to 0 with it. Where they do not, the upper
// bound is the lower one shifted by some length, and CardOfLength counts
// that shift; the same shift is what the width comes to, since adding
// the lower bound back to it recovers the upper bound plus one.
var Card = cardThm{family.Add(registry.ProofEntry{
	Name: "Card",
	Key:  "prop_1f0293c847925e40",
	Build: family.Theorem("∀m n:num. card(m .. n) = n + 1 - m",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			one := a.Ctx().Numeral(1)
			top := v.Add(n, one)   // n₀ + 1 — the far end of the width
			width := v.Sub(top, m) // (n₀ + 1) - m₀ — the count the statement claims

			reached := a.Unless(
				v.Under(n, m),
				"n₀ < m₀: the bounds cross, so there is nothing to count and nothing left to subtract",
				Given(func(a *Argument, crossed Fact) { // crossed: n₀ < m₀
					vacant := a.Have(
						"crossed bounds admit no point at all",
						"m₀ .. n₀ = ∅",
						By(crossed, Empty))
					// ↦ card(∅) = (n₀ + 1) - m₀
					a.Do(vacant.Rw())
					nothing := countsNothing(a)
					a.Show(
						"while n₀ + 1 ≤ m₀ leaves nothing to subtract either, so both sides are 0",
						By(
							crossed,
							nothing,
							At(nat_monus.SubEqZero, top, m),          // (n₀ + 1) - m₀ = 0 ⇔ n₀ + 1 ≤ m₀
							At(nat_order.SucLessEqIffLessThan, n, m), // n₀ < m₀ ⇔ suc(n₀) ≤ m₀
							nat_arith.Add1))
				}))

			span := a.Have(
				"otherwise m₀ reaches n₀, so n₀ is m₀ shifted by some length",
				"∃d:num. n₀ = m₀ + d",
				By(
					reached,
					At(nat_order.NotLessThan, n, m), // ¬(n₀ < m₀) ⇔ m₀ ≤ n₀
					nat_order.LessEqExists))
			d, shifted := a.Unpack(span) // shifted: n₀ = m₀ + d₀

			isLength := a.Have(
				"adding m₀ back to the width recovers n₀ + 1, which "+
					"is m₀ + (d₀ + 1); cancelling m₀ leaves the shift",
				"n₀ + 1 - m₀ = d₀ + 1",
				By(
					shifted,
					At(nat_monus.SubAddCancel, top, m), // m₀ ≤ n₀ + 1 ⇒ ((n₀ + 1) - m₀) + m₀ = n₀ + 1
					At(nat_order.LessEqAdd, m, v.Add(d, one)),            // m₀ ≤ m₀ + (d₀ + 1) — that guard, regrouped
					At(nat_arith.AddAssoc, m, d, one),                    // m₀ + (d₀ + 1) = m₀ + d₀ + 1
					At(nat_arith.AddSym, width, m),                       // ((n₀ + 1) - m₀) + m₀ = m₀ + ((n₀ + 1) - m₀)
					At(nat_arith.AddEqLCancel, m, width, v.Add(d, one)))) // m₀ + x = m₀ + (d₀ + 1) ⇔ x = d₀ + 1

			a.Show(
				"and an interval of that shift counts the shift, plus its own lower bound",
				By(Normalized, shifted, isLength, At(CardOfLength, m, d))) // card(m₀ .. (m₀ + d₀)) = d₀ + 1
		}),
})}

// CardFromOne — counting from 1, an interval's count is its upper bound.
//
// Card read at the lower bound 1, where the width collapses: taking one
// away from n + 1 gives back n.
var CardFromOne = cardFromOneThm{family.Add(registry.ProofEntry{
	Name: "CardFromOne",
	Key:  "prop_a92ce0971e59a9f8",
	Build: family.Theorem("∀n:num. card(1 .. n) = n",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			one := a.Ctx().Numeral(1)
			width := v.Sub(v.Add(n, one), one) // (n₀ + 1) - 1 — the width Card gives at the lower bound 1

			// The claims below are instances of the laws named, so each cite
			// closes at the claim and carries no witnesses of its own.
			flipped := a.Have(
				"the upper bound reads the same either way round",
				"n₀ + 1 = 1 + n₀",
				Cite(nat_arith.AddSym))
			reaches := a.Have(
				"so there is a 1 to take away in the first place",
				"1 ≤ n₀ + 1",
				flipped.Rw(), // ↦ 1 ≤ 1 + n₀, which is that same growth law
				Cite(nat_order.LessEqAdd))

			collapses := a.Have(
				"putting the 1 back recovers n₀ + 1, and cancelling it leaves n₀",
				"n₀ + 1 - 1 = n₀",
				By(
					reaches,
					flipped,
					At(nat_monus.SubAddCancel, v.Add(n, one), one), // 1 ≤ n₀ + 1 ⇒ ((n₀ + 1) - 1) + 1 = n₀ + 1
					At(nat_arith.AddSym, width, one),               // ((n₀ + 1) - 1) + 1 = 1 + ((n₀ + 1) - 1)
					At(nat_arith.AddEqLCancel, one, width, n)))     // 1 + x = 1 + n₀ ⇔ x = n₀

			a.Show(
				"so the count read off the bounds is the upper bound itself",
				By(collapses, Card))
		}),
})}

// UpperHalfCount — of the numbers 1, …, n, those whose double exceeds n
// number n − ⌊n/2⌋: they are ⌊n/2⌋ + 1, …, n.
var UpperHalfCount = upperHalfCountThm{family.Add(registry.ProofEntry{
	Name: "UpperHalfCount",
	Key:  "prop_81c87da8f48be6ab",
	Build: family.Theorem("∀n:num. card({k:num | 1 ≤ k ∧ k ≤ n ∧ n < 2 * k}) = n - div(n, 2)",
		func(arg *Argument, n *Expr[Nat]) {
			upper := arg.TermAs[Nat]("div(n, 2) + 1")
			halves := arg.Have(
				"n is twice ⌊n/2⌋ plus a remainder below 2",
				"n = div(n, 2) * 2 + rem(n, 2) ∧ rem(n, 2) < 2",
				By(nat_div_mod.Division.At(n, arg.TermAs[Nat]("2"))))
			pointwise := arg.Have(
				"2k exceeds n exactly when k exceeds ⌊n/2⌋",
				"∀k:num. 1 ≤ k ∧ k ≤ n ∧ n < 2 * k ⇔ k ∈ div(n, 2) + 1 .. n",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					b.Show(
						"reading the interval's membership as bounds",
						Simp(Fwd(Membership)),
						ByArith(halves))
				}))
			interval := arg.Have(
				"so the set is the interval ⌊n/2⌋ + 1 .. n",
				"{k:num | 1 ≤ k ∧ k ≤ n ∧ n < 2 * k} = div(n, 2) + 1 .. n",
				BySets(pointwise))
			arg.Show(
				"which has n − ⌊n/2⌋ members",
				interval.Rw(),
				ByArith(Card.At(upper, n)))
		}),
})}

// HasSize — an interval's size is the width between its bounds.
var HasSize = hasSizeThm{family.Add(registry.ProofEntry{
	Name: "HasSize",
	Key:  "prop_904535e123cc8ce8",
	Build: family.Theorem("∀m n:num. has_size(m .. n, n + 1 - m)",
		func(a *Argument, m, n Term) {
			// ↦ finite(m₀ .. n₀) ∧ card(m₀ .. n₀) = (n₀ + 1) - m₀
			a.Do(Unfold(cardinality.HasSizeDef))

			a.Show(
				"an interval is finite, and its count is that width",
				// Finite is cited bare: it discharges its own conjunct where
				// it stands, rather than arriving as a premise.
				By(Finite, Card))
		}),
})}

// HasSizeFromOne — counting from 1, an interval's size is its upper
// bound.
var HasSizeFromOne = hasSizeFromOneThm{family.Add(registry.ProofEntry{
	Name: "HasSizeFromOne",
	Key:  "prop_f516365a85c7acb6",
	Build: family.Theorem("∀n:num. has_size(1 .. n, n)",
		func(a *Argument, n Term) {
			// ↦ finite(1 .. n₀) ∧ card(1 .. n₀) = n₀
			a.Do(Unfold(cardinality.HasSizeDef))

			a.Show(
				"an interval is finite, and from 1 its count is its upper bound",
				By(Finite, CardFromOne))
		}),
})}

// HasSizeBelow — there are n + 1 numbers at or below n.
//
// They are the interval that starts at 0 and reaches n, so their number
// is what any interval of that length holds: the length, plus the point
// it starts from. Nothing is subtracted anywhere — a lower bound of 0
// takes nothing away.
var HasSizeBelow = hasSizeBelowThm{family.Add(registry.ProofEntry{
	Name: "HasSizeBelow",
	Key:  "prop_16d92f1f4e19641c",
	Build: family.Theorem("∀n:num. has_size({x:num | x ≤ n}, n + 1)",
		func(a *Argument, n Term) {
			zero := a.Ctx().Numeral(0)

			// ↦ finite({x | x ≤ n₀}) ∧ card({x | x ≤ n₀}) = n₀ + 1
			a.Do(Unfold(cardinality.HasSizeDef))

			interval := a.Have(
				"the numbers up to n₀ ARE the interval from 0 that reaches n₀",
				"{x:num | x ≤ n₀} = 0 .. n₀",
				Cite(Below))
			// ↦ finite(0 .. n₀) ∧ card(0 .. n₀) = n₀ + 1
			a.Do(interval.Rw())

			a.Show(
				"and an interval is finite, and one that starts at 0 is exactly n₀ long",
				By(
					Finite,
					At(CardOfLength, zero, n),    // card(0 .. (0 + n₀)) = n₀ + 1
					nat_arith.AddLeftZeroClause)) // so that interval is this one
		}),
})}

// HasSizeBelowStrict — there are n numbers strictly below n.
//
// Standing strictly below n is standing at or below n's predecessor, so
// this is the interval up to that predecessor — except below 0, where
// there is no predecessor and no number either. That case is settled
// first, and afterwards `n - 1` is only ever met under a hypothesis
// saying it succeeds.
var HasSizeBelowStrict = hasSizeBelowStrictThm{family.Add(registry.ProofEntry{
	Name: "HasSizeBelowStrict",
	Key:  "prop_d5bdde917d8cadfa",
	Build: family.Theorem("∀n:num. has_size({x:num | x < n}, n)",
		func(a *Argument, n *TermWrapper) {
			v := ops(a.Ctx())
			zero, one := a.Ctx().Numeral(0), a.Ctx().Numeral(1)
			pred := v.Sub(n, one) // n₀ - 1 — the interval's top, away from 0

			// ↦ finite({x | x < n₀}) ∧ card({x | x < n₀}) = n₀
			a.Do(Unfold(cardinality.HasSizeDef))

			a.Do(SplitConj(
				Case(
					"finite: the numbers below a bound are finite whatever the bound is",
					Cite(FiniteBelowStrict)),

				Case(
					"count: and there are n₀ of them",
					Derive(func(a *Argument) {
						nonZero := a.Unless(
							n.Eq(zero),
							"n₀ = 0: no number stands below 0, and an empty set counts nothing",
							Given(func(a *Argument, isZero Fact) { // isZero: n₀ = 0
								vacant := a.Have(
									"so the set has no members at all",
									"{x:num | x < n₀} = ∅",
									By(isZero, At(BelowStrict, n))) // {x | x < n₀} = COND(n₀ = 0, ∅, 0 .. n₀ - 1)
								// ↦ card(∅) = n₀
								a.Do(vacant.Rw())
								nothing := countsNothing(a)
								a.Show(
									"which at this bound is n₀ itself",
									By(Normalized, isZero, nothing))
							}))

						interval := a.Have(
							"away from 0 the set IS the interval up to n₀'s predecessor",
							"{x:num | x < n₀} = 0 .. n₀ - 1",
							By(nonZero, At(BelowStrict, n))) // a failing guard sends the conditional to its interval arm
						// ↦ card(0 .. (n₀ - 1)) = n₀
						a.Do(interval.Rw())

						a.Show(
							"that interval starts at 0 and reaches n₀'s predecessor, so it holds one more than that",
							By(
								nonZero,
								At(CardOfLength, zero, pred),          // card(0 .. (0 + (n₀ - 1))) = (n₀ - 1) + 1
								At(nat_arith.AddLeftZeroClause, pred), // 0 + (n₀ - 1) = n₀ - 1, so that interval is the one above
								At(nat_monus.SucOfSubOne, n),          // n₀ ≠ 0 ⇒ suc(n₀ - 1) = n₀
								nat_arith.Add1))                       // so one more than the length is n₀
					})),
			))
		}),
})}

// BelowStrictInjectiveOnto — a map of the numbers below k into
// themselves that never repeats a value misses none of them.
//
// This is the pigeonhole principle read the other way round, at the one
// finite set a counting argument over a family most often runs on. The
// range is finite, p maps it into itself, and for a self-map of a finite
// set being one-to-one and being onto are the same property
// (`cardinality.SurjectiveIffInjective`); what is left is reading the
// range's set-builder as the bound it spells.
var BelowStrictInjectiveOnto = belowStrictInjectiveOntoThm{family.Add(registry.ProofEntry{
	Name: "BelowStrictInjectiveOnto",
	Key:  "prop_7be7aee89183bfcb",
	Build: family.Theorem(Statement{
		Binders: "∀k:num. ∀p:(num → num). ∀j:num.",
		Hypotheses: []string{
			"∀i:num. i < k ⇒ p(i) < k",
			"∀i i':num. i < k ∧ i' < k ∧ p(i) = p(i') ⇒ i = i'",
			"j < k",
		},
		Conclusion: "∃i:num. i < k ∧ p(i) = j",
	},
		func(a *Argument, k *Expr[Nat], p *Arrow[Nat, Nat], into, injective Fact) {
			finite := a.Have(
				"the range is finite",
				"finite({i:num | i < k})",
				By(FiniteBelowStrict))
			// An element of the image is p's value at a point of the range,
			// which the first hypothesis keeps inside it. Go's Simp does not
			// adapt a rule's type letters, so the image law is instantiated
			// at ℕ where it is used.
			mapsInto := a.Have(
				"p maps the range into itself",
				"image(p, {i:num | i < k}) ⊆ {i:num | i < k}",
				Unfold(set_basic.SubsetDef),
				Simp(Fwd(set_image.ForallInImage.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]()))),
				BySets(into))
			injectiveOn := a.Have(
				"and never repeats a value there",
				"injective_on({i:num | i < k}, p)",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]()))),
				BySets(injective))
			ontoIffInjective := a.Have(
				"for a self-map of a finite set, onto and one-to-one are the same",
				"(∀y:num. y ∈ {i:num | i < k} ⇒ ∃x:num. x ∈ {i:num | i < k} ∧ p(x) = y) ⇔ "+
					"injective_on({i:num | i < k}, p)",
				By(finite, mapsInto, cardinality.SurjectiveIffInjective))
			onto := a.Have(
				"so p is onto the range",
				"∀y:num. y ∈ {i:num | i < k} ⇒ ∃x:num. x ∈ {i:num | i < k} ∧ p(x) = y",
				ontoIffInjective.Rw(),
				By(injectiveOn))
			a.Show(
				"which, read through the set-builder, is the claim",
				BySets(onto))
		}),
})}

// IncreasingSelfMapIsIdentity — a map f of the points below n into
// themselves that climbs at every step, f(i) < f(i + 1), fixes each of them.
// Climbing d steps from i, f rises by at least d. Climbing from i to n − 1,
// f stays below n, so f(i) is at most i; climbing from 0 to i, f(i) is at
// least i.
var IncreasingSelfMapIsIdentity = increasingSelfMapIsIdentityThm{family.Add(registry.ProofEntry{
	Name: "IncreasingSelfMapIsIdentity",
	Key:  "prop_a9fd2513c58f019f",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀f:(num → num). ∀i:num.",
		Hypotheses: []string{
			"∀j:num. j < n ⇒ f(j) < n",
			"∀j:num. suc(j) < n ⇒ f(j) < f(suc(j))",
			"i < n",
		},
		Conclusion: "f(i) = i",
	}, func(a *Argument, n *Expr[Nat], f *Arrow[Nat, Nat], h Fact) {
		given := a.Conjuncts(
			h,
			"f keeps the points below n below n",
			"f climbs at every step below n")
		into, climbs := given[0], given[1]
		rises := a.Have(
			"climbing d steps from i, f rises by at least d",
			"∀d i:num. i + d < n ⇒ f(i) + d ≤ f(i + d)",
			Derive(func(b *Argument) {
				d := b.FixAs[Nat]("d")
				b.FixAs[Nat]("i")
				b.Induct(d)
				b.Base(
					"over no step there is nothing to rise",
					ByArith())
				b.Step(
					"one more step rises once more",
					func(c *Argument, risen Fact) {
						c.Show(
							"f(i + d) < f(i + d + 1)",
							Simp(Fwd(nat_arith.AddSuc)),
							ByArith(climbs.At(c.TermAs[Nat]("i + d")), risen))
					})
			}))
		i := a.FixAs[Nat]("i")
		inside := a.Assume()
		d, gap := a.ObtainAs[Nat](
			"i lies below n, so n is i + d + 1 for some d",
			"∃d:num. n = i + suc(d)",
			By(inside, nat_order.LessThanExists.At(n, i)))
		atMost := a.Have(
			"climbing d steps from i stays below n, so f(i) is at most i",
			"f(i) ≤ i",
			ByArith(rises.At(d, i), into.At(a.TermAs[Nat]("i + d")), gap))
		atLeast := a.Have(
			"climbing i steps from 0, f(i) is at least i",
			"i ≤ f(i)",
			ByArith(rises.At(i, a.Ctx().Nat(0)), inside))
		a.Show(
			"so f(i) = i",
			ByArith(atMost, atLeast))
	}),
})}

// FiniteIndex — a set is finite exactly when an interval indexes it:
// when some map runs `1 .. card(s)` over the whole of s without ever
// repeating a point.
//
// Backwards this needs no counting at all: an interval is finite, and
// the image of a finite set is finite, so anything an interval covers
// is finite whatever the map does.
//
// Forwards, the interval `1 .. card(s)` is chosen because it holds
// exactly as many points as s does, and two finite sets of equal count
// can be matched point for point — a map each way, each undoing the
// other. The map FROM the interval is the indexing: it never repeats,
// since two indices with the same point are carried back to the same
// index; and it misses nothing, since every point is the point at its
// own rank.
//
// This is the chapter's one member whose set is not a set of numbers.
// The interval is still at `num` — it is doing the indexing — but what
// it indexes is arbitrary, so the element type here is a variable where
// everywhere else in the chapter it is `num`.
var FiniteIndex = finiteIndexThm{family.Add(registry.ProofEntry{
	Name: "FiniteIndex",
	Key:  "prop_3ca519e3b8682e30",
	Build: family.Theorem(
		"∀s:set(A). finite(s) ⇔ ∃f:(num → A). injective_on(1 .. card(s), f) ∧ s = image(f, 1 .. card(s))",
		func(a *Argument, s Term) {
			v := ops(a.Ctx())
			one := a.Ctx().Numeral(1)
			// `card` is declared at `num` in vocab.go and this member's set
			// is at `A`, so the chapter's own operator table cannot build
			// this count.
			count := a.Ctx().TermText("card(s₀)")
			seg := v.Seg(one, count) // 1 .. card(s₀) — the indexing interval

			a.Iff()
			a.Forward(
				"the interval that counts s₀ can be matched with it, and the map back is the indexing",
				func(a *Argument, isFinite Fact) { // finite(s₀)
					// `rank` sends each point to its place in the interval and
					// `nth` reads the point back off that place; each undoes
					// the other where it is defined. Only `nth` is named in Go
					// — it is the indexing the statement asks for.
					_, nth, matched := a.Obtain2(
						"s₀ and 1 .. card(s₀) hold equally many points, so they can be matched point for point",
						"∃rank:(A → num). ∃nth:(num → A). "+
							"    (∀x:A. x ∈ s₀ ⇒ rank(x) ∈ 1 .. card(s₀) ∧ nth(rank(x)) = x) ∧ "+
							"    (∀i:num. i ∈ 1 .. card(s₀) ⇒ nth(i) ∈ s₀ ∧ rank(nth(i)) = i)",
						By(
							isFinite,
							At(Finite, one, count), // finite(1 .. card(s₀)) — the matching's other guard
							At(CardFromOne, count), // card(1 .. card(s₀)) = card(s₀) — the counts agree
							// Two finite sets of the same count, here s₀ and
							// 1 .. card(s₀), are matched by a pair of mutually
							// inverse maps. The tuple is (source, target), the
							// order that entry states: s₀ supplies the points and
							// the interval indexes them, so `rank` runs s₀ → num
							// and `nth` comes back.
							At(cardinality.CardEqMutualInverses, s, seg)))
					a.Take(nth)

					a.Do(SplitConj(
						Case(
							"no repeats: two indices carrying the same point are carried back to the same index",
							Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[A]()))),
							By(matched)),

						Case(
							"and nothing missed: a point is the one at its own rank, and an index names a point of s₀",
							Derive(func(a *Argument) {
								// The arbitrary point the bridge hands back is not
								// named: both memberships are argued of it at once.
								samePoints(a, "∀y:A. y ∈ s₀ ⇔ y ∈ image(nth₀, 1 .. card(s₀))")
								// The image law is cited bare: it is read here at a
								// source of numbers and a target of anything, and
								// grounding it at that pair fails to materialize.
								a.Show(
									"so membership in s₀ and being reached by the indexing say the same thing",
									By(matched, set_basic.InImage))
							})),
					))
				})
			a.Backward(
				"an interval is finite, and so is anything an interval covers",
				func(a *Argument, indexed Fact) { // ∃f. f indexes s₀
					f, spec := a.Unpack(indexed) // spec: f₀ indexes s₀
					a.Show(
						"so s₀ is the image of a finite set, whatever the indexing does",
						By(
							Normalized,
							spec,
							At(Finite, one, count),              // finite(1 .. card(s₀))
							At(finite_set.FiniteImage, f, seg))) // finite(1 .. card(s₀)) ⇒ finite(image(f₀, 1 .. card(s₀)))
				})
		}),
})}

// FiniteRangeRepeats — a map of the numbers up to N into a set of at most N
// elements repeats a value: otherwise its image has N + 1 elements.
var FiniteRangeRepeats = finiteRangeRepeatsThm{family.Add(registry.ProofEntry{
	Name: "FiniteRangeRepeats",
	Key:  "prop_878af214150f2a92",
	Build: family.Theorem(Statement{
		Binders:    "∀C:set(A). ∀f:(num → A). ∀N:num.",
		Hypotheses: []string{"finite(C)", "card(C) ≤ N", "∀i:num. i ≤ N ⇒ f(i) ∈ C"},
		Conclusion: "∃i j:num. i ≤ N ∧ j ≤ N ∧ i ≠ j ∧ f(i) = f(j)",
	},
		func(a *Argument, C *Expr[Set[A]], f *Arrow[Nat, A], N *Expr[Nat], finiteC, bound, into Fact) {
			indices := a.TermAs[Set[Nat]]("{i:num | i ≤ N}")
			values := a.TermAs[Set[A]]("image(f, {i:num | i ≤ N})")
			noRepeat := a.SupposeNot()
			injective := a.Have(
				"f does not repeat a value on the numbers up to N",
				"injective_on({i:num | i ≤ N}, f)",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[A]()))),
				BySets(noRepeat))
			inside := a.Have(
				"its values lie in C",
				"image(f, {i:num | i ≤ N}) ⊆ C",
				BySets(into))
			size := a.Have(
				"so it has N + 1 values",
				"has_size(image(f, {i:num | i ≤ N}), N + 1)",
				By(
					injective,
					HasSizeBelow.At(N),
					cardinality.HasSizeImageInj.At(f, indices, a.TermAs[Nat]("N + 1"))))
			a.Show(
				"but C has at most N elements",
				ByArith(finiteC, bound, size, inside, cardinality.CardSubset.At(values, C), cardinality.HasSizeDef))
		}),
})}
