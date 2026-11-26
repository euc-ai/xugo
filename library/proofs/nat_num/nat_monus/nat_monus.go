// nat_monus.go — the chapter: truncated subtraction and distance.
//
// Six parts, marked by banners:
//
// - SUB definitional layer
// - SUB laws
// - SUB × MULT distribution: LeftSubDistrib · RightSubDistrib
// - The dist definitional layer
// - Dist laws
// - Dist × mult distribution laws

package nat_monus

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// SUB definitional layer
// ---------------------------------------------------------------------------
//
// `predecessor` and `Sub` (SUB) are DEFINED by their recursion clauses
// (`family.Define`, compiled against peano.Recursion): predecessor by recursion
// on its one argument, `-` by recursion on its RIGHT argument, with predecessor
// in its step. The three composition members (subPresuc, subZero,
// subSuc) close by single InductStep chains citing Sub + predecessor resident.

// ---------------------------------------------------------------------------
// predecessor — the defining equations of the predecessor function
// ---------------------------------------------------------------------------

// predecessor — defined: the predecessor of zero is zero, of a successor
// its argument. A building block of the SUB layer, so it keeps a
// chapter-internal name.
var predecessor = predecessorThm{family.Define(registry.DefEntry{
	Name:      "predecessor",
	Key:       "prop_caea680ad556383a",
	Const:     "predecessor",
	Type:      "num → num",
	Equations: []string{"predecessor(0) = 0", "∀n:num. predecessor(suc(n)) = n"},
})}

// ---------------------------------------------------------------------------
// Sub — the recursion equations of -
// ---------------------------------------------------------------------------

// Sub — `-` defined: subtracting zero is the identity, subtracting a
// successor takes the predecessor of the difference. Spelled `minus`
// in the equations, the operator having no head-position spelling.
var Sub = subThm{family.Define(registry.DefEntry{
	Name:    "Sub",
	Key:     "prop_9bcd4e32a2123047",
	Const:   "-",
	Spelled: "minus",
	Type:    "num → num → num",
	Equations: []string{
		"∀m:num. minus(m, 0) = m",
		"∀m n:num. minus(m, suc(n)) = predecessor(minus(m, n))",
	},
	Deps: []registry.EntryLike{predecessor},
})}

// ---------------------------------------------------------------------------
// subPresuc — a predecessor outside a monus cancels a successor inside
// ---------------------------------------------------------------------------

// subPresuc — the "predecessor absorbs suc across subtraction" step: induction
// on n from Sub's two clauses plus predecessor's suc clause. One induction:
//
//	base: ⊢ ∀m. predecessor(suc m - 0) = m - 0 Sub's zero clause folds
//	 suc m - 0 → suc m and
//	 m - 0 → m; predecessor's suc clause
//	 predecessor(suc m) = m identifies
//	 the two.
//	step: IH ⊢ ∀m. predecessor(suc m - suc n₀) = m - suc n₀
//	 Sub's suc clause rewrites
//	 both sides to predecessor-of-Sub-of-n₀;
//	 the IH ∀m. predecessor(suc m - n₀) =
//	 m - n₀ identifies them under
//	 predecessor congruence.
//
// The leaves cite Sub and predecessor as resident conjunction hyps and close by
// refutation — two cites putting both operators' recursion clauses in
// scope, each leaf consuming the clause its own table row names above.
// Internal auxiliary of the SUB layer, consumed by subSuc.
var subPresuc = subPresucThm{family.Add(registry.ProofEntry{
	Name: "subPresuc",
	Key:  "prop_bd936225646f82e2",
	// Cite Sub + predecessor once (both branches consume both), then induct on n —
	// ∀m stays inside each case since the recursion is on n only.
	Build: family.Theorem("∀m n:num. predecessor(suc(m) - n) = m - n",
		func(a *Argument) {
			a.Do(Cite(Sub))
			a.Do(Cite(predecessor))
			a.Induct("n")
			a.Base(
				"∀m. predecessor(suc m - 0) = m - 0 — Sub folds suc m - 0 → suc m "+
					"and m - 0 → m; predecessor's predecessor(suc m) = m identifies them",
				CnfRefute(),
			)
			a.Step(
				"Sub's suc clause opens both sides, and the IH ∀m. "+
					"predecessor(suc m - n₀) = m - n₀ identifies them under predecessor",
				CnfRefute(),
			)
		}),
})}

// ---------------------------------------------------------------------------
// subZero — monus against zero, on either side
// ---------------------------------------------------------------------------

// subZero — the "both zero-sides of monus" pair: right-zero (m - 0 = m)
// is directly Sub's zero clause; left-zero (0 - m = 0) is one induction
// on m from Sub's suc clause and predecessor's zero clause. A single InductStep
// on m handles both conjuncts jointly:
//
//	base: ⊢ (0 - 0 = 0) ∧ (0 - 0 = 0) Sub's zero clause folds both
//	 sides of both conjuncts to
//	 0 = 0.
//	step: IH (0 - m₀ = 0) ∧ (m₀ - 0 = m₀)
//	 ⊢ (0 - suc m₀ = 0) ∧ (suc m₀ - 0 = suc m₀)
//	 left: Sub's suc clause gives
//	 0 - suc m₀ = predecessor(0 - m₀);
//	 IH substitutes 0 - m₀ = 0;
//	 predecessor's zero clause predecessor(0) = 0
//	 closes. right: Sub's zero
//	 clause.
//
// The leaves cite Sub and predecessor as resident conjunction hyps and close by
// refutation, each leaf consuming the clause its table row names above.
// Internal SUB zero-side clause pair.
var subZero = subZeroThm{family.Add(registry.ProofEntry{
	Name: "subZero",
	Key:  "prop_6031cc0b343b0aa8",
	Build: family.Theorem("∀m:num. 0 - m = 0 ∧ m - 0 = m",
		func(a *Argument) {
			a.Do(Cite(Sub))
			a.Do(Cite(predecessor))
			a.Induct("m")
			a.Base(
				"(0 - 0 = 0) ∧ (0 - 0 = 0) — Sub's zero clause folds both conjuncts",
				CnfRefute(),
			)
			a.Step(
				"0 - suc m = 0 by Sub's suc clause, the IH and "+
					"predecessor(0) = 0; suc m - 0 = suc m by Sub's zero clause",
				CnfRefute(),
			)
		}),
})}

// ---------------------------------------------------------------------------
// subSuc — stepping both arguments of a monus leaves it unchanged
// ---------------------------------------------------------------------------

// subSuc — the "suc cancels across monus" clause: Sub's suc clause gives
// suc m - suc n = predecessor(suc m - n); subPresuc gives predecessor(suc m - n) = m - n;
// transitivity closes. No induction — subPresuc did the recursive work.
//
// One direct leaf: cite Sub (its suc clause supplies the LHS→predecessor
// fold), cite subPresuc (supplies the predecessor→RHS fold), refute. Internal
// suc-cancellation step of the SUB layer.
var subSuc = subSucThm{family.Add(registry.ProofEntry{
	Name: "subSuc",
	Key:  "prop_becfb0fd9c008b4d",
	Build: family.Theorem("∀m n:num. suc(m) - suc(n) = m - n",
		By(Normalized, Sub, subPresuc)),
})}

// ---------------------------------------------------------------------------
// SUB laws
// ---------------------------------------------------------------------------
//
// SUB laws: AddSubCancel · AddSubLeftCancel · SubRefl · SubEqZero ·
// SubAddCancel · SucOfSubOne · SucSubOne · LessThanIffAtMostPred ·
// MulPowSubOne. The ≤-facing members (SubEqZero, SubAddCancel, SucOfSubOne,
// LessThanIffAtMostPred) cite nat_order.
//
// Layer sits above the definitional layer (Sub, predecessor, subZero, subSuc):
// AddSubCancel, SubRefl and SubEqZero close by a single InductStep (nested for SubEqZero) whose
// leaves refute against Sub's clause pair, subSuc's suc-cancellation,
// and — for SubEqZero — nat_order's LE clauses; AddSubLeftCancel,
// SubAddCancel and its specialisation SucOfSubOne are no-induction
// compositions, the first from AddSubCancel and commutativity, the
// second from the ≤-as-existence bridge and the third from the second;
// SucSubOne is the same no-induction shape from AddSubCancel and nat_arith.Add1
// alone, the unguarded order needing no bridge. LessThanIffAtMostPred rides the same identification of m with
// suc(m - 1) into nat_order's successor bridge, and MulPowSubOne reads a
// positive power's exponent k as suc(k - 1) to peel one factor off.
//
// All nine members here are Band A (exported). AddSubCancel was Band B
// while its only readers were the three inside this chapter — SubAddCancel
// below, DistLeftAdd and LeftSubDistrib — and it left that band when a
// reader arrived from outside: a counting proof that knows a difference
// was formed by addition wants the UNGUARDED cancellation, and reaching
// SubAddCancel instead costs it the `n ≤ m` guard plus the laws to
// discharge one.

// ---------------------------------------------------------------------------
// AddSubCancel — what addition adds, monus takes back
// ---------------------------------------------------------------------------

// AddSubCancel — subtraction inverts addition on the right: induct on
// the added summand n, refute at each leaf against subZero, subSuc's
// suc-cancellation, and nat_arith.AddClauses — the base consumes nat_arith.AddClauses's
// right-identity conjunct, the step its `m + suc n` conjunct.
//
// It is the unguarded half of the pair SubAddCancel completes: here the
// sum is taken apart in the order it was built, so nothing has to be
// known about the size of the summands. SubAddCancel says the same thing
// for a difference whose subtrahend was NOT just added, and pays an
// `n ≤ m` hypothesis for it.
//
//	base: (m + 0) - 0 = m
//	 nat_arith.AddClauses's right-identity conjunct folds the argument of -
//	 to m; subZero's right-zero half collapses m - 0 to m.
//	step: IH ⊢ (m + n₀) - n₀ = m ⊢ (m + suc n₀) - suc n₀ = m
//	 nat_arith.AddClauses's `m + suc n` conjunct folds m + suc n₀ to suc(m+n₀);
//	 subSuc's suc(m) - suc(n) = m - n peels the suc pair; the IH
//	 closes.
var AddSubCancel = addSubCancelThm{family.Add(registry.ProofEntry{
	Name: "AddSubCancel",
	Key:  "prop_cdb0517426103e3a",
	// Induct on n — the second addend, which is the recursion variable of
	// both nat_arith.AddClauses's suc clauses and subSuc's suc bridge.
	Build: family.Theorem("∀m n:num. m + n - n = m",
		func(a *Argument) {
			a.Do(Cite(nat_arith.AddClauses))
			a.Do(Cite(subSuc))
			a.Do(Cite(subZero))
			a.Induct("n")
			a.Base(
				"nat_arith.AddClauses's m + 0 = m and subZero's m - 0 = m collapse (m + 0) - 0 to m",
				CnfRefute(),
			)
			a.Step(
				"nat_arith.AddClauses's m + suc n = suc(m+n) folds m + suc n₀ "+
					"to suc(m+n₀); subSuc peels the outer suc pair; the IH closes",
				CnfRefute(),
			)
		}),
})}

// ---------------------------------------------------------------------------
// AddSubLeftCancel — what addition adds on the left, monus takes back too
// ---------------------------------------------------------------------------

// AddSubLeftCancel — subtraction inverts addition on the left: no
// induction, no refutation — one rewrite and one cite. nat_arith.AddSym
// turns the sum around under the subtraction, so the subtrahend m
// stands as the right summand; what is left is AddSubCancel's own
// instance, and the cite closes it.
//
// It is the mirror of AddSubCancel, and unguarded for the same reason:
// the subtrahend was just added, so nothing has to be known about the
// size of the summands — the left position costs one commutation and
// nothing else. (SubAddCancel is the guarded relative of both.)
//
//	(m + n) - m = (n + m) - m nat_arith.AddSym, rewriting under the -
//	 = n AddSubCancel
var AddSubLeftCancel = addSubLeftCancelThm{family.Add(registry.ProofEntry{
	Name: "AddSubLeftCancel",
	Key:  "prop_a068b168be957a70",
	Build: family.Theorem("∀m n:num. m + n - m = n",
		func(a *Argument, m, n Term) {
			// nat_arith.AddSym is consumed as a rewrite of the goal, not as a
			// premise. Commutativity is permutative — its ∀-form re-matches its
			// own result — so the rule is pinned at its instance and the ∀-law
			// discharges it.
			a.Show(
				"turn m₀ + n₀ around under the subtraction; the residue is AddSubCancel read at the right summand",
				Expect(LeanRw(a.Ctx().MakePropText("m₀ + n₀ = n₀ + m₀")),
					Case(
						"the rule is nat_arith.AddSym, closed at the cite",
						Cite(nat_arith.AddSym)),
					Case(
						"↦ n₀ + m₀ - m₀ = n₀ — AddSubCancel's instance, closed at the cite",
						Cite(AddSubCancel))))
		}),
})}

// ---------------------------------------------------------------------------
// SubRefl — a number and itself differ by nothing
// ---------------------------------------------------------------------------

// SubRefl — subtracting a number from itself yields zero: single
// induction on n from Sub's clause pair and subSuc's suc-cancellation.
//
//	base: 0 - 0 = 0 Sub's zero clause folds m - 0 = m at m = 0.
//	step: IH n₀ - n₀ = 0 ⊢ suc(n₀) - suc(n₀) = 0
//	 subSuc's suc m - suc n = m - n peels the
//	 outer suc pair to n₀ - n₀; the IH closes.
var SubRefl = subReflThm{family.Add(registry.ProofEntry{
	Name: "SubRefl",
	Key:  "prop_e84c6d1887dcd8c0",
	Build: family.Theorem("∀n:num. n - n = 0",
		func(a *Argument) {
			a.Do(Cite(Sub))
			a.Do(Cite(subSuc))
			a.Induct("n")
			a.Base(
				"Sub's zero clause folds 0 - 0 to 0 — reflexivity closes",
				CnfRefute(),
			)
			a.Step(
				"subSuc peels suc n₀ - suc n₀ to n₀ - n₀; the IH closes",
				CnfRefute(),
			)
		}),
})}

// ---------------------------------------------------------------------------
// SubEqZero — a vanishing monus is exactly the order relation
// ---------------------------------------------------------------------------

// SubEqZero — the ≤ bridge: m - n = 0 iff m ≤ n. Nested induction on
// (m, n) from Sub's clauses, subSuc's suc-cancellation, subZero's
// zero-sides, and nat_order's LE clauses.
//
//	outer base (m = 0): ∀n. (0 - n = 0) ⇔ (0 ≤ n)
//	 subZero's left-zero half gives 0 - n = 0; ZeroLessEq gives 0 ≤ n
//	 unconditionally. Both sides ⊤ — the refuter closes.
//	outer step (m = suc m₀), outer IH ∀n. (m₀ - n = 0) ⇔ (m₀ ≤ n):
//	 inner induct on n.
//	 inner base (n = 0): (suc m₀ - 0 = 0) ⇔ (suc m₀ ≤ 0)
//	 Sub's zero clause folds suc m₀ - 0 to suc m₀, so the left side
//	 reads suc m₀ = 0; LE's zero clause folds the right side to the
//	 same atom. Both sides reduce to it and the iff closes by
//	 equivalence — neither side needs refuting.
//	 inner step (n = suc n₀), inner IH (suc m₀ - n₀ = 0) ⇔ (suc m₀ ≤ n₀):
//	 subSuc folds suc m₀ - suc n₀ to m₀ - n₀; SucLessEqSucIff folds
//	 suc m₀ ≤ suc n₀ to m₀ ≤ n₀. The outer IH at n₀ closes.
var SubEqZero = subEqZeroThm{family.Add(registry.ProofEntry{
	Name: "SubEqZero",
	Key:  "prop_bed555e0228ca8f",
	// Outer induction on m, inner induction on n in the step case.
	Build: family.Theorem("∀m n:num. m - n = 0 ⇔ m ≤ n",
		func(a *Argument) {
			// Both binders stay bound — one induction runs on each.
			m := a.Binder("m")
			n := a.Binder("n")

			a.Induct(m)
			a.Base(
				"outer base (m = 0): subZero's left-zero half + ZeroLessEq — both sides ⊤",
				By(Normalized, subZero, nat_order.ZeroLessEq),
			)
			a.Step(
				// The step case hands over the outer IH ∀n. (m₀ - n = 0) ⇔ (m₀ ≤ n);
				"outer step (m = suc m₀): inner induct on n",
				// the inner step names it as its premise.
				func(b *Argument, outerIH Fact) {
					b.Do(b.Ctx().InductStep(n,
						Case(
							"inner base (n = 0): Sub's zero clause + LE's zero clause reduce both sides to the atom suc m₀ = 0",
							By(Normalized, Sub, nat_order.LessEq),
						),
						Case(
							"inner step (n = suc n₀): subSuc + SucLessEqSucIff peel the suc pair; the outer IH at n₀ closes",
							By(outerIH, subSuc, nat_order.SucLessEqSucIff),
						),
					))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// SubAddCancel — adding back recovers the whole, when nothing was truncated
// ---------------------------------------------------------------------------

// SubAddCancel — subtraction inverts addition under the ≤ hypothesis:
// direct compositional close from the ≤-as-existence-shift bridge, no
// induction.
//
//	nat_order.LessEqExists: n ≤ m ⇔ ∃d. m = n + d
//	AddSubCancel @ (d, n): (d + n) - n = d
//	nat_arith.AddSym: m = n + d = d + n, so m - n = (d + n) - n = d;
//	 hence (m - n) + n = d + n = m.
var SubAddCancel = subAddCancelThm{family.Add(registry.ProofEntry{
	Name: "SubAddCancel",
	Key:  "prop_f03bee74078abd03",
	// Under the hypothesis n₀ ≤ m₀ the three bridges meet: LessEqExists
	// turns the hypothesis into a shift witness d, AddSubCancel cancels it,
	// nat_arith.AddSym orients the sum.
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"n ≤ m",
		},
		Conclusion: "m - n + n = m",
	},
		func(a *Argument, m, n Term, nLeM Fact) {
			a.Show(
				"LessEqExists turns n₀ ≤ m₀ into a shift witness d, "+
					"AddSubCancel cancels it, nat_arith.AddSym orients the sum",
				By(nLeM, nat_order.LessEqExists, AddSubCancel, nat_arith.AddSym))
		}),
})}

// ---------------------------------------------------------------------------
// SucOfSubOne — away from 0, a number IS the successor of n - 1
// ---------------------------------------------------------------------------

// SucOfSubOne — SubAddCancel taken at the subtrahend 1 and read in
// successor form: where anything is left to subtract, `n - 1` really
// is a predecessor.
//
// The hypothesis travels through this layer's three faces of
// positivity to reach the guard SubAddCancel asks for — `n ≠ 0` is
// `0 < n` is `1 ≤ n` — and under that guard taking 1 away and putting
// it back returns n. nat_arith.Add1 then reads the sum `(n - 1) + 1` as
// the successor of `n - 1`, which is the claim. All four premises are
// load-bearing: the two positivity faces are the only route from the
// hypothesis to the guard, and dropping either equation leaves the two
// spellings of `n - 1`'s successor unrelated.
//
// Stated so rather than as `n - 1 + 1 = n`: that spelling is
// SubAddCancel at 1 with its guard restated and states nothing new,
// while the successor form is what a consumer recursing on a bound
// needs — it lets a fact stated at suc(k) be read at a bound that is
// merely non-zero.
//
// The law is proved here from this family's own members and named for
// its consumers: sets/num_segment's RecRight, BelowStrict and
// CombineLeft.
//
// Named `SucOfSubOne` and not `SucSubOne` so that the suc is visibly
// OUTSIDE: `SucSubOne` below is `suc(n) - 1 = n`, a different theorem
// with the same two operations in the other order.
var SucOfSubOne = sucOfSubOneThm{family.Add(registry.ProofEntry{
	Name: "SucOfSubOne",
	Key:  "prop_99c7c2fccc7c0a43",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"n ≠ 0",
		},
		Conclusion: "suc(n - 1) = n",
	},
		func(a *Argument, n Term, nonZero Fact) {
			one := a.Ctx().Numeral(1)

			a.Show(
				"positivity carries n₀ ≠ 0 to 1 ≤ n₀, SubAddCancel puts the 1 "+
					"back under that guard, and Add1 reads the sum as a successor",
				By(
					nonZero,
					At(nat_order.PosIffNonzero, n),   // n₀ ≠ 0 ⇔ 0 < n₀
					At(nat_order.OneLessEqIffPos, n), // 1 ≤ n₀ ⇔ 0 < n₀
					At(SubAddCancel, n, one),         // 1 ≤ n₀ ⇒ n₀ - 1 + 1 = n₀
					nat_arith.Add1))
		}),
})}

// ---------------------------------------------------------------------------
// SucSubOne — one taken off a successor is what it succeeds
// ---------------------------------------------------------------------------

// SucSubOne — taking one away from a successor returns the number it
// succeeds. No induction and no guard: nat_arith.Add1 reads the successor
// as a sum whose right summand is 1, and that summand was just added,
// so AddSubCancel — the unguarded right-summand cancellation — takes it
// straight back.
//
// SucOfSubOne above is the same two operations in the other order, and
// pays the `n ≠ 0` guard that order costs.
var SucSubOne = sucSubOneThm{family.Add(registry.ProofEntry{
	Name: "SucSubOne",
	Key:  "prop_5e340e24ab1302b2",
	Build: family.Theorem("∀n:num. suc(n) - 1 = n",
		func(a *Argument, n Term) {
			one := a.Ctx().Numeral(1)

			// Normalized: the two equations meet the goal by rewriting, not
			// by refutation — Add1's instance turns the goal's suc(n₀) into
			// n₀ + 1, and what remains IS AddSubCancel's instance; no key.
			a.Show(
				"Add1 reads suc(n₀) as n₀ + 1, and AddSubCancel takes the 1 back",
				By(
					Normalized,
					At(nat_arith.Add1, n),     // suc(n₀) = n₀ + 1
					At(AddSubCancel, n, one))) // n₀ + 1 - 1 = n₀
		}),
})}

// ---------------------------------------------------------------------------
// LessThanIffAtMostPred — below a positive bound is at most its predecessor
// ---------------------------------------------------------------------------

// LessThanIffAtMostPred — lying strictly below a positive bound is
// lying at most at its predecessor: a half-open range in ℕ is a closed
// range one step down. That is the form every interval argument wants,
// which is why it is worth a name — the interval arguments in
// sets/num_segment and real/real_polynomial each derive it inline.
//
// The proof is nat_order's successor bridge read through monus. The
// guard says nothing was truncated, so SubAddCancel puts the 1 back and
// nat_arith.Add1 reads the restored sum as a successor: the bound IS the
// successor of its predecessor. A successor bound is exactly what
// nat_order.LessThanSucIffLessEq trades for the non-strict form.
//
// It rests on SubAddCancel rather than on SucOfSubOne above, which
// makes the same identification: the guard arrives here already in the
// shape SubAddCancel asks for, so routing through the ≠ 0 spelling
// would only cost the two positivity bridges that convert it back.
//
// Stated in this chapter and not in nat_order because the statement is
// about the truncated predecessor: nat_order is the chapter this one
// imports, and it cannot so much as spell the subtraction, while monus
// is what the guard is a guard FOR.
//
// The same bridge at a successor bound is
// nat_order.LessThanSucIffLessEq.
var LessThanIffAtMostPred = lessThanIffAtMostPredThm{family.Add(registry.ProofEntry{
	Name: "LessThanIffAtMostPred",
	Key:  "prop_63bbb563b0791e4c",
	Build: family.Theorem(Statement{
		Binders: "∀m j:num.",
		Hypotheses: []string{
			"1 ≤ m",
		},
		Conclusion: "j < m ⇔ j ≤ m - 1",
	},
		func(a *Argument, m, j Term, mPos Fact) {
			v := ops(a.Ctx())
			one := a.Ctx().Numeral(1)
			pred := v.Minus.Apply(m, one) // m₀ - 1, the bound's predecessor

			// Normalized: the close is simplification, not refutation — the
			// two equations rewrite the bound into the successor form the
			// bridge is stated at, and nothing is left to refute.
			a.Show(
				"under the guard m₀ is the successor of m₀ - 1, and "+
					"the successor bridge trades j₀ < m₀ for j₀ ≤ m₀ - 1",
				By(
					Normalized,
					mPos,
					At(SubAddCancel, m, one), // 1 ≤ m₀ ⇒ m₀ - 1 + 1 = m₀, guard discharged by mPos
					At(nat_arith.Add1, pred), // suc(m₀ - 1) = m₀ - 1 + 1
					At(nat_order.LessThanSucIffLessEq, j, pred), // j₀ < suc(m₀ - 1) ⇔ j₀ ≤ m₀ - 1
				))
		}),
})}

// ---------------------------------------------------------------------------
// MulPowSubOne — a positive power is its base times the power one lower
// ---------------------------------------------------------------------------

// MulPowSubOne — a positive power is its base times the power one lower:
// k is the successor of k − 1, and m^suc(j) = m·m^j.
var MulPowSubOne = mulPowSubOneThm{family.Add(registry.ProofEntry{
	Name: "MulPowSubOne",
	Key:  "prop_db3d7f2b6a5ed5f0",
	Build: family.Theorem(Statement{
		Binders: "∀m k:num.",
		Hypotheses: []string{
			"0 < k",
		},
		Conclusion: "m * m ^ (k - 1) = m ^ k",
	}, func(a *Argument, m, k *Expr[Nat], positive Fact) {
		predecessor := a.Have(
			"k is the successor of k − 1",
			"k = suc(k - 1)",
			ByArith(positive))
		a.Show(
			"m^suc(k − 1) is m·m^(k − 1)",
			By(predecessor, nat_arith.NatPow))
	}),
})}

// ---------------------------------------------------------------------------
// SUB × MULT distribution: LeftSubDistrib · RightSubDistrib
// ---------------------------------------------------------------------------
//
// Left is the heavyweight member — no induction, but a case-split via
// nat_order.LessEqTotal (monus is piecewise) whose p ≤ n branch runs
// through a Skolemized LessEqExists shift; Right is a nat_arith.MulSym mirror
// composition.

// ---------------------------------------------------------------------------
// LeftSubDistrib — ⊢ ∀m n p. m*(n-p) = m*n - m*p
// ---------------------------------------------------------------------------

// LeftSubDistrib — left-distributivity of * over − (monus) on num. Since
// monus is piecewise, the proof splits on which of n, p is larger. Two
// sub-lemmas, one per ordering, then a case-split via nat_order.LessEqTotal
// on the goal:
//
//	lemmaNLeP (n ≤ p): both sides equal 0. Since n ≤ p, nat_order.LessEqMulCancel
//	 lifts to m*n ≤ m*p; SubEqZero converts both n ≤ p
//	 and m*n ≤ m*p to sub-equal-zero equations; nat_arith.MulClauses
//	 supplies m*0 = 0. The chain is Trans through 0, with
//	 a sub-Trans through m*0 for the LHS half.
//
//	lemmaPLeN (p ≤ n): nat_order.LessEqExists gives ∃d. n = p + d.
//	 Skolemize d, substitute n = p + d, then Trans through
//	 m*d. LHS m*(n-p) = m*d closes via AddSubCancel
//	 ((p+d)-p = d after nat_arith.AddSym) + auto. RHS m*d = m*n - m*p
//	 folds through a two-level bridge: through
//	 (m*p + m*d) - m*p (which AddSubCancel + nat_arith.AddSym reduce
//	 to m*d), then through m*(p+d) inside (nat_arith.LeftAddDistrib
//	 + the Skolemized shift n = p + d).
//
//	goal: LessEqTotal at (n₀, p₀) gives n₀ ≤ p₀ ∨ p₀ ≤ n₀, and the two
//	 sub-lemmas are the matching ∀-implications — the refuter chains
//	 the disjunction through them.
var LeftSubDistrib = leftSubDistribThm{family.Add(registry.ProofEntry{
	Name: "LeftSubDistrib",
	Key:  "prop_c8fd2b80e1c34631",
	// The proof is three sections written as a linear script: the two
	// ordering lemmas are Go locals the goal cites by closure capture.
	Build: family.Sections(
		"∀m n p:num. m * (n - p) = m * n - m * p",
		func(ctx *Script, headline string) *GoalStackNode {
			// lemmaNLeP: ∀m n p. n ≤ p ⇒ m*(n-p) = m*n - m*p.
			// n ≤ p ⇒ n-p = 0 (SubEqZero) ⇒ m*(n-p) = m*0 = 0 (nat_arith.MulClauses).
			// n ≤ p ⇒ m*n ≤ m*p (LessEqMulCancel) ⇒ m*n - m*p = 0 (SubEqZero).
			lemmaNLeP := ctx.Lemma(
				Statement{
					Binders: "∀m n p:num.",
					Hypotheses: []string{
						"n ≤ p",
					},
					Conclusion: "m * (n - p) = m * n - m * p",
				},
				// The ≤-antecedent is consumed by the refuter as a resident hyp,
				// never by name.
				func(a *Argument, m, n, p Term, _ Fact) {
					a.Do(
						Cite(nat_order.LessEqMulCancel),
						Cite(SubEqZero),
						Cite(nat_arith.MulClauses),
						// Both sides collapse to 0 — the equation chain says so directly:
						// m₀*(n₀-p₀) = m₀*0 = 0 = m₀*n₀ - m₀*p₀
						CalcEq(
							Leg(
								a.Ctx().TermText("m₀ * 0"),
								"SubEqZero folds n₀-p₀ to 0 under n₀ ≤ p₀",
								CnfRefute()),
							Leg(
								a.Ctx().TermText("0"),
								"MulClauses's 0 = m*0 conjunct at m := m₀",
								CnfRefute()),
							FinalLeg(
								"LessEqMulCancel lifts n₀ ≤ p₀ to m₀*n₀ ≤ m₀*p₀, so SubEqZero collapses the difference to 0",
								CnfRefute()),
						),
					)
				})

			// lemmaPLeN: ∀m n p. p ≤ n ⇒ m*(n-p) = m*n - m*p.
			// LessEqExists at (n_0, p_0) gives ∃d. n_0 = p_0 + d. Skolemize d, keep
			// the equation resident, then bridge:
			//
			//	m*(n_0-p_0) = m*d_0 (via AddSubCancel+nat_arith.AddSym)
			//	m*d_0 = (m*p_0 + m*d_0) - m*p_0 (via AddSubCancel+nat_arith.AddSym)
			//	(m*p_0 + m*d_0) - m*p_0 = m*n_0 - m*p_0 (via Congr + nat_arith.LeftAddDistrib)
			lemmaPLeN := ctx.Lemma(
				Statement{
					Binders: "∀m n p:num.",
					Hypotheses: []string{
						"p ≤ n",
					},
					Conclusion: "m * (n - p) = m * n - m * p",
				},
				// The ≤-antecedent is consumed by the refuter as a resident hyp —
				// LessEqExists at (n₀, p₀) is what turns it into the shift witness,
				// and nothing below addresses it by name.
				func(a *Argument, m, n, p Term, _ Fact) {
					a.Do(
						// The three rewriting facts the Calc legs below consume.
						Cite(nat_arith.LeftAddDistrib),
						Cite(AddSubCancel),
						Cite(nat_arith.AddSym),
						// LessEqExists ground at (n₀, p₀), its ∀-source consumed:
						// the Calc legs below close against the whole resident
						// context, so the wide source must not survive into them.
						Cite(nat_order.LessEqExists, n, p),
					)
					// SplitHypIff on the grounded iff (∃d. n₀ = p₀+d) ⇔ (p₀ ≤ n₀) —
					// the only top-level ⇔-shaped hyp resident, so the bare form hits
					// it unambiguously, no positional index needed. Forward branch:
					// get ∃d, Skolemize → d₀, then Trans-bridge.
					a.Do(SplitHypIff(
						BothHold(
							"p₀ ≤ n₀ ⇒ ∃d. n₀ = p₀ + d — Skolemize d₀, substitute, then Trans through m*d₀",
							Given(func(b *Argument, shifted Fact) {
								// Mints d₀ — which the legs below name in text —
								// and the shift equation n₀ = p₀ + d₀, which stays
								// resident for the legs to read.
								b.Unpack(shifted)
								b.Do(
									// m₀*(n₀-p₀) = m₀*d₀ = (m₀*p₀ + m₀*d₀) - m₀*p₀ = m₀*n₀ - m₀*p₀
									CalcEq(
										Leg(
											b.Ctx().TermText("m₀ * d₀"),
											"n₀ substituted as p₀+d₀; AddSubCancel + nat_arith.AddSym reduce (p₀+d₀)-p₀ to d₀",
											CnfRefute()),
										Leg(
											b.Ctx().TermText("(m₀ * p₀ + m₀ * d₀) - m₀ * p₀"),
											"AddSubCancel + nat_arith.AddSym re-expand m₀*d₀ as (m₀*p₀ + m₀*d₀) - m₀*p₀",
											CnfRefute()),
										FinalLeg(
											"Congr strips the common − m₀*p₀, leaving m₀*p₀ + m₀*d₀ = m₀*n₀ — the sub-chain below",
											Congr(),
											// m₀*p₀ + m₀*d₀ = m₀*(p₀ + d₀) = m₀*n₀
											CalcEq(
												Leg(
													b.Ctx().TermText("m₀ * (p₀ + d₀)"),
													"LeftAddDistrib direct",
													CnfRefute()),
												FinalLeg(
													"the Skolem equation p₀+d₀ = n₀, under Congr",
													CnfRefute()),
											)),
									),
								)
							}),
						),
						NeitherHolds(
							"¬(∃d. n₀ = p₀+d) ∧ p₀ ≤ n₀ — the ¬∃ hyp contradicts the ≤; ⊥ closes trivially",
							TrivialNormalized(),
						),
					))
				})

			// Case split via nat_order.LessEqTotal at (n_0, p_0) → n₀ ≤ p₀ ∨ p₀ ≤ n₀;
			// each disjunct dispatches to the corresponding sub-lemma (as a resident
			// ∀-implication hyp introduced by Use).
			return ctx.Theorem(headline,
				func(a *Argument, m, n, p Term) {
					// LessEqTotal ground at (n₀, p₀) is the disjunction n₀ ≤ p₀ ∨ p₀ ≤ n₀;
					// the two sub-lemmas stay ∀-quantified implications, and the refuter
					// chains the disjunction through them.
					a.Do(By(At(nat_order.LessEqTotal, n, p), lemmaNLeP, lemmaPLeN))
				})
		}),
})}

// ---------------------------------------------------------------------------
// RightSubDistrib — a factor spreads across a monus, from the other side
// ---------------------------------------------------------------------------

// RightSubDistrib — right-distributivity of * over − on num, obtained by
// mirroring LeftSubDistrib through nat_arith.MulSym:
//
//	(m - n) * p = p * (m - n) [nat_arith.MulSym]
//	 = p*m - p*n [LeftSubDistrib]
//	 = m*p - n*p [nat_arith.MulSym on each product]
//
// No induction: with LeftSubDistrib and nat_arith.MulSym both resident as
// ∀-hypotheses, the leaf closes by refutation.
var RightSubDistrib = rightSubDistribThm{family.Add(registry.ProofEntry{
	Name: "RightSubDistrib",
	Key:  "prop_e9e287c3742fe725",
	// No induction, no bridges: nat_arith.MulSym commutes each product onto the form
	// LeftSubDistrib states, and the two premises close the goal together.
	Build: family.Theorem(
		"∀m n p:num. (m - n) * p = m * p - n * p",
		func(a *Argument, m, n, p Term) {
			a.Do(By(LeftSubDistrib, nat_arith.MulSym))
		}),
})}

// ---------------------------------------------------------------------------
// The dist definitional layer
// ---------------------------------------------------------------------------
//
// The dist definitional layer: Dist · DistRefl · DistSym ·
// DistEqZero. nat_dist(m, n) = (m - n) + (n - m) is the ℕ metric.
//
// `NatDistDef` defines `nat_dist` by one direct equation, not by
// recursion as `Sub` and nat_arith's operations are defined: the
// definition is a plain λ, so `Dist` rewrites by it
// (`Rewrite(ConstDef("nat_dist"))`) and no existence has to be proved.
// The three derived members each cite `Dist` and reduce to elementary
// arithmetic over `-` and `+`.
//
// The pair projections come from cartesian/pairs, which curates
// them: `nat_dist` is applied to a pair written out, so they appear the
// moment the definition unfolds.

// ---------------------------------------------------------------------------
// Dist — ⊢ ∀m n. nat_dist((m, n)) = (m - n) + (n - m)
// ---------------------------------------------------------------------------

// NatDistDef — the distance defined: the two truncated differences of a
// pair's components, added. Spelled `distance` in the equation, the
// DSL keeping `nat_dist` for its own surface.
var NatDistDef = natDistDefThm{family.Define(registry.DefEntry{
	Name:      "NatDistDef",
	Key:       "prop_2b5874dbb0b7f8ff",
	Const:     "nat_dist",
	Spelled:   "distance",
	Type:      "prod(num, num) → num",
	Overload:  "dist",
	Equations: []string{"∀p:prod(num, num). distance(p) = (fst(p) - snd(p)) + (snd(p) - fst(p))"},
	Deps:      []registry.EntryLike{Sub},
})}

// Dist — the metric on ℕ. `nat_dist` is axiomatically defined as
// `nat_dist = λp. (fst(p) - snd(p)) + (snd(p) - fst(p))`. Two sections:
// a bridge folds the pair projections on num-specialized fst / snd
// (∀m n. (m - n) + (n - m) = fst-snd-of-(m,n) form), then the goal
// rewrites dist's axiomatic def and cites the bridge.
//
// The section texts' `-` and `+` need no dep to parse: the text DSL's
// overloaded arithmetic operators resolve on num operands straight to
// the canonical arithmetic metas (buildBinOp's arithOperator table,
// scope-first). pairs.Fst / pairs.Snd are what the bridge cites, at
// (num, num) — they are polymorphic, so the cite names the pair type.
var Dist = distThm{family.Add(registry.ProofEntry{
	Name: "Dist",
	Key:  "prop_8719574ecc457f6d",
	// The proof is two sections written as a linear script: `bridge` is a Go
	// local the goal cites by closure capture.
	Build: family.Sections(
		"∀m n:num. dist((m, n)) = m - n + (n - m)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// bridge — fst / snd are polymorphic; instantiate at (num, num)
			// so the eqSimplify sees monomorphic pair-projection facts,
			// then the two cites close.
			fstAtNum := pairs.Fst.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())
			sndAtNum := pairs.Snd.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())
			bridge := ctx.Lemma(
				"∀m n:num. m - n + (n - m) = fst((m, n)) - snd((m, n)) + (snd((m, n)) - fst((m, n)))",
				func(a *Argument, m, n Term) {
					a.Do(Cite(fstAtNum), Cite(sndAtNum))
				})

			// goal: rewrite by dist's axiomatic def (fold nat_dist((m,n)) into its
			// fst/snd form), then cite the bridge to identify with (m-n)+(n-m).
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(Rewrite(ctx.ConstDef("nat_dist"), v.NatDist), CiteNode(bridge))
				})
		}),
})}

// ---------------------------------------------------------------------------
// DistRefl — a point is at no distance from itself
// ---------------------------------------------------------------------------

// DistRefl — the metric vanishes on the diagonal. nat_dist((n, n)) unfolds
// (via Dist) to (n - n) + (n - n); SubRefl gives n - n = 0; 0 + 0 = 0
// by nat_arith.AddZero (0's right-neutrality). One direct chain — no induction.
var DistRefl = distReflThm{family.Add(registry.ProofEntry{
	Name: "DistRefl",
	Key:  "prop_49b32f13fe8a80bb",
	Build: family.Theorem("∀n:num. dist((n, n)) = 0",
		By(Normalized, Dist, SubRefl, nat_arith.AddZero)),
})}

// ---------------------------------------------------------------------------
// DistSym — distance does not depend on which point comes first
// ---------------------------------------------------------------------------

// DistSym — the metric is symmetric. nat_dist((m, n)) unfolds (via Dist)
// to (m - n) + (n - m); nat_dist((n, m)) unfolds to (n - m) + (m - n);
// nat_arith.AddSym gives (m - n) + (n - m) = (n - m) + (m - n) identifying the
// two. One direct chain — no induction.
var DistSym = distSymThm{family.Add(registry.ProofEntry{
	Name: "DistSym",
	Key:  "prop_f313614644930efc",
	Build: family.Theorem("∀m n:num. dist((m, n)) = dist((n, m))",
		By(Dist, nat_arith.AddSym)),
})}

// ---------------------------------------------------------------------------
// DistEqZero — only equal points are at distance zero
// ---------------------------------------------------------------------------

// DistEqZero — the metric separates points: nat_dist((m, n)) = 0 iff
// m = n. The argument runs through the SubEqZero ≤ bridge and
// antisymmetry of ≤:
//
//	nat_dist((m,n)) = 0
//	 ⇔ (m - n) + (n - m) = 0 (Dist)
//	 ⇔ m - n = 0 ∧ n - m = 0 (nat_arith.AddEqZero on ℕ)
//	 ⇔ m ≤ n ∧ n ≤ m (SubEqZero, both directions)
//	 ⇔ m = n (LessEqAntisym)
//
// One direct compositional chain — no induction.
var DistEqZero = distEqZeroThm{family.Add(registry.ProofEntry{
	Name: "DistEqZero",
	Key:  "prop_57fc3d46af3fefed",
	// Each ⇔ of the chain above is a Have: the three intermediate
	// propositions are named and closed against their own dep, so the
	// equivalence the file draws is the structure the kernel checks rather
	// than a route the refuter has to rediscover inside one four-lemma
	// blob.
	//
	// Naming the waypoints removed the refute outright. Each claim is a
	// ground instance of exactly one dep, so the cite's own eqSimplify
	// closes it — absorbing any orientation difference against the dep's
	// recorded form — and with the three claims resident the closing
	// LessEqAntisym cite closes the goal. The flat spelling's single
	// four-lemma CnfRefute is gone, not relocated: this proof now runs
	// without any refuter call.
	Build: family.Theorem("∀m n:num. dist((m, n)) = 0 ⇔ m = n",
		func(a *Argument, m, n Term) {
			unfold := a.Have(
				"unfold: dist((m,n)) = 0 ⇔ (m-n)+(n-m) = 0 — Dist's defining equation",
				"dist((m, n)) = 0 ⇔ m - n + (n - m) = 0",
				Cite(Dist))
			split := a.Have(
				"split: a ℕ sum vanishes iff both summands do — nat_arith.AddEqZero",
				"m - n + (n - m) = 0 ⇔ m - n = 0 ∧ n - m = 0",
				Cite(nat_arith.AddEqZero))
			bridge := a.Have(
				"bridge: a vanishing monus IS a bound — SubEqZero in both directions",
				"m - n = 0 ∧ n - m = 0 ⇔ m ≤ n ∧ n ≤ m",
				Cite(SubEqZero))
			a.Show(
				"dist((m₀,n₀)) = 0 ⇔ m₀ = n₀ — LessEqAntisym collapses the two "+
					"bounds, and the three claims chain the equivalence back to dist",
				By(unfold, split, bridge, nat_order.LessEqAntisym))
		}),
})}

// ---------------------------------------------------------------------------
// Dist laws
// ---------------------------------------------------------------------------
//
// Lands the shift-cancellation pair DistLeftAdd / DistRightAdd and the ℕ-metric
// inequalities: DistLessEqCases, DistAddBound, DistTriangle, DistAdd2,
// DistAdd2Rev, DistTriangleLessEq, DistTrianglesLessEq.
//
// The de-Arith recipe at the monus layer (the BoundsLinear pilot),
// carried here by DistLessEqCases: cite nat_order.LessEqTotal to case-split
// on the ordering of two ℕ operands, then in each branch install
// SubEqZero / SubAddCancel / AddSubCancel to pin the monus terms,
// LessEqAdd / nat_arith.AddSym to bring the sum-side under LessEqTrans, and let
// CnfRefute paramodulate through the ≤-chain. Every leaf closes GROUND
// (Cite at concrete Skolems, no wide-∀ install — the
// refute-poisoning class BoundsLinear diagnosed).
//
// Above DistLessEqCases the tier leaves the monus layer entirely: the
// inequality members (DistAddBound, DistTriangle, DistAdd2,
// DistAdd2Rev) reduce their goal through DistLessEqCases' bound
// characterization — no dist unfold and no ordering case-split, just
// ground one-sided-bound facts chained by LessEqAdd / LessEqAdd2 /
// LessEqAddCancel / LessEqTrans with nat_arith.AddAssoc/arith.AddSym regrouping.
// Pure permute-and-reassociate steps are one `nat_arith.AddAC(ctx).Eq`
// premise each — the equation appears once, in the list that uses it
// (the assoc/sym ground instances happen at the Prop layer; only the
// final equation lands on the leaf); a lone nat_arith.AddSym flip or a walk
// entangled with ≤-reasoning stays hand-spelled.
//
// DAG (within this file):
//
// 	DistLeftAdd : [Dist, AddSubCancel, nat_arith.AddSym, SubEqZero, nat_arith.AddZero]
// 	 + {nat_order.LessEqAdd}
// 	DistRightAdd : [DistSym, DistLeftAdd]
// 	DistLessEqCases : [Dist, SubEqZero, SubAddCancel, nat_arith.AddSym, nat_arith.AddClauses]
// 	 + {nat_order.LessEqTotal, LessEqAddCancel, LessEqAdd, LessEqTrans}
// 	DistAddBound : [DistLessEqCases, nat_arith.AddAssoc, nat_arith.AddSym]
// 	 + {nat_order.LessEqAdd}
// 	DistTriangle : [DistLessEqCases, nat_arith.AddAssoc, nat_arith.AddSym]
// 	 + {nat_order.LessEqRefl, LessEqAdd2, LessEqTrans}
// 	DistAdd2 : [DistLessEqCases, nat_arith.AddAssoc, nat_arith.AddSym]
// 	 + {nat_order.LessEqRefl, LessEqAdd2}
// 	DistAdd2Rev : [DistLessEqCases, nat_arith.AddAssoc, nat_arith.AddSym]
// 	 + {nat_order.LessEqRefl, LessEqAdd2, LessEqAddCancel, LessEqTrans}
// 	DistTriangleLessEq : [DistTriangle] + {nat_order.LessEqTrans}
// 	DistTrianglesLessEq : [DistTriangle, DistSym, nat_arith.AddAssoc, nat_arith.AddSym]
// 	 + {nat_order.LessEqAdd2, LessEqAddCancel, LessEqTrans}

// ---------------------------------------------------------------------------
// DistLeftAdd — a point and its shift are exactly the shift apart
// ---------------------------------------------------------------------------

// DistLeftAdd — cancelling the left summand: nat_dist(m + n, m) = n. Direct
// unfold via Dist gives `((m+n)-m) + (m-(m+n))`; AddSubCancel folds the
// first monus to n through nat_arith.AddSym (its clause cancels the RIGHT
// summand, (n+m)-m = n, so nat_arith.AddSym bridges the goal's m+n operand
// order); the direct nat_order.LessEqAdd instance m ≤ m+n + SubEqZero
// fold the second monus to 0; nat_arith.AddZero collapses the resulting `n + 0`
// back to n.
//
// Chapter API: DistRightAdd below is the in-family consumer, and
// slope.toolkit_step_bound cites it directly.
var DistLeftAdd = distLeftAddThm{family.Add(registry.ProofEntry{
	Name: "DistLeftAdd",
	Key:  "prop_7d9c9c695b821254",
	Build: family.Theorem("∀m n:num. dist((m + n, m)) = n",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			mPlusN := v.Add(m, n)

			a.Do(By(
				// Unfold: nat_dist((m₀+n₀, m₀)) = ((m₀+n₀) - m₀) + (m₀ - (m₀+n₀)).
				At(Dist, mPlusN, m),
				// First monus → n₀: cancel the right summand, with nat_arith.AddSym
				// bridging the operand order.
				At(nat_arith.AddSym, m, n), // m₀ + n₀ = n₀ + m₀
				At(AddSubCancel, n, m),     // (n₀ + m₀) - m₀ = n₀
				// Second monus → 0: m₀ ≤ m₀ + n₀ makes it vanish.
				At(SubEqZero, m, mPlusN),      // m₀ - (m₀+n₀) = 0 ⇔ m₀ ≤ m₀+n₀
				At(nat_order.LessEqAdd, m, n), // m₀ ≤ m₀ + n₀
				// n₀ + 0 collapses back to n₀.
				At(nat_arith.AddZero, n),
			))
		}),
})}

// ---------------------------------------------------------------------------
// DistRightAdd — the same, with the shifted point on the right
// ---------------------------------------------------------------------------

// DistRightAdd — mirror of DistLeftAdd across the pair's arguments. DistSym
// flips `nat_dist(m, m+n)` to `nat_dist(m+n, m)`; DistLeftAdd identifies
// `nat_dist(m+n, m)` with n, and the two equations compose.
//
// Chapter API (like DistLeftAdd); slope's less_eq_exists and recip_approx
// are the outside consumers.
var DistRightAdd = distRightAddThm{family.Add(registry.ProofEntry{
	Name: "DistRightAdd",
	Key:  "prop_eeb1d46462a75014",
	Build: family.Theorem("∀m n:num. dist((m, m + n)) = n",
		func(a *Argument, m, n Term) {
			a.Do(By(Normalized, DistSym, DistLeftAdd))
		}),
})}

// ---------------------------------------------------------------------------
// DistLessEqCases — bounding a distance is bounding each side's excess
// ---------------------------------------------------------------------------

// DistLessEqCases — the metric-bound ⇔ its two one-sided bounds. Case-split
// on the ordering of (m, n) via nat_order.LessEqTotal; in the m ≤ n
// branch the metric collapses to n - m and the ⇔ reduces to the monus
// adjunction `(n-m) ≤ p ⇔ n ≤ m+p`:
//
//	SubEqZero pins m-n = 0 (so dist = 0 + (n-m), folded by nat_arith.AddClauses);
//	SubAddCancel gives n = (n-m) + m; nat_arith.AddSym flips it to m + (n-m) so
//	LessEqAddCancel's instance `(n-m) ≤ p ⇔ m+(n-m) ≤ m+p` rewrites the
//	metric side onto `n ≤ m+p`; the discarded conjunct m ≤ n+p is
//	unconditionally true on this branch (m ≤ n ≤ n+p via LessEqAdd +
//	LessEqTrans). The n ≤ m branch is symmetric.
var DistLessEqCases = distLessEqCasesThm{family.Add(registry.ProofEntry{
	Name: "DistLessEqCases",
	Key:  "prop_c6ea5c4905e7664e",
	Build: family.Theorem(
		"∀m n p:num. dist((m, n)) ≤ p ⇔ m ≤ n + p ∧ n ≤ m + p",
		func(a *Argument, m, n, p Term) {
			v := ops(a.Ctx())

			nSubM := v.Minus.Apply(n, m)
			mSubN := v.Minus.Apply(m, n)

			a.Do(
				Cite(nat_order.LessEqTotal, m, n),
				SplitDisj(
					LeftHolds(
						"m ≤ n: dist = n-m; LessEqAddCancel transports (n-m) ≤ p "+
							"onto n ≤ m+p along n = m+(n-m); m ≤ n+p rides m ≤ n ≤ n+p",
						Given(func(b *Argument, mLeN Fact) {
							b.Show(
								"the metric side folds onto n ≤ m+p, and the discarded conjunct m ≤ n+p is free on this branch",
								By(
									Normalized,
									mLeN,
									Dist,
									nat_arith.AddClauses,
									At(SubEqZero, m, n),
									At(SubAddCancel, n, m),
									At(nat_order.LessEqAddCancel, m, nSubM, p),
									At(nat_arith.AddSym, nSubM, m),
									At(nat_order.LessEqAdd, n, p),
									At(nat_order.LessEqTrans, m, n, v.Add(n, p))))
						}),
					),
					RightHolds(
						"n ≤ m: symmetric — dist = m-n, LessEqAddCancel at (m-n, p, n) "+
							"transported along m = (m-n)+n = n+(m-n); n ≤ m+p rides n ≤ m ≤ m+p",
						Given(func(b *Argument, nLeM Fact) {
							b.Show(
								"the mirror: the metric side folds onto m ≤ n+p, and n ≤ m+p is free on this branch",
								By(
									Normalized,
									nLeM,
									Dist,
									nat_arith.AddClauses,
									At(SubEqZero, n, m),
									At(SubAddCancel, m, n),
									At(nat_order.LessEqAddCancel, n, mSubN, p),
									At(nat_arith.AddSym, mSubN, n),
									At(nat_order.LessEqAdd, m, p),
									At(nat_order.LessEqTrans, n, m, v.Add(m, p))))
						}),
					),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// DistAddBound — two points are never further apart than their sum
// ---------------------------------------------------------------------------

// DistAddBound — the metric is bounded by the sum, derived ABOVE the
// monus layer through DistLessEqCases (no dist unfold, no ordering case
// split): at (m, n, m+n) the characterization reduces the goal to
//
//	m ≤ n+(m+n) ∧ n ≤ m+(m+n),
//
// and each conjunct is one ground LessEqAdd instance regrouped by one
// AC-regroup: m ≤ m+(n+n) = n+(m+n), mirrored with n ≤ n+(m+m) =
// m+(m+n).
var DistAddBound = distAddBoundThm{family.Add(registry.ProofEntry{
	Name: "DistAddBound",
	Key:  "prop_a09428dea1c6a3b4",
	Build: family.Theorem(
		"∀m n:num. dist((m, n)) ≤ m + n",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			sum := v.Add(m, n) // the goal's bound m + n

			a.Show(
				"DistLessEqCases at (m, n, m+n) leaves m ≤ n+(m+n) ∧ n ≤ m+(m+n); "+
					"each conjunct is one LessEqAdd instance through its regroup",
				By(
					At(DistLessEqCases, m, n, sum),
					At(nat_order.LessEqAdd, m, v.Add(n, n)),
					// m-side: carry the spare n across the sum
					nat_arith.AddAC(ctx).Eq(v.Add(m, v.Add(n, n)), v.Add(n, sum)),
					At(nat_order.LessEqAdd, n, v.Add(m, m)),
					// n-side: the mirror
					nat_arith.AddAC(ctx).Eq(v.Add(n, v.Add(m, m)), v.Add(m, sum))))
		}),
})}

// ---------------------------------------------------------------------------
// DistTriangle — a detour through a third point is never shorter
// ---------------------------------------------------------------------------

// DistTriangle — the triangle inequality of the ℕ-metric, derived
// entirely ABOVE the monus layer through DistLessEqCases (no case split,
// no dist unfold):
//
//	DistLessEqCases at (m, p, dmn+dnp) reduces the goal to the two
//	one-sided bounds m ≤ p + (dmn+dnp) ∧ p ≤ m + (dmn+dnp).
//	DistLessEqCases at (m, n, dmn) / (n, p, dnp) + LessEqRefl give the
//	legs' own one-sided bounds (m ≤ n+dmn, n ≤ m+dmn, n ≤ p+dnp,
//	p ≤ n+dnp); LessEqAdd2 adds a leg's metric to both sides of the
//	other leg's bound, LessEqTrans chains, and nat_arith.AddAssoc + nat_arith.AddSym
//	regroup (p+dnp)+dmn onto p + (dmn+dnp) (mirrored for the m side).
var DistTriangle = distTriangleThm{family.Add(registry.ProofEntry{
	Name: "DistTriangle",
	Key:  "prop_8b127b3244b92254",
	Build: family.Theorem(
		"∀m n p:num. dist((m, p)) ≤ dist((m, n)) + dist((n, p))",
		func(a *Argument, m, n, p Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			dMN := v.NatDist.Apply(v.Pair.Apply(m, n)) // dmn = nat_dist(m, n)
			dNP := v.NatDist.Apply(v.Pair.Apply(n, p)) // dnp = nat_dist(n, p)

			a.Show(
				"each leg's bound grown by the other leg's metric, then "+
					"chained — the goal's own reduction at (m, p, dmn+dnp)",
				By(
					// One-sided bounds of the two legs: dmn ≤ dmn (refl) feeds
					// the ⇔ forward, yielding m ≤ n+dmn ∧ n ≤ m+dmn (mirrored
					// for dnp).
					At(DistLessEqCases, m, n, dMN),
					At(DistLessEqCases, n, p, dNP),
					At(nat_order.LessEqRefl, dMN),
					At(nat_order.LessEqRefl, dNP),
					// The goal's own reduction: nat_dist(m,p) ≤ dmn+dnp ⇔ the two bounds.
					At(DistLessEqCases, m, p, v.Add(dMN, dNP)),
					// m-side: m ≤ n+dmn ≤ (p+dnp)+dmn (add dmn to n ≤ p+dnp),
					// then the p-side regroup lands it on the ⇔'s own shape.
					At(nat_order.LessEqAdd2, n, dMN, v.Add(p, dNP), dMN),
					At(nat_order.LessEqTrans, m, v.Add(n, dMN), v.Add(v.Add(p, dNP), dMN)),
					nat_arith.AddAC(ctx).Eq(
						v.Add(v.Add(p, dNP), dMN), v.Add(p, v.Add(dMN, dNP))),
					// p-side: p ≤ n+dnp ≤ (m+dmn)+dnp (add dnp to n ≤ m+dmn),
					// with the mirror regroup.
					At(nat_order.LessEqAdd2, n, dNP, v.Add(m, dMN), dNP),
					At(nat_order.LessEqTrans, p, v.Add(n, dNP), v.Add(v.Add(m, dMN), dNP)),
					nat_arith.AddAC(ctx).Eq(
						v.Add(v.Add(m, dMN), dNP), v.Add(m, v.Add(dMN, dNP))),
				))
		}),
})}

// ---------------------------------------------------------------------------
// DistAdd2 — adding pairs coordinatewise cannot outrun the two gaps
// ---------------------------------------------------------------------------

// DistAdd2 — the metric is subadditive under coordinatewise addition.
// Same DistLessEqCases route as DistTriangle (no dist unfold, no case
// split): the goal reduces to m+n ≤ (p+q)+(dmp+dnq) ∧ the mirror,
// and each bound is the pairwise sum (LessEqAdd2) of the coordinate
// bounds m ≤ p+dmp and n ≤ q+dnq (DistLessEqCases forward + LessEqRefl),
// regrouped by the additive interchange law
// (a+b)+(c+d) = (a+c)+(b+d) — one AC-regroup premise per side over the
// nat_arith.AddAssoc/arith.AddSym certs.
var DistAdd2 = distAdd2Thm{family.Add(registry.ProofEntry{
	Name: "DistAdd2",
	Key:  "prop_9fb4d13e5e5c2d07",
	Build: family.Theorem(
		"∀m n p q:num. dist((m + n, p + q)) ≤ dist((m, p)) + dist((n, q))",
		func(a *Argument, m, n, p, q Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			dMP := v.NatDist.Apply(v.Pair.Apply(m, p)) // dmp = nat_dist(m, p)
			dNQ := v.NatDist.Apply(v.Pair.Apply(n, q)) // dnq = nat_dist(n, q)
			D := v.Add(dMP, dNQ)                       // the goal's bound dmp + dnq

			// The coordinate bounds (DistLessEqCases forward at each pair,
			// unlocked by ≤-refl): m ≤ p+dmp, p ≤ m+dmp, n ≤ q+dnq, q ≤ n+dnq.
			coordMP := At(DistLessEqCases, m, p, dMP)
			coordNQ := At(DistLessEqCases, n, q, dNQ)
			reflMP := At(nat_order.LessEqRefl, dMP)
			reflNQ := At(nat_order.LessEqRefl, dNQ)

			left := a.Have(
				"left bound: m+n ≤ (p+q)+(dmp+dnq) — LessEqAdd2 sums "+
					"the coordinate bounds, the p-side interchange regroups",
				MakeProp(v.LessEq(v.Add(m, n), v.Add(v.Add(p, q), D))),
				By(
					coordMP,
					coordNQ,
					reflMP,
					reflNQ,
					At(nat_order.LessEqAdd2, m, n, v.Add(p, dMP), v.Add(q, dNQ)),
					// interchange, p-side: one AC-regroup carrying dmp across q
					nat_arith.AddAC(ctx).Eq(
						v.Add(v.Add(p, dMP), v.Add(q, dNQ)),
						v.Add(v.Add(p, q), D))))
			right := a.Have(
				"right bound: p+q ≤ (m+n)+(dmp+dnq) — mirror through the m-side interchange",
				MakeProp(v.LessEq(v.Add(p, q), v.Add(v.Add(m, n), D))),
				By(
					coordMP,
					coordNQ,
					reflMP,
					reflNQ,
					At(nat_order.LessEqAdd2, p, q, v.Add(m, dMP), v.Add(n, dNQ)),
					// interchange, m-side: the mirror regroup carrying dmp across n
					nat_arith.AddAC(ctx).Eq(
						v.Add(v.Add(m, dMP), v.Add(n, dNQ)),
						v.Add(v.Add(m, n), D))))
			a.Show(
				"DistLessEqCases at (m+n, p+q, dmp+dnq): the two bounds are exactly the reduction's conjuncts",
				By(left, right, At(DistLessEqCases, v.Add(m, n), v.Add(p, q), D)))
		}),
})}

// ---------------------------------------------------------------------------
// DistAdd2Rev — the summands' gap, read back off the gap of the sums
// ---------------------------------------------------------------------------

// DistAdd2Rev — the reverse of DistAdd2: the metric of the SUMMANDS is
// bounded by the metric of the sums plus the metric of the increments.
// Unlike DistTriangle / DistAdd2 this needs true CANCELLATION (m must
// be recovered from m+n), carried by LessEqAddCancel. Writing
// dA = nat_dist(m+n, p+q), dnq = nat_dist(n,q), D = dA+dnq, the m-side bound
// m ≤ p+D comes from
//
//	m+n ≤ (p+q)+dA DistLessEqCases fwd at the sum pair
//	p+q ≤ p+(n+dnq) q ≤ n+dnq (DistLessEqCases fwd) + cancel at p
//	⇒ m+n ≤ (p+(n+dnq))+dA LessEqAdd2 (+dA both sides) + LessEqTrans
//	 = n+(p+D) one AC-regroup (nat_arith.AddAssoc/arith.AddSym certs)
//	⇒ n+m ≤ n+(p+D) nat_arith.AddSym on the left
//	⇒ m ≤ p+D LessEqAddCancel strips the n prefix
//
// (p-side mirrored with q as the cancelled prefix); DistLessEqCases at
// (m, p, D) then closes.
var DistAdd2Rev = distAdd2RevThm{family.Add(registry.ProofEntry{
	Name: "DistAdd2Rev",
	Key:  "prop_6120a66f36e8ab20",
	Build: family.Theorem(
		"∀m n p q:num. dist((m, p)) ≤ dist((m + n, p + q)) + dist((n, q))",
		func(a *Argument, m, n, p, q Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			sumMN := v.Add(m, n)                              // m+n
			sumPQ := v.Add(p, q)                              // p+q
			dA := v.NatDist.Apply(v.Pair.Apply(sumMN, sumPQ)) // dA = nat_dist(m+n, p+q)
			dNQ := v.NatDist.Apply(v.Pair.Apply(n, q))        // dnq = nat_dist(n, q)
			D := v.Add(dA, dNQ)                               // the goal's bound dA + dnq
			nDnq := v.Add(n, dNQ)                             // n + dnq (majorizes q)
			qDnq := v.Add(q, dNQ)                             // q + dnq (majorizes n)

			// DistLessEqCases forward at the sum pair and the increment pair
			// (unlocked by ≤-refl): m+n ≤ (p+q)+dA, p+q ≤ (m+n)+dA,
			// n ≤ q+dnq, q ≤ n+dnq.
			coordSum := At(DistLessEqCases, sumMN, sumPQ, dA)
			coordNQ := At(DistLessEqCases, n, q, dNQ)
			reflA := At(nat_order.LessEqRefl, dA)
			reflNQ := At(nat_order.LessEqRefl, dNQ)

			majQ := a.Have(
				"majorize q inside p+q: p+q ≤ p+(n+dnq) — cancel at prefix p over q ≤ n+dnq",
				MakeProp(v.LessEq(sumPQ, v.Add(p, nDnq))),
				By(coordNQ, reflNQ, nat_order.LessEqAddCancel))
			majN := a.Have(
				"majorize n inside m+n: m+n ≤ m+(q+dnq) — cancel at prefix m over n ≤ q+dnq",
				MakeProp(v.LessEq(sumMN, v.Add(m, qDnq))),
				By(coordNQ, reflNQ, nat_order.LessEqAddCancel))
			mBound := a.Have(
				"m-side bound: m ≤ p+(dA+dnq) — chain m+n ≤ (p+q)+dA ≤ n+(p+D), flip m+n, cancel the n prefix",
				MakeProp(v.LessEq(m, v.Add(p, D))),
				By(
					coordSum,
					reflA,
					majQ,
					// rearrange the m-side majorant, exposing the n prefix
					nat_arith.AddAC(ctx).Eq(
						v.Add(v.Add(p, nDnq), dA),
						v.Add(n, v.Add(p, D))),
					At(nat_order.LessEqAdd2, sumPQ, dA, v.Add(p, nDnq), dA),
					At(nat_order.LessEqTrans, sumMN, v.Add(sumPQ, dA), v.Add(v.Add(p, nDnq), dA)),
					At(nat_arith.AddSym, m, n),
					At(nat_order.LessEqAddCancel, n, m, v.Add(p, D))))
			pBound := a.Have(
				"p-side bound: p ≤ m+(dA+dnq) — mirror chain through q+(m+D), cancel the q prefix",
				MakeProp(v.LessEq(p, v.Add(m, D))),
				By(
					coordSum,
					reflA,
					majN,
					// the mirror regroup, exposing the q prefix
					nat_arith.AddAC(ctx).Eq(
						v.Add(v.Add(m, qDnq), dA),
						v.Add(q, v.Add(m, D))),
					At(nat_order.LessEqAdd2, sumMN, dA, v.Add(m, qDnq), dA),
					At(nat_order.LessEqTrans, sumPQ, v.Add(sumMN, dA), v.Add(v.Add(m, qDnq), dA)),
					At(nat_arith.AddSym, p, q),
					At(nat_order.LessEqAddCancel, q, p, v.Add(m, D))))
			a.Show(
				"DistLessEqCases at (m, p, dA+dnq): the two bounds are the reduction's conjuncts",
				By(mBound, pBound, At(DistLessEqCases, m, p, D)))
		}),
})}

// ---------------------------------------------------------------------------
// DistTriangleLessEq — a bound on the two legs is a bound on the direct route
// ---------------------------------------------------------------------------

// DistTriangleLessEq — bound propagation across the triangle: chain
// DistTriangle (`nat_dist(m,p) ≤ nat_dist(m,n) + nat_dist(n,p)`) with LessEqTrans.
var DistTriangleLessEq = distTriangleLessEqThm{family.Add(registry.ProofEntry{
	Name: "DistTriangleLessEq",
	Key:  "prop_5c4d890544ec059e",
	// The antecedent is a hypothesis, so both facts of the chain
	// nat_dist(m,p) ≤ legs ≤ q are ground instances.
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p q:num.",
			Hypotheses: []string{
				"dist((m, n)) + dist((n, p)) ≤ q",
			},
			Conclusion: "dist((m, p)) ≤ q",
		},
		func(a *Argument, m, n, p, q Term, legBound Fact) {
			v := ops(a.Ctx())

			dMP := v.NatDist.Apply(v.Pair.Apply(m, p)) // the bounded metric
			legs := v.Add(v.NatDist.Apply(v.Pair.Apply(m, n)),
				v.NatDist.Apply(v.Pair.Apply(n, p))) // nat_dist(m,n) + nat_dist(n,p)
			a.Show(
				"dist(m,p) ≤ dist(m,n)+dist(n,p) ≤ q — the triangle inequality chained onto the hypothesis",
				By(legBound, At(DistTriangle, m, n, p), At(nat_order.LessEqTrans, dMP, legs, q)))
		}),
})}

// ---------------------------------------------------------------------------
// DistTrianglesLessEq — the triangle inequality with both endpoints perturbed
// ---------------------------------------------------------------------------

// DistTrianglesLessEq — perturbed triangle inequality: if each endpoint of
// the pair (m, p) sits within r (resp. s) of a reference point (n
// resp. q), the (m, p) metric is bounded by the reference metric plus
// the two tolerances. Two DistTriangle chains along m → n → q ← p:
//
//	dmp ≤ dmn + dnp DistTriangle at (m, p, n)
//	dnp ≤ dnq + dpq DistTriangle at (n, p, q) + DistSym
//	⇒ dmp ≤ r + (dnq + dpq) LessEqAdd2 with the r-hypothesis, trans
//	⇒ dmp ≤ r + (dnq + s) s-hypothesis lifted by LessEqAddCancel
//	 at prefix dnq, then at prefix r
//	 = dnq + (r + s) one AC-regroup (nat_arith.AddAssoc/arith.AddSym certs)
var DistTrianglesLessEq = distTrianglesLessEqThm{family.Add(registry.ProofEntry{
	Name: "DistTrianglesLessEq",
	Key:  "prop_70ba146301577822",
	// The tolerances are the antecedent, so every fact below is ground.
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p q r s:num.",
			Hypotheses: []string{
				"dist((m, n)) ≤ r",
				"dist((p, q)) ≤ s",
			},
			Conclusion: "dist((m, p)) ≤ dist((n, q)) + (r + s)",
		},
		func(a *Argument, m, n, p, q, r, s Term, tolerances Fact) {
			ctx := a.Ctx()
			v := ops(ctx)

			dMP := v.NatDist.Apply(v.Pair.Apply(m, p)) // the bounded metric
			dMN := v.NatDist.Apply(v.Pair.Apply(m, n)) // ≤ r by hypothesis
			dPQ := v.NatDist.Apply(v.Pair.Apply(p, q)) // ≤ s by hypothesis
			dNP := v.NatDist.Apply(v.Pair.Apply(n, p)) // the intermediate leg
			dNQ := v.NatDist.Apply(v.Pair.Apply(n, q)) // the reference metric
			refTol := v.Add(dNQ, dPQ)                  // dnq + dpq, before the s-lift

			a.Show(
				"dmp ≤ dmn+dnp ≤ r+(dnq+dpq) ≤ r+(dnq+s) = dnq+(r+s)",
				By(
					tolerances,
					// The two triangle legs m → n → p and n → q ← p (DistSym
					// flips nat_dist(q,p) onto the hypothesis form nat_dist(p,q)).
					At(DistTriangle, m, n, p),
					At(DistTriangle, n, q, p),
					At(DistSym, q, p),
					// dmn+dnp ≤ r+(dnq+dpq): the r-hypothesis on the left leg,
					// the flipped second triangle on the right.
					At(nat_order.LessEqAdd2, dMN, dNP, r, refTol),
					// Lift the s-hypothesis dpq ≤ s under the prefixes dnq, then r.
					At(nat_order.LessEqAddCancel, dNQ, dPQ, s),
					At(nat_order.LessEqAddCancel, r, refTol, v.Add(dNQ, s)),
					// regroup the majorant r+(dnq+s) onto the goal's own shape
					nat_arith.AddAC(ctx).Eq(
						v.Add(r, v.Add(dNQ, s)),
						v.Add(dNQ, v.Add(r, s))),
					At(nat_order.LessEqTrans, dMP, v.Add(dMN, dNP), v.Add(r, refTol)),
					At(nat_order.LessEqTrans, dMP, v.Add(r, refTol), v.Add(r, v.Add(dNQ, s))),
				))
		}),
})}

// ---------------------------------------------------------------------------
// Dist × mult distribution laws
// ---------------------------------------------------------------------------
//
// Dist × mult distribution laws: DistLeftMul (left) · DistRightMul
// (right; nat_arith.MulSym mirror). The workhorse is DistLeftMul — unfold dist on
// both sides, apply nat_arith.LeftAddDistrib + LeftSubDistrib to get the two
// halves matching.

// ---------------------------------------------------------------------------
// DistLeftMul — scaling two points scales the distance between them
// ---------------------------------------------------------------------------

// DistLeftMul — left-distributivity of * over the ℕ-metric dist. Unfold dist
// on both sides by citing the proved `Dist` entry (a declared Dep — this
// member never reaches for dist's ConstDef itself), then distribute *
// through the resulting (n-p) + (p-n) shape. One direct chain — no
// induction: three ground instances put the unfolds and the +-split
// on the page, and the final LeftSubDistrib rewrite closes at the
// cite.
var DistLeftMul = distLeftMulThm{family.Add(registry.ProofEntry{
	Name: "DistLeftMul",
	Key:  "prop_35ee50756042d5d4",
	Build: family.Theorem(
		"∀m n p:num. dist((m * n, m * p)) = m * dist((n, p))",
		func(a *Argument, m, n, p Term) {
			v := ops(a.Ctx())

			a.Do( // Unfold dist on both sides into (a - b) + (b - a) form.
				Cite(Dist, v.Mul(m, n), v.Mul(m, p)), // nat_dist((m₀n₀, m₀p₀)) = (m₀n₀ - m₀p₀) + (m₀p₀ - m₀n₀)
				Cite(Dist, n, p),                     // nat_dist((n₀, p₀)) = (n₀ - p₀) + (p₀ - n₀)
				// Split m₀·((n₀-p₀) + (p₀-n₀)) into the two products.
				Cite(nat_arith.LeftAddDistrib, m, v.Minus.Apply(n, p), v.Minus.Apply(p, n)),
				// Distribute m₀ through each monus — the rewrite closes the
				// residual equation at the cite.
				Cite(LeftSubDistrib),
			)
		}),
})}

// ---------------------------------------------------------------------------
// DistRightMul — the same scaling, with the factor on the other side
// ---------------------------------------------------------------------------

// DistRightMul — right-distributivity: the nat_arith.MulSym mirror of DistLeftMul. Because
// the CNF refuter does NOT thread nat_arith.MulSym's paramodulation through the
// `(_,_)` pair constructor (unlike its behavior on `+`, where the same
// mirror composition closes bare — cf. nat_arith.RightAddDistrib), we ground the
// four instances the argument needs up front — one of DistLeftMul, three
// of nat_arith.MulSym:
//
//	nat_dist((p*m, p*n)) = p * nat_dist((m, n)) [DistLeftMul @ (p, m, n)]
//	m*p = p*m [nat_arith.MulSym @ (m, p)]
//	n*p = p*n [nat_arith.MulSym @ (n, p)]
//	p * nat_dist((m, n)) = nat_dist((m, n)) * p [nat_arith.MulSym @ (p, nat_dist((m,n)))]
//
// With those four ground equations resident the refutation closes. No
// induction, no bridges — each instance rides in the premise list at
// its own witnesses.
var DistRightMul = distRightMulThm{family.Add(registry.ProofEntry{
	Name: "DistRightMul",
	Key:  "prop_a1504116d670de25",
	Build: family.Theorem(
		"∀m n p:num. dist((m * p, n * p)) = dist((m, n)) * p",
		func(a *Argument, m, n, p Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			// The outer nat_arith.MulSym instance needs the OPAQUE term nat_dist((m₀, n₀)) as
			// a witness — construct it programmatically from the two Skolems.
			distMN := v.NatDist.Apply(v.Pair.Apply(m, n))

			a.Do(By(
				// DistLeftMul @ (p, m, n): nat_dist((p₀*m₀, p₀*n₀)) = p₀*nat_dist((m₀, n₀)).
				At(DistLeftMul, p, m, n),
				// nat_arith.MulSym @ (m, p): m₀*p₀ = p₀*m₀ — pair-arg re-orient (LHS).
				At(nat_arith.MulSym, m, p),
				// nat_arith.MulSym @ (n, p): n₀*p₀ = p₀*n₀ — pair-arg re-orient (RHS).
				At(nat_arith.MulSym, n, p),
				// nat_arith.MulSym @ (p, nat_dist((m,n))): p₀*nat_dist((m₀,n₀)) = nat_dist((m₀,n₀))*p₀
				// — the outer product flip.
				At(nat_arith.MulSym, p, distMN),
			))
		}),
})}
