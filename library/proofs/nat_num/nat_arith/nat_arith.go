// nat_arith.go — the chapter: the arithmetic of ℕ.
//
// Eight parts, marked by banners:
//
// - Addition: where `+` comes from, and what it does on each side
// - The derived clauses and basic laws of +
// - Multiplication: where `*` comes from, and its laws
// - Exponentiation
// - The factorial
// - The primitive-recursion existence theorem for ℕ, in its
// polymorphic form, and dependent choice along ℕ
// - Distribution laws of * over + on num
// - The binary numeral encoding and its bridges to Peano structure

package nat_arith

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Addition: where `+` comes from, and what it does on each side
// ---------------------------------------------------------------------------
//
// `Add` DEFINES `+` by its two recursion clauses — the definition is
// the chapter's, compiled against peano.Recursion, the primitive
// recursion schema of ℕ.
//
// What the definition yields is the two LEFT-side clauses, projected out
// singly below (`AddLeftZeroClause`, `AddLeftSucClause`). The other two
// members are their RIGHT-side counterparts — `AddZero` and `AddSuc` —
// which the recursion does not give and which are each one induction on
// the recursed operand. Those four together are what every later law of
// `+` is built from; the laws themselves are in the part below.

// ---------------------------------------------------------------------------
// Add — the recursion equations of +
// ---------------------------------------------------------------------------

// Add — `+` defined: adding to zero is the identity, adding to a
// successor is the successor of the sum. Spelled `plus` in the
// equations, the operator having no head-position spelling.
var Add = addThm{family.Define(registry.DefEntry{
	Name:      "Add",
	Key:       "prop_8d1eb1111ebca901",
	Const:     "+",
	Spelled:   "plus",
	Type:      "num → num → num",
	Equations: []string{"∀n:num. plus(0, n) = n", "∀m n:num. plus(suc(m), n) = suc(plus(m, n))"},
})}

// ---------------------------------------------------------------------------
// AddLeftZeroClause · AddLeftSucClause — Add's two clauses, one apiece
// ---------------------------------------------------------------------------

// Add, Mul and NatPow each state TWO recursion clauses as one conjunction,
// and normalization merges the clauses' binders into a single install
// prefix. That prefix is not a reordering of anything the statement
// shows — it binds `m` and `n` across both clauses at once — so a
// ground cite of the pack is read POSITIONALLY against a prefix the
// file cannot display, and a consumer wanting ONE clause supplies a
// witness for the other clause's binder as well.
//
// The six entries below (this pair, and the * and exponentiation pairs) state
// each clause on its own, so a consumer cites the clause it actually
// uses, at that clause's own binders, in the order the statement shows.
// nat_order's LessEqZeroClause / LessEqSucClause solve the same problem for ≤ and
// < at that chapter's own floor.
//
// The names carry the recursion SLOT — `Left` for + and *, which
// recurse on their first argument, `Right` for nat_pow, which recurses on
// the exponent — because the chapter already states the OTHER side's
// laws under nearly the same words. `AddLeftZeroClause` (0 + n = n) is
// not `AddZero` (m + 0 = m); `mulLeftSucClause` (suc m · n = m·n + n)
// is not `MulSuc` (m · suc n = m + m·n). Those are different theorems
// with different proofs: the defining clauses recurse on the left,
// and the laws on the right each require an induction.
//
// Shared recipe (all six): bind the clause's own ∀-prefix and close by
// the pack. The install puts both clauses in scope and the close picks
// out the one this entry states — including in the zero clauses, where
// there is no disjunction to split.
//
// Band B: machine-derived projections of a row the chapter already
// exports — `Internal` entries, named lowerCamel unless cross-family
// fan-in earned one an exported name (AddLeftZeroClause and
// MulLeftZeroClause are the two that did).

// AddLeftZeroClause — Add's zero clause: 0 is a left identity.
var AddLeftZeroClause = addLeftZeroClauseThm{family.Add(registry.ProofEntry{
	Name: "AddLeftZeroClause",
	Key:  "prop_65c03807bf98c2cb",
	Build: family.Theorem("∀n:num. 0 + n = n",
		func(a *Argument, n Term) {
			a.Do(By(Add))
		}),
})}

// AddLeftSucClause — Add's successor clause: a successor in the left
// summand escapes the sum.
var AddLeftSucClause = addLeftSucClauseThm{family.Add(registry.ProofEntry{
	Name: "AddLeftSucClause",
	Key:  "prop_d3c4e38946564397",
	Build: family.Theorem("∀m n:num. suc(m) + n = suc(m + n)",
		func(a *Argument, m, n Term) {
			a.Do(By(Add))
		}),
})}

// ---------------------------------------------------------------------------
// AddZero — adding nothing on the right changes nothing
// ---------------------------------------------------------------------------

// AddZero — the right-side zero clause of +: 0 is a right identity.
// By induction on m from Add's two clauses — one induction:
//
//	base: 0 + 0 = 0 Add's zero clause 0 + n = n at n = 0 folds
//	 the LHS to 0
//	step: suc m + 0 = suc m Add's suc clause suc m + n = suc(m + n)
//	 at n = 0 rewrites the LHS to suc(m + 0);
//	 the IH m + 0 = m identifies suc(m + 0)
//	 with suc m
//
// Both leaves cite Add as a resident hyp and close by refutation. Add
// is a conjunction, so one cite puts both recursion clauses in scope;
// the base leaf needs the zero clause at n = 0, the step leaf the same
// clause together with its IH.
var AddZero = addZeroThm{family.Add(registry.ProofEntry{
	Name: "AddZero",
	Simp: true,
	Key:  "prop_bdab6326259f3ff0",
	// Induct on m — the goal's binder stays bound.
	Build: family.Theorem("∀m:num. m + 0 = m",
		func(a *Argument) {
			// Add is a sequent-form conjunction of both clauses, so the same
			// cite serves each branch — it installs the clause that branch
			// rewrites with.
			a.Induct("m")
			a.Base(
				"0 + 0 = 0 — Add's zero clause folds the LHS at n = 0",
				By(Add),
			)
			a.Step(
				"suc m + 0 = suc m — Add's suc clause rewrites LHS to suc(m + 0); the IH m + 0 = m closes it",
				func(b *Argument, ih Fact) {
					b.Show(
						"Add's suc clause opens the LHS and the IH closes the residue",
						By(Normalized, Add, ih))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// AddSuc — a successor in the right summand escapes the sum
// ---------------------------------------------------------------------------

// AddSuc — the right-side successor clause of +: suc commutes with the
// right summand. By induction on m from Add's two left clauses — one
// induction:
//
//	base: ⊢ ∀n. 0 + suc n = suc(0 + n) Add's zero clause 0+x = x
//	 folds both sides to suc n
//	step: IH ⊢ ∀n. suc m + suc n = suc(suc m + n) Add's suc clause
//	 suc x + y = suc(x + y)
//	 rewrites LHS to suc(m + suc n)
//	 and RHS to suc(suc(m + n));
//	 the IH m + suc n = suc(m + n)
//	 identifies them under suc
//
// Both leaves cite Add as a resident hyp and close by refutation, one
// cite putting both recursion clauses in scope. At the base the clauses
// apply at n and both sides collapse to suc n; at the step they apply
// at n and, with the IH, both sides collapse to the same suc-of-suc
// term.
var AddSuc = addSucThm{family.Add(registry.ProofEntry{
	Name: "AddSuc",
	Key:  "prop_4cbb21c4d4b09112",
	// Induct on m — ∀n stays in each leaf.
	Build: family.Theorem("∀m n:num. m + suc(n) = suc(m + n)",
		func(a *Argument) {
			a.Induct("m")
			a.Base(
				"∀n. 0 + suc n = suc(0 + n) — Add's zero clause collapses both sides to suc n",
				By(Normalized, Add),
			)
			a.Step(
				"Add's suc clause rewrites both sides to suc-of-suc; the IH identifies them under suc",
				func(b *Argument, ih Fact) {
					b.Show(
						"Add's suc clause opens both sides and the IH identifies them under the common suc",
						By(Add, ih))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// The derived clauses and basic laws of +
// ---------------------------------------------------------------------------
//
// The derived clauses and basic laws of + on num close with
// cancellation in equations — the general form, and then the degenerate
// one where the sum equals one of its own summands.

// ---------------------------------------------------------------------------
// AddAssoc — ⊢ ∀m n p. m + (n + p) = (m + n) + p
// ---------------------------------------------------------------------------

// AddAssoc — associativity of + on num, by induction on the first
// summand.
//
// The mathematics is just two clauses of Add's recursion, plus one
// induction on m:
//
//	0 + n = n (Add, zero clause)
//	suc m + n = suc(m + n) (Add, successor clause)
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name: "AddAssoc",
	Key:  "prop_5ae355304538196a",
	// The induction's base and step each cite exactly the clause it needs,
	// so both branches are one cite over a stated fact. The right-side laws
	// AddZero and AddSuc recurse on the OTHER argument: separate
	// statements, each carrying its own induction, and not substitutes for
	// these two.
	Build: family.Theorem("∀m n p:num. m + (n + p) = m + n + p",
		func(a *Argument) {
			a.Induct("m")
			a.Base(
				"0+(n+p) and (0+n)+p both reduce to n+p via Add's zero clause",
				StripQuant(),
				Cite(AddLeftZeroClause),
			)
			a.Step(
				"Add's successor clause brings suc outside both "+
					"sides, and the hypothesis identifies what is under it",
				StripQuant(),
				Cite(AddLeftSucClause),
				CnfRefute(),
			)
		}),
})}

// ---------------------------------------------------------------------------
// AddSym — the order of two summands does not matter
// ---------------------------------------------------------------------------

// AddSym — commutativity of + on num, by induction on m from Add's two
// left clauses plus the two right-side siblings AddZero + AddSuc:
//
//	base: ⊢ ∀n. 0 + n = n + 0 Add's zero clause reduces LHS
//	 to n; AddZero (n = n + 0) folds n
//	 into the RHS
//	step: IH ⊢ ∀n. suc m + n = n + suc m
//	 Add's suc clause rewrites LHS to
//	 suc(m + n); AddSuc rewrites RHS to
//	 suc(n + m); the IH m + n = n + m
//	 identifies them under suc
var AddSym = addSymThm{family.Add(registry.ProofEntry{
	Name: "AddSym",
	Key:  "prop_db75c36bf81c6d32",
	// Induct on m — ∀n stays in each leaf. Each branch cites Add (both left
	// clauses as a conjunction) plus the matching right-side sibling, and
	// closes on those clauses at the leaf's own atoms.
	Build: family.Theorem("∀m n:num. m + n = n + m",
		func(a *Argument) {
			a.Induct("m")
			a.Base(
				"∀n. 0 + n = n + 0 — Add's zero clause reduces LHS to n; AddZero folds n into n + 0",
				By(Normalized, Add, AddZero),
			)
			a.Step(
				"suc m + n = suc(m+n) (Add) = suc(n+m) (IH under suc) = n + suc m (AddSuc)",
				func(b *Argument, ih Fact) {
					b.Show(
						"Add's suc clause on the left, AddSuc on the right, the IH under the common suc",
						By(ih, Add, AddSuc))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// AddClauses — zero and successor read against either argument of +
// ---------------------------------------------------------------------------

// AddClauses — the four-clause simplification pack for +: both
// recursion directions of both arguments in one cite. Pure
// re-packaging of the three direct sources, one conjunct at a time:
// Add supplies the two left-side clauses, AddZero the right identity,
// AddSuc the right successor.
var AddClauses = addClausesThm{family.Add(registry.ProofEntry{
	Name: "AddClauses",
	Key:  "prop_d4f6b1ffc87dc5a9",
	// The conjunction splits down its right spine, so each clause is
	// discharged by the single source that states it.
	Build: family.Theorem(
		"(∀n:num. 0 + n = n) ∧ "+
			"((∀m:num. m + 0 = m) ∧ "+
			"    ((∀m n:num. suc(m) + n = suc(m + n)) ∧ (∀m n:num. m + suc(n) = suc(m + n))))",
		func(a *Argument) {
			a.Do(SplitConj(
				Case(
					"0 + n = n — Add's left zero clause",
					By(Add),
				),
				Case(
					"the three remaining clauses",
					SplitConj(
						Case(
							"m + 0 = m — AddZero",
							Cite(AddZero),
						),
						Case(
							"the two successor clauses",
							SplitConj(
								Case(
									"suc m + n = suc(m + n) — Add's left successor clause",
									By(Add),
								),
								Case(
									"m + suc n = suc(m + n) — AddSuc",
									Cite(AddSuc),
								),
							),
						),
					),
				),
			))
		}),
})}

// ---------------------------------------------------------------------------
// AddEqZero — zero has only the trivial decomposition as a sum
// ---------------------------------------------------------------------------

// AddEqZero — zero is indecomposable in addition: if m + n = 0, both are 0.
// By induction on m from Add's two clauses + suc_not_zero — one induction:
//
//	base: 0 + n = 0 ⇔ 0 = 0 ∧ n = 0 Add's zero clause folds
//	 0 + n → n, and both sides
//	 collapse to n = 0
//	step: suc m + n = 0 ⇔ suc m = 0 ∧ n = 0 Add's suc clause
//	 rewrites LHS to suc(m + n) = 0,
//	 which suc_not_zero refutes; suc_not_zero
//	 also refutes suc m = 0, so both
//	 sides are ⊥
//
// The IH is unused — the step's contradiction is elementary.
var AddEqZero = addEqZeroThm{family.Add(registry.ProofEntry{
	Name: "AddEqZero",
	Key:  "prop_7cbd147e3c2f4b69",
	// Induct on m; the step strips ∀n and grounds the successor clause at
	// (m, n₀), leaving the refuter to find suc_not_zero's own grounding.
	Build: family.Theorem("∀m n:num. m + n = 0 ⇔ m = 0 ∧ n = 0",
		func(a *Argument) {
			// m stays bound (the induction variable); StripQuant on ∀n
			// produces "n_0" (printed as n₀).
			m := a.Binder("m")
			n0 := Var("n_0", NumType)
			a.Induct(m)
			a.Base(
				"Add's zero clause folds 0 + n to n; both sides ⇔ (n = "+
					"0), and the cite's rewrite pass closes the leaf itself",
				Cite(AddLeftZeroClause),
			)
			a.Step(
				"Add's suc clause folds suc m + n to suc(m + n); suc_not_zero refutes both LHS and (suc m = 0)",
				StripQuant(),
				By(At(AddLeftSucClause, m, n0), peano.SucNotZero),
			)
		}),
})}

// ---------------------------------------------------------------------------
// AddEqLCancel — addition is cancellative
// ---------------------------------------------------------------------------

// AddEqLCancel — left cancellation for + in equations: equal left
// summands may be cancelled. Induction on m, the summand being
// cancelled; both leaves keep n, p ∀-bound and have Add's two
// ∀-clauses installed as resident hyps.
//
// One induction:
//
//	base: ⊢ ∀n p. (0 + n = 0 + p) ⇔ (n = p) Add's zero clause
//	 0 + x = x reduces the
//	 left side to (n = p)
//	step: IH ⊢ ∀n p. (suc m + n = suc m + p) ⇔ (n = p) Add's suc
//	 clause suc x + y =
//	 suc(x + y) rewrites both
//	 summands under suc;
//	 suc_injective unpeels the suc;
//	 the IH closes the residue
//
// The base leaf closes at Add's cite: the zero clause applies at n = 0
// and both sides collapse to (n = p). The step leaf needs suc_injective
// additionally — its cite installs the suc-elimination bridge as a
// resident hyp — and closes on Add's suc clause, suc_injective and the IH
// together, as the step row above sets out.
var AddEqLCancel = addEqLCancelThm{family.Add(registry.ProofEntry{
	Name: "AddEqLCancel",
	Key:  "prop_4382eddadc872132",
	// The closure binds NOTHING: induction needs m still bound, so the
	// statement's binders stay where they are and the body names the
	// induction variable instead.
	Build: family.Theorem("∀m n p:num. m + n = m + p ⇔ n = p",
		func(a *Argument) {
			a.Induct("m")
			a.Base(
				"0 + n = 0 + p reduces to n = p via Add's zero clause",
				By(Normalized, Add),
			)
			a.Step(
				"Add's suc clause rewrites both sides under suc; suc_injective + IH close the residue",
				func(b *Argument, ih Fact) {
					b.Show(
						"suc(m)+n = suc(m+n) on both sides; suc_injective strips the suc and the IH closes",
						By(ih, Add, peano.SucInjective))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// AddEqSelfLeft · AddEqSelfRight — a sum that equals one of its summands
// ---------------------------------------------------------------------------

// A sum can equal a summand only by adding nothing: `m + n = m` forces
// n = 0, and `m + n = n` forces m = 0. The two are the degenerate case
// of cancellation — cancel the repeated summand and what remains is
// the other one against 0 — so each is one step from AddEqLCancel,
// and neither needs an induction of its own.

// AddEqSelfLeft — a sum equals its LEFT summand exactly when the right
// one is zero. Rewrite the right-hand m as m + 0 (AddZero) and the
// statement is cancellation of the common m:
//
//	m + n = m ⇔ m + n = m + 0 ⇔ n = 0
var AddEqSelfLeft = addEqSelfLeftThm{family.Add(registry.ProofEntry{
	Name: "AddEqSelfLeft",
	Key:  "prop_34d9d7673344fb64",
	Build: family.Theorem("∀m n:num. m + n = m ⇔ n = 0",
		func(a *Argument, m, n Term) {
			zero := ops(a.Ctx()).Zero
			a.Do(By(
				Normalized,
				At(AddZero, m),               // m + 0 = m
				At(AddEqLCancel, m, n, zero), // m + n = m + 0 ⇔ n = 0
			))
		}),
})}

// AddEqSelfRight — a sum equals its RIGHT summand exactly when the left
// one is zero. Commuting the sum turns the statement into its left-hand
// sibling at the swapped pair:
//
//	m + n = n ⇔ n + m = n ⇔ m = 0
var AddEqSelfRight = addEqSelfRightThm{family.Add(registry.ProofEntry{
	Name: "AddEqSelfRight",
	Key:  "prop_4b9b08c9d2ca7ad8",
	Build: family.Theorem("∀m n:num. m + n = n ⇔ m = 0",
		func(a *Argument, m, n Term) {
			a.Do(By(
				Normalized,
				At(AddSym, m, n),        // m + n = n + m
				At(AddEqSelfLeft, n, m), // n + m = n ⇔ m = 0
			))
		}),
})}

// ---------------------------------------------------------------------------
// Multiplication: where `*` comes from, and its laws
// ---------------------------------------------------------------------------
//
// The definitional half first, then the derived laws that stand on it.
//
// `Mul` DEFINES `*` by its two recursion clauses, as `Add` defines `+`,
// compiled against peano.Recursion; the recursion runs on the LEFT
// operand. Only the clause pair differs:
//
// 	Add: 0 + n = n, suc m + n = suc(m + n)
// 	Mul: 0 * n = 0, suc m * n = m * n + n
//
// `MulZero` and `MulSuc` are the two right-side projections that pair
// with the left-side clauses Mul states. Both are single inductions on m
// (as AddZero/AddSuc above are), but Mul's suc clause `suc m * n =
// m*n + n` puts a `+ n` on the RHS that Add's `suc m + n = suc(m + n)`
// doesn't — so both Mul-side projections carry extra +-family deps
// (MulZero picks up AddZero to collapse `+ 0`; MulSuc runs a two-level
// Trans bridge citing Add / AddSuc / AddAssoc to reassociate).
//
// The derived laws follow: the unit laws (`OneMul`, `MulOne`), the
// six-clause simplification pack that repackages them (`MulClauses` —
// the go-to rewrite set for Mul in a single cite), commutativity
// (`MulSym`), associativity (`MulAssoc`), and left-cancellation in
// equations (`MulEqLCancel`), the multiplicative twin of
// AddEqLCancel above.

// ---------------------------------------------------------------------------
// Mul — the recursion equations of *
// ---------------------------------------------------------------------------

// Mul — `*` defined: zero times anything is zero, a successor times n
// adds one more n. Spelled `times` in the equations.
var Mul = mulThm{family.Define(registry.DefEntry{
	Name:      "Mul",
	Key:       "prop_39cd7c83170479ac",
	Const:     "*",
	Spelled:   "times",
	Type:      "num → num → num",
	Equations: []string{"∀n:num. times(0, n) = 0", "∀m n:num. times(suc(m), n) = times(m, n) + n"},
	Deps:      []registry.EntryLike{Add},
})}

// ---------------------------------------------------------------------------
// MulLeftZeroClause · mulLeftSucClause — Mul's two clauses, one apiece
// ---------------------------------------------------------------------------

// Add's twin projections, for *. Why the six exist, why the names say
// which argument the recursion runs on, and the shared
// close-by-the-pack recipe: the addition part, above AddLeftZeroClause.
//
// Read these against the right-side pair below them, which they are
// NOT: MulLeftZeroClause is 0 · n = 0, MulZero is m · 0 = 0;
// mulLeftSucClause is suc m · n = m·n + n, MulSuc is m · suc n =
// m + m·n. The left clauses are Mul's definition, the right ones
// each cost an induction.

// MulLeftZeroClause — Mul's zero clause: 0 annihilates on the left.
var MulLeftZeroClause = mulLeftZeroClauseThm{family.Add(registry.ProofEntry{
	Name: "MulLeftZeroClause",
	Key:  "prop_afa2681f84242f83",
	Build: family.Theorem("∀n:num. 0 * n = 0",
		func(a *Argument, n Term) {
			a.Do(By(Mul))
		}),
})}

// mulLeftSucClause — Mul's successor clause: one more copy of the right
// factor per successor on the left.
var mulLeftSucClause = mulLeftSucClauseThm{family.Add(registry.ProofEntry{
	Name: "mulLeftSucClause",
	Key:  "prop_c79c78292af2d591",
	Build: family.Theorem("∀m n:num. suc(m) * n = m * n + n",
		func(a *Argument, m, n Term) {
			a.Do(By(Mul))
		}),
})}

// ---------------------------------------------------------------------------
// MulZero — zero on the right absorbs any factor
// ---------------------------------------------------------------------------

// MulZero — the right-side zero clause of *: any m annihilates on 0.
// By induction on m from Mul's two clauses plus AddZero — one
// induction:
//
//	base: 0 * 0 = 0 Mul's zero clause 0 * n = 0 at n = 0 folds
//	 the LHS to 0
//	step: suc m * 0 = 0 Mul's suc clause suc m * n = m * n + n at
//	 n = 0 rewrites the LHS to m*0 + 0; AddZero's
//	 m + 0 = m (grounded at m*0) collapses m*0 + 0
//	 to m*0; the IH m*0 = 0 closes it
//
// Both leaves cite Mul — a conjunction — as a resident hyp and refute.
// The step case additionally cites AddZero to eliminate the trailing
// `+ 0` residual (Mul's suc clause is the arithmetic step written so
// the recursion index is on the RIGHT of the sum, so the m*n side
// carries a spurious `+ n` that becomes `+ 0` at n = 0 and needs
// AddZero to disappear — this is the sole per-step departure from
// AddZero's own structure).
var MulZero = mulZeroThm{family.Add(registry.ProofEntry{
	Name: "MulZero",
	Simp: true,
	Key:  "prop_7c79be931ec6d39b",
	// Induct on m — the goal's binder stays bound.
	Build: family.Theorem("∀m:num. m * 0 = 0",
		func(a *Argument) {
			// Both leaves cite the whole pack rather than the clause
			// projections defined above them, and that is deliberate: a leaf
			// that closes by refutation meets the entire context, so it
			// selects the clause it needs without being handed one. A leaf
			// that GROUNDS is the case that wants a projection.
			a.Induct("m")
			a.Base(
				"0 * 0 = 0 — Mul's zero clause folds the LHS at n = 0",
				By(Mul),
			)
			a.Step(
				"suc m * 0 = 0 — Mul's suc clause rewrites LHS to m*0 "+
					"+ 0; AddZero collapses the +0; IH m*0 = 0 closes it",
				func(b *Argument, ih Fact) {
					b.Show(
						"Mul's suc clause opens the LHS to m*0 + 0, AddZero "+
							"drops the trailing 0, and the IH closes the residue",
						By(Normalized, Mul, AddZero, ih))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// MulSuc — multiplication as repeated addition, read on the right factor
// ---------------------------------------------------------------------------

// MulSuc — the right-side successor clause of *: expanding a successor
// in the right factor adds one copy of m. By induction on m from Mul's
// two left clauses; the step case additionally reassociates a
// suc-of-plus chain via Add's clauses, AddSuc, and AddAssoc:
//
//	base: ⊢ ∀n. 0 * suc n = 0 + 0 * n Mul's zero clause zeroes
//	 LHS (0 * suc n = 0) and the
//	 inner 0*n on the RHS; Add's
//	 zero clause folds 0 + 0 to 0
//	step: IH ⊢ ∀n. suc m * suc n = suc m + suc m * n
//	 Mul's suc clause rewrites LHS to m*suc n + suc n and, on
//	 the RHS, suc m * n to m*n + n; the IH identifies m*suc n
//	 with m + m*n; AddAssoc + AddSuc carry
//	 (m + m*n) + suc n to suc(m + (m*n + n));
//	 Add's suc clause folds RHS's
//	 suc m + (m*n + n) into the same suc-of-sum.
//
// Unlike AddSuc (whose step case closes via Add + refute alone because
// suc commutes trivially with Add's suc clause), Mul's suc clause
// exposes an extra `+ n` factor on the RHS that must be re-threaded
// through the sum. The proof shape is: a single bridge
// suc(m + (m*n₀ + n₀)) splits the step's equality into two halves each
// closable by the refuter, with a further sub-bridge
// (m + m*n₀) + suc n₀ on the harder LHS half so the CNF matcher never
// needs to chain more than a few paramodulations per leaf.
var MulSuc = mulSucThm{family.Add(registry.ProofEntry{
	Name: "MulSuc",
	Key:  "prop_404b4440c26a3475",
	// Induct on m — ∀n stays in each leaf. The step case strips ∀n₀ and
	// drives the equality through a suc-of-sum bridge; the two Trans levels
	// keep each refute leaf's paramodulation depth small.
	Build: family.Theorem("∀m n:num. m * suc(n) = m + m * n",
		func(a *Argument) {
			ctx := a.Ctx()

			// m is the induction variable, so it stays bound; n₀ is the
			// Skolem the step case strips from ∀n — declared here so the
			// bridges below can name it.
			m := a.Binder("m")
			ctx.Var("n_0", NumType)

			// Bridges for the step case: the LHS/RHS meeting point, and the
			// LHS-half sub-split.
			outerBridge := ctx.TermText("suc(m + (m * n₀ + n₀))")
			innerBridge := ctx.TermText("(m + m * n₀) + suc(n₀)")

			a.Induct(m)
			a.Base(
				"∀n. 0 * suc n = 0 + 0 * n — Mul's zero clause "+
					"zeroes both sides; Add's zero clause folds 0 + 0 to 0",
				By(Normalized, Mul, Add),
			)
			a.Step(
				// The step case hands over the induction hypothesis
				"IH ⊢ ∀n. suc m * suc n = suc m + suc m * n — bridge through suc(m + (m*n₀ + n₀))",
				// ∀n. m * suc n = m + m*n; the first leg is where it lands.
				func(b *Argument, ih Fact) {
					b.Do(StripQuant())
					// suc m * suc n₀ = (m + m*n₀) + suc n₀
					// = suc(m + (m*n₀ + n₀))
					// = suc m + suc m * n₀
					b.Do(CalcEq(
						Leg(
							innerBridge,
							"Mul's suc clause then IH",
							By(ih, Mul)),
						Leg(
							outerBridge,
							"AddAssoc reshuffles, then AddSuc absorbs the suc into the inner sum",
							By(AddAssoc, AddSuc)),
						FinalLeg(
							"Mul's suc unfolds suc m * n₀; Add's suc clause folds suc m + · into suc(m + ·)",
							By(Mul, Add)),
					))
				},
			)
		}),
})}

// ===========================================================================
// The derived laws of * — everything below stands on the definition above
// ===========================================================================

// ---------------------------------------------------------------------------
// OneMul · MulOne — 1 is a unit for *, on either side
// ---------------------------------------------------------------------------

// OneMul / MulOne — the two unit laws of multiplication, stated apart
// from the MulClauses pack: they exist so that a proof consuming ONE
// unit law cites that law at its own binder, instead of grounding the
// whole six-clause pack's merged ∀-prefix — the pack's install prefix re-binds names its
// statement binds per clause, so no statement-order witness map exists
// for it (TestWitnessOrderCensus [witness-unmapped]) and a ground cite
// of the pack pays six positional witnesses for one clause.
//
// Each law is one pass through *'s recursion: 1 is suc(0), so the
// product unfolds once and a +-identity absorbs what is left.
//
// Both are chapter API by cross-family fan-in, which is what earns an
// exported name: nat_order.LessEqSelfMul cites MulOne, and
// nat_div_mod's DivRefl and ModRefl cite OneMul.
var OneMul = oneMulThm{family.Add(registry.ProofEntry{
	Name: "OneMul",
	Simp: true,
	Key:  "prop_9df1e0cc1b88dfc3",
	Build: family.Theorem("∀n:num. 1 * n = n",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			a.Show(
				"suc(0)·n₀ unfolds to 0·n₀ + n₀, and 0·n₀ is 0, so the sum is 0 + n₀ = n₀",
				By(
					At(mulLeftSucClause, v.Zero, n), // suc(0)*n₀ = 0*n₀ + n₀
					At(MulLeftZeroClause, n),        // 0 = 0*n₀
					At(AddLeftZeroClause, n),        // n₀ = 0 + n₀
					OneIsSucZero,                    // 1 = suc(0)
				))
		}),
})}

var MulOne = mulOneThm{family.Add(registry.ProofEntry{
	Name: "MulOne",
	Simp: true,
	Key:  "prop_f43f2e93ef433c05",
	Build: family.Theorem("∀m:num. m * 1 = m",
		func(a *Argument, m Term) {
			v := ops(a.Ctx())
			a.Show(
				"m₀·suc(0) unfolds to m₀ + m₀·0, and m₀·0 is 0, so the sum is m₀ + 0 = m₀",
				By(
					At(MulSuc, m, v.Zero), // m₀*suc(0) = m₀ + m₀*0
					At(MulZero, m),        // 0 = m₀*0
					At(AddZero, m),        // m₀ = m₀ + 0
					OneIsSucZero,          // 1 = suc(0)
				))
		}),
})}

// ---------------------------------------------------------------------------
// MulClauses — zero, one and successor read against either factor of *
// ---------------------------------------------------------------------------

// MulClauses — the six-clause simplification pack for *: the go-to
// rewrite set for Mul in one cite. Pure re-packaging of the direct
// sources, one conjunct at a time (AddClauses parity): Mul's
// conjunction states the two left clauses (0*n = 0 and
// suc(m)*n = m*n + n), MulZero states m*0 = 0, MulSuc states
// m*suc(n) = m + m*n, and the two unit conjuncts are OneMul and
// MulOne. Splits the conjunction flat with SplitConjAll so each
// conjunct's cite set is minimal.
var MulClauses = mulClausesThm{family.Add(registry.ProofEntry{
	Name: "MulClauses",
	Key:  "prop_5244641d0891d276",
	// Each conjunct binds its own variables, so there is no ∀-prefix to strip:
	// flat-split the six-way conjunction and cite per leaf. The four leaves
	// that ARE a dep's statement (m*0 = 0 matching MulZero; 1*n = n and
	// m*1 = m matching the unit laws; m*suc(n) = m + m*n matching MulSuc)
	// close on the cite alone. The leaves citing a multi-conjunct clause
	// PACK (Mul) close by the pack, which selects the right conjunct.
	Build: family.Theorem(
		"(∀n:num. 0 * n = 0) ∧ "+
			"((∀m:num. m * 0 = 0) ∧ "+
			"    ((∀n:num. 1 * n = n) ∧ "+
			"        ((∀m:num. m * 1 = m) ∧ "+
			"            ((∀m n:num. suc(m) * n = m * n + n) ∧ (∀m n:num. m * suc(n) = m + m * n)))))",
		func(a *Argument) {
			mulS := a.Ctx().DepNormalized(MulSuc)

			a.Do(SplitConjAll(
				Case(
					"0*n = 0 — Mul's left-zero clause",
					By(Mul),
				),
				Case(
					"m*0 = 0 — MulZero's statement (identity-shape close)",
					Cite(MulZero),
				),
				Case(
					"1*n = n — OneMul's statement (identity-shape close)",
					Cite(OneMul),
				),
				Case(
					"m*1 = m — MulOne's statement (identity-shape close)",
					Cite(MulOne),
				),
				Case(
					"suc(m)*n = m*n + n — Mul's left-suc clause",
					By(Mul),
				),
				// This leaf IS MulSuc, binders and all, so it is a pure
				// cache-close; a preserving install has nothing to rewrite
				// here and fails.
				Case(
					"m*suc(n) = m + m*n — MulSuc's statement verbatim",
					CiteKnown(mulS),
				),
			))
		}),
})}

// ---------------------------------------------------------------------------
// MulSym — the order of two factors does not matter
// ---------------------------------------------------------------------------

// MulSym — commutativity of * on num, by induction on m. Mirrors AddSym
// with one structural upgrade: Mul's suc clause `suc m * n = m*n + n`
// leaves a `+ n` residue that Add's suc clause doesn't, so the step
// case must re-thread the equality through a +-bridge (AddSym does the
// re-threading; the CnfRefute matcher then only chains a handful of
// paramodulations per leaf):
//
//	base: ⊢ ∀n. 0 * n = n * 0 Mul's zero clause folds LHS
//	 (0 * n = 0); MulZero is exactly
//	 (0 = n * 0) up to renaming and
//	 closes the residual by α-match
//	step: IH ⊢ ∀n. suc m * n = n * suc m
//	 Mul's suc rewrites LHS to m*n + n;
//	 MulSuc rewrites RHS to n + n*m;
//	 the IH swaps m*n ↔ n*m so both
//	 sides meet at n + m*n; AddSym
//	 supplies the +-commutation the
//	 refuter needs to close each half
//
// The step splits via `Trans(n₀ + m*n₀)` into LHS = bridge and
// bridge = RHS — one bridge, two leaves, where MulSuc's step needs a
// three-leg CalcEq over two bridges (no inner sub-split needed here
// since AddSym is already resident).
var MulSym = mulSymThm{family.Add(registry.ProofEntry{
	Name: "MulSym",
	Key:  "prop_4b12272f28f2d0c9",
	// Induct on m — ∀n stays in each leaf. Step case strips ∀n₀ and drives
	// the equality through the +-bridge n₀ + m*n₀ so each refute leaf's
	// paramodulation depth stays small.
	Build: family.Theorem("∀m n:num. m * n = n * m",
		func(a *Argument) {
			ctx := a.Ctx()

			// m is the induction variable, so it stays bound; n₀ is the
			// Skolem the step case strips from ∀n — declared here so the
			// bridge below can name it.
			m := a.Binder("m")
			ctx.Var("n_0", NumType)

			// LHS/RHS meeting point for the step case.
			bridge := ctx.TermText("n₀ + m * n₀")

			a.Induct(m)
			a.Base(
				"∀n. 0 * n = n * 0 — Mul's zero clause folds LHS to 0; MulZero folds RHS to 0; refuter closes",
				By(Normalized, Mul, MulZero),
			)
			a.Step(
				"IH ⊢ ∀n. suc m * n = n * suc m — bridge through n₀ + m*n₀",
				Cite(Mul),
				Cite(MulSuc),
				Cite(AddSym),
				StripQuant(),
				Expect(Trans(bridge),
					Case(
						"LHS half: suc m * n₀ = n₀ + m*n₀ — Mul's suc unfolds "+
							"suc m * n₀ to m*n₀ + n₀; AddSym flips to n₀ + m*n₀",
						CnfRefute(),
					),
					Case(
						"RHS half: n₀ + m*n₀ = n₀ * suc m — IH swaps m*n₀ ↔ n₀*m; MulSuc folds n₀ + n₀*m into n₀ * suc m",
						CnfRefute(),
					),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// MulAssoc — bracketing a triple product does not matter
// ---------------------------------------------------------------------------

// MulAssoc — associativity of * on num, by induction on the first
// factor. The mathematics is Mul's two recursion clauses plus
// right-distributivity of * over +:
//
//	base: ⊢ ∀n p. 0*(n*p) = (0*n)*p
//	 Mul's zero clause folds both sides to 0
//	 (LHS in one step; RHS through 0*n → 0,
//	 then 0*p → 0).
//
//	step: IH ⊢ ∀n p. suc m*(n*p) = (suc m*n)*p
//	 Mul's suc clause unfolds both sides:
//	 LHS → m*(n*p) + n*p, and the IH swaps
//	 m*(n*p) ↔ (m*n)*p;
//	 RHS → (m*n + n)*p, and RightAddDistrib spreads it
//	 to (m*n)*p + n*p.
//	 Both sides meet at (m*n)*p + n*p — the Trans bridge.
//
// The step's two bridge halves need DIFFERENT cite sets (LHS: Mul +
// IH; RHS: RightAddDistrib + Mul), so the cites live per-leaf rather
// than up-front as in MulSym — a resident RightAddDistrib on the LHS
// half poisons its refutation past the CNF budget.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name: "MulAssoc",
	Key:  "prop_6276909ee77f9b6f",
	// Induct on m — the step case strips ∀n∀p and drives through the
	// +-bridge (m*n₀)*p₀ + n₀*p₀.
	Build: family.Theorem(
		"∀m n p:num. m * (n * p) = m * n * p",
		func(a *Argument) {
			ctx := a.Ctx()

			// m is the induction variable, so it stays bound; n₀ / p₀ are the
			// Skolems the step case strips from ∀n∀p — declared here so the
			// bridge below can name them.
			m := a.Binder("m")
			ctx.Var("n_0", NumType)
			ctx.Var("p_0", NumType)

			// Where the step's two sides meet.
			bridge := ctx.TermText("m * n₀ * p₀ + n₀ * p₀")

			a.Induct(m)
			a.Base(
				"0*(n*p) = (0*n)*p — Mul's zero clause folds both sides "+
					"to 0; the cite's rewrite pass closes the leaf itself",
				Cite(MulLeftZeroClause),
			)
			a.Step(
				"IH ⊢ suc m*(n*p) = (suc m*n)*p — bridge through (m*n₀)*p₀ + n₀*p₀",
				StripQuant(),
				Expect(Trans(bridge),
					Case(
						"LHS half: Mul's suc unfolds suc m*(n₀*p₀) to m*(n₀*p₀) + n₀*p₀; IH swaps m*(n₀*p₀) into (m*n₀)*p₀",
						Cite(mulLeftSucClause),
						CnfRefute(),
					),
					Case(
						"RHS half: RightAddDistrib gathers (m*n₀)*p₀ + n₀*p₀ into (m*n₀ "+
							"+ n₀)*p₀; Mul's suc folds the sum into suc m*n₀ at the cite",
						Cite(RightAddDistrib),
						Cite(mulLeftSucClause),
					),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// MulEqLCancel — multiplication is cancellative away from zero
// ---------------------------------------------------------------------------

// MulEqLCancel — left cancellation for multiplication, with the zero
// factor retained as an alternative. Cases on m separate the zero
// factor. For a successor factor, induction on n and cases on p
// reduce the successor products to a common sum; AddEqLCancel and
// successor injectivity leave exactly the induction hypothesis.
var MulEqLCancel = mulEqLCancelThm{family.Add(registry.ProofEntry{
	Name: "MulEqLCancel",
	Key:  "prop_b2783501d026ac75",
	Build: family.Theorem(
		"∀m n p:num. m * n = m * p ⇔ m = 0 ∨ n = p",
		func(a *Argument, m *Expr[Nat]) {
			v := ops(a.Ctx())
			a.Do(peano.Cases.At(m).SplitDisj(
				LeftHolds(
					"m = 0: both products are zero",
					Given(func(b *Argument, zero Fact) {
						b.Do(zero.Rw())
						b.Show(
							"the zero factor makes both sides true",
							By(MulLeftZeroClause))
					})),
				RightHolds(
					"m is a successor: induction on the right factor n",
					Given(func(b *Argument, successor Fact) {
						k, mSuc := b.UnpackAs[Nat](successor, "k")
						b.Do(mSuc.Rw())
						sucM := v.Suc(k.Core())
						n := b.Binder("n")
						b.Induct(n)
						b.Base(
							"n = 0: the other right factor must be zero",
							By(Normalized, MulZero, MulEqZero, peano.SucNotZero))
						b.Step(
							"n is a successor: distinguish zero and successor for p",
							func(c *Argument, ih Fact) {
								p := c.FixAs[Nat]()
								c.Do(peano.Cases.At(p).SplitDisj(
									LeftHolds(
										"p = 0: a product of successors is not zero",
										Given(func(d *Argument, zero Fact) {
											d.Do(zero.Rw())
											d.Show(
												"both sides are false",
												By(MulZero, peano.SucNotZero, MulEqZero))
										})),
									RightHolds(
										"p is a successor: cancel the common summand and apply the induction hypothesis",
										Given(func(d *Argument, successor Fact) {
											q, pSuc := d.UnpackAs[Nat](successor, "q")
											d.Do(pSuc.Rw())
											d.Show(
												"the predecessors satisfy the induction hypothesis",
												By(
													ih.At(q),
													At(MulSuc, sucM, n),
													At(MulSuc, sucM, q),
													At(AddEqLCancel, sucM, v.Mul(sucM, n), v.Mul(sucM, q.Core())),
													peano.SucInjective))
										})),
								))
							})
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Exponentiation
// ---------------------------------------------------------------------------
//
// exponentiation: where `nat_pow` comes from, its powers at a fixed slot, and
// the three exponent laws.
//
// The part reads in dependency order: the definition, then the laws that
// need no exponent arithmetic, then the homomorphism laws that do.
//
// **The definition.** `NatPow` defines exponentiation by its two
// recursion clauses, as `Add` and `Mul` are defined. Its recursion runs
// on the RIGHT operand, the exponent, where theirs runs on the left.
//
// **The fixed-slot powers** — OnePow · ZeroPow · PowOne · PowTwo ·
// PowEqZero · PowTwoNonzero · PowTwoSuc.
// Four of them pin one slot of the power at a numeral and read the
// answer off NatPow's clauses — the base at 1, the base at 0, the exponent
// at 1 and at 2 — the fifth asks when a power vanishes at all, and the
// last two read the answers at base 2: a power of two is nonzero, and
// the next power of two is the doubled one. `PowOne` and `PowTwo` are
// the two whose numeral must become a successor to meet NatPow's step
// clause (`OneIsSucZero`, `Two`) — the base-2 pair also spend `Two`,
// but on the base; `PowEqZero`'s numeral fact is a different one,
// `OneNotZero`, about the value a zeroth power takes. The first five
// either induct on the exponent or compute without induction, settling
// each branch against one of NatPow's clauses plus one fact about
// multiplication — or, for `PowTwo`, the power one exponent below it;
// the base-2 pair are single computations over the members above them.
//
// **The exponent laws** — PowAdd · MulPowDistrib · PowPow.
// Exponentiation as a homomorphism, read three ways: a sum in the
// exponent becomes a product of powers, a product of bases becomes a
// product of powers, and a product in the exponent becomes an iterated
// power. All three induct on an exponent, and in the first two the whole
// content of the step is one AC regroup of the factors NatPow's step clause
// sheds — the two sides differ only in where a spare factor sits.
//
// PowPow is the tier above, since it splits its compound exponent with
// PowAdd. Its choice of induction variable is what keeps it out of the
// AC business entirely: inducting on the OUTER exponent lands both spare
// factors on the same side.
//
// Every member here is exported (Band A) except the two clause
// projections of the definition.

// ---------------------------------------------------------------------------
// NatPow — the recursion equations of exponentiation
// ---------------------------------------------------------------------------

// NatPow — exponentiation defined: the zeroth power is 1, and each
// further power multiplies by the base. The recursion runs on the
// EXPONENT, the second argument.
//
// `*` occurs in the step clause as an uninterpreted symbol — no
// property of multiplication is used; Mul is a dependency as the
// definition of the constant the clause mentions, which is also what
// orders the mints at package init. Mul's `+` is the same.
var NatPow = natPowThm{family.Define(registry.DefEntry{
	Name:  "NatPow",
	Key:   "prop_da6ea6addda591f0",
	Const: "nat_pow",
	Type:  "num → num → num",
	Equations: []string{
		"∀m:num. nat_pow(m, 0) = 1",
		"∀m n:num. nat_pow(m, suc(n)) = m * nat_pow(m, n)",
	},
	Deps: []registry.EntryLike{Mul},
})}

// ---------------------------------------------------------------------------
// powRightZeroClause · powRightSucClause — NatPow's two clauses, one apiece
// ---------------------------------------------------------------------------

// The + and * projections' twin, for nat_pow. Why the six exist and the
// shared close-by-the-pack recipe: the addition part, above AddLeftZeroClause.
//
// `Right` here is the exponent — nat_pow recurses on its second argument,
// where + and * recurse on their first. The slot marker is what keeps
// these names honest against the chapter's base/exponent convention
// (README §"One caution"): powRightZeroClause is m⁰ = 1, the exponent
// pinned to zero. The law with the BASE pinned to zero is ZeroPow
// (0ⁿ), a different theorem — and the only one in the chapter whose
// value is not uniform.
//
// The zero clause never reads the exponent and the successor clause
// never reads it either — mⁿ⁺¹ = m · mⁿ names the base and the previous
// power only — so each entry binds exactly the variables its equation
// mentions.

// powRightZeroClause — NatPow's zero clause: the empty product is 1,
// whatever the base.
var powRightZeroClause = powRightZeroClauseThm{family.Add(registry.ProofEntry{
	Name: "powRightZeroClause",
	Key:  "prop_642d25979591b45f",
	Build: family.Theorem("∀m:num. nat_pow(m, 0) = 1",
		func(a *Argument, m Term) {
			a.Do(By(NatPow))
		}),
})}

// powRightSucClause — NatPow's successor clause: one more factor of the
// base per successor in the exponent.
var powRightSucClause = powRightSucClauseThm{family.Add(registry.ProofEntry{
	Name: "powRightSucClause",
	Key:  "prop_71b21bb7872a892e",
	Build: family.Theorem("∀m n:num. nat_pow(m, suc(n)) = m * nat_pow(m, n)",
		func(a *Argument, m, n Term) {
			a.Do(By(NatPow))
		}),
})}

// ===========================================================================
// The powers of a fixed base or exponent — no exponent arithmetic yet
// ===========================================================================

// ---------------------------------------------------------------------------
// OnePow — every power of the base 1 is 1
// ---------------------------------------------------------------------------

// OnePow — by induction on the exponent. NatPow's two clauses drive one
// case each: the zero clause is the base case at base 1, and the step
// clause opens 1ⁿ⁺¹ as 1 · 1ⁿ, where the induction hypothesis collapses
// the power and 1 · 1 = 1 finishes.
//
// That last equation is all the argument knows about multiplication —
// 1 is a unit for it — and MulOne is the unit law it instantiates. No
// numeral bookkeeping is needed here, unlike sibling PowOne: the 1 in
// this statement is a BASE, so it never has to become suc 0 to meet
// NatPow's step clause.
var OnePow = onePowThm{family.Add(registry.ProofEntry{
	Name: "OnePow",
	Key:  "prop_428915b047168ce",
	Build: family.Theorem("∀n:num. nat_pow(1, n) = 1",
		func(a *Argument) {
			one := a.Ctx().Numeral(1)
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"NatPow's zero clause reads 1⁰ = 1 at base 1",
				By(powRightZeroClause),
			)
			a.Step(
				"NatPow's step clause opens 1ⁿ⁺¹ as 1 · 1ⁿ",
				func(b *Argument, ih Fact) {
					unit := b.Have(
						"1 is a unit for ·",
						"1 * 1 = 1",
						By(MulOne))
					b.Show(
						"1ⁿ⁺¹ = 1 · 1ⁿ = 1 · 1 = 1",
						By(
							Normalized,
							At(powRightSucClause, one, n), // 1 · 1ⁿ = 1^suc n
							ih,
							unit))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// ZeroPow — the powers of the base 0, the one exponentiation law whose
// value is not uniform
// ---------------------------------------------------------------------------

// ZeroPow — the empty product is 1 whatever it is a product of, while
// every longer product of zeroes is 0. That is why the statement
// carries a COND, and why the proof settles the exponent's shape rather
// than computing a single value:
//
//	exponent 0 the condition holds, so the COND is 1 — and NatPow's
//	 zero clause at base 0 says exactly that
//	exponent suc n NatPow's step clause opens the power into 0 · 0ⁿ,
//	 which Mul's left-zero clause collapses to 0; the
//	 condition is false (suc_not_zero), so the COND is 0 too
//
// Its cites mirror NatPow's two clause projections plus the successor-vs-zero
// discrimination the condition needs. `MulLeftZeroClause` rather than
// the `MulClauses` pack: the only multiplication fact used is that one
// clause, so citing the six-conjunct pack would install five unused
// conjuncts.
var ZeroPow = zeroPowThm{family.Add(registry.ProofEntry{
	Name: "ZeroPow",
	Key:  "prop_ab0abd81e8365079",
	// The induction is num's case split here: the two branches are computed
	// independently and the step never reads its hypothesis.
	Build: family.Theorem("∀n:num. nat_pow(0, n) = COND(n = 0, 1, 0)",
		func(a *Argument) {
			v := ops(a.Ctx())
			zero := v.Zero

			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"the condition 0 = 0 holds, so the COND is its "+
					"then-branch 1 — which is NatPow's zero clause at base 0",
				By(powRightZeroClause),
			)
			a.Step(
				"suc n ≠ 0 sends the COND to its else-branch 0, and NatPow "+
					"opens 0^suc n into 0 · 0ⁿ, which the left-zero clause collapses",
				// Fires as a goal rewrite, resolving the COND's condition:
				// ↦ nat_pow(0, suc n) = 0.
				Cite(peano.SucNotZero),
				By(
					At(powRightSucClause, zero, n), // 0 · 0ⁿ = 0^suc n
					MulLeftZeroClause,
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// PowOne — the first power of a base is that base
// ---------------------------------------------------------------------------

// PowOne — direct computation, no induction: the exponent 1 is a
// successor, so NatPow's step clause fires exactly once, and the recursion
// it exposes bottoms out immediately in NatPow's zero clause — leaving a
// product with 1 that multiplication's right identity finishes:
//
//	m¹ = m^suc 0 = m · m⁰ = m · 1 = m
//
// The two middle links are the two halves of ONE ground instance of
// NatPow, at base m and exponent 0. The outer two are numeral bookkeeping
// (ONE — unlike sibling OnePow, the numeral here is an EXPONENT and so
// must become suc 0 to meet NatPow's step clause) and multiplication's
// right unit law (MulOne, which states m · 1 = m outright where Mul's
// own clauses would first have to reach the numeral).
var PowOne = powOneThm{family.Add(registry.ProofEntry{
	Name: "PowOne",
	Key:  "prop_b5005fb3ede82fe2",
	Build: family.Theorem("∀m:num. nat_pow(m, 1) = m",
		func(a *Argument, m Term) {
			v := ops(a.Ctx())
			a.Show(
				"NatPow's step clause at exponent suc 0 gives m₀ · "+
					"m₀⁰, its zero clause gives m₀⁰ = 1, and m₀ · 1 is m₀",
				By(
					Normalized,
					// OneIsSucZero turns the numeral exponent into a successor —
					// the shape NatPow's step clause matches against.
					OneIsSucZero,
					At(powRightZeroClause, m),        // m₀⁰ = 1
					At(powRightSucClause, m, v.Zero), // m₀ · m₀⁰ = m₀^suc 0
					At(MulOne, m),                    // m₀ · 1 = m₀
				))
		}),
})}

// ---------------------------------------------------------------------------
// PowTwo — the square of a base is the base times itself
// ---------------------------------------------------------------------------

// PowTwo — direct computation, no induction: the shape of PowOne above,
// one exponent up. The exponent 2 is a successor, so NatPow's step clause
// fires once and exposes the first power, which PowOne reads as the
// base itself:
//
//	m² = m^suc 1 = m · m¹ = m · m
//
// Each link is one rewrite of the goal: the numeral bridge Two turns
// the exponent into a successor, NatPow's step clause opens the successor
// power as a product, and PowOne collapses the first power — leaving
// m · m on both sides. The recursion stops at the first power, so
// neither NatPow's zero clause nor a unit law of multiplication enters,
// where PowOne needed both; and a computation by rewriting has no
// refutation to record.
var PowTwo = powTwoThm{family.Add(registry.ProofEntry{
	Name: "PowTwo",
	Key:  "prop_9b806db05e5eabba",
	Build: family.Theorem("∀m:num. nat_pow(m, 2) = m * m",
		func(a *Argument, m Term) {
			a.Show(
				"rewrite the exponent 2 to suc 1, open m₀^suc 1 as m₀ · "+
					"m₀¹ by NatPow's step clause, and read m₀¹ as m₀ by PowOne",
				Simp(
					Fwd(Two),               // 2 ↦ suc(1)
					Fwd(powRightSucClause), // m₀^suc 1 ↦ m₀ · m₀¹
					Fwd(PowOne),            // m₀¹ ↦ m₀
				),
				TrivialNormalized(), // the residual m₀ · m₀ = m₀ · m₀ is reflexive
			)
		}),
})}

// ---------------------------------------------------------------------------
// PowEqZero — a power vanishes exactly when its base does and its
// exponent does not
// ---------------------------------------------------------------------------

// PowEqZero — by induction on the exponent. The two branches are
// qualitatively different arguments, not two halves of one:
//
//	base n = 0: neither side survives, and two false sides make a
//	 true ⇔. NatPow's zero clause collapses the left-hand side to 1 = 0,
//	 refuted by the `1 ≠ 0` claim below; the right-hand side asks for
//	 0 ≠ 0 and refutes itself.
//
//	step n → suc n: NatPow's step clause presents the power as a product,
//	 and MulEqZero turns its vanishing into a disjunction — the
//	 `split` claim below, the one place the two operations meet. The
//	 induction hypothesis identifies the second disjunct with
//	 `m = 0 ∧ n ≠ 0`, so BOTH disjuncts deliver m = 0, and on the
//	 other side suc n ≠ 0 holds outright by suc_not_zero.
//
// So the exponent's VALUE never enters the step — only its successor
// shape — and the induction hypothesis is spent on a single disjunct.
var PowEqZero = powEqZeroThm{family.Add(registry.ProofEntry{
	Name: "PowEqZero",
	Key:  "prop_3cba2225dd87d06d",
	// Induct on the exponent n. The other binder stays bound as well, so
	// the step can fix it and cite NatPow at the ground instance its product
	// is stated over.
	Build: family.Theorem(
		"∀m n:num. nat_pow(m, n) = 0 ⇔ m = 0 ∧ n ≠ 0",
		func(a *Argument) {
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"n = 0: both sides are false — the right on 0 ≠ 0, the left because a zeroth power is 1",
				// The clause is bare here: the base is still ∀-bound in this
				// branch, so there is no ground instance to cite it at.
				By(OneNotZero, powRightZeroClause),
			)
			a.Step(
				"n → suc n: the successor power is a product, so MulEqZero "+
					"splits its vanishing and the IH reads the second factor",
				func(b *Argument, ih Fact) {
					m := b.Fix()

					split := b.Have(
						"NatPow's step clause exposes a product; MulEqZero is that product's zero test",
						"nat_pow(m₀, suc(n)) = 0 ⇔ m₀ = 0 ∨ nat_pow(m₀, n) = 0",
						Cite(powRightSucClause, m, n), // m₀ · m₀ⁿ = m₀^suc n
						// Consumed by the eq-rewrite path along that equation,
						// so it stays bare — witnesses are refused here.
						Cite(MulEqZero),
					)
					b.Show(
						"the IH at m₀ turns the right disjunct into m₀ = 0, which "+
							"the left disjunct already is; suc_not_zero settles suc n ≠ 0",
						By(Normalized, split, ih.At(m), peano.SucNotZero))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// PowTwoNonzero — a power of two is nonzero
// ---------------------------------------------------------------------------

// PowTwoNonzero — the corpus's one home for "a power of two is
// nonzero". PowEqZero above says a power vanishes only with its base,
// and the base here is no zero, being a successor (Two +
// peano.SucNotZero). A consumer bounding a value against a power of
// two cites this fact instead of respelling that ladder.
var PowTwoNonzero = powTwoNonzeroThm{family.Add(registry.ProofEntry{
	Name: "PowTwoNonzero",
	Key:  "prop_d02639749f0b14bc",
	Build: family.Theorem("∀n:num. nat_pow(2, n) ≠ 0",
		func(a *Argument) {
			a.Show(
				"a power vanishes only with its base, and 2 is a successor",
				By(Normalized, PowEqZero, Two, peano.SucNotZero))
		}),
})}

// ---------------------------------------------------------------------------
// PowTwoSuc — the doubled power is the next power up
// ---------------------------------------------------------------------------

// PowTwoSuc — the additive reading of nat_pow's step clause at base 2.
// Stated with + rather than 2·(·) so a consumer's bound argument (the
// bit-window bounds and doubling steps of the words chapters) can
// finish on it without reopening multiplication.
var PowTwoSuc = powTwoSucThm{family.Add(registry.ProofEntry{
	Name: "PowTwoSuc",
	Key:  "prop_af69cc66c39de306",
	Build: family.Theorem("∀n:num. nat_pow(2, n) + nat_pow(2, n) = nat_pow(2, suc(n))",
		func(a *Argument, n Term) {
			ctx := a.Ctx()
			one := ctx.Numeral(1)
			two := ctx.Numeral(2)
			powN := ops(ctx).NatPow.Apply(two, n) // 2ⁿ
			a.Show(
				"the next power is 2·2ⁿ, two is suc(1), and a successor factor unfolds to the sum",
				By(
					At(powRightSucClause, two, n), // 2^suc(n) = 2 · 2ⁿ
					At(MulSym, two, powN),         // 2 · 2ⁿ = 2ⁿ · 2
					Two,                           // 2 = suc(1)
					At(MulSuc, powN, one),         // 2ⁿ · suc(1) = 2ⁿ + 2ⁿ·1
					At(MulOne, powN),              // 2ⁿ · 1 = 2ⁿ
				))
		}),
})}

// ===========================================================================
// The three exponent laws — nat_pow as a homomorphism
// ===========================================================================

// ---------------------------------------------------------------------------
// PowAdd — splitting a compound exponent into a product of powers
// ---------------------------------------------------------------------------

// PowAdd — by induction on the exponent added on the right. Each branch
// pairs one clause of NatPow with the matching clause of +:
//
//	base p = 0: the right summand and the right factor vanish together
//	 — AddZero leaves the exponent as n, NatPow's zero clause turns the
//	 spare power into 1, and 1 is a unit for · (MulOne).
//
//	step p → suc p: AddSuc reads n + suc p as suc(n + p), so NatPow's step
//	 clause opens the left side as m · mⁿ⁺ᵖ, where the induction
//	 hypothesis reads mⁿ⁺ᵖ as mⁿ · mᵖ; the SAME clause opens the right
//	 side as mⁿ · (m · mᵖ). The two sides are the same three factors
//	 and differ only in where the spare m sits, so one AC regroup
//	 finishes — and that regroup is the whole content of the step.
var PowAdd = powAddThm{family.Add(registry.ProofEntry{
	Name: "PowAdd",
	Key:  "prop_2cef9c7bdb59e0e9",
	// All three binders arrive as parameters; the induction then runs on p,
	// the only one the recursion moves.
	Build: family.Theorem(
		"∀m n p:num. nat_pow(m, n + p) = nat_pow(m, n) * nat_pow(m, p)",
		func(a *Argument, m, n, p Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			mN := v.NatPow.Apply(m, n) // mⁿ — a spectator to the recursion
			mP := v.NatPow.Apply(m, p) // mᵖ

			// The step's two sides, once their powers are opened: the same
			// three factors, differing only in where the spare m sits.
			spareOutside := v.Mul(m, v.Mul(mN, mP)) // m · (mⁿ · mᵖ)
			spareInside := v.Mul(mN, v.Mul(m, mP))  // mⁿ · (m · mᵖ)

			a.Induct(p)
			a.Base(
				"p = 0: n + 0 is n, m⁰ is 1, and 1 is a unit for ·",
				// Each fires as a goal rewrite — the zero clause folds
				// m₀⁰ to 1, AddZero folds n₀ + 0, MulOne folds the
				// trailing · 1 — so none carries a witness.
				By(powRightZeroClause, AddZero, MulOne),
			)
			a.Step(
				"p → suc p: the successor exposes a spare factor m₀ "+
					"on each side, sitting in a different place on each",
				func(b *Argument, ih Fact) {
					b.Show(
						"AddSuc lands the exponent on suc(n₀+p₀), NatPow's step clause "+
							"opens both powers, and the regroup identifies what is left",
						By(
							At(AddSuc, n, p),                      // suc(n₀ + p₀) = n₀ + suc p₀
							At(powRightSucClause, m, v.Add(n, p)), // m₀ · m₀ⁿ⁺ᵖ = m₀^suc(n₀+p₀)
							ih,
							// carry the spare m₀ across mⁿ
							MulAC(ctx).Eq(spareOutside, spareInside),
							powRightSucClause,
						))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// MulPowDistrib — a power of a product is the product of the powers
// ---------------------------------------------------------------------------

// MulPowDistrib — by induction on the exponent. NatPow's zero clause makes
// the base case an identity between three copies of 1, held together by
// 1 · 1 = 1.
//
// The step carries the content. NatPow's step clause sheds one factor of
// the base from each of the three powers, so the two sides of the goal
// become two bracketings of the SAME four factors — the two bases and
// the two p-th powers, which the induction hypothesis has already
// identified:
//
//	(m·n) · (mᵖ·nᵖ) versus (m·mᵖ) · (n·nᵖ)
//
// Nothing but associativity and commutativity of · separates those two,
// so one AC regroup finishes — the same shape PowAdd's step takes, and
// the whole difficulty of both theorems.
//
// Note this is the sub-chapter's one statement with TWO bases, so `n`
// here is a base rather than an exponent — everywhere else in the
// chapter `n` and `p` are exponents.
var MulPowDistrib = mulPowDistribThm{family.Add(registry.ProofEntry{
	Name: "MulPowDistrib",
	Key:  "prop_8ce72860dd0e4fb6",
	// All three binders arrive as parameters; the induction then runs on p,
	// the only one the recursion moves.
	Build: family.Theorem(
		"∀m n p:num. nat_pow(m * n, p) = nat_pow(m, p) * nat_pow(n, p)",
		func(a *Argument, m, n, p Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			mn := v.Mul(m, n)          // the product base
			mP := v.NatPow.Apply(m, p) // mᵖ
			nP := v.NatPow.Apply(n, p) // nᵖ

			// The step's two sides, once their powers are opened: the same
			// four factors, bracketed base-with-base or base-with-its-power.
			bases := v.Mul(mn, v.Mul(mP, nP))            // (m·n) · (mᵖ·nᵖ)
			perBase := v.Mul(v.Mul(m, mP), v.Mul(n, nP)) // (m·mᵖ) · (n·nᵖ)

			a.Induct(p)
			a.Base(
				"p = 0: 1 is a unit for ·, and one install of the zero clause reads all three powers as 1",
				By(MulOne, powRightZeroClause),
			)
			a.Step(
				"p → suc p: each power sheds one factor of its base, and the four factors regroup",
				func(b *Argument, ih Fact) {
					b.Show(
						"NatPow's step clause opens all three powers, the IH reads (m₀·n₀)ᵖ "+
							"as m₀ᵖ·n₀ᵖ, and the regroup crosses to the other bracketing",
						By(
							Normalized,
							At(powRightSucClause, mn, p), // (m₀·n₀) · (m₀·n₀)ᵖ = (m₀·n₀)^suc p₀
							At(powRightSucClause, m, p),  // m₀ · m₀ᵖ = m₀^suc p₀
							At(powRightSucClause, n, p),  // n₀ · n₀ᵖ = n₀^suc p₀
							ih,
							// pair each base with its own power instead of
							// with the other base
							MulAC(ctx).Eq(bases, perBase)))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// PowPow — a product in the exponent is a power of a power
// ---------------------------------------------------------------------------

// PowPow — by induction on p, the OUTER exponent: the one that counts
// how many times the power mⁿ is taken, with the base m and the inner
// exponent n fixed throughout.
//
//	base p = 0: MulZero collapses the exponent to 0, and NatPow's zero
//	 clause then reads each side as 1 — once at the base m, once at
//	 the base mⁿ.
//
//	step p → suc p: both sides shed the SAME spare factor mⁿ, and both
//	 shed it on the LEFT. On the right that is one move: NatPow's step
//	 clause peels (mⁿ)^suc p as mⁿ · (mⁿ)ᵖ. On the left it takes two,
//	 and the orientation is what makes them line up — MulSuc reads
//	 n · suc p as n + n·p, putting the new copy of n leftmost in the
//	 sum, so PowAdd splits m^(n + n·p) as mⁿ · m^(n·p) with the new
//	 copy of mⁿ leftmost in the product. What remains of the two
//	 sides is m^(n·p) against (mⁿ)ᵖ, which is the induction
//	 hypothesis verbatim.
//
// Because both spare factors land on the same side, no commutation of
// · is used anywhere. That is what the choice of induction variable
// buys: inducting on the INNER exponent n instead lands them on
// OPPOSITE sides and costs the crossing twice over — MulPowDistrib to
// collect the two p-th powers under a single base, then MulSym to
// commute that base. Neither is a dependency here.
var PowPow = powPowThm{family.Add(registry.ProofEntry{
	Name: "PowPow",
	Key:  "prop_2ae2caaee531e2b6",
	// All three binders arrive as parameters; the induction then runs on p.
	Build: family.Theorem(
		"∀m n p:num. nat_pow(m, n * p) = nat_pow(nat_pow(m, n), p)",
		func(a *Argument, m, n, p Term) {
			v := ops(a.Ctx())

			mN := v.NatPow.Apply(m, n) // mⁿ — the base the right-hand side is a power of

			a.Induct(p)
			a.Base(
				"p = 0: the exponent collapses and both sides are a zeroth power",
				By(
					// n₀ · 0 ↦ 0 in the goal's exponent: MulZero fires as a
					// goal rewrite, so it carries no witness.
					MulZero,
					// and the zero clause folds both zeroth powers at once.
					powRightZeroClause,
				),
			)
			a.Step(
				"p → suc p: both sides shed one spare factor mⁿ, and what is left is the induction hypothesis",
				func(b *Argument, ih Fact) {
					b.Show(
						"MulSuc puts the new n₀ leftmost in the sum, so PowAdd peels "+
							"mⁿ off the left — where NatPow peels it on the other side",
						By(
							At(MulSuc, n, p),              // n₀ · suc p₀ = n₀ + n₀·p₀
							At(PowAdd, m, n, v.Mul(n, p)), // mⁿ · m₀^(n₀·p₀) = m₀^(n₀ + n₀·p₀)
							ih,
							At(powRightSucClause, mN, p), // mⁿ · (mⁿ)^p₀ = (mⁿ)^suc p₀
						))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// The factorial
// ---------------------------------------------------------------------------
//
// factorial is the chapter's fourth operation and the one of the four that
// takes a single argument. It is also the only one of the four whose
// step reads the recursion INDEX: `+`, `*` and `nat_pow` each build their
// successor clause out of the previous value alone; factorial multiplies it
// by the successor of the index — `factorial(suc n) = suc n · factorial n`, the
// new argument itself.
//
// What the chapter says about factorial is the equations and the one law
// that does not need the order: n! ≠ 0, which is FactorialNonzero
// below and joins AddEqZero, MulEqZero and PowEqZero as the fourth
// operation's vanishing criterion. Where the chapter stops is
// the order — 0 < n!, 1 ≤ n! and the monotonicity of the factorial are
// order facts, and nat_arith sits below the order.

// ---------------------------------------------------------------------------
// Factorial — the recursion equations of factorial
// ---------------------------------------------------------------------------

// Factorial — factorial defined: the empty product is 1, and n! multiplies
// (n-1)! by n.
var Factorial = factorialThm{family.Define(registry.DefEntry{
	Name:      "Factorial",
	Key:       "prop_e49ddd47f8c8e362",
	Const:     "factorial",
	Type:      "num → num",
	Equations: []string{"factorial(0) = 1", "∀n:num. factorial(suc(n)) = suc(n) * factorial(n)"},
	Deps:      []registry.EntryLike{Mul},
})}

// ---------------------------------------------------------------------------
// FactorialNonzero — a factorial is nonzero
// ---------------------------------------------------------------------------

// FactorialNonzero — the chapter's other vanishing criteria (AddEqZero,
// MulEqZero, PowEqZero) each say WHEN a value is zero; the factorial has
// no such case at all. By induction on n. The empty product is 1, and 1
// is not 0; the successor factorial is the product suc(n) · n!, which
// MulEqZero lets vanish only through a factor, and neither factor does —
// the left one is a successor, the right one is the induction
// hypothesis.
var FactorialNonzero = factorialNonzeroThm{family.Add(registry.ProofEntry{
	Name: "FactorialNonzero",
	Key:  "prop_2fe652226e52f61a",
	// Induct on n, which therefore stays bound rather than arriving as a
	// closure parameter.
	Build: family.Theorem("∀n:num. factorial(n) ≠ 0",
		func(a *Argument) {
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"n = 0: the empty product is 1, and 1 is not 0",
				By(Factorial, OneNotZero))
			a.Step(
				"n → suc n: the successor factorial is a product, and neither of its factors vanishes",
				func(b *Argument, ih Fact) {
					b.Show(
						"a product vanishes only through a factor; no successor "+
							"is zero, and the induction hypothesis rules out the other",
						By(ih, Factorial, MulEqZero, peano.SucNotZero))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The primitive-recursion existence theorem for ℕ, in its polymorphic form,
// and dependent choice along ℕ
// ---------------------------------------------------------------------------
//
// the primitive-recursion existence theorem for ℕ, in its polymorphic
// form: for every result type A, every step function f : A → num → A, and
// every base value e : A, there exists an fn : num → A satisfying fn(0) =
// e and fn(suc n) = f(fn n, n).
//
// This is peano.Recursion's ∃!-form weakened to plain ∃: what a proof
// cites when it needs a function on ℕ to exist and has no use for its
// uniqueness — real_sequences.ClusterPointSubsequence builds its index
// map σ from it. The chapter's own operations do not pass through it:
// each is defined by its clauses, which the definition door compiles
// against peano.Recursion itself.
//
// Dependent choice iterates a step that is only known to exist: choice
// picks a successor of each state, and the recursion runs on the pick.

// ---------------------------------------------------------------------------
// PrimRecursion — a base value and a step function determine a
// function on ℕ (at every result type A)
// ---------------------------------------------------------------------------

var PrimRecursion = primRecursionThm{family.Add(registry.ProofEntry{
	Name: "PrimRecursion",
	Key:  "prop_962683188b82ab49",
	// The proof: peano.Recursion's ∃! at (f, e), normalized to its
	// existence half, is the claim up to the order of its clauses.
	Build: family.Theorem(
		"∀f:(A → num → A). ∀e:A. ∃fn:(num → A). ∀n:num. e = fn(0) ∧ fn(suc(n)) = f(fn(n), n)",
		func(a *Argument, f, e Term) {
			a.Do(By(Normalized, At(peano.Recursion, f, e)))
		}),
})}

// ---------------------------------------------------------------------------
// DependentChoice — a sequence chosen term by term along ℕ (at every state
// type A)
// ---------------------------------------------------------------------------

// DependentChoice — dependent choice along ℕ: if a start s satisfies the
// invariant G at 0, and every state satisfying G at n has a successor
// satisfying G at n + 1 and linked to it by L at n, then some sequence
// starting at s satisfies G at every n and links each term to the next by
// L. Choice picks a successor of each state, PrimRecursion iterates the
// pick from s, and induction carries G along the sequence.
var DependentChoice = dependentChoiceThm{family.Add(registry.ProofEntry{
	Name: "DependentChoice",
	Key:  "prop_b55c065a3f3dc99d",
	Build: family.Theorem(Statement{
		Binders: "∀G:(num → A → bool). ∀L:(num → A → A → bool). ∀s:A.",
		Hypotheses: []string{
			"G(0, s)",
			"∀n:num. ∀h:A. G(n, h) ⇒ ∃k:A. G(n + 1, k) ∧ L(n, h, k)",
		},
		Conclusion: "∃g:(num → A). g(0) = s ∧ (∀n:num. G(n, g(n)) ∧ L(n, g(n), g(n + 1)))",
	},
		func(a *Argument, G *Arrow2[Nat, A, Bool], L *Expr[Fun3[Nat, A, A, Bool]], s *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"the initial state satisfies G",
				"each valid state has a valid next state")
			initial, next := parts[0], parts[1]
			phi, phiDef := a.LetAs[Fun2[A, Nat, A]]("phi", "λh:A. λn:num. εk:A. G(n + 1, k) ∧ L(n, h, k)")
			choice := a.Have(
				"the chosen next state satisfies its invariant and adjacent relation",
				"∀n:num. ∀h:A. G(n, h) ⇒ G(n + 1, phi(h, n)) ∧ L(n, h, phi(h, n))",
				Derive(func(b *Argument) {
					n, h := b.FixAs[Nat]("n"), b.FixAs[A]("h")
					good := b.Assume()
					b.Do(phiDef.Rw())
					b.Show(
						"choice selects a witness of the next-state existence",
						By(HilbertDenoted, next.At(n, h), good))
				}))
			g, recursion := a.UnpackAs[Fun[Nat, A]](PrimRecursion.At(phi, s), "g")
			valid := a.Have(
				"every recursively constructed state satisfies the invariant",
				"∀n:num. G(n, g(n))",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"the recursion starts at the valid initial state",
						By(Normalized, recursion.At(b.TermAs[Nat]("0")), initial))
					b.Step(
						"the chosen successor preserves validity",
						func(c *Argument, ih Fact) {
							n := c.TermAs[Nat]("n")
							c.Show(
								"the next-state choice preserves G at the recursive successor",
								By(Normalized, choice.At(n, c.TermAs[A]("g(n)")), recursion.At(n), ih, Add1.At(n)))
						})
				}))
			adjacent := a.Have(
				"the recursion read at n + 1",
				"∀n:num. g(n + 1) = phi(g(n), n)",
				By(recursion, Add1))
			a.Take(g)
			a.Show(
				"the recursive sequence starts at s and satisfies the invariant and every adjacent relation",
				SplitConj(
					Case(
						"the initial value is s",
						By(recursion.At(a.TermAs[Nat]("0")))),
					Case(
						"each term satisfies G and is linked to the next by L",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]()
							b.Show(
								"the valid state and chosen successor satisfy L",
								By(Normalized, choice.At(n, b.TermAs[A]("g(n)")), valid.At(n), adjacent.At(n)))
						}))))
		}),
})}

// ---------------------------------------------------------------------------
// Distribution laws of * over + on num
// ---------------------------------------------------------------------------
//
// distribution laws of * over + on num, plus the indecomposability of the
// two multiplicative constants:
//
// LeftAddDistrib — m * (n + p) = m*n + m*p, induction on n
// with a two-level Trans-bridge through the
// +-reassociation.
// RightAddDistrib — (m + n) * p = m*p + n*p, MulSym-mirror of
// LeftAddDistrib (no induction needed).
// MulEqZero — zero/successor cases on both factors; two successors
// have a successor product, which cannot be zero.
// MulEqOne — the same cases; the successor-product equation reduces
// to both predecessors being zero.

// ---------------------------------------------------------------------------
// LeftAddDistrib — a factor spreads across the terms of a sum
// ---------------------------------------------------------------------------

// LeftAddDistrib — left-distributivity of * over + on num, by
// induction on the middle variable n. The mathematics is one clause
// each from Add and Mul in each direction, plus AddAssoc to
// re-associate the +-chain that appears in the step:
//
//	base: ⊢ m * (0 + p) = m*0 + m*p
//	 Add's zero clause 0 + p = p folds LHS to
//	 m*p; MulZero (0 = m*0) closes the residual
//	 by identity-shape α-match.
//
//	step: IH ⊢ m*(suc n + p) = m*suc n + m*p
//	 Add's suc clause suc(n) + p = suc(n + p) peels suc out
//	 of the +-sum on the LHS; MulSuc rewrites both
//	 m*suc(n+p) (LHS, after the peel) and m*suc(n) (RHS)
//	 into m + m*(·); the IH identifies the two m*(n+p)
//	 copies; AddAssoc reassociates the +-chain
//	 m + (m*n + m*p) ↔ (m + m*n) + m*p.
//
// The step drives the equality through a two-level bridge, keeping
// each CnfRefute leaf a few paramodulations deep:
//
//	outer: m*(suc n + p) = m + (m*n + m*p) = m*suc n + m*p
//	inner (on the RHS half of the outer):
//	 m + (m*n + m*p) = (m + m*n) + m*p = m*suc n + m*p
//
// Unlike Mul-side inductions where the +-residue from Mul's
// left-suc clause (m*n + n) forces an extra +-family cite, this
// proof's STEP stays inside the right-suc family: MulSuc is its sole
// Mul-side rewriter (the base's is MulZero), and its two
// applications (one per side) both
// fold `m*suc(·)` — the shape that Add's suc-peel produces on the
// LHS matches the shape the RHS's own suc has, so the two ends
// meet at the same `m + m*(·)` form via IH.
var LeftAddDistrib = leftAddDistribThm{family.Add(registry.ProofEntry{
	Name: "LeftAddDistrib",
	Key:  "prop_a5e5f3a8c4babe5d",
	// Induct on the middle Skolem n. The step case cites Add + MulSuc +
	// AddAssoc up-front so each bridge leaf sees the three rewrite rules
	// resident, then drives through a two-level Trans bridge.
	Build: family.Theorem(
		"∀m n p:num. m * (n + p) = m * n + m * p",
		func(a *Argument, m, n, p Term) {
			// Bridges for the step case. outer meets LHS after Add peels suc
			// and MulSuc/IH unfold, and meets RHS after MulSuc + AddAssoc
			// reassociate; inner is the RHS-half sub-bridge AddAssoc lands on
			// from outer, which MulSuc then folds into the target RHS.
			outerBridge := a.Ctx().TermText("m₀ + (m₀ * n₀ + m₀ * p₀)")
			innerBridge := a.Ctx().TermText("(m₀ + m₀ * n₀) + m₀ * p₀")

			a.Induct(n)
			a.Base(
				"m₀*(0+p₀) = m₀*0 + m₀*p₀ — Add's zero clause folds 0+p₀ to p₀; MulZero collapses m₀*0 to 0",
				By(Normalized, Add, MulZero),
			)
			a.Step(
				"IH ⊢ m₀*(suc n₀ + p₀) = m₀*suc n₀ + m₀*p₀ — the equation chain below",
				Cite(Add),
				Cite(MulSuc),
				Cite(AddAssoc),
				// m₀*(suc n₀ + p₀) = m₀ + (m₀*n₀ + m₀*p₀)
				// = (m₀ + m₀*n₀) + m₀*p₀
				// = m₀*suc n₀ + m₀*p₀
				CalcEq(
					Leg(
						outerBridge,
						"Add's suc peels suc(n₀)+p₀ to suc(n₀+p₀); MulSuc "+
							"unfolds m₀*suc(·); IH swaps m₀*(n₀+p₀) to m₀*n₀ + m₀*p₀",
						CnfRefute(),
					),
					Leg(
						innerBridge,
						"AddAssoc reshuffles m₀ + (m₀*n₀ + m₀*p₀) into (m₀+m₀*n₀) + m₀*p₀",
						CnfRefute(),
					),
					FinalLeg(
						"MulSuc folds m₀ + m₀*n₀ into m₀*suc n₀",
						CnfRefute(),
					),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// RightAddDistrib — the same spreading, with the factor on the other side
// ---------------------------------------------------------------------------

// RightAddDistrib — right-distributivity of * over + on num, obtained
// by mirroring LeftAddDistrib through MulSym. No induction; the four
// ground instances below are the mirror's four links.
var RightAddDistrib = rightAddDistribThm{family.Add(registry.ProofEntry{
	Name: "RightAddDistrib",
	Key:  "prop_f65ea3005d15d828",
	Build: family.Theorem(
		"∀m n p:num. (m + n) * p = m * p + n * p",
		func(a *Argument, m, n, p Term) {
			v := ops(a.Ctx())

			a.Do(By(
				At(MulSym, v.Add(m, n), p),  // (m₀+n₀)*p₀ = p₀*(m₀+n₀)
				At(LeftAddDistrib, p, m, n), // p₀*(m₀+n₀) = p₀*m₀ + p₀*n₀
				At(MulSym, m, p),            // m₀*p₀ = p₀*m₀
				At(MulSym, n, p),            // n₀*p₀ = p₀*n₀
			))
		}),
})}

// ---------------------------------------------------------------------------
// MulEqZero — the naturals have no zero divisors
// ---------------------------------------------------------------------------

// MulEqZero — a product is zero exactly when one factor is zero.
// Cases on both factors leave only the product of two successors:
// Mul's right-successor clause and Add's left-successor clause make
// that product a successor, so it cannot be zero.
var MulEqZero = mulEqZeroThm{family.Add(registry.ProofEntry{
	Name: "MulEqZero",
	Key:  "prop_93c8149aaa0a33db",
	Build: family.Theorem(
		"∀m n:num. m * n = 0 ⇔ m = 0 ∨ n = 0",
		func(a *Argument, m, n *Expr[Nat]) {
			v := ops(a.Ctx())
			a.Do(peano.Cases.At(m).SplitDisj(
				LeftHolds(
					"m = 0: the product is zero",
					Given(func(b *Argument, zero Fact) {
						b.Show(
							"zero annihilates the product",
							By(zero, MulLeftZeroClause))
					})),
				RightHolds(
					"m is a successor: distinguish zero and successor for n",
					Given(func(b *Argument, successor Fact) {
						k, mSuc := b.UnpackAs[Nat](successor)
						b.Do(peano.Cases.At(n).SplitDisj(
							LeftHolds(
								"n = 0: the product is zero",
								Given(func(c *Argument, zero Fact) {
									c.Show(
										"zero annihilates the product",
										By(zero, MulZero))
								})),
							RightHolds(
								"both factors are successors: the product is a successor",
								Given(func(c *Argument, successor Fact) {
									l, nSuc := c.UnpackAs[Nat](successor)
									c.Show(
										"a successor is not zero",
										By(
											Normalized,
											mSuc,
											nSuc,
											MulSuc.At(m, l),
											At(AddLeftSucClause, k, v.Mul(m.Core(), l.Core())),
											peano.SucNotZero))
								})),
						))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// MulEqOne — one is indecomposable in multiplication
// ---------------------------------------------------------------------------

// MulEqOne — a product is one exactly when both factors are one.
// Zero factors are impossible. For two successors, the recursion
// clauses and successor injectivity reduce the product equation to a
// sum equalling zero; AddEqZero and MulEqZero identify both predecessors.
var MulEqOne = mulEqOneThm{family.Add(registry.ProofEntry{
	Name: "MulEqOne",
	Key:  "prop_b75a17e26797503f",
	Build: family.Theorem(
		"∀m n:num. m * n = 1 ⇔ m = 1 ∧ n = 1",
		func(a *Argument, m, n *Expr[Nat]) {
			v := ops(a.Ctx())
			a.Do(peano.Cases.At(m).SplitDisj(
				LeftHolds(
					"m = 0: neither side can hold",
					Given(func(b *Argument, zero Fact) {
						b.Do(zero.Rw())
						b.Show(
							"zero is not one",
							By(Normalized, MulLeftZeroClause, OneIsSucZero, peano.SucNotZero))
					})),
				RightHolds(
					"m is a successor: distinguish zero and successor for n",
					Given(func(b *Argument, successor Fact) {
						k, mSuc := b.UnpackAs[Nat](successor)
						b.Do(peano.Cases.At(n).SplitDisj(
							LeftHolds(
								"n = 0: neither side can hold",
								Given(func(c *Argument, zero Fact) {
									c.Do(zero.Rw())
									c.Show(
										"zero is not one",
										By(Normalized, MulZero, OneIsSucZero, peano.SucNotZero))
								})),
							RightHolds(
								"both factors are successors: both predecessors must be zero",
								Given(func(c *Argument, successor Fact) {
									l, nSuc := c.UnpackAs[Nat](successor)
									c.Show(
										"the product is one exactly when both predecessors vanish",
										By(
											mSuc,
											nSuc,
											MulSuc.At(m, l),
											AddClauses,
											At(AddEqZero, k, v.Mul(m.Core(), l.Core())),
											MulEqZero.At(m, l),
											OneIsSucZero,
											peano.SucNotZero,
											peano.SucInjective))
								})),
						))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The binary numeral encoding and its bridges to Peano structure
// ---------------------------------------------------------------------------
//
// A literal is a tower of bit0/bit1 over 0, and the two digits are what
// turns that tower back into successors: `bit0 n = n+n` doubles, `bit1 n =
// suc(n+n)` doubles and adds one. On top of them sit the bridges a proof
// reaches for when a particular literal has to meet a successor — `1 = suc
// 0`, `2 = suc 1`, `suc m = m + 1`, `1 ≠ 0`.
//
// The bridges are the ones the corpus has needed so far, and each is
// stated separately because each was demanded separately — not because a
// proof wants one without the others. It routinely wants two: `2 = suc(1)`
// leaves a `1` that still has to reach `suc(0)`, so a consumer of `Two`
// usually cites `OneIsSucZero` in the same premise list.
//
// The two digits of the encoding are defined here: bit0, a primitive
// recursion compiled against peano.Recursion; bit1, one successor on top
// of bit0. Each is spelled by a stand-in in its equation, the DSL keeping
// the names for its own numeral surface. `Bit0` and `Bit1` then state the
// doubling laws the bridges reach for.

// Bit0Def — bit0 defined by recursion: doubling zero is zero, doubling
// a successor adds two successors.
var Bit0Def = bit0DefThm{family.Define(registry.DefEntry{
	Name:      "Bit0Def",
	Key:       "prop_aecf4aa55f469daa",
	Const:     "bit0",
	Spelled:   "double",
	Type:      "num → num",
	Equations: []string{"double(0) = 0", "∀n:num. double(suc(n)) = suc(suc(double(n)))"},
})}

// Bit1Def — bit1 is one successor on top of bit0.
var Bit1Def = bit1DefThm{family.Define(registry.DefEntry{
	Name:      "Bit1Def",
	Key:       "prop_a1d5fc130a5c01d6",
	Const:     "bit1",
	Spelled:   "double_plus_one",
	Type:      "num → num",
	Equations: []string{"∀n:num. double_plus_one(n) = suc(bit0(n))"},
	Deps:      []registry.EntryLike{Bit0Def},
})}

// ---------------------------------------------------------------------------
// Bit0 — the low digit `0`: a numeral's leading 0 doubles it
// ---------------------------------------------------------------------------

// Bit0 — `bit0 n = n + n`. bit0 is defined by recursion (Bit0Def), two
// successors for each one of its argument:
//
//	bit0(0) = 0 ∧ ∀n. bit0(suc n) = suc(suc(bit0 n))
//
// and one induction on n carries those clauses to the doubling law:
//
//	base: bit0 0 = 0 = 0 + 0
//	step: bit0(suc n) = suc(suc(bit0 n)) = suc(suc(n + n))
//	 = suc(n + suc n) = suc n + suc n
//
// so the step needs the successor clause of + read against each of its
// arguments in turn — AddLeftSucClause and its right-hand sibling
// AddSuc.
var Bit0 = bit0Thm{family.Add(registry.ProofEntry{
	Name: "Bit0",
	Key:  "prop_16fbee89eed5bbb3",
	Build: family.Sections("∀n:num. bit0(n) = n + n",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			// bit0's own two clauses, from its definition.
			clauses := ctx.Dep(Bit0Def)

			return ctx.Theorem(headline, func(a *Argument) {
				// n stays bound — it is the induction variable. `clauses`
				// is a clause pack, and although the section states it with
				// one outer ∀n, normalization pushes that binder into the
				// conjunct that reads it — so the pack has no outer binder
				// for a witness to land on and the cite is bare.
				n := a.Binder("n")
				a.Induct(n)
				a.Base(
					"bit0 0 = 0 by the mint's zero clause, and 0 + 0 = 0 folds the right side to the same",
					By(clauses, AddLeftZeroClause),
				)
				a.Step(
					"bit0(suc n) = suc(suc(bit0 n)) = suc(suc(n+n)), and + "+
						"absorbs one successor from each side of suc n + suc n",
					func(b *Argument, ih Fact) {
						b.Show(
							"the mint's step clause and the IH on the left; the two successor clauses of + on the right",
							By(
								Normalized,
								ih,
								clauses,
								At(AddLeftSucClause, n, v.Suc(n)), // suc n + suc n = suc(n + suc n)
								At(AddSuc, n, n)))                 // n + suc n = suc(n + n)
					},
				)
			})
		}),
})}

// ---------------------------------------------------------------------------
// Bit1 — the low digit `1`: a numeral's leading 1 doubles and adds one
// ---------------------------------------------------------------------------

// Bit1 — `bit1 n = suc(n + n)`. bit1 is not a recursion of its own: it is
// defined outright as `λn. suc(bit0 n)`, so unfolding that definition and
// citing Bit0 under the suc is the whole proof.
var Bit1 = bit1Thm{family.Add(registry.ProofEntry{
	Name: "Bit1",
	Key:  "prop_5c130f45992e543b",
	// The unfold has to run on the ∀-goal, so nothing is bound first.
	Build: family.Theorem("∀n:num. bit1(n) = suc(n + n)",
		func(a *Argument) {
			// bit1 ↦ λn. suc(bit0 n), leaving suc(bit0 n) = suc(n + n);
			// Bit0 rewrites bit0 n and closes at the cite.
			a.Do(Unfold(Bit1Def), Cite(Bit0))
		}),
})}

// ---------------------------------------------------------------------------
// Add1 — successor is addition of one
// ---------------------------------------------------------------------------

// Add1 — the successor / add-one numeral bridge. Two cites and a
// refute: OneIsSucZero unfolds `1` to `suc(0)`, and AddClauses supplies
// the two right-side identities — its right-identity and `k + suc l`
// conjuncts — needed to push suc out through +. The CNF refuter
// closes on the resulting ground equation.
//
// A numeral utility rather than a law of the theory, but chapter API
// by fan-in: slope's step-bound toolkit and complete's arch_zero both
// rewrite suc through it. What the argument needs from the numeral `1`
// is exactly `1 = suc(0)` — OneIsSucZero, the member whose job is that
// bridge — so the digits above never enter here, even though they are
// what OneIsSucZero itself is proved from.
var Add1 = add1Thm{family.Add(registry.ProofEntry{
	Name: "Add1",
	Key:  "prop_764a1745b8b338b4",
	// Rewrite 1 to suc(0), then AddClauses (the four-way pack — the
	// right-successor and right-identity clauses do the work here), and
	// refute.
	Build: family.Theorem("∀m:num. suc(m) = m + 1",
		func(a *Argument, m Term) {
			a.Do(By(OneIsSucZero, AddClauses))
		}),
})}

// NonzeroIsSucc — exclude zero in Peano's cases and write the
// remaining successor as addition by one.
var NonzeroIsSucc = nonzeroIsSuccThm{family.Add(registry.ProofEntry{
	Name: "NonzeroIsSucc",
	Key:  "prop_6218cdd6598d47bc",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"n ≠ 0",
		},
		Conclusion: "∃m:num. n = m + 1",
	},
		func(a *Argument, n *Expr[Nat], nonzero Fact) {
			m, successor := a.ObtainAs[Nat](
				"a nonzero natural number has a predecessor",
				"∃m:num. n = suc(m)",
				By(Normalized, nonzero, peano.Cases.At(n)))
			a.Take(m)
			a.Show(
				"write the successor as addition by one",
				Simp(Rev(Add1)),
				By(successor))
		}),
})}

// ---------------------------------------------------------------------------
// OneIsSucZero — the numeral 1, in Peano form
// ---------------------------------------------------------------------------

// OneIsSucZero — `1` unfolds through bit1's defining equation to
// suc(0 + 0), and Add's zero clause collapses the argument: two
// premises and a refute. The family states that clause on its own
// (AddLeftZeroClause), so no induction is needed here.
//
// A numeral utility like Add1 (its exact sibling in shape), and the
// chapter's smallest bridge: everything that trades a literal `1` for
// successor structure — divisibility's units, real_field's inverse
// laws, this family's own numeral rewrites — steps through it.
var OneIsSucZero = oneIsSucZeroThm{family.Add(registry.ProofEntry{
	Name: "OneIsSucZero",
	Key:  "prop_cfe12a8f490d0909",
	// Cite Bit1 (unfolds 1 = suc(0 + 0)) and the zero clause of +, then
	// refute the ground equation.
	Build: family.Theorem("1 = suc(0)",
		By(Normalized, Bit1, AddLeftZeroClause)),
})}

// ---------------------------------------------------------------------------
// Two — the numeral 2, in Peano form
// ---------------------------------------------------------------------------

// Two — `2 = suc(1)`, OneIsSucZero's successor and the next rung of the
// same ladder. The binary literal `2` is `bit0(bit1(0))` and `1` is
// `bit1(0)`, so unfolding both leaves `suc(0+0) + suc(0+0) =
// suc(suc(0+0))` — an arithmetic identity, not a numeral one, which is
// why this member needs the whole recursion of + where its predecessor
// needed only the zero clause.
//
// Chapter API by fan-in, and by demand: an ordered theory sees a literal
// as opaque, so anything that has to know how far `2` stands from `0`
// spends this bridge once and works in successors afterwards.
// nat_parity's doubling laws and int_div_rem's division by `&2` are the
// current consumers.
var Two = twoThm{family.Add(registry.ProofEntry{
	Name: "Two",
	Key:  "prop_c6342fb2c35ccf59",
	// Cite both digits of the encoding and the recursion of +, then refute
	// the ground equation.
	Build: family.Theorem("2 = suc(1)",
		By(Bit0, Bit1, Add)),
})}

// ---------------------------------------------------------------------------
// OneNotZero — the two numerals a proof has to tell apart
// ---------------------------------------------------------------------------

// OneNotZero — `1 ≠ 0`. The bridge above puts `1` in successor form, and
// no successor is zero; that is the entire proof, and it is the one the
// corpus had been writing out by hand.
//
// It exists because the refuter treats numeral literals as opaque atoms.
// Nothing in `0` or `1` tells it the two differ, so any argument that
// turns on the distinction — a divisor guard, a residue that must be told
// apart from zero, a nontriviality assumption — has to supply the fact,
// and supplying it means both this member's deps in the same premise
// list. Three chapters were doing exactly that (nat_arith's own PowEqZero,
// real_field's inverse laws, nat_parity's residue characterisation),
// which is the threshold at which the derivation belongs to the layer
// that owns the numerals rather than to each consumer.
var OneNotZero = oneNotZeroThm{family.Add(registry.ProofEntry{
	Name: "OneNotZero",
	Key:  "prop_397ca854c85bc361",
	Build: family.Theorem("1 ≠ 0",
		By(OneIsSucZero, peano.SucNotZero)),
})}

// ---------------------------------------------------------------------------
// Evaluating on numerals — the digit-by-digit laws
// ---------------------------------------------------------------------------
//
// suc, +, * and = are computed on numerals one low digit at a time:
// each has a law for every combination of low digits, and those laws
// packed into one conjunction are what a numeral evaluator consults.
// The four packs below are those conjunctions, each clause in the order
// the evaluator reads them. A clause is the two digit equations — Bit0
// and Bit1 — read on the digits in play, followed by the clauses of the
// operation — and, for + and *, one regrouping identity each:
// sumOfDoubles (associativity and commutativity of +) and
// productOfDoubles (distributivity). NumeralEq also uses the two
// doubling facts stated just before it: doublingInjective cancels a
// common factor two, and doubleNotOdd distinguishes the parities by
// induction.

// ---------------------------------------------------------------------------
// NumeralSuc — the successor of a numeral, digit by digit
// ---------------------------------------------------------------------------

var NumeralSuc = numeralSucThm{family.Add(registry.ProofEntry{
	Name: "NumeralSuc",
	Key:  "prop_ac69f32daf9d9582",
	Build: family.Theorem("suc(0) = bit1(0) ∧ "+
		"(∀n:num. suc(bit0(n)) = bit1(n)) ∧ "+
		"(∀n:num. suc(bit1(n)) = bit0(suc(n)))", func(a *Argument) {
		a.Do(SplitConjAll(
			Case(
				"suc 0 = bit1 0, the numeral 1: OneIsSucZero read right to left",
				Cite(OneIsSucZero)),
			Case(
				"suc(bit0 n) = bit1 n: both sides unfold to suc(n + n)",
				Derive(func(b *Argument) {
					n := b.Fix()
					b.Show(
						"the two digit equations at n",
						By(Normalized, At(Bit0, n), At(Bit1, n)))
				})),
			Case(
				"suc(bit1 n) = bit0(suc n): a carry — suc(suc(n + n)) is "+
					"suc n + suc n with a successor absorbed from each side",
				// The successor clauses of + move each suc out of the sum.
				Simp(Fwd(Bit1), Fwd(Bit0), Fwd(AddLeftSucClause), Fwd(AddSuc)),
				TrivialNormalized()),
		))
	}),
})}

// ---------------------------------------------------------------------------
// NumeralAdd — the sum of two numerals, digit by digit
// ---------------------------------------------------------------------------

var NumeralAdd = numeralAddThm{family.Add(registry.ProofEntry{
	Name: "NumeralAdd",
	Key:  "prop_f42cc4e1fba33c5d",
	Build: family.Sections("0 + 0 = 0 ∧ "+
		"(∀n:num. 0 + bit0(n) = bit0(n)) ∧ "+
		"(∀n:num. 0 + bit1(n) = bit1(n)) ∧ "+
		"(∀n:num. bit0(n) + 0 = bit0(n)) ∧ "+
		"(∀n:num. bit1(n) + 0 = bit1(n)) ∧ "+
		"(∀m n:num. bit0(m) + bit0(n) = bit0(m + n)) ∧ "+
		"(∀m n:num. bit0(m) + bit1(n) = bit1(m + n)) ∧ "+
		"(∀m n:num. bit1(m) + bit0(n) = bit1(m + n)) ∧ "+
		"(∀m n:num. bit1(m) + bit1(n) = bit0(suc(m + n)))", func(
		ctx *Script,
		headline string,
	) *GoalStackNode {
		// sumOfDoubles — the regrouping every digit sum comes down to:
		// the same four summands, reassociated and commuted.
		sumOfDoubles := ctx.Lemma("∀m n:num. m + m + (n + n) = m + n + (m + n)",
			func(a *Argument, m, n Term) {
				a.Do(ACRegroupWith(AddAC(ctx)))
			})

		// unfoldDigits ↦ the clause with both digits unfolded and every
		// suc an odd digit contributed moved out of the sum by the
		// successor clauses of +.
		unfoldDigits := Simp(Fwd(Bit0), Fwd(Bit1), Fwd(AddLeftSucClause), Fwd(AddSuc))

		// oddDigitSum is a digit sum with at least one odd digit.
		oddDigitSum := func() Action {
			return Derive(func(a *Argument) {
				m, n := a.Fix(), a.Fix()
				a.Do(unfoldDigits)
				a.Show(
					"sumOfDoubles under the successors",
					By(Normalized, At(sumOfDoubles, m, n)))
			})
		}

		return ctx.Theorem(headline, func(a *Argument) {
			a.Do(SplitConjAll(
				Case(
					"0 + 0 = 0: the left zero clause",
					By(AddLeftZeroClause)),
				Case(
					"0 + bit0 n = bit0 n: the left zero clause",
					By(AddLeftZeroClause)),
				Case(
					"0 + bit1 n = bit1 n: the left zero clause",
					By(AddLeftZeroClause)),
				Case(
					"bit0 n + 0 = bit0 n: the right zero clause",
					By(AddZero)),
				Case(
					"bit1 n + 0 = bit1 n: the right zero clause",
					By(AddZero)),
				Case(
					"bit0 m + bit0 n = bit0(m + n): unfolded, this is sumOfDoubles itself",
					unfoldDigits,
					Cite(sumOfDoubles)),
				Case(
					"bit0 m + bit1 n = bit1(m + n): m + m + suc(n + n) = suc(m + n + (m + n))",
					oddDigitSum()),
				Case(
					"bit1 m + bit0 n = bit1(m + n): suc(m + m) + (n + n) = suc(m + n + (m + n))",
					oddDigitSum()),
				Case(
					"bit1 m + bit1 n = bit0(suc(m + n)): the carry — suc(m + m) + suc(n + n) = suc(m + n) + suc(m + n)",
					oddDigitSum()),
			))
		})
	}),
})}

// ---------------------------------------------------------------------------
// NumeralMul — the product of two numerals, digit by digit
// ---------------------------------------------------------------------------

var NumeralMul = numeralMulThm{family.Add(registry.ProofEntry{
	Name: "NumeralMul",
	Key:  "prop_e79a08d131265a92",
	Build: family.Sections("0 * 0 = 0 ∧ "+
		"(∀n:num. 0 * bit0(n) = 0) ∧ "+
		"(∀n:num. 0 * bit1(n) = 0) ∧ "+
		"(∀n:num. bit0(n) * 0 = 0) ∧ "+
		"(∀n:num. bit1(n) * 0 = 0) ∧ "+
		"(∀m n:num. bit0(m) * bit0(n) = bit0(bit0(m * n))) ∧ "+
		"(∀m n:num. bit0(m) * bit1(n) = bit0(m) + bit0(bit0(m * n))) ∧ "+
		"(∀m n:num. bit1(m) * bit0(n) = bit0(n) + bit0(bit0(m * n))) ∧ "+
		"(∀m n:num. bit1(m) * bit1(n) = bit1(m) + (bit0(n) + bit0(bit0(m * n))))", func(
		ctx *Script,
		headline string,
	) *GoalStackNode {
		// productOfDoubles — doubling both factors quadruples the
		// product. With both digits unfolded, (m + m)·(n + n) distributes
		// into four copies of m·n, which is bit0(bit0(m·n)).
		productOfDoubles := ctx.Lemma("∀m n:num. bit0(m) * bit0(n) = bit0(bit0(m * n))",
			func(a *Argument) {
				a.Show(
					"both sides distribute to four copies of m · n",
					Simp(Fwd(Bit0), Fwd(RightAddDistrib), Fwd(LeftAddDistrib)),
					TrivialNormalized())
			})

		return ctx.Theorem(headline, func(a *Argument) {
			a.Do(SplitConjAll(
				Case(
					"0 * 0 = 0: the left zero clause",
					By(MulLeftZeroClause)),
				Case(
					"0 * bit0 n = 0: the left zero clause",
					By(MulLeftZeroClause)),
				Case(
					"0 * bit1 n = 0: the left zero clause",
					By(MulLeftZeroClause)),
				Case(
					"bit0 n * 0 = 0: the right zero clause",
					By(MulZero)),
				Case(
					"bit1 n * 0 = 0: the right zero clause",
					By(MulZero)),
				Case(
					"bit0 m * bit0 n = bit0(bit0(m * n)): this is productOfDoubles itself",
					Cite(productOfDoubles)),
				Case(
					"bit0 m * bit1 n = bit0 m + bit0(bit0(m * n)): the odd "+
						"factor sheds one bit0 m, and productOfDoubles reads the rest",
					Unfold(Bit1Def), // bit1 n ↦ suc(bit0 n)
					Simp(Fwd(MulSuc), Fwd(productOfDoubles)),
					TrivialNormalized()),
				Case(
					"bit1 m * bit0 n = bit0 n + bit0(bit0(m * n)): the odd "+
						"factor sheds one bit0 n, then the two summands commute",
					Derive(func(a *Argument) {
						a.Fix()
						a.Fix()
						a.Do(Unfold(Bit1Def), Simp(Fwd(mulLeftSucClause), Fwd(productOfDoubles))) // bit1 m ↦ suc(bit0 m)
						a.Show(
							"the two summands in the other order",
							ACRegroupWith(AddAC(ctx)))
					})),
				Case(
					"bit1 m * bit1 n = bit1 m + (bit0 n + bit0(bit0(m * n))): both "+
						"factors odd, so both step clauses fire before productOfDoubles",
					Derive(func(a *Argument) {
						a.Fix()
						a.Fix()
						a.Do(Unfold(Bit1Def), Simp(Fwd(MulSuc)), // bit1 m, bit1 n ↦ suc(bit0 m), suc(bit0 n)
							Simp(Fwd(mulLeftSucClause), Fwd(productOfDoubles)))
						a.Show(
							"the two inner summands in the other order",
							ACRegroupWith(AddAC(ctx)))
					})),
			))
		})
	}),
})}

// ---------------------------------------------------------------------------
// NumeralEq — equality of two numerals, digit by digit
// ---------------------------------------------------------------------------

// doublingInjective — equal doubles have equal halves. Write each
// double as a product by two, then cancel that nonzero factor.
// NumeralEq uses this to compare its even digits.
var doublingInjective = doublingInjectiveThm{family.Add(registry.ProofEntry{
	Name: "doublingInjective",
	Key:  "prop_2606558ef94959c1",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m + m = n + n",
		},
		Conclusion: "m = n",
	}, func(a *Argument, m, n *Expr[Nat], eq Fact) {
		one := a.TermAs[Nat]("1")
		two := a.TermAs[Nat]("2")
		products := a.Have(
			"equal doubles are equal products by two",
			"2 * m = 2 * n",
			By(eq, Two, mulLeftSucClause.At(one, m), mulLeftSucClause.At(one, n), OneMul))
		a.Show(
			"cancel the nonzero factor two",
			By(products, MulEqLCancel.At(two, m, n), Two, peano.SucNotZero))
	}),
})}

// doubleNotOdd — an even number is never one more than an even number:
// m + m ≠ suc(n + n). Induction on m and cases on n at the step
// remove two successors from each side. NumeralEq uses this to
// distinguish its even digits from its odd digits.
var doubleNotOdd = doubleNotOddThm{family.Add(registry.ProofEntry{
	Name: "doubleNotOdd",
	Key:  "prop_f0e32d603608e32d",
	Build: family.Theorem("∀m n:num. m + m ≠ suc(n + n)", func(a *Argument) {
		v := ops(a.Ctx())
		k := Var("k", NumType) // the ∃-binder in "n is zero or a successor"
		m := a.Binder("m")
		a.Induct(m)
		a.Base(
			"m = 0: 0 is not a successor",
			func(a *Argument) {
				a.Fix()
				a.Show(
					"0 + 0 is 0, and no successor is zero",
					By(AddLeftZeroClause, peano.SucNotZero))
			})
		a.Step(
			"m → suc m: n = 0 leaves a double successor ≠ suc 0, n = suc k cancels two successors to the IH",
			func(a *Argument, ih Fact) {
				n := a.Fix()
				zeroOrSuc := a.Have(
					"n is zero or a successor",
					MakeProp(n.Eq(v.Zero).Or(Exists(k)(n.Eq(v.Suc(k))))),
					By(At(peano.Cases, n)))
				a.Do(zeroOrSuc.SplitDisj(
					LeftHolds(
						"n = 0: suc m + suc m is a double successor, so not suc 0",
						Given(func(a *Argument, isZero Fact) {
							a.Do(isZero.Rw()) // n ↦ 0 in the goal
							twiceM := a.Have(
								"suc m + suc m is two successors above m + m",
								MakeProp(v.Add(v.Suc(m), v.Suc(m)).Eq(v.Suc(v.Suc(v.Add(m, m))))),
								By(AddLeftSucClause, AddSuc))
							a.Show(
								"a double successor is never suc(0), by SucInjective and SucNotZero",
								By(twiceM, AddLeftZeroClause, peano.SucInjective, peano.SucNotZero))
						})),
					RightHolds(
						"n = suc k: two successors come off each side, leaving the IH",
						Given(func(a *Argument, isSuc Fact) {
							kv, kEq := a.Unpack(isSuc)
							a.Do(kEq.Rw()) // n ↦ suc(k) in the goal
							twiceM := a.Have(
								"suc m + suc m is two successors above m + m",
								MakeProp(v.Add(v.Suc(m), v.Suc(m)).Eq(v.Suc(v.Suc(v.Add(m, m))))),
								By(AddLeftSucClause, AddSuc))
							twiceK := a.Have(
								"suc k + suc k is two successors above k + k",
								MakeProp(v.Add(v.Suc(kv), v.Suc(kv)).Eq(v.Suc(v.Suc(v.Add(kv, kv))))),
								By(AddLeftSucClause, AddSuc))
							a.Show(
								"both sides lose their shared successors, leaving m + m ≠ suc(k + k) — the IH at k",
								By(twiceM, twiceK, ih.At(kv), peano.SucInjective))
						})),
				))
			})
	}),
})}

var NumeralEq = numeralEqThm{family.Add(registry.ProofEntry{
	Name: "NumeralEq",
	Key:  "prop_2ef5e222443afafa",
	Build: family.Theorem("(∀n:num. bit0(n) = 0 ⇔ n = 0) ∧ "+
		"(∀n:num. bit1(n) ≠ 0) ∧ "+
		"(∀n:num. 0 = bit0(n) ⇔ 0 = n) ∧ "+
		"(∀n:num. 0 ≠ bit1(n)) ∧ "+
		"(∀m n:num. bit0(m) = bit0(n) ⇔ m = n) ∧ "+
		"(∀m n:num. bit0(m) ≠ bit1(n)) ∧ "+
		"(∀m n:num. bit1(m) ≠ bit0(n)) ∧ "+
		"(∀m n:num. bit1(m) = bit1(n) ⇔ m = n)", func(a *Argument) {
		// evenIff — the shared shape of the two even-digit equivalences:
		// once bit0 is unfolded on both sides the goal is m+m = n+n ⇔ m=n,
		// whose forward half is doublingInjective and whose backward half
		// is a congruence.
		evenIff := func(a *Argument, m, n Term) {
			a.Iff()
			a.Forward(
				"equal doubles have equal halves: doublingInjective",
				func(a *Argument, eq Fact) {
					a.Show(
						"the halves are equal",
						By(eq, At(doublingInjective, m, n)))
				})
			a.Backward(
				"m = n: doubling equal numbers gives equal results",
				func(a *Argument, mn Fact) {
					a.Show(
						"equal halves double to equal numbers",
						By(Normalized, mn))
				})
		}
		a.Do(SplitConjAll(
			Case(
				"bit0 n = 0 ⇔ n = 0: n + n = 0 iff n = 0, by AddEqZero",
				Derive(func(a *Argument) {
					n := a.Fix()
					a.Do(Simp(Fwd(Bit0)))
					a.Show(
						"n + n = 0 iff n = 0",
						By(Normalized, At(AddEqZero, n, n)))
				})),
			Case(
				"bit1 n ≠ 0: bit1 n is a successor, and no successor is zero",
				Derive(func(a *Argument) {
					a.Fix()
					a.Do(Simp(Fwd(Bit1)))
					a.Show(
						"no successor is zero",
						By(peano.SucNotZero))
				})),
			Case(
				"0 = bit0 n ⇔ 0 = n: the same as bit0 n = 0, read the other way",
				Derive(func(a *Argument) {
					n := a.Fix()
					a.Do(Simp(Fwd(Bit0)))
					a.Show(
						"n + n = 0 iff n = 0",
						By(Normalized, At(AddEqZero, n, n)))
				})),
			Case(
				"0 ≠ bit1 n: a successor is not zero",
				Derive(func(a *Argument) {
					a.Fix()
					a.Do(Simp(Fwd(Bit1)))
					a.Show(
						"no successor is zero",
						By(peano.SucNotZero))
				})),
			Case(
				"bit0 m = bit0 n ⇔ m = n: doubling is injective",
				Derive(func(a *Argument) {
					m, n := a.Fix(), a.Fix()
					a.Do(Simp(Fwd(Bit0)))
					evenIff(a, m, n)
				})),
			Case(
				"bit0 m ≠ bit1 n: an even number is not an odd number — doubleNotOdd",
				Derive(func(a *Argument) {
					a.Fix()
					a.Fix()
					a.Do(Simp(Fwd(Bit0), Fwd(Bit1)))
					a.Show(
						"an even number is not an odd one",
						Cite(doubleNotOdd))
				})),
			Case(
				"bit1 m ≠ bit0 n: the same parity clash, the odd number on the left",
				Derive(func(a *Argument) {
					m, n := a.Fix(), a.Fix()
					a.Do(Simp(Fwd(Bit0), Fwd(Bit1)))
					a.Show(
						"doubleNotOdd with m and n exchanged",
						By(At(doubleNotOdd, n, m)))
				})),
			Case(
				"bit1 m = bit1 n ⇔ m = n: strip the shared successor, then doubling is injective",
				Derive(func(a *Argument) {
					m, n := a.Fix(), a.Fix()
					a.Do(Simp(Fwd(Bit1), Fwd(peano.SucInjective)))
					evenIff(a, m, n)
				})),
		))

	}),
})}
