// nat_order.go — the chapter: the order theory of ℕ.
//
// Eleven parts, marked by banners:
//
// - The recursion equations of ≤ and < (LessEq, LessThan)
// - The successor/zero interaction lemmas of ≤ and < on ℕ
// - The order axioms of ≤ and < on ℕ
// - The totality/trichotomy tier of the ≤/< order on ℕ
// - The ≤/< duality bridges of the order on ℕ
// - The compatibility of ≤ / < with addition
// - The compatibility of ≤ / < with multiplication
// - Evaluating ≤ and < on numerals — the digit-by-digit laws
// - The order against exponentiation
// - Growth bounds: how ≤ behaves along linear and affine functions of
// ℕ
// - < is well-founded on ℕ

package nat_order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/solver/ac"
)

// ---------------------------------------------------------------------------
// The recursion equations of ≤ and < (LessEq, LessThan)
// ---------------------------------------------------------------------------
//
// The order relations DEFINED — ≤ and < by recursion on the right
// argument (`family.Define`, compiled against peano.Recursion), > and ≥
// as their mirrors, nat_max and nat_min as the conditional picks — plus the
// family's four INTERNAL projection lemmas (plan §Families, "Internal
// entries"): the defining clauses of each order relation as standalone
// rewrite rules, stated once here and cited family-wide instead of
// re-proved per member. The operators are spelled by
// stand-ins in their equations (`le`, `lt`, `gt`, `ge`, `max`, `min`):
// the DSL has no head-position spelling for an operator, and keeps
// nat_max / nat_min for its own numeral surface.

// ---------------------------------------------------------------------------
// LessEq — the recursion equations of ≤
// ---------------------------------------------------------------------------

// LessEq — ≤ defined: only zero is at most zero, and m is at most a
// successor when it is that successor or at most its predecessor.
var LessEq = lessEqThm{family.Define(registry.DefEntry{
	Name:      "LessEq",
	Key:       "prop_15f62aa72e478573",
	Const:     "<=",
	Spelled:   "le",
	Type:      "num → num → bool",
	Equations: []string{"∀m:num. le(m, 0) ⇔ m = 0", "∀m n:num. le(m, suc(n)) ⇔ m = suc(n) ∨ le(m, n)"},
})}

// ---------------------------------------------------------------------------
// LessThan — the recursion equations of <
// ---------------------------------------------------------------------------

// LessThan — < defined: nothing is below zero, and m is below a
// successor when it is the predecessor or below it.
var LessThan = lessThanThm{family.Define(registry.DefEntry{
	Name:      "LessThan",
	Key:       "prop_c91079eb4b5ddb26",
	Const:     "<",
	Spelled:   "lt",
	Type:      "num → num → bool",
	Equations: []string{"∀m:num. lt(m, 0) ⇔ ⊥", "∀m n:num. lt(m, suc(n)) ⇔ m = n ∨ lt(m, n)"},
})}

// GtDef · GeDef — the mirrors: m > n is n < m, m ≥ n is n ≤ m.
var GtDef = gtDefThm{family.Define(registry.DefEntry{
	Name:      "GtDef",
	Key:       "prop_18e8e4f732e85da1",
	Const:     ">",
	Spelled:   "gt",
	Type:      "num → num → bool",
	Equations: []string{"∀m n:num. gt(m, n) ⇔ n < m"},
	Deps:      []registry.EntryLike{LessThan},
})}

var GeDef = geDefThm{family.Define(registry.DefEntry{
	Name:      "GeDef",
	Key:       "prop_5cdcc6f0b6b9e6fc",
	Const:     ">=",
	Spelled:   "ge",
	Type:      "num → num → bool",
	Equations: []string{"∀m n:num. ge(m, n) ⇔ n ≤ m"},
	Deps:      []registry.EntryLike{LessEq},
})}

// NatMaxDef · NatMinDef — the larger and the smaller of two numbers, picked
// by comparing them.
var NatMaxDef = natMaxDefThm{family.Define(registry.DefEntry{
	Name:      "NatMaxDef",
	Key:       "prop_4373cc6da3df411a",
	Const:     "nat_max",
	Spelled:   "max",
	Type:      "num → num → num",
	Overload:  "max",
	Equations: []string{"∀m n:num. max(m, n) = COND(m ≤ n, n, m)"},
	Deps:      []registry.EntryLike{LessEq},
})}

var NatMinDef = natMinDefThm{family.Define(registry.DefEntry{
	Name:      "NatMinDef",
	Key:       "prop_22a39e96dff8322d",
	Const:     "nat_min",
	Spelled:   "min",
	Type:      "num → num → num",
	Overload:  "min",
	Equations: []string{"∀m n:num. min(m, n) = COND(m ≤ n, m, n)"},
	Deps:      []registry.EntryLike{LessEq},
})}

// ---------------------------------------------------------------------------
// The four projection lemmas (INTERNAL entries — plan §Families).
//
// LessEq and LessThan state their recursion clauses as one
// conjunction; members doing induction over ≤ / < need the individual
// clauses as rewrite rules. Stated once here, cited family-wide.
// Statements are ours; keys are the statements' own normalized keys
// (see the README on why these carry our names).
//
// Shared recipe (all four): bind the statement's ∀-prefix and close
// from the definition. The suc clauses spell that as Cite(def) +
// CnfRefute — the cite installs both recursion clauses without
// closing, and the trailing refute selects the disjunctive one this
// entry states. The zero clauses have no disjunction to select, so
// they close with By(def), the single step that installs the clauses
// and finishes whatever the install left. The section texts are stated ONCE
// below: Stmt and Build must stay byte-identical, and the shared const
// removes the sync burden. Only the Stmt builders carry Const
// declarations — they run on a bare Script, while a Build's statement
// parses against the family vocabulary (vocab.go).
// ---------------------------------------------------------------------------

// LessEqZeroClause — LessEq's zero clause: zero bounds only itself.
var LessEqZeroClause = lessEqZeroClauseThm{family.Add(registry.ProofEntry{
	Name: "LessEqZeroClause",
	Key:  "prop_7a80aee523a0ad34",
	Build: family.Theorem("∀m:num. m ≤ 0 ⇔ m = 0",
		func(a *Argument, m Term) {
			a.Do(By(Normalized, LessEq))
		}),
})}

// LessEqSucClause — LessEq's successor clause, restated in natural
// disjunct order (LessEq's recorded order is flipped).
var LessEqSucClause = lessEqSucClauseThm{family.Add(registry.ProofEntry{
	Name: "LessEqSucClause",
	Key:  "prop_1ac356ee6a127d8b",
	Build: family.Theorem("∀m n:num. m ≤ suc(n) ⇔ m ≤ n ∨ m = suc(n)",
		func(a *Argument, m, n Term) {
			a.Do(Cite(LessEq), CnfRefute())
		}),
})}

// LessThanZeroClause — LessThan's zero clause: nothing is below zero.
var LessThanZeroClause = lessThanZeroClauseThm{family.Add(registry.ProofEntry{
	Name: "LessThanZeroClause",
	Key:  "prop_7a28e476069cffa1",
	Build: family.Theorem("∀m:num. ¬(m < 0)",
		func(a *Argument, m Term) {
			a.Do(By(LessThan))
		}),
})}

// LessThanSucClause — LessThan's successor clause in natural disjunct order.
var LessThanSucClause = lessThanSucClauseThm{family.Add(registry.ProofEntry{
	Name: "LessThanSucClause",
	Key:  "prop_7310af881d9085d6",
	Build: family.Theorem("∀m n:num. m < suc(n) ⇔ m < n ∨ m = n",
		func(a *Argument, m, n Term) {
			a.Do(Cite(LessThan), CnfRefute())
		}),
})}

// ---------------------------------------------------------------------------
// The successor/zero interaction lemmas of ≤ and < on ℕ
// ---------------------------------------------------------------------------
//
// Holds ZeroLessEq (0 is the bottom element of ≤), the successor bridges
// LessThanSucIffLessEq (internal) and SucLessEqIffLessThan (chapter API —
// the tower's most-cited bridge), and their one-section consequences
// SucLessEqSucIff, sucLessThanSucIff and ZeroLessThanSuc.

// ZeroLessEq — zero is the bottom element of ≤, by
// induction on n from LessEq's two clause projections — one
// induction.
var ZeroLessEq = zeroLessEqThm{family.Add(registry.ProofEntry{
	Name: "ZeroLessEq",
	Key:  "prop_a9a4c6302ce129b9",
	// Induct on the bound n.
	Build: family.Theorem("∀n:num. 0 ≤ n",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"0 ≤ 0 rewrites to 0 = 0 via the zero clause — refl, closes on the cite",
				Cite(LessEqZeroClause),
			)
			a.Step(
				"0 ≤ suc n is 0 ≤ n (the IH) or 0 = suc n by the suc clause — the IH decides it",
				Cite(LessEqSucClause),
				CnfRefute(),
			)
		}),
})}

// LessThanSucIffLessEq — the successor bridge from
// < to ≤, taking the successor on the BOUND: `m < suc n ⇔ m ≤ n`.
// Its mirror is SucLessEqIffLessThan below, which takes the successor
// on the SUBJECT (`suc m ≤ n ⇔ m < n`); the two are the only ways to
// cross between the orders, and a consumer picks by which side of its
// goal already carries the suc.
//
// By induction on n from the clause projections — one induction.
var LessThanSucIffLessEq = lessThanSucIffLessEqThm{family.Add(registry.ProofEntry{
	Name: "LessThanSucIffLessEq",
	Key:  "prop_7ae6dcaaf1254ca5",
	// Induct on n — m stays a fixed free, so the IH is the bridge at n
	// for the same m.
	Build: family.Theorem("∀m n:num. m < suc(n) ⇔ m ≤ n",
		func(a *Argument, m, n Term) {
			a.Induct(n)
			// The le zero clause fires as a rewrite (m ≤ 0 → m = 0) and
			// is consumed; the two lt clauses stay resident for the
			// refuter.
			a.Base(
				"the clauses collapse both sides to m = 0 — m < suc 0 via "+
					"the lt suc + lt zero clauses, m ≤ 0 via the le zero clause",
				Cite(LessThanSucClause),
				Cite(LessThanZeroClause),
				Cite(LessEqZeroClause),
				CnfRefute(),
			)
			a.Step(
				"the suc clauses split both sides over the common disjunct m "+
					"= suc n; the IH identifies the residual m < suc n with m ≤ n",
				Cite(LessThanSucClause),
				Cite(LessEqSucClause),
				CnfRefute(),
			)
		}),
})}

// SucLessEqIffLessThan — strict order is successor bound, taking the
// successor on the SUBJECT: `suc m ≤ n ⇔ m < n`. The headline states
// it the other way round (`m < n ⇔ suc m ≤ n`) — an ⇔ reads either
// direction, and the name leads with the suc side so it cannot be
// mistaken for LessThanSucIffLessEq above, whose successor sits on the
// bound instead.
//
// By induction on n from the clause projections — one induction.
var SucLessEqIffLessThan = sucLessEqIffLessThanThm{family.Add(registry.ProofEntry{
	Name: "SucLessEqIffLessThan",
	Key:  "prop_26fd703995f49712",
	// Induct on n — m stays a fixed free, so the IH is the bound at n
	// for the same m.
	Build: family.Theorem("∀m n:num. m < n ⇔ suc(m) ≤ n",
		func(a *Argument, m, n Term) {
			a.Induct(n)
			// Cite order is load-bearing: suc_not_zero comes FIRST, while no
			// suc· = 0 atom exists yet (the le zero clause only creates
			// it), so it stays resident for the refuter instead of
			// firing and being consumed.
			a.Base(
				"both sides false — the lt zero clause kills m < 0; the le zero "+
					"clause turns suc m ≤ 0 into suc m = 0, refuted by suc_not_zero",
				Cite(peano.SucNotZero),
				Cite(LessThanZeroClause),
				Cite(LessEqZeroClause),
				CnfRefute(),
			)
			a.Step(
				"the suc clauses split each side; suc_injective identifies "+
					"the equational disjuncts, the IH the order disjuncts",
				Cite(LessThanSucClause),
				Cite(LessEqSucClause),
				Cite(peano.SucInjective),
				CnfRefute(),
			)
		}),
})}

// SucLessEqSucIff — ≤ is invariant under suc: the two successor bridges
// compose through the waypoint m < suc n. Spelled as two goal
// rewrites — each cite fires on the current goal and lands on the
// next link (per-cite comments carry the intermediate); the second
// leaves a refl-shaped iff, so the proof closes at the cite.
var SucLessEqSucIff = sucLessEqSucIffThm{family.Add(registry.ProofEntry{
	Name: "SucLessEqSucIff",
	Key:  "prop_378230592ecf90ff",
	Build: family.Theorem("∀m n:num. suc(m) ≤ suc(n) ⇔ m ≤ n",
		func(a *Argument, m, n Term) {
			a.Do(
				// Each bridge fires as a goal rewrite and is consumed:
				Cite(SucLessEqIffLessThan), // suc m₀ ≤ suc n₀ ↦ m₀ < suc n₀
				Cite(LessThanSucIffLessEq), // m₀ < suc n₀ ↦ m₀ ≤ n₀ — refl-shaped iff closes at the cite
			)
		}),
})}

// sucLessThanSucIff — < is invariant under suc — the mirror of SucLessEqSucIff,
// composing the same two bridges in the opposite order through the
// waypoint suc m ≤ n, again as two goal rewrites closing at the
// second cite.
var sucLessThanSucIff = sucLessThanSucIffThm{family.Add(registry.ProofEntry{
	Name: "sucLessThanSucIff",
	Key:  "prop_4ccda0769b341f14",
	Build: family.Theorem("∀m n:num. suc(m) < suc(n) ⇔ m < n",
		func(a *Argument, m, n Term) {
			a.Do(
				// The same two bridges, opposite order, each a goal rewrite:
				Cite(LessThanSucIffLessEq), // suc m₀ < suc n₀ ↦ suc m₀ ≤ n₀
				Cite(SucLessEqIffLessThan), // suc m₀ ≤ n₀ ↦ m₀ < n₀ — refl-shaped iff closes at the cite
			)
		}),
})}

// ZeroLessThanSuc — every successor is positive — the bridge
// LessThanSucIffLessEq rewrites 0 < suc n to 0 ≤ n, and ZeroLessEq supplies that.
// One section: the first cite strips the suc, the second closes the
// residual instance of ZeroLessEq at the cite.
//
// Chapter API rather than an internal step: it is ℕ's statement of
// positivity, and it is what an embedding chapter reaches for when a
// numeral has to be shown positive on the ℕ side of `&`
// (real_order_ring.ZeroLessThanOne is the first such reader).
var ZeroLessThanSuc = zeroLessThanSucThm{family.Add(registry.ProofEntry{
	Name: "ZeroLessThanSuc",
	Key:  "prop_c9f52f32a3a0f07",
	Build: family.Theorem("∀n:num. 0 < suc(n)",
		func(a *Argument, n Term) {
			a.Do(
				Cite(LessThanSucIffLessEq),
				Cite(ZeroLessEq),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The order axioms of ≤ and < on ℕ
// ---------------------------------------------------------------------------
//
// Holds LessEqRefl (with its one-line corollary LessEqOfEq),
// LessThanIrrefl, LessEqTrans, LessThanTrans,
// LessEqAntisym and LessThanAsym, plus the mixed-order corollaries —
// LessThanLessEqTrans, which chapters outside ℕ reach for, and the
// internal notEqualOfLessThan, lessEqLessThanTrans and lessThanLessEqAsym.

// LessEqRefl — ≤ is reflexive, by induction on n from LessEq's two
// recursion clauses: LessEqZeroClause and LessEqSucClause, the definitional internal
// entries (the recursion equations state them). One induction, one clause per branch.
var LessEqRefl = lessEqReflThm{family.Add(registry.ProofEntry{
	Name: "LessEqRefl",
	Key:  "prop_c1df2bc9f509331f",
	// Induct on the bound n.
	Build: family.Theorem("∀n:num. n ≤ n",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"0 ≤ 0 rewrites to 0 = 0 via the zero clause — refl, closes on the cite",
				Cite(LessEqZeroClause),
			)
			a.Step(
				"the suc clause turns suc n ≤ suc n into a disjunction with a "+
					"refl-true right disjunct — the refuter closes without the IH",
				Cite(LessEqSucClause),
				CnfRefute(),
			)
		}),
})}

// LessEqOfEq — an equation is a weak inequality: the one-line corollary
// of reflexivity. The equation is a rewrite, not a premise: rewriting
// m₀ by n₀ turns the goal into n₀ ≤ n₀, which IS LessEqRefl — no
// refutation runs. No induction, no case split.
var LessEqOfEq = lessEqOfEqThm{family.Add(registry.ProofEntry{
	Name: "LessEqOfEq",
	Key:  "prop_5d2f991c88317344",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m = n",
		},
		Conclusion: "m ≤ n",
	},
		func(a *Argument, m, n Term, eq Fact) {
			a.Show(
				"rewrite m₀ to n₀: the goal is n₀ ≤ n₀, reflexivity — closes at the cite",
				eq.Rw(),          // m₀ ≤ n₀ ↦ n₀ ≤ n₀
				Cite(LessEqRefl)) // n₀ ≤ n₀
		}),
})}

// LessThanIrrefl — < is irreflexive, by induction on n from LessThan's
// zero clause and suc-invariance — one induction.
var LessThanIrrefl = lessThanIrreflThm{family.Add(registry.ProofEntry{
	Name: "LessThanIrrefl",
	Key:  "prop_3da58f95c3787bf9",
	// Induct on the bound n. Both branches close at the cite: each cited
	// clause rewrites its matching atom away, leaving no refutation to run.
	Build: family.Theorem("∀n:num. ¬(n < n)",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"0 < 0 rewrites to ⊥ via the zero clause — closes on the cite",
				Cite(LessThanZeroClause),
			)
			a.Step(
				"the contraposed leaf is suc n < suc n ⊢ n < n, and "+
					"sucLessThanSucIff rewrites the hypothesis to the goal",
				Cite(sucLessThanSucIff),
			)
		}),
})}

// notEqualOfLessThan — a strict inequality separates its endpoints, the
// direct corollary of irreflexivity. A pure composition, no induction:
// under the hypothesis m₀ < n₀ the single ground instance
// LessThanIrrefl at n₀ is what the substitution m₀ = n₀ contradicts.
var notEqualOfLessThan = notEqualOfLessThanThm{family.Add(registry.ProofEntry{
	Name: "notEqualOfLessThan",
	Key:  "prop_6e2798145657f6eb",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m < n",
		},
		Conclusion: "m ≠ n",
	},
		func(a *Argument, m, n Term, lt Fact) { // lt: m₀ < n₀
			a.Show(
				"m₀ ≠ n₀ — under m₀ = n₀ the hypothesis becomes n₀ < n₀",
				By(Normalized, lt, At(LessThanIrrefl, n)))
		}),
})}

// LessEqTrans — ≤ is transitive, by induction on p from LessEq's two
// clause projections. Inducting on p (with m, n fixed frees) makes the
// IH exactly what the step needs, and the whole proof is one section.
var LessEqTrans = lessEqTransThm{family.Add(registry.ProofEntry{
	Name: "LessEqTrans",
	Key:  "prop_e42ad3f6745873e7",
	// Induct on p — m, n stay fixed frees; the induction keeps the
	// implication whole, so each branch gets m ≤ n and the p-side bound as
	// hypotheses and the IH as a resident implication.
	Build: family.Theorem(Statement{
		Binders: "∀m n p:num.",
		Hypotheses: []string{
			"m ≤ n",
			"n ≤ p",
		},
		Conclusion: "m ≤ p",
	},
		func(a *Argument, m, n, p Term) {
			a.Induct(p)
			a.Base(
				"n ≤ 0 forces n = 0 (zero clause); substituting into m ≤ n leaves m ≤ 0, the zero clause again",
				Cite(LessEqZeroClause),
				CnfRefute(),
			)
			a.Step(
				"the suc clause splits n ≤ suc p into n ≤ p and n = suc p",
				TrivialSimplify(),
				Expect(Chain(Cite(LessEqSucClause), Basic()),
					Case(
						"n ≤ p: the IH gives m ≤ p, which the suc clause lifts to m ≤ suc p",
						CnfRefute()),
					Case(
						"n = suc p: substituting into m ≤ n gives m ≤ suc p outright",
						CnfRefute()),
				),
			)
		}),
})}

// LessThanTrans — < is transitive, by induction on p from LessThan's
// two clause projections — LessEqTrans's < mirror. Inducting on p
// (with m, n fixed frees) makes the IH exactly what the step needs,
// and the whole proof is one section.
//
// Note the base-case asymmetry vs LessEqTrans: LessEq's zero clause is
// an equation (m ≤ 0 ⇔ m = 0) with substitution content, so its base
// still needs a refute after the cite; LessThan's is a pure negation,
// so the cite alone ends the branch.
var LessThanTrans = lessThanTransThm{family.Add(registry.ProofEntry{
	Name: "LessThanTrans",
	Key:  "prop_a173ced68484a466",
	// Induct on p — m, n stay fixed frees; the induction keeps the
	// implication whole, so each branch gets m < n and the p-side bound as
	// hypotheses and the IH as a resident implication.
	Build: family.Theorem(Statement{
		Binders: "∀m n p:num.",
		Hypotheses: []string{
			"m < n",
			"n < p",
		},
		Conclusion: "m < p",
	},
		func(a *Argument, m, n, p Term) {
			a.Induct(p)
			a.Base(
				"n < 0 is false by the zero clause — vacuous antecedent, closes on the cite",
				Cite(LessThanZeroClause),
			)
			a.Step(
				"n < suc p is n < p (IH + left disjunct of suc clause) or n = p (substitute into m < n)",
				Cite(LessThanSucClause),
				CnfRefute(),
			)
		}),
})}

// lessEqLessThanTrans — mixed transitivity, ≤ then <, and the composite is
// strict. A pure composition through the suc-bridge — no induction.
// The body spells the chain as three ground instances (read them in
// order: suc n₀ ≤ p₀, then suc m₀ ≤ suc n₀, then suc m₀ ≤ p₀) plus the
// closing bridge cite. SucLessEqSucIff is genuinely load-bearing:
// without it suc m ≤ suc n has no source and the chain has no left end.
var lessEqLessThanTrans = lessEqLessThanTransThm{family.Add(registry.ProofEntry{
	Name: "lessEqLessThanTrans",
	Key:  "prop_907d94b346f4beb4",
	Build: family.Theorem(Statement{
		Binders: "∀m n p:num.",
		Hypotheses: []string{
			"m ≤ n",
			"n < p",
		},
		Conclusion: "m < p",
	},
		// The trailing `_ Fact` absorbs the ⇒: the pair of order facts is
		// assumed at the boundary and the cites below land against it.
		func(a *Argument, m, n, p Term, _ Fact) {
			v := ops(a.Ctx())
			sucN, sucM := v.Suc(n), v.Suc(m)
			a.Do(
				// n₀ < p₀ ⇔ suc n₀ ≤ p₀.
				Cite(SucLessEqIffLessThan, n, p),
				// m₀ ≤ n₀ ⇔ suc m₀ ≤ suc n₀.
				Cite(SucLessEqSucIff, m, n),
				// suc m₀ ≤ suc n₀ ∧ suc n₀ ≤ p₀ ⇒ suc m₀ ≤ p₀.
				Cite(LessEqTrans, sucM, sucN, p),
				// (m < n) ⇔ (suc m ≤ n) read right-to-left carries that
				// ground bound back to the goal m₀ < p₀ — nothing is left
				// to search, so the cite closes and no refute is needed.
				Cite(SucLessEqIffLessThan),
			)
		}),
})}

// LessThanLessEqTrans — mixed transitivity the other way round, < then ≤ —
// lessEqLessThanTrans's mirror, and one cite shorter: the strict hypothesis is
// already on the left, so no suc-lift is needed. A pure
// composition through the suc-bridge — no induction. The body spells
// the chain as two ground instances (read them in order: suc m₀ ≤ n₀,
// then suc m₀ ≤ p₀) plus the closing bridge cite; the statement has no
// inductive content once the bridge exists.
var LessThanLessEqTrans = lessThanLessEqTransThm{family.Add(registry.ProofEntry{
	Name: "LessThanLessEqTrans",
	Key:  "prop_34e72b57349120ec",
	Build: family.Theorem(Statement{
		Binders: "∀m n p:num.",
		Hypotheses: []string{
			"m < n",
			"n ≤ p",
		},
		Conclusion: "m < p",
	},
		func(a *Argument, m, n, p Term, _ Fact) {
			sucM := ops(a.Ctx()).Suc(m)
			a.Do(
				// m₀ < n₀ ⇔ suc m₀ ≤ n₀.
				Cite(SucLessEqIffLessThan, m, n),
				// suc m₀ ≤ n₀ ∧ n₀ ≤ p₀ ⇒ suc m₀ ≤ p₀.
				Cite(LessEqTrans, sucM, n, p),
				// (m < n) ⇔ (suc m ≤ n) read right-to-left carries that
				// ground bound back to the goal m₀ < p₀ — nothing is left
				// to search, so the cite closes and no refute is needed.
				Cite(SucLessEqIffLessThan),
			)
		}),
})}

// LessEqAntisym — antisymmetry of ≤, stated as the characterization of
// equality by the two opposing inequalities. By induction on m whose
// step is a nested induction on n used purely as case analysis — the
// inner IH is never consumed; the outer IH (∀-quantified over n)
// closes the doubly-successor case. The whole proof is one nested
// induction.
var LessEqAntisym = lessEqAntisymThm{family.Add(registry.ProofEntry{
	Name: "LessEqAntisym",
	Key:  "prop_25a1e5cadd75238e",
	// Induct on the bound m — the step's IH must stay ∀-quantified over n
	// so the nested case analysis can use it at n.
	Build: family.Theorem("∀m n:num. m = n ⇔ m ≤ n ∧ n ≤ m",
		func(a *Argument) {
			m := a.Binder("m")
			// suc(m): witness term for grounding the zero clause in the
			// inner base.
			sucM := ops(a.Ctx()).Suc(m)
			a.Induct(m)
			a.Base(
				"0 = n ⇔ (0 ≤ n ∧ n ≤ 0) — n ≤ 0 is n = 0 (zero clause), and "+
					"under n = 0 the conjunct 0 ≤ n is the clause's reflexive instance",
				Cite(LessEqZeroClause),
				CnfRefute(),
			)
			a.Step(
				"suc m = n ⇔ (suc m ≤ n ∧ n ≤ suc m) — case analysis "+
					"on n by a nested induction (the inner IH goes unused)",
				a.Ctx().InductStep(Var("n", NumType),
					// suc_not_zero's first cite fires: it rewrites suc m = 0 to
					// ⊥, contraposing the iff into ground hyps, and is
					// consumed — the second cite re-arms it for the
					// refuter. Grounding the zero clause at suc m then
					// lets Basic rewrite suc m ≤ 0 into suc m = 0, where
					// suc_not_zero bites.
					Case(
						"both sides false — the zero clause turns suc m ≤ 0 into suc "+
							"m = 0, and suc_not_zero (cited twice) refutes both equations",
						Cite(LessEqZeroClause),
						Cite(peano.SucNotZero),
						Cite(peano.SucNotZero),
						// content-addressed grounding of the zero clause at
						// suc m (no positional hyp index — the re-arm
						// re-sorts hyps).
						GroundHyp(LessEqZeroClause, sucM),
						Basic(),
					),
					Case(
						"suc_injective and SucLessEqSucIff strip one suc from every atom, "+
							"leaving exactly the outer IH's instance at n — closes at the cite",
						Cite(peano.SucInjective),
						Cite(SucLessEqSucIff),
					),
				),
			)
		}),
})}

// LessThanAsym — asymmetry of <: it never holds both ways round. A
// pure composition of the two sibling order axioms — no induction. The
// body is one ground instance (transitivity at (m₀, n₀, m₀), whose
// conclusion m₀ < m₀ is the whole argument) plus the irreflexivity
// cite that contradicts it. The statement has no inductive content.
var LessThanAsym = lessThanAsymThm{family.Add(registry.ProofEntry{
	Name: "LessThanAsym",
	Key:  "prop_65a27c7574fc8071",
	Build: family.Theorem("∀m n:num. ¬(m < n ∧ n < m)",
		func(a *Argument, m, n Term) {
			a.Do(
				// Split the negated conjunction into its two hypotheses,
				// goal ⊥ — so the cites below land against ground hyps.
				TrivialSimplify(),
				// m₀ < n₀ ∧ n₀ < m₀ ⇒ m₀ < m₀.
				Cite(LessThanTrans, m, n, m),
				// ¬(n < n) contradicts that instance's conclusion — with
				// the waypoint ground there is nothing left to search, so
				// the cite closes the section and no refute is needed.
				Cite(LessThanIrrefl),
			)
		}),
})}

// lessThanLessEqAsym — mixed asymmetry: a strict and a non-strict inequality
// cannot oppose each other. Like LessThanAsym one member up, a pure
// composition of finished siblings — no induction. The body spells
// the descent to absurdity as
// three ground instances (read them in order: suc n₀ ≤ m₀, then
// suc n₀ ≤ n₀, then n₀ < n₀) plus the irreflexivity cite that
// contradicts the last. The statement has no inductive content.
var lessThanLessEqAsym = lessThanLessEqAsymThm{family.Add(registry.ProofEntry{
	Name: "lessThanLessEqAsym",
	Key:  "prop_6418fe955e4b254",
	Build: family.Theorem("∀n m:num. ¬(n < m ∧ m ≤ n)",
		func(a *Argument, n, m Term) {
			sucN := ops(a.Ctx()).Suc(n)
			a.Do(
				// Split the negated conjunction into its two hypotheses,
				// goal ⊥ — so the cites below land against ground hyps.
				TrivialSimplify(),
				// n₀ < m₀ ⇔ suc n₀ ≤ m₀.
				Cite(SucLessEqIffLessThan, n, m),
				// suc n₀ ≤ m₀ ∧ m₀ ≤ n₀ ⇒ suc n₀ ≤ n₀.
				Cite(LessEqTrans, sucN, m, n),
				// n₀ < n₀ ⇔ suc n₀ ≤ n₀ — read right-to-left, the absurdity.
				Cite(SucLessEqIffLessThan, n, n),
				// ¬(n < n) contradicts it — with the waypoint ground there
				// is nothing left to search, so the cite closes the section
				// and no refute is needed.
				Cite(LessThanIrrefl),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The totality/trichotomy tier of the ≤/< order on ℕ
// ---------------------------------------------------------------------------
//
// Holds LessEqTotal and LessThanTrichotomy, plus the internal
// mixed-totality lemma lessThanOrLessEq.

// LessEqTotal — ≤ is total: any two naturals are comparable. By
// induction on m whose step is a nested induction on n used purely as
// case analysis — the inner IH is never consumed; ZeroLessEq settles
// every leaf with a zero on one side, and suc-invariance reduces the
// doubly-successor leaf to the outer IH.
var LessEqTotal = lessEqTotalThm{family.Add(registry.ProofEntry{
	Name: "LessEqTotal",
	Key:  "prop_ae1d1ff3d19abdf2",
	// Induct on the bound m — the step's IH must stay ∀-quantified over n
	// so the nested case analysis can use it at n.
	Build: family.Theorem("∀m n:num. m ≤ n ∨ n ≤ m",
		func(a *Argument) {
			a.Induct("m")
			// ZeroLessEq is a bare positive factorial (not an iff): its cite
			// ⊤-rewrites the matching 0 ≤ · atom even under the residual
			// ∀n binder — positive-fact rewrites reach under binders,
			// iff rewrites do not — settling the disjunction at the
			// cite. Same in the inner base below.
			a.Base(
				"0 ≤ n ∨ n ≤ 0 — the left disjunct is ZeroLessEq, closes on the cite",
				Cite(ZeroLessEq),
			)
			a.Step(
				"suc m ≤ n ∨ n ≤ suc m — case analysis on n by a nested induction (the inner IH goes unused)",
				a.Ctx().InductStep(Var("n", NumType),
					Case(
						"suc m ≤ 0 ∨ 0 ≤ suc m — the right disjunct is ZeroLessEq, closes on the cite",
						Cite(ZeroLessEq),
					),
					// SucLessEqSucIff fires as a rewrite on both suc-headed
					// disjuncts and is consumed; the contraposed leaf
					// then resolves against the outer IH.
					Case(
						"suc m ≤ suc n ∨ suc n ≤ suc m — SucLessEqSucIff strips one "+
							"suc from both disjuncts, leaving the outer IH's instance at n",
						Cite(SucLessEqSucIff),
						CnfRefute(),
					),
				),
			)
		}),
})}

// LessThanTrichotomy — trichotomy of <: two naturals stand in exactly
// one of below, above, equal. A pure composition over totality — no
// induction (the statement has no inductive content of its own once ≤
// is known total):
//
//	LessEqTotal gives m ≤ n ∨ n ≤ m;
//	LessThanSucIffLessEq chained with LessThanSucClause decomposes the non-strict
//	order: m ≤ n ⇔ (m < n ∨ m = n);
//	decomposing both disjuncts of totality yields the
//	tri-disjunction (the n = m leftover orients to m = n by
//	symmetry of equality).
var LessThanTrichotomy = lessThanTrichotomyThm{family.Add(registry.ProofEntry{
	Name: "LessThanTrichotomy",
	Key:  "prop_83bb550970be2345",
	Build: family.Theorem("∀m n:num. m < n ∨ (n < m ∨ m = n)",
		func(a *Argument, m, n Term) {
			// Premise order is load-bearing: the resident bridge rewrites
			// the incoming clause's successor atom, so it lands as the
			// composed decomposition m ≤ n ⇔ (m < n ∨ m = n).
			a.Do(By(LessEqTotal, LessThanSucIffLessEq, LessThanSucClause))
		}),
})}

// lessThanOrLessEq — mixed totality: the strict and the non-strict order
// between two naturals already exhaust the cases. Like its sibling
// LessThanTrichotomy, a pure composition over totality — no induction:
//
//	LessEqTotal at (m, n) gives m ≤ n ∨ n ≤ m;
//	m ≤ n is the right disjunct — done;
//	LessThanSucIffLessEq chained with LessThanSucClause decomposes the non-strict
//	order, n ≤ m ⇔ (n < m ∨ n = m):
//	n < m is the left disjunct — done;
//	n = m folds the right disjunct into m ≤ m, which the same
//	decomposition at (m, m) settles by refl of its m = m disjunct
//	(so reflexivity needs no cite of its own — LessEqRefl is
//	subsumed by the decomposition instance).
var lessThanOrLessEq = lessThanOrLessEqThm{family.Add(registry.ProofEntry{
	Name: "lessThanOrLessEq",
	Key:  "prop_48badb73defc0bd4",
	Build: family.Theorem("∀n m:num. n < m ∨ m ≤ n",
		func(a *Argument, n, m Term) {
			// Premise order is load-bearing, as in LessThanTrichotomy: the
			// resident bridge composes with the incoming clause.
			a.Do(By(LessEqTotal, LessThanSucIffLessEq, LessThanSucClause))
		}),
})}

// ---------------------------------------------------------------------------
// The ≤/< duality bridges of the order on ℕ
// ---------------------------------------------------------------------------
//
// Chapter API: NotLessEq and NotLessThan (each order is the negation of
// the other's flipped-argument twin), LessEqSplit (the non-strict order
// decomposes into strict-or-equal), LessEqOfLessThan (< implies ≤), and
// the positivity triangle — PosIffNonzero (positivity IS non-zeroness),
// OneLessEqIffPos (and IS the unit bound), OneLessEqIffNonzero (the
// remaining side, stated once for its consumers).

// NotLessEq — the negation of ≤ IS the flipped strict order. A pure
// composition of the mixed totality with the mixed
// antisymmetry — no induction (the statement has no inductive content
// once lessThanOrLessEq and lessThanLessEqAsym exist). Each direction is one ground
// instance: the totality disjunction supplies the wanted side, the
// asymmetry conjunction refutes having both.
var NotLessEq = notLessEqThm{family.Add(registry.ProofEntry{
	Name: "NotLessEq",
	Key:  "prop_567363e3e08c9985",
	Build: family.Theorem("∀m n:num. ¬(m ≤ n) ⇔ n < m",
		func(a *Argument, m, n Term) {
			a.Do(By(
				Normalized,
				// ⇒: ¬(m ≤ n) kills the right disjunct — n < m remains.
				At(lessThanOrLessEq, n, m), // n₀ < m₀ ∨ m₀ ≤ n₀
				// ⇐: n < m kills the left conjunct's option — ¬(m ≤ n) remains.
				At(lessThanLessEqAsym, n, m), // ¬(n₀ < m₀ ∧ m₀ ≤ n₀)
			))
		}),
})}

// NotLessThan — the negation of < IS the flipped non-strict order —
// NotLessEq's argument-symmetric twin, mutatis mutandis: the same pair
// of siblings grounded at the mirrored instance.
var NotLessThan = notLessThanThm{family.Add(registry.ProofEntry{
	Name: "NotLessThan",
	Key:  "prop_a14982bab8179bd",
	Build: family.Theorem("∀m n:num. ¬(m < n) ⇔ n ≤ m",
		func(a *Argument, m, n Term) {
			a.Do(By(
				Normalized,
				At(lessThanOrLessEq, m, n),   // m₀ < n₀ ∨ n₀ ≤ m₀
				At(lessThanLessEqAsym, m, n), // ¬(m₀ < n₀ ∧ n₀ ≤ m₀)
			))
		}),
})}

// LessEqSplit — the non-strict order splits as strict-or-equal — the
// named composed decomposition that the totality members
// (LessThanTrichotomy, lessThanOrLessEq) synthesized on-the-fly in their hyp
// lists. A composition of two suc-bridges through the common waypoint
// m < suc n, spelled as goal rewrites — each cite fires on the
// current goal and lands on the next link, and the second leaves the
// goal refl-shaped, closing at the cite.
var LessEqSplit = lessEqSplitThm{family.Add(registry.ProofEntry{
	Name: "LessEqSplit",
	Key:  "prop_c8b73c3c62a0d819",
	Build: family.Theorem("∀m n:num. m ≤ n ⇔ m < n ∨ m = n",
		func(a *Argument, m, n Term) {
			a.Do(
				Cite(LessThanSucIffLessEq), // m₀ ≤ n₀ ↦ m₀ < suc n₀ (the waypoint)
				Cite(LessThanSucClause),    // m₀ < suc n₀ ↦ m₀ < n₀ ∨ m₀ = n₀ — closes at the cite
			)
		}),
})}

// LessEqOfLessThan — the strict order refines the non-strict — one direction of
// the LessEqSplit decomposition, at one ground instance.
var LessEqOfLessThan = lessEqOfLessThanThm{family.Add(registry.ProofEntry{
	Name: "LessEqOfLessThan",
	Key:  "prop_b0f4880f41ce361c",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m < n",
		},
		Conclusion: "m ≤ n",
	},
		func(a *Argument, m, n Term, lt Fact) { // lt: m₀ < n₀
			a.Show(
				"m₀ ≤ n₀: the strict order is the split's left disjunct",
				By(lt, At(LessEqSplit, m, n))) // m₀ ≤ n₀ ⇔ (m₀ < n₀ ∨ m₀ = n₀)
		}),
})}

// PosIffNonzero — positivity IS non-zeroness on ℕ. Three ground
// instances at (0, n), no induction — the ≤-split read at m = 0,
// where the equal disjunct becomes the disequality the statement
// negates. All three deps are load-bearing: dropping any leaves the
// ⇐ direction or the 0 ≤ n premise open.
var PosIffNonzero = posIffNonzeroThm{family.Add(registry.ProofEntry{
	Name: "PosIffNonzero",
	Key:  "prop_1633d223328d3761",
	Build: family.Theorem("∀n:num. n ≠ 0 ⇔ 0 < n",
		func(a *Argument, n Term) {
			zero := a.Ctx().Numeral(0)
			a.Do(By(
				Normalized,
				At(LessEqSplit, zero, n),        // 0 ≤ n₀ ⇔ (0 < n₀ ∨ 0 = n₀)
				At(ZeroLessEq, n),               // 0 ≤ n₀ — discharges the premise
				At(notEqualOfLessThan, zero, n), // 0 < n₀ ⇒ 0 ≠ n₀ — orients the ⇐ direction
			))
		}),
})}

// OneLessEqIffPos — the third face of positivity on ℕ. `n ≠ 0`,
// `0 < n` and `1 ≤ n` are one fact here; PosIffNonzero above relates
// the first two, this relates the last two, and OneLessEqIffNonzero
// below states the remaining side.
//
// It exists for the CONSUMERS, and that is the whole argument for it.
// Every order law in this chapter is stated at `suc(n)`, while a
// consumer in another chapter arrives holding the numeral `1` —
// real_order_ring's ZeroLessThanOne, and the words chapters wherever a
// nonzero width or range is "at least one" — and would otherwise pay
// its own `1 = suc(0)` rewrite to meet them. That bridge is performed
// here, once, and the consumers cite across it.
//
// Stated `1 ≤ n ⇔ 0 < n` rather than `1 ≤ n ⇔ n ≠ 0`: both are true and
// both are one cite from the other via PosIffNonzero, but the ORDER
// form is what the consumers need — each of them is trying to turn a
// numeral bound into a strict comparison or back, and the ≠ form would
// send them through PosIffNonzero to finish.
var OneLessEqIffPos = oneLessEqIffPosThm{family.Add(registry.ProofEntry{
	Name: "OneLessEqIffPos",
	Key:  "prop_73d128642ae85b1f",
	Build: family.Theorem("∀n:num. 1 ≤ n ⇔ 0 < n",
		func(a *Argument, n Term) {
			zero := a.Ctx().Numeral(0)
			one := a.Have(
				"the literal 1 read as a successor, which is the form this chapter's order laws are stated in",
				"1 = suc(0)",
				Cite(nat_arith.OneIsSucZero))
			a.Do(
				Cite(SucLessEqIffLessThan, zero, n), // 0 < n₀ ⇔ suc(0) ≤ n₀
				// ↦ suc(0) ≤ n₀ ⇔ 0 < n₀ — the numeral read into successor
				// form, which is the one rewrite this member exists to absorb.
				one.Rw(),
				Basic(),
			)
		}),
})}

// OneLessEqIffNonzero — the side of the positivity triangle the two
// members above leave open, closing it: PosIffNonzero relates the
// disequality to the strict order and OneLessEqIffPos relates the
// strict order to the numeral bound, so their composition — stated
// here once — relates the remaining pair. A consumer holding a numeral
// bound and wanting the disequality (or back) spends one cite instead
// of rebuilding the two-cite bridge.
var OneLessEqIffNonzero = oneLessEqIffNonzeroThm{family.Add(registry.ProofEntry{
	Name: "OneLessEqIffNonzero",
	Key:  "prop_eab7eb69e56f023c",
	Build: family.Theorem("∀n:num. 1 ≤ n ⇔ n ≠ 0",
		func(a *Argument) {
			a.Show(
				"compose the triangle's two proved sides through the strict order",
				By(OneLessEqIffPos, PosIffNonzero))
		}),
})}

// ---------------------------------------------------------------------------
// The compatibility of ≤ / < with addition
// ---------------------------------------------------------------------------
//
// Two shapes carry the tier: the existence characterizations
// LessEqExists / LessThanExists (each order IS the existence of an
// additive shift) are the inductive core; the internal primitive
// leftMonoAdd (left monotonicity of + on ≤) sits below LessEqAdd2
// and drives every downstream monotonicity. Above them a composition
// layer — LessEqAdd, LessEqAddCancel, LessThanAddCancel (its strict
// twin), LessEqAddRightCancel (right mirror), LessEqLessThanAdd2 /
// lessThanLessEqAdd2 (mixed strict / non-strict pairwise),
// and LessThanAdd2 (strict-strict) — all pure 3–7-tactic Chains.

// LessEqExists — the existence
// characterization of ≤ (the standard definition of ≤ over ℕ). By
// induction on n from the two LE clause projections plus nat_arith's zero-
// summand facts and suc's injectivity — one section.
var LessEqExists = lessEqExistsThm{family.Add(registry.ProofEntry{
	Name: "LessEqExists",
	Key:  "prop_5cb5f2902a536b69",
	// Outer induction on n. The binder order puts n — the induction
	// variable — outermost, so the step's IH stays ∀m-quantified. Frees
	// minted by the tactics: `m_0` from StripQuant on ∀m in the step case,
	// `d_0` from StripQuant on ∃d in the ⇐ branch of the step's SplitIff.
	Build: family.Theorem("∀n m:num. m ≤ n ⇔ ∃d:num. n = m + d",
		func(a *Argument) {
			n := a.Binder("n")
			m0 := Var("m_0", NumType)
			d0 := Var("d_0", NumType)
			// ByCaseStep wants a Prop-side term for the discriminant `m_0 ≤ n`.
			v := ops(a.Ctx())

			a.Induct(n)
			a.Base(
				"m ≤ 0 and ∃d. 0 = m + d both say m = 0",
				Cite(LessEqZeroClause),
				Cite(nat_arith.AddEqZero),
				CnfRefute(),
			)
			a.Step(
				"m ≤ suc n ⇔ ∃d. suc n = m + d, each direction through the suc clause and the hypothesis at n",
				StripQuant(),
				Cite(LessEqSucClause),
				Cite(nat_arith.AddClauses),
				SplitIff(
					Forward(
						"m ≤ suc n produces a shift — case-split on whether m ≤ n already holds",
						ByCaseStep(v.LessEq(m0, n),
							Case(
								"m ≤ n: the IH gives d with n = m + d, and suc lifts it to suc n = m + suc d",
								CnfRefute()),
							Case(
								"¬(m ≤ n): the suc clause forces m = suc n, so d = 0 suffices",
								CnfRefute()),
						),
					),
					Backward(
						"a shift suc n = m + d bounds m by suc n — strip d, then induct on it as case analysis",
						StripQuant(),
						a.Ctx().InductStep(d0,
							Case(
								"d = 0: suc n = m, so the suc clause's equal disjunct absorbs",
								CnfRefute()),
							Case(
								"d = suc d': suc_injective peels the suc, leaving the outer IH's shift at n",
								Cite(peano.SucInjective),
								CnfRefute(),
							),
						),
					),
				),
			)
		}),
})}

// LessThanExists — the strict
// order IS the existence of a positive shift — m < n iff n strictly
// exceeds m in the +-order (via a witness d whose successor is the
// excess). The < twin of LessEqExists with suc(d) in place of d
// (strict shift = at-least-one gap).
//
// By induction on n from the two LT clause projections plus nat_arith's
// Clauses and suc_not_zero / suc_injective from the num foundation — one section.
var LessThanExists = lessThanExistsThm{family.Add(registry.ProofEntry{
	Name: "LessThanExists",
	Key:  "prop_1d439ece801a770d",
	// Outer induction on n — the binder order puts the induction variable
	// outermost, so the step's IH stays ∀m-quantified. Nested induction on
	// d₀ in the ⇐ leaf.
	Build: family.Theorem("∀n m:num. m < n ⇔ ∃d:num. n = m + suc(d)",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"both sides are false: nothing is below 0, and m + suc(d) is a successor, never 0",
				Cite(LessThanZeroClause),
				Cite(nat_arith.AddClauses),
				Cite(peano.SucNotZero),
				CnfRefute(),
			)
			a.Step(
				"m < suc n ⇔ ∃d. suc n = m + suc(d), each direction through the suc clause and the hypothesis at n",
				Cite(LessThanSucClause),
				Cite(nat_arith.AddClauses),
				Cite(peano.SucInjective),
				StripQuant(),
				SplitIff(
					Forward(
						"m < suc n produces a strict shift — the outer IH picks d on the m < n disjunct, d = 0 fits m = n",
						CnfRefute()),
					Backward(
						"a strict shift suc n = m + suc d puts m below suc n — strip d, then induct on it as case analysis",
						StripQuant(),
						a.Ctx().InductStep(Var("d_0", NumType),
							Case(
								"d = 0: suc n = suc m, so m = n — the suc clause's equal disjunct",
								CnfRefute()),
							Case(
								"d = suc d': the outer IH lifts the residual shift to m < n",
								CnfRefute()),
						),
					),
				),
			)
		}),
})}

// leftMonoAdd — left-side monotonicity
// of + on ≤. Internal — the paired form is LessEqAdd2 below;
// downstream, LessEqAdd / LessEqAddCancel / their mirrors re-consume
// this one-sided form directly.
//
// By induction on n from nat_arith.AddClauses + SucLessEqSucIff — one induction.
var leftMonoAdd = leftMonoAddThm{family.Add(registry.ProofEntry{
	Name: "leftMonoAdd",
	Key:  "prop_24082f8592c0d7d4",
	// Induct on the shift n — the last binder, so the residual ∀m∀p stays
	// quantified in the IH and the step can re-use it at the same m, p.
	Build: family.Theorem(Statement{
		Binders: "∀m p n:num.",
		Hypotheses: []string{
			"m ≤ p",
		},
		Conclusion: "m + n ≤ p + n",
	},
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"n = 0 — the shift vanishes on both sides and the goal IS the hypothesis",
				func(b *Argument) {
					b.Fix()          // m₀
					b.Fix()          // p₀
					le := b.Assume() // m₀ ≤ p₀
					b.Show(
						"adding 0 to either side changes neither, so what is left standing is the hypothesis",
						By(Normalized, le, nat_arith.AddClauses))
				},
			)
			a.Step(
				"n = suc n₀ — both SUCs come outward, and stripping them off the ≤ leaves exactly the IH",
				func(b *Argument, ih Fact) { // ∀m p. m ≤ p ⇒ m + n₀ ≤ p + n₀
					b.Fix()          // m₀
					b.Fix()          // p₀
					le := b.Assume() // m₀ ≤ p₀
					b.Show(
						"the suc clause carries a suc out of each sum, and "+
							"stripping the two off the ≤ leaves the IH at this same pair",
						By(ih, le, nat_arith.AddClauses, SucLessEqSucIff))
				},
			)
		}),
})}

// LessEqAdd2 — addition preserves ≤ pairwise. A composition of
// leftMonoAdd applied twice — once on each summand — chained through
// LessEqTrans at the midpoint p + n; nat_arith.AddSym re-orients the
// second application's sums so both land on the midpoint. The
// single-∀-var monotonicity lemma carries the inductive content; the
// pairwise theorem is the ground chain below.
var LessEqAdd2 = lessEqAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqAdd2",
	Key:  "prop_ad6cdd7c0070bd85",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p q:num.",
			Hypotheses: []string{
				"m ≤ p",
				"n ≤ q",
			},
			Conclusion: "m + n ≤ p + q",
		},
		func(a *Argument, m, n, p, q Term, bounds Fact) { // bounds: m₀ ≤ p₀ ∧ n₀ ≤ q₀
			v := ops(a.Ctx())

			// The three points of the chain — the middle one is the
			// waypoint both monotonicity instances are arranged around.
			mPlusN := v.Add(m, n) // m₀ + n₀
			pPlusN := v.Add(p, n) // p₀ + n₀ — the midpoint
			pPlusQ := v.Add(p, q) // p₀ + q₀

			a.Show(
				"m₀ + n₀ ≤ p₀ + q₀ — each hypothesis shifted by the "+
					"other pair's summand, then chained through the midpoint",
				By(
					bounds,
					At(leftMonoAdd, m, p, n),   // m₀ ≤ p₀ ⇒ m₀ + n₀ ≤ p₀ + n₀
					At(leftMonoAdd, n, q, p),   // n₀ ≤ q₀ ⇒ n₀ + p₀ ≤ q₀ + p₀
					At(nat_arith.AddSym, p, n), // p₀ + n₀ = n₀ + p₀
					At(nat_arith.AddSym, q, p), // q₀ + p₀ = p₀ + q₀
					At(LessEqTrans, mPlusN, pPlusN, pPlusQ)))
		}),
})}

// LessEqAdd — non-strict monotonicity of + on
// the right. One cite through the ≤-as-existence bridge — no
// induction:
//
//	LessEqExists at (m+n, m) rewrites m ≤ (m + n) to ∃d. m + n = m + d,
//	which d := n satisfies as an identity.
var LessEqAdd = lessEqAddThm{family.Add(registry.ProofEntry{
	Name: "LessEqAdd",
	Key:  "prop_c1ffe9602d5733fb",
	Build: family.Theorem("∀m n:num. m ≤ m + n",
		func(a *Argument, m, n Term) {
			a.Do(
				Cite(LessEqExists),
				CnfRefute(),
			)
		}),
})}

// LessEqAddLeft — LessEqAdd with the summands exchanged: a number is
// at most itself plus anything added on the LEFT. The sum commutes, so
// rewriting m + n to n + m leaves n ≤ n + m, which LessEqAdd states.
var LessEqAddLeft = lessEqAddLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddLeft",
	Key:  "prop_1f296a6b22512ef0",
	Build: family.Theorem("∀m n:num. n ≤ m + n",
		func(a *Argument, m, n Term) {
			commuted := a.Have(
				"the sum commutes",
				"m + n = n + m",
				Cite(nat_arith.AddSym))
			a.Do(commuted.Rw(), Cite(LessEqAdd))
		}),
})}

// LessEqAddCancel — left
// summands cancel through ≤ (both directions). Unlike a one-sided
// monotonicity, the ⇐ direction needs true cancellation — LessEqExists
// carries the ≤/+ interface (n ≤ p ⇔ ∃d. p = n + d) and
// nat_arith.AddEqLCancel carries the cancellation content
// (n = p ⇔ m + n = m + p). No induction:
//
//	n ≤ p ⇔ ∃d. p = n + d (LessEqExists at (p, n))
//	(m + n) ≤ (m + p) ⇔ ∃d. m + p = (m + n) + d (LessEqExists at (m+p, m+n))
//	p = n + d ⇔ m + p = m + (n + d) (nat_arith.AddEqLCancel at m)
//	m + (n + d) = (m + n) + d (nat_arith.AddAssoc)
//
// LessEqExists is grounded at BOTH sides of the ⇔ so the refuter has
// both ∃-form equivalences resident alongside the two rewriters.
var LessEqAddCancel = lessEqAddCancelThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddCancel",
	Key:  "prop_dd7ac3d3409b99de",
	Build: family.Theorem(
		"∀m n p:num. m + n ≤ m + p ⇔ n ≤ p",
		func(a *Argument, m, n, p Term) {
			v := ops(a.Ctx())
			a.Do(By(
				At(LessEqExists, p, n),                     // n₀ ≤ p₀ ⇔ ∃d. p₀ = n₀ + d
				At(LessEqExists, v.Add(m, p), v.Add(m, n)), // m₀+n₀ ≤ m₀+p₀ ⇔ ∃d. m₀+p₀ = (m₀+n₀)+d
				nat_arith.AddAssoc,
				nat_arith.AddEqLCancel,
			))
		}),
})}

// LessThanAddCancel — the strict companion of LessEqAddCancel: a common
// left summand cancels through <. Pure order algebra, no induction:
// the strict order is the negated flipped ≤ (NotLessEq), so
// m + n < m + p is ¬(m + p ≤ m + n), LessEqAddCancel cancels m
// through that ≤ to ¬(p ≤ n), and NotLessEq once more — on p ≤ n —
// reads that as n < p.
var LessThanAddCancel = lessThanAddCancelThm{family.Add(registry.ProofEntry{
	Name: "LessThanAddCancel",
	Key:  "prop_460c330ae57d12eb",
	Build: family.Theorem(
		"∀m n p:num. m + n < m + p ⇔ n < p",
		func(a *Argument, m, n, p Term) {
			v := ops(a.Ctx())
			mN := v.Add(m, n) // m₀ + n₀
			mP := v.Add(m, p) // m₀ + p₀
			a.Show(
				"m₀ + n₀ < m₀ + p₀ is ¬(m₀ + p₀ ≤ m₀ + n₀); cancel m₀ through that ≤ and negate what it leaves",
				By(
					Normalized,
					At(NotLessEq, mP, mN),        // ¬(m₀ + p₀ ≤ m₀ + n₀) ⇔ m₀ + n₀ < m₀ + p₀
					At(LessEqAddCancel, m, p, n), // m₀ + p₀ ≤ m₀ + n₀ ⇔ p₀ ≤ n₀
					At(NotLessEq, p, n)))         // ¬(p₀ ≤ n₀) ⇔ n₀ < p₀
		}),
})}

// LessEqLessThanAdd2 — the mixed
// pairwise addition-monotonicity. Pure composition through the
// suc-bridge over the ≤-pairwise monotonicity — no induction:
//
//	assume n < q and m ≤ p;
//	SucLessEqIffLessThan rewrites n < q into suc n ≤ q, and mirrored,
//	 (m + n) < (p + q) into suc(m + n) ≤ p + q;
//	LessEqAdd2 chains m ≤ p and suc n ≤ q into m + suc n ≤ p + q;
//	nat_arith.AddClauses's suc-clause identifies m + suc n with suc(m + n).
var LessEqLessThanAdd2 = lessEqLessThanAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqLessThanAdd2",
	Key:  "prop_b42005323d680de8",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p q:num.",
			Hypotheses: []string{
				"m ≤ p",
				"n < q",
			},
			Conclusion: "m + n < p + q",
		},
		func(a *Argument, m, n, p, q Term, bounds Fact) { // bounds: m₀ ≤ p₀ ∧ n₀ < q₀
			v := ops(a.Ctx())

			a.Show(
				"m₀ + n₀ < p₀ + q₀ — both strict atoms cross the suc-bridge, "+
					"and the ≤-pairwise monotonicity closes the middle",
				By(
					Normalized,
					bounds,
					// The suc-bridge on the hypothesis and on the goal.
					At(SucLessEqIffLessThan, n, q),
					At(SucLessEqIffLessThan, v.Add(m, n), v.Add(p, q)),
					At(LessEqAdd2, m, v.Suc(n), p, q),
					// The simp pack's k + suc l clause identifies m₀ + suc n₀
					// with suc(m₀ + n₀) — taken whole, as a rewrite set.
					nat_arith.AddClauses))
		}),
})}

// LessEqAddRightCancel — right
// cancellation of + through ≤. nat_arith.AddSym flips the (·+p)-form summands
// into (p+·) form, reducing the goal to LessEqAddCancel. Composition-
// only, no induction:
//
//	(m + p) ≤ (n + p) ⇔ (p + m) ≤ (p + n) nat_arith.AddSym rewrites each side
//	(p + m) ≤ (p + n) ⇔ (m ≤ n) LessEqAddCancel at (p, m, n)
var LessEqAddRightCancel = lessEqAddRightCancelThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddRightCancel",
	Key:  "prop_29f4f581d3625a1c",
	Build: family.Theorem(
		"∀m n p:num. m + p ≤ n + p ⇔ m ≤ n",
		func(a *Argument, m, n, p Term) {
			a.Do(By(
				nat_arith.AddSym,             // rewrite set: flips both goal sums into (p₀ + ·) form
				At(LessEqAddCancel, p, m, n), // p₀ + m₀ ≤ p₀ + n₀ ⇔ m₀ ≤ n₀
			))
		}),
})}

// lessThanLessEqAdd2 — the mixed
// pairwise addition-monotonicity with the STRICT inequality on the
// LEFT summand. The nat_arith.AddSym mirror of LessEqLessThanAdd2: LessEqLessThanAdd2 carries the
// strict side on the second summand, so grounding it at swapped
// witnesses and rewriting through nat_arith.AddSym yields our goal. No
// induction:
//
//	LessEqLessThanAdd2 at (m, p, n, q) — m < p ∧ n ≤ q ⇒ (n + m) < (q + p);
//	nat_arith.AddSym rewrites (m + n) ↔ (n + m) and (p + q) ↔ (q + p).
var lessThanLessEqAdd2 = lessThanLessEqAdd2Thm{family.Add(registry.ProofEntry{
	Name: "lessThanLessEqAdd2",
	Key:  "prop_1d61314d467e6887",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p q:num.",
			Hypotheses: []string{
				"m < p",
				"n ≤ q",
			},
			Conclusion: "m + n < p + q",
		},
		func(a *Argument, m, n, p, q Term, bounds Fact) { // bounds: m₀ < p₀ ∧ n₀ ≤ q₀
			a.Show(
				"m₀ + n₀ < p₀ + q₀ — the sibling at swapped witnesses, re-oriented onto the goal's spelling",
				By(
					bounds,
					// The sibling at swapped witnesses: n₀ ≤ q₀ ∧ m₀ < p₀ ⇒
					// n₀ + m₀ < q₀ + p₀.
					At(LessEqLessThanAdd2, n, m, q, p),
					At(nat_arith.AddSym, n, m), // n₀ + m₀ = m₀ + n₀
					At(nat_arith.AddSym, q, p), // q₀ + p₀ = p₀ + q₀
				))
		}),
})}

// LessThanAdd2 — the
// strict-strict pairwise addition-monotonicity. The strict-strict
// case reduces to lessThanLessEqAdd2 (m < p ∧ n ≤ q ⇒ m+n < p+q) by weakening
// the second strict inequality — LessEqOfLessThan collapses n<q to n≤q, and
// lessThanLessEqAdd2 does the rest. No induction:
//
//	n < q ⇒ n ≤ q LessEqOfLessThan at (n, q)
//	m < p ∧ n ≤ q ⇒ (m + n) < (p + q) lessThanLessEqAdd2 at (m, n, p, q)
var LessThanAdd2 = lessThanAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessThanAdd2",
	Key:  "prop_c444442aa79acb89",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p q:num.",
			Hypotheses: []string{
				"m < p",
				"n < q",
			},
			Conclusion: "m + n < p + q",
		},
		func(a *Argument, m, n, p, q Term, bounds Fact) { // bounds: m₀ < p₀ ∧ n₀ < q₀
			a.Show(
				"m₀ + n₀ < p₀ + q₀ — weaken the second strict bound, then apply the mixed pairwise law",
				By(
					bounds,
					At(LessEqOfLessThan, n, q),         // n₀ < q₀ ⇒ n₀ ≤ q₀
					At(lessThanLessEqAdd2, m, n, p, q), // m₀ < p₀ ∧ n₀ ≤ q₀ ⇒ m₀ + n₀ < p₀ + q₀
				))
		}),
})}

// ---------------------------------------------------------------------------
// The order along a map
// ---------------------------------------------------------------------------
//
// A strictly increasing map of ℕ reaches every bound the identity does —
// what makes the indices of a subsequence reach every tail — and a map
// that rises at every step keeps the strict order between any two
// indices, which is what makes a subsequence of a subsequence one.

// LessEqStrictlyIncreasing — a strictly increasing map of ℕ never falls
// below the identity.
//
// By induction on n: f(0) is no lower than 0, the bottom element; at the
// step the bound at n and the climb from f(n) to f(n + 1) put n strictly
// below f(n + 1), and a strict bound is the successor's bound.
var LessEqStrictlyIncreasing = lessEqStrictlyIncreasingThm{family.Add(registry.ProofEntry{
	Name: "LessEqStrictlyIncreasing",
	Key:  "prop_e1442ee0176077d0",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → num). ∀n:num.",
		Hypotheses: []string{
			"∀n:num. f(n) < f(n + 1)",
		},
		Conclusion: "n ≤ f(n)",
	},
		func(a *Argument, f *Arrow[Nat, Nat], increasing Fact) {
			a.Induct("n")
			a.Base(
				"zero is the bottom element of ≤",
				By(ZeroLessEq))
			a.Step(
				"f(n + 1) lies above f(n), hence strictly above n, and n + 1 is the successor",
				func(b *Argument, ih Fact) {
					n, next := b.TermAs[Nat]("n"), b.TermAs[Nat]("n + 1")
					strict := b.Have(
						"the IH at n, then the climb from f(n) to f(n + 1)",
						"n < f(n + 1)",
						By(ih, increasing.At(n), lessEqLessThanTrans.At(n, f.Apply(n), f.Apply(next))))
					// Once Add1 equates the step's suc(n) with the statement's n + 1,
					// the close is a normalization: spelled Normalized, it records
					// no refutation.
					b.Show(
						"suc(n) is n + 1, and a strict bound is the successor's bound",
						By(Normalized, strict, nat_arith.Add1.At(n), SucLessEqIffLessThan.At(n, f.Apply(next))))
				})
		}),
})}

// LessThanStrictlyIncreasing — a map of ℕ that rises at every step rises
// between any two indices: m < n gives f(m) < f(n).
//
// By induction on n: no index lies below 0, and below n + 1 lies n itself,
// where the bound is the step f(n) < f(n + 1), or an index below n, where
// the induction hypothesis gives f(m) < f(n) and the step carries it one
// index further.
var LessThanStrictlyIncreasing = lessThanStrictlyIncreasingThm{family.Add(registry.ProofEntry{
	Name: "LessThanStrictlyIncreasing",
	Key:  "prop_975a41eda78a1c5a",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → num). ∀m n:num.",
		Hypotheses: []string{
			"∀k:num. f(k) < f(k + 1)",
			"m < n",
		},
		Conclusion: "f(m) < f(n)",
	},
		func(a *Argument, f *Arrow[Nat, Nat], increasing Fact, m *Expr[Nat]) {
			a.Induct("n")
			a.Base(
				"no index lies below 0",
				ByArith())
			a.Step(
				"f(n) < f(n + 1) carries the bound one index further",
				func(b *Argument, ih Fact) {
					below := b.Assume()
					n := b.TermAs[Nat]("n")
					b.Cases(b.Term("m = n"))
					b.When(
						"at m = n the bound is the step f(n) < f(n + 1) itself",
						func(c *Argument, same Fact) {
							c.Show(
								"f(m) = f(n) < f(n + 1)",
								ByArith(same, increasing.At(n), nat_arith.Add1.At(n)))
						})
					b.Otherwise(
						"else m lies below n, where the induction hypothesis gives f(m) < f(n)",
						func(c *Argument, other Fact) {
							c.Show(
								"so f(m) < f(n) < f(n + 1)",
								ByArith(other, below, ih, increasing.At(n), nat_arith.Add1.At(n)))
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// The compatibility of ≤ / < with multiplication
// ---------------------------------------------------------------------------
//
// Order statements about products become equations between sums via
// the ≤/+ existence characterizations; the nat_arith distributivity
// laws and the ≤/+ interface finish. The one induction is the
// factorial's, a product whose factors grow in number with its
// argument: it climbs one factor at a time.

// LessEqMulCancel — a common left factor cancels through ≤, up to the
// degenerate zero factor that erases the comparison. Both directions
// ride the ≤-as-existence bridge; neither needs induction:
//
//	⇐, m = 0: Mul's zero clause turns m₀·n₀ into 0, and ZeroLessEq
//	 gives 0 ≤ m₀·p₀.
//	⇐, n ≤ p: LessEqExists gives p = n + d; LeftAddDistrib turns
//	 m·p into m·n + m·d, and LessEqAdd closes m·n ≤ m·n + m·d.
//	⇒: with ¬(n ≤ p), NotLessEq gives p < n, so LessThanExists
//	 gives n = p + suc(d) — a STRICT shift. Distributing,
//	 the hypothesis m·n ≤ m·p reads m·p + m·suc(d) ≤ m·p + 0
//	 (AddClauses' right-identity), which LessEqAddCancel
//	 cancels to m·suc(d) ≤ 0, i.e. m·suc(d) = 0 by
//	 LessEqZeroClause. MulEqZero factors that as m = 0 ∨
//	 suc(d) = 0, and suc_not_zero kills the second disjunct.
var LessEqMulCancel = lessEqMulCancelThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulCancel",
	Key:  "prop_9fe162bd51a21d1d",
	// Split the ⇔; each direction case-splits once and obtains one
	// ∃-shift witness d₀.
	Build: family.Theorem(
		"∀m n p:num. m * n ≤ m * p ⇔ m = 0 ∨ n ≤ p",
		func(a *Argument, m *TermWrapper, n, p Term) {
			// nat_arith.Mul is a two-clause conjunction row; cite it RAW so
			// eqSimplify sees the two clauses as separate rewriting facts
			// (see README §"Reading the proofs"). Every other cite here
			// takes the installable normalized form.
			// AddClauses is consumed whole by the refuter (only its
			// right-identity clause m = m + 0 is load-bearing), so the
			// normalized shared-∀ form is fine here — no eqSimplify
			// conjunct-splitting is asked of it.
			v := ops(a.Ctx())

			mP := v.Mul(m, p) // m₀ * p₀ — the smaller product

			a.Iff()
			a.Forward(
				"m₀·n₀ ≤ m₀·p₀ ⊢ m₀ = 0 ∨ n₀ ≤ p₀ — split on whether n₀ ≤ p₀ already holds",
				// We may assume ¬(n₀ ≤ p₀): a strict shift
				// n₀ = p₀ + suc(d₀) then squeezes m₀·suc(d₀) to 0,
				// forcing m₀ = 0.
				Unless(
					v.LessEq(n, p),
					"n₀ ≤ p₀: the right disjunct of the goal",
					TrivialNormalized(),
				),
				Derive(func(b *Argument) {
					bound := b.Hyp("m₀ * n₀ ≤ m₀ * p₀")
					notLe := b.Hyp("¬(n₀ ≤ p₀)")
					dw, shift := b.Obtain(
						"¬(n₀ ≤ p₀) is p₀ < n₀, which realizes a STRICT gap suc(d)",
						"∃d:num. n₀ = p₀ + suc(d)",
						By(notLe, NotLessEq, LessThanExists))
					sd := v.Suc(dw)     // suc(d₀) — the strict gap n₀ − p₀
					mSd := v.Mul(m, sd) // m₀ · suc(d₀) — the strict increment
					b.Show(
						"cancel m₀·p₀ (LessEqAddCancel): m₀·suc(d₀) = 0 is forced, and suc(d₀) ≠ 0 leaves m₀ = 0",
						By(
							bound,
							notLe,
							shift,
							nat_arith.LeftAddDistrib,             // m₀·(p₀+suc d₀) = m₀·p₀ + m₀·suc d₀
							nat_arith.AddClauses,                 // right-identity: m₀·p₀ = m₀·p₀ + 0
							At(LessEqAddCancel, mP, mSd, v.Zero), // m₀·suc d₀ ≤ 0 ⇔ m₀·p₀ + m₀·suc d₀ ≤ m₀·p₀ + 0
							At(LessEqZeroClause, mSd),            // m₀·suc d₀ ≤ 0 ⇔ m₀·suc d₀ = 0
							At(nat_arith.MulEqZero, m, sd),       // m₀·suc d₀ = 0 ⇔ m₀ = 0 ∨ suc d₀ = 0
							peano.SucNotZero))                    // suc d₀ ≠ 0
				}),
			)
			a.Backward(
				"m₀ = 0 ∨ n₀ ≤ p₀ ⊢ m₀·n₀ ≤ m₀·p₀ — split on the degenerate factor",
				// We may assume m₀ ≠ 0; the ∨-hyp then collapses to
				// n₀ ≤ p₀, which we transport through ·m₀.
				Unless(
					m.Eq(v.Zero),
					"m₀ = 0: Mul's zero clause turns m₀·n₀ into 0; ZeroLessEq closes 0 ≤ m₀·p₀",
					Given(func(b *Argument, mZero Fact) {
						b.Show(
							"m₀·n₀ collapses to 0, which sits below every product",
							By(mZero, a.Ctx().Dep(nat_arith.Mul), ZeroLessEq))
					}),
				),
				TrivialSimplify(), // resolves (n₀ ≤ p₀) ∨ (m₀ = 0) against m₀ ≠ 0
				Derive(func(b *Argument) {
					_, shift := b.Obtain(
						"n₀ ≤ p₀ realizes the gap d with p₀ = n₀ + d",
						"∃d:num. p₀ = n₀ + d",
						Cite(LessEqExists))
					b.Show(
						"m₀·p₀ = m₀·n₀ + m₀·d₀ by distributivity; LessEqAdd bounds m₀·n₀ by that sum",
						By(shift, nat_arith.LeftAddDistrib, LessEqAdd))
				}),
			)
		}),
})}

// LessEqMul2 — pairwise ≤-monotonicity of ×: raising both factors
// raises the product — the ×-side twin of LessEqAdd2. Pure witness
// transport through the ≤-as-existence bridge — no induction:
//
//	m ≤ n and p ≤ q are additive shifts n = m + d₀, q = p + d₁
//	(LessEqExists); distributing the product of sums,
//	 n·q = (m+d₀)·(p+d₁) = m·p + (d₀·p + (m·d₁ + d₀·d₁))
//	(LeftAddDistrib once, RightAddDistrib on each half, AddAssoc to
//	regroup the four summands around m·p), and LessEqAdd bounds m·p
//	by that sum.
var LessEqMul2 = lessEqMul2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqMul2",
	Key:  "prop_1c4af0da2aadac6",
	// d₀/d₁ are the two obtained ∃-shifts.
	Build: family.Theorem(
		Statement{
			Binders: "∀m n p q:num.",
			Hypotheses: []string{
				"m ≤ n",
				"p ≤ q",
			},
			Conclusion: "m * p ≤ n * q",
		},
		func(a *Argument, m, n, p, q Term, bounds Fact) { // bounds: m₀ ≤ n₀ ∧ p₀ ≤ q₀
			v := ops(a.Ctx())

			d0, shiftN := a.Obtain(
				"the first bound realizes the gap n₀ − m₀",
				"∃d:num. n₀ = m₀ + d",
				By(bounds, LessEqExists))
			d1, shiftQ := a.Obtain(
				"the second bound realizes the gap q − p",
				"∃d:num. q = p + d",
				By(bounds, LessEqExists))

			// The distributed rectangle (m₀+d₀)·(p₀+d₁), named piecewise:
			mPd0 := v.Add(m, d0)              // m₀ + d₀ (= n₀)
			mp := v.Mul(m, p)                 // m₀·p₀ — the smaller product
			d0p := v.Mul(d0, p)               // d₀·p₀
			crossTerms := v.Add(v.Mul(m, d1), // m₀·d₁ + d₀·d₁
				v.Mul(d0, d1))
			rest := v.Add(d0p, crossTerms) // d₀·p₀ + (m₀·d₁ + d₀·d₁) — the excess over m₀·p₀

			a.Show(
				"distribute: n₀·q₀ = m₀·p₀ + rest; LessEqAdd bounds m₀·p₀ by that sum",
				By(
					shiftN,
					shiftQ,
					At(nat_arith.LeftAddDistrib, mPd0, p, d1),    // (m₀+d₀)·(p₀+d₁) = (m₀+d₀)·p₀ + (m₀+d₀)·d₁
					At(nat_arith.RightAddDistrib, m, d0, p),      // (m₀+d₀)·p₀ = m₀·p₀ + d₀·p₀
					At(nat_arith.RightAddDistrib, m, d0, d1),     // (m₀+d₀)·d₁ = m₀·d₁ + d₀·d₁
					At(LessEqAdd, mp, rest),                      // m₀·p₀ ≤ m₀·p₀ + rest
					At(nat_arith.AddAssoc, mp, d0p, crossTerms))) // regroup the distributed sum around m₀·p₀
		}),
})}

// ---------------------------------------------------------------------------
// LessEqMulMono — a common left factor preserves ≤
// ---------------------------------------------------------------------------

// LessEqMulMono — multiplying both sides of an inequality by a common
// left factor preserves it. The ⇐ direction of LessEqMulCancel with the
// degenerate disjunct absorbed (a zero factor lands on 0 ≤ 0 anyway).
// The one-sided sibling of LessEqMul2, whose pairwise form makes every
// caller that scales a SINGLE inequality first prove a reflexive t ≤ t
// guard; this member is the guard-free spelling.
var LessEqMulMono = lessEqMulMonoThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulMono",
	Key:  "prop_6d2609a14ddb507",
	Build: family.Theorem(Statement{
		Binders: "∀m n p:num.",
		Hypotheses: []string{
			"n ≤ p",
		},
		Conclusion: "m * n ≤ m * p",
	},
		func(a *Argument, m, n, p Term, le Fact) {
			a.Show(
				"the ⇐ direction of LessEqMulCancel, its right disjunct fed by n₀ ≤ p₀",
				By(le, At(LessEqMulCancel, m, n, p)))
		}),
})}

// ---------------------------------------------------------------------------
// LessEqSelfMul — a factor of at least one doesn't shrink
// ---------------------------------------------------------------------------

// LessEqSelfMul — m ≤ m·n whenever 1 ≤ n: the unit law m·1 = m names m
// as a product, and ·m₀ scales 1 ≤ n through LessEqMulMono. The 1 ≤ n
// phrasing is the order-chapter twin of nat_arith's LessEqMulNonzero
// (x = 0 ∨ b ≤ b·x), which predates this member and re-derives the
// same chain inline.
var LessEqSelfMul = lessEqSelfMulThm{family.Add(registry.ProofEntry{
	Name: "LessEqSelfMul",
	Key:  "prop_b499ec3567d1c5d9",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"1 ≤ n",
		},
		Conclusion: "m ≤ m * n",
	},
		func(a *Argument, m, n Term, oneLe Fact) {
			v := ops(a.Ctx())
			one := v.Bit1Op.Apply(v.Zero) // the numeral 1, as the DSL parses it
			a.Show(
				"m₀ is m₀·1 by the unit law, and ·m₀ scales 1 ≤ n₀ up to m₀·n₀",
				By(
					Normalized,
					oneLe,
					At(nat_arith.MulOne, m),       // m₀·1 = m₀
					At(LessEqMulMono, m, one, n))) // 1 ≤ n₀ ⇒ m₀·1 ≤ m₀·n₀
		}),
})}

// ---------------------------------------------------------------------------
// LessEqMulRightCancel — a common right factor cancels through ≤
// ---------------------------------------------------------------------------

// LessEqMulRightCancel — the right-factor twin of LessEqMulCancel
// (whose common factor sits on the left), up to the same degenerate
// zero disjunct. Pure transport: commutativity turns both products
// into their p₀·- forms, where the left cancel decides.
var LessEqMulRightCancel = lessEqMulRightCancelThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulRightCancel",
	Key:  "prop_468b8c59dc0fd39e",
	Build: family.Theorem(
		"∀m n p:num. m * p ≤ n * p ⇔ m ≤ n ∨ p = 0",
		func(a *Argument, m, n, p Term) {
			a.Show(
				"rewrite both products by commutativity; LessEqMulCancel cancels the now-left p₀",
				By(
					At(nat_arith.MulSym, m, p),    // m₀·p₀ = p₀·m₀
					At(nat_arith.MulSym, n, p),    // n₀·p₀ = p₀·n₀
					At(LessEqMulCancel, p, m, n))) // p₀·m₀ ≤ p₀·n₀ ⇔ p₀ = 0 ∨ m₀ ≤ n₀
		}),
})}

// ---------------------------------------------------------------------------
// LessThanMulCancel — a common left factor cancels through <
// ---------------------------------------------------------------------------

// LessThanMulCancel — the strict companion of LessEqMulCancel: a common
// left factor cancels through <, and a zero factor makes the strict
// comparison impossible outright. Pure order algebra, no induction:
// the strict order is the negated flipped ≤ (NotLessEq), so
// m·n < m·p is ¬(m·p ≤ m·n), LessEqMulCancel decides that ≤ as
// m = 0 ∨ p ≤ n, and negating the disjunction — NotLessEq once more,
// on p ≤ n — is m ≠ 0 ∧ n < p.
var LessThanMulCancel = lessThanMulCancelThm{family.Add(registry.ProofEntry{
	Name: "LessThanMulCancel",
	Key:  "prop_d4d436c5cf7cd86",
	Build: family.Theorem(
		"∀m n p:num. m * n < m * p ⇔ m ≠ 0 ∧ n < p",
		func(a *Argument, m, n, p Term) {
			v := ops(a.Ctx())
			mN := v.Mul(m, n) // m₀ * n₀
			mP := v.Mul(m, p) // m₀ * p₀
			a.Show(
				"m₀·n₀ < m₀·p₀ is ¬(m₀·p₀ ≤ m₀·n₀); cancel m₀ through that ≤ and negate the disjunction it leaves",
				By(
					Normalized,
					At(NotLessEq, mP, mN),        // ¬(m₀·p₀ ≤ m₀·n₀) ⇔ m₀·n₀ < m₀·p₀
					At(LessEqMulCancel, m, p, n), // m₀·p₀ ≤ m₀·n₀ ⇔ m₀ = 0 ∨ p₀ ≤ n₀
					At(NotLessEq, p, n)))         // ¬(p₀ ≤ n₀) ⇔ n₀ < p₀
		}),
})}

// ---------------------------------------------------------------------------
// FactorialMonotone — the factorial grows with its argument
// ---------------------------------------------------------------------------

// FactorialMonotone — one step never shrinks a factorial, since
// (k + 1)! = (k + 1)·k! = k·k! + k! has k! among its summands. From m
// the factorial then climbs to (m + d)! by induction on the distance d,
// one transitivity per step, and m ≤ n writes n as such an m + d.
var FactorialMonotone = factorialMonotoneThm{family.Add(registry.ProofEntry{
	Name: "FactorialMonotone",
	Key:  "prop_d6a8bfecef76b8b3",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "factorial(m) ≤ factorial(n)",
	},
		func(a *Argument, m, n *Expr[Nat], le Fact) {
			step := a.Have(
				"one more factor never shrinks a factorial: (k + 1)! is k·k! + k!",
				"∀k:num. factorial(k) ≤ factorial(suc(k))",
				a.ForEach(func(*Expr[Nat]) Action {
					return Chain(Simp(Fwd(nat_arith.Factorial), Fwd(nat_arith.Mul)), Cite(LessEqAddLeft))
				}))
			climb := a.Have(
				"from m the factorial only climbs, by induction on the distance d",
				"∀d:num. factorial(m) ≤ factorial(m + d)",
				Derive(func(b *Argument) {
					b.Induct("d")
					b.Base(
						"at distance 0 both sides are m!",
						By(nat_arith.AddZero.At(m), LessEqRefl))
					b.Step(
						"m! ≤ (m + d)! by the hypothesis, and one step more reaches (m + d + 1)!",
						func(c *Argument, ih Fact) {
							c.Show(
								"m + suc(d) is suc(m + d), and transitivity runs through (m + d)!",
								Simp(Fwd(nat_arith.AddSuc)),
								By(ih, step.At(c.TermAs[Nat]("m + d")), Where(LessEqTrans, "n", c.TermAs[Nat]("factorial(m + d)"))))
						})
				}))
			d, distance := a.Obtain(
				"m ≤ n: n is m plus some distance d",
				"∃d:num. n = m + d",
				By(le, LessEqExists.At(n, m)))
			a.Show(
				"the climb at that distance reaches n!",
				By(Normalized, distance, climb.At(d)))
		}),
})}

// ---------------------------------------------------------------------------
// Evaluating ≤ and < on numerals — the digit-by-digit laws
// ---------------------------------------------------------------------------
//
// A numeral is read one low digit at a time — bit0 n = n + n and
// bit1 n = suc(n + n) (nat_arith.Bit0, nat_arith.Bit1) — and the order between
// two numerals is decided on their low digits: NumeralLessEq and
// NumeralLessThan pack one law per digit pair, in the order a numeral
// evaluator consults them. Under the digit equations each two-digit
// clause compares two doubles — bare, or under a successor on one side
// or both — so the packs rest on two facts stated first: doubling
// preserves and reflects each order (doublingLessEqIff,
// doublingLessThanIff). A shared successor cancels (SucLessEqSucIff,
// sucLessThanSucIff); a successor on one side only crosses to the other
// order through the bridges of the successor/zero part; the clauses
// against zero are the orders' own zero facts — their zero clauses, and
// that zero is below everything — read on a double.

// doublingLessEqIff — doubling preserves and reflects ≤. The ⇐
// direction is pairwise monotonicity of + (LessEqAdd2) with the same
// inequality on both summands; the ⇒ direction is the contrapositive of
// the strict pairwise law (LessThanAdd2) — if n < m then n + n < m + m —
// with NotLessEq turning each strict fact into the negated ≤ the goal
// states.
var doublingLessEqIff = doublingLessEqIffThm{family.Add(registry.ProofEntry{
	Name: "doublingLessEqIff",
	Key:  "prop_a2d65c39a8db4d23",
	Build: family.Theorem("∀m n:num. m + m ≤ n + n ⇔ m ≤ n",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			mm := v.Add(m, m) // m₀ + m₀
			nn := v.Add(n, n) // n₀ + n₀
			a.Show(
				"⇐ doubles m₀ ≤ n₀ pairwise; ⇒ contraposes — n₀ < m₀ "+
					"doubles to n₀ + n₀ < m₀ + m₀, against the hypothesis",
				By(
					Normalized,
					At(LessEqAdd2, m, m, n, n),   // m₀ ≤ n₀ ∧ m₀ ≤ n₀ ⇒ m₀ + m₀ ≤ n₀ + n₀
					At(NotLessEq, m, n),          // ¬(m₀ ≤ n₀) ⇔ n₀ < m₀
					At(LessThanAdd2, n, n, m, m), // n₀ < m₀ ∧ n₀ < m₀ ⇒ n₀ + n₀ < m₀ + m₀
					At(NotLessEq, mm, nn)))       // ¬(m₀ + m₀ ≤ n₀ + n₀) ⇔ n₀ + n₀ < m₀ + m₀
		}),
})}

// doublingLessThanIff — doubling preserves and reflects <: the mirror
// of doublingLessEqIff, the two pairwise monotonicity laws exchanging
// roles and NotLessThan as the bridge.
var doublingLessThanIff = doublingLessThanIffThm{family.Add(registry.ProofEntry{
	Name: "doublingLessThanIff",
	Key:  "prop_9d19155678c0004d",
	Build: family.Theorem("∀m n:num. m + m < n + n ⇔ m < n",
		func(a *Argument, m, n Term) {
			v := ops(a.Ctx())
			mm := v.Add(m, m) // m₀ + m₀
			nn := v.Add(n, n) // n₀ + n₀
			a.Show(
				"⇐ doubles m₀ < n₀ pairwise; ⇒ contraposes — n₀ ≤ m₀ "+
					"doubles to n₀ + n₀ ≤ m₀ + m₀, against the hypothesis",
				By(
					Normalized,
					At(LessThanAdd2, m, m, n, n), // m₀ < n₀ ∧ m₀ < n₀ ⇒ m₀ + m₀ < n₀ + n₀
					At(NotLessThan, m, n),        // ¬(m₀ < n₀) ⇔ n₀ ≤ m₀
					At(LessEqAdd2, n, n, m, m),   // n₀ ≤ m₀ ∧ n₀ ≤ m₀ ⇒ n₀ + n₀ ≤ m₀ + m₀
					At(NotLessThan, mm, nn)))     // ¬(m₀ + m₀ < n₀ + n₀) ⇔ n₀ + n₀ ≤ m₀ + m₀
		}),
})}

var NumeralLessEq = numeralLessEqThm{family.Add(registry.ProofEntry{
	Name: "NumeralLessEq",
	Key:  "prop_c825d7713140838f",
	Build: family.Theorem("0 ≤ 0 ∧ "+
		"(∀n:num. bit0(n) ≤ 0 ⇔ n ≤ 0) ∧ "+
		"(∀n:num. ¬(bit1(n) ≤ 0)) ∧ "+
		"(∀n:num. 0 ≤ bit0(n)) ∧ "+
		"(∀n:num. 0 ≤ bit1(n)) ∧ "+
		"(∀m n:num. bit0(m) ≤ bit0(n) ⇔ m ≤ n) ∧ "+
		"(∀m n:num. bit0(m) ≤ bit1(n) ⇔ m ≤ n) ∧ "+
		"(∀m n:num. bit1(m) ≤ bit0(n) ⇔ m < n) ∧ "+
		"(∀m n:num. bit1(m) ≤ bit1(n) ⇔ m ≤ n)", func(a *Argument) {
		v := ops(a.Ctx())
		a.Do(SplitConjAll(
			Case(
				"0 ≤ 0: reflexivity",
				Cite(LessEqRefl)),
			Case(
				"bit0 n ≤ 0 ⇔ n ≤ 0: both sides say the number is zero, and n + n is zero exactly when n is",
				Simp(
					Fwd(nat_arith.Bit0),
					Fwd(LessEqZeroClause),
					Fwd(nat_arith.AddEqZero)), // ↦ ∀n. n = 0 ∧ n = 0 ⇔ n = 0
				TrivialNormalized()),
			Case(
				"¬(bit1 n ≤ 0): suc(n + n) ≤ 0 would make a successor zero",
				Simp(Fwd(nat_arith.Bit1), Fwd(LessEqZeroClause), Fwd(peano.SucNotZero)), // ↦ ∀n. ¬⊥
				TrivialNormalized()),
			Case(
				"0 ≤ bit0 n: zero is below everything",
				Cite(ZeroLessEq)),
			Case(
				"0 ≤ bit1 n: zero is below everything",
				Cite(ZeroLessEq)),
			Case(
				"bit0 m ≤ bit0 n ⇔ m ≤ n: two even digits compare as their halves",
				Simp(Fwd(nat_arith.Bit0)), // ↦ doublingLessEqIff itself
				Cite(doublingLessEqIff)),
			Case(
				"bit0 m ≤ bit1 n ⇔ m ≤ n: m + m ≤ suc(n + n) is m + m "+
					"< suc n + suc n, whose halves are m < suc n, i.e. m ≤ n",
				Derive(func(a *Argument) {
					_, n := a.Fix(), a.Fix() // the digits m, n; only n is spelled below
					// Flipped: the bridge reads m ≤ n ⇔ m < suc n, and the crossing is its reverse.
					a.Do(Simp(
						Fwd(nat_arith.Bit0),
						Fwd(nat_arith.Bit1),
						Rev(LessThanSucIffLessEq))) // ↦ m + m < suc(suc(n + n)) ⇔ m < suc n
					twoSucs := a.Have(
						"suc(suc(n + n)) is suc n + suc n, a successor moved out of each summand",
						MakeProp(v.Suc(v.Suc(v.Add(n, n))).Eq(v.Add(v.Suc(n), v.Suc(n)))),
						Simp(Fwd(nat_arith.AddLeftSucClause), Fwd(nat_arith.AddSuc)),
						TrivialNormalized())
					a.Do(twoSucs.Rw()) // ↦ m + m < suc n + suc n ⇔ m < suc n
					a.Show(
						"both doubles halve: m < suc n",
						Cite(doublingLessThanIff))
				})),
			Case(
				"bit1 m ≤ bit0 n ⇔ m < n: suc(m + m) ≤ n + n is m + m < n + n, whose halves are m < n",
				// Flipped: the bridge reads suc m ≤ n ⇔ m < n, and the crossing is its reverse.
				Simp(
					Fwd(nat_arith.Bit0),
					Fwd(nat_arith.Bit1),
					Rev(SucLessEqIffLessThan)), // ↦ doublingLessThanIff itself
				Cite(doublingLessThanIff)),
			Case(
				"bit1 m ≤ bit1 n ⇔ m ≤ n: shed the shared successor, then halve",
				Simp(Fwd(nat_arith.Bit1), Fwd(SucLessEqSucIff)), // ↦ doublingLessEqIff itself
				Cite(doublingLessEqIff)),
		))
	}),
})}

var NumeralLessThan = numeralLessThanThm{family.Add(registry.ProofEntry{
	Name: "NumeralLessThan",
	Key:  "prop_522c143050c46933",
	Build: family.Theorem("¬(0 < 0) ∧ "+
		"(∀n:num. ¬(bit0(n) < 0)) ∧ "+
		"(∀n:num. ¬(bit1(n) < 0)) ∧ "+
		"(∀n:num. 0 < bit0(n) ⇔ 0 < n) ∧ "+
		"(∀n:num. 0 < bit1(n)) ∧ "+
		"(∀m n:num. bit0(m) < bit0(n) ⇔ m < n) ∧ "+
		"(∀m n:num. bit0(m) < bit1(n) ⇔ m ≤ n) ∧ "+
		"(∀m n:num. bit1(m) < bit0(n) ⇔ m < n) ∧ "+
		"(∀m n:num. bit1(m) < bit1(n) ⇔ m < n)", func(a *Argument) {
		v := ops(a.Ctx())
		a.Do(SplitConjAll(
			Case(
				"¬(0 < 0): irreflexivity",
				Cite(LessThanIrrefl)),
			Case(
				"¬(bit0 n < 0): nothing is below zero",
				Simp(Fwd(LessThanZeroClause)), // ↦ ∀n. ¬⊥
				TrivialNormalized()),
			Case(
				"¬(bit1 n < 0): nothing is below zero",
				Simp(Fwd(LessThanZeroClause)), // ↦ ∀n. ¬⊥
				TrivialNormalized()),
			Case(
				"0 < bit0 n ⇔ 0 < n: both sides say the number is not zero, and n + n is zero exactly when n is",
				// Flipped: normalized, PosIffNonzero reads n ≠ 0 ⇔ 0 < n; positivity into non-zeroness is its reverse.
				Simp(
					Fwd(nat_arith.Bit0),
					Rev(PosIffNonzero),
					Fwd(nat_arith.AddEqZero)), // ↦ ∀n. ¬(n = 0 ∧ n = 0) ⇔ n ≠ 0
				TrivialNormalized()),
			Case(
				"0 < bit1 n: every successor is positive",
				Simp(Fwd(nat_arith.Bit1), Fwd(ZeroLessThanSuc)), // ↦ ∀n. ⊤
				TrivialNormalized()),
			Case(
				"bit0 m < bit0 n ⇔ m < n: two even digits compare as their halves",
				Simp(Fwd(nat_arith.Bit0)), // ↦ doublingLessThanIff itself
				Cite(doublingLessThanIff)),
			Case(
				"bit0 m < bit1 n ⇔ m ≤ n: m + m < suc(n + n) is m + m ≤ n + n, whose halves are m ≤ n",
				Simp(
					Fwd(nat_arith.Bit0),
					Fwd(nat_arith.Bit1),
					Fwd(LessThanSucIffLessEq)), // ↦ doublingLessEqIff itself
				Cite(doublingLessEqIff)),
			Case(
				"bit1 m < bit0 n ⇔ m < n: suc(m + m) < n + n is suc m "+
					"+ suc m ≤ n + n, whose halves are suc m ≤ n, i.e. m < n",
				Derive(func(a *Argument) {
					m, _ := a.Fix(), a.Fix() // the digits m, n; only m is spelled below
					a.Do(Simp(
						Fwd(nat_arith.Bit0),
						Fwd(nat_arith.Bit1),
						Fwd(SucLessEqIffLessThan))) // ↦ suc(suc(m + m)) ≤ n + n ⇔ suc m ≤ n
					twoSucs := a.Have(
						"suc(suc(m + m)) is suc m + suc m, a successor moved out of each summand",
						MakeProp(v.Suc(v.Suc(v.Add(m, m))).Eq(v.Add(v.Suc(m), v.Suc(m)))),
						Simp(Fwd(nat_arith.AddLeftSucClause), Fwd(nat_arith.AddSuc)), // as in NumeralLessEq
						TrivialNormalized())
					a.Do(twoSucs.Rw()) // ↦ suc m + suc m ≤ n + n ⇔ suc m ≤ n
					a.Show(
						"both doubles halve: suc m ≤ n",
						Cite(doublingLessEqIff))
				})),
			Case(
				"bit1 m < bit1 n ⇔ m < n: shed the shared successor, then halve",
				Simp(Fwd(nat_arith.Bit1), Fwd(sucLessThanSucIff)), // ↦ doublingLessThanIff itself
				Cite(doublingLessThanIff)),
		))
	}),
})}

// ---------------------------------------------------------------------------
// The order against exponentiation
// ---------------------------------------------------------------------------
//
// Chapter API: PowPositive · LessThanPow · LessEqPow. The order reads
// nat_pow through positivity and monotonicity: `0 < nat_pow(m, n)` is answered
// by composing PosIffNonzero (the duality part above) with nat_arith's own
// vanishing characterization, and the two comparison characterizations
// split the base three ways — powers of 0 collapse to 1-then-0, powers
// of 1 freeze at 1, and a base of at least 2 makes nat_pow(x, ·) strictly
// increasing. nat_pow is the chapter's one constant resolved straight to
// its mint (nat_arith's) rather than declared in the family vocabulary; a
// member that must BUILD a nat_pow witness term declares a local handle
// (Script.Const is idempotent).

// PowPositive — when a power is positive. Positivity on ℕ is
// non-zeroness (PosIffNonzero, read at the power), so the question is
// when the power vanishes — nat_arith.PowEqZero's characterization — and
// negating that characterization is the whole proof.
var PowPositive = powPositiveThm{family.Add(registry.ProofEntry{
	Name: "PowPositive",
	Key:  "prop_af298b2edb0a2abb",
	Build: family.Theorem("∀m n:num. 0 < nat_pow(m, n) ⇔ m ≠ 0 ∨ n = 0",
		func(a *Argument) {
			a.Show(
				"positivity is non-zeroness at the power, whose vanishing ExpEqZero characterizes",
				By(Normalized, nat_arith.PowEqZero, PosIffNonzero))
		}),
})}

// LessThanPow — when one power strictly exceeds another of the same
// base: only in the strict regime 2 ≤ x with a rising exponent, or in
// the one degenerate drop at base zero, 0ᵐ < 0⁰ (m ≠ 0, n = 0). The
// proof splits the base three ways (0 / 1 / at least 2) and carries the
// strict regime on two monotonicity lemmas: `monotone` (a nonzero
// base's powers never shrink) settles ⇒ by contradiction, and `strict`
// — one doubling step nat_pow(x, m) < nat_pow(x, m)·2 ≤ x·nat_pow(x, m) =
// nat_pow(x, suc m), then `monotone` up the remaining exponent gap —
// settles ⇐.
var LessThanPow = lessThanPowThm{family.Add(registry.ProofEntry{
	Name: "LessThanPow",
	Key:  "prop_711655d996fcfdc2",
	Build: family.Sections(
		"∀x m n:num. nat_pow(x, m) < nat_pow(x, n) ⇔ 2 ≤ x ∧ m < n ∨ x = 0 ∧ (m ≠ 0 ∧ n = 0)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			// The local nat_pow handle only builds the ground witness terms
			// below (part header: the constant itself resolves straight
			// to its mint).
			exp := ctx.Const("nat_pow", MakeFun(NumType, MakeFun(NumType, NumType)))
			zero, one, two := ctx.Numeral(0), ctx.Numeral(1), ctx.Numeral(2)

			// zeroBase — powers of 0 compute: 0⁰ = 1 and 0ⁿ = 0 otherwise,
			// so the only strict comparison among them is 0 < 1.
			zeroBase := ctx.Lemma("∀m n:num. nat_pow(0, m) < nat_pow(0, n) ⇔ m ≠ 0 ∧ n = 0",
				func(a *Argument, m *TermWrapper, n Term) {
					a.Cases(m.Eq(zero))
					a.When(
						"m = 0: the left power is 1 and no power of 0 exceeds 1 — both sides false",
						func(b *Argument, mZero Fact) {
							baseOne := b.Have(
								"a zeroth power is 1",
								"nat_pow(0, m₀) = 1",
								By(mZero, nat_arith.NatPow))
							vanish := b.Have(
								"the right power is 0 unless its exponent is 0",
								"nat_pow(0, n₀) = 0 ∨ n₀ = 0",
								By(At(nat_arith.PowEqZero, zero, n)))
							b.Show(
								"either way 1 < nat_pow(0, n₀) fails: 1 < 0 or 1 < 1",
								By(mZero, baseOne, vanish, At(LessThanZeroClause, one), At(LessThanIrrefl, one)))
						})
					a.Otherwise(
						"m ≠ 0: the left power is 0, so the comparison is the right power's positivity — n = 0",
						func(b *Argument, mNonzero Fact) {
							baseZero := b.Have(
								"the left power vanishes: zero base, nonzero exponent",
								"nat_pow(0, m₀) = 0",
								By(mNonzero, At(nat_arith.PowEqZero, zero, m)))
							b.Show(
								"so the comparison is 0 < nat_pow(0, n₀), which holds exactly when n₀ = 0",
								By(Normalized, mNonzero, baseZero, At(PowPositive, zero, n)))
						})
				})

			// monotone — nat_pow(x, ·) never shrinks for a nonzero base: the
			// gap d realizes nat_pow(x, n) as nat_pow(x, m)·nat_pow(x, d), and a
			// nonzero base's powers never vanish, so the factor is ≥ 1.
			monotone := ctx.Lemma(Statement{
				Binders: "∀x m n:num.",
				Hypotheses: []string{
					"x ≠ 0",
					"m ≤ n",
				},
				Conclusion: "nat_pow(x, m) ≤ nat_pow(x, n)",
			},
				func(a *Argument, x, m, n Term, h Fact) {
					gap, gapEq := a.Obtain(
						"m ≤ n realizes the slack as a gap d with n = m + d",
						"∃d:num. n₀ = m₀ + d",
						By(h, LessEqExists))
					factor := a.Have(
						"the gap factor is at least 1 — a nonzero base's powers never vanish",
						MakeProp(v.LessEq(one, exp.Apply(x, gap))),
						By(h, At(nat_arith.PowEqZero, x, gap), At(OneLessEqIffNonzero, exp.Apply(x, gap))))
					a.Show(
						"nat_pow(x, n) = nat_pow(x, m)·nat_pow(x, d), and scaling by a factor ≥ 1 only grows",
						By(
							Normalized,
							factor,
							gapEq,
							At(nat_arith.PowAdd, x, m, gap),
							At(LessEqSelfMul, exp.Apply(x, m), exp.Apply(x, gap))))
				})

			// strict — for a base of at least 2 the powers strictly climb:
			// one doubling step lands on nat_pow(x, suc m), then monotone
			// covers the rest of the exponent gap.
			strict := ctx.Lemma(Statement{
				Binders: "∀x m n:num.",
				Hypotheses: []string{
					"2 ≤ x",
					"m < n",
				},
				Conclusion: "nat_pow(x, m) < nat_pow(x, n)",
			},
				func(a *Argument, x, m, n Term, h Fact) {
					e := exp.Apply(x, m)            // the base power nat_pow(x, m)
					eTwice := v.Mul(e, two)         // nat_pow(x, m) · 2
					eStep := exp.Apply(x, v.Suc(m)) // nat_pow(x, suc m)

					xNonzero := a.Have(
						"a base of at least 2 is nonzero: 2 ≤ 0 collapses to 2 = 0 against suc(1) ≠ 0",
						"x₀ ≠ 0",
						By(Normalized, h, At(LessEqZeroClause, two), nat_arith.Two, At(peano.SucNotZero, one)))
					eOne := a.Have(
						"so the base power is at least 1",
						"1 ≤ nat_pow(x₀, m₀)",
						By(xNonzero, At(nat_arith.PowEqZero, x, m), At(OneLessEqIffNonzero, e)))
					doubled := a.Have(
						"doubling a positive quantity strictly grows it: suc e = e + 1 ≤ e + e = e·2",
						"nat_pow(x₀, m₀) < nat_pow(x₀, m₀) * 2",
						By(
							eOne,
							At(nat_arith.Add1, e),
							At(LessEqAddCancel, e, one, e),
							nat_arith.Two,
							At(nat_arith.MulSuc, e, one),
							At(nat_arith.MulOne, e),
							At(SucLessEqIffLessThan, e, eTwice)))
					scaled := a.Have(
						"and 2 ≤ x trades the 2 for one more factor of the base: e·2 ≤ e·x = nat_pow(x, suc m)",
						"nat_pow(x₀, m₀) * 2 ≤ nat_pow(x₀, suc(m₀))",
						By(
							Normalized,
							h,
							At(LessEqMulMono, e, two, x),
							At(nat_arith.MulSym, e, x),
							nat_arith.NatPow)) // its successor clause: nat_pow(x₀, suc m₀) = x₀·e
					a.Show(
						"one strict step, then the powers do not shrink over the remaining gap suc m ≤ n",
						By(
							xNonzero,
							doubled,
							scaled,
							h,
							At(SucLessEqIffLessThan, m, n),
							At(monotone, x, v.Suc(m), n),
							At(LessThanLessEqTrans, e, eTwice, eStep),
							At(LessThanLessEqTrans, e, eStep, exp.Apply(x, n))))
				})

			// The characterization assembles over the trichotomy of bases:
			// the two degenerate bases discharge inline, and under 2 ≤ x
			// the ⇔ is strict monotonicity read in both directions.
			return ctx.Theorem(headline,
				func(a *Argument, x *TermWrapper, m, n Term) {
					xNonzero := a.Unless(
						x.Eq(zero),
						"x = 0: the comparison of powers of 0 decides both sides, and the strict regime fails at ¬(2 ≤ 0)",
						Given(func(b *Argument, xZero Fact) {
							b.Show(
								"powers of 0 compare exactly when m ≠ 0 ∧ n = 0, and 2 ≤ 0 collapses to 2 = 0 against suc(1) ≠ 0",
								By(xZero, zeroBase, At(LessEqZeroClause, two), nat_arith.Two, At(peano.SucNotZero, one)))
						}))
					xNotOne := a.Unless(
						x.Eq(one),
						"x = 1: every power is 1, so neither side can hold",
						Given(func(b *Argument, xOne Fact) {
							b.Show(
								"1 < 1 refutes the left; on the right 2 ≤ 1 is suc(1) ≤ 1, i.e. 1 < 1 again",
								By(
									xOne,
									xNonzero,
									At(nat_arith.OnePow, m),
									At(nat_arith.OnePow, n),
									At(LessThanIrrefl, one),
									nat_arith.Two,
									At(SucLessEqIffLessThan, one, one)))
						}))
					atLeastTwo := a.Have(
						"a base that is neither 0 nor 1 is at least 2 — walking the "+
							"numerals down: ¬(2 ≤ x) means x < 2, so x ≤ 1, so x = 0 or x = 1",
						"2 ≤ x₀",
						By(
							xNonzero,
							xNotOne,
							At(NotLessEq, two, x),
							nat_arith.Two,
							At(LessThanSucIffLessEq, x, one),
							At(LessEqSplit, x, one),
							nat_arith.OneIsSucZero,
							At(LessThanSucIffLessEq, x, zero),
							At(LessEqZeroClause, x)))
					a.Iff()
					a.Forward(
						"a strict comparison of powers forces m < n — and 2 ≤ x already stands",
						func(b *Argument, lt Fact) {
							mBelowN := b.Have(
								"m < n: otherwise n ≤ m, and the powers could not drop — nat_pow(x, n) ≤ nat_pow(x, m)",
								"m₀ < n₀",
								By(
									lt,
									xNonzero,
									At(NotLessThan, m, n),
									At(monotone, x, n, m),
									At(lessThanLessEqAsym, exp.Apply(x, m), exp.Apply(x, n))))
							b.Show(
								"both conjuncts of the strict regime stand",
								By(mBelowN, atLeastTwo))
						})
					a.Backward(
						"the right side reduces to 2 ≤ x ∧ m < n (x ≠ 0 bars the "+
							"other disjunct), and the powers climb strictly over the gap",
						func(b *Argument, rhs Fact) {
							b.Show(
								"a base of at least 2 raised from m to n > m strictly grows the power",
								By(xNonzero, rhs, strict))
						})
				})
		}),
})}

// LessEqPow — the ¬<-reading of LessThanPow: nat_pow(x, m) ≤ nat_pow(x, n) iff
// the mirrored strict comparison nat_pow(x, n) < nat_pow(x, m) fails. The COND
// spells the same trichotomy of bases — at 0 the bound says m = 0 ⇒
// n = 0 (the one drop is barred), at 1 it is vacuous, and from 2 on it
// is m ≤ n.
var LessEqPow = lessEqPowThm{family.Add(registry.ProofEntry{
	Name: "LessEqPow",
	Key:  "prop_629ba979163d5290",
	Build: family.Theorem(
		"∀x m n:num. nat_pow(x, m) ≤ nat_pow(x, n) ⇔ COND(x = 0, m = 0 ⇒ n = 0, x = 1 ∨ m ≤ n)",
		func(a *Argument, x *TermWrapper, m, n Term) {
			ctx := a.Ctx()
			// The local nat_pow handle only builds witness terms (part header).
			exp := ctx.Const("nat_pow", MakeFun(NumType, MakeFun(NumType, NumType)))
			zero, one, two := ctx.Numeral(0), ctx.Numeral(1), ctx.Numeral(2)
			// The COND splits into its two guarded readings — a
			// goal-surface move with no deduction verb.
			a.Do(CondRewrite())

			xNonzero := a.Unless(
				x.Eq(zero),
				"x = 0: ≤ is the failure of the one strict drop — "+
					"LessThanPow mirrored at (0, n, m) reads m ≠ 0 ∨ n = 0",
				Given(func(b *Argument, xZero Fact) {
					b.Show(
						"negate the mirrored characterization; ¬(2 ≤ 0) as usual",
						By(
							xZero,
							// nat_pow(x₀, n₀) < nat_pow(x₀, m₀) ⇔ 2 ≤ x₀ ∧ n₀ < m₀ ∨ x₀ = 0 ∧ (n₀ ≠ 0 ∧ m₀ = 0)
							At(LessThanPow, x, n, m),
							At(NotLessThan, exp.Apply(x, n), exp.Apply(x, m)),
							At(LessEqZeroClause, two),
							nat_arith.Two,
							At(peano.SucNotZero, one)))
				}))
			xNotOne := a.Unless(
				x.Eq(one),
				"x = 1: both sides hold — every power is 1, and the x = 1 disjunct is its own witness",
				Given(func(b *Argument, xOne Fact) {
					b.Show(
						"1 ≤ 1 on the left; x = 1 settles the right",
						By(
							xOne,
							xNonzero,
							At(nat_arith.OnePow, m),
							At(nat_arith.OnePow, n), // nat_pow(1, m₀) = 1 = nat_pow(1, n₀)
							LessEqRefl))
				}))
			atLeastTwo := a.Have(
				"a base that is neither 0 nor 1 is at least 2 — the same numeral walk as LessThanPow's",
				"2 ≤ x₀",
				By(
					xNonzero,
					xNotOne,
					At(NotLessEq, two, x), // ¬(2 ≤ x₀) ⇔ x₀ < 2
					nat_arith.Two,
					At(LessThanSucIffLessEq, x, one), // x₀ < suc(1) ⇔ x₀ ≤ 1
					At(LessEqSplit, x, one),          // x₀ ≤ 1 ⇔ x₀ < 1 ∨ x₀ = 1
					nat_arith.OneIsSucZero,
					At(LessThanSucIffLessEq, x, zero), // x₀ < suc(0) ⇔ x₀ ≤ 0
					At(LessEqZeroClause, x)))          // x₀ ≤ 0 ⇔ x₀ = 0
			a.Show(
				"in the strict regime ≤ is exactly ¬(mirrored <): LessThanPow at "+
					"(x, n, m) through NotLessThan at the powers and at the exponents",
				By(
					Normalized,
					xNonzero,
					xNotOne,
					atLeastTwo,
					At(LessThanPow, x, n, m), // nat_pow(x₀, n₀) < nat_pow(x₀, m₀) ⇔ 2 ≤ x₀ ∧ n₀ < m₀ ∨ …
					At(NotLessThan, exp.Apply(x, n), exp.Apply(x, m)),
					At(NotLessThan, n, m))) // ¬(n₀ < m₀) ⇔ m₀ ≤ n₀
		}),
})}

// PowTwoMonotone — a power of two grows with its exponent: the base-2
// instance of the ≤-characterization, read off LessEqPow with the zero
// and one branches discharged by 2 being a successor above one. The
// words chapters' every high-bit argument spends this instance.
var PowTwoMonotone = powTwoMonotoneThm{family.Add(registry.ProofEntry{
	Name: "PowTwoMonotone",
	Key:  "prop_540d5e6042721823",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "nat_pow(2, m) ≤ nat_pow(2, n)",
	},
		func(a *Argument, m, n Term, le Fact) {
			two := a.Ctx().Numeral(2)
			a.Show(
				"the ≤-characterization at base 2: two is no zero, and m ≤ n selects the else-branch disjunct",
				By(le, At(LessEqPow, two, m, n), nat_arith.Two, peano.SucNotZero))
		}),
})}

// LessEqSelfPow — a number is at most each of its positive powers: x is
// x¹, and the ≤-characterization from the exponent 1 up to a positive k
// holds at every base, at base 0 asking only that 1 is not 0.
var LessEqSelfPow = lessEqSelfPowThm{family.Add(registry.ProofEntry{
	Name: "LessEqSelfPow",
	Key:  "prop_32d2d9866d65d8df",
	Build: family.Theorem(Statement{
		Binders: "∀x k:num.",
		Hypotheses: []string{
			"0 < k",
		},
		Conclusion: "x ≤ x ^ k",
	},
		func(a *Argument, x, k *Expr[Nat], positive Fact) {
			a.Show(
				"x is x¹, and a positive k is at least 1",
				ByArith(positive, LessEqPow.At(x, a.TermAs[Nat]("1"), k), nat_arith.PowOne.At(x)))
		}),
})}

// LessThanPowTwoSelf — every number sits below its own power of two:
// LessThanPowSelf at base 2.
var LessThanPowTwoSelf = lessThanPowTwoSelfThm{family.Add(registry.ProofEntry{
	Name: "LessThanPowTwoSelf",
	Key:  "prop_6a551ad4d19ee65e",
	Build: family.Theorem("∀n:num. n < nat_pow(2, n)",
		func(a *Argument, n Term) {
			two := a.Ctx().Numeral(2)
			a.Show(
				"the bound below a power at base 2, two being at least two",
				By(At(LessEqRefl, two), At(LessThanPowSelf, two, n)))
		}),
})}

// LessThanPowSelf — every number sits below its power at any base of at least
// two, by induction on it: the next power is the base times the last, so at
// least twice the last, which is above the number.
var LessThanPowSelf = lessThanPowSelfThm{family.Add(registry.ProofEntry{
	Name: "LessThanPowSelf",
	Key:  "prop_89517e2010fd306b",
	Build: family.Theorem(Statement{
		Binders: "∀x n:num.",
		Hypotheses: []string{
			"2 ≤ x",
		},
		Conclusion: "n < nat_pow(x, n)",
	},
		func(a *Argument, x Term, large Fact) {
			a.Induct("n")
			a.Base(
				"the zeroth power is one, and zero is below it",
				By(Normalized, nat_arith.NatPow, nat_arith.OneNotZero, PosIffNonzero))
			a.Step(
				"the next power is at least twice the last, which is above the number",
				func(b *Argument, ih Fact) {
					b.Show(
						"so the successor stays below it",
						ByArith(ih, large, nat_arith.NatPow, At(LessEqMulMono, b.Term("nat_pow(x, n)"), b.Term("2"), x)))
				})
		}),
})}

// PowBaseMonotone — a power grows with its base: by induction on the
// exponent, x^(k + 1) = x·x^k ≤ y·y^k = y^(k + 1).
var PowBaseMonotone = powBaseMonotoneThm{family.Add(registry.ProofEntry{
	Name: "PowBaseMonotone",
	Key:  "prop_30ef0906b9d8cabe",
	Build: family.Theorem(Statement{
		Binders: "∀x y k:num.",
		Hypotheses: []string{
			"x ≤ y",
		},
		Conclusion: "x ^ k ≤ y ^ k",
	},
		func(a *Argument, x, y *Expr[Nat], ordered Fact) {
			a.Induct("k")
			a.Base(
				"x⁰ = 1 = y⁰",
				ByArith(nat_arith.NatPow))
			a.Step(
				"x^(k + 1) = x·x^k ≤ y·y^k = y^(k + 1)",
				func(b *Argument, ih Fact) {
					b.Show(
						"multiply the two inequalities x ≤ y and x^k ≤ y^k",
						ByArith(
							ordered,
							ih,
							nat_arith.NatPow,
							LessEqMul2.At(x, y, b.TermAs[Nat]("x ^ k"), b.TermAs[Nat]("y ^ k"))))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Growth bounds: how ≤ behaves along linear and affine functions of ℕ
// ---------------------------------------------------------------------------
//
// BoundsLinear · BoundsLinear0 · BoundsIgnore · LessEqMulNonzero ·
// BoundsDivided · BoundsNotZero.
//
// The chapter's other files state the order against +/× one operation
// at a time; this one compares whole growth rates — a linear function
// dominates another iff its slope does, a bound holding eventually
// holds everywhere, a pointwise bound and a divided-through linear
// bound carry the same information. These are the estimates the real
// tower's nadd construction runs on.
//
// DAG (within this file):
//
// 	BoundsLinear : [nat_arith.MulSym, nat_arith.AddAssoc, nat_arith.RightAddDistrib, nat_arith.MulSuc]
// 	 + {LessEqExists, LessEqAdd, LessEqAddCancel,
// 	 LessEqTrans, LessThanExists, NotLessEq,
// 	 LessThanIrrefl, SucLessEqIffLessThan}
// 	BoundsLinear0 : [BoundsLinear, nat_arith.MulLeftZeroClause, nat_arith.AddLeftZeroClause]
// 	 + {LessEqAntisym, ZeroLessEq}
// 	BoundsIgnore : [nat_arith.AddSym, nat_arith.AddAssoc]
// 	 + {LessEqAdd, LessEqAddCancel, LessEqTrans,
// 	 NotLessEq, LessThanSucIffLessEq, LessEqAntisym, ZeroLessEq}
// 	LessEqMulNonzero : [nat_arith.MulOne, nat_arith.OneIsSucZero]
// 	 + {PosIffNonzero, SucLessEqIffLessThan, LessEqMulCancel}
// 	BoundsDivided : [nat_arith.MulSym, nat_arith.AddSym, nat_arith.RightAddDistrib, nat_arith.AddZero, LessEqMulNonzero]
// 	 + {LessEqAdd, LessEqAddCancel,
// 	 LessEqMulCancel, LessEqTrans}
// 	BoundsNotZero : [nat_arith.RightAddDistrib, nat_arith.AddEqZero, LessEqMulNonzero]
// 	 + {LessEqAddCancel, LessEqTrans, ZeroLessEq}
//
// **Ground-instance discipline is load-bearing here.** These members are
// foundation-resident (`[]` policy variant); Arith() and the arith fast-
// path are unavailable at replay. The failure mode to avoid — recurring
// enough to be worth naming — is loading a handful of ∀-form hyps into
// a single leaf and asking `CnfRefute` to search the cross-product. That
// is refute-poisoning by wide-∀, not a refuter budget wall. Instead,
// ground every cite at its specific term via `Cite(dep, w…)` (or a
// targeted `Specialize` on a resident hyp), so the fact lands consumed
// at install and the refuter merely paramodulates the residual eq
// chain. See boundsLinearSlopeFromBound for the canonical shape.

// ---------------------------------------------------------------------------
// BoundsLinear — one linear function dominates another, up to an
// additive constant, exactly when its slope does
// ---------------------------------------------------------------------------

// BoundsLinear — one linear function stays below another up to an
// additive constant, A·n ≤ B·n + C for every n, exactly when its slope
// is no larger, A ≤ B: a constant cannot make up for a steeper slope.
var BoundsLinear = boundsLinearThm{family.Add(registry.ProofEntry{
	Name: "BoundsLinear",
	Key:  "prop_d54ac239f8e0ff64",
	Build: family.Theorem(
		"∀A B C:num. (∀n:num. A * n ≤ B * n + C) ⇔ A ≤ B",
		func(a *Argument, A, B, C Term) {
			a.Iff()
			a.Forward(
				"a steeper slope B < A breaks the bound at n = suc C",
				boundsLinearSlopeFromBound(a.Ctx(), A, B, C),
			)
			a.Backward(
				"B = A + d makes B·n + C exceed A·n by d·n + C",
				boundsLinearBoundFromSlope(a.Ctx(), A, B, C),
			)
		}),
})}

// boundsLinearBoundFromSlope proves ∀n. A·n ≤ B·n + C from A ≤ B.
func boundsLinearBoundFromSlope(ctx *Script, A, B, C Term) Action {
	v := ops(ctx)
	return Given(func(a *Argument, leAB Fact) {
		n := a.Fix() // the bound's index
		gap, gapEq := a.Obtain(
			"A ≤ B realizes the slack as a gap d with B = A + d",
			"∃d:num. B₀ = A₀ + d",
			By(leAB, LessEqExists))
		a.Show(
			"distribute (A + d)·n and regroup the right side as A·n + (d·n + C)",
			By(
				gapEq,
				At(nat_arith.RightAddDistrib, A, gap, n),
				At(LessEqAdd, v.Mul(A, n), v.Add(v.Mul(gap, n), C)),
				At(nat_arith.AddAssoc, v.Mul(A, n), v.Mul(gap, n), C)))
	})
}

// boundsLinearSlopeFromBound proves A ≤ B from ∀n. A·n ≤ B·n + C, by
// contradiction.
func boundsLinearSlopeFromBound(ctx *Script, A, B, C Term) Action {
	v := ops(ctx)
	return Given(func(a *Argument, linBound Fact) {
		notLe := a.SupposeNot() // ¬(A₀ ≤ B₀) — the contradiction entry
		d0, gapEq := a.Obtain(
			"¬(A₀ ≤ B₀) is B₀ < A₀, which realizes a strict gap suc(d)",
			"∃d:num. A₀ = B₀ + suc(d)",
			By(notLe, At(NotLessEq, A, B), LessThanExists))

		// The squeeze's recurring terms.
		sC := v.Suc(C)       // suc C — the killing instance
		sD := v.Suc(d0)      // suc d — the strict gap A − B
		gap := v.Mul(sD, sC) // suc d · suc C
		BsC := v.Mul(B, sC)  // B · suc C

		cancel := a.Have(
			"substitute the gap into the bound at suc C, distribute, cancel the common B·suc C",
			"suc(d₀) * suc(C₀) ≤ C₀",
			By(
				gapEq,
				linBound.At(sC),
				At(nat_arith.RightAddDistrib, B, sD, sC),
				At(LessEqAddCancel, BsC, gap, C)))
		growth := a.Have(
			"a factor suc d does not shrink suc C: suc C·suc d = suc C + suc C·d",
			"suc(C₀) ≤ suc(d₀) * suc(C₀)",
			By(
				Normalized,
				At(nat_arith.MulSym, sD, sC),
				At(nat_arith.MulSuc, sC, d0),
				At(LessEqAdd, sC, v.Mul(sC, d0))))
		a.Show(
			"so suc C ≤ C, that is C < C — impossible",
			By(cancel, growth, At(LessEqTrans, sC, gap, C), At(SucLessEqIffLessThan, C, C), LessThanIrrefl))
	})
}

// ---------------------------------------------------------------------------
// BoundsLinear0 — only the zero slope stays under a constant bound
// ---------------------------------------------------------------------------

// BoundsLinear0 — the zero-slope corollary of BoundsLinear. A ⇔ B chain
// bridged by one asserted equation:
//
//	(∀n. A·n ≤ B) — the goal LHS
//	⇔ (∀n. A·n ≤ 0·n + B) — apply the bridge `(0·n)+B = B` under ∀n
//	⇔ A ≤ 0 — BoundsLinear at (A, 0, B)
//	⇔ A = 0 — LessEqAntisym at (A, 0) + ZeroLessEq at A
//	 (the reverse leg `0 ≤ A` is trivially
//	 supplied by ZeroLessEq, so the ⇔ collapses)
//
// A specialization consumer of BoundsLinear, cited by slope's numeral
// embedding. The recursion base clauses supply the bridge equations
// `0·n = 0` and `0 + B = B` directly; the simplification packs
// MulClauses/AddClauses are deliberately NOT deps here. LessEqAntisym
// and ZeroLessEq are the ⇔-to-A=0 closure ingredients.
var BoundsLinear0 = boundsLinear0Thm{family.Add(registry.ProofEntry{
	Name: "BoundsLinear0",
	Key:  "prop_692bdcda488876bf",
	Build: family.Theorem(
		"∀A B:num. (∀n:num. A * n ≤ B) ⇔ A = 0",
		func(a *Argument, A, B Term) {
			ctx := a.Ctx()
			zero := ctx.Numeral(0)

			bridge := a.Have(
				"bridge: (∀n. A·n ≤ B) ⇔ (∀n. A·n ≤ (0·n)+B) — the two "+
					"∀-forms differ only by the ground rewrite (0·n)+B = B",
				"(∀n:num. A₀ * n ≤ B₀) ⇔ ∀n:num. A₀ * n ≤ 0 * n + B₀",
				Derive(func(b *Argument) {
					b.Have(
						"zeroAdd: ∀n. (0·n)+B = B — Mul's 0-clause reduces 0·n → 0, then Add's 0-clause reduces 0+B → B",
						"∀n:num. 0 * n + B₀ = B₀",
						StripQuant(),
						Cite(nat_arith.MulLeftZeroClause),
						Cite(nat_arith.AddLeftZeroClause),
					)
					b.Show(
						"bridgeCloses: the ⇔ of the two ∀-forms follows by paramodulation through the ground equation",
						Basic(),
					)
				}),
			)
			a.Show(
				"main: BoundsLinear at (A, 0, B) folds LHS to A ≤ "+
					"0; LessEqAntisym + ZeroLessEq collapse A ≤ 0 ⇔ A = 0",
				By(bridge, At(BoundsLinear, A, zero, B), At(LessEqAntisym, A, zero), ZeroLessEq))
		}),
})}

// ---------------------------------------------------------------------------
// BoundsIgnore — ⊢ ∀P Q. (∃B. ∀i. P(i) ≤ Q(i)+B) ⇔ (∃B N. ∀i. N ≤ i ⇒ P(i) ≤ Q(i)+B)
// ---------------------------------------------------------------------------

// BoundsIgnore — a uniform bound holds ONLY-eventually iff it holds
// everywhere (up to slack on the initial N-block). The forward direction
// is trivial (take N = 0, ZeroLessEq); the backward direction is the
// content and proceeds by induction on N through the extracted lemma:
//
//	lemma1 : ∀N B P Q. (∀i. N ≤ i ⇒ P(i) ≤ Q(i)+B) ⇒ ∃B'. ∀i. P(i) ≤ Q(i)+B'
//
// which raises the bound past the initial block. Induction on N:
// - base N = 0: 0 ≤ i is universal (ZeroLessEq), so the antecedent
// collapses to ∀i. P(i) ≤ Q(i)+B — witness B directly.
// - step N → suc N: given the hyp at suc N, instantiate IH at
// (B+P(N), P, Q) — this reduces the goal to proving
// ∀i. N ≤ i ⇒ P(i) ≤ Q(i)+(B+P(N)). Case-split on suc(N) ≤ i:
// true (i ≥ suc N): P(i) ≤ Q(i)+B (from hyp) ≤ Q(i)+(B+P(N))
// via LessEqAddCancel + LessEqAdd + LessEqTrans.
// false (i = N): ¬(suc N ≤ i) ∧ N ≤ i force i = N through
// NotLessEq + lessThanSucIffLessEq + LessEqAntisym; the
// residual P(N) ≤ Q(N)+(B+P(N)) then closes via
// LessEqAdd + one AC-regroup.
//
// Band A (CamelCase, README lists). Higher-order (P, Q : num→num).
var BoundsIgnore = boundsIgnoreThm{family.Add(registry.ProofEntry{
	Name: "BoundsIgnore",
	Key:  "prop_5734d9e29a5aede5",
	// The proof is one lemma plus the assembly, written as a linear script:
	// the two sections are Go locals, and `extend` is cited from the goal by
	// closure capture rather than through a struct field.
	Build: family.Sections(
		"∀P Q:(num → num). (∃B:num. ∀i:num. P(i) ≤ Q(i) + B) ⇔ ∃B N:num. ∀i:num. N ≤ i ⇒ P(i) ≤ Q(i) + B",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			addAC := nat_arith.AddAC(ctx)

			// extend: a bound holding beyond N extends to a bound everywhere —
			// the inductive core. Induction on N: at N = 0 the antecedent's
			// guard 0 ≤ i is universal (ZeroLessEq) so the bound already holds
			// everywhere; at suc N the induction hypothesis is fed the bound
			// raised by P(N), which covers the one index the step exposes.
			extend := ctx.Lemma(
				Statement{
					Binders: "∀N B:num. ∀P Q:(num → num).",
					Hypotheses: []string{
						"∀i:num. N ≤ i ⇒ P(i) ≤ Q(i) + B",
					},
					Conclusion: "∃B:num. ∀i:num. P(i) ≤ Q(i) + B",
				},
				func(a *Argument) {
					// N is the induction variable, so it stays bound — named
					// here because the step case needs it as a term.
					N := a.Binder("N")
					a.Induct(N)
					a.Base(
						"0 ≤ i is universal (ZeroLessEq) so the antecedent gives ∀i. P(i) ≤ Q(i)+B directly — witness B",
						Cite(ZeroLessEq),
						CnfRefute(),
					)
					a.Step(
						"the IH at B+P(N) gives the bound once the antecedent is "+
							"raised by P(N), which covers the one index N the step exposes",
						func(b *Argument, ih Fact) {
							B := b.Fix()
							P := b.Fix()
							Q := b.Fix()
							// The step-case antecedent ∀i. suc(N) ≤ i ⇒ P₀(i) ≤ Q₀(i)+B₀.
							antSucN := b.Assume()
							raised := b.Have(
								"the bound raised by P(N) holds from N on — by cases on suc(N) ≤ i",
								"∀i:num. N ≤ i ⇒ P₀(i) ≤ Q₀(i) + (B₀ + P₀(N))",
								boundsIgnoreRaise(v, addAC, N, B, P, Q, antSucN))
							b.Show(
								"the IH at (B₀+P₀(N), P₀, Q₀) fires ∃B\u2032 on the raised antecedent — its ∃-conclusion is the goal",
								By(ih.At(v.Add(B, P.Apply(N)), P, Q), raised))
						},
					)
				})

			// The ⇔ assembles from `extend` (a bound holding eventually holds
			// everywhere) and, the trivial way round, the witness N = 0.
			return ctx.Theorem(headline,
				func(a *Argument, P, Q Term) {
					a.Iff()
					a.Forward(
						"∃B. ∀i. P(i) ≤ Q(i)+B — witness N=0 (ZeroLessEq makes 0 ≤ i universal)",
						Cite(ZeroLessEq),
						CnfRefute(),
					)
					a.Backward(
						"∃B N. ∀i. N ≤ i ⇒ P(i) ≤ Q(i)+B — the eventual bound extends everywhere via extend",
						// CiteNode, not Cite: the lemma alone closes this leaf,
						// and Cite's preserving install would leave the goal open.
						CiteNode(extend),
					)
				})
		}),
})}

// boundsIgnoreRaise proves ∀i. N ≤ i ⇒ P(i) ≤ Q(i)+(B+P(N)) from the
// step-case antecedent ∀i. suc(N) ≤ i ⇒ P(i) ≤ Q(i)+B. Case-split on
// suc(N) ≤ i: above the block the antecedent applies directly and the
// raise is pure slack; at the one index it misses, i = N, the raise IS
// the bound.
func boundsIgnoreRaise(
	v *orderOps,
	addAC *ac.Deriver,
	N, B Term,
	P, Q *TermWrapper,
	antSucN Fact,
) Action {
	return Derive(func(a *Argument) {
		i := a.Fix()
		nLeI := a.Assume()

		PN := P.Apply(N)                   // P(N)
		QiB := v.Add(Q.Apply(i), B)        // Q(i) + B
		BAddPN := v.Add(B, PN)             // B + P(N)
		QiBPN := v.Add(Q.Apply(i), BAddPN) // Q(i) + (B + P(N))
		QNB := v.Add(Q.Apply(N), B)        // Q(N) + B

		a.Cases(v.LessEq(v.Suc(N), i))
		a.When(
			"suc(N) ≤ i: P(i) ≤ Q(i)+B (the hyp at i) ≤ Q(i)+(B+P(N)) "+
				"— LessEqAdd + LessEqAddCancel + LessEqTrans ground chain",
			func(b *Argument, sucLeI Fact) {
				b.Show(
					"the step hypothesis at i, padded by P(N) under Q(i)+·",
					By(
						sucLeI,
						// The ∀i-antecedent at i → suc(N)≤i ⇒ P(i)≤Q(i)+B.
						antSucN.At(i),
						// LessEqAdd at (B, P(N)): B ≤ B + P(N).
						At(LessEqAdd, B, PN),
						// LessEqAddCancel at (Q(i), B, B+P(N)): folds
						// B ≤ B+P(N) into Q(i)+B ≤ Q(i)+(B+P(N)).
						At(LessEqAddCancel, Q.Apply(i), B, BAddPN),
						// LessEqTrans at (P(i), Q(i)+B, Q(i)+(B+P(N))).
						At(LessEqTrans, P.Apply(i), QiB, QiBPN)))
			},
		)
		a.Otherwise(
			"¬(suc(N) ≤ i): i = N via NotLessEq + lessThanSucIffLessEq + LessEqAntisym, "+
				"then P(N) ≤ Q(N)+(B+P(N)) closes by LessEqAdd + one AC-regroup",
			func(b *Argument, notSucLeI Fact) {
				iEqN := b.Have(
					"i = N — from ¬(suc(N)≤i) ⇔ i<suc(N) ⇔ i≤N and the hyp N≤i, antisym closes",
					MakeProp(i.Eq(N)),
					// The ¬suc(N)≤i ∧ N≤i ⇒ i=N chain, ground at (i, N):
					// ¬(suc(N)≤i) ⇔ i < suc(N) (NotLessEq)
					// i < suc(N) ⇔ i ≤ N (lessThanSucIffLessEq)
					// i = N ⇔ (i ≤ N ∧ N ≤ i) (LessEqAntisym)
					By(
						notSucLeI,
						nLeI,
						At(NotLessEq, v.Suc(N), i),
						At(LessThanSucIffLessEq, i, N),
						At(LessEqAntisym, i, N)))
				// The i = N rewrite lets the refuter substitute Q(i) → Q(N),
				// P(i) → P(N). The residual is P(N) ≤ Q(N)+(B+P(N)), and
				// LessEqAdd at (P(N), Q(N)+B) supplies it through the regroup
				// P(N)+(Q(N)+B) = Q(N)+(B+P(N)) — one AC-regroup instead of
				// the hand-spelled nat_arith.AddSym+nat_arith.AddAssoc walk.
				b.Show(
					"residual P(N) ≤ Q(N)+(B+P(N)) — LessEqAdd through the regroup",
					By(iEqN, addAC.Eq(v.Add(PN, QNB), v.Add(Q.Apply(N), BAddPN)), At(LessEqAdd, PN, QNB)))
			},
		)
	})
}

// ---------------------------------------------------------------------------
// LessEqMulNonzero — scaling up, except by zero, only grows
// ---------------------------------------------------------------------------

// LessEqMulNonzero — multiplying by a nonzero factor doesn't shrink:
// b ≤ b·x when x ≠ 0 (stated as the disjunction x = 0 ∨ b ≤ b·x).
// The shared strict-mult step of BoundsDivided and BoundsNotZero,
// promoted from their once-duplicated ground triples. The chain:
// posIffNonzero turns ¬(x = 0) into 0 < x, SucLessEqIffLessThan reads
// that as suc(0) ≤ x and ONE spells suc(0) as 1;
// LessEqMulCancel at (b, 1, x) lifts that to b·1 ≤ b·x; nat_arith.MulOne's
// b·1 = b folds the left side onto the goal.
//
// The statement is the family's own phrasing of nonzero-factor
// monotonicity.
var LessEqMulNonzero = lessEqMulNonzeroThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulNonzero",
	Key:  "prop_8b22c08d089c49fc",
	Build: family.Theorem("∀b x:num. x = 0 ∨ b ≤ b * x",
		func(a *Argument, b, x Term) {
			// Numeral 1 spelled bit1(_0) — the DSL's parse of "1"; the
			// spelling is load-bearing for the CNF keys.
			v := ops(a.Ctx())
			one := v.Bit1Op.Apply(v.Zero)

			a.Do(Basic()) // absorb the disjunction: ¬(x₀ = 0) becomes the hyp, b₀ ≤ b₀·x₀ the goal
			nonzero := a.Hyp("¬(x = 0)")
			a.Show(
				"x₀ ≠ 0 gives 1 ≤ x₀, which LessEqMulCancel lifts to b₀·1 ≤ b₀·x₀ — and b₀·1 is b₀",
				By(
					nonzero,
					// x₀ ≠ 0 ⇔ 0 < x₀, then 0 < x₀ ⇔ suc(0) ≤ x₀;
					// nat_arith.OneIsSucZero reads suc(0) back as the numeral 1.
					At(PosIffNonzero, x),
					At(SucLessEqIffLessThan, v.Zero, x),
					nat_arith.OneIsSucZero,
					// LessEqMulCancel at (b, 1, x): b·1 ≤ b·x ⇔ 1 ≤ x ∨ b = 0.
					At(LessEqMulCancel, b, one, x),
					At(nat_arith.MulOne, b))) // b₀·1 = b₀
		}),
})}

// ---------------------------------------------------------------------------
// BoundsDivided — uniform boundedness read as at-most-linear growth
// ---------------------------------------------------------------------------

// BoundsDivided — P is uniformly bounded exactly when n·P(n) grows at
// most linearly in n: a uniform bound B multiplies through by n, and a
// linear bound divides through by every n ≠ 0, with P(0) added to cover
// n = 0.
var BoundsDivided = boundsDividedThm{family.Add(registry.ProofEntry{
	Name: "BoundsDivided",
	Key:  "prop_fce792e8d0fca82a",
	Build: family.Theorem(
		"∀P:(num → num). (∃B:num. ∀n:num. P(n) ≤ B) ⇔ ∃A B:num. ∀n:num. n * P(n) ≤ A * n + B",
		func(a *Argument, P *TermWrapper) {
			v := ops(a.Ctx())
			a.Iff()
			a.Forward(
				"multiply the uniform bound through by n: slope B, constant 0",
				func(b *Argument, uniform Fact) {
					B, bounded := b.Unpack(uniform, "B")
					b.Take(B)      // the slope
					b.Take(v.Zero) // the constant
					n := b.Fix()
					b.Show(
						"P(n) ≤ B gives n·P(n) ≤ n·B = B·n + 0",
						By(
							Normalized,
							bounded.At(n),
							At(LessEqMulCancel, n, P.Apply(n), B),
							At(nat_arith.MulSym, n, B),
							At(nat_arith.AddZero, v.Times.Apply(B, n))))
				})
			a.Backward(
				"the linear bound n·P(n) ≤ A·n + B divides through to the uniform bound P(n) ≤ P(0) + (A + B)",
				func(b *Argument, linear Fact) {
					A, B, linBound := b.Unpack2(linear, "A", "B")
					P0 := P.Apply(v.Zero)
					AB := v.Add(A, B)
					b.Take(v.Plus.Apply(P0, AB))
					n := b.Fix()
					Pn := P.Apply(n)
					An := v.Mul(A, n)
					Bn := v.Mul(B, n)
					b.Show(
						"split on n = 0 — dividing through needs a nonzero factor",
						ByCaseStep(n.Eq(v.Zero),
							Case(
								"n = 0: the linear bound plays no part",
								Given(func(c *Argument, nZero Fact) {
									c.Show(
										"P(0) ≤ P(0) + (A + B)",
										By(Normalized, nZero, At(LessEqAdd, P0, AB)))
								}),
							),
							Case(
								"n ≠ 0: ground the linear bound at n and divide it by n",
								Given(func(c *Argument, nNonzero Fact) {
									slack := c.Have(
										"a nonzero factor does not shrink B",
										"B ≤ B * n",
										By(nNonzero, At(LessEqMulNonzero, B, n)))
									padded := c.Have(
										"so the linear bound's constant B can be raised to B·n",
										"n * P(n) ≤ A * n + B * n",
										By(
											linBound.At(n),
											slack,
											At(LessEqAddCancel, An, B, Bn),
											At(LessEqTrans, v.Mul(n, Pn), v.Plus.Apply(An, B), v.Plus.Apply(An, Bn))))
									divided := c.Have(
										"A·n + B·n = n·(A + B), and the nonzero factor n cancels",
										"P(n) ≤ A + B",
										By(
											Normalized,
											padded,
											nNonzero,
											At(nat_arith.MulSym, n, AB),
											At(nat_arith.RightAddDistrib, A, B, n),
											At(LessEqMulCancel, n, Pn, AB)))
									c.Show(
										"and A + B ≤ P(0) + (A + B)",
										By(
											Normalized,
											divided,
											At(LessEqAdd, AB, P0),
											At(nat_arith.AddSym, AB, P0),
											At(LessEqTrans, Pn, AB, v.Plus.Apply(AB, P0))))
								}),
							),
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// BoundsNotZero — an affine bound that vanishes at the origin is
// really a linear one
// ---------------------------------------------------------------------------

// BoundsNotZero — an affine bound P(m, n) ≤ A·(m + n) + B on a P that
// vanishes at the origin is a linear one, P(m, n) ≤ (A + B)·(m + n): the
// constant B matters only where m + n ≠ 0, and there it is at most
// B·(m + n).
var BoundsNotZero = boundsNotZeroThm{family.Add(registry.ProofEntry{
	Name: "BoundsNotZero",
	Key:  "prop_42e3e3f426cf76cb",
	Build: family.Theorem(
		Statement{
			Binders: "∀P:(num → num → num). ∀A B:num.",
			Hypotheses: []string{
				"P(0, 0) = 0",
				"∀m n:num. P(m, n) ≤ A * (m + n) + B",
			},
			Conclusion: "∃C:num. ∀m n:num. P(m, n) ≤ C * (m + n)",
		},
		func(a *Argument, P *TermWrapper, vanishes Fact, A, B Term, affine Fact) {
			v := ops(a.Ctx())
			AB := v.Add(A, B)
			a.Take(AB) // the slope C
			m := a.Fix()
			n := a.Fix()
			sum := v.Add(m, n)
			As := v.Mul(A, sum)
			Bs := v.Mul(B, sum)
			a.Cases(sum.Eq(v.Zero))
			a.When(
				"m + n = 0: then m = n = 0, and P(0, 0) = 0 lies below any bound",
				func(b *Argument, sZero Fact) {
					b.Show(
						"P(m, n) = P(0, 0) = 0 ≤ (A + B)·(m + n)",
						By(sZero, vanishes, At(nat_arith.AddEqZero, m, n), At(ZeroLessEq, v.Mul(AB, sum))))
				},
			)
			a.Otherwise(
				"m + n ≠ 0: absorb the affine bound's constant B into the slope",
				func(b *Argument, sNonzero Fact) {
					slack := b.Have(
						"a nonzero factor does not shrink B",
						"B ≤ B * (m + n)",
						By(sNonzero, At(LessEqMulNonzero, B, sum)))
					estimate := b.Have(
						"raise the constant to a slope, then refold the two slopes",
						"A * (m + n) + B ≤ (A + B) * (m + n)",
						CalcOrder{
							Le: func(x, y Term) Prop { return MakeProp(v.LessEq(x, y)) },
						}.CalcLeibniz(v.Add(As, B),
							LeLeg(
								v.Add(As, Bs),
								"the constant B raised to B·(m + n)",
								By(slack, At(LessEqAddCancel, As, B, Bs))),
							EqLeg(
								v.Mul(AB, sum),
								"A·(m + n) + B·(m + n) = (A + B)·(m + n)",
								Cite(nat_arith.RightAddDistrib)),
						))
					b.Show(
						"P(m, n) ≤ A·(m + n) + B ≤ (A + B)·(m + n)",
						By(affine.At(m, n), estimate, At(LessEqTrans, P.Apply(m, n), v.Add(As, B), v.Mul(AB, sum))))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// < is well-founded on ℕ
// ---------------------------------------------------------------------------
//
// < is well-founded on ℕ, in its two equivalent readings and their
// two consequences. StrongInduction is the induction reading —
// course-of-values induction, the proof principle; WellOrdering is the
// least-element reading. MaximumExists reads well-ordering upward, turning
// a bound into a maximum, and DownwardInduction, the induction that runs
// from a fixed level down, falls out of the maximum.
//
// ConsecutiveBracket takes the least next term past a number. PowerBracket
// and SquareBracket apply it to powers and squares: every N ≥ 1 lies between
// two consecutive powers of a base b ≥ 2, and every n between consecutive squares.
//
// BoundedIndexEnumeration follows them and reads none of them: it lists
// a predicate bounded by k, in increasing order, by plain induction on k.

// StrongInduction — course-of-values induction: a property that holds
// at n whenever it holds everywhere strictly below n holds everywhere.
// Ordinary induction cannot carry that closure hypothesis, but it can
// carry the STRENGTHENED property "P holds strictly below n" — and once
// that is known at every point, the closure converts it back to P.
//
// Citing this entry at both binders from a plain By whose context does
// not hold the closure installs the clause form, whose prefix is
// (point, predicate): the ∀n lives inside the conclusion and
// normalization hoists it in front of P. The tuple reads in either
// order — the stated (P, n) the typed wrapper spells, or the install's
// (n, P) — since the two types tell the slots apart. Cited at P alone
// under ByInduction, the principle installs as stated, ∀n and all.
var StrongInduction = strongInductionThm{family.Add(registry.ProofEntry{
	Name: "StrongInduction",
	Key:  "prop_192a622dba2963b1",
	Build: family.Theorem(
		Statement{
			Binders: "∀P:(num → bool). ∀n:num.",
			Hypotheses: []string{
				"∀n:num. (∀m:num. m < n ⇒ P(m)) ⇒ P(n)",
			},
			Conclusion: "P(n)",
		},
		func(a *Argument, P Term, closure Fact) {
			below := a.Have(
				"P holds strictly below n, for every n — the property ordinary induction can carry",
				"∀n m:num. m < n ⇒ P(m)",
				Derive(func(b *Argument) {
					n := b.Binder("n")
					b.Induct(n)
					b.Base(
						"nothing lies strictly below 0, so there is nothing to prove there",
						By(LessThanZeroClause),
					)
					b.Step(
						"the points below suc(n) are those below n, together with n itself",
						func(c *Argument, ih Fact) {
							c.Show(
								"the induction hypothesis settles the former, and it "+
									"is also what the closure at n consumes to settle P(n)",
								By(closure.At(n), ih, LessThanSucClause))
						},
					)
				}))

			a.Show(
				"the strengthened property supplies, at every point, exactly the premise the closure consumes",
				By(below, closure))
		}),
})}

// WellOrdering — the least-number principle: a predicate that holds
// anywhere holds at a point with nothing satisfying it below. It is
// StrongInduction read at the complement. Suppose P holds at n. Were
// ¬P closed under the strong-induction step — holding at every point
// at which it holds strictly below — StrongInduction would put ¬P at n
// too. So that step fails somewhere, and a point where it fails is a
// point satisfying P with no P-point strictly below it: the minimum.
var WellOrdering = wellOrderingThm{family.Add(registry.ProofEntry{
	Name: "WellOrdering",
	Key:  "prop_fed09bee023838a4",
	Build: family.Theorem(
		"∀P:(num → bool). (∃n:num. P(n)) ⇔ ∃n:num. P(n) ∧ (∀m:num. m < n ⇒ ¬P(m))",
		func(a *Argument, P *TermWrapper) {
			a.Iff()
			a.Forward(
				"a point satisfying P forces the strong-induction step for ¬P to fail somewhere",
				func(b *Argument, somePoint Fact) {
					n, holds := b.Unpack(somePoint)

					x := Var("x", NumType)
					notP := x.To(Not(P.Apply(x)))

					// StrongInduction at (n₀, λx. ¬P(x)):
					// (∀k. (∀m. m < k ⇒ ¬P(m)) ⇒ ¬P(k)) ⇒ ¬P(n₀)
					b.Show(
						"¬P(n₀) is false, so the step it would follow from is "+
							"false too — and its failure is exactly a least P-point",
						By(Normalized, holds, At(StrongInduction, n, notP)))
				},
			)
			a.Backward(
				"a least point satisfying P satisfies P",
				func(b *Argument, least Fact) {
					b.Show(
						"drop the minimality conjunct",
						By(Normalized, least))
				},
			)
		}),
})}

// MaximumExists — a predicate that holds somewhere and is bounded above
// attains its bound. The maximum arrives as a LEAST element rather than
// a greatest one: the numbers bounding P are themselves a predicate,
// which the given bound makes non-empty, so WellOrdering hands over the
// least bound m — and all the work is showing that P reaches it, by
// cases on m.
var MaximumExists = maximumExistsThm{family.Add(registry.ProofEntry{
	Name: "MaximumExists",
	Key:  "prop_63bd83e3b397ee69",
	Build: family.Theorem(
		"∀P:(num → bool). "+
			"    (∃x:num. P(x)) ∧ (∃M:num. ∀x:num. P(x) ⇒ x ≤ M) ⇔ ∃m:num. P(m) ∧ (∀x:num. P(x) ⇒ x ≤ m)",
		func(a *Argument, P *TermWrapper) {
			v := ops(a.Ctx())

			a.Iff()
			a.Forward(
				"the maximum is produced as the LEAST of P's bounds",
				func(b *Argument, nonemptyBounded Fact) {
					bound, x := Var("bound", NumType), Var("x", NumType)
					// λbound. ∀x. P(x) ⇒ x ≤ bound — "bound bounds P", the
					// predicate well-ordering is read at.
					boundsP := bound.To(ForAll(x)(P.Apply(x).Imply(v.LessEq(x, bound))))

					m, least := b.Obtain(
						"the given bound makes «bounds P» non-empty, so well-ordering returns its least element",
						"∃m:num. (∀x:num. P(x) ⇒ x ≤ m) ∧ (∀j:num. j < m ⇒ ¬∀x:num. P(x) ⇒ x ≤ j)",
						By(nonemptyBounded, At(WellOrdering, boundsP)))

					attained := b.Have(
						"P reaches its least bound",
						"P(m₀)",
						Derive(func(c *Argument) {
							positive := c.Unless(
								m.Eq(v.Zero),
								"settled when the least bound is 0, since 0 bounds nothing but itself",
								Given(func(d *Argument, isZero Fact) {
									d.Show(
										"the zero clause turns «bounded by 0» into «is 0», and P has a point to apply it to",
										By(isZero, nonemptyBounded, least, LessEqZeroClause))
								}),
							)

							k, isSuc := c.Obtain(
								"a non-zero number is a successor",
								"∃k:num. m₀ = suc(k)",
								By(Normalized, positive, At(peano.Cases, m)))

							escapes := c.Have(
								"k₀ lies below suc(k₀) = m₀, so minimality denies it the bounding property",
								"∃x:num. P(x) ∧ ¬(x ≤ k₀)",
								By(least, isSuc, LessThanSucClause))
							point, beyond := c.Unpack(escapes)

							c.Show(
								"bounded by suc(k₀) but not by k₀, the escaping point can only BE suc(k₀)",
								By(beyond, least, isSuc, At(LessEqSucClause, point, k)))
						}))

					b.Show(
						"m₀ is the maximum asked for: a P-point that bounds P",
						By(attained, least))
				},
			)
			a.Backward(
				"a maximum is a P-point and a bound for P",
				func(b *Argument, max Fact) {
					b.Show(
						"the two existentials on the left are both witnessed by that one point",
						By(Normalized, max))
				},
			)
		}),
})}

// DownwardInduction — the induction principle that runs downward from a
// fixed level: if P holds from m upward, and P at a point below m
// follows from P everywhere strictly above that point, then P holds
// everywhere. It needs no induction of its own. A counterexample cannot
// sit at or above m, so m bounds the counterexamples, and MaximumExists
// turns them into a GREATEST counterexample. That point lies below m
// and has P at every point above it — which is exactly what the
// downward step consumes, so P holds there after all.
//
// Citing this entry: witnesses run (point, level, predicate) — the
// prefix-merge class again, as for StrongInduction above. The
// conclusion's ∀n hoists into the install prefix ahead of the two the
// statement binds, so a ground tuple reads positionally against
// (n, m, P).
var DownwardInduction = downwardInductionThm{family.Add(registry.ProofEntry{
	Name: "DownwardInduction",
	Key:  "prop_5fd03f3cbaa5685a",
	Build: family.Theorem(
		Statement{
			Binders: "∀P:(num → bool). ∀m n:num.",
			Hypotheses: []string{
				"∀k:num. m ≤ k ⇒ P(k)",
				"∀k:num. k < m ∧ (∀p:num. k < p ⇒ P(p)) ⇒ P(k)",
			},
			Conclusion: "P(n)",
		},
		func(a *Argument, P *TermWrapper, m Term, hyps Fact) {
			x := Var("x", NumType)
			// λx. ¬P(x) — the counterexamples, as a predicate.
			notP := x.To(Not(P.Apply(x)))

			someCounter := a.SupposeNot() // ¬∀n. P(n) — some point is a counterexample

			bounded := a.Have(
				"m₀ bounds the counterexamples: at or above m₀ the upward hypothesis already gives P",
				"∀x:num. ¬P(x) ⇒ x ≤ m₀",
				By(hyps, NotLessEq, LessEqOfLessThan))

			_, greatest := a.Obtain(
				"non-empty and bounded, the counterexamples have a greatest one",
				"∃n:num. ¬P(n) ∧ (∀x:num. ¬P(x) ⇒ x ≤ n)",
				By(someCounter, bounded, At(MaximumExists, notP)))

			a.Show(
				"the greatest counterexample lies below m₀ and nothing above it is "+
					"one — the downward step's two premises, which then contradict it",
				By(greatest, hyps, NotLessEq))
		}),
})}

// ConsecutiveBracket — a sequence starting at most N and eventually exceeding N
// crosses N between consecutive terms. Take the least index whose next term
// exceeds N; its current term is bounded by the initial bound or minimality.
var ConsecutiveBracket = consecutiveBracketThm{family.Add(registry.ProofEntry{
	Name: "ConsecutiveBracket",
	Key:  "prop_73719ab6cb940ab5",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → num). ∀N:num.",
		Hypotheses: []string{
			"f(0) ≤ N",
			"∃k:num. N < f(k + 1)",
		},
		Conclusion: "∃i:num. f(i) ≤ N ∧ N < f(i + 1)",
	}, func(a *Argument, f *Expr[Fun[Nat, Nat]], N *Expr[Nat], initial, exceeds Fact) {
		i, least := a.ObtainAs[Nat](
			"take the least i whose next term exceeds N",
			"∃i:num. N < f(i + 1) ∧ (∀m:num. m < i ⇒ ¬(N < f(m + 1)))",
			By(exceeds, WellOrdering.At(a.TermAs[Set[Nat]]("λi:num. N < f(i + 1)"))))
		parts := a.Conjuncts(
			least,
			"N < f(i + 1)",
			"no smaller m has N < f(m + 1)")
		above, minimal := parts[0], parts[1]
		a.Take(i)
		a.Cases(a.TermAs[Bool]("i = 0"))
		a.When(
			"i = 0: the initial term is at most N",
			func(c *Argument, zero Fact) {
				c.Show(
					"and the next term exceeds N by the choice of i",
					ByArith(above, zero, initial))
			})
		a.Otherwise(
			"i = k + 1: minimality at k bounds the current term",
			func(c *Argument, nonzero Fact) {
				k, predecessor := c.ObtainAs[Nat](
					"i is the successor of some k",
					"∃k:num. i = k + 1",
					Witness(c.TermAs[Nat]("i - 1")),
					ByArith(nonzero))
				c.Show(
					"N < f(k + 1) fails, so f(i) is at most N",
					ByArith(above, predecessor, minimal.At(k)))
			})
	}),
})}

// PowerBracket — every N ≥ 1 lies between two consecutive powers of a base
// b ≥ 2. The powers start at 1 ≤ N and exceed N by exponent N + 1.
var PowerBracket = powerBracketThm{family.Add(registry.ProofEntry{
	Name: "PowerBracket",
	Key:  "prop_8626521e0503109e",
	Build: family.Theorem(Statement{
		Binders: "∀b N:num.",
		Hypotheses: []string{
			"2 ≤ b",
			"1 ≤ N",
		},
		Conclusion: "∃i:num. b ^ i ≤ N ∧ N < b ^ (i + 1)",
	},
		func(a *Argument, b, N *Expr[Nat], base, positive Fact) {
			exceeds := a.Have(
				"N < b^(N + 1), since N + 1 < b^(N + 1)",
				"N < b ^ (N + 1)",
				ByArith(base, LessThanPowSelf.At(b, a.TermAs[Nat]("N + 1"))))
			a.Show(
				"the power sequence crosses N between consecutive terms",
				By(
					positive,
					exceeds,
					nat_arith.NatPow,
					ConsecutiveBracket.At(a.TermAs[Fun[Nat, Nat]]("λi:num. b ^ i"), N)))
		}),
})}

// SquareBracket — every n lies between two consecutive squares.
// The squares start at 0 ≤ n and exceed n by index n + 1.
var SquareBracket = squareBracketThm{family.Add(registry.ProofEntry{
	Name: "SquareBracket",
	Key:  "prop_e4ddac4ca4254fa6",
	Build: family.Theorem(
		"∀n:num. ∃m:num. m * m ≤ n ∧ n < (m + 1) * (m + 1)",
		func(a *Argument, n *Expr[Nat]) {
			exceeds := a.Have(
				"n < (n + 1)²",
				"n < (n + 1) * (n + 1)",
				ByArith())
			a.Show(
				"the square sequence crosses n between consecutive terms",
				By(
					exceeds,
					ZeroLessEq.At(n),
					nat_arith.MulLeftZeroClause,
					ConsecutiveBracket.At(a.TermAs[Fun[Nat, Nat]]("λm:num. m * m"), n)))
		}),
})}

// BoundedIndexEnumeration — the indices below k of a property are listed
// in increasing order: by induction on k, the indices below k + 1 are those
// below k, followed by k itself when it has the property.
var BoundedIndexEnumeration = boundedIndexEnumerationThm{family.Add(registry.ProofEntry{
	Name: "BoundedIndexEnumeration",
	Key:  "prop_67aadc27164332a9",
	Build: family.Theorem(Statement{
		Binders: "∀k:num. ∀P:(num → bool).",
		Hypotheses: []string{
			"∀l:num. P(l) ⇒ l < k",
		},
		Conclusion: "∃q:num. ∃e:(num → num). " +
			"    (∀a b:num. a < b ∧ b < q ⇒ e(a) < e(b)) ∧ " +
			"    (∀a:num. a < q ⇒ P(e(a))) ∧ " +
			"    (∀l:num. P(l) ⇒ ∃a:num. a < q ∧ e(a) = l)",
	}, func(a *Argument) {
		a.Induct("k")
		a.Base(
			"no index lies below 0: the empty list",
			func(b *Argument) {
				b.FixAs[Fun[Nat, Bool]]("P")
				bound := b.Assume()
				b.Take(b.TermAs[Nat]("0"))
				b.Take(b.TermAs[Fun[Nat, Nat]]("λa:num. 0"))
				b.Show(
					"nothing to list, as no index lies below 0",
					By(
						bound,
						b.Have(
							"no index lies below 0",
							"∀l:num. ¬(l < 0)",
							ByArith())))
			})
		a.Step(
			"list the indices below k, then k itself if it has the property",
			func(b *Argument, ih Fact) {
				b.FixAs[Fun[Nat, Bool]]("P")
				bound := b.Assume()
				below := b.TermAs[Fun[Nat, Bool]]("λl:num. P(l) ∧ l < k")
				belowK := b.Have(
					"the indices of P below k lie below k",
					"∀l:num. P(l) ∧ l < k ⇒ l < k",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("l")
						c.Show(
							"an index of P below k lies below k",
							By(c.Assume()))
					}))
				q, e, listed := b.Unpack2As[Nat, Fun[Nat, Nat]](
					GroupPremises(belowK, ih.At(below)),
					"q",
					"e")
				parts := b.Conjuncts(
					listed,
					"e increases",
					"e lists indices of P below k",
					"every index of P below k is listed")
				increasing, listsBelow, onto := parts[0], parts[1], parts[2]
				b.Cases(b.TermAs[Bool]("P(k)"))
				b.When(
					"k has the property: list it after the others",
					func(c *Argument, atK Fact) {
						grows := c.Have(
							"the list with k appended increases",
							"∀a b:num. a < b ∧ b < suc(q) ⇒ COND(a = q, k, e(a)) < COND(b = q, k, e(b))",
							Derive(func(d *Argument) {
								aIndex := d.FixAs[Nat]("a")
								bIndex := d.FixAs[Nat]("b")
								given := d.Assume()
								facts := d.Have(
									"a lies below q, and b is q or below it",
									"¬(a = q) ∧ a < q ∧ (b = q ∨ b < q)",
									ByArith(given))
								d.Cases(d.TermAs[Bool]("b = q"))
								d.When(
									"b is the new last place, holding k",
									func(g *Argument, last Fact) {
										g.Show(
											"the earlier entries lie below k",
											By(listsBelow.At(aIndex), facts, last))
									})
								d.Otherwise(
									"both places are old",
									func(g *Argument, old Fact) {
										bothOld := g.Have(
											"b lies below q",
											"b < q",
											ByArith(facts, old))
										g.Show(
											"the old list increases",
											By(increasing.At(aIndex, bIndex), given, bothOld, facts, old))
									})
							}))
						lists := c.Have(
							"its entries have the property",
							"∀a:num. a < suc(q) ⇒ P(COND(a = q, k, e(a)))",
							Derive(func(d *Argument) {
								aIndex := d.FixAs[Nat]("a")
								aLt := d.Assume()
								d.Cases(d.TermAs[Bool]("a = q"))
								d.When(
									"the last entry is k",
									func(g *Argument, last Fact) {
										g.Show(
											"k has the property",
											By(atK, last))
									})
								d.Otherwise(
									"an old entry",
									func(g *Argument, old Fact) {
										g.Show(
											"listed before",
											By(
												listsBelow.At(aIndex),
												g.Have(
													"a lies below q",
													"a < q",
													ByArith(aLt, old)),
												old))
									})
							}))
						covers := c.Have(
							"every index with the property is listed",
							"∀l:num. P(l) ⇒ ∃a:num. a < suc(q) ∧ COND(a = q, k, e(a)) = l",
							Derive(func(d *Argument) {
								l := d.FixAs[Nat]("l")
								has := d.Assume()
								d.Cases(d.TermAs[Bool]("l = k"))
								d.When(
									"k sits at the last place q",
									func(g *Argument, isK Fact) {
										g.Take(q)
										g.Show(
											"k sits at q, which lies below suc(q)",
											By(
												isK,
												g.Have(
													"q lies below suc(q)",
													"q < suc(q)",
													ByArith())))
									})
								d.Otherwise(
									"an index below k sits at its old place",
									func(g *Argument, notK Fact) {
										early := g.Have(
											"l lies below k",
											"l < k",
											ByArith(bound.At(l), has, notK))
										place, at := g.UnpackAs[Nat](GroupPremises(has, early, onto.At(l)), "c")
										placed := g.Conjuncts(
											at,
											"c lies below q",
											"e(c) = l")
										g.Take(place)
										g.Show(
											"c lies below suc(q), is not q, and e lists l there",
											By(
												placed[1],
												g.Have(
													"c lies below suc(q) and is not q",
													"c < suc(q) ∧ ¬(c = q)",
													ByArith(placed[0]))))
									})
							}))
						c.Take(c.TermAs[Nat]("suc(q)"))
						c.Take(c.TermAs[Fun[Nat, Nat]]("λa:num. COND(a = q, k, e(a))"))
						c.Show(
							"the extended list",
							By(grows, lists, covers))
					})
				b.Otherwise(
					"k lacks the property: the indices below k + 1 are those below k",
					func(c *Argument, notK Fact) {
						lists := c.Have(
							"the old entries have the property",
							"∀a:num. a < q ⇒ P(e(a))",
							By(listsBelow))
						covers := c.Have(
							"every index with the property lies below k, so is listed",
							"∀l:num. P(l) ⇒ ∃a:num. a < q ∧ e(a) = l",
							Derive(func(d *Argument) {
								l := d.FixAs[Nat]("l")
								has := d.Assume()
								other := d.Have(
									"l is not k",
									"¬(l = k)",
									By(Normalized, has, notK))
								early := d.Have(
									"so l lies below k",
									"l < k",
									ByArith(bound.At(l), has, other))
								d.Show(
									"listed before",
									By(onto.At(l), has, early))
							}))
						c.Take(q)
						c.Take(e)
						c.Show(
							"the old list",
							By(increasing, lists, covers))
					})
			})
	}),
})}
