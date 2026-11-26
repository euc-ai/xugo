package serve

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
)

// arithCloses reports whether the unified arith move FULLY discharges goal:
// ArithTactic rewrites the conclusion (to ⊤ when fully decided) and the standard
// TrivialSimplifyTactic finishes a ⊤ residual via DerivesTrue — the same close
// path the engine's `_Arith + _TrivialSimplify` composite uses. A bare
// `ArithTactic != nil` only signals progress, which a partial subterm rewrite (an
// eq-hyp substitution / parity bridge) can trigger without closing — too weak to
// assert closure. (Sufficient here because every child must close: a single-atom
// goal has one child, which closes iff it reduced to ⊤.)
func unscopedArithTactic(goal core.Prop) *tactic.SubGoals {
	return tactic.ArithTactic(goal, omega.UnscopedArithPolicy(), nil)
}

func arithCloses(goal core.Prop) bool {
	sg := unscopedArithTactic(goal)
	if sg == nil || sg.Size() == 0 {
		return false
	}
	for i := 0; i < sg.Size(); i++ {
		ts := tactic.TrivialSimplifyTactic(sg.ChildGoal(i))
		if ts == nil || ts.Size() != 0 {
			return false
		}
	}
	return true
}

// TestInstallNatBundleBindingRing: with the corpus-backed bundle installed, a
// ring goal closes through the real path. The corpus test binary installs no
// placeholder fabricator (production behavior, omega/bundle.go), so if any
// ring/norm_num leaf fell back to a placeholder it would panic at the seam — a
// green run thus proves the leaves bound their real corpus theorems.
func TestInstallNatBundleBindingRing(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	// Sound through the corpus today: additive AC / associativity, and numeral
	// ADDITION (addB* ↔ NumeralAdd, same bit recursion). These exercise eqLeaf
	// (AC) + clauseLeaf (the clause packs) + the projectMatch bit-recursion leaves; with no
	// placeholder fabricator in this test binary, a green run guarantees every leaf
	// bound its real corpus theorem (a degrade would have panicked).
	goals := []string{
		"m:num, n:num ⊢ m + n = n + m",                    // AC (+)
		"a:num, b:num, c:num ⊢ a + (b + c) = (a + b) + c", // assoc (+)
		"2 + 3 = 5", // numeral addition (NumeralAdd)
	}
	for _, g := range goals {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.RingTactic(res.Prop) == nil { // closeByOmega forces the bundle leaves
				t.Fatalf("RingTactic declined to close: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingLinarith: with the corpus-backed bundle installed,
// real linear-arithmetic goals close through the populated linarith fields
// (duality NotLessThan/NotLessEq, LessEqOfEq, the LessEqOfEqSwapped derivation, the curried
// LessEqAdd2 family, the reordered LessEqAddCancel, the NumeralLessThan/NumeralLessEq/NumeralEq comparison
// leaves incl. the bare-fact projector). A degrade to a placeholder panics (no
// fabricator in this test binary) — so a green run proves every exercised leaf
// bound its real corpus theorem (or adapter). LinarithTactic is the pure-ℚ entry (the sound one); the
// goals use unit Farkas coefficients, so the scale leaves (leScale/ltScale) are
// not exercised here — coefficient>1 scaling is covered by omega's own tests.
func TestInstallNatBundleBindingLinarith(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	goals := []string{
		"a:num, b:num, c:num, a <= b, b <= c ⊢ a <= c", // ≤ transitivity
		"a:num, b:num, a < b ⊢ a <= b",                 // strict ⇒ non-strict
		"a:num, b:num, a <= b, b <= a ⊢ a = b",         // antisymmetry close (=)
		"a:num, b:num, c:num, a < b, b < c ⊢ a < c",    // < transitivity
	}
	for _, g := range goals {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.LinarithTactic(res.Prop) == nil { // closeByOmega forces the bundle leaves
				t.Fatalf("LinarithTactic declined to close: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingPolynomialLinarith: linarith over the MONOMIAL
// basis under the real bundle (domain.go polyMul) — hypothesis equations with
// polynomial content combine with the goal in the shared canonical basis, so a
// premise like `2·A = n·suc(n)` is one unit-λ Farkas combination away from
// `2·(A+suc n) = suc(n)·suc(suc n)` (transcript A5's induction leaf, the
// leaf-automation north star). Kernel-verified end-to-end: no placeholder
// fabricator, so every scale/add/cancel leaf and the normalizeProof monomial
// expansion (mulProofFull) compose real corpus theorems.
func TestInstallNatBundleBindingPolynomialLinarith(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	linGoals := []string{
		// The A5 leaf: IH ⊢ goal, no manual rw, no distributivity premises.
		"A:num, n:num, 2 * A = n * suc(n) ⊢ 2 * (A + suc(n)) = suc(n) * suc(suc(n))",
		// Sum of odd numbers: s = n² ⊢ s + (2n+1) = (n+1)².
		"s:num, n:num, s = n * n ⊢ s + (2 * n + 1) = suc(n) * suc(n)",
		// Commuted spellings are the same monomial.
		"a:num, b:num, c:num, a * b < c ⊢ b * a < c + 1",
		// A monomial is a nonnegative unknown (the injected 0 ≤ b·c row).
		"a:num, b:num, c:num ⊢ a <= a + b * c",
	}
	for _, g := range linGoals {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.LinarithTactic(res.Prop) == nil { // closeByOmega forces the bundle leaves
				t.Fatalf("LinarithTactic declined to close: %s", g)
			}
		})
	}

	// The integer layer's rounding cut over a monomial atom: 2ab < 2c+2 ⟶ ab ≤ c
	// (real LessEqRightDivEq + DivModUniq; not ℚ-valid, so LinarithTactic declines).
	t.Run("rounding cut over monomial", func(t *testing.T) {
		res := dsl.ParsePropText("a:num, b:num, c:num, 2 * (a * b) < 2 * c + 2 ⊢ a * b <= c")
		if len(res.Errors) > 0 {
			t.Fatalf("parse: %s", res.Errors[0].Message)
		}
		if tactic.LinarithTactic(res.Prop) != nil {
			t.Fatal("LinarithTactic unexpectedly closed the integrality goal (ℚ model exists)")
		}
		if tactic.OmegaTactic(res.Prop) == nil {
			t.Fatal("OmegaTactic declined the rounding cut over a monomial atom")
		}
	})

	// The unified arith move (the engine closer's composite) on the A5 leaf.
	t.Run("arith composite closes A5", func(t *testing.T) {
		res := dsl.ParsePropText(
			"A:num, n:num, 2 * A = n * suc(n) ⊢ 2 * (A + suc(n)) = suc(n) * suc(suc(n))")
		if len(res.Errors) > 0 {
			t.Fatalf("parse: %s", res.Errors[0].Message)
		}
		if !arithCloses(res.Prop) {
			t.Fatal("arith composite declined the A5 induction leaf")
		}
	})
}

// TestInstallNatBundleBindingMultiplication: numeral MULTIPLICATION and coefficient>1
// linarith close with the real bundle installed now that mulB0/mulB1 are DERIVED
// (Bit0/Bit1 + RightAddDistrib + the MulClauses suc clause) rather than
// projected from NumeralMul (whose both-operand recursion can't supply them). A
// placeholder degrade panics (no fabricator in this test binary).
func TestInstallNatBundleBindingMultiplication(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	t.Run("2 * 3 = 6", func(t *testing.T) {
		res := dsl.ParsePropText("2 * 3 = 6")
		if len(res.Errors) > 0 {
			t.Fatalf("parse: %s", res.Errors[0].Message)
		}
		if tactic.RingTactic(res.Prop) == nil {
			t.Fatal("RingTactic declined 2*3=6")
		}
	})
	t.Run("coeff>1 linarith: a<b ⊢ 2*a < 2*b", func(t *testing.T) {
		res := dsl.ParsePropText("a:num, b:num, a < b ⊢ 2 * a < 2 * b")
		if len(res.Errors) > 0 {
			t.Fatalf("parse: %s", res.Errors[0].Message)
		}
		if tactic.LinarithTactic(res.Prop) == nil {
			t.Fatal("LinarithTactic declined a<b ⊢ 2a<2b (coeff-2 scale via ltScale)")
		}
	})
}

// TestInstallNatBundleBindingReflexiveEq: reflexive numeral equality NormNatEq(n,n)
// closes with the real bundle installed. The recursion bottoms at eqZeroZero
// (`0=0 ⇔ ⊤`), which the corpus NumeralEq has NO clause for (it closes by refl)
// — eqZeroZero proves it by reflexivity instead of projecting, so a real-corpus
// run (no placeholder fabricator) survives.
func TestInstallNatBundleBindingReflexiveEq(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, n := range []uint64{0, 1, 6, 8, 42} {
		if _, ok := omega.NormNatEq(omega.Numeral(n), omega.Numeral(n)); !ok {
			t.Fatalf("NormNatEq(%d,%d) declined", n, n)
		}
	}
}

// TestInstallNatBundleBindingSymbolicProduct: full-multivariate SYMBOLIC products
// (atom·atom) close with the real bundle installed now that monoMerge (the multiplicative AC
// sort, MulSortRewrite) and mulRearrange4 (a fixed associativity/commutativity
// regroup) are DERIVED from the commuteMUL/associateMUL leaves (MulSym/MulAssoc)
// rather than placeholderEq. A degrade panics.
func TestInstallNatBundleBindingSymbolicProduct(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	goals := []string{
		"a:num, b:num ⊢ a * b = b * a",                                   // commutativity
		"a:num, b:num, c:num ⊢ (a + b) * c = a * c + b * c",              // distribution
		"a:num, b:num, c:num ⊢ a * (b * c) = (a * b) * c",                // associativity
		"a:num, b:num ⊢ (a + b) * (a + b) = a * a + 2 * (a * b) + b * b", // binomial
	}
	for _, g := range goals {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.RingTactic(res.Prop) == nil { // closeByOmega forces the bundle leaves
				t.Fatalf("RingTactic declined to close: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingInteger: with the corpus bundle installed, the
// integer (Presburger) layer is real-backed. `2a ≠ 1` is a genuine
// integer-gap goal — ℚ-Farkas cannot refute the negation `2a = 1` (a = ½ is a
// rational model), so OmegaTactic falls through to the integer extension, whose
// GCD-equality contradiction (groundedGcdEq → notDivides) is a soundness-guard
// placeholder until a bundle backs it. The bundle backs it with ModEqZero
// (`(∃q. m=q·n) ⇔ (0 = nat_mod(m, n))`) + DivModUniq (the nat_mod evaluator)
// — both pure `num`, no `divides`/real — so the guard does not fire and the
// goal closes. (prover/tactic's TestOmegaTactic asserts the SAME goal DECLINES
// with no bundle installed: placeholder + guard.)
func TestInstallNatBundleBindingInteger(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	goals := []string{
		"a:num ⊢ 2 * a != 1", // GCD-equality → groundedGcdEq → notDivides(2,1) real
	}
	for _, g := range goals {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.OmegaTactic(res.Prop) == nil {
				t.Fatalf("OmegaTactic declined to close (integer leaf not real?): %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingIntCut: the integer rounding cut closes goals that
// are integer-true but ℚ-SAT once negated, so LinarithTactic declines and only
// the integer extension (intCut, via LessEqRightDivEq + DivModUniq + ring) can close
// them. With the corpus bundle installed, closeByOmega FORCES the cut's
// LessEqRightDivEq / DivModUniq / SucLessEqIffLessThan promises to real kernel certs — so a
// green run proves intCut is not a placeholder. Each goal is also asserted
// to fire NO unsound integer leaf (the soundness counter is unchanged), which is
// what flips OmegaTactic from "decline" to "close" for the integer layer.
func TestInstallNatBundleBindingIntCut(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	goals := []string{
		"a:num, 2*a <= 1 ⊢ 2*a < 1",                    // 1-var rounding (g=2), strict goal
		"a:num, b:num, 2*a <= 2*b + 1 ⊢ 2*a < 2*b + 1", // two-sided rounding (g=2)
	}
	for _, g := range goals {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			// LinarithTactic (pure ℚ) must DECLINE — these need integrality.
			if tactic.LinarithTactic(res.Prop) != nil {
				t.Fatalf("LinarithTactic unexpectedly closed (goal is not ℚ-valid): %s", g)
			}
			if tactic.OmegaTactic(res.Prop) == nil { // closeByOmega forces the cut's leaves
				t.Fatalf("OmegaTactic declined to close: %s", g)
			}
		})
	}
}

// TestInstallNatBundleArithSimplify: the unified `arith` tactic under the
// real bundle. The identity laws must rewrite identity redexes through
// the real AddClauses / MulClauses leaves (incl. the `a*1` leaf mulOneR)
// — a placeholder degrade panics (no fabricator in this test binary). The
// decider must close an integer-specific comparison (`2a ≠ 1`, ℚ-contingent so it routes through
// the integer extension) WITHOUT declining — what the intCut/notDivides
// theorems buy: the soundness guard does not fire, so an integer-valid
// comparison atom collapses to ⊤ instead of being left untouched.
func TestInstallNatBundleArithSimplify(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	// Identity simplification through real corpus leaves, inside the
	// unified ArithTactic; the rewrite reduces `a+0 = a` (after the fold a+0→a)
	// to `a = a`, then BoolRewrite's `l=l → ⊤`, closing the goal.
	for _, g := range []string{
		"a:num ⊢ a + 0 = a", // AddClauses (a+0)
		"a:num ⊢ a * 1 = a", // MulClauses (a*1) — exercises mulOneR
	} {
		t.Run("simp "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined: %s", g)
			}
		})
	}

	// A: integer-specific decision does not decline under the real bundle.
	t.Run("decide 2*a != 1 → ⊤ (integer-specific, no decline)", func(t *testing.T) {
		res := dsl.ParsePropText("a:num ⊢ 2 * a != 1")
		if len(res.Errors) > 0 {
			t.Fatalf("parse: %s", res.Errors[0].Message)
		}
		if unscopedArithTactic(res.Prop) == nil {
			t.Fatal("ArithTactic declined an integer-valid comparison — " +
				"the integer extension should now decide it under the bundle")
		}
	})
}

// TestInstallNatBundleBindingSub: the subtraction (monus) layer under the real
// bundle. Two halves, both run with no placeholder fabricator (any
// degrade in a SubEqZero/SubAddCancel/AddSubLeftCancel/LessEqAdd/LessEqTotal leaf panics at the seam):
//
// - SIMPLIFICATION via ArithTactic — subCancel rewrites a cancellation
// `a-b → d` (AddSubLeftCancel + ring); subTrunc rewrites a truncation `a-b → 0`
// (SubEqZero + LessEqAdd + ring). The conclusion then collapses to `x = x → ⊤`.
//
// - DECISION via the monus case-split — an irreducible `a-b` (mixed sign, not
// simplifiable) in a comparison that is NOT ℚ-valid (LinarithTactic
// declines), closed only by the LessEqTotal split into SubEqZero / SubAddCancel
// `+`-facts per branch. A green run with the soundness counter unchanged
// proves the split composes real corpus lemmas end-to-end.
func TestInstallNatBundleBindingSub(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	// Simplification: cancellation + truncation rewrites, then ⊤.
	for _, g := range []string{
		"a:num ⊢ a - 0 = a",                             // subCancel, d = a
		"a:num ⊢ a - a = 0",                             // subCancel, d = 0
		"a:num, b:num ⊢ (a + b) - a = b",                // subCancel, compositional
		"a:num, b:num, c:num ⊢ (a + b + c) - a = b + c", // subCancel, compositional
		"a:num ⊢ 0 - a = 0",                             // subTrunc (SubEqZero)
		"a:num, b:num ⊢ a - (a + b) = 0",                // subTrunc, compositional
	} {
		t.Run("simp "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined (subtraction leaf not real?): %s", g)
			}
		})
	}

	// Decision: irreducible monus in a comparison, closed by the case split.
	for _, g := range []string{
		"a:num, b:num ⊢ a - b <= a",    // a-b ≤ minuend (always; needs split)
		"a:num, b:num ⊢ a - b < a + 1", // strict variant
	} {
		t.Run("split "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			// Not ℚ-valid (a-b is a free atom to linarith) — pure ℚ must decline.
			if tactic.LinarithTactic(res.Prop) != nil {
				t.Fatalf("LinarithTactic unexpectedly closed (monus atom is free): %s", g)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined — the monus case split should close it: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingDivMod: nat_div/nat_mod layer under the real bundle.
// Three tiers of coverage, all with no placeholder fabricator (a degrade in
// any wired nat_div/nat_mod leaf would panic at the seam):
//
// - SIMPLIFICATION — trivial-divisor leaves: nat_div(m, 1), nat_mod(m, 1) (via DivModUniq +
// ring witness q=m, r=0), nat_div(m, 0) / nat_mod(m, 0) (via DivZero / ModZero),
// nat_mod(n,n) (via ModRefl).
// - UNCONDITIONAL ENRICHMENT — ModLessEq / DivLessEq injection closes goals where
// the linear core needed a bound on an opaque nat_div/nat_mod atom.
// - CONDITIONAL ENRICHMENT — Division's strict bound + canonical identity at
// literal-nonzero divisors; ModLessThan (m=nat_mod(m,n) when m<n discharges);
// DivRefl (nat_div(n,n)=1 when n≠0 discharges via 0<n in hyps).
func TestInstallNatBundleBindingDivMod(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	// Simplification (trivial syntactic redexes).
	for _, g := range []string{
		"m:num ⊢ nat_div(m, 1) = m",         // DivModUniq witness
		"m:num ⊢ nat_mod(m, 1) = 0",         // DivModUniq witness
		"m:num ⊢ nat_div(m, 0) = 0",         // DivZero
		"m:num ⊢ nat_mod(m, 0) = m",         // ModZero
		"n:num ⊢ nat_mod(n, n) = 0",         // ModRefl
		"m:num ⊢ nat_div(m, 1) + 3 = m + 3", // nat_div_mod.DivOne then ring
	} {
		t.Run("simp "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined a nat_div/nat_mod simp goal: %s", g)
			}
		})
	}

	// Unconditional enrichment (ModLessEq / DivLessEq only).
	for _, g := range []string{
		"m:num, n:num ⊢ nat_mod(m, n) <= m",
		"m:num, n:num ⊢ nat_div(m, n) <= m",
		"m:num, a:num, b:num ⊢ m + nat_mod(a, b) <= m + a", // compositional ModLessEq
	} {
		t.Run("ModLessEq/DivLessEq "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined a ModLessEq/DivLessEq goal: %s", g)
			}
		})
	}

	// Conditional enrichment (Division / ModLessThan / DivRefl / DivEqZero with side
	// discharge) + DivMult2 common-factor simp.
	for _, g := range []string{
		"m:num ⊢ nat_mod(m, 5) < 5",                            // Division, literal-nonzero divisor
		"m:num, n:num, m < n ⊢ nat_mod(m, n) = m",              // ModLessThan, m<n in hyps
		"n:num, n >= 1 ⊢ nat_div(n, n) = 1",                    // DivRefl, n≠0 from n≥1
		"m:num ⊢ nat_mod(m, 5) <= 4",                           // Division strict bound + linarith
		"m:num, 0 < n, n:num ⊢ nat_mod(m, n) <= m",             // unconditional, but exercises the path
		"m:num, n:num, m < n ⊢ nat_div(m, n) = 0",              // DivEqZero, m<n + nonneg ⇒ n>0
		"a:num, b:num ⊢ nat_div(2 * a, 2 * b) = nat_div(a, b)", // DivMult2 common-factor simp
		// Symbolic-n=0 case-split tier (proveDivModSplitOnZero) + proveNeqZero
		// ¬(n=0)-hyp route:
		"m:num, n:num, n != 0 ⊢ nat_mod(m, n) < n", // n≠0 hyp via proveNeqZero direct
		"m:num, n:num, n = 0 ⊢ nat_mod(m, n) = m",  // n=0 hyp → split's n=0 branch
		"m:num, n:num, n = 0 ⊢ nat_div(m, n) = 0",  // n=0 hyp → split's n=0 branch
	} {
		t.Run("conditional "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined a conditional nat_div/nat_mod goal: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingExp: nat_pow under the real bundle.
// Split into two tiers, matching the user-facing surface:
//
// - ArithTactic auto-fires ONLY the harmless `nat_pow(_, 0) → 1` and
// `nat_pow(_, 1) → _` reductions (notation cleanup, term strictly smaller).
// - ExpandExpTactic is a separate, agent-controlled action that unfolds the
// potentially-explosive c ≥ 2 cases. Typical script is `expand_exp` then
// `arith` — expansion sets up the product form, then ring closes the
// polynomial identity.
//
// Like predecessor, nat_pow is not a default-scope const (used as a bound var in
// its recursive definition's proofs), so we parse via ParsePropTextInScope.
func TestInstallNatBundleBindingExp(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	expScope := &dsl.ParseScope{Consts: map[string]core.ConstTerm{"nat_pow": dsl.NatExpMeta.Term()}}

	// Tier 1: harmless reductions auto-fire inside ArithTactic.
	for _, g := range []string{
		"a:num ⊢ nat_pow(a, 0) = 1",        // nat_pow recursion clause 1
		"a:num ⊢ nat_pow(a, 1) = a",        // PowOne shortcut
		"n:num ⊢ nat_pow(1, n) = 1",        // OnePow: symbolic-n, special-base 1
		"a:num ⊢ nat_pow(0, 0) = 1",        // ZeroPow + Cond(0=0, 1, 0) → 1 (literal n=0)
		"n:num, 0 < n ⊢ nat_pow(0, n) = 0", // ZeroPow + Cond(n=0, 1, 0) → 0 (0<n in hyps)
		"a:num ⊢ nat_pow(0, suc(a)) = 0",   // ZeroPow + Cond(suc(a)=0, 1, 0) → 0 (suc≠0)
	} {
		t.Run("simp "+g, func(t *testing.T) {
			res := dsl.ParsePropTextInScope(g, expScope)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined a tier-1 nat_pow goal: %s", g)
			}
		})
	}

	// Tier 1: a literal exponent is READ in the monomial basis (omega
	// pow_basis.go, natPowChainUnfold through the corpus-bound nat_pow
	// clauses), so ring sees nat_pow(a, 2) and a·a as one unknown and the
	// identity decides — with the TERM untouched, which is the "no surprise
	// expansion in arith" contract (ring_nf spells a power out on request).
	t.Run("arith reads c=2 in the monomial basis", func(t *testing.T) {
		res := dsl.ParsePropTextInScope("a:num ⊢ nat_pow(a, 2) = a * a", expScope)
		if len(res.Errors) > 0 {
			t.Fatalf("parse: %s", res.Errors[0].Message)
		}
		if unscopedArithTactic(res.Prop) == nil {
			t.Fatal("ArithTactic declined nat_pow(a,2)=a*a — the pow basis must read the literal exponent")
		}
	})

	// Tier 2: agent-controlled expansion (ExpandExpTactic then ArithTactic) for
	// c ≥ 2 and polynomial identities over a complex base.
	for _, g := range []string{
		"a:num ⊢ nat_pow(a, 2) = a * a",                                                // c=2 via shortcut
		"a:num ⊢ nat_pow(a, 3) = a * a * a",                                            // c=3 via recursion
		"a:num ⊢ nat_pow(a, 4) = a * a * a * a",                                        // c=4 via recursion
		"a:num, b:num ⊢ nat_pow(a + b, 2) = nat_pow(a, 2) + 2 * a * b + nat_pow(b, 2)", // (a+b)² via ring
		"a:num, b:num ⊢ nat_pow(a * b, 2) = nat_pow(a, 2) * nat_pow(b, 2)",             // (ab)² = a²b²
	} {
		t.Run("expand+arith "+g, func(t *testing.T) {
			res := dsl.ParsePropTextInScope(g, expScope)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			expanded := tactic.ExpandExpTactic(res.Prop)
			if expanded == nil {
				t.Fatalf("ExpandExpTactic declined: %s", g)
			}
			if expanded.Size() != 1 {
				t.Fatalf("ExpandExpTactic produced %d residuals, want 1", expanded.Size())
			}
			child := expanded.ChildGoal(0)
			if unscopedArithTactic(child) == nil {
				t.Fatalf("ArithTactic declined post-expansion: %s (residual %v)", g, child.Conclusion())
			}
		})
	}
}

// TestInstallNatBundleBindingFact: the literal-factorial evaluator.
// A LITERAL `factorial(c)` folds to its numeral c! through the factorial recursion clauses
// (projected) + sucBits + NormNatMul — all real under the installed bundle, so no
// unsound integer placeholder fires. Symbolic factorial stays opaque. The `n=4 ⊢ …`
// case routes through eqHypSubst (n→4) then the literal fold.
func TestInstallNatBundleBindingFact(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	factScope := &dsl.ParseScope{Consts: map[string]core.ConstTerm{"factorial": dsl.NatFactMeta.Term()}}
	for _, g := range []string{
		"factorial(0) = 1",
		"factorial(1) = 1",
		"factorial(2) = 2",
		"factorial(3) = 6",
		"factorial(4) = 24",
		"factorial(5) = 120",
		"n:num, n = 4 ⊢ factorial(n) = 24", // eqHypSubst n→4, then literal fold
	} {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropTextInScope(g, factScope)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined a factorial goal: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingIffCompare: a CONTINGENT iff of two comparison atoms —
// neither side decidable alone, but the equivalence holds over ℤ.
// arithIffLeaf proves both directions through the forward prover and combines them
// with the engine's iff-introduction (Deduct), then folds to ⊤. No new theorem.
func TestInstallNatBundleBindingIffCompare(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	lt := func(x, y core.Term) core.Term { return ext.Apply(dsl.NatLtMeta.Term(), x, y) }
	le := func(x, y core.Term) core.Term { return ext.Apply(dsl.NatLeMeta.Term(), x, y) }
	suc := func(x core.Term) core.Term { return ext.Apply(dsl.SUCMeta.Term(), x) }
	a := core.Var("a", dsl.NumType)
	b := core.Var("b", dsl.NumType)

	cases := []struct {
		name string
		goal *prop.PropWrapper
	}{
		// (a<b) ⇔ (suc a ≤ b): forward ℚ, backward needs integrality (a<b ⟺ a+1≤b).
		{"(a<b) ⇔ (suc a ≤ b)", prop.MakeProp(core.Eq(lt(a, b), le(suc(a), b)))},
		// (a≤b) ⇔ (a < suc b): a≤b ⟺ a<b+1.
		{"(a≤b) ⇔ (a < suc b)", prop.MakeProp(core.Eq(le(a, b), lt(a, suc(b))))},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !arithCloses(tc.goal) {
				t.Fatalf("arith did not close a contingent comparison-iff: %s", tc.name)
			}
		})
	}
}

// TestInstallNatBundleBindingDivModPhase3: the modMultAdd / divDivNest simp leaves
// under the real bundle — affine-nat_mod reduction (ModMultAdd) and
// nested-nat_div flattening (DivDiv). Forces the nat_div_mod.ModMultAdd / DivDiv
// promises to real certs (no placeholder fabricator) and asserts no unsound leaf fires.
func TestInstallNatBundleBindingDivModPhase3(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		"n:num ⊢ nat_mod(2 * n + 1, n) = nat_mod(1, n)",                       // ModMultAdd, n the RIGHT factor
		"n:num ⊢ nat_mod(n * 3 + 2, n) = nat_mod(2, n)",                       // ModMultAdd, n the LEFT factor (MulSym bridge)
		"m:num ⊢ nat_div(nat_div(m, 2), 3) = nat_div(m, 6)",                   // DivDiv + numeral fold 2*3 → 6
		"m:num, a:num, b:num ⊢ nat_div(nat_div(m, a), b) = nat_div(m, a * b)", // DivDiv, symbolic
	} {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if !arithCloses(res.Prop) {
				t.Fatalf("arith did not close a phase-3 nat_div/nat_mod goal: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingDivModDist: nat_div/nat_mod distribution under the real
// bundle. divMultAdd is the conditional affine-nat_div simp (the nat_div
// companion to ModMultAdd; n≠0 discharged numerically for the literal divisor);
// divMultAddFact is its symbolic-divisor enrichment companion (n≠0 from a hyp);
// modAddMod is ModAddMod wired in the combine (term-shrinking) direction. Each
// goal closes via the leaf/fact; no unsound integer placeholder fires.
func TestInstallNatBundleBindingDivModDist(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		"a:num, b:num ⊢ nat_div(2 * a + b, 2) = a + nat_div(b, 2)",                            // DivMultAdd, multiple first summand, divisor LEFT factor
		"a:num, b:num ⊢ nat_div(a * 2 + b, 2) = a + nat_div(b, 2)",                            // DivMultAdd, divisor RIGHT factor (distinct clause)
		"a:num, b:num ⊢ nat_div(b + 2 * a, 2) = nat_div(b, 2) + a",                            // DivMultAdd, multiple SECOND summand
		"a:num, b:num, n:num, 0 < n ⊢ nat_div(n * a + b, n) = a + nat_div(b, n)",              // DivMultAdd, SYMBOLIC divisor via enrichment (n≠0 from hyp)
		"a:num, b:num, n:num ⊢ nat_mod(nat_mod(a, n) + nat_mod(b, n), n) = nat_mod(a + b, n)", // ModAddMod, combine direction
	} {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if !arithCloses(res.Prop) {
				t.Fatalf("arith did not close a nat_div/nat_mod distribution goal: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingPre: predecessor under the real bundle. The
// single bridge `predecessor n → n - 1` (derived from the Sub recursion) routes predecessor into
// the monus layer: predecessor(suc n) / predecessor(n+1) collapse via subCancel, predecessor 0 via
// subTrunc, and a symbolic predecessor m in a comparison is decided by the monus split.
func TestInstallNatBundleBindingPre(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	// predecessor is not a default-scope const (it collides with the recursion-def bound
	// var); supply it explicitly for parsing the test goals.
	preScope := &dsl.ParseScope{Consts: map[string]core.ConstTerm{"predecessor": dsl.NatPreMeta.Term()}}
	for _, g := range []string{
		"a:num ⊢ predecessor(suc(a)) = a", // suc case → subCancel
		"a:num ⊢ predecessor(a + 1) = a",  // +1 case → subCancel
		"a:num ⊢ predecessor(0) = 0",      // zero case → subTrunc
		"a:num ⊢ predecessor(a) <= a",     // symbolic → monus split on a-1
	} {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropTextInScope(g, preScope)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined a predecessor goal: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingGtGe: `≥` / `>` goals under the real installed bundle.
// These route through gtBridge/geBridge, which instantiate the `>`/`≥` defs (defNorm)
// (`∀a b. (a<b)⇔(b>a)` / `∀a b. (a≤b)⇔(b≥a)`) — stated with the strict/large
// relation on the swapped second binder. A regression in the bridge's
// instantiation order (it must be [y,x], not [x,y]) degrades the eq leaf and,
// with no placeholder fabricator, PANICS. No earlier binding test used `≥`/`>`, so
// this guards the real-def path end-to-end.
func TestInstallNatBundleBindingGtGe(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		"a:num, b:num, a >= b ⊢ a >= b", // geBridge (hyp + goal)
		"a:num ⊢ a + 1 > a",             // gtBridge, contingent (always true)
		"a:num, b:num, a > b ⊢ a >= b",  // `>` hyp ⇒ `≥` goal (both bridges)
	} {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined a valid ≥/> goal: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingMaxMin: nat_max/nat_min under the real bundle —
// the case-split engine's second client. nat_max a b = COND(a≤b,b,a) is opaque to
// linarith, so these are not ℚ-valid (LinarithTactic declines); the excluded middle
// split on the guard `a≤b` (pins from the def + COND collapse) closes them. With
// no placeholder fabricator, the nat_max/nat_min defs + the COND machinery must be real,
// and the soundness counter must stay unchanged. Idempotence (nat_max a a = a) goes through the simp
// CondId leaf, not the split.
func TestInstallNatBundleBindingMaxMin(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})

	// Idempotence via the simp leaf.
	for _, g := range []string{
		"a:num ⊢ nat_max(a, a) = a",
		"a:num ⊢ nat_min(a, a) = a",
	} {
		t.Run("simp "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined nat_max/nat_min idempotence: %s", g)
			}
		})
	}

	// Decision via the excluded middle case-split.
	for _, g := range []string{
		"a:num, b:num ⊢ a <= nat_max(a, b)",             // nat_max ≥ left operand
		"a:num, b:num ⊢ b <= nat_max(a, b)",             // nat_max ≥ right operand (needs the ¬-guard arm)
		"a:num, b:num ⊢ nat_max(a, b) >= a",             // same, via the geBridge (split ∘ ≥)
		"a:num, b:num ⊢ nat_min(a, b) <= a",             // nat_min ≤ left operand
		"a:num, b:num ⊢ nat_min(a, b) <= b",             // nat_min ≤ right operand
		"a:num, b:num ⊢ nat_min(a, b) <= nat_max(a, b)", // two splittable atoms (nested splits)
	} {
		t.Run("split "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.LinarithTactic(res.Prop) != nil {
				t.Fatalf("LinarithTactic unexpectedly closed (nat_max/nat_min is opaque): %s", g)
			}
			if unscopedArithTactic(res.Prop) == nil {
				t.Fatalf("ArithTactic declined — the nat_max/nat_min split should close it: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingDisjHyp: the disjunctive-hypothesis split.
// A hyp `p ∨ q` is dropped by the linear core (parseHypConstraint only ingests
// `< ≤ = > ≥`), so LinarithTactic declines; the case-split engine eliminates the
// disjunction (disjProof = Assume(h), no lemma) and proves the goal per branch.
// No lemma supply, so no unsound-leaf concern — but we assert it anyway.
func TestInstallNatBundleBindingDisjHyp(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		`a:num, (a = 1) \/ (a = 2) ⊢ 1 <= a`,              // each disjunct closes by linarith
		`a:num, b:num, (a < b) \/ (a = b) ⊢ a <= b`,       // <-branch + =-branch
		`a:num, (a = 0) \/ (a = 1) ⊢ a <= 1`,              // both literal-equality branches
		`a:num, b:num, (a <= b) \/ (a + 1 <= b) ⊢ a <= b`, // atom goal, both branches ⇒ a≤b
	} {
		t.Run("disj "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.LinarithTactic(res.Prop) != nil {
				t.Fatalf("LinarithTactic unexpectedly closed (disjunction hyp is dropped): %s", g)
			}
			if !arithCloses(res.Prop) {
				t.Fatalf("arith did not close — the disjunction-hyp split should close it: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingNeqHyp: the `≠`-hypothesis trichotomy split.
// A hyp `¬(a=b)` is dropped by the linear core; the split derives `a<b ∨ b<a`
// from LessThanTrichotomy (the `a=b` disjunct killed under the hyp) and proves the goal per
// branch. Forces the LessThanTrichotomy promise to a real kernel cert (no placeholder
// fabricator), and asserts no unsound integer leaf fires (the `0<a ⊢ 1≤a` branch
// uses the REAL strict→non-strict intCut, not a placeholder).
func TestInstallNatBundleBindingNeqHyp(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		"a:num, ~(a = 0) ⊢ 1 <= a",               // a≠0 over num ⇒ 0<a ⇒ 1≤a (the < branch is vacuous)
		"a:num, ~(a = 0) ⊢ 0 < a",                // same, strict goal
		"a:num, b:num, a <= b, ~(a = b) ⊢ a < b", // a≤b ∧ a≠b ⇒ a<b (b<a branch contradicts a≤b)
	} {
		t.Run("neq "+g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.LinarithTactic(res.Prop) != nil {
				t.Fatalf("LinarithTactic unexpectedly closed (≠ hyp is dropped): %s", g)
			}
			if !arithCloses(res.Prop) {
				t.Fatalf("arith did not close — the ≠-hyp trichotomy split should close it: %s", g)
			}
		})
	}
}

// TestInstallNatBundleBindingCondSplit: the generic raw-COND split. A
// num-typed `COND(guard, x, y)` whose guard the linear core can't decide is split
// on excluded middle(guard), each arm pinned by reflexivity (no nat_max/nat_min def). The
// goals are built programmatically — the text DSL has no clean COND surface. This
// is the same machinery nat_max/nat_min use (condSplit), exercised on a bare conditional.
func TestInstallNatBundleBindingCondSplit(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	a := core.Var("a", dsl.NumType)
	b := core.Var("b", dsl.NumType)
	le := func(x, y core.Term) core.Term { return ext.Apply(dsl.NatLeMeta.Term(), x, y) }
	// a ≤ COND(a≤b, b, a): then-arm a≤b ✓; else-arm (b<a) gives a≤a ✓. (= a≤nat_max a b.)
	maxLike := prop.MakeProp(le(a, ext.Cond(le(a, b), b, a)))
	// COND(a≤b, a, b) ≤ a: then-arm a≤a ✓; else-arm b≤a... wait nat_min. then a≤a, else b. (= nat_min a b ≤ a.)
	minLike := prop.MakeProp(le(ext.Cond(le(a, b), a, b), a))
	for _, tc := range []struct {
		name string
		goal *prop.PropWrapper
	}{
		{"a <= COND(a<=b, b, a)", maxLike},
		{"COND(a<=b, a, b) <= a", minLike},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if tactic.LinarithTactic(tc.goal) != nil {
				t.Fatalf("LinarithTactic unexpectedly closed (COND is opaque): %s", tc.name)
			}
			if !arithCloses(tc.goal) {
				t.Fatalf("arith did not close — the COND split should close it: %s", tc.name)
			}
		})
	}
}

// TestInstallNatBundleBindingParity: the nat_even/nat_odd → nat_mod-2 bridge.
// nat_even/nat_odd are not in the default DSL scope (recursive-def consts), so the goals
// are built programmatically. The bridge rewrites a parity atom to its nat_mod-2 form
// (EvenIffModTwoZero direct; nat_odd via OddIffNotEven ∘ EvenIffModTwoZero), after which the literal nat_mod
// evaluator / nat_mod-equality hyp closes it. Forces EvenIffModTwoZero / OddIffNotEven / DivModUniq
// to real certs (no placeholder fabricator) and asserts no unsound integer leaf fires.
func TestInstallNatBundleBindingParity(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	even := func(n core.Term) core.Term { return ext.Apply(dsl.NatEvenMeta.Term(), n) }
	odd := func(n core.Term) core.Term { return ext.Apply(dsl.NatOddMeta.Term(), n) }
	not := func(p core.Term) core.Term { return ext.Apply(prop.NOT, p) }
	modT := func(a, b core.Term) core.Term { return ext.Apply(dsl.NatModMeta.Term(), a, b) }
	mul := func(a, b core.Term) core.Term { return ext.Apply(dsl.NatStarMeta.Term(), a, b) }
	add := func(a, b core.Term) core.Term { return ext.Apply(dsl.NatPlusMeta.Term(), a, b) }
	n := core.Var("n", dsl.NumType)
	num := omega.Numeral

	cases := []struct {
		name string
		goal *prop.PropWrapper
	}{
		{"nat_even(4)", prop.MakeProp(even(num(4)))},                                                  // 0 = nat_mod(4, 2) → 0=0
		{"nat_odd(7)", prop.MakeProp(odd(num(7)))},                                                    // ¬(0 = nat_mod(7, 2)) → ¬(0=1)
		{"¬nat_even(3)", prop.MakeProp(not(even(num(3))))},                                            // ¬(0 = nat_mod(3, 2)) → ¬⊥? no: 3 odd → ⊤
		{"¬nat_odd(4)", prop.MakeProp(not(odd(num(4))))},                                              // ¬¬(0 = nat_mod(4, 2)) → ⊤
		{"nat_even(n) ⊢ 0 = nat_mod(n, 2)", prop.MakeProp(core.Eq(num(0), modT(n, num(2))), even(n))}, // nat_even-hyp enrichment
		// Nonlinear parity (EvenMul / EvenAdd structural decomposition).
		{"nat_even(n·n) ⇔ nat_even n", prop.MakeProp(core.Eq(even(mul(n, n)), even(n)))}, // (nat_even n ∨ nat_even n)⇔nat_even n → idempotence
		{"nat_even(2·n)", prop.MakeProp(even(mul(num(2), n)))},                           // nat_even 2 ∨ nat_even n → ⊤∨_
		{"nat_even(n·(n+1))", prop.MakeProp(even(mul(n, add(n, num(1)))))},               // nat_even n ∨ ¬nat_even n → excluded middle
		{"nat_odd(2·n+1)", prop.MakeProp(odd(add(mul(num(2), n), num(1))))},              // ¬(nat_even(2n) ⇔ nat_even 1) → ⊤
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if !arithCloses(tc.goal) {
				t.Fatalf("arith did not close a parity goal: %s", tc.name)
			}
		})
	}
}

// TestInstallNatBundleBindingEqSubst: equality-hypothesis substitution into opaque
// atoms. A `v = literal` hyp is substituted into the goal so an
// opaque atom on v (nat_mod/nat_div/nat_pow/nat_even) becomes literal and the existing literal
// simps evaluate it — a path the pure linear core (which only sees v=literal as
// two inequalities) cannot take. LinarithTactic must decline; ArithTactic closes.
func TestInstallNatBundleBindingEqSubst(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	// DSL-expressible cases: nat_mod / nat_div (in default scope).
	for _, g := range []string{
		"n:num, n = 2 ⊢ nat_mod(7, n) = 1", // subst n→2 ⇒ nat_mod(7,2)=1
		"m:num, m = 6 ⊢ nat_mod(m, 4) = 2", // subst m→6 ⇒ nat_mod(6,4)=2
		"n:num, n = 6 ⊢ nat_div(n, 2) = 3", // subst n→6 ⇒ nat_div(6,2)=3
		"n:num, 2 = n ⊢ nat_mod(7, n) = 1", // flipped equation orientation
	} {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if tactic.LinarithTactic(res.Prop) != nil {
				t.Fatalf("LinarithTactic unexpectedly closed (opaque atom on v): %s", g)
			}
			if !arithCloses(res.Prop) {
				t.Fatalf("arith did not close — eq-hyp substitution should close it: %s", g)
			}
		})
	}

	// nat_even/nat_pow are not default DSL-scope consts (recursive-def, like predecessor — the
	// text parser would treat them as free variables), so build these goals with
	// the real consts. This exercises substitution into a parity / nat_pow opaque atom.
	a := core.Var("a", dsl.NumType)
	n := core.Var("n", dsl.NumType)
	even := func(x core.Term) core.Term { return ext.Apply(dsl.NatEvenMeta.Term(), x) }
	expT := func(m, e core.Term) core.Term { return ext.Apply(dsl.NatExpMeta.Term(), m, e) }
	num := omega.Numeral
	for _, tc := range []struct {
		name string
		goal *prop.PropWrapper
	}{
		{"k = 4 ⊢ nat_even(k)", prop.MakeProp(even(n), core.Eq(n, num(4)))},                           // subst n→4 ⇒ nat_even(4)
		{"n = 0 ⊢ nat_pow(a, n) = 1", prop.MakeProp(core.Eq(expT(a, n), num(1)), core.Eq(n, num(0)))}, // subst n→0 ⇒ nat_pow(a,0)=1
		{"n = 1 ⊢ nat_pow(a, n) = a", prop.MakeProp(core.Eq(expT(a, n), a), core.Eq(n, num(1)))},      // subst n→1 ⇒ nat_pow(a,1)=a
	} {
		t.Run(tc.name, func(t *testing.T) {
			if !arithCloses(tc.goal) {
				t.Fatalf("arith did not close — eq-hyp substitution should close it: %s", tc.name)
			}
		})
	}
}

// TestInstallNatBundleBindingDist: the dist→monus bridge. num
// distance `nat_dist(,(m,n)) = (m-n)+(n-m)` (= |m-n|, the nat→real lift foundation)
// is rewritten via the `dist` theorem (nat_monus.Dist) and routed into the truncated-
// subtraction layer: reducible cases collapse via subCancel/subTrunc, and a
// symbolic dist in a comparison is decided by the monus case split on its two
// monus atoms. Forces nat_monus.Dist's promise (no placeholder fabricator) and asserts no unsound integer leaf.
func TestInstallNatBundleBindingDist(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		"n:num ⊢ nat_dist(,(n, n)) = 0",                        // subCancel (n-n=0, both arms)
		"n:num ⊢ nat_dist(,(n, 0)) = n",                        // subCancel + subTrunc
		"n:num ⊢ nat_dist(,(0, n)) = n",                        // subTrunc + subCancel
		"m:num, n:num ⊢ nat_dist(,(m, n)) = nat_dist(,(n, m))", // symmetry (bridge both ∘ ring)
		"m:num, n:num ⊢ nat_dist(,(m, n)) <= m + n",            // triangle-ish (monus split)
		"m:num, n:num, m <= n ⊢ nat_dist(,(m, n)) = n - m",     // conditional (monus split + hyp)
	} {
		t.Run(g, func(t *testing.T) {
			res := dsl.ParsePropText(g)
			if len(res.Errors) > 0 {
				t.Fatalf("parse: %s", res.Errors[0].Message)
			}
			if !arithCloses(res.Prop) {
				t.Fatalf("arith did not close — the dist→monus bridge should close it: %s", g)
			}
		})
	}
}

// assertArithCloses runs a text goal under the caller-installed bundle (no
// placeholder fabricator in this test binary) and asserts the unified arith move
// FULLY closes it without firing any unsound integer placeholder. Shared by the
// split-client / enumeration / enrichment tests.
func assertArithCloses(t *testing.T, g string) {
	t.Helper()
	res := dsl.ParsePropText(g)
	if len(res.Errors) > 0 {
		t.Fatalf("parse %q: %s", g, res.Errors[0].Message)
	}
	if !arithCloses(res.Prop) {
		t.Fatalf("ArithTactic did not close: %s", g)
	}
}

// TestInstallNatBundleBindingDisjGoal: the goal-side disjunction closer (omega/nat.go)
// under the real bundle — totality/trichotomy goals (no universally-true disjunct)

func TestInstallNatBundleBindingDisjGoal(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		`a:num, b:num ⊢ a <= b \/ b <= a`,       // LessEqTotal totality
		`a:num, b:num ⊢ a < b \/ b <= a`,        // pivot on a<b
		`a:num, b:num ⊢ a <= b \/ b < a`,        // pivot on a≤b
		`a:num, b:num, a < b ⊢ a <= b \/ b < a`, // direct: a≤b from a<b
	} {
		t.Run(g, func(t *testing.T) { assertArithCloses(t, g) })
	}
}

// TestInstallNatBundleBindingImplHyp: the implication-hypothesis split (omega nat_sub.go
// hypSplittable `p ⇒ q` branch) under the real bundle — `¬p ∨ q` case split.
func TestInstallNatBundleBindingImplHyp(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	// {a<b ⇒ b<a} ⊢ b≤a : ¬(a<b) gives b≤a, else b<a ⟹ b≤a. Needs the split.
	assertArithCloses(t, `a:num, b:num, a < b => b < a ⊢ b <= a`)
}

// TestInstallNatBundleBindingEnum: the bounded-variable enumeration split (omega/nat_exp.go)
// under the real bundle — a literal-bounded variable occurring nonlinearly is
// decided by enumerating its values (LessEqSplit peel + LessThanSucIffLessEq bridge + per-value
// literal evaluation).
func TestInstallNatBundleBindingEnum(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		"n:num, n <= 2 ⊢ n * n <= 4",         // enumerate n ∈ {0,1,2}
		"n:num, n <= 2 ⊢ n * n <= 2 * n + 1", // 0≤1, 1≤3, 4≤5
		"n:num, n < 3 ⊢ n * n <= 4",          // `<` bound
	} {
		t.Run(g, func(t *testing.T) { assertArithCloses(t, g) })
	}
}

// TestInstallNatBundleBindingModEnrich: the nat_mod enrichment facts for a
// multiple and a nested residue under the real bundle — multiple-is-zero
// (derived from ModEqZero, no lemma of its own) and idempotence (via
// ModModRefl). Both need a nonlinear `q·n = 0` step the Division/ModLessThan
// injection can't see.
func TestInstallNatBundleBindingModEnrich(t *testing.T) {
	InstallNatBundle()
	t.Cleanup(func() {
		omega.SetNatLemmaBundle(nil)
	})
	for _, g := range []string{
		"k:num, n:num ⊢ nat_mod(k * n, n) = 0",                     // multiple, divisor = right factor
		"k:num, n:num ⊢ nat_mod(n * k, n) = 0",                     // multiple, divisor = left factor (MulSym)
		"m:num, n:num ⊢ nat_mod(nat_mod(m, n), n) = nat_mod(m, n)", // idempotence (ModModRefl)
	} {
		t.Run(g, func(t *testing.T) { assertArithCloses(t, g) })
	}
}
