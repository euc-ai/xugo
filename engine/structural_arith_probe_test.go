package engine

import (
	"slices"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// wideRealState is the state TestInspect_ArithProbeOnWideRealContext times.
const wideRealState = "f_0:(real → real), x_0:real, g_0:(real → real), l_0:real, m_0:real, ε_0:real, c_0:real, δ_0:real, " +
	"∀a:real.∀b:real.∀l:real.∀m:real.∀η:real.(((((&0 < η) ∧ (η ≤ &1)) ∧ (real_abs(a - l) < η)) ∧ (real_abs(b - m) < η)) ⇒ (real_abs((a * b) - (l * m)) < (η * ((real_abs(l) + real_abs(m)) + &1)))), " +
	"∀ε:real.((&0 < ε) ⇒ (∃δ:real.((&0 < δ) ∧ (∀x:real.(((&0 < real_abs(x - c₀)) ∧ (real_abs(x - c₀) < δ)) ⇒ (real_abs(f₀(x) - l₀) < ε)))))), " +
	"∀ε:real.((&0 < ε) ⇒ (∃δ:real.((&0 < δ) ∧ (∀x:real.(((&0 < real_abs(x - c₀)) ∧ (real_abs(x - c₀) < δ)) ⇒ (real_abs(g₀(x) - m₀) < ε)))))), " +
	"∀ε:real.((&0 < ε) ⇒ (∃δ:real.((&0 < δ) ∧ (∀x:real.(((&0 < real_abs(x - c₀)) ∧ (real_abs(x - c₀) < δ)) ⇒ ((real_abs(f₀(x) - l₀) < ε) ∧ (real_abs(g₀(x) - m₀) < ε))))))), " +
	"∀x:real.(((&0 < real_abs(x - c₀)) ∧ (real_abs(x - c₀) < δ₀)) ⇒ ((real_abs(f₀(x) - l₀) < (ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1))) ∧ (real_abs(g₀(x) - m₀) < (ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1))))), " +
	"(ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1)) ≤ &1, " +
	"&0 < ε₀, " +
	"&0 < (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1), " +
	"&0 < (ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1)), " +
	"((ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1)) * ((real_abs(l₀) + real_abs(m₀)) + &1)) < ε₀, " +
	"(real_abs(f₀(x₀) - l₀) < (ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1))) ∧ (real_abs(g₀(x₀) - m₀) < (ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1))), " +
	"(&0 < δ₀) ∧ (∀x:real.(((&0 < real_abs(x - c₀)) ∧ (real_abs(x - c₀) < δ₀)) ⇒ ((real_abs(f₀(x) - l₀) < (ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1))) ∧ (real_abs(g₀(x) - m₀) < (ε₀ / (((ε₀ + real_abs(l₀)) + real_abs(m₀)) + &1)))))), " +
	"(&0 < real_abs(x₀ - c₀)) ∧ (real_abs(x₀ - c₀) < δ₀) " +
	"⊢ real_abs((f₀(x₀) * g₀(x₀)) - (l₀ * m₀)) < ε₀"

// TestInspect_ArithProbeOnWideRealContext bounds `inspect` on a wide real
// ε-δ context: the state of real/real_function_limits' LimitAtMul once its
// ∀-estimate is cited — three unfolded limit definitions, a ∀x ball
// statement, four η facts, three ∧-hypotheses and a five-binder ∀ estimate,
// 13 hypotheses in all. `inspect` verifies the parameterless `arith` move
// by running the full simplify-or-decide composite on a clone
// (collectStructuralMoves → proof.ApplyArithSimplify), so the clone-apply
// is the whole cost of `inspect` on this shape: every other probe is a
// small fraction of it.
//
// The work is the real decider's per-atom decision under all other
// hypotheses (tactic.arithRewriteTactic decides the conclusion, then each
// hypothesis under the others), each atom once and once negated, and a
// contingent atom's failure path is the real_abs case-split fallback
// (omega.realProveSplit), one linarith run per split level. Three
// mechanisms keep that from taking minutes: the extraction memo, without
// which every linarith run re-extracts every hypothesis's constraint with
// its kernel move-across proof (Domain.hypConstraints); the syntactic pin
// fold, without which every split level derives its two pins through a full
// deep rewrite (realCondPin); and the binder-free candidate walk, without
// which the `|·|` terms under the unfolded definitions' ∀x — pins no
// constraint row can meet — are the first eight levels of every atom's
// path. The bound below is a stall guard, not a benchmark.
//
// The field layer makes the state heavy a second way. The quotient basis
// reads `ε₀ / (…)` as a product, so every decision here meets the unit
// facts and the sign pieces, and a failing decision walks all of them. The
// decisions repeat — nine runs of the linear prover in ten ask a question
// already asked, seven decisions in eight likewise, and the sign rows
// rebuild one ring equation per monomial per run and fold the same
// factors' signs for the same monomial in nine asks of ten — so the
// answers are memoized for the step and released at its end
// (omega.ReleaseStepMemos).
//
// A decision that declines here descends the `|·|` split to its first
// open branch and asks the split's leaf there, the branch read at its pins
// (omega caseSplit): one model of the products pass beside the one the
// chain built at the root. That is the price of an operator's branch
// reaching a product: on this state, one more run of the model for every
// decision that declines. A pass that re-runs a failing
// decision over an enriched context multiplies this state's cost by the
// pass: the clearing of a hypothesis's divisor does, twice over and more,
// and is not in (the engine manual, "what still needs a premise"). The
// bound is thirty seconds: the stall it guards against was minutes, and a
// continuous-integration runner several times slower than the machine a
// change is written on must still pass under it.
//
// The parse MUST resolve real_abs to the chapter constant (a bare
// dsl.ParsePropText reads it as a free function variable, and on that goal
// the same probe is over at once — the decider never sees an |·|), so the test
// asserts the constant before timing anything. What the move buys on this
// state is pinned too — the decider's success set on the shape is the
// observation the three mechanisms must not move: the bound hypothesis
// `ε₀ / (ε₀ + |l₀| + |m₀| + &1) ≤ &1` is redundant under the sign facts and
// drops, and TrivialSimplify splits the three ∧-hypotheses; the conclusion
// stays.
func TestInspect_ArithProbeOnWideRealContext(t *testing.T) {
	installTestNatBundle()
	installTestRealBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
		setTestRealBundle(nil)
	})

	// The LimitAtMul state after `cite-node s0_cprop_1124948bd9f`, as the
	// engine printed it (statement_typed); hypothesis order is the goal's.
	const state = wideRealState

	// The chapter constants resolve through the process const-meta
	// manager, exactly as the session's claim door parses them
	// (goalScopedPropText: the corpus syntax table plus the registry
	// const resolver).
	res := dsl.ParsePropTextInScope(state, &dsl.ParseScope{
		Syntax:        constSyntax(),
		ConstResolver: registryConstResolver,
	})
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	goal := res.Prop
	require.Equal(t, 13, goal.NumHyps())
	consts := make(map[core.TermKey]ext.ConstTerm)
	ext.CollectConstTerms(goal.Conclusion(), consts)
	for _, h := range goal.Hyps() {
		ext.CollectConstTerms(h, consts)
	}
	var absConst ext.ConstTerm
	for _, c := range consts {
		if c.Name() == "real_abs" {
			absConst = c
		}
	}
	require.False(t, absConst.IsZero(), "real_abs must parse as the chapter constant, not a free variable")

	start := time.Now()
	moves := collectStructuralMoves(goal)
	elapsed := time.Since(start)
	t.Logf("collectStructuralMoves: %v", elapsed)
	var kinds []string
	for _, m := range moves {
		kinds = append(kinds, m.Tactic)
	}
	require.Contains(t, kinds, "arith", "the probe must still report the move it verifies")
	require.Less(t, elapsed, 30*time.Second,
		"inspect's arith clone-apply on a 13-hypothesis real ε-δ context took %v (the stall this test pins was minutes; see the test comment)", elapsed)

	// What the verified move does to the state.
	node := proof.CreateGoalStack(goal)
	require.True(t, proof.ApplyArithSimplify(t.Context(), node), "arith must make progress on the state")
	leaves := node.UnsolvedLeaves()
	require.Len(t, leaves, 1)
	child := leaves[0].Goal
	require.True(t, child.Conclusion().AlphaEquals(goal.Conclusion()), "the conclusion is not decided: %v", child.Conclusion())
	hasHyp := func(h core.Term) bool { return slices.ContainsFunc(child.Hyps(), h.AlphaEquals) }
	for _, h := range goal.Hyps() {
		if !hasHyp(h) {
			t.Logf("dropped: %s", ext.PrintTerm(h))
		}
	}
	for _, h := range child.Hyps() {
		if !slices.ContainsFunc(goal.Hyps(), h.AlphaEquals) {
			t.Logf("added: %s", ext.PrintTerm(h))
		}
	}
	// The pass fires ONE hypothesis rewrite (arithRewriteTactic returns at
	// its first firing): the drop of `ε₀/(ε₀+|l₀|+|m₀|+&1) ≤ &1` (hyp 5).
	// The sign fact `&0 < ε₀/(…)` (hyp 8) stays.
	require.False(t, hasHyp(goal.Hyps()[5]), "the redundant bound hypothesis must drop")
	require.True(t, hasHyp(goal.Hyps()[8]), "one firing per pass: the sign fact stays")
	for _, i := range []int{10, 11, 12} { // the three ∧-hypotheses
		l, r, ok := prop.MatchesAND(goal.Hyps()[i])
		require.True(t, ok)
		require.False(t, hasHyp(goal.Hyps()[i]), "hyp %d must be split", i)
		require.True(t, hasHyp(l) && hasHyp(r), "hyp %d's conjuncts must both survive", i)
	}
	// 13 − the drop − 3 conjunctions + their 6 conjuncts, one of which (the
	// ∀x ball statement inside hyp 11) is already hyp 4.
	require.Equal(t, 14, child.NumHyps())
}

// wideComplexState is the state TestInspect_ArithProbeOnWideRealContext
// times, one carrier over: the same thirteen hypotheses about functions
// ℂ → ℂ, every distance a complex modulus. No modulus in it has a
// compound argument a law reads; what the arith step reads of them is
// their sign.
const wideComplexState = "f_0:(complex → complex), x_0:complex, g_0:(complex → complex), l_0:complex, m_0:complex, ε_0:real, c_0:complex, δ_0:real, k_0:complex, " +
	"∀a:complex.∀b:complex.∀l:complex.∀m:complex.∀η:real.(((((&0 < η) ∧ (η ≤ &1)) ∧ (complex_abs(a - l) < η)) ∧ (complex_abs(b - m) < η)) ⇒ (complex_abs((a * b) - (l * m)) < (η * ((complex_abs(l) + complex_abs(m)) + &1)))), " +
	"∀ε:real.((&0 < ε) ⇒ (∃δ:real.((&0 < δ) ∧ (∀x:complex.(((&0 < complex_abs(x - c₀)) ∧ (complex_abs(x - c₀) < δ)) ⇒ (complex_abs(f₀(x) - l₀) < ε)))))), " +
	"∀ε:real.((&0 < ε) ⇒ (∃δ:real.((&0 < δ) ∧ (∀x:complex.(((&0 < complex_abs(x - c₀)) ∧ (complex_abs(x - c₀) < δ)) ⇒ (complex_abs(g₀(x) - m₀) < ε)))))), " +
	"∀ε:real.((&0 < ε) ⇒ (∃δ:real.((&0 < δ) ∧ (∀x:complex.(((&0 < complex_abs(x - c₀)) ∧ (complex_abs(x - c₀) < δ)) ⇒ ((complex_abs(f₀(x) - l₀) < ε) ∧ (complex_abs(g₀(x) - m₀) < ε))))))), " +
	"∀x:complex.(((&0 < complex_abs(x - c₀)) ∧ (complex_abs(x - c₀) < δ₀)) ⇒ ((complex_abs(f₀(x) - l₀) < (ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1))) ∧ (complex_abs(g₀(x) - m₀) < (ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1))))), " +
	"(ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1)) ≤ &1, " +
	"&0 < ε₀, " +
	"&0 < (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1), " +
	"&0 < (ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1)), " +
	"((ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1)) * ((complex_abs(l₀) + complex_abs(m₀)) + &1)) < ε₀, " +
	"(complex_abs(f₀(x₀) - l₀) < (ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1))) ∧ (complex_abs(g₀(x₀) - m₀) < (ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1))), " +
	"(&0 < δ₀) ∧ (∀x:complex.(((&0 < complex_abs(x - c₀)) ∧ (complex_abs(x - c₀) < δ₀)) ⇒ ((complex_abs(f₀(x) - l₀) < (ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1))) ∧ (complex_abs(g₀(x) - m₀) < (ε₀ / (((ε₀ + complex_abs(l₀)) + complex_abs(m₀)) + &1)))))), " +
	"(&0 < complex_abs(x₀ - c₀)) ∧ (complex_abs(x₀ - c₀) < δ₀) " +
	"⊢ complex_abs((f₀(x₀) * g₀(x₀)) - (l₀ * m₀)) < ε₀"

// scaledComplexState is wideComplexState with every deviation of f₀ and
// g₀ from its limit, and the goal's, multiplied by k₀ under the modulus:
// moduli of a product in the goal, in the hypotheses and under their
// binders, each of which the modulus laws rewrite to a product of
// moduli.
func scaledComplexState() string {
	s := wideComplexState
	for _, deviation := range []string{
		"f₀(x) - l₀", "g₀(x) - m₀", "f₀(x₀) - l₀", "g₀(x₀) - m₀", "(f₀(x₀) * g₀(x₀)) - (l₀ * m₀)",
	} {
		s = strings.ReplaceAll(s, "complex_abs("+deviation+")", "complex_abs(k₀ * ("+deviation+"))")
	}
	return s
}

// TestInspect_ArithProbeOnWideComplexContext bounds `inspect` with ℂ's
// modulus installed (omega modulus.go), on three wide ε-δ states: one
// where the arith step reads the sign of every modulus in sight
// (wideComplexState), one where it also rewrites the moduli of products
// (scaledComplexState), and the ℝ twin's own state, which spells no
// complex modulus and must pay nothing for the reading. A complex
// modulus is never case-split, so the two ℂ states walk no `|·|` split;
// what the reading adds to a decision is one sign fact per modulus
// beside its hypotheses, and on the scaled state the products the
// rewrite leaves.
//
// The bounds are stall guards, as the ℝ twin's is and as wide, the ℝ
// state being one of the three; the numbers to read are the logged ones. Measured against the same build with the reading
// withheld: a little less time on the plain state, a tenth of it on the
// scaled one, whose first firing is the conclusion's rewrite, and the same
// on the ℝ state.
//
// What the move buys on the plain state is pinned: with `&0 ≤ |l₀|` and
// `&0 ≤ |m₀|` in hand the bound hypothesis `ε₀ / (ε₀ + |l₀| + |m₀| + &1)
// ≤ &1` is redundant and drops, as it does over ℝ; without the sign of a
// modulus it is not.
func TestInspect_ArithProbeOnWideComplexContext(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	byArithEngine(t)
	for _, row := range []struct {
		name, state string
	}{
		{"the sign of every modulus", wideComplexState},
		{"moduli of products", scaledComplexState()},
		{"no modulus in sight", wideRealState},
	} {
		t.Run(row.name, func(t *testing.T) {
			res := dsl.ParsePropTextInScope(row.state, &dsl.ParseScope{
				Syntax:        constSyntax(),
				ConstResolver: registryConstResolver,
			})
			require.Empty(t, res.Errors, "parse: %v", res.Errors)
			goal := res.Prop
			require.Equal(t, 13, goal.NumHyps())
			consts := make(map[core.TermKey]ext.ConstTerm)
			ext.CollectConstTerms(goal.Conclusion(), consts)
			found := row.state == wideRealState
			for _, c := range consts {
				found = found || c.Name() == "complex_abs"
			}
			require.True(t, found, "complex_abs must parse as the chapter constant, not a free variable")

			start := time.Now()
			moves := collectStructuralMoves(goal)
			elapsed := time.Since(start)
			t.Logf("collectStructuralMoves: %v", elapsed)
			var kinds []string
			for _, m := range moves {
				kinds = append(kinds, m.Tactic)
			}
			require.Contains(t, kinds, "arith", "the probe must report the move it verifies")
			require.Less(t, elapsed, 30*time.Second,
				"inspect's arith clone-apply on a 13-hypothesis ε-δ context over ℂ took %v", elapsed)

			node := proof.CreateGoalStack(goal)
			require.True(t, proof.ApplyArithSimplify(t.Context(), node), "arith must make progress on the state")
			leaves := node.UnsolvedLeaves()
			require.Len(t, leaves, 1)
			child := leaves[0].Goal
			hasHyp := func(h core.Term) bool { return slices.ContainsFunc(child.Hyps(), h.AlphaEquals) }
			for _, h := range goal.Hyps() {
				if !hasHyp(h) {
					t.Logf("dropped or rewritten: %s", ext.PrintTerm(h))
				}
			}
			if row.state == wideComplexState {
				require.False(t, hasHyp(goal.Hyps()[5]), "the bound hypothesis, redundant under the moduli's signs, must drop")
			}
		})
	}
}

// nestedSetBuilderState is the state
// TestInspect_ArithProbeOnASetBuilderComparedWithItself probes: three
// definitions a session's `let` left of hedge_criterion's spin programs,
// the second's set-builder inside the first's and inside the third's
// guard.
const nestedSetBuilderState = "H:set(A), T:set(A), F:set(A), G:set(A), ρ:(A → A), κ:(A → set(A) → real), " +
	"into:(A → set(A)), W:(A → set(A) → real), U:set(A), " +
	"U = {u:A | ((u ∈ F) ∧ (u ∉ G)) ∧ (into(u) ≠ ∅)}, " +
	"into = (λv:A. {w:A | ((w ∈ H) ∧ (w ∉ T)) ∧ (ρ(w) = v)}), " +
	"W = (λv:A. λz:set(A). COND(into(v) = ∅, &0, (&1 / &4) * κ(v, z))) " +
	"⊢ ∀v:A. ∀z:set(A). ((W(v, z) = &0) ∨ (W(v, z) = (&1 / &4))) ∨ (W(v, z) = -(&1 / &4))"

// TestInspect_ArithProbeOnASetBuilderComparedWithItself bounds `inspect`
// on a state whose arith probe compares a set-builder with one that
// holds it. Read at its definitions the conclusion's guard is
// `{w | … ρ(w) = v} = ∅`, and the first hypothesis is an equation whose
// side `{u | … {w | … ρ(w) = u} ≠ ∅}` is a set-builder too, so the arith
// closer compares the two argument by argument (omega
// argument_congruence.go): body with body, where it meets the guard
// again at the bound variable. The comparison asks 25 equations, each
// more than once by the one above it, and they close on themselves.
// Worked out once each (its table of questions) the probe takes a
// tenth of a second. Worked out once for every path that reaches them
// it does not end, and `inspect` holds the session for as long.
//
// The bound is a stall guard: the probe answers at once or not at all.
func TestInspect_ArithProbeOnASetBuilderComparedWithItself(t *testing.T) {
	installTestNatBundle()
	installTestRealBundle()
	t.Cleanup(func() {
		setTestNatBundle(nil)
		setTestRealBundle(nil)
	})
	res := dsl.ParsePropTextInScope(nestedSetBuilderState, &dsl.ParseScope{
		Syntax:        constSyntax(),
		ConstResolver: registryConstResolver,
	})
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	goal := res.Prop
	require.Equal(t, 3, goal.NumHyps())

	const bound = 30 * time.Second
	done := make(chan []StructuralMove, 1)
	start := time.Now()
	go func() { done <- collectStructuralMoves(goal) }()
	var moves []StructuralMove
	select {
	case moves = <-done:
	case <-time.After(bound):
		t.Fatalf("inspect's structural probes were still running after %v", bound)
	}
	t.Logf("collectStructuralMoves: %v", time.Since(start))
	var kinds []string
	for _, m := range moves {
		kinds = append(kinds, m.Tactic)
	}
	require.Contains(t, kinds, "arith", "the probe must still report the move it verifies")
}
