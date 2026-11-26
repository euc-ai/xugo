package engine

// Evaluation test suite.
//
// Category A: Refuter capability (does XuGo give the correct valid/invalid answer?)
// Category B: Diagnostic quality (does the failure feedback help an agent fix the error?)

import (
	"context"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// mustParse parses a text-format proposition, failing the test on error.
func mustParse(t *testing.T, text string) core.Prop {
	t.Helper()
	r := Parse(text)
	require.Empty(t, r.Errors, "parse error for %q: %v", text, r.Errors)
	require.NotNil(t, r.Prop, "nil Prop for %q", text)
	return r.Prop
}

// ---------------------------------------------------------------------------
// Category A1: Valid derivations (should return valid:true)
// ---------------------------------------------------------------------------

func TestEval_A1_ValidDerivations(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	tests := []struct {
		name string
		text string // parsed as single prop (hyps become hypotheses)
	}{
		{"modus_ponens", "p, p => q ⊢ q"},
		{"contrapositive", "p => q, ~q ⊢ ~p"},
		{"case_analysis", "(p => r), (~p => r) ⊢ r"},
		{"implication_chain", "p => q, q => r ⊢ p => r"},
		{"chain_beside_a_conjunct", "a => b, b => c, d ⊢ (a => c) /\\ d"},
		{"conjunction_elim", "p /\\ q ⊢ p"},
		{"disjunction_intro", "p ⊢ p \\/ q"},
		{"double_negation", "~~p => p"},
		{"excluded_middle", "p \\/ ~p"},
		{"de_morgan", "~(p /\\ q) <=> (~p \\/ ~q)"},
		{"distribution", "(p /\\ (q \\/ r)) <=> ((p /\\ q) \\/ (p /\\ r))"},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			start := time.Now()
			goal := mustParse(t, tc.text)
			res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
				Conclusion: goal,
				TimeoutMs:  2000,
			})
			elapsed := time.Since(start)
			require.NoError(t, err)
			assert.Equal(t, ResultValid, res.Result, "%s should be valid", tc.name)
			assert.Less(t, elapsed, 200*time.Millisecond, "%s took too long: %v", tc.name, elapsed)
		})
	}
}

func TestEval_A1_UniversalInstantiation(t *testing.T) {
	// ∀x:A. P(x) ⊢ P(y) — requires type declarations
	e := newEngine(testEnv())
	ctx := context.Background()

	goal := mustParse(t, "P:A->bool ⊢ (forall x:A. P(x)) => P(y)")
	start := time.Now()
	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Conclusion: goal,
		TimeoutMs:  2000,
	})
	elapsed := time.Since(start)
	require.NoError(t, err)
	assert.Equal(t, ResultValid, res.Result, "universal instantiation should be valid")
	assert.Less(t, elapsed, 200*time.Millisecond)
}

func TestEval_A1_EqualityTransitivity(t *testing.T) {
	// a=b, b=c ⊢ a=c — BasicTactic handles equality transitivity directly.
	e := newEngine(testEnv())
	ctx := context.Background()

	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	c := ext.Var("c", core.TypeA())
	goal := prop.MakeProp(a.Eq(b).Imply(b.Eq(c).Imply(a.Eq(c))))

	start := time.Now()
	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Conclusion: goal,
		TimeoutMs:  2000,
	})
	elapsed := time.Since(start)
	require.NoError(t, err)
	assert.Equal(t, ResultValid, res.Result, "equality transitivity should be valid")
	assert.Less(t, elapsed, 200*time.Millisecond)
}

// ---------------------------------------------------------------------------
// Category A1 (multi-premise): Valid derivations requiring separate premises
// ---------------------------------------------------------------------------

func TestEval_A1_MultiPremise_ModusPonens(t *testing.T) {
	// Premises: p⇒q and p (as separate propositions). Conclusion: q.
	e := newEngine(testEnv())
	ctx := context.Background()

	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())

	premises := []core.Prop{
		prop.MakeProp(p.Imply(q)), // ⊢ p ⇒ q
		prop.MakeProp(p.Core()),   // ⊢ p
	}
	conclusion := prop.MakeProp(q.Core()) // ⊢ q

	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Premises:   premises,
		Conclusion: conclusion,
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	// Premise p ⇒ q on the goal q leaves the residual p, which premise p closes.
	assert.Equal(t, ResultValid, res.Result, "modus ponens over two separate premises")
}

// ---------------------------------------------------------------------------
// Category A2: Invalid derivations (should return valid:false)
// ---------------------------------------------------------------------------

func TestEval_A2_InvalidDerivations(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	tests := []struct {
		name string
		text string
	}{
		// Quantifier flip: ∀x.∃y.P(x,y) ⊬ ∃y.∀x.P(x,y)
		{"quantifier_flip", "P:A->A->bool ⊢ (forall x:A. exists y:A. P(x,y)) => (exists y:A. forall x:A. P(x,y))"},
		// Affirming the consequent: p⇒q, q ⊬ p
		{"affirming_consequent", "p => q, q ⊢ p"},
		// Denying the antecedent: p⇒q, ¬p ⊬ ¬q
		{"denying_antecedent", "p => q, ~p ⊢ ~q"},
		// Converse error: p⇒q ⊬ q⇒p
		{"converse_error", "(p => q) => (q => p)"},
		// Missing premise: p⇒q ⊬ q (needs p)
		{"missing_premise", "p => q ⊢ q"},
		// Non sequitur: p ⊬ q
		{"non_sequitur", "p ⊢ q"},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			goal := mustParse(t, tc.text)
			res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
				Conclusion: goal,
				TimeoutMs:  2000,
			})
			require.NoError(t, err)
			assert.NotEqual(t, ResultValid, res.Result, "%s should be INVALID", tc.name)
			assert.NotEmpty(t, res.Diagnostics, "%s should produce diagnostics", tc.name)
		})
	}
}

func TestEval_A2_DisconnectedEqualityChain(t *testing.T) {
	// a=b, c=d ⊬ a=d (no connection between the two equalities)
	e := newEngine(testEnv())
	ctx := context.Background()

	goal := mustParse(t, "a:A, b:A, c:A, d:A ⊢ (a = b) => (c = d) => (a = d)")

	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Conclusion: goal,
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	assert.NotEqual(t, ResultValid, res.Result, "disconnected equality chain should be invalid")
}

// ---------------------------------------------------------------------------
// Category A5: Complex reasoning (adapted from prover/solver/refuter/refute_test.go)
// ---------------------------------------------------------------------------

func TestEval_A5_FirstOrderEquality(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	D := ext.Var("D", core.MakeFun(core.TypeA(), core.TypeBool()))

	tests := []struct {
		name string
		goal core.Prop
	}{
		{
			// P(x) ⇔ ∀y.((x=y) ⇒ P(y))
			"Leibniz_identity",
			prop.MakeProp(P.Apply(x).Eq(ext.ForAll(y)(x.Eq(y).Imply(P.Apply(y))))),
		},
		{
			// P(x) ⇔ ∃y.((x=y) ∧ P(y))
			"existential_identity",
			prop.MakeProp(P.Apply(x).Eq(ext.Exists(y)(x.Eq(y).And(P.Apply(y))))),
		},
		{
			// ∃x.P(x) ⊢ ∃x.(P(x) ∧ (D(x) ⇒ ∀y.(P(y) ⇒ D(y))))
			"Drinker_variant",
			prop.MakeProp(
				ext.Exists(x)(P.Apply(x).And(D.Apply(x).Imply(ext.ForAll(y)(P.Apply(y).Imply(D.Apply(y)))))),
				ext.Exists(x)(P.Apply(x)),
			),
		},
		{
			// ∃x.∀y.(P(y) ⇔ (x=y)) ⇔ ∃x.P(x) ∧ ∀x.∀y.((P(x) ∧ P(y)) ⇒ (x=y))
			"unique_existence_equiv",
			prop.MakeProp(
				ext.Exists(x)(P.Apply(x)).
					And(ext.ForAll(x, y)(P.Apply(x).And(P.Apply(y)).Imply(x.Eq(y)))).
					Eq(ext.Exists(x)(ext.ForAll(y)(P.Apply(y).Eq(x.Eq(y))))),
			),
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			start := time.Now()
			res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
				Conclusion: tc.goal,
				TimeoutMs:  5000,
			})
			elapsed := time.Since(start)
			require.NoError(t, err)
			assert.Equal(t, ResultValid, res.Result, "%s should be valid (took %v)", tc.name, elapsed)
			t.Logf("%s proved in %v", tc.name, elapsed)
		})
	}
}

func TestEval_A5_GroupTheory(t *testing.T) {
	// Group axioms: assoc + left-identity + left-inverse ⊢ right-inverse
	// This is the classic challenge for equality reasoning.
	e := newEngine(testEnv())
	ctx := context.Background()

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	z := ext.Var("z", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeA(), core.TypeA()))
	I := ext.Var("Inv", core.MakeFun(core.TypeA(), core.TypeA()))
	One := ext.Var("One", core.TypeA())

	assoc := ext.ForAll(x, y, z)(P.Apply(x, P.Apply(y, z)).Eq(P.Apply(P.Apply(x, y), z)))
	leftId := ext.ForAll(x)(P.Apply(One, x).Eq(x))
	leftInv := ext.ForAll(x)(P.Apply(I.Apply(x), x).Eq(One))
	rightInv := ext.ForAll(x)(P.Apply(x, I.Apply(x)).Eq(One))

	goal := prop.MakeProp(rightInv, assoc, leftId, leftInv)

	start := time.Now()
	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Conclusion: goal,
		TimeoutMs:  5000,
	})
	elapsed := time.Since(start)
	require.NoError(t, err)
	assert.Equal(t, ResultValid, res.Result, "group theory right-inverse should be provable (took %v)", elapsed)
	t.Logf("group theory proved in %v", elapsed)
}

func TestEval_A5_RelationTheory(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	TypeB := core.MakeVarType("B")
	x := ext.Var("x", TypeB)
	y := ext.Var("y", TypeB)
	P := ext.Var("P", core.MakeFun(TypeB, TypeB, core.TypeBool()))
	R := ext.Var("R", core.MakeFun(TypeB, TypeB, core.TypeBool()))

	t.Run("sym_total_implies_universal", func(t *testing.T) {
		// Symmetric P, R⇒P, total R ⊢ universal P
		// ∀x.∀y.(P(x,y) ⇒ P(y,x)), ∀x.∀y.(R(x,y) ⇒ P(x,y))
		//   ⊢ (∀x.∀y.(R(x,y) ∨ R(y,x))) ⇒ (∀x.∀y.P(x,y))
		goal := prop.MakeProp(
			ext.ForAll(x, y)(R.Apply(x, y).Or(R.Apply(y, x))).Imply(ext.ForAll(x, y)(P.Apply(x, y))),
			ext.ForAll(x, y)(P.Apply(x, y).Imply(P.Apply(y, x))),
			ext.ForAll(x, y)(R.Apply(x, y).Imply(P.Apply(x, y))),
		)

		start := time.Now()
		res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
			Conclusion: goal,
			TimeoutMs:  5000,
		})
		elapsed := time.Since(start)
		require.NoError(t, err)
		assert.Equal(t, ResultValid, res.Result, "relation symmetry+totality (took %v)", elapsed)
		t.Logf("proved in %v", elapsed)
	})

	t.Run("trans_sym_total_dichotomy", func(t *testing.T) {
		// Transitive P, transitive+symmetric R, P∨R total ⊢ ∀P ∨ ∀R
		z := ext.Var("z", TypeB)
		goal := prop.MakeProp(
			ext.ForAll(x, y)(P.Apply(x, y)).Or(ext.ForAll(x, y)(R.Apply(x, y))),
			ext.ForAll(x, y, z)(P.Apply(x, y).And(P.Apply(y, z)).Imply(P.Apply(x, z))),
			ext.ForAll(x, y, z)(R.Apply(x, y).And(R.Apply(y, z)).Imply(R.Apply(x, z))),
			ext.ForAll(x, y)(R.Apply(x, y).Imply(R.Apply(y, x))),
			ext.ForAll(x, y)(P.Apply(x, y).Or(R.Apply(x, y))),
		)

		start := time.Now()
		res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
			Conclusion: goal,
			TimeoutMs:  5000,
		})
		elapsed := time.Since(start)
		require.NoError(t, err)
		assert.Equal(t, ResultValid, res.Result, "relation dichotomy (took %v)", elapsed)
		t.Logf("proved in %v", elapsed)
	})
}

func TestEval_A5_BooleanQuantifiers(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	x := ext.Var("x", core.TypeBool())
	R := ext.Var("R", core.MakeFun(core.TypeBool(), core.TypeBool()))

	tests := []struct {
		name string
		goal core.Prop
	}{
		{
			// ⊢ ¬∀x.x
			"not_forall_x_x",
			prop.MakeProp(ext.Not(ext.ForAll(x)(x))),
		},
		{
			// ∀x.R(x) = (R(⊤) ∧ R(⊥))
			"forall_bool_conjunction",
			prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Eq(R.Apply(ext.T).And(R.Apply(ext.F)))),
		},
		{
			// ∃x.R(x) = (R(⊤) ∨ R(⊥))
			"exists_bool_disjunction",
			prop.MakeProp(ext.Exists(x)(R.Apply(x)).Eq(R.Apply(ext.T).Or(R.Apply(ext.F)))),
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			start := time.Now()
			res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
				Conclusion: tc.goal,
				TimeoutMs:  5000,
			})
			elapsed := time.Since(start)
			require.NoError(t, err)
			assert.Equal(t, ResultValid, res.Result, "%s should be valid (took %v)", tc.name, elapsed)
			t.Logf("%s proved in %v", tc.name, elapsed)
		})
	}
}

func TestEval_A5_InvalidSubtle(t *testing.T) {
	// Subtle invalid propositions that look plausible — from TestProveUntrue.
	e := newEngine(testEnv())
	ctx := context.Background()

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	z := ext.Var("z", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	S := ext.Var("S", core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))

	tests := []struct {
		name string
		goal core.Prop
	}{
		{
			// ⊢ ∀x.(x = y)  — false: not all elements are equal
			"all_equal",
			prop.MakeProp(ext.ForAll(x)(x.Eq(y))),
		},
		{
			// x ≠ z, y ≠ z ⊢ x = y  — non-sequitur
			"neq_nonsequitur",
			prop.MakeProp(x.Eq(y), ext.Not(x.Eq(z)), ext.Not(y.Eq(z))),
		},
		{
			// ⊢ ∃!z.(S(x,z) = S(z,z))  — uniqueness doesn't hold
			"false_uniqueness",
			prop.MakeProp(ext.Unique(z)(S.Apply(x, z).Eq(S.Apply(z, z)))),
		},
		{
			// P(x) ⇔ ∃y.((x=y) ⇒ P(y))  — subtle: ⇒ instead of ∧
			"existential_imply_vs_and",
			prop.MakeProp(P.Apply(x).Eq(ext.Exists(y)(x.Eq(y).Imply(P.Apply(y))))),
		},
		{
			// P(x) ⇔ ∀y.((x=y) ∧ P(y))  — subtle: ∧ instead of ⇒
			"universal_and_vs_imply",
			prop.MakeProp(P.Apply(x).Eq(ext.ForAll(y)(x.Eq(y).And(P.Apply(y))))),
		},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
				Conclusion: tc.goal,
				TimeoutMs:  5000,
			})
			require.NoError(t, err)
			assert.NotEqual(t, ResultValid, res.Result, "%s should be INVALID", tc.name)
		})
	}
}

// ---------------------------------------------------------------------------
// Category B: Diagnostic Quality (repairability)
// ---------------------------------------------------------------------------

func TestEval_B1_PremisePartial(t *testing.T) {
	// Premise ⊢ P(a)⇒Q(a) applied to goal ⊢ Q(a) should produce premise_partial.
	// Using typed constants (type A) so free vars don't become universally quantified
	// over bool (which would make the residual trivially provable).
	e := newEngine(testEnv())
	ctx := context.Background()

	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))

	// Premise: ⊢ P(a). Conclusion: ⊢ P(a) ∧ P(b).
	// The premise matches one conjunct but leaves residual ⊢ P(b).
	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Premises:   []core.Prop{prop.MakeProp(P.Apply(a))},
		Conclusion: prop.MakeProp(P.Apply(a).And(P.Apply(b))),
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	assert.NotEqual(t, ResultValid, res.Result, "should fail — residual requires P(a)")
	require.NotEmpty(t, res.Diagnostics, "should have diagnostics")

	// First diagnostic should be premise_partial with residual info.
	diag := res.Diagnostics[0]
	assert.Equal(t, DiagPremisePartial, diag.Type, "expected premise_partial diagnostic")
	assert.Contains(t, diag.Message, "premise 0", "should reference premise index")
	assert.Contains(t, diag.Message, "residual", "should mention residual")
	t.Logf("diagnostic type=%s message=%s", diag.Type, diag.Message)
}

func TestEval_B2_MultiplePremiseDiagnostics(t *testing.T) {
	// Two premises, both partial — tests that diagnostics are generated per-premise.
	// Premise 0: ⊢ P(a). Premise 1: ⊢ P(b). Conclusion: ⊢ P(a) ∧ P(b) ∧ P(c).
	// Each premise matches partially but neither closes the goal.
	e := newEngine(testEnv())
	ctx := context.Background()

	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	c := ext.Var("c", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))

	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Premises: []core.Prop{
			prop.MakeProp(P.Apply(a)),
			prop.MakeProp(P.Apply(b)),
		},
		Conclusion: prop.MakeProp(P.Apply(a).And(P.Apply(b)).And(P.Apply(c))),
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	assert.NotEqual(t, ResultValid, res.Result, "should fail — P(c) not derivable")
	require.NotEmpty(t, res.Diagnostics, "should have diagnostics")

	// Should have per-premise diagnostics + summary.
	hasPartial := false
	hasSummary := false
	for _, d := range res.Diagnostics {
		if d.Type == DiagPremisePartial {
			hasPartial = true
		}
		if d.Type == DiagMissingPremise {
			hasSummary = true
		}
		t.Logf("diagnostic type=%s message=%s", d.Type, d.Message)
	}
	assert.True(t, hasPartial, "should have at least one premise_partial diagnostic")
	assert.True(t, hasSummary, "should have summary missing_premise diagnostic")
}

func TestEval_B3_NoPremises(t *testing.T) {
	// Non-tautology with no premises — should produce "no premises" message.
	e := newEngine(testEnv())
	ctx := context.Background()

	q := ext.Var("q", core.TypeBool())

	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{
		Conclusion: prop.MakeProp(q.Core()),
		TimeoutMs:  2000,
	})
	require.NoError(t, err)
	assert.NotEqual(t, ResultValid, res.Result, "bare q should not be provable")
	require.NotEmpty(t, res.Diagnostics, "should have diagnostics")

	diag := res.Diagnostics[0]
	assert.Equal(t, DiagMissingPremise, diag.Type)
	t.Logf("diagnostic message=%s", diag.Message)
}

func TestEval_B5_EqualityChainHint(t *testing.T) {
	// Unit test: residual is "a = c", premise has "a = b" → hint suggests "need b = c".
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	c := ext.Var("c", core.TypeA())

	residual := prop.MakeProp(a.Eq(c))
	premises := []core.Prop{prop.MakeProp(a.Eq(b))}

	hints := structuralRepairHints(residual, premises)
	require.NotEmpty(t, hints, "should produce equality chain hints")

	var found bool
	for _, h := range hints {
		t.Logf("repair_hint: %s", h.Description)
		if strings.Contains(h.Description, "equality chain") {
			found = true
		}
	}
	assert.True(t, found, "should have an equality chain repair hint")
	// The hint should mention both the existing premise side and the needed side.
	assert.Contains(t, hints[0].Description, "a")
	assert.Contains(t, hints[0].Description, "b")
}

func TestEval_B6_ImplicationChainHint(t *testing.T) {
	// Unit test: residual is "p ⇒ r", premise has "p ⇒ q" → hint suggests "need q ⇒ r".
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	r := ext.Var("r", core.TypeBool())

	residual := prop.MakeProp(p.Imply(r))
	premises := []core.Prop{prop.MakeProp(p.Imply(q))}

	hints := structuralRepairHints(residual, premises)
	require.NotEmpty(t, hints, "should produce implication chain hints")

	var found bool
	for _, h := range hints {
		t.Logf("repair_hint: %s", h.Description)
		if strings.Contains(h.Description, "implication chain") {
			found = true
		}
	}
	assert.True(t, found, "should have an implication chain repair hint")
}

func TestEval_B7_ConjunctionHint(t *testing.T) {
	// Unit test: residual is "p ∧ q" → hint suggests "need both conjuncts".
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())

	residual := prop.MakeProp(p.And(q))
	premises := []core.Prop{} // no premises needed for conjunction pattern

	hints := structuralRepairHints(residual, premises)
	require.NotEmpty(t, hints, "should produce conjunction hints")

	var found bool
	for _, h := range hints {
		t.Logf("repair_hint: %s", h.Description)
		if strings.Contains(h.Description, "conjuncts") {
			found = true
		}
	}
	assert.True(t, found, "should have a conjunction repair hint")
}

func TestEval_B8_EqualityChainSymmetric(t *testing.T) {
	// Unit test: residual is "a = c", premise has "b = c" → hint suggests "need a = b".
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	c := ext.Var("c", core.TypeA())

	residual := prop.MakeProp(a.Eq(c))
	premises := []core.Prop{prop.MakeProp(b.Eq(c))}

	hints := structuralRepairHints(residual, premises)
	require.NotEmpty(t, hints, "should produce equality chain hints for symmetric case")

	var found bool
	for _, h := range hints {
		t.Logf("repair_hint: %s", h.Description)
		if strings.Contains(h.Description, "equality chain") {
			found = true
		}
	}
	assert.True(t, found, "should have an equality chain repair hint")
}

func TestEval_B9_EqualityFallback(t *testing.T) {
	// Unit test: residual is "a = c", no premises match → generic equality hint.
	a := ext.Var("a", core.TypeA())
	c := ext.Var("c", core.TypeA())

	residual := prop.MakeProp(a.Eq(c))
	premises := []core.Prop{} // no premises

	hints := structuralRepairHints(residual, premises)
	require.NotEmpty(t, hints, "should produce fallback equality hint")
	assert.Contains(t, hints[0].Description, "connecting these terms")
	t.Logf("repair_hint: %s", hints[0].Description)
}

func TestEval_B10_NoPatternMatch(t *testing.T) {
	// Unit test: residual is a bare atom P(a) — no structural pattern matches.
	a := ext.Var("a", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))

	residual := prop.MakeProp(P.Apply(a))
	premises := []core.Prop{}

	hints := structuralRepairHints(residual, premises)
	assert.Empty(t, hints, "bare atom should not trigger any structural hint")
}

// ---------------------------------------------------------------------------
// Category B11-B13: Hypothesis chain diagnostics
// When text format "h1, h2 ⊢ conclusion" fails, decompose hypotheses and
// provide per-hypothesis diagnostics instead of a generic "not derivable" message.
// ---------------------------------------------------------------------------

func TestEval_B11_HypothesisChain_DogfoodReproducer(t *testing.T) {
	// The exact case from dogfooding: 4 hypotheses, invalid derivation.
	// Previously returned only "conclusion X is not derivable from hypotheses [...]".
	// Now should return per-hypothesis analysis with residuals.
	e := newEngine(testEnv())
	ctx := context.Background()

	goal := mustParse(t, "queued => processed, processed => response, overloaded => ~queued, ~queued => ~processed ⊢ overloaded => ~response")
	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{Conclusion: goal, TimeoutMs: 5000})
	require.NoError(t, err)
	assert.NotEqual(t, ResultValid, res.Result, "this derivation is invalid")

	// Must have more than just the summary diagnostic.
	require.Greater(t, len(res.Diagnostics), 1, "should have per-hypothesis diagnostics, not just summary")

	// The summary should still be present as the last diagnostic.
	last := res.Diagnostics[len(res.Diagnostics)-1]
	assert.Equal(t, DiagMissingPremise, last.Type)
	assert.Contains(t, last.Message, "not derivable from hypotheses")

	// At least one diagnostic should be premise_partial with chain analysis.
	hasPartial := false
	for _, d := range res.Diagnostics {
		if d.Type == DiagPremisePartial {
			hasPartial = true
			break
		}
	}
	assert.True(t, hasPartial, "at least one hypothesis should produce a chain analysis; diagnostics: %v", res.Diagnostics)

	// The chain analysis should identify the missing link.
	hasChainHint := false
	for _, d := range res.Diagnostics {
		if d.Type == DiagPremisePartial && strings.Contains(d.Message, "chain") {
			hasChainHint = true
			// Should mention what it can reach and what's missing.
			assert.Contains(t, d.Message, "¬processed")
			assert.True(t, len(d.RepairHints) > 0, "chain diagnostic should have repair hints")
			break
		}
	}
	assert.True(t, hasChainHint, "should have implication chain analysis")
}

func TestEval_B12_HypothesisChain_SimpleGap(t *testing.T) {
	// a => b, c => d ⊢ a => d — disconnected chain, should be invalid.
	e := newEngine(testEnv())
	ctx := context.Background()

	goal := mustParse(t, "a => b, c => d ⊢ a => d")
	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{Conclusion: goal, TimeoutMs: 5000})
	require.NoError(t, err)
	assert.NotEqual(t, ResultValid, res.Result)

	// Should have per-hypothesis diagnostics.
	require.Greater(t, len(res.Diagnostics), 1)

	// Summary at end.
	last := res.Diagnostics[len(res.Diagnostics)-1]
	assert.Equal(t, DiagMissingPremise, last.Type)
}

func TestEval_B13_HypothesisChain_IrrelevantHyps(t *testing.T) {
	// p, q ⊢ r — hypotheses are unrelated to conclusion.
	e := newEngine(testEnv())
	ctx := context.Background()

	goal := mustParse(t, "p, q ⊢ r")
	res, err := e.CheckDerivation(ctx, &CheckDerivationRequest{Conclusion: goal, TimeoutMs: 5000})
	require.NoError(t, err)
	assert.NotEqual(t, ResultValid, res.Result)

	// Should still produce per-hypothesis analysis (even if all partial/no-match).
	require.Greater(t, len(res.Diagnostics), 1, "should decompose hypotheses even when irrelevant")
}

// ---------------------------------------------------------------------------
// Performance: round-trip time assertions
// ---------------------------------------------------------------------------

func TestEval_Performance_StatelessOps(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()

	// Each stateless operation should complete in < 200ms.
	tests := []struct {
		name string
		fn   func() error
	}{
		{"check_tautology", func() error {
			goal := mustParse(t, "p => p")
			_, err := e.CheckDerivation(ctx, &CheckDerivationRequest{Conclusion: goal, TimeoutMs: 2000})
			return err
		}},
		{"check_invalid", func() error {
			goal := mustParse(t, "p ⊢ q")
			_, err := e.CheckDerivation(ctx, &CheckDerivationRequest{Conclusion: goal, TimeoutMs: 2000})
			return err
		}},
		{"check_consistency", func() error {
			p := ext.Var("p", core.TypeBool())
			_, err := e.CheckConsistency(ctx, &CheckConsistencyRequest{
				Statements: []core.Prop{prop.MakeProp(p.Core()), prop.MakeProp(ext.Not(p).Core())},
				TimeoutMs:  2000,
			})
			return err
		}},
	}

	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			start := time.Now()
			err := tc.fn()
			elapsed := time.Since(start)
			require.NoError(t, err)
			assert.Less(t, elapsed, 200*time.Millisecond, "%s took %v", tc.name, elapsed)
		})
	}
}
