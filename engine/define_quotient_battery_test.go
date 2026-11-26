package engine

import (
	"context"
	"go/format"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestTranscriptC_Battery is the quotient door and the lift as a
// literal battery — every author move as written, against the real
// registry and corpus: the naturals modulo parity, de novo.
//
//	C1  define recursive zz_par_rel(x, y) ⇔ nat_mod(x, 2) = nat_mod(y, 2)
//	C2  add-goal  equivalence(zz_par_rel)   — the one input, proved FIRST
//	    def_expand ×4, simp, auto
//	C3  define quotient zz_parity = num / zz_par_rel, class map zz_parity_class
//	    → seven PROVED sections; <Q>_induction / _sound / _exact bound;
//	      Eq installed; ⁅x⁆ reads as the class map
//	C4  define recursive zz_par_same(⁅a⁆) = ⁅a⁆        — a LIFT: the
//	    respectfulness opens; auto closes it; the rule installs on close
//	C5  define recursive zz_par_eqz(⁅a⁆) ⇔ nat_mod(a, 2) = 0 — a relation on
//	    classes; simp + auto close the respectfulness
//	C6  add-goal  ∀q:zz_parity. zz_par_eqz(zz_par_same(q)) ⇔ zz_par_eqz(q)
//	    induction q; simp; simplify            — Lean's inductionOn + simp
//	C7  add-goal  ∀a b. ⁅a⁆ = ⁅b⁆ ⇔ nat_mod(a, 2) = nat_mod(b, 2)
//	    simp; simplify                         — Eq as a simp rule
//	C8  emit-section (a quotient section)     — family.DefineQuotient, 1:1,
//	    Equivalence naming the equivalence's future entry
//	C9  emit-section (a lift section)         — family.Define with Respects
//	C10 emit-section (C6)                     — cites the entries by name
//
// Names are zz-prefixed (the A-battery convention): the mint is
// process-global and permanent for the test process.
func TestTranscriptC_Battery(t *testing.T) {
	env := testEnv()
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        registry.GetConstMetaManager().LoadConstMeta,
		LoadOrStoreConstMeta: registry.GetConstMetaManager().LoadOrStoreConstMeta,
		Syntax:               registry.GetConstMetaManager(),
		RangeConstMeta: func(yield func(core.ConstTermMeta) bool) {
			registry.GetConstMetaManager().Range(yield)
		},
		CNFStore: proof.NewMemoryCNFStore(),
	}
	env.LibraryThms = serve.InductionPrinciples()
	serve.RegisterAll(env)
	serve.InstallProofPolicy()
	installTestNatBundle()
	e := newEngine(env)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	apply := func(goalID, tacticType string, tac *TacticReq) *StepResult {
		t.Helper()
		req := TacticReq{Type: tacticType}
		if tac != nil {
			req = *tac
			req.Type = tacticType
		}
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: req})
		require.NoError(t, err, "apply %s on %s", tacticType, goalID)
		require.True(t, res.Success, "apply %s on %s: %+v", tacticType, goalID, res.Diagnostics)
		return res
	}
	scope := func() *dsl.ParseScope {
		return &dsl.ParseScope{
			ConstResolver:      envConstResolver(s.env),
			Syntax:             registry.GetConstMetaManager(),
			StrictResolution:   true,
			FreshenMetaLetters: true,
		}
	}
	addGoal := func(text string) string {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, scope())
		require.Empty(t, parsed.Errors, "add-goal %q", text)
		s.mu.Lock()
		defer s.mu.Unlock()
		return s.AddGoal(parsed.Prop)
	}
	states := func(root *proof.GoalStackNode, text string) {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, scope())
		require.Empty(t, parsed.Errors, "%s", text)
		require.True(t, root.Goal.AlphaEquals(parsed.Prop), "states %s, want %s",
			ext.PrintTerm(root.Goal.Conclusion()), text)
	}
	emit := func(section int, funcName string) string {
		t.Helper()
		res, err := e.EmitSection(&EmitSectionRequest{
			SessionID: info.ID, Section: section, FuncName: funcName, Family: "zz_fam",
		})
		require.NoError(t, err)
		t.Logf("emitted %s:\n%s", funcName, res.Go)
		_, ferr := format.Source([]byte(res.Go))
		require.NoError(t, ferr, "the emitted file must be well-formed Go")
		require.NotContains(t, res.Go, "TODO")
		return res.Go
	}

	// C1 — the relation.
	relRes, err := e.Define(&DefineRequest{SessionID: info.ID, Recursive: &DefineRecursive{
		Name: "zz_par_rel", Type: "num → num → bool",
		Equations: []string{"∀x y:num. zz_par_rel(x, y) ⇔ nat_mod(x, 2) = nat_mod(y, 2)"},
	}})
	require.NoError(t, err)
	require.Equal(t, "direct", relRes.Shape)

	// The door refuses a quotient whose equivalence is not yet a proved
	// section, naming the statement to prove.
	_, err = e.Define(&DefineRequest{SessionID: info.ID, Quotient: &DefineQuotient{
		Type: "zz_parity", Mk: "zz_parity_class", Abs: "zz_parity_abs", Rep: "zz_parity_rep", Relation: "zz_par_rel",
	}})
	require.Error(t, err)
	require.Contains(t, err.Error(), "is not a proved section")

	// C2 — the equivalence, as an ordinary goal: unfold the structure
	// and its three laws, the relation's definition fires from the simp
	// set, and the residue is propositional over the parities.
	equivalence := addGoal("equivalence(zz_par_rel)")
	equivalenceSection := len(s.sections) - 1
	g := equivalence
	for _, c := range []string{"equivalence", "reflexive", "symmetric", "transitive"} {
		res := apply(g, "def_expand", &TacticReq{Const: c})
		require.Len(t, res.Produced, 1, "def_expand %s", c)
		g = res.Produced[0].GoalID
	}
	simped := apply(g, "simp", nil)
	require.Len(t, simped.Produced, 1)
	require.Equal(t, "close", apply(simped.Produced[0].GoalID, "auto", nil).Effect, "C2 closes")
	require.True(t, s.sections[equivalenceSection].root.Proved())

	// C3 — the quotient: the door finds C2 by its statement.
	qRes, err := e.Define(&DefineRequest{SessionID: info.ID, Quotient: &DefineQuotient{
		Type: "zz_parity", Mk: "zz_parity_class", Abs: "zz_parity_abs", Rep: "zz_parity_rep", Relation: "zz_par_rel",
	}})
	require.NoError(t, err)
	require.Equal(t, "quotient", qRes.Shape)
	require.Equal(t, "zz_parity", qRes.TypeDefined)
	require.Equal(t, []string{"zz_parity_class", "zz_parity_abs", "zz_parity_rep"}, qRes.Consts)
	require.Equal(t, []string{"zz_parity_induction", "zz_parity_sound", "zz_parity_exact"}, qRes.Derived)
	require.Equal(t, []string{"Eq"}, qRes.SimpInstalledNames)
	require.Len(t, qRes.DerivedSections, 7)
	byKind := map[string]DerivedSectionInfo{}
	for _, sec := range qRes.DerivedSections {
		require.True(t, s.sections[sec.Section].root.Proved(), "C3: the %s section is proved on return", sec.Kind)
		byKind[sec.Kind] = sec
	}
	states(s.sections[byKind["Surjectivity"].Section].root, "∀q:zz_parity. ∃x:num. q = zz_parity_class(x)")
	states(s.sections[byKind["Eq"].Section].root, "∀x y:num. ⁅x⁆ = ⁅y⁆ ⇔ zz_par_rel(x, y)")
	states(s.sections[byKind["ForallOnImage"].Section].root, "∀P:(zz_parity → bool). (∀q:zz_parity. P(q)) ⇔ ∀x:num. P(⁅x⁆)")
	for _, name := range qRes.Derived {
		_, ok := s.env.LookupLibraryThm(name)
		require.True(t, ok, "%s is bound in the env overlay", name)
	}
	// A second mint of the type name is refused.
	_, err = e.Define(&DefineRequest{SessionID: info.ID, Quotient: &DefineQuotient{
		Type: "zz_parity", Mk: "zz_parity_class2", Abs: "zz_parity_abs2", Rep: "zz_parity_rep2", Relation: "zz_par_rel",
	}})
	require.Error(t, err)
	require.Contains(t, err.Error(), "already in use")

	// C4 — a lift: the class map as a constructor pattern, the
	// respectfulness opened and closed by auto, the rule installed on
	// the closing apply.
	sameRes, err := e.Define(&DefineRequest{SessionID: info.ID, Recursive: &DefineRecursive{
		Name: "zz_par_same", Type: "zz_parity → zz_parity",
		Equations: []string{"∀a:num. zz_par_same(⁅a⁆) = ⁅a⁆"},
	}})
	require.NoError(t, err)
	require.Equal(t, "lift", sameRes.Shape)
	require.Equal(t, "quotient_lift", sameRes.Schema)
	require.NotEmpty(t, sameRes.ObligationGoalID)
	t.Logf("C4 obligation: %s", sameRes.Obligation)
	sameSection := sameRes.Section
	require.False(t, s.sections[sameSection].root.Proved(), "the lift waits on its obligation")
	closed := apply(sameRes.ObligationGoalID, "auto", nil)
	require.Equal(t, "close", closed.Effect)
	require.Len(t, closed.DefineCompleted, 1, "the closing apply completes the lift")
	require.Equal(t, "quotient_lift", closed.DefineCompleted[0].Schema)
	require.Equal(t, 1, closed.DefineCompleted[0].SimpInstalled, "the computation rule installs")
	require.True(t, s.sections[sameSection].root.Proved())

	// C5 — a relation on classes, with the relation unfolded first.
	eqzRes, err := e.Define(&DefineRequest{SessionID: info.ID, Recursive: &DefineRecursive{
		Name: "zz_par_eqz", Type: "zz_parity → bool",
		Equations: []string{"∀a:num. zz_par_eqz(⁅a⁆) ⇔ nat_mod(a, 2) = 0"},
	}})
	require.NoError(t, err)
	require.Equal(t, "lift", eqzRes.Shape)
	eqzSection := eqzRes.Section
	simpedOb := apply(eqzRes.ObligationGoalID, "simp", nil)
	require.Len(t, simpedOb.Produced, 1)
	closedEqz := apply(simpedOb.Produced[0].GoalID, "auto", nil)
	require.Equal(t, "close", closedEqz.Effect)
	require.Len(t, closedEqz.DefineCompleted, 1)
	require.True(t, s.sections[eqzSection].root.Proved())

	// C6 — induction over the quotient, the computation rules by simp.
	use := addGoal("∀q:zz_parity. zz_par_eqz(zz_par_same(q)) ⇔ zz_par_eqz(q)")
	useSection := len(s.sections) - 1
	ind := apply(use, "induction", &TacticReq{Const: "q"})
	require.Len(t, ind.Produced, 1, "one case: the class of a representative")
	simpedUse := apply(ind.Produced[0].GoalID, "simp", nil)
	require.Len(t, simpedUse.Produced, 1)
	require.Equal(t, "close", apply(simpedUse.Produced[0].GoalID, "simplify", nil).Effect, "C6 closes")
	require.True(t, s.sections[useSection].root.Proved())

	// C7 — Eq as a simp rule: class equality is the relation.
	eqUse := addGoal("∀a b:num. ⁅a⁆ = ⁅b⁆ ⇔ nat_mod(a, 2) = nat_mod(b, 2)")
	eqUseSection := len(s.sections) - 1
	simpedEq := apply(eqUse, "simp", nil)
	require.Len(t, simpedEq.Produced, 1)
	require.Equal(t, "close", apply(simpedEq.Produced[0].GoalID, "simplify", nil).Effect, "C7 closes")
	require.True(t, s.sections[eqUseSection].root.Proved())

	// C8 — emit: any quotient section renders as the ONE
	// family.DefineQuotient call, the equivalence named as its future
	// entry.
	qEmit := emit(byKind["Eq"].Section, "ZzParityDef")
	require.Contains(t, qEmit, "var ZzParityDef = family.DefineQuotient(registry.QuotientEntry{")
	require.Contains(t, qEmit, `Name:        "ZzParity",`)
	require.Contains(t, qEmit, `Type:        "zz_parity",`)
	require.Contains(t, qEmit, `Mk:          "zz_parity_class",`)
	require.Contains(t, qEmit, `Relation:    "zz_par_rel",`)
	require.Contains(t, qEmit, "Equivalence: ZzParRelEquivalence,", "the equivalence names its future sibling entry")
	require.Equal(t, qEmit, emit(byKind["Surjectivity"].Section, "ZzParityDef"), "every section renders the same call")

	// C9 — emit: a lift renders as family.Define with its Respects.
	liftEmit := emit(eqzSection, "ZzParEqzDef")
	require.Contains(t, liftEmit, "family.Define(registry.DefEntry{")
	require.Contains(t, liftEmit, `"∀a:num. zz_par_eqz(⁅a⁆) ⇔ nat_mod(a, 2) = 0",`, "the author's spelling is kept")
	require.Contains(t, liftEmit, "Respects: []Action{")
	require.NotContains(t, liftEmit, "Measure:")

	// C10 — emit: the use member cites the lifts' future entries by
	// name, and reads the quotient's future induction entry by the name
	// it serves — no source line names that one, so the emit reports it
	// among the member's deps, which its landing's recording observes.
	useEmit := emit(useSection, "Build_ZzParEqzSame")
	require.Contains(t, useEmit, "ZzParSame")
	require.Contains(t, useEmit, "ZzParEqz")
	useRes, uerr := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: useSection, FuncName: "Build_ZzParEqzSame", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, uerr)
	require.Contains(t, useRes.DepNames, "zz_fam.ZzParityInduct")

	// A list naming a definition is refused for that reason: beside a
	// theorem, and as the target beside a theorem.
	_, derr := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: useSection, FuncName: "Build_ZzParEqzSame", Family: "zz_fam", IncludePrior: []int{eqzSection},
	})
	require.ErrorContains(t, derr, "are definitions")
	_, derr = e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: eqzSection, FuncName: "ZzParEqzDef", Family: "zz_fam", IncludePrior: []int{useSection},
	})
	require.ErrorContains(t, derr, "is a definition, a member of its own")

	// The equivalence emits as an ordinary member under the name the
	// quotient's Equivalence field expects.
	eqvEmit := emit(equivalenceSection, "Build_ZzParRelEquivalence")
	require.Contains(t, eqvEmit, "ZzParRelEquivalence")
}
