package engine

import (
	"context"
	"strings"
	"sync"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/relations/well_founded"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// familySessionEnv is the serve's env wiring for a session that binds a
// family: the process-global const-meta manager (a registry definition
// mints into it), the corpus induction principles and the nat bundle.
func familySessionEnv() *proof.ProverEnv {
	env := testEnv()
	mgr := registry.GetConstMetaManager()
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        mgr.LoadConstMeta,
		LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
		Syntax:               mgr,
		RangeConstMeta: func(yield func(core.ConstTermMeta) bool) {
			mgr.Range(yield)
		},
	}
	env.LibraryThms = serve.InductionPrinciples()
	serve.InstallProofPolicy()
	installTestNatBundle()
	return env
}

// familyFixture is a registered family with one definition of every
// shape the door serves — what a chapter that made its objects in
// session lands, and what a later session of the chapter starts from.
type familyFixture struct {
	fam                   *registry.Family
	xor, sumto, gcd, spec *registry.ProofEntry
	btree                 *registry.DatatypeEntries
}

var (
	familyFixtureOnce sync.Once
	familyFixtureVal  familyFixture
)

func testFamily(t *testing.T) familyFixture {
	t.Helper()
	familyFixtureOnce.Do(func() {
		fam := registry.NewFamily("zz_family_session_test", nil)
		familyFixtureVal = familyFixture{
			fam: fam,
			xor: fam.Define(registry.DefEntry{
				Name: "Xor", Const: "zz_fs_xor", Type: "bool → bool → bool",
				Equations: []string{"∀p q:bool. zz_fs_xor(p, q) ⇔ (p ∨ q) ∧ ¬(p ∧ q)"},
			}),
			sumto: fam.Define(registry.DefEntry{
				Name: "Sumto", Const: "zz_fs_sumto", Type: "num → num",
				Equations: []string{
					"zz_fs_sumto(0) = 0",
					"∀n:num. zz_fs_sumto(suc(n)) = zz_fs_sumto(n) + suc(n)",
				},
			}),
			gcd: fam.Define(registry.DefEntry{
				Name: "Gcd", Const: "zz_fs_gcd", Type: "num → num → num",
				Equations: []string{
					"∀m n:num. zz_fs_gcd(m, n) = COND(n = 0, m, zz_fs_gcd(n, nat_mod(m, n)))",
				},
				Measure:     "λn:num. n",
				Termination: []proof.Action{proof.By(nat_div_mod.Division.Entry())},
				Deps:        []registry.EntryLike{well_founded.Recursion, well_founded.Measure, nat_div_mod.Division},
			}),
			btree: fam.DefineData(registry.DataEntry{
				Name: "Btree", Type: "zz_fs_btree", Params: []string{"A"},
				Constructors: []proof.DataConstructorSpec{
					{Name: "zz_fs_bleaf", Args: []string{"A"}},
					{Name: "zz_fs_bnode", Args: []string{"zz_fs_btree(A)", "zz_fs_btree(A)"}},
				},
				Principles: registry.DataPrinciples{
					Induction: "BtreeInduct", Recursion: "BtreeRecursion",
					Injective: "BtreeInj", Distinct: "BtreeDistinct",
				},
				Deps: []registry.EntryLike{
					datatype_universe.Recursion, datatype_universe.FamilyCons, datatype_universe.NodeInjective,
					peano.SucNotZero, peano.SucInjective,
					pairs.Fst, pairs.Snd, pairs.PairEq,
				},
			}),
			spec: fam.DefineSpec(registry.SpecEntry{
				Name:   "Pin",
				Consts: []registry.SpecConst{{Const: "zz_fs_pin", Type: "num → num"}},
				Spec:   "∀n:num. n ≤ zz_fs_pin(n) ∧ zz_fs_pin(n) ≤ n",
				ExistenceBody: func(ctx *proof.Script) []proof.Action {
					n0 := ctx.Var("n_0", dsl.NumType)
					return []proof.Action{proof.StripQuant(), proof.Witness(n0), proof.By(nat_order.LessEqRefl.Entry())}
				},
				Deps: []registry.EntryLike{nat_order.LessEqRefl},
			}),
		}
	})
	return familyFixtureVal
}

// TestSetSessionFamily_InstallsRegisteredDefinitions: binding a session
// to a family installs, per registered definition, exactly what the
// session `define` of that shape installs — the direct and recursive
// characterizing theorems whole, a datatype's INJ and DISTINCT, the
// WF definition's guarded readings, nothing for a specification — each
// rule backed by the entry's replay promise and attributed to its entry.
func TestSetSessionFamily_InstallsRegisteredDefinitions(t *testing.T) {
	fx := testFamily(t)
	e := newEngine(familySessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	binding, err := e.SetSessionFamily(info.ID, fx.fam.Name, nil)
	require.NoError(t, err)
	assert.Equal(t, fx.fam.Name, binding.Family)

	byEntry := map[string][]InstalledRule{}
	for _, r := range binding.Installed {
		byEntry[r.Entry] = append(byEntry[r.Entry], r)
	}
	assert.Len(t, byEntry[fx.xor.Name], 1, "direct: the characterizing theorem whole")
	assert.Len(t, byEntry[fx.sumto.Name], 1, "recursive: the clause conjunction whole")
	assert.Len(t, byEntry[fx.btree.Inj.Name], 1, "data: INJ is a rule")
	assert.Len(t, byEntry[fx.btree.Distinct.Name], 1, "data: DISTINCT is a rule")
	assert.Empty(t, byEntry[fx.btree.Induct.Name], "data: INDUCT is a principle, not a rewrite")
	assert.Empty(t, byEntry[fx.btree.Recursion.Name], "data: RECURSION is a principle, not a rewrite")
	assert.Len(t, byEntry[fx.gcd.Name], 2, "wf: the two guarded readings of the COND equation")
	assert.Empty(t, byEntry[fx.spec.Name], "spec: a specification is not a directed rewrite")
	assert.Equal(t, "wf", byEntry[fx.gcd.Name][0].Shape)

	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	require.Len(t, s.simpRules, len(binding.Installed))
	for _, r := range s.simpRules {
		require.NotNil(t, r.entry, "an imported rule is attributed to its entry")
		require.NotNil(t, r.cert)
		if r.entry.Definition != proof.DefinitionWF {
			assert.Equal(t, r.cert.AlphaKey(), r.rule.AlphaKey(),
				"%s: a whole-theorem rule IS the entry's served statement", r.entry.Name)
		}
	}
	xorThm := serve.EntryThm(s.env, fx.xor)
	assert.Equal(t, xorThm.AlphaKey(), s.simpRules[0].rule.AlphaKey(),
		"the direct rule is the entry's replay promise")
	assert.Same(t, fx.fam, s.family)

	view, err := e.SessionLineage(info.ID)
	require.NoError(t, err)
	require.NotEmpty(t, view.Events)
	assert.Equal(t, "family "+fx.fam.Name, view.Events[0].Summary)
}

// TestSetSessionFamily_MatchesSessionDefine is the consistency gate: a
// session that `define`s the same equations installs the same rules
// (modulo the constant names) as a session that imports them from the
// family — the two doors share one derivation.
func TestSetSessionFamily_MatchesSessionDefine(t *testing.T) {
	fx := testFamily(t)
	ctx := context.Background()

	imported := newEngine(familySessionEnv())
	a, err := imported.CreateSession(ctx)
	require.NoError(t, err)
	_, err = imported.SetSessionFamily(a.ID, fx.fam.Name, nil)
	require.NoError(t, err)
	sa, _ := imported.getSession(a.ID)
	want := map[string]bool{}
	for _, r := range sa.simpRules {
		switch r.entry {
		case fx.xor, fx.sumto, fx.btree.Inj, fx.btree.Distinct:
			want[prop.PrintProp(r.rule)] = true
		}
	}
	require.Len(t, want, 4)

	defined := newEngine(familySessionEnv())
	b, err := defined.CreateSession(ctx)
	require.NoError(t, err)
	for _, req := range []*DefineRequest{
		{SessionID: b.ID, Recursive: &DefineRecursive{
			Name: "zz_fs2_xor", Type: "bool → bool → bool",
			Equations: []string{"∀p q:bool. zz_fs2_xor(p, q) ⇔ (p ∨ q) ∧ ¬(p ∧ q)"}}},
		{SessionID: b.ID, Recursive: &DefineRecursive{
			Name: "zz_fs2_sumto", Type: "num → num",
			Equations: []string{
				"zz_fs2_sumto(0) = 0",
				"∀n:num. zz_fs2_sumto(suc(n)) = zz_fs2_sumto(n) + suc(n)"}}},
		{SessionID: b.ID, Data: &DefineData{
			Name: "zz_fs2_btree", Params: []string{"A"},
			Constructors: []proof.DataConstructorSpec{
				{Name: "zz_fs2_bleaf", Args: []string{"A"}},
				{Name: "zz_fs2_bnode", Args: []string{"zz_fs2_btree(A)", "zz_fs2_btree(A)"}}}}},
	} {
		_, err := defined.Define(req)
		require.NoError(t, err)
	}
	sb, _ := defined.getSession(b.ID)
	got := map[string]bool{}
	for _, r := range sb.simpRules {
		require.Nil(t, r.entry, "a session define's rule has no entry")
		got[strings.ReplaceAll(prop.PrintProp(r.rule), "zz_fs2_", "zz_fs_")] = true
	}
	assert.Equal(t, want, got, "imported and session-defined rule sets agree modulo the constant names")
}

// TestSetSessionFamily_Validation pins the binding contract: an unknown
// family is refused, a session binds once, and only before any goal.
func TestSetSessionFamily_Validation(t *testing.T) {
	fx := testFamily(t)
	e := newEngine(familySessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)

	_, err = e.SetSessionFamily(info.ID, "no/such_family", nil)
	require.Error(t, err)
	assert.Contains(t, err.Error(), "not registered")

	_, err = e.SetSessionFamily(info.ID, fx.fam.Name, []string{"no/such_family"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "not registered")

	_, err = e.SetSessionFamily(info.ID, fx.fam.Name, []string{fx.fam.Name})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "imported twice")

	_, err = e.SetSessionFamily(info.ID, fx.fam.Name, nil)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, fx.fam.Name, nil)
	require.Error(t, err)
	assert.Contains(t, err.Error(), "already bound")

	later, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(later.ID)
	_, F := curateF()
	x := ext.Var("x", TypeInd)
	s.AddGoal(prop.MakeProp(F.Apply(x)))
	_, err = e.SetSessionFamily(later.ID, fx.fam.Name, nil)
	require.Error(t, err)
	assert.Contains(t, err.Error(), "before any add-goal")
}

// TestFamilySession_SimpFiresOnImportedRule: the bare `simp` rewrites
// with an imported definition exactly as with a session define, the
// rule child closing from the entry's promise; the emitted member cites
// the entry as a typed dep of its family.
func TestFamilySession_SimpFiresOnImportedRule(t *testing.T) {
	fx := testFamily(t)
	e := newEngine(familySessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.SetSessionFamily(info.ID, fx.fam.Name, nil)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	parsed := dsl.ParsePropTextInScope("zz_fs_xor(⊤, ⊥) ⇔ ⊤", &dsl.ParseScope{
		ConstResolver:    envConstResolver(s.env),
		StrictResolution: true,
	})
	require.Empty(t, parsed.Errors, "%v", parsed.Errors)
	s.mu.Lock()
	goalID := s.AddGoal(parsed.Prop)
	s.mu.Unlock()

	simped, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "simp"}})
	require.NoError(t, err)
	require.True(t, simped.Success, "%+v", simped.Diagnostics)
	require.Len(t, simped.Produced, 1, "simp leaves exactly the rewritten residual")
	require.True(t, simped.Produced[0].Changes.ConclusionChanged)

	closed, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: simped.Produced[0].GoalID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	require.Equal(t, "close", closed.Effect, "%+v", closed.Diagnostics)
	require.True(t, s.sections[0].root.Proved())

	emit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: 0, FuncName: "Build_XorFires", Family: "zz_other", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted:\n%s", emit.Go)
	assert.Contains(t, emit.Go, fx.xor.Name, "the simp fire cites the imported definition's entry")
	assert.Contains(t, emit.Go, "library/proofs/"+fx.fam.Name, "as a typed dep of its family")
}

// TestFamilySession_RealFamily binds the words/machine_word chapter — the
// corpus's family with registered definitions — and checks every one of
// them is installed as its served statement.
func TestFamilySession_RealFamily(t *testing.T) {
	fam, ok := registry.FamilyByName("words/machine_word")
	require.True(t, ok)
	var defs []*registry.ProofEntry
	for _, entry := range fam.Entries() {
		if entry.Definition != proof.NotADefinition {
			defs = append(defs, entry)
		}
	}
	require.NotEmpty(t, defs)

	e := newEngine(familySessionEnv())
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	binding, err := e.SetSessionFamily(info.ID, fam.Name, nil)
	require.NoError(t, err)
	require.Len(t, binding.Installed, len(defs))
	s, _ := e.getSession(info.ID)
	for i, entry := range defs {
		assert.Same(t, entry, s.simpRules[i].entry)
		assert.Equal(t, serve.EntryThm(s.env, entry).AlphaKey(), s.simpRules[i].rule.AlphaKey(),
			"%s installs as its served statement", entry.Name)
	}
}
