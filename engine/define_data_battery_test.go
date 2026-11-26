package engine

import (
	"context"
	"github.com/euc-ai/xugo/library/registry"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestTranscriptB_Battery is the datatype transcript as a literal
// battery test — every author move as written, against the real
// registry and the real corpus:
//
//	B1  define btree (data: bleaf(A) | bnode(btree, btree))
//	B2  define bsize  (recursive over btree)
//	B3  define bmirror (recursive over btree)
//	B4  add-goal  ∀t:btree(A). bsize(bmirror(t)) = bsize(t)
//	B5  induction t                  — dispatches on t's TYPE to btree_induction
//	B6  simp                         — leaf focus (+ the trivial-refl closer)
//	B7  simp; by — premises: IH_l, IH_r; lemmas: nat_arith.AddSym — node focus
//	B8  emit-section                 — family.DefineData + family.Define ×2 + the member
//
// Names are zz-prefixed (the A-battery convention): the mint is
// process-global and permanent for the test process.
func TestTranscriptB_Battery(t *testing.T) {

	env := testEnv()
	// In-memory CNF proof store: B7's `by` runs a live refute whose
	// proof the B8 emit-time capture re-reads (production wires the
	// file-backed session store here).
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
		return res
	}
	addGoal := func(text string) string {
		t.Helper()
		parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
			ConstResolver:      envConstResolver(s.env),
			StrictResolution:   true,
			FreshenMetaLetters: true,
		})
		require.Empty(t, parsed.Errors, "add-goal %q", text)
		s.mu.Lock()
		defer s.mu.Unlock()
		return s.AddGoal(parsed.Prop)
	}

	// B1 — define the datatype from its constructor spec.
	dataRes, err := e.Define(&DefineRequest{
		SessionID: info.ID,
		Data: &DefineData{
			Name:   "zz_btree_b",
			Params: []string{"A"},
			Constructors: []proof.DataConstructorSpec{
				{Name: "zz_bleaf_b", Args: []string{"A"}},
				{Name: "zz_bnode_b", Args: []string{"zz_btree_b(A)", "zz_btree_b(A)"}},
			},
		},
	})
	require.NoError(t, err)
	require.Equal(t, "data", dataRes.Shape)
	require.Equal(t, "zz_btree_b(A)", dataRes.TypeDefined)
	require.Equal(t, []string{"zz_bleaf_b", "zz_bnode_b"}, dataRes.Consts)
	require.Equal(t, []string{
		"zz_btree_b_induction", "zz_btree_b_recursion",
		"zz_btree_b_injective", "zz_btree_b_distinct"}, dataRes.Derived)
	require.Equal(t, []string{"zz_btree_b_injective", "zz_btree_b_distinct"},
		dataRes.SimpInstalledNames)
	for _, sec := range dataRes.DerivedSections {
		require.True(t, s.sections[sec.Section].root.Proved(),
			"B1: the %s section is proved on return", sec.Kind)
	}

	// B2/B3 — recursive defines over the new carrier; the equation
	// compiler dispatches to the freshly installed zz_btree_b_recursion.
	sizeRes, err := e.Define(&DefineRequest{
		SessionID: info.ID,
		Recursive: &DefineRecursive{
			Name: "zz_bsize_b",
			Type: "zz_btree_b(A) → num",
			Equations: []string{
				"∀a:A. zz_bsize_b(zz_bleaf_b(a)) = 1",
				"∀l r:zz_btree_b(A). zz_bsize_b(zz_bnode_b(l, r)) = zz_bsize_b(l) + zz_bsize_b(r)",
			},
		},
	})
	require.NoError(t, err)
	require.Equal(t, "recursive", sizeRes.Shape)
	require.Equal(t, "zz_btree_b_recursion", sizeRes.Schema)

	mirrorRes, err := e.Define(&DefineRequest{
		SessionID: info.ID,
		Recursive: &DefineRecursive{
			Name: "zz_bmirror_b",
			Type: "zz_btree_b(A) → zz_btree_b(A)",
			Equations: []string{
				"∀a:A. zz_bmirror_b(zz_bleaf_b(a)) = zz_bleaf_b(a)",
				"∀l r:zz_btree_b(A). zz_bmirror_b(zz_bnode_b(l, r)) = zz_bnode_b(zz_bmirror_b(r), zz_bmirror_b(l))",
			},
		},
	})
	require.NoError(t, err)
	require.Equal(t, "zz_btree_b_recursion", mirrorRes.Schema)

	// B4/B5 — the mirror-size theorem; induction dispatches on t's type.
	goal := addGoal("∀t:zz_btree_b(A). zz_bsize_b(zz_bmirror_b(t)) = zz_bsize_b(t)")
	ind := apply(goal, "induction", &TacticReq{Const: "t"})
	require.Len(t, ind.Produced, 2, "B5: one focus per constructor")

	// Identify the foci by their IH count (the template's case order is
	// the sorted-hyp order, not declaration order).
	var leafGoal, nodeGoal string
	for _, g := range ind.Produced {
		node := s.goalIndex[g.GoalID].node
		switch node.Goal.NumHyps() {
		case 0:
			leafGoal = g.GoalID
		case 2:
			nodeGoal = g.GoalID
		}
	}
	require.NotEmpty(t, leafGoal, "B5: a leaf focus with no IH")
	require.NotEmpty(t, nodeGoal, "B5: a node focus with two IHs")

	// B6 — leaf: simp fires bmirror/bsize's leaf equations from the
	// installed set (zero setup); the reflexive residual 1 = 1 closes
	// by simplify. MEASURED revision of the transcript's bare-`simp`
	// line, recorded in its post-listing note — the A4 precedent (the
	// simp set rewrites; it does not run a refl closer).
	leafSimp := apply(leafGoal, "simp", nil)
	require.Len(t, leafSimp.Produced, 1)
	leafClosed := apply(leafSimp.Produced[0].GoalID, "simplify", nil)
	require.Equal(t, "close", leafClosed.Effect, "B6: leaf focus closes")

	// B7 — node: simp rewrites through the mirror/size node equations,
	// then `by` closes from the two IHs plus nat_arith.AddSym.
	nodeSimp := apply(nodeGoal, "simp", nil)
	require.Len(t, nodeSimp.Produced, 1)
	ih0, ih1 := 0, 1
	closed := apply(nodeSimp.Produced[0].GoalID, "by", &TacticReq{
		ByHyps:     []ByHypSpec{{HypIndex: &ih0}, {HypIndex: &ih1}},
		WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddSym"}},
	})
	require.Equal(t, "close", closed.Effect, "B7: node focus closes")

	// Every section in the session is proved before B8.
	for i, sec := range s.sections {
		require.True(t, sec.root.Proved(), "section %d proved", i)
	}

	// B8 — emit. The datatype's sections render (any of the four) as
	// ONE family.DefineData call; the recursive defines as
	// family.Define; the theorem as a family member whose simp leaves
	// cite the define entries and whose dep list carries the
	// datatype's Induct entry (the induction ministep re-resolves its
	// principle by name at replay).
	dataEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: dataRes.DerivedSections[0].Section,
		FuncName: "Build_ZzBtreeB", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	require.Contains(t, dataEmit.Go, "family.DefineData(registry.DataEntry{")
	require.Contains(t, dataEmit.Go, `Type:   "zz_btree_b"`)
	require.Contains(t, dataEmit.Go, `{Name: "zz_bleaf_b", Args: []string{"A"}}`)
	require.Contains(t, dataEmit.Go, `{Name: "zz_bnode_b", Args: []string{"zz_btree_b(A)", "zz_btree_b(A)"}}`)
	require.Contains(t, dataEmit.Go, "Principles: registry.DataPrinciples{",
		"the emitted door spells its derived entries' names — nothing is derived by suffix")
	require.Contains(t, dataEmit.Go, `Induction: "ZzBtreeBInduct"`, "the session's own convention for the name")

	sizeEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: sizeRes.Section,
		FuncName: "Build_ZzBsizeB", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	require.Contains(t, sizeEmit.Go, "family.Define(registry.DefEntry{")
	require.Contains(t, sizeEmit.Go, `"∀a:A. zz_bsize_b(zz_bleaf_b(a)) = 1"`,
		"the equation renders as the author wrote it, not in the printer's form")

	memberEmit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: len(s.sections) - 1,
		FuncName: "Build_BsizeMirror", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	t.Logf("emitted BsizeMirror member:\n%s", memberEmit.Go)
	require.Contains(t, memberEmit.Go, "family.Add(registry.ProofEntry{")
	require.NotContains(t, memberEmit.Go, "TODO",
		"every leaf must classify — the define-installed rules included")
	// The size define is a same-family sibling: its cite is the bare var,
	// never the registered name as a string.
	require.Contains(t, memberEmit.Go, "ZzBsizeB",
		"simp rule children cite the size define's entry by its sibling var")
	require.NotContains(t, memberEmit.Go, `"zz_fam.ZzBsizeB"`)
	require.Contains(t, memberEmit.Go, "ZzBmirrorB",
		"simp rule children cite the mirror define's entry")
	require.NotContains(t, memberEmit.Go, `"zz_fam.ZzBmirrorB"`)
	require.Contains(t, memberEmit.DepNames, "zz_fam.ZzBtreeBInduct",
		"the induction principle rides as the datatype Induct entry's dep")
	// Commutativity of + is nat_arith.AddSym; the cite is declared under
	// its member's registered name.
	require.Contains(t, memberEmit.DepNames, "nat_arith.AddSym")
}
