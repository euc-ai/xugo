package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/library/registry"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestShapeBattery_Curried is the curried-parameter shapes' acceptance
// instrument: six recursive definitions — an ADD, an APPEND and an
// accumulator (v1.1a: recursion argument first, curried extras, the
// extra argument changing in the recursive call); a SUB, an EXP and a
// MAP (v1.1b: argument reshuffle) — each compiling through the
// `define` RPC with the equations exactly as the mathematics spells
// them (no manual reordering, no hand-currying), each characterizing
// theorem the author's equations themselves, in the author's argument
// order.
//
// The identity check is mechanical: the characterizing statement and
// the conjunction of the equations as spelled are compared through
// clausalNorm — per-conjunct ∀-closure + Normalize, applied
// identically to both sides. Because the statement's own argument
// spelling survives normalization, a compiler that leaked the
// canonical argument order would produce a DIFFERENT theorem and
// fail here.
func TestShapeBattery_Curried(t *testing.T) {
	env := testEnv()
	mgr := registry.GetConstMetaManager()
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        mgr.LoadConstMeta,
		LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
		Syntax:               mgr,
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

	shapes := []struct {
		name      string // the shape's name (the subtest)
		twin      string // the constant this battery mints
		typ       string
		schema    string
		equations []string
	}{
		// v1.1a — recursion argument first, curried extra parameters.
		{"ADD", "zz_add_b", "num → num → num", "num_recursion", []string{
			"∀n:num. zz_add_b(0, n) = n",
			"∀m n:num. zz_add_b(suc(m), n) = suc(zz_add_b(m, n))",
		}},
		{"APPEND", "zz_append_b", "list(A) → list(A) → list(A)", "list_recursion", []string{
			"∀l:list(A). zz_append_b(nil, l) = l",
			"∀h:A. ∀t l:list(A). zz_append_b(cons(h, t), l) = cons(h, zz_append_b(t, l))",
		}},
		// The accumulator class: the extra argument CHANGES in the
		// recursive call.
		{"ACCUMULATE", "zz_acc_b", "num → num → num", "num_recursion", []string{
			"∀a:num. zz_acc_b(0, a) = a",
			"∀n a:num. zz_acc_b(suc(n), a) = zz_acc_b(n, suc(a))",
		}},
		// v1.1b — the recursion argument is not first: the reshuffle.
		{"SUB", "zz_sub_b", "num → num → num", "num_recursion", []string{
			"∀m:num. zz_sub_b(m, 0) = m",
			"∀m n:num. zz_sub_b(m, suc(n)) = predecessor(zz_sub_b(m, n))",
		}},
		{"EXP", "zz_exp_b", "num → num → num", "num_recursion", []string{
			"∀m:num. zz_exp_b(m, 0) = 1",
			"∀m n:num. zz_exp_b(m, suc(n)) = m * zz_exp_b(m, n)",
		}},
		{"MAP", "zz_map_b", "(A → B) → list(A) → list(B)", "list_recursion", []string{
			"∀f:A → B. zz_map_b(f, nil) = nil",
			"∀f:A → B. ∀h:A. ∀t:list(A). zz_map_b(f, cons(h, t)) = cons(f(h), zz_map_b(f, t))",
		}},
	}

	for _, sh := range shapes {
		t.Run(sh.name, func(t *testing.T) {
			res, err := e.Define(&DefineRequest{
				SessionID: info.ID,
				Recursive: &DefineRecursive{
					Name: sh.twin, Type: sh.typ, Equations: sh.equations,
				},
			})
			require.NoError(t, err, "define %s as spelled", sh.twin)
			require.Equal(t, "recursive", res.Shape)
			require.Equal(t, sh.schema, res.Schema)
			require.Equal(t, 2, res.SimpInstalled, "both clauses install as simp rules")

			characterizing := s.sections[res.Section].root.Goal
			requireStatesEquations(t, sh.twin, sh.equations, characterizing)
		})
	}

	// The emitted form of a reshuffled define carries the author-order
	// equation strings (one per clause) — the DefEntry round-trip.
	subSection := -1
	for i, sec := range s.sections {
		if c := s.sections[i].root; c != nil && sec.root.Goal != nil {
			if termMentionsConstName(sec.root.Goal.Conclusion(), "zz_sub_b") {
				subSection = i
				break
			}
		}
	}
	require.GreaterOrEqual(t, subSection, 0, "the SUB twin's section exists")
	emit, err := e.EmitSection(&EmitSectionRequest{
		SessionID: info.ID, Section: subSection,
		FuncName: "Build_CSub", Family: "zz_fam", IncludePrior: []int{},
	})
	require.NoError(t, err)
	require.Contains(t, emit.Go, "family.Define(registry.DefEntry{")
	require.Contains(t, emit.Go, "zz_sub_b(m, 0) = m",
		"the emitted equations keep the author's argument order")
}

// requireStatesEquations checks the definition's characterizing
// statement IS the conjunction of its equations as the author spelled
// them, compared through clausalNorm.
func requireStatesEquations(t *testing.T, name string, equations []string, characterizing core.Prop) {
	t.Helper()
	require.NotNil(t, characterizing)
	// Each equation parses on its own — its type letters are its own —
	// over the registered constants (the minted one included), and the
	// clauses are conjoined as terms. The characterizing statement is no
	// scope for it: a goal's scope fixes each constant at the one
	// instance it mentions.
	var conj core.Term
	for _, eq := range equations {
		clause, err := parsePropTextInGoalScope(eq, prop.MakeProp(ext.T), nil)
		require.NoError(t, err, "the %s equation %q parses", name, eq)
		if conj == nil {
			conj = clause.Conclusion()
			continue
		}
		conj = ext.And(ext.WrapTerm(conj), ext.WrapTerm(clause.Conclusion())).Core()
	}
	mine := clausalNorm(core.MakeProp(characterizing.Conclusion()))
	want := clausalNorm(core.MakeProp(conj))
	if mine.AlphaKey() != want.AlphaKey() {
		t.Logf("equations %s canonical:      %s", name, ext.PrintTerm(want.Conclusion()))
		t.Logf("characterizing %s canonical: %s", name, ext.PrintTerm(mine.Conclusion()))
	}
	require.Equal(t, want.AlphaKey(), mine.AlphaKey(),
		"the %s characterizing statement must BE its equations as spelled "+
			"(author argument order included)", name)
}

// clausalNorm is the comparison canonicalization: per-conjunct
// ∀-closure — outer and per-clause ∀s stripped, each ∧-conjunct
// re-closed over its OWN free variables — then Normalize. The first
// step removes the one residual Normalize does not canonicalize
// between two documents of a defining conjunction: one closing its
// variables ONCE over the whole ∧, the other closing per clause — the
// same theorem by ∀/∧ distribution, distinct normalized keys when the
// binder types mix. Both sides pass through this same function, so
// the check stays symmetric and mechanical.
func clausalNorm(p core.Prop) core.Prop {
	_, matrix := ext.DecomposesFORALL(p.Conclusion())
	conjuncts := ext.DecomposesAND(matrix)
	closed := make([]core.Term, len(conjuncts))
	for i, cj := range conjuncts {
		_, body := ext.DecomposesFORALL(cj)
		out := body
		frees := body.Frees(nil)
		for j := len(frees) - 1; j >= 0; j-- {
			out = ext.ForAll(frees[j])(ext.WrapTerm(out)).Core()
		}
		closed[i] = out
	}
	rebuilt := closed[len(closed)-1]
	for i := len(closed) - 2; i >= 0; i-- {
		rebuilt = ext.And(ext.WrapTerm(closed[i]), ext.WrapTerm(rebuilt)).Core()
	}
	norm, _ := prop.Normalize(core.MakeProp(rebuilt))
	return norm
}

// termMentionsConstName reports whether the term contains a constant
// with the given name.
func termMentionsConstName(t core.Term, name string) bool {
	if c, ok := t.AsConst(); ok {
		return string(c.Name()) == name
	}
	if app, ok := t.AsAppliedTerm(); ok {
		return termMentionsConstName(app.Fun(), name) ||
			termMentionsConstName(app.Arg(), name)
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return termMentionsConstName(abs.Body(), name)
	}
	return false
}
