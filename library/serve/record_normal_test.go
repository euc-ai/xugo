package serve

import (
	"fmt"
	"os"
	"os/exec"
	"slices"
	"sort"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/simplicial/simplex_category" // mints simplex_category and coface_map
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

// TestRecordNormal_ComputesPartsUnderProjections: the instance normal
// form computes a projection at a record's constructor and through a
// definition whose value is a structure, built by a constructor directly
// or through another such definition, and leaves such a definition alone
// outside a projection. A record without a type parameter is a type of
// elements: its part at the constructor is computed, and a projection of
// one of its operations keeps its spelling. The term a matcher computes
// (InstanceNormalTerm) is the right side of the kernel's equation
// (InstanceNormal).
func TestRecordNormal_ComputesPartsUnderProjections(t *testing.T) {
	InstallRecordNormal()
	scope := corpusParseScope()
	for _, c := range []struct{ name, sequent string }{
		{"a projection at the constructor",
			"add:(A → A → A), zero:A, neg:(A → A), mul:(A → A → A), one:A, sub:(A → A → A), c:set(A) ⊢ " +
				"mk_ring(add, zero, neg, mul, one, sub, c).carrier = c"},
		{"through a definition that packs a record",
			"P:complex_ops(A, B), n:num ⊢ complex_module(P, n).carrier = P.terms(n)"},
		{"through two definitions",
			"P:complex_ops(A, B), n:num ⊢ homology_module(P, n).add = set_mul(P.add)"},
		{"a number's part at the constructor",
			"x:real, y:real ⊢ im(complex(x, y)) = y"},
	} {
		t.Run(c.name, func(t *testing.T) {
			parsed := dsl.ParsePropTextInScope(c.sequent, scope)
			require.Empty(t, parsed.Errors)
			lhs, rhs, ok := core.MatchesEQ(parsed.Prop.Conclusion())
			require.True(t, ok)
			require.True(t, tactic.InstanceNormalTerm(lhs).AlphaEquals(rhs), "term form of %s", c.sequent)
			eq := tactic.InstanceNormal(nil)(lhs)
			require.NotNil(t, eq)
			require.True(t, prop.Lhs(eq).AlphaEquals(lhs))
			require.True(t, prop.Rhs(eq).AlphaEquals(rhs), "kernel form of %s", c.sequent)
		})
	}
	t.Run("a projection only a β-reduction exposes", func(t *testing.T) {
		// category_compose(simplex_category, g, f) opens to a λ applied to
		// the coface maps, and the projections of its body are redexes
		// only once that application is reduced: the term form reaches the
		// kernel's form, which merges β with the record steps.
		parsed := dsl.ParsePropTextInScope("n:num, i:num, j:num ⊢ "+
			"category_compose(simplex_category, coface_map(n + 1, j), coface_map(n, i)) = "+
			"category_compose(simplex_category, coface_map(n + 1, i), coface_map(n, j - 1))", scope)
		require.Empty(t, parsed.Errors)
		stated := parsed.Prop.Conclusion()
		eq := tactic.InstanceNormal(nil)(stated)
		require.NotNil(t, eq)
		require.True(t, tactic.InstanceNormalTerm(stated).AlphaEquals(prop.Rhs(eq)),
			"term form %s\nkernel form %s", ext.PrintTerm(tactic.InstanceNormalTerm(stated)), ext.PrintTerm(prop.Rhs(eq)))
	})
	for _, kept := range []string{
		"z:complex, w:complex ⊢ re(z * conj(w)) = &0",
		"z:complex, w:complex ⊢ im(z - w) = &0",
		"c:complex, r:real, t:real ⊢ re(circle_path(c, r, t)) = &0",
	} {
		t.Run("a number's operation under a projection keeps its spelling", func(t *testing.T) {
			parsed := dsl.ParsePropTextInScope(kept, scope)
			require.Empty(t, parsed.Errors)
			concl := parsed.Prop.Conclusion()
			require.True(t, tactic.InstanceNormalTerm(concl).AlphaEquals(concl), "term form of %s", kept)
			require.Nil(t, tactic.InstanceNormal(nil)(concl), "kernel form of %s", kept)
		})
	}
	t.Run("a packed value outside a projection keeps its spelling", func(t *testing.T) {
		parsed := dsl.ParsePropTextInScope("R:ring_ops(A), P:complex_ops(A, B), n:num ⊢ module_on(R, complex_module(P, n))", scope)
		require.Empty(t, parsed.Errors)
		concl := parsed.Prop.Conclusion()
		require.True(t, tactic.InstanceNormalTerm(concl).AlphaEquals(concl))
		require.Nil(t, tactic.InstanceNormal(nil)(concl))
	})
}

// TestRecordNormal_TableIsTheDoors: the table is every record's
// projection equations and every definition whose value is a structure,
// a record over type parameters, and nothing else: no definition into
// ℂ, a record without one.
func TestRecordNormal_TableIsTheDoors(t *testing.T) {
	projections, valued := registry.RecordReductions()
	heads := map[string]bool{}
	for _, p := range projections {
		heads[p.Projection] = true
	}
	for _, h := range []string{"ring_add", "mod_carrier", "complex_ops_terms", "complex_re"} {
		require.True(t, heads[h], "projection %s", h)
	}
	defs := map[string]bool{}
	for _, e := range valued {
		defs[e.Defines()[0]] = true
	}
	for _, d := range []string{"complex_module", "quotient_module", "homology_module", "complex_ring"} {
		require.True(t, defs[d], "structure-valued definition %s", d)
	}
	for _, d := range []string{"homology", "module_on", "complex_abs"} {
		require.False(t, defs[d], "%s builds no record", d)
	}
	for _, d := range []string{"complex_mul", "complex_sub", "complex_of_real", "complex_integral", "circle_path"} {
		require.False(t, defs[d], "%s is arithmetic on a type of elements", d)
	}
}

// TestRecordNormal_ReadingsBuildNoProof: the readings view computes its
// laws in the instance normal form from the record equations'
// statements, so computing them builds no entry's proof. The child is
// this test binary reading the laws of module.RegularModuleOn's
// structure through it — the step every level of the view's walk takes
// — in a fresh process, where no earlier test has computed a reading or
// built an entry; it fails when the record step did not fire
// (module.SmulOne read through module.RegularModuleOn states
// `mk_module(…).carrier` and `mk_module(…).smul` without it) or when an
// entry was built, naming the entries.
func TestRecordNormal_ReadingsBuildNoProof(t *testing.T) {
	if os.Getenv("XUGO_TEST_READINGS_CHILD") != "" {
		InstallRecordNormal()
		readables := registry.ReadableDirectlyThrough(module.RegularModuleOn.Entry())
		i := slices.IndexFunc(readables, func(r registry.Readable) bool { return r.Law == module.SmulOne.Entry() })
		if i < 0 || readables[i].BodyText() != "∀u:A. u ∈ R.carrier ⇒ R.one * u = u" {
			fmt.Fprintln(os.Stderr, "module.SmulOne is not read through module.RegularModuleOn at the ring's own fields")
			os.Exit(1)
		}
		exitIfBuilt("computing the readings view")
		os.Exit(0)
	}
	inFreshProcess(t, "TestRecordNormal_ReadingsBuildNoProof", "XUGO_TEST_READINGS_CHILD")
}

// TestRecordNormal_FallbackBuildsNoProof: a caller that builds no proof
// reads a record equation through the installed fallback as a session
// cites any entry, so the normal form it computes builds no entry's
// proof and hands over a theorem still to be settled. The child is this
// test binary in a fresh process, where no earlier test has built an
// entry; it fails when the record step did not fire, when the equation
// handed over is no promise or is already settled, or when an entry was
// built, naming the entries.
func TestRecordNormal_FallbackBuildsNoProof(t *testing.T) {
	if os.Getenv("XUGO_TEST_FALLBACK_CHILD") != "" {
		InstallRecordNormal()
		parsed := dsl.ParsePropTextInScope("add:(A → A → A), zero:A, neg:(A → A), mul:(A → A → A), one:A, sub:(A → A → A), c:set(A) ⊢ "+
			"mk_ring(add, zero, neg, mul, one, sub, c).carrier = c", corpusParseScope())
		lhs, rhs, ok := core.MatchesEQ(parsed.Prop.Conclusion())
		if len(parsed.Errors) > 0 || !ok {
			fmt.Fprintln(os.Stderr, "the projection equation does not parse:", parsed.Errors)
			os.Exit(1)
		}
		eq := tactic.InstanceNormal(nil)(lhs)
		if eq == nil || !prop.Rhs(eq).AlphaEquals(rhs) {
			fmt.Fprintln(os.Stderr, "the record step did not compute mk_ring(…).carrier")
			os.Exit(1)
		}
		if !core.IsPromised(eq.Core()) || eq.Core().Proved() {
			fmt.Fprintln(os.Stderr, "the fallback handed over no unsettled promise")
			os.Exit(1)
		}
		exitIfBuilt("reading the record equation through the fallback")
		os.Exit(0)
	}
	inFreshProcess(t, "TestRecordNormal_FallbackBuildsNoProof", "XUGO_TEST_FALLBACK_CHILD")
}

// TestRecordNormal_SimpResidualReadsStatements: Simp's residual is a
// statement, so the rewrite that computes it reads the record equations
// as statements and never through the fallback. The child installs the
// corpus's equations with a fallback that panics, then computes the
// residual of a rule whose rewrite exposes a projection at a record's
// constructor.
func TestRecordNormal_SimpResidualReadsStatements(t *testing.T) {
	if os.Getenv("XUGO_TEST_SIMP_RESIDUAL_CHILD") != "" {
		equations, definitions, _ := recordEquations()
		tactic.InstallRecordNormal(equations, definitions, func(name string) *prop.PropWrapper {
			panic("the record equation " + name + " was read through the fallback")
		})
		scope := corpusParseScope()
		decls := "add:(A → A → A), zero:A, neg:(A → A), mul:(A → A → A), one:A, sub:(A → A → A), c:set(A), x:A, h:(set(A) → set(A)) ⊢ "
		goal := dsl.ParsePropTextInScope(decls+"x ∈ h(c)", scope)
		rule := dsl.ParsePropTextInScope(decls+"∀s:set(A). h(s) = mk_ring(add, zero, neg, mul, one, sub, s).carrier", scope)
		want := dsl.ParsePropTextInScope(decls+"x ∈ c", scope)
		if len(goal.Errors)+len(rule.Errors)+len(want.Errors) > 0 {
			fmt.Fprintln(os.Stderr, "the sequents do not parse:", goal.Errors, rule.Errors, want.Errors)
			os.Exit(1)
		}
		residual := proof.SimpResidual(goal.Prop, nil, []core.Prop{rule.Prop}, []bool{false})
		if residual == nil || !residual.AlphaEquals(want.Prop) {
			fmt.Fprintf(os.Stderr, "the residual is %v, not x ∈ c\n", residual)
			os.Exit(1)
		}
		os.Exit(0)
	}
	inFreshProcess(t, "TestRecordNormal_SimpResidualReadsStatements", "XUGO_TEST_SIMP_RESIDUAL_CHILD")
}

// corpusParseScope parses a sequent against the corpus's constants and
// syntax.
func corpusParseScope() *dsl.ParseScope {
	mgr := registry.GetConstMetaManager()
	return &dsl.ParseScope{
		ConstResolver: func(name string) core.ConstTermMeta {
			if meta, ok := mgr.LoadConstMeta(core.TermName(name)); ok {
				return meta
			}
			return core.ConstTermMeta{}
		},
		Syntax:       mgr,
		TypeResolver: mgr.TypeArity,
	}
}

// inFreshProcess runs the test named test in a child process of this
// test binary, with the environment variable child set, and fails with
// the child's output when it exits non-zero.
func inFreshProcess(t *testing.T, test, child string) {
	t.Helper()
	cmd := exec.Command(os.Args[0], "-test.run=^"+test+"$")
	cmd.Env = append(os.Environ(), child+"=1")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("%v\n%s", err, out)
	}
}

// exitIfBuilt exits the child process with status 1, naming the entries,
// when what the child did built any entry's proof.
func exitIfBuilt(what string) {
	built := entriesBuilt()
	if len(built) == 0 {
		return
	}
	names := make([]string, 0, len(built))
	for name := range built {
		names = append(names, name)
	}
	sort.Strings(names)
	fmt.Fprintf(os.Stderr, "%s built %d entries: %v\n", what, len(names), names)
	os.Exit(1)
}
