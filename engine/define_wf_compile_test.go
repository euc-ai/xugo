package engine

import (
	"github.com/euc-ai/xugo/library/registry"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestCompileWFExistence_Gcd drives the WF equation compiler
// end-to-end at transcript D's definition — parse the COND equation
// and the measure at the strict door, analyze, and compile the
// existence obligation against the REAL served schema rows (wellfounded_recursion /
// wellfounded_measure_less from the corpus, measure_less's definition from the registry's
// const store). The termination theorem is supplied as a test axiom in
// the analyzer's own obligation statement: this test exercises the
// DERIVATION (continuity walker, schema instantiation, transfer); the
// transcript battery proves the obligation for real.
func TestCompileWFExistence_Gcd(t *testing.T) {

	env := testEnv()
	env.ProofService = &proof.ProofService{
		LoadConstMeta:        registry.GetConstMetaManager().LoadConstMeta,
		LoadOrStoreConstMeta: registry.GetConstMetaManager().LoadOrStoreConstMeta,
		Syntax:               registry.GetConstMetaManager(),
	}
	env.LibraryThms = serve.InductionPrinciples()
	serve.RegisterAll(env)

	resolver := func(name string) core.ConstTermMeta {
		if meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(name)); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}
	base := &dsl.ParseScope{ConstResolver: resolver}
	eq, defVar, err := proof.ParseDefinitionEquation(
		"∀m n:num. zz_gcd_wfc(m, n) = COND(n = 0, m, zz_gcd_wfc(n, nat_mod(m, n)))",
		"zz_gcd_wfc", "num → num → num", base)
	require.NoError(t, err)

	mRes := dsl.ParseTermTextInScope("λn:num. n", nil,
		&dsl.ParseScope{ConstResolver: resolver, StrictResolution: true},
		ext.MakeFun(ext.NumType, ext.NumType))
	require.Empty(t, mRes.Errors)

	wfd, err := proof.AnalyzeWFDefinition(eq, defVar, mRes.Term)
	require.NoError(t, err)
	require.Equal(t, 1, wfd.RecArgPos)
	require.Len(t, wfd.CallSites, 1)

	// The obligation, as the author would read it: the guard, then the
	// decrease — nat_mod(m, n) < n.
	obligation := ext.PrintTerm(wfd.Obligation.Conclusion())
	require.Contains(t, obligation, "nat_mod(m, n) < n")

	termination := core.NewAxiom(wfd.Obligation.Conclusion())
	proved, schema, err := proof.CompileWFExistence(env, wfd, termination)
	require.NoError(t, err)
	require.Equal(t, proof.WFRecName, schema)
	require.True(t, proved.AlphaEquals(wfd.ExistsStmt),
		"compiled existence lands in the obligation's own arrangement:\n  got  %s\n  want %s",
		prop.PrintProp(proved), prop.PrintProp(wfd.ExistsStmt))
}
