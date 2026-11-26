package serve

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/chase"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/stretchr/testify/require"
)

// TestChaseBundle_InstallsTheChaptersLaws: the chase closer's table is
// bound from proved chapter theorems, every field set, and its
// capability's foundation holds the entries the laws rest on — the
// coset law and the homomorphism's additivity among them — so a member
// below them may not use the closer.
func TestChaseBundle_InstallsTheChaptersLaws(t *testing.T) {
	InstallNatBundle()
	InstallChaseBundle()
	t.Cleanup(func() {
		chase.SetLaws(nil)
		chase.SetFoundation(nil)
		omega.SetNatLemmaBundle(nil)
	})
	require.True(t, chase.Enabled())
	specs := proof.DependencyCapabilitySnapshot()
	spec, ok := specs[proof.CapabilityChase]
	require.True(t, ok, "the chase capability is not installed")
	for _, k := range entryKeys(group.LeftCosetEqOn, module_homomorphism.HomAdd,
		module_homomorphism.HomSource, module_homomorphism.HomTarget, module.AddGroupOn, module.AddComm, module.SmulIn,
		module.RingOn, module.SmulAddLeft, module.SmulAddRight, module.SmulMul, module.SmulOne, module.ZeroSmul, module.SmulZero, module_homomorphism.HomSmul,
		module_record.RingCarrierDef, module_record.ModCarrierDef,
		chain_complex.ComplexTermsDef, chain_complex.ComplexModuleDef, chain_complex.HomologyModuleDef, chain_complex.HomologyDef,
		module_record.RestrictModuleDef, submodule.QuotientModuleDef, chain_complex.CohomologyModuleDef, chain_complex.CohomologyDef) {
		require.Contains(t, spec.Roots, k)
		require.True(t, spec.Foundation[k])
		require.False(t, chase.AllowsTarget(k), "a law the closer reads may use the closer")
	}
	require.True(t, chase.AllowsTarget("prop_not_in_the_foundation"))
}

// Scalar multiplication is read through both the module's additive-group
// record and its scalar-ring record, with each carrier guard retained.
func TestChaseBundle_RecordScalarAction(t *testing.T) {
	InstallNatBundle()
	InstallChaseBundle()
	t.Cleanup(func() {
		chase.SetLaws(nil)
		chase.SetFoundation(nil)
		omega.SetStructureRingLaws(nil)
		omega.SetStructureInstances(nil)
		omega.SetModulusLaws(nil)
		omega.SetNatLemmaBundle(nil)
	})
	scope := corpusParseScope()
	prefix := "R:ring_ops(A), M:module_ops(A, B), c:A, d:A, x:B, module_on(R, M), x ∈ M.carrier, c ∈ R.carrier, d ∈ R.carrier ⊢ "
	for _, statement := range []string{
		"M.smul(R.add(c, d), x) = M.add(M.smul(c, x), M.smul(d, x))",
		"M.smul(R.mul(c, d), x) = M.smul(d, M.smul(c, x))",
	} {
		parsed := dsl.ParsePropTextInScope(prefix+statement, scope)
		require.Empty(t, parsed.Errors)
		closed, result, err := chase.Close(parsed.Prop, chase.Options{})
		require.NoError(t, err)
		require.NotNil(t, closed, result.Report)
		require.True(t, prop.IsStronger(closed, parsed.Prop))
	}
}
