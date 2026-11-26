package serve

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/stretchr/testify/require"
)

// TestModulusBundle_ItsOwnCapability: ℂ's modulus is installed with the
// structure ring and is a capability of its own. Its roots are
// complex_abs's eleven laws — the sign, the eight rewrites and the two of
// the zero test; each lies in its foundation, so the proof of
// a law is refused the reading the law backs, and none is a root of the
// structure ring's two capabilities. A member that only cites the laws,
// the triangle inequality, lies outside the foundation and may read the
// modulus.
func TestModulusBundle_ItsOwnCapability(t *testing.T) {
	InstallNatBundle()
	InstallStructureRingBundle()
	t.Cleanup(func() {
		omega.SetStructureRingLaws(nil)
		omega.SetStructureInstances(nil)
		omega.SetModulusLaws(nil)
		omega.SetNatLemmaBundle(nil)
	})
	require.True(t, omega.ModulusInstalled())
	specs := proof.DependencyCapabilitySnapshot()
	modulus, ok := specs[proof.CapabilityArithModulus]
	require.True(t, ok)
	laws := entryKeys(
		complex_abs.AbsNonneg, complex_abs.AbsMul, complex_abs.AbsInv, complex_abs.AbsDiv, complex_abs.AbsPow,
		complex_abs.AbsNeg, complex_abs.AbsConj, complex_abs.AbsOfReal, complex_abs.AbsI,
		complex_abs.AbsEqZero, complex_abs.AbsPosIffNonzero)
	require.Len(t, modulus.Roots, len(laws))
	for _, k := range laws {
		require.Contains(t, modulus.Roots, k)
		require.True(t, modulus.Foundation[k], "a law lies outside the foundation of its own capability")
		require.False(t, omega.ModulusAllowsTarget(k), "a law's own proof may read the modulus through it")
		require.NotContains(t, specs[proof.CapabilityArithStructure].Roots, k)
		require.NotContains(t, specs[proof.CapabilityArithStructureInstances].Roots, k)
	}
	consumer := core.PropKey(complex_abs.AbsTriangle.Entry().Key)
	require.False(t, modulus.Foundation[consumer])
	require.True(t, omega.ModulusAllowsTarget(consumer))
}
