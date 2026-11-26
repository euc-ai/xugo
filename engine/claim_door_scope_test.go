package engine

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
)

// TestClaimDoor_ReadsAClaimBesideTheGoalsOwnVariables: the Go claim door
// reads a claim with the variables of the block's goal and the block's
// surface names in scope, as the session's claim door reads it with the
// goal's — not with every variable the script has registered. The
// script declares a ring R₀ no goal of this theorem mentions (what
// another section's strips declare in a family.Sections member); the
// claim spells `*` at the theorem's own ring S, which the goal's
// resident ring fact binds alone. Read beside R₀ the symbol is bound by
// two structures.
func TestClaimDoor_ReadsAClaimBesideTheGoalsOwnVariables(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	fam, ok := registry.FamilyByName("algebra/field/field")
	require.True(t, ok)
	env := trustedCorpusEnv(t)
	ctx := fam.NewScript(env)
	ctx.Var("R_0", ext.MakeType("ring_ops", core.MakeVarType("A")))
	var sec *proof.GoalStackNode
	require.NotPanics(t, func() {
		sec = ctx.Theorem("∀S:ring_ops(A). comm_ring(S) ⇒ ∀y:A. S.zero * (y * y) = S.zero", func(a *proof.Argument) {
			a.Fix()
			ring := a.Assume()
			a.Fix()
			a.Show("the left zero law at y * y", proof.By(comm_ring.MulLeftZero.Read(ring)))
		})
	}, "the theorem without a claim, the control")
	require.True(t, sec.Proved())
	require.NotPanics(t, func() {
		sec = ctx.Theorem("∀S:ring_ops(A). comm_ring(S) ⇒ ∀y:A. S.zero * (y * y) = S.zero", func(a *proof.Argument) {
			a.Fix()
			ring := a.Assume()
			a.Fix()
			zero := a.Have("zero absorbs y on the left", "S.zero * y = S.zero", proof.By(comm_ring.MulLeftZero.Read(ring)))
			_ = zero
			a.Show("and y * y", proof.By(comm_ring.MulLeftZero.Read(ring)))
		})
	}, "a claim at the theorem's own ring, beside the script's R₀")
	require.True(t, sec.Proved())
}

// trustedCorpusEnv is the env an emitted member replays in
// (replayEmittedTest): the bundles installed and every registered
// statement served by its name, trusted, for a Script built in the test.
func trustedCorpusEnv(t *testing.T) *proof.ProverEnv {
	t.Helper()
	boundary := registry.SomeEntryStates
	ctx := context.Background()
	serve.InstallProofPolicy()
	installTestNatBundle()
	installTestRealBundle()
	serve.InstallIntBundle()
	serve.InstallStructureRingBundle()
	serve.InstallChaseBundle()
	serve.InstallRecordNormal()
	_, err := serve.WarmBundles(ctx, boundary)
	require.NoError(t, err)
	env := serve.NewSeedEnv()
	env.LibraryResolver = func(name string) (proof.Thm, bool) {
		e, ok := registry.ByName(name)
		if !ok {
			e, ok = registry.ByServesAs(name)
		}
		if !ok {
			return nil, false
		}
		if e.ServedAsAxiom() {
			return serve.EntryAxiom(e), true
		}
		stated := core.Promise(e.Statement().Prop, func(core.Forcer) core.ThmCert {
			panic("every registered statement is trusted, so no dependency is built: " + e.Name)
		})
		cert, _ := core.ForceWithBoundary(ctx, stated, boundary)
		return cert, !cert.IsZero()
	}
	env.Scope = proof.NewProofScope("")
	return env
}
