// zz_recurate_probe_test.go — the single-entry probe for an author
// restructuring a member.
// Mirrors replayOne's env/dep setup for ONE entry, the bundles the
// replay installs among it (installBundles), but does NOT recover
// panics, so a failing edit surfaces with the full stack naming the
// prove function (the harness's subprocess isolation swallows it).
// Combine with XUGO_REPLAY_TRACE=1 for per-step goal states — the
// pair is what makes restructure iteration cheap (~seconds per probe).
//
//	XUGO_RECURATE_PROBE=<NAME> [XUGO_REPLAY_TRACE=1] \
//	 go test ./library/integrity/gates/ -run TestZZRecurateProbe
//
// Skips unless XUGO_RECURATE_PROBE is set. The member's family pb is
// installed warm but non-strict, so the keys already recorded stay
// deterministic and the section being edited runs live; record before
// finishing.
package gates

import (
	"context"
	"os"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve/testenv"
	"github.com/euc-ai/xugo/prover/proof"
)

func TestZZRecurateProbe(t *testing.T) {
	name := os.Getenv("XUGO_RECURATE_PROBE")
	if name == "" {
		t.Skip("set XUGO_RECURATE_PROBE=<NAME>")
	}
	installBundles()
	if os.Getenv("XUGO_REPLAY_TRACE") != "" {
		proof.SetReplayTrace(os.Stderr)
		defer proof.SetReplayTrace(nil)
	}

	entry, found := registry.ByName(name)
	if !found {
		t.Fatalf("%q not in proof registry", name)
	}
	if entry.ServedAsAxiom() {
		t.Skipf("%s is stated without a proof (a card, or the postulate), nothing to replay", name)
	}

	ctx := context.Background()
	depTrust := corpusFrontier()
	depEnv := testenv.MakeT(t)
	deps := entry.DepEntries()
	certs := make([]proof.ThmCert, len(deps))
	for i, dep := range deps {
		cert, err := resolveDep(ctx, depEnv, dep, depTrust)
		if err != nil {
			t.Fatalf("dep %q: %v", dep.Name, err)
		}
		certs[i] = cert
	}

	env := testenv.MakeT(t)
	for i, dep := range deps {
		registry.InstallLibraryDep(env, dep, certs[i])
	}

	// Family member: install the family pb WARM but NON-STRICT — the
	// iteration ergonomics this probe exists for (old keys deterministic,
	// the section you're editing runs live). Record-merge before blessing.
	if family := entry.Family(); family != nil && len(family.CNF) > 0 {
		env.InstallCNFCache(family.CNF)
		env.RequireCNFCacheHit = false
	}

	// Arm proof identity from the entry (Builds read it via
	// NewScriptForEntry).
	env.Scope = proof.NewProofScope(core.PropKey(entry.Key))

	top, proof := entry.Build.Fn(env) // panics propagate with stack
	trust := exceptSelf(depTrust, top)
	for i, s := range proof.SectionThms() {
		if cert, _ := core.ForceWithBoundary(ctx, s, trust); cert.IsZero() {
			t.Fatalf("section %d yielded nil cert", i)
		}
	}
	if cert, _ := core.ForceWithBoundary(ctx, top, trust); cert.IsZero() {
		t.Fatalf("top yielded nil cert")
	}
}
