package serve

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// TestWarmBundles: every installed bundle field settles under the corpus
// trust frontier — the check that finds a field no corpus theorem backs
// (a field bound to a general form whose normalized key no entry
// carries is unbuildable, and nothing else forces an unconsumed field).
func TestWarmBundles(t *testing.T) {
	installIntForTest(t)
	ctx := context.Background()
	trusted := registry.SomeEntryStates
	// LessEqAdd2 is a fromGeneral field: a fresh root promise at every
	// install, whatever earlier tests forced (a derived field such as
	// LessEqMulMono is already a certificate once its sources are settled
	// in the process).
	natBundle := installedBundles["NatLemmaBundle"].bundle.(*omega.NatLemmaBundle)
	lessEqAdd2 := natBundle.LessEqAdd2.Core().(core.ThmPromise)
	if lessEqAdd2.Proved() {
		t.Fatal("LessEqAdd2 is settled before any warm-up")
	}
	report, err := WarmBundles(ctx, trusted)
	if err != nil {
		t.Fatalf("warm-up: %v", err)
	}
	if report.Forced == 0 || !lessEqAdd2.Proved() {
		t.Fatalf("the warm-up left LessEqAdd2 unsettled: %s", report)
	}
	for _, b := range installedBundles {
		for _, f := range bundleFields(b.bundle, b.overrides) {
			if p, ok := f.wrapper.Core().(core.ThmPromise); ok && !p.Proved() {
				t.Errorf("%s.%s is still unsettled after the warm-up", b.name, f.field)
			}
		}
	}

	// Idempotent: a settled field is counted, not forced again.
	report, err = WarmBundles(ctx, trusted)
	if err != nil || report.Forced != 0 {
		t.Fatalf("second warm-up forced %d fields (err %v)", report.Forced, err)
	}
}
