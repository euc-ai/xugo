// Package testenv constructs a ProverEnv suitable for invoking a
// member's Build (registry.ProofEntry.Build) in tests — the replay and
// CNF-record harnesses under library/integrity/gates.
//
// Self-contained: every constant a proof mentions is an engine
// built-in or the mint of a chapter package the test binary links,
// registered at init in the process-global ConstMetaManager
// (registry.GetConstMetaManager). MakeT wires
// env.ProofService.LoadConstMeta to read from that manager directly.
//
// The env binds no library theorem. Every theorem a Build reads by name
// — a cite, an induction or recursion principle, a served row — is the
// caller's to serve, through env.LibraryResolver or
// registry.InstallLibraryDep, so what a Build reads is what its caller
// served it and nothing else.
//
// (MakeT installs no CNF store: the harness installs the member's family
// store per build — env.InstallCNFStore(family.CNFStore()).)
package testenv

import (
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
)

// MakeT constructs a ProverEnv ready for a member's Build.
func MakeT(t *testing.T) *proof.ProverEnv {
	t.Helper()
	// LoadConstMeta is wired to the process-global ConstMetaManager —
	// the engine's built-ins and the mints of every chapter package the
	// test binary links. A test binary that links no chapter sees only
	// the built-ins, and a proof naming a chapter's constant does not
	// run there.
	mgr := registry.GetConstMetaManager()
	var cnfCache utils.Map[core.TermKey, ext.Prop]
	env := &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        mgr.LoadConstMeta,
			LoadOrStoreConstMeta: mgr.LoadOrStoreConstMeta,
			Syntax:               mgr,
			TypeArity:            mgr.TypeArity,
		},
		// The refuter's ceiling, as the serve's: a refute it does not find
		// in 5 s it does not find with more, and a recorded refute replays
		// with no search.
		CnfRefuterTimeout:     5 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
		LibraryThms:           map[string]core.Thm{},
	}
	return env
}
