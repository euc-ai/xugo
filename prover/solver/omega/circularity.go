// Self-circularity gate for Arith bundle dispatch.
//
// Background. `Arith()` is the unified arithmetic ministep — it dispatches
// to whatever bundles (nat / real / int) are installed in this package's
// global pointers. Each bundle CARRIES the corpus theorems it derives
// from: NatLemmaBundle.AddSym holds `⊢ ∀m n. m+n = n+m`, RealLemmaBundle.
// MulSym holds `⊢ ∀x y:real. x*y = y*x`, etc. (~70 nat lemmas, ~25 real,
// growing int.)
//
// Using a bundle to prove a theorem that lives ANYWHERE in the bundle's
// foundation closure (the bundle's fields plus the transitive corpus DAG
// reach of those fields) is circular — the bundle's stored cert IS (or
// transitively uses) the theorem, so Arith would claim "I proved
// MulSym using MulSym (or something MulSym uses)". The
// kernel accepts it because the cert IS valid; the cycle hides in the
// dependency graph.
//
// What this file owns: per-bundle FOUNDATION CLOSURES and compatibility gate
// helpers. Corpus and live proofs use prover.ProofScope, which carries target
// identity lexically through Script/GoalStackNode and passes ArithPolicy into
// omega. The process-global target below is legacy-only.
//
//  1. Bundle pointer (e.g. `natLemmaBundle`) — set by SetNatLemmaBundle.
//     Lives in nat_lemmas.go / real_lemmas.go / int_lemmas.go.
//
//  2. Foundation closure — a `map[core.PropKey]bool` of every theorem
//     key the bundle transitively reaches, in the corpus DAG's key space
//     (a member's own key). Set EXPLICITLY by the install function
//     (serve.Install*Bundle) via SetNatBundleFoundation /
//     SetRealBundleFoundation / SetIntBundleFoundation — not derived by
//     reflecting on each `*prop.PropWrapper` field and taking its
//     `AlphaKey()`. That works ONLY for `lib("X")`-style direct binds
//     (wrapper IS the statement, key matches); it silently MISSES
//     `fromGeneral(g)`-style binds (wrapper holds `core.Promise(g, ...)`
//     whose AlphaKey is the LEAF SHAPE key, not the key the promise
//     forces to). The install site knows the identity by construction:
//     it iterates the bundle, runs `prop.Normalize` on each non-nil
//     field, BFS-closes via `library/integrity/dag.Closure`, and hands
//     the result here. The gate is a single map lookup — no reflection,
//     no per-shape special-casing, and it covers TRANSITIVE circularity
//     (the DAG reach) for free instead of just direct-membership.
//
//     NOTE: the closure handed here by the corpus installs is the RAW
//     dep-edge reach (library/integrity/dag.Closure — the capability
//     edges other proofs use are invisible to it), so these maps gate
//     only the legacy scope-less path below. Scoped callers thread an
//     ArithPolicy computed from prover/proof.ProofScope, which for every
//     witnessed target carries the verdict of the complete manifest graph
//     via the policy witness; see the ProofScope doc comment
//     for the full enforcement chain.
//
//  3. `currentTargetKey` — compatibility state for callers that do not
//     own a ProofScope. Replay and the engine do not set it.
//
// The gate. Each Arith dispatch site (composeArithLeaves / NewArithCtx /
// arithDecideWithHypsRaw in engine.go) calls e.g. `NatBundleAllowsTarget
// (currentTargetKey)`: true unless the target is in this bundle's
// foundation closure. When false, the dispatch site OMITS this bundle's
// leaves from the composed rewrite — Arith CLEANLY DECLINES on those
// leaves (no fabricated placeholder); the other bundles still fire.
//
// New code should use NewArithCtxWithPolicy rather than SetCurrentTarget.

package omega

import (
	"context"

	"github.com/euc-ai/xugo/core"
)

// currentTargetKey is the AlphaKey of the theorem the in-flight Arith
// call is INSIDE the proof of, or "" when no context is active.
// Mutated only via SetCurrentTarget.
var currentTargetKey core.PropKey

// ArithPolicy is the lexical bundle-selection policy for one proof.
type ArithPolicy struct {
	Nat, Real, Int bool
	// Structure admits the structure ring (structure_ring.go): the ring
	// at a resident comm_ring_on, comm_ring or field fact; with
	// StructureInstances it reads the installed instances as well.
	Structure          bool
	StructureInstances bool
	// Modulus admits the installed modulus (modulus.go): its laws as
	// rewrites and its sign beside a decision's hypotheses.
	Modulus bool
	// Stop is the context a decision is cut off by: polled before each
	// leaf the decider calls (composeArithLeavesWithPolicy), it raises a
	// utils.Cut once it is done. It selects no bundle; it is carried
	// here because the policy is the one value every rewrite of a
	// decision is built with, the case splits' recursions included. nil,
	// and a context that is never done, never cut: a replay's decision
	// runs to its end.
	Stop context.Context
}

// modulus reports whether the policy reads an installed modulus.
func (p ArithPolicy) modulus() bool { return p.Modulus && installedModulus != nil }

// realProver is the real atom prover under the policy: with the sign of
// every modulus in sight where the policy reads the modulus, and with
// what the carrier's ring shows of its argument where the policy reads
// that ring (modulus_zero.go). reader is the proof's reading of the
// record equations for the ring's facts.
func (p ArithPolicy) realProver(reader *LibraryReader) proveFn {
	if p.modulus() {
		return modulusProver(realProveDecAtom, p.modulusEvidence(reader))
	}
	return realProveDecAtom
}

// UnscopedArithPolicy preserves SetCurrentTarget semantics for compatibility
// callers which do not own a Script/GoalStackNode scope. "Unscoped" describes
// where the bundle-selection policy comes from; it is independent of the
// current-vs-legacy residual rewrite contract used by the tactic layer.
func UnscopedArithPolicy() ArithPolicy {
	return ArithPolicy{
		Nat:                NatBundleAllowsTarget(currentTargetKey),
		Real:               RealBundleAllowsTarget(currentTargetKey),
		Int:                IntBundleAllowsTarget(currentTargetKey),
		Structure:          StructureBundleAllowsTarget(currentTargetKey),
		StructureInstances: StructureInstancesAllowTarget(currentTargetKey),
		Modulus:            ModulusAllowsTarget(currentTargetKey),
	}
}

// SetCurrentTarget records `key` as the theorem-under-proof for Arith's
// self-circularity gate. Returns a cleanup function that restores the
// previous setting. Idiomatic use is at the top of a replay harness's
// per-entry scope:
//
//	defer omega.SetCurrentTarget(entry.Key)()
//
// so every `Arith()` call inside the member's Build / section forces
// respects the gate. Restore on cleanup composes correctly across nested replays.
func SetCurrentTarget(key core.PropKey) func() {
	prev := currentTargetKey
	currentTargetKey = key
	return func() { currentTargetKey = prev }
}

// CurrentTarget returns the current target key (diagnostic use).
func CurrentTarget() core.PropKey { return currentTargetKey }

// natFoundationKeys / realFoundationKeys / intFoundationKeys carry the
// transitive entry-key closure of each bundle's fields. nil = bundle
// not yet annotated (treated as empty: every target allowed when the
// bundle is installed). Set by SetXBundleFoundation, alongside
// SetXLemmaBundle, from serve.Install*Bundle.
//
// Reads are unsynchronized because writes are install-time (process
// startup) and the gate's hot path is read-only.
var (
	natFoundationKeys  map[core.PropKey]bool
	realFoundationKeys map[core.PropKey]bool
	intFoundationKeys  map[core.PropKey]bool
)

// SetNatBundleFoundation installs the entry-key foundation closure for
// the current NatLemmaBundle. Pass nil to clear. Idempotent. Typically
// called by serve.InstallNatBundle alongside SetNatLemmaBundle.
func SetNatBundleFoundation(keys map[core.PropKey]bool) { natFoundationKeys = keys }

// SetRealBundleFoundation — twin.
func SetRealBundleFoundation(keys map[core.PropKey]bool) { realFoundationKeys = keys }

// SetIntBundleFoundation — twin.
func SetIntBundleFoundation(keys map[core.PropKey]bool) { intFoundationKeys = keys }

// NatBundleAllowsTarget reports whether the gate ALLOWS the nat bundle's
// leaves for `target`. True when target == "" (no scope, production
// path) OR target is NOT in the foundation closure. The nil-bundle case
// returns TRUE here — orthogonal to circularity; the placeholder seam
// (omega/bundle.go) handles "leaf needs bundle field but it's nil"
// at the leaf, panicking in production and using the test stand-in
// otherwise.
func NatBundleAllowsTarget(target core.PropKey) bool {
	if target == "" {
		return true
	}
	return !natFoundationKeys[target]
}

// RealBundleAllowsTarget — twin for the real bundle. Callers nil-check
// `realLemmaBundle` separately (the real dispatch path is gated on bundle
// presence; with no bundle installed the dispatch is a no-op, NOT a
// placeholder candidate — production today installs only the nat bundle).
func RealBundleAllowsTarget(target core.PropKey) bool {
	if target == "" {
		return true
	}
	return !realFoundationKeys[target]
}

// IntBundleAllowsTarget — twin for the int bundle.
func IntBundleAllowsTarget(target core.PropKey) bool {
	if target == "" {
		return true
	}
	return !intFoundationKeys[target]
}
