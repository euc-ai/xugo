package omega

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// Probe the self-circularity gate against the public per-bundle API.
// Catches three properties downstream relies on:
//
//  1. Empty target → bundle eligible (production paths unchanged when no
//     context is active).
//  2. Target NOT in foundation → bundle eligible.
//  3. Target IN foundation → bundle refused.
//  4. SetCurrentTarget save/restore composes across nested scopes.
func TestSelfCircularityGate(t *testing.T) {
	mk := func(c core.Term) *prop.PropWrapper { return prop.WrapProp(core.TestThm(c)) }
	wrapA := mk(ext.Var("a", core.TypeBool()).Core())
	wrapB := mk(ext.Var("b", core.TypeBool()).Core())
	keyA := wrapA.AlphaKey()
	keyB := wrapB.AlphaKey()
	keyMiss := core.PropKey("prop_does_not_exist")

	// Install an explicit foundation (no reflection on the bundle — the
	// install site is now the source of truth for the gate map).
	prevFoundation := natFoundationKeys
	SetNatBundleFoundation(map[core.PropKey]bool{keyA: true, keyB: true})
	t.Cleanup(func() { SetNatBundleFoundation(prevFoundation) })

	t.Run("empty target allows", func(t *testing.T) {
		defer SetCurrentTarget("")()
		if !NatBundleAllowsTarget(currentTargetKey) {
			t.Fatal("empty target must allow the nat bundle")
		}
	})
	t.Run("target not in foundation allows", func(t *testing.T) {
		defer SetCurrentTarget(keyMiss)()
		if !NatBundleAllowsTarget(currentTargetKey) {
			t.Fatal("target absent from foundation: bundle should be allowed")
		}
	})
	t.Run("target in foundation refuses", func(t *testing.T) {
		defer SetCurrentTarget(keyA)()
		if NatBundleAllowsTarget(currentTargetKey) {
			t.Fatal("target is in foundation: bundle must be refused")
		}
	})
	t.Run("SetCurrentTarget restore composes", func(t *testing.T) {
		restoreOuter := SetCurrentTarget(keyA)
		if CurrentTarget() != keyA {
			t.Fatalf("outer set: got %q want %q", CurrentTarget(), keyA)
		}
		restoreInner := SetCurrentTarget(keyB)
		if CurrentTarget() != keyB {
			t.Fatalf("inner set: got %q want %q", CurrentTarget(), keyB)
		}
		restoreInner()
		if CurrentTarget() != keyA {
			t.Fatalf("after inner restore: got %q want %q", CurrentTarget(), keyA)
		}
		restoreOuter()
		if CurrentTarget() != "" {
			t.Fatalf("after outer restore: got %q want %q", CurrentTarget(), "")
		}
	})
}
