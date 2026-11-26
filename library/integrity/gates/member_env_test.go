// member_env_test.go — the one env both harnesses build an entry in
// (newEntryEnv, replay_test.go).

package gates

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/tactic"
)

// TestMemberEnv_ServesTheCuratedInductionPrinciple: the env a member
// is built in serves `list_induction` as the REGISTERED principle's own
// statement — the member's `Induction` dep, read by the name the door
// gives it (ServesAs), with no testenv axiom and no harness overlay
// behind it — under both harnesses, because both build the env through
// newEntryEnv, and as the serve binds it for a session.
//
// The names matter, not only the theorem: an induction step's
// constructor arguments are minted off the principle's own binders, so
// the two harnesses agree about what a step's head is called exactly
// when they serve one principle. Before newEntryEnv existed the recorder
// served testenv's axiom and minted the head `aʹ` where the replay,
// which overlaid the curated principle, minted `a0`; a refuter key at a
// leaf mentioning the head was then recorded under one name and
// demanded under the other. This pins the printed form, which is
// name-sensitive where α-equality is not.
func TestMemberEnv_ServesTheCuratedInductionPrinciple(t *testing.T) {
	installBundles()
	member, ok := registry.ByName("list.Cases")
	if !ok {
		t.Skip("datatypes/list is not in this build")
	}
	principle, ok := registry.ByName("list.Induction")
	if !ok {
		t.Skip("list.Induction is not in this build")
	}
	env, _ := newEntryEnv(t, context.Background(), member, corpusFrontier(), servedDeps(member))
	served, ok := env.LookupLibraryThm("list_induction")
	if !ok {
		t.Fatal("the member env serves no list_induction at all")
	}
	if prop.BridgeNormalize(tactic.ListInductProp(), principle.Statement().Prop) == nil {
		t.Fatal("list.Induction's statement does not bridge to the analyzer's spelling")
	}
	want := principle.Statement().Prop
	if got, exp := prop.PrintProp(served), prop.PrintProp(want); got != exp {
		t.Fatalf("the member env serves list_induction as\n  %s\nand the registered principle reads\n  %s\n"+
			"— a step's constructor arguments are minted off these binders, so record and replay would name them differently",
			got, exp)
	}
}
