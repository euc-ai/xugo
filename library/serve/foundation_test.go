package serve

import (
	"fmt"
	"strings"
	"testing"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

func TestBundleCapabilityRequiresExplicitUnknownFieldIdentity(t *testing.T) {
	type testBundle struct{ Leaf *prop.PropWrapper }
	p := ext.Var("unregistered_bundle_leaf", core.TypeBool())
	bundle := &testBundle{Leaf: prop.WrapProp(core.TestThm(p))}

	func() {
		defer func() {
			if recover() == nil {
				t.Fatal("unresolved bundle field did not fail closed")
			}
		}()
		computeBundleCapability(bundle)
	}()

	roots, closure := computeBundleCapability(bundle, map[string][]core.PropKey{"Leaf": {}})
	if len(roots) != 0 || len(closure) != 0 {
		t.Fatalf("explicit primitive leaf produced theorem dependencies: roots=%v closure=%v", roots, closure)
	}
}

// A law table that stands on a card is refused: where the card is a law
// itself, and where it lies beneath a proved law, in which case the
// refusal names the law that reaches it. A table of proved theorems
// alone passes.
func TestRefuseCardFoundation(t *testing.T) {
	blob, err := proto.MarshalOptions{Deterministic: true}.Marshal(&proof.CNFCache{
		MemberDeps: map[string]*proof.EntryList{"zz_serve_law_card.Law": {Names: []string{"zz_serve_law_card.Lemma"}}},
	})
	if err != nil {
		t.Fatal(err)
	}
	fam := registry.NewFamily("zz_serve_law_card", blob)
	card := fam.Add(registry.ProofEntry{
		Name:  "Lemma",
		Build: fam.Card("∀P:(bool → bool). ∀a b:bool. b ∧ a ⇒ P(b)", "a card beneath a law, in this test"),
	})
	law := fam.Add(registry.ProofEntry{
		Name: "Law",
		Build: registry.BuildSpec{Headline: "∀P:(bool → bool). ∀a b:bool. a ∧ b ⇒ P(b)", Fn: func(*proof.ProverEnv) (proof.Thm, *proof.Proof) {
			t.Fatal("the law is never built in this test")
			return nil, nil
		}},
	})
	cardKey, lawKey := core.PropKey(card.Key), core.PropKey(law.Key)
	if got := registry.CardFrontier(law); len(got) != 1 || got[0] != card.Name {
		t.Fatalf("the fixture's law should stand on its card alone, got %v", got)
	}

	refusal := func(roots []core.PropKey, foundation map[core.PropKey]bool) (message string) {
		defer func() {
			if r := recover(); r != nil {
				message = fmt.Sprint(r)
			}
		}()
		refuseCardFoundation("zz:probe", roots, foundation)
		return ""
	}

	beneath := refusal([]core.PropKey{lawKey}, map[core.PropKey]bool{lawKey: true, cardKey: true})
	if !strings.Contains(beneath, card.Name) || !strings.Contains(beneath, "beneath "+law.Name) {
		t.Fatalf("a card beneath a proved law was not refused by name: %q", beneath)
	}
	asLaw := refusal([]core.PropKey{cardKey}, map[core.PropKey]bool{cardKey: true})
	if !strings.Contains(asLaw, card.Name) {
		t.Fatalf("a card among the laws was not refused by name: %q", asLaw)
	}
	if proved := refusal([]core.PropKey{lawKey}, map[core.PropKey]bool{lawKey: true}); proved != "" {
		t.Fatalf("a table holding no card was refused: %q", proved)
	}
}
