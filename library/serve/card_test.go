package serve

import (
	"context"
	"testing"

	"google.golang.org/protobuf/proto"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// A card is served as the axiom of its statement: EntryThm hands out
// a realized certificate stating exactly the card, memoized per entry,
// and a member citing the card forces to a certificate standing on
// that axiom with no Build run.
func TestEntryThm_CardIsServedAsItsAxiom(t *testing.T) {
	// The citer's dependency on the card is a recorded one, as a proved
	// member's is: the family blob's dependency row.
	blob, err := proto.MarshalOptions{Deterministic: true}.Marshal(&proof.CNFCache{
		MemberDeps: map[string]*proof.EntryList{"zz_serve_card.Citer": {Names: []string{"zz_serve_card.Lemma"}}},
	})
	if err != nil {
		t.Fatal(err)
	}
	fam := registry.NewFamily("zz_serve_card", blob)
	card := fam.Add(registry.ProofEntry{
		Name:  "Lemma",
		Build: fam.Card("∀P:(bool → bool). ∀a b:bool. a ∧ b ⇒ P(a)", "served as an axiom in this test"),
	})
	corpEnv := env()
	served := EntryThm(corpEnv, card)
	cert := core.Force(context.Background(), core.AsThm(served))
	if cert.IsZero() || !cert.Proved() {
		t.Fatal("the card did not force to a certificate")
	}
	if !cert.AlphaEquals(card.Statement().Prop) {
		t.Fatalf("the card's certificate states %v, not the card's statement %v", cert, card.Statement().Prop)
	}
	if again := EntryThm(corpEnv, card); again != served {
		t.Fatal("a card's axiom is minted once per entry")
	}
	if direct := EntryAxiom(card); !direct.AlphaEquals(card.Statement().Prop) {
		t.Fatalf("EntryAxiom states %v, not the card", direct)
	}

	// A member citing the card: its Build reads the dep off the env
	// the seam prepared, where the card is its axiom.
	citer := fam.Add(registry.ProofEntry{
		Name: "Citer",
		Build: registry.BuildSpec{Headline: "∀P:(bool → bool). ∀a b:bool. a ∧ b ⇒ P(a)", Fn: func(benv *proof.ProverEnv) (proof.Thm, *proof.Proof) {
			dep, ok := benv.LibraryThms[card.Name]
			if !ok {
				t.Fatalf("the card %s is not served to its citer's env", card.Name)
			}
			return core.AsThm(dep), nil
		}},
	})
	citerCert := core.Force(context.Background(), core.AsThm(EntryThm(corpEnv, citer)))
	if citerCert.IsZero() || !citerCert.AlphaEquals(citer.Statement().Prop) {
		t.Fatalf("the citer did not force to its statement through the card's axiom: %v", citerCert)
	}
}
