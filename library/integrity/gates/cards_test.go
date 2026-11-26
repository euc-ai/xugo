package gates

import (
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// TestCards checks what a card must be: a member stated without a
// proof (registry.Family.Card) states a closed theorem — no hypotheses,
// since it is served as the axiom ⊢ <statement> — under its family's
// vocabulary, and carries the note its prover reads. The census per
// family is logged: the corpus is sound relative to its cards, and this
// is where their number is read off.
func TestCards(t *testing.T) {
	perFamily := map[string][2]int{}
	cards := 0
	for _, e := range registry.All() {
		fam := e.Family().Name
		counts := perFamily[fam]
		counts[0]++
		if e.IsCard() {
			counts[1]++
			cards++
			if _, panicked := safeStatement(e); panicked != "" {
				t.Errorf("%s: the card's statement does not read: %s", e.Name, panicked)
			} else if e.Statement().Prop.NumHyps() > 0 {
				t.Errorf("%s: a card states a closed theorem — ∀-bind its variables, ⇒ its premises; "+
					"it is served as the axiom ⊢ <statement>", e.Name)
			}
			if e.CardNote() == "" {
				t.Errorf("%s: a card carries a note — why it is a member, what its proof must establish", e.Name)
			}
		}
		perFamily[fam] = counts
	}
	names := make([]string, 0, len(perFamily))
	for fam, counts := range perFamily {
		if counts[1] > 0 {
			names = append(names, fam)
		}
	}
	sort.Strings(names)
	for _, fam := range names {
		t.Logf("%s: %d of %d members are cards", fam, perFamily[fam][1], perFamily[fam][0])
	}
	t.Logf("%d card(s) in %d member(s)", cards, len(registry.All()))
}

// TestNoCardUnderADefinitionalDoor: a definition stands on no card.
// The card frontier walks the dependency graph (DepEntries), and over
// theorem citations the walk is complete by construction: a Build is
// served the certificates of its dependencies and nothing else
// (library/serve's newEntryBuildEnv, the replay harness alike), so a
// proof cites no member its dependencies do not name.
// A definition is reached otherwise. Unfold resolves a constant by name
// through the const meta manager and reads the definition theorem off
// its meta, and a minted type's inhabitation is the logic's own, used
// by every term of the type; a member that unfolds a constant or works
// in a type names no entry for either. So a card under a definitional
// door — a DefineType whose Existence is a card, a WF Define whose
// Termination cites one, a datatype whose derivations read one — would
// stand under every user of the constant or type with the user's
// frontier empty. The gate refuses it at the door: every entry a
// definition door registered has an empty card frontier. The doors are
// recognized by their three markers, since no one field marks them all:
// Definition (Define, DefineData, DefineInductive, DefineQuotient,
// DefineSpec), definesType (DefineType, which sets no shape) and
// defines. Damage-tested: a card added to a Define's Deps fails here.
func TestNoCardUnderADefinitionalDoor(t *testing.T) {
	definitions := 0
	for _, e := range registry.All() {
		if e.Definition == proof.NotADefinition && len(e.Defines()) == 0 && e.DefinesType() == "" {
			continue
		}
		definitions++
		if frontier := registry.CardFrontier(e); len(frontier) > 0 {
			t.Errorf("%s: a definition stands on no card, and this one stands on %s — "+
				"a constant is reached by name and a type by its terms, so a card under this door "+
				"would stand under every user unseen by the frontier; prove the card first, or "+
				"state the definition without it", e.Name, strings.Join(frontier, ", "))
		}
	}
	t.Logf("%d definition entries, none standing on a card", definitions)
}
