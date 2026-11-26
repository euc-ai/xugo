// mint_door_test.go — every constant a chapter mints goes through a
// define door.
//
// The constitution's §"Definitions: a chapter mints its own constants"
// names the doors (family.Define, DefineType, DefineData, DefineSpec,
// DefineInductive, DefineStructure) as the way a chapter puts a
// constant into the corpus: the equation is read in the chapter's
// vocabulary, the kernel mints the constant, and a registered entry
// carries the characterizing statement — what a session bound to the
// family installs as a use rule, what the corpus index lists as the
// definition, what a proof cites to unfold. A constant stored straight
// into the constant manager (ext.ConstDef through a chapter's own
// publish helper) is kernel-sound and invisible to all three.
//
// The constant manager records where every chapter-minted meta was
// stored from (registry.ConstMetaManager.MintSource, read off the
// call stack); the doors record what they minted
// (registry.ProofEntry.Defines). This gate demands the two agree: a
// mint with no door entry fails, naming the file and line that
// stored it.

package gates

import (
	"sort"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"
)

func TestEveryMintIsADoor(t *testing.T) {
	doored := map[string]string{}
	for _, e := range registry.All() {
		for _, name := range e.Defines() {
			doored[name] = e.Name
		}
	}
	var stray []string
	registry.GetConstMetaManager().RangeMintSources(func(name core.TermName, source string) bool {
		if _, ok := doored[string(name)]; !ok {
			stray = append(stray, string(name)+" minted at "+source)
		}
		return true
	})
	sort.Strings(stray)
	for _, s := range stray {
		t.Errorf("constant %s — not through a define door (family.Define / DefineType / DefineData / DefineSpec / DefineInductive / DefineStructure)", s)
	}
}
