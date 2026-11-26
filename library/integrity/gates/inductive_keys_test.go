package gates

import (
	"testing"

	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// TestInductiveKeys pins the keys of the theorems the inductive door
// derives for finite, is_num and is_recspace — each relation's rules,
// induction and cases — so every citer across the corpus replays against an
// unmoved statement. A door change that moves one of these keys is a
// statement change, and this gate is where it shows first.
func TestInductiveKeys(t *testing.T) {
	byName := func(name string) registry.EntryLike {
		e, ok := registry.ByName(name)
		if !ok {
			t.Fatalf("no entry %s", name)
		}
		return e
	}
	for _, row := range []struct {
		entry registry.EntryLike
		key   string
		row   string
	}{
		{finite_set.FiniteRules, "prop_49ad15a85dc9d731", "the rules of finite"},
		{finite_set.FiniteInduct, "prop_57661b5806f2d762", "the induction of finite"},
		{finite_set.FiniteCases, "prop_965790a1f633e0cc", "the cases of finite"},
		{finite_set.FiniteInductFresh, "prop_d7a990303665c76d", "the induction of finite at a fresh element"},
		{finite_set.FiniteInductStrong, "", "the door's strengthened induction"},
		{byName("peano.isNumRules"), "prop_b9c5203a514489aa", "the rules of is_num"},
		{byName("peano.isNumInduct"), "prop_fa79dd0bfe42a0ba", "the induction of is_num"},
		{byName("peano.isNumCases"), "prop_92149d9a376e20b4", "the cases of is_num"},
		{datatype_universe.UniverseRules, "prop_ef2d23ce70f46fb5", "the rules of is_recspace"},
		{datatype_universe.UniverseInduct, "prop_fc2a343209f99c24", "the induction of is_recspace"},
		{datatype_universe.UniverseCases, "prop_597714c565415d30", "the cases of is_recspace"},
	} {
		e := row.entry.Entry()
		if row.key == "" {
			t.Logf("%s: %s (not pinned: %s)", e.Name, e.Key, row.row)
			continue
		}
		if e.Key != row.key {
			t.Errorf("%s carries key %s, not %s (%s)", e.Name, e.Key, row.key, row.row)
		}
	}
}
