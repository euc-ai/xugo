package proof

import "testing"

// A RuleSet is flattened in place, its members keeping their own
// orientations; a set nested in a set flattens too, and an empty set
// contributes nothing. A set has no orientation of its own: Fwd and
// Rev take a CiteTarget, which a SimpRule is not.
func TestRuleSetFlattens(t *testing.T) {
	flat := flattenSimpRules([]SimpRule{
		Fwd(depName("a")), RuleSet(Fwd(depName("b")), Rev(depName("c")), RuleSet(Fwd(depName("d")))), RuleSet(), Rev(depName("e")),
	})
	want := []struct {
		name string
		flip bool
	}{{"a", false}, {"b", false}, {"c", true}, {"d", false}, {"e", true}}
	if len(flat) != len(want) {
		t.Fatalf("flattened to %d rules, want %d: %v", len(flat), len(want), flat)
	}
	for i, w := range want {
		got, named := flat[i].fact.target.(depName)
		if !named || string(got) != w.name || flat[i].flip != w.flip {
			t.Fatalf("rule %d: %s flipped %t, want dep %q flipped %t", i, flat[i].fact.describe(), flat[i].flip, w.name, w.flip)
		}
	}
}
