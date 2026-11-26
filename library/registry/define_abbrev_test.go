package registry

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestFamilyDefine_Abbrev: a definition's equations read under the
// chapter's abbreviation table with the entry's own (DefEntry.Abbrev)
// beneath it, as a member's statement does: the characterizing
// statement is the expanded equation's, the served table is the
// chapter's entries then the entry's own, and an entry spelling a name
// the equation rebinds further in is refused as a capture.
func TestFamilyDefine_Abbrev(t *testing.T) {
	chapter := dsl.Abbrev{{Name: "S", Text: "suc(x)"}}
	fam := NewFamily("zz_define_abbrev", nil).WithAbbrev(chapter)
	own := dsl.Abbrev{{Name: "SS", Text: "suc(«S»)"}}
	entry := fam.Define(DefEntry{
		Name:      "TwiceSucDef",
		Const:     "zz_abbrev_twice_suc",
		Type:      "num → num → bool",
		Abbrev:    own,
		Equations: []string{"∀x y:num. zz_abbrev_twice_suc(x, y) ⇔ «SS» = y ∧ «S» ≤ y"},
	})
	spelled := fam.statementScript().MakePropText("∀x y:num. zz_abbrev_twice_suc(x, y) ⇔ suc(suc(x)) = y ∧ suc(x) ≤ y")
	require.True(t, entry.Statement().Prop.AlphaEquals(spelled),
		"the chapter's entry and the definition's own expand in the equation:\n  %s", entry.StatementText())
	require.Equal(t, append(append(dsl.Abbrev(nil), chapter...), own...), entry.Abbreviations(),
		"the served table is the chapter's entries then the definition's own")

	defer func() {
		r := recover()
		require.NotNil(t, r, "an entry spelling a name the equation rebinds inside is refused")
		require.Contains(t, fmt.Sprint(r), "«Y»")
	}()
	fam.Define(DefEntry{
		Name:      "CaptureDef",
		Const:     "zz_abbrev_capture",
		Type:      "num → bool",
		Abbrev:    dsl.Abbrev{{Name: "Y", Text: "y + x"}},
		Equations: []string{"∀x:num. zz_abbrev_capture(x) ⇔ ∃y:num. «Y» = x"},
	})
	t.Fatal("the capture was not refused")
}
