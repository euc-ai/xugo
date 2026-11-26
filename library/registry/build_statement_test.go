// build_statement_test.go — the constructors' statement argument in
// parts (dsl.Statement): the headline assembled from the parts, the
// parts and the table kept on the BuildSpec, and the refusals.
package registry

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

func TestHeadlineSpec_StatementInParts(t *testing.T) {
	stmt := dsl.Statement{
		Binders:    "∀m n:num.",
		Hypotheses: []string{"m ∣ n", "«dvd»"},
		Conclusion: "m = n",
		Abbrev:     dsl.Abbrev{{Name: "dvd", Text: "n ∣ m"}},
	}
	spec := headlineSpec("Theorem", stmt)
	assert.Equal(t, "∀m n:num. m ∣ n ∧ «dvd» ⇒ m = n", spec.Headline)
	require.NotNil(t, spec.Statement)
	assert.Equal(t, stmt, *spec.Statement)
	assert.Equal(t, stmt.Abbrev, spec.abbrev.own)
	assert.Nil(t, spec.Abbreviations(), "the table is bound when the member registers")
	assert.Equal(t, map[string]bool{"m": true, "n": true}, spec.abbrev.binders)
	spec.bindChapter(NewFamily("zz_headline_spec", nil), "zz_headline_spec.Parts")
	assert.Equal(t, stmt.Abbrev, spec.Abbreviations())

	plain := headlineSpec("Card", "∀m n:num. m ∣ n ∧ n ∣ m ⇒ m = n")
	assert.Equal(t, "∀m n:num. m ∣ n ∧ n ∣ m ⇒ m = n", plain.Headline)
	assert.Nil(t, plain.Statement)
	assert.Nil(t, plain.Abbreviations())
	assert.Equal(t, map[string]bool{"m": true, "n": true}, plain.abbrev.binders)
}

func TestHeadlineSpec_Refusals(t *testing.T) {
	assert.PanicsWithValue(t,
		"registry.Theorem: the statement is a string or a Statement{Binders, Hypotheses, Conclusion, Abbrev}, not int",
		func() { headlineSpec("Theorem", 3) })
	assert.Panics(t, func() { headlineSpec("Card", dsl.Statement{Binders: "∀m:num."}) }, "no Conclusion")
	assert.Panics(t, func() {
		bad := headlineSpec("Card", dsl.Statement{Conclusion: "p", Abbrev: dsl.Abbrev{{Name: "R", Text: "p ∧"}}})
		bad.bindChapter(NewFamily("zz_headline_refusal", nil), "x")
	}, "an abbreviation that does not parse")
}

// A card and a theorem stated in parts register as the statement the
// parts assemble to, the abbreviations expanded, and serve the parts
// to the doors that render a member as written.
func TestFamily_StatementInPartsRegisters(t *testing.T) {
	fam := NewFamily("zz_statement_parts", nil)
	card := fam.Add(ProofEntry{
		Name: "Card",
		Build: fam.Card(dsl.Statement{
			Binders:    "∀x:num.",
			Hypotheses: []string{"«S» = x"},
			Conclusion: "x = 0",
			Abbrev:     dsl.Abbrev{{Name: "S", Text: "suc(x)"}},
		}, "a card in parts"),
	})
	assert.Equal(t, "∀x:num. «S» = x ⇒ x = 0", card.Build.Headline)
	assert.Equal(t, "∀x:num. «S» = x ⇒ x = 0", card.StatementText())
	assert.Equal(t, dsl.Abbrev{{Name: "S", Text: "suc(x)"}}, card.Abbreviations())
	require.NotNil(t, card.StatementParts())
	expanded := fam.statementScript().MakePropText("∀x:num. suc(x) = x ⇒ x = 0")
	assert.True(t, card.Statement().Prop.AlphaEquals(expanded), "the registered statement is the expansion")
	assert.Equal(t, KeyOf(expanded), card.Statement().Key())
}

// A chapter's table (Family.WithAbbrev) is the outer table of every
// member: a member in parts spells the chapter's names and declares
// only its own, a member stated as one string spells them too, the
// served table is the chapter's entries then the member's, and a name
// both declare is refused.
func TestFamily_WithAbbrevIsTheOuterTable(t *testing.T) {
	chapter := dsl.Abbrev{{Name: "S", Text: "suc(x)"}, {Name: "SS", Text: "suc(«S»)"}}
	fam := NewFamily("zz_chapter_abbrev", nil).WithAbbrev(chapter)
	assert.Equal(t, chapter, fam.Abbrev())
	assert.Panics(t, func() { fam.WithAbbrev(chapter) }, "declared once")
	assert.Panics(t, func() { NewFamily("zz_chapter_abbrev_empty", nil).WithAbbrev(nil) }, "an empty table")

	parts := fam.Add(ProofEntry{
		Name: "Parts",
		Build: fam.Card(dsl.Statement{
			Binders:    "∀x:num.",
			Hypotheses: []string{"«SS» = «T»"},
			Conclusion: "x = 0",
			Abbrev:     dsl.Abbrev{{Name: "T", Text: "«S» + x"}},
		}, "a card under the chapter's table"),
	})
	expanded := fam.statementScript().MakePropText("∀x:num. suc(suc(x)) = suc(x) + x ⇒ x = 0")
	assert.True(t, parts.Statement().Prop.AlphaEquals(expanded), "the chapter's entries expand in the member's")
	assert.Equal(t, append(append(dsl.Abbrev(nil), chapter...), dsl.Abbreviation{Name: "T", Text: "«S» + x"}), parts.Abbreviations(),
		"the served table is the chapter's then the member's own")
	assert.Equal(t, dsl.Abbrev{{Name: "T", Text: "«S» + x"}}, parts.StatementParts().Abbrev, "the author's literal holds its own alone")

	str := fam.Add(ProofEntry{
		Name:  "String",
		Build: fam.Card("∀x:num. «SS» = x ⇒ x = 0", "a string card spelling the chapter's name"),
	})
	assert.True(t, str.Statement().Prop.AlphaEquals(fam.statementScript().MakePropText("∀x:num. suc(suc(x)) = x ⇒ x = 0")))
	assert.Equal(t, chapter, str.Abbreviations())
	assert.Nil(t, str.StatementParts())

	assert.PanicsWithValue(t,
		`proof registry: zz_chapter_abbrev.Twice: abbreviation «S» is declared twice: by the table this one is read under, and here — one name, one meaning`,
		func() {
			fam.Add(ProofEntry{
				Name:  "Twice",
				Build: fam.Card(dsl.Statement{Binders: "∀x:num.", Conclusion: "x = 0", Abbrev: dsl.Abbrev{{Name: "S", Text: "x"}}}, "a redeclaration"),
			})
		})

	// A member stated through a structure door declared in another
	// chapter reads under the chapter it registers in.
	other := NewFamily("zz_chapter_abbrev_other", nil)
	door := other.Card("∀x:num. «SS» = x ⇒ x = 0", "a spec another family's constructor built")
	assert.Nil(t, door.Abbreviations(), "unbound until it registers")
	bound := fam.Add(ProofEntry{Name: "Bound", Build: door})
	assert.Equal(t, chapter, bound.Abbreviations())
	assert.True(t, bound.Statement().Prop.AlphaEquals(fam.statementScript().MakePropText("∀x:num. suc(suc(x)) = x ⇒ x = 0")))
}

// A chapter cut from another reads that chapter's table before
// declaring its own (Family.WithOuterAbbrev): the read entries are in
// scope for its members, its own are read under them, and what it
// exports (ChapterAbbrev) carries both, so a chapter cut from it reads
// through. An entry two of the tables read hold is read once. A chapter
// without a table exports none; a name the tables read give two texts,
// a name the chapter's own table declares again, a read declared after
// the own table or twice, and a read naming no table are refused.
func TestFamily_WithOuterAbbrevReadsAnotherChapter(t *testing.T) {
	outer := NewFamily("zz_outer_abbrev", nil).WithAbbrev(dsl.Abbrev{{Name: "S", Text: "suc(x)"}})
	assert.PanicsWithValue(t, "registry.ChapterAbbrev(zz_outer_abbrev_none): the chapter declares no table",
		func() { NewFamily("zz_outer_abbrev_none", nil).ChapterAbbrev() })

	inner := NewFamily("zz_inner_abbrev", nil).WithOuterAbbrev(outer.ChapterAbbrev()).WithAbbrev(dsl.Abbrev{{Name: "SS", Text: "suc(«S»)"}})
	assert.Equal(t, dsl.Abbrev{{Name: "S", Text: "suc(x)"}, {Name: "SS", Text: "suc(«S»)"}}, inner.Abbrev(), "the read entries, then the own")
	assert.Equal(t, dsl.Abbrev{{Name: "SS", Text: "suc(«S»)"}}, inner.AbbrevOwn())
	assert.Equal(t, []string{"zz_outer_abbrev"}, inner.AbbrevOuter())
	member := inner.Add(ProofEntry{Name: "Member", Build: inner.Card("∀x:num. «SS» = «S» ⇒ x = 0", "a card spelling both tables")})
	assert.True(t, member.Statement().Prop.AlphaEquals(inner.statementScript().MakePropText("∀x:num. suc(suc(x)) = suc(x) ⇒ x = 0")))
	assert.Equal(t, inner.Abbrev(), member.Abbreviations(), "the served table is the whole of what the member reads")

	third := NewFamily("zz_third_abbrev", nil).WithOuterAbbrev(inner.ChapterAbbrev())
	assert.Equal(t, inner.Abbrev(), third.Abbrev(), "a chapter reads through the chapter it reads under")
	assert.Nil(t, third.AbbrevOwn(), "a chapter may declare nothing of its own")
	assert.Equal(t, []string{"zz_inner_abbrev"}, third.AbbrevOuter())

	assert.PanicsWithValue(t,
		"registry.WithAbbrev(zz_clash_abbrev): abbreviation «S» is declared twice: by the table this one is read under, and here — one name, one meaning",
		func() {
			NewFamily("zz_clash_abbrev", nil).WithOuterAbbrev(outer.ChapterAbbrev()).WithAbbrev(dsl.Abbrev{{Name: "S", Text: "x"}})
		})
	// An entry reached through two of the tables read is read once: a
	// chapter and one cut from it, and two chapters cut from one parent.
	both := NewFamily("zz_both_abbrev", nil).WithOuterAbbrev(outer.ChapterAbbrev(), inner.ChapterAbbrev())
	assert.Equal(t, inner.Abbrev(), both.Abbrev(), "the parent's entry once, then the child's own")
	assert.Equal(t, []string{"zz_outer_abbrev", "zz_inner_abbrev"}, both.AbbrevOuter())
	sibling := NewFamily("zz_sibling_abbrev", nil).WithOuterAbbrev(outer.ChapterAbbrev()).WithAbbrev(dsl.Abbrev{{Name: "T", Text: "«S» + 1"}})
	diamond := NewFamily("zz_diamond_abbrev", nil).WithOuterAbbrev(inner.ChapterAbbrev(), sibling.ChapterAbbrev())
	assert.Equal(t, dsl.Abbrev{{Name: "S", Text: "suc(x)"}, {Name: "SS", Text: "suc(«S»)"}, {Name: "T", Text: "«S» + 1"}}, diamond.Abbrev(),
		"two chapters cut from one parent are read together, the parent's entry once")
	joined := diamond.Add(ProofEntry{Name: "Joined", Build: diamond.Card("∀x:num. «SS» = «T» ⇒ x = 0", "a card spelling both children's tables")})
	assert.True(t, joined.Statement().Prop.AlphaEquals(diamond.statementScript().MakePropText("∀x:num. suc(suc(x)) = suc(x) + 1 ⇒ x = 0")))
	// One name with two texts is two meanings, whichever tables hold them.
	other := NewFamily("zz_other_abbrev", nil).WithAbbrev(dsl.Abbrev{{Name: "S", Text: "x"}})
	assert.PanicsWithValue(t,
		"registry.WithOuterAbbrev(zz_clash_abbrev_outer) reading zz_other_abbrev: abbreviation «S» is declared by two of the tables read, as `suc(x)` and as `x` — one name, one meaning",
		func() {
			NewFamily("zz_clash_abbrev_outer", nil).WithOuterAbbrev(inner.ChapterAbbrev(), other.ChapterAbbrev())
		})
	assert.Panics(t, func() {
		NewFamily("zz_late_abbrev", nil).WithAbbrev(dsl.Abbrev{{Name: "T", Text: "x"}}).WithOuterAbbrev(outer.ChapterAbbrev())
	}, "read under after own")
	assert.Panics(t, func() {
		NewFamily("zz_twice_abbrev", nil).WithOuterAbbrev(outer.ChapterAbbrev()).WithOuterAbbrev(outer.ChapterAbbrev())
	}, "read declared twice")
	assert.Panics(t, func() { NewFamily("zz_empty_abbrev", nil).WithOuterAbbrev() }, "a read naming no table")
	assert.Panics(t, func() { NewFamily("zz_zero_abbrev", nil).WithOuterAbbrev(ChapterAbbrev{}) }, "a zero value names no table")
}
