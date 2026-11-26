// section_abbreviation_test.go — a section stated in parts with an
// abbreviation table (dsl.Statement): the parts assemble to the
// section's statement, the table's names are in scope for the body's
// claim and term texts, and a claim that rebinds a name an entry
// spells is refused.
//
// The fixture is section_opening_test's: `∀n:num. OpeningTestConj(R,
// Q, suc(n)) ⇒ Q(suc(n))`, its term `suc(n)` abbreviated «s», proved
// under an opening Unfold as the opening tests prove theirs.
package proof

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

func abbreviationTestStatement(name string) dsl.Statement {
	return dsl.Statement{
		Binders:    "∀n:num.",
		Hypotheses: []string{openingTestConst + "(R, Q, «" + name + "»)"},
		Conclusion: "Q(«" + name + "»)",
		Abbrev:     dsl.Abbrev{{Name: name, Text: "suc(n)"}},
	}
}

func TestSectionAbbreviations_StatementInParts(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem(abbreviationTestStatement("s"),
		Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
			// The term door reads the table, at the block's minted n.
			require.True(t, a.Term("«s»").Core().Equals(a.Term("suc(n)").Core()),
				"«s» reads as the term it abbreviates")
			// So does the claim door: R at «s» is a conjunct of the
			// unfolded hypothesis.
			a.Have("R at s, read off the unfolded hypothesis", "R(«s»)", By(h))
			a.Show("the other conjunct is the goal", By(h))
		}))
	require.True(t, sec.Proved(), "the section stated in parts did not close")
	expanded := ctx.MakePropText("∀n:num. " + openingTestConst + "(R, Q, suc(n)) ⇒ Q(suc(n))")
	require.True(t, sec.Goal.AlphaEquals(expanded),
		"the parts assemble to the statement, the abbreviation expanded; got %s", PrintProp(sec.Goal))
}

func TestSectionAbbreviations_CaptureRefused(t *testing.T) {
	ctx := newOpeningTestScript()
	defer func() {
		r := recover()
		require.NotNil(t, r, "a claim rebinding n must panic")
		require.Contains(t, fmt.Sprint(r), "«s» spells n, which a binder of this text rebinds")
	}()
	ctx.Theorem(abbreviationTestStatement("s"),
		func(a *Argument, n Term, h Fact) {
			a.Have("a claim that rebinds n", "∃n:num. R(«s»)", By(h))
		})
}

func TestSectionAbbreviations_UnknownNameNamesTheTable(t *testing.T) {
	ctx := newOpeningTestScript()
	defer func() {
		r := recover()
		require.NotNil(t, r)
		require.Contains(t, fmt.Sprint(r), "«other» is not an abbreviation of this statement (declared: «s»)")
	}()
	ctx.Theorem(abbreviationTestStatement("s"),
		func(a *Argument, n Term, h Fact) {
			a.Have("a name the table lacks", "R(«other»)", By(h))
		})
}

// A lemma with no table of its own reads under the member's, its own
// leading binders the ones its entries' names are read at.
func TestSectionAbbreviations_LemmaReadsTheMembersTable(t *testing.T) {
	ctx := newOpeningTestScript()
	table, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "s", Text: "suc(n)"}})
	require.NoError(t, err)
	ctx.UseAbbreviations(table, map[string]bool{"m": true})
	lemma := abbreviationTestStatement("s")
	lemma.Abbrev = nil
	sec := ctx.Lemma(lemma, Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
		require.True(t, a.Term("«s»").Core().Equals(a.Term("suc(n)").Core()))
		a.Show("the other conjunct is the goal", By(h))
	}))
	require.True(t, sec.Proved(), "the lemma's leading n is its own, not a capture")
	require.Equal(t, map[string]bool{"m": true}, ctx.ParseScope.AbbreviationBinders, "the member's binders come back")
}

// A lemma's own table joins the script's for the lemma's texts and
// leaves with it; a name both declare is refused.
func TestSectionAbbreviations_LemmaTableIsScoped(t *testing.T) {
	ctx := newOpeningTestScript()
	lemma := abbreviationTestStatement("t")
	sec := ctx.Lemma(lemma, Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
		require.True(t, a.Term("«t»").Core().Equals(a.Term("suc(n)").Core()))
		a.Show("the other conjunct is the goal", By(h))
	}))
	require.True(t, sec.Proved())
	require.Nil(t, ctx.ParseScope.Abbreviations, "the lemma's table leaves the script with the lemma")

	table, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "t", Text: "n"}})
	require.NoError(t, err)
	ctx.UseAbbreviations(table, map[string]bool{"n": true})
	defer func() {
		r := recover()
		require.NotNil(t, r, "a lemma redeclaring the script's «t» must panic")
		require.Contains(t, fmt.Sprint(r), "one name, one meaning")
	}()
	ctx.Lemma(lemma, func(a *Argument, n Term, h Fact) { a.Show("never reached", By(h)) })
}

// A lemma's entry may spell an entry of the table it is read under: the
// lemma's entries and the member's are one table, the member's first.
func TestSectionAbbreviations_LemmaEntrySpellsTheMembers(t *testing.T) {
	ctx := newOpeningTestScript()
	table, err := dsl.ParseAbbreviations(dsl.Abbrev{{Name: "s", Text: "suc(n)"}})
	require.NoError(t, err)
	ctx.UseAbbreviations(table, map[string]bool{"n": true})
	lemma := abbreviationTestStatement("s")
	lemma.Abbrev = dsl.Abbrev{{Name: "goal", Text: "Q(«s»)"}}
	lemma.Conclusion = "«goal»"
	sec := ctx.Lemma(lemma, Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
		require.True(t, a.Term("«goal»").Core().Equals(a.Term("Q(suc(n))").Core()),
			"«goal» reads through the member's «s»")
		a.Show("the other conjunct is the goal", By(h))
	}))
	require.True(t, sec.Proved())
	require.Same(t, table, ctx.ParseScope.Abbreviations, "the member's table comes back")

	// An entry spelling a name neither table declares is refused, and
	// the refusal names it.
	lemma.Abbrev = dsl.Abbrev{{Name: "goal", Text: "Q(«other»)"}}
	defer func() {
		r := recover()
		require.NotNil(t, r, "an entry spelling an undeclared name must panic")
		require.Contains(t, fmt.Sprint(r), "«goal» spells «other», which is not declared before it")
	}()
	ctx.Lemma(lemma, func(a *Argument, n Term, h Fact) { a.Show("never reached", By(h)) })
}
