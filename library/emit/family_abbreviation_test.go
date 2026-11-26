package emit

import (
	"regexp"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// The member declares every abbreviation its texts spell on its
// headline, once: the Script reads the headline's table for every
// section and claim of the member, so a lemma under family.Sections
// declares none, and a card beside the member declares its own.

var falsehoodTable = dsl.Abbrev{{Name: "falsehood", Text: "⊥"}}

// sectionsFixture is a two-section member: the lemma ⊥, which spells
// «falsehood» under the table, and the headline.
func sectionsFixture(env *proof.ProverEnv, headline string) []*proof.DetailedProofProto {
	ctx := proof.NewScript(env)
	pb := ext.NewPoolBuilder()
	lemma := pb.PropRef(ctx.MakePropText("⊥"))
	top := pb.PropRef(ctx.MakePropText(headline))
	return []*proof.DetailedProofProto{
		detailed(pb, &proof.StepProto{Goal: lemma, Step: &proof.StepProto_TrivialSimplify{}}),
		detailed(pb, &proof.StepProto{Goal: top, Step: &proof.StepProto_TrivialSimplify{}}),
	}
}

// TestEmit_FamilySectionsDeclareAbbreviationsOnce: the headline and the
// lemma both spell «falsehood»; family.Sections declares it once, on
// the headline, and the lemma — with no premise — is the one string.
// An authored headline declaring the entry keeps its literal as
// written; one declaring nothing gains the entry the lemma spells.
func TestEmit_FamilySectionsDeclareAbbreviationsOnce(t *testing.T) {
	env := makeTestEnv(t)
	declared := regexp.MustCompile(`Name:\s+"falsehood"`)
	for _, tc := range []struct {
		name     string
		headline string         // the statement the session proved
		stated   string         // its authored text, "" where the headline is printed
		parts    *dsl.Statement // the authored parts, nil where printed
	}{
		{"printed", "∀p q:bool. p ∨ q ∨ ⊥", "", nil},
		{"authored declaring", "∀p q:bool. p ∨ q ∨ ⊥", "∀p q:bool. p ∨ q ∨ «falsehood»",
			&dsl.Statement{Binders: "∀p q:bool.", Conclusion: "p ∨ q ∨ «falsehood»",
				Abbrev: append(make(dsl.Abbrev, 0, 4), falsehoodTable...)}},
		{"authored gaining", "∀p q:bool. p ∨ q", "∀p q:bool. p ∨ q",
			&dsl.Statement{Binders: "∀p q:bool.", Conclusion: "p ∨ q"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			var written dsl.Abbrev // the author's slice, spare capacity included
			if tc.parts != nil {
				written = slices.Clone(tc.parts.Abbrev[:cap(tc.parts.Abbrev)])
			}
			src := emitMember(t, env, EmitOptions{
				FuncName:       "Build_SectionAbbreviations",
				Abbreviations:  falsehoodTable,
				StatementText:  tc.stated,
				StatementParts: tc.parts,
			}, sectionsFixture(env, tc.headline)...).Source
			start := strings.Index(src, "family.Sections(")
			require.NotEqual(t, -1, start, "not rendered through family.Sections:\n%s", src)
			sections := src[start:]
			head := sections[:strings.Index(sections, "func(ctx *Script, headline string)")]
			assert.Len(t, declared.FindAllString(src, -1), 1, "declared once across the member:\n%s", src)
			assert.Len(t, declared.FindAllString(head, -1), 1, "declared on the headline:\n%s", src)
			assert.Contains(t, src, "ctx.Lemma(\"«falsehood»\",", "a lemma with no premise is the one string:\n%s", src)
			if tc.parts != nil {
				assert.Equal(t, written, tc.parts.Abbrev[:cap(tc.parts.Abbrev)],
					"emission wrote into the author's literal")
			}
		})
	}
}

// TestEmit_CardNamesAreTheCardsOwn: a card beside the member spells
// «falsehood» and the member does not; the card declares it, and the
// member's headline stays the one string.
func TestEmit_CardNamesAreTheCardsOwn(t *testing.T) {
	env := makeTestEnv(t)
	ctx := proof.NewScript(env)
	pb := ext.NewPoolBuilder()
	top := pb.PropRef(ctx.MakePropText("∀p q:bool. p ∨ q"))
	src := emitMember(t, env, EmitOptions{
		FuncName:      "Build_BesideACard",
		Abbreviations: falsehoodTable,
		Cards:         []EmitCard{{Name: "Falsehood", Statement: "∀p:bool. p ∨ «falsehood»", Note: "stated ahead of its proof"}},
	}, detailed(pb, &proof.StepProto{Goal: top, Step: &proof.StepProto_TrivialSimplify{}})).Source
	card, member, found := strings.Cut(src, "var BesideACard")
	require.True(t, found, src)
	assert.Contains(t, card, `Name: "falsehood"`, "the card declares its own entry:\n%s", src)
	assert.Contains(t, member, `family.Theorem("∀p q:bool. p ∨ q",`, "the member spells no entry:\n%s", src)
	assert.NotContains(t, member, "falsehood", "the card's entry leaked into the member:\n%s", src)
}

// headlineEmitter is a bare emitter over table whose rendered texts
// spelled the names used, its headline authored in parts or printed.
func headlineEmitter(t *testing.T, headline string, parts *dsl.Statement, table dsl.Abbrev, used ...string) *_Emitter {
	t.Helper()
	parsed, err := dsl.ParseAbbreviations(table)
	require.NoError(t, err)
	e := &_Emitter{abbrevTable: parsed, abbrevUsed: map[string]bool{}, familyGoalText: headline}
	if parts != nil {
		e.opts = EmitOptions{StatementText: headline, StatementParts: parts}
	}
	for _, name := range used {
		e.abbrevUsed[name] = true
	}
	return e
}

// TestHeadlineArg_DeclaresWhatTheProofSpells: the headline declares the
// entries the proof spells and what they stand on, not the rest of the
// table — appended to an authored literal, which is left as written
// and keeps its own spelling of a name it declares itself.
func TestHeadlineArg_DeclaresWhatTheProofSpells(t *testing.T) {
	table := dsl.Abbrev{
		{Name: "base", Text: "m + n"},
		{Name: "body", Text: "suc(«base»)"},
		{Name: "unused", Text: "n + m"},
	}
	const headline = "∀m n:num. m < n ⇒ m ≤ n"
	t.Run("printed", func(t *testing.T) {
		got := headlineEmitter(t, headline, nil, table, "body").headlineArg("\t")
		assert.Contains(t, got, `Name: "base"`)
		assert.Contains(t, got, `Name: "body"`)
		assert.NotContains(t, got, `Name: "unused"`)
		assert.Equal(t, `"∀m n:num. m = n"`, headlineEmitter(t, "∀m n:num. m = n", nil, table).headlineArg("\t"))
	})
	t.Run("authored gains the proof's", func(t *testing.T) {
		authored := &dsl.Statement{Binders: "∀m n:num.", Hypotheses: []string{"m < n"}, Conclusion: "m ≤ n"}
		got := headlineEmitter(t, headline, authored, table, "body").headlineArg("\t")
		assert.Contains(t, got, `Name: "base"`)
		assert.Contains(t, got, `Name: "body"`)
		assert.NotContains(t, got, `Name: "unused"`)
		assert.Empty(t, authored.Abbrev, "the author's literal is left as written")
	})
	t.Run("authored keeps its own spelling", func(t *testing.T) {
		authored := &dsl.Statement{Binders: "∀m n:num.", Hypotheses: []string{"m < n"}, Conclusion: "m ≤ n",
			Abbrev: dsl.Abbrev{{Name: " base ", Text: "m + n"}, {Name: " body ", Text: "suc(«base»)"}}}
		got := headlineEmitter(t, headline, authored, table, "body").headlineArg("\t")
		assert.Len(t, regexp.MustCompile(`Name:`).FindAllString(got, -1), 2, got)
		assert.Contains(t, got, `Name: " body "`)
		assert.NotContains(t, got, `Name: "body"`)
	})
}

// TestHeadlineArg_RefusesANameUnderTwoTexts: an entry the landed entry
// and the session's table both declare, under different texts, is an
// inconsistency.
func TestHeadlineArg_RefusesANameUnderTwoTexts(t *testing.T) {
	const headline = "∀m n:num. m ≤ «body»"
	authored := &dsl.Statement{Binders: "∀m n:num.", Conclusion: "m ≤ «body»",
		Abbrev: dsl.Abbrev{{Name: "body", Text: "suc(n)"}}}
	e := headlineEmitter(t, headline, authored, dsl.Abbrev{{Name: "body", Text: "suc(m)"}}, "body")
	require.PanicsWithValue(t,
		`emit: «body» is "suc(n)" in the landed entry's statement and "suc(m)" in the session's table — one name, one meaning`,
		func() { e.headlineArg("\t") })
}

// TestHeadlineArg_ErrsWhereTheNamesHaveNoPlace: a headline that cannot
// be written in parts — a sequent — while the proof spells an entry is
// an emit error, not a declaration dropped.
func TestHeadlineArg_ErrsWhereTheNamesHaveNoPlace(t *testing.T) {
	const headline = "m ≤ «body» ⊢ m ≤ «body»"
	table := dsl.Abbrev{{Name: "body", Text: "suc(n)"}}
	e := headlineEmitter(t, headline, nil, table, "body")
	assert.Equal(t, `"m ≤ «body» ⊢ m ≤ «body»"`, e.headlineArg("\t"))
	require.Error(t, e.textErr)
	assert.Contains(t, e.textErr.Error(), "«body»")

	e = headlineEmitter(t, "m ≤ n ⊢ m ≤ n", nil, table)
	e.headlineArg("\t")
	require.NoError(t, e.textErr, "a member spelling no entry has nothing to declare")
}

// TestRequireNoAbbreviations_ErrsAtAOneStringDoor: the Instance door
// states the member as one string; a proof under it spelling an entry
// is an emit error.
func TestRequireNoAbbreviations_ErrsAtAOneStringDoor(t *testing.T) {
	table := dsl.Abbrev{{Name: "pt", Text: "zz_point"}}
	e := headlineEmitter(t, "zz_triple(zz_point)", nil, table, "pt")
	e.requireNoAbbreviations("Instance")
	require.Error(t, e.textErr)
	assert.Contains(t, e.textErr.Error(), "«pt»")
	assert.Contains(t, e.textErr.Error(), "Instance door")

	e = headlineEmitter(t, "zz_triple(zz_point)", nil, table)
	e.requireNoAbbreviations("Instance")
	require.NoError(t, e.textErr)
}

// TestHeadlineArg_LeavesTheChaptersEntriesOut: an entry the chapter's
// table declares (FamilyVocab.Abbrev) is in scope for every text of
// the chapter, so the member declares only what it spells beyond it —
// and a member spelling nothing beyond it keeps the one string, as a
// card beside it does.
func TestHeadlineArg_LeavesTheChaptersEntriesOut(t *testing.T) {
	chapter := &FamilyVocab{Abbrev: map[string]bool{"falsehood": true}}
	table := dsl.Abbrev{{Name: "falsehood", Text: "⊥"}, {Name: "both", Text: "«falsehood» ∧ «falsehood»"}}
	e := &_Emitter{opts: EmitOptions{Abbreviations: table, FamilyVocab: chapter}, abbrevUsed: map[string]bool{}}
	var err error
	e.abbrevTable, err = dsl.ParseAbbreviations(table)
	require.NoError(t, err)

	e.familyGoalText = "∀p:bool. p ∨ «falsehood»"
	assert.Equal(t, `"∀p:bool. p ∨ «falsehood»"`, e.headlineArg("\t"), "only the chapter's name: the one string")
	assert.Equal(t, `"∀p:bool. p ∨ «falsehood»"`, e.cardArg("∀p:bool. p ∨ «falsehood»", "\t"))
	e.requireNoAbbreviations("Instance")

	e.abbrevUsed = map[string]bool{}
	e.familyGoalText = "∀p:bool. p ∨ «both»"
	parts := e.headlineArg("\t")
	assert.Contains(t, parts, `{Name: "both", Text: "«falsehood» ∧ «falsehood»"}`, "the member's own entry is declared")
	assert.NotContains(t, parts, `Name: "falsehood"`, "the chapter's is not")
}

// The structure supplies a law's prefix; the body's own table must
// still be declared when the proof, rather than its headline, uses it.
func TestLawArg_DeclaresTheProofsAbbreviations(t *testing.T) {
	table := dsl.Abbrev{
		{Name: "base", Text: "m + n"},
		{Name: "body", Text: "suc(«base»)"},
		{Name: "unused", Text: "n + m"},
	}
	e := headlineEmitter(t, "∀m n:num. m < n ⇒ m ≤ n", nil, table, "body")
	got := e.lawArg("∀m n:num. m < n ⇒ m ≤ n", "\t")
	require.NoError(t, e.textErr)
	assert.Contains(t, got, `Binders: "∀m n:num."`)
	assert.Contains(t, got, `"m < n"`)
	assert.Contains(t, got, `Conclusion: "m ≤ n"`)
	assert.Contains(t, got, `{Name: "base", Text: "m + n"}`)
	assert.Contains(t, got, `{Name: "body", Text: "suc(«base»)"}`)
	assert.NotContains(t, got, `Name: "unused"`)

	e = headlineEmitter(t, "∀m n:num. m ≤ n", nil, table)
	assert.Equal(t, `"∀m n:num. m ≤ n"`, e.lawArg("∀m n:num. m ≤ n", "\t"))
	require.NoError(t, e.textErr)
}

// TestSurfaceText_AnAppliedLambdaKeepsItsSpellingBesideTheFolds: a claim
// that applies a λ as written — the instance of a law at a λ witness,
// `(λx. f(x))(a)` — is printed with that redex spelled out where an
// abbreviation names the λ: `«through»(a)` reads as `f(a)`, another
// proposition. The fold is made where it reads back and nowhere else,
// so the rest of the text keeps the member's abbreviations.
func TestSurfaceText_AnAppliedLambdaKeepsItsSpellingBesideTheFolds(t *testing.T) {
	table, err := dsl.ParseAbbreviations(dsl.Abbrev{
		{Name: "through", Text: "λx:A. f(x)"},
		{Name: "twice", Text: "f(f(a))"},
	})
	require.NoError(t, err)
	scope := &dsl.ParseScope{
		Vars:          map[string]core.HolType{"a": core.TypeA(), "f": core.MakeFun(core.TypeA(), core.TypeA())},
		Abbreviations: table,
	}
	e := &_Emitter{abbrevTable: table, abbrevUsed: map[string]bool{}}

	original := dsl.ParsePropTextAtDoor("(λx:A. f(x))(f(a)) = f(f(a))", scope)
	require.Empty(t, original.Errors)
	folded := prop.FormatPropForParserNoDecls(e.foldProp(original.Prop, scope))
	require.NotContains(t, folded, "«through»(f(a))", "the applied λ is not folded into its name")
	require.Contains(t, folded, "«twice»")

	text, err := e.surfaceTextIn("claim", original.Prop, scope, false, nil)
	require.NoError(t, err)
	read := dsl.ParsePropTextAtDoor(text, scope)
	require.Empty(t, read.Errors)
	require.True(t, original.Prop.AlphaEquals(read.Prop), "the text %q reads as %s", text, prop.PrintProp(read.Prop))
	require.Contains(t, text, "«twice»", "the text keeps the abbreviations that read back")
	require.True(t, e.abbrevUsed["twice"])
}
