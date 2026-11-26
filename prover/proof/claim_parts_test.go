// claim_parts_test.go — a claim written in parts (dsl.Statement) at the
// claim verbs: it assembles to the one string the verb would read, the
// claim's own Binders are exempt from the abbreviation capture check
// as a section's leading binders are, and a claim carrying a table of
// its own or a part that does not parse is refused naming the verb.
//
// The fixture is section_opening_test's: R, Q over num, the constant
// OpeningTestConj(R, Q, n) ≔ R(n) ∧ Q(n), and section_abbreviation_test's
// statement in parts with «s» ≔ suc(n).
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// A Have in parts: the hypotheses ∧-join into one antecedent under the
// binders, and the fact resident is that statement.
func TestClaimParts_HaveAssemblesTheParts(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem(openingTestStatement,
		Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
			both := a.Have("R at every m where R and Q both hold", dsl.Statement{
				Binders:    "∀m:num.",
				Hypotheses: []string{"R(m)", "Q(m)"},
				Conclusion: "R(m)",
			}, CnfRefute())
			content, ok := both.BoundContent()
			require.True(t, ok, "a Have's fact is resident")
			require.True(t, content.AlphaEquals(a.Term("∀m:num. R(m) ∧ Q(m) ⇒ R(m)").Core()),
				"the parts assemble to the ∧-joined statement; got %s", PrintTerm(content))
			a.Show("the goal is the other conjunct", By(h))
		}))
	require.True(t, sec.Proved())
}

// A Hyp in parts locates the resident premise the parts assemble to.
func TestClaimParts_HypLocatesThePremise(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem("∀n:num. (∀m:num. R(m) ⇒ Q(m)) ∧ R(n) ⇒ Q(n)",
		func(a *Argument, n Term, step Fact, base Fact) {
			found := a.Hyp(dsl.Statement{
				Binders:    "∀m:num.",
				Hypotheses: []string{"R(m)"},
				Conclusion: "Q(m)",
			})
			want, _ := step.BoundContent()
			got, _ := found.BoundContent()
			require.True(t, got.AlphaEquals(want), "Hyp in parts names the ∀-premise; got %s", PrintTerm(got))
			a.Show("Q at n from the premise at n", By(found.At(n), base))
		})
	require.True(t, sec.Proved())
}

// The claim's own Binders are exempt from the capture check — an entry
// spelled under such a binder is read at it — and nothing else is: the
// same text as one string rebinds the member's n and is refused, and so
// is a Conclusion that binds n itself.
func TestClaimParts_OwnBindersExemptFromCapture(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem(abbreviationTestStatement("s"),
		Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
			atEvery := a.Have("R at s, for every n", dsl.Statement{
				Binders:    "∀n:num.",
				Hypotheses: []string{"R(«s»)"},
				Conclusion: "R(«s»)",
			}, CnfRefute())
			content, _ := atEvery.BoundContent()
			require.True(t, content.AlphaEquals(a.Term("∀n:num. R(suc(n)) ⇒ R(suc(n))").Core()),
				"«s» is read at the claim's own n; got %s", PrintTerm(content))
			mustPanicContaining(t, "«s» spells n, which a binder of this text rebinds", func() {
				a.Have("the same claim as one string binds the member's n", "∀n:num. R(«s») ⇒ R(«s»)", CnfRefute())
			})
			mustPanicContaining(t, "«s» spells n, which a binder of this text rebinds", func() {
				a.Have("a Conclusion that binds n is no Binders entry", dsl.Statement{Conclusion: "∃n:num. R(«s»)"}, By(h))
			})
			a.Show("the other conjunct is the goal", By(h))
		}))
	require.True(t, sec.Proved())
}

// The refusals name the verb: a part that does not parse, a table of
// the claim's own, a nil pointer, no Conclusion.
func TestClaimParts_Refusals(t *testing.T) {
	ctx := newOpeningTestScript()
	sec := ctx.Theorem(openingTestStatement,
		Opening(Unfold(openingTestDefinition), func(a *Argument, n Term, h Fact) {
			mustPanicContaining(t, `Argument.Have: statement: Hypotheses[1] "Q(n"`, func() {
				a.Have("a hypothesis that does not parse", dsl.Statement{Hypotheses: []string{"R(n)", "Q(n"}, Conclusion: "R(n)"}, By(h))
			})
			mustPanicContaining(t, "Argument.Obtain: the claim declares «t» — a claim's abbreviations are the member's", func() {
				a.Obtain("a claim with a table of its own", dsl.Statement{
					Conclusion: "∃m:num. R(«t»)",
					Abbrev:     dsl.Abbrev{{Name: "t", Text: "suc(n)"}},
				}, By(h))
			})
			mustPanicContaining(t, "Argument.Hyp: a nil *Statement", func() {
				var none *dsl.Statement
				a.Hyp(none)
			})
			mustPanicContaining(t, "Argument.Have: statement: no Conclusion", func() {
				a.Have("no conclusion", dsl.Statement{Hypotheses: []string{"R(n)"}}, By(h))
			})
			a.Show("the other conjunct is the goal", By(h))
		}))
	require.True(t, sec.Proved())
}
