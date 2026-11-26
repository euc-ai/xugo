package emit

import (
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
)

// statementLiteral renders the parts as the authoring surface spells
// them: one hypothesis and one abbreviation per line, the keys as
// gofmt lays them out, the lines after the first at the call's
// indentation.
func TestStatementLiteral(t *testing.T) {
	got := statementLiteral(&dsl.Statement{
		Binders:    "∀L:field_on(A). ∀E:set(A).",
		Hypotheses: []string{"subfield(L, k)", "e ∉ E"},
		Conclusion: "fst(«P») = «P»",
		Abbrev:     dsl.Abbrev{{Name: "P", Text: "free_pair(L, E)"}},
	}, "\t\t")
	assert.Equal(t, "Statement{\n"+
		"\t\t\tBinders: \"∀L:field_on(A). ∀E:set(A).\",\n"+
		"\t\t\tHypotheses: []string{\n"+
		"\t\t\t\t\"subfield(L, k)\",\n"+
		"\t\t\t\t\"e ∉ E\",\n"+
		"\t\t\t},\n"+
		"\t\t\tConclusion: \"fst(«P») = «P»\",\n"+
		"\t\t\tAbbrev: Abbrev{\n"+
		"\t\t\t\t{Name: \"P\", Text: \"free_pair(L, E)\"},\n"+
		"\t\t\t},\n"+
		"\t\t}", got)

	got = statementLiteral(&dsl.Statement{Binders: "∀m n:num.", Conclusion: "m < n ∨ m = n",
		Abbrev: dsl.Abbrev{{Name: "lt", Text: "m < n"}}}, "\t")
	assert.Equal(t, "Statement{\n"+
		"\t\tBinders:    \"∀m n:num.\",\n"+
		"\t\tConclusion: \"m < n ∨ m = n\",\n"+
		"\t\tAbbrev: Abbrev{\n"+
		"\t\t\t{Name: \"lt\", Text: \"m < n\"},\n"+
		"\t\t},\n"+
		"\t}", got)
}
