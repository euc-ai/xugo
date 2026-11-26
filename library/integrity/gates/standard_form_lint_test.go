package gates

import (
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
)

// TestLintStatementStandardForm — every member is stated in the one
// standard form, `∀x₁ … xₙ. H₁ ∧ … ∧ Hₘ ⇒ C`: every binder in front, the
// premises one ∧-joined antecedent, a conclusion that opens with neither
// ∀ nor ⇒ (constitution §"The section boundary is a binding form").
//
// Nothing else refuses a member stated otherwise. A curried or
// interleaved statement registers, binds at its section and replays, and
// is read short everywhere that reads only the standard form: typedgen
// writes no Read for it, and its parts list no hypotheses. So the text is
// held here.
//
// The text read is the author's: the constructor headline (a string, or
// the one a Statement literal assembles to), as written in the proof
// file. A member a door states (a definition, a door's induction
// principle) has no headline and is read as served. The served text is
// not read for a member with a headline: the bundle fold may serve
// `∀φ:ring_homomorphism(R, S).` for a premise the author wrote after its
// binder, which reads as standard while the file does not.
func TestLintStatementStandardForm(t *testing.T) {
	checked := 0
	for _, e := range registry.All() {
		text := e.Build.Headline
		if text == "" {
			text = e.StatementText()
		}
		checked++
		if _, err := dsl.StandardParts(text); err != nil {
			t.Errorf("%s: %v", e.Name, err)
		}
	}
	if checked == 0 {
		t.Fatal("no statements seen — registry enumeration broke, the gate is vacuous")
	}
	t.Logf("checked %d statements", checked)
}

// TestLintStatementInParts — a statement with a premise is written in
// parts, `Statement{Binders, Hypotheses, Conclusion}`, one hypothesis
// per line (constitution §"The section boundary is a binding form"),
// whichever constructor states it: a member's (Theorem, Card, Sections,
// Derived, Lifted), a section's (Lemma, Script.Theorem), a door's body
// (a structure's Law, Axiom and `X.Statement(body)` under any of them, a
// predicate definition's Law and Conjunct) — the arguments
// statementTextArg reads. Refused:
//
//   - a string, one literal or several joined by +, whose text has a
//     premise and whose parts assemble to its canonical spelling
//     (dsl.CanonicalParts, the criterion emit-section writes parts by);
//   - a Statement literal that names no hypothesis while its text has a
//     premise — the premise sits in its Binders or its Conclusion.
//
// Each refusal prints the parts to paste. A curried or interleaved
// statement splits no premise and stays as written: a section's `∀x. H
// ⇒ ∀y. H′ ⇒ C` binds a fact per premise, which one antecedent cannot
// say. A claim is not read here — it is not held to the standard form,
// and B3 holds a claim split by + to parts (TestLintClaimTextIsData) —
// nor the postulate, whose door takes a string.
//
// Nothing else observes the rule: a string with a premise registers,
// binds and keys as its parts do. The census of the statements read, by
// form, is logged.
func TestLintStatementInParts(t *testing.T) {
	fset := token.NewFileSet()
	forms := map[string]int{}
	for _, f := range chapterProofFiles(t) {
		af, err := parser.ParseFile(fset, f, nil, 0)
		if err != nil {
			t.Fatalf("parse %s: %v", f, err)
		}
		for _, refusal := range statementsOutOfParts(fset, af, forms) {
			t.Error(refusal)
		}
	}
	if forms[statementFormParts] == 0 || forms[statementFormString] == 0 {
		t.Fatalf("no statements read in parts or as strings (%v) — the reader broke, the gate is vacuous", forms)
	}
	names := make([]string, 0, len(forms))
	for name := range forms {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		t.Logf("statements written as %-44s %5d", name, forms[name])
	}
}

// The forms TestLintStatementInParts counts a statement argument as.
const (
	statementFormParts         = "parts"
	statementFormString        = "a string with no premise"
	statementFormCurried       = "a string, curried or interleaved"
	statementFormStringPremise = "a string with a premise (refused)"
	statementFormHiddenPremise = "parts holding the premise elsewhere (refused)"
	statementFormUnread        = "neither a literal nor parts"
)

// statementsOutOfParts reads every statement argument of af's
// constructor calls (statementTextArg) and returns a refusal for each
// one written out of parts, counting each argument's form in forms.
func statementsOutOfParts(fset *token.FileSet, af *ast.File, forms map[string]int) []string {
	var refusals []string
	ast.Inspect(af, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		verb, arg, ok := statementTextArg(call)
		if !ok || verb == "Postulate" {
			return true
		}
		pos := fset.Position(arg.Pos())
		if text, ok := joinedStringLiterals(arg); ok {
			parts, ok := dsl.CanonicalParts(text)
			switch {
			case !ok:
				forms[statementFormUnread]++
			case len(parts.Hypotheses) > 0:
				forms[statementFormStringPremise]++
				refusals = append(refusals, fmt.Sprintf("%s:%d: %s states a premise in one string — write it in parts:\n%s",
					pos.Filename, pos.Line, verb, statementPartsSource(parts)))
			case premiseShaped(text):
				forms[statementFormCurried]++
			default:
				forms[statementFormString]++
			}
			return true
		}
		stmt, ok := statementLiteral(arg)
		if !ok {
			forms[statementFormUnread]++
			return true
		}
		forms[statementFormParts]++
		if len(stmt.Hypotheses) > 0 {
			return true
		}
		text, err := stmt.Text()
		if err != nil {
			return true
		}
		if parts, ok := dsl.CanonicalParts(text); ok && len(parts.Hypotheses) > 0 {
			forms[statementFormParts]--
			forms[statementFormHiddenPremise]++
			parts.Abbrev = stmt.Abbrev
			refusals = append(refusals, fmt.Sprintf("%s:%d: %s's Statement names no hypothesis, and its text has a premise — "+
				"write the premise as one:\n%s", pos.Filename, pos.Line, verb, statementPartsSource(parts)))
		}
		return true
	})
	return refusals
}

// statementPartsSource is parts as the Statement literal a proof file
// spells, gofmt-aligned, for a refusal to print.
func statementPartsSource(parts dsl.Statement) string {
	var b strings.Builder
	b.WriteString("Statement{\n")
	if parts.Binders != "" {
		fmt.Fprintf(&b, "Binders: %q,\n", parts.Binders)
	}
	b.WriteString("Hypotheses: []string{\n")
	for _, h := range parts.Hypotheses {
		fmt.Fprintf(&b, "%q,\n", h)
	}
	b.WriteString("},\n")
	fmt.Fprintf(&b, "Conclusion: %q,\n", parts.Conclusion)
	if len(parts.Abbrev) > 0 {
		b.WriteString("Abbrev: Abbrev{\n")
		for _, a := range parts.Abbrev {
			fmt.Fprintf(&b, "{Name: %q, Text: %q},\n", a.Name, a.Text)
		}
		b.WriteString("},\n")
	}
	b.WriteString("}")
	src, err := format.Source([]byte("package p\n\nvar _ = " + b.String() + "\n"))
	if err != nil {
		return b.String()
	}
	return strings.TrimSuffix(strings.TrimPrefix(string(src), "package p\n\nvar _ = "), "\n")
}

// TestStatementsOutOfPartsReadsTheSource: the reader refuses a premise
// written in one string at every constructor it reads — a card, a card
// through a structure's door, a law of another family's door, a law of
// a predicate definition's entry, a lift —
// and a premise a Statement literal keeps out of its Hypotheses, and
// passes a statement with no premise, one already in parts, a section's
// interleaved parts and a curried string.
func TestStatementsOutOfPartsReadsTheSource(t *testing.T) {
	// The curried census needs the premise shape told apart — a
	// standard and a curried premise from a ⇒ that is no premise.
	for text, want := range map[string]bool{
		"∀x:num. x = 0 ⇒ x ≤ 1":           true,
		"x = 0 ⇒ x = 1 ⇒ x = 2":           true,
		"∀x:num. (x = 0 ⇒ x ≤ 1) ∧ x = x": false,
		"∀x:num. ∃y:num. x = 0 ∧ y = x":   false,
		"∀s:set(A). s ⊆ s":                false,
	} {
		if got := premiseShaped(text); got != want {
			t.Fatalf("premiseShaped(%q) = %v, want %v", text, got, want)
		}
	}

	const src = `package p

var card = family.Card("∀m n:num. m ∣ n ∧ n ∣ m ⇒ m = n", "note")
var plain = family.Card("∀m n:num. m ∣ n ⇔ ∃k:num. n = m * k", "note")
var door = family.Card(topological_space.IsTopology.Statement("∀s:set(A). connected_in(s) ⇒ connected_in(closure(s))"), "note")
var law = comm_ring.CommRingOn.Law("∀x:A. x ∈ R.carrier ⇒ x = x", proof)
var conjunct = SubmoduleDef.Entry().Law("∀u:B. u ∈ N ⇒ -u ∈ N", proof)
var hidden = family.Theorem(Statement{Binders: "∀x:num.", Conclusion: "x = 0 ⇒ x ≤ 1"}, body)
var parts = family.Theorem(Statement{Binders: "∀x:num.", Hypotheses: []string{"x = 0"}, Conclusion: "x ≤ 1"}, body)
var interleaved = ctx.Lemma(Statement{Binders: "∀H:set(num).", Hypotheses: []string{"finite(H)"}, Conclusion: "∀d:num. d ∈ H ⇒ d ≤ d"}, body)
var curried = ctx.Lemma("∀m:num. p ⇒ q ⇒ m = m", body)
var lift = family.Lifted("∀x y z:int. x ≤ y ∧ " + "y ≤ z ⇒ x ≤ z", real_construction.LessEqTrans)
`
	fset := token.NewFileSet()
	af, err := parser.ParseFile(fset, "p.go", src, 0)
	if err != nil {
		t.Fatal(err)
	}
	forms := map[string]int{}
	refusals := statementsOutOfParts(fset, af, forms)
	var lines []int
	for _, r := range refusals {
		var line int
		if _, err := fmt.Sscanf(strings.TrimPrefix(r, "p.go:"), "%d:", &line); err != nil {
			t.Fatalf("a refusal that names no line: %s", r)
		}
		lines = append(lines, line)
	}
	if want := []int{3, 5, 6, 7, 8, 12}; fmt.Sprint(lines) != fmt.Sprint(want) {
		t.Fatalf("refused the statements on lines %v, want %v:\n%s", lines, want, strings.Join(refusals, "\n"))
	}
	if !strings.Contains(refusals[0], `Hypotheses: []string{
		"m ∣ n",
		"n ∣ m",
	},`) {
		t.Errorf("the refusal does not print the parts to paste:\n%s", refusals[0])
	}
	want := map[string]int{
		statementFormStringPremise: 5, statementFormHiddenPremise: 1, statementFormParts: 2,
		statementFormString: 1, statementFormCurried: 1,
	}
	if fmt.Sprint(forms) != fmt.Sprint(want) {
		t.Errorf("counted %v, want %v", forms, want)
	}
}
