package gates

import (
	"fmt"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/xugofmt"
)

// TestLintClaimPartsByWidth — a claim with a premise is written in parts
// where its one string does not fit on its line, and as the one string
// where it does (manual §"The constructors"): written as the quoted
// text, the line the claim's argument stands on past xugofmt.LineWidth
// columns from its indentation is the parts', `Statement{Binders, Hypotheses, Conclusion}`,
// one hypothesis per line. emit-section writes a claim so (library/emit's
// claimArg). The verbs read are the claim verbs — Have, Obtain and its
// numbered and typed twins, ObtainChosen, Hyp; a member's and a
// section's statements are TestLintStatementInParts's, in parts
// whatever their width. Refused (claimLayoutRefusal):
//
//   - a string, one literal or several joined by +, whose text has a
//     premise (dsl.CanonicalParts) and whose line runs past the width —
//     the parts are printed to paste;
//   - a Statement literal whose one string fits, or that names no
//     hypothesis — parts whose Conclusion implies again, a section's
//     interleaved claim, have their premise in the Hypotheses they
//     name — unless its Binders are written over an
//     abbreviation's names: the claim door exempts a claim's own
//     Binders from the capture check in parts and not in a string
//     (TestLintClaimExemptsWhatTheDoorExempts), so that claim reads in
//     parts alone.
//
// A claim spelled by a const or assembled from Go strings is B3's
// (TestLintClaimTextIsData) and is not read here. The census of the
// claims read, by layout, is logged.
func TestLintClaimPartsByWidth(t *testing.T) {
	scopes := newClaimScopeCache(claimLintEnv())
	famByDir := claimFamilyByDir()
	col := collectClaimSites(t)
	layouts := map[string]int{}
	for _, s := range col.sites {
		if claimHeadlineVerbs[s.verb] || s.verb == "Term" || !s.literal && s.statement == nil {
			continue
		}
		layout, refusal := claimLayoutRefusal(s, func() bool {
			return claimBindsOverAbbreviation(scopes.scope(famByDir[s.dir]), s)
		})
		layouts[layout]++
		if refusal != "" {
			t.Errorf("%s:%d: %s %s", s.file, s.line, s.verb, refusal)
		}
	}
	if layouts[claimLayoutString] == 0 || layouts[claimLayoutWide] == 0 {
		t.Fatalf("no claims read as strings or as parts past the width (%v) — the reader broke, the gate is vacuous", layouts)
	}
	names := make([]string, 0, len(layouts))
	for name := range layouts {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		t.Logf("claims written as %-48s %5d", name, layouts[name])
	}
}

// The layouts TestLintClaimPartsByWidth counts a claim as.
const (
	claimLayoutString       = "a string"
	claimLayoutStringWide   = "a string with a premise past the width (refused)"
	claimLayoutWide         = "parts past the width"
	claimLayoutBinders      = "parts its Binders keep"
	claimLayoutPartsFitting = "parts that fit, or with no premise (refused)"
)

// claimLayoutRefusal is the layout the claim s is written in and, where
// the layout is not the claim's, why: a string with a premise past
// xugofmt.LineWidth is the parts', and parts that fit or name no
// hypothesis are the one string's unless keptByBinders — whether the
// claim's Binders must stay exempt from the capture check, asked only
// of parts the rule would otherwise refuse.
func claimLayoutRefusal(s claimSite, keptByBinders func() bool) (string, string) {
	parts, ok := dsl.CanonicalParts(s.text)
	premise := ok && len(parts.Hypotheses) > 0
	if s.statement != nil {
		premise = len(s.statement.Hypotheses) > 0
	}
	fits := s.width <= xugofmt.LineWidth
	switch {
	case s.literal && premise && !fits:
		return claimLayoutStringWide, fmt.Sprintf("claim's one string runs to %d columns and states a premise — write it in parts:\n%s",
			s.width, claimPartsSource(parts))
	case s.literal:
		return claimLayoutString, ""
	case premise && !fits:
		return claimLayoutWide, ""
	case keptByBinders():
		return claimLayoutBinders, ""
	case !premise:
		return claimLayoutPartsFitting, fmt.Sprintf("claim in parts names no hypothesis — write it as the one string:\n  %q", s.text)
	default:
		return claimLayoutPartsFitting, fmt.Sprintf("claim in parts fits on its line as the one string (%d columns) — write it so:\n  %q",
			s.width, s.text)
	}
}

// claimBindsOverAbbreviation reports whether the claim in parts s reads
// otherwise as the one string: its Binders are exempt from the capture
// check only in parts, and the exemption is all that differs between the
// two readings, so a difference is an abbreviation the string's binders
// would capture.
func claimBindsOverAbbreviation(scope *dsl.ParseScope, s claimSite) bool {
	if len(s.exempt) == 0 {
		return false
	}
	plain := s
	plain.exempt = nil
	return claimErrString(parseClaimSite(scope, s)) != claimErrString(parseClaimSite(scope, plain))
}

// claimPartsSource is a claim's parts as the Statement literal a proof
// file spells — statementPartsSource with no table, since a claim reads
// the member's.
func claimPartsSource(parts dsl.Statement) string {
	parts.Abbrev = nil
	return statementPartsSource(parts)
}

// TestClaimLayoutRefusal: the rule reads the width and the premise, and
// keeps in parts what its Binders need — a long string with a premise
// and short parts are refused, a short string, a long string with no
// premise and long parts, interleaved ones too, pass, and short parts
// pass where their Binders are written over an abbreviation;
// claimLineWidth measures the line
// the argument stands on as xugofmt does, a tab four columns.
func TestClaimLayoutRefusal(t *testing.T) {
	long := "∀x:num. x ∈ " + strings.Repeat("s", 90) + " ⇒ x ≤ x"
	short := "∀x:num. x ∈ s ⇒ x ≤ x"
	never := func() bool { t.Fatal("keptByBinders asked of a claim the rule does not refuse"); return false }
	guarded := &dsl.Statement{Binders: "∀x:num.", Hypotheses: []string{"x ∈ s"}, Conclusion: "x ≤ x"}
	interleaved := &dsl.Statement{Binders: "∀x:num.", Hypotheses: []string{"x ∈ s"}, Conclusion: "∀y:num. y ∈ s ⇒ x ≤ y"}
	for _, c := range []struct {
		site    claimSite
		kept    func() bool
		layout  string
		refused bool
	}{
		{claimSite{text: long, literal: true, width: 120}, never, claimLayoutStringWide, true},
		{claimSite{text: short, literal: true, width: 40}, never, claimLayoutString, false},
		{claimSite{text: "∀x:num. " + strings.Repeat("x + ", 30) + "x = x", literal: true, width: 140}, never, claimLayoutString, false},
		{claimSite{text: long, statement: guarded, width: 120}, never, claimLayoutWide, false},
		{claimSite{text: "∀x:num. x ∈ s ⇒ ∀y:num. y ∈ s ⇒ x ≤ y", statement: interleaved, width: 120}, never, claimLayoutWide, false},
		{claimSite{text: short, statement: guarded, width: 40}, func() bool { return false }, claimLayoutPartsFitting, true},
		{claimSite{text: short, statement: guarded, width: 40}, func() bool { return true }, claimLayoutBinders, false},
		{claimSite{text: "∀x:num. x ≤ x", statement: &dsl.Statement{Binders: "∀x:num.", Conclusion: "x ≤ x"}, width: 40},
			func() bool { return false }, claimLayoutPartsFitting, true},
	} {
		layout, refusal := claimLayoutRefusal(c.site, c.kept)
		if layout != c.layout || (refusal != "") != c.refused {
			t.Errorf("%q (width %d, parts %v): layout %q, refusal %q; want %q, refused %v",
				c.site.text, c.site.width, c.site.statement != nil, layout, refusal, c.layout, c.refused)
		}
	}
	if _, refusal := claimLayoutRefusal(claimSite{text: long, literal: true, width: 120}, never); !strings.Contains(refusal, `Hypotheses: []string{
		"x ∈ `) {
		t.Errorf("the refusal does not print the parts to paste:\n%s", refusal)
	}
	src := []byte("package p\n\nfunc f() {\n\tx := a.Hyp(Statement{\n\t\tConclusion: \"p\",\n\t})\n}\n")
	from := strings.Index(string(src), "Statement{")
	to := strings.Index(string(src), "})") + 1
	if got, want := claimLineWidth(src, from, to, "∀n:num. p"), xugofmt.ContentWidth("\tx := a.Hyp(\"∀n:num. p\")"); got != want || want != 23 {
		t.Errorf("claimLineWidth = %d, want %d (23)", got, want)
	}
}
