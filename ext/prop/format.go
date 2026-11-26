package prop

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

const (
	latexIndent    = "\\quad"
	latexTurnstile = "\\vdash"
)

func formatProp(t Prop, latex bool) string {
	Assert(t != nil)

	s := ""
	if t.NumHyps() > 0 {
		hyps := make([]string, t.NumHyps())
		for i := range t.NumHyps() {
			hyps[i] = ext.FormatTerm(t.Hyp(i), latex)
			if latex {
				hyps[i] = fmt.Sprintf("&%s", hyps[i])
			}
		}
		if latex {
			s = fmt.Sprintf("%s\\\\&%s", strings.Join(hyps, ",\\\\"), latexIndent)
		} else {
			s = fmt.Sprintf("%s\n\t", strings.Join(hyps, ",\n"))
		}
	}
	proves := utils.TurnstileStr + " "
	if latex {
		proves = latexTurnstile
	}
	return fmt.Sprintf("%s%s%s", s, proves, ext.FormatTerm(t.Conclusion(), latex))
}

func PrintProp(t Prop) string { return formatProp(t, false) }

func LatexProp(t Prop) string { return formatProp(t, true) }

// FormatPropForParser renders a Prop in a form parsable by
// dsl.ParsePropTextInScope. Differs from PrintProp in three ways:
//
//   - No leading "⊢ " when the prop has no hypotheses and no free
//     variables (the latter triggers the decl prelude — see below).
//   - Quantifier-bound vars carry `:type` annotations
//     (∀m:num. … rather than ∀m. …) so the parser doesn't need
//     bound-var inference (a separate deferred work item).
//   - Free variables (whose types the parser cannot infer from the
//     hypothesis/conclusion expression alone) are declared as
//     `name : type` entries in the decl prelude before ⊢, e.g.
//     `B1 : num, B2 : num, hyp1, hyp2 ⊢ concl`. Without this prelude,
//     hyps/conclusions like `∀n. (dest_nadd(x, n) ≤ … + B1)`
//     trip the parser's "variable B1 has no type declaration"
//     diagnostic and fail to round-trip.
//
// Hypotheses, when present, are rendered as a comma-joined list
// before the turnstile, matching the parser grammar
// `decls "⊢" expr` where each decl is either `name : type` or a
// hypothesis expression. The free-var cleaning pass that formatProp
// uses is replicated here so the printed text mirrors what an
// alpha-key compare would see.
func FormatPropForParser(t Prop) string {
	return formatPropForParserImpl(t, ext.FormatTermForParserInConflicts, true)
}

// FormatPropForParserNoDecls is FormatPropForParser with the free-variable
// decl prelude OMITTED — the text states only mathematical content
// (hypotheses, when present, still precede the turnstile).
//
// It is parsable ONLY against a scope whose Vars already carry the free
// variables' types — i.e. after Script.Var has declared them. Use it when
// the consumer emits those declarations alongside the text (the chapter
// charter's rule: types are declared in Go, the blessed string is
// mathematics). Without matching declarations the parser rejects the text
// with "variable X has no type declaration"; it does not silently guess.
func FormatPropForParserNoDecls(t Prop) string {
	return formatPropForParserImpl(t, ext.FormatTermForParserInConflicts, false)
}

// FormatPropForParserNameFaithful is FormatPropForParser with the
// name-faithful term profile: print shorthands that DROP bound-variable
// names (the `{x | φ}` / `{t | x | φ}` set-builders, whose set_comprehension
// λ-binder is re-synthesized position-derived at parse) are disabled, so
// parse(print(t)) reproduces t's binder names exactly, not just its
// α-class. The one binder no text can spell faithfully — one shadowing
// a same-named different-typed free variable — prints under
// ext.RenameShadowedBinders' variant, α-equal and capture-free, rather
// than leaving the statement without a text at all.
//
// Use for REPLAY-PARSED proof payloads (emit's SectionText / MakePropText
// forms): recorded steps re-derive fresh-variable names via
// RenameToAvoid over ALL names in the goal — bound included — so a
// bound-binder rename can leak into a FREE variable's name downstream
// (the funext `ẋ` → `ẋʹ` class of cardinality.HasSizeUnions) and diverge goal
// α-keys from the recorded protos. α-consumed surfaces (registry Stmt_
// texts, display comments) keep the sugared FormatPropForParser.
func FormatPropForParserNameFaithful(t Prop) string {
	return formatPropForParserImpl(t, ext.FormatTermForParserInConflictsNameFaithful, true)
}

// FormatPropForParserNameFaithfulNoDecls combines the two variants above:
// the name-faithful term profile (for replay-parsed payloads) with the
// decl prelude omitted (for scopes that declare their frees via
// Script.Var). See FormatPropForParserNoDecls for the scope requirement.
func FormatPropForParserNameFaithfulNoDecls(t Prop) string {
	return formatPropForParserImpl(t, ext.FormatTermForParserInConflictsNameFaithful, false)
}

// declareFrees selects whether free variables are declared in the prelude
// (`B1 : num, … ⊢ concl`) or left to the parse scope.
func formatPropForParserImpl(
	t Prop,
	formatTerm func(core.Term, map[core.TermName]bool) string,
	declareFrees bool,
) string {
	Assert(t != nil)

	// Conflict set spans the WHOLE prop: hyps and conclusion parse
	// against one shared scope, so a const name at different instances
	// across two terms needs annotations in both — a term-local set
	// (plain FormatTermForParser) would leave the single-instance term
	// bare and let the parser resolve it at the other term's instance.
	terms := make([]core.Term, 0, t.NumHyps()+1)
	terms = append(terms, t.Conclusion())
	for i := range t.NumHyps() {
		terms = append(terms, t.Hyp(i))
	}
	conflicts := ext.ConstConflictSet(terms...)

	concl := formatTerm(t.Conclusion(), conflicts)

	// Collect free-var decls in stable order: first appearance across
	// (conclusion, hyp0, hyp1, …). Map to dedupe by name.
	seen := map[core.TermName]bool{}
	var decls []string
	collectFrees := func(term core.Term) {
		for _, v := range term.Frees(nil) {
			name := v.Name()
			if seen[name] {
				continue
			}
			seen[name] = true
			decls = append(decls,
				fmt.Sprintf("%s:%s", string(name), ext.FormatType(v.Type())))
		}
	}
	if declareFrees {
		collectFrees(t.Conclusion())
		for i := range t.NumHyps() {
			collectFrees(t.Hyp(i))
		}
	}

	if t.NumHyps() == 0 && len(decls) == 0 {
		return concl
	}

	parts := decls
	for i := range t.NumHyps() {
		parts = append(parts, formatTerm(t.Hyp(i), conflicts))
	}
	return strings.Join(parts, ", ") + " " + utils.TurnstileStr + " " + concl
}

func AddTab(s string) string {
	lines := strings.Split(s, "\n")
	newlines := make([]string, len(lines))
	for i, l := range lines {
		newlines[i] = "\t" + l
	}
	return strings.Join(newlines, "\n")
}

func PrintVarsInProp(t Prop) (string, string) {
	vars := make(map[core.TermKey]VarTerm)
	ext.CollectVars(t.Conclusion(), vars)
	for h := range t.HypIter() {
		ext.CollectVars(h, vars)
	}
	varsList := make([]string, 0, len(vars))
	varsLatexList := make([]string, 0, len(vars))
	for _, v := range vars {
		varsList = append(varsList,
			fmt.Sprintf("%s:%s", v.Name(), ext.FormatType(v.Type())))
		varsLatexList = append(varsLatexList,
			fmt.Sprintf("%s:%s", ext.FormatTerm(v, true), ext.FormatType(v.Type())))
	}
	return strings.Join(varsList, "\n"), strings.Join(varsLatexList, "\n")
}

func PrintConstsInProp(t Prop) (string, string) {
	consts := make(map[core.TermKey]ConstTerm)
	ext.CollectConstTerms(t.Conclusion(), consts)
	for h := range t.HypIter() {
		ext.CollectConstTerms(h, consts)
	}
	constsList := make([]string, 0, len(consts))
	constsLatexList := make([]string, 0, len(consts))
	for _, c := range consts {
		constsList = append(constsList,
			fmt.Sprintf("%s:%s", c.Name(), ext.FormatType(c.Type())))
		constsLatexList = append(constsLatexList,
			fmt.Sprintf("%s:%s", ext.FormatTerm(c, true), ext.FormatType(c.Type())))
	}
	return strings.Join(constsList, "\n"), strings.Join(constsLatexList, "\n")
}
