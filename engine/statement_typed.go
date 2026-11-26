package engine

import (
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
)

// FormatStatementTyped renders a goal in the parse-faithful text-DSL
// profile and returns it ONLY when the print → parse → α-key round-trip
// closes. It is the engine-side answer to the "display strings do not
// round-trip" gap: the plain `statement` display drops quantifier type
// annotations and the free-var declaration prefix, and the text-DSL
// parser (single-pass, left-to-right, no unification) cannot recover
// them — so a printed statement pasted back into `add-goal {text}`
// fails with "ill-typed term" whenever a bare variable's first
// occurrence precedes its type-pinning occurrence (e.g. `y ∈ t`).
//
// The renderer is prop.FormatPropForParser, the sugared parser profile:
// quantifier binders carry `:type`, free variables get a declaration
// prelude before ⊢ (`s:(var:A → bool), …`), constants at conflicting
// instantiations carry explicit ⟨⟩ annotations, and a set-builder or a
// paired lambda reads as one (`{x:A | φ}`, `λ(x:A, y:B). t`). Those two
// shorthands drop the name of the encoding's own binder, which the
// parse re-synthesizes — so the text is the goal's α-class, not its
// binder names, and that is what its consumer needs: a pasted text
// makes a NEW goal whose names are its own, and the steps recorded on
// it are recorded against those. The texts a replay re-parses against
// an existing recording are emit's payloads, and emit prints them
// itself in the name-faithful profile with a syntactic check
// (library/emit tryTextForm).
//
// Validation is the consumer's own reading: the text is re-parsed in
// the scope the add-goal text path parses with (StatementDoorScope —
// one constructor for the door and for this check) and must come back
// α-equal to the input. A prop with no text the door reads back (a
// const no registry knows, a parser-unsupported shape, an `&` no
// operand anchors under a family that declares no domain, …) returns
// ("", false) and the caller omits the field — an absent
// `statement_typed` means "the door reads no print of this", never
// "here is a text that parses into something else", and a served one
// is never a text the door refuses. This is the typed text under no
// family — the nil output door (spelling.go); a session's or an
// entry's texts go through theirs.
func FormatStatementTyped(goal core.Prop) (string, bool) {
	return FormatStatementTypedUnder(goal, nil)
}

// FormatStatementTypedUnder is FormatStatementTyped in a chapter's
// spelling, read at the statement door of a session bound to family
// (nil: bound to none). The chapter's spelling comes first: with the
// family's instance bindings for implicit structure arguments, the
// components the chapter's scope reads back are dropped from the text
// and the chapters' declared notations fold their constants
// (ext/dsl/outfix.go); nil still drops the components a statement
// binds itself — a structure law's ∀-prefix. Where that text does not
// read back to the goal, the parser print itself is served if it does.
// The short text can read where the print does not: the print spells a
// bound component in full (`vec_zero(&0)`), and an `&` standing alone
// in an argument has no anchor at a door that declares no domain.
// Either text is then put in the surface form (dsl.SurfaceForm: sets
// as set(τ), redundant instance ties and numeric embeddings dropped) where that reads
// back too. Spelling.Typed is this behind the output door; Spelling.Prop
// is the display's reading, which has no key to check against.
func FormatStatementTypedUnder(goal core.Prop, family *registry.Family) (string, bool) {
	typed, ok := StatementTypedUnder(goal, family)
	return typed.Text, ok
}

// StatementTyped is a statement's typed text and which text it is.
type StatementTyped struct {
	Text string
	// ChapterSpelling reports the text is the chapter's spelling of the
	// parser print — which may coincide with the print, for a statement
	// with nothing to fold; false where the print itself is served
	// because the spelling did not read back at the statement door.
	ChapterSpelling bool
}

// StatementTypedUnder is FormatStatementTypedUnder reporting besides
// which text it served. The gate over the served surfaces keeps the
// census of the members served the print (library/integrity/gates,
// TestServedStatementSurface): the print is a text the door reads, and
// a spelling rule the door refuses is a defect of the rule or the door.
func StatementTypedUnder(goal core.Prop, family *registry.Family) (StatementTyped, bool) {
	if goal == nil {
		return StatementTyped{}, false
	}
	scope := StatementDoorScope(family)
	reads := func(text string) bool {
		res := dsl.ParsePropTextAtDoor(text, scope)
		return len(res.Errors) == 0 && res.Prop.AlphaKey() == goal.AlphaKey()
	}
	text := prop.FormatPropForParser(goal)
	if short, err := dsl.ChapterSpelling(text, constSyntax(), scope.ImplicitBindings); err == nil && reads(short) {
		return StatementTyped{Text: dsl.SurfaceForm(short, reads), ChapterSpelling: true}, true
	}
	if reads(text) {
		return StatementTyped{Text: dsl.SurfaceForm(text, reads)}, true
	}
	return StatementTyped{}, false
}

// EntryStatementTyped is a landed entry's statement_typed: its typed
// text at its family's statement door (FormatStatementTypedUnder), each
// binder typed as the entry's authored text (StatementText) types it
// where the author spelled a set: a binder of type `τ → bool` the
// author wrote `set(τ)` prints `set(τ)` — the type the printer writes
// as an arrow, and the fold rule (dsl.RespellSets) leaves one when the
// binder is never applied (`∀S:(num → set(I))` handed whole to a
// constant). The respelled text is served where it reads back as the
// statement; "" when the door reads no print of it.
func EntryStatementTyped(entry *registry.ProofEntry) string {
	typed, _ := StatementTypedForEntry(entry)
	return typed.Text
}

// StatementTypedForEntry returns the entry's served text and its spelling
// classification in one pass, including the author's set-valued binder types.
func StatementTypedForEntry(entry *registry.ProofEntry) (StatementTyped, bool) {
	stated := entry.Statement().Prop
	typed, ok := StatementTypedUnder(stated, entry.Family())
	if !ok {
		return StatementTyped{}, false
	}
	scope := StatementDoorScope(entry.Family())
	reads := func(text string) bool {
		res := dsl.ParsePropTextAtDoor(text, scope)
		return len(res.Errors) == 0 && res.Prop.AlphaKey() == stated.AlphaKey()
	}
	typed.Text = setBindersAsAuthored(typed.Text, entry.StatementText(), reads)
	return typed, true
}

// setBindersAsAuthored respells text's binder types as authored spells
// them where authored writes a set: the binders are paired by name and
// by occurrence among that name's binders, and a type authored spells
// with `set(…)` replaces text's spelling of it. The result is kept only
// where reads accepts it, and where either text is not the verbatim
// normalized spelling the binder spans index (dsl.AnalyzeSetSpelling)
// text stands as it is.
func setBindersAsAuthored(text, authored string, reads func(string) bool) string {
	got, want := dsl.AnalyzeSetSpelling(text), dsl.AnalyzeSetSpelling(authored)
	if len(got.Errors) > 0 || len(want.Errors) > 0 || !got.Verbatim || !want.Verbatim {
		return text
	}
	byName := map[string][]dsl.SetBinder{}
	for _, b := range want.Binders {
		byName[b.Name] = append(byName[b.Name], b)
	}
	type splice struct {
		start, end int
		text       string
	}
	var splices []splice
	seen := map[string]int{}
	spliced := map[int]bool{}
	for _, b := range got.Binders {
		k := seen[b.Name]
		seen[b.Name]++
		source := byName[b.Name]
		if k >= len(source) || spliced[b.TypeStart] {
			continue
		}
		if spelled := source[k].TypeText; spelled != b.TypeText && strings.Contains(spelled, "set(") {
			spliced[b.TypeStart] = true
			splices = append(splices, splice{b.TypeStart, b.TypeEnd, spelled})
		}
	}
	if len(splices) == 0 {
		return text
	}
	sort.Slice(splices, func(i, j int) bool { return splices[i].start > splices[j].start })
	out := text
	for _, s := range splices {
		out = out[:s.start] + s.text + out[s.end:]
	}
	if !reads(out) {
		return text
	}
	return out
}
