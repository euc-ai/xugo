// headline_surface_test.go — the statement-surface gate: a registered
// statement is mathematics, not a normal form (chapter_constitution.md
// §"The headline invariant").
//
// The set-builder sugar parses to exactly the machine encoding —
// `{t | x⃗ | φ}` IS `set_comprehension(λv. ∃x⃗. comprehension_spec(v, φ, t))`, and `{x | φ}`
// its template-equals-binder case — so no public statement ever needs
// to spell set_comprehension, comprehension_spec, or a machine binder. The replay harness
// cannot see the difference (its identity relation is normalized-alpha,
// which the two spellings share), which is why this is a lint and not a
// replay property.
//
// The gate reads the hand-written statement surface the registry
// carries: the constructor headline (Build.Headline — Theorem /
// Sections / Derived members). Interior section statements are out of
// scope by design: a proof may reason about the machine form when that
// form is what it reasons about. Members a definition door computed
// carry no hand-written statement text and have nothing to check here.
//
// A headline that must legitimately mention a banned token — none is
// known; a non-sugarable set_comprehension shape (one not of the canonical
// λ/∃/comprehension_spec form) would be the only candidate — goes in
// headlineSurfaceAllowlist with its reason, and leaves again when the
// need does (the plan's escape rule: narrow census, exit condition).
//
// TestServedStatementSurface holds what a door SERVES for a member to
// the same surface. A member has two texts and every door serves those
// two: the chapter's (registry.ProofEntry.StatementText — `query`,
// `retrieve`, `cards` and the index pages) and the one that reads with
// nothing declared (engine.StatementTypedForEntry at the family's
// statement door — `statement_typed` at `query member`, `query dossier`
// and `cards`). Neither is replay-checked, so a door printing a member
// through a printer of its own, or a print profile spelling the
// comprehension's machine binder, is green everywhere but here. The two
// constants' own definitions state them, and are the only members that
// do. The same test keeps the census of the typed texts served as the
// parser print rather than the chapter's spelling of it
// (servedTypedPrinted): the door reads the print of every statement,
// so a spelling the door refuses is green everywhere but here too. The
// final text, including the author's set-valued binder types, must parse
// at that family's statement door into the same closed statement.
package gates

import (
	"fmt"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/engine"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
)

// headlineSurfaceForbidden are the comprehension encoding's machine
// tokens: the synthesized binder namespace and the two constants the
// set-builder sugar lowers to.
var headlineSurfaceForbidden = []string{"GEN%PVAR%", "comprehension_spec", "set_comprehension"}

// headlineSurfaceAllowlist maps entry name → reason for the one shape
// that may ever legitimately spell a banned token (a non-sugarable
// set_comprehension). Empty today; an addition needs the reason inline and an exit
// condition in the family plan.
var headlineSurfaceAllowlist = map[string]string{}

func TestHeadlineSurface(t *testing.T) {
	surfaces := 0
	for _, e := range registry.All() {
		text := e.Build.Headline
		if text == "" {
			continue
		}
		surfaces++
		for _, tok := range headlineSurfaceForbidden {
			if !strings.Contains(text, tok) {
				continue
			}
			if reason, ok := headlineSurfaceAllowlist[e.Name]; ok {
				t.Logf("allowlisted %s: the headline spells %q — %s", e.Name, tok, reason)
				continue
			}
			t.Errorf("%s: the headline spells the machine surface %q — restate the comprehension "+
				"as {x | φ} / {t | x⃗ | φ} (the sugar lowers to the identical term):\n  %s",
				e.Name, tok, text)
		}
	}
	if surfaces == 0 {
		t.Fatal("no statement surfaces seen — registry enumeration broke, the gate is vacuous")
	}
	t.Logf("checked %d statement surfaces", surfaces)
}

// servedTypedPrinted are the members whose statement_typed is the
// parser print — `var:A`, every node parenthesized, a bundle binder
// spelled as its record and its structure fact — because the chapter's
// spelling of the print does not read back at the family's statement
// door (engine.StatementTypedUnder). Empty today — every member is
// served the chapter's spelling; a row names the spelling rule the
// door refuses, and leaves when the spelling reads back.
var servedTypedPrinted = map[string]string{}

func TestServedStatementSurface(t *testing.T) {
	type _ServedSurface struct {
		text, typed    string
		spelled, ok    bool
		roundTripError string
	}
	all := registry.All()
	surfaces := fanOut(all, func(e *registry.ProofEntry) _ServedSurface {
		typed, ok := engine.StatementTypedForEntry(e)
		surface := _ServedSurface{
			text: e.StatementText(), typed: typed.Text,
			spelled: typed.ChapterSpelling, ok: ok,
		}
		if ok {
			scope := engine.StatementDoorScope(e.Family())
			scope.AbbreviationBinders = map[string]bool{}
			for _, name := range dsl.LeadingBinderNames(typed.Text) {
				scope.AbbreviationBinders[name] = true
			}
			back := dsl.ParsePropTextAtDoor(typed.Text, scope)
			switch {
			case len(back.Errors) > 0:
				surface.roundTripError = fmt.Sprintf("the statement door refuses it: %v", back.Errors)
			case back.Prop.NumHyps() != 0:
				surface.roundTripError = "add-goal requires a closed statement, but the text has hypotheses"
			case back.Prop.AlphaKey() != e.Statement().Prop.AlphaKey():
				surface.roundTripError = "the text parses to a different statement"
			}
		}
		return surface
	})
	members := 0
	for i, e := range all {
		members++
		text, typed, spelled, ok := surfaces[i].text, surfaces[i].typed, surfaces[i].spelled, surfaces[i].ok
		if err := surfaces[i].roundTripError; err != "" {
			t.Errorf("%s: statement_typed does not round-trip: %s\n  %s", e.Name, err, typed)
		}
		if !ok || typed == "" {
			t.Errorf("%s: the member has no statement_typed that reads back at its family's statement door", e.Name)
		}
		if _, printed := servedTypedPrinted[e.Name]; ok && printed == spelled {
			t.Errorf("%s: statement_typed is the chapter's spelling = %v, servedTypedPrinted lists it = %v — the list is the census of "+
				"members served the parser print because the chapter's spelling does not read back; keep it exact:\n  %s", e.Name, spelled, printed, typed)
		}
		for _, s := range []struct{ name, text string }{{"statement", text}, {"statement_typed", typed}} {
			for _, tok := range headlineSurfaceForbidden {
				// The member defining one of the two constants states it.
				if strings.Contains(s.text, tok) && !slices.Contains(e.Defines(), tok) {
					t.Errorf("%s: the served %s spells the machine surface %q:\n  %s", e.Name, s.name, tok, s.text)
				}
			}
		}
	}
	if members == 0 {
		t.Fatal("no members seen — registry enumeration broke, the gate is vacuous")
	}
	t.Logf("checked %d members", members)
}
