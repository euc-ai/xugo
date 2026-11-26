// surface_agreement_test.go — the shared-elaborator commitment (one
// elaborator, two surfaces) as an executable invariant: a statement literal
// validated on the SESSION surface and registered on the GO surface must be
// the same theorem.
//
// The literal-text contract already makes the two surfaces share bytes;
// this battery checks they share MEANING. For every member
// headline (the authoring door), the literal is parsed twice:
//
// - under the family vocabulary (registration's scope — ParseScript), and
// - under the session statement-door scope (the registry's resolver +
// the strict switches, no vocabulary — what add-goal/mint see).
//
// When BOTH parses succeed they must be the same statement — the same key
// after Normalize, the corpus's one identity. A DIVERGENCE — both sides
// accept, different theorems — is the seam the shared elaborator exists to
// kill, and FAILS the test.
//
// One side refusing is NOT a divergence: the session scope knows less
// (no standard frees, no declared coercion domain, no vocabulary
// instances), and under the strict switches it REFUSES what it cannot
// pin instead of silently meaning something else. Refusals are counted
// and logged; the safe direction is exactly the design.
package gates

import (
	"fmt"
	"os"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
)

func TestStatementSurfaceAgreement(t *testing.T) {
	env := serve.NewSeedEnv()

	sessionParse := func(text string) (p core.Prop, perr string) {
		defer func() {
			if r := recover(); r != nil {
				p, perr = nil, trimPanic(r)
			}
		}()
		ctx := proof.NewScript(env)
		ctx.ParseScope.StrictResolution = true
		ctx.ParseScope.StrictMint = true
		ctx.ParseScope.FreshenMetaLetters = true
		return ctx.MakePropText(text), ""
	}

	const (
		skip = iota
		sessionRefused
		agree
		diverge
	)
	// compare reads one headline on both surfaces; a divergence carries
	// the two normal forms it reports.
	type comparison struct {
		verdict     int
		famN, sessN core.Prop
	}
	compare := func(e *registry.ProofEntry) comparison {
		h := e.Build.Headline
		if h == "" || e.Family() == nil {
			return comparison{verdict: skip}
		}
		famProp, _, perr := censusParseHeadline(env, e)
		if perr != "" || famProp == nil {
			return comparison{verdict: skip} // the census owns registration-side parse health
		}
		sessProp, serr := sessionParse(h)
		if serr != "" {
			return comparison{verdict: sessionRefused} // the safe direction, counted
		}
		famN, _ := prop.Normalize(famProp)
		sessN, _ := prop.Normalize(sessProp)
		if sessN.AlphaKey() == famN.AlphaKey() {
			return comparison{verdict: agree}
		}
		return comparison{diverge, famN, sessN}
	}

	var agreed, familyOnly, skipped int
	all := registry.All()
	for i, c := range fanOut(all, compare) {
		switch c.verdict {
		case skip:
			skipped++
		case sessionRefused:
			familyOnly++
		case agree:
			agreed++
		case diverge:
			t.Errorf("SURFACE DIVERGENCE %s: the same literal parses to DIFFERENT theorems\n"+
				"  literal: %s\n  family:  %s\n  session: %s",
				all[i].Name, all[i].Build.Headline, prop.PrintProp(c.famN), prop.PrintProp(c.sessN))
		}
	}
	t.Logf("surface agreement: %d agreed, %d session-refused (safe), %d skipped (bare/sequent/unparsed)",
		agreed, familyOnly, skipped)
}

// TestStatementPrintRoundTrip — the print round-trip, first leg of the
// elaborator's invariant triple, as a standing GATE, corpus-wide: the
// name-faithful printer's output re-parses to the SAME statement (an oracle
// interface must not lie). The printer's recoverability analysis
// (ext.ConstConflictSet) annotates exactly the occurrences the reparse
// could not re-derive; a failure here means an un-annotated unrecoverable
// instance regressed — fix the analysis, never the statement.
func TestStatementPrintRoundTrip(t *testing.T) {
	env := serve.NewSeedEnv()
	// A statement re-parses against the corpus's registry — a chapter
	// statement names only constants chapters define.
	corpusResolver := func(name string) core.ConstTermMeta {
		if meta, ok := env.ProofService.LoadConstMeta(core.TermName(name)); ok {
			return meta
		}
		return core.ConstTermMeta{}
	}
	// Two failure kinds, and they are not the same defect. `lie` is the
	// printed text re-parsing to a DIFFERENT statement — the oracle
	// saying something false, which is what this gate exists to forbid.
	// `gap` is the printed text not re-parsing at all: the printer has
	// no readable spelling for that shape. A gap is loud and harmless
	// (nobody is misled); a lie is silent and not.
	const (
		roundTripOK = iota
		roundTripGap
		roundTripLie
	)
	roundTrips := func(p core.Prop, resolver func(string) core.ConstTermMeta) (kind int, detail string) {
		defer func() {
			if r := recover(); r != nil {
				kind, detail = roundTripGap, "panic: "+trimPanic(r)
			}
		}()
		text := prop.FormatPropForParserNameFaithful(p)
		// FreshenMetaLetters mirrors every REAL door — the registry's
		// statement door, emit, the session, prover/proof and the CLI all
		// set it, so a round trip measured without it measures a
		// configuration nothing parses under. This is the flag's own
		// "doors flip after the corpus diff is measured" (ext/dsl/dsl.go):
		// the diff was the six point-free `iterate` definitions and the
		// eleven word rows whose printed annotation was INCOMPLETE, fixed
		// at the printer (ext/format.go, formatConstTypeAnnotation).
		res := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
			ConstResolver: resolver, FreshenMetaLetters: true})
		if len(res.Errors) > 0 {
			return roundTripGap, "re-parse: " + res.Errors[0].Message + " | " + text
		}
		if res.Prop.AlphaKey() != p.AlphaKey() {
			return roundTripLie, "α-drift | " + text
		}
		return roundTripOK, ""
	}
	var pass, fail int
	var dump strings.Builder
	report := func(door, name, detail string) {
		fail++
		if fail <= 40 {
			t.Logf("ROUNDTRIP %-9s %-40s %s", door, name, detail)
		}
		fmt.Fprintf(&dump, "%s\t%s\t%s\n", door, name, detail)
	}
	// BOTH kinds fail the gate: a shape the printer cannot spell is a
	// shape a headline must not use — it is fixed at the printer or the
	// parser, never counted.
	for _, e := range registry.All() {
		p, perr := censusCallStmt(func() core.Prop { return e.Statement().Prop })
		if perr != "" || p == nil {
			continue // the census owns parse health
		}
		if k, d := roundTrips(p, corpusResolver); k == roundTripOK {
			pass++
		} else {
			report("stmt", e.Name, d)
		}
	}
	t.Logf("print round-trip: %d ok, %d failed", pass, fail)
	if fail > 0 {
		t.Errorf("print round-trip is the layer's invariant: %d statements no longer reproduce", fail)
	}
	if out := os.Getenv("XUGO_ROUNDTRIP_OUT"); out != "" && fail > 0 {
		if err := os.WriteFile(out, []byte(dump.String()), 0o644); err != nil {
			t.Errorf("round-trip dump: %v", err)
		} else {
			t.Logf("full dump: %s", out)
		}
	}
}

// trimPanic renders a recovered panic value for a log line.
func trimPanic(r any) string {
	if err, ok := r.(error); ok {
		return err.Error()
	}
	if str, ok := r.(string); ok {
		return str
	}
	return "non-error panic"
}
