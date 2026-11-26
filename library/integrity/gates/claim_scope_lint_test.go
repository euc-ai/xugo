// claim_scope_lint_test.go — B3: the claim-variable SCOPE lint, on top
// of the static binding-reconstruction library (claim_env_test.go).
//
// B3 — CLAIM FREE VARIABLES ARE IN SCOPE. For every claim literal
// whose environment the library reconstructs (a CLOSED env), each free
// variable name of the parsed claim must be accounted for by one of:
//
// - an in-scope binding's surface name (closure param, Obtain
// witness, in-body Fix, Denote/Binder-introduced name);
// - a mint spelling whose SurfaceBase is an in-scope binding
// (`n₀`/`n_0` for a bound `n` — both spellings are legal at
// runtime, derive.go §"Surface names");
// - a family-vocab variable (the chapter's standard frees) or a
// Script-level `.Var("name", …)` registration of the file;
// - a constant (a built-in or a chapter mint) — which never shows up
// here, because a name that resolves as a const does not parse as a
// free variable.
//
// Anything else is a finding: the shape a typo'd variable (or a claim
// referencing a mint of a DIFFERENT section) parses into.
//
// Discipline (B0/B1/B2's): measured corpus-wide; the class gates only
// at zero findings or all-confirmed-defects, otherwise it ships as a
// census. Unknown/OPEN regions are skipped silently (counted, not
// judged). The instrument guard proves the detector can fire.
//
// TestClaimSweepableCensus is the sweep's worklist: closed-env claims
// carrying mint spellings whose base is unambiguous in scope — exactly
// the population TestSurfaceSweep (surface_sweep_test.go) rewrites —
// reported per family.
package gates

import (
	"fmt"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
)

// envScopeFindings runs the B3 classification over one site. Returns
// findings (unaccounted names) and census notes.
func envScopeFindings(scope *dsl.ParseScope, vocab, scriptVars map[string]bool, site *envSite) (findings, census []string) {
	out := envSeededParse(scope, scriptVars, site)
	errStr := ""
	if out.panicked != "" {
		errStr = "panic: " + out.panicked
	} else if len(out.res.Errors) > 0 {
		e := out.res.Errors[0]
		errStr = fmt.Sprintf("[%s] %s", e.Code, e.Message)
	}
	if errStr != "" {
		if out.panicked == "" && out.res.Errors[0].Code == dsl.CodeMissingType {
			if m := missingTypeVar.FindStringSubmatch(out.res.Errors[0].Message); m != nil {
				if envNameKnown(site, m[1], vocab, scriptVars) {
					census = append(census, fmt.Sprintf("known name %q is statically untypable (%s)", m[1], errStr))
					return findings, census
				}
				findings = append(findings, fmt.Sprintf("free name %q is not in scope (%s)", m[1], errStr))
				return findings, census
			}
		}
		if site.verb == "Term" {
			census = append(census, "term literal does not type statically: "+errStr)
		} else {
			census = append(census, "claim does not parse under the reconstructed env: "+errStr)
		}
		return findings, census
	}
	for _, name := range envFreeNames(out, site.verb == "Term") {
		if !envNameKnown(site, name, vocab, scriptVars) {
			findings = append(findings, fmt.Sprintf("free name %q is not in scope", name))
		}
	}
	return findings, census
}

// TestLintClaimVarScope is B3. Ships as a census unless the corpus
// measures clean — see the file header's gate rule.
func TestLintClaimVarScope(t *testing.T) {
	env := claimLintEnv()
	scopes := newClaimScopeCache(env)
	col := collectEnvSites(t, scopes)

	// Instrument guard: a claim over an unknown free name, in a closed
	// env binding something else, must produce a finding.
	probeStmt := dsl.ParsePropText("∀n:num. n = n")
	if len(probeStmt.Errors) > 0 {
		t.Fatalf("instrument guard: probe statement failed to parse: %v", probeStmt.Errors)
	}
	abs := ext.MatchesFORALL(probeStmt.Prop.AsProp().Conclusion())
	if abs.IsZero() {
		t.Fatalf("instrument guard: probe statement lost its ∀")
	}
	probeSite := &envSite{
		verb: "Have", text: "n + zzNoSuchVar = n",
		env: &envSnap{bindings: []envBinding{{name: "n", typ: abs.Var().Type(), aliased: true}}},
	}
	pf, _ := envScopeFindings(&dsl.ParseScope{}, map[string]bool{}, map[string]bool{}, probeSite)
	if len(pf) == 0 {
		t.Fatalf("instrument guard: the scope check did not flag zzNoSuchVar")
	}
	// And the mint spelling of the bound name must be ACCEPTED.
	mintSite := &envSite{verb: "Have", text: "n₀ + n = n + n₀", env: probeSite.env}
	if mf, _ := envScopeFindings(&dsl.ParseScope{}, map[string]bool{}, map[string]bool{}, mintSite); len(mf) != 0 {
		t.Fatalf("instrument guard: the mint spelling of a bound base was flagged: %v", mf)
	}

	namedObtainGuard(t, scopes)

	closed, open := 0, 0
	openReasons := map[string]int{}
	censusKinds := map[string]int{}
	var findings []string
	for _, s := range col.sites {
		if s.env == nil {
			open++
			reason := s.openReason
			if reason == "" {
				reason = "(unclassified)"
			}
			openReasons[reason]++
			continue
		}
		closed++
		vocab := scopes.vocabVars(s.fam)
		f, c := envScopeFindings(scopes.scope(s.fam), vocab, col.scriptVars[s.dir], s)
		for _, msg := range f {
			findings = append(findings, fmt.Sprintf("%s: %s claim %q: %s", s.where(), s.verb, s.text, msg))
		}
		for _, msg := range c {
			key, _, _ := strings.Cut(msg, ":")
			censusKinds[key]++
		}
	}
	t.Logf("B3: %d claim sites in CLOSED envs checked; %d sites in open/unclassified regions skipped", closed, open)
	for _, k := range envSortedKeys(openReasons) {
		t.Logf("B3 open: %-58s %4d", k, openReasons[k])
	}
	for _, k := range envSortedKeys(censusKinds) {
		t.Logf("B3 census (not gated): %-45s %4d", k, censusKinds[k])
	}
	// GATED at zero. A finding here is an out-of-scope name in a claim —
	// the typo'd variable shape, or a claim leaning on another section's
	// mint.
	sort.Strings(findings)
	for _, f := range findings {
		t.Errorf("B3 finding: %s", f)
	}
	t.Logf("B3 findings (out-of-scope claim names): %d", len(findings))
}

// namedObtainGuardSource is an Obtain whose Named marker spells its
// witness ζ: the runtime binds ζ alone and not the claim's binder ξ,
// and a marker of anything but literals leaves the names unknown.
const namedObtainGuardSource = `package arith

var Guard = family.Theorem("∀P:(num → bool). (∃m:num. P(m)) ⇒ (∃m:num. P(m))",
	func(a *Argument, P Term, h Fact) {
		a.Obtain("a witness", "∃ξ:num. P(ξ)", By(h), Named("ζ"))
		a.Term("suc(ζ)")
		a.Term("suc(ξ)")
		a.Obtain("a second witness", "∃ξ:num. P(ξ)", By(h), Named(spelling))
		a.Term("suc(suc(ζ))")
	})
`

// namedObtainGuard walks namedObtainGuardSource and holds the walker to
// the runtime: ζ in scope and ξ not after the marker, B3 accepting a
// term spelling ζ and flagging one spelling ξ, and the env OPEN after a
// non-literal marker.
func namedObtainGuard(t *testing.T, scopes *claimScopeCache) {
	col := envWalkSource(t, scopes, "nat_num/nat_arith", namedObtainGuardSource)
	byText := map[string]*envSite{}
	for _, s := range col.sites {
		byText[s.text] = s
	}
	given, binder, unread := byText["suc(ζ)"], byText["suc(ξ)"], byText["suc(suc(ζ))"]
	if given == nil || binder == nil || unread == nil {
		t.Fatalf("instrument guard: the Named guard's claims were not all collected (%d sites)", len(col.sites))
	}
	if given.env == nil || binder.env == nil {
		t.Fatalf("instrument guard: a literal Named marker opened the env (%s)", given.openReason)
	}
	if given.env.lookup("ζ") == nil || given.env.lookup("ξ") != nil {
		t.Fatalf("instrument guard: a Named(\"ζ\") witness must bind ζ alone, not the claim's binder ξ")
	}
	vocab := scopes.vocabVars(given.fam)
	if vocab["ζ"] || vocab["ξ"] {
		t.Fatalf("instrument guard: ζ or ξ is a family vocabulary variable — the guard cannot see the binding")
	}
	scope := scopes.scope(given.fam)
	if f, _ := envScopeFindings(scope, vocab, nil, given); len(f) != 0 {
		t.Fatalf("instrument guard: the Named witness's own spelling was flagged: %v", f)
	}
	if f, _ := envScopeFindings(scope, vocab, nil, binder); len(f) == 0 {
		t.Fatalf("instrument guard: the claim's binder ξ, which a Named marker does not bind, was not flagged")
	}
	if unread.env != nil {
		t.Fatalf("instrument guard: a Named marker of a non-literal name left the env closed")
	}
}

func envSortedKeys(m map[string]int) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

// TestClaimSweepableCensus reports the sweep worklist: closed-env
// claims carrying mint spellings whose base is unambiguously in scope.
func TestClaimSweepableCensus(t *testing.T) {
	env := claimLintEnv()
	scopes := newClaimScopeCache(env)
	col := collectEnvSites(t, scopes)
	bodyMints := envBodyMints(col, scopes)

	perFamily := map[string]int{}
	perFamilyMintTotal := map[string]int{}
	sweepable, closedWithMints, openWithMints := 0, 0, 0
	for _, s := range col.sites {
		hasMintToken := false
		for _, tk := range envTokenize(s.text) {
			if b := proof.SurfaceBase(tk.norm); b != tk.norm && b != "" {
				hasMintToken = true
				break
			}
		}
		if s.env == nil {
			if hasMintToken {
				openWithMints++
			}
			continue
		}
		if !hasMintToken {
			continue
		}
		closedWithMints++
		perFamilyMintTotal[s.fam.Name]++
		out := envSeededParse(scopes.scope(s.fam), col.scriptVars[s.dir], s)
		cands := envSweepCandidates(s, out, bodyMints[s.bodyID], scopes.scope(s.fam), col.scriptVars[s.dir])
		if len(cands) == 0 || s.lit == nil {
			continue
		}
		sweepable++
		perFamily[s.fam.Name]++
	}
	for _, fam := range envSortedKeys(perFamilyMintTotal) {
		t.Logf("sweepable census: %-28s %3d sweepable of %3d closed claims carrying mint spellings",
			fam, perFamily[fam], perFamilyMintTotal[fam])
	}
	t.Logf("sweepable census totals: %d sweepable / %d closed-with-mints / %d open-with-mints (unreachable)",
		sweepable, closedWithMints, openWithMints)
}
