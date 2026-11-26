// surface_sweep_test.go — the surface-spelling sweep: a test-gated
// tool (precedent: record_cnf_test.go writes family pbs) that rewrites
// claim literals from MINTED variable spellings (`n₀`/`n_0`) to
// SURFACE spellings (`n`), family by family.
//
//	XUGO_SURFACE_SWEEP='<Family.Name>' go test -run TestSurfaceSweep ./library/integrity/gates/
//	XUGO_SURFACE_SWEEP=ALL go test -run TestSurfaceSweep ./library/integrity/gates/
//
// A rewrite is applied only when ALL of the following hold (the
// library's candidate + safety rules, claim_env_test.go):
//
// - the claim sits in a CLOSED reconstructed environment and reached
// the verb as a direct string literal (const-indirected claims are
// shared text — never spliced);
// - the mint's SurfaceBase is an in-scope RUNTIME-ALIASED binding,
// introduced exactly once (no shadowing), spelled as exactly one
// mint in the claim, in the body (no second spelling anywhere),
// and not itself a declared `.Var`/vocab variable;
// - the STATIC check accepts: original and rewritten text, parsed
// under the runtime's alias model (seeded scope + surface→mint
// core.Substitute — Argument.parseClaim, replicated), denote
// EXACTLY equal terms. Never merely α-equal: the parsed Prop must
// be bit-identical so every recorded CNF key keeps hitting.
//
// Labels: when a claim-bearing call's claim was rewritten, the SAME
// whole-token replacements are applied to that call's label literal
// (display-only, no parse check). Comments are never touched.
//
// Each edited file is re-parsed and formatted (xugofmt) before it is
// written. The per-family replay (XUGO_REPLAY_SCOPE) is the runtime
// oracle on top.
package gates

import (
	"fmt"
	"go/parser"
	"go/token"
	"os"
	"sort"
	"strconv"
	"testing"

	"github.com/euc-ai/xugo/library/xugofmt"
)

// sweepEdit is one literal replacement, in file byte offsets.
type sweepEdit struct {
	off, end int
	text     string // replacement INCLUDING quotes
}

func TestSurfaceSweep(t *testing.T) {
	scope := os.Getenv("XUGO_SURFACE_SWEEP")
	if scope == "" {
		t.Skip("set XUGO_SURFACE_SWEEP=<Family.Name>|ALL to run the sweep (it rewrites proof files)")
	}
	env := claimLintEnv()
	scopes := newClaimScopeCache(env)
	col := collectEnvSites(t, scopes)
	bodyMints := envBodyMints(col, scopes)

	if scope != "ALL" {
		known := false
		for _, s := range col.sites {
			if s.fam != nil && s.fam.Name == scope {
				known = true
				break
			}
		}
		if !known {
			t.Fatalf("XUGO_SURFACE_SWEEP=%q matches no registered family with claim sites "+
				"(the scope is Family.Name, e.g. nat_num/nat_gcd)", scope)
		}
	}

	type stat struct{ rewritten, labels, skipped int }
	perFamily := map[string]*stat{}
	skipReasons := map[string]int{}
	edits := map[string][]sweepEdit{} // file → edits
	var editedFiles []string

	for _, s := range col.sites {
		if s.env == nil || s.lit == nil {
			continue
		}
		if scope != "ALL" && s.fam.Name != scope {
			continue
		}
		famScope := scopes.scope(s.fam)
		scriptVars := col.scriptVars[s.dir]
		out := envSeededParse(famScope, scriptVars, s)
		cands := envSweepCandidates(s, out, bodyMints[s.bodyID], famScope, scriptVars)
		if len(cands) == 0 {
			continue
		}
		st := perFamily[s.fam.Name]
		if st == nil {
			st = &stat{}
			perFamily[s.fam.Name] = st
		}
		newText, applied := envRewriteText(s.text, cands)
		if len(applied) == 0 {
			continue
		}
		ok, reason := envSweepCheck(famScope, scriptVars, s, newText, cands)
		if !ok {
			st.skipped++
			skipReasons[reason]++
			t.Logf("skip %s: %s claim %q: %s", s.where(), s.verb, s.text, reason)
			continue
		}
		st.rewritten++
		if len(edits[s.file]) == 0 {
			editedFiles = append(editedFiles, s.file)
		}
		edits[s.file] = append(edits[s.file], sweepEdit{
			off:  col.fset.Position(s.lit.Pos()).Offset,
			end:  col.fset.Position(s.lit.End()).Offset,
			text: strconv.Quote(newText),
		})
		// The same replacements on the call's label, display-only.
		if s.labelLit != nil {
			if label, isString := xugofmt.StringValue(s.labelLit); isString {
				newLabel, labelApplied := envRewriteText(label, cands)
				if len(labelApplied) > 0 {
					st.labels++
					edits[s.file] = append(edits[s.file], sweepEdit{
						off:  col.fset.Position(s.labelLit.Pos()).Offset,
						end:  col.fset.Position(s.labelLit.End()).Offset,
						text: strconv.Quote(newLabel),
					})
				}
			}
		}
	}

	sort.Strings(editedFiles)
	for _, f := range editedFiles {
		if err := sweepApplyEdits(f, edits[f]); err != nil {
			t.Fatalf("apply edits to %s: %v", f, err)
		}
		t.Logf("rewrote %s (%d literal(s))", f, len(edits[f]))
	}

	for _, fam := range envSortedKeys2(perFamily) {
		st := perFamily[fam]
		t.Logf("sweep %-28s rewritten %3d (labels %d), skipped %d", fam, st.rewritten, st.labels, st.skipped)
	}
	for _, r := range envSortedKeys(skipReasons) {
		t.Logf("sweep skip reason: %-50s %3d", r, skipReasons[r])
	}
}

func envSortedKeys2[V any](m map[string]V) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

// sweepApplyEdits splices the edits into the file (descending offset),
// verifies the result parses, formats it (xugofmt), and writes it.
func sweepApplyEdits(file string, edits []sweepEdit) error {
	src, err := os.ReadFile(file)
	if err != nil {
		return err
	}
	sort.Slice(edits, func(i, j int) bool { return edits[i].off > edits[j].off })
	for i, e := range edits {
		if e.off < 0 || e.end > len(src) || e.off >= e.end {
			return fmt.Errorf("edit %d out of range (%d..%d of %d)", i, e.off, e.end, len(src))
		}
		if i > 0 && e.end > edits[i-1].off {
			return fmt.Errorf("edit %d overlaps its neighbor", i)
		}
		src = append(src[:e.off], append([]byte(e.text), src[e.end:]...)...)
	}
	if _, err := parser.ParseFile(token.NewFileSet(), file, src, 0); err != nil {
		return fmt.Errorf("edited source no longer parses: %v", err)
	}
	formatted, err := xugofmt.Source(src)
	if err != nil {
		return fmt.Errorf("format of edited source: %v", err)
	}
	return os.WriteFile(file, formatted, 0o644)
}
