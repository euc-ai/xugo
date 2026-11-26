// strict_census_test.go — the strict-resolution census over every
// registered statement literal (the elaboration design's P1 opening
// move). Report-only: it PASSES whatever it finds; the classified
// counts are the migration baseline for the strict switches, not a
// gate. When the switches land, the statement doors themselves reject
// and this census becomes their regression walker.
//
// Loose resolution never fails on an undeclared name — it freshens: a
// free VarTerm whose type is inferred from context, or a def-less
// DSL-side surface meta at an unpinned instance. Both yield a
// well-formed statement that need not be the statement the author
// meant, with every downstream gate green. The claim/term paths assert
// today (prover/proof: parseClaim, TermText); the statement doors run
// no such check. This census asks the strict question at those doors.
//
// Doors:
//
//	headline: member headline literals, parsed under the
//	 family vocabulary (Statement's route).
//	stmt: statements (entry.Statement — the headline, or a
//	 definition kit's computed statement).
//
// Buckets:
//
//	FRESHENED_FREE a free variable neither the parse scope nor the
//	 text sanctions — the class-1 signature: loose
//	 resolution minted it.
//	OPEN_DECLARED a free variable the family vocabulary DECLARES
//	 (sequent chapters' standard frees) — benign, counted.
//	SEQUENT_FREE a free variable of a statement carrying hypotheses
//	 (a definition door's induction principle) —
//	 sanctioned, counted.
//	SURFACE_META a const resolved to the DSL-side def-less surface
//	 meta: neither vocab nor the ConstMetaManager supplied the name.
//	ORPHAN_SOLO a type variable in exactly ONE const occurrence and
//	 no variable's type — the unpinned-instance signature
//	 (the 𝕌/∅ and bare-poly-head shape).
//	ORPHAN_SHARED an unanchored tyvar shared by several const
//	 occurrences — usually the type-parameter genre
//	 (dimensions), where statements are ABOUT a letter.
//	HYPS a parsed statement carrying hypotheses.
//	PARSEFAIL the literal does not parse at all (note: Statement
//	 is lazy — nothing invokes it at registration, so a
//	 broken literal here otherwise waits for the harness).
//	NOSTMT generated entry with no text-form Stmt.
//
// Full findings dump: set XUGO_CENSUS_OUT=<path> (TSV).
package gates

import (
	"fmt"
	"os"
	"sort"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
)

type censusFinding struct {
	Bucket string
	Door   string
	Entry  string
	Detail string
}

// surfaceFallback is the DSL's def-less fallback meta table, fetched
// once — census compares meta POINTERS against it.
var surfaceFallback = dsl.SurfaceFallbackMetas()

func TestStrictResolutionCensus(t *testing.T) {
	env := serve.NewSeedEnv()

	var findings []censusFinding
	add := func(bucket, door, entry, detail string) {
		findings = append(findings, censusFinding{bucket, door, entry, detail})
	}

	famVarsCache := map[*registry.Family]map[string]core.HolType{}
	famVars := func(f *registry.Family) map[string]core.HolType {
		if f == nil {
			return nil
		}
		if v, ok := famVarsCache[f]; ok {
			return v
		}
		v := f.ParseScript(env).ParseScope.Vars
		famVarsCache[f] = v
		return v
	}

	var headlines, stmts int

	for _, e := range registry.All() {
		fam := e.Family()

		// Door 1: the headline literal under the family vocabulary.
		if h := e.Build.Headline; h != "" && fam != nil {
			headlines++
			hp, declared, perr := censusParseHeadline(env, e)
			if perr != "" {
				add("PARSEFAIL", "headline", e.Name, perr)
			} else {
				censusAnalyze(hp, declared, "headline", e.Name, add)
			}
		}

		// Door 2: the trust-set statement.
		stmts++
		sp, perr := censusCallStmt(func() core.Prop { return e.Statement().Prop })
		if perr != "" {
			add("PARSEFAIL", "stmt", e.Name, perr)
		} else {
			censusAnalyze(sp, famVars(fam), "stmt", e.Name, add)
		}
	}

	// ----- report -------------------------------------------------------

	counts := map[string]int{}
	for _, f := range findings {
		counts[f.Door+"/"+f.Bucket]++
	}
	keys := make([]string, 0, len(counts))
	for k := range counts {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	t.Logf("census: %d headlines, %d chapter stmts parsed", headlines, stmts)
	for _, k := range keys {
		t.Logf("  %-32s %d", k, counts[k])
	}

	// Detail lines for the suspect buckets, capped per bucket. The
	// genre buckets (declared frees, sequent frees, hyp counts, shared
	// orphans) are counted in the summary; the TSV dump has their rows.
	countedOnly := map[string]bool{
		"OPEN_DECLARED": true, "NOSTMT": true,
		"SEQUENT_FREE": true, "HYPS": true, "ORPHAN_SHARED": true,
		"MACHINE_OPEN": true,
	}
	const detailCap = 60
	shown := map[string]int{}
	for _, f := range findings {
		if countedOnly[f.Bucket] {
			continue
		}
		shown[f.Bucket]++
		if shown[f.Bucket] <= detailCap {
			t.Logf("%-14s %-9s %-44s %s", f.Bucket, f.Door, f.Entry, f.Detail)
		}
	}
	for b, n := range shown {
		if n > detailCap {
			t.Logf("%-14s … %d more (set XUGO_CENSUS_OUT for the full dump)", b, n-detailCap)
		}
	}

	if out := os.Getenv("XUGO_CENSUS_OUT"); out != "" {
		var sb strings.Builder
		for _, f := range findings {
			fmt.Fprintf(&sb, "%s\t%s\t%s\t%s\n", f.Bucket, f.Door, f.Entry, f.Detail)
		}
		if err := os.WriteFile(out, []byte(sb.String()), 0o644); err != nil {
			t.Errorf("census dump: %v", err)
		} else {
			t.Logf("full dump: %s (%d findings)", out, len(findings))
		}
	}
}

// TestZZFreshenCensus measures the corpus under FreshenMetaLetters:
// every member headline parses twice — the door's current scope, and
// the same scope with occurrence-local meta letters — and the keys are
// compared. DRIFT rows depended on name capture for their CURRENT
// meaning (the migration list: add the ⟨⟩ tie); FRESHEN_REJECT rows
// stop parsing without capture (same list, louder). INVARIANT is the
// expected bulk: anchors and ties are capture-free by construction.
func TestZZFreshenCensus(t *testing.T) {
	env := serve.NewSeedEnv()
	var invariant, drift, freshenReject, skipped int
	for _, e := range registry.All() {
		h := e.Build.Headline
		if h == "" || e.Family() == nil {
			skipped++
			continue
		}
		normal, _, perr := censusParseHeadline(env, e)
		if perr != "" || normal == nil {
			skipped++
			continue
		}
		var fresh core.Prop
		var ferr string
		func() {
			defer func() {
				if r := recover(); r != nil {
					fresh, ferr = nil, trimPanic(r)
				}
			}()
			ctx := e.Family().ParseScript(env)
			ctx.ParseScope.FreshenMetaLetters = true
			fresh = ctx.MakePropText(h, e.Build.HeadlineConsts...)
		}()
		switch {
		case ferr != "" || fresh == nil:
			freshenReject++
			t.Logf("FRESHEN_REJECT %-44s %s", e.Name, ferr)
		case normal.AlphaKey() == fresh.AlphaKey():
			invariant++
		default:
			drift++
			t.Logf("DRIFT          %-44s %s", e.Name, h)
		}
	}
	t.Logf("freshen census: %d invariant, %d drift, %d freshen-reject, %d skipped",
		invariant, drift, freshenReject, skipped)
}

// censusParseHeadline parses the member's headline literal under the
// family vocabulary and hands back the scope's declared standard frees.
func censusParseHeadline(env *ProverEnv, e *registry.ProofEntry) (
	p core.Prop, declared map[string]core.HolType, perr string) {
	defer func() {
		if r := recover(); r != nil {
			p, perr = nil, trimPanic(r)
		}
	}()
	ctx := e.Family().ParseScript(env)
	declared = ctx.ParseScope.Vars
	p = ctx.MakePropText(e.Build.Headline, e.Build.HeadlineConsts...)
	return p, declared, ""
}

// censusCallStmt invokes a lazy Stmt func under recover.
func censusCallStmt(fn func() core.Prop) (p core.Prop, perr string) {
	defer func() {
		if r := recover(); r != nil {
			p, perr = nil, trimPanic(r)
		}
	}()
	return fn(), ""
}

// censusAnalyze runs the strict-resolution question over one parsed
// statement: undeclared frees (flavor 1), DSL surface-fallback metas
// (flavor 2), and orphan instance type variables (the unpinned-instance
// signature behind the nullary-const and bare-poly-head receipts).
//
// genre marks the sequent/decl form (a turnstile prefix in the entry's
// text, or hypotheses in the parse): its frees are sanctioned in-text,
// so they bucket as SEQUENT_FREE rather than FRESHENED_FREE.
func censusAnalyze(p core.Prop, declared map[string]core.HolType,
	door, entry string, add func(bucket, door, entry, detail string)) {
	if p == nil {
		add("PARSEFAIL", door, entry, "nil statement")
		return
	}
	genre := p.NumHyps() > 0
	if genre {
		add("HYPS", door, entry, fmt.Sprintf("%d hypotheses", p.NumHyps()))
	}
	terms := append([]core.Term{p.Conclusion()}, p.Hyps()...)

	// Flavor 1: free variables vs the scope's declared standard frees.
	freeSeen := map[string]bool{}
	for _, tm := range terms {
		for _, v := range tm.Frees(func(core.VarTerm) bool { return true }) {
			name := string(v.Name())
			if freeSeen[name] {
				continue
			}
			freeSeen[name] = true
			switch {
			case declaredHas(declared, name):
				add("OPEN_DECLARED", door, entry, name+" : "+ext.FormatType(v.Type()))
			case genre:
				add("SEQUENT_FREE", door, entry, name+" : "+ext.FormatType(v.Type()))
			default:
				add("FRESHENED_FREE", door, entry, name+" : "+ext.FormatType(v.Type()))
			}
		}
	}

	vars := map[core.TermKey]core.VarTerm{}
	consts := map[core.TermKey]core.ConstTerm{}
	for _, tm := range terms {
		ext.CollectVars(tm, vars)
		ext.CollectConstTerms(tm, consts)
	}

	// Flavor 2: DSL-side def-less surface metas, by meta POINTER.
	for _, c := range consts {
		if m, ok := surfaceFallback[string(c.Name())]; ok && c.Meta() == m {
			add("SURFACE_META", door, entry, string(c.Name())+" : "+ext.FormatType(c.Type()))
		}
	}

	// Orphan instance type variables: a tyvar carried by const
	// instances but by no variable's type — nothing term-level anchors
	// it. Split by how many distinct const occurrences share the tyvar:
	// a SOLO orphan (one occurrence) is the freshened-instance
	// signature; a SHARED one is usually the type-parameter genre
	// (cardinal.CantorUniv's `card_lt(𝕌⟨A:A⟩, 𝕌⟨A:set(A)⟩)` — a
	// statement ABOUT a type letter, legitimately variable-free), with
	// the both-sides-freshened eq trap hiding in the same bucket. The split is the instrument's
	// honest resolution limit, not a verdict.
	anchored := map[core.TypeKey]bool{}
	for _, v := range vars {
		for _, tv := range v.Type().TypeVars() {
			anchored[tv.Key()] = true
		}
	}
	orphanUses := map[core.TypeKey]int{}
	orphanRows := map[core.TypeKey][]string{}
	for _, c := range consts {
		for _, tv := range c.Type().TypeVars() {
			if anchored[tv.Key()] {
				continue
			}
			orphanUses[tv.Key()]++
			orphanRows[tv.Key()] = append(orphanRows[tv.Key()],
				string(c.Name())+"@"+string(tv.Name())+" in "+ext.FormatType(c.Type()))
		}
	}
	for k, n := range orphanUses {
		bucket := "ORPHAN_SOLO"
		if n > 1 {
			bucket = "ORPHAN_SHARED"
		}
		sort.Strings(orphanRows[k])
		add(bucket, door, entry, strings.Join(orphanRows[k], "; "))
	}
}

// declaredHas is a nil-safe scope-Vars lookup.
func declaredHas(declared map[string]core.HolType, name string) bool {
	if declared == nil {
		return false
	}
	_, ok := declared[name]
	return ok
}
