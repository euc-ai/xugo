package gates

// zz_witness_probe_test.go — TestZZWitnessOrderProbe, a scratch tool
// (not one of the gates): for one dep, print
// the raw display statement, its normalized install form, and a ground
// cite at distinguishable numerals — the definitive "which author slot
// fills which binder" answer, measured on the engine rather than
// inferred. Use it when a ground cite mis-grounds and the census row
// alone doesn't explain the slot map.

import (
	"context"
	"fmt"
	"os"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
)

// forallPrefixVarsForProbe is forallPrefixNamesForCensus keeping the
// bound VARIABLES rather than just their names — the probe needs each
// binder's TYPE to build a witness the specializer will accept.
func forallPrefixVarsForProbe(t core.Term) []core.VarTerm {
	var vars []core.VarTerm
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			return vars
		}
		vars = append(vars, abs.Var())
		t = abs.Body()
	}
}

func TestZZWitnessOrderProbe(t *testing.T) {
	name := os.Getenv("XUGO_WITNESS_PROBE_DEP")
	if name == "" {
		t.Skip("set XUGO_WITNESS_PROBE_DEP=<registered entry name>")
	}
	env := serve.NewSeedEnv()

	// A registered entry is not in the seed env's LibraryThms — that map
	// holds only the library-convention names the corpus env binds (the
	// induction and recursion principles, the WF schemas). Serve it the
	// way replay's resolveDep does: prefer the entry's own HEADLINE when it has one, since that
	// is the form a cross-family ground cite is read against, and the
	// whole question this probe answers is which author slot fills which
	// binder OF THAT FORM. Without this the probe could not be pointed
	// at the deps whose slot map is hardest to guess — the cross-family
	// ones, whose two chapters name the same sets oppositely.
	if e, ok := registry.ByName(name); ok {
		stmt := e.Statement().Prop
		env.LibraryThms[name] = core.Promise(stmt, func(core.Forcer) core.ThmCert {
			t.Fatalf("probe forced the entry build for %q — statement-only was expected", name)
			return core.ThmCert{}
		})
	}

	// Settle the dep promise from its statement (trust-everything
	// boundary — this probe only needs the statement shape).
	thm, ok := env.LibraryThms[name]
	if !ok {
		t.Fatalf("no LibraryThms entry %q", name)
	}
	cert, _ := core.ForceWithBoundary(context.Background(), thm, func(core.Prop) bool { return true })
	if cert.IsZero() {
		t.Fatalf("ForceWithBoundary yielded nil cert")
	}
	env.LibraryThms[name] = cert
	ctx := proof.NewScript(env)

	// The dep by its name: the probe takes a library-convention name as
	// readily as an entry's, so it claims the cert it just stored rather
	// than spelling an entry for ctx.Dep.
	ctx.ClaimProvedThm(cert)
	raw := cert
	t.Logf("raw dep:        %s", prop.PrintProp(raw))
	norm := ctx.NormalizedThm(raw)
	t.Logf("normalized thm: %s", prop.PrintProp(norm))

	// Ground-cite onto a dummy goal the way the cite verbs do (install
	// + content-locate + Specialize), at distinguishable witnesses —
	// the printed ground hyp shows which author slot fills which
	// binder. NOTE: this path is the LEGACY positional one (no
	// statement-order permutation), so what it prints is the raw
	// install-slot order the permutation maps onto.
	// Witnesses are fresh VARIABLES at each binder's own type, not ℕ
	// numerals: a ℤ-side dep rejects a
	// num witness in Specialize, and a probe passing numerals dies there
	// — a panic inside its own canned cite, before printing the instance
	// it exists to print, on exactly the deps whose slot map is hardest
	// to guess. Distinguishable names answer the slot question at least as
	// well as numerals, and cannot be confused with numerals already in
	// the statement.
	binders := forallPrefixVarsForProbe(norm.AsProp().Conclusion())
	if len(binders) == 0 {
		t.Logf("(no ∀-prefix — nothing to ground)")
		return
	}
	wits := make([]core.Term, len(binders))
	slots := make([]string, len(binders))
	for i, b := range binders {
		wits[i] = ext.Var(ext.TermName(fmt.Sprintf("w%d", i+1)), b.Type())
		slots[i] = fmt.Sprintf("w%d=%s", i+1, string(b.Name()))
	}
	t.Logf("install-slot order: %v", slots)
	goal := ctx.SectionText("0 = 1")
	before := goal.Goal
	goal.CiteSpecialize(norm, wits...)
	after := goal.UnsolvedLeaves()
	t.Logf("goal before: %s", prop.PrintProp(before))
	for _, l := range after {
		t.Logf("goal after:  %s", prop.PrintProp(l.Goal))
	}
}
