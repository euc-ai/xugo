package engine

// The replay of an emitted member as emitted: the text EmitSection
// renders is compiled in a scratch package beside this one and its
// Build is run under a fresh corpus env, so a rendering is checked by
// the compiler and the kernel, never by eye. A test emits into a
// scratch family of its own (emitScratchFamily), where every dependency
// is an import and nothing of a chapter's is in reach.

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
)

// emitScratchFamily is the family path a member is emitted into for a
// replay as emitted: its last segment is the scratch package's name.
func emitScratchFamily(pkg string) string { return "zz_emit/" + pkg }

// emitInto renders section 0 of s into emitScratchFamily(pkg) under
// Build_<name>, checking the source parses, and returns it.
func emitInto(t *testing.T, e *Engine, s *Session, pkg, name string) string {
	t.Helper()
	require.True(t, s.sections[0].root.Proved(), "section 0 is proved")
	out, err := e.EmitSection(&EmitSectionRequest{
		SessionID: s.ID, Section: 0, FuncName: "Build_" + name, Family: emitScratchFamily(pkg), IncludePrior: []int{},
	})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	return out.Go
}

// replayEmitted queues src for the compile-and-replay batch TestMain runs
// after the selected tests pass. Each member keeps its own package and
// process: no other fixture's statement enters its trust boundary.
func replayEmitted(t *testing.T, pkg, name, src string) {
	t.Helper()
	replayEmittedUnder(t, ".", pkg, name, src)
}

// replayEmittedWithPhantoms is replayEmitted for a member whose
// signature names the phantom of a type a chapter mints: phantoms is
// the Go file declaring it in the scratch package, as the generated
// wrapper file of the family the member lands in aliases it from its
// owner.
func replayEmittedWithPhantoms(t *testing.T, pkg, name, src, phantoms string) {
	t.Helper()
	replayEmittedUnder(t, ".", pkg, name, src)
	emittedReplays[len(emittedReplays)-1].phantoms = phantoms
}

// replayEmittedUnder is replayEmitted with the scratch package under
// parent, a directory given relative to this one: a member that reads
// an internal chapter compiles only inside that chapter's tree.
func replayEmittedUnder(t *testing.T, parent, pkg, name, src string) {
	t.Helper()
	if !strings.HasPrefix(src, "package "+pkg+"\n") {
		t.Fatalf("the member is not emitted into the scratch package %s:\n%s", pkg, src)
	}
	emittedReplays = append(emittedReplays, _EmittedReplay{test: t.Name(), parent: parent, pkg: pkg, name: name, src: src})
}

type _EmittedReplay struct {
	test, parent, pkg, name, src string
	// phantoms is the scratch package's phantoms.go, "" for none.
	phantoms string
}

var emittedReplays []_EmittedReplay

// replayEmittedBatch shares one Go package-loading and build invocation.
// The replay processes run serially, each forcing its member under the
// same frontier as an individually selected test. A failure fails the
// package even though the rendering assertions have already finished.
func replayEmittedBatch() error {
	if len(emittedReplays) == 0 {
		return nil
	}
	args := []string{"test", "-count=1", "-p", "1", "-timeout", "10m", "-run", "^TestReplayEmitted$"}
	var sources strings.Builder
	for _, r := range emittedReplays {
		dir, err := os.MkdirTemp(r.parent, "zz_emit_"+r.pkg+"_")
		if err != nil {
			return fmt.Errorf("%s: create replay package: %w", r.test, err)
		}
		defer os.RemoveAll(dir)
		files := map[string]string{
			"member.go": r.src,
			"family.go": fmt.Sprintf("package %s\n\nimport \"github.com/euc-ai/xugo/library/registry\"\n\nvar family = registry.NewFamily(%q, nil)\n",
				r.pkg, emitScratchFamily(r.pkg)),
			"replay_test.go": fmt.Sprintf(replayEmittedTest, r.pkg, r.pkg+"."+r.name),
		}
		if r.phantoms != "" {
			files["phantoms.go"] = r.phantoms
		}
		for file, content := range files {
			if err := os.WriteFile(filepath.Join(dir, file), []byte(content), 0o644); err != nil {
				return fmt.Errorf("%s: write replay package: %w", r.test, err)
			}
		}
		args = append(args, "./"+filepath.ToSlash(dir))
		fmt.Fprintf(&sources, "\n--- %s (%s): ---\n%s", r.test, dir, r.src)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Minute)
	defer cancel()
	out, err := exec.CommandContext(ctx, "go", args...).CombinedOutput()
	if err != nil {
		return fmt.Errorf("emitted members do not compile and replay: %w\n%s\n%s", err, out, sources.String())
	}
	fmt.Printf("emitted-member replay (%d fixtures):\n%s", len(emittedReplays), out)
	return nil
}

// replayEmittedTest is the scratch package's test: the member found by
// its registered name, built under a seed env wired as the corpus
// replay wires one — the bundles installed and warmed under the trust
// frontier, every other registered entry served by name as a trusted
// dep is, its statement settled at the frontier, a card as its axiom —
// and forced with that frontier; the member's own proof is the one
// that runs, and its certificate is held to the member's statement.
const replayEmittedTest = `package %s

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
)

func TestReplayEmitted(t *testing.T) {
	member, ok := registry.ByName(%q)
	if !ok {
		t.Fatal("the emitted member is not registered under its name")
	}
	boundary := func(s core.Prop) bool {
		for _, e := range registry.EntriesStating(s) {
			if e != member {
				return true
			}
		}
		return false
	}
	ctx := context.Background()
	serve.InstallProofPolicy()
	serve.InstallNatBundle()
	serve.InstallRealBundle()
	serve.InstallIntBundle()
	serve.InstallStructureRingBundle()
	serve.InstallChaseBundle()
	serve.InstallRecordNormal()
	if _, err := serve.WarmBundles(ctx, boundary); err != nil {
		t.Fatalf("warming the bundles: %%v", err)
	}
	env := serve.NewSeedEnv()
	env.LibraryResolver = func(name string) (proof.Thm, bool) {
		e, ok := registry.ByName(name)
		if !ok {
			e, ok = registry.ByServesAs(name)
		}
		if !ok || e == member {
			return nil, false
		}
		if e.ServedAsAxiom() {
			return serve.EntryAxiom(e), true
		}
		stated := core.Promise(e.Statement().Prop, func(core.Forcer) core.ThmCert {
			panic("the replay trusts every registered statement, so no dependency is built: " + e.Name)
		})
		cert, _ := core.ForceWithBoundary(ctx, stated, boundary)
		return cert, true
	}
	env.Scope = proof.NewProofScope(core.PropKey(member.Key))
	top, built := member.Build.Fn(env)
	for _, s := range built.SectionThms() {
		core.ForceWithBoundary(ctx, s, boundary)
	}
	cert, _ := core.ForceWithBoundary(ctx, top, boundary)
	if says, _ := prop.Normalize(cert); !member.Statement().Normalized().AlphaEquals(says) {
		t.Fatalf("the member's proof yields a certificate of %%s, which is not the member's statement %%s",
			prop.PrintProp(says), prop.PrintProp(member.Statement().Normalized()))
	}
}
`
