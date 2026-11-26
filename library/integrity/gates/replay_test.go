// replay_test.go — the replay harness (hand-written, committed):
// CORPUS-WIDE TRUST + ONE PROCESS PER FAMILY + PARALLEL FAMILIES via
// per-family subprocess fanout.
//
// - CARDS. A member stated without a proof (registry.Family.Card) has
// nothing to replay: its subtest is skipped, and a member citing it is
// served the card's axiom (resolveDep) — the corpus-wide trust below,
// made permanent for the cards. The cards gate checks what a card must
// be; `xugo cards` lists the frontier.
//
// - CORPUS-WIDE TRUST. An entry's force trusts every other
// entry's statement (settled via the trust boundary; their builders
// never run; self excluded). Every entry is kernel-verified by its own
// force, so trusting it by statement here is sound and
// bounds force at the corpus boundary instead of cascading through
// every transitive arith-foundation lemma pulled in by Arith() /
// NatBundle. An entry's statement is ProofEntry.Statement —
// elaborated once per process, no LibraryThms required.
//
// - ONE PROCESS PER FAMILY. Each family runs in its OWN re-exec of the
// test binary (XUGO_REPLAY_FAMILY=<family>), replaying its entries
// one after another in registration order.
// A process per family rather than per entry because the process
// floor — linking and initializing the corpus, installing the lemma
// bundles — is about a CPU-second, more than half of a typical entry's
// cost, and a family pays it once.
//
// What sharing a process means. A force bounded at the trust frontier
// settles every ROOT promise it reaches whose statement is trusted, and
// the cell stays settled for the rest of the process (core/force.go,
// _PromiseCell.force). The cells an entry's force reaches are its own
// fresh promises (resolveDep's) and the PROCESS-GLOBAL ones: the
// installed lemma bundles' cells, whose statements are foundation
// entries of this corpus. So an entry's force may find a global cell
// the warm-up or a sibling's force settled from its statement — a cell
// holding the entry's OWN statement among them, which its own frontier
// does not trust. The certificate says so either way: it carries every
// statement it was settled on, whichever force settled the cell and
// whenever, and the assumptions check below refuses a member whose
// certificate stands on its own statement or on anything outside its
// recorded edges. The order a family's entries replay in therefore
// decides nothing.
//
// The lemma bundles are warmed first (warmBundles): every bundle field's
// root promise is settled under the same trust frontier before any
// entry's force runs, because core.deriveProp makes a derivation lazy
// the moment a dependency is an unforced promise, and in a fresh process
// every bundle field is one — the first arithmetic-heavy entry otherwise
// builds its whole proof as a lazy DAG retained until its force (eudoxus_slope.Mul
// alone: 4.4 s and a 1.4 GB live heap against 2 s and 200 MB warm). A
// field no corpus theorem backs fails the child by name
// (serve.WarmBundles).
//
// A hang still names its entry: a per-entry watchdog in the child
// writes the entry's failure and exits with every goroutine dumped
// (entryDeadline). A crash ends the family's process, and the entries
// it had not reached are reported NOT RUN, never green. A panic an
// entry's replay recovers (replayOne) fails that entry and the family
// goes on: a cell settles only with a completed certificate, so what
// a cut-short build leaves behind is kernel-backed or absent.
//
// - ASSUMPTIONS. A certificate lists the statements it stands on that
// no rule derived (core's ThmCert.Assumes): the dependencies the
// frontier trusted, the bundle roots the warm-up settled, a card's
// axiom. A replayed member's certificates are held to its recorded
// edges by that list (checkAssumptions): each assumption is the
// statement of an entry in the member's dependency cone or in the
// foundation of a capability recorded there, never the member's own,
// never a TestThm. The dependency and capability records are what the
// build was observed to read; this is what the kernel saw it stand on,
// and an edge the record lacks fails here.
//
// - PARALLEL. t.Parallel() lets the parent fan out family subprocesses,
// at most replayParallelism() at once (half the machine's cores unless
// -test.parallel is given), largest families first so the longest
// serial run starts earliest. Every entry is still its own subtest
// under its family (`TestReplayAll/<family path>/<entry>`): the child
// writes one record per entry and the parent turns each into a subtest,
// so every -run spelling below selects exactly what it names.
//
// Why forcing is the real correctness check (not just Build + a contract
// assertion): forcing each section to a kernel certificate is what
// surfaces a circular dependency as a failure (a cycle cannot bottom out
// in kernel axioms). As the corpus grows this is the self-bootstrapping
// replay the plan's terminal goal describes.
//
// Self-contained. Every constant a proof mentions is an engine built-in
// or a chapter's mint (registry.ConstMetaManager); an entry proof's deps are
// the entries it declares, resolved here (resolveDep) and pre-loaded
// into env.LibraryThms.
//
// The corpus is chapter packages only (library/proofs/<domain>/<family>/, entry vars —
// pulled in via library/proofs/proofs.go's blank imports), all consumed through
// the central registry package. Every subtest is named
// <family>/<NAME>, and every entry's CNF cache is its FAMILY's shared
// blob (Family.CNF), installed env-side here before Build — proof
// files never call InstallCNFCache themselves (lint-enforced). The
// family recorder is the only recording path.
//
// Narrow to one proof (the parent reads the -run pattern's element at
// the entry's level and hands it to the family's child, so the first
// form replays that one entry and nothing around it):
//
//	go test ./library/integrity/gates/ -run 'TestReplayAll/<family>/<NAME>$'
//	# family-scoped: -run 'TestReplayAll/<family>/'
//	# or via the child entry-point directly (registry name):
//	XUGO_REPLAY_ONE=<name> go test ./library/integrity/gates/ -run TestReplayAll
//
// Narrow to what a LANDING can have affected — its families/entries plus
// every entry that cites them (see envReplayScope for why one hop
// is the whole coupling, and for the four changes that still need the
// whole corpus):
//
//	XUGO_REPLAY_SCOPE='nat_num/nat_arith,sets/set_order' \
//	 go test -count=1 ./library/integrity/gates/ -run TestReplayAll
//
// Unlike a -run filter, an unresolvable token here is FATAL rather than
// vacuous, and the selection size is logged — by t.Logf, so it prints
// only under -v.
package gates

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"slices"
	"sort"
	"strings"
	"sync"
	"testing"
	"time"
	"unicode"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/library/serve/testenv"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
)

// envReplayOne names the child-mode entry to replay — in a process of
// its own, the door every author's one-member verify uses.
const envReplayOne = "XUGO_REPLAY_ONE"

// envReplayFamily names the child-mode family to replay: its entries in
// registration order, one process. The parent fanout's door.
const envReplayFamily = "XUGO_REPLAY_FAMILY"

// envReplayEntries, set alongside envReplayFamily, narrows the child to
// a comma-separated subset of the family's registered entry names — the
// parent's scope (envReplayScope) and the -run pattern's entry element,
// applied child-side so a one-entry -run replays one entry and not the
// family around it. Unset means every entry.
const envReplayEntries = "XUGO_REPLAY_ENTRIES"

// envReplayResults, set alongside envReplayFamily, names the file the
// child appends one JSON line per entry to (replayRecord): `started`
// before the entry's replay, then `ok` or `fail`. The parent reads it
// back into per-entry subtests, so an entry the child never finished —
// a crash, the watchdog — is reported as such, never as green.
const envReplayResults = "XUGO_REPLAY_RESULTS"

// entryDeadline bounds one entry's replay inside a family's process: the
// watchdog (replayFamilyByName) names the hung entry. A one-entry run
// (envReplayOne) has the test binary's timeout.
const entryDeadline = 300 * time.Second

// envDumpSteps, set alongside envReplayOne, prints the
// replayed member's proof tree — every node's ministep and goal, in
// preorder — the way the session's dump-section reads a lineage. It
// is the instrument that tells WHICH leaf of a member mints a key:
// the By step's description names its closer family, not whether the
// apply rung or the refuter closed the leaf, and the recorder's
// "recorded N CNF proto(s)" counts without locating.
const envDumpSteps = "XUGO_DUMP_STEPS"

// envReplayScope narrows the PARENT fanout to a subset of the
// corpus: a comma-separated list of family names ("nat_num/nat_arith") and/or
// registered entry names ("nat_arith.AddSym"). Each token is expanded with
// its DIRECT CONSUMERS — every entry whose dependencies (DepEntries,
// recorded or declared) include it.
//
// Why a subset is sound, and why one hop is enough. Under corpus-wide
// trust an entry reaches another entry ONLY through that entry's
// STATEMENT: resolveDep declares the dep's promise at its statement,
// which the frontier trusts, and ForceWithBoundary
// settles there without running the dep's builder. So a change to an
// entry's proof BODY is invisible to every other entry, and a change to
// its STATEMENT can only reach the entries that cite it. Those consumers'
// own statements are their own declarations and do not move when a dep's
// does — so the coupling does not propagate a second hop.
//
// The three changes this does NOT cover, which need the whole corpus:
// framework edits (this harness, registry, family.go, prover/core/corpus);
// a change to the statement of an entry a serve bundle binds — the rows
// of serve.InstallIntBundle's omega.IntBridges, and of the nat, real and
// int-lemma bundles alike: a consumer reaches such a row through a
// capability token, reads no entry for it, and this scope does
// not select it; and a policy-witness regeneration whose diff touches
// keys outside the landed members.
const envReplayScope = "XUGO_REPLAY_SCOPE"

// replayScopeFromEnv resolves envReplayScope into the set of
// registered entry names to replay — nil meaning "the whole corpus".
// An unresolvable token is fatal rather than empty: a selection that
// silently matches nothing reports `ok` and reads as a pass, which is
// the documented footgun of the -run spelling this env var replaces.
func replayScopeFromEnv(t *testing.T) map[string]bool {
	spec := strings.TrimSpace(os.Getenv(envReplayScope))
	if spec == "" {
		return nil
	}
	all := registry.All()
	seeds := scopeEntries(t, envReplayScope, spec)
	selected := make(map[string]bool, len(seeds))
	for n := range seeds {
		selected[n] = true
	}
	consumers := 0
	for _, e := range all {
		if selected[e.Name] {
			continue
		}
		for _, d := range e.DepEntries() {
			if seeds[d.Name] {
				selected[e.Name] = true
				consumers++
				break
			}
		}
	}
	t.Logf("%s=%q → %d of %d entries (%d selected + %d direct consumers)",
		envReplayScope, spec, len(selected), len(all), len(seeds), consumers)
	return selected
}

// scopeEntries resolves a scope — family names and registered entry
// names, separated by commas or whitespace — into the set of entry
// names it names: a family's every member, an entry itself. env names
// the variable the scope was read from, for the refusals. An
// unresolvable token is fatal rather than empty, and so is a scope
// that names nothing.
func scopeEntries(t *testing.T, env, spec string) map[string]bool {
	t.Helper()
	all := registry.All()
	byFamily := make(map[string][]*registry.ProofEntry, 32)
	registered := make(map[string]bool, len(all))
	for _, e := range all {
		fam := e.Family().Name
		byFamily[fam] = append(byFamily[fam], e)
		registered[e.Name] = true
	}
	named := make(map[string]bool, len(all))
	// Tokens are separated by commas or whitespace — a family name has
	// neither, so both spellings read the same list.
	separator := func(r rune) bool { return r == ',' || unicode.IsSpace(r) }
	for _, tok := range strings.FieldsFunc(spec, separator) {
		if fam, ok := byFamily[tok]; ok {
			for _, e := range fam {
				named[e.Name] = true
			}
			continue
		}
		if registered[tok] {
			named[tok] = true
			continue
		}
		families := make([]string, 0, len(byFamily))
		for f := range byFamily {
			families = append(families, f)
		}
		sort.Strings(families)
		t.Fatalf("%s: %q is neither a family name nor a registered entry name "+
			"(tokens are separated by commas or whitespace; an entry name carries its family prefix — `nat_arith.AddSym`, not `AddSym`).\n"+
			"  families: %s", env, tok, strings.Join(families, " "))
	}
	if len(named) == 0 {
		t.Fatalf("%s=%q resolved to no entries", env, spec)
	}
	return named
}

func TestReplayAll(t *testing.T) {
	if len(registry.All()) == 0 {
		t.Skip("no proofs yet")
	}

	// Child mode, one entry: a single entry's replay, picked by env var —
	// an author's one-member verify.
	if name := os.Getenv(envReplayOne); name != "" {
		// Whistle-free invariant — same contract as TestReplayAll: no
		// stored proof may ever meet a divergence-whistle backstop. The
		// check is deferred, so the cuts are reported when the replay
		// ends the test itself as well.
		whistle := openWhistleGate()
		defer func() {
			whistle.close()
			if n, cuts := whistle.fired(); n != 0 {
				t.Errorf("replay must be whistle-free; the divergence whistle fired %d time(s):%s", n, cuts)
			}
		}()
		replayOneByName(t, name)
		return
	}

	// Child mode, one family: its entries in registration order, one
	// process.
	if name := os.Getenv(envReplayFamily); name != "" {
		replayFamilyByName(t, name)
		return
	}

	// Parent mode: re-exec this binary once per family. Each child
	// replays that family's selected entries and writes a record per
	// entry; the parent turns the records into subtests.
	self, err := os.Executable()
	if err != nil {
		t.Fatalf("os.Executable: %v", err)
	}
	scope := replayScopeFromEnv(t)
	type familyJob struct {
		fam   *registry.Family
		batch []*registry.ProofEntry
	}
	var jobs []familyJob
	inFamilies := 0
	for _, fam := range registry.Families() {
		inFamilies += len(fam.Entries())
		entryFilter := runPatternEntryFilter(t, fam)
		job := familyJob{fam: fam}
		for _, e := range fam.Entries() {
			if scope != nil && !scope[e.Name] {
				continue
			}
			if entryFilter != nil && !entryFilter.MatchString(e.Name) {
				continue
			}
			job.batch = append(job.batch, e)
		}
		if len(job.batch) == 0 {
			continue
		}
		jobs = append(jobs, job)
	}
	if inFamilies != len(registry.All()) {
		t.Fatalf("the families hold %d entries and the registry %d — an entry outside every family would replay nowhere",
			inFamilies, len(registry.All()))
	}
	// Largest batch first: parallel subtests start in registration
	// order, and the longest serial run bounds the wall clock.
	sort.SliceStable(jobs, func(i, j int) bool { return len(jobs[i].batch) > len(jobs[j].batch) })
	// A subtest holds one of the slots while its child runs, so at most
	// replayParallelism() children run at once.
	slots := make(chan struct{}, replayParallelism())
	for _, job := range jobs {
		job := job
		// A family's subtest is its FULL domain path (`-run
		// TestReplayAll/nat_num/nat_arith`): -run matches the pattern's
		// /-separated parts against the subtest name's. The child env
		// vars take registered names, family prefix included —
		// registry.ByName is keyed on them and Family.Add prefixes every
		// entry, so a bare name reports "not in proof registry".
		t.Run(job.fam.Name, func(t *testing.T) {
			t.Parallel()
			slots <- struct{}{}
			defer func() { <-slots }()
			replayFamilyChild(t, self, job.fam, job.batch)
		})
	}
}

// defaultReplayParallelism is how many replay children run at once when
// -test.parallel is not given: half the machine's cores, at least one.
// Memory bounds the fan-out before cores do — a child's peak heap is most
// of a gigabyte (childEnv's GOGC=400 headroom), and fourteen children on
// a 14-core, 24 GB machine drove it into memory compression — and other
// sessions on the same machine share that memory.
func defaultReplayParallelism() int {
	return max(runtime.NumCPU()/2, 1)
}

// replayParallelism is how many replay children the parent runs at
// once: -test.parallel when it was given (`go test -parallel N`),
// defaultReplayParallelism otherwise.
func replayParallelism() int {
	n := defaultReplayParallelism()
	flag.Visit(func(f *flag.Flag) {
		if f.Name == "test.parallel" {
			n = f.Value.(flag.Getter).Get().(int)
		}
	})
	return n
}

// childEnv is the environment every replay child runs under. A child's
// heap is mostly the linked corpus, and at the default GOGC the
// collector is about half of its CPU. GOGC=400 buys that back for a
// doubled peak heap — measured on one family's 14-way per-entry fan-out:
// 37% less CPU, 31% less wall; the heaviest member's peak RSS 0.6 →
// 1.2 GB — and the memory limit caps what a family's run accumulates
// across its entries and what a pathological member reaches.
func childEnv(pairs ...string) []string {
	return append(append(os.Environ(), pairs...), "GOGC=400", "GOMEMLIMIT=2GiB")
}

// replayFamilyChild re-execs this binary on one family's batch and turns
// the child's records into one subtest per entry. The child's timeout is
// a backstop only: the watchdog inside it names a hung entry at
// entryDeadline.
func replayFamilyChild(t *testing.T, self string, fam *registry.Family, batch []*registry.ProofEntry) {
	resultsPath := filepath.Join(t.TempDir(), "results.jsonl")
	names := make([]string, len(batch))
	for i, e := range batch {
		names[i] = e.Name
	}
	args := []string{
		"-test.run", "^TestReplayAll$",
		"-test.timeout", (time.Duration(len(batch)+1) * entryDeadline).String(),
	}
	if testing.Verbose() {
		args = append(args, "-test.v")
	}
	cmd := exec.Command(self, args...)
	cmd.Env = childEnv(
		envReplayFamily+"="+fam.Name,
		envReplayEntries+"="+strings.Join(names, ","),
		envReplayResults+"="+resultsPath,
	)
	out, runErr := cmd.CombinedOutput()
	records := readReplayResults(t, resultsPath)
	if runErr != nil {
		t.Errorf("family %s: child failed: %v\n%s", fam.Name, runErr, out)
	}
	for _, e := range batch {
		e := e
		t.Run(e.Name, func(t *testing.T) {
			if e.ServedAsAxiom() {
				t.Skip("stated without a proof (a card, or the postulate), served as its axiom")
			}
			rec, ok := records[e.Name]
			switch {
			case !ok:
				t.Errorf("replay %s (%s): NOT RUN — the family child exited before reaching it (%v)",
					e.Name, e.Key, runErr)
			case rec.State == "started":
				t.Errorf("replay %s (%s): the family child died while replaying it (%v); its output is on the family's failure",
					e.Name, e.Key, runErr)
			case rec.State == "fail":
				t.Errorf("replay %s (%s) failed: %s", e.Name, e.Key, rec.Error)
			default:
				t.Logf("%.2fs", rec.Seconds)
			}
		})
	}
}

// replayFamilyByName is the family child's entry: look up the family,
// select its entries, and replay them in registration order, a watchdog
// per entry and a record per entry.
func replayFamilyByName(t *testing.T, name string) {
	installBundles()
	var fam *registry.Family
	for _, f := range registry.Families() {
		if f.Name == name {
			fam = f
			break
		}
	}
	if fam == nil {
		t.Fatalf("%s=%q: not a registered family (the full name — `nat_num/nat_arith`)", envReplayFamily, name)
	}
	var only map[string]bool
	if spec := os.Getenv(envReplayEntries); spec != "" {
		only = make(map[string]bool)
		for _, n := range strings.Split(spec, ",") {
			only[n] = true
		}
	}
	results := openReplayResults(t)
	defer results.close()
	frontier := corpusFrontier()
	warmBundles(t, frontier)

	for _, e := range fam.Entries() {
		if only != nil && !only[e.Name] {
			continue
		}
		e := e
		if e.ServedAsAxiom() {
			// A card or the postulate has no proof to replay: it is
			// served as its axiom to every member citing it (resolveDep),
			// the parent reports it skipped, and the cards gate checks
			// what a card must be.
			t.Run(e.Name, func(t *testing.T) {
				t.Skip("stated without a proof (a card, or the postulate), served as its axiom")
			})
			continue
		}
		t.Run(e.Name, func(t *testing.T) {
			results.write(replayRecord{Entry: e.Name, Key: e.Key, State: "started"})
			watchdog := time.AfterFunc(entryDeadline, func() {
				results.write(replayRecord{Entry: e.Name, Key: e.Key, State: "fail",
					Error: fmt.Sprintf("exceeded %s", entryDeadline)})
				fmt.Fprintf(os.Stderr, "replay %s (%s): exceeded %s — the family child exits; every goroutine follows\n",
					e.Name, e.Key, entryDeadline)
				pprof.Lookup("goroutine").WriteTo(os.Stderr, 1)
				os.Exit(2)
			})
			defer watchdog.Stop()

			// Whistle-free invariant, attributed to the entry.
			whistle := openWhistleGate()
			defer whistle.close()

			var failures []string
			start := time.Now()
			err := replayOne(t, e, frontier)
			seconds := time.Since(start).Seconds()
			if err != nil {
				failures = append(failures, err.Error())
			}
			if n, cuts := whistle.fired(); n != 0 {
				failures = append(failures, fmt.Sprintf(
					"replay must be whistle-free; the divergence whistle fired %d time(s):%s", n, cuts))
			}
			if len(failures) > 0 {
				msg := strings.Join(failures, "\n")
				results.write(replayRecord{Entry: e.Name, Key: e.Key, State: "fail", Seconds: seconds, Error: msg})
				t.Errorf("replay %s (%s) failed: %s", e.Name, e.Key, msg)
				return
			}
			results.write(replayRecord{Entry: e.Name, Key: e.Key, State: "ok", Seconds: seconds})
		})
	}
}

// corpusFrontier is the trust frontier: a statement some entry states.
// Each entry is kernel-verified by its own force, in its family's
// process, so trusting it by statement is sound and bounds
// force at the corpus boundary; self is excluded inside replayOne
// (exceptSelf). A statement is elaborated once per process
// (ProofEntry.Statement), needs no LibraryThms, and is the form a cited
// entry's promise is declared at (resolveDep), so the one statement per
// entry is the whole boundary. Every statement is read here, before a
// force asks. What a force asks of a statement is answered by comparing
// it with the entries' statements, never by its key alone
// (registry.EntriesStating).
func corpusFrontier() func(core.Prop) bool {
	for _, e := range registry.All() {
		e.Statement()
	}
	return registry.SomeEntryStates
}

// exceptSelf is frontier without the statement of top, the theorem the
// member under verification built: the member runs its own work, and
// every other entry is verified by its own force.
func exceptSelf(frontier func(core.Prop) bool, top core.Prop) func(core.Prop) bool {
	return func(s core.Prop) bool { return frontier(s) && !s.AlphaEquals(top) }
}

// runPatternEntryFilter returns the -run pattern's element at the
// family's entry level, compiled, or nil when the pattern stops before
// it. Go matches a -run pattern element by element against a subtest
// name's /-separated parts (testing/match.go; splitRegexp is its
// splitter), and the parent hands the entry element to the family's
// child so `-run 'TestReplayAll/<family path>/<entry>$'` replays that
// entry and nothing around it. Go filters the reporting subtests by the
// same element, so a disagreement between the two readings would show
// as a NOT RUN entry, never a silent pass.
func runPatternEntryFilter(t *testing.T, fam *registry.Family) *regexp.Regexp {
	f := flag.Lookup("test.run")
	if f == nil || f.Value.String() == "" {
		return nil
	}
	elems := splitRegexp(f.Value.String())
	level := 1 + len(strings.Split(fam.Name, "/")) // TestReplayAll / <family parts> / <entry>
	if level >= len(elems) {
		return nil
	}
	re, err := regexp.Compile(elems[level])
	if err != nil {
		t.Fatalf("-run %q: element %q: %v", f.Value.String(), elems[level], err)
	}
	return re
}

// splitRegexp splits a -run pattern at the slashes outside brackets and
// parentheses — Go's own splitter (testing/match.go), so an alternation
// spanning a slash reads here as it does there.
func splitRegexp(s string) []string {
	a := make([]string, 0, strings.Count(s, "/"))
	cs := 0
	cp := 0
	for i := 0; i < len(s); {
		switch s[i] {
		case '[':
			cs++
		case ']':
			if cs--; cs < 0 { // An unmatched ']' is legal.
				cs = 0
			}
		case '(':
			if cs == 0 {
				cp++
			}
		case ')':
			if cs == 0 {
				cp--
			}
		case '\\':
			i++
		case '/':
			if cs == 0 && cp == 0 {
				a = append(a, s[:i])
				s = s[i+1:]
				i = 0
				continue
			}
		}
		i++
	}
	return append(a, s)
}

// replayRecord is one line of a family child's results file.
type replayRecord struct {
	Entry   string  `json:"entry"`
	Key     string  `json:"key"`
	State   string  `json:"state"` // started | ok | fail
	Seconds float64 `json:"seconds,omitempty"`
	Error   string  `json:"error,omitempty"`
}

// replayResults appends records to the child's results file. nil when
// no file was named (a direct XUGO_REPLAY_FAMILY invocation), and
// every method is nil-safe.
type replayResults struct {
	mu sync.Mutex
	f  *os.File
}

func openReplayResults(t *testing.T) *replayResults {
	path := os.Getenv(envReplayResults)
	if path == "" {
		return nil
	}
	f, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_APPEND, 0o644)
	if err != nil {
		t.Fatalf("%s=%q: %v", envReplayResults, path, err)
	}
	return &replayResults{f: f}
}

func (r *replayResults) write(rec replayRecord) {
	if r == nil {
		return
	}
	line, err := json.Marshal(rec)
	if err != nil {
		panic(err)
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	if _, err := r.f.Write(append(line, '\n')); err != nil {
		panic(err)
	}
}

func (r *replayResults) close() {
	if r != nil {
		r.f.Close()
	}
}

// readReplayResults reads a child's results file back: the LAST record
// per entry, so an entry's `started` is superseded by its verdict and
// stands alone when the child died on it.
func readReplayResults(t *testing.T, path string) map[string]replayRecord {
	data, err := os.ReadFile(path)
	if err != nil && !os.IsNotExist(err) {
		t.Fatalf("reading %s: %v", path, err)
	}
	last := make(map[string]replayRecord)
	for _, line := range strings.Split(string(data), "\n") {
		if strings.TrimSpace(line) == "" {
			continue
		}
		var rec replayRecord
		if err := json.Unmarshal([]byte(line), &rec); err != nil {
			t.Errorf("results file %s: unreadable line %q: %v", path, line, err)
			continue
		}
		last[rec.Entry] = rec
	}
	return last
}

// installBundles installs the process-global proof policy and every
// corpus lemma bundle an entry can reach. Every harness in this
// package calls it — the replay child, the CNF recorder and the
// recurate probe — and that is the point: one sequence, where copies
// would drift.
//
// Every omission in it fails the same silent way, which is why the drift is
// expensive. A missing bundle does not make the corresponding capability
// FORBIDDEN, it makes it un-installed: `capabilitySpec` misses,
// `ProofScope.allowsInstalled` returns false, the matching `ArithPolicy` field
// stays false however the entry was declared, and the closer then declines
// with a bare `ministep <X> failed` naming only the leaf. Nothing points at
// the harness.
//
// A capability installed in the replay harness alone breaks recording with
// nothing noticing: the members that use it already hold their pb keys, so no
// recording run needs the bundle until a new member does, and that member is
// green at replay and cannot be recorded. The single call site closes the
// class: a new capability has one place to be added.
//
// Ordering is load-bearing and is documented per install below. Idempotent
// process-globals throughout (corpus.envOnce + the SetXLemmaBundle pattern),
// so calling it per entry-subprocess is safe.
func installBundles() {
	// Proof policy: NewProofScope applies each target's complete-graph
	// verdict (the capabilities the canonical graph denies it). The table
	// lives corpus-side (library/integrity/policy) and is installed, not
	// imported — so a missing install would not fail loudly, it would
	// silently skip the indirect-cycle check. Assert it landed.
	serve.InstallProofPolicy()
	if !proof.ProofPolicyInstalled() {
		panic("replay harness: proof policy not installed — the indirect-cycle " +
			"verdicts in NewProofScope would silently go unapplied")
	}
	// Nat: entries (the replayed one or a transitive dep) have
	// arithmetic-bottoming subgoals that omega's `Arith` ministep closes
	// through the bundle; without it they panic "omega: bundle-nil leaf …
	// no test placeholder fabricator is installed".
	serve.InstallNatBundle()
	// Real: same shape as nat. Entry constructors carry their target and
	// capability declarations in a lexical ProofScope, so foundation theorems
	// exclude circular bundle dispatch without ambient target state.
	serve.InstallRealBundle()
	// Int: the homomorphism bridges Script.IntOfRealDerive rewrites through,
	// plus the per-source `int_of_real:<REAL key>` capabilities. A ℤ member
	// whose proof is a lift declares one of those. Must follow the real
	// bundle: the bridge proofs themselves run on real arith.
	serve.InstallIntBundle()
	// There is no word bundle: the words chapters close through the
	// ordinary channels — cites, def-unfold, omega — because their
	// statements are born at the `val` layer, where peeling the word TYPE
	// has no work object. Their replays here are what keeps that ground
	// honest.
	// The LEMMA bundle is what installs `arith:int` itself (serve/int_bundle.go's
	// InstallDependencyCapability(CapabilityArithInt, …) sits inside it), and
	// it panics without InstallIntBundle above it. divides.CoprimeLMod is the
	// first entry to declare that capability.
	serve.InstallIntLemmaBundle()
	// Structure ring: the algebra chapters' general laws and the
	// carrier instances (ℂ) the ring at a comm_ring / field fact reads.
	serve.InstallStructureRingBundle()
	// Diagram chase: the carrier laws a ByChase close is derived from,
	// installed as the manifest and the CLI install them, so a member
	// that closes a step by ByChase replays and records here as it
	// closes in a session.
	serve.InstallChaseBundle()
	// Record normal form: the record equations an instance is computed
	// with where it is handed over (prover/tactic, InstanceNormal).
	serve.InstallRecordNormal()
}

// warmBundles settles every installed bundle field under the corpus
// trust frontier (file header, "The lemma bundles are warmed first").
// Runs after installBundles, in every harness that installs: a field no
// corpus theorem backs fails the run here by name.
func warmBundles(t *testing.T, trusted func(core.Prop) bool) {
	t.Helper()
	report, err := serve.WarmBundles(context.Background(), trusted)
	if err != nil {
		t.Fatalf("%v", err)
	}
	t.Logf("bundle warm-up: %s", report)
}

// replayOneByName is the one-entry child's entry: look up `name` in
// the proof registry, build the corpus-wide trust set, and run
// replayOne.
func replayOneByName(t *testing.T, name string) {
	installBundles()

	entry, found := registry.ByName(name)
	if !found {
		t.Fatalf("XUGO_REPLAY_ONE=%q: not in proof registry", name)
	}
	if entry.ServedAsAxiom() {
		t.Skipf("%s is stated without a proof (a card, or the postulate), served as its axiom; nothing to replay", name)
	}
	frontier := corpusFrontier()
	warmBundles(t, frontier)
	// Say what is being replayed. A correct child run's output was
	// otherwise byte-identical to a run that did nothing — bare
	// "--- PASS: TestReplayAll" even under -v — so the primary
	// verify command could not evidence itself, and authors re-checked
	// through the -run filter form, whose own failure mode (a wrong
	// prefix matching nothing) is the silent one.
	t.Logf("replaying entry %s (%s)", entry.Name, entry.Key)
	if err := replayOne(t, entry, frontier); err != nil {
		t.Errorf("replay %s (%s) failed: %v", entry.Name, entry.Key, err)
	}
}

// resolveDep returns the kernel certificate for a cited dep. The
// realized cert is pre-loaded into env.LibraryThms before the citing
// proof's Build runs; its own correctness is covered by its own replay.
//
// The force is BOUNDED by the same corpus-wide trust set the citing
// proof itself uses — so resolving a dep whose statement is in the set
// settles it from its statement instead of running its Build. Sound:
// the dep's own replay is what kernel-verifies it.
//
// **Entry→entry recursion.** `e.Build(env)` requires THAT entry's
// own deps pre-loaded in `env.LibraryThms` — the Build
// contract. We satisfy that here by recursively resolving each sub-dep
// into the same env before the Build call, so a multi-layer chain
// works without manual ordering; with the trust set covering every
// statement, the recursion bottoms out at the trust boundary
// at the lowest statement that matches, not at kernel axioms.
func resolveDep(ctx context.Context, env *proof.ProverEnv, e *registry.ProofEntry,
	trust func(core.Prop) bool) (proof.ThmCert, error) {
	cert, _ := core.ForceWithBoundary(ctx, dependencyPromise(env, e), trust)
	if cert.IsZero() {
		return proof.ThmCert{}, fmt.Errorf("dep %q ForceWithBoundary yielded nil cert", e.Name)
	}
	return cert, nil
}

// dependencyPromise leaves a dependency's force to its caller, so a nested
// dependency uses the builder's Forcer and inherits its trust boundary.
func dependencyPromise(env *proof.ProverEnv, e *registry.ProofEntry) core.Thm {
	// A card or the postulate is served as its axiom, exactly as the
	// corpus seam serves it to a session (library/serve): there is no
	// Build to wrap. The citing proof replays standing on it; the corpus
	// is sound relative to its postulate and its cards.
	if e.ServedAsAxiom() {
		return serve.EntryAxiom(e)
	}
	// **Why a Promise wrapper around Build.** Build is EAGER — it runs
	// every section of the proof, even for transitive deps that the
	// trust set could settle by statement alone. Wrapping the Build in
	// `core.Promise(stmt, builder)` defers the work to force time;
	// `ForceWithBoundary` then checks the trust set FIRST and, if the
	// statement is trusted, settles directly from the statement without
	// running the builder (core/force.go: _PromiseCell.force).
	//
	// The promise is declared at the entry's statement — the form the
	// entry's own file signs, binder order included, which is what
	// ground-cite witness tuples are read against
	// (prover/proof/witness_order.go). The frontier trusts it, and the
	// settle gate α-checks the built theorem against it.
	return core.Promise(e.Statement().Prop, func(f core.Forcer) core.ThmCert {
		// Sub-deps are resolved only when the trust check at force time
		// DID NOT short-circuit; for a trusted statement this whole
		// closure is skipped.
		for _, sub := range e.ServedDeps() {
			if _, ok := env.LibraryThms[sub.Name]; ok {
				continue
			}
			subCert := f.Force(dependencyPromise(env, sub))
			registry.InstallLibraryDep(env, sub, subCert)
		}
		// Arm the DEP's own identity around its Build (entry Builds
		// read env.Scope via NewScriptForEntry); restore the caller's
		// scope after.
		prev, prevForcer := env.Scope, env.Forcer
		env.Scope = proof.NewProofScope(core.PropKey(e.Key))
		env.Forcer = &f
		defer func() { env.Scope, env.Forcer = prev, prevForcer }()
		thm, _ := e.Build.Fn(env)
		return f.Force(core.AsThm(thm))
	})
}

// newEntryEnv builds the env an entry's Build runs in: it binds no
// library theorem, and the corpus entries the build reads are served
// on call (the returned library, the env's LibraryResolver) — a cite,
// an induction or recursion principle, a served row alike, each a read
// of the entry that serves the name and noted as one. It is the ONE
// construction the replay harness and the CNF recorder share, and it
// must stay one: a recording is read back in the replay's env, and
// every key it writes is computed over goals that env builds. The
// `induction` tactic names a case's constructor arguments after the
// principle's own binders, so a principle served in one spelling at
// record time and another at replay makes a leaf carrying such an
// argument two sequents. The CNF certificate key is canonical over
// free-variable names and hides the split; the conditioning plan's key
// (the bare leaf's goal AlphaKey) is not — every plan recorded on such
// a leaf misses at replay, the leaf reaches the refuter un-conditioned,
// and the certificate misses too.
//
// deps says which entries the build is served: the whole corpus for a
// recording, which observes what the proof reads, or exactly a list
// for a replay, which serves the record (_EntryDeps).
//
// Deps are resolved in a THROWAWAY env: building a dep may install its
// CNF cache and flip that env strict, which would refuse the entry's
// own live refutes. The forced ThmCert is env-independent (it carries
// its own proof / trust-mint), so only the certs move into the
// entry's env. depTrust is the caller's frontier — an over-approximation
// with no self exclusion is fine here, because the library never serves
// the member itself. What a caller adds on top — the family's strict
// store, or a warm non-strict one with a capture — is its mode.
func newEntryEnv(t *testing.T, ctx context.Context, e *registry.ProofEntry,
	depTrust func(core.Prop) bool, deps _EntryDeps) (*proof.ProverEnv, *_EntryLibrary) {
	lib := &_EntryLibrary{
		ctx:     ctx,
		member:  e,
		deps:    deps,
		depEnv:  testenv.MakeT(t),
		trust:   depTrust,
		certs:   map[*registry.ProofEntry]proof.ThmCert{},
		read:    map[*registry.ProofEntry]bool{},
		refused: map[*registry.ProofEntry]bool{},
	}
	if !deps.everyEntry {
		lib.allowed = make(map[*registry.ProofEntry]bool, len(deps.only))
		for _, d := range deps.only {
			lib.allowed[d] = true
		}
	}

	env := testenv.MakeT(t)
	env.LibraryResolver = lib.resolve
	return env, lib
}

// _EntryDeps says which corpus entries a member's build is served:
// every entry but the member itself (a recording, which observes what
// the proof reads), or exactly a list (a replay, which serves the
// record).
type _EntryDeps struct {
	everyEntry bool
	only       []*registry.ProofEntry
}

// recordingDeps serves a recording: the whole corpus, the member
// excepted — what a session's corpus env binds, by Name and by
// ServesAs (library/serve).
var recordingDeps = _EntryDeps{everyEntry: true}

// servedDeps serves a replay of e: exactly its dependencies.
func servedDeps(e *registry.ProofEntry) _EntryDeps { return _EntryDeps{only: e.ServedDeps()} }

// buildDeps is what a recording serves e: the whole corpus when e's
// dependencies are recorded, and its declared Deps when they are not (a
// definition door's entries, whose Deps are their inputs).
func buildDeps(e *registry.ProofEntry) _EntryDeps {
	if e.DepsRecorded() {
		return recordingDeps
	}
	return servedDeps(e)
}

// _EntryLibrary is a member env's LibraryResolver. A read of a corpus
// entry — by its registered name (a cite) or by the library name it
// ServesAs (a principle, a served row) — resolves the entry's
// certificate in the throwaway env (resolveDep, bounded at the trust
// frontier), serves it, and notes the entry: what the build read is
// the member's dependency record. An entry outside the served list is
// a miss, noted as refused; the member itself is never served.
type _EntryLibrary struct {
	ctx     context.Context
	member  *registry.ProofEntry
	deps    _EntryDeps
	allowed map[*registry.ProofEntry]bool
	depEnv  *proof.ProverEnv
	trust   func(core.Prop) bool

	mu      sync.Mutex
	certs   map[*registry.ProofEntry]proof.ThmCert
	read    map[*registry.ProofEntry]bool
	refused map[*registry.ProofEntry]bool
}

func (l *_EntryLibrary) resolve(name string) (proof.Thm, bool) {
	d, ok := registry.ByName(name)
	if !ok {
		d, ok = registry.ByServesAs(name)
	}
	if !ok || d == l.member {
		return nil, false
	}
	l.mu.Lock()
	defer l.mu.Unlock()
	if !l.deps.everyEntry && !l.allowed[d] {
		l.refused[d] = true
		return nil, false
	}
	l.read[d] = true
	if cert, ok := l.certs[d]; ok {
		return cert, true
	}
	cert, err := resolveDep(l.ctx, l.depEnv, d, l.trust)
	if err != nil {
		panic(fmt.Sprintf("%s reads %s, which does not resolve: %v", l.member.Name, d.Name, err))
	}
	l.certs[d] = cert
	return cert, true
}

// Read is the entries the build read, by registered name, sorted.
func (l *_EntryLibrary) Read() []string { return l.names(l.read) }

// Refused is the corpus entries the build read and was not served —
// reads off a replay's list — by registered name, sorted.
func (l *_EntryLibrary) Refused() []string { return l.names(l.refused) }

func (l *_EntryLibrary) names(set map[*registry.ProofEntry]bool) []string {
	l.mu.Lock()
	defer l.mu.Unlock()
	out := make([]string, 0, len(set))
	for d := range set {
		out = append(out, d.Name)
	}
	sort.Strings(out)
	return out
}

// refusedReads names, ahead of err, the entries a replayed build read
// off its served list — the cause a "no library theorem is bound"
// panic leaves out. err itself when there are none.
func refusedReads(e *registry.ProofEntry, lib *_EntryLibrary, err error) error {
	if lib == nil {
		return err
	}
	refused := lib.Refused()
	if len(refused) == 0 {
		return err
	}
	if e.DepsRecorded() {
		return fmt.Errorf("%s reads %v, which its recorded deps do not list — re-record the member "+
			"(%s=%s): %w", e.Name, refused, envRecordFamilyCNF, e.Name, err)
	}
	return fmt.Errorf("%s reads %v, which its Deps do not declare: %w", e.Name, refused, err)
}

// checkRecordedDeps is the dependency drift gate: the entries a proved
// member's build read must be exactly its record (recorded reports the
// record exists). The record IS the member's dependency edges — the
// DAG, the manifest, the index and the session seam read them — so a
// read off it is an edge nothing else sees, and an entry on it the
// build no longer reads is an edge that is not there.
func checkRecordedDeps(e *registry.ProofEntry, lib *_EntryLibrary, record []string, recorded bool) error {
	if err := refusedReads(e, lib, nil); err != nil {
		return err
	}
	if !e.DepsRecorded() {
		return nil
	}
	read := lib.Read()
	if !recorded {
		if len(read) == 0 {
			return nil
		}
		return fmt.Errorf("%s reads %v but the family blob records no deps for it — record the member (%s=%s)",
			e.Name, read, envRecordFamilyCNF, e.Name)
	}
	if strings.Join(record, " ") != strings.Join(read, " ") {
		return fmt.Errorf("%s's dependencies drifted: recorded %v, this build read %v — re-record the member (%s=%s)",
			e.Name, record, read, envRecordFamilyCNF, e.Name)
	}
	return nil
}

// replayOne builds a fresh env serving entry e exactly its
// dependencies (DepEntries), runs e.Build, forces every section + the
// top, bounded at the corpus-wide trust frontier (forceMember), and
// holds the build to the member's record: its capabilities, its
// dependencies, and what its certificates assume.
func replayOne(t *testing.T, e *registry.ProofEntry, frontier func(core.Prop) bool) (err error) {
	var lib *_EntryLibrary
	defer func() {
		if r := recover(); r != nil {
			// Keep the stack. A `utils.Assert` failure names its own
			// site; the frames above it say which Action reached it,
			// which is otherwise a multi-step bisect over a ~12 s build
			// per round.
			err = refusedReads(e, lib, fmt.Errorf("panic: %v\n%s", r, debug.Stack()))
		}
	}()
	ctx := context.Background()

	var env *proof.ProverEnv
	env, lib = newEntryEnv(t, ctx, e, frontier, servedDeps(e))

	// Family members replay from the FAMILY's shared recorded CNF blob,
	// installed env-side here (family proof files never call
	// InstallCNFCache — the pb is a package-level artifact, not a
	// per-proof one). Legacy flat-corpus proofs keep self-installing in
	// their own Build. An empty blob means "nothing recorded yet":
	// skip the install so refutes run live rather than strict-missing —
	// but say so, loudly: in that window a green replay certifies
	// NOTHING about refute determinism (live CnfRefute is a parallel
	// search), and before the recorded_members marker existed the
	// silence here let measured-zero families sit in the window forever.
	if family := e.Family(); family.CNFStore() != nil {
		env.InstallCNFStore(family.CNFStore())
	} else {
		t.Logf("family %s pb is empty_set — %s replayed NON-STRICT: refutes (if any) ran live and this green says nothing about them. Measure the family (writes the recorded_members marker even at zero keys):\n  XUGO_FAMILY_CNF_GC=%s go test -count=1 -v -run TestRecordFamilyCNF ./library/integrity/gates/",
			family.Name, e.Name, family.Name)
	}

	if err := checkKeyMinted(e); err != nil {
		return err
	}

	// Arm proof identity from the registry entry: entry Builds read it
	// via NewScriptForEntry — the proof file never spells its own key.
	env.Scope = proof.NewProofScope(core.PropKey(e.Key))

	top, built := e.Build.Fn(env)
	dumpProofTree(t, built)
	certs, err := forceMember(ctx, e, top, built, frontier)
	if err != nil {
		return err
	}
	capabilities, measured := e.Family().RecordedCapabilities()[e.Name]
	if err := checkRecordedCapabilities(e, env.Scope.Used(), capabilities, measured); err != nil {
		return err
	}
	record, recorded := e.Family().RecordedDeps()[e.Name]
	if err := checkRecordedDeps(e, lib, record, recorded); err != nil {
		return err
	}
	unfolds, opened := e.Family().RecordedUnfolds()[e.Name]
	if err := checkRecordedUnfolds(e, unfoldedDefiners(e, env.Scope), unfolds, opened); err != nil {
		return err
	}
	// Last: it reads the member's recorded edges, which the three gates
	// above have just held to what this build did.
	return checkAssumptions(e, e.DepEntries(), capabilities, certs)
}

// forceMember holds a built member's top to the entry's statement and
// forces the member — every section, then the top — under the
// corpus-wide trust frontier with the member's own statement left out
// of it. It returns the certificates, the top's last.
//
// top and the sections come out of the member's Build, code the replay
// does not trust: a type there can embed a theorem and answer every
// exported method itself, its statement and its key included. So top is
// read as its kernel value (core.AsThm) before anything is asked of it,
// that value is held to the entry's statement (checkBuiltIdentity), and
// core forces it: the certificate that comes back is the kernel's, of
// the statement just checked, whatever the build handed back and
// however it answers. What the certificates assume is the caller's last
// check (checkAssumptions).
func forceMember(ctx context.Context, e *registry.ProofEntry, top proof.Thm, built *proof.Proof,
	frontier func(core.Prop) bool) ([]core.ThmCert, error) {
	top = core.AsThm(top)
	if err := checkBuiltIdentity(e, top); err != nil {
		return nil, err
	}

	// Trust the corpus-wide frontier EXCEPT self. self must run its own
	// work (it's the entry being verified); every other entry is verified
	// by its own force.
	trust := exceptSelf(frontier, top)

	var certs []core.ThmCert
	for _, s := range built.SectionThms() {
		cert, _ := core.ForceWithBoundary(ctx, s, trust)
		certs = append(certs, cert)
	}
	cert, _ := core.ForceWithBoundary(ctx, top, trust)
	return append(certs, cert), nil
}

// checkAssumptions holds what a replayed member's certificates assume to
// the member's place in the corpus's graph. A certificate lists every
// statement that entered it without a rule deriving it (core's
// ThmCert.Assumes), whichever force settled it and whenever: a
// dependency the frontier trusted, a bundle field's root the warm-up
// settled, a card's axiom. The replay trusts every other entry's
// statement, so that list is the member's real edges, and the corpus's
// soundness is those edges being the ones the graph records: an edge
// the record lacks is one the cycle scan never saw. So each assumption
// must be the statement of an entry in the member's cone — an entry its
// dependencies reach, or one in the foundation of a capability an entry
// of the cone records — and never the member's own, and never a
// TestThm. deps and capabilities are the member's own edges as its
// record has them: the registry's for a replay, the blob's the recorder
// is about to write for a recording.
//
// Which entry an assumption is, whether it is the member's own, and
// whether it was checked already are each answered by comparing
// statements: a key files the statements to compare and settles none of
// the three (core.PropKey).
func checkAssumptions(e *registry.ProofEntry, deps []*registry.ProofEntry, capabilities []string, certs []core.ThmCert) error {
	own := e.Statement().Prop
	var cone *_Cone
	type _AssumptionKey struct {
		statement core.PropKey
		door      core.AssumptionDoor
	}
	checked := map[_AssumptionKey][]core.Prop{}
	var findings []string
	for _, cert := range certs {
		for _, a := range cert.Assumes() {
			assumption := _AssumptionKey{a.Statement.AlphaKey(), a.Door}
			if utils.Any(checked[assumption], a.Statement.AlphaEquals) {
				continue
			}
			checked[assumption] = append(checked[assumption], a.Statement)
			switch stating := registry.EntriesStating(a.Statement); {
			case a.Door == core.TestDoor:
				findings = append(findings, fmt.Sprintf("a TestThm of %s", prop.PrintProp(a.Statement)))
			case a.Statement.AlphaEquals(own):
				findings = append(findings, fmt.Sprintf("its own statement, through %s", a.Door))
			case len(stating) == 0:
				findings = append(findings, fmt.Sprintf("%s, through %s, which no entry states", prop.PrintProp(a.Statement), a.Door))
			default:
				if cone == nil {
					cone = coneOf(deps, capabilities)
				}
				if !utils.Any(stating, cone.holds) {
					findings = append(findings, fmt.Sprintf("%s, through %s, which is outside its dependencies and the foundations of the capabilities they record",
						stating[0].Name, a.Door))
				}
			}
		}
	}
	if len(findings) == 0 {
		return nil
	}
	sort.Strings(findings)
	return fmt.Errorf("%s's certificate assumes what its recorded edges do not account for:\n    %s",
		e.Name, strings.Join(findings, "\n    "))
}

// _Cone is what an entry may stand on: the entries its dependencies
// reach, and the foundations of the capabilities it and they record.
type _Cone struct {
	entries     map[*registry.ProofEntry]bool
	foundations []map[core.PropKey]bool
}

// coneOf is the cone of a member whose own edges are deps and
// capabilities.
func coneOf(deps []*registry.ProofEntry, capabilities []string) *_Cone {
	cone := &_Cone{entries: map[*registry.ProofEntry]bool{}}
	specs := proof.DependencyCapabilitySnapshot()
	recorded := map[string]bool{}
	record := func(names []string) {
		for _, name := range names {
			if !recorded[name] {
				recorded[name] = true
				cone.foundations = append(cone.foundations, specs[name].Foundation)
			}
		}
	}
	var reach func(ds []*registry.ProofEntry)
	reach = func(ds []*registry.ProofEntry) {
		for _, d := range ds {
			if !cone.entries[d] {
				cone.entries[d] = true
				record(d.Family().RecordedCapabilities()[d.Name])
				reach(d.DepEntries())
			}
		}
	}
	record(capabilities)
	reach(deps)
	return cone
}

func (c *_Cone) holds(x *registry.ProofEntry) bool {
	if c.entries[x] {
		return true
	}
	for _, foundation := range c.foundations {
		if foundation[core.PropKey(x.Key)] {
			return true
		}
	}
	return false
}

// checkKeyMinted refuses an entry registered without a Key — it carries
// the unminted sentinel — and hands the author the paste-ready value,
// the statement's normalized key, instead of replaying under a bogus
// identity.
func checkKeyMinted(e *registry.ProofEntry) error {
	if !strings.HasPrefix(e.Key, registry.UnmintedKeyPrefix) {
		return nil
	}
	k := e.Statement().Key()
	field, where := keySpelling(e)
	return fmt.Errorf("entry %s has no Key — its statement's normalized key is %s; paste  %s: %q  into %s",
		e.Name, k, field, string(k), where)
}

// checkBuiltIdentity is the identity cross-check on a built member —
// entry metadata is verified, not trusted. Statement-level, cheap,
// before the heavy force:
// (1) the built theorem IS the declared statement: α-equal to it after
// Normalize, the two normal forms compared and not their keys
// (core.PropKey), and nothing weaker. A Theorem or Sections member
// builds the headline it states, and Derived / Lifted bridge their
// derived top to the headline inside the constructor, so a mismatch
// here is a member stating one theorem and proving another.
// (2) Key is the statement's own normalized key (the minting rule).
func checkBuiltIdentity(e *registry.ProofEntry, top proof.Thm) error {
	st := e.Statement()
	normTop, _ := prop.Normalize(top)
	if !normTop.AlphaEquals(st.Normalized()) {
		return fmt.Errorf("built theorem %s (key %s) is not the entry's declared statement %s (key %s): not α-equal after Normalize",
			prop.PrintProp(normTop), normTop.AlphaKey(), prop.PrintProp(st.Normalized()), st.Key())
	}
	if got := string(st.Key()); got != e.Key {
		field, where := keySpelling(e)
		return fmt.Errorf("entry Key %s is not the statement's own normalized key %s — paste  %s: %q  into %s", e.Key, got, field, got, where)
	}
	return nil
}

// checkRecordedCapabilities is the capability drift gate: what a member's
// build was observed to use must be what the family blob records for it
// (recorded, ok: the blob's row, and whether it has one).
// The record IS the member's capability edges in the dependency manifest,
// so an unrecorded use is an edge the canonical dependency graph never saw,
// and a use the record no longer matches is a witness computed on stale
// edges.
func checkRecordedCapabilities(e *registry.ProofEntry, used, recorded []string, ok bool) error {
	if !ok {
		if len(used) == 0 {
			return nil
		}
		return fmt.Errorf("%s uses %v but the family blob records no capability use for it — "+
			"record the member (XUGO_RECORD_FAMILY_CNF=%s) so the dependency manifest sees the use, "+
			"then regenerate the policy witness (go generate ./library/integrity/manifest)",
			e.Name, used, e.Name)
	}
	if strings.Join(recorded, " ") != strings.Join(used, " ") {
		return fmt.Errorf("%s's capability use drifted: recorded %v, this build used %v — "+
			"re-record the member (XUGO_RECORD_FAMILY_CNF=%s) and regenerate the policy witness",
			e.Name, recorded, used, e.Name)
	}
	return nil
}

// unfoldedDefiners are the entries defining the constants a member's
// build opened by their definitions (ProofScope.Unfolded), by
// registered name, sorted. A constant the logic defines before any
// chapter has no entry, and a member opening the constant its own
// entry defines stands on nothing else by it.
func unfoldedDefiners(e *registry.ProofEntry, scope *proof.ProofScope) []string {
	names := []string{}
	for _, constant := range scope.Unfolded() {
		if d := registry.Definer(constant); d != nil && d != e {
			names = append(names, d.Name)
		}
	}
	slices.Sort(names)
	return slices.Compact(names)
}

// checkRecordedUnfolds is the drift gate of the definitions a proved
// member opens: the entries defining the constants its build unfolded
// must be the ones the family blob records for it (recorded, ok: the
// blob's row, and whether it has one). The record IS those edges of
// the member's dependency graph (ProofEntry.DepEntries), so an
// unrecorded opening is a definition the graph does not show the member
// standing on, and a recorded one the build no longer makes is an edge
// that is not there.
func checkRecordedUnfolds(e *registry.ProofEntry, opened, recorded []string, ok bool) error {
	if !e.DepsRecorded() {
		return nil
	}
	if !ok {
		if len(opened) == 0 {
			return nil
		}
		return fmt.Errorf("%s opens the definitions %v but the family blob records no unfolds for it — record the member (%s=%s)",
			e.Name, opened, envRecordFamilyCNF, e.Name)
	}
	if strings.Join(recorded, " ") != strings.Join(opened, " ") {
		return fmt.Errorf("%s's unfolds drifted: recorded %v, this build opened %v — re-record the member (%s=%s)",
			e.Name, recorded, opened, envRecordFamilyCNF, e.Name)
	}
	return nil
}

// dumpProofTree prints a built member's proof tree — every node's
// ministep and goal, in preorder — when XUGO_DUMP_STEPS is set. Both
// harnesses call it right after Build, so the two trees a member gets
// under record and under replay can be diffed line for line: the
// instrument that separates "a different name" from "a different goal"
// when the two disagree about a leaf.
func dumpProofTree(t *testing.T, built *proof.Proof) {
	if os.Getenv(envDumpSteps) == "" {
		return
	}
	var walk func(n *GoalStackNode, depth int)
	walk = func(n *GoalStackNode, depth int) {
		t.Logf("%s%s  ⊢  %s", strings.Repeat("  ", depth), n.StepDescription(), abbreviateGoalForDump(n.Goal))
		for c := range n.ChildrenIter() {
			walk(c, depth+1)
		}
	}
	for root := range built.SectionIter() {
		walk(root, 0)
	}
}

// abbreviateGoalForDump keeps a dumped goal to one readable line.
func abbreviateGoalForDump(p core.Prop) string {
	str := prop.PrintProp(p)
	if len(str) > 200 {
		return str[:200] + "…"
	}
	return str
}
