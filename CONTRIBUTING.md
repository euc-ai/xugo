# Contributing

XuGo is a kernel, a proof session, and a library of mathematics written
through that session. What a change has to satisfy is written down and
mostly held by tests; this page says where.

## The checks

CI (`.github/workflows/ci.yml`) runs on every change. By hand, its
checks are, in this order:

```sh
gofmt -l .                  # prints nothing
go mod tidy -diff           # prints nothing
go build ./... && go vet ./...
git ls-files -s | awk '$1 != "100644"'   # prints nothing
go test -count=1 -p 1 -timeout 30m -skip '^TestReplayAll$' ./library/integrity/... &&
  go test -count=1 -p 1 -timeout 30m $(go list ./... | grep -v /library/integrity/) &&
  go test -count=1 -timeout 720m -run '^TestReplayAll$' ./library/integrity/gates/
```

The first and the last of the three test commands are the battery the
corpus stands on: the lints, statement identity, the dependency graph
and the gates that hold the generated files current, then every member
replayed through the kernel. The replay is most of the time the checks
take, so it runs last, and each test command runs only when the one
before it passed: a failing gate stops the checks before the replay
starts. One `go test ./library/integrity/...` runs the same battery, but
there a gate's failure is known only after the replay, which shares its
package. Several tests hold a wall-clock budget, so the commands run one
package at a time and the replay runs alone. On a machine with cores to
spare, `go test ./...` is the same tests in one command.

The corpus-wide typed-statement check is `TestServedStatementSurface` in
`library/integrity/gates`: every member's final served text must read back
as the same closed statement under its family's scope. The command's
`TestAddGoal_ReadsServedStatementTyped` checks the query-to-add-goal path
on a fixed set of input forms; it does not enumerate the corpus.

A few tests go further and assert that a live search closes inside its
time ceiling, or that a read returns inside a latency bound. Their
verdict depends on the machine: they pass on the one the ceilings were
measured on and fail on a slower one, with no defect in the code. Such a
test opens with `wallclock.SkipOnSlowMachine(t)` (`utils/wallclock`) and
is skipped where `XUGO_SLOW_MACHINE=1`, which CI sets for the runner of
its tests; `git grep SkipOnSlowMachine` lists them. A test joins them
when it fails on a slow machine and passes there with its ceilings
raised and nothing else changed.

The engine's emitted-code tests queue the scratch members produced by the
selected tests. After their assertions pass, `TestMain` compiles and replays
them in one `go test` invocation, one isolated process per member, run
serially. A compile or replay failure fails the package. Selecting one of
these tests with `-run` still compiles and replays the member it emits.

The fourth line lists every tracked file that is not a plain one: a
built binary, or a script added with its executable bit. Nothing the
tree holds is executable; a script is run as `sh <file>` or
`bash <file>`, and `git update-index --chmod=-x <file>` clears the bit
of one already added.

CI also regenerates the protobuf code and compares (see "Generated
files").

While iterating, replay the member you touched:

```sh
XUGO_REPLAY_ONE=<family>.<Name> go test ./library/integrity/gates/ -run '^TestReplayAll$' -count=1
```

The constitution's §"Verification contract" says which edits need a
wider scope than that.

## A chapter

`library/chapter_constitution.md` is the contract: what a chapter is,
how a statement is stated and a proof written, what a name is, and what
is verified. A chapter is reviewed against it. `library/proofs/README.md`
says how the chapters read.

A proof is found in a session and written down afterwards.
`engine/xugo-engine.md` has the session's commands, the playbook, and
the Go a chapter is written in. The pipeline that does both, a dialogue
that scopes a chapter and an agent that proves one statement, is
`.claude/skills/prove/SKILL.md` with `.claude/agents/xugo-prover.md`.

What a first contribution meets:

- **Cards.** A member may be stated before it is proved. It is then a
  card, served as an axiom, and `xugo query cards` (the index's cards
  page) lists the cards, frontier leaves first. Proving one is the smallest whole
  contribution: the proof lands under the card's name and key, and
  nothing that cites it changes.
- **Recorded refutations and dependencies.** A proof step that calls
  the refuter is recorded into its family's `.cnf.pb`, and so are the
  entries the member's proof reads, which are its dependencies: a
  proved member spells no `Deps`, and a definition's edges are read off
  its equation, its `Deps` naming only its own family's mints that Go
  must initialize first. Replay reads the record and never
  searches. A member is recorded when it lands and again when its
  proof changes what it cites, and the run ends by replaying the member
  against the record it leaves, so a passing run is also its replay:

  ```sh
  XUGO_RECORD_FAMILY_CNF=<family>.<Name> go test -count=1 -v -run TestRecordFamilyCNF ./library/integrity/gates/
  ```

  What the proof's text names is among what the record holds: the lint
  battery's `TestLintProofNamesRecordedDeps` refuses a member a step
  names, directly or through a local bound to a citation, that the
  replay recorded no read of.

  The header of `library/integrity/gates/record_cnf_test.go` and the
  manual's §"The recorder's two gates" say what the run writes and what
  it refuses to. The record names entries by their registered names, so
  an entry renamed in the source is carried into every blob with
  `go run ./library/cmd/rekey_cnf_blob -rename-entries <old>=<new>`,
  an entry deleted from the source is taken out of every blob with
  `go run ./library/cmd/rekey_cnf_blob -drop-entries <old>` (until it
  is, every reader of the dependency graph panics on the stale name,
  the recorder of any family among them), and a landing made in another
  tree is brought into this one with
  `go run ./library/cmd/merge_cnf_blob -base <commit> -theirs <root>`,
  a set merge of the blobs that runs no proof. A blob also names each
  certificate by the key of its refute prop as the CNF conversion builds
  it, the row a replay finds the certificate by before it normalizes
  anything. A change to the CNF conversion or to its naming moves those
  keys, and the replay then finds every certificate by its normal form,
  as slowly as before the table: `go run ./library/cmd/rekey_cnf_blob`,
  over every blob, writes the rows again and runs no proof.
- **Defects below the chapter.** A defect in the engine, or in the Go
  that `emit-section` renders, is a change of its own. It is fixed at
  its source and never patched around in a proof file.

## Generated files

Run `go generate ./library/...` once after the change that moves one,
before the gates. Every generator is idempotent — one with nothing to
write writes nothing — so there is nothing to decide about which to
run; apart from the protobuf code, each has a gate in the battery that
fails on a stale file and names the command.

| Generated | By |
|---|---|
| every family's `zz_*_gen.go`: the typed wrappers, the vocabulary, and the package's doc comment (the title line of the chapter's `README.md`) | `go generate ./library/proofs`, one run over every family |
| `library/authoring/zz_constructors_gen.go`, the scanned half of the bare names a proof file dot-imports, and their roster, `library/registry/aliasgen/zz_surface_gen.go` | `go generate ./library/authoring/` |
| `library/integrity/policy/policy_gen.go` | `go generate ./library/integrity/manifest` |
| `library/carddata/cards_gen.go`, the cards' display and typed statements | `go generate ./library/carddata` |
| the landmarks list in `site/landmarks.html` and `site/zh/landmarks.html`, between their `<!-- landmarks … -->` marks, from `site/landmarks.json` | `go generate ./library/landmarks` |
| a `*.pb.go` | `protoc`, by the command in its `.proto`'s header |
| `.agents/skills/prove/SKILL.md`, `.gemini/skills/prove/SKILL.md`: the /prove skill, for harnesses that look for a skill there | `mkdir -p .agents/skills/prove .gemini/skills/prove && cp .claude/skills/prove/SKILL.md .agents/skills/prove/SKILL.md && cp .claude/skills/prove/SKILL.md .gemini/skills/prove/SKILL.md`; the skill is edited under `.claude/` |

`go generate ./library/...` runs the first five; `TestLintSiteLandmarksCurrent` holds the landmarks pages to their list. `TestCardDataCurrent`
holds the card spellings to the current registry: membership, notation
and typed-print changes require regeneration even when names and keys
stay the same. The CLI and server read these texts without parsing or
normalizing the corpus's cards; new cards without a matching generated
row are read on demand until regeneration.

The corpus index renders no file. `xugo query` answers its views from
the registry, and `xugo browse` serves the same corpus to read in a
browser — the family graph, each theorem's page, a search — drawing a
page when it is asked for and writing nothing to disk. What a chapter can
break there is gated in the battery a family's checkpoint runs:
`TestFamilyGraphAcyclic` holds what the index refuses, a cycle in the
family graph.

The protobuf code is the one generated surface that needs a tool
besides Go. The header of a `*.pb.go` names the `protoc` and
`protoc-gen-go` versions that wrote it; CI installs those two,
regenerates, and fails on a difference. Install the plugin with
`go install google.golang.org/protobuf/cmd/protoc-gen-go@<version>`.

Write a comment in a `.proto` the way gofmt writes a doc comment: a
list item under `  - `, its continuation lines under four spaces, a
blank line between a list and the paragraph after it. A plugin built by
Go 1.26 rewrites any other form into that one and a plugin built by
Go 1.27 does not, so only the gofmt form generates the same bytes
whichever built the plugin.

## The kernel, the prover, the engine

Two rules hold in every package: a logical inconsistency
panics ("Soundness by panic"), and a comment says what the code beside
it does now ("Comments state the contract"). `core/` is the trusted
base; `core/README.md` describes it and how what it trusts is audited.

An unexported type is spelled `_Name`, and a value handed to reflection
is typed by a narrow named interface rather than `any`. Code written
before the rule does not all follow it yet; new and touched code does.

### Soundness by panic

The project deviates from Go's error-handling idiom on purpose: a
logical inconsistency panics. A theorem object exists only because the
kernel built it, and any violation of a kernel or framework invariant
stops the program rather than propagating. Errors are returned only at
the edges, where input from outside is read.

### Comments state the contract 

A comment says what the code beside it does now. It carries no date,
no "landed" or "renamed from", no account of how an earlier version
was built, and no pointer into a working log or a plan: git holds the
history, and a comment that repeats it goes stale beside code that is
checked. The constitution says this of a chapter's proof files; the
kernel, the prover and the engine hold to the same rule.

A package has one doc comment, and its first sentence says what the
package is: "Package registry is the framework a chapter is written
in". That sentence is the line `go doc` opens on and the line
pkg.go.dev prints beside the package. Go joins every comment that
touches a `package` clause into the package's documentation, so
exactly one file carries it, and every other file's header stands a
blank line clear of its clause. A chapter's doc comment is not
written by hand: it is the title line of the chapter's `README.md`,
`# <name> — <gloss>`, which the family generator writes onto the
package. The gates check the count and the opening in every package
of the module; that the sentence is true of the package is held by
reading.

A shorthand label in a comment, a rule or stage number such as `S4`,
says whose label it is ("the manual's S4"). Its owner is a document
that lives long and changes slowly, and the label is kept only where
it recurs across many files. A label met a handful of times is
written out where it stands, as a proposition used once is expanded in
the proof and not named a lemma. A label a file's own header defines
already says whose it is.

## Environment variables

Every variable the code reads is named `XUGO_…` and is listed here;
`TestLintEnvVarTable` in the battery fails on one the code reads and
this table lacks, on a row no code reads, and on a document that names
one outside the table. None is needed to build, to run the session, or
to pass the checks: unset, each leaves the default behaviour. The one
exception is `XUGO_SLOW_MACHINE`, which a slow machine sets to pass the
tests.

Verifying and recording (all read by tests under
`library/integrity/gates/` unless a place is named):

| Variable | Effect |
|---|---|
| `XUGO_REPLAY_ONE` | `TestReplayAll` replays the one named member, `<family>.<Name>`, in a process of its own |
| `XUGO_REPLAY_SCOPE` | `TestReplayAll` replays a subset: a comma-separated list of family names and member names, each with its direct consumers |
| `XUGO_RECORD_FAMILY_CNF` | `TestRecordFamilyCNF` records the named member's refutations live and merges them into its family's `.cnf.pb` |
| `XUGO_FAMILY_CNF_GC` | `TestRecordFamilyCNF` collects the named family's `.cnf.pb` to the rows its members' row records name, running no proof; a member the blob holds no record for is measured |
| `XUGO_RECORD_CNF_DRY_RUN` | `=1`, beside either of the two above: the run lists the rows it would touch and writes nothing. Unset or `=0` the run writes; a value that is no boolean stops it |
| `XUGO_GATE_BASE` | the git ref the gates that compare the tree against a commit read: the re-pointed-name report (`TestLintRepointedNames`) and the claim-text gate (`TestLintClaimTextIsData`, which refuses a claim text assembled from Go strings — a const, a local string, a helper or a builder spliced in — that the base does not have, and counts the ones it has); `HEAD` unset, and CI sets it to the base of the change |
| `XUGO_PASTE_KEYS` | `TestEntryKeyIsOwnKey` writes each missing or moved `Key` of the entries named — a family as `<domain>/<family>`, a member as `<family>.<Name>`, as `XUGO_REPLAY_SCOPE` reads them — into its entry's source and reports what it wrote; the run passes once every named key is written, and only reports (never writes) another entry's missing or moved key, which the gate's run without the variable fails on |
| `XUGO_RECORD_EMIT_CNF` | `=1`: the tests of `library/emit` re-record their own refutation fixture, `testdata/cnf_replay.gob` |
| `XUGO_EMIT_REPLAY` | `=1`: the emit-section tests of `engine` that call `replayEmittedInFamily` land the member they emit in its family through a build overlay — the member file and the family's blob with the member recorded, the tree untouched — and replay it with `TestReplayAll`; unset, those tests check the rendering alone. Scratch-member replays queued by `replayEmitted` always run |
| `XUGO_SLOW_MACHINE` | `=1`: the tests that open with `wallclock.SkipOnSlowMachine` are skipped (`utils/wallclock`): their verdict depends on the machine's speed. CI sets it for the runner of its tests |

Diagnostics. Each prints or writes something and changes no verdict,
except the sweep, which edits proof files:

| Variable | Effect |
|---|---|
| `XUGO_DUMP_STEPS` | beside `XUGO_REPLAY_ONE`: prints the replayed member's proof tree, every node's step and goal |
| `XUGO_RECURATE_PROBE` | `TestZZRecurateProbe` replays the one named member without recovering a panic, so a failing edit shows its full stack |
| `XUGO_REPLAY_TRACE` | beside `XUGO_RECURATE_PROBE`: every step the replay runs is logged with its goal |
| `XUGO_WITNESS_PROBE_DEP` | `TestZZWitnessOrderProbe` prints the named member's statement, its installed form and a ground cite at distinguishable numerals: which stated slot fills which binder |
| `XUGO_CENSUS_OUT` | `TestStrictResolutionCensus` writes its full findings, as TSV, to the named path |
| `XUGO_ROUNDTRIP_OUT` | `TestStatementPrintRoundTrip` writes the statements that failed the round trip to the named path |
| `XUGO_SURFACE_SWEEP` | `TestSurfaceSweep` rewrites claim literals from minted variable spellings to surface ones, in the named family or `ALL` |
| `XUGO_EMIT_PROBE_OUT`, `XUGO_EMIT_PROBE_LEANRW_OUT`, `XUGO_EMIT_PROBE_AC_OUT` | three tests of `engine` write the family member they emit to the named file, for a replay of it through the harness |
| `XUGO_EMIT_PROBE_HYPVERBS` | `1`: the `engine` tests of the session moves twinning `Cite(Law.Read(h))`, `a.Conjuncts` and `a.Unfolded` write each member they emit into its family's package as `zz_probe_<name>.go`, for a replay of it through the harness; the files are the caller's to delete |
| `XUGO_SIGHTING_SESSION_STORE`, `XUGO_SIGHTING_CNF_STORE`, `XUGO_SIGHTING_SESSION`, `XUGO_SIGHTING_FAMILY` | `TestEmitSection_StoredSighting` resumes the named session from the named session store and CNF store and logs the member `emit-section` renders of its section 0 into the named family; the resume writes the lineage back, so name copies of a serve's stores |
| `XUGO_DEEPREWRITE_TRACE` | `count` or `trace`: `ext/prop` reports to stderr how often a deep rewrite fires |

The engine itself:

| Variable | Effect |
|---|---|
| `XUGO_TRACE_LOG` | the `xugo` command appends its operation traces to the named file; the `--trace-log` flag takes precedence |
| `XUGO_UNIFY_BUDGET` | the unifier's work budget, in poll units, where the caller sets no deadline (`ext/unify`; `DefaultUnifyBudget` unset). It decides which unifications succeed, so a recorded proof is replayed under the budget it was recorded under |
| `XUGO_UNIFY_WALLCLOCK` | `=1`: the unifier takes a wall-clock cap in place of that budget. Its result then depends on the machine's load; an experiment's switch, never a setting to record or replay under |

Set by the tests for the processes they start, and never by hand:

| Variable | Effect |
|---|---|
| `XUGO_REPLAY_FAMILY`, `XUGO_REPLAY_ENTRIES`, `XUGO_REPLAY_RESULTS` | `TestReplayAll` hands each family's child process its family, the entries to replay and the file to report into |
| `XUGO_TEST_READ_LATENCY_CHILD` | marks the fresh child process of the engine's first-request latency test |
| `XUGO_TEST_ENGINE_INIT_CHILD` | marks the fresh child process of the command's production-startup test |
| `XUGO_TEST_ENGINE_FREE_LINE` | the command line the child process of the `xugo` command's engine-free test runs `main` on |
| `XUGO_TEST_READ_INPUT_CHILD` | marks the child process of the `xugo` command's input-reading test |
| `XUGO_TEST_READINGS_CHILD` | marks the child process of `library/serve`'s test that the readings view builds no proof |
| `XUGO_TEST_FALLBACK_CHILD` | marks the child process of `library/serve`'s test that reading a record equation through the fallback builds no proof |
| `XUGO_TEST_SIMP_RESIDUAL_CHILD` | marks the child process of `library/serve`'s test that Simp's residual reads the record equations as statements |

## Versions

XuGo is at v0. A release is a tag `v0.MINOR.PATCH` on the default
branch, at a commit the checks pass. Between tags nothing is promised to
stay the same, the names of members and the shapes of the session's
RPCs included.
