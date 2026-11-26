# XuGo: instructions for agents

XuGo is a higher-order-logic theorem prover in Go with an LCF kernel, a
corpus of mathematics proved in it, and the proof session the corpus
is written through. `README.md` is the front page and the reading
map; this file is what an agent needs before it touches the tree.

## Build and check

Go at the version `go.mod` names; there is nothing else to install.

```sh
go build ./... && go vet ./...
go build -o xugo ./engine/cmd/xugo/
XUGO_REPLAY_ONE=<family>.<Name> go test ./library/integrity/gates/ -run '^TestReplayAll$' -count=1
go test -count=1 -run TestLint ./library/integrity/gates/
```

The second line builds the CLI and the session server (git ignores the
binary). The third replays one member through the kernel and the
fourth is the lint battery: the two are the check for a change to one
proof. `CONTRIBUTING.md` has every check a change passes before it
merges, the whole-corpus battery among them, and the constitution's
§"Verification contract" says which edits need more than one member's
replay. Several tests hold a wall-clock budget, so run one heavy suite
at a time.

Go shares its build cache between checkouts and worktrees only under
`-trimpath`, set once per machine in `GOFLAGS`: without it a new tree
compiles the whole corpus again, tens of seconds and a few gigabytes.
`engine/xugo-engine.md`, "Session commands", has the command and the
reason. The setting is the machine owner's: where `go env GOFLAGS`
does not show it, tell the user once and go on, and never pass
`-trimpath` to a single command, which compiles a second copy of every
package.

## Reading the corpus

Ask the corpus before grepping it. `./xugo query <overview |
family | member | dossier | deps | dependents | between | definition |
definitions | cards | axioms>` answers from the registry, and
`./xugo browse` serves the same corpus to read in a browser: the family
graph, each theorem's page, a search. A member is found by
its statement, not by a name from another library. `family`,
`member`, `dossier`, `deps`, `dependents` and `definition` take several
names in one call, and a call registers the corpus before it answers:
ask for them together, never in a loop. The open work is
the cards: members stated without a proof, served as axioms until one
lands.

## Rules that hold in every package

- A logical inconsistency panics. Errors are returned only where
  input from outside is read (CONTRIBUTING, "Soundness by panic").
- A comment says what the code beside it does now: no date, no
  account of an earlier version, no pointer into a log or a plan
  (CONTRIBUTING, "Comments state the contract").
- A generated file is never edited by hand: `*_gen.go`, `*.pb.go`,
  the skill's copies under `.agents/skills/` and `.gemini/skills/`, and
  the landmarks list between the marks of the two landmarks pages (its
  source is `site/landmarks.json`) come from the commands in
  `CONTRIBUTING.md`, "Generated files".
- A defect in the engine, or in the Go that `emit-section` renders, is
  fixed at its source and never patched around in a proof file.
- `core/` is the trusted base. A theorem exists only because the
  kernel built it: `TestThm` is refused in proof files, and a constant
  is minted only through a definition door.
- Work-in-progress commits in an agent's own worktree are its call:
  a base for isolated workers, a checkpoint, a merge's starting state.
  What lands on master, and in how many commits, is settled with the
  user first. No automatic rebase or cherry-pick to another branch.
  Never push unasked.

## Writing mathematics

A chapter is written through `/prove`. `.claude/skills/prove/SKILL.md`
is the working session: what a chapter holds is settled with the user,
and each statement is then proved and written down by a sub-agent
whose instructions are `.claude/agents/xugo-prover.md`. What they
produce is held to `library/chapter_constitution.md`; the session's
commands and the Go a chapter is written in are
`engine/xugo-engine.md`.

The skill's section "The harness" maps the same pipeline to Claude
Code, Codex and Gemini (Antigravity and Gemini CLI): cold sub-agents,
completion, worktree assignment, shell lifetime and permissions. The
prover file's body is shared; its frontmatter configures the native
agent only where recognized. On another harness, adapt that section to
the tools actually exposed.

`.agents/skills/prove/SKILL.md` and `.gemini/skills/prove/SKILL.md` are
the skill copied byte for byte, for harnesses that look for a skill in
those directories. They are read the same way, and an edit goes to the
file under `.claude/`.

A sub-agent dispatched with a brief follows its brief and its own
instruction file; where those are narrower than this file, they
govern.
