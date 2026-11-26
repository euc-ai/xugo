---
name: prove
metadata:
  version: "1.0.0"
description: |
  The working session for a chapter of mathematics in XuGo. One
  skill, two layers: you and the user decide what a chapter contains
  and how it is organized (dialogue); `xugo-prover` sub-agents prove
  each statement in a session lineage and curate it into the chapter's
  family package (pipeline). A statement is the author's: a
  definition made in session, a theorem the user states, or a card a
  chapter stated ahead of its proof. A reference the user supplies —
  a textbook proof, a script from another prover — is read for its
  structure and is never required. The product is the family package
  under `library/proofs/`; the oracle is the kernel plus replay;
  the quality loop is fresh-eye
  review. There is no acceptance step and no construction ledger.
  Use for "prove", "curate", "write the chapter on …", "/prove".
  `/prove` with a qualified card name fills that card (Step 5,
  "Filling cards"); with free text it opens a chapter session or
  proves the one statement the text gives.
allowed-tools: Bash Read Write Edit Grep Glob TaskCreate TaskUpdate Agent ScheduleWakeup
---

# `/prove` — the chapter working session

Proving and curating are one activity in two phases: a proof is found
in a session, then written into the chapter as mathematics. This
skill runs both, with the same sub-agent and the same exit — a registered family entry that
replays.

**Two layers.**

- **Dialogue (you ↔ the user).** Chapter boundary and member set, the
  order of construction, the chapter's conventions (which structure
  shape, which names, which file groups), framework changes, packet
  scope, when to stop and look. Prepare evidence → propose → the user
  decides. Never resolve these alone.
- **Pipeline (you → `xugo-prover`).** Per statement: brief →
  dispatch → verify → review → route feedback. Scripted.

The placement test: if two chapters would answer a question
differently, it is dialogue; if every chapter answers it the same
way, it is mechanics and lives in this file, the manual, or the constitution.

**What records what.** The chapter's family package is the record:
a registered entry is a theorem, the entries its proof reads and the
definitions it opens — recorded in the family blob, a card's narrative
`Deps` — are the
dependency graph, the `README.md` is the chapter's mathematical
narrative. A
theorem stated before it is proved is a CARD: a member whose Build
is `family.Card(<statement>, <note>)`, served as the axiom
`⊢ <statement>` until a proof lands in place of the Card — landed,
replayed (nothing to replay), cited and retrieved like any member.
`defer` in the manual's session table makes one from an open leaf
and closes the leaf by it; `emit-section` renders the card entry
beside the member. What a card buys is divide and conquer: work laid
as statements that do not depend on each other's proofs, filled in
parallel, by anyone, in any order. What it costs is a pipeline — lay
it (statement, key, wrappers, README row, referee), fill it (a
dispatch with its gates, the record, the replay, the merge, the log),
then apply it at the sites that cite it. So a macro framework is laid
as cards, while a step inside one proof — split off a fill, or turned
up by a review — buys none of that parallelism and is a lemma
promotion: the agent that owns the proof mints the member beside it,
proves it and cites it, in the same dispatch. The corpus is sound relative to its cards at every
moment, so a tree holding cards is its normal state, not a transition
to be finished. Open
work is the cards: `xugo query cards` reads them off the registry —
which members stand on each — and lists them leaves first, the
cheapest order to fill them in and not a schedule; `xugo cards` adds
what the session store knows, the cards a lineage minted and which
lineage is proving each. Any card, by anyone, at any
time (Step 5, "Filling cards"). A chapter can be planned top-down by writing cards by
hand; a chapter can be laid out from a source read as a textbook — a
book, a paper, another prover's library — by restating its theorems
as cards. A lineage still being worked resumes where it stopped. There is
no `PLAN.md`, no tier number, no "landed"/"closed" state, no sign-off:
proofs are improved whenever someone reads them and sees better, and
a change is verified by replay, the same as the first landing.

# Mandatory rules

1. **Authoring goes to sub-agents.** Dispatch `xugo-prover` for
   proofs; your context holds scoping, briefs, verdicts, test output
   and the log — not proof bodies (read one to diagnose a `FAILED`).
   Working a member yourself is a deliberate, user-visible choice —
   usual for a chapter's first member, where the conventions get
   set, and for a direct task (Step 4, "Session or direct") shorter
   to write than to brief — never a silent default.
2. **The only session RPCs you run yourself are read-only** —
   `query`, `inspect`, `session-lineage`, `list-checkpoints` — and the
   statement pre-parse of Step 4, an `add-goal` on a scratch session,
   which proves nothing.
   Everything else is the sub-agent's. A bridge lemma the dialogue
   plans is a MEMBER, landed first and cited by name.
3. **Never change engine behavior silently, and never take an
   engine claim on an agent's word.** A `FAILED` is one navigation
   path, not a capability fact: before it reaches the user or a
   knowledge file, probe the claim yourself (a fresh session, a
   different navigation, ≤5 minutes). A wall without a runnable
   repro is a rumor. New engine primitives land in
   `engine/xugo-engine.md` in the same commit as their
   implementation — an undocumented primitive is invisible.
4. **You are a mathematician first.** Composite triage — how a
   theorem decomposes, which lemmas have independent value, what
   structure a chapter should carry — is your work BEFORE the first
   dispatch, from the mathematics and from the reference where the
   user supplied one, not something to discover after two failures.
5. **Think the task through from the agent's seat.** A sub-agent
   sees its brief and the files it opens; you see the corpus, the
   wave, the other agents and what the session has already learned.
   A dispatch hands over the work, not the thinking: before it, work
   out how the agent would do the task most efficiently if it saw
   what you see, and put that in the brief — where the proof it needs
   already stands (to move, not to re-derive, and then whether the
   task is direct: Step 4, "Session or direct"), which files another
   agent is editing now, which steps repeat and can run as one batch,
   and whether the task is the agent's at all. A run that is slow or
   roundabout is first a question about the brief.
6. **Rolling pool ≤ 5, non-blocking, one statement per agent.**
   Dispatch in the background, refill per completion, re-read the
   chapter's state per completion, never barrier. Within one family,
   dispatch sequentially unless the agents are worktree-isolated:
   the family CNF blob is read-modify-write and proof files are
   shared.
7. **Briefs carry structure, never numbers.** No budgets, no round
   counts, no prior-failure tallies (failure priming). A shape target
   is a technique.
8. **Replay by scope, never by reflex — and by the WHOLE corpus for
   the elaborator.** A proof body reaches no other entry; a statement
   change reaches its citers, one hop (`XUGO_REPLAY_SCOPE`). The
   whole corpus (~38 CPU-min) runs for a framework edit, the
   induction principle's statement, the statement of a member a serve
   bundle binds (its consumers reach it through a capability, read no
   entry for it, and the scope does not select them — read the bundle
   literals in `library/serve` at scoping), or a policy-witness diff that
   leaves the landing — and ALWAYS for a change to the elaborator,
   the parser, or a registration gate, before it lands: those touch
   chapters the change never mentions, and nothing else sees them.
   Measured once: the pinned-constant gate widened, and the
   elaborator suite, the key gate, the lint battery and every
   targeted member replay stayed green; the full replay alone caught
   `num_segment.HasSizeBelowStrict` and `num_segment.Card` (CNF MISS)
   in a chapter nothing in the wave had opened.
9. **Knowledge accumulates by tag.** Friction routes to the
   knowledge files below; promote on the second occurrence; a wall
   needs a repro. Never tighten the verification contract because a
   proof "feels weak" — a new guard needs a concrete failure it
   would have caught.
10. **Work-in-progress commits are yours; the landing is settled with
    the user. Never push.** In a worktree of your own — the session's
    branch, an isolated lane's tree — commit work in progress whenever
    it serves: the base an isolated lane is cut from, a checkpoint
    before a risky move, the state a merge starts from. Such a commit
    is reversible and asks for no approval. What lands on master or on
    the branch the user works on, and in what shape (one commit or
    several, which subjects, what is squashed), is discussed with the
    user before it is made. Do not rebase or cherry-pick onto another
    branch as a pipeline step. Batch the log into the landing where the
    clone tracks it.
11. **Statements.** Every statement is the author's, in natural
    mathematical form (one taken from a reference is restated, in the
    chapter's vocabulary, from what the reference proves); it is read — by you
    at verify, by the fresh-eye reviewer — and improved like any
    other text. No sign-off ritual.
12. **An engine fault is the engine's record, not an agent's report.**
    The engine writes down every fault it meets, with the request and
    the goal, and the session that met it takes no further move
    (`engine/xugo-engine.md`, "Engine faults"). A command that
    overruns is in the same record or says so itself: a run its budget
    ends answers that it was cut off (`unknown(timeout)`, an `inspect`
    fact marked `unverified`), which is no verdict on the tactic; one
    that ends seconds past its deadline is written down as an overrun;
    and a serve stopped under a command that never answered leaves the
    request, whatever the command. `./xugo
    --data-dir="$DATA_DIR" faults` lists the ones nobody has
    acknowledged and fails while there is one: run it when an agent
    returns and at session end. An open fault is handled before the
    wave goes on past it — reproduced from its record, then fixed at
    its source or put to the user — and acknowledged with what was done
    (`faults ack <id> --note "…"`). A wave with an open fault is not
    done, whatever its verdict lines say, and a proof that went around
    the faulting step does not stand in for the fix.

# The harness

This section maps one pipeline to Claude Code, Codex and Gemini
(Antigravity and Gemini CLI). Everywhere else the file says
"dispatch", "in the background", "isolated" and "generic sub-agent",
and means what the table defines. The prover's standing instructions
are `.claude/agents/xugo-prover.md`; its body and §Connect apply across
all of them. A port adds its execution mapping here, without forking
the proof instructions.

`.agents/skills/prove/SKILL.md` and `.gemini/skills/prove/SKILL.md` are
this file copied byte for byte, for harnesses that look for a skill in
those directories: Codex and Antigravity discover `.agents/skills/`,
and Gemini CLI discovers `.gemini/skills/` (or `.agents/skills/`). They
are copies and not ports; the file under `.claude/` is the one edited,
`CONTRIBUTING.md`, "Generated files", has the command that copies it,
and a gate holds the three equal.

| The pipeline needs | Claude Code | Codex | Gemini (Antigravity / Gemini CLI) |
|---|---|---|---|
| **A cold prover**, its final message the verdict | `Agent` with `subagent_type: xugo-prover` and the brief as prompt | `collaboration.spawn_agent` with `fork_turns: "none"`; the prompt tells it to read `AGENTS.md` and the prover instruction file in its assigned tree, then supplies the entire brief | Antigravity: `define_subagent` once (`Name: "xugo-prover"`, `EnableWriteTools: true`, `SystemPrompt` pointing to `AGENTS.md` and `.claude/agents/xugo-prover.md` in its assigned tree) then `invoke_subagent` (`TypeName: "xugo-prover"`) with the brief as `Prompt`. Gemini CLI: `generalist` sub-agent tool, its prompt telling it to read `AGENTS.md` and `.claude/agents/xugo-prover.md` in its assigned tree, then supplying the entire brief |
| **Background dispatch and per-agent completion** | `run_in_background: true`; completion notifications. `SendMessage` to a finished agent resumes it with its context and, under isolation, its tree: the next brief of a sequence goes there | Spawning returns an agent ID; completion is delivered to the parent. Use `collaboration.wait_agent` when there is no independent work; refill per completion | Antigravity: `invoke_subagent` launches in the background and returns a `conversationId`; completion wakes the parent reactively (never poll). `send_message` resumes an idle prover with its context and workspace. Gemini CLI: parallel `generalist` calls in one turn where supported, else sequential; each call starts cold |
| **Optional worktree isolation**, required for concurrent authors in one family | `isolation: "worktree"`; verify the actual assigned root and base | Create or reuse a separate worktree before spawning, then pass its absolute root in the brief; spawning alone shares the parent's workspace | Antigravity: `invoke_subagent` with `Workspace: "share"` (verify the actual assigned root and base), or create/reuse a separate worktree before spawning (`Workspace: "inherit"`) and pass its absolute root in the brief. Gemini CLI: create or reuse a separate worktree before delegating and pass its absolute root in the brief |
| **A generic reviewer**, read-only by its brief | `subagent_type: general-purpose` | A cold `collaboration.spawn_agent`, told to read the project's instructions and the review brief, with no prover role | Antigravity: `invoke_subagent` with `TypeName: "research"` (read-only sandbox, no network). Gemini CLI: `codebase_investigator` or a cold `generalist` call told by its brief to read only and run no tests or builds |
| **Shell and file access**, including `go`, `curl` and a reachable session server | The native tools named by the frontmatters | The shell/file tools actually exposed by the host; tool names in the frontmatters do not grant access | Antigravity: `run_command`, `read_file`, `write_file`, `edit_file`, `manage_task`. Gemini CLI: `run_shell_command`, `read_file`, `write_file`, `replace`, `grep_search`, `glob`. Tool names in the frontmatters do not grant access |

**Codex dispatch.** The table names the collaboration tools of this
host. On a host exposing equivalent spawn/wait tools, use their actual
schema and cold-context option. If sub-agents are unavailable, report
that limitation; authoring locally is the user-visible choice of
rule 1. Do not create a separate user chat with `create_thread` for a
pipeline worker. The pool is at most five AND at most the host's
available child-agent capacity. Keep the returned IDs with each
member and worktree path. `collaboration.send_message` delivers
feedback to a running agent; `collaboration.followup_task` resumes an
idle one. Use the host's default model unless the user supplied a
supported override; the prover file's Claude Code model/tool fields
are not Codex configuration.

**Gemini dispatch.** In Antigravity, register `xugo-prover` once per
conversation with `define_subagent` (`Name: "xugo-prover"`,
`EnableWriteTools: true`, `EnableSubagentTools: false`, `SystemPrompt`
telling it to read `AGENTS.md` and `.claude/agents/xugo-prover.md` in
its assigned tree before acting — never inline the prover file into
`SystemPrompt`; the registration persists across context compaction and
refuses a duplicate `Name`, so reuse the registered type name rather than
re-defining it), then launch each prover with `invoke_subagent`
(`TypeName: "xugo-prover"`, `Model: "inherit"` unless the user
requested another model, `Prompt`: the brief). Keep each returned
`conversationId` with its member and worktree path. `invoke_subagent`
is asynchronous and wakes the parent reactively when a child returns:
end your turn rather than polling `manage_subagents` or setting timers,
and refill per completion within the five-agent pool. `send_message`
(`Recipient: conversationId`) sends the next brief of a sequence to an
idle prover; leave finished provers idle rather than calling
`manage_subagents` `kill` or `kill_all`, which deletes a `share`
workspace along with the agent. Do not use `swarm` or `run_workflow`
for pipeline dispatches unless the user asks. In Gemini CLI, the skill
loads through `activate_skill` (or `/skills`), and each prover is a
cold `generalist` tool call whose prompt names `AGENTS.md` and
`.claude/agents/xugo-prover.md` in its assigned tree before the brief;
if default `runConfig` (`maxTurns` or `maxTimeMinutes` under
`agents.overrides.generalist`) clips a long run, report `FAILED
stage:harness` rather than guessing edits. Neither host reads the
prover file's Claude Code frontmatter.

**Worktree assignment and base.** In Codex desktop, inspect
`list_artifacts` for a suitable existing worktree first; otherwise
use `create_worktree` with `ref` set to the exact committed base from
Step 5, and wait for completion if creation is pending. These tools
do not switch a child agent's working directory. On a host without
them, a separate `git worktree add --detach` at that same commit
serves the same purpose. Record the returned absolute root; never
infer it from an agent ID or a directory naming convention.

For native isolation — Claude Code's `isolation: "worktree"` or
Antigravity's `Workspace: "share"` on `invoke_subagent` — the tool
assigns the root during dispatch. The brief may say "harness-assigned
isolated cwd"; the worker resolves and reports that root before
writing, and the parent reads it off the worktree list right after the
dispatch (Step 5's audit), without waiting for the report, and records
it. In Antigravity, merge every landing out of a `share` workspace
before any `manage_subagents` `kill`, which deletes that workspace.
Explicit worktree assignment (Codex, Gemini CLI, or Antigravity with
`Workspace: "inherit"`) uses the absolute root returned before
spawning, never this native-isolation shortcut.

Before an isolated agent writes, verify `git -C <root> rev-parse HEAD`
equals the brief's `Expected commit`, its tree is clean, and its
required files exist. A clean tree that starts elsewhere is brought to
that exact commit by whatever git route reaches it; a tree carrying
edits the agent did not make returns `FAILED stage:fork-point`. A
shared worker uses the current tree, including its uncommitted
prerequisites, and does not repair git state. Every child's shell call specifies its
assigned working directory, and every file edit targets that tree.
The orchestrator independently checks the recorded root and base —
the worktree list gives both (Step 5's audit) — and never audits a
hardcoded `.claude/worktrees/agent-<id>` path.

**One build cache for every tree.** Go keys a compiled package by its
directory unless `-trimpath` is set, so every worktree, an isolated
prover's among them, otherwise compiles the whole corpus before its
first `go build` or `go test` answers: tens of seconds and a few
gigabytes of cache per tree. On a machine set up for the pipeline
`go env GOFLAGS` shows `-trimpath` (`engine/xugo-engine.md`, "Session
commands", has the command and the reasoning), and a fresh tree at a
commit built anywhere then only links. The setting is the machine
owner's: where Step 1 shows it absent, tell the user once and go on.
Never pass `-trimpath` to single commands: a package compiled with it
and one compiled without are two cache entries, and a pipeline that
mixes them pays for both.

**Shell and server lifetime.** Step 1's shell variables (`STATE_DIR`
among them) and `erpc`, and the agent's `rpc`, are setup fragments,
not persistent tool state. Define them in each shell call that needs them or pass their
resolved values explicitly; in Antigravity (`run_command`) and Gemini
CLI (`run_shell_command`), working-directory changes (`cd`) do not
persist across calls either, so open each call at the assigned root or
pass `git -C <root>`. Use a retained process session when the
host provides one (`IsDaemon: true, WaitMsBeforeAsync: 500` on
Antigravity's `run_command`, tracked via `manage_task`, passing a
fixed `--port=<port>` and a `--port-file` under the conversation's
`scratch/` directory rather than `/tmp` so sandboxed and unsandboxed
steps never clash on file ownership), or the detached
launch in Step 1 when supported.
Check `/health` in a later tool call before dispatching: `nohup`
alone does not prove that the host kept the process alive. Preserve
the process/session handle and log path for recovery. A child in
another execution environment must be able to reach the brief's
server; sharing a repository does not establish that connection.

**Claude Code's shell: no `$()` in a chained command.** In the Bash
tool under zsh, one command of the form `VAR=$(subcmd) && OTHER=… &&
curl …` intermittently fails with `(eval):1: failed to change group
ID: operation not permitted`. It is the sandbox meeting zsh's process
groups, not the engine, and retrying the identical command does not
help; `VAR=literal && curl …` is unaffected. So the orchestrator and
the prover alike either split the work across tool calls — the working
directory persists between them and shell variables do not, so read
the value in one call and write it as a literal into the next — or,
where one call must chain, paste the value as a literal:

```bash
curl -s http://127.0.0.1:$PORT/rpc -d '{"cmd":"session-create"}'    # returns {"id":"s_abc123…"}
```

```bash
curl -s http://127.0.0.1:$PORT/rpc -d '{"cmd":"add-goal","session_id":"s_abc123…",…}'
```

and never `SESSION=$(rpc '…' | jq -r .id) && rpc '{…"session_id":"'$SESSION'"…}'`.

**Claude Code's isolated shell: no heredoc, no loop, no `'` escape.**
Under worktree isolation the harness refuses as too complex to verify
a heredoc (on curl's stdin, into `python3 -`, or writing a file), a
shell-function definition such as the `rpc` helper, a `for` loop, a
shell variable feeding a command, a `|` inside a quoted `go test -run`
regex, and single-quoted JSON holding a `'` escape; one plain
`curl -s http://127.0.0.1:<port>/rpc -d '…'` or `go test -run X` per
call works. A payload that spells a prime (f', N') goes in a file
written with the Write tool and is sent with `curl -d @<file>`; a loop
or a `-run 'A|B'` battery goes in a script file at a literal absolute
path, run with `bash <file>`.

**Permissions.** Verify the actual runtime permits the assigned
tree, local server access and the required commands before dispatch.
In Claude Code, per-machine `permissions.allow` entries in
`.claude/settings.local.json` can cover `curl -s` / `curl -fsS` to
`http://127.0.0.1:<port>`, scoped `go test`, `go build`, `go run ./library/cmd/xugo_fmt`,
the isolated worker's `git merge --ff-only` repair, and a prover's own
serve: its binary under the scratchpad, `lsof -ti tcp:<port>`, and `kill`
of that PID. In Antigravity, `run_command` runs sandboxed by default
(`BypassSandbox: false`), which permits workspace and conversation
scratch files (and localhost `xugo serve` binding when allowed by
policy) while blocking outbound loopback connections and paths outside
those roots unless permitted: try sandboxed first, and run corpus
queries sandboxed through `./xugo query ...` rather than over HTTP. When
loopback `curl` is blocked, write every session-server JSON payload to
one fixed scratch file (`<scratch>/rpc_req.json`), invoke `curl` with
one invariant command shape (`curl --noproxy 127.0.0.1 -s http://127.0.0.1:<port>/rpc -d @<scratch>/rpc_req.json`,
`BypassSandbox: true`, identical `toolSummary`, no `$()` or `$VAR`
expansion, no `env` or `timeout` wrapper) and at most one `curl` call
per turn so approvals do not collide and prefix-match across calls,
while keeping builds, `go test`, `xugo_fmt` and `./xugo query`
sandboxed. Codex and Gemini CLI follow their own sandbox
and approval rules; this skill and `allowed-tools` cannot override
them. A child denied access reports `FAILED stage:harness` with the
blocked operation. The parent resolves it through the host's permission
flow or reports the limitation; permission failures are not engine
faults.

**The frontmatter.** The skill uses the shared format: `name`,
`description`, version under `metadata`, and `allowed-tools` as a
space-separated string. Antigravity and Gemini CLI read `name` and
`description` for progressive disclosure and ignore `allowed-tools`;
its Claude Code tool names, including the optional `TaskCreate`,
`TaskUpdate` and `ScheduleWakeup`, have meaning only on a host that
recognizes them. No step depends on these task-list conveniences.

# Knowledge files

The pipeline's working memory is one directory, `working_state/`: THIS
CLONE's own state, written by the sessions run here and no part of the
published tree. A clone that has run no session has no such directory,
and each file begins at its first write, in the formats Step 7 gives;
nothing in the corpus, the manual or the constitution depends on what
is in it.

Git ignores the directory, and where it stands follows from that.
Untracked, it stands at the clone's root beside the session store
`data/`: one per clone, shared by its worktrees and lost with none of
them. A clone that wants the notes to keep a history tracks them by
choice (`git add -f working_state`, and `-f` or `-u` at every later
add: a plain `git add` of an ignored path exits 1 even where the file
is tracked); they are then files of each tree and travel by commits.
Step 1 sets `STATE_DIR` to whichever holds, with two lines that every
later block reading `$STATE_DIR` repeats — shell state does not outlive
a tool call (§"The harness"), and a block that reads the variable
unset reads an empty path. Two things below turn on which holds: the
commit at Session end, and the log's rotation.

| File, under `$STATE_DIR/` | Role |
|---|---|
| `proof_curation_log.md` | the iteration log: append-only, except by a rotation (§"Rotating the log") |
| `curation_walls.md` | corpus-wide blockers — every entry carries a runnable repro |
| `curation_known_issues.md` | promoted friction, by surface (Architecture / Kernel / Skill / Sub-agent / Emit — the emitter's defects, human-gated batches) |
| `curation_observation_buffer.md` | first occurrences awaiting promotion |
| `curation_compact_history.md` | the rotation's archive of cards, read only via a `[[compact:iter#N]]` pointer |
| `batch_notes.md` | a fill wave's open batches, one section each: the per-fill details the batch's entry folds in (Step 5, "Batches"); never tracked |

Tags a sub-agent surfaces and where each lands: `[emit-issue]` →
known-issues, its Emit section; `[arch-issue]` / `[kernel-wishlist]` /
`[skill-feedback]` / `[subagent-feedback]` / `[tactic-feedback]` →
buffer → known-issues on the 2nd occurrence; `[wall-candidate]` →
walls once a repro is in hand; `[style-regression]` /
`[curate-mismatch]` → the log entry only.

# Step 1: Setup (once per session)

A session that lays a scope as cards (Step 3) needs the build, the
gates and `xugo query`, not the serve: start the serve at the first
dispatch.

Record the starting HEAD and initial working-tree status, and keep
the set of families this session changes. Session-end verification
includes uncommitted and newly created files as well as commits.

```bash
WORKTREE=$(git rev-parse --show-toplevel); cd "$WORKTREE"      # `go` (1.27 or later) and `curl` are on PATH
WT_TAG=$(basename "$WORKTREE")
# The session store: one per clone, shared by its worktrees, ignored by git.
DATA_DIR=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")/data
# The pipeline's notes (§"Knowledge files"): each tree's own where this clone tracks them,
# else one directory per clone beside the session store. These two lines open every later
# call that reads $STATE_DIR: shell state does not outlive a tool call.
STATE_DIR=$(git rev-parse --show-toplevel)/working_state
[ -n "$(git ls-files working_state | head -1)" ] || STATE_DIR=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")/working_state
go env GOFLAGS      # `-trimpath`: every tree shares one build cache (§"The harness"). Absent: each worktree compiles the corpus again
go build ./... && go vet ./library/... \
  && go build -o ./xugo ./engine/cmd/xugo/

# One serve per worktree, port file namespaced by $WT_TAG. Reuse a live one.
PORT_FILE=/tmp/xugo-serve.${WT_TAG}.port
# The log is kept with the session store: what a serve said before it died outlives a reboot.
mkdir -p "$DATA_DIR/logs"; LOG_FILE="$DATA_DIR/logs/xugo-serve.${WT_TAG}.log"
PORT=$(cat "$PORT_FILE" 2>/dev/null || true)
if [ -n "$PORT" ] && curl -fsS "http://127.0.0.1:$PORT/health" >/dev/null 2>&1; then
  echo "reusing serve PORT=$PORT"
else
  rm -f "$PORT_FILE"
  nohup ./xugo --data-dir="$DATA_DIR" serve \
    --port=0 --port-file="$PORT_FILE" --timeout=12h >"$LOG_FILE" 2>&1 &
  for i in $(seq 1 300); do [ -f "$PORT_FILE" ] && break; sleep 1; done
  PORT=$(cat "$PORT_FILE")
fi
erpc() { curl -s http://127.0.0.1:$PORT/rpc -d "$1"; }

# The serve links the proof registry at BUILD time: a binary older
# than the tree serves a registry without the entries landed since.
# Rebuild + restart is the default preflight before every dispatch.
# The staleness check is a fingerprint, not a guess from file times:
#   ./xugo registry-fingerprint                                            # the binary you just built
#   erpc '{"cmd":"registry-fingerprint"}'                                    # the serve you are about to dispatch on
# Equal digests: the serve cites exactly what the tree registers.
# Unequal: a member landed (or moved key/name) since the serve was
# built — start a SECOND serve from the fresh binary on its own port
# file (never pkill a serve with live agents; the old one expires on its
# own timeout). The cheap pre-check, before any build:
#   find library/proofs -name '*.go' -newer ./xugo | head             # any line = the binary predates a landing
# A log ending `<signal> received, shutting down` means the process was
# SIGNALLED — the inactivity timeout names itself and its duration —
# so a serve that died mid-wave was killed by something; restart it
# and account for the signal, never read it as the timeout.

# Smoke: ONE entry through the harness — every shared mechanism, not the corpus.
XUGO_REPLAY_ONE=nat_arith.AddSym go test -count=1 -run TestReplayAll ./library/integrity/gates/
```

Capability probe on a reused serve: `erpc '{"cmd":"session-lineage","session_id":"x"}'`
must answer "session x not found" — "unknown command" means a stale
binary (pre-lineage); rebuild and restart.

# Step 2: Read previous state (once per session)

```bash
cd "$(git rev-parse --show-toplevel)"
STATE_DIR=$(git rev-parse --show-toplevel)/working_state                 # Step 1's two lines, again
[ -n "$(git ls-files working_state | head -1)" ] || STATE_DIR=$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")/working_state
if [ -d "$STATE_DIR" ]; then
  tail -n 300 "$STATE_DIR"/proof_curation_log.md      # the last few iterations
  cat "$STATE_DIR"/curation_walls.md                  # blockers, with repros
  cat "$STATE_DIR"/curation_known_issues.md           # promoted friction
  grep -n "BUFFERED" "$STATE_DIR"/curation_observation_buffer.md | tail -20
else
  echo "no $STATE_DIR: nothing to read"
fi
```

A file the clone has not written yet answers `No such file`: there is
nothing in it to read.

Engine mechanics live in the manual's §Playbook and §"Chapter Go"
(`engine/xugo-engine.md`) — the canonical home for every
lesson about how the engine behaves; the knowledge files carry
process friction and walls.

# Step 3: Scope (the dialogue layer)

The user proposes a scope: a chapter (a theory, a dozen to a few dozen
statements), sometimes one theorem, seeded by whatever followed
`/prove`. Do the homework, come back with evidence and proposals,
converge before any dispatch.

**Two products, and the user picks which — after the sizing.** The
same homework ends either in briefs — each statement proved bottom-up
and landed with its proof — or in CARDS: the scope landed first as
members stated without proofs, their dependency order written into
their Deps, the proofs filled in afterwards in parallel and in any
order (Step 5 reads them off `query cards`). Which one is the user's
decision, but not a naked
question: "prove these now, or lay cards first?" asked cold sends the
user back to "how big is this?", which is the homework's own first
item. So the order is: do the homework; report the SIZE and the
LAYERS of what is on the table (item 1 below — how many statements the
source covers at the agreed topic, how many the corpus already has,
how many levels of lemma stand between the definitions and the
landmarks, how many families it spans); then recommend one of the two
products with the reason, and ask whether the user agrees. Never
infer the answer from the size yourself — your sense of "a chapter's
worth" need not match theirs — and never ask before the sizing is on
the table. The homework below is the same for both products; "Laying
the scope as cards" after it says what differs.

**Inventory and names are chosen, not inherited.** A chapter's
member set need not mirror a reference's (absorb a theorem into a section
of the member that needs it; promote a recurring anonymous statement
to an entry of its own when it carries mathematics a reader would look
up — recurrence alone promotes nothing, and a fact one `By` of existing
laws closes stays in the proof however often it recurs; a bare
corollary — a statement that one cite of a stated member closes, which
is measured in a session and not judged by eye — is not kept beside
that member, unless it is the statement a reader would look up and
the member does not read as it; rename where
the reference's name obscures the mathematics). The criterion is the chapter's narrative plus outside
fan-in. The inventory IS the mathematics the user wants written, and
the definitions it needs come first.

**A general chapter is extensible.** When the natural statement of a
target needs a notion a general chapter lacks — a permutation of
lists, a law of finite sets, a fold — the notion is a gap in THAT
chapter, not a constraint on the target. Cost it as a member of the
general chapter, ask only whether it will be used again, and propose
the extension beside the target; never a restatement of the target
around the gap. Counting the extension as the target's own cost makes
the worse form look cheaper: unique factorization is stated over
lists because `datatypes/list` gained `list_permutation` for it, and
the permutation's laws serve every later chapter. The form of the new
definition is still the user's to choose.

**Constants are minted, never served.** The corpus knows a constant
only once a chapter mints it through a define door. A member that
spells a name no chapter defines fails to parse at registration, and a
session goal that spells one does not parse either. So
the homework answers, per statement, who mints each constant it
spells: THIS chapter (a definition member, landed before any member
that spells it, and named in the `Deps` of a same-chapter definition
that spells it), an
IMPORT (the family's `imports`), or a reference's spelling the corpus
does not adopt and never mints (mathlib's `Finset.sum`, HOL Light's
`num_divides`: the member is stated by text in the chapter's
vocabulary, with `real_sum` or `∣`). A constant the text DSL spells for its own
surface is still a constant with an owner (`≥` on ℝ is `real_ge`,
minted by real_order_ring). A type is a definition too: the
session's `define` door has a `typedef:` payload (prove the
inhabitation as a goal first; a trivially inhabited shape needs none)
whose sections emit as the chapter's `family.DefineType`, or a
`data:` payload for a datatype. The brief carries the answer as its
`Constants:` line; a sub-agent never invents one.

**Two priors you carry in from elsewhere are wrong here, and nothing
in the session will tell you.** Decide the chapter's FORM against
them before the first brief:

1. *"A dimension is a type."* mathlib indexes a vector by a type
   (`EuclideanSpace ℝ (Fin n)`), HOL Light puts N in the type
   (`real^N`), and every source you were
   trained on does the same. XuGo does NOT: a dimension is a num
   TERM in the statement (`vec⟨n⟩(u)`, `dot⟨n⟩(u, v)`, `‖u‖_n`) and a
   PHANTOM on the Go value (`ext/dimtypes.Vec[Real, DimN]`). A chapter
   over an indexed carrier (`num → A`: vectors, tuples, words,
   matrices) is stated over explicit structure components with the
   components IMPLICIT in the text (`DefEntry.Implicit`; a chapter at an
   instance binds them once, `family.WithInstance`), spells its
   operations by declared NOTATION (`DefEntry.Notation: "‖u‖_n"`),
   declares each operation's dimension slot (`DefEntry.Dim`), and its
   members take `*Vec[Elem, DimN]` closure parameters so the generated
   `At` writes the dimension off the vector. Read constitution
   §Structures ("Implicit component arguments") and §"The typed
   surface" ("The dimension refinement"); `vector/euclidean` is the
   model chapter. A brief for such a chapter carries a `Form:` line
   naming which of these the chapter uses.
2. *"Go has no generic methods."* It does since 1.27, and the proof
   surface is BUILT on them: `a.FixAs[φ]()`, `a.TermAs[φ](text)`,
   `a.LetAs[φ](name, text)`, `a.VecAs[Real, DimN](text)`, `Thm.Inst[τ]()`,
   `Thm.At[DimN](u)`,
   `TypeBinder.BindA[τ]()`. They are not exotic; they are the default
   spelling wherever a value has a phantom, and the untyped `Term` /
   `proof.At(dep, w…)` forms are the fallback. A body that repeats a
   dimension or a type at every cite is the sign the typed spelling
   was not reached for. The language's measured boundary is
   `utils/generic_test.go`; read it before deciding a spelling is
   impossible.

**The homework, per proposed scope** (read, grep, query — no
sessions, no Go yet):

1. **Size and layers.** Before any member is chosen: what the topic
   covers and how it is built. Count: the statements the user wants
   and the objects they need, those the corpus already states (`xugo
   query family`, the READMEs), the levels between the definitions
   and the landmark theorems (Urysohn stands on a shrinking lemma and
   a continuity criterion; Tietze on Urysohn and a uniform-limit
   lemma: three levels), and the families the topic would span or
   open. Where the user supplies a source — a book chapter, a paper,
   a file of another prover's library — read it BY STATEMENT first: a
   list of name, statement and section header for every theorem (a
   one-off extractor for a prover's file; one topology file of another
   library ran to 2.4k statements under 70 section headers), counted
   under the sections the topic names. This is what the product
   question is asked against (above), and what the left-out list is
   measured against.
2. **Members.** The statements, in natural form, and the objects
   they need defined. A reference proof the user supplied for a
   statement — a textbook proof, a script from another prover (Lean
   with mathlib, HOL Light, …) — travels with the member as its blueprint: a
   reference for which lemmas and which case structure, never a step
   chain to copy, and never looked up by the skill itself — the
   corpus ships no other system's sources. Whether the corpus
   already states a member is a question about the mathematics,
   answered by `retrieve` on the restated statement, not by a name.
   There is no separate proving queue.
3. **Triage.** Work each statement's proof out BEFORE committing —
   from the mathematics, and from the reference where there is one: a
   one-step argument (one rewrite, one simplification, one
   first-order search) is a short session; a composite (a wide case
   split, several intermediate claims, a staged construction, a
   nontrivial induction) is decomposed NOW — the phase lemmas become
   members (a shared bridge is landed before the members that need
   it), each its own dispatch. The bar: can one agent close it comfortably in ~30
   ministeps? If not, split before the first brief.
4. **Order.** Which members cite which (the mathematics, or a
   reference's named lemmas) → bottom-up construction order. Mirror pairs. Count
   each lane's DEPTH: a lane whose leaves are already known is
   dispatched bottom-up (each level lands proved); a card is for the
   scope the user chose to lay as cards (below), or for a leaf
   discovered mid-proof that is independent work of its own — too
   large for the dispatch, or another family's — never for a step the
   proof in hand can carry, which is promoted ("What records what",
   above). Beside its pipeline a card costs trust — every member
   citing it stands on an axiom until then — and a card found false is restated and whatever
   was proved on it re-proved, which is why leaves first is the cheap
   order to fill in (`query cards` lists it) though not a constraint.
5. **External frontier.** Dependencies outside the scope: already a
   family entry (a typed cite) / no entry yet (it lands as its own member first —
   there is no string channel) / evidence the boundary should move.
6. **Structure and conventions.** Which shape carries the chapter's
   objects (a structure as a predicate with instance theorems, a
   quotient, a datatype …), read from the mathematics and from what
   the corpus already does for the same kind of object (survey the
   shape before choosing — a sibling chapter routinely writes the
   same move differently, and the divergence is a design input);
   names; which members share which file (the README's sections are
   the file groups; merging related members is the norm, a standalone
   file has a stated reason). Conventions are shown by the code and
   told by the README — never a ledger. Every NAME the pack proposes
   is checked before the pack is presented, because the name the user
   approves must be the name that can land, and a rename after the
   ruling is a second ruling: a family basename is global (it is the
   registered-name prefix and the Go package name — `ls
   library/proofs/*/` for the collision, and two families in one pack
   cannot share one), and a constant is a kernel-wide word, so a
   generic mathematical word carries its domain's stem (`set_cross`,
   not `cross`, which the vector cross product wants; `vec_space`, not
   `space`). The question for each is "would another domain want this
   bare word?" — never "does it clash inside this domain?". The
   topology horizon's pack proposed `sets/product` and
   `topology/product`, one basename for two families, and `cross`;
   all three were caught at scaffolding and landed under other names.
7. **Domain placement.** A family sits under the domain its
   DEFINITIONAL layer is closed in (`rational` is a predicate on ℝ,
   defined through ℝ's own constants, so the chapter lives under
   `real/`, not beside the integers) —
   read the definitions, not the subject matter.
8. **First packet.** What to dispatch first — usually the definitions
   and the conventions-setting member, worked in pilot mode. The
   pilot's cites are the convention every later author copies: read
   the constitution's paragraph on dependencies first (a definition a
   member merely unfolds is not a dependency).

Present the pack; the user decides. Never decide alone: boundary or
member set, conventions, framework changes, packet scope, or any
deviation from what was agreed.

**Laying the scope as cards.** When the user chose cards, the pack is
not prose: it lands. What differs from a proving packet, in the order
it happens:

1. *Definitions and boundary first — discussed, then landed.* Every
   card's text spells the chapter's constants, so a definition changed
   after forty cards is a sweep; and whether a notion is this
   chapter's, a new family's or another domain's (a product of sets
   belongs to sets/, Zorn's lemma to relations/) is boundary. Bring
   the user, in one message: each constant to mint (its name, its
   form where a choice exists — "convergence asks every term to lie in
   M; the reference asks it eventually" — and its family), every new family,
   every cross-domain mint, and what is LEFT OUT with the reason —
   the names already checked as item 6 says. "The
   corpus has no such constant" is never the reason — minting is what
   a skeleton does; a placement or a dependency the user has not ruled
   on is. The user decides; then land the definitions and scaffold the
   new families yourself.
2. *Cards land, then the user reads them.* A card is a statement and a
   note — the mathematician's work (rule 4), yours to write, not a
   dispatch — and it is cheap to restate while nothing stands on it
   (its own key, no citer), so write them all, land them, and hand
   the user the `cards` page (`xugo query cards F`) and the READMEs
   to read, not a list in chat. Read every card
   cold before minting it, against its degenerate cases (the empty
   set, `⋂∅ = 𝕌`, an interval `⟦a, b⟧` with b < a and the set empty,
   M = ∅): a false card is an axiom until someone fails to prove it,
   and no gate reads a card's truth — two of the topology skeleton's
   forty-six changed in that reading. Read them together once more for
   structure that recurs across the cards — a compound term spelled out
   in many statements, one shape of hypothesis or conclusion stated
   again and again: a statement is cheapest to change before anything
   cites it, so name what may be a concept (a defined constant, a
   structure, a member stated once and cited) and bring it to the user
   beside the cards; Step 6.5's category 9 asks the same of proofs.
   Read each card's place in the graph as well. A card with empty
   `Deps` claims that its proof unfolds the definitions and uses
   nothing a reader would name; test the claim against its note.
   Every step the note names — an integration by parts, a Cauchy
   criterion, a compactness argument, a sibling's theorem — is a
   member to name in `Deps`, proved or a card. A step the corpus
   states nowhere is a missing layer: a card of its own when several
   cards stand on it, the filler's promotion when one does. A card no
   member cites claims a place of its own — a target of the chapter,
   or a statement a reader will look up or a later chapter will cite
   — and is dropped when it has neither. Read an uncited card first as
   a question about the others: a `Dep` missing there leaves uncited a
   card that half the chapter stands on. Measured once, on the hundred
   cards of nine analysis chapters: of thirty-five with empty `Deps`,
   nine were basic; of thirty with no citer, eleven were needed by
   cards that had not named them (one by fourteen), and two had no
   use. Then, before the user reads
   them, the REFEREE PASS below: the author's reading is the weakest
   reading of their own cards, as Step 6.5 says of proofs, and a card
   is served as an axiom, so its truth gets at least the review a
   proof's readability gets. Dispatch one generic sub-agent
   per family group (cards that cite each other go together),
   read-only, no tests, in parallel, each with this brief — the
   ENCODING paragraph written for the chapter at hand, since that is
   where false statements hide (a dispatch's prompt is literal: paste
   the whole brief into every call):

   ```
   You are an independent mathematical referee for a formal proof
   corpus. READ-ONLY: edit nothing, run no tests or builds, start no
   servers. One job: find CARDS THAT ARE FALSE. A card is a theorem
   stated WITHOUT proof and served to the corpus as an axiom until
   proved; a false card is an inconsistency, so each must be true
   exactly as written. No machine check exists; you are the check.

   Repository root: <worktree root>. A card is an entry whose Build is
   `family.Card(<statement>, <note>)`; the note sketches the intended
   route. Theorem / Law / Define entries are proved or definitions —
   use them as facts, do not review them.
   `<Struct>.Statement("BODY")` is `∀<components>. <pred>(…) ⇒ BODY`.
   Implicit arguments: <which constants leave which leading argument
   out, under which binder names>.

   THE ENCODING — read it twice:
   <the chapter's traps, each one sentence: what a statement without
   the structure hypothesis claims (an ARBITRARY family / distance /
   operation); what lies outside the carrier (a set may leave ⋃T, a
   map is total on the type); the degenerate values (⋂∅ = 𝕌, ∅, a
   one-point space, r ≤ 0, a centre outside M); where each
   constant's definition is (the definitions.go files — read them
   first, they are what you check against).>

   For every card in your files: (1) expand the statement fully and
   state what it claims; (2) try to break it — degenerate values,
   missing hypotheses, quantifier order, each direction of an ⇔;
   (3) if it survives, check the note's route works with the
   hypotheses the statement HAS; (4) report no style, no wording, no
   card found true.

   OUTPUT, plain text: first line `REVIEWED <n> cards in <files>`;
   then one block per problem, most serious first —
   `<family>.<Name> — FALSE | LIKELY FALSE | UNSURE | NOTE WRONG`,
   `Claim:` the expanded statement, `Counterexample / gap:` concrete
   (name the family, the sets, the map), `Fix:` the smallest change
   that makes it true. A FALSE needs a counterexample checked against
   the definitions; an UNSURE says exactly what was not settled.
   Per file with nothing: `<file>: all true as far as I can verify`.

   YOUR FILES: <the family group's card files + its definitions.go>
   ```

   Check each finding yourself before acting (a referee reads the
   same text you did, and can misread it the same way); a FALSE is a
   restatement, re-keyed, before anything stands on it; a NOTE WRONG
   is a note edit. What a referee establishes about a card that is
   TRUE — which hypothesis is load-bearing and why, what the empty
   set or an empty family does to it, which axiom enters where — goes
   into the entry's `Reading` field (registry.ProofEntry.Reading, a
   definition's DefEntry.Reading): the dossier serves it to the next
   reader, and it is otherwise thrown away with the report. The pass does not replace the user's reading and
   is not Step 6.5: the fresh-eye reads a proof's readability with the
   kernel standing behind its truth, the referee reads a statement's
   truth with nothing behind it; when the card is later filled, its
   proof takes the fresh-eye like any other. Measured once, on 269
   cards over thirteen families: five referees in parallel, five to
   nine minutes each, no false statement, three wrong notes and two
   missing citations found, which the author's own cold read of the
   same cards had not.
3. *The form.* `family.Add(registry.ProofEntry{Name, Key, Deps, Build:
   family.Card(statement, note)})`: the statement in the family's
   vocabulary exactly as `family.Theorem` will read it — in parts
   where it has a premise (`Statement{Binders, Hypotheses,
   Conclusion}`, one hypothesis per line), the one string where it
   has none, a law's body through the door alike — the note
   naming the statement's source where it has one and the
   proof's route in two or three sentences — the brief its filler
   reads; `Deps` the entries the proof will cite, narrative (nothing
   replays them). A skeleton's cards land in the family's `cards.go`,
   which holds the cards and nothing else: the definitions go to
   `definitions.go`, the blank imports linking the vocabulary to
   `definitions.go` or `family.go`; a card laid beside the theorems of
   its subject stands in their file. A law-shaped card inside the
   structure's own family is written
   `family.Card(IsTopology.Statement(body), note)` — the
   text `IsTopology.Law(body, …)` will have, so the fill keeps the
   key; in another family the same door is the structure's, qualified —
   `family.Card(topological_space.IsTopology.Statement(body), note)`,
   filled by `topological_space.IsTopology.Law(body, …)` (a structure's
   Law and Statement serve every family: `vec_space` states its laws
   through `comm_ring.CommRing.Law`, `compact` through
   `topological_space.IsTopology.Law`). A statement that needs the axiom
   of one of TWO spaces spells `is_topology(T) ∧ … ⇒` itself. Write the entries Key-less — the
   `Define`, `DefineStructure` and `DefineSpec` literals too, which carry a
   Key as a theorem's entry does — and let
   the gate write the keys: `XUGO_PASTE_KEYS=<domain>/<family>[,…] go test
   -count=1 -run TestEntryKeyIsOwnKey ./library/integrity/gates/` pastes
   each missing (or moved) `Key:` of the families named under its
   entry's `Name:` and formats the file (`xugo_fmt`'s layout);
   then `go generate ./library/...` (the typed wrappers), a row in
   `gates/implicit_args_test.go` per implicit-argument definition. The README marks each card ` — card` in its
   members table; and the domain aggregator's doc and the sibling
   READMEs are re-read, because a skeleton falsifies prose invariants
   silently ("no theorem here carries `is_topology`", "nothing here is
   stated about a particular space" — both fell to the first one).
4. *Verify* as a landing: TestCards, the lint battery, the index gate
   and the scoped replay — a card SKIPs ("served as its axiom"), so
   the replay checks the proved members around it. The family graph
   takes an edge from every constant a statement spells, and
   `TestFamilyGraphAcyclic` refuses a card stated over a constant of a
   chapter that stands on the card's own chapter, naming it.
5. *The fill is Step 5's "Filling cards"*: one card, one brief with
   `Statement source: card <entry>`, one lineage, by anyone at any
   time; a session whose goal IS a card's statement is not closed by
   the card, and the landing keeps the card's name and key — filled in
   `cards.go`, it leaves that file for the proof file of its subject.

The reading that chooses the backbone is item 1's: the source read by
statement, then the chapter's existing split deciding each one's
family.

**Scaffold on first dispatch — or on the definitions' landing.** A
new family: `library/proofs/<domain>/<family>/{family.go, README.md}`
+ an empty `<family>.cnf.pb` + the blank import in the domain
aggregator or `library/proofs/proofs.go` — BEFORE `go generate`:
gen_family regenerates the families the registry holds, and a package
no aggregator links is not one of them — then `go generate
./library/proofs` (one run over every family writes
`zz_typed_thms_gen.go`, and `zz_vocab_gen.go` where the family
declares vocabulary rows). `xugo
query` refuses a family without its README, and so does `go generate`:
the README's title line, `# <family> — <gloss>`, is where the chapter's
gloss is written, and gen_family writes it onto the package as its doc
comment — one sentence, so a gloss holds no period followed by a space.
Below the title and before the first `##` section the README opens with
its introduction, written with the scaffold: prose saying what the
chapter holds and how it is organized, which the lint battery asks of
every family (`TestLintReadmeIntroduction`), a family of definitions and
cards included.
The empty blob is fine
while the family holds only definitions and cards; the measured-blob
lint (`TestLintFamilyPBMeasured`) asks for the recorder's stamp once
the first proved member lands. A proof file reads the bare names of
the proof surface — the verbs (`By`, `Cite`, `Have`), the typed
shorthands (`Expr`, `Arrow`, `Nat`, the letters) and the phantoms of the
types minted below the chapters (`Real`, `Int`, `Ind`) — through
`import . "github.com/euc-ai/xugo/library/authoring"`, which every
file that spells one carries and no other file does (Go refuses an
unused import); a new family's first proof file writes `*Expr[Real]`
from its first line. The phantom of another CHAPTER's type (`Complex`,
`List`) is aliased by the generated wrapper file only once a REGISTERED
statement of the family names that type, and gen_family needs the
package to compile: until then name it by its owner
(`*Expr[complex_field.Complex]`). Once aliased it stays while a proof
file of the family names it bare, so a statement moved out of the
family takes no alias from the files it leaves.
`library/proofs/iterate/monoidal/` is
the live template. The README is the chapter's mathematical story — what the
theory is and why it is organized this way — with at most one line of
framework mechanics and a pointer to the constitution. Its introduction
is that story in brief and is kept true as the chapter grows: a section
added, a framework laid or a chapter split re-reads it. A formula
Unicode cannot set plainly is written in LaTeX and the rest as it is,
by the constitution's rule for a README.

**A single theorem** is the degenerate case: the theorem, its
reference if the user gave one, one brief, no scaffolding. **A single card** is the other: the card's
statement and note, one brief, no scaffolding, the landing at the
card's key (Step 5, "Filling cards").

# Step 4: Build the brief

Self-contained — the sub-agent is cold-started. Assemble from the
statement, the constitution, the
knowledge entries Step 2 surfaced, and the chapter's decisions. Start
from `xugo query dossier <member>` for a card or a member being
restructured: it carries the statement in both spellings, the
definitions the statement spells with their readings, the plan under
the card, who stands on it, the instances supplying each hypothesis,
the family's variants and the cite at its witnesses — most of the
brief's `Deps available`, `Constants` and `Conventions` lines, read
off the tree rather than remembered. A wave's dossiers are one call,
`xugo query dossier <member> <member> …`: each call loads the corpus
anew.

**Parse every statement of the packet before the first brief.** One
scratch session bound to the family, `add-goal` each statement, read
`inspect`. It takes minutes; every brief then pastes a statement known
to read at the door, and the ambiguities that would cost a dispatch
show in the goal as the engine read it — one `Σ` glyph standing for
two different folds inside a single equation was visible nowhere
else.

**Session or direct — the orchestrator's call, written into the
brief.** A proof is found in a session and transcribed from it: that
is the default, and it is the default because of what the other way
costs. An author who writes a proof with any search in it straight
into Go meets a panic, guesses a fix, meets the next panic, and goes
round; one closed exploration and one `emit-section` would have
replaced every one of those rounds of builds and records, and the
author is the last to see it, since each next guess looks like the
last one needed. So the choice is not left to the author, whose
confidence is exactly what goes wrong: the orchestrator decides it
before the dispatch, from the task, and the brief's `Mode:` line
carries it. A prover never takes direct mode on its own.

The rule cuts the other way too. Most refactors are ordinary
programming — two members share a sub-argument, and it becomes a
member both cite — and sending such a task through a session costs
an exploration of a proof that already stands in Go, and the rounds
of RPCs that come with it, to reach what the author could write in
one pass.

- `Mode: direct` — every step can be written down before the task
  starts, because the proof already stands in Go: moving or merging
  members or files; extracting a sub-argument that members share into
  a member of its own, verbatim or with a ground term generalized to
  a binder; citing such a member in place of the inline chain it
  replaces; renaming, relabeling, rewording; re-spelling a step the
  recorder has already measured. The brief names the source of each
  proof the task moves, by file and member. A task that can name no
  source is not direct.
- `Mode: session` — everything else: new mathematics, a proof that
  does not yet stand in Go, a step whose shape cannot be written down
  before trying it. Where the steps are not visible at a glance, the
  task is exploration, and trial and error belongs to the session.

In direct mode the recorder is the oracle, one named fix per failing
leaf and then a session for that leaf; the prover's §"Direct mode"
has the steps, and the orchestrator working a direct task itself
(rule 1) is held to them.

A direct brief is sized for that oracle. The recorder certifies one
member at a time, for the edits it ran after, so a brief of a few
moves is checked move by move and a brief of thirty is checked at the
end or not at all: an author with the whole list in front of them
rewrites files into scratch copies and records nothing until the
rewrite is done, and a wrong move is then found an hour later, by the
orchestrator, with no record to say which move it was. Measured once:
two agents with about thirty rulings each, in one shared tree, worked
an hour and landed nothing; the same rulings as fifteen briefs of three
to seven moves, each move recorded, all landed, and every failed record
was closed by the fix it named. So a refactor beyond a few moves goes
as a sequence of briefs — to fresh agents in the orchestrator's tree,
or as messages to one isolated agent that keeps its context — each
landing before the next is sent. Keeping the context serves the briefs
that build on one another; it does not tie a family's refactor to one
agent however long it runs. An agent that has done a good share of the
work is replaced by a fresh one: by then the early briefs no longer
inform it, and a new agent sheds the stale history and the memory it
holds. The orchestrator reads every landing
at its boundary, and a brief that proves wrong costs one step, not the
wave. A block moved whole is checked by the build and its record like
any other move, so a brief's ban on scripted edits covers edits of a
proof, not the move of one.

```
Target: <the entry's name | the statement, natural form>
Statement source: de novo (the user's statement[, after <the reference it was restated from>]) | card <entry> (minted in session <id> | landed)
Statement: <verbatim — the natural form the entry will sign>
Family: <domain/family>; package library/proofs/<domain>/<family>/ ; write into <file>.go
Entry: var <Name> = family.Add(registry.ProofEntry{Name, Key, Build}) — write it BARE and Key-less, with no Deps
       (the recorder writes what the proof reads);
       `XUGO_PASTE_KEYS=<family>.<Name> go test -run TestEntryKeyIsOwnKey ./library/integrity/gates/` writes the Key
       (the member alone: a sibling's file in the same tree is never touched);
       every dep is an entry var (no string channel)
Deps available: <entry vars; one landed in this wave's shared tree before its family was regenerated is cited untyped, `At(Entry, w…)`>;
                <names landed since the serve was built — rebuild the serve before citing them>
Constants: <each constant the statement spells → minted by this chapter's <Def entry> (land it first) |
            import <family> | a reference's spelling the corpus does not adopt (state the member by text in the chapter's vocabulary)>
Blueprint: <the user's proof sketch | the card's note and the statements of the members it names | a reference proof the
           user supplied, verbatim (a textbook proof, a script from another prover) — for its lemmas and its case
           structure, never a step chain to copy>
Strategy hint: <the decomposition Step 3 chose; lemma candidates; for a reference script, the session moves its tactics correspond to>
Shape target: <technique — e.g. "the relation-transfer law applied at R, its obligations as Haves">
Conventions: <the chapter's — structure shape, naming, what the file groups>
Form: <for an indexed carrier: the definitions' Implicit / Notation / Dim declarations, the family's
       WithInstance, closure params as *Vec[Elem, DimN] after the dimension binder; for a structure on a set:
       the hypothesis as its typed fact (group GroupFact[on.C]), guarded points as *Member[A, on.C],
       sub-structures as projection readings — or "plain">
Known friction: <knowledge entries that apply, with their repros>
Worktree root: <absolute path assigned to THIS agent; or "harness-assigned isolated cwd" for native isolation only>
Worktree mode: shared | isolated
Expected commit: <exact commit SHA for an isolated tree; "current working tree" for shared>
Mode: session | direct (<the source of each proof the task moves: file, member>)
Server port: <PORT — fresh, from the preflight; a direct brief carries it too, for a leaf that turns into exploration>
Session: fresh (family <name>[, imports …]) | resume <session id> (a lineage this member was already worked in) | none (direct)
Scratch prefix: <Name>_    (concurrent agents share the scratchpad)
README: return the member's README row and any prose sentence in the verdict; the README is the
        orchestrator's file (the agent doc's constraint 1), never ask the agent to edit it
Read first: <the required chapter and dependency files in the assigned tree>
For an isolated tree, verify the root, clean status and Expected commit before writing.
  A CLEAN tree whose HEAD is elsewhere is brought to that exact commit by any git route
  (a fast-forward, a checkout of the commit) and rechecked; a tree carrying edits you did
  not make is FAILED stage:fork-point. Include any finished file inline. Never repair a shared tree.
```

One preflight that costs one command:

- **Own key.** An entry's `Key` is its own statement's normalized key;
  the brief says "paste the printed key",
  never a guessed one.
- **A card's brief.** The target is the card's statement
  (`statement_typed` from `query cards`, paste-ready for `add-goal
  {text}`; a card written in parts enters as `add-goal {entry}`, its
  abbreviations with it); the landing REPLACES `family.Card(…)` in the
  card's own entry with `family.Theorem(<the same statement>, body)`
  — same name, same Key, the members citing it untouched. A restated
  statement re-keys: say so in the verdict, and the citers replay one
  hop. What a card's brief says of the corpus it reads off the corpus:
  a member it names as a proved model is one `query member` reports
  proved (`"card": false` — a dossier's `variants` and a file's name
  list cards and theorems alike), and whether the corpus already
  states the card's conclusion is answered as for a chapter's member,
  by a goal-mode `retrieve` on the statement, its result in the brief:
  a card a member already implies is a ruling for the user, not a fill.
  When a chain/cochain or other mathematical twin is proved, the
  brief names its body: reuse its spellings where the statements agree,
  and explain any necessary difference. Tell the agent whether the README
  already has a members table. A brief need not carry ℝ-arithmetic workarounds — `by {arith:true}` reads a product of
  variables as one unknown, so "name the product with `DenotedAs`" is
  retired; what a brief may still need to say is that a product's SIGN
  comes only from its factors' resident signs (an inverse factor's from
  its argument's), and that a symbolic divisor is cleared from a goal's
  quotient but not out of a hypothesis, where the law is cited. A
  positive FACTOR cancels out of a hypothesis on its strict sign, with
  nothing cited. `real_pow(x, 2)` and
  `x * x` are ONE unknown to the closer (a power with a literal exponent
  is its monomial; measured on complex_abs.AbsSquare), so a brief
  never prescribes `PowTwo` for arithmetic. The manual's Playbook
  section is the reference for all of these.
- **A verb at a new shape.** A `Shape target:` that leans on a VERB at
  a shape the corpus has not used (`ByInduction` at a parameterized
  principle, `Where` on a cross-type law, …) is a hypothesis about the
  engine read off the verb's documentation, not a measurement. Probe it
  once — one scratch site, one strict replay — before the first brief,
  exactly as every statement is parsed once, and write the brief from
  what fired: the measured spelling, or the hand-written shape. The
  closure chapter's first brief said "one ByInduction with two Cases"
  from the manual; the verb could not read the principle, and the same
  line was about to go into five more briefs. A `ByInduction` is
  rehearsed in a session as `by_induction` (the principle by key; its
  predicate read from the goal, or under `term_specialize` where it is
  not the goal): the leaves it opens are the obligations the file's
  Cases will prove.
- **An induction's other binders.** Whether the statement's OTHER
  binders are stripped before the induction is a choice about the
  induction HYPOTHESIS, and the brief makes it. Left ∀-bound, the
  hypothesis is quantified: `rw` refuses it and a `By(Normalized, ih)`
  spends it, usually at a key. Stripped — the closure's typed
  parameters — it is ground at those variables and `ih.Rw()` fires it
  with no search. Write "fix m, induct on n" unless the step needs the
  hypothesis at another instance; a one-binder statement has no choice
  to make (the manual's `induction` row).

# Step 5: Dispatch

**Serve preflight — rebuild + restart** whenever the tree has grown an
entry since the serve started (the registry is linked at build time).
Measure it, every dispatch: `find library/proofs -name '*.go' -newer
./xugo` names the landings the binary predates; after `go build`,
the binary's `registry-fingerprint` against the serve's
`{"cmd":"registry-fingerprint"}` says whether the serve is the tree
(Step 1 has both lines). When a sibling agent has live sessions on the
old serve, build to a second path and start a second serve on its own
port file — never `pkill` the pattern; the old serve expires on its own
timeout. A landed name the serve does not know cannot be cited until
it is rebuilt, and the brief's "Deps available" list must resolve on
the serve it names.

The preflight covers a dispatch, not the run after it. A prover that
lands a member and needs it in a session builds the tree and starts a
serve of its own, one at a time, opens a fresh session, and stops that
serve by its PID (the prover file, §Connect, "Your own serve"). A wave's
promotions are therefore no reason to leave the session, and the brief's
`Mode:` line holds through the run.

Dispatch `xugo-prover` in the background, the brief its whole prompt
(§"The harness" has the call). Shared-tree workers see the current
uncommitted files; same-family workers run sequentially. Isolation
requires an identified commit containing all the brief's prerequisites.
Pin that exact commit, verify the assigned tree, and verify the serve
contains its dependencies. When a later wave needs new landings,
choose and verify its base again.

Where native isolation cuts an agent's tree is not fixed — the main
checkout's head, the dispatching branch and origin's master have all
been seen — and it need not be: a clean isolated tree is brought to the
Expected commit by git before its first write (the brief's last lines),
and the result is what is checked.

**Audit the assigned trees right after the dispatch**, by the worktree
list and never by a path convention: list `git worktree list
--porcelain` before dispatching and again after, and the worktrees that
appeared are the agents', each with its HEAD in the listing. Record
them — they are the paths the rotation's scan excludes — with the HEAD
each started at:

```bash
WT_TAG=$(basename "$(git rev-parse --show-toplevel)")
git worktree list --porcelain | awk '/^worktree /{print $2}' > /tmp/xugo-worktrees.$WT_TAG.before   # before the dispatch
# … dispatch …
git worktree list --porcelain | awk '/^worktree /{p=$2} /^HEAD /{print p, $2}' \
  | while read -r root head; do grep -qxF "$root" /tmp/xugo-worktrees.$WT_TAG.before && continue
      echo "$root started at $head"; done
```

A tree that started off the Expected commit is no fault: the agent
brings it to that commit before writing, and the verdict's `Tree:` line
says where it stood (§"Merging worktree landings"). Where the
orchestrator created the worktree itself (§"The harness"), the root is
in hand and the same record is kept.

If required prerequisites are uncommitted, commit them on the
session's own branch (rule 10) and pin that commit; the orchestrator
makes this dispatch commit, never the prover. Do not rebase or
cherry-pick merely to prepare or finish a wave.

A `FAILED stage:session-unavailable` is a recovery request:
health-check, restart, re-dispatch the same brief. A `FAILED
stage:harness` reports a tool or access limitation: resolve the
reported operation before re-dispatch, rather than restarting the
serve. A `CURATED`
report whose `Promoted:` line is not empty minted and proved those
members beside its own; the merge takes them with it. One whose
`Cards:` line is not empty landed the member standing
on cards it minted; the cards are the next dispatches. Each is read
as a laid card is (Step 3, "Laying the scope as cards", item 2), its
`Deps` included — the prover names them at the `defer`, and a
deferred card is work too large for the session, so empty `Deps`
there is a claim to test, not a default. Read them from the store,
not from the reply:

```bash
./xugo --data-dir="$DATA_DIR" cards                  # every card a lineage minted or is proving
./xugo --data-dir="$DATA_DIR" cards --lineage <id>   # the cards one lineage minted or is proving
./xugo query cards <F>                               # one chapter's cards, leaves first, statement_typed with each
```

`cards` and `query` link the registry at BUILD time like the serve:
rebuild the binary after a landing, or a landed card reads `landed:
false` in `cards` with its lineage as parent, and `query cards` misses
it. A card `attacked_by` another lineage is
being proved there — do not dispatch it twice. A card a proved entry
states is no card and is not listed.

**Filling cards.** A card is filled by anyone, at any time, in any
order: one card is one brief (`Statement source: card <entry>`, the
statement from `statement_typed`, or `add-goal {entry}` for a card
written in parts), one `xugo-prover` dispatch, one
lineage, and its landing keeps the entry — `family.Card(…)` becomes
`family.Theorem(<the same statement>, body)` in the card's own entry,
same name, same key. A card laid in a proof file is filled where it
stands. A card in the family's `cards.go` is not: that file holds
cards only (`TestLintCardsFileHoldsCards`), so the filled entry moves
to the proof file of its subject — beside the theorems a reader looks
for it with, a new file named for the subject when no file's subject
fits — and a `cards.go` left with no entry is deleted. The brief's
`write into` names that file, chosen as a batch is cut, by where the
proofs will live. The entry keeps its name, so the package compiles
with it in one file or the other and never in both: the move is one
edit, the new file written and the card deleted before the next build. The move is inside the package: the citers replay
unchanged and nothing downstream sees it. The corpus is sound relative
to its cards at every moment, so a tree holding cards is its normal
state and not a transition: there is no "all filled" and nothing
waits for it; a chapter is proved to the extent the `counts` of
`query family F` say, and that census is the whole progress report. The model is
distributed by construction — today one piece, tomorrow another, one
person here and another there — and what follows is what that asks of
each filler.

- *Entry.* `/prove <family>.<Card>` fills one card, the degenerate
  session with no scaffolding; a session may fill one or a wave. The
  state is read off `query cards` and `cards` (rebuild the binary
  first), never off the log or a list in chat.
- *Order.* Leaves first is the cheap order, not a constraint. A card
  found false is restated and re-keyed, and whatever was proved on it
  replays one hop or is re-proved; filling its leaves first keeps that
  blast radius small, which is what `query cards` sorts by (ties by
  citers).
  A non-leaf filled first is legal all the same — its proof cites the
  cards below it as the axioms they are — and the right card to fill
  is as often the one a downstream chapter needs today.
- *Blueprint.* The card's note, with the statements of the members it
  names — `xugo query dossier <card>` assembles both, with the
  card's reading, the definitions it spells and the instances its
  hypotheses have: it was written from the mathematics in the
  chapter's vocabulary, and the referee pass (Step 3) checked its
  route against the statement's hypotheses. A reference proof the
  user supplied is attached only for a composite card — one whose note
  says what to split off first — and then as a reference for its case
  structure and its boundary cases, never a step chain to copy; where
  the corpus's encoding differs from the reference's (a product
  defined pointwise, sequences where it has nets) the reference
  misleads.
  The decomposition is the orchestrator's, before the brief (rule 4).
  A card's `Deps` are narrative and go with `family.Card` at the
  landing; the landed member's are what its proof is recorded reading,
  and the brief says so.
- *The lock.* `attacked_by` names a lineage in THIS machine's session
  store and reaches no other machine. Across people the lock is the
  merge: the fill that lands first stands, and a second proof of the
  same card is compared with it — by the path each takes, every card
  assumed filled — and the choice put to the user. So a filler says
  which cards they are on where the others can see it (the branch, the
  pull request).
- *Concurrency on one family.* Two fillers in one family change the
  same blob; the merge is `merge_cnf_blob` over the commit both
  started from, never a pick (Step 6, merging worktree landings).
  Inside one session the rule is any
  wave's: same-family dispatches sequential or worktree-isolated (rule
  5). A skeleton's cards cluster in a few families; use isolation
  when the committed prerequisites above are available, otherwise
  fill each family's cards sequentially in the shared tree.
- *Batches.* A wave reviews and logs by batch, not by fill. A batch
  is to a fill wave what a packet is to a chapter session — the unit
  Step 6.5 reads, and here the unit of Step 7's entry as well — cut
  by where the proofs will live rather than by what was dispatched
  together: cards that belong together, best the ones that will end
  up side by side, in one file or one section, or stating one
  construction from its two ends; one family is the usual case, not
  the rule. A reviewer reading siblings together is what finds two
  proofs of one lemma, a helper three fills each wrote, a spelling
  that drifted between them; a fill read alone shows none of it, and
  an entry per fill only grows the log. The size is a judgement, not
  a number: large enough to read as one story, early enough that the
  conventions a family's first proved members set are still cheap to
  change. Cut the batches before dispatch and work the queue batch by
  batch, so that each closes: a batch closes when its landed cards
  are all in. A card that FAILED or was restated leaves it for the
  queue and is named in the entry with its verdict; a card a proof
  `defer`red joins it, since it will sit beside them. Per-fill
  details (key, sections, recorded keys, session, tags) wait in
  `$STATE_DIR/batch_notes.md`, one section per open batch, never
  tracked; the batch's entry folds them in and the section is
  deleted. What waits is the entry and, with it, the routing of the
  batch's tags, whose stamp names the entry; what never waits is the
  report: a `FAILED`, a `[curate-mismatch]` or a wall candidate stops
  for the user at once (Step 8).
- *Per fill, after Step 6.* The usual landing and two steps a card
  adds: the README row loses its ` — card` marker and continues to
  state the theorem, without adding proof-method commentary (`xugo
  query cards` reads the registry, so the card leaves the frontier as
  it lands); and the fresh-eye (Step 6.5) and the log entry (Step 7)
  are the batch's, above. The family's FIRST proved member needs
  nothing more: its recording stamps the blob that held only cards,
  which is what `TestLintFamilyPBMeasured` asks (Step 3's scaffold
  paragraph). The referee's work on that card is over.
- *Discovery.* A proof that needs a lemma proves it as a member beside
  its own, in the same dispatch — a promotion, cited by its siblings
  like any member. It `defer`s a card only for independent work of
  its own, too large for the dispatch or another family's: a new card
  lands beside the member, the stock grows, and `query cards` shows it. A card
  found false or ill-posed is restated — its citers replay one hop,
  and a proof in flight elsewhere that cites it does so by the entry
  var, so it is unaffected until it merges — or deleted, with what
  stood on it re-proved. Neither stops a wave; both are logged.

# Step 6: Verify (independently — never trust the verdict line)

```bash
cd "$(git rev-parse --show-toplevel)"
N=<Name>; FAM=<path.Base of the family name>
grep -rqE "Name:\s*\"$N\"" library/proofs/ --include='*.go' || echo "not registered"
XUGO_REPLAY_ONE=$FAM.$N go test -count=1 -timeout=300s -run TestReplayAll ./library/integrity/gates/
go test -count=1 -run TestLint ./library/integrity/gates/     # the whole lint battery, ~3 s — a label over the cap, a rendered role tag left on a label or a positional hyp sits in the tree until a sibling trips on it otherwise
grep -rn TestThm library/proofs/ --include='*.go' | grep -v _test.go    # expect empty
go build ./library/... && go vet ./library/... && go run ./library/cmd/xugo_fmt -l library/proofs/ && gofmt -l library/integrity/
```

A landing that mints cards adds one gate: `go test -run TestCards
./library/integrity/gates/`, which checks each card is closed and
carries its note, and logs the per-family census.

`REPLAY_ONE` takes the REGISTERED name (`<path.Base(family)>.<Name>`)
and fails loudly on a typo; a `-run` filter that matches nothing
prints `ok`. That one subtest is the whole gate for an ordinary
landing. Widen with `XUGO_REPLAY_SCOPE=<family names, comma- or
space-separated>` when
the landing changed a statement or landed a row another family
cites — the
instrument adds the consumers across family boundaries and refuses a
bad token.

**Evidence audit (every restructure verdict).** Pick one checkable
engine claim the verdict makes and reproduce it in a fresh session
(two RPCs). A fabricated navigation does not survive this. The
`Session:` id resolves through `session-lineage` — read what the
agent actually did. A direct verdict has no lineage unless a leaf
went to a session: read the diff against the sources its brief named,
and the recorder's log, instead.

**Regenerate once, at the commit boundary.** With the wave's landings
in your tree and no prover writing there, run `go generate
./library/...` once, before Step 6's gates: the typed wrappers and
vocabulary of every family (the bare entries wrapped in place), the
authoring surface and the policy witness. Every generator is
idempotent and byte-gated, so there is nothing to decide: one with
nothing to write writes nothing, and the gate names the one that was
skipped. The index's pages are not among them: nothing here reads
them (`xugo query` answers from the registry), and the gate suite holds
what the index refuses (`TestFamilyGraphAcyclic`). A policy change is never a way to exempt a use the
fixed point denies. While a prover still writes in a shared tree, the
in-place wrap would touch the file it is editing, so regenerate the
landed families alone until the wave settles: `go run
./library/cmd/gen_family -pkg <package>[,…]` — the flag takes a
family's package name, the last element of its path (same-family dispatches
are sequential, so a landed family is quiet), which costs about the
same and gives the next refill typed deps.

**GC the recorded families once per commit, never per landing.** A
recording only adds rows and a merge only unions them, so a blob
holds rows no member reads until it is collected; nothing reads them,
and no gate asks for their absence, so a landing, a merge and a review
fix each leave the blob as it is. Collect once, at the session end
(below): after the last merge and the last recording, before the
replay of the scope, which is what verifies the collected blob:
`XUGO_FAMILY_CNF_GC=<domain>/<family> go test -v -run
TestRecordFamilyCNF ./library/integrity/gates/` for every family whose
blob moved or that lost a member since the last commit (`git status
--porcelain -- library/proofs` names the moved blobs), one pass each.
A GC runs no proof: every recording writes the member's row record —
the certificate and plan keys its run touched — and the GC keeps
exactly the rows the members' records name and drops the rest, in the
time it takes to decode the blob. A member the blob holds no record
for — no row record, or one naming a row the blob lacks — is measured
by the GC as a recording measures it, warm against the committed
blob, and that costs the member's run; a pass that stops at a refute
there is run again as it is, at the default budget and never a larger
one: the live search is nondeterministic and a loaded machine slows
it, so a few runs decide it, one that goes through collects the blob,
and only a refute cut off on every run is a proof to reshape (the
manual's Lesson 4b). A shaping's footprint is the member's own
touched rows, which its recording lists under `leaves of <Name>`: a
key the shaping made unnecessary is absent there, and leaves the blob
at this GC. An empty-blob record still over-records (every leaf falls
to the conditioned rung's live search); it is for a new family and
for a rung-class engine change, followed by one GC, which measures
every member and whose S7 audit lines are read for the family as a
whole. The GC refuses to write a blob that does not replay strictly
and whistle-free at a member it measured (it names the member); a
family it refuses cold keeps its committed blob and is GC'd warm
until the member's route changes. An S7 "inert" line — a shape
element, `Broadcast`, a `BySets` premise — means a recording of the
`By` without the element touches no row the `By` with it does not (the
keyless rung, or the same certificates and plans) — apply the drop,
then re-record; a key or a plan the drop would add in the element's
place does not count as inert.

**Merging worktree landings.** Check the verdict's `Tree:` line first —
`git -C <root> rev-parse HEAD` is the Expected commit — then copy the
agent's new file (or the member
block it appended to a shared file) into your tree; merge README rows
and any section header two siblings both invented by hand; then merge
the blobs, which diverged from yours: `go run
./library/cmd/merge_cnf_blob -base <that HEAD> -theirs <root>`
unions the rows either tree's members read and takes each member's
dependency and capability rows from the tree that recorded it, in
seconds and with no proof run. A member recorded in both trees — one
card filled twice, one proof edited in both — keeps your rows and is
named: the scope's replay holds every member to its rows, and one it
names is recorded again, alone. Then regenerate, and replay the
family's scope. Card-text constants
collide when two agents each invented one: keep the family's one and
point the others at it.

**Consolidate the wave's files.** Per-packet files are a dispatch
artifact: at aggregation ask whether the wave's files should be one
file and whether that file joins a sibling. Merging is free (bodies
move verbatim, no key moves); the two non-mechanical parts are the
prose's scope ("the file's one induction" is false at the merged
scope) and references to deleted filenames in sibling files.

# Step 6.5: Fresh-eye review (per landed packet; in a fill wave, per batch)

The author cannot fresh-read their own landing. After Step 6 passes,
dispatch ONE generic sub-agent, read-only, no tests, with
this lens and no expectations:

```
You are a fresh-eye reviewer for a proof corpus. Read as a
mathematician seeing these files for the first time. Do NOT edit —
report only. Run NO tests. One question: could a reader unfamiliar
with the theorem reconstruct each proof's idea from the file alone —
first with the comments, then with the comments deleted?

Files: <the packet's or batch's proof files + each family's README.md>
Quality bar: library/chapter_constitution.md §"What 'elegant'
means", §"Argument structure", §"Citation forms", §"File granularity".

Report per category (say "clean" where you find nothing):
1. Reader gaps — unexplained Actions, magic tokens, names that do not
   match the comment's vocabulary, idiom departures without a why.
2. Readability — dead fields, one-line mega-terms, shadowing, xugo_fmt.
3. Doc-code drift — README claims contradicted by the code.
4. Structure — flat chains, premise piles, a nested argument that wants
   a statement of its own, duplicated statements that want a shared
   section, godoc surface, a hypothesis the proof never
   reads or reads only for a weaker one (direction: weaken in place).
5. File grouping — should these files be one, and join a sibling?
6. Cross-layer motifs — repeated proof mechanics suggesting a missing
   primitive of the engine or the authoring surface (a verb, a closer,
   a reading).
7. Narration economy — one story told in several homes; comments
   restating adjacent code; a fact named in prose that the body lacks.
8. Construction-order leaks — grep for tier numbers, packet or wave
   labels, dates, "landed"/"closed", sibling filenames.
9. Concepts in waiting — a structure that recurs: a compound term
   spelled out across many statements, one shape of hypothesis or
   conclusion stated again and again, one argument rebuilt in several
   proofs. Repetition is where a new concept can be born — a defined
   constant, a structure, a member a reader would look up, a general
   theorem whose home is a more general chapter — and it is as often
   plain repetition. Report each as a question, not a fix: where it
   recurs, what concept it might be, and what naming it would cost
   (statements re-keyed, citers moved). "clean" is a good answer.

One line per finding: <file>:<line> — <category> — <what + direction>,
tagged where a routing tag fits. End with one paragraph on the
reconstruction test.
```

Route tagged findings through Step 7; batch the mechanical fixes into
one pass; bring judgment findings to the user at the next report. An
over-strong hypothesis is batched with the mechanical fixes and
weakened in place without a ruling (the constitution's §"Inventory and
names"), re-key and all, and moved where the wider statement's chapter
is; it goes to the user only where the weakened member would duplicate
one the corpus has. A
category-9 finding is always the user's: read it as a mathematician —
is it a concept, who else would use it, what naming it costs — and
bring it as a discussion item, whatever latitude the user gave on the
other findings.

# Step 7: Log + route feedback

Iteration entry → `$STATE_DIR/proof_curation_log.md`, in a call that
opens with Step 1's two `STATE_DIR` lines. The log begins
with its title `# Proof Curation Log` and a `## Log` heading, the
archive with `# Curation compact history` and `## Compacted
iterations`; a clone's first write creates the directory and them. An
entry:

```
### Iter #<N>: <Name> <VERDICT>
**Key:** <hash>   **File:** <path>   **Statement source:** de novo | card
**Sections:** <M>   **Session:** <id>   **Deps:** [<names>]
**Fresh-eye:** clean | <K> findings — <routed tags> + <M> fixes batched
**Notes:** <the agent's observations, your verify, what you probed>
**Tags:** [<tag>], …
```

In a fill wave the entry is the batch's (Step 5, "Batches"), one `N`
for the batch, its heading naming every member with its verdict:

```
### Iter #<N>: <family.A>, <family.B>, <family2.C> CURATED (cards filled); <family.D> FAILED
**Statement source:** cards   **Fresh-eye:** clean | <K> findings — <routed tags> + <M> fixes batched
**<A>:** key <hash>   file <path>   sections <M>   session <id>   deps [<names>]
**<B>:** … one line per member, from the batch note
**Notes:** <per member, the agent's observations and your verify; then the batch read together — what the siblings showed>
**Tags:** [<tag>], …
```

The batch's tags route when this entry is written, since their stamp
names it; the report to the user never waited for it (Step 8).

`N` is one above the largest number of every heading in the file —
`grep -oE '^### Iter #[0-9]+' "$STATE_DIR"/proof_curation_log.md | grep -oE '[0-9]+' | sort -n | tail -1`,
after the same two lines — never a tail read: numbers collide across concurrent sessions and
the heading is the unique key, so after the append, and again before a
commit, the same grep piped to `sort | uniq -d` must print nothing new.

Route every tag per the table above (buffer format: summary, first /
last seen, observation, why it matters, direction, status; promote on
the 2nd occurrence by copying into known-issues and marking the buffer
entry PROMOTED). A tag that routed nowhere is a routing mistake. A
correction to an entry that was promoted goes into the PROMOTED copy:
the known-issues text is what the next session reads, and a buffer
entry corrected alone leaves the wrong diagnosis standing there.

An entry built on a REFUSED tactic carries the request as the agent
sent it — the JSON — and the response verbatim. The session store
keeps only the applies that succeeded, so a refused shape cannot be
re-run from the lineage: without its request text the entry can be
believed but never verified, and a reviewer who rebuilds the shape
from its words tests a different one.

# Step 8: Report to the user

Between reports you run the pipeline over the agreed packet. Stop and
summarize at the agreed points and on any anomaly (`FAILED`, a
`[curate-mismatch]`, a wall candidate — immediately, not after more
packets). The summary: what landed (members, sections), what is open
(lineages and their open leaves), findings awaiting the user's decision,
proposals for the next packet. There is no chapter-closing ritual: a
chapter is whatever its package says it is, and the next session can
improve it.

# Session end

GC every family whose blob moved or that lost a member (Step 6, one
pass each), then replay the scope of every family this session touched
(`XUGO_REPLAY_SCOPE`). Use the recorded family set and check it
against the diff from the session's starting HEAD, including staged
and unstaged changes, plus untracked files under `library/proofs/`.
Include both families of a moved entry; distinguish pre-existing
user changes using the initial status. A committed-only branch diff
does not cover an uncommitted session. Then rotate the log if it
passed 1200 lines and this clone tracks it (§"Rotating the log").
The landing is the user's to shape (rule 10): propose it — one commit
of the chapter files and the policy witness, with the knowledge files
where this clone tracks them, or the split the work suggests — and
make it on the user's word, on the current branch; the session
branch's work-in-progress commits are squashed or kept as that
decision says. Moving changes to another branch requires its own user
instruction; never push.

## Rotating the log

The log is append-only; a rotation is the one edit that deletes from
it, and the one step where two concurrent sessions collide — two
sessions applying this policy to one base file select the same
entries. It fires when the log is above 1200 lines and cards the
oldest bodies until the file is at or under about 1000. Protected,
never carded: the six most recent iterations, and any iteration a
live knowledge entry points at for operational detail through
`[[compact:iter#N]]` (a bare `First seen:` stamp is not such a
pointer; a card satisfies it).

**Only a clone that tracks the log rotates it.** A rotation deletes
bodies and leaves cards, and git is what keeps the bodies (step 5). An
untracked log is left to grow: Step 2 reads its last 300 lines and
Step 7 numbers by its headings, whatever its length. The paths below
are a tracking clone's, whose directory is each tree's `working_state/`.

1. **Scan for a rotation in flight, before appending your own entry.**
   Enumerate `git worktree list --porcelain`, preserving each full
   path; exclude the exact child-worktree paths recorded at dispatch,
   not a guessed name pattern. In every remaining tree inspect
   `git diff HEAD --numstat -- working_state/proof_curation_log.md`
   for staged and unstaged edits, and inspect log commits reachable
   from that tree's HEAD but not your own. These read-only checks
   cover both a sibling's uncommitted rotation and one it committed;
   they do not depend on an integration branch's name. Read the
   ratio, not the dirtiness: a live session's own entry is a pure
   append, a rotation deletes an order of magnitude more than it adds;
   compare a stale sibling's file with the newer committed log before
   reading it as a blocker. On either signal, skip the rotation,
   append your entry only, and say
   so in the entry — a skip by decision otherwise reads like a skip by
   threshold.
2. **Build a card per eligible body, oldest first**, from the entry's
   own structured fields: the `### Iter` heading verbatim; one line
   `**CARD.** Rotated from the log <date> (iter #N); full body in git log -p`;
   the `**Tags:**` segment verbatim (in a one-line entry, from
   `**Tags:**` to the end of the line); and any `[curate-mismatch]` /
   `[style-regression]` detail verbatim — those two tags have no
   promotion route, so the card is their only durable home. Never a
   paraphrase of the Notes: nothing is judged on the way out, and an
   iteration whose detail is wanted is one `git log -p` away.
3. **Append the cards to the archive's tail in log order and delete
   the bodies from the log.** A card's home is the archive, never the
   log.
4. **Add a `> **Rotation <date>: N -> M.**` paragraph to the log's
   header**, then count again — the paragraph adds lines.
5. **Assert**: the log still starts with its title;
   `grep -oE '^### Iter #[0-9]+' working_state/proof_curation_log.md | sort | uniq -d`
   prints no new line; and the archive's duplicate-heading count rose
   only by the number collisions you moved — the orphan check: a body
   carded by one session and deleted by neither is the damage it
   catches. Full bodies stay in
   `git log --follow -p -- working_state/proof_curation_log.md`.

If a sync afterwards still meets another pass over the same entries,
take its cards whole and drop yours — both are built from the same
fields — and keep both sides' disjoint bodies.

# Reference

**Verdicts** (the first line of every sub-agent reply):
`CURATED <Name>` (an entry landed and replays; its `Promoted:` line
lists the members it minted and proved beside it, its `Cards:` line
the cards it minted, each the next dispatch), `FAILED <Name>`
(stage, output, cause, lineage id). Any other shape is a
`[subagent-feedback]`.

**Parallelism.** Same-tree parallel agents on one family are
forbidden: they write one package — its proof files, its generated
wrappers, its README — and a save of one that does not compile stops
the other. Their recordings alone do not collide: a recorder holds a
lock on its family's blob from its read of it to its write, and a
second one waits. Worktree-isolated agents on one family are fine,
with the orchestrator recording each landed member into the blob
sequentially afterwards. Cross-family parallelism is always fine; the
one thing a lane does that reaches the others is to move, rename or
delete an entry, which stops every reader of the dependency graph in
the tree until the blobs carry the change, and the prover file's
§"Direct mode" makes the edit, the build and the rename one step.

**Pilot mode.** When you author a member yourself, the agent doc is
your instruction file too; the review in Step 6.5 is not optional
there — self-review is the weakest review. While same-tree agents are
live, every save you make must compile — the tree is their gate too —
or pilot in a worktree of your own.
