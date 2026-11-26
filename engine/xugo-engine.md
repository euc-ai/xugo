# The XuGo manual

Four parts: the session's commands, the playbook, the design rules, and
chapter Go, the surface a proof is written in.

# Session commands

Binary: `engine/cmd/xugo/main.go`

Build, from the repository root: `go build -o xugo ./engine/cmd/xugo/`

The binary links the whole corpus, so a build that finds nothing in
Go's build cache compiles every family: tens of seconds and a few
gigabytes of cache. The time is the families' dependency chain, each
package waiting for the ones it imports, so past a handful of cores
more of them do not shorten it. Go keys a compiled package by the
directory it was compiled in, and a second checkout or worktree
therefore pays all of it again.
Under `-trimpath` the key drops the directory and every tree shares
one cache: a tree whose packages were compiled anywhere only links, a
few seconds, and a tree that differs recompiles the packages it
changed and the ones that import them. A package compiled with the
flag and the same package compiled without it are two cache entries,
so the flag reaches every `go` command alike, `go test` and `go vet`
among them, or it saves nothing. It is therefore set once per machine,
in Go's own environment, and never on a single command:

```sh
go env -w GOFLAGS=-trimpath    # replaces GOFLAGS: join it to the flags `go env GOFLAGS` already shows
```

A binary built this way names a source file by its module path
(`github.com/euc-ai/xugo/core/…`) where a plain build prints the
absolute path: in a panic's stack, and to a debugger.

Quick discovery: `xugo --help` lists all commands. `xugo <command> --help` shows per-command details with examples.

---

## Commands

### Corpus (read-only)

| Command | Purpose |
|---------|---------|
| `query <what> …` | The corpus as a whole. `what` is `overview`, `map`, `family`, `member`, `dossier`, `deps` / `dependents`, `between`, `definition`, `definitions`, `cards`, `axioms` or `graph`. **Entry below: `query <what> …`.** |
| `browse` | The corpus to read in a browser: the family graph, each member's proof graph, a search of the theorems. CLI only. **Entry below: `browse`.** |

A session has ONE exit: `emit-section`, whose output the author lands as
a registered family entry — the family package is a chapter's record,
force-replay its gate. A serve started with `--data-dir DIR` persists
its sessions there: lineages under `DIR/sessions` and the CNF
certificates and conditioning plans they record, with the
certificates' exact keys, under `DIR/cnf_cache`
(engine.SessionCNFStore, one file per key) — a CACHE, read back by
`emit-section`'s strict re-run and by `session-create {resume}`; a
member's certificates live in its family blob. Deleting the directory
costs a live re-search; after a change that moves keys it is deleted,
not re-keyed. The records of the engine faults the sessions met are
under `DIR/faults` (§"Engine faults"), and are no cache: an open one is
work owed.

#### `query <what> …`

**The corpus as a whole** (library/index — the one reading of the registry
behind this door and behind `xugo browse`, so what it answers and what a
reader browses are one thing). `what` is one of:

- `overview` (the panorama, read first: totals and per-family counts in
  four strata — `proved` outright, `on_cards`, `cards`, and `postulates`,
  the members assumed outright — one line per family with its gloss and
  `height` in the dependency graph, and the weighted `domain_edges`.
  Under 80 KB, readable whole; it carries nothing another question serves —
  a family's imports are in `family`, the cards and the heads of their
  plans in `cards`)
- `family` (`{"family":"real/real_sequences"}` → the chapter: gloss,
  imports, importers, counts, members in registration order with statements,
  each with its `gloss` and `internal` or not. A family is named by its
  path or, failing that, by its short name alone, the path's last
  element and the prefix of its members' registered names
  (`real_sequences`), while no other family has that short name; a
  short name two families share names neither, and the refusal lists
  their paths.
  `{"families":["…","…"]}` asks for several in one answer, `families`
  and `unknown`, as `member` does below; CLI:
  `xugo query family <family> <family> …`)
- `member` (`{"member":"…"}` → one member in full, the door that shows a
  member: `id`, `entry` (its registered name) and `key`; `statement` and
  `statement_typed`, its two texts (see "A member's two texts" below);
  `kind` and, for a definition door's entry, the `shape` it served; `deps`
  and `dependents`, and `used_by` as `dependents` below has it; its `card`
  flag and `note` — `card: true` for a member
  stated without a proof, `note` then what its proof must establish, and
  `backing` its recorded support, read off the registry and never off the
  note's sense: `theorem_deps`, the deps that are no definition door;
  `note_names`, each member name the note mentions resolved to a `member`
  id, or to `candidates` when chapters disagree, or to nothing; and
  `note_names_not_cited`, the members the note names that the deps do not
  list. A card whose note names no member and cites definition doors alone
  shows every list empty, written — and
  the `cards` it stands on, its card frontier: every card under it through
  its dependencies, itself included, empty when the corpus proves it outright; its
  `depth`, its `reading`, what it `concludes`, its `constants` and, split
  by where the statement mentions them, `conclusion_constants` and
  `hypothesis_constants` — what the member establishes and what it asks
  for — defines, source; and two things read off the chapter file as
  text, once per file and only when asked: its `gloss`, the doc comment
  above the member with the `Name — ` left off, and its `outline`, the
  narration of its proof step by step as written — per step the `verb`
  (Have, Show, ObtainAs, When, Cases, …), its `label`, its `claim` where
  the verb takes one, the members its proof `cites` by id — named in the
  step or through a local a `:=` bound to a citation; a member named to
  form a statement (`Entry.Statement(…)`, `Entry.Law(…)`) or a structure
  entry read as an instance is no citation — the other names it `uses`,
  its `depth` under the argument and its `line`. A step's claim is what
  the replay proved; its label is prose, served as written. Empty for a
  member with no Go argument. What a proof names is among what its
  replay recorded (`deps`): the lint `TestLintProofNamesRecordedDeps`
  holds every proof to it;
  and, for a PROJECTION law — one whose body states another structure —
  the `projection` it states and the laws `readable` through it — the
  laws of that structure, each with the `body` the reading states in this
  chapter's spelling and, for one that is itself a projection, the
  `projection` it states, under which the reading continues (the family
  page's "Readable through a projection"; a longer chain, and every
  reading by goal, is the `retrieve` entry's readings group); and, for a
  member a door call registered together with others, the call's id as
  `door` (`algebra/group/group.GroupOps` on `group.GroupMulDef`). The
  members it names are index ids. `{"members":["…","…"]}` asks for several
  in one answer: `members`, the answer for each member, and `unknown`,
  each name no member carries with its refusal, both in the order given.
  CLI: `xugo query member <member> <member> …`, two or more names)
- `dossier` (`{"member":"…"}` → the member in the round, what a reader or a
  filler wants before citing or proving it: the statement and
  `statement_typed`; its `gloss` and `outline`, as `member` has them; its
  `reading` and, per constant it `spells`, the
  definition's statement and reading; its stratum (`status`), a card's
  `note`, `depth` and `fill_order`; the family's place (`height`, strata
  counts), the README's `narrative` paragraphs that speak of it; the
  `plan` under it, `deps` and `dependents` with
  statements, and `used_by`; `supplies` — per predicate its hypotheses apply, the members
  concluding it, the instances it applies to; its `variants` in the family
  by shared constants; a projection law's `projection` and `readable`, as
  `member` has them; and `cite`: the witnesses in stated order, the Go
  `At` call, the structure it is a `law` of. `{"members":["…","…"]}` asks
  for several in one answer, `dossiers` and `unknown`, as `member` does;
  CLI: `xugo query dossier <member> <member> …`)
- `deps` / `dependents` (`{"member":"…","depth":N}` — level by level;
  `depth` absent is 1, `0` the whole reach. The levels are what a
  member stands on: the entries its proof reads and the definitions it
  opens (`Unfold`, `Unfolded`), which the family's blob records beside
  them; `member` and `dossier` list the opened ones among `deps` as
  `unfolds`. A definition is also stood on where a statement spells a
  constant it mints, which reads no entry and opens nothing, so
  `dependents` of a definition door's member also answers `used_by`: each
  member that does not depend on it and whose `statement` spells a
  constant it mints, with the constants. A definition is unused when both
  are empty, never on `levels` alone. `{"members":["…","…"],"depth":N}` asks for several
  members' in one answer, `neighborhoods` and `unknown`, as `member` does,
  the `depth` every member's; CLI: `xugo query deps <member> <member> …
  [--depth N]`)
- `between` (`{"from":"…","to":"…"}` → a shortest citation chain in either
  direction)
- `definition` (`{"const":"nat_gcd"}` → the defining member, the members
  whose statements mention the constant per family, `concluded_by` — the
  members whose conclusion mentions it, by stratum, `proved` then
  `on_cards`, `card`, `postulate`, the definition doors left out — and
  `assumed_by`, the members whose hypotheses mention it, by stratum; both
  written when empty, an empty `concluded_by` saying the corpus states the
  constant and never establishes it; `cited_by`, the members standing on
  the definition, and among them `unfolded_by`, the members whose proofs
  open the constant; a type's name or a declared word is refused naming the
  member that minted the type or the constants the word spells.
  `{"consts":["nat_gcd","int_gcd",…]}` asks for several in one answer:
  `definitions`, the answer for each constant defined, and `undefined`,
  each other name with its refusal, both in the order given. CLI:
  `xugo query definition nat_gcd int_gcd …`, two or more names)
- `definitions`
- `cards` (every card, each fillable now and in any order: `leaves`, the
  cards citing no card, a proof of which is proved outright; `on_cards`,
  each with the cards it stands on, a proof of which cites them as axioms;
  `heads`, the cards no member cites with the size and depth of the plan
  under each; then every card in fill order, leaves first — the cheap
  order, not a schedule — and the members `standing` on one. Each card
  carries its `note`, its citers and its `statement_typed`, paste-ready
  for `add-goal {text}` (absent where the print does not round-trip;
  `add-goal {entry}` states a landed card with its abbreviations).
  `{"family":"…"}` or `{"families":["…","…"]}` — each a path or a short
  name, as `family` takes them — keeps those families' cards and the
  members of theirs standing on one; a name naming no family refuses
  the question. CLI: `xugo query cards [<family> …]`. The fill order puts
  a card after every card its dependencies reach, through proved members
  too (a proof may use them), ties by how many members stand on it, then
  by name: filling leaves first only finds a false card before much is
  proved on it. A family's census — how many of its members are proved,
  on cards, cards — is `family`'s `counts`.)
- `axioms` (every member the corpus serves as an axiom: the `postulates`,
  assumed outright and for good — the registry admits one,
  `nat_num/peano.Infinity` — each with the members citing it, and the
  `cards` in fill order, each with its note and citers. A cite of either
  is a cite of an axiom, and nothing else in the corpus is one).
- `graph` (`{"scope":…}` → the corpus drawn (`library/visualize`), one of
  two graphs laid out: its nodes and edges with their coordinates, as the
  page drawing it reads them. `families` is every family on the row of its `height`, the
  foundations at the foot, in a block as wide as its name, with its counts
  — `members`, those `proved` outright and among them the
  `proved_theorems` and the `theorems_on_cards` not proved yet, the
  `postulates` and the `cards` — its gloss, its README's introduction (`intro`, the
  prose before the first section, block by block, a formula the README
  writes in LaTeX typeset as MathML), its `definitions` by name — a door
  call that registered several members by its own — and its `theorems`
  by name, each with its `status` — `proved`, `on_cards`, `card` or
  `postulate`;
  `edges` `{s, t}` say s imports t, transitively reduced. `proof` (`{"member":"…"}`) draws a member. A theorem's graph is its proof,
  drawn left to right as the results it stands on, the member (`target`)
  in the last column, at three `grains`: `compact`, `standard`, `deep`.
  The nodes are chosen from the dependency graph alone. Every theorem of
  the member's chapter in its cone is one (`own`), and so are the
  chapter's definitions those cite (`definition`). Of each other family,
  the theorems cited from outside it that gather a part of their chapter
  under them — a node's `steps` count the units of its family it stands
  on through that family — and that no other such theorem of the family
  gathers in turn. Every card the member stands on is drawn at every
  grain, whatever its family: the cards drawn are its card frontier, the
  `plan` its dossier lists. A card has no proof to draw, and every unit
  it cites — its `deps`, a theorem of any size or a definition of any
  family — is drawn at every grain. A family many more families stand on than
  stand on the member's own is ambient: of its theorems, those a node of
  the others cites directly are drawn (`ambient`), apart, under the
  grain's `line`, and so are its cards.
  A finer grain counts fewer families ambient and admits smaller
  theorems, and says its rule in `allowance`, `theorems` and
  `per_family`. `edges` `{s, t}` say s
  stands on t with no drawn node between them, marked `via` where that is
  no direct citation; an edge to an `ambient` node is a direct citation,
  and every one is listed, and an `ambient` card no node cites directly
  has the edges of the relation reduced over every node drawn, each
  `via`. A door call that registers several members from one
  literal — `DefineData` (a datatype's principles and a record's fields),
  `DefineType`, `DefineQuotient`, `DefineInductive` — is one node named
  by the literal's `Name` (`algebra/group/group.GroupOps`), and a member
  the call registered is drawn as the call. A node carries its `status`
  (`proved`, `on_cards`, `card` or `postulate`), the `theorems` it stands
  on in the whole corpus — its results, theorems and cards, a postulate
  counted no more than a definition — and the `cards` among them, its
  `statements` — a member's statement as `member` has it, with the
  `abbreviations` it spells, its `reading` where it has one and what a
  definition mints (`shape`, `defines`, `type`), and a door call's part
  by part — and its
  `gloss` — a member's as `member` has it, or its row in the chapter's
  README where the chapter leaves it uncommented, a formula in it
  typeset as in `families`; a door call's is its first part's, the
  comment above the call. A definition's graph is one drawing — `grains`
  holds it alone — of what it is built from and who uses it, and
  `definition` counts the `users` and their `families`. Left of the
  definition is every unit it cites, under the same edges. Right of it
  is one column: the units of its own family that use it, each with its
  `use` — `defines` (a definition whose statement names a constant it
  mints), `about` (a theorem whose statement names one) or `cites` (its
  proof cites or unfolds it, and its statement names none) — under the
  headings in `groups`; then every other family as one node (`use`
  `family`, `users` the units it stands for), the family with the most
  first and those past 24 under one node (`more`). An edge runs from the
  definition to each. The rules in full are the headers of
  `library/visualize/proofgraph.go` and `definitiongraph.go`. CLI: `xugo query graph families`,
  `xugo query graph proof <member>`; the pages drawing the graphs are
  `browse`'s).

A member is named by its index id (`real/real_sequences.CauchyConverges` —
the registered name with the family's full path, so two chapters with one
basename never collide), its registered name, or its own key; an answer
names members by id, and a session cites one by its registered name — the id
from its last `/` on (`real_sequences.CauchyConverges`). A bare name, the
name after the family's (`CauchyConverges`), is no reference but a search:
`member`, `dossier`, `deps` and `dependents` ask of every member under it,
family by family, and answer a list however many that holds (`AddAssoc`
holds one for each number system) — in a question of several names,
each bare name's members stand in its place. `between` and `graph proof`,
asked of one member each, take a bare name one member alone has and
refuse one several share, listing their ids. A field a question
does not take is refused by name. Internal lemmas are listed like every
member, marked `internal`. CLI: `xugo query overview`,
`xugo query deps <member> --depth 2`, …; `--root DIR` names `library/proofs`
when the working directory is not under the module.

A new question is read from the outside in: `overview` to choose the
families whose glosses speak of it, `family` for their members' statements,
then `member` or `dossier` for the candidates — each one's card frontier,
its note, how to cite it. The CLI loads the corpus on every call — the
registry's members at process start, every statement spelled behind
`index.Load` — some seconds each, so the candidates are asked for
together: `family`, `member`, `dossier`, `deps`, `dependents` and
`definition` take several names and answer them in one call, where a loop
of calls loads the corpus once per name. A running serve answers the same questions at `POST /rpc`, the body
`{"cmd":"query","what":…}` with the fields below, and loads the corpus
once, so a reading that asks many different questions, every family say,
asks them of a serve.

##### Finding vocabulary on a carrier

Names such as `group_on`, `comm_ring_on` and `injective_on` state
properties on a specified carrier. The ambient comes first and the
subject last — `injective_on(c, f)`, `compact_in(T, k)`,
`prime_ideal(R, p)` — and a structure on a set names its carrier
first too, then its relations and operations,
`comm_monoid_on(c, op, e)`, `equivalence_on(c, R)`; a group, ring or
field predicate takes its record, whose `carrier` field is the set,
`group_on(G)` (constitution, §"Inventory and names"). The suffix says nothing
about tactic support: query the definition and the laws it supplies.
Structure laws use the carrier's membership
guards; see [A structure is read on its carrier](#a-structure-is-read-on-its-carrier)
and [The structure doors](#the-structure-doors) for readings at an
instance and typed members.

For functions, start with `injective_on(c, f)` for injectivity on `c`
and `image(f, c) = c'` for the image being exactly the target carrier.
`inverse_on(c, f, y)` chooses a preimage of `y` in `c`, with the carrier
first as in `injective_on`. Its right-inverse and membership laws
require `y ∈ image(f, c)`; its left-inverse law needs injectivity
on `c` and `x ∈ c`. Outside the image it has no useful guarantee. The
[functions README](../library/proofs/sets/functions/README.md#a-named-inverse-on-a-carrier)
gives the inverse, uniqueness and bijection laws.

When a proof needs the reverse of a group, ring, module or simplicial
isomorphism, look up that structure's `IsomorphismInverse`: these
theorems use the named carrier inverse, degree by degree for simplicial
sets. Start with the constant's definition to find its family and
users, then read the members' dossiers, in one call, for their guards,
citation forms and their families' README narratives:

```sh
./xugo query definition inverse_on
./xugo query family sets/functions
./xugo query dossier functions.InverseOnLeft ring_homomorphism.IsomorphismInverse
```

### Session (stateful proof navigation)

| Command | Purpose |
|---------|---------|
| `session-create` | Create a new proof session → returns `{id}`. In every session, previously proved authored sections are citable siblings, a cite must name a registry entry — its registered name or its own key (force-replay of the landed file is the cycle gate), `emit-section` renders the family form. Optional `"family":"iterate/real/real_sum"` (plus `"imports":["words/machine_word",…]`) BINDS the session to a chapter: every registered definition of the bound families installs as a use rule — `proof.DefinitionSimpRules` over the entry's served shape (`registry.ProofEntry.Definition`) and its replay promise, the ONE derivation the session `define` also installs from — so the bare `simp` fires the chapter's definitions with zero setup (`simp_all` with them; `simp_with` fires only the rules it names) and a fire emits as a typed cite of the entry — and every theorem the bound chapters marked `Simp: true` (`registry.ProofEntry.Simp`, the chapter's simp set, Lean's `@[simp]`) installs beside them, in its stated orientation, reported with shape `simp`. The response carries `binding:{family, imports, installed:[{entry, shape, rule}]}`. Import a family for its DEFINITIONS, never to make its members citable — a cite names any registered entry the bound family's package can name in Go, imported or not — and read what an import installs: `int_num/int_construction`'s definitions are the CONSTRUCTIONS of ℤ's operations, so a bare `simp` under that import unfolds `int_mul` into `int_of_real(real_of_int(x) * real_of_int(y))`; `def_expand` the one constant you mean, and `restore` to the auto-checkpoint when a `simp` did more than that. Bound once, before any goal; a bare session has the same semantics with nothing installed. |
| `session-create {"resume":"<id>"}` | Resume a persisted session under its own id. **Entry below: `session-create {"resume":"<id>"}`.** |
| `session-lineage` | `{"session_id"}` → the session's transcript, summarized: `{id, created_at, persisted, events:[{seq, kind, section?, goal_id?, summary}]}`. Read it to see what a resumed (or a sibling agent's) session actually did; the summary carries the tactic type and its effect. An event of kind `fault` is an engine fault the session met, with its record's id (§"Engine faults"). |
| `defer` | An open leaf becomes a CARD — a member of the session's family stated without a proof, standing on the `deps` named — and the leaf closes by citing it. **Entry below: `defer`.** |
| `cards` | The cards the session store knows of — those a lineage minted with `defer`, and those a lineage is proving — with the lineages. The corpus's cards, who stands on them and the order to fill them in, are `query cards`. **Entry below: `cards`.** |
| `faults` | CLI only, no serve: `xugo --data-dir DIR faults` lists the engine faults on record that no one has acknowledged and exits 1 while there is one. **Entry below: Engine faults.** |
| `dump-section` | Preorder step+goal walk of one section's proof tree: `{"session_id","section":<idx>,"max_nodes":<opt, default 400>}` → `{proved, num_nodes, truncated, nodes:[{path,depth,step,statement,proved}]}`. Built for reading a section's proof — a resumed lineage's, or your own closed one — since proved interiors are invisible to the open-goal index: read what each step actually proves instead of guessing from the emitted Go. A `by` prints as `By(<n> premises; <closer>)`, and the closer is the one the step was CONFIGURED with (`cnf`, `arith`, `settac`), not what closed it: a `by` the apply rung or a keyless stage settles still prints `cnf` and records no key. Key demand is never read off this walk — the recorder's `leaves of <Name>:` lines are the key oracle (§"The recorder's two gates"). |
| `emit-section` | The session's one exit: a proved section rendered as a member of a family. **Entry below: `emit-section`.** |
| `add-goal` | Add a proposition, given by `goal.text` — with `goal.abbreviations`, the names the text and the proof's texts spell as `«Name»` (§"Abbreviations") — or by `goal.entry`, a registered member stated as its author did, abbreviations included, as a proof goal to the session. The text is read at the session's statement door (`engine.StatementDoorScope`, the scope a served `statement_typed` is checked against): a name it neither binds nor declares is an error, a type variable must be spelled by a binder or a `⟨⟩` tie, a constant's type letters are its own at every occurrence, and the session's family supplies the implicit components and the `&` domain. A session states only constants the corpus defines: define a constant first (the `define` door, or the chapter's Go door). A table declaring a name an earlier section declares with another text is REFUSED, naming both texts (§"Abbreviations"). A goal states a closed theorem: a text with hypotheses left of `⊢` is REFUSED, naming its closed spelling (its variables ∀-bound, its premises ⇒-antecedents). A text goal that a PROVED section of the session already states is REFUSED, naming the section: a fresh section stating what a proved sibling states closes on that sibling at its first step and proves nothing of its own — a clean re-proof of a proved statement goes through `restore` to a checkpoint before that section and proves in place. `goal.allow_duplicate:true` admits the duplicate anyway. |
| `define` | The definition move — the ONE door a fresh constant name may enter. One payload per genre: `recursive:` (direct, recursive, well-founded, a lift on classes), `data:`, `spec:`, `typedef:`, `quotient:`, `inductive:`. **Entry below: `define`.** |
| `inspect` | Show open goals + structural facts about the focused goal (applicable parameterless moves, definable consts, induction vars, case-split positions). **`goals` is the named goal alone when `goal_id` is given** — its `hypotheses` are the indices a `by_hyps` or `instantiate` at that goal takes — **and every open goal when `goal_id` is empty**; `num_open` counts the session's open goals either way. No score, no priority — facts only. **Applicability contract:** for parameterless moves, `def_expand`, `induction`, and `subst`, each fact has been verified by running the tactic on a clone — `apply` will succeed (modulo state changes between `inspect` and `apply`). For the four parameterized facts (`witness`, `instantiate`, `trans`, `case_split`), only the shape precondition is verified; full applicability with the agent-supplied parameter is checked at `apply` time. See "inspect.structural_facts contract" below. **A probe that reads a clock runs under a budget of its own** (`arith`, `ring_nf`, each `rw` direction): 1 s each, or the request's `budget_ms`, never past the request's deadline. One it cuts off is a fact carrying `unverified`, the reason, in the place the verified fact would have, and every other fact stands: an `unverified` fact is neither verified nor ruled out, and is never left out (§"inspect.structural_facts contract"). **A goal id is not an identity of the proposition.** It is `s<section>_g<prefix>`, the prefix cut from the α-key of the goal as it STANDS, not of its normal form: two spellings of one proposition — an equation the other way round, conjuncts in another order — carry different ids, and a differing id never says two goals differ. Whether two texts state one proposition is the KEY's to say (`retrieve`'s `match:"exact"`, a member's `Key`). |
| `retrieve` | Look up lemma candidates in the CORPUS, grouped by strategy. **Entry below: `retrieve`.** |
| `probe` | Non-destructively run a tactic on a goal. Returns `success` (with subgoals + `effect` ∈ `close` / `simplify` / `branch` and `auto_matched` listing leaves that auto-match would silently close — a proved sibling section's statement, or a cited entry's own reproduction child), `fail` (strong negative for structural / lemma tactics), or `unknown` (with `reason`: `timeout`, `unsupported_tactic`, `candidate_too_large`, `index_not_ready`, `panic_recovered`, `budget_exhausted`). A `by` or `by_induction` the budget cut off is `unknown(timeout)`, one that failed inside it `fail` (§`by`, "The deadline"); the cut-off names the probe budget AND the session refuter budget an apply would run under, so a close cut off at the probe budget is not read as a failed close. A `by`/`by_induction` probe that CLOSES reports `by_closer` (the routes, as the apply response names them — so `probe` no longer answers `{success, close}` with no closer) and `records` (the rows the recorder would write for the close — `Records 1 key (prop_…), 1 plan` or `Records nothing`, the same text the apply `by_records` diagnostic carries), so three spellings' key cost are read without an apply and a restore each; one whose close fired the divergence whistle also reports `by_whistle`, the text of the apply's diagnostic of that name (§`by`) — a spelling the recorder refuses, read before any Go is written. `effect` and `subgoals` are computed AFTER the predicted auto-match — so probe and apply agree on leaf count. Default budget 1 s (`budget_ms` sets another); honors the request context deadline. A structural step answers in milliseconds whatever the budget; a search that finds nothing waits it out. An `arith`, a `ring_nf` or an `rw` that does not end inside the budget is cut off inside its run and answers `unknown(timeout)`, with a diagnostic `<tactic> was cut off …`; so does a `set_tac` or an `auto` whose budget ends while the key of a refute is normalized (`… was cut off inside the pre-CNF normalization of the sequent, …`: the leaf is too wide for the budget). It is never `fail`, which says the tactic does not apply (§"Engine faults", "A run its budget cuts off"). `unknown(panic_recovered)` comes with `engine_fault` and locks the session (§"Engine faults"). |
| `apply` | Apply one tactic to a goal → returns new state or diagnostics. **Read the DISPOSITION, not the success flag**: `effect` ∈ `close` / `simplify` / `noop` / `branch` (same enum and classifier as `probe`, computed AFTER auto-match) says what the apply did to the focused goal, and `produced:[{goal_id, changes:{hyps_added, hyps_dropped, conclusion_changed}}]` carries the per-subgoal structural diff against the input goal. The forks that `success: true` alone cannot distinguish are exactly these fields: a lemma consumed as a goal REWRITE reads `conclusion_changed: true, hyps_added: 0`; the same lemma INSTALLED as a wide-∀ hypothesis reads `hyps_added: 1, conclusion_changed: false` with the goal untouched (the start of a premise pile — decided, for an ⇔ law, by whether the ∀-prefix was stripped first); a branch a `trans` created and auto-match closed is visible as `effect: "simplify"` + an `auto_matched` entry rather than a branch that never existed; a cite that discharged a second obligation shows `effect: "close"` with two `auto_matched` entries. Transcribing a session by hand from tactic-call history loses these; `emit-section` never does. For `lemma` / `lean_rw`, a cite serves the entry's own statement (see "apply lemma — the served form"). `goal_id` is REQUIRED, with one open goal as with many — an apply without it is refused by name (`inspect` reports the focused goal's id as `focused_goal_id`). A tactic that broke the engine answers `success: false` with `engine_fault` and an `engine_fault` diagnostic in place of `tactic_failure`, and locks the session (§"Engine faults"). A run its `budget_ms` or its client's hang-up ended answers `success: false` with a `tactic_failure` reading `… was cut off …` and no repair hint: nothing was decided and nothing is committed (§"Engine faults", "A run its budget cuts off"). |
| `batch-apply` | Try multiple tactics: `first_success` (stop on first) or `compare_all` (preview all). A tactic that met an engine fault ends the batch: its result carries `engine_fault`, each later tactic's result says it was not run (§"Engine faults"). |
| `checkpoint` | Save proof state snapshot (named). The engine also auto-creates one named `auto_<n>` after every successful `apply` at the RPC boundary, and `auto_0` BEFORE the first apply — so a first move taken the wrong way (an induction on the wrong variable) is one `restore` away, not a second session. `auto_<n>` is always "the state after apply n, with whatever `add-goal` added before apply n+1": an apply that follows an `add-goal` refreshes the newest snapshot under its own name before committing, so restoring to it keeps the added section. LRU-capped (default 500 per session, configurable via `WithAutoCheckpoint(cap)` / `WithAutoCheckpointOff()`). Manual (non-`auto_` prefix) checkpoints are exempt from LRU eviction. |
| `list-checkpoints` | List the session's checkpoints, oldest first: `[{id, name, created_at, num_open_leaves, num_sections}, …]`. The `id` is what `restore` takes. |
| `restore` | Revert to a saved checkpoint. Works uniformly on manual and auto entries. The field is `checkpoint_id` and its value is the checkpoint's **UUID**, never the `name` — passing the name answers `checkpoint not found`, and passing the wrong field name answers the same with an EMPTY name interpolated, which reads as eviction rather than as a spelling. Read the id off `list-checkpoints`. |
| `commit-plan` | Commit a deferred plan from `compare_all` mode |

The split into `inspect` / `retrieve` / `probe` follows the
"engine supplies bricks, not architecture" principle — each is
single-purpose and composable, the agent does the strategy.

#### `browse`

**The corpus to read in a browser** (`library/visualize`, `Site`). `xugo
browse [--port N] [--timeout D] [--root DIR]` reads the corpus, prints the
address as one line of JSON — `{"status":"listening","url":"http://127.0.0.1:8717/",
"families":…,"members":…}` — and serves on this machine alone until it is
interrupted, or, with `--timeout`, until no page has been asked for that
long. `xugo browse --write DIR [--root DIR]` serves nothing: it writes the
same site into DIR, an empty directory or a new one, and prints
`{"status":"written","dir":…,"files":…,"bytes":…,"families":…,"members":…}`.
It is a command, not an RPC, and drives no engine.

The site is two pages and the files they paint, and a page holds no
graph: it asks for its data.

- `/` (`index.html`) is the family graph (`query graph families`). A
  family clicked is locked and read in the sidebar: what its README
  opens with, the families nearest it either way, and its definitions,
  theorems and cards by name, each a link. The page opens at a font size
  of 6 px, whatever the screen. The address names the locked family and
  a font size other than 6 (`?family=<name>&size=10`).
- `proof.html?m=<member>` is the member's graph (`query graph proof`),
  the member named by its id, `<family>.<Name>`. The sidebar gives the
  node read — its statement, its gloss, what it stands on and what
  stands on it, each name a link to that member's page — and a node
  clicked twice opens its page. A definition's page draws what it is
  built from and who uses it, and its sidebar lists both. The address
  names the grain and the font size (`&grain=deep&size=14`), and a link
  carries both along; the grains are offered where they draw different
  graphs.
- On either page a click on the drawing's blank, a drag aside, clears
  the lock and the search, as the Clear focus button does.
- `data/families.json` is the family graph's layout.
  `data/family/<family>.json` is what the site says of a family and of
  each of its units, once: the family's gloss and its README's
  introduction, and per unit its `status`, the `theorems` it stands on
  and the `cards` among them, a card's `plan` — what it cites, as counts
  of `results`, `postulates` and `definitions` — its `gloss`, and its
  `members`, each with its `kind`, its `status` and its statement.
  `data/proof/<family>.<Name>.json` is a unit's page: the layout of its
  graph alone — the `units` drawn, and per grain the `columns`, the
  `nodes` (a unit by its place among `units`, its column, its height)
  and the `edges` (their ends by their places among the nodes) — and
  nothing a family's file says.
- The search field of either page finds, among the members of every
  kind, those whose name, family or statement holds every word typed,
  the nearest name first, and lists the first 40. It reads the families'
  files, at the first search.

Serving, a page is drawn when it is asked for, and a member's registered
name or own key names its page too. A site written holds a page for every
member — a door call's parts share the call's — and its links are relative,
so it reads the same under any address it is published at. Either way
the pages are of the corpus the binary linked, so a rebuilt binary serves
or writes the corpus as it then is.

#### `session-create {"resume":"<id>"}`

**Resume a persisted session under its own id** (engine/lineage.go). Every
session records its LINEAGE — the family binding, `define`s, `add-goal`s,
committed `apply`s (batch-apply / commit-plan winners included),
`checkpoint`s and `restore`s, in order, in the form the engine received them
— and persists it as it happens under
`<data-dir>/sessions/<id>/lineage.json`, plus each proved section's record
(`section_<k>.pb`, its DetailedProofProto — the bytes `emit-section` renders
from). Resume rebuilds the session by re-issuing the transcript: defines
RE-MINT (a process that already holds the name fails at that event —
constant identity is process-global and there is no "same definition, reuse"
rule), goals re-add from the recorded statement, applies re-run under a
CACHE-ONLY context (a CNF refute the store does not hold is a divergence,
never a live search) and WITHOUT the `budget_ms` they recorded (it bounded
the apply's search; on a replay a deadline would only make a slower run a
divergence, and with none the unifier runs in its deterministic mode, as the
chapter Go's replay does), checkpoints/restores replay with ids mapped.
A restore after resuming records a recorded checkpoint's transcript identity,
so the session can resume again after that restore. It
stops at the FIRST event that no longer applies and leaves the session live
at the state before it:
`{"session":{id,family,imports}, "events":N, "replayed":M, "diverged"?:{seq,kind,error}, "sections":[{section,statement,proved,record_matches?}]}`
— `record_matches` compares a re-proved section to its record, so a proof
that re-closed by a different route is visible; on divergence the full
transcript is set aside as `lineage.diverged-<time>.json` and the live
lineage is truncated to what replayed. An unfinished session resumes exactly
as a finished one (its open section's transcript replays to the same open
leaf).

**The replay outlives the request.** A client that hangs up mid-resume
(`curl --max-time`) loses the response, not the session: the replay runs to
its end, and a hang-up is never a divergence. A resume of an id whose replay
is still running waits for that replay and returns its result — the retry
after a hang-up; a second replay would re-mint the session's defines into a
serve that holds them. A waiter that hangs up in turn is told the replay is
still running, and the replay goes on. Until the replay ends the session
takes no other call: `inspect`, `apply`, `add-goal`, `session-lineage` and
the rest are refused with `session <id> is being resumed: …`, so no move lands
between two replayed events and no read sees a state halfway through —
resume again to wait for it.

Refused: an id live in this serve (it is usable as it stands — a session
whose resume finished after its client left is one), and a string that is
not a session id — the id names the session's directory under the store, so
resume takes the UUID `session-create` returned, in lowercase, and nothing
else. This is what survives a rebuild + restart — the serve's session map
does not.

#### Engine faults

**A panic that marks a defect of the engine is not a tactic that did not
apply** (engine/fault.go). The engine writes it down itself, marks the
response, and stops the session that met it, so the defect is handled at
its source whether or not the response is read.

What counts. A panic that leaves a command is a fault whatever its value.
Inside a tactic whose failures are panics (`by`, `by_induction`, the kits)
a fault is a failed assertion, an error of the Go runtime (a nil
dereference, an index out of range, a failed type assertion) or a panic on
a goroutine a search or a fan-out started; a search whose goroutine
panicked answers nothing, and the fault is raised on the request that asked
for the search.

The response:

- `apply` → `{"success": false, "engine_fault": {"id", "site", "panic", "record"}, "diagnostics": [{"type": "engine_fault", "message", "goal_id"}]}`.
  The diagnostic carries no repair hint.
- `probe` → `{"outcome": "unknown", "reason": "panic_recovered", "engine_fault": {…}, "diagnostic"}`,
  for a `by` as for any tactic.
- `batch-apply` → the faulting tactic's result is `{"success": false, "engine_fault": {…}, "diagnostics"}` and the batch ends there.
- any other command → HTTP 500 `{"error": "panic: …", "engine_fault": {…}}`.

`engine_fault.record` is the record's file, `<data-dir>/faults/<id>.json`
(absent when the serve has no `--data-dir`):
`{id, at, binary:{revision, dirty, registry_fingerprint}, command, rpc_body, session, family, imports, lineage_seq, goal:{goal_id, section, statement, closed, blob}, tactic, budget_ms, panic, site, goroutine, stack, raised_at?, refuted?:{statement, blob}, late?, in_flight?, overrun?, ack?:{at, note}}`.
`rpc_body` is the request as `/rpc` received it, to be sent again as it is.
`goal.closed` is the leaf's closed reading as `add-goal` text and
`goal.blob` its pooled prop (`ext.UnmarshalPropBlob` rebuilds the sequent
in a test); `tactic` is the tactic in the lineage's form; `lineage_seq` is
how many events the session's lineage held when the request arrived, the
state a resume of a copy of the session reaches. `goroutine` is `request`
or `worker`; for a worker `stack` is that goroutine's and `raised_at` the
request's. `refuted` is the sequent a faulting refutation ran on. `late`
marks a fault a search met after its request had answered: no response
carries it, and the record and the lock are its only signs.

**The session is locked.** From the fault on it answers `inspect`,
`session-lineage`, `list-checkpoints`, `dump-section`, `emit-section` and
`retrieve`, and refuses every move (`apply`, `probe`, `batch-apply`,
`commit-plan`, `add-goal`, `define`, `defer`, `checkpoint`, `restore`) with
an error naming the fault and its record. The fault is an event of the
lineage (`kind: "fault"`), so a resumed session is locked the same way. An
agent that meets one stops and reports `ENGINE-FAULT` with the id; a route
around the faulting step is not a fix.

**`xugo --data-dir DIR faults`** reads the store, with no serve:

```
xugo --data-dir DIR faults [--all]        # {"open": N, "acknowledged": M, "faults": [{id, at, command, session, goal_id, tactic, site, panic, goroutine, late, in_flight:[{command, session, goal_id, tactic}], overrun_ms, record, ack}]}
xugo --data-dir DIR faults show ID        # one record, whole
xugo --data-dir DIR faults ack ID --note "what was done about it"
```

The listing is the open faults, newest first (`--all` adds the
acknowledged ones), and exits 1 while there is one, 0 when there is none.
`ack` writes the acknowledgment into the record; a session the fault had
locked takes moves again from its next request. With no `--data-dir` there
is no record to acknowledge and the lock stands for the session's life.

**A serve whose process ends** — a runtime fatal error, a kill — runs no
recover. While it runs it keeps, in the same store, the runtime's crash
report (`serve-<pid>.crash`) and each request it has not answered
(`serve-<pid>-<n>.inflight`, one file a request); the next serve to start
on the data dir, and `faults`, turn what a process that is gone left there
into a record with `command: "serve"`, `goroutine: "process"`, the report
as `stack`, and
`in_flight: [{at, command, session, lineage_seq, goal_id, rpc_body, tactic, budget_ms}]`.
A request is in flight whatever its command. One that runs a tactic is on
disk from the start of the run, with `tactic` and `budget_ms` while the
run lasts; any other (`inspect`, `add-goal`, `session-create`,
`emit-section`, `retrieve`) is on disk once it has run 2 s, named by its
command, the session and goal its body names, and the session's
`lineage_seq`. So a serve stopped under a command that never answered
leaves the request to send again, and `faults` lists it.

**A run its budget cuts off** (engine/overrun.go). The deadline of a
request — `probe`'s and `inspect`'s budget, `apply`'s `budget_ms`, a
client that hangs up — is read inside the four runs that can outlast any
budget: an arith decision, before each leaf of the decider, a closer's
firing and the one an apply rung tries on an antecedent alike; `ring_nf`,
before each subterm it normalizes; `rw`, before each pass of its fixpoint;
and the normalization that keys a refute, before each of its stages,
hypotheses, rewrites, passes and sorts, at each node of its deep prenex
walk, and before each step that distributes a binder of a quantifier
block over a clause (one rewrite or one sort of it is otherwise the unit
a cut waits for: the longest measured, the sort of a 316-clause
disjunction, is 0.6 to 0.8 s). A run cut off there unwinds with nothing decided and nothing kept,
and answers that it was cut off: `probe` `unknown(timeout)`, `apply` a
`tactic_failure` reading `<tactic> was cut off …`, a `by` its own cut-off
(§`by`, "The deadline"), `inspect` the fact marked `unverified`. A
cut-off is no fault, locks nothing and is not recorded. A replay carries
no deadline and is never cut off.

The key of a refute is the normal form of the whole leaf, every
hypothesis moved into one disjunction (`PreCNFCache.NormalizeUntil` in
ext/prop): a certificate is stored under it, and served under it to
every spelling of the leaf that has the form. A certificate is first
looked for without it: the store's exact-key table names, by the
refute prop's own key as the CNF conversion builds it, the certificate
that was recorded for that very refute prop, and a leaf found there is
closed with nothing normalized. The key is computed for a leaf the
table does not name — a new leaf, which every refute's is until it is
stored, the refuter's in a `by`, the set driver's in a `by` with
`settac` and in `set_tac`, and `auto`'s, and a leaf whose certificate
another spelling recorded. It is seconds on a wide leaf
and grows faster than the square of the leaf's hypotheses: measured on
one shape, 1.6 s at 166 hypotheses and 7.9 s at 316, and in a serve 11 s
on a set driver's residual of 186 hypotheses, 7 s of them in the
canonical form of its quantifier block. A run cut off there
reads `… was cut off inside the pre-CNF normalization of the sequent, …`:
the leaf is too wide for the budget, and the search had not begun. Name
fewer premises, or set a budget longer than the normalization; a
normalization that ended is kept for the life of the serve, and the next
run on that leaf starts at the search.

**An overrun is recorded.** A run that ends more than 5 s past its
deadline, cut off or answered, held a unit of work that read no clock for
that long: a defect of the engine, whatever the run was looking for. The
engine writes it to the fault store as a record with `overrun: {what,
budget_ms, late_ms, cut_off}`, the request, the goal, and the stack of the
cut that ended it; `faults` lists it (`overrun_ms`) until it is
acknowledged. It locks no session and marks no response: the run did
answer.

#### `defer`

**An open leaf becomes a CARD — a member of the session's family stated
without a proof — and the leaf closes by citing it** (engine/defer.go).
`{"session_id","goal_id","name","note","deps"?:["<family>.<Name>",…]}` →
`{status, stated_by?, open_elsewhere?, card:{key,name,entry,note,deps?,statement,statement_typed,section}, section:{section,statement,proved,cards:[…]}, state}`.
The leaf's conclusion, ∀-closed over its free variables, is the card; its
normalized key is its identity (the same lemma deferred twice is one card,
under its first name); `entry` is its registered name `<family>.<name>` —
the spelling every later cite uses (`by {with_lemmas:[{key:"<entry>"}]}`,
`lemma {key}`). The session serves the card as the axiom `⊢ <statement>`,
the leaf closes by the `lemma` move naming it (recorded like any cite,
re-run on resume), and `emit-section` renders the card as a `family.Add`
entry built by `family.Card(<statement>, <note>)` — the statement in parts
where it has a premise, as every member's — BESIDE the member, whose
proof cites it — land both.

`deps` are the card's `Deps`: the members its proof will cite, the
narrative a hand-laid card carries — it orders the fill and nothing
replays it. Omitted, the card stands on nothing, which says its proof
cites nothing. Each is a registered name as a `lemma` cite spells it, a
sibling's qualified too: a registry entry, proved or a card, or a card
this session minted, by its `entry`. The rendered entry lists them as
`Deps: []registry.EntryLike{…}` between `Key` and `Build` — a sibling or
a card of the session by its bare var, another family's entry qualified,
its package imported — and a card of the session that a rendered card
names is rendered beside it, cited or not. The same lemma deferred twice
is one card standing on what either defer named. The lineage records the
deps, and resume re-issues them.

Replay serves a landed card as its axiom (the harness's trust frontier, made
permanent for cards) until a proof lands in place of `family.Card`: the
entry keeps its name and key, nothing downstream changes, and an entry
in the family's `cards.go` moves to the proof file of its subject
(the constitution's §"Families"). `status: "proved"`
— a proved entry already states the card, nothing was minted, cite the name
in `stated_by`; `"card"` — a landed card states it, cite that one. Refused,
the fix named: a session bound to no family (`session-create {family}`); a
`name` that is not an exported Go identifier; an empty `note` (the brief the
card's prover reads: why it is a member, what its proof must establish); a
leaf mentioning section-local variables (assert the ∀-closed statement
first, then defer its claim leaf — the card may not name a Skolem); a card
that is the section's own conclusion (the leaf IS the theorem); a name
minted in this session for another statement; a dep that is empty, that
names no registered entry and no card of the session (a sibling written
bare is told its registered name), that names an entry the family's
package cannot name in Go (as a cite of it is refused), that is the card
itself, or that stands on the card through the session's cards' deps.

A leaf carrying hypotheses defers too — the card is its conclusion closed,
the hypotheses are not in it — so read the card cold before deferring: a
false card is an axiom until someone fails to prove it.

#### `cards`

**The cards the session store knows of — members stated without a proof,
served as axioms until their proofs land — with the lineages that minted
or are proving each** (engine/cards.go; also
`xugo --data-dir D cards [--lineage ID] [--key KEY]`, no proof engine or
serve needed). A lineage knows a card two ways: it minted the card with
`defer` (a parent), or its target states the card (an attacker). The
corpus's cards — who stands on each, the order to fill them in, a family's
alone — are `query cards`; this view reads the registry only to tell a
landed card from one minted and emitted nowhere yet. A landed card's
display and typed texts are generated by `go generate ./library/carddata`
and compiled into the binary; `TestCardDataCurrent` checks them against
the current statements and spelling rules. A card with no matching
generated row is read on demand. The session store is read on each call.
`{"lineage"?,"key"?}` →
`{cards:[{key,name,entry,family,note,deps?,statement,statement_typed,landed,parents:[{lineage,section,statement}],attacked_by:[{lineage,section}]}], problems?}`,
by registered name.
`deps`: what the card says it stands on, by registered name — a landed
card's `Deps`, or every name the defers that minted it gave.
`statement_typed`: the card's parse-faithful spelling, paste-ready for
`add-goal {text}` (absent when the print does not round-trip — restate by
hand from `statement`); `abbreviations`, where the card declares any,
the names its `statement` spells as `«Name»` — a landed card is attacked
as `add-goal {entry}`, which states it with them. `landed`: a registry
entry; otherwise `parents` are the lineage sections that minted it. `attacked_by`: lineages whose target
states the card — do not dispatch it twice.

A card a proved entry states is no card and is not listed. Filling a
card is a `/prove` session whose target is the card's statement, landed by
replacing `family.Card(…)` with `family.Theorem(<the same statement>, body)`
in the card's entry, an entry in the family's `cards.go` moving to the proof
file of its subject; a restated statement re-keys like any restatement (the
registered-name gate passes it, the citers replay one hop). `query member`
reports a member's own `card` flag and its `cards` frontier — every card it
stands on through its dependencies.

#### `emit-section`

**The session's one exit: a proved section rendered as a member of a
family.**
`{"cmd":"emit-section","session_id":S,"section":<k>,"include_prior":[…],"family":"<family path>","func_name":"Build_<Name>"}`
→
`{section_id, func_name, sections_included, go, capabilities, dep_names, unfold_names, cnf_cache}`.
`include_prior` selects the other PROVED sections rendered with the
target: omitted, the sections the target cites, directly or through
another section, opened before the target or after it; `[]`, none; a
list, exactly those, each one the target's cites reach — a section
nothing cites would render as a local nothing reads, and is refused.
A definition section is a member of its own: a theorem that uses a
session definition cites the definition's family entry, and a list that
names a definition beside other sections is refused. The texts are
written for the family the member lands in: its instance bindings decide
which structure arguments a text leaves out, and a text is kept only
where it reads back under its numeric domain. A family the server has
not registered declares neither.
The member orders them itself: each after the sections it cites, ties in
section order, the target last (`sections_included` gives the order). A
section cites only the sections before it, never one stating its own
statement — its cite of that statement is the theorem it restates —
and sections that cite one another round a cycle are refused. `family`
omitted is the family the session is bound to.

**What it renders.** One section is a `family.Theorem` entry, with no `Deps`
(what the proof reads and opens is recorded when the landing records the
member; `dep_names` and `unfold_names` say what that record will hold); a
`def_expand` is `Unfold` of the definition's entry — the landed entry that
defines the constant, or, for a constant the session defined, the entry
its `define` section lands as, which is landed first: a constant with
neither renders as its quoted name, which `Unfold` does not take; a
`define` section is its definition door call; several sections are
`family.Sections`, each earlier one a `ctx.Lemma` local the later ones cite,
the target last, the member's abbreviation table every included
section's (a session reads each section's text under the tables of all
its sections, one name one meaning across them — `add-goal` refuses a
second text — so a later section spells an earlier one's names). The strips a section's proof opens with — `strip_quant`,
`strip_imp`, in any order — are the closure's parameters, as the chapter
binds them (§"The section boundary binds"): a ∀-binder a typed term
parameter where its type has a phantom in the family's scope (`V
*Expr[ModuleOps[A, B]]`, `s *Arrow[Nat, A]`, `K *Expr[Set[A]]`) and `Term`
otherwise, a ⇒-antecedent a `Fact` — the typed structure fact where it
applies a structure with a phantom at carriers the `on` vocabulary names,
`module.ModuleFact[on.R, on.M]` — and a bundle binder ONE structure-fact
parameter named after the bundle, `φ
ring_homomorphism.RingHomomorphismFact[on.R, on.S]` for
`∀φ:ring_homomorphism(A, B).`, `Fact` where its carriers have no letter.
The body starts after the lifted strips; a premise or a reading at a
bound antecedent is its parameter (`Law.Read(φ)`, `By(h, …)`), a Go
expression over a bound binder's Skolem is the parameter, no `ctx.Var`
registers one, and the claim of a Have or an Obtain is the statement
string the block's claim door reads, each bound binder spelled under its
own name (`"p < p + (q + 1)"`, the door's alias of `p₀`); an
`AssertStep(ctx.MakePropText(…))` branch and a
`ResidentHyp(ctx.MakePropText(…))` — a hypothesis no Go value names,
located by content at the leaf — are parsed at the Script's door, which
has no alias: their texts spell the minted names, in the chapter's
surface form (the set-builder sugar, the member's abbreviations folded,
the ties the parse needs). A hypothesis whose surface print does not
read back at that door keeps the name-faithful print a payload takes;
one with no text that reads back fails the emit naming it. A Have's fact
that a later branch rewrites in place while the proof after the branch
still reads it is bound again at the branch's root — `fact4 := c.Hyp(…)`
opening a `Derive` block, one line for each such fact — so the rewrite
moves the branch's handle and the Have's stays where it was bound. A constant
the family's scope serves gets no `ctx.Const` line and no scope override
at any instance: the Script reads it at each occurrence's own. The term
a `case_split` is on is the text the Argument reads, unwrapped
(`ByCaseStep(a.TermAs[Bool]("s < k").Core(), …)`). A strip the lift cannot read
as the boundary binds it — a partial strip, a strip after another step, a
binder whose name the closure cannot take (`ctx`, `env`, a constant's Go
name) — stays a step of the body; a section whose proof opens with such
a strip keeps the session's statement as its text, the telescope the
strip runs against. Every section lifts, a `ctx.Lemma` as the target
does. A Skolem two sections share is the parameter of each closure whose
strips mint it and a `ctx.Var` of the script in a section that meets it
elsewhere — one that does not lift (both strip `∀s t:set(A)`), or one
whose strip further down mints the same name (a lemma's `∀x` and the `∀x`
a branch of the theorem strips) — so a section's signature does not
depend on what another section mentions. A structure instance — one section stating
`<predicate>(components…)` for a structure a chapter defined with
`DefineStructure`, under a ∀-prefix or none, whose first step unfolds the
predicate (after the strip of the prefix) and whose conjunction is then only
split down to the definition's conjuncts — is
`family.Instance(<Structure>, "<statement>", Case, …)`, one Case per
conjunct in the definition's order; the strip, the unfold and the splits are
the door's own and are not rendered. A law of a structure — a statement
`∀<components>. <predicate>(<components>) ⇒ <body>` whose proof strips the
components and the hypothesis first, in a family that states a member
through the structure's door already (a law, an axiom, a card at
`S.Statement`) — is `<Structure>.Law("<body>", func(a *Argument, h
<fact>, …) {…})`: the door binds both, the hypothesis the structure's typed
fact where it has one (`h comm_ring.CommRingFact[on.R]`) and `Fact`
otherwise, the body's own leading strips the further parameters, and a
premise that is the hypothesis, resident or read under, is `h`
(`Law.Read(h)`); a body that is one action naming no hypothesis and
binding nothing more is that action. A proof spelling abbreviations of the
member's own declares them on a body written as `Statement{…, Abbrev}`.
The body is what follows the door's
opening in the headline — the headline in the standard form (below),
opening as the door's statement does: the components' binders and the
predicate at them (`∀R:ring_ops(A). ∀x:A. comm_ring_on(R) ∧ … ⇒ …`), or
the bundle binder (`∀R:comm_ring_on(A). <body>`). A card the proof deferred that
states a law of such a structure is `family.Card(<Structure>.Statement(<body>),
"<note>")`, the body in parts where it has a premise. In a family stating its bundles in the text — no entry
through the door — the same statement is the `family.Theorem` whose
bundle binds as the one typed fact above. A statement whose root
unfolds one definition and whose unfolded goal one action closes is
`family.Theorem("<statement>", Opening(Unfold(<c's definition>), <close>))`. A
conditional instance, a law whose statement binds more before the
hypothesis, a member with lemma sections and a structure named by
`StructureOf` stay `family.Theorem`. The binding these doors and the
lift make records other strips than the session's strip-all, at the same
goals, the Skolems minted under the same names; the landing records the
member's own steps.

Scaled coefficients register their symbols and bind the Go variables their
rendered expressions use, including symbols occurring only in a coefficient.

A `by` preserves explicit type bindings through `AtTypes`, including an
identity binding: the explicit instance disables goal-side type adaptation.
A `by` renders as `By(…)` and a `simp_with` as `Simp(…)`, a law read at an
instance as `Law.Read(Instance)` in either — a law with a loose letter read
under a resident fact, which the session cites as the law beside the fact,
among them (`At(Law.Read(fact), w…)` when grounded, the components the
macro prefixes left off). A polymorphic rule the session adapted to the
goal's instances is the bare entry where Go's `Simp` adapts the entry to
the same rewrite (the residual it leaves is the recorded one), and an
instance Go would choose differently — one pinned on a goal that spells
more — keeps its spelling (`Inst[τ]()`, `ctx.AtTypes(…)`); a `let` as `LetTerm(…)`; a
`lemma` close as `Cite(<Entry>)` — the entry's variable, as a `By` premise
spells it; a name no landed entry carries renders quoted,
`Cite("fam.Name")`, which the verb refuses — the entry lands first. A `cite-node` of the root of an INCLUDED
section is a cite of that section's local, and the section's proof stands
once, as the local's body: `Cite(lemmaN)` on the spine where the cite verb
installs exactly what the recorded assert installed (`Cite(lemmaN, w…)` when
the next step grounds the installed fact), and otherwise the assert as
recorded with `Cite(lemmaN)` closing its claim branch; a section not
included keeps its inlined proof.

A WITNESS of a `by` premise (`At(fact, w…)`) or of a cite fused with its
grounding (`Cite(fact, w…)`, of an entry or of an earlier section) that is
no variable is the text a chapter writes, parsed by the Argument its steps
run under and typed by its phantom — `a.TermAs[Real]("(m - l) / &2")` —
where the type has a phantom in scope, and by its untyped door,
`a.Term("normal_distribution(&0, &1)")`, where none spells the type —
where the text reads back as the witness
in the member's scope, every bound binder spelled under its own name
(the Argument's alias of its Skolem); a witness with no text that reads
back is the Go term expression, and a variable is its Go local — except a bundle's
component, which the boundary fixes under its own name and no
parameter binds: that is the text of the name, `a.TermAs[RingOps[A]]("c")`.
A type instance of a landed entry is its typed wrapper's: for a
sole-letter statement `<Entry>.Inst[<T>]()` at every type a phantom spells,
a typedef's among them (`Inst[Real]()`, `Inst[Int]()`), and for a
statement of several letters `<Entry>.Inst(TypeBinder.BindA[<T>](),
TypeBinder.BindB[<U>]())`, each letter bound by name — an identity
instance the session pinned among them (`BindA[A]()`). An earlier section
of the member cited at a type instance is bound by its letters too,
`ctx.AtTypeVars(lemma1, TypeBinder.BindA[<T>]())`. A statement letter with
no `Bind` method, or a type no phantom in scope spells, keeps the
positional `ctx.AtTypes(…, τ…)`.

**A chapter's phantom is spelled only where the family has it**: the phantom
of a type minted below the chapters (`Real`, `Int`, `Ind`) is
`library/authoring`'s and every proof file has it, while the phantom of a
type a chapter mints (`Complex`, `List`, …) is spelled by the emitter only
where a signature of the family binds a variable of the type (the member's
own statement counted) — the family's generated wrapper file aliases it
there — so in a family that binds none the instance keeps
`ctx.AtTypes(ctx.Dep(X), MakeType("complex"))`
and the witness is read by `a.Term` — lines that compile there. In a Have
chain, a later `by`'s resident premise that is the hypothesis an earlier
Have of the same block stated is that Have's handle — `fact1`,
`At(fact1, w…)` when grounded — where the claim stays a hypothesis down to
that `by`; every other resident premise is `ResidentHyp(…)`. A recorded
`cond_rewrite` on a goal with no COND, whose residual a `basic` leaf closes
and which `Basic()` closes as it stands (checked when rendered), is that
`Basic()` alone. A session `by_induction` — the asserts of a principle's
obligations and the by that closes on them — renders as
`ByInduction(At(<principle>, pred…), extras…, Case("case_<i>: <obligation>", <its proof>)…)`,
the principle cited before its predicate where that predicate is the one the
goal reads (§`by_induction`),
the shape Go's verb records, and a Derive block's Haves stop where such an
induction starts — its tail is `Show(…, ByInduction(…))`; an assert run whose
tail is not that by stays a Derive block. An assert of an ∃ that the next step
opens (`strip_quant {hyp_index}` at the hypothesis it added) is one
`Obtain(…)` in the block, its witness the Skolem the declarations name and its
instance the Fact it returns, the facts after it Haves as before.

A datatype's derived principle is emitted through its Go handle,
`list.ListData.Induct`, and a type definition's theorem through its
door's field, `eudoxus_slope.NaddDef.Membership`; a record field's projection
equation by the name its field registers, `module_record.RingCarrierDef`,
which the family's generated file declares. Ordinary theorem entries
retain their named Go variables. A hypothesis a nested closure takes
(`Given(func(b *Argument, h_2 Fact)`) is named apart from the Law door's
`h` and the Have handles in scope.

**The headline and every asserted claim are printed in the chapter's surface
form** — the text `statement_typed` serves: a set-builder as
`{t | x:A, y:B | P}`, declared notations folded, an integer literal as `&n`
where its partner types it, a set binder as `set(τ)` and no `⟨A:τ⟩` tie a
constant's arguments already fix (dsl.SurfaceForm) — **and read back before
they are emitted**, at the door the emitted call parses them at: the
Script's, which resolves a constant the family's scope serves through
the inventory at the constant's own letters, so a `⟨A:τ⟩` tie whose
removal leaves a letter unpinned stays (the claim door refuses the pinless
text, `dsl.UnpinnedLetters`); a Have's claim under the goal's resident
facts too. A statement a landed entry states — the card a session fills —
is emitted under the entry's own text (`registry.ProofEntry.StatementText`:
`∀S:(num → set(I))` where the printer spells the arrow, a tie on the atom
the author tied), where it reads back; the entry's `statement_typed` is the
same text. **The headline is the statement in the standard form** every
member is written in — every binder in front, the premises one ∧-joined
antecedent, `∀xs. H₁ ∧ … ∧ Hₙ ⇒ C` — restated from the session's goal
where the goal curried its premises or bound again after one
(`∀x. H ⇒ ∀y. H′ ⇒ C` is emitted as `∀x y. H ∧ H′ ⇒ C`), a lemma
section's statement as the target's — the boundary binds the
standard form's telescope as the lifted strips bound the session's —
but for a section whose proof opens with a strip the lift does not bind
(above); a card the session deferred is restated the same way. A goal whose restating would
capture a name — a binder after a premise that spells the name — fails the
emit, naming both texts, and is restated in the session. The
headline must carry the statement's own key; a claim must read back as the
proposition itself, up to bound names, since a Have installs what its text
reads as. A text that does not read back fails the emit, naming the section
and the text, and nothing is emitted in its place: restate it in the session
— a hand-patched text is checked by nothing. Lemma and rewrite-rule payloads
and `ResidentHyp` statements keep the name-faithful print. `cnf_cache` is
the certificates a strict re-run of the recorded closes reads: non-empty
says a leaf reached the refuter and will cost a recorded key. It is never
installed — the family recorder writes the member's blob. For a law read
under a resident hypothesis, the re-run restores that automatically kept
hypothesis as part of the reading; it is not an extra authored premise
subject to the unused-premise audit. Errors: an
unproved section, an `include_prior` index that is the target, out of
range, unproved or repeated, a listed section the target's cites do not
reach, sections citing one another round a cycle, no family, a statement that normalizes to
⊤, a text that does not read back, a strict-walk MISS in the CNF collection
— the last one returned beside the rendered member (`go` and the other
fields with `error`), since the rendering reads no certificate.

#### `define` — Go: the definition doors

The definition move (the ONE door a fresh constant name may enter —
§"Statements and definitions — one elaborator"):
`{"session_id","recursive":{"name","type","equations":[…],"measure"?}}`
mints the constant at the RPC boundary and creates one PROVED definition
section whose statement is the characterizing theorem, body = the single
`define` composite ministep. Equations parse with the definiendum declared
at `type` and both strict switches ON — any other undeclared name errors
naming the repair, and a name already registered errors (EXCLUSIVE, never
shadows; constant identity is process-global, so the minted constant
resolves in every later statement text with no declaration — serve restart
is the experiment eraser).

Three `recursive:` shapes served: a single `c`-free equation over plain
variables `∀x̄. c(x̄) = body` (`⇔` at bool) is the DIRECT case (λ-mint); one
equation per constructor with direct recursive calls `c(argᵢ)` is the
RECURSIVE case (ε-mint) — and so is a SINGLE equation whose left side takes
a constructor pattern although nothing recurs, the projection of a
one-constructor datatype (`complex_re(complex(x, y)) = x`): a pattern is
read only by the compiler, so one equation goes to the direct shape exactly
when its arguments are variables and its body is `c`-free
(`proof.IsCompiledDefinitionEquation`, the one classifier the registry door,
this door and emit share) — the equation compiler instantiates the carrier's
registered recursion schema (`num_recursion` / `<T>_recursion` in the
library theorems), weakens ∃!→∃, and discharges the existence obligation
ENGINE-SIDE with a pure kernel derivation (deterministic, refuter-free;
compile runs BEFORE the mint, so a definition the schema cannot discharge
registers nothing).

Adding `"measure":"λn:num. n"` selects the WF shape: the measure is a term
over the RECURSION ARGUMENT alone, its λ-binder matched BY NAME against the
LHS argument it measures, and the equation must be ONE total COND-form
equation over all-variable arguments
(`∀m n:num. gcd2(m, n) = COND(n = 0, m, gcd2(n, nat_mod(m, n)))`). The WF
shape does NOT close engine-side: the composite surfaces the TERMINATION
obligation (per recursive call site: ∀-closed COND guards ⇒ measure
decrease, β-normalized) as the definition section's one OPEN child — the
response carries `obligation` (the statement, printed) +
`obligation_goal_id`, the author closes it with ordinary tactics (real
mathematics — the division theorem for gcd), and the definition completes on
the closing apply, reported in that apply's `StepResult.DefineCompleted`
(`schema:"wellfounded_recursion (measure)"`; the WF compiler is a pure
kernel derivation, refuter-free, against the
wellfounded_recursion/wellfounded_measure_less rows served from the
`well_founded` chapter).

The `data:` payload
(`{"session_id","data":{"name","params":["A",…],"constructors":[{"name","args":["A","btree(A)",…]},…]}}`)
is the DATATYPE door (the recspace pipeline): it mints the type
(`core.NewTypeDef` over the impredicative shape predicate, witness = the
first basal constructor's ε-filled encoding) plus one constructor constant
per spec — all EXCLUSIVE and process-global — and creates one PROVED section
per derived-theorem family: `<T>_induction` (the standard form, which the
induction tactic's analyzer reads), `<T>_recursion` (list_recursion's arrangement —
the equation compiler's schema for later `recursive:` defines over the
carrier), `<T>_injective`, `<T>_distinct` (each absent when the shape has
none), each body ONE `define_data` composite ministep re-deriving its
theorem from the minted metas + the recspace corpus rows
(recspace_recursion/recspace_node_injective/family_cons_definition/suc_not_zero/suc_injective/pair_injective/fst_of_pair/snd_of_pair)
— deterministic, refuter-free, close-or-fail. The induction and recursion
principles install into the env's library overlay under their conventional
names (so `induction` dispatches on the goal variable's TYPE and the
compiler resolves the schema, both with zero setup); the injectivity and
distinctness laws join the session SIMP SET. The shape served: a single
non-mutual datatype, each constructor argument either exactly `T(σ)` or an
external type (no nested/function-typed recursion), ≥1 constructor with no
recursive argument, params distinct ascending single letters, each used. →
adds
`{type, consts, derived, simp_installed_names, derived_sections:[{kind, principle, goal_id, section}]}`
to the result.

`emit-section` with `family` renders ANY of the datatype's sections as the
ONE `family.DefineData(registry.DataEntry{…})` call (registration re-mints
and re-registers the four entries — Induct/Recursion carry `ServesAs`, the
harness's principle-name binding); a later member's `induction` over the
type reads the Induct entry by that name, which its recording observes, and its
injectivity/distinctness simp fires cite the
`<family-base>.<ExportedType>Inj`/`…Distinct` entries.

The `spec:` payload
(`{"session_id","spec":{"consts":[{"name","type"},…],"spec":"<statement>"}}`)
is the SPECIFICATION door (a composite — transcript S): one or more
constants in DEFINITION ORDER pinned by CHOICE against a specification,
nothing equation-shaped required. The spec parses with each definiendum
declared as a typed VARIABLE (both strict switches on); the session door is
FRESH-only by ruling — a name already registered errors pointing at the
chapter door (`family.DefineSpec` serves the claim provenance). The move
mints the nested tag-free ε chain and opens the section's one child for the
author: the POINTWISE existence obligation
`∀points. ∃values. spec-at-values` (recomputed from the recorded goal by
AnalyzeSpecGoal — nothing else rides the wire to drift), returned in
`obligation`/`obligation_goal_id`; completion rides the closing apply's
`DefineCompleted` (`schema:"specification"`, `consts` = the group,
`simp_installed:0`).

`emit-section` renders a spec section as ONE
`family.DefineSpec(registry.SpecEntry{…})` — Spec/Consts as literals (the
Spec round-trip-verified at emit to serve BOTH provenances: clean replay =
FRESH re-mint, already-registered process = CLAIM), the recorded existence
proof as the ctx-hosted `ExistenceBody` closure, its cites body-first
dep-marked into `Deps`.

The `typedef:` payload
(`{"session_id","typedef":{"type","abs","rep","pred","witness"?}}`) is the
TYPE-DEFINITION door (the one kernel principle besides constant definition):
a type carved out of a representation type ρ by a closed predicate `pred` (a
λ over ρ in text, both strict switches on — `"λn:num. 0 < n"`), with
`abs : ρ → T` and `rep : T → ρ` its bijection. The inhabitation is the
author's mathematics, proved BEFORE the define as an ordinary goal —
`∃x:ρ. pred(x)`, or with `witness` (a closed point of ρ) the membership
`pred(w)` with a λ's redex reduced (`0 < 1`) — and the door finds that
proved section by its statement (no id on the wire; a resume finds it
again); a predicate the normalizer decides (`∃x. pred(x)` normalizes to ⊤ —
the pair shape, an equivalence-class shape) needs none and refuses a
witness.

The move mints the type and the pair (EXCLUSIVE, process-global; a type name
already in use is refused) and creates two PROVED sections, each ONE
`define_type` composite: Retraction `∀a:T. abs(rep(a)) = a` and Membership
`∀r:ρ. pred(r) ⇔ rep(abs(r)) = r`, the composite's one child (the
inhabitation; absent when trivial) closed by citing the proved section's
theorem. Nothing installs into the simp set (the chapter door registers the
two theorems as plain entries, and a session and an import must agree on
what a definition installs): a later member cites them (`cite-node` + `by`).

`emit-section` with `family` renders EITHER section as the ONE
`family.DefineType(registry.TypeEntry{Name, Type, Abs, Rep, Pred, Existence?, Witness?, Deps?})`
call, `Existence` naming the inhabitation's entry — the landed one when the
registry has it by key, else the session convention
`<ExportedType>Inhabited`, renamed at landing (emit the inhabitation section
as an ordinary member under that name).

The `quotient:` payload
(`{"session_id","quotient":{"type","mk","abs","rep","relation"}}`) is the
QUOTIENT door (Lean's `Quot`, Isabelle's `quotient_type`): the type carved
out of the equivalence classes of a relation `R : ρ → ρ → bool` the session
or a chapter already defined (a constant, possibly applied to its parameters
— never a bare λ), with `mk : ρ → T` its CLASS MAP — spelled `⁅x⁆` and by
the word `class`, the notation every quotient shares, the body's type
picking the quotient (a second quotient over one carrier keeps its class
map's name alone) — and `abs`/`rep` the typedef pair underneath, which
nothing cites. The one input is the author's mathematics, proved BEFORE the
define as an ordinary goal and found by statement: `equivalence(R)`, the
relations chapter's structure predicate (a chapter's theorem closes it in
one `lemma`; `def_expand` of
`equivalence`/`reflexive`/`symmetric`/`transitive` plus `auto` proves it de
novo).

The move mints the type and the three constants (EXCLUSIVE, process-global)
and creates SEVEN PROVED sections, each ONE `define_quotient` composite (tag
65; payload = the class map alone) with the equivalence as its one child,
closed by citing the proved section — pure kernel derivations over the
typedef axioms and the relations chapter's definitions:
`Surjectivity ∀q. ∃x. q = ⁅x⁆`, `Induct` (the standard form
`∀P q. (∀x:ρ. P(⁅x⁆)) ⇒ P(q)`, installed as `<T>_induction` so the `induction`
tactic dispatches on a class-typed goal variable — Lean's
`Quotient.inductionOn` — its one case the representative),
`Sound ∀x y. R(x, y) ⇒ ⁅x⁆ = ⁅y⁆` and `Exact` (its converse; installed as
`<T>_sound` / `<T>_exact`, which the lift compiler reads),
`Eq ∀x y. ⁅x⁆ = ⁅y⁆ ⇔ R(x, y)` — the one rule among the seven, installed
into the session SIMP SET (Lean's simp-marked `Quotient.eq`) — and
`ForallOnImage` / `ExistsOnImage` (`(∀q. P(q)) ⇔ (∀x. P(⁅x⁆))` and the ∃
twin). →
`{defined, shape:"quotient", type, consts:[mk, abs, rep], derived:[<T>_induction, <T>_sound, <T>_exact], simp_installed_names:["Eq"], derived_sections:[{kind:"Surjectivity"|"Induct"|"Sound"|"Exact"|"Eq"|"ForallOnImage"|"ExistsOnImage", principle, goal_id, section}]}`,
`characterizing`/`key`/`goal_id` the Eq section's.

`emit-section` with `family` renders ANY of the seven sections as the ONE
`family.DefineQuotient(registry.QuotientEntry{Name, Type, Mk, Abs, Rep, Relation, Equivalence?, Deps?})`
call, `Equivalence` naming the equivalence's entry — the landed one when the
registry has it by key, else the session convention
`<ExportedRelation>Equivalence`, renamed at landing (emit the equivalence
section as an ordinary member under that name).

A FUNCTION ON THE CLASSES is the `recursive:` payload with the class map as
a constructor pattern among its arguments — the LIFT shape (Lean's
`Quotient.lift`/`lift₂`, Isabelle's `lift_definition`): ONE equation
`∀a b:ρ. op(⁅a⁆, ⁅b⁆) = ⁅a + b⁆` (a class-valued operation, the value
written as a class), `∀a b:ρ. le(⁅a⁆, ⁅b⁆) ⇔ a ≤ b` (a relation on classes),
or `∀x:A. ∀p:ρ. mem(x, ⁅p⁆) ⇔ …` (an external argument beside a class — a
plain binder, held fixed); nothing recurs.

The move mints `op` as `εf. <the equation>` (the recursive shape's
payload) and opens the RESPECTFULNESS obligation as the section's one
child, in the shape the corpus states its well-definedness laws —
`∀a a' b b'. R(a, a') ∧ R(b, b') ⇒ R'(a + b, a' + b')`, each class binder
followed by its primed twin, `R'` the value's relation (`=`/`⇔` for an
external value) — returned in `obligation`/`obligation_goal_id` with
`shape:"lift"`, `schema:"quotient_lift"`; the author closes it with ordinary
tactics (a chapter's well-definedness law closes it in one `cite-node`/`by`)
and the definition completes on the closing apply
(`StepResult.DefineCompleted`, `schema:"quotient_lift"`, `simp_installed:1`
— the computation rule installs whole, so the bare `simp` computes at the
classes with zero setup; the lift compiler then derives the existence by
kernel rules from the proved respectfulness and the quotient's Sound/Exact).

`emit-section` renders a lift section as
`family.Define(registry.DefEntry{…, Respects: []Action{…}})`, the
obligation's steps as `Respects` — `family.Define` declares the quotient's
Sound and Exact entries as its deps itself. The standard proof of a law over
a quotient is then Lean's: `induction` each class-typed binder (the
representative is the one case), `simp` (the computation rules and Eq
rewrite the goal to representatives), `by` the law one layer down — see the
real tower's `nonneg_real` and `real_construction` chapters, every transported law of which
is those three moves.

The `inductive:` payload
(`{"session_id","inductive":{"name","type","params":["R"]?,"rules":["…",…]}}`)
is the INDUCTIVE-DEFINITION door (Isabelle's `inductive`): a relation minted
as the SMALLEST one closed under the stated rules, each rule
`∀v̄. H₁ ∧ … ∧ Hₖ ⇒ name(p̄, t̄)` (or unconditional) with the definiendum
applied at the declared parameters then its indices, every Hᵢ a side
condition free of the relation or a positive premise `∀ū. G ⇒ name(p̄, s̄)`
with G free of it — the first charter's fragment (bare premises: finite; a
premise under ∀: is_recspace's `∀n. Z(r(n))`; a guarded one: accessibility;
a parameter with two premises: transitive closure); mutual definitions and a
relation under ∃/∨/¬ are refused by name.

Three or four PROVED sections come back, each ONE `define_inductive`
composite (tag 63; payload = the constant, the parameter variables and the
rules as stated — the rules are the definition's identity and ride the
record like the WF measure): `<name>_rules` (the rule set verbatim),
`<name>_induction` (rule induction, the weak form:
`∀p̄ P x̄. rules[P] ∧ name(p̄, x̄) ⇒ P(x̄)`, the rules one hypothesis each) `<name>_cases`
(`∀p̄. ∀ā. name(p̄, ā) ⇔ D₁(ā) ∨ …`, one canonical disjunct per rule with a
variable index substituted rather than equated), and — when some rule has a
premise to strengthen — `<name>_induction_strong`, the same induction with
each recursive premise carrying `name(p̄, s̄)` ALONGSIDE `P(s̄)` (with no
premise to strengthen it IS the plain induction, so the door omits it rather
than register two entries under one key) — all pure kernel derivations,
refuter-free. Nothing installs (R4: the rules are not rewrite rules and
Cases would rewrite the relation into itself).

The closure form the constant is minted with is NOT a proof surface:
`def_expand`/`Unfold` on an inductively minted relation is refused by a
message naming the three theorems; cite the sections (`cite-node`) instead,
and emit renders the definition as ONE
`family.DefineInductive(registry.InductiveEntry{Name, Keys, Const, Type, Params?, Rules, Deps})`
whose registration re-mints and re-registers
`<Name>Rules`/`Induct`/`Cases`/`InductStrong` under the keys `Keys`
spells (a chapter's members cite those). →
`{defined, shape:"direct"|"recursive"|"lift"|"data"|"spec"|"typedef"|"quotient"|"inductive", schema?, characterizing, key, goal_id, section, simp_installed, scope:"process"}`
(plus
`{type, consts:[abs, rep], derived_sections:[{kind:"Retraction"|"Membership", goal_id, section}]}`
for the typedef shape, and
`{consts:[name], derived:[…_rules, …_induction, …_cases], derived_sections:[{kind:"rules"|"induction"|"cases", principle, goal_id, section}]}`
for the inductive shape, whose `characterizing`/`key`/`goal_id` are the
Rules section's) — plus `obligation`/`obligation_goal_id` for the
authored-obligation shapes (WF, spec) and `consts` for the spec group.

R4 — installation is part of definition, and WHAT installs is per shape:
direct/recursive install the characterizing theorem whole into the session's
SIMP SET (`simp_installed` counts its clauses) and the bare `simp` tactic
fires it with zero setup; the WF shape installs the two DERIVED guarded
readings — the substitution-discharged base equation plus the
Horn-conditional step reading (`simp_installed:2`; the characterizing COND
equation itself is deliberately NOT a rule — an unconditional unfold would
rewrite every occurrence on sight); the spec shape installs NOTHING
(`simp_installed:0` — a specification is not a directed rewrite; the author
cites the characterizing theorem, `cite-node` + `by`); the data shape
installs the injectivity/distinctness laws as listed above.

`emit-section` with `family` set renders the section 1:1 as
`family.Define(registry.DefEntry{…})` (one author-form equation string per
clause), whose registration re-mints at package init (the nat_divides
pattern) and whose Build re-derives through the same composite — the
door finding the recursion schema itself and `Deps` naming only the
family's own entries; a WF
section renders with `Measure` + `Termination` (the obligation child's steps
through the standard step renderer, the measure re-spelled with its binder
annotation and round-trip-verified at emit) + `Deps` (the entries serving
the WF rows plus the termination proof's cites).

A LATER member's `simp` fire against a define-installed equation emits as a
dep cite of the definition's conventional entry name
(`<family-base>.<ExportedConst>`, a dep the landing's recording observes —
the session-define leaf tier; the name is changed at landing exactly as with FuncName).

#### `retrieve`

Look up lemma candidates in the CORPUS, grouped by strategy. Request:
`{"cmd":"retrieve","session_id":S,"mode":"goal","goal_id":G}` (`goal` mode
reads an OPEN GOAL of the session by id — there is no goal-text field; add
the statement as a goal first), `{"mode":"consts","consts":[…]}`,
`{"mode":"name_pattern","name_pattern":"…"}`,
`{"mode":"related_to","related_to":"<entry or key>"}`; optional
`max_per_group`, `budget_ms`.

**The corpus group** (`matched_via:"corpus"`, engine/retrieve_corpus.go):
the proof registry read as a lemma index, every member reported by its
registered name —
`{entry, family, key (the entry's own), statement, match, witnesses, premises}`.

In `goal` mode it lists the members whose statement IS the goal
(`match:"exact"`, by key, over the goal's stronger variants; a variant the
normalizer closes to ⊤ is no hit) and the members that APPLY to it
(`match:"apply"`): the goal is opened first (leading ∀ freed, leading ⇒ made
hypotheses — the sequent your strips would reach) and each member's stated
form is read by the apply rung's own plan (`proof.StatedHead.Read` — the head
telescoped through binders, guards and antecedents, its conclusion matched
against the goal at every type instance the goal offers and at the instances
the corpus's structure facts offer for its antecedents — `comm_monoid.Comm`,
whose conclusion spells no constant but `=`, reads at `x * y = y * x` on ℝ
at the carrier `real_ring.MulMonoid` fixes — the remaining
binders pinned from the antecedents against the context and then against the
corpus's bare facts — the structure instances; a law stated at a structure
record spells its operations as the record's projections, which the goal at
an instance spells by their values, so its record is pinned first, from the
antecedent that takes it whole, and its conclusion read there in the instance
normal form — `comm_ring.MulLeftZero`, `∀R:comm_ring(A). ∀x:A. R.zero * x =
R.zero`, reads at `&0 * x = &0` on ℝ with `R` the record `real_ring.CommRing`
states, where `R.zero` is `&0` and `R.mul` is `real_mul`), so a member listed here is
one `by {with_lemmas:[{key:"<entry>"}, …]}` fires as a named premise up to
the kernel's spelling of the instance, once its premises are in hand;
`witnesses` are the binders that were pinned, `premises` the antecedents at
those witnesses, each `status:"resident"` (in the context), `"entry"`
(stated by the member named in the premise's `entry` — cite it alongside),
`"card"` (stated by a member that is a card, named in `entry` the same way —
cite it alongside, and the close stands on a card until its proof lands), or
`"open"` (yours to supply first).

Ranked exact first, then fewest unsupplied premises (open or card), then
name. A scan, not an index: the registry is read whole under the call's
budget, and a large goal truncates rather than hangs. `consts` lists the
members mentioning every named constant (fewest others first),
`name_pattern` the members whose registered name contains the pattern,
`related_to` takes an entry name or key and answers `corpus_deps` /
`corpus_dependents` (one hop, from the entries' dependencies). Per-strategy
ranking only — no global fusion across groups.

**The readings group** (`matched_via:"corpus_readings"`, after the corpus
group, in `goal` mode): what no member states. A law whose body states
another structure is a PROJECTION — `ring_homomorphism.AdditiveHomomorphism`
states a group homomorphism, `comm_ring.AddGroupOn` an abelian group on the
carrier, `field.Ring` a ring — and read at a fact of its structure it is an
instance of the other, so every law of the other is a value at it, and so
on through the structures a chain of projections reaches
(registry.Readables: each chain to its fixpoint, no structure visited
twice, one entry per derived statement, the shorter chain kept). Such a
value is cited where it is used and is no member (the constitution's
§Readings): "a ring homomorphism keeps zero" is `group_homomorphism.MapOne`
read at `AdditiveHomomorphism`. The kernel derives each reading's statement
once per process (proof.ReadLawAt, written back over the root structure's
components), in the background from the engine's construction; the group
matches those statements by the plan above, and a request that arrives
before the walk is done answers without waiting, the group truncated and
empty. A hit is `{entry, key, family, statement, match:"apply", witnesses, premises,
card, reading}`: the law by its registered name and own key, `statement`
what the reading states — the law's body at the components the chain pins,
under the root structure's hypothesis, in that chapter's spelling — the
first premise the structure fact the chain is read at, `card` when the law
or a projection in the chain is one, and `reading: {through, go, read_at}`:
the chain outermost first, the Go value
`group_homomorphism.MapOne.Read(ring_homomorphism.AdditiveHomomorphism.Read(ResidentHyp(ring_homomorphism(…))))`
(an instance entry by its name; a hypothesis as `ResidentHyp(<fact>)`, where
a chapter writes its Fact parameter), and the `read_at` the law's `by`
premise takes —
`{"key":"ring_homomorphism.AdditiveHomomorphism","read_at":{"hyp_index":0}}`
— given when the fact is a hypothesis of the goal as it stands or an
instance entry; a fact the goal holds only opened, or not at all, leaves it
out (strip to it, or supply it, then name it). Ranked by unsupplied
premises, then chain length, then name; capped and truncated like the
corpus group. The members' group never lists a reading, so a goal no
projection reaches answers as before.

### Checks (stateless)

| Command | Input | Output | Purpose |
|---------|-------|--------|---------|
| `check` | proposition text on stdin | `{result, diagnostics}` | Verify a derivation — is this proposition logically valid? |
| `check-derivation` | JSON `{"premises":[PropInput,...], "conclusion": PropInput}` | `{result, diagnostics}` | Multi-premise verification |
| `check-consistency` | JSON `{"statements":[PropInput,...]}` | `{result, conflict_subset}` | Check if statements are mutually consistent |
| `parse-prop` (bare) | JSON `{"text":"..."}` | `{ok, normalized_input, statement_text, warnings}` | Preview / lint a text-DSL proposition (authoring aid, no goal scope) |
| `parse-prop` (scoped) | JSON `{"text":"...", "session_id":"...", "goal_id":"..."}` | same as bare | Preview `assert.claim_text` / `lemma.lemma_text` against the session's focused (or named) goal — the parser sees the goal's free-var types, goal-local constants, and the corpus's registered constants exactly as `apply` will. `goal_id` optional (falls back to focused). |
| `parse-term` | JSON `{"text":"...", "session_id":"...", "goal_id":"...", "expected_type":"..."}` | `{ok, normalized_input, term_text, warnings}` | Preview a term-DSL string used for `witness` / `trans` / `instantiate` / `case_split`. `session_id` REQUIRED — a bare term has no type scope. `expected_type` (e.g. `"bool"` for `case_split`) is optional. A tactic's own parameter term (`trans`, `witness`, `instantiate`, `term_specialize`, a `by_hyps` witness) is read in this same scope — the goal's resident structure facts included, so an operator at a structure's carrier (`y + x` under a resident `comm_ring(R)`, a `Σ` over its addition) lowers in a parameter exactly as it does here, and a session transcript is spelled in the chapter's own dialect. |

Every JSON command that names a proposition takes a **`PropInput`**:

- **`text`**: agent-authored text DSL, parsed by the engine. A
  statement — a goal, an `assert` claim, a `check-derivation` premise
  or conclusion — is given this way.
- **`key`**: a proof-registry entry — its registered name
  (`dot.AddLeft`) or its own key — accepted only where a lemma is
  cited (`lemma` / `lean_rw`; `with_lemmas[].key` is the same slot).
  A session bound to a family refuses an entry that family's package
  cannot name in Go — another chapter's unexported entry, or one in a
  Go `internal/` package outside the family's tree — and names the
  entries it stands on that the family can cite; `known` does not close
  by one, and `emit-section` refuses a member citing one for the family
  it is emitted into.

There is no `proto_hex` ingress and no embedded JSON term tree. Proto
stays inside in-process Go / future gRPC; JSON envelopes carry only
text and keys.

**Every body is decoded STRICTLY** (`decodeRPCInput`, engine/cmd/xugo/main.go) — an RPC body and a command's JSON on stdin alike: the envelope's `cmd` is dropped and any other member the command's input does not declare is refused by name — `{"cmd":"query","what":"member","name":"dot.AddLeft"}` answers `parse input: … unknown name "name"`, never a downstream "requires `member`". A field the manual does not list is a field the wire does not take.

---

## <a name="prop-input"></a>PropInput — naming a proposition in JSON

Every JSON-envelope command that accepts a proposition takes a
`PropInput` object:

```json
{"text": "<text-DSL proposition>"}    // a statement; parsed by the engine
{"key":  "dot.AddLeft"}               // a registry entry, where a lemma is cited
{"text": "… «R» …", "abbreviations": [{"name": "R", "text": "<term>"}]}  // a goal with its table
{"entry": "projective_line_free_pair.FreeLinePairSplit"}   // a goal: a member's statement, as its author stated it
```

Rules:

- A statement — a goal, an `assert` claim, a `check-derivation` /
  `check-consistency` statement — is given as `text`; `key` there is
  refused.
- A goal may carry `abbreviations`, the names its text and the texts of
  its proof spell as `«Name»` (§"Abbreviations"), or be given as
  `entry`, a registered member whose statement and abbreviations the
  goal takes as written — how a card is attacked.
- `text` follows the [text format](#text-format) below. The engine
  normalizes ASCII operators, runs type inference, and returns
  structured diagnostics on parse failure.
- `key` names a proof-registry entry — its registered name
  (`dot.AddLeft`) or its own key — in a lemma slot (`lemma`, `lean_rw`,
  `with_lemmas[]`). `retrieve`'s corpus group reports members by that
  name, and `query member` takes it.

There is **no `proto_hex` ingress** and no embedded JSON term tree.
Proto stays inside in-process Go APIs and (future) gRPC; JSON
envelopes carry only text and keys. Use `parse-prop` to preview how a
piece of text will be interpreted before committing it.

---

## <a name="apply-lemma-modes"></a>apply lemma — the served form

`apply` (and `probe`) for `lemma` / `lean_rw`, and every
`with_lemmas[]` entry of `by` / `auto_with` / `simp_with`, cite a
registry entry and install the entry's own statement — the form
`query member` prints for it and `ctx.Dep(<entry>)` serves at replay.
Read `term_specialize` keys off that statement — a subscripted binder in
the spelling it prints, `x₀`, or the kernel's `x_0`, either one, never
both; `type_specialize` keys are its type variables. A law read at an
instance (`read_at`) takes the names its statement gives as well: where
the instance spells a free variable of a binder's name — a record over a
term a `let` has since named `N` — the kernel holds that binder under
another name (`N` as `Kʹ`), and the table takes either, never both; a
refusal lists it as `N (held here as Kʹ)`.

A statement no member states is not citable. Prove it as a section of
the session and let the sibling close the leaf, or land the member
first and cite it by name.

---

## <a name="text-format"></a>Text format

```
# A closed statement: its variables ∀-bound, its premises ⇒-antecedents
forall p q:bool. p => (p => q) => q

# A binder's type is written at the binder
forall P:A->bool. forall y:A. (forall x:A. P(x)) => P(y)
```

A goal, like a section or member statement, is closed: `add-goal` (and
the session-less `parse-prop` preview of it) refuses a text with
hypotheses left of `⊢`, naming the closed spelling — every premise is
a ⇒-antecedent the closure's `Fact` parameter binds. The parser still
reads the sequent form `hyps ⊢ conclusion`, with `name:type`
declarations among the comma-separated pieces before `⊢`
(`P:A->bool, forall x:A. P(x) ⊢ P(y)`): it is the input of `xugo check`
(§"Examples"), and the shape the engine prints a proof state in —
`inspect` shows an open goal as `hyps ⊢ conclusion`, and a definition
door's induction principle is served that way.

### Abbreviations

A statement names a compound term that recurs in it, and the texts of
its proof spell the name between guillemets (one constant at three or
fewer plain arguments — names, fields of names, numerals — is written
out, its components implicit, in every table, and a lint refuses the
entry; a constant at more of them may be named where it recurs):

```
# the statement's table: R ≔ restrict_ring(field_ring(L), «O»), O ≔ ring_away(…)
∀L:field_on(A). ∀k:set(A). ∀t:A. subfield(L, k) ⇒ comm_ring_on(«R»)
```

The table is the statement's (`Statement.Abbrev` in Go,
`goal.abbreviations` at `add-goal`, a member's own at `add-goal
{entry}`; a definition's is `registry.DefEntry.Abbrev`, its Equations
read under it over their leading binders, the constant and its key the
expanded equations' — the served statement of a definition is spelled
out, the table being the Go literal's), in order: an entry may spell
the entries before it. A
claim written in parts (`a.Have(label, Statement{…}, …)`) declares
none — every text of the proof reads the member's table. A
`«Name»` is a SPELLING and nothing else — it expands before any name
resolves, exactly as if the term were written out, so every name the
entry spells resolves where the abbreviation is written: the
statement's binder, the goal's variable under its surface name, the
chapter's constant. No equation joins the goal (that is `Denote` /
`Let`), a closer sees the term, and the member's key is the expanded
statement's. The name is verbatim (`«R₀»`, `«free pair»`), never a
token: nothing inside the guillemets is rewritten.

An entry applied — `«P»(m)` — is the application the author would
have written out: for `P ≔ f(a, b)` the one application `f(a, b, m)`,
a dimension the entry writes in its head's `⟨…⟩` staying there
(`«D»(v)` for `D ≔ vec_dist⟨n⟩(u)` is `vec_dist⟨n⟩(u, v)`),
and for a λ, `P ≔ λx. body`, the body at the argument, `body[m/x]`
(`«HasPrimeProduct»(J)` for `HasPrimeProduct ≔ λH. ∃v. v ∈ H ∧ …` is
`∃v. v ∈ J ∧ …`). An argument that is itself a λ is applied where the
body applies its binder, so no redex is left: `«HasPrimeProduct»(λx.
x = m)` is `∃v. v = m ∧ …`. So a claim headed by an applied abbreviation has the
∃ or ∀ its body has — `Obtain` reads its witness off it, `Take`
witnesses a goal that spells it, `f.At(w)` grounds a Have that spells
it — and a leaf's key is the body's, whatever order the entry took its
arguments in: «Without»(m, w) and «Delete»(w, m) for one body are one
plan. A redex the author writes out, `(λx. body)(m)`, is kept as
written.

An entry is generic in the type letters it is written at. An applied
use reads the letters of the λ-binders its arguments fill off the
arguments, so one entry serves every type pair a statement applies it
at: for `predicateAtoms ≔ λR:ring_ops(A). λP:(A → bool). …`,
`«predicateAtoms»(R, P)` over `R:ring_ops(A)` and
`«predicateAtoms»(S, Q)` over `S:ring_ops(B)` are each the entry at
its arguments' letter. A letter no argument fixes is the one the entry
writes, unless the use ties it as a constant's is tied,
`«carrier»⟨A:B⟩`: an unapplied use, an entry passed as an argument
(`fo_quantifier_free_equivalent(«realClosed»⟨A:B⟩, …)`), reads at the
written letters or at the tie's. A letter a free name the entry spells
already types — a statement binder it is written over — stays that
binder's. A tie naming a letter the entry does not write is refused.
The output door folds an instance at other letters back to the entry,
with the tie the text needs to read it again.

One name, one meaning: a text that rebinds a name an entry spells
(`∃t:A. … «R» …` where R is written over the statement's `t`) is
refused as a capture, except the statement's own leading ∀-prefix,
which is what the entries are written over. A `«Name»` with no table
in scope, or a name the table lacks, is refused naming the table.

A chapter has a table of its own, for the terms its statements share —
the ring restricted to the overlap, the pairs over the datum, the datum
itself at its binders — declared once on the family handle, written
over the binders the chapter's statements share:

```
var family = registry.NewFamily("scheme/invertible_lattice_pair", familyCNF).WithAbbrev(Abbrev{
	{Name: "wbVectors", Text: "restrict_module(regular_module(field_ring(L)))"},
	{Name: "wbField", Text: "«wbVectors»(L.carrier)"},
	{Name: "wbRing", Text: "restrict_ring(field_ring(L))"},
	…
})
```

The chapter's table is the outer table of every member and of every
text of the chapter: a statement, in parts or as one string, spells the
chapter's names without declaring them; a member's own `Abbrev` is
read under the chapter's — an entry of the member's may spell the
chapter's, and a name both declare is refused at registration — so a
member declares only the entries that are its own. A lemma stated in
parts inside a member's proof (`ctx.Lemma(Statement{…, Abbrev})`) is
read one level further in: its entries under the member's and the
chapter's, as one table, so an entry of the lemma may spell theirs and
a name both declare is refused. A proof written across the funcs of its
package carries its table along the calls: the Sections script a member
names, a lemma written as its own func and a reader a closure calls each
read under the table of the statement that reaches them. A func two
statements reach reads the entries both declare with one text, and the
claim lints refuse a text of it that spells any other name, and a
statement of it that declares one again (`TestLintClaimParse`). An
exported func and a method are reached from outside the package's
statements, so the lints read them under no caller's table. The same
holds at
a session bound to the family: `add-goal`'s text spells the chapter's
names, its `goal.abbreviations` are read under the chapter's table (a
name the chapter declares is refused), a member attacked by
`goal.entry` comes with its chapter's entries, and the output door
folds a printed term into the chapter's names as into the goal's. A
session's sections spell one table, the member's: a later section's
texts spell an earlier section's names without declaring them, a
section may declare a name an earlier one declares with the same
text (one entry), and `add-goal` REFUSES a table declaring a name an
earlier section declares with another text, naming the section and
the two texts — a claim never reads a name with another section's
meaning; rename the entry in one of the two, or prove that goal in a
session of its own. What `emit-section` writes declares only the
entries beyond the chapter's.
The index renders the chapter's table once, on the family's page, and
a member's statement with the entries it spells.

A chapter whose statements spell another chapter's names — one cut
from it, as a rule — reads that chapter's table before declaring its
own:

```
var family = registry.NewFamily("scheme/closed_divisor", familyCNF).WithOuterAbbrev(smooth_curve.ChapterAbbrev).WithAbbrev(Abbrev{
	…
})
```

the read chapter exporting its table from its family.go as `var
ChapterAbbrev = family.ChapterAbbrev()`. The read entries are the
outer table of every text of the reading chapter — a statement, a
proof's claims, a definition's equations, a session bound to the
family, the output door's fold — and the chapter declares only the
entries that are its own; a name its own table declares again is
refused at registration, and what the chapter exports carries what it
read, so a chapter that reads under it in turn reads through. A
chapter may read several tables, `.WithOuterAbbrev(a.ChapterAbbrev,
b.ChapterAbbrev)`: an entry two of them hold, one name with one text,
is read once — two chapters cut from one parent each export the
parent's entries — and one name with two texts is refused. The entries are
written over the read chapter's binders, so a chapter reads a table
only where its statements bind the same names. The index lists the
read chapter on the reading chapter's page and the entries on the
read chapter's.

What the engine serves folds the other way: a goal, a hypothesis, a
witness the output door prints spells `«R»` where the term stands, and
`«P»(m)` where the body of a λ-entry stands at m
(`inspect`, the lineage, `emit-section`'s claims and witnesses), and
the typed text (`statement_typed`) stays written out, since it is
checked against a key at a door that reads under no session's table.

### Connectives

| Write        | Means | Notes |
|-------------|-------|-------|
| `p => q`    | p ⇒ q | implication, right-associative |
| `p <=> q`   | p ⇔ q | biconditional |
| `p /\ q`    | p ∧ q | conjunction, binds tighter than ∨. **LEFT-associative** — `a ∧ b ∧ c` is `(a ∧ b) ∧ c`. See the note below |
| `p \/ q`    | p ∨ q | disjunction, **LEFT-associative** — same caveat |
| `~p`        | ¬p    | negation |
| `true`      | ⊤     | top |
| `false`     | ⊥     | bottom |
| `x = y`     | x = y | equality |

All ASCII variants (`=>`, `/\`, `\/`, `~`, `<=>`, `->`, `forall`, `exists`, `true`, `false`, `not`, `and`, `or`, `&&`, `!`) are auto-normalized to Unicode silently. The turnstile has no ASCII spelling and `||` is not ∨: `|` opens the `|x|` notation, so `||x||` and `|-x|` are magnitudes.

**When ∧'s associativity is load-bearing.** `Normalize` flattens a
conjunction that sits where clausification reaches it — an implication's
antecedent, a top-level conclusion — so `(a ∧ b) ∧ c` and `a ∧ (b ∧ c)`
are usually the same normalized proposition and the associativity above
is invisible. It is NOT flattened inside a quantifier body that survives
into the normal form: under an `∃`, the two nestings normalize to
different props with different keys, and a `∀` hoisted out of the left
pair can merge with its neighbour where the right nesting keeps the two
binders apart. So a three-way conjunction restated from a source whose `∧`
nests to the right needs its parentheses written out under an `∃` — a
bare `a ∧ b ∧ c` here is not it.

### Implicit structure arguments

A chapter's derived operation declares the structure components it reads
as IMPLICIT leading arguments (`registry.DefEntry.Implicit`: `vec_add` reads `add`; `vec` reads `zero`;
`dot` reads `add, mul`; `basis_vector` reads `zero, one`; `vec_linear` reads
`add, mul`). Under a goal or session that binds those names the text
leaves them out and the parser completes them (ext/dsl/implicit.go):

| Write | Means | When |
|---|---|---|
| `vec_add(u, v)` | `vec_add(add, u, v)` | the goal binds `add` — a structure law's `∀add …` prefix, or its Skolemized binder |
| `vec_add` | `vec_add(add)` | a bare head, as a fold's operation: `iterated_op(vec_add, s, F)`, `monoidal_op(vec_add)` |
| `dot⟨n⟩(u, v)` | `dot⟨n⟩(real_add, real_mul, u, v)` | the session's family binds the components to an instance (`session-create` with `family: vector/euclidean`) |
| `dot⟨n⟩(real_add, real_mul, vec_of_int(u), vec_of_int(v))` | itself | under `vector/lattice`'s integer binding: the arguments' types read the prefix as another instance's components |
| `closed_in(S, c)` | itself | under a binder `T` for the family `closed_in` reads implicitly, at a SECOND space `S`: the short reading would put `c` past the predicate's spine, whose result is bool and takes nothing more, so the application is read as the prefix it spells |
| `subtopology(real_topology, s)` | itself | under a binder `T : set(set(A))`, a SET-valued constant at a second space: the short reading has slots to spare (the result is a set of sets), and `real_topology : set(set(real))` fits the slot `set(A)` on its own by taking A to be `real → bool` — but the two readings are each checked as ONE application, the components put in front included, so T's own type pins A first and real_topology no longer fits; the same check keeps `interior(T₀, s₀)` as written beside a declared `T` |
| `subtopology(subtopology(T, s), t)` | itself | under a binder `T : set(set(A))`, a set-valued constant at a space BUILT from the bound one: the first argument is an application of a polymorphic constant, whose result the reading takes off its arguments' own types (`subtopology(T, s) : set(set(A))`, `product_topology(T, S)` a set of sets of pairs) — an application whose arguments fix every letter of its result is typed, one that leaves a letter open is not. That type contradicts the short reading's next slot, so the explicit spelling is kept; left untyped nothing refuted the short reading and `T` was put in front of a full application (`dsl.TestImplicitArgs_SetValuedAtCompoundSpace`). |

A record in scope supplies an implicit component by its field name:
under `R:ring_ops(A)`, `vec_add(u, v)` reads `vec_add(R.add, u, v)`.
A bound or declared component name has priority, followed by a local
record field, then a family instance binding. Local records shadow the
family default. Where several records declare a field, the
application's types pick the record: each record is tried in the short
reading, checked as one application as below, and the one reading that
stands is taken. Under `R:ring_ops(A)` and `S:ring_ops(B)`,
`polynomial_eval(P, y)` with `P : num → B` reads S's four fields; an
operator and a big operator pick by their operands' types the same way.
Records on one carrier, or arguments whose types the text leaves open
(a bare head, an unannotated binder), leave more than one reading
standing; no record is guessed, and the field is written explicitly.
An application beginning with an explicit record field keeps that prefix
when its arguments fit the explicit slots, including a different second
component: `delta_at(R.zero, a, x)` uses coefficient `a`. A prefix missing
an operation of the required type is still refused. `WithInstance` binds
the record and its normalized fields from its instance theorem, so a
concrete chapter's short spelling uses the concrete operations. Fields
shared by several instance records retain their record qualifiers.

The leading arguments are either the components or absent: a prefix
spelled in part is an error. They are the components when they spell
the bound ones — the name where a binder binds it, the minted variable
that name stands for under stripped binders (`delta_at(zero₀, one₀, x₀)`
beside a surface `zero`, `one`: the print of a session goal reads back),
the instance's canonical spelling where a family does — and when the text can only
mean that: under a binding, an application whose leading arguments
spell ANOTHER instance's components in full is read as the prefix it
is, by the arguments' types — and so is one whose first arguments
happen to spell bound names before the rest spell another structure's
is the explicit application, not a prefix spelled in part. Where the text fixes an argument's type
on its own (a constant's, a coercion's, an annotated binder's, a
numeral's, a typed lambda's, read from its body) that type is read
against the constant's binders under both readings, as the implicit
prefix and as the explicit arguments. An operator application's type
is the one the build dispatches it to: an arithmetic symbol at its
operands' common type and `^` at its base's, each in its built-in
domain, and only where those types exclude that domain, the result
the symbol's applicable declarations agree on — so
`λa:real. λb:real. a + b` is typed as `λa:real. λb:real. real_add(a, b)`
is. An application with an operand whose type the text does not fix
stays untyped, since the build reads each operand at its own type
before it chooses: `&1 + &2`, and `c • (x + -y)`, which the build
reads as a module's smul once x − y is read at the module's elements,
though vec_scalar_mul, which declares `•`, would take it. The prefix
is spelled when no such argument contradicts the explicit reading while
one contradicts the short one: under the integer ring,
`dot⟨n⟩(real_add, real_mul, vec_of_int(u), vec_of_int(v))` is the real
form of the images (`real_add` fits `add` and is no dimension) and
`vec⟨n⟩(&0, vec_of_int(u))` the real membership (a coercion is no num).
Where both readings fit, or nothing local decides, the bound instance's
reading stands: `vec_zero(0)` under ℤ is the integer zero vector at
index 0, `vec_scalar_mul(&2, u)` the scaling it looks like (a coercion
is no operation). Where nothing binds the names the
parser completes nothing — the application is the explicit one it can
only be there, and a short form fails as the type error it is; where
some but not all are bound, the short form is refused naming the
missing binder (`dot: its implicit argument mul is not in scope`). A
variable named like a component is that component where it carries a
structure — a structure predicate is applied to it, in the text or in a
fact of the goal the text is read under, or it is a record — or where
every component of the application is read from a variable. Where a
variable that carries none has the name of one component and a record
or the family's instance supplies another, the application — the short
form and an operator alike — is refused naming the variable: under a
family that binds a monoid, `∃e:complex. … (c − c) ^ n …` would
otherwise read the power at the bound `e` as its identity. A binder, a
Let or an obtained witness named `e`, `op`, `add`, `zero`, … beside
such a use is renamed. Both
spellings parse to the same term and key;
`query member`, `inspect`, `cards` and `emit-section` print the short one
under the same scope, a term of another instance staying explicit there.
The dimension is never implicit.

**The output door.** Every text the engine serves about a goal or a
statement — `inspect` / `apply` `statement`, `hypotheses[].term` and
`statement_typed`, `new_hyps`, `closed_subtrees`, `auto_matched`, the
`parse-prop` / `parse-term` previews, `session-create`'s installed
rules, `defer` / `cards` / `lineage` / `dump-section` statements — and
every prose label `emit-section` writes (a Have, Show
or Case label, a `// context:` comment) goes through one door
(engine/spelling.go, `Session.Spelling`): the kernel printers' text,
read back through the chapter's spelling (ext/dsl `ChapterSpelling`,
served as `DisplaySpelling`) under the bound family's instance
bindings. Operator probes give each constant occurrence its own type
letters; carrier letters written in the statement stay fixed, including
function carriers. The kernel printers themselves are untouched and the door is
pure text: implicit components the family binds to an instance are
dropped, a component bound to a VARIABLE is dropped only where a
structure predicate over it stands in the text — a law's
`is_topology(T) ⇒ … closed_in(c)` is served short, a plain theorem's
`closed_in(T, c)` as written, the chapter's visible sign that it needs
no structure (constitution §Structures; the registration lint's
criterion, `dsl.ConstSyntax.StructurePredicate` the door's), and what a
definition's equation states — its definiendum, the body conjuncts
that apply a structure predicate — keeps its components, as the bundle
fold leaves them spelled (§"Bundles") — and
full applications fold into the notations the chapters declared —
`‖u‖_n`, `u + v`, `Σ_{i<n} f(i)`, `sum(s, f)` — never `vec_norm(n, u)`. A
structure's component, or a record's field, folds into its symbol only
where the parser reads the symbol back as that component or field:
where every binder and declared variable is typed, the parse's own
reading decides, and in a display, whose binders and Skolems carry no
types, a symbol folds only where one holder holds it at that arity —
one component, a variable, or one field of one record the display
shows by a projection or a predicate on records applied to it
(`ring_add(R, a, b)`, `comm_ring_on(R)`). Under `comm_ring_on(R),
group_on(G)`, R a ring on A and G a group on B, `R.add(a, b)` prints
`a + b`, which R.add alone holds, and `R.mul(a, b)`, `G.mul(u, v)`,
which share `*`, keep their names, the spelling that reads back either
way, as two components sharing one symbol both do. A component
structure's fact spelled over a record's fields binds none of them
there, the record's own field symbols deciding what the parser reads.
The fold
reads the symbol, not its operands, and a display drops its binders'
types: `∀a b. a + b = b + a` reads back only where another occurrence
types `a` and `b` — `R.mul(a, b)` beside it does — while a Skolem
operand, declared in the session, always is typed. The
parse-faithful `statement_typed` is the same spelling checked to
re-parse to the goal's key at the statement door of a session bound to
the family — the scope `add-goal` parses with, built by the one
constructor both use (`engine.StatementDoorScope`), so a served
`statement_typed` is a text `add-goal` reads there and an absent one
is a statement the door reads no print of — an `&` no operand
anchors, under a chapter that declares no domain, is the one such
shape; a display has no key, so there the
spelling is sound by construction: an application still carrying an
implicit prefix the scope would not put back (a session bound to no
family, a term of another instance) keeps the call form — its leading
arguments are components, not an operator's holes — and a text the
spelling cannot read is served as the printer wrote it. The door
re-prints every text it reads, whether or not a notation folded: a
statement with nothing to fold comes out in the chapter's form too —
binders grouped, the left-associated ∧ unbracketed, a comprehension in
braces — never in the kernel printer's parenthesized one because its
neighbour happened to fold (`dsl.ChapterSpellingFolded` reports the
fold for the one reader that keeps an author's own text when nothing
folded: the index's headlines). A session
bound to no family spells under no bindings: the registry's notations
still fold, every structure component stays spelled. Diagnostics (a
tactic's refusal naming a hypothesis) still quote the kernel printer.

**A member's two texts.** A corpus member is not printed through that
door: it has an authored text, and every door that shows a member
serves the same two texts for it. `statement` is the chapter's
(`registry.ProofEntry.StatementText`) — the headline the member's
constructor parses, folded into the notation the chapter declares
today when the fold parses back to the member's own key; a statement a
definition door computed has no headline and is the parser print in
the same spelling. Every `query` answer, `retrieve`'s corpus entries,
a landed card in `cards` and the pages under `library/index` serve it,
so
`∀f:(A → B). ∀P:(A → bool). {f(x) | x:A | P(x)} = image(f, {x:A | P(x)})`
is what each of them says. It reads at the member's statement door —
under the family's vocabulary, which may declare its variables.
`statement_typed` (at `query member`, `query dossier` and a landed
card in `cards`) is the member's statement as a goal's is served
(`engine.EntryStatementTyped`, at the family's statement door):
the text that reads with nothing declared, paste-ready for `add-goal`
in a session bound to the member's family — every binder typed, a
constant's type letters pinned where nothing else fixes them
(`𝕌⟨A:B⟩`), a free variable declared before `⊢`, checked at that
door's own scope to parse back to the statement, absent when no print
of it does. `TestServedStatementSurface` requires every member to have
one and checks every final served text against the member's statement.
`TestAddGoal_ReadsServedStatementTyped` checks the live
query-to-add-goal path on representative input forms. A session bound
to another family, or to none, may
refuse the text: it leaves the family's components unspelled and its
`&` unanchored.
Binder names are the statement's in both texts (`term_specialize`
keys), and so are the type variables — the letters of the binder types
(`type_specialize` keys).

**`statement_typed` is the α-class.** For a goal and a member alike
the typed text is the sugared parser print: a set-builder reads
`{x:A | φ}` and a paired lambda `λ(x:A, y:B). t`, never the encoding
they lower to (`set_comprehension(λGEN%PVAR%33:A. …)`,
`pattern_abstraction(λf. …)`). The encoding's own binder has no
spelling in that text and the parse names it afresh, so a pasted text
is the same statement up to that one name — a new goal, whose recorded
steps are recorded against its own names. Where the name surfaces (a
step that frees the comprehension's binder), read it off the goal the
step leaves, not off an earlier goal's.

A chapter may also declare a NOTATION for a constant
(`registry.DefEntry.Notation`, spelled with the definition's binders;
ext/dsl/outfix.go and ext/dsl/operator.go read the forms).
An OUTFIX — `"‖u‖_n"` for `vec_norm⟨n⟩(u)`, `"⟪u, v⟫_n"` for `dot⟨n⟩(u, v)`,
`"|x|"` for `real_abs(x)` — is body arguments between a delimiter pair the
lexer knows (`‖…‖`, `|…|`, `⟪…⟫`, `⁅…⁆` — U+2045/U+2046, a quotient's
class — and `⟦` or `⟬` — U+27E6, the mathematical left white square
bracket, and U+27EC, the mathematical left white tortoise shell bracket —
each closed by `⟧` or `⟭`), then an optional `_` subscript that is a
name, a numeral or a parenthesized expression. A notation is its delimiter
PAIR: the four bounded intervals of reals are four notations on four
constants — `⟦a, b⟧` real_closed_interval, `⟬a, b⟭` real_open_interval,
`⟦a, b⟭` real_closed_open_interval, `⟬a, b⟧` real_open_closed_interval —
and `(a, b)` stays the pair: a pair of reals where a set is expected is
refused with the open interval's spelling. The textbook brackets `[`, `]`,
`⟮`, `⟯` are not lexed; the refusal names the four spellings. Prose writes
intervals the same way, rays included (`⟦a, ∞⟭`, `⟬−∞, b⟧`), and the
extended nonnegative reals are `⟦0, ∞⟧`; a statement writes a ray as its
set-builder. A pair of delimiters belongs
to one constant, or to several that declare one overloaded word and place
their holes alike — `|x|` on real_abs, int_abs and complex_abs under `abs`:
the notation is the word in bars, read by the body's type exactly as
`abs(x)` is (a variable named `abs` shadows both). `|` is also the
set-builder's separator and the two never meet: the separator follows an
expression, the notation opens one (`{x | |x| < &1}`, `{ |x| | x | x ∈ s }`);
`||x||` and `|-x|` read as written: `||` is not an ASCII ∨ and `|-` not an
ASCII ⊢. An INFIX or PREFIX — `"u + v"` for `vec_add`,
`"u - v"` for `vec_sub`, `"c • u"` for `vec_scalar_mul`, `"-u"` for `vec_neg`,
`"a ⟶ l"` for `real_converges_to` — is a
symbol the grammar already parses, resolved by OPERAND TYPE like `+` at
num/real/int: the built-in domains first, then the declaring constant,
its implicit prefix completed from the scope. Several constants may
declare one symbol at one arity, each on its own carrier — `z * w` is
`complex_mul` on ℂ, `p * q` is `permutation_compose` on the permutations,
`u + v` is `vec_add` on vectors beside `complex_add` on ℂ — and the
operands' types pick the one that fits; operands two of them fit alike
are refused naming both, and the constant's name is the spelling there.
A vector `+` beside a real `+` in one statement are two operators, each
on its own operands. A declaring constant whose implicit prefix the
scope cannot complete steps aside for a structure's component or a
record value's field that takes the operands (`u + v` at the vectors of
a module value M is `mod_add(M)(u, v)`, not `vec_add` missing its
`add`), and its refusal is the one reported when nothing else does. The
infix alphabet is `+ - * / • ⟶ ^ ≤ <`; `•`, `⟶` and `^` have no built-in
domain, so the declaring constant is asked outright and the two operands
need not share a type. `≤` and `<` are an order a type declares
(`"x ≤ y"` for `extended_le` on ⟦0, ∞⟧), read like `+`: the built-in
domains first, then the declaring constant; `≥` and `>` are not
declarable, so a declared order is written with its smaller side on
the left. `^` is the power: it binds tighter than the
prefix `-` and `¬`, looser than `&` and application, and associates to
the right, so `-x ^ 2` is `-(x ^ 2)`, a negated base is written
`(-x) ^ 2`, `&2 ^ n` is `(&2) ^ n`, and `x ^ m ^ n` is `x ^ (m ^ n)`. `⟶` sits at the comparison level, non-associative:
`a ⟶ l + e` is `a ⟶ (l + e)`, and `a ⟶ l ⟶ m` is the chained-relational
parse error `a < b < c` is. `⟶` alone also has a THREE-hole form, the
limit mixfix `"f ⟶ l (at c)"`: the relation followed by a point clause,
parsed exactly as the congruence `x ≡ y (mod m)` is (the clause is part
of the production, `at` is not a reserved word, and an application in
the limit slot does not swallow it). The clause form is served by the
constant declaring `⟶` at arity 3 and the bare form by the one at arity
2 — two constants, told apart by the clause, not by operand type — and
the notation's holes are read in reading order (function, limit, point)
against the constant's own argument order, so `real_limit_at(f, c, l)` may
declare `"f ⟶ l (at c)"`.

| Write | Means |
|---|---|
| `‖u‖_n` | `vec_norm⟨n⟩(u)` |
| `|x|`, `|z|` | `real_abs(x)`, `int_abs(x)`, `complex_abs(z)` — by the body's type, as `abs(…)` |
| `‖u + v‖_(m + 1)` | `vec_norm⟨m + 1⟩(vec_add(real_add, u, v))` under vector/euclidean |
| `⟪u, v⟫_n` | `dot⟨n⟩(real_add, real_mul, u, v)` under vector/euclidean |
| `a ⟶ l` | `real_converges_to(a, l)` under real/real_sequences |
| `f ⟶ l (at c)` | the constant declaring `⟶` at arity 3, its point clause read like `(mod m)` — REFUSED where no chapter declares one |
| `c • u - v` | `vec_sub(real_add, real_neg, vec_scalar_mul(real_mul, c, u), v)` — `•` sits between `+ -` and `* /`, right-associative |
| `-u` | `vec_neg(real_neg, u)` |
| `z ^ n` | `monoid_pow(complex_mul, complex_of_real(&1), z, n)` where the family binds ℂ's product monoid — REFUSED where nothing binds `op`, `e` |
| `u + v` | REFUSED where nothing binds `add` — the short spelling it stands for |
| `c + d`, `c * d`, `c - d`, `-c` at the ring's carrier; `c • u` at a scalar and a vector | `R.add(c, d)`, `R.mul(c, d)`, `R.sub(c, d)`, `R.neg(c)` — the fields of the bound ring record R (`DataField.Symbol`); a record's part carries its symbol the same way (`c • u` is `mod_smul(M)(c, u)` under a module value M, DataField.Symbol), read at the operands' types, so a part whose operands differ carries one too; `R.zero`, `R.one` stay fields |

`\|` is the set-builder's separator and the magnitude's bar alike — the
separator follows an expression, `\|x\|` opens one, so the two never meet —
and `‖` is the norm's; `−` (U+2212) reads as `-`. A notation with
no constant declaring it in scope is an error; the printers fold a full
application back into it, an operation applied to a point as `(u + v)(i)`.

A BIG OPERATOR is declared on a carrier's named sum
(`registry.DefEntry.BigOp: "Σ"` on `real_sum`, `nat_sum`, `int_sum`; `"Π"` on the
products; ext/dsl/bigop.go) and dispatched by the BODY's type; a carrier with no named sum
folds through `iterated_op` at its `+`. The index binds over the body and
carries no annotation — its type is the range's — and the body is read
at `•`'s level: a product is in, a sum needs parentheses. `∑` reads as
`Σ`.

| Write | Means |
|---|---|
| `Σ_{i<n} u(i) * v(i)` | `real_sum({i:num \| i < n}, λi:num. u(i) * v(i))` at a real body |
| `Σ_{i∈s} f(i)` | `nat_sum(s, λi:num. f(i))` at a num body |
| `Σ_{i∈s} F(i)` | `iterated_op(vec_add(real_add), s, λi:num. F(i))` at a vector body under vector/euclidean |
| `Σ_{i<n} a(i) + b` | `real_sum(…, λi. a(i)) + b` — the body stops before `+` |
| `Σ_{i∈s} f(i)` at `f:(num → A)` under the ring | `iterated_op(add, s, λi:num. f(i))` — the fold at the bound component |
| `Σ_{i<n} g(i)` at `g:(num → A)` with no structure fact | REFUSED — no sum at a type variable |

The binder always produces a λ. `iterated_op(vec_add, s, F)` is the same
statement at another kernel term — keys, the apply rung and the
assumption step identify the two up to βη — and the printers fold only
the λ form: a served claim denotes the term the proof stated.

An OVERLOADED WORD names, among the constants that declare it, the one
the arguments select (`registry.DefEntry.Overload`, and
`registry.SpecConst.Overload` for a constant a specification mints;
ext/dsl/overload.go): `sum` on `real_sum`, `nat_sum`, `int_sum`,
`product` on the four products, `sup` / `inf` on `real_sup` /
`real_inf`, `dist` on `nat_dist`, `real_dist` and `vec_dist`, `div` /
`rem` on ℕ's and ℤ's division pairs (`nat_div` / `nat_mod`, `int_div` /
`int_rem`), `sgn`, `max` and `min` on the ℕ, ℤ and ℝ constants, `exp`,
`log`, `cos`, `sin` on the ℝ and ℂ functions. The number of arguments
narrows first, then their types — built on their own, so the summand's
values decide, and a bare `&` is ℝ's (`sgn(&0)` is `real_sgn(&0)`).
Where that reading fits no candidate, each candidate reads the
arguments against its own domains, as its name would, and the one that
reads them is the constant: `rem(n, &2)` at `n:int` is `int_rem(n, &2)`.
The term is the constant's own application: a statement's key does not
depend on which spelling its text used, and a verb that names a
constant (`def_expand`, `Unfold`, a vocabulary row) keeps the
constant's name.

| Write | Means |
|---|---|
| `sum(s, f)` at `f:(A → real)` | `real_sum(s, f)` |
| `sum(s, λi:num. i)` | `nat_sum(s, λi:num. i)` — a num body |
| `dist((m, n))` / `dist⟨n⟩(u, v)` | `nat_dist((m, n))` / `vec_dist⟨n⟩(u, v)` — by the number of arguments, and the dimension in the word's `⟨…⟩` (§"Dimensions") |
| `sup(s)` | `real_sup(s)` — one constant under the word |
| `div(m, n)` at `m n:int` | `int_div(m, n)`; at `m n:num`, `nat_div(m, n)` |
| `rem(n, &2)` at `n:int`, `div(&7, &2)` | `int_rem(n, &2)`, `int_div(&7, &2)` — ℝ takes no division, so the `&` is read at the one candidate that reads the arguments |
| `sum(s, λi:A. &0)`, `max(&m, &n)` | `real_sum(s, λi:A. &0)`, `real_max(&m, &n)` — a bare `&` is ℝ's where ℝ is a candidate; write `int_sum`, `int_max` for ℤ |
| `sum(s, f)` at `f:(A → B)` | REFUSED — no sum at a type variable |
| `sum` unapplied, `sum⟨A:num⟩(…)` | REFUSED — the word spells a full application; annotate the constant |

Resolution order for an applied name: a bound or declared variable, a
constant the scope declares, the word, then the resolver — so in a
session `sum(s, f)` reads as the constant its arguments select. The
output door (above) folds a full application back into the word unless
the text already spells that word; `statement_typed` and an emitted
payload keep the short text only when it re-parses to the same
statement.

### Dimensions

A constant that reads its vectors, matrices or maps at a dimension
declares which arguments those are (`registry.DefEntry.Dim`,
`RowDim`/`ColumnDim`, `SourceDim`/`TargetDim`): the leading arguments
after its implicit prefix. A constant that reads a space at a dimension
no such argument carries — a manifold, whose points are no vectors —
names those binders in `DefEntry.Dimensions` instead, and they take
the same place: `smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)`. The text
writes the declared dimensions in the `⟨…⟩` after the constant's name,
where an instance's type letters stand (`fun_add⟨D:D⟩`), and
everything else in the parentheses (ext/dsl/dimension.go):

| Write | Means |
|---|---|
| `vec⟨n⟩(u)` | u is a vector of dimension n, at the zero the scope binds |
| `vec⟨n⟩(zero, u)` | the same with the component spelled: an implicit prefix the text writes stays in the parentheses, which is how a definition's own equation reads |
| `matrix⟨n, m⟩(A)` | every declared dimension, in argument order |
| `vec_dist⟨n⟩` | the constant at its dimension and nothing more — the metric of ℝⁿ, as `metric_space({u \| vec⟨n⟩(u)}, vec_dist⟨n⟩)` takes it |
| `dist⟨n⟩(u, v)` | `vec_dist⟨n⟩(u, v)`: an overloaded word takes the suffix its constant does |
| `vec⟨A:real, n⟩(u)` | a type letter beside the dimension |
| `‖u‖_n`, `⟪u, v⟫_n` | a notation's subscript is the same argument |
| `vec(n, u)`, `vec(zero, n, u)` | REFUSED: a dimension in the parentheses. The refusal prints the text to write |

The kernel term is the plain application, `vec(zero, n, u)`: a key is
that term's, a verb names the constant or its definition (`def_expand`
`{const: "vec"}`, `Unfold(vec_space.VecDef)`),
the kernel printers print the application, and the output door writes
their text with the suffix as it folds a notation. The constants
that declare `Dim`, `RowDim`/`ColumnDim` or `SourceDim`/`TargetDim` are
the ones whose Go wrappers carry the dimension as a phantom on the
value (§"Vectors and matrices: the dimension rides the type, not the
statement"); a binder named in `Dimensions` stays an ordinary
parameter of the wrapper. A num argument no declaration names —
`adjoint(m, n, f, y)`, `vec_span(k, e)`, `basis_vector(k)` — is an
ordinary argument.

### Bundles

A BUNDLE is a name standing for a structure's components in the text
(ext/dsl/bundle.go), the way a locale's context fixes its parameters
once. The parser writes every bundle out as the components before it
reads anything else, so the kernel term and its key are those of the
spelled-out text, and the chapter spelling folds them back. A structure
on one record — a group, ring or field — has the record as its one
component, so its bundle binder binds the record itself, and the
record's field `R.add` is its projection (§"Records").

| Write | Means |
|---|---|
| `∀G:sheaf_of_rings(C, D). body` | `∀G_T:set(set(C)). ∀G:(set(C) → ring_ops(D)). ∀G_res:(set(C) → set(C) → D → D). sheaf_of_rings(G_T, G, G_res) ⇒ body` — a BUNDLE BINDER: the structure applied to bundles in scope and to the types of the components no bundle gives (C, D); each fresh component named after the definition's binder where the text does not hold that name, else under its bundle (`G_T`: a sheaf F before G took `T`; a name carries the structure it belongs to, never a count of the structures before it), the subject (the component the definition declares the predicate said of, `DefEntry.Subject`) after the binder |
| `∀S:comm_ring_on(B). body` | `∀S:ring_ops(B). comm_ring_on(S) ⇒ body` — the bundle binder of a structure on a record: the record is the one component and the subject |
| `∃G:sheaf_of_rings(C, D). body` | the same components bound by `∃`, the structure fact `∧ body` |
| `∀S:short_exact_complexes(A, B, C, D). body` | a structure with no subject, under the letter it declares (`DefEntry.Letter`): every component fresh under its definition's name (`R`, `P'`, `P`, `P''`, `i`, `p`), the bundle `S` no component is |
| `lrs_isomorphism(F, G, φ, ψ)` | `lrs_isomorphism(T, F, res, G_T, G, G_res, φ, ψ)` — a BUNDLE ARGUMENT, laid out where the constant declares a bundle of its structure goes; the other arguments fill the remaining parameters in order |
| `lrs_morphism(X, spec_sheaf(R), f, ψ)` | the three terms of the tuple `spec_sheaf(R)`, `zariski_topology(R), spec_section_ops(R), structure_restrict`, spliced where it stands |
| `X.T`, `G.res` | the component of the bundle that the structure's definition names so |
| `comm_ring_on(F(U))`, `ring_homomorphism(F(U), F(V), res(U, V))`, `local_ring_on(stalk_ring(x))` | a FIBRE: the sub-structure a structure's definition states for every value of an index — the ring homomorphism between the rings on F(U) and F(V) of a sheaf of rings, the local ring at a point of a locally ringed space — named by its subject's template at any term; its components are the definition's templates at that term, the ring record `F(U)` itself for a structure on a record |

After `strip_quant`, resident bundles remain readable through both the
surface aliases (`P`, `P.d`) and the minted names (`P₀`, `P₀.d`). A subject
that keeps its name while its components are renamed denotes the same
bundle; those two spellings are not conflicting structure facts.

A bundle is read off a STRUCTURE FACT — a structure predicate applied to
variables, spelled out or in its implicit-short form — as the bundle
binder states it, as a law's antecedent states it
(`comm_ring.CommRingOn.Statement` gives the ring R), or as a goal's
resident hypothesis does. It is
named after its SUBJECT, the component the definition declares the
predicate said of (`DefEntry.Subject`: the record a ring is, the map a
homomorphism is, the relation an order is, the sections a sheaf
assigns), and each sub-structure the structure's definition states over
its components (a ring homomorphism's two rings) is a bundle named
after that one's subject; a sub-structure on the structure's own
subject (a locally ringed space's sheaf of rings on F) is the
structure, and F stays the locally ringed space. A
structure on a whole type declares no subject: its bundle has the
binder's name only, and a fact of it states none. One with no single
subject — three complexes and two maps — declares instead the letter
its laws fold under (`DefEntry.Letter: "S"`, no component's name), and
the chapter spelling writes such a law's components as
`∀S:short_exact_complexes(A, B, C, D).`. A bundle's scope is
the right side of the `⇒` or `∧` that states it. A name two facts read
differently is no bundle, unless one fact is a sub-structure fact of
the other over its components — a scheme F restated as a locally
ringed space — when the richer stands.

Where a bundle goes: a structure lays out its own components and its
sub-structures, read off its definition; another definition declares
its layouts (`registry.DefEntry.Bundles`, each a structure applied to the
definition's binders, `_` for a component it does not take). A bundle
takes the first unused layout of its structure that the arguments so
far leave free or fill as it would, so of two sheaves the first takes
the first layout and the second the second (`lrs_isomorphism(F, G, φ,
ψ)`).
A layout of a sub-structure counts too, composed through the layout
that states it, where it lands on components alone.
An application spelling every parameter is read as spelled; one with
exactly the arguments its implicit prefix leaves, every implicit name
bound, is the implicit completion's, and where a bundle would lay it
out otherwise the two readings are refused together — spell the
components. At a goal whose resident bundle's
components are spelled by surface names (`X₀` as `X` after
`strip_quant`), the bound implicit names ARE those components — until
the text binds the name itself (`∀X:… .`), below which `X` is the
text's: under the one resident instance its short spelling lays out the
same components either way and reads one way. Beside a second instance
whose components the bound names are not, the second's short spelling
reads two ways — the bound names (the first instance's) against the
ones minted under its bundle — and is refused naming both.

A structure INDEXED by another states the fibre in its definition as a
conjunct under ∀ binders, over terms in its components — `sheaf_of_rings`'s
`∀U V:set(A). U ∈ T ∧ V ∈ T ∧ V ⊆ U ⇒ ring_homomorphism(F(U), F(V),
res(U, V))` —
and the registry reads it as an indexed layout (`BundleLayout.Index`,
`Templates`). A fact of the structure then states the fibres as a
FAMILY (ext/dsl/bundle_fibre.go), a bundle with a hole per index, and
a text names a fibre by its subject's template at a term, the
implicit-short spelling included: `F(U ∩ V)`, `stalk_ring(x)`.
A ∀-fact in a text states a family the same way, so a definition's
second conjunct passes the fibres its first states; a resident fact
over terms states the bundle its subject term names. The left side of
a definition's `⇔` states, for the body, the bundles its constant lays
out — a structure's own; a definition's declared layouts, registered
before its equation is read, so that `lrs_isomorphism`'s body writes
`ring_isomorphism(F'(V), F(…), ψ(V))` under its two sheaves. What the
equation STATES is served spelled in full: the definiendum, and each
conjunct of the body, through ∀ binders and ⇒ guards, that applies a
structure predicate — the layouts the registry reads off it. The body
is the statement of those layouts, not a restatement of the left side,
so `chain_complex(R, P) ⇔ … ∧ (∀n:num. module_homomorphism(R,
complex_module(P, n + 1), complex_module(P, n), P.d(n + 1))) ∧ …` says
which modules the boundary runs between, where a law under the complex
restates the fibre by its name, `module_homomorphism(P.d(n + 1))`; the
elision keeps a stated application's components the same way, and a
use in the body — `face_family(n, …)` under `kan_complex(X)` — folds
as in a law. A field of a family's head is a component that
does not vary with the index, `X.T`, a locally ringed space's topology.

The chapter spelling writes a structure applied to the components of a
bundle in scope as that bundle — `comm_ring_on(F(U))`,
`local_ring_on(stalk_ring(x))` — unless its layouts name every other
component as a bundle too, when it is written over those,
`ring_homomorphism(F(U), F(V), res(U, V))`; a structure fact over
variables is what states its bundles and stays spelled. A fold names a
bundle by a variable or an application, never by a λ. Two layouts may
share components — the inclusion's and the projection's in
`short_exact_modules(i, p)` share the ring and the middle module — and
each folds, the later at the first of its slots the earlier left.

A quantified structure hypothesis folds to its bundle binder even when
parentheses enclose the whole implication (`∀`) or conjunction (`∃`),
including the parentheses emitted by the typed parser printer. The fold
preserves the residual body's logical grouping and the surrounding scope,
including negation and occurrence inside another implication.

A TUPLE (`registry.Family.Tuple`) is a named list of terms that stands
among an application's arguments and is spliced there: a constructed
structure's components named once (`spec_sheaf(R)`, the spectrum's
topology, section rings and restriction). A parameter stands for a
term, for a type where a type stands, or for a bundle through its
fields (`sheaf_restriction(S, U)` reads `S.T`, `S.F` and `S.res`). A
type parameter takes a type a term spells, so no function type: those
components are written out. A tuple's term may bind, a λ over an index,
and the chapter spelling folds it back where the binders are those
names and no parameter's argument mentions them.

A proof closure binds a bundle binder with ONE Fact parameter: a Fact
where no hypothesis is available binds the binders next in order up to
the hypothesis that mentions each of them — the structure fact at its
components — the binders fixed under their own names
(prover/proof/section_binding.go). A structure with a typed fact may
bind the bundle as that fact at the binder's letter instead (`L
field.FieldFact[on.L]`, §"The structure doors").

### Nat arithmetic

| Write | Means | Notes |
|-------|-------|-------|
| `m + n` | `+ : num → num → num` | left-associative |
| `m - n` | `-` (truncated subtraction) | left-associative |
| `m * n` | `*` | binds tighter than `+ -` |
| `m < n` | `<` | non-associative; same level as `=` |
| `m <= n` / `m ≤ n` | `≤` | |
| `m > n` / `m >= n` / `m ≥ n` | `>` / `≥` | |
| `m != n` / `m ≠ n` | `¬(m = n)` | desugars to negated equality |
| `0`, `1`, `42`, … | `bit0`/`bit1` over `_0` | decimal literal → bit-tree; `0` → `_0` |
| `suc(n)` | `suc : num → num` | well-known reserved const |
| `_0`, `bit0`, `bit1`, `suc` | numeric-encoding metas | reserved names — don't shadow with local vars |

A bare variable against a numeral literal always reads variable →
numeral in the equality rewriters (ext/prop `contextEq`): by raw size
a literal is the larger side (`1` is bit1(_0), two symbols), and the
bigger-side-on-LHS rule would read a resident `x = 1` as `1 → x`,
rewriting the literal — and the `1` inside `2`'s tower — into a
variable the arith closer cannot evaluate (`p = 1` beside `2 ≤ p`
becomes `bit0(p) ≤ p`). Compound terms keep the size rule,
towers included: the datatype door's tag reasoning rewrites `1` into
`suc(0)` inside a larger tag on purpose.

Precedence (low to high): `⇔ < ⇒ < ∨ < ∧ < relational (= < ≤ > ≥ ≠ ∈ ∉ ⊆ ⊊ ∣ ⟶) < ∪ ∖ < ∩ < + - < • < * / < ∘ < ¬ and prefix - < ^ < & < application`.

Quantifier type annotations remain mandatory: write `∀m:num. m + 0 = m`,
not `∀m. m + 0 = m`. Type inference doesn't propagate the nat type from
operator usage back to the binder.

### The other arith domains — one symbol, several instances

`+ - * < ≤ > ≥` are resolved by **operand type**, never by const name:
both operands num ⇒ the nat consts above, both real ⇒ `real_add`/…,
both int ⇒ `int_add`/…, and for `+ * ≤` also at the ℝ-construction
tower's three layers (`hreal`, `nadd`, `treal`). Each operator
dispatches on its own operands, so one statement may mix domains
(`hreal_of_num(m + n) ≤ x` is nat inside, hreal outside); only the two
operands of ONE operator have to agree, and genuinely mismatched
operands are rejected. The printer is the same map read backwards:
`real_add` renders as `+`, so print↔parse round-trips.

**Coverage is per symbol, and uneven — do not assume a symbol exists at
your domain.** Only `+ * ≤` reach all six; `- < > ≥` have three
instances (num, real, int) and no tower instance at all; `∣` is num and
int; `..` is num alone; `/` is real alone. `-` is num's truncated monus
and `real_sub`/`int_sub` (TOTAL) at real/int. A symbol with no instance
at the operand's domain is reported as
`operator X has no instance for operand type T` — a typed refusal, not
a parse error.

| Write | Means | Notes |
|-------|-------|-------|
| `&n`, `&m` | `real_of_num(…)` | the ℕ→ℝ coercion, tight prefix; `&0`/`&1` are the field literals. Inside a congruence's modulus slot it means int — see above |
| `&x` (x real) | `complex_of_real(x)` | the declared lift of the real line — a constant of type `real → τ` marked `Coercion: true` at its define door (one per τ); fires where τ is expected, where a partner is τ (`exp(i * &π) + &1 = &0` — the num under `&` lifts through the real line), and in a chapter that declared τ as its domain. A `&` in a slot the application's other arguments decide — a COND's branch — takes the default where it stands; where the other arguments do not fit that, it is read after them, at the type they give the slot, so `COND(c, &0, z)` and `COND(c, z, &0)` are one term at a z of τ, and a branch beside an int one is the integer. The chapter spelling writes the lift back as `&` where the position types it — a slot of τ, a slot an earlier argument pins, a partner of τ, the body of a λ at such a slot — and keeps `complex_of_real(…)` at a slot only a later argument pins |
| `&0`, `&n` (n num) | `extended_of_real(&0)` | a lift that embeds the nonnegative line alone, marked `NumeralCoercion: true` at its define door (extended_of_real into ⟦0, ∞⟧ sends a negative real to 0): `&` of a num lifts through the real line where τ is expected or a partner is τ (`μ(s) ≤ &0`, `f(i) = &0`); `&x` of a real is refused, and the chapter spelling folds the application back to `&n` at a num operand only — applied to a real it keeps its name, `extended_of_real(x)`. A constant declares `Coercion` or `NumeralCoercion`, not both |
| `-x` | `real_neg` / `int_neg` | unary; binary `-` at the same operand type is `real_sub` / `int_sub` |
| `x / y` | `real_div(x, y)` | **real only.** `*`'s level, left-associative, so `x / y * z` is `(x / y) * z` |

**An `&` that no operand anchors is read under the chapter's declared
domain, at every door.** `&0 < &n` has no operand that says ℝ or ℤ, so
what it embeds into is the chapter's to declare: a `CoerceDomain` row
of its vocabulary (`CoerceDomain(RealDomain)`), or, for a chapter with
no vocabulary of its own, the declaration on its family handle
(`registry.NewFamily(…).WithCoerceDomain(RealDomain)`) — once, in one
of the two. The declaration is read wherever a text of the chapter is:
a member's statement, a claim in its proof (`Have`, `Show`, `Obtain` —
whether or not the block has minted a name), a definition's equation,
and every text door of a SESSION bound to the family (`add-goal`,
`assert`, a lemma text, a parameter term, the `define` doors). An
anchor still wins (`x < &n` with `x:int` is ℤ in a chapter that
declared ℝ). A chapter may declare a domain some constant is the
coercion into (the complex chapters declare ℂ through
`complex_field.ComplexDomain`): there `&x` with `x:real` is the lift,
`&exp(x)` likewise, and a num under `&` is still read on the real line
— the chapter's literals stay real, and lift exactly where a complex
position or partner asks. Where nothing is declared — a chapter that declares none,
a session bound to no family — an unanchored `&` in a statement or a
claim is REFUSED, naming the repairs: declare the domain, anchor an
operand, or spell the embedding longhand (`real_of_num(n)`,
`int_of_num(n)`). So a claim reads the same in the session and in the
Go it is emitted as; a parameter TERM (`witness`, `a.Term`) is not
refused, and takes the declared domain or, with none, ℝ. `emit-section`
validates a rendered text under the same rule: one that would be
refused at the chapter's door is rendered as a Go expression instead.

**A relation between numerals alone is typed by the domain, and the
session says at which type.** `&2 ≠ &0`, `&1 + &1 = &2`, `&0 < &1`:
both sides are `&` numerals, or sums, differences, products and
negations of them, so nothing in the text names a type and the domain
decides. In a chapter that declared ℂ that is the real line, and the
claim is a fact about reals that closes nothing at ℂ; its echo cannot
show it, since a numeral prints the same at every type. A session step
that reads such a text — the claim of an `assert`, a lemma or premise
given by `text` — carries a `numeral_domain` diagnostic: the relation
and where it stands, the type it was read at, what decided it, and the
spelling that states it at the chapter's domain (`complex_of_real(&2) ≠
&0`: lift one side and the other follows). The text is read as it
stands and the step is not refused; `parse-prop` answers the same as a
warning with the code `numeral_domain`. A relation one side of which
names a type (`x ≠ &0`, `z = &1`) is not reported. A numeral in an
argument slot is not this diagnostic's: a slot of another type refuses
it by name.

**A λ applied in place stays a redex, and the session says what it
reduces to.** A text keeps the redex it spells: `(λx:real. &0)(x) ≤
g(x)` is that proposition, where an abbreviation of a λ, applied, reads
as its body at the argument. A law taken at a λ does not show one — its
instance is handed over reduced, `&0 ≤ g(x)` — so a claim written by
substituting the λ into the law's premise by hand states the premise
with a redex the instance does not have. A closer reads the two alike
and the plan key is one for both, but the redex stays in the member:
every later text, and what `emit-section` writes, spells it. An `assert`
whose claim applies a λ in place carries a `written_redex` diagnostic:
each such application, outermost first, with the term it reduces to,
`` `(λx. &0)(x)`, reduced `&0` ``. The claim is read as it stands and
the step is not refused; restate the claim reduced unless the redex is
what it is about.

**`/` is the one arith symbol with no num or int instance, deliberately.**
ℕ's truncated division and ℤ's Euclidean division keep an applied
spelling — the overloaded words `div(m, n)` and `rem(m, n)`, which the
operands' domain resolves to `nat_div` / `nat_mod` or `int_div` /
`int_rem`: giving `/` a second meaning at num or int would make one
symbol denote two different operations, and neither chapter has a `/`
notation to inherit. Every OTHER overloaded symbol is num-anchored,
which is why `isArithOperator` had to become a union over domains
rather than the num table alone. `real_inv` likewise has no notation:
write `real_inv(x)`.

### Divisibility and congruence

**A known integer position embeds natural values automatically.** With
`a k p:num`, `c.TermAs[Int]("a * k")` reads as
`int_of_num(a * k)`. An integer function slot, the body of
a lambda expected to return int, or an integer partner in arithmetic,
an equation, a comparison or divisibility supplies the same expectation:
`legendre_symbol(a, p)` embeds `a` and keeps `p` natural. Only num→int
is implicit; the ambient `CoerceDomain` alone does not promote bare nums.

Natural computations keep their operators: `c.TermAs[Int]("a - k")`
is `int_of_num(a - k)`, natural monus followed by the embedding. The
result expectation does not turn it into integer subtraction. An integer
operand selects integer arithmetic; `c.TermAs[Int]("&a - k")` reads
as `int_of_num(a) - int_of_num(k)`. Named natural-valued calls likewise
keep their argument domains and embed their result.
Overloaded words prefer the instance matching their arguments without
embeddings, so `rem(a * k, p)` still computes a natural remainder when
its result stands at int.

For an integer congruence one integer operand or `&` is enough:
`rem(a * k, p) ≡ a * k (mod &p)` reads as
`int_of_num(rem(a * k, p)) ≡ int_of_num(a * k) (mod int_of_num(p))`.
To retain the integer product of the embeddings as the exact kernel term,
write `rem(a * k, p) ≡ &a * k (mod &p)` instead.
With all three operands natural and no `&`, the relation remains `nat_cong`.

| Write | Means | Notes |
|-------|-------|-------|
| `d ∣ n` | `nat_divides(d, n)` at num / `int_divides` at int | U+2223 (NOT ASCII `\|`); dispatched by operand type; relational level; real rejected |
| `x ≡ y (mod m)` | `nat_cong(x, y, m)` at num / `int_cong(x, y, m)` at int | U+2261; the `(mod …)` clause is mandatory; relational level, non-associative |

**At num both infixes denote ℕ's OWN constants** (`proofs/nat_num/`),
defined inside ℕ and not through the `&` embedding. The printer matches:
`nat_divides` and `int_divides` render as `∣`, `nat_cong` and `int_cong`
as the mixfix.

The two domains lower to one shape: `nat_cong` and `int_cong` are both
three-place relations in the order the mixfix reads, so `x ≡ y (mod m)`
builds `nat_cong(x, y, m)` at num and `int_cong(x, y, m)` at int.

A `&` coercion operand always means int (num is impossible for a
coercion, real is not dispatched) — so the ℕ⇔ℤ transfer statement needs
no type annotations: `==(x, y, num_mod(n)) ⇔ &x ≡ &y (mod &n)` at
`x y n : num`. Converting a statement text between an infix and its
longhand moves no key, pb, or Skolem trajectory: the parse builds the
identical term. The general relation slot — `==(x, y, rel)` with `rel` a
variable, `num_mod`, or `real_mod` — keeps the application form in both
parse and print. `mod` is not a reserved word; only the two-token shape `( mod`
immediately after an operand is claimed (an application argument list
literally starting with a variable named `mod` would need renaming —
the corpus has no such identifier). The printer renders the mixfix on
every profile.

**Generated texts omit redundant integer embeddings.** The kernel
printers spell `int_of_num(n)` explicitly. `statement_typed` and
`emit-section` shorten that spelling only where parsing at the consumer's
scope recovers the same term, up to bound names. Thus `z = int_of_num(n)`
at `z:int` becomes `z = n`, and an emitted witness
`a.TermAs[Int]("int_of_num(n - k)")` becomes `a.TermAs[Int]("n - k")`.
Recorded payloads whose bound names matter require syntactic equality too.

A domain anchor stays where it is needed: the integer difference of
two embedded naturals is `a.TermAs[Int]("&n - k")`, while a polymorphic
first argument such as `fun_support(int_of_num(0), f)` can still require
the explicit integer zero. The check compares the terms themselves,
not their mathematical equivalence or a normalized statement key.
Authored headlines and definitions keep their authored text.

Displays without a typed read-back (including the index's display
spelling) use the chapter's syntactic fold: `int_of_num(n)` becomes `&n`
beside an integer partner or among a congruence's operands, and keeps
its explicit spelling where the fold has no integer anchor.

### Set theory

A set is its own membership predicate, `A → bool`, and the text spells
that type `set(A)` when the binder is a set: `∀s:set(A). x ∈ s`,
`∀T:set(set(A))` for a family of sets, `A → set(B)` for a set-valued
function, `set(A) → bool` for a property of sets. The alias is a
spelling, not a type — the parser lowers `set(τ)` to `τ → bool`, so
keys, matching and the printers never see it (the printers spell the
arrow; `∀s:set(A)` and `∀s:(A → bool)` are one key). It carries the
author's intent, and the parser holds the author to it: a binder
declared `set(…)` is never applied — `∀s:set(A). s(x)` is refused
(`set_applied`), and so is `∀t:(A → set(B)). t(x)(y)`. Write `x ∈ s`;
a predicate applied to points keeps the arrow, `∀P:(A → bool). P(x)`.
The corpus gate `TestSetSpellingLint` reports the converse — a binder
spelled `X → bool` that is never applied and stands under a set
operator. Every form below lowers to the `sets/set_basic` constant of
the same meaning (the table names it), so a statement written in the
surface builds the term the chapter's definitions state.

| Write | Means | Notes |
|-------|-------|-------|
| `x ∈ s` | `set_member(x, s)` | relational level, same as `=` / `<` |
| `x ∉ s` | `¬(x ∈ s)` | relational level; desugars to negated membership, as `≠` does to negated equality, and the printers write every `¬(x ∈ s)` this way |
| `s ⊆ t`, `s ⊊ t` | `subset` / `proper_subset` | relational level |
| `s ∪ t`, `s ∖ t` | `union` / `set_difference` | left-associative, tighter than relational |
| `s ∩ t` | `intersection` | left-associative, tighter than `∪` |
| `∅`, `𝕌` | `empty_set` / `universe` | nullary polymorphic atoms |
| `⋃f`, `⋂f` | `big_union` / `big_intersection` | unary prefix over a set of sets |
| `{a₁, …, aₙ}` | `insert(a₁, … insert(aₙ, ∅))` | enumeration; `{}` is `∅` |
| `{x \| φ}` / `{x:T \| φ}` | `set_comprehension(λv. ∃x. comprehension_spec(v, φ, x))` | set-builder, **identity form only** |
| `{t \| x₁, …, xₙ \| φ}` | `set_comprehension(λv. ∃x₁ … ∃xₙ. comprehension_spec(v, φ, t))` | set-builder, **general form** — three parts |

Binders may be annotated in either form (`{x:T \| φ}`, `{t:U \| x:T \| φ}`);
in the general form the head annotation `U` types the OUTPUT, and hence
the hidden set_comprehension λ-binder, rather than the witness.

**The set-builder has two forms and the two-part one is deliberately
narrow.** `{x | φ}` accepts only a bare identifier on the left. For an
arbitrary output term the binder list must be written out:
`{f(x) | x | x ∈ s}`, not `{f(x) | x ∈ s}` — the latter is a parse
error whose message carries the correction. The reason is
disambiguation: with an explicit binder list the bound-variable set,
order and names are surface-determined rather than guessed from the
output's free variables. `|` is never an operator (divisibility is
U+2223 `∣`; the magnitude's bars open a notation where an expression
begins), so a φ can never contain a top-level bar and the two forms
are told apart by probing for a second one.

A binder the text does not annotate takes its type from its first use,
so the fact that types it comes first: `{x | x ∈ s ∧ |x| < &1}`, the
membership before the word that needs x's type to pick its constant.
In the general form the output is built after the binders' uses in φ,
so `{ x + x | x | x ∈ s }` and `{ |w| | w | w ∈ s }` build with no
annotation; a binder named like a declared variable shadows it.

`∅` and `𝕌` are polymorphic and nullary: under a set infix or `=` the
partner operand fixes their instance (`x ∈ ∅` at x's type, `s ⊆ 𝕌` at
s's), and where no partner does — a statement naming one at two levels
at once, `⋃∅ = ∅`, or the family-level `∅` hidden inside `{s}`'s
insert-lowering — each occurrence is inferred on its own, not per name.

**Each set name is resolved on demand.** The parser surfaces the name a
surface form lowers to (`∈` and `∉` → `set_member`, `∅` → `empty_set`, `{a, b}` → `insert`,
`{x | φ}` → `set_comprehension`/`comprehension_spec`, `⋃` → `big_union`, …) to the caller's const
resolver exactly when the text uses that form, so a scope or resolver
carrying the chapter-minted definition wins and a statement with no set
notation never touches the set vocabulary at all; only a name nothing
supplied falls back to the DSL's own def-less surface meta (a scope-less
parse in tests or agent surfaces).

### Functions

| Write | Means | Notes |
|-------|-------|-------|
| `f ∘ g` | `o(f, g)` | composition, right-associative, one level tighter than `*` |

`∘` is U+2218 RING OPERATOR. It binds one level tighter than `*`; since
the operands are functions, on which no arithmetic operator has an
instance, the level resolves no genuine ambiguity.

**A bare `∘` builds a def-LESS surface meta unless the caller supplies
`o`.** The parser surfaces the name `"o"` to the caller's const resolver
whenever it sees the operator, so a scope or resolver that carries the
chapter's `o` (sets/functions) wins — but a scope-less parse falls back to the DSL's own
def-less meta, and `def_expand` then finds no definition to unfold. A
proof that unfolds a composition must therefore have `o` in its
ParseScope (`ctx.Const("o", …)`, whose meta comes from the corpus). The
"not seeded by name" rule above is about not SHADOWING a variable named
`o`; it is not a prohibition on declaring the const.

Applied to a point the sugar stays on the composition and the point
rides outside — `(f ∘ g)(x)`, never `o(f, g, x)`. That is not cosmetic:
`o` is one of the few consts the DSL declines to seed into scope by
name (a one-letter identifier is a plausible binder, unlike the all-caps
set vocabulary), so the applied spelling reparses to a free VARIABLE
wherever `o` is not declared, while `∘` builds the const in any scope.

### Pairs / tuples

| Write | Means | Notes |
|-------|-------|-------|
| `(a, b)` | pair `,(a, b) : prod(α, β)` | the pair constructor `,`; always in scope |
| `(a, b, c)` | `(a, (b, c))` | right-associative; nests for tuples |

`(a, b)` is the infix tuple form the printer emits (`nat_dist((m, n))`,
`snd((a, b))`). It round-trips — copy a printed pair straight into an
`assert` / `trans` / `witness` parameter. The legacy prefix spelling
`,(a, b)` is still accepted but no longer emitted.

### Lambdas

| Write | Means | Notes |
|-------|-------|-------|
| `λx:T. body` | single binder | type optional when inferable |
| `λ(x:T) (y:T). body` | `λx:T. λy:T. body` | paren-grouped currying; one typed binder per group |
| `λ(u:T₁, x:T₂). body` | pair-PATTERN lambda | see below |
| `λ((a:T, b:T), c:T). body` | nested pattern | pattern tree mirrors the pair nesting |
| `εx:T. body` | the Hilbert choice binder | `ε` is the binder only when a binder NAME follows it directly; a bare `ε` — `∀ε:real. &0 < ε ⇒ …`, `… < ε)`, the Skolem `ε₀` — is an ordinary identifier, so analysis writes its ε-δ with the letters it uses |

A pattern lambda lowers to the pattern_abstraction encoding
`pattern_abstraction(λf. ∀u x. f((u, x)) = body)` with a **fresh** internal binder `f`
(chosen to avoid every name in the body — a body referencing an outer
variable that happens to be named `f` is safe). Pattern components must
have distinct names. The printer renders canonical pattern_abstraction terms back in
this pattern form, so printed goals round-trip.

Same-name shadowing: when a term binds a variable whose name collides
with a *different-typed* outer variable free in its body (legal in the
kernel — variable identity is name+type), the printer renames the inner
binder to a fresh variant (`f` → `g`, …) so the text has one unambiguous
lexical reading. Copy printed text verbatim; don't "restore" such names.

### Quantifiers

Bound variables MUST have type annotations:

```
forall x:A. P(x)
exists x:A. exists y:B. R(x, y)
```

Quantifier body extends to the end of the expression. Use parentheses to limit scope:

```
(forall x:A. P(x)) => Q       # ∀ scopes over P(x) only
forall x:A. P(x) => Q         # ∀ scopes over entire P(x) ⇒ Q
```

### Types

```
bool                    # boolean
A, B, C                 # type variables (single uppercase letter) — canonical spelling
var:A, var:Repty        # var:-prefixed type variables; required for multi-letter names
A->B  or  A→B          # function type, right-associative
nat, num                # named types
prod(A, B)              # product type (the type of a pair `(a, b)`)
```

Bare single uppercase letters are the **canonical** type-variable
spelling. `var:X` remains accepted: for a single uppercase letter the
parser normalizes it at AST construction (`var:M` and `M` parse to the
identical statement, and the statement formatter outputs the bare `M`
form). Multi-letter type-variable names still **require** the prefix —
a bare multi-letter name (`Repty`) means a nullary named type, not a
type variable. Skolem type variables (`?94099`, printed as
`var:?94099`) are unaffected by the normalization.

**A member's statement pins every type letter of the constants it
names.** A statement that names a polymorphic constant and no term of
the letter's type — `group(permutation_group)`, `{permutation_identity}`
— leaves the parser nothing to read the instance from, and the statement
door refuses it, naming the constant and the letter: write the tie once
where the constant stands, `permutation_group⟨A:A⟩`. (Unrefused, such a
statement registered at the parser's own stand-in for the letter: its
key was not the pinned statement's, a typed `FixAs` at the family's
letter did not fit it, and the typed generator could not name a Go type
parameter after it.) A binder of the letter's type pins the constant as
any argument does, and so does the slot the constant stands in, where
its head fixes that slot's type (below).

**A constant's type letters are its own.** A polymorphic constant is
declared over letters of its own — composition's are `A`, `B`, `C` —
and a statement's type variables are the author's. At every text
door — a member's statement, `add-goal`, `assert`, a lemma text
(`lemma` / `lean_rw`, a text premise of `by` / `auto_with` /
`simp_with`), a tactic's term parameter (`witness`, `instantiate`,
`trans`, a `term_specialize` witness), the `parse-prop` and
`parse-term` previews, and in Go a proof body's claim and term texts
(`Have` / `Obtain` / `Show`, `a.Term` / `TermAs`), whether or not the
block has minted a surface name — the two never meet:
each occurrence of a constant is read with fresh letters,
instantiated from its arguments, its partner or its expected type (a
`term_specialize` witness's is the binder it grounds, a reading's
witness's the reading's binder) —
an instance the goal already holds pins nothing (`F ≠ ∅` resident at
set(set(A)) leaves the ∅ of `s = ∅` at s's type), and at a claim door
a letter none of them fixes is refused by name — so a statement over its own `A` may
hold the constant at an instance containing that `A` — `g ∘ f` with
`f g:((num → A) → (num → A))` — and renaming the statement's type
variables never changes what it states. A `⟨A:…⟩` tie still
addresses the constant's letters by their declared names.

The expected type is the slot the constant stands in, so a letter that
only the constant's RESULT mentions needs no tie where the slot fixes
it: `injective_on(s, fun_zero(z))` with `s : U → bool` reads
`fun_zero(z) : D → num` at `D = U` — the slot `U → B` and the argument
`D → num` are unified, each side's letters binding — and so does an
argument of a variable (`P(inject_num(3))` with
`P : (num → num → bool) → bool` puts inject_num's `A` at num) and the
receiver of a field, whose operands fix the record's carrier
(`free_module_record(R, 𝕌).add(f, f)` with `f : U → A` reads as
`mod_add(free_module_record(R, 𝕌), f, f)` does). A term door's
expected type is its slot as well: a tactic's term parameter or a Go
proof's `TermAs` text `fun_zero(z)` expected at `U → num` reads `D` at
`U`. Two sibling arguments at one letter, neither pinned, take the pin
a later argument makes: `fun_add(add, fun_zero(z), fun_zero(z), x)`
with `x : U` reads both at `D = U`. A slot the argument cannot take is
refused with its two types before the kernel sees the application. A
variable is never retyped at one of its occurrences: a binder its
first use left at a constant's letter
(`∀x. fun_zero(z, x) = z ∧ x ∈ s` with `s : U → bool`) is refused
where a later use reads it at another type — an argument, an operand
of `=` or of an operator alike, since rewriting that occurrence alone
would leave it free beside its binder — and is written with its type
at its binder, `∀x:U.`.

A CLAIM that leaves one of a constant's letters unpinned — no term of
the claim has that type, so nothing says at which type the constant is
read (`∅ = ∅`) — is refused where it is written, the session's `assert`
and a Go claim alike, with the edit that pins it (the letter written
on the constant, `∅⟨A:num⟩`), as a member's statement is. An ad-hoc
lemma text states a lemma, which may be polymorphic, and is not asked.

**An operator standing alone is its constant.** `+`, `*`, `<`, `>`,
`<=`, `>=`, `∧`, `∨`, `⇒`, `¬`, `∀` and `∃` written as a standalone
argument, a parenthesized value or the whole text — `monoidal_op(+)`,
`word_bitwise_binary(k, ∧, x, y)`, `word_bitwise_unary(n, ¬, x)`,
`op = (∧)`, a term text that is `+` — denote the constant of that
name (the nat operator, the connective, the quantifier), and an
operator before `(` heads a prefix call: `*(k)` is the partial
application `λn. k * n`, as the printer spells it. The printer spells
a bare operator so, and the engine reads its own spelling back where
a text is the operator alone: the component of a resident
`comm_monoid_on(𝕌, +, 0)`. Anywhere else an operator wants its
operands, so `x + + y` is still an error. `=`, `⇔` and `-` have no
bare spelling.

> **`(A, B)` in TYPE position ≠ a pair.** `(C, P) → B` is the *curried*
> two-arg function `C → P → B`, NOT `prod(C, P) → B`. The product *type*
> is written `prod(C, P)`. (In term/value position `(a, b)` IS a product
> pair — see Pairs above.)

### When you need type declarations

- Bound variables in quantifiers: type is in the binding (`x:A`), no declaration needed.
- Free variables used in function application: type is inferred from arity and context. `P:A→bool, P(x)` infers `x:A`.
- Equality partners: `x:A ⊢ x = y` infers `y:A` from the equality.
- Free variables with NO context: must declare. Error includes `suggested_types` with best guess.

---

## Output format

```json
{"result": "valid"}
```

```json
{"result": "invalid", "diagnostics": [
  {"type": "premise_partial", "message": "premise 0 applies but leaves residual: ⊢ P(b)",
   "repair_hints": [{"description": "need both conjuncts as premises"}]},
  {"type": "missing_premise", "message": "could not derive conclusion from given premises",
   "repair_hints": [{"description": "try expanding definition of COND"}]}
]}
```

```json
{"result": "unknown", "capability_hint": {"reason": "unsupported_domain", "domain": "arithmetic"}}
```

### Result values

- `"valid"` — proved
- `"invalid"` — confirmed invalid (positive evidence of invalidity, not just failure to prove)
- `"unknown"` — could not determine; check `capability_hint` for why

### Diagnostic types

| Type | Meaning |
|------|---------|
| `premise_partial` | Premise matched but left a residual (shows what's still needed) |
| `premise_no_match` | Premise didn't unify with goal |
| `missing_premise` | Summary diagnostic with repair hints (definition expansion, structural suggestions) |

### Parse error codes

| Code | Meaning |
|------|---------|
| `missing_type` | Variable has no type; check `suggestion` and `suggested_types` |
| `validation_error` | Type mismatch or semantic error |
| `parse_error` | Syntax error |
| `core_panic` | Internal error (likely type error in input) |

---

## Capability boundary

**Works** (BasicTactic + CNF refutation handles these):
- Propositional tautologies, De Morgan, distribution, contrapositive
- Implication chains, modus ponens with hypotheses
- Contradiction detection
- Universal instantiation
- Equality reasoning: transitivity, symmetry, Leibniz identity, group theory
- First-order with equality, unique existence
- Relation theory: symmetry + transitivity + totality
- Mixed quantifier reasoning (within CNF refutation power)
- Multi-hypothesis reasoning (`p, p => q, q => r |- r`)

**Works** (via the `arith` move — corpus-backed `ring` + `linarith` / `omega`):
- `num` polynomial equalities: additive AC, distribution, numeral folding
  (`2*3 = 6`), symbolic products incl. binomial `(a+b)² = a²+2ab+b²`
- ℚ-valid `num` linear comparisons: transitivity (`a≤b, b≤c ⊢ a≤c`),
  strict→non-strict (`a<b ⊢ a≤b`), antisymmetry (`a≤b, b≤a ⊢ a=b`)
- Coefficient-scaled linear goals (`a<b ⊢ 2a < 2b`) via the `ltScale`
  c≠0 discharge composed with the derived `mulB0`/`mulB1` numeral
  multiplication leaves
- Integer facts of `num` and `int` that turn on an equation, in one step and
  without naming the quotient: a bound from parity or from a residue
  (`nat_odd(n), 1 < n ⊢ 3 ≤ n`; `nat_mod(n, 3) = 2, 2 < n ⊢ 5 ≤ n`;
  `3 ≤ n ⊢ 1 ≤ nat_div(n, 2)`; `int_rem(n, &2) = &1, &1 < n ⊢ &3 ≤ n`), and
  the same with the quotient a variable (`n = 2 * q + 1, 1 < n ⊢ 3 ≤ n`;
  `n = 2 * q, n = 2 * p + 1 ⊢ ⊥`). The divisor is a literal or shown
  nonzero. A statement that needs a case analysis on a residue
  (`nat_mod(n * n, 4) = 0 ∨ nat_mod(n * n, 4) = 1`) is still written as
  cases

### Representative examples (capability ground-truth)

Concrete one-liners distilled from `prover/solver/refuter/refute_test.go` — the
engine's own tests, so this is authoritative, not aspirational. "Refutable"
= bare `auto` closes it (the CNF refuter is what does the work, via
`auto`'s pipeline; there is no separate agent-facing `refute` tactic).
To check whether a *new* goal is in scope,
copy the nearest shape into a 10-line probe (the test file is the template;
the `/prove` skill's rule 3 asks for this probe before a capability claim is
reported). Lesson up front: **scope is
logical validity, not surface shape** — see the contrast pairs at the bottom.

**Refutable — these CLOSE:**
- Group theory — `∀x y z. P(x,P(y,z))=P(P(x,y),z), ∀x. P(1,x)=x, ∀x. P(i(x),x)=1 ⊢ ∀x. P(x,i(x))=1` (equality + paramodulation + ∀-instantiation)
- Relation theory — `∀x y. R(x,y)⇒P(x,y), ∀x y. P(x,y)⇒P(y,x) ⊢ (∀x y. R(x,y)∨R(y,x)) ⇒ ∀x y. P(x,y)`
- Saturation disjunction — `[P,R transitive; R symmetric; ∀x y. P(x,y)∨R(x,y)] ⊢ (∀x y. P(x,y)) ∨ (∀x y. R(x,y))`
- Relation defined by ∃ — `[Q assoc + comm; ∀x y. R(x,y)⇔∃z. y=Q(z,x)] ⊢ ∀x y z. R(x,y)⇒R(x,Q(z,y))`
- Choice / ε-witness — `∀x. P(x, εa. (x=x₀⇒a=y₀)∧(x≠x₀⇒a=f(x))) ⊢ ∃f. f(x₀)=y₀ ∧ ∀x. P(x,f(x))`
- Cantor / Russell diagonal — `⊢ ¬∃x S. ∀u. (S(x,u) ⇔ ¬S(u,u))`
- Boolean-quantifier expansion — `⊢ (∀x:bool. R(x)) ⇔ (R(⊤) ∧ R(⊥))`  and  `⊢ (∃x:bool. R(x)) ⇔ (R(⊤) ∨ R(⊥))`
- First-order unsat with a function symbol — `∀u. R(u)∨R(f(u)), ∀v w. ¬R(v)∨R(f(w)), ∀x. ¬R(x)∨¬R(f(x)) ⊢ ⊥`
- Mixed-quantifier ∃-witness — `∃x. P(x) ⊢ ∃x. P(x) ∧ (D(x) ⇒ ∀y. P(y)⇒D(y))`
- Unique-characterization iff — `⊢ (∃x ∀y. P(y)⇔(x=y)) ⇔ ((∃x. P(x)) ∧ ∀x y. P(x)∧P(y)⇒x=y)`
- Inductive/impredicative bootstrap with quantifier alternation + λ-defined predicate — the `num` definition `num = λa. ∀f. (∀a. ((a=0)∨∃i. a=Suc(i)∧f(i)) ⇒ f(a)) ⇒ f(a)` and its monotonicity/closure obligations are refutable (forms too large to inline — see `refute_test.go` `TestProve4`).

**NOT refutable — these correctly stay open (don't expect `auto` to close them):**
- `⊢ ∀x. x = y` (invalid)
- `x≠z, y≠z ⊢ x=y` (invalid — nothing forces it)
- `⊢ (∀x. ∃y. P(x,y)) ⇒ (∃y. ∀x. P(x,y))` (quantifier flip, invalid)
- `⊢ ∃!z. (S(x,z) ⇔ S(z,z))` — synthesizing a *bare* unique-existence GOAL does not close. (Uniqueness *reasoning* from ∃! hyps, or via the `∀a b. P(a)∧P(b)⇒a=b` clause, DOES — that's the "unique existence" listed under **Works**. The distinction: ∃! as available premise/clause = fine; ∃! as a goal to invent the witness for = no. With the witness in hand, give it: `witness` (Go `a.Take(t)`) on an ∃! goal leaves `P(t) ∧ (∀y. P(y) ⇒ y = t)`.)
- **Contrast pairs (shape identical, validity differs — the refuter tracks validity):**
  - `P(x) ⇔ ∃y. (x=y ∧ P(y))` CLOSES, but `P(x) ⇔ ∃y. (x=y ⇒ P(y))` does NOT.
  - `P(x) ⇔ ∀y. (x=y ⇒ P(y))` CLOSES, but `P(x) ⇔ ∀y. (x=y ∧ P(y))` does NOT.

When `auto` fails on a goal whose shape matches a **Refutable** row above, the
problem is almost certainly navigation (the goal isn't yet in that clean
first-order form — load the lemmas / decompose with `congr`/`funext`/
`strip_quant`/`case_split` first), NOT a missing engine capability.

**Works with session API**:
- Boolean case split: split a goal on any boolean term `b` → two branches (b true / b false). Use via `apply` with `{"tactic":{"type":"case_split","const":"b"}}`.
- Structural induction on a variable of any registered inductive type — `num` (base `P(_0)`, step `P(n) ⊢ P(suc(n))`), `list(A)` (base `P(nil)`, step `P(t) ⊢ P(cons(h, t))`), `option(A)` (`none`, `some x`). Surfaced via `inspect`'s `structural_facts` (kind=`induction`) AND the recommendation list — eligible vars from every registered type are enumerated, not just num. Invoke directly with `{"tactic":{"type":"induction","const":"<var>"}}`; subgoal count follows the type's induction principle. The tactic accepts a var name from a ∀-headed goal or an in-scope Skolem; it does NOT need the caller to peel outer ∀'s first.
- Boolean case split (`case_split`) and induction both produce subgoals the agent works on independently via `inspect` → `probe` → `apply`.

**Available tactics** (for `apply`, `probe`, and `batch-apply`):

*Closing moves* — search + verification under the hood. Pick a candidate
via `retrieve` (its corpus group), confirm cheaply with `probe`, then
commit with `apply`.

| Tactic | What it does | Parameters |
|--------|-------------|------------|
| `auto` | Full automated proof. **Entry below: `auto`.** | none |
| `set_tac` | The set closer, recorded as ONE first-class ministep. **Entry below: `set_tac`.** | none |
| `simp_with` | The simplifier, recorded as ONE first-class ministep. **Entry below: `simp_with`.** | see the entry |
| `simp_all` | **Lean's `simp_all`** without the hypotheses as rules of each other: the installed simp set — the bound families' definitions and the theorems their chapters marked `Simp` — plus any `with_lemmas` rewrites the conclusion and every hypothesis in place, one target per round to a fixpoint across the targets. Progress-or-fail. Each round records one `simp_with` ministep, so `emit-section` renders the rounds as the `Simp` / `fact.Simp` steps they are; a resident equation that should rewrite the others is `rw`, or a `simp_with` rule by its index — a `{hyp_index}` rule is refused here, where every hypothesis, that one among them, is a target. |
| `auto_with` | Scoped lemma + focused-auto + close-or-fail. **Entry below: `auto_with`.** | `with_lemmas: [{key:str, text:str, type_specialize:{…}, term_specialize:{…}}, …]` (each entry: an entry's `key` OR DSL `text`, optional per-entry `type_specialize`, optional per-entry `term_specialize`); optional `keep_hyp_indices: [int,…]` (exclusive with drop); optional `drop_hyp_indices: [int,…]` (exclusive with keep) |
| `by` | The math layer's premise-disciplined close (`By`/`ByArith`) as a session move — `auto_with`'s DECLARED sibling. **Entry below: `by`.** | see the entry |
| `by_induction` | Go's `ByInduction` as a session move. **Entry below: `by_induction`.** | see the entry |
| `type_inst` | **A polymorphic entry read AT a type instance.** Closes the focused goal when it is a type instantiation of the entry's statement — σ is recovered from the goal itself (`_TypeInstStep`'s match tiers: raw structural, normalized-source-vs-raw-goal, normalized-vs-normalized), so no type map is supplied. This is the tactic that discharges the foreign-instance obligation a polymorphic `lemma` install leaves open (the `pairs.PairEta`-at-`prod(B,C)` class: every `lemma` route declines, the leaf IS the entry at another instance). Records a `type_inst` ministep against the polymorphic source with the entry stamped, so dep extraction resolves it directly. Close-or-fail: a goal that is not an instance of the entry fails with a diagnostic naming both. | `lemma_key: str` (the polymorphic entry; required — text lemmas carry no certificate) |
| `ac_regroup` | **The AC kit's goal face as a session move** (`proof.ACRegroup` / `ACRegroupWith`). The focused goal must be the bare equation `lhs = rhs` between two ⊕-sums over one leaf multiset — strip the binders first (`strip_quant`); the kit derives the rearrangement certificate from the assoc/sym pair (kernel Refl/Apply/EqSym/EqTrans composition, no CNF refute, no search) and closes the goal with it (recorded `known_thm` against the derived cert), or — when the goal is not itself the regroup equation — installs it as a resident hypothesis for a downstream refute. `assoc` / `sym` name the entries of the ⊕ associativity (`∀m n p. (m⊕n)⊕p = m⊕(n⊕p)`, either orientation) and commutativity (`∀m n. m⊕n = n⊕m`) laws over the SAME op, which the kit reads off the assoc statement; their rows back the derivation as forceable promises. This is the leg a flat cite cannot close. | `assoc: str`, `sym: str` (registry entries: registered names or own keys) |
| `expand` | Structural decomposition + leaf cleanup. Does NOT attempt refutation. | none |
| `lemma` | Apply a lemma to the goal. **Entry below: `lemma`.** | see the entry |
| `apply_search` | **Lean's `exact?`**: the corpus searched for a member that CLOSES the goal — a member whose statement is the goal (exact, by key) or one that applies to it by the apply rung's reading (the `retrieve goal` ranking) — each candidate tried as a `lemma` on a clone of its own, and the first that closes committed as that `lemma` step, so the record and the replay see a cite and nothing of the search; the rest are reported. A candidate that only rewrites or installs is passed over. The corpus scan takes 3 s (`budget_ms` when shorter). Fails naming the candidates tried; `retrieve` lists the members that apply with their open premises when nothing closes outright. |
| `cite-node` | Session-internal lemma reuse. **Entry below: `cite-node`.** | `node_id`: closed sub-derivation id from `inspect.closed_subtrees[].node_id`, format `s<N>_c<hash>` (the `c` prefix distinguishes from open `g` leaves); cross-session, pass the id reported by the session that proved it |
| `def_expand` | Expand a definition — without `hyp_index`, in the goal and every resident hypothesis, renumbering them, as Go's `Unfold` does (the goal alone is `simp_with` by the definition entry). **Entry below: `def_expand`.** | `const`: constant name; optional `hyp_index: int` — open the constant in THAT hypothesis alone, the unfolded statement joining the hypotheses (the Go `a.Unfolded(fact, <the definition>)`) |
| `known` | Close if the goal is an already-known fact: (1) proved in the theorem cache, (2) a proved section of this session or a registry entry stating it (by normalized key; the session's own target excluded), or (3) **a constant's own defining equation** `∀x⃗. c(x⃗) = f(x⃗)` — e.g. the point-free head `c = f` left after `congr`/`funext` reduces a pointwise def-equation. Case (3) is what closes a specification-minted or Hilbert-ε const's defining equation (which `def_expand` never surfaces — it yields only the property `P(c)`); it records as `AxiomDef`. The `def_eq` structural fact (see `inspect`) names these equations. | none |
| `induction` | Structural induction on a variable of an inductive type. **Entry below: `induction`.** | `const`: variable name (typed per the goal — e.g. `"n"` for num, `"l"` for list), as the goal prints it or its surface name (`"k"` for `k₀`) |
| `assert` | Introduce a hyp-free boolean claim φ as an intermediate sub-claim. Produces **2 subgoals**: the claim `Γ ⊢ φ` (you discharge φ on the next move) and the residual `Γ, φ ⊢ G` (the original goal with φ added as a new hypothesis). In `produced` the claim is the goal whose `changes` read `hyps_added: 0, conclusion_changed: true` and the residual the one with `hyps_added: 1` — tell the two apart by `changes`, not by position. **No registry entry closes the claim**: even if φ exactly matches an entry's statement, you still get the 2-child split — chain `assert(φ) → lemma(φ)` (or `assert(φ) → auto`) when you want both. A claim that a PROVED SECTION of the session states is closed at once by that section (the session matches an open leaf to a proved sibling section), and `produced` then holds the residual alone. Distinct from `case_split` (which adds `¬φ` on a second branch — `assert` is single-direction). Use to thread an inline lemma into a proof chain: when the bridge term you need isn't a subterm of the current goal, assert the bridge equation, prove it under the current hyps, then keep going. The claim's free variables must already be in scope (declared in `Γ` or introduced by a prior `strip_quant` / `induction`). A claim that applies a λ in place is asserted with the redex in it and answers a `written_redex` diagnostic (below, "A λ applied in place stays a redex"). | `claim`: PropInput — `{"text": "..."}` (ad-hoc DSL); must resolve to a hyp-free Prop |

*Structural moves* — parameterless shape decompositions; applicability is
a deterministic syntactic check. `inspect` lists which ones fit the
focused goal under `structural_facts` (no ranking, no confidence — which
axis to peel is the agent's planning decision).

| Tactic | What it does | Triggers when |
|--------|-------------|---------------|
| `strip_imp` | ⊢ A⇒B → A ⊢ B | concl is A ⇒ B |
| `split_conj` | ⊢ A∧B → ⊢ A and ⊢ B — at the outermost ∧, and ∧ is left-associative: `A ∧ B ∧ C ∧ D` splits into `A ∧ B ∧ C` and `D`. With `hyp_index`, the HYPOTHESIS at that index instead: `A ∧ B ∧ C ⊢ G` → `A ∧ B ∧ C, A, B, C ⊢ G`, every flat conjunct of its spine, the conjunction kept, the conclusion untouched — the session twin of the Go verb `a.Conjuncts(fact, …)`, recorded as the verb records it (one assert per conjunct, in order, each closed by `By(Normalized, fact)`) and emitted as `parts := a.Conjuncts(<fact>, "<label>"…)`, one label per conjunct, a later use of a conjunct `parts[k]`. Refused, naming the conjunct: one that is the goal's conclusion (close with `by` on the fact), as the verb refuses it; one already resident (use it, and `assert` the rest) and one that repeats an earlier conjunct, which the verb binds to the hypothesis that states it and this record, one assert per conjunct, has no step for; a hypothesis that is no conjunction fails cleanly (`split_conj hyp_index 2 (…) is not A ∧ B`). A hypothesis that is a membership in a set-builder of a conjunction is split through its predicate: `f ∈ {g | P(g) ∧ Q(g) ∧ R(g)}` gives `P(f)`, `Q(f)`, `R(f)` (the set-builder reading, §"Structural moves at a hypothesis"), and the refusal of one whose reading is no conjunction names the reading (`… is not A ∧ B, nor is its reading P(f)`). | concl is A ∧ B; optional `hyp_index: int` |
| `split_conj_all` | ⊢ A∧B∧…∧Z → ⊢ A, ⊢ B, …, ⊢ Z (N flat subgoals, one step) | concl flattens to ≥3 ∧-conjuncts |
| `split_disj` | A∨B ⊢ C → A ⊢ C and B ⊢ C. Optional `hyp_index` targets a specific ∨-hyp when several are resident (`split_disj({"hyp_index":15})` splits hyp 15, not the first ∨-hyp the engine scans to), or a membership in a set-builder whose predicate is a disjunction (`x ∈ {y | P(y) ∨ K(y)}` into `P(x)` and `K(x)`). Absent → pick the first — the pre-fix behavior every existing corpus record was built under. | a hypothesis is A ∨ B; optional `hyp_index: int` |
| `split_iff` | ⊢ A⇔B → `[0] B ⊢ A` (the ⇐ direction FIRST), then `[1] A ⊢ B` — read `produced`, not the statement's order. Declines where one half subsumes the other and the two merge into one (`L ⊢ L ⇔ ⊥`): simplify instead. | concl is A ⇔ B |
| `split_hyp_iff` | A⇔B ⊢ C → A,B ⊢ C and ¬A,¬B ⊢ C. Optional `hyp_index` targets a specific ⇔-hyp (same semantics as `split_disj`'s `hyp_index`). Declines where one branch subsumes the other and the two merge into one (`p ⇔ q, p, q ⊢ C`); without `hyp_index` such a hypothesis is passed over for the next ⇔-hyp, as one with α-equal sides is. | a hypothesis is A ⇔ B; optional `hyp_index: int` |
| `split_hyp_imply` | A⇒B ⊢ C → ¬A ⊢ C and B ⊢ C. A hypothesis `A ⇒ ¬A` says `¬A`, the two cases being one: the one subgoal ¬A ⊢ C. Optional `hyp_index` targets a specific ⇒-hyp (same semantics as `split_disj`'s `hyp_index`). | a hypothesis is A ⇒ B; optional `hyp_index: int` |
| `cond_rewrite` | Expand COND terms (elim at bool level, swap outward at non-bool) | goal contains COND(c,a,b) |
| `case_split` | Boolean case split on any bool term — two branches, ordered by the term under one leading ¬ (the term itself where it has none): child 0 holds that term as a hyp and child 1 its negation, so `case_split` on `¬p` gives `[0] p ⊢ …`, `[1] ¬p ⊢ …`. The term need NOT be a subterm of the current goal; reconstruction goes through `ExcludedMiddle(t)`, so any well-typed bool is sound. Use to introduce a fresh discriminant (`p = 0`, `q1 ≤ q2`, …) the goal doesn't already mention. Both branches arrive as the split makes them — the `¬t` branch is NOT pre-simplified — the record the chapter verb `a.Cases` makes; a shaping you want is your own `simplify` step. | `const`: bool term — subterm in scope or novel term parsed via text DSL (see "Parameter terms" below) |
| `strip_quant` | Strip EVERY leading ∀ from the conclusion — the whole prefix in one apply (`∀f. ∀l. …` leaves `f₀, l₀`; the Go `StripQuant()` twin peels the same prefix) — or, when the conclusion is not ∀-headed, Skolemize the first ∃-hypothesis. One apply does ONE of the two, the conclusion first. Optional `hyp_index` names the ∃-hypothesis to open (`strip_quant({"hyp_index":3})`): that hypothesis alone is Skolemized and the conclusion is left as it stands, ∀-headed or not — the session twin of the Go verb `a.Unpack`, recorded and emitted as `StripQuantAt(3)`. A membership in a set-builder whose reading is an ∃ is Skolemized through it: `x ∈ {y | ∃z. R(y, z)}` to `R(x, z₀)`, the three-part `x ∈ {f(k) | k | P(k)}` to `P(k₀) ∧ x = f(k₀)`. Absent → the pick-first form above. An out-of-range index, or a hypothesis at that index that is not ∃-headed, fails cleanly (`"strip_quant hyp_index 3 (…) is not ∃x. …"`) rather than opening a different hypothesis. An inner binder an author means to keep must be kept by not stripping: there is no single-binder session verb. | concl is ∀x. … or hyp is ∃x. …; optional `hyp_index: int` |
| `witness` | ⊢ ∃x. P(x) → ⊢ P(t). Consumes the ∃. On ⊢ ∃!x. P(x) it is the introduction of unique existence: → ⊢ P(t) ∧ (∀y. P(y) ⇒ y = t), the body at the witness and that the body holds of nothing else (one `split_conj`-able goal; the step is a kernel derivation and writes no refutation record). | `const`: witness term — subterm in scope or novel term parsed via text DSL (see "Parameter terms" below) |
| `instantiate` | Ground the ∀-hyp at `hyp_index` (required — use `inspect` to locate it). **Entry below: `instantiate`.** | `hyp_index: int` (**required**) + one of: `terms: ["<term_text>", …]` (multi-witness) OR `const: "<term_text>"` (single-witness); optional `keep: bool` |
| `ematch` | **E-matching ground pre-instantiation** of ALL resident ∀-hyps at once — the mechanized iter-#70 grounding ladder. For each ∀-hyp, extracts trigger patterns (const-headed atoms mentioning the binders), matches them against the goal's GROUND subterms (skeleton-indexed, deterministic one-way HO matching incl. λ-predicate synthesis for comprehension arguments), and applies ALL resulting ground instantiations as ONE composite `specialize` ministep (sources kept; the recorded step carries the plans as data — hyp index + witness tuple per entry — so replay is independent of the trigger heuristics). Three levels per hyp: whole-atom triggers → subterm triggers with type-filled completion → first-binder type fallback (the case of `pairs.PairSurjective`). Prefix-partial σ supported (grounds the predicate P of a pair-comprehension membership law while its pair coordinates stay ∀). Bounded (≤8 instances/hyp, ≤32 total) and deterministic. Fails with a clean message when nothing NEW can be grounded. **Intended flow**: `lemma…` (pin instances via `type_specialize`/`term_specialize` where the goal needs a non-default type instance) → `ematch` → `clear` the wide originals → `auto`/`split_iff`+`auto`. The tactic only ADDS hyps; it never closes a goal by itself. | none |
| `assumption` | Close goal when concl α-equals some hypothesis. | none |
| `refl` | Close goal when concl is `t = t`. | none |
| `basic` | The chapter verb `Basic()` as a session move: the propositional rewrites alone. Closes a `⊤` conclusion — what a `rw` or a `simp_with` leaves open when its result is reflexive, where `refl` refuses, the conclusion being `⊤` and no longer an equation — a reflexive equation, and a conclusion that is a hypothesis; any other goal is left as those rewrites leave it. Recorded as the `Basic()` step, so the emitted ladder ends `…, Basic()` as a chapter writes it. | none |
| `left` | ⊢ A∨B → ⊢ A | concl is A ∨ B |
| `right` | ⊢ A∨B → ⊢ B | concl is A ∨ B |
| `funext` | ⊢ f = g → ⊢ ∀x. f(x) = g(x) (function extensionality), every equation between functions in the conclusion at once — a conjunct, or one under a binder, as the one at the top — and through EVERY arrow of the sides' type: functions whose values are sets, `s r:(set(A) → set(prod(A, A)))`, go to `∀ẋ ẋʹ. s(ẋ, ẋʹ) ⇔ r(ẋ, ẋʹ)` — the point and the member in one step, which is what the Go `Funext()` does too (one tactic, `tactic.FunextTactic`, no depth). The one-argument form `∀q. s(q) = r(q)` is stated as a Have and the equation closed from it by `by` (spec_functor.SpecIdentity lands it so). **It is function extensionality, and not the move for an equation between SETS.** A set and a predicate are one type to the kernel, so `funext` leaves both as applications: `P(ẋ) ⇔ Q(ẋ)` is what a predicate's laws read, and `S(ẋ) ⇔ T(ẋ)` is not what a set's read — they speak `x ∈ S`, and to the plain `by` `S(x)` and `x ∈ S` are two atoms (`S ⊆ T ∧ T ⊆ S ⊢ ∀ẋ. S(ẋ) ⇔ T(ẋ)` with SubsetDef runs to its budget; only `settac` unfolds `∈`). Open an equation between sets by `simp_with` with `set_basic.Extension`, which leaves `∀x. x ∈ S ⇔ x ∈ T`, or prove its two inclusions (`set_order.SubsetAntisym`). After a `funext` a set-builder side is left applied to the point, `{p \| φ}(ẋ)`, printed with the builder's machine names, a form the hypothesis moves do not read as a membership (`split_conj`, `split_disj` and the ∃ strip at a hypothesis refuse it, naming it and the rewrite); the step's answer carries a `set_equation` diagnostic that says so. Where the `funext` stays, assert what the membership says and close that by `by {settac:true}` over the hypothesis. | concl holds an equation `f = g` with function-typed sides |
| `symm` | ⊢ a = b → ⊢ b = a | concl is `a = b` with `a ≢ b` |
| `congr` | ⊢ s = t → one subgoal per differing argument (TermDiff first; falls back to spine decomposition, one congruence per application) | concl is `s = t` with `s ≢ t` |
| `congr_arg` | **Forward** congruence on an equality hyp: hyp `(a = b)` at `hyp_index` + a function `f` → adds the hyp `f(a) = f(b)` (original equality kept). The hyp-directed counterpart of `congr` (Lean `congrArg`). Use to push an equality hyp through a function symbol without hand-priming `auto` via repeated `instantiate`. | `hyp_index: int` (the equality hyp), `const`: function term `f` (named const or λ, parsed via text DSL; its domain must match the equality's side type) |
| `congr_fun` | Dual of `congr_arg`: function-equality hyp `(f = g)` at `hyp_index` + an argument `x` → adds the hyp `f(x) = g(x)` (Lean `congrFun`). | `hyp_index: int` (the function-equality hyp), `const`: argument term `x` (its type must match the function domain) |
| `by_contra` | ⊢ G → ¬G ⊢ ⊥ (proof by contradiction). **Not enumerated** by `inspect` — the shape predicate would fire on essentially every non-⊥ goal. | concl is not already `⊥` |
| `subst` | Substitute using equality hypothesis at `hyp_index`. Single-target (rewrites only the FIRST hyp-or-conclusion the rule touches), auto-oriented (bigger side → smaller side) and size-monotone. For "rewrite everywhere, in the direction I chose", use `rw`. A size-guard refusal ("had no effect (no rewrite reduced the goal size)") on an equality hypothesis names `rw` on that hypothesis as its FIRST repair hint — the size-guard-free sibling, which `inspect`'s `structural_facts` lists for every equality hyp. | (parameterized: agent supplies `hyp_index: int`) |
| `rw` | Directed equality-hyp rewrite to fixpoint. **Entry below: `rw`.** | `hyp_index: int` (**required**, the equality hyp), `flip: bool` (optional, default false — rewrite right-to-left instead) |
| `clear` | Drop hyp(s) from the goal — weakening, producing the single subgoal `Γ\{dropped} ⊢ G`. Unconditionally sound (a proof under fewer assumptions is stronger). Reliability fallback (not a default): when `auto` stalls on resident wide multi-quantifier ∀-lemmas the goal doesn't need, drop them so the CNF refuter — which has no set-of-support gate — doesn't burn its ~5s ceiling on resolutions that never touch the goal (refute-poisoning). `hyp_indices` is its only hyp param (a single drop is `[i]`): drops the whole set in ONE apply — all indices read off the goal as you currently see it (no shift compensation); validated all-or-nothing (duplicate / out-of-range → typed error, nothing dropped); always records one `clear_hyps` ministep. | `hyp_indices: [int,…]` (**required**; single drop is `[i]`) |
| `trans` | ⊢ a = c → ⊢ a = b and ⊢ b = c | `const`: middle term — subterm in scope or novel term parsed via text DSL (typical use: build an arithmetic bridge like `m * suc(n + p)` that isn't visible as a goal subterm) |
| `intro` | Smart dispatch: ⇒ → `strip_imp`, ∀ → `strip_quant`. The committed ministep is the canonical name (`strip_imp` / `strip_quant`). | concl is `A ⇒ B` or `∀x. P` |
| `lean_rw` | LEAN-style equational rewrite. **Entry below: `lean_rw`.** | the lemma's conclusion (after stripping outer ∀) is `=` or `⇔`; optional `term_specialize: {"<binder_name>": "<witness_text>", …}`; optional `type_specialize: {"<typevar_name>": "<type_expr>", …}` |
| `arith` | THE unified num-arithmetic move. **Entry below: `arith`.** | the goal contains some num arithmetic content (a `+`/`*` subterm or a comparison atom, anywhere) |
| `ring_nf` | **The ring normal form as a REWRITE** — Lean's `ring_nf` beside the closer in `arith`: every arithmetic subterm of the conclusion and of each hypothesis (num, int, real) is rewritten to the sum of monomials the ring normalizer reads — each a numeral coefficient times a sorted product of atoms, the constant last, a unit coefficient and a zero constant elided — so two spellings of one polynomial meet as one term for every step that follows, the refuter and a cited law included (`(b + a) * 2 ≤ c` is `2 * a + 2 * b ≤ c`; `(x + y) * (x + y)` is `x * x + 2 * (x * y) + y * y`). Subtraction and negation stay atoms; a power with a literal exponent is read as its monomial. Shape-gated on arithmetic content, progress-or-fail, deterministic (replay re-runs it; no CNF key); the Go face is `RingNf()`. |

`case_split`, `witness`, `instantiate`, `subst`, `rw`, and `trans` are
structural in spirit but take a parameter; `inspect` surfaces them
under `structural_facts` when their shape predicate fires (any bool
subterm for `case_split` — enumeration only, NOT an applicability
constraint: `case_split` accepts any bool term, including ones not in
the goal; the enumeration just suggests the in-goal candidates the
agent is most likely to want, top-level concl-∃ or ∃! for `witness`, any
∀-headed hyp for `instantiate` — one fact per ∀-hyp, each carrying its
`hyp_index`, any equality hyp for `subst` and `rw` — probe-verified,
the `rw` fact also carries the `flip` direction that applies — any
equality conclusion for `trans`). Bool subterms whose head is a logical
connective (∧/∨/⇒/⇔/¬) are filtered from the `case_split` enumeration
— splitting on them is strictly worse than the dedicated move
(`split_conj` etc.); the dedicated move appears in the same
`structural_facts` list when applicable.

### Tactic entries

The tactics whose contract does not fit a table row. The row above
names its entry; an entry opens with what the tactic is and gives its
wire shape, what it leaves, what it records and what it refuses.

#### `auto`

Full automated proof. This is the ONLY agent-facing tactic that runs the CNF
refuter; there is no separate `refute`, and **`cnf_refute` is not a session
tactic either** — it is the spelling of the Go Action (`CnfRefute()`), and
both names are rejected with an error naming `auto`. The rejection is
deliberately not an alias: `auto` also runs the arith fast-path, which the
target's scope gates — a target the arithmetic bundle is built on (any
member of `nat_arith`, `nat_order`; the bundle's foundation is computed, nothing
is declared) refuses it and `auto` falls through to its non-arith stages or
declines. Dispatch-layer fast-path: runs the unified `arith` composite
(simplify-or-decide) on the whole goal first; if it closes, you're done. If
it doesn't close (or doesn't apply), `auto` falls through to `AutoExpand`:
CondRewrite → BasicTactic (with close-checks — h⊢h, h+¬h⊢⊥ via AlphaEquals,
trivial-⊤ collapse) → AutoDenote ×2 → BasicTactic → per-leaf CNF refutation.
Every preprocessing stage is an equivalence (no-hurt).

Pure num-arith goals close in ~ms without paying the CNFRefute cost;
matched-atom / trivial-⊤ goals close in the BasicTactic pass without paying
CNF either; non-arith goals pay an O(1) shape gate on the way in. The arith
fast-path lives at the engine dispatch layer (NOT inside AutoExpand's
pipeline) so corpus Build_X replay — which goes through CloseByAuto →
AutoExpand directly — never invokes it; that avoids the deadlock hazard
where a Build_X's auto step's leaf could re-force a bundle promise the
current Build_X is already forcing.

**Hard ~5s ceiling on CNFRefute**: the CNF refuter reliably finds
refutations within ~5s; past that the search is in a hopeless branch. A
larger `budget_ms` is *clamped* to the ceiling (`MaxEffectiveCnfTimeoutMs`),
so escalating it genuinely cannot change the answer. An `auto` that fails
is final; one cut off at the ceiling where you expect a close is run again
at the default budget, never with a larger one, and one cut off on every
run is final too (Lesson 4b); then switch tactic. On higher-order
function-equality / pointwise-iff goals `auto` times out (and says so)
rather than failing fast — decompose with `congr` / `funext` /
`split_hyp_iff` instead.

#### `set_tac` — Go `SetTac()`; the recorded mode `SetTacMembership()` / `SetTacLegacy()`

**The set closer, recorded as ONE first-class ministep**
(`StepProto_SetTac`). Deterministic fixpoint-unfold of the set vocabulary
(`set_member`, `empty_set`, `universe`, `insert`, `delete`, `union`,
`intersection`, `set_difference`, `subset`, `proper_subset`, `disjoint`,
`big_union`, `big_intersection`, `image`, `set_comprehension`,
`comprehension_spec`, and every constant declared to read its
membership, `registry.DefEntry.MembershipRead`: `preimage_on`,
`fun_support`, `m .. n` and the four real intervals `⟦a, b⟧`, `⟬a, b⟭`,
`⟦a, b⟭`, `⟬a, b⟧`) across goal AND hyps
(per-occurrence type instantiation — the same `TryDefExpand` walker
`def_expand` uses, so polymorphic `set_member⟨A:prod(A,B)⟩` occurrences
unfold too), then a bare CNF refute on every residual leaf.

A rewritten slot is cleared of the boolean constants the unfolding put there
(`x ∈ 𝕌` is ⊤, `x ∈ ∅` is ⊥: `⊤ ∧ p`, `p ⇔ ⊥` and their kin are simplified
away), and a residual whose conclusion is then a resident hypothesis up to
binder names closes by assumption with no key — so a complement in the whole
type or a disjointness closes keyless from the pointwise fact of the same
content (`BySets(fact)`, the fact itself by `ByArith()` or a cite) — and a
residual the apply rung closes closes on it, with no key (`setTacRungClose`:
the By family's one closing procedure, run where the unfolding has put the
goal and the hypotheses in the vocabulary the driver decides, so a resident
law that concludes a membership in a union or an image applies to the
goal it unfolds to; the stage's rung, run before the driver, reads a
set-builder's membership as its condition at the point and nothing of the
other set operators, so `∀y. |y − c| < δ ⇒ y ∈ {x | x ∈ space ∧ P(x)}`
applies to `P(a)` there and `∀y. … ⇒ y ∈ s ∪ t` only here).

The goal takes one apply and its antecedents one more, as on the stage; the
refute is reached only by what neither closes.

**Close-or-fail**: the ministep records ONLY when every residual leaf closes
— a fail leaves the session untouched; fall back to manual `def_expand`
navigation. The recorded proto carries the const list, and replay re-runs
the same driver code (record/emit/replay-reuse — no expansion snapshot; the
closing refutes' CNF cache keys are identical at record and replay by
construction). Use when a set-theory goal should close after unfolding the
set vocabulary: for a set-typed equality GOAL `s = t`, bridge via
`set_basic.Extension` to the pointwise form first (not `funext`, which
leaves applications where Extension leaves memberships), then `set_tac`;
membership/inclusion goals take `set_tac` directly.

**Two modes, one door.** The driver has a MEMBERSHIP mode — set operators
stay first-order terms, their membership rules are installed as premises,
set witnesses stay first-order — and a LEGACY mode, the full λ-level
expansion of every vocabulary const. The session's `set_tac` and the Go
`SetTac()` are the same door (`proof.SetTacOrder`): membership first, then
legacy, each close-or-fail, and the step recorded is the one of the mode
that closed — `dump-section` prints it, `SetTac(<n> consts,
SET_TAC_MEMBERSHIP)`, and emit renders it as the exact-mode form,
`SetTacMembership()` or `SetTacLegacy()`, which replays that one driver.
A chapter spells an exact form itself only to say which mode a record is
(set_algebra's conditional laws, legacy by measurement); a hand-written
`SetTac()` replays as the door, the recorded mode's keys closing it
whichever mode that was.

**A failure names its leaf.** A `BySets(…)` (a `By` with the set
closer) that does not close prints, beside the premise list, the leaf
the driver was handed — the conditioned sequent, after the shaping the
author spelled — and the driver's residual leaves after its membership
rewrite, the ones no refutation closed (`the set driver's residual
leaves, after its membership rewrite, that did not close: …`), so a
membership the rewrite left folded is read off the residual; the other
closers print the leaf they were handed the same way (`the closer … did
not close the leaf / on leaf goal: …`).

**The const list is the DRIVER's fixed vocabulary, not a per-caller choice**
— `proof.SetTac()` / `proof.SetTacMembership()` / `proof.SetTacLegacy()`
called with NO consts use
`proof.StandardSetVocabulary()` (the names above), which is what every
call site in the tree passes anyway; a name the goal does not mention is
inert, so a narrower list buys nothing and a hand-spelled copy can only omit
one, in which case the driver silently fails to unfold rather than reporting
anything. Pass consts explicitly only to deliberately withhold a name.

#### `simp_with` — Go `Simp(Fwd(…), Rev(…))`

**The simplifier, recorded as ONE first-class ministep**
(`StepProto_SimpWith`). Rewrites the goal's CONCLUSION with an ORDERED rule
set, jointly, to fixpoint. A clause whose matrix under its antecedent is an
ATOM rather than an equation (`finite(s) ⇒ finite(insert(x, s))`, the insert
half of `finite_set.FiniteRules`) is a closure rule: it can discharge
another rewrite's side condition, but does not itself rewrite the target.
The rule-set diagnostics (`rule_shape`) name that role at resolution,
and the no-progress diagnostic explains it. To derive the atom directly,
cite the law in a `by`.

**Parameters.**
`with_lemmas: [{key:str | text:str | hyp_index:int, type_specialize:{…}, term_specialize:{…}, flip:bool, normalized:bool}, …]`
(ordered — slice order is firing order). A rule named by `key` certifies
its own child against the entry; a rule given by `text` names no entry, so
its child — the rule as stated, or an adapted or specialized instance of
it — closes only on a proved section of the session, or an entry, that
states it, whether or not the rule carries type letters. A step that
would leave that child open is REFUSED, naming the rule, and the session
is unchanged, as `by` refuses a text premise nothing certifies (`simp_all`
refuses its named rules the same way). A text rule is proved before it is
used: a law as a section of its own, a fact about the goal's own variables
by `assert`, which leaves it a hypothesis. A text rule that is an equation
the goal holds as a hypothesis has no child: the driver rewrites by that
hypothesis, and `emit-section` spells it as the fact naming the
hypothesis, as it spells `{hyp_index}`. A conditional rule the goal holds
is cited by `{hyp_index}`: the child of its text is the rule under no
hypothesis, which the hypothesis does not certify, and the refusal names
the index. A text rule the normalizer decides — its normal form is ⊤,
as `∀p. p = (p ∧ p)` turned around to contract a conjunction — closes on
no section that states it, since the pass that reads the proved sections
passes over such a statement: its refusal says so and names its one
route, `assert` the rule, close the claim, and cite the hypothesis by
`{hyp_index}`. A
resident hypothesis is a rule by its index, `{hyp_index: i}`, alone on its
entry (beside `flip` at most): the hypothesis assumed, `h ⊢ h`, at its own
types, its child closed on the hypothesis itself before any entry is
consulted — never a text rule, whose child names no entry. It is the Go
`Simp(Fwd(fact))` (§"Simp(Fwd(r₁), Rev(r₂), …)", "A resident fact is a
rule"): a guarded resident equation fires as a conditional rule, and a
resident closure discharges another rule's side condition. Refused under
`simp_all`, on `by` and `auto_with` entries, and as the rule of the
hypothesis `hyp_index` rewrites. `normalized:true` serves the rule
in the NORMALIZER's orientation — `proof.NormalizedForm` of the entry's
statement, the form the Go `Fwd(MakeFact(ctx.DepNormalized(name)))` fires — for the
one-pass script whose earlier rule leaves an equation the next rule's stated
form has no redex for (after the flipped `LengthEqNil` the goal reads
`0 = list_length(l) + list_length(m)`, and `nat_arith.AddEqZero` stated
`m + n = 0 ⇔ …` never fires, while its normal form `0 = m + n ⇔ …` does —
`[{key:"list.LengthEqNil", flip:true}, {key:"list.LengthAppend"}, {key:"nat_arith.AddEqZero", normalized:true}]`
is the one call; `list.AppendEqNil` ships it as
`Simp(Rev(LengthEqNil), Fwd(LengthAppend), Fwd(MakeFact(ctx.DepNormalized(nat_arith.AddEqZero)))), TrivialNormalized()`.
The residual differs from a tautology only by the sides of its equations,
and session `auto` closes it through the arith fast path, recording
`Arith()` — so close it in Go with `TrivialNormalized()`, keyless, not with
what `auto` emitted). The rule child closes against the entry as any rule
child does; emit renders the rule `Fwd(MakeFact(ctx.DepNormalized(<var>)))`
(`Rev` with `flip`; `ctx.AtTypes(ctx.DepNormalized(…), τ…)` for an
auto-adapted instance). Refused beside `type_specialize` / `term_specialize`
(a specialized instance is served stated, as `AtTypes` serves it), and
refused by name on `by` and `auto_with`. **`hyp_index` addresses a
HYPOTHESIS** (Lean's `simp at h`): that hypothesis is rewritten in its
place, the rules' side conditions discharged against the other hypotheses,
the conclusion untouched; the Go face is `fact.Simp(rules…)`
(`SimpAt(i, rules…)` positionally, which emit falls back to when no Fact
names the hypothesis). **The matcher reads an antecedent as written.** A
conditional rule whose antecedent is `A ∧ B` does not fire where the
target's antecedent is `A ∧ B ∧ R` — `(A ∧ B ∧ R) ⇒ Q` is not read as
`A ∧ B ⇒ (R ⇒ Q)`; matching modulo that equivalence would change which
conditional rules fire corpus-wide, and is not done. State the law in the
shape it is cited at, or prove the two directions
(topological_space.ConnectedInSubtopology).

Rule shapes (per conjunctive clause, after the outer ∀-strip — a Horn clause
PACK `C ⇒ eq₁ ∧ eq₂` under one antecedent is one conditional rule per
conjunct, `iterate/monoidal`'s `Clauses` included): `l = r` / `l ⇔ r`
(unconditional, fires in written direction — NO bidirectional retry; set the
per-entry `flip: true` bit to fire an unconditional equation right-to-left —
the recorded rule prop stays the entry's statement and only a parallel
`SimpWithProto.rule_flip` bit changes on the wire, so the rule child
α-matches the entry exactly as an unflipped rule would and the emit records
the same entry. `flip:true` also turns around the equation matrix of a
CONDITIONAL rule — `C ⇒ … ⇒ ∀ys. C' ⇒ … ⇒ l = r` or `¬C ∨ … ∨ l = r` — in
place, the antecedents untouched; only a rule with no equation to flip, a fact, is
rejected at resolve time with a typed error. The normalizer keeps a bare
variable on an equation's LEFT (`x = op(e, x)`, `zero = add(neg(x), x)`),
which is the expanding direction and a bare-binder LHS besides, so a
structure law served by key collapses only `flip:true`); any other boolean
`P` (a factorial — oriented to `P ⇔ ⊤` as a rewrite AND usable as a
side-condition discharge oracle, the role `nat_sum.MonoidalNatAdd` plays);
`C₁ ⇒ … ⇒ (l = r)` or the normalized clause form `¬C₁ ∨ … ∨ (l = r)`
(CONDITIONAL — the class of `monoidal.Union` / `monoidal.Clauses`).

Conditional rules fire by instance mining at binder-closed positions: the
LHS is matched first-order — a ∀-bound HEAD applied to arguments binds to
the head it meets, so a structure law's `op(x, e)` matches `add(a, zero)`
with op := add — and every ∀-binder must be pinned: by the LHS, or, for a
binder the LHS never mentions (the `zero` of `add(neg(x), x) = zero`), by
the side conditions matched against the goal hyps and then the set's ground
fact rules with the bindings so far in hand (the resident
`abelian_group(G)`, or the instance `comm_monoid(real_add, &0)`
passed as a rule, says what zero is — the assumption read as a matcher; a
binder nothing pins is never invented). A side condition the goal holds as a
CONJUNCT of a hypothesis — `x ∈ c` under a resident `x ∈ c ∧ y ∈ c`, the
one guard fact a carrier law's proof receives — is discharged by
∧-elimination from that hypothesis, which the reconstruction then stands
on; the mirror of the rule side, where a conjunctive antecedent is read
as its conjuncts.

Each side condition `Cᵢσ` is read in β-normal form — a binder the rule
APPLIES (`∀k x. Q(k(x)) ⇒ …`), bound to a λ by the match, leaves
`Q((λy. t)(a))` in the instance, and it is `Q(t[a])` that a hypothesis, a
fact or a rewrite holds — and must then discharge via (a) α-match against a
goal hyp or a conjunct of one, or a match up to the record reading — a
hypothesis spelling a projection of a packed value as its author wrote it,
`u ∈ free_module_record(c, S).carrier`, holds the condition an instance
states at the part, `u ∈ finite_supp(c.zero, c.carrier, S)`, both sides read
through the record equations as the step's cites, the reading a closer's
leaf is handed in — strip_quant/strip_imp FIRST so antecedents sit in the
hyps (the assumptions read as rewrite rules), (b) full-pin match against a fact rule
in the set, (c) the set's own unconditional rewrites reducing it to ⊤
(depth 1, no recursion), or (d) a CLOSURE rule of the set — a rule whose
matrix under the antecedents is an atom, `x ∈ c ∧ y ∈ c ⇒ x * y ∈ c`,
which rewrites nothing — whose conclusion matches the condition, its
remaining binders pinned as a conditional rule's are and each antecedent
instance discharged by these same routes, every antecedent the goal does
not hold a smaller term than the condition (the chain descends and
terminates; no term is invented): the carrier-membership decision, `x *
inv(x) ∈ c` from `x ∈ c` by the closures under `*` and `inv` named in the
set. A conjunctive antecedent (`x ∈ c ∧ y ∈ c ⇒ …`) is
its conjuncts, each a side condition of its own, and a guard under a
structure law's inner ∀ (`S(comps) ⇒ ∀x. x ∈ c ⇒ …`) is a side condition
beside `S`. Mined ground equations join the rewrite set and the
loop re-runs (an unconditional fire can expose a conditional redex — a
definition unfold, a conditional union law and a monoid fact close in ONE
call), bounded by policy fuses + the per-fire divergence whistle. A
rewrite the whistle cuts ends the step with nothing committed ("A rule
set that feeds itself is cut", below).

**Higher-order rules fire**: an unconditional rule whose ∀-bound PREDICATE
variable is applied to bound vars under λ/∃ (the pair-comprehension
membership class,
`set_comprehension(λg. ∃x y. comprehension_spec(g, P(x,y), (x,y)))((a,b)) ⇔ P(a,b)`)
rewrites via Miller-pattern matching and β-reduces the instance (verified:
`TestSimpWith_HOComprehensionRule`). So does a conditional one: a
quotient's "every class" reading, `h ⊆ c ⇒ ∀P. (∀s. s ∈ left_cosets(c,
h) ⇒ P(s)) ⇔ ∀x. x ∈ c ⇒ P(left_coset(x, h))`, at the goal `∀s. s ∈
left_cosets(c, N) ⇒ Q(s) ∧ R(s)` binds P to `λs. Q(s) ∧ R(s)`; the
instance is checked against the subterm, mined and written into the
conclusion in its β-normal form, `P(left_coset(x, N))` read as
`Q(left_coset(x, N)) ∧ R(left_coset(x, N))`, its side conditions
discharged as above (verified: `TestSimpWith_PredicateBinderGuardedFires`).

**A first-order rule matches as the base case of the same fragment**: a rule
variable standing bare for a subterm — the projection law
`re(complex(a, b)) = a` at `re(complex(X, Y))`; a definition whose left side
is its head applied to its binders fires on the head by η and never unifies
— is the n = 0 Miller pattern, whose one unifier is the subterm itself, and
the unifier commits it at once; its imitation branches, which copy the
subterm one constructor per step and re-verify every pending pair at each
step, are never entered for it (`ext/unify/flexible.go` tryMillerPattern;
`TestTryMillerPattern_BaseVar_LargeGroundTerm` pins the match on a large
term).

**The pre-CNF fallback reads one normal form per rule set, and never where
no normal form can hold the pattern.** A rule that fails as written on a
Bool node is retried on that node's pre-CNF normal form — the bridge for a
propositional pattern that IS the normal form's skeleton (⇒ as ¬∨, a
quantifier's scope, a clause's order, an equation's orientation) — unless
its pattern is an implication, which no normal form contains, so that rule
is never retried and normalizes nothing. A rule whose pattern is headed by a
constant is not retried on a node that lacks the constant either: the
normalizer's rewrites are the logic's own, so the normal form names no
constant beside a connective, a quantifier or equality that the node does
not name, and the retry would find nothing (`prop.preCNFRetryOf`;
`TestPreCNFNormalFormHoldsNoConstantItsInputLacks` pins the premise). A
pattern headed by a variable or by one of the logic's constants is retried
on every Bool node.

The rewrites of one rule set share one normalization cache
(`prop.PreCNFCache`: one per `simp_with`/`Simp`, rules and mined instances
alike, one per multi-clause `lean_rw`, one per `eqSimplify` tactic call over
a goal's hypotheses), so a node the rules do not fire on is normalized once
per set and per spelling, not once per rule — the fixpoint driver calls
every rule at every node of its walk, in every round, and with a cache per
rule the same node was normalized once per rule. A `Simp` step runs its rule
set three times over the one goal — for its children, at its reconstruction
gate, and for its theorem — and the three runs read the step's one cache,
which lives as long as the step. The residual reading that adapts a
polymorphic rule before the step is a run of its own, with a cache of its
own.

A fixpoint that calls an equality tactic on one goal after another — `Basic`
and its bounded forms, the trivial simplification, the simplification after
a lemma install, the passes of `rw` — is one run, and the run keeps the
normal forms its tactic calls read (`tactic._SearchMode.asRun`). A goal of
the run keeps most of the hypotheses of the one before it, so each call's
cache stands in front of the run's (`prop.NewPreCNFCacheOver`) and takes
from it a hypothesis the run has read under the same spelling, bound names
included; a term spelled otherwise is computed, as it would be with no run
behind. The run's cache is freed with the run, and nothing is kept for the
process.

A TERM rule (an equation at a non-Bool type) is retried too, and the
recorded corpus depends on it: its pattern meets, through the normalizer's
β, an instance a previous fire left inside a redex — the projection
`re(complex(a, b)) = a` at `(λu v. re u = re v ∧ …)(complex(x, y), …)`, the
⇔ rule's own instance — one rule-chain before the set's β rule would expose
it, and the fire carries the goal's whole re-spelling (binders sorted,
equations oriented) along; the propositional-only criterion that would
retire this is exact in no cheap form and MOVES KEYS (`cartesian/pairs`'
refutes replay only with the term-rule fire), so it waits for a re-keying. A
∀-stated identity costs more under a rule set than the same identity with
its binders fixed (`FixAs` each, then the Simp), which is the shape to
write. When a combined rule set leaves vacuous Boolean clauses
(such as `¬⊥ ∨ P`), `Basic()` removes them. Separate rewrite passes are
appropriate when the next verb needs the intervening binder shape;
regrouping the rules does not promise the same residual syntax.

Pass such rules as TEXT in the goal's form (applicative vs set_member-form)
and in the FIRING orientation — elimination laws state the P-application on
the LEFT, so the comprehension-eliminating direction is usually the flip.

**A structure law read at an instance is a rule** — the Go
`Fwd(law.Read(instance))`: `{"key": law, "read_at": …}`, the instance an
entry, a resident hypothesis or a reading exactly as on a `by` premise (the
`by` row). The rule is the law's equation at the instance's components, the
structure hypothesis discharged by the kernel, entered once at its own
letters: `field.InvZero` read at `complex_field.Field` rewrites
`complex_inv(complex_of_real(&0))`, where the law and the instance listed as
two rules fire nothing — the law's redex is `inv(zero)` at a zero nothing
told the matcher. Under a resident hypothesis the rule is the sequent, and
it fires where the goal holds that hypothesis. `flip` composes;
`term_specialize`, `type_specialize` and `normalized` are refused on a
reading. The fired rule's child certifies from the derived theorem; recorded
in `SimpWithProto.rule_reading`, emitted as `Simp(Fwd(Law.Read(Instance)))`.

**A COND a rule INTRODUCES is decided by the resident guard**: the driver
reads the goal's hypotheses for a COND's guard exactly as it reads them for
a conditional rule's side condition (α-match; `c` selects the first branch,
`¬c` the second, and `d` decides `COND(¬d, …)`), so under a case split's
resident `x ∈ s` the rule set
`[cardinality.CardClauses, listing.FiniteSetOfList, …]` leaves `card(s) ≤ …`
and not `COND(x ∈ s, card(s), suc(card(s))) ≤ …` beside the guard. The tidy
after `def_expand` / `Unfold` does NOT decide such a COND (it reads no
resident fact into the goal; §Playbook, "The tidy after an unfolding applies
no resident fact"): where a definition's body is a COND on a resident guard,
open it as a rule, `Simp(Fwd(<Def>))`, and the driver decides it here, or
unfold and close with the guard named, `Unfold(c), By(guard, …)`, whose
closer decides it. The decision is a consequence
the context supplies, never progress on its own: a rule set that fires
nothing still fails. A `cond_rewrite` after such a `simp_with` fails as
no-progress, the COND being gone. A session bound to a family installs that
family's definitions for the BARE `simp` and for `simp_all`; `simp_with`
fires only the ordered rules it is given, as the Go `Simp(Fwd(…), Rev(…))`
it renders to does, so the session move and the file's step are one for
one — a `simp_with` of one definition unfolds that definition and nothing
the chapter defines beneath it. A step that needs a chapter definition
beside the cited law lists it (`[{key:"list.ReverseAppend"},
{key:"list.ListAppendDef"}]`, one `Simp` of two rules) or is followed by a
bare `simp` (two steps). The `simp` row's "fires the chapter's definitions
with zero setup" is the bare verb's alone. `installed` is a parameter of
no simp verb; a request carrying it is refused by name.

**A PERMUTATIVE law is safe HERE, unlike in `lean_rw`** — the driver's
rewriting is ordered, so `∀m n. m + n = n + m` fires once and stops. On
`⊢ a₀ + b₀ = b₀ + a₀`, `simp_with [nat_arith.AddSym]` leaves `a₀ + b₀ = a₀ + b₀`
in ONE fire with no whistle and `refl` closes it, while
`by {with_lemmas:[nat_arith.AddSym]}` on the same leaf closes through the
refuter (`By(1 premises; cnf)`) and records a key. So the `lean_rw` row's
"never the ∀-form of a permutative law" does NOT carry over: for a
commutativity/symmetry law the RULE is the keyless spelling and the premise
is the keyed one.

**Progress-or-fail**: records only when at least one rule fired; a fail
leaves the session untouched with a diagnostic naming the likely fix.
Children = the USED rule statements (closed against the cited entries, incl.
the type-instance pass for adapted AND explicitly `type_specialize`'d
polymorphic rules — recorded as TypeInst against the polymorphic entry, so
deps record like `lemma`'s claim child and the emit resolves them through
the polymorphic source) + the rewritten residual. Replay re-runs the same
driver (record/emit/replay-reuse, the `set_tac` pattern); the proto carries
the RESOLVED rule props verbatim, so later corpus changes never alter a
recorded step. Per-entry `type_specialize` / `term_specialize` compose
exactly as on `lemma`.

A polymorphic rule WITHOUT explicit σ **auto-adapts to every distinct
instance found by the finite anchor-pin walk**, read off the goal AND off
what the rewrite exposes — the
set is run, every adaptable rule is re-adapted against the residual, and the
loop repeats while a round adds an instance (a pair law behind
`letter_inverse`'s unfold, an append clause behind `list_reverse`'s, adapt
in the call that unfolds them; the recorded step is still the one driver run
over the final set) — including the instance whose image contains a letter
of the same NAME as the rule's own (`A ↦ A → bool`: a set lemma read at
families, the goal's point type inside the image; or the letters swapped,
`A ↦ (B → bool), B ↦ (A → bool)`): the adaptation sweep's occurs-check is by
name and drops such a binding as recursive, so it is reached by a SECOND
sweep with the rule's colliding letters renamed apart, run only when the
first sweep dropped a binding by that occurs-check, even if it found other instances
(`typematch.renameLemmaTypeVarsApart`). The enumerations add its instances
beside the rule at its own letters. The single adaptation a `lemma`/`by`
install commits (`TryAdaptLemmaTypes`) REPLACES the bare rule, so it
retries only where the first sweep left a rule letter with no binding at
all whose name the goal spells — the rule, or the instance committed, would
read that letter as the goal's, at an instance the goal holds nowhere — and
takes the retry's instance when it binds every renamed letter. Where the
first sweep bound every such letter, if only to itself (a law cited at its
own statement), the install keeps what that sweep found: a retry there
reaches a coincidental wrong instance.

What the sweep commits is then held against the constants the goal holds.
The sweep commits its largest anchor's first candidate, so a constant in a
side position of the law can decide the instance: the largest anchor of
`cardinality.CardClauses` is the membership of its insert clause, and at a
leaf over `card({S | S ∈ C ∧ f(x) ∈ S})` it meets `f(x) ∈ S` at the element
type, where the leaf holds no `card` and no `∅`. An instance MISSES a
constant of the law that the goal spells and carries at no type the
instance gives it. Where the commit — or the law at its own letters, the
sweep having made no instance — misses one, and an instance the goal offers
(the enumeration below) misses none, that instance is the install
(`typematch.readsEvery`); of several, the enumeration's first. So
`CardClauses` cited bare at that leaf installs at sets of sets, whichever
membership the predicate spells first and whether the chapter's letter is
the law's own or another. An instance that itself misses a constant is
never taken: at a leaf that holds the law's membership at the element type
alone and its `card` at sets of sets alone the commit stands, and the
instance is pinned (`type_specialize`, a typed `.At`). A `by` that fails
with such a premise says so ahead of its other advice: it names the
premise, the instance installed, the constants the leaf holds at no type
that instance gives them, and each instance the leaf offers that reads one
of them, spelled as the pin that selects it (`A := (var:A → bool)`). A type
letter that a hypothesis or a free variable of the lemma spells is its
context's and is never moved.

For simplification, `typematch.EnumerateLemmaTypeAdaptations` completes
all anchor pins in the finite target — the one enumeration the `by`
rung's head candidates read too — deduplicating the resulting rule
instances by AlphaKey. It uses the same structural matching and sweep
completion as the general adapter; this is not an exhaustive higher-order
search. An anchor is a real constant of the rule, or an equation between
its binders at a compound type, so `set_basic.Extension` can adapt from a
set equation alone. No per-rule instance count truncates this enumeration.
The rule at its own letters remains beside the adapted instances, since
both can have redexes in the same target. Go and session simplification
use this discovery path for the conclusion or the selected hypothesis;
the other hypotheses remain available for conditional rules.

Rewriting can expose further instances, so discovery repeats against the
residual. The rounds are bounded (`proof.MaxSimpAdaptRounds`) because a
rule can restate its constant at a larger type
(`card(s) = card(image(singleton, s))`) and expose a new instance of
itself at every round. A copy added at the bound that rewrites the
residual further is a refusal naming the rule, the instance and the
spelling that ends the re-adaptation (an explicit instance is not
re-adapted); copies with no redex are inert, and the set is complete as
it stands. Nothing is committed on the refusal.

Each expanded copy is recorded verbatim in `SimpWithProto.rules` — nothing
new to replay, deps dedup to one entry via the shared TypeInst channel. A
rule WITH an explicit `type_specialize` (or `term_specialize`) is honored
exactly — pinned to that single instance, no re-adaptation, no
multi-expansion. A `term_specialize`'d rule's claim child is a TERM instance
(not a type instance) of the entry, so the auto-close pass leaves it OPEN —
close it yourself (`lemma({key})` then `auto`); it is never mis-recorded as
an unresolvable per-session KnownThm.

#### `auto_with`

**Scoped lemma + focused-auto + close-or-fail.** One atomic call that (1)
clears noisy ∀-hyps from the session per a clear mode, (2) installs each
entry of `with_lemmas` against the post-clear leaf (with the same
type-instance pass the agent-facing `lemma` flow uses, so each install's
claim subgoal closes against the entry it names), (3) runs `auto` across
every remaining leaf — per-leaf arith, then `AutoExpandWithCtx.Apply` (which
iterates `n.unsolvedLeavesIter()` internally), then a final auto-match pass
in a make-progress loop. If the residual doesn't `.Proved()` at the end, the
entire orchestration is **rolled back** — the session never absorbs the
clear or the scoped lemma installs without a close. Use when the session has
accumulated wide ∀-hyps (the refute-poisoning class — `lemma`/`def_expand`
resident loads) AND the close needs a specific small set of entries to
chain. Equivalent to manual `clear([…]) → lemma(L₁) → lemma(L₂) → … → auto`,
but atomic, with the trial-and-error rollback the manual chain doesn't have.
Clear modes (mutually exclusive): `drop_hyp_indices=[i,j,…]` drops exactly
those; `keep_hyp_indices=[i,j,…]` clears every hyp NOT in keep; **default**
(neither given) clears every top-level ∀-headed hyp — the heuristic
targeting the dual-type pollution case of `cardinality.CardEqBijection`.

**Tolerates benign branching.** When a lemma install's claim subgoal doesn't
close against its entry (normalization gap or polymorphic-key mismatch), the
claim survives as a sibling leaf. Subsequent installs target the most-recent
residual (`UnsolvedLeaves[last]`); the final close pass attempts every leaf.
An earlier strict guard rejected this with
`"unexpected branching — single-residual step produced 2 leaves"` and walled
on multi-lemma chains for the union, difference, inclusion-exclusion and
image laws of an iterated operation; the guard is gone. The diagnostic on a
real failure enumerates every open residual leaf (up to 3) so the agent sees
exactly what didn't close. Each `with_lemmas` entry mirrors `lemma`'s shape:
`{"key": "…"}` (an entry) or `{"text": "..."}` (DSL), optional
`type_specialize: {…}`, optional `term_specialize: {…}`. No new proto tag —
internally records as
`ClearHyps + LemmaPreserve×N + KnownThm×N + Arith + AutoExpand` (the same
ministep sequence the manual chain produces); replay re-runs the chain
unchanged; emit and chapter Go are transparent.

**Failure diagnostic names what was tried**: initial hyp + ∀-count, indices
cleared (with text shapes for the first few), lemma identifiers (key +
type_specialize), residual leaves + their ∀-counts, plus a one-line hint
pointing at the most likely next move (`keep_hyp_indices` when default
cleared the only ∀-hyp; missing-`with_lemmas` when none were given but the
residual needs chaining; `case_split`/`split_disj` when residual has
multiple branches; `instantiate`/`type_specialize` when a wide ∀ survived).
Don't chain `auto_with` calls — its atomicity is per-call. For multi-stage
exposure (strip + split + auto_with), do the structural moves explicitly,
then one `auto_with` for the close. Example:
`auto_with({"with_lemmas": [{"key": "prop_7d7685f1427a8d6c"}, {"key": "prop_265109053fc36238"}, {"key": "prop_78ff54e48227718e"}, {"key": "prop_cb63abd1d029ab71"}]})`
closes the unfolded `monoidal_op(*)` 3-conjunct (`real_ring.NeutralMul` +
`real_construction.MulSym` / `MulAssoc` / `MulLeftId`) in one move.

#### `by` — Go `By(premises…)` / `ByArith`

**The math layer's premise-disciplined close (`By`/`ByArith`) as a session
move — `auto_with`'s DECLARED sibling.** A statement, not a search: THESE
premises (resident hyps named in `by_hyps` are KEPT and everything else is
CLEARED FIRST — the lexical scope that defeats ∀-hyp refute-poisoning;
lemmas in `with_lemmas` are installed via the preserving chain, ground at
`term_specialize` witnesses; a premise of either kind with `coefficient:"c"`
— a term text in the goal's scope — is followed by the congruence
`c·l = c·r` of its equation, Lean's `linear_combination` coefficient, see
the Playbook §"The structure ring"), the declared `by_shape` normalization
(`normalized` = Basic between installs and close; `pre_normalized` /
`denoted:n` / `hilbert` mirror the ByShape values — and **`denoted:n` runs
`Denote(n) + Basic()` where `n` is a SIZE THRESHOLD on the subterms to
abbreviate, NOT a count of how many to denote**, so the useful values are a
band rather than a small integer: on one induction terminal `n=1,2` failed,
`n=4…20` succeeded and `n=40` failed again. Probing only the natural first
guesses `1` and `2` concludes "denote does not help" when it does), then ONE
refutation — or the gated arithmetic closer with `arith:true` (scope-gated
by the session's proof scope exactly as replay's omega circularity gate;
`by` NEVER takes the arith fast-path silently, so it cannot record the
un-replayable surprise `Arith()` the de-Arith recipe exists for).

**A premise reads the leaf the premises before it have built.** The
premises are installed in list order — `by_hyps`, then `with_lemmas` as
listed; in Go the arguments of `By(…)` as written, the resident
hypotheses kept from the start — and two installs read the leaf they
install into. A bare lemma goes through the preserving chain, which
rewrites the goal by the law, or closes where its rewrite meets a
hypothesis: `[HomCompose@(R, V, V, V, S, T), ComposeApply]` closes
`module_homomorphism(R, V, V, λw. T(S(w)))` at `ComposeApply`'s install,
its rewrite to `T ∘ S` meeting the instance, and
`[ComposeApply, HomCompose@(…)]` installs the law as a clause and fails
at the refuter, which does not rewrite under the binder. A witnessed
lemma takes its stated form where the leaf supplies its guards and the
closer's clause form where it does not: `[InUniv, law@(…)]` discharges
the instance's carrier guard at `𝕌`, `[law@(…), InUniv]` hands the closer
the guarded clause. The goal's own antecedents supply no guard at an
install: S2 moves them into the hypotheses after every premise is
installed, so on a goal `v ∈ S ⇒ …` an instance that `v ∈ S` guards
takes the clause form, and after an `Assume` of `v ∈ S` the stated one.
So a fact is listed before the premise that reads
it: what supplies a guard first, a law that rewrites the goal last. A
close that fails for the order says so — it runs the installs again with
one premise moved to the end and names the bare lemma whose install then
closes the goal, or the witnessed lemma that then takes its stated form
(`listOrderNote`, prover/proof/step_by.go). `emit-section` renders the
premises in the session's order, so the member is the close the session
made; a hand transcription keeps that order.

**Parameters.** One whole envelope, as the wire takes it:
`{"cmd":"apply","session_id":S,"goal_id":G,"tactic":{"type":"by","by_hyps":[{"hyp_index":0}],"with_lemmas":[{"key":"dot.AddLeft"},{"key":"real_ring.CommRing"}],"by_shape":{"normalized":true}}}`
— `by_hyps` is a list of OBJECTS and `by_shape` an OBJECT; a bare index, or
the string `"normalized"`, fails to unmarshal.

- `by_hyps: [{hyp_index:int, terms:[str,…]}, …]` (resident premises;
  optional witnesses in the hyp's stated binder order, the binders behind
  an antecedent included, as Go's `fact.At` reads them: `∀c. c ∈ s ⇒ ∀ε.
  &0 < ε ⇒ …` takes `["y₀", "ε₀"]`, its guard discharged from the
  premises);
- `with_lemmas: [{key|text, type_specialize:{…}, term_specialize:{…}}, …]`
  (named premises; `term_specialize` names the dep's STATED binders — a
  table naming a stated prefix grounds exactly those binders, wherever the
  clause form's canonical labeling put them (the executor moves them to the
  front of the clause's ∀-block: `LessEqTrans` pinned `{m, n}` grounds m and
  n of `∀m n p`, not the first two slots of its clause `∀n p m`); a prefix
  that stops short of a principle's guarded binders — `{P}` on a
  rule-induction or strong-induction principle — is completed from the goal
  (the index read off the conclusion) and takes the stated form where the
  obligations are resident, so `{P}` beside the named obligations closes as
  `{P, x0, x1}` does; a table naming exactly the dep's own leading
  ∀-binders — a card `∀R M N. S(R, M, N) ⇒ ∀p u. …` at `{R, M, N}` — takes
  the stated form where their guard is resident, the guarded ∀s of the
  body standing in the instance; and a sparse table seeds the apply rung; witnesses
  that bind every type variable of a polymorphic law make the premise EXACT,
  as `type_specialize` does — the session twin of Go's typed `.At`, which
  installs exactly the instance its witnesses infer — whatever letters the
  instance is stated over, the goal's own included (the law's `B` read at
  `set(A)`, its two letters swapped); an explicit `type_specialize` σ
  applies BEFORE term_specialize and marks the premise EXACT — installed
  verbatim, no goal-side re-adaptation — recorded as `ByPremiseProto.exact`;
  `flip` and `normalized` rejected by name — both are simp_with rule forms;
  a premise has no form to choose: bare it installs in the closer's clause
  form, witnessed in its stated form grounded at the tuple);
- optional
  `by_shape: {normalized|pre_normalized|denoted:int|hilbert|denoted_as:{name,term}|hilbert_denoted_as:{name,term}}`
  — `denoted_as` is the EXPLICIT denote, the Go `DenotedAs(name, term)` a
  chapter writes
  (`"by_shape":{"denoted_as":{"name":"d","term":"f(x + y)"}}`, the term read
  at the goal; `hilbert_denoted_as` its ε-term twin), where `denoted:n` is
  the search form that proves only that SOME denote closes the leaf:
  validate the shaping the file will carry with `denoted_as`. A By names at
  most one term, as in Go; emit renders `DenotedAs("d", …)`;
- optional `arith: bool` (the gated arithmetic closer — the math layer's
  `ByArith`; bare premise-free form legal: every hypothesis is cleared and
  the goal is decided as a fact of arithmetic alone, a close that needs a
  hypothesis names it; a premise guarded by what another named premise
  states — a membership, a predicate, an arithmetic fact — is read as its
  consequent, the `arith` entry's rule for a formula a hypothesis states);
- optional `settac: bool` (the membership-mode set driver — the math
  layer's `BySets`; mutually exclusive with the other closers; bare
  premise-free form legal, the vocabulary unfolding being its content; emit
  renders the composite back as `BySets(...)` 1:1);
- optional `chase: {depth:int}` (the diagram-chase closer — the math
  layer's `ByChase(Depth(k), …)`; mutually exclusive with `arith` and
  `settac`; premises required, since the closer reads its diagram from
  them — the Playbook's §"Diagram chases in `by {chase}`" says which
  shapes it reads and which stay out; `depth` is the number of pull-back
  rounds, a parameter of the record, never a wall clock; emit renders
  the composite back as `ByChase(Depth(k), ...)` 1:1);
- optional `broadcast: bool`.

`keep_hyp_indices` / `drop_hyp_indices` are `auto_with`'s fields and are
REFUSED here by name, never dropped — `by` reads `by_hyps`.

`broadcast:true` runs the closer over every leaf the shaping fanned —
bounded at 64 rounds (`byBroadcastRoundBudget`, one round per leaf
conditioned, shaped and closed): a shaping that re-fans each leaf it
conditions never converges, and the loop refuses it with the leaf it stopped
on rather than running until the process is killed. With or without
`broadcast`, a round that hands the closer a leaf an earlier round handed it
is refused at once, the same way ("the rounds cycle"): the rounds read
nothing but that leaf, so the orbit would run to the budget — measured on a
leaf whose conditioning grounded the instances the mop-up stripped again,
sixty rounds at seconds a round. Records **ONE `by`
composite ministep** (`StepProto_By`, prover/proof/step_by.go —
record/emit/replay-reuse: the same executor chapter Go's `By(...)` runs),
with each named premise's claim obligation as a child closed against the
entry it names; emit renders the record back as the literal
`By(Normalized, At(<Entry>, w…), …)` — each premise the entry var the
registry resolves the name to (`ConvexDef` for a sibling, `vec_space.ZeroSmul`
across families), never the registered name as a string, and the statement
inline as `family.Theorem`'s first argument — what the session validated is
what the chapter Go says, 1:1.

**The deadline.** A `by` stops at its request's deadline — `probe`'s
`budget_ms` (default 1 s), `apply`'s `budget_ms`, a client that hangs
up. The executor polls between units of work and never before the first:
before each round over the working leaves after the first, each Arith
firing after the first on a leaf, each step of the shaping stage's
`Basic()` after the first (`Normalized`, `PreNormalized`, a denote), and
the ladder's conditioned rung, its run on the pruned leaf and the
bare retry; the CNF refuter reads the
same deadline itself, in its search, in the normalization that builds
its clauses and inside the one that keys the refute (seconds on a wide
leaf: measured, a `by` with `settac` held 10 s past a 5 s budget by the
key of a 186-hypothesis residual is cut off 0.2 s past it), and so does
the install of a named premise, in the rewrites
and unifications that read the premise against the leaf, and so does an
Arith firing, before each leaf of its decision (one decision can outlast
any budget: measured, a first firing still running at two minutes with no
deadline is cut off 2 ms past a 500 ms budget), and the arithmetic
decision the apply rung tries on an antecedent, the same decider under
the same poll (a rung asks it of every antecedent of every head it
weighs: measured, an arith `by` over three premises held 17 s past a
60 s budget by those trials is cut off 40 ms past it). So a unit in flight finishes — the overrun is that unit, 250 ms
past a 5 s budget on the measured step — and a close the first unit makes
is never refused, at any budget, with two exceptions. A named premise
that installs under a budget already spent is cut off before it has run
(measured on a close of 4 ms: `success` at `budget_ms: 50`,
`unknown(timeout)` at `budget_ms: 1`). And an arith close is cut off
where its budget is shorter than the close itself: the budget is the
budget, for the first firing as for the next. So is a close whose leaf
takes longer to key than the budget lasts: the cut-off reads `… was cut
off inside the pre-CNF normalization of the sequent, …`, and what it
says is that the leaf is too wide for the budget (§"Engine faults", "A
run its budget cuts off"). Each reads `was cut off`,
never as a close that failed. A `by` cut off fails with `By: the <closer> close was cut off
…` and releases the session; `probe` reports it `unknown(timeout)`, and a
`by` that fails inside its budget stays `fail`. A cut-off is no verdict on
the premises or the shape. One that reads `… was cut off inside the install
of premise <key>` names a premise whose install is the cost. An equation
installs as a rewrite rule, read from its larger side, and from the left
of its clause form where the two sides have one size; where that side is
headed by a bound variable — `function_module.FunAddDef`, installed as
`add(f(x), g(x)) = fun_add(add, f, g, x)` — no term of the leaf is passed
over for its head, and each unification against one runs to the unifier's
work budget, seconds a term (measured 1–10 s). Unfold such a definition
with `simp_with` (`Simp(Fwd(…))`), which reads it as stated, and leave it
out of the premise list. An `arith` close that does not close but whose
every firing rewrites the leaf (measured on `j - 1` and `COND`s inside an
opaque application) runs its rounds out on every rung, minutes, before it
fails, so its failure arrives as the cut-off at any practical budget; what
closed the measured step was the fact the closer needed (`j - 1 = n`)
asserted as its own step. Replay's `By` runs under no deadline — the
chapter Go's and a resumed session's.

**A proved section of the session is a premise by its STATEMENT**:
`with_lemmas:[{"text":"∀x:real. x ≤ x + &1"}]`, with `term_specialize` as
for any premise. `type_specialize`, or term witnesses binding the section's
type variables, can select a different type instance. The claim certifies
against the section's kernel proof. An explicit instance also carries the
derived clause Go's typed cite of the local installs — the section's
clause formed first, its types instantiated after — so it certifies as a
key premise's explicit instance does, a partial term tuple and source type
variables that become one type included. `emit-section` renders the cite as the chapter writes it — `By(lemma1)`,
`By(At(lemma1, f_0.Apply(c_0)))` — with no hypothesis cleared and no proof
inlined, so `cite_node` is not the road to a sibling section in a `by`. The
`key` slot names registry entries only; handed a node id of the session it
refuses, and the refusal carries the section's statement to paste.

**An ⇔ law is read as its two Horn clauses, and through a side that is
itself a law** (`u ∈ T ⇔ ∀x. x ∈ u ⇒ ∃δ. …` closes the radius at a point
from `u ∈ T` and `c ∈ u`), bare or grounded at its witnesses — see the
Playbook section "An ⇔ law with a quantified side". Close-or-fail with the
By premise-economy diagnostics (cleared-hyp list on a missing premise; the
CNF-MISS record-vs-Normalized split; unused trailing premises when the goal
closed early; the premise list beside the residual when a closer returns
with a leaf open; a note naming the set driver when a plain close fails on a
leaf that spells set vocabulary by name — `subset`, `union`, `big_union`, a
comprehension — which the refuter meets folded; and a note naming the plain
close when the set driver fails on a leaf that holds an equation between
sets, which the driver reads pointwise and the refuter keeps an equation:
two names of one set-builder whose predicate holds a set equation, `card(F)
≠ 0 ⊢ F ≠ ∅`).

**A premise that IS the leaf's statement closes it** (Lean's `exact`): the
context the list does not name is cleared, what is left is the entry's
statement, and that is the premise's claim, certified by the entry; where
the goal is that statement with no context to clear the composite has
nothing to do and the refusal names the move, `lemma` at that key.

**On success `by_closer` names the routes used by the successful attempt:**
premise installation, apply/conditioning, shaping, arithmetic, sets, chase,
the choice function of a hypothesis, CNF preprocessing without a key, a
cached CNF certificate, or a live refute; a close made by the conditioned
rung's run on the pruned leaf names that as well.
A branched close can name more than one route. Failed ladder attempts and
economy probes are excluded. The recorded `By(…; cnf)` still names the
configured closer, not this runtime result.

A `by` may also carry an economy finding, a diagnostic of type
`by_economy`: a leaf the close sent to the refuter closes under a plain
`Basic()`, and the same `by` with `by_shape:{"normalized":true}` was run
and closes on fewer rows than this close touched (the finding gives both
counts) — the economy audit's first probe (S7), read here before any blob
is written. A respelling that leaves a leaf open, or that reads the same
certificates and plans, is not reported. Whether a shape element is inert,
and what a spelling costs across a re-record, stay the recorder's to say
(`by_records`, next, reports this one close's own rows).

**On success `by` also carries a `by_records` diagnostic:** the rows the
recorder would write for THIS close — the certificate keys its refutes
wrote (a live refute) or read (a cached certificate) and the conditioning
plan keys the stage persisted or applied from the store — as `Records 1 key (prop_…), 1 plan`, or
`Records nothing` for a keyless close (the apply rung, a shaping, a
prelude close, arith/chase). It answers, before any blob is written, the
question the session's close could not: does this leaf cost a recorded
key or a plan. It is the SESSION's close. Where the member's Go spells a
DIFFERENT premise list than the session transcript — a grounded cite
folded into a resident `Have`, a guard the apply rung reads βη-resident
here but the refuter meets folded in Go — the two record different rows.
On the SAME spelling the two install the same premises: a key premise
whose `term_specialize` binds every binder of the law (or one under
`type_specialize`) is an explicit instance, and it carries the clause
form Go's `Law.At(…)` carries — the law's normalized statement at the
instance, Normalize first and the types after — so a witnessed ⇔ law
installs that form in both (its function equations pointwise), and the
recorded step carries it for emit's CNF collector. So does a law read at
an instance entry (`read_at {key}`) whose witnesses pin a type letter the
instance leaves loose: it carries the clause Go's `At(Law.Read(Entry),
w…)` carries, the reading's normalized form with its stated ∀-order, at
the instance's types. The recorder's dry run
(`XUGO_RECORD_CNF_DRY_RUN=1`, which runs the member's Go) is the
keylessness oracle for the member until the Go and the session read one
conditioning input.

**A `by` whose close fired the divergence whistle carries a `by_whistle`
diagnostic** in its `apply` response — `by_induction` too, and a closing
`probe` as its `by_whistle` field. The whistle cuts a search at a backstop: a case
analysis that reaches 512 open leaves is refused whole (nine hypotheses
`A ⇔ B`, `A ∨ B` or `A ⇒ B` whose sides nothing decides are 2⁹), and a
simplification branch or a rewrite that keeps re-containing what it came
from is cut as divergent. The search goes on with what is left, and the
close stands: a cut costs a simplification, never soundness. The
diagnostic lists each cut with the `by` it ran under, what was refused,
and the statement — for a refused case analysis the goal the analysis
was entered with, which is the one to read, and not the leaf that
happened to reach the count. A cut is a function of the goal it is made
at, so a replay of the same step meets it again, and the recorder
refuses a member whose replay fires the whistle (§"The recorder's two
gates"): the spelling does not record as written, and this is where to
change it — fewer premises, a quantified premise grounded at the terms
the goal needs, the intermediate fact as a step of its own. The cuts
listed are those of the rungs a replay of the recording runs: the bare
probe and the conditioned rung; the probe and the conditioned rung's
run on the pruned leaf when that run closed after the first failed;
the bare retry alone when that rung closed after the
conditioned one failed; every rung's when the close came after a
refutation of the conditioned rung ran to budget, since either rung
can then be the one recorded. A cut reported more than once is
listed once with its count, the first five cuts are spelled out, and a
statement past 4000 characters is cut there. It is the SESSION's close,
as `by_records` is: where the member's Go spells a different premise
list, the recorder's run is the oracle, and a close that reports no cut
is not thereby promised to record. A `by` that fails reports no cut, and
`batch-apply` returns none of a `by`'s diagnostics. The serve's stderr
carries every cut of every session, one `[whistle]` line each, naming
the `by` it ran under when it ran under one.

**Unapplied-witnesses contract** (unconditional): a witnessed premise whose
∀-form install absorbs the goal fails with *"closed the goal at its ∀-form
install, so its witness tuple was never applied"* — the tuple would
otherwise be unchecked text. The fix is the message's own: cite that premise
BARE — the same contract `Cite(dep, w…)` has always enforced with
*"witnesses are unused — cite bare instead"*. Every path runs it — sessions,
replay, the recorder — with no flag: a full replay panics on any remaining
site, and the corpus has none. Consequence for authors: under strict, a
premise list's ground/bare split faithfully marks which instances the closer
actually consumes.

**The apply rung runs first** (prover/proof/apply_close.go): before any
closer, `by` tries to close the leaf by APPLYING a resident law or a named
premise's stated form whose telescoped conclusion (binders through guards,
antecedents, conclusion) matches the goal, discharging antecedents by
assumption — an antecedent resident up to βη counts, exactly as the
conclusion is matched up to βη: the big-operator sugar lowers `Σ_{i∈k} u(i)`
to `real_sum(k, λi.u(i))` while a `real_sum` law binds the bare `u`, and the
two are one fact (a dry run that read antecedents α-only would leave such a
leaf to the refuter) — Lean's `apply h; assumption`, keyless and recorded
nowhere.

**The rung's identity is βη, the membership reading, the record reading
and the numeral reading**: a membership in an identity-form set-builder is its condition at
the point, `x ∈ {p | φ}` read as φ[x/p] (`tactic.MembershipNormal`, the set
driver's own unfolding of set_member, set_comprehension and
comprehension_spec with the ∃-one-point fusion, taken as one
normalization), and a record projection of a packed value is the part,
`mk_r(c).carrier` read as `c` through the record equations
(`tactic.InstanceNormalTerm`, the form of S5), and a statement is read at
its numerals, `X(2 + 1)` as `X(3)` and `0 < 2` as ⊤ (`omega.NumeralNormal`,
what SA's row says it reads and under which policy), the three readings
taken to a joint fixpoint (`rungReader.reading`), on both sides of every identity the
rung takes — the goal against a hypothesis, a guard against a fact — and,
where no reading of a head matches the goal as spelled, on both sides of the
match too (the head's telescoped pieces and the goal in the normal form; a
goal read against a head whose set is a binder, `y ∈ s`, would match nothing
the spelling matches, so the spelling is tried first) — and in both
directions: the guard `u ∈ {p | polynomial_over(c, p)}` is supplied by a
resident `polynomial_over(c, u)`, the guard `x ∈ {i | i ≤ n}` by a resident
`x ≤ n`, a goal `P(a)` closes on a resident `a ∈ {p | P(p)}`, a law
concluding `y ∈ {x | P(x)}` applies to the goal `P(a)`, a guard
`x ∈ ⟦a, b⟧` of a constant declared to read its membership is supplied by
the resident bounds, and a cited law's
guard `x ∈ hom_set(…)` is supplied by a resident `x ∈ V.carrier` at the
packed `V` whose carrier that is. The kernel carries the statement across
the reading: where a leaf closes up to it, the leaf is read first — its
memberships through the definitions' bridge (`MembershipRead`, prover/tactic
`MembershipReadTactic`), its record projections through the record
equations (`RecordRead`, `InstanceNormalTactic`), a step a reading — and
the assumption step closes what is then resident up to βη. A membership in
the three-part form is read to its ∃: `x ∈ {s * m | s, m | s ∈ S ∧ m ∈ M}`
is `∃s m. (s ∈ S ∧ m ∈ M) ∧ x = s * m`, so the goal spelled so closes on the
membership and the membership on the goal, keyless — and no further: the
witnesses of that ∃ are the author's (`Witness`, the set driver), as every
witness on the rung is. The match itself is up to η as well: a head whose
conclusion spells an abstraction where the goal spells the function, or the
other way round, matches — a witness pinned as `λT. ⋃T` meets a goal that
`def_expand` left at `big_union`, and a reading whose record part computes to
`λr x. r * x` meets a claim spelling `mul` — and the dry run reads the
kernel's instance back up to βη (the matcher's η reading,
`ext/unify.TermMatchApproxEtaWith`). Nothing else is read: a membership in a
union, an image or a named set stays as spelled (the set driver's), and a
set-builder spelled with surface constants that carry no definition is not
read. Measured: a fill of the polynomial module bridged the two spellings
with an iff Have (`∀q. q ∈ {p | polynomial_over(c, p)} ⇔ polynomial_over(c,
q)`) cited at five Cases, and the convolution chapter restated guards as
memberships in a sum's own index set.

**An antecedent is a goal of its own, closed by the same procedure one apply
shallower**: in the context, an equation between one term and itself (by
reflexivity — `f(zero) = zero'` read at `f := complex_of_real`), a
conjunction of supplied parts, a law opened (binders fixed, antecedents
assumed) to a supplied conclusion, or the conclusion of one more resident
fact — or one more named premise's stated form, installed where it fires —
applied with ITS antecedents held — so `∀N. P(N)` supplies `P(c)` and
`∀n. 0 ≤ n ⇒ P(n)` alike, and a chain of cited laws closes with each guard
supplied by the consequents before it; the rung closes what is two applies
away and no further, except that a STRUCTURAL apply — every antecedent it
leaves to close a smaller term than its goal, the carrier-membership
decision: `x * inv(x) ∈ c` by the closure of c under `*`, with `inv(x) ∈ c`
left to the closure under `inv`, from `x ∈ c` held — spends no depth, the
sizes bounding that chain, so a membership nested however deep closes from
the closure laws named as premises; and a witnessed premise's guard is read
the same way (see "A guard is SUPPLIED" under the Go surface). A goal the context already
holds closes by assumption before any head is read, and an antecedent that
IS the goal is never supplied to itself: a head asking for the goal makes no
progress on it (transitivity read at `R(a, c) ∧ R(c, c) ⇒ R(a, c)`, its
second antecedent closed by reflexivity).

**A conjunctive goal is split by the conditioning stage**: each conjunct is
a leaf of its own, conditioned and closed in its turn — by assumption, by
the rung, or by the closer on that conjunct alone, which records a
certificate for the conjunct that wanted a search and nothing for the
others. No `broadcast` is needed for it (`broadcast` declares a fan the
SHAPING makes — an ⇔ under `normalized`, a case split). A law that CONCLUDES
a conjunction is read, in turn, as the law it is for each conjunct
(`∀n. H(n) ⇒ P(n) ∧ K(n)` closes `K(c)` with `H(c)` held), since a split
goal meets it only so — and so is an ⇔ whose side is a conjunction, on
either side and at any conjunct: `∀d. d ∈ F ⇔ chain(R, d) ∧ c ⊆ d`
closes `c ⊆ s` with `s ∈ F` held, or supplied (through `G ⊆ F` and
`s ∈ G`, `set_basic.SubsetDef` named), and `has_size(P, n) ⇔ finite(P)
∧ card(P) = n` supplies a guard `finite(P)` with `has_size(P, n)` held. Two carve-outs: a `by` with a premise pinned by name
(`Where`) addresses one goal and is not split, and a bare attempt (`raw`,
and the ladder's first rung) reads the goal whole, so a certificate recorded
for the whole goal keeps closing it.

A polymorphic head is tried at every type instance the goal offers and then
— for a Horn law or an ⇔, at a goal carrying the head's own type variables
— at those variables themselves (the identity instance the enumerator
drops), planned, dry-run and committed on the terms of every enumerated
instance: the case of a structure law applied at its own hypothesis, every
leaf of an abstract chapter, and of a set law with a conjunctive antecedent
(`finite(t) ∧ s ⊆ t ⇒ finite(s)`, extensionality within a carrier) cited
bare at the chapter's own letter — which type letter a chapter happens to
use never decides whether a bare cite fires. A bare polymorphic premise is
such a head even where its clause form is its stated form (a law Normalize
leaves as it is, `∀s t u. s ∪ t ⊆ u ⇔ s ⊆ u ∧ t ⊆ u`): what the install
makes resident is ONE instance, the single type adaptation the closer
receives, and the head's enumeration reaches every instance the goal
offers — `set_order.UnionSubset` cited at sets of `prod(B, C) → A`, the
law's own letter inside the instance, among them. The closer receives the
install alone, so a leaf only a refutation closes at an instance other
than the install's needs that instance pinned (`type_specialize`, a typed
`.At`, `.Inst`, `.Read`). So a law stated for an
arbitrary operation/predicate/relation
(`∀op. monoidal_op(op) ⇒ ∀f p s. … ⇒ iterated_op(op, s, f) = …`) closes its
instance BARE — at an operation that is a variable or a partial application
of a constant alike: the head `add(x, y) = add(y, x)` reads
`vec_add(add₀, u, v) = vec_add(add₀, v, u)` at add := `vec_add(add₀)`, the
matcher's first-order approximation binding a flexible head to the target's
head applied to the leading arguments the pattern does not spell
(`ext/unify.TermMatchApprox`; measured at `polynomial.PolynomialModuleOn`,
where the same bare cite of `abelian_group.CommOn` that is keyless at
`module.RegularModuleOn`'s own `add` cost a key and a plan at `vec_add(add)`)
—
`by {with_lemmas:[monoidal.Bijection, real_sum.MonoidalRealAdd]}` — with no
`term_specialize`, no strip, no grounding: the goal spells the instance, the
context supplies the antecedents.

A failing `by` reports the rung's nearest miss ("matches the goal but
neither it nor the context pins every binder" / "its antecedent … is not in
the context"), which is the repair prompt: an ∃-antecedent must be opened
first (`strip_quant` with the `hyp_index` of that hypothesis — the session
twin of the Go verb `a.Unpack`), a relation only higher-order unification
would find must be named (`term_specialize`).

**A SPARSE `term_specialize` table pins binders by name for the rung**
(Lean's `apply law (R := r)`): when the named binders are not a prefix of
the stated ∀-chain — the usual case for a relation or predicate binder that
sits before the binders the goal spells — the premise installs nothing on
its own and enters the apply rung as a seeded head: the pinned binders are
substituted (β-reduced), the remaining binders are read off the goal's
conclusion and then off the context, every antecedent must be resident, and
the leaf closes by kernel apply, keyless. A named premise MUST fire — a `by`
whose pinned premise does not apply fails with the rung's nearest miss
(`with R := …, the conclusion of … reads …, which does not match the goal …`),
never falls through to the closer, and refuses `arith` and `raw`.

Emit renders it as `Where(<dep>, "R", <term>)` (`fact.go` Where). A PREFIX
table keeps its positional semantics: the premise is grounded at the tuple
and the rung reads the grounded instance as a resident head.

**A structure law read at an instance is a premise** — the Go
`law.Read(instance)`: `{"key": law, "read_at": R}`, with R one of
`{"key": instance entry}`
(`{"key":"comm_ring.MulLeftZero","read_at":{"key":"real_ring.CommRing"}}`),
`{"hyp_index": i}` (a resident structure fact of the goal — the hypothesis a
chapter stated over the structure holds), or
`{"key": projection law, "read_at": R′}` (a reading as the instance:
`comm_ring.MulLeftZero` read at
`{"key":"field.Ring","read_at":{"key":"real_field.Field"}}`). The premise is
the law's statement with its components pinned to the instance's and its
structure hypothesis discharged, derived by the kernel from the two
theorems, and `term_specialize` then names the READING's binders, the
component slots being gone; a witness is read at the reading's binder
with the hypothesis's letters fixed (`{"S": "∅"}` at `∀S:set(B)` under
a resident `module_on(R, M)` reads ∅ at the module's set(B), and a
tuple no reading of the binders takes is refused naming the binder,
the witness and the tie). A letter of the law that no component fixes
— the index letter `D` of `module.ModuleSumIn` — is the reading's own,
and where the instance spells the same letter (the chains, a free module
on `D → A`) the reading carries the law's under the prefix `♭`, `♭D`,
the mark of a lemma's letter held apart from the goal's; grounding the
index set at `num` then leaves the carrier's `D` alone. At an entry it
is a named premise like any other, bare in the clause form and witnessed
in the stated one, its claim certified by the derived theorem.

Under a resident hypothesis it materializes as Go's does: bare, asserted
ahead of every install with its claim closed from the derived sequent;
witnessed, that sequent installed exactly and grounded; either way the
engine keeps the hypothesis beside it, so `by_hyps` need not list it. A law
carrying a type letter its instance does not fix is cited as the law beside
the hypothesis, a tuple grounding the law at the hypothesis's components
and the table's witnesses together, each at the binder the law states it at
— what Go makes of it. `product_topology.ProductMapContinuous` states
`∀T S U V f g. continuous_map(T, U, f) ∧ continuous_map(S, V, g) ⇒ …`; read
at `continuous_map(T₀, S₀, f₀)` with `{"S":"S₀","V":"S₀","g":"identity_map"}`
it is the law at (T₀, S₀, S₀, S₀, f₀, identity_map). A tuple grounds a
prefix of the law's binders, so such a table runs far enough to hold every
component: `{"S":"S₀"}` there stops at V, stated before f, and is refused
naming V as the binder to give through; the bare reading and the table
through V both close. A table shorter than the reading's binders is the
reading's telescope at those binders — a hypothesis about them alone stands
ahead of the binders left — and certifies from the reading as the whole
table does.
The law is a registry entry by its key, or a PROVED section of the session
by its root's id — the id `add-goal` returned (`s<k>_g…`) or the one
`inspect` prints once it is closed (`s<k>_c…`) — a section stated over the
structure binder, read as an entry's law is (the `Read` entry); an open
section, or a node inside one, is refused naming it.
`text` and `type_specialize` are refused beside `read_at` (the law is named
by its key or its id; the reading's types are the instance's), and
`auto_with` refuses `read_at`.

Recorded as `ByPremiseProto.reading`; emit renders `Law.Read(Instance)`,
`Law.Read(ResidentHyp(…))`, `Law.Read(Projection.Read(…))`.

**An equation between FUNCTIONS reaches an ARGUMENT position through
the refuter when it stands alone or under a guard.** The normalizer reads
such an equation pointwise (`∀ẋ. f(ẋ) = g(ẋ)`, its η-expansion), which
rewrites an applied occurrence only; the refuter recovers the equation
itself from the pointwise clause (FUNEXT, `ext/clause/funext.go`), a
guard's literal riding along — and an equation that NAMES a function
value, `e = λx. T`, an obtained witness or a denotation (the name a
variable `T` does not mention; a vocabulary constant's definition,
`set_comprehension = λs. s` from the set driver's residence rule, and a
variable standing in its own value, `Q = λx y. Q(y, x)` from a
commutativity axiom, are not recovered: recorded, the one unfolds the
constant through the search and the other makes its own redexes), is
recovered the same
way and kept beside its pointwise form, so the name is reached where it
stands as an argument, `equivalence_class(R, e)`, as well as where it is
applied — so a `by` naming `vec_space.NeutralVecAdd`
beside the ring premise does rewrite `vec_add(neutral_elem(vec_add), u)`
and `‖iterated_op(vec_add, ∅, F)‖_n`. Inside a disjunction it does not;
there `simp_with` with the same entry rewrites it (the stated form,
unexpanded), and the residual then closes — the `Simp` route stays the
one that needs no premise beside the law. `vec_space.MonoidalVecAdd`'s third clause is
`Chain(Simp(Fwd(NeutralVecAdd)), By(AddLeftZero, ring))`;
`euclidean.NormIterateLe`'s ∅ case is one `Simp` over the fold clause, the
neutral's reading and the norm of zero. A Horn clause PACK
(`monoidal_op(op) ⇒ eq₁ ∧ eq₂`) is split into one conditional rule per
conjunct by the driver. Prefer `by` over `auto` on any deduction leaf whose
premise list you know; `auto`/`auto_with` remain the search moves.

#### `by_induction` — Go `ByInduction`

**Go's `ByInduction` as a session move** (`prover/proof/induction.go`):
induction by CITING a principle.
`{"type":"by_induction","lemma":{"key":"<principle entry>"},"by_hyps":[{"hyp_index":0}]}`
— the principle is an entry named by key, and its predicate is read from
the goal: the goal abstracted over the index, which the `by_hyps`
hypothesis that states the principle's guard fixes (`finite(T₀)` for
`finite_set.FiniteInduct`, the relation's own hypothesis for a rule
induction, which fixes the parameters too); with no such hypothesis named,
the goal has to be the principle's conclusion `∀x̄. guard ⇒ φ(x̄)`, and its
body is the predicate (strong induction at `∀n. φ(n)`). A predicate that is
NOT the goal — an induction on a degree or a cardinality, a claim
strengthened for the induction, hypotheses the induction has to carry — is
written: `"term_specialize":{"P":"λn:num. …"}` grounds the principle at a
PREFIX of its stated binders in their names (the parameters stated before
the predicate, the predicate; the indices after it too if the author grounds
them), which is the tuple Go's `At(principle, w…)` writes positionally, and
a table that stops before the predicate (the parameters alone) is read from
the goal like no table. Optional `by_hyps` / `with_lemmas` are the extras
the conclusion needs (a guard's hypothesis), `by_shape` the shaping
(`{"normalized":true}` for a deep transparent predicate, as the Go verb's
`Normalized`). The engine reads
the principle's case obligations off its statement at that tuple
(`proof.InductionObligations` — the Go verb's own reading), asserts each,
and closes the goal by a `by` over the asserted obligations, the extras and
the principle in its STATED form grounded at the tuple.

**What stays open is one leaf per obligation**, under the principle's own
binder names, each the case the author proves next; the terminal either
closes or the move fails with the By diagnostics and nothing is applied.

Recorded as the shape Go's verb records — one assert per obligation, then
the by — and `emit-section` renders it back as
`ByInduction(At(<principle>, pred…), extras…, Case("case_<i>: …", …)…)`, the
labels carrying the numbered tag the lint refuses until each is restated.
Where the recorded predicate is the one the goal reads — whether the table
wrote it or left it out — the cite is rendered before the predicate,
`ByInduction(<principle>, extras…, Case(…)…)`: the member does not state its
goal twice.

Refused: a text principle (an entry certifies the terminal's claim), a
sparse table (the obligations need the prefix), an entry whose conclusion is
not a predicate applied to its index ("not an induction principle"), `arith`
/ `settac` (the terminal is the plain refutation). The route it replaces —
`lemma {key, term_specialize:{P}}` then `by` over the resident clauses —
installed the principle in the closer's clause form, whose merged prefix a
partial tuple misreads.

#### `elementarity` — Go `ByElementarity(source, facts…)`

**By elementarity: a proposition about a closed field, proved by
carrying a first-order sentence over from a structure where it holds
(elementary equivalence), or an iff read on both sides of an elementary
embedding.**
The goal is read as a sentence in the integer-polynomial language of
`first_order` (`prover/reify`: the formula, its names, its obligations
and a plan naming each node's lemma); the bridge `Φ ⇔
ring_formula_truth(F, φ)` is proved from the plan, one lemma instance and
modus ponens or congruence a node, with no refuter and no CNF key
(`prover/bridge`); the formula's closedness is proved the same way; and
the transfer theorem is cited. Every library theorem the executor reads
is the proof's own cite, so the member's recorded dependencies hold it;
the inequalities between block boundaries go to the arithmetic closer,
which records `arith:nat`.

**Parameters.** `{"cmd":"apply","session_id":S,"goal_id":G,"tactic":{"type":"elementarity","source":{"key":"<entry>"} | {"hyp_index":k},"facts":[{"hyp_index":i},{"key":"<entry>"},…],"terms":["<param>",…]}}`.

- `source` — an entry stating the property at a concrete structure (`∀n d.
  Φ(S, n, d)`, its binders the property's other arguments), or a resident
  family of models by prime, `∀p. nat_prime(p) ⇒ ∃G.
  algebraically_closed_field_on(G) ∧ field_characteristic(G, p) ∧ Φ(G)`
  (under `.At`, with the property's other arguments bound ahead of the
  prime, `∀n d. ∀p. … Φ(G, n, d)`); absent for the embedding mode.
- `facts` — resident hypotheses and entries the obligations are read
  from: the goal's structure as `algebraically_closed_field_on(F)` (the
  ring theory) or `real_closed_field(F, lt)` (the ordered theory); for an
  entry source in the ring theory, `same_characteristic(F, S)` (the
  source structure's closed-field fact is the corpus entry stating it,
  `real_closed_instance.RealClosed` for the reals, read by its statement
  where no fact names it); under `.At`, the parameters' membership facts
  and the property's other guards.
- `terms` — the fixed-parameter form `.At(params…)`: the source's
  property, unfolded, is instantiated at the terms, in the order of its
  ∀ binders, and its consequent there is the goal. The degree bound is
  CommonDegreeBound's, taken from each polynomial parameter's
  `p ∈ polynomial_algebra(field_ring(F), {i | i < n})` fact (a family's
  `∀j. j < k ⇒ P(j) ∈ …`); the property is transferred at it and
  instantiated, and every other guard is a fact. A polynomial in one
  variable is quantified by the property as the ring tuple of its
  coefficients, `ring_tuple(field_ring(F), n, p)`, and read at a scalar
  by `polynomial_eval(p, x)`; its length bound is TupleOfPolynomial's,
  taken from the parameter's `polynomial_over(F.carrier, p)` fact (one
  such guard per bound). A family of models is instantiated at the
  property's arguments so settled and transfers the property there.

The mode and the theory are derived from the goal and the facts, and
recorded beside the call; a replay that derives otherwise refuses.
Records ONE `elementarity` ministep (`StepProto_Elementarity`); emit
renders it back as `ByElementarity(<source>, <facts>…)` (with
`.At(<params>…)`), an entry as its Go var, a resident fact as
`ResidentHyp(<statement>)` or its handle.

**What it reads now.** The equivalence mode for algebraically closed
fields, from an entry or from a family of models by prime
(`lefschetz.PrimeFamilyTransfer`), and for real closed fields from an
entry; the fixed-parameter form `.At` from an entry or a family of
models; and the embedding mode for algebraically closed and for real
closed fields. With no source the goal is an iff `Φ(F,
params) ⇔ Φ(G, i(params))`, in either order: the facts give
`ring_homomorphism(field_ring(F), field_ring(G), i)`, both structures'
`algebraically_closed_field_on`, or both structures'
`real_closed_field(F, lt)` and `real_closed_field(G, ls)` (each side then
read with its own order), and each parameter's bound — a family's
`∀j. j < k ⇒ polynomial_bound(field_ring(F), n, d, P(j))`, a
polynomial's `polynomial_bound(field_ring(F), n, d, p)`, or, as `.At`
reads them, its membership `∀j. j < k ⇒ P(j) ∈
polynomial_algebra(field_ring(F), {i | i < n})` or `p ∈ …`, whose
CommonDegreeBound the step takes and discharges. Its images on
G's side are written `λj. λm. i(P(j, m))` and `λm. i(p(m))`. The
parameters are encoded in one environment, the two sides read at it and
at its image, and the theory's `EmbeddingElementary`
(`algebraically_closed_field_transfer`'s or
`real_closed_field_transfer`'s) cited; a scalar or a tuple
parameter is refused. A goal outside the reifier's grammar is refused at
the subterm it stops at (the grammar: `prover/reify`'s package doc); a
source whose sentence reads as another formula than the goal's is
refused with both formulas.

Linear algebra of symbolic size reads in every mode. A finite sum
`module_sum(F.add, F.zero, {j:num | j < k}, λj:num. t)` of scalar terms
(the record's parts written `F.add` or `field_ring(F).add`) is the
integer polynomial ring's sum over the same indices, carried by
evaluation's homomorphism (`polynomial_formula.IntegerPolynomialEvalHom`,
`ring_homomorphism.MapSum`) and closed by
`polynomial_formula.ParameterPolynomialsSumIn`; a family that is no
λ-abstraction, or an index set other than `{j | j < k}`, is refused. An
existential index `∃j:num. j < k ∧ φ` is read as `¬∀j. j < k ⇒ ¬φ`,
the negation of a finite conjunction. An index — of a coordinate, or of
a family's member — is a natural-number term of numerals and variables
under `+`, `*` and `suc`: `x(j * N + c)`, `Q(j * N + c)` of a family of
`r * N`, `x(i)` under `i < j` and `j < n`, `x(0)` of a tuple of length
1. The arithmetic closer (`arith:nat`) keeps it below the tuple's length
or the family's count, from the bounds of the index binders in scope; a
product `a * t` of a bounded index `a < m` reaches it as
`suc(a) * t ≤ m * t` (`nat_order.LessEqMul2`). An index it does not keep
below is refused at the coordinate or the member (`x(m)` of a tuple of
length `n`, `x(j + 1)` under `j < n`).

#### `lemma`

Apply a lemma to the goal. Best-effort multi-strategy: tries `IsStronger`
close, then equational rewrite (size-monotone), then
`lemmaConclMatchTactic`, then `lemmaHypMatchTactic` (which adds the lemma as
a new hypothesis when nothing else fires).

**Parameters.** `lemma`: PropInput — `{"key": "…"}` (a registry entry,
preferred; **the key slot takes the entry's own `prop_…` key or its
registered name (`pairs.Fst`)** — nothing else; name matching is EXACT and
case-sensitive. The cited entry certifies its own reproduction child —
`⊢ <its statement>` at the instance the install adapted to closes on the
cite, whichever spelling named it. Same spellings in
`by`/`auto_with`/`simp_with` `with_lemmas[].key`: an entry serves its own
statement) or `{"text": "..."}` (ad-hoc DSL). **`term_specialize` and
`type_specialize` are SIBLINGS of `lemma` at the tactic level, NOT members
of the `lemma` object** —
`{"type":"lemma","lemma":{"key":"prop_…"},"term_specialize":{"x":"x_0"}}`.
Nesting either one inside `lemma` (the reading this column's prose invites,
and the natural guess since `key` lives there) errors with
`unknown object member name "term_specialize" within "/tactic/lemma"`, which
reads as "this tactic has no specialize" rather than "you nested it one
level too deep". Optional
`term_specialize: {"<binder_name>": "<witness_text>", …}` pre-instantiates
the lemma's outer ∀-binders before installing the hyp; optional
`type_specialize: {"<typevar_name>": "<type_expr>", …}` pre-substitutes the
lemma's free type-vars

**A goal that IS the cited entry closes on the cite**: a hypothesis-free
goal equal to the entry's (or the card's) statement modulo Normalize — its
contrapositive, its binders in another order, its type variables under
other names — comes back `effect:"close"`,
as Go's `Cite(X)` closes it; the entry is not installed as a hypothesis
beside a goal it already proves.

**Hypothesis-preserving**: every pre-existing hyp survives the apply — in
particular, ground instances you built with `instantiate` are NOT
re-absorbed into their ∀-forms by a later lemma load (a result that would
rewrite/drop an existing hyp is downgraded to the plain add-as-hyp). The
lemma may still rewrite the goal's CONCLUSION (the documented size-monotone
eq path), so a `trans` middle term can still be rewritten away — load
rewrite-capable lemmas before `trans` if the middle must persist. Use this
when you're unsure how the lemma should engage. For an explicit directional
rewrite that doesn't fall back to "added as hyp", use `lean_rw`.

**Optional `term_specialize` parameter** pre-substitutes the lemma's outer
term-level ∀-binders before install — selected by NAME, not position. Map
keys are ∀-binder names read off the member's statement (what `query member`
prints for it); map values are witness terms parsed via the text-DSL against
the goal's scope. The engine installs the lemma + grounds the residual's
installed ∀-hyp via ONE composite `specialize` ministep (only the final
instance lands; the source ∀-hyp is consumed; no intermediate partial hyps),
leaving the (partially or fully) specialized ground instance on the residual
leaf with no ∀-residual to refute-poison `auto`. Peeling proceeds
outside-in: at each outermost ∀-binder, if its name is in the map the engine
peels it; if NOT in the map, peeling stops there. Every map key must be
consumed — an unmatched key (typo, or named binder lives below a
non-specialized outer binder) is a hard error.

**Polymorphic binders are handled automatically**: when a binder's type
contains a type variable (e.g. `∀P:(A→bool)→bool. …`), the witness's
concrete type is unified against the binder type and σ_type extends to the
rest of the lemma — the agent does NOT need a companion `type_specialize`
for the binder's vars. Mirrors LEAN `apply h (P := λs. …) (a := empty_set)`
ergonomics. **A witness that is a bare polymorphic constant is read at
its binder's type**: `∅`, `𝕌`, `identity_map` carry the constant's own
fresh letters, which nothing in the text pins, and the binder they
ground is their expected type — as Go's `TermAs[Set[B]]("∅")` reads
the same text at its phantom's — so `{"S": "∅"}` at `∀S:set(B)` reads
∅ at set(B), `{"s": "𝕌"}` at a binder already read at set(num) reads
𝕌 at set(num), and `{"f": "identity_map"}` at `∀f:(B → C)` reads it at
`C → C`, binding the lemma's B to its C (`proof.FitWitness`,
`dsl.ReadTermAt`). The witness then spells the lemma's letters as the
instance does, apart from the goal's where the goal spells them (the
own-letter rule above). A witness that fits its binder no way, or
carries a letter the binder does not fix, is refused naming the
binder's type, the witness's, and the `⟨A:τ⟩` tie that pins it.

**Optional `type_specialize` parameter** pre-substitutes the lemma's free
TYPE variables before install — the type-level counterpart of
`term_specialize`. Solves "lemma loads at the wrong type-pair": when a
polymorphic lemma (e.g.
`set_basic.InImage : ∀s f y. … ⇔ set_member⟨A:var:B⟩(y, image(f, s))` with
type-vars `A`, `B`) is needed at multiple type-instances in one goal (the
`IMAGE_o` pattern — three IMAGEs at three distinct `(source, target)`
type-pairs), the default goal-context matcher pins both type-vars to ONE
pair, blocking the other two uses. With `type_specialize` the agent
explicitly directs each load:
`lemma(set_basic.InImage) type_specialize={A: "?71152", B: "?71148"}`
produces a hyp specialized to that pair. Map keys are the statement's type
variables — the letters in the binder types of the member's statement
(`∀f:(A → B).` has `A` and `B`; `statement_typed` types every binder). Map
values are type expressions parsed via the type-DSL (`num`, `bool`,
`num→bool`, `var:A`, or `?71143` for the printer's Skolem form).

**An explicit `type_specialize` is honored EXACTLY**: it disables the
install path's speculative goal-context adapter entirely, so the σ target is
never re-bound to the goal's type instance (a silent override — σ requested
at `?27845`, hyp installed at `?27847` — is fixed) and any type-var NOT
pinned stays polymorphic in the installed hyp (it is NOT
goal-context-inferred; pin every var you need concrete), under a letter of
its own: one whose name the goal also spells is renamed apart (the first
uppercase letter neither the goal nor the instance uses), never read as the
goal's letter. Unknown key (typo)
or unparseable value is a hard error — never silently dropped. Both
`term_specialize` and `type_specialize` are independent and compose:
`type_specialize` fires first, then `term_specialize`. The cited entry is
still recorded as `polymorphicSourceKey`, so dep extraction still points at
the polymorphic entry. Mirrors LEAN `apply @h (A := T) (B := U)` ergonomics.

**Type vs term — don't conflate**: `type_specialize` keys are TYPE variables
(the letters in the statement's binder types); `term_specialize` keys are
TERM-level ∀-binders (the `∀P.` / `∀a.` chain on the conclusion). A typo'd
key surfaces with `available: […]` listing only the relevant domain.

**A structure law read at an instance is cited with `read_at`** — the Go
`Law.Read(instance)` as the `lemma` slot's entry:
`{"type":"lemma","lemma":{"key":"comm_ring.MulLeftZero","read_at":{"hyp_index":0}}}`,
the instance an entry `{"key":…}`, a resident hypothesis `{"hyp_index":…}` or
a reading `{"key":…,"read_at":…}` exactly as on a `by` premise or a
`simp_with` rule (the `by` row; `engine/reading.go`). The reading is the
law's statement with its components pinned to the instance's and its
structure hypothesis discharged, derived by the kernel. A goal the reading
proves — stronger than it, or the same proposition modulo Normalize —
closes on the cite, as Go's `Cite(Law.Read(h))` does, `effect:"close"`,
recorded as a known theorem carrying the reading and emitted
`Cite(<Law>.Read(<fact>))`. Any other goal has the reading brought to bear
as `lemma` brings any lemma and as Go's `Cite` does: an equational reading
whose left side occurs in the goal REWRITES it (the size-monotone eq path
above); any other goal has the reading installed as a resident hypothesis
for the moves that follow (`strip_quant {hyp_index}`, `split_conj
{hyp_index}`, a `by` naming it), as an entry's `lemma` install does — the
install exact at the reading's types, its claim child closed from the
derived theorem, the hypothesis the reading is under kept beside it,
emitted `Cite(<Law>.Read(<fact>))`. The reading's letters are the
instance's; a letter the instance leaves loose — a polymorphic instance
ENTRY's, `symmetric_group.SymmetricGroup` is `group⟨A:permutation(A)⟩(…)`
— is pinned off the goal when the cite is bare and off the tuple when it
is witnessed, as a `by` premise's is, and a hypothesis's letters stay
rigid. A `term_specialize` PREFIX of the reading's binders grounds the
installed hypothesis at the tuple and drops the ∀-source, emitted
`Cite(<Law>.Read(<fact>), w…)`; an install whose chain closes the goal at
the very instance the tuple names is accepted as Go's witnessed Cite
accepts it, and one whose chain rewrote the goal is refused, naming the
rewrite and the roads: the bare cite takes the rewrite, a `by` premise at
the tuple (`with_lemmas:[{key, read_at, term_specialize}]`) brings the
instance to bear, `lean_rw` rewrites on purpose, and an `assert` of the
instance closed by that premise leaves it resident. Refused by name:
`text` beside `read_at` (the law is an entry or a proved section, named
by its key or its id), `type_specialize` (the reading's letters are the
instance's, or pinned off the goal or the tuple), a sparse table (a
binder pinned by name is a `by` premise's `Where`).

#### `cite-node`

**Session-internal lemma reuse.** (The one hyphenated wire type in a
snake_case table; `cite_node` is accepted as the same tactic.) Install the
conclusion ψ of a previously-closed node in THIS session tree as a hyp at
the current focus, *without re-searching to re-prove ψ*. Mechanically:
`assert(target.Concl)` whose first (claim) child is materialized from the
cited node's cloned proof subtree (miniStep + subGoals + provedThm,
re-parented). Replay sees a regular `assert` with a fully-proven first
branch — no new ministep variant, no proto change, no new replay path. A
DEFINITION section (a `define` composite at its root, any payload) is cited
as a KNOWN THEOREM instead: the claim child closes by the section's promised
theorem, never by inlining the composite, so the emitted member cites the
definition's entry (`Cite(<Const>)`, the variable the definition lands as; a recorded dep) — the
one use path for the spec and typedef shapes, which install no rule.

**Soundness gate (engine-enforced)**: `target.Proved()` must hold AND
`target.Goal.AllHyp(focus.HasHyp)` — the target's hyp context must be an
α-equiv subset of the current focus's hyp context (the same
`IsStronger`-composable predicate `lemma` uses). Discover citable targets
via `inspect`'s `closed_subtrees` field (entries carry `node_id`,
`statement`, `hyp_count`, `depth`, `section_id`, capped at 50). Distinct
from `lemma`: cite-node references a session-internal sub-derivation by
node-id; `lemma` references a registry entry. Distinct from `assert`:
cite-node short-circuits the first branch via the cited proof; `assert`
opens it as a new obligation.

**When to use**: sibling sub-goals (from `split_conj` / `case_split` /
`split_disj` / induction step-cases) share a non-trivial intermediate lemma
— prove it once in the first branch, cite-node it in the others. Under the
per-leaf dispatch model the orchestrator rarely produces multi-branch
sessions where this fires; most sessions stay one-goal-deep and
`closed_subtrees` stays empty. The mechanism comes alive when a single
session's proof tree branches (the agent's OWN `assert` chain across
`split_conj` sub-goals is the typical case, not cross-target).

**Cross-session grafting**: when `node_id` isn't found in this session, the
engine consults the serve-global closed-derivation pool — every sequent any
session of this serve process closes is published there, keyed by the
sequent's canonical content hash (the `<hash>` part of the id; the `s<N>_`
prefix is session-local presentation and is ignored). Same soundness gate,
same recorded step structure — the cited subtree is inlined into the
assert's first branch, so stored decompositions replay without the pool.
This is the merge layer for parallel divide-and-conquer proving: sub-agents
prove phases in separate sessions and a collector session cite-nodes their
results by id. Pool entries are LRU-capped; a miss just means re-prove
(never an error class of its own).

#### `def_expand` — Go `Unfold(<definition>)` / `DefExpandStep`

Expand a definition.

**Without `hyp_index`, the goal AND every resident hypothesis** —
`{"type":"def_expand","const":"subset"}` is the step Go's
`Unfold(set_basic.SubsetDef)` records, and emit renders it so: the
session names the constant, the chapter the entry that defines it. It opens the constant in the goal and in
every resident hypothesis that mentions it, and its tidy (below) splits a
resident conjunction into its conjuncts, so the hypotheses after the step
are renumbered: an index read before it names another hypothesis after it.
The response's `context_changed` diagnostic lists each original hypothesis
the step rewrote or removed, by its old index; `inspect` the leaf for the
current indices. To open the goal alone, rewrite it by the definition
entry with `simp_with`
(`{"type":"simp_with","with_lemmas":[{"key":"set_basic.SubsetDef"}]}`, Go
`Simp(Fwd(set_basic.SubsetDef))`), which touches no hypothesis; to open one
hypothesis alone, `hyp_index` (next). A goal-level `def_expand`
transcribed as that `Simp` leaves the rest of the proof a different
context: transcribe it as `Unfold`, which is what emit writes.

**With `hyp_index`, in ONE hypothesis** —
`{"type":"def_expand","const":"real_converges_to","hyp_index":0}` opens the
constant in that hypothesis alone: the unfolded statement joins the
hypotheses beside the folded one, the goal and every other hypothesis
untouched — the session twin of the Go verb
`a.Unfolded(fact, <the definition>)`, recorded as the verb records it (an
assert of the unfolded statement whose claim child the unfold closes) and
emitted `fact := a.Unfolded(<fact>, <the definition's entry>)`. The statement is computed by the
def-expand walker on the hypothesis (`proof.UnfoldedHypothesis`), so no text
restates what the engine holds; `new_hyps` reports it. Refused, naming the
cause: a hypothesis that does not mention the constant, a constant with no
definition to open, an opening that changes nothing, an index out of range.

**Refused on a constant of the logic itself** — `⊤`, `⊥`, a connective,
the conditional, `∀`, `∃`, `∃!`, the constants the logic defines before
any chapter (`ext.InitConstMetaMap`). No chapter entry defines one, so the
Go a member is written in has no definition to name for it, and the
session offers no step its emitted member could not spell. The refusal
names what reads the constant instead: the move made for it —
`strip_quant`, `witness`, `instantiate`, `split_conj`, `split_disj`,
`strip_imp`, `case_split` — or a closer, which reads `∃!` through
normalization: `by` with a `∃!` fact as a premise has its existence and
its uniqueness, and its witness is named by an `assert` of the ∃
statement closed by the fact, then `strip_quant`. `inspect` and the
recommendations never offer the move for these constants.

**Refused on an inductively minted relation** (finite, is_num, is_recspace,
anything `define inductive:` minted): the closure form is not a proof
surface, and the refusal names the relation's Rules / Induct / Cases
theorems — `cite-node` those.

**Pure rewrite semantics** — uses the same path as `lean_rw` (including
bidirectional retry) to rewrite occurrences of the const in place, in the
goal and in the resident hypotheses (above). Works for directly defined consts (`c = λx.body`, the common case)
regardless of whether the definition states it as `c = body` or `body = c`.
When the rewrite path doesn't fire (e.g. for a type definition's `mk_T` /
`dest_T` pairs whose def thms have the form `∀r. P(r) ⇔ dest(mk r) = r` —
there's no subterm to rewrite), returns clean failure rather than silently
adding the def thm as a hypothesis. A const whose definition is a Hilbert
choice (`c = εx.P(x)`, with or without parameters: the specification and
recursion mints, a chapter's `c = εx. P(x)` definition) is opened like any
other — `c` becomes its ε-term, and the tidy's normalizer reads the opened
`P(εx.P(x))` as `∃x.P(x)`, so with the existence resident the leaf `P(c)`
closes. "c is chosen among the x with P, and some x has P, so P(c)" is an
`assert` of the existence and this step, in the session as in Go
(`a.Have("…", "∃x. P(x)", …)` then `Unfold(<c's definition>)`). Without the existence the
opened ε-goal stands, for `hilbert_denote` or a `by` under its ε-denoting
shaping. The reading that keeps `c` folded and hands the two obligations over
as cases, `⊢ ∃x.P(x)` and `Γ, P(c) ⊢ G`, is the chapter step
`ExistentialConstDefStep(c, Case(…), Case(…))` (§"The Go Script API
surface"); no session command records it.

The step records no simplification of its own: the session and the chapter
form (`Unfold`) record one tree. The
post-expansion tidy (`tactic.UnfoldTidyTactic`: β, the connectives, a
resident conjunction split, a leaf a hypothesis states closed — and no
resident fact read into the goal, which is the author's `rw` or `by`;
§Playbook, "The tidy after an unfolding applies no resident fact") never
swaps a COND outward THROUGH a λ (the direction
`(λx. COND(b, f(x), g(x))) = COND(b, λx. f(x), λx. g(x))`): a COND of
predicates under a binder would otherwise cycle with the quantifier rule's
η-expansion — `∀ P` ⇄ `∀x. P(x)` — without bound, which is what killed the
serve on `def_expand(iterate)` at a fold whose summand carried a COND (and
on ANY failing apply there, since the repair-hint probe reaches the same
expansion). The swap fires one level down, at the application. Pinned by
`engine.TestDefExpandIterate_CondSummandTerminates` and
`prop.TestCondSwap_UnderBinder_Terminates`;
`XUGO_DEEPREWRITE_TRACE=count|trace` on a serve prints the plain rewriter's
fire counts / the divergent call's fire log to stderr.

#### `induction`

Structural induction on a variable of an inductive type. Supported types and
their case splits: `num` → 2 subgoals `P(_0)` / `P(n) ⊢ P(suc(n))`;
`list(A)` → 2 subgoals `P(nil)` / `P(t) ⊢ P(cons(h, t))`; `option(A)` → 2
subgoals `P(NONE)` / `P(SOME x)`. Number/shape of subgoals matches the
inductive type's principle. The named var can be bound by an outer ∀ on the
current goal (tactic auto-peels) or an in-scope Skolem constant — either
works.

**`const` names the variable as the goal prints it or by its surface
name.** A strip subscripts every ∀-binder of the conclusion, the ones it
leaves bound among them: after `strip_quant` and `strip_imp`, `∀m. m = m ⇒
∀k. k * m = m * k` reads `m₀ = m₀ ⊢ ∀k₀. k₀ * m₀ = m₀ * k₀`. `"const":"k₀"`
(or `k_0`) names the binder, and so does `"const":"k"`, the name the
statement gave it — the surface name every claim and term text of the
session takes (`inspect`'s `surface_names`), read here for a free variable
and for a binder of the leading ∀-prefix alike. A variable literally named
by the spelling owns it; a surface name two variables of the goal share
(`k₀` free beside a bound `k₁`) is refused listing them, and each is then
named as printed. A name that is no variable of the goal is refused
listing the goal's free variables and the binders of its leading ∀.

**The step case arrives as the principle states it** — `P(n) ⊢ P(suc n)`,
the IH a hypothesis, nothing simplified: a `≠` goal is NOT contraposed and
an implication's antecedent is NOT moved into the hyps. `by` takes the case
as is (its conditioning stage and the refuter handle negated goals); an
agent wanting the shaped form records it with an explicit `simplify`,
exactly as a Go author writes `TrivialSimplify()`. This is what the chapter
verb `a.Induct` records, so a session and its landed twin agree on every
induction.

**Stripping the statement's OTHER binders first is a choice about the
induction hypothesis, and it decides the closer.** Induct with them still
∀-bound and the hypothesis is ∀-quantified: `rw` refuses it (a rewrite takes
a ground equation), and it is consumed by a `by` that names it —
`By(Normalized, ih)` in Go, usually at the cost of a key. Strip them first
(in Go, the closure's typed parameters) and the hypothesis is ground at
exactly those variables: `rw {hyp_index}` / `ih.Rw()` fires it with no
search. Take the quantified hypothesis only where the step needs it at
ANOTHER instance; a statement with one binder has no choice to make.

#### `instantiate`

Ground the ∀-hyp at `hyp_index` (required — use `inspect` to locate it). Two
forms, both recording as ONE composite `specialize` ministep.

**Multi-witness `terms` form**: `{"hyp_index": i, "terms": ["t₁", …, "tₖ"]}`
grounds one binder per term in the hyp's stated order, a binder behind an
antecedent included, as Go's `fact.At` reads it (`∀c. c ∈ s ⇒ ∀ε. …` at
`["y", "e"]` adds `y ∈ s ⇒ …[y, e]`, the guard kept); only the final ground
instance is added (no intermediate partial hyps, so no index re-inspection
between rungs) and the source is CONSUMED (Lean `specialize h t₁ … tₖ`
semantics; `specialize` alias works). Pass `keep: true` to keep the source
resident (e.g. it will serve another witness tuple later).

**Single-witness `const` form**: `{"hyp_index": i, "const": "t"}` peels ONE
outer binder; source KEPT by default (set `keep:false` to consume). The two
forms are mutually exclusive.

**Type adaptation is automatic**: when a witness's type doesn't equal the
binder's but the binder type MATCHES it under a substitution σ of the hyp's
type vars (the classic wall — hyp `∀x:list(var:A). …` loaded from a
polymorphic entry vs Skolem witness `l₀:list(var:?27361)` minted by
`strip_quant`), the engine re-derives the hyp at σ from the registry entry
whose statement it is and grounds THAT — no re-load, no manual
`type_specialize` round-trip. σ accumulates across the witness list
(`terms[0]` can pin `A`, then `terms[1]`'s binder is matched post-σ). The
stale hyp is REPLACED: with `keep:true` the kept ∀-source is the σ-instance,
not the original named-var form.

Recorded as `clear_hyps` + `lemma_preserve` (the entry's key as
`polymorphicSourceKey`) + `specialize`; the σ-instance claim child closes
through the type-instance channel against the entry — all existing
ministeps, replay-transparent. If the σ-instance outright PROVES the goal
(the conclusion is itself an instance of the adapted hyp), the apply reports
`Effect:"close"` instead of adding a hyp.

**Bound**: the hyp must be an entry's statement (its normalized key is a
registry entry's own key, not the session's target; a hyp's type vars are
sequent-scoped, so there is no per-hyp kernel type instantiation) — a
derived/mid-ladder hyp fails LOUDLY with the computed σ and the manual
recipe (re-load via `lemma` + `type_specialize:{…}` and redo the ladder).

#### `rw` — Go `f.Rw()` / `Rw`

**Directed equality-hyp rewrite to fixpoint** (Lean `rw [h] at *`). Given
the equality hyp `(a = b)` at `hyp_index`, rewrites `a→b` (or `b→a` with
`flip: true`) across the conclusion AND all other hyps, descending into
every subterm position — relation-atom arguments (`≤`, `<`, …) and opaque
function arguments (`dist(m,n)`, `dest_nadd(x,·)`) included — repeated to
fixpoint. One subgoal; the equality hyp itself is kept as it stands, in
either direction (`flip` rewrites with it and leaves it `a = b`). With no
occurrence of the oriented left side outside the equality itself the step
does not apply — it is not a way to turn the hypothesis round. Subsumes the
manual `congr_arg`-per-layer / `subst`-per-target loop that bloated the
nadd-metric proofs.

**Structural matching only**: the hyp must be a top-level ground equality —
`instantiate` a ∀-quantified equation to ground form first (the Go
`f.At(w…).Rw()` grounds and rewrites in one). A ∀-equation that must
rewrite under a binder, or at every instance at once, is a `simp_with`
rule by its index, `{hyp_index: i}`.

**A ground `⇔` is an equation at bool and rewrites the same way**: `p ⇔ q`
at `hyp_index` turns `p` into `q` wherever it stands, under a connective and
inside the other hypotheses — which is how an ⇔ fact acts as a rewrite where
a permutative law could not be a `simp_with` rule; a ∀-quantified `⇔` is not
ground and is cited at its instance in a `by`. A self-expanding equality
(LHS occurring in its own RHS, e.g. `x = f(x)`) is refused. Direction is
preserved verbatim (no size guard), so expansion rewrites (`d → dist(m,n)`)
work with `flip`.

#### `lean_rw` — Go `LeanRw`

LEAN-style equational rewrite.

**Pure rewrite path** — bypasses the size-decrease guard inside
`eqSimplify`, so expansion-style lemmas (extensionality, COND distribution,
definitional unfolding, biconditional folds where the RHS is bigger than the
LHS) actually rewrite the goal.

**Bidirectional**: tries the lemma's natural direction (LHS → RHS) first,
then falls back to the flipped direction (RHS → LHS) if no match was found.
The rule is oriented by what fires — agents don't need to know which
direction each entry states.

**No fallback** to `lemmaConclMatchTactic` / `lemmaHypMatchTactic`: when
neither direction's rewrite matches, you get a clean `lean_rw did not apply`
rather than the lemma being silently added as a hypothesis. Rejects
non-equational lemmas with the typed error
`"lean_rw expects an equality lemma; got: …"`.

**Optional `term_specialize` parameter** — same shape and semantics as the
`lemma` row's `term_specialize`, but applied via pre-rewrite β-substitution
(`lean_rw` doesn't install as a hyp, so there's no post-install instantiate
chain — the lemma is β-substituted to the witness directly and the rewrite
path uses the specialized form). Use when the rewrite rule needs to fire at
a specific instance of an outer ∀-binder; the canonical case is
`lean_rw({key: <real_sgn_abs.AbsOfNum's key>, term_specialize: {n: "5"}})`
rewriting `real_abs(&5) → &5` against the goal. Polymorphic binders are
handled the same way as in `lemma` — the witness's type pins the binder's
type-vars.

**Optional `type_specialize` parameter** — same shape and semantics as the
`lemma` row's `type_specialize`, applied to the rewrite-rule lemma before
the equality check. Use when the rewrite rule needs to fire at a specific
type-instance the default goal-context adapter would pin differently; an
explicit `type_specialize` DISABLES that adapter — the σ is honored exactly
or the rewrite fails cleanly (unpinned type-vars stay polymorphic). Both
parameters compose (TYPE first, then TERM). The equality check sees the
post-σ form, so a fully-pinned σ that breaks the equality shape (rare)
errors cleanly.

#### `arith` — Go `Arith()`

THE unified num-arithmetic move. Blind composite that runs (i) the local
identity simplifier (a+0→a, a*1→a, 2+3→5), then (ii) the deep, hyp-aware
decider — every comparison/equality atom the goal's hyps make universally
true/false reduces to ⊤/⊥, including nonlinear semiring equalities
(`a*b=b*a` via RingProveFull) and atoms buried under ⇒/∧/∨/¬ or under a
binder (capture-avoiding lift via EqRewrite's machinery), then (iii) a
trivial close that turns a `⊢ ⊤` residual into a closed goal. Beyond the
linear/ring core it also discharges the opaque-operator layers — monus `a−b`
(cancellation/truncation, plus a case split on `a ≤ b ∨ b ≤ a` for
irreducible `a−b`), nat_max/nat_min (idempotence + guard case-split),
predecessor (bridge to `n−1`), and nat_div/nat_mod (trivial simp +
bounded-atom enrichment + common-factor cancellation). So a fully-decidable
goal closes in one move; a partial decision (`(a<a+1) ∧ Q → ⊤ ∧ Q → Q`)
advances the goal. The nat_div/nat_mod bounds are held in the branches of
a hypothesis split as well, so a `≠` beside a quotient or a remainder is
decided: `nat_odd(n), n ≠ 1 ⊢ 1 < n` (`nat_odd(n)` is read as
`0 ≠ rem(n, 2)`), `0 ≠ div(n, 2) ⊢ n ≠ 0`. A parity fact that needs the
quotient is decided too, the quotient unnamed: `nat_odd(n), 1 < n ⊢ 3 ≤
n` (the integer core eliminates Division's equation before it rounds).

A hypothesis that is a DISJUNCTION, a `≠` or an implication is split
(over ℕ, ℤ and ℝ alike), and a branch the linear prover leaves open,
once nothing is left to split, goes to the handlers that read the
hypotheses: the sign-known nonlinear fragment, the cancellation and the
products pass over ℤ and ℝ; over ℕ the branch's equation substituted
into the goal, then the bounded enumeration. So a value known up to a
finite disjunction reaches a product: `s = &1 ∨ s = −&1 ⊢ s·s = &1`,
`s = 1 ∨ s = 2 ⊢ s·s ≤ 4`, with no `SplitDisj` written.

Over ℕ a comparison is SCALED by a factor its two sides share, and a
shared factor is CANCELLED from a premise (omega `nat_scaling.go`), as
over ℤ and ℝ. The two sides are read by their factors, whatever the
order and the grouping of the products: with P the product of the
shared factors and a, b what is left of each side, the comparison is
`P * a ⋈ P * b`, a side that is one of the other's factors leaving `1`.
A goal follows from `a ⋈ b` — `y ≤ z ⊢ x * y ≤ z * x`, `y ≤ 1 ⊢ x * y ≤
x`, strictly with the factor shown positive, `y < z ∧ 0 < x ⊢ x * y < x
* z` — two products with no common factor from their factors compared
pairwise, `y ≤ z ∧ x ≤ w ⊢ x * y ≤ w * z`, and two sums summand by
summand, `y ≤ z ⊢ x * y + c ≤ x * z + c`. A goal that is no comparison
of two products follows from the premises' comparisons scaled by the
cofactors the sequent spells beside them: `B ≤ S ∧ c ≤ q + B * r ⊢ c ≤ q
+ S * r` (the premise `B ≤ S` times r, the cofactor of B), `2 ≤ p ∧ d ≤
i ∧ 0 < d ⊢ suc(d) ≤ p * i`, `s < g ∧ c = s * s ∧ g * g ≤ c ⊢ ⊥`. A
premise `P * a = P * b` or `P * a ≤ P * b` gives `a = b` or `a ≤ b`
where P is shown positive, and a strict one gives `a < b` and `0 < P`
outright: `0 < x ∧ x * y = x * z ⊢ y = z`, `(x + 1) * y = (x + 1) * z ⊢
y = z`, `x * y < x * z ⊢ y < z`; a negated order is read as the order
it is, `¬(y < x * y) ∧ 0 < y ∧ 0 < x ⊢ x = 1`. The scaled comparison
need not be one premise: where the premises prove `P * a ⋈ P * b`
linearly and both products are spelled among them, the factor cancels
from the goal — two equations with a side in common, `2 ≤ p ∧ n * n = p
* (k * k) ∧ n * n = p * (p * (c * c)) ⊢ k * k = p * (c * c)`.
No `nat_arith.MulEqLCancel`, `nat_order.LessEqMulCancel`, `LessEqMulMono`,
`LessEqMul2` or `LessThanMulCancel` is cited for these. A factor is
shown positive by the linear layer, by a resident `t ≠ 0`, factor by
factor for a product, and by its base for a power; with no such
evidence nothing is cancelled, `x * y = x * z ⊢ y = z` being false at
`x = 0`.

A piecewise OPERATOR outside a binder (`|x|`, `max`, `min`, `sgn`, a
`COND`) is split the same way, and its branch holds the
guard and the pin: `d ≤ &1` and `real_min(d, &1) = d`. A `COND` whose
condition is not one `<` or `≤` — a disjunction, a conjunction, a
negation, an equation, a membership, a propositional variable — is
split by the condition's atoms, one at a time, each branch holding the
atom or its negation and the `COND` with that atom decided: `v + COND(t
< m - 1 ∨ t = m, 1, 0) ≤ v + 1`, `&0 ≤ COND(a < b ∨ a = b, b - a, a -
b)`, `COND(p ∈ S, x, x + 1) ≤ x + 1`. The branch goes
to the same handlers, so a bound on an operator feeds a product beside
it: `|x| ≤ c ∧ &0 ≤ w ⊢ x * w ≤ c * w`, `|x| ≤ c ∧ |y| ≤ c ⊢ x * y ≤
c * c`. Where the operator itself stands inside a product, a quotient
or an opaque atom, the branch is read with the operator replaced by
its arm, goal and hypotheses alike, before it is decided: `&0 < w ⊢
real_min(d, &1) * w ≤ w`, `&0 < w ∧ ε ≤ &1 ∧ real_min(a, &1) * w <
ε * w ⊢ a < ε`, `d ≤ &1 ⊢ real_min(d, &1) * w = d * w` with no sign of
`w`, `a ≤ b ⊢ f(real_min(a, b)) = f(a)`, `nat_min(d, 1) * w ≤ w`. No
`MinIsArgument` or `MinLowerBound` is handed over for the operator's
sake. What the arms leave is decided as a split's branch is: the field
handler is not asked there, so an operator in a DIVISOR (`&0 ≤ x ⊢
x / real_max(w, &1) ≤ x`) still wants the operator's bound as a
premise, and ℕ's `a − b` has no arm to be read at where it is not zero.

It also strips a **leading `∀`/`⇒` wrapper** on the conclusion when that
exposes a decidable sequent: `⊢ (a≤b)⇒(b≤c)⇒(a≤c)` and
`⊢ ∀a b c. (a≤b)⇒(b≤c)⇒(a≤c)` close by moving the antecedents to hypotheses
(and the ∀-vars to fresh consts) and deciding the matrix — so no manual
`strip_imp`/`strip_quant` is needed before `arith` (the strip is committed
only if the decider then fully closes, so a non-closing `arith` never leaves
a half-stripped residual). This is distinct from the buried-atom case above
(a universally-true atom *inside* the formula); here the antecedents are the
Farkas facts the consequent follows from.

It further closes a goal that is an **arbitrary boolean combination of
comparison atoms which no single atom decides** — a `⇒` nested inside a `∨`,
an n-ary trichotomy `(a<b) ∨ (a=b) ∨ (b<a)`, a `⇔` between compound booleans
`(a≤b ∧ b≤a) ⇔ (a=b)`, etc. — by case-analysis on the atoms
(ExcludedMiddle), collapsing each branch under its atom-assumption and
recursing on the residual (interleaved, so the 2ⁿ assignment tree is never
materialized); an invalid such boolean is left untouched, never falsely
closed.

**A `COND(g, a, b)` whose guard is resident is read at its arm**: with `g`
among the hypotheses the first, with `¬g` the second, whatever `g` is — a
membership, an opaque predicate, no atom of the decider's own splits — and
on ℕ, ℤ and ℝ alike, so `&0 ≤ p, n ∈ s ⊢ real_abs(COND(n ∈ s, p, &0)) ≤ p`
closes with no case split on the guard (under `by {arith:true}` the guard is
one of the hypotheses the list names).

**A formula a hypothesis states is read as ⊤, and as ⊥ when a
hypothesis states its negation** — the COND rule for every formula, in
the conclusion and in a hypothesis alike. An arithmetic formula is
decided as every comparison is, a hypothesis among its facts; the rule
is for what the decider's own atoms do not cover, a membership or an
opaque predicate or a propositional variable, which is therefore
discharged as an arithmetic guard is: `i ∈ H, i ∈ H ⇒ i ≤ n + 1 ⊢ i ≤ n + 2` closes under `by
{arith:true}` naming both hypotheses, and a filler's face equations
`1 ∈ S ⇒ d(1 + 1, 1, w) = y(1)` beside `1 ∈ S` are read at their faces
with no step that reads the membership first. An ⇔ one of whose sides
a hypothesis states reads as its other side: a membership law at its
instance, `j ∈ 0 .. r ⇔ j ≤ r`, beside `j ∈ 0 .. r` gives the closer
`j ≤ r`, and `j < r + 1` closes. The guard is read as a
hypothesis spells it (under `by`, whose conditioning splits a
conjunctive premise, as a conjunct of one too). A guard the hypotheses
imply only through a definition, a membership in a defined set with
nothing resident that states it, is not unfolded: the refusal names it
(`the premise … is still guarded: the context does not supply …`), and
the close names the hypothesis that states it, or a reading of it to
its arithmetic content (a plain `By` with the definition) made first.

Each underlying step records under
its own proto tag so replay is faithful. A strict comparison over num — a
hypothesis `i < q`, or the negation of a `≤` goal — is read as `i + 1 ≤ q`
once ℚ-reasoning has declined, so `i < q ⊢ 1 ≤ p + q` closes, and so does
the truncation branch of `i < q ⊢ p + q − 1 + 1 = p + q` (`p + q ≤ 1`
pinned, `1 = p + q` asked), with no `i + 1 ≤ q` restated. Integer-specific
decisions (`2a ≠ 1`) require the corpus bundle's integer leaves (intCut /
notDivides via the bundle's `LessEqRightDivEq` / `DivModUniq` /
`ModEqZero`) — under the no-bundle placeholder mode they decline cleanly.

**A law stated at a symbolic dimension, cited at a numeral, is a plain
`By`.** A law written at `n + 1` or `n + 2` — the simplicial identities,
`simplicial_set.FaceIn` — read at `n := 0` or `1` installs `X(0 + 1)`,
`d(1 + 1, …)`, `s(0, 1 − 1, …)` beside a goal spelled `X(1)`, `d(2, …)`,
and guards such as `1 ≤ 1`. The apply rung reads a statement at its
numerals (the numeral reading, §"The conditioning stage of `by`", SA): a
guard `x ∈ X(2 + 1)` is supplied by a resident `x ∈ X(3)`, the guard
`1 ≤ 2 + 1` asks for nothing, and the instance's conclusion at `2 + 1`
is the goal at `3`. So the close is `By(<law>.Read(h).At(…),
<memberships>)`, keyless. The reading is the rung's and not the
refuter's: a close that needs the refuter to carry `X(0 + 1)` to `X(1)`
— a bare law it instantiates itself, a chain of equations — still lists
the numeral equation as a fact, or is `ByArith`. At a
SYMBOLIC dimension the arithmetic closer folds the argument: with
`x ∈ X(m + 1 + 1)` resident, `x ∈ X(m + 2)` closes under `ByArith` and
records nothing, and so does `FaceIn` read at `n + 1` against a goal
spelled at `n + 2` (`simplicial_module.SphereToMooreCycle`), while
`Normalized` alone leaves the two spellings apart. `RingNf()`
(the session's `ring_nf`) normalizes every arithmetic subterm of the goal
and its hypotheses, both spellings meeting at `m + 2`, and the leaf then
closes by assumption; a ground equation such as `n - 1 + 1 = n`, had by
`ByArith` and left for `Normalized` to rewrite with, is the narrower
spelling (`kan_complex.FacesCompatible`). `suc(n)` against `n + 1` is no
ring question: `RingNf()` refuses such a goal, and the bridge is the
rewrite `Simp(Fwd(nat_arith.Add1))` (`n + 1 = suc(n)`) — in the same `Simp`
as a recursive definition stated at `suc(n)`, which still fires first
(`simplicial_set.BaseSimplexIn`); a definition clause at `suc(i)` read at
`i + 1` takes `Simp(Rev(nat_arith.Add1), Fwd(<definition>))`
(`simplicial_chain.FaceSumCancel`).

### inspect.structural_facts contract

Each fact in `inspect.structural_facts` has been gated by one of two
predicates, depending on whether the tactic is auto-applicable or
takes an agent-supplied parameter:

**Strong contract — verified by clone-apply.** For these facts, the
engine actually runs the tactic on a fresh clone before listing it.
If the fact is in the response without `unverified`, `apply` will succeed
(modulo state changes between `inspect` and `apply`). The runs that read
a clock — `arith`, `ring_nf`, each direction of an `rw` — have 1 s each
(`inspect {budget_ms}` sets another): one cut off there is listed with
`unverified`, the reason, and says nothing either way about the move.
`probe` the tactic with a larger `budget_ms` to learn which. An `rw` fact
names the first direction seen to apply; where the other was cut off its
description says so.

- All parameterless structural moves (`strip_imp`, `split_conj`,
  `split_conj_all`, `split_disj`, `split_iff`, `split_hyp_iff`, `split_hyp_imply`,
  `strip_quant`, `cond_rewrite`, `assumption`, `refl`, `left`,
  `right`, `funext`, `symm`, `congr`, `arith`) — for `arith`, the
  clone-apply runs the full simplify-or-decide composite, so a positive
  enumeration means the move would actually make progress on the goal
  (close it, rewrite the conclusion, or rewrite or drop a hypothesis the
  others make redundant); a goal that's only shape-eligible but where
  nothing reduces is filtered out. `split_disj` /
  `split_hyp_iff` / `split_hyp_imply` / `strip_quant` accept an optional
  `hyp_index` at `apply` time — the enumeration lists them once per goal
  (pick-first semantics), and the agent adds `hyp_index` when
  disambiguation between multiple ∨/⇔/⇒/∃-hyps matters, or when
  `strip_quant` must open an ∃-hyp under a conclusion that is still
  ∀-headed
- `def_expand` — gated by `prover.TryDefTactic` (deduped by const
  name; type-distinct instances of the same printed name like `$`
  are collapsed into one fact)
- `induction` — gated by `prover.TryInductionTactic` per candidate var
- `subst` — gated by `prover.ApplySubst` per equality hyp

**Shape contract — applicability requires the agent's parameter.**
For these four, only the shape precondition is verified at enumeration
time. The agent's specific parameter choice is validated at `apply` /
`probe` time — the same parameter on the same goal can succeed or fail
depending on the agent-supplied term:

- `witness` — concl is top-level ∃ or ∃!; agent picks the witness term
- `instantiate` — hyp is ∀-headed; agent picks the witness term
  (and optionally `hyp_index`)
- `trans` — concl is `a = c`; agent picks the middle term
- `case_split` — agent picks any bool term; the enumeration lists
  in-goal bool subterms as suggestions, but the agent may also pass a
  fresh discriminant not in the goal (sound via `ExcludedMiddle`)

For shape-contract facts, use `probe` to cheaply check applicability
with a specific parameter before committing via `apply`.

**Informational fact — `def_eq` (citable material, not an applicable
move).** For each defined constant in the goal, `inspect` surfaces the
constant's *defining equation(s)* as a `def_eq` fact
(`Params{"const", "equation"[, "role"]}`). This is reference material —
the definitions `def_expand` and `retrieve` don't show — not a tactic
to apply directly. Two cases:

- **NewConstDef Hilbert/ε** (nat_mod, nat_div, HD, +, *): the point-free
  `c = εx.…` (role omitted/`def`). `def_expand(c)` only yields the
  property `P(c)`, never this equation. To *use* it: reduce a pointwise
  goal `∀x⃗. c(x⃗) = …` toward the head `c = f` via `congr`/`funext`,
  then `known` closes (case 3 of `known`).
- **NewTypeDef abs/rep** (mk/dest pairs): the type-def axioms
  `abs(rep a) = a` (role `typedef_abs`) and `P(r) ⇔ rep(abs r) = r`
  (role `typedef_rep`), surfaced here so you don't have to go find them.

  A session cites them through the chapter that defines the type: its
  `family.DefineType` registers the two theorems as entries
  (Retraction and Membership), cited by name like any member. The
  implication-form recipe below works for every pair regardless, and
  stays the primary discipline: it is what transfers 1:1 to the Go
  idiom.

  In Go they come from `Script.TypeDefExpand(constName, source)`, which
  returns BOTH axioms from one call and takes the non-emptiness witness
  (`⊢ P(x)` for some x) as `source`; `Script.TypeDefSource(constName)`
  supplies that witness when no proved section carries it. See
  `proofs/nat_num/peano/peano.go` for the two-output pattern
  (`numTypeDefAxioms`) and `proofs/real/tower/internal/eudoxus_slope` for the
  family-level packaging.

  **The body IS session-validatable, indirectly — state the derivation
  as an implication.** There is no session route to the axioms
  themselves, but there is nothing special about their CONTENT: write
  the goal as `<axiom> ⇒ <axiom> ⇒ <what you want to prove>`, add THAT
  as a session goal, and `strip_imp` puts the axioms in as ordinary
  hypotheses. Everything after that — which witness to ground at, which
  hyps to clear, where the close actually lands — is measured rather
  than guessed, and the tactic sequence transfers to Go with the
  stripped hyps replaced by `Cite(axiom, w…)` on the `TypeDefExpand`
  outputs. One difference to expect when transcribing: in session the
  ∀-axiom stays resident after `instantiate` (hence the `clear` you will
  often need), whereas `Cite(axiom, w…)` installs only the ground
  instance, so the Go usually needs no clear. Worked through for both
  members of `proofs/cartesian/pairs`; both replayed on
  the first run.

`subst` and `instantiate` expose `hyp_index` via the same
string-stringified convention as `case_split`'s `term` and
`induction`'s `const`: `inspect` emits `Params{"hyp_index": "0"}` (a
string), and the agent feeds an int back in via the JSON wire field
`tactic.hyp_index: 0`. For `subst`, `hyp_index` is required (omitting it
returns a typed error). For `instantiate`, it is optional — when absent,
the engine falls back to "first ∀-hyp matching the witness type", which
is what LEAN-style `specialize` callers expect. `clear` is the exception:
it takes `hyp_indices` (a list — its only hyp param, required; a single
drop is `[i]`), never `hyp_index`.

`split_disj`, `split_hyp_iff`, `split_hyp_imply`, and `strip_quant`
also take an optional `hyp_index` (same wire field). Absent → pick the
first matching ∨/⇔/⇒/∃-hyp (the pre-payload semantics every existing
corpus record was recorded under, preserved for back-compat; for
`strip_quant` a ∀-headed conclusion is stripped before any hyp is
looked at). Set → disambiguate when several hyps share the shape;
for `strip_quant` the named ∃-hyp is Skolemized and the conclusion is
left alone. An out-of-range index or a hyp of the wrong shape at that
index fails cleanly with a typed diagnostic (`"split_disj hyp_index 15
out of range [0, 12)"`, `"split_hyp_iff hyp_index 3 (…) is not A ⇔ B"`,
`"strip_quant hyp_index 3 (…) is not ∃x. …"`) rather than silently
picking a different hyp. `simp_with` and `simp` refuse an index past
the hypotheses the same way (`"simp_with hyp_index 0 out of range
[0, 0): the goal has 0 hypotheses"`).

#### Structural moves at a hypothesis: the set-builder reading

The index-targeted hypothesis moves — `split_conj`, `split_disj`,
`split_hyp_iff`, `split_hyp_imply` and `strip_quant`, each with
`hyp_index` — open a hypothesis that is a membership in a set-builder
through its predicate when it is not the move's shape as written:
`x ∈ {y | φ(y)}` is read as `φ(x)`, the three-part `x ∈ {t | x̄ | φ}`
as `∃x̄. φ ∧ x = t`, and the move opens that reading. It is one reading,
the one the closers' conditioning stage makes (prover/tactic,
membership_reading.go), carried by the kernel's bridge from the three
set-builder definitions — no restated Have, no key. Only the
hypothesis's top is read: a membership the predicate itself tests
stays as written (`x ∈ {y | y ∈ s ∧ P(y)}` splits into `x ∈ s` and
`P(x)`), and a hypothesis that is the shape as written is opened as
written, so a conjunction one of whose conjuncts is a membership splits
at its own ∧ as before. The pick-first forms (no `hyp_index`) do not
read a membership. The Go verbs read it alike — `a.Conjuncts`,
`a.Unpack*`, and a fact's `SplitDisj` / `SplitIff` / `SplitImply` /
`DismissLeft` / `DismissRight` — and `emit-section` renders the moves
as before: `parts := a.Conjuncts(<fact>, …)`, `StripQuantAt(i)`,
`SplitDisjAt(i, LeftHolds(…), RightHolds(…))`. A membership in a set
named by a definition (`f ∈ polynomial_algebra(R, S)`) is opened by
the definition first (`def_expand {const, hyp_index}`, Go
`a.Unfolded`), then split.

### Parameter terms (`witness` / `instantiate` / `trans` / `case_split`)

A parameter term may spell a minted goal variable by its bare surface
name (`n` for `n₀`) where `inspect.surface_names` lists the alias —
see §"Surface names — claim texts spell the statement's binders" (Chapter
Go, the math layer), "Session parity".

These four tactics accept their parameter term via two paths, tried in order:

1. **Subterm lookup** (fast path) — if the printed form matches a
   subterm already in scope (free variables introduced by `strip_quant`
   / `strip_imp` / `induction`, constants, small in-scope expressions),
   the engine reuses the existing term object directly.
2. **Text-DSL parse** (slow path) — otherwise the parameter is parsed
   via `ext.ParseTermText` with the goal's free-var types as context
   and an expected type derived from the tactic (`trans` uses the
   equality side type; `witness` uses the ∃- or ∃!-binder type; `instantiate`
   uses the ∀-binder type; `case_split` requires `bool`). The text
   format is the same one used for PropInput (see "Text format"
   below) — including arithmetic infix and numeric literals — but at
   term level rather than at proposition level. A scope guard rejects
   any fresh free variable the parsed term would introduce; only names
   already in scope at the goal are allowed.

For `instantiate`, a witness that resolves at a type DIFFERENT from the
∀-binder's does not fail outright: when the binder type matches the
witness's under a hyp-side type-var substitution, the engine's
automatic type adaptation fires (see the `instantiate` row above).

Practical effect: agents can construct novel bridge terms not appearing
in the goal — e.g. `trans` with `const: "m * suc(n + p)"` as the
midpoint of an equality goal, even when only `n + suc(p)` is visible
in the printed goal. For `case_split` the same is true: introducing a
fresh discriminant such as `p = 0` or `q1 ≤ q2` is sound (reconstruction
goes through `ExcludedMiddle`, an unconditional tautology), so pass the
bool term you
want to case on, whether or not it already occurs in the goal.

*Internal-only* (still dispatchable for back-compat, not advertised in the
agent vocabulary; `auto` / `expand` already chain these in their proper
place): `rewrite`, `simplify`, `denote`. Semantic ordering:
`rewrite ⊆ simplify ⊆ expand ⊆ auto`.

`denote` has one form worth knowing as an agent — the EXPLICIT one.
Bare `{"type":"denote"}` runs the search stage (heuristic picks the
subterm, mints `α₀`). With `const` it is the abbreviation move "let
*name* = *const*":

```json
{"tactic":{"type":"denote","const":"dest_nadd(x_0, n) + dest_nadd(y_0, n)","name":"d"}}
```

- `const` — the term to name, text-DSL, parsed against the focused
  goal's scope (the same path `witness` / `trans` use). An ε-term
  routes to the Hilbert transform automatically.
- `name` — optional; omitted, the step mints `α₀`. Requires `const`
  (`name` alone is an error, not a silent search).

A term the goal does not contain, or a name already free in it, is a
typed error from this call — the whole reason the explicit form
exists. See "Denote — the abbreviation family" for the Go-side twins
and the recording contract.

`let` is the DEFINITION move, "let *name* := *const*" — the session
face of `a.Let`:

```json
{"tactic":{"type":"let","name":"L","const":"⋂{b | F(b) ⊆ b}"}}
```

The equation `L = ⋂{b | F(b) ⊆ b}` joins the hypotheses, every
occurrence of the term in the goal becomes the name, and the goal
keeps its form. Unlike `denote`, the term need not occur — `let` names
an object the argument is about to reason ABOUT (the set a supremum is
taken of, a fold's summand, a map built for the witness) — and the goal
does not move to ⊥-form. Both fields are required; a name already free
in the goal is a typed error. The defining equation is a hypothesis
like any other: a later `by` lists it in `by_hyps` where the close
unfolds the name, and leaves it out where the name should stay one
atom. Recorded as the `denote` ministep in its `let` mode; emit renders
`LetTerm("L", …)`, which a hand-written body spells `a.Let("L", …)`, or
`a.LetAs[φ]("L", …)` where the body goes on to speak the name.

Wire format: `{"tactic":{"type":"<name>","const":"...","lemma":{"key":"<entry>"}}}`
for a registry entry, or `{"tactic":{"type":"lemma","lemma":{"text":"..."}}}`
for an ad-hoc inline lemma. The `lemma` field is a
[PropInput](#prop-input) — set exactly one of `key` or `text`. For
`subst`, the `"hyp_index": N` field is **required** — omitting it
returns the typed error `"subst requires the 'hyp_index' field"`
rather than silently defaulting to hyp 0. For `instantiate`,
`"hyp_index": N` is likewise **required**; use `inspect` to locate
the target ∀-hyp's index. The `lemma.key` form is
preferred for an entry — the engine serves the entry's own statement
without a client-side text round-trip.

For `lemma` and `lean_rw`, the optional `term_specialize` field
pre-instantiates named outer ∀-binders BEFORE the hyp is installed (or
the rewrite fires) — collapsing the
`lemma → instantiate(t_1) → … → instantiate(t_k) → clear(∀-hyps)`
chain into one apply. It's a Lean-style named map:
```json
{"tactic":{"type":"lemma","lemma":{"key":"prop_..."},
           "term_specialize":{"x":"n","y":"m"}}}
```
Map keys are ∀-binder names read off the statement the session SERVES
for the key — a row a chapter member proves is served as the member's
statement (`query member <key>` prints it; binder letters and clause
packaging are the member's);
values are witness terms parsed in the goal's scope (same path
`instantiate`'s `const` uses — subterm-lookup first, text-DSL
fallback). Peeling proceeds outside-in: at each outermost ∀-binder, if
its name is in the map the engine peels it; if NOT in the map, peeling
stops there (the trailing ∀-binders survive on the installed hyp).
Every map key must be consumed — an unmatched key (typo or binder
buried under a non-specialized outer one) is a hard error.
**Polymorphic binders are handled automatically:** when a binder's
type contains a type variable (`∀P:(A→bool)→bool. …`), the witness's
concrete type unifies with the binder type and σ_type propagates to
the rest of the lemma. No companion `type_specialize` needed for the
binder's vars; the agent's witness pins them. A positional
`specialize: [...]` array is refused with an error pointing at
`term_specialize`.

For `assert`, the `claim` field is a [PropInput](#prop-input) — set
exactly one of `key` or `text`. The resolved Prop must be hyp-free and
have a boolean conclusion. The apply response carries the resulting two
subgoals in `[claim, residual]` order: `subgoals[0]` is `Γ ⊢ φ` (close
this next), `subgoals[1]` is `Γ, φ ⊢ G` (the original goal with φ
appended at the highest hyp index). Free variables in φ must already be
in scope at the current goal — `assert` does **not** auto-introduce
them. If the claim references an unbound name, the engine returns
`"assert claim references unbound variable %q; introduce it via
strip_quant or declare it explicitly"`.

A bare in-scope free var needs **no** `name:type` declaration: the text
form is parsed against the goal's scope, so its type is taken from the
goal (the same way `witness` / `trans` / `instantiate` resolve a bare
term — see the **Parameter terms** section below). A claim never spells
⊢: a var the goal does not already constrain is refused by the scope
check.
Three wire-format examples:

```json
# Inline text DSL — the bridge claim in the chapter's spelling
{"tactic": {"type": "assert",
            "claim": {"text": "m * suc(n + p) = m * suc(n) + m * p"}}}

# Claim with a free variable just introduced by strip_quant — fine,
# the var is now in scope on the current goal
{"tactic": {"type": "assert", "claim": {"text": "f(x) = g(x)"}}}
```

For `auto_with`, the wire shape is symmetric to `lemma` but takes a
LIST of scoped lemma entries plus an optional clear mode. The default
(no clear field) clears every top-level ∀-headed hyp; `keep_hyp_indices`
inverts that to "clear every hyp NOT listed"; `drop_hyp_indices` is the
explicit-drop form. The whole orchestration is atomic close-or-fail —
on no-close the session is unchanged. Wire shapes:

```json
# Close a goal that needs a few entries chained.
# Default clear heuristic drops every ∀-headed hyp (refute-poisoning class).
{"tactic": {"type": "auto_with",
            "with_lemmas": [{"key": "prop_7d7685f1427a8d6c"},
                            {"key": "prop_265109053fc36238"},
                            {"key": "prop_78ff54e48227718e"},
                            {"key": "prop_cb63abd1d029ab71"}]}}

# Per-lemma type_specialize / term_specialize are honored (same semantics as `lemma`'s).
{"tactic": {"type": "auto_with",
            "with_lemmas": [{"key": "prop_...",
                             "type_specialize": {"A": "?71152", "B": "?71148"},
                             "term_specialize": {"P": "λs. card s = 0"}}]}}

# Preserve a specific ∀-hyp the default heuristic would otherwise drop.
{"tactic": {"type": "auto_with",
            "with_lemmas": [{"key": "prop_..."}],
            "keep_hyp_indices": [0, 2]}}

# Drop exactly the listed indices (mutually exclusive with keep_hyp_indices).
{"tactic": {"type": "auto_with",
            "with_lemmas": [{"key": "prop_..."}],
            "drop_hyp_indices": [1, 3, 5]}}
```

Failure shape: when the post-clear, post-install residual doesn't close,
the diagnostic lists `Initial:` hyp + ∀-count, `Cleared:` indices (with
text shapes for the first 3), `Installed:` lemma identifiers,
`Residual:` open-leaf count + top leaf's hyps/concl, plus a `Hint:` line
naming the most likely next move (`keep_hyp_indices`, missing
`with_lemmas`, `case_split`/`split_disj`, or `instantiate`/`type_specialize`
on a surviving ∀). Use the hint to author the next attempt — don't
chain `auto_with` calls speculatively.

Type adaptation (lemma / lean_rw). Polymorphic entries applied
to a concretely-typed goal are auto-aligned: the engine recovers a type
substitution from structural overlap between the lemma and the goal's
hyps/conclusion and applies it to the lemma before introducing the new
hyp. Effect: the new hyp's ∀-binders come out concretely typed, so a
following `instantiate(witness=...)` works without any manual
type-instantiation step. The `lemma`-reproduction subgoal that
`LemmaTactic` produces alongside is also closed in the same `apply`
call via type-instance match against the cited entry (this is what
`auto_matched` reports in the apply response, with the entry as
`MatchedKey`). `probe` runs the same auto-match prediction against a
clone, so its `effect` and `subgoals` reflect the post-auto-match leaf
count — and `probe.auto_matched` lists exactly the same closures that
`apply` would commit. Read them together: an `effect:"simplify"` with
one entry in `auto_matched` means "this move would have produced 2
subgoals, but one is auto-closed by the listed entry." When
the lemma and the goal share no const heads in matchable positions,
alignment falls through silently and the lemma is applied with its
original type vars — a subsequent `instantiate` then fails with a
binder-vs-witness type mismatch, which is the signal that
auto-adaptation didn't fire and the lemma is structurally inappropriate
at the current goal.

### LEAN correspondence

LEAN-fluent agents can use the names below; they map onto XuGo's
canonical tactics. Aliases are pure dispatch-table entries (no behavior
change); `intro` and `lean_rw` are real engine-level dispatchers.

| LEAN name | XuGo canonical | Notes |
|-----------|------------------|-------|
| `apply`        | `lemma`        | |
| `unfold`       | `def_expand`   | |
| `use`          | `witness`      | |
| `specialize`   | `instantiate`  | |
| `simp`         | its own verb   | the session SIMP SET (R4): rewrites the conclusion with the rules `define` installed, each polymorphic rule adapted to the goal's type instances and to the instances the rewrite exposes (an imported clause stated at the chapter's letters fires at the goal's instance) — per shape: direct/recursive install the characterizing theorem conjunction-whole, a datatype installs its injectivity/distinctness laws, the WF (`measure:`) shape installs the two DERIVED guarded readings (never the characterizing COND equation itself), and the spec shape installs NOTHING (cite the characterizing theorem instead — `cite-node` + `by`). The rule child closes from the definition section's own cert, invisible to the agent. Progress-or-fail with a set installed; with NOTHING installed it behaves as `simplify` (the historical alias meaning). `simp_with` stays the explicit-rule general form |
| `simp at h`    | `simp_with` / `simp` with `hyp_index` | the hypothesis rewritten in its place; Go `fact.Simp(rules…)` |
| `simp_all`     | `simp_all`     | the installed set over every target, to a fixpoint; Go `SimpAll(rules…)` |
| `@[simp]`      | `Simp: true` on a chapter's `registry.ProofEntry` | the chapter's simp set: read by a bound session's bare `simp` / `simp_all` beside its definitions, and by `Simp(fam.SimpSet())` in Go |
| `ring_nf`      | `ring_nf`      | every arithmetic subterm to its ring normal form; Go `RingNf()` |
| `ring` / `linarith` / `nlinarith` / `omega` / `norm_num` / `positivity` | `by {arith:true}` (Go `ByArith`) | one closer: ring over the monomial basis, Farkas, the pairwise products of the context's differences (the nlinarith step), the integer layer, sign rows, the field layer; a num hypothesis reaches a real or int refutation through its cast |
| `exact?` / `apply?` | `apply_search` | the corpus member that closes the goal, committed as its `lemma` cite; `retrieve` is the listing |
| `cases`        | `case_split`   | bool only; non-bool LEAN `cases` is not modeled |
| `rfl`          | `refl`         | |
| `lean_rw`      | `lemma` (eq)   | rejects non-equality lemmas |
| `intro`        | smart dispatch | ⇒ → `strip_imp`, ∀ → `strip_quant`; the committed ministep is whichever fired |
| `assumption`, `refl`, `left`, `right`, `funext`, `by_contra`, `symm`, `subst`, `trans`, `congr`, `congr_arg`, `congr_fun` | (same name) | first-class XuGo tactics; see the table above. `congr_arg` / `congr_fun` mirror Lean's `congrArg` / `congrFun` (forward hyp-congruence). |

> Note on `rewrite` vs `lean_rw`: XuGo's bare `rewrite` is
> `BasicRewrite` (boolean canonicalization), which is unrelated to
> LEAN's `rw`. If you're a LEAN-trained agent reaching for `rw`, use
> `lean_rw` — not `rewrite`. `lean_rw` and `lemma` are
> semantically distinct: `lean_rw` is a pure directional rewrite
> (size-decrease guard bypassed, no fallback to "add as hyp"),
> `lemma` is a best-effort multi-strategy apply. Pick `lean_rw` when
> you specifically want to rewrite the goal using an equational
> lemma; pick `lemma` when you want the engine to figure out how to
> use the lemma.

**Does NOT work** (returns `unknown` or `invalid` even if logically valid):
- Integer-only `num` goals under the no-bundle placeholder mode (production
  has the corpus bundle installed, so they DO close via the real intCut /
  notDivides path: `b<a+1 ⊢ b≤a`, `2a ≠ 1`, `2a ≤ 1 ⊢ a = 0`).
- Arithmetic the deciders (num, int, real, and the structure ring at a
  ring or field fact, ℂ's installed instance among them —
  `prover/solver/omega`) do not reach: over ℂ, a goal that needs ℂ's
  definitions rather than its field laws — its parts `re` and `im`, its
  norm, its conjugate (the complex chapters `Simp(complex_field.Parts,
  Fwd(<the definitions>))` to real components, then `ByArith()`) — or
  an equation the structure ring declines (§"The structure ring": a
  rational or polynomial coefficient, a divisor with no evidence that
  it is nonzero, two inverse pairs in one monomial); a symbolic exponent (`x ^ (n + 1) = x · x ^ n`; a
  LITERAL exponent is read as its monomial over num, int and real alike);
  a residue argument through `nat_mod` with symbolic dividends (`n mod 2
  = 1 ∧ m mod 2 = 1 ⊢ (n + m) mod 2 = 0`); an existence goal whose
  witness is a number (`∃n. 3 < n ∧ n < 5` — name it).
- A wide law and arithmetic in the REFUTER: `(∀y. y < 3 ⇒ P(y)) ∧ x + 1 <
  3 ⊢ P(x)` does not close by `auto` (the refuter has no arithmetic); it
  closes by `by {arith:true}` naming both — the apply rung reads the law
  at x and decides its guard by arithmetic under the context.
- Some higher-order reasoning involving boolean quantifiers.

When result is `unknown`, it means "could not prove", not "definitely invalid". The prover is sound but incomplete.

---

## Examples

```bash
echo 'p => p' | xugo check                              # valid
echo '~~p => p' | xugo check                             # valid
echo '~(p /\ q) <=> (~p \/ ~q)' | xugo check            # valid
echo 'p, p => q |- q' | xugo check                      # valid (modus ponens)
echo 'a => b, b => c, a, ~c |- false' | xugo check      # valid (contradiction)
echo 'P:A->bool |- (forall x:A. P(x)) => P(y)' | xugo check  # valid (∀ instantiation)
echo 'x:A, y:A, z:A |- (x = y) => (y = z) => (x = z)' | xugo check  # valid (transitivity)

# Correctly rejected:
echo 'p |- q' | xugo check                              # invalid
echo '(forall x:A. exists y:A. P(x,y)) => (exists y:A. forall x:A. P(x,y))' | xugo check
                                                           # invalid (quantifier flip)

# JSON envelopes — PropInput shape (text):
echo '{"premises":[{"text":"p"},{"text":"p ⇒ q"}],"conclusion":{"text":"q"}}' \
    | xugo check-derivation                                          # valid (modus ponens)

echo '{"statements":[{"text":"p"},{"text":"~p"}]}' \
    | xugo check-consistency                                         # inconsistent

# Preview a text-DSL proposition before committing:
echo '{"text":"forall x:A. P(x) => P(x)"}' | xugo parse-prop

# Scoped preview against a live session — the parser sees goal-local free
# vars (e.g. n_0 produced by strip_quant) and goal-local constants,
# exactly as `assert` / `lemma` will at apply time:
echo '{"text":"n_0 + 0 = n_0", "session_id":"<id>", "goal_id":"<gid>"}' \
    | xugo parse-prop

# Preview a term-DSL argument (witness / trans / instantiate / case_split):
echo '{"text":"suc(n_0)", "session_id":"<id>"}' | xugo parse-term
echo '{"text":"m + n = n + m", "session_id":"<id>", "expected_type":"bool"}' \
    | xugo parse-term
```

## Common mistakes

1. **Forgetting parentheses around quantifiers in implications:**
   ```
   # WRONG: ∀ scopes over entire expression
   forall x:A. P(x) => exists y:A. Q(y)
   # RIGHT:
   (forall x:A. P(x)) => (exists y:A. Q(y))
   ```

2. **Free variable without type:** declare via function signature (`P:A->bool, P(y)` infers `y:A`) or explicitly (`y:A`).

3. **Using `->` for implication:** `->` is the type arrow. Use `=>` for implication.

---

# Playbook (agent-facing)

Everything above this line is REFERENCE — the CLI/RPC surface, wire
format, capability boundary. Everything below is PLAYBOOK — how to
decide which move to reach for, what pattern to recognize, what
pitfalls to sidestep. Distilled from operational lessons in both
phases of the work, the session and the chapter Go written from it;
what one teaches is written here for the other.

Read the lessons once when you start driving the engine; the cost of a
lesson NOT read is measured in edit-run-debug rounds, not seconds. Five
are read when their shape is in front of you, and the agent file says
which: the arithmetic lesson and its worked closes, the polymorphic
constants, the ⇔ law with a quantified side, the equation between
functions.

**Section index**:

- §"What `auto` actually is — exposure gated, not power gated"
- §"Wide ∀-hypotheses refute-poison the CNF stage" (Lesson 4)
- §"5-second CNF ceiling is HARD, not soft" (Lesson 4b)
- §"ℝ and ℤ arithmetic in `by {arith:true}` — linear over MONOMIALS, and what stays out"
- §"Diagram chases in `by {chase}` — what it reads, and what stays out"
- §"Three arithmetic closes, worked: ε-N, ε-δ, a product estimate"
- §"∀-hypothesis absorbs your `instantiate` before CNF sees it" (Lesson 12)
- §"Existence goals need a witness" (Lesson 7)
- §"Collapse the wide-∀ residual at load time" (Lesson 10)
- §"Polymorphic constants — twin snapshots + `⟨⟩` disambiguation"
- §"Text-DSL discipline — the type-var scope trap"
- §"Post-tactic hyp-index renumbering"
- §"An ⇔ law with a quantified side — cite it"
- §"An equation between functions — rewrite with it, do not hand it to a closer"
- §"A slow `By` is its premises, not the refuter"

The lesson numbers are this playbook's labels: the agent file cites a
section by its number.

---

## What `auto` actually is — exposure gated, not power gated

`auto` is a near-complete first-order prover with equality
(paramodulation), ∀/∃-instantiation, ε-choice, and boolean-quantifier
expansion. It tracks **logical validity, not surface shape**, and
closes goals that look far past first-order — ε-choice-function
synthesis, Cantor diagonal, unique-characterization iff (full
ground-truth list: §Representative examples above).

**Its reach is gated by exposure, not power.** It will not:

- *find* your lemmas — you `lemma` / `Cite` them,
- do the structural *exposure* — you `strip` / `split` / `instantiate`
  / `congr` / `funext` to the first-order core,
- invent an induction, or synthesize a bare `∃`-goal witness (see
  §"Existence goals need a witness" below).

So when `auto` fails, the goal almost always just isn't in clean
valid-first-order form yet — load the cited lemma(s), do the
**minimum** exposure (often one move), `auto` again. The ~5s ceiling
is a **search** bound (see next section), not a verdict on capability.

**Reading `auto` failures**:

- `unknown(timeout)` — the CNF refuter hit its deadline without
  finding a refutation. A budget past the 5 s ceiling never helps;
  a close you expect is run again, unchanged, not lengthened
  (Lesson 4b).
- `fail` — the refuter proved there's no refutation at the given
  depth. Different from timeout: a bigger budget doesn't help.
- `panic_recovered` — an engine defect. The response carries
  `engine_fault` and the session takes no further move (§"Engine
  faults"). Stop and report `ENGINE-FAULT` with the fault's id; the
  record holds the faulting call and the goal. Don't paper over.

**In chapter Go** the analog is
`CnfRefute()`, plus `Basic()` / `Arith()` / `ctx.CloseByAuto()`.
Same 5s ceiling, same exposure semantics. If `CnfRefute()` panics
with "ministep CNF Refute. failed", think exposure — is the leaf
carrying too many wide ∀-hyps? See next section. On a strict replay,
the cache MISS of a refute that no `By` reached — a bare
`CnfRefute()`, a Calc leg, a kit's terminal, the set driver's own —
ends with a `(Checked: …)` line saying whether the goal closes under
`Basic()`. Where it does, the refuter was never wanted there and no
key should be recorded: close with `Basic()`, or state the step as
`By(Normalized, …)`. Where it does not, no shaping stands in for the
refute. A `By`'s own failure message answers the same question for
its leaf.

---

## Wide ∀-hypotheses refute-poison the CNF stage (Lesson 4)

**Pattern.** A resident wide multi-quantifier ∀-lemma in the hyp
context (e.g. a conjunction bundle of numeral-comparison clauses, a 4-var
monotonicity lemma like `nat_order.LessEqAdd2` / `LessThanAdd2`, or a handful of
pointwise-∀ lemmas all resident at once — the exact shape that
breaks a collapsed multi-section restructure) drives the
CNF refuter to its 5s ceiling **even when the actual refutation is
trivial and ground**.

**Cause.** The CNF refuter (`prover/solver/refuter/refute.go`) is a
saturation given-clause loop with **no set-of-support gate**. Every
hyp — including the wide ∀-bundle — becomes initial clauses that
resolve and factor against everything. A wide ∀-clause explodes the
passive set on resolutions that never touch the negated goal.

**Severity is not uniform: a ∀-PREDICATE hypothesis poisons alone.**
The ">~6 ∀-headed hyps" heuristic below is calibrated on first-order
∀-lemmas. A hypothesis whose quantifier ranges over a PREDICATE
(second-order — the closure form of an inductive definition, `∀P.
(closure(P) ⇒ P(s₀))`, is the type case) explodes the
instantiation space on its own: ONE such resident hypothesis is
enough. The inductive door keeps that particular form out of a
context: it mints finite, is_num, is_recspace and every relation
defined by rules, and refuses `def_expand`/`Unfold` on them — the
theorems the definition comes with are the proof surface. The rule
below stands for any other second-order hypothesis: a leaf fails
`auto` at budget with a `∀P` hypothesis resident, and the identical
leaf closes at once with only its ground instances in context.
**Diagnosis rule: a refute timeout on a leaf carrying a
wide ∀-hyp — any ∀-predicate hyp, or >~6 first-order ones — is a
context problem until proven otherwise. Do not report an engine wall
before re-trying with the noise gone.**

**Operational rule.** When `auto` / `CnfRefute()` stalls AND you
have >~6 ∀-headed hyps in scope (count them from the leaf display),
the noise is likely the problem, not the goal. Two ways forward:

1. **`clear` the noise, then close.** Use the `clear` tactic
   (session) or `ClearHyps(indices)` (chapter Go) to drop the ∀-hyps
   the specific close doesn't need, THEN call auto / `CnfRefute()`.
   Sound unconditionally (weakening only). See the `clear` row in
   the tactics table above.

2. **Load fewer wide ∀-hyps in the first place** — prefer
   `Fact(dep, w…)` (chapter Go) / `lemma { term_specialize }`
   (session) to install the pre-grounded instance at load time, so
   the wide ∀-hyp never enters context. See §"Collapse the wide-∀
   residual" below.

**Prover-only escape: `auto_with`.** For session-side proving,
`auto_with` is one atomic call that does `clear` + install scoped
lemmas + `auto`, rollback-safe. Reach for it when you know the
exact entries the close chains through.

**In chapter Go, `By(premises…)` IS the fix, built in.**
The math layer's close (constitution §"The math layer") clears every
hyp its premise list does not name BEFORE installing/grounding the
named premises and refuting — clear + scoped installs + close in one
verb, which is `auto_with`'s discipline without the manual index
juggling. So in chapter Go refute-poisoning is a SPELLING
diagnosis: a leaf that times out under a bare `auto`/`CnfRefute()`
wants a `By` with its premises named (grounded where an instance is
what the argument uses), not a bigger budget and not a wall report.
(The historical adaptation — a hand-built `Chain(ClearHyps(...),
installs…, CnfRefute())` — is the superseded install-pile-then-refute
close; don't author new sites.) Two structural aids remain true:
prove the close in a session first when in doubt, and keep sections
fine-grained enough that no leaf accumulates a large ∀-load.

**Concrete symptom** (chapter Go, an injective-iff-surjective member):
a 3-section restructure collapsed 10 seed sections into one
`injToSurj` body. Its close-witness leaf carried 11 wide ∀-hyps
(`cardinality.CardImageInj` Skolem + pointwise `CardSubsetEq` + pointwise
`set_order.SubsetAntisym` + `set_basic.InImage` + 6 more card/finite bounds).
`CnfRefute()` panicked at the 5s ceiling. The fix isn't index
juggling — it's more sections (the seed's staging count is often
load-bearing precisely because each sub-lemma keeps its ∀-load
small).

---

## 5-second CNF ceiling is HARD, not soft (Lesson 4b)

The refuter's `MaxEffectiveCnfTimeoutMs = 5000` is hard-capped at
one place, `effectiveCnfTimeout` in `prover/proof/step.go`; a larger
`budget_ms` is clamped, it genuinely cannot help.

**Empirical fact.** Refutations that succeed do so in well under
5s; past 5s the search is in a hopeless branch and longer timeouts
only burn CPU without changing the answer. The clamp exists
precisely because agents were requesting 15s budgets on
stuck goals — pure CPU-burn.

**A cut-off you expect to close is run again, never lengthened.**
The live search is nondeterministic, and its 5 s are wall-clock
time that a loaded machine shortens, so a refute cut off at the
ceiling can close on the next run of the same call. Where you have
reason to believe the close goes through, run the same call again,
unchanged and at the default budget, a few times: the session
`apply` with no `budget_ms` (each refute then runs at the session's
5 s, and a `by` runs every rung of its ladder, as the recorder does;
a `budget_ms` also bounds the whole apply, so a short one can cut
the ladder before its last rung), the recording as it stands. One
close is enough: the session keeps the step, and the recording
stores the certificate that replay reads with no search. A `probe`
cut off at its 1 s default has not been tried at the ceiling; apply
the move.

**Rule.** A `fail`, or a cut-off on every one of those runs, is
**final for that goal shape**. Switch strategy on the next move:

- `assert` / `trans` with a named bridge term,
- `induction`, `case_split`, `congr` / `congr_arg` for a
  hyp-congruence step,
- a specific entry retrieve missed,
- `clear` the poisoning ∀-hyps first (see previous section),
- decompose the goal into smaller pieces (chapter Go: add
  intermediate sections; session: assert intermediate claims).

Do NOT: retry with a bigger budget, hope a slight tactic reordering
will help, or edit code hoping to make the same call succeed.

---

## ℝ and ℤ arithmetic in `by {arith:true}` — linear over MONOMIALS, and what stays out

The arith closer's linear layer reads a product of variables as ONE
unknown over every domain (num, real, int — omega `Domain.polyMul`
over the ring's canonical monomial basis), so an ordering leaf whose
refutation is a linear combination of the premises after ring
normalization closes bare, products included: `2·((a·b)·d) ≤
2·(((a·a)·b)·b) ⊢ (a·b)·d ≤ ((a·a)·b)·b`; `2·(w·x) ≤ q − y ∧ p =
(q − 2·(w·x)) + s ∧ 0 < s ⊢ y < p`; a hypothesis carrying a product
combines with the goal instead of being dropped; `&0 < a·b ⊢ &0 <
&2·(a·b)`. A numeral guard inside a witnessed law's Horn premise
(`(&1 ≤ x ∧ 1 ≤ 2) ⇒ …` from `real_pow.PowMonoExp` at (x, 1, 2);
`2 ≠ 0` from `PowMonoBase`) is folded before the decider meets the
premise, and the closer runs its Arith to a fixpoint once the single
firing has failed, so a firing spent resolving a premise against the
others is followed by the decision; a rewrite the mop-up undoes is
passed over, and the round goes to the next hypothesis — a hypothesis's
(a resident `n = 2 * m` rewrites `2 ∣ n` to `2 ∣ (2 * m)` and the mop-up
rewrites it back) or the conclusion's (`|x * y|` pushed to `|x| * |y|`,
which the mop-up folds back by the equation the firing leaves beside
it), so a conclusion that holds a product under an absolute value keeps
no hypothesis from its turn. The rounds keep the equations the close
reads as written, which the congruence pass substitutes by and the mop-up
rewrites with: a hypothesis the decider proves redundant as a whole is
replaced by the value equations it holds below a connective — `(|n·b| =
n·b) ⇔ (&0 ≤ n·b)` with both sides true leaves `&n·|b| = &n·b`, and
`g ⇒ inv(t) = &2` with g decided leaves the equation. A hypothesis that
is the conjunction of those equations already — `inv(p) * p = &1 ∧ p *
inv(p) = &1` beside `&0 < p` — is kept as it stands. Before that
verdict the rounds read such a hypothesis ATOM BY ATOM: each atom the
other hypotheses settle is put at its value, the connectives are
folded, and what is left takes the hypothesis's place. So an instance of
a law the closer reads by itself, handed in beside the fact that
settles one of its sides, is its other side, though the closer proves
the instance outright: `2·n < 3·p` beside `nat_div_mod.LessEqRightDivEq`
at (p, 2·n, 3) — `(3 ≤ div(2·n, p)) ⇔ (p·3 ≤ 2·n)` — leaves `¬(3 ≤
div(2·n, p))`, and two counts `g = n·c` and `g = c·k` beside
`nat_arith.MulEqLCancel` at (c, n, k) leave `c = 0 ∨ n = k`. The verdict as
a whole drops a hypothesis only where its atoms leave ⊤, or the context
settles none of them. The one-shot `arith` move reports progress
only on a leaf it changed: a firing the tidy takes back whole is no
progress, and leaves the leaf as it was handed. No `DenotedAs` for a
product and no `a.Denote` of it.

### The structure ring — an equation at a ring or field fact

The same closer reads an equation at a resident `comm_ring_on(R)`,
`comm_ring(R)`, `field_on(F)` or `field(F)` fact, or an instance such as
`complex_field.Field`. The `by_hyps` names the resident fact, since By
clears unnamed hypotheses. The ring's operations and carrier are the
record's fields, computed through the instance normal form. Its leaves
are the algebra chapters' carrier laws, instantiated at those records
and guarded by membership. The field's ring is `field_ring(F)`; its
inverse and division closures require the original operands to lie in
`F.carrier`. A whole-type fact is bridged to its record restricted to `𝕌`, where
memberships follow from `set_basic.InUniv`. On a proper carrier they
come from the context.
The leaves carry the fact as a hypothesis when it is one; the ring's
numerals are the additive powers of one (`monoid_pow(add, zero, one,
n)`), to which a carrier's own literal (`complex_of_real(&2)`) is
bridged. **On a carrier set, the membership of every ATOM of the two
sides must be resident** — a hypothesis `x ∈ c`, or a conjunct of one
(`x ∈ c ∧ y ∈ c ∧ …`, the shape a carrier law's guards arrive in) —
and a term the ring forms lies in c by the closure laws (ZeroIn, OneIn,
AddIn, NegIn, MulIn, SubIn; PowIn for a power and a numeral), which the
closer reads itself. A membership the context lacks is a decline that
names the atom (`by {arith:true}` reports it: "the premises hold no
membership in it for y", the ring named); `y ∈ s` with `s ⊆ c` resident is NOT read — the closer does
not infer memberships through subsets, since every such inference is
one more rule of a second, weaker set prover inside the ring, and the
boundary "resident, as a hypothesis or a conjunct" is one an author can
hold. Have the membership (`BySets(subset, yIn)`), once, as the
conjunction the chapter's other steps read. So over ℂ
`complex_mul(complex_add(z, w), complex_add(z, w)) =
complex_add(complex_add(complex_mul(z, z), complex_mul(complex_of_real(&2),
complex_mul(z, w))), complex_mul(w, w))` closes by one bare `by
{arith:true}` — no componentwise `Simp(Parts, …)` first — and so do a
difference of squares, a negation through a product, a quotient read as
a product with the inverse (`(z + w)/w = z/w + w/w`), a negated square
(`(-z) * (-z) = z * z`), and a power at a
literal exponent (`monoid_pow(mul, one, x, 2) = mul(x, x)`); in an
abstract chapter the same goals close with the fact named, and on a
carrier set with the fact and the atoms' memberships named. What it
decides: a ring identity, an equation the context denies (below), and an
equation that is an INTEGER linear
combination of the context's equations over the monomial basis
(`x = y, u = v ⊢ x + u = y + v`; `x + x = y ⊢ x + x + x + x = y + y`;
`p − r = R.zero ⊢ p = r`). The context's equations are read as
hypotheses and as conjuncts of one (`p ∈ c ∧ r ∈ c ∧ p − r = R.zero`,
the shape a card's premise arrives in), and an equation between two
ATOMS, which names no operation of the ring, is read at every ring on
its carrier once the context holds an equation there to combine it
with; on a carrier set an equation whose atom lacks a membership is
not read into the combination, and the decline names that atom as it
names the goal's. A ground equation between two compound terms at the
carrier is substituted into the goal, bigger side to smaller, before the
ring reads it, as at the number carriers (the paragraph on premises
below): `A′ = −A, B′ = B, A ∈ c, B ∈ c ⊢ A′·B′ = −(A·B)` closes with no
membership for A′ or B′, the goal read in the spelling the memberships
name.
Declined, correctly: a combination needing a rational coefficient
(`x + x = y + y ⊢ x = y` — false in characteristic 2), and one needing a
POLYNOMIAL coefficient — Gröbner territory, where the coefficient is
the author's to supply (next paragraph). Order is not a ring notion:
`≤` at ℂ or at an abstract ring is not read. The capability is
`arith:structure` (roots: the carrier laws, universe bridges, record
equations and `InUniv`), and a carrier read through an installed
instance adds `arith:structure-instances` (roots: the instances — ℂ's
`Field`, `AddPowOne` and `OfRealInjective`), so a chapter over a ring of
its own depends on no instance; a member in a capability's foundation — the algebra
chapters' own laws for the first, ℂ's instance and what it rests on for
the second — may not use it, by the same gate as `arith:real`.

**A scaled premise (`coefficient`, Go `Scaled(c, h)`) — Lean's
`linear_combination c * h`.** The deciders combine the context's
equations by integers; a coefficient that is itself a term is supplied
on the premise: `by_hyps:[{hyp_index:0, coefficient:"e"},
{hyp_index:1, coefficient:"b"}]` (and `with_lemmas:[{key:…,
coefficient:"…"}]`; `term_specialize` grounds first, the instance is
what is scaled). The coefficient's text is read at the type of the
equation it scales, so beside an equation over ℤ `&q` is the integer
the goal prints as `&q₀`; where a law's carrier is settled only by its
install the text is read as it stands. The premise is installed as usual and its congruence
`c·l = c·r` under the carrier's multiplication is added beside it,
proved from the equation (keyless), so `a + b = c·d ⊢ (a + b)·e = c·d·e`
closes once `e` scales the premise — over ℂ, over ℝ and ℤ (whose linear
layers read the scaled rows over the monomial basis) and over num alike.
An equation that defines a variable needs no coefficient: `a = b·c,
d = c·e ⊢ a·e = b·d` closes with a and d read at their definitions. Two
premises that bound one difference from both sides are such an equation
without stating it (omega `paired_equation.go`): `t ≤ &0 ∧ &0 ≤ t ⊢ t·A
= &0` and `x ≤ y ∧ y ≤ x ⊢ f(x) = f(y)` close over ℕ, ℤ and ℝ, in every
spelling the linear layer reads a comparison in (`≥`, a negated strict
comparison, a difference moved across), on ℕ and ℤ with a strict
neighbour (`x ≤ y ∧ y < x + 1`), and where one of the two is the guard of
a split's branch (`x ≤ &0 ⊢ |x|·w = −(x·w)`, on the arm `&0 ≤ x`). The
pair must have a variable side, as a stated equation must. Three
comparisons in a chain (`x ≤ y ∧ y ≤ z ∧ z ≤ x`) are no pair, and an
equation with no variable side (`u·&2 = &0`) defines nothing: state the
equation the step needs (an atom's argument is the exception, below). A
premise pinned by name (a sparse `term_specialize`) takes no
coefficient; `simp_with` and `auto_with` refuse the field, having no
premise to scale.

**Two applications that differ in their arguments** (omega
`argument_congruence.go`). An application of a function or a predicate
the layers do not read is an atom to them, and two atoms are one
unknown only where they are one term. Under arith two applications of
one head are compared argument by argument instead, each pair that is
not one term asked as an equation of the arith closer itself under the
same premises, and where every pair decides equal the two are equal by
congruence. So the alignment a face or a degree needs is no step of
its own: `i + 1 < n ∧ q = n − 1 − (i + 1) ⊢ face_iterate_top(d, n, n −
1 − i, x) = face_iterate_top(d, n, q + 1, x)`, `f(n + 1 + 1) = f(n +
2)`, `f(suc(n)) = f(n + 1)`, `m ≤ n ⊢ f(n − m + m) = f(n)` and the chain
`x ≤ y ∧ y ≤ z ∧ z ≤ x ⊢ f(x) = f(y)` close. It is read three ways: an
equation between two such applications; an equation a premise equation
states up to the arguments of its sides, either way round (`f(n + 1) =
g(m) ⊢ g(m + 0) = f(1 + n)`); and a formula a premise states up to its
arguments, or whose negation one states (`i < n ∧ P(n − i − 1 + 1) ⊢
P(n − i)`, `x ∈ S(n − i − 1 + 1) ⊢ x ∈ S(n − i)`). An argument that is
an application of one head on both sides is compared the same way, and
two abstractions by their bodies, so a set-builder's bound is reached:
`{i | i < n + 1} = {i | i < suc(n)}`, `i < n ⊢ card({j | j < n − i − 1 +
1}) = card({j | j < n − i})`. At a carrier a ring reads — a number
carrier, or a structure ring's under its `comm_ring_on` or `field_on`
fact — an equation of the ring's sums and products is the ring's own,
and only two applications the ring does not read are compared
(`g(n + 1 + 1) = g(n + 2)` for `g : num → num`); so `a + b = c·d ⊢ (a +
b)·e = c·d·e` still takes `Scaled`. A comparison of two such atoms,
`g(n + 1 + 1) ≤ g(n + 2)`, is the layers' formula and is not read by its
arguments. The plain `by` does
not compare arguments: the refuter meets the same equation through a
premise that states it ground, `n − 1 − i = q + 1`.

**At a field, a factor and its INVERSE cancel** wherever they stand in
a monomial, as over ℝ (next section), on the context's evidence that
the factor is not zero; the cancellation reads the field's own left
inverse law (`field.MulLeftInverseOn`). So over ℂ the primitive αz +
βz²/2 of a linear function differentiates back by one bare `by
{arith:true}` — `α·&1 + β/&2·(&1·u + u·&1) = α + β·u`, with no premise
at all (the literal's evidence is ℝ's, below) — and `y ≠ &0 ⊢ x / y ·
y = x` and `z ≠ c ⊢ (f − p) / (z − c) · (z − c) = f − p` close the
same way, at an abstract field with the fact named, and on a carrier
set with the memberships too. The closer adds `R · (inv(t)·t)
= R` for each cofactor R the sequent multiplies the pair by, read off
the goal and the context's equations, and combines them with those
equations — only once the context's equations alone decline, so a goal
that closed without them closes as it did. The EVIDENCE is the
context's: `t ≠ zero` resident (a premise or a conjunct of one, either
way round), or a resident disequality that `t = zero` contradicts by a
ring identity or an integer combination — `z ≠ c` for the divisor `z −
c`. At an abstract field a LITERAL is not nonzero on its own: a field
may have a characteristic (`&2 = &0` holds in characteristic 2), so
`F.one + F.one ≠ F.zero` is a premise to name. An instance that names
an injective EMBEDDING OF ℝ has characteristic zero, and there an
embedded real is nonzero on ℝ's evidence: ℂ's instance names
`complex_of_real`, injective by `complex_field.OfRealInjective`, whose
value at `&0` is ℂ's zero, so the divisor `complex_of_real(r)` is
nonzero wherever ℝ's closer shows `r ≠ &0` — a literal by itself (`&2`,
`-&2`), or a sign the context states (`&0 < r`, `a < b` for `r = b −
a`) — and injectivity carries it across. So no premise is named for a
literal divisor over ℂ, nor for a real of known sign lifted into it.
The step is ℝ's arithmetic, so a member in `arith:real`'s foundation,
where that is withheld, names the premise as at an abstract field. As
over ℝ, every pair a monomial holds cancels, the inverse of a product is
read as the product of the inverses, and a product shown nonzero is
evidence for each of its factors; with no evidence nothing cancels.

**The ring refutes as well as proves.** An equation the context denies
is decided false, so a context that contradicts itself at the carrier
closes its leaf. What a context denies is its disequalities and, at a
field, `F.one = F.zero` (`field.OneNotZeroOn`, never a premise to name):
an equation is refuted where it and the context's equations combine by
integers to a denied one. So over ℂ `z * w = &1 ∧ z = &0 ⊢ ⊥` closes
bare (`&0 * w = &1` reads `&0 = &1`), as do `z + &1 = z ⊢ ⊥` and
`¬(&1 = &0)`, and at an abstract field `F.mul(x, y) = F.one ∧ x =
F.zero ⊢ ⊥` with the fact and the memberships named. A commutative ring
that is no field refutes only against a resident disequality: the zero
ring is a commutative ring, and there `R.zero = R.one`. At a field the
terms that are not zero are closed under the product, the inverse and
the quotient, and the closer reads that both ways: `g ≠ &0 ∧ q ≠ &0 ⊢
g * q ≠ &0`, `⊢ g / q ≠ &0` and `⊢ inv(q) ≠ &0` close, a divisor that is
such a product cancels on its factors' evidence, and `g * q = &0 ∧ g ≠
&0 ⊢ q = &0` closes — no `field.MulEqZero` cited for any of them. A
power is not zero where its base is not, at every exponent, and a power
that is zero has a zero base (`field.PowEqZeroOn`, never a premise to
name): `z ≠ &0 ⊢ zⁿ ≠ &0`, a divisor `zⁿ` cancels on z's evidence, and
`zⁿ = &0 ⊢ z = &0`. And a premise whose two sides share a factor that is
not zero gives the equation of what is left of them, the sides read by
their factors as over ℕ: `x ≠ &0 ∧ x * y = z * x ⊢ y = z`, `x ≠ c ∧ (x −
c) * y = (x − c) * z ⊢ y = z`, at ℂ and at an abstract field alike, with
no `integral_domain.MulCancelLeft` cited. A literal factor is a
coefficient to the ring and is not cancelled.

### The modulus of ℂ — its laws and its sign

A complex modulus is a real number, and ℝ's rows hold it as an unknown.
The closer reads three things about it, from the laws `complex_abs`
states, and reads them in a hypothesis as it reads them in the goal.

**Its laws across ℂ's operations, as rewrites toward the leaves.** A
modulus of a product, a quotient, an inverse, a power, a negative, a
conjugate, an embedded real or `complex_i` is rewritten by
`complex_abs.AbsMul`, `AbsDiv`, `AbsInv`, `AbsPow`, `AbsNeg`, `AbsConj`,
`AbsOfReal` and `AbsI`, until every modulus left stands on a term none
of them reads. So `|z * w| = |z| * |w|`, `|z / w| = |z| / |w|`,
`|z ^ n| = real_pow(|z|, n)`, `|-z| = |z|`, `|conj(z)| = |z|`,
`|&x| = |x|` and `|complex_i| = &1` close by one bare `by {arith:true}`,
nested as they come (`|&r * (z * conj(w))| = |r| * (|z| * |w|)`), and a
hypothesis spelled one way meets a goal spelled the other:
`|z * w| ≤ B ⊢ |z| * |w| ≤ B`, `|a * z ^ n| ≤ B ⊢ |a| * real_pow(|z|, n)
≤ B`. No `Simp(Fwd(complex_abs.AbsMul), …)` goes before an arithmetic
close, and no instance of these laws stands among its premises. What
`|&x|` leaves is ℝ's `|x|`, read as ℝ reads it: split on its sign,
and under a product or under a symbolic power read at the arm its
branch pins it to.

**Its sign.** `&0 ≤ |t|` stands beside the hypotheses of every decision,
for every modulus the hypotheses and the atom being decided spell
outside a binder, as `&0 ≤ &n` does for a cast. So `&0 ≤ |z| * |w|`,
`a ≤ b ⊢ |z| * a ≤ |z| * b` and `|z| ≤ &1 ∧ |w| ≤ &1 ⊢ |z * w| ≤ &1`
close with no `complex_abs.AbsNonneg` named: the sign is a monomial's
factor sign and a scaling's side condition like any resident one. A
strict sign the context states, `&0 < |z|`, is the one read.

**Its zero test.** A term and its modulus vanish together
(`complex_abs.AbsEqZero`, `AbsPosIffNonzero`), and the closer carries
that across the two layers in both directions (omega `modulus_zero.go`).
What ℂ's ring shows of a modulus's argument is a fact about the
modulus: `z ≠ &0 ⊢ &0 < |z|`, `z ≠ c ⊢ &0 < |z − c|`, `z = w ⊢ |z − w| =
&0`, and with nothing resident `|c − c| = &0`, so a disc holds its
centre, `&0 < r ⊢ |c − c| < r`. What ℝ's rows show of a modulus is a
fact about its argument: `&0 < |z − c| ⊢ z ≠ c`, `|u − v| < |u| ⊢ u ≠
&0`, `|z| ≤ &0 ⊢ z = &0`, and a divisor has its evidence from a
punctured disc, `&0 < |z − c| ⊢ f / (z − c) * (z − c) = f`, a power of it
included. Neither law is cited in an arithmetic close, and no `Have`
carries `z ≠ c` to `&0 < |z − c|` or back for one. The ring is asked
about the moduli a decision spells, and ℝ about the moduli the premises
spell; a disequation whose term no modulus spells (`&r * exp(…) ≠ &0`)
is the ring's own to show, by its factors.

**What stays a cited law.** A sum or a difference under a modulus is
one unknown, as spelled. ℝ's `|x − y| = |y − x|` and `|x + y| ≤ |x| +
|y|` close because ℝ's absolute value is decided by cases on a sign,
and ℂ's is not. So the swap is `complex_abs.AbsSubComm`; an estimate of
a sum is `AbsTriangle`, `AbsSubTriangle` or `AbsTriangleReverse` at the
point the argument chooses; a part against the modulus is `ReLessEqAbs`,
`ImLessEqAbs` or `AbsLeParts`. Inside a `By`, which reads no
arithmetic, the zero test is cited too (`AbsPosIffNonzero`,
`AbsEqZero`).

The laws rewrite a modulus the sequent SPELLS. From a resident
`x = a * b` the closer does not take `|x| = |a| * |b|`: rewrite with
the equation first (`eq.Rw()`, then `ByArith(…)`), which puts the
product under the modulus where the laws read it. A cited `AbsMul`
instance does not do this. The closer applies the law to the instance
as to every hypothesis, and what is left of the premise is `⊤`.

The capability is `arith:modulus` (roots: the eleven laws — the sign,
the eight rewrites, and the two of the zero test). A member in
its foundation — `complex_abs`'s own laws and what they rest on — may
not use it, by the same gate as `arith:real`.

### What the closer reads on its own

A monomial's SIGN reaches the rows as well (over ℝ and ℤ alike), so the
closer combines it with everything else. It comes from the factors' RESIDENT signs
(`&0 < a ∧ &0 < b ∧ a·b ≤ c ⊢ &0 < c`; `a ≤ &0 ∧ &0 ≤ b ∧ &0 < a·b + c
⊢ &0 < c`), or from the monomial being a SQUARE, which needs no
hypothesis at all — every base atom occurring an even number of times
is enough, so `x·x ≤ y ⊢ &0 ≤ y` and `x·x + y·y = &0 ⊢ x·x = &0`
close, `((a·a)·b)·b` included. The factors need not be base atoms: a
sign the context states about a PRODUCT or a QUOTIENT prices every
monomial that product divides (`&0 < a·b ∧ &0 < a ∧ a·a·b ≤ c ⊢ &0 <
c`; a tolerance `η = e / d` with `&0 < η` and `&0 < e` resident prices
e·e·inv(d), where d has no sign in sight), and an inverse atom takes
its sign from its argument's (`&0 < a ∧ &0 < v ∧ a / v ≤ c ⊢ &0 < c`).

A power with a LITERAL exponent is the monomial it denotes, so
`real_pow(x, 2)` and `x * x` are one unknown: a hypothesis spelled one
way meets a goal spelled the other, and `real_pow(x + y, 2)` expands.
The term is untouched, so `PowTwo` is needed only where a proof step
genuinely wants the product written out. `int_pow` and num's `nat_pow`
read the same way.

A cast of a num SUM, PRODUCT or successor written in a real or int term
is the sum or product of the casts it denotes (omega `cast_basis.go`):
`&(m + 1)` is `&m + &1` and `&(a * b)` is `&a * &b`, so `&m` and
`&(m + 1)` are one unknown and a constant apart —
`&m ≤ A ∧ A + &1 < B ⊢ &(m + 1) < B` is linear, as it is with the num
fact `m ≤ k` resident, whose lift was always written over the casts of
its leaves. The term is untouched; no `OfNumAdd` rewrite goes first. The
cast of a truncated difference `&(a - b)`, of a power or of a variable
is the unknown it was: num's difference stops at zero, so that one is
rewritten by the law that carries its guard.

A quotient by a SYMBOLIC divisor is the monomial `u · inv(v)` it
denotes (ℝ only; omega `quotient_basis.go`), in the model, the
certificate and the signed normalizer alike, so quotients over one
divisor combine and a quotient is linear beside the facts that name
it: `(f + g − (p + q)) / (x − c) = (f − p) / (x − c) + (g − q) / (x −
c)`, the same for a scalar multiple, a negative and a product; `q = a /
v ∧ r = b / v ⊢ (a + b) / v = q + r`. No `Unfold(real_field.RealDivDef)` before an
arithmetic close. The term is untouched, so the field handler goes on
clearing the `/` the author wrote (`&0 < v ∧ a ≤ b·v ⊢ a / v ≤ b`), and
a LITERAL divisor keeps its stronger reading (below). Nothing about the
divisor is assumed: `x / y = x · inv y` is the definition.

The INVERSE OF A PRODUCT is the product of the inverses it denotes,
`inv(a · b)` read as `inv(a) · inv(b)`, in the same three readers (ℝ and
a field's structure ring alike), so a divisor that is a product lands in
the basis its factors' inverses land in: `x / a · (y / b) = x · y / (a ·
b)` is a ring identity, with no premise and no `InvMul` cited. Nothing
about the factors is assumed: the law holds of every pair, zero included.
What the context says of the PRODUCT still serves, read at the factors: a
product shown nonzero — `a · b ≠ &0`, `&0 < a · b`, `2πi ≠ 0` at ℂ — is
evidence that each factor is (in a field the two say the same), and a sign
stated of `a · b` is the sign of `inv(a) · inv(b)` together, which is what
a quotient by it needs, though it prices neither inverse alone.

A factor and its INVERSE cancel wherever they stand in a monomial, on
evidence that the factor is not zero (over ℝ here; a field's, ℂ's
included, is the structure ring's, above): `v ≠ &0 ⊢ a / v · v = a`;
`x ≠ c ⊢ (f − p) / (x − c) · (x − c) = f − p`; `u ≠ &0 ∧ l ≠ &0 ⊢ (inv u
− inv l)·(u·l) = l − u`, whose pairs exist only after the product is
multiplied out, one in each monomial; and SEVERAL pairs in one monomial,
`a ≠ &0 ∧ b ≠ &0 ⊢ x / a · (y / b) · (a · b) = x · y`, each divisor on
its own evidence. The closer injects `R · (inv(t)·t) = R` for each
cofactor R a pair stands under (omega `unit_facts.go`,
`real_unit_facts.go`): read off the sequent's own monomials first, and
then off each cofactor found, which is the monomial the fact reduces to —
the second pair's cancellation exists only there. A divisor that is a
product cancels factor by factor, `a ≠ &0 ∧ b ≠ &0 ⊢ x / (a · b) · a · b
= x`, one factor at a time, `b ≠ &0 ⊢ x / (a · b) · b = x / a`, and on the
product's own evidence, `a · b ≠ &0 ⊢ x / (a · b) · a · b = x`. The
facts of one decision are capped (twenty-four), which four pairs in one
monomial exceed: split such a monomial by a step. The EVIDENCE is read in each form a context
holds it (`real_nonzero.go`): `t ≠ &0` as written, or in the square
form `&0 < t·t` the arith step itself rewrites it into; a strict sign
of t, stated or a linear consequence of the context (`a < b` for the
divisor `b − a`); for a difference, `x ≠ c` or `&0 < |x − c|` —
what a punctured ball hands over; and, for a factor, a disequality or a
strict comparison whose two sides become one polynomial with &0 put for
it — `a · b ≠ &0`, `&0 < a · b`. A goal `x − c ≠ &0` closes on the same
evidence. With no evidence nothing cancels: `a / v · v = a` fails at
v = &0, and `&0 ≤ v` is not evidence.

A product compared with its OWN bare factor is the monotone scaling with
`&1` in the empty slot, over ℝ and ℤ alike: `&0 < x ∧ x ≤ &1 ⊢ x·x ≤ x`,
`&0 ≤ x ∧ &1 ≤ y ⊢ x ≤ y·x`, `&0 < x ∧ a < &1 ⊢ a·x < x` — the factor's
sign and the comparison of the other factor with `&1` are the closer's
own side conditions, exactly as for `x·a ⋈ x·b`. A product against a
bare factor that is NOT one of its own (`η·η + w ≤ η + w`) is not a
scaling shape and stays out.

A positive factor is cancelled out of a HYPOTHESIS, over ℝ and ℤ
alike (omega `real_cancel.go`, `int_cancel.go`): `&0 < P ∧ P·a ≤ P·b
⊢ a ≤ b`, the strict comparison and the factor on the right likewise.
The sign is the closer's own side condition and must be STRICT —
`&0·a ≤ &0·b` holds for every a and b, so `&0 ≤ P` cancels nothing.
An EQUATION cancels a factor on weaker evidence, that it is not zero:
`x ≠ &0 ∧ x·y = x·z ⊢ y = z` over ℝ as over ℤ, whatever the sign of x
and however its being nonzero is held — a disequation, a sign, `x ≠ c`
for the factor `x − c`. Over ℝ the two sides are read by the factors
they share, so `x·y = z·x` and `x·y·w = x·z·w` cancel as `x·y = x·z`
does, each factor on its own evidence; no `real_ring.MulLeftCancel` is
cited.

The PAIRWISE PRODUCTS of the context's differences are rows too — the
step Lean's `nlinarith` adds to `linarith` (omega `real_products.go`,
`int_products.go`): every comparison the refutation holds, the negated
goal included, is a nonnegative difference, and the product of two of
them is nonnegative, so `x·y = &1 ∧ &0 < x ⊢ &0 < y` closes from
`(&0 − y)·x ≥ 0` beside the equation, `a ≤ b ∧ c ≤ d ⊢ a·d + b·c ≤ a·c
+ b·d` from `(b − a)·(d − c) ≥ 0`, and `&0 ≤ s ∧ s·s = y ∧ &0 < y ⊢ &0
< s` from `(&0 − s)·s ≥ 0`. A strict difference meets a non-strict one
through the weakening `l < r ⊢ l ≤ r`, whatever the difference is
written over: `&0 ≤ t ∧ t ≤ &1 ∧ x < y ⊢ x ≤ t·x + (&1 − t)·y`, `t ≤ &1
∧ A < r ⊢ &0 ≤ (&1 − t)·(r − A)`. The pass
runs last, only once every cheaper handler has declined, and only where
a constraint carries a product; the facts multiplied are the first
twelve, the products of three or more stay out, and so does a product
with a quantity no fact bounds (`a ≤ b ⊢ a·c ≤ b·c` wants the sign of c).

A NUM hypothesis reaches a real or int refutation through its cast
(omega `domain.go` liftHyp): `a ≤ b` is the row `&a ≤ &b`, the cast
pushed to the leaves (`&(a + 1)` is `&a + &1`), and a strict `a < b` is
also its integrality `&a + &1 ≤ &b`, so `a ≤ b ⊢ &a ≤ &b`, `b < a + 1 ⊢
&b ≤ &a` and `4 ≤ n ∧ x·x ≤ &4 ⊢ x·x ≤ &n` close with nothing cited.
The goal-side collapse of images (`&n·&n = &(n·n)`, `&0 ≤ &n·&n`) stays
hyp-free on purpose: the arith step drops a hypothesis decided ⊤ under
the others, and a comparison of images decided from num facts the rows
did not hold would take with it what the refutation still needs.

### The zero test

Whether a term is zero is read on both sides of the turnstile, in
either spelling of the equation, and of a product through its factors,
at every carrier.

A GOAL that denies a variable a value, `¬(v = e)`, is decided by the
reading a premise `v = e` gets (omega `denied_value.go`): the value is
read into the premises that name v — under a product, inside an atom —
and a premise it makes false refutes it. So `g * u = &1 ⊢ ¬(u = &0)`
closes over ℤ, ℝ and ℂ (`g * &0 = &1` is false), `¬(g * u = &0) ⊢ ¬(u =
&0)`, `x * w < y * w ⊢ ¬(x = y)`, and through a definition `0 < r ∧ r =
g * v ⊢ ¬(v = 0)`. On ℕ a variable is positive exactly where it is not
zero, so the goals `0 < v`, `1 ≤ v` and `v > 0` are read the same way:
`0 < g * u ⊢ 0 < u`, `1 ≤ g * u ⊢ 1 ≤ u`. The goal must deny a VARIABLE
a value; a compound term's is the next paragraph's, or a premise. A
STRICT goal is read the same way beside the opposite bound: `a < b`
denies `b ≤ a`, which beside a premise `a ≤ b` is the equation `a = b`
(the pair of the scaled-premise paragraph above, from the other side of
the turnstile), so `x ≤ y ∧ ¬(f(x) = f(y)) ⊢ x < y` and `&0 ≤ t ∧ &0 <
t * A ⊢ &0 < t` close over ℕ, ℤ and ℝ, the goal in any spelling (`y >
x`, `¬(y ≤ x)`). A goal that puts a term AT zero is read from the other
side too: its denial is the nonzero evidence a cancellation asks for,
so `z = c * z ∧ &1 < c ⊢ z = &0` closes with no zero-product law cited
— were z not zero it would cancel, leaving `&1 = c`.

On ℕ a PRODUCT is zero exactly where a factor is (omega
`nat_products.go`), which is ℤ's and ℝ's zero-product split and their
sign rows in one law. A premise `a * b = 0`, the zero on either side,
is split into `a = 0 ∨ b = 0`: `g * q = 0 ∧ g ≠ 0 ⊢ q = 0`, `x * x = 0 ⊢
x = 0`. A product whose factors are shown positive — by the linear
layer, by a resident `t ≠ 0`, or factor by factor — is positive, in the
goal and in a premise alike: `0 < g ∧ 0 < q ⊢ 0 < g * q`, `1 ≤ g ∧ 1 ≤ q
⊢ 1 ≤ g * q`, `g ≠ 0 ∧ q ≠ 0 ⊢ g * q ≠ 0`, `0 < g ∧ 0 < q ∧ g * q + a ≤
c ⊢ a < c`, and under a truncated difference `a ≠ 0 ∧ t ≠ 0 ⊢ suc(a * t
- 1) = a * t`. No instance of `nat_arith.MulEqZero` is cited for these. The
factors' own positivity is the closer's side condition: with `0 < g`
alone `0 < g * q` does not follow, and does not close.

The ZERO stands on either side. A zero test is carried through an
inverse, a negation and a quotient (`inv x = &0`, `-x = &0`, `¬(x =
&0)`), and each of these reads `&0 = …` as it reads `… = &0`, in the
goal and in a premise: `g ≠ &0 ∧ q ≠ &0 ⊢ ¬(&0 = g * inv(q))` closes as
`⊢ ¬(g * inv(q) = &0)` does, with the evidence spelled `¬(&0 = g)` as
well. Over ℝ a premise `a / b = &0` is the zero product `a * inv(b)`
and splits into `a = &0 ∨ b = &0`. A field's own zero tests are the
structure ring's (above).

A POWER is zero only where its base is, at every exponent. Its base's
evidence is the power's: `r ≠ &0 ⊢ rⁿ ≠ &0`, and a divisor `rⁿ` cancels
on `&0 < r`, on `r < &0` or on `r ≠ &0`, with no `&0 < rⁿ` stated
(`&0 < r ⊢ M / rⁿ · rⁿ = M`). Read from the other side, a premise `rⁿ =
&0` puts r at zero: `rⁿ = &0 ⊢ r = &0`. Over ℕ the same is positivity:
`0 < x ⊢ 0 < xⁿ`, a power of a positive base cancels as a factor, and
`xⁿ = 0 ⊢ x = 0 ∧ 0 < n`. A power that is not zero says nothing of its
base, the exponent being free to be zero.

### What still needs a premise, and what does not

What still needs a premise, because it is not linear over the
monomials:

1. A monomial's sign when no sign of its factors, or of pieces that
   multiply to it, is resident — `&0 < a ⊢ &0 < &2·(a·b)` does not
   close; cite the sign fact (`real_order_ring.MulPos`). (Factors whose
   signs differ in STRICTNESS do price the monomial, non-strictly, the
   strict fact weakened first: `&0 < a ∧ &0 ≤ b ∧ a·b ≤ c ⊢ &0 ≤ c`. And
   an inverse standing alone takes its sign from its argument's, so a
   quotient is priced through an equation and inside a sum: `s = x / p ∧
   &0 < p ∧ &0 ≤ x ⊢ &0 ≤ s`, `&0 ≤ M ∧ &0 < x ⊢ &1 ≤ (M + &1) / x + &1`.)
2. A symbolic divisor cleared from a HYPOTHESIS — `&0 < v ∧ a / v ≤ b ⊢
   a ≤ b·v`. The field handler clears a goal; a hypothesis's quotient
   is read as the monomial a·inv(v), and multiplying the row by v is
   division by a variable. Cite `real_order_field.LessEqDivMulRight`.
   (The converse of a sign row — a FACTOR's sign off the monomial's,
   `x·y = &1 ∧ &0 < x ⊢ &0 < y` — is a product of the negated goal with
   the sign fact and closes through the products pass.)
3. A symbolic divisor cleared from a goal that carries a SUBTRACTION
   in the NUMERATOR or on the OTHER SIDE of its quotient: `&0 < v ∧ f −
   p ≤ φ·v ⊢ (f − p) / v ≤ φ`; `&0 < v ∧ a ≤ (φ − ψ)·v ⊢ a / v ≤ φ − ψ`;
   `x ≠ c ∧ f − p = φ·(x − c) ⊢ φ = (f − p) / (x − c)`. The subtraction
   is moved across before the field handler runs, the quotient is then
   monomials `·inv(v)` on both sides and no longer a side of the
   comparison, and what is left is a hypothesis scaled by inv(v) —
   division by a variable once more. (A subtraction in the DIVISOR
   alone clears: `c < x ∧ a ≤ φ·(x − c) ⊢ a / (x − c) ≤ φ`; so does a
   goal with no subtraction: `v ≠ &0 ∧ f + p = φ·v ⊢ (f + p) / v = φ`.)
   For an equation, rewrite the goal's numerator by the hypothesis
   first (`h.Rw()`, then `ByArith(<the evidence>)`): `φ = (φ·(x − c)) /
   (x − c)` is a unit pair, and the closer's. For an ordering, state
   the quotient times its divisor as a fact (`(f − p) / v · v = f − p`,
   the closer's too): with it resident the ordering closes, the product
   of the fact with the divisor's sign being the row that was missing.

Items 2 and 3 are one boundary, held on purpose. A divisor is cleared
where the quotient is a whole side of the GOAL and nowhere else — not
among the goal's summands, not in a hypothesis. Clearing from the
summands costs nothing and gains little; clearing from a hypothesis
gains nothing and doubles, at the least, every decision that fails on a context holding a
quotient — and the arith step decides each hypothesis under the others,
decisions that are made to fail. One without the other is a closer that
reads a quotient in the goal and not the same quotient in a hypothesis,
so neither is in.

The failing `by`'s hint names these.

Three shapes that need no premise: a division by a literal in a HYPOTHESIS
(`x/&2 ≤ y ⊢ x ≤ &2·y` — it clears as a rewrite, wherever the simp runs), a
`&n` coercion (an opaque atom, and over ℝ a nonnegative one), and a SQUARE
written out with a subtraction (`⊢ &0 ≤ (x−y)·(x−y)`, and the same square
bounding something in a hypothesis). Such a square stays ONE unknown, so it keeps its sign; and the
same unknown also gets its expansion as a row of its own, `(x−y)·(x−y) +
&2·x·y = x·x + y·y`, so an identity that needs the square multiplied out
(the two-squares identity behind `|z·w| = |z|·|w|`) closes beside the sign
facts rather than instead of them. A POWER of such a base is the same
square spelled otherwise: the pow basis reads `real_pow(t, c)` /
`int_pow(t, c)` with a literal exponent as its monomial only when `t` carries
no subtraction or negation, so `real_pow(−x, 2)` and `real_pow(x − y, 2)`
stay one unknown each — and each gets its expansion as a row too, from the
power's own unfold, so `real_pow(−x, 2) = real_pow(x, 2)`,
`real_pow(−&1, 2) = &1` and `real_pow(−x, 3) = −(x·x·x)` close with no
premise. And a GROUND equation premise between two compound terms of one
carrier — a number carrier or a ring fact's: `pi / &2 = &2`, `x + y = &3`,
`A′ = −A` at a `comm_ring_on` — is substituted, bigger side to smaller (an
abstraction's body counted with it), into the goal before the closer reads it, so an atom whose argument
is spelled one way meets the same atom spelled the other way as one unknown:
`pi / &2 = &2 ⊢ real_cos(pi / &2) = real_cos(&2)` closes, as it always did
in a `By` (the refuter's demodulation). What that pass does not do is
expand — an equation whose smaller side is an atom with variables
(`real_cos(x) = …`) is never applied in the growing direction, so a
definition's instance that the goal needs multiplied out is still the
author's `Rw`. An equation premise with a VARIABLE on one side, `v = e`,
is the other rule: it defines v, and a decision has two readings. The
closer first decides the goal as the premises spell it, v one unknown —
which is what a name is for: with `d` standing for a difference,
`-(&2 * s) ≤ d ∧ d ≤ &2 * s` gives `d ^ 2 ≤ &4 * s ^ 2` as one product of
two premises. Where that does not decide it, the goal and every premise
are read with v at e together, at each of those carriers — a value
(`t = &0`, so `t * A = &0` closes and `y ≤ t * A` reads `y ≤ &0`), or a
definition whatever its variables are called (`a = b + c`, so
`a * x = b * x + c * x` is a ring identity; `ρ = |c| + δ`, read in the
goal's `ρ ^ n` and in a premise's alike). Each variable has one
definition, a value before any other, and the definitions do not run in a
circle: `a = b + &1` beside `b = a + &1` defines a and leaves the second
an equation. A ring's own elements are not defined — over a
`comm_ring(add, zero, …)` stated on variable components `p - r = zero`
pins a difference and `x = zero` defines x. A FUNCTION is defined the
same way: a premise `F = λx. e` with F a variable — the equation of a
function-valued `a.Let` or of a session `let` — defines F, and the second
reading takes `F(s)` as e at s and F standing alone as the λ, in the goal
and in every premise together: `a = λi. x(i) − h ∧ &0 < h ⊢ a(i) < x(i)`
closes with the Let's equation among the premises and no `Rw` before it.
A set written by a builder is no λ and is not read this way. A goal neither reading
decides stays as the author wrote it, and so does a premise, which the
second reading can only find contradictory. In a `by {arith:true}` close
with nothing else left to fire, the leaf is read whole at the definitions
— every premise and the goal, the defining equations gone
with their variables — before the rounds go on. Every other
product carrying a
subtraction still expands, which is what `x·(a−b) ≤ c ⊢ x·a ≤ c + x·b`
needs. A fourth: a division by a
literal BESIDE another summand, in a hypothesis or the goal (`&0 < e ⊢ x < x +
e/&2`, `s − e/&2 < y` resident, `(c + d/&2) − c = d/&2`) — the quotient is a
linear unknown with its defining equation `y = (y/&k)·&k` injected, so it is
read wherever it stands, not only as a whole side of an atom — and where it
MULTIPLIES, the equation is injected times the cofactor, so the product is a
linear unknown too (`&2·a ≤ d ⊢ a ≤ &1/&2·d`).

## Diagram chases in `by {chase}` — what it reads, and what stays out

One step of an abelian diagram chase — a preimage through an exactness
or an onto map, an element a map kills, two elements of one coset, an
equation between elements of a module — closes as `by
{chase:{depth:k}}` over the premises that name the diagram (Go
`ByChase(Depth(k), premises…)`). The closer searches nothing: it reads
the facts by shape, decides by integral polynomial-module algebra, and
derives the kernel certificate from the chapters' carrier laws
(installed by library/serve). An element is a linear combination of
homomorphism words applied to generators (the elements the leaf names
and the preimages the chase introduces), with coefficients in the
integer polynomial ring on the leaf's scalar atoms. Homomorphisms
preserve these coefficients. The scalar ring is the commutative ring
supplied by `module_on(R, M)`; scalar sums, differences, negations and
products normalize, and supplied scalar equations generate coefficient
relations at every module generator. Equality and image membership
return polynomial combinations of the supplied relations; a kernel
modulo target relations is computed by elimination from the graph of
the homomorphism. The polynomial backend uses strong standard bases
over ℤ, with both cancellation and gcd pairs, and retains every row's
expression over the inputs. The constant case uses Hermite form. No
scalar or integer is inverted: a module may have torsion (`2x = 0` does
not give `x = 0`, and `2x = 0 ∧ 3x = 0` does). These decisions concern
the displayed polynomial presentation, not hidden identities of an
arbitrary concrete ring. Every accepted combination is reconstructed
from the proved ring, module and homomorphism laws.

**What it reads** (by the head constant, in a hypothesis as in the
goal, an equation in either orientation):

- `module_on(R, M)` — a module whose operations and carrier are fields
  of the record `M`, over the ring record `R`. A universally quantified
  family over degrees is read at the degrees the leaf spells.
- `module_homomorphism(R, M, N, f)` — an edge that supplies both endpoint
  module structures through `HomSource` and `HomTarget`; separate module
  premises are unnecessary. `f(u + v)`, `f(−u)`, `f(0)` are linearized
  through it, using each endpoint's own operations. Supplied defining
  equations reduce record projections and `restrict_module`,
  `quotient_module`, `complex_module`, `homology_module`, and
  `cohomology_module`, so a packed endpoint and a module fact at its
  parts name the same module. The leaf is read in one normal form, the
  one the other closers read it in: the definitions and the projections
  reduced and every application of a λ computed. A packed complex holds
  its terms and its differentials as λs over its degrees, and what
  `free_complex(R, S, d).terms(n)` gives is the set a membership spells
  out, its differential there the map spelled out. The By composite puts
  the leaf in that form
  before `Normalized` or `PreNormalized` can substitute a zero alias;
  this gives the substitution the same components in both spellings.
  Every expansion uses a supplied, proved equation under the chase
  capability. Conflicting operations on one carrier are refused.
  A homomorphism given by a λ, `module_homomorphism(R, M, N, λw. T(S(w)))`,
  is read by its body: `T(S(u + v))` is its value at `u + v` and is
  linearized as `f(u + v)` is for a named `f`, and a fact or a goal that
  states the map's value at a variable it binds — one-to-one, onto
  pointwise, a preimage asked — names the map by that value. The reading
  is first-order: a value in which the argument is itself applied, or
  has a part taken that computes away, is not read back, and is an
  element by its own membership.
- `x ∈ M.carrier` — a generator at a record module; `c ∈ R.carrier` —
  a scalar (at a packed value its carrier reduced, `x ∈ P.terms(n)`), so `c • u` is an
  element. Scalar memberships are derived through the ring's closure
  laws. The module action distributes over both additions, composes
  products, respects zero, one and negation, and passes through a named
  homomorphism by `HomSmul`. Relations may be multiplied by arbitrary
  polynomial coefficients in the named scalars.
- `l = r` between elements — a relation; a side that is no element yet
  while the other is an element of `M` is an element of `M` by the
  equation (`z = p(w)` with `p(w) ∈ B` gives `z ∈ B`). A variable equal
  to a zero (`b = zero'`) is read as that zero at every module whose zero
  it is, every module of one type sharing it; a map's image equal to a
  zero (`dd(n)(u) = zero'`) is a relation, read once the map is.
- `∀u. u ∈ M ⇒ l(u) = r(u)` — an equation schema (a commuting square, a
  boundary's `d ∘ d = 0`, a chain homotopy), instantiated at every
  generator of `M` the chase knows, the preimages it introduces
  included; scalar multiples follow from relation closure. A scalar
  coefficient depending on the schema's module binder is refused as
  non-linear. An opaque module application introduced by a schema is
  read through its equation, but does not seed further schema
  instances. Its named homomorphism images inherit that restriction,
  so an opaque map cannot feed the same schema indefinitely.
- `p ⇒ q` — a grounded law (`above.At(m, u)`, `u ∈ Q(m + 1) ⇒ …`) read
  as `q` once `p` holds: a premise stating `p`, or a membership or an
  equation the diagram decides from what it has read, a conjunction
  conjunct by conjunct. Pending guards are retried after saturation and after each pull-back
  round. A guard still undecided stays in the report's "not read" list.
- `exact_at(e, A, B, g, f)`, or `image(g, A) = group_kernel(e, B, f)` —
  exactness at `B`, read both ways: `f(g(a)) = e`, and an element of `B`
  that `f` provably kills has a preimage under `g`.
- `image(p, A) = B`, or `∀z. z ∈ B ⇒ ∃u. u ∈ A ∧ p(u) = z` — onto: every
  element of `B` has a preimage.
- `injective_on(A, g)`, or its definition's `∀u v. u ∈ A ∧ v ∈ A ∧ g(u) =
  g(v) ⇒ u = v` — one-to-one: an element of `A` that `g` provably kills
  is zero.
- `x ∈ image(f, A)`, `x ∈ group_kernel(e, B, g)` — a witness introduced
  at once; a membership and a relation.
- `submodule(R, M, N)` — `N ⊆ M`, and the subgroup the coset law needs.
- `left_coset(add', x, N) = left_coset(add', y, N)` with such an `N` —
  reduced to `add'(neg'(x), y) ∈ N`, as a hypothesis and as a goal
  (`group.LeftCosetEqOn`); `N` is then read as an image or a kernel.
- `∀n:num. …` — a fact over degrees, instantiated at every `num` term
  the leaf spells, and once more at the degrees that first reading
  spells and the leaf does not (a square read at `n` names `f(n + 1)`,
  a map only by the complex's facts read at `n + 1`); one generation,
  which is what bounds a complex's infinite diagram to the part a step
  touches. Where the scope allows nat arithmetic every degree is read in
  its nat ring normal form, in the conclusion, the hypotheses and every
  instance alike: `(n + 1) + 1` and `n + 2` are one degree, `0 + 1` and
  `1` another, whichever a definition's clause, a fact read at `n + 1`
  or the leaf spells, and the certificate is carried back to the leaf's
  own spelling; a degree known only through a hypothesis
  `n = m + 1` is not, and the author substitutes it first: `nEq.Rw()`
  moves the goal and every hypothesis together, each handle following
  its hypothesis to its rewrite; `By(Normalized, fact, nEq)` carries
  one fact across keyless and leaves the context as it stands.
- A map is any term applied to an element, the member `d(n + 1)` of an
  indexed family included, so long as a `module_homomorphism` fact names
  that term.

**What it decides**: an equation between elements; a membership in a
module, an image or a kernel; `∃u. u ∈ A ∧ f(u) = t` (either order,
either orientation of the equation); a coset equation; and the facts it
reads, stated as the goal: `injective_on(A, g)` (two fresh points, the
definition's antecedents assumed, `x = y` chased), `exact_at(e, A, B, g,
f)` (its definition's set equation), and an equation `S = T` between
module carriers, images and kernels — onto as `image(p, A) = B` among
them — which extensionality makes two memberships of a fresh point,
each chased at the same depth. A conjunctive goal is split by the
conditioning stage first, each conjunct its own leaf. An existential
preimage goal names one homomorphism and one equation. For a composite
or simultaneous equations, expose each lift separately and reuse a
proved construction such as `CycleLiftPullback` or `CocycleLiftPullback`.

**Depth**: round 0 reads the premises, introduces the witnesses they
hold outright and decides. Each further round pulls back — at every
exactness, a basis of the elements the outgoing map provably kills and
the incoming map does not yet provably reach; at every onto map, every
element not yet reached; at every one-to-one map, the elements it kills
become zero — saturates the squares over what it introduced, and
decides again. A round that introduces nothing ends the chase. The
depth is the number of rounds the step needs, not of preimages: one
round carries every link of a chain taken in that order (an exactness,
then an onto map, then a one-to-one elimination), and a link that must
wait for a later kind starts the next round. The closer's tests measure
the shapes: the connecting
homomorphism's pull-back 1, its cycle condition 1 (an elimination), the
four lemma's injective half 3 (as `x = y` and as `injective_on`), its
surjective half 3 (as a preimage and as `image(f, A) = B`), an exactness
goal 1. A depth one
short fails and says so; a depth too large costs nothing but the
rounds that introduce nothing.

**Failure is loud**: close-or-fail, no fall-through to the refuter.
The report names the rounds run, the element and the module the goal
stayed outside after them (`d(u) is not in the image of i`, an equation
whose difference stays outside the polynomial module the relations
generate), every hypothesis the closer could not read and why, and the
witnesses each round introduced. A diagram with a cycle (an
endomorphism) is refused by the edge that closes it.

**What stays out** — each a one-cite step or the author's structure,
not a capability the closer does half of:

- Non-polynomial scalar operations: `(−1)ⁿ`, inversion, and an opaque
  scalar function remain scalar atoms with a required carrier
  membership. Their additional identities must be supplied as
  equations; no nonzero scalar is cancelled. Equation schemas with
  coefficients depending on their module element are outside the
  R-linear reading.
- Non-abelian groups, normality, conjugation.
- Cyclic diagrams.
- Quantitative chases: an `ε`, a constant `C`, a filtration index.
- Finite sums (`module_sum`) and pointwise reasoning in a function
  module (`fun_add`, `finite_supp`): the closer reads a function as one
  element, never at its points.
- A module or a ring whose operation is given by a λ that is no named
  operation at its own arguments — a sum packed as `λs t. λk. …`, where
  `λi j. h(i, j)` reads as `h` does: the closer writes a sum as one
  operation applied to its elements, and refuses the structure by name.
- A chapter's own definitions — `cycles`, `boundaries`, `homology`, the
  connecting map's ε — are unfolded or obtained by the author; the
  closer reads the module vocabulary alone, so a cycle's `d(n)(u) = zero'`
  and a class's representative are hypotheses before the `by`.
- A membership in a submodule `N` that is neither a module of the
  diagram nor an image or a kernel.
- An integer combination whose coefficients sum past 64: the
  certificate spells each integral summand |cᵢ| times. One polynomial
  basis construction, and one reduction of a vector against a basis,
  each stop after 20000 reduction operations, and a vector past 4096
  terms stops the computation, each reported as a resource limit.
  These limits are independent of `depth`, which counts pull-back
  rounds only. Saturation also stops at 4096 monomial-labelled atoms at
  one module.

## Three arithmetic closes, worked: ε-N, ε-δ, a product estimate

The rules of the lesson above, run on three shapes a real-analysis
chapter meets at every turn — which facts each close takes, which
premises slow it, where the apply rung replaces a refutation. Read the
one whose shape is in front of you.

**An ε-N argument** is walked like this (the two-Obtain walk is
`real_sequences.LimitCommonIndex` — two limits share, for every ε, one
index past which both hold, the index `N₁ + N₂` — and LimitLessEq,
LimitSqueeze and the algebra of limits stand on it, uniqueness a
corollary of LimitLessEq). A convergence hypothesis `a ⟶ l` is
read as the ε-N statement it abbreviates by `def_expand` on the
HYPOTHESIS — bare `simp` on a conclusion-only goal does nothing — and in
Go by `a.Unfolded(converges, real_sequences.RealConvergesToDef)` (the
spelled form, `Have(<the ∀ε statement>, Unfold(real_sequences.RealConvergesToDef))`,
records the same tree), keyless. The
`∀ε` hypothesis is instantiated by the apply rung: `by {by_hyps:[{hyp_index:
<the ∀ε hyp>, terms:["(m − l) / &2"]}, {hyp_index:<&0 < ε>}]}` closes the
`∃N. ∀n. …` claim in milliseconds and records nothing (the bare `by_hyps`
form without `terms` also closes — the rung reads ε off the goal); the Go
twin is `By(nearL.At(eps), pos)`. The refuter route (the conjunction
hypothesis with `ConvergesToDef` named) closes too, and records a key per
Obtain — four keys the rung avoids. `strip_quant` Skolemizes the `∃N`, and
the names RESTART per case branch (both branches mint N₀, N₁). The closing
leaf is `by {arith:true}` on the two tail estimates at `N₀ + N₁` with the
two nat guards and `&0 < ε` resident: the arith closer reads the `real_abs`
hypotheses itself — grounding `AbsBetween` on top SLOWS it several-fold,
and so does leaving `&0 < ε` out. ε's positivity, `&0 < (m − l) / &2`
from `l < m`, is `by {arith:true}`: the CNF closer with `SubPos` and
`DivPos` named fails, because it does not evaluate the ground literal
comparison `&0 < &2`, and `OfNumLessThan` at (0, 2) does not help (`0 < 2`
is not evaluated either) — literal positivity is the arith closer's, as
real_sqrt already takes it. The tail index is `N₀ + N₁` — the corpus has no
order laws for ℕ's `nat_max` — and its two guards are one `Cite` each:
`N₀ ≤ N₀ + N₁` of `nat_order.LessEqAdd`, `N₁ ≤ N₀ + N₁` of
`nat_order.LessEqAddLeft`.

**An ε-δ argument** is the ε-N walk with a point in place of an index. The
running example is the uniqueness lemma `real_limit_at(f, c, l) ∧ real_limit_at(f, c, m) ∧ l < m ⇒ l = m`
under the definition `real_limit_at(f, c, l) ⇔ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. &0 < |x − c| ∧ |x − c| < δ
⇒ |f(x) − l| < ε`. `def_expand
real_limit_at` on the goal opens EVERY occurrence in the conjunctive hypothesis and
splits the conjuncts, a third conjunct `l < m` included — and a goal-side
`def_expand` (Go: `a.Do(Unfold(real_function_limits.RealLimitAtDef))`) unfolds the RESIDENT hypothesis
too (§"`Unfold(d Definition) Action`", "The goal and every hypothesis", has the
rule and the ways around it), so EVERY use of a conjunctive hypothesis Fact that
mentions the constant must come BEFORE the goal's Unfold: a Have reading it by
`Unfold` (after, its statement is already resident and the assert panics), and a
`By(…, limits)` citing it (after, the Fact has no single successor — the tidy split
the opened conjunction into its conjuncts — and the use fails naming the Unfold).
So such a handle is used before the goal Unfold that follows it — or the Unfold
is the last step and closes on the resident facts, as it does when its residual
is one of them. The pattern: state
the fact the proof needs from the hypothesis first (`shared := Have(<CommonRadius's conclusion>,
By(LimitAtCommonRadius, limits))`), then Unfold the goal and ground `shared` at
the ε the goal fixes. An arith leaf whose estimates still sit behind a ball
GUARD is slow, the closer discharging the guard itself; take the estimates at
the point first as a Have (`By(within.At(x), ball)`). ε's positivity and the
two `∃δ` claims go exactly as the ε-N ones (arith; `assert` + `by_hyps` with
`terms`, keyless). `strip_quant` Skolemizes each `∃δ` and leaves `&0 < δ₀ ∧ ∀x. …`
as ONE hypothesis; do NOT `expand` it — expand splits it but denotes the shared
guard as `α₀(δ, x)` and rewrites the other hypotheses through the abbreviation —
`assert` each half and close it `by {by_hyps:[the conjunction]}`. A radius below
two radii: `&0 < real_min(δ₀, δ₁)` is one cite of `real_sup_inf.LessThanMin`, and a
point of the punctured ball is `real_function_limits.PuncturedBallPoint` at that
min. Then cite `LessThanMin` a SECOND time, at the point's distance
(`LessThanMin.At(δ₀, δ₁, |p − c|)` with the ball fact): it turns `|p − c| < min`
into `|p − c| < δ₀ ∧ |p − c| < δ₁`, and every fact at the point is then plain
modus ponens (`By(within.At(point), inBall, inBoth)`) — where
`MinLowerBound` plus an arith discharge of each guard is slower by an order
of magnitude. **What the arith closer does and does not read:** an abs GOAL whose
argument is linear over atoms is INSIDE its fragment — it signs the argument
itself, `|(c + q) − c| < d` from `&0 < q ∧ q < d`, `&0 < |(c + q) − c|` from
`&0 < q`, `|k − k| < ε` from `&0 < ε`, all bare — and so is an abs term with a
bound on it resident (`|x − c| < m`, `m ≤ d ⊢ |x − c| < d`). A DIVISION BY A NUMERAL is
read wherever it stands: `y / &k` is a linear unknown tied to y by its defining
equation `y = (y/&k)·&k`, which the closer injects for every literal quotient
the sequent mentions (prover/solver/omega/real_quotient.go), so `&2 * (m / &2)
= m`, the offset `(c + m / &2) − c = m / &2`, `x < x + e / &2` from `&0 < e` and
the halved point's ball fact `|(c + d / &2) − c| < d` from `&0 < d` all close
bare, beside the whole-side shapes `&0 < m / &2` and `m / &2 < d` that always
did. The same quotient as a FACTOR is read as well: for each monomial of the
sequent that multiplies it by a cofactor R the closer injects `R·y =
R·((y/&k)·&k)`, in a hypothesis and in the goal alike, so `&2·a ≤ d ⊢ a ≤ &1/&2·d`,
its mirror `&1/&2·d ≤ a ⊢ d ≤ &2·a`, `&1/&2·d + &1/&2·d = d` and — beside a
numeral's inverse, whose pair the unit facts cancel — `real_inv(&3)·p·(&3/&2) =
p/&2` close bare; no `RealDivDef` rewrite is owed to a literal quotient before
an arithmetic close. The cost is confined to sequents that hold such a
product — a failing close over several of them is a few times slower than
without the facts — and a sequent with none is untouched. A midpoint `c + d / &2` therefore needs no `real_field.DivLeftMul` premise
(PuncturedBallPoint's older route); a SYMBOLIC divisor still needs its sign
resident. The tails
instantiate at the point (`instantiate {hyp_index, terms:[…]}`) and the close is
`by {arith:true}` on the two instantiated tails, the ball facts, `&0 < ε` and
`l < m` — the closer discharges the conjunctive guards from the resident facts.

**A product estimate under `by {arith:true}`** — the estimate behind
the product of limits, `&0 < η ∧ η ≤ &1 ∧ |a − l| < η ∧ |b − m| < η ⊢
|a·b − l·m| < η·(|l| + |m| + &1)`. The closer does three things itself: the ring
identity `a·b − l·m = (a − l)(b − m) + l(b − m) + m(a − l)` (linear over the
monomial basis once expanded), the three-term triangle
`|a·b − l·m| ≤ |T₁| + |T₂| + |T₃|` bare (the abs arguments signed by the
closer; it is slowest with the estimate's two abs hypotheses resident — so it
is closed with no premise, `by {arith:true}` / `ByArith()`, which clears
them), and the final linear combination of the term bounds. It does NOT
derive the triangle INSIDE a close that also has to combine the bounds (the
direct final close fails), and the bare-factor scaling `η·η ≤ η` it reads as a
GOAL it does not find mid-chain: rung 1 without `η·η ≤ η` resident fails, with
it as a Have it closes. It does
NOT multiply two bounds (`|u| < η ∧ |v| < η ⊢ |u|·|v| < η·η` fails bare, closes
with `LessThanMul2` ground at (|u|, η, |v|, η) and `AbsNonneg` ground),
and does not scale a bound by a factor whose sign is not resident
(`LessEqMulLeft` ground where it is, or state the factor's sign). It DOES
read `|x·y|` as `|x|·|y|`, scale a bound by an atom whose sign is
resident (`&0 ≤ u ∧ v < η ⊢ u·v ≤ u·η`), and read a product against its own bare factor as
the scaling with `&1` in the empty slot: `&0 < η ∧ η ≤ &1 ⊢ η·η ≤ η`,
`&0 ≤ x ∧ &1 ≤ y ⊢ x ≤ y·x`, strict forms alike, over ℝ and ℤ. So the
estimate is a FOUR-rung ladder, each rung one `by`, and LimitAtMul shows
which instances each rung needs: `|T₁| < η`
takes `LessThanMul2` at (|u − l|, η, |v − m|, η) and `AbsNonneg` at both
deviations (the two bounds multiplied — the one thing outside the fragment),
`|T₂| ≤ |l|·η` and `|T₃| ≤ |m|·η` take `AbsNonneg` at l resp. m ALONE (the
closer reads |x·y| as |x|·|y| and scales the bound by the signed atom itself;
an `AbsMul` or `LessEqMulLeft` instance handed over there is redundant), then
the final close bare — with the first term's bound STRICT, since the sum of
three `≤` cannot give the `<`. One shot with every one of those instances handed to
a single `by` fails: the ladder is the shape, not a workaround (the
one-shot's cost is the abs case split over eight abs atoms, not the missing
rows).

## ∀-hypothesis absorbs your `instantiate` before CNF sees it (Lesson 12)

**Pattern.** After
`instantiate(hyp_index=k, const="t")` produces the ground fact
`P(t)` from a resident `∀x. P(x)` (kept via `keep:true` OR via the
`const` form's default keep-source), calling `apply expand` OR
`apply auto` next silently **absorbs `P(t)` back into the ∀-hyp** —
CNF's verdict: `P(t)` is a rewrite-to-⊤ image of `∀x. P(x)`, so
it's dropped. Your manual `instantiate` work is gone; `auto` fails;
atomicity rolls state back so the ground fact is restored — but
`auto` was doomed on that turn regardless.

**Root.** Both `expand` and `auto` route through `_BasicTactic` →
`BasicTactics` (`prover/tactic/tactic.go`), which includes
`unifyEqSimplifyTactic` — the pass that recognizes a resident
universal as covering any ground instance and drops the instance.

**Rule.** If you needed the ∀ instantiated for `auto` to close,
**drop the ∀-source before closing**:

```
instantiate hyp_index=k const="t1"
instantiate hyp_index=k const="t2"    # more grounds OK, ∀ still resident
clear hyp_indices=[k]                  # drop the ∀ — nothing to absorb into
apply auto                             # BasicTactic pass has no ∀ target now
```

**Never** `instantiate → auto` while the ∀-hyp is still resident.

**Mirror of Lesson 4.** Both hazards are the ∀-hyp interacting with
the CNF pipeline: Lesson 4 says "the wide ∀ chokes the refuter";
Lesson 12 says "the same ∀ eats your ground before the refuter
sees it." Same underlying cause, same fix family (`clear` before
closing, OR use `Specialize` bare (drops source) instead of
`SpecializeKeep` when you're done with the ∀).

**In chapter Go.** Bare `Specialize(InstHyp(k, ...))` DROPS the
source ∀-hyp; `SpecializeKeep` retains it. Reach for bare
`Specialize` when you're done with the ∀; use `SpecializeKeep` only
when you'll instantiate it again at another witness AND you'll
`ClearHyps` it before the closing `CnfRefute()` / `CloseByAuto()`.

---

## Existence goals need a witness (Lesson 7)

**Pattern.** When the concl is (or strips to) `∃x:T. P(x)`, `auto`
alone almost never closes it. Refutation search doesn't invent the
witness — it only verifies one you supply.

**Playbook** — cheapest first:

**a. Direct witness.** Name a term `t:T` with `P(t)`, then
`witness({"const":"<t>"})` (session) / `Witness(t)` (chapter Go) and
`auto` the residual. `t` can be a subterm in scope, a text-DSL
term, or a Hilbert choice term `εx:T. P(x)` (the DSL parses ε
binders — the canonical witness when `P` pins `x`).

**b. Reduce to `∃!`.** If the corpus has `∃!x. P(x)` (same body,
uniqueness form), `lemma` / `Cite` it; `∃` falls out (∃! ⇒ ∃).
This is how `num_recursion`-style uniqueness rows discharge bare-`∃`
recursion-existence goals.

**c. IFF bridge.** If the corpus has `(∃x. P(x)) ⇔ Q` (often `Q`
is a graph-functionality claim `∀n. ∃!y. R(n,y)`, or an
inductively-defined-relation existence), `lemma` / `Cite` the
bridge and prove `Q`.

**d. Skolem-from-upstream.** If the corpus has a ●-form
Skolemization of the same body, `lemma` / `Cite` it as a hyp; its
Skolem constants are the witnesses, and `auto` closes once both
sides are stripped.

**e. A function assembled from per-point choices.** `∃f. ∀x. R(x,
f(x))` needs no witness when the per-point fact is RESIDENT: a
`∀x̄. ∃y. R(x̄, y)` hypothesis read through the Skolem stage of the
normalization IS `∃f. ∀x̄. R(x̄, f(x̄))`, and a goal that states it is
closed on that identity before a refuter is built — no search, no key
(`by_closer`: "choice function of a hypothesis (no key)";
`prop.SkolemEqBridge`), at any number of arguments, with f's values
sets or functions, read as often as the statement reads it. State the
per-point fact first — `assert` it (session) / `a.Have` (chapter Go) —
and close with a `by` that names it. No choice principle is cited and
no ε-term is spelled. f takes its arguments in the order the fact
binds them, and the goal states what the fact states: a goal that
writes `f(n, I)` under a fact binding `I` before `n`, or adds a
conjunct the fact lacks, is left to the refuter, which reads the goal
NEGATED — f a universal variable there, the points Skolem functions of
it — and has to find f by higher-order unification; that closes the
plain shapes and runs out of budget on a set-valued f of two
arguments. Bind the fact in the goal's order, or state the function's
bare specification first and derive the rest from it.

**Type adaptation seeds from the ∃-binder.** A 1-arg
primitive-recursion lemma `∀f e. ∃fn:num→A. …` adapts to a
higher-arity goal `∃fn:num→num→num. …` automatically — the engine
matches the conclusion's ∃-binder types and instantiates `A :=
num→num` *before* the const-anchor sweep can mispin it. Don't
abandon a structurally-right lemma just because its stored type
prints monomorphic; `lemma` / `Cite` it and try the witness at
the goal's type — the adaptation fires.

**In chapter Go.** ∃-witness at the top of `Sections()` is uncommon
(most members' Tops are ∀-closed) but common inside AssertStep
close paths (an existential intermediate). Same playbook applies.

---

## Collapse the wide-∀ residual at load time (Lesson 10)

**Preventive form of Lesson 4.** Rather than loading a wide `∀x₁.
∀x₂. … ∀xₖ. P(x₁,…,xₖ)` and later `clear`ing it after grounding,
install the pre-grounded instance directly at load time.

**Prover: `lemma { term_specialize: {binder→witness, …} }`.**
Peels outer binders BY NAME at cite time. Collapses `lemma →
instantiate(t1) → … → instantiate(tk) → clear(∀-hyps)` (2k+1
round-trips) into ONE apply. The residual leaf carries the ground
(or partially specialized) instance — no wide ∀-hyp left to
refute-poison `auto`.

```json
# Before (3 calls for one lemma at one witness):
{"tactic":{"type":"lemma","lemma":{"key":"<key>"}}}
{"tactic":{"type":"instantiate","const":"n","hyp_index":<idx>}}
{"tactic":{"type":"clear","hyp_indices":[<old_idx>]}}

# After (1 call):
{"tactic":{"type":"lemma","lemma":{"key":"<key>"},
           "term_specialize":{"x":"n","y":"m","z":"p"}}}
```

Polymorphic binder types work automatically — the witness's
concrete type unifies with the binder type and σ extends to the
rest of the lemma, no companion `type_specialize` needed.

**Chapter Go: `Fact(dep, w1, w2, …)`.** Same mechanic. Peels the
∀-binders in order at cite time (the CiteSpecialize tree — that
spelling survives in engine internals). `Fact` also
takes the dep DIRECTLY — a registry entry var (`Fact(nat_arith.AddSym,
w…)`) — resolving the dep's STATED form itself
(its ∀-closure for a sequent-shaped row — a definition door's
induction principle; a text-stated member is closed), so the file carries
no `ctx.NormalizedThm(ctx.Dep(…))` manifest line; a witness tuple is
typed and ordered by its own terms against the stated binders. Inside
a `By`, a BARE named premise is consumed by the closer alone and so
installs in the closer's clause form (the normalized dep), its stated
form riding as the apply rung's head; a witnessed premise grounds the
stated form and discharges its guards from the context. A guard is
SUPPLIED when the context holds it as written (up to βη, the membership
reading — `u ∈ {p | φ}` and φ[u/p] are one guard, in either direction —, the
record reading — `x ∈ V.carrier` at a packed `V` and `x ∈ hom_set(…)`,
its computed carrier, are one guard — and the numeral reading —
`x ∈ X(2 + 1)` and `x ∈ X(3)` are one guard —, an
equation in either orientation) or, for a conjunction, holds each side that
way —
so a guard `A ∧ B ∧ C` is supplied by one resident fact `A ∧ B ∧ C` and
by three resident facts alike (`guardSuppliedByContext`, the apply
rung's own reading). A guard that reads ⊤ at its numerals — `0 < 2`,
`4 ≠ 0`, `&0 ≤ &1 / &2`, the `1 ≤ 2 + 1` a law at `n + 1` asks at 2 — is
supplied with nothing in the context: it is a value, and no fact states
it. And a guard the context does not hold is
supplied when the context CLOSES it, as a goal of its own, one apply
deep (`closeGoal`, prover/proof/apply_close.go): a conjunction conjunct
by conjunct; a law opened — its binders fixed, its antecedents assumed
— to a conclusion the context closes; a conjunct of a resident
conjunction; or the conclusion of ONE resident fact applied, that
fact's own antecedents held (or a conjunction, or a law opened to
something held — no second apply). So `∀N. a(N) ≤ b(N)` supplies both
`a(c) ≤ b(c)` and `∀n. 0 ≤ n ⇒ a(n) ≤ b(n)` (what `LimitLessEq` asks
read from index 0 on); an injectivity over the whole type supplies the
injectivity on a set; and in a chain of cited laws each one's guard is
supplied by the consequents of the ones before it —
`By(LessEqAdd.At(v, w), LessThanSucIffLessEq.At(v, v + w),
LessEqOfLessThan.At(v, suc(v + w)), …)` discharges the third law's
`v < suc(v + w)` from the first two. Nothing is searched for: every
binder is pinned from the goal and the context before an antecedent is
read, so the parts are independent — each antecedent at the first
hypothesis it meets, and where one meets several (a guard
`subfield(L, M)` with three subfields resident), the other pinnings in
turn, the antecedent meeting the fewest taken first (`M ⊆ N` before
`subfield(L, M)`), four pinnings in all (`pinningBound`), so a law
whose binder only its guards pin closes bare as it closes grounded. What is stated to prove a guard is
stated inside the modus ponens' ¬guard branch, which closes on the
guard and its negation in ONE spelling — the guard carried to the
instance's own by the kernel's βη conversion, never by a closer that
normalizes (an instance at a λ-witness states its guard as a redex, and
a normalizing closer read `∀n. 0 ≤ n ⇒ (λN. i(N))(n) ≤ a(n) ∧ …` and the
same law reduced as clause sets that no longer met) — so the closer's
leaf holds the facts the author named and the consequent, nothing
derived on the way. A consequent the context already holds (the same
law read twice at one point in a `By` — a member's evidence carried by
two cites) leaves no ¬guard branch: the kernel folds it into the
consequent branch, and the guard is discharged into the resident
consequent. Two applies away is the closer's.
This is the reading of a `By` premise and of the apply rung. On the
SPINE — `fact.At(w…)` as a step, `Cite(dep, w…)`, `GroundHyp`, and the
bare install of a fact a verb acts on (`a.Conjuncts(law.Read(fact))`) —
a guard is discharged by assumption alone: as written, or conjunct by
conjunct, each conjunct resident as written or as a conjunct of ONE
resident fact, or reading ⊤ at its numerals, which no fact has to state
(with `a ≤ a` and `a ≤ x ∧ x ≤ b` resident the guard
`a ≤ a ∧ a ≤ x ∧ x ≤ b` is discharged), and a guard the context would
have to prove stays in the fact the step names. The
discharge runs once, at the grounding: a guard assumed AFTER the fact
was grounded (the witness obtained first, its guard assumed second) is
not discharged in retrospect — assume first, or name the guarded
instance with `a.Hyp` where it is consumed. A full tuple whose guards are not all supplied installs the
closer's CLAUSE form instead — which every closer reads, the diagram
chase as the guarded law it spells (§"The diagram chase") — and the `By` failure message names the
guard the context was missing under the premise it belongs to; the
stated form at the tuple still rides as the apply rung's head, its
guards then closed as any antecedent of an apply is, so a guard the
context supplies only through a law named beside it (a ∀-membership
over an `insert(x, s)` that `insert(x, s) ⊆ c`, `set_basic.SubsetDef`
and a closure over c supply) closes a grounded cite on the rung as it
closes the bare one. The
clause form's ∀-prefix is Normalize's, in an order and under names the
author never sees; the tuple is read in the stated order all the same
(witness_order.go): by name where Normalize kept it, and for a renamed
binder by elimination among the statement's unclaimed binders of its
type — the once-bound names, and the SPINE's bindings of a name the
statement binds more than once (`… ∧ (∀x. a < x ∧ x < b ⇒ &0 ≤ f'(x)) ⇒
∀x y. … ⇒ f(x) ≤ f(y)`: the antecedent's x stays existential, the
spine's arrives renamed), each at the reading position of its own
binding site. Bare `Fact(dep)` is the ungrounded cite:
close-if-stronger, else preserving install + obligation close (the
constitution's §"Citation forms" for the full contract and the two marked escapes —
raw `Fact(ctx.Dep(N))`, destructive `UseLemma`).

**Also chapter Go: `CiteInstances(cert, w1, w2, …)`.** DIFFERENT
semantics — takes k separate 1-witness `InstHyp(0, wi)` instances
of the SAME 1-binder lemma (each re-hits the top ∀). Use for
surjectivity-style lemmas applied at multiple representatives; NOT
for peeling a multi-binder lemma at one point (that's
`CiteSpecialize`).

**Auto-grounding of section frees.** When the cited lemma's
∀-binders share NAMES with the section's free variables, `Cite`
may auto-ground them silently — the residual has fewer ∀-binders
than you expected. Verify by checking the next `Specialize`'s
expected witness count against the leaf display, or use
`CiteSpecialize(cert, exactWitnesses...)` which errors cleanly if
the count doesn't match.

---

## Polymorphic constants — twin snapshots + `⟨⟩` disambiguation

The corpus's constants like `card`, `finite`, `set_member`, `image`,
`subset`, `delete` are **polymorphic in one or more type variables**
(`card : ∀α. (α → bool) → num`, `image : ∀α β. (α → β) → set(α) →
set(β)`, etc.). XuGo's Go DSL flattens each occurrence into a
**monomorphic snapshot**: one `ctx.Const("card", …sig…)` call binds
one `*TermWrapper` at one concrete type instance. Go's type system
has no first-class type-var abstraction over term wrappers, so this is
the current representation.

**Consequence for chapter Go, written or emitted.** A proof that
mentions the same polymorphic const at two type instances (`finite(s)`
with `s:setA` and `finite(t)` with `t:setB`) needs **two Const
declarations** — one per instance. Naming the two is style, but you
MUST declare both.

Symptom of missing a twin: parse-time errors like `const "finite": arg
type var:A → bool does not match domain var:B → bool` when the
section text mentions the un-declared instance.

**The error names the CONSUMER, not the culprit.** It is raised where
the mis-instantiated term is used as an argument, so the const it
names is the one that took the argument — not the one that needed the
annotation. `identity_map ∘ f = f ∧ f ∘ identity_map = f` at `f : A → B` reports `const "o":
arg type (var:A → var:B) does not match domain (var:A → var:A)`, and
`o` is fine; it is `identity_map`, bound once at `A → A`, that has to be
written `identity_map⟨A:B⟩` in its left-composition occurrence. When the named const's own
declaration looks right, read the reported DOMAIN as a description of
some other head in the same application and annotate that one.

**⟨⟩ annotations in section text** — the second half of the pattern.
Text like `finite⟨A:var:A⟩(s)` says: "look up finite in scope, then
instantiate its type-parameter `A` to `var:A` before building the
Applied term." The annotations exist because the DSL's polymorphic
resolver (`buildAppViaMeta` in `ext/dsl/build.go`) works by matching
arg types against the meta's abstract signature — the annotation
pre-pins the type-var explicitly, which matters when:

- The head is used **bare** (no args), so arg types can't drive
  matching: `∀_32093:(var:B → bool). …` needs `finite⟨A:var:B⟩` if
  the body uses `finite(_32093)`.
- The head has **multiple free type-vars** and the first arg only
  pins some of them (`image(f, s)`: `f: A→B` pins both A and B, so no
  annotation needed; but if you write `∀x. x ∈ image(f, s)`, the `x`
  binder wants the annotation).
- Emit determinism: emit always writes annotations so re-rendering the
  same proof produces byte-identical text.

The annotation name (`A` / `?83148`) mirrors the meta's abstract-type
type-var identifier — the same one printed inside `MakeVarType("…")`
when you declare the const. For most consts it's the human-name `A`
(e.g. finite, image, set_member, subset); for a handful — card is the notable
one — the kernel assigned a synthetic name (`?83148`) at definition
time. You don't memorize these; read them off `emit-section`'s
declarations:

```
card := ctx.Const("card", MakeFun(MakeFun(MakeVarType("A"), TypeBool), NumType))
card_2 := ctx.Const("card", MakeFun(MakeFun(MakeVarType("B"), TypeBool), NumType))
card_3 := ctx.Const("card", MakeFun(MakeFun(MakeVarType("?83488"), TypeBool), NumType))
```

The `A`/`B`/`?83488` inside `MakeVarType` is the substitution key —
same string appears inside `card⟨?83148:…⟩`. `?83148` vs `?83488`
(a different card instance) just means the kernel assigned two
different type-var names at two different registration sites — the
emitted declaration is authoritative.

**Twin count**. Enumerate the goal's type variables (`var:A`,
`var:B`, …) and per polymorphic const consumed in the proof
(including inside cited deps' statements!), declare one Const per
type-instance the proof actually uses.

In a chapter the declarations that only exist so a STATEMENT parses
belong to the family vocabulary (the `registry.NewVocabSpec` rows in
vocab.go), not to the member — a `family.Theorem` member has no
pre-section body to declare them in, because its statement parses
before its closure runs. **Reference example**:
`cardinality.SurjectiveIffInjectiveGen`
(`library/proofs/sets/cardinality/maps.go`, a typed-surface
family — the statement's polymorphism rides the family vocabulary).

**Ergonomic escape** — `Script.PolyConst(name, domTypes... , codomain)`
(prover/proof/script.go). One declaration collapses the twin-`Const` pattern
by carrying the abstract signature as first-class values. The
abstract-type args are variadic (same convention as `core.MakeFun`) —
domains + codomain flat, right-associated into a curried function
type internally. Multi-typevar consts (`image: (α → β) → set(α) →
set(β)`) just put more `MakeVarType` placeholders in the same
signature — the arg-vs-abs-domain matching accumulates substitutions
across all binder positions in one pass:

```go
tyA, tyB := MakeVarType("A"), MakeVarType("B")

// One typevar:
card := ctx.PolyConst("card",
    MakeFun(tyA, TypeBool), NumType)                                    // (α → bool) → num
finite := ctx.PolyConst("finite",
    MakeFun(tyA, TypeBool), TypeBool)                                   // (α → bool) → bool
member := ctx.PolyConst("set_member",
    tyA, MakeFun(tyA, TypeBool), TypeBool)                              // α → (α → bool) → bool

// Two typevars — same API, more placeholders:
image := ctx.PolyConst("image",
    MakeFun(tyA, tyB), MakeFun(tyA, TypeBool), MakeFun(tyB, TypeBool))  // (α → β) → set(α) → set(β)

// Apply auto-picks the monomorphic instance from arg types + caches:
card.Apply(s_of_typeA)   // card@A
card.Apply(t_of_typeB)   // card@B — same wrapper, different instance
image.Apply(f, s)        // (α := var:A, β := var:B) pinned from f's type in one Match
```

The `Apply` path runs the same abs-domain-vs-arg-type unification as
the DSL parser (`buildAppViaMeta` in `ext/dsl/build.go`). The meta is
registered in `ParseScope.ConstMetas` upfront, which lets **section
text drop `⟨⟩` annotations entirely for the applied case** —
`finite(s) ∧ finite(t) ∧ card(s) = card(t)` parses cleanly with a
single `finite`, `card` declaration and no `⟨A:var:A⟩` on the
call sites (the parser's polymorphic path infers from arg types).

`⟨⟩` annotations remain necessary only for:
- **Bare-head references** (a polymorphic const appearing as a
  0-arg atom, e.g. inside `∀_var:(var:B → bool). …finite⟨A:var:B⟩(_var)…`
  where the outer binder's type isn't visible to the applied path).
- **Multi-free-typevar heads with under-constrained args**
  (rare; if the first arg pins all free type-vars, no annotation is
  needed).
- **Emit-generated code**, which always writes annotations for
  round-trip determinism regardless of necessity.

Prefer `PolyConst` in new proofs for any const used at 2+
type instances — in a typed-surface family the vocab layer plays this
role, and the live PolyConst user is the set domain's shared alphabet
(`proofs/sets/internal/setvocab/setvocab.go`, `empty_set` and
`universe`): one PolyConst declaration replaces the twin `Const` calls,
one per type instance, and the `⟨⟩` annotations that tell them apart.

---

## Text-DSL discipline — the type-var scope trap

The text-DSL parses proposition and term strings passed to
`assert`, `lemma { text }`, `witness`, `instantiate`, `trans`,
`case_split` — and, in chapter Go, to `MakePropText`. Full syntax spec
at §Text format above. Beyond the syntax, four disciplines that
repeatedly bite:

1. **Type annotations MANDATORY on every binder** — `∀x:A. …`,
   `∀s:set(A). …`, `∀P:(A → bool). …`, `λv:prod(A,B). …`. Bare `∀x. …` fails or
   resolves to an unintended type. The parser doesn't infer binder
   types from the body.

2. **Single-binder form only** — `∀a:A. ∀s:set(A). …`, NOT `∀a
   s. …`. Each ∀ binds one variable.

3. **Fresh capitalized `A`/`B`/`C` type vars in text do NOT unify
   with goal-side pinned `var:A`/`var:B`/`var:C`.** THE trap. A
   goal has `s:(var:A → bool)` from the session's type context. A
   `MakePropText("∀x:A. P(x)", …)` creates a fresh type var also
   displayed as "A" — but internally it's a different type. The
   subsequent unification (against a cert bound at that fresh A,
   or against a goal-side hyp) fails silently or with a cryptic
   type-mismatch. **Fix**: use `subterm-lookup` (load a `lemma`
   that pins the type instance into scope, then parse text against
   that context) or `type_specialize` with explicit type mapping.

   In chapter Go: passing a B-typed `exact` prop
   to `TypeInstSourceExact(A-cert, exact)` fails with "does not
   normalize-coincide" — same root cause. Match the exact's
   type-vars to the cert's native type-vars.

4. **Pair literal is comma-first** — `,(a, b)`, NOT `(a, b)`. Bare
   `(a, b)` parses as a parenthesized expression with a spurious
   comma. Applies wherever a pair term appears in text (`witness`,
   `trans`, etc).

**Preview before you apply.** For any non-trivial text — paired
lambdas / pattern_abstraction, prod-type binders, session-Skolem frees, chapter
consts — use `parse-prop` or `parse-term` BEFORE
`assert`/`lemma`/`witness`/`instantiate`. Iterating parse errors
this way is ~1000× cheaper than iterating apply errors (you see
the actual parse failure, not a parse+apply composite). Chapter Go
has no parse preview of its own — use a session-level
`parse-prop` against the same const context if the DSL string is
complex.

---

## Post-tactic hyp-index renumbering

**Pattern.** Hyp indices are positional into a goal's
*canonically-sorted* hyp list. Any hyp-adding tactic —
`instantiate`, `assert`, `congr_arg`, `congr_fun`, `lemma`,
`cite-node`, and their chapter-Go analogs — **re-sorts the list and
renumbers it**. An index you read from an `inspect` BEFORE the
apply is then stale.

**Rule (session).** After a hyp-adding apply, read fresh indices
from EITHER:

- the apply response's `new_hyps` field (`[{goal_id, index,
  term}, …]` — post-apply positions of each newly-added hyp), OR
- the apply response's `state.goals[i].hypotheses` field
  (`[{index, term}, …]` — full post-apply hyp list of each
  goal), OR
- a fresh `inspect` (costs an extra round-trip; prefer the two
  above).

Do NOT chain several `instantiate`s against one pre-apply
`inspect`'s indices — the chain drifts and lands on the wrong
∀-hyp.

**Rule (chapter Go).** Chapter Go proofs have no runtime inspect.
Every `Cite`, `AssertStep`, `LemmaPreserve`, `TypeInst`,
`SpecializeKeep` shifts indices in ways the Go author cannot
observe without a `go test` round. Two mitigations:

1. **Prefer atomic composites** — `Fact(dep, w1, …)`
   bundles Cite + Specialize as one atomic move, so there's no
   intermediate index to track.
2. **Session-validate BEFORE writing Go.** Add the planned leaf
   into a session, execute the same tactic sequence,
   verify the indices at each step from the session's `inspect`.
   Transcribe INDICES to Go with confidence.

**Symptom of drift.** "Specialize hyp N at [...] failed" panic —
the hyp at N isn't ∀-headed or has the wrong binder count for
the witness list. Almost always an index that shifted since the
preceding Cite / LemmaPreserve.

---

## An ⇔ law with a quantified side — cite it

**Pattern.** A law `A ⇔ ∀x. P(x) ⇒ ∃δ. …` — an atom on one side, a
law on the other: `real_topology.OpenIff` (`u ∈ real_topology ⇔ ∀x.
x ∈ u ⇒ ∃δ. …`), `ClosedIff`, `ClosedIffSequential`,
`topological_space.OpenInSubtopology`.

**Rule.** Cite it, bare or at its witnesses, beside the facts that
supply the other side: the apply rung closes the leaf with no key.

    d, radius := b.ObtainAs[Real]("some radius δ around sup(t) stays in v",
        "∃δ:real. &0 < δ ∧ ∀y:real. real_abs(y - sup(t)) < δ ⇒ y ∈ v",
        By(vOpen, mInV, OpenIff.At(v)))

The rung reads the ⇔ as its two Horn clauses and, where a side is
itself a law, THROUGH that side to its conclusion: the goal is the
radius at a point, `vOpen` supplies the atom side and `mInV` the
side's own antecedent. The side whole (`∀x. x ∈ v ⇒ ∃δ. …` as the
claim, `By(vOpen, OpenIff)`) and the atom side from the quantified one
resident close the same way. A failing close names what the context
lacks: "the other side … is not in the context", or the side's
antecedent.

Each of the four spellings of one site — the radius at a point, bare
and at `.At(v)`, and the whole side, bare and at `.At(v)` — closes on
the rung, keyless.

**A law whose right side holds its left is not a rewrite.** Read at a
topology `T`, `topological_space.OpenPointwise` is `u ∈ T ⇔ ∀x. x ∈ u ⇒
∃v. v ∈ T ∧ …`: unconditional, with an instance of its left side under
`∃v`. It would rewrite its own output without end, so a simp set
refuses it when the set is built, and `Simp(Fwd(OpenPointwise.Read(h)))`
fails naming it, "Refused as a rewrite". The check also reads nested
binder bodies as the fixpoint walk does: folding
`φ(m, n) = k` into `(m, n) ∈ {p | φ(fst(p), snd(p)) = k}` is
self-embedding below the pair binder, even though its type differs from
the rule's two numeric parameters. Two spellings work. The other
side stated and closed as above, `By(neighbourhoods,
OpenPointwise.Read(h))`. Or the law cited bare, `Simp(Fwd(OpenPointwise))`
with `is_topology(T)` resident: a conditional rule fires at
binder-closed positions only, once here. A polymorphic rule's adapted
copies meet the same refusal at the instances where their right side
holds their left (`set_image.SimpleImageGen` at `f:(τ → τ)`, where
`{x | P(x)}` is the left side at the identity); only a rule refused
where its left side matches is named, so "no rule fired" alone still
means no match.

**A rule set that feeds itself is cut.** The refusal above reads one
rule against its own output. Two rules can feed each other with neither
holding its own left side: `f(x) = g(x)` beside `g(x) = h(f(x))` restores
`f(x)` under one more `h` at every pass. The divergence whistle ends
such a rewrite at the first firing it judges divergent, and the step
fails with nothing rewritten: `Simp`, `SimpAt` and `SimpAll` panic "the
rule set was cut as divergent", `simp_with`, `simp` and `simp_all` return
the same words and leave the session unchanged, and each adds the
firing the cut fell at and its budget. What a cut rewrite leaves is no
normal form, so no part of it is kept, and no further round runs. Leave
out the rule that restores another rule's left side, or state the result
and close it with `By` citing the rules. The whistle over-approximates
divergence, so a rewrite that would end can be cut too: an ordered AC
sort over eight or more variable atoms is the known case, and no stored
proof meets one. It is refused in the same words; rewrite in two steps,
or state the result.

The members written before it state the side as a Have and rewrite
the GOAL back — `Simp(Rev(OpenIff)), By(vOpen)`, then ground the Have
at the point. That stays keyless and correct; a polymorphic law used
as a `Simp` rule adapts to the goal's concrete type, as a `By` premise
does, and the corpus's `.Inst[Real]()` pins on such rules are explicit
instances that still fire.

**A side that is a conjunction is read through each conjunct that is
a law.** Where the law is one conjunct of the quantified side —
`metric_space.OpenIff`, `u ∈ metric_topology(M, d) ⇔ u ⊆ M ∧ ∀x. x ∈ u
⇒ ∃r. …` — the rung eliminates the ⇔ toward the side, splits the
resident side until that conjunct is resident, and applies it:
`By(uOpen, xInU, OpenIff)` closes the radius at a point keyless, at the
chapter's own type letter as at another (metric_space.ContinuousMapIff
at its second space, MetricTopologySubspace at its own). The reading
at a law's OWN letter is the identity type instance, which the rung
admits for a Horn law with one atom as antecedent and for an ⇔; a law
of another shape at its own letter still meets the closers.

## An equation between functions — rewrite with it, do not hand it to a closer

**Pattern.** A step that carries an equation between SETS (or vectors,
or sequences — any two terms of a function type) into a place where
one side stands as an argument: `u ∈ T ∧ v ∈ T ⊢ {u, v} ⊆ T` (a member
of the pair EQUALS u or v), `w ∈ F`, `w = u ∩ s ⊢ u ∩ s ∈ F`, a vector
`P(i) = vec_zero` under `dot`.

**What the closers do with it.** Normalize reads an equation between
functions pointwise (`x = v` becomes `∀ẋ. x(ẋ) ⇔ v(ẋ)`), and a
pointwise fact says nothing about `T(x)`, where `x` is an argument.
On a session `by` at the stripped leaf:

| the equation stands | sets (`A → bool`) | other function types (`num → A`) |
|---|---|---|
| as a fact of its own (`w = u ∩ s`, either way round, any spelling) | `By` closes: the refuter recovers the equation from its two pointwise clauses. `BySets` does NOT, and spends its whole budget failing | `By` closes: the pointwise clause rewrites the argument (`P(u)`, `u = v` ⊢ `P(v)`, in a millisecond), a side that keeps a λ included (`f = λx. h(x, c)` ⊢ `K(f) = K(λx. h(x, c))`) |
| inside a disjunction (`x = u ∨ x = v`) | fails, `By` and `BySets` | fails |
| under a guard or an ∃ (`∀w. w ∈ F ⇒ ∃u. u ∈ T ∧ w = u ∩ s`) | `By` closes: the guard's literals ride into both pointwise clauses and the refuter recovers the equation under them (the ∃ as a Skolem function). `BySets` does NOT | `By` closes: once the guard is discharged — resolved away, or split off when the guard is ground — the pointwise equation rewrites the argument |
| — the same three at an ELEMENT type | close, in milliseconds | |

What separates the rows is the TYPE of the two sides and nothing in
the mathematics, so it cannot be predicted from the statement: read the
rule.

**Rule.** An equation between functions is applied by REWRITING, or
by a law that states the consequence:

- a resident equation: `fact.Rw()` (or `Simp(Fwd(<law>))` for a law),
  then close what is left — `classIsCoset.Rw(), By(LeftCosetSize, …)`;
- a set identity first, the abstract law after: state the identity as
  a Have by `BySets`, rewrite the GOAL by it, cite the law at the
  instance (real_topology.OpenIntervalOpen);
- an enumerated family: the algebra of insert —
  `Simp(Fwd(set_order.InsertSubset.Inst[Set[A]]()), Fwd(set_order.EmptySubset.Inst[Set[A]]())), By(open)`
  for `{u, v} ⊆ T` (topological_space.UnionOpen);
- a family defined through an equation: name it by a condition read
  pointwise (`{u | u ∈ T ∧ u ∩ s ⊆ ⋃F}` for `{u | u ∈ T ∧ u ∩ s ∈ F}`),
  or cite the membership law ground, which the closer reads as an atom
  (`set_basic.InImage.At(cut, T, ⋃F)`).

A standalone equation between functions, sets included, may be left
to `By` — never to `BySets`, whose driver reads every equation
pointwise before it closes.

**A cited law's set guards are `BySets`'s to discharge.** A law whose
antecedents are inclusions and disjointnesses of the instance's own
sets beside one fact of another kind — a semigraphoid law, `X ⊆ V ∧
W ⊆ V ∧ X ∩ W = ∅ ∧ … ∧ R(X, Y ∪ W, Z) ⇒ R(X, Y, Z)`; a rule of a
derivation relation guarded by `X ⊆ O ∧ X ∩ Y = ∅ ∧ …` — is cited at
its witnesses in a `BySets` over the base facts: the driver reads each
guard pointwise and derives it from the inclusions and disjointnesses
it was handed, so no Have restates the guards at the instance. `By`
over the same premises does not close: the refuter meets
`X ∩ (Y ∖ W) = ∅` as an atom and the apply rung finds the guard in no
hypothesis. What the driver will not do is the row above: it does not
carry `R(X, Y, Z)` to `R(X, W ∪ (Y ∖ W), Z)` through `W ∪ (Y ∖ W) = Y`.
So the law's other antecedent stands in the context AS THE LAW SPELLS
IT, a set equation moved first by a Have of its own that `By` closes,
and a conclusion the law spells differently from the claim is carried
back the same way:

```go
moved := a.Have("read Y as W with its complement", "R(X, W ∪ (Y ∖ W), Z)", By(separated, split))
a.Show("decompose to W",
    BySets(decompose.At(X, W, rest, Z), moved, inX, inY, inZ, apartXY, apartXZ, apartYZ, subset))
```

**A set the proof reasons ABOUT is named.** A set whose supremum,
membership or emptiness the argument is about — `sup({x | …})`,
`a ∈ {x | a ≤ x ∧ x ≤ b ∧ ∃d. d ⊆ c ∧ finite(d) ∧ {y | a ≤ y ∧ y ≤ x} ⊆ ⋃d}`
— gets a name, by `a.Let` or as an obtained variable, and its
membership iff as one Have (`∀x. x ∈ S ⇔ …`, a bare `BySets`); each
use then cites the iff at its point, `By(Normalized, iff.At(t), …)`.
Left as a literal comprehension inside another construct it is opened
wherever it stands — the inner `⊆` pointwise, under the `∃` — and a
membership the named set closes in milliseconds spends the budget and
misses. The driver reads inside a comprehension on purpose: with a
comprehension that stands as an object kept atomic, members of the
corpus that close today stop closing, while the shape above fails as
before — so the naming is the author's, and no change
of the driver is pending.

**The tidy after an unfolding applies no resident fact.** The
simplification that follows `def_expand` / `Unfold` β-reduces the
opened sequent, simplifies its connectives, splits a resident
conjunction and closes a leaf whose conclusion a hypothesis states as
a whole — and reads no resident fact into the goal: not an equation
(at any type, ⇔ included), and not a fact as the rewrite `P ↦ ⊤`. After
`def_expand matrix_mul` the hypothesis `transpose(Q, j) = vec_zero(zero)`
has substituted nothing and the opened goal still spells
`transpose(Q, j)`; an unfolded `comm_ring_on(T)` whose nine clauses
are resident stays open as the conjunction. The close and the rewrite
are the author's lines — `fact.Rw()` (`RwRev()` for the other
direction) on the goal, `a.Simplified(h, Fwd(fact))` on a hypothesis,
`By(Normalized, clause₁, …)` or `Basic()` for the opened conjunction —
so the proof says which facts it leans on (the constitution's premise
discipline), and a later rewrite that finds nothing names the step
that substituted it.
The simplification inside `Basic` and after `lean_rw` keeps the older
rule — a resident equation applied from its LARGER side to its
smaller, only where the result comes out strictly smaller, a bare
variable against a numeral always variable → numeral — which is why a
`By(Normalized, …)` still reads an equation an `Unfold` left alone. A
result no smaller is taken in one case: it closes the leaf — the
conclusion rewritten into a hypothesis or its symmetric, a hypothesis
rewritten into the conclusion or its symmetric — so an equation between
two sides of one size, which the size rule would read in neither
direction, still brings two spellings of one value together
(prover/tactic, settlesAgainstContext).

## A slow `By` is its premises, not the refuter

**Pattern.** A member replays in seconds where its neighbours take
milliseconds, and the time sits in one `By` — or in the `Have` or
`Obtain` it proves. The recorder's dry run
(`XUGO_RECORD_FAMILY_CNF=<family>.<Name> XUGO_RECORD_CNF_DRY_RUN=1`)
lists the leaves that reach the refuter, and the slow step is usually
not among them: its seconds go to normalizing the premises before any
refutation — the canonical binder labeling, the pre-CNF rewrites —
on parallel goroutines, so its CPU is several times its wall.

**Two shapes cause nearly all of it.**

- *A law, definition or clause pack cited bare with many binders or
  type letters.* `By(…, RingHomomorphism)` hands the closer a
  fifteen-binder body to normalize and an instance to search for; so
  do `By(…, FractionClassEq)`, `By(…, GermEq.Read(pre))` and
  `By(…, SupportClauses)`. Ground it at the step's own terms:
  `Law.At(w…)`; `Law.Read(inst).At(w…)`, or `.AsFact().At(w…)` when
  the typed reading wants carrier members the step does not hold as
  facts; `At(Structure, w…)` for a structure; `Pack.At[T…](w)` for a
  clause pack. A definition that heads the goal is opened by
  `Unfold(<the definition>)` before the `By`, one that heads a
  hypothesis by `a.Unfolded(fact, <the definition>)`; when the unfolded
  goal is ONE fact already resident, the `Unfold` closes it alone, and a
  conjunction of resident facts stays open for the `By` or `Basic()`
  that follows. `Unfold` rewrites the
  resident hypotheses too, so a `By` that reads a law at a hypothesis
  the same definition heads (`Source.Read(hom)` under a
  `ring_homomorphism` goal) finds no handle to read at: open the goal
  alone by `Simp(Fwd(<the definition's entry>))` there.
- *A `By` whose premise already is the goal*, once grounded or after a
  rewrite: `By(h.At(w), g₁, g₂)` with the guards resident, `By(eq,
  fact)` where rewriting the goal by `eq` leaves `fact`. The closer
  pays a full normalization to find an assumption. Spell the grounding
  and the close: `h.At(w), Assumption()` for a resident ∀-fact,
  `Cite(law, w…)` for a named law, `eq.Rw(), Assumption()` — with
  `Symm()` before the `Assumption()` when the fact runs the other way.

**Where the second shape stops.** The spine discharges a guard by
assumption alone (§"Collapse the wide-∀ residual at load time"): as
written, conjunct by conjunct, never a conjunct of a resident
conjunction; a guard it does not find leaves the claim open. A rewrite
can η-contract the goal — `λy. (p, y)` becomes `,(p)` — and the
instance a `Cite` installs, still spelled with the λ, is then not the
goal to an α-match. In those places keep the `By`, after the rewrite,
with the premises it still needs: the normalizer reads through both.
A witnessed `Cite` that the bare form already closes is refused
("witnesses are unused").

**What moves.** Neither reshape changes a statement, and a step that
never reached the refuter leaves the family's blob as it was: the
family GC reports no write. A member stands on a definition it opens
as on one it cites (`member_unfolds` beside `member_deps`), so trading
a bare definition cite for an `Unfold` moves the entry from the one
row to the other and keeps the edge. Measured, member alone:
CompactBounded, whose compactness step was `By(subcover.At(cover),
open, covers)`, went from 17 CPU-seconds to half of one as
`subcover.At(cover), Assumption()`; IsomorphismInverse, its bare
`RingHomomorphism` opening the goal by `Simp(Fwd(RingHomomorphism))`
instead, from 14 to about 1. Check the two shapes before suspecting
the engine.

# Design rules

What the engine commits to, stated once. The labels below are this
part's own; the code states a rule in place where it needs one, and
cites two by label because it needs them often — R4, installation,
and S4, the grounding stage — each time as the manual's.

## Statements and definitions — one elaborator

One elaboration layer stands between surface text and the kernel, and
it has two halves: checking a statement, and synthesizing a
definition. They are one design because of one invariant: **a fresh
name enters the system only through a definition move.** The checking
half forbids the accident; the `define` door is the synthesis half.

- **E1 — strict modes.** *Strict resolution*: an identifier the scope
  does not bind and the statement does not quantify is an ERROR, never
  a fresh constant — the undeclared free variable, and the
  constant-looking name that would resolve to a definition-less meta
  at a fresh type variable. *Strict mint*: every type variable of a
  minted statement is ANCHORED — spelled by the author through a
  binder's or a variable's type, or a `⟨⟩` tie — never inherited from
  a bare head's own letters. (Statement registration does not run the
  mint check: type letters are legitimate there, the dimension genre.)
  The statement doors are strict together — the session never accepts
  a text that registration refuses. Every rejection names its repair:
  the tie to add, the near-miss declarations in scope. Half the
  readers of an error are agents, for whom its text is the repair
  prompt.
- **E2 — one elaborator, two surfaces.** Statement elaboration —
  typed, scope-directed, with a per-domain coercion policy — is
  implemented once and read by both the session (`add-goal`, `lemma`,
  `by` text) and the Go registration path (`family.Theorem` texts,
  `a.Have` claims), so a session-validated text and a registered text
  cannot differ in meaning. A known integer position embeds natural values;
  an explicit `&` reads its target from the position or the scope's declared
  ambient domain (`CoerceDomain`). An operand type the author spelled wins;
  an unanchored `&` with no declaration is an error naming the repairs.
  Elaboration, printing and signatures are one triple: the print of every
  registered statement parses back to it (a standing gate), two distinct
  constants never print identically, and the typed wrapper a chapter
  cites through is rendered from the registered statement.
- **E3 — delivery.** A bad statement literal fails at registration,
  on the first test run; a wrong citation is a compile error, and a
  wrong type instance panics naming the statement's own letters.
- **E4 — definition packages.** Every definition is a variant of the
  one `define` command — `recursive:`, `data:`, `spec:`, `typedef:`,
  `inductive:`, `quotient:`, one per kernel principle or package that
  earned its place. Each records as ONE composite step, and
  `emit-section` renders it 1:1 as the chapter's `family.Define…`.
  `recursive:` dispatches on the equations' recursion pattern to any
  registered recursor; `data:` registers its induction theorem for
  typed dispatch; a minted type ships its Go-side phantom. Nothing is
  granted: a recursor, an induction principle, the facts a quotient
  comes with are derived by kernel rules like any theorem.
- **E5 — non-goals.** No definitional equality: a definition is
  unfolded by a theorem, explicitly (`Unfold(<the definition>)`), and nothing is
  proved by computation. No term-indexed type families: the ceiling
  of simple type theory, accepted. The session's language and Go's
  are not merged. (A numeral is no exception: the apply rung's numeral
  reading and the arithmetic closer evaluate `2 + 1` by the corpus's own
  theorems about numerals, through the kernel, under the proof's
  arithmetic policy and on its record — a derived rule, not a
  conversion the kernel grants.)

The rules a definition move keeps:

- **R1 — only ceremony is automated.** Every obligation with
  mathematical content stays the author's proof.
- **R2 — strictness pays for itself.** The strict modes ride inside
  the moves; strictness that adds an annotation is paid for by
  inference that removes more.
- **R3 — binders stay explicit.** No automatic ∀; terseness comes
  from type and coercion inference, never from eliding a binder.
- **R4 — a definition is installed, not just minted.** Every `define`
  registers its characterizing equations as simp rules, derived from
  the SHAPE it was served through (`proof.DefinitionSimpRules`), for
  the session that made it and for a chapter that imports it alike.
- **R5 — the session is the writing surface; Go is the output
  format.** A session's exit is `emit-section`, and what it emits is
  landable as it stands.
- **R6 — fluency is equation compilation plus simp discipline**, the
  class of Isabelle's function package, not definitional unfolding.

## The conditioning stage of `by`

The closers are sensitive to the syntactic form of their input: the
same goal with the same facts moves between a timeout and a close in
milliseconds on the spelling of a premise alone. The moves that
bridge it — strip, split, ground, denote — are run by the `by`
executor between premise install and terminal close: the author names
the mathematical facts, the executor puts them in the form the closer
digests. Two boundaries hold it. **No new search power**: a goal
whose named premises are insufficient stays open, and conditioning
only transforms what the author named. **No lost search power**: a
goal that closes on its bare spelling still closes. No budget moves.

- **G1 — no new trust.** Every stage is a transformation the step
  vocabulary already expresses, run through the same kernel paths;
  close-or-fail.
- **G2 — determinism.** The stage is a pure function of (goal,
  premises, closer): fixed traversal orders, work budgets rather than
  wall clock. One code path runs in the session and in the recorder.
- **G3 — the author's hand wins.** An explicit shape or a ground cite
  suppresses the automatic stage for that premise; `Raw`
  (`by_shape:{raw:true}`) turns the stage off for one call.
- **G4 — what is recorded replays untouched.** The bare form's key is
  tried first (the ladder below), so no recorded certificate goes
  stale when a stage changes.
- **G5 — diagnostics name what was tried.** A conditioned close that
  fails lists the stage's actions — splits, witnesses, denoted terms.
- **G6 — acceptance is the battery**
  (`engine/by_conditioning_battery_test.go`), not judgment.
- **G7 — no stage consumes or reclassifies a premise.** `By` does not
  rewrite with an equation premise of its own accord, and does not
  substitute a cheaper closer for the one spelled; what would close
  cheaper is reported as a finding and never applied. A premise
  reaches the closer as the fact the author named, or not at all.

The stages, in execution order. The numbers are the labels the code
uses; two are retired.

| Stage | What it does | For which closers |
|---|---|---|
| S1 | a premise whose matrix is a conjunction is installed as its conjuncts | `set_tac`, arith |
| S2 | the residual goal's ∀-binders are fixed, its antecedents moved into the hypotheses, a conjunctive goal split into its conjuncts, each a leaf of its own from there on, and every membership in a set-builder the leaf spells — in the goal or a hypothesis — read as its condition at the point, `x ∈ {p | φ}` as φ[x/p] and the three-part `t ∈ {f(k) | k | φ}` as `∃k. φ ∧ t = f(k)`, and a membership in a constant declared to read its membership (`registry.DefEntry.MembershipRead`) as the set-builder its definition is — `x ∈ ⟦a, b⟧` as `a ≤ x ∧ x ≤ b`, `i ∈ m .. n` as `m ≤ i ∧ i ≤ n` — through the kernel's bridge (the apply rung's reading, SA): the refuter unfolds no definition, so a membership it met unread was an opaque atom — `x ∈ {i | i < n}` beside `x < n` did not meet, and a membership whose condition the context contradicts ran to the ceiling. With it, for the refuter, the arithmetic closer and `set_tac`, every record projection of a packed value the leaf spells — in the goal or a hypothesis — is read as the part (S5's form; the rung's `RecordRead` step run on the leaf), the two readings taken until neither changes the leaf, since a part may spell a set-builder and a read condition a projection: these closers compare terms as written, and unread a resident `x ∈ V.carrier` at a packed `V` and a cited instance's `x ∈ hom_set(…)` were two atoms to each of them, so a claim spelled `{P} ⊆ polynomial_algebra_ring(R, S).carrier` did not meet `P ∈ polynomial_algebra(R, S)`. The readings run after SA and S4, which match the leaf as spelled — a law's guard `x ∈ M.carrier` finds its `M` in the hypothesis the author wrote | every closer but word arithmetic |
| SA | the apply rung — `apply h; assumption` over the leaf's context and the named premises' STATED forms: binders pinned from the goal and the context, antecedents closed one apply deep, the instantiation dry-run through the kernel before it is committed; the goal, the context and the head's pieces compared in the rung's reading (`x ∈ {p | φ}` as φ[x/p]; a record projection of a packed value as the part; a statement at its numerals — a term with no variable built from natural-number literals by `+`, `−`, `·` and `suc` as its value, `2 + 1` as `3`, likewise a sum or a product of `&` literals in ℝ and ℤ, and a comparison with no variable, its sides built from literals by `+`, `−`, `·` and ℝ's `/`, as ⊤ or ⊥, the constant folded out of what holds it, `0 < 2 ∧ A` as `A`; nothing that names a variable is read, `0 ≤ n` and `n + 1 + 1` among them, and no factorial, power, quotient of naturals, root or absolute value, which are the arithmetic closer's; the numerals are evaluated by that closer's theorems, so the reading runs under the proof's arithmetic policy, is off in a proof those theorems rest on, and a reading that fired is recorded as a use of them) — the match as spelled first, then in that form — and the leaf read through the kernel (its memberships, its record projections, its numerals) before it closes by assumption; a goal that reads ⊤ at its numerals is closed by that reading, and so is a leaf one of whose hypotheses reads ⊥. The numeral reading is the rung's alone: the leaf a closer is handed is not rewritten by it, since the refuter does not compute and a numeral fact its author listed (`3 ≠ 0`) is a fact it uses once its own substitution has made the comparison. Keyless and deterministic; run first on a goal the context already holds, as written or in that reading, before S2 strips it — a goal naming a predicate applied, `∀E. fin(E) ⇒ «Motive»(E)` beside the law spelled with the motive's body, is that law up to β, and stripped it is a redex no law matches — else once S1 and S2 have exposed the goal, and again after S4 | the refuter, `set_tac` |
| S4 | grounding — a wide ∀-premise is instantiated at the ground terms the leaf already spells (e-matching). The stage has two leaves it can hand a closer. The WHOLE leaf holds the instances beside every premise. The PRUNED leaf has each premise every binder of which a match pins replaced by its instances — unless the plan is a GUESS: its witnesses came from matching the premise's CONCLUSION alone, and the instance has an antecedent the leaf does not hold (as written or conjunct by conjunct, the apply rung's reading). The leaf always spells the conclusion such a match lands on, so the match says nothing about which instance the close wants, and the premise stays on both leaves — `∀d. d ∈ s ⇒ disjoint(x, d)` at `disjoint(x, ⋃s)` grounds at d := ⋃s and is kept, so the set driver reaches it at the Skolem point of `a ∈ ⋃s`. Neither leaf is the safe one. Pruned, a close loses the premise at a point the stage could not ground it at: a witness the refutation makes, a term another instance produces — `∀y. P(y) ⇒ y = z` beside `P(z)` grounds at z, and a goal `∃!x. P(x)` wants it at the two witnesses of its refutation. Whole, the search can be lost among the wide forms, and a simplifier discards an instance that stands beside the premise it came from. Which a close needs is known only once a search has run, so a `by` is run on the whole leaf, which loses no premise, and where that fails on the pruned one ("The ladder around the stage"). The one stage that searches; its output is recorded as plans | the refuter, `set_tac` |
| S5 | the record reading at the refuter's own instantiations — for every projection the leaf applies to a bound variable, or to a name a hypothesis equates with a record value (a Let's: `Zn = free_module_record(R, S)` beside `Zn.add`), and every record value of that variable's type the leaf spells (a constructor or a definition a projection reads through, applied in full, ground in the leaf), the part equation `p(v) = part` is installed as a hypothesis, and the ones the close used are read through the record equations as the proof's cites; a clause with a variable of a record type is instantiated at such a value inside the search, and the projection of the value it then spells is a redex only these equations reduce (`RecordParts`; prover/tactic `RecordPartsTactic`). The equations join the leaf with the premises, so every rung of the ladder closes with them in hand, and again on the conditioned leaf, where a strip may expose a value; a function of the leaf and the installed equations, recorded nowhere | the refuter |
| S6 | a fat opaque term — a set comprehension — is denoted, so the refuter meets an atom; a frequent term is read β-normal, and a function value the leaf already names by a hypothesis `e = λx. T` is folded into that name wherever else it stands (the clause pipeline reads the naming pointwise, which reaches none of the value's other occurrences), the equation kept as spelled | the refuter |
| S7 | the economy audit — after a close under the recorder the leaf is probed for a cheaper spelling, and the finding is reported, never applied (G7). Its first probe — a refuted leaf that closes under `Basic()`, and the `By` respelled with `Normalized` closing on fewer rows — also runs after a session `by` closes, and returns as a `by_economy` diagnostic | the recorder; the first probe, a session `by` |

S3, orienting an equation premise as a rewrite, is what G7 bars; its
work is done by ground congruence closure inside the refuter, which
consumes nothing. S5, the instance normal form at every instantiation
boundary, is an engine-wide rule that defines what the bare form is,
and a stage only where the refuter instantiates on its own (the row
above): the stage hands the search the parts of the record values the
leaf spells, since no boundary the calculus owns reads an instance the
search forms. An instance is handed over β-normal, and with every
record projection applied to a value its record's constructor builds
computed to the part — `ring_add(mk_ring(a, …, g))` is `a` — a
projection reading through a definition whose value is a structure, a
record over type parameters, built by its constructor directly or
through another such definition: `complex_module(P, n).carrier` is
`P.terms(n)`. Such a definition is unfolded under a projection only, so
`module_on(R, complex_module(P, n))` keeps its spelling. A record
without a type parameter is a type of elements, and ℂ is the one the
corpus has: `re(complex(a, b))` is `a`, and no operation into it is read
through, so `re(z * w)` and `re(circle_path(c, r, t))` stand as spelled
at every boundary, and a proof that wants the parts cites the law
(`complex_field.PartsMul`). The boundaries are the grounding of a ∀-fact at witnesses
(`At`, an S4 plan, the session's `term_specialize`), a reading, an
unfolded definition and a Simp rewrite. A resident hypothesis is NOT
one: a statement's antecedent, a `Have` / `Obtain` claim and a `Let`'s
equation stand as the author spelled them, `V.carrier` at a packed `V`
included, and what `inspect` shows and `a.Hyp(text)` names is that
spelling. The apply rung reads BOTH sides instead: a candidate and the
goal, a guard and the hypothesis that supplies it, are compared in the
rung's reading — βη, the membership reading and this form — so a
hypothesis spelled `x ∈ V.carrier` supplies a cited law's guard
`x ∈ hom_set(…)`, and a goal `V.carrier = hom_set(…)` is closed by an
instance that spells it `hom_set(…) = hom_set(…)`, keyless and without
a bridge. Where the reading is what identifies the two, the rung reads
the leaf through the record equations before the assumption step (the
`RecordRead` step beside `MembershipRead`), and the proof's recorded
dependencies hold the equations it read with. The closers are handed
the leaf read the same way: the conditioning stage runs that step on
the working leaf before the refuter, the arithmetic closer or `set_tac`
(S2 above), so a close does not fail on a fact stated in the other
spelling. The hypothesis itself stays as written, and a move that
matches a pattern without closing — `Rw` by a resident equation, a
`Let`'s fold, a Simp rule's left side — meets the spelling the author
wrote. The equations are the record
door's projection equations and every definition whose value is a
structure (`registry.RecordReductions`), and a proof reads
each one it computes with as it reads any library theorem, so its
recorded dependencies hold them (prover/tactic, InstanceNormal).

**The ladder around the stage.** The CNF closer's `by` first runs the
conditioned attempt with the refuter barred and nothing grounded — in
a session, under the recorder and under a strict replay alike: a leaf
the strips, the apply rung and the shaping close needs no certificate,
and is closed before the key it would be looked up under is computed —
the normal form of the whole refute prop, over the bare leaf's CNF,
seconds to tens of seconds on a wide leaf, and for a session's new leaf
a key the store has no row under. Rung 1 tries the BARE spelling
against recorded certificates only; a strict replay passes over it for
a leaf the store holds a plan for — its recording closed in rung 2 —
and comes back to it only where that rung does not close. Before it
asks rung 1 by the key, a strict replay asks rung 1 and then rung 2 by
exact keys alone: a recording that closed at either wrote its
certificate with the row that names it, so the replay of the same leaf
closes there with no refute prop normalized, and where neither closes
the two rungs run as described here, on the keys (measured over the
corpus: 2,164 misses of rung 1's key in a replay, 108 seconds of
normal form, 1,654 of them at a `by` whose rung 2 then read a
certificate that its exact key names). A session
and the recorder ask it there too: their store also holds the plans of
other spellings of the leaf, a plan's key being the leaf before any
shaping, and is no record of how this `by` closes. Rung 2 runs the
conditioned attempt. A plan the store holds for the leaf is applied as
recorded. With none, S4 grounds, and the rung is run on the WHOLE leaf:
every premise reaches the closer as the author named it, its instances
beside it. Where that fails and a match pinned a premise in full, the
rung is run once more, live only, on the PRUNED leaf: the search has
fewer clauses to be lost in, and a shaping's `Basic()` — which
discards an instance that stands beside its premise, so that under
`Normalized`, `PreNormalized` or a denote the whole leaf reaches the
closer with its groundings undone — is handed a ground leaf. A close
made there records the plan of that run, which replaces, so its replay
is rung 2 applying the plan, and `by_closer` adds "conditioned on the
pruned leaf". The arithmetic closer reads its facts wide and is handed
the whole leaf alone. Rung 3, live only, retries the bare spelling
with full semantics — which is what keeps the second boundary. A `by`
no rung closes reports rung 2's failure on the whole leaf, and where
the pruned leaf was run that failure says so: the wide premises are
then not what the search is lost in. The standalone doors, `set_tac`
and `auto`, ground to the pruned leaf, and their own ladders run the
bare leaf beside it.

**Recording.** The deterministic stages record nothing; replay
re-runs them. S4's plans — pairs of a premise and a witness tuple —
live in the CNF store beside the certificates, keyed by the bare
leaf's α-key under canonical names for its free variables
(`prop.CanonicalFreeKey`), their premise and witness terms stored under
the same names, so every replay applies the recorded plans with no
search — a member's binder names are no part of its recording, and
a statement whose binders were renamed replays — and a change to the
grounding heuristics — which premises a plan replaces included —
reaches future recordings only. No conditioning action is rendered into a proof
file: the emitted `By(…)` is the bare spelling, and the text stays
the author's mathematics.

**What stays the author's.** S4 generates candidates and is not
complete: a witness no term of the leaf spells is an `At(…)`. The
apply rung invents nothing: a witness nothing spells, an existential
antecedent still folded, a relation only higher-order unification
would find, a fact three applies away. Its miss names the head whose
conclusion matched and the antecedent the context lacks; a head whose
conclusion equates two of its own binders — a spelled-out injectivity
`∀u v. f(u) = f(v) ⇒ u = v`, antisymmetry, extensionality — matches
EVERY equation, and the miss says so: that it matched is no sign it is
the law the step needs (the constitution's "A property of a map stands
in the context as its atom" is the author's side). Restructuring a goal, other
than splitting a conjunction — a `Have`, a case split, halving an ⇔ —
is proof structure. And premises that are insufficient stay
insufficient: conditioning adds no fact.

## A closer's capability is symmetric or absent

An author learns what a closer does from what they have seen it
close. So a capability a closer gains — reading a quotient, clearing
a divisor, any use of a fact it was not told to make — is exercised
the same way whether the fact stands in the goal or in a hypothesis,
or it is not built. "The closer does not clear a divisor from a sum:
cite the law" is a rule an author can hold. "It clears the quotient
in the goal and not the same quotient in a hypothesis" is an exception
found only by failing, and what is generalized from it is wrong. A
missing capability costs one cited step where it is wanted; an
asymmetric one costs failed attempts. Where only one side is
affordable, neither goes in — the boundary of the ℝ closer's divisor
clearing (the Playbook's arithmetic section, "Items 2 and 3 are one
boundary") is this rule applied.

What such a pass costs is read off the decisions that FAIL, not off
the proofs that replay. A pass that enriches the context and re-runs
the decision chain is paid at every failing decision, and the
arithmetic step decides each hypothesis under the others — decisions
made to fail — so the cost is multiplied by the size of the context.
A replay runs closes on the premises an author named and cannot see
it; the engine's `TestInspect_ArithProbeOnWideRealContext` is the
instrument.

## A structure is read on its carrier

An engine capability reads the guarded carrier laws of a group,
commutative ring or field: `group_on(G)`, `comm_ring_on(R)` or
`field_on(F)`. A whole-type fact is read through the chapter's bridge
at a record restricted to `𝕌`, where `InUniv` discharges membership.
The whole-type laws remain views for proof authors; a capability uses
one carrier reading of the mathematics.

Projection equations and record-valued definitions compute under
projections, using kernel theorems. The matching normal form computes
the same fields from their statements without building proofs. The
structure ring and chase closer consume this form and preserve every
membership required on a proper carrier, including division operands.

# Chapter Go — the authoring surface

The Go side of the shared API: how a proof is written and
landed. Read after §Playbook (the session side). The philosophy and
the quality bar are `library/chapter_constitution.md`; this section is
the mechanics — constructors, verbs, the cheat sheet, registration and
the harness; witness order is §Playbook's, and the recording flow is
`library/integrity/gates/record_cnf_test.go`'s header. The two are cut
by one test: a rule a reviewer holds a landed file to, replay green or
not, is stated in the constitution and cited here by its section; what
a file needs in order to compile and replay is stated here and cited
there. Every file under
`library/proofs/` is build-current, so it is a grep-on-demand
idiom source for anything not listed here.

## The framework (read this before writing)

A proof is a small set of pieces. The corpus is FAMILY
sub-packages (`library/proofs/<domain>/<family>/`; the brief names
yours):

- **The proof body — one constructor per member shape** (§"The
  constructors" below has each): `family.Theorem(stmt, closure)` for a
  single-section member; `family.Sections(headline, …)` for a
  multi-section one; `family.Lifted(headline, source)` for a member
  that is its ℝ twin carried across the embedding; a DEFINITION DOOR
  (`family.Define` / `family.DefineData` / `family.DefineInductive` /
  `family.DefineType` / `family.DefineQuotient` / `family.DefineSpec`)
  for a member that IS a definition; the STRUCTURE doors
  (`family.DefineStructure` with `S.Law` / `S.Axiom`, `family.Instance`,
  `family.StructureOf`) for a structure's laws and its instances.
- **Registration — family member**: an exported entry var in the SAME
  proof file (no `init()`), and this bullet is its full shape:
  `var <N> = family.Add(registry.ProofEntry{Name, Key, Build})`.
  `family` is the family handle declared once in `family.go`
  (you never touch that file). A proved member spells no `Deps` —
  `family.Add` panics on one: its dependencies are the entries its
  proof reads, which the family recorder writes into the family blob
  when you record the member, and replay serves exactly those. A cite
  is a reference to an entry var of a landed member or an imported
  family, so the edges a proof spells are compiler-checked: a
  same-family cycle is a var-init cycle, a cross-family cycle an
  import cycle, both compile errors — and a not-yet-landed entry has
  no var and cannot be cited: it lands first. Every family carries the typed wrapper
  surface (`zz_typed_thms_gen.go`); landed
  entries read `var Sing = singThm{family.Add(…)}`: ONE name is the
  registration and the typed citation surface.
  **Write YOUR new entry bare** (`var <N> = family.Add(…)`) — the
  wrapper type for a new member does not exist until the generator
  runs; the orchestrator's `go generate` at the checkpoint emits it
  and applies the wrap itself. The bare names of a proof body (`By`,
  `Cite`, `Argument`, `Expr`, `Nat`, …) are the package
  `library/authoring`, which your file DOT-IMPORTS —
  `import . "github.com/euc-ai/xugo/library/authoring"` — beside
  `registry` and the family packages it cites, exactly like
  `proofs/nat_num/nat_order/nat_order.go`. The names are in scope in
  the file that carries the import and in no other: a file that spells
  one without it is `undefined: By`, a file that spells none carries no
  import (Go refuses an unused one), and a package-level name of yours
  that takes one of them is `By already declared through dot-import` —
  rename yours. `go doc ./library/authoring` lists them. **A family proof file never
  touches CNF wiring**: no `//go:embed`, no `InstallCNFCache` — the
  harness installs the family's shared `<family>.cnf.pb` env-side
  (the family recording flow is the header of
  `library/integrity/gates/record_cnf_test.go`, and each family's own
  `family.go` header carries its two recorder env spellings).
- `Key` is the statement's own normalized key (paste what
  `TestEntryKeyIsOwnKey` prints); the statement IS the headline, and it
  is closed: its variables ∀-bound, its premises ⇒-antecedents, no ⊢ (a
  headline with hypotheses panics at the statement door, naming the
  closed spelling). `Reading` is the statement read in the encoding — hypotheses, degenerate cases, what a short spelling leaves out — served by `query dossier`; the constitution's cards section says when to write one.
  Do NOT edit
  `library/registry/registry.go` — types +
  aggregation only (duplicate Name/Key panics at package init).
- **`gates/replay_test.go`** (do NOT touch): `TestReplayAll`
  serves your member the entries its record names (DB-free), then
  force-replays your sections + Top bounded at
  those deps, and fails when what the build reads drifts from the
  record — re-record the member after changing what it cites. Family members run as subtests `<family>/<NAME>`.

Your file's shape comes from the constitution's principles and your own
session-validated proof, not from imitating an existing file. The corpus
is an IDIOM SOURCE: grep `library/proofs/**/*.go` for a specific
construct when a concrete question arises (every file there is
build-current, so what you find is live API) — targeted lookup, never
whole-file modeling. A brief citing a specific file is shape-target
evidence, not a template.

## The section boundary binds — write the statement's binders as parameters

The rule is the constitution's §"The section boundary is a binding
form"; this section is how it is written.

A section statement IS a λ. Its leading binders flow into the Go
closure that proves it, so a body never re-declares them:

```go
var BoundsLinear = family.Add(registry.ProofEntry{
    Name: "BoundsLinear",
    Build: family.Theorem(
        "∀A B C:num. (∀n:num. A * n ≤ B * n + C) ⇔ A ≤ B",
        func(a *Argument, A, B, C Term) {
            a.Iff()
            a.Forward("…", …)
            a.Backward("…", …)
        }),
})
```

**The rule: the parameters bind by dependency.** A statement is
binders and hypotheses, `∀x₁ … xₙ. H₁ ∧ … ∧ Hₘ ⇒ C`, and a hypothesis
depends on the binders it mentions. Parameters after the leading
`*Argument` open it in their order, any order that respects the
dependencies being the same theorem: a `Term` parameter binds the next
binder in the statement's order (strip + mint + ParseScope registration,
handed to you); a `Fact` parameter binds the hypotheses whose binders
are all bound before it — standing alone, all of them, read apart by
`a.Conjuncts`; standing together with other facts, one each, in the
statement's order, as long as they last. More hypotheses than facts
standing together is ambiguous and refused: move each fact to stand
right after the binders its hypotheses mention. A `Fact` where nothing
is available binds a bundle — the binders next in order up to the
hypothesis that mentions every one of them, the structure fact at its
components — which is what a bundle binder states (below). The
statement is closed — a section text with hypotheses left of ⊢ panics
at `SectionText`, naming the closed spelling. What the parameters leave
stays in the goal as a statement, `∀(the binders not bound). (the
hypotheses not taken) ⇒ C`: an induction proof that must NOT pre-strip
its variable writes the parameters before it and inducts in the body,
and the induction hypothesis is general in every binder left with it. A
hypothesis that is itself a conjunction stays one hypothesis where it is
written second or later; written first it reads as its conjuncts.

**`Term` unless the body needs a receiver.** A ∀-parameter may also be
spelled `*TermWrapper` — same binding, same value — and that spelling
earns its place only when the body calls the wrapper's own methods on
the variable (`x.Apply(…)`, `x.Eq(…)`, `x.To(…)`). A variable the body
only passes along — into `At`, `Cite`, a handle's `Apply` — stays
`Term`; a helper's parameters and results follow the same rule.

**Typed binder parameters (Go 1.27 surface — the default; every
family carries `zz_typed_thms_gen.go`).** A ∀-parameter may be spelled at its
statement type instead of `Term`: `*Expr[φ]` for any binder (`φ` a
phantom — the `A…E` letters, `Set[…]`, `Nat`, `Real`, … — all names of
`library/authoring`; a letter beyond `E` is
declared by `zz_typed_thms_gen.go` once a statement of the family binds
it, e.g. monoidal's `I`, and the phantom of another chapter's type is
aliased there once a statement of the family names the type, and for as
long after as a proof file of the family names it),
`*Arrow[X, Y]` / `*Arrow2[X, Y, R]` for a function binder, which arrives
BORN APPLICABLE (`f.Apply(x)` — postfix, domain/codomain static, no
`%v`-into-text needed to apply it). The phantom is checked against the
statement's binder at plan time — a wrong type is a loud panic naming
the parameter, not a downstream mismatch. Same goal move, same tree as
`Term` (1:1). A ⇒-parameter stays a `Fact`, except where the
antecedent is a fact of a structure on a set: then it is that
structure's typed fact, `group GroupFact[on.C]`, checked against the
antecedent's predicate at plan time and its carriers at binding. A
bundle binder binds the same way, at the letter of its own name:
`∀R:comm_ring_on(A).` is `R comm_ring.CommRingFact[on.R]`, and
`∀L:field_on(A).` is `L field.FieldFact[on.L]`. A
∀-binder whose run of binders ends in a guard stating its membership in
a carrier may be a member, `x, y *Member[A, on.C]`; the guard then binds
no parameter, and every conjunct of it must be one of those
memberships. Both are §"The structure doors" (typed structure facts and
members). Example (monoidal):

```go
func(a *Argument, op *Arrow2[carrier, carrier, carrier], mon Fact,
    s, t *Expr[indexSet], f *Arrow[index, carrier], onSets Fact) { … }
```

`Expr`/`Typed`/`Arrow`/`Arrow2`/`Nat` are names of `library/authoring`; a
chapter usually also aliases its letters (`index = A`). Inside
the body, `b.FixAs[φ]()` / `a.TermAs[φ](text)` are the typed Fix/Term
(same move + a checked adoption; `TermAs` reads its text at φ, so a
polymorphic constant the text leaves bare takes its instance from φ —
`a.TermAs[Set[A]]("∅")`, no `⟨A:A⟩`), and `x, xDef := a.LetAs[φ]("x",
text)` the typed Let: the text read at φ, the name's handle beside its
equation. A typed value is not a `Term`: it
yields its term through `Core()`, and a verb's term slot is a
`TermLike` — a typed value or a core term, taken as it is. The Go-built
terms over typed handles are the surface's functions: `Equal(x, y)` the
equation, `Lambda(x, body)` the abstraction; an application of typed
handles is text, `ctx.TermText("x_1(a_0)")`, since the handles are
registered names.

An introduction verb with no typed variant yet (`Obtain`/`Unpack`/
`Binder`, …) is not a wall: `ext.As[φ](…)` around its result is the
spelling — identical by construction (`As` is the one adoption gate
every typed verb funnels through anyway; import `ext` for it). If
your member needed such a wrap, say so in Notes — recurring `As`-wraps
around one verb are exactly how verbs get promoted to `<Verb>As`
(the constitution's §"The typed surface"). Do NOT invent the promoted spelling
yourself (`a.<Verb>As` does not exist until it does).

**Not written at a section boundary** — the constitution's rule (§"The
section boundary is a binding form") is that a body does not reconstruct
its statement's binders; what each spelling gives way to:

| Not this | This |
|---|---|
| `ctx.Var("A_0", NumType)` for a section Skolem, with a comment that declaration order is strip order | a `Term` parameter named `A` |
| an opening `StripQuant()` / `StripImp()` choreography | the parameter list |
| `ctx.Const(…)` lines that only exist so the statement PARSES | the family vocabulary (§"The family vocabulary" below) |
| `GroundHyp(MakePropText("<the premise, retyped>"), w)` | `h.At(w)` on the `Fact` parameter that premise arrived as |

**`a.Goal()` reads the goal** — a READ, never a step. It is there for
the solver kits that COMPUTE a proof plan from the statement rather
than taking premises (a kit that reads the goal's operator tree to
decide its own moves is the motivating case; such a member binds
NOTHING when the kit must see the ∀-prefix unstripped). Never re-parse
your own statement text to recover a Prop the Argument already holds;
that is the statement written twice.
It is NOT for inspecting the goal and branching on it — a proof
reacting to machine state is what the verbs exist to prevent.

**Structure verbs** (`a.Iff()` / `a.Cases(t)` / `a.Induct(nameOrTerm)`)
carry the argument's shape inside a `Derive` or a `Theorem` body. Each
OPENS a fan-out and takes no label of its own — the branch labels carry
the narrative — and each may be TERMINAL: when the branches close
between them the block is closed, and when one survives the deduction
continues on it. `a.Binder("N")` names a goal binder you are
deliberately NOT stripping (an induction variable whose branch bodies
need it as a term); it is not a proof step and takes its TYPE from the
statement. **The name is the statement's, in every closure.** Once a
parameter is bound the binders after it read α-renamed in the goal (`n`
prints `n₀`), and `Binder` inverts that rename: `a.Binder("n")` — and so
`a.Induct("n")` — finds `n₀`, binds `n` as a surface spelling for the
claim texts, and returns the engine's variable; the renamed spelling
(`a.Binder("n_0")`) still resolves, by exact match. So the string form
`a.Induct("n")` is one move in a zero-parameter closure and after
`func(a *Argument, f *Arrow[A, Nat], …)` alike. **Use the TERM form
whenever a step `Have` builds its claim programmatically**: `m :=
a.Binder("m")` captured before `a.Induct(m)` is a `Term` the step body
can build claims from (`MakeProp(v.Add(v.Suc(m), v.Suc(m)).Eq(…))`); the
same holds for the witness a `peano.Cases` split unpacks (`kv, kEq :=
a.Unpack(isSuc)`) — programmatic claims only.

**Two shapes legitimately stay outside the binding form** — boundaries
of the mechanism, not failures:

- **A ⇒-antecedent the proof later `Clear`s or grounds BY HANDLE stays
  a `HypHandle`**, not a `Fact` parameter: a `Fact` has `.At(…)` but no
  `Clear`-able identity. (The real fix is the close becoming a
  `By(premises…)`, which clears by construction — but that is an
  ARGUMENT change, so it does not belong in a boundary conversion.)
- **A body that must unfold a definition BEFORE stripping keeps the
  zero-parameter form.** `DefExpandStep` on a ∀-form goal behaves
  differently from `DefExpandStep` on a stripped `A ⇒ B` (on the
  latter it also discharges the antecedent), so binding first can
  leave a following `StripImp` with no implication. This is an ordering
  constraint in the proof, not a limitation of the boundary.

**The context parameter need not be named `a`.** When the statement
itself binds `a`/`b`/`c`, rename the context (`func(arg *Argument, a,
b, c Term)`) — the lint constrains only the BOUND parameters.

**Parameter names are lint-checked.** Binding is positional (Go
reflection cannot read names), so `TestLintBinderClosureNames` requires
the i-th `Term` parameter to be spelled like the i-th ∀-binder. A
swapped pair fails the build. `Fact` parameters carry no name
obligation — name them for their mathematical role, or `_` when the
body never needs them.

**pb rule:** converting the BOUNDARY re-keys nothing (the
CNF cache is keyed on the goal prop, and k single strips reach the
same prop as one strip-all). Changing the ARGUMENT — a `Chain`
rewritten as a `Derive`, a new `Have`, a different close — does. So a
conversion that suddenly needs a re-record is telling you that you
changed more than the boundary.

### Vectors and matrices: the dimension rides the type, not the statement

Two priors from outside this codebase mislead here, and neither is
corrected by anything you will see in a session transcript:

- A type `real^N` puts the dimension in the TYPE. XuGo's
  term-level chapters (`vector/`, `cartesian/carrier`) put it in a num
  binder of the statement and on a PHANTOM of the Go value. The
  statement spells `vec⟨n⟩(u)`, `dot⟨n⟩(u, v)`, `‖u‖_n` — the ring's
  components implicit (§Text format, "Implicit structure arguments"),
  the norm by its declared notation; the Go closure spells the vector
  binders as `*Vec[Real, DimN]` and the dimension binder before them.
- Go 1.27 generic METHODS exist and are this surface's idiom
  (`a.VecAs[Real, DimN](…)`, `NormPow2.At[DimN](u)` with `DimN` inferred).
  Reach for them first; `Term` parameters and `proof.At(dep, n, u)`
  are the fallback when a value has no phantom.

```go
// euclidean.NormTriangle — the dimension is written ONCE, on the
// parameters; every cite writes it off the vector.
Build: family.Theorem("∀n:num. ∀u v:(num → real). ‖vec_add(u, v)‖_n ≤ ‖u‖_n + ‖v‖_n",
    func(a *Argument, n *Expr[Nat], u, v *Vec[Real, DimN]) {
        sum := a.VecAs[Real, DimN]("vec_add(u, v)")       // anchored at the same n
        … By(Normalized, NormPow2.At(sum)) …           // norm's n comes from sum
        … By(Normalized, CauchySchwarz.At(u, v)) …     // u, v tied to one DimN

// euclidean.LinearBasisEstimate — two dimensions; crossing them is a compile error.
    func(a *Argument, m, n *Expr[Nat], f *VecFun[Real, DimM, DimN], x *Vec[Real, DimM], linear, member Fact) {
        xM := proof.Inhabit(x, member)                   // x, at the dimension m, with its membership
        … By(BasisExpansion.Read(real_ring.CommRing).At(xM)) … // the evidence rides the cite
        … ComponentLeNorm.At(i, xM.Vec) …              // an N-vector here would not compile
```

The rules: (1) a `*Vec[Elem, D]` parameter binds a carrier binder
(`num → Elem`) and anchors D's letters to the num binders bound BEFORE
it — the typed surface refuses a vector parameter ahead of its dimension; the
anchor is the section's own variable (`n_0` after a rename), resolved
through the surface names, never a bare `Var("n")`. (2) `a.VecAs[Elem,
D](text)` is the typed `Term` for a vector; `u.Dim()` is the term a cite
writes; a bare `dimtypes.AsVec` label has no `Dim()` and panics. A
dimension no letter spells — a Let, a literal, `suc(m)`,
`polynomial_degree(p)` — is anchored at the term itself:
`a.VecAt[Elem](dim, text)` carries `SomeDim`, the one phantom with no
name to resolve, and two such vectors are tied at the cite
(`SameDimension`) rather than at compile time; a closure parameter at
`SomeDim` is refused, since the binder door anchors by name.
(3) `proof.Inhabit(v, fact)` pairs a vector with the resident fact that
spells its dimension and itself as the last two arguments
(`vec⟨n⟩(zero, u)`, `tuple(n, v)`); the pairing cannot be crossed.
`proof.InhabitFrom(p, fact)` is the same pairing with the dimension
READ OFF the fact — the form for a vector the proof holds only through
its membership (`vec⟨suc(polynomial_degree(zero, p))⟩(zero, p)`), which
restates no dimension and carries `SomeDim`. (4)
The generated `At` of a member whose vector binders are read at ONE
dimension binder takes `*Vec[…, DimN]` and elides the dimension; a
membership among the antecedents — the conjuncts of the one ⇒ under
the prefix — makes the parameter an `*Inhabited` and the result a
`PremiseGroup` carrying the evidence; a stacked antecedent (a second ⇒
below the first) keeps the evidence with you — a `*Vec` slot takes no
`*Inhabited`, so nothing passes it unseen. A structure law's READING
refines its witnesses against the reading's own guards, and a point
whose membership in a COMPONENT set is one of them arrives as a
`*Member` (`DistSym.Read(metric).At(xM, yM)` with `xM :=
proof.MemberOf(x, inM)`), its membership bundled likewise — wherever
the guard sits in the reading's telescope: with a second antecedent
below it (`field.InvLeftUniqueOn.Read(L).At(xM, yM)` for `x ∈ c ∧ y ∈ c
⇒ x * y = one ⇒ inv(y) = x`, the `x * y = one` yours to list) or under
a ∀ after an earlier antecedent. A `*Member` embeds its term, so any
other `At` — an `ext.Typed` slot, `.AsFact().At`, a resident fact's
`h.At(xM)` — takes the point and leaves the evidence behind; such a
slot is never a component membership's. Where the member's membership
is nonetheless a guard of the instance (`x ∈ k` for a set `k` a
`proof.MemberOf` member was paired with), the `By` consuming the
premise reads it: the member listed beside the premise, a fact of its
evidence listed, or a resident fact stating the membership listed, or
the `By` is refused naming the member — `By(…, xM, h.At(xM))` or
`xM.With(h.At(xM))` (prover/proof/member_evidence.go). A step holding
the points as plain terms, their memberships inside a conjunction,
cites `.AsFact().At(x, y)` with the conjunction listed. A structure LAW's own `At`
lists the components first; at an instance READ it —
`dot.AddLeft.Read(real_ring.CommRing)` is the law with its components
pinned and its hypothesis discharged (proof.Read: kernel-derived at
consumption, stated form, keyless), one value for a `By` premise, a
`Simp` rule and the typed cite, whose `At` takes the law's remaining
witnesses (`vec_space.BasisExpansion.Read(real_ring.CommRing).At(x)`
with the vector membership named beside it). A
bare `By(dot.AddLeft, real_ring.CommRing)` still closes by the rung.
Inside a chapter stated over the structure the instance is the
RESIDENT hypothesis itself — `vec_space.MonoidalVecAdd.Read(ring)` is
`comm_ring_on(R) ⊢ R.carrier = 𝕌 ⇒ monoidal_op(vec_add(R.add))`, kept under the ring by the consuming
By — so a structure fact another law asks for as an antecedent is
supplied in the premise list rather than by a Have.
(5) These are the chapter's to declare, at its definitions:
`Implicit` (the components an operation reads), `Notation` (its outfix
form), `Dim` (its dimension slot); a chapter at an instance adds
`WithInstance(structure, instance)` on its family. A member never
restates them. Which phantoms the file has in scope is §"The generated
wrappers" below.

(6) A binder read at two dimensions, or at one that is not a binder,
keeps its plain slot: nothing is elided the statement does not
determine. The wrapper type is `ext/dimtypes.Vec[Elem, DimN]`, each
operation declares its dimension argument at its definition
(`DefEntry.Dim`), and the generator pairs every vector binder of a
statement with the dimension its operations read it at
(`Extensionality.At(uM, vM)` bundles two memberships the same way
`BasisExpansion.At(xM)` bundles one).

**A MATRIX is the same refinement at two dimensions**, and the surface
is at parity: the carrier is `num → num → A` read as a sequence of ROW
vectors, the Go wrapper is `dimtypes.Mat[Elem, Rows, Cols]`, and a
closure parameter spelled `*Mat[A, DimN, DimM]` anchors BOTH phantoms' letters
to the dimension binders fixed before it (`AnchorMat`, `a.MatAs`,
`a.MatFixAs`; `Rows()` and `Cols()` are what a cite writes for it, and a
bare label panics exactly as `Vec.Dim()` does). A constant that reads a
matrix argument declares the PAIR at its definition (`DefEntry.RowDim` /
`ColumnDim` → `registry.MatrixDimSlots`) rather than `Dim`, and the two
declarations are independent: `matrix⟨n, m⟩(zero, P)` declares both,
`matrix_act⟨k⟩(add, mul, P, x, i)` declares `Dim: "k"` for the VECTOR it
acts on and nothing for the matrix, whose row count that term does not
carry. The generator then refines a statement's matrix binders the same
way it refines its vector binders — both dimension binders leave the
parameter list and are written off the matrix (`MatrixDef.At(zero, P)`)
— and a matrix whose membership is among the antecedents arrives as a
`proof.InhabitedMat`. Which refinement a binder gets is decided by its
carrier shape and never by position: `num → τ` is a vector, `num → num →
τ` a matrix, and `ext.MatchesFun` flattens the arrow spine so the length
test alone separates them.

**A FUNCTION between two vector spaces is the third carrier**, `(num →
A) → num → A`: one type whatever space it carries into whatever space,
read at two dimensions as a matrix is, linear or not — a derivative's
map f is one as its derivative L is. The Go wrapper is
`dimtypes.VecFun[Elem, Source, Target]` — `*VecFun[Real, DimN, DimM]`
is a map read on n-vectors whose values are read as m-vectors — and a
closure parameter so spelled anchors both phantoms' letters to the
dimension binders fixed before it (`AnchorVecFun`, `a.VecFunAs`,
`a.VecFunFixAs`; `a.VecFunAt[Elem](source, target, text)` at dimensions
no letter spells; `Source()` and `Target()` are what a cite writes for
it, and a bare label panics as `Vec.Dim()` does). The image of a vector is typed by the
map: `L.Apply(u)` takes a `*Vec` at L's own source phantom and is a
`*Vec` at its target phantom, anchored at L's target term — what
`a.VecAs[Real, DimM]("L(u)")` spells by hand, the dimension read off the
map instead of restated, and a vector of another dimension under it does
not compile.

```go
// Schematic — a statement over a constant D(n, m, f, c, L) that reads two
// maps of n-vectors to m-vectors and a point at n, `Bound` a member
// stated over it. Neither dimension is restated in the body.
    func(a *Argument, n, m *Expr[Nat], f, L *VecFun[Real, DimN, DimM], c *Vec[Real, DimN], derivative Fact) {
        image := L.Apply(c)                                      // *Vec[Real, DimM], anchored at m
        … By(Bound.At(f, L, c), derivative) …                    // n and m written off the maps and the point
        twice := a.VecFunAs[Real, DimN, DimM]("λu:(num → real). &2 • L(u)") // a map built in the body
```

A constant that reads map arguments declares the pair at its definition
(`DefEntry.SourceDim` / `TargetDim` → `registry.VecFunDimSlots`),
independently of `Dim` and of `RowDim`/`ColumnDim`: the constant above
declares `Dim: "n"` for its point and `SourceDim: "n"`, `TargetDim: "m"`
for its two maps, and a constant of maps of one space into itself names
its one dimension binder for both. The generator then refines a
statement's map binders as it does its matrices: a binder every
map-declared constant reads at ONE source binder and ONE target binder
becomes a `*VecFun` at both phantoms and both dimensions leave the
parameter list, written off the map and tied to every vector, matrix
and map read at the same binder (`SameDimension`). Two maps composed in
the wrong order, a map between two spaces where a map of one space into
itself is read, and a matrix or a plain arrow at a map's slot are
compile errors. A declaration governs EVERY map argument of its
constant, so a constant whose maps are read at different pairs of
dimensions — a composition taking f from n to m and g from m to k —
declares none, as `matrix_mul` declares none. Three limits, stated
because the type does not show them. The phantoms are authoring intent,
as a vector's is: no fact that the map carries n-vectors to m-vectors
rides the value, and a statement that needs one states it. Source and
target are sequences over ONE element; a map into sequences over another
type keeps its plain slot. And the two worlds meet one way only: a
`*VecFun` passes to a plain `Typed` slot — the `At` of a member none of
whose constants declares the pair — while a plain `*Arrow` does not pass
to a `*VecFun` slot, and is adopted by its text, `a.VecFunAs[Real, DimN,
DimM]("L")`.

### The generated wrappers

Every family carries `zz_typed_thms_gen.go`, generated from the entries'
own statements by `library/cmd/gen_family`, which `go generate
./library/proofs` runs once over every registered family; a new family
joins by being registered, its package linked from an aggregator. Per
theorem the generator writes:

- `At(w…)` / `Cite(w…)` — the ground cite, the type instance INFERRED
  from the typed witnesses and installed exact (the cheat sheet's
  `<Entry>.At` row has the witness order and the partial-tuple rule);
- `Inst` — the explicit type instance, where there are no witnesses to
  infer from: a SOLE-letter statement spells `Inst[τ]()` (one variable,
  nothing to pair — `proof.InstSole` binds it namelessly), a
  multi-letter statement spells `Inst(TypeBinder.BindA[τ](),
  TypeBinder.BindB[τ'](), …)`, one named binding per letter, "bind A to
  τ", and a wrong, missing or double letter panics listing the
  statement's own;
- `Read(instance)` on a structure law, which drops the component slots
  and keeps the law's remaining witnesses (the cheat sheet's `Read`
  row); for a structure with one or two carriers, the structure's
  phantom and its fact alias (`GroupStructure`, `GroupFact[Car]`),
  declared in the defining family's file, and a typed `Read` that
  infers the structure and carriers from the instance (§"The structure
  doors", typed structure facts).

The wrapper of a definition a proof may open — a `family.Define` or
`family.DefineSpec` entry, one constant — also answers the constant its
door minted (`DefinedConstant`), which makes it the `proof.Definition`
that `Unfold` and `a.Unfolded` take; a structure's wrapper has the
method from the `*registry.Structure` it embeds. A theorem's wrapper
has none, so naming a theorem where a definition belongs does not
compile.

A `family.Define` var is wrapped like a `family.Add` var, and so is a
`family.DefineStructure` var: `var ModuleHomomorphismDef =
moduleHomomorphismDefThm{family.DefineStructure(…)}`. A structure's
wrapper embeds the `*registry.Structure` the door returns
(`registry.StructureLike`), so the one var is both the structure —
`S.Law`, `S.Axiom`, `S.Statement`, `family.Instance(S, …)`,
`WithInstance(S, …)`, `S.AtUniverse(…)` — and its definition entry with
the typed `At` / `Inst` above. The definition at an explicit
instance is `ModuleHomomorphismDef.Inst(TypeBinder.BindA[A](),
TypeBinder.BindB[Set[B]](), TypeBinder.BindC[C]())` — B bound to
`set(B)` for a map out of a quotient module — and at witnesses that
carry the instance it is `ModuleHomomorphismDef.At(R, N, M, g)`.

A wrapper is a `registry.EntryLike` (`Entry`) and a `proof.NamedDep`
(`DepName`), so a Deps list, a bare cite and `ctx.Dep` take it as they
take the entry; the entry's other fields and methods are reached
through `Entry()`.

Generated type parameters are the deliberately letter-free `Type0,
Type1, …`: inside a generic method the parameter name is erased, so a
parameter spelled like a letter would only LOOK like the letter's
phantom alias while denoting the caller's instance.

A statement naming a typedef renders as the typedef's own phantom,
declared beside the mint (`dsl.Real` / `dsl.Int`, `peano.Ind`,
`nonneg_real.Hreal`, `eudoxus_slope.Nadd`, `list.List`, `complex_field.Complex`). The
generator's table (`typedefPhantoms`) maps metatype to owner; a metatype
absent from it fails loudly, and landing the phantom beside the mint
plus its table row is the teaching the error asks for. A phantom minted
below the chapters (`Real`, `Int`, `Ind`) is in every proof file's
scope, a name of `library/authoring`, so ℤⁿ's real images under
`vec_of_int` are `a.VecAs[Real, DimN]("vec_of_int(u)")`. The phantom of
another CHAPTER's type is aliased from its owner in the preamble of the
generated wrapper file where the family's STATEMENTS spell the type, and
is in scope in that family's proof files from then on: the generator
keeps an alias a proof file names bare, so the last such statement
leaving the family — a member moved to another chapter — breaks no file
it leaves. A chapter whose bodies alone name such a type from the start
names the phantom by its owner (`complex_field.Complex`): the generator
runs on a package that compiles. The generated file itself
reads the proof surface through the same aliases (`Fact`,
`Typed[Real]`), by a dot import of `library/authoring` where it names
one. A name outside that surface, such as `proof.InstSole` or
`on.Carrier`, keeps its qualifier, and so does a name a method's own
parameter shadows. The integer polynomial `(num → num) → int` is
written as `library/authoring`'s `IntegerPolynomial` wherever it
stands, as a proof file writes it: `Typed[IntegerPolynomial]`,
`Typed[Formula[IntegerPolynomial]]`, and `Typed[Fun[Nat,
IntegerPolynomial]]` for `num → (num → num) → int`. The file carries no
statement: a wrapper's statement is its entry's, served by `xugo query
member`.

A statement letter beyond `A…E` is the other phantom the file declares:
one for each letter a registered statement of the family binds, its
hypotheses' included, a zero-size type under the letter's name whose
`Reify` is `MakeVarType` of that name, the contract `ext.A…E` keep. A
proof file of the family spells it bare (`*Arrow[Nat, Set[I]]`), and no
member declares one (`TestLintTypeLetterPhantomIsGenerated`). Every
capital is such a letter, in every family alike: `library/authoring`
exports no capital beyond `A…E` (`TestSurfaceSpellsNoOtherLetter`), its
truth constants being `True` and `False` and its dimension letters
`DimN`, `DimM` and `DimK`. Only a multi-letter `var:` type variable whose
name the surface exports under another meaning has no phantom: the file
names it in a comment and `gen_family` in a note, and a member that
wants it typed declares a phantom under a name of its own, the one
hand-declared letter phantom the lint allows. A letter that only
a statement about to land binds is declared when the family regenerates
after the landing, so `emit-section` spells the letters the family's
registered statements bind and keeps `Term` at any other
(`typedgen.LettersInScope`).

The exits from the typed surface are explicit. `Core()` is the term a
typed value holds, and `Equal` / `Lambda` build on typed values as on
any term. A partial-witness cite stays on
untyped `At` / `ctx.AtTypes`, which also remains the spelling for
instantiating a multi-variable non-entry Thm, such as a `TypeDefExpand`
axiom; a Thm or raw row with exactly ONE type variable — machine-named
included — takes `ctx.AtSoleType(dep, τ)`, no name, no position.

### The family vocabulary

A chapter states its alphabet as data: `registry.NewVocabSpec` rows in
vocab.go, one per name, attached by `Family.WithVocabSpec`, and the
generated zz_vocab_gen.go hands the same rows to proof bodies as
handles (the `ops` accessor a body builds with). A domain
`registry.Alphabet` carries the types several families share; an `Embed`
row takes another chapter's alphabet whole (the words faces embed
`machine_word.Bundle`). A name's type comes from the domain table or the
mint, which `Term` and `Defined` rows read, or from the row itself —
`Spelled`, for an instance the chapter pins: a phantom spelling reified
by `ext.HolTypeOf`, or a type the domain table cannot carry.

A statement parses without a row for every minted constant it names:
the script's constant resolver serves any minted name at its generic
type (prover/proof/script.go, the replay-side mirror of the session's).
What a row adds is one of two things — when a chapter declares one is
the constitution's §"The section boundary is a binding form", "What a
row buys":

- **a PINNED instance in the parse scope** — `Term` declares the name at
  ONE instance for every statement the chapter parses, which is what a
  chapter naming a constant beside its own type letters needs (`nil`
  beside an `A`-lettered term, so `nil⟨A:B⟩`-style annotation is not
  forced), or a name whose generic instance would otherwise freeze the
  wrong letters into a statement (the pinned-constant gate,
  ext/dsl/build.go); `Poly` is the row for a name the chapter states at
  two instances at once;
- **a handle** — the generated ops field members build terms with
  (`v.Cons.Apply(x, m)`), `TermText` / `Built` for terms the rows cannot
  spell as a name.

The generated surface is the row set's mirror and nothing more:
deleting a row a member's body builds with fails at `go generate` / the
drift gate, not at the parser, and that failure says only that rows and
generated code must agree.

## The constructors

One per member shape; each is the `Build` of the entry literal.

- `family.Theorem(stmt, closure)` — one section. The statement parses
  against the family vocabulary BEFORE the closure runs, so anything
  its text mentions must be in the vocabulary, not declared in the body.
  The statement is one string, or a `Statement` written in parts —
  the one string assembled from them, the hypotheses ∧-joined into the
  one antecedent the closure's `Fact` parameter binds:

  ```go
  Build: family.Theorem(Statement{
      Binders:    "∀L:field_on(A). ∀k:set(A). ∀t:A.",
      Hypotheses: []string{"subfield(L, k)", "t ∈ L.carrier"},
      Conclusion: "comm_ring_on(«R»)",
      Abbrev: Abbrev{
          {Name: "O", Text: "ring_away(field_ring(L), polynomial_image(field_ring(L), k, t), t)"},
          {Name: "R", Text: "restrict_ring(field_ring(L), «O»)"},
      },
  }, func(a *Argument, L FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], h Fact) { … }),
  ```

  The abbreviations (§"Text format", "Abbreviations") are in scope for
  every claim and term text of the body — `a.Have("…", "fst(«P») ⊆ «O»",
  …)`, `a.TermAs[Set[A]]("«O»")` — and `emit-section` writes a member
  back in this form, folding its claims into the names. A statement
  with a premise reads in parts; one without stays the one string. The
  rule is every statement's, whichever door states it — `family.Card`,
  `family.Lifted`, `ctx.Lemma`, a law's body under `S.Law`, `S.Axiom`,
  `S.Statement` or a definition's `Conjunct` — and the lint
  `TestLintStatementInParts` refuses a premise written in one string,
  printing the parts to paste.
  A claim of the body is written as the statement is: `a.Have`,
  `a.Obtain` (its numbered and typed twins with it), `a.ObtainChosen`
  and `a.Hyp` take the one string or a `Statement{Binders, Hypotheses,
  Conclusion}`, which assembles to the string the verb reads — the
  hypotheses one per line, ∧-joined into the one antecedent; the
  claim's own `Binders` exempt from the capture check as a section's
  leading binders are; no `Abbrev` of its own, since a claim
  reads the member's table (a claim declaring one is refused). A claim
  with a premise is written in parts where its one string would run
  past 100 columns on the claim's line (xugo_fmt's width, counted from
  the line's indentation), and as the one string where it fits: `∀x:A. x ∈ s ⇒ f(x) ∈
  t` reads as one formula, its premise the quantifier's range, and
  parts pay off where the premises are long or many. `emit-section`
  renders a claim so, and `TestLintClaimPartsByWidth` refuses either
  layout on the wrong side of the width, keeping in parts a claim
  whose `Binders` an abbreviation it spells is written over. A text
  — the one string, a part, a term, an abbreviation's text — whose
  line still runs past the width is laid out by `xugo_fmt` as a chain
  of literals joined by `+`, one line each: its binders end a line
  and their scope stands four spaces in, an operator chain breaks at
  its loosest operator, the operator ending each line, and a group
  breaks at its commas. The pieces read as the one string does, the
  lexer skipping the blanks between them, and a text that fits is one
  literal again. A label, a card's note or a `Reading` past the width
  is a chain too, broken at its blanks into the fewest lines, as even
  as that allows, and spelling the same string byte for byte. Write
  either kind as the one string: the formatter breaks it, and breaks
  any other line of code past the width at a list on it: a call's
  arguments go to the line under it, together where that line holds
  them and one to a line where it does not, and a literal's elements
  and a function's parameters go one to a line. A claim
  is not held to the standard form — `By` and `Simp` read a telescope
  either way, so a curried claim may stay the one string.
- `family.Sections(headline, func(ctx *Script, headline string)
  *GoalStackNode {…})` — several sections. The headline is the FIRST
  ARGUMENT (it is what a citing consumer is served); the body receives
  it back and opens its top with `ctx.Theorem(headline, closure)` —
  return that section; a divergent top literal panics (α-guard).
  `ctx.Lemma(stmt, closure)` opens each intermediate; both Qed
  themselves. A cross-section citation is closure capture:
  `chain := ctx.Lemma(…)` then `Cite(chain)`, and what the sections
  share is a Go local of the body.
- `family.Derived(headline, func(ctx *Script) Thm {…})` — the member
  shape whose top is a DERIVED theorem, not a section. Its one client
  is `family.Lifted`; a definition, of any genre, is a definition
  door's and never this. Headline first as in Sections; the constructor
  BridgeNormalize-lifts the raw derive output into the headline's
  α-form and panics if the two are not normalize-equivalent, so the
  served, built, and stated forms coincide.
- `family.Lifted(headline, source)` — Derived specialised to a TRANSPORT member,
  whose whole proof is "this is its ℝ twin, carried across the
  embedding" (one `IntOfRealDerive` step). The member is then pure
  data, so write the data: `Build: family.Lifted(mulAssoc,
  real_construction.MulAssoc)` in the entry literal. There is nothing to
  declare: the constructor makes the `int_of_real:<source key>` use
  itself (BuildSpec.Capabilities — its own record of what the body
  does, not an author field), and the family recorder observes it
  like every other use. Use `Lifted` when the source is a landed
  entry (imported-package vars initialize first, so its Key
  is set), `LiftedFrom` when the source has not landed yet — and
  migrate the pair to `Lifted` when the source lands.

### The definition doors

A member that IS a definition takes none of the constructors above: it
is the entry literal of a door, with no Build closure of your own.
Registration mints the constant(s) at package init (EXCLUSIVE,
process-global), and the entry's Build re-derives the characterizing
theorem through the define composite. That every constant a chapter
spells comes in through a door, and which chapter mints it, is the
constitution's §"Definitions: a chapter mints its own constants".

A door that registers ONE entry — `Define`, `DefineStructure`,
`DefineSpec` — takes the entry's `Key` in its literal, as `family.Add`
does: the characterizing statement's own key, which registration reads
and does not compute. Write the literal Key-less and let the key gate
paste it (`XUGO_PASTE_KEYS`, the same run that pastes the chapter's
theorems' keys); `emit-section` writes it into the call it renders. A
door that registers SEVERAL entries from one literal has no `Name:`
line per entry for a key to stand under (registry.ProofEntry.Key).
`DefineInductive` spells its entries' keys in the literal's `Keys`
field, one field per entry (`Keys: registry.InductiveKeys{Rules,
Induct, Cases, InductStrong}`), and its registration reads them and
normalizes nothing: a principle of a relation with many rules takes
over a second to normalize, and every process that links the corpus
runs the door. Write the literal without `Keys` and the same gate
pastes the block. `DefineData` (with its record's projections),
`DefineType` and `DefineQuotient` compute their entries' keys at
registration.

- `family.Define(registry.DefEntry{Name, Key, Const, Type, Equations, …})` for
  an equation-shaped constant (direct / recursive, whose `Deps` name only
  the family's own definitions its equation spells — the edge to another
  family's constant is read off the equation, the import orders its mint,
  and registration refuses the entry in `Deps`; `Measure` +
  `Termination` actions + `Deps` naming the entries that serve
  `wellfounded_recursion` / `wellfounded_measure_less`
  (relations/well_founded's) for the WF shape — the termination proof is
  the author's mathematics).
- `family.DefineData(registry.DataEntry{Name, Type, Params, Constructors,
  Principles})` for a datatype (registers the four derived entries under
  the names `Principles{Induction, Recursion, Injective, Distinct}` spells
  — the chapter's own words, `list.NilNotCons`, so a session cites what
  the file's var is called; nothing is derived by suffix, and a missing or
  superfluous name is refused at registration; Induction/Recursion carry
  `ServesAs`; a RECORD — one constructor — may declare `Fields:
  []registry.DataField{{Name, Const, Overload?, Field?, Symbol?}}`, one
  per constructor argument, and the door then also defines each part by
  its projection equation (`complex_re(complex(a, b)) = a`, registered
  under the field's Name, the word `Overload` declares written for it); a
  part with a `Field` reads as a field of a value of the record, `R.add`
  for `ring_add(R)`, including expression receivers such as `P(n).zero`,
  constructor values and nested fields; a field returning a function
  can be applied or passed as a value, as in `P(n).add(u, v)` or
  `P(n).add`, and an applied field types its arguments at the field's
  domains as the projection applied to the record and the arguments
  does — `∀a b. R.add(a, b) = R.add(b, a)` reads `a`, `b` at R's
  carrier. A part with a `Symbol` — an operation or a map — reads
  by that symbol, `c + d` for `ring_add(R)(c, d)`, wherever a binder or a
  declared variable of the record's type is in scope, resolved at the
  operands' types like a structure fact's components (two values of one
  record at one carrier refuse the symbol). Intrinsic arithmetic and
  applicable declared operators retain their precedence; use the field
  explicitly when they serve the same operand types. The chapter
  spelling keeps the field whenever the bare symbol would be ambiguous
  or select another operation, and otherwise writes the symbol
  (`module_record.RingOpsData` is the model) — in a display, which
  types nothing, only where that field alone holds the symbol (the
  output door, §"Implicit structure arguments"); it derives the record's
  extensionality `u = v ⇔ p₁(u) = p₁(v) ∧ …` under
  `Principles.Extensionality`, and hands back `Parts` — that law and the
  projections as ONE rule set — so an equation between records is read
  componentwise as `Simp(Parts, Fwd(<operation's definition>)),
  ByArith()` (complex_field is the model). A projection of a packed
  value is computed wherever an instance is handed over (S5, the
  instance normal form), so a proof does not rewrite with the projection
  equations. The family's generated file names each one after its
  field's entry, `module_record.RingAddDef`, the name a Deps list and a
  cite spell; the handle's `Fields` slice is how the generated file
  reaches it, and a proof does not index it;
  the session's `data:` payload declares no fields — a session defines a
  part by a `recursive:` projection equation, which the equation compiler
  reads as a definition by cases).
- `family.DefineInductive(registry.InductiveEntry{Name, Keys, Const, Type,
  Params?, Rules, Deps})` for a relation defined by introduction rules
  (registers `<Name>Rules` / `<Name>Induct` / `<Name>Cases`, plus
  `<Name>InductStrong` where a rule has a premise to strengthen — the rule
  set verbatim, the weak rule induction, the canonical case analysis, and
  the induction whose step carries the relation beside the property — each
  derived by kernel rules from the closure the constant is minted with; NO
  definition entry: the closure form is refused at every unfold surface,
  and a definition of the same family that spells the relation names one of the three in `Deps`;
  the door's first charter is one relation with declared parameters whose
  premises are side conditions or `∀ū. G ⇒ R(p̄, s̄)`, no mutual
  induction; the handle's fields are wrapped by hand, `var FiniteInduct =
  finiteInductThm{finite.Induct}`, the generator's own precedent for a
  non-literal name).
- `family.DefineType(registry.TypeEntry{Name, Type, Abs, Rep, Pred,
  Existence?, Witness?})` for a type carved out of a representation type
  by a predicate (registers `<Name>Retraction` and `<Name>Membership`, the
  var is `<Name>Def`; the inhabitation `∃x. Pred(x)` is proved at the mint
  by the normalizer when trivial, else `Existence` names the chapter's
  entry proving it — `∃x. Pred(x)`, or with `Witness` the applied form
  `Pred(w)` the basic type definition takes (`is_num(ind_zero)`) — and the
  type is minted on that entry's PROMISE: the axioms derive from its
  certificate at replay, and forcing the promise runs the entry through
  `registry.ForceEntry`; the abs/rep names are claimed first, so a name
  another chapter minted refuses; each entry's Build runs the
  `define_type` composite, its inhabitation child closed by the Existence
  dep's certificate, which must state the child — `∃x. Pred(x)`, or the
  reduced membership at Witness — α-equally).
- `family.DefineQuotient(registry.QuotientEntry{Name, Type, Mk, Abs, Rep,
  Relation, Equivalence, Deps?})` for the quotient of a carrier by a
  relation the chapter defined (registers the seven entries
  `<Name>Surjectivity` / `Induct` / `Sound` / `Exact` / `Eq` /
  `ForallOnImage` / `ExistsOnImage`, the var is `<Name>Def`; `Equivalence`
  names the entry proving `equivalence(R)`, the one input every section's
  composite child cites; a function on the classes is `family.Define` with
  class patterns and `Respects`, see §"`family.DefineQuotient(registry.QuotientEntry{…})`
  and the lift" below).
- `family.DefineSpec(registry.SpecEntry{Name, Consts, Spec,
  Existence|ExistenceBody, Deps})` for a specification group (constants
  pinned by CHOICE against `Spec`, in definition order; serves BOTH
  provenances — CLAIM when every constant is already registered, FRESH
  mint otherwise; exactly one of `Existence`, the claim sites' one-cite
  value form, or the ctx-hosted `ExistenceBody` closure for a proof
  needing declarations/env-bound constructors).

`DefEntry.Spelled` is for a definiendum the text DSL cannot spell in
head position — an operator (`,`, `+`) or a name the DSL keeps for its
own surface (`_0`, `suc`, `bit0`, `real_of_num`) — the equations
spelling the stand-in and the constant minted under Const.

`DefEntry.MembershipRead: true` declares that the closers read a
membership in the constant as the set-builder its definiens is: a direct
definition `∀ā. c(ā) = {x | φ}` (or the three-part form) whose `y ∈ c(ā)`
then reads as φ at y in By's conditioning (S2: the refuter, Arith), the
apply rung and a hypothesis opened, and which the set driver opens —
in the goal and in every hypothesis, under a binder too, so a cited
instance's guard `∀x. x ∈ ⟦a, b⟧ ⇒ …` reads as bounds. The constant
reads exactly as the set-builder it names, in every closer; the
reading is the kernel's, through the definition the door minted —
whatever meta an occurrence was built with, the parser's `..` operator
included, which carries none (prover/tactic, membership_declared.go) —
and adds no dependency, as `Unfold` adds none. `m .. n`, the four real intervals, `preimage_on` and `fun_support`
declare it, as mathlib marks `mem_Icc` a simp lemma; a constant without
it stays closed until a proof opens it, whatever its definiens — most
of the corpus's set-builder definitions (a topology, an image, a
kernel) are reasoned about as objects. The door refuses the
declaration on a definiens that is no set-builder over the arguments,
and on a recursive, WF or lift definition. A membership law beside such
a constant (`real_topology.ClosedIntervalMembership`) is the reading as
a statement, for a rewrite or an instance; a closer needs no citation
of it.

A spec-genre ε-mint is `DefineSpec` whenever `proof.AnalyzeSpecGoal`
admits it — a constant applied at goal binders or pair literals of
them. A specification at an encoding (num_pair_fst at num_pair(x, y))
is one it does not admit: it is a `Define` whose equation spells the
choice (`num_pair_fst(n) = εx. ∃y. n = num_pair(x, y)`), and its
property is read off by `Unfold` once the existence is in hand, as for
every choice constant (§"def_expand"). Peano's ind_suc and ind_zero are
two such definitions, read by `indSucSpec` through
`ExistentialConstDefStep` with the two obligations of each choice as
cases; the typedef itself (NumDef) goes through `DefineType`. No
ε-witness ceremony is written by hand, and none through `Derived`.

A session-validated definition arrives here for free: `emit-section`
renders a `define` session section 1:1 as the matching door call (the
`define` row of §"Session commands").

#### `family.DefineQuotient(registry.QuotientEntry{…})` and the lift

The chapter form of the `quotient:` payload (library/registry/
define_quotient.go). ONE call mints the type over the equivalence-class
shape with its class map and abs/rep pair at package init and
registers the seven entries `<Name>Surjectivity`, `<Name>Induct`
(ServesAs `<type>_induction`), `<Name>Sound` / `<Name>Exact` (ServesAs
`<type>_sound` / `<type>_exact`), `<Name>Eq` (a use rule: an importing
session installs it), `<Name>ForallOnImage` and `<Name>ExistsOnImage`,
each Build ONE `define_quotient` composite whose child is the
`Equivalence` dep's certificate (α-checked against `equivalence(R)` —
an entry proving something else fails the Build loudly). The class map
is spelled `⁅x⁆` and by the word `class` (`ClassNotation` on the
handle says whether the notation was registered — a second quotient
over one carrier keeps its class map's name alone).

```go
// real/tower/internal/nonneg_real/definitions.go
var HrealDef = family.DefineQuotient(registry.QuotientEntry{
    Name: "Hreal", Type: "hreal", Mk: "hreal_of_nadd", Abs: "mk_hreal", Rep: "dest_hreal",
    Relation: "nadd_eq", Equivalence: eudoxus_slope.NaddEqEquivalence,
})

// A function on the classes: family.Define with class patterns, the
// respectfulness obligation closed by Respects (here the layer below's
// well-definedness law, one cite). The door declares HrealDef.Sound and
// HrealDef.Exact as the entry's deps itself.
var HrealAddDef = hrealAddDefThm{family.Define(registry.DefEntry{
    Name: "HrealAddDef", Const: "hreal_add", Type: "hreal → hreal → hreal",
    Equations: []string{"∀a b:nadd. hreal_add(⁅a⁆, ⁅b⁆) = ⁅a + b⁆"},
    Respects:  []Action{Cite(eudoxus_slope.AddWellDef)},
    Deps:      []registry.EntryLike{eudoxus_slope.NaddAddDef, eudoxus_slope.AddWellDef},
})}

// A law over the quotient: induct each class-typed binder to a
// representative, compute at the classes, cite the law below.
Build: family.Theorem("∀x y:hreal. x + y = y + x",
    func(a *Argument) {
        a.Induct("x")
        a.Induct("y")
        a.Show("…", Simp(Fwd(HrealAddDef), Fwd(HrealDef.Eq)), By(eudoxus_slope.AddSym))
    }),
```

A quotient over a POLYMORPHIC carrier takes the carrier's type letters
as its parameters, read off the relation's constant (`free_group(A)` over
`word_equiv : list(prod(A, bool)) → …`; the relation text is read back
at the constant's own letters, so the type carries `A`, never a parser
stand-in). One consequence for the chapter: EVERY definition whose type
or equation mentions the quotient type or its class map lists the
quotient entry (`FreeGroupDef.Surjectivity`) in `Deps` — Go initializes a
package's variables in declaration order, its files taken by name, and
a variable waits only for the package variables its initializer names.
A `Define` that spells the quotient in its text alone names none, so
one declared in a file that sorts before the quotient's runs FIRST and
fails "unknown type" at the type parse.

Two readings the text DSL makes that a chapter over a polymorphic
carrier leans on. The two operands of `=`, `≠` and the arithmetic
operators are unified across a constant's occurrence-local stand-ins:
a bare polymorphic nullary beside a typed partner reads at the
partner's instance (`free_one * x` dispatches to the chapter's `*`,
`free_one = ⁅nil⁆` needs no ⟨⟩ tie), while two sides written at
different letters of the author's still disagree. And a constant a
chapter's vocabulary PINS (`Term("nil")`, list(A)) is re-read through
its meta where an application demands another instance of it:
`cons(x, nil)` with `x : prod(A, bool)` puts nil at
list(prod(A, bool)), and `⁅nil⁆` at the empty word. The re-read
happens in one place only — the application is being read through its
head's meta, the last reading it has, and the pinned instance has
failed to unify with the argument's domain — so a pin that DOES unify
is what instantiates the application: `card(∅)` in a chapter pinning
∅ at num reads at num, which keeps a premise installed at the pin and
a goal built from the same text one instance (a rule keyed on how the
expected type is SPELLED cannot serve here: a pinned head's generic
letter and an author's letter are spelled alike). The session's
elaborator, which pins nothing, reads the same texts the same way, so
a claim the session accepts the Go claim parse accepts.

A representative an induction introduces is named by `a.StepArgs("xr")`
when a later claim text must spell it; `HrealDef.Surjectivity` cited
by `By` closes `∃xr:nadd. x = ⁅xr⁆` for a free x (the apply rung, no
key). A transported law records zero refutation keys this way: the
`By` of the law below is the apply rung's instance.

### The structure doors

How a structure is stated — a predicate over explicit components, a law
a Horn theorem, an instance a theorem of a chapter of the carrier,
inheritance the definition's shape — is the constitution's
§"Structures"; these are the doors that write it.

- `family.DefineStructure(registry.DefEntry{…})` / `S.Law(body, proof)` /
  `S.Axiom(body)` — the STRUCTURE door (registry/structure.go): a
  structure is a Define entry whose one direct equation applies the
  predicate to its COMPONENTS on the left — `∀op:(A → A → A). ∀e:A.
  comm_monoid(op, e) ⇔ C₁ ∧ … ∧ Cₙ` — and DefineStructure reads the
  components (names and type spellings) off it once. The generator
  wraps the var in its definition entry's typed wrapper, which embeds
  the structure (§"The generated wrappers"). `S.Law(body,
  proof)` is `family.Theorem` at the statement `∀<components>.
  <pred>(<components>) ⇒ <body>` (S.Statement renders it: adjacent
  same-typed components grouped, a body whose top-level connective is
  ⇔ parenthesized); `proof` is `func(a *Argument, h Fact, …)` receiving
  the structure hypothesis and then, optionally, the body's own leading
  ∀-binders as Term / typed parameters in the body's order (`func(a
  *Argument, group Fact, x, y, z Term)`) — the components are bound
  under their own names, so claim texts spell `op(x, e)` as the
  statement does — or one Action run with the hypothesis resident. A
  structure over TWO carriers may declare one symbol on both operations
  (`Symbols: mul ↦ *, mul' ↦ *`): the parser reads each `*` at its own
  operands, and the definition refuses one symbol only on two
  components of ONE type; a homomorphism between two records reads its
  symbols off the records' fields the same way. `S.Axiom(body)` is the law
  whose body is one conjunct of the definition, proved by
  `Unfold` of the structure alone (the conjunct is then resident and the leaf
  closes on contact; zero keys). A predicate DEFINITION that is not a
  structure has the same door on its Define entry: `subgroup(G, h)`
  reads a set against a group record, and
  `SubgroupDef.Entry().Conjunct("G.one ∈ h")` states `∀<the left side's
  variables>. subgroup(G, h) ⇒ G.one ∈ h` (S.Statement's
  rendering) and proves it by the same `Unfold`, the definition its dep
  by construction; it refuses a structure's entry (its conjuncts are its
  Axioms) and an entry that is not a direct predicate definition. Any
  other law over such a predicate is `<Def>.Entry().Law(body, proof)`:
  the same statement, the definition its dep, proved by any of
  `S.Law`'s closure forms — so a law read through a conjunct binds
  only the hypothesis the reading is taken at,
  `SubmoduleDef.Entry().Law("M.zero ∈ N", func(a *Argument, sub Fact)
  { a.Show(…, By(group.SubgroupOne.Read(SubmoduleSubgroup.Read(sub))))
  })`, where a `family.Theorem` would restate the left side and bind
  R, M and N the body never reads. It refuses what Conjunct refuses (a
  structure states its laws through its own `S.Law`). The door serves
  a predicate the chapter reads as it reads a structure — a sub-object
  such as a subgroup, a submodule or an ideal; a theorem whose
  antecedent applies a defined relation to its binders, `∀x y:real. x
  < y ⇒ …`, keeps its statement written out. Emit renders such a
  section as `family.Theorem`; the door is restated at landing. A structure's axioms are its first
  laws; a later law cites them at the hypothesis — `By(Comm, LeftIdentity,
  monoid)` — exactly as a consumer cites them at an INSTANCE, the
  carrier chapter's theorem `comm_monoid(real_add, &0)`: the apply rung
  reads the components off the goal and the rest off the instance
  (two instances resident are told apart by the goal's operation; a
  miss names the unpinned binder and says `Where`). An ⇔-shaped
  conclusion is read as either of its Horn clauses: the goal matched
  against one side, the other side pinned from and discharged by the
  context — a cancellation law `x + y = x + z ⇔ y = z` closes `y = z`
  with the sum resident, and `x + y = x + z` with the equation
  resident, keyless; the exact ⇔ is tried first, and a side the
  context lacks is a named miss. An equation goal is also matched the
  other way round — the goal `b = a` against a head (or ⇔ side) stating
  `a = b`, closed by one `Symm` before the modus ponens — so a law's
  orientation never decides whether it applies. An antecedent (or an
  ⇔'s other side) the context does not hold is a goal of its own,
  closed one apply shallower — by a resident fact or a cited law's
  stated form applied with ITS antecedents held, two applies deep and
  no further (the `by` row, "An antecedent is a goal of its own");
  what lies further off is a Have or a reading.
- `S.Intro(steps…)` / `S.Parts(fact)` — a structure fact built and read
  WHOLE inside a proof. `S.Intro` proves the predicate at the goal's
  components: the goal alone is opened by the definition,
  `Simp(Fwd(<definition>))` (Unfold would open the resident structure
  facts too and kill their handles), then one `Case` per conjunct of the
  definition in its order, as an instance proves them, or the actions
  given, run on the opened conjunction as a whole —
  `real_closed_field.RealClosedField.Intro(Case(…, By(ordered)), Case(…))`,
  `first_order.QuantifierFreeEquivalent.Intro(Simp(Fwd(WellFormedDef), …),
  By(Normalized, …))`; a structure `StructureOf` names has no definition
  entry and takes `Unfold`. `S.Parts(fact)` is every axiom of the
  structure (its `S.Axiom` entries) read at the fact, one premise group a
  `By` list takes in place of the readings one by one:
  `By(Normalized, QuantifierFreeEquivalent.Parts(eq))` for the four
  `Equivalent….Read(eq)`; a reading that needs only some parts names
  those.
- `family.Instance(S, "<pred>(<concrete components>)", cases…)` — the
  INSTANCE door, in a chapter of the carrier: the predicate unfolded, one
  Case per conjunct of the definition in its order, each closed by the
  carrier's own law or the sub-structure instance in hand (a carrier
  builds bottom-up: the monoid, the group citing it, the ring citing
  both). A PARAMETRIC instance states the predicate under a ∀-prefix
  (`"∀n:num. metric_space({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩)"`,
  `"∀X:set(A). is_topology({t:set(A) | t ⊆ X})"`): the prefix is bound
  as the section's binders under their own names, so a Case's texts
  spell `n` and a vector verb anchors at it, and the body is the door's
  own. What the door does not hand a Case is the parameter as a Go
  VALUE — a case that cites a law `.At(M, d, …)` keeps the Theorem
  form with typed binders (metric_space.MetricTopology). A consumer cites a law at the instance by name —
  `By(Normalized, comm_monoid.Monoidal, AddMonoid)`, `Normalized`
  saying the leaf closes under normalization alone and records no key.
  Inheritance is the constitution's rule 4: the sub-structure at a
  hypothesis is an Axiom (`comm_ring.AddGroupOn`), and a consumer holding
  only the ring's instance reaches a sub-structure's through it
  (`By(comm_ring.AddGroupOn, CommRing)`). Emit renders a
  law's proof as any member's; the headline is restated as
  `S.Law(body, …)` at landing. The live chapters:
  `proofs/algebra/group/comm_monoid` (with the bridge to the fold
  mechanism's `monoidal_op`), `algebra/group/abelian_group`,
  `algebra/ring/comm_ring`; the instances: `real/real_ring` and
  `int_num/int_real_lift`.
- `family.StructureOf("<pred>", "<name>:<type>", …)` — the same door
  with the components spelled by the author instead of read off a
  Define (`iterate/monoidal`: `family.StructureOf("monoidal_op",
  "op:(B → B → B)")`); no definition entry is declared as the laws'
  dep. `S.Law` then takes EITHER closure form: `func(a
  *Argument, h Fact, …)` as above, or — for a proof that BUILDS at a
  component (grounds a cite at the operation, applies it under a λ) —
  the components named first, typed, `func(a *Argument, op
  *Arrow2[B, B, B], mon Fact, …)`, which is the statement's plain
  Theorem closure and is bound as one. The door fixes the carrier's
  LETTER (the structure's component type as spelled once), so a body
  chooses its other letters around it: `iterate/monoidal`'s thirty laws
  went through it with the carrier at the chapter's `B` throughout —
  the seven doubly-indexed members that had moved the carrier to `C`
  took their second index at `C` instead, which moved their own keys
  (the corpus key reads type-variable names) — and the two members that had stated the structure binder
  after other binders (`Delta`, `Related`) took it first, which moved
  no key (binder order is normalized) but re-slotted their typed `At`.

- `S.AtUniverse(S_on, bridge, inUniv)` / `View.Law(body, onLaw)` is the
  universe-view door for separate components: `S_on` takes the carrier
  first and `S`'s components after it, and the bridge states
  `S(comps) ⇔ S_on(𝕌, comps)`. For a record structure,
  use `S.AtUniverseRecord(S_on, bridge, recordAtUniverse, universe…)`.
  For example, `Group.AtUniverseRecord(GroupOn, GroupOnUniverse,
  "restrict_group(G, 𝕌)", set_basic.InUniv, set_order.SubsetUniv)` reads
  the bridge `group(G) ⇔ group_on(restrict_group(G, 𝕌))`. The whole
  predicate uses the record's operations on the whole type; its stored
  carrier imposes no condition. A law is proved once on the carrier,
  `GroupOn.Law(Statement{Binders: "∀x y:A.", Hypotheses: []string{"x ∈ G.carrier", "y ∈ G.carrier"}, Conclusion: "…"}, proof)`.
  Its unguarded whole-type member is
  `GroupAtUniverse.Law(body, onLaw)`. The door reads the carrier law at
  the restricted record and discharges the guards with the supplied
  universe laws. Its dependencies are the whole definition, carrier law,
  bridge, and the universe laws its guards require.
  A carrier law's PROOF holds its guards as one Fact (the closure
  parameter after the binders; the rung splits the conjunction), and a
  term the argument forms — `inv(x)`, `x * y` — gets its membership from
  the closure axioms NAMED beside the law, `By(AssocOn, group, members,
  InvIn, MulIn)`: the rung takes a named premise's stated form as the
  head of an apply inside an antecedent, and an apply that descends —
  each antecedent it leaves to close a smaller term, `x ∈ c` for
  `inv(x) ∈ c` — spends none of its depth, so `x * inv(x) ∈ c` closes
  two closures deep with no Have and no key (§"The conditioning stage of
  `by`", the apply rung). A closure law of ANOTHER structure is named
  with that structure's fact: `By(double,
  group.IdempotentIsOneOn.Read(additive), module, member, SmulIn)` in
  `module.ZeroSmul` — with `module` resident but unnamed, the rung does
  not read the module's closure law inside the antecedent. A guarded law is a Simp rule where its guards
  are resident, as facts or as conjuncts of one — the Law door hands a
  body's several guards as ONE conjunction, and the discharge reads a
  conjunct out of it (the `simp` row of §"Tactic entries") — or follow
  from closure rules in the set, `Simp(Fwd(InvMulCancelLeftOn),
  Fwd(InvIn))`, route (d) of the side-condition discharge; a rule
  stated at another type's structure — the group on the vectors inside
  a module — is passed as its reading,
  `Simp(Fwd(group.LeftIdentityOn.Read(additive)))`: a structure law's
  components are the instance's, which a type adaptation alone does
  not supply (`module.SmulZero`). A
  membership that follows through an INCLUSION (`x ∈ h` and `h ⊆ c`)
  is neither a closure nor a guard: the rung reads it with
  `set_basic.SubsetDef` named beside the inclusion, whatever h's shape
  (`x ∈ s₁ ∪ s₂` and `s₁ ∪ s₂ ⊆ c` alike), as one apply of the
  definition read through its ⇔ — an apply like any other, so it
  counts against the rung's depth: where the membership is the guard
  of a ∀-fact whose apply already spends it (not a descent, its
  conclusion no larger than the guard), it is a third apply and the
  rung declines, and the membership is had as a Have from the unfolded
  inclusion (`inclusion := a.Unfolded(hInC, set_basic.SubsetDef)`, then
  `By(inclusion, member)`). A proof under a `group_on(G)` hypothesis
  that UNFOLDS `group_on` — to show a second group on a set, the
  quotient or a subgroup's — opens the resident hypothesis as well, and
  every handle on it dies: the conjuncts are had FIRST, as facts stated
  word for word, and the unfolding then closes each on contact
  (`quotient_group.QuotientGroupOn`, `group.SubgroupGroupOn`; the same
  for an isomorphism unfolding `group_homomorphism` under one,
  `quotient_group.FirstIsomorphism`). A coset equation is read INSIDE
  the carrier: both sides lie in it, so `set_basic.ExtensionWithin` at
  the carrier and the two inclusions, cited at its three witnesses,
  reads the equation one point of the carrier at a time
  (`quotient_group.LeftCosetMulOn`). A predicate over a structure's
  subsets or maps takes the CARRIER — `subgroup(G, h)`,
  `normal_subgroup(G, h)`, `left_cosets(c, h)`, `group_kernel(c, f)`,
  `ring_ideal(R, I)`, a homomorphism's `(G, H, f)` or `(R, S, f)` — and a whole-type instance puts `𝕌`
  in the records' carrier fields.

- Typed structure facts and members (prover/proof/structure_fact.go,
  member.go; the carrier phantoms are ext/on). For every structure with
  one or two carriers — a set component, or a carrier structure
  record whose `carrier` field is one — the generated wrapper file of its family
  declares a structure phantom and the alias of its facts at any
  carriers, `GroupStructure` / `GroupFact[Car]`
  (= `proof.StructureFact[…, Car]`), `ModuleStructure` /
  `ModuleFact[Car0, Car1]` (= `proof.StructureFact2`). Both are named
  by the structure's stem, the definition's name less the `On` or `In`
  its constant ends in (`group_on` → `Group`, `module_on` → `Module`;
  `continuous_map` keeps `ContinuousMap`), and the fact is spelled at
  its carriers everywhere: a law's closure binds the components under
  the definition's own names, `GroupFact[on.G]`,
  `ModuleFact[on.R, on.M]`; a bundle binder names its carrier after
  itself (`R comm_ring.CommRingFact[on.R]` for `∀R:comm_ring_on(A).`,
  `L field.FieldFact[on.L]` for the field chapters'
  `∀L:field_on(A).`). A carrier or bundle binder under a letter package
  on lacks binds an untyped `Fact` until the letter is added there, one
  type; no generated file reads the letters.
  A law's closure may bind its hypothesis as the typed fact and the
  points a run of binders guards as members of their carriers:

  ```go
  GroupOn.Law(Statement{
      Binders: "∀x y:A.",
      Hypotheses: []string{
          "x ∈ G.carrier",
          "y ∈ G.carrier",
      },
      Conclusion: "G.inv(x) * (x * y) = y",
  },
      func(a *Argument, group GroupFact[on.G], x, y *Member[A, on.G]) {
          … By(AssocOn, group, x, y, InvIn) … By(LeftIdentityOn, group, y) …
  ModuleOn.Law(Statement{
      Binders:    "∀u:B.",
      Hypotheses: []string{"u ∈ M.carrier"},
      Conclusion: "R.zero • u = M.zero",
  },
      func(a *Argument, module ModuleFact[on.R, on.M], u *Member[B, on.M]) {
          ring := RingOn.Read(module)          // comm_ring.CommRingFact[on.R], no Have
          … group.IdempotentIsOneOn.Read(AddGroupOn.Read(module)) …
  ```

  The run's guard — the antecedent after the members' binders — binds
  no parameter: it is assumed, every conjunct must be the membership of
  one member (a guard with any other conjunct stays a `Fact`
  parameter, refused at the plan), and each member's carrier phantom
  must name the set its conjunct states, checked at binding through the
  block's surface names (`on.G` is the record G, whose carrier is `G.carrier`; `on.M` under
  `module_on(R, M)` is the record M, whose carrier is `M.carrier`). The
  typed fact's predicate is checked at the plan and its carriers at
  binding. A member stands, in a `By` list, for its evidence — the
  guard, which members of one run share and the list carries once — so
  `By(AssocOn, group, x, y, InvIn)` is `By(AssocOn, group, members,
  InvIn)` premise for premise, and naming the points a cite reads is
  the spelling. A law of a structure with a phantom has a typed `Read`:
  the structure and the carriers are inferred from the instance
  (`proof.Instance`), so a reading at a typed fact takes members of its
  carriers alone; a projection law — its body another phantom
  structure's fact at the law's carriers — reads as that structure's
  typed fact (`AddGroupOn.Read(module)` is a `group.GroupFact[on.M]`);
  a closure law whose only antecedent is its points' memberships reads,
  at its points, as the member it concludes
  (`group.MulIn.Read(additive).At(fx, gx)`, the member F(x) + G(x), its
  evidence the points' and the reading's) — at a typed fact, a resident
  fact, an instance entry, or a reading of any of these
  (`module.SmulIn.Read(HomSource.Read(hom)).At(cm, um)` under the
  homomorphism's fact), the member named from what the reading states
  before the proof runs: the law's statement at what its instance
  says, through the chain. A point a body shows in a
  carrier by hand is paired with `a.MemberOf[on.M](x, fact)`, which
  checks the term and the set. Every untyped instance — a Fact, a
  handle, an instance entry, a reading of a structure without a phantom
  — still reads, at `proof.AnyStructure` and `on.Any`, and takes the
  members `proof.MemberOf` pairs; a typed member does not pass to such a
  reading, nor a member of one carrier to a reading at another, nor a
  law to a fact of another structure — each a compile error
  (`TestTypedReading_CompileWalls`, beside the module family). Measured
  limits: a closure law with no points (`OneIn`, `ZeroIn`) reads as a
  plain reading, no member, since nothing names its element type; a
  closure law with any other antecedent (`ModuleSumIn`, finiteness)
  reads as a plain reading, since its member would hide premises; a
  reading at a reading is not resident, so a `Simp` rule guarded by its
  membership names that membership as a rule (`Simp(Fwd(LeftIdentityOn.Read(monoid)),
  Fwd(zeroIn))`, `module.ZeroSmul`); and a closure member listed beside
  a wide ∀-premise can move the conditioning stage's grounding guess off
  the ∀ (`module.ModuleSumNeg` keeps its Have for that membership). A
  structure with no carrier or more than two has no phantom, and its
  laws read untyped.

## The math layer: how a body is written

A proof body is written at the MATH LAYER: **facts are Go
values, and every deduction close names the premises it uses.** Read
this section before the API cheat sheet — it decides which primitives
you reach for at all.

**The three pieces** (`prover/proof/fact.go`, `prover/proof/derive.go`;
the constitution's §"The math layer: facts as values"):

| Piece | What it is |
|---|---|
| `Fact` (the TYPE) | a fact VALUE — lazy, passable, no goal-state effect until consumed. Produced by the `Argument` verbs (`a.Have`, `a.Obtain`, `a.Assume`, `a.SupposeNot`, `a.Hyp`), by `At` / `Where` / `Read`, or by `MakeFact(cert)`. What a cite verb takes — `Cite`, `At`, `Where`, `Scaled`, a rule's `Fwd` / `Rev` — is a `CiteTarget`, any value that reads as a `Fact`: a `Fact`, an entry var, a typed instance (`ctx.AtTypes`), a section node, a handle; the compiler refuses anything else. The VERB that acts on the goal now is `Cite` — a different thing. |
| `At(dep, w…)` / `f.At(w…)` | the ground instance AS A VALUE — "LessEqTrans at (a, b, c)". Grounding is function application, not a step. The verbs that act on a fact as a hypothesis take `f.At(w…)` of a fact in hand too, and ground it first (§"A fact in hand", below the verb table). |
| `Where(dep, "R", t)` / `f.Where("R", t)` | ONE stated binder pinned by name — Lean's `apply law (R := r)` — for a binder the goal cannot determine (a relation, a predicate). The consuming `By` applies the law with the remaining binders read off the goal and the context, its antecedents resident, and closes keylessly. A named fact must apply; it is never handed to the closer. |
| `By(premises…)` / `ByArith(premises…)` | the close: bring exactly these premises to bear, clear every other hyp, refute (or run gated arith). Premises are `Fact` values or entry vars. `ByArith()` with no premise closes a fact of arithmetic alone; `ByArith(ring)` with a resident `comm_ring`/`field` fact closes a ring identity at it, and bare over a carrier whose instance is installed (ℂ). `Scaled(c, fact)` adds the equation's congruence `c·l = c·r` beside it (Lean's `linear_combination c * h`). |
| `ac.New(assoc, sym).Eq(lhs, rhs)` | an AC-rearrangement equation AS A PREMISE — "these are the same factors in a different order". The equation appears ONCE, as the two terms. |

**A premise may carry its own proof — but only from a solver kit.**
`ac.New(assoc, sym).Eq(lhs, rhs)` proves itself when the `By` consumes
it (the AC rearrangement is computed from the two terms). It reads as a
premise everywhere it is used; its Go type is the kit's own, adopted
through the `SelfProvingPremise` outlet — kits sit below `proof` and
cannot name its types. That shape is reserved for `prover/solver/**` kits, whose
every emitted step cites what the consumer passed. A hand-built one is
what the constitution's §"Premise discipline" rules out: an intermediate
fact that needs a proof of its own is `a.Have(label, claim, By(…))`, the
claim and its justification both on the page.

**Why `By` and not a bare refute.** `By` clears the ambient context
first, so a premise list is a real claim about what the argument
needs — refute-poisoning by a wide-∀ leftover cannot happen, and no
`Clear` bookkeeping exists to get wrong. The list is also the checked
form of the sentence you would write in prose: "by A, B and C".

Read that in the diagnostic direction too, because the failure lies to
you: a bare `auto`/`CnfRefute()` timing out on a leaf that carries a
resident wide-∀ hypothesis — and a ∀-PREDICATE hypothesis (the closure
form of any inductively defined constant) poisons ALONE, no ~6-hyp
accumulation needed — prints an engine-ceiling diagnostic and is
usually a missing premise list: the same leaf that fails `auto` at
budget closes at once under `By` with the ground premises named. Try
the premise-list spelling BEFORE reporting a `[wall-candidate]` or a
refuter-budget note in your verdict (Playbook Lesson 4 has the
mechanism).

**The deduction block** — `Derive(func(a *Argument) { … })`:

```go
return Derive(func(a *Argument) {
    bound := a.Hyp("∀n:num. A₀ * n ≤ B₀ * n + C₀")   // name a resident premise
    notLe := a.SupposeNot()                           // suppose not
    d0, gapEq := a.Obtain("∃d:num. A₀ = B₀ + suc(d)", // obtain d with …
        By(notLe, At(NotLessEq, A, B),
                  At(LessThanExists, A, B)))
    cancel := a.Have("cancel the common B·suc C",     // we have …, because …
        "suc(d₀) * suc(C₀) ≤ C₀",
        By(gapEq, bound.At(sC), At(nat_arith.RightAddDistrib, B, sD, sC)))
    a.Show("squeeze: suc C ≤ C is C < C — irreflexivity closes",
        By(cancel, At(LessEqTrans, sC, gap, C), LessThanIrrefl))
})
```

The Go variable graph IS the proof DAG: `cancel` flows into the
premise list that uses it. Contracts (loud, named panics): a `Have`'s
proof must close its claim; every non-terminal verb leaves exactly one
unsolved leaf; the block must close its goal.

**The verb set** — a verb exists exactly where a paper proof has a
word for the move:

| Verb | Paper phrase | Returns |
|---|---|---|
| `a.Fix()` / `a.Fix("u")` | "let n be arbitrary" (∀-intro); the optional name makes `u` the claim-text spelling — the reach when the goal's own binder name is already live (an induction principle's `∀x s.` beside the section's `s`) | the fixed term |
| `a.FixAs[φ]()` / `a.FixAs[φ]("u")` | the same, asserting the binder's type — typed dialect's Fix (mismatch panics AT the Fix, not downstream) | the fixed term as `*Expr[φ]` |
| `a.ForEach(func(x *Expr[φ]) Action)` | "for every x, this" — an ACTION (placed where a `By` goes: a `Have`'s proof, a `Show`) that fixes the goal's leading ∀ as `FixAs[φ]` would, hands the variable to the closure and runs the one Action it returns, which must close the leaf. The one-line ∀-lift: `Have("…", "∀n. a(n) ≤ B", a.ForEach(func(n *Expr[Nat]) Action { return By(bounded.At(n), AbsBounds.At(a.Apply(n), B)) }))` records the strip and the close and nothing else, where the bare `By(bounded, AbsBounds)` on the ∀-goal closes too but has the conditioning stage ground the wide premises by search and persists a PLAN row. A body that must parse a term against the variable, name an antecedent, or state a fact on the way is a `Derive`; an antecedent the close needs is S2's to move in, which S2 does after the premises are installed. So on a guarded ∀, `∀v. v ∈ S ⇒ …`, a cited instance that `v ∈ S` guards (`law.At(v)`) is installed with that guard not supplied, as its clause, and unless its conclusion is the goal itself the close goes through S4 and the refuter and records a PLAN row and a key; the `Derive` that assumes `v ∈ S` and lists it ahead of the instance has the guard discharged at the install. A method, not a function, because a generic function cannot be aliased into a family package (typed.go). | the Action |
| `a.VecFixAs[Elem, D]()` / `("x")` | FixAs for a vector binder: the dug binder adopted as a D-dimensional vector ANCHORED to the dimension binders in scope — the one verb for what was `Fix()` followed by `VecAs[Elem, D]("x")`, the goal's own name spelled twice | `*Vec[Elem, D]` |
| `a.VecAs[Elem, D](text)` | a vector term at dimension phantom D, ANCHORED to the binders in scope (§"Vectors and matrices: the dimension rides the type, not the statement"); `.Dim()` is the term a cite writes | `*Vec[Elem, D]` |
| `a.VecAt[Elem](dim, text)` | a vector term ANCHORED at the given dimension term — a Let, a literal, `suc(m)`, a degree: the dimension no letter spells; `.Dim()` is that term, and two such vectors are tied at the cite rather than at compile time (`a.MatAt[Elem](rows, cols, text)` at a matrix, `a.VecFunAt[Elem](source, target, text)` at a map between two vector spaces) | `*Vec[Elem, SomeDim]` |
| `a.VecFunAs[Elem, Source, Target](text)` | a map between two vector spaces, a term of type `(num → Elem) → num → Elem`, at the dimension phantom it is read on and the one its values are read at, ANCHORED to the binders in scope; `.Source()` and `.Target()` are the terms a cite writes, and `f.Apply(x)` is the image of a `*Vec[Elem, Source]` as a `*Vec[Elem, Target]` anchored at the target (`a.VecFunFixAs[Elem, Source, Target]()` digs the goal's leading binder as one) | `*VecFun[Elem, Source, Target]` |
| `a.BigOpAs[I, T](text)` | a big-operator term — `Σ_{i<m} …` at ℝ, the fold at vectors, anything a chapter declared as one (`DefEntry.BigOp`) — read with its parts: the value is the term, `.Range()` its index set, `.Summand()` its body as the `λi. …` a sum law's slot takes. One spelling read three ways, so the λ handed to `real_sum.Monotone.At(range, f, g)` / `ScalarRight.At(c, f, range)` / `NormIterateLe.At(n, range, F)` is derived from the Σ the claim shows, never restated beside it. A head the scope declares no big operator at panics naming it (prover/proof/bigop.go) | `*BigOp[I, T]` |
| `proof.Inhabit(v, fact)` | pair an anchored vector with the resident fact naming its dimension and itself; the generated `At` of a member with that membership among its antecedents takes the result and bundles the evidence | `*Inhabited[Elem, D]` (embeds the Vec: `.Vec`, `.Evidence()`) |
| `proof.InhabitFrom(p, fact)` | the same pairing with the dimension READ OFF the fact — for a vector held only through its membership (`vec⟨suc(polynomial_degree(zero, p))⟩(zero, p)`), restating no dimension; `proof.InhabitMatFrom(P, fact)` at a matrix | `*Inhabited[Elem, SomeDim]` |
| `proof.MemberOf(x, fact)` | pair a point with the resident fact `x ∈ s` about it, as the fact was bound (a ground instance `f.At(w…)` or a law read at a fact pairs through `a.MemberOf`, which grounds it); a structure law's generated `Read(…).At` takes the result where the reading's antecedent holds the point's membership in a component set (`x ∈ M` under `metric_space(M, d)`) or a set field of a component record (`u ∈ M.carrier` under `module_on(R, M)`) and bundles the evidence; its carrier is `on.Any`, what a reading at an untyped instance takes | `*Member[Elem, on.Any]` (embeds the Expr: `.Evidence()`, `.AsFact()`) |
| `a.MemberOf[on.M](x, fact)` | the same pairing in a named carrier — the set the binder resolves to, or that record's `carrier` field — checked; what a reading at a typed structure fact takes (§"The structure doors", typed structure facts). The fact is any fact in hand: a resident one is read as it stands (recording nothing, so it may sit in a branch verb's argument list), and a ground instance or a law read at a fact is grounded on the spine first, the member's evidence then the resident instance — `b.MemberOf[on.C](q.Apply(j), qIn.At(j))`, `a.MemberOf[on.R](t, comm_ring.OneIn.Read(ring))`. At `on.Any` no carrier is checked: the pairing is the free `MemberOf`'s, from any fact in hand — `a.MemberOf[on.Any](x, qIn.At(j))` is how a ground instance or a reading pairs for a law read at an untyped instance | `*Member[Elem, on.M]` |
| `a.Assume()` | "assume H" (⇒-intro) | H as a `Fact` |
| `a.SupposeNot()` | "suppose not" | ¬goal as a `Fact` |
| `a.Obtain(label, claim, By(…))` / `d.Obtain2` … `d.Obtain5` | "obtain d such that P(d)" (∃-elim, proving the ∃; the claim a string, or a `Statement` in parts as a Have's). The one Skolemization opens the claim's whole ∃-prefix, so the verb is the prefix's length, one to five: `Obtain2` on `∃x y z. …` is refused, the refusal naming the verb that opens it (`expected 2 minted witness(es), found 3 — a leading ∃-prefix opens whole: Obtain3 opens this one`), and the same holds for the Unpack verbs; a prefix longer than five has no verb, and its further witnesses are stated under an inner ∃ and opened in a second step. `Named("r₀")` in the proof list — the verbs' one variadic slot, not a step — gives the witness its surface spelling, as Unpack's trailing names do: strict, one per witness, all or none; without it the witness is spelled by the claim's binder where that name is free and by the engine's subscripted form otherwise, which the file cannot show | witness term(s) + the instance `Fact` |
| `a.Unpack(f)` / `d.Unpack2` … `d.Unpack5` | "write f as P(w) for some w" (∃-elim on a fact ALREADY established — a premise, a branch hyp, an earlier Have, or a fact in hand grounded first: `a.Unpack2As[A, A](fractions.At(X), "r", "u")` with `fractions : ∀X. X ∈ L ⇒ ∃r u. …` resident and `X ∈ L` beside it, a typed reading's `law.Read(F).At(…)` with its members). Records one `StripQuantAt` at the hypothesis it resolved: the conclusion's ∀-prefix and every other ∃-hyp stay as they are. The strip opens the fact's whole leading ∃-prefix at once, and the verb's count must equal it: Unpack3 opens `∃a b c. …`, never the first three of `∃a b c d e. …`, which Unpack5 opens (structure_sheaf's common neighbourhood of two sections, weil_curve's presentation through `Obtain5As`). No verb opens a prefix of six or more: such a fact is stated with its further ∃s nested (`∃a b c d e. … ∧ (∃f g. …)`, opened by Unpack5 and then Unpack2 on a conjunct). A membership in a set-builder whose reading is an ∃ is opened through it (`x ∈ {y | ∃z. …}`, the three-part `x ∈ {f(k) | k | …}`; §"Structural moves at a hypothesis"). The witness is spelled by the fact's own binder unless the author names it: `a.Unpack(f, "a")` / `a.Unpack2(f, "m", "b")` bind the given names as the witnesses' surface spellings, as `Fix("u")` does — strict (a name that already means something panics), all or none, and the machine layer untouched (same mint, same instance, same keys). The road where two facts share a binder: two memberships of one span both read `∃c`, and `a.Unpack(a.Unfolded(a.Unfolded(uIn, set_basic.SetMemberDef), VecSpanDef), "a")` with its sibling at `"b"` spells the two coefficient sequences `a` and `b` (vec_space.SpanSubspace). NOT `Obtain` with a renamed claim: Obtain proves its claim, and a claim α-equal to a resident hypothesis is refused by the assert, whose refusal says so. A fact headed by ∃! is opened at its definition: `c, only := a.Unpack(unique)` on `∃!x. P(x)` hands over the witness with `∀y. P(y) ⇔ c = y`; no proof unfolds ∃! itself — a closer reads a `∃!` premise through normalization (`By(unique)` gives the plain ∃ and the uniqueness); an ∃! to be proved first is stated as a `Have` and unpacked | witness term(s) + the instance `Fact` |
| `a.ObtainChosen(label, claim, premises…)` | "obtain THE d" — the witness is the Hilbert-choice term `εd. P(d)` instead of a fresh one, for an argument that must continue with the canonical choice; the ∃ is proved from the premises under an implicit `HilbertDenoted` shaping and never becomes a resident fact | the ε-term + `P(εd. P(d))` as a `Fact` |
| `a.ObtainAs[T](label, claim, By(…))` / `a.Obtain2As[T, U]` … `a.Obtain5As[T, U, V, W, X]` / `a.UnpackAs[T](f)` / `a.Unpack2As[T, U]` … `a.Unpack5As[T, U, V, W, X]` | the same ten verbs with the witness asserted at its type — the thin `verb + ext.As[T]` composition (constitution §"The typed surface"), so a typed `.At(…)` takes the witness without a cast at the site; the Unpack pair takes the untyped verbs' optional names (`a.UnpackAs[Fun[Nat, A]](f, "a")`) | typed witness(es) + the instance `Fact` |
| `a.Calc(kit, from, legs…)` / `a.CalcOrder` / `a.CalcLeibniz` | a relation chain run as a deduction item | the chained `Fact` |
| `a.Have(label, claim, By(…))` | "we have P, because …" — the claim a string, or where P has a premise and its string runs past 100 columns from its line's indentation a `Statement{Binders, Hypotheses, Conclusion}` in parts, as the constructors take a statement (§"The constructors") | P as a `Fact` |
| `a.Let(name, term)` / `a.Denote(name, term)` | "let w := ⟨term⟩" — the definition: its equation joins the hypotheses, the term becomes the name wherever it occurs, and the goal keeps its form — and the abbreviation of a term the goal carries; neither has a proof obligation (§"Denote — the abbreviation family", an Action entry of the cheat sheet, has both). The term is a `TermLike`: `a.Term(text)`, a typed value, a core term | the defining equation as a `Fact` |
| `a.LetAs[φ](name, text)` | "let w:φ := ⟨text⟩" — Let with the text read at φ, as `TermAs` reads one, and the name returned as its typed handle beside the equation: `tower, towerDef := a.LetAs[Set[Set[A]]]("tower", "{t:set(A) | set_tower(f, t)}")`, where the handle feeds the typed slots and claim texts spell `tower`. The one verb for a Let followed by a `TermAs` of its own name | the name as `*Expr[φ]` + the defining equation as a `Fact` |
| `a.Conjuncts(f, labels…)` | "from A ∧ B ∧ …, A; B; …" — a conjunctive fact split into one Fact per conjunct: a resident one in place, as the hypothesis stands at the leaf (a Let or a rewrite since the fact was taken respelled it, and the parts spell the current text), a fact in hand (`f.At(w…)`, a typed reading's `.At(…)`) or a named one materialized first, as the context verbs take it — no Have restating the conjunction to split it; one label each in the conjunction's order; each part is a Have closed against the fact by normalization (∧-elimination on contact, engine-shaped so the S7 audit does not advise it), except a part the leaf already holds — a hypothesis α-equal to it, resident before the split or installed by an earlier part — whose `Fact` names that hypothesis, nothing asserted: a fact that restates some of the context (a member's statement taken where its parts are already split) is split for the rest, every label given, and the parts that were already held come back as the context's own. A part that is the goal's conclusion is refused (close with `By(f)`). A membership in a set-builder of a conjunction is split through its predicate — `a.Conjuncts(fIn, "…", "…", "…")` on `f ∈ {g | P(g) ∧ Q(g) ∧ R(g)}` gives `P(f)`, `Q(f)`, `R(f)`, keyless (§"Structural moves at a hypothesis"). Session twin: `split_conj {hyp_index}` (the structural table), which `emit-section` renders back as this verb | one `Fact` per conjunct |
| `a.Take(t)` | "take B := t" (∃-intro); on a goal `∃!x. P(x)`, ∃!-intro: the goal becomes `P(t) ∧ (∀y. P(y) ⇒ y = t)` | — |
| `a.Hyp(content)` | name an already-resident hyp that no Case handed you — an assumed premise the signature did not bind, or a branch hyp in a Case that is not a `Given`. **`content` may be a TERM**, so pass the discriminant itself rather than re-spelling it as text | that hyp as a `Fact` |
| `a.Unfolded(h, CDef)` | "h, read by the definition of c" — the Fact-level face of `Unfold`: the resident fact opened at the constant `CDef` defines and returned as ONE new resident Fact (a conjunction stays whole), the folded fact, the goal and every other hypothesis untouched. Records exactly the hand-written idiom `Have(<the unfolded statement>, Unfold(CDef))` — the claim is COMPUTED by the def-expand walker on the fact's content, so no text restates what the engine holds. `near := a.Unfolded(converges, real_sequences.RealConvergesToDef)`; `m, c, pSum := a.Unpack2(a.Unfolded(isPolynomial, real_polynomial.PolynomialFunctionDef))`. Panics on an inductively-minted constant, a fact the constant does not occur in, a definition the walker declines. Session twin: `def_expand {const, hyp_index}` (the `def_expand` entry), rendered back as this verb | the unfolded fact as a `Fact` |
| `a.Simplified(h, rules…)` | "h, simplified" — the Fact-level face of `h.Simp(rules…)`: a fact not yet resident (a law read at an instance, ground it first with `.At(w…)`; a named lemma; a ground instance `f.At(w…)` of a resident fact, grounded on the spine; a typed reading's `.At(…)` with its members) is installed as the context verbs install one, then rewritten in place by the rules, and returned as the resident Fact it becomes. The statement is the engine's, so no text restates it: a law grounded at a packed record value, a definition among its terms unfolded, states the parts the record was packed from — `free := a.Simplified(free_module.FreeModuleOn.At(packed, S), Fwd(free_module.FreeModuleRecordDef))` (simplicial_chain.ChainsModule); a projection of a packed value needs no rule, the instance normal form computes it (S5), so with no rules `a.Simplified(h)` installs `h` as handed over: `sums := a.Simplified(module_homomorphism.HomSum.Read(linear))`. Records the install and the rewrite. A rewrite of a captured fact inside a branch is that branch's: a sibling branch reads the fact as it stood at the split and may rewrite it in turn. Panics as `Fact.Simp` does when rules are given and none fires. | the rewritten fact as a `Fact` |
| `a.StepArgs(names…)` | "at cons(h, t): …" — name the constructor's arguments the enclosing induction step introduced, one author name per argument in the constructor's order; the primary recursive argument is the induction variable itself, and its own name is accepted as a no-op. Records nothing. The names are required: an induction step's arguments are engine-minted variables with NO other spelling (not statement binders, in no hypothesis), and a claim text speaks the author's names | the arguments as terms, in order |
| `a.Show(label, By(…))` | "hence G ∎" | — (terminal) |
| `a.Do(actions…)` | **marked escape**: a goal-surface move with no verb yet | — |

**A fact in hand.** A resident Have, the ground instance `f.At(w…)`
of a resident ∀-fact, and a law read at a resident structure fact
(`law.Read(fact)`, its typed `.At(…)` with the members) are facts of
the proof in progress, and every verb that acts on a fact as a
hypothesis takes them alike: `f.Rw()` / `RwRev` / `Subst` /
`CongrArg` / `f.Simp(rules…)`, the splits (`SplitDisj`, `SplitIff`,
`SplitImply`, `DismissLeft/Right`), `a.Unpack*`, `a.Conjuncts`,
`a.Unfolded`, `a.Simplified` and `a.MemberOf`. A law read bare at the
fact (`law.Read(fact)`, no witnesses) or a named fact is installed as
its stated form, one hypothesis, and its guards are discharged as a
ground instance's are (next): `a.Conjuncts(IntegerModule.Read(L))`
splits the conjunction that stood behind the law's `number_field(L)`,
resident as written or as a conjunct of one fact, where
`IntegerModule.At(fieldL)` always did. A ground instance is
grounded on the spine first, exactly as `a.Do(f.At(w…))` grounds it:
one `SpecializeKeep` — the ∀-source stays resident, re-groundable at
other witnesses — and the instance's guards discharged from the facts
listed with it, where they supply them (Lean's `h w ‹A›`): the facts of
the group it is handed in (`GroupPremises`, next), the fact its law is
read at, the evidence of its members, its own ∀-source — a guard clause
stated by one of them as written, up to βη, or as a conjunct of ONE
listed fact. A datum gathered into one Have,
`datum := a.Simplified(GroupPremises(curve, CurveOverItsLine.Read(L).At(…)))`,
supplies every clause it holds, so `GroupPremises(datum, LaurentThroughInverse.Read(L).At(k, tm))`
discharges its `t ∈ L` from the datum exactly as `By(datum, …)` would
have — the one reading for a fact in hand and for a By premise, whose
leaf holds the listed premises alone; the verb then acts on the
instance. An instance already resident is taken as it stands, recording
nothing for the grounding. A guard the context supplies through a fact
the verb was not handed is REFUSED, naming the clause, the resident fact
that states it and the spelling that lists it (`… is guarded by u₀ ∈ s₀,
which the context supplies and the fact in hand does not list: u₀ ∈ s₀ —
stated by the resident fact u₀ ∈ s₀`): a fact standing in the context
supplies a guard once it is named, so the Go value naming it is the edge
the proof shows. A guard nothing supplies stays on the instance, and a
verb that needs the instance's own shape refuses, naming the guard and,
clause by clause, what of it the context does not supply (`… is still guarded by (u₀ ∈ s₀) ∧ R₀(u₀)
… the context does not supply R₀(u₀)`); where an earlier step rewrote
the hypothesis that held a clause — a `Simp` at the hypothesis, an
`Unfold` whose tidy reached it — the refusal names that step and what
the hypothesis became (`u₀ ∈ s₀ stood in the context until step … rewrote it: it became u₀ ∈ t₀`).
State what is missing as a Have first — a guard is discharged by a
listed fact, never assumed. The same note follows a By whose premise
instance stays guarded (`guards the close could not discharge: …`). A By
whose closer is not ByArith reads a guard at its numerals and does no
other arithmetic on it: `0 < 2` is supplied, and `u ≤ u`, `0 ≤ n` or
`x < 3` beside `x + 1 < 3` — anything that names a variable — is not
unless it stands in the context as written. Where the arithmetic closer
decides such a guard under the leaf, the By's failure says so on the
guard's line — the still-guarded line, or the line of a law that fell to
its clause form for it (`arithmetic decides this guard from the leaf …`):
state the guard as a Have closed by ByArith and list it, close the step
with ByArith, or, for a reflexive bound, list the order's reflexivity law
(`nat_order.LessEqRefl`), which the rung applies to the guard. A
typed reading's `.At(…)` brings its members' evidence into context
first, then the instance. Nothing is refuted: the grounding is keyless, so
`a.Do(GroupPremises(uIn, agree.At(u)).Rw())` replaces a Have that
restated `g(u) = f(u)` to rewrite by it, and
`a.Conjuncts(law.Read(F).At(K, aM), …)` one that restated the
conjunction to split it. A NAMED law is not in hand:
`f.Rw()` / `f.Simp(…)` refuse it, naming `Cite` / `Simp(Fwd(dep))`,
and the other verbs install it through Cite's path as before. As a
`By` premise nothing changes: there `f.At(w…)` is grounded inside the
close's own leaf.

**The facts an instance consumes travel with it.** A verb that takes a
fact in hand has no premise list, and a fact that stands to discharge
one of the instance's guards is still a premise of that step.
`GroupPremises(facts…, instance)` is one value — the instance, a `Fact`,
with the facts listed on it; `PremiseGroup` names that value where a
signature spells it — so every verb above takes it as it takes the
instance alone, and so does every fact verb:

```go
large := a.Have("q exceeds one", "1 < q", …)
empty := a.Have("no divisor has negative degree", "∀n:int. n < &0 ⇒ a(n) = &0", …)
parts := a.Conjuncts(GroupPremises(large, empty, RiemannRochNumerator.At(q, g, h, a)), "…", "…")
```

A resident fact materializes as itself and records nothing, so a group
moves no key, and it is the only slot a fact read this way has: written
as a bare `a.Have(…)`, a fact the next step reads is bound to nothing,
deleting it still compiles, and two steps reading one fact show neither
edge. The parts of a `Conjuncts` read the same way are bound and listed
by index, a member by itself (its evidence) or with its membership. A
typed reading's `.At` that returns a group of its own is spliced in as
the instance. A guard the list leaves out is refused, naming the
resident fact that states it (above); the group is not a `By`, and
nothing is cleared. The list is exact the other way too: a fact listed
that discharges no guard of the instance — it has none, or another
listed fact states each one this fact would — is refused, naming it
(`… is listed with facts it does not need …`); of two that state one
guard, the later is named. A guard that reads ⊤ at its numerals (`0 < 2`)
is discharged with no fact listed; a fact that states it, listed, still
states a guard of the instance and is not named. A member listed in a group (a `Member`, an
inhabited vector) stands for its evidence, which travels with it whether
a guard reads it or not, as does the evidence a typed reading's `.At`
attaches; neither is named, and a plain fact that only repeats a
member's evidence is. An instance grounded as a step, and a fact verb on
an instance, take their facts the same way:

```go
a.Do(GroupPremises(h, f.At(w…)))
a.Do(GroupPremises(uIn, agree.At(u)).Rw())
```

**A SPLIT IS TWO SENTENCES, AND EACH BRANCH IS CLAIMED BY NAME.** The
opener states the move and takes no branches; a branch verb then takes
one branch and proves it:

| opener | branches |
|---|---|
| `a.Cases(t)` — "by cases on t" | `a.When` (t resident) / `a.Otherwise` (t's denial resident: ¬t, or p for t = ¬p — the split contracts a leading ¬) |
| `a.Induct(v)` — "by induction on v" | `a.Base` / `a.Step` (its hyp is the IH); on a one-constructor datatype none — see below |
| `a.Iff()` — "both directions" | `a.Forward` (⇒) / `a.Backward` (⇐) |

Which branch a body proves is the VERB, never the position — the same
principle the ⇔ halves established, applied to every split. The two may
be written in either order, a branch claimed twice panics, and a branch
never claimed panics naming it. The opener may be terminal (the
branches close the goal between them) or leave one branch's leaf open
for the deduction to continue on, exactly as before.

**A one-constructor datatype has one case and no split.** Induction on
`z:complex` (the pair type `complex(x, y)`) produces a single obligation
with no hypothesis — "write z as complex(x, y)". `a.Induct("z")` then
opens no branches: the deduction continues on that case, and
`a.StepArgs("x", "y")` names the constructor's arguments there as in a
step (`complex_field.ComplexEq` inducts on both of its variables in two
lines). The datatype door's `Induction` principle is a member like any
other, in the standard form, so `ByInduction(At(<T>.Induction, P), …)`
cites it as it cites a hand-written principle; the verb is the shorter
way in, reading the principle by the variable's type.

**A branch receives the hypothesis it introduces.** A branch body is a
list of Actions, or ONE closure — `func(b *Argument, h Fact)` where the
branch adds exactly one hypothesis (an `Induct` step's IH, a `Cases`
branch's discriminant or its negation, an `Iff` half's antecedent),
`func(b *Argument, left, right Fact)` or `func(b *Argument, ihs []Fact)`
where an induction step adds one per RECURSIVE constructor argument
(a binary tree's Node grants two, one per subtree, in the constructor's
argument order — the left subtree's first), `func(b *Argument)` where
it adds none:

```go
a.Induct(p)
a.Base("at 0 the exponent contributes nothing", By(…))
a.Step("one more factor regroups across mⁿ", func(b *Argument, ih Fact) {
    regroup := b.Have("carry the spare m₀ across mⁿ", …)
    b.Show("…", By(ih, regroup, At(Exp, m, p)))
})
```

The alternative — `a.Hyp("nat_pow(m₀, n₀ + p₀) = nat_pow(m₀, n₀) * nat_pow(m₀, p₀)")`
— restates a hypothesis the engine just built, in a text that must
match it exactly; for an IH it also forces binding the induction
variable so the text parses. Take the value; `a.Hyp` stays for the hyps
no branch introduced. When an induction step adds several at once —
one per recursive argument of its constructor — take them all, in the
constructor's order: `func(b *Argument, left, right Fact)` for two,
`func(b *Argument, ihs []Fact)` for any number; each is located by
CONTENT (the step's conclusion at that subtree, read off the induction
the branch belongs to), never by its position among the goal's
hypotheses, and a closure that names a different number than the step
grants is refused naming both.

**A step's constructor arguments are named by `a.StepArgs`.** The head
a list induction puts in front, the label and second subtree a `Node`
introduces, are variables the engine minted: not the statement's
binders, so `a.Binder` cannot reach them, and in no hypothesis, so a
claim text cannot spell them under any name — the `h` a printed goal
shows is a printer alias. `b.StepArgs("h", "t")` inside the step body
binds the author's names to them, in the constructor's order (the
primary recursive argument IS the induction variable, so `"t"` there
is a second spelling of `l`, and `"l"` itself is accepted), and returns
them as terms:

```go
a.Induct("l")
a.Step("at cons(h, t): …", func(b *Argument, ih Fact) {
    args := b.StepArgs("h", "t")           // head, tail := args[0], args[1]; t is l itself
    b.Cases(b.Term("h ∈ set_of_list(t)"))  // a split whose guard mentions the head, claimed by name
    …
})
```

The names are for what MENTIONS an argument — a witness, a split's
guard, a `Have` about the head. A step's HYPOTHESES are not what they
are for: a `Node` grants one per subtree, and the branch hands them
over directly — `func(b *Argument, left, right Fact)` — so no
hypothesis is re-spelled by text (`tree.FlattenMirror`). Naming the
arguments and then taking each hypothesis with `b.Hyp("flatten(mirror(r))
= …")` is the same proof with a text that must match what the engine
built; take the value. Binding records nothing, so a step converted to it
keeps its tree and every recorded key. Never declare an engine's
minted name (`ctx.Var("a2", …)`) to reach one of these: that spelling is
read off whichever principle the env serves and is the engine's to
change.

The list form keeps a one-line branch on one line —
`a.Base("at 0 both sides are false", By(Odd, Even))` — and needs no
`Chain`: the slot already sequences.

**While a split is open the ordinary verbs refuse.** Between the opener
and the last branch the deduction has no single line to continue on, so
`a.Have` / `a.Show` / `a.Fix` there panic naming the branches still
unproved — which is the forgotten-branch mistake caught where it is
made. The READS are exempt (`a.Term`, `a.Goal`, `a.Hyp`, the typed term
readers), because Go evaluates a branch's argument list BEFORE the
branch verb runs and the corpus puts reads there:

```go
b.Cases(b.Term("j < m"))
b.When("…", Unfold(AdjointDef), CalcEq(Leg(b.Term("…"), …)))   // read, split open
```

That read is well defined and unchanged by the split: an opener does not
move the spine, so it sees the same goal the expression form's identical
call saw.

**The `Given` / `Derive` values remain** for a Chain-form `Case` body,
which is where the splits with no Argument verb still live
(`SplitDisj` arms, an `AssertStep`'s **after** branch, an
`ExistentialConstDefStep`'s second Case, an `Unless` / `Assuming` SIDE
body). `Given(func(a *Argument, h Fact) { … })` is the same binding the
closure form gets. A hyp-neutral step may sit between the branch and
the `Given` — the binding walks up to the nearest step that introduced
a hypothesis. When unsure, convert and let the build plus strict replay
decide: a wrong guess fails loudly and immediately.

Two shapes that qualify mechanically but should NOT be converted: a
branch whose hypothesis the body never names (consumed ambiently by a
terminal refute / after `SupposeNot`) — `Given` would leave an unused
parameter, and naming it is a close-form change, not a rename; and a
body that consumes its hypothesis through goal-surface handle verbs
(`h.Ground` inside `a.Do`), where `Fact` does not substitute without
moving what the terminal refute sees.

`a.Obtain` / `a.Fix` register their minted Skolems in the ParseScope,
so later claim texts spell them with no `ctx.Var` declaration. The
surface-name contract is ONE NAME, ONE MEANING: an uncontested binder
name is offered as the spelling (write it directly); a name already
live — a declared variable, an alias, a constant, another goal free —
is never re-pointed, and the named form `Fix("u")` / `FixAs[φ]("u")`
is the road to a readable spelling (loud when the chosen name is
taken; an Obtain claim's ∃-binder is your own text — pick a fresh
letter there). A claim naming something the scope never declared
PANICS (the undeclared-free assert) instead of silently freshening. The
semantics in full — shadowing, the minted spelling as the escape hatch,
`a.Term`, the session twin — is §"Surface names — claim texts spell the
statement's binders" at the end of this section.

Claim, statement and term text is written as LITERALS (the
constitution's §"Stable authoring rules"; the lint is
`TestLintNoSprintfInProofFiles`). The `+` concatenation with a named Go
const that the rule permits is what `deltaSummand`, `acceptedHalf` and
`emptySecond` are. A schema the proof genuinely carries — an induction
property — is written ONCE as its λ-literal (`relatedOn` in
iterate/monoidal/monoidal.go is the model); its instances are
restated in place, where each is read.

Goal-surface choreography with NO paper word — `Basic()`, bare
`StripQuant()`, `CondRewrite()` — has no verb by design: it lives
inside the verbs' implementations, or behind `a.Do(…)` when a
particular goal really needs it. Reaching for `a.Do` repeatedly in one
body is a signal to report (`[kernel-wishlist]`: the missing verb),
not a style to settle into.

**Where the math layer is NOT the tool** — these are part of the
style, each with its own jurisdiction (which form an argument takes is
the constitution's §"Division of labor"; what each form is, here):

- **Structure**: `SplitIff` (named halves) / `InductStep` / `ByCaseStep` with Case
  labels, the linearizers (`Assuming` / `Unless` / `Suffices`),
  branch-method extraction. A Case body hosts a `Derive` block where
  it carries a deduction.
- **Calc kits** (`CalcEq` / `CalcRel` / `CalcOrder` / `CalcLeibniz`):
  an equation or relation chain stays a calc chain; a leg's
  one-or-two-cite body needs no `By`. A leg whose proof rewrites its
  two sides to one term is proved: the `t = t` a `Simp` leaves, and
  the `⊤` a `CondRewrite` after it leaves, are closed by the leg, with
  no trailing `Refl()` or `Basic()`. Two spellings, decided by where
  the chain ENDS: a chain whose endpoint IS the goal is terminal and
  is spelled `a.Show(label, kit.Calc(from, legs…))`; a chain that
  stops short of the goal is a fact producer, `f := a.CalcOrder(kit,
  from, legs…)` (`a.Calc` / `a.CalcLeibniz` likewise), consumed by a
  later `By`. `a.CalcOrder` on a terminal chain PANICS by design.
  Kernel-equality theories (ℝ, ℕ, ℤ) leave the kit's `Eq` nil —
  `CalcLeibniz` refuses a kit that supplies one — and
  `real_order_ring.OrderCalc(ctx)` is ℝ's instance,
  `nat_order.OrderCalc(ctx)` ℕ's.
- **Rewrite ladders**: consecutive `Cite`s consumed as goal rewrites
  (each stepping the goal — the `↦`-comment form) are computation with
  equations, not deduction from premises. `By` deliberately cannot
  express this.
- **Single-fact closes**: where ONE fact closes the leaf, prefer
  `Cite(f)` — it says "computation with one equation" rather than
  "deduction from one premise". That preference is for EQUATION-shaped
  facts at the normalize tier. A ground instance of an IMPLICATION law
  (`IntervalCongruence.At(…)`, any `… ⇒ …` law) stays a one-premise
  `By(law.At(…))` even when no refute is wanted: `Cite` installs it and
  leaves the antecedent obligation open, while `By`'s apply/close path
  discharges the antecedent from the context. A one-premise `By(f)` does **not**
  panic: the over-specification check (`prover/proof/step_by.go`, `closedAt`) fires
  only when a premise closes the leaf BEFORE the list is exhausted,
  naming the premises after it that never entered the leaf — an
  install never run, a witnessed premise never grounded. A bare
  resident fact listed after the closer is never named: `By` keeps
  every listed resident in the leaf before its first install, so the
  closing install's simplification had it in hand, and `By(law, h)`
  and `By(h, law)` are one close. Closing on the LAST premise is
  exactly the intended case. So reach for `Cite(f)` on grounds of what it says,
  never because the alternative is rejected; and a one-premise `By` is
  right where the terminal refute is wanted (`peano.Cases` ships as
  `By(At(Induction, m, isZeroOrSuc))`).

A handle bound outside a `Derive` block reaches its premise lists as
itself — a handle is a `CiteTarget` — with no text round-trip.

**Do not author** (the constitution's §"Division of labor"; the
superseded spellings it means): `Deduce`/`Have`/`Show` item blocks, the
`HypHandle` ceremony (`NewHypHandle` / `.From` / `.FromResident` /
`.Ground` / `Clear`), and any install-pile-then-`CnfRefute` close.

### Surface names — claim texts spell the statement's binders

A semantics of every `Argument` claim text (`a.Have` / `a.Show`-side
claims via `Obtain`/`ObtainChosen`, `a.Hyp`, and the `a.Term` parser
below), not a new Action. After

```go
func(a *Argument, x, y Term, h Fact) { … }   // ∀x y. … ⇒ …
```

or any in-body `x := a.Fix()` / `w, f := a.Obtain(…)`, a claim may
spell the STATEMENT's binder name — `"&0 ≤ x - y"` — even though the
goal's variable is the minted `x₀`. Each block records
`surface name → minted variable` as its verbs mint (`Fix` reads the
∀-binder it strips; `Obtain`/`Unpack` read the ∃-binders), a nested
block (`Derive`, `Given`, a `Case` body, a `Have` proof) inherits the
enclosing chain's bindings, and an inner binding of the same name
shadows the outer one — Go's own shadowing rule, so the claim's `x`
and the body's Go variable `x` agree by the closure-parameter lint.

Semantics: parse-scope overlay + capture-avoiding free-variable rename
(`core.Substitute`), NOT text substitution. Consequences worth knowing:

- the minted spelling (`x₀`) stays valid for the rest of the block that
  minted it and every block nested in it — the escape hatch for an outer
  variable whose name an inner block re-bound, and the whole
  pre-existing corpus. It ends with the block: a mint is a free of that
  block's goal, and a sibling branch is another goal whose strip picks
  its names from that goal alone, so it may mint the same spelling at
  another type (two `Case` bodies each fixing a binder `c`, one at `num`
  and one at `bool`, both mint `c₀`). Each block therefore withdraws, on
  exit, the parse-scope names it added (`Argument.declare`); a name an
  enclosing scope declared first stays that scope's. A NESTED block's
  strip is held to the enclosing blocks' names where a sibling's is
  not: its leaf need not mention a variable an enclosing block fixed
  (a `Have` whose claim leaves the statement's `x` out, with no
  hypothesis about it), the spelling is then fresh for the leaf, and a
  binder of another type would take it — a second type for one name.
  `Fix`, `Unpack` and `Obtain` pass over a spelling the scope declares
  at another type and fix the next: with `x₀:A` the statement's, a
  binder `x:set(A)` is fixed as `x₁`;
- a binder inside the claim (`∀x. …`) binds as usual and is untouched;
- a surface name that collides with a scope CONST still resolves as
  the const (unchanged from before);
- a surface name is read as a claim text reads it: `Fix("s₁")`,
  `Named("w₁")` and `Unpack(f, "p₁")` bind `s_1`, `w_1`, `p_1` — the
  names the claims' `s₁`, `w₁`, `p₁` parse to — so the two spellings
  are one name whatever the goal's own binder was, and a name live as
  `s₁` is taken as `s_1` too. A prime (`y'`) is an identifier character
  and folds to nothing. `a.Let`, `a.LetAs` and `a.Denote` name the
  variable they introduce the same way, as a session's `let` and
  `denote` do: `a.LetAs[Nat]("i₀", …)` introduces `i_0`, which later
  claims spell `i₀` or `i_0`.

`Argument.Term(raw string) *ext.TermWrapper` is the term-level
counterpart — `Script.TermText` with the block's aliases applied — for
the verbs that take a `Term`:

```go
q := a.Fix()                     // goal spells q₀
a.Take(a.Term("q + 1"))          // the witness names the surface q
```

Panics: parse failures and hyp-location failures with aliases active
append a legend line — `(surface names: q ≔ q₀)` — bridging what the
author wrote to what the goal prints.

Desugar: none — binding is bookkeeping; no ministep is recorded, and
recorded CNF keys are untouched (both spellings parse to the same
Prop).

**Session parity.** The same spelling works in a session, where "the
enclosing scope" is the focused goal: claim texts (`assert` /
`lemma` / `lean_rw` / `by` lemmas) and term parameters (`witness` /
`instantiate` / `trans` / `case_split`) may spell the bare base name
of a goal free variable whose spelling is minted (`n` for `n₀`),
PROVIDED it is unambiguous at that goal — no second mint shares the
base and no free variable is literally named it; on ambiguity spell
the mint. `inspect` advertises the live aliases per goal as
`surface_names` (`{"n": "n₀"}`). Source: `engine/surface_alias.go`.
`induction`'s `const` reads the same name, and reads it of a binder of the
goal's leading ∀-prefix as well, which a strip subscripts where it stands
(the `induction` entry).

A CLOSED claim or lemma text — one that binds every name it uses; a
bundle binder `∀X:presheaf(A, B).` binds X's components itself — is read
closed, with no surface name, goal variable or resident fact in scope:
at a leaf where the strip-minted `T₀ X₀ res₀` are live and spelled
`T X res`, the text `∀X:presheaf(A, B). ∀U:set(A). U ∈ T ⇒ …` states
the bundle's T, never the focus's T₀ under its surface name (the
bundle would then mint `X_T` beside it, and a proved section cited
by that text would state something else and fail to certify). The
text decides: one that reads with nothing declared is closed; one that
names something of the focus — a free variable, an operator a resident
structure fact binds — is read at the focus. The Go doors read a text the
same way, by the same function: `ctx.Lemma`, `ctx.Theorem`, a
`family.Sections` headline and `ctx.MakePropText` with the script's
variables set aside, an `a.Have` claim with the block's, so a section
stated over its own structure reads beside a record the member's strips
declare (`ctx.Var("R_0", …)`). An `a.Have` claim that is not closed is
read, as the session reads a claim, beside its goal's own variables and
surface names and the goal's hypotheses — never a variable the script
registered for another section or branch, which no goal of the block
states. emit checks every text it renders in the scope the replay parses
it in: an `a.Have` claim at its goal's; a `ctx.MakePropText` text beside
all the member's declarations and the Skolems its closure's parameters
fix (`R₀`, never the binder's own name `R`, which only the claim door
aliases), the spelled component (`ring_mul(S₀, …)`) where the short form
would meet a second record there.
Source: `ext/dsl/door.go` (`ParsePropTextAtDoor`); a direct parse of a
statement or claim text elsewhere fails `TestLintTextDoorsReadOneWay`.

Source: `prover/proof/derive.go` §"Surface names".

## The Go Script API surface (cheat sheet)

Authoritative reference for the primitives exported to proofs via
`library/authoring`. **Look here BEFORE grep-ing `prover/` or pattern-matching a
reference file for API shapes.** Anything not listed is either not intended
for chapter Go or too specialized to memorize — grep on demand. The
categories below cover ~95 % of what a file calls.

### Composition rules

- A section is a `*GoalStackNode`: what `ctx.Lemma(stmt, closure)` and
  `ctx.Theorem(headline, closure)` return, each already Qed'd, with
  `.PromisedThm()` its deferred cert. Inside a closure the argument
  advances with **`a.Do(step)`**, where `step` is an Action or
  `Chain(...)`.
- `.Do(Chain(a, b, c))` == `.Do(a).Do(b).Do(c)` for leaf-advancing steps.
  Multi-leaf Steps (`SplitConj`, `SplitIff`, `InductStep`, `AssertStep`,
  `ByCaseStep`, `ExistentialConstDefStep`) take `Case(...)` arms — the
  Cases are NOT chained, they're arguments. A SEQUENCE of asserted
  facts is never spelled as nested AssertStep Cases — it is a
  `Derive` block (§"The math layer").
- `Case("label", act1, act2, …)` labels a branch. Multi-arg `Case` composes
  its actions into a Chain internally — no explicit `Chain(...)` needed
  inside a Case. Labels carry mathematical content (the quality checklist in the
  agent doc), not boilerplate ("claim"/"after"/goal paraphrase).

### Script methods (the `*Script`: `ctx` in a `family.Sections` body, `a.Ctx()` inside a closure)

| Call | Returns | Use |
|---|---|---|
| `ctx.MakePropText(s)`                      | `Prop`           | build a `Prop` from text (for short `AssertStep` claims). Text is content-only: no ⊢, neither hypotheses nor `name:type` decls left of it (lint-enforced) — declare frees via `ctx.Var` instead. `ctx.MakePropText(s, overrides…)` pins a name for that one parse: a constant at the instance passed, or a variable — where disjoint branches mint one name at two types, `ctx.Var` refuses the second type, so each is a plain `Var(name, τ)` value and every text spelling the name passes the one it means (emit renders exactly this). Inside a `family.Theorem` closure the Script-scoped parser knows the MINTED names (`m₀`, `n₀`) and NOT the binder-name aliases (`m`, `n`) that `a.Have` claim texts accept — `a.Ctx().MakePropText("m + n = n + m")` fails with `variable "m" has no type declaration`; spell `m₀ + n₀ = n₀ + m₀` |
| `ctx.Const(name, ty)`                      | `*TermWrapper`   | declare a constant |
| `ctx.Var(name, ty)`                        | `*TermWrapper`   | declare a proof-level free AND register it in the parse scope. **Not for section Skolems** — those arrive as closure parameters (§"The section boundary binds"); not for a statement's const alphabet — that is the family vocabulary. What remains: a variable of the proof a Go expression or a text names — a Skolem a mid-body strip mints that no deduction verb returns. The binder of a Go-built term (a λ's, a `ForAll`'s) is `Var(name, ty)`, which builds the variable and registers nothing: registered, the name would be the one every later text reads and no closure binding it could alias, and `emit-section` writes the two so. Idempotent same-type; panics on a same-name different-type re-declaration |
| `ctx.ConstAs[φ](name)` / `ctx.VarAs[φ](name)` | `*Expr[φ]` | the typed spellings of `Const`/`Var`: the type is a phantom expression (`Fun2[indexSet, indexSet, Bool]`) instead of a `MakeFun`/`MakeVarType` assembly — the declaration reads as the type it declares, and the HANDLE is ready for typed slots — an application of it is text over the registered names — `ctx.TermText("plus(a, b)")`, or `a.TermAs[φ](text)` where a typed slot wants it — and `Equal` / `Lambda` build on the handles directly. Same ParseScope registration/panics |
| `ctx.Nat(n)`                               | `*Expr[Nat]`     | `Numeral` in the typed world — numerals are `:num` |
| `ctx.ConstDef(c)`                          | `Prop`           | fetch a const's defining equation |
| `ctx.Dep(Entry)`                          | `ThmCert`        | the claiming dep verb: LibraryThm lookup + claim, idempotent, the entry in its RAW stated form — what `LeanRw`, a `Simp` rule and the marked raw-form cite take. The harness serves every entry your member's record names; you do not build deps yourself |
| `ctx.ClaimProvedThm(thm)`                  | —                | realize a harness-loaded dep so citations resolve |
| `ctx.NormalizedThm(dep)`                   | `Thm`            | a dep's installable canonical CNF form. `Cite(entry)` computes this automatically — spell it only for cert-valued PARAMETERS (Calc kits' `Trans:`, algebra.Group fields) and handle content-matchers, never for leaf cites (the constitution's §"Citation forms") |
| `ctx.AtTypes(dep, τ…)`                     | `*TypedThm`      | dep type-instantiated at `τ…` (type args positional over the NORMALIZED statement's type vars; witnesses through it read in the dep's STATED order — a PARTIAL tuple too, wherever the stated binders stand in the install's leading ∀-block (the executor moves them to its front); positionally only where Normalize renamed a stated binder or put it below a guard or an ∃ — §`ByInduction`'s "The predicate is the head of the principle's conclusion, and the tuple is read as the terminal grounds it" is where that convention is stated and why it is load-bearing) — replaces LemmaPreserve+TypeInst text pairs. **In a typed-surface family prefer the letter-keyed spellings** — a wrapper's `At`/`Cite` (instance inferred from typed witnesses), sole-letter `Inst[τ]()`, or multi-letter `Inst(TypeBinder.BindA[τ](), …)` (named bindings, order-free) — same install tail, byte-identical form, no positional convention authored; `ctx.AtTypes` remains for partial tuples and multi-variable non-entry Thms, `ctx.AtSoleType(dep, τ)` for a sole-variable Thm or raw row (machine-named included). These methods and `ctx.AtTypeVars` also accept a proved local section node, retaining its stated binder names and deferred certificate |
| `ctx.InductStep(v, cases...)`              | `Step`           | induction on `v`; first Case is the base, second the step (step's IH is a hyp) |
| `ctx.AssertStep(claim, cases...)`          | `Step`           | assert `claim`; first Case proves it, second uses it as hyp |
| `ctx.ByCaseStep(disj, cases...)`           | `Step`           | classical case split on `disj` / ¬`disj` |
| `ctx.ExistentialConstDefStep(c, cases...)` | `Step`           | Hilbert-ε const introduction: `child(0)` = existence, `child(1)` = residual w/ defining property as hyp |
| `ctx.AxiomDefStep(c)`                      | `Step`           | close a leaf that IS `c`'s defining equation |

### Actions (leaf-consuming ministeps — pass to `.Do(...)` or `Chain(...)`)

**Quantifier / hypothesis structure**

| Action | Effect |
|---|---|
| `StripQuant()`                          | peel ALL consecutive top-level ∀ into fresh frees. Never call twice for ONE ∀-prefix (one call handles it; a consecutive second call on the same prefix is a no-op that trips the leaf-tracker). Consecutive calls ARE legitimate when each Skolemizes a different ∃-HYP on a sequent goal — emit renders that pattern and it replays. |
| `StripImp()`                            | peel a top-level ⇒ (introduces the antecedent as a hyp). |
| `ClearHyps(indices ...int)`             | drop multiple hyps (original indices, applied in reverse). |
| `Witness(t Term)`                       | supply `t` for a top-level ∃-goal, leaving `P(t)`; for a top-level ∃!-goal, leaving `P(t) ∧ (∀y. P(y) ⇒ y = t)`. |
| `Instantiate(t Term)`                   | instantiate a top-level ∀-hyp at `t`; keeps hyp. |
| `Specialize(hyps ...SpecializeHyp)`     | batch ∀-hyp grounding + clear. **Preferred over `Instantiate×k + ClearHyps`.** |
| `SpecializeKeep(hyps ...)`              | same, but keeps the specialized hyp. |
| `InstHyp(idx int, ws ...Term)`          | `SpecializeHyp` bundle constructor (used inside `Specialize`/`SpecializeKeep`). |

**Hyps are NEVER addressed by index** (the lint
`TestLintNoPositionalHypIndices` fails any NEW integer hyp index). Hyp
lists are canonically sorted and renumber on every hyp-adding step, so
a session's hyp index must NOT be transcribed literally. In a
`Derive` block a hypothesis is a `Fact` VALUE — `a.Hyp(content)` names
a resident one, the other verbs return the ones they introduce, and
`f.At(w…)` grounds — so no addressing arises.

Outside a `Derive` block (a Calc leg, a rewrite ladder, a Case body
that is not a deduction) the remaining index verbs are handle-addressed
via `HypHandle`:

| Handle verb | Effect |
|---|---|
| `h := NewHypHandle("cauchyX")`  | create (a local; never package-level). Name the fact's mathematical role, not its position. |
| `h.From(act)`                   | bind: `act` must introduce exactly ONE new hyp; `h` names it. Tracks through StripQuant Skolemization and Specialize replacement automatically. |
| `h.Rw()` / `h.RwRev()` / `h.Subst()` / `h.CongrArg(fn)` / `h.SplitDisj(LeftHolds(…), RightHolds(…))` | the index verbs, handle-addressed. `Rw` fires the hyp's equation as written (l → r), `RwRev` reversed — the same `Fwd` / `Rev` orientation vocabulary the simp rules use, spelled in the verb so no call site carries a bare bool. The equation may be a ground `⇔` (an equation at bool): `iff.Rw()` rewrites its left atom to its right everywhere; a ∀-quantified one is grounded first — `f.At(t).Rw()` grounds it on the spine and rewrites by the instance (§"A fact in hand") — or taken whole as a rule, `Simp(Fwd(f))`, which also reaches under a binder. |
| `h.DismissLeft(label, body…)` / `h.DismissRight(…)` | linearized BINARY disjunctive-hyp split: discharge the named disjunct inline (must close — labeled panic), continue the enclosing chain with the other disjunct resident. |
| `h.FromResident(content)`        | bind an ALREADY-RESIDENT hyp by α-content: ByCase/Split* branch hyps (content = discriminant / its negation), multi-hyp installs. |
| `h.Ground(w…)` / `h.GroundKeep(w…)` / `Clear(h…)` / `CiteSpecializeKeepAs` | grounding and context bookkeeping — a deduction has no use for these (`f.At` grounds; `By` clears), so reaching for one means the body is not a `Derive` block. |

For an UNTRANSFORMED resident hyp, content addressing
(`GroundHyp(dep, w…)` — entry/name targets resolve to the same
canonical form `Cite` installs — or a fresh `Cite(dep, w…)` cite)
remains equally legal. A hyp rewritten TOGETHER with several others in one step (e.g.
by a preceding `Rw`) is ambiguous to the tracker — it panics naming the
step; only such sites may stay positional, under the lint's per-file
allowlist (shrink-only).

**Citation — `Cite` is THE verb (the constitution's §"Citation forms")**

| Action | Effect |
|---|---|
| `Cite(dep)`                              | **The default cite.** Bring the fact to bear: closes the leaf outright when the fact is stronger (old bare `CiteKnown`) OR when the leaf IS the fact modulo Normalize (the normalize-tier close — session auto-match parity, so a ⇒-law cited at the sequent leaf that states it CLOSES even though the named target resolves to the packed clause form), else installs it as a hyp via the PRESERVING chain and closes the reproduction obligation (old `UseLemmaExact`). A no-op panics loudly. Targets: registry entry var (`Cite(nat_arith.AddSym)`, another family's qualified the same way), sibling section node (`Cite(fwd)`), or explicit Prop/cert (verbatim). An entry resolves to the canonical install form (NormalizedThm∘Dep) and is claimed at use — NO manifest line, NO wrapper. A RESIDENT fact is not a target: `Cite(h)` on a `Have` result panics ("is a RESIDENT fact"); close with `By(h)`, or let the goal-surface step that reaches it close on it — an `Unfold` whose residual is a resident hypothesis closes the leaf itself, exactly as one whose residual is an identity does. |
| `Cite(dep, w1,…,wk)`                     | ground instance at witnesses — the old `CiteSpecialize` mechanics (replay-exact install + content-located Specialize; ∀-source dropped). Witnesses unused (cite closed the section) panics: drop them. |
| `CiteKeep(dep, w1,…,wk)`                 | same, keeping the ∀-source resident. Witnesses required. |
| `<Entry>.At(w…)`                         | **the typed cite** — in a family with `zz_typed_thms_gen.go`, every entry var is its own wrapper: `At` is the ground `Fact` — a premise; as a step the cite is the verb's, `Cite(<Entry>, w…)`, or `Cite(<Entry>.Inst[T](), w…)` at a chosen instance — witnesses in the STATEMENT's binder order (⇒-antecedents are not slots) as `Typed[φ]` values (closure params, `FixAs`/`TermAs` results — an untyped term enters via `ext.As[φ]`). For a polymorphic dep the type instance is INFERRED from the witnesses and installed EXACT — the speculative-σ fork never runs, and no positional type-arg order is authored. Full witness tuple only; a partial cite stays on untyped `At`/`Cite`. **A statement binds each prefix binder once.** A tuple is mapped onto the install prefix by binder NAME; where the statement binds a prefix name a second time inside its body (an index re-bound in an obligation, a point re-bound under a quantifier), no slot is addressable by name and a partial tuple is read positionally against the clause prefix — correct where that prefix stands in the stated order, corrected by type where the reading is ill-typed, and silently wrong where the clause form reorders the prefix and two of its binders share a type. The gate `TestLintTwiceBoundPrefixBinderIsReadPositionally` refuses that statement; the remedy is to bind the inner occurrence under another name (α-neutral, the key unmoved), and a grounding that fails names the lane it read the tuple in. |
| `<Entry>.At[DimN](u, v *Vec[Elem, DimN])`  | the typed cite of a VECTOR member: the statement's vector binders arrive as `*Vec` at one inferred dimension phantom, the dimension binder is written off them (`proof.SameDimension`) and is not a parameter; an `*Inhabited` parameter (the vector's membership among the antecedents) makes the result a `proof.PremiseGroup`. A `*Vec[Real, DimM]` where the phantom ties to another vector's `DimN` does not compile. A matrix binder arrives the same way as a `*Mat` at its two phantoms and a map binder as a `*VecFun[Elem, DimN, DimM]`, both dimension binders written off it. |
| `<Entry>.Inst[τ]()` / `<Entry>.Inst(TypeBinder.BindA[τ](), …)` | the bare premise at an EXPLICIT type instance — no witnesses to infer from, so the types are spelled. A SOLE-letter statement takes one positional phantom (`Inst[Real]()` — one variable, nothing to pair). A multi-letter statement takes one NAMED binding per letter: `TypeBinder.BindA[Real]()` reads "bind the statement's A to Real"; argument order carries no meaning, and a wrong/missing/double letter panics listing the statement's own. No positional multi-letter type-argument surface exists. For a dep taken raw: `ctx.AtTypeVars(ctx.Dep(Entry), TypeBinder.BindA[τ](), …)`. Feeds `By`/premise lists exactly like `ctx.AtTypes` (same install tail, byte-identical). |
| `<Law>.Read(instance)` / `proof.Read(law, instance)` | A structure law read at an instance of its structure: `∀comps. S(comps) ⇒ body` at `⊢ S(c…)` is `⊢ body[comps := c]`, keyless — one cite target for `By`, `Simp(Fwd(…))` and the typed `.At(w…)`. `retrieve` by goal returns a law read through a projection as a `corpus_readings` hit, with the chain and both spellings. **Entry below: `<Law>.Read(instance)` / `proof.Read(law, instance)`.** |
| `UseLemma(thm)`                          | **MARKED legacy: the DESTRUCTIVE install.** Lemma+KnownThm fusion whose whole-context simplify may rewrite EXISTING hyps — reach for it only when the argument needs exactly that (the "closes at the cite via hyp-rewrite" idiom; Cite's preserving install never touches resident hyps). A surviving `UseLemma` is a deliberate signal, and carries a comment. |
| `Cite(MakeFact(ctx.Dep(N)))`             | **MARKED raw-form escape**: cite a row's RAW surface form when eqSimplify must split a multi-clause conjunction's separate binders (nat_arith.Mul/Add class). Carries a comment. |
| `UseLemmaSpecialize(thm, w1,…,wk)`       | ground ONE k-binder lemma at `(w1,…,wk)` via the DESTRUCTIVE install (`UseLemma + Specialize(InstHyp(0,…))` — a different tree from `Cite(dep, w…)`). Legacy; keep only where the destructive install matters. |
| `UseLemmaInstances(thm, t1,…,tk)`        | k parallel top-binder instances of a **1-binder** lemma (destructive install). |
| `UseLemmaExact` / `CiteKnown` / `CiteNode` / `CiteSpecialize(Keep)` | the pre-consolidation spellings — frozen for engine internals; in hand-written chapter Go they are all subsumed by `Cite`. Don't author new sites with them. |

**Equation / congruence / definition**

| Action | Effect |
|---|---|
| `Trans(b Term)`                          | split `A = C` into `A = b` + `b = C`. |
| `Congr()`                                | `f(a) = f(b)` → `a = b` (all args). |
| `CongrArg(fn, hypIdx)` / `CongrFun(arg, hypIdx)` | congruence at arg / function position. |
| `Funext()`                               | `f = g` → `∀x. f(x) = g(x)`, every function equation of the conclusion at once. It is function extensionality, the verb for functions and predicates, and not the one for an equation between sets: that becomes `∀x. S(x) ⇔ T(x)`, applications where the laws of sets and the plain `By` read `x ∈ S`, with each set-builder applied to the point, `{p \| φ}(x)`, which no verb reads as a membership (`Unpack`, `Conjuncts` and `SplitDisj` refuse it, naming it and the rewrite). An equation between sets is opened by `Simp(Fwd(set_basic.Extension))`, which leaves `∀x. x ∈ S ⇔ x ∈ T`, or by its two inclusions (`set_order.SubsetAntisym`). Where a Funext on sets stays, a branch's hypothesis of the applied form is opened by stating what it says, `Obtain…As(label, "∃…", BySets(fact))`. |
| `Rewrite()` (= `RewriteAuto`)            | apply rewrite fixpoint over eqSimplify. |
| `CondRewrite()`                          | conditional-rewrite dispatcher. |
| `LeanRw(lemma)`                          | Lean-style single-shot rewrite. `lemma` is any `Prop` — a `MakePropText` you spell, or `ctx.Dep("<NAME>")`, which rewrites by a dependency's own statement without copying it. **Never the ∀-form of a PERMUTATIVE law** (commutativity, any rule whose result re-matches its own pattern): the rewrite oscillates until the divergence whistle trips and dies in a `Should not happen` assertion naming its site (session `lean_rw` → HTTP 500, same cause). Pin the instance — `term_specialize` in the session, a ground `MakePropText("m₀ + n₀ = n₀ + m₀")` in Go — and discharge the rule obligation with `Cite(dep)`. The step leaves its equation as its FIRST obligation, so it is normally `Expect(LeanRw(…), Case(<the equation>, Cite(dep)), Case(<the residue>, …))`. |
| `Simp(Fwd(r₁), Rev(r₂), …)` | The Go face of session `simp_with`: rewrite the goal's conclusion with an ORDERED rule set, jointly, to fixpoint; `Fwd`/`Rev` name the direction against the rule's STATEMENT as written; a polymorphic rule is adapted to the goal's type instances and to the instances the rewrite exposes, as the session adapts its rules (one copy per discovered instance, the copy's obligation a type instance of the rule) — a definition stated at the chapter's letter fires at the goal's type without a pin, and `.Inst[τ]()` pins an instance the adaptation does not reach. **Entry below: `Simp(Fwd(r₁), Rev(r₂), …)`.** |
| `Rw(hypIdx, flip)`                       | rewrite using hyp `hypIdx` (left→right unless `flip`). The positional Step — the shared bottom under `h.Rw()` / `f.Rw()`, and the only spelling that still takes the bool. `TestLintNoPositionalHypIndices` bans it in a chapter body; emit renders it only when no `Have` owns the hyp. |
| `Subst(hypIdx)`                          | substitute using an equational hyp. |
| `Unfold(<definition>)`                   | open a definition: the constant it defines is expanded on the whole leaf — the def-expand composite ministep (`prover/proof/step_composite.go`; `DefExpandStep(c)` is the same step taking the constant, the engine's own spelling). The argument is the definition itself, the entry that defines the constant (`set_basic.SubsetDef`, `group.GroupOn`), and the member is recorded standing on it. **An `Unfold` whose opened goal is an identity CLOSES the leaf itself** (`computeDefExpandSubGoals` returns no child): its tidy (`tactic.UnfoldTidyTactic`) closes a leaf whose conclusion is ⊤ once the basic rewrites and the connective simplification have run (an equation of equal sides among them), whose conclusion a hypothesis states as a whole modulo that normalization, or whose hypotheses contradict. Emit renders no closer after it, and a step after it is refused "no unsolved leaves remaining", the refusal naming the `Unfold`, the line it was written on and what its tidy found; only add a closer when the opened goal is none of these. **Entry below.** |
| `TypeInst(source)`                       | polymorphic type instantiation from `source`. |
| `Denote(sizeThreshold)`                  | denote/expand at size threshold. **Entry below: "Denote — the abbreviation family".** |
| `HilbertDenote()`                        | expand a Hilbert ε-term. |

**Splitting**

| Action | Effect |
|---|---|
| `SplitConj(cases ...Case)`               | split the conclusion at its outermost `∧`, in two — two Cases, whatever the two sides hold (one for `A ∧ A`). `∧` is left-associative: `A ∧ B ∧ C` splits into `A ∧ B` and `C`. |
| `SplitConjAll(cases ...Case)`            | flatten the whole `∧`-spine, however it is associated, into one subgoal per conjunct — one Case per conjunct. |
| `SplitDisj(LeftHolds(…), RightHolds(…))` | split a disjunctive hypothesis `A ∨ B ⊢ C` into the branch where A holds and the branch where B holds, each claimed by the disjunct it assumes (a typed slot, so a swapped pair does not compile); `SplitDisjAt(i, …)` names the hypothesis. The positional `SplitDisjCases` is emit's caseless form and no chapter writes it. |
| `SplitIff(Forward(…), Backward(…))`      | split `A ⇔ B` into its two arms. The halves are NAMED, not positional: `Forward` is `A ⊢ B`, `Backward` is `B ⊢ A`, they are distinct types so neither fits the other's slot, and the verb places each where the tactic wants it — the ⇐ arm is the one the tactic emits FIRST, which is the reverse of the reading order and exactly the convention nobody should have to hold. The `⇒`/`⇐` prefix of the rendered label comes from the slot, so it cannot disagree with the branch. `a.Iff()` + `a.Forward(…)` / `a.Backward(…)` is the same split as Derive verbs. The order is asserted on every split (prover/proof/iff_direction.go): nothing else observes it, and a tactic change would otherwise leave every landed label quietly lying. |
| `SplitHypIff(BothHold(…), NeitherHolds(…))` / `SplitHypImply` | split ⇔/⇒ appearing in a hyp. An ⇔ in the HYPOTHESES has no directions — it splits into the branch where both sides hold and the branch where neither does — so its halves are named for truth, not for arrows. `SplitHypIffAt(i, …)` targets one index; `f.SplitIff` / `h.SplitIff` address the hyp by content. |

**Closers**

| Action | Effect |
|---|---|
| `CnfRefute()`                            | CNF-based refuter. **Live is nondeterministic** — the family blob covers it (the gotcha below; recording is the header of `library/integrity/gates/record_cnf_test.go`). |
| `Basic()`                                | mini-refuter for trivial closes. |
| `TrivialSimplify()`                      | β-reduce / trivial simplification — a SHAPING action, never a close site: it may not close, and a leaf that ends on it closes by accident. The lint `TestLintNoTerminalTrivialSimplify` refuses it as the last action of a list; spell the close — `TrivialNormalized()` (normalize-to-⊤), `Refl()`, or `ByArith(premises…)` for an arithmetic close. Mid-list (`a.Do(TrivialSimplify())` before a `Show`) it is fine. |
| `TrivialNormalized()`                    | close via normalize-to-⊤ short-circuit. **Distinct from `CnfRefute`**: no CNF cache key. Session `auto` reporting `matched_key:""` with no `matched_section` is this, NOT a refute. |
| `Arith()`                                | gated arithmetic ministep. Sound-by-construction under the omega circularity gate. |
| `RingNf()`                               | the ring normal form as a rewrite: every arithmetic subterm of the goal — conclusion and hypotheses — to the sum of monomials the ring normalizer reads, unit coefficients and a zero constant elided (`(b + a) * 2` is `2 * a + 2 * b`). Under the same policy gate as `Arith()`; session `ring_nf`. |
| `fact.Simp(Fwd(r₁), …)`                  | `Simp` at the fact's own hypothesis (Lean's `simp at h`): rewritten in its place, side conditions discharged against the other hypotheses, the conclusion untouched; the fact goes on naming the rewritten hypothesis. `SimpAt(i, rules…)` is the positional form emit falls back to. |
| `SimpAll(rules…)`                        | `Simp` over the conclusion and every hypothesis, one target per round to a fixpoint across the targets (session `simp_all`); a Fact bound to a hypothesis it rewrites follows it. |
| `Simp(fam.SimpSet())`                    | the chapter's simp set as one rule: every theorem `fam` marked `Simp: true` in its stated orientation, the step recording only the rules that fired (`registry.Family.SimpSet`). |
| `SetTac()` / `SetTacMembership()` / `SetTacLegacy()` | set-theoretic tactics. **Session spelling is the bare `{"type":"set_tac"}` — it takes NO arguments**, and `{"membership":true}` is rejected. `SetTac()` IS the session move: the door tries MEMBERSHIP mode first, then legacy full expansion (`proof.SetTacOrder`, run by `engine/engine.go`'s `case "set_tac"` and by the Go step alike), and records the step of the mode that closed; `dump-section` confirms per-site, printing `SetTac(<n> consts, SET_TAC_MEMBERSHIP)`, and emit renders the record as the exact-mode form, `SetTacMembership()` or `SetTacLegacy()`, which replays that one driver. The const list is the driver's fixed vocabulary, not a per-caller choice — all three Go forms called with no consts use `StandardSetVocabulary()`. |
| `Assumption()` / `Refl()` / `Symm()` / `Left()` / `Right()` / `ByContra()` | boilerplate closers. A rewrite ladder whose result is reflexive ends on one: `Rw` and `Simp` leave `t = t` (or the `⊤` it tidies to) OPEN, and a `Show` of `Rw, Simp` alone panics "did not close" until `Refl()` or `Basic()` follows — the session's `basic` is the same close. |

**Composite (multi-leaf) forms**

| Constructor | Purpose |
|---|---|
| `Chain(actions ...Action)`               | sequential composition (single-leaf progression). |
| `Case(label, actions ...Action)`         | labeled branch of a Chain-form multi-leaf Step; multi-arg sequences internally, so a `Chain(...)` inside it composes nothing — flatten it. Inside a `Derive` the split verbs take their branches as statements instead (§"A split is two sentences"). |
| `AssertStep(claim Prop, cases ...Case)`  | package-level twin of `ctx.AssertStep` — for a genuinely BINARY assert (residual immediately branches); sequences use `Derive`. |
| `Derive(func(a *Argument))`                   | the deduction block — verbs, contracts and the worked example in §"The math layer" above. |
| `By(premises…)` / `ByArith(premises…)` / `ByChase(Depth(k), premises…)` | the deduction close: exactly these premises, everything else cleared, then refute / gated arith / the diagram chase at k pull-back rounds. `ByArith()` and `BySets()` are legal with no premise: the closer's own procedure is the content; `ByChase` reads its diagram from the premises and carries `Depth(k)` in its list. **`ByArith`, `ByChase`: entries below.** |
| `By(Normalized, …)` / `By(DenotedAs(name, term), …)` / `By(HilbertDenoted, …)` | the same, with a normalization between the installs and the close (`Basic` / `Denote`+Basic / `HilbertDenote`+Basic). **Only when the close fails with NO cleared hyps** — that is a shape problem, not a missing premise; the panic says so. The denote shaping available to a proof file is `DenotedAs(name, term)` / `HilbertDenotedAs(name, term)` — the size-threshold form `Denoted(n)` is a search stage and is deliberately NOT on the bare-name surface (`library/authoring`'s comment on the shaping options says so), so writing `By(Denoted(n), …)` in a file is `undefined: Denoted`. A `By` also REFUSES two explicit denote shapings in one premise list — a By names at most one. |
| `f.Rw()` / `f.RwRev()` / `f.Subst()` / `f.CongrArg(fn)` | A fact in hand driving a goal rewrite — resident, or `f.At(w…)` grounded first. It RETURNS the step, which runs inside `a.Do(…)`, a Show or a Case. **Entry below: `f.Rw()` / `f.RwRev()` / `f.Subst()` / `f.CongrArg(fn)`.** |
| `At(dep, w…)` / `f.At(w…)`               | a ground instance as a VALUE (premise-list element), not a step. A registered entry and a fact are typed and take the method, `dep.At(w…)`; a sibling SECTION (`chain := ctx.Lemma(…)`) is a bare node with no typed handle, so it is the one cite a typed chapter writes with the function, `At(chain, w…)`, its witnesses passing as `Term`. |
| `MakeFact(cert)`                         | name a kernel certificate or an explicit statement as a `Fact`, for a verb that takes a `CiteTarget`: `Cite(MakeFact(ctx.Dep(N)))`, `Fwd(MakeFact(ctx.DepNormalized(N)))`. Every other target — an entry var, a typed instance, a section node, a handle, a `Fact` — is a `CiteTarget` already and passes as itself; a `By` list takes a certificate bare. |
| `Deduce` / `Have` / `Show` (package-level) | superseded by `Derive`. Don't author new sites. |
| `Assuming(t, label, side ...Action)`     | linearized case split — "we may assume t": discharge the branch on which t fails inline (must close; labeled panic), continue the enclosing chain under hyp `t` — whatever t's polarity: `Assuming(¬p)` continues under `¬p`. |
| `Unless(t, label, side ...Action)`       | mirror — "settled when t holds": discharge the branch on which t holds, continue under t's denial (`¬t`, or `p` for t = `¬p` — the split contracts a leading ¬). |
| `Suffices(claim, label, bridge ...Action)` | Have's mirror — "it suffices to prove claim": `bridge` closes goal-from-claim inline, the chain continues proving `claim`. |
| `CalcEq(Leg(t, label, proof…), …, FinalLeg(label, proof…))` | flat equation chain L = t₁ = … = R; desugars to the identical right-nested Trans tree (pb-stable). A leg's proof may end on `t = t` or `⊤`: the leg closes either. |
| `CalcRel{Rel, Trans}.Calc(from, Leg…)`   | relation chain (≤ …) as a fact producer inside `Derive`; the transitivity groundings are COMPUTED from the leg terms; the chained fact ends resident. **Entries below: `CalcOrder{…}.Calc`, `CalcLeibniz`, "Calc: two contracts".** |
| `ByCaseStep(disj Term, cases ...Case)`   | package-level twin. |
| `ExistentialConstDefStep(c, cases ...)`  | package-level twin: a choice constant `c = εx. P(x)` read by its two obligations as cases, `⊢ ∃x. P(x)` and `P(c) ⊢ G`, `c` kept folded — the spelling for a goal that is not P(c) itself, or for two choices read in one proof (peano's ind_suc/ind_zero pair, `indSucSpec`, `proofs/nat_num/peano/peano.go`). Where the goal IS P(c), `a.Have("…", "∃x. P(x)", …)` then `Unfold(<c's definition>)` is the same move on every choice constant, with or without parameters (§"def_expand"). A spec mint is never this step: `family.DefineSpec` (a short SpecEntry) where `proof.AnalyzeSpecGoal` admits the constant (applied at plain goal binders or pair literals of them), a `Define` whose equation spells the choice at an ENCODING (`num_pair_fst(n) = εx. ∃y. n = num_pair(x, y)`, datatype_universe's num_pair_fst/num_pair_snd and num_tag_value). |
| `Lemma(prop, cases ...Case)`             | inject `prop` via Cases (older shape; prefer `AssertStep`). |
| `LemmaPreserve(prop)`                    | preservation-mode lemma (KI:471 payload). |

### Action entries

The Actions whose contract does not fit a table row — the Go-side
primitives a body composes, record-and-replay counterparts of session
tactics, exposed through the Script API. An entry names the signature,
the desugar (which recorded ministeps land), the panic contract and a
usage sketch; panics are the soundness posture — every misuse is loud,
nothing degrades silently. A row above names its entry.

#### `Opening(open Action, body any) any`

The OPENED section: wraps a `Theorem` / `Lemma` body with ONE opening
action that runs on the section root BEFORE any binder is bound.

```go
Build: family.Theorem(
    "∀s:set(A). ∀f:(A → real). finite(s) ⇒ …",
    Opening(Unfold(RealSumDef), func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], finite Fact) { … }))
```

The gap it closes: the binder closure's parameters are bound before the
body's first action, so a member whose proof must REWRITE first — unfold
a defined constant so the hypothesis it is handed is the unfolded one —
could not use them at all. Its only route was the zero-parameter form
with `a.Fix()`/`a.Assume()` walls, which also forfeited the TYPED binder
parameters (`*Expr[φ]` / `*Arrow[X, Y]`) and dropped the whole member to
the untyped surface.

Contract:

- `open` runs through `a.Do` on the section root, inside the section's
  own block; the body is then bound against the goal AS IT STANDS AFTER
  the opening. A closure's parameters PLAN against that goal — an
  `Unfold` that rewrites inside an antecedent hands the closure the
  unfolded `Fact`; the ∀-binder names stay the statement's own where the
  opened goal still carries them (the plan reads them off the goal, as
  always); a binder the opening consumed is no longer a slot, and the
  existing plan error fires with the parameter index and says the
  mismatch is against the OPENED goal. Typed parameters adopt after the
  opening exactly as at an unopened boundary (same checked constructor,
  same plan-time type check).
- Several opening moves are spelled as ONE `Chain(…)`.
- Composes with both body shapes — `Opening(Unfold(RealSumDef), BySets())` is
  the opening move then the one action — and with `Script.Lemma`, so
  `Family.Sections` bodies get it for free. The registry passes the body
  through as `any`; nothing changes there.
- An unwrapped body is untouched: the unopened path is the same code it
  was, byte-identical recorded steps, no per-section cost.

Desugar: the opening action's own recorded step(s) on the section root,
then the closure form's `StripQuant1` / `StripImp` binds — no new proto,
no change to record or replay. A no-op opening (`Opening(Chain(), body)`)
records exactly what the unwrapped body records.

Panics, each naming `Opening`: a nil opening action; a wrapper nested in
a wrapper (spell the moves as one `Chain`); a body that is neither a
binder closure nor an `Action` (nil included) — all three at the call
site, before the section opens; an opening action that fails or that
closes the section outright (nothing left for the body), attributed to
the opening; and the plan mismatch above, which prints the opened goal.

Higher-order binders go through the same gate: a `∀P:(set(A) → bool)` binder is adopted at an `*Arrow[Set[A], Bool]` parameter after the opening exactly as at an unopened boundary, and the adopted arrow goes where a witness slot wants a term, as every typed value does (the slot takes a `TermLike`).

Source: `prover/proof/section.go`, beside `Script.Theorem`.

#### `family.Postulate(statement, term)` — the axiom of infinity

The one statement the corpus assumes outright is a registry member:
`peano.Infinity`, `⊢ ∃f:(ind → ind). ∃z:ind. (∀x₁ x₂:ind. f(x₁) = f(x₂) ⇒
x₁ = x₂) ∧ (∀x:ind. f(x) ≠ z)` — some map of `ind` into itself separates
points and misses a point. It is built by `family.Postulate`, which takes
the statement text and a Go function building the same term from the
logic's constructors: the text is the member's surface (its key, the
index, the typed wrapper), the term is what `core.NewAxiom` is handed,
and the mint panics unless the two are α-equal. The member has no proof
and is no card; the corpus seam and the replay harness serve it as its
axiom exactly where they serve a card (`registry.ProofEntry.ServedAsAxiom`),
and a member cites it as it cites any other — `Cite(peano.Infinity)`.

The registry admits one postulate: a second panics at registration,
naming the first. It has one consumer, `peano.indSucSpec`, whose Hilbert
choices of `ind_suc` and `ind_zero` read the axiom's two witnesses;
everything else in the `num` construction goes through that theorem.

#### The arithmetic close — `ByArith(premises…)`

One arithmetic closer is on the chapter surface, and it keeps By's
premise discipline: every hypothesis the list does not name is cleared,
the named premises are installed, and the gated arithmetic decides the
leaf (`Arith`, then the trivial simplification of what it leaves, in
bounded rounds).

```go
a.Have("the ring identity", "(m + n) * (3 * B) = B * (m + (m + n)) + B * (n + (m + n))", ByArith())
a.Show("the bound, carried across it", ByArith(identity, cauchy.At(m, n), At(nat_monus.DistLessEqCases, p, q, r)))
```

An equation at a ring that is one BY A FACT — a chapter's `ring Fact`
on a carrier set, named as a premise with the atoms' memberships
(`ByArith(ring, members)`), an abstract whole-type chapter's
(`ByArith(ring)`), or a carrier whose instance is installed (ℂ:
`ByArith()` bare) — closes through the structure ring (§"The structure
ring"): the carrier laws read at the fact's components and its set,
the whole-type fact bridged to 𝕌, with the ring's numerals the
additive powers of one. **`Scaled(c, h)`** is the premise `h` — an equation once
installed and grounded — followed by its congruence `c·l = c·r`, added
beside it and proved from it: Lean's `linear_combination c * h`, for the
polynomial coefficient the deciders cannot search for
(`ByArith(Scaled(a.Term("e"), h))` closes
`a + b = c·d ⊢ (a + b)·e = c·d·e`; an equation with a variable on one
side defines it and needs none). It composes with `At` (`Scaled(c,
At(law, w…))` scales the grounded instance), not with `Where`.

**`ByArith()` with no premise** states that the goal is a fact of
arithmetic alone — an identity, a guard such as `n ≤ m + n`, an estimate
that asks nothing of its point. The closer reads the goal and nothing
else, so a leaf that needed a resident hypothesis fails with the
cleared-hypothesis list, and the repair is to name it. The session
spelling is `by {arith:true}` with no `by_hyps` and no `with_lemmas`.

A fact the close needs is a PREMISE, not an install: `X.At(w…)`,
`fact.At(w…)`, `a.Hyp("…")` in the list, in place of a `Cite` or a
grounding step ahead of the close. An equation or an ⇔ read at its
witnesses (`At(nat_order.LessEqMulCancel, m, n, p)`) is a premise like
any other.

`Arith()` and `TrivialSimplify()` stay as ministeps for the middle of a
hand-driven chain, where they shape a leaf and do not close it.

#### The diagram chase — `ByChase(Depth(k), premises…)`

One step of an abelian diagram chase closes through the chase closer
(prover/solver/chase) with By's premise discipline: every hypothesis the
list does not name is cleared, the named premises are read as the
diagram — the modules (`module_on` facts, including
those supplied by a self-contained homomorphism), the homomorphisms between
them, the commuting squares and the other equation laws, the exactness,
onto and one-to-one facts, the submodules a coset is reduced through,
the elements and their memberships — and the leaf is decided by the
integral polynomial-module algebra of that diagram, pulling preimages
back for `Depth(k)` rounds. `Depth(k)` is the list's one parameter and
is required; a `By`, `ByArith` or `BySets` refuses it.

```go
// chain_complex.BoundariesSubsetCycles above degree 0: u a member of the image of d(m + 1 + 1)
modules, boundaryMaps := ComplexModules.Read(cx), ComplexBoundaryHom.Read(cx)
cycle := b.Have("u lies in P(m + 1) and d(m + 1) kills it, two boundaries in a row being zero", "u ∈ P(m + 1) ∧ d(m + 1)(u) = zero'",
	ByChase(Depth(0), modules, boundaryMaps, ComplexBoundaryTwice.Read(cx), boundary))
```

The complex's laws reach the closer as readings at the resident fact
`cx`, each a ∀-fact over degrees the closer reads at the degrees the
leaf spells (`ComplexBoundaryTwice` is stated at `n + 2`, the leaf
spells `m + 1 + 1`: the nat ring normalizer bridges the two); `boundary`
is the leaf's `u ∈ image(d(m + 1 + 1), P(m + 1 + 1))`, whose preimage
the closer introduces itself.

A guarded premise is retried after equation saturation and after new
pull-backs: once the diagram decides its guard, its consequent joins the
same fixpoint. An undecided guard supplies no consequence. This adds no
pull-back round and does not extend the closer's degree horizon. A
premise installed in the closer's clause form — `¬p ∨ q`, the form a
full-tuple cite takes where the context does not hold its guard as
written (`DoubleTotalCoordinate.At(V, D, p + 1, q, u)` states its guard
at the degree `(p + 1) + q`, the leaf holds it at `p + q + 1`), under a
∀-prefix for a partial tuple — is read as the guarded law `p ⇒ q` it is,
its guard decided at the canonical degree like any other.

What the closer reads, what it decides and what stays out are the
Playbook's §"Diagram chases in `by {chase}`". Deterministic and
bounded: the composite records the call (the closer and its depth) and
no key, and replay re-runs the same reading. A leaf it does not close
fails with the chase's report — the rounds run, the element and the
module the goal stayed outside, the hypotheses it could not read — and
never falls through to the refuter. The session spelling is
`by {chase:{depth:k}, by_hyps:[…], with_lemmas:[…]}`.

#### Denote — the abbreviation family

Denoting is "let *d* = ⟨big term⟩": a repeated subterm is replaced
throughout the goal by a fresh variable, and the defining equation
joins the hypotheses. It is ordinary mathematics, and the CNF stage
likes it — a named term is a stable opaque atom.

The family comes in two halves, and the difference is the whole
point. An EXPLICIT denote says WHICH term is being named. A SEARCH
denote says only how big a term has to be before a heuristic picks
one. **Hand-written proofs use the explicit forms.** The search forms
are the engine's internal stage and are not on the surface at
all.

##### Explicit — the authoring forms

| Form | Kind | Use |
| --- | --- | --- |
| `a.Denote(name string, term TermLike) Fact` | `Argument` verb | The abbreviation. Denotes on the spine and RETURNS the equation `name = term` as a `Fact` for later premise lists. The term as `a.Term(text)`, a typed value or a core term. |
| `DenoteTerm(name string, term Term) Step` | `Step` | The bare ministep, for a `Case` body / `Chain` that has no `Argument`. |
| `a.Let(name string, term TermLike) Fact` | `Argument` verb | The DEFINITION — "let w := ⟨term⟩" (the term as `a.Term(text)` in a hand-written body, or a typed value, or a core term): the equation joins the hypotheses, every occurrence of the term — in the hypotheses and in the conclusion — becomes the name, and the goal KEEPS ITS FORM (it is not negated into the hypotheses); the term need not occur. A definition comes before the facts that spell its term, as in prose: a handle taken earlier on such a fact follows it through the Let, however many hypotheses the Let rewrote beside it (the step records each hypothesis's successor). Returns the defining equation. |
| `a.LetAs[φ](name, text string) (*Expr[φ], Fact)` | `Argument` verb | Let with the text read at φ — a polymorphic constant the text leaves bare takes φ's instance, a text that cannot be read at φ is refused naming both types — returning the name as its typed handle beside the equation. Same step as `Let`; the handle is what `a.TermAs[φ](name)` would read after it. |
| `LetTerm(name string, term Term) Step` | `Step` | Let's bare ministep, and what a session's `let` tactic records and emits as. |
| `DenotedAs(name string, term Term) ByShape` | `ByShape` value | Shapes a `By`'s context: denote, then `Basic()`, then the close. |
| `DenoteRefuteAs(name string, term Term) Action` | `Action` | `Chain(DenoteTerm(name, term), Basic(), CnfRefute())` — the standard denote-close. |
| `HilbertDenoteTerm(name string, term Term) Step` | `Step` | Same for an ε-term: `term` must be `εx.P(x)`; it is replaced by `name` and its defining existential joins the hyps. |
| `HilbertDenotedAs(name, term)` / `HilbertDenoteRefuteAs(name, term)` | `ByShape` / `Action` | ε twins of `DenotedAs` / `DenoteRefuteAs`. |

`a.Denote` and `a.Let` are the members of the deduction vocabulary
next to `Have` and `Obtain` with **no proof obligation**: `Have`
introduces a fact that must be proved, `Obtain` unpacks an `∃` that
must be shown inhabited, `Denote` gives a long term the goal already
carries a short name, `Let` defines a name for an object the argument
is about to build with.

**Which of the two.** `Let` is the mathematical naming — "take
w = ‖v‖·u − ‖u‖·v", "let B be Σᵢ ‖f(eᵢ)‖" — and it is goal-preserving:
the definition `w = term` joins the hypotheses, the goal keeps its form,
and the term need not occur anywhere yet (it usually does not; the
argument is about to use it). Later claim texts spell `w`, and the
returned `Fact` is the definition, for the premise lists that unfold
it. `Denote` is the abbreviation at a ⊥-form close: it requires the
term to occur, replaces every occurrence, and moves the spine to ⊥-form
(the goal's negated conclusion joins the hypotheses, like a
`SupposeNot`), so the block's terminal `Show` closes by refutation —
the shape a refute-heavy argument on a big repeated term wants. Neither
decides what the CLOSER treats as an atom: a resident `w = term` may be
unfolded either way by the refuter, so a leaf that must read `w` as one
unknown still says so with `DenotedAs` (the leaf-local shaping).

```go
d := a.Denote("d", v.mk_nadd(n.To(v.sum(v.at(x, n), v.at(y, n)))))
a.Show("both sides are d", By(d, lemma3))
```

```go
a.Show("re-bracket each side and close",
    By(DenotedAs("s", add(add(fx1, fy1), add(sx2, sy2))), sum,
        p4.At(fx1, sx2, fy1, sy2)))
```

**Panic contracts** (all of them fire AT THE STEP, which is the
reason the explicit form exists):

- the term does not occur in the goal's hypotheses or negated
  conclusion — *"denote(⟨term⟩): the term does not occur …"*. A denote
  for something that is not there is a stale line of the proof.
- `name` is already free in the goal — *"denote: the name … is already
  free in the goal"*. The name is part of the record, so it is never
  silently renamed.
- `HilbertDenoteTerm` on a term that is not an ε-term.
- `Argument.Denote` with an empty `name`.
- inside a `By`, an explicit shaping that applied to NO leaf —
  *"By: the explicit denote shaping named a term that no leaf
  contains"*. (Under `Broadcast` the shaping runs per leaf and a leaf
  without the term legitimately skips it; applying nowhere at all is
  still the drift the form exists to catch.)

A denote whose term is ALREADY denoted (some hyp is `v = term` for a
variable `v`) declines rather than duplicating the abbreviation, so
the step reports failure.

Source: `prover/proof/derive.go` (`Argument.Denote`),
`prover/proof/script.go` (`DenoteTerm`, `HilbertDenoteTerm`),
`prover/proof/fact.go` (`DenotedAs`, `HilbertDenotedAs`),
`prover/proof/action.go` (`DenoteRefuteAs`,
`HilbertDenoteRefuteAs`), `prover/tactic/denote_tactics.go` (the
transform).

##### Search — `Denote(size ...int)` / `Denoted(size ...int)` / `DenoteRefute(size ...int)`

**These are an INTERNAL SEARCH STAGE, not authoring verbs**, and they
are excluded from the bare-name surface, `library/authoring`
(`library/registry/aliasgen`'s `retiredNames`): a proof
file writing `Denote(8)` does not compile, and inside a chapter
package the name `Denote` means `Argument.Denote`.

They remain exported from `prover/proof` for one consumer: the
`auto` / `expand` pipelines and the `denote` session tactic, which run
the selection heuristic (`ext.FrequentSubTerms` above the threshold,
then `ext.HilbertSubTerm`) as part of search. A search firing records
the term it chose, and emit renders that explicit form; only a
degenerate firing that placed its selection nowhere is recorded without
a choice, and emit renders it as the search form.

The size is OPTIONAL and defaults to `_DENOTE_SIZE_THRES`
(`prover/proof/utils.go`) — the threshold `auto` and `expand` run at.
Passing more than one panics.

A search denote that finds nothing over the threshold FAILS
(`ministep Auto Denote. failed`) rather than passing as a no-op.

##### What the record carries

`AutoDenoteProto` has `size_threshold`, `hilbert`, `term` and `name`.
A **search** firing RECORDS ITS CHOICE: the selected term is
written into the section pool and the minted variable's name alongside
it, so replay reproduces the decision instead of re-running the
heuristic against a goal that may have drifted upstream. `term == 0`
is the proto3 zero and means "heuristic mode": a proto recorded with
no term re-runs the search.

#### `HypHandle.SplitIff(both, neither)` / `HypHandle.SplitImply(cases ...Case)`

Content-addressed forms of `SplitHypIffAt(idx, …)` /
`SplitHypImplyAt(idx, …)` — the handle resolves the index at run time
(same ministep at the resolved index: tree-identical, zero pb churn),
so no integer hyp address appears in blessed text:

```go
cancelIff := NewHypHandle("cancelIff")
… cancelIff.From(Fact("nat_order.LessEqMulCancel", n0, d, t)) …
cancelIff.SplitIff(
    BothHold("…", …),
    NeitherHolds("…", …),
)
```

Binding limit (same as every handle surface): the hyp must be
bindable at its introduction (`From` on the introducing action /
`FromResident` by content). A hyp introduced EARLIER whose duplicate
cite installs nothing ("install added no hyp") cannot bind — such
sites stay index-addressed (the `mul_sym` Rw-site class;
`proofs/real/tower/internal/eudoxus_slope/algebra.go`'s `Mul` member carries
the worked example with a site comment).

Source: `prover/proof/hyp_handle.go`; exemplar:
the `homogeneous` member in
`proofs/real/tower/internal/eudoxus_slope/toolkit.go`.

#### `SimpRule` / `Fwd(rule)` / `Rev(rule)` / `Script.SimpWithOriented(rules ...SimpRule) Step`

Per-rule orientation for simp-rule sets — the call-site spelling of
`SimpWithFlipped`'s parallel `[]bool` vector (which forced the reader
to align booleans against the rule list positionally):

```go
Expect(ctx.SimpWithOriented(
    Rev(MakeFact(ctx.MakePropText("∀x y z:hreal. x * y + x * z = x * (y + z)"))), // fires r→l
    Fwd(MakeFact(ctx.MakePropText("∀x y:hreal. x * y = y * x"))),
), …)
```

Builds the IDENTICAL step (and proto) as the equivalent
`SimpWithFlipped` call — converting between the spellings never
re-records a pb. `Rev` on a non-equation rule fails at resolve
time exactly as `flip:true` does on the session surface. A rule
spelled by NAME (an entry var, `ctx.Dep(name)`, a typed instance) is
served in its stated form, and the marker reads against that
statement — the `Simp` row of the cheat sheet has the contract.

Source: `prover/proof/step_composite.go`; exemplars:
the `LessEqMul` and `MulLeftInverse` members in
`proofs/real/tower/internal/nonneg_real_formal_diff/nonneg_real_formal_diff.go`.

**`RuleSet(rules ...SimpRule) SimpRule`** bundles rules into one, so a
chapter can export a rewrite it performs as a unit and a consumer names
it beside its own rules: `int_construction.InReals` is the embedding of
ℤ in ℝ as rules — every integer equation becomes one between
representatives, every comparison its definition, every operation
crosses by its bridge — and a ℤ chapter borrowing a theorem of ℝ writes
`Simp(int_construction.InReals, Fwd(DotBridge))`, then cites the real
theorem (`vector/lattice`'s `DotPosLe`, `NullVectorOrthogonal`). `Simp`
and `SimpWithOriented` flatten a set in place: the step built, recorded
and rendered is the flat list, a member of the set that does not fire
costs nothing, and a set has no orientation of its own (`Rev` on a set
is refused).

#### `Unfold(d Definition) Action`

Opens a definition: the constant `d` defines is expanded on the whole
leaf.

```go
a.Do(Unfold(real_order_ring.RealGeDef), Cite(LessEqAddLeft))
```

`d` is the definition itself, a `proof.Definition`: the typed wrapper of
the entry whose door defined the constant (`set_basic.SubsetDef`) or a
structure (`group.GroupOn`, or one `StructureOf` names). A constant the
logic defines before any chapter has no entry and is not unfolded: `∃!`
is opened by `a.Unpack` on a fact it heads and read by every closer
through normalization. The
generator gives the method to the wrapper of an entry a proof may open —
a `Define` or `DefineSpec` entry, one constant — so a theorem named
where a definition belongs does not compile, and neither does a constant
no entry defines. The step it records is `DefExpandStep`'s at the
constant's abstract type: the walker instantiates the definition at each
occurrence.

**The member stands on the definition.** An opening is a dependency:
the recorder writes the entry that defines each constant a member's
proof opens into the family blob (`member_unfolds`, beside
`member_deps`), the registry reads it back among the member's
dependencies (`ProofEntry.DepEntries`), and a replay fails a build whose
openings drifted from the row. So `deps`, `dependents`, a scoped replay
and the card frontier see a member that opens `subset` standing on
`SubsetDef` as they see one that cites it. The definition is read off
the constant, so a build is not served the entry
(`ProofEntry.ServedDeps`).

**The goal and every hypothesis.** The unfold rewrites the goal AND every
resident hypothesis, and its tidy pass reaches hypotheses the constant does
not occur in: a resident conjunction is split and a fact is re-normalized.
No resident fact is applied: the opened goal keeps every term a resident
equation could rewrite and every clause a resident fact would close, and
the author rewrites or closes it (`eq.Rw()`, `a.Simplified(h, Fwd(eq))`,
`By(Normalized, clauses…)`) where the proof needs it. A handle
taken before the step follows its hypothesis through the opening and the
re-normalization, however many hypotheses the step touches; a handle into a
hypothesis the tidy splits fails at its next use, naming the Unfold, and a
rewrite that finds nothing left to rewrite names the side that occurs
nowhere and the step past which it stopped occurring (`f(a) last stood in the goal before step "Rw on hyp 1", which rewrote it away`).
To open the goal alone,
rewrite it by the definition entry, `Simp(Fwd(BallDef))` (a Simp touches no
hypothesis). A session `def_expand` reports `context_changed` when an
original hypothesis is absent from a surviving leaf, naming its old index
and statement; inspect that leaf for the replacement and current indices.
A closed goal has no surviving context to report. To open one fact,
`a.Unfolded(h, CDef)` (below); to unfold
nothing and keep every fact named, pass the definition itself as a premise —
its stated entry, `By(f₁, f₂, nat_congruence.CongDef)`, which the apply rung
reads one named premise deep and closes keyless (a membership through an
inclusion, `By(LeftIdentityOn, group, memberOfH, hInC, set_basic.SubsetDef)`,
closes the same way). The rung reads the definition at the instance the
goal pins and meets the goal up to its identity — βη and the readings —
never through an equation, so where the opened side reaches the goal only
by a rewrite (`inv(inv(t))` against `t`), open it by `Simp(Fwd(<Def>))`,
rewrite, then close. Or pass its normalized reading,
`ctx.ConstDefNormalized("nat_cong")`, which the refuter reads and records; where the `Unfold` stays, state the
conjunctive facts its tidy would split before it, or use their handles before it. The
reach is the step's contract, and recorded proofs lean on it — some close
only by a hypothesis the constant does not occur in — so the goal-only
spelling is the `Simp` above, and no narrower `Unfold` is pending.

**The Fact-level face: `a.Unfolded(h, CDef)`.** `Unfold` opens the
constant on the WHOLE leaf — the goal and every hypothesis — and its
residual simplification splits any conjunction the opening leaves in a
hypothesis, so a handle that pointed into one has no single successor
past the step (a handle into a hypothesis the opening merely rewrites
follows it). Where the
mathematics is "this hypothesis, read by its definition" — a
convergence read as its ε-N statement, a polynomial read as its
coefficient sum before an `Unpack2` — the verb is `a.Unfolded(h, CDef)`:
it returns the opened fact as one new resident Fact and touches
nothing else. It records the hand-written idiom exactly (a `Have`
whose claim is the unfolded statement, closed by `Unfold(CDef)`), with
the claim computed by the same walker the step runs, so a converted
site moves no key. The root-of-section case, where the antecedent to
open is still in the goal, is `Opening(Unfold(CDef), func(a, …, h Fact))`;
what neither gives is the halves of a conjunctive Fact.

Source: `prover/proof/step_composite.go`, beside `DefExpandStep`;
`Argument.Unfolded` in `derive.go`.

#### `ByInduction(principle CiteTarget, rest ...any) Action`

Closes a leaf by **citing** an induction principle: proves one
obligation per case of the principle, each under its own label, then
closes by `By` over those obligations, the principle, and any extra
premises the conclusion needs.

```go
a.Show("by induction on the finite set s",
    ByInduction(finite_set.FiniteInduct, finiteS,
        Case("at ∅: the image is that empty set, which is finite outright",
            By(noPoints, FiniteRules)),
        Case("across insert: one more point in the source is one more in the image",
            Derive(func(b *Argument) { … }))))
```

**The predicate is read from the goal where the cite stops before it.**
A principle cited bare, or at its parameters alone, is run at the
predicate the goal reads, by one of two readings:

- *At a premise.* A principle concludes `∀x̄. G(x̄) ⇒ P(x̄)`. An extra
  that states the guard `G` at some terms — `finiteS` above, a
  `transitive_closure(R, u, v)`, a derivation — fixes the index at
  them, and the parameters the cite left open with it, and the
  predicate is the goal abstracted over the index, `λx̄. goal[index :=
  x̄]`. This is "by induction on the walk": the fact is named, the
  predicate is not. A binder the principle states after its predicate
  is fixed the same way, by the fact that states the guard it stands
  in: `FiniteInductFreshOn` binds `∀P Q s.` and guards `∀y. y ∈ s ⇒
  Q(y)`, which the fact `∀x. x ∈ s ⇒ F(x) ∈ c` states at `Q := λx.
  F(x) ∈ c`, so `ByInduction(finite_set.FiniteInductFreshOn, finiteS,
  membersInC, Case…)` writes neither. Where several listed facts state
  a guard, the first fixes the index; a goal that does not mention the
  index so fixed is refused, naming it.
- *Off the goal's binders.* With no extra stating the guard, the goal
  is the principle's conclusion itself, `∀x̄. G(x̄) ⇒ φ(x̄)` with the
  guard among its antecedents, conjoined or curried, and the predicate
  is its body without the guard — strong induction at a Have's
  `∀m. ∀r. … ⇒ …`. A binder stated between the predicate and the
  index is fixed by its guard among those antecedents, and the tuple
  runs on through it.

`Generalizing(h₁, …, hₙ)` among the extras names resident hypotheses
about the index that the induction must carry: the predicate is then
`λx̄. (h₁ ∧ … ∧ hₙ) ⇒ goal`, and the terminal discharges it at the
index from those facts. None is gathered on its own: a hypothesis on
the index that the cases do not need stays in the context.

```go
a.Show("by induction, every finite set of points algebraic over K generates a finite extension",
    ByInduction(finite_set.FiniteInduct, finiteS, Generalizing(sInL, algebraic),
        Case("no point adjoined: K(∅) = K", …),
        Case("one more algebraic point adjoined", …)))
```

The predicate is **written** — `At(principle, params…, P, index…)`, as
below — where it is not the goal: an induction on a compound term (a
degree, a cardinality, `s ∖ t`), where the predicate says how the term
enters and usually generalizes the object (`λn. ∀f. degree(f) = n ⇒
…`); a claim strengthened for the induction, or generalized over
another variable (`λφ. ∀ρ. …`); and an unguarded principle at a goal
that is an instance (`Q(k)` with `k` fixed), which names neither a
fact nor a binder to read the index from. A reading that does not fit
panics with the guard a premise would state and the reason the goal's
binders did not serve.

```go
// the predicate written: induction on the degree of p, every polynomial of that degree at once
ByInduction(At(nat_order.StrongInduction, sameDegree, degree), Normalized, Case(…))
```

`rest` is the extra premises first, then one `Case` per obligation in
the principle's own case order (a `Case` followed by an extra panics —
the order is what makes the cases read against the principle).

**The session twin is `by_induction`** (the tactic table): the same
principle under `lemma`, the same tuple under `term_specialize`, the
extras under `by_hyps` / `with_lemmas`; it leaves one leaf open per
obligation and records the asserts and the by this verb records, so a
session rehearses the induction the file will carry and `emit-section`
writes it back as this verb.

**This is not `a.Induct`.** `a.Induct(v)` drives the induction
TACTIC: the principle is the one the datatype comes with, the engine
finds it from the variable's type, and the goal itself is the
predicate. `ByInduction` cites a principle as an ordinary theorem — an
inductive definition's rule induction (`finite_set.FiniteInduct`), a strengthened
variant, a wellfoundedness principle — at a predicate that is the goal
read at the index, or one the proof writes.

**What it removes.** The obligations of a cited induction are the
principle's own case hypotheses read at the chosen predicate, so
writing them by hand means performing the substitution and the
β-reduction in Go source — in practice a `fmt.Sprintf` interpolating
the predicate's body at two or three places, i.e. the same mathematics
stated three times for the reader to check agrees. ByInduction computes
them from the principle. The Case LABELS are what it cannot compute,
and they are the point: a `ByInduction` whose labels are "base" and
"step" has discarded the only content the verb left for the author.

**The predicate is the head of the principle's conclusion, and the
tuple is read as the terminal grounds it.** An induction principle
concludes its predicate applied to the index — `∀x0 x1.
transitive_closure(R, x0, x1) ⇒ P(x0, x1)` — past the conclusion's own
binders and guards, and that head is the predicate. A PARAMETER (the `R`
an inductive definition minted with parameters states before `P`) occurs
there only under the minted constant, never as the head; reading the
predicate off the CASES instead ("the binder the cases apply") was right
for every parameter-free principle and wrong for every parameterized
one, whose first rule applies the parameter too. The obligations are the
antecedent at EVERY leading binder the tuple grounds — the rules mention
the parameter as they mention the predicate — so a parameterized
principle is cited at its parameters first, then the predicate, then the
index, in the stated binder order the generated typed `At` also spells:

```go
ByInduction(TransitiveClosureInduct.At(R, reachesInS, x, y), reachesInR,
    Case("every R-step is an S-step, and S's first rule puts it in S's closure", By(containedInS, TransitiveClosureRules.At(S))),
    Case("S's second rule: two stretches of its closure meeting at a point make one", By(TransitiveClosureRules.At(S))))
```

The tuple is read by the SAME function the terminal's grounding uses
(`reorderWitnessesToInstall` over the statement's guarded prefix), so
the obligations are read at the instance the terminal applies. A tuple
whose positional reading is ill-typed is permuted by type where the
binder types settle it — peano's `At(Induction, point, pred)` against
`∀P. … ⇒ ∀n. P(n)` (where `n` is bound twice and no slot is
name-addressable) still reads right — and a parameter and a predicate of
ONE type (`A → A → bool` both, for a relation's closure) are told apart
by position, which is exact because the statement names them. A tuple
that stops before the predicate, or before a parameter the cases
mention, panics naming the binder and the order to cite in; a
`Where`-pinned principle is refused (it would enter the terminal By as
the apply rung's head, not as the grounded tuple the obligations were
read at).

**Accepted principle shapes.** `∀P… . obligation₁ ∧ … ∧ obligationₙ ⇒
conclusion`, with the obligations either conjoined
or curried as an ⇒-chain — both flatten the same. The
conclusion is not consulted: `P(x)`, `∀x. P(x)` and a guarded
`∀x. finite(x) ⇒ P(x)` are all fine, and the guard is discharged by an
extra premise (that is what `finiteS` is doing above). Obligations
carry the PRINCIPLE'S own binder names, so two members citing one
principle receive the identical obligation.

**Records nothing new.** The emitted proof is one `AssertStep` per
obligation followed by the terminal `By` — exactly what the
hand-written spelling emits — so converting a site whose Haves state the
obligations under the principle's own binder names **moves no recorded
CNF key** (where the motive is the rule set's own parameter, as in
`relations/closure.Closed`, one obligation normalizes to ⊤ and is
asserted as a Case closed by `Basic()`). A
hand-written Have spelled under OTHER binder names (`∀u v.` where the
principle says `∀x y.`) is the same claim and a different leaf once a
Case body Fixes it: the Skolem constants carry the binder names and the
CNF keys hash them, so converting it re-records — the names, not the
verb. Run the family recorder and GC after such a conversion.

**The principle installs in its stated form.** The terminal `By`
receives the principle as its file states it — the form the
obligations were read off — whatever spelling named it: an entry var,
a dep name, a typed instance (`statedPrinciple`, induction.go). That is
not what `By` makes of a named premise on its own: a witnessed named
premise takes its stated form — read at the tuple as the telescope at
its prefix: a card `∀R M N p u. S(R, M, N) ∧ u ∈ … ⇒ …` at `(R, M, N)`
is read `∀R M N. S(R, M, N) ⇒ ∀p u. u ∈ … ⇒ …`, the hypotheses about
the grounded binders ahead as the guards and the rest standing in the
instance — only where the tuple grounds every binder ahead of the first
guard and every guard is supplied — resident as written or
conjunct by conjunct, or closed by the context as a goal, one apply
deep — and the closer's CLAUSE form otherwise (step_by.go,
`statedGuardsSupplied`) — and a principle
cited at its predicate with the index left universal is a partial
tuple that the executor COMPLETES from the goal where it can: the
stated conclusion is matched against the goal with the author's
witnesses seeded (the apply rung's head matcher), the index read off
it, and the premise takes its stated form exactly where that form's
guards are then supplied — the obligations resident, as written or
conjunct by conjunct — so `By(At(principle, P))` with the obligation
named beside it closes by one modus ponens; where the guards are not
supplied, or the statement carries free term variables, the tuple
stays partial. A tuple the executor cannot complete still takes the
stated form where it is exactly the leading ∀-binders of a statement
with no free term variables and their guards are supplied; any other
partial tuple takes the clause form. The clause prefix is in Normalize's order, which the
author never sees (`nat_order.StrongInduction`'s is `∀n.∀P.…`); a
tuple of one predicate is read at `P` all the same — the executor moves
the stated binders to the front of the clause's ∀-block — but the
clause form has dissolved the `⇒` (`nat_order.StrongInduction` becomes `∃kʹ.∀m. P(n) ∨
(¬P(kʹ) ∧ …)`), which hands the closing modus ponens to the CNF
refuter: it finishes at a shallow or OPAQUE predicate and not at a
transparent one with quantifier alternations in its body (`λa. ∀b.
∃d. … ∧ (∀e. …)`, the gcd-existence predicate, ends in
`ByInduction(…): By: CnfRefute failed` with every premise present).
Under ByInduction the entry spelling and the raw `ctx.Dep(name)`
spelling are therefore one install, and the entry is the spelling; a
normalized target (`ctx.DepNormalized(name)`) has no antecedent to
read cases off and is refused.

**Deep transparent predicates: add `Normalized`.** The grounded
principle keeps its λ-redexes, and at a predicate of that depth the
proved obligation never α-meets the antecedent without the shaping:

```go
ByInduction(At(nat_order.StrongInduction, hasGcd),
    Normalized, // β-collapse the grounded principle so its antecedent meets the proved step
    Case("…", Derive(func(c *Argument) { … })))
```

Whether a site needs it is measured, not predicted: the recorder's S7
audit reports a `Normalized` the close does not use. In
`sets/finite_set` the audit keeps it at `FiniteTransitivityChain`,
whose property is an implication with a ∀-quantified antecedent, and
`FinitePowerset` closes without it.

**Panics**, all naming the principle: a Case count that disagrees with
the principle, printing every computed obligation (also the cheapest
way to see what a principle asks for); a cite before the predicate
whose goal fits neither reading, whose index is not a tuple of
distinct variables, or whose index the goal does not mention; a binder
stated after the predicate that no listed fact fixes, naming the guard
a fact would state; `Generalizing` beside a written predicate, or with
no premise to fix the index; a `Where`-pinned
principle; a conclusion not headed by one of the leading binders; a
resident hypothesis passed as the principle; a statement with no
antecedent to read cases off.

Source: `prover/proof/induction.go`, `prover/proof/induction_motive.go`.

#### `PairCollapse(fst, snd Prop) Action`

Drives literal-pair projection redexes `fst((a, b)) → a` /
`snd((a, b)) → b` to fixpoint on the current leaf — the replay-side
counterpart of the engine's ambient `runAutoFSTSND` pass (which fires
after any tactic that exposes a projection over a concrete pair
constructor; an entry's Build replays only its recorded ministeps, so
the same def-expand in Go leaves the projections resident). Each
iteration commits one `_LeanRwTactic` ministep + one `_TypeInstStep`
discharging the rule-reproduction child from the polymorphic rule —
pure sugar, no new proto tag.

`fst` / `snd` are the polymorphic projection certificates. A chapter
writes `pairs.Collapse(ctx)` (`cartesian/pairs`), which is
`PairCollapse(ctx.Dep(Fst), ctx.Dep(Snd))` from the package
that can name the two entries — the caller reads `pairs.Fst` /
`pairs.Snd` through `ctx.Dep`, which claims them, and its recording
carries them as deps.

Panics: nil rule; a rule whose statement does not mention its
projection const (swapped-args guard, at construction); a leaf with
no projection site to collapse (apply-time authoring error, not a
silent no-op); a rewrite or discharge that fails mid-fixpoint; more
than 64 iterations on one goal (runaway).

Source: `prover/proof/step_composite.go` +
`prover/proof/step_composite_test.go`. It is a standalone Action,
not a `DefExpandStep` variant, and pure sugar with no proto tag of
its own. The site scanner `FindPairProjectionSite` is exported and
shared with the engine pass.

```go
Chain(
    Unfold(IntLcmDef),                // exposes fst((c,d)) / snd((c,d)) redexes
    pairs.Collapse(ctx),              // reduces every literal-pair projection to fixpoint
    /* … residual … */
)
```

The fixpoint handles NESTED redexes in one call — only a new unfold
LAYER (e.g. a follow-on `def_expand` that exposes fresh projection
sites) needs a second `PairCollapse` call. A reflexive projection-free
residual is closed by the last rewrite's own eqSimplify: `PairCollapse`
alone can prove `f(fst((c, d)), snd((c, d))) = f(c, d)`.

#### `ACRegroup(assoc, sym Thm) Action` / `ACRegroupWith(d *ac.Deriver) Action` — the goal face of the AC kit

The AC kit (`prover/solver/ac`) derives `⊢ lhs = rhs` for two ground sums
over one associative-commutative binary op ⊕ that flatten to the same leaf
multiset — the `assoc` / `sym` instances composed at the `PropWrapper`
layer (kernel-checked `Refl` / `Apply` / `EqSym` / `EqTrans`, never a
recorded per-instance tactic chain), so only the FINAL equation touches
the goal tree; no CNF refute, no search, no cache state, and a Build
re-run replays it byte for byte. It has three faces.
`By(ac.New(assoc, sym).Eq(lhs, rhs))` is the premise face (§"The math
layer"). `CiteACRegroup(assoc, sym, lhs, rhs)` installs the equation as
a hypothesis with its endpoints spelled; no chapter writes it. `ACRegroup`
is for a leaf whose goal IS the rearrangement — a member whose whole
statement is `m ⊕ (n ⊕ p) = n ⊕ (m ⊕ p)` — where spelling the endpoints
would write the equation twice, once as the section statement and once
as a pair of hand-built terms: it reads them off the leaf, and the
derivation is the same pure function of `(assoc, sym, lhs, rhs)`.

```go
// the goal is the rearrangement — no endpoints to spell
ACRegroup(ctx.DepNormalized(real_construction.AddAssoc),
    ctx.DepNormalized(real_construction.AddSym))
```

`ACRegroupWith` takes a `*ac.Deriver` the caller already holds, so a
family that states its assoc/sym pair once (`func addAC(ctx *Script)
*ac.Deriver` in `family.go`) reaches BOTH kit faces from that one
statement — `By(addAC(ctx).Eq(lhs, rhs))` for the premise face,
`ACRegroupWith(addAC(ctx))` for the goal face:

```go
ACRegroupWith(addAC(ctx))     // same as the four-line spelling above
```

Note the layering, because the natural guess does not compile: this is
NOT a method `(*ac.Deriver).Regroup()`. `proof` imports the solver kits,
so a kit cannot name `Action` — the same constraint that makes a kit
supply a premise through `SelfProvingPremise` rather than by returning
a `Fact`.

Panics (soundness-first): no unsolved leaf; the leaf's goal is not an
equation; the two sides are not AC-equal (via `ac.Validate`, which
prints both leaf lists).

Derivation (deterministic): let canon be the right-associated chain
over `lhs`'s leaves in first-appearance order. Each side is proved
equal to canon — flatten by recursion on the ⊕-tree (assoc instances +
congruence), then reorder by selection sort (each adjacent swap is one
assoc⁻¹/sym/assoc sandwich) — and the two halves compose by
`EqTrans` + `EqSym`.

Orientation auto-detected: `assoc` may be stored as either
`(m⊕n)⊕p = m⊕(n⊕p)` or `m⊕(n⊕p) = (m⊕n)⊕p` — the derivation flips as
needed. Op is read off the `assoc` statement; the two certs must
agree on ⊕. Works for any AC op whose certs are supplied — nothing
is hardcoded to a particular law.

The kit refuses, on every face: nil arg; `assoc` / `sym` carrying hypotheses; wrong assoc
or sym shape; disagreeing op; `lhs` / `rhs` off the certs' operand
type (a polymorphic cert must be type-specialized first);
`lhs` / `rhs` α-equal to one of the certs' OWN equation sides (a lemma
PATTERN passed where a ground sum belongs); `lhs` α-equals `rhs`;
flattened leaf multisets differ (prints both lists).

A sum whose LEAVES merely share a name with a cert binder derives
normally — instantiation runs through the kernel's capture-avoiding
`ConclForAllInsts`.

Source: `prover/proof/fact.go` (the Action shell) +
`prover/solver/ac/` (the derivation) + `prover/proof/fact_test.go`
(its tests).

#### `CalcOrder{…}.Calc(from Term, legs ...CalcLeg) Action` — mixed-relation chains

The chain combinator for arguments that interleave an order with an
equivalence — the shape `CalcRel` (single relation, single `Trans`
certificate) cannot express:

```
x·y  ≤  x·y + x·d   [self-add]
     ≈  x·(y + d)   [distributivity, flipped]
     ≈  x·z         [well-definedness transports z ≈ y + d]
                    ⟹  x·y ≤ x·z
```

Without it such proofs are spelled as a pile of consecutive unground
`UseLemmaExact` installs plus one `CnfRefute`: the chain survives only
in the doc comment while the refuter reconstructs it invisibly.
`CalcOrder` makes the narrated chain the checked structure — every
link is an asserted, independently closed leg with its own label.

Theory-FREE: both relations and all three composition laws arrive as
parameters, exactly as `CalcRel`'s `Rel` / `Trans` do.

```go
type CalcOrder struct {
    Le, Eq  func(a, b Term) Prop  // the two relations as Prop builders
    LeTrans CiteTarget            // ∀a b c. Le(a,b) ∧ Le(b,c) ⇒ Le(a,c)
    EqTrans CiteTarget            // ∀a b c. Eq(a,b) ∧ Eq(b,c) ⇒ Eq(a,c)
    EqToLe  CiteTarget            // ∀a b.   Eq(a,b) ⇒ Le(a,b)
}
```

A certificate is any fact a `By` takes as a premise: the fold hands it
to the chained fact's close at the tuple it computed, as the
hand-written `By(link₁, link₂, trans.At(a, b, c))` does. So it may be a
law named by its entry (`nat_order.LessEqTrans`), a certificate
(`MakeFact(ctx.DepNormalized(X))`), or a **resident fact** — the
transitivity rule of an inductive relation, read out of its rules with
`a.Conjuncts`. What the fold asks of it is that its open binders are
the composition's own terms in order, so the law of a relation with
parameters is handed over at them, `DerivableTransitive.At(E, O)`; the
rule read out of `DoDerivableRules.At(E, O)` already is. ⇒-form and
∨-form spellings both work, the closer sees through the propositional
shape. Legs' `to` terms reach the `Prop` builders
exactly as passed, as `Term`; a vocabulary handle's `Apply` takes
`Term`, so a builder applies its handle to them directly.

**Leg tagging.** Legs are built by `LeLeg(to, label, body…)` and
`EqLeg(to, label, body…)` — same shape as `Leg`, plus which relation
the link travels. The untagged `Leg` is rejected here (a mixed chain
cannot guess), and conversely `LeLeg`/`EqLeg` are rejected by `CalcEq`
and `CalcRel.Calc`, which hold no certificate for a second relation.

**Fold.** From the running fact `rel(from, prev)` and the new link
`rel(prev, to)`:

| running | link | ⟹ | how |
|---|---|---|---|
| ≤ | ≤ | ≤ | `LeTrans` |
| ≈ | ≈ | ≈ | `EqTrans` |
| ≤ | ≈ | ≤ | `EqToLe` lifts the LINK, then `LeTrans` |
| ≈ | ≤ | ≤ | `EqToLe` lifts the CHAIN, then `LeTrans` |

so the running relation is ≤ as soon as any leg is ≤, and ≈ only while
every leg has been ≈. **Every grounding tuple is COMPUTED** from the
leg terms — `(from, prev, to)` for a transitivity, `(prev, to)` or
`(from, prev)` for a lift — never spelled by the author. Only the
certificates a chain's tags actually reach are required; an all-`LeLeg`
chain needs no `Eq`/`EqTrans`/`EqToLe` at all and produces the same
tree as the `CalcRel` it generalizes.

**Desugar.** One `AssertStep` per link, plus one per chained fact from
the second leg on; each chained fact's proof is one PREMISE-SCOPED
close: the chained fact closes from exactly its two links and the
transitivity (and lift) instances — the kit's certificates at the
computed tuples, premises of that close — every other resident
hypothesis cleared first — so a chain is usable inside a
context full of resident ∀-facts, and a failure there is a mis-tagged
leg (or a certificate that does not compose the two links), never a
missing premise or a key to record. All facts end resident; exactly one
unsolved leaf remains, so it composes as a `Deduce` item.

**Terminal chains.** If a fact the chain would assert is α-equal to
the goal, the chain has ARRIVED: it is proved against the goal instead
of asserted beside it, and the block CLOSES rather than leaving a leaf.
Asserting it is not an option (`tactic.AssertTactic` refuses a claim
α-equal to the goal) and not a loss — nothing remains to assert it
for. This is `CalcEq`'s mode, reached by a chain whose endpoint is what
was to be proved. Such a chain must be its `Deduce` block's final item
or stand alone in the enclosing `Chain`.

Panics on: fewer than two legs; a leg with no target term (`FinalLeg`
is `CalcEq`-only); an untagged leg; a certificate the chain's tags
require left nil (names which composition wanted it); a leg whose
proof does not CLOSE its link (names the leg and prints the open
leaves); a leg following the chain's arrival at the goal.

Source: `prover/proof/calc.go` (beside `CalcEq` / `CalcRel`). Landed with
the `eudoxus_slope.LessEqMulLeft` pilot, which it took from eight unground
installs + one refute to an explicit four-term chain.

```go
CalcOrder{
    Le:      func(a, b Term) Prop { return MakeProp(v.nadd_le.Apply(a, b)) },
    Eq:      func(a, b Term) Prop { return MakeProp(v.nadd_eq.Apply(a, b)) },
    LeTrans: MakeFact(ctx.DepNormalized(LessEqTrans)),
    EqToLe:  MakeFact(ctx.DepNormalized(EqImpliesLessEq)),
 // EqTrans unused: the chain turns ≤ at leg 1 and never composes ≈ with ≈
}.Calc(xy,
    LeLeg(v.nadd_add.Apply(xy, xd), "x·y ≤ x·y + x·d — LessEqSelfAdd",
        UseLemmaExact(ctx.DepNormalized(LessEqSelfAdd))),
    EqLeg(v.nadd_mul.Apply(x0, yd), "x·y + x·d ≈ x·(y + d) — LeftDistrib through EqSym",
        CiteSpecialize(MakeFact(ctx.DepNormalized(LeftDistrib)), x0, y0, d0),
        CiteSpecialize(MakeFact(ctx.DepNormalized(EqSym)), /* … */),
        CnfRefute()),
    EqLeg(v.nadd_mul.Apply(x0, z0), "x·(y + d) ≈ x·z — MulWellDef transports the gap",
        /* … */
        CnfRefute()),
)
```

#### `CalcOrder{…}.CalcLeibniz(from Term, legs ...CalcLeg) Action` — when ≈ is `=`

`CalcOrder.Calc` was built for a family whose ≈ is a DEFINED relation
(`nadd_eq`). Most order chains in the corpus mix ≤ with the kernel's
own equality instead — `m = m * 1` beside `P(m,n) ≤ A·(m+n)+B`. Same
legs, same tagging, same fold table, same terminal semantics; what
changes is which compositions must be CITED.

For a defined ≈, `a ≈ b` is an opaque atom: to use it under ≤ the chain
lifts it (`EqToLe`) and then chains (`LeTrans`). The kernel's `=` is not
opaque — the refuter rewrites WITH it — so every composition touching an
`=` closes by paramodulation from the two resident facts, citing nothing:

| running | link | ⟹ | how |
|---|---|---|---|
| ≤ | ≤ | ≤ | `LeTrans` — **the only certificate a Leibniz chain needs** |
| = | = | = | — `=` is transitive in the kernel |
| ≤ | = | ≤ | — the link rewrites `to` for `prev` in the running bound |
| = | ≤ | ≤ | — the running fact rewrites `from` for `prev` in the link |

So the kit carries `Le` and `LeTrans` and nothing else. Supplying `Eq`,
`EqTrans` or `EqToLe` **panics**: there is no ≈ theory here to certify.
`LeTrans` itself is required only if some step composes two ORDER facts,
so a chain that turns `=` at its last leg needs no certificate at all.
Each chained fact closes premise-scoped here too — the running fact and
the `=` link alone (plus the `LeTrans` instance on a ≤∘≤ step), everything
else cleared — so the paramodulation never meets the ambient context, and
a failure there is a mis-tagged leg.

**Why a second verb, not a nil-certificate convention on `.Calc`.**
Inferring the mode from three absent fields would turn "you forgot
`EqToLe`" from a precise construction-time panic into a silent
reinterpretation that fails much later inside the refuter. The mode is
chosen by the verb, visibly, at the call site.

```go
// nat_order.BoundsNotZero — the estimate that absorbs an affine constant.
CalcOrder{
    Le: func(a, b Term) Prop { return MakeProp(p.le.Apply(a, b)) },
 // no LeTrans: the chain turns `=` at the last leg, so ≤ never
 // composes with ≤ and nothing is cited at all.
}.CalcLeibniz(p.plus.Apply(As, p.B),
    LeLeg(p.plus.Apply(As, Bs), "A₀·s+B₀ ≤ A₀·s+B₀·s — LessEqAddCancel raises the constant",
        UseLemmaExact(leAddCancel)),
    EqLeg(p.times.Apply(AB, s), "… = (A₀+B₀)·s — RightAddDistrib refolds the two slopes",
        UseLemmaExact(rightDistrib)),
)
```

Source: `prover/proof/calc.go`, `prover/proof/calc_test.go`.

#### Calc: two contracts worth knowing before you convert

**The chained fact closes premise-scoped.** In `CalcRel.Calc`,
`CalcOrder.Calc` and `CalcLeibniz` alike, each chained fact is closed
from exactly its two links and the transitivity (and lift) instances
the fold computed — every other resident hypothesis is cleared first,
the same clear-first close a hand-written `By(link₁, link₂,
trans.At(…))` runs — so a chain is usable inside a context full of
resident ∀-facts (a coverage `∀x. x ∈ s ⇒ ∃y. …`, a `⊆`, a set-builder
membership), where an ambient refute of the same three-step leaf ran to
its budget and failed. A failure of that close is a mis-tagged leg (the
link is not the relation the leg claims) or a certificate that does not
compose the two links; the panic prints the chained fact and its
premises. It is never a missing premise and never a key to record. The
scoped leaf's hypothesis multiset is what the recorded CNF key is
computed over.

**Terminal chains are `CalcRel`'s too.** `CalcRel.Calc` and
`CalcOrder.Calc` are both Deduce-item factorial PRODUCERS, but either may
ARRIVE: when a fact the chain would assert is α-equal to the goal, it
is proved against the goal and the block CLOSES instead of leaving a
leaf. Without this a chain whose endpoint IS the section goal cannot be
one `Calc` at all — `AssertTactic` refuses a claim α-equal to the goal,
so the last fold dies with `ministep Assert … failed` and the author has
to run the `Calc` over the interior waypoints and hand-write the
terminal leg as a `Show` with its own ground cites, splitting one chain
into two spellings. A terminal chain must be its `Deduce` block's final
item; legs after the arrival panic.

**The grounding ceiling shows up MID-chain.** A leg body may panic with
`cite … closed the section; witnesses are unused — cite bare
instead`, or with `no unsolved leaves` at its `CnfRefute`. Neither means
the chain is wrong. A calc leg is a far smaller goal than the blob it
was carved out of, so a cite that needed grounding plus a refute in the
flat spelling frequently closes the leg outright. The fix is to shorten
that leg — drop its `CnfRefute`, or drop the witnesses
(`Fact(dep, w…)` → `Fact(dep)`). `runLegBody` names the offending leg
and says this.

Rule of thumb from the arith conversions: a leg citing a BARE equation
dep closes on the install; a leg citing a multi-conjunct clause PACK
(`Mul`, `Add`) still needs its refute to select the conjunct.

**A chain in an inductive relation takes the relation's own rules.**
A relation defined by rules (`do_derivable`, a closure) has its
reflexivity, symmetry, transitivity and congruences as conjuncts of its
rules, resident once `a.Conjuncts(<X>Rules.At(params…), …)` has read
them out. The transitivity conjunct is the kit's `Trans` as it stands.
Inside a leg a rule is cited **bare** wherever the leg's goal is the
rule's conclusion at the instance — a congruence, a commutation, a unit
law — because the close reads the witnesses off the goal; a rule the
goal does not determine carries its `At`: the reflexivity of the factor
a congruence leaves alone, and a rule read backwards, cited at its
instance beside the bare symmetry rule.

```go
derives := CalcRel{Rel: derivable, Trans: r.transitive}   // r: the rules, read out once
joined := a.Calc(derives, conditionalTimesMarginal,
    Leg(appended, "multiply the conditional and its replacement by the marginal",
        By(factors, conditionalAsProduct, r.reflexive.At(marginal), r.productCongruence)),
    Leg(reassociated, "associate the reciprocal with the marginal",
        By(factors, reciprocalFormed, r.associate.At(joint, reciprocal, marginal), r.symmetric)),
    Leg(jointTimesUnit, "cancel the two marginal factors inside the product",
        By(factors, cancelMarginal, r.reflexive.At(joint), r.productCongruence)),
    Leg(unitTimesJoint, "commute the unit to the front", By(factors, unitFormed, r.commute)),
    Leg(joint, "the unit law recovers the joint", By(factors, r.unit)))
```

#### `<Law>.Read(instance)` / `proof.Read(law, instance)` — session `read_at`

a structure law read at an instance of its structure:
`∀comps. S(comps) ⇒ body` at `⊢ S(c…)` is `⊢ body[comps := c]`, derived by
the kernel when consumed (instantiation at the components, modus ponens
against the instance), served in its stated form, keyless; deps = the two
entries. One cite target for `By`, `Simp(Fwd(…))` and the typed `.At(w…)`
over the law's remaining witnesses (an `Inhabited` where the reading's sole
antecedent is a membership).

Refuses, naming both statements, a fact that is not the law's structure at
its components. `dot.AddLeft.Read(real_ring.CommRing)`;
`Simp(Fwd(dot.SubLeft.Read(real_ring.CommRing)))`, no side-condition rule
beside it; `vec_space.BasisExpansion.Read(real_ring.CommRing).At(x)`
with the vector membership named beside it.

An instance entry that is itself polymorphic — `symmetric_group.SymmetricGroup`
is `group⟨A:permutation(A)⟩(mk_group(…))`, `free_group.Group` and the
category instances likewise — leaves its letter in the reading. A cite of
the reading pins it off the goal when bare and off the tuple when
witnessed (the session's `lemma {key, read_at}`, `proof.ReadingAtGoalTypes`
and `ReadingAtWitnessTypes`), and Go's `Cite` adapts it at the goal as it
adapts any lemma's.

The instance may instead be a RESIDENT structure fact of the proof in
progress — the hypothesis a Law's closure receives, a Have's fact — and the
reading is then the law UNDER it, `S(c) ⊢ body[comps := c]`, the fact as the
leaf consuming the reading spells it: the handle is followed there as a By
premise's is, so a reading taken before an `a.Let` that respelled the fact
is derived at the Let's text; dep = the law alone. A By keeps that hypothesis
resident beside the reading and materializes the reading as the Have it
replaces — asserted BEFORE every install whatever its list position (an
install's strategies read the context, so the leaf must be the one the Have
left), the claim branch closed from the derived sequent, the fact then
resident — the form the apply rung reads an antecedent in:
`By(finite, vec_space.MonoidalVecAdd.Read(ring), comm_ring.MonoidalAdd.Read(ring), Where(monoidal.Homomorphic, "h", pairWithY))`
supplies both `monoidal_op(…)` guards without a Have. The fact is the
instance itself — grounded or pinned it is refused; a hypothesis rewritten
away after binding refuses at the By, naming it. Witnessed —
`AutomorphismsSubgroup.Read(M).At(K, L)` — the reading is the sequent
grounded at the tuple in its STATED form whatever its body, a conjunction
included: a premise with hypotheses never takes the closed clause form,
which would ∀-close the components (the leaf's own terms) and fold the
hypothesis back in as an antecedent — the law the reading was taken from.

For successive bundle hypotheses, Go accepts `Read(law, first, second, …)`.
For example, `Read(FourLemmaSurjective, complexP, complexQ).At(f)` reads the
law at both resident complexes without listing their component operations.
Each instance discharges the next structure antecedent. Shared components
stay fixed, including a second bundle whose components are all shared;
all resident hypotheses remain attached to the derived reading. A second
instance with incompatible components is refused. Generated `Law.Read`
wrappers and the session's `read_at` still take one instance; the variadic
spelling is the Go `Read` function.

The instance may also be a READING:
`comm_monoid.RightIdentity.Read(abelian_group.Monoid.Read(group))` reads the
monoid chapter's law at the group's monoid projection, under the group — the
inner reading's conclusion is the sub-structure at its components, and the
outer law's hypothesis is discharged against it — one value where a
projection's reading as side-condition oracle beside the law at the
carrier's letter
(`Simp(Fwd(Monoid.Read(group)), Fwd(RightIdentity.Inst[B]()))`) stood; the
reading pins the type from its instance, so no `Inst` is spelled. The
reading is the instance bare: one grounded at its witnesses
(`SmulIn.Read(QuotientModuleOn.Read(module).At(N))`) is a structure fact at
concrete components and is refused, naming the spelling that serves it —
a Have proved by the grounded reading, the law read at the Have.

A reading whose conclusion IS the goal closes it alone —
`By(abelian_group.MonoidOn.Read(comm_ring.AddGroupOn.Read(ring)))` proves
`comm_monoid_on(R.carrier, R.add, R.zero)` from the resident ring, its certificate closing the
leaf where an assertion would make no progress — and the hypothesis the
engine keeps beside a resident reading is never reported as an unused
premise.

A law whose statement carries a type letter no component's type carries — a
LOOSE letter, `vec_space.SubspaceIterate`'s index type B beside the ring's
carrier A — cannot be materialized as that Have, whose fact would keep the
letter rigid; a By reads such a resident reading as the law cited beside the
hypothesis instead (bare, the apply rung pins the letter off the goal;
witnessed, the tuple becomes the law's: the components and the witnesses
in the order the law states its binders, each component at its own), so
`By(vec_space.SubspaceIterate.Read(ring), subspace, summands)` and its
`.At(s, t, F)` form both close. The hypothesis's binders need not lead the
law's: `product_topology.ProductMapContinuous.Read(f).At(S, V, g)`, the
law stated `∀T S U V f g.` and read at `continuous_map(T, U, f)`, grounds
it at (T, S, U, V, f, g). A tuple grounds a prefix of the law's binders, so
it runs far enough to hold every component; one that stops before a binder
stated ahead of a component is refused where the By is built, naming the
binder to give through. A bare nested reading uses the same
path: the outer law stands beside the inner reading's structure fact,
whose kernel-derived certificate keeps all its resident hypotheses. An
explicit witness tuple instead instantiates the loose type letters left
by the projections. Every type letter occurring in a resident hypothesis
stays fixed; the witnesses cannot change the types of an already chosen
structure. Go and the session use the same kernel-derived type instance.

If a bare outer reading and its inner reading would both require this
loose-law expansion, `By` refuses the combination: materialize the inner
structure as a fact first. This fixes the intermediate instance and keeps
the session and emitted Go on the same premise path. Witnessed readings
and projections whose component types are fixed do not need that step.

The law may also be a proved LOCAL section of the member, stated over the
structure binder — the node `ctx.Lemma` returns: `chart :=
ctx.Lemma("∀L:field_on(A). …", …)`, then `Read(chart, L).At(k, A₀, A₁, A₀₁,
t, M)` at the bundle fact, at as many instances as the member needs, where
the section's components would otherwise be spelled at each cite. The
free function takes it (a section has no typed wrapper, so `At` is the
untyped one); the reading is derived from the section's theorem, in the
section's spelling, and adds no dep. A section whose certificate is still a
promise when it is read — every section whose proof touches a served dep
or a bundle field is one at replay and under serve — is read as a promise
of its own, settled with the consumer's; nothing is forced at the read, as
no cite of a section forces it. A section still open when the reading is
consumed is refused naming it. In a session the section is named by its
root's id, `{"key": "s0_c…", "read_at": …}`, and emit renders the reading
as `Read(<section>, <instance>)`.

In a session the same value is the premise or rule
`{"key": law, "read_at": …}` of `by` and `simp_with` (the `by` row), and
the entry `lemma` cites — `{"type":"lemma","lemma":{"key": law, "read_at":
…}}` closes a goal the reading states and installs it otherwise (the
`lemma` entry) — resolved to these same premises, executed by the same
code and emitted in this spelling.

What a projection makes readable is found by goal: `retrieve` lists, after
the members, the laws read through a chain of projections from a structure
the goal holds a fact of, each with its chain, the Go value and the
`read_at` above (the `retrieve` entry's readings group); `query member` and
the index page list under each projection law the laws of the structure it
states, and mark the projections among them, under which the reading
continues. The value is no
member — a statement a reading derives is not written as one (the
constitution's §Readings) — and the tools are how it is found.

#### `Simp(Fwd(r₁), Rev(r₂), …)` — session `simp_with`

the Go face of session `simp_with`: rewrite the goal's conclusion with an
ORDERED rule set, jointly, to fixpoint. Each rule is a dep — typed entry
var, `ctx.Dep(name)`, or a sibling section — wrapped in a direction marker.

**`Fwd`/`Rev` name the direction against the rule's STATEMENT as written** —
the headline you read in the source: a named dep or a typed instance of one
is served in its stated form, exactly as a `By` premise is (normalize last;
`prover/proof/action.go`'s `resolveLemmaTarget`), so `Fwd(nat_arith.PowOne)`
with `nat_pow(m, 1) = m` collapses the power, a structure law
`∀comps. S(comps) ⇒ ∀xs. l = r` is a conditional rule fired `Fwd` in its
written direction with `S` discharged from the context — a guarded one,
`∀comps. S(comps) ⇒ ∀xs. G ⇒ l = r`, the same with `G` discharged from the
hypotheses beside `S`: ⇒ chains and ∀ blocks alternate freely — and a
FUNCTION-valued equation (`neutral_elem(vec_add) = vec_zero`) reaches the
driver unexpanded, so it rewrites the function where it occurs as an
ARGUMENT (`vec⟨n⟩(neutral_elem(vec_add))`). A session `simp_with` of an
entry serves the same headline, so its direction transcribes 1:1. To fire a
rule in its NORMALIZED orientation on purpose, pass that form explicitly —
`Fwd(MakeFact(ctx.DepNormalized(name)))`, as nonneg_real_formal_diff does for its AC canonicalizers;
the session spelling is the per-rule `normalized:true` bit, and
`emit-section` renders it as exactly that target.

**A resident fact is a rule.** `Fwd(f)` / `Rev(f)` with f a resident
Fact — an Argument verb's result, a handle, `ResidentHyp(…)` — is the
hypothesis assumed, the sequent `h ⊢ h`: the driver fires a rule that
carries a hypothesis only where the goal holds it, and its obligation
closes on the hypothesis itself (an `Assumption` step), never on a cached
theorem or an entry. So a resident pointwise equation rewrites where its
instances are: a guarded `∀y. y ∈ t ⇒ F(y) = z` is a conditional rule
whose guard discharges against the context, a resident `∀n. f(n) = g(n)`
rewrites under a λ no ground instance reaches, and a resident closure
`∀x y. x ∈ s ∧ y ∈ s ⇒ op(x, y) ∈ s` listed beside a conditional rule
discharges its side condition at `op(u, v) ∈ s` — `Simp(Fwd(eq),
Fwd(closed))`. A resident ∀-fact the rules do not name is not searched
for a side condition: list it. The rule keeps the proof's types (never
adapted). A grounded fact is no rule (`f.At(w…).Rw()` rewrites by the
instance); `fact.Simp(Fwd(fact))` (a fact rewriting itself) and a
resident rule under `SimpAll` (which rewrites every hypothesis) are
refused. The session spelling is the `simp_with` rule `{hyp_index: i}`,
and `emit-section` renders it as the fact naming the hypothesis — a
Have's handle where one names it, else `ResidentHyp(<statement>)`.

A COND the rules introduce whose guard is resident (or whose negation is)
collapses to its branch — the driver reads the context for it as it does for
a side condition — in `Simp` and `simp_with` alike. A wrong marker is only
sometimes loud (`Simp: no rule fired`); with a MIRROR PAIR
(`&0 < -x ⇔ x < &0` beside `-x < &0 ⇔ &0 < x`) the twin rule matches the
pattern its partner should have, so the set fires and the step SUCCEEDS with
a wrong goal, surfacing one step later as a CNF MISS or as a following `By`
blaming a ground witness that is correct. When that happens, compare the
goal printed above the panic against the leaf you validated in session.
`simp_with` is progress-or-fail, so with a SINGLE rule and the wrong marker
you get `success:false` and no child — try, flip, read.

**Polymorphic rule discovery is shared by Go and the session.** Each
adaptable rule contributes all distinct instances found by the finite
anchor-pin enumeration, alongside its original statement. No per-rule
copy limit and no pin count cuts this set off: the enumeration is the
`by` rung's own, complete over the finite goal. The actual rewrite driver still decides which rules
fire, including rules used only to discharge another rule's condition.
A resident reading keeps its instance's types and is not re-adapted.

Discovery also runs on what rewriting exposes, using the selected
hypothesis for `SimpAt` / `hyp_index` and the conclusion otherwise, to a
fixpoint within the round bound (`proof.MaxSimpAdaptRounds`): a copy
added at the bound that rewrites the residual further is refused by
name — the rule, the instance it was exposed at, and the spelling that
ends the re-adaptation — before that target's rewrite is committed, and
the session surfaces every round's instance diagnostics beside the
refusal. A copy with no redex is inert: the set is complete, and the
step proceeds. Session `simp_all` runs all targets on a clone, so a
refusal discards the whole call. Go `SimpAll` rewrites its targets in
sequence: earlier targets' rewrites may remain in a Script whose later
target is refused, but the action panics and supplies no completed
theorem.

An explicit `.Inst[τ]()` or session `type_specialize` supplies a
particular instance and is honored without further adaptation. The
session also preserves an explicit term specialization. A polymorphic
rule with nothing to rewrite stays legal in a rule set.

**A rearrangement law is not a Simp rule.** The driver fires a same-material
rewrite (associativity, commutativity — the two sides one multiset of
variables) only where the instance DECREASES the term order, which is what
keeps the rule set terminating; so `Simp(Fwd(Assoc))` fires in whichever
direction the letters make decreasing, not in the direction written. A Calc
leg that IS an associativity instance closes `By(Assoc, group)`, keyless; a
regrouping inside a context is a named Have of the instance, then `.Rw()`
(the group chapter is written this way).

#### `f.Rw()` / `f.RwRev()` / `f.Subst()` / `f.CongrArg(fn)` — session `rw`

a fact in hand driving a goal rewrite — the bridge for a body that mixes a
premise-list close with a rewrite. The fact is resident, or the ground
instance of a resident ∀-fact, `agree.At(u).Rw()`, grounded on the spine
first with its guards discharged by the context (§"A fact in hand"); the
session's spelling is `instantiate` then `rw`. It RETURNS the step: on its own line
(`parts[0].Rw()`) the call builds the step and drops it, the goal stands,
and the failure surfaces steps later — the lint `TestLintNoDiscardedAction`
refuses that statement, for every Action constructor and Fact method; the
step runs inside `a.Do(…)`, a Show or a Case. An equation over two NONLINEAR
products is always this, never a premise (the closer keeps such products as
distinct opaque atoms).

**When the equation comes from a DEP rather than from the goal's own
context**, every `Fact` producer listed above yields a fact in hand, and
a dep read as a `Fact` is not — `Fact.Rw` panics on it, and its panic
text names the alternative. Two spellings, and the choice is about whether
the equation earns a name in the checked layer: `LeanRw(ctx.Dep(dep))`
rewrites straight from the dependency, copying nothing — prefer it when the
dep IS the equation and is NOT permutative (see the `LeanRw` row: a
commutativity law must be pinned at its instance), since the rewrite's own
first obligation is then discharged by `Cite(dep)`;
`f := a.Have(label, claim, Cite(dep))` then `f.Rw()` puts a hand-written
claim in the checked layer, which is right when the equation you rewrite by
is a SPECIALIZATION or consequence of the dep rather than the dep itself. Do
not reach for the `Have` form merely to obtain a rewritable fact — that
copies the dep's statement into the consuming file and drags its vocabulary
with it.

### The recorder's two gates (`TestRecordFamilyCNF`)

A family GC (`XUGO_FAMILY_CNF_GC=<domain>/<family>`) and a member
record (`XUGO_RECORD_FAMILY_CNF=<family>.<Name>`) REFUSE to write a
blob that does not replay: before the write, the member — under a GC,
every member the GC measured, and every member whose kept rows that
measuring re-derived — is replayed strictly against the fresh bytes
under the replay harness's two gates — every refute a cache hit, and
no divergence whistle — and under the rest of what a replay of the
member checks:
the Key minted and the built theorem the entry's own statement, and
the capability use and the entries read what the bytes record. A
failure names the member and leaves the committed blob in place. A
member record replays its member even when the bytes do not change,
so a recording that passes is that member's replay and needs no
second run; `XUGO_REPLAY_ONE` is for a member you did not re-record. The recorder's route is a search and the replay's a lookup,
and the two have been seen to differ (a cold record choosing a
conditioning plan the merged driver cannot finish within its backstop
at replay; a recorded key the current engine cannot re-derive within
the 5 s ceiling): such a family can only be GC'd WARM until the
member's route changes, and the GC says so instead of writing bytes
the corpus replay rejects one run later.

**A whistle refusal says where.** "the recorded route fires the
divergence whistle N time(s) at replay:" is followed by one numbered
entry for each distinct cut (listed as in a `by_whistle`, §`by`): the
`By` it ran under, by its premises and the
`file:line` it is written at, as an S7 line names one; what the driver
refused — a case analysis at 512 open leaves, a branch or a rewrite cut
as divergent; the statement, which for a refused case analysis is the
goal the analysis was entered with; and `chapter line:`, the line of the
chapter's verb that was applying the step, which locates a cut under a
step that is no `By` (a `Simp`, a `Basic()`, an `Unfold`'s tidy). The
replay harness fails a member in the same words (`TestReplayAll`,
`XUGO_REPLAY_ONE`). The recording run is a search, and a cut does not
stop a search: it goes on with what is left and closes, so a member
records its rows and is refused here, where the replay is held to no
cut. A session `by` that closes past a cut says so in its response
(`by_whistle`, §`by`), before the Go exists.

**What a GC runs.** No proof. Every recording writes the member's row
record — the certificate and plan keys its run touched
(`member_rows`) — beside its capability and dependency rows, and a GC
keeps exactly the rows the members' row records name, with every
member's records, and drops the rest: a blob of hundreds of members
collects in the time it takes to decode. A member the blob holds no
record for — no row record, a row record naming a row the blob lacks,
no capability row — is measured by the GC as a recording measures it,
warm against the committed blob, and its records are written from
that run; a GC of a family with no measured member runs every member
once. A member record (`XUGO_RECORD_FAMILY_CNF`) always runs. The
replay harness does not hold a member to its row record: the By
ladder reads the bare key before the conditioned plan and
certificate, so a replay can read a sibling's row in place of the
member's own, and every row it can read is one some member's record
keeps; the one way a replay reads a row no record names is through a
sibling's row that sibling's re-record no longer holds, and the scope
replay after the GC misses there, names the member, and the member's
record refreshes its row. The bundles are installed and warmed only
when a member runs.

**A read-only run.** With `XUGO_RECORD_CNF_DRY_RUN=1` beside either
variable the run is the same and nothing is written: the member (under
a GC, every member it measures) runs as it would be recorded, its rows
are listed by leaf, the resulting blob is verified to replay, and the
last line says what WOULD have been merged or retired. It is how to
ask "does this member reach the refuter, and with which keys" or "what
would a GC retire" without moving a blob — the question a session's
close cannot answer and a recording answers only by writing. One row is the
machine's, not the spelling's: at a `By` whose conditioned rung runs
to the refuter budget and whose bare retry then closes, the recording
holds a bare key and no plan where, given the time, it holds a
conditioned key and a plan row — both replay, and the S7 audit says
so at that step ("in the conditioned rung a refutation ran to its …
budget and was cut off; the bare retry closed the leaf"). Likewise
where the rung is cut off on the whole leaf and closes on the pruned
one: the plan recorded replaces where, given the time, it replaces
nothing ("… run again on the pruned leaf, the rung closed it"). A row
difference at such a step between two recordings, or between two
spellings read by their rows, is read on an unloaded machine before
it is read as the spelling's.

**The recorder names leaves.** Every row a member touches is printed
with its serialized size and the leaf it stands for, under `leaves of
<Name>:` — `new | re-derived | hit key <k> (<n> bytes) ← <sequent>`
for a certificate (the sequent that reached resolution: the conditioned
leaf, premises installed) and `new | re-recorded | hit plan <k> (<n>
bytes) ← <sequent>` for a plan (the bare working leaf, the plan table's
key) — and a GC prints the rows of each member it measures, and the
rows it retires, by key. The last line sizes the blob
before and after, `<k> keys + <p> plans (<n> bytes)`. A certificate the
run writes (new, or re-derived) above 256 KB is named again under a
`WARNING: … outsized certificate(s)` line, its leaf worth re-reading
for a smaller close: its bytes are live memory in the serve and in
every replay. Above 1 MB the lint battery fails the blob
(`TestLintCertificateSize`).
So "+2 new" is two leaves to read, not two keys to hunt for in the
blob's strings, and a member's hits are its key demand, which the
counts alone never list. The mechanism is `CNFGoalNoter`
(prover/proof/cnf_store.go): the capturing store keeps the goal the
refute or the plan stage hands it beside the key; the persisted stores
implement nothing new.

The S7 economy audit the recorder runs reports two spellings: a keyed
leaf that "closes under Basic()" wants `By(Normalized, …)` where the
`By` so respelled, run through the same ladder and held to the close's
rows, closes on fewer of them — the line gives the two counts, and a
`By` that already carries a shape is not advised (the marker retires
the key; a session `by` that closes says the same of its own leaf, as
a `by_economy` diagnostic, so the marker can be spelled before the
first record), and an element is "inert" — a shape element
(`Normalized`, `PreNormalized`, `Denoted(n)`, `DenotedAs`,
`HilbertDenoted`, `Raw`), the `Broadcast` flag, a premise of `BySets` —
only when a recording of the `By` without it would touch no row the
`By` with it does not: it closes at the ladder's keyless rung (the
conditioned attempt with no grounding, which the ladder runs first for
the CNF closer), at the bare rung on the same certificates, or at
the conditioned rung on the same plan and certificates. The probe runs
the recorder's ladder with the element taken out, held to that one
close's rows; it searches for no refutation and reads no clock. A leaf
the refuter closes at another key is not inert, however quickly it
closes; neither is a close whose grounding stage (S4) would record a
plan, nor one the blob would serve from a row the close does not touch
(a row of a spelling since abandoned, or another member's): each is a
row in the member's record where the element was one token of text. So
the drop of an inert element costs nothing — the re-record writes no
row for that close, and the member's rows do not grow.
What the line leaves unsaid is every drop that changes the rows: one
that trades the close's key for another, or several rows for fewer, is
not called inert, and whether it is cheaper is the recorder's count (a
dry run of the member without the element, read at its `leaves of
<Name>` lines). A drop can expose a second-order finding, so re-run the
audit until it is quiet.
Apply a finding, then
re-record (the recording replays the member); never replay first
against the old blob and read a MISS as the audit's error.

The replay cannot stand in for the recorder. It answers "does this
proof close against this blob"; what a spelling COSTS is a property of
the leaves the proof reaches, and only a live capture counts them.
"Delete the shaping, replay strict against the unchanged blob: still
green, so it was decoration" is unsound twice over. The old blob
still holds the retired shape's keys, so a refute the edit ADDED lands
on one of them and passes. And a strict replay reports the first
missing key and stops, so two spellings that miss at one key look
equal where the recorder reads two certificates against one. A family
blob is embedded in the test binary (`//go:embed`), and the replay's
children re-execute that binary: after a re-record, replay with a
binary built after it, or the old blob is what is read.

Every finding names its SITE — `By(…) at library/proofs/<dir>/<file>.go:<line>`,
the line where the author wrote the `By` (`ByArith`, `BySets`), or the
`ByInduction` whose cases it closes — so a finding reaches exactly one
call even where a member holds several `By`s with the same premises.
A shape the PROVER inserts (a Calc chain's close, `ObtainChosen`'s
choice) is no author's to drop, and the audit does not advise it. A
finding is advice, and the recorded footprint is the judge: keep an
applied finding only if the member's touched rows (the GC's
`touched N key(s)` line) do not grow. An "inert" line keeps that bound
by its test: what a recording of the `By` without the element touches
is among the rows the member already names. The "closes under Basic()"
line trades rows for a marker, by the count it prints, and is read at
the re-record. A comment
beside a close that says an element was "checked by removal" is a
measurement with a date, not a contract: the recorder is believed.

### Common gotchas

- **`UseLemma(thm)` on a freshly-`StripQuant`'d clause closes via eqSimplify.** No trailing closer — a redundant `CnfRefute()` after it panics "no unsolved leaves".
- **`StripQuant()` peels ALL consecutive ∀** — never call it twice on the same ∀-prefix (the second is a no-op that trips the leaf-tracker). Distinct consecutive calls that each Skolemize a different ∃-hyp of a sequent goal are a valid, emit-rendered pattern. `StripQuantN(n)` peels exactly n and panics when the prefix is shorter.
- **`Cite` decides close-vs-install from the goal state** — you do not predict whether a cite closes the leaf or installs a hyp. Two close tiers: stronger-fact (concl α-equal, hyps ⊆) and normalize-tier (the leaf IS the fact modulo Normalize — what the session's auto-match commits, so a session-closed leaf closes in Go too). If you MEANT "this must close right here" and it installs instead, the leaf was NOT the fact you cited — inside `CalcEq`/`Derive` the enclosing block's own panic is already loud and local; do NOT reach for legacy `CiteKnown` (lint-banned in hand-written chapter Go), diagnose the form gap in the session instead.
- **`Cite` installs PRESERVING** — it never rewrites an existing hypothesis. An argument that needs the destructive whole-context simplify (a cited iff rewriting a resident hyp to become the goal) keeps legacy `UseLemma`, with a comment. Symptom of getting this wrong: strict-mode CNF cache MISS (the goal reaching a refute differs) or an unsolved leaf where the old chain closed.
- **`Specialize(InstHyp(0, t1, …, tk))`** grounds k binders in one step. Fused with citation: `UseLemmaSpecialize(thm, t1, …, tk)`.
- **`a.Hyp(text)` is located when Go evaluates it; `ResidentHyp(text)` when the `By` runs.** `a.Hyp` finds the hypothesis in the leaf as it stands at the call, and panics when it is not there — so inside ONE `a.Do(step, By(a.Hyp(h)))` it cannot name a hypothesis `step` creates: Go evaluates the whole argument list before the first Action runs. Split the `a.Do`, or name the hypothesis with `ResidentHyp(text)`, a premise located by content at the consuming leaf (it is what emit renders a session `by_hyps` premise as). A lexical fact — a closure parameter, the value a verb returned — is preferred wherever one exists.
- **`CnfRefute()` live is nondeterministic.** The family blob covers it: record the member once (recipes in the header of `library/integrity/gates/record_cnf_test.go`) and strict replay reads the certificate. Before recording a MISS, read its `(Checked: …)` line: a goal that closes under `Basic()` wants `Basic()` or `By(Normalized, …)`, and no key.
- **`TrivialNormalized()` ≠ `CnfRefute()`.** The former is the normalize-to-⊤ short-circuit (no cache key); the latter is a refuter close. Pick the right primitive when translating from session `apply` responses — `auto_matched` with `matched_key:""` and no section is a `TrivialNormalized`.
- **Nothing follows a close.** After a step that closes the last leaf (`UseLemma` on an identity goal, a terminating `CnfRefute`, an `Unfold` whose tidy finds an identity), a further action panics "no unsolved leaves", naming the step that closed the last leaf (an `Unfold` with its line and what its tidy found) and the leaf it closed.
- **Branch label format.** What a label says is the constitution's §"Argument structure: flat chain → named cases"; what the compiler and the lints hold of it is here. A branch claimed by a NAMED verb has its position in the verb, a slot the compiler checks: `a.When`/`a.Otherwise`, `a.Base`/`a.Step`, `a.Forward`/`a.Backward`, and the Chain-form `Forward`/`Backward` and `BothHold`/`NeitherHolds`. A positional `Case` arg of a Chain-form multi-leaf Step (`InductStep`/`AssertStep`/`ByCaseStep`) has no such slot, and its sentence is what tells the branches apart. `Case` exists ONLY as an argument to a case-eligible multi-leaf Step — `prover.Case` deliberately does not implement `Action`, so a free-standing `Case(...)` inside a plain `Chain(...)` is a compile error (`does not implement Action`); a linear chain carries its labels as per-Action `//` comments instead (the `Cauchy` member's idiom — `proofs/real/tower/internal/eudoxus_slope/toolkit.go`). `Derive` blocks carry labels on `a.Have`/`a.Show`/`a.Obtain` directly, under the same rule. The chapter lint refuses a label that is, or opens with `<token>:` for, one of `claim`, `after`, `residual`, `premise`, `left`, `right`, `true`, `false`, `base`, `step`, `forward`, `backward`, `case_<n>`, and a `Base`/`Step` label that opens with its own verb's word (`TestLintNoStructuralTokenInLabel`). Those are every role tag `emit-section` leads a rendered `Case` label with — `left: <the arm's conclusion>`, the arm's hypotheses being the `// context:` comment under it — so a rendered branch is refused until its label is restated; a rendered `Show`, `Forward` or `Backward` label is the conclusion alone, restated on the same pass. ALL labels stay under 140 runes (lint-enforced): state the branch's mathematical MOVE, referring to named quantities by their Go names — never re-spell a multi-factor formula.
- **Asymmetric splits linearize; chains are Calc.** Which split takes
  which form is the constitution's §"Division of labor"
  (`real_sgn_abs/real_sgn_abs.go`'s `SgnMulSelfIsAbs` is the worked
  example). The spellings: a split whose one
  branch is trivial is `Assuming`/`Unless`/`Suffices`/
  `h.DismissLeft|Right` — the main line stays in the enclosing chain
  (k dismissals cost 0 extra indent, not k), where a symmetric split
  costs ONE indent per level in the statement form; ≥2 nested
  `Expect(Trans)` bridges or a transitivity-only Have staircase
  spells as `CalcEq`/`CalcRel.Calc`. All are tree-identical desugars
  over the existing ministeps — recorded pbs keep hitting.
  Group/monoid consequences (perm4, shift-cancellation
  ladders) are instantiated from `prover/solver/algebra` (the
  cert-passing Group kit — pass YOUR family's Sym/Assoc/LInv/LId
  certs; it adds nothing to your dep base), never re-derived
  inline.
- **Claim construction.** Claim and statement texts carry no ⊢ — neither hypotheses nor `name:type` decls left of it (lint-enforced, `TestLintNoTurnstileInStatementText`); a statement is closed, its premises ⇒-antecedents: a section's variables arrive as closure parameters, a Skolem minted by `a.Fix`/`a.Obtain` is registered by the verb, and `ctx.Var` is for what its row above leaves it. Name the estimate's recurring terms (the estTerms idiom: a struct of commented `*TermWrapper` fields + an `est()` builder), and construct any claim that mentions a named quantity — or would spell a subterm twice — programmatically: `a.Have(label, MakeProp(v.le(v.sum(t.distShift, t.distX), t.distYBX)), By(…))` (the `LessEqExists` member in `real/tower/internal/eudoxus_slope/order.go` is the model; the constitution's §"Stable authoring rules" asks for the value over a re-spelling). Text claims stay for short notation-dominant statements and closed statements over bound variables. Section statements stay text regardless of length — an unreadable one is a signal to restructure the member.
- **A claim-text helper's INTERNAL binders must be disjoint from every variable a caller may substitute into it.** A Go helper `disjClause(x, v string)` that returns text binding `∃c i r y. …` and is called with arguments built from a caller's own `c`, `i`, `r`, `y` (`r(n)`, `Fn(c, i, r, y)`) has those substituted terms CAPTURED by the inner `∃` — text substitution is not capture-avoiding. The claim parses, so nothing panics; the statement is subtly wrong and the failure surfaces far away (`At(fact, λ-predicate)` "not grounding", a `By` that should close). `datatype_universe.Recursion` met this; renaming the inner binders `∃d j s z` fixed it. Name a helper's binders with letters no caller uses, or take the binder names as parameters.
- **`At(factParam, λ-predicate)` DOES instantiate second-order.** If it appears not to ground, suspect the claim text (see the previous bullet), not the verb.
- **A function equation substitutes under `By` when it stands alone or under a guard.** A ground equation between FUNCTION-typed terms (`s = r` at `num → recspace(A)`), as a fact of its own or under a guard, demodulates `Fn(…, s, …)` to `Fn(…, r, …)` under `By`: the refuter rewrites the argument from the equation's pointwise clause, or recovers the equation from its pointwise clauses, at a set type as at any other, and a given clause meets the same rewrite a derived one does. Inside a disjunction it does not — rewrite the argument first (`f.Rw`), then refute. The Playbook section "An equation between functions — rewrite with it, do not hand it to a closer" has the table.

### Where the full details live

- `library/authoring` (`authoring.go` + the generated
  `zz_constructors_gen.go`) — the authoritative list of the bare names;
  `go doc ./library/authoring` prints it. This cheat sheet is derived
  from it; when they disagree, the package wins.
- `prover/proof/action.go`, `prover/proof/script.go`, `prover/proof/goal_stack.go` — full signatures + docstrings.
- `library/proofs/<domain>/<family>/*.go` — grep for a specific idiom when a concrete
  question arises (entry-var shape, citation helpers). Targeted lookup, not whole-file modeling —
  §"The framework" above.
- **Typed surface**: `proofs/iterate/monoidal/` is the live typed
  dialect (closures, wrapper cites, `vocab.go`'s rows;
  cross-family cites go straight at the owner's wrapped var —
  `num_segment.Rec.At(m, n)` — no local facades); §"The generated
  wrappers" documents the wrapper lexicon; `prover/proof/typed.go` + `ext/expr.go` +
  `ext/holtype_phantom.go` carry the verb/wrapper
  docstrings; `utils/generic_test.go` pins what Go 1.27 generic
  methods can and cannot express (read it, never re-probe).

