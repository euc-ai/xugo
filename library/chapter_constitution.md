# The chapter constitution

The terminal goal is **elegant Go documents that are mathematics**.
The proofs are ordinary Go programs whose execution constructs
kernel-checked proofs. They must meet two non-negotiable requirements:

1. **Strict correctness.** The kernel accepts the proof, force replay
   succeeds, and the built theorem is the entry's statement up to
   normalized alpha-equivalence.
2. **Readability and maintainability.** A mathematician-agent can recover
   the argument from the source, and the corpus can be refactored like a
   well-designed Go library.

`library/proofs/` is the artifact governed by this document. This
file is a constitution, not a progress ledger. A chapter's record is its
package — the registered entries, the family blob that records what
their proofs read, the README narrative;
construction history belongs in git. There is no construction ledger.

Two readers hold a chapter to it, at two moments. What a chapter is —
its domain and its files (§"Directory organization", §"File
granularity"), which statements become members and which do not
(§"Inventory and names", the inventory half), how a family begins and
grows (§"Family lifecycle", §"Growth mode") — is settled in dialogue
before a brief is written, and the brief carries the result. A prover
dispatched with a brief writes one member and holds it to everything
else here; the names it gives (§"Inventory and names", the naming half),
the file it writes (§"Families") and the checks it runs (§"Verification
contract") bind both.

## Architecture: one corpus, the author's statements

`library/proofs/` is the library. A statement enters it from its
author, stated in natural form. The author may be working from a
reference — a textbook, a paper, another prover's library — and the
reference is then a blueprint for the proof, read
for its lemmas and its case structure; the corpus ships no other
system's sources and needs none. Either way the statement is written in
the chapter's own vocabulary, the proof is found in a session and
written as chapter Go; the session's record (`emit-section`) is
transport, never a style model.

An entry may diverge from the reference it was proved from in proof
structure, dependency direction, names, file boundaries, and theorem
inventory; once landed, its statement is its own. A reference's
declaration order has no normative force.

A mechanical defect in what `emit-section` renders is recorded as an
emit issue for separate review; it is fixed at the emitter,
never patched around in a proof file, and never mixed into a chapter
landing without separate authorization and verification.

## Correctness model

The kernel, with force replay, is a total oracle for logical
correctness. Authors should therefore refactor proof bodies boldly: a wrong
body fails rather than silently proving a false theorem.

The oracle does not judge presentation, and logical validity alone does not
establish a usable dependency architecture. The following guards are part of
correctness:

- **Force replay is mandatory.** It reduces proof promises to kernel
  certificates and is the authoritative cycle check.
- **No `TestThm` in proof files.** It creates an unproved trusted
  theorem and bypasses replay.
- **Automation must remain foundation-safe.** `Arith` is allowed through the
  installed nat/real foundation gates. A foreign procedure may not expand the
  proof's axiom or procedure base beyond the installed foundation gates
  without an explicit architecture decision.
- **Statements receive human review.** Normalize-alpha equality deliberately
  identifies a natural statement with its machine normal form, so replay
  cannot tell which surface is readable mathematics.

## The headline invariant: a registered statement is mathematics, not a normal form

A entry's headline states the theorem in natural mathematical form.
Do not sign artifacts of normalization such as:

- prenex-CNF clause soup;
- refutation witnesses with no mathematical role;
- reversed equations chosen by normalization;
- machine binder names;
- binders hoisted out of the conjunct or implication where they belong.

For a statement taken from a reference, start from what the reference
proves, then improve its binder order or logical presentation when useful.

A theorem that says a bound or a constant EXISTS is stated as the bound.
`vec_linear(f) ∧ vec⟨m⟩(x) ⇒ ‖f(x)‖_n ≤ (Σ_{i<m} ‖f(basis_vector(i))‖_n) * ‖x‖_m`
is the member (`vector/euclidean.LinearBasisEstimate`), and the familiar
`∃B. ∀x. vec⟨m⟩(x) ⇒ ‖f(x)‖_n ≤ B * ‖x‖_m` is one cite of it away, a bare
corollary. An existential bound does not compose: a later theorem that sums
the estimate, iterates it or reads it at a family has no TERM to put under its
sum — the bilinear bound applies the linear one twice, and an `∃` would have
to be chosen at every index and the choices assembled into a sequence before
the sum could be written.

A binder's type says what the binder is. A set is `set(A)` and a predicate is
`A → bool` — one type in the logic, two readings for the reader: a family of
sets is `set(set(A))`, a set-valued map `A → set(B)`, a property of sets
`set(A) → bool`, and a definition's `Type:` row spells its constant the same
way (`closed_in : set(set(A)) → set(A) → bool`). The parser refuses a
`set(…)` binder applied as a function, and `TestSetSpellingLint` reports a
binder spelled `X → bool` that only ever stands under a set operator.

A binder's name says how it stands to its neighbours. Members of one
sequence are indexed by subscript digits: `x₁ x₂`, `0 → N₁ → N₂ → N₃ → 0`,
`op₂` for a second operation. One prime marks a modified copy of a single
object (`f'`, `S'` a second resolution). The parser reads `x₁` as the
kernel name `x_1` and the printer writes it back as `x₁`, so the two
spellings are one name; `x1` is another name, which no printer
subscripts. `TestLintSequenceBindersUseSubscripts` reports a binder whose
name ends in ASCII digits. A closure parameter spells a subscripted binder
with ASCII digits (`x₁` binds `x1`), which `TestLintBinderClosureNames`
checks.

The entry headline and an internal proof section have different roles. An
internal section may use a normalized or witness-bearing form when the proof
genuinely reasons about that form. Keep the public headline natural and bridge
to the internal section. If the body works unchanged after restating the
headline, restate it directly; do not add a bridge for imagined consumer
safety.

An apology comment is a defect signal, not a remedy. Comments such as “stated
as the clause”, “recorded flipped”, or prose decoding a Skolem witness usually
mean the statement should be repaired. Fix the statement and remove the
decoder.

## Citation forms: compute, don't pin

A proof computes a cited theorem's usable form from the dependency; it
does not copy an emitted record's exact normalized text.

Use the single citation vocabulary; what each form installs is the manual's
(`engine/xugo-engine.md`, the cheat sheet's "Citation" table):

- `Cite(dep)` brings an entry variable or a sibling section to bear. It
  closes when possible and otherwise performs the preserving install.
- `Cite(dep, witnesses...)` cites a ground instance.
- `CiteKeep(dep, witnesses...)` keeps the quantified source when it will be
  instantiated again.
- An entry's own typed wrapper is the cite wherever its witnesses carry a
  phantom (§"The typed surface"): `Entry.At(witnesses...)` as a premise, the
  type instance inferred from the witnesses, and `Entry.Inst` binding it by
  letter where there are none. As a step the cite is the verb's —
  `Cite(Entry, witnesses...)`, at a chosen instance
  `Cite(Entry.Inst[T](), witnesses...)`.
  The positional `ctx.AtTypes` is that surface's exit, not a citation form
  of its own.
- `Cite(section)` cites a sibling section captured as a Go value.

Dependencies are typed entry variables and nothing else: there is no string
channel, so a dep that has no entry yet is not citable until it lands.

Raw or destructive installs are exceptional:

- `Cite(MakeFact(ctx.Dep(name)))` is allowed when the raw surface is structurally
  required, for example a multi-clause conjunction whose separate binders must
  be split, or a set-quantified statement that normalization pointwise-expands
  too early.
- `UseLemma(ctx.DepNormalized(name))` is allowed when the proof intentionally
  rewrites resident hypotheses destructively.

Each such site carries a short mathematical or engine-shape reason. Exact
quoted citation text is a last resort for a load-bearing variant form, never a
way to stabilize routine replay.

Quoted propositions remain appropriate for statements the proof itself
asserts: section headlines, `Have` claims, and explicit premise handles.

## The math layer: facts as values (`Fact` / `By` / `Derive`)

A deduction is written at the math layer. Facts are Go values and each
close names its premises lexically.

### Core vocabulary

The verbs, their contracts and a worked body are the manual's
(`engine/xugo-engine.md`, §"The math layer: how a body is written"). What
the chapter form asks of them:

- A `Fact` is a value: a certified fact or a resident hypothesis, and a
  ground instance of one (`dep.At(witnesses...)`, `f.At(witnesses...)`) is
  a value too, a description until a close consumes it. `Where` pins one
  stated binder by name where the goal cannot determine it; a fact so
  named must apply and is never handed to the closer.
- A close names its premises. `By(premises...)` clears every other
  hypothesis, installs exactly the listed ones and closes once; `ByArith`
  is the same close through the gated arithmetic closer, `BySets`
  through the set driver, and `ByChase(Depth(k), ...)` through the
  diagram chase at k pull-back rounds. The list is a claim about what the argument
  needs, so a close reached before the list ends is an error: it makes
  the list dishonest.
- `Derive(func(a *Argument) {...})` is the ordinary deduction block, and a
  verb exists exactly where a paper proof has a word for the move — "we
  have", "obtain", "suppose not", "let", "take", "hence".
- A split is two sentences: the opener states the move (`a.Cases`,
  `a.Induct`, `a.Iff`), and each branch is claimed after it BY NAME —
  `a.When` / `a.Otherwise`, `a.Base` / `a.Step`, `a.Forward` /
  `a.Backward`. Which branch a body proves is the verb, never the
  position, so the two may be written in either order and neither can
  drift.
- A branch that grants a hypothesis hands it over as a `Fact`. Take the
  hypotheses the branch hands over; do not re-spell a machine-built
  hypothesis with `a.Hyp`.

Use `Unpack` to eliminate an established existential, including a named
theorem or a ground instance. Use `Obtain` when the existential itself must be
proved. Use `ObtainChosen` only when the argument must continue with the
canonical Hilbert-choice term rather than a fresh witness.

Nested arguments may reuse receiver name `a`. Use `b`, then `c`, when the
inner block needs to reference the enclosing argument.

### Premise discipline

The Go variable graph should visibly be the proof DAG. A hand-written
intermediate fact stays on the page:

```go
step := a.Have("description", "P", By(premise1, premise2))
a.Show("Q", By(step, premise3))
```

A `Have` is an intermediate fact when its sentence is one the reader wants
on the page. A fact that only bridges one hop — proved from one or two
premises and read once, by one close — is that close's premise, not a
step: list its premises there and write no `Have`, whether or not the
folded leaf then records a key or a plan. A fact a law is read at
(`Law.Read(h)`) is a value the reading needs, and stays. A key or a plan
is a measured cost of a spelling, weighed when two spellings of one close
are compared, never a reason to add a step the mathematics does not have.

A nested argument is a step's own justification: the reader holds the
step's sentence and reads its proof under it. An argument that carries its
own case analysis or induction, under hypotheses the reader has to keep in
mind, is a statement of its own: it is stated in full and proved before the
argument that cites it, as a section of the member (`ctx.Lemma`), or as a
member of the family where it has value outside this proof.
`TestLintArgumentDepth` refuses a member whose arguments nest more than six
deep; the bound marks where the criterion has plainly been missed, and is
not the criterion.

A verb that reads a fact in hand — `a.Conjuncts`, `a.Simplified`,
`a.Unfolded`, `a.Unpack`, `a.Do(f.At(x))` — discharges the instance's
guards from the facts listed with it and from nothing else, as `By` closes
from its listed premises alone. A fact that stands to discharge such a
guard is bound and travels with the instance as one value:

```go
bound := a.Have("description", "P", By(premise))
parts := a.Conjuncts(GroupPremises(bound, Law.At(x)), "first", "second")
```

The parts of a `Conjuncts` read this way are listed by index, a member by
itself or with its membership. A guard the context supplies through a fact
the list leaves out is refused, naming the fact, and so is a listed fact
that discharges no guard another listed fact does not; a member's evidence
travels with the member and is never refused.

A premise may carry its own proof only when it is a fixed solver-kit value,
such as an AC rearrangement derived from explicitly supplied laws. Do not hide
an arbitrary hand-written subproof inside a premise list.

Shaping that has no mathematical content is a value in the premise list:
`Normalized`, `PreNormalized`, `DenotedAs(name, term)`, `HilbertDenoted`, and
`Broadcast`. Add shaping only after a premise-complete close shows that the
remaining failure is goal form rather than missing facts.

When bare `auto` or `CnfRefute` times out in the presence of wide quantified
hypotheses, first replace ambient-context reasoning with an explicit `By`
premise list. Do not classify the site as an engine wall until irrelevant
hypotheses have been eliminated.

#### A premise whose install absorbs the goal is cited BARE, and its instance
#### is not restated anywhere

`By` executes a named premise in two steps: install the ∀-form, then apply the
witness tuple. One class of premise never reaches the second step — a law that
discharges its own obligation (reflexivity, an identity, a value law read at
the goal's own point) closes the goal at install. A witness tuple written at
such a site is never applied, so it is unchecked text: a deliberately wrong
tuple replays green.

`prover/proof/step_by.go` refuses the spelling — *"closed the goal at its
∀-form install, so its witness tuple was never applied — cite the premise
bare"* — aligning `By` with the contract `Cite` has always enforced. The fix is
the message's own: drop the tuple.

**Do not relocate the instance into a comment.** A comment is unchecked text by
exactly the same argument that condemned the tuple, and an instance nobody
verifies is worse adjacent to code that looks like it verifies one. The bare
cite is the whole edit; where the reader needs to know which instance the
install pins, the answer is the resident premises next to it, which are
checked.

**"Comment" here means every unchecked surface, narration strings included.** A
`Have` / `Obtain` / `Show` / `Case` label reading *"… — tightBound at (P₀,
r_fn₀)"* asserts the same unverified instance a trailing `//` would, and being
emitted narration rather than a comment does not make it checked. Such a label
keeps its mathematical content and loses the `at (…)` clause; nothing in the
loop reads a label as a claim, so the rule is the only guard.

**The contract is unconditional.** `By` panics on an unapplied witness
tuple in every path — sessions, replay children, the recorder — with no
flag and no tolerate mode. A plain `go test` of the corpus IS the strict
check: a member carrying a dead witness tuple fails its own replay,
naming the site.

#### A property of a map stands in the context as its atom

A map's injectivity is kept as its atom — `injective_on(s, f)`, at
`𝕌` for a map injective outright — read where it is spent
(`functions.InjectiveOnDef` states the formula). The spelled-out
`∀u v. u ∈ s ∧ v ∈ s ∧ f(u) = f(v) ⇒ u = v` is not left resident as a premise: its
conclusion equates two of its own binders, so it matches every
equation. The apply rung meets it at each equation goal and reports
its antecedent missing (the miss says the head matches every
equation), and a refuter given it resolves it against every equation
of the leaf. Where the formula is what a step uses, ground it there,
`.At(u, v)`. Surjectivity onto a set is the equation `image(f, s) = t`,
and a type whose predicate is a bijection is stated with the two — a
permutation is `injective_on(𝕌, f) ∧ image(f, 𝕌) = 𝕌`
(`symmetric_group.MapBijective`).

### Division of labor

`By`/`Derive` is the default for deduction, not a universal syntax:

- symmetric splits, induction, and side cases keep explicit structural
  combinators with named `Case`s;
- asymmetric splits linearize: when one branch is trivial and the other
  carries the argument, `Assuming`/`Unless` discharge the light branch
  inline and keep the main argument on the main line, with the decided
  guard surviving as a named `Fact` — never a nested tree whose every
  first branch is a one-line close;
- equality and relation chains use `CalcEq`, `CalcRel`, `CalcOrder`, or
  `CalcLeibniz`;
- rewrite ladders keep visible ordered rewrites;
- a single named outside fact closes with `Cite(dep)`;
- a single resident `Fact` closes with `By(f)`;
- low-level choreography with no paper-proof word is hidden inside a
  mathematical verb or, exceptionally, behind a small `a.Do(...)`.

Do not author new sites using superseded deduction blocks or `HypHandle`
ceremony. Prefer `Derive`, `Fact`, `a.Hyp`, `a.Obtain`, and `f.At`.

## The section boundary is a binding form

A section statement is a lambda, and it is closed, in the one standard
form every member is written in: `∀x₁ … xₙ. H₁ ∧ … ∧ Hₘ ⇒ C` — every
binder in front, the premises one ∧-joined antecedent, a conclusion that
opens with neither ∀ nor ⇒; the lint refuses a member stated in any
other form, reading the text its author wrote. No statement or claim text spells ⊢ — neither
hypotheses left of it nor `name : type` declarations; a statement with
hypotheses panics at its door, naming the closed spelling, and the lint
refuses the text. Its closure signature binds the statement by dependency
— a hypothesis depends on the binders it mentions — the parameters after
`*Argument` opening it in their order:

- a `Term` parameter, or its typed spelling (§"The typed surface"), binds
  the next binder;
- a `Fact` parameter binds the hypotheses whose binders are all bound
  before it: standing alone, all of them, read apart by `a.Conjuncts`;
  standing with other facts, one each, in the statement's order. A typed
  structure fact binds its structure's hypothesis, a `*Member` its
  membership; where no hypothesis is available yet, a `Fact` binds a
  bundle — the binders next in order up to the hypothesis that mentions
  every one of them, that hypothesis the structure fact at its components;
- what the parameters leave stays in the goal as a statement, `∀(the
  binders not bound). (the hypotheses not taken) ⇒ C`: an induction that
  must not pre-strip its variable binds the parameters before it and
  inducts in the body.

Do not reconstruct statement binders with `ctx.Var` walls or opening
`StripQuant` choreography. Binder names and closure parameters must agree; the
lint enforces this where static inspection is possible.

A statement is written as one string, or in parts — `Statement{Binders,
Hypotheses, Conclusion, Abbrev}` — which assemble to the one string:
the hypotheses, one per line, ∧-joined into the one antecedent (a
hypothesis that is itself a conjunction stays one hypothesis where it is
written second or later; written first, it reads as its conjuncts); the
abbreviations, the names the statement and the texts of its proof
spell as `«Name»` for a compound term that recurs, each a spelling and
nothing more (the member's key is the expanded statement's). One
constant at three or fewer arguments, each a name, a field of one or a
numeral, is no compound term: it is written out, its components
implicit (`polynomial_degree(p)`, `field_ring(L)`, never a `«deg»` or a
`«ring»`), in every table, and a lint refuses the entry. A constant at
more of them — the datum a chapter fixes at its six binders, a complex
at its parameters — may be named where it recurs, as a paper fixes its
notation once; whether the name earns its place is the review's call.
A term the chapter's statements share is an entry of the chapter's
table, declared once on the family handle
(`registry.NewFamily(…).WithAbbrev(Abbrev{…})`) and spelled by every
statement and every text of the chapter without declaring it; a
member's own table is read under the chapter's and holds only the
entries that are its own. A chapter whose statements
spell another chapter's names, one cut from it as a rule, reads that
chapter's table before its own (`.WithOuterAbbrev(<chapter>.ChapterAbbrev)`, the read
chapter exporting `ChapterAbbrev` from its family.go) and declares only
the entries that are its own: one name, one meaning, across the
tables (an entry reached through two read tables, one name with one
text, is read once), and the read entries written over binders the
reading chapter's statements share. A definition's equations read
under the same tables, its own declared as `DefEntry.Abbrev`; the
constant and its characterizing statement are the expanded equations'. A statement with a premise
reads in parts whichever door states it — a member's constructor or a
section's, a card, a lift, the body of a structure's or a predicate
definition's law — and `TestLintStatementInParts` refuses it written as
one string. A claim of the proof takes the same parts: `a.Have`, `a.Obtain` and
`a.Hyp` read a `Statement{Binders, Hypotheses, Conclusion}`, with
no table of its own, since a claim reads the member's. A claim with a
premise is written in parts where its one string would run past the
line, 100 columns from its indentation, and as the one string where it
fits — a bounded
quantifier `∀x:A. x ∈ s ⇒ …` reads as one formula — and
`TestLintClaimPartsByWidth` holds both sides. A claim is not held
to the standard form, as `By` and `Simp` read a telescope either way. A
statement's text is data, and a claim's with it: a literal, a `Statement`
literal, or a structure door's — never Go assembled from constants and
helpers, which is what the abbreviations replace.

A member's constructor matches its shape: `family.Theorem` for a
single-section member, `family.Sections` for a multi-section member whose
returned top section is the public headline, and a door of its own for a
transported twin, a definition, a structure's law or an instance. The
constructors, a worked member and the shapes that stay outside the binding
form are the manual's (`engine/xugo-engine.md`, §"The section boundary
binds" and §"The constructors").

Vocabulary belongs to the chapter or domain rather than each proof. A
chapter states its alphabet as data — the rows of its vocab.go — and a
name's type is declared once, at the lowest common stable layer: the domain
table or the mint, and the row itself only for an instance the chapter
pins. The row kinds and the handles generated from them are the manual's
(§"The family vocabulary").

**What a row buys, and when a stated name needs one.** A statement
parses without a row for every minted constant it names, so the absence
of a row says nothing about a name — measured by dropping `listing`'s
`Term("list_length")`, regenerating, and replaying the family green at
unchanged keys. A row buys one of two things, a PINNED instance in the
parse scope or a handle a body builds terms with, and a chapter declares
one exactly when it wants one of them. A name a chapter merely states,
at the instance its arguments give it, needs no row; a chapter that
declares such a row anyway documents a pin it does not need. A chapter
header states which of the two a row was declared for when it is not
obvious; it does not state a rule of its own.

## The typed surface: statements carried in Go types

Go 1.27's generic methods let the surface carry a statement's types in the
host language: `ext.Expr[T]` wraps a term the compiler knows to have HOL type
`ext.HolTypeOf[T]()` (the phantom vocabulary, ext/holtype_phantom.go —
`ext.A…E` for the shared statement letters, a letter beyond them declared
once by the generated wrapper file of each family whose statements bind it,
`Fun/Fun2/Fun3/Set/Op` for arrows, concrete
phantoms such as `ext.Nat` or a typedef's own declared where the type's
identity lives — for a type a family mints, that family's vocab.go);
`ext.Arrow[X, Y]` / `Arrow2` wrap arrow terms born applicable (`f.Apply(x)`,
domain and codomain static); `ext.Typed[T]` is the parameter currency both
flow into. A proof file writes all of these bare (`*Expr[Set[A]]`, `Nat`,
`Real`): they are names of `library/authoring`, which the file dot-imports.

Reach for the typed spelling FIRST wherever a value has a phantom — a
closure parameter as `*Expr[φ]` / `*Arrow` / `*Vec[Elem, DimN]`, a term as
`TermAs` / `VecAs`, a cite as the wrapper's `At` — and drop to the untyped
form only where no phantom exists. These are Go 1.27 generic methods; a
body that repeats a type or a dimension at every cite is one that did
not reach for them.

The discipline is **1:1**: every typed spelling maps onto exactly the untyped
runtime call it replaces — same Fact contents, same install form, same
recorded steps. The typed layer buys compile-time checking and inference,
never a second grounding path, and it deliberately carries no
term-construction surface: propositions stay claim TEXT (§The math layer);
what is typed is CHECKING and FLOW — adopting a value at an asserted type and
carrying that assertion into the slots that consume it. Three places consume
it:

- **Typed binder closures.** A section closure's ∀-parameters are spelled
  at their statement types — `*Expr[φ]`, `*Arrow[X, Y]`, `*Vec[Elem, DimN]` —
  instead of `Term`; the binder's HOL type is checked against the
  parameter's phantom at plan time, and an arrow binder arrives
  applicable. Same goal moves, same tree.
- **Typed verbs.** The untyped verb plus a checked adoption (`ext.As`, the
  one gate): `a.FixAs[T]()`, `a.TermAs[T](s)` and their siblings.
  `TermAs` reads its text at T, so a polymorphic constant the text
  leaves bare takes T's instance (`a.TermAs[Set[A]]("∅")`).
- **Wrapper theorems.** A family's entries are born wrapped — `var Sing =
  singThm{family.Add(…)}` — one name serving registration, the entry a
  card's or a definition's `Deps` names (`registry.EntryLike`) and the
  typed citation surface. The wrappers are
  generated from the entries' own statements. A cite's type instance is
  INFERRED from its typed witnesses, always exact, the engine's speculative
  adaptation never running on the typed surface; where there are no
  witnesses it is bound BY LETTER, one named binding per statement letter,
  so the argument order carries no meaning and NO positional multi-letter
  type-argument surface exists to silently re-pair under a restatement.
  The statement letter lives in exactly one executable place, the binding
  that names it; no spelling anywhere depends on normalization order. A
  statement naming a typedef renders as the typedef's own phantom,
  declared beside the mint, so the Go type is ONE type wherever a
  signature spells it.

The parameter spellings, the verbs, what the generator writes and the
scope a phantom is in are the manual's (`engine/xugo-engine.md`, §"The
section boundary binds" and §"The generated wrappers").

**The dimension refinement.** A term-level vector chapter's carrier is
`num → A` for every dimension; the dimension is a TERM in the statement
(`vec⟨n⟩(u)`, `dot⟨n⟩(u, v)`, `‖u‖_n`) and a PHANTOM on the Go surface —
`*Vec[Elem, DimN]` for a vector, `*Mat[Elem, Rows, Cols]` at two
dimensions for a matrix, whose carrier `num → num → A` is read as a
sequence of row vectors, and `*VecFun[Elem, Source, Target]` for a map
between two vector spaces, whose carrier `(num → A) → num → A` is read on
the vectors of one dimension and into those of another; the image of a
vector under a map is a vector at the map's target. A typed parameter
anchors its phantom's letters to the dimension binders fixed before it,
each operation declares its dimension argument at its definition, and the
generated cite writes the dimension off the vector: citing at the wrong
dimension is a compile error and crossing two is unrepresentable. A
vector read at a dimension that is no binder — a Let, a literal,
`suc(m)`, a degree — is anchored at the term, or at the dimension its
membership fact spells, and carries `SomeDim`: two such vectors are tied
at the cite rather than at compile time. Which refinement a binder gets is
decided by its carrier shape and never by position, and nothing is elided
the statement does not determine — a binder read at two dimensions, or at
one that is not a binder, keeps its plain slot. The kernel sees the
untyped cite plus the premises, as always. The anchoring rules, the verbs
and what a generated `At` takes are the manual's (§"Vectors and matrices:
the dimension rides the type, not the statement").

**The carrier refinement.** A structure on a set — `group_on(G)`,
`module_on(R, M)` — has its carriers among its components, and the Go
surface carries them as phantoms of package `on` (ext/on): a fact of the
structure is a typed value, `group.GroupFact[on.G]`, a group fact on G.carrier,
an alias the generator declares beside the structure's definition for
every carrier structure with one or two carriers (a set component, or a
record whose `carrier` field is one). Whole-type record views have no
carrier refinement: their record's stored carrier does not bound their laws. It is named by the structure's stem, its
definition's name less the `On` or `In` its constant ends in, since the
carrier phantom says where the fact lives, and it is the one name of the
fact: every spelling writes its carriers. A
point of a carrier together with its membership is a
`*Member[A, on.C]`. A structure law's closure binds its
hypothesis as the typed fact and each point a run of binders guards as a
member, the guard consumed as their evidence, so the body never names
the guard conjunction. A law read at a typed fact takes members of that
fact's carriers alone, a law of another structure does not read there, a
projection law reads as the typed fact of the structure it concludes
(`module.AddGroupOn.Read(module)` is a `group.GroupFact[on.M]`, no
Have), and a closure law whose only antecedent is its points'
memberships reads, at its points, as the member it concludes
(`group.MulIn.Read(additive).At(fx, gx)` is the member F(x) + G(x)).
Crossing two carriers or two structures is a compile error. An untyped
instance — a Fact, an instance entry, a reading of a structure without a
phantom — reads at `proof.AnyStructure` and `on.Any`, its members paired
by `proof.MemberOf`, so every untyped call site reads as it did; the two
worlds meet by an explicit step (`a.MemberOf[on.M](x, fact)`, `AsFact()`).
The 1:1 discipline holds here too: a typed fact is its Fact, a member
stands in a premise list for its evidence (a guard two members share
listed once), and a typed reading is the reading `proof.Read` builds.
The binding rules, what the generator writes and the measured limits are
the manual's (§"The structure doors", "Typed structure facts").

Exits are explicit: `Core()` is the term a typed value holds, a
partial-witness cite and a theorem that is no entry stay on the untyped
forms the manual lists, and a site measured to NEED the speculative-σ
adaptation takes the reserved name `AtAdapted`, never the natural ones —
no site has needed it. The language feature's measured boundary — what a
generic method can express, and the walls — is pinned executable in
`utils/generic_test.go`; read or extend that file, never re-probe it.

The verb set grows by demand, not by symmetry. Only INTRODUCTION verbs
qualify for a typed variant — verbs whose result is a term the body threads
onward (`Fix`/`Term`/`Let`/`Const`/`Var`/`Numeral`, and the existential
eliminations `Obtain`/`Unpack` with their two- and three-witness twins;
`Binder` is the reserve bench). Shaping markers (`DenotedAs`,
`HilbertDenoteTerm`), closers, and Fact-valued results never get one: a Fact
carries a statement, and the typed layer types TERMS. The variant must be the
thin composition `verb + ext.As[T]` through the one adoption gate — same goal
move, same install, the 1:1 discipline — and where that composition cannot be
spelled per value there is no variant: `Skolemize` returns a slice, and the
typed spelling of skolemization already exists (typed closure parameters, or
a `FixAs` chain). A consumption verb (`Take`) may instead get a
`Typed`-parameter variant — the check moves to the input — under the same
demand rule. Until a variant exists, the interim spelling is `ext.As[φ](…)`
around the untyped verb, identical by construction; a landed member carrying
that wrap IS the promotion signal — `grep `ext.As[` library/proofs/` is the demand
ledger, the orchestrator proposes at aggregation, taste gates as always. A
new verb lands in `prover/proof/typed.go` beside its siblings plus a
cheat-sheet row; the generator is unaffected.

## Structures: a predicate over explicit components

A mathematical structure — a monoid, a group, a ring, an order — is stated
in the corpus as a PREDICATE over its explicit components on a free
carrier: `comm_monoid(op, e)`, `group_on(G)`, `comm_ring_on(R)` and
`field_on(F)`. Groups, rings and fields hold their operations and carrier
in `group_ops(A)`, `ring_ops(A)` and `field_ops(A)` record values.
The shape has four rules, and every
structure follows all four:

1. **Identity is the explicit value or component tuple.** Two
   structures on one carrier (ℝ's additive and multiplicative monoids) are
   two instances with different components; no selection ever reads the
   type alone. Every distinguished element is a component — never derived
   by choice inside the predicate — so an instance names all of them and
   a consumer rewrites none of them. **The arity is the signature's and
   stops there:** an operation the structure's own equations would define
   from its other components — a power from the product, a multiple from
   the sum, a vector operation from the ring's — is not a component but
   a constant Defined over them with the components implicit
   (`vec_sub(sub, u, v)`, reading the ring's subtraction pointwise;
   "Implicit component arguments" below), its symbol that definition's
   Notation. The tower keeps two
   such components, the ring's `sub` and the field's `div`, and admits
   no third: a structure's component list does not grow with a chapter's
   vocabulary.
2. **A law is a Horn theorem** `∀comps. S(comps) ⇒ body`, written
   `S.Law(body, proof)` so that the components are stated once, in the
   definition. The apply rung reads the components off the goal and the
   rest off the resident instance; a component the body cannot pin is
   pinned by name (`Where`). As a REWRITE the same law is a `Simp` rule
   at the hypothesis — `Simp(Fwd(LeftInverse))` collapses
   `add(neg(x), x)` to `zero` with `zero` read off the resident
   `abelian_group_on(G)` — so a chain of law applications is
   a chain of rewrites and mints no key; a rule fires in the direction
   its statement writes it, and `Rev` is that direction's reverse
   (the rule is served in its stated form, as a premise is). A structure's
   axioms are its first laws (`S.Axiom`), cited at a hypothesis inside
   the chapter and at an instance outside it, in the same spelling. A
   predicate defined as a conjunction that is not a structure — a
   subgroup — reads its conjuncts off the same way, through its
   definition (`SubgroupDef.Conjunct(body)`).
3. **An instance is a theorem of a chapter of the carrier, and it adds
   no dependency** — `S(concrete components)`, the predicate unfolded
   and one case per conjunct citing the carrier's own laws. Its
   obligations are exactly the axioms; an instance that must prove more
   is a framework leak. It lives in a chapter of the carrier that
   already depends on S's chapter, the lowest one its readers reach:
   ℝ's ring in `real_ring`, its metric in `real_topology`, ℝ as an
   integral domain in `real_formal_series`. Where no chapter of the
   carrier depends on S, the instance opens one above both
   (`real_closed_instance`). It is never S's chapter, since an abstract
   chapter imports no concrete carrier, and never a chapter of the
   carrier that would import S for the instance alone: everything that
   chapter carries would then sit on a structure it never reads.
4. **Inheritance is the definition's shape.** A super-structure's equation
   is the conjunction of its sub-structures' predicates plus its own
   axioms, so a sub-structure at a hypothesis is an Axiom of the
   super-structure, and a carrier builds its instances bottom-up — the
   monoid, then the group citing it, then the ring citing both — each
   conjunct closed by the carrier's own law or the instance in hand. A
   consumer holding only the ring's instance reaches a sub-structure's
   through the projection (`By(comm_ring.AddGroupOn, CommRing)`). The
   instance graph is that set of named theorems; nothing searches it,
   and a consumer names the instance its law wants.

**One proof per law: the carrier form and its view.** A structure
whose instances are quotiented, taken sub-objects of, or indexed in a
family is stated on a carrier set, with membership guards. Groups,
commutative rings and fields hold the operations and that set in one
record: `group_on(G)`, `comm_ring_on(R)`, `field_on(F)`.
A carrier law states its guards first among its hypotheses:
`GroupOn.Law(Statement{Binders: "∀x y:A.", Hypotheses: []string{"x ∈ G.carrier", "y ∈ G.carrier"}, Conclusion: "…"}, proof)`.

The whole-type predicates `group(G)`, `comm_ring(R)` and `field(F)`
state their laws on every value of the component type, independently
of the record's stored carrier. The chapter proves a bridge once,
`group(G) ⇔ group_on(restrict_group(G, 𝕌))`, and declares its view with
`Group.AtUniverseRecord(GroupOn, GroupOnUniverse,
"restrict_group(G, 𝕌)", set_basic.InUniv, set_order.SubsetUniv)`.
Every whole-type law is then a view of its carrier law,
`GroupAtUniverse.Law(body, AssocOn)`, with its own statement and key,
proved by the door. The view discharges universe conditions centrally;
whole-type consumers keep the unguarded interface. Concrete carriers
such as ℝ, ℂ and ℤ keep their whole-type instance theorems. A genuine
carrier such as the cosets reads a guarded law at its carrier instance.

Predicates on subsets or maps take their ambient records:
`subgroup(G, h)`, `ring_ideal(R, I)`, `group_homomorphism(G, H, f)`
and `ring_homomorphism(R, S, f)`. At a whole-type instance the ambient
record's carrier is replaced by `𝕌`. Restricting a structure uses
`restrict_group`, `restrict_ring` or `restrict_field`. Forgetting
structure uses a named map such as `additive_group(R)` or
`field_ring(F)`. Monoid and equivalence chapters keep explicit component
predicates and `AtUniverse`; their fold substrate is unchanged.

The layout follows: `proofs/algebra/<kind>/<structure>`, one family per
structure predicate, the kinds mirroring the tower (group-like, ring-like,
fields, order-like), an aggregator per kind once it holds two families. A chapter
unfolds only its own predicate; what it needs of a sub-structure it cites
through that structure's laws at the projection. The fold mechanism's
`monoidal_op(op)` — the choice-named reading of a commutative monoid — is
bridged once, in both directions, in `comm_monoid`; every chapter above
reads a fold through that bridge rather than restating it. A structure
whose components the author spells rather than reads off a Define is
named as one by `family.StructureOf` (no definition entry is the laws'
dep) and states its laws through the same door: `iterate/monoidal` does,
with `op` the one component and the carrier at the chapter's letter
throughout.

An instance parametric in a term — the n-vectors at every n, every
subset's discrete topology — states the predicate under a ∀-prefix
through the same door, the prefix bound as the section's binders
(`euclidean.EuclideanMetric`, `topological_space.Discrete`). A structure
whose components are DERIVED from another's — the vectors
over a ring, `abelian_group_on(mk_group(vec_add(R.add),
vec_zero(R.zero), vec_neg(R.neg), 𝕌))` under
`comm_ring_on(R)` with `R.carrier = 𝕌` — is a conditional instance, and
the Instance door has no form under a hypothesis. Until it does, such a
member is a Law whose body is the structure predicate, proved by
unfolding the predicate and the sub-structure predicates it is the
conjunction of and closing one Case per conjunct, in the definitions'
order (`vector/vec_space.AbelianGroup` is the model); the comment names
which definitions were unfolded, since the reader cannot see it from
the cases.

**Implicit component arguments.** A derived operation of the structure —
`vec_add(add, u, v)`, `vec⟨n⟩(zero, u)`, `dot⟨n⟩(add, mul, u, v)` — reads its
components as leading arguments, and its definition declares them
implicit (`DefEntry.Implicit`). Under a scope that binds those names,
or has a record declaring the corresponding fields — the only one, or
the one the application's types pick among records on different
carriers — the text leaves them out; records on one carrier leave the
choice to the text, which names the record. A locally bound component or record takes priority
over a family instance's default; a variable that has the name of one component and carries no
structure — no structure predicate is applied to it and it is no record — beside components a record
or the instance supplies is refused, being no component of that structure. A law under `S.Law` binds its components by its ∀-prefix, so
its body spells `vec_add(u, v)`, `vec⟨n⟩(u)`, `monoidal_op(vec_add)`,
`neutral_elem(vec_add) = vec_zero`; a chapter working at an instance binds them once,
at its family (`WithInstance(comm_ring.CommRingOn, real_ring.CommRing)`
reads `R ↦ real_ring` and its normalized fields
`add ↦ real_add, zero ↦ &0, …` off the instance theorem; shared fields of
several instance records need their qualifiers), so its
statements spell `dot⟨n⟩(u, v)` and `vec⟨m⟩(x)`. The completion is the
parser's (ext/dsl/implicit.go) and the inverse is the printer's: the
kernel term, the key and every consumer see the explicit application, and
how each text is read and served is the manual's (`engine/xugo-engine.md`,
§"Text format", "Implicit structure arguments"). The
explicit spelling stays legal — under an instance's binding an application
spelling ANOTHER instance's components in full is read as the prefix it is,
by the arguments' types, so a chapter at ℤ states the real form of an image
as `dot⟨n⟩(real_add, real_mul, vec_of_int(u), vec_of_int(v))` and the served
spelling keeps that side explicit. A statement that carries no structure over
a component spells it: a member stated for ANY zero (`vec_space.VecMono`)
spells `vec⟨m⟩(zero, u)`, and a theorem about closed sets that uses no axiom
of the topology spells `closed_in(T, c)` — that spelling is the visible sign
that the statement needs no structure. The parser would complete the short
form from any binder of the component's name, structure or not, with the
same key, so the rule is a lint's (`TestLintImplicitSpellingNeedsStructure`):
an implicit argument a registered statement leaves out and the parser
completes to one of the statement's variables must be a variable some
structure predicate in the statement is applied to; the served spelling
reads the same rule back. Completion to a
family's instance component is licensed by the family. The definitional layer always spells every binder
of the constant it defines; its body reads every OTHER constant as a member's text does —
a declared notation lowers, and under an instance the components it leaves out are completed.
What the equation states — the definiendum, and each body conjunct that applies a structure
predicate — is served spelled in full; a use in the body is served as a member's text is.
The dimension is never implicit: it varies within a statement, and a
term-level dimension is the chapter's mathematics, not its context — it
rides a NOTATION instead where one is declared.

**Bundles.** A statement over several structures names each once: a
bundle is a name standing for a structure's components, written out by
the parser before anything reads the text (ext/dsl/bundle.go; the
manual's §"Bundles"). `∀G:sheaf_of_rings(C, D).` binds a sheaf of
rings — its fresh components named after the definition's binders,
under the bundle's name where the text holds a binder's already (`G_T`
beside a sheaf F whose `T` came first), its subject G — and states the
predicate as the antecedent, the subject being the component the
definition declares the predicate said of (`DefEntry.Subject`: the ring
record, the map a homomorphism is, the sections a sheaf assigns; a
structure on a whole type over components declares none, and one with
no single subject the letter its laws fold under,
`∀S:short_exact_complexes(A, B, C, D)`, `DefEntry.Letter`); a structure
on one record has the record as its one component, so
`∀S:comm_ring_on(B).` binds a ring record S;
`lrs_isomorphism(F, G, φ, ψ)` passes two bundles where
the constant declares they go (`DefEntry.Bundles`; a structure's own
sub-structures are read off its definition); `G.T` is a component and
`S.add` a record's field; and a
constructed structure is a record value; helper operation tuples
(`Family.Tuple`) remain text abbreviations inside an explicit constructor. A structure indexed by
another — the ring on each F(U) of a sheaf of rings — states the fibre
in its definition as a conjunct under ∀, and a fact of it states the
fibres as a FAMILY: a fibre is named by applying the subject to any
term, `comm_ring_on(F(U))`, `ring_homomorphism(F(U), F(V), res(U, V))`,
`local_ring_on(stalk_ring(T, F, res, x))`.
The kernel term is the
spelled-out one, so a statement is free to say it either way and its
key does not move; the chapter spelling folds a spelled-out binder run,
argument block, fibre and tuple back. A bundle is no term: a set of rings, a
choice of a ring or a category whose objects are rings is not
expressible this way, and a chapter that needs one states it over record values.

**Notations.** A definition declares its constant's notation with the
definition's own binders (`DefEntry.Notation`), in one of three forms: an
OUTFIX (`"‖u‖_n"` for `vec_norm⟨n⟩(u)`), or an INFIX or PREFIX over a
symbol the grammar already parses (`"u + v"` for `vec_add(add, u, v)`,
`"a ⟶ l"` for `real_converges_to(a, l)`). The parser lowers it in the
chapter's scope while the printers fold it back, and an operator is
resolved by OPERAND TYPE, as `+` at num, real and int already is: several
constants may declare one symbol, each on its own carrier (`z * w` on ℂ,
`p * q` on permutations). A sum is the BIG OPERATOR `Σ_{i<m} body` /
`Σ_{i∈s} body` that a carrier's named sum declares (`DefEntry.BigOp`), and
a carrier that contains the real line declares its embedding as the
chapter's `&` (`DefEntry.Coercion`, τ as the chapter's domain by
`WithCoerceDomain`). The forms, their precedence and what each text reads
as are the manual's (§"Text format", "Implicit structure arguments").

A record's fields declare the operator symbols they carry
(`DataField.Symbol`: ring `add ↦ +`, `mul ↦ *`, `neg ↦` prefix `-`,
`sub ↦` binary `-`). The parser reads them at the operands' types:
under `R:ring_ops(A)`, `x + y` is `R.add(x, y)` and `-x` is `R.neg(x)`.
Two records with the same operation signature require explicit fields.
Predicates over separate component variables may declare the same
binding through `DefEntry.Symbols` and a resident structure fact.
Distinguished elements stay explicit fields, `R.zero` and `R.one`.

**Records.** A structure may hold its components in VALUES of record
types — a record is `family.DefineData` with one constructor
and `Fields` (`group_ops(A)`, `ring_ops(A)`, `field_ops(A)` and
`module_ops(A, B)`) —
and is then a predicate of the values: `module_on(R, M)`, a ring R and a
module M over it. A text reads a part as a field of a value (`R.zero`,
`M.carrier`) and an operation by the symbol its field declares, at its
operands' types (`c + d` at scalars, `u + v` and `c • u` at vectors;
`DataField.Symbol`), and a notion derived from the structure takes the
values too (`submodule(R, M, N)`, `module_dim(R, M)`). A component
whose operands differ carries its symbol like any other, so the
scaling `c • u` stands beside the two additions each at its own
carrier. An instance is a packed value (`mk_module(…)`, or a definition
that packs one, `free_module_record(R, S)`), and a law read or grounded
there states the parts it was packed from: the engine hands every
instance over with each projection of a packed value computed (the
instance normal form, the manual's S5), so no proof spells a record's
projection equations, and a proof states a part as the part
(`P.terms(n)`, never `complex_module(P, n).carrier`).

**Readings.** A law is also a VALUE at an instance: `law.Read(instance)`
— `dot.AddLeft.Read(real_ring.CommRing)` — is the law with its
components pinned to the instance's and its hypothesis discharged,
derived by the kernel when a verb consumes it, served in its stated form,
keyless. It is ONE cite target for the three faces a law is wanted on: a
`By` premise, a `Simp` rule and the typed ground cite. The instance may
also be a RESIDENT structure fact of the proof in progress — the
hypothesis a Law's closure receives, a Have's fact — and the reading is
then the law UNDER that hypothesis. What a reading derives, what its `At`
takes and how a `By` materializes one are the manual's (the cheat sheet's
`Read` row). Three rules are the chapter form's:

- A member whose whole body is such a cite is not written: the value is
  cited where it is used, and the query tools find it. A law whose body
  states another structure is a PROJECTION
  (`ring_homomorphism.AdditiveHomomorphism`, `comm_ring.AddGroupOn`),
  and what every law of that structure states when read through it —
  "a ring homomorphism keeps zero" is `group_homomorphism.MapOne` read
  at `AdditiveHomomorphism` — is matched by `retrieve` by goal, in a
  group after the members, with the chain and both spellings of the
  value (the manual's `retrieve` entry). `query member` and the index
  list under the projection law the laws of the structure it states,
  read at it, and mark the projections among them, under which the
  reading continues.
- `By(law, instance)` still closes by the rung and remains right where the
  law is applied at a goal.
- A structure fact another law asks for as an antecedent is the one hop a
  chapter stated over a structure otherwise writes as a Have per use
  (`a.Have("pointwise addition folds", "monoidal_op(vec_add)",
  By(vec_space.MonoidalVecAdd, ring))`): where the fact is consumed once,
  read the law at the hypothesis in the premise list instead and write no
  Have. The rung itself never chains — a Horn law cited beside the ring
  does not supply the antecedent the rung asks for; the reading does.

**Moduli: a set of records, its classes, and the structure laid on
them.** A structure of a kind on a carrier is a value of its record type
that the structure predicate holds of, so the structures of that kind
on a type form a SET of records, and a family of structures is a
function into the record type (the sheaf `F : set(A) → ring_ops(B)` of
`scheme(T, F, res)`). A classification is written in three moves and
needs no door of its own. The isomorphism is an equivalence on that
set, proved once as a member (`curve_degree.PairMultipleEquivalenceOn`).
The classes are `quotient_on` of the set by it — never the quotient
door, whose respectfulness is unconditional while an isomorphism
respects the operations only under the structure hypotheses
(§"Definitions") — and an invariant of the structure descends to them
through `respects_on` and `induced_map`. The structure the classes carry
is a record on the class set, proved as any instance is:
`curve_degree.PicZeroAbelian`, the group of Pic⁰ on `curve_pic_zero`,
and `biaffine_deformation.BiaffineExalGroupOn`, the Baer sum on the
classes of extensions, are the models; a set a classification bijection
parametrizes takes the record along the bijection's inverse through
`group_homomorphism.ImageAbelianGroupOn`, never axiom by axiom
(`elliptic_curve.PointGroupTransported`). The price of the set is one
type: a class is a set of records on ONE host type, so an isomorphism
between records on different types is an equivalence only once both are
realized on the host, and a statement that reads a class carries the
universe hypotheses that make the host large enough
(`biaffine_deformation.BiaffineExalClassEqIff`: a class on any type is
one of the host's). Where the classes are identified with another set —
the deformations of an algebra with the classes of `D^1(T/R, M)`,
`algebra_deformation.DeformationsTorsor` — the member states the
identification as the torsor or bijection it is, and the structure the
classes carry is read through it.

## Definitions: a chapter mints its own constants

A chapter's constants and types are DEFINED in the chapter, through the
define doors (`family.Define`, `family.DefineType`, `family.DefineData`,
`family.DefineSpec`, `family.DefineInductive`, `family.DefineQuotient`),
by the chapter whose definitional layer closes over them — the same
placement rule the domain tree states. A quotient's door registers the
seven facts the quotient comes with (surjectivity, the induction
principle, soundness, exactness, class equality, and the two image
laws) and takes the relation's `equivalence(R)` entry as its one
input; a function on its classes is a `family.Define` whose equations
take the class map as a constructor pattern (`op(⁅a⁆, ⁅b⁆) = ⁅a + b⁆`)
and whose `Respects` closes the respectfulness obligation — nothing
else about a quotient is a chapter's to prove by hand (a quotient over
a polymorphic carrier takes the carrier's letters as its parameters,
`free_group(A)`, and every definition over the type or its class map
names the quotient entry in its `Deps`, the init-order rule below). A
lift's respectfulness is unconditional — the obligation and the
equation are statements without hypotheses — so a function on classes
that respects the relation only under a hypothesis has no form at the
door: the extension of a map on generators to the free group respects
word equivalence only where the target is a group. The definition entry is a member: its statement is
the characterizing equation (or a type definition's two axioms), its
Build the one
definition step, its identity its own key. A relation defined by
introduction rules (`family.DefineInductive`) has no definition entry:
its Rules, Induct and Cases entries are the definition's face, a
definition of the same family that spells the relation names one of them in its `Deps`, and the
closure form the relation is minted with is not a proof surface —
`Unfold` refuses it, and nothing in a chapter reads it.

Every constant the corpus spells is minted by a chapter. The corpus's
constant registry (`registry.ConstMetaManager`) holds the engine's
built-ins and the chapters' mints and nothing else; there is no other
source a statement, a proof body, a vocabulary row or a serve bundle
can read a constant from, so a name no chapter defines fails to parse
at registration. The door is the only way in: the constant registry
records where every chapter mint was stored from, and the gate
`TestEveryMintIsADoor` (library/integrity/gates) demands each such
mint is a door entry's — a chapter that hands the kernel a λ itself
(`ext.ConstDef`) is kernel-sound and fails the gate. A chapter defines what its statements spell and its
imports do not already define, before the member that spells it (a
definition that mentions a same-chapter constant names the minting
entry in its `Deps` — the entry var named there is what orders the two:
without it Go initializes a package's variables in declaration order,
its files taken by name). A Go
value that holds a minted constant — the term a `DefExpandStep` unfolds,
a meta a helper builds terms from — is read the same way, through a
chapter helper whose first argument is the minting entry
(`mintedTerm(PrimeDef, "nat_prime")`): the argument is the
initialization edge and is not otherwise read, and a lookup by name
alone may run before the mint. A theorem that states a definition's
own equation IS the definition: the two have one key, the registry
refuses the second entry at initialization (`duplicate Key`), and the
member is written as the `family.Define` under its name. A
spelling from a reference that the corpus does not adopt is never
minted, and a
member is stated in the chapter's own vocabulary. A constant
the text DSL spells for its own surface (`≥` on ℝ is `real_ge`) is
still a constant the corpus states, and the chapter that owns it mints
it. A type's inhabitation is never trusted: the door proves it at the
mint when the normalizer decides it, and otherwise takes the chapter's
entry proving `∃x. P(x)` as a promise the replay discharges through
that entry.

## Argument structure: flat chain → named cases

The most important per-proof refactor is turning a search-trace action chain
into an argument whose branches and intermediate claims have mathematical
names.

Operational rules:

- Two or more closing actions such as `Basic`, `CnfRefute`, or
  `HilbertDenote` inside one uninterrupted chain are a signal to expose the
  separate leaves as named `Case`s.
- Case labels say what is proved, not “claim”, “after”, “left”, a step number,
  or the tactic that happens to close it.
- A recurring anonymous fact should become a local lemma, sibling section, or
  family entry according to its fan-in and mathematical importance.
- Comments must not substitute for proof structure. If a comment explains
  which leaf a refuter is closing, give that leaf a checked name in the proof.
- Green replay is necessary but does not certify curation quality. A long,
  unlabeled search trace is still a curate mismatch.

Flat form is acceptable for:

- a section that closes in one action;
- a short chain whose outer `SplitIff`, induction, or cases already exposes
  the structure;
- a short terminal pair operating on the only leaves remaining inside a
  mathematically named case.

The test is simple: could a mathematician-agent unfamiliar with the theorem
recover the proof idea from the Go file?

## What "elegant" means

Avoid both extremes:

- **Under-abstraction:** a raw search trace with no argument visible.
- **Over-abstraction:** a generic framework whose parameters hide the
  mathematical idea of each theorem.

Related theorems may share a fixed solver kit, a local helper, or a common
lemma. Parallel proofs may also remain explicit when that is clearer.

When the same low-level motif occurs at least three times corpus-wide or twice
inside one large proof, first ask whether the layer below the chapter lacks a
primitive. Record emit-only problems as emit issues; record framework,
prover, or engine proposals as issues with a concrete API sketch. Do not conceal a systematic tooling defect behind many local
helpers.

## Directory organization: the domain tree

The corpus is organized by domain, with families nested as the mathematical
subject calls for (`domain/family`, `domain/topic/family`, and deeper paths).
There is no fixed limit on nesting depth; infrastructure stays at the root.
A family is a coherent theory chapter, not a batch of theorems taken from a reference.

A family's domain is chosen by the definitional layer in which its objects and
constants close. Do not place a family solely because its subject matter
resembles that domain. Dependency evidence and definitions
override intuition.

A directory is a family or a topic, never both. A family's directory
holds its own package and nothing nested. A topic is a mathematical
subject that several chapters make up. They share the topic's
directory, and the chapter the topic is named for, where there is one,
sits at X/X: `algebra/group/group` among the group-like structures,
`algebra/field/field` beside field theory,
`probability/martingale/martingale` beside `l2_martingale` and
`optional_stopping`. A chapter built on one other chapter, or split
from it, does not make a topic with it: the two are siblings in the
enclosing directory, as `cartesian/kuhn` and `cartesian/kuhn_labelling`
are, or `real/real_pow` and `real/real_sqrt`. What a topic holds is
decided by the mathematics, not by whether every family there reads X.
Whether some chapters form a subject of their own is a judgment, and
where it is unclear it is settled with the user before the directory
is laid out. A topic's Go file, where it has one, is its aggregator,
and it links the families beneath it. A family cannot be its own
topic's aggregator, because the families beside it import it.
`TestLintDirectoryTree` refuses a family nested in another family's
directory; whether a topic is a subject is held by reading.

Package names remain unique enough for readable qualified references.
A family's package is named by the family's own name with its
underscores kept (`comm_ring`, `nat_order`, `set_basic`): the package
name is the chapter's name as the registry, the directory and the index
spell it, and it is read as a qualifier in proof text, where
`comm_ring.CommRingFact` is legible and `commring` is not. Go's
convention of single-word package names is set aside for this on
purpose; a package is not renamed to satisfy it.
Cross-package prose and code use the package qualifier when the unqualified
name could mislead.

## File granularity: relatedness decides, and merging is the default

Files are reader navigation units, not theorem identity units.

- Put strongly related theorems in the same file when a reader benefits from
  seeing them together: forward/reverse directions, symmetric companions,
  successive variants, or a shared construction.
- Split when the mathematical topic, proof architecture, or vocabulary changes
  enough to deserve a separate reading unit.
- A genuinely self-contained centerpiece may have its own file at any length;
  record the reason in the chapter's README.
- Per-member files created to avoid concurrent edit collisions are
  consolidated once the concurrent work has landed.

Do not use a mechanical line threshold. Large files and tiny files are both
signals to review relatedness, not automatic failures.

Once a chapter is one file, its parts are named by what they prove, and a
cross-reference names that content rather than a filename or a construction
tier. A comment pointing at a file that was merged away is the same defect as
one pointing at a tier number: both send the reader to a map that no longer
describes the territory.

## Families: a theory chapter as a sub-package

A family package normally contains:

- `family.go`: registry manifest and embedded family CNF cache;
- proof files with package-level entry variables. A proof file that
  spells a bare name of the proof surface (`By`, `Cite`, `Argument`,
  `Expr`, `Nat`) dot-imports `library/authoring`, the one dot import in
  the module (`TestLintDotImport`). The names are in scope in the file
  that carries the import and are no declaration of the family's
  package: the package exports its own members and nothing of the
  surface, a file that spells no such name carries no import, and a
  package-level name of the family that takes one of the surface's is a
  compile error — the family's is the one renamed;
- `cards.go` when the family lays cards ahead of their proofs: the
  cards and nothing else (`TestLintCardsFileHoldsCards`), so the file
  shows what is still open. A definition laid with the cards stands in
  `definitions.go`, the blank imports that link the family's vocabulary
  in `definitions.go` or `family.go`. A card filled there leaves it for
  the proof file of its subject, a new one when no file's subject fits,
  and the file goes with its last card, taking nothing else with it. A
  card laid in a proof file, beside the theorems of its subject, is
  filled where it stands (§"Cards: a member stated without a proof");
- `README.md`: the finished chapter narrative and public member map; its
  title line, `# <name> — <gloss>`, is the one place the chapter's gloss is
  written — the index's line for the family and the package's doc comment
  are read off it. Between the title line and the first `##` section stands
  the chapter's introduction: prose, not a table, saying what the chapter
  holds and how it is organized — the overview read before any section
  (`TestLintReadmeIntroduction`);
- `vocab.go` when the family owns vocabulary: its VocabSpec rows, and the
  phantom of every type the family mints — the file exists for the phantom
  alone when the family declares no rows;
- the generated files: the typed theorem wrappers
  (`zz_typed_thms_gen.go`), carrying the package's doc comment — no
  hand-written file of a family has one, and a file's header stands a
  blank line clear of its `package` clause — and, where the family
  declares vocabulary rows, their handles (`zz_vocab_gen.go`). The
  wrapper file reads the proof surface through the dot import of
  `library/authoring` where it names it, a name outside the surface
  qualified; the vocabulary handles name the surface qualified;
- one shared `<family>.cnf.pb`.

### Entries and dependencies

Register entries through exported or deliberately unexported Go variables,
never `init` registration.

An entry whose statement normalizes to ⊤ is refused at registration, a
card included: normalization closes such a statement everywhere, so no
member can prove it (the section harness refuses the trivially true
section) and none can be cited for it, and its key is the one every other
tautology would carry. A test fixture is no exception — spell a statement
that is neither valid nor refutable.

One declaration per entry: the `family.Add` literal spells the metadata
fields first and the Build constructor call inline and last, so the entry
reads statement-first, proof-last, in one place. A separate build variable
the literal references by name splits one fact across two declarations; a
lint rejects that shape.

A proved member's dependencies are what its proof reads, and its entry does
not repeat them. A cite names the entry var it stands on, a typed reference,
so Go enforces initialization and import acyclicity over the edges a proof
spells; a package boundary that would need a string cite is a mis-cut
chapter, fixed by re-cutting the packages along the layering (the
`int_embed` read-back parts were the last such case). The family recorder
builds the member with the whole corpus on call and writes the entries the
build read — its cites, and the principles and rows it reads by a name an
entry serves — into the family blob. That record is the trust surface the
proof stands on: replay serves the member exactly the record and fails when
what the build reads drifts from it in either direction, and nobody edits
it. A card declares `Deps` instead: it has no proof to observe. A
definition's edges are read off its equation, one to the definer of each
constant it spells, and its `Deps` name only the definitions of its own
family whose mints Go must initialize before it; a constant another
family mints is ordered by the import. A door whose definition carries a
proof of its own — a WF definition's termination, a lift's
respectfulness, a specification's existence — also declares what that
proof reads.

A definition a member OPENS is a dependency. `Unfold(CDef)` names the
definition's entry and expands the constant it defines; the step reads
the definition off the constant, so no read serves it, and the recorder
writes the entry into the family blob all the same, in the member's
unfold row beside its read row. The member's dependencies are the two
together: `deps` and `dependents`, a scoped replay and the card frontier
see a member that opens a definition standing on it as they see one
that reads it as a fact (`Simp(Fwd(CDef))`, a `Cite`), and replay fails
a build whose openings drifted from the row. The extrema chapter's
`real_has_sup` members and the sequences chapter's `real_converges_to`
members are the shape: they open their definitions and stand on each of
them.

An entry cited across family boundaries is chapter API in practice. Export and
name it accordingly rather than relying indefinitely on a string reference to
an unexported implementation fact.

A family may introduce an entry for any mathematically useful fact, whether
or not a reference states it; its statement is read at review like every other
entry's.

### Inventory and names

The chapter inventory is chosen rather than inherited:

- absorb an unimportant theorem of a reference as a section or omit it from the
  chapter API;
- promote a recurring anonymous fact when it is load-bearing;
- keep a theorem as an unexported entry when it is verified chapter
  implementation rather than public API.

A bare corollary is not a member. A statement is a BARE corollary when one
cite of a member the corpus already states closes it — a `by` naming that
member and nothing else, in a session: a measurement, not a judgment of how
near the two statements look. With `∀n. ∃p. nat_prime(p) ∧ n < p ∧ p ≤
factorial(n) + 1` stated (`nat_prime.EuclidBound`), the familiar `∀n. ∃p.
nat_prime(p) ∧ n < p` is bare and has no entry. A consumer that wants the
weaker form cites the stronger member and its own cite does the weakening;
one that cited the weaker form would have lost the bound for everything
built on it. A statement that takes steps of its own to reach is not bare
and is judged like any other candidate: `PrimesInfinite` does not close on
`EuclidBound` alone — it argues through what `infinite` means — and it says
that a SET is infinite, in a vocabulary the bound does not use.

The one exception is the statement a reader would look up. Where the
stronger member does not read as the theorem it implies — a technical
strengthening in which the familiar statement cannot be recognized — the
familiar statement keeps its entry although it is bare: without the entry,
"the usual form follows" is a sentence in a README, which no gate reads.
Where the stronger member IS the familiar theorem with its constant shown
(`vec_op_norm⟨m, n⟩(f) ≤ Σ_{i<m} ‖f(basis_vector(i))‖_n`, for "a linear map
on a finite-dimensional space is bounded") the reader has what they came for,
and the existential form has no entry.

Nor does a technical intermediate estimate become a member because two
proofs need it: it is a section in each, and a name is for a statement a
reader would look up.

A statement asks no more than its proof reads. A hypothesis the proof
never reads, or reads only for a weaker one — a positive degree read
only as `p ≠ vec_zero`, a commutative ring whose ring structure no step
touches, a linear map read only as sending zero to zero — is weakened
in place: the conclusion stays, the member re-keys, and its proved
citers re-record; a citer whose own hypothesis served only to supply
the dropped one is weakened in turn. A citer that holds the stronger
hypothesis still cites it, so the wider statement costs no reader
anything. This is a fix, not a ruling. Whoever finds it makes it, as a
mechanical fix is made, and a reviewer reports it with that direction.
What the proof reads is measured, not read off the Go text — a step
that names no premise still reads the context, and an unbound handle
proves nothing — so the weakened statement is recorded before it is
kept. A weakened statement whose home is a more general chapter moves
there with it. The one question it can raise is a duplicate: a
weakened member that states what the corpus already has.

Use Go-natural CamelCase with full mathematical words. Public chapter API is
exported; demoted helpers use lowerCamel. Read the statement before expanding
a reference's abbreviations or directional suffixes. A reference's name is
provenance, not a semantic promise.

A constant is named in lowercase snake_case with full words — a datatype's
constructors included (`nil`, `cons`, `none`, `some`). A word may take the
short form its domain already reads (`add`, `mul`, `div`, `pow`, `abs`,
`op`, `dist`, `elem`: `iterated_op`, `nat_dist`, `neutral_elem`); what is
refused is a private compression a reader has to look up (`wadd`, `nsum`).
The constant table is one namespace for the whole corpus, so a word more
than one domain would want carries its domain's stem (`nat_pow` beside `int_pow` and `real_pow`,
`real_sum`, `int_div`, `list_append`, `vec_span`, and a constructor a second
type would want, `btree_node`); a word only one domain uses stays bare
(`card`, `finite`, `factorial`). The word the domains share is then an
overloaded word the constants declare (`DefEntry.Overload`, or
`SpecConst.Overload` for a constant a specification mints: `sum` on
`real_sum`, `nat_sum`, `int_sum`; `div` on `nat_div`, `int_div`), which
a text writes where the arguments pick the constant — or, when the word
has a notation, in its
delimiters (`|x|` is `abs(x)`: real_abs, int_abs and complex_abs declare
`Notation: "|x|"` beside the word, and a pair of delimiters is shared only
so). A definition's entry follows its constant
(`NatPowDef`-style: `nat_arith.NatPow`, `list.ListAppendDef`). Another
library's spelling is never the reason for a name, and a chapter README
carries no table of another library's names. The library-theorem names
the engine resolves by name (`ServesAs`) take the same form — `<type>_induction`, `<type>_recursion`, `suc_injective`,
`wellfounded_recursion`. The engine's logical built-ins (`COND`, beside
the connectives) are the logic's, not a chapter's, and keep their
spelling. A type definition's bijection is `mk_T` / `dest_T`,
whichever door mints it. The names no statement text spells follow the
same rule — the set notation's are `set_member`, `union`,
`set_comprehension`, …, the numeral encoding's `_0`, `bit0` and `bit1`.

A predicate stated on an ambient — a set, a topology, a structure
record — names the ambient first and the subject it classifies last:
`injective_on(s, f)`, `real_continuous_on(s, f)`, `subgroup(G, h)`,
`prime_ideal(R, p)`, `submodule(R, M, N)`, `compact_in(T, k)`,
`continuous_map(T, S, f)`. A structure on a set names its carrier
first and its relations and operations after it, though the carrier
is the set the structure is said of: `equivalence_on(c, R)`,
`partial_order_on(c, R)`, `complete_lattice_on(c, R, sup, inf)`,
`comm_monoid_on(c, op, e)` — as the constants built over them do,
`relation_on(c, R)`, `quotient_on(c, R)`, `has_sup_on(c, R, s, b)`. A
group, ring or field predicate has its record as subject: `group_on(G)`,
`comm_ring_on(R)`, `field_on(F)`. The set a statement is about stands
first throughout. Where the subject stands last the order also reads as
a class: application is curried and membership is application, so the
predicate applied up to its ambient is the class of the subjects on
that ambient, a set like any other — `prime_ideal(R)` is the prime
spectrum of `R`, `subgroup(G)` its subgroups, `closed_in(T)` the closed
sets of `T`, and `f ∈ injective_on(s)` is `injective_on(s, f)` by one
unfolding.
Where the subject is a function on a carrier, that class holds every
function agreeing on the carrier, and the class with one member per
map is minted with its off-carrier normalization (`hom_set`).

Reader-facing Go comments never mention another library's theorem names, seeds, generated
spellings, migration history, replay accidents, or the chapter's construction
order — tier numbers, packet and wave labels, landing dates, status markers.
Those record how the chapter got BUILT. The build record already exists in
the curation log and git, and neither is the proof file. A tier number is the sharpest case: it tells a
reader nothing they can act on while sending them to a ledger to decode it.

Refer to a part by its CONTENT: the banner label it already carries, a
positional word (above / below / the next part), or the entry itself
(`AddZero above`). The same holds in a chapter `README.md`; there a movement
list is bullets or a 1-based numbered list, never a 0-based one, which is tier
numbering wearing a different hat. Unnumbered "tier" or "layer" as an ordinary
English noun is fine — the NUMBER is what carries the process.

A chapter `README.md` says what the package holds. It never counts — members,
entries, files — and never measures the package against a source library
(what the source has and the chapter does not, how many members are
unexported): a number in prose is a claim no gate reads, and the generated
index (`library/index`) is where the corpus is counted. What a reader may
come looking for and will not find is stated as mathematics, with the
reason it is absent, never as a queue.

A chapter `README.md` writes a formula in LaTeX where Unicode cannot set
it plainly: a sum or product with its range written under it
(Σ_{n ≥ 1}), an exponent or index of more than one symbol written out
with ^ or _ (n^(1−s), Ω_{S/R}), a fraction whose numerator or
denominator is compound, a notation that stacks (the Legendre symbol), a
formula set on its own line. Such a formula is written whole, as `$…$`
on one line or between two `$$` lines; the rest stays as it is — a
symbol, a power or index already raised in Unicode (xⁿ⁺¹, H¹, A₀₁) or
of one symbol (q^m, e_j, Σ_k), a quotient R/I, a relation. A code span
quotes the corpus in its own spelling and stays as written, as does a
row giving a definition's type.
GitHub still applies markdown inside the math, so a formula holds no
backslash before punctuation, no `*` and no `|` (`TestLintReadmeMath`).
A `|` inside a table cell, in a code span too, is written `\|`: GitHub
splits a row at every other pipe and drops what passes the header's
cells (`TestLintReadmeTables`).

Put provenance in registry metadata.

A name handed to a different theorem is a merge-time hazard, not a
fault. A recast may move a theorem to a new name and give the vacated
name to another theorem — the door now mints the principle a hand member
used to state, or a member is renamed for what it adds and the plainer
name goes to a plainer law. Inside one tree that is safe once every
citer names the theorem it means, which the replay of their scope
checks. A citer the change never saw — on a branch cut before it —
still names the old theorem, and two entries with one typed-wrapper
signature are interchangeable to the compiler, so it merges, builds,
vets and lints green against the new statement and is noticed only by a
replay that reaches it. `TestLintRepointedNames` lists each name whose
key changed at a commit while its old key is still registered under
another name (`XUGO_GATE_BASE` picks the base; HEAD by default); the
landing that carries one says so, and a branch merged after it is
searched for cites of that name. A restatement, whose old key is gone,
is not listed and is checked by the citers' replay as before.

### Family lifecycle

A family has no closing state. The boundary, file grouping and conventions
agreed in dialogue become the first dispatch's brief and then the code; a
landing is verified by its scope's replay and the lints; consolidation,
review and improvement happen whenever a reader sees better.

Within one family, writes to the shared CNF cache are serialized. Parallel
work belongs across independent families.

## Verification contract

Every registered entry must satisfy:

1. **Kernel verification and force replay.** Every section and the top theorem
   reduce to certificates within the declared trust boundary.
2. **Statement identity.** The built theorem is normalized-alpha-equal to the
   entry headline. An entry's `Key` is the key of its statement's normal
   form, and the normal form does not see how the statement was spelled:
   the names of its binders and their order within a quantifier block, the
   order and association of a conjunction, the orientation of an equation
   or an ⇔, η, and a function equation against its pointwise reading all
   reach one key. The type
   variables are different: a type letter is keyed by its name, and where
   two things share a type variable is part of what the statement says.
3. **Realization.** The build returns a theorem installed in the environment;
   no section silently skips `Qed`.
4. **Dependency integrity.** Declared dependencies resolve, the registry DAG
   is coherent, and no proof bypasses replay with `TestThm`.

The shared harness is canonical; do not add one-off per-proof test files.

Run the smallest scope that covers the edit while iterating, then run the full
gates required by the family checkpoint. The baseline commands are:

```sh
XUGO_REPLAY_ONE=<family>.<Name> go test ./library/integrity/gates/ -run '^TestReplayAll$' -count=1
go build ./library/... && go vet ./library/... && go run ./library/cmd/xugo_fmt -l library/proofs/
go test ./library/integrity/... -count=1 -skip '^TestReplayAll$' &&   # the whole battery: lints, identity, DAG,
  go test ./library/integrity/gates/ -count=1 -run '^TestReplayAll$'  # then the replay, once they pass
```

Use `XUGO_REPLAY_SCOPE` for a family or entry plus its direct
consumers. A proof-body-only change normally needs the changed entry's replay;
a statement, dependency, registry, vocabulary, induction, or framework change
has a wider blast radius and must be tested accordingly. A renamed CONSTANT
reaches outside the library: tests under `engine/` state goals in the
chapters' vocabulary as text, which no build compiles and the battery above
does not run, so a rename also greps the old name across `engine/`,
`prover/` and `library/serve/` and runs `go test ./engine/...`. A renamed
ENTRY — or one moved to another family — is recorded by its registered
name in every family blob whose members read it, so the rename is carried
into the blobs once the source carries it:
`go run ./library/cmd/rekey_cnf_blob -rename-entries <old>=<new>`
rewrites the member records of every blob and touches no certificate. A
DELETED entry leaves its name in the rows of the members that read it the
same way, and every reader of the graph — the recorder of any family, the
DAG gate, the index — panics on the stale name until
`go run ./library/cmd/rekey_cnf_blob -drop-entries <old>` takes it out;
each citer's replay then holds its row to what its proof reads.

Do not introduce dependency-count or reference-depth rules as correctness
checks. The library may legally choose a different basis. Replay and the
actual dependency graph decide acyclicity; readability review decides whether
a dependency is disproportionate.

### Why no dep-set / dep-depth lints

A source library's order and dependency depth reflect its history, not a
required basis for the corpus. A heavier theorem may legitimately support a
lighter one if the graph remains acyclic and the resulting chapter reads well.
Force replay checks the former; review checks the latter. Add a narrower lint
only after observing a concrete structural defect that replay and readability
review do not expose.

## The session

Use the session when understanding or changing proof shape. The session is the
exploration and validation medium; the committed Go file is the refined
mathematical document. A session's lineage persists (`session-lineage`,
`session-create {resume}`): a proof found in one session is read back and
continued in another, never re-derived.

Three uses:

1. **Reading.** `session-lineage` and `dump-section` on a resumed lineage show
   what was done and what each step proved.
2. **Shape validation.** Add the planned natural-form section goals and prove
   them bottom-up before writing substantial Go.
3. **Leaf labeling.** Inspect long or multi-refuter chains so every branch can
   be given a mathematical `Case` label.

### One kind of session

Every session has one semantics — there is no other kind:

1. previously proved authored sibling sections may be cited;
2. a cite names a registry entry — nothing else; force-replay of the
   landed file is the cycle gate;
3. `emit-section` transports a closed authored session section to the family
   form plus its CNF cache, after which the author refactors the result into
   the math-layer style;
4. the session uses the corpus automation policy and foundation gates.

A session BOUND to a family (`session-create {"family":…,"imports":[…]}`)
additionally starts with every registered definition of the bound families
installed as a use rule, derived from the entry's served shape by the same
function the session `define` installs from — the chapter's definitions
are in force before the first goal, and a `simp` fire emits as a typed
cite of the entry.

`emit-section` is a machine interface, not a chapter-code generator. Never
accept its output as finished merely because it compiles.

### Cards: a member stated without a proof

A chapter may state a theorem before anyone has proved it. Such a member
is a CARD: its Build is `family.Card(<statement>, <note>)` — the
statement in the family's vocabulary, exactly as `family.Theorem` reads
its headline, and a note saying why it is a member and what its proof
must establish. It registers, is cited, retrieved and typed like any
member, and is served as the axiom `⊢ <statement>`: by the corpus seam
to a session, by the replay harness to every member citing it. The
corpus is sound relative to its cards. `xugo query cards` lists them, leaves
first; `query member` reports a member's card frontier — every card it
stands on through its dependencies; a chapter's README marks each card in its
members table with ` — card` after the statement, so the narrative says
which of its theorems are stated and which are proved.

```go
var DividesAntisym = family.Add(registry.ProofEntry{
	Name: "DividesAntisym",
	Key:  "prop_…",
	Build: family.Card(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ∣ n",
			"n ∣ m",
		},
		Conclusion: "m = n",
	}, "antisymmetry of divisibility; each divides the other, so each is at most the other"),
})
```

A card states a closed theorem in the standard form — its binders in
front, its premises one antecedent, no turnstile — written as every
statement is (§"The section boundary is a binding form"): in parts where
it has a premise, one hypothesis per line, and as one string where it has
none; a law of a structure through the structure's door,
`S.Statement(body)`, its body written the same way. Its proof keeps the
statement as written when it lands. Its
`Deps` are the chapter's narrative of what its proof will
cite — they order the fill and are replayed by nothing. The fill drops
them with the `family.Card`: the proved member's dependencies are what its
proof is recorded reading. And the proof names only what it is recorded
reading: a member a step names — in its proof, or through a local bound
to a citation — that the replay recorded no read of is decoration, a
witness whose evidence no closer consumed or a lemma passed and never
used, and the lint `TestLintProofNamesRecordedDeps` refuses it; the
author drops the name or makes a step use it. The record may hold reads
the text never spells, a reading's laws or a simp set, and nothing asks
the text to spell them. A member — a card above all, since
nothing but a reader checks it — may carry a `Reading`
(`registry.ProofEntry.Reading`, `DefEntry.Reading`): the statement read in
this encoding, in two or three sentences — which hypothesis is
load-bearing and why, what the empty set or an empty family does to it,
which axiom enters where, which argument a short spelling leaves out —
never its proof, which the note sketches. It is served by the member's
dossier (`xugo query dossier`) and listed on the family's index page;
empty is the ordinary state, and a referee's finding about a card that
is true is what fills it. A card may be cited anywhere except
under a capability's foundation: the manifest refuses a card reachable
from an arithmetic bundle's roots, since that would put an axiom under
every arithmetic close.

Filling a card is local: a `/prove` session whose target is the card's
statement lands by replacing `family.Card(…)` with
`family.Theorem(<the same statement>, body)` — the name and key stay,
nothing downstream changes. The entry stays in its file unless that file
is the family's `cards.go`, which holds cards only: there the filled entry
moves to the proof file of its subject (§"Families"), a move inside the
package that no citer sees. A restated statement re-keys like any
restatement, and its citers replay one hop. A card found false is
restated or deleted, and whatever was proved on it is re-proved. So
leaves first is the cheap order to fill cards in (`query cards` gives it) —
not a schedule: any card may be filled at any time, its proof citing
the cards under it as the axioms they are — and a card is read cold
before it is minted.

In a session the move is `defer`: an open leaf's conclusion, ∀-closed
over its free variables, becomes a card of the session's family, the
leaf closes by citing it, and `emit-section` renders the card entry
beside the member — land both. The chapter's open work is its cards;
there is no unproved node, no sequent member standing on premises, and
no later restatement.

## Stable authoring rules (anti-instructions)

These rules apply to all new or modified proof files:

- Lead with the mathematical statement and argument; keep machinery in
  `family.go`, `vocab.go`, the generated files, or framework packages.
- Use natural headlines, typed dependencies, Go-natural names, and qualified
  cross-package references.
- Use `Fact`/`By`/`Derive`, named cases, calc kits, and fixed solver kits at
  their intended abstraction level.
- Prefer a direct fact value over re-parsing or re-spelling a theorem,
  hypothesis, type variable, or witness already held by the program.
- Write statement, claim, and term text as literals; never assemble it with
  `fmt.Sprintf` (a printed term re-parses through the display form, and a
  misspelled literal now fails loudly instead of silently freshening). A
  claim or term text is one literal or a `Statement` literal, a text
  whose line runs past 100 columns from its indentation written as the
  chain of literals
  joined by `+` that `xugo_fmt` lays it out as, one line each (a label,
  a note and a `Reading` are laid out so too, at their blanks): a term it
  shares with other texts of the member is an entry of the statement's
  `Abbrev` table, which every text of the proof spells as
  `«Name»` — applied to an argument where a Go builder took one — never
  a Go const or string the texts splice in; a term that spells a name
  the claim itself binds is written out; a term the chapter's statements
  share is an entry of the chapter's table (`WithAbbrev`), spelled the
  same way. The text gate (`TestLintClaimTextIsData`) refuses a
  statement or claim text assembled from Go strings that the base
  commit does not have. A dug binder that needs
  a readable claim-text name takes it at the verb (`Fix("u")` /
  `FixAs[φ]("u")`); a live name is never silently re-pointed.
- Keep comments durable and mathematical. Explain why a non-obvious step is
  needed, not what a tactic invocation visibly does and not how an earlier
  version was built.
- Do not encode proof structure solely in comments.
- Do not retain seed hashes, goal keys, another library's theorem names, CNF dumps, section
  numbers, construction tier / packet / wave labels, migration dates, failure
  counts, or temporary agent notes in reader-facing proof files. The build
  record is the curation log and git; the proof file is the finished
  mathematics.
- Do not add speculative helpers, vocabulary, solver members, or abstraction
  layers without a current consumer.
- Do not hand-roll a fixed pattern when an adopted kit expresses it more
  directly; do not create a generic kit merely to remove superficial
  repetition.
- Do not weaken replay, identity checks, lints, or the dependency declaration
  to make a proof land.

When a rule must be escaped, keep the escape local, explain the actual reason,
and add it to a narrow census or allowlist with an exit condition when the
class can recur.

## Growth mode: de novo proving

A statement reaches the library by the same pipeline whether its
author works from a reference or from nothing:

```text
statement + hints -> session proof -> emit-section -> chapter Go
```

A reference proof, where there is one, is the blueprint, and the
statement is restated in the chapter's vocabulary. Interactive
execution is the only source of the goal states, so the session is
mandatory. In both cases:

- statements are chosen in natural form;
- exploration happens in the session;
- `emit-section` supplies the machine-faithful transport;
- refinement happens in Go;
- force replay and statement review gate the result.

A statement a reference proves is a known-provable target; every
statement is read at review, which is the authority a landed statement
rests on.

## Out of scope

- Patching an emit defect inside a proof file instead of at the emitter.
- Autonomous changes to the emit pipeline or the engine from a chapter finding.
- Treating this document as the corpus status page or historical changelog.
