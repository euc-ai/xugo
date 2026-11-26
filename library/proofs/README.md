# proofs — reading the chapters

This file is the corpus-wide reader orientation for the family
chapter packages under `library/proofs/` — the conventions every chapter's proofs
follow, stated once. Each family's `README.md` carries the chapter's
mathematical narrative and any mechanics specific to that chapter, and
points here for the rest. The quality bar itself is set by
`library/chapter_constitution.md` (the constitution); this file
describes it for a reader, it does not define it.

## Statements

A member's statement lives in exactly one place: the checked headline
text the entry's `Build` carries (`family.Theorem("∀m n:num. m + n = n +
m", …)`, or `family.Sections` where the argument needs its own lemma
sections). Statement texts are written in the
canonical statement style — grouped binders, minimal parentheses,
Unicode subscripts for Skolem-suffixed names — so the checked text IS
the readable form; doc comments do not restate it.

## The four closing forms

A proof carries exactly as much visible structure as its argument
needs. Four closing forms recur, ordered by how much of the argument
they write down:

- **Bare premises.** `By(A, B, C)` — the step's honest justification
  is one sentence naming no intermediate: "immediate from A, B and
  C". Legal exactly at that triviality; an argument with steps names
  its steps. (A step justified by a SINGLE fact is `Cite(f)`, not a
  one-premise `By`.)
- **Ground premises.** Each link of the argument appears as a premise
  instantiated at the leaf's own terms (`At(dep, w…)`), so the
  intermediate terms are written on the page rather than searched
  for; recurring terms are named Go variables (the midpoint / estTerms
  idiom). **This is the default for composition-tier members**: when a
  justification names an instance or a waypoint, the witness spelling
  it appears in the body.
- **Named intermediate facts.** A `Derive` block states each fact in
  turn — `d.Have` per fact, `d.Show` to close — so a multi-step
  argument reads as its own list of steps, each proved with only what
  it needs. Facts are values: a `Have`'s result flows by name into the
  premise lists of the steps that use it.
- **Calculation chains.** An equation or relation chain a = t₁ = … = b
  spells as a `Calc` block with one justification per leg — the shape
  the chain already has on paper.

Which form a member uses is a property of its argument, not a house
style, and the first is not a default from which the others are
departures. The corresponding promise to the reader: **no step of the
mathematics lives only in a comment** — what the comments explain,
the proof text already shows.

## Cites: the resident-hypothesis default

By default a cited ∀-fact installs as a resident hypothesis and the
closing refutation finds the needed groundings itself — proof files
never narrate this. Comments mark only departures from the default:

- a cite that fires as a REWRITE of a matching goal atom and is
  consumed — marked with a `↦` comment stating the goal it lands on
  (a chain of such rewrites, each landing on the next link, is a
  legitimate closing form; the second cite of a refl-shaped residue
  closes at the cite);
- a leaf that closes at the cite itself with no refutation left to
  run;
- cite order that matters (a resident iff rewrites later incoming
  cites, so swapping two cites changes what the refuter sees).

One install-form mechanic recurs wherever a multi-clause conjunction
row is cited: the normalized cert (`NormalizedThm` — what a named
`Fact` target resolves to) re-binds the clauses under one shared
∀-prefix — fine for refute-closed leaves, but un-splittable for
eqSimplify. A leaf that needs the individual clauses as standalone
rewrite facts takes the raw `ctx.Dep` cert, whose separate binders
split. Files note which form they use when it matters.

## Structures

A structure is a predicate over its explicit components on a free
carrier (`comm_monoid(op, e)`), or over a record value holding them
(`comm_ring(R)`, `R : ring_ops(A)`), defined by `family.DefineStructure`; a law of it is stated by
`S.Law(body, proof)` and reads `∀<components>. S(<components>) ⇒ body`;
its axioms are its first laws (`S.Axiom`). An instance is a theorem of
a chapter of the carrier, the lowest one already reading the structure,
written `family.Instance(S, "comm_monoid(real_add,
&0)", cases…)` — the predicate unfolded, one case per conjunct — and a
consumer cites a law at an instance by name, `By(Normalized,
comm_monoid.Monoidal, AddMonoid)`: the operation is read off the goal,
the identity off the instance, and `Normalized` says the leaf closes
under normalization alone, recording no key. A law is also a `Simp`
rule at its hypothesis or instance — `Simp(Flipped(LeftInverse))`
collapses `add(neg(x), x)` to `zero`, `zero` read off the resident
`abelian_group(G)` — so a chain of law applications
rewrites instead of refuting; the normalizer keeps a bare variable on
an equation's left (`zero = add(neg(x), x)`), so a law served by name
collapses `Flipped` and expands `Fwd`. A super-structure's
definition is the conjunction of its sub-structures' predicates plus its
own axioms, so inheritance is a projection law (`comm_ring.AddGroup`)
and a carrier builds its instances bottom-up. A structure defined by a
plain equation rather than through `DefineStructure` — the fold
mechanism's `monoidal_op(op)` — is named by
`family.StructureOf("monoidal_op", "op:(B → B → B)")`, the components
spelled by the author since `StructureOf` reads no equation, and its
laws go through the same `S.Law`; a proof that builds at a component
names the components first, typed, before the hypothesis. The constitution's §"Structures" states the four rules; the
live chapters are under `algebra/`, and `iterate/monoidal` states its
thirty laws through the door.

## Assumptions and cards

A member's statement carries its hypotheses; its card frontier carries
the cards it stands on; beyond those the corpus assumes the kernel's
rules and its one postulate, the axiom of infinity
(`peano.Infinity`), nothing else — `xugo query axioms` lists the
postulate and the cards together. The two are read
differently.

A structure's assumptions are part of each law's statement:
`∀comps. S(comps) ⇒ body`. `S.Law` assembles that antecedent from the
definition, once per law; there is no persistent structure context,
and consumers name the instances they use. `S.Axiom(body)` unfolds the
defining predicate and proves one of its conjuncts under this
antecedent; `Conjunct` does the same for a defined predicate that is
not a structure. Both produce ordinary checked theorems; neither calls
`NewAxiom`. The consequences of a closed conjecture `C` are stated as
`C ⇒ T` through ordinary `family.Theorem`: `StructureOf` requires at
least one component and is for a predicate over those components, and
a closed conjecture needs no structure wrapper.

These conditions are visible to the kernel. Inside a law's proof the
assumption is a hypothesis of the section's sequent, `S(comps) ⊢ body`,
the Fact the closure receives; the section's binder closure discharges
it, so the member's certificate has no hypotheses and states
`∀comps. S(comps) ⇒ body`. Only modus ponens at an instance removes the
condition, and that is a cite of the instance by name.

A card (the constitution's §"Cards: a member stated without a proof")
is an axiom, not a hypothesis: its statement `C` is served through
`NewAxiom` as `⊢ C`, so a proof using it yields `⊢ T` with no `C` in
the statement, and a `ThmCert` by itself carries no record of which
cards were used. The registry tracks the cards through the dependency
graph — `query member` reports them as `cards`, the corpus index as
the member's frontier and stratum — and the walk is the whole of what
a member stands on because of two facts: a Build is served the
certificates of its dependencies and nothing else — a proved member's
are the entries its proof was recorded reading — so a proof that read
an entry off its record would not replay; and no definition door
stands on a card (the gate `TestNoCardUnderADefinitionalDoor`), since
a constant is reached by name and a type by its terms, not through a
dependency. Below the first card the frontier is a forecast: a card's
own `Deps` are what its proof is expected to cite, so a member standing on
`C₁` also lists the cards `C₁`'s plan names, though until `C₁` is
proved it stands on `C₁` alone. Reading a result therefore means
reading both the conditions in its statement and its card frontier.
What can mint a certificate at all is audited in `core/README.md`,
§"Soundness: construction confined to core".

## Definitions

A chapter defines its own constants and types, through the define
doors (`family.Define` for an equation-shaped constant,
`family.DefineType` for a type carved out of a representation type by a
predicate, `family.DefineData` for a datatype, `family.DefineSpec` for a
specification, `family.DefineInductive` for a relation given by
introduction rules), and the definition entry reads like any member: its
statement is the characterizing equation, its Build is the one
definition step. Every constant is defined here, by
the chapter whose definitional layer it belongs to — `wellfounded` in
relations/well_founded, `mk_pair` and `prod` in pairs. A type's
inhabitation is proved at the mint when the normalizer decides it;
otherwise the chapter proves `∃x. P(x)` as an entry and the type is
minted on that entry's promise, its two axioms derived from the
entry's certificate at replay. A constant no chapter defines does not
exist for the corpus: the registry (`registry.ConstMetaManager`) holds
engine built-ins and chapter mints only, so a statement that spells an
undefined name fails to parse at registration — the chapter that owns
the constant defines it first, and a chapter that spells another
chapter's constant imports that chapter. Every chapter mint goes
through a door — the gate `TestEveryMintIsADoor` fails a constant a
chapter handed the kernel itself — so the index's definitions page is
the whole definitional layer.

## Skolems

`StripQuant` Skolemizes a binder by appending `_0` (printed `x₀`);
`InductStep` on `Var("x", …)` reuses the binder's name for the
step-case Skolem. A proof takes the minted frees as its closure's
parameters — the section boundary binds the statement's binders under
the statement's own names — and a claim text spells the statement's
`x` for the minted `x₀`. Programmatic bridge and witness terms rebind their
Consts (`+`, `*`, `suc`) into the Script's parse scope via
`ctx.Const` before `Apply`-spelling the term.

## Naming

Names follow the constitution's §"Inventory and names". A name is
reserved for a chapter's public API — the facts later chapters cite — in
Go-natural CamelCase; every other statement is demoted to an internal
lemma (unexported entry var, lowerCamel), fully verified and
typed-citable within the family. Every entry's `Key` is its own statement's
normalized key (`TestEntryKeyIsOwnKey` and the replay harness check
it).

A proof body's Argument receiver is `a`; where the statement itself
binds a variable named `a`, the receiver is `arg` instead, so the
statement's letter can be the Go variable that holds it.

## Framework, in one line

Members register as typed entry vars in a family sub-package
(compiler-checked dep DAG, one shared `<family>.cnf.pb`, force-replay
as `TestReplayAll/<family>/…` underneath) — mechanics in the
constitution §Families and `library/registry/registry.go`.

## The index

The corpus read as one object is `library/index`, beside the chapters.
`xugo query` answers its views in JSON: the totals and the families by
height, a family with every member's statement, who a member cites and
where it is registered, the definitions, the cards. `xugo browse` serves
the same corpus to read in a browser: the family graph (transitively
reduced, so it draws), each member's page with its statement and the
results it stands on, and a search of the theorems. Neither writes a
file. A chapter's narrative stays in its README — the index points at it
and does not restate it.

The landmarks — by subject, the results a reader arriving from a
textbook looks for — are a page written and kept by hand,
`site/landmarks.html`, published with the corpus browser on the
project's site (`site/README.md`). No view of the index reads it.
