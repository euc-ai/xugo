# prover/ — the big tent of fixed proving machinery

prover/ is a directory, not a package. It collects the FIXED machinery
of the proving system — everything that does not grow as theorems
accumulate. The complementary criterion places the growing side:
the theorem corpus and its production line live under `library/`.

Fixed does not mean self-contained. Machinery routinely NEEDS proved
theorems (induction needs the induction theorem; omega needs a pile of
proved arithmetic), and the tent gets them by INVERSION rather than
import: a package declares a slot, and the corpus fills it at startup
(`serve.InstallNatBundle`, `serve.InstallIntBundle`,
`serve.InstallRealBundle`, `serve.InstallStructureRingBundle`, in
`library/serve`). So the tent invariant is `prover/` never imports
`library/` — not "the tent needs no theorems". A package qualifies by
the fixed/growing test (growth is an engineering event, never a side
effect of proving more theorems) plus that invariant.

Within the tent the layers, innermost first:

1. **`solver/`** — theory solvers in the SMT sense: certificate
   manufacturers BELOW the proof calculus. Given a theory's facts they
   derive a kernel-checked certificate; they never touch the goal
   stack. Members: `refuter` (propositional and equational logic, by
   CNF saturation), `omega` (ℕ/ℤ/ℝ linear arithmetic and ring
   normalization), `ac` (associative-commutative rearrangement),
   `ematch` (E-matching: it PLANS the ground instances of a goal's
   ∀-hypotheses and applies none of them).

2. **`proof/`** — the proof calculus itself (package `proof`, the tent's
   center): goal state, the Step/Macro/Action inference layers, the
   record/replay machinery, and the mathematical writing surface
   (Fact/Cite/Derive/Calc/Script). One package by necessity: the
   Action world is closed (unexported `applyAction` + proto tags), the
   soundness basis of record/replay. Also below it: `tactic/`
   (subgoal computation), `typematch/` (lemma type adaptation),
   `reify/` (a proposition about a field record read as a first-order
   formula, for the elementarity step) and `bridge/` (the kernel proof
   that the reified formula's evaluation is the proposition, built
   from the reifier's plan by lemma instances and modus ponens).
   The canonical capability-policy TABLE is not here: it is one entry
   per proved target, so it is corpus content (`library/integrity/policy`)
   installed into proof at startup (`serve.InstallProofPolicy`), and
   only the query stays in the tent.

3. **Above `proof/`** — machinery whose output is expressed in the
   calculus's own vocabulary. A KIT produces proof SCRIPT: `algebra/`
   (group and monoid ladders). Every mathematical fact arrives as an
   explicit certificate parameter, so a kit adds nothing to any
   proof's dependency base. A kit carries a migration lien: a member
   that produces a statement is a theorem in disguise, destined for a
   chapter.

The tree encodes the dependency order: everything under `solver/` is
importable by `proof/`; a kit imports `proof/`; nothing in the tent
imports `library/`.

## When a motif earns a place here

A new member of the tent is read by every future author: it enters
the manual, and emit, record and replay each have to know it, under a
contract that its recorded form stays stable. A helper in a chapter
costs only the chapter's author. That asymmetry is the prior, and the
places a recurring motif can live are a ladder, each rung taken only
when the one below cannot hold it:

1. a helper inside the proof;
2. a helper of the family (its own file beside the proofs);
3. a helper exported by the chapter that owns the notion, for its
   consumers;
4. sugar in `prover/proof` that desugars to existing ministeps;
5. a primitive with a proto tag of its own.

How often a motif occurs decides whether it is extracted at all,
never which rung it goes to. One question tells the two kinds of
helper apart: would it still exist if the engine were perfect? If it
would, it is vocabulary, and is written. If it would not, it is a
workaround: it is written all the same, and the wish it stands for is
filed. A motif reaches `prover/` on one of four
grounds:

- the public surface cannot write it — it needs the engine's own
  state (a hypothesis handle tracked across steps, a synthesized λ,
  the engine's redex scanner);
- its value is a guarantee only this layer can give, not an
  abbreviation — a desugaring identical in the recorded tree, a
  stable key, a recorded step the session and replay share;
- it encodes a canonical form of the engine that hand-written code
  would drift from (a numeral's bit tower);
- it is the canonical spelling of a leaf action ubiquitous ACROSS
  families (`ByArith`, `ctx.DepNormalized`) — across families, not
  frequent in one.

Two questions come before the ladder. Which side should wrap: when a
wish for a primitive meets the import order — a primitive here that
would have to know a chapter's constants — the convenience belongs to
the chapter, which can name them (`pairs.Collapse(ctx)` over
`PairCollapse`); asking the lower layer to know the upper is the
wrong question. And what do the siblings write: a motif found in one
family is surveyed across the corpus before the primitive is built,
since another family routinely spells the same move in another
argument order, and a primitive must never key on a cite's witness
position.
