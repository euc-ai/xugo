# Package proof — the proof calculus

## Overview

Package `proof` (at `prover/proof/`) is the proof calculus of XuGo:
goal-directed proof construction, the Step/Macro/Action inference
layers, record and replay, and the mathematical writing surface a
chapter's proofs are authored in. See `prover/README.md` for the tent
layering around it, and the manual's part "Chapter Go — the authoring
surface" (`engine/xugo-engine.md`) for how a proof is written with it.

## File map

The package is one Go package by necessity, not by accident: every
Action carries an unexported `applyAction` and a proto tag, so the
record/replay world is closed and cannot be split across packages. The
files are grouped by role instead.

**Proof state** — what a proof IS while it is being built.
`prover.go` (the environment and its theorem cache), `goal_stack.go`
(the goal tree), `proof.go` (a script's sections and the wire form of
a closed one), `registry.go` (the lazy by-key namespace of buildable
theorems), `proof_scope.go` (dependency capabilities and the policy
query), `cnf_store.go` (the certificate and plan tables a recorded
close reads back), `utils.go` (the package's reading vocabulary).

**Inference calculus** — how a goal becomes subgoals.
`step.go` (atomic Steps), `macro.go` (the compound Macro layer and
`auto`), `action.go` (the umbrella Action interface both satisfy),
`try.go` (non-committing probes), `tactic_apply.go` (the apply surface
the engine drives).

**Recorded composite steps** — recurring mathematical actions, one
proto tag each: `step_composite.go` (DefExpand, SetTac, SimpWith,
PairedBeta, PairCollapse), `step_by.go` (the `By` family's close),
`step_condition.go` (the conditioning stage the closer doors share),
`apply_close.go` (the apply rung that runs before any closer),
`step_ac.go` (the AC regroup), `step_define.go` (the definition
moves).

**The definition moves** — analysis, mint and derivation for each
door, shared by the session's `define` and the chapter's
`family.Define…`: `define.go` (the shared driver and the recursive
shapes), `define_wf.go` (well-founded recursion), `define_spec.go`
(constants chosen against a specification), `define_type.go`,
`define_data.go`, `define_inductive.go`, `define_quotient.go`,
`define_lift.go` (a function on a quotient's classes),
`define_rules.go` (the use rules a definition installs, derived from
its shape).

**The mathematical writing surface** — the language proofs are
written in. `script.go` (the Script a proof file runs on),
`section.go` (how a statement's binders reach the proving closure),
`derive.go` (`Derive` and `Argument`, the body style), `fact.go` (the
`Fact` value, the `By` closers, the `Cite` verbs), `calc.go` (equation
and estimate chains), `branch.go`, `iff_direction.go` and
`disjunction_branches.go` (a split's branches claimed by name), `induction.go` (`ByInduction`),
`reading.go` (a law read at an instance), `hyp_handle.go` (named
hypothesis references), `witness_order.go` (a cite's witnesses in the
stated binder order), `typed.go`, `vec.go`, `bigop.go` and `member.go`
(the typed face: expressions, dimension-refined vectors, big
operators, a point with its membership).

**Persistence** — `proof.proto` and the generated `proof.pb.go`.

Test files mirror their source file (`fact_test.go`,
`step_composite_test.go`, …).

## A recorded composite step

A recurring mathematical action is recorded as itself, never as the
expansion it ran. A step recorded as an expansion has three code paths
that must agree — the live driver, the recorded sequence, and the Go
that emit renders from it — and every drift between them is a replay
divergence. A composite removes the paths: it is one proto tag whose
payload is the CALL (what the author said: the constant unfolded, the
rule set, the premise list and closer), and whose `apply` IS the live
driver. The session's dispatch and a chapter body run that one
function on the same input, and replay is the chapter body run again
— nothing decodes a recorded tree back into steps. A new composite
holds four things:

- **One executor.** The engine's tactic dispatch and the Script verb
  each construct the step and run it; neither reimplements a part of
  it.
- **Determinism inside.** Replay re-runs the executor cold. Anything
  it iterates in map order is sorted first, and no decision reads the
  wall clock.
- **Options set inside.** A context stamp or an option the driver
  needs is set in the executor, never at one caller's layer —
  otherwise the record and the replay normalize differently and
  compute different CNF keys.
- **Nothing of the session.** What exists only in a live session — the
  auto-match against the registry, the session's own state — stays
  outside the recorded step: a chapter's replay has none of it. A
  premise's obligation therefore surfaces as a CHILD of the composite,
  closed outside it (by the entry it names, in a session; by the cited
  certificate, in a chapter).

The payload carries identities, never per-goal instances: a
polymorphic rule is recorded as the rule, and its instance is
re-derived at replay (`_KnownThmStep.proto` panics on a payload that
is not the statement it certifies). Emit knows a payload-carrying step
in three places — `walkMiniStep`, which registers its variables and
constants, `markGoUsedFromMiniStep`, which keeps their declarations,
and the renderer `emitMiniStep` — and a new tag needs all three: a
variable the second walk never marks is pruned as unused, and the
rendered Go names something undeclared.

## Adding a closer to the `By` family

`By`, `ByArith` and `BySets` are one composite with a closer choice,
and the choice travels on the wire. A new closer is therefore more
than a function beside `ByArith`:

1. `proof.proto` — a `bool` on `ByProto`, and `proof.pb.go`
   regenerated by the command in the `.proto` file's header, with the
   protoc and protoc-gen-go versions the generated file names (another
   version rewrites the whole file).
2. `fact.go` — the constructor, the `_ByAction` field, and the two
   premise-count guards, which mean different things: the empty-list
   guard and the no-facts guard. A DRIVER closer, whose lowering is
   its content, is exempt from both, as `BySets` is; a
   refutation-style closer is exempt from neither.
3. `step_by.go` — the `_ByStep` field, `String()`, `proto()`,
   `closerName()`, the dispatch in `closeOne`, and `BySpec`, the
   session's entry (`ApplyByStep`). The closers are mutually
   exclusive: the guard there compares the two that exist, and a
   third makes it a count.
4. The manual — the closer's entry, and the underlying tactic's if it
   has none.

The executor builds a PRIVATE goal tree, and a capability-gated closer
is sound only because that tree's root takes the step's proof scope
(`root.SetProofScope(step.scope)`) and its children inherit it: the
lexical policy that reaches the closer is the circularity contract,
and a scope that silently arrived nil would be a hole every test still
passes. Check it for the new closer. The plumbing is testable without
the closer's lemma bundle: construct the `_ByStep` with the flag set
and assert `closerName()`, `String()` and the proto bit.

## Dependencies

Below this package, and imported by it: `core`, `ext` and its
subpackages, `prover/tactic` (subgoal computation), `prover/typematch`
(lemma type adaptation), and the solvers — `prover/solver/refuter`
(the CNF closer), `prover/solver/omega` (arithmetic),
`prover/solver/ac` (AC-rearrangement certificates),
`prover/solver/ematch` (instance planning).

The packages ABOVE this one (the kit `prover/algebra`, plus
everything under `library/` and `engine/`) import it as `proof`. A
package above proof cannot supply a primitive Action (`applyAction` is
unexported, and a primitive must inspect goal state at apply time); a
package below proof cannot mention proof's types at all. Which side a
piece of machinery falls on is decided by that, not by subject
matter — the tent README spells out the layering.
