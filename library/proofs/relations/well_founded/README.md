# relations/well_founded — well-founded relations

A relation is **well-founded** when every non-empty predicate has a
minimal element — one with no other element of the predicate below
it. That minimal-element reading is the definition; the chapter is
the small circle of equivalent readings, supplies and schemas that make
it usable.

The chapter sits in `relations`, the domain of the chapters whose
objects are relations themselves rather than the numbers, sets or
vectors a relation happens to compare. It reads `transitive_closure`
from `relations/closure` for the one theorem that says what taking a
closure does to well-foundedness.

The chapter defines both of the constants it speaks: `WellfoundedDef` is that
minimal-element reading, and `MeasureLessDef` says `measure_less(m, x, y) ⇔
m(x) < m(y)` — the relation a ℕ-valued measure induces.

## Reading well-foundedness

- **Induction** — well-foundedness IS the licence to do induction
  along the relation: `wellfounded(R)` holds exactly when a property that holds
  at a point whenever it holds everywhere below holds everywhere. The
  other members build on this characterization (Measure through
  InverseImage and NatLess rather than directly).
- **InverseImage** — well-foundedness pulls back along any map: if `R`
  is well-founded on the target, `λx y. R(m(x), m(y))` is well-founded
  on the source. This is how a well-founded relation on one type
  becomes one on any type a measure can leave.
- **NatLess** — the canonical supply: `<` on ℕ is well-founded, read
  off `nat_order`'s course-of-values induction through the Induction
  characterization.
- **Measure** — the composition of the last two at the ℕ instance:
  `measure_less(m)` — the relation `m(x) < m(y)` — is well-founded for
  every ℕ-valued `m`. Termination arguments cite this one.
- **Accessibility** — the chapter's two readings of well-foundedness
  are one notion: a relation is well-founded exactly when every one of
  its points is *accessible*, the inductively defined predicate that
  holds at a point once it holds at every point below. Each direction
  spends the induction licence against one of accessibility's own
  theorems — forwards, the licence carries accessibility itself, whose
  induction step IS the introduction rule; backwards, rule induction
  along accessibility turns "every point is accessible" into the
  licence. `accessible` is defined here, by its one rule, and comes
  with the four theorems a definition by rules comes with. Its closure
  form is not a proof surface — `Unfold` refuses it — so the members
  below cite those theorems and never the definition.
- **Subrelation** — well-foundedness is inherited downwards: a
  relation contained in a well-founded one is itself well-founded. The
  chapter's transport along a *containment*, beside `InverseImage`'s
  along a map, and proved the same way — read both sides through
  `Induction`, and a property closed under the smaller relation's
  predecessors is closed under the larger's, so the larger's licence
  to induct is the smaller's.
- **TransitiveClosureWellFounded** — taking the transitive closure
  neither creates nor destroys well-foundedness. Downwards it is
  containment: `R` sits inside its own closure, so `Subrelation`
  carries well-foundedness back. Upwards it is accessibility carried
  along the closure — every point reaching `x` in the closure either
  steps to it directly, which the induction hypothesis speaks of, or
  passes through a point the hypothesis reaches, from which
  accessibility passes back down.
- **EmptyRelation** — the empty relation is well-founded, vacuously:
  nothing is below anything, so any point of an inhabited predicate is
  already minimal in it. The degenerate end of the supply.

Two further relations arrive with a certificate rather than a reading,
and both get it by counting.

- **FinitePredecessors** — the criterion. A transitive, irreflexive
  relation under which every point has only finitely many points below
  it is well-founded. Counting is what leaves no room for an infinite
  descent: transitivity puts everything below a point below whatever
  that point is itself below, so passing down the relation can only
  shrink the set of points below; irreflexivity makes the shrinking
  strict; and a proper subset of a finite set is counted strictly
  smaller. So the number of points below is a ℕ-valued measure that
  drops along the relation, and the pull-back above finishes it. The
  criterion is stated in this chapter rather than in the counting one
  because finiteness declines to speak of well-foundedness.
- **ProperSubsetBelow** — that criterion spent. A subset of a finite
  set cannot be shrunk forever: proper inclusion, confined below a
  finite set, is well-founded. Proper inclusion is irreflexive and
  transitive of its own accord, and the confinement is what makes the
  predecessors finite — a set below `t` lies inside `t`, which the
  guard puts inside the finite `s`, so the sets below `t` are among
  `s`'s subsets, and those form a finite collection.

## Recursion along a well-founded relation

The reason the chapter exists. A recursive description whose value at
`x` depends only on values strictly below `x` pins down a function —
and "pins down" is two theorems, one for each half.

- **Recursion** — such a description is SATISFIED: there is a function
  obeying the recursion equation everywhere. Proved directly, by
  building the recursion's graph impredicatively as the least relation
  closed under "if `f` is already forced below `x`, then `x` is forced
  to `H(f, x)`". This is the existence schema an equation compiler
  instantiates to define functions by well-founded recursion.
- **RecursionUnique** — and it is satisfied by only ONE function. A
  single induction along the relation: agreement below a point plus
  admissibility forces agreement at it, and pointwise agreement is
  function equality.
- **RecursionInvariant** — the same existence, with admissibility
  WEAKENED by an invariant. The description need only be admissible
  across functions that satisfy `S` below `x`, and the price is that it
  must also carry `S` up to `H(f, x)`. Note what this does NOT do: the
  conclusion is `∃f. ∀x. f(x) = H(f, x)`, character for character
  `Recursion`'s, so `S` never leaves the premise and the member exports
  no property of the function it returns. It buys a definition whose
  admissibility is only true on the good functions, and nothing else —
  a consumer wanting a property of the defined function proves it
  afterwards, or wants `RecursionExists` below.

  It is derived from `Recursion` rather than built again: GUARD the
  description, replacing `H(f, x)` by an arbitrary value wherever `S`
  fails below `x`. The guard reads its argument only below `x`, so the
  guarded description is admissible in the plain sense even when `H` is
  not, and the fixed point `Recursion` returns for it is a fixed point
  of `H` once the invariant is known to hold everywhere.
- **RecursionExists** — the schema for a RELATIONAL description. Where
  the members above take a body `H` computing the value at `x`, this
  takes a predicate `Q` saying which values are acceptable there, and
  returns a function acceptable everywhere. It is what a definition
  wants when the recursion does not pin its value down and a choice has
  to be made at each point. Also a reduction: the chooser
  `λf. λx. εy. Q(f, x, y)` is a description in the ordinary sense —
  admissible because agreement below `x` makes the two acceptability
  predicates the same predicate, and ε is a function of the predicate —
  so `Recursion` supplies the fixed point and one induction along `R`
  turns "an acceptable value exists" into "the chosen one is
  acceptable".
- **NatRecursion** — the schema at ℕ's `<`, where the well-foundedness
  premise discharges once and for all against `NatLess`. Course-of-
  values recursion, and the form a consumer defining a function by
  strong recursion on a natural actually wants: no relation to name and
  no well-foundedness to supply.

Note the direction, since the source theory runs it the other way: there,
the invariant schema is proved first and the plain one read off it. Here
the graph construction is what needs writing out, and the general form
follows from it by guarding — a reduction rather than a second
construction.

## What is not here

Three things a reader may come looking for, and the reason each is
absent differs.

**The machinery of pattern matching.** A function written as
overlapping equations — one clause per constructor, earlier clauses
shadowing later ones — becomes a single well-founded recursion only
after the clauses are split into disjoint cases and the split is shown
exhaustive. A theory that does that inside its own logic must carry a
vocabulary for it: a predicate saying that a list of clauses forms an
admissible tail recursion, another naming the case analysis they
generate, and the theory of lists underneath both. XuGo does the
splitting in Go instead — the define door reads the equation list,
works out the cases, and instantiates the schemas above. So none of
that vocabulary is defined anywhere in this corpus and the chapter
states nothing about it. The two schemas the door reaches for are
`Recursion` and `Measure`.

**Descending chains.** The classical reading of well-foundedness is
that no sequence descends forever, and it is genuinely a second
reading rather than a restatement: getting from "some predicate has no
minimal element" to an actual infinite descent means choosing a
smaller point at every step, so the equivalence rests on a choice
principle that nothing else in the chapter needs. The same holds of
its transitive refinement and of the minimal-bad-sequence argument
built on it.

**The rest of the order theory.** Well-foundedness is inherited by any
RESTRICTION as well as by a sub-relation; it forbids a point below
itself and forbids two points below each other; and two well-founded
relations combine, on a product, both lexicographically and pointwise.
Of those the chapter states only the sub-relation case
(`Subrelation`) — for the others nothing it carries asks. Nor does it
state the converses of the recursion
theorems, that a relation admitting recursion, or admitting at most
one solution, is well-founded. Each is a genuine addition rather than a
corollary of anything above.

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
