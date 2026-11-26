# relations/order — orders: chains and bounds, Zorn's lemma, complete lattices on a carrier, well-orders

A relation is a **preorder** when it is reflexive and transitive, a
**partial order** when it is moreover antisymmetric, and a **total
order** when moreover any two points are comparable. Each is stated as
a structure whose one component is the relation, and the second and
third are each the one before with one axiom more: `partial_order(R)`
is `preorder(R) ∧ antisymmetric(R)`, so a law of a preorder is read at
a partial order through `PartialOrderPreorder`, and a law of a partial
order at a total one through `TotalOrderPartialOrder` (constitution
§Structures). The three are kept in one chapter because they are one
notion at three strengths: nothing here is stated of one that is not
read at the next through its projection.

`R(x, y)` is read "x is below y" throughout, and two points are
comparable when one is below the other.

The relation is a function on the host type; the carrier is a set.
`preorder_on(c, R)` asks for reflexivity and transitivity only among
points of `c`, and `partial_order_on(c, R)` adds antisymmetry there.
What the relation does outside `c` is unrestricted. The whole-type
preorder and partial order are the cases `c = 𝕌`: their reflexivity,
transitivity and antisymmetry are views of the carrier laws through
`PreorderAtUniverse` and `PartialOrderAtUniverse`.

Bounds of a family inside a carrier must themselves lie in the
carrier. `has_sup_on(c, R, s, b)` and `has_inf_on(c, R, s, b)` express
this, and compare `b` only with bounds in `c`. A complete lattice on
`c` supplies both for every `s ⊆ c`, including the empty set.

The maximal-principle argument is proved through Zorn's lemma.

## Orders on a carrier

| member | statement |
|---|---|
| `PreorderOn` | reflexivity and transitivity on `c` |
| `ReflexiveOn`, `TransitiveOn` | the two guarded axioms |
| `PreorderOnUniverse` | `preorder(R) ⇔ preorder_on(𝕌, R)` |
| `PartialOrderOn` | `preorder_on(c, R)` and antisymmetry among points of `c` |
| `PartialOrderOnUniverse` | `partial_order(R) ⇔ partial_order_on(𝕌, R)` |
| `PartialOrderOnPreorder`, `AntisymmetricOn` | the carrier preorder and its antisymmetry law |
| `HasSupOnDef`, `HasInfOnDef` | the supremum and infimum of `s ⊆ c`, compared with bounds in `c` |
| `CompleteLatticeOn` | a partial order on `c`, with a supremum and infimum for every subset of `c` |
| `CompleteLatticeOnPartialOrder`, `SupHasSupOn`, `InfHasInfOn` | the carrier order and the two bounds supplied by the lattice |
| `CompleteLatticeOnDual` | reversing the relation and exchanging supremum with infimum gives a complete lattice on the same carrier |
| `PowersetCompleteLattice` | `{s \| s ⊆ X}` is a complete lattice under inclusion, with supremum `⋃F` and infimum `X ∩ ⋂F` |

## The order relations

| member | statement |
|---|---|
| `AntisymmetricDef` | `antisymmetric(R) ⇔ ∀x y. R(x, y) ∧ R(y, x) ⇒ x = y` |
| `Preorder` | `preorder(R) ⇔ reflexive(R) ∧ transitive(R)` |
| `Reflexive` | `preorder(R) ⇒ R(x, x)` |
| `Transitive` | `preorder(R) ⇒ (R(x, y) ∧ R(y, z) ⇒ R(x, z))` |
| `PartialOrder` | `partial_order(R) ⇔ preorder(R) ∧ antisymmetric(R)` |
| `PartialOrderPreorder` | `partial_order(R) ⇒ preorder(R)` |
| `Antisymmetric` | `partial_order(R) ⇒ (R(x, y) ∧ R(y, x) ⇒ x = y)` |
| `TotalOrder` | `total_order(R) ⇔ partial_order(R) ∧ (∀x y. R(x, y) ∨ R(y, x))` |
| `TotalOrderPartialOrder` | `total_order(R) ⇒ partial_order(R)` |
| `Total` | `total_order(R) ⇒ R(x, y) ∨ R(y, x)` |

## Chains and maximal points

A **chain** is a set any two of whose points are comparable. The two
points may be one point, so a point of a chain is below itself; under a
preorder that asks nothing. An **upper bound** of a set is a point
every point of the set is below, in the set or not. A point of a set is
**maximal** in it when whatever point of the set it is below is below
it in turn — the reading that is right for a preorder, where two points
may each be below the other without being equal. Maximal is not
greatest: the other points of the set need not be below a maximal one,
only not strictly above it.

| member | statement |
|---|---|
| `MonotoneOnNatInterval` | adjacent steps `R(a(k), a(k + 1))` for `m ≤ k < n` in a preorder imply `R(a(m), a(n))` whenever `m ≤ n` |
| `ChainDef` | `chain(R, c) ⇔ ∀x y. x ∈ c ∧ y ∈ c ⇒ R(x, y) ∨ R(y, x)` |
| `UpperBoundDef` | `upper_bound(R, s, b) ⇔ ∀x. x ∈ s ⇒ R(x, b)` |
| `MaximalDef` | `maximal(R, s, m) ⇔ m ∈ s ∧ (∀x. x ∈ s ∧ R(m, x) ⇒ R(x, m))` |
| `ChainSubset` | `chain(R, c) ∧ d ⊆ c ⇒ chain(R, d)` |
| `ChainInsert` | `chain(R, insert(x, c)) ⇔ chain(R, c) ∧ R(x, x) ∧ (∀y. y ∈ c ⇒ R(x, y) ∨ R(y, x))` |
| `ChainUnions` | `(∀c. c ∈ F ⇒ chain(R, c)) ∧ (∀c d. c ∈ F ∧ d ∈ F ⇒ c ⊆ d ∨ d ⊆ c) ⇒ chain(R, ⋃F)` |
| `MaximalIff` | `partial_order(R) ⇒ (maximal(R, s, m) ⇔ m ∈ s ∧ (∀x. x ∈ s ∧ R(m, x) ⇒ x = m))` |

The chain laws hold of any relation. `ChainUnions` asks that the family
be a chain under inclusion and spells that out, as every statement of
the chapter about a family of sets does: `chain(λs t. s ⊆ t, F)` says
the same and reads worse. `MaximalIff` is the familiar reading of
maximality, which antisymmetry buys.

## Greatest and least points

A **lower bound** is the mirror of an upper one. A **greatest** point
of a set is an upper bound of it lying in it, a **least** point a lower
bound lying in it.

| member | statement |
|---|---|
| `LowerBoundDef` | `lower_bound(R, s, b) ⇔ ∀x. x ∈ s ⇒ R(b, x)` |
| `GreatestDef` | `greatest(R, s, m) ⇔ m ∈ s ∧ upper_bound(R, s, m)` |
| `LeastDef` | `least(R, s, m) ⇔ m ∈ s ∧ lower_bound(R, s, m)` |
| `MaximalGreatest` | `total_order(R) ⇒ (maximal(R, s, m) ⇒ greatest(R, s, m))` |
| `FiniteMaximal` | `preorder(R) ⇒ (finite(s) ∧ s ≠ ∅ ⇒ ∃m. maximal(R, s, m))` |

`FiniteMaximal` is Zorn's lemma where no choice is needed.

## Inclusion

| member | statement |
|---|---|
| `SubsetPreorder` | `preorder(λs t. s ⊆ t)` |
| `SubsetPartialOrder` | `partial_order(λs t. s ⊆ t)` |
| `SupersetPreorder` | `preorder(λs t. t ⊆ s)` |
| `IncreasingFromSteps` | `(∀k. m ≤ k ∧ k < n ⇒ s(k) ⊆ s(k + 1)) ∧ m ≤ n ⇒ s(m) ⊆ s(n)`: `MonotoneOnNatInterval` at `SubsetPreorder` |
| `DecreasingFromSteps` | `(∀k. m ≤ k ∧ k < n ⇒ s(k + 1) ⊆ s(k)) ∧ m ≤ n ⇒ s(n) ⊆ s(m)`: `MonotoneOnNatInterval` at `SupersetPreorder` |

Inclusion is the chapter's instance: the structures are not empty, and
`MaximalIff` and `Zorn` read at it. The maximal principle for a family
of sets below is not obtained that way round — it is proved first, and
`Zorn` from it. Inclusion is an order both ways round, and
`MonotoneOnNatInterval` read at the two gives the sequences of sets
nested one step at a time: each set of such a sequence lies in every
later one, or holds it.

An instance is a theorem of the chapter that defines its relation, and
inclusion is defined by the set chapters. Those lie below every chapter
of `relations`, which reads sets, so they cannot state that inclusion
is an order, and its instances are kept here. The order of the natural
numbers is in the same position. The rule stands for a relation defined
by a chapter above this one: its instance is that chapter's to state.

## The tower of an operation on sets

`set_tower(f)` is the least family of sets closed under an operation
`f` on sets and under the union of any of its subfamilies. Where `f`
only enlarges its argument, the tower is what `f` reaches from the
empty set when it is iterated through every limit, and it is how this
chapter iterates an operation without ordinals. It is defined by its
two rules and comes with the theorems a definition by rules comes
with; its closure form is not a proof surface, so no member unfolds it.

| member | statement |
|---|---|
| `setTowerRules` | `set_tower(f, s) ⇒ set_tower(f, f(s))`, and `(∀s. s ∈ F ⇒ set_tower(f, s)) ⇒ set_tower(f, ⋃F)` |
| `setTowerInduct` | `(∀s. P(s) ⇒ P(f(s))) ∧ (∀F. (∀s. s ∈ F ⇒ P(s)) ⇒ P(⋃F)) ⇒ (set_tower(f, s) ⇒ P(s))` |
| `setTowerInductStrong` | `(∀s. set_tower(f, s) ∧ P(s) ⇒ P(f(s))) ∧ (∀F. (∀s. s ∈ F ⇒ set_tower(f, s) ∧ P(s)) ⇒ P(⋃F)) ⇒ (set_tower(f, s) ⇒ P(s))` |
| `setTowerCases` | `set_tower(f, s) ⇔ (∃t. s = f(t) ∧ set_tower(f, t)) ∨ (∃F. s = ⋃F ∧ (∀t. t ∈ F ⇒ set_tower(f, t)))` |

Where `f` only enlarges its argument the tower is a chain under
inclusion, and that is read off one fact about its steps: `f(c)` is the
next set of the tower after `c`, nothing of the tower lying strictly
between the two.

| member | statement |
|---|---|
| `TowerSuccessor` | `(∀s. s ⊆ f(s)) ⇒ (set_tower(f, c) ∧ set_tower(f, d) ∧ c ⊆ d ⇒ d = c ∨ f(c) ⊆ d)` |
| `TowerChain` | `(∀s. s ⊆ f(s)) ⇒ (set_tower(f, c) ∧ set_tower(f, d) ⇒ c ⊆ d ∨ d ⊆ c)` |
| `TowerLeast` | `(∀s. s ⊆ f(s)) ⇒ (G ≠ ∅ ∧ (∀s. s ∈ G ⇒ set_tower(f, s)) ⇒ ∃m. m ∈ G ∧ (∀s. s ∈ G ⇒ m ⊆ s))` |

`TowerSuccessor` and `TowerChain` rest on one comparison, kept as an
unexported member: at a set `d` such that `f` keeps inside `d` every
set of the tower lying strictly inside it, each set of the tower lies
in `d` or contains `f(d)`. That hypothesis on `d` is the conclusion of
`TowerSuccessor` read at `d`: `TowerSuccessor` is the rule induction
that carries it along the tower, and `TowerChain` is the comparison
with it discharged. `TowerLeast` says the chain is a well-ordered one:
a family of sets of the tower that is not empty has a least member.

## The fixed point

| member | statement |
|---|---|
| `BourbakiWitt` | `(∀s. s ⊆ f(s)) ∧ (∀s. P(s) ⇒ P(f(s))) ∧ (∀F. (∀s. s ∈ F ⇒ P(s)) ∧ (∀s t. s ∈ F ∧ t ∈ F ⇒ s ⊆ t ∨ t ⊆ s) ⇒ P(⋃F)) ⇒ ∃s. P(s) ∧ f(s) = s` |

An operation on sets that only enlarges its argument has a fixed point
inside any property of sets that it preserves and that passes to the
union of a chain of sets having it. The fixed point is the union of the
whole tower: it is a set of the tower by the second rule, so its image
is one by the first and lies inside it, and `f`, which only enlarges,
fixes it. The property reaches it by rule induction along the tower,
whose union case is where `TowerChain` is spent — a family of sets of
the tower is a chain. The empty family is a chain, so the third
hypothesis includes `P(∅)`, and a property to be carried must hold of
the empty set.

## The maximal principles

| member | statement |
|---|---|
| `ZornFamily` | `F ≠ ∅ ∧ (∀c. c ⊆ F ∧ c ≠ ∅ ∧ (∀s t. s ∈ c ∧ t ∈ c ⇒ s ⊆ t ∨ t ⊆ s) ⇒ ⋃c ∈ F) ⇒ ∃m. m ∈ F ∧ (∀s. s ∈ F ∧ m ⊆ s ⇒ s = m)` |
| `HausdorffMaximality` | `chain(R, c) ⇒ ∃m. c ⊆ m ∧ chain(R, m) ∧ (∀d. chain(R, d) ∧ m ⊆ d ⇒ d = m)` |
| `Zorn` | `preorder(R) ⇒ ((∀c. c ⊆ s ∧ chain(R, c) ⇒ ∃b. b ∈ s ∧ upper_bound(R, c, b)) ⇒ ∃m. maximal(R, s, m))` |

`ZornFamily` is Zorn's lemma for a family of sets: a non-empty family
that contains the union of each of its non-empty chains has a member
that no other member contains. It is `BourbakiWitt` at a function that
moves each set to a member of the family containing it and other than
it, where there is one, and leaves it in place otherwise, carried with
the property of being empty or a member of the family; the set the
function fixes has nothing of the family above it, and it is a member
because the family has one. "Empty or a member" is the property with the
empty set let in, as the fixed-point theorem asks. The function is
chosen point by point, and that is the one place a choice is made in
this maximal-principle argument: the two principles below make none of
their own.

`HausdorffMaximality` is Hausdorff's maximal principle in its extension
form: every chain of a relation lies in a chain that no other chain
contains. It is `ZornFamily` at the family of the chains that contain
the given one, which is not empty and contains the union of each of its
non-empty chains by `ChainUnions`; nothing is asked of the relation.

`Zorn` is Zorn's lemma, stated for a preorder: a set in which every
chain has an upper bound in the set has a maximal point. It is
`HausdorffMaximality` at the relation cut down to the set — two points
of `s`, the first below the second — grown from the empty chain. A
maximal chain `m` of that relation lies in `s` and is a chain of `R`,
because a chain compares each of its points with itself; an upper bound
`b` of `m` in `s` is then maximal, since a point of `s` that `b` is
below could be added to `m` (`ChainInsert`) and so is a point of `m`
already. Reflexivity and transitivity are each spent once and
antisymmetry not at all, which is why the law is the preorder's and
`maximal` is read as it is; under a partial order `MaximalIff` turns the
conclusion into the familiar one. The set is not asked to be non-empty:
the empty set is a chain, and its bound is a point of the set.

They are proved in that order because the choice is made once, for a
family of sets, and the chains of a relation and then the points of a
preorder are read at it.

## Well-orders

A **well-order** is a total order under which every set that is not
empty has a least point.

| member | statement |
|---|---|
| `WellOrder` | `well_order(R) ⇔ total_order(R) ∧ (∀s. s ≠ ∅ ⇒ ∃m. least(R, s, m))` |
| `WellOrderTotalOrder` | `well_order(R) ⇒ total_order(R)` |
| `WellOrderLeast` | `well_order(R) ⇒ (s ≠ ∅ ⇒ ∃m. least(R, s, m))` |
| `WellOrderingTheorem` | `∃R. well_order(R)` |

The `WellOrderingTheorem` says every type has a well-order; its route is
Zermelo's, along the tower of an operation that adds one chosen point
at a time, with `TowerLeast` supplying the least points.

## Closure operators on a carrier

A closure operator on a partially ordered set `c` maps `c` into itself,
is extensive and monotone there, and is idempotent. The relation and
operation are explicit components; their values outside `c` are
unrestricted. In a powerset instance the points of this order are sets,
so its carrier is `{s | s ⊆ X}`.

`ClosureFromLeast` supplies a shared construction: if `F ⊆ c` and
`cl(x)` is the least point of `F` above every `x ∈ c`, then `cl` is a
closure operator. Its proof establishes monotonicity by transitivity
and idempotence by leastness and antisymmetry.

| member | statement |
|---|---|
| `ClosureOperatorOn` | a carrier partial order with a closed, extensive, monotone, idempotent operation |
| `ClosureOperatorOnPartialOrder` | the underlying partial order on the carrier |
| `ClosureOnIn`, `ClosureExtensive`, `ClosureMonotone`, `ClosureIdempotent` | the four guarded closure laws |
| `ClosureFromLeast` | least points of a family above each carrier point define a closure operator |
| `ClosureFixedPointsCompleteLattice` | the fixed points of a closure operator on a complete lattice form a complete lattice, with supremum `cl(sup(F))` and infimum `inf(F)` |

## What is not here

**Maximal principles on a carrier.** The preorder and partial order
have carrier forms, as does the complete lattice. `Zorn` still asks
`preorder(R)` of the whole type although its proof looks at `R` only
inside `s`; the maximal principles and well-orders are stated for the
whole type only.

**Minimal points and the dual order.** The chapter states maximal
points and not minimal ones. Reversing the relation is a law only for a
complete lattice on a carrier (`CompleteLatticeOnDual`); for the whole
type there is none.

**Fixed points in an order.** `BourbakiWitt` is the theorem for sets
under inclusion; its form for an order in which every chain has a
supremum is not stated. Knaster and Tarski's theorem is
`sets/set_order`'s `KnasterTarski`, for sets under inclusion; it is not
stated for a complete lattice.

**Order isomorphisms, and the comparison of well-orders.** No map
between two orders is spoken of, so neither the isomorphism of
well-orders with their segments nor the ordinals are here.

**The orders of the numbers.** No instance is stated for ℕ, ℤ or ℝ.
ℤ's and ℝ's chapters lie above this one and could state theirs; ℕ's
cannot, as said of inclusion.

**The axiom of choice.** Choice is not a hypothesis anywhere in the
corpus: the logic has a choice operator, and a function assembled from
per-point choices is proved to exist. So the maximal principles are
theorems outright, and their equivalence with choice has nothing to be
stated against.

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
