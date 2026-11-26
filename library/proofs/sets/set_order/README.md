# set_order — inclusion

`set_basic` says what it takes to be IN a set. This chapter is about
what it takes for one set to be inside another: `⊆` is an ordering, and
the sets one can build are placed in it.

The ordering itself, its strict part, inclusion set against each way
of building a set, and — because every family of sets has an
intersection — a fixed point for every map that respects the order.

## ⊆ is a partial order

The chapter opens by establishing the three laws that make inclusion an ordering
rather than merely a relation — reflexivity, transitivity,
antisymmetry — and then the two sets that bound it.

Antisymmetry is the one carrying weight. `s ⊆ t` and `t ⊆ s` give a
set *equation*, and that is how essentially every set identity in the
library is proved: **SubsetAntisymEq** turns `s = t` into two
inclusions, each of which is a statement about elements that the
`set_basic` laws can interpret. The equality here is not a coincidence
of the definition — a set is nothing but the elements it admits, so
agreeing on elements is all that being equal can mean.

The bounds come in pairs, and the pairing is the point. `∅ ⊆ s` for
every `s` says ∅ is *a* lower bound; `s ⊆ ∅ ⇔ s = ∅` says it is the
*least* set, with nothing strictly below it. `𝕌` mirrors both.

## ⊊, the strict part

`⊊` is the same ordering with equality removed: `s ⊊ t` is
`s ⊆ t` together with `s ≠ t`. That makes it irreflexive and
transitive, and it composes with `⊆` on either side — a strict step
followed by an inclusion is still strict, and so is an inclusion
followed by a strict step.

The member worth knowing is **ProperSubsetWitness**, which trades the
inequality for an element that `t` holds and `s` does not — the form
that makes ⊊ something an argument can take apart.

Its bounds are ⊆'s, read strictly, and they degenerate as one would
expect: nothing is properly below ∅, nothing is properly above 𝕌, and
a set falls properly short of 𝕌 exactly when it misses something.

## Where the constructions come in

The next part places the meet and join in the ordering, and then
characterizes them. **InterSubset** and **SubsetUnion** locate them — a
meet is below each of its arguments, a join above each — but
**SubsetInter** and **UnionSubset** are the sharp statements: to sit
below `t ∩ u` is *exactly* to sit below both, and to sit above `s ∪ t`
is *exactly* to sit above both. That is what makes `∩` the greatest
lower bound and `∪` the least upper bound, which is the whole content of
calling this a lattice. `⋂` and `⋃` repeat all of it over an arbitrary
family, and both acquire a direction in the family itself: `⋃` rises
with it, `⋂` falls. At arbitrary arity the locating half is
**MemberSubsetUnions** — each member lies inside the union — stated on
its own because the set closer, holding the membership only as a
hypothesis, does not find the member that witnesses it.

Each of those two has a sharper form worth stating separately.
**UnionsMonotoneRefine** and **IntersAntitoneRefine** drop the
requirement that the families be comparable at all: it is enough that
each member of one be covered by *some* member of the other. The
inclusion-hypothesis versions are the special case where the covering
member is the set itself.

The same is done for the element-wise operations: inserting
into `s` and staying inside `t` costs exactly the new element's
membership, deleting only ever moves down, and landing inside
`delete(t, x)` is landing inside `t` while avoiding `x`. **SingSubset**
is the one to know — it says membership IS an inclusion once the element
is packaged as `{x}`, which is how a fact about a single element reaches
a law stated about sets.

The last part closes the circle. Inclusion can be read off either
binary operation without mentioning `⊆` at all — `s ∩ t = s`, or
`s ∪ t = t` — which is how a lattice recovers its order from its
operations.

## A monotone map has a fixed point

Because every family of sets has an intersection, **KnasterTarski** can
name a fixed point for any map F on sets that respects inclusion: the
intersection L of the sets F shrinks (those b with F(b) ⊆ b). F(L) lies
inside each of them, so F shrinks L; applying F to that inclusion, F
shrinks F(L) too, so F(L) is one of the sets whose intersection L is,
and contains L. The fixed point is stated, not merely asserted to
exist, because a consumer wants the set itself: Schröder–Bernstein
builds its bijection around it (`sets/cardinal`).

## The proofs

Almost every member here closes with one recorded `set_tac` ministep:
definitional unfolding of the set vocabulary down to a first-order
residual, then a kernel-checked refutation.

That is the honest shape for this chapter, not a shortcut. `s ⊆ t` is
*defined* as `∀x. x ∈ s ⇒ x ∈ t`, so each of these laws is a property
of `⇒` — reflexivity is `P ⇒ P`, transitivity is composition of
implications — read through that definition. Unfolding is the entire
argument, and there is nothing further a reader could be told. Which is
also why those proof bodies bind no variables: there is no step that
names one.

The members that depart from it each have a reason. **KnasterTarski** is
a chain of inclusions, each cited at the sets it relates.
**ForallSubsetInsert** splits its equivalence and cases on membership.
**SubsetUnionAbsorption** is proved one
direction at a time: its two directions are unrelated arguments — one
runs through `s ⊆ s ∪ t`, the other through what `s ⊆ t` does to the
union's members — and splitting the equivalence is what lets each be
seen for what it is. **UnionsMonotoneRefine** opens its goal before
closing it, for a reason particular to `⋃`: unfolding membership in a
union produces an existential carrying an equation, and that equation
is discharged against the covering witness only once the covering
hypothesis is available as a hypothesis rather than sitting behind
the `⇒`.

The driver consumes only the kernel's definitional axioms and
kernel-composed derivations, never a theorem, so the members it closes
rest on nothing but the definitional layer and do not consult the very
laws proved here; KnasterTarski, a chain of those laws, cites them.
