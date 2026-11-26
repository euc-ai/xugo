# set_algebra — the algebra of sets

`set_basic` says what it takes to be IN a constructed set. `set_order`
places the constructions in an ordering. This chapter is about what the
constructions do to *each other*, and it speaks in equations: `s ∪ t =
t ∪ s`, `𝕌 ∖ (𝕌 ∖ s) = s`, `⋃{s, t} = s ∪ t`.

Sixty-one members, in five files.

## ∪ and ∩ make a lattice, and ∅ and 𝕌 are its units

The lattice laws are the classical picture. Both operations are commutative,
associative and idempotent; ∅ is the unit for ∪ and the annihilator for
∩, and 𝕌 is each of those with the roles swapped. Then each distributes
over the other — which is what makes this a *distributive* lattice, and
is the one part of the picture that does not hold in an arbitrary one.

The two distributive laws are stated as **InterDistribUnion** (`s ∩
(t ∪ u) = s∩t ∪ s∩u`) and **UnionDistribInter** (`(s ∪ t) ∩ (s ∪ u) =
s ∪ t∩u`). The second is the one that surprises: intersecting two sets
that share a common part leaves that part plus whatever the other two
halves share.

**UnionEqEmpty** is the lattice's order in equational clothing. A union
is empty only when both sides are — the join of two things reaches the
bottom only if both were already there, which is `set_order`'s "∅ is the
*least* set" read without mentioning ⊆.

## ∖ is not a complement, but 𝕌 ∖ · is

Difference is not one of the lattice operations: it is
not commutative, not associative, and `s ∖ s = ∅` rather than `s`. What
it gives is *relative* complement, and taking the ambient set to be 𝕌
recovers the absolute one — **DoubleComplement** (`𝕌 ∖ (𝕌 ∖ s) = s`) is
the involution that says so.

The chapter's other difference laws are the degenerate cases (against
∅, 𝕌, itself), **DiffInsert** — removing `insert(x, t)` from `s` is
removing `x` and then removing `t` — and **InsertDiff**, which pushes an
insertion the other way and is the one law in this file that needs a
case (below). This part also holds `∖`'s interaction with insert
and delete, while `∪` and `∩` against insert live in the next part:
the boundary follows the OPERATION, not the constructor.

## insert and delete, and the four laws with a case in them

This is the chapter's largest part, because adding and removing a
single element interacts with everything. Most of it is what one would
guess: both are idempotent, both commute with themselves, and
**InsertDelete** and **DeleteNonElement** are the two halves of the
round trip — putting `x` back after deleting it recovers `s` exactly
when `x` was there, and deleting it changes nothing exactly when it was
not.

Four members are stated with a `COND`, and they are the ones worth
pausing on: **InsertUnion**, **InsertInter**, **DeleteInsert** here, and
**InsertDiff** over in the difference part. Pushing `insert(x, ·)` through a
binary operation has to ask whether `x` is already on the other side,
and the answer changes the shape of the result rather than just its
value; `DeleteInsert`'s question is the other one available, whether the
element being removed is the one just added. The law that escapes the
case is **InsertUnionEq** — inserting into a union is the same as
inserting into its LEFT operand first, unconditionally, because a union
cannot lose the element either way.

**InsertAbsorb** is the bridge back to membership: `x ∈ s` exactly when
inserting `x` does nothing. That is the same trade `set_order`'s
absorption laws make between an inclusion and an equation, one element
at a time.

## Disjointness

`disjoint(s, t)` is `s ∩ t = ∅`, and **InDisjoint** is
the form an argument actually uses: no element belongs to both. From
there the laws are what the definition forces — it is symmetric,
everything is disjoint from ∅, a union is disjoint from `u` exactly
when both halves are, and inserting `x` into `s` keeps `s` disjoint
from `t` exactly when `x` was not in `t` to begin with.

**DisjointSelf** is the one that is not a mirror of anything: a set is
disjoint from *itself* only when it is empty, since any element it held
would be in the overlap.

## ⋃ and ⋂ against the constructions

The two big operators are ∪ and ∩ at arbitrary arity —
`x ∈ ⋃s` is "`x` is in *some* member of `s`", and `x ∈ ⋂s` is "in
*every* member" — and this part works out what they do to each way of
building the family they range over.

The small cases are where the quantifiers show through. `⋃∅ = ∅` and
`⋂∅ = 𝕌`: over no members at all, "some member" is unsatisfiable and
"every member" is vacuous, so the two constants come out on opposite
sides. At one member each collapses to it, and at two they are exactly
∪ and ∩ — which is what makes them the arbitrary-arity versions rather
than merely analogues. **UnionsInsert** and **IntersInsert** are the
recursion behind all of that, peeling one member off the family.

**UnionsEqEmpty** and **IntersEqUniv** are the ∀/∃ asymmetry stated
directly: a union of a family is empty only if *every* member is,
while an intersection is everything only if every member is. Both read
"every", because both are the *hard* direction of their operator.

The asymmetry is visible one last time in **UnionsUnion** and
**IntersUnion**, which distribute each operator over a union of
FAMILIES; their entry docs say what separates them.

The ⋃ half also carries three members with no ⋂ mirror — `⋃𝕌 = 𝕌`, and
the two saying an empty member can be adjoined to or discarded from a
family without moving the union. Each is about a member contributing
NOTHING, and "nothing" is ∅ for a union and 𝕌 for an intersection, so
the ⋂ statements of the same shape are about adjoining 𝕌, which no
chapter has had reason to state.
