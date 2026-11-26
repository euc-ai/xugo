# set_basic — the language of sets

A set, here, is not a new kind of object. It is a predicate: a set of
`A`s **is** a function `A → bool`, and `x ∈ s` is `s` applied to `x`.
Everything in this chapter follows from taking that identification
seriously, and the chapter's job is to make it usable — to say, once and
for all, what it takes to belong to each of the sets one can build, and
how to take an arbitrary set apart.

The chapter gives seventeen definitions and twenty-nine theorems on set
constructors, membership, and quantification.

## Definitions

The basic constructors come first.
Membership `set_member` is application; the two names a comprehension
lowers to, `set_comprehension` and `comprehension_spec`, come first;
then `empty_set`, `universe`, `insert`, and every operation as a
comprehension over membership — `delete`, `union`, `intersection`,
`set_difference`, `subset`, `proper_subset`, `disjoint`, `big_union`,
`big_intersection`, `image`. No statement spells these names: each is
the meaning of a notation (`∈`, `{x | φ}`, `∅`, `𝕌`, `{a, b}`, `∪`,
`∩`, `∖`, `⊆`, `⊊`, `⋃`, `⋂`), and an equation spells its definiendum
by a stand-in (`member`, `set_union`, `is_subset`, …) because the DSL
keeps the names for its set surface. The kernel checks each definition
at the mint, and the `set_tac` unfolds every set chapter closes with
read these mints and nothing else; the sets domain's vocabulary table
now carries only the two nullary names, every other one reading its
type off its definition here.

## Set equality is membership

The chapter opens with **Extension**: two sets are equal exactly when
they have the same members. It is the bridge every set *equation*
crosses to become a statement about elements, which is what the rest of
the chapter then interprets. **NotEqualSets** is its contrapositive,
and the one an argument by contradiction reaches for: if agreeing on
every element is what equality means, then two sets differ exactly
when some element exists that they disagree about.

Its proof is a single unfolding, and that is worth a word lest it look
too thin. Sets are functions, and the normalizer already dissolves an
equation between functions into its pointwise form — so by the time
`s = t` is a goal it reads `∀x. s(x) ⇔ t(x)` on its own, and all that
remains between the two sides is that `s(x)` and `x ∈ s` are the same
thing.

## Membership in a constructed set

The constructor laws hold one member per constructor, each answering the
same question: given how this constructor is defined, what does it take
to be in the set it builds? It runs from the two constant sets (`∅`,
`𝕌`) through adding and removing a single element, the binary
operations, the image of a map, and the big operators.

These laws are what the rest of set theory is written in. An inclusion
or an identity between constructed sets becomes, through Extension, a
claim about elements; these laws are what that claim means.

## Toggling a point

`set_toggle(i, X)` reverses membership at `i` and preserves membership
at every other point (`ToggleDef`, `InToggle`). It removes `i` if
`i ∈ X` and inserts it if `i ∉ X` (`ToggleWhenMember`, `ToggleWhenAbsent`).
Two flips at the same point recover `X` (`ToggleInvolution`). For fixed
`X`, distinct points give distinct sets after one flip (`ToggleInjective`).
A flip at `j` commutes with inserting a different point `i`
(`ToggleInsertCommute`).

## Quantifying over a constructed set

The quantifier transports ask the constructor question one level up. The laws
above say what it takes for ONE element to be in a constructed set;
these say what happens when a whole quantifier ranges over one. The
constructor dissolves, and what is left quantifies over the pieces the
set was assembled from: adding an element splits that element off, a
union splits into its two sides, a big union becomes two quantifiers —
one choosing a member of the family, one ranging inside it.

They come in dual pairs, and the duality is the content: over a set
built from pieces, a universal claim is the CONJUNCTION of the claims
about the pieces and an existential one is their DISJUNCTION. That is
what makes such a quantifier usable in an argument — a hypothesis
about all of `s ∪ t` is consumed by taking the side one needs, and a
goal about all of it is discharged by proving both.

**ForallInInsert** is the one that earns its keep most often: it is
the shape an induction over a finite set leaves behind at every step.

## Taking a set apart

The laws above describe sets one has BUILT. This part is about a
set one has merely been given: decide whether it is empty
(**MemberNotEmpty**), and if it is not, split off one of its elements
(**Decomposition**), which together give the case analysis
(**SetCases**) that arguments over arbitrary sets run on.

This is where the chapter stops being purely definitional. Everywhere
else, unfolding a definition and refuting is the whole argument; here
the ⇒ directions must EXHIBIT something — a member, or what remains of
the set once a member is removed — and `delete(s, x)` is the witness
that does it.

## The proofs

The membership laws use `set_tac` to unfold the set vocabulary and
check the resulting first-order statement in the kernel. The toggle
laws open `ToggleDef` and close by the same membership reasoning.
