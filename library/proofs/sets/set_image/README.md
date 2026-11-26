# set_image — the image of a set under a map

`set_basic` and `set_order` speak about sets over a single element type:
what it means to belong to each constructed set, and for one set to be
contained in another. `functions` speaks about maps between two types.
This chapter is where the two meet. Given `f : A → B` and a set `s` of
`A`'s,

    image(f, s)   =   { f(x) | x ∈ s }

is a set of `B`'s, and the question the chapter answers is what that
operation preserves.

## Membership, first

Everything else is read through one fact, which `set_basic` already
states: `y` lies in the image exactly when it is `f(x)` for some `x` of
`s`. Three consequences open the chapter. A point of `s` lands in the
image (`FunInImage`). A property holds throughout the image exactly when
the pulled-back property holds throughout `s` — for one point
(`ForallInImage`, `ExistsInImage`), or for two or three at once
(`ForallInImagePair`, `ForallInImageTriple`) — so an argument about
images never has to name an image point. Read at the property `y ∈ t`, that transfer is the inclusion
test: `image(f, s) ⊆ t` exactly when f sends every point of s into t
(`ImageSubsetIff`). And `ImageEqEmpty` is the limiting case: the points of the
image answer to the points of the source, so one side runs out exactly
when the other does.

The image of the whole source is the map's RANGE, and its two readings
are stated once so that no argument about a range carries the
membership `x ∈ 𝕌`, which asks nothing: a point lies in the range
exactly when it is a value of the map (`InRange`), and every value lies
in it (`FunInRange`).

## The functor laws

Taking images respects the identity map and composition:

    image(λx. x, s) = s          image(f ∘ g, s) = image(f, image(g, s))

`ImageIdentity` and `ImageCompose` are what the word *functor* names, and
`ImageI` is the first of them stated through the identity COMBINATOR `identity_map`
rather than through the λ — the same theorem, and the reason both are
here is that later chapters cite both spellings.

`SimpleImage` closes the circle back to the notation this chapter opened
with: the comprehension `{f(x) | x ∈ s}` and the constant `image(f, s)`
are the same set. `SimpleImageGen` says it again with an arbitrary guard
in place of membership.

## Carrying the constructions across

`image(f, ·)` is a left adjoint in disguise, and the pattern of what it
preserves follows from that, though the chapter never says so: it
commutes with everything built from unions and gets only one inclusion
from everything built from intersections.

Unions pass through exactly — the empty set and `insert`
(`ImageClauses`), binary union (`ImageUnion`), arbitrary union
(`ImageUnions`), and `⋃` composed with an indexed family
(`UnionsImage`, and its monotone form `UnionsImageMonotone`).

Intersections do not. `image(f, s ∩ t) ⊆ image(f,s) ∩ image(f,t)` holds
(`ImageInterSubset`, and `ImageIntersSubset` at arbitrary arity), and the
reverse fails as soon as `f` identifies two points — one in `s`, one in
`t` — that were distinct. So equality is exactly what injectivity buys:
`ImageInterInjOn` (injectivity on a set holding both; `ImageInterInj` is
its form for a map one-to-one outright), `ImageDiffInj` and
`ImageDeleteInj` are the constructions that need it, each stating the
hypothesis it actually requires. `IntersImage` is the ⋂
counterpart of `UnionsImage`, and it is an equation because there the
intersection is taken over the family after `f` has already produced it,
so no two members' points ever have to be told apart.

## Inclusion, and the map itself

Everything above follows from membership: unfold what it means to lie in
an image, and the fact falls out. The rest of the chapter does not, and
it is different in one specific way — each part has to EXHIBIT a set
that unfolding does not produce.

The inclusion part reads the image against `⊆`. One direction is free
(`ImageSubset`: a larger source has a larger image), and so is the image
of one source under two maps that agree on it (`ImageCongruence`). The other asks when
a set lies inside an image, and answers that it does exactly when it IS
the image of a piece of the source. Producing that piece is the work.
For `SubsetImage` there is a canonical one — the part of `t` that `f`
sends into `s`, the largest that could work. For `SubsetImageInj` the
piece must moreover be one `f` does not fold, and the largest one is
precisely the wrong answer, so a single source is CHOSEN per point
instead. That choice is the chapter's one citation from outside set theory.

The map-side part turns the reading around: `image(f, ·)` is itself a map,
and four of its members say that a property of that map is exactly the
property of `f` — surjective for surjective, injective for injective,
each in both the absolute form (`SurjectiveImage`, `InjectiveImage`) and
the form relative to a subset (`SurjectiveOnImage`, `InjectiveOnImage`). Going from the SET
side to the POINT side, all four apply the set law to the smallest sets
there are, the one-point sets `{x}`. Coming back, surjectivity has to
PRODUCE a set and it is always a preimage, while injectivity produces
nothing: its hypothesis already speaks about two arbitrary sets. A
bijection of s onto t restricts to one of u onto v when a point lies in u
exactly as its image lies in v (`BijectionRestricts`): injectivity
restricts to any subset, and the image is v by antisymmetry of `⊆`.

Two more members open that part because they are what the surjectivity
results are read through. `SurjectiveImageEq` is the criterion for a set
to BE an image — membership matching pointwise is enough — and
`SurjectiveImageThm` says the same characterization as `SurjectiveImage`
with comprehensions in place of arbitrary sets.

## Pulling back

`image(f, ·)` is one map `f` induces on subsets; pulling back is the
other, and it runs backwards. The preimage is named in `functions`:

    preimage_on(s, f, t) = {x | x ∈ s ∧ f(x) ∈ t}

Asked the map-side part's two questions, `t ↦ preimage_on(s, f, t)`
answers with the variance turned over.

Pulling back is INJECTIVE exactly when `f` is surjective
(`InjectivePreimage`, and `InjectiveOnPreimage` relativized to a source
set `s` and a target set `u`). Distinct test sets have distinct
preimages only if `f` reaches every point that could tell them apart: a
point of `u` that `f` misses is invisible to preimages, and one such
point already collapses a test set onto a smaller one. The proof of the
harder direction is that observation made exact, and the test it takes
is a single pair — `{y}` against `∅`, which pull back to the same
subset of `s` precisely when `y` is missed.

Pulling back is SURJECTIVE exactly when `f` is injective
(`SurjectivePreimage`, `SurjectiveOnPreimage`). Every subset `k` of the
source is a preimage only if `f` never folds two points together, and
when it does not, the subset that pulls back to `k` is `k`'s own image —
a candidate that works precisely because injectivity stops it from
dragging anything else back in. The relativized form carries a second
condition, that `f`'s values on `s` stay inside `u`, and both conditions
turn out to be instances of the same hypothesis: read at `k := s` it
gives the bound, read at a one-point `k` it gives injectivity.

The unrestricted members are their relativized siblings read at `𝕌` on
both sides of the map.

That is the whole chapter: what images do to sets, and what images and
preimages say about maps.

## Mechanics

`setTac()` — the engine's set_tac ministep, definitional unfolding to a
first-order residual then a kernel-checked refute, recorded as one step —
is the closer everywhere, and for most members it is the entire proof.

The exceptions are all of one kind: something has to be put in front of
the closer that unfolding will not supply.

- A function constant is opaque to a closer whose vocabulary is the set
  constructors, so `ImageI` and `ImageCompose` unfold `identity_map` and `∘` first.
- What the residual keeps depends on whether the outer prefix is still
  standing, so `IntersImage`, `ImageInterInj` and `ImageDiffInj` strip
  their binders first.
- A set that no unfolding produces has to be written down, so the
  members of the last three parts that take their biconditional a
  direction at a time exhibit one — a preimage, an image, a one-point
  set, or a set of chosen sources — or apply a set law at one. Those are
  the chapter's only members with a case per direction. Most case labels
  name the set the branch offers; the two ⇐ branches of the image
  injectivity laws offer none, and say so.
- The two unrestricted preimage laws read their relativized siblings at
  `𝕌` on both sides of the map. `BySets()` unfolds `𝕌`, so
  `SurjectivePreimage`'s guards dissolve without a law being cited;
  `InjectivePreimage`'s instance and goal no longer meet once the driver
  has read them pointwise, so it closes by a `By`, which does no
  unfolding and is handed `set_order`'s two laws about `𝕌`
  (`SubsetUniv`, `UnivSubset`).

`SurjectiveImage` is split into its two directions, which is how its
siblings are written anyway.

The driver is sound to use on these theorems for the reason its sibling
chapters record: it consumes the kernel's definitional axioms and
kernel-composed derivations only, resolves no stored theorem, and has no
foundation closure — so proving a set law by it creates no cycle, since
these laws are downstream of the driver and never inputs to it.

One citation here is not set theory: `SubsetImageInj` needs to choose a source per point,
and choice arrives as `functions.SurjectiveOnRightInverse` — a statement
about maps with no image in it, which is why it lives in the sibling
chapter about maps rather than here. `BijectionRestricts` cites two set
facts of its sibling chapters, injectivity on a subset
(`functions.InjectiveOnSubset`) and antisymmetry of `⊆`
(`set_order.SubsetAntisym`).
