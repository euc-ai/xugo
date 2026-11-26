# finite_set — finiteness

The chapter of the `finite` predicate: which sets have finitely many
elements, how that survives the set constructions, and — the same
material read the other way round — which sets do not. Cardinality —
`card` and `has_size`, the counting that only finite sets admit — is the
chapter `cardinality` beside this one.

`finite` is defined inductively, and that one fact decides how the whole
chapter reads. It is the smallest predicate holding at `∅` and closed
under `insert` — two rules, stated in `definitions.go` beside
`infinite`, which is its negation, and `set_fold_stage`, the fold's stage
relation defined by recursion on the step count (`fold.go`'s members
read its two clauses off that definition). A definition by rules comes
with its theorems: the rules themselves, rule induction, that induction
strengthened to carry `finite` into the step, and the case analysis.
Those four are what the chapter cites. The closure form the constant is
minted with is not a proof surface — `Unfold` refuses it — so **no
member unfolds `finite`**. Other constants do get unfolded — `image` where
a member reasons about what a map carves out, `infinite` on every page
of the last file — and neither is a change of subject the way this one
is.

That is also why the set-membership driver the sibling `sets/` chapters
close with plays a smaller role here than there: it can reach the set
constructors *around* a statement, but not the predicate the statement is
about, since `finite` has no membership reading.
It remains the right tool for a leaf that really is about
constructors: inclusions like `FiniteInsert`'s `s ⊆ insert(x, s)`,
memberships in a construction like the ones the powerset split turns
on, and quantified forms of either.

## The rules and the principles the definition comes with

- **`FiniteRules`** — `finite(∅)`, and `finite(s) ⇒ finite(insert(x, s))`.
  The definition's rule set, registered verbatim by the door.
- **`FiniteInduct`** — induction over finite sets: a property true of ∅
  and preserved by adding one element is true of every finite set.
  "Smallest" read as a principle — `finite(a)` says `a` lies in every
  predicate closed under the two rules, so read at the property being
  proved it simply *is* the conclusion. The weak form: the step
  receives `P(s)` alone.
- **`FiniteInductStrong`** — the definition's strengthened induction:
  the step may assume the set it enlarges is finite, alongside the
  property it carries. The door derives it by running the plain
  induction on `λt. finite(t) ∧ P(t)` and reading the property back.
- **`FiniteInductFresh`** — that induction sharpened once more: the
  element added is *new* to the set. Freshness is not obtained from the
  definition but dispatched — if `x` already lies in `s` then
  `insert(x, s)` is `s` and the step has nothing to prove, so a rule
  stated for a fresh `x` runs the induction for every `x`. This is the
  principle the chapters above `finite_set` actually cite: a fold over
  `insert(x, s)` recurses only when `x` was not already counted.
- **`FiniteInductFreshOn`** — the fresh induction over the finite sets
  whose members satisfy a predicate `Q`: the step meets a new `x` with
  `Q(x)`, added to a finite `s` all of whose members satisfy `Q` — the
  shape of a fold whose terms must lie in a carrier. It is
  `FiniteInductFresh` run at the guarded property "if every member
  satisfies `Q`, then `P`": across a fresh `x` the guard on `insert(x, t)`
  is `Q(x)` together with the guard on `t`.
- **`FiniteCases`** — the case analysis the door derives: a finite set
  is either empty or splits off one element, leaving a finite
  remainder. The rules read backwards give one direction; induction at
  that very disjunction gives the other.

The last two members turn the induction round, and walk a finite set
*down* along `⊊` instead of up along `insert`. The first is the descent
principle itself, which Hall's theorem (`relations/matching`) descends
along; the second is the removal rule built on it.

- **`FiniteInductProperSubset`** — a property that holds at every finite set whose
  proper subsets all carry it holds at every finite set. What makes a
  downward walk terminate is that below a finite set there is no
  infinite descending chain, and the chapter reaches that without any
  notion of wellfoundedness: it runs ordinary induction on the
  *relativized* statement — "every descending property reaches every
  subset of this set" — and reads the result at the set itself,
  inclusion being reflexive. Relativizing alone is not enough. A step
  adds a point `x`, and the subsets of `insert(x, v)` that *contain*
  `x` are not subsets of `v`, so the induction hypothesis says nothing
  about them. The repair is to quantify the descending property
  *inside* the relativized statement, so that a step may apply its own
  hypothesis at a **shifted** property — `P` at a set together with `P`
  at that set with `x` added — whose right half, read at the subsets of
  `v`, is exactly the part that was missing.
- **`FiniteInductDelete`** — induction by *removal*: a property holding
  at ∅, and inherited by any non-empty finite set from at least one of
  its one-point deletions, holds at every finite set. The rule is
  unusual in what it lets the caller choose — not survival of removing
  an arbitrary point, but only of *some* point, named after seeing the
  set. That is what makes it the natural rule for a property carried by
  a distinguished element, a maximum or a first coordinate, rather than
  by an arbitrary one. Removal shrinks, so the rule is descent, and the
  whole content is `FiniteInductProperSubset` read at `P`: what descent hands the
  step is that every proper subset already carries `P`, and the point
  the hypothesis names deletes the set to one of them.

## Finiteness and the subset order

- **`FiniteSubset`** — a subset of a finite set is finite. The induction
  is on the *containing* set, at the predicate "every subset of `u` is
  finite": a subset has no structure of its own to induct on and the
  containing set has all of it, so generalizing the subset away is the
  whole trick. Across `insert` the work is the observation that enlarging
  a set by one element enlarges its subsets in exactly one way — each is
  either already a subset or one such with the new element added.
- **`FiniteInsert`** — adding one element changes nothing about
  finiteness. Backwards it is `finite`'s own insert rule; forwards it is
  `FiniteSubset` read at the one inclusion `insert` always gives,
  `s ⊆ insert(x, s)`.

Together these two are why no later member runs the induction again:
to show a construction finite, either bound it by something finite or
build it up by insertions.

## Induction over finitely supported functions

A function into `num` that is nonzero at only finitely many points is a
finite set with a number at each point; the principles above induct on
the set alone, and this one carries the numbers along.

- **`FiniteInductSupport`** — a property that holds of the zero function
  `λx. 0`, and passes to `u` from `u` with one nonzero coordinate `a`
  cleared to `0` (`λx. COND(x = a, 0, u(x))`, with `u`'s support finite),
  holds of every function of finite support. It is the rule for a
  property of a finitely supported vector — exponents, multiplicities —
  proved by removing one supported coordinate at a time, and it is the
  bounding-set induction done once: `FiniteInductFresh` runs on a finite
  `E` at "every function supported in `E` has the property". A function
  supported in `insert(a, E)` either vanishes at `a`, so `E` already
  bounds it, or loses its `a`-coordinate to a function `E` bounds; the
  support of `v` then bounds `v` itself.

## Finiteness under the set constructions

- **`FiniteUnionImp`** — a union of two finite sets is finite, by
  induction on the left operand at "joining `t` leaves a finite set".
  Joining `t` to ∅ gives `t` back; joining it to one more element gives
  the same set as adding that element to the join, so the insert rule
  carries finiteness across the step.

- **`FiniteUnion`**, **`FiniteInter`**, **`FiniteDiff`**,
  **`FiniteDeleteImp`**, **`FiniteDelete`** — the remaining
  constructions, and none of them needs an induction. Each lands
  *inside* one of its own inputs, so each is `FiniteSubset` read at one
  inclusion: an intersection sits inside either factor, a difference
  inside its minuend, a deletion inside its source. Only the union
  genuinely grows, which is why it is the one that inducts.
- **`FiniteSing`** — the one member that neither bounds nor inducts. A
  singleton IS `∅` with one element inserted, so the two clauses of
  `FiniteRules` fire once each, the base on `∅` and the insert clause
  on the element, and there is no third thing to check.

Stated the other way round: this tier is one move — `FiniteSubset` at an
inclusion — made five times, with only the inclusion varying; plus the
union, which is the one construction that genuinely grows and so is the
one that inducts, and the singleton, which is small enough to read
straight off the rules.

## Finiteness travels along a map

- **`FiniteImage`** — the image of a finite set is finite, under any map
  at all. The chapter cannot argue this by size, having no notion of
  size to compare with; what it has is the induction principle, which
  says a finite set is one *reached* from ∅ by finitely many insertions.
  So the
  comparison is replayed as a construction: build the image the same way
  the source was built. That works because image is computed by
  recursion on exactly the two constructions finite is closed under — at
  ∅ the image is ∅, which is finite outright, and at one more source
  point the image gains exactly that point's value, which the insert
  rule absorbs. Nothing is assumed about the map: one that collapses
  points only makes the image smaller, and the induction never counts.
- **`FiniteImageExpand`** — the same theorem with the image written out
  as the comprehension `image` abbreviates. The two sets are one by the
  constant's own definition, so identifying them is a question about the
  set constructors and spends no finiteness; the induction above is not
  run a second time. It is a member because a consumer meets an image
  under both spellings and should not have to unfold the constant to use
  what this chapter proved.
- **`FiniteImageInjGeneral`**, **`FiniteImageInjEq`** — the same
  question travelled backwards, which no map answers in general: a map
  may send infinitely many points to one, and then a finite image says
  nothing about the source. Assuming it does not — that `f` separates
  the points of `s` — is exactly enough, and the reason is that a map
  which separates points can be *undone*. Fix a `g` undoing `f` on `s`;
  then any `x` of `s` whose value lands in a set `t` is `g`'s value at
  that landing point, so the part of `s` that `f` sends into `t` lies
  inside `image(g, t)` — an image, where the previous member already
  applies. That is the general statement; the equivalence
  `finite(image(f, s)) ⇔ finite(s)` is it read at `t := image(f, s)`,
  where `s` is recognized as the part of itself that `f` sends into its
  own image. Injectivity is spent once, in producing `g`, and the rest
  of both arguments is about plain images.
- **The eight transfer members** — `ExistsFiniteSubsetImageInj`,
  `ForallFiniteSubsetImageInj`, `ExistsFiniteSubsetImage`,
  `ForallFiniteSubsetImage`, `FiniteSubsetImage`,
  `FiniteSubsetImageImp`, `FiniteImageEq`, `FiniteImageEqInj` — are ONE
  further fact said eight ways: *a finite subset of an image is the
  image of a finite subset*, and the subset can moreover be chosen so
  that `f` does not fold it. Read it as an exchange between the two
  sides of the map: whatever a property `P` asked of a finite subset
  over there may be asked of a finite subset over here instead.

  Three axes index the eight. Whether the exchanged set is quantified
  `∃` or `∀` — the `∀` forms are their `∃`-twins negated, since *every*
  finite subset satisfies `P` exactly when *no* finite subset satisfies
  `¬P`. Whether the folding clause is promised or dropped — dropping it
  is a weakening, and the `⇐` leg never consulted injectivity anyway,
  which is why the members that promise it and the members that do not
  share that leg verbatim. And whether `P` is arbitrary or FIXED —
  fixing it at "being exactly this set" turns the exchange from a
  transfer principle into a description: a finite `t` inside
  `image(f, s)` simply *is* `image(f, u)` for some finite `u ⊆ s`, and
  both directions fall out of the one instance, because a fixed property
  leaves each side's `∃` a single candidate.

  Only the `∃`/arbitrary-`P`/with-folding corner carries content —
  `set_image.SubsetImageInj` supplies the preimage and `FiniteImageInjEq`
  carries its finiteness back. Everything else is that corner read
  somewhere else on the three axes. `FiniteSubsetImageImp` weakens the
  description's equation to an inclusion, and `FiniteImageEq` /
  `FiniteImageEqInj` read it at `t := image(f, s)` where the containment
  it asks for is reflexivity — giving the tier's sentence in its most
  usable form: *a finite image is always the image of a finite piece,
  and the piece can be taken faithfully.*

## Finiteness of what a set-builder carves out, and of a chain

Two strands. The chapter's first members whose subject is written
`{… | …}`, which divide by what the builder ranges over; and a second
strand that drops the builder and keeps only the second type level,
where the subject is a family of sets ordered by inclusion.

Ahead of both stands a member with no finiteness in it at all.

- **`PowersetClauses`** — how the collection of subsets is BUILT.
  Nothing lies inside ∅ but ∅ itself; and enlarging a set by a point
  DOUBLES its subsets, the new half being the old half with that point
  put in — so the subsets of `insert(a, s)` are the subsets of `s`
  together with the image of those under inserting `a`. The hard half
  turns on whether a subset of the enlarged set holds the new point: one
  that misses it keeps nothing outside the old set, and one that holds
  it is its own deletion of that point, with the point put back. Its two
  clauses stand at INDEPENDENT element types, which is the theorem and
  not a slip: the base clause names no set the step clause names, so
  nothing ties its element type to the step's.

- **`FiniteRestrict`** — cutting a finite set down by any condition at
  all leaves a finite set. A builder ranging over the *points* of `s`
  can only thin it out: whatever the condition is, what survives it sat
  in `s` already. So this is the constructions part's move once more — exhibit the
  inclusion, let `FiniteSubset` finish — read at the inclusion a
  set-builder gives rather than at one of the set operations.
- **`FinitePowerset`** — a finite set has finitely many subsets. A
  builder ranging over the *subsets* of `s` is the opposite case to the
  one above: it manufactures sets `s` never contained, so nothing lying
  around bounds it and the collection has to be built the way `s` was,
  one insertion at a time. That building is the identity stated above,
  and this member is an induction that reads one of its clauses at each
  case, as a rewrite of the collection standing under `finite`. What is
  left each time is a finiteness fact about whatever the clause put
  there: below ∅, a collection holding one member; at an enlargement, a
  union of two collections one of which is an image of the other. So
  finiteness surviving an image and surviving a union of two is the
  whole of what this member spends, which is why it is the first to
  need the closure tier *and* the image tier under it where the earlier
  ones needed neither.

  Worth saying because it is the natural thing to assume otherwise:
  **nothing here requires `x` to be new.** If `x` was already in `s` the
  two halves simply overlap, and the identity holds either way — an
  equation does not care that its right-hand side counts something
  twice. Disjointness is what *counting* would need, and this chapter
  never counts; `cardinality` will, and that is exactly where the strong
  induction principle starts earning its keep.
- **`FinitePowersetEq`** — a set is finite exactly when its powerset is.
  One direction is `FinitePowerset`; the other is why the equivalence is
  worth stating, since a collection of subsets could be finite for no
  better reason than that there were few subsets to have. The witness is
  the singleton map `x ↦ {x}`. It sends `s` into the powerset, so the
  singletons are a finite collection; and it separates the points of
  `s`, a one-element set determining its element. A map that separates
  points neither creates nor destroys finiteness, so `s` is as finite as
  its singletons are.

Once the powerset exists it is the bound the file reaches for wherever a
collection of sets needs one, there being nowhere else to get one.

- **`FiniteRestrictedSubsets`** — imposing any condition at all on the
  subsets of a finite set leaves finitely many of them: `FiniteRestrict`
  read one level up. Both cut a collection down by a condition nothing
  is assumed about, and both are settled by naming what the survivors
  were drawn from. What changes with the level is that the ambient
  collection is no longer lying around — a restriction of `s` lands
  inside `s`, where a restriction of `s`'s subsets lands inside `s`'s
  powerset.
- **`FiniteUnions`** — a union over a family of sets is finite exactly
  when the family is finite and so is every set in it. Neither condition
  is free, so the two directions are separate arguments. Backwards is
  the constructive one, and it inducts over the FAMILY rather than over
  a set: the union of nothing is nothing, and one more member adds
  exactly its own points. Forwards needs no
  induction, only the observation that every member of a family is
  contained in that family's union — which is what a union is — so each
  member is finite for the same reason the union is; and the family,
  being a collection of subsets of the union, sits inside the union's
  powerset. That last step is the one worth pausing on: it bounds the
  family by a collection the family is not a member of and has no
  evident relation to.
- **`FiniteFiniteUnions`** — the same equivalence with the family's
  finiteness granted in advance. A conjunct known to hold is discharged
  wherever it stands, and here it stands on the side of the equivalence
  that speaks about the family, so what remains is the condition on the
  members. Its sibling read under an extra hypothesis; nothing about
  unions is proved a second time.

`FiniteTransitivityChain` and the two product members range over neither
the points of a set nor its subsets.

- **`FiniteTransitivityChain`** — a finite set on which a strict order
  is everywhere continuable is empty. Read the relation as "comes
  strictly later": nothing comes after itself, coming after is
  transitive, and every point of the set is followed by another point
  *of the set*. A finite set cannot support all three. The proof does
  not build the revisiting chain, which would need counting; it runs the
  induction the finiteness is there to license, and the content is all
  in the step. Add a point `x` to `u` and suppose the enlarged set is
  still everywhere continuable: `x`'s own successor cannot be `x`, so it
  lies in `u` already; and a point of `u` whose successor was `x` can
  follow `x`'s step instead, transitivity closing the two moves into
  one. So `u` too is everywhere continuable, and the induction
  hypothesis empties it — leaving `x`'s successor nowhere to be. The
  step case never arises, and at ∅ there was nothing to prove.
- **`FiniteProductDependent`**, **`FiniteProduct`** — the values of a
  map on every point of a finite set paired with every point of that
  point's own finite fibre are finitely many; and a product of two
  finite sets, `set_cross(s, t)`, is finite, being the case where the
  fibre does not vary and the map is the pairing. For each base point,
  the values form the image of its finite fibre. These images form a
  finite family, and the whole dependent product image is their union.
  `FiniteImage` and `FiniteUnions` supply its finiteness.
- **`FiniteImagePair`** — two maps that take finitely many values on a
  set take finitely many pairs of values together: the pairs lie in
  the product of the two images, finite by `FiniteProduct`, and
  `FiniteSubset` carries finiteness down.

The chain strand takes the second type level as its whole subject. A
CHAIN is a family any two of whose members are comparable under `⊆`, and
a finite non-empty one is therefore an ordering with endpoints — which
is all four of these members say, from different sides.

- **`UnionsInChain`**, **`IntersInChain`** — a non-empty finite chain
  contains its own union, and its own intersection. Said the other way:
  it has a largest member and a smallest one, and those are exactly `⋃`
  and `⋂` of it. Neither would hold without finiteness — an infinite
  chain need contain neither. `FiniteTransitivityChain` rules out
  continuing strict inclusion indefinitely inside the family, giving
  a maximal member; comparability makes it the largest and hence the
  union. Reversing inclusion gives the smallest member and the
  intersection.
- **`FiniteSubsetUnions`** — a finite subset of `⋃f` already sits inside
  the union of finitely many members of `f`. No chain needed: each of
  the finitely many points is covered by *some* member, and finitely
  many choices make a finite subfamily. The induction is on the subset,
  which is what keeps the argument free of any choice principle.
- **`FiniteSubsetUnionsChain`** — the two composed. Shrink the family to
  a finite subfamily still covering `s`; a subfamily of a chain is a
  chain, so that subfamily contains its own union, which is one member
  of the original containing all of `s`. The empty case is separate and
  is where non-emptiness of `f` is spent: nothing covers `s` only if `s`
  is empty, and then any member will do.

The file spans three type levels in all — a collection of sets over a
set of points, and pairs drawn from two sets at once — and that shows up
in the proofs as laws having to be read one level up before they can be
cited.

## The same chapter, contraposed

`infinite` is defined as the negation of `finite` and has no content of
its own, so unfolding it is not a change of subject the way unfolding
`finite` is: it leaves a finite-side statement standing, and the work is
to say which already-proved theorem that is. That is the whole of the
first four members below — one of which needs no unfolding at all,
because what it leans on already speaks of infinite sets. The fifth is
the exception the file exists for: what stands after its unfolding is a
counting argument nothing else in the chapter needed, so the file proves
that argument rather than citing it.

- **`InfiniteSuperset`** — a set containing an infinite set is infinite.
  This is `FiniteSubset` contraposed and nothing else: finiteness
  descends along `⊆`, so its failure climbs.
- **`InfiniteDiffFinite`** — removing a finite set from an infinite one
  leaves an infinite set. Only the finiteness of what is removed
  matters. Were the remainder finite, putting the removed part back
  would exhibit a finite set containing the original — every point
  either survived the removal or was what was removed — and a set inside
  a finite set is finite.
- **`InfiniteImage`** — a map that separates the points of an infinite
  set carries it to an infinite one. `FiniteImageInjEq` settles the
  finite side in both directions at once for such a map, and an
  equivalence reports the failure of a property as readily as the
  property.
- **`InfiniteImageInj`** — the same for a map injective everywhere,
  which separates in particular the points of any given set.
- **`FiniteImageInfinite`** — a map taking only finitely many values on
  an infinite set takes one of them infinitely often. Contrapositively:
  if no value were, every fibre would be finite, and the fibres cover
  the set — each point lies in the one over its own value. There are
  only as many fibres as there are values, so the set would be a union
  of finitely many finite sets, hence finite. Indexing the fibres by the
  **values** rather than by the points is where the hypothesis is spent:
  either index gives the same collection, but only that one presents it
  as the image of a finite set, and that presentation is the entire use
  the finiteness of the image is put to.

Membership in this file is the notion rather than the duality: a
statement about infinite sets need not have a partner on the finite
side. The first four have one; the last does not, and its counting
lemma is the reason the file stands apart from the four chapters its
members would otherwise be scattered across.

## Folding over a finite set

Everything above says which sets are finite. This part says what one
can DO to a finite set that no infinite set admits: fold a step
function over its elements one at a time, and get an answer that does
not depend on the order they were visited in. That last clause is the
whole content, and it is what the counting chapter below rests on.

The instrument is `set_fold_stage`, this chapter's own definition, by recursion
on the number of steps: `set_fold_stage(f, b, s, a, n)` says that folding `f`
from `b` over `s` in exactly `n` steps CAN produce `a`. It is a
relation and not a function on purpose — at each step ANY element of
the set may be the one taken off — so a set with several elements is
folded in several ways, and the part's work is to show that on a finite
set all of them agree.

- The two clauses are the definition's own (`setFoldStageDef`), and each
  member reads them off it as a fact at its own argument tuple. In no
  steps the fold reaches `b`, and only out of the empty set. In one step
  more than `n`, some element `x` of `s` comes off first, the remaining
  `n` steps fold `s ∖ {x}` to some `c`, and the answer is `f(x, c)`.
- **SetFoldStageSingleton** — what ONE step is. A one-step fold is a fold of
  a singleton, and its value is the step applied to that point and the
  starting value. A set with a member whose removal leaves nothing IS
  that singleton, and that is the entire content.
- **SetFoldStageStep** — the rearrangement, and the one place the hypothesis
  on `f` is spent. If the step function's two arguments do not
  interfere — feeding in `x` then `y` gives what feeding in `y` then
  `x` gives — a fold can be rearranged to take ANY chosen element of
  the set off first. By induction on the length: at one step there is
  only one element to choose; at more, either the chosen element came
  off first already, or the induction hypothesis moves it to the front
  of the shorter fold and the commutation swaps the outer two
  applications.
- **SetFoldStageUnique** — single-valuedness. Two folds of one set reach the
  same value in the same number of steps. One induction on the first
  length, with the rearrangement making the second fold take the same
  element off first, so the induction hypothesis compares two folds of
  one smaller set. A zero-step fold beside a stepping fold of the same
  set is a contradiction outright, the stepping one having named an
  element of ∅.
- **SetFoldStageExists** — totality, on the finite sets and nowhere else. ∅
  folds in no steps, and a set with one further point folds by taking
  that point off first. This is where finiteness enters the part, and
  it is why the whole development lives in this chapter rather than
  beside the counting it serves.

Those last two are what turn the relation into a function.

- **SetFoldStageFold** — the fold AS a function of the set, chosen out of the
  relation: `g(s)` is the value some fold of `s` produces. The choice
  set is inhabited by totality and forced by single-valuedness, so
  nothing about the choice shows. The clauses come out stated at a
  delete — for any point `x` of a finite `s`, `g(s)` is `f(x, g(s ∖ {x}))`.
- **FoldExists** — the same function's clauses stated at an insert,
  which is how a finite set is BUILT rather than how it is taken apart:
  `g(∅)` is `b`, and putting a point in applies the step once, unless
  the point was already there. Turning the one form into the other is a
  case split on that "unless". This is the surface the counting chapter
  consumes, and the only one it does.

## What is not here

Three subjects a reader may expect to find under "finiteness" and will
not, each absent for its own reason.

- **"Finitely many of", as a combinator.** A property of sets can be
  lifted to a property of a set built from a FAMILY: it holds when the
  set is a union of a family each of whose members has the property.
  Finiteness is one condition such a lift can be taken at, and a great
  many statements about the combinator therefore mention it — but their
  subject is the combinator, not finiteness, and nothing in this corpus
  defines one.
- **Finiteness of a TYPE, as an encoding.** Where a dimension is
  itself a type and the finiteness of that type is what makes a
  cartesian power well behaved, "finite" is doing indexing work rather
  than set theory. That encoding belongs to `cartesian/`, is built
  term-level there, and says nothing about the sets in this chapter.
- **Enumerating an infinite set of naturals.** An infinite set of
  naturals is the range of a strictly increasing sequence. That is real
  mathematics — a well-founded recursion on minima, resting on a wide
  slice of ℕ's division and parity theory — and not a corollary of
  anything here. It is the one item in this list that would be a genuine
  addition to the chapter.

What is genuinely counting rather than finiteness — how many maps a
finite set admits into another, how many subsets it has — is the chapter
beside this one, below.

## The chapter beside it

Counting lives beside this chapter, in
[cardinality](../cardinality/README.md): `card(s)` is how many elements a
finite set has, `has_size(s, n)` says that count is `n`, and both are
notions only finite sets admit. Everywhere in THIS chapter a theorem
carries `finite` across a construction; there, a theorem reads the
number. The dependency is one-way — `cardinality` imports this package and
never the reverse.
