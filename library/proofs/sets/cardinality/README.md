# cardinality — how many elements a finite set has

`card(s)` is that number, and `has_size(s, n)` says it is `n`. Both are
notions only finite sets admit, which is why this chapter is nested
inside `finite_set` rather than placed beside it: `card` is total only
because the recursion defining it is justified by finiteness. Almost
every member here STATES finiteness, and the parent chapter is where
that hypothesis gets established. The exceptions are the members that
count something already known finite by construction — a singleton, the
two truth values — and the one that is handed a size rather than a set.

Not every member READS it, though, and the ones that do not are worth
recognizing as a kind rather than as a list: a member whose whole content
is repackaging another member's statement carries finiteness across
without ever reasoning with it. `PsubsetOfDifferentCount` never counts;
the two transport members — `MutualInversesHasSize` and its equivalence —
never unfold a size; and the two `Forall…` readings of the bounded
exchange carry `card`, `finite` and `⊆` through a negation while spending
none of them. Each says so where it appears below.

`has_size` has no chapter of its own. It is definitionally
`finite(s) ∧ card(s) = n`, so a boundary between it and `card` would cut
through members rather than between them.

## What the chapter holds

The counting theorems, grouped below by what they count, and a handful
of statements of the chapter's own that carry between them.

Those own statements fall into kinds. Most say how a count SPLITS — at a
single member, at a whole subset, at a union's left operand — which is
the move almost every member here is spending. Two read a split in the
other direction, as GROWTH: what a count does when a point is laid in,
and the bridge between a count being at least one and the set having a
point at all; reading a removal as growth is what lets several members
avoid subtraction entirely. One bounds instead of computing, and one is
a shared step two members divide. Each says so where it appears below.

### Where counting comes from

`card` is not defined by a recursion. To fold a step over a set you must
visit its elements in some order, and a set has no order — so the fold
is introduced as an arbitrary function that happens to satisfy the two
clauses one wants. `set_fold` is Hilbert's ε over exactly that
specification, and `card` is that fold taken at the step which adds one.
All three counting names — `set_fold`, `card`, and `has_size` as
`finite(s) ∧ card(s) = n` — are this chapter's own definitions
(`definitions.go`).

A definition by choice says nothing until something is there to choose
from, and supplying that is the chapter's first member.

- **`FiniteRecursion`** — a fold over the finite sets really does compute
  what its clauses say. The one thing asked of the step is that its two
  arguments do not interfere: feeding in `x` then `y` gives what feeding
  in `y` then `x` gives, which is what makes the answer independent of
  the order the elements are visited in.

  The proof is two sentences. A fold with these clauses *exists*; and
  `set_fold(f, ·, b)` is by definition a choice among the functions that
  have them, so unfolding the definition leaves the ε-term facing its own
  specification, which the existence discharges. No induction over the
  set appears, and no order of visits — both live beneath, in the
  well-definedness of the fold, which this chapter absorbs rather than
  restates.

- **`FiniteRecursionDelete`** — the same fold read at a DELETION rather
  than at an insertion: what a set's fold is, given the fold of that set
  with one element taken out. The two are one theorem from two sides.
  The insertion form answers "what does putting an element in cost", and
  its answer is conditional on the element being new; this one asks
  nothing in return, because both branches of the conditional are
  stated. That is what a consumer walking a set DOWN wants — name any
  point and get the fold of the remainder, with no side condition to
  discharge first. One branch, one law: where the point is in the set,
  putting it back into the remainder recovers the set, so the insertion
  clause read AT the remainder is already the answer; where it is not,
  deleting changes nothing and no recursion is spent.

- **`FiniteRecursionWithin`** — `FiniteRecursion` for a step that is
  closed and left-commutative only on a set `K`, folded from a start in
  `K`. The step guarded by `K` — `f` inside `K`, standing still outside
  it — commutes everywhere, so `FiniteRecursion` gives it a fold. That
  fold never leaves `K` on a finite set, so each of its steps is a step
  of `f`, and it has `f`'s own clauses: the witness the choice behind
  `set_fold(f, ·, b)` needs. A module on a set folds its sums this way.

- **`FoldOfAgreeingStepsWithin`** — two steps that are closed and
  left-commutative only on a set `K`, folded from a start in `K`, fold a
  finite set alike when they agree on its points. `K` is spent once, at
  the start: `FiniteRecursionWithin` gives each fold its two clauses, and
  those speak of every finite set with `K` nowhere in them. The induction
  then runs on the set, and the agreement has to travel INSIDE the
  property rather than be assumed once outside: it is a statement about
  the set, so it changes as the set grows, and the sets the induction
  passes through are not subsets of the one in hand. Across a fresh point
  both folds take their step there, and the two steps are one step at
  that point applied to one value.

- **`FoldOfAgreeingSteps`** — a fold reads its step function only at the
  points of the set it folds, so two steps agreeing on those points fold
  it to the same value, whatever either does elsewhere. Both steps are
  asked to commute — not for the proof's convenience, but because without
  it neither side of the equation says anything. It is
  `FoldOfAgreeingStepsWithin` read at `K = 𝕌`, where every start and every
  step lies inside.

- **`CardClauses`** — the empty set counts none, and putting an element
  into a finite set raises the count by one unless the element was
  already there. These are `FiniteRecursion`'s own clauses read at the
  step that forgets the element and adds one: a step which ignores its
  element cannot tell in which order two of them arrived, so the side
  condition costs nothing. Everything the rest of the chapter computes
  with comes through here.

### The calculus

Four theorems, one arc, all of them resting on the clauses above.
A count is a lossy summary of a set — how many elements there are says
almost nothing about which ones — so the arc starts at the single value
where it says everything, and ends where counting stops describing sets
and starts doing arithmetic.

- **`CardEqZero`** — a finite set is counted 0 exactly when it is empty.
  One direction is card's zero clause read along an equation. The other
  is an induction that never uses its hypothesis: the property survives
  an insertion vacuously, because a set just enlarged by a new element
  counts one more than something and no successor is 0. What the
  induction supplies is only that every finite set is reached from ∅,
  and the strong rule is needed solely because its new-element premise
  is the side condition card's clause turns on.

- **`CardSing`** — a one-point set has one element. The smallest thing
  the recursion computes: ∅ with a point laid in, so the insertion
  clause applies at exactly one step, over the one finiteness rule that
  carries no premise of its own.

- **`CardDelete`** — removing an element costs the count one when the
  set held it and nothing when it did not. The two branches are not two
  cases of one argument. Where the set held it, the content is the
  recursion clause read backwards; where it did not, there is no
  recursion at all — the deletion is the identity.

- **`CountsOneMore`** — a finite set counts one more than what remains
  when one of its members is removed. It is card's insertion clause read
  backwards, stated on its own because four theorems here, and the
  inversion count of the determinant chapter, cite it. Stating it as a
  SUCCESSOR is the
  whole point — `CardDelete` says the same computation in truncated
  subtraction, which says as much only once the set is known to hold
  something, so anything counting upwards would have to argue its way
  back.

- **`InsertCountsOneMore`** — putting into a finite set an element it
  does not already hold raises the count by exactly one. card's clause
  answers an insertion with a CONDITION; a proof that has just laid in a
  point the set did not have already knows which side it is on, and
  wants that side alone as an equation. This is that side, projected
  once rather than re-derived. `CountsOneMore` above is the same
  statement read at a REMAINDER, so the deletion direction is a
  consequence of this one rather than a second projection.

- **`InsertCountsAtMostOneMore`** — laying a point in raises the count
  by at most one, new or not. The exact form has to be TOLD the point
  was absent, and a counting induction is rarely in a position to say
  so — the point arrives from wherever the induction found it. Carrying
  a bound and wanting a bound back, such a proof needs the inexact
  answer, so this member splits on the condition instead of assuming it
  away and holds each side against the bound.

- **`countsAtLeastOne`** — a finite set counts at least one exactly when
  it has a point. `CardEqZero` read against a BOUND rather than against
  a value, which changes nothing about what is known and everything
  about what can be done with it: a proof that has just bounded a count
  from below holds a number and wants a point. Three members of the
  image group take that step, and they take it here.

- **`CardUnion`** — two finite sets sharing no element are counted by
  adding their counts. This is where counting becomes ARITHMETIC: the
  count of a construction as an expression in the counts of its parts,
  with disjointness precisely the price of the `+`. The argument is the
  recursion run to exhaustion, one element at a time off the left set,
  and the whole of the work is showing that an element new to that set
  is new to the union as well — which is where the disjointness is
  spent.

- **`countsSubsetAndRest`** — a finite set's count splits at any subset
  into that subset's count and the count of what the subset leaves.
  Also the chapter's own, and the union count read at the one
  decomposition every subset supplies for free: a subset and the part
  outside it cover the set between them and meet nowhere, so the two
  conditions the union count asks about its operands are supplied by
  the split rather than assumed. That is what turns a statement about
  two unrelated sets into a statement about one set and a subset of
  it — and it is where the comparison theorems begin.

- **`countsLeftAndSurplus`** — the same split read at a subset that
  costs nothing to find. A set lies inside its own union with anything,
  so a union's count is the left operand's plus the count of the
  surplus the union holds beyond it — and that surplus, being what a
  union has that its left operand does not, came from the right one.
  Also the chapter's own. It states the two facts together because
  they are always wanted together: the equation alone leaves the
  surplus an unknown quantity, and it is the containment that ties it
  back to the set the theorem is about. `CardUnionLe`,
  `DisjointIffCountsAdd` and `CardUnionMinusOverlap` all open with it,
  which is what makes those three one construction read three ways
  rather than three parallel arguments.

### Having a SIZE

`has_size(s, n)` abbreviates `finite(s) ∧ card(s) = n` — it is not a
characterization established somewhere, it is what the constant means.
So every member here takes that as given and lands back on the calculus.

- **`FiniteHasSize`** — a set has its own count as a size exactly when
  it is finite. The relation is inhabited on precisely the finite sets,
  and where it is inhabited the function is what inhabits it. Read the
  other way it says a count is no evidence of anything: `card(s)` is a
  number whatever `s` is.

- **`CardOfSized`** — a set that has a size is counted by it. Half the
  abbreviation read out, and nothing is established: the size is given
  rather than proved, so the division IS the theorem. It has a name
  because it is the shortest move for a reader holding a size and
  wanting a count, and it is what the chapter's counting members
  actually cite: five of them hold a size they have just proved and take
  its count through here. The three that keep the FINITENESS instead
  cannot — that half of the abbreviation has no member of its own — and
  read their size apart in place.

- **`HasSizeZero`** — size 0 is emptiness. The counting equivalence
  already did this induction, so this member cites it rather than
  re-running it, and adds the one thing counting cannot supply: at
  size 0 the emptiness carries its own finiteness.

- **`HasSizeSuc`** — a set has size `suc n` exactly when it is nonempty
  and deleting *any* member leaves size `n`. The shrinking form: a
  sized set can be taken apart, and the taking apart may start
  anywhere.

- **`HasSizeClauses`** — the growing form. A set of size `suc n` IS a
  set of size `n` with one new element in it. Neither direction comes
  cheaply from the other: recovering this from the deletion form would
  mean supplying the deletion fact for every member at once, which is
  the theorem again.

  Its `suc` clause is two separate facts travelling by different routes,
  which is how the proof is organized: splitting an element **off** a
  counted set is set surgery, done with `delete` and its membership
  laws, with the count carried by the deletion form of the same
  recursion step; putting one **back** never touches the set laws at
  all, being `finite`'s own closure rule beside `card`'s. There the
  whole question is whether the element was already present, and it is
  exactly the assumption that it was not that makes the count rise.

- **`HasSizePair`** — two distinct points make a set of two:
  `a ≠ b ⇒ has_size({a, b}, 2)`.

### Comparing two counts

Everything above reads a count off one set. These read two counts
against each other, or — in the last of them — a count against a
numeral. They fall into three strands, and the whole of the first rests
on `countsSubsetAndRest`.

- **`CardSubset`** — a subset of a finite set has no more elements than
  the set does. The bound comes out of an equation rather than out of
  comparing the two sets element by element: split the containing set at
  the subset, and a summand never runs past its sum.

- **`CardSubsetEq`** — and a subset carrying the whole of that count IS
  the set. This is where a count stops being a lossy summary. Laid
  inside a set it is exactly as large as, a subset has nothing left to
  be smaller by: the remainder costs nothing, a finite set counted 0 is
  empty, and a set with nothing outside a subset of it is that subset.

- **`CardSubsetLe`** — the same conclusion off a weaker hypothesis. A
  containing set that counts no MORE than its subset is pinned between
  that bound and this one, so the counts agree and the previous member
  finishes it.

- **`SubsetEqIffSameCount`** — and those close into an equivalence:
  under a fixed finite container, carrying the same count and being the
  same set are one condition. Its two directions cost wildly different
  things — one IS the theorem above, the other is congruence — which is
  the point worth recording.

Then the same three-way shape over STRICT containment, where the
asymmetry is starker still.

- **`PsubsetOfDifferentCount`** — containment is STRICT as soon as the
  two counts fail to agree. The odd member of the comparison group, and
  the only one of them carrying no finiteness hypothesis, because it
  never counts anything: `card` occurs in it only as a function, so counts that
  differ belong to sets that differ and the rest is congruence. Whether
  either count is the number of elements of its set — which is what
  finiteness would buy — is never asked.

- **`CardPsubset`** — the converse, and it is the expensive direction
  exactly as that suggests: getting a count inequality OUT of strict
  containment means actually counting, so finiteness returns and the
  containment strand above is what pays for it.

- **`PsubsetIffFewerElements`** — the equivalence over those two. It
  spends one law neither implication spends, reconciling the strict
  order the headline states with the disagreement the converse asks
  for; and its antecedent is the join of what the two sides separately
  need, with neither side needing both.

- **`AtMostOneIffInSingleton`** — the bottom of the scale, and the
  chapter's only member that compares a count against a numeral rather
  than against another count. A finite set with at most one element is
  empty or a singleton, and either way sits inside some singleton;
  conversely a subset of a singleton is finite and counts at most one.
  The forward direction splits on whether the count is zero: at zero the
  set is empty and the existential costs nothing at all — no point has
  to be named, because the residual asks for an element the set does not
  have — and above zero the count is exactly one, which is a size, and a
  size hands the element over.

### Counts under union and difference

The calculus proves that counts add over a union of two sets that meet
nowhere. That single fact is spent ten ways, and nothing in this group
is a new phenomenon — seven readings keep the union, `CardLeDiffAdd` reads
its bound at a cover, and two drop it and keep the split that underwrites
it.

- **`CardOfDisjointParts`** — the law read as a DECOMPOSITION. There the
  union is built and then counted; here a set arrives under a name of
  its own together with a way it comes apart, which is the form the law
  is actually cited in. The decomposition is spent twice and in opposite
  directions: downwards it carries finiteness from the whole to the
  parts, upwards it puts the count back onto the whole.

- **`CardOfPredicateParts`** — the decomposition a predicate makes. A
  finite T comes apart into the points where P holds and those where it
  fails, and the two counts add up to card(T).

- **`HasSizeUnion`** — the same statement carrying its finiteness with
  it. Having a size splits along the `finite ∧ card` seam, and each half
  goes to the law that already answers it. Disjointness is stated as
  `disjoint` and wanted as an empty intersection; those are the same
  thing by definition, so one unfold is the whole bridge.

- **`CardUnionLe`** — the disjointness dropped and the equation weakened
  to a BOUND. The two changes are one change: an element of both sets is
  paid for twice on the right and once on the left, and the overlap is
  never measured — it is precisely what the inequality allows to be
  wasted.

- **`CardLeDiffAdd`** — that bound read at a cover. A set whose remainder
  after deleting a finite set is finite was finite itself, and counts at
  most the remainder plus the deleted set. Nothing asks the deleted set
  to lie inside, which is why this is a bound and not `CardDiff`'s
  equation: putting the deleted set back covers the set, and the cover
  is a union of two finite sets.

- **`OverlapOfShortUnion`** — that bound read backwards. A union
  counting SHORT of the sum has already ruled out disjointness. How far
  short is never asked, which is why the conclusion is a bare
  non-emptiness rather than a bound of its own.

- **`DisjointIffCountsAdd`** — the equivalence those two were the halves
  of. Its hard direction forms no difference at all: splitting the union
  at the first set and cancelling leaves a surplus counting exactly as
  much as the second, and a subset carrying a finite set's whole count
  IS that set. The three members around it never FORM a difference; this
  one goes further and never states one, where its obvious route runs
  through the correction below.

- **`CardUnionMinusOverlap`** — instead of weakening, correcting. The
  sum overshoots by exactly the overlap, which is two-set
  inclusion–exclusion.

- **`CardDiff`** — the split solved for the remainder. On ℕ that is a
  condition rather than a formality: `card(s) - card(t)` behaves only
  once `card(t)` is known not to run past `card(s)`, and containment is
  what buys it. But the guard is never established as a fact of its
  own, because the split has already presented the whole's count as
  something the subset's count was ADDED to — and what addition adds,
  monus takes back with nothing asked about the size of either summand.
  So the proof never subtracts, never bounds, and never compares two
  counts; containment does its work by making the split available.

- **`HasSizeDiff`** — again the size-carrying package. Only the larger
  set's finiteness is ever spent; containment supplies the rest, so the
  second size hypothesis is present entirely for the number it carries.

### Counting a union of a family

The section above counts a union of two sets. When a whole finite family
of sets meet pairwise nowhere AND all have one size, the count of their
union is still a product, and needs no Σ.

- **`HasSizeUnions`** — blocks of m elements, pairwise disjoint and
  finitely many, have a union of m · card(P) elements. The induction
  runs over the sub-families of P rather than over arbitrary families,
  so the two hypotheses on the blocks stay facts about P, read at
  whichever blocks the step meets; each step lays one new block in, and
  `HasSizeUnion` adds its m. This is the counting step of Lagrange's
  theorem (`algebra/group/group`), where the blocks are the cosets of a
  subgroup.

### Counting under a map

`card` is a lossy summary and a map is a second source of loss. Seven of
these eleven say how much: a count can only fall under a map, and it falls
exactly where the map identifies two points. The last four ask a
different question and form a strand of their own at the end of the
group.

- **`CardImageLe`** — a map never sends a finite set onto more points
  than the set has. It asks nothing of the map, which is what lets every
  coincidence go unaccounted for: the bound is claimed, never an
  equation. `finite_set.FiniteImageEqInj` chooses a subset on which
  the map is injective and which has the same image. `CardImageInj`
  counts that image as the subset, and `CardSubset` bounds it by the
  original set.
- **`CardImageInj`** — rule coincidence out and the loss disappears: a
  map that separates a finite set's points sends it to a set of the same
  size. By induction, and the separating hypothesis is spent in
  exactly one place, the step, where the added point's value must be
  shown NEW to the image so that both counts rise together. The property
  carries the separation as its own hypothesis rather than assuming it
  once outside, because the induction reaches its set through sets that
  are not subsets of it.
- **`SameCountIffInjective`** — the two above, closed into a test: the
  image counts the same exactly when the map separates. The hard
  direction runs the loss backwards. If two points merged, one is
  redundant — dropping it leaves the image untouched — so the source
  counts no more than what remains when a point is removed; but a subset
  of a finite set whose count does not fall short IS that set, and the
  dropped point is then a point the set both has and does not.
- **`CardOfUniquePreimages`** — the same equation from a hypothesis about
  a TARGET set instead of about the map: every point of `t` has exactly
  one preimage in `s`. The condition does double duty and separating its
  halves is the whole proof. Existence puts `t` inside the image and the
  containment puts the image inside `t`, so the two sets are one;
  uniqueness IS separation, read directly.
- **`CardImageSameFibres`** — two maps with the same fibres on a finite
  set have images of one size: each image is in one-to-one correspondence
  with the fibres.
- **`HasSizeImageInj`** and **`HasSizeImageInjEq`** — the same question
  at `has_size`, in one direction and as the equivalence. Both take the
  chapter's cheapest move: a size unfolds into a finiteness and a count,
  and each half then goes to the law that answers it — though both draw on
  the source's finiteness, which the counting law asks for and, in the
  equivalence, only the finiteness half can supply. That equivalence needs
  no case split at all, because an equation between counts has no
  direction: one instance answers both halves.

- **`ExistsSmallSubsetImageInj`** — the seventh, and it asks about
  EXCHANGE rather than about loss. The parent chapter already trades a
  finite subset of an image for a finite subset of the source, carrying
  an arbitrary property of the image-side set across with it. Add a size
  bound to both sides and the bound is not a second thing to transport:
  read that exchange at the property "P, and with fewer than n points"
  and it travels as part of P, by the one instance. What comes back is a
  bound on the image's count rather than the source's, and the equation
  above — a map that separates a set counts it exactly — converts it,
  which it may because the exchange hands back a set the map does not
  fold.

- **`ExistsSmallSubsetImage`** — the same exchange with nothing asked of
  the map. Dropping injectivity costs arithmetic rather than saving it:
  without a separating map the count fact is an inequality
  (`card(image(f, u)) ≤ card(u)`) where the member above has an equation,
  and composing `≤` with `<` is order reasoning the refuter does not do.
  It is the one member of this file that spends a capability, and that is
  why.

- **`ForallSmallSubsetImage`** and **`ForallSmallSubsetImageInj`** — the
  two above read at a negated property. Each is one cite: a statement
  about every small subset is a statement about none satisfying the
  negation, and the ∃-law already transports that. Their proofs are two
  lines and their shaping is opposite — worth knowing only if you are
  reading the code, where each says which flags it needed and why.

### Bounding a count

The groups above relate counts to each other. These relate a count to a
NUMBER standing over it, which is the form a consumer actually carries a
finite set around in: shown finite once, counted under some n, and then
used at whatever sits inside it or is reached from it.

The two directions here are not converses. A bound is INHERITED downward
without being recomputed, and — the harder statement — a bound is
REALIZED, by a subset of exactly the size asked for.

- **`BoundedCountOfSubset`** and **`BoundedCountOfImage`** — a bound
  descends along containment, and across a map. In both, the two halves
  of the conclusion travel by separate laws and meet nowhere: finiteness
  crosses on its own, and the ceiling crosses by composing the count's
  own bound with the one assumed. Nothing about n is recomputed.

- **`ChooseSubsetStrong`** — a set has a subset of every size its count
  leaves room for. By induction on the size asked for: at zero the empty
  set answers, and each step takes one point out, hands what is left to
  the induction, and puts the point back. It is the STRONG form because
  the size condition is an implication rather than a conjunction, so a
  set with no count discharges it vacuously and is asked for a subset of
  every size at once — which is why nothing in the proof branches on
  finiteness. The counting is a successor rather than a difference, and
  that is what keeps the whole argument free of subtraction.

- **`ChooseSubset`** — the same law read at a set that HAS a count. The
  strong form guards its conclusion by an implication so that a set with
  no count discharges it vacuously; that is what makes it strong and also
  what makes it awkward to cite, and the whole of this member is that a
  conjunction implies the implication.

- **`SubsetOfSizeIffLargeEnough`** — the two directions closed into one
  equivalence, which turns the realization from a sufficient construction
  into an exact characterization. Its converse half never counts
  anything: a size is an equation between a number and a count, so a
  bound on the count becomes a bound on the number by substitution.

- **`ChooseSubsetBetween`** — the same size asked for with a set already
  in hand that the answer must contain, so the choosing happens not in
  the ambient set but in what it holds beyond the one given, and the
  answer is assembled rather than found. The shortfall is obtained as a
  witness — a `d` with `n = card(s) + d` — rather than computed as
  `n - card(s)`, so no subtraction appears anywhere and no truncation
  guard is needed.

### Counting by matching

Everything above reads a count off a set. These read a count and a map
against each other — building a map from two counts, laying one set
inside another when the counts only compare, carrying a size along a
matching already given, and reading off what a map has no room left to
be.

- **`SurjectiveIffInjectiveGen`** — the finite pigeonhole principle.
  Between finite sets of equal size, a map that stays inside its target
  reaches all of it exactly when it separates the points of its source.

  Both halves count, in opposite directions. *Onto from separating*: a
  map that separates the points of `s` produces an image with exactly
  `s`'s count; the target has that count too and contains the image, and
  a subset carrying the full count is the whole set. *Separating from
  onto*: if `f` folded two points together, one could be dropped and the
  map would still reach everything — but the smaller set is one point
  short, and no set is reached from fewer points than it has. The second
  half needs neither the target's finiteness nor the containment, and
  the proof states only what it spends.

- **`CardEqBijection`** — the converse construction, and one of the two
  places in the chapter where a count is SPENT rather than read. Two finite
  sets of the same count are matched point for point, and the matching
  is built rather than found: pair the sets off one element at a time,
  checking only that removing a matched pair leaves two sets that still
  count the same. The recursion supplies that check and nothing else is
  needed — in particular no choice principle, since the partner comes
  from the target being non-empty, which its count being a successor
  already says.

- **`MutualInversesHasSize`** — a size crosses a pair of maps that undo
  each other. This is the only member in the chapter that reads no
  finiteness at all: `has_size` stays folded from beginning to end,
  because the law it ends on is already stated at a size. The hypothesis
  does two unrelated jobs and separating them is the whole proof — read
  forwards it identifies the target as the source's image, read
  backwards it makes the map injective, and only then does a count enter.

- **`SurjectiveIffInjective`** — the pigeonhole on a single set. A map
  of a finite set into itself has nowhere to put a repetition: it is
  sending as many points as it has places to fill. Taking the target to
  be the source discharges two of the general law's four hypotheses —
  the equal counts become reflexivity, the target's finiteness is the
  source's — so the member is one citation.

- **`ImageImpInjectiveGen`** — the same principle read off an image
  rather than a containment. When a map carries a finite set exactly
  onto a set of the same count, that one set equality supplies both of
  the things the general law asks for that the statement does not: the
  ontoness is its right-hand side, and the target's finiteness follows
  from the source's through the image. What is left is the pigeonhole.

- **`CardEqMutualInverses`** — the construction read in both
  directions. The same equal counts that give a map into, onto and
  separating give that map an inverse, and the inverse costs nothing
  extra: onto-plus-separating already says that each point of the
  target has exactly one preimage. So the proof never builds a second
  map. It states the preimage assignment as one total claim — every
  point of the target type has a preimage, vacuously off the target —
  and lets that statement be the map. Pushing the existential out from
  under the membership test is the one real move; left inside, the
  fact is inert.

- **`CardLeInj`** — the same idea when the counts only compare. A source
  no larger than its target can be laid inside it: a map that lands in
  the target and keeps the source's points apart, with no claim that it
  reaches everything. `ChooseSubset` selects a subset of the target
  with exactly the source's size; `CardEqBijection` matches the source
  to that subset. Including the subset in the target gives the
  required injection.

- **`MutualInversesHasSizeEq`** — the transport read in both
  directions, which is the transport twice. The hypothesis is symmetric
  in the two sets and their two maps, so the reverse reading is the
  same law with the roles exchanged — an exchange of types as well as
  of terms, since the two sets are drawn from different ones. The
  equivalence is never split: one premise list carrying both readings
  closes it.

- **`MutualInversesCard`** — the transport read at counts, and the
  converse of `CardEqMutualInverses`. A finite source has the size it
  counts; the transport carries that size across the pair, and a size at
  the target is its finiteness together with its count.

- **`ImageImpInjective`** — the image law on a single set, the
  companion to `SurjectiveIffInjective` above. Read at one set the
  general law stops weighing two counts against each other, because
  the counts it asks to agree are one count; what remains of its
  hypotheses is what the statement already assumes.

### Counting a set of pairs

Every group above counts ONE set. This one counts a set of PAIRS: draw a
first coordinate from a base set, and a second from a set that may
depend on which first coordinate was drawn. The count is the product of
the two sizes — as many rows as the base has points, each row as long as
that point's fibre.

The dependent form is the general one and is proved first. Nothing in
its argument needs the fibre to be the same set at every point, only
that every point's fibre has the same SIZE; the other two members are
that theorem read back at a fibre held still — the product
`set_cross(s, t)` of `sets/set_product` — and then at counts instead of
sizes.

- **`HasSizeProductDependent`** — a base of size m whose every point has
  a fibre of size n spans m · n pairs.

  The induction runs on the base's SIZE rather than on the base. A set
  of size `suc m` IS a set of size m with one further point put in from
  outside it — that is `HasSizeClauses`, and taking the recursion in
  that form means the step never has to argue that the point it adds is
  new, nor to compute anything from `card`'s own recursion.

  At each step the enlarged rectangle splits in two: the pairs whose
  first coordinate is the new point form that point's row, which is its
  fibre carried across by the pairing and so counts what the fibre
  counts; everything else is the rectangle the old base spans, counted
  by the induction hypothesis. The two are disjoint because a pair's
  first coordinate cannot be both the new point and one of the old ones,
  so the counts add — m · n and one further n, which is what (m+1) · n
  is. At the base of the induction a set of size 0 is empty outright, so
  the rectangle over it is empty and 0 · n is 0.

  Two points may have literally the same fibre or disjoint ones; the
  rows they contribute are disjoint either way, because it is the FIRST
  coordinate that separates them.

- **`HasSizeProduct`** — the product `set_cross(s, t)` of two sets of
  known size has the product of their sizes.

  Opened by its definition, the product is the rectangle over `s` whose
  every fibre is `t`, so this is the member above at a fibre that does
  not vary: hand every point of the base the same second set. A
  constant fibre meets the dependent law's condition for the trivial
  reason — there is one fibre, and it has the size it has — so the
  general theorem specialises to this one with nothing left over, and
  the constant map is the entire proof.

- **`CardProduct`** — the product `set_cross(s, t)` of two finite sets
  holds as many pairs as their counts multiply to.

  The same fact said with counts instead of sizes, and the translation
  is all that happens. A finite set has its own count as a size, so each
  side supplies one; the product law returns a size for the rectangle
  they span; and being a size IS being finite and counting it, which is
  what `has_size` abbreviates rather than a theorem about it. So the
  member reads the count off that size by citing `CardOfSized`, which is
  where that reading is stated, and the rectangle's finiteness — which
  the headline does not ask for — is simply not taken.

The rectangle's count has one more reading: a two-place map that tells
its argument pairs apart takes as many values on s × t as there are
pairs.

- **`HasSizeProductImage`** — `has_size(s, m) ∧ has_size(t, n)` and `f`
  separating argument pairs give `has_size({f(x, y) | x ∈ s ∧ y ∈ t},
  m · n)`. The values are the rectangle's image under `f` read at a
  pair's two coordinates, which separates the rectangle's pairs; it is
  the step that counts the permutations of a finite set
  (`algebra/group/symmetric_group`).

### How many maps a finite domain admits into a finite codomain

A function space is the set of maps from one set into another, pinned to
a default value off the domain — the pinning is what makes it a SET of
the right size, since off the domain a map is otherwise free. The count
is the codomain's size raised to the domain's: each point of the domain
chooses among the codomain's values independently.

- **`HasSizeFunspace`** — the maps from a finite `s` into a finite `t`
  number `|t|` raised to `|s|`. One induction on the DOMAIN's size, and
  its step is a bijection: a map from one-more-point splits into its
  value at the new point paired with its truncation to the old domain,
  and every such pair is assembled back by answering the one at the new
  point and following the other elsewhere. So the enlarged funspace
  stands in size-preserving correspondence with `t ×` the smaller
  funspace, the product law of the group above counts the pairs, and
  `nat_pow`'s successor clause absorbs the factor. At the base, pinning to
  the default forces every value, one map remains, and `n⁰` is 1.

- **`funspaceHasSizeAtCounts`** — the law above read at the counts two
  finitenesses supply. A finite set has its own count as a size, so at a
  pair of finite sets the sizes are theirs to give. Internal, and stated
  only because the next two members are its two halves: writing it once
  is what keeps them from proving the same thing twice.

- **`CardFunspace`**, **`FiniteFunspace`** — that size read as a count,
  and read as a finiteness; neither runs the induction again. A size IS
  finiteness together with a count, and the two halves are taken
  differently: the count is what `CardOfSized` states, so this one cites
  it, while the finiteness has no member of its own and is read apart in
  place. The two are one theorem, divided.

### How many points a whole type holds

The group above counts a set carved out of a type. This one counts the
type itself, which is what a function space over `𝕌` needs to read its
base off.

- **`HasSizeBool`** — there are exactly two booleans. `𝕌` at `bool` is
  `{⊥, ⊤}`, so the count is the insertion clause read once over a
  singleton: `⊥` is not in `{⊤}`, so laying it in costs one, and a
  singleton counts one.
- **`CardBool`**, **`FiniteBool`** — that size read as a count, and read
  as a finiteness. The two truth values are laid out once, above; these
  two divide what laying them out proved, exactly as `CardFunspace` and
  `FiniteFunspace` divide the funspace's size.

- **`HasSizeFunspaceUniv`** — where a domain type and a codomain type
  each hold finitely many points, so does the function type between
  them, and it holds the codomain's count raised to the domain's. The
  funspace law of the group above, read where both sides are whole
  types: over `𝕌` there is no point off the domain, so the default that
  law pins its maps to constrains nothing and the set it counts is the
  function type entire. No default is ever chosen — both halves are
  stated FOR EVERY default, and it is their meeting that leaves a
  statement with no default in it.
- **`funspaceUnivHasSizeAtCounts`** — that law read at the counts the two
  finitenesses supply. A finite type's universe has its own count as a
  size, so where both types are finite the sizes are theirs to give.
  Internal, and stated only because the next two members are its two
  halves: writing it once is what keeps them from instantiating the same
  law twice.
- **`CardFunspaceUniv`**, **`FiniteFunspaceUniv`** — that size read as a
  count, and read as a finiteness. Neither runs anything, and they
  divide the size exactly as `CardFunspace` / `FiniteFunspace` do a
  group earlier: the count half cites `CardOfSized`, the finiteness half
  reads the abbreviation apart in place.

### How many subsets a set has

The groups above count a set built out of two others, or the points a
type holds. This one counts what ONE set generates: the sets lying
inside it. The answer is a power, and the reason is that a subset IS a
map — choosing one means answering a yes-or-no question at each point
of the set, which is exactly a map into the truth values, saying
nothing about the points outside. So the count is two raised to the
size, and the group above has already done the counting.

- **`HasSizePowerset`** — a set of size n has 2ⁿ subsets. Containment
  in `s` is a pointwise condition — `t ⊆ s` says `t` answers ⊥ wherever
  `s` does — and that is precisely the condition pinning a map off `s`.
  So the powerset is the set of maps from `s` into the truth values
  pinned to ⊥ outside it: an identity about membership and containment,
  with no count in it anywhere and no subset exhibited to see it. From
  there the function-space law counts those maps, and the two points of
  `bool` are counted beside it. Nothing is asked of `s` but its size.
- **`CardPowerset`** — the same fact read as a count. A finite set has
  its own count as a size, so its finiteness supplies the size the law
  above is read at, and `CardOfSized` reads the count off what comes
  back. The finiteness is not taken, and losing it costs nothing: the
  parent chapter states it as `FinitePowerset`, by an induction that
  never counts.

## What is not here

The count of a union of many sets of DIFFERENT sizes. Where the members
of a family of sets meet pairwise in nothing, the points of `⋃s` number
the SUM of their counts — a Σ indexed by the family, not the `+` of the
additive part above — so the statement cannot be written in this
chapter's vocabulary at all. It is a theorem about finite sums that
happens to be about counting, and the place to look for it is where Σ
over a finite set lives, `iterate/nat/nat_sum`. Only when the blocks share
one size does the sum collapse to a product, and that case is here
(`HasSizeUnions`).

Two of the facts the chapter reaches for outside it are worth naming,
not because the edge is unusual — the chapter cites ℕ's arithmetic and
order, the set chapters and the pair chapter throughout — but because a
reader may expect to find them here. `finite_set.FoldExists` is where
the fold's well-definedness is established, and this chapter
deliberately does not restate it; `nat_monus.SucSubOne` supplies the one
`suc(n) - 1` step, in `CardDelete`.

## Reading the code

The dependency direction is one-way: `cardinality` imports `finite_set`,
never the reverse, so the package's blank import lives in `sets/sets.go`.

The proof files follow the groups above. `counting.go` carries where
counting comes from — the fold, its two readings at an insertion and at
a deletion, what it does not depend on, the two readings for a step
closed only on a set, and the clauses it gives card —
the calculus with the chapter's own statements, the size layer, the
comparisons, and the union and difference counts. `maps.go`
carries what a shared count and a map force on each other, the counts
under a map (and the four card-bounded exchanges that follow them), and
a count against a number standing over it. `constructions.go` carries
the counts of a built set: a set of pairs, a function space, a whole
type, and a powerset. `vocab.go` holds what is chapter-wide
rather than proof-specific — the counting names, why `set_tac` cannot
close a cardinality statement even though it closes steps inside one,
and the pointwise fold that explains where `Normalized` appears.

| Member | Statement |
|---|---|
| `TaggedCopySize` | Tagging a sized set by a fixed boolean keeps its size |
| `TaggedUnionCount` | Tagging two finite sets by false and true adds their sizes |
| `BoundedFiniteSubsets` | A set whose finite subsets all have at most n points is finite with at most n points |
