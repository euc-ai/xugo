# cardinal — comparing the sizes of sets

`finite_set` measures a finite set by counting it: `card(s)` is a
number, and two finite sets compare as their numbers do. That stops at
the finite. This chapter compares sizes the way that does not stop:
one set is no larger than another when it can be sent into it without
two of its points landing together, and two sets are the same size when
a map joins them point for point. Nothing is counted, and nothing needs
to be finite; the map is the whole content of the comparison.

The sets compared may live in different types — ℕ against ℝ, a set
against the set of its subsets — so every relation here is stated at
two element types, and a law takes a separate element type for each set
it compares, unless its statement ties them (an inclusion `s ⊆ t`, a set
against its own subsets).

## The comparisons

    card_le(s, t)   some f sends s into t, identifying no two points of s
    card_eq(s, t)   some f is injective on s and carries s onto t
    card_lt(s, t)   card_le(s, t) and not card_le(t, s)
    countable(s)    card_le(s, 𝕌⟨num⟩)

`card_eq` asks for a bijection of `s` onto `t` and says it in the two
clauses a reader checks: that no two points are identified, and that
the points of `s` go exactly onto `t`. `card_lt` is the strict part of the preorder,
not "an injection that is not onto": `n ↦ n + 1` sends ℕ into itself and
misses 0, and ℕ is not smaller than itself.

A set is countable when it is no larger than ℕ — when its points can be
tagged by naturals, distinct points by distinct tags. Finite sets are
countable, and so is ℕ itself.

## The order

`card_le` is a preorder: the identity sends a set into itself
(`CardLeRefl`), and one injection followed by another is an injection
(`CardLeTrans`). A subset is no larger than a set containing it, by the
identity again (`CardLeSubset`).

`card_eq` is an equivalence. The identity is a bijection of a set onto
itself (`CardEqRefl`); a bijection f of s onto t has a two-sided inverse
g on t, which identifies no two points of t, since f undoes it, and
reaches each x of s at f(x) (`CardEqSym`); and one bijection followed by
another is a bijection (`CardEqTrans`). A bijection is in particular an
injection (`CardEqImpLe`).

The strict order composes with the preorder on either side
(`CardLtLeTrans`, `CardLeLtTrans`): `s ≤ t ≤ u` puts `s` below `u`, and
`u` below `s` would reverse the strict step — t ≤ u ≤ s in the first
law, u ≤ s ≤ t in the second.

Being no larger is also a statement about maps going the other way
(`CardLeCover`): s is no larger than t exactly when some map from t
covers s. A left inverse of an injection covers the set it injects, and
choosing one source for each covered point is an injection back; both
directions choose. This surjective reading is how the rest of the
chapter speaks: Cantor's theorem reads it forward (an injection gives a
covering map, which the diagonal refutes), countability reads it both
ways (a set is countable exactly when a sequence covers it), and read
backward at a map's own image it says the image of a set is no larger
than the set (`CardLeImage`): the map itself covers its image.

Sizes multiply under the cartesian product (`CardLeProduct`): an
injection on each side, applied componentwise, injects the pairs.

In a type A whose pairs inject into it, a set L strictly smaller than A
leaves room for all of A outside it (`ComplementRoom`): a coding of the
pairs splits A into blocks, one copy of A for each first coordinate x,
and some block misses L, since a point of L chosen in each would inject
A into L.

## Schröder–Bernstein

Two sets each no larger than the other are the same size. The argument
has one piece of mathematics beyond bookkeeping: a set u of s fixed by
X ↦ g(t ∖ f(s ∖ X)), where f injects s into t and g injects t into s.
Given it, the map h that follows a left inverse k of g on u and f off u
is a bijection of s onto t (`SchroederBernsteinBijection`). The fixed
point is read as the two inclusions it is — g carries into u the points
of t that f does not reach from s ∖ u, and every x of u is g(k(x)) with
k(x) such a point — so h sends u onto the part of t that f misses from
s ∖ u, and s ∖ u onto the part f reaches: two disjoint parts covering t.
The one delicate step is injectivity across the pieces: a point of u
lands outside f(s ∖ u), a point of s off u inside it, so two points with
one image lie on the same side of u; there g undoes h on u, and f is
injective off it.

The fixed point comes from Knaster–Tarski (`SchroederBernstein`,
`set_order.KnasterTarski`): X ↦ g(t ∖ f(s ∖ X)) is monotone — a larger X
leaves less of s ∖ X for f to reach, and so more of t for g to carry —
so it fixes u, the intersection of the sets it shrinks. Conversely a
bijection and its inverse are injections both ways, so the two sets are
each no larger than the other.

## Cantor's theorem

A set is strictly smaller than the set of its subsets (`CantorStrict`).
One half is an injection: `x ↦ {x}` sends `s` among its subsets and
identifies nothing, since `{x} = {y}` puts `x = y`. The other half is
Cantor's diagonal argument. Were the subsets no larger than `s`, the
comparison's surjective reading (`CardLeCover`) would give a map `g` from
`s` covering every subset of `s`; but the functions chapter's `Cantor`
exhibits a subset of `s` — the points `x` of `s` that `g(x)` does not
contain — which `g` reaches at no point of `s`. Read at the whole of a
type (`CantorUniv`), where every set is a subset of 𝕌: the sets of A's
outnumber the A's — the form `real_cardinality` reads at ℕ.

## Countable sets

A set is countable when it is no larger than ℕ, and — reading the
comparison surjectively — exactly when some sequence runs through all
of it (`CountableCover`). ℕ is countable by the identity
(`NumCountable`); a set no larger than a countable one is countable
(`CardLeCountable`), so a subset of a countable set is
(`CountableSubset`); and ∅ is, vacuously (`CountableEmpty`).

The pairs of naturals are countable (`NumPairCountable`): the pairing
function `num_pair(x, y) = 2ˣ·(2y + 1)` of `datatypes/datatype_universe` tags each
pair by a natural, and no two pairs share a tag, because equal tags have
equal components and a pair is the pair of its components. They are as
many as the naturals (`PairNumBijection`): `n ↦ (n, 0)` sends the
naturals among the pairs, identifying none of them, and Schröder–Bernstein
joins it to the tagging.

A finite set is countable (`FiniteCountable`): some f lists it on the
positions 1 .. card(s), and since those positions are naturals, f run
over all of ℕ already covers it. A nonempty countable set is not merely
covered by a sequence but is exactly the range of one
(`CountableEnumeration`): take a point a of s and a sequence e covering
s, and keep e(n) where it lies in s, putting a in its place elsewhere —
every value is then a point of s, and each point of s, being some e(n),
is still reached at n.

The image of a countable set under any map is countable
(`CountableImage`): a sequence e running through s, followed by f, runs
through image(f, s), because the image of ℕ under f ∘ e is f's image of
e's values, and those values hold s.

The product `set_cross(s, t)` of two countable sets is countable
(`CountableProduct`): sequences e₁ and e₂ covering them give the map
(i, j) ↦ (e₁(i), e₂(j)) on ℕ × ℕ, whose image is countable, being the
image of a countable set, and contains every pair (e₁(i), e₂(j)); a
point of the product has its components in s and t, so is such a pair,
and the whole product lies in the image.

A union of two countable sets is countable (`CountableUnion`):
the family `{s, t}` is finite, hence countable, and both its members
are countable. `CountableUnions` applies to that family, whose union
is `s ∪ t`.

A countable union of countable sets is countable (`CountableUnions`).
With no sets the union is empty. Otherwise F is the range of a sequence
e (`CountableEnumeration`), and each e(i), being a member of F, is
covered by a sequence. Choosing one such cover C(i) for every i at once
is the argument's one use of choice, and it indexes the union by pairs
of naturals: a point of e(i) is C(i, j) for some j. So the union lies in
the image of ℕ × ℕ under (i, j) ↦ C(i, j), and that image is countable
because the pairs of naturals are.

The finite subsets of a countable set form a countable set
(`CountableFiniteSubsets`). Every finite subset of a sequence's range
lies in the image of some finite initial segment. Each such finite
image has finitely many subsets, so their union over the natural
indices is countable. The functions that differ from a fixed function
`a` at finitely many points of a countable set `J`, each changed value
drawn from a countable set `C(i)`, are countably many
(`CountableFiniteModifications`): each is fixed by its graph on the
points where it differs from `a`, a finite subset of the countable
`J × ⋃image(C, J)`.

## Members

The comparisons:

| entry | statement |
|---|---|
| `CardLeDef` | `card_le(s, t) ⇔ ∃f. (∀x. x ∈ s ⇒ f(x) ∈ t) ∧ injective_on(s, f)` |
| `CardEqDef` | `card_eq(s, t) ⇔ ∃f. injective_on(s, f) ∧ image(f, s) = t` |
| `CardLtDef` | `card_lt(s, t) ⇔ card_le(s, t) ∧ ¬card_le(t, s)` |
| `CountableDef` | `countable(s) ⇔ card_le(s, 𝕌⟨num⟩)` |

The order:

| entry | statement | argument |
|---|---|---|
| `CardLeRefl` | `card_le(s, s)` | the identity |
| `CardLeTrans` | `card_le(s, t) ∧ card_le(t, u) ⇒ card_le(s, u)` | g after f |
| `CardLeSubset` | `s ⊆ t ⇒ card_le(s, t)` | the identity |
| `CardEqRefl` | `card_eq(s, s)` | the identity |
| `CardEqImpLe` | `card_eq(s, t) ⇒ card_le(s, t)` | forget that the bijection is onto |
| `CardEqSym` | `card_eq(s, t) ⇒ card_eq(t, s)` | the inverse of the bijection |
| `CardEqTrans` | `card_eq(s, t) ∧ card_eq(t, u) ⇒ card_eq(s, u)` | g after f |
| `CardLtLeTrans` | `card_lt(s, t) ∧ card_le(t, u) ⇒ card_lt(s, u)` | u ≤ s would put t ≤ u ≤ s |
| `CardLeLtTrans` | `card_le(s, t) ∧ card_lt(t, u) ⇒ card_lt(s, u)` | u ≤ s would put u ≤ s ≤ t |
| `CardLeCover` | `card_le(s, t) ⇔ ∃g. s ⊆ image(g, t)` | a left inverse of the injection covers s; one chosen source per point of s is an injection |
| `CardLeImage` | `card_le(image(f, s), s)` | f covers its own image |
| `CardLeProduct` | `card_le(s, s') ∧ card_le(t, t') ⇒ card_le(set_cross(s, t), set_cross(s', t'))` | the two injections componentwise |
| `ComplementRoom` | `card_le(𝕌⟨prod(A, A)⟩, 𝕌⟨A⟩) ∧ card_lt(L, 𝕌⟨A⟩) ⇒ card_le(𝕌⟨A⟩, {x \| x ∉ L})` | the pair coding splits A into blocks, copies of A; one misses L, else a point chosen in each injects A into L |

Schröder–Bernstein:

| entry | statement | argument |
|---|---|---|
| `SchroederBernsteinBijection` | f injects s into t, g injects t into s, `image(g, t ∖ image(f, s ∖ u)) = u` ⇒ `card_eq(s, t)` | k (g's left inverse) on u, f off u |
| `SchroederBernstein` | `card_le(s, t) ∧ card_le(t, s) ⇔ card_eq(s, t)` | X ↦ g(t ∖ f(s ∖ X)) is monotone, Knaster–Tarski gives its fixed point, SchroederBernsteinBijection joins f and g there; conversely CardEqImpLe both ways, via CardEqSym |

Cantor's theorem:

| entry | statement | argument |
|---|---|---|
| `CantorStrict` | `card_lt(s, {t \| t ⊆ s})` | the singletons inject s into its subsets; a map from s covering them is refuted by the diagonal argument |
| `CantorUniv` | `card_lt(𝕌⟨A⟩, 𝕌⟨set(A)⟩)` | CantorStrict at 𝕌, whose subsets are every set |

Countable sets:

| entry | statement | argument |
|---|---|---|
| `CountableCover` | `countable(s) ⇔ ∃f:num → A. s ⊆ image(f, 𝕌)` | CardLeCover at ℕ |
| `NumCountable` | `countable(𝕌⟨num⟩)` | the identity |
| `CardLeCountable` | `card_le(s, t) ∧ countable(t) ⇒ countable(s)` | s ≤ t ≤ ℕ |
| `CountableSubset` | `countable(t) ∧ s ⊆ t ⇒ countable(s)` | a subset is no larger |
| `CountableEmpty` | `countable(∅)` | any map, vacuously |
| `NumPairCountable` | `countable(𝕌⟨prod(num, num)⟩)` | tag a pair by num_pair of its components (`NumPairInjective`, `PairEta`) |
| `PairNumBijection` | `card_eq(𝕌⟨prod(num, num)⟩, 𝕌⟨num⟩)` | n ↦ (n, 0) one way (`PairEq`), NumPairCountable the other; SchroederBernstein joins them |
| `CountableEnumeration` | `countable(s) ∧ ¬(s = ∅) ⇒ ∃f:num → A. s = image(f, 𝕌)` | a point a of s and a covering sequence e; keep e(n) when it lies in s, else a |
| `FiniteCountable` | `finite(s) ⇒ countable(s)` | f lists s on 1 .. card(s) (`FiniteIndex`); those positions are naturals, so f over ℕ covers s |
| `CountableImage` | `countable(s) ⇒ countable(image(f, s))` | a sequence e covering s gives f ∘ e covering image(f, s) (`ImageCompose`, `ImageSubset`) |
| `CountableProduct` | `countable(s) ∧ countable(t) ⇒ countable(set_cross(s, t))` | e₁, e₂ covering s and t; a point of the product, its components in s and t (`set_product.InCrossProjections`, `pairs.PairEta`), is some (e₁(i), e₂(j)), the value at (i, j) of a map on ℕ × ℕ whose image is countable and holds the product |
| `CountableUnion` | `countable(s) ∧ countable(t) ⇒ countable(s ∪ t)` | `CountableUnions` at the finite family `{s, t}` |
| `CountableUnions` | `countable(F) ∧ (∀s. s ∈ F ⇒ countable(s)) ⇒ countable(⋃F)` | F the range of e; a cover C(i) of each e(i), chosen at once; ⋃F inside the image of ℕ × ℕ under (i, j) ↦ C(i, j) |
| `CountableFiniteSubsets` | `countable(s) ⇒ countable({t \| finite(t) ∧ t ⊆ s})` | finite subsets lie in finite initial images of a sequence covering s |
| `CountableFiniteModifications` | `countable(J) ∧ (∀i. i ∈ J ⇒ countable(C(i))) ⇒ countable({f \| finite({i \| f(i) ≠ a(i)}) ∧ (∀i. f(i) ≠ a(i) ⇒ i ∈ J ∧ f(i) ∈ C(i))})` | a function is fixed by its graph where it differs from a, a finite subset of the countable J × ⋃image(C, J) |

## Mechanics

A proof that builds or takes apart the map behind a comparison unfolds
the comparison — at the section root where the whole statement is read
that way (`Opening(Unfold(CardLeDef), …)`: the closure is handed the
map's existence as a fact to `Unpack`, and the goal is the ∃ a `Take`
answers), and at one fact where only a hypothesis is (`a.Unfolded`, as
`SchroederBernstein` does, keeping `card_eq` folded for the core it
cites). A proof that only composes comparisons cites the laws and
unfolds nothing. A definition merely unfolded is not a dependency.

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.

## A powerset index closed under finite-support encoding

### Sequences, pairs, naturals, multiplicities and polynomials over one inner type

Over a single inner type A put `U = set(prod(num, A))`. The natural
coordinate carries the index of a sequence, so the encodings below work
whatever A is, a one-point type included, and U is infinite through
that coordinate. A sequence of subsets is one subset, the n-th written
on the slices paired with n, and so is a pair, (S, T) being the
sequence S, T, T, …. Since U's pairs inject into U, a set of subsets
strictly smaller than U leaves a whole copy of U outside it
(`ComplementRoom` at the type U). A natural beside a subset is a pair
of subsets, n written as `{(n, a) | a : A}`, which inhabitation of A
makes nonempty; read at 0 and at 1 this gives two injections of U into
itself with disjoint images. A finitely supported map from U to ℕ is
the sequence code of its points paired with their values, read along a
sequence that runs through its finite support. A coefficient function
on such maps — nonzero at finitely many of them, and only at finitely
supported ones — is again its finite
graph, once the coefficients it takes off its zero lie in a set C that
has room in U: at C a ring's carrier the set holds the ring's
polynomials whose variables are the points of U, and the room asked is
the carrier's, not its type's.
The finite supports are written `finite(fun_support(0, m))` for
multiplicities and `finite(fun_support(zero, f))` for coefficients;
`fun_support` records where a function differs from its default value.

Finiteness is load-bearing at each level. Every subset of U gives the
map with value 1 on it, so all maps from U to ℕ outnumber U (Cantor's
theorem); and without the finite support of the maps that carry a
coefficient, one function per map U → ℕ would already be too many.

| member | statement |
|---|---|
| `SequencesIntoPowerSet`, `PairsIntoPowerSet` | `num → U` and `prod(U, U)` inject into U |
| `PowerSetTimesNum` | `prod(num, U)` injects into U |
| `FiniteMultisetsIntoPowerSet` | the finitely supported maps `U → num` inject into U |
| `PolynomialsIntoPowerSet` | if `C : set(B)` injects into U, the functions `(U → num) → B` that are zero off finitely many maps, each finitely supported, with their other values in C, inject into U |

### Eventually constant functions over a product

Put `X = prod(num,prod(A,B))`. A sequence of subsets of X, and so a
pair of them, is one subset (above, at the inner type `prod(A, B)`). Every HOL type is inhabited, so
`b ↦ {(0,(a,b)) | a:A}` embeds B, and the symmetric construction
embeds A.

An eventually constant function on `set(X)` is encoded by a chosen
constant value and its finite exceptional graph: a sequence runs
through the exceptional points — a countable cover of a finite set,
so an empty graph needs no case of its own — and lists each with the
value there. The value and the sequence are encoded by the preceding
pair and sequence maps. Recovering the graph recovers the whole
function. This uses choice and a countable cover, not a well-ordering or
an infinite-cardinal multiplication theorem: no κ·κ = κ is needed.
In particular, one injection works for finite support with respect
to every possible zero element, so resolution's `index_embedding`
needs no zero parameter.

| member | statement |
|---|---|
| `EventuallyConstantDef` | constant outside a finite set |
| `LeftFactorIntoPowerSet` | the left factor A injects into `set(X)` |
| `RightFactorIntoPowerSet` | the right factor B injects into `set(X)` |
| `FiniteSupportIntoPowerSet` | all eventually constant `set(X) → A` functions inject into `set(X)` |
