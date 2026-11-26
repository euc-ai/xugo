# symmetric_group — the permutations of a type

The first group in the tower that does not commute. A permutation of a
type `A` is a bijective map of `A` to itself; the permutations form the
type `permutation(A)`, carved out of the maps `A → A` by the predicate
`injective_on(𝕌, f) ∧ image(f, 𝕌) = 𝕌` (`f` separates the points of `A` and
sends `A` onto itself), and under
composition, with the identity and the inverse, they form a group. On a
type with three distinct points that group is not abelian.

The elements have type `permutation(A)`, and the group they form is the
record `permutation_group`, whose carrier is `𝕌`, so the group chapter's
carrier laws apply to every permutation. A group of permutations is that
record restricted to its own carrier, `restrict_group(permutation_group, h)`.
The permutations of a SET `s` are then
a subset of that type: `symmetric_group(s)`, the permutations that move
no point outside `s`, a subgroup of the whole. So the symmetric group on
`n` points is `symmetric_group({0, …, n-1})` inside the permutations of
ℕ, and Lagrange's theorem, stated for a subgroup of a finite subgroup,
reads there.

The product of two permutations is written `p * q` — run `q`, then `p` —
the notation `permutation_compose` declares, which the parser reads as
that constant exactly where no built-in `*` serves the operands. The
other operations are spelled by name — `permutation_identity`,
`permutation_inverse(p)`, `transposition(a, b)` — and a permutation is
applied through the map it is, `permutation_map(p, x)`. The product is
spelled by name too where it stands unapplied, as a component of
`permutation_group`, and inside a set comprehension's
element, where the declared operator does not yet reach the binders'
types. A statement that names the operations or the group but no point
of `A` pins the type (`permutation_group⟨A:A⟩`), since nothing else in
it does.

## The type and its operations

| member | statement |
|---|---|
| `PermutationInhabited` | `∃f:(A → A). injective_on(𝕌, f) ∧ image(f, 𝕌) = 𝕌` |
| `PermutationDef` | the type `permutation(A)`, with `permutation_of_map` and `permutation_map` |
| `PermutationComposeDef` | `p * q = permutation_of_map(permutation_map(p) ∘ permutation_map(q))` |
| `PermutationIdentityDef` | `permutation_identity = permutation_of_map(identity_map)` |
| `PermutationInverseDef` | `permutation_inverse(p) = permutation_of_map(inverse_on(𝕌, permutation_map(p)))` |
| `PermutationGroupDef` | `permutation_group = mk_group(permutation_compose, permutation_identity, permutation_inverse, 𝕌)` — the group the permutations form |
| `TranspositionDef` | `transposition(a, b) = permutation_of_map(λx. COND(x = a, b, COND(x = b, a, x)))` |
| `SymmetricGroupDef` | `symmetric_group(s) = {p \| ∀x. x ∉ s ⇒ permutation_map(p, x) = x}` |

## A permutation and its map

A permutation is determined by where it sends each point, and each
operation on permutations is the matching operation on maps. Every such
law is one argument: the map in question is bijective, so it survives
the round trip through the type (`MapOfBijection`). The inverse uses
`inverse_on(𝕌, permutation_map(p))`. `InverseOnInjective` and
`InverseOnImage` make this map a bijection of the whole type, and
`InverseOnLeft` says that it sends the image of a point back to that point.

| member | statement |
|---|---|
| `MapBijective` | `injective_on(𝕌, permutation_map(p)) ∧ image(permutation_map(p), 𝕌) = 𝕌` |
| `MapOfBijection` | `injective_on(𝕌, f) ∧ image(f, 𝕌) = 𝕌 ⇒ permutation_map(permutation_of_map(f), x) = f(x)` |
| `PermutationEq` | `p = q ⇔ ∀x. permutation_map(p, x) = permutation_map(q, x)` |
| `MapCompose` | `permutation_map(p * q, x) = permutation_map(p, permutation_map(q, x))` |
| `MapIdentity` | `permutation_map(permutation_identity, x) = x` |
| `MapInverse` | `permutation_map(permutation_inverse(p), permutation_map(p, x)) = x` |
| `MapInverseRight` | `permutation_map(p, permutation_map(permutation_inverse(p), x)) = x` |
| `MapTransposition` | `permutation_map(transposition(a, b), x) = COND(x = a, b, COND(x = b, a, x))` |

## The group, and why it does not commute

Each group axiom is an equation between permutations, read point by
point. The failure of commutativity needs three points: `(a b)(b c)`
sends `a` to `b` and `(b c)(a b)` sends it to `c`.

| member | statement |
|---|---|
| `SymmetricGroup` | `group(permutation_group)` |
| `RestrictPermutationGroupUniverse` | `restrict_group(permutation_group, 𝕌) = permutation_group` — the group restricted to the whole type, as a law of subgroups asks for it at 𝕌 |
| `TranspositionSelfInverse` | `transposition(a, b) * transposition(a, b) = permutation_identity` |
| `TranspositionsDoNotCommute` | `a ≠ b ∧ b ≠ c ∧ a ≠ c ⇒ transposition(a, b) * transposition(b, c) ≠ transposition(b, c) * transposition(a, b)` |
| `TranspositionConjugate` | `a ≠ b ∧ a ≠ c ⇒ transposition(a, c) = transposition(b, c) * transposition(a, b) * transposition(b, c)` |
| `TranspositionSymmetric` | `transposition(a, b) = transposition(b, a)` |
| `NotAbelian` | `a ≠ b ∧ b ≠ c ∧ a ≠ c ⇒ ¬abelian_group(permutation_group)` |

## Powers of a permutation

`s^n` is `monoid_pow(permutation_compose, permutation_identity, s, n)`, the n-fold product in `permutation_group`; `permutation_order(s)` is the least positive e with `s^e` the identity, chosen.

| Member | Statement |
|---|---|
| `PermutationPowerAdd` | `s^(i + j) = s^i * s^j` |
| `PermutationPowerIn` | `subgroup(permutation_group, h) ∧ s ∈ h ⇒ s^n ∈ h` |
| `PermutationPowerRepeat` | `i < j ∧ s^i = s^j ⇒ 0 < j - i ∧ s^(j - i) = permutation_identity` |
| `PermutationOrderDef` | `permutation_order(s) = εe. 0 < e ∧ s^e = permutation_identity ∧ (∀d. 0 < d ∧ s^d = permutation_identity ⇒ e ≤ d)`: the order of s, chosen |
| `PermutationOrderUnique` | `0 < e ∧ s^e = permutation_identity ∧ (∀d. 0 < d ∧ s^d = permutation_identity ⇒ e ≤ d) ⇒ permutation_order(s) = e` |
| `PowersSubgroup` | for e the least positive exponent with `s^e = permutation_identity`, the powers `s^j`, `j < e`, form a subgroup with e elements |

## The symmetric group on a set

| member | statement |
|---|---|
| `InSymmetricGroup` | `p ∈ symmetric_group(s) ⇔ ∀x. x ∉ s ⇒ permutation_map(p, x) = x` |
| `SymmetricGroupSubgroup` | `subgroup(permutation_group, symmetric_group(s))` |
| `SymmetricGroupMono` | `s ⊆ t ⇒ symmetric_group(s) ⊆ symmetric_group(t)` |
| `SymmetricGroupMapsInto` | `q ∈ symmetric_group(t) ∧ x ∈ t ⇒ permutation_map(q, x) ∈ t` |
| `FiniteInjectionPermutation` | `finite(s) ∧ (∀x. x ∈ s ⇒ f(x) ∈ s) ∧ injective_on(s, f) ∧ (∀x. x ∉ s ⇒ f(x) = x) ⇒ ∃p. p ∈ symmetric_group(s) ∧ permutation_map(p) = f` |
| `TranspositionInSymmetricGroup` | `a ∈ s ∧ b ∈ s ⇒ transposition(a, b) ∈ symmetric_group(s)` |
| `SymmetricGroupEmpty` | `symmetric_group(∅) = {permutation_identity}` |
| `SymmetricGroupUniverse` | `symmetric_group(𝕌) = 𝕌` |
| `PermutationAdjacentDescent` | `q ∈ symmetric_group({i \| i < n}) ∧ q ≠ permutation_identity ⇒ ∃k. suc(k) < n ∧ permutation_map(q, suc(k)) < permutation_map(q, k)` |
| `PermutationMovesSomePointDown` | `p ∈ symmetric_group({i \| i < n}) ∧ p ≠ permutation_identity ⇒ ∃i. i < n ∧ permutation_map(p, i) < i` |

## How many permutations a finite set has

Laying a point `a` into `s`, every permutation of `insert(a, s)` is sorted
by where it sends `a`: it is a transposition `(a b)` after a permutation
of `s`, with `b` the image of `a`. When `a` is new, the products `(a b)·p`
are pairwise distinct — each sends `a` to its `b`, and `(a b)` cancels —
so laying the point in multiplies the count by the new number of points
(the cardinality chapter's `HasSizeProductImage` counts the products as
pairs), and the symmetric group on `n` points has `n!` elements.

| member | statement |
|---|---|
| `SymmetricGroupInsert` | `symmetric_group(insert(a, s)) = {transposition(a, b) * p \| b ∈ insert(a, s) ∧ p ∈ symmetric_group(s)}` |
| `InsertProductsDistinct` | `a ∉ s ∧ p, q ∈ symmetric_group(s) ∧ transposition(a, b) * p = transposition(a, c) * q ⇒ b = c ∧ p = q` |
| `CardSymmetricGroup` | `finite(s) ⇒ has_size(symmetric_group(s), factorial(card(s)))` |
| `SymmetricGroupFinite` | `finite(s) ⇒ finite(symmetric_group(s))` |
| `CardPermutations` | `finite(𝕌⟨A⟩) ⇒ has_size(𝕌⟨permutation(A)⟩, factorial(card(𝕌⟨A⟩)))` |

## Lagrange's theorem in the symmetric group

The symmetric group on a finite set is a finite subgroup of the
permutations of the whole type, so Lagrange's theorem (`group`) reads
there with nothing added: any group of permutations of `n` points has an
order dividing `n!`. The four chapters meet in this one statement — the
group's cosets, the partition's class count, the union count, and the
count of the permutations themselves.

| member | statement |
|---|---|
| `SubgroupOrderDividesFactorial` | `finite(s) ∧ subgroup(permutation_group, h) ∧ h ⊆ symmetric_group(s) ⇒ card(h) ∣ factorial(card(s))` |

## Inversions and parity

The inversions of a permutation are the pairs of points below n whose
order it reverses. An even permutation has an even number of inversions.
Swapping adjacent positions changes the inversion count by one. Every
permutation of the points below n other than the identity has an adjacent
descent, so induction on the inversion count gives the product law. The
identity has no inversions. An adjacent swap is odd, and conjugating
(k l) by the adjacent (l l+1) gives (k l+1), so induction on the
larger point makes every transposition odd.

| Member | Statement |
|---|---|
| `PermutationInversionsDef` | `permutation_inversions(n, p) = {z \| fst(z) < snd(z) ∧ snd(z) < n ∧ permutation_map(p, snd(z)) < permutation_map(p, fst(z))}` |
| `PermutationEvenDef` | `permutation_even(n, p) ⇔ nat_even(card(permutation_inversions(n, p)))` |
| `PermutationIdentityEven` | The identity permutation is even |
| `PermutationParityProduct` | A product p·q, where q permutes the points below n and p is any permutation, is even exactly when p and q have the same parity |
| `InversionsAdjacentSwap` | Composing on the right with the swap of two adjacent points below n changes the number of inversions by exactly one: up when the permutation keeps them in order, down when it reverses them |
| `PermutationParityAdjacentSwap` | Composing on the right with the swap of two adjacent points below n flips the parity |
| `PermutationParityInverse` | A permutation of the points below n has the parity of its inverse |
| `TranspositionOdd` | A transposition of two distinct points below n is odd |
| `ParityAfterTransposition` | Composing a permutation of the points below n with a transposition of two of them flips its parity |
