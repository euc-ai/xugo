# list — finite sequences

A list is a finite sequence: either empty (`nil`) or one element in
front of a list (`cons`). The chapter mints the type through the
datatype door, which carves `list(A)` out of the recursive-type
universe `recspace(A)` and derives the four principles a datatype comes
with:

- **Induction** — a property that holds at `nil` and is preserved by
  `cons` holds of every list. The `induction` tactic dispatches on it
  under the library name `list_induction`.
- **Recursion** — a function on lists is determined by its value at
  `nil` and its step at `cons`. The define door's equation compiler
  instantiates it under `list_recursion`: each recursive operation
  below is one definition against it.
- **ConsInjective** and **NilNotCons** — `cons(h, t) = cons(h', t')`
  exactly when the heads and the tails agree, and `nil` is not a
  `cons`. Between them, every equation between constructor terms is
  decided.

The universe's own theory — the encoding of a tree as a predicate, the
inductive universe and the type carved from it, the constructors'
injectivity, induction and recursion theorems — is the sibling chapter
`datatype_universe`, which the door's derivations read.

## The operations

Seven operations are defined by primitive recursion over the two
constructors:

| constant | reading |
|---|---|
| `list_append(l, m)` | concatenation: `l` in front of `m` |
| `list_length(l)` | the number of elements |
| `list_reverse(l)` | the elements in the opposite order |
| `list_map(f, l)` | `f` applied to every element, the order kept |
| `list_member(x, l)` | `x` occurs in `l` |
| `list_fold(f, l, b)` | the fold from the right: `f(a₁, f(a₂, … f(aₙ, b)))` |
| `list_nth(l, i)` | the element at position `i`, counting from 0; past the end, one fixed element of the type |

Four more constants complete the chapter. `list_distinct(l)` says no element occurs twice — the head is not in the tail, and the
tail is distinct. `list_sum(l)`, for a list of naturals, is the fold
at addition started at 0, the list-side twin of `nat_sum = iterated_op(+)`;
through `list_fold`'s clauses it is the recursion a reader expects,
`list_sum(nil) = 0` and `list_sum(cons(h, t)) = h + list_sum(t)`. Those
two exist for the listing correspondence (`sets/listing`),
which reads a list as a finite set: a list's set counts at most its
length, with equality exactly for a distinct list, and Σ over the set
of a distinct list is the fold over the list. `list_product(l)` is the
same fold at multiplication started at 1, the twin of
`nat_product = iterated_op(*)`. `list_permutation(l, m)` says the two lists hold the
same elements, each as often, in some order; it is a relation defined
by rules rather than an operation defined by recursion, and has a part
of its own below. Those two exist for factorization into primes
(`nat_num/nat_prime`), which is unique only up to the order of the
factors — the statement a permutation makes.

## The structure

One member stands apart from the operations. `Cases` says every list is
either empty or a head in front of a tail — the plain case analysis the
datatype door does not derive. It is what a proof reaches for when it
must decompose an unknown list and has no use for a hypothesis about
the tail.

| member | statement |
|---|---|
| `Cases` | `l = nil ∨ ∃h t. l = cons(h, t)` |

## Concatenation

`list_append` recurses on its first argument, so a law about it inducts
there and the second list rides along untouched; `list_length` and `list_reverse`
are read through it.

| member | statement |
|---|---|
| `AppendNil` | `list_append(l, nil) = l` — the right unit; the left one is a definitional clause |
| `AppendAssoc` | `list_append(l, list_append(m, n)) = list_append(list_append(l, m), n)` |
| `AppendEqNil` | a concatenation is empty exactly when both parts are |
| `AppendLeftCancel` | `list_append(l, m) = list_append(l, n) ⇔ m = n` |
| `AppendRightCancel` | `list_append(l, n) = list_append(m, n) ⇔ l = m` |
| `LengthAppend` | `list_length(list_append(l, m)) = list_length(l) + list_length(m)` |
| `LengthEqNil` | `list_length(l) = 0 ⇔ l = nil` |
| `LengthEqCons` | `list_length(l) = suc(n)` exactly when `l` is a head in front of a tail of length `n` |
| `LengthEqConsOver` | a list of length `suc(n)` with entries in s is a head in s in front of a tail of length n with entries in s |
| `BoolListsOfLengthFinite` | there are finitely many boolean lists of each length |
| `ListsCount` | the lists of length n with entries in a finite set s number `card(s) ^ n` |
| `LengthReverse` | reversing does not change the length |
| `ReverseAppend` | `list_reverse(list_append(l, m)) = list_append(list_reverse(m), list_reverse(l))` — the order flips |
| `ReverseReverse` | `list_reverse(list_reverse(l)) = l` |
| `ReverseEqNil` | a reversal is empty exactly when the list is |

## The map

`list_map` changes what a list holds and nothing else, so every law here
says that some other operation does not notice. This is the one part
of the chapter where two element types meet: a statement over
`f : A → B` reads its list operations at both.

| member | statement |
|---|---|
| `MapAppend` | `list_map` distributes over concatenation |
| `MapId` | mapping the identity is the identity |
| `MapMap` | `list_map(g ∘ f, l) = list_map(g, list_map(f, l))`, the composite written as a λ so the chapter needs no function theory |
| `MapReverse` | `list_map` and `list_reverse` commute |
| `LengthMap` | mapping does not change the length |
| `MapEqNil` | an image is empty exactly when the list is |
| `MapAgreesOnMembers` | two maps with the same image list agree on its members |
| `MapCongruence` | two functions that agree on the members of a list have one image of it |

## Positions

A position is a natural number below the length, and `list_nth` reads
the list there. These laws say where an element sits after a cons, a
map or a concatenation, that the members are the elements at positions,
that a list is fixed by its length and its elements, and that every
finite sequence is some list's.

| member | statement |
|---|---|
| `NthHead` | the head is at position 0 |
| `NthTail` | position `suc(i)` of `cons(h, t)` is position `i` of `t` |
| `NthMap` | the image has `f` of the element at every position |
| `NthAppendLeft` | a position of the front list keeps its element in the concatenation |
| `NthAppendRight` | position `i` of the back list sits at `list_length(l) + i` in `list_append(l, m)` |
| `MemberNth` | the members are the elements at positions |
| `NthExtensionality` | two lists of one length with the same element at every position are equal |
| `TabulatedList` | every sequence of `n` elements is the list of some list's positions |

## Membership

A member sits at a split of the list, and the other laws here say
where an element can be found after something has been done to the
list. `list_distinct` is stated in terms of `list_member` and closes the
part; the one law about it is what the listing chapter reads when it
counts a list's set.

| member | statement |
|---|---|
| `MemberAppend` | `list_member(x, list_append(l, m)) ⇔ list_member(x, l) ∨ list_member(x, m)` |
| `MemberSplit` | `list_member(x, l) ⇒ ∃a b. l = list_append(a, cons(x, b))` — a member sits at a split of the list |
| `MemberReverse` | reversing does not change what a list contains |
| `MemberMap` | `list_member(y, list_map(f, l)) ⇔ ∃x. list_member(x, l) ∧ y = f(x)` — the image, elementwise |
| `DistinctAppend` | `list_distinct(list_append(l, m))` exactly when both are distinct and share no element |

## The fold

`list_fold` is the general fold from the right; `list_sum` is that fold at
addition, started at 0. Its three laws are the recursion a consumer
computes with, the split over a concatenation, and the fact that a sum
does not change under reversal. The last is where the chapter spends
commutativity of addition, and the only place it does. `list_product`
is the fold at multiplication, started at 1, and has its recursion.

| member | statement |
|---|---|
| `FoldAppend` | `list_fold(f, list_append(l, m), b) = list_fold(f, l, list_fold(f, m, b))` — a fold over a concatenation is the outer fold started at the inner one |
| `ConstantListFold` | `list_fold(op, l, e) = monoid_pow(op, e, x, list_length(l))` when every entry of l is x |
| `ListSumClauses` | `list_sum(nil) = 0` and `list_sum(cons(h, t)) = h + list_sum(t)` |
| `ListSumAppend` | `list_sum` is additive over concatenation |
| `ListSumReverse` | `list_sum(list_reverse(l)) = list_sum(l)` |
| `ListProductClauses` | `list_product(nil) = 1` and `list_product(cons(h, t)) = h * list_product(t)` |

## Permutations

Two lists are permutations of each other when one can be rearranged
into the other. The definition says so by the moves a rearrangement is
made of, through the inductive door: the empty list is a permutation of
itself, a common head extends a permutation, the first two elements may
trade places, and two permutations in a row are one; `list_permutation` is
the smallest relation closed under those four moves. The door hands
back the moves as one rule set (`ListPermutationRules`), rule induction
(`ListPermutationInduct`, and `ListPermutationInductStrong`, whose moves are also
told that what they extend or compose is a permutation), and the case
analysis (`ListPermutationCases`). The chapter uses the rule set and the
plain induction; the other two are published for a consumer that needs
them. Each move is also restated as a member of its own, because every
argument about permutations names the move it makes.

A law that starts from a permutation is a rule induction: a property
that holds of the empty pair, survives a common head, holds of every
swap and composes, holds of every permutation. A law that produces a
permutation — reflexivity, moving a member to the front — inducts on
the list instead.

| member | statement |
|---|---|
| `PermutationNil` | `list_permutation(nil, nil)` |
| `PermutationCons` | `list_permutation(l, m) ⇒ list_permutation(cons(x, l), cons(x, m))` |
| `PermutationSwap` | `list_permutation(cons(x, cons(y, l)), cons(y, cons(x, l)))` |
| `PermutationTrans` | `list_permutation(l, m) ∧ list_permutation(m, n) ⇒ list_permutation(l, n)` |
| `PermutationRefl` | every list is a permutation of itself |
| `PermutationSym` | `list_permutation(l, m) ⇒ list_permutation(m, l)` |
| `PermutationMember` | `list_permutation(l, m) ⇒ (list_member(x, l) ⇔ list_member(x, m))` — a rearrangement loses no element and gains none |
| `PermutationListProduct` | `list_permutation(l, m) ⇒ list_product(l) = list_product(m)` — a rearrangement leaves a product unchanged |
| `PermutationMoveToFront` | `list_member(x, m) ⇒ ∃r:list(A). list_permutation(m, cons(x, r))` — a member of a list can be moved to its front |

## Ascending lists

`ascending_list(n, P)` lists the numbers from 0 to `n` satisfying `P` in
increasing order, by recursion on `n`; a list is ascending when every
member is below every later one. It is the only ascending list with
those members. The simplex category reads the missed values and the
repeats of a monotone map through it.

| member | statement |
|---|---|
| `ListAscendingDef` | `list_ascending(l)`: every member below every later member |
| `AscendingListDef` | `ascending_list(n, P)`: the numbers from 0 to `n` satisfying `P`, ascending |
| `AscendingListMember` | `list_member(i, ascending_list(n, P)) ⇔ i ≤ n ∧ P(i)` |
| `ListAscendingCons` | a cons list is ascending exactly when its tail is ascending and its head precedes every tail member |
| `AscendingListSorted` | the listing is ascending |
| `ListAscendingExt` | ascending lists with identical members are equal |
| `AscendingListUnique` | an ascending list with exactly those members is the listing |

## Two habits

Worth meeting once rather than at every member that uses them.

**Emptiness is a statement about length.** Every "… is nil exactly
when …" law is proved by reading `LengthEqNil` from right to left,
which turns each emptiness into a condition on a number, and then
citing what the operation does to the length. None of them is proved by
induction.

**A polymorphic operation is read at every element type the statement
spells.** A law over `f : A → B` mentions its list operations twice,
once at B for the image and once at A for the source, and a proof cites
the definition at both; a law that pins the element type, as the sums
over `list(num)` do, cites it at that type rather than at the abstract
letter. Either way the spelling is `Def.Inst[τ]()`, and where it stands
beside a bare `Def` the two occurrences are the two readings.

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
