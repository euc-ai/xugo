# listing — a finite set and its lists

`set_of_list(l)` is the set of a list's elements: nothing for `nil`,
and the head laid into the tail's set for `cons`. `list_of_set(s)` is
a list enumerating a set — some list whose set is `s` and whose length
is the count of `s`, chosen. The length clause is what makes the
enumeration repetition-free: a list's set counts at most its length,
with equality exactly for a distinct list, so a list meeting both
clauses lists each element once.

`list_of_set` chooses some enumeration and no order. The ordered one,
for a bounded set of naturals, is `datatypes/list`'s `ascending_list`,
which reads no set.

The chapter sits inside `finite_set`, beside `cardinality`, because
the set of a list is finite and every finite set has a list enumerating
it. On an infinite set, `list_of_set` chooses arbitrarily: no list can
have that set of elements.

The lists come from `datatypes/list`, finiteness from the parent
chapter, and the count from `cardinality`.

## Reading a list as a set

The elementary layer: what `set_of_list` is, elementwise, and how it
carries the list operations over to the set operations. `InSetOfList`
is the reading itself and `SetOfListEqEmpty` its one degenerate case,
which needs no correspondence at all. The last three are one sentence
in three operations, carrying the list algebra into the set algebra and
forgetting exactly order and repetition.

| member | statement |
|---|---|
| `InSetOfList` | `x ∈ set_of_list(l) ⇔ list_member(x, l)` — the defining elementwise reading |
| `SetOfListEqEmpty` | a list's set is empty exactly when the list is |
| `SetOfListAppend` | concatenation becomes union |
| `SetOfListMap` | `list_map` becomes `image` |
| `SetOfListReverse` | reversing changes nothing — order is what the reading forgets |

## Finiteness

Why the chapter sits inside `finite_set`: a list's set is always finite,
and finiteness is exactly listability. The second law
is the chapter's reason for existing — it makes "finite" and "can be
written down" the same statement.

| member | statement |
|---|---|
| `FiniteSetOfList` | `finite(set_of_list(l))` |
| `FiniteIffListable` | `finite(s) ⇔ ∃l. set_of_list(l) = s` |

## Counting

What repetition costs. A list's set counts at most its
length, and the slack is exactly the repetition: equality holds precisely
for a distinct list. These two are what make `list_of_set`'s length
clause a repetition-free requirement rather than a size coincidence.

| member | statement |
|---|---|
| `CardSetOfListLe` | `card(set_of_list(l)) ≤ list_length(l)` |
| `HasSizeSetOfListIffDistinct` | `has_size(set_of_list(l), list_length(l)) ⇔ list_distinct(l)` |

## Enumeration

The other direction: every finite set has a list.
`Enumerates` is the existence the choice in `list_of_set`'s definition
needs; `ListOfSetProperties` is that existence read back off the chosen
list, and it is the form every consumer cites.

| member | statement |
|---|---|
| `Enumerates` | `finite(s) ⇒ ∃l. set_of_list(l) = s ∧ list_length(l) = card(s)` |
| `ListOfSetProperties` | the two clauses hold of `list_of_set(s)` itself |

## Σ across the correspondence

The chapter's payoff. Σ over a set and Σ over a list are two
folds at one operation, and the correspondence equates them — one way
for a distinct list, the other way through the chosen enumeration of a
finite set. Between them a sum over a set may be computed by writing the
set down and adding along it.

| member | statement |
|---|---|
| `SumOverListing` | `list_distinct(l) ⇒ nat_sum(set_of_list(l), f) = list_sum(list_map(f, l))` |
| `SumViaListOfSet` | `finite(s) ⇒ nat_sum(s, f) = list_sum(list_map(f, list_of_set(s)))` |

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
