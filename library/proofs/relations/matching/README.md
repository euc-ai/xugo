# relations/matching — finite Hall's theorem

**Hall** characterizes when a finite family of sets has a system of
distinct representatives. For a finite set of indices `s` and a
family `N : A → set(B)`, an injective choice `f` on `s` with
`f(x) ∈ N(x)` exists exactly when every subset `t` of `s` with a
finite combined neighbourhood `⋃image(N, t)` has at least `card(t)`
neighbours. The neighbourhood of a subset may be infinite.

A choice of distinct representatives sends `t` injectively into its
combined neighbourhood, giving the necessary bound. For sufficiency,
descend along proper subsets (`finite_set.FiniteInductProperSubset`): a
finite family whose proper subfamilies are all matched under Hall's
condition is matched under it. A nonempty proper subset with exactly
as many neighbours as indices reserves its whole neighbourhood. To check
Hall's condition for the remaining indices after that neighbourhood is
removed, apply the original bound to a subset joined with the reserved
indices and cancel their equal counts. If every nonempty proper subset
with finitely many neighbours has a strict bound, match one index to
any of its neighbours. The strict bound pays for deleting that one
neighbour before recursing. In both cases what remains is a proper
subfamily, matched by the descent outside what was reserved, and the
two choices have disjoint images and combine into a choice on the
original set.
