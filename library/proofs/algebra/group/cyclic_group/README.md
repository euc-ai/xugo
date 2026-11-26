# cyclic_group — the order of a group element, and the cyclic groups and their subgroups

An element x of a group G on a set has powers `monoid_pow(G.mul, G.one, x, n)`,
the product of n copies of x, spelled in full: the power's implicit
arguments are a monoid's `op` and `e`, which a group record does not name.
The laws of exponents on a set (a power of a member is a member, and
exponents add and multiply) are `algebra/group/group`'s. The order of x is the least positive n with
x ^ n the identity, and 0 when there is none; in a finite group every
element has a positive order, which divides the group's size by
Lagrange's theorem. The subgroup x generates is its powers and their
inverses, and a group is cyclic when one element generates it. The
subgroups of a cyclic group are cyclic, and an element of order d
generates a subgroup holding φ(d) elements of order d. Read backwards this
is the counting criterion: a finite group in which x ^ d = 1 has at most d
solutions for each d > 0 is cyclic.

## Members

| Member | Statement |
|---|---|
| `GroupElementOrderDef` | `group_element_order`: group_ops(A) → A → num |
| `CyclicSubgroupDef` | `cyclic_subgroup`: group_ops(A) → A → set(A) |
| `CyclicGroupDef` | `cyclic_group`: group_ops(A) → bool |

## Powers and the order

An exponent n with x ^ n the identity is a period of x; x raised to its
order is the identity whether or not the order is positive, a power
depends only on its exponent's remainder by the order, and the periods of
x are exactly the multiples of its order. Two equal powers make the gap
between their exponents a positive period, so in a finite group, where
pigeonhole forces two powers to coincide, every order is positive.

| Member | Statement |
|---|---|
| `OrderLeast` | A positive period makes the order positive, a period itself, and at most that period |
| `PowOrderIsOne` | x raised to its order is the identity |
| `PowOrderMulIsOne` | Every multiple of the order is a period |
| `PowRemOrder` | A power depends only on its exponent's remainder by the order |
| `OrderDividesIff` | A power of a member is the identity exactly when the order divides the exponent |
| `OrderAtMostGap` | Two equal powers at distinct exponents make the order positive and at most the gap between them |
| `FiniteOrderPositive` | In a finite group every element has a positive order |
| `PowersBelowOrderInjective` | The powers of x at exponents below its order are distinct |

## The subgroup an element generates

When the order is positive, the subgroup an element generates is its
distinct powers below the order, so its size is the order; Lagrange's
theorem then makes the order divide the group's size, and x raised to the
group's size is the identity.

| Member | Statement |
|---|---|
| `CyclicSubgroupSubgroup` | The powers of a member and their inverses form a subgroup |
| `CyclicSubgroupPowersBelowOrder` | For a positive order, that subgroup is the powers below the order |
| `CardCyclicSubgroup` | For a positive order, that subgroup has as many elements as the order |
| `OrderDividesCard` | In a finite group every order is positive and divides the group's size |
| `PowCardIsOne` | In a finite group x raised to the group's size is the identity |

## Subgroups and images

The powers of a member g lying in a subgroup H are those at the multiples
of one exponent d, the least positive one that puts a power of g in H, or 0
when none does. So in a group g generates, H is the subgroup g ^ d
generates. A homomorphism carries x ^ n to f(x) ^ n, so it carries the
subgroup x generates onto the subgroup f(x) generates, and the image of a
cyclic group is cyclic.

| Member | Statement |
|---|---|
| `SubgroupOfCyclic` | Every subgroup of a cyclic group is cyclic |
| `MapCyclicSubgroup` | A homomorphism carries the subgroup x generates onto the subgroup f(x) generates |
| `ImageOfCyclic` | A homomorphism onto a group carries a cyclic group to a cyclic group |

## The elements of each order, and the counting criterion

When x has positive order d, the power x ^ k has order d exactly when k is
coprime to d, so the subgroup x generates holds φ(d) elements of order d.
Where y ^ d = 1 has at most d solutions, the d elements of that subgroup
are all of the solutions; every element of order d is a solution, so it
lies in that subgroup, and the group has exactly φ(d) elements of order d.
In a finite group where this holds for every d, the n elements sorted by
their orders give n as a sum over the divisors d of n of counts at most
φ(d). By Gauss's identity the φ(d) themselves also add up to n, so every
count is φ(d). Since φ(n) > 0, some element has order n, and it generates
the group.

| Member | Statement |
|---|---|
| `OrderOfPowerCoprime` | For x of positive order d, x ^ k has order d exactly when k is coprime to d |
| `ElementsOfOrderInCyclic` | For x of positive order d, the subgroup x generates holds φ(d) elements of order d |
| `ElementsOfOrderUnderRootBound` | In a finite group, if x has order d and y ^ d = 1 has at most d solutions, there are φ(d) elements of order d |
| `ElementOfFullOrderGenerates` | In a finite group, an element whose order is the group's size generates it |
| `CyclicCriterion` | A finite group in which x ^ d = 1 has at most d solutions for every d > 0 is cyclic |
