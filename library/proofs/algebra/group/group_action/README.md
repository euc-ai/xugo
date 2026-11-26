# group_action — actions of a group on a set, their orbits and stabilizers, Burnside's lemma, the fixed points of a p-group, the actions by conjugation and on cosets, and Cauchy's theorem

A group G on a set acts on a set X when each element moves X into
itself, the identity moves nothing, and acting by a product is acting by
the factors in turn. The orbit of a point is where the group can move it
and its stabilizer the elements that fix it. The orbits partition X, the
stabilizer is a subgroup, and the orbit of x is in bijection with the
cosets of its stabilizer: the orbit–stabilizer theorem. Counting the pairs
(g, x) with g fixing x once by g and once by x gives Burnside's lemma, the
number of orbits as the average number of fixed points. When the order of
the group divides a power of a prime p every orbit but a fixed point has
size divisible by p, so the group fixes, mod p, as many points as it acts
on. A group acts on its own subsets by conjugation, the normalizer of a
subgroup being the stabilizer there, and on the cosets of a subgroup by
translation, where the cosets a finite subgroup fixes are those of its
normalizer; these are the actions behind the Sylow theorems. Cauchy's
theorem follows from an action too: the residues mod p rotate the p-tuples
of G whose product is the identity, and counting the fixed tuples mod p
finds a constant one other than the tuple of ones.

## Members

| Member | Statement |
|---|---|
| `GroupAction` | `group_action`: group_ops(A) → set(B) → (A → B → B) → bool |
| `GroupOrbitDef` | `group_orbit`: group_ops(A) → (A → B → B) → B → set(B) |
| `GroupStabilizerDef` | `group_stabilizer`: group_ops(A) → (A → B → B) → B → set(A) |
| `GroupFixedPointsDef` | `group_fixed_points`: set(B) → (A → B → B) → A → set(B) |
| `GroupConjugateDef` | `group_conjugate`: group_ops(A) → A → set(A) → set(A) |
| `GroupNormalizerDef` | `group_normalizer`: group_ops(A) → set(A) → set(A) |
| `ActingGroup` | The acting group is a group on its carrier |
| `ActIn` | Acting by an element keeps a point of X in X |
| `ActOne` | The identity fixes every point |
| `ActMul` | Acting by a product is acting by its factors in turn |
| `RestrictAction` | An action restricts to every subgroup of the acting group |
| `SubsetAction` | An action restricts to every subset of X the group keeps in itself |

## Orbits and stabilizers

The stabilizer of a point is a subgroup, and two elements move the point
to one place exactly when they lie in one coset of it, so the orbit is
counted by the cosets and Lagrange's theorem gives the orbit–stabilizer
formula. A point lies in its own orbit, the orbits lie in X, and a point
of an orbit has that orbit, so the orbits are the fibres of the orbit map
and partition X: a sum over X is the sum over the orbits of the sums
over each, and a point is fixed by every element exactly when its orbit
is the point alone.

| Member | Statement |
|---|---|
| `InvActCancel` | Acting by g and then by its inverse fixes a point |
| `StabilizerSubgroup` | The stabilizer of a point is a subgroup |
| `ActEqIffStabilizer` | g and h move x to one place exactly when g⁻¹h fixes x |
| `OrbitStabilizer` | For a finite group, the group's size is the orbit's size times the stabilizer's |
| `InOwnOrbit` | A point lies in its own orbit |
| `OrbitSubset` | An orbit lies in X |
| `OrbitOfAct` | A point and its image under the group have one orbit |
| `OrbitOfMember` | A point of an orbit has that orbit |
| `OrbitFibre` | The points of X with the orbit of x are that orbit |
| `FixedIffSingletonOrbit` | A point is fixed by every element exactly when its orbit is the point alone |
| `SumOverOrbits` | A sum over a finite set acted on is the sum over the orbits of the sums over each |

## Burnside's lemma

Over one orbit the stabilizers add up to the order of the group; counting
the pairs (g, x) with g fixing x by x, grouped by orbit, and then by g,
gives the number of orbits times the order as the total number of fixed
points.

| Member | Statement |
|---|---|
| `SumStabilizersOverOrbit` | Over one orbit the stabilizers' sizes add up to the group's size |
| `Burnside` | The number of orbits times the group's size is the total number of fixed points |

## Groups of prime order

A subgroup's order divides the group's (Lagrange), so a group of prime
order has no subgroup between the trivial one and itself.

| Member | Statement |
|---|---|
| `PrimeOrderSubgroup` | a subgroup of a finite group of prime order is `{G.one}` or the whole carrier |

## Groups of prime-power order

When the acting group is a p-group, p a prime, the orbit–stabilizer
theorem makes the size of every orbit a divisor of its order, a power of
p, so itself a power of p: 1 or a multiple of p. The singleton orbits are
the points every element fixes, so summing over the orbits counts the set
and those points alike modulo p. A group of prime order p is the case
Cauchy's theorem reads.

| Member | Statement |
|---|---|
| `PrimePowerFixedPoints` | A p-group, p a prime, acting on a finite set fixes as many points as the set has, mod p |

## Conjugation and the normalizer

A group acts on the subsets of its carrier by conjugation, S ↦
group_conjugate(G, g, S), the image gSg⁻¹. A conjugate of a subgroup is
a subgroup, a conjugate of a finite subset of the carrier has its size,
and the normalizer of a subgroup H, the stabilizer of H under this
action, is a subgroup in which H is normal.

| Member | Statement |
|---|---|
| `ConjugationAction` | A group acts on the subsets of its carrier by conjugation |
| `ConjugateSubgroup` | A conjugate of a subgroup is a subgroup |
| `ConjugateCard` | Conjugation keeps the size of a finite subset of the carrier |
| `ConjugateFinite` | A conjugate of a finite set is finite |
| `NormalizerSubgroup` | The normalizer of a subgroup is a subgroup holding it, in which it is normal |
| `NormalizerIsStabilizer` | The normalizer of a set is its stabilizer when the group acts by conjugation |

## Acting on cosets

A group acts on the left cosets of a subgroup H by left translation. An
element h fixes the coset gH exactly when g⁻¹hg lies in H, so the cosets
every element of a finite H fixes are those of the points of its
normalizer, the carrier of the normalizer's quotient by H.

| Member | Statement |
|---|---|
| `CosetAction` | A group acts on the left cosets of a subgroup by left translation |
| `CosetFixedIff` | h fixes the coset gH exactly when g⁻¹hg lies in H |
| `FixedCosetsNormalizer` | The cosets of a finite subgroup H that H fixes are the cosets of H in its normalizer |

## Cauchy's theorem

The residues mod p act by rotation on the p-tuples of G whose product is
the identity. There are card(G) ^ (p − 1) such tuples, a multiple of p, so
p divides the number of fixed tuples. A tuple is fixed exactly when it is
constant, and the tuple of ones is fixed, so another fixed tuple is
constant at some x ≠ 1 with x ^ p = 1, and x has order p.

| Member | Statement |
|---|---|
| `ResidueAddGroupOn` | The residues mod n > 0 form a group under addition mod n |
| `RotatedLength` | A list rotated at length n has length n |
| `RotatedEntry` | A list rotated by k holds at position j < n the entry at j + k mod n |
| `RotationFixesConstant` | Rotating a list of length n whose entries are all x gives the list back |
| `RotationFixedIsConstant` | A list every rotation fixes holds its first entry at every position j < n |
| `RotationAction` | For n > 0, the residues mod n act by rotation on the n-tuples whose product is the identity |
| `ProductOneListsCount` | The lists of length n + 1 over a finite group whose product is the identity number card(G) ^ n |
| `Cauchy` | A finite group whose order a prime p divides has an element of order p |
