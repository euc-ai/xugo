# sylow — the Sylow theorems: a finite group has subgroups of every prime-power order dividing its own, and its Sylow subgroups are conjugate and counted 1 mod p

A Sylow p-subgroup of a finite group G is a p-subgroup, a subgroup
whose order is a power of p, whose index p does not divide. A
p-subgroup H acts on its left cosets by translation; the cosets it fixes
are the cosets of H by points of its normalizer, so when p divides the
index of H it divides the order of the normalizer's quotient by H, and
the preimage of a subgroup of order p there, which Cauchy's theorem
supplies, is a subgroup of order p times that of H with H normal in it.
Starting from
the trivial subgroup this gives a subgroup of every order p ^ n dividing
card(G), and a Sylow subgroup (Sylow I). A nontrivial p-group has order p ^ k with k positive, so its subgroup of
order p ^ (k − 1) has index p.

A p-subgroup Q acting on the cosets of a subgroup P of index prime to p
fixes, modulo p, as many cosets as there are, so it fixes one; a coset gP
it fixes puts Q inside the conjugate gPg⁻¹. So every p-subgroup lies in a
conjugate of each Sylow subgroup, and any two Sylow subgroups are
conjugate (Sylow II).
G acts transitively by conjugation on its Sylow p-subgroups, with the
normalizer of P as stabilizer, so their number is the index of the
normalizer and divides the index of P. P acting on them fixes only
itself: a Sylow subgroup Q it fixes has P in its normalizer, where Q is a
Sylow subgroup and normal, so it holds every p-subgroup there, P among
them, and P = Q. So their number is 1 modulo p (Sylow III).

## Members

| Member | Statement |
|---|---|
| `SylowSubgroupDef` | `sylow_subgroup`: group_ops(A) → num → set(A) → bool |
| `SylowSubgroupsDef` | `sylow_subgroups`: group_ops(A) → num → set(set(A)), the set of the Sylow p-subgroups; a membership in it reads as sylow_subgroup |
| `SylowSubgroupPSubgroup`, `SylowSubgroupIndexNotDivisible` | its two conditions: a Sylow p-subgroup is a p-subgroup, and p does not divide its index |
| `SylowSubgroupSubgroup` | A Sylow p-subgroup is a subgroup |

## Sylow I: existence

| Member | Statement |
|---|---|
| `PSubgroupGrowth` | A p-subgroup whose index p divides is normal in a subgroup p times as large |
| `PrimePowerOrderSubgroup` | A finite group has a subgroup of every order p ^ n, p a prime, dividing its own |
| `SylowOrder` | In a finite group, for 2 ≤ p, the Sylow p-subgroups are exactly the subgroups of order p ^ e, e the multiplicity of p in the order of the group |
| `SylowExists` | A finite group has a Sylow p-subgroup for every prime p |
| `PGroupOfOrderDividing` | A finite group whose order divides a power of a prime p is a p-group |
| `PGroupIndexPrime` | A nontrivial p-group, p a prime, has a subgroup of index p |

## Sylow II: conjugacy

| Member | Statement |
|---|---|
| `PSubgroupInConjugate` | A p-subgroup lies in a conjugate of every subgroup of finite index that p does not divide |
| `SylowConjugacy` | Any two Sylow p-subgroups are conjugate |
| `ConjugateIsSylow` | A conjugate of a Sylow p-subgroup is a Sylow p-subgroup |

## Sylow III: the number of Sylow subgroups

| Member | Statement |
|---|---|
| `SylowConjugationAction` | A finite group acts by conjugation on its Sylow p-subgroups |
| `SylowCountIndex` | The number of Sylow p-subgroups is the index of the normalizer of any one |
| `SylowCountDivides` | The number of Sylow p-subgroups divides the index of each |
| `SylowInSubgroup` | A Sylow p-subgroup of G inside a subgroup K is a Sylow p-subgroup of K |
| `SylowInNormalizer` | A Sylow p-subgroup inside the normalizer of another is that one |
| `SylowCountMod` | The number of Sylow p-subgroups is 1 mod p |
