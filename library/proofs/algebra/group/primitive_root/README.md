# primitive_root — primitive roots: the units mod a prime and mod an odd prime power form a cyclic group

A primitive root mod n is a generator of the units mod n. The units mod a
prime p form a cyclic group because, read in a field of p elements through
the integers' map, the residues with a ^ d ≡ 1 (mod p) go one-to-one to
roots of x ^ d = 1, of which a field has at most d — the counting criterion
for a finite group to be cyclic. A primitive root mod p lifts to one mod
every power of an odd prime p.

## The units mod a prime

| Member | Statement |
|---|---|
| `ResidueRootsBound` | Mod a prime p and for d > 0, at most d residues below p solve a ^ d ≡ 1 (mod p) |
| `UnitsModPrimeCyclic` | The units mod a prime form a cyclic group |
| `PrimitiveRootModPrime` | A primitive root mod p exists: some g prime to p has order p − 1, g ^ e ≡ 1 (mod p) exactly when p − 1 divides e |

## The units mod a power of an odd prime

Of g and g · (1 + p), for a primitive root g mod p, one — h — has
h ^ (p − 1) = 1 + p · t with p ∤ t. Raising 1 + p · t to the p-th power
raises the power of p in its distance from 1 by exactly one, since p
divides C(p, 2) for odd p. So the order of h mod p ^ k is a multiple of
p − 1 that divides φ(p ^ k) = (p − 1) · p ^ (k − 1) but not
(p − 1) · p ^ (k − 2), which makes it φ(p ^ k), and h generates the units.

| Member | Statement |
|---|---|
| `DivisorPinnedByPrimePower` | For a prime p, a multiple of n dividing n · p ^ (j + 1) but not n · p ^ j is n · p ^ (j + 1) |
| `PthPowerOfOnePlusMultiple` | For an odd prime p, (1 + p · a) ^ p is 1 + p² · a plus a multiple of p³ · a² |
| `OnePlusPPowersNotOne` | For an odd prime p not dividing t, (1 + p · t) ^ (p ^ i) is not 1 mod p ^ (i + 2) |
| `CongruentWithPExactlyDividing` | For a prime p and g prime to p, some h ≡ g (mod p) has h ^ (p − 1) = 1 + p · t with p not dividing t |
| `UnitsModPrimePowerCyclic` | The units mod a power of an odd prime form a cyclic group |
