# units_mod — the residues coprime to n as a group under multiplication mod n, with Euler's and Wilson's theorems

The units of the integers mod n are taken as residues: the numbers below n
coprime to n, multiplied and reduced mod n. They form an abelian group on
that set with φ(n) elements, so Lagrange's theorem gives Euler's theorem
$a^{\varphi(n)} \equiv 1 \pmod{n}$ for every a coprime to n. Mod a prime every nonzero
residue is a unit and only ±1 are their own inverses; pairing every other
residue with its inverse gives Wilson's theorem (p − 1)! ≡ −1 (mod p), and
no composite n satisfies the congruence.

## Members

| Member | Statement |
|---|---|
| `UnitsModDef` | `units_mod`: num → group_ops(num) |

## The group

For n > 0 the units form an abelian group. A unit's inverse is the
inverse mod n that `nat_congruence.InverseExists` finds below n.

| Member | Statement |
|---|---|
| `AbelianGroupOn` | For n > 0, the units mod n form an abelian group |
| `MulEqOne` | Two residues multiply to the identity exactly when their product is 1 mod n |
| `ResidueIn` | For n > 0 the residue mod n of a number coprime to n is a unit |
| `UnitsModPrime` | Mod a prime the units are the residues 1 .. p − 1 |

## Euler's theorem

The units mod n number φ(n), and a member of a finite group raised to the
group's size is the identity, so the residue of a number coprime to n,
raised to φ(n), is 1 mod n. The group's power of a residue is the ordinary
power reduced mod n, and a number is congruent to its residue, so their
powers are congruent.

| Member | Statement |
|---|---|
| `UnitsPowMod` | In the units mod n, the k-th power of a is the residue of a ^ k |
| `CarrierHasSize` | There are φ(n) units mod n |
| `Euler` | Euler's theorem: $a^{\varphi(n)} \equiv 1 \pmod{n}$ for n > 0 and a coprime to n |

## Wilson's theorem

Mod a prime every nonzero residue is a unit, and only 1 and p − 1 are
their own inverses. The inverse map pairs off the other residues into
pairs with product 1, which leaves (p − 1)! ≡ 1 · (p − 1) ≡ −1.
Conversely, a divisor of n other than n is one of the factors of (n − 1)!,
so dividing (n − 1)! + 1 as well it divides 1.

| Member | Statement |
|---|---|
| `ProductPairedInverses` | A finite set that a map pairs off into inverse pairs mod n has product 1 mod n |
| `Wilson` | Wilson's theorem: (p − 1)! + 1 ≡ 0 (mod p) for a prime p |
| `WilsonConverse` | A number n > 1 with (n − 1)! + 1 ≡ 0 (mod n) is prime |

## −1 is a square mod a prime p ≡ 1 (mod 4)

Write $h = \frac{p-1}{2}$. The factors of (p − 1)! above h are the complements of
1, …, h to p, and two complements multiply as the numbers do. So when h is
even (p ≡ 1 mod 4), (p − 1)! ≡ h!², and Wilson's theorem makes h!² ≡ −1.

| Member | Statement |
|---|---|
| `MinusOneSquare` | For a prime p ≡ 1 (mod 4), p divides h!² + 1 where $h = \frac{p-1}{2}$ |
| `MinusOneSquareExists` | Mod a prime p ≡ 1 (mod 4), −1 is a square |
