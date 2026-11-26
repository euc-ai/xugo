# quadratic_residue — the Legendre symbol, Euler's criterion, Gauss's lemma and the values at −1 and 2

The Legendre symbol $\left(\frac{a}{p}\right)$ is 0 when the prime p divides a, 1 when a is a
nonzero square mod p, and −1 otherwise. The chapter reads congruences mod
p as equations in a field with p elements. Euler's criterion mod p is
then the finite field's criterion read back through that map, and the
symbol's multiplicativity and its value at −1 follow from it; Gauss's
lemma counts the residues that multiplication by a sends past p/2, and
gives the value at 2.

## Members

| Member | Statement |
|---|---|
| `LegendreSymbolDef` | `legendre_symbol`: int → num → int |

## Euler's criterion

Euler's criterion is read in a field of p elements, which has
characteristic p and onto which the integers map, two integers having the
same image exactly when they are congruent mod p
(`finite_field.PrimeSizeCharacteristic`, `finite_field.IntegerMapOnto`,
`finite_field.IntegerMapEqIff`): there an integer is a square mod p exactly
when its image is a square (`finite_field.SquareModIff`), and $a^{\frac{p-1}{2}}$
is ±1 according as a's image is a square, which is the image of $\left(\frac{a}{p}\right)$.
Multiplicativity and the value at −1 follow, since two values between −1
and 1 congruent modulo an odd prime are equal
(`int_congruence.EqOfCongruentSigns`).

| Member | Statement |
|---|---|
| `LegendreInField` | For a field of prime size p, $\left(\frac{a}{p}\right)$ maps to 0, 1 or −1 as the image of a is zero, a nonzero square, or neither |
| `EulerCriterion` | Euler's criterion: for an odd prime p, $a^{\frac{p-1}{2}} \equiv \left(\frac{a}{p}\right) \pmod{p}$ |
| `LegendreValues` | The Legendre symbol takes only the values 0, 1 and −1 |
| `LegendreOne` | $\left(\frac{1}{p}\right) = 1$ for every p other than 1 |
| `LegendreCongruent` | Integers congruent mod p have the same Legendre symbol |
| `LegendreMul` | For an odd prime p, $\left(\frac{ab}{p}\right) = \left(\frac{a}{p}\right)\left(\frac{b}{p}\right)$ |
| `LegendrePow` | The symbol of a power is the power of the symbol: $\left(\frac{a^k}{p}\right) = \left(\frac{a}{p}\right)^k$ for an odd prime p |
| `LegendreMinusOne` | For an odd prime p, $\left(\frac{-1}{p}\right) = (-1)^{\frac{p-1}{2}}$ |

## Sums of Legendre symbols

A nonresidue e exists modulo every odd prime: a field of p elements has a
nonzero non-square, and the integers map onto it. Multiplying by e
permutes the residues below p and reverses every symbol, so the sum of the
symbols over the residues is its own negative, and so 0.

| Member | Statement |
|---|---|
| `NonresidueExists` | For an odd prime p, some natural number e has $\left(\frac{e}{p}\right) = -1$ |
| `LegendreSumZero` | For an odd prime p, the symbols $\left(\frac{a}{p}\right)$ for a < p add up to 0 |

## Gauss's lemma and the value at 2

The product of the residues of a, 2a, …, h · a modulo p = 2h + 1 is
computed twice. Each residue is congruent to k · a, so the product is
a ^ h · h!. Each residue is also ± its absolute least residue, and those
are 1, …, h in some order, so the product is (−1) ^ μ · h!. Cancelling h!,
which p does not divide, and applying Euler's criterion gives
$\left(\frac{a}{p}\right) = (-1)^\mu$. At a = 2 the doubles stay below p, so μ = h − ⌊h/2⌋,
which is even exactly when p ≡ ±1 (mod 8).

| Member | Statement |
|---|---|
| `LeastResiduesPermute` | The absolute least residues of a, 2a, …, h · a are 1, …, h in some order |
| `GaussLemma` | Gauss's lemma: $\left(\frac{a}{p}\right) = (-1)^\mu$, where μ counts the k ≤ h whose residue k · a mod p exceeds h |
| `LegendreTwo` | The second supplement: $\left(\frac{2}{p}\right) = 1$ exactly when p ≡ ±1 (mod 8) |
| `LegendreTwoSign` | For an odd prime p, $\left(\frac{2}{p}\right) = (-1)^{\frac{p^2-1}{8}}$ |
