# local_ring — local rings on sets, and the local ring of fractions at a prime ideal

A ring `R` is local when one is not zero and a sum of two non-units
is a non-unit: `local_ring_on(R)`. In such a ring the non-units form the
one maximal ideal (`NonUnitsMaximal`); the definition asks only what an
instance checks. Every ring satisfying `is_localization_on` at the
complement of a prime ideal is local (`LocalizationAtPrimeLocal`).
For a representation `y * ι(s) = ι(a)`, the numerator lies outside the
prime exactly when `y` is a unit (`LocalizationAtPrimeUnit`). These
statements apply directly to the stalk ring of the structure sheaf.

| member | statement |
|---|---|
| `LocalRingOn` | `local_ring_on(R)` ⇔ a ring, `R.one ≠ R.zero`, a sum of non-units is a non-unit |
| `Ring`, `OneNotZero`, `NonUnitAdd` | the three axioms |
| `NonUnitsIdeal` | the non-units of a local ring form an ideal |
| `NonUnitsMaximal` | the non-units form the one maximal ideal |
| `PrimeComplementMultiplicative` | `prime_ideal(R, p) ⇒ multiplicative_set(R.carrier, R.carrier ∖ p)` |
| `LocalizationAtPrimeUnit` | a represented element `y * ι(s) = ι(a)` in a localization at `R.carrier ∖ p` is a unit iff `a ∉ p` |
| `LocalizationAtPrimeLocal` | `is_localization_on(R, R.carrier ∖ p, L, ι)` at a prime `p` implies that `L` is local |

## The residue field

The cosets of the non-units are the residue field, `residue_field(R)`;
it is a field on its set, the quotient ring chapter's field at a
maximal ideal read at the maximal ideal of non-units. The residue field
of the local ring of fractions at a prime `p` is the scheme chapters'
`κ(p)`, spelled as this constant at that ring.

| member | statement |
|---|---|
| `ResidueFieldDef` | `residue_field(R) = left_cosets(R.add, R.carrier, {x \| x ∈ R.carrier ∧ ¬ring_unit(R, x)})` |
| `ResidueFieldOn` | `local_ring_on(R) ⇒ field_on(restrict_field(ideal_quotient_field(R, the non-units), residue_field(R)))` |

## Nakayama's lemma

| member | statement |
|---|---|
| `Nakayama` | an ideal N that finitely many of its members generate modulo J, with N ⊆ J + I·N, is carried into J by some s ≡ one modulo I |
