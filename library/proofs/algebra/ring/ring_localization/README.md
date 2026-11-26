# ring_localization — the ring of fractions of a ring on a set, with denominators in a multiplicative set

A fraction `r / u` is the class of a pair, `r` in the carrier `c = R.carrier` of a ring `R`
and `u` in a multiplicative set `s ⊆ c`, under `(r, u) ~ (r', u')` ⇔ some
`t ∈ s` has `t * (r * u') = t * (r' * u)` — the fraction relation, an
equivalence on `c × s` (`FractionEquivalenceOn`). The classes are sets of
pairs, and the ring of fractions is the quotient of `c × s` by the
relation, relations/equivalence's `quotient_on`: a ring on a set, the
record `localized_ring(R, s)` of `fraction_add(c, s), …` on
`ring_localization(c, s)` (`LocalizationRing`). No type of fractions could carry it, since `c` and
`s` are variables; and no equality of types is ever asked: two rings of
fractions, at two multiplicative sets, are two sets of classes of one
type.

The operations choose nothing, as the quotient group's do: the sum of two
classes is the union of the classes of the sums of their
representatives. That the union is one class — the class of the sum of
any representatives — is a theorem (`FractionAddClass`), and every law
of the ring of fractions is read through the three class laws and
`FractionClassEq`.

## The definitions

| member | statement |
|---|---|
| `MultiplicativeSetDef` | `multiplicative_set(c, s)` ⇔ `s ⊆ c`, `one ∈ s`, closed under `*` |
| `PowersMultiplicative` | in a commutative ring, the powers of a member `x` form a multiplicative set, `multiplicative_set(R.carrier, monoid_powers(x))` |
| `fractionRelationDef` | `fraction_relation(c, s, p, q)` ⇔ `q ∈ c × s` and some `t ∈ s` has `t * (fst(p) * snd(q)) = t * (fst(q) * snd(p))` |
| `FractionClassDef` | `fraction_class(c, s, r, u)` = the class of `(r, u)` under `fraction_relation(c, s)` |
| `FractionClassMember` | `(x, y) ∈ fraction_class(mul, c, s, r, u)` ⇔ `x ∈ c`, `y ∈ s`, and some `t ∈ s` relates the pairs |
| `RingLocalizationDef` | `ring_localization(c, s)` = `quotient_on(c × s, fraction_relation(c, s))` |
| `RingLocalizationMember` | `X ∈ ring_localization(mul, c, s)` ⇔ `X` is the class of some `r ∈ c` over some `u ∈ s` |
| `FractionAddDef`, `FractionMulDef`, `FractionNegDef`, `FractionSubDef` | the operations on classes |
| `FractionZeroDef`, `FractionOneDef` | the classes of `zero / one` and `one / one` |
| `ToFractionDef` | `to_fraction(c, s, r)` = the class of `r / one` |

The relation asks its second pair to lie in `c × s`, so the class of any
pair lies in `c × s` and is its class inside `c × s`: the quotient is the
image of `c × s` under the class map, with no hypothesis.

## The ring

| member | statement |
|---|---|
| `FractionEquivalenceOn` | `multiplicative_set(c, s) ⇒ equivalence_on(c × s, fraction_relation(c, s))` |
| `FractionClassEq` | two classes are equal ⇔ their pairs are equivalent: the class law at `FractionEquivalenceOn` |
| `FractionClassCross` | two pairs whose cross products agree have one class |
| `FractionAddClass` | the sum of two classes is the class of the sum of representatives |
| `FractionMulClass` | and the product |
| `FractionNegClass` | and the negation |
| `FractionZeroIff` | `r / u` is zero ⇔ some `t ∈ s` has `t * r = zero` |
| `LocalizedRingDef` | `localized_ring(R, s) = mk_ring(fraction_add(R.add, R.mul, R.carrier, s), fraction_zero(R.zero, R.mul, R.one, R.carrier, s), fraction_neg(R.neg, R.mul, R.carrier, s), fraction_mul(R.mul, R.carrier, s), fraction_one(R.mul, R.one, R.carrier, s), fraction_sub(R.add, R.neg, R.mul, R.carrier, s), ring_localization(R.mul, R.carrier, s))` |
| `LocalizationRing` | the fractions form a ring on the set of classes |
| `ToFractionHomomorphism` | `r ↦ r / one` is a ring homomorphism |
| `DenominatorUnit` | `(u / one) * (one / u) = one / one` for `u ∈ s` |
| `DenominatorClearsFraction` | `(b / one) * (a / b) = a / one` for `b ∈ s` |

## Localization as a relation

`is_localization_on(R, S, L, ι)` describes a localization on any target
carrier. The source and target use the `ring_ops` records. The
map sends a multiplicative set to units, every target element admits a
fraction representation, and each element of its kernel is annihilated
by a denominator. The relation includes the zero ring and localization
at a set containing zero. `is_module_localization_on(R, Q, S', ρ, N, N', ν)`
is its companion for a module: `N'` over `S'` is `N` with the members of
`Q` inverted, along `ρ`. It asks the fraction and kernel conditions of
`ν` only; that `S'` is the localization of `R` is stated beside it, as
`is_localization_on`.

| member | statement |
|---|---|
| `IsLocalizationOnDef` | the multiplicative-set, homomorphism, unit, fraction-representation and kernel conditions |
| `IsModuleLocalizationOnDef` | `N'` a module over `S'`, `ν` linear over `R` with `N'` read through `ρ`, each member of `N'` times some `ρ(q)`, `q ∈ Q`, an image of `ν`, and each member of `N` that `ν` kills killed by some `q ∈ Q` |
| `ToFractionIsLocalization` | the concrete ring of fraction classes under `to_fraction` satisfies the relation |
| `LocalizationHomomorphismExtensional` | homomorphisms from a localization agree on its carrier when they agree on the original ring |
| `LocalizationUniversal` | a homomorphism sending denominators to units extends uniquely on the localization carrier |
| `LocalizationIsomorphism` | two localizations at the same denominators admit a unique comparison over the source ring, with `inverse_on` as its inverse |
| `LocalizationAtProduct` | localization at the powers of `f`, followed by the powers of the image of `g`, is localization at the powers of `f * g` |
| `LocalizationAtUnits` | if the denominators are already units, the original coefficient map is a ring isomorphism |
| `LocalizationCarrierCardLe` | `card_le(L.carrier, set_cross(R.carrier, S))`: every member is a fraction — card |

## The field of fractions

An integral domain's nonzero members form a multiplicative set, and its
fractions with every nonzero denominator form a field on their set,
`fraction_field(c)`: the inverse of a class `r / u` with `r` nonzero is
the class `u / r`, obtained by turning the class's pairs round, and the
zero class is its own inverse, as a field's convention asks.
`integral_element` reads a fraction field inside a given field instead, by
`fraction_field_carrier`; there the fractions K of a subring S are the
localization of S at its nonzero members, so a one-to-one ring map out of S
extends to K (`FractionFieldLift`). A domain
cancels the relation's witness, so two fractions are equal exactly when
their cross products are, and a fraction is zero exactly when its
numerator is; the embedding `r ↦ r / one` separates points by that
criterion. The ring of fractions at any
`s` is the record `localized_ring(R, s)`, and the field the record
`fraction_field_record(R)`, its eight operations taken at the nonzero
members.

| member | statement |
|---|---|
| `FractionInvDef` | `fraction_inv(c, s, X)` = the zero class at the zero class, else the pairs of `X` turned round |
| `FractionDivDef` | `fraction_div(c, s, X, Y) = fraction_mul(c, s, X, fraction_inv(c, s, Y))` |
| `FractionFieldDef` | `fraction_field(c) = ring_localization(c, c ∖ {zero})` |
| `FractionFieldRecordDef` | `fraction_field_record(R) = mk_field(fraction_add(…), fraction_zero(…), fraction_neg(…), fraction_mul(…), fraction_one(…), fraction_sub(…), fraction_inv(…), fraction_div(…), fraction_field(R.zero, R.mul, R.carrier))`, each operation at `R`'s components, `R.carrier` and `R.carrier ∖ {R.zero}` |
| `NonzeroMultiplicative` | `integral_domain_on(R) ⇒ multiplicative_set(R.carrier, R.carrier ∖ {R.zero})` |
| `DomainFractionClassMember` | in a domain, `(x, y) ∈ r / u` ⇔ `x, y ∈ c`, `y ≠ zero` and `r * y = x * u` |
| `DomainFractionZeroIff` | in a domain, for `u ≠ zero`: `r / u` is zero ⇔ `r = zero` |
| `DomainFractionEqIff` | in a domain, for nonzero denominators: `r / u = r' / u'` ⇔ `r * u' = r' * u` |
| `FractionInvClass` | `r, u` nonzero in a domain ⇒ `fraction_inv(c, c ∖ {zero}, r / u) = u / r` |
| `FractionField` | `integral_domain_on(R) ⇒ field_on(fraction_field_record(R))` |
| `ToFractionInjective` | `integral_domain_on(R) ⇒ injective_on(R.carrier, to_fraction(R.carrier, R.carrier ∖ {R.zero}))` |
| `FractionFieldLift` | inside a field `L`, a one-to-one ring map `φ` from a subring `S` into a field `T` extends to a subfield `K` that is the field of fractions of `S` (`fraction_field_carrier`), agreeing with `φ` on `S` |

## Maps and prime correspondence

A ring homomorphism sending source denominators into target denominators maps a fraction class to the union of the classes of its image representatives. The class law makes this a single class; no representative is selected. Extension and contraction identify primes of the localization with primes disjoint from the denominator set, including the degenerate localization when zero is inverted.

| member | statement |
|---|---|
| `FractionMapDef` | unite the classes of all image representatives |
| `FractionMapClass` | the image of a/u is φ(a)/φ(u) |
| `FractionMapHomomorphism` | the fraction map is a ring homomorphism — card |
| `FractionMapToFraction` | it commutes with the canonical ring maps — card |
| `FractionMapCompose` | the fraction map of χ ∘ φ is the fraction map of χ after that of φ |
| `FractionMapIdentity` | the identity fixes each fraction of the ring at s |
| `LocalizationPrimeCorrespondence` | extend a prime disjoint from the denominators, then contract to the same prime — card |
| `LocalizationPrimeCorrespondenceInverse` | contract a localization prime, then extend to the same prime — card |
