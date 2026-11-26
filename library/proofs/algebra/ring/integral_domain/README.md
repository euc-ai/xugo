# integral_domain — a commutative ring on a set with no zero divisors

An integral domain is a commutative ring whose one is not its zero and
in which a product vanishes only when a factor does:
`integral_domain_on(R)` is `comm_ring_on(R)`, `R.one ≠ R.zero`, and
`x * y = R.zero ⇒ x = R.zero ∨ y = R.zero` for the members of
`R.carrier`. The ring is
the first conjunct, so every law of the ring chapter's carrier form
applies at a domain through `Ring`, and this chapter states only what
the absence of zero divisors adds: a nonzero factor cancels, and in a
finite domain every nonzero member is a unit. A field on a set is an
integral domain, since a nonzero factor's inverse strips it off a
vanishing product; the chapter states that bridge, and the ring of
fractions of a domain is a field on a set (`ring_localization`'s
`FractionField`).

The structure is stated on a set and nowhere on a whole type: the
domains the corpus meets — a field's carrier, a prime ideal's quotient,
a ring inside its field of fractions — are subsets of a type. The
structure is a predicate of a ring record: a member here binds the
record as `integral_domain_on(A)`, and the record's fields carry the
ring's symbols.

## The structure and its axioms

| member | statement |
|---|---|
| `IntegralDomainOn` | `integral_domain_on(R)` ⇔ `comm_ring_on(R)`, `R.one ≠ R.zero`, and `x * y = R.zero ⇒ x = R.zero ∨ y = R.zero` for members of `R.carrier` |
| `Ring` | `comm_ring_on(R)` |
| `OneNotZero` | `R.one ≠ R.zero` |
| `NoZeroDivisors` | `x ∈ R.carrier ∧ y ∈ R.carrier ∧ x * y = R.zero ⇒ x = R.zero ∨ y = R.zero` |

## What the axiom gives

| member | statement |
|---|---|
| `MulCancelLeft` | `x ∈ R.carrier ∧ y ∈ R.carrier ∧ z ∈ R.carrier ⇒ x ≠ R.zero ⇒ (x * y = x * z ⇔ y = z)` |
| `MulCancelRight` | `x ∈ R.carrier ∧ y ∈ R.carrier ∧ z ∈ R.carrier ⇒ x ≠ R.zero ⇒ (y * x = z * x ⇔ y = z)` |
| `FieldIntegralDomain` | `field_on(F) ⇒ integral_domain_on(field_ring(F))` |
| `FiniteDomainIsField` | `finite(c.carrier) ∧ a ∈ c.carrier ∧ a ≠ c.zero ⇒ ∃b. b ∈ c.carrier ∧ a * b = c.one`: in a finite domain every nonzero member has an inverse |
| `SubringOfFieldDomain` | A subring of a field is a domain |
| `SubringOfDomainIsDomain` | `subring(R, S) ⇒ integral_domain_on(restrict_ring(R, S))`: a subring of a domain is a domain |

Cancellation is the axiom read at a difference: `x * y = x * z` puts
`x * (y - z)` at zero, and with `x` nonzero the difference is zero. A
finite domain is a field: multiplication by a nonzero member is
injective on the carrier, so on a finite carrier it is onto, and what it
sends to one is the inverse.
