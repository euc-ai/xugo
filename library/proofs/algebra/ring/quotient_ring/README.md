# quotient_ring — the ring of cosets of an ideal, its projection, and the field at a maximal ideal

An ideal `I` of a ring `R` cuts its carrier `c = R.carrier` into its cosets `x + I`, the
left cosets of `I` in the additive group, and the cosets are a ring: two
cosets add as sets, `set_mul(R.add, s, t)`, as the quotient group adds
them; they multiply as the set of products pushed back onto a coset,
`quotient_mul(I, s, t) = set_mul(R.add, set_mul(R.mul, s, t), I)`, which for
`x + I` and `y + I` is `x * y + I`; the coset `one + I` is the one and
`I` itself the zero. That ring is `R/I` (`QuotientRingOn`), a ring on
the set `left_cosets(R.add, c, I)` and nothing else: the carrier is a set
of subsets of the type, and no type carries it (`algebra/group/quotient_group`'s
README holds the argument). Its laws come from `R`'s: the map
`x ↦ x + I` carries the six operations of `R` to the coset operations,
and the image of a commutative ring along such a map is one
(`ring_homomorphism.ImageCommRingOn`). The same map is a ring
homomorphism onto it with kernel `I`. At a prime ideal the cosets form an integral
domain, and at a maximal ideal a field: the inverse of a coset `x + m`
with `x ∉ m` is chosen among the cosets that multiply it to `one + m`.
The inverse of the zero coset is the zero coset, as a field's convention
asks.

The product of cosets is choice-free, as the quotient group's is: the
set of products `(x + i) * (y + j)` is not itself a coset, only a
subset of `x * y + I`, and adding `I` fills it out. The inverse must
choose, since a map returns one value: `QuotientInverseExists` shows that
a coset does what the choice asks, and `QuotientInvCoset` reads the two
laws of `quotient_inv` off the choice.

The quotient is the ring record `ideal_quotient_ring(R, I)` — the
coset sum, `I`, the coset negation, `quotient_mul(I)`, `one + I`, the
coset difference, on `left_cosets(R.add, R.carrier, I)` — and
`ideal_quotient_field(R, I)` adds the inverse and the division; a
statement writes `comm_ring_on(ideal_quotient_ring(R, I))`. The
operations take the ring's components implicitly: under a law over a
ring `R` the text writes `quotient_mul(I, s, t)`, `quotient_sub(s, t)`,
`quotient_inv(R.carrier, I, s)`; the cosets themselves are the group
chapter's `left_coset(R.add, x, I)`, spelled at the addition, since
under a ring the bare coset would read the product.

## The operations and the records

| member | statement |
|---|---|
| `QuotientMulDef` | `quotient_mul(add, mul, I, s, t) = set_mul(add, set_mul(mul, s, t), I)` |
| `QuotientSubDef` | `quotient_sub(add, neg, s, t) = set_mul(add, s, set_inv(neg, t))` |
| `QuotientInvDef` | `quotient_inv(add, mul, one, c, I, s) = COND(s = I, I, εt. t ∈ left_cosets(add, c, I) ∧ quotient_mul(add, mul, I, t, s) = left_coset(add, one, I))` |
| `QuotientDivDef` | `quotient_div(add, mul, one, c, I, s, t) = quotient_mul(add, mul, I, s, quotient_inv(add, mul, one, c, I, t))` |
| `IdealQuotientRingDef` | `ideal_quotient_ring(R, I) = mk_ring(set_mul(R.add), I, set_inv(R.neg), quotient_mul(R.add, R.mul, I), left_coset(R.add, R.one, I), quotient_sub(R.add, R.neg), left_cosets(R.add, R.carrier, I))`: R/I as a ring record |
| `IdealQuotientFieldDef` | `ideal_quotient_field(R, I)`: the same cosets and operations with the coset inverse `quotient_inv(R.add, R.mul, R.one, R.carrier, I)` and the coset division `quotient_div(R.add, R.mul, R.one, R.carrier, I)`, a field record |
| `IdealQuotientProjectionDef` | `ideal_quotient_projection(R, I, a) = a + I` |

## The cosets of an ideal

| member | statement |
|---|---|
| `IdealSubgroup` | `ring_ideal(R, I) ⇒ subgroup(additive_group(R), I)` |
| `IdealNormal` | `ring_ideal(R, I) ⇒ normal_subgroup(additive_group(R), I)` |
| `CosetEqIff` | `ring_ideal(R, I) ∧ x ∈ R.carrier ∧ y ∈ R.carrier ⇒ (left_coset(R.add, x, I) = left_coset(R.add, y, I) ⇔ x - y ∈ I)` |
| `CosetEqIdealIff` | `ring_ideal(R, I) ∧ x ∈ R.carrier ⇒ (left_coset(R.add, x, I) = I ⇔ x ∈ I)` |
| `QuotientMulCoset` | `ring_ideal(R, I) ∧ x ∈ R.carrier ∧ y ∈ R.carrier ⇒ quotient_mul(I, left_coset(R.add, x, I), left_coset(R.add, y, I)) = left_coset(R.add, x * y, I)` |
| `QuotientSubCoset` | `ring_ideal(R, I) ∧ x ∈ R.carrier ∧ y ∈ R.carrier ⇒ quotient_sub(left_coset(R.add, x, I), left_coset(R.add, y, I)) = left_coset(R.add, x - y, I)` |

## The quotient ring and its projection

| member | statement |
|---|---|
| `QuotientRingOn` | `ring_ideal(R, I) ⇒ comm_ring_on(ideal_quotient_ring(R, I))` |
| `ProjectionHomomorphism` | `ring_ideal(R, I) ⇒ ring_homomorphism(R, ideal_quotient_ring(R, I), ideal_quotient_projection(R, I))` |
| `ProjectionKernel` | `ring_ideal(R, I) ⇒ ring_kernel(I, R.carrier, ideal_quotient_projection(R, I)) = I` |
| `IdealQuotientProjection` | `comm_ring_on(R) ∧ ring_ideal(R, I) ⇒` the projection is a ring map from R onto `ideal_quotient_ring(R, I)` with kernel I |
| `QuotientCarrierCardLe` | `card_le(ideal_quotient_ring(R, I).carrier, R.carrier)`, the cosets an image of the carrier |

## The isomorphism theorems

The first isomorphism theorem names its map: a ring map onto E induces `induced_map(ψ)`, ψ at the chosen member of a coset, so the isomorphism is computed on cosets and not only asserted; the two rings may sit on different types. An automorphism carrying one ideal onto another induces the isomorphism of the quotients the same way.

| member | statement |
|---|---|
| `QuotientFirstIso` | a ring map `ψ` from R onto E ⇒ `induced_map(ψ)` is a ring isomorphism from `ideal_quotient_ring(R, ring_kernel(E.zero, R.carrier, ψ))` to E, and it sends the coset of `r` to `ψ(r)` |
| `KernelQuotientImage` | a ring map identifies the source modulo its kernel with its image, a subring of the target |
| `QuotientAutoIso` | a ring automorphism `α` of R with `image(α, J₁) = J₂`, both ideals ⇒ the map induced by `r ↦ α(r) + J₂` is a ring isomorphism R/J₁ → R/J₂ sending `r + J₁` to `α(r) + J₂` |

## Prime and maximal ideals

| member | statement |
|---|---|
| `QuotientDomain` | `prime_ideal(R, p) ⇒ integral_domain_on(ideal_quotient_ring(R, p))` |
| `QuotientInverseExists` | `maximal_ideal(R, m) ∧ x ∈ R.carrier ∧ x ∉ m ⇒ ∃t. t ∈ left_cosets(R.add, R.carrier, m) ∧ quotient_mul(m, t, left_coset(R.add, x, m)) = left_coset(R.add, R.one, m)` |
| `QuotientInvCoset` | `maximal_ideal(R, m) ∧ x ∈ R.carrier ∧ x ∉ m ⇒ quotient_inv(R.carrier, m, left_coset(R.add, x, m)) ∈ left_cosets(R.add, R.carrier, m) ∧ quotient_mul(m, quotient_inv(R.carrier, m, left_coset(R.add, x, m)), left_coset(R.add, x, m)) = left_coset(R.add, R.one, m)` |
| `IdealQuotientFieldRing` | `field_ring(ideal_quotient_field(R, I)) = ideal_quotient_ring(R, I)`: the ring of the quotient field is the quotient ring |
| `QuotientFieldOn` | `maximal_ideal(R, m) ⇒ field_on(ideal_quotient_field(R, m))` |

A coset `x + m` with `x ∉ m` has an inverse because `x` is a unit modulo
the maximal ideal (`ring_ideal.MaximalUnitModulo`). The local ring chapter
reads the field at the non-units of a local ring as its residue field.

## Residues in a subfield

Inside a ring, take a subring S containing a field k under the ring's operations. `rational_ideal(R, k, S, I)` says that I is a proper ideal of S whose residues all lie in k — each member of S congruent modulo I to a member of k — so that S/I is k: I is the ideal of a k-rational point. A proper ideal of S meets k only at zero; the ideal of a k-rational point is maximal and is the kernel of a ring map S → k fixing k; and the kernel of such a map is the ideal of a k-rational point, with the map's values as residues.

| member | statement |
|---|---|
| `RationalIdealDef` | `rational_ideal(R, k, S, I) ⇔ ring_ideal(restrict_ring(R, S), I) ∧ R.one ∉ I ∧ (∀x. x ∈ S ⇒ ∃y. y ∈ k ∧ x + -y ∈ I)` |
| `FieldResiduesMaximal` | the ideal of a k-rational point of a subring S ⊇ k, k a field, is maximal |
| `ProperIdealMeetsFieldAtZero` | a proper ideal of S ⊇ k meets the field k only at zero |
| `FieldResiduesHomomorphism` | the ideal of a k-rational point of S ⊇ k is the kernel of a ring map S → k fixing k |
| `KernelFieldResidues` | the kernel of a ring map S → k fixing k is the ideal of a k-rational point of S, each member congruent modulo it to its value |

## The index of an ideal

The index of an ideal is `ideal_index(R, I) = card(left_cosets(R.add, R.carrier, I))`, the
number of its cosets — a count only when they are finitely many, so a statement about it
carries `finite(left_cosets(R.add, R.carrier, I))` beside it. Read in the additive group the
index is multiplicative, so finiteness passes up to a larger ideal and a strict enlargement
lowers the index; so an increasing chain above an ideal of finite index stabilizes, and a
strict inclusion `J ⊆ I` with finitely many cosets of `J` in `I` has a simple layer above
`J`. A prime ideal of finite index is maximal: its quotient is a finite domain, hence a
field (`integral_domain.FiniteDomainIsField`).

| member | statement |
|---|---|
| `IdealIndexDef` | `ideal_index(R, I) = card(left_cosets(R.add, R.carrier, I))`: the number of cosets of `I`, when they are finitely many |
| `FiniteQuotientAboveIdeal` | `ring_ideal(R, I) ∧ ring_ideal(R, J) ∧ I ⊆ J ∧ finite(left_cosets(R.add, R.carrier, I)) ⇒ finite(left_cosets(R.add, R.carrier, J))` |
| `StrictIdealInclusionLowersIndex` | `ring_ideal(R, I) ∧ ring_ideal(R, J) ∧ I ⊆ J ∧ I ≠ J ∧ finite(left_cosets(R.add, R.carrier, I)) ⇒ ideal_index(R, J) < ideal_index(R, I)` |
| `FiniteIndexPrimeMaximal` | `prime_ideal(R, p) ∧ finite(left_cosets(R.add, R.carrier, p)) ⇒ maximal_ideal(R, p)` |
| `FiniteIndexChainStabilizes` | `ring_ideal(R, I) ∧ finite(left_cosets(R.add, R.carrier, I)) ∧ I ⊆ C(0) ∧ (∀n. ring_ideal(R, C(n)) ∧ C(n) ⊆ C(n + 1)) ⇒ ∃N. ∀n. N ≤ n ⇒ C(n) = C(N)` |
| `FiniteQuotientHasSimpleLayer` | `ring_ideal(R, I) ∧ ring_ideal(R, J) ∧ J ⊆ I ∧ J ≠ I ∧ finite(left_cosets(R.add, I, J)) ⇒ ∃H. ideal_cover(R, J, H) ∧ H ⊆ I` |
| `IdealsAboveFiniteIndex` | Finitely many ideals lie above an ideal of finite index |
