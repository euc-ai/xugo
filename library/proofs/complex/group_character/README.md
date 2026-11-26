# group_character — characters of a finite abelian group: extension from a subgroup, the two orthogonality relations, and their number

A character of a group G is a homomorphism from G to the nonzero complex
numbers. `group_character(G, χ)` asks that of χ on G's carrier and asks
χ to be 0 off it: a homomorphism is constrained only on the carrier, and
fixing the values elsewhere is what makes the characters of a finite
group a finite set of functions. Every group has the trivial character,
1 on the carrier (`TrivialCharacter`). The laws of a character on the carrier
— it is 1 at the identity and carries products, inverses and powers to
products, inverses and powers — are the homomorphism chapter's
(`group_homomorphism.MapOne`, `MapMul`, `MapInv`, `MapPow`), read at
`field_units(complex_field_ops)`; the product law, read once in ℂ's own
multiplication, is `CharacterMul`.

On a finite group a character's values are roots of unity, and its
value at an inverse is the conjugate (`CharacterConjugateInverse`). The
chapter's theorem is that a finite abelian group has enough characters:
a character of a subgroup extends to the group, one generator at a
time. With d the order of x modulo the subgroup, it extends to a
subgroup holding x with any value at x whose d-th power is its value at
xᵈ (`CharacterExtendsOneStep`), and ℂ has such a root
(`complex_polynomial.UnitPowerRoot`). No structure theorem is used.
So every element other than the identity is separated from it by a
character, the characters' values at a fixed element sum to 0 unless
the element is the identity, and counting $\sum_x \sum_\chi \chi(x)$ in both orders
gives as many characters as elements.

## The definition (definitions.go)

| constant | reading |
|---|---|
| `group_character(G, χ)` | `group_homomorphism(G, field_units(complex_field_ops), χ)`, and `χ(x) = 0` for x off `G.carrier` |

## Values and closure (characters.go)

| member | statement |
|---|---|
| `CharacterMul` | `∀G:group_ops(A). ∀χ:(A → complex). ∀x y:A. group_homomorphism(G, field_units(complex_field_ops), χ) ∧ x ∈ G.carrier ∧ y ∈ G.carrier ⇒ χ(x * y) = χ(x) * χ(y)` |
| `CharacterUnitModulus` | `∀G:group_ops(A). ∀χ:(A → complex). ∀x:A. group_homomorphism(G, field_units(complex_field_ops), χ) ∧ finite(G.carrier) ∧ x ∈ G.carrier ⇒ χ(x) ^ card(G.carrier) = &1 ∧ \|χ(x)\| = &1` |
| `CharacterConjugateInverse` | `∀G:group_ops(A). ∀χ:(A → complex). ∀x:A. group_homomorphism(G, field_units(complex_field_ops), χ) ∧ finite(G.carrier) ∧ x ∈ G.carrier ⇒ χ(x) * conj(χ(x)) = &1 ∧ χ(G.inv(x)) = conj(χ(x))` |
| `TrivialCharacter` | `∀G:group_on(A). group_character(G, λx:A. COND(x ∈ G.carrier, complex_of_real(&1), &0))` |
| `CharacterClosure` | `∀G:group_ops(A). ∀χ ψ:(A → complex). group_character(G, χ) ∧ group_character(G, ψ) ⇒ group_character(G, λx:A. χ(x) * ψ(x)) ∧ group_character(G, λx:A. conj(χ(x)))` |
| `CharactersFinite` | `∀G:group_ops(A). finite(G.carrier) ⇒ finite({χ:A → complex \| group_character(G, χ)})` |

## Extension and separation (characters.go)

| member | statement |
|---|---|
| `CyclicCharacter` | `∀G:group_ops(A). ∀x:A. group_on(G) ∧ finite(G.carrier) ∧ x ∈ G.carrier ∧ x ≠ G.one ⇒ ∃χ:(A → complex). group_character(restrict_group(G, cyclic_subgroup(G, x)), χ) ∧ χ(x) ≠ &1` |
| `CharacterExtendsOneStep` | `∀G:group_ops(A). ∀K:set(A). ∀χ:(A → complex). ∀x:A. ∀d:num. ∀w:complex. abelian_group_on(G) ∧ finite(G.carrier) ∧ subgroup(G, K) ∧ group_character(restrict_group(G, K), χ) ∧ x ∈ G.carrier ∧ (∀j:num. monoid_pow(G.mul, G.one, x, j) ∈ K ⇔ d ∣ j) ∧ w ^ d = χ(monoid_pow(G.mul, G.one, x, d)) ⇒ ∃K':set(A). ∃χ':(A → complex). subgroup(G, K') ∧ K ⊆ K' ∧ x ∈ K' ∧ group_character(restrict_group(G, K'), χ') ∧ (∀y:A. y ∈ K ⇒ χ'(y) = χ(y)) ∧ χ'(x) = w` |
| `CharacterExtends` | `∀G:group_ops(A). ∀K:set(A). ∀χ:(A → complex). abelian_group_on(G) ∧ finite(G.carrier) ∧ subgroup(G, K) ∧ group_character(restrict_group(G, K), χ) ⇒ ∃χ':(A → complex). group_character(G, χ') ∧ (∀y:A. y ∈ K ⇒ χ'(y) = χ(y))` |
| `SeparatingCharacter` | `∀G:group_ops(A). ∀x:A. abelian_group_on(G) ∧ finite(G.carrier) ∧ x ∈ G.carrier ∧ x ≠ G.one ⇒ ∃χ:(A → complex). group_character(G, χ) ∧ χ(x) ≠ &1` |

## The orthogonality relations and the count (characters.go)

| member | statement |
|---|---|
| `CharacterSum` | `∀G:group_ops(A). ∀χ:(A → complex). group_homomorphism(G, field_units(complex_field_ops), χ) ∧ finite(G.carrier) ⇒ Σ_{x∈G.carrier} χ(x) = COND(∀x:A. x ∈ G.carrier ⇒ χ(x) = &1, complex_of_real(&card(G.carrier)), &0)` |
| `CharacterSumOverCharacters` | `∀G:group_ops(A). ∀x:A. abelian_group_on(G) ∧ finite(G.carrier) ∧ x ∈ G.carrier ⇒ Σ_{χ∈{χ:A → complex \| group_character(G, χ)}} χ(x) = COND(x = G.one, complex_of_real(&card({χ:A → complex \| group_character(G, χ)})), &0)` |
| `CharacterCount` | `∀G:group_ops(A). abelian_group_on(G) ∧ finite(G.carrier) ⇒ card({χ:A → complex \| group_character(G, χ)}) = card(G.carrier)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
