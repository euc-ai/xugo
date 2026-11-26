# dirichlet_character — Dirichlet characters modulo q and their orthogonality relations

A Dirichlet character modulo q is a function χ from the natural numbers
to ℂ that is completely multiplicative, has period q, and vanishes
exactly at the numbers not coprime to q. That is the arithmetic
definition, and `dirichlet_character(q, χ)` is it. The characters mod q
are the characters of the group of units mod q, read at a number's
residue and extended by 0 (`CharacterIffGroupCharacter`), one to one
(`ExtensionBijective`); through that
correspondence the count and the orthogonality relations of
`group_character` become statements about residues: there are φ(q)
characters, a non-principal one sums to 0 over a period, so its partial
sums are bounded by φ(q), and the sum of conj(χ(a))·χ(n) over the
characters picks out the residue class of a.

The principal character is the one that is 1 at every number coprime to
q (`PrincipalCharacter`); it has no constant, and "χ is not principal" is written
`∃n. nat_coprime(n, q) ∧ χ(n) ≠ &1`. A real character is one with
`∀n. im(χ(n)) = &0`.

## The definition (definitions.go)

| constant | reading |
|---|---|
| `dirichlet_character(q, χ)` | χ is completely multiplicative, `χ(n + q) = χ(n)`, and `χ(n) = 0` exactly when n is not coprime to q |

## Values (characters.go)

| member | statement |
|---|---|
| `CharacterMul` | `∀q m n:num. ∀χ:(num → complex). dirichlet_character(q, χ) ⇒ χ(m * n) = χ(m) * χ(n)` |
| `CharacterPeriodic` | `∀q n:num. ∀χ:(num → complex). dirichlet_character(q, χ) ⇒ χ(n + q) = χ(n)` |
| `CharacterEqZero` | `∀q n:num. ∀χ:(num → complex). dirichlet_character(q, χ) ⇒ (χ(n) = &0 ⇔ ¬nat_coprime(n, q))` |
| `CharacterAtOne` | `∀q:num. ∀χ:(num → complex). dirichlet_character(q, χ) ⇒ χ(1) = &1` |
| `CharacterCongruent` | `∀q m n:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ m ≡ n (mod q) ⇒ χ(m) = χ(n)` |
| `CharacterPow` | `∀q n k:num. ∀χ:(num → complex). dirichlet_character(q, χ) ⇒ χ(n ^ k) = χ(n) ^ k` |
| `CharacterUnitModulus` | `∀q n:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ nat_coprime(n, q) ⇒ \|χ(n)\| = &1 ∧ χ(n) ^ totient(q) = &1` |
| `CharacterAbsLessEqOne` | `∀q n:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ⇒ \|χ(n)\| ≤ &1` |
| `PrincipalCharacter` | `∀q:num. dirichlet_character(q, λn:num. COND(nat_coprime(n, q), complex_of_real(&1), &0))` |
| `CharacterClosure` | `∀q:num. ∀χ ψ:(num → complex). dirichlet_character(q, χ) ∧ dirichlet_character(q, ψ) ⇒ dirichlet_character(q, λn:num. χ(n) * ψ(n)) ∧ dirichlet_character(q, λn:num. conj(χ(n)))` |

## The characters of the units mod q (characters.go)

In `ExtensionBijective`, «extendCharacter» reads a function ω at a
number's residue mod q and extends it by 0 off the numbers coprime to q;
it maps «unitCharacters», the characters of `units_mod(q)`, one to one
onto «dirichletCharacters», the Dirichlet characters mod q. In
`CharacterSumOverResidues`, «periodResidues» is the set of residues
below q.

| member | statement |
|---|---|
| `CharacterIffGroupCharacter` | `∀q:num. ∀χ:(num → complex). 0 < q ⇒ (dirichlet_character(q, χ) ⇔ ∃ω:(num → complex). group_character(units_mod(q), ω) ∧ χ = λn:num. COND(nat_coprime(n, q), ω(rem(n, q)), &0))` |
| `ExtensionBijective` | `∀q:num. 0 < q ⇒ image(«extendCharacter», «unitCharacters») = «dirichletCharacters» ∧ injective_on(«unitCharacters», «extendCharacter»)` |
| `CharacterCount` | `∀q:num. 0 < q ⇒ finite({χ:num → complex \| dirichlet_character(q, χ)}) ∧ card({χ:num → complex \| dirichlet_character(q, χ)}) = totient(q)` |
| `CharacterSumOverResidues` | `∀q:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ⇒ Σ_{n∈«periodResidues»} χ(n) = COND(∀n:num. nat_coprime(n, q) ⇒ χ(n) = &1, complex_of_real(&totient(q)), &0)` |
| `CharacterPartialSumsBounded` | `∀q N:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1) ⇒ \|Σ_{n∈1 .. N} χ(n)\| ≤ &totient(q)` |
| `CharacterOrthogonality` | `∀q a n:num. 0 < q ∧ nat_coprime(a, q) ⇒ Σ_{χ∈{χ:num → complex \| dirichlet_character(q, χ)}} conj(χ(a)) * χ(n) = COND(n ≡ a (mod q), complex_of_real(&totient(q)), &0)` |

## Real characters (characters.go)

| member | statement |
|---|---|
| `RealCharacterValues` | `∀q n:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∀m:num. im(χ(m)) = &0) ⇒ χ(n) = &0 ∨ χ(n) = &1 ∨ χ(n) = -&1` |
| `NonRealCharacterSquare` | `∀q:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ (∃n:num. im(χ(n)) ≠ &0) ⇒ ∃n:num. nat_coprime(n, q) ∧ χ(n) * χ(n) ≠ &1` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
