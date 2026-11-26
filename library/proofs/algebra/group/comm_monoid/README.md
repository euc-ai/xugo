# comm_monoid — a commutative monoid

The smallest structure the corpus states abstractly: one operation on
a carrier that commutes and associates, with an identity element. The
structure is the predicate `comm_monoid(op, e)` over its two
components, the operation and the identity; a law is a theorem with
that predicate as antecedent; an instance is a theorem of a chapter of
the carrier (`comm_monoid(real_add, &0)`, in `real_ring`), and a consumer cites a law at
an instance bare — `By(comm_monoid.RightIdentity, AddMonoid)` — the apply rung
reading the operation off the goal and the identity off the instance.

The chapter is short by design. Its point is the two readings of the
same object: the identity carried as a component here, and the fold
mechanism's `monoidal_op op`, which names the identity by Hilbert choice
(`neutral_elem op`) so that a fold can be stated from the operation alone.
`Neutral` says the two identities agree, `Monoidal` and `FromMonoidal`
carry a monoid across in each direction, and a ring's two fold
instances are read through them. The power is defined here once, for
every commutative monoid.

## The structures and their axioms

Every law of the monoid is proved once, for a commutative monoid on a
SET — `comm_monoid_on(c, op, e)`, the same three axioms for the members
of `c`, which holds the identity and is closed under the operation — and
stated beside it for the whole type, where it reads unguarded: the
whole-type monoid is the monoid on `𝕌`, and its law is the view of the
set's. The tables spell the whole-type statement; the set's member
guards each variable by membership in `c`. The bridge to the fold
mechanism stays on the whole type, where the fold and the choice-named
identity live; the power reads no carrier, and its laws are proved on a
set like every other law.

| member | statement |
|---|---|
| `CommMonoid` | `comm_monoid(op, e)` ⇔ `op` commutes, associates, and `e` is its left identity |
| `CommMonoidOn` | `comm_monoid_on(c, op, e)` ⇔ `e ∈ c`, `c` closed under `op`, the three axioms for members of `c` |
| `CommMonoidOnUniverse` | `comm_monoid(op, e) ⇔ comm_monoid_on(𝕌, op, e)` |
| `IdentityIn` | `e ∈ c` |
| `OpIn` | `x ∈ c ∧ y ∈ c ⇒ op(x, y) ∈ c` |

| whole type | on a set | statement |
|---|---|---|
| `Comm` | `CommOn` | `op(x, y) = op(y, x)` |
| `Assoc` | `AssocOn` | `op(x, op(y, z)) = op(op(x, y), z)` |
| `LeftIdentity` | `LeftIdentityOn` | `op(e, x) = x` |

## What the axioms give

| whole type | on a set | statement |
|---|---|---|
| `RightIdentity` | `RightIdentityOn` | `op(x, e) = x` |
| `LeftComm` | `LeftCommOn` | `op(x, op(y, z)) = op(y, op(x, z))` |

## The homomorphic image of a commutative monoid

The homomorphic image of a commutative monoid is one. A map `f` that
carries `c` onto `d`, the operation of a commutative monoid on `c` to a
second operation `op₂` and its identity to `e₂`, makes `d` a commutative
monoid under `op₂` with identity `e₂`. Nothing is asked of `op₂` off the
image, and `f` need not be injective. The image holds `e₂` because `e₂`
is `f(e)`. Each other condition quantifies over points of the image, and
`set_image`'s pull-backs turn it into a condition at the values of
points of `c`, where the map's law makes it the source's own condition.

| member | statement |
|---|---|
| `ImageCommMonoidOn` | `comm_monoid_on(c, op, e) ∧ image(f, c) = d ∧ (∀x y. x ∈ c ∧ y ∈ c ⇒ f(op(x, y)) = op₂(f(x), f(y))) ∧ f(e) = e₂ ⇒ comm_monoid_on(d, op₂, e₂)` |

## The bridge to the fold mechanism

| member | statement |
|---|---|
| `Neutral` | `neutral_elem(op) = e` |
| `Monoidal` | `monoidal_op(op)` |
| `FromMonoidal` | `monoidal_op(op) ⇒ comm_monoid(op, neutral_elem(op))` |

## The power

`x ^ n` is `x` combined with itself `n` times — `monoid_pow(op, e, x, n)`,
by recursion on `n`: `x ^ 0 = e` and `x ^ suc(n) = op(x, x ^ n)`. The
operation and the identity are implicit: under a law here they are the
structure's components, and a chapter at an instance binds them once
(`family.WithInstance`) and writes `z ^ n`.

| member | statement |
|---|---|
| `MonoidPowDef` | `x ^ 0 = e`, `x ^ suc(n) = op(x, x ^ n)` |
| `MonoidPowersDef` | `monoid_powers(op, e, x)` = the powers `x ^ n` for every `n` |
| `PowIn` | `x ∈ c ⇒ x ^ n ∈ c` |
| `MapPow` | `h(e) = e₂ ∧ (∀u v. h(op(u, v)) = op₂(h(u), h(v))) ⇒ h(x ^ n) = monoid_pow(op₂, e₂, h(x), n)` |

| whole type | on a set | statement |
|---|---|---|
| `PowOne` | `PowOneOn` | `x ^ 1 = x` |
| `PowTwo` | `PowTwoOn` | `x ^ 2 = op(x, x)` |
| `PowAdd` | `PowAddOn` | `x ^ (m + n) = op(x ^ m, x ^ n)` |
| `MulPow` | `MulPowOn` | `op(x, y) ^ n = op(x ^ n, y ^ n)` |
| `PowPow` | `PowPowOn` | `(x ^ m) ^ n = x ^ (m * n)` |
| `IdentityPow` | `IdentityPowOn` | `e ^ n = e` |
| `PowInverse` | `PowInverseOn` | `op(x, y) = e ⇒ op(x ^ n, y ^ n) = e` |

The laws of exponents are inductions on an exponent. `PowAdd` runs on
`m`, associativity carrying one more factor of `x` past `x ^ m`;
`PowPow` runs on `n`, where `m · suc(n) = m + m · n` hands the step to
`PowAdd`; `MulPow` is the one law that needs the operation to commute,
its step regrouping four factors. `MapPow` asks for no structure at
all, only that the map keep the identity and carry the operation, so it
carries powers along any such map. Its statement spells the second
power with its components (`monoid_pow(op₂, e₂, …)`): the short `x ^ n`
reads `op` and `e`, the first operation's.
