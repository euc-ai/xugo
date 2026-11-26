# lattice — ℤⁿ: the integer vectors, and what they inherit from ℝⁿ

The generic chapters read at the integer ring. The family binds the
ring's components once — `WithInstance(comm_ring.CommRing,
int_real_lift.CommRing)` reads `add ↦ int_add`, `zero ↦ &0`, `mul ↦
int_mul`, … off the instance theorem — so under that binding `u + v`,
`c • u`, `vec⟨n⟩(u)`, `⟪u, v⟫_n` mean `vec_add(int_add, u, v)`,
`vec_scalar_mul(int_mul, c, u)`, `vec⟨n⟩(&0, u)`, `dot⟨n⟩(int_add,
int_mul, u, v)` (the chapter's own statements use the last two), and a sum of
integers is `Σ_{i<n} f(i)`, the fold `int_sum`. Every law of `vec_space` and
`dot` stands here by citing that instance, or read at it as one value
(`dot.Sym.Read(int_real_lift.CommRing)`), exactly as the real chapters
cite theirs — ℤ is a second instance of those chapters.

What ℤ adds is its order, and ℤ's order is ℝ's: `x ≤ y` at ℤ is the
constant `int_le`, defined as `real_of_int(x) ≤ real_of_int(y)`. So the
chapter does not rebuild the order theory of the form; it carries it
across the embedding. `vec_of_int(u)` is the real sequence with u's
entries, and the one identity the chapter proves about it — the form of
two integer vectors, seen in ℝ, is the real form of their images — is
what every order fact of the form at ℤ is read through: positivity, and
that a null vector is orthogonal to everything. Definiteness is not read
that way, because it is not an order fact: with null-implies-orthogonal
in hand at ℤ, the equality of two integer vectors is decided by
non-degeneracy, a law of the generic chapter, and nothing about ℝ
enters — so `DotEqZero` is `dot.Definite` read at the integer ring. A real vector inside a statement of
this chapter spells its operations with their components in full,
`dot⟨n⟩(real_add, real_mul, vec_of_int(u), vec_of_int(v))`: the binding
is the integer ring's, the parser reads that prefix as ℝ's by the
arguments' types (constitution §Structures, "Implicit component
arguments"), and the explicit spelling is the visible sign that the
statement crosses into ℝⁿ.

On the Go side a member's vectors are `*Vec[Int, DimN]` parameters after the
dimension binder; the image of u is a real vector built in the body,
`a.VecAs[Real, DimN]("vec_of_int(u)")`, and a
real law is cited at it with the dimension read off the same binder,
`euclidean.DotPosLe.At(image)` (constitution §"The typed surface", the
dimension refinement).

## The definitional layer (definitions.go)

| constant | reading |
|---|---|
| `vec_of_int(u)` | `λi. real_of_int(u(i))` — the entrywise embedding ℤⁿ ↪ ℝⁿ |

## The two bridges (embed.go)

| member | statement |
|---|---|
| `DotIsSum` | `⟪u, v⟫_n = Σ_{i<n} u(i) * v(i)` — the bridge from the fold to Σ over ℤ |
| `DotBridge` | `real_of_int(⟪u, v⟫_n) = dot⟨n⟩(real_add, real_mul, vec_of_int(u), vec_of_int(v))` — both forms are sums over the active range; the integer sum crosses into ℝ term by term (`int_sum.IntSumBridge`), each product factor by factor (`int_construction.MulBridge`) |

## What the form does at ℤ (dot.go)

| member | statement |
|---|---|
| `DotPosLe` | `&0 ≤ ⟪u, u⟫_n` — the form at ℤ is positive semidefinite: the inequality is the inequality of the representatives, and the representative of the form is the real form of the image, positive semidefinite by `euclidean.DotPosLe` |
| `NullVectorOrthogonal` | `⟪u, u⟫_n = &0 ⇒ ⟪u, v⟫_n = &0` — an integer vector null for the form is orthogonal to every integer vector: both equations read through the embedding, and the real theorem at the images carries one to the other |
| `DotEqZero` | `vec⟨n⟩(u) ⇒ (⟪u, u⟫_n = &0 ⇔ u = vec_zero)` — on a dimension the form is definite: `dot.Definite` read at the integer ring, whose one hypothesis — a null vector is orthogonal to everything — is the chapter's `NullVectorOrthogonal`; no order fact, so nothing passes through ℝ |

## Where this chapter sits

Above `vector/dot` and `vector/euclidean` — ℤⁿ sits inside ℝⁿ, and the
chapter says so rather than proving ℝⁿ's order theory a second time —
above `int_num/int_real_lift`, whose `CommRing` is the instance the
family binds and the generic laws are read at, above
`int_num/int_construction`, whose bridges (`real_of_int` over `+`, `*`,
the numerals) carry the entries across, and above `iterate/int/int_sum`,
whose `IntSumBridge` carries the sum. It is not a chapter of
`int_num/`: its objects are vectors, and its definitional layer is the
vector chapters' read at ℤ.
