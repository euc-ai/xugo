# homotopy_group — the spheres of a Kan complex at a vertex, homotopy between them, the homotopy groups, and the map a simplicial map induces

At a vertex `x₀` of a simplicial set `X` the n-spheres are the
n-simplices every face of which is the base simplex
`base_simplex(x₀, n − 1)`, `simplicial_sphere(X, x₀, n)`, written
`simplicial_sphere(x₀, n)` where `X` is the one simplicial set in
scope; at `n = 0` every vertex is one. Two simplices are homotopic,
`simplicial_homotopic(X, x₀, n, x, y)`, when an
(n+1)-simplex has `x` as its n-th face, `y` as its (n+1)-th and the
base simplex below; at `n = 0` an edge from `y` to `x`. A simplex
homotopic to a sphere is a sphere, a sphere is homotopic to itself by
its n-th degeneracy, and in a Kan complex the relation is symmetric and
transitive, each by filling one horn of dimension `n + 2`: so it is an
equivalence on the spheres, and `simplicial_homotopy_group(X, x₀, n)` is
the set of its classes, `πₙ(X, x₀)`.

For `0 < n` the classes multiply: the product of the classes of two
spheres `x` and `y` is the class of the n-th face of a product filler,
an (n+1)-simplex with `x` as its last face, `y` as its (n−1)-th and
the base simplex below `n − 1` — the filler of a horn, which exists in
a Kan complex. The operation reads representatives and a filler chosen
by `ε`; that the class of the n-th face does not depend on the filler
nor on the representatives is three horn fillings of dimension
`n + 2`, and `MulClass` is the one law through which the operation is
read afterwards. The unit is the class of the base simplex, a left
identity through the degeneracy `X.s(n, n − 1, y)`; the inverse of a
class is the class of the last face of a filler whose (n−1)-th face is
a representative and whose n-th face is the base simplex, a left
inverse by construction; associativity is one horn of dimension
`n + 2` holding three product fillers. So `πₙ(X, x₀)` is a group on a
set for `0 < n`, and abelian for `2 ≤ n`, where the free face `n − 2`
lets the product be computed in the other order. In `π₁` the product
of the classes of the edges `x` then `y` is the class of the edge the
2-simplex with `x` and `y` as its first two sides closes: the
composite in the order of traversal, the order the homotopy category
of a quasi-category composes in.

A simplicial map carries the base simplex to the base simplex, spheres
to spheres and homotopies to homotopies, so it induces a map of the
classes, `simplicial_homotopy_map(X, Y, F, x₀, n)`, a homomorphism for
`0 < n` since the image of a product filler is one.

## Spheres, homotopy and the classes

| member | statement |
|---|---|
| `SimplicialSphereDef` | `simplicial_sphere(X, x₀, n)` = the n-simplices with every face `base_simplex(x₀, n − 1)`, under `0 < n` |
| `SimplicialHomotopicDef` | `simplicial_homotopic(X, x₀, n, x, y)` ⇔ an (n+1)-simplex with faces the base simplex below `n`, `x` at `n`, `y` at `n + 1` |
| `SimplicialHomotopyGroupDef`, `SimplicialHomotopyUnitDef` | the quotient of the spheres by homotopy (`quotient_on`); the class of the base simplex |
| `BaseSphere`, `HomotopicSphere` | the base simplex is a sphere; a simplex homotopic to a sphere is a sphere |
| `SphereDegeneracyFaces` | the face table of a degeneracy `X.s(n, k, x)` of a sphere: an (n+1)-simplex with `x` at its faces `k` and `k + 1` and the base simplex at every other face |
| `SphereHornCompatible` | a horn of n-spheres is a horn: its members are n-simplices, and for `0 < n` every face the horn condition compares is the base simplex one dimension down, so the condition holds; at `n = 0` it compares nothing |
| `SphereHornFill` | in a Kan complex a horn of n-spheres has a filler: it is a horn (`SphereHornCompatible`), and `KanFill` fills it |
| `HomotopicRefl` | a sphere is homotopic to itself, by its n-th degeneracy |
| `HomotopicSym`, `HomotopicTrans` | in a Kan complex the relation is symmetric and transitive, each by one horn of dimension `n + 2`: an equivalence on the spheres |
| `HomotopicEquivalenceOn` | in a Kan complex homotopy is an equivalence on the spheres: reflexive there (`HomotopicRefl`), symmetric and transitive (`HomotopicSym`, `HomotopicTrans`) |
| `InHomotopyGroup` | a member of πₙ is the class of a sphere: the spheres are closed under homotopy (`HomotopicSphere`), so their quotient is their image under the class map (`equivalence.QuotientOnClosed`) |
| `ClassInHomotopyGroup` | the class of a sphere is a member of πₙ: the spheres are closed under homotopy (`HomotopicSphere`), and `equivalence.ClassInQuotientOnClosed` |
| `ClassEqIff` | the classes of two spheres agree exactly when they are homotopic: homotopy is an equivalence on the spheres (`HomotopicEquivalenceOn`), which are closed under it (`HomotopicSphere`), and `equivalence.ClassEqIffClosed` |
| `Representative` | a class has a chosen member, a sphere, whose class it is |

## The product and the group

| member | statement |
|---|---|
| `SimplicialHomotopyMulDef`, `SimplicialHomotopyInvDef` | the product by a chosen product filler; the inverse by a chosen filler with the base simplex as its n-th face |
| `ProductFillerExists` | for `0 < n` two spheres have a product filler, a filler of the horn of spheres with `x` at `n + 1` and `y` at `n − 1` |
| `ProductSphere` | the n-th face of a product filler is a sphere |
| `InverseFillerExists`, `InverseSphere` | for `0 < n` a sphere has an inverse filler, an (n+1)-simplex with the sphere at its face `n − 1` and the base simplex at `n` and below `n − 1`; its last face is a sphere |
| `ProductIndependent`, `ProductLeftHomotopic`, `ProductRightHomotopic` | the n-th face of a product filler of spheres is independent of the filler and of either sphere, up to homotopy |
| `MulClass` | the product of the classes of `x` and `y` is the class of the n-th face of any product filler |
| `MulIn`, `UnitIn` | πₙ is closed under the product and holds the unit |
| `LeftIdentity` | the unit is a left identity |
| `InvIn` | πₙ is closed under the inverse |
| `LeftInverse` | the inverse is a left inverse |
| `Assoc` | the product is associative |
| `GroupOn` | `group_on(mk_group(…, simplicial_homotopy_group(x₀, n)))` for `0 < n` |
| `JuxtapositionExists`, `MulClassLower` | for `2 ≤ n`: two spheres lie side by side in an (n+1)-simplex, `x` at its faces `n − 2`, `n − 1` and `y` at `n`, `n + 1`; an (n+1)-simplex with `x` at `n − 2`, `y` at `n` and the base simplex at `n + 1` and below `n − 2` has the product of their classes as the class of its face `n − 1` |
| `Commutative` | the product commutes for `2 ≤ n`, by three horns of dimension `n + 2` |
| `AbelianGroupOn` | `abelian_group_on(mk_group(…, simplicial_homotopy_group(x₀, n)))` for `2 ≤ n` |

## The induced map

| member | statement |
|---|---|
| `SimplicialHomotopyMapDef` | `simplicial_homotopy_map(X, Y, F, x₀, n, C)` = the class of the image of a representative |
| `MapSphere`, `MapHomotopic` | spheres to spheres at `F(0, x₀)`; homotopies to homotopies |
| `HomotopyMapClass` | the class of `x` goes to the class of `F(n, x)`, the target being Kan |
| `HomotopyMapIn` | `πₙ(X, x₀)` into `πₙ(Y, F(0, x₀))`, with no Kan condition |
| `HomotopyMapHom` | a group homomorphism for `0 < n` |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
