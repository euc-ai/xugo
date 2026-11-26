# simplicial_set — simplicial sets with their identities, maps and sub-objects, the base simplex at a vertex, iterated faces, standard simplices and fixed-prefix cones

A simplicial set on a type `A` is one value of the record
`simplicial_ops(A)`, `mk_simplicial(simplices, d, s)`: under a binder
`X` of the type, `X.simplices(n)` is the set of n-simplices, and the two
total maps `X.d`, `X.s : num → num → A → A` give `X.d(n, i, x)`, the
i-th face of the n-simplex `x`, and `X.s(n, i, x)`, its i-th
degeneracy. `simplicial_set(X)` says the record is a simplicial set
(the domain's package comment says why the dimension is an argument of
the maps). What a map does off the sets or off the index range is
unconstrained, so each identity carries its membership and its index
bounds as hypotheses, closed by arithmetic wherever they are used. The
eight axioms are the two closures and the simplicial identities, each
stated on a simplex whose dimension is written `n + 1` or `n + 2`, so
that a truncated difference appears only as a face index under the
bound that makes it exact.

A sub-simplicial set of `X` is a family of subsets `Y : num → set(A)`
closed under the maps of `X`, and `restrict_simplicial_set(X, Y)`, the
subsets with the maps of `X`, is a simplicial set. A simplicial map
`simplicial_map(X, Y, F)` is a map `F : num → A → B` between simplicial
sets on two types, commuting with the faces and the degeneracies; maps
compose, restrict to sub-simplicial sets, and carry sub-simplicial sets
back. The base simplex at a vertex is the totally degenerate simplex,
the 0-th degeneracy iterated, and every face and every degeneracy of
it is the base simplex of the neighbouring dimension: it is the simplex
the homotopy groups are measured against. An iterated face removes the
top or the bottom k vertices of a simplex, the last or the 0-th face
taken k times, and a single face passes it as the face identity says.

The standard simplex `Δⁿ`, `standard_simplex(n)`, has for m-simplices
the monotone maps `[m] → [n]`, encoded as sequences `num → num` monotone
on `0 .. m`, bounded by `n` there, and zero past `m`. Its faces and
degeneracies precompose with the cofaces and codegeneracies of the
simplex category and are the same two constants at every `n`; the
padding is preserved without a truncation step, and the six identities
between the two constants hold of every sequence, each a case analysis
on an index closed by arithmetic. The k-th horn `simplex_horn(n, k)` is
`Δⁿ` restricted to the maps that miss a vertex other than `k`.

## The structure and its axioms

| member | statement |
|---|---|
| `SimplicialOps` | the record `simplicial_ops(A)`: `mk_simplicial(simplices, d, s)`, its parts read as the fields `X.simplices`, `X.d` and `X.s` |
| `SimplicialSet` | `simplicial_set(X)` ⇔ the two closures and the six identities — a structure |
| `FaceIn`, `DegeneracyIn` | `x ∈ X.simplices(n+1) ∧ i ≤ n+1 ⇒ X.d(n+1, i, x) ∈ X.simplices(n)`; `x ∈ X.simplices(n) ∧ i ≤ n ⇒ X.s(n, i, x) ∈ X.simplices(n+1)` |
| `FaceFace` | `d_i d_j = d_{j−1} d_i` for `i < j`, on `X.simplices(n+2)` |
| `DegeneracyDegeneracy` | `s_i s_j = s_{j+1} s_i` for `i ≤ j` |
| `FaceDegeneracyBelow`, `FaceDegeneracyEqual`, `FaceDegeneracyNext`, `FaceDegeneracyAbove` | `d_i s_j = s_{j−1} d_i` for `i < j`; `d_i s_i = id`; `d_{i+1} s_i = id`; `d_i s_j = s_j d_{i−1}` for `i > j + 1` |

## Edges and 2-simplices

An edge `e` runs from its face 1, `X.d(1, 1, e)`, to its face 0,
`X.d(1, 0, e)`. How the faces of the low-dimensional simplices fit together is read
off the identities once, here: the degenerate edge at a vertex, the
ends of an edge with the identity edge at each, the three edges of a 2-simplex meeting at its three vertices, and the two
degenerate 2-simplices on an edge, out of which the quasi-category
chapter builds its homotopies of edges.

| member | statement |
|---|---|
| `VertexDegeneracyFaces` | the degeneracy `X.s(0, 0, v)` of a vertex is an edge from `v` to `v`: `DegeneracyIn`, `FaceDegeneracyEqual` and `FaceDegeneracyNext`, each at the index 0 |
| `EdgeEndIdentities` | the two ends of an edge are vertices, and the identity edge at each end starts and ends there |
| `TwoSimplexFaceEnds` | the three edges of a 2-simplex `w` meet at its three vertices: its three faces are edges (`FaceIn`), and each shared vertex is one face identity (`FaceFace`) — faces 1 and 2 start at the vertex 0 (the pair `(1, 2)`), face 2 ends at the vertex 1 where face 0 starts (`(0, 2)`), and faces 1 and 0 end at the vertex 2 (`(0, 1)`) |
| `EdgeLastDegeneracyFaces` | the last degeneracy `X.s(1, 1, f)` of an edge is a 2-simplex with faces `X.s(0, 0, X.d(1, 0, f))`, `f` and `f` |
| `EdgeFirstDegeneracyFaces` | the first degeneracy `X.s(1, 0, g)` of an edge is a 2-simplex with faces `g`, `g` and `X.s(0, 0, X.d(1, 1, g))` |

## Sub-simplicial sets and simplicial maps

| member | statement |
|---|---|
| `SubSimplicialSetDef` | `sub_simplicial_set(X, Y)` ⇔ `Y(n) ⊆ X.simplices(n)`, closed under the faces and the degeneracies of `X` |
| `RestrictSimplicialSetDef` | `restrict_simplicial_set(X, Y) = mk_simplicial(Y, X.d, X.s)`: the simplices `Y` with the faces and degeneracies of `X` |
| `SubSimplicialSet` | a sub-simplicial set `Y` of a simplicial set `X` is a simplicial set under the restricted maps, `simplicial_set(restrict_simplicial_set(X, Y))`: the two closures are its own, and each identity holds of a simplex of `Y` because it lies in `X`, where the axiom states it |
| `SubSimplicialSetRefl` | a simplicial set is a sub-simplicial set of itself, `sub_simplicial_set(X, X.simplices)`: `X.simplices(n) ⊆ X.simplices(n)`, and the two closures are the closure axioms `FaceIn` and `DegeneracyIn`, the definition passed as a premise |
| `SubSimplicialSetInter` | for any record `X`, with no simplicial structure assumed, the intersection of two sub-simplicial sets is one: a simplex of both has its faces and degeneracies in both, and the inclusion into `X` is either one's — each case one set close |
| `SimplicialMap` | `simplicial_map(X, Y, F)` ⇔ both structures, `F(n)` carries `X.simplices(n)` into `Y.simplices(n)`, and commutes with the faces and the degeneracies — a structure |
| `MapSource`, `MapTarget`, `MapIn`, `MapFace`, `MapDegeneracy` | its five axioms |
| `MapCompose` | the composite of two simplicial maps is simplicial: the source is the first map's, the target the second's, membership chains through both, and each commutation is the first map's law followed by the second's at the image simplex |
| `MapIdentity` | the identity map is simplicial: its five clauses are the two structures, both the hypothesis, a tautology `x ∈ X.simplices(n) ⇒ x ∈ X.simplices(n)` and two reflexive equations, the definition passed as a premise |
| `MapInclusion` | the inclusion of a sub-simplicial set `Y` is simplicial, from `restrict_simplicial_set(X, Y)` to `X`: the source is a simplicial set by `SubSimplicialSet`, the target is the hypothesis, a simplex of `Y` lies in `X` by the containment conjunct, and the two commutations are reflexive equations, the definition passed as a premise |
| `MapRestrict` | a simplicial map restricted to a sub-simplicial set `Z` of its source is simplicial, from `restrict_simplicial_set(X, Z)`: compose the inclusion of `Z` into `X` from `MapInclusion` with the given map by `MapCompose`; `MapSource` supplies the simplicial-set structure on `X` |
| `MapPreimage` | the preimage of a sub-simplicial set `Z` of `Y` is one of `X`: a simplex of the preimage lies in `X`; its faces and degeneracies lie in `X`, and `MapFace` / `MapDegeneracy` carry each to the same face or degeneracy of its image, which `Z`'s closure keeps in `Z` |
| `SimplicialIsomorphismDef` | `simplicial_isomorphism(X, Y, F)` ⇔ a simplicial map bijective between `X.simplices(n)` and `Y.simplices(n)` at every `n` |
| `IsomorphismInverse` | the degreewise carrier inverse `λn. inverse_on(X.simplices(n), F(n))` is simplicial and satisfies both inverse equations |

## The base simplex, the point and the constant simplicial sets

| member | statement |
|---|---|
| `BaseSimplexDef` | `base_simplex(s, x₀, 0) = x₀`, `base_simplex(s, x₀, n+1) = s(n, 0, base_simplex(s, x₀, n))` |
| `BaseSimplexIn` | `x₀ ∈ X.simplices(0) ⇒ base_simplex(x₀, n) ∈ X.simplices(n)`: by induction on `n`, the vertex at 0, and at `n + 1` the 0-th degeneracy of an n-simplex |
| `BaseSimplexSucc` | `base_simplex(s, x₀, n + 1) = s(n, 0, base_simplex(s, x₀, n))`: the definition's clause at `suc` read at `n + 1` |
| `BaseSimplexFixedPoint` | every `s(m, 0)` fixes `x₀` ⇒ `base_simplex(s, x₀, n) = x₀` in every dimension — card |
| `BaseSimplexFace` | `x₀ ∈ X.simplices(0) ∧ i ≤ n + 1 ⇒ X.d(n + 1, i, base_simplex(x₀, n + 1)) = base_simplex(x₀, n)`: write the base simplex as a degeneracy using `BaseSimplexDegeneracy`; for `i ≤ n`, cancel its i-th degeneracy by `FaceDegeneracyEqual`, and for `i = n + 1`, cancel its n-th degeneracy by `FaceDegeneracyNext` |
| `BaseSimplexDegeneracy` | `x₀ ∈ X.simplices(0) ∧ i ≤ n ⇒ X.s(n, i, base_simplex(x₀, n)) = base_simplex(x₀, n + 1)`: the 0-th degeneracy by the definition, a higher one by induction on `n`, writing `i = j + 1` and passing the degeneracy through `X.s(n, 0, ·)` (`DegeneracyDegeneracy` at `(0, j)`) to the hypothesis at `j` |
| `BaseSimplexFaceInherited` | `x₀ ∈ X.simplices(0) ∧ v ∈ X.simplices(n + 2) ∧ i < k ≤ n + 2 ∧ X.d(n + 2, i, v) = base_simplex(x₀, n + 1) ⇒ X.d(n + 1, i, X.d(n + 2, k, v)) = base_simplex(x₀, n)`: `FaceFace` at `(i, k)` makes it the face `k − 1` of the base simplex at `n + 1`, which `BaseSimplexFace` makes the base simplex at `n` |
| `MapBaseSimplex` | a simplicial map carries the base simplex at a vertex to the base simplex at its image, `F(n, base_simplex(X.s, x₀, n)) = base_simplex(Y.s, F(0, x₀), n)`: by induction on `n`, the vertex at 0, and at `n + 1` the map passes the 0-th degeneracy (`MapDegeneracy` at `i = 0`) to the hypothesis |
| `SimplicialPointSimplicesDef` | `simplicial_point_simplices(a, n) = {a}` |
| `SimplicialPointDef` | `simplicial_point(a)`: the point `a` in every dimension, its faces and degeneracies the constant maps at `a` |
| `SimplicialPoint` | the point is a simplicial set under the constant maps, `simplicial_set(simplicial_point(a))`, an instance: the unfold leaves three obligations, the two closures (`a` is a simplex in every dimension) and `d s = id`, which reads `a = x` for a simplex `x`, the only one; the four identities equating two composites read `a = a` |
| `MapToPoint` | every simplicial set maps to the point by the constant map, `simplicial_map(X, simplicial_point(a), λn x. a)`: the point is a simplicial set (`SimplicialPoint`), `a` lies in it in every dimension, and each commutation is `a = a` |
| `ConstantSimplicialSetDef` | `constant_simplicial_set(S)`: the set `S` in every dimension, every face and degeneracy the identity |
| `ConstantSimplicialSet` | the constant simplicial set is a simplicial set, `simplicial_set(constant_simplicial_set(S))`, an instance: the six identities read `x = x`, and the unfold leaves the two closures, each `x ∈ S ⇒ x ∈ S` |

## The standard simplices

| member | statement |
|---|---|
| `StandardSimplexSimplicesDef` | `standard_simplex_simplices(n, m)` = the sequences monotone on `0 .. m`, at most `n` there, zero past `m` |
| `InStandardSimplex` | `f` is an m-simplex of Δⁿ exactly when it is monotone on `0 .. m`, at most `n` there, and zero past `m`; the two closures and the non-Kan example read it in place of the definition |
| `SimplexFaceDef`, `SimplexDegeneracyDef` | `simplex_face(i, f, k) = COND(k < i, f(k), f(k+1))`; `simplex_degeneracy(i, f, k) = COND(k ≤ i, f(k), f(k−1))` |
| `SimplexFaceIn` | a face of an (m+1)-simplex is an m-simplex: the face reads `f` at `k` below `i` and at `k + 1` from `i` on, an order-preserving map keeping `0 .. m` inside `0 .. m + 1`; an index past `m` is at least `i`, so the face reads `f` past `m + 1`, where it is zero |
| `SimplexDegeneracyIn` | a degeneracy of an m-simplex is an (m+1)-simplex: it reads `f` at `k` up to `i` and at `k − 1` past `i`, an order-preserving map sending `0 .. m + 1` into `0 .. m` (at `m + 1` since `i ≤ m`); an index past `m + 1` is past `i`, so it reads `f` past `m`, where it is zero |
| `SimplexFaceDegeneracyEqual` | `simplex_face(i, simplex_degeneracy(i, f)) = f`: below `i` both read `f(k)`, from `i` on the face looks one step ahead where the degeneracy looks one step back |
| `SimplexFaceFace` | `simplex_face(i, simplex_face(j, f)) = simplex_face(j − 1, simplex_face(i, f))` for `i < j`: below `i` both sides read `f(k)`, between `i` and `j − 1` both read `f(k + 1)`, from `j − 1` on both read `f(k + 2)` |
| `SimplexDegeneracyDegeneracy` | `simplex_degeneracy(i, simplex_degeneracy(j, f)) = simplex_degeneracy(j + 1, simplex_degeneracy(i, f))` for `i ≤ j`: up to `i` both sides read `f(k)`, from `i` to `j + 1` both read `f(k − 1)`, past `j + 1` both read `f(k − 2)` |
| `SimplexFaceDegeneracyBelow` | `simplex_face(i, simplex_degeneracy(j, f)) = simplex_degeneracy(j − 1, simplex_face(i, f))` for `i < j`: below `i` both sides read `f(k)`, from `i` to `j − 1` both read `f(k + 1)`, from `j` on both read `f(k)`, the step ahead and the step behind cancelling |
| `SimplexFaceDegeneracyNext` | `simplex_face(i + 1, simplex_degeneracy(i, f)) = f`: up to `i` both read `f(k)`, past `i` the face looks one step ahead where the degeneracy looks one step back |
| `SimplexFaceDegeneracyAbove` | `simplex_face(i, simplex_degeneracy(j, f)) = simplex_degeneracy(j, simplex_face(i − 1, f))` for `j + 1 < i`: up to `j` both sides read `f(k)`, from `j + 1` to `i − 1` both read `f(k − 1)`, from `i` on both read `f(k)`, the step behind and the step ahead cancelling |
| `StandardSimplexDef` | `standard_simplex(n) = mk_simplicial(standard_simplex_simplices(n), λm. simplex_face, λm. simplex_degeneracy)`: Δⁿ, the same two operators in every dimension |
| `StandardSimplex` | `simplicial_set(standard_simplex(n))` at every `n`: the two closures are the membership laws and each identity is the identity of the two constants over every sequence, the membership the axiom carries unused |
| `SimplexHornSimplicesDef` | `simplex_horn_simplices(n, k, m)`: the m-simplices missing a vertex other than `k` |
| `SimplexHornDef` | `simplex_horn(n, k)`: those simplices with the operators of Δⁿ, `restrict_simplicial_set(standard_simplex(n), simplex_horn_simplices(n, k))` |
| `SimplexHornSub` | the horn is a sub-simplicial set of `Δⁿ` — card |

## Iterated faces

The spines below read the edges of a simplex as
iterated faces, and the cones below read their fixed prefix and tail
the same way; how a face or a degeneracy passes an iteration is stated
once, here.

| member | statement |
|---|---|
| `FaceIterateTopDef`, `FaceIterateBottomDef` | `face_iterate_top(d, n, k, x)`, `face_iterate_bottom(d, n, k, x)`: the top (bottom) `k` vertices of `x` removed, the last (0-th) face taken `k` times |
| `FaceIterateTopSucc`, `FaceIterateBottomSucc` | one more removal is one more face: `face_iterate_top(d, n, k + 1, x) = d(n − k, n − k, face_iterate_top(d, n, k, x))`, and at the bottom the face `0` |
| `FaceIterateTopIn`, `FaceIterateBottomIn` | removing `k ≤ n` top (bottom) vertices of an n-simplex leaves an (n − k)-simplex |
| `FaceIterateTopFace`, `FaceIterateBottomFace` | a face of `x` at a vertex below its top `k + 1` (not among its bottom `k`) commutes with the removal of the top (bottom) `k` vertices, its index unchanged (lowered by `k`) |
| `FaceIterateTopAbove`, `FaceIterateBottomBelow` | a face of `x` at one of its top (bottom) `k + 1` vertices is absorbed by the removal of the top (bottom) `k` |
| `FaceIterateBottomDegeneracy` | removing the bottom `k ≤ i` vertices commutes with the `i`-th degeneracy, its dimension and index lowered by `k` |
| `FaceIterateTopDegeneracyAbove` | a degeneracy at one of the top `k + 1` vertices is absorbed when they are removed: `face_iterate_top(n + 1, k + 1, X.s(n, i, x)) = face_iterate_top(n, k, x)` for `n − k ≤ i ≤ n` |

## Compatible families of faces

A family of n-simplices indexed by a set `S` of the faces of an
(n+1)-simplex is compatible when its members meet as the faces of one
(n+1)-simplex do, `d_i y(j) = d_{j−1} y(i)` for `i < j` in `S`; it is a
face family of `X` when its members are moreover n-simplices of `X` —
a map to `X` from the union of those faces — and an (n+1)-simplex fills
it when its faces at `S` are the family. A horn missing the face `k` is
the case `S = {i | i ≤ n + 1 ∧ i ≠ k}`, and the boundary of a cone below
is a face family on `0 .. r`.

| member | statement |
|---|---|
| `FacesCompatibleDef` | `faces_compatible(d, n, S, y)`: `d(n, i, y(j)) = d(n, j − 1, y(i))` for `i < j` in `S` |
| `FaceFamilyDef` | `face_family(X, n, S, y)`: `y(i) ∈ X.simplices(n)` for `i ∈ S`, and the family is compatible on `S` under `X.d` |
| `FacesFillerDef` | `faces_filler(d, n, S, y, x)`: `d(n + 1, i, x) = y(i)` for `i ∈ S` |

## Cones under a simplex and its boundary

For a fixed r-simplex `k`, the cone `simplex_cone(X, r, k)` has for
q-simplices the (r + q + 1)-simplices of `X` whose first `r + 1`
vertices form `k`, `simplex_cone_simplices(X, r, k, q)`. The face and
degeneracy indices are shifted by `r + 1`. A q-simplex of the boundary
cone `simplex_boundary_cone(X, r, k)`, a simplicial set on `num → A`,
is a family `y : num → A` of `r + 1` compatible (r + q)-simplices of
`X` restricting to the faces of `k`, padded with `junk` past `r`. Its
operators act coordinatewise, shifted by `r`, and restore that
padding. Restriction takes the prefix faces of a cone; projection
removes the prefix from the zeroth boundary face to obtain the tail.

When `r = 0`, the boundary restriction condition is empty: the sole
active coordinate `y(0)` is any simplex of `X`, so the boundary cone is
a copy of `X`, read off through the projection; the carrier remains
`num → A`. No face of a vertex is constrained.
These are fixed-prefix constructions: arbitrary joins and slices are
not defined. Their left-fibration properties are stated in
`quasi_category`, which supplies inner horn filling.

| member | statement |
|---|---|
| `SimplexConeSimplicesDef` | `simplex_cone_simplices(X, r, k, q)`: the (r + q + 1)-simplices of `X` with fixed prefix `k` |
| `SimplexConeFaceDef`, `simplexConeDegeneracyDef` | tail operators with indices shifted by `r + 1` |
| `SimplexConeDef` | `simplex_cone(X, r, k) = mk_simplicial(simplex_cone_simplices(X, r, k), simplex_cone_face(X.d, r), simplex_cone_degeneracy(X.s, r))` |
| `SimplexBoundaryConeSimplicesDef` | `simplex_boundary_cone_simplices(X, r, k, q)`: a face family on `0 .. r` of (r + q)-simplices of `X` whose tops are the faces of `k`, normalized past `r`, with no prefix restriction at `r = 0` |
| `BoundaryConeMembership` | a family normalized on `0 .. r` is in the boundary cone exactly when its values there form a face family whose tops are the faces of `k` |
| `SimplexBoundaryConeFaceDef`, `simplexBoundaryConeDegeneracyDef` | coordinatewise tail operators shifted by `r`, normalized past `r` |
| `SimplexBoundaryConeDef` | `simplex_boundary_cone(X, r, k) = mk_simplicial(simplex_boundary_cone_simplices(X, r, k), simplex_boundary_cone_face(X.d, r), simplex_boundary_cone_degeneracy(X.s, r))` |
| `SimplexConeRestrictionDef` | `simplex_cone_restriction(d, r)`: the normalized family of prefix faces |
| `SimplexBoundaryConeProjectionDef` | `simplex_boundary_cone_projection(d, r)`: the common tail, read from face 0 |
| `SimplexConeSimplicialSet` | the cone under any `k` is a simplicial set, `simplicial_set(simplex_cone(X, r, k))` |
| `BoundaryConeSimplicialSet` | the boundary cone under any `k` is a simplicial set, `simplicial_set(simplex_boundary_cone(X, r, k))` |
| `ConeRestrictionMap` | restriction from the cone to its boundary cone is simplicial |
| `ConeProjectionMap` | projection from the boundary cone to `X` is simplicial |

## Spines

The spine of an n-simplex is its chain of edges between consecutive
vertices, read by iterating the last face and then the 0-th; the spine
map is that chain padded with the degenerate edge at the last vertex.
Consecutive spine edges share a vertex, and the spine edges of a face of
`x` are spine edges of `x` away from the deleted vertex. Nothing here
reads a filler condition: the nerve, Segal's characterization and the
maps into a nerve read the spines of any simplicial set.

| member | statement |
|---|---|
| `SimplexSpineDef` | `simplex_spine(n, x, i)`, the edge of `x` between the vertices `i` and `i + 1` |
| `SpineIn`, `SpineEnds` | a spine edge is an edge; consecutive spine edges share a vertex |
| `SpineMapDef` | `spine_map(n, x)`, the chain of spine edges of `x`, padded with the degenerate edge at its last vertex |
| `FaceSpineBelow` | below the vertex a face deletes, the spine edges of the face are those of `x` |
| `FaceSpineAbove` | above it, they are those of `x` one index up |

## The opposite, and the set of simplicial maps

The opposite of a simplicial set, `opposite_simplicial_set(X)`, has
the same simplices with the order of the vertices reversed: the i-th
face of an n-simplex is its (n − i)-th face in `X`, and likewise the
degeneracies, so removing the bottom `k` vertices there removes the top
`k` in `X`. The simplicial maps from `X` to `Y`, normalized with `junk`
off each `X.simplices(n)`, form a set whose equality is extensional on
the simplices.

| member | statement |
|---|---|
| `OppositeFaceDef`, `OppositeDegeneracyDef` | `opposite_face(d)(n, i, x) = d(n, n − i, x)`; `opposite_degeneracy(s)` likewise |
| `OppositeSimplicialSetDef` | `opposite_simplicial_set(X) = mk_simplicial(X.simplices, opposite_face(X.d), opposite_degeneracy(X.s))` |
| `OppositeSimplicialSet` | a simplicial set read in the opposite order is a simplicial set, `simplicial_set(opposite_simplicial_set(X))`: each axiom of `X` at the reversed indices, `FaceDegeneracyBelow` and `FaceDegeneracyAbove` exchanged, and `FaceDegeneracyEqual` and `FaceDegeneracyNext` |
| `FaceIterateBottomOpposite`, `FaceIterateTopOpposite` | for any face map, reversal exchanges the iterated faces: `face_iterate_bottom(opposite_face(d), m, k, x) = face_iterate_top(d, m, k, x)`, and with top and bottom exchanged |
| `SimplicialMapSetDef` | `simplicial_map_set(X, Y)`: the simplicial maps from `X` to `Y`, normalized off each `X.simplices(n)` |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
