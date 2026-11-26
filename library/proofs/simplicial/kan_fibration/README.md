# kan_fibration — Kan and left fibrations, fibres, and the long exact sequence of homotopy groups

A Kan fibration is a simplicial map `p : X → Y` along which every horn
of `X` whose image is the horn of a simplex `z` of `Y` has a filler
over `z`, `kan_fibration(X, Y, p)`. Over a Kan complex
the source of a fibration is a Kan complex. The fibre over a vertex
`y₀`, the simplices over the base simplex at `y₀` with the faces and
degeneracies of `X`, `simplicial_fiber(X, Y, p, y₀)`, is a
sub-simplicial set and, over any base, a Kan complex;
a simplicial set is a Kan complex exactly when its map to the point is
a fibration; and fibrations compose.

With `x₀` a vertex of `X` and `p(0, x₀)` the base point of `Y`, the
connecting map `simplicial_connecting_map(X, Y, p, x₀, n)` sends the class
of an (n+1)-sphere `z` of `Y` to the class, in the fibre, of the n-th
face of a lift of `z` whose other faces are the base simplex. The lift
exists by the lifting condition at the constant horn, its n-th face is
a sphere of the fibre, the lifts of homotopic spheres have homotopic
n-th faces through one lift over the homotopy, and for `0 < n` the map is a homomorphism:
the lift of a product filler of `Y`, read along two more horns, is a
product filler of the fibre. The sequence of the fibre, the total
space and the base is exact at each of the three groups, each
exactness two implications about classes; the proofs lift one new
horn at the total space, one at the base and none at the fibre, whose lifts
are the connecting map's own; at `n = 0` the same statements read on
the sets of components.

## Left fibrations

A left fibration `left_fibration(X, Y, p)` lifts the
horns `Λ^q_i` for `0 ≤ i < q`. In the face-family indexing this is
`k ≤ n` in dimension `n + 1`, including the one-dimensional horn
`Λ¹₀`, which lifts an edge from its source. Both source and target are
simplicial sets; neither is required to be a quasi-category by the
definition. The quasi-category consequences, including reflection of
equivalences and lifting to a prescribed target, live in
`quasi_category`.

| member | statement |
|---|---|
| `LeftFibration` | `left_fibration(X, Y, p)` ⇔ a simplicial map lifting every non-last horn over a base simplex — a structure |
| `LeftFibrationMap`, `LeftFibrationLift` | its simplicial map and lifting axioms |
| `LeftFibrationTriangleLift` | the horn `Λ²₀` lifts: two edges `g`, `h` out of one vertex, over a triangle `t` of `Y` whose faces 1 and 2 are their images, are the faces 1 and 2 of a triangle of `X` over `t` — the lifting axiom at `n = 1`, `k = 0` |

## The structure, the fibre, and the Kan complexes it gives

| member | statement |
|---|---|
| `KanFibration` | `kan_fibration(X, Y, p)` ⇔ a simplicial map along which every horn with a filled image lifts — a structure |
| `FibrationMap`, `FibrationLift` | its two axioms |
| `simplicialFiberSimplicesDef` | `simplicial_fiber_simplices(X, Y, p, y₀, n)` = the n-simplices of `X` over `base_simplex(Y.s, y₀, n)` |
| `SimplicialFiberDef` | `simplicial_fiber(X, Y, p, y₀) = restrict_simplicial_set(X, simplicial_fiber_simplices(X, Y, p, y₀))`: those simplices with the faces and degeneracies of `X` |
| `FiberSub` | the fibre over a vertex is a sub-simplicial set of `X`: a face or a degeneracy of a simplex over the base simplex maps to a face or a degeneracy of the base simplex, which is the base simplex one dimension down or up |
| `FiberSimplicialSet` | the fibre over a vertex is a simplicial set, `simplicial_set(simplicial_fiber(X, Y, F, y₀))`: a sub-simplicial set of the simplicial set `X` |
| `FiberSphere` | the fibre's spheres are the spheres of `X` over the base simplex: with the spheres and the fibre unfolded, the two memberships are the same three conditions regrouped |
| `FiberBasePoint` | a vertex `x₀` of `X` lies in the fibre over its image `p(0, x₀)`: the base simplex at 0 is the vertex itself |
| `TotalKan` | over a Kan complex the source of a fibration is Kan: a horn of `X` maps to a horn of `Y`, which fills there, and the filling lifts |
| `FiberKan` | the fibre over a vertex is a Kan complex: a horn of the fibre is a horn of `X` over the base simplex, whose images are the faces of the base simplex one dimension up; it lifts over that simplex, and the lift lies in the fibre |
| `FibrationCompose` | fibrations compose: a horn of `X` filled under `q ∘ p` maps to a horn of `Y` filled by the same simplex, which lifts along `q`, and the horn then lifts along `p` over that lift |
| `KanIffFibrationToPoint` | a simplicial set is Kan exactly when its map to the point is a fibration: forward, a horn's filler lies over the point's one simplex; backward, a horn lifts over `a` |

## The connecting map

| member | statement |
|---|---|
| `SimplicialConnectingMapDef` | `simplicial_connecting_map(X, Y, p, x₀, n, L)` = the class in the fibre of the n-th face of a lift of a representative of `L` |
| `ConnectingLiftExists` | an (n+1)-sphere of `Y` lifts with the base simplex for its faces other than the n-th: the base simplex of `X` is a sphere, so the constant family at it, a family of spheres missing the face n, is a horn (`SphereHornCompatible`), whose member maps to the base simplex of `Y`, every face of the sphere; it lifts over the sphere |
| `ConnectingLiftFace` | the n-th face of such a lift is a sphere of the fibre |
| `ConnectingHomotopic` | lifts of homotopic simplices of `Y`, the lifts having the base simplex for their faces other than the n-th, have homotopic n-th faces in the fibre: one horn, the base simplex below n with the two lifts at n + 1 and n + 2, lifts over the homotopy, and the n-th face of that lift is the homotopy in the fibre |
| `ConnectingMapClass` | well defined on classes |
| `ConnectingMapIn` | `πₙ₊₁(Y)` into `πₙ(F)` |
| `ConnectingProductLift` | lifts of the last two faces of a product filler determine a lift of its n-th face with prescribed last faces |
| `ConnectingProductClass` | the boundary class of a lifted product is the product of the two boundary classes |
| `ConnectingMapHom` | a homomorphism for `0 < n` |

## Exactness

Classes are written `C` in `X`, `K` in the fibre and `L` in `Y`.

| member | statement |
|---|---|
| `FiberInclusionClass` | the inclusion of the fibre carries the class of a sphere of the fibre to its class in `X`, with only `X` Kan: the fibre is a sub-simplicial set containing `x₀` (`FiberBasePoint`), so the inclusion is a simplicial map into the Kan complex `X`, which `HomotopyMapClass` reads on classes |
| `ExactAtTotal` | at `πₙ(X)`: `p_*(C)` is the unit ⇔ `C` comes from `πₙ(F)`: the horn of `x` and the base simplex lifts over a homotopy in `Y` to the base simplex, and its last face is a sphere of the fibre homotopic to `x` |
| `ExactAtBase` | at `πₙ₊₁(Y)`: `∂L` is the unit ⇔ `L` comes from `πₙ₊₁(X)`: one horn, a homotopy in the fibre beside a lift, lifts over the last degeneracy of `z`, and the last face of the lift is a sphere of `X` over `z` |
| `ExactAtFiber` | at `πₙ(F)`: `i_*(K)` is the unit ⇔ `K` is a connecting image: a lift of a sphere of `Y` is a homotopy in `X` from its n-th face to the base simplex, and such a homotopy from a sphere of the fibre is a lift |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
