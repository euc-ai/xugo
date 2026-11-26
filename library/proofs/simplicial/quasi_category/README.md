# quasi_category — quasi-categories, their homotopy categories, and Joyal lifting through fixed-prefix cones

A quasi-category is a simplicial set in which every inner horn,
`0 < k < n + 1`, has a filler, `quasi_category(X)`; every Kan
complex is one, so is the nerve of every category, and so is every
simplicial set with unique inner fillers. Two edges are homotopic,
`edge_homotopic(X, f, g)`, when a 2-simplex has `f` as its last face, `g`
as its middle face and the degenerate edge at the target of `g` as
its 0-th; homotopic edges have the same ends, an edge is homotopic to
itself by its last degeneracy, and in a quasi-category the relation
is symmetric and transitive, each by filling one inner horn of
dimension 3.

The homotopy category of a quasi-category has the vertices for
objects and the classes of edges for morphisms,
`homotopy_category_morphisms(X)`; the source and target of a
class are those of a chosen representative, the identity at a vertex
is the class of its degenerate edge, and the composite of two classes,
`edge_class_compose(X, G, F)` for `G` after `F`, is the class of the
middle face of a chosen 2-simplex with a representative of `F` as its
last face and one of `G` as its 0-th. Two such 2-simplices of
homotopic edges have homotopic middle faces, by three 3-simplices in
turn, so the composite is well defined; the unit laws are the two
degeneracies of an edge; associativity is one 3-simplex filling the
inner horn the three composite 2-simplices form. The homotopy category
of the nerve of a category is the category itself.

## The structure and its first examples

| member | statement |
|---|---|
| `QuasiCategory` | `quasi_category(X)` ⇔ a simplicial set in which every inner horn has a filler — a structure |
| `QuasiSimplicialSet`, `InnerFill` | its two axioms |
| `KanQuasi` | a Kan complex is a quasi-category: every inner horn, `0 < k ≤ n`, is a horn of the Kan condition, which asks only `k ≤ n + 1` |
| `UniqueInnerQuasi` | a simplicial set with unique inner fillers is a quasi-category: its two axioms (`nerve.UniqueInnerSimplicialSet`, `nerve.UniqueInnerFill`) give the simplicial set and, for each inner horn, its one filler |
| `NerveQuasi` | the nerve of a category is a quasi-category, `quasi_category(nerve(C))` |

## Homotopy of edges and the homotopy category

| member | statement |
|---|---|
| `EdgeHomotopicDef` | `edge_homotopic(X, f, g)` ⇔ a 2-simplex with faces `f` at 2, `g` at 1 and the degenerate edge at the target of `g` at 0 |
| `EdgeHomotopicEnds` | homotopic edges are edges with the same ends: both are faces of the homotopy, whose faces are edges meeting at its vertices (`simplicial_set.TwoSimplexFaceEnds`), its face 0 the degenerate edge at the target of `g` (`simplicial_set.VertexDegeneracyFaces`) |
| `EdgeHomotopicRefl` | an edge is homotopic to itself, by its last degeneracy (`simplicial_set.EdgeLastDegeneracyFaces`) |
| `ThreeHornFillOne` | the inner horn Λ³₁ fills: three 2-simplices placed as the faces 3, 2, 0 of a 3-simplex and meeting as those faces do have the fourth face, the face 1 of a filler, with the faces the identity prescribes |
| `ThreeHornFillTwo` | the inner horn Λ³₂ fills: three 2-simplices placed as the faces 3, 1, 0 of a 3-simplex and meeting as those faces do have the fourth face, the face 2 of a filler, with the faces the identity prescribes |
| `EdgeHomotopicSym` | symmetric in a quasi-category: the inner horn Λ³₁ on the homotopy, the last degeneracy of the first edge and the degenerate 2-simplex at the target fills (`ThreeHornFillOne`), and its fourth face — `g`, `f` and the degenerate edge at the target of `f` as faces 2, 1, 0 — is a homotopy back |
| `EdgeHomotopicTrans` | transitive in a quasi-category: the inner horn Λ³₂ on the two homotopies and the degenerate 2-simplex at the common target fills (`ThreeHornFillTwo`), and its fourth face — `f`, `k` and the degenerate edge at the target of `k` as faces 2, 1, 0 — is a homotopy from the first edge to the third |
| `EdgeHomotopicEquivalenceOn` | in a quasi-category homotopy is an equivalence on the edges: reflexive there (`EdgeHomotopicRefl`), symmetric and transitive (`EdgeHomotopicSym`, `EdgeHomotopicTrans`) |
| `EdgeClassEqIff` | two edges have one class exactly when homotopic: homotopy is an equivalence on the edges (`EdgeHomotopicEquivalenceOn`), which are closed under it (`EdgeHomotopicEnds`), and `equivalence.ClassEqIffClosed` |
| `SegalCompositeDef` | `segal_composite(X, g, f)`, the composite of two edges: the middle face of a chosen 2-simplex with `f` and `g` as its faces 2 and 0 |
| `HomotopyCategoryMorphismsDef`, `edgeClassSourceDef`, `edgeClassTargetDef`, `edgeClassIdentityDef`, `edgeClassComposeDef` | the quotient of the edges by homotopy (`quotient_on`); the ends of a class; the identity at a vertex; the composite of classes |
| `InHomotopyCategoryMorphisms` | a morphism is the class of an edge: the edges are closed under homotopy (`EdgeHomotopicEnds`), so their quotient is their image under the class map (`equivalence.QuotientOnClosed`) |
| `ClassInHomotopyCategoryMorphisms` | the class of an edge is a morphism: the edges are closed under homotopy (`EdgeHomotopicEnds`), and `equivalence.ClassInQuotientOnClosed` |
| `EdgeRepresentative` | a class has a chosen edge whose class it is: the class of an edge `f` holds `f`, so its chosen member lies in it, `f` homotopic to it, hence an edge with `f`'s class |
| `EdgeClassMorphism` | in any simplicial set the class of an edge is a morphism (`ClassInHomotopyCategoryMorphisms`) with the edge's ends: the edge lies in its own class (`EdgeHomotopicRefl`), so the chosen member does, the edge homotopic to it and so sharing its ends (`EdgeHomotopicEnds`) |
| `CompositeExists` | composable edges have a composite 2-simplex, the filler of the inner horn Λ²₁ they form |
| `CompositeHomotopic` | composite 2-simplices of homotopic edges have homotopic middle faces: three inner horns fill in turn — Λ³₁ on the homotopy from `f` to `f'`, `w` and the first degeneracy of `g` (`ThreeHornFillOne`); Λ³₂ on that fourth face, the last degeneracy of the middle face and the homotopy from `g` to `g'` (`ThreeHornFillTwo`); Λ³₁ on that fourth face, `w'` and the last degeneracy of `g'` — and the last fourth face is the homotopy |
| `ComposeClass` | the composite of classes is the class of any composite's middle face: `f` and `g` are homotopic to the chosen members of their classes, which are composable, the chosen composite exists (`CompositeExists`), and `X.d(2, 1, w)` is homotopic to its middle face (`CompositeHomotopic`), so the classes agree (`EdgeClassEqIff`) |
| `HomotopyCategoryDef` | `homotopy_category(X)`: the category record with the vertices `X.simplices(0)` for objects, the classes of edges for morphisms, and the ends, identities and composites of classes above |
| `HomotopyCategory` | `category(homotopy_category(X))`: a morphism is the class of an edge, with the edge's ends (`EdgeClassMorphism`); the identity at a vertex is the class of its degenerate edge (`simplicial_set.VertexDegeneracyFaces`); a composite is the class of a composite 2-simplex's middle face (`ComposeClass`), whose faces give its ends (`simplicial_set.TwoSimplexFaceEnds`); the unit laws read the two degeneracies of an edge; associativity fills one inner horn Λ³₂ (`ThreeHornFillTwo`) |
| `NerveEdgeHomotopicEq` | a sequence is homotopic to an edge of a category nerve exactly when it is that edge |
| `NerveHomotopyCategory` | the homotopy category of the nerve of a category is the category, by an isomorphism of categories |

## The homotopy category and the nerve

The functors from the homotopy category of a quasi-category to a
category `C` are the simplicial maps into the nerve of `C`: a functor
gives the map sending a simplex to the images of the classes of its
spine edges, and a simplicial map into a nerve sends homotopic edges to
equal morphisms (`nerve.NerveMapCriterion`).

| member | statement |
|---|---|
| `homotopyNerveAdjunctDef` | `homotopy_nerve_adjunct(X, F)`: an n-simplex sent to the images of the classes of its spine edges |
| `HomotopyNerveAdjunction` | h ⊣ N on quasi-categories: the adjunct is a bijection from the functors `hX → C` onto the simplicial maps `X → N(C)`, `simplicial_map_set(X, nerve(C))` — card |

## Equivalences

An edge is an equivalence when its class is an isomorphism of the
homotopy category. A compositional equality of classes can be realized
by a triangle with exactly the specified edges: replace the middle
edge of a chosen composite using an inner 3-horn. Thus an equivalence
has one inverse edge and two inverse triangles with degenerate middle
edges. Reversing these triangles proves that the opposite has the same
equivalences.

| member | statement |
|---|---|
| `EdgeEquivalenceDef` | `edge_equivalence(X, f)`: an edge whose class is an isomorphism of the homotopy category |
| `CompositeTriangleExists` | for edges `f`, `g`, `h` with matching ends, the class of `g` after that of `f` is the class of `h` ⇔ one triangle has `f`, `h`, `g` as its faces 2, 1, 0: the middle edge of a composite of `f` and `g` is homotopic to `h`, and the inner horn Λ³₂ on that triangle, the homotopy and the last degeneracy of `g` replaces it by `h` (`ThreeHornFillTwo`); conversely a triangle's middle edge represents the composite (`ComposeClass`) |
| `EdgeEquivalenceIffInverseTriangles` | an edge is an equivalence iff it has one inverse edge and two triangles with degenerate middle edges |
| `OppositeQuasi` | the opposite of a quasi-category is a quasi-category, `quasi_category(opposite_simplicial_set(X))`: an inner horn of the opposite, reversed, is an inner horn of `X` (`kan_complex.HornFamilyOpposite`), whose filler fills the original (`kan_complex.HornFillerOpposite`) |
| `EdgeEquivalenceOpposite` | inverse triangles reverse, so the opposite has the same equivalences |

## Left fibrations and fixed-prefix cone lifting

The definition of a left fibration is in `kan_fibration`; the cone
carriers and their simplicial maps are in `simplicial_set`. Over a
quasi-category the total space of a left fibration is a quasi-category.
Two `Λ²₀` lifts give reflection of equivalences via the homotopy
category. An inverse triangle also permits lifting an equivalence to
a specified target: lift its inverse from that target along `Λ¹₀`,
then lift the inverse triangle along `Λ²₀`.

The combinatorial statement `PartialConeHornFill` fixes a tail
`b ∈ X.simplices(q)`, a missing tail index `i < q`, and the first `t` prefix
facets of an ambient `(p + q + 1)`-simplex. Its specified faces form a
face family on the faces made up of those `t` facets and all tail
facets except `p + 1 + i`, and agree with the tail `b`; the filler has
them as its faces there. Induction on `p` extends the prefix facets in
numeric order: on facet `j` the same problem has parameters
`(p - 1, j)`. Once they are all present, one inner horn fill completes
the simplex. At `p = 0`, the specified tail supplies face 0, even when
`t = 0`. This states the extension of
`(A_t^p ⋆ Δ^q) ∪ (Δ^p ⋆ Λ_i^q) ∪ Δ^q` directly through face equations,
without defining a general join or a subset recursion.

For every `k` (no hypothesis `k ∈ X.simplices(r)` is needed), the restriction
from its cone to its boundary cone is a left fibration by a single
inner horn. The boundary cone's projection to `X` is a left fibration:
a horn over a base simplex `b` lifts to the normalized family of
`r + 1` facets with tail `b`, the faces of `k` on top and the supplied
faces as tail faces. When the fixed prefix `k` is a vertex (`r = 0`)
the one facet is `b` itself; otherwise facet `t = 0, …, r` is a
`PartialConeHornFill` at `(p, q, t) = (r - 1, n + 1, t)` over the
facets before it.

| member | statement |
|---|---|
| `LeftFibrationTotalQuasi` | a left fibration over a quasi-category has a quasi-category as total space |
| `LeftFibrationReflectsEquivalence` | an edge above an equivalence in a quasi-category is an equivalence |
| `LeftFibrationLiftEquivalenceToTarget` | lift an equivalence to a specified target, strictly over the given edge |
| `PartialConeHornFill` | extend a tail horn over a fixed tail simplex while preserving the first `t` prefix facets |
| `ConeRestrictionLeftFibration` | restriction from a simplex cone to its boundary cone is a left fibration: one ambient inner horn fill |
| `ConeProjectionLeftFibration` | projection from a boundary cone to the quasi-category is a left fibration: a horn over a base simplex `b` lifts to `r + 1` facets with tail `b`, built one at a time by `PartialConeHornFill` (`b` itself when the fixed prefix `k` is a vertex) |

## Special horns, and Joyal's theorem

The homotopy category of a Kan complex is a groupoid: the outer horn
`Λ²₀` on an edge and the identity at its source gives a left inverse,
`Λ²₂` on the edge and the identity at its target a right inverse. The
converse needs the special outer horns. `RightSpecialHornFill` applies
the two left fibrations of the cones above to the cone under
`k = X.d(n, n, y(n))`: projection reflects the horn's last edge to an
equivalence `e` of the boundary cone, and restriction lifts `e` to the
filler, an edge of the cone ending at `y(n)`. The left special horn is
the right one read in the opposite. With both, a quasi-category is Kan
exactly when its homotopy category is a groupoid, so the nerve of a
category is Kan exactly when that category is a groupoid.

| member | statement |
|---|---|
| `KanHomotopyGroupoid` | the homotopy category of a Kan complex is a groupoid: the outer horns at an edge and the identities at its ends give a left and a right inverse (`kan_complex.CommonSourceTriangle`, `kan_complex.CommonTargetTriangle`), and `category.IsomorphismFromInverses` |
| `RightSpecialHornFill` | an outer horn `Λⁿ⁺¹ₙ₊₁` whose last edge is an equivalence fills |
| `LeftSpecialHornFill` | an outer horn `Λⁿ⁺¹₀` whose first edge is an equivalence fills: reversed (`kan_complex.HornFamilyReversed`, `HornFillerReversed`), it is a right special horn of the opposite, which `RightSpecialHornFill` fills there (`OppositeQuasi`) |
| `KanIffHomotopyGroupoid` | Joyal: a quasi-category is a Kan complex ⇔ its homotopy category is a groupoid |
| `NerveKanIffGroupoid` | the nerve of a category is a Kan complex exactly when the category is a groupoid, `kan_complex(nerve(C)) ⇔ groupoid(C)` |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
