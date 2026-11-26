# de_rham_cover — two-open covers: the Mayer–Vietoris sequence, its connecting map and finite-dimensional cohomology

The chapter compares the cohomology of a manifold with that of two
open sets covering it. The cover complex of pairs of forms and its two
maps make a short exact sequence of cochain complexes once smooth
weights subordinate to the cover are supplied; its long exact sequence
is Mayer–Vietoris, with a connecting map that is natural under pullback
and commutes with multiplication by a closed form up to a degree sign.
The sequence then carries finite-dimensional cohomology from two
Euclidean opens to their union, hence to finite unions of boxes, to
compact Euclidean retracts, and to every compact manifold. The complex,
its classes and their pullback are [de_rham](../de_rham/README.md)'s.

## Two-open covers and Mayer–Vietoris

For open U and V covering the manifold, `de_rham_cover_complex` is the
componentwise product of the de Rham complexes of U and V. Its elements
are pairs of normalized form families on the same base type. The two maps
are paired restriction and the **U-minus-V** difference of restrictions
to the intersection. Local agreement glues a unique global form: a chart
crossing both opens is read through its restricted charts, since neither
local form need have an active component at the whole ambient chart.

The final surjection uses two supplied smooth scalar weights φ and ψ.
Their supports are closed in the whole manifold and contained in U and V,
respectively, and φ+ψ=1 on its carrier. For an intersection form ω, extend
ψω into U and −φω into V. Their difference is ω. Neither compact support
nor nonnegativity is needed; the support containment is what makes the
zero extensions smooth. `MayerVietoris` packages these facts as the
generic short exact sequence of cochain complexes.

`EuclideanProductMayerVietoris` supplies this sequence for
(O₁∪O₂)×W with arbitrary Euclidean open sets O₁,O₂ and any smooth W.
The Euclidean two-open partition pulls back along the first projection,
then is normalized outside the product carrier. The closed relative
Euclidean supports control its supports in the product. W need not be
compact or oriented. No general partition theorem for noncompact
manifolds is used. The open factors use the ambient product's restricted
atlases, so all maps have exactly the normalized chart families specified
by restriction.

`CoverCohomology` identifies the quotient of pairs with the pair of
quotients by the two induced projections. These are different host types;
the relationship is a module isomorphism. With this identification the
long exact sequence reads

$$
0\longrightarrow H^0(M)\longrightarrow H^0(U)\times H^0(V)\longrightarrow H^0(U\cap V)\longrightarrow H^1(M)\longrightarrow\cdots\longrightarrow H^k(M)\longrightarrow H^k(U)\times H^k(V)\longrightarrow H^k(U\cap V)\longrightarrow H^{k+1}(M)\longrightarrow\cdots.
$$

The first two arrows are the class restriction pair and its difference.
`de_rham_connecting` uses the generic lift, differentiate and glue map.
`ConnectingClass` computes it from any lift, and the three exactness
positions and the injective start use the existing cochain long exact
sequence. Exactness and linearity are asserted on cohomology carriers,
not on arbitrary sets of forms. The geometric adapter statements retain
the open-cover hypotheses beside short exactness.

## Natural maps and the connecting sign

A smooth map taking each source open into the corresponding target open
pulls back the two cover sequences. Full inverse-image equality is not
needed. The two cochain squares commute on their degree carriers, which
is precisely the hypothesis of the generic connecting naturality theorem.
Thus the square involving δ commutes as well as the restriction squares.

For a global closed p-form γ and a closed intersection k-form ω, let η
represent δ[ω]. The two wedge formulas are

$$
\delta[\omega\wedge\gamma\vert_{U\cap V}]=[\eta\wedge\gamma],
\qquad
\delta[\gamma\vert_{U\cap V}\wedge\omega]=(-1)^p[\gamma\wedge\eta].
$$

They are stated directly on closed representatives, including the equation
that η represents the connecting class. The Leibniz rule fixes the sign;
changing η by an exact form changes the displayed product by an exact form.
The first formula supplies the sign-free connecting square for the
product-basis map α ↦ π₁*α∧π₂*γ. The second records the correction required
if the fixed closed form is put on the left. These are the connecting
squares of a commuting ladder, rather than just two independently exact
rows.

## Finite box unions

Mayer–Vietoris propagates finite-dimensional cohomology from two
Euclidean opens and their intersection to their union. Degree zero uses
the injective start; in successor degree, the kernel is an image of
the intersection cohomology and the image lies in a finite product.
The restricted and canonical Euclidean atlases are identified by
smooth identity maps before this sequence uses the finiteness hypotheses.

Consequently finite unions of open boxes have finite-dimensional
cohomology in every degree. Induct on the number of boxes, simultaneously
in all degrees. Intersecting the remaining boxes with one removed box
gives another family of boxes with at most the remaining cardinality;
some intersections can coincide. The empty family is handled by the
empty-manifold calculation.

## Retractions and compact Euclidean images

Smooth maps i:M→N and r:N→M with r∘i=id on M give i*r*=id on
cohomology. Thus r* is injective, i* is surjective, and finite-dimensional
cohomology of N implies that of M, with no larger dimension. No homotopy
between i∘r and id on N is needed.

Suppose M is compact and these maps instead run between M and a
Euclidean open U. Cover the compact image i(M) by finitely many boxes
whose union V lies inside U. Corestrict i to V and restrict r to V.
Their composite remains the identity, so finiteness for V transfers to M.
This statement takes the smooth retraction as a hypothesis; constructing
an embedding and tubular retraction is separate geometry. V need not be
homotopy equivalent to M, and intersections of its boxes with M need not
form a good cover.

The [compact embedding and tubular retraction](../manifold_embedding/README.md)
provide this Euclidean neighbourhood data for every compact smooth
manifold. Compactness alone therefore gives finite-dimensional
cohomology in each degree; no choice of embedding, retraction or
orientation is an input to that conclusion.

## Definitions

| Member | Constant |
|---|---|
| `CoverComplexDef` | `de_rham_cover_complex⟨n⟩(T, 𝒜, U, V)` |
| `CoverRestrictionDef` | `de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V)` |
| `CoverDifferenceDef` | `de_rham_cover_difference⟨n⟩(T, 𝒜, U, V)` |
| `ConnectingDef` | `de_rham_connecting⟨n⟩(T, 𝒜, U, V, k, s)` |

## The cover sequence

| Member | Statement |
|---|---|
| `CoverGluing` | Agreeing forms on two covering opens glue uniquely — card |
| `CoverCochain` | The cover complex and its two maps are cochain objects — card |
| `CoverDifferenceSurjective` | Subordinate weights make the difference onto in every degree — card |
| `MayerVietoris` | A two-open cover with supplied weights gives a short exact sequence — card |
| `EuclideanProductMayerVietoris` | Euclidean two-open covers times any manifold give that sequence — card |
| `CoverCohomology` | Cohomology of the cover complex is the product of the two cohomologies — card |
| `ConnectingClass` | Differentiate any lift and glue to compute the connecting class — card |
| `MayerVietorisMaps` | The three cohomology maps are linear on their carriers — card |
| `MayerVietorisExact` | Exactness at each of the three repeating positions — card |
| `MayerVietorisStart` | The first map in degree zero is injective — card |
| `CoverPullbackSquares` | Pullback along a map carrying each designated open into its counterpart gives a cochain map and two commuting squares — card |
| `ConnectingNaturality` | Pullback commutes with the connecting maps — card |
| `ConnectingWedgeRight` | Right multiplication by a closed form commutes with δ — card |
| `ConnectingWedgeLeft` | Left multiplication by a closed p-form commutes with δ up to (-1)^p — card |

## Finite unions and retractions

| Member | Statement |
|---|---|
| `EuclideanUnionFiniteCohomology` | Finiteness for two opens and their intersection implies finiteness for their union — card |
| `FiniteBoxUnionFiniteCohomology` | Finite unions of open boxes have finite-dimensional cohomology — card |
| `RetractCohomology` | A smooth retraction splits pullback on cohomology — card |
| `RetractFiniteCohomology` | A smooth retract of a manifold with finite cohomology has finite cohomology of no larger dimension — card |
| `CompactEuclideanRetractFiniteCohomology` | A compact manifold with a supplied smooth Euclidean neighbourhood retraction has finite cohomology — card |
| `CompactManifoldFiniteCohomology` | compact smooth manifolds have finite cohomology in every degree — card |
