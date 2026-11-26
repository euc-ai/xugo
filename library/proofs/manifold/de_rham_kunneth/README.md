# de_rham_kunneth — the cohomology of a product through a finite homogeneous basis: the Künneth comparison over box unions, retracts and compact manifolds

The chapter computes the cohomology of a product X×M from the
cohomology of X and a finite homogeneous basis of the cohomology of M.
The comparison map is a finite sum of external products
([de_rham_product](../de_rham_product/README.md)). It is an isomorphism
over a convex open, passes to a union of two opens along the
Mayer–Vietoris ladder of [de_rham_cover](../de_rham_cover/README.md),
hence holds over finite box unions, and descends to smooth retracts
and so to compact manifolds. The first section has the squares of that
ladder which involve the connecting map.

## The connecting map and the cohomology product

The connecting formulas also hold directly on classes. If s belongs
to Hᵏ(U∩V) and t to Hᵖ(M), the U-minus-V convention gives

$$
\delta(s\wedge t\vert_{U\cap V})=\delta(s)\wedge t,
\qquad
\delta(t\vert_{U\cap V}\wedge s)=(-1)^p t\wedge\delta(s).
$$

These use the ambient manifold's restricted atlas on the intersection.
The representative formulas and the connecting map's carrier property
supply the quotient identities. Together with external-product
naturality, they give the multiplication maps needed in the
Mayer–Vietoris comparison for finite homogeneous bases. No tensor-product
module or choice of a cohomology basis is part of these operations.

| Member | Statement |
|---|---|
| `ConnectingWedgeClassRight` | Right multiplication by a global cohomology class commutes with δ — card |
| `ConnectingWedgeClassLeft` | Left multiplication by a global degree-p class commutes with δ up to (-1)^p — card |

## Finite-basis Künneth comparisons

A finite homogeneous basis E is a finite set of pairs `(degree, class)`:
each degree fibre is a basis of the corresponding cohomology module.
Finite dimensionality in every degree supplies E because cohomology
above the manifold dimension vanishes. The tags distinguish different
degrees even though all classes have the same whole-form host type.

For a first factor X and a basis of a second factor M, the coefficient
module in total degree k is the product over the fixed set E of
$H^{k-d}(X)$. A label of degree d>k instead receives the singleton zero
submodule of H^0(X). Thus negative degrees are zero, and natural-number
subtraction never turns them into an extra H^0 summand. Functions are
normalized by their factor zero outside E. This is a finite direct sum
built with [indexed module products](../../algebra/module/function_module/README.md).

The comparison sends a coefficient family a to
`Σ_(d,c)∈E, d≤k π₁*a(d,c) ∧ π₂*c`. It is linear for any finite set of
valid tagged classes and natural in the first factor. Right multiplication
by the global second-factor class commutes with the cover connecting
map without a sign. That statement uses the atlas restricted from the
ambient product on the cover intersection, so it is literally the
intersection term of the connecting map.

On a nonempty convex Euclidean open the comparison reduces to basis
expansion followed by the second projection isomorphism. Empty opens
have zero source and target. For a union of two opens, the finite product
of the shifted Mayer–Vietoris rows stays exact. Naturality and the
connecting formula give the ladder, and the
[five lemma](../../algebra/module/module_homomorphism/README.md) gives
the comparison isomorphism. At the bottom of each shift the injective
start supplies exactness after padding with zeros. Strong induction on
the number of boxes then handles every finite box union.

A smooth retraction in the first factor gives a retraction of comparison
maps. An isomorphism on the ambient manifold therefore descends to its
retract. If that retract is compact inside a Euclidean open, finitely
many boxes sandwich its image inside that open. This proves the comparison
for compact manifolds with the supplied smooth Euclidean retraction.
In particular, their self-product cohomology is spanned by external
products, equivalently by finite sums of products of closed-form classes.
Existence of an embedding and a tubular retraction is a separate input.

| Member | Statement |
|---|---|
| `HomogeneousBasisDef` | a finite degree-tagged set whose fibres are cohomology bases |
| `KunnethCoefficientModuleDef` | the fixed-index product of shifted cohomology modules, zero in negative degrees |
| `KunnethMapDef` | the finite sum of external products with the tagged classes |
| `HomogeneousBasisExists` | degreewise finite cohomology has a finite homogeneous basis — card |
| `HomogeneousBasisDegreeBound` | every basis label has degree at most the manifold dimension — card |
| `KunnethCoefficientModule` | the coefficient record is a real module — card |
| `KunnethMapHom` | comparison with finitely many valid tagged classes is linear — card |
| `KunnethNaturality` | pullback in the first factor commutes with comparison — card |
| `ExternalProductConnecting` | the first-factor connecting map commutes with external product on the right — card |
| `ConvexOpenKunneth` | comparison over a convex Euclidean open is an isomorphism — card |
| `EuclideanUnionKunneth` | comparisons for two opens and their intersection imply comparison for their union — card |
| `FiniteBoxUnionKunneth` | comparison over a finite union of Euclidean boxes is an isomorphism — card |
| `RetractKunneth` | comparison descends along a smooth retraction of the first factor — card |
| `CompactEuclideanRetractKunneth` | comparison for a compact Euclidean retract and a second factor with finite homogeneous basis is an isomorphism — card |
| `CompactEuclideanRetractSelfProductSpan` | external products span every degree of the self-product cohomology — card |

## Compact manifold conclusions

The [compact embedding and tubular retraction](../manifold_embedding/README.md)
provide the Euclidean neighbourhood data used above. Compactness alone
therefore gives finite-dimensional cohomology in each degree
([de_rham_cover](../de_rham_cover/README.md)) and a finite
homogeneous basis. No choice of embedding, retraction or orientation is
an input to these conclusions.

For a compact first factor and any second manifold with a supplied finite
homogeneous basis, the Künneth comparison is an isomorphism. In particular,
every self-product class lies in the span of external products of classes
whose nonnegative degrees sum to the total degree. Span means finite
linear combinations; choose closed representatives for the factors and
absorb coefficients into them by bilinearity to obtain the corresponding
finite sum of products of closed forms. Empty and disconnected compact
manifolds are allowed.

| Member | Statement |
|---|---|
| `CompactManifoldHomogeneousBasis` | a compact smooth manifold has a finite homogeneous cohomology basis — card |
| `CompactManifoldKunnethComparison` | comparison is an isomorphism for a compact first factor and a second factor with a finite homogeneous basis — card |
| `CompactManifoldKunneth` | external products span each degree of a compact manifold's self-product cohomology — card |
