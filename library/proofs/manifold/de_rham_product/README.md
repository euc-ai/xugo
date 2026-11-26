# de_rham_product — the wedge product of de Rham cohomology classes and their external product on a product manifold

The chapter multiplies de Rham cohomology classes. `de_rham_wedge` is
the product on one manifold, computed on closed representatives;
`de_rham_external_product` takes a class on each of two manifolds to a
class on their product. Both are stated on the cohomology modules of
[de_rham](../de_rham/README.md), and neither needs an orientation,
compactness or a tensor product of modules.

## Products on cohomology

`de_rham_wedge` multiplies a degree-p class and a degree-q class on the
same manifold to give a degree-(p+q) class. Its definition chooses closed
normalized representatives and takes the class of their wedge. The
representative formula proves that the result is independent of both
choices. All laws are guarded by cohomology carrier membership; the
definition gives no meaningful representative specification for arbitrary
sets of forms outside those carriers.

For well-definedness, change one representative at a time. An exact
change in the first factor wedges with a closed second factor to an exact
form. An exact change in the second factor uses the signed primitive
`(-1)^p α∧θ`. Degree zero uses equality of the representatives themselves,
because its coboundaries contain only the zero form. No negative-degree
primitive is introduced.

The product is bilinear, associative and graded commutative, with sign
`(-1)^(p*q)`. The class of the normalized constant-one zero-form is its
unit. Leibniz applied to `1∧1=1` gives `d1=0`. On an empty manifold this
unit equals the zero class. Smooth pullback preserves both multiplication
and the unit, with source and target dimensions allowed to differ.

For classes a and b on two manifolds, their external product is

$$
a\times b=\pi_1^\ast a\wedge\pi_2^\ast b.
$$

It is a class on the product point type and is bilinear in its two
arguments. Pullback by f×g applies f* and g* to the two factors. Swapping
the factors contributes `(-1)^(p*q)` for degrees p and q, independent of
the manifold dimensions and without any orientation assumptions. For
a,b,c,d of respective degrees p,q,r,h, multiplication satisfies

$$
(a\times b)\wedge(c\times d)=(-1)^{qr}(a\wedge c)\times(b\wedge d).
$$

The sign comes from moving the middle two factors past each other.
Taking a unit in either factor recovers the other projection pullback;
pulling the external product back by the diagonal recovers the internal
wedge. Empty factors and degrees above dimension are included.

## Definitions

| Member | Constant |
|---|---|
| `WedgeDef` | `de_rham_wedge⟨n⟩(T, 𝒜, p, q, s, t)` |
| `ExternalProductDef` | `de_rham_external_product⟨n, m⟩(T, 𝒜, S, ℬ, p, q, s, t)` |

## The cohomology product

| Member | Statement |
|---|---|
| `WedgeClassCongruence` | Replacing either closed representative by a cohomologous one preserves the wedge class — card |
| `WedgeClass` | Multiplication of closed-form classes is the class of their wedge — card |
| `WedgeBilinear` | The quotient product is bilinear between its degree modules — card |
| `WedgeAssociative` | Cohomology multiplication is associative — card |
| `WedgeGradedCommutative` | Interchanging degrees p and q contributes $(-1)^{pq}$ — card |
| `WedgeUnit` | The normalized form unit gives a two-sided cohomology unit — card |
| `PullbackWedge` | Smooth pullback preserves the cohomology product — card |
| `PullbackUnit` | Smooth pullback preserves the cohomology unit — card |

## External products

| Member | Statement |
|---|---|
| `ExternalProductClass` | The external product is represented by the wedge of the two projection pullbacks — card |
| `ExternalProductBilinear` | External product is bilinear on the factor cohomology modules — card |
| `ExternalProductNaturality` | Pullback by a product map acts on each external-product factor — card |
| `ExternalProductSwap` | Swapping factors contributes the cohomological sign $(-1)^{pq}$ — card |
| `ExternalProductMultiplicative` | Multiplication of external products has the middle-factor sign $(-1)^{qr}$ — card |
| `ExternalProductUnit` | External product with a unit is projection pullback — card |
| `ExternalProductDiagonal` | Diagonal pullback of an external product is the internal wedge — card |
