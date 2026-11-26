# manifold_diagonal — a tangent-disk neighbourhood of the diagonal: its projection homotopy, coordinate fibers, orientation and cohomology

The chapter models a neighbourhood of the diagonal of M×M by a disk
bundle inside the tangent bundle. Its data are a smooth embedding i of
M in ℝᴺ and a smooth retraction r of an open neighbourhood of i(M) onto
M. They are hypotheses throughout; their existence for a compact
manifold is [manifold_embedding](../manifold_embedding/README.md)'s. The sections follow
the construction: the embedded tangent disks; the map Φ, a
diffeomorphism from a uniform disk onto an open neighbourhood W of the
diagonal, with the homotopy between the two projections of W; the
fibers of W in a chart; the orientation of the fiber maps and the
integrals of top forms through them
([form_integral](../form_integral/README.md)); and the equality of the
two projections on cohomology ([de_rham](../de_rham/README.md)).
Tangent vectors, the tangent bundle and the Euclidean differential
di are [tangent](../tangent/README.md)'s.

## Embedded tangent disks

The open embedded tangent disk of radius δ is
`Dδ = {(x,v)∈TM | ‖di_x(v)‖_N < δ}`. Its definition includes tangent
carrier membership. It is open even without immersion; a nonpositive
radius gives the empty set, and a positive radius contains the zero
section. For a compact base and an immersion, the closed norm sublevel
set is compact. In each compact chart patch the lower bound for an
injective matrix controls fiber coordinates by the embedded norm.
The closed unit disk outside any given open zero-section neighbourhood
is compact and contains no zero of the embedded norm. Its positive
minimum, or radius one when it is empty, puts a uniform Dδ inside the
neighbourhood.

| Member | Statement |
|---|---|
| `EmbeddedTangentDiskDef` | the strict norm sublevel set inside the tangent bundle |
| `EmbeddedTangentDiskOpen` | embedded tangent disks are open — card |
| `EmbeddedTangentDiskZeroSection` | every positive disk contains the zero section — card |
| `CompactEmbeddedTangentDisk` | a closed norm sublevel set over a compact base is compact for an immersion — card |
| `CompactZeroSectionDisk` | every open zero-section neighbourhood over a compact base contains a uniform positive disk — card |

## A neighbourhood of the diagonal

Suppose i is a smooth Euclidean embedding and r:U→M a supplied smooth
retraction on an open U containing i(M). Define

$$
\Phi(x,v)=\bigl(x,r(i(x)+di_x(v))\bigr).
$$

Its first projection is literally the tangent base point, and the
zero section maps to the diagonal. In a lifted chart and the paired
product chart, its differential at a zero tangent is the invertible
block map `(a,b) ↦ (a,a+b)`: differentiating r∘i=id supplies the second
identity block. Thus Φ is locally a diffeomorphism near every zero
tangent, without a compactness assumption.

For compact M, choose a uniform positive disk Dδ on which Φ is a
diffeomorphism onto an open neighbourhood W of the diagonal. The first
coordinate prevents collisions between different base points. Finite
base patches ensure that two small tangent vectors over the same point
lie in a common local inverse neighbourhood. This gives global
injectivity in addition to the local inverse function theorem.

The radius is also chosen so that every affine step
`i(x)+t di_x(v)` remains in U for all `(x,v)∈Dδ` and **−1<t<2**.
Transporting these steps by the inverse disk map defines
`diagonal_neighbourhood_homotopy`: at time zero it is the first
projection of W and at time one it is the second. It is smooth on W
times the normalized Euclidean time strip (−1,2), an open domain
containing [0,1]. The homotopy and its endpoint equations use only the
disk diffeomorphism and this explicit containment, so their statement
does not need compactness again.

The disk atlas is restricted from the tangent atlas; the W atlas is
restricted from the ambient product atlas. No independent atlas is
silently identified with either of these. Empty bases give empty disks
and W, and all statements include n=0. The fiber orientation section below uses positive
base charts to orient the coordinate fiber maps.

| Member | Statement |
|---|---|
| `diagonalMapDef` | Φ takes a tangent point to its base and retracted ambient tangent step |
| `diagonalHomotopyDef` | scale the inverse disk point's ambient tangent step and retract |
| `DiagonalMapZeroSection` | Φ maps the zero section to the diagonal — card |
| `DiagonalMapLocalDiffeomorphism` | Φ is a local diffeomorphism at every zero tangent — card |
| `DiagonalNeighbourhood` | over a compact base, one positive disk gives an open diagonal-neighbourhood diffeomorphism and the full strip containment — card |
| `DiagonalHomotopy` | the inverse-disk construction smoothly connects the two neighbourhood projections on the open time strip — card |

## Coordinate fibers of the diagonal neighbourhood

Fix a compatible chart c through x. Reconstructing a tangent vector
from its c component u identifies the embedded fiber disk with

$$
E(c,x,\delta)=\lbrace u\in\mathbb{R}^n:\lVert di_x(v_c(u))\rVert_N<\delta\rbrace,\qquad v_c(u)=\operatorname{tangentFromChart}(c,x,u).
$$

`embedded_tangent_fiber_disk` retains both the normalized-vector guard
and membership of the reconstructed point in the actual tangent disk.
For positive radius it is an open convex set containing zero, hence
connected. This needs only smoothness of i: without immersion the norm
can be a seminorm and the coordinate disk need not be bounded.
The map u↦(x,tangent_from_chart(c,x,u)) is smooth into the tangent bundle.

`diagonal_fiber_map` takes the second component of the diagonal map
on this fiber. Given the disk diffeomorphism Φ:Dδ→W, it restricts to
a diffeomorphism E(c,x,δ)→W_x, where W_x={y∈M | (x,y)∈W}. The inverse
on this slice reads the c component of Φ⁻¹(x,y). Preservation of the
first coordinate ensures that this inverse stays in the same fiber.
No compactness is needed once δ and W have been supplied.

The fiber map sends zero to x. In output chart c its Jacobian at zero
is the identity, with determinant one, by differentiating r∘i=id.
This calculation is local: only a neighbourhood of zero must map into
c and have its ambient steps in the retraction domain. A positive base
chart and connectedness of the full fiber disk then supply orientation
preservation in the next section. The same
statements include dimension zero and its empty identity matrix.

| Member | Statement |
|---|---|
| `embeddedTangentFiberDiskDef` | coordinate preimage of an embedded tangent-disk fiber |
| `diagonalFiberMapDef` | second diagonal-map component after chart reconstruction |
| `EmbeddedTangentFiberDiskCoordinate` | the fiber disk is the strict norm sublevel set of a fixed coordinate Jacobian — card |
| `EmbeddedTangentFiberDiskGeometry` | a positive coordinate fiber disk is open, convex, contains zero and is connected — card |
| `TangentFiberInclusionSmooth` | fixing the base and reconstructing from chart coordinates gives a smooth map into TM — card |
| `DiagonalFiberMapZero` | the fiber map sends zero to its base point — card |
| `DiagonalFiberMapZeroJacobian` | in the same base chart the fiber-map Jacobian at zero is the identity, with determinant one — card |
| `DiagonalFiberDiffeomorphism` | the supplied diagonal diffeomorphism restricts to a diffeomorphism onto the actual slice W_x — card |

## Orientation of diagonal fiber maps

On a connected oriented source, a diffeomorphism whose Jacobian has
positive determinant at one point preserves orientation
([form_integral](../form_integral/README.md)). Apply this to the
coordinate tangent disk at x.
The chosen base chart c is positive. The disk E(c,x,δ) is open and
convex, and the diagonal fiber map F has determinant one at zero in
output chart c. The given total disk diffeomorphism onto W makes F a
diffeomorphism onto W_x={y∈M | (x,y)∈W}. Thus F preserves orientation
on its entire coordinate disk. The target uses
`oriented_open_atlas⟨n⟩(T,𝒜,W_x)`, not the full compatible-chart family;
these atlases have the same smooth structure but only the first retains
the chosen orientation. No orientation of M×M is needed.

For a compactly supported top form ω on M whose entire support lies
inside W_x, the pullback F*ω has compact support in the coordinate disk
and its integral equals the integral of ω over M, with positive sign.
Compactness alone would not suffice for a map into a proper open image;
the support containment lets one first restrict the integral to W_x.
All formulas include n=0. A base point is required, so empty bases have

| Member | Statement |
|---|---|
| `DiagonalFiberOrientedDiffeomorphism` | a positive base chart makes the diagonal fiber map orientation preserving on the supplied disk — card |
| `DiagonalFiberIntegral` | a compact top form supported inside W_x pulls back with compact support and the same integral — card |

## Projections of a diagonal neighbourhood

The tangent-disk construction above provides a specific
open neighbourhood W of the diagonal and a smooth homotopy from its
first projection to its second. Its time domain is the open strip
(−1,2), and the radius condition keeps every affine tangent step in
the supplied retraction domain. Homotopy invariance
([de_rham](../de_rham/README.md)) therefore gives
equal pullbacks of every genuine cohomology class along these two
projections.

The statement retains the same disk radius, embedding, retraction and
neighbourhood W as the geometric construction. Its cohomology uses
the atlas actually restricted from the ambient product. This lets the
comparison apply to forms supported in that chosen neighbourhood.

| Member | Statement |
|---|---|
| `DiagonalNeighbourhoodCohomology` | the two projections of a tangent-disk diagonal neighbourhood induce equal pullbacks on every cohomology carrier — card |
