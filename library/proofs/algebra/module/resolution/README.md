# resolution — free resolutions, canonical construction and comparison

A free resolution `free_resolution(R, M, S, d, eps)` is a chain complex
of free modules on the sets `S(n)`, exact above zero, augmented onto
`M`, with image of `d(1)` equal to the kernel of `eps`. The ring and
module are records. Its subject is `S`; `free_complex(R, S, d)` packages
the shared pointwise operations, carriers and boundary in a
`complex_ops` record. The comparison theorem applies to any two free
resolutions, on any index types.

## Existence and comparison

| member | statement |
|---|---|
| `FreeComplexOf` | the record of a sequence of free modules with boundary `d` |
| `FreeResolution` | the augmented exact complex; subject `S` |
| `ResolutionModule`, `ResolutionComplex`, `ResolutionExact`, `ResolutionAugmentationHom`, `ResolutionAugmentationOnto`, `ResolutionAugmentationKernel` | the six laws |
| `FreeLiftThrough` | a map out of a free module lifts through a surjection |
| `FreeComplexModule`, `FreeComplexFields` | the module at each degree of a free complex is the free module on `S(n)`, with its terms, differential and zero read off |
| `FreeComplexDifferentialHom` | each differential of a free chain complex is linear between consecutive free modules |
| `LiftThroughBoundaries` | a linear map from a free module into degree `m` of a free chain complex with values in the boundaries lifts through the differential out of degree `m + 1` |
| `FreeResolutionExists` | existence on any index type containing injections of the module and its free coefficient space — card |
| `ResolutionComparison` | a module map lifts to an augmentation-compatible chain map between free resolutions |
| `ResolutionComparisonHomotopy` | two chain maps from a free chain complex into a free resolution that agree after its augmentation are chain homotopic |
| `ResolutionComparisonEquivalence` | lifts of the identity between two free resolutions of one module are inverse chain homotopy equivalences |

## One index type for the canonical resolution

For scalar type `A` and module carrier type `B`, fix
`I(A,B) = set(prod(num, prod(A,B)))`. Every free term lives at
`I(A,B) → A`. The explicit `carrier_embedding` sends `b` to all
`(0,(a,b))`. The cardinal chapter supplies an injection from functions
on `I(A,B)` that are constant outside a finite set back into `I(A,B)`.
`index_embedding` chooses one such injection per pair of types. It has
no ring, module or zero argument; it is reused in every degree and in
every map. Finite support relative to any ring zero lies in its domain
(`function_module.FiniteSupportEventuallyConstant`).

The decoders are the inverses of the two encodings on their domains:
`carrier_preimage(M, j) = inverse_on(M.carrier, carrier_embedding, j)`
and `index_preimage(j) = inverse_on({v | eventually_constant(v)},
index_embedding, j)`. The construction reads them only on the
respective images, where `CarrierPreimageEmbedding` and
`IndexPreimageEmbedding` say they invert the encodings: each is
`functions.InverseOnLeft` at that decoder, the encoding being one-to-one
on its domain. No resolution is selected by a separate choice operator.

`canonical_syzygy(R, M, n)` is a natural-number recursion holding the
basis set and boundary. In degree zero the basis is the image of
`M.carrier`; the augmentation is the free extension of its decoder.
The next basis is the image under `index_embedding` of the current
kernel, and its boundary freely extends `index_preimage`. The kernel
at zero is the augmentation kernel; at positive degree it is the
boundary kernel. The degree-zero boundary is a dummy zero map and is
never used as the augmentation. Each kernel lies inside its free term
by definition (`CanonicalKernelInFree`). On a basis index of the next
degree the decoder returns the kernel vector the index encodes
(`IndexPreimageInKernel`), the boundary is the linear extension of a
map into the free term (`CanonicalBoundaryHom`), and each kernel is the
kernel of a homomorphism (`CanonicalKernelSubmodule`).

| member | statement |
|---|---|
| `carrierEmbeddingDef`, `IndexEmbeddingDef`, `carrierPreimageDef`, `IndexPreimageDef` | explicit carrier encoding, fixed function encoding and their decoders |
| `CanonicalEpsDef`, `CanonicalKernelAtDef`, `CanonicalSyzygyDef` | augmentation, the degree-sensitive kernel, and recursion |
| `CanonicalResolutionTermsDef`, `CanonicalBoundaryDef`, `CanonicalKernelDef` | the sequence's named projections |
| `CarrierEmbeddingInjective` | the carrier encoding is one-to-one on all of B |
| `IndexEmbeddingInjective` | the fixed encoding is one-to-one on the eventually constant functions |
| `CarrierPreimageEmbedding`, `IndexPreimageEmbedding` | each decoder returns the carrier element, or the eventually constant function, whose code it is given |
| `CanonicalTermsEncodeKernel`, `CanonicalBoundaryFreeLift` | in degree n + 1 the basis is the image of the degree-n kernel under `index_embedding`, and the boundary is the free lift of `index_preimage` |
| `CanonicalKernelInFree` | each kernel lies in its free term |
| `IndexPreimageInKernel` | the decoder carries each basis index of degree n + 1 to a vector of the degree-n kernel |
| `CanonicalEpsHom` | the augmentation is linear |
| `CanonicalEpsOnto` | the augmentation is onto — card |
| `CanonicalBoundaryHom` | each boundary of positive degree is linear |
| `CanonicalKernelSubmodule` | each kernel is a submodule of its free term: the kernel of the augmentation in degree 0, of the boundary in each positive degree |
| `CanonicalImageIsKernel`, `CanonicalBoundaryTwice` | each next image is the kernel and consecutive boundaries compose to zero — card |
| `CanonicalResolution` | these data form a free resolution, without a size hypothesis — card |

## Strict maps on the canonical resolution

`canonical_map(R, M, L, f, n)` freely pushes generators along
`carrier_embedding ∘ f ∘ carrier_preimage` in degree zero, and along
`index_embedding ∘ canonical_map(n) ∘ index_preimage` in the next
degree. The chain and augmentation squares carry each kernel into the
next module's kernel. The same fixed encodings therefore cancel in
identity and composition. These equalities are asserted only on the
source free carrier: arbitrary values of the total decoders outside
their images play no role.

| member | statement |
|---|---|
| `CanonicalMapDef` | the recursive lift of a module map |
| `CanonicalMapAugmentation`, `CanonicalMapKernel`, `CanonicalMapChain` | augmentation square, kernel preservation and chain map — card |
| `CanonicalMapIdentity`, `CanonicalMapCompose` | identity and composition hold pointwise on each free carrier — card |
