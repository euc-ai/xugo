# module_homomorphism — linear maps between modules on sets, kernels, images, exactness

`module_homomorphism(R, M, N, f)` includes `module_on(R, M)` and
`module_on(R, N)`, as well as preservation of the carrier, addition
and scalar multiplication. The ring and both modules are record values;
the map is the structure's subject. A raw function has no implicit
source or target module: the records remain part of its linearity claim.

The additive kernel and image are submodules, and so is the preimage of a submodule of the target. The projection onto a
quotient is linear, as are the inclusions into a product of two modules
and its first projection, and the first isomorphism theorem identifies
the quotient by the kernel with the image. Identity needs a module; a
restriction needs actual source and target submodules. These hypotheses
are part of the self-contained notion of homomorphism.

## Homomorphisms

| member | statement |
|---|---|
| `ModuleHomomorphismDef` | both endpoint modules, carrier preservation, additivity and linearity; subject `f` |
| `HomSource`, `HomTarget`, `HomIn`, `HomAdd`, `HomSmul` | the five individual laws |
| `HomGroup` | a homomorphism of the additive groups |
| `HomRestrictScalars` | a homomorphism over R is one over any subring S ⊆ R |
| `HomRestrictSubring` | a homomorphism over R restricted to K is one over R restricted to any subring S ⊆ K |
| `HomZero` | preserves zero |
| `HomNeg` | preserves negation |
| `HomSum` | preserves finite sums |
| `HomCombination` | carries a finite combination `Σ_{x∈s} c(x) • F(x)` of an indexed family of vectors to the combination of the images with the same coefficients |
| `KernelSubmodule` | the kernel is a submodule of the source |
| `ImageSubmodule` | the image is a submodule of the target |
| `HomImageSubmodule` | the image of a submodule is a submodule |
| `HomPreimageSubmodule` | the preimage `preimage_on(M.carrier, f, T)` of a submodule `T` of the target is a submodule of the source |
| `HomCompose` | the composite of two homomorphisms is linear |
| `HomIdentity` | the identity is linear |
| `ScalingLinearOverSubring` | for M a module over S, scaling by c ∈ S is linear over every subring T ⊆ S |
| `HomDiff` | the difference of two linear maps is linear |
| `HomPointwiseSum` | the pointwise sum of two linear maps is linear |
| `HomPointwiseNeg` | the pointwise negative of a linear map is linear |
| `HomScalarMultiple` | a scalar multiple of a linear map is linear |
| `HomRestrictSource` | a homomorphism restricted to a submodule `S` is a homomorphism out of `restrict_module(M, S)` |
| `HomCorestrict` | a homomorphism with values in a submodule `T` is a homomorphism into `restrict_module(N, T)` |
| `HomRestrict` | restriction is linear |
| `HomCongruence` | a map agreeing with a homomorphism on the source carrier is a homomorphism |
| `ProjectionHom` | projection onto a quotient is linear |
| `ProjectionKernel` | the projection's kernel is the submodule |
| `ProductModuleOn` | `product_module(M, N)` is a module, and `u ↦ (u, 0)`, `n ↦ (0, n)`, `z ↦ fst(z)` are homomorphisms |

## Maps out of quotients

A relation between representatives can be closed under addition and
scaling even when no choice of representatives or lifts is linear.
`QuotientRelationHom` uses this closure and totality to prove linearity
of a map whose values agree with the relation on cosets.
`QuotientRelationDescends` constructs such a map when related outputs
have equal target cosets whenever their inputs have equal source
cosets. This condition includes both independence of the output choice
and compatibility with changing the source representative. The map is
specified only on the source quotient carrier.

| member | statement |
|---|---|
| `QuotientRelationHom` | a map on quotients agreeing with a total relation closed under addition and scaling is linear |
| `QuotientInclusionHom` | for submodules K ⊆ X ⊆ Y and L ⊆ Y with K ⊆ L, the map X/K → Y/L, u + K ↦ u + L, is linear |
| `QuotientIsomorphism` | an isomorphism f : M → N gives, by X ↦ f(X), an isomorphism M/K → N/f(K) for any submodule K |
| `IsomorphismQuotientFinite` | for an isomorphism f : M → P and a submodule N, M/N is finite exactly when P/f(N) is |
| `QuotientRelationDescends` | a total relation compatible with source cosets and single-valued in target cosets, closed under addition and scaling, induces a linear quotient map |
| `InducedMapHom` | the factor theorem: a homomorphism `f` killing a submodule `K` descends to the quotient by `K` as `induced_map(f)`, taking the value `f(x)` on the coset of `x` |

## Bilinear maps

A bilinear map is linear in each argument: both families of slices are
homomorphisms, so the clauses of additivity and homogeneity in each
argument, with the modules themselves, can be read off it and it can be
recognized from them.

| member | statement |
|---|---|
| `BilinearMapDef` | `bilinear_map(R, M, N, L, phi)`: every slice `phi(u, -)` at a vector of M and every slice `phi(-, v)` at a vector of N is a homomorphism |
| `BilinearMapOfClauses` | a map into a module, additive and homogeneous in each argument, is bilinear |
| `BilinearMapClauses` | the converse: a bilinear map goes between modules, takes the pairs into the target, and is additive and homogeneous in each argument |

## Isomorphisms

| member | statement |
|---|---|
| `ModuleIsomorphismDef`, `ModuleIsomorphicDef` | a linear map injective on its source carrier and onto its target; existence of such a map |
| `IsomorphicOfIsomorphism` | modules with an isomorphism between them are isomorphic |
| `IsomorphismInverse` | the carrier inverse `inverse_on(M.carrier, f)` is a module isomorphism from `N` to `M` |
| `IsomorphismCompose` | the composite `g ∘ f` of module isomorphisms `f: M → N` and `g: N → L` is a module isomorphism from `M` to `L` |
| `IsomorphismCongruence` | a map agreeing with a module isomorphism `f` on the source carrier is a module isomorphism |
| `IsomorphismOntoImage` | a one-to-one homomorphism is an isomorphism of its source onto `restrict_module` of the target to its image |
| `KernelTrivialIffInjective` | trivial kernel iff injective on the source carrier |
| `FirstIsomorphism` | the quotient by the kernel is isomorphic to the image |

## Exactness

`exact_at(e, U, V, f, g)` states `image(f, U) = group_kernel(e, V, g)`;
`e` is the zero of the target of `g`. It needs only these five data.
`short_exact_modules(R, N', N, N'', i, p)` additionally asserts the two
strong homomorphisms, injectivity of `i`, exactness at `N`, and
surjectivity of `p`. Both homomorphisms already carry all three module
laws.

| member | statement |
|---|---|
| `ExactAtDef` | image equals kernel |
| `ShortExactModules` | a short exact sequence of three module records |
| `ExactComposeZero` | an exact composite is zero on its source |
| `FiveLemma` | two exact five-term rows with commuting vertical maps, isomorphisms at positions two and four, surjectivity at one and injectivity at five have an isomorphism at three — card |
| `ExactAtIsomorphism` | exactness is equivalent across two commuting squares of module isomorphisms |
| `IdempotentSplits` | an idempotent endomorphism `f` splits its module into image and kernel: the two meet only in zero, and every vector is a value of `f` plus a vector of `group_kernel(M.zero, M.carrier, f)` |
| `KernelRetractionFromInnerInverse` | for linear f and g with f ∘ g ∘ f = f on the source carrier, v ↦ v − g(f(v)) is a linear retraction onto ker f |
| `ModuleCokernelOfSplitting` | given linear f, q, s, h with q ∘ f = 0 on U, q ∘ s = id on N and f ∘ h + s ∘ q = id on M, N is isomorphic to `quotient_module(M, image(f, U.carrier))` |

A commuting diagram of three module isomorphisms carries exactness from
either row to the other. The carrier bijections lift preimages, and
injectivity transports the kernel condition.

Two members read a splitting: an inner inverse of f gives a linear
retraction onto its kernel, and a split sequence identifies its third
term with the cokernel of f.

The five lemma permits a different vector host type at every vertex.
Each row is exact at its three interior positions; commutation is
required on the carriers. This applies directly to long exact sequences
whose terms alternate between single modules and binary products.
