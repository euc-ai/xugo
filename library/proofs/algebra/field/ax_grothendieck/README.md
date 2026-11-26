# ax_grothendieck — injective polynomial self-maps of affine space are surjective

Finite subfields give the source argument: restrict an injective polynomial map to a finite field containing its coefficients and a desired image point. The property at a fixed dimension and degree quantifies every coefficient of the map, so it is a closed sentence, which elementarity (`ByElementarity`) carries over. Zero-dimensional tuples form one point.

The models it starts from, a locally finite algebraically closed field of each prime characteristic, are lefschetz.PrimeClosureLocallyFinite; lefschetz.PrimeFamilyTransfer carries the sentence from them to every algebraically closed field, by same-characteristic transfer in positive characteristic and Lefschetz stability in characteristic zero.

| Member | Statement |
|---|---|
| `AxPropertyDef` | The degree-bounded polynomial injective-implies-surjective statement. |
| `LocallyFiniteSource` | Over a locally finite field an injective polynomial self-map is surjective. |
| `AlgebraicallyClosedAxProperty` | Over an algebraically closed field, an injective polynomial self-map of n-space of degree at most d is surjective. |
| `AxGrothendieck` | Every injective polynomial self-map of finite-dimensional affine space over an algebraically closed field is surjective. |
