# tensor_product — the tensor product of two modules on sets

The tensor product of modules `M` and `N` on sets over one ring `R`,
each one value of its record (module_record), is the free module on the
pairs `M.carrier × N.carrier` modulo the submodule the bilinearity
relations span: `tensor_relations(R, M, N)` is that submodule,
`tensor_product(R, M, N)` the cosets, and `tensor(R, M, N, u, v)` the
pure tensor `u ⊗ v`, the coset of the generator at `(u, v)`. The members
are cosets, at the type `set(prod(B, C) → A)`, of functions on the pairs,
finite support being the free module's carrier, and
`tensor_module(R, M, N)` is the quotient of the free module record by
the relations, `quotient_module`: the coset sum, the relations as zero,
the coset inverse and the quotient scaling. A bilinear map `M × N → L`
induces one homomorphism out of the tensor product, the pure tensors
span, and tensoring with `M` is right exact. The derived functors Tor
are the homology of the tensor product of a free resolution with a
module; for a free module the tensor product is read as finitely
supported functions into the module (tor_ext, `FiniteSuppTensorIso`), and
`TorZero` returns to the tensor product stated here.

## The construction

| member | statement |
|---|---|
| `tensorRelationsDef` | `tensor_relations(R, M, N) = module_span(R, free_module_record(R, M.carrier × N.carrier), …)` over the four kinds of relation element |
| `TensorProductDef` | `tensor_product(R, M, N) = left_cosets(+, finite_supp(R.zero, R.carrier, M.carrier × N.carrier), tensor_relations(R, M, N))` |
| `TensorDef` | `tensor(R, M, N, u, v) = left_coset(+, delta_at((u, v)), tensor_relations(R, M, N))` |
| `TensorModuleDef` | `tensor_module(R, M, N) = quotient_module(free_module_record(R, M.carrier × N.carrier), tensor_relations(R, M, N))` |
| `TensorModuleCarrier` | `tensor_module(R, M, N).carrier = tensor_product(R, M, N)` |
| `TensorModuleAdd` | `tensor_module(R, M, N).add = set_mul(fun_add(R.add))` |
| `TensorModuleZero` | `tensor_module(R, M, N).zero = tensor_relations(R, M, N)` |
| `TensorModuleSmul` | `tensor_module(R, M, N).smul = quotient_smul(fun_add(R.add), fun_smul(R.mul), tensor_relations(R, M, N))` |
| `PairGeneratorIn` | the generator at a pair of `M × N` lies in the free module |
| `TensorRelationKinds` | a set holding the four kinds of relation element holds them all |
| `TensorRelationsSubmodule` | the relations are a submodule of the free module record |
| `TensorRelationIn` | a relation element lies in `tensor_relations(R, M, N)` |
| `TensorModuleOn` | `module_on(R, tensor_module(R, M, N))` |
| `TensorProjectionHom` | `coset_map(+, tensor_relations(R, M, N))` is a homomorphism of the free module on the pairs into `tensor_module(R, M, N)` |
| `TensorIsProjection` | `tensor(R, M, N, u, v)` is the projection `coset_map(+, tensor_relations(R, M, N))` of the generator at `(u, v)` |
| `TensorRelatedCoset` | two functions of the free module whose difference is a relation element have one coset |
| `TensorRelatedSum` | a function of the free module differing from `x + y` by a relation element projects to the sum of the projections of `x` and `y` |
| `TensorRelatedScaled` | a function of the free module differing from `s • x` by a relation element projects to `s` times the projection of `x` |
| `TensorIn` | `u ∈ M.carrier ∧ v ∈ N.carrier ⇒ tensor(R, M, N, u, v) ∈ tensor_product(R, M, N)` |
| `TensorAddLeft` | the tensor is additive in the first argument |
| `TensorAddRight` | the tensor is additive in the second argument |
| `TensorSmulLeft` | `tensor(c • u, v) = c • tensor(u, v)` in the tensor module |
| `TensorSmulRightFactor` | `tensor(u, c • v) = c • tensor(u, v)` in the tensor module |
| `TensorBalance` | `tensor(u, c • v) = tensor(c • u, v)`: a scalar passes between the two arguments of a pure tensor |
| `TensorZeroRight` | `u ⊗ N.zero` is the relations, the tensor product's zero |
| `TensorSpan` | every member is a finite sum of scaled pure tensors, in the tensor module's own operations |
| `PureTensorsSpan` | `module_span(R, tensor_module(R, M, N), pure tensors) = tensor_module(R, M, N).carrier` |
| `TensorInduction` | a submodule of `tensor_module(R, M, N)` holding every pure tensor `u ⊗ v` holds all of it |
| `TensorPureSum` | every tensor is a finite sum of pure tensors |

## The universal property and right exactness

| member | statement |
|---|---|
| `BilinearLift` | a bilinear map read on the pairs extends to a homomorphism out of the free module, sending the generator at `(u, v)` to `phi(u, v)` |
| `BilinearLiftKillsRelations` | that lift's kernel holds `tensor_relations(R, M, N)` |
| `TensorUniversal` | a map with `bilinear_map(R, M, N, L, phi)` induces a homomorphism with `h(u ⊗ v) = phi(u, v)` |
| `TensorLinearBilinear` | a homomorphism `h` out of `tensor_module(R, M, N)` gives `bilinear_map(R, M, N, L, λu v. h(u ⊗ v))`: the converse of `TensorUniversal` |
| `TensorUniversalUnique` | homomorphisms agreeing on pure tensors agree throughout the tensor product |
| `TensorFunctional` | a linear form on `V` contracts `V ⊗ W` onto `W` |
| `TensorBasisSeparates` | a basis of `V` separates the terms of a tensor |
| `TensorRightExact` | `N → L → N'' → 0` exact ⇒ `M ⊗ N → M ⊗ L → M ⊗ N'' → 0` exact, `N → L` linear or not |
| `TensorRegular` | `u ⊗ r ↦ r • u` is an isomorphism `M ⊗ R → M` — card |

The universal property and right exactness read homomorphisms
`module_homomorphism(R, M, N, f)` between module records over the one
ring record; the third module `L`, and `N''`, any module that `p` maps
onto, are each one more record. `TensorRightExact` has a file of its own,
`right_exact.go`: it is a self-contained centerpiece, with its own
vocabulary of quotient, descent and lifts.
