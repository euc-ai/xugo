# module_record — the records a ring and a module over it are held in

A module over a ring is two values: the ring's six operations and its
carrier in one value of the record `ring_ops(A)`, the module's own
addition, zero, negation, scaling and carrier in one value of the record
`module_ops(A, B)`. A statement reads a part as a field of the value
(`R.zero`, `M.carrier`) and an operation by its symbol (`c + d` at
scalars, `u + v` and `c • u` at vectors), each read at its operands'
types; the kernel term applies the record's projection
(`ring_add(R)(c, d)`). The record door mints each record's constructor
(`mk_ring`, `mk_module`) and its projections, each defined by its
equation at the constructor, and the record's extensionality,
injectivity, induction and recursion. The structure on the two values,
`module_on(R, M)`, and its laws are the module chapter's.

The product of two modules over the same scalars,
`product_module(M, N)`, is the record on the pairs
`set_cross(M.carrier, N.carrier)` with every operation taken
componentwise; that it is a module, with its two inclusions and its
first projection homomorphisms, is `ProductModuleOn`
(algebra/module/module_homomorphism).

| member | statement |
|---|---|
| `RingOpsData`, `ModuleOpsData` | the two records: constructors, the projection equations and the derived principles |
| `RestrictModuleDef` | `restrict_module(M, S)` keeps M's operations and replaces its carrier by S |
| `ScalarRestrictionDef` | `scalar_restriction(f, M)` reads M over the scalars of f's domain, each scalar r acting as f(r); a ring S read over R along f is `scalar_restriction(f, regular_module(S))`, and a submodule of the result is `restrict_module(scalar_restriction(f, M), S)` |
| `RestrictModuleCarrier` | `restrict_module(M, M.carrier) = M` |
| `RestrictModuleTwice` | `restrict_module(restrict_module(M, S), T) = restrict_module(M, T)` |
| `ProductModuleDef` | `product_module(M, N)`: the pairs of `set_cross(M.carrier, N.carrier)`, componentwise operations |
| `RestrictRingDef` | `restrict_ring(R, S)` keeps R's operations and replaces its carrier by S: a subring, or a subfield acting as scalars |
| `RestrictRingCarrier` | `restrict_ring(R, R.carrier) = R` |
| `RestrictRingTwice` | `restrict_ring(restrict_ring(R, S), T) = restrict_ring(R, T)` |
| `RegularModuleDef` | `regular_module(R)` is the ring R as a module over itself: its addition, zero and negation, scaled by its product, on its carrier |
| `RegularModuleRestrict` | `regular_module(restrict_ring(R, S)) = restrict_module(regular_module(R), S)` |
| `ScalarRestrictionIdentity` | `scalar_restriction(λa. a, M) = M` |
| `AdditiveGroupDef` | `additive_group(R)` is the additive group of the ring R: its addition, zero and negation on its carrier, a group record |
| `ModuleAdditiveGroupDef` | `module_additive_group(M)` is the additive group of the module M: its addition, zero and negation on its carrier |
| `ModuleAdditiveGroupRestrict` | `module_additive_group(restrict_module(M, N)) = restrict_group(module_additive_group(M), N)` |
