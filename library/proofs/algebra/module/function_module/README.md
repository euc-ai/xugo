# function_module — function modules and indexed products of modules

For a module N and a set S of generators, two modules of N-valued
functions on S stand for the two functors of a free module:
`finite_supp(N.zero, N.carrier, S)`, the finitely supported functions, is the
free module on S tensored with N, and `fun_module(N.zero, N.carrier, S)`,
all functions zero off S, is the homomorphisms out of the free module on
S into N, each read at the generators. With N's operations read
pointwise (`fun_add`, `fun_zero`, `fun_neg`, `fun_smul`) the second is a
module, `function_module(N, S)`, and the first a submodule of it, the
module `finite_supp_module(N, S)`. With N the ring itself, the finitely
supported functions are the free module
([`free_module`](../free_module/README.md)), which is
`finite_supp_module` at the ring as a module over itself. The two are
the terms of the tensor and Hom complexes of a free resolution
([`tor_ext`](../tor_ext/README.md)).

## Function modules

| member | statement |
|---|---|
| `FiniteSupportDef` | `finite_support(zero, f)` ⇔ `finite({x \| f(x) ≠ zero})` |
| `FiniteSupportEventuallyConstant` | `finite_support(zero, f) ⇒ eventually_constant(f)` |
| `FunAddDef`, `FunZeroDef`, `FunNegDef`, `FunSmulDef` | the pointwise operations (`fun_smul` scales functions into any module) |
| `FiniteSuppDef` | `finite_supp(zero, c, S)` = finite support, valued in `c`, zero off `S` |
| `FiniteSuppMember` | `f ∈ finite_supp(zero, c, S)` ⇔ the support of `f` is finite and lies in `S`, and `f` is valued in `c` |
| `FiniteSuppCountable` | `countable(c) ∧ countable(S) ⇒ countable(finite_supp(zero, c, S))` |
| `FunModuleDef` | `fun_module(zero, c, S)` = valued in `c`, zero off `S` |
| `FiniteSuppModuleDef`, `FunctionModuleDef` | `finite_supp_module(N, S)` and `function_module(N, S)`: the two at `N`'s zero and carrier, with `N`'s operations read pointwise |
| `FunModuleOn` | `module_on(R, M) ⇒ module_on(R, function_module(M, S))` |
| `ModuleSumApply` | a sum of functions into a module evaluates pointwise |
| `FiniteSuppSubmodule` | `module_on(R, M) ⇒ submodule(R, function_module(M, S), finite_supp(M.zero, M.carrier, S))` |
| `FiniteSuppModuleOn` | `module_on(R, M) ⇒ module_on(R, finite_supp_module(M, S))` |

## Sums over the support

Homomorphisms `T(x)` of `N` into `P`, one at each point of `S`, sum to a
homomorphism out of the finitely supported functions: `g ↦ Σ T(x, g(x))`
over the support of `g`.

| member | statement |
|---|---|
| `FiniteSuppSumHom` | `module_on(R, N) ∧ module_on(R, P) ∧ (∀x. x ∈ S ⇒ module_homomorphism(R, N, P, T(x))) ⇒ module_homomorphism(R, finite_supp_module(N, S), P, λg. Σ_{supp g} T(x, g(x)))` |

## Indexed products

`indexed_product_module(J, M)` permits the module record M(i) to vary
with i. Its carrier is `indexed_functions(J, λi. M(i).zero,
λi. M(i).carrier)`. Addition, negation and scaling use the factor
operations on J and return the prescribed factor zero everywhere else.
The factors share a vector host type, but need not have equal carriers.
Inactive factor records need satisfy no module laws. For finite J this
product is also the finite direct sum.

`indexed_module_map(J, N, f)` applies f(i) at each active coordinate
and returns the target zero off J. The scalar ring hypothesis in the
product and map laws matters only for J empty, where no factor supplies
the ring. Exactness of a product reads only exactness of its components,
with no linearity. It and surjectivity of arbitrary products use choice
to select component preimages.

| member | statement |
|---|---|
| `IndexedProductModuleDef` | the module record of normalized functions in the varying factors |
| `indexedModuleMapDef` | the coordinate map normalized by target zeros |
| `IndexedProductModule` | a commutative scalar ring and modules at active indices give a product module — card |
| `IndexedMapHom` | component homomorphisms give a product homomorphism — card |
| `IndexedMapIsomorphism` | component isomorphisms give a product isomorphism — card |
| `IndexedProductExact` | component exact sequences give an exact product sequence |
| `IndexedProductSumHom` | a finite sum of component maps to one target module is linear — card |
