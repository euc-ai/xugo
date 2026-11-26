# square_zero_classification — the square-zero extensions of an algebra by a module classified by the first André–Quillen cohomology, with both directions explicit

For an algebra `S` over `R`, through `f`, and a module `N` over `S`, the
isomorphism classes of square-zero extensions of `S` by `N` over `R`
(algebra/ring/square_zero_extension) are the members of
`D^1(S/R, N)`, the first cohomology of the cotangent cochain complex
(algebra/cotangent/cotangent_complex). This chapter does not reopen the
cochain differential. It joins two chapters through two statements of
each: `ConormalClassSurjective` and `ConormalClassEqIffDerivation` of
algebra/cotangent/cohomology_one, which read `D^1` as the conormal maps
of the standard presentation `P = R[S] → S` modulo the restrictions of
derivations; and the graph, shear and lift constructions of the
square-zero chapter, at that presentation.

From an extension to a class. `P` is free on the tags of `S`'s
elements, so the augmentation lifts to every extension `E`, a preimage
chosen under the projection for each element. A lift `s` reads a
conormal map `γ_s`, and `square_zero_class(R, S, f, N, E)` is its class.
Two lifts differ by a derivation whose restriction to the kernel is the
difference of their conormal maps, so every lift gives the one class,
and an isomorphism of extensions carries a lift to a lift with the same
conormal map. The class lies in the one `D^1` on the host `U` whatever
type the extension sits on.

From a class to an extension. `square_zero_realization(R, S, f, N, ξ)`
is the graph extension `(P ⋉_ε N)/J_γ` of `γ = G(c)`, `c` a cocycle
chosen in `ξ`. Its class is computed through the canonical lift
`u ↦ [(u, 0)]`, which reads `γ` back since `[(x, 0)] = [(0, γ(x))]` on
the kernel, and it is `[C(G(c))] = ξ`.

Back again. The realization of the class of `E` is isomorphic to `E`:
the lift's sum map `(u, n) ↦ s(u) + i(n)` gives $E_{\gamma_s} \cong E$, and the
shear by the derivation joining `γ_s` to the realization's conormal map
gives the rest. So two extensions, on any two types, are isomorphic
exactly when their classes are equal. No card composes or inverts
square-zero isomorphisms; the two round-trip statements do it in their
proofs.

The statements carry `cotangent_universe(R, 𝕌⟨A:U⟩) ∧
cotangent_universe(S, 𝕌⟨A:U⟩)`; the letter `U` of `square_zero_class`
is fixed by them, written `square_zero_class⟨U:U⟩` where nothing else
fixes it.

## The class and the realization

| member | statement |
|---|---|
| `SquareZeroClassDef` | `square_zero_class(R, S, f, N, E)` = `conormal_class` of `extract_conormal` at a lift chosen among the lifts of `P`'s augmentation to `E` |
| `SquareZeroRealizationDef` | `square_zero_realization(R, S, f, N, ξ)` = `square_zero_graph` over `P` at `cocycle_to_conormal(R, S, f, N, c)`, `c` chosen in `ξ` |

## From an extension to its class

| member | statement |
|---|---|
| `StandardExtensionLiftExists` | every square-zero extension of `S` by `N` over `R` has a lift of `P`'s augmentation — card |
| `ExtensionClassWellDefined` | the class is in `D^1(S/R, N)`, it is the class of every lift's conormal map, and isomorphic extensions have one class — card |

## From a class to an extension, and back

| member | statement |
|---|---|
| `ExtensionRealizeClass` | `ξ` in `D^1(S/R, N)` ⇒ its realization is a square-zero extension with class `ξ` — card |
| `ExtensionRealizeRoundTrip` | every extension `E` is isomorphic to the realization of its class — card |
| `ExtensionIsoIffSameClass` | two extensions on any two types are isomorphic ⇔ they have the same class — card |
