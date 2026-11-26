# sphere — the spheres as spaces: punctured spheres contractible, the equator a homotopy retract of the sphere less its poles, Sⁿ simply connected for n ≥ 2, and Hₙ(Sⁿ) ≅ R

The sphere Sⁿ is euclidean_topology's, the (n + 1)-vectors of norm 1,
and as a space `euclidean_sphere_topology(n)`, its subspace topology.
Less one of its points it is contractible, stereographic projection from
that point carrying it onto a hyperplane. As a set of sequences Sⁿ is the
equator of Sⁿ⁺¹ — an (n + 1)-vector of norm 1 is an (n + 2)-vector of
norm 1 with last coordinate 0 — and the sphere Sⁿ⁺¹ less its north and
south poles is homotopy equivalent to it, by the inclusion one way and
by flattening the last coordinate and rescaling the other.

Those two facts decompose Sⁿ⁺¹ into two open sets, the sphere less the
north pole and less the south pole, contractible, whose intersection is
homotopy equivalent to Sⁿ. For the fundamental group, two simply
connected open sets with a path-connected intersection have a simply
connected union (topology/fundamental_group), so the spheres of
dimension at least 2 are simply connected. For homology, the two open
sets are acyclic, and the Mayer–Vietoris sequence
(simplicial/singular_homology) identifies the top homology of Sⁿ⁺² with
the top homology of Sⁿ⁺¹, one degree lower. H₁(S¹) ≅ R starts the
induction, from the low end of the same sequence: the intersection of the
two punctured circles is two arcs, and H₁ of the circle is the kernel of
R ⊕ R → R ⊕ R, (a, b) ↦ (a + b, a + b). So Hₙ(Sⁿ) ≅ R for n ≥ 1, with
coefficients in any commutative ring R.

No constant is minted; the chapter's statements name the poles in their
own tables.

## The spheres (sphere.go)

| member | statement |
|---|---|
| `SpherePuncturedContractible` | `x ∈ euclidean_sphere(n) ⇒ contractible_space(subtopology(euclidean_topology(n + 1), euclidean_sphere(n) ∖ {x}))` — card |
| `SphereEquatorHomotopyEquivalence` | `∃g. homotopy_equivalence(euclidean_sphere_topology(n), subtopology(euclidean_topology(n + 2), euclidean_sphere(n + 1) ∖ {«north», «south»}), λx. x, g)`, the poles ±e₍ₙ₊₁₎ — card |
| `SphereSimplyConnected` | `simply_connected_space(euclidean_sphere_topology(n + 2))` — card |
| `CircleFirstHomology` | `comm_ring_on(R) ⇒ module_isomorphic(R, homology_module(singular_complex(R, euclidean_sphere_topology(1)), 1), regular_module(R))` — card |
| `SphereHomologyStep` | `comm_ring_on(R) ⇒ module_isomorphic(R, homology_module(singular_complex(R, euclidean_sphere_topology(n + 2)), n + 2), homology_module(singular_complex(R, euclidean_sphere_topology(n + 1)), n + 1))` — card |
| `SphereTopHomology` | `comm_ring_on(R) ⇒ module_isomorphic(R, homology_module(singular_complex(R, euclidean_sphere_topology(n + 1)), n + 1), regular_module(R))` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
