# standard_quotient_spaces — the circle, the spheres and the torus as quotient spaces

The standard spaces of topology arise by gluing. The line wrapped onto
itself by the integers is the circle, ℝ/ℤ ≅ S¹; the closed ball $D^{n+1}$
with its boundary sphere collapsed to one point is the sphere $S^{n+1}$;
the plane wrapped by the integer lattice, ℝ²/ℤ², is the torus S¹ × S¹.
Each quotient is the quotient topology of `continuous` along the map
sending a point to its class, and each identification is one instance of
`continuous.FibreQuotientHomeomorphic`: a continuous map onto a Hausdorff
space, already onto from a compact part of its domain, identifies the
target with the quotient of the domain by its fibres. What each instance
supplies is the map — t ↦ (cos 2πt, sin 2πt) for the circle, an algebraic
map of the ball for the sphere — and the fact that its fibres are the
classes being glued. The spheres themselves are `euclidean_topology`'s,
subspaces of $\mathbb{R}^{n+1}$, `euclidean_sphere_topology(n)`.

## The circle (circle.go)

Write «circle»(t) for the plane vector (cos 2πt, sin 2πt). The unit
circle of the plane is cut out by x² + y² = 1, and the circle map takes
its values there, cos² + sin² being 1. It is continuous, its two
coordinates being the cosine and the sine after the polynomial t ↦ 2πt.
Two reals have one image exactly when their difference is an integer
(`real_trigonometry.CosSinEqIff` at 2πs and 2πt), and from ⟦0, 1⟧ it
already reaches every point of the circle
(`real_trigonometry.CircleParametrization`, rescaled by 2π). So the
classes {y | integer(y − x)} are its fibres, and the fibre quotient at
the compact ⟦0, 1⟧ identifies ℝ/ℤ with S¹.

| member | statement |
|---|---|
| `UnitCircleEquation` | `u ∈ euclidean_sphere(1) ⇔ vec⟨2⟩(u) ∧ u(0) * u(0) + u(1) * u(1) = &1` |
| `CircleMapOnCircle` | `«circle»(t) ∈ euclidean_sphere(1)` |
| `CircleMapContinuous` | `continuous_map(real_topology, euclidean_sphere_topology(1), «circle»)` |
| `CircleMapFibres` | `«circle»(s) = «circle»(t) ⇔ integer(s - t)` |
| `CircleMapOnto` | `image(«circle», ⟦&0, &1⟧) = euclidean_sphere(1)` |
| `CircleQuotient` | `homeomorphic(quotient_topology(real_topology, λx. {y \| integer(y - x)}), euclidean_sphere_topology(1))` — ℝ/ℤ ≅ S¹ |

## The torus (torus.go)

The circle map in each coordinate is continuous from the plane to the
torus S¹ × S¹, a Hausdorff product of circles, and carries the compact
unit square onto it. Two pairs have one image exactly when both
coordinates differ by integers, so the classes of the integer lattice
are the fibres: ℝ²/ℤ² ≅ S¹ × S¹.

| member | statement |
|---|---|
| `TorusQuotient` | `homeomorphic(quotient_topology(product_topology(real_topology, real_topology), λp. {q \| integer(fst(q) - fst(p)) ∧ integer(snd(q) - snd(p))}), product_topology(S¹, S¹))`, S¹ = `euclidean_sphere_topology(1)` — ℝ²/ℤ² ≅ S¹ × S¹ |

## The spheres (sphere.go)

The collapse map sends x of norm r to (2√(1 − r²)·x, 2r² − 1). Its
squared norm is 4(1 − r²)r² + (2r² − 1)² = 1, so it carries the ball
$D^{n+1}$ into $S^{n+1}$; it sends the boundary Sⁿ to the north pole and
is one to one inside, equal images forcing equal norms and then a common
positive factor; and it is onto, a point away from the pole being the
image of its first coordinates divided by √(2 − 2s). It is continuous
coordinate by coordinate, the norm and the square root on ⟦0, ∞⟭ being
continuous. On the ball its fibres are the classes of the collapse
(quotient topologies of class maps that agree on the space are one), so
with the ball compact and the sphere Hausdorff, $D^{n+1}/S^n \cong S^{n+1}$.

| member | statement |
|---|---|
| `CollapseOnSphere` | `x ∈ euclidean_ball(n + 1) ⇒ «collapse»(x) ∈ euclidean_sphere(n + 1)` |
| `CollapseFibres` | `x ∈ euclidean_ball(n + 1) ∧ y ∈ euclidean_ball(n + 1) ⇒ («collapse»(x) = «collapse»(y) ⇔ x ∈ euclidean_sphere(n) ∧ y ∈ euclidean_sphere(n) ∨ x = y)` |
| `CollapseOnto` | `image(«collapse», euclidean_ball(n + 1)) = euclidean_sphere(n + 1)` |
| `CollapseContinuous` | `continuous_map(subtopology(euclidean_topology(n + 1), euclidean_ball(n + 1)), euclidean_sphere_topology(n + 1), «collapse»)` |
| `QuotientTopologyCongruence` | `(∀x. x ∈ ⋃T ⇒ f(x) = g(x)) ⇒ quotient_topology(T, f) = quotient_topology(T, g)` |
| `SphereQuotient` | `homeomorphic(quotient_topology(subtopology(euclidean_topology(n + 1), euclidean_ball(n + 1)), λx. COND(x ∈ euclidean_sphere(n), euclidean_sphere(n), {x})), euclidean_sphere_topology(n + 1))` — $D^{n+1}/S^n \cong S^{n+1}$ |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
