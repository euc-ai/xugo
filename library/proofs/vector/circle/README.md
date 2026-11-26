# circle — the fundamental group of the circle, the circle as no retract of the disc, and the Borsuk–Ulam theorem in the plane

The circle map «circle»(t) = (cos 2πt, sin 2πt) of standard_quotient_spaces
is a covering of the unit circle S¹ by the line: the circle less one
point is evenly covered, its preimage the disjoint open intervals of
length 1 between the preimages of the missing point. A loop of the circle
at «circle»(s) lifts to a path of the line from s, ending at s + k for an
integer k, and homotopic loops lift to homotopic paths with the same end
(topology/covering_space). So every loop at «circle»(s) is homotopic to
exactly one of the standard loops t ↦ «circle»(s + k t), and joining two
standard loops adds their integers: the integers, under addition, are
the fundamental group of the circle, k going to the class of the loop
that winds k times.

π₁(S¹) ≅ ℤ is the whole of what follows. The closed disc is convex,
hence simply connected, and a retraction of it onto its boundary circle
would factor the identity of π₁(S¹) through the trivial group: the circle
is not a retract of the disc, which is Brouwer's theorem in the plane
read in its equivalent form. A map of the circle to itself that commutes
with x ↦ −x lifts to a path whose ends differ by an odd integer, so it is
not homotopic to a constant map; and a continuous map of the 2-sphere to
the plane with no antipodal pair sharing a value would give such a map
that extends over the disc, through the upper hemisphere. So every
continuous map of S² to ℝ² sends some pair of antipodal points to one
point.

No constant is minted. The chapter's table names «circle» and «D²», the
closed disc; the circle as a space is `euclidean_sphere_topology(1)`.

## The fundamental group of the circle (fundamental_group.go)

| member | statement |
|---|---|
| `CircleCovering` | `covering_map(real_topology, euclidean_sphere_topology(1), «circle»)` — card |
| `CircleLoopStandard` | `g ∈ loops_at(euclidean_sphere_topology(1), «circle»(s)) ⇒ ∃k:int. path_homotopic(euclidean_sphere_topology(1), g, λt. «circle»(s + real_of_int(k) * t))` — card |
| `CircleLoopsDistinct` | `path_homotopic(euclidean_sphere_topology(1), λt. «circle»(s + real_of_int(j) * t), λt. «circle»(s + real_of_int(k) * t)) ⇒ j = k` — card |
| `CircleLoopsJoin` | `path_homotopic(euclidean_sphere_topology(1), path_join(λt. «circle»(s + real_of_int(j) * t), λt. «circle»(s + real_of_int(k) * t)), λt. «circle»(s + (real_of_int(j) + real_of_int(k)) * t))` — card |
| `CircleFundamentalGroup` | `group_isomorphism(additive_group(int_ring), fundamental_group(euclidean_sphere_topology(1), «circle»(s)), λk. path_class(euclidean_sphere_topology(1), λt. «circle»(s + real_of_int(k) * t)))` — card |

## The disc and the sphere (disc.go)

| member | statement |
|---|---|
| `NoRetractionDisc` | `¬retract_of(«D²», euclidean_sphere(1))` — card |
| `OddMapNotNullHomotopic` | `continuous_map(euclidean_sphere_topology(1), euclidean_sphere_topology(1), g) ∧ (∀x. x ∈ euclidean_sphere(1) ⇒ g(-x) = -g(x)) ⇒ ¬∃c. homotopic_rel(euclidean_sphere_topology(1), euclidean_sphere_topology(1), ∅, g, λx. c)` — card |
| `BorsukUlamPlane` | `continuous_map(euclidean_sphere_topology(2), euclidean_topology(2), f) ⇒ ∃x. x ∈ euclidean_sphere(2) ∧ f(-x) = f(x)` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
