# de_rham — the de Rham complex, cohomology classes, pullback and smooth homotopy invariance

The chapter holds the de Rham complex of a smooth manifold, its
cohomology modules and classes, the pullback of classes along smooth
maps, and smooth homotopy invariance with its first consequence, the
cohomology of a convex factor. Four chapters are cut from it:
[de_rham_cover](../de_rham_cover/README.md) has the two-open cover
sequence and finite-dimensionality,
[de_rham_product](../de_rham_product/README.md) the wedge and external
products of classes, [de_rham_kunneth](../de_rham_kunneth/README.md)
the cohomology of a product through a finite homogeneous basis, and
[de_rham_betti](../de_rham_betti/README.md) the Betti numbers and the
Euler characteristic.

The de Rham complex of a smooth n-dimensional manifold is a
`complex_ops(real, form)` record. Its degree-k carrier is the existing
module of normalized manifold k-forms; its coboundary is exterior
differentiation. Addition, zero, negation and real scaling are the
same pointwise operations in every degree. The form-module and
exterior-derivative laws make this a nonnegative cochain complex.

The chapter uses the generic cocycles, coboundaries and quotient
modules from [chain_complex](../../algebra/module/chain_complex/README.md).
`de_rham_cohomology_module` is that cohomology module, and
`de_rham_class` takes a form to its coset by the coboundaries. A class
is a set of whole normalized forms, not a selected representative.
Form membership and closedness put a representative's coset in the
cohomology carrier. Every class has such a representative. Quotient
addition and scalar multiplication take sums and scalar multiples of
representatives.

Two closed (k+1)-forms have the same class exactly when their difference
is the exterior derivative of a k-form. In degree zero, coboundaries
are only the zero form, so two closed zero-forms have the same class
exactly when the forms themselves agree. There is no negative-degree
space obtained by natural-number subtraction. Above the ambient
dimension every form is zero, and cohomology has its zero class alone.

For a smooth map f from an n-dimensional source to an m-dimensional
target, degreewise form pullback is a cochain map from the target
complex to the source complex. `de_rham_pullback` is its induced map
on the quotient modules. It is linear, sends the class of a closed
form to the class of its pullback, preserves identities and reverses
composition. Agreement of maps on the source carrier suffices for
agreement of the induced maps on genuine target cohomology classes.
The constants and maps are total, but these carrier guards are part
of every functor law.

## Time contraction and homotopy

Time points are normalized vectors in Euclidean one-space. An open
set J contains every time point for 0 <= t <= 1. The cylinder uses
`product_topology(T, subtopology(euclidean_topology(1), J))` and its
paired product atlas. The map j_t sends x to `(x, time_point(t))` and
is smooth whenever its time point belongs to J. J may have additional
components; no contraction of all of J is asserted.

`manifold_form_homotopy` uses the Euclidean homotopy operator on each
base chart paired with the identity time chart. Its argument k is
its **output degree**: K takes (k+1)-forms on the cylinder to k-forms
on the base. Time is the last coordinate, but its vector is inserted
in the first form slot. This convention gives

$$
dK(\omega)+K(d\omega)=j_1^\ast\omega-j_0^\ast\omega\quad(\deg\omega>0),\qquad K(d\omega)=j_1^\ast\omega-j_0^\ast\omega\quad(\deg\omega=0).
$$

Product transitions fix time. Their horizontal Jacobian blocks are
independent of the time variable, so the finite coefficients in the
change of horizontal frame pass through the integral. This proves
that K respects compatible-chart overlap equations. Invalid base
charts and exterior coordinate values remain zero. Neither compact
support, compactness nor orientation of the base is required.

The two equations give the generic cochain homotopy between endpoint-one
and endpoint-zero pullback. The generic h(q) has input degree q,
so h(q) is K at output degree q-1 when q>0; its unused h(0) is explicitly
the zero operator. This separates the bottom-degree equation from the
successor-degree equation.

A smooth H from the cylinder to another manifold therefore gives equal
endpoint maps on cohomology. Pull a target class back along H, apply the
endpoint cochain homotopy, then use contravariant composition. The
endpoint maps may agree with the stated f and g only on the base
carrier; the carrier congruence theorem supplies precisely the required
identification. No representative is chosen by the induced-map definition.

## Convex factors

For a nonempty convex Euclidean open U and any smooth manifold M,
projection U×M → M induces an isomorphism on cohomology. A specified
point of U gives its inverse by section pullback. Pairing the smooth
convex contraction with the identity of M gives the required homotopy;
neither compactness nor orientation is needed, and M may be empty.
The class types on M and U×M differ, so this is an isomorphism between
modules rather than their literal equality.

A nonempty convex open has one-dimensional cohomology in degree zero
and zero cohomology in positive degrees. The empty manifold has the
zero module in every degree. Its zero class is the singleton containing
the zero form. These cases include Euclidean dimension zero.

## Definitions

| Member | Constant |
|---|---|
| `ComplexDef` | `de_rham_complex⟨n⟩(T, 𝒜)` |
| `CohomologyModuleDef` | `de_rham_cohomology_module⟨n⟩(T, 𝒜, k)` |
| `ClassDef` | `de_rham_class⟨n⟩(T, 𝒜, k, ω)` |
| `PullbackDef` | `de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)` |
| `HomotopyDef` | `manifold_form_homotopy⟨n⟩(T, 𝒜, J, k, ω)` |

## Classes and the cochain complex

| Member | Statement |
|---|---|
| `Complex` | Manifold forms and exterior differentiation form a cochain complex — card |
| `CohomologyModule` | Every de Rham cohomology degree is a real module — card |
| `CocycleClosedForm` | The cocycles of the de Rham complex are the closed forms |
| `ClassMember` | A closed form represents a class in cohomology — card |
| `ClassRepresentative` | Every cohomology class has a closed form representative — card |
| `ClassAdd` | Class addition takes the pointwise sum of representatives — card |
| `ClassScale` | Class scaling takes the real scalar multiple of a representative — card |
| `ClassEqualSucc` | Closed successor-degree forms have equal classes exactly when their difference is exact — card |
| `ClassAddExact` | Adding an exact form to a closed form does not change its class |
| `ClassEqualZero` | Closed zero-forms have equal classes exactly when they agree — card |
| `CohomologyAboveDimension` | Cohomology above the manifold dimension has only its zero class — card |

## Pullback

| Member | Statement |
|---|---|
| `PullbackCochain` | Smooth form pullback is a contravariant cochain map — card |
| `PullbackCocycle` | Smooth pullback carries cocycles to cocycles |
| `PullbackHom` | Pullback induces a homomorphism on cohomology — card |
| `PullbackClass` | The class of a closed form pulls back to the class of its pullback — card |
| `PullbackCongruence` | Source-carrier agreement preserves the induced cohomology map — card |
| `PullbackIdentity` | Identity pullback fixes every cohomology class — card |
| `PullbackCompose` | Pullback reverses smooth-map composition on cohomology — card |

## Homotopy

| Member | Statement |
|---|---|
| `EndpointSmooth` | A time slice inside the open time set is a smooth map into the cylinder — card |
| `HomotopyForm` | Time contraction and integration give a normalized base form — card |
| `HomotopyLinear` | The homotopy operator is linear between the appropriate form degrees — card |
| `HomotopyOperator` | Positive-degree forms satisfy dK+Kd = j₁*−j₀* — card |
| `HomotopyOperatorZeroDegree` | Degree-zero forms satisfy Kd = j₁*−j₀* — card |
| `EndpointCochainHomotopy` | The degree-adjusted operator is a cochain homotopy of the endpoint pullbacks — card |
| `HomotopyInvariance` | Smoothly homotopic maps induce equal maps on de Rham cohomology — card |

## Convex factors and the empty manifold

| Member | Statement |
|---|---|
| `ConvexProductCohomology` | Projection from a nonempty convex open times any manifold induces an isomorphism, with section pullback as inverse — card |
| `EmptyCohomology` | Empty manifolds have singleton cohomology carriers and dimension zero — card |
| `ConvexOpenCohomology` | Convex Euclidean opens have the expected zero- or one-dimensional cohomology — card |
