# vec_critical_point — critical points of smooth Euclidean maps, and Sard's theorem that their values are null

For a smooth map f from an open subset U of ℝⁿ into ℝᵐ, a point is
critical when its Jacobian does not map the n-vector carrier onto the
m-vector carrier. The definition uses `vec_jacobian_matrix` and
`matrix_act`, so rank is expressed as failure of surjectivity without
introducing another matrix-rank convention. The differential reading
is made under the smoothness hypothesis; outside differentiability,
the chosen partial derivatives have no asserted analytic meaning.

Sard's theorem says that the image of these points is a null set in
the cube-cover sense of `vec_null`. The theorem includes an empty
domain and zero dimensions. A map to ℝ⁰ has no critical points; when
n = 0 < m its image has at most one point and is null.

| member | statement |
|---|---|
| `CriticalPointDef` | `vec_critical_point⟨n, m⟩(f, x)`: x is an n-vector and its Jacobian fails to be onto the m-vectors |
| `SmoothSard` | for open U and smooth f : U → ℝᵐ, `image(f, {x ∈ U \| vec_critical_point⟨n, m⟩(f, x)})` is null in ℝᵐ — card |

The proof proceeds by source dimension and by strata where successive
derivatives vanish. A nonzero first derivative straightens one
coordinate, bringing in the compact-slice theorem. A nonzero
differential of a higher partial supplies a hypersurface and lowers
the source dimension. Where sufficiently many derivatives vanish,
Taylor's theorem on segments inside a compact neighbourhood gives
uniform estimates, and subdivision forces the image volume to zero.
Countable local covers assemble these results.

The low-dimensional image theorem lives below this chapter and does
not use Sard. Finite differentiability at the optimal threshold and
the formulation on abstract manifolds are separate statements from
the smooth Euclidean theorem here.
