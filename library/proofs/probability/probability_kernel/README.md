# probability_kernel — probability kernels, their mixtures, joins and compositions

A probability kernel from (Ω, S) to (V, T) gives each point of Ω a
probability on V, the mass of each measurable set varying measurably
with the point (`ProbabilityKernelOn`). A kernel acts in three ways. Mixed
against a measure μ on its source it gives the measure μK on its target
(`KernelMixtureDef`); joined with μ it gives the measure μ ⊗ K on pairs,
whose section at x carries K(x) (`KernelJointDef`); and followed by a
second kernel it composes into one (`KernelComposeDef`). For a constant
kernel the join is `product_measure`; the deterministic kernel of a
measurable map is the point mass at its value, and mixing it is pushing
forward.

The join of a probability with a kernel is a probability on the product
σ-algebra with marginals μ and μK, and integrating against it is
integrating against K(x) and then against μ. Composition is associative
with the identity kernel as its unit, so finitely many kernels compose
in any bracketing, and mixing in two steps is mixing the composite.

| Member | Statement |
|---|---|
| `ProbabilityKernelOn` | `probability_kernel_on(Ω, S, V, T, K)`: K(x) a probability on (V, T) at each x ∈ Ω, each x ↦ K(x, t) measurable |
| `KernelMixtureDef` | `kernel_mixture(Ω, S, μ, K, t) = nonneg_integral(Ω, S, μ, λx. K(x, t))` |
| `KernelJointDef` | `kernel_joint(Ω, S, μ, K, E) = nonneg_integral(Ω, S, μ, λx. K(x, {y \| (x, y) ∈ E}))` |
| `KernelComposeDef` | `kernel_compose(V, T, K, L, x, u) = nonneg_integral(V, T, K(x), λy. L(y, u))` |
| `DiracKernel` | the point mass at a measurable map's value is a probability kernel — card |
| `KernelMixtureProbability` | a probability mixed with a probability kernel is a probability — card |
| `KernelMixtureDirac` | mixing the deterministic kernel of f is pushing forward along f — card |
| `KernelJointProbability` | section masses x ↦ K(x, E_x) are measurable, and μ ⊗ K is a probability on the product σ-algebra, ∫_s K(x, t) μ(dx) on a rectangle — card |
| `KernelJointIntegral` | integrating against μ ⊗ K is integrating against K(x) and then μ — card |
| `KernelJointMarginals` | the marginals of μ ⊗ K are μ and μK — card |
| `KernelCompose` | two probability kernels compose into a probability kernel — card |
| `KernelComposeAssoc` | composition of kernels is associative — card |
| `KernelMixtureCompose` | (μK)L = μ(K ; L) — card |
| `KernelComposeDirac` | the identity kernel is a unit for composition on both sides — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
