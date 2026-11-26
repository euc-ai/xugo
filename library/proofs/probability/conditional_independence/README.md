# conditional_independence — conditional independence of σ-algebras in Doob's form

Two sub-σ-algebras G and H of a probability space are independent
given a third, K, when every version of the conditional expectation of
the indicator of an event of G given K is also a version given σ(K ∪
H) (`CondIndependentSigmaDef`). The definition is an implication
between two facts of the conditional-expectation relation, so no
choice of version enters and no product of versions is written; the
probability and sub-σ-algebra hypotheses are part of it, as they are of
`independent_sigma`.

The chapter states the operations a semigraphoid asks for —
triviality, monotonicity, the two absorption laws, weak union,
contraction and symmetry through the product characterization — and
reads conditional independence back as an identity of event
probabilities on each fibre of a conditioning variable at a point. At
a trivial condition it is `independent_sigma`; that bridge is stated
here, read from `probability/independence`, which does not read this
chapter.

| Member | Statement |
|---|---|
| `CondIndependentSigmaDef` | `cond_independent_sigma(Ω, S, μ, G, H, K)`: every version of E[1_E \| K], E ∈ G, is a version of E[1_E \| σ(K ∪ H)] |
| `CondIndepTrivial` | G ⊥ {∅, Ω} \| K — card |
| `CondIndepMonoLeft` | a sub-σ-algebra of the left side stays independent — card |
| `CondIndepMonoRight` | a sub-σ-algebra of the right side stays independent — card |
| `CondIndepAbsorbRight` | G ⊥ H \| K ⇔ G ⊥ σ(H ∪ K) \| K — card |
| `CondIndepWeakUnion` | G ⊥ σ(H ∪ L) \| K gives G ⊥ H \| σ(K ∪ L) — card |
| `CondIndepContraction` | G ⊥ H \| σ(K ∪ L) and G ⊥ L \| K give G ⊥ σ(H ∪ L) \| K — card |
| `CondIndepProduct` | G ⊥ H \| K exactly when the product of versions for E ∈ G and D ∈ H is a version for E ∩ D — card |
| `CondIndepSymmetric` | G ⊥ H \| K gives H ⊥ G \| K — card |
| `CondIndepAbsorbLeft` | G ⊥ H \| K gives σ(G ∪ K) ⊥ H \| K — card |
| `CondIndepUnconditional` | G ⊥ H \| {∅, Ω} ⇔ independent_sigma(Ω, S, μ, G, H) — card |
| `CondIndepPointFiber` | given σ(W), at a point w with {w} measurable: μ(E ∩ D ∩ F) μ(F) = μ(E ∩ F) μ(D ∩ F), F = {W = w} — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
