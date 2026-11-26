# independence — independent events, sigma algebras and random variables

Independence is stated by factorization of probabilities: of two events, of two σ-algebras (independent_sigma), and of the members of any family of σ-algebras, over the finite subfamilies of its index set (independent_sigma_family); a family of real variables is independent when the σ-algebras they pull back are. Independence is checked on generators: an event independent of every member of a π-system is independent of the σ-algebra it generates (`EventIndependentGeneratedSigma`), so two independent π-systems generate independent σ-algebras (`IndependentGeneratedSigma`), and the joins of an independent family over two disjoint blocks of indices are independent, the finite intersections over each block being such a π-system (`IndependentFamilyGroups`). It holds in either order (`IndependentSigmaSymmetric`), survives passing to a smaller σ-algebra (`IndependentSigmaSubset`) and, for variables, to a subfamily with a Borel function applied to each (`IndependentVariableFamilyCompose`). Integrals factor over an independent event: the integral of f over an event of G is the event's probability times the integral of f, for f measurable for a σ-algebra independent of G (`IndependentNonnegIntegral`, `IndependentEventIntegral`). So an integrable variable measurable for a σ-algebra independent of G has its expectation as its conditional expectation given G (`IndependentCondExp`), and in an independent family a Borel function of X(k) has its expectation as its conditional expectation given the variables of any block that does not hold k (`IndependentFamilyCondExp`). Stated and not yet proved: integrable independent variables have product expectation; finitely many fair coins under the uniform law on the subsets of a finite set of coins, a sample being the set of coins that show heads, decide independent σ-algebras on disjoint blocks; and a fair coin tossed beside the space is independent of every pulled-back family, the two-point mixture that holds two distributions in one space.

## Members

| Entry | Statement |
| --- | --- |
| `IndependentSigmaDef` | independent_sigma |
| `IndependentVariablesDef` | independent_variables: measurable, with independent pulled-back σ-algebras |
| `IndependentFamilyDef` | independent_sigma_family |
| `IndependentVariableFamilyDef` | independent_variable_family: each X(i) measurable, with an independent family of pulled-back σ-algebras |
| `BoolMixtureSigmaDef` | `bool_mixture_sigma(Ω, S)`: the sets on Ω × bool with both slices in S |
| `BoolMixtureMeasureDef` | `bool_mixture_measure(μ)`: the average of the two slices' measures |
| `EventIndependentGeneratedSigma` | an event independent of every member of a π-system D is independent of every event of generated_sigma(Ω, D): μ(E ∩ V) = μ(E) * μ(V) |
| `IndependentGeneratedSigma` | independent_sigma(Ω, S, μ, generated_sigma(Ω, C), generated_sigma(Ω, D)) |
| `IndependentFamilyGroups` | independent_sigma(Ω, S, μ, sigma_join(Ω, F, K), sigma_join(Ω, F, L)) for disjoint K, L inside an independent family's index set |
| `IndependentSigmaSubset` | independent_sigma(Ω, S, μ, G, H') for a σ-algebra H' inside H, when G and H are independent |
| `IndependentSigmaSymmetric` | independent_sigma(Ω, S, μ, H, G) when G and H are independent |
| `IndependentVariableFamilyCompose` | restricted to K ⊆ J, with a Borel function h(i) applied to each X(i), an independent family of variables stays independent: `independent_variable_family(Ω, S, μ, K, λi:I. λx:A. h(i, X(i, x)))` |
| `IndependentVariableFamilyMeasurable` | the variables of an independent family are random variables on a probability space: probability_on(Ω, S, μ) ∧ (∀i:I. i ∈ J ⇒ real_measurable(Ω, S, X(i))) |
| `IndependentNonnegIntegral` | for E an event of G, G independent of H, and f measurable for H: nonneg_integral(Ω, S, μ, λx:A. COND(x ∈ E, f(x), &0)) = μ(E) * nonneg_integral(Ω, S, μ, f) |
| `IndependentEventIntegral` | for E an event of G, G independent of H, and X measurable for H: event_integral(Ω, S, μ, E, X) = extended_to_real(μ(E)) * expectation(Ω, S, μ, X) |
| `IndependentCondExp` | for G independent of H and X integrable and measurable for H: is_cond_exp(Ω, S, μ, G, X, λx:A. expectation(Ω, S, μ, X)) |
| `IndependentFamilyCondExp` | for k outside K in an independent family of variables and a Borel h with h ∘ X(k) integrable: `is_cond_exp` of h ∘ X(k) given the join of the σ-algebras of the X(j), j ∈ K, is the constant expectation of h ∘ X(k) |
| `IndependentProductExpectation` | real_integrable(Ω, S, μ, λx:A. X(x) * Y(x)) ∧ expectation(Ω, S, μ, λx:A. X(x) * Y(x)) = expectation(Ω, S, μ, X) * expectation(Ω, S, μ, Y) — card |
| `CoinBlocksProbability` | under the uniform law on the subsets of a finite set K of coins, events decided by disjoint blocks of coins have the product of their frequencies — card |
| `CoinBlocksIndependent` | the σ-algebras of disjoint blocks of coins form an independent family — card |
| `BinaryMixtureExtension` | a fair coin beside a probability space is a probability space, and the coin with the pulled-back independent family is independent — card |
