# discrete_l2 — discrete L2 and weighted square-summable sequences

The discrete measure on arbitrary indices is defined by finite subsums, and its nonnegative integral is the weighted discrete mass (integral_convergence.DiscreteNonnegIntegral). Its complex integral agrees with the corresponding unordered sum, and strictly positive finite weights identify its L2 classes with the weighted square-summable functions of sequence_hilbert by an isometric linear bijection.

## Members

| Entry | Statement |
| --- | --- |
| `DiscreteComplexIntegral` | unordered_complex_sums(J, λi:I. complex_of_real(w(i)) * f(i), complex_measure_integral(J, {E:set(I) \| E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), f)) — card |
| `SequenceL2Isometry` | module_isomorphism(complex_ring, weighted_sequence_module(J, w), lp_module(J, {E:set(I) \| E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), &2), ae_class(J, {E:set(I) \| E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))))) ∧ (∀u v:(I → complex). u ∈ weighted_sequence_module(J, w).carrier ∧ v ∈ weighted_sequence_module(J, w).carrier ⇒ l2_inner(J, {E:set(I) \| E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), ae_class(J, {E:set(I) \| E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), u), ae_class(J, {E:set(I) \| E ⊆ J}, discrete_measure(J, λi:I. extended_of_real(w(i))), v)) = weighted_sequence_inner(J, w, u, v)) — card |
