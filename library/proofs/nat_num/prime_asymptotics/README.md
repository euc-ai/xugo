# prime_asymptotics — the prime number theorem: ψ(n) ~ n and π(n) ~ n / log n

The prime number theorem is proved for Chebyshev's ψ first:
ψ(n)/n tends to 1 (`PsiAsymptotic`), and then $\frac{\pi(n) \cdot \log n}{n}$ tends to 1
(`PrimeNumberTheorem`). The proof is Newman's.

The coefficients ψ(n)/n − 1 are bounded, by Chebyshev's bound. For
Re s > 1 their Dirichlet series is the series of ψ(n)/n less ζ(s), and
partial summation writes the first as D(Λ, s)/s plus a correction
series, the table's `«correction»`, the sum of its terms
`«correctionTerm»(s, n)`, that converges on Re s > 0. A linear bound
ψ(n + 1) ≤ C·(n + 1) puts the term under C·|s + 1| times
`«correctionPower»(s, n)`, the power $(n+1)^{-\operatorname{Re} s - 1}$, for s ≠ 0 with
Re s ≥ −2 (`PsiCorrectionTermBound`). Now
D(Λ, s) and ζ(s) have the same pole at 1 and are otherwise holomorphic
near the closed half-plane Re s ≥ 1 — that is ζ's continuation and its
having no zero on the line — so the poles cancel and the series of
ψ(n)/n − 1 continues holomorphically past the line
(`PsiSeriesContinuation`). By `tauberian.NewmanTauberian` it converges
at s = 1 (`PsiSeriesConverges`): the series of $\frac{\psi(n)/n - 1}{n}$ converges. ψ is monotone, so
were ψ(N) above (1 + ε)·N for arbitrarily large N, a block of that
series starting at N would stay above a fixed positive number, against
Cauchy's criterion; and likewise from below.

π is read back from ψ in two steps: ψ(n) ≤ π(n)·log n, and
$\pi(n) \le m + \frac{\psi(n)}{\log m}$ for m about $n^{1 - \frac{1}{k}}$.

## The Dirichlet series of ψ(n)/n − 1 (psi_series.go)

| member | statement |
|---|---|
| `PsiCorrectionTermBound` | `∀s:complex. ∀n:num. ∀C:real. -&2 ≤ re(s) ∧ s ≠ &0 ∧ chebyshev_psi(n + 1) ≤ C * &(n + 1) ⇒ \|«correctionTerm»(s, n)\| ≤ C * \|s + &1\| * «correctionPower»(s, n)` |
| `PsiCorrectionSums` | `∀s:complex. &0 < re(s) ⇒ complex_sums(«correctionTerm»(s), «correction»(s))` |
| `PsiCorrectionHolomorphic` | `holomorphic_on({s:complex \| &0 < re(s)}, «correction»)` |
| `PsiSeriesIdentity` | `∀s:complex. &1 < re(s) ⇒ dirichlet_sums(λn:num. &(chebyshev_psi(n) / &n), s, dirichlet_series(λn:num. &von_mangoldt(n), s) / s + «correction»(s))` |
| `PsiSeriesContinuation` | `∃U:set(complex). ∃F:(complex → complex). U ∈ complex_topology ∧ (∀s:complex. &1 ≤ re(s) ⇒ s ∈ U) ∧ holomorphic_on(U, F) ∧ (∀s:complex. &1 < re(s) ⇒ dirichlet_sums(λn:num. &(chebyshev_psi(n) / &n - &1), s, F(s)))` |
| `PsiSeriesConverges` | `∃v:complex. dirichlet_sums(λn:num. &(chebyshev_psi(n) / &n - &1), &1, v)` |

## The asymptotics (psi.go)

| member | statement |
|---|---|
| `PsiUpperAsymptotic` | `∀ε:real. &0 < ε ⇒ ∃K:num. ∀n:num. K ≤ n ⇒ chebyshev_psi(n) ≤ (&1 + ε) * &n` |
| `PsiLowerAsymptotic` | `∀ε:real. &0 < ε ⇒ ∃K:num. ∀n:num. K ≤ n ⇒ (&1 - ε) * &n ≤ chebyshev_psi(n)` |
| `PsiAsymptotic` | `(λn:num. chebyshev_psi(n) / &n) ⟶ &1` |
| `PrimeCountingUpperAsymptotic` | `∀ε:real. &0 < ε ⇒ ∃K:num. ∀n:num. K ≤ n ⇒ &prime_counting(n) * log(&n) ≤ (&1 + ε) * &n` |
| `PrimeNumberTheorem` | `(λn:num. &prime_counting(n) * log(&n) / &n) ⟶ &1` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
