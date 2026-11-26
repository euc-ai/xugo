# elliptic_hasse_weil — the Hasse–Weil bound read at an elliptic curve: the Riemann hypothesis for every extension degree, and Hasse's theorem

A smooth Weierstrass cubic (elliptic_curve's smooth_weierstrass: 2 ≠ 0
and 4a³ + 27b² ≠ 0) over a finite field k of q elements is a smooth finite curve
of genus one in the sense of scheme/smooth_curve
(closed_point.WeierstrassSmoothFiniteCurve, elliptic_curve.GenusOne), and its
Frobenius count N_m is the curve's count of closed points of degree dividing
m, weighted by degree (closed_point.FrobeniusCountIsWeightedMultiples). The
curve is read as weil_curve reads one: its function field K is a subfield of
an algebraically closed field M, and the smooth datum is stated in M
restricted to K, where closed_point reads it; that field keeps M's
operations, so its 2 ≠ 0 and its discriminant are M's.
weil_curve.HasseWeilClosedPoints bounds that count by 2g·√(q^m) = 2·√(q^m)
from q^m + 1. Squaring gives the integer form, and m = 1 is Hasse's
theorem, N₁ = N (closed_point.FrobeniusCountOne) because the closed points
of degree one are the rational ideal pairs. The trace q + 1 − N is the one
integer this chapter defines. Complex roots and general genus are
weil_curve's.

## Definitions

| Member | Meaning |
|---|---|
| `FrobeniusTraceDef` | `elliptic_frobenius_trace(R, k, x, y) = card(k) + 1 − N`, the trace of Frobenius q + 1 − N |

## Theorems

| Member | Statement |
|---|---|
| `RiemannHypothesisEllipticReal` | For every m≥1, abs(q^m+1−N_m)≤2 sqrt(q^m). |
| `RiemannHypothesisElliptic` | For every m≥1, (q^m+1−N_m)²≤4q^m. |
| `HasseTheoremReal` | The rational point count satisfies abs(N−q−1)≤2 sqrt(q). |
| `HasseTheorem` | The integer Frobenius trace satisfies (q+1−N)²≤4q. |
