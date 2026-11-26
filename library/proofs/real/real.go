// Package real is the aggregator for ℝ's chapters.
//
// The domain holds two groups. tower is the construction of the reals
// from ℕ (eudoxus_slope → nonneg_real → nonneg_real_formal_diff → the
// type definition → the ordered-field laws → Dedekind completeness).
// The THEORY chapters are built on top of it: real_ring is ℝ's ring
// algebra, derived from the laws tower/real_construction exports;
// real_field is the multiplicative inverse and division, derived from
// real_ring plus the inverse axiom;
// real_order_ring is what ≤ and its strict part < say about
// themselves and about +, − and ·; real_order_field is what the
// order and the inverse say together; real_sgn_abs is the
// sign–absolute-value pair, two case definitions at the same layer
// that become algebra by splitting on their own guards, joined by the
// polar decomposition that is about the pair rather than either half;
// and real_sup_inf is the extrema layer — the binary max/min pair and
// the set-level sup/inf pair with their attained-bound relations
// real_has_sup/real_has_inf, one chapter because finite sup/inf compute through
// max/min and the pair-set bridges are about both layers at once.
//
// The order chapters pair off with the algebra chapters, and one
// criterion assigns a row within each pair — does the statement name
// real_inv or real_div? It separates real_ring from real_field, and it
// separates real_order_ring from real_order_field.
//
// Those four share a deeper property that real_archimedean is defined
// against: every statement in them holds in ANY ordered field, and none
// of them cites tower/real_completeness. real_archimedean is the first chapter
// above the tower whose theorems are false in some ordered field —
// ℝ(x) is the standard counterexample — so it is where the reals stop
// being "some ordered field" and become the reals. What identifies it
// is the STATEMENT (ℕ is unbounded in ℝ) rather than the proof's need
// for completeness: completeness is reachable from the whole ℤ-division
// development and from sup/inf too, so needing it does not single a
// chapter out. Further chapters become further siblings here —
// real_pow, ℝ's powers at a natural exponent, by recursion on it, and
// three chapters built on it: real_zpow, the power at an integer
// exponent, by the exponent's sign — the one of the powers that
// reads ℤ; real_sqrt, the square root, justified
// once by completeness — the nonnegative reals whose square is at most
// a positive x have a least upper bound, and it squares to x — every
// other law being read off that existence and the uniqueness of the
// nonnegative root; and real_rpow, the power at a real
// exponent, exp(a · log x) at a positive base; rational, ℚ as a predicate
// on ℝ, a real that is a quotient of two integers: the rationals are
// a subfield, they lie densely in the line by the Archimedean
// property, and no prime has a square root among them, so the
// irrationals lie densely too; real_polynomial, the polynomial
// functions, whose closure and root theory are written throughout in
// the Σ its own definition names; real_sequences, sequences of reals and their limits, the
// first chapter to speak ε-N and the first consumer of sup and inf
// outside the extrema chapter — monotone convergence is where a least
// upper bound becomes the number a process approaches;
// real_function_limits, limits of real functions at a point, the ε-δ
// chapter, whose sequential characterization is what makes the two
// limit chapters one theory; real_topology, the line as a topological
// space — an instance of topology/topological_space — where the
// intervals are the connected sets and a closed interval is compact,
// both by least-upper-bound arguments; real_continuous, continuity
// of real functions, where the ε-δ reading and the open-set reading
// meet and the intermediate and extreme value theorems follow from the
// abstract chapter's image theorems; and real_derivative, the derivative
// as the limit of a difference quotient, with the rules that compute it
// and what it says about its function — Rolle's theorem, the mean value
// theorem and the sign of the derivative as a test of monotonicity, all
// from the extreme value theorem. Above them sit the series and the
// functions they define: real_series, a series summing as a relation on its
// partial sums, with the comparison and ratio tests and the Cauchy
// product; real_exp_log, the exponential function as the sum of its
// series and the logarithm as its inverse; and real_trigonometry, the
// sine and the cosine by their series, their addition formulas through
// the Cauchy product, and π as twice the one zero of the cosine
// between 0 and 2. real_formal_series reads the formal power series
// of algebra/ring/polynomial/formal_series at the real ring: a simple pole at one,
// which the substitution T ↦ Tᵈ keeps, and the zeta numerator
// (1 − T)(1 − qT)·A of a Riemann–Roch count A, with its support, its
// value at one and the reciprocity of its coefficients.
// real_cardinality stands on the series and on
// rational, and counts the number sets inside ℝ by the comparisons of
// sets/cardinal: the integers and the rationals are countable, the
// rationals exactly as many as the naturals, and the reals are not —
// they are exactly as many as the sets of naturals, a set going to the
// sum of its ternary expansion one way and a real to the rationals
// below it the other, Schröder–Bernstein joining the two injections.
// The tower's internal/ boundary keeps them all honest: they can cite
// tower/real_construction and tower/real_completeness, and the Go compiler refuses them
// the construction underneath.
//
// The chapters' shared statement alphabet — the NAME → type table for
// ℝ's constants — is internal/realvocab, reachable from inside this
// domain only.
//
// The blank imports below are the package's whole content: they trigger
// the chapters' registration into registry and give
// proofs/proofs.go one line per domain rather than one per family.
// real_ordered_instance is ℝ as an ordered field, the instance through which
// the real chapters read the laws of algebra/field/ordered_field;
// real_closed_instance reads the real field through polynomial intermediate
// values; real_polynomial_geometry supplies the finite-dimensional continuity,
// compactness, extrema and polynomial fixed-point sources for field transfer.
// lebesgue_riemann reads the Lebesgue integral of a continuous function on
// an interval as its Riemann integral, and computes the Gaussian integral
// on the line with it.
// hermite_function holds the Hermite polynomials and the Hermite functions on
// ℝⁿ, orthonormal for the integral over ℝⁿ of vector/vec_integral, with the
// ladder relations of a coordinate and its partial derivative.
package real

import (
	_ "github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	_ "github.com/euc-ai/xugo/library/proofs/real/hermite_function"
	_ "github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	_ "github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	_ "github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	_ "github.com/euc-ai/xugo/library/proofs/real/rational"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_closed_instance"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_convex"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_field"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_formal_series"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_integral"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_inverse_trigonometry"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_ordered_instance"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_polynomial_geometry"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_pow"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_power_series"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_ring"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_series"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_taylor"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_topology"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_uniform_convergence"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_zpow"
	_ "github.com/euc-ai/xugo/library/proofs/real/tower"
)
