// Package complex is the aggregator for the complex numbers:
// complex_field (the type, its arithmetic, conjugation, and ℂ as an
// instance of the abstract field), complex_abs (the modulus),
// complex_series (series and their sums), complex_exp (the
// exponential, the cosine and the sine, and Euler's formula) and
// complex_polynomial (the fundamental theorem of algebra);
// complex_topology (ℂ as a metric space: limits and continuity) and
// complex_derivative (the complex derivative and the holomorphic
// functions); complex_power_series (power series, differentiated term
// by term, and the derivatives of exp, cos and sin); complex_log (the
// argument and
// the principal logarithm); path_integral (integrals along piecewise
// smooth paths); cauchy_integral (Cauchy's theorem and integral formula
// and what follows from them, series of holomorphic functions among it);
// residue (winding indices, residues, the orders of zeros
// and poles); complex_cpow (complex powers), dirichlet_series, riemann_zeta (ζ on
// Re s > 0) and tauberian (Newman's theorem); group_character and
// dirichlet_character (characters of finite abelian groups and modulo q)
// and dirichlet_l_function (their L-series). A complex
// number is a pair of reals, so every family here sits above real/ and
// reads ℝ through its public chapters.
package complex

import (
	_ "github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_log"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	_ "github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_character"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_l_function"
	_ "github.com/euc-ai/xugo/library/proofs/complex/dirichlet_series"
	_ "github.com/euc-ai/xugo/library/proofs/complex/finite_spectrum"
	_ "github.com/euc-ai/xugo/library/proofs/complex/gaussian_integer"
	_ "github.com/euc-ai/xugo/library/proofs/complex/group_character"
	_ "github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	_ "github.com/euc-ai/xugo/library/proofs/complex/residue"
	_ "github.com/euc-ai/xugo/library/proofs/complex/riemann_zeta"
	_ "github.com/euc-ai/xugo/library/proofs/complex/tauberian"
)
