// Package analysis is the aggregator for functional analysis on complex
// module carriers: hilbert_space (normed and inner-product structure,
// completeness, orthogonal complements and projections), bounded_operator
// (bounded, compact and finite-rank operators and the adjoint), fredholm
// (Fredholm operators, parametrices and the integer index) and
// sequence_hilbert (weighted square-summable sequence spaces);
// torus_fourier (Fourier coefficients and series on the torus) and
// torus_sobolev (integer-order Sobolev sequence spaces and local
// operators on the torus); toeplitz_operator (Toeplitz operators on the
// unilateral sequence space, whose index is the negative winding number).
// Seminorm quotients, Lp spaces, their L2 Hilbert instance and conditional
// projection connect these structures to general measure theory; discrete_l2
// identifies the positive-weight discrete instance with sequence_hilbert.
// The carriers are complex modules, so every family here sits above
// complex/ and reads ℂ through its public chapters.
package analysis

import (
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bott_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/conditional_projection"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/discrete_l2"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/fredholm"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/l2_space"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/lp_space"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/toeplitz_operator"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_fourier"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_pseudo_differential"
	_ "github.com/euc-ai/xugo/library/proofs/analysis/torus_sobolev"
)
