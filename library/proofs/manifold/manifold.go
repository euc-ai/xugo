// Package manifold collects smooth manifolds described by atlases on
// arbitrary point types and geometric objects indexed by compatible
// charts. Smooth maps are tested on chart preimages; tangent vectors
// transform by Jacobians and the tangent bundle retains their base points.
// Chartwise nullity gives Sard and dense regular values; regular fibers
// carry embedded submanifold atlases in their subspace topology.
// Compact manifolds admit Euclidean embeddings with the weak Whitney
// bounds and smooth tubular retractions. Uniform tangent disks model
// diagonal neighbourhoods, whose two projections are smoothly homotopic.
// Their coordinate fiber maps preserve orientation in positive base charts
// and preserve integrals of top forms supported inside their images.
// Differential forms are compatible Euclidean form families, with wedge,
// exterior derivative and smooth pullback defined in coordinates.
// Positive charts define compact top-form integration and Stokes.
// Riemannian metrics pair tangent vectors; positive orthonormal frames
// carry the unique skew torsion-free connection and its curvature.
// Frame and coordinate changes preserve the normalized curvature Pfaffian
// on positive overlaps, giving the closed global Euler form.
// The de Rham complex records graded cohomology products, smooth homotopy
// invariance and the natural Mayer–Vietoris sequence for two-open covers. Convex factors
// preserve cohomology; finite box unions and compact Euclidean retracts
// have finite-dimensional cohomology. Finite homogeneous bases give
// Künneth comparisons over these box unions and compact retracts, hence
// over compact smooth manifolds without supplied retraction data.
// Betti numbers give the integer-valued de Rham Euler characteristic,
// invariant under smooth homotopy equivalence, additive across finite
// Mayer–Vietoris covers and multiplicative on compact products.
// Angular transgression and radial cutoffs give compact tangent Thom forms.
// Their diagonal kernels give the Euler integral, Poincaré duality and GBC.
// Smooth singular integration and finite-box descent compare de Rham
// cohomology with real singular cohomology on compact manifolds.
// Sobolev sections of smooth projection bundles are represented in finite
// atlas Fourier coordinates, with equivalent localization norms, compact
// order inclusions and bounded chart restriction and extension.
package manifold

import (
	_ "github.com/euc-ai/xugo/library/proofs/manifold/analytic_index"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/chern_thom"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/chern_weil"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/cohomological_index"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/compact_chern"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/compact_de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_betti"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_comparison"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_kunneth"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/de_rham_thom"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/dirac_index"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/embedding_normal"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/index_comparison"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_cotangent"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_critical_point"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_diagonal"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/projection_geometry"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/projective_bundle"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/pseudo_differential"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/riemannian"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/smooth_singular"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/sobolev_section"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/spin_geometry"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/thom_form"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/topological_index"
	_ "github.com/euc-ai/xugo/library/proofs/manifold/torus_manifold"
)
