// Package scheme is the aggregator for the chapters of algebraic
// geometry over a commutative ring on a set: the prime spectrum and its
// Zariski topology, sheaves of rings and locally ringed spaces, the
// structure sheaf of the spectrum, schemes, Spec on ring maps, and the
// correspondence between maps to a spectrum and global-section maps; and
// the curves held by two affine charts inside a function field — the
// projective line, curves finite over it with their Riemann–Roch, the
// elliptic curve and its group, their finite separable covers with
// Riemann–Hurwitz, and the scheme two charts glue to.
//
// # The boundary
//
// A point of the spectrum is a prime ideal, a set; a section of the
// structure sheaf is a function from primes to fractions, each a class
// of pairs; a germ is a class of pairs of an open set and a section.
// Every object here is therefore a set of one fixed type built from the
// ring's carrier type, and every construction a formula: two rings of
// fractions are two sets of classes of one type, two stalks two sets of
// germs of one type, and no equality between types is ever asked. The
// section-ring records of a sheaf are indexed by the open set, since
// the ring of sections changes with it.
//
// The curve chapters keep the same discipline by another means: a curve
// is a function field L with the coordinate rings of two charts inside
// it, so every ring, every invertible module and every point is a subset
// of L or a pair of them, and a module on the curve is a pair of chart
// modules inside one container module over the overlap. Nothing is
// glued by an isomorphism and nothing is transported; the cohomology of
// a two-chart cover has two terms and is read off directly. Among the
// deformations of a curve held by two charts a square-zero extension of a
// chart ring sits on a type of its own, and two are compared by an
// isomorphism of extensions, never by an equality of types.
//
// # The chapters
//
// - prime_spectrum — the prime spectrum, V(I) and D(f), the Zariski
// topology, D(f) a base of compact open sets, and when the D(h) cover a
// D(f).
// - locally_ringed_space — presheaves and sheaves of rings, stalk rings,
// locally ringed spaces, and their isomorphisms between spaces
// of two types, with local morphisms and unit tests by germs.
// - structure_sheaf — the structure sheaf of the spectrum: the sections
// over D(f) are the fractions at the powers of f, the global sections
// are the ring, the stalk at p is the local ring at p, and the spectrum
// is a locally ringed space.
// - scheme — schemes, the locally ringed spaces covered by open sets
// isomorphic to the spectra of their rings of sections; the spectrum of
// a ring is one.
// - spec_functor — Spec on ring homomorphisms, its composition and
// identity equations, and basic opens as spectra of localizations.
// - gamma_spec — maps to Spec R correspond to ring maps R to global
// sections; affine morphisms recover their ring maps.
// - lattice_pair — a curve held by the coordinate rings of two affine
// charts and their overlap, modules on it as pairs of chart modules
// glued on the overlap, and their two-term Čech cohomology.
// - projective_line — the projective line inside a field as the lattice
// pairs over k[t] and k[1/t]: Laurent coefficients, the pairs O(n) and
// their cohomology, and duality with O(−2) by the coefficient of t⁻¹.
// - biaffine_scheme — the scheme a biaffine datum glues from the spectra
// of its two charts: its points as pairs of chart ideals, its sheaf of
// pairs of chart sections, the charts as spectra of their rings, and the
// projective line inside a field as one.
// - algebraic_curve — curves finite over the projective line inside their
// function field: finiteness, degree, duality and Riemann–Roch.
// - curve_cover — finite separable covers of curves over one line,
// pullback, the inverse different, the dualizing bridge and Riemann–Hurwitz.
// - elliptic_curve — the curve y² = x³ + ax + b over a field: its two
// affine charts as quotients of free algebras and inside its function
// field, smooth when 2 ≠ 0 and 4a³ + 27b² ≠ 0, its rational points,
// genus one, the lines through its points, and its points as a group
// through Pic⁰.
// - closed_point — arbitrary closed points of a Weierstrass curve, their
// residue degrees, the invertibility of their ideals, and the coordinate
// count of rational points; the charts are normal, the datum is a smooth
// finite curve, and its closed points, degrees and Frobenius counts are
// that curve's.
// - curve_valuation — pole spaces at the origin.
// - zeta_recurrence — the trace and Lucas sequences of the elliptic zeta
// numerator.
// - quadratic_twist — coefficient twisting and affine solution pairing.
// - elliptic_hasse_weil — the Hasse–Weil bound read at an elliptic curve:
// the elliptic Riemann hypothesis for every extension degree, and Hasse's
// theorem at degree one.
// - biaffine_deformation — the deformations of a curve held by two
// charts: two chart extensions glued by an isomorphism of their
// localizations on the overlap, the classification of those extensions
// through the derivation pair and the chart classes, their group under
// the chartwise Baer sum, and the obstruction in two levels, local in D² of each chart and gluing in the cokernel of
// the restrictions to the overlap.
package scheme

import (
	_ "github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/biaffine_deformation"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/biaffine_scheme"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/closed_point"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/constant_twist"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/cover_deformation"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/curve_cover"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/curve_valuation"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/curve_zeta"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/divisor_lattice_correspondence"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/elliptic_hasse_weil"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/fixed_twist_models"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/galois_good_fibres"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/gamma_spec"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_sequence"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/locally_ringed_space"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/plane_model"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/prime_spectrum"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_affine_piece"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_form_chart"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_form_pair"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_generic_point"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_line_duality"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_line_free_pair"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_presentation"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_sections"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/projective_transfer"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/quadratic_twist"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/rational_point_bound"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/regular_point"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/scheme"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve_riemann_roch"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/spec_functor"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/structure_sheaf"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/twist_quotient_bound"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/twisted_count"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/weil_curve"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/zeta_recurrence"
)
