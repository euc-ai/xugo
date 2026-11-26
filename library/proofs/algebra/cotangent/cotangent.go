// Package cotangent is the aggregator for the cotangent complex of a
// ring map and André–Quillen homology: polynomial simplicial algebras
// hosted in one type, the standard resolution of an algebra and the
// relative resolution over it, the comparison of resolutions, the
// cotangent complex with coefficients in a module, the transitivity
// triangle of a tower of rings, the complex computed on polynomial
// algebras, quotients and étale hypersurfaces, the first cohomology read
// as conormal maps modulo derivations, the classification of
// square-zero extensions by it, and the deformations of an algebra over a
// square-zero thickening. Each is one family.
//
// # The route
//
// A resolution is a polynomial simplicial algebra whose underlying
// simplicial module has an exact Moore complex, and the cotangent
// complex is its module of differentials: the finitely supported
// functions on the names under the Jacobians of the faces. The general
// module of Kähler differentials enters in degree 0 only. Two
// resolutions are compared degree by degree on the generators the
// degeneracies keep, the Kan property entering only as horn filling. The
// transitivity triangle is three double complexes and the assembly
// lemmas of chain_complex: the rows of its right term are contracted by
// an induction that separates the two simplicial directions of a
// bisimplicial set and takes the diagonal, and its left map is
// identified through the Alexander–Whitney map. In degree 1 the cochains
// are read on the standard presentation R[S] → S: a 1-cocycle is a
// conormal map on its kernel, a coboundary the restriction of a
// derivation, and D^1 classifies the square-zero extensions, a class
// realized by the graph of a conormal map and an extension read back
// through a lift. The cohomology sequence of a tower is the dual of the
// same triangle taken with coefficients in T: the totals and the
// cotangent complexes are based complexes, and the dual of the split
// sequence of totals, joined to the cotangent complexes by the edges,
// carries its long exact sequence (free_complex_duality in the module
// domain). Over a thickening R → R₀ with square-zero kernel and an algebra
// T over R₀, the right map of that sequence is the pullback of extensions,
// the class of R pushed into the coefficients is the class a deformation
// of T must pull back to, and the connecting map at it is the obstruction
// to a deformation. None of the following is
// used or stated here: the Eilenberg–Zilber theorem beyond its
// Alexander–Whitney half, spectral sequences, a base-change theorem for
// the cotangent complex, the homotopy invariance of Kan complexes, and
// the normalization theorem comparing the Moore complex with the face
// complex.
//
// The host type is a type variable and every ring keeps its own type,
// so a theorem of the domain applies to the rings of other chapters as
// those chapters write them; the room each ring's carrier needs in the
// host is the hypothesis that brings them together, and at a powerset
// host it passes from a ring to its polynomial ring, its quotients and
// its localizations, so a tower is read in the host chosen for its base.
package cotangent

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cohomology_one"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/resolution_comparison"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
)
