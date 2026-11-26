// Package vector is the aggregator for the chapters on vectors indexed
// by a natural number: sequences `num → A` whose entries from index n
// on are zero.
//
// The dimension is a TERM. A statement quantifies over it, computes
// with it, and relates vectors of different dimensions by ordinary
// index arithmetic; membership in dimension n is a predicate on the
// sequence, not a type. Where a type `real^N` carries its
// dimension as a type variable whose size is read off `dimindex`, this
// domain reads the same number off a binder, so `n = 0` is an ordinary
// case and the coordinate laws carry no `1 ≤ dimindex` guard.
//
// The scalars are a ring_ops or field_ops record. Whole-type laws state
// comm_ring(R) or field(F); carrier laws state comm_ring_on(R) and keep
// their entry-membership conditions. Derived vector operations read the
// record fields they use: vec_add(R.add, u, v) is the pointwise sum. Under
// the record binder the DSL completes these fields and writes u + v,
// c • u, vec⟨n⟩(u), ⟪u, v⟫_n and Σ_{i<m} x(i) • basis_vector(i).
// A concrete chapter binds its instance once through WithInstance, and
// reads the laws at it, for example dot.AddLeft.Read(real_ring.CommRing).
//
// - vec_space — the module: the pointwise operations, the zero-padded
// membership `vec⟨n⟩(u)`, and the laws that make the sequences
// an abelian group with a scalar action.
// - dot — the bilinear form `⟪u, v⟫_n`, the fold of the pointwise
// product over the active range; bilinearity and symmetry are what the
// fold mechanism and the ring's laws say together. The form also reads
// coordinates off the standard basis, and is non-degenerate on a
// dimension — which is what lets the chapter build a linear map's
// ADJOINT out of it and prove that taking it twice gives the map back.
// - basis — independence, bases and the dimension: which families are
// independent, which span a set exactly, and why every basis of one set
// has the same length. The laws about independence and the standard
// basis hold over any commutative ring; the exchange of one vector for
// another divides by a coefficient, so everything from the exchange
// lemma on is stated over a field.
// - matrix — a linear map written down, and read back: a matrix is a
// sequence of row vectors, its action and its product are dot's form
// applied to rows and columns, and the matrix of a map has the map's
// images of the basis vectors for its columns. The matrix of a linear
// map acts as the map, the matrix of a composite is the product of the
// matrices, and the adjoint dot builds is the transposed matrix acting.
// - determinant — the signed permutation sum over a carrier ring,
// alternating multilinear forms, the cofactor adjugate and the inverse
// matrix when the determinant is nonzero.
// - pfaffian — the signed matching sum of an alternating matrix, its
// congruence and determinant identities, and vanishing on a unimodular
// kernel vector over any commutative carrier ring.
// - euclidean — the reals: positivity of `dot`, the norm as its
// square root, the distance, and the inequalities (Cauchy–Schwarz,
// the triangle inequality) that make ℝⁿ a metric space.
// - euclidean_topology — the topology of ℝⁿ: the metric topology of the
// n-vectors under the distance, read in the n-vectors' own vocabulary;
// convergence coordinate by coordinate and the sequential compactness of
// the unit cube; and Brouwer's fixed point theorem on the cube, through
// Kuhn's combinatorial lemma; the unit sphere Sⁿ and the closed unit ball.
// - matrix_norm — the quadratic form of a positive matrix and the image
// norm of an injective one, bounded above and below by the Euclidean
// norm uniformly over a continuous family on a compact set.
// - vec_derivative — the derivative of a map from ℝⁿ to ℝᵐ at a point, a
// linear map approximating the increment; the rules that compute it, the
// chain rule, the partial derivatives and the criterion of continuous
// partials, and the symmetry of mixed partials.
// - inverse_function — the implicit function theorem with the variables in
// two blocks, and the inverse function theorem as its corollary.
// - vec_smooth — smooth functions on open sets of ℝⁿ: the partial
// derivative as a function, the classes Cᵏ and their closure under sums,
// products and composition, smooth maps, the Jacobian, diffeomorphisms
// and the smooth inverse function theorem, bump functions and partitions
// of unity, and Hadamard's lemma.
// - vec_form — smooth differential forms on Euclidean open sets, read
// on matrices of column vectors, with wedge product, exterior derivative
// and pullback, integration of the time component and matrix-valued
// form calculus, the commutative ring of even forms, Pfaffians and
// orthogonal gauge changes of curvature; zero extension fixes equality
// outside each open domain.
// - vec_integral — the integral over ℝⁿ, one coordinate at a time, of
// continuous functions of rapid decay: Fubini, the linear changes of
// variables, the integral of a partial derivative and of a product of
// one-variable functions; the smooth change of variables for compact
// support; radial integrals in even dimension and the Gaussian integral.
// - vec_null — null sets through countable open cube covers, local
// Lipschitz images, lower-dimensional images and compact null slices.
// - vec_critical_point — critical points of smooth maps on Euclidean open
// sets, and Sard's theorem that their values are null.
// - standard_quotient_spaces — the circle, the spheres and the torus as
// quotient spaces: ℝ/ℤ ≅ S¹, D^(n + 1) with its boundary collapsed ≅
// S^(n + 1), ℝ²/ℤ² ≅ S¹ × S¹.
// - euclidean_simplex — the standard simplices of ℝⁿ⁺¹, the cofaces and
// codegeneracies between them with the cosimplicial identities, and the
// retraction of a simplex onto a horn.
// - convex_topology — convex sets of ℝⁿ as spaces: contractible, retracts
// of ℝⁿ by the nearest point, and Brouwer's fixed point theorem on
// compact convex sets and the ball.
// - circle — π₁(S¹) ≅ ℤ through the covering of the circle by the line;
// the circle is no retract of the disc, and the Borsuk–Ulam theorem in
// the plane.
// - jordan_curve — the Jordan curve theorem, by Maehara's route through
// Brouwer's theorem.
// - sphere — punctured spheres contractible, Sⁿ simply connected for
// n ≥ 2, and Hₙ(Sⁿ) ≅ R by Mayer–Vietoris.
// - convex — the reals again, with no norm and no dimension: a set
// closed under the weighted averages of its points, and the finite
// combinations such a set turns out to be closed under. The weights
// are what needs the order, and the chapter reads no active range.
// - lattice — ℤⁿ, the integer vectors: the generic chapters read at
// the integer ring, and the one thing ℤ adds, its order — which is
// ℝ's, so the positivity of the form is carried across the entrywise
// embedding of ℤⁿ in ℝⁿ and not proved a second time.
//
// # The boundary
//
// Placement follows the definitional layer. vec_space, dot, basis and
// matrix define their constants over an arbitrary ring, so they sit above the
// abstract algebra and the fold mechanism and below every carrier —
// basis states its exchange argument over a field, but an unordered one,
// which the abstract algebra supplies as well; euclidean and convex name
// ℝ's own operations and its order, so they sit above ℝ. An ORDERED
// field is what those two need and the others do not, and they need it
// for different reasons — a square root for the norm, the sign of a
// weight for convexity. euclidean_topology sits above euclidean and
// topology/metric_space: ℝⁿ's open sets are the metric topology of its
// distance, and euclidean itself states the instance that makes the
// n-vectors a metric space. It sits above cartesian/kuhn_labelling as well, whose
// lemma on the grid of naturals its fixed point theorem reads. The
// chapters of algebraic topology on ℝⁿ — convex_topology, circle,
// jordan_curve, sphere — sit above topology/homotopy and
// topology/fundamental_group, whose notions they read at subspaces of
// ℝⁿ, and sphere above simplicial/singular_homology as well;
// euclidean_simplex is below simplicial/singular_set, which reads its
// simplices. vec_smooth sits above vec_derivative, inverse_function,
// determinant and the one-variable integral, whose partial derivatives,
// inverse, determinant and parameter integrals it reads; vec_integral
// sits above vec_smooth and real/lebesgue_integral, its one-variable
// integral being Lebesgue's. lattice sits above ℤ, at whose ring it
// reads the generic chapters, and above euclidean, whose order facts
// are the ones it carries back to the integer vectors.
// None of them is a chapter of `cartesian/`: that domain's term-level
// carrier pads with an arbitrary junk element so that any element type
// can be tupled, whereas a vector space pads with its own zero — the
// convention that makes the pointwise operations closed without a
// truncation, and the reason `vec⟨n⟩(·)` is a subspace rather
// than a set of tuples.
package vector

import (
	_ "github.com/euc-ai/xugo/library/proofs/vector/basis"
	_ "github.com/euc-ai/xugo/library/proofs/vector/circle"
	_ "github.com/euc-ai/xugo/library/proofs/vector/convex"
	_ "github.com/euc-ai/xugo/library/proofs/vector/convex_topology"
	_ "github.com/euc-ai/xugo/library/proofs/vector/determinant"
	_ "github.com/euc-ai/xugo/library/proofs/vector/dot"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean_simplex"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	_ "github.com/euc-ai/xugo/library/proofs/vector/inverse_function"
	_ "github.com/euc-ai/xugo/library/proofs/vector/jordan_curve"
	_ "github.com/euc-ai/xugo/library/proofs/vector/lattice"
	_ "github.com/euc-ai/xugo/library/proofs/vector/matrix"
	_ "github.com/euc-ai/xugo/library/proofs/vector/matrix_norm"
	_ "github.com/euc-ai/xugo/library/proofs/vector/pfaffian"
	_ "github.com/euc-ai/xugo/library/proofs/vector/sphere"
	_ "github.com/euc-ai/xugo/library/proofs/vector/standard_quotient_spaces"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_critical_point"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_null"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_space"
)
