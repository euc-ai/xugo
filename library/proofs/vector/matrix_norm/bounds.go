// A continuous family of positive or injective matrices over a compact
// parameter set compares the measure it gives a vector with the
// Euclidean norm by two constants, uniformly in the parameter. Both
// comparisons are read off one theorem: a continuous function of a point
// and a vector, positive and homogeneous in the vector, lies between two
// positive multiples of a power of the norm.

package matrix_norm

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// CompactPositiveHomogeneousBounds — a continuous function f(x, v) of a
// point x of a compact K and an n-vector v, homogeneous of a positive
// degree d in v and positive at every nonzero vector, lies between two
// positive multiples of ‖v‖ᵈ, uniformly over K. Twice the zero vector is
// the zero vector, so homogeneity at 2 makes f(x, 0) equal to 2ᵈ times
// itself, and 2ᵈ exceeds 1: f vanishes at the zero vector. On K times the
// unit sphere of ℝⁿ, a compact set, f attains a least and a greatest
// value, and positivity makes the least one positive. A nonzero v is ‖v‖
// times the unit vector v/‖v‖, so homogeneity makes f(x, v) the value at
// that unit vector times ‖v‖ᵈ, which lies between ‖v‖ᵈ times the two.
// When K is empty there is no point to bound at, and when n is 0 the only
// n-vector is the zero vector, where both sides vanish: any constants
// serve.
var CompactPositiveHomogeneousBounds = compactPositiveHomogeneousBoundsThm{family.Add(registry.ProofEntry{
	Name: "CompactPositiveHomogeneousBounds",
	Key:  "prop_60df12906a49a6b7",
	Reading: "Continuity is asked only on K × ℝⁿ, homogeneity only at points of K, n-vectors " +
		"and positive scalars. The degree must be positive: it is what makes f vanish at the " +
		"zero vector, and at degree 0, with n = 0 and K not empty, the zero function meets every " +
		"hypothesis while the estimate asks 0 < a ≤ f(x, vec_zero) = 0. For empty K or n = 0 " +
		"every pair of constants satisfies the estimate, and the conclusion still gives 0 < a ≤ b.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀K:set(A). ∀n d:num. ∀f:(A → (num → real) → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, K)",
			"0 < d",
			"continuous_map(«K × ℝⁿ», real_topology, λp:prod(A, num → real). f(fst(p), snd(p)))",
			"∀x:A. ∀t:real. ∀v:(num → real). x ∈ K ∧ vec⟨n⟩(v) ∧ &0 < t ⇒ f(x, t • v) = t ^ d * f(x, v)",
			"∀x:A. ∀v:(num → real). x ∈ K ∧ vec⟨n⟩(v) ∧ v ≠ vec_zero ⇒ &0 < f(x, v)",
		},
		Conclusion: "∃a b:real. " +
			"    &0 < a ∧ " +
			"    a ≤ b ∧ " +
			"    (∀x:A. ∀v:(num → real). " +
			"        x ∈ K ∧ vec⟨n⟩(v) ⇒ a * ‖v‖_n ^ d ≤ f(x, v) ∧ f(x, v) ≤ b * ‖v‖_n ^ d)",
		Abbrev: Abbrev{
			{Name: "K × ℝⁿ", Text: "product_topology(subtopology(T, K), euclidean_topology(n))"},
			{Name: "sphere", Text: "{u:num → real | vec⟨n⟩(u) ∧ ‖u‖_n = &1}"},
			{Name: "K × sphere", Text: "set_cross(K, «sphere»)"},
		},
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		K *Expr[Set[A]],
		n, d *Expr[Nat],
		f *Expr[Fun2[A, Fun[Nat, Real], Real]],
		topology, compactness, positiveDegree, continuity, homogeneous, positive Fact,
	) {
		zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
		vanishes := a.Have(
			"f vanishes at the zero vector",
			"∀x:A. x ∈ K ⇒ f(x, vec_zero) = &0",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inK := b.Assume()
				two := b.TermAs[Real]("&2")
				b.Show(
					"twice 0 is 0, so homogeneity at 2 gives f(x, 0) = 2ᵈ · f(x, 0), while 2ᵈ > 1ᵈ = 1 for positive d",
					ByArith(
						inK,
						positiveDegree,
						vec_space.VecZero.At(zero, n),
						vec_space.SmulZero.Read(real_ring.CommRing).At(two),
						homogeneous.At(x, two, b.VecAs[Real, DimN]("vec_zero")),
						real_pow.PowMonoBaseStrict.At(one, two, d)))
			}))
		zeroPower := a.Have(
			"the zero vector has norm 0, and 0 to the positive power d is 0",
			"‖vec_zero‖_n ^ d = &0",
			ByArith(positiveDegree, euclidean.NormVecZero.At(n), real_pow.ZeroPow.At(d)))
		a.Cases(a.TermAs[Bool]("K = ∅ ∨ n = 0"))
		a.When(
			"if K is empty or n is 0, the constants 1 and 1 serve: "+
				"a point of K forces n = 0, where the only n-vector is 0",
			func(b *Argument, degenerate Fact) {
				b.Take(one)
				b.Take(one)
				b.Do(SplitConj(
					Case(
						"1 is positive and at most itself",
						ByArith()),
					Case(
						"at a point x of K an n-vector v is 0, and both sides vanish",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							v := c.VecFixAs[Real, DimN]("v")
							parts := c.Conjuncts(
								c.Assume(),
								"x lies in K",
								"v is an n-vector")
							isZero := c.Have(
								"K holds x, so n = 0 and v is the zero vector",
								"v = vec_zero",
								By(degenerate, parts[0], parts[1], set_basic.NotInEmpty.At(x), vec_space.VecDimZero.At(zero, v)))
							c.Show(
								"so both sides are 0",
								ByArith(isZero, parts[0], vanishes.At(x), zeroPower))
						}))))
			})
		a.Otherwise(
			"otherwise f takes a positive least and a greatest value on K × sphere",
			func(b *Argument, nondegenerate Fact) {
				y, inK := b.ObtainAs[A](
					"K has a point y",
					"∃y:A. y ∈ K",
					By(nondegenerate, set_basic.MemberNotEmpty))
				positiveDimension := b.Have(
					"and the dimension n is positive",
					"0 < n",
					ByArith(nondegenerate))
				sphereCompact := b.Have(
					"the unit sphere of ℝⁿ is compact, ℝⁿ being ℝ^((n - 1) + 1) for positive n",
					"compact_in(euclidean_topology(n), «sphere»)",
					ByArith(
						positiveDimension,
						euclidean_topology.SphereCompact.At(b.TermAs[Nat]("n - 1")),
						euclidean_topology.EuclideanSphereDef.At(b.TermAs[Nat]("n - 1"))))
				origin := b.TermAs[Nat]("0")
				firstBasis := b.VecAs[Real, DimN]("basis_vector(0)")
				onSphere := b.Have(
					"the first basis vector lies on it, its index 0 being below the positive n",
					"vec⟨n⟩(basis_vector(0)) ∧ ‖basis_vector(0)‖_n = &1",
					By(
						positiveDimension,
						vec_space.VecBasisVector.At(zero, one, n, origin),
						euclidean.NormBasisVector.At(n, origin)))
				parameters := b.TermAs[Set[Set[A]]]("subtopology(T, K)")
				vectors := b.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)")
				space := b.TermAs[Set[Set[Prod[A, Fun[Nat, Real]]]]]("«K × ℝⁿ»")
				sphere := b.TermAs[Set[Fun[Nat, Real]]]("«sphere»")
				cylinder := b.TermAs[Set[Prod[A, Fun[Nat, Real]]]]("«K × sphere»")
				onPairs := b.TermAs[Fun[Prod[A, Fun[Nat, Real]], Real]]("λp:prod(A, num → real). f(fst(p), snd(p))")
				cylinderCompact := b.Have(
					"K × sphere is compact in K × ℝⁿ",
					"compact_in(«K × ℝⁿ», «K × sphere»)",
					By(
						compactness,
						sphereCompact,
						product_topology.CompactProduct.At(parameters, vectors, K, sphere),
						topological_space.SubtopologyTopology.Read(topology).At(K),
						euclidean_topology.EuclideanTopology.At(n),
						compact.CompactInOwnSubtopology.At(T, K)))
				cylinderInhabited := b.Have(
					"and holds the point (y, e₀)",
					"«K × sphere» ≠ ∅",
					By(
						inK,
						onSphere,
						set_product.InCross.At(K, sphere, y, firstBasis),
						set_basic.NotInEmpty.At(b.TermAs[Prod[A, Fun[Nat, Real]]]("(y, basis_vector(0))"))))
				p, least := b.ObtainAs[Prod[A, Fun[Nat, Real]]](
					"f takes a least value on the compact K × sphere, at some p",
					"∃p:prod(A, num → real). "+
						"    p ∈ «K × sphere» ∧ "+
						"    (∀w:prod(A, num → real). w ∈ «K × sphere» ⇒ f(fst(p), snd(p)) ≤ f(fst(w), snd(w)))",
					By(
						continuity,
						cylinderCompact,
						cylinderInhabited,
						real_valued.ContinuousCompactMinimum.At(space, onPairs, cylinder)))
				q, greatest := b.ObtainAs[Prod[A, Fun[Nat, Real]]](
					"and a greatest value, at some q",
					"∃q:prod(A, num → real). "+
						"    q ∈ «K × sphere» ∧ "+
						"    (∀w:prod(A, num → real). w ∈ «K × sphere» ⇒ f(fst(w), snd(w)) ≤ f(fst(q), snd(q)))",
					By(
						continuity,
						cylinderCompact,
						cylinderInhabited,
						real_valued.ContinuousCompactMaximum.At(space, onPairs, cylinder)))
				lowParts := b.Conjuncts(
					least,
					"p lies in K × sphere",
					"where f is least")
				highParts := b.Conjuncts(
					greatest,
					"q lies in K × sphere",
					"where f is greatest")
				components := b.Have(
					"p pairs a point of K with a unit n-vector",
					"fst(p) ∈ K ∧ vec⟨n⟩(snd(p)) ∧ ‖snd(p)‖_n = &1",
					By(lowParts[0], set_product.InCrossProjections.At(K, sphere, p)))
				point, direction := b.TermAs[A]("fst(p)"), b.VecAs[Real, DimN]("snd(p)")
				leastPositive := b.Have(
					"a unit vector is not 0, so f is positive there: the least value is positive",
					"&0 < f(fst(p), snd(p))",
					ByArith(components, positive.At(point, direction), euclidean.NormVecZero.At(n)))
				estimate := b.Have(
					"at a point of K, f at an n-vector v lies between "+
						"‖v‖ᵈ times the least value and ‖v‖ᵈ times the greatest",
					Statement{
						Binders:    "∀x:A. ∀v:(num → real).",
						Hypotheses: []string{"x ∈ K", "vec⟨n⟩(v)"},
						Conclusion: "f(fst(p), snd(p)) * ‖v‖_n ^ d ≤ f(x, v) ∧ f(x, v) ≤ f(fst(q), snd(q)) * ‖v‖_n ^ d",
					},
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						v := c.VecFixAs[Real, DimN]("v")
						parts := c.Conjuncts(
							c.Assume(),
							"x lies in K",
							"v is an n-vector")
						xInK, vIn := parts[0], parts[1]
						length := c.TermAs[Real]("‖v‖_n")
						c.Cases(c.TermAs[Bool]("‖v‖_n = &0"))
						c.When(
							"v of norm 0 is the zero vector, where both sides vanish",
							func(e *Argument, zeroNorm Fact) {
								e.Show(
									"f vanishes at the zero vector, and so does ‖v‖ᵈ",
									ByArith(zeroNorm, euclidean.NormEqZero.At(proof.Inhabit(v, vIn)), xInK, vanishes.At(x), zeroPower))
							})
						c.Otherwise(
							"otherwise v is ‖v‖ times the unit vector v/‖v‖, and homogeneity carries the extremes to v",
							func(e *Argument, nonzeroNorm Fact) {
								scale := e.TermAs[Real]("real_inv(‖v‖_n)")
								normalized := e.VecAs[Real, DimN]("real_inv(‖v‖_n) • v")
								positiveLength := e.Have(
									"a norm is never negative, so ‖v‖ is positive",
									"&0 < ‖v‖_n",
									ByArith(nonzeroNorm, euclidean.NormNonneg.At(v)))
								normalizedIn := e.Have(
									"v/‖v‖ is an n-vector",
									"vec⟨n⟩(real_inv(‖v‖_n) • v)",
									By(vec_space.VecSmul.Read(real_ring.CommRing).At(scale, proof.Inhabit(v, vIn))))
								onCylinder := e.Have(
									"of norm 1, so (x, v/‖v‖) is a point of K × sphere",
									"(x, real_inv(‖v‖_n) • v) ∈ «K × sphere»",
									By(
										xInK,
										normalizedIn,
										nonzeroNorm,
										euclidean.NormNormalize.At(v),
										set_product.InCross.At(K, sphere, x, normalized)))
								pair := e.TermAs[Prod[A, Fun[Nat, Real]]]("(x, real_inv(‖v‖_n) • v)")
								extremes := e.Have(
									"where f lies between its least and its greatest value",
									"f(fst(p), snd(p)) ≤ f(x, real_inv(‖v‖_n) • v) ∧ f(x, real_inv(‖v‖_n) • v) ≤ f(fst(q), snd(q))",
									By(
										onCylinder,
										lowParts[1].At(pair),
										highParts[1].At(pair),
										pairs.Fst.At(x, normalized),
										pairs.Snd.At(x, normalized)))
								inverse := e.Have(
									"‖v‖ is not 0, so it times its inverse is 1",
									"‖v‖_n * real_inv(‖v‖_n) = &1",
									ByArith(nonzeroNorm))
								rescaled := e.Have(
									"so ‖v‖ times v/‖v‖ is v",
									"‖v‖_n • (real_inv(‖v‖_n) • v) = v",
									Simp(Rev(vec_space.SmulMul.Read(real_ring.CommRing))),
									By(inverse, vec_space.SmulOne.Read(real_ring.CommRing)))
								scaled := e.Have(
									"and homogeneity at the positive ‖v‖ makes f(x, v) the value ‖v‖ᵈ · f(x, v/‖v‖)",
									"f(x, v) = ‖v‖_n ^ d * f(x, real_inv(‖v‖_n) • v)",
									By(xInK, normalizedIn, positiveLength, rescaled, homogeneous.At(x, length, normalized)))
								power := e.TermAs[Real]("‖v‖_n ^ d")
								value := e.TermAs[Real]("f(x, real_inv(‖v‖_n) • v)")
								smallest, largest := e.TermAs[Real]("f(fst(p), snd(p))"), e.TermAs[Real]("f(fst(q), snd(q))")
								e.Show(
									"multiplying the extremes by the positive ‖v‖ᵈ gives the two bounds",
									ByArith(
										extremes,
										scaled,
										positiveLength,
										real_pow.PowPos.At(length, d),
										real_order_ring.LessEqMulLeft.At(power, smallest, value),
										real_order_ring.LessEqMulLeft.At(power, value, largest)))
							})
					}))
				b.Take(b.TermAs[Real]("f(fst(p), snd(p))"))
				b.Take(b.TermAs[Real]("f(fst(q), snd(q))"))
				b.Show(
					"so the least value of f and the greatest are the constants",
					By(leastPositive, highParts[0], lowParts[1].At(q), estimate))
			})
	}),
})}

// MatrixActCoordinateContinuous — a coordinate of a matrix family's
// action is continuous where the entries of its row are: when each entry
// G(x, i, j) of row i, j < n, is continuous on K, the i-th coordinate of
// G(x)v is a continuous function of (x, v) on K × ℝⁿ. That coordinate is
// the sum over j < n of G(x, i, j)·v(j), each term the product of an
// entry read through the first projection and a coordinate of v read
// through the second, and a finite sum of continuous real functions is
// continuous.
var MatrixActCoordinateContinuous = matrixActCoordinateContinuousThm{family.Add(registry.ProofEntry{
	Name: "MatrixActCoordinateContinuous",
	Key:  "prop_f5c69d20926e8eeb",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀K:set(A). ∀n i:num. ∀G:(A → num → num → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"∀j:num. j < n ⇒ continuous_map(subtopology(T, K), real_topology, λx:A. G(x, i, j))",
		},
		Conclusion: "continuous_map(«K × ℝⁿ», " +
			"    real_topology, " +
			"    λp:prod(A, num → real). matrix_act⟨n⟩(G(fst(p)), snd(p), i))",
		Abbrev: Abbrev{
			{Name: "K × ℝⁿ", Text: "product_topology(subtopology(T, K), euclidean_topology(n))"},
		},
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		K *Expr[Set[A]],
		n, i *Expr[Nat],
		G *Expr[Fun3[A, Nat, Nat, Real]],
		topology, row Fact,
	) {
		parameters := a.TermAs[Set[Set[A]]]("subtopology(T, K)")
		vectors := a.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)")
		space := a.TermAs[Set[Set[Prod[A, Fun[Nat, Real]]]]]("«K × ℝⁿ»")
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		productTopology := a.Have(
			"K × ℝⁿ is a topological space",
			"is_topology(«K × ℝⁿ»)",
			By(
				product_topology.ProductTopology.At(parameters, vectors),
				topological_space.SubtopologyTopology.Read(topology).At(K),
				euclidean_topology.EuclideanTopology.At(n)))
		first := a.Have(
			"the first projection is continuous from K × ℝⁿ onto K",
			"continuous_map(«K × ℝⁿ», subtopology(T, K), fst)",
			Cite(product_topology.FstContinuous))
		second := a.Have(
			"and the second onto ℝⁿ",
			"continuous_map(«K × ℝⁿ», euclidean_topology(n), snd)",
			Cite(product_topology.SndContinuous))
		terms := a.Have(
			"each term G(x, i, j)·v(j) of its sum is continuous",
			Statement{
				Binders:    "∀j:num.",
				Hypotheses: []string{"j < n"},
				Conclusion: "continuous_map(«K × ℝⁿ», " +
					"    real_topology, " +
					"    λp:prod(A, num → real). G(fst(p), i, j) * snd(p)(j))",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				column := b.Assume()
				entry := b.Have(
					"the entry G(x, i, j), read through the first projection",
					"continuous_map(«K × ℝⁿ», real_topology, λp:prod(A, num → real). G(fst(p), i, j))",
					By(
						column,
						row.At(j),
						continuous.Compose.Read(first).At(line, b.TermAs[Fun[A, Real]]("λx:A. G(x, i, j)")),
						functions.ComposeApply))
				coordinate := b.Have(
					"the coordinate v(j), read through the second",
					"continuous_map(«K × ℝⁿ», real_topology, λp:prod(A, num → real). snd(p)(j))",
					By(
						column,
						euclidean_topology.CoordinateContinuous.At(n, j),
						continuous.Compose.Read(second).At(
							line, b.TermAs[Fun[Fun[Nat, Real], Real]]("λu:(num → real). u(j)")),
						functions.ComposeApply))
				b.Show(
					"and so is their product",
					By(productTopology, entry, coordinate, real_valued.ContinuousRealMul))
			}))
		a.Show(
			"the i-th coordinate is the sum over j < n of those terms",
			Simp(Fwd(matrix.MatrixActDef), Fwd(euclidean.DotIsSum)),
			By(
				productTopology,
				terms,
				real_valued.ContinuousRealSum.At(
					space,
					a.TermAs[Fun2[Nat, Prod[A, Fun[Nat, Real]], Real]](
						"λj:num. λp:prod(A, num → real). G(fst(p), i, j) * snd(p)(j)"),
					n)))
	}),
})}

// MatrixActContinuous — a family of m × n matrices whose entries are
// continuous on K acts continuously: (x, v) ↦ G(x)v is a continuous map
// from K × ℝⁿ into ℝᵐ. Each coordinate of the action is continuous by
// MatrixActCoordinateContinuous above, the matrices put the image in ℝᵐ,
// and a map into ℝᵐ whose coordinates are continuous is continuous.
var MatrixActContinuous = matrixActContinuousThm{family.Add(registry.ProofEntry{
	Name: "MatrixActContinuous",
	Key:  "prop_9a8dc3dce1dc7db8",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀K:set(A). ∀n m:num. ∀G:(A → num → num → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"∀i j:num. i < m ∧ j < n ⇒ continuous_map(subtopology(T, K), real_topology, λx:A. G(x, i, j))",
			"∀x:A. x ∈ K ⇒ matrix⟨m, n⟩(G(x))",
		},
		Conclusion: "continuous_map(«K × ℝⁿ», " +
			"    euclidean_topology(m), " +
			"    λp:prod(A, num → real). matrix_act⟨n⟩(G(fst(p)), snd(p)))",
		Abbrev: Abbrev{
			{Name: "K × ℝⁿ", Text: "product_topology(subtopology(T, K), euclidean_topology(n))"},
		},
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		K *Expr[Set[A]],
		n, m *Expr[Nat],
		G *Expr[Fun3[A, Nat, Nat, Real]],
		topology, entries, matrices Fact,
	) {
		parameters := a.TermAs[Set[Set[A]]]("subtopology(T, K)")
		vectors := a.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)")
		productTopology := a.Have(
			"K × ℝⁿ is a topological space",
			"is_topology(«K × ℝⁿ»)",
			By(
				product_topology.ProductTopology.At(parameters, vectors),
				topological_space.SubtopologyTopology.Read(topology).At(K),
				euclidean_topology.EuclideanTopology.At(n)))
		intoVectors := a.Have(
			"at a point of K × ℝⁿ the matrix acts into ℝᵐ",
			"∀p:prod(A, num → real). p ∈ ⋃«K × ℝⁿ» ⇒ vec⟨m⟩(matrix_act⟨n⟩(G(fst(p)), snd(p)))",
			Derive(func(b *Argument) {
				p := b.FixAs[Prod[A, Fun[Nat, Real]]]("p")
				point := b.Assume()
				head := b.TermAs[A]("fst(p)")
				inK := b.Have(
					"its first coordinate lies in K",
					"fst(p) ∈ K",
					By(
						point,
						product_topology.ProductSpace.At(parameters, vectors),
						topological_space.SubtopologySpace.At(T, K),
						set_product.InCrossProjections.At(
							b.TermAs[Set[A]]("⋃T ∩ K"),
							b.TermAs[Set[Fun[Nat, Real]]]("⋃euclidean_topology(n)"),
							p),
						set_basic.InInter.At(b.TermAs[Set[A]]("⋃T"), K, head)))
				b.Show(
					"where G is an m × n matrix",
					By(inK, matrices.At(head), matrix.MatrixActVec.Read(real_ring.CommRing)))
			}))
		coordinates := a.Have(
			"each coordinate of the image is continuous on K × ℝⁿ",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i < m"},
				Conclusion: "continuous_map(«K × ℝⁿ», " +
					"    real_topology, " +
					"    λp:prod(A, num → real). matrix_act⟨n⟩(G(fst(p)), snd(p), i))",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				row := b.Assume()
				b.Show(
					"the entries of row i are continuous on K, i being below m",
					By(topology, row, entries, MatrixActCoordinateContinuous.At(T, K, n, i, G)))
			}))
		a.Show(
			"a map into ℝᵐ whose coordinates are continuous is continuous",
			By(productTopology, intoVectors, coordinates, euclidean_topology.ContinuousIffCoordinates))
	}),
})}

// CompactPositiveQuadraticBounds — a continuous family of positive
// quadratic forms over a compact K is bounded below by one positive
// constant times ‖v‖² and above by another, uniformly over K. The form
// ⟪v, G(x)v⟫ is continuous on K × ℝⁿ, each coordinate of v and of G(x)v
// being continuous there; it scales by t² when v is scaled by t and is
// positive at every nonzero vector, so CompactPositiveHomogeneousBounds
// above applies to it at degree 2.
var CompactPositiveQuadraticBounds = compactPositiveQuadraticBoundsThm{family.Add(registry.ProofEntry{
	Name: "CompactPositiveQuadraticBounds",
	Key:  "prop_36c493edbe02c990",
	Reading: "Continuity is required only on K. Positivity of the quadratic form suffices; no " +
		"symmetry is assumed, and only the entries G(x, i, j) with i, j < n are read. For empty K or n " +
		"= 0 every pair of constants satisfies the estimate, and the conclusion still gives 0 < a ≤ b.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀K:set(A). ∀n:num. ∀G:(A → num → num → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, K)",
			"∀i j:num. i < n ∧ j < n ⇒ continuous_map(subtopology(T, K), real_topology, λx:A. G(x, i, j))",
			"∀x:A. ∀v:(num → real). x ∈ K ∧ vec⟨n⟩(v) ∧ v ≠ vec_zero ⇒ &0 < ⟪v, matrix_act⟨n⟩(G(x), v)⟫_n",
		},
		Conclusion: "∃a b:real. " +
			"    &0 < a ∧ " +
			"    a ≤ b ∧ " +
			"    (∀x:A. ∀v:(num → real). " +
			"        x ∈ K ∧ vec⟨n⟩(v) ⇒ " +
			"        a * ‖v‖_n ^ 2 ≤ ⟪v, matrix_act⟨n⟩(G(x), v)⟫_n ∧ " +
			"        ⟪v, matrix_act⟨n⟩(G(x), v)⟫_n ≤ b * ‖v‖_n ^ 2)",
		Abbrev: Abbrev{
			{Name: "K × ℝⁿ", Text: "product_topology(subtopology(T, K), euclidean_topology(n))"},
		},
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		K *Expr[Set[A]],
		n *Expr[Nat],
		G *Expr[Fun3[A, Nat, Nat, Real]],
		topology, compactness, entries, positive Fact,
	) {
		continuity := a.Have(
			"the form (x, v) ↦ ⟪v, G(x)v⟫ is continuous on K × ℝⁿ",
			"continuous_map(«K × ℝⁿ», "+
				"    real_topology, "+
				"    λp:prod(A, num → real). ⟪snd(p), matrix_act⟨n⟩(G(fst(p)), snd(p))⟫_n)",
			Derive(func(b *Argument) {
				parameters := b.TermAs[Set[Set[A]]]("subtopology(T, K)")
				vectors := b.TermAs[Set[Set[Fun[Nat, Real]]]]("euclidean_topology(n)")
				space := b.TermAs[Set[Set[Prod[A, Fun[Nat, Real]]]]]("«K × ℝⁿ»")
				productTopology := b.Have(
					"K × ℝⁿ is a topological space",
					"is_topology(«K × ℝⁿ»)",
					By(
						product_topology.ProductTopology.At(parameters, vectors),
						topological_space.SubtopologyTopology.Read(topology).At(K),
						euclidean_topology.EuclideanTopology.At(n)))
				imageCoordinates := b.Have(
					"each coordinate of G(x)v is continuous on K × ℝⁿ",
					Statement{
						Binders:    "∀i:num.",
						Hypotheses: []string{"i < n"},
						Conclusion: "continuous_map(«K × ℝⁿ», " +
							"    real_topology, " +
							"    λp:prod(A, num → real). matrix_act⟨n⟩(G(fst(p)), snd(p), i))",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						row := c.Assume()
						c.Show(
							"the entries of row i are continuous on K, i being below n",
							By(topology, row, entries, MatrixActCoordinateContinuous.At(T, K, n, i, G)))
					}))
				vectorCoordinates := b.Have(
					"and each coordinate of v, the second projection being continuous into ℝⁿ",
					"∀i:num. i < n ⇒ continuous_map(«K × ℝⁿ», real_topology, λp:prod(A, num → real). snd(p)(i))",
					By(
						productTopology,
						product_topology.SndContinuous.At(parameters, vectors),
						euclidean_topology.ContinuousIffCoordinates.At(
							n, space, b.TermAs[Fun[Prod[A, Fun[Nat, Real]], Fun[Nat, Real]]]("snd"))))
				terms := b.Have(
					"so each term v(i)·(G(x)v)(i) of the dot product is continuous",
					Statement{
						Binders:    "∀i:num.",
						Hypotheses: []string{"i < n"},
						Conclusion: "continuous_map(«K × ℝⁿ», " +
							"    real_topology, " +
							"    λp:prod(A, num → real). snd(p)(i) * matrix_act⟨n⟩(G(fst(p)), snd(p), i))",
					},
					By(productTopology, vectorCoordinates, imageCoordinates, real_valued.ContinuousRealMul))
				b.Show(
					"and ⟪v, G(x)v⟫ is the sum over i < n of those terms",
					Simp(Fwd(euclidean.DotIsSum)),
					By(
						productTopology,
						terms,
						real_valued.ContinuousRealSum.At(
							space,
							b.TermAs[Fun2[Nat, Prod[A, Fun[Nat, Real]], Real]](
								"λi:num. λp:prod(A, num → real). snd(p)(i) * matrix_act⟨n⟩(G(fst(p)), snd(p), i)"),
							n)))
			}))
		homogeneous := a.Have(
			"the form is quadratic: scaling v by t scales ⟪v, G(x)v⟫ by t²",
			"∀x:A. ∀t:real. ∀v:(num → real). "+
				"    ⟪t • v, matrix_act⟨n⟩(G(x), t • v)⟫_n = t ^ 2 * ⟪v, matrix_act⟨n⟩(G(x), v)⟫_n",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.FixAs[Real]("t")
				b.FixAs[Fun[Nat, Real]]("v")
				pulled := b.Have(
					"G(x) is linear, so it carries the scaling to the image",
					"matrix_act⟨n⟩(G(x), t • v) = t • matrix_act⟨n⟩(G(x), v)",
					By(
						matrix.MatrixActLinear.Read(real_ring.CommRing).At(n, b.TermAs[Fun2[Nat, Nat, Real]]("G(x)")),
						vec_space.VecLinearDef))
				b.Show(
					"and the dot product takes a scalar out of either argument",
					Simp(
						Fwd(pulled),
						Fwd(dot.SmulLeft.Read(real_ring.CommRing)),
						Fwd(dot.SmulRight.Read(real_ring.CommRing))),
					ByArith())
			}))
		a.Show(
			"a continuous form, quadratic and positive at every nonzero "+
				"vector, is compared with ‖v‖² by two positive constants",
			By(
				topology,
				compactness,
				continuity,
				homogeneous,
				positive,
				CompactPositiveHomogeneousBounds.At(
					T,
					K,
					n,
					a.TermAs[Nat]("2"),
					a.TermAs[Fun2[A, Fun[Nat, Real], Real]]("λx:A. λv:(num → real). ⟪v, matrix_act⟨n⟩(G(x), v)⟫_n"))))
	}),
})}

// CompactInjectiveMatrixBounds — a continuous family of injective m × n
// matrices over a compact K stretches every vector by at least one
// positive constant and at most another, uniformly over K. The size
// ‖G(x)v‖ is continuous on K × ℝⁿ, the action being continuous into ℝᵐ;
// G(x) is linear, so the size scales by t when v is scaled by a positive
// t; an injective G(x) sends no nonzero vector to 0, so the size is
// positive there. CompactPositiveHomogeneousBounds above then applies to
// it at degree 1.
var CompactInjectiveMatrixBounds = compactInjectiveMatrixBoundsThm{family.Add(registry.ProofEntry{
	Name: "CompactInjectiveMatrixBounds",
	Key:  "prop_215eb7c1a597eec3",
	Reading: "The parameter space is arbitrary and the matrices may be " +
		"rectangular. Injectivity is imposed separately at each parameter; compactness " +
		"upgrades it to one positive lower bound. For empty K or n = 0 every pair of " +
		"constants satisfies the estimate, and the conclusion still gives 0 < a ≤ b.",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀K:set(A). ∀n m:num. ∀G:(A → num → num → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"compact_in(T, K)",
			"∀i j:num. i < m ∧ j < n ⇒ continuous_map(subtopology(T, K), real_topology, λx:A. G(x, i, j))",
			"∀x:A. x ∈ K ⇒ matrix⟨m, n⟩(G(x))",
			"∀x:A. ∀v:(num → real). x ∈ K ∧ vec⟨n⟩(v) ∧ matrix_act⟨n⟩(G(x), v) = vec_zero ⇒ v = vec_zero",
		},
		Conclusion: "∃a b:real. " +
			"    &0 < a ∧ " +
			"    a ≤ b ∧ " +
			"    (∀x:A. ∀v:(num → real). " +
			"        x ∈ K ∧ vec⟨n⟩(v) ⇒ " +
			"        a * ‖v‖_n ≤ ‖matrix_act⟨n⟩(G(x), v)‖_m ∧ ‖matrix_act⟨n⟩(G(x), v)‖_m ≤ b * ‖v‖_n)",
		Abbrev: Abbrev{
			{Name: "K × ℝⁿ", Text: "product_topology(subtopology(T, K), euclidean_topology(n))"},
		},
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		K *Expr[Set[A]],
		n, m *Expr[Nat],
		G *Expr[Fun3[A, Nat, Nat, Real]],
		topology, compactness, entries, matrices, injective Fact,
	) {
		action := a.Have(
			"(x, v) ↦ G(x)v is continuous from K × ℝⁿ into ℝᵐ",
			"continuous_map(«K × ℝⁿ», "+
				"    euclidean_topology(m), "+
				"    λp:prod(A, num → real). matrix_act⟨n⟩(G(fst(p)), snd(p)))",
			By(topology, entries, matrices, MatrixActContinuous.At(T, K, n, m, G)))
		continuity := a.Have(
			"so is its size (x, v) ↦ ‖G(x)v‖, the norm being continuous on ℝᵐ",
			"continuous_map(«K × ℝⁿ», "+
				"    real_topology, "+
				"    λp:prod(A, num → real). ‖matrix_act⟨n⟩(G(fst(p)), snd(p))‖_m)",
			By(
				euclidean_topology.NormContinuous.At(m),
				continuous.Compose.Read(action).At(
					a.TermAs[Set[Set[Real]]]("real_topology"),
					a.TermAs[Fun[Fun[Nat, Real], Real]]("λw:(num → real). ‖w‖_m")),
				functions.ComposeApply))
		homogeneous := a.Have(
			"G(x) is linear, so scaling v by a positive t scales ‖G(x)v‖ by t",
			Statement{
				Binders:    "∀x:A. ∀t:real. ∀v:(num → real).",
				Hypotheses: []string{"&0 < t"},
				Conclusion: "‖matrix_act⟨n⟩(G(x), t • v)‖_m = t * ‖matrix_act⟨n⟩(G(x), v)‖_m",
			},
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				t := b.FixAs[Real]("t")
				b.FixAs[Fun[Nat, Real]]("v")
				positiveScale := b.Assume()
				pulled := b.Have(
					"G(x) carries the scaling to the image",
					"matrix_act⟨n⟩(G(x), t • v) = t • matrix_act⟨n⟩(G(x), v)",
					By(
						matrix.MatrixActLinear.Read(real_ring.CommRing).At(n, b.TermAs[Fun2[Nat, Nat, Real]]("G(x)")),
						vec_space.VecLinearDef))
				b.Show(
					"and the norm takes the scalar out as its size |t|, which is t",
					ByArith(
						positiveScale,
						pulled,
						euclidean.NormSmul.At(t, b.VecAs[Real, DimM]("matrix_act⟨n⟩(G(x), v)")),
						real_sgn_abs.AbsFixedIffNonneg.At(t)))
			}))
		positive := a.Have(
			"an injective G(x) sends a nonzero n-vector to a nonzero m-vector, whose norm is positive",
			"∀x:A. ∀v:(num → real). x ∈ K ∧ vec⟨n⟩(v) ∧ v ≠ vec_zero ⇒ &0 < ‖matrix_act⟨n⟩(G(x), v)‖_m",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				v := b.VecFixAs[Real, DimN]("v")
				parts := b.Conjuncts(
					b.Assume(),
					"x lies in K",
					"v is an n-vector",
					"v is not 0")
				inRm := b.Have(
					"the image is an m-vector, G(x) being an m × n matrix",
					"vec⟨m⟩(matrix_act⟨n⟩(G(x), v))",
					By(parts[0], matrices.At(x), matrix.MatrixActVec.Read(real_ring.CommRing)))
				image := proof.Inhabit(b.VecAs[Real, DimM]("matrix_act⟨n⟩(G(x), v)"), inRm)
				b.Show(
					"and it is not 0, G(x) being injective, so its norm is positive",
					ByArith(
						parts[0],
						parts[1],
						parts[2],
						injective.At(x, v),
						euclidean.NormEqZero.At(image),
						euclidean.NormNonneg.At(image.Vec)))
			}))
		// At degree 1 the powers t¹ and ‖v‖¹ of the comparison are t and ‖v‖.
		bounds := a.Simplified(
			CompactPositiveHomogeneousBounds.At(
				T,
				K,
				n,
				a.TermAs[Nat]("1"),
				a.TermAs[Fun2[A, Fun[Nat, Real], Real]]("λx:A. λv:(num → real). ‖matrix_act⟨n⟩(G(x), v)‖_m")),
			Fwd(real_pow.PowOne))
		a.Show(
			"a continuous size, homogeneous of degree 1 and positive at every "+
				"nonzero vector, is compared with ‖v‖ by two positive constants",
			By(topology, compactness, continuity, homogeneous, positive, bounds))
	}),
})}
