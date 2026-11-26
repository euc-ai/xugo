// bounded.go — a map linear in each of its arguments is bounded on
// finite-dimensional subspaces.
//
// A vector is a sequence and the dimension is carried by the membership
// predicate rather than by the type, so "finite-dimensional" is a
// hypothesis on the ARGUMENT: `vec⟨m⟩(x)` says x vanishes from index m
// on, and eᵢ below is the i-th standard basis vector of that range.
// Nothing is asked of the image: the target norm reads its first n
// coordinates and says nothing about the rest.
//
// Each bound is stated as a FORMULA in the map and the dimensions —
// Σᵢ ‖f(eᵢ)‖ for one argument, Σⱼ Σᵢ ‖h(eᵢ, eⱼ)‖ for two — and the
// familiar existential form is one cite of it away, so it is no member.
// The order is forced by the two-argument case: its estimate sums the
// one-argument estimate over the second dimension, and a bound that
// exists only behind an ∃ supplies no term to put under the Σ. An
// explicit bound applies twice; an existential one does not apply at
// all. The one-argument estimate is also what makes the operator norm
// (opnorm.go) a supremum of a bounded set. The README walks the argument;
// each member's comment says what its labels cannot.

package euclidean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// LinearBasisEstimate — the total size of the images of a dimension's
// basis vectors bounds a linear map on that dimension: no m-vector x is
// stretched by more than that factor, ‖f(x)‖ ≤ (Σᵢ ‖f(eᵢ)‖)·‖x‖.
//
// Uniformity is the content: the bound names no argument, so one
// estimate serves every x of the dimension at once. It is bought along
// the basis expansion of x, where the one step that could have cost it
// — bounding a coordinate by the norm — holds on the active range, which
// is exactly where the expansion lives.
var LinearBasisEstimate = linearBasisEstimateThm{family.Add(registry.ProofEntry{
	Name: "LinearBasisEstimate",
	Key:  "prop_849ca2dc7ebd42f1",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num. ∀f:((num → real) → num → real). ∀x:(num → real).",
			Hypotheses: []string{
				"vec_linear(f)",
				"vec⟨m⟩(x)",
			},
			Conclusion: "‖f(x)‖_n ≤ «basisImageTotal» * ‖x‖_m",
			Abbrev: Abbrev{
				{Name: "argumentRange", Text: "{i:num | i < m}"},
				{Name: "expansionTerm", Text: "x(i) • basis_vector(i)"},
				{Name: "basisImageNorm", Text: "‖f(basis_vector(i))‖_n"},
				{Name: "basisImageTotal", Text: "Σ_{i<m} ‖f(basis_vector(i))‖_n"},
			},
		},
		func(
			a *Argument,
			m, n *Expr[Nat],
			f *VecFun[Real, DimM, DimN],
			x *Vec[Real, DimM],
			linear, member Fact,
		) {
			// The argument carries its membership: the evidence travels
			// with every cite at it.
			xM := proof.Inhabit(x, member)

			// The sums the argument runs through, each read once as the Σ
			// its claim shows; their ranges and summands are what the
			// laws take.
			expansionSum := a.BigOpAs[Nat, Fun[Nat, Real]]("Σ_{i<m} x(i) • basis_vector(i)")
			imageSum := a.BigOpAs[Nat, Fun[Nat, Real]]("Σ_{i<m} f(x(i) • basis_vector(i))")
			imageNormSum := a.BigOpAs[Nat, Real]("Σ_{i<m} ‖f(x(i) • basis_vector(i))‖_n")
			pricedSum := a.BigOpAs[Nat, Real]("Σ_{i<m} ‖f(basis_vector(i))‖_n * ‖x‖_m")
			bound := a.BigOpAs[Nat, Real]("«basisImageTotal»")
			argumentNorm := a.TermAs[Real]("‖x‖_m")

			finite := a.Have(
				"the active range is finite",
				"finite(«argumentRange»)",
				By(At(num_segment.FiniteBelowStrict, m)))
			expansion := a.Have(
				"x is its own basis expansion",
				"x = Σ_{i<m} x(i) • basis_vector(i)",
				By(vec_space.BasisExpansion.Read(real_ring.CommRing).At(xM)))
			image := a.Have(
				"so f(x) is the fold of the images of the expansion's terms",
				"f(x) = Σ_{i<m} f(x(i) • basis_vector(i))",
				By(
					At(
						vec_space.LinearIterate.Read(real_ring.CommRing), f, expansionSum.Range(), expansionSum.Summand()),
					expansion,
					finite,
					linear))

			// Each term of the expansion is a multiple of a basis vector, so
			// homogeneity prices its image by the size of the coordinate, and
			// the coordinate is within ‖x‖ because its index is active.
			perIndex := a.Have(
				"each term's image is within ‖f(eᵢ)‖·‖x‖",
				"∀i:num. i ∈ «argumentRange» ⇒ ‖f(x(i) • basis_vector(i))‖_n ≤ ‖f(basis_vector(i))‖_n * ‖x‖_m",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					indexed := b.Assume()

					coordinate := b.TermAs[Real]("x(i)")
					coordinateSize := b.Term("|x(i)|")
					basisImage := b.VecAs[Real, DimN]("f(basis_vector(i))")
					imageNorm := b.Term("«basisImageNorm»")

					homogeneous := b.Have(
						"f pulls the coordinate out of the term",
						"f(«expansionTerm») = x(i) • f(basis_vector(i))",
						By(linear, vec_space.VecLinearDef))
					active := b.Have(
						"the index is inside the active range",
						"i < m",
						BySets(indexed))
					within := b.Have(
						"so the coordinate is no larger in size than ‖x‖",
						"|x(i)| ≤ ‖x‖_m",
						By(ComponentLeNorm.At(i, xM.Vec), active))
					b.Show(
						"and ‖f(eᵢ)‖ is nonnegative, so it carries that bound through "+
							"the product, the product turned round to put ‖f(eᵢ)‖ first",
						By(
							homogeneous,
							within,
							NormSmul.At(coordinate, basisImage),
							NormNonneg.At(basisImage),
							At(real_order_ring.LessEqMulLeft, imageNorm, coordinateSize, argumentNorm),
							At(real_construction.MulSym, coordinateSize, imageNorm)))
				}))

			a.Show(
				"so ‖f(x)‖ is within the total size of the basis images, times ‖x‖",
				real_order_ring.OrderCalc(a.Ctx()).CalcLeibniz(a.Term("‖f(x)‖_n"),
					LeLeg(
						imageNormSum,
						"the fold's norm is within the sum of the norms of its terms",
						By(NormIterateLe.At(n, imageSum.Range(), imageSum.Summand()), finite, image)),
					LeLeg(
						pricedSum,
						"and each of those is at most its basis image's norm times ‖x‖",
						By(
							finite,
							perIndex,
							real_sum.Monotone.At(imageNormSum.Range(), imageNormSum.Summand(), pricedSum.Summand()))),
					EqLeg(
						a.Term("«basisImageTotal» * ‖x‖_m"),
						"where the common factor ‖x‖ comes back out of the sum",
						By(real_sum.ScalarRight.At(argumentNorm, bound.Summand(), bound.Range())))))
		}),
})}

// BilinearBasisBound — the total size of the images of the two
// dimensions' basis pairs bounds a bilinear map on those dimensions,
// uniformly in both arguments.
//
// The linear estimate (LinearBasisEstimate) applies twice, and the two
// applications are not alike: the first is at h(x, ·), one map, and
// prices h(x, y) by the images of the second dimension's basis vectors;
// the second is at h(·, eⱼ), a DIFFERENT map for each j, and prices each
// of those images in turn. What joins them is that the first bound is a sum over j of
// exactly the quantities the second bounds, so the second can be summed
// into it — which an explicit bound allows and an existential one
// cannot.
var BilinearBasisBound = bilinearBasisBoundThm{family.Add(registry.ProofEntry{
	Name: "BilinearBasisBound",
	Key:  "prop_a0a6a2b8fa1e1ea4",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n k:num. ∀h:((num → real) → (num → real) → num → real). ∀x y:(num → real).",
			Hypotheses: []string{
				"vec_bilinear(h)",
				"vec⟨m⟩(x)",
				"vec⟨n⟩(y)",
			},
			Conclusion: "‖h(x, y)‖_k ≤ «pairImageTotal» * ‖x‖_m * ‖y‖_n",
			Abbrev: Abbrev{
				{Name: "secondArgumentRange", Text: "{j:num | j < n}"},
				{Name: "pairImageTotal", Text: "Σ_{j<n} Σ_{i<m} ‖h(basis_vector(i), basis_vector(j))‖_k"},
			},
		},
		func(a *Argument, m, n, k *Expr[Nat], h *Expr[Fun3[Fun[Nat, Real], Fun[Nat, Real], Nat, Real]],
			x *Vec[Real, DimM], y *Vec[Real, DimN], bilinear, memberX, memberY Fact) {
			// The estimate below is uniform in the index: the range
			// condition is what the sum step needs of it, not what its
			// proof uses.
			perIndex := a.Have(
				"each image of a basis vector of the second dimension under "+
					"h(x, ·) is within the basis pairs' total size, times ‖x‖",
				Statement{
					Binders: "∀j:num.",
					Hypotheses: []string{
						"j ∈ «secondArgumentRange»",
					},
					Conclusion: "‖h(x, basis_vector(j))‖_k ≤ (Σ_{i<m} ‖h(basis_vector(i), basis_vector(j))‖_k) * ‖x‖_m",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("j")
					fixedSecond := b.Have(
						"fixing the second argument at eⱼ leaves a map linear in the first",
						"vec_linear(λu:(num → real). h(u, basis_vector(j)))",
						By(bilinear, vec_space.VecBilinearDef))
					first := b.VecFunAs[Real, DimM, DimK]("λu:(num → real). h(u, basis_vector(j))")
					b.Show(
						"to which the linear estimate applies at x, whatever the index",
						By(fixedSecond, LinearBasisEstimate.At(k, first, proof.Inhabit(x, memberX))))
				}))

			// The two sums the estimate joins, each read once as the Σ its
			// claim shows.
			fixedImageSum := a.BigOpAs[Nat, Real]("Σ_{j<n} ‖h(x, basis_vector(j))‖_k")
			pricedPairSum := a.BigOpAs[Nat, Real](
				"Σ_{j<n} (Σ_{i<m} ‖h(basis_vector(i), basis_vector(j))‖_k) * ‖x‖_m")
			pairSum := a.BigOpAs[Nat, Real]("«pairImageTotal»")
			firstArgumentNorm := a.TermAs[Real]("‖x‖_m")
			secondArgumentNorm := a.Term("‖y‖_n")
			scaledBound := a.Term("«pairImageTotal» * ‖x‖_m")

			sumEstimate := a.Have(
				"summing over the second dimension, with the common factor ‖x‖ coming back out of the sum",
				"Σ_{j<n} ‖h(x, basis_vector(j))‖_k ≤ «pairImageTotal» * ‖x‖_m",
				By(
					perIndex,
					real_sum.Monotone.At(fixedImageSum.Range(), fixedImageSum.Summand(), pricedPairSum.Summand()),
					At(num_segment.FiniteBelowStrict, n),
					real_sum.ScalarRight.At(firstArgumentNorm, pairSum.Summand(), pairSum.Range())))

			fixedFirst := a.Have(
				"fixing the first argument at x leaves a map linear in the second",
				"vec_linear(λv:(num → real). h(x, v))",
				By(bilinear, vec_space.VecBilinearDef))
			second := a.VecFunAs[Real, DimN, DimK]("λv:(num → real). h(x, v)")

			a.Show(
				"so ‖h(x, y)‖ is within the total size of the basis pairs' images, times ‖x‖ and ‖y‖",
				real_order_ring.OrderCalc(a.Ctx()).CalcLeibniz(a.Term("‖h(x, y)‖_k"),
					LeLeg(
						a.Term("(Σ_{j<n} ‖h(x, basis_vector(j))‖_k) * ‖y‖_n"),
						"h(x, ·) is linear, so the linear estimate prices h(x, "+
							"y) by the images of the second dimension's basis vectors",
						By(fixedFirst, LinearBasisEstimate.At(k, second, proof.Inhabit(y, memberY)))),
					LeLeg(
						a.Term("«pairImageTotal» * ‖x‖_m * ‖y‖_n"),
						"and ‖y‖ is nonnegative, so it carries the sum estimate through the product",
						By(
							sumEstimate,
							NormNonneg.At(y),
							At(real_order_ring.LessEqMulRight, fixedImageSum, scaledBound, secondArgumentNorm)))))
		}),
})}
