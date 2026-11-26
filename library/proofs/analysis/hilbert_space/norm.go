package hilbert_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/registry"
)

// NormMetric — taking the norm of a difference gives a metric on the
// carrier of a complex normed space.
var NormMetric = normMetricThm{family.Add(registry.ProofEntry{
	Name: "NormMetric",
	Key:  "prop_51b6092f115783d5",
	Build: family.Theorem(
		NormedSpace.Statement("metric_space(M.carrier, norm_distance(M, v))"),
		func(a *Argument, M *Expr[ModuleOps[Complex, A]], v *Arrow[A, Real], norm NormedSpaceFact[on.M]) {
			laws := a.Conjuncts(
				a.Unfolded(norm, NormedSpace),
				"the underlying complex module",
				"nonnegativity and definiteness",
				"the norm triangle inequality",
				"absolute homogeneity")
			moduleOn, definite, triangle, homogeneous := laws[0], laws[1], laws[2], laws[3]
			additive := module.AddGroupOn.Read(moduleOn)
			inverseIn := group.InvIn.Read(additive)

			differenceIn := a.Have(
				"the carrier contains the difference of any two of its vectors",
				"∀x y:A. x ∈ M.carrier ∧ y ∈ M.carrier ⇒ x + -y ∈ M.carrier",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					in := b.Conjuncts(
						b.Assume(),
						"x belongs to the carrier",
						"y belongs to the carrier")
					b.Show(
						"add x to the inverse of y",
						By(in[0], in[1], At(inverseIn, y), At(group.MulIn.Read(additive), x, b.TermAs[A]("-y"))))
				}))

			a.Do(
				Unfold(metric_space.MetricSpace),
				Unfold(NormDistanceDef),
				SplitConjAll(
					Case(
						"distance vanishes precisely for equal vectors",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							in := b.Conjuncts(
								b.Assume(),
								"x belongs to the carrier",
								"y belongs to the carrier")
							xy := b.TermAs[A]("x + -y")
							zeroDifference := b.Have(
								"the difference is zero exactly when x equals y",
								"x + -y = M.zero ⇔ x = y",
								By(
									in[0],
									in[1],
									At(inverseIn, y),
									At(group.InvUniqueOn.Read(additive), x, b.TermAs[A]("-y")),
									At(group.InvInvOn.Read(additive), y)))
							b.Show(
								"the norm detects the zero vector",
								By(in[0], in[1], At(differenceIn, x, y), At(definite, xy), zeroDifference))
						})),
					Case(
						"reversing the difference preserves its norm",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							in := b.Conjuncts(
								b.Assume(),
								"x belongs to the carrier",
								"y belongs to the carrier")
							xy := b.TermAs[A]("x + -y")
							unitModulus := b.Have(
								"minus one has unit modulus",
								"|-complex_ring.one| = &1",
								ByArith())
							negationPreservesNorm := b.Have(
								"multiplying the difference by minus one preserves its norm",
								"v(-(x + -y)) = v(x + -y)",
								By(
									in[0],
									in[1],
									At(differenceIn, x, y),
									unitModulus,
									At(homogeneous, b.TermAs[Complex]("-complex_ring.one"), xy),
									At(module.NegOneSmul.Read(moduleOn), xy),
									At(real_construction.MulLeftId, b.TermAs[Real]("v(x + -y)"))))
							reversed := b.Have(
								"the inverse of the difference interchanges the two vectors",
								"-(x + -y) = y + -x",
								By(
									in[0],
									in[1],
									At(inverseIn, y),
									At(group.InvMulOn.Read(additive), x, b.TermAs[A]("-y")),
									At(group.InvInvOn.Read(additive), y)))
							b.Show(
								"apply the norm to the reversed difference",
								By(reversed, negationPreservesNorm))
						})),
					Case(
						"the distance satisfies the triangle inequality",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							y := b.FixAs[A]("y")
							z := b.FixAs[A]("z")
							in := b.Conjuncts(
								b.Assume(),
								"x belongs to the carrier",
								"y belongs to the carrier",
								"z belongs to the carrier")
							xy := b.TermAs[A]("x + -y")
							yz := b.TermAs[A]("y + -z")
							joined := b.Have(
								"adding the two successive differences cancels the middle vector",
								"(x + -y) + (y + -z) = x + -z",
								By(
									in[0],
									in[1],
									in[2],
									At(differenceIn, x, y),
									At(inverseIn, z),
									At(group.AssocOn.Read(additive), xy, y, b.TermAs[A]("-z")),
									At(group.InvMulCancelRightOn.Read(additive), y, x)))
							b.Show(
								"bound the norm of the sum by the sum of the norms",
								By(
									in[0],
									in[1],
									in[2],
									At(differenceIn, x, y),
									At(differenceIn, y, z),
									At(triangle, xy, yz),
									joined))
						})),
				))
		}),
})}
