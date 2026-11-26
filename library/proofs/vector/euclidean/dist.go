// dist.go — the distance, and the n-vectors as a metric space.

package euclidean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// NormEqZero — on a dimension the norm vanishes exactly at the zero
// vector. The norm is the root of the form: a norm of zero squares to a
// form of zero, and the root of a zero form is zero. On a dimension the
// form in turn vanishes exactly at the zero vector (DotEqZero).
var NormEqZero = normEqZeroThm{family.Add(registry.ProofEntry{
	Name: "NormEqZero",
	Key:  "prop_403da0d8c8ef68ac",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀u:(num → real).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
		},
		Conclusion: "‖u‖_n = &0 ⇔ u = vec_zero",
	},
		func(a *Argument, n *Expr[Nat], u *Vec[Real, DimN], member Fact) {
			formZero := a.Have(
				"the norm vanishes exactly where the form does",
				"‖u‖_n = &0 ⇔ ⟪u, u⟫_n = &0",
				Derive(func(b *Argument) {
					b.Iff()
					b.Forward(
						"a norm of zero squares to a form of zero",
						func(c *Argument, zero Fact) {
							c.Do(Simp(Rev(NormPow2)), zero.Rw())
							c.Show(
								"and zero squared is zero",
								ByArith())
						})
					b.Backward(
						"the root of a zero form is zero",
						func(c *Argument, zero Fact) {
							c.Show(
								"the norm is the root of the form, which is zero, and the root of zero is zero",
								Simp(Fwd(VecNormDef)),
								zero.Rw(),
								By(real_sqrt.SqrtZero))
						})
				}))
			a.Show(
				"and on a dimension the form vanishes exactly at the zero vector",
				By(formZero, At(DotEqZero, n, u), member))
		}),
})}

// DistEqZero — two n-vectors are at distance zero exactly when they are
// equal: their difference is an n-vector, whose norm vanishes exactly
// when it is the zero vector, which is to say when u = v.
var DistEqZero = distEqZeroThm{family.Add(registry.ProofEntry{
	Name: "DistEqZero",
	Key:  "prop_15f70479cfea323",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀u v:(num → real).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
			"vec⟨n⟩(v)",
		},
		Conclusion: "dist⟨n⟩(u, v) = &0 ⇔ u = v",
	},
		func(a *Argument, n *Expr[Nat], u, v *Vec[Real, DimN], members Fact) {
			diff := a.VecAs[Real, DimN]("u - v")
			inDim := a.Have(
				"the difference is an n-vector",
				"vec⟨n⟩(u - v)",
				By(members, vec_space.VecSub.Read(real_ring.CommRing)))
			// The distance is the norm of the difference.
			a.Do(Unfold(VecDistDef))
			definite := a.Have(
				"the difference, an n-vector, has norm zero exactly when it is the zero vector",
				"‖u - v‖_n = &0 ⇔ u - v = vec_zero",
				By(NormEqZero.At(proof.Inhabit(diff, inDim))))
			a.Show(
				"and the difference is the zero vector exactly when u = v",
				definite.Rw(),
				By(vec_space.SubEqZero.Read(real_ring.CommRing).At(u, v)))
		}),
})}

// NormSubRefl — every sequence is at distance zero from itself, on a
// dimension or not: u − u is the zero vector, whose norm is zero.
var NormSubRefl = normSubReflThm{family.Add(registry.ProofEntry{
	Name: "NormSubRefl",
	Key:  "prop_9e2b2c0bd6fb82d4",
	Build: family.Theorem("∀n:num. ∀u:(num → real). ‖u - u‖_n = &0",
		func(a *Argument, n *Expr[Nat], u *Expr[Fun[Nat, Real]]) {
			a.Show(
				"u − u is the zero vector, of norm zero",
				By(Normalized, vec_space.SubEqZero.Read(real_ring.CommRing).At(u, u), NormVecZero.At(n)))
		}),
})}

// LineThroughPoint — the line t ↦ c + t•u through an n-vector c in the
// direction of an n-vector u: it starts at c, and its point at t is an
// n-vector, t•u from c, at distance |t|‖u‖ from it.
var LineThroughPoint = lineThroughPointThm{family.Add(registry.ProofEntry{
	Name: "LineThroughPoint",
	Key:  "prop_40540b79137a0ed7",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀c u:(num → real).",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
			"vec⟨n⟩(u)",
		},
		Conclusion: "c + &0 • u = c ∧ " +
			"(∀t:real. vec⟨n⟩(c + t • u) ∧ c + t • u - c = t • u ∧ ‖c + t • u - c‖_n = |t| * ‖u‖_n)",
	},
		func(a *Argument, n *Expr[Nat], c, u *Vec[Real, DimN], cIn, uIn Fact) {
			a.Do(SplitConj(
				Case(
					"the line starts at c, pointwise c(i) + 0·u(i) being c(i)",
					Funext(),
					Unfold(vec_space.VecAddDef),
					Unfold(vec_space.VecScalarMulDef),
					ByArith()),
				Case(
					"its point at t is an n-vector, t•u from c, at distance |t|‖u‖",
					Derive(func(b *Argument) {
						t := b.FixAs[Real]("t")
						step := b.VecAs[Real, DimN]("t • u")
						offset := b.Have(
							"the step from c to c + t•u is t•u",
							"c + t • u - c = t • u",
							By(
								Normalized,
								vec_space.AddComm.Read(real_ring.CommRing).At(c, step),
								vec_space.AddSubCancelRight.Read(real_ring.CommRing).At(step, c)))
						b.Show(
							"c + t•u is a sum of n-vectors, and the step t•u has the norm |t|‖u‖",
							By(
								cIn,
								vec_space.VecSmul.Read(real_ring.CommRing).At(t, proof.Inhabit(u, uIn)),
								vec_space.VecAdd.Read(real_ring.CommRing),
								offset,
								NormSmul.At(t, u)))
					}))))
		}),
})}

// DistSym — the distance reads the same both ways: the form of the
// difference with itself does not see the order of the two vectors, and
// the distance is its root.
var DistSym = distSymThm{family.Add(registry.ProofEntry{
	Name: "DistSym",
	Key:  "prop_7b751b549744ff6",
	Build: family.Theorem("∀n:num. ∀u v:(num → real). dist⟨n⟩(u, v) = dist⟨n⟩(v, u)",
		func(a *Argument, n *Expr[Nat], u, v *Vec[Real, DimN]) {
			// Each distance is the root of the form of its difference.
			a.Do(Unfold(VecDistDef), Unfold(VecNormDef))
			form := a.Have(
				"the form of the difference with itself, expanded, reads the same either way round",
				"⟪u - v, u - v⟫_n = ⟪v - u, v - u⟫_n",
				Simp(Fwd(dot.SubLeft.Read(real_ring.CommRing)), Fwd(dot.SubRight.Read(real_ring.CommRing))),
				ByArith())
			a.Show(
				"so the two roots are one",
				form.Rw(),
				TrivialNormalized())
		}),
})}

// DistTriangle — the triangle inequality for the distance: u − w is the
// sum of the two steps u − v and v − w, and the norm of a sum is at most
// the sum of the norms (NormTriangle).
var DistTriangle = distTriangleThm{family.Add(registry.ProofEntry{
	Name: "DistTriangle",
	Key:  "prop_bafdd7b738eecef8",
	Build: family.Theorem("∀n:num. ∀u v w:(num → real). dist⟨n⟩(u, w) ≤ dist⟨n⟩(u, v) + dist⟨n⟩(v, w)",
		func(a *Argument, n *Expr[Nat], u, v, w *Vec[Real, DimN]) {
			steps := a.Have(
				"the difference u − w is the sum of the two steps u − v and v − w",
				"u - w = (u - v) + (v - w)",
				Funext(),
				Unfold(vec_space.VecAddDef),
				Unfold(vec_space.VecSubDef),
				ByArith())
			a.Do(Unfold(VecDistDef), steps.Rw())
			a.Show(
				"and the norm of a sum is at most the sum of the norms",
				By(NormTriangle.At(a.VecAs[Real, DimN]("u - v"), a.VecAs[Real, DimN]("v - w"))))
		}),
})}

// EuclideanMetric — the n-vectors with the distance form a metric space,
// at every n: the three axioms are the three facts above, read on the
// carrier of the n-vectors.
var EuclideanMetric = euclideanMetricThm{family.Add(registry.ProofEntry{
	Name: "EuclideanMetric",
	Key:  "prop_7c7e160290822494",
	Build: family.Instance(metric_space.MetricSpace, "∀n:num. "+
		"    metric_space({u:(num → real) | vec⟨n⟩(u)}, vec_dist⟨n⟩)",
		Case(
			"two n-vectors are at distance zero exactly when they are equal",
			Derive(func(b *Argument) {
				x := b.VecFixAs[Real, DimN]("x")
				y := b.VecFixAs[Real, DimN]("y")
				members := b.Conjuncts(
					b.Have(
						"both are n-vectors",
						"vec⟨n⟩(x) ∧ vec⟨n⟩(y)",
						BySets(b.Assume())),
					"x is an n-vector",
					"so is y")
				b.Show(
					"which is the distance's definiteness",
					By(DistEqZero.At(proof.Inhabit(x, members[0]), proof.Inhabit(y, members[1]))))
			})),
		Case(
			"the distance is symmetric",
			BySets(DistSym)),
		Case(
			"and it obeys the triangle inequality",
			BySets(DistTriangle)),
	),
})}
