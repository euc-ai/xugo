// opnorm.go — the operator norm of a linear map between Euclidean spaces.
//
// `vec_op_norm⟨n, m⟩(L)` is the supremum of ‖L(u)‖_m over the n-vectors u
// of norm at most 1. A supremum says something only of a set that is
// nonempty and bounded above, and for a linear L both hold: the zero
// vector lies in the unit ball, and the basis estimate
// (LinearBasisEstimate) bounds every image of the ball by the total size
// of L's images of the basis. Every law below is therefore stated for a
// linear L, and the first is the one place the boundedness is spent: the
// operator norm bounds the image of the unit ball. Scaling carries that
// to every n-vector, ‖L(h)‖ ≤ ‖L‖·‖h‖, and the operator norm is the least
// nonnegative factor that does so.

package euclidean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// OpNormUnitBall — the operator norm of a linear map is at least the size
// of its image of every n-vector of norm at most 1. The sizes of those
// images are bounded above by the total size of the map's images of the
// basis (LinearBasisEstimate), so their supremum is at least each of them.
var OpNormUnitBall = opNormUnitBallThm{family.Add(registry.ProofEntry{
	Name: "OpNormUnitBall",
	Key:  "prop_b5d8891415f34d2d",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀L:((num → real) → (num → real)). ∀u:(num → real).",
		Hypotheses: []string{
			"vec_linear(L)",
			"vec⟨n⟩(u)",
			"‖u‖_n ≤ &1",
		},
		Conclusion: "‖L(u)‖_m ≤ vec_op_norm⟨n, m⟩(L)",
		Abbrev: Abbrev{
			{Name: "unitImages", Text: "{‖L(v)‖_m | v:(num → real) | vec⟨n⟩(v) ∧ ‖v‖_n ≤ &1}"},
			{Name: "basisImageTotal", Text: "Σ_{i<n} ‖L(basis_vector(i))‖_m"},
		},
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			L *VecFun[Real, DimN, DimM],
			u *Vec[Real, DimN],
			linear, member, small Fact,
		) {
			total := a.Term("«basisImageTotal»")
			nonneg := a.Have(
				"the total size of L's images of the basis is not negative",
				"&0 ≤ «basisImageTotal»",
				By(real_sum.Nonneg, NormNonneg))
			bounded := a.Have(
				"so the sizes of L's images of the unit ball are bounded above, by that total",
				"∃b:real. ∀y:real. y ∈ «unitImages» ⇒ y ≤ b",
				Derive(func(b *Argument) {
					b.Take(total)
					b.FixAs[Real]("y")
					v, inBall := b.UnpackAs[Fun[Nat, Real]](b.Assume(), "v")
					b.Show(
						"the basis estimate prices L(v) at the total times ‖v‖, at most the total itself",
						ByArith(
							inBall,
							nonneg,
							linear,
							At(LinearBasisEstimate, n, m, L, v),
							At(real_order_ring.LessEqMulLeft, total, b.TermAs[Real]("‖v‖_n"), b.TermAs[Real]("&1"))))
				}))
			inSet := a.Have(
				"‖L(u)‖ is one of those sizes, u lying in the unit ball",
				"‖L(u)‖_m ∈ «unitImages»",
				By(member, small))
			a.Do(Unfold(VecOpNormDef))
			a.Show(
				"and a member of a set bounded above is at most its supremum",
				By(
					bounded,
					inSet,
					At(real_sup_inf.MemberLessEqSup, a.TermAs[Set[Real]]("«unitImages»"), a.TermAs[Real]("‖L(u)‖_m"))))
		}),
})}

// OpNormBound — a linear map stretches no n-vector by more than its
// operator norm: ‖L(h)‖_m ≤ ‖L‖·‖h‖_n. A vector of norm 0 has an image of
// size 0, by the basis estimate; any other h, scaled by 1/‖h‖, has norm
// 1 (NormNormalize) and so lies in the unit ball, where the operator norm
// bounds the image (OpNormUnitBall), and L, being linear, scales that
// image back by ‖h‖.
var OpNormBound = opNormBoundThm{family.Add(registry.ProofEntry{
	Name: "OpNormBound",
	Key:  "prop_4a6db98f346f2ea2",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀L:((num → real) → (num → real)). ∀h:(num → real).",
		Hypotheses: []string{
			"vec_linear(L)",
			"vec⟨n⟩(h)",
		},
		Conclusion: "‖L(h)‖_m ≤ vec_op_norm⟨n, m⟩(L) * ‖h‖_n",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			L *VecFun[Real, DimN, DimM],
			h *Vec[Real, DimN],
			linear, member Fact,
		) {
			size := a.TermAs[Real]("‖h‖_n")
			a.Cases(a.TermAs[Bool]("‖h‖_n = &0"))
			a.When(
				"h has norm 0, and the basis estimate prices L(h) at 0",
				func(b *Argument, zero Fact) {
					b.Show(
						"the total size of L's images of the basis times 0",
						ByArith(zero, linear, LinearBasisEstimate.At(m, L, proof.Inhabit(h, member))))
				})
			a.Otherwise(
				"otherwise h scaled by 1/‖h‖ has norm 1, and its image is L(h) scaled the same way",
				func(b *Argument, nonzero Fact) {
					scale := b.TermAs[Real]("real_inv(‖h‖_n)")
					unit := b.VecAs[Real, DimN]("real_inv(‖h‖_n) • h")
					pulled := b.Have(
						"L, being linear, carries the scaling to the image",
						"L(real_inv(‖h‖_n) • h) = real_inv(‖h‖_n) • L(h)",
						By(linear, vec_space.VecLinearDef))
					image := b.Have(
						"so the image of the scaled vector has size ‖L(h)‖/‖h‖",
						"‖L(real_inv(‖h‖_n) • h)‖_m = real_inv(‖h‖_n) * ‖L(h)‖_m",
						pulled.Rw(),
						ByArith(
							nonzero,
							NormSmul.At(scale, L.Apply(h)),
							At(real_sgn_abs.AbsInv, size),
							At(real_sgn_abs.AbsFixedIffNonneg, size),
							NormNonneg.At(h)))
					b.Show(
						"which the operator norm bounds; multiplying back by ‖h‖ gives the estimate",
						ByArith(
							nonzero,
							NormNormalize.At(h),
							image,
							linear,
							vec_space.VecSmul.Read(real_ring.CommRing).At(scale, proof.Inhabit(h, member)),
							At(OpNormUnitBall, n, m, L, unit),
							NormNonneg.At(h),
							At(
								real_order_ring.LessEqMulLeft,
								size,
								b.TermAs[Real]("real_inv(‖h‖_n) * ‖L(h)‖_m"),
								b.TermAs[Real]("vec_op_norm⟨n, m⟩(L)"))))
				})
		}),
})}

// OpNormNonneg — the operator norm of a linear map is not negative: the
// zero vector lies in the unit ball, and the size of its image is a norm.
var OpNormNonneg = opNormNonnegThm{family.Add(registry.ProofEntry{
	Name: "OpNormNonneg",
	Key:  "prop_f15d32212bfcd460",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀L:((num → real) → (num → real)).",
		Hypotheses: []string{
			"vec_linear(L)",
		},
		Conclusion: "&0 ≤ vec_op_norm⟨n, m⟩(L)",
	},
		func(a *Argument, n, m *Expr[Nat], L *VecFun[Real, DimN, DimM], linear Fact) {
			zero := a.VecAs[Real, DimN]("vec_zero")
			a.Show(
				"the zero vector, of norm 0, lies in the unit ball, and its image has a size of at least 0",
				ByArith(
					linear,
					vec_space.VecZero.At(a.TermAs[Real]("&0"), n),
					NormVecZero.At(n),
					At(OpNormUnitBall, n, m, L, zero),
					NormNonneg.At(L.Apply(zero))))
		}),
})}

// OpNormLessEqIff — a nonnegative B is at least the operator norm of a
// linear map exactly when the map stretches no n-vector by more than B:
// the operator norm is the least such factor. One way, the operator norm
// stretches no vector by more than itself (OpNormBound); the other, a
// factor that bounds every stretch bounds every image of the unit ball,
// and so their supremum. The sign of B is needed only there: in dimension
// 0 every factor bounds the stretch of the one vector, of norm 0.
var OpNormLessEqIff = opNormLessEqIffThm{family.Add(registry.ProofEntry{
	Name: "OpNormLessEqIff",
	Key:  "prop_899270798671f6ed",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀L:((num → real) → (num → real)). ∀B:real.",
		Hypotheses: []string{
			"vec_linear(L)",
			"&0 ≤ B",
		},
		Conclusion: "vec_op_norm⟨n, m⟩(L) ≤ B ⇔ ∀h:(num → real). vec⟨n⟩(h) ⇒ ‖L(h)‖_m ≤ B * ‖h‖_n",
		Abbrev: Abbrev{
			{Name: "unitImages", Text: "{‖L(v)‖_m | v:(num → real) | vec⟨n⟩(v) ∧ ‖v‖_n ≤ &1}"},
		},
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			L *VecFun[Real, DimN, DimM],
			B *Expr[Real],
			linear, nonneg Fact,
		) {
			norm := a.TermAs[Real]("vec_op_norm⟨n, m⟩(L)")
			images := a.TermAs[Set[Real]]("«unitImages»")
			a.Iff()
			a.Forward(
				"B, at least the operator norm, is at least every stretch",
				func(b *Argument, below Fact) {
					h := b.VecFixAs[Real, DimN]("h")
					member := b.Assume()
					b.Show(
						"‖L(h)‖ is at most ‖L‖·‖h‖, at most B·‖h‖ as ‖h‖ is not negative",
						ByArith(
							below,
							OpNormBound.At(L, proof.Inhabit(h, member)),
							linear,
							NormNonneg.At(h),
							At(real_order_ring.LessEqMulRight, norm, B, b.TermAs[Real]("‖h‖_n"))))
				})
			a.Backward(
				"a factor that bounds every stretch bounds every image of the unit ball, and so their supremum",
				func(b *Argument, stretch Fact) {
					zeroInBall := b.Have(
						"the zero vector lies in the unit ball, its norm being 0",
						"‖vec_zero‖_n ≤ &1",
						ByArith(NormVecZero.At(n)))
					atZero := b.Have(
						"so the size of L's image of it is among the sizes",
						"‖L(vec_zero)‖_m ∈ «unitImages»",
						By(vec_space.VecZero.At(b.TermAs[Real]("&0"), n), zeroInBall))
					nonempty := b.Have(
						"so the set of the sizes is not empty",
						"«unitImages» ≠ ∅",
						By(atZero, set_basic.MemberNotEmpty.At(images)))
					capped := b.Have(
						"and each size is at most B, its vector's norm being at most 1",
						"∀y:real. y ∈ «unitImages» ⇒ y ≤ B",
						Derive(func(c *Argument) {
							c.FixAs[Real]("y")
							v, inBall := c.UnpackAs[Fun[Nat, Real]](c.Assume(), "v")
							c.Show(
								"‖L(v)‖ is at most B·‖v‖, at most B",
								ByArith(
									inBall,
									stretch.At(v),
									nonneg,
									At(real_order_ring.LessEqMulLeft, B, c.TermAs[Real]("‖v‖_n"), c.TermAs[Real]("&1"))))
						}))
					b.Do(Unfold(VecOpNormDef))
					b.Show(
						"the supremum of a nonempty set is at most any bound of it",
						By(nonempty, capped, At(real_sup_inf.SupLessEqBound, images, B)))
				})
		}),
})}

// LinearBasisBound — the operator norm of a linear map on the m-vectors is
// at most the total size of its images of the basis: that total bounds
// every stretch (LinearBasisEstimate), and the operator norm is the least
// such factor (OpNormLessEqIff). The total is a formula in the map, so
// the bound composes — it can be summed, iterated and read at a family.
var LinearBasisBound = linearBasisBoundThm{family.Add(registry.ProofEntry{
	Name: "LinearBasisBound",
	Key:  "prop_84111db38423a94e",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num. ∀f:((num → real) → num → real).",
			Hypotheses: []string{
				"vec_linear(f)",
			},
			Conclusion: "vec_op_norm⟨m, n⟩(f) ≤ «basisImageTotal»",
			Abbrev: Abbrev{
				{Name: "basisImageTotal", Text: "Σ_{i<m} ‖f(basis_vector(i))‖_n"},
			},
		},
		func(a *Argument, m, n *Expr[Nat], f *VecFun[Real, DimM, DimN], linear Fact) {
			total := a.TermAs[Real]("«basisImageTotal»")
			nonneg := a.Have(
				"the total size of f's images of the basis is not negative",
				"&0 ≤ «basisImageTotal»",
				By(real_sum.Nonneg, NormNonneg))
			stretch := a.Have(
				"and it bounds every stretch of f on the m-vectors",
				"∀x:(num → real). vec⟨m⟩(x) ⇒ ‖f(x)‖_n ≤ «basisImageTotal» * ‖x‖_m",
				By(linear, At(LinearBasisEstimate, m, n, f)))
			a.Show(
				"so it is at least the least such factor, the operator norm",
				By(stretch, linear, nonneg, OpNormLessEqIff.At(f, total)))
		}),
})}

// OpNormTriangle — the operator norm of a sum of linear maps is at most
// the sum of their operator norms. The sum is linear, and at each n-vector
// the norm's triangle inequality and the two maps' bounds (OpNormBound)
// price its image by the sum of the norms; the operator norm is the least
// such factor (OpNormLessEqIff).
var OpNormTriangle = opNormTriangleThm{family.Add(registry.ProofEntry{
	Name: "OpNormTriangle",
	Key:  "prop_232087adb161a8be",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀L K:((num → real) → (num → real)).",
		Hypotheses: []string{
			"vec_linear(L)",
			"vec_linear(K)",
		},
		Conclusion: "vec_op_norm⟨n, m⟩(λv:(num → real). L(v) + K(v)) ≤ " +
			"vec_op_norm⟨n, m⟩(L) + vec_op_norm⟨n, m⟩(K)",
	},
		func(a *Argument, n, m *Expr[Nat], L, K *VecFun[Real, DimN, DimM], linearL, linearK Fact) {
			sum := a.VecFunAs[Real, DimN, DimM]("λv:(num → real). L(v) + K(v)")
			bound := a.TermAs[Real]("vec_op_norm⟨n, m⟩(L) + vec_op_norm⟨n, m⟩(K)")
			linear := a.Have(
				"the sum of the two linear maps is linear",
				"vec_linear(λv:(num → real). L(v) + K(v))",
				By(linearL, linearK, vec_space.LinearAdd.Read(real_ring.CommRing).At(L, K)))
			nonneg := a.Have(
				"the sum of the two operator norms is not negative",
				"&0 ≤ vec_op_norm⟨n, m⟩(L) + vec_op_norm⟨n, m⟩(K)",
				ByArith(linearL, linearK, OpNormNonneg.At(L), OpNormNonneg.At(K)))
			stretch := a.Have(
				"the sum stretches no n-vector by more than the sum of the operator norms",
				Statement{
					Binders: "∀h:(num → real).",
					Hypotheses: []string{
						"vec⟨n⟩(h)",
					},
					Conclusion: "‖L(h) + K(h)‖_m ≤ (vec_op_norm⟨n, m⟩(L) + vec_op_norm⟨n, m⟩(K)) * ‖h‖_n",
				},
				Derive(func(b *Argument) {
					h := b.VecFixAs[Real, DimN]("h")
					member := b.Assume()
					b.Show(
						"the norm's triangle inequality, then each map's bound",
						ByArith(
							NormTriangle.At(L.Apply(h), K.Apply(h)),
							OpNormBound.At(L, proof.Inhabit(h, member)),
							OpNormBound.At(K, proof.Inhabit(h, member)),
							linearL,
							linearK))
				}))
			a.Show(
				"so the sum of the operator norms is at least the least such factor",
				By(stretch, linear, nonneg, OpNormLessEqIff.At(sum, bound)))
		}),
})}

// OpNormSmul — scaling a linear map by c scales its operator norm by |c|.
// The scaled map stretches each vector by |c| times what the map does
// (NormSmul), so |c|·‖L‖ bounds its stretch and is at least its operator
// norm (OpNormLessEqIff). Conversely, for c ≠ 0 the map stretches each
// vector by 1/|c| times what the scaled map does, so ‖L‖ is at most
// ‖c•L‖/|c|; for c = 0 the left side is 0, below every operator norm.
var OpNormSmul = opNormSmulThm{family.Add(registry.ProofEntry{
	Name: "OpNormSmul",
	Key:  "prop_546d0450438bebf",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀L:((num → real) → (num → real)). ∀c:real.",
		Hypotheses: []string{
			"vec_linear(L)",
		},
		Conclusion: "vec_op_norm⟨n, m⟩(λv:(num → real). c • L(v)) = |c| * vec_op_norm⟨n, m⟩(L)",
	},
		func(a *Argument, n, m *Expr[Nat], L *VecFun[Real, DimN, DimM], c *Expr[Real], linear Fact) {
			scaled := a.VecFunAs[Real, DimN, DimM]("λv:(num → real). c • L(v)")
			size := a.TermAs[Real]("|c|")
			norm := a.TermAs[Real]("vec_op_norm⟨n, m⟩(L)")
			scaledLinear := a.Have(
				"the scaled map is linear",
				"vec_linear(λv:(num → real). c • L(v))",
				By(linear, vec_space.LinearScale.Read(real_ring.CommRing).At(L, c)))
			nonneg := a.Have(
				"‖L‖ and |c| are not negative",
				"&0 ≤ vec_op_norm⟨n, m⟩(L) ∧ &0 ≤ |c|",
				By(linear, OpNormNonneg.At(L), At(real_sgn_abs.AbsNonneg, c)))
			stretch := a.Have(
				"the scaled map stretches each vector by |c| times what L does",
				"∀h:(num → real). ‖c • L(h)‖_m = |c| * ‖L(h)‖_m",
				Derive(func(b *Argument) {
					h := b.VecFixAs[Real, DimN]("h")
					b.Show(
						"the norm of a multiple",
						By(NormSmul.At(c, L.Apply(h))))
				}))
			above := a.Have(
				"so |c|·‖L‖ bounds its stretch, and is at least its operator norm",
				"vec_op_norm⟨n, m⟩(λv:(num → real). c • L(v)) ≤ |c| * vec_op_norm⟨n, m⟩(L)",
				Derive(func(b *Argument) {
					bound := b.TermAs[Real]("|c| * vec_op_norm⟨n, m⟩(L)")
					within := b.Have(
						"|c|·‖L‖ bounds the stretch of the scaled map",
						"∀h:(num → real). vec⟨n⟩(h) ⇒ ‖c • L(h)‖_m ≤ |c| * vec_op_norm⟨n, m⟩(L) * ‖h‖_n",
						Derive(func(d *Argument) {
							h := d.VecFixAs[Real, DimN]("h")
							member := d.Assume()
							d.Show(
								"|c| times L's bound at h",
								ByArith(
									stretch.At(h),
									OpNormBound.At(L, proof.Inhabit(h, member)),
									linear,
									nonneg,
									real_order_ring.LessEqMulLeft.At(
										size, d.TermAs[Real]("‖L(h)‖_m"), d.TermAs[Real]("vec_op_norm⟨n, m⟩(L) * ‖h‖_n"))))
						}))
					b.Show(
						"the operator norm is the least such factor",
						ByArith(within, scaledLinear, nonneg, OpNormLessEqIff.At(scaled, bound)))
				}))
			a.Cases(a.TermAs[Bool]("c = &0"))
			a.When(
				"c = 0: |c|·‖L‖ is 0, and the scaled map's operator norm is not negative",
				func(b *Argument, zero Fact) {
					b.Show(
						"both sides are 0",
						ByArith(zero, above, nonneg, scaledLinear, OpNormNonneg.At(scaled), real_sgn_abs.AbsOfZero))
				})
			a.Otherwise(
				"c ≠ 0: L stretches each vector by 1/|c| times what the "+
					"scaled map does, so ‖L‖ is at most its operator norm over |c|",
				func(b *Argument, nonzero Fact) {
					inverse := b.TermAs[Real]("real_inv(|c|)")
					positive := b.Have(
						"|c| is positive",
						"&0 < |c|",
						By(nonzero, At(real_sgn_abs.AbsPosIffNonzero, c)))
					below := b.Have(
						"‖c•L‖/|c| bounds the stretch of L",
						Statement{
							Binders: "∀h:(num → real).",
							Hypotheses: []string{
								"vec⟨n⟩(h)",
							},
							Conclusion: "‖L(h)‖_m ≤ real_inv(|c|) * vec_op_norm⟨n, m⟩(λv:(num → real). c • L(v)) * ‖h‖_n",
						},
						Derive(func(d *Argument) {
							h := d.VecFixAs[Real, DimN]("h")
							member := d.Assume()
							d.Show(
								"|c|·‖L(h)‖ is the scaled map's stretch, at most ‖c•L‖·‖h‖; divide by |c|",
								ByArith(
									stretch.At(h),
									OpNormBound.At(scaled, proof.Inhabit(h, member)),
									scaledLinear,
									positive,
									real_order_ring.LessEqMulLeft.At(
										inverse,
										d.TermAs[Real]("|c| * ‖L(h)‖_m"),
										d.TermAs[Real]("vec_op_norm⟨n, m⟩(λv:(num → real). c • L(v)) * ‖h‖_n"))))
						}))
					least := b.Have(
						"so ‖L‖ is at most ‖c•L‖/|c|",
						"vec_op_norm⟨n, m⟩(L) ≤ real_inv(|c|) * vec_op_norm⟨n, m⟩(λv:(num → real). c • L(v))",
						ByArith(
							below,
							linear,
							positive,
							scaledLinear,
							OpNormNonneg.At(scaled),
							OpNormLessEqIff.At(
								L, b.TermAs[Real]("real_inv(|c|) * vec_op_norm⟨n, m⟩(λv:(num → real). c • L(v))"))))
					b.Show(
						"and |c|·‖L‖ ≤ ‖c•L‖, which with the other bound is equality",
						ByArith(
							above,
							least,
							positive,
							nonneg,
							real_order_ring.LessEqMulLeft.At(
								size, norm, b.TermAs[Real]("real_inv(|c|) * vec_op_norm⟨n, m⟩(λv:(num → real). c • L(v))"))))
				})
		}),
})}
