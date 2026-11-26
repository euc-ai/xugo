// derivative.go — the derivative: uniqueness, continuity, the rules and
// the chain rule, and the derivative read along a line — coordinate by
// coordinate a one-variable derivative — with the mean value inequality it
// gives. The file opens with the fact that a map which inverts another on
// ℝⁿ is one-to-one there.

package vec_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// InverseInjective — a map K that inverts L on ℝⁿ is one-to-one there: two
// n-vectors with one image under K are both L of that image.
var InverseInjective = inverseInjectiveThm{family.Add(registry.ProofEntry{
	Name: "InverseInjective",
	Key:  "prop_c60258daf5965974",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀L K:((num → real) → (num → real)). ∀u v:(num → real).",
		Hypotheses: []string{
			"vec_inverse_on⟨n⟩(L, K)",
			"vec⟨n⟩(u)",
			"vec⟨n⟩(v)",
			"K(u) = K(v)",
		},
		Conclusion: "u = v",
	},
		func(
			a *Argument,
			n *Expr[Nat],
			L, K *VecFun[Real, DimN, DimN],
			u, v *Vec[Real, DimN],
			inverse, uIn, vIn, same Fact,
		) {
			undoes := a.Conjuncts(
				a.Unfolded(inverse, VecInverseOnDef),
				"K is linear",
				"and on ℝⁿ it takes values in ℝⁿ, L undoes it and it undoes L")[1]
			a.Show(
				"u is L(K(u)), which is L(K(v)), which is v",
				By(undoes.At(u), uIn, undoes.At(v), vIn, same))
		}),
})}

// VecDerivativeUnique — a map has at most one derivative at a point: two
// derivatives agree at every n-vector u. Each coordinate of L(u) below m,
// and of K(u), is the derivative at 0 of the coordinate of f along the
// line through c in the direction u (DirectionalDerivative), and a real
// function has one derivative (real_derivative.DerivativeUnique); two
// m-vectors that agree below m are equal (vec_space.Extensionality).
var VecDerivativeUnique = vecDerivativeUniqueThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeUnique",
	Key:  "prop_e8cbe4645e5635b9",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f L K:((num → real) → (num → real)). ∀c u:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
			"vec_derivative_at⟨n, m⟩(f, c, K)",
			"vec⟨n⟩(u)",
		},
		Conclusion: "L(u) = K(u)",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, L, K *VecFun[Real, DimN, DimM],
			c, u *Vec[Real, DimN],
			ofL, ofK, member Fact,
		) {
			valuesL := a.Have(
				"L takes the n-vectors to m-vectors",
				"∀v:(num → real). vec⟨n⟩(v) ⇒ vec⟨m⟩(L(v))",
				By(a.Unfolded(ofL, VecDerivativeAtDef)))
			valuesK := a.Have(
				"and so does K",
				"∀v:(num → real). vec⟨n⟩(v) ⇒ vec⟨m⟩(K(v))",
				By(a.Unfolded(ofK, VecDerivativeAtDef)))
			direction := proof.Inhabit(u, member)
			imageL := L.Apply(u)
			imageK := K.Apply(u)
			inL := a.Have(
				"L(u) is an m-vector",
				"vec⟨m⟩(L(u))",
				By(valuesL.At(u), member))
			inK := a.Have(
				"and so is K(u)",
				"vec⟨m⟩(K(u))",
				By(valuesK.At(u), member))
			coordinates := a.Have(
				"L(u) and K(u) agree below m",
				"∀i:num. i < m ⇒ L(u)(i) = K(u)(i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					below := b.Assume()
					b.Show(
						"each is the derivative at 0 of the i-th coordinate "+
							"of f along the line through c in the direction u",
						By(
							real_derivative.DerivativeUnique.At(
								b.TermAs[Fun[Real, Real]]("λt:real. f(c + t • u)(i)"),
								b.TermAs[Real]("&0"),
								b.TermAs[Real]("L(u)(i)"),
								b.TermAs[Real]("K(u)(i)")),
							ofL,
							below,
							DirectionalDerivative.At(i, f, L, c, direction),
							ofK,
							DirectionalDerivative.At(i, f, K, c, direction)))
				}))
			a.Show(
				"two m-vectors that agree below m are equal",
				By(
					coordinates,
					vec_space.Extensionality.At(
						a.TermAs[Real]("&0"),
						proof.Inhabit(imageL, inL),
						proof.Inhabit(imageK, inK))))
		}),
})}

// VecDerivativeIncrementBound — near a point where it has the derivative
// L, a map grows at most at the rate ‖L‖ + 1, ‖L‖ the operator norm:
// within some radius of c its increment is at most (‖L‖ + 1)·‖x − c‖.
// Inside the radius that serves ε = 1 the error is at most ‖x − c‖,
// L(x − c) is at most ‖L‖·‖x − c‖ (euclidean.OpNormBound), and the
// increment is the error plus L(x − c).
var VecDerivativeIncrementBound = vecDerivativeIncrementBoundThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeIncrementBound",
	Key:  "prop_c24cfcaebd025f34",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f L:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ " +
			"    ∀x:(num → real). " +
			"        vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ ‖f(x) - f(c)‖_m ≤ (vec_op_norm⟨n, m⟩(L) + &1) * ‖x - c‖_n",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			derivative Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(derivative, VecDerivativeAtDef),
				"c is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near c the error is within ε·‖x − c‖")
			point, linear, near := parts[0], parts[1], parts[3]
			δ, radius := a.UnpackAs[Real](
				GroupPremises(real_order_ring.ZeroLessThanOne, near.At(a.TermAs[Real]("&1"))),
				"δ")
			inside := a.Conjuncts(
				radius,
				"the radius is positive",
				"and inside it the error is within ‖x − c‖")
			a.Take(δ)
			a.Do(SplitConj(
				Case(
					"the radius is positive",
					By(inside[0])),
				Case(
					"inside it the increment is the error plus L(x − c), and each is priced",
					Derive(func(b *Argument) {
						x := b.VecFixAs[Real, DimN]("x")
						ball := b.Assume()
						member := b.Conjuncts(
							ball,
							"x is an n-vector",
							"within δ of c")[0]
						step := b.VecAs[Real, DimN]("x - c")
						stepIn := b.Have(
							"the step x − c is an n-vector",
							"vec⟨n⟩(x - c)",
							By(vec_space.VecSub.Read(real_ring.CommRing).At(proof.Inhabit(x, member), proof.Inhabit(c, point))))
						split := b.Have(
							"the increment is the error plus L(x − c)",
							"f(x) - f(c) - L(x - c) + L(x - c) = f(x) - f(c)",
							Funext(),
							Unfold(vec_space.VecAddDef),
							Unfold(vec_space.VecSubDef),
							ByArith())
						triangle := b.Have(
							"so its norm is at most the error's plus that of L(x − c)",
							"‖f(x) - f(c)‖_m ≤ ‖f(x) - f(c) - L(x - c)‖_m + ‖L(x - c)‖_m",
							By(
								split,
								euclidean.NormTriangle.At(
									b.VecAs[Real, DimM]("f(x) - f(c) - L(x - c)"),
									b.VecAs[Real, DimM]("L(x - c)"))))
						b.Show(
							"the error is at most ‖x − c‖ and L(x − c) at most ‖L‖·‖x − c‖",
							ByArith(
								inside[1].At(x),
								ball,
								euclidean.OpNormBound.At(L, proof.Inhabit(step, stepIn)),
								linear,
								triangle))
					})),
			))
		}),
})}

// VecDerivativeContinuous — a map with a derivative L at c is continuous
// there. Near c the increment is at most (‖L‖ + 1)·‖x − c‖, ‖L‖ the
// operator norm (VecDerivativeIncrementBound), and a radius below
// ε/(‖L‖ + 1) keeps it below ε; ‖L‖ is not negative
// (euclidean.OpNormNonneg), so nothing divides by zero.
var VecDerivativeContinuous = vecDerivativeContinuousThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeContinuous",
	Key:  "prop_130e1f6c261c1cc5",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f L:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
		},
		Conclusion: "vec_continuous_at⟨n, m⟩(f, c)",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			derivative Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(derivative, VecDerivativeAtDef),
				"c is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near c the error is within ε·‖x − c‖")
			total := a.Have(
				"the operator norm of L is not negative",
				"&0 ≤ vec_op_norm⟨n, m⟩(L)",
				By(parts[1], euclidean.OpNormNonneg.At(L)))
			δ, growth := a.UnpackAs[Real](
				GroupPremises(derivative, VecDerivativeIncrementBound.At(f, L, c)),
				"δ")
			inside := a.Conjuncts(
				growth,
				"a positive radius",
				"inside which the increment is at most (‖L‖ + 1)·‖x − c‖")
			a.Do(
				Unfold(VecContinuousAtDef),
				SplitConj(
					Case(
						"c is an n-vector",
						By(parts[0])),
					Case(
						"and a radius below ε/(‖L‖ + 1) keeps the increment below ε",
						Derive(func(b *Argument) {
							ε := b.FixAs[Real]("ε")
							pos := b.Assume()
							tolerance := b.TermAs[Real]("ε / (vec_op_norm⟨n, m⟩(L) + &1)")
							b.Take(b.TermAs[Real]("min(δ, ε / (vec_op_norm⟨n, m⟩(L) + &1))"))
							b.Do(SplitConj(
								Case(
									"the smaller radius is positive",
									ByArith(total, inside[0], pos, real_sup_inf.LessThanMin.At(δ, tolerance, b.TermAs[Real]("&0")))),
								Case(
									"inside it ‖x − c‖ < ε/(‖L‖ + 1), so the increment is below ε",
									Derive(func(d *Argument) {
										x := d.VecFixAs[Real, DimN]("x")
										ball := d.Assume()
										distance := d.TermAs[Real]("‖x - c‖_n")
										d.Show(
											"(‖L‖ + 1)·‖x − c‖ < ε",
											ByArith(
												inside[1].At(x),
												total,
												ball,
												real_sup_inf.LessThanMin.At(δ, tolerance, distance),
												real_order_field.LessThanDivMulLeft.At(distance, ε, d.TermAs[Real]("vec_op_norm⟨n, m⟩(L) + &1"))))
									})),
							))
						}))))
		}),
})}

// VecDerivativeExactIncrement — a linear map L carrying ℝⁿ into ℝᵐ is the
// derivative at c of a map whose increment from c it matches exactly: the
// error is the zero vector, so any radius serves every ε.
var VecDerivativeExactIncrement = vecDerivativeExactIncrementThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeExactIncrement",
	Key:  "prop_fc0c64eae8182e3d",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f L:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
			"vec_linear(L)",
			"∀u:(num → real). vec⟨n⟩(u) ⇒ vec⟨m⟩(L(u))",
			"∀x:(num → real). f(x) - f(c) = L(x - c)",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(f, c, L)",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			point, linear, values, exact Fact,
		) {
			noError := a.Have(
				"at every point the error vanishes",
				"∀x:(num → real). f(x) - f(c) - L(x - c) = vec_zero",
				Derive(func(b *Argument) {
					x := b.FixAs[Fun[Nat, Real]]("x")
					b.Show(
						"the increment f(x) − f(c) is L(x − c), so the difference of the two is the zero vector",
						By(exact.At(x), vec_space.SubEqZero.Read(real_ring.CommRing)))
				}))
			a.Do(
				Unfold(VecDerivativeAtDef),
				SplitConj(
					Case(
						"c is an n-vector, and L is linear with values among the m-vectors",
						By(point, linear, values)),
					Case(
						"the error is the zero vector, so the radius 1 serves every ε",
						Derive(func(b *Argument) {
							b.FixAs[Real]("ε")
							pos := b.Assume()
							b.Take(b.TermAs[Real]("&1"))
							b.Show(
								"a norm of zero is at most ε times a norm",
								ByArith(noError, pos, euclidean.NormVecZero, euclidean.NormNonneg))
						}))))
		}),
})}

// VecDerivativeConst — a constant map has the zero map as its derivative
// at every point of ℝⁿ: its increment is the zero vector, which the zero
// map, linear and with values among the m-vectors, matches exactly
// (VecDerivativeExactIncrement).
var VecDerivativeConst = vecDerivativeConstThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeConst",
	Key:  "prop_9b7f1f1d584f86f8",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀k c:(num → real).",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(λx:(num → real). k, c, λu:(num → real). vec_zero)",
	},
		func(a *Argument, n, m *Expr[Nat], k *Expr[Fun[Nat, Real]], c *Vec[Real, DimN], point Fact) {
			constant := a.VecFunAs[Real, DimN, DimM]("λx:(num → real). k")
			zeroMap := a.VecFunAs[Real, DimN, DimM]("λu:(num → real). vec_zero")
			increment := a.Have(
				"the increment of a constant is the zero vector",
				"k - k = vec_zero",
				Funext(),
				Unfold(vec_space.VecSubDef),
				Unfold(vec_space.VecZeroDef),
				ByArith())
			a.Show(
				"the zero map is linear, takes values among the m-vectors, and matches that increment exactly",
				By(
					vec_space.LinearZeroMap.Read(real_ring.CommRing),
					vec_space.VecZero,
					increment,
					VecDerivativeExactIncrement.At(constant, zeroMap, proof.Inhabit(c, point))))
		}),
})}

// VecDerivativeLinear — a linear map carrying ℝⁿ into ℝᵐ is its own
// derivative at every point of ℝⁿ: its increment L(x) − L(c) is L(x − c)
// exactly (vec_space.LinearSub, VecDerivativeExactIncrement).
var VecDerivativeLinear = vecDerivativeLinearThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeLinear",
	Key:  "prop_3d403a7b30a16891",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀L:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
			"vec_linear(L)",
			"∀u:(num → real). vec⟨n⟩(u) ⇒ vec⟨m⟩(L(u))",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(L, c, L)",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			point, linear, values Fact,
		) {
			increment := a.Have(
				"L carries x − c to L(x) − L(c)",
				"∀x:(num → real). L(x) - L(c) = L(x - c)",
				a.ForEach(func(x *Expr[Fun[Nat, Real]]) Action {
					return By(Normalized, linear, vec_space.LinearSub.Read(real_ring.CommRing).At(L, x, c))
				}))
			a.Show(
				"so L matches its own increment exactly",
				By(linear, values, increment, VecDerivativeExactIncrement.At(L, L, proof.Inhabit(c, point))))
		}),
})}

// VecDerivativeIdentity — the identity is its own derivative at every
// point of ℝⁿ: it is linear and keeps ℝⁿ (VecDerivativeLinear).
var VecDerivativeIdentity = vecDerivativeIdentityThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeIdentity",
	Key:  "prop_22b6fbfd5e9c0d3",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀c:(num → real).",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
		},
		Conclusion: "vec_derivative_at⟨n, n⟩(λu:(num → real). u, c, λu:(num → real). u)",
	},
		func(a *Argument, n *Expr[Nat], c *Vec[Real, DimN], point Fact) {
			linear := a.Have(
				"the identity is linear",
				"vec_linear(λu:(num → real). u)",
				Unfold(vec_space.VecLinearDef))
			a.Show(
				"a linear map keeping ℝⁿ is its own derivative",
				By(
					linear,
					VecDerivativeLinear.At(
						a.VecFunAs[Real, DimN, DimN]("λu:(num → real). u"), proof.Inhabit(c, point))))
		}),
})}

// VecDerivativeAdd — the derivative of a sum is the sum of the
// derivatives. The error of f + g at x is the sum of the two errors, so
// inside the smaller of the radii that serve f and g at ε/2 the triangle
// inequality keeps it within ε·‖x − c‖; the sum of L and K is linear
// (vec_space.LinearAdd) and takes the n-vectors to m-vectors.
var VecDerivativeAdd = vecDerivativeAddThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeAdd",
	Key:  "prop_e3f4d6b9f3d8a66",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f g L K:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
			"vec_derivative_at⟨n, m⟩(g, c, K)",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(λx:(num → real). f(x) + g(x), " +
			"    c, " +
			"    λu:(num → real). L(u) + K(u))",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, g, L, K *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			ofF, ofG Fact,
		) {
			byF := a.Conjuncts(
				a.Unfolded(ofF, VecDerivativeAtDef),
				"c is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near c the error of f is within ε·‖x − c‖")
			byG := a.Conjuncts(
				a.Unfolded(ofG, VecDerivativeAtDef),
				"c is an n-vector",
				"K is linear",
				"K takes the n-vectors to m-vectors",
				"and near c the error of g is within ε·‖x − c‖")
			a.Do(
				Unfold(VecDerivativeAtDef),
				SplitConj(
					Case(
						"c is an n-vector, and L + K is linear with values among the m-vectors",
						By(
							byF[0],
							vec_space.LinearAdd.Read(real_ring.CommRing).At(L, K),
							byF[1],
							byG[1],
							byF[2],
							byG[2],
							vec_space.VecAdd.Read(real_ring.CommRing))),
					Case(
						"inside both radii that serve f and g at ε/2 the two errors add up to at most ε·‖x − c‖",
						Derive(func(b *Argument) {
							b.FixAs[Real]("ε")
							pos := b.Assume()
							half := b.TermAs[Real]("ε / &2")
							halfPos := b.Have(
								"the tolerance ε/2 is positive",
								"&0 < ε / &2",
								ByArith(pos))
							δ1, nearF := b.UnpackAs[Real](GroupPremises(halfPos, byF[3].At(half)), "δ₁")
							δ2, nearG := b.UnpackAs[Real](GroupPremises(halfPos, byG[3].At(half)), "δ₂")
							insideF := b.Conjuncts(
								nearF,
								"δ₁ is positive",
								"and inside it the error of f is within ε/2·‖x − c‖")
							insideG := b.Conjuncts(
								nearG,
								"δ₂ is positive",
								"and inside it the error of g is within ε/2·‖x − c‖")
							b.Take(b.TermAs[Real]("min(δ₁, δ₂)"))
							b.Do(SplitConj(
								Case(
									"the smaller radius is positive",
									By(insideF[0], insideG[0], real_sup_inf.LessThanMin.At(δ1, δ2, b.TermAs[Real]("&0")))),
								Case(
									"inside it the error of the sum is the sum of the errors",
									Derive(func(d *Argument) {
										x := d.VecFixAs[Real, DimN]("x")
										ball := d.Assume()
										split := d.Have(
											"the error of f + g is the error of f plus the error of g",
											"f(x) + g(x) - (f(c) + g(c)) - (L(x - c) + K(x - c)) = "+
												"f(x) - f(c) - L(x - c) + (g(x) - g(c) - K(x - c))",
											Funext(),
											Unfold(vec_space.VecAddDef),
											Unfold(vec_space.VecSubDef),
											ByArith())
										d.Show(
											"each error is at most ε/2·‖x − c‖, and the norm of a sum is at most the sum of the norms",
											split.Rw(),
											ByArith(
												insideF[1].At(x),
												insideG[1].At(x),
												ball,
												real_sup_inf.LessThanMin.At(δ1, δ2, d.TermAs[Real]("‖x - c‖_n")),
												euclidean.NormTriangle.At(
													d.VecAs[Real, DimM]("f(x) - f(c) - L(x - c)"),
													d.VecAs[Real, DimM]("g(x) - g(c) - K(x - c)"))))
									})),
							))
						}))))
		}),
})}

// VecDerivativeScale — the derivative of a scalar multiple is the
// multiple of the derivative. The error of a•f is a times the error of
// f, which euclidean.NormSmul prices at |a|, so a radius that serves f
// at ε/(|a| + 1) serves a•f at ε; the multiple of L is linear
// (vec_space.LinearScale).
var VecDerivativeScale = vecDerivativeScaleThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeScale",
	Key:  "prop_406d1133218fd7a4",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f L:((num → real) → (num → real)). ∀c:(num → real). ∀a:real.",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(λx:(num → real). a • f(x), c, λu:(num → real). a • L(u))",
	},
		func(
			arg *Argument,
			n, m *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			a *Expr[Real],
			derivative Fact,
		) {
			byF := arg.Conjuncts(
				arg.Unfolded(derivative, VecDerivativeAtDef),
				"c is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near c the error of f is within ε·‖x − c‖")
			size := real_sgn_abs.AbsNonneg.At(a)
			arg.Do(
				Unfold(VecDerivativeAtDef),
				SplitConj(
					Case(
						"c is an n-vector, and a•L is linear with values among the m-vectors",
						By(
							byF[0],
							vec_space.LinearScale.Read(real_ring.CommRing).At(L, a),
							byF[1],
							byF[2],
							vec_space.VecSmul.Read(real_ring.CommRing))),
					Case(
						"a radius that serves f at ε/(|a| + 1) serves a•f at ε",
						Derive(func(b *Argument) {
							b.FixAs[Real]("ε")
							pos := b.Assume()
							tolerance := b.TermAs[Real]("ε / (|a| + &1)")
							tolerancePos := b.Have(
								"the tolerance ε/(|a| + 1) is positive",
								"&0 < ε / (|a| + &1)",
								ByArith(pos, size))
							δ, near := b.UnpackAs[Real](GroupPremises(tolerancePos, byF[3].At(tolerance)))
							inside := b.Conjuncts(
								near,
								"the radius is positive",
								"and inside it the error of f is within ε/(|a| + 1)·‖x − c‖")
							b.Take(δ)
							b.Do(SplitConj(
								Case(
									"the radius is positive",
									By(inside[0])),
								Case(
									"inside it the error of a•f is a times the error of f",
									Derive(func(d *Argument) {
										x := d.VecFixAs[Real, DimN]("x")
										ball := d.Assume()
										scaled := d.Have(
											"the error of a•f is a times the error of f",
											"a • f(x) - a • f(c) - a • L(x - c) = a • (f(x) - f(c) - L(x - c))",
											Funext(),
											Unfold(vec_space.VecSubDef),
											Unfold(vec_space.VecScalarMulDef),
											ByArith())
										unit := d.Have(
											"|a| + 1 times the tolerance at x is ε·‖x − c‖",
											"(|a| + &1) * (ε / (|a| + &1) * ‖x - c‖_n) = ε * ‖x - c‖_n",
											ByArith(size))
										errF := d.VecAs[Real, DimM]("f(x) - f(c) - L(x - c)")
										d.Show(
											"its norm is |a| times that of the error of f, at most |a|·ε/(|a| + 1)·‖x − c‖",
											scaled.Rw(),
											ByArith(
												inside[1].At(x),
												ball,
												unit,
												euclidean.NormSmul.At(a, errF),
												size,
												euclidean.NormNonneg.At(errF)))
									})),
							))
						}))))
		}),
})}

// VecDerivativeNeg — the derivative of −f is −L: a negation is the
// multiple by −1, and the scaling rule applies at −1.
var VecDerivativeNeg = vecDerivativeNegThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeNeg",
	Key:  "prop_c78a14580f96d58a",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f L:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(λx:(num → real). -f(x), c, λu:(num → real). -L(u))",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			derivative Fact,
		) {
			a.Show(
				"a negation is the multiple by −1, and the scaling rule applies at −1",
				Simp(Fwd(vec_space.NegIsSmul.Read(real_ring.CommRing))),
				By(derivative, VecDerivativeScale.At(f, L, c, a.TermAs[Real]("-&1"))))
		}),
})}

// VecDerivativeSub — the derivative of f − g is L − K: a difference is
// the sum with the negation, and the sum rule applies to f and −g.
var VecDerivativeSub = vecDerivativeSubThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeSub",
	Key:  "prop_ed10fe730cfc24e3",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f g L K:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
			"vec_derivative_at⟨n, m⟩(g, c, K)",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(λx:(num → real). f(x) - g(x), " +
			"    c, " +
			"    λu:(num → real). L(u) - K(u))",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, g, L, K *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			ofF, ofG Fact,
		) {
			negG := a.VecFunAs[Real, DimN, DimM]("λx:(num → real). -g(x)")
			negK := a.VecFunAs[Real, DimN, DimM]("λu:(num → real). -K(u)")
			a.Show(
				"a difference is the sum with the negation, and the sum rule applies to f and −g",
				Simp(Fwd(vec_space.SubAddNeg.Read(real_ring.CommRing))),
				By(ofF, VecDerivativeNeg.At(g, K, c), ofG, VecDerivativeAdd.At(f, negG, L, negK, c)))
		}),
})}

// VecDerivativeLocal — the derivative is local: a map that agrees with g
// on a ball about c has g's derivative at c. The centre lies in the ball,
// so f(c) = g(c); inside the smaller of the ball's radius and a radius
// that serves g at ε, f's increment is g's, and so is its error.
var VecDerivativeLocal = vecDerivativeLocalThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeLocal",
	Key:  "prop_8614c1ab424e9605",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f g L:((num → real) → (num → real)). ∀c:(num → real). ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n < r ⇒ f(x) = g(x)",
			"vec_derivative_at⟨n, m⟩(g, c, L)",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(f, c, L)",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, g, L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			r *Expr[Real],
			positive, agree, derivative Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(derivative, VecDerivativeAtDef),
				"c is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near c the error of g is within ε·‖x − c‖")
			point, linear, values, near := parts[0], parts[1], parts[2], parts[3]
			centre := a.Have(
				"the centre is at distance zero from itself",
				"‖c - c‖_n = &0",
				By(Normalized, vec_space.SubEqZero.Read(real_ring.CommRing).At(c, c), euclidean.NormVecZero.At(n)))
			atCentre := a.Have(
				"so the centre lies in the ball, and f(c) = g(c)",
				"f(c) = g(c)",
				ByArith(agree.At(c), centre, positive, point))
			a.Do(
				Unfold(VecDerivativeAtDef),
				SplitConj(
					Case(
						"c is an n-vector, and L is linear with values among the m-vectors",
						By(point, linear, values)),
					Case(
						"inside the smaller of g's radius and r, f's increment is g's",
						Derive(func(b *Argument) {
							ε := b.FixAs[Real]("ε")
							pos := b.Assume()
							δ, radius := b.UnpackAs[Real](GroupPremises(pos, near.At(ε)), "δ")
							inside := b.Conjuncts(
								radius,
								"the radius is positive",
								"and inside it g's error is within ε·‖x − c‖")
							b.Take(b.TermAs[Real]("min(δ, r)"))
							b.Do(SplitConj(
								Case(
									"the smaller radius is positive",
									By(inside[0], positive, real_sup_inf.LessThanMin.At(δ, r, b.TermAs[Real]("&0")))),
								Case(
									"inside it f agrees with g, at the centre too, so g's bound is f's",
									Derive(func(d *Argument) {
										x := d.VecFixAs[Real, DimN]("x")
										ball := d.Assume()
										d.Show(
											"x is within δ and within r of c",
											By(
												ball,
												agree.At(x),
												inside[1].At(x),
												atCentre,
												real_sup_inf.LessThanMin.At(δ, r, d.TermAs[Real]("‖x - c‖_n"))))
									})),
							))
						}))))
		}),
})}

// VecDerivativeTangent — a map whose increments agree with g's to first
// order at c has g's derivative there. The error of f is the error of g
// plus the difference of the two increments; inside the smaller of the
// radii that serve g's derivative and the agreement at ε/2, the triangle
// inequality keeps it within ε·‖x − c‖.
var VecDerivativeTangent = vecDerivativeTangentThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeTangent",
	Key:  "prop_902568f8ca94a6dc",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f g L:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(g, c, L)",
			"∀ε:real. " +
				"    &0 < ε ⇒ " +
				"    ∃δ:real. " +
				"        &0 < δ ∧ " +
				"        ∀x:(num → real). " +
				"            vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ ‖f(x) - f(c) - (g(x) - g(c))‖_m ≤ ε * ‖x - c‖_n",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(f, c, L)",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, g, L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			ofG, tangent Fact,
		) {
			byG := a.Conjuncts(
				a.Unfolded(ofG, VecDerivativeAtDef),
				"c is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near c the error of g is within ε·‖x − c‖")
			a.Do(
				Unfold(VecDerivativeAtDef),
				SplitConj(
					Case(
						"c is an n-vector, and L is linear with values among the m-vectors",
						By(byG[0], byG[1], byG[2])),
					Case(
						"inside both radii that serve g and the agreement at ε/2 "+
							"the two parts of the error add up to at most ε·‖x − c‖",
						Derive(func(b *Argument) {
							b.FixAs[Real]("ε")
							pos := b.Assume()
							half := b.TermAs[Real]("ε / &2")
							halfPos := b.Have(
								"the tolerance ε/2 is positive",
								"&0 < ε / &2",
								ByArith(pos))
							δ1, nearG := b.UnpackAs[Real](GroupPremises(halfPos, byG[3].At(half)), "δ₁")
							δ2, nearF := b.UnpackAs[Real](GroupPremises(halfPos, tangent.At(half)), "δ₂")
							insideG := b.Conjuncts(
								nearG,
								"δ₁ is positive",
								"and inside it the error of g is within ε/2·‖x − c‖")
							insideF := b.Conjuncts(
								nearF,
								"δ₂ is positive",
								"and inside it the increments of f and g differ by at most ε/2·‖x − c‖")
							b.Take(b.TermAs[Real]("min(δ₁, δ₂)"))
							b.Do(SplitConj(
								Case(
									"the smaller radius is positive",
									By(insideG[0], insideF[0], real_sup_inf.LessThanMin.At(δ1, δ2, b.TermAs[Real]("&0")))),
								Case(
									"inside it the error of f is the difference of the increments plus the error of g",
									Derive(func(d *Argument) {
										x := d.VecFixAs[Real, DimN]("x")
										ball := d.Assume()
										split := d.Have(
											"the error of f is the difference of the increments plus the error of g",
											"f(x) - f(c) - L(x - c) = f(x) - f(c) - (g(x) - g(c)) + (g(x) - g(c) - L(x - c))",
											Funext(),
											Unfold(vec_space.VecAddDef),
											Unfold(vec_space.VecSubDef),
											ByArith())
										d.Show(
											"each part is at most ε/2·‖x − c‖, and the norm of a sum is at most the sum of the norms",
											split.Rw(),
											ByArith(
												insideF[1].At(x),
												insideG[1].At(x),
												ball,
												real_sup_inf.LessThanMin.At(δ1, δ2, d.TermAs[Real]("‖x - c‖_n")),
												euclidean.NormTriangle.At(
													d.VecAs[Real, DimM]("f(x) - f(c) - (g(x) - g(c))"),
													d.VecAs[Real, DimM]("g(x) - g(c) - L(x - c)"))))
									})),
							))
						}))))
		}),
})}

// VecDerivativeChain — the chain rule: when f has derivative L at c, g
// has derivative K at f(c), and f carries the n-vectors within some radius
// r of c to m-vectors, the composite g ∘ f has derivative K ∘ L at c. Its
// error at x splits as the error of g at f(x) plus K applied to the error
// of f, K being linear (vec_space.LinearSub). Near c, f(x) is near f(c)
// (VecDerivativeContinuous) and ‖f(x) − f(c)‖ is at most
// (‖L‖ + 1)·‖x − c‖, ‖L‖ the operator norm (VecDerivativeIncrementBound),
// so the first part is at most ε/2·‖x − c‖ once the error of g is within
// ε/2/(‖L‖ + 1); K stretches the error of f by at most its operator norm
// ‖K‖ (euclidean.OpNormBound), at most ε/2·‖x − c‖ once that error is
// within ε/2/(‖K‖ + 1).
var VecDerivativeChain = vecDerivativeChainThm{family.Add(registry.ProofEntry{
	Name: "VecDerivativeChain",
	Key:  "prop_d57111ba33f3fe1",
	Build: family.Theorem(Statement{
		Binders: "∀n m k:num. ∀f g L K:((num → real) → (num → real)). ∀c:(num → real). ∀r:real.",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
			"vec_derivative_at⟨m, k⟩(g, f(c), K)",
			"&0 < r",
			"∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n < r ⇒ vec⟨m⟩(f(x))",
		},
		Conclusion: "vec_derivative_at⟨n, k⟩(g ∘ f, c, K ∘ L)",
	},
		func(
			a *Argument,
			n, m, k *Expr[Nat],
			f *VecFun[Real, DimN, DimM],
			g *VecFun[Real, DimM, DimK],
			L *VecFun[Real, DimN, DimM],
			K *VecFun[Real, DimM, DimK],
			c *Vec[Real, DimN],
			r *Expr[Real],
			ofF, ofG, rPos, maps Fact,
		) {
			byF := a.Conjuncts(
				a.Unfolded(ofF, VecDerivativeAtDef),
				"c is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near c the error of f is within ε·‖x − c‖")
			byG := a.Conjuncts(
				a.Unfolded(ofG, VecDerivativeAtDef),
				"f(c) is an m-vector",
				"K is linear",
				"K takes the m-vectors to k-vectors",
				"and near f(c) the error of g is within ε·‖y − f(c)‖")
			sizeL := a.Have(
				"the operator norm of L is not negative",
				"&0 ≤ vec_op_norm⟨n, m⟩(L)",
				By(byF[1], euclidean.OpNormNonneg.At(L)))
			sizeK := a.Have(
				"and neither is that of K",
				"&0 ≤ vec_op_norm⟨m, k⟩(K)",
				By(byG[1], euclidean.OpNormNonneg.At(K)))
			δ1, growth := a.UnpackAs[Real](
				GroupPremises(ofF, VecDerivativeIncrementBound.At(f, L, c)),
				"δ₁")
			nearGrowth := a.Conjuncts(
				growth,
				"δ₁ is positive",
				"and inside it the increment of f is at most (‖L‖ + 1)·‖x − c‖")
			continuous := a.Conjuncts(
				a.Unfolded(GroupPremises(ofF, VecDerivativeContinuous.At(f, L, c)), VecContinuousAtDef),
				"c is an n-vector",
				"and near c, f(x) is near f(c)")[1]
			condition := a.Have(
				"near c the error of g ∘ f is within ε·‖x − c‖",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀x:(num → real). " +
						"        vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ ‖(g ∘ f)(x) - (g ∘ f)(c) - (K ∘ L)(x - c)‖_k ≤ ε * ‖x - c‖_n)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Real]("ε")
					pos := b.Assume()
					posG := b.Have(
						"the tolerance ε/2/(‖L‖ + 1) is positive",
						"&0 < ε / &2 / (vec_op_norm⟨n, m⟩(L) + &1)",
						ByArith(pos, sizeL))
					posF := b.Have(
						"and so is ε/2/(‖K‖ + 1)",
						"&0 < ε / &2 / (vec_op_norm⟨m, k⟩(K) + &1)",
						ByArith(pos, sizeK))
					ρ, radiusG := b.UnpackAs[Real](
						GroupPremises(posG, byG[3].At(b.TermAs[Real]("ε / &2 / (vec_op_norm⟨n, m⟩(L) + &1)"))),
						"ρ")
					insideG := b.Conjuncts(
						radiusG,
						"ρ is positive",
						"and inside it the error of g is within ε/2/(‖L‖ + 1) times the distance")
					δ2, continuity := b.UnpackAs[Real](GroupPremises(insideG[0], continuous.At(ρ)), "δ₂")
					nearContinuity := b.Conjuncts(
						continuity,
						"δ₂ is positive",
						"and inside it f(x) is within ρ of f(c)")
					δ3, radiusF := b.UnpackAs[Real](
						GroupPremises(posF, byF[3].At(b.TermAs[Real]("ε / &2 / (vec_op_norm⟨m, k⟩(K) + &1)"))),
						"δ₃")
					insideF := b.Conjuncts(
						radiusF,
						"δ₃ is positive",
						"and inside it the error of f is within ε/2/(‖K‖ + 1)·‖x − c‖")
					outer := b.TermAs[Real]("min(δ₁, r)")
					inner := b.TermAs[Real]("min(δ₂, δ₃)")
					zero := b.TermAs[Real]("&0")
					b.Take(b.TermAs[Real]("min(min(δ₁, r), min(δ₂, δ₃))"))
					b.Do(SplitConj(
						Case(
							"the smallest of the four radii is positive",
							By(
								nearGrowth[0],
								rPos,
								nearContinuity[0],
								insideF[0],
								real_sup_inf.LessThanMin.At(outer, inner, zero),
								real_sup_inf.LessThanMin.At(δ1, r, zero),
								real_sup_inf.LessThanMin.At(δ2, δ3, zero))),
						Case(
							"inside it the error of g ∘ f is the error of g at f(x) plus K of the error of f",
							Derive(func(d *Argument) {
								x := d.VecFixAs[Real, DimN]("x")
								ball := d.Assume()
								member := d.Conjuncts(
									ball,
									"x is an n-vector",
									"within the smallest radius of c")[0]
								distance := d.TermAs[Real]("‖x - c‖_n")
								within := d.Have(
									"so x is within δ₁, r, δ₂ and δ₃ of c",
									"‖x - c‖_n < δ₁ ∧ ‖x - c‖_n < r ∧ ‖x - c‖_n < δ₂ ∧ ‖x - c‖_n < δ₃",
									By(
										ball,
										real_sup_inf.LessThanMin.At(outer, inner, distance),
										real_sup_inf.LessThanMin.At(δ1, r, distance),
										real_sup_inf.LessThanMin.At(δ2, δ3, distance)))
								value := f.Apply(x)
								valueIn := d.Have(
									"f(x) is an m-vector, x lying within r of c",
									"vec⟨m⟩(f(x))",
									By(maps.At(x), member, within))
								firstBound := d.Have(
									"the error of g at f(x) is at most ε/2·‖x − c‖",
									"‖g(f(x)) - g(f(c)) - K(f(x) - f(c))‖_k ≤ ε / &2 * ‖x - c‖_n",
									Derive(func(e *Argument) {
										errorG := e.Have(
											"f(x) is within ρ of f(c), so the error of g there is within ε/2/(‖L‖ + 1)·‖f(x) − f(c)‖",
											"‖g(f(x)) - g(f(c)) - K(f(x) - f(c))‖_k ≤ ε / &2 / (vec_op_norm⟨n, m⟩(L) + &1) * ‖f(x) - f(c)‖_m",
											By(insideG[1].At(value), valueIn, nearContinuity[1].At(x), member, within))
										unitG := e.Have(
											"‖L‖ + 1 times the tolerance of g is ε/2",
											"(vec_op_norm⟨n, m⟩(L) + &1) * (ε / &2 / (vec_op_norm⟨n, m⟩(L) + &1) * ‖x - c‖_n) = "+
												"ε / &2 * ‖x - c‖_n",
											ByArith(sizeL))
										e.Show(
											"and ‖f(x) − f(c)‖ is at most (‖L‖ + 1)·‖x − c‖",
											ByArith(errorG, nearGrowth[1].At(x), member, within, posG, sizeL, unitG))
									}))
								step := d.VecAs[Real, DimN]("x - c")
								rise := d.VecAs[Real, DimM]("f(x) - f(c)")
								linearPart := d.VecAs[Real, DimM]("L(x - c)")
								secondBound := d.Have(
									"K of the error of f is at most ε/2·‖x − c‖",
									"‖K(f(x) - f(c) - L(x - c))‖_k ≤ ε / &2 * ‖x - c‖_n",
									Derive(func(e *Argument) {
										stepIn := e.Have(
											"x − c is an n-vector",
											"vec⟨n⟩(x - c)",
											By(vec_space.VecSub.Read(real_ring.CommRing).At(
												proof.Inhabit(x, member), proof.Inhabit(c, byF[0]))))
										riseIn := e.Have(
											"f(x) − f(c) is an m-vector",
											"vec⟨m⟩(f(x) - f(c))",
											By(vec_space.VecSub.Read(real_ring.CommRing).At(
												proof.Inhabit(value, valueIn), proof.Inhabit(f.Apply(c), byG[0]))))
										linearPartIn := e.Have(
											"and so is L(x − c)",
											"vec⟨m⟩(L(x - c))",
											By(byF[2].At(step), stepIn))
										errorF := e.VecAs[Real, DimM]("f(x) - f(c) - L(x - c)")
										errorFIn := e.Have(
											"so the error of f at x is an m-vector",
											"vec⟨m⟩(f(x) - f(c) - L(x - c))",
											By(vec_space.VecSub.Read(real_ring.CommRing).At(
												proof.Inhabit(rise, riseIn), proof.Inhabit(linearPart, linearPartIn))))
										unitF := e.Have(
											"‖K‖ + 1 times the tolerance of f is ε/2",
											"(vec_op_norm⟨m, k⟩(K) + &1) * (ε / &2 / (vec_op_norm⟨m, k⟩(K) + &1) * ‖x - c‖_n) = "+
												"ε / &2 * ‖x - c‖_n",
											ByArith(sizeK))
										e.Show(
											"K stretches the error of f by at most ‖K‖, and that error is within ε/2/(‖K‖ + 1)·‖x − c‖",
											ByArith(
												euclidean.OpNormBound.At(K, proof.Inhabit(errorF, errorFIn)),
												byG[1],
												insideF[1].At(x),
												member,
												within,
												sizeK,
												posF,
												euclidean.NormNonneg.At(step),
												unitF))
									}))
								difference := d.Have(
									"K, being linear, carries the error of f to K(f(x) − f(c)) less K(L(x − c))",
									"K(f(x) - f(c) - L(x - c)) = K(f(x) - f(c)) - K(L(x - c))",
									By(byG[1], vec_space.LinearSub.Read(real_ring.CommRing).At(K, rise, linearPart)))
								split := d.Have(
									"so the error of g ∘ f is the error of g at f(x) plus K of the error of f",
									"g(f(x)) - g(f(c)) - K(L(x - c)) = g(f(x)) - g(f(c)) - K(f(x) - f(c)) + K(f(x) - f(c) - L(x - c))",
									difference.Rw(),
									Funext(),
									Unfold(vec_space.VecAddDef),
									Unfold(vec_space.VecSubDef),
									ByArith())
								d.Show(
									"the norm of the sum is at most the sum of the norms, each at most ε/2·‖x − c‖",
									Unfold(functions.ComposeApply),
									split.Rw(),
									ByArith(
										euclidean.NormTriangle.At(
											d.VecAs[Real, DimK]("g(f(x)) - g(f(c)) - K(f(x) - f(c))"),
											d.VecAs[Real, DimK]("K(f(x) - f(c) - L(x - c))")),
										firstBound,
										secondBound))
							})),
					))
				}))
			values := a.Have(
				"K ∘ L carries the n-vectors to k-vectors",
				"∀u:(num → real). vec⟨n⟩(u) ⇒ vec⟨k⟩((K ∘ L)(u))",
				Unfold(functions.ComposeApply),
				By(byF[2], byG[2]))
			a.Do(
				Unfold(VecDerivativeAtDef),
				SplitConj(
					Case(
						"c is an n-vector, and K ∘ L is linear and carries the n-vectors to k-vectors",
						By(byF[0], vec_space.LinearCompose.Read(real_ring.CommRing).At(L, K), byF[1], byG[1], values)),
					Case(
						"and near c the error of g ∘ f is within ε·‖x − c‖",
						By(condition))))
		}),
})}

// DerivativeAlongLine — along the line through x in the direction w, each
// coordinate of f is a real function of the parameter, and its derivative
// at t₀ is that coordinate of L(w). The step from x + t₀•w to x + t•w is
// (t − t₀)•w, of norm |t − t₀|·‖w‖, and L carries it to (t − t₀)•L(w); a
// coordinate below m is at most the norm (euclidean.ComponentLeNorm). So
// inside the radius that serves f at ε/(‖w‖ + 1), the coordinate's error
// is at most ε/(‖w‖ + 1)·|t − t₀|·‖w‖, below ε·|t − t₀| — the increment
// form of a real derivative (real_derivative.DerivativeIncrement).
var DerivativeAlongLine = derivativeAlongLineThm{family.Add(registry.ProofEntry{
	Name: "DerivativeAlongLine",
	Key:  "prop_19577050bec4e224",
	Build: family.Theorem(Statement{
		Binders: "∀n m i:num. ∀f L:((num → real) → (num → real)). ∀x w:(num → real). ∀t₀:real.",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, x + t₀ • w, L)",
			"vec⟨n⟩(x)",
			"vec⟨n⟩(w)",
			"i < m",
		},
		Conclusion: "real_derivative_at(λt:real. f(x + t • w)(i), t₀, L(w)(i))",
	},
		func(
			a *Argument,
			n, m, i *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			x, w *Vec[Real, DimN],
			t0 *Expr[Real],
			derivative, xIn, wIn, coordinate Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(derivative, VecDerivativeAtDef),
				"x + t₀•w is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near x + t₀•w the error is within ε times the distance")
			homogeneous := a.Conjuncts(
				a.Unfolded(parts[1], vec_space.VecLinearDef),
				"L carries a sum to the sum of the images",
				"and commutes with scaling")[1]
			size := euclidean.NormNonneg.At(w)
			a.Show(
				"in the increment form of a real derivative: each ε > 0 has a radius "+
					"about t₀ within which the coordinate's error is below ε·|t − t₀|",
				Simp(Fwd(real_derivative.DerivativeIncrement)),
				Derive(func(d *Argument) {
					d.FixAs[Real]("ε")
					pos := d.Assume()
					tolerance := d.TermAs[Real]("ε / (‖w‖_n + &1)")
					tolerancePos := d.Have(
						"the tolerance ε/(‖w‖ + 1) is positive",
						"&0 < ε / (‖w‖_n + &1)",
						ByArith(pos, size))
					δ, radius := d.UnpackAs[Real](GroupPremises(tolerancePos, parts[3].At(tolerance)), "δ")
					inside := d.Conjuncts(
						radius,
						"the radius is positive",
						"and inside it the error is within ε/(‖w‖ + 1) times the distance")
					widened := d.TermAs[Real]("‖w‖_n + &1")
					d.Take(d.TermAs[Real]("δ / (‖w‖_n + &1)"))
					d.Do(SplitConj(
						Case(
							"the radius δ/(‖w‖ + 1) in the parameter is positive",
							ByArith(inside[0], size)),
						Case(
							"within it of t₀, x + t•w lies within δ of x + t₀•w, "+
								"and a coordinate of the error is at most its norm",
							Derive(func(b *Argument) {
								b.FixAs[Real]("t")
								near := b.Assume()
								gap := b.TermAs[Real]("|t - t₀|")
								point := b.VecAs[Real, DimN]("x + t • w")
								pointIn := b.Have(
									"x + t•w is an n-vector",
									"vec⟨n⟩(x + t • w)",
									By(xIn, wIn, vec_space.VecAdd.Read(real_ring.CommRing), vec_space.VecSmul.Read(real_ring.CommRing)))
								step := b.Have(
									"the step from x + t₀•w to x + t•w is (t − t₀)•w",
									"x + t • w - (x + t₀ • w) = (t - t₀) • w",
									Funext(),
									Unfold(vec_space.VecAddDef),
									Unfold(vec_space.VecSubDef),
									Unfold(vec_space.VecScalarMulDef),
									ByArith())
								distance := b.Have(
									"so its norm is |t − t₀|·‖w‖",
									"‖x + t • w - (x + t₀ • w)‖_n = |t - t₀| * ‖w‖_n",
									By(step, euclidean.NormSmul.At(b.TermAs[Real]("t - t₀"), w)))
								inBall := b.Have(
									"which is below δ, |t − t₀| being below δ/(‖w‖ + 1)",
									"‖x + t • w - (x + t₀ • w)‖_n < δ",
									ByArith(distance, near, real_order_field.LessThanDivMulLeft.At(gap, δ, widened), size))
								errorBound := b.Have(
									"there the error is within ε/(‖w‖ + 1)·|t − t₀|·‖w‖",
									"‖f(x + t • w) - f(x + t₀ • w) - L(x + t • w - (x + t₀ • w))‖_m ≤ "+
										"ε / (‖w‖_n + &1) * (|t - t₀| * ‖w‖_n)",
									distance.RwRev(),
									By(inside[1].At(point), pointIn, inBall))
								coordinateValue := b.Have(
									"its i-th coordinate is the increment of the coordinate along the line, less L(w)(i)·(t − t₀)",
									"(f(x + t • w) - f(x + t₀ • w) - L(x + t • w - (x + t₀ • w)))(i) = "+
										"f(x + t • w)(i) - f(x + t₀ • w)(i) - L(w)(i) * (t - t₀)",
									step.Rw(),
									homogeneous.At(b.TermAs[Real]("t - t₀"), w).Rw(),
									Unfold(vec_space.VecSubDef),
									Unfold(vec_space.VecScalarMulDef),
									ByArith())
								coordinateBound := b.Have(
									"and a coordinate below m is at most the norm",
									"|f(x + t • w)(i) - f(x + t₀ • w)(i) - L(w)(i) * (t - t₀)| ≤ "+
										"‖f(x + t • w) - f(x + t₀ • w) - L(x + t • w - (x + t₀ • w))‖_m",
									By(
										coordinate,
										coordinateValue,
										euclidean.ComponentLeNorm.At(
											i,
											b.VecAs[Real, DimM]("f(x + t • w) - f(x + t₀ • w) - L(x + t • w - (x + t₀ • w))"))))
								scaled := b.Have(
									"‖w‖ + 1 times the tolerance is ε",
									"(‖w‖_n + &1) * (ε / (‖w‖_n + &1) * |t - t₀|) = ε * |t - t₀|",
									ByArith(size))
								b.Show(
									"so the coordinate's error is below ε·|t − t₀|",
									ByArith(scaled, coordinateBound, errorBound, tolerancePos, near))
							})),
					))
				}))
		}),
})}

// DirectionalDerivative — the derivative of f at c, read along the line
// through c in the direction w: each coordinate of t ↦ f(c + t•w) has
// derivative at 0 the coordinate of L(w). The line passes c at 0, so
// this is DerivativeAlongLine at t₀ = 0.
var DirectionalDerivative = directionalDerivativeThm{family.Add(registry.ProofEntry{
	Name: "DirectionalDerivative",
	Key:  "prop_8091e4c044e7eba2",
	Build: family.Theorem(Statement{
		Binders: "∀n m i:num. ∀f L:((num → real) → (num → real)). ∀c w:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
			"vec⟨n⟩(w)",
			"i < m",
		},
		Conclusion: "real_derivative_at(λt:real. f(c + t • w)(i), &0, L(w)(i))",
	},
		func(
			a *Argument,
			n, m, i *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			c, w *Vec[Real, DimN],
			derivative, wIn, coordinate Fact,
		) {
			point := a.Have(
				"c is an n-vector",
				"vec⟨n⟩(c)",
				By(a.Unfolded(derivative, VecDerivativeAtDef)))
			start := a.Have(
				"the line through c in the direction w passes c at 0",
				"c + &0 • w = c",
				Funext(),
				Unfold(vec_space.VecAddDef),
				Unfold(vec_space.VecScalarMulDef),
				ByArith())
			atStart := a.Have(
				"so L is the derivative of f where the line is at 0",
				"vec_derivative_at⟨n, m⟩(f, c + &0 • w, L)",
				start.Rw(),
				By(derivative))
			a.Show(
				"and the derivative along the line at 0 is the coordinate of L(w)",
				By(
					atStart,
					coordinate,
					DerivativeAlongLine.At(
						i, f, L, proof.Inhabit(c, point), proof.Inhabit(w, wIn), a.TermAs[Real]("&0"))))
		}),
})}

// DotDerivativeAlongLine — along the line through x in the direction w,
// the component of f against a fixed sequence u, t ↦ ⟪u, f(x + t•w)⟫_m,
// has derivative ⟪u, L(w)⟫_m at t₀. The form is the sum over i < m of
// u(i)·f(x + t•w)(i), and the i-th summand is u(i) times a coordinate
// whose derivative is L(w)(i) (DerivativeAlongLine). The sum of the first
// k summands is differentiated term by term, by induction on k: the
// empty sum is the constant 0, and one more term adds its derivative
// (real_derivative.DerivativeAdd).
var DotDerivativeAlongLine = dotDerivativeAlongLineThm{family.Add(registry.ProofEntry{
	Name: "DotDerivativeAlongLine",
	Key:  "prop_3d4ae58bdce83ef9",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f L:((num → real) → (num → real)). ∀u x w:(num → real). ∀t₀:real.",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, x + t₀ • w, L)",
			"vec⟨n⟩(x)",
			"vec⟨n⟩(w)",
		},
		Conclusion: "real_derivative_at(λt:real. ⟪u, f(x + t • w)⟫_m, t₀, ⟪u, L(w)⟫_m)",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			u *Vec[Real, DimM],
			x, w *Vec[Real, DimN],
			t0 *Expr[Real],
			derivative, xIn, wIn Fact,
		) {
			partial := a.Have(
				"the sum of the first k terms of the form has the sum "+
					"of the first k terms of ⟪u, L(w)⟫ as its derivative",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"k ≤ m",
					},
					Conclusion: "real_derivative_at(λt:real. Σ_{i<k} u(i) * f(x + t • w)(i), " +
						"    t₀, " +
						"    Σ_{i<k} u(i) * L(w)(i))",
				},
				Derive(func(b *Argument) {
					b.Induct("k")
					b.Base(
						"with no terms the sum is the constant 0, whose derivative is 0",
						Simp(Fwd(real_sum.BelowClauses)),
						By(real_derivative.DerivativeConst))
					b.Step(
						"the sum to k + 1 adds u(k) times the k-th coordinate "+
							"along the line, and its derivative u(k)·L(w)(k)",
						func(d *Argument, ih Fact) {
							within := d.Assume()
							d.Do(Simp(Fwd(real_sum.BelowClauses)))
							k := d.TermAs[Nat]("k")
							below := d.Have(
								"k lies below m",
								"k < m",
								ByArith(within))
							term := d.Have(
								"the k-th coordinate along the line has derivative L(w)(k), and u(k) times it u(k)·L(w)(k)",
								"real_derivative_at(λt:real. u(k) * f(x + t • w)(k), t₀, u(k) * L(w)(k))",
								By(
									below,
									derivative,
									DerivativeAlongLine.At(k, f, L, proof.Inhabit(x, xIn), proof.Inhabit(w, wIn), t0),
									real_derivative.DerivativeScale.At(
										d.TermAs[Fun[Real, Real]]("λt:real. f(x + t • w)(k)"),
										t0,
										d.TermAs[Real]("L(w)(k)"),
										d.TermAs[Real]("u(k)"))))
							d.Show(
								"the derivatives of the first k terms and of the k-th add up",
								By(ih, below, term, nat_order.LessEqOfLessThan.At(k, m), real_derivative.DerivativeAdd))
						})
				}))
			a.Show(
				"the form is the sum of all m terms",
				Simp(Fwd(euclidean.DotIsSum)),
				By(partial.At(m), nat_order.LessEqRefl.At(m)))
		}),
})}

// MeanValueInequality — the mean value inequality in several variables: if
// at every point of the segment from x to y the map f has a derivative
// of operator norm at most B, then ‖f(y) − f(x)‖ is at most B·‖y − x‖. Choose the derivative D(t) at each point x + t•(y − x) of the
// segment, and read f along the segment against the fixed vector
// f(y) − f(x): the real function φ(t) = ⟪f(y) − f(x), f(x + t•(y − x))⟫
// has derivative ⟪f(y) − f(x), D(t)(y − x)⟫ on ⟦0, 1⟧
// (DotDerivativeAlongLine). The mean value theorem gives z in ⟬0, 1⟭ with
// φ(1) − φ(0) equal to that derivative at z. The left side is
// ⟪f(y) − f(x), f(y) − f(x)⟫ = ‖f(y) − f(x)‖², and by Cauchy–Schwarz the
// right side is at most ‖f(y) − f(x)‖·‖D(z)(y − x)‖, the second factor at
// most ‖D(z)‖·‖y − x‖ (euclidean.OpNormBound), so at most B·‖y − x‖. Where ‖f(y) − f(x)‖ is not zero it cancels; where it is,
// the bound B·‖y − x‖ is at least ‖D(z)(y − x)‖, a norm, so not negative.
var MeanValueInequality = meanValueInequalityThm{family.Add(registry.ProofEntry{
	Name: "MeanValueInequality",
	Key:  "prop_39a7d2c0781e18bb",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. ∀f:((num → real) → (num → real)). ∀x y:(num → real). ∀B:real.",
		Hypotheses: []string{
			"vec⟨n⟩(x)",
			"vec⟨n⟩(y)",
			"∀t:real. " +
				"    &0 ≤ t ∧ t ≤ &1 ⇒ " +
				"    ∃L:((num → real) → (num → real)). " +
				"        vec_derivative_at⟨n, m⟩(f, x + t • (y - x), L) ∧ vec_op_norm⟨n, m⟩(L) ≤ B",
		},
		Conclusion: "‖f(y) - f(x)‖_m ≤ B * ‖y - x‖_n",
		Abbrev: Abbrev{
			{Name: "φ", Text: "λs:real. ⟪f(y) - f(x), f(x + s • (y - x))⟫_m"},
		},
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f *VecFun[Real, DimN, DimM],
			x, y *Vec[Real, DimN],
			B *Expr[Real],
			xIn, yIn, derivatives Fact,
		) {
			_, choice := a.Obtain(
				"a choice D(t) of the derivative, with its bound, at each point of the segment",
				"∃D:(real → ((num → real) → (num → real))). ∀t:real. "+
					"    &0 ≤ t ∧ t ≤ &1 ⇒ "+
					"    vec_derivative_at⟨n, m⟩(f, x + t • (y - x), D(t)) ∧ vec_op_norm⟨n, m⟩(D(t)) ≤ B",
				By(derivatives))
			step := a.VecAs[Real, DimN]("y - x")
			stepIn := a.Have(
				"the step y − x is an n-vector",
				"vec⟨n⟩(y - x)",
				By(vec_space.VecSub.Read(real_ring.CommRing).At(proof.Inhabit(y, yIn), proof.Inhabit(x, xIn))))
			increment := a.VecAs[Real, DimM]("f(y) - f(x)")
			slope := a.TermAs[Fun[Real, Real]]("λt:real. ⟪f(y) - f(x), D(t)(y - x)⟫_m")
			phi := a.TermAs[Fun[Real, Real]]("«φ»")
			along := a.Have(
				"at each t of ⟦0, 1⟧, φ has derivative ⟪f(y) − f(x), D(t)(y − x)⟫",
				"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ real_derivative_at(«φ», t, ⟪f(y) - f(x), D(t)(y - x)⟫_m)",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]()
					inside := b.Assume()
					b.Show(
						"D(t) is the derivative of f at x + t•(y − x), read along the segment against f(y) − f(x)",
						By(
							choice.At(t),
							inside,
							DotDerivativeAlongLine.At(
								f,
								b.VecFunAs[Real, DimN, DimM]("D(t)"),
								increment,
								proof.Inhabit(x, xIn),
								proof.Inhabit(step, stepIn),
								t)))
				}))
			z, atZ := a.ObtainAs[Real](
				"the mean value theorem for φ, continuous on ⟦0, 1⟧ as it has "+
					"derivatives there: some z in ⟬0, 1⟭ where φ'(z) is the chord's slope",
				"∃z:real. &0 < z ∧ z < &1 ∧ «φ»(&1) - «φ»(&0) = ⟪f(y) - f(x), D(z)(y - x)⟫_m * (&1 - &0)",
				By(
					along,
					real_derivative.DerivativeContinuousOn.At(phi, slope, a.TermAs[Set[Real]]("⟦&0, &1⟧")),
					real_derivative.MeanValue.At(phi, slope, a.TermAs[Real]("&0"), a.TermAs[Real]("&1")),
					real_order_ring.ZeroLessThanOne,
					real_order_ring.LessEqOfLessThan))
			mean := a.Conjuncts(
				atZ,
				"z lies above 0",
				"and below 1",
				"and the increment of φ over ⟦0, 1⟧ is its derivative at z")
			stretch := a.VecFunAs[Real, DimN, DimM]("D(z)")
			inSegment := a.Have(
				"z lies in ⟦0, 1⟧",
				"&0 ≤ z ∧ z ≤ &1",
				By(
					mean[0],
					mean[1],
					real_order_ring.LessEqOfLessThan.At(a.TermAs[Real]("&0"), z),
					real_order_ring.LessEqOfLessThan.At(z, a.TermAs[Real]("&1"))))
			derivativeAtZ := a.Conjuncts(
				GroupPremises(inSegment, choice.At(z)),
				"D(z) is the derivative of f at the point of the segment at z",
				"and its operator norm is at most B")
			linear := a.Conjuncts(
				a.Unfolded(derivativeAtZ[0], VecDerivativeAtDef),
				"the point is an n-vector",
				"D(z) is linear",
				"D(z) takes the n-vectors to m-vectors",
				"and near the point the error is within ε times the distance")[1]
			bound := a.Have(
				"D(z) stretches y − x by at most its operator norm, at most B",
				"‖D(z)(y - x)‖_m ≤ B * ‖y - x‖_n",
				ByArith(
					euclidean.OpNormBound.At(stretch, proof.Inhabit(step, stepIn)),
					linear,
					derivativeAtZ[1],
					euclidean.NormNonneg.At(step),
					real_order_ring.LessEqMulRight.At(
						a.TermAs[Real]("vec_op_norm⟨n, m⟩(D(z))"), B, a.TermAs[Real]("‖y - x‖_n"))))
			atOne := a.Have(
				"the segment reaches y at 1",
				"x + &1 • (y - x) = y",
				Funext(),
				Unfold(vec_space.VecAddDef),
				Unfold(vec_space.VecSubDef),
				Unfold(vec_space.VecScalarMulDef),
				ByArith())
			atZero := a.Have(
				"and starts at x at 0",
				"x + &0 • (y - x) = x",
				Funext(),
				Unfold(vec_space.VecAddDef),
				Unfold(vec_space.VecScalarMulDef),
				ByArith())
			normSquared := a.Have(
				"so φ(1) − φ(0) is ⟪f(y) − f(x), f(y) − f(x)⟫, the squared norm of f(y) − f(x)",
				"«φ»(&1) - «φ»(&0) = ‖f(y) - f(x)‖_m ^ 2",
				atOne.Rw(),
				atZero.Rw(),
				By(
					dot.SubRight.Read(real_ring.CommRing).At(increment, f.Apply(y), f.Apply(x)),
					euclidean.NormPow2.At(increment)))
			product := a.Have(
				"by Cauchy–Schwarz the squared norm is at most ‖f(y) − f(x)‖·‖D(z)(y − x)‖",
				"‖f(y) - f(x)‖_m ^ 2 ≤ ‖f(y) - f(x)‖_m * ‖D(z)(y - x)‖_m",
				ByArith(normSquared, mean[2], euclidean.CauchySchwarz.At(increment, stretch.Apply(step))))
			a.Cases(a.Term("‖f(y) - f(x)‖_m = &0"))
			a.When(
				"‖f(y) − f(x)‖ = 0: the bound B·‖y − x‖ is at least the norm ‖D(z)(y − x)‖, so not negative",
				func(b *Argument, zero Fact) {
					b.Show(
						"0 ≤ ‖D(z)(y − x)‖ ≤ B·‖y − x‖",
						ByArith(zero, bound, euclidean.NormNonneg.At(stretch.Apply(step))))
				})
			a.Otherwise(
				"‖f(y) − f(x)‖ is positive and cancels: ‖f(y) − f(x)‖ ≤ ‖D(z)(y − x)‖ ≤ B·‖y − x‖",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"cancel the positive factor ‖f(y) − f(x)‖",
						ByArith(nonzero, product, bound, euclidean.NormNonneg.At(increment)))
				})
		}),
})}
