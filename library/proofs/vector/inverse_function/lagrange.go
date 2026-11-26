// lagrange.go — Lagrange multipliers, by the chain rule along the graph of the implicit function.

package inverse_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_derivative"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// GraphDerivativeAlongLine — the chain rule for a real function of two
// blocks read on the graph of a map: when f has at (a, b) the gradients p
// and q, and g, with g(a) = b, carries the n-vectors near a to m-vectors
// and has the derivative L there, then t ↦ f(a + t•u, g(a + t•u)) has the
// derivative ⟪p, u⟫ + ⟪q, L(u)⟫ at 0. Near a, the increment of f at
// (x, g(x)) is ⟪p, x − a⟫ + ⟪q, g(x) − b⟫ to within η(‖x − a‖ + ‖g(x) − b‖),
// g(x) − b is L(x − a) to within η‖x − a‖, and ‖g(x) − b‖ is at most
// (‖L‖ + 1)‖x − a‖ with ‖L‖ the operator norm; with η = ε/(2 + ‖L‖ + ‖q‖)
// the errors add up to at most ε‖x − a‖. Along the line x − a is t•u,
// and L(t•u) = t•L(u).
var GraphDerivativeAlongLine = graphDerivativeAlongLineThm{family.Add(registry.ProofEntry{
	Name: "GraphDerivativeAlongLine",
	Key:  "prop_ebd208c6e04257f7",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. " +
			"∀f:((num → real) → (num → real) → real). " +
			"∀g L:((num → real) → (num → real)). " +
			"∀p q a b u:(num → real). " +
			"∀ρ:real.",
		Hypotheses: []string{
			"∀ε:real. " +
				"    &0 < ε ⇒ " +
				"    ∃δ:real. " +
				"        &0 < δ ∧ " +
				"        ∀x y:(num → real). " +
				"            vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < δ ∧ ‖y - b‖_m < δ ⇒ " +
				"            |f(x, y) - f(a, b) - ⟪p, x - a⟫_n - ⟪q, y - b⟫_m| ≤ ε * (‖x - a‖_n + ‖y - b‖_m)",
			"vec_derivative_at⟨n, m⟩(g, a, L)",
			"g(a) = b",
			"&0 < ρ",
			"∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - a‖_n < ρ ⇒ vec⟨m⟩(g(x))",
			"vec⟨n⟩(u)",
		},
		Conclusion: "real_derivative_at(λt:real. f(a + t • u, g(a + t • u)), &0, ⟪p, u⟫_n + ⟪q, L(u)⟫_m)",
	},
		func(arg *Argument, n, m *Expr[Nat], f *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Real],
			g, L *VecFun[Real, DimN, DimM], p *Vec[Real, DimN], q *Vec[Real, DimM], a *Vec[Real, DimN],
			b *Vec[Real, DimM], u *Vec[Real, DimN], ρ *Expr[Real],
			differentiable, ofG, gAtA, ρPos, gValues, uIn Fact) {
			byG := arg.Conjuncts(
				arg.Unfolded(ofG, vec_derivative.VecDerivativeAtDef),
				"a is an n-vector",
				"L is linear",
				"L takes the n-vectors to m-vectors",
				"and near a, g(x) − g(a) is L(x − a) to within ε‖x − a‖")
			homogeneous := arg.Conjuncts(
				arg.Unfolded(byG[1], vec_space.VecLinearDef),
				"L carries a sum to the sum of the images",
				"and commutes with scaling")[1]
			size := arg.Have(
				"the operator norm of L is not negative",
				"&0 ≤ vec_op_norm⟨n, m⟩(L)",
				By(byG[1], euclidean.OpNormNonneg.At(L)))
			qSize := euclidean.NormNonneg.At(q)
			δ0, growth := arg.UnpackAs[Real](
				GroupPremises(ofG, vec_derivative.VecDerivativeIncrementBound.At(g, L, a)),
				"δ₀")
			grows := arg.Conjuncts(
				growth,
				"δ₀ is positive",
				"and within δ₀ of a, g(x) − g(a) is at most (‖L‖ + 1)‖x − a‖")

			// Near a, f(x, g(x)) − f(a, b) is ⟪p, x − a⟫ + ⟪q, L(x − a)⟫ to first order.
			chain := arg.Have(
				"near a, the increment of f at (x, g(x)) is ⟪p, x − a⟫ + ⟪q, L(x − a)⟫ to within ε‖x − a‖",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀x:(num → real). " +
						"        vec⟨n⟩(x) ∧ ‖x - a‖_n < δ ⇒ " +
						"        |f(x, g(x)) - f(a, b) - (⟪p, x - a⟫_n + ⟪q, L(x - a)⟫_m)| ≤ ε * ‖x - a‖_n)",
				},
				Derive(func(d *Argument) {
					d.FixAs[Real]("ε")
					pos := d.Assume()
					η, ηDef := d.LetAs[Real]("η", "ε / (&2 + vec_op_norm⟨n, m⟩(L) + ‖q‖_m)")
					ηPos := d.Have(
						"the tolerance η = ε/(2 + ‖L‖ + ‖q‖) is positive",
						"&0 < η",
						ByArith(ηDef, size, pos, qSize))
					ηUnit := d.Have(
						"2 + ‖L‖ + ‖q‖ times η is ε",
						"(&2 + vec_op_norm⟨n, m⟩(L) + ‖q‖_m) * η = ε",
						ByArith(ηDef, size, qSize))
					_, nearF := d.UnpackAs[Real](GroupPremises(ηPos, differentiable.At(η)), "δ₁")
					byF := d.Conjuncts(
						nearF,
						"δ₁ is positive",
						"and within δ₁ of (a, b), f's increment is ⟪p, x − a⟫ + ⟪q, y − b⟫ to within η(‖x − a‖ + ‖y − b‖)")
					δ2, nearG := d.UnpackAs[Real](GroupPremises(ηPos, byG[3].At(η)), "δ₂")
					byL := d.Conjuncts(
						nearG,
						"δ₂ is positive",
						"and within δ₂ of a, g(x) − g(a) is L(x − a) to within η‖x − a‖")
					θ, θDef := d.LetAs[Real]("θ", "δ₁ / (vec_op_norm⟨n, m⟩(L) + &2)")
					θPos := d.Have(
						"θ = δ₁/(‖L‖ + 2) is positive",
						"&0 < θ",
						ByArith(θDef, size, byF[0]))
					θUnit := d.Have(
						"‖L‖ + 2 times θ is δ₁",
						"(vec_op_norm⟨n, m⟩(L) + &2) * θ = δ₁",
						ByArith(θDef, size))
					inner := d.TermAs[Real]("min(δ₀, δ₂)")
					outer := d.TermAs[Real]("min(ρ, θ)")
					d.Take(d.TermAs[Real]("min(min(δ₀, δ₂), min(ρ, θ))"))
					d.Do(SplitConj(
						Case(
							"the radius min(min(δ₀, δ₂), min(ρ, θ)) is positive",
							By(
								grows[0],
								byL[0],
								ρPos,
								θPos,
								real_sup_inf.LessThanMin.At(inner, outer, d.TermAs[Real]("&0")),
								real_sup_inf.LessThanMin.At(δ0, δ2, d.TermAs[Real]("&0")),
								real_sup_inf.LessThanMin.At(ρ, θ, d.TermAs[Real]("&0")))),
						Case(
							"within it, the two errors add up to at most (2 + ‖L‖ + ‖q‖)η‖x − a‖ = ε‖x − a‖",
							Derive(func(e *Argument) {
								x := e.VecFixAs[Real, DimN]("x")
								atX := e.Conjuncts(
									e.Assume(),
									"x is an n-vector",
									"within the radius of a")
								distance := e.TermAs[Real]("‖x - a‖_n")
								within := e.Have(
									"so x is within δ₀, δ₂, ρ and θ of a",
									"‖x - a‖_n < δ₀ ∧ ‖x - a‖_n < δ₂ ∧ ‖x - a‖_n < ρ ∧ ‖x - a‖_n < θ",
									By(
										atX[1],
										real_sup_inf.LessThanMin.At(inner, outer, distance),
										real_sup_inf.LessThanMin.At(δ0, δ2, distance),
										real_sup_inf.LessThanMin.At(ρ, θ, distance)))
								gx := g.Apply(x)
								gxIn := e.Have(
									"g(x) is an m-vector",
									"vec⟨m⟩(g(x))",
									By(gValues.At(x), atX[0], within))
								moved := e.Have(
									"g(x) is within (‖L‖ + 1)‖x − a‖ of b",
									"‖g(x) - b‖_m ≤ (vec_op_norm⟨n, m⟩(L) + &1) * ‖x - a‖_n",
									By(grows[1].At(x), atX[0], within, gAtA))
								step := e.VecAs[Real, DimN]("x - a")
								inBox := e.Have(
									"so x and g(x) lie within δ₁ of a and b, θ being δ₁/(‖L‖ + 2)",
									"‖x - a‖_n < δ₁ ∧ ‖g(x) - b‖_m < δ₁",
									ByArith(
										within,
										moved,
										θPos,
										θUnit,
										size,
										euclidean.NormNonneg.At(step),
										real_order_ring.LessEqMulLeft.At(e.TermAs[Real]("vec_op_norm⟨n, m⟩(L)"), distance, θ)))
								errorF := e.Have(
									"there f's increment is ⟪p, x − a⟫ + ⟪q, g(x) − b⟫ to within η(‖x − a‖ + ‖g(x) − b‖)",
									"|f(x, g(x)) - f(a, b) - ⟪p, x - a⟫_n - ⟪q, g(x) - b⟫_m| ≤ η * (‖x - a‖_n + ‖g(x) - b‖_m)",
									By(byF[1].At(x, gx), atX[0], gxIn, inBox))
								errorG := e.Have(
									"and g(x) − b is L(x − a) to within η‖x − a‖",
									"‖g(x) - b - L(x - a)‖_m ≤ η * ‖x - a‖_n",
									By(byL[1].At(x), atX[0], within, gAtA))
								residual := e.VecAs[Real, DimM]("g(x) - b - L(x - a)")
								minusOne := e.TermAs[Real]("-&1")
								pairing := e.Have(
									"by Cauchy–Schwarz at the residual and at its negative, "+
										"⟪q, residual⟫ is at most ‖q‖ times its norm in size",
									"|⟪q, g(x) - b - L(x - a)⟫_m| ≤ ‖q‖_m * ‖g(x) - b - L(x - a)‖_m",
									ByArith(
										euclidean.CauchySchwarz.At(q, residual),
										euclidean.CauchySchwarz.At(q, e.VecAs[Real, DimM]("(-&1) • (g(x) - b - L(x - a))")),
										dot.SmulRight.Read(real_ring.CommRing).At(minusOne, q, residual),
										euclidean.NormSmul.At(minusOne, residual)))
								scaledMove := e.Have(
									"η‖g(x) − b‖ is at most η(‖L‖ + 1)‖x − a‖",
									"η * ‖g(x) - b‖_m ≤ η * ((vec_op_norm⟨n, m⟩(L) + &1) * ‖x - a‖_n)",
									ByArith(moved, ηPos))
								scaledError := e.Have(
									"‖q‖ times the residual's norm is at most ‖q‖η‖x − a‖",
									"‖q‖_m * ‖g(x) - b - L(x - a)‖_m ≤ ‖q‖_m * (η * ‖x - a‖_n)",
									ByArith(errorG, qSize))
								e.Show(
									"⟪q, g(x) − b⟫ − ⟪q, L(x − a)⟫ is ⟪q, residual⟫, and (2 + ‖L‖ + ‖q‖)η = ε",
									ByArith(
										errorF,
										pairing,
										scaledMove,
										scaledError,
										Scaled(distance, ηUnit),
										dot.SubRight.Read(real_ring.CommRing).At(q, e.VecAs[Real, DimM]("g(x) - b"), L.Apply(step))))
							}))))
				}))

			// Along the line x = a + t•u the first-order term is (⟪p, u⟫ + ⟪q, L(u)⟫)t.
			line := arg.Conjuncts(
				euclidean.LineThroughPoint.At(proof.Inhabit(a, byG[0]), proof.Inhabit(u, uIn)),
				"the line through a in the direction u starts at a",
				"and its point at t is an n-vector, t•u from a, at distance |t|‖u‖")
			along := arg.Have(
				"along the line, f(a + t•u, g(a + t•u)) − f(a, b) is (⟪p, u⟫ + ⟪q, L(u)⟫)t to within ε|t|",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀t:real. " +
						"        &0 < |t| ∧ |t| < δ ⇒ " +
						"        |f(a + t • u, g(a + t • u)) - f(a, b) - (⟪p, u⟫_n + ⟪q, L(u)⟫_m) * t| < ε * |t|)",
				},
				Derive(func(d *Argument) {
					d.FixAs[Real]("ε")
					pos := d.Assume()
					uSize := euclidean.NormNonneg.At(u)
					κ, κDef := d.LetAs[Real]("κ", "ε / (‖u‖_n + &1)")
					κPos := d.Have(
						"κ = ε/(‖u‖ + 1) is positive",
						"&0 < κ",
						ByArith(κDef, pos, uSize))
					κUnit := d.Have(
						"‖u‖ + 1 times κ is ε",
						"(‖u‖_n + &1) * κ = ε",
						ByArith(κDef, uSize))
					_, nearA := d.UnpackAs[Real](GroupPremises(κPos, chain.At(κ)), "δ₁")
					nearChain := d.Conjuncts(
						nearA,
						"δ₁ is positive",
						"and within δ₁ of a, f's increment at (x, g(x)) is ⟪p, x − a⟫ + ⟪q, L(x − a)⟫ to within κ‖x − a‖")
					ω, ωDef := d.LetAs[Real]("ω", "δ₁ / (‖u‖_n + &1)")
					ωPos := d.Have(
						"ω = δ₁/(‖u‖ + 1) is positive",
						"&0 < ω",
						ByArith(ωDef, nearChain[0], uSize))
					ωUnit := d.Have(
						"‖u‖ + 1 times ω is δ₁",
						"(‖u‖_n + &1) * ω = δ₁",
						ByArith(ωDef, uSize))
					d.Take(ω)
					d.Do(SplitConj(
						Case(
							"ω is positive",
							By(ωPos)),
						Case(
							"for 0 < |t| < ω, the error is at most κ|t|‖u‖, below ε|t|",
							Derive(func(e *Argument) {
								t := e.FixAs[Real]("t")
								atT := e.Conjuncts(
									e.Assume(),
									"t is not zero",
									"and |t| < ω")
								point := e.VecAs[Real, DimN]("a + t • u")
								onLine := e.Conjuncts(
									line[1].At(t),
									"a + t•u is an n-vector",
									"t•u from a",
									"at distance |t|‖u‖ from a")
								tSize := e.TermAs[Real]("|t|")
								nearPoint := e.Have(
									"so within δ₁ of a, |t| being less than ω = δ₁/(‖u‖ + 1)",
									"‖a + t • u - a‖_n < δ₁",
									ByArith(
										onLine[2],
										atT[1],
										ωUnit,
										ωPos,
										uSize,
										real_order_ring.LessEqMulLeft.At(e.TermAs[Real]("‖u‖_n"), tSize, ω)))
								estimate := e.Have(
									"there f's increment is ⟪p, t•u⟫ + ⟪q, L(t•u)⟫ to within κ|t|‖u‖",
									"|f(a + t • u, g(a + t • u)) - f(a, b) - (⟪p, a + t • u - a⟫_n + ⟪q, L(a + t • u - a)⟫_m)| ≤ "+
										"κ * ‖a + t • u - a‖_n",
									By(nearChain[1].At(point), onLine[0], nearPoint))
								first := e.Have(
									"and ⟪p, t•u⟫ + ⟪q, L(t•u)⟫ is (⟪p, u⟫ + ⟪q, L(u)⟫)t, L commuting with scaling",
									"⟪p, a + t • u - a⟫_n + ⟪q, L(a + t • u - a)⟫_m = (⟪p, u⟫_n + ⟪q, L(u)⟫_m) * t",
									onLine[1].Rw(),
									homogeneous.At(t, u).Rw(),
									ByArith(
										dot.SmulRight.Read(real_ring.CommRing).At(t, p, u),
										dot.SmulRight.Read(real_ring.CommRing).At(t, q, L.Apply(u))))
								e.Show(
									"κ|t|‖u‖ is below (‖u‖ + 1)κ|t| = ε|t|",
									ByArith(estimate, first, onLine[2], Scaled(tSize, κUnit), atT[0], κPos))
							}))))
				}))
			arg.Show(
				"by the derivative's definition at 0, where the line "+
					"is at a and g at b, this is the estimate along the line",
				Simp(
					Fwd(real_derivative.DerivativeIncrement),
					Fwd(line[0]),
					Fwd(gAtA),
					Fwd(real_ring.SubRightZero)),
				By(along))
		}),
})}

// LagrangeMultiplier — Lagrange multipliers in block form: at a local
// minimum (a, b) of f on the zeros of G, where f has the gradients p and q
// and G's derivative in y is invertible at (a, b) (inverse K), there is a
// multiplier μ in ℝᵐ with ⟪p, u⟫ = ⟪μ, Lx(u)⟫ and ⟪q, v⟫ = ⟪μ, Dy(a, b)(v)⟫,
// Lx and Dy(a, b) being G's derivatives in x and in y. The multiplier is the
// adjoint of K at q, so ⟪q, K(w)⟫ = ⟪μ, w⟫; the second equation is that
// identity at w = Dy(a, b)(v), K undoing Dy(a, b). The implicit function g of
// G(x, y) = 0 has the derivative −K ∘ Lx at a, so along the line through a
// in the direction u, t ↦ f(a + t•u, g(a + t•u)) has the derivative
// ⟪p, u⟫ − ⟪μ, Lx(u)⟫ at 0 (GraphDerivativeAlongLine); g being continuous at
// a, (a + t•u, g(a + t•u)) is a nearby zero of G for small t, so t = 0 is a
// local minimum and the derivative vanishes there.
var LagrangeMultiplier = lagrangeMultiplierThm{family.Add(registry.ProofEntry{
	Name: "LagrangeMultiplier",
	Key:  "prop_b36f117c851aa639",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. " +
			"∀f:((num → real) → (num → real) → real). " +
			"∀G:((num → real) → (num → real) → (num → real)). " +
			"∀Dy:((num → real) → (num → real) → (num → real) → (num → real)). " +
			"∀Lx K:((num → real) → (num → real)). " +
			"∀p q a b:(num → real). " +
			"∀r:real.",
		Hypotheses: []string{
			"vec⟨n⟩(a)",
			"vec⟨m⟩(b)",
			"&0 < r",
			"G(a, b) = vec_zero",
			"∀x y:(num → real). vec⟨n⟩(x) ∧ vec⟨m⟩(y) ⇒ vec⟨m⟩(G(x, y))",
			"∀x y:(num → real). " +
				"    vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < r ∧ ‖y - b‖_m < r ⇒ " +
				"    vec_derivative_at⟨m, m⟩(λv:(num → real). G(x, v), y, Dy(x, y))",
			"∀ε:real. " +
				"    &0 < ε ⇒ " +
				"    ∃δ:real. " +
				"        &0 < δ ∧ " +
				"        ∀x y:(num → real). " +
				"            vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < δ ∧ ‖y - b‖_m < δ ⇒ " +
				"            vec_op_norm⟨m, m⟩(λv:(num → real). Dy(x, y, v) - Dy(a, b, v)) ≤ ε",
			"vec_derivative_at⟨n, m⟩(λu:(num → real). G(u, b), a, Lx)",
			"vec_inverse_on⟨m⟩(Dy(a, b), K)",
			"∀ε:real. " +
				"    &0 < ε ⇒ " +
				"    ∃δ:real. " +
				"        &0 < δ ∧ " +
				"        ∀x y:(num → real). " +
				"            vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < δ ∧ ‖y - b‖_m < δ ⇒ " +
				"            |f(x, y) - f(a, b) - ⟪p, x - a⟫_n - ⟪q, y - b⟫_m| ≤ ε * (‖x - a‖_n + ‖y - b‖_m)",
			"∃ρ:real. " +
				"    &0 < ρ ∧ " +
				"    ∀x y:(num → real). " +
				"        vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < ρ ∧ ‖y - b‖_m < ρ ∧ G(x, y) = vec_zero ⇒ " +
				"        f(a, b) ≤ f(x, y)",
		},
		Conclusion: "∃μ:(num → real). " +
			"    vec⟨m⟩(μ) ∧ " +
			"    (∀u:(num → real). vec⟨n⟩(u) ⇒ ⟪p, u⟫_n = ⟪μ, Lx(u)⟫_m) ∧ " +
			"    (∀v:(num → real). vec⟨m⟩(v) ⇒ ⟪q, v⟫_m = ⟪μ, Dy(a, b, v)⟫_m)",
	},
		func(arg *Argument, n, m *Expr[Nat], f *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Real],
			G *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Nat, Real]],
			Dy *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Fun[Nat, Real], Fun[Nat, Real]]],
			Lx *VecFun[Real, DimN, DimM], K *VecFun[Real, DimM, DimM], p *Vec[Real, DimN], q *Vec[Real, DimM],
			a *Vec[Real, DimN], b *Vec[Real, DimM], r *Expr[Real],
			aIn, bIn, rPos, root, values, derivatives, continuity, ofX, inverse, differentiable, minimum Fact) {
			// The implicit function g of G(x, y) = 0 near (a, b), with the derivative −K ∘ Lx at a.
			ρ, _, _, solved := arg.Unpack3As[Real, Real, Fun[Fun[Nat, Real], Fun[Nat, Real]]](
				GroupPremises(
					rPos,
					root,
					values,
					derivatives,
					continuity,
					ofX,
					inverse,
					ImplicitFunction.At(G, Dy, Lx, K, proof.Inhabit(a, aIn), proof.Inhabit(b, bIn), r)),
				"ρ",
				"σ",
				"g")
			sol := arg.Conjuncts(
				solved,
				"ρ is positive",
				"σ is positive",
				"g(a) = b",
				"near a, g(x) is an m-vector within σ of b with G(x, g(x)) = 0",
				"and the only zero of G(x, ·) within σ of b",
				"and g has the derivative −K ∘ Lx at a")
			g := arg.VecFunAs[Real, DimN, DimM]("g")
			slope := arg.VecFunAs[Real, DimN, DimM]("λu:(num → real). -K(Lx(u))")

			// μ, the adjoint of K at q, carries K across the form.
			inverts := arg.Conjuncts(
				arg.Unfolded(inverse, vec_derivative.VecInverseOnDef),
				"K is linear",
				"and on ℝᵐ it takes values in ℝᵐ and inverts Dy(a, b) on both sides")
			μ, μDef := arg.LetAs[Fun[Nat, Real]]("μ", "adjoint(m, m, K, q)")
			multiplier := arg.VecAs[Real, DimM]("μ")
			transfers := arg.Have(
				"⟪q, K(w)⟫ = ⟪μ, w⟫ for w in ℝᵐ",
				"∀w:(num → real). vec⟨m⟩(w) ⇒ ⟪q, K(w)⟫_m = ⟪μ, w⟫_m",
				Derive(func(d *Argument) {
					w := d.VecFixAs[Real, DimM]("w")
					wIn := d.Assume()
					d.Show(
						"the adjoint's identity ⟪K(w), q⟫ = ⟪w, μ⟫, each side read the other way round",
						By(
							Normalized,
							μDef,
							inverts[0],
							dot.AdjointWorks.Read(real_ring.CommRing).At(K, proof.Inhabit(w, wIn), q),
							dot.Sym.Read(real_ring.CommRing).At(q, K.Apply(w)),
							dot.Sym.Read(real_ring.CommRing).At(w, multiplier)))
				}))

			// The y-equation: K undoes Dy(a, b).
			atCentre := arg.Have(
				"Dy(a, b) is the derivative of y ↦ G(a, y) at b, (a, b) being at distance zero from itself",
				"vec_derivative_at⟨m, m⟩(λv:(num → real). G(a, v), b, Dy(a, b))",
				By(
					derivatives.At(a, b),
					aIn,
					bIn,
					euclidean.NormSubRefl.At(n, a),
					euclidean.NormSubRefl.At(m, b),
					rPos))
			yMaps := arg.Conjuncts(
				arg.Unfolded(atCentre, vec_derivative.VecDerivativeAtDef),
				"b is an m-vector",
				"Dy(a, b) is linear",
				"Dy(a, b) takes the m-vectors to m-vectors",
				"and near b, G(a, y) − G(a, b) is Dy(a, b)(y − b) to within ε‖y − b‖")[2]
			yEquation := arg.Have(
				"⟪q, v⟫ = ⟪q, K(Dy(a, b)(v))⟫ = ⟪μ, Dy(a, b)(v)⟫ for v in ℝᵐ",
				"∀v:(num → real). vec⟨m⟩(v) ⇒ ⟪q, v⟫_m = ⟪μ, Dy(a, b, v)⟫_m",
				Derive(func(d *Argument) {
					v := d.VecFixAs[Real, DimM]("v")
					vIn := d.Assume()
					d.Show(
						"K undoes Dy(a, b) on ℝᵐ",
						By(transfers.At(d.VecAs[Real, DimM]("Dy(a, b, v)")), yMaps.At(v), inverts[1].At(v), vIn))
				}))

			// The x-equation: along every line through a, f(x, g(x)) is least at a.
			ρ1, minimal := arg.UnpackAs[Real](minimum, "ρ₁")
			atMin := arg.Conjuncts(
				minimal,
				"ρ₁ is positive",
				"and f(a, b) ≤ f(x, y) at every zero (x, y) of G within ρ₁ of (a, b)")
			gContinuous := arg.Conjuncts(
				arg.Unfolded(
					GroupPremises(sol[5], vec_derivative.VecDerivativeContinuous.At(g, slope, a)),
					vec_derivative.VecContinuousAtDef),
				"g is continuous at a: a is an n-vector",
				"and near a, g(x) is near g(a)")
			δ0, continuous := arg.UnpackAs[Real](GroupPremises(atMin[0], gContinuous[1].At(ρ1)), "δ₀")
			stays := arg.Conjuncts(
				continuous,
				"δ₀ is positive",
				"and within δ₀ of a, g(x) stays within ρ₁ of g(a)")
			inner := arg.TermAs[Real]("min(ρ, δ₀)")
			radiusPos := arg.Have(
				"the radius min(min(ρ, δ₀), ρ₁) is positive",
				"&0 < min(min(ρ, δ₀), ρ₁)",
				By(
					sol[0],
					stays[0],
					atMin[0],
					real_sup_inf.LessThanMin.At(inner, ρ1, arg.TermAs[Real]("&0")),
					real_sup_inf.LessThanMin.At(ρ, δ0, arg.TermAs[Real]("&0"))))
			xMaps := arg.Conjuncts(
				arg.Unfolded(ofX, vec_derivative.VecDerivativeAtDef),
				"a is an n-vector",
				"Lx is linear",
				"Lx takes the n-vectors to m-vectors",
				"and near a, G(x, b) − G(a, b) is Lx(x − a) to within ε‖x − a‖")[2]
			xEquation := arg.Have(
				"⟪p, u⟫ = ⟪μ, Lx(u)⟫ for u in ℝⁿ",
				"∀u:(num → real). vec⟨n⟩(u) ⇒ ⟪p, u⟫_n = ⟪μ, Lx(u)⟫_m",
				Derive(func(d *Argument) {
					u := d.VecFixAs[Real, DimN]("u")
					uIn := d.Assume()
					uSize := euclidean.NormNonneg.At(u)
					rate := d.TermAs[Real]("⟪p, u⟫_n + ⟪q, -K(Lx(u))⟫_m")
					chain := d.Have(
						"t ↦ f(a + t•u, g(a + t•u)) has the derivative ⟪p, u⟫ + ⟪q, −K(Lx(u))⟫ at 0",
						"real_derivative_at(λt:real. f(a + t • u, g(a + t • u)), &0, ⟪p, u⟫_n + ⟪q, -K(Lx(u))⟫_m)",
						By(
							differentiable,
							sol[5],
							sol[2],
							sol[0],
							sol[3],
							GraphDerivativeAlongLine.At(f, g, slope, p, q, a, b, proof.Inhabit(u, uIn), ρ)))
					line := d.Conjuncts(
						euclidean.LineThroughPoint.At(proof.Inhabit(a, aIn), proof.Inhabit(u, uIn)),
						"the line through a in the direction u starts at a",
						"and its point at t is an n-vector, t•u from a, at distance |t|‖u‖")
					δ, δDef := d.LetAs[Real]("δ", "min(min(ρ, δ₀), ρ₁) / (‖u‖_n + &1)")
					δPos := d.Have(
						"δ is positive",
						"&0 < δ",
						ByArith(δDef, radiusPos, uSize))
					δUnit := d.Have(
						"‖u‖ + 1 times δ is min(min(ρ, δ₀), ρ₁)",
						"(‖u‖_n + &1) * δ = min(min(ρ, δ₀), ρ₁)",
						ByArith(δDef, uSize))
					least := d.Have(
						"for |t| < δ, (a + t•u, g(a + t•u)) is a zero of "+
							"G within ρ₁ of (a, b), where f is at least f(a, b)",
						"∀t:real. |t| < δ ⇒ f(a, b) ≤ f(a + t • u, g(a + t • u))",
						Derive(func(e *Argument) {
							t := e.FixAs[Real]("t")
							short := e.Assume()
							point := e.VecAs[Real, DimN]("a + t • u")
							onLine := e.Conjuncts(
								line[1].At(t),
								"a + t•u is an n-vector",
								"t•u from a",
								"at distance |t|‖u‖ from a")
							near := e.Have(
								"so within min(min(ρ, δ₀), ρ₁) of a, |t| being less than δ",
								"‖a + t • u - a‖_n < min(min(ρ, δ₀), ρ₁)",
								ByArith(
									onLine[2],
									short,
									δUnit,
									uSize,
									real_order_ring.LessEqMulLeft.At(e.TermAs[Real]("‖u‖_n"), e.TermAs[Real]("|t|"), δ)))
							distance := e.TermAs[Real]("‖a + t • u - a‖_n")
							within := e.Have(
								"within ρ, δ₀ and ρ₁ of a",
								"‖a + t • u - a‖_n < ρ ∧ ‖a + t • u - a‖_n < δ₀ ∧ ‖a + t • u - a‖_n < ρ₁",
								By(
									near,
									real_sup_inf.LessThanMin.At(inner, ρ1, distance),
									real_sup_inf.LessThanMin.At(ρ, δ0, distance)))
							e.Show(
								"g(a + t•u) is an m-vector within ρ₁ of g(a) = b, with G(a + t•u, g(a + t•u)) = 0",
								By(
									atMin[1].At(point, g.Apply(point)),
									sol[3].At(point),
									stays[1].At(point),
									onLine[0],
									within,
									sol[2]))
						}))
					zero := d.Have(
						"so that derivative vanishes, t = 0 being a least point "+
							"within δ (Fermat's rule), where the line is at a and g at b",
						"⟪p, u⟫_n + ⟪q, -K(Lx(u))⟫_m = &0",
						By(
							real_derivative.LocalMinDerivativeZero.At(
								d.TermAs[Fun[Real, Real]]("λt:real. f(a + t • u, g(a + t • u))"),
								d.TermAs[Real]("&0"),
								δ,
								rate),
							line[0],
							sol[2],
							real_ring.SubRightZero,
							δPos,
							least,
							chain))
					d.Show(
						"⟪q, −K(Lx(u))⟫ is −⟪q, K(Lx(u))⟫ = −⟪μ, Lx(u)⟫",
						ByArith(
							zero,
							transfers.At(Lx.Apply(u)),
							xMaps.At(u),
							uIn,
							dot.NegRight.Read(real_ring.CommRing).At(q, K.Apply(Lx.Apply(u)))))
				}))
			arg.Take(μ)
			arg.Show(
				"μ is an m-vector satisfying both equations",
				By(Normalized, μDef, dot.AdjointVec.Read(real_ring.CommRing).At(m, m, K, q), xEquation, yEquation))
		}),
})}
