// theorem.go — the implicit function theorem, and the inverse function theorem as its case.

package inverse_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_derivative"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ImplicitFunction — the implicit function theorem: when F(a, b) = 0, F
// has near (a, b) a derivative Dy(x, y) in y continuous at (a, b) with
// Dy(a, b) invertible (inverse K), and x ↦ F(x, b) has the derivative Lx
// at a, the equation F(x, y) = 0 defines y = g(x) near a, with g(a) = b,
// and g has the derivative −K ∘ Lx at a. x ↦ F(x, b) is continuous at a,
// so ImplicitSolution gives g, within 2‖K(F(x, b))‖ of b; that is at most
// G‖x − a‖ near a, G = 2‖K‖(‖Lx‖ + 1) with ‖K‖ and ‖Lx‖ the operator
// norms (vec_derivative.VecDerivativeIncrementBound).
// The map h(x) = −K(F(x, b)) has the derivative −K ∘ Lx at a by the
// chain rule. g(x) − b − (h(x) − h(a)) is T(g(x)) − T(b) for
// T(y) = y − K(F(x, y)), which fixes g(x); near (a, b), T moves points at
// most κ times their distance for any κ > 0 (ImplicitLipschitz), so this
// difference is at most κG‖x − a‖, and g has h's derivative
// (vec_derivative.VecDerivativeTangent).
var ImplicitFunction = implicitFunctionThm{family.Add(registry.ProofEntry{
	Name: "ImplicitFunction",
	Key:  "prop_e59796c5065141e7",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. " +
			"∀F:((num → real) → (num → real) → (num → real)). " +
			"∀Dy:((num → real) → (num → real) → (num → real) → (num → real)). " +
			"∀Lx K:((num → real) → (num → real)). " +
			"∀a b:(num → real). " +
			"∀r:real.",
		Hypotheses: []string{
			"vec⟨n⟩(a)",
			"vec⟨m⟩(b)",
			"&0 < r",
			"F(a, b) = vec_zero",
			"∀x y:(num → real). vec⟨n⟩(x) ∧ vec⟨m⟩(y) ⇒ vec⟨m⟩(F(x, y))",
			"∀x y:(num → real). " +
				"    vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < r ∧ ‖y - b‖_m < r ⇒ " +
				"    vec_derivative_at⟨m, m⟩(λv:(num → real). F(x, v), y, Dy(x, y))",
			"∀ε:real. " +
				"    &0 < ε ⇒ " +
				"    ∃δ:real. " +
				"        &0 < δ ∧ " +
				"        ∀x y:(num → real). " +
				"            vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < δ ∧ ‖y - b‖_m < δ ⇒ " +
				"            vec_op_norm⟨m, m⟩(λv:(num → real). Dy(x, y, v) - Dy(a, b, v)) ≤ ε",
			"vec_derivative_at⟨n, m⟩(λu:(num → real). F(u, b), a, Lx)",
			"vec_inverse_on⟨m⟩(Dy(a, b), K)",
		},
		Conclusion: "∃ρ σ:real. ∃g:((num → real) → (num → real)). " +
			"    &0 < ρ ∧ " +
			"    &0 < σ ∧ " +
			"    g(a) = b ∧ " +
			"    (∀x:(num → real). " +
			"        vec⟨n⟩(x) ∧ ‖x - a‖_n < ρ ⇒ vec⟨m⟩(g(x)) ∧ ‖g(x) - b‖_m < σ ∧ F(x, g(x)) = vec_zero) ∧ " +
			"    (∀x y:(num → real). " +
			"        vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < ρ ∧ ‖y - b‖_m < σ ∧ F(x, y) = vec_zero ⇒ " +
			"        y = g(x)) ∧ " +
			"    vec_derivative_at⟨n, m⟩(g, a, λu:(num → real). -K(Lx(u)))",
		Abbrev: Abbrev{
			{Name: "G", Text: "&2 * vec_op_norm⟨m, m⟩(K) * (vec_op_norm⟨n, m⟩(Lx) + &1)"},
			{Name: "T", Text: "λw:(num → real). w - K(F(x, w))"},
		},
	},
		func(
			arg *Argument,
			n, m *Expr[Nat],
			F *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Nat, Real]],
			Dy *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Fun[Nat, Real], Fun[Nat, Real]]],
			Lx *VecFun[Real, DimN, DimM],
			K *VecFun[Real, DimM, DimM],
			a *Vec[Real, DimN],
			b *Vec[Real, DimM],
			r *Expr[Real],
			aIn, bIn, rPos, root, values, derivatives, continuity, ofX, inverse Fact,
		) {
			// x ↦ F(x, b) is continuous at a, where it vanishes.
			slice := arg.VecFunAs[Real, DimN, DimM]("λu:(num → real). F(u, b)")
			fromRoot := arg.Have(
				"F(x, b) less F(a, b) is F(x, b), F(a, b) being zero",
				"∀x:(num → real). F(x, b) - F(a, b) = F(x, b)",
				Derive(func(d *Argument) {
					d.FixAs[Fun[Nat, Real]]("x")
					d.Show(
						"subtracting zero changes nothing",
						root.Rw(),
						Funext(),
						Unfold(vec_space.VecSubDef),
						Unfold(vec_space.VecZeroDef),
						ByArith())
				}))
			start := arg.Have(
				"F(x, b) is small near a, x ↦ F(x, b) being continuous there, and F(x, b) − F(a, b) being F(x, b)",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. &0 < δ ∧ (∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - a‖_n < δ ⇒ ‖F(x, b)‖_m < ε)",
				},
				By(
					arg.Unfolded(
						GroupPremises(ofX, vec_derivative.VecDerivativeContinuous.At(slice, Lx, a)),
						vec_derivative.VecContinuousAtDef),
					fromRoot))

			// The solution g, and its bound by K(F(x, b)).
			ρ, σ, g, solved := arg.Unpack3As[Real, Real, Fun[Fun[Nat, Real], Fun[Nat, Real]]](
				GroupPremises(
					rPos,
					root,
					values,
					derivatives,
					continuity,
					inverse,
					start,
					ImplicitSolution.At(F, Dy, K, proof.Inhabit(a, aIn), proof.Inhabit(b, bIn), r)),
				"ρ",
				"σ",
				"g")
			sol := arg.Conjuncts(
				solved,
				"ρ is positive",
				"σ is positive",
				"g(a) = b",
				"near a, g(x) is an m-vector within σ of b, a zero of F(x, ·), within 2‖K(F(x, b))‖ of b",
				"and the only zero of F(x, ·) within σ of b")

			// K: linear, carrying ℝᵐ into ℝᵐ, keeping zero; the operator norms of K and Lx.
			inverts := arg.Conjuncts(
				arg.Unfolded(inverse, vec_derivative.VecInverseOnDef),
				"K is linear",
				"and on ℝᵐ it takes values in ℝᵐ and inverts Dy(a, b) on both sides")
			linear := inverts[0]
			kValues := arg.Have(
				"K carries ℝᵐ into ℝᵐ",
				"∀h:(num → real). vec⟨m⟩(h) ⇒ vec⟨m⟩(K(h))",
				By(inverts[1]))
			kZero := arg.Have(
				"K, being linear, keeps zero",
				"K(vec_zero) = vec_zero",
				By(linear, vec_space.LinearVecZero.Read(real_ring.CommRing).At(K)))
			size := arg.Have(
				"the operator norm of K is not negative",
				"&0 ≤ vec_op_norm⟨m, m⟩(K)",
				By(linear, euclidean.OpNormNonneg.At(K)))
			sizeX := arg.Have(
				"nor is that of Lx",
				"&0 ≤ vec_op_norm⟨n, m⟩(Lx)",
				By(arg.Unfolded(ofX, vec_derivative.VecDerivativeAtDef), euclidean.OpNormNonneg.At(Lx)))
			growthNonneg := arg.Have(
				"so G = 2‖K‖(‖Lx‖ + 1) is not negative",
				"&0 ≤ «G»",
				ByArith(size, sizeX))

			xValues := arg.Have(
				"x ↦ F(x, b) carries ℝⁿ into ℝᵐ",
				"∀x:(num → real). vec⟨n⟩(x) ⇒ vec⟨m⟩(F(x, b))",
				By(values, bIn))
			atRoot := arg.VecAs[Real, DimM]("F(a, b)")
			atRootIn := arg.Have(
				"F(a, b) is an m-vector",
				"vec⟨m⟩(F(a, b))",
				By(xValues.At(a), aIn))
			ofK := arg.Have(
				"K, being linear, is its own derivative at F(a, b)",
				"vec_derivative_at⟨m, m⟩(K, F(a, b), K)",
				By(linear, kValues, vec_derivative.VecDerivativeLinear.At(K, proof.Inhabit(atRoot, atRootIn))))
			// The chain rule asks x ↦ F(x, b) to carry the n-vectors within
			// some radius of a into ℝᵐ; it carries all of ℝⁿ there, so any
			// positive radius serves, r among them.
			ofComposite := arg.Have(
				"so by the chain rule x ↦ K(F(x, b)) has the derivative K ∘ Lx at a",
				"vec_derivative_at⟨n, m⟩(λx:(num → real). K(F(x, b)), a, λu:(num → real). K(Lx(u)))",
				By(
					ofX,
					ofK,
					rPos,
					xValues,
					vec_derivative.VecDerivativeChain.At(slice, K, Lx, K, a, r),
					functions.ComposeApply))
			composite := arg.VecFunAs[Real, DimN, DimM]("λx:(num → real). K(F(x, b))")
			compositeSlope := arg.VecFunAs[Real, DimN, DimM]("λu:(num → real). K(Lx(u))")
			ofH := arg.Have(
				"and h(x) = −K(F(x, b)) has the derivative −K ∘ Lx",
				"vec_derivative_at⟨n, m⟩(λx:(num → real). -K(F(x, b)), a, λu:(num → real). -K(Lx(u)))",
				By(ofComposite, vec_derivative.VecDerivativeNeg.At(composite, compositeSlope, a)))

			// Near a, g(x) is a fixed point of T within G‖x − a‖ of b.
			δ1, increment := arg.UnpackAs[Real](
				GroupPremises(ofX, vec_derivative.VecDerivativeIncrementBound.At(slice, Lx, a)),
				"δ₁")
			grows := arg.Conjuncts(
				increment,
				"δ₁ is positive",
				"and within δ₁ of a, F(x, b) − F(a, b) is at most (‖Lx‖ + 1)‖x − a‖")
			growth := arg.Have(
				"within min(ρ, δ₁) of a, g(x) is an m-vector T fixes, within G‖x − a‖ of b",
				Statement{
					Binders: "∀x:(num → real).",
					Hypotheses: []string{
						"vec⟨n⟩(x)",
						"‖x - a‖_n < min(ρ, δ₁)",
					},
					Conclusion: "vec⟨m⟩(g(x)) ∧ g(x) - K(F(x, g(x))) = g(x) ∧ ‖g(x) - b‖_m ≤ «G» * ‖x - a‖_n",
				},
				Derive(func(d *Argument) {
					x := d.VecFixAs[Real, DimN]("x")
					atX := d.Conjuncts(
						d.Assume(),
						"x is an n-vector",
						"within min(ρ, δ₁) of a")
					xClose := d.Have(
						"x is within ρ and within δ₁ of a",
						"‖x - a‖_n < ρ ∧ ‖x - a‖_n < δ₁",
						By(atX[1], real_sup_inf.LessThanMin.At(ρ, δ1, d.TermAs[Real]("‖x - a‖_n"))))
					atG := d.Conjuncts(
						GroupPremises(atX[0], xClose, sol[3].At(x)),
						"g(x) is an m-vector",
						"within σ of b",
						"a zero of F(x, ·)",
						"within 2‖K(F(x, b))‖ of b")
					image := d.VecAs[Real, DimM]("F(x, b)")
					imageIn := d.Have(
						"F(x, b) is an m-vector",
						"vec⟨m⟩(F(x, b))",
						By(xValues.At(x), atX[0]))
					moved := d.Have(
						"F(x, b) is at most (‖Lx‖ + 1)‖x − a‖",
						"‖F(x, b)‖_m ≤ (vec_op_norm⟨n, m⟩(Lx) + &1) * ‖x - a‖_n",
						By(grows[1].At(x), atX[0], xClose, fromRoot))
					bound := d.Have(
						"so ‖g(x) − b‖ ≤ 2‖K(F(x, b))‖ ≤ 2‖K‖‖F(x, b)‖ ≤ G‖x − a‖",
						"‖g(x) - b‖_m ≤ «G» * ‖x - a‖_n",
						ByArith(
							atG[3],
							euclidean.OpNormBound.At(K, proof.Inhabit(image, imageIn)),
							linear,
							real_order_ring.LessEqMulLeft.At(
								d.TermAs[Real]("vec_op_norm⟨m, m⟩(K)"),
								d.TermAs[Real]("‖F(x, b)‖_m"),
								d.TermAs[Real]("(vec_op_norm⟨n, m⟩(Lx) + &1) * ‖x - a‖_n")),
							size,
							moved))
					d.Show(
						"g(x) is an m-vector, a zero of F(x, ·) that T therefore fixes, within G‖x − a‖ of b",
						By(atG[0], linear, atG[2], ZeroIsFixedPoint.At(F, K, x, d.TermAs[Fun[Nat, Real]]("g(x)")), bound))
				}))

			tangent := arg.Have(
				"g(x) − g(a) agrees with h(x) − h(a) to first order at a",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀x:(num → real). " +
						"        vec⟨n⟩(x) ∧ ‖x - a‖_n < δ ⇒ " +
						"        ‖g(x) - g(a) - (-K(F(x, b)) - -K(F(a, b)))‖_m ≤ ε * ‖x - a‖_n)",
				},
				Derive(func(d *Argument) {
					d.FixAs[Real]("ε")
					pos := d.Assume()
					κ, κDef := d.LetAs[Real]("κ", "ε / («G» + &1)")
					κPos := d.Have(
						"the factor κ = ε/(G + 1) is positive",
						"&0 < κ",
						ByArith(pos, growthNonneg, κDef))
					κUnit := d.Have(
						"G + 1 times κ is ε",
						"(«G» + &1) * κ = ε",
						ByArith(growthNonneg, κDef))
					_, contracting := d.UnpackAs[Real](
						GroupPremises(
							rPos,
							values,
							derivatives,
							continuity,
							inverse,
							κPos,
							ImplicitLipschitz.At(F, Dy, K, proof.Inhabit(a, aIn), proof.Inhabit(b, bIn), r, κ)),
						"δ₂")
					lip := d.Conjuncts(
						contracting,
						"δ₂ is positive",
						"and within δ₂ of (a, b), T moves points at most κ times their distance")
					q, qDef := d.LetAs[Real]("q", "δ₂ / («G» + &1)")
					qPos := d.Have(
						"q = δ₂/(G + 1) is positive",
						"&0 < q",
						ByArith(lip[0], growthNonneg, qDef))
					qUnit := d.Have(
						"G + 1 times q is δ₂",
						"(«G» + &1) * q = δ₂",
						ByArith(growthNonneg, qDef))
					d.Take(d.TermAs[Real]("min(min(ρ, δ₁), q)"))
					d.Do(SplitConj(
						Case(
							"the radius min(min(ρ, δ₁), q) is positive",
							By(
								sol[0],
								grows[0],
								qPos,
								real_sup_inf.LessThanMin.At(ρ, δ1, d.TermAs[Real]("&0")),
								real_sup_inf.LessThanMin.At(d.TermAs[Real]("min(ρ, δ₁)"), q, d.TermAs[Real]("&0")))),
						Case(
							"within it, g(x) − g(a) − (h(x) − h(a)) is T(g(x)) "+
								"− T(b), at most κ‖g(x) − b‖ ≤ κG‖x − a‖ ≤ ε‖x − a‖",
							Derive(func(e *Argument) {
								x := e.VecFixAs[Real, DimN]("x")
								atX := e.Conjuncts(
									e.Assume(),
									"x is an n-vector",
									"within min(min(ρ, δ₁), q) of a")
								distance := e.TermAs[Real]("‖x - a‖_n")
								within := e.Have(
									"x lies within min(ρ, δ₁) and within q of a",
									"‖x - a‖_n < min(ρ, δ₁) ∧ ‖x - a‖_n < q",
									By(atX[1], real_sup_inf.LessThanMin.At(e.TermAs[Real]("min(ρ, δ₁)"), q, distance)))
								atG := e.Conjuncts(
									GroupPremises(atX[0], within, growth.At(x)),
									"g(x) is an m-vector",
									"T fixes g(x)",
									"within G‖x − a‖ of b")
								nearCentre := e.Have(
									"x, g(x) and b lie within δ₂ of a and b, b being at distance zero from itself",
									"‖x - a‖_n < δ₂ ∧ ‖g(x) - b‖_m < δ₂ ∧ ‖b - b‖_m < δ₂",
									ByArith(
										within,
										atG[2],
										qPos,
										qUnit,
										growthNonneg,
										real_order_ring.LessEqMulLeft.At(e.TermAs[Real]("«G»"), distance, q),
										euclidean.NormSubRefl.At(m, b),
										lip[0]))
								gx := e.VecAs[Real, DimM]("g(x)")
								step := e.Have(
									"T(g(x)) = g(x) lies within κ‖g(x) − b‖ of T(b)",
									"‖g(x) - «T»(b)‖_m ≤ κ * ‖g(x) - b‖_m",
									By(lip[1].At(x, gx, b), atX[0], atG[0], bIn, nearCentre, atG[1]))
								difference := e.Have(
									"g(x) − g(a) − (h(x) − h(a)) is g(x) − T(b), as g(a) = b and h(a) = 0",
									"g(x) - g(a) - (-K(F(x, b)) - -K(F(a, b))) = g(x) - «T»(b)",
									sol[2].Rw(),
									root.Rw(),
									kZero.Rw(),
									Funext(),
									Unfold(vec_space.VecSubDef),
									Unfold(vec_space.VecNegDef),
									Unfold(vec_space.VecZeroDef),
									ByArith())
								e.Show(
									"κ‖g(x) − b‖ ≤ κG‖x − a‖ ≤ ε‖x − a‖",
									difference.Rw(),
									ByArith(
										step,
										atG[2],
										κPos,
										κUnit,
										growthNonneg,
										real_order_ring.LessEqMulLeft.At(
											κ, e.TermAs[Real]("‖g(x) - b‖_m"), e.TermAs[Real]("«G» * ‖x - a‖_n")),
										euclidean.NormNonneg.At(e.VecAs[Real, DimN]("x - a"))))
							}))))
				}))
			derivative := arg.Have(
				"so g has h's derivative −K ∘ Lx at a",
				"vec_derivative_at⟨n, m⟩(g, a, λu:(num → real). -K(Lx(u)))",
				By(
					ofH,
					tangent,
					vec_derivative.VecDerivativeTangent.At(
						arg.VecFunAs[Real, DimN, DimM]("g"),
						arg.VecFunAs[Real, DimN, DimM]("λx:(num → real). -K(F(x, b))"),
						arg.VecFunAs[Real, DimN, DimM]("λu:(num → real). -K(Lx(u))"),
						a)))
			arg.Take(ρ)
			arg.Take(σ)
			arg.Take(g)
			arg.Show(
				"the radii, g(a) = b, the zeros, and the derivative",
				By(sol[0], sol[1], sol[2], sol[3], sol[4], derivative))
		}),
})}

// InverseFunction — the inverse function theorem: a map f of ℝⁿ into
// itself whose derivative D(y) exists near a, is continuous at a, and is
// invertible at a (inverse K) has near f(a) an inverse g with g(f(a)) = a,
// the only solution of f(y) = x near a, and g has the derivative K at
// f(a). It is ImplicitFunction at F(x, y) = f(y) − x, centred at (f(a), a):
// y ↦ f(y) − x has f's derivative D(y), x ↦ f(a) − x the derivative −id,
// and the derivative −K ∘ (−id) it gives g is K, K being linear.
var InverseFunction = inverseFunctionThm{family.Add(registry.ProofEntry{
	Name: "InverseFunction",
	Key:  "prop_bed6a3c4f277e548",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. " +
			"∀f K:((num → real) → (num → real)). " +
			"∀D:((num → real) → (num → real) → (num → real)). " +
			"∀a:(num → real). " +
			"∀r:real.",
		Hypotheses: []string{
			"vec⟨n⟩(a)",
			"&0 < r",
			"∀y:(num → real). vec⟨n⟩(y) ⇒ vec⟨n⟩(f(y))",
			"∀y:(num → real). vec⟨n⟩(y) ∧ ‖y - a‖_n < r ⇒ vec_derivative_at⟨n, n⟩(f, y, D(y))",
			"∀ε:real. " +
				"    &0 < ε ⇒ " +
				"    ∃δ:real. " +
				"        &0 < δ ∧ " +
				"        ∀y:(num → real). " +
				"            vec⟨n⟩(y) ∧ ‖y - a‖_n < δ ⇒ vec_op_norm⟨n, n⟩(λv:(num → real). D(y, v) - D(a, v)) ≤ ε",
			"vec_inverse_on⟨n⟩(D(a), K)",
		},
		Conclusion: "∃ρ σ:real. ∃g:((num → real) → (num → real)). " +
			"    &0 < ρ ∧ " +
			"    &0 < σ ∧ " +
			"    g(f(a)) = a ∧ " +
			"    (∀x:(num → real). " +
			"        vec⟨n⟩(x) ∧ ‖x - f(a)‖_n < ρ ⇒ vec⟨n⟩(g(x)) ∧ ‖g(x) - a‖_n < σ ∧ f(g(x)) = x) ∧ " +
			"    (∀x y:(num → real). " +
			"        vec⟨n⟩(x) ∧ vec⟨n⟩(y) ∧ ‖x - f(a)‖_n < ρ ∧ ‖y - a‖_n < σ ∧ f(y) = x ⇒ y = g(x)) ∧ " +
			"    vec_derivative_at⟨n, n⟩(g, f(a), K)",
	},
		func(
			arg *Argument,
			n *Expr[Nat],
			f, K *VecFun[Real, DimN, DimN],
			D *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Nat, Real]],
			a *Vec[Real, DimN],
			r *Expr[Real],
			aIn, rPos, fValues, derivatives, continuity, inverse Fact,
		) {
			// The hypotheses of ImplicitFunction at F(x, y) = f(y) − x, centred at (f(a), a).
			image := f.Apply(a)
			imageIn := arg.Have(
				"f(a) is an n-vector",
				"vec⟨n⟩(f(a))",
				By(fValues.At(a), aIn))
			root := arg.Have(
				"F(f(a), a) = f(a) − f(a) is zero",
				"f(a) - f(a) = vec_zero",
				By(vec_space.SubEqZero.Read(real_ring.CommRing).At(image, image)))
			values := arg.Have(
				"F(x, y) = f(y) − x carries ℝⁿ × ℝⁿ into ℝⁿ",
				"∀x y:(num → real). vec⟨n⟩(x) ∧ vec⟨n⟩(y) ⇒ vec⟨n⟩(f(y) - x)",
				Derive(func(d *Argument) {
					x := d.VecFixAs[Real, DimN]("x")
					y := d.VecFixAs[Real, DimN]("y")
					both := d.Conjuncts(
						d.Assume(),
						"x is an n-vector",
						"and so is y")
					valueIn := d.Have(
						"f(y) is an n-vector",
						"vec⟨n⟩(f(y))",
						By(fValues.At(y), both[1]))
					d.Show(
						"a difference of n-vectors",
						By(vec_space.VecSub.Read(real_ring.CommRing).At(
							proof.Inhabit(f.Apply(y), valueIn), proof.Inhabit(x, both[0]))))
				}))
			ofY := arg.Have(
				"y ↦ f(y) − x has f's derivative D(y), a constant shift changing no increment",
				Statement{
					Binders: "∀x y:(num → real).",
					Hypotheses: []string{
						"vec⟨n⟩(x)",
						"vec⟨n⟩(y)",
						"‖x - f(a)‖_n < r",
						"‖y - a‖_n < r",
					},
					Conclusion: "vec_derivative_at⟨n, n⟩(λv:(num → real). f(v) - x, y, D(y))",
				},
				Derive(func(d *Argument) {
					x := d.VecFixAs[Real, DimN]("x")
					y := d.VecFixAs[Real, DimN]("y")
					at := d.Conjuncts(
						d.Assume(),
						"x is an n-vector",
						"y is an n-vector",
						"x is within r of f(a)",
						"and y is within r of a")
					ofF := d.Have(
						"D(y) is f's derivative at y",
						"vec_derivative_at⟨n, n⟩(f, y, D(y))",
						By(derivatives.At(y), at[1], at[3]))
					constant := d.VecFunAs[Real, DimN, DimN]("λv:(num → real). x")
					zero := d.VecFunAs[Real, DimN, DimN]("λu:(num → real). vec_zero")
					minus := d.Have(
						"so y ↦ f(y) − x has the derivative u ↦ D(y)(u) − 0, the constant x having the derivative 0",
						"vec_derivative_at⟨n, n⟩(λv:(num → real). f(v) - x, y, λu:(num → real). D(y, u) - vec_zero)",
						By(
							ofF,
							vec_derivative.VecDerivativeConst.At(n, x, proof.Inhabit(y, at[1])),
							vec_derivative.VecDerivativeSub.At(f, constant, d.VecFunAs[Real, DimN, DimN]("D(y)"), zero, y)))
					dropZero := d.Have(
						"D(y)(u) − 0 is D(y)(u)",
						"∀u:(num → real). D(y, u) - vec_zero = D(y, u)",
						Derive(func(e *Argument) {
							e.FixAs[Fun[Nat, Real]]("u")
							e.Show(
								"subtracting zero changes nothing",
								Funext(),
								Unfold(vec_space.VecSubDef),
								Unfold(vec_space.VecZeroDef),
								ByArith())
						}))
					d.Show(
						"so the derivative is D(y), which agrees with u ↦ D(y)(u) − 0 at every point",
						By(minus, dropZero))
				}))
			dyContinuity := arg.Have(
				"Dy(x, y) = D(y) is continuous at (f(a), a)",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀x y:(num → real). " +
						"        vec⟨n⟩(x) ∧ vec⟨n⟩(y) ∧ ‖x - f(a)‖_n < δ ∧ ‖y - a‖_n < δ ⇒ " +
						"        vec_op_norm⟨n, n⟩(λv:(num → real). D(y, v) - D(a, v)) ≤ ε)",
				},
				By(continuity))
			identity := arg.VecFunAs[Real, DimN, DimN]("λu:(num → real). u")
			ofShift := arg.Have(
				"x ↦ f(a) − x has the derivative u ↦ 0 − u at f(a), the "+
					"constant f(a) having the derivative 0 and the identity itself",
				"vec_derivative_at⟨n, n⟩(λu:(num → real). f(a) - u, f(a), λu:(num → real). vec_zero - u)",
				By(
					vec_derivative.VecDerivativeConst.At(n, image, proof.Inhabit(image, imageIn)),
					vec_derivative.VecDerivativeIdentity.At(proof.Inhabit(image, imageIn)),
					vec_derivative.VecDerivativeSub.At(
						arg.VecFunAs[Real, DimN, DimN]("λu:(num → real). f(a)"),
						identity,
						arg.VecFunAs[Real, DimN, DimN]("λu:(num → real). vec_zero"),
						identity,
						image)))
			negation := arg.Have(
				"0 − u is −u",
				"∀u:(num → real). vec_zero - u = -u",
				Derive(func(d *Argument) {
					d.FixAs[Fun[Nat, Real]]("u")
					d.Show(
						"pointwise, 0 − u(i) is −u(i)",
						Funext(),
						Unfold(vec_space.VecSubDef),
						Unfold(vec_space.VecNegDef),
						Unfold(vec_space.VecZeroDef),
						ByArith())
				}))
			ofX := arg.Have(
				"so x ↦ f(a) − x has the derivative −id at f(a), which agrees with u ↦ 0 − u at every point",
				"vec_derivative_at⟨n, n⟩(λu:(num → real). f(a) - u, f(a), λu:(num → real). -u)",
				By(Normalized, ofShift, negation))

			// ImplicitFunction gives g, with the derivative u ↦ −K(−u) at f(a).
			ρ, σ, g, solved := arg.Unpack3As[Real, Real, Fun[Fun[Nat, Real], Fun[Nat, Real]]](
				GroupPremises(
					rPos,
					root,
					values,
					ofY,
					dyContinuity,
					ofX,
					inverse,
					ImplicitFunction.At(
						arg.TermAs[Fun2[Fun[Nat, Real], Fun[Nat, Real], Fun[Nat, Real]]](
							"λx:(num → real). λy:(num → real). f(y) - x"),
						arg.TermAs[Fun2[Fun[Nat, Real], Fun[Nat, Real], Fun[Fun[Nat, Real], Fun[Nat, Real]]]](
							"λx:(num → real). λy:(num → real). D(y)"),
						arg.VecFunAs[Real, DimN, DimN]("λu:(num → real). -u"),
						K,
						proof.Inhabit(image, imageIn),
						proof.Inhabit(a, aIn),
						r)),
				"ρ",
				"σ",
				"g")
			sol := arg.Conjuncts(
				solved,
				"ρ is positive",
				"σ is positive",
				"g(f(a)) = a",
				"near f(a), g(x) is an n-vector within σ of a with f(g(x)) − x zero",
				"and the only one",
				"and g has the derivative u ↦ −K(−u) at f(a)")

			// −K(−u) is K(u), K being linear.
			linear := arg.Conjuncts(
				arg.Unfolded(inverse, vec_derivative.VecInverseOnDef),
				"K is linear",
				"and on ℝⁿ it takes values in ℝⁿ and inverts D(a) on both sides")[0]
			homogeneous := arg.Conjuncts(
				arg.Unfolded(linear, vec_space.VecLinearDef),
				"K carries a sum to the sum of the images",
				"and commutes with scaling")[1]
			kNeg := arg.Have(
				"−K(−u) is K(u), K commuting with the scaling by −1",
				"∀u:(num → real). -K(-u) = K(u)",
				Derive(func(d *Argument) {
					u := d.FixAs[Fun[Nat, Real]]("u")
					minusOne := d.TermAs[Real]("-&1")
					scaled := d.Have(
						"−u is (−1)•u",
						"-u = (-&1) • u",
						Funext(),
						Unfold(vec_space.VecNegDef),
						Unfold(vec_space.VecScalarMulDef),
						ByArith())
					d.Show(
						"−((−1)•K(u)) is K(u)",
						scaled.Rw(),
						homogeneous.At(minusOne, u).Rw(),
						Funext(),
						Unfold(vec_space.VecNegDef),
						Unfold(vec_space.VecScalarMulDef),
						ByArith())
				}))
			// Maps that agree at every point are one map, so the slope u ↦ −K(−u) is K.
			derivative := arg.Have(
				"so g has the derivative K at f(a), which agrees with u ↦ −K(−u) at every point",
				"vec_derivative_at⟨n, n⟩(g, f(a), K)",
				By(Normalized, sol[5], kNeg))
			solves := arg.Have(
				"near f(a), g(x) is an n-vector within σ of a with f(g(x)) = x",
				"∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - f(a)‖_n < ρ ⇒ vec⟨n⟩(g(x)) ∧ ‖g(x) - a‖_n < σ ∧ f(g(x)) = x",
				Derive(func(d *Argument) {
					x := d.VecFixAs[Real, DimN]("x")
					near := d.Assume()
					atX := d.Conjuncts(
						GroupPremises(near, sol[3].At(x)),
						"g(x) is an n-vector",
						"within σ of a",
						"and f(g(x)) − x is zero")
					d.Show(
						"f(g(x)) − x is zero exactly when f(g(x)) = x",
						By(
							atX[0],
							atX[1],
							atX[2],
							vec_space.SubEqZero.Read(real_ring.CommRing).At(d.TermAs[Fun[Nat, Real]]("f(g(x))"), x)))
				}))
			only := arg.Have(
				"a solution y of f(y) = x within σ of a is g(x)",
				"∀x y:(num → real). vec⟨n⟩(x) ∧ vec⟨n⟩(y) ∧ ‖x - f(a)‖_n < ρ ∧ ‖y - a‖_n < σ ∧ f(y) = x ⇒ y = g(x)",
				Derive(func(d *Argument) {
					x := d.VecFixAs[Real, DimN]("x")
					y := d.VecFixAs[Real, DimN]("y")
					at := d.Conjuncts(
						d.Assume(),
						"x is an n-vector",
						"y is an n-vector",
						"x is within ρ of f(a)",
						"y is within σ of a",
						"and f(y) = x")
					zero := d.Have(
						"so f(y) − x is zero",
						"f(y) - x = vec_zero",
						By(at[4], vec_space.SubEqZero.Read(real_ring.CommRing).At(f.Apply(y), x)))
					d.Show(
						"a zero of f(·) − x within σ of a is g(x)",
						By(sol[4].At(x, y), at[0], at[1], at[2], at[3], zero))
				}))
			arg.Take(ρ)
			arg.Take(σ)
			arg.Take(g)
			arg.Show(
				"the radii, g(f(a)) = a, the solutions, and the derivative",
				By(sol[0], sol[1], sol[2], solves, only, derivative))
		}),
})}
