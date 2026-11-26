// contraction.go — T(y) = y − K(F(x, y)) fixes the zeros of F(x, ·) and contracts near (a, b).

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

// ZeroIsFixedPoint — T fixes every zero y of F(x, ·): there T(y) is
// y − K(0), and K, being linear, keeps zero.
var ZeroIsFixedPoint = zeroIsFixedPointThm{family.Add(registry.ProofEntry{
	Name: "ZeroIsFixedPoint",
	Key:  "prop_d29a444587366f0",
	Build: family.Theorem(Statement{
		Binders: "∀F:((num → real) → (num → real) → (num → real)). " +
			"∀K:((num → real) → (num → real)). " +
			"∀x y:(num → real).",
		Hypotheses: []string{
			"vec_linear(K)",
			"F(x, y) = vec_zero",
		},
		Conclusion: "«T»(y) = y",
		Abbrev: Abbrev{
			{Name: "T", Text: "λw:(num → real). w - K(F(x, w))"},
		},
	},
		func(
			arg *Argument,
			F *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Nat, Real]],
			K *Expr[Fun[Fun[Nat, Real], Fun[Nat, Real]]],
			x, y *Expr[Fun[Nat, Real]],
			linear, zero Fact,
		) {
			kZero := arg.Have(
				"K, being linear, keeps zero",
				"K(vec_zero) = vec_zero",
				By(linear, vec_space.LinearVecZero.Read(real_ring.CommRing).At(K)))
			arg.Show(
				"so T(y) is y − 0, which is y",
				zero.Rw(),
				kZero.Rw(),
				Funext(),
				Unfold(vec_space.VecSubDef),
				Unfold(vec_space.VecZeroDef),
				ByArith())
		}),
})}

// ImplicitLipschitz — near (a, b) the map T(y) = y − K(F(x, y)) moves
// points as little as we like: for every κ > 0, within some δ of (a, b)
// it brings any two points y and z to within κ times their distance,
// uniformly in x, where K inverts Dy(a, b), the derivative of F in y at
// (a, b). Its derivative T' at a point v is u ↦ u − K(Dy(x, v)(u)): the
// identity less K ∘ Dy(x, v), by the chain rule, K being its own
// derivative. As K undoes Dy(a, b) and is linear, T'(u) is K applied to
// Dy(a, b)(u) − Dy(x, v)(u). K stretches no vector by more than its
// operator norm ‖K‖ (euclidean.OpNormBound), and near (a, b) the
// continuity of Dy keeps the operator norm of Dy(x, v) − Dy(a, b) below
// κ/(‖K‖ + 1), so T' stretches no vector by more than κ, and its
// operator norm is at most κ (euclidean.OpNormLessEqIff). The radius is
// the smaller of the one that continuity serves and the radius r on which
// the derivatives exist. The ball is convex (euclidean.SegmentInBall), so
// the mean value inequality along the segment from z to y gives the
// factor κ.
var ImplicitLipschitz = implicitLipschitzThm{family.Add(registry.ProofEntry{
	Name: "ImplicitLipschitz",
	Key:  "prop_58ea3d91390e6e76",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. " +
			"∀F:((num → real) → (num → real) → (num → real)). " +
			"∀Dy:((num → real) → (num → real) → (num → real) → (num → real)). " +
			"∀K:((num → real) → (num → real)). " +
			"∀a b:(num → real). " +
			"∀r κ:real.",
		Hypotheses: []string{
			"vec⟨n⟩(a)",
			"vec⟨m⟩(b)",
			"&0 < r",
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
			"vec_inverse_on⟨m⟩(Dy(a, b), K)",
			"&0 < κ",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ " +
			"    ∀x y z:(num → real). " +
			"        vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ vec⟨m⟩(z) ∧ ‖x - a‖_n < δ ∧ ‖y - b‖_m < δ ∧ ‖z - b‖_m < δ ⇒ " +
			"        ‖y - K(F(x, y)) - (z - K(F(x, z)))‖_m ≤ κ * ‖y - z‖_m",
		Abbrev: Abbrev{
			{Name: "tolerance", Text: "κ / (vec_op_norm⟨m, m⟩(K) + &1)"},
			{Name: "T", Text: "λw:(num → real). w - K(F(x, w))"},
		},
	},
		func(arg *Argument, n, m *Expr[Nat], F *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Nat, Real]],
			Dy *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Fun[Nat, Real], Fun[Nat, Real]]],
			K *VecFun[Real, DimM, DimM], a *Vec[Real, DimN], b *Vec[Real, DimM], r, κ *Expr[Real],
			aIn, bIn, rPos, values, derivatives, continuity, inverse, factor Fact) {
			// K's three properties: it is linear, it carries ℝᵐ into ℝᵐ, and
			// there it undoes Dy(a, b).
			inverts := arg.Conjuncts(
				arg.Unfolded(inverse, vec_derivative.VecInverseOnDef),
				"K is linear",
				"and on ℝᵐ it takes values in ℝᵐ and inverts Dy(a, b) on both sides")
			linear := inverts[0]
			kValues := arg.Have(
				"K carries ℝᵐ into ℝᵐ",
				"∀h:(num → real). vec⟨m⟩(h) ⇒ vec⟨m⟩(K(h))",
				By(inverts[1]))
			kUndoes := arg.Have(
				"and undoes Dy(a, b) there",
				"∀h:(num → real). vec⟨m⟩(h) ⇒ K(Dy(a, b, h)) = h",
				By(inverts[1]))
			size := arg.Have(
				"the operator norm of K is not negative",
				"&0 ≤ vec_op_norm⟨m, m⟩(K)",
				By(linear, euclidean.OpNormNonneg.At(K)))

			// Dy(a, b) is the derivative at the centre, so it too carries ℝᵐ
			// into ℝᵐ.
			atCentre := arg.Have(
				"Dy(a, b) is the derivative of F(a, ·) at b, (a, b) being at distance zero from itself",
				"vec_derivative_at⟨m, m⟩(λv:(num → real). F(a, v), b, Dy(a, b))",
				ByArith(
					derivatives.At(a, b),
					aIn,
					bIn,
					rPos,
					euclidean.NormSubRefl.At(n, a),
					euclidean.NormSubRefl.At(m, b)))
			centre := arg.Conjuncts(
				arg.Unfolded(atCentre, vec_derivative.VecDerivativeAtDef),
				"b is an m-vector",
				"Dy(a, b) is linear",
				"Dy(a, b) carries ℝᵐ into ℝᵐ",
				"and approximates F(a, ·) near b")
			centreLinear, centreValues := centre[1], centre[2]

			// The tolerance κ/(‖K‖ + 1): positive, and ‖K‖ times it is at most κ.
			tolerance := arg.TermAs[Real]("«tolerance»")
			tolerancePos := arg.Have(
				"the tolerance κ/(‖K‖ + 1) is positive",
				"&0 < «tolerance»",
				ByArith(size, factor))
			unit := arg.Have(
				"‖K‖ + 1 times the tolerance is κ",
				"(vec_op_norm⟨m, m⟩(K) + &1) * «tolerance» = κ",
				ByArith(size))
			small := arg.Have(
				"so ‖K‖ times the tolerance is at most κ",
				"vec_op_norm⟨m, m⟩(K) * «tolerance» ≤ κ",
				ByArith(unit, tolerancePos))
			δ1, radius := arg.UnpackAs[Real](GroupPremises(tolerancePos, continuity.At(tolerance)), "δ₁")
			near := arg.Conjuncts(
				radius,
				"δ₁ is positive",
				"and within δ₁ of (a, b), the operator norm of Dy(x, y) − Dy(a, b) is at most the tolerance")

			arg.Take(arg.TermAs[Real]("min(δ₁, r)"))
			arg.Do(SplitConj(
				Case(
					"the radius min(δ₁, r) is positive",
					By(near[0], rPos, real_sup_inf.LessThanMin.At(δ1, r, arg.TermAs[Real]("&0")))),
				Case(
					"within it, T moves points at most κ times their distance",
					Derive(func(d *Argument) {
						x := d.VecFixAs[Real, DimN]("x")
						y := d.VecFixAs[Real, DimM]("y")
						z := d.VecFixAs[Real, DimM]("z")
						inBall := d.Conjuncts(
							d.Assume(),
							"x is an n-vector",
							"y is an m-vector",
							"z is an m-vector",
							"x is within min(δ₁, r) of a",
							"y is within min(δ₁, r) of b",
							"and so is z")
						xIn, yIn, zIn := inBall[0], inBall[1], inBall[2]
						xClose := d.Have(
							"x is within δ₁ and within r of a",
							"‖x - a‖_n < δ₁ ∧ ‖x - a‖_n < r",
							By(inBall[3], real_sup_inf.LessThanMin.At(δ1, r, d.TermAs[Real]("‖x - a‖_n"))))
						slice := d.Have(
							"F(x, ·) carries ℝᵐ into ℝᵐ",
							"∀w:(num → real). vec⟨m⟩(w) ⇒ vec⟨m⟩(F(x, w))",
							By(values, xIn))

						local := d.Have(
							"at every point v of the ball, T has the derivative "+
								"u ↦ u − K(Dy(x, v)(u)), of operator norm at most κ",
							Statement{
								Binders: "∀v:(num → real).",
								Hypotheses: []string{
									"vec⟨m⟩(v)",
									"‖v - b‖_m < min(δ₁, r)",
								},
								Conclusion: "vec_derivative_at⟨m, m⟩(«T», v, λu:(num → real). u - K(Dy(x, v, u))) ∧ " +
									"vec_op_norm⟨m, m⟩(λu:(num → real). u - K(Dy(x, v, u))) ≤ κ",
							},
							Derive(func(e *Argument) {
								v := e.VecFixAs[Real, DimM]("v")
								atV := e.Conjuncts(
									e.Assume(),
									"v is an m-vector",
									"within min(δ₁, r) of b")
								vIn := atV[0]
								vClose := e.Have(
									"v is within δ₁ and within r of b",
									"‖v - b‖_m < δ₁ ∧ ‖v - b‖_m < r",
									By(atV[1], real_sup_inf.LessThanMin.At(δ1, r, e.TermAs[Real]("‖v - b‖_m"))))
								ofF := e.Have(
									"Dy(x, v) is the derivative of F(x, ·) at v",
									"vec_derivative_at⟨m, m⟩(λw:(num → real). F(x, w), v, Dy(x, v))",
									By(derivatives.At(x, v), xIn, vIn, xClose, vClose))
								slopeParts := e.Conjuncts(
									e.Unfolded(ofF, vec_derivative.VecDerivativeAtDef),
									"v is an m-vector",
									"Dy(x, v) is linear",
									"Dy(x, v) carries ℝᵐ into ℝᵐ",
									"and approximates F(x, ·) near v")
								dyLinear, dyValues := slopeParts[1], slopeParts[2]

								// The derivative: the identity less K ∘ Dy(x, v).
								image := e.VecAs[Real, DimM]("F(x, v)")
								imageIn := e.Have(
									"F(x, v) is an m-vector",
									"vec⟨m⟩(F(x, v))",
									By(slice.At(v), vIn))
								ofK := e.Have(
									"K, being linear, is its own derivative at F(x, v)",
									"vec_derivative_at⟨m, m⟩(K, F(x, v), K)",
									By(linear, kValues, vec_derivative.VecDerivativeLinear.At(K, proof.Inhabit(image, imageIn))))
								fiber := e.VecFunAs[Real, DimM, DimM]("λw:(num → real). F(x, w)")
								slope := e.VecFunAs[Real, DimM, DimM]("Dy(x, v)")
								// The chain rule asks F(x, ·) to carry the m-vectors within
								// some radius of v into ℝᵐ; it carries all of ℝᵐ there, so
								// any positive radius serves, r among them.
								ofComposite := e.Have(
									"so by the chain rule K(F(x, ·)) has the derivative K ∘ Dy(x, v) at v",
									"vec_derivative_at⟨m, m⟩(λw:(num → real). K(F(x, w)), v, λu:(num → real). K(Dy(x, v, u)))",
									By(
										ofF,
										ofK,
										rPos,
										slice,
										vec_derivative.VecDerivativeChain.At(fiber, K, slope, K, v, r),
										functions.ComposeApply))
								identity := e.VecFunAs[Real, DimM, DimM]("λu:(num → real). u")
								derivative := e.Have(
									"the identity is its own derivative, so T = id − K(F(x, "+
										"·)) has the derivative u ↦ u − K(Dy(x, v)(u)) at v",
									"vec_derivative_at⟨m, m⟩(«T», v, λu:(num → real). u - K(Dy(x, v, u)))",
									By(
										vec_derivative.VecDerivativeIdentity.At(proof.Inhabit(v, vIn)),
										ofComposite,
										vec_derivative.VecDerivativeSub.At(
											identity,
											e.VecFunAs[Real, DimM, DimM]("λw:(num → real). K(F(x, w))"),
											identity,
											e.VecFunAs[Real, DimM, DimM]("λu:(num → real). K(Dy(x, v, u))"),
											v)))

								// The bound: u − K(Dy(x, v)(u)) is K of Dy(a, b)(u) − Dy(x, v)(u).
								gapNorm := GroupPremises(xIn, vIn, xClose, vClose, near[1].At(x, v))
								gapMap := e.VecFunAs[Real, DimM, DimM]("λw:(num → real). Dy(x, v, w) - Dy(a, b, w)")
								gapLinear := e.Have(
									"Dy(x, v) − Dy(a, b), a difference of linear maps, is linear",
									"vec_linear(λw:(num → real). Dy(x, v, w) - Dy(a, b, w))",
									Simp(
										Fwd(vec_space.SubAddNeg.Read(real_ring.CommRing)),
										Fwd(vec_space.NegIsSmul.Read(real_ring.CommRing))),
									By(
										dyLinear,
										centreLinear,
										vec_space.LinearAdd.Read(real_ring.CommRing).At(
											slope,
											e.VecFunAs[Real, DimM, DimM]("λw:(num → real). -&1 • Dy(a, b, w)")),
										vec_space.LinearScale.Read(real_ring.CommRing).At(
											e.VecFunAs[Real, DimM, DimM]("Dy(a, b)"),
											e.TermAs[Real]("-&1"))))
								pointwise := e.Have(
									"u − K(Dy(x, v)(u)) is at most κ times u in norm, on ℝᵐ",
									"∀h:(num → real). vec⟨m⟩(h) ⇒ ‖h - K(Dy(x, v, h))‖_m ≤ κ * ‖h‖_m",
									Derive(func(c *Argument) {
										h := c.VecFixAs[Real, DimM]("h")
										hIn := c.Assume()
										atCentreH := c.VecAs[Real, DimM]("Dy(a, b, h)")
										atVH := c.VecAs[Real, DimM]("Dy(x, v, h)")
										gap := c.VecAs[Real, DimM]("Dy(a, b, h) - Dy(x, v, h)")
										gapIn := c.Have(
											"Dy(a, b)(h) − Dy(x, v)(h) is an m-vector",
											"vec⟨m⟩(Dy(a, b, h) - Dy(x, v, h))",
											By(centreValues.At(h), dyValues.At(h), hIn, vec_space.VecSub.Read(real_ring.CommRing)))
										undone := c.Have(
											"K undoes Dy(a, b) at h and is linear, so h − K(Dy(x, v)(h)) is K of the gap",
											"h - K(Dy(x, v, h)) = K(Dy(a, b, h) - Dy(x, v, h))",
											By(linear, kUndoes.At(h), hIn, vec_space.LinearSub.Read(real_ring.CommRing).At(K, atCentreH, atVH)))
										turned := c.Have(
											"the gap has the norm of Dy(x, v)(h) − Dy(a, b)(h)",
											"‖Dy(a, b, h) - Dy(x, v, h)‖_m = ‖Dy(x, v, h) - Dy(a, b, h)‖_m",
											By(euclidean.DistSym.At(atCentreH, atVH), euclidean.VecDistDef))
										gapBound := c.Have(
											"which Dy(x, v) − Dy(a, b) stretches from h by at most its operator norm, at most the tolerance",
											"‖Dy(x, v, h) - Dy(a, b, h)‖_m ≤ «tolerance» * ‖h‖_m",
											ByArith(
												euclidean.OpNormBound.At(gapMap, proof.Inhabit(h, hIn)),
												gapLinear,
												gapNorm,
												euclidean.NormNonneg.At(h),
												real_order_ring.LessEqMulRight.At(
													c.TermAs[Real]("vec_op_norm⟨m, m⟩(λw:(num → real). Dy(x, v, w) - Dy(a, b, w))"),
													tolerance,
													c.TermAs[Real]("‖h‖_m"))))
										c.Show(
											"K stretches the gap by at most ‖K‖, and the gap is at most the tolerance times ‖h‖",
											undone.Rw(),
											ByArith(
												turned,
												size,
												small,
												gapBound,
												euclidean.OpNormBound.At(K, proof.Inhabit(gap, gapIn)),
												linear,
												euclidean.NormNonneg.At(h)))
									}))
								linearT := e.Conjuncts(
									e.Unfolded(derivative, vec_derivative.VecDerivativeAtDef),
									"v is an m-vector",
									"the derivative is linear",
									"it carries ℝᵐ into ℝᵐ",
									"and approximates T near v")[1]
								e.Show(
									"the derivative, whose operator norm κ bounds, as κ bounds every stretch",
									By(
										derivative,
										pointwise,
										linearT,
										factor,
										real_order_ring.LessEqOfLessThan.At(e.TermAs[Real]("&0"), κ),
										euclidean.OpNormLessEqIff.At(
											e.VecFunAs[Real, DimM, DimM]("λu:(num → real). u - K(Dy(x, v, u))"),
											κ)))
							}))

						mapT := d.VecFunAs[Real, DimM, DimM]("«T»")
						along := d.Have(
							"at each point z + t•(y − z) of the segment, T has a derivative of operator norm at most κ",
							Statement{
								Binders: "∀t:real.",
								Hypotheses: []string{
									"&0 ≤ t",
									"t ≤ &1",
								},
								Conclusion: "∃L:((num → real) → (num → real)). " +
									"    vec_derivative_at⟨m, m⟩(«T», z + t • (y - z), L) ∧ vec_op_norm⟨m, m⟩(L) ≤ κ",
							},
							Derive(func(e *Argument) {
								t := e.FixAs[Real]("t")
								inside := e.Assume()
								point := e.VecAs[Real, DimM]("z + t • (y - z)")
								pointIn := e.Have(
									"the point z + t•(y − z) is an m-vector",
									"vec⟨m⟩(z + t • (y - z))",
									By(
										zIn,
										vec_space.VecSub.Read(real_ring.CommRing).At(proof.Inhabit(y, yIn), proof.Inhabit(z, zIn)),
										vec_space.VecAdd.Read(real_ring.CommRing),
										vec_space.VecSmul.Read(real_ring.CommRing)))
								pointClose := e.Have(
									"and lies in the ball, which is convex",
									"‖z + t • (y - z) - b‖_m < min(δ₁, r)",
									By(
										inBall[5],
										inBall[4],
										inside,
										euclidean.SegmentInBall.At(m, b, z, y, e.TermAs[Real]("min(δ₁, r)"), t)))
								e.Take(e.VecFunAs[Real, DimM, DimM]("λu:(num → real). u - K(Dy(x, z + t • (y - z), u))"))
								e.Show(
									"the derivative found at every point of the ball",
									By(local.At(point), pointIn, pointClose))
							}))
						d.Show(
							"by the mean value inequality from z to y, T(y) − T(z) is at most κ times ‖y − z‖ in norm",
							ByArith(
								along,
								vec_derivative.MeanValueInequality.At(mapT, proof.Inhabit(z, zIn), proof.Inhabit(y, yIn), κ)))
					}))))
		}),
})}
