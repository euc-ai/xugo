// solution.go — the solution g(x): the fixed point of T on a closed ball about b.

package inverse_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_derivative"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ImplicitSolution — the implicit function theorem's solution: for x near
// a the equation F(x, y) = 0 has a solution y = g(x) near b, with
// g(a) = b, the only one within σ of b, and at most twice ‖K(F(x, b))‖
// from b. At such x the map T(y) = y − K(F(x, y)) halves distances within
// δ of b (ImplicitLipschitz at the factor 1/2); take σ = δ/2 and M the
// closed ball of radius σ about b, complete as a closed ball of ℝᵐ
// (euclidean_topology.ClosedBallComplete). T moves b by K(F(x, b)), which
// is below σ/2 once F(x, b) is below σ/(2‖K‖ + 2), ‖K‖ the operator norm
// (euclidean.OpNormBound); so T maps M into M, and Banach's theorem gives its
// one fixed point there. A fixed point p has K(F(x, p)) = 0, so
// F(x, p) = 0, K being one-to-one on ℝᵐ; and
// ‖p − b‖ ≤ ‖T(p) − T(b)‖ + ‖K(F(x, b))‖ ≤ ‖p − b‖/2 + ‖K(F(x, b))‖.
// A zero of F(x, ·) within σ of b is a fixed point of T in M, so it is p.
// The fixed points, chosen at each x, are g.
var ImplicitSolution = implicitSolutionThm{family.Add(registry.ProofEntry{
	Name: "ImplicitSolution",
	Key:  "prop_9b3776776ea95125",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. " +
			"∀F:((num → real) → (num → real) → (num → real)). " +
			"∀Dy:((num → real) → (num → real) → (num → real) → (num → real)). " +
			"∀K:((num → real) → (num → real)). " +
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
			"vec_inverse_on⟨m⟩(Dy(a, b), K)",
			"∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - a‖_n < δ ⇒ ‖F(x, b)‖_m < ε",
		},
		Conclusion: "∃ρ σ:real. ∃g:((num → real) → (num → real)). " +
			"    &0 < ρ ∧ " +
			"    &0 < σ ∧ " +
			"    g(a) = b ∧ " +
			"    (∀x:(num → real). " +
			"        vec⟨n⟩(x) ∧ ‖x - a‖_n < ρ ⇒ " +
			"        vec⟨m⟩(g(x)) ∧ " +
			"        ‖g(x) - b‖_m < σ ∧ " +
			"        F(x, g(x)) = vec_zero ∧ " +
			"        ‖g(x) - b‖_m ≤ &2 * ‖K(F(x, b))‖_m) ∧ " +
			"    (∀x y:(num → real). " +
			"        vec⟨n⟩(x) ∧ vec⟨m⟩(y) ∧ ‖x - a‖_n < ρ ∧ ‖y - b‖_m < σ ∧ F(x, y) = vec_zero ⇒ y = g(x))",
		Abbrev: Abbrev{
			{Name: "M", Text: "{u:(num → real) | vec⟨m⟩(u) ∧ ‖u - b‖_m ≤ σ}"},
			{Name: "T", Text: "λw:(num → real). w - K(F(x, w))"},
		},
	},
		func(arg *Argument, n, m *Expr[Nat], F *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Nat, Real]],
			Dy *Arrow2[Fun[Nat, Real], Fun[Nat, Real], Fun[Fun[Nat, Real], Fun[Nat, Real]]],
			K *VecFun[Real, DimM, DimM], a *Vec[Real, DimN], b *Vec[Real, DimM], r *Expr[Real],
			aIn, bIn, rPos, root, values, derivatives, continuity, inverse, start Fact) {
			halfPos := arg.Have(
				"the factor 1/2 is positive",
				"&0 < &1 / &2",
				ByArith())
			δ, contracting := arg.UnpackAs[Real](
				GroupPremises(
					rPos,
					values,
					derivatives,
					continuity,
					inverse,
					halfPos,
					ImplicitLipschitz.At(
						F, Dy, K, proof.Inhabit(a, aIn), proof.Inhabit(b, bIn), r, arg.TermAs[Real]("&1 / &2"))),
				"δ")
			contraction := arg.Conjuncts(
				contracting,
				"δ is positive",
				"and within δ of (a, b), T moves points at most half their distance")
			// σ = δ/2 puts the closed σ-ball about b inside the open δ-ball.
			σ, σDef := arg.LetAs[Real]("σ", "δ / &2")
			σBounds := arg.Have(
				"σ is positive and below δ",
				"&0 < σ ∧ σ < δ",
				ByArith(contraction[0], σDef))

			// K is linear, carries ℝᵐ into ℝᵐ, and stretches by at most ‖K‖.
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

			// The radius about a: within δ₂, F(x, b) is below ε = σ/(2‖K‖ + 2).
			ε, εDef := arg.LetAs[Real]("ε", "σ / (&2 * vec_op_norm⟨m, m⟩(K) + &2)")
			εPos := arg.Have(
				"ε is positive",
				"&0 < ε",
				ByArith(size, σBounds, εDef))
			unit := arg.Have(
				"2‖K‖ + 2 times ε is σ",
				"(&2 * vec_op_norm⟨m, m⟩(K) + &2) * ε = σ",
				ByArith(size, εDef))
			δ2, starting := arg.UnpackAs[Real](GroupPremises(εPos, start.At(ε)), "δ₂")
			startNear := arg.Conjuncts(
				starting,
				"δ₂ is positive",
				"and within δ₂ of a, F(x, b) is below ε")
			ρPos := arg.Have(
				"the radius min(δ, δ₂) is positive",
				"&0 < min(δ, δ₂)",
				By(contraction[0], startNear[0], real_sup_inf.LessThanMin.At(δ, δ2, arg.TermAs[Real]("&0"))))
			selfClose := arg.Have(
				"a lies within min(δ, δ₂) of a, and b within σ of b, each being at distance zero from itself",
				"‖a - a‖_n < min(δ, δ₂) ∧ ‖b - b‖_m < σ",
				ByArith(euclidean.NormSubRefl.At(n, a), euclidean.NormSubRefl.At(m, b), ρPos, σBounds))

			// M, the closed ball of radius σ about b: complete, a metric space, holding b.
			space := arg.TermAs[Set[Fun[Nat, Real]]]("{u:(num → real) | vec⟨m⟩(u)}")
			distance := arg.TermAs[Fun2[Fun[Nat, Real], Fun[Nat, Real], Real]]("vec_dist⟨m⟩")
			ball := arg.TermAs[Set[Fun[Nat, Real]]]("«M»")
			complete := arg.Have(
				"M, a closed ball of ℝᵐ, is complete",
				"metric_complete(«M», vec_dist⟨m⟩)",
				By(euclidean_topology.ClosedBallComplete.At(proof.Inhabit(b, bIn), σ)))
			inSpace := arg.Have(
				"M lies in ℝᵐ",
				"«M» ⊆ {u:(num → real) | vec⟨m⟩(u)}",
				BySets())
			metric := arg.Have(
				"so M is a metric space under the distance of ℝᵐ",
				"metric_space(«M», vec_dist⟨m⟩)",
				By(inSpace, euclidean.EuclideanMetric.At(m), metric_space.SubMetricSpace.At(space, distance, ball)))
			bInM := arg.Have(
				"b lies in M",
				"b ∈ «M»",
				By(bIn, selfClose, real_order_ring.LessEqOfLessThan))
			nonempty := arg.Have(
				"so M is not empty",
				"¬(«M» = ∅)",
				By(bInM, set_basic.MemberNotEmpty.At(ball)))
			half := arg.Have(
				"the factor 1/2 is below one",
				"&1 / &2 < &1",
				ByArith())

			// At each x near a, T maps M into itself and halves distances
			// there; its fixed point is the zero sought.
			solution := arg.Have(
				"for x within min(δ, δ₂) of a, F(x, ·) has a zero p within σ "+
					"of b, at most 2‖K(F(x, b))‖ from b, the only zero within σ of b",
				Statement{
					Binders: "∀x:(num → real).",
					Hypotheses: []string{
						"vec⟨n⟩(x)",
						"‖x - a‖_n < min(δ, δ₂)",
					},
					Conclusion: "∃p:(num → real). " +
						"    vec⟨m⟩(p) ∧ " +
						"    ‖p - b‖_m < σ ∧ " +
						"    F(x, p) = vec_zero ∧ " +
						"    ‖p - b‖_m ≤ &2 * ‖K(F(x, b))‖_m ∧ " +
						"    (∀w:(num → real). vec⟨m⟩(w) ∧ ‖w - b‖_m < σ ∧ F(x, w) = vec_zero ⇒ w = p)",
				},
				Derive(func(d *Argument) {
					x := d.VecFixAs[Real, DimN]("x")
					atX := d.Conjuncts(
						d.Assume(),
						"x is an n-vector",
						"within min(δ, δ₂) of a")
					xIn := atX[0]
					xClose := d.Have(
						"x is within δ and within δ₂ of a",
						"‖x - a‖_n < δ ∧ ‖x - a‖_n < δ₂",
						By(atX[1], real_sup_inf.LessThanMin.At(δ, δ2, d.TermAs[Real]("‖x - a‖_n"))))
					atB := d.VecAs[Real, DimM]("F(x, b)")
					atBIn := d.Have(
						"F(x, b) is an m-vector",
						"vec⟨m⟩(F(x, b))",
						By(values.At(x, b), xIn, bIn))
					small := d.Have(
						"F(x, b) is below ε, x lying within δ₂ of a",
						"‖F(x, b)‖_m < ε",
						By(startNear[1].At(x), xIn, xClose))
					shift := d.Have(
						"T moves b by K(F(x, b)), which ‖K‖ and F(x, b) < ε keep below σ/2",
						"‖K(F(x, b))‖_m < σ / &2",
						ByArith(
							euclidean.OpNormBound.At(K, proof.Inhabit(atB, atBIn)),
							linear,
							real_order_ring.LessEqMulLeft.At(
								d.TermAs[Real]("vec_op_norm⟨m, m⟩(K)"), d.TermAs[Real]("‖F(x, b)‖_m"), ε),
							size,
							small,
							unit,
							εPos))
					bMoved := d.VecAs[Real, DimM]("«T»(b)")
					flip := d.Have(
						"T(b) − b is −K(F(x, b))",
						"«T»(b) - b = (-&1) • K(F(x, b))",
						Funext(),
						Unfold(vec_space.VecSubDef),
						Unfold(vec_space.VecScalarMulDef),
						ByArith())
					step := d.Have(
						"so T(b) lies ‖K(F(x, b))‖ from b",
						"‖«T»(b) - b‖_m = ‖K(F(x, b))‖_m",
						flip.Rw(),
						ByArith(euclidean.NormSmul.At(d.TermAs[Real]("-&1"), d.VecAs[Real, DimM]("K(F(x, b))"))))
					detour := d.Have(
						"a point's distance from b is at most its distance from T(b) plus ‖K(F(x, b))‖",
						"∀u:(num → real). ‖u - b‖_m ≤ ‖u - «T»(b)‖_m + ‖K(F(x, b))‖_m",
						Derive(func(e *Argument) {
							u := e.VecFixAs[Real, DimM]("u")
							e.Show(
								"the triangle inequality through T(b)",
								By(euclidean.DistTriangle.At(u, bMoved, b), euclidean.VecDistDef, step))
						}))
					halves := d.Have(
						"on M, T halves distances, M lying within δ of b",
						"∀y z:(num → real). y ∈ «M» ∧ z ∈ «M» ⇒ ‖«T»(y) - «T»(z)‖_m ≤ ‖y - z‖_m / &2",
						Derive(func(e *Argument) {
							y := e.VecFixAs[Real, DimM]("y")
							z := e.VecFixAs[Real, DimM]("z")
							both := e.Conjuncts(
								e.Assume(),
								"y lies in M",
								"and so does z")
							atY := e.Conjuncts(
								both[0],
								"y is an m-vector",
								"within σ of b")
							atZ := e.Conjuncts(
								both[1],
								"z is an m-vector",
								"within σ of b")
							within := e.Have(
								"y and z lie within δ of b, σ being below δ",
								"‖y - b‖_m < δ ∧ ‖z - b‖_m < δ",
								ByArith(atY[1], atZ[1], σBounds))
							e.Show(
								"the contraction at x, a half of the distance being the distance halved",
								ByArith(contraction[1].At(x, y, z), xIn, atY[0], atZ[0], xClose, within))
						}))
					inDistance := d.Have(
						"in the distance of ℝᵐ, T contracts M by the factor 1/2",
						"∀y z:(num → real). y ∈ «M» ∧ z ∈ «M» ⇒ dist⟨m⟩(«T»(y), «T»(z)) ≤ &1 / &2 * dist⟨m⟩(y, z)",
						Derive(func(e *Argument) {
							y := e.VecFixAs[Real, DimM]("y")
							z := e.VecFixAs[Real, DimM]("z")
							both := e.Assume()
							e.Show(
								"the factor 1/2 read in norms",
								Simp(Fwd(euclidean.VecDistDef)),
								ByArith(halves.At(y, z), both))
						}))
					maps := d.Have(
						"T maps M into M: T(y) is within ‖y − b‖/2 of T(b), which is within σ/2 of b",
						"∀y:(num → real). y ∈ «M» ⇒ «T»(y) ∈ «M»",
						Derive(func(e *Argument) {
							y := e.VecFixAs[Real, DimM]("y")
							yInM := e.Assume()
							atY := e.Conjuncts(
								yInM,
								"y is an m-vector",
								"within σ of b")
							value := e.VecAs[Real, DimM]("K(F(x, y))")
							valueIn := e.Have(
								"K(F(x, y)) is an m-vector",
								"vec⟨m⟩(K(F(x, y)))",
								By(kValues, values.At(x, y), xIn, atY[0]))
							yMoved := e.VecAs[Real, DimM]("«T»(y)")
							near := e.Have(
								"T(y) is within σ of b",
								"‖«T»(y) - b‖_m ≤ σ",
								ByArith(detour.At(yMoved), halves.At(y, b), yInM, bInM, atY[1], shift))
							e.Show(
								"an m-vector within σ of b",
								By(
									vec_space.VecSub.Read(real_ring.CommRing).At(
										proof.Inhabit(y, atY[0]), proof.Inhabit(value, valueIn)),
									near))
						}))
					mapT := d.TermAs[Fun[Fun[Nat, Real], Fun[Nat, Real]]]("«T»")
					p, fixedPoint := d.UnpackAs[Fun[Nat, Real]](
						GroupPremises(
							metric,
							complete,
							nonempty,
							maps,
							half,
							inDistance,
							complete_metric.BanachFixedPoint.At(ball, distance, mapT, d.TermAs[Real]("&1 / &2"))),
						"p")
					fixed := d.Conjuncts(
						fixedPoint,
						"p lies in M",
						"T fixes p",
						"and p is the only fixed point of T in M")
					atP := d.Conjuncts(
						fixed[0],
						"p is an m-vector",
						"within σ of b")
					pv := d.VecAs[Real, DimM]("p")
					cancel := d.Have(
						"K(F(x, p)) is p less T(p)",
						"K(F(x, p)) = p - «T»(p)",
						Funext(),
						Unfold(vec_space.VecSubDef),
						ByArith())
					kp := d.Have(
						"so K(F(x, p)) is zero, T fixing p, and zero is K(vec_zero)",
						"K(F(x, p)) = K(vec_zero)",
						By(cancel, fixed[1], vec_space.SubEqZero.Read(real_ring.CommRing).At(pv, pv), kZero))
					value := d.VecAs[Real, DimM]("F(x, p)")
					valueIn := d.Have(
						"F(x, p) is an m-vector",
						"vec⟨m⟩(F(x, p))",
						By(values.At(x, pv), xIn, atP[0]))
					zero := d.VecAs[Real, DimM]("vec_zero")
					zeroIn := d.Have(
						"and so is the zero vector",
						"vec⟨m⟩(vec_zero)",
						By(vec_space.VecZero))
					zeroAtP := d.Have(
						"and F(x, p) is zero, K being one-to-one on ℝᵐ",
						"F(x, p) = vec_zero",
						By(
							inverse,
							kp,
							vec_derivative.InverseInjective.At(
								d.VecFunAs[Real, DimM, DimM]("Dy(a, b)"),
								K,
								proof.Inhabit(value, valueIn),
								proof.Inhabit(zero, zeroIn))))
					nearFixed := d.Have(
						"p, being fixed, is within half its distance from b of T(b)",
						"‖p - «T»(b)‖_m ≤ ‖p - b‖_m / &2",
						By(halves.At(pv, b), fixed[0], bInM, fixed[1]))
					bound := d.Have(
						"so ‖p − b‖ is at most twice ‖K(F(x, b))‖",
						"‖p - b‖_m ≤ &2 * ‖K(F(x, b))‖_m",
						ByArith(detour.At(pv), nearFixed))
					only := d.Have(
						"a zero of F(x, ·) within σ of b is a fixed point of T in M, so it is p",
						"∀w:(num → real). vec⟨m⟩(w) ∧ ‖w - b‖_m < σ ∧ F(x, w) = vec_zero ⇒ w = p",
						Derive(func(e *Argument) {
							w := e.VecFixAs[Real, DimM]("w")
							atW := e.Conjuncts(
								e.Assume(),
								"w is an m-vector",
								"within σ of b",
								"and a zero of F(x, ·)")
							wInM := e.Have(
								"w lies in M",
								"w ∈ «M»",
								By(atW[0], atW[1], real_order_ring.LessEqOfLessThan))
							e.Show(
								"T fixes the zero w, and the fixed point of T in M is p",
								By(fixed[2].At(w), wInM, linear, atW[2], ZeroIsFixedPoint.At(F, K, x, w)))
						}))
					pClose := d.Have(
						"so p lies within σ of b",
						"‖p - b‖_m < σ",
						ByArith(bound, shift))
					d.Take(p)
					d.Show(
						"p is an m-vector within σ of b, a zero of F(x, ·), and the only one",
						By(atP[0], pClose, zeroAtP, bound, only))
				}))

			g, chosen := arg.ObtainAs[Fun[Fun[Nat, Real], Fun[Nat, Real]]](
				"choose the zero g(x) at each x",
				"∃g:((num → real) → (num → real)). ∀x:(num → real). "+
					"    vec⟨n⟩(x) ∧ ‖x - a‖_n < min(δ, δ₂) ⇒ "+
					"    vec⟨m⟩(g(x)) ∧ "+
					"    ‖g(x) - b‖_m < σ ∧ "+
					"    F(x, g(x)) = vec_zero ∧ "+
					"    ‖g(x) - b‖_m ≤ &2 * ‖K(F(x, b))‖_m ∧ "+
					"    (∀w:(num → real). vec⟨m⟩(w) ∧ ‖w - b‖_m < σ ∧ F(x, w) = vec_zero ⇒ w = g(x))",
				By(solution))
			atA := arg.Conjuncts(
				GroupPremises(aIn, selfClose, chosen.At(a)),
				"g(a) is an m-vector",
				"within σ of b",
				"a zero of F(a, ·)",
				"at most 2‖K(F(a, b))‖ from b",
				"and the only zero of F(a, ·) within σ of b")
			atCentre := arg.Have(
				"g(a) = b: b is a zero of F(a, ·) within σ of b",
				"g(a) = b",
				By(atA[4].At(b), bIn, selfClose, root))
			arg.Take(arg.TermAs[Real]("min(δ, δ₂)"))
			arg.Take(σ)
			arg.Take(g)
			arg.Show(
				"the radii are positive, and g is the solution chosen",
				By(ρPos, σBounds, atCentre, chosen))
		}),
})}
