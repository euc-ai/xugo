// partials.go — partial derivatives: the derivative determines them,
// continuous partials make a derivative, and mixed partials commute.

package vec_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// PartialAlongLine — f has partial derivative d along the coordinate j at
// the point x + s·e_j exactly when t ↦ f(x + t·e_j) has derivative d at s.
// The line through x + s·e_j, read from 0, is the line through x read from
// s: each is the other composed with a translation of ℝ, whose derivative
// is 1, so the chain rule carries the derivative across once the two
// parametrizations are seen to visit the same points.
var PartialAlongLine = partialAlongLineThm{family.Add(registry.ProofEntry{
	Name: "PartialAlongLine",
	Key:  "prop_b2e1f6286319f93c",
	Build: family.Theorem(
		"∀f:((num → real) → real). ∀j:num. ∀x:(num → real). ∀s d:real. "+
			"    partial_derivative_at(f, j, x + s • basis_vector(j), d) ⇔ "+
			"    real_derivative_at(λt:real. f(x + t • basis_vector(j)), s, d)",
		func(
			a *Argument,
			f *Arrow[Fun[Nat, Real], Real],
			j *Expr[Nat],
			x *Expr[Fun[Nat, Real]],
			s, d *Expr[Real],
		) {
			zero := a.TermAs[Real]("&0")
			one := a.TermAs[Real]("&1")
			line := a.TermAs[Fun[Real, Real]]("λt:real. f(x + t • basis_vector(j))")
			shifted := a.TermAs[Fun[Real, Real]]("λt:real. f(x + s • basis_vector(j) + t • basis_vector(j))")
			a.Iff()
			a.Forward(
				"the line through x + s·e_j read from 0, translated back by s, is the line through x read from s",
				func(b *Argument, partial Fact) {
					atZero := b.Have(
						"the line through x + s·e_j has derivative d at s − s = 0",
						"real_derivative_at(λt:real. f(x + s • basis_vector(j) + t • basis_vector(j)), s - s, d)",
						By(b.Unfolded(partial, PartialDerivativeAtDef), real_ring.SubRefl.At(s)))
					back := b.TermAs[Fun[Real, Real]]("λy:real. y - s")
					translation := b.Have(
						"y ↦ y − s has derivative 1",
						"real_derivative_at(λy:real. y - s, s, &1)",
						By(
							Normalized,
							real_derivative.DerivativeSub.At(
								b.TermAs[Fun[Real, Real]]("λy:real. y"),
								b.TermAs[Fun[Real, Real]]("λy:real. s"),
								s,
								one,
								zero),
							real_derivative.DerivativeId,
							real_derivative.DerivativeConst,
							real_ring.SubRightZero.At(one)))
					composite := b.Have(
						"so by the chain rule the composite has derivative d·1 at s",
						"real_derivative_at( "+
							"    (λt:real. f(x + s • basis_vector(j) + t • basis_vector(j))) ∘ (λy:real. y - s), s, d * &1)",
						By(atZero, translation, real_derivative.DerivativeChain.At(shifted, back, s, d, one)))
					samePoints := b.Have(
						"translated back, the line through x + s·e_j visits the points of the line through x",
						"∀y:real. x + s • basis_vector(j) + (y - s) • basis_vector(j) = x + y • basis_vector(j)",
						b.ForEach(func(y *Expr[Real]) Action {
							return Chain(Funext(), Unfold(vec_space.VecAddDef), Unfold(vec_space.VecScalarMulDef), ByArith())
						}))
					b.Show(
						"so the composite is t ↦ f(x + t·e_j), with derivative d at s",
						By(b.Simplified(
							b.Unfolded(composite, functions.ComposeApply),
							Fwd(samePoints),
							Fwd(real_ring.MulRightId))))
				})
			a.Backward(
				"the line through x read from s, translated forward "+
					"by s, is the line through x + s·e_j read from 0",
				func(b *Argument, derivative Fact) {
					atS := b.Have(
						"the line through x has derivative d at s + 0",
						"real_derivative_at(λt:real. f(x + t • basis_vector(j)), s + &0, d)",
						By(derivative, real_ring.AddRightId.At(s)))
					forward := b.TermAs[Fun[Real, Real]]("λt:real. s + t")
					translation := b.Have(
						"t ↦ s + t has derivative 1",
						"real_derivative_at(λt:real. s + t, &0, &1)",
						By(
							Normalized,
							real_derivative.DerivativeAdd.At(
								b.TermAs[Fun[Real, Real]]("λt:real. s"),
								b.TermAs[Fun[Real, Real]]("λt:real. t"),
								zero,
								zero,
								one),
							real_derivative.DerivativeConst,
							real_derivative.DerivativeId,
							real_construction.AddLeftId.At(one)))
					composite := b.Have(
						"so by the chain rule the composite has derivative d·1 at 0",
						"real_derivative_at((λt:real. f(x + t • basis_vector(j))) ∘ (λt:real. s + t), &0, d * &1)",
						By(atS, translation, real_derivative.DerivativeChain.At(line, forward, zero, d, one)))
					samePoints := b.Have(
						"translated forward, the line through x visits the points of the line through x + s·e_j",
						"∀t:real. x + (s + t) • basis_vector(j) = x + s • basis_vector(j) + t • basis_vector(j)",
						b.ForEach(func(t *Expr[Real]) Action {
							return Chain(Funext(), Unfold(vec_space.VecAddDef), Unfold(vec_space.VecScalarMulDef), ByArith())
						}))
					along := b.Unfolded(composite, functions.ComposeApply)
					b.Show(
						"so t ↦ f(x + s·e_j + t·e_j) has derivative d at 0, which is the partial along j",
						along.Simp(Fwd(samePoints), Fwd(real_ring.MulRightId)),
						Unfold(PartialDerivativeAtDef))
				})
		}),
})}

// PartialFromDerivative — the derivative determines the partial
// derivatives: the j-th partial derivative of the i-th coordinate of f at
// c is the i-th coordinate of L(e_j). The partial derivative is the
// derivative at 0 along the line through c in the direction e_j, an
// n-vector for j < n (DirectionalDerivative).
var PartialFromDerivative = partialFromDerivativeThm{family.Add(registry.ProofEntry{
	Name: "PartialFromDerivative",
	Key:  "prop_b253a07082eab17a",
	Build: family.Theorem(Statement{
		Binders: "∀n m i j:num. ∀f L:((num → real) → (num → real)). ∀c:(num → real).",
		Hypotheses: []string{
			"vec_derivative_at⟨n, m⟩(f, c, L)",
			"j < n",
			"i < m",
		},
		Conclusion: "partial_derivative_at(λx:(num → real). f(x)(i), j, c, L(basis_vector(j))(i))",
	},
		func(
			a *Argument,
			n, m, i, j *Expr[Nat],
			f, L *VecFun[Real, DimN, DimM],
			c *Vec[Real, DimN],
			derivative, below, coordinate Fact,
		) {
			direction := a.VecAs[Real, DimN]("basis_vector(j)")
			directionIn := a.Have(
				"the basis vector e_j is an n-vector, j being below n",
				"vec⟨n⟩(basis_vector(j))",
				By(below, vec_space.VecBasisVector.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1"), n, j)))
			a.Do(Unfold(PartialDerivativeAtDef))
			a.Show(
				"the partial derivative is the derivative along the direction e_j",
				By(
					derivative,
					coordinate,
					DirectionalDerivative.At(i, f, L, c, proof.Inhabit(direction, directionIn))))
		}),
})}

// ContinuousPartialsIncrement — a real function on ℝⁿ whose partial
// derivatives exist near c and are continuous at c has, at c, the
// increment ⟪D(c), x − c⟫ up to an error small against ‖x − c‖.
//
// Put η = ε/(n + 1). One radius ρ serves every partial below n at once
// (real_order_ring.CommonRadius): on its ball every partial below n stays
// within η of its value at c; take δ = min(ρ, r)/(n + 1). Walk from c to x
// one coordinate at a time: Y(k) agrees with x below k and with c from k
// on, so Y(0) = c, Y(n) = x, and the k-th step adds
// (x(k) − c(k))·e_k. A point on the k-th step differs from c by at most δ in
// each coordinate, so lies within n·δ < min(ρ, r) of c. On that step
// t ↦ f(Y(k) + t·e_k) has the partial along k as its derivative
// (PartialAlongLine), within η of D(c)(k), so the mean value inequality
// against the slope D(c)(k) bounds the step's increment less
// D(c)(k)·(x(k) − c(k)) by η|x(k) − c(k)| ≤ η‖x − c‖. The n steps add up to
// f(x) − f(c) less ⟪D(c), x − c⟫, to within n·η‖x − c‖ ≤ ε‖x − c‖.
var ContinuousPartialsIncrement = continuousPartialsIncrementThm{family.Add(registry.ProofEntry{
	Name: "ContinuousPartialsIncrement",
	Key:  "prop_7d8929d8f775f427",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. " +
			"∀f:((num → real) → real). " +
			"∀D:((num → real) → (num → real)). " +
			"∀c:(num → real). " +
			"∀r ε:real.",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
			"&0 < r",
			"∀x:(num → real). ∀j:num. " +
				"    vec⟨n⟩(x) ∧ ‖x - c‖_n < r ∧ j < n ⇒ partial_derivative_at(f, j, x, D(x)(j))",
			"∀j:num. " +
				"    j < n ⇒ " +
				"    ∀η:real. " +
				"        &0 < η ⇒ " +
				"        ∃δ:real. &0 < δ ∧ ∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ |D(x)(j) - D(c)(j)| < η",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ " +
			"    ∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ |f(x) - f(c) - ⟪D(c), x - c⟫_n| ≤ ε * ‖x - c‖_n",
	},
		func(
			a *Argument,
			n *Expr[Nat],
			f *Arrow[Fun[Nat, Real], Real],
			D *Arrow[Fun[Nat, Real], Fun[Nat, Real]],
			c *Vec[Real, DimN],
			r, ε *Expr[Real],
			cIn, rPos, partials, continuous, εPos Fact,
		) {
			zero := a.TermAs[Real]("&0")
			η, ηDef := a.LetAs[Real]("η", "ε / (&n + &1)")
			ηPos := a.Have(
				"η is positive",
				"&0 < η",
				ByArith(ηDef, εPos, real_order_ring.NumNonneg.At(n)))
			ηScale := a.Have(
				"n + 1 copies of η make ε",
				"(&n + &1) * η = ε",
				ByArith(ηDef, real_order_ring.NumNonneg.At(n)))
			each := a.Have(
				"each partial below n stays within η of its value at c on some ball about c",
				Statement{
					Binders: "∀j:num.",
					Hypotheses: []string{
						"j < n",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ (∀x:(num → real). ‖x - c‖_n < δ ⇒ vec⟨n⟩(x) ⇒ |D(x)(j) - D(c)(j)| < η)",
				},
				a.ForEach(func(j *Expr[Nat]) Action { return By(continuous.At(j, η), ηPos) }))
			ρ, common := a.UnpackAs[Real](
				GroupPremises(
					each,
					real_order_ring.CommonRadius.At(
						n,
						a.TermAs[Fun[Fun[Nat, Real], Real]]("λx:(num → real). ‖x - c‖_n"),
						a.TermAs[Fun2[Nat, Fun[Nat, Real], Bool]](
							"λj:num. λx:(num → real). vec⟨n⟩(x) ⇒ |D(x)(j) - D(c)(j)| < η"))),
				"ρ")
			commonParts := a.Conjuncts(
				common,
				"so all of them do on one ball, of a positive radius ρ",
				"on which every partial below n is within η of its value at c")
			minPos := a.Have(
				"the smaller of ρ and r is positive",
				"&0 < min(ρ, r)",
				By(commonParts[0], rPos, real_sup_inf.LessThanMin.At(ρ, r, zero)))
			δ, δDef := a.LetAs[Real]("δ", "min(ρ, r) / (&n + &1)")
			δPos := a.Have(
				"δ is positive",
				"&0 < δ",
				ByArith(δDef, minPos, real_order_ring.NumNonneg.At(n)))
			δScale := a.Have(
				"n + 1 copies of δ make min(ρ, r)",
				"(&n + &1) * δ = min(ρ, r)",
				ByArith(δDef, real_order_ring.NumNonneg.At(n)))
			a.Take(δ)
			a.Do(SplitConj(
				Case(
					"the radius δ is positive",
					By(δPos)),
				Case(
					"and at every point x of the ball the walk from c to x bounds the increment",
					Derive(func(b *Argument) {
						x := b.VecFixAs[Real, DimN]("x")
						ball := b.Assume()
						xParts := b.Conjuncts(
							ball,
							"x is an n-vector",
							"x lies within δ of c")
						xc := b.VecAs[Real, DimN]("x - c")
						sub := b.TermAs[Op[Real]]("real_sub")
						cVanishes := b.Unfolded(cIn, vec_space.VecDef)
						xVanishes := b.Unfolded(xParts[0], vec_space.VecDef)
						coordsClose := b.Have(
							"every coordinate of x − c below n is less than δ in size",
							"∀i:num. i < n ⇒ |x(i) - c(i)| < δ",
							Derive(func(d *Argument) {
								i := d.FixAs[Nat]("i")
								below := d.Assume()
								d.Show(
									"a coordinate is at most the norm",
									ByArith(
										below,
										xParts[1],
										euclidean.ComponentLeNorm.At(i, xc),
										vec_space.VecSubDef.At(sub, x, c, i)))
							}))
						_, YDef := b.LetAs[Fun2[Nat, Nat, Real]]("Y", "λk:num. λi:num. COND(i < k, x(i), c(i))")
						start := b.Have(
							"the walk starts at c",
							"Y(0) = c",
							Funext(),
							YDef.Rw(),
							b.ForEach(func(i *Expr[Nat]) Action { return Chain(CondRewrite(), ByArith()) }))
						finish := b.Have(
							"and ends at x: from n on both x and c vanish",
							"Y(n) = x",
							Funext(),
							YDef.Rw(),
							b.ForEach(func(i *Expr[Nat]) Action {
								return Chain(
									CondRewrite(),
									Derive(func(d *Argument) {
										past := d.Assume()
										d.Show(
											"past n both coordinates are 0",
											ByArith(past, cVanishes.At(i), xVanishes.At(i)))
									}))
							}))
						steps := b.Have(
							"the k-th step moves the coordinate k from c(k) to x(k)",
							"∀k:num. Y(k) + (x(k) - c(k)) • basis_vector(k) = Y(suc(k))",
							b.ForEach(func(k *Expr[Nat]) Action {
								return Chain(
									Funext(),
									YDef.Rw(),
									Unfold(vec_space.VecAddDef),
									Unfold(vec_space.VecScalarMulDef),
									Unfold(vec_space.BasisVectorDef),
									b.ForEach(func(i *Expr[Nat]) Action { return Chain(CondRewrite(), ByArith()) }))
							}))
						rest := b.Have(
							"a step of 0 stays put",
							"∀k:num. Y(k) + &0 • basis_vector(k) = Y(k)",
							b.ForEach(func(k *Expr[Nat]) Action {
								return Chain(Funext(), Unfold(vec_space.VecAddDef), Unfold(vec_space.VecScalarMulDef), ByArith())
							}))
						near := b.Have(
							"on the k-th step, a point within δ of Y(k) is an n-vector within ρ and within r of c",
							Statement{
								Binders: "∀k:num. ∀t:real.",
								Hypotheses: []string{
									"k < n",
									"-δ < t",
									"t < δ",
								},
								Conclusion: "vec⟨n⟩(Y(k) + t • basis_vector(k)) ∧ " +
									"‖Y(k) + t • basis_vector(k) - c‖_n < ρ ∧ " +
									"‖Y(k) + t • basis_vector(k) - c‖_n < r",
							},
							Derive(func(d *Argument) {
								d.FixAs[Nat]("k")
								d.FixAs[Real]("t")
								on := d.Conjuncts(
									d.Assume(),
									"k lies below n",
									"t lies above −δ",
									"and below δ")
								p := d.VecAs[Real, DimN]("Y(k) + t • basis_vector(k) - c")
								coords := d.Have(
									"its coordinates differ from c's by x(i) − c(i) below k, by t at k, and not at all past k",
									"∀i:num. i < n ⇒ |(Y(k) + t • basis_vector(k) - c)(i)| ≤ δ",
									Derive(func(e *Argument) {
										i := e.FixAs[Nat]("i")
										below := e.Assume()
										e.Show(
											"each of the three is at most δ in size",
											Unfold(vec_space.VecSubDef),
											Unfold(vec_space.VecAddDef),
											Unfold(vec_space.VecScalarMulDef),
											Unfold(vec_space.BasisVectorDef),
											YDef.Rw(),
											CondRewrite(),
											ByArith(coordsClose.At(i), below, on[1], on[2]))
									}))
								member := d.Have(
									"Y(k) + t·e_k is an n-vector: past n it agrees with c, which vanishes there",
									"vec⟨n⟩(Y(k) + t • basis_vector(k))",
									Unfold(vec_space.VecDef),
									d.ForEach(func(i *Expr[Nat]) Action {
										return Derive(func(e *Argument) {
											past := e.Assume()
											e.Show(
												"past n, and so past k, the walk point is c's coordinate, which is 0",
												Unfold(vec_space.VecAddDef),
												Unfold(vec_space.VecScalarMulDef),
												Unfold(vec_space.BasisVectorDef),
												YDef.Rw(),
												CondRewrite(),
												ByArith(cVanishes.At(i), on[0], past))
										})
									}))
								bound := d.Have(
									"so its distance from c is at most n·δ, below min(ρ, r)",
									"‖Y(k) + t • basis_vector(k) - c‖_n < min(ρ, r)",
									ByArith(coords, δScale, δPos, euclidean.CoordinateNormBound.At(p, δ)))
								d.Show(
									"below min(ρ, r) is below each",
									By(
										member,
										bound,
										real_sup_inf.LessThanMin.At(ρ, r, d.TermAs[Real]("‖Y(k) + t • basis_vector(k) - c‖_n"))))
							}))
						increments := b.Have(
							"each step changes f by D(c)(k) times the step, to within η‖x − c‖",
							"∀k:num. k < n ⇒ |f(Y(suc(k))) - f(Y(k)) - D(c)(k) * (x(k) - c(k))| ≤ η * ‖x - c‖_n",
							Derive(func(d *Argument) {
								k := d.FixAs[Nat]("k")
								below := d.Assume()
								line := d.TermAs[Fun[Real, Real]]("λs:real. f(Y(k) + s • basis_vector(k))")
								slope := d.TermAs[Fun[Real, Real]]("λs:real. D(Y(k) + s • basis_vector(k))(k)")
								base := d.TermAs[Fun[Nat, Real]]("Y(k)")
								derivative := d.Have(
									"on ⟬−δ, δ⟭ the line through Y(k) along e_k carries f with the partial along k as its derivative",
									Statement{
										Binders: "∀t:real.",
										Hypotheses: []string{
											"-δ < t",
											"t < δ",
										},
										Conclusion: "real_derivative_at(λs:real. f(Y(k) + s • basis_vector(k)), " +
											"    t, " +
											"    D(Y(k) + t • basis_vector(k))(k))",
									},
									Derive(func(e *Argument) {
										t := e.FixAs[Real]("t")
										inside := e.Assume()
										point := e.TermAs[Fun[Nat, Real]]("Y(k) + t • basis_vector(k)")
										e.Show(
											"the point lies within r of c, where f has its partial along k",
											By(
												partials.At(point, k),
												near.At(k, t),
												below,
												inside,
												PartialAlongLine.At(f, k, base, t, e.TermAs[Real]("D(Y(k) + t • basis_vector(k))(k)"))))
									}))
								bound := d.Have(
									"and there the partial along k is within η of D(c)(k)",
									"∀t:real. -δ < t ∧ t < δ ⇒ |D(Y(k) + t • basis_vector(k))(k) - D(c)(k)| ≤ η",
									Derive(func(e *Argument) {
										t := e.FixAs[Real]("t")
										inside := e.Assume()
										point := e.TermAs[Fun[Nat, Real]]("Y(k) + t • basis_vector(k)")
										e.Show(
											"the point lies within ρ of c",
											ByArith(commonParts[1].At(point, k), near.At(k, t), below, inside))
									}))
								ends := d.Have(
									"both 0 and x(k) − c(k) lie in ⟬−δ, δ⟭",
									"-δ < &0 ∧ &0 < δ ∧ -δ < x(k) - c(k) ∧ x(k) - c(k) < δ",
									ByArith(coordsClose.At(k), below, δPos))
								h := d.TermAs[Real]("x(k) - c(k)")
								moved := d.Have(
									"so by the mean value inequality against the slope D(c)(k) the "+
										"step moves f by D(c)(k)·(x(k) − c(k)), to within η|x(k) − c(k)|",
									"|f(Y(k) + (x(k) - c(k)) • basis_vector(k)) - "+
										"f(Y(k) + &0 • basis_vector(k)) - "+
										"D(c)(k) * (x(k) - c(k) - &0)| ≤ "+
										"η * |x(k) - c(k) - &0|",
									By(
										derivative,
										bound,
										ends,
										real_derivative.MeanValueNearSlope.At(
											line, slope, d.TermAs[Real]("-δ"), δ, d.TermAs[Real]("D(c)(k)"), η, zero, h)))
								coordinate := d.Have(
									"|x(k) − c(k)| is at most ‖x − c‖",
									"|x(k) - c(k)| ≤ ‖x - c‖_n",
									ByArith(below, euclidean.ComponentLeNorm.At(k, xc), vec_space.VecSubDef.At(sub, x, c, k)))
								d.Show(
									"the step takes Y(k) to Y(suc k), and a step of 0 stays at Y(k)",
									ByArith(d.Simplified(moved, Fwd(steps), Fwd(rest), Fwd(real_ring.SubRightZero)), coordinate, ηPos))
							}))
						summand := b.TermAs[Fun[Nat, Real]]("λj:num. D(c)(j) * (x(j) - c(j))")
						walk := b.Have(
							"after k steps f has changed by the first k terms of ⟪D(c), x − c⟫, to within k·η‖x − c‖",
							"∀k:num. k ≤ n ⇒ |f(Y(k)) - f(c) - Σ_{j<k} D(c)(j) * (x(j) - c(j))| ≤ &k * (η * ‖x - c‖_n)",
							Derive(func(d *Argument) {
								k := d.Binder("k")
								d.Induct(k)
								d.Base(
									"no step taken: Y(0) = c and the empty sum is 0",
									ByArith(start, real_sum.BelowClauses))
								d.Step(
									"one more step adds the next term of the sum and at most η‖x − c‖ to the error",
									func(e *Argument, ih Fact) {
										last := e.Assume()
										e.Show(
											"the sum gains the term at k, and the k-th step is within η‖x − c‖ of it",
											ByArith(ih, last, increments.At(k), real_sum.BelowClauses.At(summand)))
									})
							}))
						dotSum := b.Have(
							"⟪D(c), x − c⟫ is the sum over the coordinates below n",
							"⟪D(c), x - c⟫_n = Σ_{j<n} D(c)(j) * (x(j) - c(j))",
							Simp(Fwd(euclidean.DotIsSum)),
							Unfold(vec_space.VecSubDef))
						b.Show(
							"after n steps the walk is at x, and n·η‖x − c‖ ≤ ε‖x − c‖",
							ByArith(
								walk.At(n),
								nat_order.LessEqRefl.At(n),
								dotSum,
								finish,
								ηPos,
								ηScale,
								euclidean.NormNonneg.At(xc)))
					})),
			))
		}),
})}

// ContinuousPartialsDerivative — a map from ℝⁿ to ℝᵐ whose coordinates have
// partial derivatives near c, continuous at c, has at c the derivative L
// that takes u to the vector of the products ⟪D(c)(i), u⟫ for i < m.
//
// L is linear because the form is linear in its second argument, coordinate
// by coordinate, and it carries every sequence to an m-vector, vanishing
// from m on. For the estimate, ContinuousPartialsIncrement read at each
// coordinate f(·)(i) with the tolerance η = ε/(m + 1) gives a ball about
// c, and real_order_ring.CommonRadius one ball for all m of them; on it
// every coordinate of f(x) − f(c) − L(x − c) below m is at most η‖x − c‖ in
// size, so its norm is at most m·η‖x − c‖ ≤ ε‖x − c‖.
var ContinuousPartialsDerivative = continuousPartialsDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ContinuousPartialsDerivative",
	Key:  "prop_4fbf9e6a4e0f092d",
	Build: family.Theorem(Statement{
		Binders: "∀n m:num. " +
			"∀f:((num → real) → (num → real)). " +
			"∀D:((num → real) → num → (num → real)). " +
			"∀c:(num → real). " +
			"∀r:real.",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
			"&0 < r",
			"∀x:(num → real). ∀i j:num. " +
				"    vec⟨n⟩(x) ∧ ‖x - c‖_n < r ∧ i < m ∧ j < n ⇒ " +
				"    partial_derivative_at(λy:(num → real). f(y)(i), j, x, D(x)(i)(j))",
			"∀i j:num. " +
				"    i < m ∧ j < n ⇒ " +
				"    ∀ε:real. " +
				"        &0 < ε ⇒ " +
				"        ∃δ:real. " +
				"            &0 < δ ∧ ∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ |D(x)(i)(j) - D(c)(i)(j)| < ε",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(f, " +
			"    c, " +
			"    λu:(num → real). λi:num. COND(i < m, ⟪D(c)(i), u⟫_n, &0))",
	},
		func(
			a *Argument,
			n, m *Expr[Nat],
			f *VecFun[Real, DimN, DimM],
			D *Arrow2[Fun[Nat, Real], Nat, Fun[Nat, Real]],
			c *Vec[Real, DimN],
			r *Expr[Real],
			cIn, rPos, partials, continuous Fact,
		) {
			_, LDef := a.LetAs[Fun2[Fun[Nat, Real], Nat, Real]](
				"L", "λu:(num → real). λi:num. COND(i < m, ⟪D(c)(i), u⟫_n, &0)")
			linear := a.Have(
				"L is linear: the form is linear in its second argument, coordinate by coordinate",
				"vec_linear(L)",
				Unfold(vec_space.VecLinearDef),
				LDef.Rw(),
				Simp(Fwd(dot.AddRight.Read(real_ring.CommRing)), Fwd(dot.SmulRight.Read(real_ring.CommRing))),
				SplitConj(
					Case(
						"it carries a sum to the sum of the images",
						Derive(func(b *Argument) {
							b.FixAs[Fun[Nat, Real]]("u")
							b.FixAs[Fun[Nat, Real]]("v")
							b.Show(
								"below m the coordinates add, and from m on both sides are 0",
								Funext(),
								Unfold(vec_space.VecAddDef),
								b.ForEach(func(i *Expr[Nat]) Action { return Chain(CondRewrite(), ByArith()) }))
						})),
					Case(
						"and a multiple to the multiple of the image",
						Derive(func(b *Argument) {
							b.FixAs[Real]("a")
							b.FixAs[Fun[Nat, Real]]("u")
							b.Show(
								"below m the coordinates scale, and from m on both sides are 0",
								Funext(),
								Unfold(vec_space.VecScalarMulDef),
								b.ForEach(func(i *Expr[Nat]) Action { return Chain(CondRewrite(), ByArith()) }))
						}))))
			into := a.Have(
				"L carries every n-vector to an m-vector: from m on its coordinates are 0",
				"∀u:(num → real). vec⟨n⟩(u) ⇒ vec⟨m⟩(L(u))",
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, Real]]("u")
					b.Assume()
					b.Show(
						"past m the condition i < m fails",
						Unfold(vec_space.VecDef),
						b.ForEach(func(i *Expr[Nat]) Action { return Chain(LDef.Rw(), CondRewrite(), ByArith()) }))
				}))
			estimate := a.Have(
				"near c the increment of f is L(x − c), to within ε‖x − c‖ for any ε > 0",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ " +
						"    (∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ ‖f(x) - f(c) - L(x - c)‖_m ≤ ε * ‖x - c‖_n)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Real]("ε")
					εPos := b.Assume()
					η, ηDef := b.LetAs[Real]("η", "ε / (&m + &1)")
					ηPos := b.Have(
						"η is positive",
						"&0 < η",
						ByArith(ηDef, εPos, real_order_ring.NumNonneg.At(m)))
					ηScale := b.Have(
						"m + 1 copies of η make ε",
						"(&m + &1) * η = ε",
						ByArith(ηDef, real_order_ring.NumNonneg.At(m)))
					coordinates := b.Have(
						"each coordinate of f has, near c, the increment ⟪D(c)(i), x − c⟫ to within η‖x − c‖",
						Statement{
							Binders: "∀i:num.",
							Hypotheses: []string{
								"i < m",
							},
							Conclusion: "∃δ:real. " +
								"    &0 < δ ∧ " +
								"    (∀x:(num → real). " +
								"        ‖x - c‖_n < δ ⇒ vec⟨n⟩(x) ⇒ |f(x)(i) - f(c)(i) - ⟪D(c)(i), x - c⟫_n| ≤ η * ‖x - c‖_n)",
						},
						Derive(func(d *Argument) {
							d.FixAs[Nat]("i")
							below := d.Assume()
							d.Show(
								"the coordinate i of f has the partials D(·)(i), continuous at c",
								By(
									partials,
									continuous,
									below,
									rPos,
									ηPos,
									ContinuousPartialsIncrement.At(
										d.TermAs[Fun[Fun[Nat, Real], Real]]("λy:(num → real). f(y)(i)"),
										d.TermAs[Fun2[Fun[Nat, Real], Nat, Real]]("λy:(num → real). D(y)(i)"),
										proof.Inhabit(c, cIn),
										r,
										η)))
						}))
					δ, common := b.UnpackAs[Real](GroupPremises(
						coordinates,
						real_order_ring.CommonRadius.At(
							m,
							b.TermAs[Fun[Fun[Nat, Real], Real]]("λx:(num → real). ‖x - c‖_n"),
							b.TermAs[Fun2[Nat, Fun[Nat, Real], Bool]](
								"λi:num. λx:(num → real). vec⟨n⟩(x) ⇒ |f(x)(i) - f(c)(i) - ⟪D(c)(i), x - c⟫_n| ≤ η * ‖x - c‖_n"))))
					commonParts := b.Conjuncts(
						common,
						"so all of them do on one ball, of a positive radius δ",
						"on which every coordinate below m has its increment to within η‖x − c‖")
					b.Take(δ)
					b.Do(SplitConj(
						Case(
							"the radius δ is positive",
							By(commonParts[0])),
						Case(
							"and at every point x of the ball the error vector has norm at most m·η‖x − c‖",
							Derive(func(d *Argument) {
								x := d.VecFixAs[Real, DimN]("x")
								ball := d.Assume()
								sub := d.TermAs[Op[Real]]("real_sub")
								coords := d.Have(
									"below m each coordinate of f(x) − f(c) − L(x − c) is at most η‖x − c‖ in size",
									"∀i:num. i < m ⇒ |(f(x) - f(c) - L(x - c))(i)| ≤ η * ‖x - c‖_n",
									Derive(func(e *Argument) {
										i := e.FixAs[Nat]("i")
										below := e.Assume()
										e.Show(
											"the coordinate i of L(x − c) is ⟪D(c)(i), x − c⟫",
											LDef.Rw(),
											ByArith(
												commonParts[1].At(x, i),
												ball,
												below,
												vec_space.VecSubDef.At(
													sub,
													e.TermAs[Fun[Nat, Real]]("f(x) - f(c)"),
													e.TermAs[Fun[Nat, Real]]("λi:num. COND(i < m, ⟪D(c)(i), x - c⟫_n, &0)"),
													i),
												vec_space.VecSubDef.At(sub, f.Apply(x), f.Apply(c), i)))
									}))
								d.Show(
									"so its norm is at most m·η‖x − c‖ ≤ ε‖x − c‖",
									ByArith(
										coords,
										ηPos,
										ηScale,
										euclidean.CoordinateNormBound.At(
											d.VecAs[Real, DimM]("f(x) - f(c) - L(x - c)"),
											d.TermAs[Real]("η * ‖x - c‖_n")),
										euclidean.NormNonneg.At(d.VecAs[Real, DimN]("x - c"))))
							}))))
				}))
			a.Show(
				"c is an n-vector, L is linear into ℝᵐ, and the estimate holds: L is the derivative at c",
				Unfold(VecDerivativeAtDef),
				By(cIn, linear, into, estimate))
		}),
})}

// MixedPartialsCommute — the mixed partial derivatives of f along the
// coordinates i and j agree at c when they are continuous there (Schwarz).
//
// Write p(s, t) = c + s·e_i + t·e_j and take the second difference
// Δ(h) = f(p(h, h)) − f(p(h, 0)) − (f(p(0, h)) − f(p(0, 0))). Read along e_i
// first, it is the increment over ⟦0, h⟧ of σ ↦ f(p(σ, h)) − f(p(σ, 0)), whose
// derivative Di(p(σ, h)) − Di(p(σ, 0)) is, by the mean value inequality along
// e_j, h·Dij(c) to within ε|h|; so Δ(h) is h²·Dij(c) to within εh². Read along
// e_j first, the same Δ(h) is h²·Dji(c) to within εh². If the two mixed
// partials differed, the tolerance ε = |Dij(c) − Dji(c)|/4 and a small h would
// make the two estimates contradict each other.
var MixedPartialsCommute = mixedPartialsCommuteThm{family.Add(registry.ProofEntry{
	Name: "MixedPartialsCommute",
	Key:  "prop_c5d8af513e47a666",
	Build: family.Sections(Statement{
		Binders: "∀f Di Dj Dij Dji:((num → real) → real). ∀i j:num. ∀c:(num → real). ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"∀s t:real. |s| < r ∧ |t| < r ⇒ partial_derivative_at(f, i, «p»(s, t), Di(«p»(s, t)))",
			"∀s t:real. |s| < r ∧ |t| < r ⇒ partial_derivative_at(f, j, «p»(s, t), Dj(«p»(s, t)))",
			"∀s t:real. |s| < r ∧ |t| < r ⇒ partial_derivative_at(Di, j, «p»(s, t), Dij(«p»(s, t)))",
			"∀s t:real. |s| < r ∧ |t| < r ⇒ partial_derivative_at(Dj, i, «p»(s, t), Dji(«p»(s, t)))",
			"∀ε:real. " +
				"    &0 < ε ⇒ " +
				"    ∃δ:real. " +
				"        &0 < δ ∧ " +
				"        ∀s t:real. " +
				"            |s| < δ ∧ |t| < δ ⇒ |Dij(«p»(s, t)) - Dij(c)| < ε ∧ |Dji(«p»(s, t)) - Dji(c)| < ε",
		},
		Conclusion: "Dij(c) = Dji(c)",
		Abbrev: Abbrev{
			{Name: "p", Text: "λs:real. λt:real. c + s • basis_vector(i) + t • basis_vector(j)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The second difference of a function F of two reals over the
			// square ⟦0, h⟧² is h² times its mixed derivative, to within εh²,
			// where the mixed derivative stays within ε of b on a square about
			// the origin: the mean value inequality against a slope, once in
			// each variable.
			secondDifference := ctx.Lemma(Statement{
				Binders: "∀F A B:(real → real → real). ∀ρ b ε h:real.",
				Hypotheses: []string{
					"∀s t:real. " +
						"    |s| < ρ ∧ |t| < ρ ⇒ " +
						"    real_derivative_at(λσ:real. F(σ, t), s, A(s, t)) ∧ " +
						"    real_derivative_at(λτ:real. A(s, τ), t, B(s, t)) ∧ " +
						"    |B(s, t) - b| ≤ ε",
					"|h| < ρ",
				},
				Conclusion: "|F(h, h) - F(h, &0) - (F(&0, h) - F(&0, &0)) - b * h * h| ≤ ε * h * h",
			},
				func(a *Argument, F, A, B *Arrow2[Real, Real, Real], ρ, b, ε, h *Expr[Real], square, small Fact) {
					zero := a.TermAs[Real]("&0")
					low := a.TermAs[Real]("-ρ")
					ends := a.Have(
						"both 0 and h lie in ⟬−ρ, ρ⟭",
						"-ρ < &0 ∧ &0 < ρ ∧ -ρ < h ∧ h < ρ",
						ByArith(small))
					inner := a.Have(
						"along the second variable, A(s, ·) moves from 0 to h by b·h, to within ε|h|",
						"∀s:real. -ρ < s ∧ s < ρ ⇒ |A(s, h) - A(s, &0) - b * (h - &0)| ≤ ε * |h - &0|",
						Derive(func(d *Argument) {
							s := d.FixAs[Real]("s")
							within := d.Assume()
							along := d.Have(
								"on ⟬−ρ, ρ⟭ the derivative of A(s, ·) is B(s, ·), within ε of b",
								"∀t:real. -ρ < t ∧ t < ρ ⇒ real_derivative_at(λτ:real. A(s, τ), t, B(s, t)) ∧ |B(s, t) - b| ≤ ε",
								Derive(func(e *Argument) {
									t := e.FixAs[Real]("t")
									on := e.Assume()
									e.Show(
										"(s, t) lies in the square",
										ByArith(square.At(s, t), within, on))
								}))
							d.Show(
								"the mean value inequality against the slope b",
								By(
									along,
									ends,
									real_derivative.MeanValueNearSlope.At(
										d.TermAs[Fun[Real, Real]]("λτ:real. A(s, τ)"),
										d.TermAs[Fun[Real, Real]]("λτ:real. B(s, τ)"),
										low,
										ρ,
										b,
										ε,
										zero,
										h)))
						}))
					outer := a.Have(
						"along the first variable, F(·, h) − F(·, 0) has derivative A(·, h) − A(·, 0)",
						"∀s:real. -ρ < s ∧ s < ρ ⇒ real_derivative_at(λσ:real. F(σ, h) - F(σ, &0), s, A(s, h) - A(s, &0))",
						Derive(func(d *Argument) {
							s := d.FixAs[Real]("s")
							within := d.Assume()
							d.Show(
								"the difference of the derivatives at (s, h) and (s, 0)",
								ByArith(
									square.At(s, h),
									square.At(s, zero),
									within,
									ends,
									real_derivative.DerivativeSub.At(
										d.TermAs[Fun[Real, Real]]("λσ:real. F(σ, h)"),
										d.TermAs[Fun[Real, Real]]("λσ:real. F(σ, &0)"),
										s,
										d.TermAs[Real]("A(s, h)"),
										d.TermAs[Real]("A(s, &0)"))))
						}))
					moved := a.Have(
						"so the mean value inequality against the slope b·h bounds the second difference",
						"|F(h, h) - F(h, &0) - (F(&0, h) - F(&0, &0)) - b * (h - &0) * (h - &0)| ≤ ε * |h - &0| * |h - &0|",
						By(
							inner,
							outer,
							ends,
							real_derivative.MeanValueNearSlope.At(
								a.TermAs[Fun[Real, Real]]("λσ:real. F(σ, h) - F(σ, &0)"),
								a.TermAs[Fun[Real, Real]]("λσ:real. A(σ, h) - A(σ, &0)"),
								low,
								ρ,
								a.TermAs[Real]("b * (h - &0)"),
								a.TermAs[Real]("ε * |h - &0|"),
								zero,
								h)))
					step := a.TermAs[Real]("h - &0")
					squared := a.Have(
						"the step squared is h²",
						"|h - &0| * |h - &0| = h * h",
						ByArith(real_sgn_abs.AbsMul.At(step, step)))
					a.Show(
						"which is h²·b to within εh²",
						ByArith(moved, Scaled(ε, squared)))
				})
			return ctx.Theorem(headline,
				func(
					a *Argument,
					f, Di, Dj, Dij, Dji *Arrow[Fun[Nat, Real], Real],
					i, j *Expr[Nat],
					c *Expr[Fun[Nat, Real]],
					r *Expr[Real],
					rPos, fAlongI, fAlongJ, diAlongJ, djAlongI, continuous Fact,
				) {
					zero := a.TermAs[Real]("&0")
					commute := a.Have(
						"p(s, t) is also reached by moving along e_j first",
						"∀s t:real. «p»(s, t) = c + t • basis_vector(j) + s • basis_vector(i)",
						Derive(func(b *Argument) {
							b.FixAs[Real]("s")
							b.FixAs[Real]("t")
							b.Show(
								"coordinate by coordinate the two sums agree",
								Funext(),
								Unfold(vec_space.VecAddDef),
								Unfold(vec_space.VecScalarMulDef),
								ByArith())
						}))
					alongI := a.Have(
						"along e_i the partials of f and of Dj are the derivatives of the restrictions",
						Statement{
							Binders: "∀s t:real.",
							Hypotheses: []string{
								"|s| < r",
								"|t| < r",
							},
							Conclusion: "real_derivative_at(λσ:real. f(«p»(σ, t)), s, Di(«p»(s, t))) ∧ " +
								"real_derivative_at(λσ:real. Dj(«p»(σ, t)), s, Dji(«p»(s, t)))",
						},
						Derive(func(b *Argument) {
							s := b.FixAs[Real]("s")
							t := b.FixAs[Real]("t")
							inside := b.Assume()
							base := b.TermAs[Fun[Nat, Real]]("c + t • basis_vector(j)")
							b.Show(
								"moving along e_j first, the line through p(s, t) along e_i is a line through c + t·e_j",
								Simp(Fwd(commute)),
								SplitConj(
									Case(
										"for f, whose partial along e_i there is Di",
										By(
											commute,
											fAlongI.At(s, t),
											inside,
											PartialAlongLine.At(
												f, i, base, s, b.TermAs[Real]("Di(c + t • basis_vector(j) + s • basis_vector(i))")))),
									Case(
										"and for Dj, whose partial along e_i there is Dji",
										By(
											commute,
											djAlongI.At(s, t),
											inside,
											PartialAlongLine.At(
												Dj, i, base, s, b.TermAs[Real]("Dji(c + t • basis_vector(j) + s • basis_vector(i))"))))))
						}))
					alongJ := a.Have(
						"along e_j the partials of f and of Di are the derivatives of the restrictions",
						Statement{
							Binders: "∀s t:real.",
							Hypotheses: []string{
								"|s| < r",
								"|t| < r",
							},
							Conclusion: "real_derivative_at(λτ:real. f(«p»(s, τ)), t, Dj(«p»(s, t))) ∧ " +
								"real_derivative_at(λτ:real. Di(«p»(s, τ)), t, Dij(«p»(s, t)))",
						},
						Derive(func(b *Argument) {
							s := b.FixAs[Real]("s")
							t := b.FixAs[Real]("t")
							inside := b.Assume()
							base := b.TermAs[Fun[Nat, Real]]("c + s • basis_vector(i)")
							b.Show(
								"the line through p(s, t) along e_j is a line through c + s·e_i",
								SplitConj(
									Case(
										"for f, whose partial along e_j there is Dj",
										By(fAlongJ.At(s, t), inside, PartialAlongLine.At(f, j, base, t, b.TermAs[Real]("Dj(«p»(s, t))")))),
									Case(
										"and for Di, whose partial along e_j there is Dij",
										By(
											diAlongJ.At(s, t),
											inside,
											PartialAlongLine.At(Di, j, base, t, b.TermAs[Real]("Dij(«p»(s, t))"))))))
						}))
					differs := a.SupposeNot()
					ε, εDef := a.LetAs[Real]("ε", "|Dij(c) - Dji(c)| / &4")
					εPos := a.Have(
						"ε is positive",
						"&0 < ε",
						ByArith(εDef, differs))
					δ, near := a.UnpackAs[Real](GroupPremises(εPos, continuous.At(ε)), "δ")
					nearParts := a.Conjuncts(
						near,
						"δ is positive",
						"and on the square of half-side δ both mixed partials are within ε of their values at c")
					ρ, ρDef := a.LetAs[Real]("ρ", "min(δ, r)")
					h, hDef := a.LetAs[Real]("h", "ρ / &2")
					small := a.Have(
						"h is positive and inside ⟬−ρ, ρ⟭",
						"&0 < h ∧ |h| < ρ",
						ByArith(hDef, ρDef, rPos, nearParts[0], real_sup_inf.LessThanMin.At(δ, r, zero)))
					firstI := a.Have(
						"on the square of half-side ρ, f along e_i, then Di along e_j, with Dij within ε of Dij(c)",
						Statement{
							Binders: "∀s t:real.",
							Hypotheses: []string{
								"|s| < ρ",
								"|t| < ρ",
							},
							Conclusion: "real_derivative_at(λσ:real. f(«p»(σ, t)), s, Di(«p»(s, t))) ∧ " +
								"real_derivative_at(λτ:real. Di(«p»(s, τ)), t, Dij(«p»(s, t))) ∧ " +
								"|Dij(«p»(s, t)) - Dij(c)| ≤ ε",
						},
						Derive(func(b *Argument) {
							s := b.FixAs[Real]("s")
							t := b.FixAs[Real]("t")
							inside := b.Assume()
							b.Show(
								"a point of the smaller square lies within r and within δ",
								ByArith(
									alongI.At(s, t),
									alongJ.At(s, t),
									nearParts[1].At(s, t),
									ρDef,
									inside,
									real_sup_inf.LessThanMin.At(δ, r, b.TermAs[Real]("|s|")),
									real_sup_inf.LessThanMin.At(δ, r, b.TermAs[Real]("|t|"))))
						}))
					firstJ := a.Have(
						"and, with the variables exchanged, f along e_j, then Dj along e_i, with Dji within ε of Dji(c)",
						Statement{
							Binders: "∀s t:real.",
							Hypotheses: []string{
								"|s| < ρ",
								"|t| < ρ",
							},
							Conclusion: "real_derivative_at(λσ:real. f(«p»(t, σ)), s, Dj(«p»(t, s))) ∧ " +
								"real_derivative_at(λτ:real. Dj(«p»(τ, s)), t, Dji(«p»(t, s))) ∧ " +
								"|Dji(«p»(t, s)) - Dji(c)| ≤ ε",
						},
						Derive(func(b *Argument) {
							s := b.FixAs[Real]("s")
							t := b.FixAs[Real]("t")
							inside := b.Assume()
							b.Show(
								"a point of the smaller square lies within r and within δ",
								ByArith(
									alongJ.At(t, s),
									alongI.At(t, s),
									nearParts[1].At(t, s),
									ρDef,
									inside,
									real_sup_inf.LessThanMin.At(δ, r, b.TermAs[Real]("|s|")),
									real_sup_inf.LessThanMin.At(δ, r, b.TermAs[Real]("|t|"))))
						}))
					viaDij := a.Have(
						"read along e_i first, the second difference is h²·Dij(c) to within εh²",
						"|f(«p»(h, h)) - f(«p»(h, &0)) - (f(«p»(&0, h)) - f(«p»(&0, &0))) - Dij(c) * h * h| ≤ ε * h * h",
						By(
							firstI,
							small,
							At(secondDifference,
								a.TermAs[Fun2[Real, Real, Real]]("λs:real. λt:real. f(«p»(s, t))"),
								a.TermAs[Fun2[Real, Real, Real]]("λs:real. λt:real. Di(«p»(s, t))"),
								a.TermAs[Fun2[Real, Real, Real]]("λs:real. λt:real. Dij(«p»(s, t))"),
								ρ, a.TermAs[Real]("Dij(c)"), ε, h)))
					viaDji := a.Have(
						"read along e_j first, the same second difference is h²·Dji(c) to within εh²",
						"|f(«p»(h, h)) - f(«p»(&0, h)) - (f(«p»(h, &0)) - f(«p»(&0, &0))) - Dji(c) * h * h| ≤ ε * h * h",
						By(
							firstJ,
							small,
							At(secondDifference,
								a.TermAs[Fun2[Real, Real, Real]]("λt:real. λs:real. f(«p»(s, t))"),
								a.TermAs[Fun2[Real, Real, Real]]("λt:real. λs:real. Dj(«p»(s, t))"),
								a.TermAs[Fun2[Real, Real, Real]]("λt:real. λs:real. Dji(«p»(s, t))"),
								ρ, a.TermAs[Real]("Dji(c)"), ε, h)))
					apart := a.Have(
						"so h² times the gap between the mixed partials is at most 2εh² either way",
						"(Dij(c) - Dji(c)) * (h * h) ≤ &2 * ε * (h * h) ∧ (Dji(c) - Dij(c)) * (h * h) ≤ &2 * ε * (h * h)",
						ByArith(viaDij, viaDji))
					squarePos := a.Have(
						"h² is positive",
						"&0 < h * h",
						ByArith(small))
					gap := a.Have(
						"so the gap is at most 2ε either way",
						"Dij(c) - Dji(c) ≤ &2 * ε ∧ Dji(c) - Dij(c) ≤ &2 * ε",
						ByArith(squarePos, apart))
					a.Show(
						"but 2ε is half the gap, which is not 0",
						ByArith(differs, εDef, gap))
				})
		}),
})}
