// mycielski.go — Mycielski's theorem: a meager relation on a nonempty
// Polish space without isolated points has continuum many pairwise
// independent points.

package baire_category

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/words/bit_set"
	"github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/proofs/words/word_bits"
	"github.com/euc-ai/xugo/library/registry"
)

// MycielskiIndependentCantorSet — A meager relation on a nonempty perfect Polish space admits continuum many pairwise independent points.
//
// Take a compatible complete metric, and an increasing sequence of closed
// nowhere dense sets N(n) whose union holds r (MeagerClosedCover). The
// diagonal is closed in the square, the metric topology being Hausdorff,
// and nowhere dense there, because no point is isolated
// (DiagonalClosedNowhereDense); G(n) is the diagonal with N(n).
// Level n of a Cantor scheme holds 2ⁿ closed balls of radius below
// 1/(n+1). Level n+1 is level n doubled, balls i and i + 2ⁿ both starting
// from ball i (parentValid), after which every two distinct balls of the
// doubled level are shrunk until their product misses G(n). The twin
// copies start equal, and it is the diagonal inside G(n) that pulls them
// apart: this is where the absence of isolated points does its work. A
// subset s of ℕ picks the branch through its binary words, whose balls
// meet in a point c(s) by completeness. Two distinct subsets part at some
// bit k, so (c(s), c(t)) misses every G(n) with n ≥ k: it is off the
// diagonal, which makes c injective, and off every N(j), which makes the
// images independent.
var MycielskiIndependentCantorSet = mycielskiIndependentCantorSetThm{family.Add(registry.ProofEntry{
	Name: "MycielskiIndependentCantorSet",
	Key:  "prop_31d3a0f500b578ca",
	Build: family.Sections(
		Statement{
			Binders: "∀T:set(set(A)). ∀r:set(prod(A, A)).",
			Hypotheses: []string{
				"polish_space(T)",
				"¬(⋃T = ∅)",
				"∀x:A. x ∈ ⋃T ⇒ {x} ∉ T",
				"meager(product_topology(T, T), r)",
			},
			Conclusion: "∃c:(set(num) → A). " +
				"    injective_on(𝕌⟨A:set(num)⟩, c) ∧ " +
				"    (∀s:set(num). c(s) ∈ ⋃T) ∧ " +
				"    (∀s t:set(num). ¬(s = t) ⇒ (c(s), c(t)) ∉ r)",
			Abbrev: Abbrev{
				{Name: "cballAt", Text: "λp₁:prod(A, real). closed_ball(M, d, fst(p₁), snd(p₁))"},
				{Name: "shrunkIn", Text: "λS₁:(num → prod(A, real)). " +
					"λS₂:(num → prod(A, real)). " +
					"λi:num. " +
					"λε₁:real. " +
					"    fst(S₁(i)) ∈ M ∧ " +
					"    &0 < snd(S₁(i)) ∧ " +
					"    snd(S₁(i)) < ε₁ ∧ " +
					"    «cballAt»(S₁(i)) ⊆ ball(M, d, fst(S₂(i)), snd(S₂(i)))"},
				{Name: "pairOff", Text: "λS₁:(num → prod(A, real)). λi:num. λj:num. λK₁:set(prod(A, A)). " +
					"    set_cross(«cballAt»(S₁(i)), «cballAt»(S₁(j))) ∩ K₁ = ∅"},
				{Name: "shrinking", Text: "λS₁:(num → prod(A, real)). " +
					"λS₂:(num → prod(A, real)). " +
					"λm₁:num. " +
					"λK₁:set(prod(A, A)). " +
					"λε₁:real. " +
					"    (∀i:num. i < m₁ ⇒ «shrunkIn»(S₁, S₂, i, ε₁)) ∧ " +
					"    (∀i j:num. i < m₁ ∧ j < m₁ ∧ i ≠ j ⇒ «pairOff»(S₁, i, j, K₁))"},
				{Name: "stage", Text: "λS₁:(num → prod(A, real)). λS₂:(num → prod(A, real)). λn₁:num. λk₁:num. " +
					"    (∀i:num. i < suc(n₁) ⇒ «shrunkIn»(S₁, S₂, i, ε)) ∧ " +
					"    (∀i j:num. i < n₁ ∧ j < n₁ ∧ i ≠ j ⇒ «pairOff»(S₁, i, j, K)) ∧ " +
					"    (∀j:num. j < k₁ ⇒ «pairOff»(S₁, j, n₁, K) ∧ «pairOff»(S₁, n₁, j, K))"},
				{Name: "stepNext", Text: "λS₁:(num → prod(A, real)). λn₁:num. λS₂:(num → prod(A, real)). " +
					"    «shrinking»(S₂, λi:num. S₁(rem(i, 2 ^ n₁)), 2 ^ suc(n₁), G(n₁), real_inv(&suc(n₁) + &1))"},
				{Name: "branchBall", Text: "λs₁:set(num). λn₁:num. «cballAt»(B(n₁, word_of_bits(n₁, s₁)))"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			// Ball n of a family F of open balls of M is paired off K against the
			// balls before it. Given a shrinking E of the first n balls off the
			// closed nowhere dense set K of M × M, for every k up to n the first
			// suc(n) balls shrink to closed balls of radius below ε, each inside
			// its open ball, such that any two distinct ones below n still have
			// their product off K, and so do ball n and each ball below k, in both
			// orders. Of F itself only ball n is assumed a ball of M: the earlier
			// ones are read through E.
			//
			// The complement of K in the square is open and dense, K being closed
			// and nowhere dense, so it meets the rectangle of two open balls, a
			// non-empty open set, at a point off K. The part of the rectangle off
			// K is open, and about that point the product topology holds an open
			// rectangle inside it, which holds the product of two closed balls of
			// one radius. The top ball starts at half the smaller of its radius
			// and ε, beside the balls of E, and is then paired off K against each
			// earlier ball in turn, in both orders, every shrink keeping the
			// inclusions and separations already won.
			pairTopBallOffNowhereDense := ctx.Lemma(
				Statement{
					Binders: "∀M:set(A). " +
						"∀d:(A → A → real). " +
						"∀K:set(prod(A, A)). " +
						"∀ε:real. " +
						"∀n:num. " +
						"∀F E:(num → prod(A, real)). " +
						"∀k:num.",
					Hypotheses: []string{
						"metric_space(M, d)",
						"closed_in(«prodTop», K)",
						"nowhere_dense(«prodTop», K)",
						"&0 < ε",
						"fst(F(n)) ∈ M ∧ &0 < snd(F(n))",
						"«shrinking»(E, F, n, K, ε)",
						"k ≤ n",
					},
					Conclusion: "∃F':(num → prod(A, real)). «stage»(F', F, n, k)",
				},
				func(
					a *Argument,
					M *Expr[Set[A]],
					d *Expr[Fun2[A, A, Real]],
					K *Expr[Set[Prod[A, A]]],
					ε *Expr[Real],
					n *Expr[Nat],
					F, E *Expr[Fun[Nat, Prod[A, Real]]],
					metric metric_space.MetricSpaceFact[on.M],
					kClosed, kNowhereDense, epsPos, fnValid, propsE Fact,
				) {
					mt := a.TermAs[Set[Set[A]]]("metric_topology(M, d)")

					tTop := a.Have(
						"the product topology is a topology",
						"is_topology(«prodTop»)",
						By(product_topology.ProductTopology.At(mt, mt), metric_space.MetricTopology.At(M, d)),
					)
					complementK := a.TermAs[Set[Prod[A, A]]]("⋃«prodTop» ∖ K")
					complementOpenDense := a.Have(
						"K is closed and nowhere dense, so its complement in the square is open and dense",
						"⋃«prodTop» ∖ K ∈ «prodTop» ∧ closure(«prodTop», ⋃«prodTop» ∖ K) = ⋃«prodTop»",
						By(kClosed, kNowhereDense, ClosedNowhereDenseComplement.Read(tTop).At(K)),
					)
					crossDisjointMono := a.Have(
						"shrinking factors preserves disjointness from K",
						"∀s₁ s₂ t₁ t₂:set(A). s₁ ⊆ s₂ ∧ t₁ ⊆ t₂ ∧ set_cross(s₂, t₂) ∩ K = ∅ ⇒ set_cross(s₁, t₁) ∩ K = ∅",
						Derive(func(c *Argument) {
							s1 := c.FixAs[Set[A]]("s₁")
							s2 := c.FixAs[Set[A]]("s₂")
							t1 := c.FixAs[Set[A]]("t₁")
							t2 := c.FixAs[Set[A]]("t₂")
							h := c.Assume()
							subRect := c.Have(
								"smaller rectangle sits inside larger rectangle",
								"set_cross(s₁, t₁) ⊆ set_cross(s₂, t₂)",
								By(set_product.CrossSubsetIff.At(s1, s2, t1, t2), h),
							)
							c.Show(
								"a subset of a rectangle disjoint from K is also disjoint from K",
								BySets(subRect, h),
							)
						}),
					)

					pairShrink := a.Have(
						"any pair of open balls shrinks to closed balls of one radius below ε whose product misses K",
						Statement{
							Binders:    "∀x y:A. ∀r₁ r₂:real.",
							Hypotheses: []string{"x ∈ M", "y ∈ M", "&0 < r₁", "&0 < r₂"},
							Conclusion: "∃x' y':A. ∃ρ:real. " +
								"    x' ∈ M ∧ " +
								"    y' ∈ M ∧ " +
								"    &0 < ρ ∧ " +
								"    ρ < ε ∧ " +
								"    closed_ball(M, d, x', ρ) ⊆ ball(M, d, x, r₁) ∧ " +
								"    closed_ball(M, d, y', ρ) ⊆ ball(M, d, y, r₂) ∧ " +
								"    set_cross(closed_ball(M, d, x', ρ), closed_ball(M, d, y', ρ)) ∩ K = ∅",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							y := c.FixAs[A]("y")
							r1 := c.FixAs[Real]("r₁")
							r2 := c.FixAs[Real]("r₂")
							hParts := c.Conjuncts(
								c.Assume(),
								"x belongs to M",
								"y belongs to M",
								"the first radius is positive",
								"the second radius is positive")
							xm := c.MemberOf[on.M](x, hParts[0])
							ym := c.MemberOf[on.M](y, hParts[1])
							ballX := c.TermAs[Set[A]]("ball(M, d, x, r₁)")
							ballY := c.TermAs[Set[A]]("ball(M, d, y, r₂)")
							rectangle := c.TermAs[Set[Prod[A, A]]]("set_cross(ball(M, d, x, r₁), ball(M, d, y, r₂))")
							offK := c.TermAs[Set[Prod[A, A]]]("set_cross(ball(M, d, x, r₁), ball(M, d, y, r₂)) ∖ K")

							rectangleOpen := c.Have(
								"the rectangle of the two balls is open in the product topology",
								"set_cross(ball(M, d, x, r₁), ball(M, d, y, r₂)) ∈ «prodTop»",
								By(
									product_topology.RectangleOpen.At(mt, mt, ballX, ballY),
									metric_space.BallOpen.Read(metric).At(xm, r1),
									metric_space.BallOpen.Read(metric).At(ym, r2)),
							)
							centres := c.Have(
								"and it holds the pair of centres",
								"(x, y) ∈ set_cross(ball(M, d, x, r₁), ball(M, d, y, r₂))",
								By(
									set_product.InCross.At(ballX, ballY, x, y),
									metric_space.CentreInBall.Read(metric).At(xm, r1),
									metric_space.CentreInBall.Read(metric).At(ym, r2),
									hParts[2],
									hParts[3]),
							)
							meets := c.Have(
								"the dense complement of K meets the rectangle, a non-empty open set",
								"set_cross(ball(M, d, x, r₁), ball(M, d, y, r₂)) ∩ (⋃«prodTop» ∖ K) ≠ ∅",
								By(
									rectangleOpen,
									centres,
									complementOpenDense,
									set_basic.MemberNotEmpty.At(rectangle),
									set_order.SubsetDiff.At(c.TermAs[Set[Prod[A, A]]]("⋃«prodTop»"), K),
									topological_space.DenseMeetsOpen.Read(tTop).At(complementK)),
							)
							p, pOffK := c.ObtainAs[Prod[A, A]](
								"so the rectangle has a point p off K",
								"∃p:prod(A, A). p ∈ set_cross(ball(M, d, x, r₁), ball(M, d, y, r₂)) ∖ K",
								BySets(meets),
							)
							u, v, box := c.Obtain2As[Set[A], Set[A]](
								"the part of the rectangle off the closed K is open, "+
									"so an open rectangle u × v lies about p inside it",
								"∃u v:set(A). "+
									"    u ∈ metric_topology(M, d) ∧ "+
									"    v ∈ metric_topology(M, d) ∧ "+
									"    p ∈ set_cross(u, v) ∧ "+
									"    set_cross(u, v) ⊆ set_cross(ball(M, d, x, r₁), ball(M, d, y, r₂)) ∖ K",
								By(
									product_topology.ProductOpenIff.At(mt, mt, offK),
									kClosed,
									topological_space.DiffOpen.Read(tTop).At(c.MemberOf[on.Any](rectangle, rectangleOpen), K),
									pOffK),
							)
							boxParts := c.Conjuncts(
								box,
								"u is open",
								"v is open",
								"p lies in u × v",
								"u × v lies in the rectangle off K")
							coordinates := c.Have(
								"the coordinates of p lie in u and in v",
								"fst(p) ∈ u ∧ snd(p) ∈ v",
								By(boxParts[2], set_product.InCrossProjections.At(u, v, p)),
							)
							inBalls := c.Have(
								"u and v are not empty, so u × v inside the rectangle puts them inside the two balls",
								"u ⊆ ball(M, d, x, r₁) ∧ v ⊆ ball(M, d, y, r₂)",
								BySets(boxParts[3], coordinates, set_product.CrossSubsetIff.At(u, ballX, v, ballY)),
							)
							centresInM := c.Have(
								"so the coordinates of p are points of M",
								"fst(p) ∈ M ∧ snd(p) ∈ M",
								BySets(
									coordinates,
									inBalls,
									metric_space.BallDef.At(M, d, x, r1),
									metric_space.BallDef.At(M, d, y, r2)),
							)
							δ1, uBall := c.ObtainAs[Real](
								"u is open, so a ball about fst(p) lies in it",
								"∃δ₁:real. &0 < δ₁ ∧ ball(M, d, fst(p), δ₁) ⊆ u",
								By(metric_space.OpenIff.At(M, d, u), boxParts[0], coordinates),
							)
							δ2, vBall := c.ObtainAs[Real](
								"and a ball about snd(p) lies in v",
								"∃δ₂:real. &0 < δ₂ ∧ ball(M, d, snd(p), δ₂) ⊆ v",
								By(metric_space.OpenIff.At(M, d, v), boxParts[1], coordinates),
							)
							smaller := c.TermAs[Real]("min(δ₁, δ₂)")
							zero := c.TermAs[Real]("&0")
							minPositive := c.Have(
								"the smallest of δ₁, δ₂ and ε is positive",
								"&0 < min(min(δ₁, δ₂), ε)",
								By(
									uBall,
									vBall,
									epsPos,
									real_sup_inf.LessThanMin.At(δ1, δ2, zero),
									real_sup_inf.LessThanMin.At(smaller, ε, zero)),
							)
							ρ, ρDef := c.LetAs[Real]("ρ", "min(min(δ₁, δ₂), ε) / &2")
							radius := c.Have(
								"half of it is positive and below ε, δ₁ and δ₂",
								"&0 < ρ ∧ ρ < ε ∧ ρ < δ₁ ∧ ρ < δ₂",
								ByArith(
									ρDef,
									minPositive,
									real_sup_inf.MinLowerBound.At(smaller, ε),
									real_sup_inf.MinLowerBound.At(δ1, δ2)),
							)
							inBox := c.Have(
								"the closed balls of radius ρ about fst(p) and snd(p) lie in u and in v",
								"closed_ball(M, d, fst(p), ρ) ⊆ u ∧ closed_ball(M, d, snd(p), ρ) ⊆ v",
								BySets(
									radius,
									uBall,
									vBall,
									metric_space.ClosedBallSubsetBall.At(M, d, c.TermAs[A]("fst(p)"), ρ, δ1),
									metric_space.ClosedBallSubsetBall.At(M, d, c.TermAs[A]("snd(p)"), ρ, δ2)),
							)
							c.Take(c.TermAs[A]("fst(p)"))
							c.Take(c.TermAs[A]("snd(p)"))
							c.Take(ρ)
							c.Show(
								"they lie in the two balls, and their product lies in u × v, off K",
								BySets(
									centresInM,
									radius,
									inBox,
									inBalls,
									boxParts[3],
									set_product.CrossSubsetIff.At(
										c.TermAs[Set[A]]("closed_ball(M, d, fst(p), ρ)"),
										u,
										c.TermAs[Set[A]]("closed_ball(M, d, snd(p), ρ)"),
										v)),
							)
						}),
					)

					partsE := a.Conjuncts(
						propsE,
						"prefix shrunk balls stay inside the originals",
						"distinct pairs below n miss K",
					)
					shrunkE, offKE := partsE[0], partsE[1]
					hnLtSuc := a.Have(
						"top index lies below suc(n)",
						"n < suc(n)",
						ByArith())

					a.Induct("k")
					a.Base(
						"at k = 0, E below n with ball n at half the smaller of its radius and ε is a stage-0 shrinking",
						func(e *Argument) {
							e.Assume()
							H, defH := e.LetAs[Fun[Nat, Prod[A, Real]]](
								"H", "λi:num. COND(i < n, E(i), (fst(F(n)), min(snd(F(n)), ε) / &2))")
							fnRad := e.TermAs[Real]("snd(F(n))")
							minBound := real_sup_inf.MinLowerBound.At(fnRad, ε)
							minPos := e.Have(
								"the smaller of the top radius and ε is positive",
								"&0 < min(snd(F(n)), ε)",
								By(real_sup_inf.LessThanMin.At(fnRad, ε, e.TermAs[Real]("&0")), fnValid, epsPos),
							)
							halfBelow := e.Have(
								"half the minimum is below the top radius",
								"min(snd(F(n)), ε) / &2 < snd(F(n))",
								ByArith(minPos, minBound),
							)
							fnShrunkSub := e.Have(
								"so the closed ball of that radius lies inside the top open ball",
								"closed_ball(M, d, fst(F(n)), min(snd(F(n)), ε) / &2) ⊆ ball(M, d, fst(F(n)), snd(F(n)))",
								By(
									halfBelow,
									metric_space.ClosedBallSubsetBall.At(
										M,
										d,
										e.TermAs[A]("fst(F(n))"),
										e.TermAs[Real]("min(snd(F(n)), ε) / &2"),
										fnRad)),
							)
							shrunkH := e.Have(
								"all entries of the initial sequence satisfy the shrinking conditions",
								"∀i:num. i < suc(n) ⇒ «shrunkIn»(H, F, i, ε)",
								Derive(func(f *Argument) {
									i := f.FixAs[Nat]("i")
									hi := f.Assume()
									f.Cases(f.TermAs[Bool]("i < n"))
									f.When(
										"i lies strictly below n",
										func(g *Argument, hiLtN Fact) {
											g.Show(
												"the conditional selects the prefix entry at i",
												By(defH, hiLtN, shrunkE.At(i)))
										})
									f.Otherwise(
										"i equals n",
										func(g *Argument, hiNotLtN Fact) {
											hiEqN := g.Have(
												"i equals the top index",
												"i = n",
												ByArith(hi, hiNotLtN),
											)
											radPos := g.Have(
												"half the minimum radius is positive",
												"&0 < min(snd(F(n)), ε) / &2",
												ByArith(minPos),
											)
											radLtEps := g.Have(
												"half the minimum radius is strictly below ε",
												"min(snd(F(n)), ε) / &2 < ε",
												ByArith(minBound, epsPos),
											)
											g.Show(
												"the conditional selects the halved top ball",
												By(defH, hiNotLtN, hiEqN, fnValid, radPos, radLtEps, fnShrunkSub, pairs.Fst, pairs.Snd),
											)
										})
								}),
							)
							offKH := e.Have(
								"all distinct pairs strictly below n already miss K",
								"∀i j:num. i < n ∧ j < n ∧ i ≠ j ⇒ «pairOff»(H, i, j, K)",
								Derive(func(f *Argument) {
									i := f.FixAs[Nat]("i")
									j := f.FixAs[Nat]("j")
									hij := f.Assume()
									f.Show(
										"prefix entries come from E",
										By(defH, offKE.At(i, j), hij))
								}),
							)
							vacuousH := e.Have(
								"no index lies strictly below zero",
								"∀j:num. j < 0 ⇒ «pairOff»(H, j, n, K) ∧ «pairOff»(H, n, j, K)",
								By(nat_order.LessThanZeroClause),
							)
							e.Take(H)
							e.Show(
								"all three base invariants hold",
								By(shrunkH, offKH, vacuousH))
						})
					a.Step(
						"a stage-k shrinking gives a stage-suc(k) one once balls k and n are paired off K in both orders",
						func(e *Argument, innerIH Fact) {
							k := e.TermAs[Nat]("k")
							hsuc := e.Assume()
							hkLeN := e.Have(
								"k is at most n",
								"k ≤ n",
								ByArith(hsuc))
							hkLtN := e.Have(
								"k is strictly less than n",
								"k < n",
								ByArith(hsuc))
							hkLtSucN := e.Have(
								"k lies inside the extended range",
								"k < suc(n)",
								ByArith(hsuc))
							hkNeN := e.Have(
								"k differs from the top index",
								"k ≠ n",
								ByArith(hsuc))

							_, propsL := e.ObtainAs[Fun[Nat, Prod[A, Real]]](
								"by the inner induction hypothesis, choose a stage-k shrinking L of F",
								"∃F':(num → prod(A, real)). «stage»(F', F, n, k)",
								Named("L"),
								By(innerIH, hkLeN),
							)
							partsL := e.Conjuncts(
								propsL,
								"all current balls stay inside the originals",
								"distinct pairs below n miss K",
								"prefix pairs with top index miss K",
							)
							shrunkL, offKL, withTopL := partsL[0], partsL[1], partsL[2]

							shrunkLk := e.Have(
								"the current entry at k satisfies the shrinking invariant",
								"«shrunkIn»(L, F, k, ε)",
								By(shrunkL.At(k), hkLtSucN),
							)
							shrunkLn := e.Have(
								"the current top entry satisfies the shrinking invariant",
								"«shrunkIn»(L, F, n, ε)",
								By(shrunkL.At(n), hnLtSuc),
							)

							x1, y1, ρ1, pass1 := e.Obtain3As[A, A, Real](
								"the balls of L at k and at n shrink to closed balls "+
									"about x₁ and y₁ of radius ρ₁ whose product misses K",
								"∃x₁ y₁:A. ∃ρ₁:real. "+
									"    x₁ ∈ M ∧ "+
									"    y₁ ∈ M ∧ "+
									"    &0 < ρ₁ ∧ "+
									"    ρ₁ < ε ∧ "+
									"    closed_ball(M, d, x₁, ρ₁) ⊆ ball(M, d, fst(L(k)), snd(L(k))) ∧ "+
									"    closed_ball(M, d, y₁, ρ₁) ⊆ ball(M, d, fst(L(n)), snd(L(n))) ∧ "+
									"    set_cross(closed_ball(M, d, x₁, ρ₁), closed_ball(M, d, y₁, ρ₁)) ∩ K = ∅",
								By(
									pairShrink.At(
										e.TermAs[A]("fst(L(k))"),
										e.TermAs[A]("fst(L(n))"),
										e.TermAs[Real]("snd(L(k))"),
										e.TermAs[Real]("snd(L(n))")),
									shrunkLk,
									shrunkLn),
							)
							p1 := e.Conjuncts(
								pass1,
								"first intermediate centre lies in M",
								"second intermediate centre lies in M",
								"first pass radius is positive",
								"first pass radius is below ε",
								"first pass first closed ball shrinks",
								"first pass second closed ball shrinks",
								"first pass product misses K",
							)
							x1Mem, y1Mem, ρ1Pos, x1Sub, y1Sub, knOff1 := p1[0], p1[1], p1[2], p1[4], p1[5], p1[6]

							y2, x2, ρ2, pass2 := e.Obtain3As[A, A, Real](
								"in the reverse order these shrink again, to closed "+
									"balls about y₂ and x₂ of radius ρ₂ whose product misses K",
								"∃y₂ x₂:A. ∃ρ₂:real. "+
									"    y₂ ∈ M ∧ "+
									"    x₂ ∈ M ∧ "+
									"    &0 < ρ₂ ∧ "+
									"    ρ₂ < ε ∧ "+
									"    closed_ball(M, d, y₂, ρ₂) ⊆ ball(M, d, y₁, ρ₁) ∧ "+
									"    closed_ball(M, d, x₂, ρ₂) ⊆ ball(M, d, x₁, ρ₁) ∧ "+
									"    set_cross(closed_ball(M, d, y₂, ρ₂), closed_ball(M, d, x₂, ρ₂)) ∩ K = ∅",
								By(pairShrink.At(y1, x1, ρ1, ρ1), y1Mem, x1Mem, ρ1Pos),
							)
							p2 := e.Conjuncts(
								pass2,
								"second pass second centre lies in M",
								"second pass first centre lies in M",
								"second pass radius is positive",
								"second pass radius is below ε",
								"second pass second closed ball shrinks",
								"second pass first closed ball shrinks",
								"second pass product misses K",
							)
							y2Mem, x2Mem, ρ2Pos, ρ2LtEps, y2Sub, x2Sub, nkOff := p2[0], p2[1], p2[2], p2[3], p2[4], p2[5], p2[6]

							cbX2 := e.TermAs[Set[A]]("closed_ball(M, d, x₂, ρ₂)")
							cbY2 := e.TermAs[Set[A]]("closed_ball(M, d, y₂, ρ₂)")
							cbX1 := e.TermAs[Set[A]]("closed_ball(M, d, x₁, ρ₁)")
							cbY1 := e.TermAs[Set[A]]("closed_ball(M, d, y₁, ρ₁)")

							nested := e.Have(
								"each closed ball of the second pass lies in the first-pass closed ball it shrinks",
								"closed_ball(M, d, x₂, ρ₂) ⊆ closed_ball(M, d, x₁, ρ₁) ∧ "+
									"closed_ball(M, d, y₂, ρ₂) ⊆ closed_ball(M, d, y₁, ρ₁)",
								BySets(
									x2Sub,
									y2Sub,
									metric_space.BallSubsetClosedBall.At(M, d, x1, ρ1),
									metric_space.BallSubsetClosedBall.At(M, d, y1, ρ1)),
							)
							knOff := e.Have(
								"so the pair ordered k then top index stays off K",
								"set_cross(closed_ball(M, d, x₂, ρ₂), closed_ball(M, d, y₂, ρ₂)) ∩ K = ∅",
								By(crossDisjointMono.At(cbX2, cbX1, cbY2, cbY1), nested, knOff1),
							)
							inCurrent := e.Have(
								"and the new balls at k and at the top index lie in the current closed balls there",
								"closed_ball(M, d, x₂, ρ₂) ⊆ closed_ball(M, d, fst(L(k)), snd(L(k))) ∧ "+
									"closed_ball(M, d, y₂, ρ₂) ⊆ closed_ball(M, d, fst(L(n)), snd(L(n)))",
								BySets(
									nested,
									x1Sub,
									y1Sub,
									metric_space.BallSubsetClosedBall.At(M, d, e.TermAs[A]("fst(L(k))"), e.TermAs[Real]("snd(L(k))")),
									metric_space.BallSubsetClosedBall.At(M, d, e.TermAs[A]("fst(L(n))"), e.TermAs[Real]("snd(L(n))"))),
							)

							P, defP := e.LetAs[Fun[Nat, Prod[A, Real]]](
								"P", "λi:num. COND(i = k, (x₂, ρ₂), COND(i = n, (y₂, ρ₂), L(i)))")

							monoP := e.Have(
								"every updated closed ball sits inside the corresponding previous closed ball",
								"∀i:num. i < suc(n) ⇒ «cballAt»(P(i)) ⊆ «cballAt»(L(i))",
								Derive(func(f *Argument) {
									f.FixAs[Nat]("i")
									f.Assume()
									f.Cases(f.TermAs[Bool]("i = k"))
									f.When(
										"i equals k",
										func(g *Argument, hiEqK Fact) {
											pEq := g.Have(
												"at k, P(i) evaluates to (x₂, ρ₂)",
												"P(i) = (x₂, ρ₂)",
												By(defP, hiEqK),
											)
											g.Do(pEq.Rw(), hiEqK.Rw())
											g.Show(
												"updating at k shrinks the ball at k",
												By(inCurrent, pairs.Fst.At(x2, ρ2), pairs.Snd.At(x2, ρ2)))
										})
									f.Otherwise(
										"i differs from k",
										func(g *Argument, hiNeK Fact) {
											g.Cases(g.TermAs[Bool]("i = n"))
											g.When(
												"i equals the top index",
												func(h *Argument, hiEqN Fact) {
													pEq := h.Have(
														"at the top index, P(i) evaluates to (y₂, ρ₂)",
														"P(i) = (y₂, ρ₂)",
														By(defP, hiNeK, hiEqN),
													)
													h.Do(pEq.Rw(), hiEqN.Rw())
													h.Show(
														"updating at the top index shrinks the top ball",
														By(inCurrent, pairs.Fst.At(y2, ρ2), pairs.Snd.At(y2, ρ2)))
												})
											g.Otherwise(
												"i differs from both k and the top index",
												func(h *Argument, hiNeN Fact) {
													eqP := h.Have(
														"the updated sequence agrees with the previous one at i",
														"P(i) = L(i)",
														By(defP, hiNeK, hiNeN),
													)
													ballLi := h.TermAs[Set[A]]("«cballAt»(L(i))")
													h.Show(
														"all other indices are unchanged",
														By(eqP, set_basic.SubsetDef.At(ballLi, ballLi)),
													)
												})
										})
								}),
							)
							shrunkP := e.Have(
								"all entries of the updated sequence satisfy the shrinking conditions",
								"∀i:num. i < suc(n) ⇒ «shrunkIn»(P, F, i, ε)",
								Derive(func(f *Argument) {
									i := f.FixAs[Nat]("i")
									hi := f.Assume()
									f.Cases(f.TermAs[Bool]("i = k"))
									f.When(
										"i equals k",
										func(g *Argument, hiEqK Fact) {
											x2SubFK := g.Have(
												"the updated k ball lies in the original k open ball",
												"closed_ball(M, d, x₂, ρ₂) ⊆ ball(M, d, fst(F(k)), snd(F(k)))",
												BySets(inCurrent, shrunkLk),
											)
											pEq := g.Have(
												"at k, P(i) evaluates to (x₂, ρ₂)",
												"P(i) = (x₂, ρ₂)",
												By(defP, hiEqK),
											)
											g.Do(pEq.Rw(), hiEqK.Rw())
											g.Show(
												"the updated entry at k stays inside the open ball at k",
												By(Normalized, x2Mem, ρ2Pos, ρ2LtEps, x2SubFK, pairs.Fst.At(x2, ρ2), pairs.Snd.At(x2, ρ2)),
											)
										})
									f.Otherwise(
										"i differs from k",
										func(g *Argument, hiNeK Fact) {
											g.Cases(g.TermAs[Bool]("i = n"))
											g.When(
												"i equals the top index",
												func(h *Argument, hiEqN Fact) {
													y2SubFN := h.Have(
														"the updated top ball lies in the original top open ball",
														"closed_ball(M, d, y₂, ρ₂) ⊆ ball(M, d, fst(F(n)), snd(F(n)))",
														BySets(inCurrent, shrunkLn),
													)
													pEq := h.Have(
														"at the top index, P(i) evaluates to (y₂, ρ₂)",
														"P(i) = (y₂, ρ₂)",
														By(defP, hiNeK, hiEqN),
													)
													h.Do(pEq.Rw(), hiEqN.Rw())
													h.Show(
														"the updated top entry stays inside the top open ball",
														By(Normalized, y2Mem, ρ2Pos, ρ2LtEps, y2SubFN, pairs.Fst.At(y2, ρ2), pairs.Snd.At(y2, ρ2)),
													)
												})
											g.Otherwise(
												"i differs from both k and the top index",
												func(h *Argument, hiNeN Fact) {
													h.Show(
														"unchanged entries inherit the previous invariant",
														By(defP, hiNeK, hiNeN, shrunkL.At(i), hi))
												})
										})
								}),
							)
							offKP := e.Have(
								"distinct pairs strictly below the top index stay disjoint from K",
								"∀i j:num. i < n ∧ j < n ∧ i ≠ j ⇒ «pairOff»(P, i, j, K)",
								Derive(func(f *Argument) {
									i := f.FixAs[Nat]("i")
									j := f.FixAs[Nat]("j")
									hij := f.Assume()
									hiLtSucN := f.Have(
										"i lies inside the extended range",
										"i < suc(n)",
										ByArith(hij))
									hjLtSucN := f.Have(
										"j lies inside the extended range",
										"j < suc(n)",
										ByArith(hij))
									f.Show(
										"monotonicity transfers disjointness from the previous sequence",
										By(
											crossDisjointMono.At(
												f.TermAs[Set[A]]("«cballAt»(P(i))"),
												f.TermAs[Set[A]]("«cballAt»(L(i))"),
												f.TermAs[Set[A]]("«cballAt»(P(j))"),
												f.TermAs[Set[A]]("«cballAt»(L(j))"),
											),
											monoP.At(i),
											hiLtSucN,
											monoP.At(j),
											hjLtSucN,
											offKL.At(i, j),
											hij,
										),
									)
								}),
							)
							withTopP := e.Have(
								"all pairs with an index below suc(k) and the top index are disjoint from K",
								"∀j:num. j < suc(k) ⇒ «pairOff»(P, j, n, K) ∧ «pairOff»(P, n, j, K)",
								Derive(func(f *Argument) {
									j := f.FixAs[Nat]("j")
									hj := f.Assume()
									f.Cases(f.TermAs[Bool]("j = k"))
									f.When(
										"j equals k",
										func(g *Argument, hjEqK Fact) {
											g.Show(
												"both orientations at k and the top index come directly from the two shrink passes",
												By(
													defP,
													hjEqK,
													hkNeN,
													knOff,
													nkOff,
													pairs.Fst.At(x2, ρ2),
													pairs.Snd.At(x2, ρ2),
													pairs.Fst.At(y2, ρ2),
													pairs.Snd.At(y2, ρ2)),
											)
										})
									f.Otherwise(
										"j is strictly below k",
										func(g *Argument, hjNeK Fact) {
											hjLtK := g.Have(
												"j lies strictly below k",
												"j < k",
												ByArith(hj, hjNeK))
											hjLtSucN := g.Have(
												"j lies inside the extended range",
												"j < suc(n)",
												ByArith(hjLtK, hkLtN))
											g.Show(
												"earlier pairs against the top index preserve disjointness by monotonicity",
												By(
													crossDisjointMono.At(
														g.TermAs[Set[A]]("«cballAt»(P(j))"),
														g.TermAs[Set[A]]("«cballAt»(L(j))"),
														g.TermAs[Set[A]]("«cballAt»(P(n))"),
														g.TermAs[Set[A]]("«cballAt»(L(n))"),
													),
													crossDisjointMono.At(
														g.TermAs[Set[A]]("«cballAt»(P(n))"),
														g.TermAs[Set[A]]("«cballAt»(L(n))"),
														g.TermAs[Set[A]]("«cballAt»(P(j))"),
														g.TermAs[Set[A]]("«cballAt»(L(j))"),
													),
													monoP.At(j),
													hjLtSucN,
													monoP.At(n),
													hnLtSuc,
													withTopL.At(j),
													hjLtK,
												),
											)
										})
								}),
							)
							e.Take(P)
							e.Show(
								"all three step invariants hold",
								By(shrunkP, offKP, withTopP))
						})
				},
			)

			// m open balls of M, given as (centre, radius) pairs, shrink to closed
			// balls of radius below ε, each inside its open ball, such that the
			// product of any two distinct ones misses the closed nowhere dense set
			// K of M × M. Only the first m pairs of B are read. K need not be
			// symmetric, so both orders of a pair are separated; for m at most 1
			// the separation is vacuous and only the radius bound is at work.
			//
			// The family is shrunk one index at a time: a shrinking of the first n
			// balls is carried to ball n by pairing it off K against every earlier
			// ball (pairTopBallOffNowhereDense), which leaves every two distinct
			// balls below suc(n) with their products off K.
			shrinkBallsOffNowhereDense := ctx.Lemma(
				Statement{
					Binders: "∀M:set(A). " +
						"∀d:(A → A → real). " +
						"∀K:set(prod(A, A)). " +
						"∀ε:real. " +
						"∀m:num. " +
						"∀B:(num → prod(A, real)).",
					Hypotheses: []string{
						"metric_space(M, d)",
						"closed_in(«prodTop», K)",
						"nowhere_dense(«prodTop», K)",
						"&0 < ε",
						"∀i:num. i < m ⇒ fst(B(i)) ∈ M ∧ &0 < snd(B(i))",
					},
					Conclusion: "∃B':(num → prod(A, real)). «shrinking»(B', B, m, K, ε)",
				},
				func(
					a *Argument,
					M *Expr[Set[A]],
					d *Expr[Fun2[A, A, Real]],
					K *Expr[Set[Prod[A, A]]],
					ε *Expr[Real],
					m *Expr[Nat],
					B *Expr[Fun[Nat, Prod[A, Real]]],
					metric metric_space.MetricSpaceFact[on.M],
					kClosed, kNowhereDense, epsPos, bBalls Fact,
				) {
					byInduction := a.Have(
						"every finite family of open balls shrinks off K by induction",
						Statement{
							Binders:    "∀n:num. ∀F:(num → prod(A, real)).",
							Hypotheses: []string{"∀i:num. i < n ⇒ fst(F(i)) ∈ M ∧ &0 < snd(F(i))"},
							Conclusion: "∃F':(num → prod(A, real)). «shrinking»(F', F, n, K, ε)",
						},
						Derive(func(a *Argument) {
							a.Induct("n")
							a.Base(
								"with no index below 0, F is its own shrinking",
								func(b *Argument) {
									F := b.FixAs[Fun[Nat, Prod[A, Real]]]("F")
									b.Assume()
									b.Take(F)
									b.Show(
										"every index bound below zero holds vacuously",
										By(nat_order.LessThanZeroClause),
									)
								})
							a.Step(
								"if every n open balls shrink off K, so do any suc(n)",
								func(b *Argument, ih Fact) {
									n := b.TermAs[Nat]("n")
									F := b.FixAs[Fun[Nat, Prod[A, Real]]]("F")
									fBalls := b.Assume()

									fBallsN := b.Have(
										"the initial prefix has centres in M and positive radii",
										"∀i:num. i < n ⇒ fst(F(i)) ∈ M ∧ &0 < snd(F(i))",
										Derive(func(c *Argument) {
											i := c.FixAs[Nat]("i")
											hi := c.Assume()
											hiSuc := c.Have(
												"index below n lies below suc(n)",
												"i < suc(n)",
												ByArith(hi))
											c.Show(
												"inherited from the full family",
												By(fBalls.At(i), hiSuc))
										}),
									)
									E, propsE := b.ObtainAs[Fun[Nat, Prod[A, Real]]](
										"by the induction hypothesis, choose a shrinking E of the first n balls of F",
										"∃F':(num → prod(A, real)). «shrinking»(F', F, n, K, ε)",
										Named("E"),
										By(ih.At(F), fBallsN),
									)

									hnLtSuc := b.Have(
										"top index lies below suc(n)",
										"n < suc(n)",
										ByArith())
									fnValid := b.Have(
										"the top index ball has centre in M and positive radius",
										"fst(F(n)) ∈ M ∧ &0 < snd(F(n))",
										By(fBalls.At(n), hnLtSuc),
									)

									Q, propsQ := b.ObtainAs[Fun[Nat, Prod[A, Real]]](
										"pairing ball n off K against every ball below it, choose a stage-n shrinking Q of F",
										"∃F':(num → prod(A, real)). «stage»(F', F, n, n)",
										Named("Q"),
										By(
											At(pairTopBallOffNowhereDense, M, d, K, ε, n, F, E, n),
											metric,
											kClosed,
											kNowhereDense,
											epsPos,
											fnValid,
											propsE,
											nat_order.LessEqRefl.At(n)),
									)
									partsQ := b.Conjuncts(
										propsQ,
										"all extended balls stay inside the originals",
										"distinct pairs below n miss K",
										"all lower indices pair cleanly with top index",
									)
									shrunkQ, offKQ, withTopQ := partsQ[0], partsQ[1], partsQ[2]

									allOffQ := b.Have(
										"every distinct pair below the successor count misses K",
										"∀i j:num. i < suc(n) ∧ j < suc(n) ∧ i ≠ j ⇒ «pairOff»(Q, i, j, K)",
										Derive(func(c *Argument) {
											i := c.FixAs[Nat]("i")
											j := c.FixAs[Nat]("j")
											hij := c.Assume()
											c.Cases(c.TermAs[Bool]("i = n"))
											c.When(
												"i equals the top index",
												func(e *Argument, hiEqN Fact) {
													hjLtN := e.Have(
														"j must lie strictly below the top index",
														"j < n",
														ByArith(hij, hiEqN))
													e.Show(
														"second orientation against the top index holds",
														By(hiEqN, withTopQ.At(j), hjLtN))
												})
											c.Otherwise(
												"i is strictly below the top index",
												func(e *Argument, hiNeN Fact) {
													hiLtN := e.Have(
														"i lies strictly below the top index",
														"i < n",
														ByArith(hij, hiNeN))
													e.Cases(e.TermAs[Bool]("j = n"))
													e.When(
														"j equals the top index",
														func(f *Argument, hjEqN Fact) {
															f.Show(
																"first orientation against the top index holds",
																By(hjEqN, withTopQ.At(i), hiLtN))
														})
													e.Otherwise(
														"both indices lie strictly below the top index",
														func(f *Argument, hjNeN Fact) {
															hjLtN := f.Have(
																"j lies strictly below the top index",
																"j < n",
																ByArith(hij, hjNeN))
															f.Show(
																"both indices already missed K from the previous stage",
																By(offKQ.At(i, j), hiLtN, hjLtN, hij))
														})
												})
										}),
									)
									b.Take(Q)
									b.Show(
										"both the ball invariants and pairwise disjointness hold for the successor count",
										By(shrunkQ, allOffQ))
								})
						}),
					)

					a.Show(
						"in particular the m given balls shrink off K",
						By(byInduction.At(m, B), bBalls))
				},
			)

			// A Cantor scheme of balls: level n holds 2ⁿ balls of radius below 1/(n+1), each ball of level n+1 lies in its parent, and distinct balls of level n+1 have products missing G(n).
			cantorBallScheme := ctx.Lemma(
				Statement{
					Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:A. ∀G:(num → set(prod(A, A))).",
					Hypotheses: []string{
						"metric_space(M, d)",
						"x ∈ M",
						"∀n:num. closed_in(«prodTop», G(n)) ∧ nowhere_dense(«prodTop», G(n))",
					},
					Abbrev: Abbrev{
						{Name: "levelValid", Text: "λS₁:(num → prod(A, real)). λn₁:num. ∀i:num. " +
							"    i < 2 ^ n₁ ⇒ fst(S₁(i)) ∈ M ∧ &0 < snd(S₁(i))"},
					},
					Conclusion: "∃B:(num → num → prod(A, real)). " +
						"    (∀n i:num. " +
						"        i < 2 ^ n ⇒ fst(B(n, i)) ∈ M ∧ &0 < snd(B(n, i)) ∧ snd(B(n, i)) < real_inv(&n + &1)) ∧ " +
						"    (∀n i:num. " +
						"        i < 2 ^ suc(n) ⇒ " +
						"        «cballAt»(B(suc(n), i)) ⊆ " +
						"        ball(M, d, fst(B(n, rem(i, 2 ^ n))), snd(B(n, rem(i, 2 ^ n))))) ∧ " +
						"    (∀n i j:num. " +
						"        i < 2 ^ suc(n) ∧ j < 2 ^ suc(n) ∧ i ≠ j ⇒ " +
						"        set_cross(«cballAt»(B(suc(n), i)), «cballAt»(B(suc(n), j))) ∩ G(n) = ∅)",
				},
				func(
					a *Argument,
					M *Expr[Set[A]],
					d *Expr[Fun2[A, A, Real]],
					x *Expr[A],
					G *Expr[Fun[Nat, Set[Prod[A, A]]]],
					metric metric_space.MetricSpaceFact[on.M],
					xMem, gClosedND Fact,
				) {
					stepExists := a.Have(
						"any valid level of open balls shrinks to a split level avoiding G(n)",
						Statement{
							Binders:    "∀P:(num → prod(A, real)). ∀n:num.",
							Hypotheses: []string{"«levelValid»(P, n)"},
							Conclusion: "∃B':(num → prod(A, real)). «stepNext»(P, n, B')",
						},
						Derive(func(b *Argument) {
							b.FixAs[Fun[Nat, Prod[A, Real]]]("P")
							n := b.FixAs[Nat]("n")
							hpValid := b.Assume()
							invPos := b.Have(
								"the target radius bound is positive",
								"&0 < real_inv(&suc(n) + &1)",
								ByArith(real_order_field.InvPos.At(b.TermAs[Real]("&suc(n) + &1"))),
							)
							parentValid := b.Have(
								"duplicating level n gives every index i a valid parent, ball rem(i, 2 ^ n) of level n",
								"∀i:num. fst(P(rem(i, 2 ^ n))) ∈ M ∧ &0 < snd(P(rem(i, 2 ^ n)))",
								Derive(func(c *Argument) {
									i := c.FixAs[Nat]("i")
									pow := c.TermAs[Nat]("2 ^ n")
									c.Show(
										"the remainder of i at 2 ^ n lies below 2 ^ n, where level n is valid",
										By(hpValid, nat_div_mod.Division.At(i, pow), nat_arith.PowTwoNonzero.At(n)),
									)
								}),
							)
							b.Show(
								"the 2 ^ suc(n) doubled balls shrink below 1/suc(suc(n)) and off G(n)",
								By(
									parentValid,
									gClosedND.At(n),
									metric,
									invPos,
									At(
										shrinkBallsOffNowhereDense,
										M,
										d,
										b.TermAs[Set[Prod[A, A]]]("G(n)"),
										b.TermAs[Real]("real_inv(&suc(n) + &1)"),
										b.TermAs[Nat]("2 ^ suc(n)"),
										b.TermAs[Fun[Nat, Prod[A, Real]]]("λi:num. P(rem(i, 2 ^ n))"))),
							)
						}),
					)

					step, chosen := a.ObtainAs[Fun2[Fun[Nat, Prod[A, Real]], Nat, Fun[Nat, Prod[A, Real]]]](
						"one such split level chosen for every valid level P and depth n",
						"∃step:((num → prod(A, real)) → num → num → prod(A, real)). ∀P:(num → prod(A, real)). ∀n:num. "+
							"    «levelValid»(P, n) ⇒ «stepNext»(P, n, step(P, n))",
						By(stepExists),
					)

					B, hBRec := a.ObtainAs[Fun2[Nat, Nat, Prod[A, Real]]](
						"choose B recursively: every ball of level 0 is (x, 1/2), and level suc(n) is step(B(n), n)",
						"∃B:(num → num → prod(A, real)). ∀n:num. "+
							"    (λi:num. (x, real_inv(&2))) = B(0) ∧ B(suc(n)) = step(B(n), n)",
						By(nat_arith.PrimRecursion.At(
							step, a.TermAs[Fun[Nat, Prod[A, Real]]]("λi:num. (x, real_inv(&2))"))),
					)

					bBounds := a.Have(
						"every entry in B stays in M with positive shrinking radius",
						"∀n i:num. i < 2 ^ n ⇒ fst(B(n, i)) ∈ M ∧ &0 < snd(B(n, i)) ∧ snd(B(n, i)) < real_inv(&n + &1)",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							b.Induct(n)
							b.Base(
								"at level 0 the constant ball (x, 1/2) satisfies 1/2 < 1",
								func(c *Argument) {
									half := c.TermAs[Real]("real_inv(&2)")
									radius := c.Have(
										"1/2 is positive and below 1/(0 + 1)",
										"&0 < real_inv(&2) ∧ real_inv(&2) < real_inv(&0 + &1)",
										ByArith(),
									)
									c.Show(
										"every ball of level 0 is (x, 1/2), and x lies in M",
										By(hBRec, xMem, radius, pairs.Fst.At(x, half), pairs.Snd.At(x, half)),
									)
								},
							)
							b.Step(
								"level suc(n) is step(B(n), n), whose centres lie in M and radii below 1/suc(suc(n))",
								func(c *Argument, ih Fact) {
									c.Show(
										"level n is valid, so the chosen step bounds level suc(n)",
										By(ih, hBRec.At(n), chosen.At(c.TermAs[Fun[Nat, Prod[A, Real]]]("B(n)"), n)),
									)
								},
							)
						}),
					)

					bNested := a.Have(
						"every closed ball at level suc(n) sits inside its parent open ball at level n",
						Statement{
							Binders:    "∀n i:num.",
							Hypotheses: []string{"i < 2 ^ suc(n)"},
							Conclusion: "«cballAt»(B(suc(n), i)) ⊆ " +
								"ball(M, d, fst(B(n, rem(i, 2 ^ n))), snd(B(n, rem(i, 2 ^ n))))",
						},
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							b.Show(
								"level n is valid, so the chosen step nests level suc(n) in it",
								By(bBounds.At(n), hBRec.At(n), chosen.At(b.TermAs[Fun[Nat, Prod[A, Real]]]("B(n)"), n)),
							)
						}),
					)

					bDisjoint := a.Have(
						"distinct balls at level suc(n) have product disjoint from G(n)",
						Statement{
							Binders:    "∀n i j:num.",
							Hypotheses: []string{"i < 2 ^ suc(n) ∧ j < 2 ^ suc(n) ∧ i ≠ j"},
							Conclusion: "set_cross(«cballAt»(B(suc(n), i)), «cballAt»(B(suc(n), j))) ∩ G(n) = ∅",
						},
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							b.Show(
								"level n is valid, so the chosen step parts level suc(n) off G(n)",
								By(bBounds.At(n), hBRec.At(n), chosen.At(b.TermAs[Fun[Nat, Prod[A, Real]]]("B(n)"), n)),
							)
						}),
					)

					a.Take(B)
					a.Show(
						"the recursive scheme satisfies bounds, nesting, and separation",
						By(bBounds, bNested, bDisjoint),
					)
				},
			)

			// The closed balls along every binary branch s are nested, with radii tending to zero, so in the complete space they have a common point c(s) (NestedClosedBallsMeet).
			cantorSchemeLimits := ctx.Lemma(
				Statement{
					Binders: "∀M:set(A). ∀d:(A → A → real). ∀B:(num → num → prod(A, real)).",
					Hypotheses: []string{
						"metric_space(M, d)",
						"metric_complete(M, d)",
						"∀n i:num. i < 2 ^ n ⇒ fst(B(n, i)) ∈ M ∧ &0 ≤ snd(B(n, i)) ∧ snd(B(n, i)) < real_inv(&n + &1)",
						"∀n i:num. " +
							"    i < 2 ^ suc(n) ⇒ " +
							"    «cballAt»(B(suc(n), i)) ⊆ ball(M, d, fst(B(n, rem(i, 2 ^ n))), snd(B(n, rem(i, 2 ^ n))))",
					},
					Conclusion: "∃c:(set(num) → A). ∀s:set(num). ∀n:num. c(s) ∈ «branchBall»(s, n)",
				},
				func(
					a *Argument,
					M *Expr[Set[A]],
					d *Expr[Fun2[A, A, Real]],
					B *Expr[Fun2[Nat, Nat, Prod[A, Real]]],
					metric metric_space.MetricSpaceFact[on.M],
					complete, bBounds, bNested Fact,
				) {
					branchLimits := a.Have(
						"every binary branch s admits an intersection point across all levels",
						"∀s:set(num). ∃l:A. ∀n:num. l ∈ «branchBall»(s, n)",
						Derive(func(b *Argument) {
							s := b.FixAs[Set[Nat]]("s")
							parentIdx := b.Have(
								"dropping the highest bit of a branch word recovers its parent word",
								"∀n:num. rem(word_of_bits(suc(n), s), 2 ^ n) = word_of_bits(n, s)",
								Derive(func(c *Argument) {
									n := c.FixAs[Nat]("n")
									word := c.TermAs[Nat]("word_of_bits(n, s)")
									c.Show(
										"the word at suc(n) adds a multiple of 2 ^ n to the word at n, which lies below 2 ^ n",
										By(
											machine_word.WordOfBitsDef,
											word_bits.WordOfBitsBound.At(n, s),
											nat_div_mod.ModMultAdd,
											nat_div_mod.ModLessThan.At(word, c.TermAs[Nat]("2 ^ n"))),
									)
								}),
							)

							branchBalls := b.Have(
								"the balls along s are about points of M, of radius at least zero",
								"∀n:num. fst(B(n, word_of_bits(n, s))) ∈ M ∧ &0 ≤ snd(B(n, word_of_bits(n, s)))",
								Derive(func(c *Argument) {
									n := c.FixAs[Nat]("n")
									c.Show(
										"the word of s at n lies below 2 ^ n, where the balls of level n are bounded",
										By(bBounds.At(n, c.TermAs[Nat]("word_of_bits(n, s)")), word_bits.WordOfBitsBound.At(n, s)),
									)
								}),
							)
							vanishing := b.Have(
								"the radii along s tend to zero, the n-th being below 1/(n + 1)",
								"∀ε:real. &0 < ε ⇒ ∃n:num. snd(B(n, word_of_bits(n, s))) < ε",
								Derive(func(c *Argument) {
									ε := c.FixAs[Real]()
									positive := c.Assume()
									N, small := c.ObtainAs[Nat](
										"some 1/(N + 1) is below ε",
										"∃N:num. real_inv(&N + &1) < ε",
										By(positive, real_archimedean.ExistsReciprocalBelow.At(ε)),
									)
									c.Take(N)
									c.Show(
										"the word of s at N lies below 2 ^ N, so the N-th radius along s is below 1/(N + 1)",
										ByArith(
											small,
											bBounds.At(N, c.TermAs[Nat]("word_of_bits(N, s)")),
											word_bits.WordOfBitsBound.At(N, s)),
									)
								}),
							)
							nestedBranch := b.Have(
								"the closed balls along branch s form a descending chain",
								"∀n:num. «branchBall»(s, n + 1) ⊆ «branchBall»(s, n)",
								Derive(func(c *Argument) {
									n := c.FixAs[Nat]("n")
									subBall := c.Have(
										"the successor closed ball lies in the parent open ball",
										"«branchBall»(s, suc(n)) ⊆ "+
											"ball(M, d, fst(B(n, word_of_bits(n, s))), snd(B(n, word_of_bits(n, s))))",
										By(parentIdx.At(n), bNested, word_bits.WordOfBitsBound.At(c.TermAs[Nat]("suc(n)"), s)),
									)
									c.Show(
										"the open ball lies in the closed ball of the same centre and radius, and n + 1 is suc(n)",
										BySets(
											subBall,
											nat_arith.Add1.At(n),
											metric_space.BallSubsetClosedBall.At(
												M,
												d,
												c.TermAs[A]("fst(B(n, word_of_bits(n, s)))"),
												c.TermAs[Real]("snd(B(n, word_of_bits(n, s)))"))),
									)
								}),
							)
							b.Show(
								"the space being complete, the nested closed balls along s, whose radii tend to zero, meet",
								By(
									metric,
									complete,
									branchBalls,
									nestedBranch,
									vanishing,
									complete_metric.NestedClosedBallsMeet.At(
										M,
										d,
										b.TermAs[Fun[Nat, A]]("λn:num. fst(B(n, word_of_bits(n, s)))"),
										b.TermAs[Fun[Nat, Real]]("λn:num. snd(B(n, word_of_bits(n, s)))"))),
							)
						}),
					)
					a.Show(
						"choose one intersection limit c(s) for each branch s",
						By(branchLimits),
					)
				},
			)

			return ctx.Theorem(headline,
				func(
					arg *Argument,
					T *Expr[Set[Set[A]]],
					r *Expr[Set[Prod[A, A]]],
					tPolish, tNonempty, tNoIso, rMeager Fact,
				) {
					d, hdMetric := arg.ObtainAs[Fun2[A, A, Real]](
						"choose a compatible complete metric d on ⋃T",
						"∃d:(A → A → real). metric_space(⋃T, d) ∧ metric_complete(⋃T, d) ∧ metric_topology(⋃T, d) = T",
						By(tPolish, polish_space.PolishSpaceDef.At(T)),
					)
					metricParts := arg.Conjuncts(
						hdMetric,
						"d is a metric on ⋃T",
						"d is complete",
						"and its topology is T",
					)
					metric, complete, metricTopology := metricParts[0], metricParts[1], metricParts[2]
					x0, hx0 := arg.ObtainAs[A](
						"choose a basepoint x₀ in ⋃T",
						"∃x:A. x ∈ ⋃T",
						By(tNonempty, set_basic.MemberNotEmpty.At(arg.TermAs[Set[A]]("⋃T"))),
					)
					topology := arg.Have(
						"T is a topology",
						"is_topology(T)",
						By(tPolish, polish_space.PolishSpaceDef.At(T)),
					)
					prodTopology := arg.Have(
						"product_topology(T, T) is a topology",
						"is_topology(product_topology(T, T))",
						By(product_topology.ProductTopology.At(T, T), topology),
					)
					_, covered := arg.ObtainAs[Fun[Nat, Set[Prod[A, A]]]](
						"r is meager, so it lies in an increasing sequence of closed nowhere dense sets N(n) of T × T",
						"∃N:(num → set(prod(A, A))). "+
							"    (∀n:num. "+
							"        closed_in(product_topology(T, T), N(n)) ∧ "+
							"        nowhere_dense(product_topology(T, T), N(n))) ∧ "+
							"    (∀m n:num. m ≤ n ⇒ N(m) ⊆ N(n)) ∧ "+
							"    r ⊆ ⋃image(N, 𝕌)",
						By(rMeager, MeagerClosedCover.Read(prodTopology).At(r)),
					)
					coverParts := arg.Conjuncts(
						covered,
						"every N(n) is closed and nowhere dense in T × T",
						"N grows with n",
						"r lies in the union of the N(n)",
					)
					hausdorff := arg.Have(
						"T is the topology of a metric, so it is Hausdorff",
						"hausdorff(T)",
						By(Normalized, metricTopology, metric_space.MetricHausdorff.Read(metric)),
					)
					diag := arg.TermAs[Set[Prod[A, A]]]("set_diagonal(⋃T)")
					diagProps := arg.Have(
						"the diagonal of ⋃T × ⋃T is closed and nowhere dense in T × T",
						"closed_in(product_topology(T, T), set_diagonal(⋃T)) ∧ "+
							"nowhere_dense(product_topology(T, T), set_diagonal(⋃T))",
						By(topology, hausdorff, tNoIso, DiagonalClosedNowhereDense.At(T)),
					)
					G, gDef := arg.LetAs[Fun[Nat, Set[Prod[A, A]]]]("G", "λn:num. set_diagonal(⋃T) ∪ N(n)")
					gClosedT := arg.Have(
						"every G(n), the diagonal with N(n), is closed and nowhere dense in T × T",
						"∀n:num. closed_in(product_topology(T, T), G(n)) ∧ nowhere_dense(product_topology(T, T), G(n))",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							layer := b.TermAs[Set[Prod[A, A]]]("N(n)")
							b.Show(
								"two closed nowhere dense sets unite to one",
								By(
									Normalized,
									gDef,
									diagProps,
									coverParts[0].At(n),
									topological_space.UnionClosed.Read(prodTopology).At(diag, layer),
									NowhereDenseUnion.Read(prodTopology).At(diag, layer)),
							)
						}),
					)
					gHolds := arg.Have(
						"every G(n) holds the diagonal and N(n)",
						"∀n:num. set_diagonal(⋃T) ⊆ G(n) ∧ N(n) ⊆ G(n)",
						BySets(gDef),
					)
					gClosedMetric := arg.Have(
						"every G(n) is closed and nowhere dense in the square of the metric topology of d",
						"∀n:num. "+
							"    closed_in(product_topology(metric_topology(⋃T, d), metric_topology(⋃T, d)), G(n)) ∧ "+
							"    nowhere_dense(product_topology(metric_topology(⋃T, d), metric_topology(⋃T, d)), G(n))",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							b.Show(
								"since the metric topology of d is T",
								By(Normalized, gClosedT.At(n), metricTopology),
							)
						}),
					)
					B, hB := arg.ObtainAs[Fun2[Nat, Nat, Prod[A, Real]]](
						"choose a Cantor scheme of balls whose level suc(n) has its products off G(n)",
						"∃B:(num → num → prod(A, real)). "+
							"    (∀n i:num. "+
							"        i < 2 ^ n ⇒ fst(B(n, i)) ∈ ⋃T ∧ &0 < snd(B(n, i)) ∧ snd(B(n, i)) < real_inv(&n + &1)) ∧ "+
							"    (∀n i:num. "+
							"        i < 2 ^ suc(n) ⇒ "+
							"        closed_ball(⋃T, d, fst(B(suc(n), i)), snd(B(suc(n), i))) ⊆ "+
							"        ball(⋃T, d, fst(B(n, rem(i, 2 ^ n))), snd(B(n, rem(i, 2 ^ n))))) ∧ "+
							"    (∀n i j:num. "+
							"        i < 2 ^ suc(n) ∧ j < 2 ^ suc(n) ∧ i ≠ j ⇒ "+
							"        set_cross(closed_ball(⋃T, d, fst(B(suc(n), i)), snd(B(suc(n), i))), "+
							"            closed_ball(⋃T, d, fst(B(suc(n), j)), snd(B(suc(n), j)))) ∩ "+
							"        G(n) = "+
							"        ∅)",
						By(gClosedMetric, hx0, metric, At(cantorBallScheme, arg.TermAs[Set[A]]("⋃T"), d, x0, G)),
					)
					bParts := arg.Conjuncts(
						hB,
						"centres stay in ⋃T with vanishing radii",
						"successor closed balls sit inside parent open balls",
						"distinct branch products at level suc(n) miss G(n)",
					)
					bBounds, bNested, bDisjoint := bParts[0], bParts[1], bParts[2]
					radii := arg.Have(
						"the balls of the scheme are about points of ⋃T, of radius at least zero and below 1/(n + 1)",
						"∀n i:num. i < 2 ^ n ⇒ fst(B(n, i)) ∈ ⋃T ∧ &0 ≤ snd(B(n, i)) ∧ snd(B(n, i)) < real_inv(&n + &1)",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							i := b.FixAs[Nat]("i")
							below := b.Assume()
							b.Show(
								"the radius is positive",
								ByArith(bBounds.At(n, i), below))
						}),
					)
					c, hc := arg.ObtainAs[Fun[Set[Nat], A]](
						"choose a point c(s) in every closed ball along each branch s",
						"∃c:(set(num) → A). ∀s:set(num). ∀n:num. "+
							"    c(s) ∈ closed_ball(⋃T, d, fst(B(n, word_of_bits(n, s))), snd(B(n, word_of_bits(n, s))))",
						By(radii, bNested, metric, complete, At(cantorSchemeLimits, arg.TermAs[Set[A]]("⋃T"), d, B)),
					)
					avoidG := arg.Have(
						"if s and t differ at k then (c(s), c(t)) avoids G(n) for every n at least k",
						"∀s t:set(num). ∀n k:num. k ≤ n ∧ ¬(k ∈ s ⇔ k ∈ t) ⇒ (c(s), c(t)) ∉ G(n)",
						Derive(func(b *Argument) {
							s := b.FixAs[Set[Nat]]("s")
							t := b.FixAs[Set[Nat]]("t")
							n := b.FixAs[Nat]("n")
							k := b.FixAs[Nat]("k")
							hkDiff := b.Assume()
							sucN := b.TermAs[Nat]("suc(n)")
							wordsDistinct := b.Have(
								"at depth suc(n) the prefix words for s and t are valid and distinct",
								"word_of_bits(suc(n), s) < 2 ^ suc(n) ∧ "+
									"word_of_bits(suc(n), t) < 2 ^ suc(n) ∧ "+
									"word_of_bits(suc(n), s) ≠ word_of_bits(suc(n), t)",
								By(
									hkDiff,
									word_bits.WordOfBitsBound.At(sucN, s),
									word_bits.WordOfBitsBound.At(sucN, t),
									bit_set.EqByBitSetBelow.At(sucN, s, t),
									nat_order.LessThanSucIffLessEq.At(k, n)),
							)
							b.Show(
								"the pair (c(s), c(t)) lies in the disjoint closed ball product at suc(n)",
								BySets(
									hc.At(s, sucN),
									hc.At(t, sucN),
									bDisjoint.At(n, b.TermAs[Nat]("word_of_bits(suc(n), s)"), b.TermAs[Nat]("word_of_bits(suc(n), t)")),
									wordsDistinct,
									set_product.InCross.At(
										b.TermAs[Set[A]](
											"closed_ball(⋃T, "+
												"    d, "+
												"    fst(B(suc(n), word_of_bits(suc(n), s))), "+
												"    snd(B(suc(n), word_of_bits(suc(n), s))))"),
										b.TermAs[Set[A]](
											"closed_ball(⋃T, "+
												"    d, "+
												"    fst(B(suc(n), word_of_bits(suc(n), t))), "+
												"    snd(B(suc(n), word_of_bits(suc(n), t))))"),
										b.TermAs[A]("c(s)"),
										b.TermAs[A]("c(t)"))),
							)
						}),
					)
					cInSpace := arg.Have(
						"every branch limit c(s) lies in ⋃T",
						"∀s:set(num). c(s) ∈ ⋃T",
						Derive(func(b *Argument) {
							s := b.FixAs[Set[Nat]]("s")
							zero := b.TermAs[Nat]("0")
							b.Show(
								"level-0 closed ball membership places c(s) inside ⋃T",
								BySets(
									hc.At(s, zero),
									metric_space.ClosedBallDef.At(
										b.TermAs[Set[A]]("⋃T"),
										d,
										b.TermAs[A]("fst(B(0, word_of_bits(0, s)))"),
										b.TermAs[Real]("snd(B(0, word_of_bits(0, s)))"))),
							)
						}),
					)
					cInj := arg.Have(
						"distinct subsets of ℕ receive distinct branch limits",
						"injective_on(𝕌⟨A:set(num)⟩, c)",
						Derive(func(b *Argument) {
							b.Do(Simp(Fwd(functions.InjectiveOnDef)))
							s := b.FixAs[Set[Nat]]("s")
							t := b.FixAs[Set[Nat]]("t")
							hst := b.Assume()
							hsNe := b.SupposeNot()
							k, hkDiff := b.ObtainAs[Nat](
								"choose a k in exactly one of s and t",
								"∃k:num. ¬(k ∈ s ⇔ k ∈ t)",
								By(hsNe, set_basic.NotEqualSets.At(s, t)),
							)
							cs := b.TermAs[A]("c(s)")
							ct := b.TermAs[A]("c(t)")
							limitsOnDiagonal := b.Have(
								"c(s) = c(t) is a point of ⋃T, so (c(s), c(t)) lies on the diagonal",
								"(c(s), c(t)) ∈ set_diagonal(⋃T)",
								BySets(cInSpace.At(s), hst, set_product.InDiagonal.At(b.TermAs[Set[A]]("⋃T"), cs, ct)),
							)
							b.Show(
								"the diagonal lies in G(k), which (c(s), c(t)) avoids",
								BySets(limitsOnDiagonal, gHolds.At(k), avoidG.At(s, t, k, k), hkDiff, nat_order.LessEqRefl.At(k)),
							)
						}),
					)
					cIndep := arg.Have(
						"distinct subsets map to pairs outside the meager relation r",
						"∀s t:set(num). ¬(s = t) ⇒ (c(s), c(t)) ∉ r",
						Derive(func(b *Argument) {
							s := b.FixAs[Set[Nat]]("s")
							t := b.FixAs[Set[Nat]]("t")
							hst := b.Assume()
							hInR := b.SupposeNot()
							k, hkDiff := b.ObtainAs[Nat](
								"choose a k in exactly one of s and t",
								"∃k:num. ¬(k ∈ s ⇔ k ∈ t)",
								By(hst, set_basic.NotEqualSets.At(s, t)),
							)
							j, hjInN := b.ObtainAs[Nat](
								"choose an N(j) containing (c(s), c(t))",
								"∃j:num. (c(s), c(t)) ∈ N(j)",
								BySets(hInR, coverParts[2]),
							)
							ordSum := b.Have(
								"both k and j are at most k + j",
								"k ≤ k + j ∧ j ≤ k + j",
								ByArith(),
							)
							kj := b.TermAs[Nat]("k + j")
							b.Show(
								"N(j) lies in N(k + j), inside G(k + j), yet (c(s), c(t)) avoids G(k + j)",
								BySets(hkDiff, avoidG.At(s, t, kj, k), coverParts[1].At(j, kj), gHolds.At(kj), hjInN, ordSum),
							)
						}),
					)
					arg.Take(c)
					arg.Show(
						"c is injective into ⋃T and maps distinct sets outside r",
						By(cInj, cInSpace, cIndep),
					)
				},
			)
		},
	),
	Reading: "The space is nonempty and has no isolated point; without either the conclusion " +
		"fails, the first because c must land in the carrier. The relation is meager in the " +
		"product topology of the space with itself and is not assumed symmetric: both orders of " +
		"a pair of distinct images avoid it. Distinct subsets of ℕ go to distinct, independent " +
		"points, and nothing is asserted about the continuity of c. Separability, a conjunct of " +
		"polish_space, is not used: the proof reads only a compatible complete metric.",
})}
