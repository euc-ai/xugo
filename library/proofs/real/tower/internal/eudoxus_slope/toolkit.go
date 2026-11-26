// toolkit.go — the slope toolkit: what a slope is, and the bounds every argument runs on.
//
// Three parts, marked by banners:
//
// - The defining bound and everything the chapter estimates with
// - The growth bounds the inverse construction runs on
// - Slope equivalence (`nadd_eq`

package eudoxus_slope

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The defining bound and everything the chapter estimates with
// ---------------------------------------------------------------------------
//
// the defining bound and everything the chapter estimates with: linear
// growth, the dist calculus, near-additivity and near-homogeneity, and the
// alternative product estimate. ZeroIsSlope closes the file — the defining
// bound at the constantly-zero function, which is the inhabitant the
// type definition is stamped against.
//
// README: the "toolkit" bullet.

// Cauchy — every slope carrier's representative function obeys
// the defining near-linearity bound:
//
//	⊢ ∀x : nadd. ∃B. ∀m n. nat_dist(m·dest_nadd(x, n), n·dest_nadd(x, m)) ≤ B·(m + n)
//
// The nadd type is carved out of ℕ→ℕ by the predicate is_nadd, so the
// theorem is the typedef's own membership axiom read back through the
// mk_nadd/dest_nadd pair:
//
// - isSlope: is_nadd holds of λm.dest_nadd(x, m). By the membership
// axiom this reduces to dest_nadd(mk_nadd(r)) = r at
// r := λm.dest_nadd(x, m); η collapses r to dest_nadd(x), the
// retraction axiom sends mk_nadd(dest_nadd(x)) back to x, and the
// equation is reflexive.
// - goal: expanding is_nadd at that representative β-reduces to
// exactly the stated bound.
//
// The η-bridge between the two spellings of the representative and
// the iff-plumbing between the typedef axiom and the is_nadd
// expansion are absorbed by the refuter's η/β-normalization.
//
// It cites the two facts the type's definition comes with
// (NaddDef.Retraction and NaddDef.Membership, definitions.go).
var Cauchy = cauchyThm{family.Add(registry.ProofEntry{
	Name: "Cauchy",
	Key:  "prop_1b6a2684d1212aef",
	// The proof is one lemma plus the assembly: `isSlope` is a Go local the
	// goal cites by closure capture.
	Build: family.Sections(
		"∀x:nadd. ∃B:num. ∀m n:num. dist((m * dest_nadd(x, n), n * dest_nadd(x, m))) ≤ B * (m + n)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			retraction, membership := naddTypeDefAxioms(ctx)

			x_0 := ctx.Var("x_0", MakeType("nadd"))
			m := ctx.Var("m", NumType)
			// representative = λm. x₀(m), the function whose slope-hood is claimed.
			representative := m.To(v.DestNadd.Apply(x_0, m))

			// isSlope: the representative function of every carrier is a slope —
			// the two typedef axioms make the membership equation reflexive.
			isSlope := ctx.Lemma("∀x:nadd. is_nadd(λm:num. dest_nadd(x, m))",
				func(a *Argument) {
					a.Do(
						UseLemma(retraction),
						// is_nadd(r) ⇔ dest_nadd(mk_nadd(r)) = r
						UseLemma(membership),
						Given(func(a *Argument, membershipIff Fact) {
							a.Do(
								StripQuant(),                     // fix x₀
								membershipIff.At(representative), // membership read at r := λm. x₀(m)
								// η collapses r to dest_nadd(x₀), retraction sends
								// mk_nadd(dest_nadd(x₀)) to x₀, so dest_nadd(mk_nadd(r)) = r
								// is reflexive.
								CnfRefute(),
							)
						}),
					)
				})

			// goal: with isSlope in scope, expanding is_nadd at λm.dest_nadd(x, m)
			// β-reduces the goal to the hypothesis itself — the def-expand
			// composite's own simplification closes it, no refutation left.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(Cite(isSlope), Unfold(IsNaddDef))
				})
		}),
})}

// LinearBound — every slope is pinned under a line:
//
//	⊢ ∀x:nadd. ∃A B. ∀n. dest_nadd(x, n) ≤ A·n + B
//
// The classic one-liner off the defining bound (Cauchy)
// instantiated at (m, n) := (n, 1):
//
//	nat_dist(n·x(1), 1·x(n)) ≤ B₀·(n + 1)
//
// whose two-sided reading (nat_monus.DistLessEqCases) gives in particular
// x(n) ≤ n·x(1) + B₀·(n+1); re-associating the right-hand side
// yields the linear bound with A := B₀ + x(1) and B := B₀.
//
// Two gated-Arith closes (arith:nat): the ring identity relating the
// witness form to the Cauchy form, and the final transport of the
// dist bound across it.
var LinearBound = linearBoundThm{family.Add(registry.ProofEntry{
	Name: "LinearBound",
	Key:  "prop_a51e4465e894da94",
	// Cauchy bound at (m, n) := (n₀, 1), unpacked and re-associated.
	Build: family.Theorem("∀x:nadd. ∃A B:num. ∀n:num. dest_nadd(x, n) ≤ A * n + B",
		func(a *Argument, x Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := ctx.Numeral(1)
			n_0 := ctx.Var("n_0", NumType)

			// Bring in the slope's defining bound at x₀:
			// ∃B. ∀m n. nat_dist(m·x₀(n), n·x₀(m)) ≤ B·(m+n)
			// unpacking the Cauchy constant B₀ out of the ∃.
			B_0, cauchyX := a.Unpack(At(Cauchy, x))

			a.Do(
				// The line: A := B₀ + x₀(1), B := B₀.
				Witness(v.sum(B_0, v.at(x, one))),
				Witness(B_0),
				// Fix n₀.
				StripQuant(),
			)

			// The second side of the dist bound, 1·x₀(n₀) ≤ n₀·x₀(1) +
			// B₀·(n₀+1), is the goal up to ring re-association of the bound.
			identity := a.Have(
				"(B₀ + x₀(1))·n₀ + B₀ = n₀·x₀(1) + B₀·(n₀+1) — distribute and re-associate, a ring identity",
				ctx.MakePropText("(B₀ + dest_nadd(x₀, 1)) * n₀ + B₀ = n₀ * dest_nadd(x₀, 1) + B₀ * (n₀ + 1)"),
				ByArith())
			a.Show(
				"x₀(n₀) = 1·x₀(n₀) ≤ n₀·x₀(1) + B₀·(n₀+1) — the dist "+
					"bound's second side, carried across the identity",
				ByArith(
					// The proof's one idea: the Cauchy bound at (m, n) :=
					// (n₀, 1) compares n₀·x₀(1) against 1·x₀(n₀):
					// nat_dist(n₀·x₀(1), 1·x₀(n₀)) ≤ B₀·(n₀ + 1)
					cauchyX.At(n_0, one),
					// dist ≤ in its two-sided reading: at these witnesses
					// the instance's second conjunct is the bound, modulo
					// the identity.
					At(nat_monus.DistLessEqCases,
						v.mul(B_0, v.sum(n_0, one)), // m := B₀·(n₀+1)
						v.mul(one, v.at(x, n_0)),    // n := 1·x₀(n₀)
						v.mul(n_0, v.at(x, one)),    // p := n₀·x₀(1)
					),
					identity))
		}),
})}

// stepBound — a slope's consecutive steps are uniformly
// bounded:
//
//	⊢ ∀x:nadd. ∃B. ∀n. nat_dist(dest_nadd(x, suc(n)), dest_nadd(x, n)) ≤ B
//
// Writing f = dest_nadd(x, ·), this is the near-additivity bound
// (additive), with constant B₀, read at the pair (n, 1): since
// suc(n) = n + 1 (nat_arith.Add1),
//
//	nat_dist(f(suc n), f(n) + f(1)) ≤ B₀,
//
// and the triangle inequality (nat_monus.DistTriangle) through the midpoint
// f(n) + f(1) — whose distance back to f(n) is exactly f(1)
// (nat_monus.DistLeftAdd) — bounds every step by B := B₀ + f(1).
//
// The three ground estimates feed one Arith close directly — no
// nat_order.LessEqTrans / nat_order.LessEqAdd2 chaining.
var stepBound = stepBoundThm{family.Add(registry.ProofEntry{
	Name: "stepBound",
	Key:  "prop_65b1b6ac5591e33e",
	// goal — with f = dest_nadd(x, ·), take B := B₀ + f(1) where B₀ is x's
	// near-additivity bound.
	Build: family.Theorem("∀x:nadd. ∃B:num. ∀n:num. dist((dest_nadd(x, suc(n)), dest_nadd(x, n))) ≤ B",
		func(a *Argument, x Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := ctx.Numeral(1)
			n_0 := ctx.Var("n_0", NumType)
			// f is the slope's underlying function at t: dest_nadd(x₀, t).
			f := func(t Term) Term { return v.at(x, t) }

			// Near-additivity of x₀: ∃B.∀m n. nat_dist(f(m+n), f(m)+f(n)) ≤ B,
			// unpacked to its Skolem bound B₀.
			B_0, additiveX := a.Unpack(At(additive, x))

			a.Do(
				// The uniform step bound: B := B₀ + f(1).
				Witness(v.sum(B_0, f(one))),
				StripQuant(),
				AssertStep(ctx.MakePropText(
					"dist((dest_nadd(x₀, suc(n₀)), dest_nadd(x₀, n₀) + dest_nadd(x₀, 1))) ≤ B₀"),
					Case(
						"near-additivity at (n₀, 1) — f(suc n₀) = f(n₀ + "+
							"1) (nat_arith.Add1) lies within B₀ of f(n₀) + f(1)",
						additiveX.At(n_0, one),
						Cite(nat_arith.Add1),
					),
					Case(
						"dist(f(suc n₀), f(n₀)) ≤ B₀ + f(1) by the triangle through the "+
							"midpoint f(n₀) + f(1), whose leg back to f(n₀) is exactly f(1)",
						Given(func(b *Argument, midpoint Fact) {
							b.Show(
								"linear arithmetic over the three ground dist estimates",
								ByArith(
									midpoint,
									// nat_dist(f(suc n₀), f(n₀)) ≤ nat_dist(f(suc n₀), f(n₀)+f(1)) + nat_dist(f(n₀)+f(1), f(n₀))
									At(nat_monus.DistTriangle,
										f(v.Suc.Apply(n_0)), v.sum(f(n_0), f(one)), f(n_0)),
									// f(1) = nat_dist(f(n₀)+f(1), f(n₀))
									At(nat_monus.DistLeftAdd, f(n_0), f(one))))
						}),
					),
				),
			)
		}),
})}

// shiftBound — the n-step shift bound:
//
//	⊢ ∀x : nadd. ∃B. ∀m n. nat_dist(x(m + n), x(m)) ≤ B · n
//
// (writing x(m) for dest_nadd(x, m)). The bound B is exactly the
// unit-step bound from stepBound: if each step of x moves the
// value by at most B, then n steps move it by at most B·n. The proof
// is that one sentence, split into 2 sections:
//
// - lemma1: the iterated step bound — for ANY x and B, if
// ∀k. nat_dist(x(suc k), x(k)) ≤ B then ∀m n. nat_dist(x(m+n), x(m)) ≤ B·n.
// Induction on the shift n; the step case walks the triangle
// inequality through the intermediate point x(m+n).
// - goal: pick B by stepBound and apply lemma1.
//
// The linear assembly of the two bounds through the triangle
// estimate (nat_monus.DistTriangle) is the gated Arith ministep's.
var shiftBound = shiftBoundThm{family.Add(registry.ProofEntry{
	Name: "shiftBound",
	Key:  "prop_80c5e3709beab017",
	// The proof is two sections written as a linear script: `lemma1` is a Go
	// local the goal cites by closure capture.
	Build: family.Sections(
		"∀x:nadd. ∃B:num. ∀m n:num. dist((dest_nadd(x, m + n), dest_nadd(x, m))) ≤ B * n",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			B_0 := ctx.Var("B_0", NumType)
			m_0 := ctx.Var("m_0", NumType)
			n_0 := ctx.Var("n_0", NumType)

			// lemma1 — the iterated step bound, by induction on the shift n. Each
			// induction step inserts the waypoint x(m+n) between x(m+suc n) and
			// x(m): the first leg is one unit step (≤ B, the hypothesis at
			// k := m+n), the second is the induction hypothesis (≤ B·n), and
			// nat_monus.DistTriangle plus B + B·n = B·suc n assemble the two.
			lemma1 := ctx.Lemma(Statement{
				Binders: "∀x:nadd. ∀B:num.",
				Hypotheses: []string{
					"∀k:num. dist((dest_nadd(x, suc(k)), dest_nadd(x, k))) ≤ B",
				},
				Conclusion: "∀m n:num. dist((dest_nadd(x, m + n), dest_nadd(x, m))) ≤ B * n",
			},
				// unitStep is the ⇒-antecedent, the unit-step bound
				// ∀k. nat_dist(x(suc k), x(k)) ≤ B.
				func(a *Argument, x, B Term, unitStep Fact) {
					a.Do(
						StripQuant(), // fix the shift's arguments m₀, n₀
						ctx.InductStep(n_0,
							Case(
								"a zero shift moves nothing — dist(x(m+0), x(m)) = 0 = B·0, by arith's dist/num normalization",
								ByArith(),
							),
							Case(
								"an (n+1)-step shift is one more unit step on top of an n-step shift",
								Given(func(b *Argument, ih Fact) {
									idxShift := b.Have(
										"index arithmetic — the shifted argument m + suc n IS the successor suc(m + n)",
										ctx.MakePropText("m₀ + suc(n₀) = suc(m₀ + n₀)"),
										ByArith())
									// The identity is consumed as a REWRITE of the goal, which
									// becomes nat_dist(x(suc(m+n)), x(m)) ≤ B·suc n.
									b.Do(idxShift.Rw())
									sucBound := b.Have(
										"the target bound unfolds — B·suc n = B + B·n, by ring arithmetic",
										"B₀ * suc(n₀) = B₀ + B₀ * n₀",
										ByArith())
									b.Show(
										"linear assembly — dist ≤ leg₁ + leg₂ ≤ B + B·n = B·suc n",
										ByArith(
											ih,
											sucBound,
											// leg 1 — the unit step at k := m+n
											unitStep.At(v.sum(m_0, n_0)),
											// leg 2 is the induction hypothesis; nat_monus.DistTriangle joins them at the waypoint
											At(
												nat_monus.DistTriangle,
												v.at(x, v.Suc.Apply(v.sum(m_0, n_0))),
												v.at(x, v.sum(m_0, n_0)),
												v.at(x, m_0))))
								}),
							),
						),
					)
				})

			// goal: stepBound hands us the unit-step bound B of x; that same B
			// witnesses the ∃, and the residual ∀m n bound is exactly lemma1's
			// conclusion.
			return ctx.Theorem(headline,
				func(a *Argument, x Term) {
					a.Do(
						Cite(stepBound, x),
						StripQuant(), // Skolemize the unit-step bound as B₀
						Witness(B_0),
						CiteNode(lemma1),
					)
				})
		}),
})}

// lipschitz — every slope is lipschitz:
//
//	⊢ ∀x:nadd. ∃B. ∀m n. nat_dist(dest_nadd(x, m), dest_nadd(x, n)) ≤ B * nat_dist(m, n)
//
// The proof: the shift bound (shiftBound) already IS the lipschitz
// bound, read along one order of the arguments; the SAME constant B
// works. WLOG m ≤ n by totality (nat_order.LessEqTotal); write the
// larger argument in gap form n = m + d (nat_order.LessEqExists); then
// the shift bound at (m, d) is the whole estimate — dist's symmetry
// and nat_dist(m, m+d) = d are decided by the gated arith dist calculus,
// so no dist lemma is cited at all.
//
// (nat_order.LessEqTotal / nat_order.LessEqExists are the ℕ-order rows;
// slope's own sibling entries LessEqTotal / LessEqExists are the
// slope-order statements and are NOT what this member cites.)
var lipschitz = lipschitzThm{family.Add(registry.ProofEntry{
	Name: "lipschitz",
	Key:  "prop_7c9418f242636780",
	// The proof is two sections written as a linear script: `lemma1` is a Go
	// local the goal cites by closure capture.
	Build: family.Sections(
		"∀x:nadd. ∃B:num. ∀m n:num. dist((dest_nadd(x, m), dest_nadd(x, n))) ≤ B * dist((m, n))",
		func(ctx *Script, headline string) *GoalStackNode {
			ops(ctx)

			B_0 := ctx.Var("B_0", NumType)
			d_0 := ctx.Var("d_0", NumType)
			ctx.Var("m_0", NumType)
			ctx.Var("n_0", NumType)

			// lemma1 — the core: a shift bound with constant B gives the
			// lipschitz bound with the SAME constant. WLOG split on which
			// argument is larger (LessEqTotal); each branch is the shift bound
			// read at the gap. (Writing dest_nadd(x, ·) as x(·) in comments.)
			//
			// shiftEst is the premise — the n-step shift estimate
			// ∀m n. nat_dist(x(m+n), x(m)) ≤ B·n; each WLOG branch grounds it at
			// its gap decomposition of the arguments.
			lemma1 := ctx.Lemma(Statement{
				Binders: "∀x:nadd. ∀B:num.",
				Hypotheses: []string{
					"∀m n:num. dist((dest_nadd(x, m + n), dest_nadd(x, m))) ≤ B * n",
				},
				Conclusion: "∀m n:num. dist((dest_nadd(x, m), dest_nadd(x, n))) ≤ B * dist((m, n))",
			},
				func(a *Argument, x, B Term, shiftEst Fact, m, n Term) {
					a.Do(
						// WLOG on which argument is larger: totality at (m₀, n₀)
						// installs (m₀ ≤ n₀) ∨ (n₀ ≤ m₀) and splits it.
						At(nat_order.LessEqTotal, m, n).SplitDisj(
							LeftHolds(
								"m₀ ≤ n₀ — write n₀ = m₀ + d and read the bound off the shift estimate at (m₀, d)",
								lipschitzLeft(ctx, shiftEst, m, d_0),
							),
							RightHolds(
								"n₀ ≤ m₀ — mirror gap m₀ = n₀ + d, shift estimate at (n₀, d)",
								lipschitzRight(ctx, shiftEst, n, d_0),
							),
						),
					)
				})

			// goal: extract the shift constant B₀ from shiftBound and witness the
			// lipschitz constant with it; the residual is lemma1 at (x₀, B₀),
			// its premise the shift bound just installed.
			return ctx.Theorem(headline,
				func(a *Argument, x Term) {
					a.Do(
						Cite(shiftBound, x),
						StripQuant(), // skolemize the shift constant: B₀
						Witness(B_0),
						Cite(lemma1, x, B_0),
						Assumption(), // the installed instance is the goal
					)
				})
		}),
})}

// lipschitzLeft: under m₀ ≤ n₀, prove nat_dist(x(m₀), x(n₀)) ≤ B·nat_dist(m₀, n₀).
func lipschitzLeft(ctx *Script, shiftEst Fact, m_0, d_0 Term) Action {
	return AssertStep(ctx.MakePropText("∃d:num. n₀ = m₀ + d"),
		Case(
			"m₀ reaches n₀ by some gap d — nat_order.LessEqExists on the branch hypothesis",
			Cite(nat_order.LessEqExists),
		),
		Case(
			"in gap form the goal IS the shift bound at (m₀, d₀), up to dist algebra",
			Given(func(a *Argument, gapExists Fact) {
				// skolemize the gap: d₀ with n₀ = m₀ + d₀
				_, gapEq := a.Unpack(gapExists)
				a.Do(
					gapEq.Rw(), // rewrite n₀ → m₀ + d₀ in goal and hyps
					// shift bound: nat_dist(x(m₀+d₀), x(m₀)) ≤ B·d₀; the dist
					// calculus is the closer's: nat_dist(a,b) = nat_dist(b,a),
					// nat_dist(m, m+d) = d
					ByArith(shiftEst.At(m_0, d_0)),
				)
			}),
		),
	)
}

// lipschitzRight: under n₀ ≤ m₀, the mirror image — same steps with the
// roles of m₀ and n₀ exchanged (here the goal's dist is already in
// shift orientation, but the arith dist calculus absorbs either way).
func lipschitzRight(ctx *Script, shiftEst Fact, n_0, d_0 Term) Action {
	return AssertStep(ctx.MakePropText("∃d:num. m₀ = n₀ + d"),
		Case(
			"n₀ reaches m₀ by some gap d — nat_order.LessEqExists on the branch hypothesis",
			Cite(nat_order.LessEqExists),
		),
		Case(
			"in gap form the goal IS the shift bound at (n₀, d₀), up to dist algebra",
			Given(func(a *Argument, gapExists Fact) {
				// skolemize the gap: d₀ with m₀ = n₀ + d₀
				_, gapEq := a.Unpack(gapExists)
				a.Do(
					gapEq.Rw(), // rewrite m₀ → n₀ + d₀ in goal and hyps
					// shift bound: nat_dist(x(n₀+d₀), x(n₀)) ≤ B·d₀; the dist
					// calculus nat_dist(n+d, n) = d closes the estimate
					ByArith(shiftEst.At(n_0, d_0)),
				)
			}),
		),
	)
}

// homogeneous — near-homogeneity of a slope: x(m·n) ≈ m·x(n)
// up to a defect linear in m (homogeneity, not multiplicativity
// f(m·n) = f(m)·f(n)):
//
//	⊢ ∀x:nadd. ∃B. ∀m n. nat_dist(x(m·n), m·x(n)) ≤ B·m + B
//
// (Writing dest_nadd(x, ·) as x(·) in comments.) The constant is
// B := B₀ + x(0), where B₀ is the near-linearity constant Cauchy
// supplies for x. Split on the scalar n:
//
// - n = 0: the defect collapses to nat_dist(x(0), m·x(0)), which
// nat_monus.DistAddBound bounds by x(0) + m·x(0) — no Cauchy data
// needed (lemma1).
// - n ≠ 0: scale the defect by n. The dist calculus (nat_monus.DistLeftMul
// to pull n inside, AC to align n·(m·x(n)) = (m·n)·x(n),
// nat_monus.DistSym to flip) turns n·nat_dist(x(m·n), m·x(n)) into exactly
// the dist the Cauchy bound at the pair (m·n, n) estimates
// (lemma2); the bound B₀·(m·n + n) sits under n·(B·m + B), and
// nat_order.LessEqMulCancel cancels the factor n ≠ 0.
var homogeneous = homogeneousThm{family.Add(registry.ProofEntry{
	Name: "homogeneous",
	Key:  "prop_ed89c7cca135e600",
	// The proof is three sections written as a linear script: the two lemmas
	// are Go locals the goal cites by closure capture.
	Build: family.Sections(
		"∀x:nadd. ∃B:num. ∀m n:num. dist((dest_nadd(x, m * n), m * dest_nadd(x, n))) ≤ B * m + B",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zero := ctx.Numeral(0)

			B_0 := ctx.Var("B_0", NumType)
			m_0 := ctx.Var("m_0", NumType)
			n_0 := ctx.Var("n_0", NumType)
			x_0 := ctx.Var("x_0", MakeType("nadd"))

			// x0at0 — the term x₀(0), the value of the slope at 0 (the additive
			// part of the homogeneity constant).
			x0at0 := v.at(x_0, zero)
			// witnessB — the homogeneity constant B := B₀ + x₀(0).
			witnessB := v.sum(B_0, x0at0)
			// target — the bound (B₀ + x₀(0))·m₀ + (B₀ + x₀(0)) the defect must
			// stay under.
			target := v.sum(v.mul(witnessB, m_0), witnessB)
			// defect — the homogeneity defect nat_dist(x₀(m₀·n₀), m₀·x₀(n₀)).
			defect := v.d(v.at(x_0, v.mul(m_0, n_0)), v.mul(m_0, v.at(x_0, n_0)))

			// lemma1 — the degenerate (n = 0) branch of the estimate: both
			// components of the pair are x(0)-terms, so no Cauchy data is needed.
			// nat_monus.DistAddBound bounds the dist by the sum x(0) + m·x(0), and the
			// target dominates that sum with slack B·m + B.
			lemma1 := ctx.Lemma("∀x:nadd. ∀m B:num. "+
				"    dist((dest_nadd(x, 0), m * dest_nadd(x, 0))) ≤ "+
				"    (B + dest_nadd(x, 0)) * m + (B + dest_nadd(x, 0))",
				func(a *Argument, x, m, B Term) {
					regroup := a.Have(
						"regroup the target — (B+x(0))·m + (B+x(0)) = (x(0) + m·x(0)) + (B·m + B), a ring identity",
						MakeProp(target.Eq(v.sum(
							v.sum(x0at0, v.mul(m_0, x0at0)),
							v.sum(v.mul(B_0, m_0), B_0)))),
						ByArith())
					a.Show(
						"dist ≤ x(0) + m·x(0) by DistAddBound at (x₀(0), m₀·x₀(0)); "+
							"the target exceeds that sum by the nonnegative slack B·m + B",
						ByArith(regroup, At(nat_monus.DistAddBound, x0at0, v.mul(m_0, x0at0))))
				})

			xAtMN := v.at(x_0, v.mul(m_0, n_0)) // x₀(m₀·n₀)
			xAtN := v.at(x_0, n_0)              // x₀(n₀)

			// mulAC — the ×-deriver for the file's one AC rearrangement.
			mulAC := nat_arith.MulAC(ctx)

			// lemma2 — the scaling identity: multiplying the homogeneity defect by
			// n turns it into a dist between the two terms the Cauchy bound at
			// (m·n, n) compares. nat_monus.DistLeftMul pulls the factor n inside the
			// dist; an AC rearrangement aligns n·(m·x(n)) with (m·n)·x(n);
			// nat_monus.DistSym flips the pair into the Cauchy orientation.
			lemma2 := ctx.Lemma("∀x:nadd. ∀m n:num. "+
				"    n * dist((dest_nadd(x, m * n), m * dest_nadd(x, n))) = "+
				"    dist((m * n * dest_nadd(x, n), n * dest_nadd(x, m * n)))",
				func(a *Argument, x, m, n Term) {
					a.Show(
						"chain the three equations — scale the distance through by n, "+
							"regroup n·(m·x(n)) as (mn)·x(n), then swap the two arguments",
						ByArith(
							// n·(m·x(n)) = (m·n)·x(n) — a pure AC rearrangement of ×.
							mulAC.Eq(v.mul(n_0, v.mul(m_0, xAtN)), v.mul(v.mul(m_0, n_0), xAtN)),
							// nat_monus.DistLeftMul at (n₀, x₀(m₀·n₀), m₀·x₀(n₀)):
							// nat_dist(n₀·x₀(m₀n₀), n₀·(m₀·x₀(n₀))) = n₀·nat_dist(x₀(m₀n₀), m₀·x₀(n₀)).
							At(nat_monus.DistLeftMul, n_0, xAtMN, v.mul(m_0, xAtN)),
							// nat_monus.DistSym at (n₀·x₀(m₀·n₀), (m₀·n₀)·x₀(n₀)) — the flip
							// into Cauchy orientation (larger multiple first).
							At(nat_monus.DistSym, v.mul(n_0, xAtMN), v.mul(v.mul(m_0, n_0), xAtN))))
				})

			// goal: extract x₀'s Cauchy constant B₀, witness B := B₀ + x₀(0), and
			// split on the scalar n₀: the n₀ = 0 branch is lemma1; the n₀ ≠ 0
			// branch scales by n₀ (lemma2), bounds via the Cauchy estimate at
			// (m₀·n₀, n₀), and cancels the factor n₀.
			return ctx.Theorem(headline,
				func(a *Argument, x Term) {
					// Cauchy at x₀ supplies ∃B. ∀m n. …; Unpack installs it and
					// Skolemizes the constant as B₀.
					_, cauchy := a.Unpack(At(Cauchy, x))
					a.Do(
						Witness(witnessB),
						StripQuant(), // the scalar pair: m₀, n₀
						ByCaseStep(n_0.Eq(zero),
							Case(
								"n₀ = 0 — the defect is dist(x₀(0), m₀·x₀(0)); lemma1 "+
									"at (x₀, m₀, B₀), then substitute n₀ = 0 into the goal",
								Given(func(b *Argument, nIsZero Fact) {
									b.Show(
										"lemma1's degenerate estimate, carried across n₀ = 0",
										ByArith(nIsZero, At(lemma1, x_0, m_0, B_0)))
								}),
							),
							Case(
								"n₀ ≠ 0 — scale the defect by n₀, bound it by the Cauchy estimate, cancel n₀",
								homogeneousScaleAndCancel(v, cauchy, lemma2,
									x_0, m_0, n_0, B_0, x0at0, target, defect),
							),
						),
					)
				})
		}),
})}

// homogeneousScaleAndCancel — the n₀ ≠ 0 branch:
//
//	n₀·defect = nat_dist((m₀n₀)·x₀(n₀), n₀·x₀(m₀n₀)) (lemma2)
//	 ≤ B₀·(m₀n₀ + n₀) (Cauchy at (m₀·n₀, n₀))
//	 ≤ n₀·target (ring regrouping)
//
// then nat_order.LessEqMulCancel with n₀ ≠ 0 cancels the factor n₀.
func homogeneousScaleAndCancel(v *slopeVocab, cauchy Fact, lemma2 *GoalStackNode,
	x_0, m_0, n_0, B_0, x0at0, target, defect Term) Action {
	mn := v.mul(m_0, n_0) // the composite scale m₀·n₀
	return Derive(func(a *Argument) {
		a.Have(
			"the scaled defect obeys the scaled target — Cauchy bound plus the ring regrouping below",
			MakeProp(v.le(v.mul(n_0, defect), v.mul(n_0, target))),
			Derive(func(b *Argument) {
				regroup := b.Have(
					"regroup the scaled target — n₀·target = B₀·(m₀n₀+n₀) + the "+
						"x₀(0)-slack, a ring identity exposing the Cauchy bound as a summand",
					MakeProp(v.mul(n_0, target).Eq(v.sum(
						v.mul(B_0, v.sum(mn, n_0)),
						v.sum(v.mul(x0at0, mn), v.mul(x0at0, n_0))))),
					ByArith())
				b.Show(
					"linear chain — n₀·defect ≤ B₀·(m₀n₀+n₀) ≤ n₀·target, the x₀(0)-slack being nonnegative",
					ByArith(
						regroup,
						// Cauchy bound at (m₀·n₀, n₀):
						// nat_dist((m₀n₀)·x₀(n₀), n₀·x₀(m₀n₀)) ≤ B₀·(m₀n₀ + n₀).
						cauchy.At(mn, n_0),
						// lemma2: the scaled defect IS the dist just bounded.
						At(lemma2, x_0, m_0, n_0)))
			}))
		a.Show(
			"cancel the factor n₀ — nat_order.LessEqMulCancel turns n₀·defect ≤ "+
				"n₀·target into defect ≤ target ∨ n₀ = 0, and n₀ ≠ 0 leaves the bound",
			// Drop the wide Cauchy ∀-hyp — the finish is propositional in
			// the ⇔, the scaled bound, and n₀ ≠ 0.
			Clear(cauchy),
			At(nat_order.LessEqMulCancel, n_0, defect, target).SplitIff(
				BothHold(
					"the ⇔ holds — the scaled bound selects defect ≤ target "+
						"∨ n₀ = 0, and n₀ ≠ 0 eliminates the right disjunct",
					TrivialNormalized(),
				),
				NeitherHolds(
					"¬(n₀·defect ≤ n₀·target) contradicts the scaled bound just proved",
					TrivialNormalized(),
				),
			))
	})
}

// additive — the additivity defect of a slope is uniformly
// bounded:
//
//	⊢ ∀x. ∃B. ∀m n. nat_dist(x(m+n), x(m) + x(n)) ≤ B
//
// (writing x(n) for dest_nadd(x, n)). The classical estimate: take B₀
// from the defining bound (Cauchy: nat_dist(m·x(n), n·x(m)) ≤
// B₀·(m+n)) and witness B := 3·B₀ + x(0). For m+n ≠ 0, scale the
// defect by m+n and factor:
//
//	(m+n)·nat_dist(x(m+n), x(m)+x(n))
//	 = nat_dist(m·x(m+n) + n·x(m+n), (m+n)·x(m) + (m+n)·x(n)) [nat_monus.DistLeftMul, distributivity]
//	 ≤ nat_dist(m·x(m+n), (m+n)·x(m)) + nat_dist(n·x(m+n), (m+n)·x(n)) [nat_monus.DistAdd2]
//	 ≤ B₀·(m+(m+n)) + B₀·(n+(m+n)) = (m+n)·(3·B₀) [two Cauchy instances, ring]
//
// then cancel the nonzero factor (nat_order.LessEqMulCancel). For m+n = 0 the
// defect is literally nat_dist(x(0), x(0)+x(0)) = x(0) ≤ 3·B₀ + x(0).
//
// The scaled estimate is pure dist algebra over ℕ — no slopes in it —
// and is proved once as lemma1 over opaque u = x(m+n), v = x(m),
// w = x(n); the linear chaining around the two Cauchy instances is
// absorbed by gated arith, which knows dist's monus form.
var additive = additiveThm{family.Add(registry.ProofEntry{
	Name: "additive",
	Key:  "prop_df88f552d6669f94",
	// The proof is two sections written as a linear script: `lemma1` is a Go
	// local the goal cites by closure capture.
	Build: family.Sections(
		"∀x:nadd. ∃B:num. ∀m n:num. dist((dest_nadd(x, m + n), dest_nadd(x, m) + dest_nadd(x, n))) ≤ B",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zero := ctx.Numeral(0)

			// Skolem constants as the strips mint them: m_0, n_0 the two
			// arguments, B_0 the Cauchy constant, x_0 the slope; u_0, v_0,
			// w_0 are lemma1's opaque stand-ins for x(m+n), x(m), x(n).
			B_0 := ctx.Var("B_0", NumType)
			m_0 := ctx.Var("m_0", NumType)
			n_0 := ctx.Var("n_0", NumType)
			u_0 := ctx.Var("u_0", NumType)
			v_0 := ctx.Var("v_0", NumType)
			w_0 := ctx.Var("w_0", NumType)
			x_0 := ctx.Var("x_0", MakeType("nadd"))

			// lemma1 — the core estimate, pure dist algebra over ℕ. Read
			// u = x(m+n), v = x(m), w = x(n): the antecedents are the two
			// Cauchy-bound instances at (m, m+n) and (n, m+n), the conclusion the
			// additivity defect bound. Scale the defect by m+n, factor, apply the
			// triangle inequality, sum the hypotheses, cancel the nonzero factor.
			lemma1 := ctx.Lemma("∀m n u v w B:num. "+
				"    dist((m * u, (m + n) * v)) ≤ B * (m + (m + n)) ⇒ "+
				"    (dist((n * u, (m + n) * w)) ≤ B * (n + (m + n)) ⇒ (m + n ≠ 0 ⇒ dist((u, v + w)) ≤ 3 * B))",
				func(a *Argument) {
					a.Do(
						StripQuant(),
						StripImp(), // h: nat_dist(m₀·u₀, (m₀+n₀)·v₀) ≤ B₀·(m₀+(m₀+n₀))
						StripImp(), // h: nat_dist(n₀·u₀, (m₀+n₀)·w₀) ≤ B₀·(n₀+(m₀+n₀))
						StripImp(), // h: (m₀+n₀) ≠ 0
						Derive(func(b *Argument) {
							b.Have(
								"the defect scaled by m₀+n₀ is bounded by (m₀+n₀)·(3B₀)",
								"(m₀ + n₀) * dist((u₀, v₀ + w₀)) ≤ (m₀ + n₀) * (3 * B₀)",
								additiveScaledDefectBound(v, m_0, n_0, u_0, v_0, w_0))
							b.Show(
								"cancel the factor m₀+n₀ ≠ 0 — nat_order.LessEqMulCancel's "+
									"iff turns the scaled bound into dist(u₀, v₀+w₀) ≤ 3B₀",
								Cite(nat_order.LessEqMulCancel))
						}),
					)
				})

			three := ctx.Numeral(3)

			// goal: fix x₀, take B₀ from Cauchy, witness B := 3·B₀ + x₀(0), and
			// split on whether m₀+n₀ = 0 (lemma1's cancellation needs it ≠ 0).
			return ctx.Theorem(headline,
				func(a *Argument, x Term) {
					// Cauchy at x₀; the StripQuant Skolemizes its ∃B into the
					// constant B₀, leaving x₀'s defining bound resident.
					a.Do(Cite(Cauchy, x), StripQuant())
					cauchyX := a.Hyp("∀m n:num. dist((m * dest_nadd(x₀, n), n * dest_nadd(x₀, m))) ≤ B₀ * (m + n)")
					a.Do(
						Witness(v.sum(v.mul(three, B_0), v.at(x_0, zero))),
						StripQuant(),
						ByCaseStep(v.sum(m_0, n_0).Eq(zero),
							Case(
								"degenerate case m₀+n₀ = 0 — the defect collapses to dist(x₀(0), x₀(0)+x₀(0)) = x₀(0)",
								additiveDegenerateCase(),
							),
							Case(
								"main case — two Cauchy instances feed lemma1, then pad the bound with x₀(0)",
								additiveMainCase(v, cauchyX, lemma1, m_0, n_0),
							),
						),
					)
				})
		}),
})}

// additiveScaledDefectBound: (m₀+n₀)·nat_dist(u₀, v₀+w₀) ≤ (m₀+n₀)·(3B₀),
// from the two hypothesis bounds. Factor the scaled dist into the two
// cross terms, then triangle inequality + the hypotheses.
func additiveScaledDefectBound(v *slopeVocab, m_0, n_0, u_0, v_0, w_0 Term) Action {
	return Derive(func(a *Argument) {
		crossM := a.Hyp("dist((m₀ * u₀, (m₀ + n₀) * v₀)) ≤ B₀ * (m₀ + (m₀ + n₀))")
		crossN := a.Hyp("dist((n₀ * u₀, (m₀ + n₀) * w₀)) ≤ B₀ * (n₀ + (m₀ + n₀))")
		factored := a.Have(
			"factor — nat_monus.DistLeftMul pulls m₀+n₀ inside dist, then the "+
				"two distributive laws split each component into the cross terms",
			"(m₀ + n₀) * dist((u₀, v₀ + w₀)) = dist((m₀ * u₀ + n₀ * u₀, (m₀ + n₀) * v₀ + (m₀ + n₀) * w₀))",
			Cite(nat_monus.DistLeftMul),
			Cite(nat_arith.LeftAddDistrib),
			Cite(nat_arith.RightAddDistrib))
		// Bound the factored dist.
		ring := a.Have(
			"ring identity — the two hypothesis bounds sum to exactly the scaled target",
			"(m₀ + n₀) * (3 * B₀) = B₀ * (m₀ + (m₀ + n₀)) + B₀ * (n₀ + (m₀ + n₀))",
			ByArith())
		a.Show(
			"nat_monus.DistAdd2 splits dist across the two cross-term pairs; "+
				"each summand is a hypothesis bound, and the close is linear",
			ByArith(
				factored,
				ring,
				crossM,
				crossN,
				At(
					nat_monus.DistAdd2,
					v.mul(m_0, u_0),
					v.mul(n_0, u_0),
					v.mul(v.sum(m_0, n_0), v_0),
					v.mul(v.sum(m_0, n_0), w_0))))
	})
}

// additiveDegenerateCase: m₀+n₀ = 0. Both arguments are 0, so the defect
// is nat_dist(x₀(0), x₀(0)+x₀(0)) = x₀(0) ≤ 3B₀ + x₀(0).
func additiveDegenerateCase() Action {
	return Derive(func(a *Argument) {
		zeros := a.Have(
			"a zero sum has zero summands",
			"m₀ = 0 ∧ n₀ = 0",
			ByArith(a.Hyp("m₀ + n₀ = 0")))
		a.Show(
			"substitute and collapse — dist(x₀(0), x₀(0)+x₀(0)) = x₀(0) ≤ 3B₀ + x₀(0)",
			// the zeros substituted, dist unfolds to its monus form, and
			// the monus form decides — nat_dist(a, a+a) collapses to a
			ByArith(zeros))
	})
}

// additiveMainCase: m₀+n₀ ≠ 0. Ground the Cauchy bound at (m₀, m₀+n₀)
// and (n₀, m₀+n₀) — exactly lemma1's two antecedents at u = x₀(m₀+n₀),
// v = x₀(m₀), w = x₀(n₀) — and let lemma1 deliver defect ≤ 3B₀.
func additiveMainCase(v *slopeVocab, cauchy Fact, lemma1 *GoalStackNode, m_0, n_0 Term) Action {
	sum := v.sum(m_0, n_0)
	// nonzero is the branch's own hypothesis, m₀ + n₀ ≠ 0.
	return Given(func(a *Argument, nonzero Fact) {
		defect := a.Have(
			"modus ponens — grounded lemma1 discharges against the two Cauchy instances and m₀+n₀ ≠ 0",
			"dist((dest_nadd(x₀, m₀ + n₀), dest_nadd(x₀, m₀) + dest_nadd(x₀, n₀))) ≤ 3 * B₀",
			By(cauchy.At(m_0, sum), cauchy.At(n_0, sum), nonzero, lemma1.PromisedThm()))
		a.Show(
			"pad the constant — defect ≤ 3B₀ ≤ 3B₀ + x₀(0)",
			ByArith(defect))
	})
}

// mulAlt — the alternative multiplication formula. Slope
// multiplication is COMPOSITION ((x·y)(n) = x(y(n))), and this
// estimate is why composition represents the PRODUCT of the limits:
// n·x(y(n)) ≈ x(n)·y(n) up to a linear error. Morally
// x(y(n)) ≈ x(n)/n · y(n), because y(n) sits within B₀·(n + y(n)) of
// where the defining bound of x pins it.
//
//	⊢ ∀x y : nadd. ∃A B. ∀n. nat_dist(n·x(y(n)), x(n)·y(n)) ≤ A·n + B
//
// (x(n) abbreviates dest_nadd(x, n).) Proof: fix x, y; let B₀ be the
// Cauchy constant of x and (A₀, B₁) the growth constants of y. Take
// A := B₀·(1+A₀) and B := B₀·B₁. For each n, chain two estimates:
//
//	nat_dist(n·x(y(n)), x(n)·y(n)) ≤ B₀·(n + y(n)) [Cauchy at (n, y(n))]
//	B₀·(n + y(n)) ≤ (B₀·(1+A₀))·n + B₀·B₁ [y(n) ≤ A₀·n + B₁]
//
// The file states the two pure-arithmetic ingredients as standalone
// lemmas (the ring identity behind the constants, and the monotone
// linearization), then the goal section is exactly the two estimates
// plus LessEqTrans.
var mulAlt = mulAltThm{family.Add(registry.ProofEntry{
	Name: "mulAlt",
	Key:  "prop_642e491495056af2",
	// The proof is three sections written as a linear script: the two lemmas
	// are Go locals the goal cites by closure capture.
	Build: family.Sections(
		"∀x y:nadd. ∃A B:num. ∀n:num. "+
			"    dist((n * dest_nadd(x, dest_nadd(y, n)), dest_nadd(x, n) * dest_nadd(y, n))) ≤ A * n + B",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// lemma1/lemma2 frees (minted by the strips from the binders
			// b, a, n, c, w): b is the Cauchy constant, a·n + c the linear
			// bound, w the bounded quantity (instantiated with y(n)).
			a_0 := ctx.Var("a_0", NumType)
			b_0 := ctx.Var("b_0", NumType)
			c_0 := ctx.Var("c_0", NumType)
			n_0 := ctx.Var("n_0", NumType)
			w_0 := ctx.Var("w_0", NumType)
			// goal frees: the slopes x₀, y₀ (the skolemized constants B₀ from
			// Cauchy at x₀ and (A₀, B₁) from LinearBound at y₀ arrive as the
			// goal section's Unpack values).
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			y_0 := ctx.Var("y_0", MakeType("nadd"))

			one := ctx.Numeral(1)

			// Ladder terms for lemma1 (b₀, a₀, n₀, c₀ are the stripped frees).
			bn := v.mul(b_0, n_0)
			ban := v.mul(b_0, v.mul(a_0, n_0))
			bc := v.mul(b_0, c_0)
			m1 := v.sum(v.sum(bn, ban), bc)                                      // (b·n + b·(a·n)) + b·c
			m2 := v.sum(v.mul(b_0, v.sum(n_0, v.mul(a_0, n_0))), bc)             // b·(n + a·n) + b·c
			m3 := v.sum(v.mul(b_0, v.sum(v.mul(one, n_0), v.mul(a_0, n_0))), bc) // b·(1·n + a·n) + b·c
			m4 := v.sum(v.mul(b_0, v.mul(v.sum(one, a_0), n_0)), bc)             // b·((1+a)·n) + b·c

			// lemma1 — the ring identity behind the witness constants: with
			// b := B₀ the Cauchy constant and a·n + c := A₀·n + B₁ the growth
			// bound of y, it rewrites the error bound B₀·(n + (A₀·n + B₁)) into
			// the linear form (B₀·(1+A₀))·n + B₀·B₁ whose coefficients are the
			// ∃A ∃B witnesses. Proved as a transitivity ladder, one
			// distributivity/associativity law per rung.
			lemma1 := ctx.Lemma("∀b a n c:num. b * (n + (a * n + c)) = b * (1 + a) * n + b * c",
				func(d *Argument) {
					d.Do(
						StripQuant(),
						// b·(n+(a·n+c)) = (b·n + b·(a·n)) + b·c
						// = b·(n + a·n) + b·c
						// = b·(1·n + a·n) + b·c
						// = b·((1+a)·n) + b·c
						// = (b·(1+a))·n + b·c
						//
						// Each rung installs exactly the laws its label names, so the
						// rule set is checked per leg rather than piled in front of
						// the chain.
						CalcEq(
							Leg(
								m1,
								"distribute b over the sum (nat_arith.LeftAddDistrib ×2) and reassociate (nat_arith.AddAssoc)",
								Cite(nat_arith.LeftAddDistrib),
								Cite(nat_arith.AddAssoc)),
							Leg(
								m2,
								"fold nat_arith.LeftAddDistrib back over the first two summands",
								Cite(nat_arith.LeftAddDistrib)),
							Leg(
								m3,
								"n = 1·n (nat_arith.MulClauses)",
								By(nat_arith.MulClauses)),
							Leg(
								m4,
								"fold nat_arith.RightAddDistrib",
								Cite(nat_arith.RightAddDistrib)),
							FinalLeg(
								"nat_arith.MulAssoc reassociates b·((1+a)·n) into (b·(1+a))·n",
								Cite(nat_arith.MulAssoc)),
						),
					)
				})

			// lemma2 — monotone linearization: a quantity w with linear bound
			// a·n + c makes b·(n+w) linear in n. Two cancellation laws grow the
			// bound under n + · and b · ·; lemma1 then rewrites the right-hand
			// side into the goal's shape, and the chained equivalences close the
			// goal against the antecedent (no refuter needed).
			lemma2 := ctx.Lemma(Statement{
				Binders: "∀b n w a c:num.",
				Hypotheses: []string{
					"w ≤ a * n + c",
				},
				Conclusion: "b * (n + w) ≤ b * (1 + a) * n + b * c",
			},
				func(d *Argument) {
					d.Do(
						StripQuant(),
						StripImp(),
						// w ≤ a·n+c ⇔ n+w ≤ n+(a·n+c): nat_order.LessEqAddCancel at (n, w, a·n+c).
						Cite(nat_order.LessEqAddCancel,
							n_0, w_0, v.sum(v.mul(a_0, n_0), c_0)),
						// b·(n+w) ≤ b·(n+(a·n+c)) ⇔ n+w ≤ n+(a·n+c) ∨ b = 0: nat_order.LessEqMulCancel.
						Cite(nat_order.LessEqMulCancel,
							b_0, v.sum(n_0, w_0), v.sum(n_0, v.sum(v.mul(a_0, n_0), c_0))),
						// Rewrite the goal's RHS by the ring identity; the two ⇔s reduce
						// the goal to the antecedent hypothesis and the section closes.
						Cite(lemma1),
					)
				})

			// goal: unpack the toolkit bounds (B₀ Cauchy-of-x, (A₀,B₁)
			// growth-of-y), witness A := B₀·(1+A₀), B := B₀·B₁, then chain the two
			// estimates through B₀·(n + y(n)) via LessEqTrans.
			return ctx.Theorem(headline,
				func(d *Argument, x, y Term) {
					// The defining bound of x₀: ∃B. ∀m n. nat_dist(m·x₀(n), n·x₀(m)) ≤ B·(m+n),
					// unpacked into the Cauchy constant B₀.
					B_0, cauchyX := d.Unpack(At(Cauchy, x))
					// Linear growth of y₀: ∃A B. ∀n. y₀(n) ≤ A·n + B; unpacked into A₀, B₁.
					A_0, B_1, growthY := d.Unpack2(At(LinearBound, y))

					// The point-of-use values and the three terms of the ≤-chain.
					yn := v.at(y_0, n_0) // y₀(n₀)
					xn := v.at(x_0, n_0) // x₀(n₀)
					distT := v.d(
						v.mul(n_0, v.at(x_0, yn)), // n₀·x₀(y₀(n₀))
						v.mul(xn, yn))             // x₀(n₀)·y₀(n₀)
					midT := v.mul(B_0, v.sum(n_0, yn)) // B₀·(n₀ + y₀(n₀))
					rhsT := v.sum(
						v.mul(v.mul(B_0, v.sum(one, A_0)), n_0),
						v.mul(B_0, B_1)) // (B₀·(1+A₀))·n₀ + B₀·B₁

					d.Do(
						Witness(v.mul(B_0, v.sum(one, A_0))), // A := B₀·(1+A₀)
						Witness(v.mul(B_0, B_1)),             // B := B₀·B₁
						StripQuant(),                         // fix n₀
						// The growth bound of y₀ at n₀ goes on the spine: it is what
						// lemma2's cite discharges its antecedent against.
						growthY.At(n_0),
						Derive(func(e *Argument) {
							est1 := e.Have(
								"the Cauchy bound of x₀ at (n₀, y₀(n₀)), its second "+
									"component commuted by nat_arith.MulSym into x₀(n₀)·y₀(n₀)",
								"dist((n₀ * dest_nadd(x₀, dest_nadd(y₀, n₀)), dest_nadd(x₀, n₀) * dest_nadd(y₀, n₀))) ≤ "+
									"B₀ * (n₀ + dest_nadd(y₀, n₀))",
								By(cauchyX.At(n_0, yn), At(nat_arith.MulSym, yn, xn)))
							est2 := e.Have(
								"B₀·(n₀ + y₀(n₀)) ≤ (B₀·(1+A₀))·n₀ + B₀·B₁ — lemma2 at (B₀, n₀, "+
									"y₀(n₀), A₀, B₁); its antecedent is the growth bound of y₀ at n₀",
								"B₀ * (n₀ + dest_nadd(y₀, n₀)) ≤ B₀ * (1 + A₀) * n₀ + B₀ * B₁",
								Cite(lemma2))
							e.Show(
								"dist ≤ B₀·(n₀ + y₀(n₀)) ≤ A·n₀ + B — LessEqTrans grounded at the three chain terms",
								By(est1, est2, At(nat_order.LessEqTrans, distT, midT, rhsT)))
						}),
					)
				})
		}),
})}

// ZeroIsSlope — the zero function satisfies the slope condition:
//
//	⊢ is_nadd(λn. 0)
//
// Unfolding is_nadd asks for a bound B with nat_dist(m·0, n·0) ≤ B·(m+n)
// at all m, n. Both products vanish, the self-distance nat_dist(0, 0)
// vanishes, and B := 0 closes the residual 0 ≤ 0.
//
// This is the inhabitant the type definition is stamped against
// (NaddDef's Existence, definitions.go): a type may only be carved out
// of a shape something has.
var ZeroIsSlope = zeroIsSlopeThm{family.Add(registry.ProofEntry{
	Name: "ZeroIsSlope",
	Key:  "prop_14076927afd4e286",
	// goal — unfold the slope condition, bound the zero defect by zero.
	Build: family.Theorem("is_nadd(λn:num. 0)",
		func(a *Argument) {
			ctx := a.Ctx()
			zero := ctx.Numeral(0)
			a.Do(
				// is_nadd(λn.0) unfolds to ∃B. ∀m n. nat_dist(m·0, n·0) ≤ B·(m+n).
				Unfold(IsNaddDef),
				// The defect is identically zero, so B := 0 serves.
				Witness(zero),
				StripQuant(),
				// Both cites fire as goal rewrites, so they stay bare: one
				// pass of `m * 0 = 0` folds both products at once, and
				// `0 * n = 0` folds the bound side.
				// ↦ nat_dist((0, 0)) ≤ 0
				Cite(nat_arith.MulZero),
				Cite(nat_arith.MulLeftZeroClause),
				// … and the self-distance rewrites away too. ↦ 0 ≤ 0
				Cite(nat_monus.DistRefl),
				By(nat_order.ZeroLessEq),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The growth bounds the inverse construction runs on
// ---------------------------------------------------------------------------
//
// Each is EVENTUAL (it holds past a threshold) and purely multiplicative
// (no additive constant), and they come in companion pairs:
//
// - upperBound caps every slope by B·n — LinearBound with the additive
// witness folded into the coefficient;
// - lowerBound is its opposite direction, n ≤ A·x(n) for a nonzero
// slope, and recipGrowthBound is upperBound's analogue for the
// reciprocal rinv(x,n) = ⌊n²/x(n)⌋, obtained by cancelling x(n) out
// of a lowerBound-scaled n² bound;
// - nonzero says a nonzero slope never eventually vanishes, which is
// what lets the two multiplicative cancellations above run.
//
// ArchMult is the bridge from ℕ-arithmetic into all of them: nonzero and
// lowerBound both peel off it.
//
// README: the "growth bounds" bullet.

// upperBound — every slope has a purely linear upper bound above
// some threshold:
//
//	⊢ ∀x:nadd. ∃B N. ∀n. N ≤ n ⇒ dest_nadd(x, n) ≤ B · n
//
// LinearBound already hands us an A, B such that x(n) ≤ A·n + B for
// all n; this proof folds the additive constant B into the linear
// coefficient by paying a threshold.
//
// The witnesses: B := A₀ + B₀, N := 1. The threshold hypothesis
// 1 ≤ n₀ is exactly what makes B₀ ≤ B₀·n₀, and then
//
//	x(n₀) ≤ A₀·n₀ + B₀ ≤ A₀·n₀ + B₀·n₀ = (A₀+B₀)·n₀
//
// by distributivity — nat_order.LessEqMulCancel dominates the constant,
// nat_arith.RightAddDistrib refolds the coefficient.
var upperBound = upperBoundThm{family.Add(registry.ProofEntry{
	Name: "upperBound",
	Key:  "prop_4db33667c943fddc",
	// LinearBound's affine bound A₀·n + B₀ becomes purely linear by
	// paying an N₀ := 1 threshold: with 1 ≤ n₀ assumed, B₀ is dominated
	// by B₀·n₀ and distributivity finishes the job.
	Build: family.Theorem("∀x:nadd. ∃B N:num. ∀n:num. N ≤ n ⇒ dest_nadd(x, n) ≤ B * n",
		func(a *Argument, x Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := ctx.Numeral(1)
			A_0 := ctx.Var("A_0", NumType)
			B_0 := ctx.Var("B_0", NumType)
			n_0 := ctx.Var("n_0", NumType)

			a.Do(
				// Pull in the slope's affine bound from LinearBound; skolemize
				// the coefficients A₀, B₀ out of the ∃∃.
				Cite(LinearBound, x),
				StripQuant(),
			)
			affineBound := a.Hyp("∀n:num. dest_nadd(x₀, n) ≤ A₀ * n + B₀")
			a.Do(
				// Witnesses: the linear coefficient B := A₀ + B₀ (folding the
				// constant into the multiplicative slope), threshold N := 1.
				Witness(v.sum(A_0, B_0)),
				Witness(one),
				StripQuant(),
				StripImp(), // assume the threshold: 1 ≤ n₀
			)

			threshold := a.Hyp(MakeProp(v.le(one, n_0)))
			dominated := a.Have(
				"B₀ ≤ B₀·n₀ — the constant is dominated by its multiplicative shadow when 1 ≤ n₀",
				MakeProp(v.le(B_0, v.mul(B_0, n_0))),
				// (B₀·1 ≤ B₀·n₀) ⇔ (1 ≤ n₀ ∨ B₀ = 0);
				// arith reduces B₀·1 to B₀ and closes on the 1 ≤ n₀ hyp.
				ByArith(threshold, At(nat_order.LessEqMulCancel, B_0, one, n_0)))
			a.Show(
				"linear assembly — x(n₀) ≤ A₀·n₀ + B₀ ≤ A₀·n₀ + B₀·n₀ = (A₀+B₀)·n₀",
				ByArith(
					dominated,
					// the affine bound at n₀: x(n₀) ≤ A₀·n₀ + B₀
					affineBound.At(n_0),
					// (A₀+B₀)·n₀ = A₀·n₀ + B₀·n₀ — the last piece
					At(nat_arith.RightAddDistrib, A_0, B_0, n_0)))
		}),
})}

// ArchMult — the Archimedean bound on scaling a slope:
//
//	⊢ ∀x : nadd. ∀k. x ≁ 0 ⇒ ∃N. (k ≤ N·x)
//
// (Writing dest_nadd(x, ·) as x(·) below, and reading nadd_le(a, b) as
// "a ≤ b eventually + linear shift".) For a slope not equivalent to
// zero, some scale N₀ makes N₀·x dominate the constant slope k up to
// a shift. The witness comes from x's non-equivalence with 0:
//
// - Cauchy of x supplies B₀ with nat_dist(m·x(n), n·x(m)) ≤ B₀·(m+n).
// - x ≁ 0 says the Cauchy bound at (·, 0) FAILS somewhere: for
// every threshold B, some n makes nat_dist(x(n), 0) > B. Applied at
// the threshold B₀ + k, some index n₀ has x(n₀) > B₀ + k.
//
// Take N := n₀ and B := B₀·n₀. The pointwise bound to check at each
// n₁ is k·n₁ ≤ n₀·x(n₁) + B₀·n₀. Split on n₁:
//
// - n₁ = 0: LHS = k·0 = 0, dominated trivially (nat_order.ZeroLessEq
// covers it).
// - n₁ ≠ 0: Cauchy at (n₀, n₁) gives n₁·x(n₀) ≤ n₀·x(n₁) + B₀·(n₀+n₁).
// Since x(n₀) > B₀+k, we have n₁·(B₀+k) < n₁·x(n₀) ≤ n₀·x(n₁) +
// B₀·n₀ + B₀·n₁, and cancelling B₀·n₁ leaves k·n₁ < n₀·x(n₁) +
// B₀·n₀. nat_order.LessEqMulCancel turns the n₁-scaled strict inequality
// into the target modulo the settled n₁ ≠ 0.
var ArchMult = archMultThm{family.Add(registry.ProofEntry{
	Name: "ArchMult",
	Key:  "prop_9ba7059b6aa2d321",
	// Assume x ≁ 0, then pull the Cauchy constant and a threshold-failing
	// index off the definition of nadd_eq and run the pointwise argument
	// sketched in the doc.
	// The trailing `_ Fact` absorbs the ⇒: the assumption x₀ ≁ 0 is used
	// below as a resident hypothesis (its unfolded form supplies the
	// failure witness), so the body never needs it by name.
	Build: family.Theorem(
		Statement{
			Binders: "∀x:nadd. ∀k:num.",
			Hypotheses: []string{
				"¬nadd_eq(x, nadd_of_num(0))",
			},
			Conclusion: "∃N:num. nadd_of_num(k) ≤ nadd_of_num(N) * x",
		},
		func(a *Argument, x, k Term, _ Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero := ctx.Numeral(0)

			B_0 := ctx.Var("B_0", NumType)
			n_0 := ctx.Var("n_0", NumType)
			n_1 := ctx.Var("n_1", NumType)

			// Cauchy of x₀ + its Cauchy-with-0 failure supply the
			// witnesses N₀ := n₀ and B := B₀·n₀. Every cited fact is named
			// at its use site; Cite computes each one's canonical install
			// form, which is what the specialize chain matches against.
			a.Do(archMultBody(ctx, v, k, x, B_0, n_0, n_1, zero))
		}),
})}

// archMultBody — the argument under the assumption x₀ ≁ 0.
//
// 1. Cauchy of x₀ (Skolemize ∃B as B₀; keep the ∀m∀n form under a
// handle for later grounding at (n₀, n₁)).
// 2. Unfold ¬nadd_eq to ∀B∃n ¬(…); ground at B₀+k₀, Skolemize as n₀
// — the index where the Cauchy-with-0 bound fails.
// 3. Witness N := n₀ and B := B₀·n₀ in the goal; Skolemize the free
// n₁ where the pointwise bound must hold.
// 4. Ground the morphism identities (OfNum, Mul), a Cauchy instance
// at (n₀, n₁), and dist at both distance pairs — one named handle
// per instance.
// 5. Case-split n₁ = 0 vs n₁ ≠ 0 and finish each with the appropriate
// cited fact.
func archMultBody(
	ctx *Script, v *slopeVocab,
	k_0, x_0, B_0, n_0 Term, n_1 *TermWrapper, zero Term,
) Action {
	return Derive(func(a *Argument) {
		// (1) Cauchy of x₀: install the ∀-source, ground it at x_0
		// (source kept — the Clear in (4) drops it explicitly), and
		// Skolemize the resulting ∃B as B₀.
		a.Do(Cite(Cauchy))
		cauchySrc := a.Hyp(ctx.DepNormalized(Cauchy))
		a.Do(cauchySrc.At(x_0))
		_, cauchyAtX := a.Unpack(a.Hyp(
			"∃B:num. ∀m n:num. dist((m * dest_nadd(x₀, n), n * dest_nadd(x₀, m))) ≤ B * (m + n)"))

		// (2) Unfold ¬nadd_eq in the assumption, ground at B₀+k₀,
		// Skolemize the failing index n₀.
		a.Do(Unfold(NaddEqDef))
		failSrc := a.Hyp("∀B:num. ∃n:num. ¬(dist((dest_nadd(x₀, n), dest_nadd(nadd_of_num(0), n))) ≤ B)")
		a.Do(failSrc.At(v.sum(B_0, k_0)), Clear(failSrc))
		a.Unpack(a.Hyp(
			"∃n:num. ¬(dist((dest_nadd(x₀, n), dest_nadd(nadd_of_num(0), n))) ≤ B₀ + k₀)"))

		// (3) Witness N := n₀; unfold nadd_le; witness B := B₀·n₀;
		// Skolemize the free n₁.
		a.Do(
			Witness(n_0),
			Unfold(NaddLeDef),
			Witness(v.mul(B_0, n_0)),
			StripQuant(),
		)

		// (4) Install OfNum and Mul as ∀-sources, then mint one ground
		// instance per point of use. f.At keeps the source, so the next
		// instance grounds the same ∀-hyp again.
		a.Do(Cite(OfNum), Cite(Mul))
		ofNumSrc := a.Hyp(ctx.DepNormalized(OfNum))
		mulSrc := a.Hyp(ctx.DepNormalized(Mul))
		a.Do(
			ofNumSrc.At(k_0, n_1),
			ofNumSrc.At(zero, n_0),
			ofNumSrc.At(n_0, v.at(x_0, n_1)),
			mulSrc.At(n_1, v.NaddOfNum.Apply(n_0), x_0),
			cauchyAtX.At(n_0, n_1),
		)
		ofNumKN := a.Hyp("k₀ * n₁ = dest_nadd(nadd_of_num(k₀), n₁)")
		ofNumZN := a.Hyp("0 * n₀ = dest_nadd(nadd_of_num(0), n₀)")
		ofNumN0X := a.Hyp("n₀ * dest_nadd(x₀, n₁) = dest_nadd(nadd_of_num(n₀), dest_nadd(x₀, n₁))")
		mulN0X := a.Hyp(
			"dest_nadd(nadd_of_num(n₀), dest_nadd(x₀, n₁)) = dest_nadd(nadd_of_num(n₀) * x₀, n₁)")
		cauchyN0N1 := a.Hyp("dist((n₀ * dest_nadd(x₀, n₁), n₁ * dest_nadd(x₀, n₀))) ≤ B₀ * (n₀ + n₁)")
		a.Do(Clear(cauchySrc, ofNumSrc, mulSrc, cauchyAtX))

		// The dist expansions for the two distance pairs (Cauchy's pair
		// and the failure's pair).
		a.Do(Cite(nat_monus.Dist))
		distSrc := a.Hyp(ctx.DepNormalized(nat_monus.Dist))
		a.Do(
			distSrc.At(v.mul(n_0, v.at(x_0, n_1)), v.mul(n_1, v.at(x_0, n_0))),
			distSrc.At(v.at(x_0, n_0), v.at(v.NaddOfNum.Apply(zero), n_0)),
		)
		distCauchyEq := a.Hyp("dist((n₀ * dest_nadd(x₀, n₁), n₁ * dest_nadd(x₀, n₀))) = " +
			"(n₀ * dest_nadd(x₀, n₁) - n₁ * dest_nadd(x₀, n₀)) + " +
			"(n₁ * dest_nadd(x₀, n₀) - n₀ * dest_nadd(x₀, n₁))")
		distFailEq := a.Hyp("dist((dest_nadd(x₀, n₀), dest_nadd(nadd_of_num(0), n₀))) = " +
			"(dest_nadd(x₀, n₀) - dest_nadd(nadd_of_num(0), n₀)) + " +
			"(dest_nadd(nadd_of_num(0), n₀) - dest_nadd(x₀, n₀))")
		a.Do(Clear(distSrc))

		// (5) Case-split on n₁ = 0.
		a.Do(ByCaseStep(n_1.Eq(zero),
			Case(
				"n₁ = 0: LHS = k₀·0 = 0; nat_order.ZeroLessEq dominates 0 ≤ anything",
				archMultZeroLeg(ctx),
			),
			Case(
				"n₁ ≠ 0: Cauchy(n₀, n₁) + nat_order.LessEqMulCancel(n₁) transport x(n₀) > B₀+k₀ to the goal",
				archMultCancelLeg(ctx, v, k_0, n_0, n_1, B_0, x_0, zero,
					cauchyN0N1, distCauchyEq, distFailEq,
					ofNumKN, ofNumZN, ofNumN0X, mulN0X),
			),
		))
	})
}

// archMultZeroLeg — the n₁ = 0 branch: rewrite the goal by n₁=0 so
// the LHS folds to k₀·0=0, and nat_order.ZeroLessEq covers 0 ≤ RHS.
func archMultZeroLeg(ctx *Script) Action {
	// nEqZero is the branch's own hypothesis, n₁ = 0.
	return Given(func(a *Argument, nEqZero Fact) {
		a.Do(nEqZero.Rw())
		kAt0IsZero := a.Have(
			"dest_nadd(nadd_of_num(k₀), 0) = 0 — OfNum + k₀·0 = 0",
			ctx.MakePropText("dest_nadd(nadd_of_num(k₀), 0) = 0"),
			ByArith(a.Hyp("k₀ * 0 = dest_nadd(nadd_of_num(k₀), 0)")))
		a.Do(kAt0IsZero.Rw())
		a.Show(
			"nat_order.ZeroLessEq closes 0 ≤ dest_nadd(nadd_of_num(n₀) * x₀, 0) + B₀·n₀",
			Cite(nat_order.ZeroLessEq))
	})
}

// archMultCancelLeg — the n₁ ≠ 0 branch (the analytic core).
//
// Strategy: by_contra turns the pointwise goal `k₀·n₁ ≤ n₀·x(n₁) +
// B₀·n₀` into its negation as a fresh hyp. Then the whole context is
// contradictory:
//
// - The failure witness gives B₀+k₀ < x(n₀), after the dist expansion
// and 0·n₀ = 0 reduce nat_dist(x(n₀), 0·n₀) to x(n₀).
// - The negated goal + Cauchy bound + ring identities cascade the
// contradiction; nat_order.NotLessEq + nat_order.LessEqMulCancel
// bridge each strict/⇔ step, and arith takes the final linear
// combination.
func archMultCancelLeg(
	ctx *Script, v *slopeVocab,
	k_0, n_0, n_1, B_0, x_0, zero Term,
	cauchyN0N1, distCauchyEq, distFailEq,
	ofNumKN, ofNumZN, ofNumN0X, mulN0X Fact,
) Action {
	return Derive(func(a *Argument) {
		// The ℕ-multiplication AC deriver: the closer's two operand
		// commutations are one self-proving `ac` premise each, written
		// once as their endpoints in the closing list.
		mulAC := nat_arith.MulAC(ctx)

		// by_contra: negate the pointwise goal to a hyp; goal is now ⊥.
		negGoal := a.SupposeNot() // ¬(k₀·n₁ ≤ n₀·x(n₁) + B₀·n₀)

		// Cauchy → monus → additive form.
		monusForm := a.Have(
			"monus form of Cauchy: (n₁·x(n₀)) − (n₀·x(n₁)) ≤ B₀·(n₀+n₁)",
			ctx.MakePropText("n₁ * dest_nadd(x₀, n₀) - n₀ * dest_nadd(x₀, n₁) ≤ B₀ * (n₀ + n₁)"),
			ByArith(cauchyN0N1, distCauchyEq))
		addForm := a.Have(
			"additive form: n₁·x(n₀) ≤ n₀·x(n₁) + B₀·(n₀+n₁)",
			MakeProp(v.le(
				v.mul(n_1, v.at(x_0, n_0)),
				v.sum(v.mul(n_0, v.at(x_0, n_1)), v.mul(B_0, v.sum(n_0, n_1))))),
			ByArith(monusForm))

		// The two distributivity identities the arith closer needs to
		// bridge nonlinear atoms. (Their commutative companions are AC
		// rearrangements and ride along in the closing list below.)
		distBN := a.Have(
			"distributivity B₀·(n₀+n₁) = B₀·n₀ + B₀·n₁",
			ctx.MakePropText("B₀ * (n₀ + n₁) = B₀ * n₀ + B₀ * n₁"),
			ByArith())
		distNB := a.Have(
			"distributivity n₁·(B₀+k₀) = n₁·B₀ + n₁·k₀",
			ctx.MakePropText("n₁ * (B₀ + k₀) = n₁ * B₀ + n₁ * k₀"),
			ByArith())

		// Convert the failure witness to its arithmetic content up-front,
		// so the arith closer sees B₀+k₀ < x(n₀) directly without having
		// to route through the dist expansion inside a negated hyp (the
		// destructive-partial-expansion pattern the brief warned about).
		// nat_dist(x(n₀), 0·n₀) collapses to x(n₀) — first spell that
		// collapse as its own eq, then nat_order.NotLessEq turns the
		// negated failure hyp into the strict pointwise form.
		a.Have(
			"dist(x(n₀), 0·n₀) = x(n₀) — both monus differences vanish (0·n₀ = 0)",
			MakeProp(v.d(v.at(x_0, n_0), v.mul(zero, n_0)).Eq(v.at(x_0, n_0))),
			ByArith(ofNumZN, distFailEq))
		strict := a.Have(
			"failure witness pointwise: B₀+k₀ < x(n₀)",
			MakeProp(v.LtOp.Apply(v.sum(B_0, k_0), v.at(x_0, n_0))),
			Cite(nat_order.NotLessEq))

		// Scale the strict bound by n₁ ≠ 0. nat_order.LessEqMulCancel:
		// (n₁·x(n₀) ≤ n₁·(B₀+k₀)) ⇔ (n₁ = 0 ∨ x(n₀) ≤ B₀+k₀), whose right
		// side fails at both disjuncts; nat_order.NotLessEq reads each
		// failed ≤ as the reversed <.
		scaledStrict := a.Have(
			"scaled strict: n₁·(B₀+k₀) < n₁·x(n₀)",
			MakeProp(v.LtOp.Apply(v.mul(n_1, v.sum(B_0, k_0)), v.mul(n_1, v.at(x_0, n_0)))),
			ByArith(
				strict,
				a.Hyp("n₁ ≠ 0"),
				At(nat_order.LessEqMulCancel, n_1, v.at(x_0, n_0), v.sum(B_0, k_0)),
				At(nat_order.NotLessEq, v.mul(n_1, v.at(x_0, n_0)), v.mul(n_1, v.sum(B_0, k_0)))))

		a.Show(
			"close: from n₁·(B₀+k₀) < n₁·x(n₀) chained with the additive Cauchy "+
				"bound and the ring identities, arith gets k₀·n₁ ≤ n₀·x(n₁) + B₀·n₀",
			ByArith(
				negGoal,
				addForm,
				distBN,
				distNB,
				// the two operand commutations n₁·B₀ = B₀·n₁, n₁·k₀ = k₀·n₁
				mulAC.Eq(v.mul(n_1, B_0), v.mul(B_0, n_1)),
				mulAC.Eq(v.mul(n_1, k_0), v.mul(k_0, n_1)),
				scaledStrict,
				ofNumKN,
				ofNumN0X,
				mulN0X))
	})
}

// nonzero — a nonzero slope has an eventually-nonzero underlying
// function:
//
//	⊢ ∀x : nadd. ¬nadd_eq(x, nadd_of_num(0))
//	 ⇒ ∃N. ∀n. N ≤ n ⇒ dest_nadd(x, n) ≠ 0
//
// Some N₀ separates x from 0 in the sense that beyond N₀ the
// underlying function never vanishes. The witness comes from ArchMult
// applied at k := 1: since x ≢ 0, some scale N₀ makes N₀·x dominate
// the constant slope 1 up to a shift B₀, meaning n ≤ N₀·x(n) + B₀ at
// every n. If x(n₀) = 0 that forces n₀ ≤ B₀, so N := B₀ + 1 witnesses
// eventual nonvanishing — beyond it the shift can't cover the excess
// and x(n) must be nonzero. Everything past that step is
// ℕ-arithmetic; the arithmetic closer decides both legs of the
// contradiction.
var nonzero = nonzeroThm{family.Add(registry.ProofEntry{
	Name: "nonzero",
	Key:  "prop_cca8e131f591e4cb",
	// Assume x ≢ 0, then read the witness off ArchMult and the pointwise
	// bound it supplies. Only the ∀x binds at the boundary: the
	// ⇒-antecedent stays a tracked hypothesis (`notZero`) because it is
	// Cleared once it has killed ArchMult's degenerate disjunct.
	Build: family.Theorem(Statement{
		Binders: "∀x:nadd.",
		Hypotheses: []string{
			"¬nadd_eq(x, nadd_of_num(0))",
		},
		Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ dest_nadd(x, n) ≠ 0",
	},
		func(a *Argument, x Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := ctx.Numeral(1) // both the ArchMult scale factor and the witness slack

			N_0 := ctx.Var("N_0", NumType) // the scale ArchMult supplies
			B_0 := ctx.Var("B_0", NumType) // the shift the pointwise bound supplies
			n_0 := ctx.Var("n_0", NumType) // an arbitrary index for the witness check

			notZero := a.Assume() // assume x₀ ≢ 0

			a.Do(
				// ArchMult at (x₀, 1), its x₀ ≢ 0 guard discharged from the
				// assumption: ∃N. 1 ≤ N·x₀.
				Cite(ArchMult, x, one),
				StripQuant(), // Skolemize the scale as N₀
				// The assumption has done its work.
				Clear(notZero),
				// (1 ≤ N₀·x₀) unfolds to ∃B. ∀n. 1(n) ≤ (N₀·x₀)(n) + B.
				Unfold(NaddLeDef),
			)
			// Skolemize the shift as B₀.
			_, pointwiseBound := a.Unpack(a.Hyp(
				"∃B:num. ∀n:num. dest_nadd(nadd_of_num(1), n) ≤ dest_nadd(nadd_of_num(N₀) * x₀, n) + B"))

			a.Do(
				// Witness: N := B₀ + 1. Beyond that, the shift can't
				// absorb the extra unit if x₀(n) vanished.
				Witness(v.sum(B_0, one)),
				StripQuant(), // fix the arbitrary index n₀ of the witness check
				StripImp(),   // assume the index is beyond the witness: B₀ + 1 ≤ n₀
			)
			// The residual is a pure ℕ estimate, and its pivot is the
			// collapsed bound: where x₀ vanishes, the shift alone has
			// to cover the index.
			pivot := a.Have(
				"n₀ ≤ B₀ whenever x₀ vanishes at n₀ — the pointwise bound with x₀(n₀) = 0 substituted",
				ctx.MakePropText("dest_nadd(x₀, n₀) = 0 ⇒ n₀ ≤ B₀"),
				ByArith(
					// the ∀-bound at n₀
					pointwiseBound.At(n_0),
					// The pointwise values: nadd_of_num(k) at n is k·n
					// (OfNum), and nadd_mul(x, y) at n composes the two
					// underlying functions (Mul). Composed at
					// (nadd_of_num(N₀), x₀, n₀) they collapse
					// dest(N₀·x₀, n₀) to N₀·x₀(n₀), and at (1, n₀) they
					// collapse dest(nadd_of_num(1), n₀) to n₀.
					At(OfNum, one, n_0),
					At(Mul, n_0, v.NaddOfNum.Apply(N_0), x),
					At(OfNum, N_0, v.at(x, n_0))))
			a.Show(
				"beyond the witness B₀ + 1 that pivot is contradictory, so x₀(n₀) ≠ 0",
				ByArith(pivot, a.Hyp(MakeProp(v.le(v.sum(B_0, one), n_0)))))
		}),
})}

// lowerBound — every nonzero slope has a purely linear LOWER bound
// above some threshold:
//
//	⊢ ∀x:nadd. ¬nadd_eq(x, nadd_of_num(0))
//	 ⇒ ∃A N. ∀n. N ≤ n ⇒ n ≤ A·dest_nadd(x, n)
//
// A nonzero slope grows fast enough that some pair (A, N) makes
// n ≤ A·x(n) hold at every index past N. The witnesses come from two
// facts:
// ArchMult at scale 1 supplies constants N₁, B with
//
//	∀n. n ≤ N₁·x(n) + B (*)
//
// after unfolding nadd_le and folding dest_nadd through Mul + OfNum
// (dest_nadd(nadd_mul(a,b), n) = a(b(n)) and dest_nadd(nadd_of_num(k),
// n) = k·n). nonzero supplies the threshold N₀ past which x(n) is
// nonzero (so x(n) ≥ 1). Above the threshold, that unit lower bound
// on x(n) lets the additive constant fold into the coefficient:
//
//	B ≤ B·x(n) (†)
//
// by nat_order.LessEqMulCancel — B·1 ≤ B·x(n) ⇔ 1 ≤ x(n) ∨ B = 0. Combining
// (*), (†) and nat_arith.RightAddDistrib:
//
//	n ≤ N₁·x(n) + B ≤ N₁·x(n) + B·x(n) = (N₁+B)·x(n)
//
// so A := N₁ + B, N := N₀ witnesses the bound.
var lowerBound = lowerBoundThm{family.Add(registry.ProofEntry{
	Name: "lowerBound",
	Key:  "prop_31c1ec11ca5cf0da",
	// Linear spine: nonzero and ArchMult supply the threshold N₀ and
	// scale N₁ (their degenerate nadd_eq disjuncts are dismissed against
	// the assumption x₀ ≁ 0); witness A := N₁ + B₀, N := N₀; the
	// pointwise leaf folds the additive slack into the coefficient via
	// nat_order.LessEqMulCancel + nat_arith.RightAddDistrib. The trailing
	// Fact is the ⇒'s assumption x₀ ≁ 0, listed with ArchMult's instance
	// for its guard.
	Build: family.Theorem(Statement{
		Binders: "∀x:nadd.",
		Hypotheses: []string{
			"¬nadd_eq(x, nadd_of_num(0))",
		},
		Conclusion: "∃A N:num. ∀n:num. N ≤ n ⇒ n ≤ A * dest_nadd(x, n)",
	},
		func(a *Argument, x Term, xNotZero Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := ctx.Numeral(1) // the ArchMult scale factor

			N_0 := ctx.Var("N_0", NumType) // the nonvanishing threshold from nonzero
			N_1 := ctx.Var("N_1", NumType) // the multiplicative scale from ArchMult
			B_0 := ctx.Var("B_0", NumType) // the additive slack from nadd_le's unfolding
			n_0 := ctx.Var("n_0", NumType) // an arbitrary index for the witness check

			a.Do(
				// nonzero at x₀: ∃N. ∀n. (¬(N ≤ n) ∨ x(n) ≠ 0) ∨ x ≡ 0.
				// Skolemize N₀ before def_expand touches its ∀-body — the
				// ∨ nadd_eq disjunct simplifies away against the
				// assumption when nadd_le is unfolded below.
				CiteKeep(nonzero, x),
				StripQuant(), // Skolemize the threshold as N₀
			)

			// ArchMult at (x₀, 1), its x₀ ≢ 0 guard discharged from the
			// assumption: ∃N. 1 ≤ N·x₀. Unpack Skolemizes the scale as N₁.
			_, _ = a.Unpack(GroupPremises(xNotZero, At(ArchMult, x, one)))

			a.Do(
				// (1 ≤ N₁·x₀) unfolds to ∃B. ∀n. 1(n) ≤ (N₁·x₀)(n) + B;
				// Skolemize the slack as B₀.
				Unfold(NaddLeDef),
				StripQuant(),
			)
			// nadd_le's pointwise unfold, now Skolemized at B₀.
			archBound := a.Hyp("∀n:num. dest_nadd(nadd_of_num(1), n) ≤ dest_nadd(nadd_of_num(N₁) * x₀, n) + B₀")

			// Witnesses: A := N₁ + B₀ (folded coefficient), N := N₀
			// (nonzero's threshold). Above N₀ the unit lower bound on
			// x₀(n₀) makes B₀ ≤ B₀·x₀(n₀), letting the additive slack
			// fold into the coefficient.
			a.Take(v.sum(N_1, B_0))
			a.Take(N_0)
			a.Fix()            // fix an arbitrary index n₀
			past := a.Assume() // it is past the threshold: N₀ ≤ n₀

			// nonzero's ∀-hyp, its x₀ ≢ 0 guard already discharged from
			// the assumption. Ground at n₀ — the assumed N₀ ≤ n₀ discharges
			// the threshold guard as well, leaving the nonvanishing
			// x(n₀) ≠ 0 resident — and drop the spent ∀-source.
			nonvanish := a.Hyp("∀n:num. N₀ ≤ n ⇒ dest_nadd(x₀, n) ≠ 0")
			a.Do(GroupPremises(past, nonvanish.At(n_0)), Clear(nonvanish))
			nonvanishAt := a.Hyp("dest_nadd(x₀, n₀) ≠ 0")

			// x(n₀) ≠ 0 — fold the additive slack into the coefficient.
			folded := a.Have(
				"B₀ ≤ B₀·x(n₀) — nat_order.LessEqMulCancel folds the "+
					"unit lower bound on x(n₀) into a multiplicative one",
				MakeProp(v.le(B_0, v.mul(B_0, v.at(x, n_0)))),
				ByArith(nonvanishAt, At(nat_order.LessEqMulCancel, B_0, one, v.at(x, n_0))))
			arch := a.Have(
				"n₀ ≤ N₁·x(n₀) + B₀ — the folded ArchMult bound, reading dest_nadd "+
					"through Mul + OfNum at (n₀, N₁·x₀) and (1, n₀) and (N₁, x(n₀))",
				MakeProp(v.le(n_0, v.sum(v.mul(N_1, v.at(x, n_0)), B_0))),
				ByArith(
					archBound.At(n_0),
					// Collapse dest_nadd(nadd_of_num(1), n₀) to 1·n₀ = n₀.
					At(OfNum, one, n_0),
					// Compose dest_nadd((nadd_of_num(N₁) * x₀), n₀)
					// to dest_nadd(nadd_of_num(N₁), x(n₀)) then to N₁·x(n₀).
					At(Mul, n_0, v.NaddOfNum.Apply(N_1), x),
					At(OfNum, N_1, v.at(x, n_0))))
			distrib := a.Have(
				"(N₁+B₀)·x(n₀) = N₁·x(n₀) + B₀·x(n₀) — distributivity in ring form",
				MakeProp(
					v.mul(v.sum(N_1, B_0), v.at(x, n_0)).Eq(v.sum(v.mul(N_1, v.at(x, n_0)), v.mul(B_0, v.at(x, n_0))))),
				Cite(nat_arith.RightAddDistrib))
			a.Show(
				"linear assembly — n₀ ≤ N₁·x(n₀) + B₀ ≤ N₁·x(n₀) + B₀·x(n₀) = (N₁+B₀)·x(n₀)",
				ByArith(folded, arch, distrib))
		}),
})}

// recipGrowthBound — for a slope x that is not the zero slope, the
// reciprocal function rinv(x, n) = ⌊n² / x(n)⌋ has a purely linear
// upper bound, with an additive slack B.
//
// The coefficient A is read off lowerBound directly. If A₀, N₀ are
// lowerBound's witnesses (i.e. n ≤ A₀·x(n) beyond N₀), then A := A₀
// with an eventual-slack B is enough. nat_order.BoundsIgnore trades the
// eventuality (suc(N₀) as the threshold) for a globally-bounded
// statement.
//
// The eventual step (suc(N₀) ≤ i₀) is the analytical core:
//
// 1. If x(i₀) = 0 then nat_div(_, 0) = 0 by ℕ convention, so
// rinv(x, i₀) = 0 ≤ A₀·i₀ + 0.
//
// 2. Otherwise, nat_div_mod.Division gives i₀² = nat_div·x(i₀) + nat_mod with
// nat_mod ≥ 0; hence nat_div·x(i₀) ≤ i₀². Scaling the lowerBound instance
// i₀ ≤ A₀·x(i₀) by i₀ (nat_order.LessEqMulRightCancel)
// gives i₀² ≤ (A₀·i₀)·x(i₀). Chaining, nat_div·x(i₀) ≤ (A₀·i₀)·x(i₀);
// a second right-cancel removes the common factor x(i₀) ≠ 0 to
// deliver rinv(x, i₀) = nat_div(i₀², x(i₀)) ≤ A₀·i₀.
var recipGrowthBound = recipGrowthBoundThm{family.Add(registry.ProofEntry{
	Name: "recipGrowthBound",
	Key:  "prop_d77d02114056f6e0",
	// The argument is a linear spine of side-case dismissals: assume
	// x₀ ≁ 0; A := A₀ (lowerBound's coefficient); by nat_order.BoundsIgnore it
	// suffices to bound eventually; fix i₀ past the threshold suc(N₀); if
	// x(i₀) = 0 the ℕ division convention closes; the surviving pointwise
	// leaf is the analytical core nat_div(i₀², x(i₀)) ≤ A₀·i₀ via nat_div_mod.Division +
	// the ≤ right-cancel (×2). The trailing `_ Fact` absorbs the ⇒:
	// x₀ ≁ 0 collapses lowerBound's zero-slope disjunct as a resident
	// hypothesis, so the body never needs it by name.
	Build: family.Theorem(
		Statement{
			Binders: "∀x:nadd.",
			Hypotheses: []string{
				"¬nadd_eq(x, nadd_of_num(0))",
			},
			Conclusion: "∃A B:num. ∀n:num. nadd_rinv(x, n) ≤ A * n + B",
		},
		func(a *Argument, x Term, xNotZero Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			// nat_div appears after unfolding nadd_rinv; nat_mod is introduced by
			// nat_div_mod.Division's post-cite disjunction. Both need declaring so
			// the text-DSL claims below parse.
			DIV := ctx.Const("nat_div", MakeFun(NumType, MakeFun(NumType, NumType)))
			ctx.Const("nat_mod", MakeFun(NumType, MakeFun(NumType, NumType)))

			zero := ctx.Numeral(0)

			A_0 := ctx.Var("A_0", NumType) // lowerBound's linear coefficient
			N_0 := ctx.Var("N_0", NumType) // lowerBound's threshold
			i_0 := ctx.Var("i_0", NumType) // arbitrary pointwise index in the eventual RHS
			n := ctx.Var("n", NumType)     // λ-binder for nat_order.BoundsIgnore's (P, Q) arguments

			// Named subterms — the estimate reads by structure.
			xi := v.at(x, i_0)                 // x(i₀)
			iSq := v.mul(i_0, i_0)             // i₀²
			divAt := DIV.Apply(iSq, xi)        // nat_div(i₀², x(i₀)) = nadd_rinv(x_0, i_0) after def_expand
			aiXi := v.mul(v.mul(A_0, i_0), xi) // (A₀·i₀)·x(i₀) — the coefficient's scaled shadow
			witnessN := v.Suc.Apply(N_0)       // suc(N₀) — the eventual-bound threshold

			// biIff keeps a *HypHandle. nat_order.BoundsIgnore is higher-order,
			// so citing it at two λ-arguments lands a ⇔ whose P(i)/Q(i)
			// occurrences are un-β-reduced applications
			// ((λn.nadd_rinv(x₀,n))(i) ≤ (λn.A₀*n)(i) + B, twice over): the
			// hyp IS content-addressable, but only by a text that
			// transcribes the redexes, which is the machine-shaped
			// restatement a.Hyp exists to avoid. Its one use is the Clear
			// below.
			biIff := NewHypHandle("biIff") // nat_order.BoundsIgnore specialized to (λn.rinv(x_0,n), λn.A_0·n)

			// lowerBound at x_0: ∃A ∃N. ∀n. (¬(N ≤ n) ∨ n ≤ A·x(n)) ∨ x_0 ~ 0;
			// Unpack2 installs it and Skolemizes (A_0, N_0).
			_, _, lbBody := a.Unpack2(GroupPremises(xNotZero, At(lowerBound, x)))

			a.Take(A_0) // The reciprocal's linear coefficient.

			a.Do(
				// nat_order.BoundsIgnore at (λn. rinv(x_0, n), λn. A_0·n): the goal
				// (∃B ∀i. rinv ≤ A_0·i + B) reduces to the eventually-bounded
				// form (∃B ∃N ∀i. ¬(N ≤ i) ∨ rinv ≤ A_0·i + B).
				biIff.From(Cite(nat_order.BoundsIgnore,
					n.To(v.NaddRinv.Apply(x, n)),
					n.To(v.mul(A_0, n)))),

				Suffices(ctx.MakePropText("∃B N:num. ∀i:num. ¬(N ≤ i) ∨ nadd_rinv(x₀, i) ≤ A₀ * i + B"),
					"nat_order.BoundsIgnore ⇐ upgrades the eventually-bounded form to the globally-bounded goal",
					Basic()),
			)

			// Eventually, rinv(x_0, i) ≤ A_0·i — witness B := 0, N := suc(N_0).
			a.Take(zero)
			a.Take(witnessN)
			a.Fix() // fix the arbitrary index i_0

			a.Do(
				Assuming(
					v.le(witnessN, i_0),
					"below threshold: ¬(suc(N_0) ≤ i_0) is the goal's left disjunct — direct",
					TrivialNormalized()),

				// Above threshold: unfold rinv → nat_div, ground lowerBound at i_0.
				Clear(biIff),        // ⇔ spent — its role was structuring the suffices bridge
				lbBody.At(i_0),      // the x_0 ~ 0 disjunct collapses against the section's ¬nadd_eq
				Clear(lbBody),       // wide ∀-hyp done its work
				Unfold(naddRinvDef), // rinv(x_0, i_0) → nat_div(i_0², x(i_0))
			)

			// The bound at i_0 waits on its threshold guard; suc(N_0) ≤ i_0
			// is one past it — SucLessEqIffLessThan reads that hypothesis as
			// N_0 < i_0, LessEqOfLessThan weakens it — and the guarded fact
			// then applies.
			lbAt := a.Hyp("N₀ ≤ i₀ ⇒ i₀ ≤ A₀ * dest_nadd(x₀, i₀)")
			aboveThreshold := a.Have(
				"N_0 ≤ i_0, one below the assumed suc(N_0) ≤ i_0",
				MakeProp(v.le(N_0, i_0)),
				By(
					a.Hyp("suc(N₀) ≤ i₀"),
					At(nat_order.SucLessEqIffLessThan, N_0, i_0),
					At(nat_order.LessEqOfLessThan, N_0, i_0)))
			lower := a.Have(
				"so the lower bound holds at i_0",
				MakeProp(v.le(i_0, v.mul(A_0, xi))),
				By(lbAt, aboveThreshold))

			a.Do(
				// split on x(i_0) = 0.
				Unless(
					xi.Eq(zero),
					"x(i_0) = 0: div(_, 0) = 0 by ℕ convention closes nat_div ≤ A_0·i_0 + 0",
					ByArith(ResidentHyp(MakeProp(xi.Eq(zero))))),
			)
			// x(i_0) ≠ 0 — the analytical core.
			divisorNonzero := a.Hyp(xi.Neq(zero))

			// The ≤-chain nat_div·x(i_0) ≤ i_0² ≤ (A_0·i_0)·x(i_0).
			chained := a.Calc(CalcRel{
				Rel:   v.rel(v.LeOp),
				Trans: nat_order.LessEqTrans,
			}, v.mul(divAt, xi),
				// From the nat_div_mod.Division identity + nat_mod ≥ 0 in ℕ.
				// nat_div_mod.Division at (i_0², x(i_0)): (x(i_0) = 0) ∨
				// (nat_mod(i_0², x(i_0)) < x(i_0) ∧ i_0² = nat_div·x(i_0) + nat_mod(i_0², x(i_0))).
				// The x(i_0) = 0 alternative collapses on this branch.
				Leg(
					iSq,
					"div(i_0², x(i_0))·x(i_0) ≤ i_0² — the gated arith close reads nat_div_mod.Division",
					ByArith(At(nat_div_mod.Division, iSq, xi), divisorNonzero)),
				// Scale i_0 ≤ A_0·x(i_0) by i_0 via the ≤ right-cancel; the
				// closer reads (A_0·x(i_0))·i_0 and (A_0·i_0)·x(i_0) as one
				// product of the same three factors.
				Leg(
					aiXi,
					"i_0² ≤ (A_0·i_0)·x(i_0) — LessEqMulRightCancel scales i_0 ≤ A_0·x(i_0) by i_0",
					ByArith(
						lower,
						// (m, n, p): i₀·i₀ ≤ (A₀·x(i₀))·i₀ ⇔ i₀ ≤ A₀·x(i₀) ∨ i₀ = 0
						At(nat_order.LessEqMulRightCancel, i_0, v.mul(A_0, xi), i_0))),
			)

			// Cancel x(i_0) ≠ 0 from nat_div·x(i_0) ≤ (A_0·i_0)·x(i_0) — right-cancel again.
			a.Show(
				"div(i_0², x(i_0)) ≤ A_0·i_0 — LessEqMulRightCancel cancels "+
					"x(i_0) from the chained fact nat_div·x(i_0) ≤ (A_0·i_0)·x(i_0)",
				ByArith(
					chained,
					divisorNonzero,
					// (m, n, p): nat_div·x(i₀) ≤ (A₀·i₀)·x(i₀) ⇔ nat_div ≤ A₀·i₀ ∨ x(i₀) = 0
					At(nat_order.LessEqMulRightCancel, divAt, v.mul(A_0, i_0), xi)))
		}),
})}

// ---------------------------------------------------------------------------
// Slope equivalence (`nadd_eq`
// ---------------------------------------------------------------------------
//
// slope equivalence (`nadd_eq`: a bounded pointwise defect) is an
// equivalence relation. Every welldef theorem in this chapter, and every
// transport in the two layers above it, is stated against these three.

// NaddEqRefl — slope equivalence is reflexive:
//
//	⊢ ∀x : nadd. nadd_eq(x, x)
//
// nadd_eq(x, y) asks for one bound B with
// nat_dist(dest_nadd(x, n), dest_nadd(y, n)) ≤ B for every n. Against
// itself the defect is the distance between equal numbers, which is
// zero (nat_monus.DistRefl) — so B := 0 serves, and the bound to check is
// just 0 ≤ 0 (an instance of nat_order.ZeroLessEq).
var NaddEqRefl = naddEqReflThm{family.Add(registry.ProofEntry{
	Name: "NaddEqRefl",
	Key:  "prop_f8e3b138ea4e6601",
	// goal — unfold the equivalence, then bound the self-defect by zero.
	Build: family.Theorem("∀x:nadd. nadd_eq(x, x)",
		func(a *Argument, x Term) {
			ctx := a.Ctx()
			a.Do(
				// x₀ ~ x₀ unfolds to
				// ∃B. ∀n. nat_dist(dest_nadd(x₀, n), dest_nadd(x₀, n)) ≤ B.
				Unfold(NaddEqDef),
				// The self-defect is identically zero, so B := 0 bounds it.
				Witness(ctx.Numeral(0)),
				StripQuant(),
				// The defect vanishes: nat_dist(dest_nadd(x₀, n₀), dest_nadd(x₀, n₀))
				// rewrites to 0 …
				Cite(nat_monus.DistRefl),
				// … and 0 ≤ 0 closes the bound.
				Cite(nat_order.ZeroLessEq),
			)
		}),
})}

// NaddEqSym — slope equivalence is symmetric:
//
//	⊢ ∀x y : nadd. nadd_eq(x, y) ⇔ nadd_eq(y, x)
//
// Both sides unfold to bounded-defect statements that differ only in
// the order of the two arguments of dist: a bound B on
// nat_dist(dest_nadd(x, n), dest_nadd(y, n)) versus the same bound on
// nat_dist(dest_nadd(y, n), dest_nadd(x, n)). By the symmetry of dist
// (nat_monus.DistSym) the two defects are equal at every n, so either bound
// serves the other.
var NaddEqSym = naddEqSymThm{family.Add(registry.ProofEntry{
	Name: "NaddEqSym",
	Key:  "prop_39a91c41354e55ac",
	// Unfold both sides, then let the symmetry of dist identify the two
	// defects.
	// The closure binds NOTHING: the unfold and the refute both work under
	// the ∀-prefix, so there is no leading strip for a parameter to absorb.
	Build: family.Theorem("∀x y:nadd. nadd_eq(x, y) ⇔ nadd_eq(y, x)",
		func(a *Argument) {
			a.Do(
				// Both sides become ∃B. ∀n. nat_dist(defect at n) ≤ B, with the
				// two dist arguments swapped between the sides.
				Unfold(NaddEqDef),
				// nat_dist(m, n) = nat_dist(n, m) makes the two defects equal at every
				// n; one refute transports each side's bound to the other.
				Cite(nat_monus.DistSym),
				CnfRefute(),
			)
		}),
})}

// NaddEqTrans — slope equivalence is transitive:
//
//	⊢ ∀x y z : nadd. nadd_eq(x, y) ⇒ nadd_eq(y, z) ⇒ nadd_eq(x, z)
//
// Writing x(n) for dest_nadd(x, n): the hypotheses supply bounds B₀
// and B₁ with nat_dist(x(n), y(n)) ≤ B₀ and nat_dist(y(n), z(n)) ≤ B₁ for
// every n, and B := B₀ + B₁ then bounds the pair x, z — at each n
// the triangle inequality through the midpoint y(n) gives
//
//	nat_dist(x(n), z(n)) ≤ nat_dist(x(n), y(n)) + nat_dist(y(n), z(n)) ≤ B₀ + B₁.
//
// nat_order.LessEqAdd2 sums the two leg estimates; nat_monus.DistTriangleLessEq
// lowers the leg-sum bound to the outer distance.
var NaddEqTrans = naddEqTransThm{family.Add(registry.ProofEntry{
	Name: "NaddEqTrans",
	Key:  "prop_13d8fde3e368706",
	// goal — unfold the equivalences, witness the sum of the two hypothesis
	// bounds, and settle the pointwise estimate by triangle through y.
	// The closure binds NOTHING: the equivalences are unfolded BEFORE the
	// slopes are fixed (so the unfold sees the ∀-form and leaves the two
	// implications for the explicit StripImps to name), and a bound
	// parameter would have to strip first.
	Build: family.Theorem(Statement{
		Binders: "∀x y z:nadd.",
		Hypotheses: []string{
			"nadd_eq(x, y)",
			"nadd_eq(y, z)",
		},
		Conclusion: "nadd_eq(x, z)",
	},
		func(a *Argument) {
			ctx := a.Ctx()
			v := ops(ctx)
			nadd := MakeType("nadd")
			x0, y0, z0 := ctx.Var("x_0", nadd), ctx.Var("y_0", nadd), ctx.Var("z_0", nadd)
			n0 := ctx.Var("n_0", NumType)
			a.Do(
				// Each equivalence unfolds to ∃B.∀n. nat_dist(·(n), ·(n)) ≤ B.
				Unfold(NaddEqDef),
				StripQuant(), // fix the slopes x₀, y₀, z₀
			)
			bounds := a.Conjuncts(
				a.Assume(),
				"x₀ stays within a uniform bound of y₀",
				"y₀ stays within a uniform bound of z₀")
			boundXYEx := bounds[0] // ∃B.∀n. nat_dist(x₀(n), y₀(n)) ≤ B
			boundYZEx := bounds[1] // ∃B.∀n. nat_dist(y₀(n), z₀(n)) ≤ B

			// The two legs' uniform bounds, Skolemized as B₀ and B₁.
			B0, boundXY := a.Unpack(boundXYEx)
			B1, boundYZ := a.Unpack(boundYZEx)

			a.Do(
				// The bounds compose: B := B₀ + B₁ works for the pair x₀, z₀.
				Witness(v.sum(B0, B1)),
				StripQuant(), // fix the evaluation point n₀
			)
			legSum := a.Have(
				"the leg estimates add — LessEqAdd2 sums the two uniform bounds read "+
					"at n₀: the x₀–y₀ distance is at most B₀, the y₀–z₀ distance at most B₁",
				ctx.MakePropText(
					"dist((dest_nadd(x₀, n₀), dest_nadd(y₀, n₀))) + dist((dest_nadd(y₀, n₀), dest_nadd(z₀, n₀))) ≤ "+
						"B₀ + B₁"),
				By(
					boundXY.At(n0),
					boundYZ.At(n0),
					At(nat_order.LessEqAdd2,
						v.d(v.at(x0, n0), v.at(y0, n0)),
						v.d(v.at(y0, n0), v.at(z0, n0)), B0, B1)))
			a.Show(
				"triangle through the midpoint y₀(n₀) — nat_monus.DistTriangleLessEq "+
					"lowers the leg-sum bound to dist(x₀(n₀), z₀(n₀)) ≤ B₀ + B₁",
				By(
					legSum,
					At(nat_monus.DistTriangleLessEq,
						v.at(x0, n0), v.at(y0, n0), v.at(z0, n0),
						v.sum(B0, B1))))
		}),
})}

// NaddEqEquivalence — slope equivalence is an equivalence relation in the
// sense of relations/equivalence, so that chapter's class calculus and
// its partition theorem read at nadd_eq, whose classes are the
// non-negative reals of the layer above.
var NaddEqEquivalence = naddEqEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "NaddEqEquivalence",
	Key:  "prop_1e302afd4c29e5e4",
	Build: family.Instance(equivalence.Equivalence, "equivalence(nadd_eq)",
		Case(
			"reflexive: every slope is equivalent to itself",
			Unfold(equivalence.ReflexiveDef),
			Cite(NaddEqRefl)),
		Case(
			"symmetric: an equivalence reads the same backwards",
			Unfold(equivalence.SymmetricDef),
			By(NaddEqSym)),
		Case(
			"transitive: two equivalences through a common slope compose",
			Unfold(equivalence.TransitiveDef),
			By(NaddEqTrans))),
})}
