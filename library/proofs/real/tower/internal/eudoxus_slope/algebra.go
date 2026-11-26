// algebra.go — the algebra of slopes: addition, multiplication, inversion, and ℕ's image.
//
// Four parts, marked by banners:
//
// - Slope addition
// - Slope multiplication, which is COMPOSITION of the underlying
// functions
// - The chapter's hard analytic core
// - The ℕ-embedding n ↦ (m ↦ n·m) and its morphism laws

package eudoxus_slope

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Slope addition
// ---------------------------------------------------------------------------
//
// slope addition, which is the pointwise sum on the underlying ℕ→ℕ
// functions:
//
// 	(x + y)(n) = dest_nadd(x, n) + dest_nadd(y, n)
//
// and whose laws hold up to slope equivalence (nadd_eq), not strict
// equality — the quotient one layer up (nonneg_real) turns them into honest
// equations. The file opens at the carrier level (the pointwise sum of
// two slopes IS a slope, which is where the tier's laws all start) and
// then runs commutativity, associativity, the identity and
// cancellation.
//
// README: the "addition" half of the addition/multiplication bullet.

// Add — reading slope addition pointwise:
//
//	⊢ ∀n x y. x(n) + y(n) = dest_nadd((x + y), n)
//
// (writing x(n) for dest_nadd(x, n)). nadd_add packages the pointwise
// sum λn. x(n)+y(n) as a slope via mk_nadd; the theorem says dest_nadd
// undoes the packaging. Two ingredients:
//
// - isSlope: the pointwise sum of two slopes satisfies the defining
// near-linearity bound. Its defect splits along the sum
// (nat_monus.DistAdd2) into the two summands' own defects, so the two
// Cauchy constants B₀, B₁ bound it by (B₀+B₁)·(m+n).
// - goal: a function is a slope exactly when dest_nadd ∘ mk_nadd
// fixes it (the membership axiom of the nadd type definition), so
// dest_nadd(nadd_add(x, y)) = λn. x(n)+y(n); the statement is that
// equation read at n.
//
// Gated arith carries the estimate's plumbing: the distributivity
// regroupings are ONE ring-identity assert, and the ≤-chaining of the
// split defects is linear — nat_arith.LeftAddDistrib /
// nat_arith.RightAddDistrib / nat_order.LessEqAdd2 / nat_order.LessEqTrans
// are all absorbed there, so this member cites none of them.
var Add = addThm{family.Add(registry.ProofEntry{
	Name: "Add",
	Key:  "prop_f92a243048d4b62",
	// The proof is one lemma plus the assembly, written as a linear script:
	// `isSlope` is a Go local the goal cites by closure capture.
	Build: family.Sections(
		"∀n:num. ∀x y:nadd. dest_nadd(x, n) + dest_nadd(y, n) = dest_nadd(x + y, n)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// x_0, y_0 the two slopes; B_0, B_1 their Cauchy constants;
			// m_0, n_0 the defect's two arguments. n is the pointwise sum's
			// λ-binder.
			B_0 := ctx.Var("B_0", NumType)
			B_1 := ctx.Var("B_1", NumType)
			m_0 := ctx.Var("m_0", NumType)
			n_0 := ctx.Var("n_0", NumType)
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			y_0 := ctx.Var("y_0", MakeType("nadd"))
			n := ctx.Var("n", NumType)

			membershipThm := naddMembership(ctx)

			// The pointwise values and cross products of the defect at (m₀, n₀),
			// writing x(n) for dest_nadd(x, n): xn = x₀(n₀), mxn = m₀·x₀(n₀), ….
			xn := v.at(x_0, n_0)
			yn := v.at(y_0, n_0)
			xm := v.at(x_0, m_0)
			ym := v.at(y_0, m_0)
			mxn, myn := v.mul(m_0, xn), v.mul(m_0, yn)
			nxm, nym := v.mul(n_0, xm), v.mul(n_0, ym)
			mn := v.sum(m_0, n_0)
			// The ring identities: each defect component and the bound
			// distribute into the cross terms nat_monus.DistAdd2 speaks about.
			distribM := v.mul(m_0, v.sum(xn, yn)).Eq(v.sum(mxn, myn))
			distribN := v.mul(n_0, v.sum(xm, ym)).Eq(v.sum(nxm, nym))
			distribB := v.mul(v.sum(B_0, B_1), mn).
				Eq(v.sum(v.mul(B_0, mn), v.mul(B_1, mn)))

			// isSlope: the pointwise sum of two slopes is a slope — its defect at
			// (m, n) splits along the sum into the two summands' defects
			// (nat_monus.DistAdd2), each bounded by its own Cauchy constant, so
			// B₀+B₁ bounds the sum.
			isSlope := ctx.Lemma("∀x y:nadd. is_nadd(λn:num. dest_nadd(x, n) + dest_nadd(y, n))",
				func(a *Argument) {
					a.Do(
						// is_nadd unfolds (and β-reduces) to the near-linearity bound
						// ∃B. ∀m n. nat_dist(m·(x(n)+y(n)), n·(x(m)+y(m))) ≤ B·(m+n).
						Unfold(IsNaddDef),
						StripQuant(), // fix the two slopes: x₀, y₀
					)
					// Cauchy at x₀ and at y₀; each Unpack Skolemizes the ∃B into
					// the constant B₀ resp. B₁, with body
					// ∀m n. nat_dist(m·x₀(n), n·x₀(m)) ≤ B₀·(m+n).
					_, cauchyX := a.Unpack(At(Cauchy, x_0))
					_, cauchyY := a.Unpack(At(Cauchy, y_0))
					a.Do(
						// The summed constant bounds the summed defect.
						Witness(v.sum(B_0, B_1)),
						StripQuant(), // fix the defect's arguments: m₀, n₀
					)
					ring := a.Have(
						"ring identities — the defect's two components and the bound each "+
							"distribute into the cross terms nat_monus.DistAdd2 speaks about",
						MakeProp(distribM.And(distribN).And(distribB)),
						ByArith())
					a.Show(
						"the ≤-chain is linear — DistanceAdd2 splits the regrouped defect "+
							"into the two Cauchy-bounded distances, summing to (B₀+B₁)·(m₀+n₀)",
						ByArith(
							ring,
							// both Cauchy bounds at (m₀, n₀)
							cauchyX.At(m_0, n_0), // nat_dist(m₀·x₀(n₀), n₀·x₀(m₀)) ≤ B₀·(m₀+n₀)
							cauchyY.At(m_0, n_0), // nat_dist(m₀·y₀(n₀), n₀·y₀(m₀)) ≤ B₁·(m₀+n₀)
							// nat_monus.DistAdd2 at the four cross products: the
							// componentwise-summed dist is at most the sum of
							// the two componentwise dists.
							At(nat_monus.DistAdd2, mxn, myn, nxm, nym)))
				})

			// membership keeps a *HypHandle: UseLemma is a NON-preserving
			// install, so what lands is not the axiom's own statement (the
			// lemma tactic rewrites the resident context on the way in) and
			// content-addressing has nothing to name. Capture is the only
			// available locator here.
			membership := NewHypHandle("membership") // the typedef membership axiom
			// sum = λn. x₀(n) + y₀(n), the pointwise sum under mk_nadd.
			sum := n.To(v.sum(v.at(x_0, n), v.at(y_0, n)))

			// goal: with isSlope in hand the close is refutation-free — ground the
			// membership axiom at the pointwise sum, and citing isSlope turns the
			// iff into dest_nadd(mk_nadd(sum)) = sum, which β-reduces the goal to
			// reflexivity.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(
						membership.From(UseLemma(membershipThm)), // the typedef membership axiom as resident fact
						StripQuant(),                             // n₀, x₀, y₀
						Unfold(NaddAddDef),                       // (x₀ + y₀) → mk_nadd(sum)
						membership.Ground(sum),                   // membership read at r := sum
						// isSlope discharges the iff's left side, so
						// dest_nadd(mk_nadd(sum)) = sum rewrites the goal closed.
						Cite(isSlope),
					)
				})
		}),
})}

// AddWellDef — slope addition respects slope equivalence:
//
//	⊢ ∀x x' y y' : nadd. nadd_eq(x, x') ∧ nadd_eq(y, y')
//	 ⇒ nadd_eq((x + y), (x' + y'))
//
// Writing x(n) for dest_nadd(x, n): the equivalences supply bounds
// B₀, B₁ with nat_dist(x(n), x'(n)) ≤ B₀ and nat_dist(y(n), y'(n)) ≤ B₁ at
// every n, and B₀ + B₁ then bounds the defect of the sums — at each
// point the sums' distance splits across the two coordinates,
//
//	nat_dist(x(n) + y(n), x'(n) + y'(n)) ≤ nat_dist(x(n), x'(n)) + nat_dist(y(n), y'(n)) ≤ B₀ + B₁,
//
// and Add's dest equation identifies (x + y)(n) with
// x(n) + y(n). That one sentence is the whole proof: unfold, add the
// bounds, evaluate pointwise. The chain's midpoint is the coordinate
// split, which the ℕ-bundle decides directly — no nat_monus.DistAdd2 dep
// needed.
//
// Sole dep: Add (the dest equation ∀n x y. x(n) + y(n) = dest_nadd((x + y), n)).
var AddWellDef = addWellDefThm{family.Add(registry.ProofEntry{
	Name: "AddWellDef",
	Key:  "prop_85c458a202d748d8",
	// Unfold the equivalences, witness the sum of the two defect bounds,
	// and settle the pointwise estimate coordinate-by-coordinate.
	// The trailing `_ Fact` absorbs the ⇒: the pair of equivalences is
	// assumed at the boundary, then split and unfolded below, so the body
	// never needs it by name.
	Build: family.Theorem(Statement{
		Binders: "∀x x' y y':nadd.",
		Hypotheses: []string{
			"nadd_eq(x, x')",
			"nadd_eq(y, y')",
		},
		Conclusion: "nadd_eq(x + y, x' + y')",
	},
		func(a *Argument, x, xp, y, yp Term, _ Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			B_0, B_1 := ctx.Var("B_0", NumType), ctx.Var("B_1", NumType)
			n_0 := ctx.Var("n_0", NumType)
			a.Do(
				// Split the assumed conjunction into the two separate
				// hypotheses nadd_eq(x₀, x'₀) and nadd_eq(y₀, y'₀), so each
				// unfolds to its own defect bound below.
				TrivialSimplify(),
				// Each equivalence unfolds to ∃B.∀n. nat_dist(·(n), ·(n)) ≤ B.
				Unfold(NaddEqDef),
				StripQuant(), // Skolemize the x₀–x'₀ defect bound as B₀
				StripQuant(), // Skolemize the y₀–y'₀ defect bound as B₁
			)
			boundX := a.Hyp("∀n:num. dist((dest_nadd(x₀, n), dest_nadd(x'₀, n))) ≤ B₀")
			boundY := a.Hyp("∀n:num. dist((dest_nadd(y₀, n), dest_nadd(y'₀, n))) ≤ B₁")
			a.Do(
				// The defect bounds add: B := B₀ + B₁ works for the sums.
				Witness(v.sum(B_0, B_1)),
				StripQuant(), // fix the evaluation point n₀
			)
			// The estimate's midpoint: the sums' defect splits across the
			// two coordinates, and only then do the two bounds apply.
			split := a.Have(
				"dist(x(n)+y(n), x'(n)+y'(n)) ≤ dist(x(n),x'(n)) + "+
					"dist(y(n),y'(n)) — the sums' defect splits across the coordinates",
				MakeProp(v.le(
					v.d(v.sum(v.at(x, n_0), v.at(y, n_0)), v.sum(v.at(xp, n_0), v.at(yp, n_0))),
					v.sum(v.d(v.at(x, n_0), v.at(xp, n_0)), v.d(v.at(y, n_0), v.at(yp, n_0))))),
				ByArith())
			a.Show(
				"each coordinate defect is bounded by B₀ resp. B₁, so the split sum is bounded by B₀ + B₁",
				ByArith(
					split,
					// the two uniform bounds at n₀
					boundX.At(n_0),
					boundY.At(n_0),
					// Add's dest equation evaluates both sums at n₀:
					// (x₀ + y₀)(n₀) = x₀(n₀) + y₀(n₀), likewise for the primes.
					At(Add, n_0, x, y),
					At(Add, n_0, xp, yp)))
		}),
})}

// AddSym — commutativity of slope addition, up to slope
// equivalence:
//
//	⊢ ∀x y : nadd. nadd_eq((x + y), (y + x))
//
// Commutativity at the function level follows from commutativity of
// `+` on ℕ (nat_arith.AddSym) plus extensionality, then weakens from `=`
// to nadd_eq via reflexivity (NaddEqRefl). The proof is 3 lemmas +
// the goal:
//
// - lemma1: pointwise commutativity at each `n` — nat_arith.AddSym.
// - lemma2: congruence under mk_nadd from lemma1.
// - lemma3: lift `=` to nadd_eq via NaddEqRefl.
// - goal: Unfold(NaddAddDef) + Cite(lemma3).
var AddSym = addSymThm{family.Add(registry.ProofEntry{
	Name: "AddSym",
	Key:  "prop_270fe4f3a161582a",
	// The proof is four sections written as a linear script: each lemma is a
	// Go local the next section cites by closure capture.
	Build: family.Sections(
		"∀x y:nadd. nadd_eq(x + y, y + x)",
		func(ctx *Script, headline string) *GoalStackNode {
			EqReflThm := ctx.Dep(NaddEqRefl)

			v := ops(ctx)

			n := ctx.Var("n", NumType)
			// The Skolem constants lemma3's StripQuant mints.
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			y_0 := ctx.Var("y_0", MakeType("nadd"))

			// lemma1: pointwise commutativity — nat_arith.AddSym at the witness
			// `(dest_nadd(x, n), dest_nadd(y, n))`.
			lemma1 := ctx.Lemma("∀n:num. ∀x y:nadd. "+
				"    dest_nadd(x, n) + dest_nadd(y, n) = dest_nadd(y, n) + dest_nadd(x, n)",
				func(a *Argument) {
					a.Do(Cite(nat_arith.AddSym), a.Ctx().CloseByAuto())
				})

			// lemma2 — congruence under mk_nadd from lemma1's pointwise equality.
			lemma2 := ctx.Lemma("∀x y:nadd. "+
				"    mk_nadd(λn:num. dest_nadd(x, n) + dest_nadd(y, n)) = "+
				"    mk_nadd(λn:num. dest_nadd(y, n) + dest_nadd(x, n))",
				func(a *Argument) {
					a.Do(StripQuant(), Congr(), CiteNode(lemma1))
				})

			// lemma3: ⊢ ∀x y. nadd_eq(mk_nadd(λn. ...), mk_nadd(λn. ...))
			// Lift lemma2's `=` to `nadd_eq` via NaddEqRefl.
			lemma3 := ctx.Lemma("∀x y:nadd. "+
				"    nadd_eq(mk_nadd(λn:num. dest_nadd(x, n) + dest_nadd(y, n)), "+
				"        mk_nadd(λn:num. dest_nadd(y, n) + dest_nadd(x, n)))",
				func(a *Argument) {
					// The left slope — x₀ + y₀ read pointwise and packaged back
					// by mk_nadd. Both the assertion and the close speak about it.
					sumSlope := v.MkNadd.Apply(n.To(v.sum(v.at(x_0, n), v.at(y_0, n))))
					a.Do(
						StripQuant(),
						AssertStep(
							MakeProp(sumSlope.Eq(
								v.MkNadd.Apply(n.To(v.sum(v.at(y_0, n), v.at(x_0, n)))))),
							Case(
								"the two pointwise sum slopes at (x₀, y₀) are equal — lemma2's instance",
								CiteNode(lemma2),
							),
							Case(
								"the slopes being equal, nadd_eq between them is its reflexivity",
								UseLemma(EqReflThm),
								// Name the left slope: against NaddEqRefl's ∀x. nadd_eq(x, x)
								// the asserted equality is then a plain identity between
								// two atoms, and what is left is propositional.
								DenoteTerm("sumSlope", sumSlope),
								Basic(),
							),
						),
					)
				})

			// goal: unfold nadd_add's pointwise-sum definition; lemma3 then matches.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(Unfold(NaddAddDef), Cite(lemma3))
				})
		}),
})}

// AddAssoc — slope addition is associative up to slope equivalence:
//
//	⊢ ∀x y z : nadd. nadd_eq((x + (y + z)), ((x + y) + z))
//
// Writing x(n) for dest_nadd(x, n): Add's dest equation gives
// (x + y)(n) = x(n) + y(n), and applying it twice to each side of
// the associative equation shows both sides evaluate to
//
//	x(n) + y(n) + z(n)
//
// at every n. The pointwise defect is therefore identically zero,
// so B := 0 witnesses the equivalence bound. Two sections:
//
// - lemma1: the pointwise regrouping — 4 Add instances +
// ℕ-associativity (a single gated-arith close).
// - goal: unfold nadd_eq, witness 0, cite lemma1, close by
// 0-distance.
//
// Sole dep: Add (the dest equation ∀n x y. x(n) + y(n) = dest_nadd((x + y), n)).
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name: "AddAssoc",
	Key:  "prop_6d070c8d29722e9a",
	// The proof is two sections written as a linear script: `lemma1` is a Go
	// local the goal cites by closure capture.
	Build: family.Sections(
		"∀x y z:nadd. nadd_eq(x + (y + z), x + y + z)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// lemma1's abstract points — free variables of its sequent, so
			// declared rather than bound.
			n := ctx.Var("n", NumType)
			x := ctx.Var("x", MakeType("nadd"))
			y := ctx.Var("y", MakeType("nadd"))
			z := ctx.Var("z", MakeType("nadd"))
			// The goal's Skolem constants, minted by its StripQuant below.
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			y_0 := ctx.Var("y_0", MakeType("nadd"))
			z_0 := ctx.Var("z_0", MakeType("nadd"))
			n_0 := ctx.Var("n_0", NumType)

			// lemma1: x, y, z : nadd, n : num
			//
			//	⊢ dest_nadd((x + (y + z)), n)
			//	 = dest_nadd(((x + y) + z), n)
			//
			// The pointwise regrouping. Add instantiated at each of the four
			// distinct sub-additions expresses every dest_nadd((· + ·), n)
			// as an ℕ-level sum of dest_nadd(·, n)s — after which both sides equal
			// x(n) + y(n) + z(n) by ℕ-associativity of +.
			lemma1 := ctx.Lemma("dest_nadd(x + (y + z), n) = dest_nadd(x + y + z, n)",
				func(a *Argument) {
					a.Do(
						// The four sub-additions the two sides mention:
						// (x + (y + z)) — outer, left side
						// (y + z) — inner, left side
						// (x + y) — inner, right side
						// ((x + y) + z) — outer, right side
						// One Add instance per sub-addition names its value at n,
						// and both sides unfold to x(n) + y(n) + z(n) — linear
						// arithmetic.
						ByArith(
							At(Add, n, x, v.NaddAdd.Apply(y, z)),
							At(Add, n, y, z),
							At(Add, n, x, y),
							At(Add, n, v.NaddAdd.Apply(x, y), z)),
					)
				})

			// goal: the pointwise defect from lemma1 is zero, so B := 0 witnesses
			// the slope-equivalence bound.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(
						StripQuant(), // fix the slopes x₀, y₀, z₀
						// Unfold nadd_eq: ⊢ ∃B.∀n. nat_dist(LHS(n), RHS(n)) ≤ B.
						Unfold(NaddEqDef),
						// The defect is identically zero, so B := 0 bounds it.
						Witness(ctx.Numeral(0)),
						StripQuant(), // fix the evaluation point n₀
						// lemma1 at (x₀, y₀, z₀, n₀) equates the two dests, and
						// equal numbers have distance 0, so the bound holds.
						ByArith(At(lemma1, x_0, y_0, z_0, n_0)),
					)
				})
		}),
})}

// AddLeftId — 0 + x is equivalent to x:
//
//	⊢ ∀x : nadd. nadd_eq((nadd_of_num(0) + x), x)
//
// Slope equivalence asks the pointwise defect to stay uniformly
// bounded. Read pointwise at each n, the defect vanishes identically:
//
//	dest_nadd((nadd_of_num(0) + x), n)
//	 = dest_nadd(nadd_of_num(0), n) + dest_nadd(x, n) -- Add
//	 = 0 · n + dest_nadd(x, n) -- OfNum
//	 = 0 + dest_nadd(x, n) -- ℕ arith
//	 = dest_nadd(x, n) -- ℕ arith
//
// so the distance to dest_nadd(x, n) is exactly 0 and any bound
// including B := 0 works. One section: unfold nadd_eq, witness B := 0,
// ground the pointwise equations at n₀ / at (0, n₀), let arithmetic
// finish the ℕ residual — a transport chain through pointwise=dest
// and 0-arith identities, every step already in the closer's language.
var AddLeftId = addLeftIdThm{family.Add(registry.ProofEntry{
	Name: "AddLeftId",
	Key:  "prop_46c4f201d282e3c1",
	Build: family.Theorem("∀x:nadd. nadd_eq(nadd_of_num(0) + x, x)",
		func(a *Argument, x Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero := ctx.Numeral(0) // the bound B := 0 and the atom 0 : num
			n_0 := ctx.Var("n_0", NumType)
			a.Do(
				// nadd_eq unfolds to
				// ∃B. ∀n. nat_dist(dest_nadd((nadd_of_num(0) + x₀), n),
				// dest_nadd(x₀, n)) ≤ B.
				Unfold(NaddEqDef),
				Witness(zero), // the defect vanishes pointwise, so B := 0
				StripQuant(),  // n₀
				// Residual: nat_dist(0·n₀ + dest_nadd(x₀,n₀), dest_nadd(x₀,n₀)) ≤ 0.
				// The closer handles 0·n₀ = 0, 0 + a = a, nat_dist(a, a) = 0, 0 ≤ 0.
				ByArith(
					// dest_nadd((a + b), n) = dest_nadd(a, n) + dest_nadd(b, n)
					// at (n₀, nadd_of_num(0), x₀).
					At(Add, n_0, v.NaddOfNum.Apply(zero), x),
					// dest_nadd(nadd_of_num(k), n) = k · n at (0, n₀), so the
					// first summand is 0 · n₀.
					At(OfNum, zero, n_0)),
			)
		}),
})}

// AddLeftCancel — the left-cancellation law for slope addition:
//
//	⊢ ∀x y z : nadd. nadd_eq((x + y), (x + z))
//	 ⇒ nadd_eq(y, z)
//
// Writing x(n) for dest_nadd(x, n), the Add dest equation reads
// (x + y)(n) = x(n) + y(n), so
//
//	nat_dist((x + y)(n), (x + z)(n))
//	 = nat_dist(x(n) + y(n), x(n) + z(n)) -- Add ×2
//	 = nat_dist(y(n), z(n)) -- ℕ dist cancels the shared summand
//
// pointwise. So the two equivalences carry the SAME bound: the
// constant assumed for the sums serves y and z verbatim. Sole
// non-arith dep: Add (the dest equation
// ∀n x y. x(n) + y(n) = dest_nadd((x + y), n)).
var AddLeftCancel = addLeftCancelThm{family.Add(registry.ProofEntry{
	Name: "AddLeftCancel",
	Key:  "prop_edd570dbd3733deb",
	// Assume the sums are equivalent and unfold: the assumption is a
	// uniform bound B₀ on nat_dist((x+y)(n), (x+z)(n)), the goal the same
	// shape for y, z. Witness the goal with the very same B₀; at a fixed
	// index n₀ the two Add dest equations rewrite the assumed distance
	// into nat_dist(x₀(n₀) + y₀(n₀), x₀(n₀) + z₀(n₀)), where arith cancels
	// the shared summand.
	// The trailing `sumsEq` Fact is the ⇒-antecedent: the assumed
	// equivalence of the sums, unfolded and then Skolemized into the
	// uniform bound `sumBound`.
	Build: family.Theorem(
		Statement{
			Binders: "∀x y z:nadd.",
			Hypotheses: []string{
				"nadd_eq(x + y, x + z)",
			},
			Conclusion: "nadd_eq(y, z)",
		},
		func(a *Argument, x, y, z Term, sumsEq Fact) {
			ctx := a.Ctx()
			n0 := ctx.Var("n_0", NumType) // the evaluation point

			// Assumption and goal both become bounded-defect statements
			// ∃B. ∀n. nat_dist(·(n), ·(n)) ≤ B.
			a.Do(Unfold(NaddEqDef))
			// B₀ the assumed defect bound of the sums:
			// sumBound is ∀n. nat_dist((x₀+y₀)(n), (x₀+z₀)(n)) ≤ B₀.
			B0, sumBound := a.Unpack(sumsEq)
			a.Do(
				Witness(B0),  // the same bound is claimed for y₀, z₀
				StripQuant(), // fix the evaluation point n₀
			)
			a.Show(
				"dist(x(n) + y(n), x(n) + z(n)) = dist(y(n), z(n)) — the "+
					"shared summand cancels and the assumed bound transfers",
				ByArith(
					sumBound.At(n0),
					// Add's dest equation at (n₀, x₀, y₀) and (n₀, x₀, z₀):
					// x₀(n₀) + y₀(n₀) = (x₀ + y₀)(n₀) resp. (x₀ + z₀)(n₀), so
					// the assumed distance is between two shared-summand sums.
					At(Add, n0, x, y),
					At(Add, n0, x, z)))
		}),
})}

// ---------------------------------------------------------------------------
// Slope multiplication, which is COMPOSITION of the underlying functions
// ---------------------------------------------------------------------------
//
// slope multiplication, which is COMPOSITION of the underlying functions:
// the carrier-level operation and its two welldef lemmas, then
// commutativity, associativity, the identity, and distributivity on both
// sides — all up to slope equivalence.
//
// README: the "multiplication" half of the addition/multiplication
// bullet.

// Mul reads the composition representative of a product. Writing f and g
// for the underlying functions of x and y, route its defect through
//
//	m·f(g(n)) → f(m·g(n)) → f(n·g(m)) → n·f(g(m)).
//
// Homogeneity bounds the outer legs and lipschitz transports g's Cauchy
// bound across the middle. The resulting affine bound becomes linear by
// nat_order.BoundsNotZero, since the defect vanishes at the origin.
var Mul = mulThm{family.Add(registry.ProofEntry{
	Name: "Mul",
	Key:  "prop_378b04ef3639f96b",
	Build: family.Sections(
		"∀n:num. ∀x y:nadd. dest_nadd(x, dest_nadd(y, n)) = dest_nadd(x * y, n)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			isSlope := ctx.Lemma("∀x y:nadd. is_nadd(λn:num. dest_nadd(x, dest_nadd(y, n)))",
				func(a *Argument, x, y *Expr[Nadd]) {
					a.Do(Unfold(IsNaddDef))
					C, cauchyY := a.UnpackAs[Nat](Cauchy.At(y), "C")
					L, lipschitzX := a.UnpackAs[Nat](lipschitz.At(x), "L")
					H, homogX := a.UnpackAs[Nat](homogeneous.At(x), "H")
					coefficient := v.sum(H.Core(), v.mul(L.Core(), C.Core()))
					constant := v.sum(H.Core(), H.Core())
					affine := a.Have(
						"the three-leg estimate gives an affine bound",
						"∀m n:num. "+
							"    dist((m * dest_nadd(x, dest_nadd(y, n)), n * dest_nadd(x, dest_nadd(y, m)))) ≤ "+
							"    (H + L * C) * (m + n) + (H + H)",
						Derive(func(b *Argument) {
							m := b.FixAs[Nat]()
							n := b.FixAs[Nat]()
							yn := v.at(y.Core(), n.Core())
							ym := v.at(y.Core(), m.Core())
							myN := v.mul(m.Core(), yn)
							nyM := v.mul(n.Core(), ym)
							p := v.mul(m.Core(), v.at(x.Core(), yn))
							q := v.mul(n.Core(), v.at(x.Core(), ym))
							r := v.at(x.Core(), myN)
							s := v.at(x.Core(), nyM)
							cauchyBound := v.mul(C.Core(), v.sum(m.Core(), n.Core()))
							middle := b.Have(
								"lipschitz transports the Cauchy bound across the middle leg",
								MakeProp(v.le(v.d(r, s), v.mul(L.Core(), cauchyBound))),
								ByArith(
									cauchyY.At(m, n),
									lipschitzX.At(myN, nyM),
									At(nat_order.LessEqMulCancel, L, v.d(myN, nyM), cauchyBound)))
							b.Show(
								"the triangle inequalities join the middle and homogeneity legs",
								ByArith(
									middle,
									homogX.At(m, yn),
									homogX.At(n, ym),
									At(nat_monus.DistTriangle, p, q, r),
									At(nat_monus.DistTriangle, r, q, s),
									At(nat_monus.DistSym, p, r)))
						}))
					origin := a.Have(
						"the defect vanishes at the origin",
						"dist((0 * dest_nadd(x, dest_nadd(y, 0)), 0 * dest_nadd(x, dest_nadd(y, 0)))) = 0",
						ByArith())
					defect := a.TermAs[Op[Nat]](
						"λm:num. λn:num. dist((m * dest_nadd(x, dest_nadd(y, n)), n * dest_nadd(x, dest_nadd(y, m))))")
					a.Show(
						"absorb the affine constant into a linear bound",
						By(affine, origin, At(nat_order.BoundsNotZero, defect, coefficient, constant)))
				})

			return ctx.Theorem(headline,
				func(a *Argument, n *Expr[Nat], x, y *Expr[Nadd]) {
					a.Do(Unfold(NaddMulDef))
					composition := a.TermAs[Fun[Nat, Nat]]("λn:num. dest_nadd(x, dest_nadd(y, n))")
					representative := a.Have(
						"membership recovers the composition representative",
						MakeProp(v.DestNadd.Apply(v.MkNadd.Apply(composition.Core())).Eq(composition.Core())),
						By(At(isSlope, x, y), At(NaddDef.Membership, composition)))
					a.Show(
						"evaluate the representative at the given index",
						representative.Rw(),
						Basic())
				})
		}),
})}

// mulWellDefRight — replacing the right factor of a slope product by
// an equivalent slope stays equivalent. Combined with commutativity
// (MulSym) this is the full well-definedness of nadd_mul on
// equivalence classes — the fact the hreal quotient turns into an
// honest ring multiplication, and six hreal consumers ride on this
// lemma alone.
//
//	⊢ ∀x y y' : nadd. nadd_eq(y, y') ⇒ nadd_eq(x · y, x · y')
//
// (writing x(n) for dest_nadd(x, n) and · for nadd_mul.)
// Since multiplication is composition, (x·y)(n) = x(y(n)); the defect
// between the products is
//
//	nat_dist( x(y(n)) , x(y'(n)) ) .
//
// Two facts control it: the lipschitz entry grounded at x (constant
// B_x), and the assumed equivalence y ~ y', whose nadd_eq unfolding
// supplies a uniform bound B on nat_dist(y(n), y'(n)). Chain them at n:
//
//	nat_dist(x(y(n)), x(y'(n))) ≤ B_x · nat_dist(y(n), y'(n)) [lipschitz]
//	 ≤ B_x · B [monotonicity of · in the right argument]
//
// so B_x · B is the ∃-witness for the product's defect.
// nat_order.LessEqMulCancel gives the "monotone in the right argument"
// step, and the two-step chain is linear.
//
// One section — the argument reads top-to-bottom exactly as the math
// above: unfold nadd_eq, take B_x from lipschitz, witness B_x·B, scale
// the y-defect by B_x, and chain it under the lipschitz bound, the two
// Mul equalities normalizing the compositions.
var mulWellDefRight = mulWellDefRightThm{family.Add(registry.ProofEntry{
	Name: "mulWellDefRight",
	Key:  "prop_665bd1b253e9deb4",
	// Unfold nadd_eq — both sides of the implication become the ∃B.∀n
	// form. Assume y ~ y' and take its ∃B (calling it B₀), take the
	// lipschitz constant from x (calling it B₁), and witness B₁·B₀ for
	// the product's equivalence. Then at the point n₀ the chain is
	// lipschitz ∘ monotone-cancellation, the second through
	// nat_order.LessEqMulCancel.
	Build: family.Theorem(Statement{
		Binders: "∀x y y':nadd.",
		Hypotheses: []string{
			"nadd_eq(y, y')",
		},
		Conclusion: "nadd_eq(x * y, x * y')",
	},
		func(a *Argument, x, y, yp Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			n_0 := ctx.Var("n_0", NumType)

			a.Do(
				// Unfolding nadd_eq rewrites both sides of the implication to
				// the ∃B.∀n form and discharges the antecedent into a
				// hypothesis in the same step: y₀ ~ y'₀ becomes the assumption
				// ∃B. ∀n. nat_dist(y₀(n), y'₀(n)) ≤ B.
				Unfold(NaddEqDef),
				Given(func(a *Argument, yDefectEx Fact) {
					// Skolemize that defect bound as B₀.
					B_0, yDefect := a.Unpack(yDefectEx)
					// Take the lipschitz bound of x₀ (uniform in m, n):
					// nat_dist(x₀(m), x₀(n)) ≤ B₁ · nat_dist(m, n), unpacking B₁.
					B_1, lipschitzX := a.Unpack(At(lipschitz, x))

					// The y-defect at the point, and the two ends of its scaling.
					yDist := v.d(v.at(y, n_0), v.at(yp, n_0))
					middle := v.mul(B_1, yDist)
					rhs := v.mul(B_1, B_0)

					a.Do(
						Witness(v.mul(B_1, B_0)), // B := B₁ · B₀ — lipschitz scaling of the y-defect
						StripQuant(),             // fix the evaluation point n₀
					)
					scaled := a.Have(
						"the y-defect scaled by the lipschitz constant — B₁·dist(y(n₀), y'(n₀)) ≤ B₁·B₀",
						MakeProp(v.le(middle, rhs)),
						ByArith(
							// y-defect at n₀: nat_dist(y₀(n₀), y'₀(n₀)) ≤ B₀
							yDefect.At(n_0),
							// nat_order.LessEqMulCancel turns "B₁·dist ≤ B₁·B₀" into
							// "B₁ = 0 ∨ dist ≤ B₀"
							At(nat_order.LessEqMulCancel, B_1, yDist, B_0)))
					a.Show(
						"the chain dist(x(y), x(y')) ≤ B₁·dist(y, y') ≤ B₁·B₀, read through the two composition equations",
						ByArith(
							scaled,
							// lipschitz at (y₀(n₀), y'₀(n₀)):
							// nat_dist(x₀(y₀(n₀)), x₀(y'₀(n₀))) ≤ B₁ · nat_dist(y₀(n₀), y'₀(n₀))
							lipschitzX.At(v.at(y, n_0), v.at(yp, n_0)),
							// Two ground Mul cites reduce (x·y)(n₀) and (x·y')(n₀) to
							// their composed forms x₀(y₀(n₀)) and x₀(y'₀(n₀)) — the
							// shape the lipschitz bound already speaks.
							At(Mul, n_0, x, y),
							At(Mul, n_0, x, yp)))
				}),
			)
		}),
})}

// MulWellDef — slope multiplication respects slope equivalence:
//
//	⊢ ∀x x' y y' : nadd. nadd_eq(x, x') ∧ nadd_eq(y, y')
//	 ⇒ nadd_eq((x * y), (x' * y'))
//
// mulWellDefRight only varies the RIGHT factor. Commutation is what
// makes it cover the left one too, so the whole proof is one chain
// alternating the two:
//
//	x·y ≈ x·y' ≈ y'·x ≈ y'·x' ≈ x'·y'
var MulWellDef = mulWellDefThm{family.Add(registry.ProofEntry{
	Name: "MulWellDef",
	Key:  "prop_4f604ebea905e11b",
	// `equivs` is the assumed pair of equivalences; the two varying legs
	// carry it as a premise and read off the half each one needs.
	Build: family.Theorem(Statement{
		Binders: "∀x x' y y':nadd.",
		Hypotheses: []string{
			"nadd_eq(x, x')",
			"nadd_eq(y, y')",
		},
		Conclusion: "nadd_eq(x * y, x' * y')",
	},
		func(a *Argument, x, xp, y, yp Term, equivs Fact) {
			ctx := a.Ctx()
			v := ops(ctx)

			mul := func(p, q Term) Term { return v.NaddMul.Apply(p, q) }
			// The chain's five terms.
			xy := mul(x, y)
			xyp := mul(x, yp)
			ypx := mul(yp, x)
			ypxp := mul(yp, xp)
			xpyp := mul(xp, yp)

			a.Do(
				// The chain's endpoint IS the goal, so it closes it.
				CalcOrder{
					Eq:      v.rel(v.NaddEq),
					EqTrans: NaddEqTrans,
				}.Calc(xy,
					EqLeg(
						xyp,
						"x·y ≈ x·y' — mulWellDefRight at (y₀, y'₀, x₀), its premise discharged by the hyp y₀ ≈ y'₀",
						By(equivs, At(mulWellDefRight, x, y, yp))),
					EqLeg(
						ypx,
						"x·y' ≈ y'·x — MulSym: the factor still to be varied moves into the right slot",
						Cite(MulSym)),
					EqLeg(
						ypxp,
						"y'·x ≈ y'·x' — mulWellDefRight at (x₀, x'₀, y'₀), its premise discharged by the hyp x₀ ≈ x'₀",
						By(equivs, At(mulWellDefRight, yp, x, xp))),
					EqLeg(
						xpyp,
						"y'·x' ≈ x'·y' — MulSym, commuting back into the goal's factor order",
						Cite(MulSym)),
				),
			)
		}),
})}

// MulSym — nadd multiplication is commutative up to slope
// equivalence:
//
//	⊢ ∀x y : nadd. nadd_eq((x * y), (y * x))
//
// Slope multiplication is COMPOSITION, (x·y)(n) = x(y(n)) — a
// non-symmetric operation whose commutativity is not a formal identity
// but a bounded-defect claim. The proof runs the alternative-mul
// estimate mulAlt SYMMETRICALLY, at BOTH (x, y) and (y, x):
//
//	nat_dist(n·x(y(n)), x(n)·y(n)) ≤ A₀·n + B₀ [mulAlt at (x, y)]
//	nat_dist(n·y(x(n)), y(n)·x(n)) ≤ A₁·n + B₁ [mulAlt at (y, x)]
//
// Their two right-hand terms x(n)·y(n) and y(n)·x(n) are EQUAL (nat_arith.MulSym
// on the ℕ-multiplication of the two point values), so the triangle
// inequality through the shared midpoint sums the two bounds into a
// linear estimate on n·nat_dist(x(y(n)), y(x(n))). nat_order.BoundsDivided then
// peels the factor n off, giving the required uniform bound; the
// composition bridge Mul rephrases that bound as the ∃B ∀n form
// nadd_eq unfolds to.
//
// The four sections mirror the four analytic stages, each named for its
// estimate:
//
//	triangleBound nat_dist(n·x(y(n)), n·y(x(n))) ≤ A·n + B
//	divideByN n · nat_dist(x(y(n)), y(x(n))) ≤ A·n + B (nat_monus.DistLeftMul)
//	defectBounded nat_dist(x(y(n)), y(x(n))) ≤ B (nat_order.BoundsDivided)
//	proveGoal nadd_eq((x * y), (y * x)) (unfold + Mul bridge)
//
// It cites mulAlt (the symmetric-use engine — a toolkit sibling), the
// dist calculus, ordering lemmas and Mul (the composition bridge).
// Capability arith:nat for the linear ring identity that folds
// (A₀·n+B₀)+(A₁·n+B₁) into (A₀+A₁)·n+(B₀+B₁).
var MulSym = mulSymThm{family.Add(registry.ProofEntry{
	Name: "MulSym",
	Key:  "prop_22c7cb287fdb0816",
	// The proof is four sections written as a linear script: each estimate
	// is a Go local the next section cites by closure capture.
	Build: family.Sections(
		"∀x y:nadd. nadd_eq(x * y, y * x)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// Skolem frees:
			// x_0, y_0 — the two slopes
			// n_0 — the evaluation point
			// A_0, B_0 — mulAlt's error constants at (x, y)
			// A_1, B_1 — mulAlt's error constants at (y, x)
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			y_0 := ctx.Var("y_0", MakeType("nadd"))
			n_0 := ctx.Var("n_0", NumType)
			A_0 := ctx.Var("A_0", NumType)
			B_0 := ctx.Var("B_0", NumType)
			A_1 := ctx.Var("A_1", NumType)
			B_1 := ctx.Var("B_1", NumType)

			// The three pointwise terms of the triangle chain at n₀:
			// nxy = n₀·x(y(n₀)) (the first mulAlt LHS)
			// nyx = n₀·y(x(n₀)) (the second mulAlt LHS)
			// xnyn = x(n₀)·y(n₀) (the shared midpoint; nat_arith.MulSym commutes to y(n₀)·x(n₀))
			nxy := v.mul(n_0, v.at(x_0, v.at(y_0, n_0)))
			nyx := v.mul(n_0, v.at(y_0, v.at(x_0, n_0)))
			xnyn := v.mul(v.at(x_0, n_0), v.at(y_0, n_0))
			// ynxn is xnyn after the nat_arith.MulSym rewrite — the midpoint as the
			// second mulAlt estimate spells it.
			ynxn := v.mul(v.at(y_0, n_0), v.at(x_0, n_0))

			// triangleBound — run mulAlt at (x, y) and again at (y, x): Skolemize
			// the two error pairs (A₀, B₀) and (A₁, B₁). Witness A := A₀+A₁ and
			// B := B₀+B₁. At each n the two mulAlt estimates share the midpoint
			// x(n)·y(n) = y(n)·x(n) (nat_arith.MulSym), so nat_monus.DistTriangle + nat_monus.DistSym chain
			// them into dist ≤ (A₀·n+B₀) + (A₁·n+B₁); the ring identity folds
			// that RHS into (A₀+A₁)·n + (B₀+B₁), by arithmetic.
			triangleBound := ctx.Lemma("∀x y:nadd. ∃A B:num. ∀n:num. "+
				"    dist((n * dest_nadd(x, dest_nadd(y, n)), n * dest_nadd(y, dest_nadd(x, n)))) ≤ A * n + B",
				func(d *Argument, x, y Term) {
					// The two symmetric-use mulAlt bounds, each installed at (·, ·)
					// and Skolemized in place: (A₀, B₀) from (x, y); (A₁, B₁) from
					// (y, x). One Unpack2 per install peels both the ∃A and the ∃B.
					_, _, mulAltXY := d.Unpack2(At(mulAlt, x, y))
					_, _, mulAltYX := d.Unpack2(At(mulAlt, y, x))

					d.Do(
						// Witness A := A₀+A₁, B := B₀+B₁, fix n₀.
						Witness(v.sum(A_0, A_1)),
						Witness(v.sum(B_0, B_1)),
						StripQuant(),
						// Ground both mulAlt ∀-hyps at n₀, dropping each source.
						mulAltXY.At(n_0),
						Clear(mulAltXY),
						mulAltYX.At(n_0),
						Clear(mulAltYX),
						// Ground the algebra bridges at the exact points of use.
						Cite(nat_monus.DistTriangle, nxy, xnyn, nyx),
						Cite(nat_monus.DistSym, xnyn, nyx),
						Cite(nat_arith.MulSym, v.at(x_0, n_0), v.at(y_0, n_0)),
						// nat_order.LessEqAdd2 at the two triangle summands and their mulAlt bounds.
						Cite(nat_order.LessEqAdd2,
							v.d(nxy, xnyn), v.d(xnyn, nyx),
							v.sum(v.mul(A_0, n_0), B_0), v.sum(v.mul(A_1, n_0), B_1)),
						// LessEqTrans (ℕ-level) at (nat_dist(n₀·x, n₀·y), sum-of-two-triangle-dists,
						// (A₀·n₀+B₀)+(A₁·n₀+B₁)): once the two mulAlt bounds sum via nat_order.LessEqAdd2,
						// this chains through the triangle to the target linear form.
						Cite(nat_order.LessEqTrans,
							v.d(nxy, nyx),
							v.sum(v.d(nxy, xnyn), v.d(xnyn, nyx)),
							v.sum(v.sum(v.mul(A_0, n_0), B_0),
								v.sum(v.mul(A_1, n_0), B_1))),
						// The clean triangle bound BEFORE the ring identity folds, then the
						// identity rewrite closes the chain.
						Derive(func(e *Argument) {
							// nat_arith.MulSym at (x(n₀), y(n₀)), resident from the cite above.
							mulSymEq := e.Hyp(xnyn.Eq(ynxn))
							chained := e.Have(
								"triangle through x(n₀)·y(n₀) — nat_arith.MulSym aligns the second "+
									"mulAlt bound, nat_monus.DistSym flips it, nat_order.LessEqAdd2 sums",
								"dist((n₀ * dest_nadd(x₀, dest_nadd(y₀, n₀)), n₀ * dest_nadd(y₀, dest_nadd(x₀, n₀)))) ≤ "+
									"A₀ * n₀ + B₀ + (A₁ * n₀ + B₁)",
								// Both equations are consumed as REWRITES of the goal,
								// in this order: the midpoint must be commuted before
								// the dist flip can see it.
								Derive(func(f *Argument) {
									f.Do(mulSymEq.Rw()) // x(n₀)·y(n₀) → y(n₀)·x(n₀)
									// That rewrite rebuilds the whole hyp list, so the
									// dist-symmetry equation is re-located by content —
									// in its post-commutation form — rather than tracked
									// through it.
									distSymEq := f.Hyp(MakeProp(v.d(ynxn, nyx).Eq(v.d(nyx, ynxn))))
									f.Do(
										distSymEq.Rw(), // nat_dist(y(n₀)x(n₀), n₀·y(x(n₀))) → nat_dist(n₀·y(x(n₀)), y(n₀)x(n₀))
										CnfRefute())
								}))
							folded := e.Have(
								"the ring identity (A₀·n+B₀)+(A₁·n+B₁) = (A₀+A₁)·n+(B₀+B₁)",
								"A₀ * n₀ + B₀ + (A₁ * n₀ + B₁) = (A₀ + A₁) * n₀ + (B₀ + B₁)",
								ByArith())
							e.Show(
								"rewrite the triangle bound's RHS by the identity — the chain closes",
								By(chained, folded))
						}),
					)
				})

			// divideByN — instantiate triangleBound at (x, y) to get the linear
			// bound on nat_dist(n·x(y(n)), n·y(x(n))), then apply
			// nat_monus.DistLeftMul(n, x(y(n)), y(x(n))): nat_dist(n·a, n·b) = n·nat_dist(a, b),
			// pulling the factor n out of the dist. The witnesses A, B are reused
			// unchanged.
			divideByN := ctx.Lemma("∀x y:nadd. ∃A B:num. ∀n:num. "+
				"    n * dist((dest_nadd(x, dest_nadd(y, n)), dest_nadd(y, dest_nadd(x, n)))) ≤ A * n + B",
				func(d *Argument, x, y Term) {
					// triangleBound at (x₀, y₀); one Unpack2 Skolemizes its ∃A ∃B
					// into A₀, B₀.
					_, _, triBound := d.Unpack2(At(triangleBound, x, y))

					d.Do(
						// Same witnesses A₀, B₀ work — nat_monus.DistLeftMul is a pure equality.
						Witness(A_0),
						Witness(B_0),
						StripQuant(), // fix n₀
						// Ground the triangleBound at n₀ and drop its ∀-source.
						triBound.At(n_0),
						Clear(triBound),
						// nat_monus.DistLeftMul as a rewrite: n·nat_dist(a, b) = nat_dist(n·a, n·b) (fired
						// right-to-left on the goal LHS) turns the goal into the exact
						// shape of the grounded triangleBound hyp and closes the section.
						UseLemma(ctx.DepNormalized(nat_monus.DistLeftMul)),
					)
				})

			// nat_order.BoundsDivided at P := λn. nat_dist(x₀(y₀(n)), y₀(x₀(n))).
			n := Var("n", NumType)
			defectAtN := v.d(v.at(x_0, v.at(y_0, n)), v.at(y_0, v.at(x_0, n)))

			// defectBounded — nat_order.BoundsDivided with its predicate P
			// instantiated at λn. nat_dist(x(y(n)), y(x(n))); the ⇐ direction, together
			// with divideByN at (x, y) supplying the RHS-witness, gives the LHS.
			defectBounded := ctx.Lemma("∀x y:nadd. ∃B:num. ∀n:num. "+
				"    dist((dest_nadd(x, dest_nadd(y, n)), dest_nadd(y, dest_nadd(x, n)))) ≤ B",
				func(d *Argument, x, y Term) {
					d.Do(
						Cite(nat_order.BoundsDivided, n.To(defectAtN)),
						// The ⇔ becomes (∃B. ∀n. P(n) ≤ B) ⇔ (RHS); the RHS is exactly
						// divideByN at (x₀, y₀), which supplies the witness for the ⇐ closure.
						// The citation itself closes the section — divideByN α-matches the
						// ⇔'s RHS shape.
						UseLemma(divideByN.PromisedThm()),
					)
				})

			// eqDef keeps a *HypHandle: UseLemma is a NON-preserving install, so
			// what lands is not the definition's own statement (the lemma tactic
			// rewrites the resident context on the way in) and content-addressing
			// has nothing to name.
			eqDef := NewHypHandle("eqDef")

			// goal: unfold nadd_eq — nadd_eq(u, v) ⇔ ∃B. ∀n. nat_dist(dest_nadd(u, n), dest_nadd(v, n)) ≤ B.
			// The composition bridge Mul rewrites dest_nadd(nadd_mul(x, y), n)
			// as dest_nadd(x, dest_nadd(y, n)) = x(y(n)) (and similarly for the
			// swapped side), reducing the goal to the defectBounded shape
			// ∃B. ∀n. nat_dist(x(y(n)), y(x(n))) ≤ B, which defectBounded supplies.
			return ctx.Theorem(headline,
				func(d *Argument, x, y Term) {
					d.Do(
						// nadd_eq(u, v) ⇔ ∃B. ∀n. nat_dist(dest_nadd(u, n), dest_nadd(v, n)) ≤ B;
						// grounded at u := nadd_mul(x₀, y₀), v := nadd_mul(y₀, x₀).
						eqDef.From(UseLemma(ctx.ConstDefNormalized("nadd_eq"))),
						eqDef.Ground(
							v.NaddMul.Apply(x, y),
							v.NaddMul.Apply(y, x)),
						// The composition bridge: dest_nadd(x, dest_nadd(y, n)) = dest_nadd(nadd_mul(x, y), n).
						UseLemma(ctx.DepNormalized(Mul)),
						// defectBounded at (x₀, y₀) supplies ∃B. ∀n. nat_dist(x(y(n)), y(x(n))) ≤ B,
						// which is nadd_eq's characterization after the Mul bridge.
						Cite(defectBounded, x, y),
						CnfRefute(),
					)
				})
		}),
})}

// MulAssoc — slope multiplication is associative up to slope
// equivalence:
//
//	⊢ ∀x y z : nadd. nadd_eq((x * (y * z)),
//	 ((x * y) * z))
//
// Slope multiplication is function composition — its dest equation is
//
//	dest_nadd((x * y), n) = dest_nadd(x, dest_nadd(y, n)) (Mul)
//
// so at each n both sides of the associative equation collapse to
//
//	dest_nadd(x, dest_nadd(y, dest_nadd(z, n)))
//
// via two Mul rewrites on each side. The pointwise defect is
// therefore identically zero and B := 0 witnesses the equivalence
// bound. Two sections:
//
// - lemma1: the pointwise regrouping — 4 Mul instances (one
// per sub-mul on either side) collapse both sides to the common
// triple-composition.
// - goal: unfold nadd_eq, witness 0, cite lemma1 at the Skolems,
// and close the 0-distance residual with nat_monus.DistRefl + ZeroLessEq
// (arith-free — no arithmetic close is available under this member's
// caps [] regime).
//
// No transport through mk_nadd is needed: the pointwise defect is
// already zero once nadd_eq is unfolded directly on the goal.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name: "MulAssoc",
	Key:  "prop_81db1e582c02bac7",
	// The proof is two sections written as a linear script: `lemma1` is a Go
	// local the goal cites by closure capture.
	Build: family.Sections(
		"∀x y z:nadd. nadd_eq(x * (y * z), x * y * z)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// lemma1's abstract points — free variables of its sequent.
			n := ctx.Var("n", NumType)
			x := ctx.Var("x", MakeType("nadd"))
			y := ctx.Var("y", MakeType("nadd"))
			z := ctx.Var("z", MakeType("nadd"))
			// The goal's Skolem constants: x_0/y_0/z_0 are declared at nadd here
			// and at num elsewhere in the family, so they stay per-member.
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			y_0 := ctx.Var("y_0", MakeType("nadd"))
			z_0 := ctx.Var("z_0", MakeType("nadd"))
			n_0 := ctx.Var("n_0", NumType)

			// lemma1: x, y, z : nadd, n : num
			//
			//	⊢ dest_nadd((x * (y * z)), n)
			//	 = dest_nadd(((x * y) * z), n)
			//
			// The pointwise regrouping. Four Mul instances name the four
			// sub-muls appearing on either side; each cite lifts one dest_nadd((· * ·),·)
			// into a nested dest_nadd(·, dest_nadd(·, ·)). Both sides then read
			//
			//	dest_nadd(x, dest_nadd(y, dest_nadd(z, n)))
			//
			// and the equality closes propositionally.
			lemma1 := ctx.Lemma("dest_nadd(x * (y * z), n) = dest_nadd(x * y * z, n)",
				func(a *Argument) {
					a.Do(
						// One Mul per sub-mul on either side:
						// (x * (y * z)) outer left — at n
						// (y * z) inner left — at n
						// (x * y) inner right — at dest_nadd(z, n)
						// ((x * y) * z) outer right — at n
						Cite(Mul, n, x, v.NaddMul.Apply(y, z)),
						Cite(Mul, n, y, z),
						Cite(Mul, v.at(z, n), x, y),
						Cite(Mul, n, v.NaddMul.Apply(x, y), z),
						// Both sides now unfold to dest_nadd(x, dest_nadd(y, dest_nadd(z, n))).
						CnfRefute(),
					)
				})

			// goal: the pointwise defect from lemma1 is zero, so B := 0 witnesses
			// the slope-equivalence bound; nat_monus.DistRefl + ZeroLessEq discharge 0 ≤ 0
			// without touching arith.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(
						StripQuant(), // fix the slopes x₀, y₀, z₀
						// Unfold nadd_eq: ⊢ ∃B.∀n. nat_dist(LHS(n), RHS(n)) ≤ B.
						Unfold(NaddEqDef),
						// The defect is identically zero, so B := 0 bounds it.
						Witness(ctx.Numeral(0)),
						StripQuant(), // fix the evaluation point n₀
						// lemma1 at (x₀, y₀, z₀, n₀) equates the two dests.
						Cite(lemma1, x_0, y_0, z_0, n_0),
						// Residual: nat_dist(t, t) ≤ 0. The t here is the goal's own LEFT
						// dest, dest_nadd(x₀ * (y₀ * z₀), n₀) — the triple composition
						// x₀(y₀(z₀(n₀))) is lemma1's internal waypoint and is not
						// visible at this leaf, where all lemma1 contributes is that
						// the two dests are equal. nat_monus.DistRefl at that t gives
						// nat_dist((t, t)) = 0; nat_order.ZeroLessEq at 0 gives 0 ≤ 0.
						Cite(nat_monus.DistRefl, v.at(v.NaddMul.Apply(x_0, v.NaddMul.Apply(y_0, z_0)), n_0)),
						Cite(nat_order.ZeroLessEq, ctx.Numeral(0)),
						CnfRefute(),
					)
				})
		}),
})}

// MulLeftId — nadd_of_num(1) · x is equivalent to x:
//
//	⊢ ∀x : nadd. nadd_eq((nadd_of_num(1) * x), x)
//
// Slope multiplication is function composition and OfNum(1) is the
// identity function on ℕ. Read pointwise at each n:
//
//	dest_nadd((nadd_of_num(1) * x), n)
//	 = dest_nadd(nadd_of_num(1), dest_nadd(x, n)) -- Mul
//	 = 1 · dest_nadd(x, n) -- OfNum
//	 = dest_nadd(x, n) -- nat_arith.MulClauses (n = 1·n)
//
// so the defect vanishes identically and B := 0 witnesses the
// slope-equivalence bound. Two sections:
//
// - lemma1: the pointwise equation — one close from three facts (Mul,
// OfNum, nat_arith.MulClauses) chaining the three-equation rewrite.
// - goal: unfold nadd_eq, witness 0, cite lemma1 (its install-time
// eqSimplify rewrites both sides of the pointwise dist to the
// same term), and close the 0-distance residual with
// nat_monus.DistRefl and nat_order.ZeroLessEq — arith-free, this member
// declaring no capabilities.
//
// No transport of the ℕ identity through mk_nadd/dest_nadd is needed:
// the pointwise defect is already zero once one direct nat_arith.MulClauses
// cite grounds the ℕ side.
var MulLeftId = mulLeftIdThm{family.Add(registry.ProofEntry{
	Name: "MulLeftId",
	Key:  "prop_cf3c0698b2fe7b7",
	// The proof is two sections written as a linear script: `lemma1` is a Go
	// local the goal cites by closure capture.
	Build: family.Sections(
		"∀x:nadd. nadd_eq(nadd_of_num(1) * x, x)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			one := ctx.Numeral(1) // argument of nadd_of_num and the multiplier we erase

			// x₀ — the outer ∀x; n₀ — the point (lemma1) / the evaluation
			// point at which the pointwise defect is measured (goal).
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			n_0 := ctx.Var("n_0", NumType)

			// lemma1: x : nadd, n : num
			//
			//	⊢ dest_nadd((nadd_of_num(1) * x), n) = dest_nadd(x, n)
			//
			// The pointwise erasure of the leading `1·`. Mul rewrites the
			// composition to a nested dest_nadd(nadd_of_num(1), dest_nadd(x, n));
			// OfNum at (1, dest_nadd(x, n)) turns dest_nadd(nadd_of_num(1), ·)
			// into `1 · ·`; nat_arith.MulClauses contributes `n = 1 · n` which erases
			// the leading `1·` from both sides propositionally.
			//
			// The binders peel to Skolems (x_0, n_0), so the three facts
			// below are ground instances.
			lemma1 := ctx.Lemma("∀x:nadd. ∀n:num. dest_nadd(nadd_of_num(1) * x, n) = dest_nadd(x, n)",
				func(a *Argument) {
					a.Do(StripQuant())
					a.Show(
						"the leading 1· erases pointwise: Mul opens the composition, OfNum "+
							"reads nadd_of_num(1) at a point as 1·(that point), and 1·n = n",
						By(
							Normalized,
							At(Mul, n_0, v.NaddOfNum.Apply(one), x_0),
							At(OfNum, one, v.at(x_0, n_0)),
							nat_arith.MulClauses))
				})

			// goal: the pointwise defect from lemma1 is zero, so B := 0 witnesses
			// the slope-equivalence bound; nat_monus.DistRefl + ZeroLessEq discharge 0 ≤ 0.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(
						StripQuant(), // fix the slope x₀
						// Unfold nadd_eq: ⊢ ∃B.∀n. nat_dist(LHS(n), RHS(n)) ≤ B.
						Unfold(NaddEqDef),
						// The defect is identically zero, so B := 0 bounds it.
						Witness(ctx.Numeral(0)),
						StripQuant(), // fix the evaluation point n₀
						// lemma1's dest equation ∀x n. dest_nadd((nadd_of_num(1) * x), n)
						// = dest_nadd(x, n) — installed as a ∀-hyp, its install-time
						// eqSimplify rewrites both sides of the pointwise dist to
						// dest_nadd(x₀, n₀), leaving nat_dist(t, t) ≤ 0 as the residual.
						Cite(lemma1),
						// nat_monus.DistRefl rewrites the LHS to 0; nat_order.ZeroLessEq
						// closes 0 ≤ 0.
						Cite(nat_monus.DistRefl),
						Cite(nat_order.ZeroLessEq),
					)
				})
		}),
})}

// LeftDistrib — left distributivity of slope multiplication over
// slope addition, up to slope equivalence:
//
//	⊢ ∀x y z : nadd. nadd_eq(x · (y + z), (x · y) + (x · z))
//
// (writing x(n) for dest_nadd(x, n) and · , + for nadd_mul, nadd_add.)
// Multiplication is composition:
//
//	(x · y)(n) = x(y(n)) [Mul]
//	(x · (y+z))(n) = x((y+z)(n)) = x(y(n) + z(n)) [Mul + Add]
//	((x·y)+(x·z))(n) = (x·y)(n) + (x·z)(n)
//	 = x(y(n)) + x(z(n)) [Add + Mul·2]
//
// so at every n the defect is
//
//	nat_dist( x(y(n)+z(n)) , x(y(n)) + x(z(n)) )
//
// — an additivity defect of x at the point (y(n), z(n)). additive
// bounds it uniformly by B_x, so B_x is itself the ∃B witness for the
// whole slope equivalence. The proof unfolds nadd_eq to expose the
// ∃B.∀n form, takes B_x from additive, grounds the additivity bound
// at (y(n), z(n)), then five ground rewrites (Mul at each of
// the three composed products, Add at each of the two sums)
// normalize the two sides to the shape the bounded hyp closes.
//
// One section; the composition-plus-additive argument surfaces
// through the ground-cite + arith close.
var LeftDistrib = leftDistribThm{family.Add(registry.ProofEntry{
	Name: "LeftDistrib",
	Key:  "prop_a69e99cf3d5df6aa",
	// Unfold nadd_eq to the ∃B.∀n form, take B_x from additive, ground
	// the additivity bound at (y(n), z(n)), then rewrite the two sides
	// to the shape that hyp closes.
	Build: family.Theorem("∀x y z:nadd. nadd_eq(x * (y + z), x * y + x * z)",
		func(a *Argument, x, y, z Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			// n₀ the point of evaluation.
			n0 := ctx.Var("n_0", NumType)

			a.Do(Unfold(NaddEqDef)) // unfold to ∃B.∀n. nat_dist(...) ≤ B

			// Take the additivity bound of x₀ (uniform in m, n):
			// nat_dist(x₀(m+n), x₀(m) + x₀(n)) ≤ B₀ — B₀ the additive constant of x₀.
			B0, additiveX := a.Unpack(At(additive, x))

			a.Do(
				Witness(B0),  // B_x IS the ∃B witness for the whole equivalence
				StripQuant(), // fix the evaluation point n₀
				ByArith(
					// The additivity bound at (y₀(n₀), z₀(n₀)) IS the defect of
					// x at that point:
					// nat_dist(x₀(y₀(n₀) + z₀(n₀)), x₀(y₀(n₀)) + x₀(z₀(n₀))) ≤ B₀.
					additiveX.At(v.at(y, n0), v.at(z, n0)),
					// Five ground equations — Mul at each of the three composed
					// products, Add at each of the two sums — normalize both
					// sides of the goal to the same shape as the additivity
					// bound:
					//
					// (x·(y+z))(n₀) = x₀(dest_nadd((y₀ + z₀), n₀))
					// = x₀(y₀(n₀) + z₀(n₀))
					// ((x·y)+(x·z))(n₀) = (x·y)(n₀) + (x·z)(n₀)
					// = x₀(y₀(n₀)) + x₀(z₀(n₀))
					At(Mul, n0, x, v.NaddAdd.Apply(y, z)),
					At(Mul, n0, x, y),
					At(Mul, n0, x, z),
					At(Add, n0, y, z),
					At(Add, n0, v.NaddMul.Apply(x, y), v.NaddMul.Apply(x, z))),
			)
		}),
})}

// RightDistrib — right distributivity of slope multiplication over
// slope addition, up to slope equivalence:
//
//	⊢ ∀x y z : nadd. nadd_eq((x + y) · z, (x · z) + (y · z))
//
// (writing · for nadd_mul, + for nadd_add.) One chain, conjugating
// LeftDistrib by MulSym:
//
//	(x + y)·z ≈ z·(x + y) ≈ (z·x) + (z·y) ≈ (x·z) + (y·z)
//
// The chain is entirely inside slope equivalence — no numerical
// estimate, no ℕ-arithmetic.
var RightDistrib = rightDistribThm{family.Add(registry.ProofEntry{
	Name: "RightDistrib",
	Key:  "prop_2100952f581e6e17",
	Build: family.Theorem("∀x y z:nadd. nadd_eq((x + y) * z, x * z + y * z)",
		func(a *Argument, x, y, z Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			mul := func(p, q Term) Term { return v.NaddMul.Apply(p, q) }
			add := func(p, q Term) Term { return v.NaddAdd.Apply(p, q) }
			// The chain's four terms, plus the four products the last leg swaps.
			xPlusY := add(x, y)
			lhs := mul(xPlusY, z)     // (x + y)·z
			flipped := mul(z, xPlusY) // z·(x + y)
			zx, zy := mul(z, x), mul(z, y)
			xz, yz := mul(x, z), mul(y, z)
			distributed := add(zx, zy) // (z·x) + (z·y)
			rhs := add(xz, yz)         // (x·z) + (y·z)

			a.Do(
				// The chain's endpoint IS the goal, so it closes it.
				CalcOrder{
					Eq:      v.rel(v.NaddEq),
					EqTrans: NaddEqTrans,
				}.Calc(lhs,
					EqLeg(
						flipped,
						"(x+y)·z ≈ z·(x+y) — MulSym, putting the sum where LeftDistrib can see it",
						Cite(MulSym)),
					EqLeg(
						distributed,
						"z·(x+y) ≈ (z·x) + (z·y) — LeftDistrib",
						Cite(LeftDistrib)),
					EqLeg(
						rhs,
						"(z·x) + (z·y) ≈ (x·z) + (y·z) — AddWellDef pinned at the "+
							"four products, premises MulSym at (z₀, x₀) and (z₀, y₀)",
						By(At(MulSym, z, x), At(MulSym, z, y), At(AddWellDef, zx, xz, zy, yz))),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The chapter's hard analytic core
// ---------------------------------------------------------------------------
//
// rinv(x)(n) = ⌊n²/x(n)⌋ is the pointwise reciprocal, and the file proves,
// in order: the division-error estimate, that rinv is itself a slope (the
// mirror of the toolkit's defining bound, and the theorem the rest rests
// on), the carrier-level operation, the inverse identity behind the field
// axiom, and well-definedness.
//
// README: the "hard analytic core" bullet.

// recipApprox — the eventual reciprocal estimate:
//
//	⊢ ∀x : nadd. ¬nadd_eq(x, nadd_of_num(0))
//	 ⇒ ∃N. ∀n. N ≤ n ⇒ nat_dist(x(n)·rinv(x, n), n·n) ≤ x(n)
//
// For x ≁ 0, nonzero supplies a threshold N₀ beyond which x(n) ≠ 0;
// at those n, the pointwise section (below) gives nat_dist(...) ≤ x(n)
// unconditionally.
//
// Read this bound as the engine of the whole movement: every lemma
// after it scales, cross-multiplies or symmetrizes it, but the raw
// content is one application of nat_div_mod.Division with residue < x(n),
// read through nat_arith.MulSym and nat_monus.DistRightAdd into pair form and
// softened from strict to non-strict by nat_order.LessEqOfLessThan.
var recipApprox = recipApproxThm{family.Add(registry.ProofEntry{
	Name: "recipApprox",
	Key:  "prop_8c1fc3f5342772f2",
	// The proof is two sections written as a linear script: `pointwise` is a
	// Go local the goal cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x:nadd.",
			Hypotheses: []string{
				"¬nadd_eq(x, nadd_of_num(0))",
			},
			Conclusion: "∃N:num. ∀n:num. " +
				"    N ≤ n ⇒ dist((dest_nadd(x, n) * nadd_rinv(x, n), n * n)) ≤ dest_nadd(x, n)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// The goal section's Skolem variables.
			ctx.Var("x_0", MakeType("nadd"))
			N_0 := ctx.Var("N_0", NumType)
			n_0 := ctx.Var("n_0", NumType)

			// Local const declarations for the natural-number division machinery
			// — Const is idempotent, and nat_div/nat_mod only appear in the pointwise
			// section.
			DIV := ctx.Const("nat_div", MakeFun(NumType, MakeFun(NumType, NumType)))
			MOD := ctx.Const("nat_mod", MakeFun(NumType, MakeFun(NumType, NumType)))

			// pointwise — nadd_rinv unfolds to λn. nat_div(n·n, x(n)); nat_div_mod.Division at
			// (x(n), n·n) supplies the residue equation with
			// r = nat_mod(n·n, x(n)) < x(n); nat_arith.MulSym commutes x(n) with nat_div;
			// nat_monus.DistRightAdd renames the residue as nat_dist(quot·x(n), quot·x(n) + r);
			// nat_order.LessEqOfLessThan weakens strict to non-strict. The
			// residual is then propositional over one abbreviation: the multiple
			// quot·x(n) — the largest multiple of x(n) at or below n², the side
			// of the residue equation both the estimate and DistRAdd0 speak
			// about. The `_ Fact` binds the premise, which the closing refute
			// reads off the hypotheses.
			pointwise := ctx.Lemma(Statement{
				Binders: "∀x:nadd. ∀n:num.",
				Hypotheses: []string{
					"dest_nadd(x, n) ≠ 0",
				},
				Conclusion: "dist((dest_nadd(x, n) * nadd_rinv(x, n), n * n)) ≤ dest_nadd(x, n)",
			},
				func(a *Argument, x, n Term, _ Fact) {
					xn := v.at(x, n)
					nn := v.mul(n, n)
					quot := DIV.Apply(nn, xn)
					rem := MOD.Apply(nn, xn)
					a.Do(
						Unfold(naddRinvDef),
						Cite(nat_div_mod.Division, nn, xn),
						Cite(nat_arith.MulSym, xn, quot),
						Cite(nat_monus.DistRightAdd, v.mul(quot, xn), rem),
						Cite(nat_order.LessEqOfLessThan, rem, xn),
						Basic(),
						DenoteTerm("multiple", v.mul(quot, xn)),
						Basic(),
					)
				})

			// goal: assume x₀ ≁ 0 and read the threshold N₀ off nonzero — the
			// same N₀ witnesses the goal. At an index n₀ past it, nonzero's ground
			// body gives x₀(n₀) ≠ 0, which is exactly the pointwise section's
			// hypothesis.
			return ctx.Theorem(headline,
				// The trailing Fact is the ⇒'s assumption x₀ ≁ 0.
				func(a *Argument, x Term, xNotZero Fact) {
					// nonzero is stated under x ≁ 0; the assumption, listed with
					// its instance, discharges that guard, and Unpack Skolemizes
					// its threshold as N₀.
					_, nonzeroBody := a.Unpack(GroupPremises(xNotZero, At(nonzero, x)))

					a.Do(
						Witness(N_0), // the same N₀ witnesses the goal
						StripQuant(), // fix the arbitrary index n₀
					)
					past := a.Assume() // it is past the threshold: N₀ ≤ n₀
					a.Do(
						// Ground nonzero's ∀n body at n₀ — the assumption N₀ ≤ n₀
						// discharges its threshold guard, leaving x₀(n₀) ≠ 0
						// resident — and drop the spent source.
						GroupPremises(past, nonzeroBody.At(n_0)),
						Clear(nonzeroBody),

						// x₀(n₀) ≠ 0: the pointwise section at (x₀, n₀) — its
						// premise is resident, and its conclusion is the goal.
						Cite(pointwise, x, n_0),
					)
				})
		}),
})}

// recipCauchy — the reciprocal is a slope:
//
//	⊢ ∀x : nadd. ¬nadd_eq(x, nadd_of_num(0))
//	 ⇒ ∃B. ∀m n. nat_dist(m·rinv(x, n), n·rinv(x, m)) ≤ B·(m+n)
//
// The mirror of the toolkit's Cauchy axiom one level up: Cauchy says
// every slope's underlying function has bounded defect; recipCauchy
// says the pointwise reciprocal of a nonzero slope does too. It is
// the central analytic theorem of the inverse movement — what
// legitimizes mk_nadd(rinv x) as the inverse construction — and the
// proof has the standard two-leg shape of a Cauchy estimate:
//
// - LARGE indices (both m, n past a threshold): cross-multiply the
// reciprocal defect by x(m)·x(n), reduce it via the triangle
// inequality to the division-error estimate (recipApprox) and x's
// own Cauchy defect, then cancel the x-factors with lowerBound
// and the m·n factor with nat_order.LessEqMulCancel.
// - SMALL indices (m under the threshold): both reciprocal values
// are affinely bounded via the reciprocal's linear growth
// (recipGrowthBound), so the defect is crudely affine in n.
//
// nat_order.BoundsNotZero stitches the legs: an affine bound A·(m+n) + B
// together with vanishing at the origin upgrades to the purely
// linear B'·(m+n) the statement demands.
var recipCauchy = recipCauchyThm{family.Add(registry.ProofEntry{
	Name: "recipCauchy",
	Key:  "prop_9f97311d99cee71a",
	// The proof is five sections written as a linear script: each estimate
	// is a Go local the next section cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x:nadd.",
			Hypotheses: []string{
				"¬nadd_eq(x, nadd_of_num(0))",
			},
			Conclusion: "∃B:num. ∀m n:num. dist((m * nadd_rinv(x, n), n * nadd_rinv(x, m))) ≤ B * (m + n)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// The ×-rearrangement kit: every "same factors, regrouped" step
			// below is one `mulAC.Eq(lhs, rhs)` premise, derived from its own
			// endpoints rather than restated as a claim.
			mulAC := nat_arith.MulAC(ctx)

			// The cross defect's λ-binders, for the goal's BoundsNotZero cite.
			m := ctx.Var("m", NumType)
			n := ctx.Var("n", NumType)

			// Skolem names minted by the strips, in first-appearance order:
			// B₀/N₀ from the first ∃∃ each section meets, then A₀/B₁/N₁/C₀
			// as the later cites arrive.
			A_0 := ctx.Var("A_0", NumType)
			B_0 := ctx.Var("B_0", NumType)
			B_1 := ctx.Var("B_1", NumType)
			C_0 := ctx.Var("C_0", NumType)
			N_0 := ctx.Var("N_0", NumType)
			N_1 := ctx.Var("N_1", NumType)
			m_0 := ctx.Var("m_0", NumType)
			n_0 := ctx.Var("n_0", NumType)

			// The reciprocal defect of x at (i, j): nat_dist(i·rinv(x, j), j·rinv(x, i)).
			defect := func(x, i, j Term) Term {
				return v.d(v.mul(i, v.NaddRinv.Apply(x, j)), v.mul(j, v.NaddRinv.Apply(x, i)))
			}

			// ---- triangle ---------------------------------------------------
			// RA-bound at m ⇒ RA-bound at n ⇒ x(m)·x(n)·defect(m,n) ≤ mn·nat_dist(m·x(n), n·x(m)) + x(m)·x(n)·(m+n)
			//
			// The cross-multiplied reduction: scaling the two division-error
			// estimates by m·x(m) and n·x(n), rewriting each through
			// nat_monus.DistLeftMul, and joining them with the two-sided triangle
			// inequality (nat_monus.DistTrianglesLessEq) bounds the x(m)·x(n)-scaled
			// reciprocal defect by x's own defect (scaled by mn) plus the
			// accumulated error x(m)·x(n)·(m+n). Every step below either scales
			// an inequality by a common left factor (nat_order.LessEqMulMono),
			// renames a product through nat_monus.DistLeftMul, or regroups the same
			// factors (the AC kit).
			triangle := ctx.Lemma("∀x:nadd. ∀m n:num. "+
				"    dist((dest_nadd(x, m) * nadd_rinv(x, m), m * m)) ≤ dest_nadd(x, m) ⇒ "+
				"    dist((dest_nadd(x, n) * nadd_rinv(x, n), n * n)) ≤ dest_nadd(x, n) ⇒ "+
				"    dest_nadd(x, m) * dest_nadd(x, n) * dist((m * nadd_rinv(x, n), n * nadd_rinv(x, m))) ≤ "+
				"    m * n * dist((m * dest_nadd(x, n), n * dest_nadd(x, m))) + "+
				"    dest_nadd(x, m) * dest_nadd(x, n) * (m + n)",
				// The two premises are the division-error estimates at m and at n.
				func(a *Argument, x, m, n Term, estM, estN Fact) {
					triXm, triXn := v.at(x, m), v.at(x, n)
					triRn := v.NaddRinv.Apply(x, n) // rinv(x, n)
					triRm := v.NaddRinv.Apply(x, m)
					triMxm := v.mul(m, triXm) // m·x(m) — the scale factor for the n-side estimate
					triNxn := v.mul(n, triXn)
					triXx := v.mul(triXm, triXn)                      // x(m)·x(n)
					triMn := v.mul(m, n)                              // m·n
					triMpn := v.sum(m, n)                             // m+n
					triDistN := v.d(v.mul(triXn, triRn), v.mul(n, n)) // the RA estimate's dist at n
					triDistM := v.d(v.mul(triXm, triRm), v.mul(m, m))
					// The triangle's three chords, written with the scale factor outside.
					triA1 := v.mul(triMxm, v.mul(triXn, triRn)) // (m·x(m))·(x(n)·rinv(x,n))
					triB1 := v.mul(triMxm, v.mul(n, n))
					triA2 := v.mul(triNxn, v.mul(triXm, triRm))
					triB2 := v.mul(triNxn, v.mul(m, m))
					triD := defect(x, m, n)
					triDistX := v.d(v.mul(m, triXn), v.mul(n, triXm)) // x's own defect at (m, n), goal orientation
					// …and in nat_monus.DistLeftMul's native orientation
					triDistXE4 := v.d(v.mul(n, triXm), v.mul(m, triXn))

					// Scale each division-error estimate by the opposite side's factor.
					scaledN := a.Have(
						"the n-side estimate scaled by m·x(m)",
						MakeProp(v.le(v.mul(triMxm, triDistN), v.mul(triMxm, triXn))),
						By(estN, At(nat_order.LessEqMulMono, triMxm, triDistN, triXn)))
					scaledM := a.Have(
						"the m-side estimate scaled by n·x(n)",
						MakeProp(v.le(v.mul(triNxn, triDistM), v.mul(triNxn, triXm))),
						By(estM, At(nat_order.LessEqMulMono, triNxn, triDistM, triXm)))
					// Push the scale factors inside the distances.
					chordN := a.Have(
						"scaled n-side estimate in chord form",
						MakeProp(v.le(v.d(triA1, triB1), v.mul(triMxm, triXn))),
						By(scaledN, nat_monus.DistLeftMul))
					chordM := a.Have(
						"scaled m-side estimate in chord form",
						MakeProp(v.le(v.d(triA2, triB2), v.mul(triNxn, triXm))),
						By(scaledM, nat_monus.DistLeftMul))
					// The two-sided triangle inequality joins the chords.
					joined := a.Have(
						"triangle: dist(a₁, a₂) ≤ dist(b₁, b₂) + accumulated error",
						MakeProp(v.le(
							v.d(triA1, triA2), v.sum(v.d(triB1, triB2), v.sum(v.mul(triMxm, triXn), v.mul(triNxn, triXm))))),
						By(
							chordN,
							chordM,
							At(
								nat_monus.DistTrianglesLessEq,
								triA1,
								triB1,
								triA2,
								triB2,
								v.mul(triMxm, triXn),
								v.mul(triNxn, triXm))))
					// Both chords carry the same factors as the goal's; only the
					// grouping differs, so each endpoint is one AC rearrangement.
					leftEnd1 := mulAC.Eq(triA1, v.mul(triXx, v.mul(m, triRn)))
					leftEnd2 := mulAC.Eq(triA2, v.mul(triXx, v.mul(n, triRm)))
					leftChord := a.Have(
						"the left chord is the x(m)·x(n)-scaled reciprocal defect",
						MakeProp(v.le(
							v.mul(triXx, triD), v.sum(v.d(triB1, triB2), v.sum(v.mul(triMxm, triXn), v.mul(triNxn, triXm))))),
						By(joined, leftEnd1, leftEnd2, At(nat_monus.DistLeftMul, triXx, v.mul(m, triRn), v.mul(n, triRm))))
					rightEnd1 := mulAC.Eq(triB1, v.mul(triMn, v.mul(n, triXm)))
					rightEnd2 := mulAC.Eq(triB2, v.mul(triMn, v.mul(m, triXn)))
					rightChord := a.Have(
						"the right chord is m·n times x's defect",
						MakeProp(v.d(triB1, triB2).Eq(v.mul(triMn, triDistXE4))),
						By(rightEnd1, rightEnd2, At(nat_monus.DistLeftMul, triMn, v.mul(n, triXm), v.mul(m, triXn))))
					// dist is symmetric in its pair — one nat_monus.DistSym instance
					// under the m·n factor.
					orient := a.Have(
						"x's defect read in the goal's orientation",
						MakeProp(v.mul(triMn, triDistXE4).Eq(v.mul(triMn, triDistX))),
						By(nat_monus.DistSym))
					// Not an AC rearrangement — the two summands share x(m)·x(n)
					// and the step is the distributive law.
					regroup := a.Have(
						"the accumulated error regroups as x(m)·x(n)·(m+n)",
						MakeProp(v.sum(v.mul(triMxm, triXn), v.mul(triNxn, triXm)).Eq(v.mul(triXx, triMpn))),
						ByArith())
					a.Show(
						"assemble: x(m)·x(n)·defect ≤ mn·dist(m·x(n), n·x(m)) + x(m)·x(n)·(m+n)",
						By(leftChord, rightChord, orient, regroup))
				})

			// ---- crossBound -------------------------------------------------
			// x ≁ 0 ⇒ ∃B N. ∀m n ≥ N. x(m)·x(n)·defect(m,n) ≤ B·(mn·(m+n))
			//
			// The triangle reduction becomes an eventual bound: recipApprox
			// supplies the threshold N₀ past which its estimates hold, Cauchy
			// bounds x's own defect by B₀·(m+n), and upperBound bounds each
			// x-value by B₁·(index) past N₁. Witnesses: B := B₀ + B₁², N := N₀+N₁.
			cbMn := v.mul(m_0, n_0)
			cbMpn := v.sum(m_0, n_0)
			cbBigB := v.sum(B_0, v.mul(B_1, B_1))                // the witness B₀ + B₁²
			cbLinProd := v.mul(v.mul(B_1, m_0), v.mul(B_1, n_0)) // (B₁m₀)·(B₁n₀)

			crossBound := ctx.Lemma(Statement{
				Binders: "∀x:nadd.",
				Hypotheses: []string{
					"¬nadd_eq(x, nadd_of_num(0))",
				},
				Conclusion: "∃B N:num. ∀m n:num. " +
					"    N ≤ m ∧ N ≤ n ⇒ " +
					"    dest_nadd(x, m) * dest_nadd(x, n) * dist((m * nadd_rinv(x, n), n * nadd_rinv(x, m))) ≤ " +
					"    B * (m * n * (m + n))",
			},
				func(a *Argument, x Term, nonzero Fact) {
					cbXm, cbXn := v.at(x, m_0), v.at(x, n_0)
					cbXx := v.mul(cbXm, cbXn)
					cbD := defect(x, m_0, n_0)
					cbDistX := v.d(v.mul(m_0, cbXn), v.mul(n_0, cbXm))
					cbDistRAn := v.d(v.mul(cbXn, v.NaddRinv.Apply(x, n_0)), v.mul(n_0, n_0))
					cbDistRAm := v.d(v.mul(cbXm, v.NaddRinv.Apply(x, m_0)), v.mul(m_0, m_0))

					// The three eventual estimates at x, Skolemized in cite order:
					// Cauchy → B₀, recipApprox → N₀, upperBound → B₁/N₁.
					// recipApprox's x ~ 0 disjunct rides along; the ¬nadd_eq
					// hypothesis settles it at each use below.
					_, cauchyBody := a.Unpack(At(Cauchy, x))
					_, raBody := a.Unpack(GroupPremises(nonzero, At(recipApprox, x)))
					_, _, ubBody := a.Unpack2(At(upperBound, x))

					a.Do(
						Witness(cbBigB),
						Witness(v.sum(N_0, N_1)),
						StripQuant(),
						StripImp(),
						Derive(func(b *Argument) {
							aboveN := b.Hyp(MakeProp(v.le(v.sum(N_0, N_1), m_0).And(v.le(v.sum(N_0, N_1), n_0))))
							thresholds := b.Have(
								"the combined threshold covers each component threshold",
								MakeProp(v.le(N_0, m_0).And(v.le(N_0, n_0)).And(v.le(N_1, m_0)).And(v.le(N_1, n_0))),
								ByArith(aboveN))
							estAtM := b.Have(
								"the division-error estimate holds at m₀",
								MakeProp(v.le(cbDistRAm, cbXm)),
								By(thresholds, nonzero, raBody.At(m_0)))
							estAtN := b.Have(
								"…and at n₀",
								MakeProp(v.le(cbDistRAn, cbXn)),
								By(thresholds, nonzero, raBody.At(n_0)))
							linBounds := b.Have(
								"x's values are linearly bounded at both indices",
								MakeProp(v.le(cbXm, v.mul(B_1, m_0)).And(v.le(cbXn, v.mul(B_1, n_0)))),
								By(thresholds, ubBody.At(m_0), ubBody.At(n_0)))
							triAt := b.Have(
								"the triangle reduction instantiates at (m₀, n₀)",
								MakeProp(v.le(v.mul(cbXx, cbD), v.sum(v.mul(cbMn, cbDistX), v.mul(cbXx, cbMpn)))),
								By(estAtM, estAtN, At(triangle, x, m_0, n_0)))
							// Bound the two summands: Cauchy handles the defect term,
							// the linear bounds handle the error term. The defect term
							// is scaled by the common LEFT factor m₀·n₀, the error term
							// by the common RIGHT factor m₀+n₀.
							defectBound := b.Have(
								"the defect summand is at most mn·(B₀·(m₀+n₀))",
								MakeProp(v.le(v.mul(cbMn, cbDistX), v.mul(cbMn, v.mul(B_0, cbMpn)))),
								By(cauchyBody.At(m_0, n_0), At(nat_order.LessEqMulMono, cbMn, cbDistX, v.mul(B_0, cbMpn))))
							prodBound := b.Have(
								"the product x(m₀)·x(n₀) is at most (B₁m₀)·(B₁n₀)",
								MakeProp(v.le(cbXx, cbLinProd)),
								By(linBounds, At(nat_order.LessEqMul2, cbXm, v.mul(B_1, m_0), cbXn, v.mul(B_1, n_0))))
							errorBound := b.Have(
								"so the error summand is at most (B₁m₀)·(B₁n₀)·(m₀+n₀)",
								MakeProp(v.le(v.mul(cbXx, cbMpn), v.mul(cbLinProd, cbMpn))),
								By(prodBound, nat_order.LessEqMulRightCancel))
							witnessEq := b.Have(
								"the two bounds sum to the witness: (B₀+B₁²)·(mn·(m+n))",
								MakeProp(v.mul(cbBigB, v.mul(cbMn, cbMpn)).Eq(
									v.sum(v.mul(cbMn, v.mul(B_0, cbMpn)), v.mul(cbLinProd, cbMpn)))),
								ByArith())
							b.Show(
								"chain the three inequalities through the ring identity",
								ByArith(triAt, defectBound, errorBound, witnessEq))
						}),
					)
				})

			// ---- largeIndex -------------------------------------------------
			// x ≁ 0 ⇒ ∃B N. ∀m n ≥ N. defect(m,n) ≤ B·(m+n)
			//
			// Cancellation: lowerBound turns each index into at most A₀·x(index),
			// so m·n ≤ A₀²·x(m)·x(n); scaling the crossBound estimate by A₀² and
			// cancelling the now-common m·n factor (nonzero since the threshold
			// forces m, n ≥ 1) leaves the purely linear bound with B := A₀²·B₀.
			liAA := v.mul(A_0, A_0)
			liOne := ctx.Numeral(1)
			liBigB := v.mul(liAA, B_0) // the witness A₀²·B₀

			largeIndex := ctx.Lemma(Statement{
				Binders: "∀x:nadd.",
				Hypotheses: []string{
					"¬nadd_eq(x, nadd_of_num(0))",
				},
				Conclusion: "∃B N:num. ∀m n:num. " +
					"    N ≤ m ∧ N ≤ n ⇒ dist((m * nadd_rinv(x, n), n * nadd_rinv(x, m))) ≤ B * (m + n)",
			},
				func(a *Argument, x Term, nonzero Fact) {
					cbXm, cbXn := v.at(x, m_0), v.at(x, n_0)
					cbXx := v.mul(cbXm, cbXn)
					cbD := defect(x, m_0, n_0)

					// crossBound's eventual bound at x — its premise is ours —
					// Skolemized at B₀, N₀.
					_, _, cbBody := a.Unpack2(GroupPremises(nonzero, At(crossBound, x)))
					// lowerBound's x ~ 0 disjunct rides along; the ¬nadd_eq
					// hypothesis settles it below. Unpack2 Skolemizes A₀, N₁.
					_, _, lbBody := a.Unpack2(GroupPremises(nonzero, At(lowerBound, x)))
					a.Do(
						Witness(liBigB),
						Witness(v.sum(v.sum(N_0, N_1), liOne)),
						StripQuant(),
						StripImp(),
						Derive(func(b *Argument) {
							aboveN := b.Hyp(
								MakeProp(v.le(v.sum(v.sum(N_0, N_1), liOne), m_0).And(v.le(v.sum(v.sum(N_0, N_1), liOne), n_0))))
							thresholds := b.Have(
								"the padded threshold covers each component and keeps both indices positive",
								MakeProp(v.le(N_0, m_0).And(v.le(N_0, n_0)).And(v.le(N_1, m_0)).And(v.le(N_1, n_0)).And(
									v.le(liOne, m_0)).And(
									v.le(liOne, n_0))),
								ByArith(aboveN))
							crossAt := b.Have(
								"the cross-multiplied bound holds at (m₀, n₀)",
								MakeProp(v.le(v.mul(cbXx, cbD), v.mul(B_0, v.mul(cbMn, cbMpn)))),
								By(thresholds, cbBody.At(m_0, n_0)))
							domIdx := b.Have(
								"each index is dominated by A₀ times its x-value",
								MakeProp(v.le(m_0, v.mul(A_0, cbXm)).And(v.le(n_0, v.mul(A_0, cbXn)))),
								By(thresholds, nonzero, lbBody.At(m_0), lbBody.At(n_0)))
							prodDom := b.Have(
								"so m₀·n₀ ≤ (A₀·x(m₀))·(A₀·x(n₀))",
								MakeProp(v.le(cbMn, v.mul(v.mul(A_0, cbXm), v.mul(A_0, cbXn)))),
								By(domIdx, At(nat_order.LessEqMul2, m_0, v.mul(A_0, cbXm), n_0, v.mul(A_0, cbXn))))
							// …which is the same four factors grouped around A₀².
							regroupAA := mulAC.Eq(v.mul(v.mul(A_0, cbXm), v.mul(A_0, cbXn)), v.mul(liAA, cbXx))
							mnBound := b.Have(
								"hence m₀·n₀ ≤ A₀²·(x(m₀)·x(n₀))",
								MakeProp(v.le(cbMn, v.mul(liAA, cbXx))),
								By(prodDom, regroupAA))
							// The defect scales as the common RIGHT factor…
							scaledD := b.Have(
								"scale the defect: mn·defect ≤ (A₀²·x(m₀)·x(n₀))·defect",
								MakeProp(v.le(v.mul(cbMn, cbD), v.mul(v.mul(liAA, cbXx), cbD))),
								By(mnBound, nat_order.LessEqMulRightCancel))
							regroupD := mulAC.Eq(v.mul(v.mul(liAA, cbXx), cbD), v.mul(liAA, v.mul(cbXx, cbD)))
							// …and A₀² as the common LEFT factor.
							scaledCross := b.Have(
								"scale the cross bound by A₀²",
								MakeProp(v.le(v.mul(liAA, v.mul(cbXx, cbD)), v.mul(liAA, v.mul(B_0, v.mul(cbMn, cbMpn))))),
								By(crossAt, At(nat_order.LessEqMulMono, liAA, v.mul(cbXx, cbD), v.mul(B_0, v.mul(cbMn, cbMpn)))))
							// The right-hand side is the same factors with m₀·n₀ outermost.
							regroupOut := mulAC.Eq(
								v.mul(liAA, v.mul(B_0, v.mul(cbMn, cbMpn))), v.mul(cbMn, v.mul(liBigB, cbMpn)))
							chained := b.Have(
								"chain: mn·defect ≤ mn·(A₀²B₀·(m₀+n₀))",
								MakeProp(v.le(v.mul(cbMn, cbD), v.mul(cbMn, v.mul(liBigB, cbMpn)))),
								ByArith(scaledD, regroupD, scaledCross, regroupOut))
							oneOne := b.Have(
								"1·1 ≤ m₀·n₀ — both factors are at least 1",
								MakeProp(v.le(v.mul(liOne, liOne), cbMn)),
								By(thresholds, At(nat_order.LessEqMul2, liOne, m_0, liOne, n_0)))
							mnNonzero := b.Have(
								"so m₀·n₀ is nonzero",
								MakeProp(Not(cbMn.Eq(ctx.Numeral(0)))),
								ByArith(oneOne))
							// nat_order.LessEqMulCancel drops the common m₀·n₀; its
							// degenerate "the factor is zero" disjunct is what
							// mnNonzero is for.
							b.Show(
								"defect ≤ A₀²B₀·(m₀+n₀) — cancel m₀·n₀",
								By(chained, mnNonzero, nat_order.LessEqMulCancel))
						}),
					)
				})

			// ---- smallIndex -------------------------------------------------
			// x ≁ 0 ⇒ ∃A B. ∀m n. m ≤ K ⇒ defect(m,n) ≤ A·n + B
			//
			// For bounded m the defect is crudely affine in n: nat_dist(a, b) ≤ a + b
			// (nat_monus.DistAddBound) splits the defect into m·rinv(x, n) ≤ K·(A₀n + B₀)
			// and n·rinv(x, m) ≤ n·(A₀K + B₀), both via the reciprocal's linear
			// growth. Witnesses: A := K·A₀ + (A₀·K + B₀), B := K·B₀.
			siAffN := v.sum(v.mul(A_0, n_0), B_0) // A₀·n₀ + B₀

			smallIndex := ctx.Lemma(Statement{
				Binders: "∀x:nadd. ∀K:num.",
				Hypotheses: []string{
					"¬nadd_eq(x, nadd_of_num(0))",
				},
				Conclusion: "∃A B:num. ∀m n:num. " +
					"    m ≤ K ⇒ dist((m * nadd_rinv(x, n), n * nadd_rinv(x, m))) ≤ A * n + B",
			},
				func(a *Argument, x, K Term, _ Fact) {
					siRn := v.NaddRinv.Apply(x, n_0)
					siRm := v.NaddRinv.Apply(x, m_0)
					siAffK := v.sum(v.mul(A_0, K), B_0) // A₀·K + B₀

					// The reciprocal's linear growth at x — the chapter's one
					// generated delegate; its x ≁ 0 guard is discharged from
					// the assumption at the cite.
					a.Do(Cite(recipGrowthBound, x))
					// The reciprocal's affine growth bound, Skolemized at A₀, B₀.
					_, _, growthBody := a.Unpack2(a.Hyp("∃A B:num. ∀n:num. nadd_rinv(x, n) ≤ A * n + B"))
					a.Do(
						Witness(v.sum(v.mul(K, A_0), siAffK)),
						Witness(v.mul(K, B_0)),
						StripQuant(),
						StripImp(),
						Derive(func(b *Argument) {
							mUnderK := b.Hyp(MakeProp(v.le(m_0, K)))
							grows := b.Have(
								"the reciprocal grows affinely at both indices",
								MakeProp(v.le(siRn, siAffN).And(v.le(siRm, v.sum(v.mul(A_0, m_0), B_0)))),
								By(growthBody.At(n_0), growthBody.At(m_0)))
							first := b.Have(
								"first summand: m₀·rinv(x, n₀) ≤ K·(A₀n₀ + B₀)",
								MakeProp(v.le(v.mul(m_0, siRn), v.mul(K, siAffN))),
								By(mUnderK, grows, At(nat_order.LessEqMul2, m_0, K, siRn, siAffN)))
							mGrowth := b.Have(
								"A₀·m₀ stays under A₀·K",
								MakeProp(v.le(v.mul(A_0, m_0), v.mul(A_0, K))),
								By(mUnderK, At(nat_order.LessEqMulMono, A_0, m_0, K)))
							capsAtK := b.Have(
								"so the m₀-growth bound caps at the K-growth bound",
								MakeProp(v.le(siRm, siAffK)),
								ByArith(grows, mGrowth))
							second := b.Have(
								"second summand: n₀·rinv(x, m₀) ≤ n₀·(A₀K + B₀)",
								MakeProp(v.le(v.mul(n_0, siRm), v.mul(n_0, siAffK))),
								By(capsAtK, At(nat_order.LessEqMulMono, n_0, siRm, siAffK)))
							totalEq := b.Have(
								"the two summand bounds total the affine witness",
								MakeProp(v.sum(v.mul(v.sum(v.mul(K, A_0), siAffK), n_0), v.mul(K, B_0)).Eq(
									v.sum(v.mul(K, siAffN), v.mul(n_0, siAffK)))),
								ByArith())
							// nat_dist(a, b) ≤ a + b splits the defect.
							b.Show(
								"defect ≤ (K·A₀ + (A₀K+B₀))·n₀ + K·B₀ — sum the split through the identity",
								ByArith(At(nat_monus.DistAddBound, v.mul(m_0, siRn), v.mul(n_0, siRm)), first, second, totalEq))
						}),
					)
				})

			// ---- goal -------------------------------------------------------
			// Combine the legs. Assuming x ≁ 0: largeIndex supplies (B₀, N₀);
			// smallIndex at K := N₀ supplies (A₀, B₁), covering m ≤ N₀ directly
			// and n ≤ N₀ after flipping the defect with nat_monus.DistSym. Together
			// the legs give the affine bound (B₀+A₀)·(m+n) + B₁ at EVERY (m, n);
			// since the defect vanishes at the origin, nat_order.BoundsNotZero
			// upgrades affine to linear, and its constant C₀ is the witness.
			zero := ctx.Numeral(0)
			// The top strips its own ∀x; with the ambient x taken by the
			// estimate sections, the fresh instance is named x₀.
			x0 := ctx.Var("x_0", MakeType("nadd"))
			dAt := func(i, j Term) *TermWrapper {
				return v.d(v.mul(i, v.NaddRinv.Apply(x0, j)), v.mul(j, v.NaddRinv.Apply(x0, i)))
			}
			goalD := dAt(m_0, n_0)
			goalDflip := dAt(n_0, m_0)
			goalMpn := v.sum(m_0, n_0)
			affA := v.sum(B_0, A_0) // the affine slope B₀ + A₀

			// bnzBody keeps a *HypHandle: nat_order.BoundsNotZero is cited at
			// a λ-argument, so its body's text is a β-redex — naming that λ,
			// the cross defect, in the close is what stands in for it.
			bnzBody := NewHypHandle("bnzBody") // nat_order.BoundsNotZero's ∀∀ body

			// The affine claim, ∀-closed over m, n.
			affineProp := ctx.MakePropText(
				"∀m n:num. dist((m * nadd_rinv(x₀, n), n * nadd_rinv(x₀, m))) ≤ (B₀ + A₀) * (m + n) + B₁")

			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(StripQuant())     // fix the slope x₀
					xNonzero := a.Assume() // assume x₀ ≁ 0
					// The large leg at our x — its premise is ours — Skolemized
					// at its bound B₀ and threshold N₀.
					_, _, liBody := a.Unpack2(GroupPremises(xNonzero, At(largeIndex, x0)))
					// The small leg at exactly that threshold: A₀, B₁.
					_, _, siBody := a.Unpack2(GroupPremises(xNonzero, At(smallIndex, x0, N_0)))

					a.Do(
						Suffices(affineProp,
							"vanish at the origin, then linearize via nat_order.BoundsNotZero",
							Derive(func(b *Argument) {
								// A direct nat_monus.DistRefl instance — the exact cite closes it.
								b.Have(
									"the defect vanishes at the origin — both arguments are the same term",
									MakeProp(
										zero.Eq(v.d(v.mul(zero, v.NaddRinv.Apply(x0, zero)), v.mul(zero, v.NaddRinv.Apply(x0, zero))))),
									Cite(nat_monus.DistRefl))
								// The cross defect of the reciprocal estimate as a
								// function of both indices — the object every leg of
								// this proof bounds, and what the close abbreviates
								// once BoundsNotZero has been cited at it.
								crossDefect := m.To(n.To(v.d(
									v.mul(m, v.NaddRinv.Apply(x0, n)),
									v.mul(n, v.NaddRinv.Apply(x0, m)))))

								// nat_order.BoundsNotZero at the defect function: its
								// two guards — the origin value and the affine claim,
								// the Suffices branch's own premise — are in hand, so
								// the cite lands the linearized bound itself; its
								// constant C₀ becomes the witness.
								b.Do(Cite(nat_order.BoundsNotZero, crossDefect, affA, B_1))
								b.Do(bnzBody.From(StripQuant())) // Skolemize the linear constant C₀
								b.Take(C_0)
								b.Do(StripQuant()) // fix the goal's indices m₀, n₀
								b.Do(bnzBody.Ground(m_0, n_0))
								b.Show(
									"β-reduce the linearized bound's λ-applications: it is the goal",
									By(bnzBody))
							})),

						// The affine claim: the defect is affinely bounded at EVERY
						// pair of indices. Both index comparisons split symmetrically —
						// each branch runs a different leg, so they stay explicit.
						StripQuant(),
						Cite(nat_order.LessEqTotal, N_0, m_0),
						Cite(nat_order.LessEqTotal, N_0, n_0),
					)

					caseM := a.Hyp("N₀ ≤ m₀ ∨ m₀ ≤ N₀")
					caseN := a.Hyp("N₀ ≤ n₀ ∨ n₀ ≤ N₀")

					a.Do(
						caseM.SplitDisj(
							LeftHolds(
								"N₀ ≤ m₀ — look at n₀",
								caseN.SplitDisj(
									LeftHolds(
										"N₀ ≤ n₀ too: the large leg applies directly",
										// nAbove is this branch's own disjunct; mAbove
										// came from the outer split on m₀.
										Given(func(b *Argument, nAbove Fact) {
											mAbove := b.Hyp(MakeProp(v.le(N_0, m_0)))
											largeAt := b.Have(
												"the large-leg bound at (m₀, n₀)",
												MakeProp(v.le(goalD, v.mul(B_0, goalMpn))),
												By(mAbove, nAbove, liBody.At(m_0, n_0)))
											slopeOrder := b.Have(
												"B₀ sits under the affine slope B₀ + A₀",
												MakeProp(v.le(B_0, affA)),
												ByArith())
											slopeFits := b.Have(
												"its slope fits under the affine slope — the common factor (m₀+n₀) scales it",
												MakeProp(v.le(v.mul(B_0, goalMpn), v.mul(affA, goalMpn))),
												By(slopeOrder, nat_order.LessEqMulRightCancel))
											b.Show(
												"affine bound in the large case",
												ByArith(largeAt, slopeFits))
										}),
									),
									RightHolds(
										"n₀ ≤ N₀: the small leg applies with the defect flipped",
										Given(func(b *Argument, nUnder Fact) {
											flipBound := b.Have(
												"the small-leg bound at (n₀, m₀) — the flipped defect",
												MakeProp(v.le(goalDflip, v.sum(v.mul(A_0, m_0), B_1))),
												By(nUnder, siBody.At(n_0, m_0)))
											// A direct nat_monus.DistSym instance — the exact cite closes it.
											symm := b.Have(
												"dist is symmetric: the defect equals its flip",
												MakeProp(goalD.Eq(goalDflip)),
												Cite(nat_monus.DistSym))
											dominated := b.Have(
												"A₀ and m₀ are dominated by the affine slope and the sum",
												MakeProp(v.le(A_0, affA).And(v.le(m_0, goalMpn))),
												ByArith())
											absorbs := b.Have(
												"the affine slope absorbs A₀·m₀",
												MakeProp(v.le(v.mul(A_0, m_0), v.mul(affA, goalMpn))),
												By(dominated, At(nat_order.LessEqMul2, A_0, affA, m_0, goalMpn)))
											b.Show(
												"affine bound via the flipped small leg",
												ByArith(flipBound, symm, absorbs))
										}),
									),
								),
							),
							RightHolds(
								"m₀ ≤ N₀: the small leg applies directly",
								Given(func(b *Argument, mUnder Fact) {
									smallAt := b.Have(
										"the small-leg bound at (m₀, n₀)",
										MakeProp(v.le(goalD, v.sum(v.mul(A_0, n_0), B_1))),
										By(mUnder, siBody.At(m_0, n_0)))
									dominated := b.Have(
										"A₀ and n₀ are dominated by the affine slope and the sum",
										MakeProp(v.le(A_0, affA).And(v.le(n_0, goalMpn))),
										ByArith())
									absorbs := b.Have(
										"the affine slope absorbs A₀·n₀",
										MakeProp(v.le(v.mul(A_0, n_0), v.mul(affA, goalMpn))),
										By(dominated, At(nat_order.LessEqMul2, A_0, affA, n_0, goalMpn)))
									b.Show(
										"affine bound in the small case",
										ByArith(smallAt, absorbs))
								}),
							),
						),
					)
				})
		}),
})}

// inv — reading the reciprocal slope pointwise:
//
//	⊢ ∀ẋ x. dest_nadd(nadd_inv(x), ẋ) =
//	 COND(nadd_eq(x, nadd_of_num(0)), λn. 0, nadd_rinv(x), ẋ)
//
// nadd_inv splits on nadd_eq(x, 0): the zero branch stores nadd_of_num(0)
// (whose dest_nadd is λn. 0·n, i.e. λn. 0), the nonzero branch stores
// mk_nadd(nadd_rinv(x)), which reads back as nadd_rinv(x) provided that
// function is a slope. Two ingredients:
//
// - isSlope: for every x, nadd_rinv(x) either satisfies the defining
// near-linearity bound, or x is the zero slope. Unfolding is_nadd
// reveals the ∃B.∀m n.(...) core, and the disjunct-form recipCauchy
// bound matches it directly.
// - goal: cite the mk_nadd typedef membership axiom (dest_nadd ∘ mk_nadd
// fixes any slope), then case-split on nadd_eq(x, 0):
// · true: the constant-zero branch, reading nadd_of_num(0) pointwise
// as 0·ẋ = 0 (OfNum at k=0 plus Mul's 0·n clause).
// · false: isSlope hands is_nadd(nadd_rinv(x)); membership at
// r := nadd_rinv(x) then rewrites the goal to reflexivity.
var inv = invThm{family.Add(registry.ProofEntry{
	Name: "inv",
	Key:  "prop_4de88c1d6b742866",
	// The proof is one lemma plus the assembly, written as a linear script:
	// `isSlope` is a Go local the goal cites by closure capture.
	Build: family.Sections(
		"∀ẋ:num. ∀x:nadd. "+
			"    dest_nadd(nadd_inv(x), ẋ) = COND(nadd_eq(x, nadd_of_num(0)), λn:num. 0, nadd_rinv(x), ẋ)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zero := ctx.Numeral(0)

			// x_0 the slope being inverted; the read-out point ẋ_0 is minted
			// fresh by StripQuant off the goal binder ẋ.
			x_0 := ctx.Var("x_0", MakeType("nadd"))
			xDot_0 := ctx.Var("ẋ_0", NumType)

			membershipThm := naddMembership(ctx)

			// isSlope: unfolding is_nadd exposes the near-linearity core
			// ∃B.∀m n. nat_dist(m·rinv(x,n), n·rinv(x,m)) ≤ B·(m+n); with the
			// trailing disjunct nadd_eq(x, 0), the recipCauchy bound matches
			// shape-for-shape.
			isSlope := ctx.Lemma("∀x:nadd. is_nadd(nadd_rinv(x)) ∨ nadd_eq(x, nadd_of_num(0))",
				func(a *Argument) {
					a.Do(Unfold(IsNaddDef), Cite(recipCauchy))
				})

			// The COND discriminant, in terms of x_0.
			xIsZero := v.NaddEq.Apply(x_0, v.NaddOfNum.Apply(zero))

			// goal: bring in membership, unfold nadd_inv to expose the internal
			// COND on nadd_eq(x, 0), then split on that discriminant. Both COND
			// arms collapse under the same hyp, so each branch closes with the
			// ingredient specific to its side.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(
						UseLemma(membershipThm),
						Given(func(a *Argument, membership Fact) {
							a.Do(
								StripQuant(), // ẋ_0, x_0
								Unfold(NaddInvDef),
								ByCaseStep(xIsZero,
									Case(
										"x ≈ 0 — both COND arms collapse; residual 0·ẋ₀ = "+
											"0 closes via OfNum at (0, ẋ₀) and Mul's 0·n clause",
										Given(func(b *Argument, isZero Fact) {
											b.Show(
												"both COND arms collapse under x ≈ 0 and the residual 0·ẋ₀ = 0 decides",
												By(
													isZero,
													// OfNum ground at k = 0 and the read-out point:
													// 0 · ẋ₀ = dest_nadd(nadd_of_num(0), ẋ₀).
													At(OfNum, zero, xDot_0),
													nat_arith.Mul))
										}),
									),
									Case(
										"x ≁ 0 — COND picks the mk_nadd(nadd_rinv(x)) arm; membership "+
											"at r := nadd_rinv(x) with isSlope collapses dest_nadd ∘ mk_nadd",
										membership.At(v.NaddRinv.Apply(x_0)),
										UseLemma(isSlope.PromisedThm()),
										CnfRefute(),
									),
								),
							)
						}),
					)
				})
		}),
})}

// MulLeftInverse — for every non-zero slope, inv(x)·x is the identity
// slope:
//
//	⊢ ∀x:nadd. ¬nadd_eq(x, nadd_of_num(0))
//	 ⇒ nadd_eq((nadd_inv(x) * x), nadd_of_num(1))
//
// Non-zeroness is what makes nadd_inv meaningful — at x ≈ 0 it
// degenerates via COND. This closes the inverse movement and equips
// the slope monoid with reciprocals for the quotient in nonneg_real. The
// theorem factors through two eventual estimates:
//
//	Section A (scaledReciprocalError) — the pointwise reciprocal error
//	 nat_dist(x(n)·rinv(x,n), n²) is affinely bounded. recipApprox bounds
//	 it by x(n) itself past a threshold N₀; LinearBound pins x(n)
//	 linearly (A₀·n + B₀) everywhere; nat_order.BoundsIgnore trades the
//	 eventuality for a global bound.
//
//	Section B (pointwiseIdentity) — the n-scaled pointwise defect
//	 n·nat_dist((inv(x)·x)(n), 1(n)) is affinely bounded. Section A's
//	 constants enter as A₀/B₀ and mulAlt's as A₁/B₁; the witness is
//	 their sum. Composition on the nadd side is pointwise composition
//	 (Mul); mulAlt bridges n·(inv(x))(x(n)) to (inv(x))(n)·x(n) up to
//	 linear error; inv and nat_arith.MulSym commute the reciprocal into
//	 Section A's shape; nat_monus.DistLeftMul and OfNum bridge n·1(n) to n².
//
//	Section C (goal) — assemble. With x₀ ≁ 0 assumed,
//	 nat_order.BoundsDivided converts Section B's n-scaled bound into the
//	 pure ∃B∀n form that unfolds nadd_eq(inv(x₀)·x₀, 1).
var MulLeftInverse = mulLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "MulLeftInverse",
	Key:  "prop_738ddc37d9c53b3d",
	// The proof is three sections written as a linear script: each estimate
	// is a Go local the next section cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x:nadd.",
			Hypotheses: []string{
				"¬nadd_eq(x, nadd_of_num(0))",
			},
			Conclusion: "nadd_eq(nadd_inv(x) * x, nadd_of_num(1))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// scaledReciprocalError — the reciprocal defect is affinely bounded,
			// globally. The two sources are an eventual bound (recipApprox) and
			// a global growth bound (LinearBound); chaining them past the
			// threshold gives an eventual affine bound, which nat_order.BoundsIgnore
			// upgrades.
			scaledReciprocalError := ctx.Lemma(Statement{
				Binders: "∀x:nadd.",
				Hypotheses: []string{
					"¬nadd_eq(x, nadd_of_num(0))",
				},
				Conclusion: "∃A B:num. ∀n:num. dist((dest_nadd(x, n) * nadd_rinv(x, n), n * n)) ≤ A * n + B",
			},
				func(a *Argument, x Term, nonzero Fact) {
					// recipApprox is stated under x ≁ 0, so its install carries a
					// trailing x ~ 0 disjunct; `nonzero` is what settles it.
					N_0, eventual := a.Obtain(
						"threshold N₀ beyond which the reciprocal defect is at most x itself — recipApprox at x",
						"∃N:num. ∀n:num. N ≤ n ⇒ dist((dest_nadd(x, n) * nadd_rinv(x, n), n * n)) ≤ dest_nadd(x, n)",
						By(At(recipApprox, x), nonzero))
					A_0, B_0, growth := a.Obtain2(
						"growth constants A₀, B₀ with x(n) ≤ A₀·n + B₀ everywhere",
						"∃A B:num. ∀n:num. dest_nadd(x, n) ≤ A * n + B",
						By(LinearBound))

					a.Take(A_0) // the global bound's slope is the growth's slope
					a.Do(Suffices(
						ctx.MakePropText(
							"∃B N:num. ∀i:num. N ≤ i ⇒ dist((dest_nadd(x₀, i) * nadd_rinv(x₀, i), i * i)) ≤ A₀ * i + B"),
						"nat_order.BoundsIgnore ⇐: an eventual A₀·i + B bound forces the global one",
						// The claim above is the eventually-bounded form as
						// nat_order.BoundsIgnore states it, so the bridge cites
						// the entry.
						Cite(nat_order.BoundsIgnore)))

					a.Take(B_0)
					a.Take(N_0)
					i_0 := a.Fix()
					a.Show(
						"beyond N₀: dist(x(i₀)·rinv(x,i₀), i₀²) ≤ x(i₀) ≤ A₀·i₀ + B₀ "+
							"— nat_order.LessEqTrans chains the eventual and growth bounds",
						By(
							At(eventual, i_0),
							At(growth, i_0),
							At(nat_order.LessEqTrans,
								v.d(v.mul(v.at(x, i_0), v.NaddRinv.Apply(x, i_0)), v.mul(i_0, i_0)),
								v.at(x, i_0),
								v.sum(v.mul(A_0, i_0), B_0),
							)))
				})

			// pointwiseIdentity — the n-scaled pointwise defect between
			// (inv(x)·x)(n) and 1(n) is affinely bounded, with the two estimates'
			// constants added.
			pointwiseIdentity := ctx.Lemma(Statement{
				Binders: "∀x:nadd.",
				Hypotheses: []string{
					"¬nadd_eq(x, nadd_of_num(0))",
				},
				Conclusion: "∃A B:num. ∀n:num. " +
					"    n * dist((dest_nadd(nadd_inv(x) * x, n), dest_nadd(nadd_of_num(1), n))) ≤ A * n + B",
			},
				func(a *Argument, x Term, nonzero Fact) {
					A_0, B_0, recipError := a.Obtain2(
						"reciprocal-error constants A₀, B₀ — Section A at x, whose premise `nonzero` discharges",
						"∃A B:num. ∀n:num. dist((dest_nadd(x, n) * nadd_rinv(x, n), n * n)) ≤ A * n + B",
						By(At(scaledReciprocalError, x), nonzero))
					A_1, B_1, altError := a.Obtain2(
						"near-multiplicativity constants A₁, B₁",
						"∃A B:num. ∀n:num. "+
							"    dist((n * dest_nadd(nadd_inv(x), dest_nadd(x, n)), "+
							"            dest_nadd(nadd_inv(x), n) * dest_nadd(x, n))) ≤ "+
							"    A * n + B",
						By(mulAlt))

					// The sum absorbs both defects.
					a.Take(v.sum(A_0, A_1))
					a.Take(v.sum(B_0, B_1))
					n_0 := a.Fix()
					a.Do(mulLeftInversePointwiseChain(ctx, v, x, n_0, A_0, A_1, B_0, B_1,
						nonzero, recipError, altError))
				})

			// goal — the top statement. Under x₀ ≁ 0, Section B at x₀ supplies
			// ∃A B ∀n. n·nat_dist((inv(x₀)·x₀)(n), 1(n)) ≤ A·n + B, and
			// nat_order.BoundsDivided's ⇐ direction divides out the n to leave
			// ∃B ∀n. nat_dist((inv(x₀)·x₀)(n), 1(n)) ≤ B — nadd_eq unfolded.
			return ctx.Theorem(headline,
				func(a *Argument, x Term, nonzero Fact) {
					invXComposeX := v.NaddMul.Apply(v.NaddInv.Apply(x), x)
					oneN := v.NaddOfNum.Apply(ctx.Numeral(1))
					n := ctx.Var("n", NumType) // nat_order.BoundsDivided's λ-binder

					// The two constants are never needed by name — only the bound
					// they carry, which nat_order.BoundsDivided consumes wholesale.
					_, _, scaled := a.Obtain2(
						"a scaled-defect bound for inv(x₀)·x₀ against 1 — "+
							"Section B at x₀, whose premise `nonzero` discharges",
						"∃A B:num. ∀n:num. "+
							"    n * dist((dest_nadd(nadd_inv(x₀) * x₀, n), dest_nadd(nadd_of_num(1), n))) ≤ A * n + B",
						By(At(pointwiseIdentity, x), nonzero))

					// Slope equivalence IS a global pointwise bound, so it suffices
					// to produce one; the bridge is the nadd_eq unfold.
					a.Do(Suffices(
						ctx.MakePropText(
							"∃B:num. ∀n:num. dist((dest_nadd(nadd_inv(x₀) * x₀, n), dest_nadd(nadd_of_num(1), n))) ≤ B"),
						"nadd_eq(inv(x₀)·x₀, 1) unfolds to exactly this global bound",
						Rewrite(ctx.ConstDef("nadd_eq"), v.NaddEq)))

					// The pointwise defect of inv(x₀)·x₀ against 1, as a function
					// of the index: what Section B bounds after scaling by n, and
					// what nat_order.BoundsDivided is cited at. Naming it keeps the
					// close reading about the defect rather than its spelling.
					defect := n.To(v.d(v.at(invXComposeX, n), v.at(oneN, n)))

					a.Show(
						"hence the defect is globally bounded — nat_order.BoundsDivided "+
							"⇐ divides the n out of Section B's scaled bound",
						By(DenotedAs("defect", defect), scaled, At(nat_order.BoundsDivided, defect)))
				})
		}),
})}

// mulLeftInversePointwiseChain assembles the pointwise identity at the
// fixed index n₀ out of the two eventual estimates: `recipError` is
// Section A's bound at x, `altError` is mulAlt's at (inv(x), x), and
// `nonzero` is the premise x ≁ 0 that picks rinv out of nadd_inv's
// COND. Named subterms make the algebra readable at the Have level.
func mulLeftInversePointwiseChain(ctx *Script, v *slopeVocab,
	x, n_0, A_0, A_1, B_0, B_1 Term,
	nonzero, recipError, altError Fact) Action {
	// Named subterms — the algebra reads by structure.
	invX := v.NaddInv.Apply(x)
	invXComposeX := v.NaddMul.Apply(invX, x)     // inv(x)·x
	oneN := v.NaddOfNum.Apply(ctx.Numeral(1))    // nadd_of_num(1)
	xn := v.at(x, n_0)                           // x(n₀)
	rinvXn := v.NaddRinv.Apply(x, n_0)           // rinv(x, n₀)
	invXn := v.at(invX, n_0)                     // (inv(x))(n₀)
	invXComposeXn := v.at(invXComposeX, n_0)     // (inv(x)·x)(n₀)
	invXAtXn := v.at(invX, xn)                   // (inv(x))(x(n₀))
	oneAtN := v.at(oneN, n_0)                    // 1(n₀)
	nn := v.mul(n_0, n_0)                        // n₀·n₀
	witRHS := v.sum(v.mul(v.sum(A_0, A_1), n_0), // the composite bound
		v.sum(B_0, B_1)) // (A₀+A₁)·n₀ + (B₀+B₁)

	// The two chords of the triangle, and their sum.
	firstChord := v.d(v.mul(n_0, invXAtXn), v.mul(invXn, xn))
	secondChordTerm := v.d(v.mul(invXn, xn), nn)
	rawBound := v.sum(v.sum(v.mul(A_1, n_0), B_1), v.sum(v.mul(A_0, n_0), B_0))

	return Derive(func(a *Argument) {
		mulAltAt := a.Have(
			"mulAlt at n₀: n₀·(inv(x))(x(n₀)) and (inv(x))(n₀)·x(n₀) agree up to A₁·n₀+B₁",
			MakeProp(v.le(firstChord, v.sum(v.mul(A_1, n_0), B_1))),
			By(At(altError, n_0)))

		recipAt := a.Have(
			"Section A at n₀: dist(x(n₀)·rinv(x,n₀), n₀²) ≤ A₀·n₀+B₀",
			MakeProp(v.le(v.d(v.mul(xn, rinvXn), nn), v.sum(v.mul(A_0, n_0), B_0))),
			By(At(recipError, n_0)))

		invUnfold := a.Have(
			"inv unfold at n₀: (inv(x))(n₀) = rinv(x, n₀) — x ≁ 0 discharges COND's zero branch",
			MakeProp(invXn.Eq(rinvXn)),
			By(At(inv, n_0, x), nonzero))

		oneValue := a.Have(
			"OfNum at (1, n₀): 1(n₀) = 1·n₀, which arith finishes",
			MakeProp(oneAtN.Eq(n_0)),
			ByArith(At(OfNum, ctx.Numeral(1), n_0)))

		secondChord := a.Have(
			"second chord ≤ A₀·n₀+B₀: nat_arith.MulSym and the inv unfold turn "+
				"(inv(x))(n₀)·x(n₀) into x(n₀)·rinv(x,n₀), where Section A applies",
			MakeProp(v.le(secondChordTerm, v.sum(v.mul(A_0, n_0), B_0))),
			By(recipAt, invUnfold, At(nat_arith.MulSym, invXn, xn)))

		rawSum := a.Have(
			"chord sum (raw): dist₁ + dist₂ ≤ (A₁·n₀+B₁) + (A₀·n₀+B₀) "+
				"— nat_order.LessEqAdd2 adds the two chord bounds",
			MakeProp(v.le(v.sum(firstChord, secondChordTerm), rawBound)),
			By(
				mulAltAt,
				secondChord,
				At(nat_order.LessEqAdd2,
					firstChord,                  // m
					secondChordTerm,             // n
					v.sum(v.mul(A_1, n_0), B_1), // p
					v.sum(v.mul(A_0, n_0), B_0), // q
				)))

		regroup := a.Have(
			"ring rearrangement: (A₁·n₀+B₁) + (A₀·n₀+B₀) = (A₀+A₁)·n₀ + (B₀+B₁)",
			MakeProp(rawBound.Eq(witRHS)),
			ByArith())

		chordSum := a.Have(
			"chord sum (witness): dist₁ + dist₂ ≤ (A₀+A₁)·n₀ + (B₀+B₁) — the same bound with the RHS regrouped",
			MakeProp(v.le(v.sum(firstChord, secondChordTerm), witRHS)),
			By(rawSum, regroup))

		composite := a.Have(
			"composite bound at n₀ — nat_monus.DistTriangleLessEq consumes "+
				"the chord sum, Mul reads (inv(x))(x(n₀)) as (inv(x)·x)(n₀)",
			MakeProp(v.le(v.d(v.mul(n_0, invXComposeXn), nn), witRHS)),
			By(
				chordSum,
				At(nat_monus.DistTriangleLessEq,
					v.mul(n_0, invXAtXn), // m := n₀·(inv(x))(x(n₀))
					v.mul(invXn, xn),     // n := (inv(x))(n₀)·x(n₀)
					nn,                   // p := n₀·n₀
					witRHS,               // q := (A₀+A₁)·n₀ + (B₀+B₁)
				),
				At(Mul, n_0, invX, x)))

		scaleBridge := a.Have(
			"n₀·1(n₀) = n₀·n₀ — the identity slope's value at n₀ is n₀",
			MakeProp(v.mul(n_0, oneAtN).Eq(nn)),
			By(Normalized, oneValue))

		scaledDefect := a.Have(
			"scaled defect: n₀·dist((inv(x)·x)(n₀), 1(n₀)) = "+
				"dist(n₀·(inv(x)·x)(n₀), n₀·1(n₀)) by DistanceLeftMul",
			MakeProp(v.mul(n_0, v.d(invXComposeXn, oneAtN)).Eq(
				v.d(v.mul(n_0, invXComposeXn), v.mul(n_0, oneAtN)))),
			By(nat_monus.DistLeftMul))

		a.Show(
			"hence n₀·dist((inv(x)·x)(n₀), 1(n₀)) ≤ (A₀+A₁)·n₀ + "+
				"(B₀+B₁) — the composite bound read across the two bridges",
			By(composite, scaledDefect, scaleBridge))
	})
}

// InvWellDef — slope inversion respects slope equivalence:
//
//	⊢ ∀x y : nadd. nadd_eq(x, y) ⇒ nadd_eq(nadd_inv(x), nadd_inv(y))
//
// The boundary lemma a split-out proof would need is absorbed inline —
// nadd_inv's COND-eval at x ≈ 0 is one def_expand plus a CondRewrite —
// so the whole member is the case-split below, whose interesting half
// is a purely algebraic identity in the slope monoid.
//
// Case-split on the boundary x ≈ 0:
//
// - x ≈ 0: from x ≈ y and x ≈ 0 the y ≈ 0 branch of nadd_inv's
// defining COND fires on both sides, collapsing inv(x) and inv(y)
// to the same term nadd_of_num(0). Reflexivity of nadd_eq closes.
//
// - x ≢ 0: with x ≈ y this forces y ≢ 0, so MulLeftInverse
// grants inv(x)·x ≈ 1 and inv(y)·y ≈ 1. Chain
//
// inv(x) ≈ inv(x)·(y·inv(y)) (y·inv(y) ≈ 1)
// ≈ (inv(x)·y)·inv(y) (MulAssoc)
// ≈ 1·inv(y) (inv(x)·y ≈ 1)
// ≈ inv(y) (MulLeftId)
//
// the closing algebra. Each equational step is one MulWellDef
// ground instance plus one NaddEqTrans; MulSym rotates y·inv(y) and
// the leading inv(x)·1 into the LeftId form.
var InvWellDef = invWellDefThm{family.Add(registry.ProofEntry{
	Name: "InvWellDef",
	Key:  "prop_63431cda9393a29b",
	// One section: split on x ≈ 0; unfold at zero and use the inverse
	// algebra in the nonzero branch.
	Build: family.Sections(
		Statement{
			Binders: "∀x y:nadd.",
			Hypotheses: []string{
				"nadd_eq(x, y)",
			},
			Conclusion: "nadd_eq(nadd_inv(x), nadd_inv(y))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			// zero_ — the base-point nadd_of_num(0), the COND's discriminant.
			zero_ := v.NaddOfNum.Apply(ctx.Numeral(0))

			// goal — case-split on x ≈ 0: the boundary branch collapses through
			// the COND, the non-boundary branch runs the MulLeftInverse algebra.
			return ctx.Theorem(headline,
				// The trailing `_ Fact` absorbs the ⇒: x ≈ y is assumed at the
				// boundary and named inside the algebraic branch instead.
				func(a *Argument, x, y Term, _ Fact) {
					a.Do(ByCaseStep(v.NaddEq.Apply(x, zero_),
						Case(
							"x₀ ≈ 0: nadd_inv's COND fires on both sides — inv(x) and "+
								"inv(y) both collapse to nadd_of_num(0), and reflexivity closes",
							Unfold(NaddInvDef),
							Cite(NaddEqTrans),
							Cite(NaddEqSym),
							Cite(NaddEqRefl),
							CondRewrite(),
							Basic(),
							CnfRefute(),
						),
						Case(
							"x₀ ≢ 0: MulLeftInverse grants inv(x)·x ≈ 1 and inv(y)·y ≈ 1; the algebraic chain closes",
							invWellDefWhenXNonzero(ctx, v, x, y),
						),
					))
				})
		}),
})}

// invWellDefWhenXNonzero — the algebraic branch. The Derive block
// establishes the seven intermediate equations and closes via a
// two-leg NaddEqTrans chain (inv(x) ≈ inv(x)·(y·inv(y)) ≈ (inv(x)·y)·inv(y)
// ≈ inv(y)).
func invWellDefWhenXNonzero(ctx *Script, v *slopeVocab, x_0, y_0 Term) Action {
	// one — the numeral 1 (MulLeftInverse's identity, MulLeftId's
	// leading factor).
	one := ctx.Numeral(1)

	// Named subterms — the algebra reads by structure, not by re-spelt formulae.
	invX := v.NaddInv.Apply(x_0)
	invY := v.NaddInv.Apply(y_0)
	oneN := v.NaddOfNum.Apply(one)
	invXTimesX := v.NaddMul.Apply(invX, x_0)
	invYTimesY := v.NaddMul.Apply(invY, y_0)
	invXTimesY := v.NaddMul.Apply(invX, y_0)
	yTimesInvY := v.NaddMul.Apply(y_0, invY)
	invXTimesYinvY := v.NaddMul.Apply(invX, yTimesInvY)
	invXyTimesInvY := v.NaddMul.Apply(invXTimesY, invY)

	// Claim builder — nadd_eq(a, b), the shape every Have carries.
	eq := func(a, b Term) Prop {
		return MakeProp(v.NaddEq.Apply(a, b))
	}

	// xNonzero is the branch's own hypothesis, x₀ ≢ 0; the equivalence
	// x ≈ y was assumed at the section boundary, so it is named here.
	return Given(func(a *Argument, xNonzero Fact) {
		xEqY := a.Hyp(v.NaddEq.Apply(x_0, y_0))

		// inv(x)·x ≈ 1 — MulLeftInverse at x, guarded by x₀ ≢ 0.
		invXXisOne := a.Have(
			"inv(x)·x ≈ 1 — MulLeftInverse at x₀ (x₀ ≢ 0 discharges its boundary disjunct)",
			eq(invXTimesX, oneN),
			By(xNonzero, At(MulLeftInverse, x_0)))

		// inv(y)·y ≈ 1 — MulLeftInverse at y, boundary refuted by
		// x ≈ y + x ≢ 0.
		invYYisOne := a.Have(
			"inv(y)·y ≈ 1 — MulLeftInverse at y₀ (x ≈ y and x ≢ 0 force y ≢ 0, discharging its boundary)",
			eq(invYTimesY, oneN),
			By(xEqY, xNonzero, At(MulLeftInverse, y_0), NaddEqTrans, NaddEqSym))

		// inv(x)·y ≈ 1 — substitute y for x on the right of the
		// MulLeftInverse product via MulWellDef (inv(x) ≈ inv(x) and x ≈ y).
		invXYisOne := a.Have(
			"inv(x)·y ≈ 1 — MulWellDef substitutes y for x on the right of inv(x)·x, using x ≈ y",
			eq(invXTimesY, oneN),
			By(xEqY, invXXisOne, MulWellDef, NaddEqRefl, NaddEqSym, NaddEqTrans))

		// y·inv(y) ≈ 1 — MulSym commutes inv(y)·y ≈ 1.
		yInvYisOne := a.Have(
			"y·inv(y) ≈ 1 — MulSym commutes inv(y)·y ≈ 1",
			eq(yTimesInvY, oneN),
			By(invYYisOne, MulSym, NaddEqTrans, NaddEqSym))

		// MulAssoc bridge — inv(x)·(y·inv(y)) ≈ (inv(x)·y)·inv(y).
		assocBridge := a.Have(
			"MulAssoc bridge — inv(x)·(y·inv(y)) ≈ (inv(x)·y)·inv(y)",
			eq(invXTimesYinvY, invXyTimesInvY),
			Cite(MulAssoc))

		// (inv(x)·y)·inv(y) ≈ inv(y) — inv(x)·y collapses to 1 (via
		// MulWellDef), MulLeftId erases the leading 1·.
		collapse := a.Have(
			"(inv(x)·y)·inv(y) ≈ inv(y) — the inner inv(x)·y collapses to 1, then MulLeftId erases 1·",
			eq(invXyTimesInvY, invY),
			By(
				invXYisOne,
				// MulLeftId at inv(y): 1·inv(y) ≈ inv(y).
				At(MulLeftId, invY),
				// MulWellDef pinned at (inv(x)·y, 1, inv(y), inv(y)) — swaps
				// the leading factor from (inv(x)·y) to 1 given inv(x)·y ≈ 1
				// and inv(y) ≈ inv(y).
				At(MulWellDef, invXTimesY, oneN, invY, invY),
				NaddEqRefl,
				NaddEqTrans,
				NaddEqSym))

		// inv(x) ≈ inv(x)·(y·inv(y)) — the mirror bridge: erase 1 as
		// y·inv(y), then peel MulLeftId off inv(x) (via MulSym) to
		// exhibit inv(x)·1. The swap turns on the right-inverse law
		// y·inv(y) ≈ 1.
		mirrorBridge := a.Have(
			"inv(x) ≈ inv(x)·(y·inv(y)) — mirror bridge: MulLeftId+MulSym "+
				"peels off inv(x)·1, MulWellDef swaps 1 for y·inv(y)",
			eq(invX, invXTimesYinvY),
			By(
				yInvYisOne,
				// MulLeftId at inv(x): 1·inv(x) ≈ inv(x).
				At(MulLeftId, invX),
				// MulSym at (inv(x), 1): inv(x)·1 ≈ 1·inv(x).
				At(MulSym, invX, oneN),
				// MulWellDef pinned at (inv(x), inv(x), y·inv(y), 1) — swaps
				// the right factor from (y·inv(y)) to 1 given y·inv(y) ≈ 1
				// and inv(x) ≈ inv(x).
				At(MulWellDef, invX, invX, yTimesInvY, oneN),
				NaddEqRefl,
				NaddEqTrans,
				NaddEqSym))

		// Two NaddEqTrans legs chain the assembled facts:
		// inv(x) ≈ inv(x)·(y·inv(y)) ≈ (inv(x)·y)·inv(y) ≈ inv(y).
		a.Show(
			"chain — NaddEqTrans(inv(x), inv(x)·(y·inv(y)), inv(y)) via the middle bridge (inv(x)·y)·inv(y)",
			By(
				mirrorBridge,
				assocBridge,
				collapse,
				At(NaddEqTrans, invX, invXTimesYinvY, invY),
				At(NaddEqTrans, invXTimesYinvY, invXyTimesInvY, invY)))
	})
}

// ---------------------------------------------------------------------------
// The ℕ-embedding n ↦ (m ↦ n·m) and its morphism laws
// ---------------------------------------------------------------------------
//
// well-definedness, injectivity, and preservation of ≤, + and ·.
//
// README: the "ℕ-embedding" bullet.

// OfNum — reading the embedded natural k back out of its slope:
//
//	⊢ ∀k n. k·n = dest_nadd(nadd_of_num(k), n)
//
// nadd_of_num(k) packages λn. k·n as a slope via mk_nadd; the theorem
// says dest_nadd undoes the packaging, pointwise. Two ingredients:
//
// - isSlope: λn. k·n satisfies the defining near-linearity bound
// outright. Its defect nat_dist(m·(k·n), n·(k·m)) is identically zero —
// both products rearrange to k·(m·n) by assoc/comm — so B := 0
// already bounds it.
// - goal: a function is a slope exactly when dest_nadd ∘ mk_nadd
// fixes it (the membership axiom of the nadd type definition), so
// dest_nadd(nadd_of_num(k)) = λn. k·n; the statement is that
// equation read at n.
var OfNum = ofNumThm{family.Add(registry.ProofEntry{
	Name: "OfNum",
	Key:  "prop_51ac18f3411f11a3",
	// The proof is one lemma plus the assembly, written as a linear script:
	// `isSlope` is a Go local the goal cites by closure capture.
	Build: family.Sections(
		"∀k n:num. k * n = dest_nadd(nadd_of_num(k), n)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zero := ctx.Numeral(0) // the bound B := 0

			k_0 := ctx.Var("k_0", NumType)
			ctx.Var("m_0", NumType)
			ctx.Var("n_0", NumType)

			membershipThm := naddMembership(ctx)

			// isSlope: multiplication by a fixed k is a slope, with the best
			// possible bound — its defect is identically zero.
			isSlope := ctx.Lemma("∀k:num. is_nadd(λn:num. k * n)",
				func(a *Argument) {
					a.Do(
						// is_nadd unfolds (and β-reduces) to the near-linearity bound
						// ∃B. ∀m n. nat_dist(m·(k·n), n·(k·m)) ≤ B·(m + n).
						Unfold(IsNaddDef),
						StripQuant(),
						Witness(zero), // the defect vanishes identically, so B := 0
						StripQuant(),
						AssertStep(ctx.MakePropText("m₀ * (k₀ * n₀) = n₀ * (k₀ * m₀)"),
							Case(
								"the defect's two products agree — both rearrange to k·(m·n) by assoc/comm",
								Derive(func(b *Argument) {
									b.Show(
										"commutativity and associativity rearrange both products to k·(m·n)",
										By(nat_arith.MulSym, nat_arith.MulAssoc))
								}),
							),
							Case(
								"the defect is a dist of equal arguments — zero by "+
									"nat_monus.DistRefl — and 0 ≤ 0·(m+n) by ZeroLessEq",
								Given(func(b *Argument, products Fact) {
									b.Show(
										"nat_monus.DistRefl sends the equal-argument dist to 0, and ZeroLessEq bounds it",
										By(products, nat_monus.DistRefl, nat_order.ZeroLessEq))
								}),
							),
						),
					)
				})

			// membershipIff keeps a *HypHandle: UseLemma is a NON-preserving
			// install, so what lands is not the axiom's own statement (the lemma
			// tactic rewrites the resident context on the way in) and
			// content-addressing has nothing to name.
			membershipIff := NewHypHandle("membershipIff") // is_nadd(r) ⇔ dest_nadd(mk_nadd(r)) = r
			n := ctx.Var("n", NumType)
			// carrier = λn. k₀·n, the function nadd_of_num(k₀) wraps in mk_nadd.
			carrier := n.To(v.Times.Apply(k_0, n))

			// goal: the close mirrors eudoxus_slope.Mul's — ground the membership axiom at
			// the carrier nadd_of_num packages, cite isSlope to discharge the
			// iff's left side, and β-reduce the residual equation.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(
						membershipIff.From(UseLemma(membershipThm)), // typedef membership as resident fact
						StripQuant(),                  // k_0, n_0
						Unfold(NaddOfNumDef),          // nadd_of_num(k₀) → mk_nadd(carrier)
						membershipIff.Ground(carrier), // membership read at r := λn. k₀·n
						Cite(isSlope),                 // discharges the iff's left side
					)
				})
		}),
})}

// OfNumWellDef — the numeral embedding respects equality:
//
//	⊢ ∀m n : num. m = n ⇒ nadd_eq(nadd_of_num(m), nadd_of_num(n))
//
// Substituting m = n makes the two sides literally identical, and
// reflexivity of slope equivalence (NaddEqRefl) closes.
var OfNumWellDef = ofNumWellDefThm{family.Add(registry.ProofEntry{
	Name: "OfNumWellDef",
	Key:  "prop_2b662ce6f7e325f3",
	// The closure binds NOTHING: the refute works on the ∀⇒-form as it
	// stands, so there is no leading strip for a parameter to absorb.
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m = n",
		},
		Conclusion: "nadd_eq(nadd_of_num(m), nadd_of_num(n))",
	},
		func(a *Argument) {
			a.Do(
				// Reflexivity of slope equivalence: ∀x. nadd_eq(x, x).
				Cite(NaddEqRefl),
				// One refute: m = n rewrites nadd_of_num(m) to nadd_of_num(n),
				// and the reflexivity instance at nadd_of_num(n) closes.
				CnfRefute(),
			)
		}),
})}

// OfNumEq — the numeral embedding is injective up to slope
// equivalence:
//
//	⊢ ∀m n : num. (m = n) ⇔ nadd_eq(nadd_of_num(m), nadd_of_num(n))
//
// The two directions:
// - ⇐ is OfNumWellDef: equal numbers give equivalent slopes.
// - ⇒ is the content: equivalence of the embedded slopes says the
// multiples nat_dist(m·k, n·k) are uniformly bounded (their underlying
// functions compute k ↦ m·k and k ↦ n·k — OfNum). Factor
// nat_dist(m·k, n·k) = nat_dist(m,n)·k (nat_monus.DistRightMul); a linear function with
// a uniform bound has zero coefficient (nat_order.BoundsLinear0); zero
// distance forces m = n (nat_monus.DistEqZero).
//
// lemma1 isolates the numeric heart — uniform boundedness of the
// multiples is equivalent to m = n; lemma2 transports it through the
// definition of nadd_eq; the goal assembles the two directions.
var OfNumEq = ofNumEqThm{family.Add(registry.ProofEntry{
	Name: "OfNumEq",
	Key:  "prop_cfe02a68d5ad84d0",
	// The proof is three sections written as a linear script: each lemma is
	// a Go local the next section cites by closure capture.
	Build: family.Sections(
		"∀m n:num. m = n ⇔ nadd_eq(nadd_of_num(m), nadd_of_num(n))",
		func(ctx *Script, headline string) *GoalStackNode {

			// lemma1: the numeric heart — the multiples of m and n stay uniformly
			// close exactly when m = n. One joint simplification rewrites the
			// bounded-multiples predicate down to nat_dist(m,n) = 0, and nat_monus.DistEqZero
			// finishes.
			lemma1 := ctx.Lemma("∀m n:num. (∃B:num. ∀k:num. dist((m * k, n * k)) ≤ B) ⇔ m = n",
				func(a *Argument, m, n Term) {
					a.Do(Expect(Simp(
						Fwd(nat_monus.DistRightMul),  // nat_dist(m·p, n·p) → nat_dist(m,n)·p
						Fwd(nat_order.BoundsLinear0), // (∀k. A·k ≤ B) → (A = 0)
					),
						Case(
							"(∃B. dist(m₀,n₀) = 0) ⇔ (m₀ = n₀) — the vacuous ∃B collapses, and zero distance means equal",
							Cite(nat_monus.DistEqZero),
						),
					))
				})

			// lemma2: the forward direction — equivalence of the embedded slopes
			// forces m = n. The ⇒-antecedent is assumed at the boundary and only
			// ever read by the refuter, so the body never needs it by name.
			lemma2 := ctx.Lemma(Statement{
				Binders: "∀m n:num.",
				Hypotheses: []string{
					"nadd_eq(nadd_of_num(m), nadd_of_num(n))",
				},
				Conclusion: "m = n",
			},
				func(a *Argument, m, n Term, _ Fact) {
					a.Do(
						// lemma1 at (m₀, n₀): the multiples of m₀ and n₀ are uniformly
						// close iff m₀ = n₀.
						Cite(lemma1),
						GroundHyp(lemma1.PromisedThm(), m, n),
						// Unfold nadd_eq: the assumed equivalence becomes a uniform bound
						// on the distances between the underlying functions' values.
						Unfold(NaddEqDef),
						// The embedded slopes' underlying functions compute the multiples:
						// dest_nadd(nadd_of_num(k), j) = k·j (OfNum). Rewriting
						// turns the assumed bound into lemma1's bounded-multiples form,
						// which contradicts m₀ ≠ n₀ — the cite's own simplify/auto-match
						// discharges that contradiction and closes the leaf (no separate
						// refute step).
						Cite(OfNum),
					)
				})

			// goal: assemble the equivalence from its two directions — lemma2 (⇒,
			// the injectivity content) and OfNumWellDef (⇐, substitution and
			// reflexivity); one refute stitches the two clauses into the ⇔.
			return ctx.Theorem(headline,
				func(a *Argument) {
					a.Do(
						Cite(lemma2),
						Cite(OfNumWellDef),
						CnfRefute(),
					)
				})
		}),
})}

// OfNumLessEq — the numeral embedding is an order embedding:
//
//	⊢ ∀m n : num. (m ≤ n) ⇔ (nadd_of_num(m) ≤ nadd_of_num(n))
//
// The order on slopes is a uniform one-sided bound between the
// underlying functions, and the embedded slopes' functions compute the
// multiples k ↦ m·k and k ↦ n·k (OfNum). So the right-hand side is the
// pivot
//
//	∃B. ∀k. m·k ≤ n·k + B
//
// and comparing linear growth rates is exactly what nat_order.BoundsLinear
// decides: m ≤ n makes every multiple comparable with any slack
// whatsoever, while a linear excess could never stay uniformly
// bounded — so the slack is vacuous and B := 0 already serves.
var OfNumLessEq = ofNumLessEqThm{family.Add(registry.ProofEntry{
	Name: "OfNumLessEq",
	Key:  "prop_682fbf0d6dcdba04",
	Build: family.Theorem("∀m n:num. m ≤ n ⇔ nadd_of_num(m) ≤ nadd_of_num(n)",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()
			zero := ctx.Numeral(0)

			a.Do(
				// The slope order becomes its defining bound: ∃B. ∀k.
				// dest_nadd(nadd_of_num(m₀), k) ≤ dest_nadd(nadd_of_num(n₀), k) + B.
				Unfold(NaddLeDef),
				SplitIff(
					Forward(
						"m₀ ≤ n₀: the bound holds with no slack at all — B "+
							":= 0, and BoundsLinear at (m₀, n₀, 0) is the pivot",
						Given(func(b *Argument, order Fact) {
							b.Take(zero)
							b.Show(
								"BoundsLinear at (m₀, n₀, 0) IS the slackless pivot",
								By(
									order,
									// OfNum rewrites dest_nadd(nadd_of_num(·), k) to
									// the multiple under the ∀k binder, so it enters
									// in ∀-form.
									OfNum,
									At(nat_order.BoundsLinear, m, n, zero)))
						}),
					),
					Backward(
						"some uniform slack B₀ bounds the excess: the pivot ∀k. m₀·k ≤ n₀·k "+
							"+ B₀ is exactly BoundsLinear's left side, so it reads back as m₀ ≤ n₀",
						// Skolemize the bound's ∃B as B₀; the pivot it leaves
						// resident is what the two cites below act on.
						StripQuant(),
						// OfNum rewrites dest_nadd(nadd_of_num(·), k) into the
						// multiple under the ∀k binder, so it enters in ∀-form.
						Cite(OfNum),
						// BoundsLinear's install decides this direction outright —
						// its (m₀, n₀, B₀) instance is the whole residual goal, so
						// there is nothing left to ground it against.
						Cite(nat_order.BoundsLinear),
					),
				),
			)
		}),
})}

// OfNumAdd — additivity of the ℕ-embedding, up to slope equivalence:
//
//	⊢ ∀m n : num. nadd_eq((nadd_of_num(m) + nadd_of_num(n)),
//	 nadd_of_num(m + n))
//
// The embedding computes multiples — dest_nadd(nadd_of_num(k), j) = k·j
// (OfNum) — and addition on slopes is pointwise (Add), so at
// every point k the defect between the two sides collapses to
// distributivity:
//
//	dest_nadd((nadd_of_num(m) + nadd_of_num(n)), k)
//	 = dest_nadd(nadd_of_num(m), k) + dest_nadd(nadd_of_num(n), k)
//	 = m·k + n·k = (m + n)·k = dest_nadd(nadd_of_num(m + n), k)
//
// Zero defect ⇒ B := 0 bounds the distance. Completes the OfNum
// morphism ladder alongside OfNumEq (injectivity) and OfNumLessEq
// (order-embedding). The proof grounds four facts at the Skolems —
// Add once, OfNum three times (one per summand, one for the packaged
// sum), and nat_arith.RightAddDistrib — so nat_monus.DistRefl +
// nat_order.ZeroLessEq close the residual 0 ≤ 0 with no refute and no
// arith.
var OfNumAdd = ofNumAddThm{family.Add(registry.ProofEntry{
	Name: "OfNumAdd",
	Key:  "prop_a49f41c4eadc09f8",
	Build: family.Theorem("∀m n:num. nadd_eq(nadd_of_num(m) + nadd_of_num(n), nadd_of_num(m + n))",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			// n₁ comes from the ∀n strip after Witness — the point at which
			// the defect is measured.
			n1 := ctx.Var("n_1", NumType)
			a.Do(
				// nadd_eq unfolds to ∃B. ∀k. nat_dist(...) ≤ B.
				v.ZeroDefectClose(ctx), // unfold nadd_eq, B := 0, fix n₁
				// pointwise sum: dest_nadd((a + b), k) = dest_nadd(a,k) + dest_nadd(b,k)
				// at (n₁, nadd_of_num(m₀), nadd_of_num(n₀)).
				Cite(Add,
					n1, v.NaddOfNum.Apply(m), v.NaddOfNum.Apply(n)),
				// embedding computes multiples: three uses, one per summand and
				// one for the packaged (m₀ + n₀) side.
				Cite(OfNum, m, n1),
				Cite(OfNum, n, n1),
				Cite(OfNum, v.sum(m, n), n1),
				// (m₀ + n₀)·n₁ = m₀·n₁ + n₀·n₁ — the identity that closes the defect.
				Cite(nat_arith.RightAddDistrib, m, n, n1),
				// The two sides now reduce to the same term m₀·n₁ + n₀·n₁; the
				// distance vanishes by nat_monus.DistRefl, …
				Cite(nat_monus.DistRefl),
				// … and 0 ≤ 0 closes the bound.
				Cite(nat_order.ZeroLessEq),
			)
		}),
})}

// OfNumMul — multiplicativity of the ℕ-embedding, up to slope
// equivalence:
//
//	⊢ ∀m n : num. nadd_eq((nadd_of_num(m) * nadd_of_num(n)),
//	 nadd_of_num(m * n))
//
// The embedding computes multiples — dest_nadd(nadd_of_num(k), j) = k·j
// (OfNum) — and multiplication on slopes is composition (Mul:
// dest_nadd(nadd_mul(x, y), k) = dest_nadd(x, dest_nadd(y, k))), so at
// every point k' the defect between the two sides collapses to
// associativity of ℕ multiplication:
//
//	dest_nadd((nadd_of_num(m) * nadd_of_num(n)), k')
//	 = dest_nadd(nadd_of_num(m), dest_nadd(nadd_of_num(n), k'))
//	 = dest_nadd(nadd_of_num(m), n·k')
//	 = m·(n·k') = (m·n)·k' = dest_nadd(nadd_of_num(m·n), k')
//
// Zero defect ⇒ B := 0 bounds the distance. Completes the OfNum
// morphism ladder alongside OfNumEq (injectivity), OfNumLessEq
// (order-embedding), and OfNumAdd (additivity). The proof grounds Mul
// + three OfNum instances + nat_arith.MulAssoc at the Skolems, so
// nat_monus.DistRefl + ZeroLessEq close the residual 0 ≤ 0 — no arith.
var OfNumMul = ofNumMulThm{family.Add(registry.ProofEntry{
	Name: "OfNumMul",
	Key:  "prop_7f4f7e10e22e559e",
	Build: family.Theorem("∀m n:num. nadd_eq(nadd_of_num(m) * nadd_of_num(n), nadd_of_num(m * n))",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			// n₁ comes from the ∀k' strip after Witness — the point at which
			// the defect is measured.
			n1 := ctx.Var("n_1", NumType)
			a.Do(
				// nadd_eq unfolds to ∃B. ∀k'. nat_dist(...) ≤ B.
				v.ZeroDefectClose(ctx), // unfold nadd_eq, B := 0, fix n₁
				// pointwise mul: dest_nadd((x * y), k) = dest_nadd(x, dest_nadd(y, k))
				// at (n₁, nadd_of_num(m₀), nadd_of_num(n₀)) — peels the outer dest.
				Cite(Mul,
					n1, v.NaddOfNum.Apply(m), v.NaddOfNum.Apply(n)),
				// Embedding computes multiples: three uses, evaluating each
				// dest_nadd(nadd_of_num(·), ·) that survived.
				// (n₀, n₁) — the inner dest → n₀·n₁
				// (m₀, n₀·n₁) — the outer dest → m₀·(n₀·n₁)
				// (m₀·n₀, n₁) — the RHS dest → (m₀·n₀)·n₁
				Cite(OfNum, n, n1),
				Cite(OfNum, m, v.mul(n, n1)),
				Cite(OfNum, v.mul(m, n), n1),
				// m₀ * (n₀ * n₁) = (m₀ * n₀) * n₁ — the identity that closes the defect.
				Cite(nat_arith.MulAssoc, m, n, n1),
				// The two sides now reduce to the same term (m₀ * n₀) * n₁; the
				// distance vanishes by nat_monus.DistRefl there, …
				Cite(nat_monus.DistRefl, v.mul(v.mul(m, n), n1)),
				// … and 0 ≤ 0 closes the bound.
				Cite(nat_order.ZeroLessEq, ctx.Numeral(0)),
				// One refute over the loaded facts + ground equations: absorb
				// the equation chain to identify the two dist arguments, then
				// discharge the resulting nat_dist(t, t) ≤ 0 via nat_monus.DistRefl and
				// nat_order.ZeroLessEq.
				CnfRefute(),
			)
		}),
})}
