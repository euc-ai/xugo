// nat_div_mod.go — the chapter: Euclidean division on ℕ.
//
// Six parts, marked by banners:
//
// - The nat_div/nat_mod definitional layer
// - Uniqueness of the quotient and remainder
// - The values nat_div and nat_mod actually take
// - How far a division can reach
// - Division and the ring operations
// - Dividing and taking remainders twice

package nat_div_mod

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The nat_div/nat_mod definitional layer
// ---------------------------------------------------------------------------
//
// Euclidean division enters the chapter in three moves, and this file is
// all three:
//
// 1. DivModExist / divModExistZero — quotient and remainder EXIST, by
// well-ordering on the set of remainders m leaves representable.
// 2. divModSpec — the two constants nat_div and nat_mod are minted, once, from
// that existence. The specification door packages the per-point ∃q∃r
// into a pair of functions and names them; the entry is the
// ε-free characterization both constants satisfy.
// 3. Division / DivZero / ModZero — each is one instance of the spec,
// read off at the point where the COND guard decides.
//
// DAG (within this file):
//
// 	DivModExist : [nat_arith.Mul, nat_arith.Add, nat_arith.AddAssoc, nat_arith.AddSym, nat_arith.AddZero,
// 	 nat_order.WellOrdering, nat_order.NotLessThan,
// 	 nat_order.LessEqExists, nat_order.LessEqRefl,
// 	 nat_order.PosIffNonzero, nat_order.LessEqLessThanAdd2]
// 	divModExistZero : [DivModExist]
// 	divModSpec : [divModExistZero]
// 	Division : [divModSpec]
// 	DivZero : [divModSpec]
// 	ModZero : [divModSpec]
//
// Every statement here is stated in its natural mathematical form.
// Normalize absorbs the difference from a clause disjunction, a COND
// or a reversed equation, so the readable form costs nothing.

// ---------------------------------------------------------------------------
// DivModExist — division with remainder is possible
// ---------------------------------------------------------------------------

// DivModExist — Euclidean division exists, by well-ordering. Call r
// REPRESENTABLE (for the fixed m, n) when m = q·n + r for some q. The
// argument is the classical one, in three sentences:
//
//	some r is representable (take out no copy of n: r = m, q = 0),
//	so the representable r have a LEAST one r₀ (nat_order.WellOrdering),
//	and that r₀ is already below n — else one more n would come out.
//
// The ∃-eliminations are driven by name below, rather than by splitting
// the well-ordering iff into a hypothesis and reading the argument out
// of the resulting clauses.
var DivModExist = divModExistThm{family.Add(registry.ProofEntry{
	Name: "DivModExist",
	Key:  "prop_78c59320f95e6f3e",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num.",
			Hypotheses: []string{
				"n ≠ 0",
			},
			Conclusion: "∃q r:num. m = q * n + r ∧ r < n",
		},
		func(a *Argument, m *TermWrapper, n Term, nonzero Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			// q/r are the λ-binders of the well-ordering predicate.
			q := ctx.Var("q", NumType)
			r := ctx.Var("r", NumType)

			// P := λr. ∃q. m₀ = q·n₀ + r — "r is a representable remainder".
			isRemainder := r.To(Exists(q)(m.Eq(v.Add(v.Mul(q, n), r))))

			// Well-ordering in least-element form: a non-empty set of
			// naturals has a least member. Its non-emptiness side is what
			// the inner Have supplies; its least-element side is the claim.
			// leastRep carries BOTH halves of the ∃-body — the representation
			// m₀ = q₀·n₀ + r₀ and the minimality of r₀ — and the argument
			// below consumes them at different steps.
			r0, q0, leastRep := a.Obtain2(
				"well-ordering at P: a non-empty set of remainders has a least one",
				"∃r q:num. m = q * n + r ∧ (∀s:num. s < r ⇒ ¬∃p:num. m = p * n + s)",
				Derive(func(b *Argument) {
					some := b.Have(
						"P is non-empty: m itself is representable — take out no copy of n and all of m is left over",
						"∃r q:num. m = q * n + r",
						Derive(func(c *Argument) {
							c.Take(m)      // r := m₀
							c.Take(v.Zero) // q := 0
							c.Show(
								"0·n₀ + m₀ = m₀ — the zero clauses of · and of + collapse the left side",
								By(Normalized, nat_arith.Mul, nat_arith.Add))
						}))
					// The predicate reaches the refuter as an unreduced
					// application P(x); the denote+normalize pass is what
					// β-reduces it. What is named is the two-place division
					// relation itself — "r is what is left of m₀ after q
					// copies of n₀" — which is isRemainder with the ∃q peeled.
					b.Show(
						"so well-ordering's least-element side holds at P",
						By(some, At(nat_order.WellOrdering, isRemainder)))
				}))

			below := a.Have(
				"the least remainder is already below n",
				"r₀ < n",
				divModExistBelow(v, n, r0, q0, leastRep, nonzero))

			a.Take(q0) // the quotient
			a.Take(r0) // the remainder
			a.Show(
				"(q₀, r₀) is the pair the theorem asks for",
				By(leastRep, below))
		}),
})}

// divModExistBelow is the one real step: r₀ < n₀. Suppose not. Then
// n₀ ≤ r₀, so r₀ = n₀ + d₀ for some d₀, and one more copy of n₀ comes
// out of m₀:
//
//	m₀ = q₀·n₀ + r₀ = q₀·n₀ + (n₀ + d₀) = (q₀·n₀ + n₀) + d₀ = suc(q₀)·n₀ + d₀
//
// so d₀ is representable as well. And d₀ < n₀ + d₀ = r₀ precisely
// because n₀ ≠ 0. A representable remainder strictly below the least one
// is the contradiction.
func divModExistBelow(v *divmodOps, n, r0, q0 Term, leastRep, nonzero Fact) Action {
	return Derive(func(a *Argument) {
		notBelow := a.SupposeNot() // ¬(r₀ < n₀)

		d0, shift := a.Obtain(
			"¬(r₀ < n₀) is n₀ ≤ r₀, which realizes r₀ as n₀ shifted by some d",
			"∃d:num. r₀ = n₀ + d",
			By(
				notBelow,
				At(nat_order.NotLessThan, r0, n), // ¬(r₀ < n₀) ⇔ n₀ ≤ r₀
				// LessEqExists fires as a goal rewrite: ↦ n₀ ≤ r₀.
				nat_order.LessEqExists))

		// One more n₀ comes out of m₀ — regroup, then fold the sum
		// q₀·n₀ + n₀ into suc(q₀)·n₀ by the suc clause of `·`.
		deeper := a.Have(
			"d₀ is representable too, with quotient suc q₀",
			"m₀ = suc(q₀) * n₀ + d₀",
			By(
				Normalized,
				leastRep,
				shift,
				At(nat_arith.AddAssoc, v.Mul(q0, n), n, d0), // q₀·n₀ + (n₀ + d₀) = (q₀·n₀ + n₀) + d₀
				nat_arith.Mul)) // suc(q₀)·n₀ = q₀·n₀ + n₀

		// The step "a < b + a when b ≠ 0" has no home of its own
		// (nat_order absorbed it), so its instance is composed here:
		// nat_order.LessEqLessThanAdd2 adds d₀ ≤ d₀ to 0 < n₀, and nat_arith.AddZero / nat_arith.AddSym
		// re-spell the resulting d₀ + 0 < d₀ + n₀ as d₀ < n₀ + d₀.
		smaller := a.Have(
			"d₀ < r₀, because r₀ overshoots d₀ by the nonzero n₀",
			"d₀ < r₀",
			By(
				Normalized,
				nonzero,
				shift,
				At(nat_order.LessEqLessThanAdd2, d0, v.Zero, d0, n), // d₀ ≤ d₀ ∧ 0 < n₀ ⇒ d₀ + 0 < d₀ + n₀
				At(nat_order.LessEqRefl, d0),                        // d₀ ≤ d₀
				At(nat_order.PosIffNonzero, n),                      // n₀ ≠ 0 ⇔ 0 < n₀
				At(nat_arith.AddZero, d0),                           // d₀ + 0 = d₀
				At(nat_arith.AddSym, d0, n)))                        // d₀ + n₀ = n₀ + d₀

		a.Show(
			"but r₀ was least: no representable remainder is below it",
			By(Normalized, leastRep, deeper, smaller))
	})
}

// ---------------------------------------------------------------------------
// divModExistZero — division with remainder, total in the divisor
// ---------------------------------------------------------------------------

// divModExistZero — the divisor-total form of DivModExist: the COND
// answers the n = 0 case by convention (quotient 0, remainder m) instead
// of excluding it, which is what makes ONE pair of Skolem functions
// definable over all of ℕ×ℕ. Band B — the shape exists for divModSpec's
// mint, not as a fact anyone states. One case split on that guard.
var divModExistZero = divModExistZeroThm{family.Add(registry.ProofEntry{
	Name: "divModExistZero",
	Key:  "prop_e4693b21cfdb81c2",
	Build: family.Theorem(
		"∀m n:num. ∃q r:num. COND(n = 0, q = 0 ∧ r = m, m = q * n + r ∧ r < n)",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			a.Cases(n.Eq(v.Zero))
			a.When(
				"n = 0: the COND selects q = 0 ∧ r = m, so take exactly that pair",
				Witness(v.Zero), // q := 0
				Witness(m),      // r := m
				CondRewrite(),   // the branch hypothesis n₀ = 0 picks the then-side
				Basic(),         // 0 = 0 ∧ m₀ = m₀
			)
			a.Otherwise(
				"n ≠ 0: the COND selects the division equation, which is DivModExist",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"what survives the guard is DivModExist at m = m₀, n = n₀",
						CondRewrite(), // n₀ ≠ 0 decides the guard
						By(nonzero, At(DivModExist, m, n)))
				},
			)
		}),
})}

// ---------------------------------------------------------------------------
// divModSpec — nat_div and nat_mod, minted together (Internal)
// ---------------------------------------------------------------------------

// divModSpecStmt is the specification, exactly the defining property
// nat_mod's introduction leaves behind. nat_div and nat_mod are spelled by the
// stand-ins `quotient` and `remainder`: the DSL keeps both names for
// its own numeral surface, so a definiendum cannot wear them.
const divModSpecStmt = "∀m n:num. COND(n = 0, quotient(m, n) = 0 ∧ remainder(m, " +
	"n) = m, m = quotient(m, n) * n + remainder(m, n) ∧ remainder(m, n) < n)"

// divModSpec — the ε-free characterization of nat_div and nat_mod, and the
// entry that INTRODUCES both constants: one two-constant
// specification off divModExistZero, through the define door's
// spec shape. The author's two surfaces are the specification
// itself and the pointwise existence it rests on; the ε-witness
// Skolemization, the name-tag conditioning, and the two nested
// definitional bridges run inside the composite.
//
// One entry introducing both constants serves the three consumers,
// which become one-cite projections.
var divModSpec = divModSpecThm{family.DefineSpec(registry.SpecEntry{
	Name: "divModSpec",
	Key:  "prop_ab6e9275b3de21c6",
	Consts: []registry.SpecConst{
		{Const: "nat_div", Type: "num → num → num", Spelled: "quotient", Overload: "div"},
		{Const: "nat_mod", Type: "num → num → num", Spelled: "remainder", Overload: "rem"},
	},
	Spec: divModSpecStmt,
	Deps: []registry.EntryLike{divModExistZero},
	// The obligation IS divModExistZero's statement — the guard that
	// makes one Skolem pair definable over all of ℕ×ℕ.
	Existence: []Action{Cite(divModExistZero)},
})}

// ---------------------------------------------------------------------------
// Division — the division equation, where there is one
// ---------------------------------------------------------------------------

// Division — the spec at a nonzero divisor. The COND guard is decided by
// the hypothesis, so the else-branch — the division equation together
// with the remainder bound — is all that is left.
var Division = divisionThm{family.Add(registry.ProofEntry{
	Name: "Division",
	Key:  "prop_64ac3f58b337991b",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n:num.",
			Hypotheses: []string{
				"n ≠ 0",
			},
			Conclusion: "m = div(m, n) * n + rem(m, n) ∧ rem(m, n) < n",
		},
		func(a *Argument, m, n Term, _ Fact) {
			a.Do(
				// The spec at m = m₀, n = n₀.
				Cite(divModSpec, m, n),
				CondRewrite(), // n₀ ≠ 0 decides the guard: the else-branch
				Basic(),
			)
		}),
})}

// ---------------------------------------------------------------------------
// DivZero · ModZero — the convention at divisor zero
// ---------------------------------------------------------------------------

// DivZero — dividing by zero yields zero. The spec at m = n, n = 0 takes
// its then-branch, whose first conjunct is exactly this. (Not to be
// confused with `ZeroDiv`, nat_div(0, n) = 0.)
var DivZero = divZeroThm{family.Add(registry.ProofEntry{
	Name: "DivZero",
	Key:  "prop_e27ffa167d7b4c1b",
	Build: family.Theorem("∀n:num. div(n, 0) = 0",
		func(a *Argument, n Term) {
			a.Do(
				// The spec at m = n₀, n = 0.
				Cite(divModSpec, n, ops(a.Ctx()).Zero),
				TrivialNormalized(),
			)
		}),
})}

// ModZero — a number modulo zero is itself, the second conjunct of the
// same then-branch DivZero reads its first from. (Not to be confused
// with `ZeroMod`, nat_mod(0, n) = 0.)
var ModZero = modZeroThm{family.Add(registry.ProofEntry{
	Name: "ModZero",
	Key:  "prop_6ea41364f1170fe9",
	Build: family.Theorem("∀n:num. rem(n, 0) = n",
		func(a *Argument, n Term) {
			a.Do(
				// The spec at m = n₀, n = 0.
				Cite(divModSpec, n, ops(a.Ctx()).Zero),
				TrivialNormalized(),
			)
		}),
})}

// ---------------------------------------------------------------------------
// Uniqueness of the quotient and remainder
// ---------------------------------------------------------------------------
//
// The definitional layer above mints nat_div and nat_mod and shows the pair they name
// IS a division with remainder. This tier shows it is the ONLY one: a
// representation m = q·n + r whose remainder is below the divisor
// determines both q and r. So the file is one theorem and three
// readings of it:
//
// 1. divModUniqLemma — two such representations of the same m agree.
// Stated without nat_div and nat_mod, so it says nothing about which
// representation a particular pair of functions picks.
// 2. DivModUniq — Division supplies a second representation at
// (nat_div(m,n), nat_mod(m,n)), so that is the representation.
// 3. DivUniq / ModUniq — one conjunct of DivModUniq each.
//
// DAG (within this file):
//
// 	divModUniqLemma : [nat_arith.AddLeftZeroClause, nat_arith.MulLeftZeroClause, nat_arith.AddAssoc,
// 	 nat_arith.AddEqLCancel, nat_arith.RightAddDistrib, nat_arith.MulSym, nat_arith.AddZero,
// 	 nat_order.LessEqMulNonzero]
// 	 + nat_order.{LessEqTotal, LessEqExists, LessEqAdd,
// 	 LessEqTrans, NotLessEq}
// 	DivModUniq : [Division, divModUniqLemma] + nat_order.{lessThanZeroClause}
// 	DivUniq : [DivModUniq]
// 	ModUniq : [DivModUniq]
//
// All four are stated in their natural ⇒-form.

// ---------------------------------------------------------------------------
// divModUniqLemma — a bounded remainder pins the representation
// ---------------------------------------------------------------------------

// divModUniqLemma — a number has at most one representation as
// quotient·divisor + remainder with the remainder below the divisor.
// Band B: the nat_div/nat_mod-free core the three named theorems below are
// read off — DivModUniq by combining it with Division, and the other
// two by projecting DivModUniq.
//
// The argument is symmetric in the two representations, so it is
// written ONCE — `divModUniqOneSided` — under the standing assumption
// that the first quotient is the smaller of the two; totality of ≤
// covers the other order by running the same step with the roles
// exchanged. Under q ≤ p, write p = q + d and cancel the shared q·n:
//
//	q·n + r = m = (q + d)·n + s = q·n + (d·n + s) so r = d·n + s.
//
// A positive d would fit a whole copy of the divisor below r —
// n ≤ n·d = d·n ≤ d·n + s = r — which r < n forbids. So d = 0 and the
// two representations are the same one.
var divModUniqLemma = divModUniqLemmaThm{family.Add(registry.ProofEntry{
	Name: "divModUniqLemma",
	Key:  "prop_3d93cfe249db8b78",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n q₁ r₁ q₂ r₂:num.",
			Hypotheses: []string{
				"m = q₁ * n + r₁",
				"r₁ < n",
				"m = q₂ * n + r₂ ∧ r₂ < n",
			},
			Conclusion: "q₁ = q₂ ∧ r₁ = r₂",
		},
		// m is bound but never named: it is the value the two representations
		// share, and the argument only ever reaches it through `reps`.
		func(a *Argument, m, n Term, q1, r1, q2, r2 *TermWrapper, reps Fact) {
			v := ops(a.Ctx())
			a.Cases(v.LessEq(q1, q2))
			a.When(
				"q₁ ≤ q₂: run the one-sided step with the first representation the narrower one",
				func(b *Argument, le Fact) {
					divModUniqOneSided(b, v, n, q1, r1, q2, r2, le, reps)
				})
			a.Otherwise(
				"q₂ ≤ q₁: the failed side of a total order is the other order — the same step, roles exchanged",
				func(b *Argument, notLe Fact) {
					le := b.Have(
						"the quotients are comparable, so failing one way settles the other",
						MakeProp(v.LessEq(q2, q1)),
						By(notLe, At(nat_order.LessEqTotal, q1, q2))) // q₁ ≤ q₂ ∨ q₂ ≤ q₁
					divModUniqOneSided(b, v, n, q2, r2, q1, r1, le, reps)
				})
		}),
})}

// divModUniqOneSided runs the argument above under q ≤ p. `reps`
// carries both representations and both remainder bounds, but only the
// bound on the NARROWER remainder r is used — which is exactly what
// makes proving one direction enough.
//
// Unlike the chapter's other extracted step (the definitional layer's
// divModExistBelow, which returns an Action because it is a Have's
// proof) this one is a plain function: both call sites are Case bodies
// that already hold the *Argument it runs in.
func divModUniqOneSided(
	a *Argument,
	v *divmodOps,
	n, q Term,
	r, p *TermWrapper,
	s Term,
	le, reps Fact,
) {
	d := a.Ctx().Var("d", NumType) // the ∃-binder of the shift below

	d0, shift := a.Obtain(
		"q ≤ p realizes the larger quotient as the smaller one shifted by d",
		MakeProp(Exists(d)(p.Eq(v.Add(q, d)))),
		// LessEqExists fires as a goal rewrite: ↦ q ≤ p, which is the assumption.
		By(le, nat_order.LessEqExists))

	qn, dn := v.Mul(q, n), v.Mul(d0, n)

	cancel := a.Have(
		"cancelling the q·n both representations share leaves r as s plus d₀ copies of n",
		MakeProp(r.Eq(v.Add(dn, s))),
		By(
			reps,
			shift,
			At(nat_arith.RightAddDistrib, q, d0, n), // (q + d₀)·n = q·n + d₀·n
			At(nat_arith.AddAssoc, qn, dn, s),       // q·n + (d₀·n + s) = (q·n + d₀·n) + s
			At(nat_arith.AddEqLCancel, qn, r, v.Add(dn, s)), // r = d₀·n + s ⇔ q·n + r = q·n + (d₀·n + s)
		))

	dZero := a.Have(
		"d₀ vanishes: a positive one fits a whole copy of the divisor below r, and r < n",
		MakeProp(d0.Eq(v.Zero)),
		By(
			reps,
			cancel,
			At(nat_order.LessEqMulNonzero, n, d0), // d₀ = 0 ∨ n ≤ n·d₀
			At(nat_arith.MulSym, n, d0),           // n·d₀ = d₀·n
			At(nat_order.LessEqAdd, dn, s),        // d₀·n ≤ d₀·n + s, which cancel says is r
			At(nat_order.LessEqTrans, n, dn, r),   // n ≤ d₀·n and d₀·n ≤ r give n ≤ r
			At(nat_order.NotLessEq, n, r),         // ¬(n ≤ r) ⇔ r < n
		))

	a.Show(
		"with d₀ = 0 both representations collapse onto one: p = q + 0 and r = 0·n + s",
		By(
			shift,
			cancel,
			dZero,
			At(nat_arith.AddZero, q),           // q = q + 0
			At(nat_arith.MulLeftZeroClause, n), // 0 = 0·n
			At(nat_arith.AddLeftZeroClause, s), // s = 0 + s
		))
}

// ---------------------------------------------------------------------------
// DivModUniq — nat_div and nat_mod are the representation
// ---------------------------------------------------------------------------

// DivModUniq — anyone who exhibits a representation of m with a
// remainder below n has exhibited nat_div(m, n) and nat_mod(m, n). Division
// supplies the competing representation and divModUniqLemma identifies
// the two.
var DivModUniq = divModUniqThm{family.Add(registry.ProofEntry{
	Name: "DivModUniq",
	Key:  "prop_7557e8530ab9874c",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n q r:num.",
			Hypotheses: []string{
				"m = q * n + r",
				"r < n",
			},
			Conclusion: "div(m, n) = q ∧ rem(m, n) = r",
		},
		func(a *Argument, m, n, q, r Term, rep Fact) {
			v := ops(a.Ctx())
			div, mod := v.Div(m, n), v.Mod(m, n)

			a.Show(
				"Division supplies the second representation, and the two agree",
				By(
					rep,
					At(nat_order.LessThanZeroClause, r), // ¬(r₀ < 0), so r₀ < n₀ rules out n₀ = 0
					// Division at m₀ ÷ n₀ — its escape clause n₀ = 0 is the one
					// lessThanZeroClause just killed.
					At(Division, m, n),
					// The lemma at (q₁, r₁) := (q₀, r₀), (q₂, r₂) := (nat_div, nat_mod).
					At(divModUniqLemma, m, n, q, r, div, mod),
				))
		}),
})}

// ---------------------------------------------------------------------------
// DivUniq · ModUniq — the two halves, separately
// ---------------------------------------------------------------------------

// DivUniq — the quotient half of DivModUniq, which is how the quotient
// is usually recognised: exhibit any remainder below the divisor and
// the quotient you used is nat_div.
var DivUniq = divUniqThm{family.Add(registry.ProofEntry{
	Name: "DivUniq",
	Key:  "prop_af09678516dfb250",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n q r:num.",
			Hypotheses: []string{
				"m = q * n + r",
				"r < n",
			},
			Conclusion: "div(m, n) = q",
		},
		func(a *Argument, m, n, q, r Term, rep Fact) {
			a.Show(
				"the quotient conjunct of DivModUniq at the same point",
				By(rep, At(DivModUniq, m, n, q, r)))
		}),
})}

// ModUniq — the remainder half, read off the same instance.
var ModUniq = modUniqThm{family.Add(registry.ProofEntry{
	Name: "ModUniq",
	Key:  "prop_d0a3435816312099",
	Build: family.Theorem(
		Statement{
			Binders: "∀m n q r:num.",
			Hypotheses: []string{
				"m = q * n + r",
				"r < n",
			},
			Conclusion: "rem(m, n) = r",
		},
		func(a *Argument, m, n, q, r Term, rep Fact) {
			a.Show(
				"the remainder conjunct of DivModUniq at the same point",
				By(rep, At(DivModUniq, m, n, q, r)))
		}),
})}

// ---------------------------------------------------------------------------
// The values nat_div and nat_mod actually take
// ---------------------------------------------------------------------------
//
// Uniqueness proved that a representation m = q·n + r with r < n determines
// both q and r. That turns every value question in this file into an
// exhibition: write the dividend in that form, check the remainder is
// small enough, and uniqueness names the answer. Nothing here inducts.
//
// Three representations carry four of the six members:
//
// 	0 = 0·n + 0 ZeroMod, ZeroDiv — dividing zero
// 	m = 0·n + m ModLessThan — a number below the divisor is its own remainder
// 	n = 1·n + 0 DivRefl — a nonzero number goes into itself once
//
// The remaining two read a vanishing remainder as divisibility
// (ModEqZero) and apply that at n itself (ModRefl).
//
// The divisor-zero case is the recurring wrinkle: where n = 0 no
// remainder is below the divisor at all, so uniqueness says nothing and
// the definitional convention (DivZero / ModZero) answers instead. The three
// members that argue directly and carry no hypothesis split on it;
// ModLessThan and DivRefl get the bound from their own hypothesis, and
// ModRefl inherits the split from ModEqZero.
//
// DAG (within this file):
//
// 	ZeroMod : [ModUniq, ModZero, nat_arith.MulLeftZeroClause, nat_arith.AddLeftZeroClause]
// 	 + nat_order.{posIffNonzero}
// 	ZeroDiv : [DivUniq, DivZero, nat_arith.MulLeftZeroClause, nat_arith.AddLeftZeroClause]
// 	 + nat_order.{posIffNonzero}
// 	ModLessThan : [ModUniq, nat_arith.MulLeftZeroClause, nat_arith.AddLeftZeroClause]
// 	DivRefl : [DivUniq, nat_arith.OneMul, nat_arith.AddZero] + nat_order.{posIffNonzero}
// 	ModEqZero : [Division, ModUniq, ModZero, nat_arith.MulZero, nat_arith.AddZero]
// 	 + nat_order.{posIffNonzero}
// 	ModRefl : [ModEqZero, nat_arith.OneMul]

// ---------------------------------------------------------------------------
// ZeroMod · ZeroDiv — dividing zero
// ---------------------------------------------------------------------------

// ZeroMod — taking out no copy of the divisor leaves all of zero over,
// so 0 = 0·n + 0 is a division with remainder 0, and ModUniq names that
// remainder. The branch hypothesis is used in exactly one place, to put
// 0 below n: positivity IS non-zeroness.
var ZeroMod = zeroModThm{family.Add(registry.ProofEntry{
	Name: "ZeroMod",
	Key:  "prop_28f5b02fb2d62e44",
	Build: family.Theorem("∀n:num. rem(0, n) = 0",
		func(a *Argument, n *TermWrapper) {
			v := ops(a.Ctx())
			a.Cases(n.Eq(v.Zero))
			a.When(
				"n₀ = 0: no remainder is below the divisor, so uniqueness is vacuous and the convention answers",
				func(b *Argument, isZero Fact) {
					b.Show(
						"the convention gives rem(0, 0) = 0",
						By(isZero, At(ModZero, v.Zero))) // 0 = nat_mod(0, 0)
				})
			a.Otherwise(
				"n₀ ≠ 0: 0 = 0·n₀ + 0 is a division with remainder 0, and 0 < n₀ puts that remainder in range",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"so the remainder of that representation is the remainder",
						By(
							Normalized,
							nonzero,
							At(nat_order.PosIffNonzero, n),          // n₀ ≠ 0 ⇔ 0 < n₀
							At(nat_arith.MulLeftZeroClause, n),      // 0 = 0·n₀
							At(nat_arith.AddLeftZeroClause, v.Zero), // 0 = 0 + 0
							// ModUniq at (dividend, divisor, quotient, remainder)
							// := (0, n₀, 0, 0).
							At(ModUniq, v.Zero, n, v.Zero, v.Zero),
						))
				})
		}),
})}

// ZeroDiv — the same representation as ZeroMod, read for its quotient
// instead of its remainder; mutatis mutandis throughout.
var ZeroDiv = zeroDivThm{family.Add(registry.ProofEntry{
	Name: "ZeroDiv",
	Key:  "prop_348f906d020f36e3",
	Build: family.Theorem("∀n:num. div(0, n) = 0",
		func(a *Argument, n *TermWrapper) {
			v := ops(a.Ctx())
			a.Cases(n.Eq(v.Zero))
			a.When(
				"n₀ = 0: no remainder is below the divisor, so uniqueness is vacuous and the convention answers",
				func(b *Argument, isZero Fact) {
					b.Show(
						"the convention gives div(0, 0) = 0",
						By(isZero, At(DivZero, v.Zero))) // 0 = nat_div(0, 0)
				})
			a.Otherwise(
				"n₀ ≠ 0: 0 = 0·n₀ + 0 is a division with remainder 0, and 0 < n₀ puts that remainder in range",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"so the quotient of that representation is the quotient",
						By(
							Normalized,
							nonzero,
							At(nat_order.PosIffNonzero, n),          // n₀ ≠ 0 ⇔ 0 < n₀
							At(nat_arith.MulLeftZeroClause, n),      // 0 = 0·n₀
							At(nat_arith.AddLeftZeroClause, v.Zero), // 0 = 0 + 0
							// DivUniq at the same four slots as ModUniq above:
							// (0, n₀, 0, 0).
							At(DivUniq, v.Zero, n, v.Zero, v.Zero),
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// ModLessThan — below the divisor, a number is its own remainder
// ---------------------------------------------------------------------------

// ModLessThan — dividing m by a larger n takes out no copy of n at all, so
// the whole of m is what is left over: m = 0·n + m, a representation
// whose remainder m is below n by hypothesis. ModUniq turns that into
// the value of nat_mod, and the zero clauses of · and of + are what make
// 0·n + m the same number as m.
var ModLessThan = modLessThanThm{family.Add(registry.ProofEntry{
	Name: "ModLessThan",
	Key:  "prop_ecfdc7d8078caca9",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m < n",
		},
		Conclusion: "rem(m, n) = m",
	},
		func(a *Argument, m, n Term, below Fact) {
			v := ops(a.Ctx())
			a.Show(
				"take out no copy of n₀: the representation m₀ = "+
					"0·n₀ + m₀ leaves remainder m₀, which m₀ < n₀ bounds",
				By(
					below,
					// ModUniq at (dividend, divisor, quotient, remainder)
					// := (m₀, n₀, 0, m₀).
					At(ModUniq, m, n, v.Zero, m),
					At(nat_arith.MulLeftZeroClause, n), // 0 = 0·n₀
					nat_arith.AddLeftZeroClause,
				))
		}),
})}

// ---------------------------------------------------------------------------
// DivRefl — a nonzero number goes into itself once
// ---------------------------------------------------------------------------

// DivRefl — one copy of n comes out of n and nothing is left over:
// n = 1·n + 0, a representation whose remainder 0 is below n precisely
// because n is nonzero. DivUniq turns that into the value of nat_div,
// nat_order.PosIffNonzero is what reads the remainder bound off the
// hypothesis, and nat_arith.OneMul with nat_arith.AddZero collapse 1·n + 0 to n.
var DivRefl = divReflThm{family.Add(registry.ProofEntry{
	Name: "DivRefl",
	Key:  "prop_58c8effe3f3ac23d",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"n ≠ 0",
		},
		Conclusion: "div(n, n) = 1",
	},
		func(a *Argument, n Term, nonzero Fact) {
			v := ops(a.Ctx())
			one := a.Ctx().Numeral(1) // the chapter vocabulary carries 0, not 1

			a.Show(
				"take out one copy of n₀: the representation n₀ = 1·n₀ + 0 leaves remainder 0, which n₀ ≠ 0 bounds",
				By(
					nonzero,
					// DivUniq at (dividend, divisor, quotient, remainder)
					// := (n₀, n₀, 1, 0).
					At(DivUniq, n, n, one, v.Zero),
					At(nat_arith.OneMul, n),  // n₀ = 1·n₀
					At(nat_arith.AddZero, n), // n₀ = n₀ + 0
					nat_order.PosIffNonzero,
				))
		}),
})}

// ---------------------------------------------------------------------------
// ModEqZero — a remainder vanishes exactly on the multiples
// ---------------------------------------------------------------------------

// ModEqZero — the divisor splits the argument, because a zero divisor
// has no division equation to appeal to:
//
//	n = 0 nat_mod(m, 0) is m, and 0 has only itself as a multiple, so
//	 both sides of the ⇔ say m = 0;
//	n ≠ 0 one instance each way round. From m = q·n, that is the
//	 representation m = q·n + 0, whose remainder uniqueness's
//	 ModUniq names — and 0 < n is what admits it. From
//	 nat_mod(m, n) = 0, the definitional division equation
//	 m = nat_div(m, n)·n + nat_mod(m, n) loses its remainder, so the
//	 multiplier is nat_div(m, n): read off a resident fact rather
//	 than constructed.
var ModEqZero = modEqZeroThm{family.Add(registry.ProofEntry{
	Name: "ModEqZero",
	Key:  "prop_bb56ebe458646682",
	Build: family.Theorem(
		"∀m n:num. rem(m, n) = 0 ⇔ ∃q:num. m = q * n",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			a.Cases(n.Eq(v.Zero))
			a.When(
				"n₀ = 0: both sides collapse to m₀ = 0, so the ⇔ needs no split",
				func(b *Argument, isZero Fact) {
					b.Show(
						"rem(m₀, 0) is m₀, and any multiple of 0 is 0",
						By(
							isZero,
							At(ModZero, m), // m₀ = nat_mod(m₀, 0)
							// Bare, not ground: the ⇐ direction reads
							// m₀ = 0 off SOME multiple of 0 without ever
							// naming which, so there is no instance to
							// ground at.
							nat_arith.MulZero))
				})
			a.Otherwise(
				"n₀ ≠ 0: with a division equation available the two directions separate",
				func(b *Argument, nonzero Fact) {
					b.Iff()
					b.Forward(
						"the multiplier is the quotient: Division's representation loses its remainder",
						func(c *Argument, noRem Fact) {
							quot := v.Div(m, n)
							c.Take(quot) // the multiplier, read off Division rather than constructed
							c.Show(
								"what is left of the division equation once rem(m₀, n₀) is 0",
								By(noRem, nonzero, At(Division, m, n), nat_arith.AddZero))
						})
					b.Backward(
						"m₀ = q₀·n₀ is a representation whose remainder is 0, and 0 < n₀ is what admits it",
						func(c *Argument, mult Fact) {
							q0, rep := c.Unpack(mult) // m₀ = q₀ · n₀
							c.Show(
								"so ModUniq names that remainder",
								By(
									rep,
									nonzero,
									At(ModUniq, m, n, q0, v.Zero),  // 0 < n₀ ∧ m₀ = q₀·n₀ + 0 ⇒ nat_mod(m₀, n₀) = 0
									At(nat_order.PosIffNonzero, n), // n₀ ≠ 0 ⇔ 0 < n₀
									nat_arith.AddZero))
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// ModRefl — a number leaves no remainder on itself
// ---------------------------------------------------------------------------

// ModRefl — n is its own multiple, 1·n, so ModEqZero at (n, n) settles
// it. nat_arith.OneMul is where 1·n = n lives.
var ModRefl = modReflThm{family.Add(registry.ProofEntry{
	Name: "ModRefl",
	Key:  "prop_55a477c7b49c6fee",
	Build: family.Theorem("∀n:num. rem(n, n) = 0",
		func(a *Argument, n Term) {
			a.Show(
				"n₀ = 1·n₀ exhibits n₀ as a multiple of itself",
				By(
					Normalized,
					At(ModEqZero, n, n),      // nat_mod(n₀, n₀) = 0 ⇔ ∃q. n₀ = q·n₀
					At(nat_arith.OneMul, n))) // n₀ = 1·n₀
		}),
})}

// ---------------------------------------------------------------------------
// How far a division can reach
// ---------------------------------------------------------------------------
//
// The part above read off the values nat_div and nat_mod take at particular points.
// This tier bounds them everywhere: neither the quotient nor the
// remainder can exceed the dividend, the divisor's copies taken out of
// the dividend are still inside it, the quotient vanishes exactly below
// the divisor, and — the tier's real content — the quotient is
// characterized by an adjunction.
//
// 	DivMulLessEq the copies taken out are still inside
// 	DivLessEq, ModLessEq a division cannot grow its dividend
// 	DivEqZero the quotient vanishes exactly below the divisor
// 	LessEqRightDivEq the division adjunction
// 	FloorDoubleBound doubling the dividend doubles the quotient, give or take one
//
// The members argue from the definitional division equation
// m = nat_div(m,n)·n + nat_mod(m,n), so a member whose statement carries no
// hypothesis splits on the divisor, where that equation does not exist.
// What answers in that branch differs: DivLessEq, ModLessEq and LessEqRightDivEq appeal
// to the definitional convention, while DivMulLessEq needs no convention at all —
// its product collapses by ·'s own zero clause.
//
// DivMulLessEq comes first because the bound it states — the divisor's
// copies are inside the dividend — is also a step of DivLessEq's and of
// LessEqRightDivEq's, and both cite it rather than re-read the equation. That
// bound has one owner here.
//
// LessEqRightDivEq is why the rest of the chapter can reason about nat_div without
// unfolding it: it says dividing by a is right adjoint to multiplying
// by a, so a bound on a quotient may always be traded for a bound on a
// product, and conversely.
//
// DAG (within this file):
//
// 	DivMulLessEq : [Division, nat_arith.MulLeftZeroClause, nat_arith.MulSym]
// 	 + nat_order.{LessEqAdd, ZeroLessEq}
// 	DivLessEq : [DivMulLessEq, DivZero, nat_order.LessEqMulNonzero, nat_arith.MulSym]
// 	 + nat_order.{LessEqTrans, ZeroLessEq}
// 	ModLessEq : [Division, ModZero, nat_arith.AddSym]
// 	 + nat_order.{LessEqAdd, LessEqRefl}
// 	DivEqZero : [Division, DivUniq, nat_arith.MulLeftZeroClause, nat_arith.AddLeftZeroClause]
// 	LessEqRightDivEq : [Division, DivMulLessEq, nat_arith.MulSuc, nat_arith.MulSym, nat_arith.AddSym]
// 	 + nat_order.{LessEqMulCancel, LessEqTrans, LessEqAddCancel,
// 	 NotLessEq, SucLessEqIffLessThan}
// 	FloorDoubleBound : [Division, LessEqRightDivEq]

// ---------------------------------------------------------------------------
// DivMulLessEq — the quotient never overshoots
// ---------------------------------------------------------------------------

// DivMulLessEq — the copies of the divisor taken out of m are still inside
// m. The divisor splits the argument, as everywhere in this
// sub-chapter:
//
//	n = 0 nothing comes out — the product is 0·nat_div(m, 0), which nat_arith.Mul's
//	 zero clause collapses to 0, and 0 is below everything;
//	n ≠ 0 Division writes m as nat_div(m, n)·n + nat_mod(m, n), which exhibits
//	 the product as a SUMMAND of m, and a summand is bounded by
//	 its sum.
var DivMulLessEq = divMulLessEqThm{family.Add(registry.ProofEntry{
	Name: "DivMulLessEq",
	Key:  "prop_db32d4d2574a6d56",
	Build: family.Theorem("∀m n:num. n * div(m, n) ≤ m",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			quot := v.Div(m, n)    // how many copies of n₀ come out of m₀
			prod := v.Mul(quot, n) // the part of m₀ those copies fill

			a.Cases(n.Eq(v.Zero))
			a.When(
				"n₀ = 0: no copy of the divisor comes out at all, and 0 is below every number",
				func(b *Argument, isZero Fact) {
					b.Show(
						"the product collapses to 0",
						By(
							isZero,
							At(nat_arith.MulLeftZeroClause, quot), // 0 = 0·nat_div(m₀, n₀)
							At(nat_order.ZeroLessEq, m)))          // 0 ≤ m₀
				})
			a.Otherwise(
				"n₀ ≠ 0: the copies that come out are a summand of m₀, and a summand is bounded by its sum",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"Division makes div(m₀, n₀)·n₀ that summand; nat_arith.MulSym "+
							"puts its factors the way the statement writes them",
						By(
							nonzero,
							At(Division, m, n),
							At(nat_arith.MulSym, n, quot), // n₀·nat_div(m₀, n₀) = nat_div(m₀, n₀)·n₀
							// nat_div(m₀,n₀)·n₀ ≤ nat_div(m₀,n₀)·n₀ + nat_mod(m₀,n₀)
							At(nat_order.LessEqAdd, prod, v.Mod(m, n))))
				})
		}),
})}

// ---------------------------------------------------------------------------
// DivLessEq — a quotient never exceeds its dividend
// ---------------------------------------------------------------------------

// DivLessEq — the quotient is buried one layer deeper in the division
// equation than the remainder is, so the nonzero case takes two steps
// rather than one: nat_order.LessEqMulNonzero lifts the quotient to its product with
// the divisor (a nonzero factor cannot shrink it), that product's bound
// is DivMulLessEq's whole statement — cited, up to nat_arith.MulSym, rather than
// re-derived — and nat_order.LessEqTrans chains the two. Where the
// divisor is zero there is no equation to read and DivZero answers
// instead: the quotient is 0, below everything.
var DivLessEq = divLessEqThm{family.Add(registry.ProofEntry{
	Name: "DivLessEq",
	Key:  "prop_bc1b98f94503db0b",
	Build: family.Theorem("∀m n:num. div(m, n) ≤ m",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			quot := v.Div(m, n)
			prod := v.Mul(quot, n) // the part of m₀ those copies fill

			a.Cases(n.Eq(v.Zero))
			a.When(
				"n₀ = 0: no division equation to read, and the convention puts the quotient at 0",
				func(b *Argument, isZero Fact) {
					b.Show(
						"0 is below every natural number",
						By(
							isZero,
							At(DivZero, m),               // 0 = nat_div(m₀, 0)
							At(nat_order.ZeroLessEq, m))) // 0 ≤ m₀
				})
			a.Otherwise(
				"n₀ ≠ 0: the quotient sits below its own product with "+
					"n₀, and DivMulLessEq already bounds that product by m₀",
				func(b *Argument, nonzero Fact) {
					grow := b.Have(
						"scaling by the nonzero n₀ cannot shrink the quotient",
						MakeProp(v.LessEq(quot, prod)),
						// n₀ = 0 ∨ nat_div(m₀,n₀) ≤ nat_div(m₀,n₀)·n₀ — note the
						// SCALED slot is second here, not the divisor.
						By(nonzero, At(nat_order.LessEqMulNonzero, quot, n)))

					part := b.Have(
						"and what came out of m₀ is still inside it",
						MakeProp(v.LessEq(prod, m)),
						// DivMulLessEq holds at every divisor, so this step
						// takes no guard; nat_arith.MulSym turns its n₀·nat_div(m₀,n₀)
						// into the product nat_order.LessEqMulNonzero just produced.
						By(At(DivMulLessEq, m, n), At(nat_arith.MulSym, n, quot)))

					b.Show(
						"the two bounds meet at that product",
						By(grow, part, At(nat_order.LessEqTrans, quot, prod, m)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// ModLessEq — a remainder never exceeds its dividend
// ---------------------------------------------------------------------------

// ModLessEq — the remainder is already a summand of the division equation,
// so the nonzero case is one step: nat_order.LessEqAdd bounds a summand
// by the sum, and nat_arith.AddSym is what puts the remainder on the side that
// lemma bounds (it bounds the LEFT summand; the division equation
// writes the remainder on the right). Where the divisor is zero,
// ModZero says the whole of m is left over and reflexivity finishes.
var ModLessEq = modLessEqThm{family.Add(registry.ProofEntry{
	Name: "ModLessEq",
	Key:  "prop_f48df88da2f6ec5e",
	Build: family.Theorem("∀m n:num. rem(m, n) ≤ m",
		func(a *Argument, m Term, n *TermWrapper) {
			v := ops(a.Ctx())
			rem := v.Mod(m, n)
			prod := v.Mul(v.Div(m, n), n) // the part of m₀ the divisor's copies fill

			a.Cases(n.Eq(v.Zero))
			a.When(
				"n₀ = 0: no copy of the divisor comes out, so the convention leaves all of m₀ over",
				func(b *Argument, isZero Fact) {
					b.Show(
						"a number is at most itself",
						By(
							isZero,
							At(ModZero, m),               // m₀ = nat_mod(m₀, 0)
							At(nat_order.LessEqRefl, m))) // m₀ ≤ m₀
				})
			a.Otherwise(
				"n₀ ≠ 0: the remainder is the second part m₀ splits into, so re-order the sum to bound it",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"what is left over is at most what it was left over from",
						By(
							Normalized,
							nonzero,
							At(Division, m, n),
							// nat_div(m₀,n₀)·n₀ + nat_mod(m₀,n₀) = nat_mod(m₀,n₀) + nat_div(m₀,n₀)·n₀
							At(nat_arith.AddSym, prod, rem),
							// nat_mod(m₀,n₀) ≤ nat_mod(m₀,n₀) + nat_div(m₀,n₀)·n₀, which that flip makes m₀
							At(nat_order.LessEqAdd, rem, prod)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// DivEqZero — the quotient vanishes exactly below the divisor
// ---------------------------------------------------------------------------

// DivEqZero — each direction is one instance of a tier already in hand,
// and the two use disjoint equipment:
//
//	⇐ below the divisor no copy of it comes out, so m = 0·n + m is a
//	 representation whose remainder m the hypothesis m < n bounds, and
//	 DivUniq names the quotient 0. This is ModLessThan's argument read for
//	 its quotient instead of its remainder.
//	⇒ at quotient 0 the division equation m = nat_div(m, n)·n + nat_mod(m, n)
//	 collapses to m = nat_mod(m, n), and its own second conjunct puts that
//	 below n.
//
// So n ≠ 0 is used in ⇒ alone, where it is what buys a division
// equation at all; ⇐ never needs it, and its premise list says so. What
// collapses 0·n + x to x either way is the left zero clause of · and
// of +.
var DivEqZero = divEqZeroThm{family.Add(registry.ProofEntry{
	Name: "DivEqZero",
	Key:  "prop_24600305c12ce37e",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"n ≠ 0",
		},
		Conclusion: "div(m, n) = 0 ⇔ m < n",
	},
		func(a *Argument, m, n Term, nonzero Fact) {
			v := ops(a.Ctx())
			a.Iff()
			a.Forward(
				"a vanishing quotient takes nothing out, so the whole of m₀ is what is left over",
				func(b *Argument, noQuotient Fact) {
					b.Show(
						"the division equation collapses to m₀ = rem(m₀, "+
							"n₀), and its own remainder bound puts that below n₀",
						By(
							noQuotient,
							nonzero,
							At(Division, m, n),
							At(nat_arith.MulLeftZeroClause, n), // 0 = 0·n₀
							nat_arith.AddLeftZeroClause,
						))
				})
			a.Backward(
				"take out no copy of n₀: the representation m₀ = "+
					"0·n₀ + m₀ leaves remainder m₀, which m₀ < n₀ bounds",
				func(b *Argument, below Fact) {
					b.Show(
						"so the quotient of that representation is the quotient",
						By(
							below,
							// DivUniq at (dividend, divisor, quotient, remainder)
							// := (m₀, n₀, 0, m₀).
							At(DivUniq, m, n, v.Zero, m),
							At(nat_arith.MulLeftZeroClause, n), // 0 = 0·n₀
							nat_arith.AddLeftZeroClause,
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// LessEqRightDivEq — dividing by a is right adjoint to multiplying by it
// ---------------------------------------------------------------------------

// LessEqRightDivEq — nat_div(b, a) is the LARGEST n whose a-fold multiple still
// fits inside b, which is what makes division a right adjoint. The two
// directions divide the equipment between them: ⇐ runs on Division,
// which accounts for the leftover exactly as nat_mod(b, a) < a, and ⇒ on
// DivMulLessEq, which says a·nat_div(b, a) fits inside b. Neither cites the
// other's fact.
//
//	⇐ suppose n overshoots the quotient. Then n is at least one past
//	 it, so a whole extra copy of a fits inside b on top of the
//	 quotient's copies — but Division leaves only nat_mod(b, a) there,
//	 and that is smaller than a.
//	⇒ multiply the bound through by a and chain onto DivMulLessEq's.
//
// a ≠ 0 is used in ⇐ alone. In ⇒ the conclusion is free at a = 0, since
// 0 ≤ b holds outright, and that direction's premise list says so.
//
// "One past the quotient" is written suc(nat_div(b, a)) rather than
// nat_div(b, a) + 1: suc is what ·'s recursion clause already speaks, so
// nat_arith.MulSuc expands the extra copy directly and no numeral arithmetic
// enters the proof.
var LessEqRightDivEq = lessEqRightDivEqThm{family.Add(registry.ProofEntry{
	Name: "LessEqRightDivEq",
	Key:  "prop_1bcc9dcd07133d9c",
	// The context is `arg` because the statement itself binds a.
	Build: family.Theorem(
		Statement{
			Binders: "∀a b n:num.",
			Hypotheses: []string{
				"a ≠ 0",
			},
			Conclusion: "n ≤ div(b, a) ⇔ a * n ≤ b",
		},
		func(arg *Argument, a, b, n Term, nonzero Fact) {
			v := ops(arg.Ctx())
			quot := v.Div(b, a)     // the copies of a₀ that come out of b₀
			next := v.Suc(quot)     // one copy more than that
			rem := v.Mod(b, a)      // what is left over once they have come out
			block := v.Mul(quot, a) // the part of b₀ those copies fill

			arg.Iff()
			arg.Forward(
				"from n₀ ≤ div(b₀, a₀): multiplying the bound by a₀ lands it under DivMulLessEq's",
				func(c *Argument, below Fact) {
					c.Show(
						"a₀·n₀ ≤ a₀·div(b₀, a₀), and a₀·div(b₀, a₀) is inside b₀",
						By(
							below,
							// a₀·n₀ ≤ a₀·nat_div(b₀,a₀) ⇔ n₀ ≤ nat_div(b₀,a₀) ∨ a₀ = 0
							At(nat_order.LessEqMulCancel, a, n, quot),
							At(DivMulLessEq, b, a),
							At(nat_order.LessEqTrans, v.Mul(a, n), v.Mul(a, quot), b)))
				})
			arg.Backward(
				"from a₀·n₀ ≤ b₀: were n₀ past the quotient, one more whole copy of a₀ would fit inside b₀",
				func(c *Argument, fits Fact) {
					past := c.SupposeNot() // ¬(n₀ ≤ nat_div(b₀, a₀))

					oneMore := c.Have(
						"past the quotient means at least one past it, and that many copies of a₀ still fit",
						MakeProp(v.LessEq(v.Mul(a, next), b)),
						By(
							fits,
							past,
							At(nat_order.NotLessEq, n, quot), // ¬(n₀ ≤ nat_div(b₀,a₀)) ⇔ nat_div(b₀,a₀) < n₀
							At(nat_order.SucLessEqIffLessThan, quot, n), // nat_div(b₀,a₀) < n₀ ⇔ suc(nat_div(b₀,a₀)) ≤ n₀
							// a₀·suc(nat_div(b₀,a₀)) ≤ a₀·n₀ ⇔ suc(nat_div(b₀,a₀)) ≤ n₀ ∨ a₀ = 0
							At(nat_order.LessEqMulCancel, a, next, n),
							At(nat_order.LessEqTrans, v.Mul(a, next), v.Mul(a, n), b)))

					spare := c.Have(
						"re-spell that many copies: the quotient's own copies with one spare a₀ on top",
						MakeProp(v.LessEq(v.Add(block, a), b)),
						By(
							oneMore,
							At(nat_arith.MulSuc, a, quot),   // a₀·suc(nat_div(b₀,a₀)) = a₀ + a₀·nat_div(b₀,a₀)
							At(nat_arith.MulSym, a, quot),   // a₀·nat_div(b₀,a₀) = nat_div(b₀,a₀)·a₀
							At(nat_arith.AddSym, a, block))) // a₀ + nat_div(b₀,a₀)·a₀ = nat_div(b₀,a₀)·a₀ + a₀

					c.Show(
						"but Division leaves only rem(b₀, a₀) on top of those copies, "+
							"so cancelling them puts the spare a₀ below the remainder",
						By(
							Normalized,
							nonzero,
							spare,
							At(Division, b, a),
							// a₀ ≤ nat_mod(b₀,a₀) ⇔ nat_div(b₀,a₀)·a₀ + a₀ ≤ nat_div(b₀,a₀)·a₀ + nat_mod(b₀,a₀)
							At(nat_order.LessEqAddCancel, block, a, rem),
							At(nat_order.NotLessEq, a, rem))) // ¬(a₀ ≤ nat_mod(b₀,a₀)) ⇔ nat_mod(b₀,a₀) < a₀
				})
		}),
})}

// ---------------------------------------------------------------------------
// FloorDoubleBound — doubling the dividend doubles the quotient, give or take one
// ---------------------------------------------------------------------------

// FloorDoubleBound — doubling n doubles its quotient by d ≠ 0, give or take
// one: with n = q·d + r and r < d, 2n = 2q·d + 2r lies at or above 2q·d and
// below (2q + 2)·d.
var FloorDoubleBound = floorDoubleBoundThm{family.Add(registry.ProofEntry{
	Name: "FloorDoubleBound",
	Key:  "prop_6579eac65d2cd681",
	Build: family.Theorem(Statement{
		Binders: "∀n d:num.",
		Hypotheses: []string{
			"d ≠ 0",
		},
		Conclusion: "2 * div(n, d) ≤ div(2 * n, d) ∧ div(2 * n, d) ≤ 2 * div(n, d) + 1",
	},
		func(a *Argument, n, d *Expr[Nat], nonzero Fact) {
			double := a.TermAs[Nat]("2 * n")
			a.Show(
				"n = q·d + r with r < d puts 2n at or above 2q·d and below (2q + 2)·d",
				ByArith(
					nonzero,
					Division.At(n, d),
					LessEqRightDivEq.At(d, double, a.TermAs[Nat]("2 * div(n, d)")),
					LessEqRightDivEq.At(d, double, a.TermAs[Nat]("2 * div(n, d) + 2"))))
		}),
})}

// ---------------------------------------------------------------------------
// Division and the ring operations
// ---------------------------------------------------------------------------
//
// The parts above evaluated and bounded nat_div and nat_mod. This one says how
// they interact with multiplication and addition. Every member that
// argues at all argues the same way as the rest of the sub-chapter —
// write the dividend as q·n + r with r < n and let uniqueness name the
// answer — and ModMultAdd is the one that does not argue, being four
// instances of ModEq.
//
// 	DivMult, DivMult2 dividing a product by one of its factors, and
// 	 scaling dividend and divisor together
// 	ModEq adding a multiple of the modulus changes no
// 	 remainder — the congruence law
// 	ModMultAdd that addition leaves the remainder alone
// 	DivMultAdd and raises the quotient by exactly the
// 	 multiplier
//
// The last two are 4-conjunct bundles for different reasons; their entry
// docs say which.
//
// DAG (within this file):
//
// 	DivMult : [DivUniq, nat_arith.MulSym, nat_arith.AddZero] + nat_order.{posIffNonzero}
// 	DivMult2 : [Division, DivUniq, DivZero, nat_arith.MulZero, nat_arith.LeftAddDistrib,
// 	 nat_arith.MulAssoc, nat_arith.MulSym]
// 	 + nat_order.{LessEqMulCancel, NotLessEq}
// 	ModEq : [Division, ModUniq, nat_arith.RightAddDistrib, nat_arith.AddAssoc, nat_arith.AddSym,
// 	 nat_arith.MulZero, nat_arith.AddZero]
// 	ModMultAdd : [ModEq, nat_arith.AddSym, nat_arith.MulSym]
// 	DivMultAdd : [Division, DivUniq, nat_arith.RightAddDistrib, nat_arith.AddAssoc, nat_arith.MulSym,
// 	 nat_arith.AddSym]

// ---------------------------------------------------------------------------
// DivMult — a product divided by one of its factors is the other
// ---------------------------------------------------------------------------

// DivMult — m·n is ALREADY a division of itself by m: take out n copies
// of m and nothing is left over. So the proof exhibits that
// representation and lets DivUniq read the quotient off it, and the two
// things the representation owes are the two steps:
//
// - the remainder 0 must sit below the divisor, which for 0 is exactly
// m ≠ 0 — the only place the hypothesis is used;
// - m·n must literally be n·m + 0, since DivUniq writes the quotient
// on the LEFT of its product and accounts for a remainder even when
// there is none.
var DivMult = divMultThm{family.Add(registry.ProofEntry{
	Name: "DivMult",
	Key:  "prop_e92d9458160b8196",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≠ 0",
		},
		Conclusion: "div(m * n, m) = n",
	},
		func(a *Argument, m, n Term, nonzero Fact) {
			v := ops(a.Ctx())

			fits := a.Have(
				"a remainder of 0 still has to be below the divisor, and for m that is the hypothesis itself",
				"0 < m",
				By(nonzero, nat_order.PosIffNonzero))

			rep := a.Have(
				"read m·n as a division by m: n copies of m, nothing left over",
				"m * n = n * m + 0",
				Cite(nat_arith.MulSym, m, n), // m₀·n₀ = n₀·m₀ — the quotient's factor moves left
				Cite(nat_arith.AddZero),      // ↦ m₀·n₀ = n₀·m₀: the spare remainder comes off at the cite
			)

			a.Show(
				"DivUniq turns that representation into the quotient",
				By(
					fits,
					rep,
					// DivUniq at (dividend, divisor, quotient, remainder)
					// := (m₀·n₀, m₀, n₀, 0).
					At(DivUniq, v.Mul(m, n), m, n, v.Zero)))
		}),
})}

// ---------------------------------------------------------------------------
// DivMult2 — scaling dividend and divisor together leaves the quotient
// ---------------------------------------------------------------------------

// DivMult2 — the quotient of a division is unchanged when both sides are
// scaled by the same nonzero m. The proof again exhibits a
// representation, this time by scaling the one the definitional layer already supplies:
// multiplying n = nat_div(n,p)·p + nat_mod(n,p) through by m turns it into a
// representation of m·n by m·p with the SAME quotient and remainder m
// times as large.
//
// Whether that is a legal representation is the member's one real
// obligation, and it is where m ≠ 0 is used: a remainder must stay
// below its divisor, so m·nat_mod(n,p) < m·p is needed, and a strict
// multiplication cancellation is what supplies it. This corpus has no
// strict twin of nat_order.LessEqMulCancel, so the strict form is read
// off the non-strict one by duality: m·nat_mod(n,p) < m·p fails only if
// m·p ≤ m·nat_mod(n,p), which cancels the common m (nonzero) to
// p ≤ nat_mod(n,p) — and nat_mod(n,p) < p forbids that. Two
// nat_order.NotLessEq instances turn the two < into the two ≤ the
// cancellation speaks.
//
// The divisor p splits the argument, as everywhere in this
// sub-chapter, because at p = 0 there is no division equation to scale:
// m·0 is 0 by nat_arith.MulZero, so both sides are a division by zero and DivZero
// answers for each.
//
// The scaled representation writes its quotient's product as
// nat_div(n,p)·(m·p) — the divisor m·p kept whole — while distributing m
// over the equation produces m·(nat_div(n,p)·p). Those are the same three
// factors in a different arrangement, so one AC rearrangement of ·
// closes the gap and no further multiplication law is needed.
var DivMult2 = divMult2Thm{family.Add(registry.ProofEntry{
	Name: "DivMult2",
	Key:  "prop_65aaf20fb59ad6ad",
	Build: family.Theorem(Statement{
		Binders: "∀m n p:num.",
		Hypotheses: []string{
			"m ≠ 0",
		},
		Conclusion: "div(m * n, m * p) = div(n, p)",
	},
		func(a *Argument, m, n Term, p *TermWrapper, nonzero Fact) {
			ctx := a.Ctx()
			v := ops(ctx)

			quot := v.Div(n, p)     // how many copies of p₀ come out of n₀
			rem := v.Mod(n, p)      // what is left of n₀ once they have come out
			block := v.Mul(quot, p) // the part of n₀ those copies fill

			// The scaled division. Everything about it is m₀ times as large
			// EXCEPT quot, which is the theorem.
			scaledDividend := v.Mul(m, n) // m₀·n₀
			scaledDivisor := v.Mul(m, p)  // m₀·p₀
			scaledRem := v.Mul(m, rem)    // m₀·nat_mod(n₀, p₀)

			a.Cases(p.Eq(v.Zero))
			a.When(
				"p₀ = 0: scaling a zero divisor leaves it zero, so both sides fall back on the convention",
				func(b *Argument, isZero Fact) {
					b.Show(
						"each side is a division by 0, and there the quotient is 0",
						By(
							isZero,
							At(nat_arith.MulZero, m),    // 0 = m₀·0
							At(DivZero, scaledDividend), // 0 = nat_div(m₀·n₀, 0)
							At(DivZero, n)))             // 0 = nat_div(n₀, 0)
				})
			a.Otherwise(
				"p₀ ≠ 0: scale n₀'s division equation by m₀, having checked the scaled remainder still fits",
				func(b *Argument, nonzeroP Fact) {
					fits := b.Have(
						"were the scaled remainder NOT below the scaled divisor, "+
							"cancelling m₀ would put p₀ below its own remainder",
						MakeProp(v.LessThan(scaledRem, scaledDivisor)),
						By(
							nonzero,
							nonzeroP,
							At(Division, n, p), // nat_mod(n₀,p₀) < p₀
							// m₀·p₀ ≤ m₀·nat_mod(n₀,p₀) ⇔ p₀ ≤ nat_mod(n₀,p₀) ∨ m₀ = 0
							At(nat_order.LessEqMulCancel, m, p, rem),
							// the duality flips: each < above, as the ≤ the cancellation speaks
							At(nat_order.NotLessEq, p, rem), // ¬(p₀ ≤ nat_mod(n₀,p₀)) ⇔ nat_mod(n₀,p₀) < p₀
							// ¬(m₀·p₀ ≤ m₀·nat_mod(n₀,p₀)) ⇔ m₀·nat_mod(n₀,p₀) < m₀·p₀
							At(nat_order.NotLessEq, scaledDivisor, scaledRem),
						))

					scaled := b.Have(
						"multiplying n₀'s division equation through by m₀ scales every part of it but the quotient",
						MakeProp(scaledDividend.Eq(v.Add(v.Mul(quot, scaledDivisor), scaledRem))),
						By(
							nonzeroP,
							At(Division, n, p), // n₀ = nat_div(n₀,p₀)·p₀ + nat_mod(n₀,p₀)
							// m₀·(nat_div(n₀,p₀)·p₀ + nat_mod(n₀,p₀)) = m₀·(nat_div(n₀,p₀)·p₀) + m₀·nat_mod(n₀,p₀)
							At(nat_arith.LeftAddDistrib, m, block, rem),
							// keeping the divisor whole moves m₀ across nat_div(n₀, p₀)
							nat_arith.MulAC(ctx).Eq(v.Mul(quot, scaledDivisor), v.Mul(m, block)),
						))

					b.Show(
						"that exhibits m₀·n₀ divided by m₀·p₀ with quotient div(n₀, p₀), and DivUniq names it",
						By(
							fits,
							scaled,
							// DivUniq at (dividend, divisor, quotient, remainder)
							// := (m₀·n₀, m₀·p₀, nat_div(n₀,p₀), m₀·nat_mod(n₀,p₀)).
							At(DivUniq, scaledDividend, scaledDivisor, quot, scaledRem)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// ModEq — adding a multiple of the divisor leaves the remainder alone
// ---------------------------------------------------------------------------

// ModEq — the divisor splits the argument, as in this
// sub-chapter, but here the zero case appeals to no convention:
//
//	p = 0 q copies of nothing are nothing, so m and n are the same
//	 number and the two remainders are the same TERM. Neither the
//	 divisor-zero convention nor nat_div is touched.
//	p ≠ 0 Division writes n as nat_div(n,p)·p + nat_mod(n,p); folding the q
//	 further copies of p into that quotient exhibits m as
//	 (q + nat_div(n,p))·p + nat_mod(n,p), a representation of m by p whose
//	 remainder Division has already bounded — so ModUniq names it,
//	 and it is n's remainder unchanged.
//
// Folding the copies in is three rearrangements and nothing else: nat_arith.AddSym
// brings them to the front of the sum, nat_arith.AddAssoc regroups them against
// Division's product, nat_arith.RightAddDistrib collects the two products into
// one.
var ModEq = modEqThm{family.Add(registry.ProofEntry{
	Name: "ModEq",
	Key:  "prop_9ee845d8e84e70a",
	Build: family.Theorem(Statement{
		Binders: "∀m n p q:num.",
		Hypotheses: []string{
			"m = n + q * p",
		},
		Conclusion: "rem(m, p) = rem(n, p)",
	},
		func(a *Argument, m, n Term, p *TermWrapper, q Term, rep Fact) {
			v := ops(a.Ctx())
			quot := v.Div(n, p)     // the copies of p₀ already inside n₀
			rem := v.Mod(n, p)      // what n₀ leaves over
			block := v.Mul(quot, p) // the part of n₀ those copies fill
			extra := v.Mul(q, p)    // the q₀ further copies m₀ carries

			a.Cases(p.Eq(v.Zero))
			a.When(
				"p₀ = 0: q₀ copies of nothing are nothing, so m₀ "+
					"and n₀ are one number and their remainders one term",
				func(b *Argument, isZero Fact) {
					b.Show(
						"the hypothesis collapses to m₀ = n₀",
						By(
							rep,
							isZero,
							At(nat_arith.MulZero, q),  // 0 = q₀·0
							At(nat_arith.AddZero, n))) // n₀ = n₀ + 0
				})
			a.Otherwise(
				"p₀ ≠ 0: fold the q₀ further copies of p₀ into n₀'s "+
					"own quotient, which leaves n₀'s remainder standing",
				func(b *Argument, nonzero Fact) {
					b.Show(
						"the copies join div(n₀, p₀), and Division's own bound "+
							"on rem(n₀, p₀) admits the result, so ModUniq names it",
						By(
							nonzero,
							rep,
							At(Division, n, p),
							At(nat_arith.AddSym, n, extra), // n₀ + q₀·p₀ = q₀·p₀ + n₀
							// q₀·p₀ + (nat_div(n₀,p₀)·p₀ + nat_mod(n₀,p₀)) = (q₀·p₀ + nat_div(n₀,p₀)·p₀) + nat_mod(n₀,p₀)
							At(nat_arith.AddAssoc, extra, block, rem),
							At(nat_arith.RightAddDistrib, q, quot, p), // (q₀ + nat_div(n₀,p₀))·p₀ = q₀·p₀ + nat_div(n₀,p₀)·p₀
							// ModUniq at (dividend, divisor, quotient, remainder)
							// := (m₀, p₀, q₀ + nat_div(n₀,p₀), nat_mod(n₀,p₀)).
							At(ModUniq, m, p, v.Add(q, quot), rem),
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// ModMultAdd — ModEq in all four spellings of the shifted dividend
// ---------------------------------------------------------------------------

// ModMultAdd — four cites of one fact. Each conjunct is ModEq at a
// single point: the dividend is the addend plus some copies of the
// divisor, so its remainder is the addend's. No conjunct carries any
// reasoning of its own. What varies is only surface spelling — which
// side of the sum the copies sit on, and which factor of the product
// comes first — so each leg carries at most one commutation, nat_arith.AddSym to
// move the copies past the addend and nat_arith.MulSym to swap the product's
// factors, and the leg that already spells the sum ModEq's way carries
// neither.
var ModMultAdd = modMultAddThm{family.Add(registry.ProofEntry{
	Name: "ModMultAdd",
	Key:  "prop_93413e5537af4b31",
	// Each conjunct binds its own variables, so there is no ∀-prefix to
	// strip: flat-split the four-way conjunction, strip inside each leg, and
	// cite ModEq at that leg's own dividend. Every tuple below reads
	// (dividend, representative, modulus, multiplier) — ModEq's own binder
	// order.
	Build: family.Theorem(
		"(∀m n p:num. rem(m * n + p, n) = rem(p, n)) ∧ "+
			"((∀m n p:num. rem(n * m + p, n) = rem(p, n)) ∧ "+
			"    ((∀m n p:num. rem(p + m * n, n) = rem(p, n)) ∧ (∀m n p:num. rem(p + n * m, n) = rem(p, n))))",
		func(a *Argument) {
			v := ops(a.Ctx())

			// The Skolems each leg mints from its own binders (naming rule:
			// README §"Reading the proofs").
			m0 := Var("m_0", NumType)
			n0 := Var("n_0", NumType)
			p0 := Var("p_0", NumType)

			// The copies of the divisor, either way round.
			copies := v.Mul(m0, n0)
			flipped := v.Mul(n0, m0)

			a.Do(SplitConjAll(
				Case(
					"copies before the addend, factors as ModEq writes them: only the sum turns round",
					StripQuant(),
					By(
						At(ModEq, v.Add(copies, p0), p0, n0, m0),
						At(nat_arith.AddSym, copies, p0)), // m₀·n₀ + p₀ = p₀ + m₀·n₀
				),
				Case(
					"copies before the addend, divisor as the first factor: the sum turns round and the factors swap",
					StripQuant(),
					By(
						At(ModEq, v.Add(flipped, p0), p0, n0, m0),
						At(nat_arith.MulSym, n0, m0),       // n₀·m₀ = m₀·n₀
						At(nat_arith.AddSym, flipped, p0)), // n₀·m₀ + p₀ = p₀ + n₀·m₀
				),
				Case(
					"addend before the copies, factors as ModEq writes "+
						"them: this IS ModEq's spelling, so one cite closes it",
					StripQuant(),
					By(At(ModEq, v.Add(p0, copies), p0, n0, m0)),
				),
				Case(
					"addend before the copies, divisor as the first factor: only the factors swap",
					StripQuant(),
					By(At(ModEq, v.Add(p0, flipped), p0, n0, m0), At(nat_arith.MulSym, n0, m0)), // n₀·m₀ = m₀·n₀
				),
			))
		}),
})}

// ---------------------------------------------------------------------------
// DivMultAdd — the quotient rises by exactly the copies added
// ---------------------------------------------------------------------------

// DivMultAdd — ModMultAdd's counterpart for the quotient, and unlike
// ModMultAdd it cannot be an instance of ModEq: adding a copies of n to
// b does not leave the quotient alone, it raises it by exactly a. So the
// file's `quotient` section argues it once, in the sub-chapter's usual
// way — exhibit a representation and let uniqueness name the answer:
//
//	Division writes b as nat_div(b,n)·n + nat_mod(b,n), so a·n + b is
//	(a + nat_div(b,n))·n + nat_mod(b,n) — nat_arith.AddAssoc regroups the a copies against
//	Division's product and nat_arith.RightAddDistrib collects the two products into
//	one — a representation whose remainder Division has already bounded,
//	so DivUniq names its quotient.
//
// The four conjuncts are then that section at one point each, differing
// only by a nat_arith.MulSym in the product or an nat_arith.AddSym in one of the two sums,
// exactly as ModMultAdd's four differ.
//
// Unlike ModMultAdd's, these legs carry n ≠ 0, and they have to: at a
// zero divisor the remainder claim survives (both sides are the whole
// dividend) but the quotient claim does not — a + nat_div(b,0) is a, while
// nat_div(a·0 + b, 0) is 0.
var DivMultAdd = divMultAddThm{family.Add(registry.ProofEntry{
	Name: "DivMultAdd",
	Key:  "prop_756011830896a3fb",
	Build: family.Sections(
		"(∀a b n:num. n ≠ 0 ⇒ div(a * n + b, n) = a + div(b, n)) ∧ "+
			"((∀a b n:num. n ≠ 0 ⇒ div(n * a + b, n) = a + div(b, n)) ∧ "+
			"    ((∀a b n:num. n ≠ 0 ⇒ div(b + a * n, n) = div(b, n) + a) ∧ "+
			"        (∀a b n:num. n ≠ 0 ⇒ div(b + n * a, n) = div(b, n) + a)))",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// quotient — the member's one real argument. The context is `arg`
			// because the statement itself binds `a`.
			quotient := ctx.Lemma(Statement{
				Binders: "∀a b n:num.",
				Hypotheses: []string{
					"n ≠ 0",
				},
				Conclusion: "div(a * n + b, n) = a + div(b, n)",
			},
				func(arg *Argument, a, b, n Term, nonzero Fact) {
					quot := v.Div(b, n)     // the copies of n₀ already inside b₀
					rem := v.Mod(b, n)      // what b₀ leaves over
					block := v.Mul(quot, n) // the part of b₀ those copies fill
					added := v.Mul(a, n)    // the a₀ copies added to b₀

					arg.Show(
						"the a₀ new copies join b₀'s own quotient and leave "+
							"b₀'s remainder, which Division has already bounded",
						By(
							nonzero,
							At(Division, b, n),
							// a₀·n₀ + (nat_div(b₀,n₀)·n₀ + nat_mod(b₀,n₀)) = (a₀·n₀ + nat_div(b₀,n₀)·n₀) + nat_mod(b₀,n₀)
							At(nat_arith.AddAssoc, added, block, rem),
							At(nat_arith.RightAddDistrib, a, quot, n), // (a₀ + nat_div(b₀,n₀))·n₀ = a₀·n₀ + nat_div(b₀,n₀)·n₀
							// DivUniq at (dividend, divisor, quotient, remainder)
							// := (a₀·n₀ + b₀, n₀, a₀ + nat_div(b₀,n₀), nat_mod(b₀,n₀)).
							At(DivUniq, v.Add(added, b), n, v.Add(a, quot), rem),
						))
				})

			// The Skolems each leg of the headline mints from its own binders.
			a0 := Var("a_0", NumType)
			b0 := Var("b_0", NumType)
			n0 := Var("n_0", NumType)

			// The copies of the divisor, either way round, and the addend's own
			// quotient — the second summand each of the last two legs has to move.
			copies := v.Mul(a0, n0)
			flipped := v.Mul(n0, a0)
			addendQuot := v.Div(b0, n0)

			// `quotient` at the leg's own point, in its own statement's binder
			// order — (multiplier, representative, divisor) — because it is a
			// SIBLING SECTION, not a named dep (README §"Reading the proofs").
			atLeg := At(quotient, a0, b0, n0)

			return ctx.Theorem(headline,
				func(arg *Argument) {
					arg.Do(SplitConjAll(
						Case(
							"copies before the addend, quotient sum as `quotient` states it: this leg IS that section",
							Cite(quotient),
						),
						Case(
							"copies before the addend, divisor as the first factor: the product's factors swap",
							StripQuant(),
							By(atLeg, At(nat_arith.MulSym, n0, a0)), // n₀·a₀ = a₀·n₀
						),
						Case(
							"addend before the copies: both sums turn round — the dividend's and the quotient's",
							StripQuant(),
							By(
								atLeg,
								At(nat_arith.AddSym, b0, copies),      // b₀ + a₀·n₀ = a₀·n₀ + b₀
								At(nat_arith.AddSym, a0, addendQuot)), // a₀ + nat_div(b₀,n₀) = nat_div(b₀,n₀) + a₀
						),
						Case(
							"addend before the copies, divisor as the first factor: both sums turn round and the factors swap",
							StripQuant(),
							By(
								atLeg,
								At(nat_arith.MulSym, n0, a0),          // n₀·a₀ = a₀·n₀
								At(nat_arith.AddSym, b0, flipped),     // b₀ + n₀·a₀ = n₀·a₀ + b₀
								At(nat_arith.AddSym, a0, addendQuot)), // a₀ + nat_div(b₀,n₀) = nat_div(b₀,n₀) + a₀
						),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Dividing and taking remainders twice
// ---------------------------------------------------------------------------
//
// Dividing and taking remainders twice, and the residue algebra
// that grows out of it.
//
// What happens when nat_div or nat_mod is applied to its own output. The first
// members collapse an iterated nat_div or nat_mod to a single application; on
// top of them the tier states the algebra of "reduce after every
// operation" — the mod-n ring's addition and multiplication written
// over raw nat_mod.
//
// 	DivDiv dividing twice is dividing by the product
// 	ModAddMod reducing the summands first changes no remainder
// 	ModMod reducing mod a product, then mod a factor
// 	ModModRefl reducing twice by the same modulus
// 	ModAddAssoc associativity of addition-then-reduction
// 	ModMulMod reducing the factors first changes no remainder
// 	ModAddModLeft reducing just the left summand changes no remainder
// 	ModAddModRight · · · the right summand
// 	ModMulModLeft reducing just the left factor changes no remainder
// 	ModMulModRight · · · the right factor
// 	ModMulAssoc associativity of multiplication-then-reduction
// 	ModSmallCases under twice the divisor, the remainder in two cases
// 	ModAddComplement what tops a number up to the next multiple
// 	ModInjectiveBelow below the divisor, the remainder determines the number
// 	DivOne dividing by one changes nothing
// 	ModOne · · · and leaves nothing over
// 	DivMod the nat_div/nat_mod interchange over a compound divisor
// 	ModDoubleSplit a residue at a doubled modulus, digit by digit
//
// DivDiv is where the reach adjunction earns its keep — its entry doc
// below says how. Two members here guard on a compound divisor and
// reach OPPOSITE conclusions about whether one guard suffices; each
// says why at its own entry, and the criterion that separates them is
// whether the outer operation's degenerate value depends on the
// factorization.
//
// DAG (within this file):
//
// 	DivDiv : [LessEqRightDivEq, nat_arith.MulAssoc, nat_arith.MulEqZero, DivZero, ZeroDiv,
// 	 nat_arith.MulLeftZeroClause, nat_arith.MulZero]
// 	 + nat_order.{LessEqAntisym, LessEqRefl}
// 	ModAddMod : [Division, ModEq, ModZero, nat_arith.RightAddDistrib, nat_arith.AddAssoc,
// 	 nat_arith.AddSym]
// 	ModMod : [Division, ModEq, ModZero, nat_arith.MulZero, nat_arith.AddZero, nat_arith.AddSym,
// 	 nat_arith.MulAssoc, nat_arith.MulSym]
// 	ModModRefl: [ModMod, nat_arith.MulOne]
// 	ModAddAssoc : [ModAddMod, ModModRefl, nat_arith.AddAssoc]
// 	ModMulMod : [Division, ModEq, ModZero, nat_arith.RightAddDistrib,
// 	 nat_arith.LeftAddDistrib, nat_arith.AddSym, nat_arith.MulAssoc, nat_arith.MulSym]
// 	ModAddModLeft : [ModAddMod, ModModRefl]
// 	ModAddModRight : [ModAddMod, ModModRefl]
// 	ModMulModLeft : [ModMulMod, ModModRefl]
// 	ModMulModRight : [ModMulMod, ModModRefl]
// 	ModMulAssoc : [ModMulModLeft, ModMulModRight, nat_arith.MulAssoc]
// 	ModSmallCases : [ModLessThan, ModEq, nat_arith.OneMul, nat_monus.SubAddCancel]
// 	 + nat_order.{NotLessThan, NotLessEq, LessEqAddRightCancel}
// 	ModAddComplement : [Division, ModEq, ZeroMod, nat_arith.RightAddDistrib, nat_arith.OneMul,
// 	 nat_arith.AddLeftZeroClause, nat_arith.AddAssoc, nat_arith.AddSym,
// 	 nat_monus.SubAddCancel, nat_order.LessEqOfLessThan]
// 	ModInjectiveBelow: [ModLessThan]
// 	DivOne : [DivMult, nat_arith.OneMul, nat_arith.OneNotZero]
// 	ModOne : [ModUniq, nat_arith.MulOne, nat_arith.AddZero, nat_arith.OneIsSucZero]
// 	 + nat_order.ZeroLessThanSuc
// 	DivMod : [Division, DivUniq, ModEq, ModLessThan, LessEqRightDivEq, ModZero,
// 	 DivZero, ZeroMod, nat_arith.MulEqZero, nat_arith.MulZero,
// 	 nat_arith.RightAddDistrib, nat_arith.AddAssoc, nat_arith.AddSym,
// 	 nat_arith.MulAssoc, nat_arith.MulSym] + nat_order.NotLessEq
// 	ModDoubleSplit : [Division, ModMod, DivMod]

// ---------------------------------------------------------------------------
// DivDiv — dividing twice is dividing by the product
// ---------------------------------------------------------------------------

// DivDiv — the member where the reach adjunction earns its keep. LessEqRightDivEq
// characterizes a quotient by the bounds it admits, and each side of this
// equation is characterized by the SAME bounds: for any k,
//
//	k ≤ nat_div(nat_div(m,n), p) ⇔ p·k ≤ nat_div(m,n) ⇔ n·(p·k) ≤ m
//	 ⇔ (n·p)·k ≤ m ⇔ k ≤ nat_div(m, n·p)
//
// — three adjunction instances joined by one reassociation. Reading that
// chain at k := either quotient makes each bound the other, and
// nat_order.LessEqAntisym identifies them. So the proof never unfolds a
// division: it only trades bounds on quotients for bounds on products.
//
// The adjunction needs nonzero divisors and there are two of them, so
// two zero cases stand outside the chain, each settled where it arises
// rather than nested around it: the definitional DivZero at a zero inner
// divisor, ZeroDiv plus ·'s zero clause at a zero outer one.
//
// Guarding on the product n·p instead would NOT merge them, and the
// reason is specific to this member: the left side is
// nat_div(nat_div(m,n), p), which cannot collapse until it is known WHICH
// factor vanished — so nat_arith.MulEqZero hands back exactly the two cases the
// single guard was meant to avoid. (ModMod, below, guards once on the
// product and merges, because nat_mod(m, n·p) collapses by the
// divisor-zero convention whatever the factorization. The difference
// is whether the outer operation's degenerate value depends on the
// factors.) nat_arith.MulEqZero is therefore cited here only for the converse —
// that a product of nonzero factors is nonzero, which is what admits
// the third adjunction instance.
var DivDiv = divDivThm{family.Add(registry.ProofEntry{
	Name: "DivDiv",
	Key:  "prop_e15e2dcb3fc0cc0",
	Build: family.Theorem("∀m n p:num. div(div(m, n), p) = div(m, n * p)",
		func(a *Argument, m Term, n, p *TermWrapper) {
			v := ops(a.Ctx())
			twice := v.Div(v.Div(m, n), p) // the iterated quotient
			once := v.Div(m, v.Mul(n, p))  // the quotient by the product

			// Settled where either divisor is zero — the chain below has no
			// adjunction to run there.
			nonzeroN := a.Unless(
				n.Eq(v.Zero),
				"n₀ = 0: div(m₀, 0) is 0, so the left side divides "+
					"0 by p₀; and 0·p₀ = 0 divides m₀ by 0 on the right",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"both sides are 0",
						By(
							isZero,
							At(DivZero, m),                      // 0 = nat_div(m₀, 0), collapsing the inner division
							At(ZeroDiv, p),                      // 0 = nat_div(0, p₀), collapsing the outer one
							At(nat_arith.MulLeftZeroClause, p))) // 0 = 0·p₀
				}))
			nonzeroP := a.Unless(
				p.Eq(v.Zero),
				"p₀ = 0: the outer division is by 0, and n₀·0 = 0 makes the right-hand division by 0 as well",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"both sides are 0",
						By(
							isZero,
							At(DivZero, v.Div(m, n)), // 0 = nat_div(nat_div(m₀, n₀), 0)
							At(nat_arith.MulZero, n), // 0 = n₀·0 — the right zero clause of ·
							At(DivZero, m)))          // 0 = nat_div(m₀, 0)
				}))

			// agreeAt(k) grounds the chain above at a single k: three
			// adjunction instances whose biconditionals carry a bound on a
			// quotient down to a bound on a product, the reassociation that
			// joins the two middle ones, and reflexivity to enter the chain
			// at k itself. Every divisor it grounds at has to be nonzero,
			// the product n₀·p₀ included.
			agreeAt := func(k Term) []any {
				return []any{
					nonzeroN, nonzeroP,
					At(nat_arith.MulEqZero, n, p), // 0 = n₀·p₀ ⇔ n₀ = 0 ∨ p₀ = 0, so n₀·p₀ ≠ 0
					At(nat_order.LessEqRefl, k),   // k ≤ k
					// k ≤ nat_div(nat_div(m₀,n₀), p₀) ⇔ p₀·k ≤ nat_div(m₀,n₀)
					At(LessEqRightDivEq, p, v.Div(m, n), k),
					// p₀·k ≤ nat_div(m₀,n₀) ⇔ n₀·(p₀·k) ≤ m₀
					At(LessEqRightDivEq, n, m, v.Mul(p, k)),
					At(nat_arith.MulAssoc, n, p, k), // n₀·(p₀·k) = (n₀·p₀)·k
					// k ≤ nat_div(m₀, n₀·p₀) ⇔ (n₀·p₀)·k ≤ m₀
					At(LessEqRightDivEq, v.Mul(n, p), m, k),
				}
			}

			up := a.Have(
				"the iterated quotient bounds itself, so it bounds the other one too",
				MakeProp(v.LessEq(twice, once)),
				By(agreeAt(twice)...))
			down := a.Have(
				"and the same chain read at the other quotient sends it back the other way",
				MakeProp(v.LessEq(once, twice)),
				By(agreeAt(once)...))

			a.Show(
				"two numbers each below the other are the same number",
				By(up, down, At(nat_order.LessEqAntisym, twice, once)))
		}),
})}

// ---------------------------------------------------------------------------
// ModAddMod — reducing the summands first changes nothing
// ---------------------------------------------------------------------------

// ModAddMod — taking each summand's remainder before adding only throws
// away whole copies of the modulus, and throwing those away is invisible
// to the remainder. ModEq is the sentence that says so; the work is
// putting the sum into the shape ModEq asks for.
//
// Division hands out one representation of each summand — so many copies
// of n, plus what is left over. nat_arith.Add the two representations and gather
// like terms: the leftovers to one side, the copies of n to the other,
// where nat_arith.RightAddDistrib pools two multiples of n into one. What is
// exhibited is a + b as the reduced sum plus a multiple of n, which is
// ModEq's hypothesis on the nose.
//
// Modulus zero has no division equation to appeal to and needs none:
// ModZero makes nat_mod(·, 0) the identity, so the reduced sum on the left
// collapses back into a + b and the two sides coincide. That branch is
// one cite each way, hence discharged inline rather than as a Case.
var ModAddMod = modAddModThm{family.Add(registry.ProofEntry{
	Name: "ModAddMod",
	Key:  "prop_e9c030325a6db577",
	// The context is `arg` because the statement itself binds a and b.
	Build: family.Theorem(
		"∀a b n:num. rem(rem(a, n) + rem(b, n), n) = rem(a + b, n)",
		func(arg *Argument, a, b Term, n *TermWrapper) {
			ctx := arg.Ctx()
			v := ops(ctx)

			qa, qb := v.Div(a, n), v.Div(b, n) // copies of n₀ coming out of a₀ / b₀
			ra, rb := v.Mod(a, n), v.Mod(b, n) // what is left over from each
			reduced := v.Add(ra, rb)           // the reduced-then-added side
			pooled := v.Add(qa, qb)            // both quotients as one multiplier

			nonzero := arg.Unless(
				n.Eq(v.Zero),
				"n₀ = 0: nothing is ever taken out, so reducing first is the identity",
				Given(func(c *Argument, isZero Fact) {
					c.Show(
						"with rem(a₀, 0) = a₀ and rem(b₀, 0) = b₀ the left side is the right side already",
						By(isZero, At(ModZero, a), At(ModZero, b)))
				}))

			split := arg.Have(
				"gather the two division equations: leftovers on one side, the copies of n₀ pooled on the other",
				MakeProp(v.Add(a, b).Eq(v.Add(reduced, v.Mul(pooled, n)))),
				By(
					nonzero,
					At(Division, a, n),                       // a₀'s division equation
					At(Division, b, n),                       // b₀'s
					At(nat_arith.RightAddDistrib, qa, qb, n), // pools the two multiples of n₀ into one
					// The gathering itself: the same four summands,
					// reassociated so the leftovers meet.
					nat_arith.AddAC(ctx).Eq(
						v.Add(v.Add(v.Mul(qa, n), ra), v.Add(v.Mul(qb, n), rb)),
						v.Add(reduced, v.Add(v.Mul(qa, n), v.Mul(qb, n))))))

			arg.Show(
				"the two sums differ by a multiple of n₀, and a difference like that leaves the remainder alone",
				// ModEq at (dividend, representative, modulus, multiplier)
				// := (a₀+b₀, nat_mod(a₀,n₀)+nat_mod(b₀,n₀), n₀, nat_div(a₀,n₀)+nat_div(b₀,n₀)).
				By(split, At(ModEq, v.Add(a, b), reduced, n, pooled)))
		}),
})}

// ---------------------------------------------------------------------------
// ModMod — a second reduction by a factor of the first divisor
// ---------------------------------------------------------------------------

// ModMod — ModEq is the whole engine: two numbers differing by a
// multiple of n share a remainder mod n. Everything reduces to
// exhibiting m and its remainder mod n·p as such a pair, and the
// divisor splits that claim, since a vanishing divisor has no division
// equation to appeal to:
//
//	n·p ≠ 0 Division supplies the equation at the compound divisor;
//	 nat_arith.AddSym puts the remainder first and the regroup below
//	 turns that multiple of n·p into a multiple of n;
//	n·p = 0 nat_mod at divisor 0 returns m and the same regroup sends the
//	 multiple to a product with 0, so the claim reads m = m + 0.
//
// The regroup — the two ways of bracketing the three factors quotient,
// p and n — is what both branches turn on, and it is the whole reason p
// may be discarded: p sits inside the compound divisor on one side and
// outside the multiplier on the other.
var ModMod = modModThm{family.Add(registry.ProofEntry{
	Name: "ModMod",
	Key:  "prop_2dfeafceb97a6c9d",
	Build: family.Theorem(
		"∀m n p:num. rem(rem(m, n * p), n) = rem(m, n)",
		func(a *Argument, m *TermWrapper, n, p Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			np := v.Mul(n, p)         // the compound divisor
			quot := v.Div(m, np)      // copies of n·p taken out of m
			rem := v.Mod(m, np)       // what is left of m
			nCopies := v.Mul(quot, p) // the same copies, counted in n's

			// The regroup, as a premise both branches consume: the multiple
			// of n·p that Division sheds IS a multiple of n.
			regroup := nat_arith.MulAC(ctx).
				Eq(v.Mul(nCopies, n), v.Mul(quot, np))

			rep := a.Have(
				"m₀ and its remainder mod n₀·p₀ differ by div(m₀, n₀·p₀)·p₀ copies of n₀",
				MakeProp(m.Eq(v.Add(rem, v.Mul(nCopies, n)))),
				ByCaseStep(np.Eq(v.Zero),
					Case(
						"n₀·p₀ = 0: nat_mod at divisor 0 returns m₀ and the "+
							"regrouped multiple vanishes, so the claim reads m₀ = m₀ + 0",
						Given(func(b *Argument, isZero Fact) {
							b.Show(
								"the convention supplies both halves",
								By(
									isZero,
									regroup,
									At(ModZero, m),              // m₀ = nat_mod(m₀, 0)
									At(nat_arith.MulZero, quot), // 0 = nat_div(m₀, n₀·p₀)·0
									nat_arith.AddZero))
						})),
					Case(
						"n₀·p₀ ≠ 0: this is Division's own equation, its summands swapped and its multiple regrouped",
						Given(func(b *Argument, nonzero Fact) {
							b.Show(
								"the division equation at the compound divisor, read the other way round",
								By(
									nonzero,
									regroup,
									// m₀ = nat_div(m₀, n₀·p₀)·(n₀·p₀) + nat_mod(m₀, n₀·p₀)
									At(Division, m, np),
									// nat_div(m₀, n₀·p₀)·(n₀·p₀) + nat_mod(m₀, n₀·p₀) = nat_mod(m₀, n₀·p₀) + nat_div(m₀, n₀·p₀)·(n₀·p₀)
									At(nat_arith.AddSym, v.Mul(quot, np), rem)))
						})),
				))

			a.Show(
				"differing by a multiple of n₀ is what leaves the remainder mod n₀ alone",
				// ModEq at (dividend, representative, modulus, multiplier)
				// := (m₀, nat_mod(m₀, n₀·p₀), n₀, nat_div(m₀, n₀·p₀)·p₀).
				By(rep, At(ModEq, m, rem, n, nCopies)))
		}),
})}

// ---------------------------------------------------------------------------
// ModModRefl — reducing twice by the same divisor
// ---------------------------------------------------------------------------

// ModModRefl — the same statement at p = 1, where the compound divisor
// n·1 is n itself. nat_arith.MulOne is where n = n·1 lives.
var ModModRefl = modModReflThm{family.Add(registry.ProofEntry{
	Name: "ModModRefl",
	Key:  "prop_a00b3c664f36be66",
	Build: family.Theorem("∀m n:num. rem(rem(m, n), n) = rem(m, n)",
		func(a *Argument, m, n Term) {
			one := a.Ctx().Numeral(1) // the chapter vocabulary carries 0, not 1

			a.Show(
				"n₀·1 is n₀, so ModMod at the multiplier 1 already is the statement",
				By(
					At(ModMod, m, n, one), // nat_mod(m₀, n₀) = nat_mod(nat_mod(m₀, n₀·1), n₀)
					nat_arith.MulOne))
		}),
})}

// ---------------------------------------------------------------------------
// ModAddAssoc — associativity of addition-then-reduction
// ---------------------------------------------------------------------------

// ModAddAssoc — reducing after each addition associates: adding z to an
// already-reduced x + y and reducing again is adding a reduced y + z to
// x and reducing again. This is the associativity of the mod-n ring's
// addition stated over raw nat_mod — hypothesis-free (at n = 0 the
// reduction is the identity and the statement is nat_arith.AddAssoc itself),
// and the ∀n form the words chapter's width-instantiated twins cite
// (mint-once: every fixed-width associativity is one instance of this).
//
// Each side absorbs its inner reduction by ModAddMod read at two
// depths — the bare summand enters as its own double reduction
// (ModModRefl) — and the raw sums meet in the middle by nat_arith.AddAssoc.
var ModAddAssoc = modAddAssocThm{family.Add(registry.ProofEntry{
	Name: "ModAddAssoc",
	Key:  "prop_f9e3fee42eddc0bd",
	Build: family.Theorem(
		"∀x y z n:num. rem(rem(x + y, n) + z, n) = rem(x + rem(y + z, n), n)",
		func(a *Argument, x, y, z, n Term) {
			v := ops(a.Ctx())
			sumXY, sumYZ := v.Add(x, y), v.Add(y, z)

			leftAbsorbs := a.Have(
				"the left side is one reduction of the raw sum",
				MakeProp(v.Mod(v.Add(v.Mod(sumXY, n), z), n).Eq(v.Mod(v.Add(sumXY, z), n))),
				By(
					// nat_mod(nat_mod(nat_mod(x+y,n),n) + nat_mod(z,n), n) = nat_mod(nat_mod(x+y,n) + z, n)
					At(ModAddMod, v.Mod(sumXY, n), z, n),
					// the double reduction collapses
					At(ModModRefl, sumXY, n),
					// nat_mod(nat_mod(x+y,n) + nat_mod(z,n), n) = nat_mod((x+y)+z, n)
					At(ModAddMod, sumXY, z, n)))
			rightAbsorbs := a.Have(
				"and so is the right side",
				MakeProp(v.Mod(v.Add(x, v.Mod(sumYZ, n)), n).Eq(v.Mod(v.Add(x, sumYZ), n))),
				By(At(ModAddMod, x, v.Mod(sumYZ, n), n), At(ModModRefl, sumYZ, n), At(ModAddMod, x, sumYZ, n)))
			a.Show(
				"the raw sums meet by associativity",
				By(leftAbsorbs, rightAbsorbs, nat_arith.AddAssoc))
		}),
})}

// ---------------------------------------------------------------------------
// ModMulMod — reducing the factors first changes nothing
// ---------------------------------------------------------------------------

// ModMulMod — ModAddMod's multiplicative twin: taking each factor's
// remainder before multiplying only throws away whole copies of the
// modulus, and throwing those away is invisible to the remainder. ModEq
// is again the closing sentence, but where a sum of two division
// equations gathers in one move, a product of them expands into four
// terms — so here the copies leave one factor at a time, and ModEq
// speaks twice.
//
// Division writes m as its copies of n plus nat_mod(m, n); distributing p
// over that representation splits m·p into nat_mod(m, n)·p plus a multiple
// of n, which is ModEq's hypothesis on the nose. The same move on p
// inside the surviving product nat_mod(m, n)·p sheds the second factor's
// copies, and the two ModEq conclusions meet by transitivity. Each
// multiple needs one regroup — its n pulled out of the middle of three
// factors to stand last, the position ModEq's q·p reads.
//
// Modulus zero: ModZero makes nat_mod(·, 0) the identity, so reducing the
// factors first is no move at all and the two sides are one term. One
// cite per factor, discharged inline as in ModAddMod.
var ModMulMod = modMulModThm{family.Add(registry.ProofEntry{
	Name: "ModMulMod",
	Key:  "prop_70bddd59b5ee86f2",
	Build: family.Theorem(
		"∀m p n:num. rem(m * p, n) = rem(rem(m, n) * rem(p, n), n)",
		func(a *Argument, m, p Term, n *TermWrapper) {
			ctx := a.Ctx()
			v := ops(ctx)

			qm, rm := v.Div(m, n), v.Mod(m, n) // m₀'s copies of n₀, and what is left
			qp, rp := v.Div(p, n), v.Mod(p, n) // p₀'s

			nonzero := a.Unless(
				n.Eq(v.Zero),
				"n₀ = 0: nothing is ever taken out, so reducing first is the identity",
				Given(func(c *Argument, isZero Fact) {
					c.Show(
						"with rem(m₀, 0) = m₀ and rem(p₀, 0) = p₀ the two sides are one term",
						By(isZero, At(ModZero, m), At(ModZero, p)))
				}))

			mSheds := a.Have(
				"distributing p₀ over m₀'s division equation sends m₀'s copies of n₀ out of the product",
				MakeProp(v.Mul(m, p).Eq(v.Add(v.Mul(rm, p), v.Mul(v.Mul(qm, p), n)))),
				By(
					nonzero,
					At(Division, m, n), // m₀ = nat_div(m₀,n₀)·n₀ + nat_mod(m₀,n₀)
					// (nat_div(m₀,n₀)·n₀ + nat_mod(m₀,n₀))·p₀ = (nat_div(m₀,n₀)·n₀)·p₀ + nat_mod(m₀,n₀)·p₀
					At(nat_arith.RightAddDistrib, v.Mul(qm, n), rm, p),
					// the multiple's n₀, pulled out to stand last
					nat_arith.MulAC(ctx).Eq(v.Mul(v.Mul(qm, n), p), v.Mul(v.Mul(qm, p), n)),
					At(nat_arith.AddSym, v.Mul(v.Mul(qm, p), n), v.Mul(rm, p))))
			pSheds := a.Have(
				"and distributing rem(m₀, n₀) over p₀'s sends out p₀'s",
				MakeProp(v.Mul(rm, p).Eq(v.Add(v.Mul(rm, rp), v.Mul(v.Mul(rm, qp), n)))),
				By(
					nonzero,
					At(Division, p, n), // p₀ = nat_div(p₀,n₀)·n₀ + nat_mod(p₀,n₀)
					// nat_mod(m₀,n₀)·(nat_div(p₀,n₀)·n₀ + nat_mod(p₀,n₀)) = nat_mod(m₀,n₀)·(nat_div(p₀,n₀)·n₀) + nat_mod(m₀,n₀)·nat_mod(p₀,n₀)
					At(nat_arith.LeftAddDistrib, rm, v.Mul(qp, n), rp),
					nat_arith.MulAC(ctx).Eq(v.Mul(rm, v.Mul(qp, n)), v.Mul(v.Mul(rm, qp), n)),
					At(nat_arith.AddSym, v.Mul(v.Mul(rm, qp), n), v.Mul(rm, rp))))

			a.Show(
				"each shedding is a difference by a multiple of n₀, and such differences leave the remainder alone",
				// ModEq at (dividend, representative, modulus, multiplier),
				// once per factor.
				By(
					mSheds,
					pSheds,
					At(ModEq, v.Mul(m, p), v.Mul(rm, p), n, v.Mul(qm, p)),
					At(ModEq, v.Mul(rm, p), v.Mul(rm, rp), n, v.Mul(rm, qp))))
		}),
})}

// ---------------------------------------------------------------------------
// ModAddModLeft · ModAddModRight — reducing one summand at a time
// ---------------------------------------------------------------------------

// ModAddModLeft — reducing just the left summand changes no remainder.
// ModAddMod reduces both summands at once; to reduce only one, read it
// at two depths: the left side re-enters as a double reduction of a
// (which ModModRefl collapses) beside a single reduction of b, and
// ModAddMod equates both depths to the raw sum's remainder.
var ModAddModLeft = modAddModLeftThm{family.Add(registry.ProofEntry{
	Name: "ModAddModLeft",
	Key:  "prop_b7f2a91f8eb1e25b",
	Build: family.Theorem(
		"∀a b n:num. rem(rem(a, n) + b, n) = rem(a + b, n)",
		func(arg *Argument, a, b, n Term) {
			v := ops(arg.Ctx())
			arg.Show(
				"both depths of reduction are the raw sum's remainder",
				By(
					Normalized,
					// nat_mod(nat_mod(nat_mod(a₀,n₀),n₀) + nat_mod(b₀,n₀), n₀) = nat_mod(nat_mod(a₀,n₀) + b₀, n₀)
					At(ModAddMod, v.Mod(a, n), b, n),
					// the double reduction collapses
					At(ModModRefl, a, n),
					// nat_mod(nat_mod(a₀,n₀) + nat_mod(b₀,n₀), n₀) = nat_mod(a₀ + b₀, n₀)
					At(ModAddMod, a, b, n)))
		}),
})}

// ModAddModRight — the same absorption on the right summand.
var ModAddModRight = modAddModRightThm{family.Add(registry.ProofEntry{
	Name: "ModAddModRight",
	Key:  "prop_14de177ca577e41d",
	Build: family.Theorem(
		"∀a b n:num. rem(a + rem(b, n), n) = rem(a + b, n)",
		func(arg *Argument, a, b, n Term) {
			v := ops(arg.Ctx())
			arg.Show(
				"both depths of reduction are the raw sum's remainder",
				By(Normalized, At(ModAddMod, a, v.Mod(b, n), n), At(ModModRefl, b, n), At(ModAddMod, a, b, n)))
		}),
})}

// ---------------------------------------------------------------------------
// ModMulModLeft · ModMulModRight — reducing one factor at a time
// ---------------------------------------------------------------------------

// ModMulModLeft — reducing just the left factor changes no remainder:
// ModMulMod read at two depths, with ModModRefl collapsing the double
// reduction, exactly as ModAddModLeft reads ModAddMod.
var ModMulModLeft = modMulModLeftThm{family.Add(registry.ProofEntry{
	Name: "ModMulModLeft",
	Key:  "prop_93bc9ef915fda659",
	Build: family.Theorem(
		"∀a b n:num. rem(rem(a, n) * b, n) = rem(a * b, n)",
		func(arg *Argument, a, b, n Term) {
			v := ops(arg.Ctx())
			arg.Show(
				"both depths of reduction are the raw product's remainder",
				By(
					Normalized,
					// nat_mod(nat_mod(nat_mod(a₀,n₀),n₀) · nat_mod(b₀,n₀), n₀) = nat_mod(nat_mod(a₀,n₀) · b₀, n₀)
					At(ModMulMod, v.Mod(a, n), b, n),
					At(ModModRefl, a, n),
					// nat_mod(nat_mod(a₀,n₀) · nat_mod(b₀,n₀), n₀) = nat_mod(a₀ · b₀, n₀)
					At(ModMulMod, a, b, n)))
		}),
})}

// ModMulModRight — the same absorption on the right factor.
var ModMulModRight = modMulModRightThm{family.Add(registry.ProofEntry{
	Name: "ModMulModRight",
	Key:  "prop_df4c91ebd84875e6",
	Build: family.Theorem(
		"∀a b n:num. rem(a * rem(b, n), n) = rem(a * b, n)",
		func(arg *Argument, a, b, n Term) {
			v := ops(arg.Ctx())
			arg.Show(
				"both depths of reduction are the raw product's remainder",
				By(Normalized, At(ModMulMod, a, v.Mod(b, n), n), At(ModModRefl, b, n), At(ModMulMod, a, b, n)))
		}),
})}

// ---------------------------------------------------------------------------
// ModMulAssoc — associativity of multiplication-then-reduction
// ---------------------------------------------------------------------------

// ModMulAssoc — reducing after each multiplication associates: this is
// the associativity of the mod-n ring's multiplication stated over raw
// nat_mod, hypothesis-free, exactly as ModAddAssoc states its addition's.
// Each side absorbs its inner reduction by the one-factor member for
// its side, and the raw products meet by associativity.
var ModMulAssoc = modMulAssocThm{family.Add(registry.ProofEntry{
	Name: "ModMulAssoc",
	Key:  "prop_908be5e11b2abee6",
	Build: family.Theorem(
		"∀x y z n:num. rem(rem(x * y, n) * z, n) = rem(x * rem(y * z, n), n)",
		func(a *Argument, x, y, z, n Term) {
			a.Show(
				"each side is one reduction of the raw triple product, and those agree by associativity",
				// Both absorptions enter bare: each fires on its own side of
				// the goal as the rewrite it is.
				By(ModMulModLeft, ModMulModRight, nat_arith.MulAssoc))
		}),
})}

// ---------------------------------------------------------------------------
// ModSmallCases — under twice the divisor, the remainder in two cases
// ---------------------------------------------------------------------------

// ModSmallCases — a number under 2n is at most one copy of n away from
// its remainder: below n it IS its remainder (ModLessThan), and from n
// up, taking the one copy out leaves a − n, which the same bound names
// as the remainder — a = (a − n) + 1·n is a difference by a multiple of
// n (ModEq), and a − n lands below n. Both monus facts are
// nat_monus.SubAddCancel's compensation (a − n) + n = a read against
// the hypothesis a < n + n: once as the representation itself, once
// with the common n cancelled from under the hypothesis.
var ModSmallCases = modSmallCasesThm{family.Add(registry.ProofEntry{
	Name: "ModSmallCases",
	Key:  "prop_a49ea894b1676713",
	Build: family.Theorem(
		Statement{
			Binders: "∀a n:num.",
			Hypotheses: []string{
				"a < n + n",
			},
			Conclusion: "rem(a, n) = COND(a < n, a, a - n)",
		},
		func(arg *Argument, a *TermWrapper, n Term, small Fact) {
			ctx := arg.Ctx()
			v := ops(ctx)
			one := ctx.Numeral(1) // the chapter vocabulary carries 0, not 1
			diff := v.Sub(a, n)   // what is left once the one copy is out

			arg.Cases(v.LessThan(a, n))
			arg.When(
				"a₀ < n₀: no copy of n₀ comes out, so a₀ is its own remainder",
				func(b *Argument, below Fact) {
					b.Show(
						"the guard resolves to a₀, which is ModLessThan's value",
						By(below, At(ModLessThan, a, n)))
				})
			arg.Otherwise(
				"¬(a₀ < n₀): one copy of n₀ comes out, and what is left is below n₀",
				func(b *Argument, over Fact) {
					bound := b.Have(
						"the copy is there to take: n₀ sits inside a₀",
						MakeProp(v.LessEq(n, a)),
						// Bare: the duality fires on the goal as the
						// rewrite it is.
						By(over, nat_order.NotLessThan))
					rep := b.Have(
						"a₀ is what is left plus that one copy",
						MakeProp(a.Eq(v.Add(diff, v.Mul(one, n)))),
						By(
							bound,
							At(nat_monus.SubAddCancel, a, n), // (a₀ − n₀) + n₀ = a₀
							nat_arith.OneMul))
					fits := b.Have(
						"and under twice the divisor, what is left is below n₀",
						MakeProp(v.LessThan(diff, n)),
						By(
							Normalized,
							small,
							At(nat_monus.SubAddCancel, a, n),
							bound,
							// n₀ + n₀ ≤ (a₀−n₀) + n₀ ⇔ n₀ ≤ a₀−n₀ — were the
							// leftover NOT below n₀, a₀ would reach n₀ + n₀
							At(nat_order.LessEqAddRightCancel, n, diff, n),
							At(nat_order.NotLessEq, n, diff),         // ¬(n₀ ≤ a₀−n₀) ⇔ a₀−n₀ < n₀
							At(nat_order.NotLessEq, v.Add(n, n), a))) // ¬(n₀+n₀ ≤ a₀) ⇔ a₀ < n₀+n₀
					b.Show(
						"so the remainder of a₀ is the remainder of a₀ − n₀, which is a₀ − n₀ itself",
						// ModEq at (dividend, representative, modulus, multiplier)
						// := (a₀, a₀ − n₀, n₀, 1).
						By(Normalized, over, rep, fits, At(ModEq, a, diff, n, one), At(ModLessThan, diff, n)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// ModAddComplement — what tops a number up to the next multiple
// ---------------------------------------------------------------------------

// ModAddComplement — n − nat_mod(a, n) is the complement: adding it to a
// lands on a multiple of n, so the remainder vanishes. Division's
// representation makes the sum nat_div(a, n)·n + nat_mod(a, n) + (n − nat_mod(a, n)),
// where the remainder and its complement assemble one further copy of n
// — nat_monus.SubAddCancel's compensation, admitted by the remainder
// bound nat_mod(a, n) < n weakened to ≤. So the sum is (nat_div(a, n) + 1)·n, a
// difference from 0 by a multiple of n, and ModEq with ZeroMod read the
// remainder off it. n ≠ 0 is what admits the division equation; nothing
// else asks for it.
var ModAddComplement = modAddComplementThm{family.Add(registry.ProofEntry{
	Name: "ModAddComplement",
	Key:  "prop_f33586dcd9a29f7d",
	Build: family.Theorem(
		Statement{
			Binders: "∀a n:num.",
			Hypotheses: []string{
				"n ≠ 0",
			},
			Conclusion: "rem(a + (n - rem(a, n)), n) = 0",
		},
		func(arg *Argument, a, n Term, nonzero Fact) {
			ctx := arg.Ctx()
			v := ops(ctx)
			one := ctx.Numeral(1)

			q, r := v.Div(a, n), v.Mod(a, n)
			topped := v.Add(a, v.Sub(n, r)) // a₀, topped up to the next multiple
			k := v.Add(q, one)              // how many copies of n₀ that is

			rep := arg.Have(
				"topping up assembles the remainder and its complement into one further copy of n₀",
				MakeProp(topped.Eq(v.Add(v.Zero, v.Mul(k, n)))),
				By(
					nonzero,
					// a₀ = nat_div(a₀,n₀)·n₀ + nat_mod(a₀,n₀), nat_mod(a₀,n₀) < n₀
					At(Division, a, n),
					At(nat_order.LessEqOfLessThan, r, n), // the bound, weakened to what the monus asks
					At(nat_monus.SubAddCancel, n, r),     // (n₀ − nat_mod(a₀,n₀)) + nat_mod(a₀,n₀) = n₀
					// the remainder walks over to meet its complement
					nat_arith.AddAC(ctx).Eq(v.Add(v.Add(v.Mul(q, n), r), v.Sub(n, r)),
						v.Add(v.Mul(q, n), v.Add(v.Sub(n, r), r))),
					At(nat_arith.OneMul, n), // 1·n₀ = n₀
					// (nat_div(a₀,n₀) + 1)·n₀ = nat_div(a₀,n₀)·n₀ + 1·n₀
					At(nat_arith.RightAddDistrib, q, one, n),
					// bare: the zero clause fires on the goal directly
					nat_arith.AddLeftZeroClause))

			arg.Show(
				"a multiple of n₀ leaves no remainder",
				// ModEq at (dividend, representative, modulus, multiplier)
				// := (a₀ + (n₀ − nat_mod(a₀,n₀)), 0, n₀, nat_div(a₀,n₀) + 1).
				By(rep, At(ModEq, topped, v.Zero, n, k), ZeroMod))
		}),
})}

// ---------------------------------------------------------------------------
// ModInjectiveBelow — below the divisor, the remainder determines the number
// ---------------------------------------------------------------------------

// ModInjectiveBelow — nat_mod(·, n) is injective below n: a number under
// the divisor is its own remainder (ModLessThan), so two of them with
// equal remainders ARE equal. This is what makes the numbers under n a
// system of representatives for the residues.
var ModInjectiveBelow = modInjectiveBelowThm{family.Add(registry.ProofEntry{
	Name: "ModInjectiveBelow",
	Key:  "prop_5f3d3fff919f3f0d",
	Build: family.Theorem(
		Statement{
			Binders: "∀a b n:num.",
			Hypotheses: []string{
				"a < n",
				"b < n",
				"rem(a, n) = rem(b, n)",
			},
			Conclusion: "a = b",
		},
		func(arg *Argument, a, b, n Term, aBelow, bBelow, sameRem Fact) {
			arg.Show(
				"each side is its own remainder, and the remainders are equal",
				By(Normalized, aBelow, bBelow, sameRem, At(ModLessThan, a, n), At(ModLessThan, b, n)))
		}),
})}

// ---------------------------------------------------------------------------
// DivOne · ModOne — the divisor-one values
// ---------------------------------------------------------------------------

// DivOne — dividing by one changes nothing: n is n whole copies of one,
// and DivMult divides whole copies back out exactly. nat_arith.OneMul spells
// n as 1·n, the shape DivMult reads.
var DivOne = divOneThm{family.Add(registry.ProofEntry{
	Name: "DivOne",
	Key:  "prop_1d6e0d8e761588a5",
	Build: family.Theorem("∀n:num. n = div(n, 1)",
		func(a *Argument, n Term) {
			one := a.Ctx().Numeral(1) // the chapter vocabulary carries 0, not 1

			a.Show(
				"n₀ whole copies of one divide back out exactly",
				By(
					nat_arith.OneNotZero,
					At(DivMult, one, n), // 1 ≠ 0 ⇒ nat_div(1·n₀, 1) = n₀
					nat_arith.OneMul))   // 1·n₀ = n₀
		}),
})}

// ModOne — and leaves nothing over: the same representation, read by
// the remainder's uniqueness. n = n·1 + 0 exhibits a remainder that
// sits below the divisor — 0 < 1 is ZeroLessThanSuc read through
// 1 = suc(0) — so ModUniq names it.
var ModOne = modOneThm{family.Add(registry.ProofEntry{
	Name: "ModOne",
	Key:  "prop_e98d8b16f295f563",
	Build: family.Theorem("∀n:num. 0 = rem(n, 1)",
		func(a *Argument, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			one := ctx.Numeral(1) // the chapter vocabulary carries 0, not 1

			a.Show(
				"n₀ copies of one leave nothing over, and uniqueness names the remainder",
				By(
					At(nat_arith.MulOne, n),               // n₀·1 = n₀
					At(nat_arith.AddZero, v.Mul(n, one)),  // n₀·1 + 0 = n₀·1
					nat_arith.OneIsSucZero,                // 1 = suc(0), what 0 < 1 is spelled through
					At(nat_order.ZeroLessThanSuc, v.Zero), // 0 < suc(0)
					// ModUniq at (dividend, divisor, quotient, remainder)
					// := (n₀, 1, n₀, 0).
					At(ModUniq, n, one, n, v.Zero)))
		}),
})}

// ---------------------------------------------------------------------------
// DivMod — the nat_div/nat_mod interchange over a compound divisor
// ---------------------------------------------------------------------------

// DivMod — dividing a residue is reducing a quotient: what m's residue
// mod n·p leaves when divided by n is what m's quotient by n leaves mod
// p. The two sides count the same thing — the copies of n inside m that
// did NOT assemble into whole copies of n·p — once from below, once
// from above.
//
// The argument is the sub-chapter's usual one, run twice and closed by
// uniqueness on each side. Division at the compound divisor writes m as
// Q·(n·p) + R; Division again inside the residue writes R as q·n + r.
// Regrouping exhibits m as (Q·p + q)·n + r with r still below n, so
// DivUniq counts nat_div(m, n) = Q·p + q — the left side's q plus Q whole
// copies of p. Those copies are invisible mod p (ModEq), and q itself
// survives the reduction because it sits below p: were p ≤ q, the
// adjunction (LessEqRightDivEq) would put n·p ≤ R, against Division's
// own bound.
//
// The degenerate divisors split apart, as in DivDiv, because the left
// side cannot collapse until it is known WHICH factor vanished: at
// n = 0 both sides divide by zero and vanish, while at p = 0 neither
// reduction ever fires and both sides are nat_div(m, n) — opposite values,
// so no single guard on the product could merge them.
var DivMod = divModThm{family.Add(registry.ProofEntry{
	Name: "DivMod",
	Key:  "prop_dd6262bd961f7dfa",
	Build: family.Theorem(
		"∀m n p:num. div(rem(m, n * p), n) = rem(div(m, n), p)",
		func(a *Argument, m, n, p *TermWrapper) {
			ctx := a.Ctx()
			v := ops(ctx)

			np := v.Mul(n, p)            // the compound divisor
			bigQuot := v.Div(m, np)      // Q: the copies of n·p taken out of m
			rem := v.Mod(m, np)          // R: the compound residue
			q := v.Div(rem, n)           // the left side: the residue's quotient
			r := v.Mod(rem, n)           // what the residue leaves mod n
			nCopies := v.Mul(bigQuot, p) // Q's copies of n·p, counted in n's

			nonzeroN := a.Unless(
				n.Eq(v.Zero),
				"n₀ = 0: both sides divide by zero — the left directly, the right inside the reduction",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"both sides are 0",
						By(
							isZero,
							At(DivZero, rem), // nat_div(nat_mod(m₀, n₀·p₀), 0) = 0
							At(DivZero, m),   // nat_div(m₀, 0) = 0
							At(ZeroMod, p)))  // nat_mod(0, p₀) = 0
				}))
			nonzeroP := a.Unless(
				p.Eq(v.Zero),
				"p₀ = 0: n₀·0 = 0 disarms the left side's reduction and the right side's alike",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"both sides are div(m₀, n₀)",
						By(
							isZero,
							At(nat_arith.MulZero, n),  // n₀·0 = 0
							At(ModZero, m),            // nat_mod(m₀, 0) = m₀
							At(ModZero, v.Div(m, n)))) // nat_mod(nat_div(m₀,n₀), 0) = nat_div(m₀,n₀)
				}))

			outer := a.Have(
				"Division at the compound divisor, its multiple regrouped into copies of n₀",
				MakeProp(m.Eq(v.Add(v.Mul(nCopies, n), rem))),
				By(
					nonzeroN,
					nonzeroP,
					At(nat_arith.MulEqZero, n, p), // n₀·p₀ = 0 ⇔ n₀ = 0 ∨ p₀ = 0, so n₀·p₀ ≠ 0
					At(Division, m, np),           // m₀ = Q·(n₀·p₀) + R
					// the regroup: Q's multiple of n₀·p₀ IS Q·p₀ copies of n₀
					nat_arith.MulAC(ctx).Eq(v.Mul(bigQuot, np), v.Mul(nCopies, n))))
			inner := a.Have(
				"and Division again inside the residue",
				MakeProp(rem.Eq(v.Add(v.Mul(q, n), r))),
				By(nonzeroN, At(Division, rem, n)))
			rep := a.Have(
				"together: m₀ as Q·p₀ + q copies of n₀, plus r",
				MakeProp(m.Eq(v.Add(v.Mul(v.Add(nCopies, q), n), r))),
				By(
					outer,
					inner,
					// (Q·p₀)·n₀ + (q·n₀ + r) = ((Q·p₀)·n₀ + q·n₀) + r
					At(nat_arith.AddAssoc, v.Mul(nCopies, n), v.Mul(q, n), r),
					// bare: the distribution fires on the goal as the rewrite it is
					nat_arith.RightAddDistrib))

			quotient := a.Have(
				"a representation whose remainder Division has already bounded, so DivUniq counts the quotient",
				MakeProp(v.Div(m, n).Eq(v.Add(nCopies, q))),
				By(
					nonzeroN,
					rep,
					At(Division, rem, n), // r < n₀ — the bound conjunct
					// DivUniq at (dividend, divisor, quotient, remainder)
					// := (m₀, n₀, Q·p₀ + q, r).
					At(DivUniq, m, n, v.Add(nCopies, q), r)))

			small := a.Have(
				"q sits below p₀: were it not, p₀ whole copies of n₀ would fit inside the compound residue",
				MakeProp(v.LessThan(q, p)),
				By(
					nonzeroN,
					nonzeroP,
					At(nat_arith.MulEqZero, n, p),
					At(Division, m, np),              // R < n₀·p₀
					At(LessEqRightDivEq, n, rem, p),  // p₀ ≤ q ⇔ n₀·p₀ ≤ R
					At(nat_order.NotLessEq, np, rem), // ¬(n₀·p₀ ≤ R) ⇔ R < n₀·p₀
					At(nat_order.NotLessEq, p, q)))   // ¬(p₀ ≤ q) ⇔ q < p₀

			a.Show(
				"the quotient's excess over q is whole copies of p₀ — "+
					"invisible mod p₀ — and below p₀, q is its own remainder",
				By(
					quotient,
					small,
					At(nat_arith.AddSym, nCopies, q), // Q·p₀ + q = q + Q·p₀
					// ModEq at (dividend, representative, modulus, multiplier)
					// := (Q·p₀ + q, q, p₀, Q).
					At(ModEq, v.Add(nCopies, q), q, p, bigQuot),
					At(ModLessThan, q, p))) // q < p₀ ⇒ nat_mod(q, p₀) = q
		}),
})}

// ---------------------------------------------------------------------------
// ModDoubleSplit — a residue at a doubled modulus, taken apart
// ---------------------------------------------------------------------------

// ModDoubleSplit — doubling the modulus buys exactly one digit. The
// residue mod 2m carries everything the residue mod m does, plus the
// parity of the quotient by m weighted by m itself — which is the
// binary place value of a positional expansion, read one place at a
// time.
//
// It is Division read AT the doubled residue, with both halves of the
// resulting representation identified by the interchange laws: what
// nat_mod(x₀, m₀·2) leaves mod m₀ is nat_mod(x₀, m₀) (ModMod), and what it
// leaves when divided by m₀ is nat_mod(nat_div(x₀, m₀), 2) (DivMod). The
// equation is stated in Division's own orientation, multiple first.
var ModDoubleSplit = modDoubleSplitThm{family.Add(registry.ProofEntry{
	Name: "ModDoubleSplit",
	Key:  "prop_a43f3966bdefc671",
	Build: family.Theorem(
		Statement{
			Binders: "∀m x:num.",
			Hypotheses: []string{
				"m ≠ 0",
			},
			Conclusion: "rem(x, m * 2) = rem(div(x, m), 2) * m + rem(x, m)",
		},
		func(a *Argument, m, x Term, nonzero Fact) {
			v := ops(a.Ctx())
			two := a.Ctx().Numeral(2)

			a.Show(
				"Division splits the doubled residue, and the interchange laws "+
					"name both halves: ModMod the residue, DivMod the multiplier",
				By(
					nonzero,
					// nat_mod(x₀, m₀·2) = nat_div(nat_mod(x₀, m₀·2), m₀)·m₀ + nat_mod(nat_mod(x₀, m₀·2), m₀)
					At(Division, v.Mod(x, v.Mul(m, two)), m),
					// nat_mod(nat_mod(x₀, m₀·2), m₀) = nat_mod(x₀, m₀)
					At(ModMod, x, m, two),
					// Bare: with the other two resident the interchange
					// closes the goal at its ∀-form install, so it names
					// no instance.
					DivMod))
		}),
})}
