// nonneg_real_formal_diff.go — the chapter: formal differences, the real tower's third layer.
//
// Six parts, marked by banners:
//
// - Treal addition and negation, which are componentwise on the pair
// - Treal_eq is an equivalence relation on formal differences
// - Treal_inv, the family's hardest movement
// - Treal multiplication, which is bilinear on the pair
// - The numeral embedding ℕ → treal, k ↦ (hreal_of_num k, 0)
// - The treal order

package nonneg_real_formal_diff

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	nn "github.com/euc-ai/xugo/library/proofs/real/tower/internal/nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Treal addition and negation, which are componentwise on the pair
// ---------------------------------------------------------------------------
//
// treal addition and negation, which are componentwise on the pair: the
// group laws up to treal_eq (plus AddSymEq, where the pair identity holds
// on the nose), and the two welldef theorems that are the quotient's
// descent data for + and unary -.
//
// README: "the commutative-ring laws with additive inverse" and the
// welldef tier.

// AddSym — `treal_add` commutes up to `treal_eq`:
//
//	⊢ ∀x y : hreal × hreal. treal_eq((x + y), (y + x))
//
// treal values are formal-difference pairs and `treal_eq` compares
// them by cross-sum, so unfolding the equivalence turns the goal into
// the hreal-side identity
//
//	fst(x + y) + snd(y + x) = fst(y + x) + snd(x + y)
//
// The strict-equality sibling AddSymEq identifies the two sums on the
// nose — treal addition is componentwise, and hreal addition already
// commutes — so paramodulating it over the occurrences of
// `treal_add(y, x)` leaves the same projection sum on both sides.
var AddSym = addSymThm{family.Add(registry.ProofEntry{
	Name: "AddSym",
	Key:  "prop_43125c42ea09b613",
	Build: family.Theorem(
		"∀x y:prod(hreal, hreal). treal_eq(x + y, y + x)",
		func(a *Argument, x, y Term) {
			// cross-sum identity over fst/snd of the two treal_add terms.
			a.Do(Unfold(TrealEqDef))
			a.Show(
				"both sides name the same sum once AddSymEq identifies x₀ + y₀ with y₀ + x₀",
				By(AddSymEq))
		}),
})}

// AddSymEq — strict commutativity of `treal_add`:
//
//	⊢ ∀x y : hreal × hreal. (x + y) = (y + x)
//
// Where the sibling AddSym holds only up to treal_eq, this is a
// literal equality: treal_add is defined component-wise on the pair
// as `(fst x + fst y, snd x + snd y)`, and hreal addition itself
// commutes (nn.AddSym), so unfolding the definition reduces both
// sides to the same pair.
//
// The Go body is one Chain: unfold treal_add, then a single SimpWith
// rewrites both hreal_add sub-terms by nn.AddSym; the residual is a
// reflexive pair identity that normalizes to ⊤.
var AddSymEq = addSymEqThm{family.Add(registry.ProofEntry{
	Name: "AddSymEq",
	Key:  "prop_7d8a1982c2d40c73",
	Build: family.Theorem(
		"∀x y:prod(hreal, hreal). x + y = y + x",
		func(a *Argument, x, y Term) {
			a.Do(
				Unfold(TrealAddDef),
				Expect(Simp(Fwd(nn.AddSym)),
					Case(
						"both components coincide, the pair identity normalizes to ⊤",
						TrivialNormalized()),
				),
			)
		}),
})}

// AddAssoc — treal addition is associative up to treal_eq:
//
//	⊢ ∀x y z : treal. treal_eq((x + (y + z)),
//	 ((x + y) + z))
//
// treal values are formal differences (a, b): treal_add adds
// component-wise and treal_eq is the cross-sum identity, so unfolding
// both constants turns the goal into an hreal equation whose two
// sides are the same six projections fst/snd(x₀,y₀,z₀) summed under
// different bracketings — exactly the shape nn.AddAssoc's rewrite
// orientation `x + (y + z) → (x + y) + z` normalizes: one injection
// re-brackets both sides to the common left-nested form and the
// equation closes by reflexivity (no refute, no symmetry flip).
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name: "AddAssoc",
	Key:  "prop_aec09ade27ec55f3",
	Build: family.Theorem(
		"∀x y z:prod(hreal, hreal). treal_eq(x + (y + z), x + y + z)",
		func(a *Argument, x, y, z Term) {
			ctx := a.Ctx()

			a.Do(
				Unfold(TrealEqDef),  // cross-sum identity over fst/snd of the treal_add terms
				Unfold(TrealAddDef), // component-wise pairs — exposes the projection redexes
				pairs.Collapse(ctx), // project them out: both sides are re-bracketed six-term hreal sums
				// nn.AddAssoc left-nests every hreal_add on both sides;
				// the injection's rewrite pass closes the equation.
				Cite(nn.AddAssoc),
			)
		}),
})}

// AddLeftId — treal_of_num(0) is a left identity for treal addition
// up to treal_eq:
//
//	⊢ ∀x : treal. treal_eq((treal_of_num(0) + x), x)
//
// treal_of_num(0) is the pair (hreal_of_num(0), hreal_of_num(0)), and
// treal_add adds component-wise, so unfolding treal_eq → treal_add →
// treal_of_num leaves an hreal equation whose only mismatch is a
// `hreal_of_num(0) + _` prefix on each side. nn.AddLeftId's flipped
// orientation `x = hreal_add(hreal_of_num(0), x)` strips exactly that
// prefix as a right-to-left rewrite — one injection closes the
// equation (no refute, no symmetry flip).
var AddLeftId = addLeftIdThm{family.Add(registry.ProofEntry{
	Name: "AddLeftId",
	Key:  "prop_4bf85f6165a53d7a",
	Build: family.Theorem(
		"∀x:prod(hreal, hreal). treal_eq(treal_of_num(0) + x, x)",
		func(a *Argument, x Term) {
			ctx := a.Ctx()

			a.Do(
				Unfold(TrealEqDef),  // cross-sum identity over fst/snd of the treal_add term
				Unfold(TrealAddDef), // component-wise pairs — first redex layer
				// ⊢ (fst(treal_of_num(0)) + fst(x₀)) + snd(x₀) = fst(x₀) + (snd(treal_of_num(0)) + snd(x₀))
				pairs.Collapse(ctx),
				Unfold(TrealOfNumDef), // treal_of_num(0) → (hreal_of_num(0), hreal_of_num(0)) — second redex layer
				// ⊢ (hreal_of_num(0) + fst(x₀)) + snd(x₀) = fst(x₀) + (hreal_of_num(0) + snd(x₀))
				pairs.Collapse(ctx),
				// nn.AddLeftId (`x = hreal_of_num(0) + x`, flipped form)
				// strips both zero prefixes; the injection's rewrite pass
				// closes the equation.
				Cite(nn.AddLeftId),
			)
		}),
})}

// AddLeftInv — treal negation is a left additive inverse up to
// treal_eq:
//
//	⊢ ∀x. treal_eq((treal_neg(x) + x), treal_of_num(0))
//
// Componentwise, treal_neg(x) + x is the pair (snd(x) + fst(x),
// fst(x) + snd(x)) — both components the same sum up to order — and
// treal_of_num(0) is the pair (hreal_of_num(0), hreal_of_num(0)), so
// after unfolding all four treal constants and projecting the pair
// literals the goal is the bare hreal identity
//
//	(snd(x) + fst(x)) + 0 = 0 + (fst(x) + snd(x))
//
// which nn.AddLeftId and nn.AddSym close.
var AddLeftInv = addLeftInvThm{family.Add(registry.ProofEntry{
	Name: "AddLeftInv",
	Key:  "prop_ed3252f83bee5212",
	Build: family.Theorem(
		"∀x:prod(hreal, hreal). treal_eq(treal_neg(x) + x, treal_of_num(0))",
		func(a *Argument, x Term) {
			ctx := a.Ctx()
			a.Do(
				Unfold(TrealNegDef),   // treal_neg(x₀) → (snd(x₀), fst(x₀)); no projections exposed yet
				Unfold(TrealAddDef),   // componentwise sums put fst/snd over the neg literal
				pairs.Collapse(ctx),   // → (snd(x₀)+fst(x₀), fst(x₀)+snd(x₀))
				Unfold(TrealOfNumDef), // treal_of_num(0) → (hreal_of_num(0), hreal_of_num(0))
				Unfold(TrealEqDef),    // cross-sum equality projects both pair literals
				pairs.Collapse(ctx),   // → (snd(x₀)+fst(x₀)) + 0 = 0 + (fst(x₀)+snd(x₀))
				// nn.AddLeftId is used twice on purpose. Its as-written
				// orientation puts the `0 +` sum on the RIGHT of the equation, so
				// here it fires right-to-left: this first cite collapses the
				// goal's RHS `0 + (F+S)` to `F+S` and is consumed doing so,
				// leaving the LHS's `+ 0` — whose 0 sits on the right of its sum,
				// outside the pattern.
				Cite(nn.AddLeftId),
			)
			a.Show(
				"the surviving `(S+F) + 0`: AddSym moves the 0 to the front, where AddLeftId deletes it",
				By(nn.AddSym, nn.AddLeftId))
		}),
})}

// AddWellDef — treal addition respects treal_eq in both arguments:
//
//	⊢ ∀x1 x2 y1 y2 : hreal × hreal.
//	 treal_eq(x1, x2) ∧ treal_eq(y1, y2) ⇒
//	 treal_eq((x1 + y1), (x2 + y2))
//
// treal_eq unfolds to the cross-sum identity `F(x1)+S(x2) = F(x2)+S(x1)`
// and treal_add adds componentwise, so after the unfolds and pair
// projection the goal reads
//
//	(F(x1)+F(y1)) + (S(x2)+S(y2)) = (F(x2)+F(y2)) + (S(x1)+S(y1))
//
// (F = fst, S = snd) — each side is a regrouping of the pointwise SUM
// of the two hypothesis cross-sums. Adding the hypotheses gives
//
//	(F(x1)+S(x2)) + (F(y1)+S(y2)) = (F(x2)+S(x1)) + (F(y2)+S(y1))
//
// and the 4-atom AC permutation `(a+b)+(c+d) = (a+c)+(b+d)` (perm4),
// grounded once per side, re-brackets each half into the goal's
// grouping; the goal then closes through the ground equation chain
// goal-LHS = sum-LHS = sum-RHS = goal-RHS. The additive sibling of
// NegWellDef (whose conclusion is the hypothesis commuted — no
// regrouping needed) and LessEqWellDef (same perm4 helper + bridge,
// plus the ≤ transport this pure-equation case doesn't need).
var AddWellDef = addWellDefThm{family.Add(registry.ProofEntry{
	Name: "AddWellDef",
	Key:  "prop_e5eb9280d5f045b9",
	// The proof is the algebra kit's perm4 section plus the assembly:
	// `perm4` is a Go local the goal grounds twice by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x₁ x₂ y₁ y₂:prod(hreal, hreal).",
			Hypotheses: []string{
				"treal_eq(x₁, x₂)",
				"treal_eq(y₁, y₂)",
			},
			Conclusion: "treal_eq(x₁ + y₁, x₂ + y₂)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// perm4 — the 4-atom AC permutation on abstract hreal frees,
			// generated by the shared algebra kit from this family's own AddSym /
			// AddAssoc certificates:
			//
			//	⊢ ∀a b c d : hreal. (a + b) + (c + d) = (a + c) + (b + d)
			//
			// It is grounded once per side of the summed-hypotheses equation in
			// the goal's Show.
			ac := hrealAdd(ctx)
			perm4 := ac.RegroupSection(ctx, ac.Perm4Text())

			hreal := MakeType("hreal")
			fst, snd := pairs.ProjectionsAt(ctx, hreal, hreal)

			// add — hreal_add as an infix-reading builder for the sum claim.
			add := func(p, q Term) *TermWrapper { return v.HrealAdd.Apply(p, q) }

			// The main theorem; the entry var's doc carries the argument, the
			// Have/Show labels stage it: sum the two cross-sum hypotheses, then
			// re-bracket each side via a ground perm4 instance.
			return ctx.Theorem(headline,
				func(a *Argument, x1, x2, y1, y2 Term) {
					// The eight projection atoms, named f/s by projection — the
					// perm4 grounding tuples below read directly in this vocabulary.
					fx1, sx1 := fst.Apply(x1), snd.Apply(x1)
					fx2, sx2 := fst.Apply(x2), snd.Apply(x2)
					fy1, sy1 := fst.Apply(y1), snd.Apply(y1)
					fy2, sy2 := fst.Apply(y2), snd.Apply(y2)

					a.Do(
						// the two premises become the cross-sum hyps; goal cross-sums the treal_add terms
						Unfold(TrealEqDef),
						Unfold(TrealAddDef), // treal_add(u, v) → the componentwise pair literal
						pairs.Collapse(ctx),
					)
					eqX := a.Hyp(MakeProp(add(fx1, sx2).Eq(add(fx2, sx1))))
					eqY := a.Hyp(MakeProp(add(fy1, sy2).Eq(add(fy2, sy1))))
					a.Have(
						"sum: adding eq_x and eq_y pointwise",
						MakeProp(add(add(fx1, sx2), add(fy1, sy2)).Eq(add(add(fx2, sx1), add(fy2, sy1)))),
						By(eqX, eqY),
					)
					a.Show(
						"re-bracket each side of sum via perm4: both sides of the goal "+
							"are sum's regrouped, and the equation chain closes on the install",
						Cite(perm4))
				})
		}),
})}

// NegWellDef — treal_eq is a congruence for treal negation:
//
//	⊢ ∀x1 x2. treal_eq(x1, x2) ⇒ treal_eq(treal_neg(x1), treal_neg(x2))
//
// treal_neg swaps the pair components — the formal difference a − b
// negates to b − a. So the hypothesis unfolds to the cross-sum
// fst(x1) + snd(x2) = fst(x2) + snd(x1), and the conclusion (after
// unfolding treal_neg and projecting over its literal (snd(xᵢ),
// fst(xᵢ)) pairs) to snd(x1) + fst(x2) = snd(x2) + fst(x1) — the SAME
// equation with both sides commuted. One nn.AddSym install and the
// refuter closes the gap.
var NegWellDef = negWellDefThm{family.Add(registry.ProofEntry{
	Name: "NegWellDef",
	Key:  "prop_4c3c142a1acecc27",
	Build: family.Theorem(
		Statement{
			Binders: "∀x₁ x₂:prod(hreal, hreal).",
			Hypotheses: []string{
				"treal_eq(x₁, x₂)",
			},
			Conclusion: "treal_eq(treal_neg(x₁), treal_neg(x₂))",
		},
		func(a *Argument, x1, x2 Term, cross Fact) {
			ctx := a.Ctx()
			a.Do(
				Unfold(TrealEqDef),  // hyp: fst(x₁)+snd(x₂) = fst(x₂)+snd(x₁); concl still projects treal_neg terms
				Unfold(TrealNegDef), // treal_neg(xᵢ) → (snd(xᵢ), fst(xᵢ)) literals under the concl's fst/snd
				pairs.Collapse(ctx), // project them out: concl snd(x₁)+fst(x₂) = snd(x₂)+fst(x₁)
			)
			a.Show(
				"the conclusion is that cross-sum with both sides commuted",
				By(cross, nn.AddSym))
		}),
})}

// ---------------------------------------------------------------------------
// Treal_eq is an equivalence relation on formal differences
// ---------------------------------------------------------------------------
//
// Each law is the defining cross-sum equation read as an hreal-level
// identity, and every welldef theorem in this family is stated against
// these three.
//
// README: "the equivalence tier".

// TrealEqRefl — reflexivity of treal equivalence:
//
//	⊢ ∀x : hreal × hreal. treal_eq(x, x)
//
// Unfolding treal_eq to `(fst(x) + snd(x)) = (fst(x) + snd(x))` leaves a trivially reflexive equation which the def-unfold
// normalizes to ⊤ in one step. No named deps.
var TrealEqRefl = trealEqReflThm{family.Add(registry.ProofEntry{
	Name: "TrealEqRefl",
	Key:  "prop_a5de7346649e01d0",
	Build: family.Theorem("∀x:prod(hreal, hreal). treal_eq(x, x)",
		func(a *Argument, x Term) {
			a.Do(Unfold(TrealEqDef))
		}),
})}

// TrealEqSym — symmetry of treal equivalence:
//
//	⊢ ∀x y : hreal × hreal. treal_eq(x, y) ⇔ treal_eq(y, x)
//
// Unfolding treal_eq turns the iff into `hreal_add(fst(x), snd(y)) =
// (fst(y) + snd(x)) ⇔ (fst(y) + snd(x)) =
// hreal_add(fst(x), snd(y))` — the two sides swap the same equation,
// normalized to ⊤ by the def-unfold step. No named deps.
var TrealEqSym = trealEqSymThm{family.Add(registry.ProofEntry{
	Name: "TrealEqSym",
	Key:  "prop_1db54f35e2af25f4",
	Build: family.Theorem("∀x y:prod(hreal, hreal). treal_eq(x, y) ⇔ treal_eq(y, x)",
		func(a *Argument, x, y Term) {
			a.Do(Unfold(TrealEqDef))
		}),
})}

// TrealEqTrans — transitivity of treal equivalence:
//
//	⊢ ∀x y z : hreal × hreal.
//	 treal_eq(x, y) ∧ treal_eq(y, z) ⇒ treal_eq(x, z)
//
// The proof adds the two hypotheses' cross-sum identities, rearranges
// the resulting 4-term equation via the local `swap` lemma to put
// `fst(y)+snd(y)` on both sides as the right addend, then cancels it
// via nn.EqAddRightCancel. The Have/Show labels stage each
// intermediate.
var TrealEqTrans = trealEqTransThm{family.Add(registry.ProofEntry{
	Name: "TrealEqTrans",
	Key:  "prop_e499aa218344b772",
	// The proof is one lemma plus the assembly: `swap` is a Go local the
	// goal cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x y z:prod(hreal, hreal).",
			Hypotheses: []string{
				"treal_eq(x, y)",
				"treal_eq(y, z)",
			},
			Conclusion: "treal_eq(x, z)",
		},
		func(ctx *Script, headline string) *GoalStackNode {

			// swap — the 4-term hreal_add rearrangement
			//
			//	⊢ ∀a b c d. (a+b)+(c+d) = (a+d)+(c+b)
			//
			// swaps the second and fourth addends of any 4-term sum; the goal
			// below cites it twice (once per side of the added-cross-sums
			// equation). The AC kit composes the rearrangement out of this
			// family's own assoc/sym certificates by kernel steps, so the
			// section carries no refutation at all.
			swap := hrealAdd(ctx).RegroupSection(ctx,
				"∀a b c d:hreal. a + b + (c + d) = a + d + (c + b)")

			// goal — see file header; the Have/Show labels carry the argument.
			return ctx.Theorem(headline,
				func(a *Argument, x, y, z Term) {
					a.Do(Unfold(TrealEqDef))
					h0 := a.Hyp("fst(x) + snd(y) = fst(y) + snd(x)")
					h1 := a.Hyp("fst(y) + snd(z) = fst(z) + snd(y)")
					hSum := a.Have(
						"h_sum: adding h0 and h1 pointwise",
						"fst(x) + snd(y) + (fst(y) + snd(z)) = fst(y) + snd(x) + (fst(z) + snd(y))",
						By(h0, h1))
					a.Have(
						"intermediate: rearrange each side of h_sum so fst(y)+snd(y) sits as the right addend",
						"fst(x) + snd(z) + (fst(y) + snd(y)) = fst(z) + snd(x) + (fst(y) + snd(y))",
						By(hSum, h0, h1, swap))
					a.Show(
						"cancel the common fst(y)+snd(y) right addend via nn.EqAddRightCancel",
						Cite(nn.EqAddRightCancel))
				})
		}),
})}

// TrealEqEquivalence — the three laws above, assembled: the classes of
// treal_eq are the real numbers, and the class calculus of
// relations/equivalence now reads at it.
var TrealEqEquivalence = trealEqEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "TrealEqEquivalence",
	Key:  "prop_a28b94c4ff5241b4",
	Build: family.Instance(equivalence.Equivalence, "equivalence(treal_eq)",
		Case(
			"reflexive: every pair is equivalent to itself",
			Unfold(equivalence.ReflexiveDef),
			Cite(TrealEqRefl)),
		Case(
			"symmetric: an equivalent pair is equivalent the other way round",
			Unfold(equivalence.SymmetricDef),
			By(TrealEqSym)),
		Case(
			"transitive: two equivalences through a common middle pair make one",
			Unfold(equivalence.TransitiveDef),
			Cite(TrealEqTrans))),
})}

// ---------------------------------------------------------------------------
// Treal_inv, the family's hardest movement
// ---------------------------------------------------------------------------
//
// Inversion is a three-way case split on how a pair's components compare,
// and each strict branch inverts the Hilbert-chosen GAP between them. The
// two members below that do real work run on the gap's ε-defining
// equation:
//
// MulLeftInverse's gapUnit and InvWellDef's gapTransport.
//
// README: the treal_inv display and the paragraph under it.

// InvZero — the treal inverse of zero is zero (up to treal_eq):
//
//	⊢ treal_eq(treal_inv(treal_of_num(0)), treal_of_num(0))
//
// treal_inv is defined by cases on how the two components of the pair
// compare: equal components (a formal difference representing 0) map
// to the zero pair outright, and only the two strict-sign branches
// mention hreal_inv. treal_of_num(0) is the pair (hreal_of_num(0),
// hreal_of_num(0)) with equal components, so the whole proof is one
// definition evaluation: unfold treal_of_num and treal_inv, project
// the pair literals so the case condition becomes the reflexively-true
// hreal_of_num(0) = hreal_of_num(0) and the conditional collapses to
// the zero pair, then unfold treal_eq into the cross-sum identity
// 0 + 0 = 0 + 0, which holds by reflexivity.
var InvZero = invZeroThm{family.Add(registry.ProofEntry{
	Name: "InvZero",
	Key:  "prop_e3da0e9cef098692",
	Build: family.Theorem(
		"treal_eq(treal_inv(treal_of_num(0)), treal_of_num(0))",
		func(a *Argument) {
			ctx := a.Ctx()
			a.Do(
				Unfold(TrealOfNumDef), // both zeros → literal pairs
				Unfold(TrealInvDef),   // expose the component-comparison COND
				pairs.Collapse(ctx),   // condition reflexively true → zero pair
				Unfold(TrealEqDef),    // cross-sum 0 + 0 = 0 + 0 — closes
			)
		}),
})}

// MulLeftInverse — every treal not equivalent to zero has treal_inv as
// a left multiplicative inverse (up to treal_eq):
//
//	⊢ ∀x : treal. ¬treal_eq(x, treal_of_num(0)) ⇒
//	 treal_eq((treal_inv(x) * x), treal_of_num(1))
//
// Write F = fst(x), S = snd(x), so x is the formal difference F − S
// and x ≈ 0 exactly when F = S. treal_inv is defined by cases on how F
// and S compare: equal components map to the zero pair, and each
// strict-sign branch inverts the GAP between the components — the
// Hilbert-chosen ε with (larger) = (smaller) + ε — placing hreal_inv(ε)
// on the positive or negative side accordingly.
//
// The whole theorem therefore rests on one hreal-level fact, the gap
// identity gapUnit: if x ≤ y strictly then, for the chosen gap ε with
// y = x + ε,
//
//	1 + inv(ε)·x = inv(ε)·y
//
// (derivation in gapUnit's doc). The main section case-splits on
// F = S — the equal case IS x ≈ 0 — and, on the strict side, on S ≤ F
// to resolve treal_inv's inner conditional; each sign branch unfolds
// the treal product componentwise, strips the 0·t products and +0
// paddings, and lands exactly on a gapUnit instance.
var MulLeftInverse = mulLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "MulLeftInverse",
	Key:  "prop_133a7c637f5cc3d5",
	// The gap-identity helper plus the main theorem, written as a linear
	// script: gapUnit is a Go local the sign legs cite by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x:prod(hreal, hreal).",
			Hypotheses: []string{
				"¬treal_eq(x, treal_of_num(0))",
			},
			Conclusion: "treal_eq(treal_inv(x) * x, treal_of_num(1))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			hreal := MakeType("hreal")
			// The projection heads, for term construction: the vocab bundle
			// carries only the treal/hreal operator floor.
			fstC, sndC := pairs.ProjectionsAt(ctx, hreal, hreal)
			d := Var("d", hreal) // ε-binder only — plain Var, never enters the parse scope
			zero := v.HrealOfNum.Apply(ctx.Numeral(0))
			one := v.HrealOfNum.Apply(ctx.Numeral(1))

			// gap builds εd.(y = x + d) — the Hilbert-chosen gap of x ≤ y.
			gap := func(x Term, y *TermWrapper) Term {
				return d.SuchThat(y.Eq(v.HrealAdd.Apply(x, d)))
			}
			// invGapMul builds inv(εd.(y = x + d)) · t — a gap-inverse multiple.
			invGapMul := func(x Term, y *TermWrapper, t Term) Term {
				return v.HrealMul.Apply(v.HrealInv.Apply(gap(x, y)), t)
			}

			// gapUnit — the hreal-level heart:
			//
			//	⊢ ∀x y : hreal. x ≤ y ∧ x ≠ y ⇒
			//	 1 + inv(εd.(y = x + d))·x = inv(εd.(y = x + d))·y
			//
			// Under the strict inequality the chosen gap ε satisfies y = x + ε
			// (nn.LessEqExists supplies the existence the ε-axiom needs), and the
			// identity chains through four ground facts:
			// inv(ε)·y = inv(ε)·x + inv(ε)·ε (LeftDistrib), inv(ε)·ε = 1 unless
			// ε = 0 (nn.MulLeftInverse) — but ε = 0 would force y = x + 0 = x
			// (AddSym + AddLeftId at x) against x ≠ y — and AddSym at
			// (inv(ε)·x, 1) reorients the sum to the goal's 1 + inv(ε)·x.
			//
			// The closure binds nothing: its x/y live at hreal while the main
			// theorem's x₀ lives at the pair type, and a free name carries one
			// parse-scope type — so this section's binders stay unchartered.
			x := Var("x_0", hreal)
			y := Var("y_0", hreal)
			gapUnit := ctx.Lemma(
				Statement{
					Binders: "∀x y:hreal.",
					Hypotheses: []string{
						"x ≤ y",
						"x ≠ y",
					},
					Conclusion: "hreal_of_num(1) + hreal_inv(εd:hreal. y = x + d) * x = " +
						"hreal_inv(εd:hreal. y = x + d) * y",
				},
				func(a *Argument) {
					a.Do(StripQuant())
					// The premise lands as the two hypotheses x ≤ y and x ≠ y, and
					// the goal is the gap identity 1 + inv(ε)·x = inv(ε)·y.
					a.Do(TrivialSimplify())
					le := a.Hyp(MakeProp(v.HrealLe.Apply(x, y)))
					eps, gapEq := a.ObtainChosen(
						"x ≤ y inhabits the gap's choice set — LessEqExists feeds the ε-axiom",
						MakeProp(Exists(d)(y.Eq(v.HrealAdd.Apply(x, d)))),
						le,
						nn.LessEqExists)
					// x ≠ y is what rules out ε = 0, the one escape nn.MulLeftInverse
					// leaves open: with y = x + ε and 0 + x = x, a zero gap would
					// collapse y onto x.
					strict := a.Hyp(MakeProp(x.Neq(y)))
					a.Show(
						"the four ground facts (doc above) chain down to 1 + inv(ε)·x = inv(ε)·y",
						By(
							gapEq,
							strict,
							At(nn.LeftDistrib, v.HrealInv.Apply(eps), x, eps),
							At(nn.MulLeftInverse, eps),
							At(nn.AddLeftId, x),
							At(nn.AddSym, x, zero),
							At(nn.AddSym, v.HrealMul.Apply(v.HrealInv.Apply(eps), x), one),
						))
				})

			// The main theorem, by cases on how the components of the
			// Skolemized pair x₀ compare.
			return ctx.Theorem(headline,
				func(a *Argument, x Term) {
					// F = fst(x₀), S = snd(x₀) — the formal difference's components.
					fstX := fstC.Apply(x)
					sndX := sndC.Apply(x)

					// residualActs closes a sign leg's arithmetic residual. The
					// final AddLeftId install is deliberately citation-as-close:
					// after AddSym rewrites the remaining t + 0 to 0 + t,
					// installing AddLeftId fires as the finishing rewrite and the
					// leaf closes on the gapUnit instance (the double-cite idiom —
					// the flipped simp rule below was consumed rewriting and
					// cannot serve here).
					residualActs := func(lo Term, hi *TermWrapper, needTotal bool) []Action {
						acts := []Action{
							Cite(gapUnit, lo, hi),
						}
						if needTotal {
							// Negative side: after the simp pass one +0 pad survives, on
							// inv(ε)·hi; totality converts the resident ¬(S ≤ F) into the
							// lo ≤ hi that gapUnit's guard needs.
							acts = append(acts,
								Cite(nn.LessEqTotal, sndX, fstX),
								Cite(nn.AddSym, invGapMul(lo, hi, hi), zero))
						} else {
							// Positive side: a double pad on inv(ε)·hi (the left component
							// collected both zeros) and a single pad on inv(ε)·lo.
							acts = append(acts,
								Cite(nn.AddSym, invGapMul(lo, hi, hi), zero),
								Cite(nn.AddLeftId, invGapMul(lo, hi, hi)),
								Cite(nn.AddSym, invGapMul(lo, hi, lo), zero))
						}
						acts = append(acts,
							Cite(nn.AddLeftId),
						)
						return acts
					}

					// signLeg proves one sign branch of the inverse: with lo ≤ hi
					// strictly (hi = F, lo = S on the positive side; hi = S, lo = F
					// after totality on the negative side), the branch goal is
					//
					//	treal_eq((<inv pair> * x₀), treal_of_num(1))
					//
					// where <inv pair> carries inv(ε) for the chosen gap
					// hi = lo + ε on one component and 0 on the other. The program:
					// assert the gap equation (LessEqExists, plus LessEqTotal to
					// flip the resident ¬(S ≤ F) on the negative side — needTotal),
					// unfold the product and the equivalence componentwise,
					// collapse the pair-literal projections, strip 0·t products and
					// 0+t sums by rewriting, and close on gapUnit at (lo, hi): the
					// surviving equation IS 1 + inv(ε)·lo = inv(ε)·hi modulo one +0
					// on the right, which AddSym at (inv(ε)·lo, 0) and a final
					// AddLeftId absorb.
					signLeg := func(lo Term, hi *TermWrapper, needTotal bool) Action {
						// The gap's inhabitation premises: the branch discriminant
						// carries the dominance lo ≤ hi — resident directly on the
						// positive side; on the negative side as ¬(S ≤ F), which
						// the ground totality instance flips.
						gapPremises := func(b *Argument) []any {
							if needTotal {
								return []any{
									b.Hyp(MakeProp(Not(v.HrealLe.Apply(sndX, fstX)))),
									At(nn.LessEqTotal, sndX, fstX),
									At(nn.LessEqExists, lo, hi),
								}
							}
							return []any{
								b.Hyp(MakeProp(v.HrealLe.Apply(sndX, fstX))),
								At(nn.LessEqExists, lo, hi),
							}
						}

						// The 0-stripping rewrite pass: 0·t → 0 (MulLeftZero flipped) and
						// 0 + t → t (AddLeftId flipped). AddSym is deliberately NOT a
						// rule here — as a simp rule it rewrites inside the ε-binder's
						// body and detaches the goal's gap term from gapUnit's. The
						// AddLeftId rule only has a redex on the negative side; the
						// positive side simply never fires it.
						simpStep := Expect(Simp(
							Fwd(nn.MulLeftZero), // 0·t → 0
							Fwd(nn.AddLeftId),   // 0 + t → t
						),
							Case(
								"the goal is gapUnit at (lo, hi) modulo +0 padding — AddSym "+
									"swaps each pad, AddLeftId absorbs it, and the install closes",
								residualActs(lo, hi, needTotal)...,
							),
						)

						return Derive(func(b *Argument) {
							b.ObtainChosen(
								"the chosen gap satisfies hi = lo + ε — LessEqExists at "+
									"(lo, hi), with totality flipping ¬(S ≤ F) when needed",
								MakeProp(Exists(d)(hi.Eq(v.HrealAdd.Apply(lo, d)))),
								gapPremises(b)...)
							b.Show(
								"the product unfolded componentwise, its 0·t products "+
									"and +0 padding stripped, is gapUnit at (lo, hi)",
								Unfold(TrealMulDef), // (a₁,a₂)·(b₁,b₂) componentwise; fst/snd hit the inv-pair literal
								pairs.Collapse(ctx),
								Unfold(TrealEqDef), // cross-sum equivalence over the product pair and the one pair
								pairs.Collapse(ctx),
								Unfold(TrealOfNumDef), // numeral pairs become literals
								pairs.Collapse(ctx),
								simpStep,
							)
						})
					}

					// goalZero — the F = S branch, where the premise ¬(x₀ ≈ 0) is
					// false. Unfolding treal_eq turns that premise into the
					// hypothesis F + 0 ≠ 0 + S, which the branch refutes directly:
					// AddSym at (F, 0) gives F + 0 = 0 + F, and F = S closes the
					// cycle. The product identity is left as the (never-reached)
					// residual goal.
					goalZero := Chain(
						Unfold(TrealEqDef),    // premise and goal become cross-sum equations over fst/snd
						Unfold(TrealOfNumDef), // the zero and one pairs become literals
						pairs.Collapse(ctx),
						Cite(nn.AddSym, fstX, zero),
						CnfRefute(),
					)

					// goalInverse — the F ≠ S branch: prove the product identity
					// treal_eq(treal_inv(x₀)·x₀, 1). Unfolding treal_inv exposes its
					// case tree; the simplification that follows resolves the F = S
					// test against the branch hypothesis, leaving the sign
					// conditional on S ≤ F, which a second case split resolves. Each
					// sign leg then runs the same program with the roles of F and S
					// exchanged: fix the gap equation, unfold the product
					// componentwise, strip the 0·t products and the +0 padding, and
					// close on a gapUnit instance.
					goalInverse := Chain(
						// normalize the branch hyps (¬(x₀ ≈ 0) from the premise, F ≠ S from the split) into the leaf
						TrivialSimplify(),
						Unfold(TrealInvDef), // expose the case tree: the F = S test over the sign conditional
						// the F = S test resolves against the resident F ≠ S; the S ≤ F conditional remains
						TrivialSimplify(),
						ByCaseStep(v.HrealLe.Apply(sndX, fstX),
							Case(
								"S ≤ F — the inverse sits on the positive side, (inv(ε), 0) with F = S + ε",
								CondRewrite(), // eliminate the conditional into its two guarded legs
								SplitConj(
									Case(
										"the S ≤ F leg carries the proof — its guard is the resident hypothesis",
										StripImp(),
										signLeg(sndX, fstX, false),
									),
									Case(
										"the ¬(S ≤ F) leg is vacuous — its guard contradicts the resident S ≤ F",
										TrivialNormalized()),
								),
							),
							Case(
								"¬(S ≤ F) — totality puts F ≤ S; the inverse sits on the negative side, (0, inv(ε)) with S = F + ε",
								TrivialSimplify(), // re-absorb this branch's ¬(S ≤ F) literal into the leaf's hypotheses
								signLeg(fstX, sndX, true),
							),
						),
					)

					a.Do(
						ByCaseStep(fstX.Eq(sndX),
							Case(
								"F = S — x₀ IS a zero difference, contradicting the premise",
								goalZero),
							Case(
								"F ≠ S — treal_inv's sign conditional resolves, and each sign leg lands on gapUnit",
								goalInverse),
						),
					)
				})
		}),
})}

// InvWellDef — treal inversion respects the formal-difference
// equivalence:
//
//	⊢ ∀x y : treal. treal_eq(x, y) ⇒ treal_eq(treal_inv(x), treal_inv(y))
//
// Writing x = (a₁, a₂) and y = (b₁, b₂) (component reads via fst/snd),
// treal_eq(x, y) unfolds to the cross-sum equation a₁+b₂ = b₁+a₂, and
// treal_inv unfolds to a three-way case split:
//
//	inv(x) = (0, 0) if a₁ = a₂
//	 = (hreal_inv(gap a₁ a₂), 0) if a₂ ≤ a₁ (gap u v = εd. u = v+d)
//	 = (0, hreal_inv(gap a₂ a₁)) otherwise
//
// Welldef-ness is three transports across the cross-sum, each a small
// ∀-closed hreal lemma used twice (forward, and mirrored/contraposed
// with the roles of x and y swapped):
//
// - eqTransport: a₁ = a₂ ⇒ b₁ = b₂ (right-cancel the cross-sum)
// - leTransport: a₂ ≤ a₁ ⇒ b₂ ≤ b₁ (via gapTransport + x ≤ x+d)
// - gapTransport: a₂ ≤ a₁ ⇒ b₁ = b₂ + gap a₁ a₂
// — the x-side ε-witness ALSO realizes the y-side gap, which is the
// heart of the theorem: both sides' hreal_inv arguments are then
// identified by left-cancellation, so the selected inv pairs agree
// componentwise and the treal_eq goal is reflexive.
//
// The main section replays treal_inv's case tree: the zero case closes
// by reflexivity after both CONDs fire; each dominance case derives its
// discriminant transport, the shared gap, and the ε-identification, and
// the case-expansion hypothesis refutes.
var InvWellDef = invWellDefThm{family.Add(registry.ProofEntry{
	Name: "InvWellDef",
	Key:  "prop_56b30a1df7eece06",
	// The three transport lemmas and the main section are Go locals; each
	// citation downstream is closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x y:prod(hreal, hreal).",
			Hypotheses: []string{
				"treal_eq(x, y)",
			},
			Conclusion: "treal_eq(treal_inv(x), treal_inv(y))",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			hreal := MakeType("hreal")
			// fst, snd — the component projections at the treal pair type.
			fst, snd := pairs.ProjectionsAt(ctx, hreal, hreal)
			// d — the ε-binder of the gap witnesses (never free).
			d := Var("d", hreal) // ε-binder only — plain Var, never enters the parse scope

			// add — hreal_add as an infix-reading helper for the claim builders.
			add := func(x, y Term) *TermWrapper { return v.HrealAdd.Apply(x, y) }
			// gap — the ε-witness of the dominance gap w ≤ u: εd. u = w + d.
			gap := func(u *TermWrapper, w Term) *TermWrapper { return d.SuchThat(u.Eq(add(w, d))) }

			// eqTransport — component equality transports across the cross-sum:
			//
			//	⊢ ∀a1 a2 b1 b2 : hreal.
			//	 a₁+b₂ = b₁+a₂ ∧ a₁ = a₂ ⇒ b₁ = b₂
			//
			// Right-cancel a₂ from the cross-sum: the ground cancellation iff at
			// (b₁, b₂, a₂) turns the goal into b₁+a₂ = b₂+a₂, one AddSym instance
			// aligns a₂+b₂ with b₂+a₂, and the ground refute chains cross-sum →
			// substitution → cancellation.
			eqTransport := ctx.Lemma(
				Statement{
					Binders: "∀a₁ a₂ b₁ b₂:hreal.",
					Hypotheses: []string{
						"a₁ + b₂ = b₁ + a₂",
						"a₁ = a₂",
					},
					Conclusion: "b₁ = b₂",
				},
				func(a *Argument, a1, a2, b1, b2 Term) {
					a.Do(
						Basic(), // the premise's two conjuncts land as hypotheses
						// (b₁ = b₂) ⇔ (b₁+a₂ = b₂+a₂), grounded at the target components.
						Cite(nn.EqAddRightCancel, b1, b2, a2),
						// a₂+b₂ = b₂+a₂ — aligns the substituted cross-sum with the iff's RHS.
						Cite(nn.AddSym, a2, b2),
						Basic(),
						CnfRefute(),
					)
				})

			// gapTransport — the x-side gap witness also realizes the y-side
			// gap:
			//
			//	⊢ ∀a1 a2 b1 b2 : hreal.
			//	 a₁+b₂ = b₁+a₂ ∧ a₂ ≤ a₁ ⇒ b₁ = b₂ + gap a₁ a₂
			//
			// LessEqExists supplies ∃d. a₁ = a₂+d, so the ε-term gap a₁ a₂
			// genuinely witnesses the x-side gap (Hilbert). Substituting that
			// realization into the cross-sum and cancelling a₂ (after one AC
			// regroup of the three summands) transports the SAME witness to the
			// y-side difference.
			gapTransport := ctx.Lemma(
				Statement{
					Binders: "∀a₁ a₂ b₁ b₂:hreal.",
					Hypotheses: []string{
						"a₁ + b₂ = b₁ + a₂",
						"a₂ ≤ a₁",
					},
					Conclusion: "b₁ = b₂ + εd:hreal. a₁ = a₂ + d",
				},
				func(a *Argument, a1 *TermWrapper, a2, b1, b2 Term) {
					a.Do(Basic()) // the premise's two conjuncts land as hypotheses
					dom := a.Hyp(MakeProp(v.HrealLe.Apply(a2, a1)))
					gapA, _ := a.ObtainChosen(
						"a₂ ≤ a₁ inhabits the x-side gap's choice set (LessEqExists at (a₂, a₁))",
						MakeProp(Exists(d)(a1.Eq(add(a2, d)))),
						dom,
						At(nn.LessEqExists, a2, a1))
					// (b₁ = b₂+gapA) ⇔ (b₁+a₂ = (b₂+gapA)+a₂) — right-cancel a₂,
					// grounded at the target equation.
					a.Do(Cite(nn.EqAddRightCancel, b1, add(b2, gapA), a2))
					a.Have(
						"AC regroup of the three summands: (a₂+gapA)+b₂ = (b₂+gapA)+a₂",
						MakeProp(add(add(a2, gapA), b2).Eq(add(add(b2, gapA), a2))),
						// Kernel-derived from the family's AC spec, endpoints read
						// off the ground claim — the ε-gap is an opaque leaf to
						// the regroup, so no denote vocabulary and no refutation
						// are involved. (Group.Regroup is the ∀-closed form; a
						// ground claim takes the bare ACRegroup.)
						ACRegroup(ctx.DepNormalized(nn.AddAssoc), ctx.DepNormalized(nn.AddSym)),
					)
					// The assoc install triggers the rewrite fixpoint that chains
					// cancellation-iff + realization + regroup + cross-sum down to
					// a reflexive identity — no refute needed.
					a.Show(
						"cancel a₂: b₁+a₂ = a₁+b₂ = (a₂+gapA)+b₂ = (b₂+gapA)+a₂, so the cancellation iff delivers the goal",
						Cite(nn.AddAssoc),
					)
				})

			// leTransport — dominance transports across the cross-sum:
			//
			//	⊢ ∀a1 a2 b1 b2 : hreal.
			//	 a₁+b₂ = b₁+a₂ ∧ a₂ ≤ a₁ ⇒ b₂ ≤ b₁
			//
			// gapTransport rewrites b₁ as b₂ + gapA; LessEqSelfAdd grants
			// b₂ ≤ b₂ + gapA, and the two facts compose.
			leTransport := ctx.Lemma(
				Statement{
					Binders: "∀a₁ a₂ b₁ b₂:hreal.",
					Hypotheses: []string{
						"a₁ + b₂ = b₁ + a₂",
						"a₂ ≤ a₁",
					},
					Conclusion: "b₂ ≤ b₁",
				},
				func(a *Argument, a1 *TermWrapper, a2, b1, b2 Term) {
					a.Do(Basic()) // the premise's two conjuncts land as hypotheses
					cross := a.Hyp(MakeProp(add(a1, b2).Eq(add(b1, a2))))
					dom := a.Hyp(MakeProp(v.HrealLe.Apply(a2, a1)))
					a.Show(
						"gapTransport at (a₁,a₂,b₁,b₂) — consuming both conjuncts "+
							"— rewrites b₁ as b₂ + gapA, and b₂ ≤ b₂ + gapA lands it",
						By(Normalized, cross, dom, At(gapTransport, a1, a2, b1, b2), At(nn.LessEqSelfAdd, b2, gap(a1, a2))))
				})

			// dominantCase — S(x₀) ≤ F(x₀): transport the dominance, transport
			// the gap witness, identify the two ε-terms, and the case-expansion
			// hypothesis refutes on its inv(gapX)+0 ≠ inv(gapY)+0 disjunct.
			dominantCase := func(fx, sx Term, fy *TermWrapper, sy Term, gapX *TermWrapper, gapY Term) Action {
				return Derive(func(b *Argument) {
					b.Have(
						"y inherits dominance: S(y₀) ≤ F(y₀) — leTransport at (F(x₀),S(x₀),F(y₀),S(y₀))",
						MakeProp(v.HrealLe.Apply(sy, fy)),
						Cite(leTransport, fx, sx, fy, sy),
						TrivialNormalized(),
					)
					sharedGap := b.Have(
						"the shared gap: F(y₀) = S(y₀) + gapX — x's ε-witness realizes y's gap (gapTransport)",
						MakeProp(fy.Eq(add(sy, gapX))),
						// Cited in ∀-form: gapTransport's conclusion IS this claim at
						// (F(x₀),S(x₀),F(y₀),S(y₀)) and both its premises are resident,
						// so the install closes before a witness is consumed (which is
						// what the witness form rejects).
						Cite(gapTransport),
					)
					b.Have(
						"ε-identification: gapX = gapY — the shared gap witnesses "+
							"y's ∃ (Hilbert), and left-cancel over S(y₀) equates the two",
						MakeProp(gapX.Eq(gapY)),
						By(sharedGap, At(nn.EqAddLeftCancel, gapX, gapY, sy)))
					b.Show(
						"with gapX = gapY resident, hreal_inv(gapX)+0 = "+
							"hreal_inv(gapY)+0 holds and the case-expansion hypothesis refutes",
						Basic(),
					)
				})
			}

			// negativeCase — ¬(S(x₀) ≤ F(x₀)): the mirror of dominantCase. The
			// y side is not dominant either (leTransport contraposed), totality
			// flips the discriminant into F(x₀) ≤ S(x₀), and the mirrored gap
			// transport + ε-identification close the remaining disjunct.
			negativeCase := func(fx, sx Term, fy, sy, negGapX *TermWrapper, negGapY Term) Action {
				return Derive(func(b *Argument) {
					// The enclosing context's facts, named so the By closes below
					// can list them: the cross-sum equation (from the treal_eq
					// unfold), y's nonzero fact, and the branch discriminant.
					cross := b.Hyp(MakeProp(add(fx, sy).Eq(add(fy, sx))))
					nonzeroY := b.Hyp(MakeProp(fy.Neq(sy)))
					notDomX := b.Hyp(MakeProp(Not(v.HrealLe.Apply(sx, fx))))
					notDom := b.Have(
						"y is not dominant either: ¬(S(y₀) ≤ F(y₀)) — leTransport with x and y swapped, contraposed",
						MakeProp(Not(v.HrealLe.Apply(sy, fy))),
						Cite(leTransport, fy, sy, fx, sx),
						TrivialNormalized(),
					)
					flipped := b.Have(
						"totality flips the discriminant: F(x₀) ≤ S(x₀)",
						MakeProp(v.HrealLe.Apply(fx, sx)),
						Cite(nn.LessEqTotal, sx, fx),
						TrivialNormalized(),
					)
					sharedGap := b.Have(
						"mirrored shared gap: S(y₀) = F(y₀) + negGapX — gapTransport at "+
							"swapped components; two AddSym instances commute the cross-sum",
						MakeProp(sy.Eq(add(fy, negGapX))),
						// The nonzero and discriminant facts kill the spurious
						// branches.
						By(
							cross,
							nonzeroY,
							notDomX,
							flipped,
							notDom,
							At(gapTransport, sx, fx, sy, fy),
							At(nn.AddSym, sx, fy),
							At(nn.AddSym, sy, fx)))
					b.Have(
						"ε-identification: negGapX = negGapY — left-cancel over F(y₀) after "+
							"Hilbert realizes y's own mirrored ε (the shared gap witnesses its ∃)",
						MakeProp(negGapX.Eq(negGapY)),
						// The mirror of the dominant case.
						By(sharedGap, At(nn.EqAddLeftCancel, negGapX, negGapY, fy)))
					b.Show(
						"with negGapX = negGapY resident, 0+hreal_inv(negGapY) = "+
							"0+hreal_inv(negGapX) holds and the case-expansion hypothesis refutes",
						Basic(),
					)
				})
			}

			// The main theorem. Unfolding treal_eq absorbs the cross-sum
			// equation as a hypothesis and turns the goal into the componentwise
			// cross-sum over the two treal_inv values; unfolding treal_inv
			// exposes both three-way CONDs. The chain then follows treal_inv's
			// case tree, spelled linearly: the zero discriminant F(x₀) = S(x₀)
			// is dismissed inline (eqTransport identifies y's components, both
			// CONDs select (0,0), reflexivity), the swapped eqTransport carries
			// the nonzero fact to the y side, the CONDs case-expand, and the one
			// genuine split — the dominance discriminant S(x₀) ≤ F(x₀) — stays
			// explicit: its branches are true mirrors, each deriving its
			// discriminant transport, the shared gap, and the ε-identification
			// that closes the residual.
			return ctx.Theorem(headline,
				func(a *Argument, x, y Term) {
					// Component reads and gap witnesses, named for the claims below.
					fx, sx := fst.Apply(x), snd.Apply(x)
					fy, sy := fst.Apply(y), snd.Apply(y)
					gapX := gap(fx, sx)    // εd. F(x₀) = S(x₀)+d — x's magnitude when S(x₀) ≤ F(x₀)
					gapY := gap(fy, sy)    // εd. F(y₀) = S(y₀)+d
					negGapX := gap(sx, fx) // εd. S(x₀) = F(x₀)+d — the mirrored magnitude
					negGapY := gap(sy, fy) // εd. S(y₀) = F(y₀)+d

					a.Do(Unfold(TrealEqDef))  // hyp: F(x₀)+S(y₀) = F(y₀)+S(x₀); goal: cross-sum over the inv values
					a.Do(Unfold(TrealInvDef)) // both inv values unfold to their three-way COND
					// We may assume x ≉ 0: in the zero case y's components coincide
					// too, and the goal is reflexive.
					a.Unless(
						fx.Eq(sx),
						"x ≈ 0 (F(x₀) = S(x₀)): both CONDs select (0,0) and the goal is reflexive",
						Derive(func(b *Argument) {
							b.Have(
								"y's components coincide too — eqTransport grounded at "+
									"(F(x₀),S(x₀),F(y₀),S(y₀)) resolves against the cross-sum",
								MakeProp(fy.Eq(sy)),
								Cite(eqTransport, fx, sx, fy, sy),
								TrivialNormalized(),
							)
							b.Show(
								"both zero-branches fire; the projections over (0,0) collapse and 0+0 = 0+0 closes reflexively",
								CondRewrite(),
								pairs.Collapse(ctx),
							)
						}),
					)
					// x ≉ 0: y is nonzero too, and the dominance discriminant
					// decides which inv branch both sides select.
					a.Do(TrivialSimplify()) // normalize the fresh F(x₀) ≠ S(x₀) branch hypothesis into the leaf
					a.Have(
						"F(y₀) ≠ S(y₀) — eqTransport with the roles of x and y swapped, contraposed against F(x₀) ≠ S(x₀)",
						MakeProp(fy.Neq(sy)),
						Cite(eqTransport, fy, sy, fx, sx),
						TrivialNormalized(),
					)
					// Both zero-branches are dead; the CONDs case-expand and the
					// dominance discriminant splits the proof.
					a.Do(CondRewrite())
					a.Do(pairs.Collapse(ctx))
					a.Do(ByCaseStep(v.HrealLe.Apply(sx, fx),
						Case(
							"S(x₀) ≤ F(x₀): both sides select (hreal_inv(gap), 0); the two gaps carry the same ε-witness",
							dominantCase(fx, sx, fy, sy, gapX, gapY),
						),
						Case(
							"¬(S(x₀) ≤ F(x₀)): both sides select (0, hreal_inv(gap)) — the mirrored argument via totality",
							TrivialSimplify(), // prune the case-expansion hyp's now-dead dominance disjunct
							negativeCase(fx, sx, fy, sy, negGapX, negGapY),
						),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Treal multiplication, which is bilinear on the pair
// ---------------------------------------------------------------------------
//
// treal multiplication, which is bilinear on the pair: the monoid laws up
// to treal_eq (plus MulSymEq, where the pair identity holds on the nose),
// left distributivity, and the welldef theorem that is the quotient's
// descent datum for · — proved one argument at a time, the left half
// first.
//
// README: "the commutative-ring laws" and the welldef tier.

// MulSym — commutativity of `treal_mul` measured by `treal_eq`
// rather than strict equality:
//
//	⊢ ∀x y : hreal × hreal. treal_eq((x * y), (y * x))
//
// The strict-equality sibling mulSymEq already gives
// `treal_mul(x, y) = treal_mul(y, x)`; unfolding `treal_eq` turns the
// goal into the hreal-side cross-sum identity
//
//	fst(x * y) + snd(y * x) =
//	fst(y * x) + snd(x * y)
//
// and paramodulating the strict equality over both occurrences of
// `treal_mul(y, x)` reduces it to `hreal_add(fst a, snd a) =
// hreal_add(fst a, snd a)`, which the refuter closes on identity.
var MulSym = mulSymThm{family.Add(registry.ProofEntry{
	Name: "MulSym",
	Key:  "prop_fcb04282cd1a518f",
	Build: family.Theorem(
		"∀x y:prod(hreal, hreal). treal_eq(x * y, y * x)",
		func(a *Argument, x, y Term) {
			// cross-sum identity over fst/snd of the two treal_mul terms.
			a.Do(Unfold(TrealEqDef))
			// The strict-equality sibling identifies the two products, and
			// the cross-sum collapses to a reflexive hreal_add equation.
			a.Show(
				"both sides name the same product once mulSymEq identifies x₀ * y₀ with y₀ * x₀",
				By(mulSymEq))
		}),
})}

// mulSymEq — strict commutativity of `treal_mul`:
//
//	⊢ ∀x y : hreal × hreal. (x * y) = (y * x)
//
// treal multiplication is defined bilinearly on the pair — writing
// `x = (a₁, a₂)`, `y = (b₁, b₂)`, `treal_mul(x, y)` is
// `(a₁·b₁ + a₂·b₂, a₁·b₂ + a₂·b₁)`. Swapping the pair arguments
// swaps every hreal_mul factor pair, and in the second component
// also swaps the sum orientation, so nn.MulSym + nn.AddSym together
// reduce both pair components to a shared canonical form.
//
// The Go body is one pass: unfold treal_mul, then a single SimpWith
// with both hreal-side commutativity rules; the residual normalizes
// to ⊤.
var mulSymEq = mulSymEqThm{family.Add(registry.ProofEntry{
	Name: "mulSymEq",
	Key:  "prop_5d3ba988ec963e40",
	Build: family.Theorem(
		"∀x y:prod(hreal, hreal). x * y = y * x",
		func(a *Argument, x, y Term) {
			a.Do(
				Unfold(TrealMulDef),
				Expect(Simp(Fwd(nn.MulSym), Fwd(nn.AddSym)),
					Case(
						"cross-term component's outer sum symmetrizes, both pair components coincide",
						TrivialNormalized()),
				),
			)
		}),
})}

// MulAssoc — treal multiplication is associative up to treal_eq:
//
//	⊢ ∀x y z : treal. treal_eq((x * (y * z)),
//	 ((x * y) * z))
//
// treal values are formal-difference pairs (a, b): componentwise the
// product `treal_mul((a₁,a₂), (b₁,b₂))` is
// `(a₁·b₁ + a₂·b₂, a₁·b₂ + a₂·b₁)`, so associativity unfolds to a pair
// identity whose two components each carry the same 4 monomials in
// different bracketing. Concretely, letting a=fst(x), b=snd(x),
// c=fst(y), d=snd(y), e=fst(z), f=snd(z):
//
//	LHS.1 = a·(c·e + d·f) + b·(c·f + d·e) = ace + adf + bcf + bde
//	RHS.1 = (a·c + b·d)·e + (a·d + b·c)·f = ace + bde + adf + bcf
//
// So the residual after def_expand + congr is a 4-monomial permutation
// on each side. The proof is a 3-tier stack, each tier supplying the
// next one a rewrite rule:
//
// 1. `rDistrib` — right-distributivity `(x+y)·z = x·z + y·z`, derived
// inline from nn.LeftDistrib + nn.MulSym (LDistrib's mirror on the
// other outer factor);
// 2. `perm4` — the 4-term rearrangement lemma
// `add(add(A,B), add(C,D)) = add(add(A,D), add(B,C))`, composed by
// the AC kit from nn.AddSym + nn.AddAssoc;
// 3. Anonymous helper `eqAp`: a pair-equality `x = y` implies
// `treal_eq(x, y)` — Skolemize, case-split on `x = y`, subst
// collapses to `treal_eq(y, y)` which cites TrealEqRefl.
//
// The main goal then assembles: def_expand treal_mul + congr splits the
// pair equality into the two 4-monomial identities; each closes via a
// single simp pass that normalizes with LDistrib flipped, rDistrib,
// MulAssoc (left-nest), and finally perm4 lands the AC permutation.
// The residual treal_eq is delivered by the pair-equality through the
// anonymous bridge.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name: "MulAssoc",
	Key:  "prop_1901ecbc8d864824",
	// The four helper tiers and the main theorem, written as a linear
	// script: each tier is a Go local the next one cites by closure
	// capture.
	Build: family.Sections(
		"∀x y z:prod(hreal, hreal). treal_eq(x * (y * z), x * y * z)",
		func(ctx *Script, headline string) *GoalStackNode {

			// The hreal laws the two rewrite passes below fire, in their
			// canonical install form — the orientation each Flipped/Fwd is
			// stated against.

			// rDistrib — hreal right-distributivity, derived from LDistrib +
			// MulSym rather than cited, so the family takes on no further
			// outside dep.
			//
			//	⊢ ∀x y z : hreal. (x + y)·z = x·z + y·z
			//
			// Route: MulSym flips both sides' outer factor, LDistrib fires on the
			// resulting `z·(x+y)`, and one last MulSym flip on each summand aligns
			// with the target orientation.
			//
			// The closure binds nothing: its x/y/z live at hreal, and the treal
			// sections below mint x₀/y₀/z₀ at the pair type — one type per free
			// name, so this tier leaves the names alone.
			rDistrib := ctx.Lemma(
				"∀x y z:hreal. (x + y) * z = x * z + y * z",
				func(a *Argument) {
					a.Do(
						StripQuant(),
						// Rules: MulSym + LDistrib (flipped so `x·(y+z) → x·y + x·z`).
						// MulSym is unoriented — the whistle keeps it Compare-decreasing
						// on each fire, so it settles the outer-factor position without
						// treadmilling. LDistrib flipped then splits the sum.
						Expect(Simp(
							Fwd(nn.MulSym),      // unoriented; the whistle keeps each fire Compare-decreasing
							Fwd(nn.LeftDistrib), // fires as unfold: x·(y+z) → x·y + x·z
						),
							Case(
								"both sides now have the outer factor on the same side, and the identity normalizes to ⊤",
								TrivialNormalized()),
						),
					)
				})

			// perm4 — the 4-term AC rearrangement lemma:
			//
			//	⊢ ∀A B C D : hreal. (A + B) + (C + D) = (A + D) + (B + C)
			//
			// Cited below as a simp rule, so it is wanted ∀-closed. The AC kit
			// composes it from the family's assoc/sym certificates.
			perm4 := hrealAdd(ctx).RegroupSection(ctx,
				"∀A B C D:hreal. A + B + (C + D) = A + D + (B + C)")

			// eqAp — the anonymous helper:
			//
			//	⊢ ∀x y : hreal × hreal. (x ≠ y) ∨ treal_eq(x, y)
			//
			// Contrapositive form: `x = y ⇒ treal_eq(x, y)`. Case-split on
			// `x = y`; the `x ≠ y` branch trivially matches the LHS disjunct;
			// subst collapses the `x = y` branch to `treal_eq(y, y)` which cites
			// TrealEqRefl. Cited only through eqAp.PromisedThm().
			eqAp := ctx.Lemma(
				"∀x y:prod(hreal, hreal). x ≠ y ∨ treal_eq(x, y)",
				func(a *Argument, x *TermWrapper, y Term) {
					a.Do(
						ByCaseStep(x.Eq(y),
							Case(
								"x_0 = y_0 — subst on the case hyp collapses the goal to treal_eq(y_0, y_0), closed by TrealEqRefl",
								// The branch hands over its discriminant hyp `x_0 = y_0`.
								Given(func(b *Argument, xyEq Fact) {
									b.Do(xyEq.Subst())
									b.Show(
										"hence treal_eq(y₀, y₀)",
										Cite(TrealEqRefl))
								}),
							),
							Case(
								"x_0 ≠ y_0 — the `x ≠ y` disjunct matches the resident "+
									"hyp; refuter closes on the trivial disjunction",
								Basic(),
							),
						),
					)
				})

			// One shared SimpWith cluster for each pair component. The four
			// rules together AC-normalize a bilinearly-expanded triple product
			// to a canonical monomial sum.
			componentClose := func(label string) proof.Case {
				return Case(
					label,
					Expect(Simp(
						Fwd(nn.LeftDistrib), // x·(y+z) → x·y + x·z
						Fwd(rDistrib),       // (x+y)·z → x·z + y·z
						Fwd(nn.MulAssoc),    // left-nest the monomials
						Fwd(perm4),          // the AC 4-way transposition
					),
						Case(
							"both sides normalize to the same canonical 4-monomial sum",
							TrivialNormalized()),
					),
				)
			}

			// The main theorem.
			//
			// Recipe:
			// - Assert the strict pair equality
			// `(x * (y * z)) = ((x * y) * z)`.
			// Two branches result:
			// - Residual (pair_eq as hyp ⊢ treal_eq(...)): cite eqAp, refuter
			// lands the treal_eq via the substitutive-equality bridge.
			// - Pair-eq proof: def_expand treal_mul on both sides makes both
			// pairs literal `((mul + mul), (mul + mul))`;
			// Congr splits into two component identities. Each component
			// closes via one SimpWith pass — LDistrib flipped + rDistrib
			// flipped + MulAssoc unfold every product to left-nested
			// monomials; perm4 lands the resulting 4-monomial AC permutation.
			return ctx.Theorem(headline,
				func(a *Argument, x, y, z Term) {
					// The pair equality asserted mid-flow.
					pairEq := ctx.MakePropText("x₀ * (y₀ * z₀) = x₀ * y₀ * z₀")
					a.Do(
						AssertStep(pairEq,
							Case(
								"treal_mul associates as a strict pair equality — the "+
									"fst/snd-collapsed componentwise SimpWith cluster does the work",
								Unfold(TrealMulDef),
								pairs.Collapse(ctx),
								Expect(Congr(),
									componentClose("component 1: LHS.1 = RHS.1 — the (ace + adf + bcf + bde) 4-way permutation"),
									componentClose("component 2: LHS.2 = RHS.2 — the (acf + ade + bce + bdf) 4-way permutation"),
								),
							),
							Case(
								"pair_eq bridges into treal_eq via the anonymous eqAp helper — refuter grounds it at (LHS, RHS)",
								// The branch hands over the asserted pair equality.
								Given(func(b *Argument, pairEqHyp Fact) {
									b.Show(
										"hence treal_eq of the two associated products",
										By(pairEqHyp, eqAp))
								}),
							),
						),
					)
				})
		}),
})}

// MulLeftId — treal_of_num(1) is a left identity for treal
// multiplication (up to treal_eq):
//
//	⊢ ∀x : treal. treal_eq((treal_of_num(1) * x), x)
//
// treal_of_num(1) is the pair (hreal_of_num(1), hreal_of_num(0)),
// treal_mul expands the pair bilinearly, and treal_eq is the cross-sum
// identity, so unfolding treal_eq → treal_mul → treal_of_num turns the
// goal into an hreal-side identity with four residual products
//
//	(1·xf + 0·xs) + xs = xf + (1·xs + 0·xf)
//
// where xf = fst(x₀), xs = snd(x₀). Four SimpWith rewrites — nn.MulLeftId
// flipped (`1·x → x`), nn.MulLeftZero flipped (`0·x → 0`), nn.AddLeftId
// flipped (`0+x → x`), and nn.AddSym in its natural orientation as an
// ordered-AC canonicalizer — strip the numeric factors and reorient the
// sums. The residual is a bare AC leaf `snd + (fst + 0) = fst + (snd + 0)`
// whose closure needs nn.AddAssoc + nn.AddSym + nn.AddLeftId chained by
// CnfRefute — installing the three as fact hyps completes the leaf.
var MulLeftId = mulLeftIdThm{family.Add(registry.ProofEntry{
	Name: "MulLeftId",
	Key:  "prop_84f4ea356891cb52",
	Build: family.Theorem(
		"∀x:prod(hreal, hreal). treal_eq(treal_of_num(1) * x, x)",
		func(a *Argument, x Term) {
			ctx := a.Ctx()

			// The hreal laws this proof rewrites and closes with, in their
			// canonical install form — the orientation each Flipped/Fwd
			// below is stated against.

			a.Do(
				Unfold(TrealEqDef), // cross-sum identity over fst/snd of the treal_mul terms
				// (a₁,a₂)·(b₁,b₂) → (a₁·b₁+a₂·b₂, a₁·b₂+a₂·b₁); fst/snd applied to the fresh pair literal
				Unfold(TrealMulDef),
				pairs.Collapse(ctx), // project the pair-literal fst/snd redexes exposed by treal_mul
				// treal_of_num(1) → (hreal_of_num(1), hreal_of_num(0)) — a second pair-literal layer
				Unfold(TrealOfNumDef),
				pairs.Collapse(ctx), // project the new fst/snd-of-(hreal_of_num(1), hreal_of_num(0)) redexes
				// Four rewrites strip the numeric factors and reorient the
				// resulting sums: (1·xf + 0·xs) + xs on LHS becomes
				// snd + (fst + 0), and RHS's xf + (1·xs + 0·xf) becomes
				// fst + (snd + 0). The residual is a bare AC leaf modulo `+0`.
				Expect(Simp(
					Fwd(nn.MulLeftId),   // 1·x → x
					Fwd(nn.MulLeftZero), // 0·x → 0
					Fwd(nn.AddLeftId),   // 0+x → x
					Fwd(nn.AddSym),      // ordered-AC canonicalizer
				),
					Case(
						"snd+(fst+0) = fst+(snd+0) — AddAssoc re-brackets, AddSym swaps, AddLeftId absorbs the `+0`",
						By(nn.AddAssoc, nn.AddSym, nn.AddLeftId),
					),
				),
			)
		}),
})}

// LeftDistrib — treal multiplication left-distributes over treal
// addition (up to treal_eq):
//
//	⊢ ∀x y z : treal.
//	 treal_eq((x * (y + z)),
//	 ((x * y) + (x * z)))
//
// treal values are formal differences (a, b) : hreal × hreal; treal_add
// adds componentwise, treal_mul expands bilinearly, and treal_eq is the
// cross-sum identity. Unfolding all three constants and projecting the
// pair-literal fst/snd redexes leaves both sides as balanced 4+4 sums
// mixing distributed products (xf·yf, …) with four remaining factored
// products x·(y+z). One SimpWith pass fires nn.LeftDistrib FLIPPED
// (rewrite `x·(y+z) → x·y + x·z`) to distribute the four factored
// subterms; both sides then hold the SAME 8 elementary products
//
//	xf·yf, xf·zf, xs·ys, xs·zs, xf·ys, xs·yf, xf·zs, xs·zf
//
// but bracketed by two DIFFERENT 4-splittings — LHS bundles by
// (real-part / imag-part) of the factor, RHS bundles by (y-summand /
// z-summand) of the sum. The two arrangements differ by the classical
// 4-arg AC transposition
//
//	(a + b) + (c + d) = (a + c) + (b + d)
//
// applied once per half. The AC bridge itself is a Have in the
// residual's Derive block, closed by nn.AddAssoc and nn.AddSym;
// grounding it at the two 4-atom halves yields the two directed
// rewrites and the residual close reduces to reflexivity.
var LeftDistrib = leftDistribThm{family.Add(registry.ProofEntry{
	Name: "LeftDistrib",
	Key:  "prop_9daf85ee50b8c6bd",
	Build: family.Theorem(
		"∀x y z:prod(hreal, hreal). treal_eq(x * (y + z), x * y + x * z)",
		func(a *Argument, x, y, z Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			hreal := MakeType("hreal")
			fst, snd := pairs.ProjectionsAt(ctx, hreal, hreal)

			// The 8 elementary products the two componentwise expansions
			// share. Named after which projection of which factor they mix:
			// xfYf = fst(x₀)·fst(y₀), xsZs = snd(x₀)·snd(z₀), and so on.
			mul := v.HrealMul
			xf, xs := fst.Apply(x), snd.Apply(x)
			yf, ys := fst.Apply(y), snd.Apply(y)
			zf, zs := fst.Apply(z), snd.Apply(z)
			xfYf, xfZf, xsYs, xsZs := mul.Apply(xf, yf), mul.Apply(xf, zf), mul.Apply(xs, ys), mul.Apply(xs, zs)
			xfYs, xsYf, xfZs, xsZf := mul.Apply(xf, ys), mul.Apply(xs, yf), mul.Apply(xf, zs), mul.Apply(xs, zf)

			// add — hreal_add as an infix-reading builder for the two ground
			// transposition claims.
			add := func(p, q Term) *TermWrapper { return v.HrealAdd.Apply(p, q) }

			// The family's hreal-additive AC spec; the bridge below is its
			// 4-atom transposition, statement and proof both.
			ac := hrealAdd(ctx)

			a.Do(
				Unfold(TrealEqDef),  // cross-sum identity over fst/snd of the treal_add/treal_mul terms
				Unfold(TrealAddDef), // componentwise pairs — first pair-literal layer
				pairs.Collapse(ctx), // project the exposed fst/snd-of-literal-pair redexes
				Unfold(TrealMulDef), // (a₁,a₂)·(b₁,b₂) → (a₁·b₁+a₂·b₂, a₁·b₂+a₂·b₁) — second pair-literal layer
				pairs.Collapse(ctx), // project the new pair-literal fst/snd redexes
				// Both sides now sit as balanced 4+4 sums whose products are
				// partly distributed and partly still factored as
				// `x·(y+z)`. SimpWith fires nn.LeftDistrib flipped
				// (`x·(y+z) → x·y + x·z`) to distribute every remaining
				// factored subterm; the residual holds the two 8-atom sums
				// bracketed by the two 4-splittings the AC transposition
				// bridges.
				Expect(Simp(Fwd(nn.LeftDistrib)), // x·(y+z) → x·y + x·z
					Case(
						"the two sides are one 8-atom sum, bracketed "+
							"(xfYf+xfZf)+(xsYs+xsZs) against (xfYf+xsYs)+(xfZf+xsZs) at each half",
						Derive(func(b *Argument) {
							bridge := b.Have(
								"bridge: 4-arg AC transposition (a+b)+(c+d) = (a+c)+(b+d)",
								ac.Perm4Text(),
								ac.Regroup())
							fstHalf := b.Have(
								"first half: the bridge at (xfYf, xfZf, xsYs, xsZs)",
								MakeProp(add(add(xfYf, xfZf), add(xsYs, xsZs)).
									Eq(add(add(xfYf, xsYs), add(xfZf, xsZs)))),
								By(bridge.At(xfYf, xfZf, xsYs, xsZs)))
							sndHalf := b.Have(
								"second half: the bridge at (xfYs, xsYf, xfZs, xsZf)",
								MakeProp(add(add(xfYs, xsYf), add(xfZs, xsZf)).
									Eq(add(add(xfYs, xfZs), add(xsYf, xsZf)))),
								By(bridge.At(xfYs, xsYf, xfZs, xsZf)))
							b.Show(
								"close: the two ground transpositions rewrite the "+
									"LHS bracketing into the RHS's, leaving reflexivity",
								By(fstHalf, sndHalf))
						}),
					),
				),
			)
		}),
})}

// mulWellDefLeft — treal multiplication respects treal_eq on its
// LEFT argument:
//
//	⊢ ∀x1 x2 y : hreal × hreal.
//	 treal_eq(x1, x2) ⇒ treal_eq((x1 * y), (x2 * y))
//
// After unfolding treal_eq to its hreal_add cross-sum
// and treal_mul to its bilinear pair expansion, the goal reduces to
// an hreal-side polynomial identity between two 4-term sums:
//
//	F(x1)·F(y) + S(x1)·S(y) + F(x2)·S(y) + S(x2)·F(y) =
//	F(x2)·F(y) + S(x2)·S(y) + F(x1)·S(y) + S(x1)·F(y)
//
// (writing F/S for fst/snd, · for hreal_mul, + for hreal_add.) The
// hypothesis `F(x1) + S(x2) = F(x2) + S(x1)` (the ring content of
// treal_eq(x1, x2)) is the only thing that closes the identity, and
// the 4-atom AC rearrangement has to be spelled out rather than left
// to the closing refutation.
//
// The shape asserts two factoring bridges — one for each side
// of the identity, both closed by an `LDISTRIB(flipped) + AC` SimpWith
// pass (the flipped LDISTRIB expands `p·(m+n) → p·m + p·n`, the AC
// rules canonicalize; the hyp fires as a resident side-condition oracle
// during that pass). Each bridge rewrites its side to the factored
// form `mul(add(F1, S2), F(y)) + mul(add(S1, F2), S(y))` and its
// mirror. The Show step installs one more nn.AddSym and closes over the
// two bridges + the hyp — the ring-work is already done by then.
var mulWellDefLeft = mulWellDefLeftThm{family.Add(registry.ProofEntry{
	Name: "mulWellDefLeft",
	Key:  "prop_fa41ad08a58aeaa4",
	Build: family.Theorem(
		Statement{
			Binders: "∀x₁ x₂ y:prod(hreal, hreal).",
			Hypotheses: []string{
				"treal_eq(x₁, x₂)",
			},
			Conclusion: "treal_eq(x₁ * y, x₂ * y)",
		},
		func(a *Argument, x1, x2, y Term) {
			ctx := a.Ctx()
			hreal := MakeType("hreal")
			// Register fst/snd as consts so the bridge claim texts parse
			// (the treal vocab doesn't declare them).
			pairs.ProjectionsAt(ctx, hreal, hreal)

			// The hreal laws the bridge pass fires and closes with, in
			// their canonical install form — the orientation each
			// Flipped/Fwd below is stated against.

			// bridgeProof: given a claim `LHS_orig = LHS_factored` (as
			// asserted below), close it by
			// - one simp pass: LDISTRIB flipped expands the factored
			// right-hand side to atoms; ASSOC + AddSym + MulSym then
			// canonicalize both sides, and hyp0 fires as a side-condition
			// oracle to align the treal_eq-constrained factor;
			// - ASSOC + AddSym close the AC-permutation residual.
			bridgeProof := func() Action {
				return Expect(Simp(
					Fwd(nn.LeftDistrib), // p·(m+n) → p·m + p·n
					Fwd(nn.AddAssoc),    // left-nests the sum tree
					Fwd(nn.AddSym),      // canonicalizes the atom order
					Fwd(nn.MulSym),      // canonicalizes each mul-atom by term order
				),
					Case(
						"associativity and commutativity of + land the AC-permutation between the two canonical sums",
						By(nn.AddAssoc, nn.AddSym),
					),
				)
			}

			// LHS_orig = (F(x1)+S(x2))·F(y0) + (S(x1)+F(x2))·S(y0)
			// The factored right-hand side names the two cross-sums that
			// hyp0 will identify with the RHS's factored form.
			lhsBridgeClaim := ctx.MakePropText(
				"fst(x₁) * fst(y₀) + snd(x₁) * snd(y₀) + (fst(x₂) * snd(y₀) + snd(x₂) * fst(y₀)) = " +
					"(fst(x₁) + snd(x₂)) * fst(y₀) + (snd(x₁) + fst(x₂)) * snd(y₀)")

			// RHS_orig = (F(x2)+S(x1))·F(y0) + (S(x2)+F(x1))·S(y0)
			// The mirror of lhsBridgeClaim — hyp0 will pair the first
			// factors and AddSym the second.
			rhsBridgeClaim := ctx.MakePropText(
				"fst(x₂) * fst(y₀) + snd(x₂) * snd(y₀) + (fst(x₁) * snd(y₀) + snd(x₁) * fst(y₀)) = " +
					"(fst(x₂) + snd(x₁)) * fst(y₀) + (snd(x₂) + fst(x₁)) * snd(y₀)")

			a.Do(
				// hyp0: hreal_add(fst(x₁), snd(x₂)) = hreal_add(fst(x₂), snd(x₁)); goal: cross-sum identity on treal_mul
				Unfold(TrealEqDef),
				Unfold(TrealMulDef), // exposes the two treal_mul terms as pair literals (a₁b₁+a₂b₂, a₁b₂+a₂b₁)
				// project the pair-literal fst/snd redexes — goal becomes a 4+4 sum on hreal atoms
				pairs.Collapse(ctx),
			)
			crossSum := a.Hyp("fst(x₁) + snd(x₂) = fst(x₂) + snd(x₁)")
			bridgeL := a.Have(
				"bridgeL: LHS_expanded folds to (F(x₁)+S(x₂))·F(y₀) + (S(x₁)+F(x₂))·S(y₀) "+
					"— the factored form the cross-sum will identify with the RHS bridge",
				lhsBridgeClaim,
				bridgeProof(),
			)
			bridgeR := a.Have(
				"bridgeR: RHS_expanded folds to (F(x₂)+S(x₁))·F(y₀) + (S(x₂)+F(x₁))·S(y₀) — mirror of bridgeL",
				rhsBridgeClaim,
				bridgeProof(),
			)
			a.Show(
				"close: the two bridges reduce the goal to a symmetric "+
					"4-monomial identity that the cross-sum + one AddSym rewrite align",
				By(crossSum, bridgeL, bridgeR, nn.AddSym))
		}),
})}

// MulWellDef — treal multiplication respects treal_eq in both
// arguments simultaneously:
//
//	⊢ ∀x1 x2 y1 y2 : hreal × hreal.
//	 treal_eq(x1, x2) ∧ treal_eq(y1, y2) ⇒
//	 treal_eq((x1 * y1), (x2 * y2))
//
// The argument is the four-leg equivalence chain in the body — the
// Calc carries legs 1–3, naming the three interior waypoints, and the
// Show carries the terminal one; every leg holds its own
// justification. TrealEqTrans is the chain's transitivity certificate and
// fires three times: CalcRel folds it into legs 2 and 3, and the Show
// grounds it once more to reach the goal.
var MulWellDef = mulWellDefThm{family.Add(registry.ProofEntry{
	Name: "MulWellDef",
	Key:  "prop_f72acb77b9ab5653",
	Build: family.Theorem(
		Statement{
			Binders: "∀x₁ x₂ y₁ y₂:prod(hreal, hreal).",
			Hypotheses: []string{
				"treal_eq(x₁, x₂)",
				"treal_eq(y₁, y₂)",
			},
			Conclusion: "treal_eq(x₁ * y₁, x₂ * y₂)",
		},
		func(a *Argument, x1, x2, y1, y2 Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			mul := v.TrealMul.Apply

			// The chain's five terms: the goal's LHS, three interior
			// waypoints, the goal's RHS.
			start := mul(x1, y1)
			wY1X1 := mul(y1, x1)
			wY2X1 := mul(y2, x1)
			wX1Y2 := mul(x1, y2)
			end := mul(x2, y2)

			// The chain kit: treal_eq as the relation, TrealEqTrans as its
			// transitivity certificate. Calc grounds the certificate at the
			// COMPUTED triple (start, previous waypoint, this waypoint).
			trealEqChain := CalcRel{
				Rel: func(s, t Term) Prop {
					return MakeProp(v.TrealEq.Apply(s, t))
				},
				Trans: TrealEqTrans,
			}

			// Move the antecedent's two conjuncts into the hypotheses
			// (the mulWellDefLeft legs consume them), leaving the bare
			// equivalence treal_mul(x₁,y₁) ≈ treal_mul(x₂,y₂) the chain
			// travels.
			a.Do(Basic())
			eqY := a.Hyp(MakeProp(v.TrealEq.Apply(y1, y2)))
			// Legs 1–3, to the last interior waypoint. Calc cannot
			// carry the fourth: its chained fact would be the goal
			// itself, and asserting the goal as a claim is degenerate
			// — hence the terminal link is the Show below.
			chain := a.Calc(trealEqChain, start,
				// MulSym is cited in ∀-form on its two legs: its
				// conclusion matches each leg exactly, so the install
				// closes before a witness is consumed (which is what the
				// witness form rejects).
				Leg(
					wY1X1,
					"MulSym @ (x₁, y₁): commute, exposing y₁ in the left slot",
					Cite(MulSym)),
				Leg(
					wY2X1,
					"mulWellDefLeft @ (y₁, y₂, x₁): the y-premise now varies a LEFT slot, at fixed right factor x₁",
					By(eqY, At(mulWellDefLeft, y1, y2, x1))),
				Leg(
					wX1Y2,
					"MulSym @ (y₂, x₁): commute back, restoring x₁ to the left slot",
					Cite(MulSym)),
			)
			eqX := a.Hyp(MakeProp(v.TrealEq.Apply(x1, x2)))
			a.Show(
				"leg 4 — mulWellDefLeft @ (x₁, x₂, y₂) varies the left slot at fixed "+
					"y₂; TrealEqTrans @ (x₁·y₁, x₁·y₂, x₂·y₂) folds it onto the chain",
				By(chain, eqX, At(mulWellDefLeft, x1, x2, y2), At(TrealEqTrans, start, wX1Y2, end)))
		}),
})}

// ---------------------------------------------------------------------------
// The numeral embedding ℕ → treal, k ↦ (hreal_of_num k, 0)
// ---------------------------------------------------------------------------
//
// The morphism laws hold up to treal_eq.
//
// README: "the ℕ-embedding morphism laws".

// OfNumEq — the numeral embedding is treal-injective:
//
//	⊢ ∀m n : num. (m = n) ⇔ treal_eq(treal_of_num(m), treal_of_num(n))
//
// Both constants unfold: treal_eq(x, y) is the cross-sum identity
// hreal_add(fst x, snd y) = hreal_add(fst y, snd x), and
// treal_of_num(k) is the pair (hreal_of_num(k), hreal_of_num(0)).
// Collapsing the projections leaves the hreal identity
//
//	(hreal_of_num(m) + hreal_of_num(0))
//	 = (hreal_of_num(n) + hreal_of_num(0))
//
// standing against (m = n). nn.EqAddRightCancel drops the shared zero
// addend, and nn.OfNumEq — hreal-numeral injectivity — closes the
// equivalence by fusion; no refute, so the member adds no keys to the
// family pb.
//
// The pair projections come from cartesian/pairs, as in every member
// here that projects a pair.
var OfNumEq = ofNumEqThm{family.Add(registry.ProofEntry{
	Name: "OfNumEq",
	Key:  "prop_3c401869e57abb76",
	Build: family.Theorem(
		"∀m n:num. m = n ⇔ treal_eq(treal_of_num(m), treal_of_num(n))",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()

			a.Do(
				Unfold(TrealEqDef),        // treal_eq opens to the hreal cross-sum
				Unfold(TrealOfNumDef),     // treal_of_num(k) → (hreal_of_num(k), hreal_of_num(0))
				pairs.Collapse(ctx),       // project fst/snd out of the pair literals
				Cite(nn.EqAddRightCancel), // right-cancel the shared hreal_of_num(0)
				Cite(nn.OfNumEq),          // hreal-numeral injectivity closes the iff
			)
		}),
})}

// OfNumLessEq — the numeral embedding is treal-order-faithful:
//
//	⊢ ∀m n : num. (m ≤ n) ⇔ (treal_of_num(m) ≤ treal_of_num(n))
//
// Both constants unfold: treal_of_num(k) is the pair (hreal_of_num(k),
// hreal_of_num(0)), and treal_le(x, y) is the cross-sum comparison
// hreal_le(fst x + snd y, fst y + snd x). Collapsing the projections
// leaves
//
//	(hreal_of_num(m) + hreal_of_num(0)) ≤
//	 (hreal_of_num(n) + hreal_of_num(0))
//
// standing against (m ≤ n) — the hreal-side statement carrying a zero
// addend on each side. Three facts discharge it: nn.AddSym brings the
// trailing zero to the front, nn.AddLeftId deletes it, and
// nn.OfNumLessEq is the hreal-side order embedding.
//
// Mechanically the ⇔ has CNF-normalized into a single refute
// obligation by the time the pairs appear, so the projections are
// collapsed inside a hypothesis rather than in the goal, and the three
// facts install as rewriting facts for the closing refute.
//
// The pair projections come from cartesian/pairs — as in OfNumEq.
var OfNumLessEq = ofNumLessEqThm{family.Add(registry.ProofEntry{
	Name: "OfNumLessEq",
	Key:  "prop_d9cab71f8dbb2838",
	Build: family.Theorem(
		"∀m n:num. m ≤ n ⇔ treal_of_num(m) ≤ treal_of_num(n)",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()

			a.Do(
				Unfold(TrealOfNumDef), // treal_of_num(k) → (hreal_of_num(k), hreal_of_num(0))
				Unfold(TrealLeDef),    // treal_le opens to the hreal cross-sum comparison
				pairs.Collapse(ctx),   // project fst/snd out of the pair literals
				Cite(nn.OfNumLessEq),  // the hreal-side order embedding
				Cite(nn.AddLeftId),    // 0 is a left identity for hreal_add
				Cite(nn.AddSym),       // commute, so left identity reaches the trailing 0
				CnfRefute(),
			)
		}),
})}

// OfNumAdd — the treal_of_num morphism preserves addition (up to
// treal_eq):
//
//	⊢ ∀m n : num. treal_eq((treal_of_num(m) + treal_of_num(n)),
//	 treal_of_num(m + n))
//
// treal_of_num(k) pairs the numeral against zero as (hreal_of_num(k),
// hreal_of_num(0)), and treal_add on pairs is componentwise hreal
// addition. Unfolding treal_eq → treal_add → treal_of_num exposes
// fst/snd over the resulting pair literals; PairCollapse projects
// them out, leaving a bare hreal identity between two sums. One
// SimpWith pass finishes it: nn.OfNumAdd splits hreal_of_num(m + n)
// into hreal_add(hreal_of_num(m), hreal_of_num(n)), nn.AddLeftId
// (fired right-to-left — its natural form keeps the bare side on the
// left) absorbs the hreal_of_num(0) addends, and nn.AddSym reorients
// the trailing 0-addend so AddLeftId can reach it. Both sides reduce
// to the same sum and the residual normalizes to ⊤ — refute-free.
var OfNumAdd = ofNumAddThm{family.Add(registry.ProofEntry{
	Name: "OfNumAdd",
	Key:  "prop_e5e74b23d2426bc6",
	Build: family.Theorem(
		"∀m n:num. treal_eq(treal_of_num(m) + treal_of_num(n), treal_of_num(m + n))",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()
			a.Do(
				Unfold(TrealEqDef),    // exposes (fst(_) + snd(_)) = (fst(_) + snd(_))
				Unfold(TrealAddDef),   // (a₁, a₂)+(b₁, b₂) → (a₁+b₁, a₂+b₂) under the projections
				Unfold(TrealOfNumDef), // treal_of_num(k) → (hreal_of_num(k), hreal_of_num(0))
				pairs.Collapse(ctx),   // project every fst/snd-of-literal-pair redex out
				// Post-collapse residual (o = hreal_of_num):
				// ((o(m₀) + o(n₀)) + o(0)) =
				// (o(m₀ + n₀) + (o(0) + o(0)))
				Expect(Simp(
					Rev(nn.OfNumAdd),  // o(m + n) → o(m) + o(n)
					Fwd(nn.AddLeftId), // o(0) + x → x
					Fwd(nn.AddSym),    // ordered-AC canonicalizer
				),
					Case(
						"both sides reduce to (hreal_of_num(m) + hreal_of_num(n))",
						TrivialNormalized()),
				),
			)
		}),
})}

// OfNumMul — the treal numeral embedding respects multiplication:
//
//	⊢ ∀m n : num. treal_eq((treal_of_num(m) * treal_of_num(n)),
//	 treal_of_num(m * n))
//
// treal_of_num(k) pairs the numeral against zero as `(hreal_of_num(k),
// hreal_of_num(0))`, and treal_mul expands the pair bilinearly, so
// after unfolding both sides the goal collapses to an hreal-side
// identity that boils down to four cited facts, each in its
// as-written orientation:
//
// - nn.OfNumMul — the hreal-tier multiplicativity this proof lifts;
// - nn.MulLeftZero — collapses the three cross terms whose zero
// factor stands on the LEFT;
// - nn.AddLeftId — strips the residual zero addends;
// - nn.AddSym — reorients the asymmetric leftover.
//
// One factor pattern, `(hreal_of_num(m) * hreal_of_num(0))`,
// carries its zero on the RIGHT and so falls outside nn.MulLeftZero's
// pattern. The intermediate `mulRightZero` fact commutes it via
// nn.MulSym first — a single Have stages it as a fifth premise of the
// close.
var OfNumMul = ofNumMulThm{family.Add(registry.ProofEntry{
	Name: "OfNumMul",
	Key:  "prop_749b9480abe6d09",
	Build: family.Theorem(
		"∀m n:num. treal_eq(treal_of_num(m) * treal_of_num(n), treal_of_num(m * n))",
		func(a *Argument, m, n Term) {
			ctx := a.Ctx()

			// After the def-expands of treal_eq/treal_mul the goal has fst
			// and snd applied to pair literals; PairCollapse projects them
			// out. The later def-expand of treal_of_num exposes a second
			// layer of redexes over its (hreal_of_num(k), hreal_of_num(0))
			// literals — a second collapse leaves a pure hreal-side equation.
			a.Do(
				Unfold(TrealEqDef),    // exposes (fst(_) + snd(_)) = (fst(_) + snd(_))
				Unfold(TrealMulDef),   // (a₁, a₂)·(b₁, b₂) → (a₁·b₁ + a₂·b₂, a₁·b₂ + a₂·b₁)
				pairs.Collapse(ctx),   // project the exposed fst/snd redexes
				Unfold(TrealOfNumDef), // treal_of_num(k) → (hreal_of_num(k), hreal_of_num(0))
				pairs.Collapse(ctx),   // second redex layer over the numeral pairs
			)
			mulRightZero := a.Have(
				"mulRightZero: the right-zero product collapses — nn.MulSym "+
					"commutes it into the left-zero shape nn.MulLeftZero recognizes",
				"hreal_of_num(m) * hreal_of_num(0) = hreal_of_num(0)",
				By(nn.MulSym, nn.MulLeftZero))
			a.Show(
				"OfNumMul folds m·n, the zero-factor cross terms drop, and the residual zero addends are absorbed",
				By(Normalized, mulRightZero, nn.OfNumMul, nn.MulLeftZero, nn.AddLeftId, nn.AddSym),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The treal order
// ---------------------------------------------------------------------------
//
// `treal_le` compares cross-sums exactly as `treal_eq` does, so most of
// these laws are an hreal order fact once the two constants are unfolded
// and the pair projections collapse;
//
// LessEqMul, which must multiply two cross-sum comparisons out, is the
// one that does real work. The movement closes on LessEqWellDef, the
// quotient's descent datum for ≤.
//
// README: "the total order with its add/mul compatibility laws".

// LessEqTrans — the treal order is transitive:
//
//	⊢ ∀x y z : treal. (x ≤ y) ∧ (y ≤ z) ⇒ (x ≤ z)
//
// After def-unfolding treal_le the two premises are resident hyps and
// goal and hyps are all hreal_le on cross-sums:
//
//	hyp₁ : (F(x)+S(y) ≤ F(y)+S(x)) — (x ≤ y)
//	hyp₂ : (F(y)+S(z) ≤ F(z)+S(y)) — (y ≤ z)
//	 ⊢ (F(x)+S(z) ≤ F(z)+S(x)) — (x ≤ z)
//
// (F = fst, S = snd.) Add the two hyps with nn.LessEqAdd2 to get a
// sum-bound on (F(x)+S(y))+(F(y)+S(z)) ≤ (F(y)+S(x))+(F(z)+S(y)); AC
// (nn.AddSym + nn.AddAssoc) reshuffles the two sums into
// (F(x)+S(z))+(F(y)+S(y)) ≤ (F(z)+S(x))+(F(y)+S(y)); the trailing
// F(y)+S(y) is cancelled by nn.LessEqAddRight, leaving the goal.
//
// Written flat as two shuffle-facts followed by a cancel Show: the
// asserted equalities are the only NEW arithmetic obligation, and each
// is pure AC.
var LessEqTrans = lessEqTransThm{family.Add(registry.ProofEntry{
	Name: "LessEqTrans",
	Key:  "prop_3a807261e57c4095",
	Build: family.Theorem(
		Statement{
			Binders: "∀x y z:prod(hreal, hreal).",
			Hypotheses: []string{
				"x ≤ y",
				"y ≤ z",
			},
			Conclusion: "x ≤ z",
		},
		func(a *Argument, x, y, z Term) {
			a.Do(Unfold(TrealLeDef)) // unfold both sides to hreal_le on cross-sums
			leXY := a.Hyp("fst(x) + snd(y) ≤ fst(y) + snd(x)")
			leYZ := a.Hyp("fst(y) + snd(z) ≤ fst(z) + snd(y)")
			shiftLHS := a.Have(
				"shiftLHS: (F(x)+S(y))+(F(y)+S(z)) rearranges to (F(x)+S(z))+(F(y)+S(y))",
				"fst(x) + snd(y) + (fst(y) + snd(z)) = fst(x) + snd(z) + (fst(y) + snd(y))",
				By(nn.AddSym, nn.AddAssoc))
			shiftRHS := a.Have(
				"shiftRHS: (F(y)+S(x))+(F(z)+S(y)) rearranges to (F(z)+S(x))+(F(y)+S(y))",
				"fst(y) + snd(x) + (fst(z) + snd(y)) = fst(z) + snd(x) + (fst(y) + snd(y))",
				By(nn.AddSym, nn.AddAssoc))
			a.Show(
				"cancel: LessEqAdd2 sums the two premises, the shifts rewrite "+
					"both sides to the common (F(y)+S(y)) tail, RCANCEL removes it",
				By(leXY, leYZ, shiftLHS, shiftRHS, nn.LessEqAdd2, nn.LessEqAddRight))
		}),
})}

// LessEqAntisym — treal equivalence coincides with two-sided treal_le:
//
//	⊢ ∀x y : treal. treal_eq(x, y) ⇔ (x ≤ y) ∧ (y ≤ x)
//
// After unfolding treal_eq and treal_le, both sides of the iff live at
// the hreal layer:
//
//	treal_eq(x, y) ↦ F(x) + S(y) = F(y) + S(x)
//	(x ≤ y) ↦ (F(x)+S(y) ≤ F(y)+S(x))
//	(y ≤ x) ↦ (F(y)+S(x) ≤ F(x)+S(y))
//
// (F = fst, S = snd.) The goal becomes the shape of nn.LessEqAntisym at
// the cross-sum witnesses (a = F(x)+S(y), b = F(y)+S(x)):
//
//	(a = b) ⇔ ((a ≤ b) ∧ (b ≤ a))
//
// One cite closes.
var LessEqAntisym = lessEqAntisymThm{family.Add(registry.ProofEntry{
	Name: "LessEqAntisym",
	Key:  "prop_e0b5c82eb4440604",
	Build: family.Theorem(
		"∀x y:prod(hreal, hreal). treal_eq(x, y) ⇔ x ≤ y ∧ y ≤ x",
		func(a *Argument, x, y Term) {
			a.Do(
				Unfold(TrealEqDef),     // LHS → hreal cross-sum equality
				Unfold(TrealLeDef),     // both conjuncts → hreal_le on cross-sums
				Cite(nn.LessEqAntisym), // (a = b) ⇔ le(a,b) ∧ le(b,a) — closes on the (F+S, F+S) witnesses
			)
		}),
})}

// LessEqTotal — the treal order is total, reduced by one def-unfold to
// hreal-level totality on cross-sums:
//
//	⊢ ∀x y : treal. (x ≤ y) ∨ (y ≤ x)
//
// treal_le(x, y) ∨ treal_le(y, x) unfolds to the same disjunction with
// hreal_le on cross-sums; nn.LessEqTotal covers every pair of hreals.
var LessEqTotal = lessEqTotalThm{family.Add(registry.ProofEntry{
	Name: "LessEqTotal",
	Key:  "prop_fe3277d00c599456",
	// The closure binds nothing: the def-unfold reaches under the ∀-prefix,
	// so the statement's binders never have to be stripped.
	Build: family.Theorem(
		"∀x y:prod(hreal, hreal). x ≤ y ∨ y ≤ x",
		func(a *Argument) {
			a.Do(Unfold(TrealLeDef)) // treal_le → hreal_le on cross-sums
			a.Show(
				"hreal totality covers the two cross-sums",
				By(nn.LessEqTotal))
		}),
})}

// LessEqAddLeftImp — treal_le is preserved by left addition:
//
//	⊢ ∀x y z : treal. (y ≤ z) ⇒ ((x + y) ≤ (x + z))
//
// After def-unfolding treal_le and treal_add, the goal becomes a plain
// hreal_le monotonicity obligation over pair cross-sums:
//
//	hyp₁ : (F(y)+S(z) ≤ F(z)+S(y)) — (y ≤ z)
//	 ⊢ ((F(x)+F(y))+(S(x)+S(z)) ≤ (F(x)+F(z))+(S(x)+S(y))) — (x+y ≤ x+z)
//
// (F = fst, S = snd.) Under AC each side splits into the same
// common addend (F(x)+S(x)) plus one factor from the hypothesis:
//
//	LHS = (F(x)+S(x)) + (F(y)+S(z))
//	RHS = (F(x)+S(x)) + (F(z)+S(y))
//
// so cancelling the common addend leaves exactly hyp₁. Two Have blocks
// state the AC regroupings (each pure AC); the closing
// Show cancels the common (F(x)+S(x)) with
// nn.LessEqAddRight + nn.AddSym — same shape as LessEqTrans's
// AC-shuffle + cancel pattern.
var LessEqAddLeftImp = lessEqAddLeftImpThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddLeftImp",
	Key:  "prop_77a2aa9457b6629c",
	Build: family.Theorem(
		Statement{
			Binders: "∀x y z:prod(hreal, hreal).",
			Hypotheses: []string{
				"y ≤ z",
			},
			Conclusion: "x + y ≤ x + z",
		},
		func(a *Argument, x, y, z Term) {
			ctx := a.Ctx()
			a.Do(
				Unfold(TrealLeDef),  // both sides collapse to hreal_le on cross-sums
				Unfold(TrealAddDef), // (a,b)+(c,d) = (a+c, b+d) — exposes fst/snd redexes over pair literals
				pairs.Collapse(ctx), // project them out; goal is now pure hreal_le on flat sums
			)
			leYZ := a.Hyp("fst(y) + snd(z) ≤ fst(z) + snd(y)")
			regroupLHS := a.Have(
				"regroupLHS: (F(x)+F(y))+(S(x)+S(z)) = (F(x)+S(x))+(F(y)+S(z))",
				"fst(x) + fst(y) + (snd(x) + snd(z)) = fst(x) + snd(x) + (fst(y) + snd(z))",
				By(nn.AddAssoc, nn.AddSym))
			regroupRHS := a.Have(
				"regroupRHS: (F(x)+F(z))+(S(x)+S(y)) = (F(x)+S(x))+(F(z)+S(y))",
				"fst(x) + fst(z) + (snd(x) + snd(y)) = fst(x) + snd(x) + (fst(z) + snd(y))",
				By(nn.AddAssoc, nn.AddSym))
			// SYM reorients RCANCEL's (m+p, n+p) shape to match the
			// (m+n, m+p) common-prefix pattern the regroups expose.
			a.Show(
				"cancel: RCANCEL + SYM strip the common (F(x)+S(x)) prefix, leaving the hyp",
				By(leYZ, regroupLHS, regroupRHS, nn.LessEqAddRight, nn.AddSym))
		}),
})}

// LessEqMul — treal multiplication preserves nonnegativity up to
// treal_le:
//
//	⊢ ∀x y : treal. (0 ≤ x) ∧ (0 ≤ y) ⇒ (0 ≤ x·y)
//
// treal values are formal-difference pairs (a, b) : hreal × hreal;
// treal_le(0, x) unfolds (with treal_of_num(0) = (h0, h0)) to the pure
// hreal statement snd(x) ≤ fst(x). Componentwise, (x * y) is
// (F(x)·F(y) + S(x)·S(y), F(x)·S(y) + S(x)·F(y)), so the goal collapses
// to the elementary hreal inequality
//
//	F(x)·S(y) + S(x)·F(y) ≤ F(x)·F(y) + S(x)·S(y)
//
// (F = fst, S = snd.) Classical route: LessEqExists extracts witnesses
// d1, d2 with F(x) = S(x) + d1, F(y) = S(y) + d2, and the goal reduces
// to A ≤ A + d1·d2 (LessEqSelfAdd) via the bilinear ring identity
//
//	(b+p)·(d+q) + b·d = ((b+p)·d + b·(d+q)) + p·q
//
// which packages the (F(x)·F(y) + S(x)·S(y)) − (F(x)·S(y) + S(x)·F(y))
// = d1·d2 residual as a single equation on abstract hreal frees.
//
// Proof shape:
//
// 1. `ringIdent` — the bilinear identity on abstract hreal frees,
// proved by one SimpWith(LDistrib flipped + MulSym + AC) pass —
// both sides normalize to identical 5-monomial sums — followed by
// an AC-refute close.
//
// 2. Main — def-unfolds + PairCollapse expose the hreal form; two
// Have blocks lift the noisy hyps (0+S(v) ≤ F(v)+0) to the clean
// (S(v) ≤ F(v)); LessEqExists on each clean hyp yields
// F(v) = S(v) + d_v, which Rw substitutes out of the goal; and the
// close is the ring identity at (S(x₀), d₀, S(y₀), d₁) together
// with LessEqSelfAdd at (LHS_sum, d₀·d₁).
var LessEqMul = lessEqMulThm{family.Add(registry.ProofEntry{
	Name: "LessEqMul",
	Key:  "prop_941230ff756b6fab",
	// The proof is one lemma plus the assembly: `ringIdent` is a Go local
	// the goal ground-cites by closure capture.
	Build: family.Sections(
		Statement{
			Binders: "∀x y:prod(hreal, hreal).",
			Hypotheses: []string{
				"treal_of_num(0) ≤ x",
				"treal_of_num(0) ≤ y",
			},
			Conclusion: "treal_of_num(0) ≤ x * y",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// The hreal laws the two rewrite passes fire and the leaves
			// close with, in their canonical install form — the orientation
			// each Flipped/Fwd below is stated against.
			lessEqAddRight := ctx.DepNormalized(nn.LessEqAddRight)

			// ringIdent — the bilinear ring identity on abstract hreal frees:
			//
			//	⊢ ∀b p d q : hreal. (b+p)·(d+q) + b·d = ((b+p)·d + b·(d+q)) + p·q
			//
			// Both sides expand to the same 5-monomial sum 2·b·d + b·q + p·d + p·q;
			// one SimpWith pass with LDistrib flipped (fires as `x·(y+z) → x·y+x·z`
			// against the whistle order) + MulSym + AC-normalizers converts both
			// sides to canonical monomial trees, and an AC-refute with AddAssoc +
			// AddSym resident closes the residual sum-tree permutation. It is
			// cited by the main proof after the F(v) = S(v) + d_v equations Rw
			// the goal into the identity's (b+p)·(d+q) + b·d = … shape.
			ringIdent := ctx.Lemma(
				"∀b p d q:hreal. (b + p) * (d + q) + b * d = (b + p) * d + b * (d + q) + p * q",
				func(a *Argument, b, p, d, q Term) {
					// One rule set: LDistrib flipped (whistle fires it as unfold
					// `x·(y+z) → x·y+x·z`), MulSym to shuffle outer factors, and
					// AddSym+AddAssoc to canonicalize add-trees. Both sides
					// converge to the same 5-monomial sum.
					a.Do(Expect(Simp(
						Fwd(nn.LeftDistrib), // x·(y+z) → x·y + x·z
						Fwd(nn.MulSym),      // shuffles outer factors
						Fwd(nn.AddSym),      // whistle-ordered AC
						Fwd(nn.AddAssoc),    // whistle-ordered AC
					),
						Case(
							"both sides are now canonical 5-monomial sums, equal up to AC",
							By(nn.AddAssoc, nn.AddSym),
						),
					))
				})

			// The main theorem.
			hreal := MakeType("hreal")
			fst, snd := pairs.ProjectionsAt(ctx, hreal, hreal)
			// The LessEqExists witnesses. Declared so the Have claim texts +
			// ringIdent ground-cite terms below reference the same core vars
			// the goal contains.
			d1 := ctx.Var("d_0", hreal) // Skolem name auto-generated by strip on 1st ∃
			d2 := ctx.Var("d_1", hreal) // Skolem name auto-generated on 2nd ∃

			return ctx.Theorem(headline,
				func(a *Argument, x, y Term) {
					// The LHS sum of the goal after F-substitution, used to ground
					// LessEqSelfAdd at (LHS_sum, d_0·d_1).
					lhsSum := v.HrealAdd.Apply(
						v.HrealMul.Apply(v.HrealAdd.Apply(snd.Apply(x), d1), snd.Apply(y)),
						v.HrealMul.Apply(snd.Apply(x), v.HrealAdd.Apply(snd.Apply(y), d2)),
					)
					a.Do(
						Unfold(TrealLeDef),    // treal_le → cross-sum hreal_le on fst/snd
						Unfold(TrealOfNumDef), // 0 → (h0, h0)
						Unfold(TrealMulDef),   // treal_mul → bilinear pair literal
						pairs.Collapse(ctx),   // project all exposed pair-literal fst/snd redexes
						// One SimpWith pass strips the 0-shifts from the goal (AddSym
						// flips `A + 0` to `0 + A`, AddLeftId flipped fires `0 + A → A`
						// on both sides). Hyps stay noisy but the clean derivatives
						// below carry the load.
						Expect(Simp(
							Fwd(nn.AddLeftId), // 0 + A → A
							Fwd(nn.AddSym),    // flips `A + 0` so AddLeftId reaches it
						),
							Case(
								"the goal, now F·S + S·F ≤ F·F + S·S, follows from the hypotheses stripped of their 0-shifts",
								Derive(func(b *Argument) {
									noisyX := b.Hyp("hreal_of_num(0) + snd(x₀) ≤ fst(x₀) + hreal_of_num(0)")
									noisyY := b.Hyp("hreal_of_num(0) + snd(y₀) ≤ fst(y₀) + hreal_of_num(0)")
									hLeqX := b.Have(
										"hLeqX: snd(x_0) ≤ fst(x_0) — RCANCEL + AddLeftId + AddSym strip the 0-shifts from the x hyp",
										"snd(x₀) ≤ fst(x₀)",
										By(noisyX, lessEqAddRight, nn.AddLeftId, nn.AddSym))
									hLeqY := b.Have(
										"hLeqY: snd(y_0) ≤ fst(y_0) — same cancel on the y hyp",
										"snd(y₀) ≤ fst(y₀)",
										By(noisyY, lessEqAddRight, nn.AddLeftId, nn.AddSym))
									// LessEqExists at (S(v), F(v)), its guard the
									// clean le-hyp listed with it: Unpack peels the
									// ∃ and hands back the gap equation
									// F(v) = S(v) + d_v.
									_, xEq := b.Unpack(GroupPremises(hLeqX, At(nn.LessEqExists, snd.Apply(x), fst.Apply(x))))
									_, yEq := b.Unpack(GroupPremises(hLeqY, At(nn.LessEqExists, snd.Apply(y), fst.Apply(y))))
									// Each Rw substitutes its F(v) → S(v)+d_v
									// throughout the goal and the surviving hyps.
									b.Do(yEq.Rw())
									b.Do(xEq.Rw())
									b.Show(
										"close: the ring identity at (S(x_0), d_0, S(y_0), d_1) rewrites the "+
											"goal's LHS into LHS_sum + d_0·d_1, and LessEqSelfAdd there lands it",
										By(
											At(ringIdent, snd.Apply(x), d1, snd.Apply(y), d2),
											At(nn.LessEqSelfAdd, lhsSum, v.HrealMul.Apply(d1, d2)),
										))
								}),
							),
						),
					)
				})
		}),
})}

// LessEqWellDef descends the treal order to formal-difference classes.
var LessEqWellDef = lessEqWellDefThm{family.Add(registry.ProofEntry{
	Name: "LessEqWellDef",
	Key:  "prop_84ba26bcc771fce1",
	Build: family.Theorem(
		Statement{
			Binders: "∀x₁ x₂ y₁ y₂:prod(hreal, hreal).",
			Hypotheses: []string{
				"treal_eq(x₁, x₂)",
				"treal_eq(y₁, y₂)",
			},
			Conclusion: "x₁ ≤ y₁ ⇔ x₂ ≤ y₂",
		},
		func(a *Argument, x1, x2, y1, y2 *Expr[Prod[Hreal, Hreal]], equivalent Fact) {
			xBounds := a.Have(
				"equivalent lower endpoints bound each other",
				"x₁ ≤ x₂ ∧ x₂ ≤ x₁",
				By(equivalent, LessEqAntisym.At(x1, x2)))
			yBounds := a.Have(
				"equivalent upper endpoints bound each other",
				"y₁ ≤ y₂ ∧ y₂ ≤ y₁",
				By(equivalent, LessEqAntisym.At(y1, y2)))
			a.Iff()
			a.Forward(
				"transport the comparison to x₂ and y₂",
				func(b *Argument, comparison Fact) {
					lower := b.Have(
						"x₂ ≤ x₁ ≤ y₁",
						"x₂ ≤ y₁",
						By(xBounds, comparison, LessEqTrans.At(x2, x1, y1)))
					b.Show(
						"continue through y₁ ≤ y₂",
						By(lower, yBounds, LessEqTrans.At(x2, y1, y2)))
				})
			a.Backward(
				"transport the comparison to x₁ and y₁",
				func(b *Argument, comparison Fact) {
					lower := b.Have(
						"x₁ ≤ x₂ ≤ y₂",
						"x₁ ≤ y₂",
						By(xBounds, comparison, LessEqTrans.At(x1, x2, y2)))
					b.Show(
						"continue through y₂ ≤ y₁",
						By(lower, yBounds, LessEqTrans.At(x1, y2, y1)))
				})
		}),
})}
