// monotone.go — monotone and bounded means convergent, and the limit
// is the extremum.
//
// README, "Monotone and bounded means convergent". A rising sequence
// bounded above converges to the supremum of its range, a falling one
// bounded below to the infimum, and the classical sentence — a
// monotone bounded sequence converges — is the corollary. The movement
// opens with the bridge both wings stand on: a sequence that is
// monotone from each term to the next is monotone between any two
// indices, which is what carries the one term the extremum's
// approximation law hands over to every later term of the tail. It
// closes with a first use of the falling wing, PowerTendsToZero: the
// powers of a number below 1 in size tend to 0.
//
// A member that argues a convergence GOAL from its ε-N statement opens
// it by `Unfold(RealConvergesToDef)`, which, as a side effect, splits
// the conjunctive hypothesis into its two halves — so those members
// take the hypothesis as `_ Fact` and name the halves by `arg.Hyp`.

package real_sequences

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// IncreasingLessEq — a sequence that never falls from one term to the
// next (increasing, step by step) never falls at all.
//
// The finite-interval law for preorders composes the adjacent steps.
var IncreasingLessEq = increasingLessEqThm{family.Add(registry.ProofEntry{
	Name: "IncreasingLessEq",
	Key:  "prop_d79bf0814771fab0",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀m n:num.",
		Hypotheses: []string{
			"∀k:num. a(k) ≤ a(k + 1)",
			"m ≤ n",
		},
		Conclusion: "a(m) ≤ a(n)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], m, n *Expr[Nat], step, le Fact) {
			preorder := arg.Have(
				"the real order is reflexive and transitive",
				"preorder(λx:real. λy:real. x ≤ y)",
				order.Preorder.Intro(
					Case(
						"each real is below itself",
						Unfold(equivalence.ReflexiveDef),
						Cite(real_order_ring.LessEqRefl)),
					Case(
						"two comparisons compose",
						Unfold(equivalence.TransitiveDef),
						Cite(real_construction.LessEqTrans))))
			arg.Show(
				"the adjacent steps compose across the interval from m to n",
				By(step, le, order.MonotoneOnNatInterval.Read(preorder).At(a, m, n)))
		}),
})}

// DecreasingLessEq — a sequence that never rises from one term to the
// next (decreasing, step by step) never rises at all; the mirror of
// IncreasingLessEq, read through negation.
//
// The negated sequence -a rises step by step, since -a(n) ≤ -a(n + 1)
// is the step a(n + 1) ≤ a(n) with both sides negated. So
// IncreasingLessEq at -a carries -a(m) ≤ -a(n) across any m ≤ n, and
// negating both sides back gives a(n) ≤ a(m).
var DecreasingLessEq = decreasingLessEqThm{family.Add(registry.ProofEntry{
	Name: "DecreasingLessEq",
	Key:  "prop_ad394fcf7b90787c",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀m n:num.",
		Hypotheses: []string{
			"∀k:num. a(k + 1) ≤ a(k)",
			"m ≤ n",
		},
		Conclusion: "a(n) ≤ a(m)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], step Fact) {
			negated := arg.TermAs[Fun[Nat, Real]]("λn:num. -a(n)")
			rises := arg.Have(
				"the negated sequence -a rises step by step",
				"∀n:num. -a(n) ≤ -a(n + 1)",
				Derive(func(g *Argument) {
					n := g.FixAs[Nat]()
					next := g.TermAs[Nat]("n + 1")
					g.Show(
						"-a(n) ≤ -a(n + 1) is the step a(n + 1) ≤ a(n) with both sides negated",
						By(step.At(n), real_order_ring.LessEqNeg2.At(a.Apply(n), a.Apply(next))))
				}))

			m := arg.FixAs[Nat]("m")
			n := arg.FixAs[Nat]("n")
			le := arg.Assume()
			arg.Show(
				"so -a(m) ≤ -a(n) by the rising case at -a, and negating both sides back gives a(n) ≤ a(m)",
				By(
					rises,
					le,
					IncreasingLessEq.At(negated, m, n),
					real_order_ring.LessEqNeg2.At(a.Apply(m), a.Apply(n))))
		}),
})}

// IncreasingBoundedConvergesToSup — a rising sequence bounded above
// converges, and its limit is the supremum of its range.
//
// The range image(a, 𝕌) holds every term, so it is nonempty, and B
// bounds it; hence sup of the range is its supremum. Given ε > 0 the
// supremum is approached from inside: some member of the range — a
// term a(N) — exceeds sup − ε. Past N every term is at least a(N),
// because the sequence rises, and at most the supremum, because it caps
// the range; so the tail past N lies in ⟬sup − ε, sup⟧, within ε of sup.
var IncreasingBoundedConvergesToSup = increasingBoundedConvergesToSupThm{family.Add(registry.ProofEntry{
	Name: "IncreasingBoundedConvergesToSup",
	Key:  "prop_b88e8fde0db957aa",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. a(n) ≤ a(n + 1)",
			"∀n:num. a(n) ≤ B",
		},
		Conclusion: "a ⟶ sup(image(a, 𝕌))",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], _ Fact) {
			arg.Do(Unfold(RealConvergesToDef))
			step := arg.Hyp("∀n:num. a(n) ≤ a(n + 1)")
			bounded := arg.Hyp("∀n:num. a(n) ≤ B")
			naturals := arg.TermAs[Set[Nat]]("𝕌")
			image := arg.TermAs[Set[Real]]("image(a, 𝕌)")
			supremum := arg.TermAs[Real]("sup(image(a, 𝕌))")
			zero := arg.Ctx().Nat(0)

			nonempty := arg.Have(
				"the range is nonempty — a(0) is in it",
				"image(a, 𝕌) ≠ ∅",
				By(
					Normalized,
					set_image.FunInImage.At(a, naturals, zero),
					set_basic.InUniv.At(zero),
					set_basic.MemberNotEmpty.At(image)))
			boundedAbove := arg.Have(
				"and B bounds it: a bound on the range is a bound on every term, read back along a",
				"∀x:real. x ∈ image(a, 𝕌) ⇒ x ≤ B",
				By(
					bounded,
					set_image.ForallInImage.At(a, naturals, arg.TermAs[Set[Real]]("λx:real. x ≤ B")),
					set_basic.InUniv))
			hasSup := arg.Have(
				"so sup of the range is its supremum",
				"real_has_sup(image(a, 𝕌), sup(image(a, 𝕌)))",
				By(nonempty, boundedAbove, real_sup_inf.HasSupIsSup.At(image, supremum)))

			arg.FixAs[Real]()
			pos := arg.Assume()
			belowSup := arg.TermAs[Real]("sup(image(a, 𝕌)) - ε")
			strictlyBelow := arg.Have(
				"the strict ordering the approximation law asks for: sup − ε lies below the supremum",
				"sup(image(a, 𝕌)) - ε < sup(image(a, 𝕌))",
				ByArith(pos))
			N, exceeds := arg.ObtainAs[Nat](
				"the supremum is approached from inside: a member of the range "+
					"exceeds sup − ε, and a member of the range is a term a(N)",
				"∃N:num. sup(image(a, 𝕌)) - ε < a(N)",
				By(
					hasSup,
					strictlyBelow,
					real_sup_inf.HasSupApproach.At(image, supremum, belowSup),
					set_image.ExistsInImage.At(
						a, naturals, arg.TermAs[Set[Real]]("λy:real. sup(image(a, 𝕌)) - ε < y"))))

			arg.Take(N)
			n := arg.FixAs[Nat]()
			past := arg.Assume()
			risen := arg.Have(
				"past N the sequence has risen at least to a(N)",
				"a(N) ≤ a(n)",
				By(step, past, IncreasingLessEq.At(a, N, n)))
			capped := arg.Have(
				"and the supremum caps every term — a(n) is in the range",
				"a(n) ≤ sup(image(a, 𝕌))",
				By(
					hasSup,
					set_image.FunInImage.At(a, naturals, n),
					set_basic.InUniv.At(n),
					real_sup_inf.HasSupUpperBound.At(image, supremum, a.Apply(n))))
			arg.Show(
				"so sup − ε < a(N) ≤ a(n) ≤ sup: the term lies within ε of sup",
				ByArith(exceeds, risen, capped, pos))
		}),
})}

// DecreasingBoundedConvergesToInf — a falling sequence bounded below
// converges, and its limit is the infimum of its range.
//
// The range image(a, 𝕌) holds every term, so it is nonempty, and B
// floors it; hence inf of the range is its infimum. Given ε > 0 the
// infimum is approached from inside: some member of the range — a
// term a(N) — lies below inf + ε. Past N every term is at most a(N),
// because the sequence falls, and at least the infimum, because it
// floors the range; so the tail past N lies in ⟦inf, inf + ε⟭, within
// ε of inf.
var DecreasingBoundedConvergesToInf = decreasingBoundedConvergesToInfThm{family.Add(registry.ProofEntry{
	Name: "DecreasingBoundedConvergesToInf",
	Key:  "prop_770b8d31d2a0c845",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. a(n + 1) ≤ a(n)",
			"∀n:num. B ≤ a(n)",
		},
		Conclusion: "a ⟶ inf(image(a, 𝕌))",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], _ Fact) {
			arg.Do(Unfold(RealConvergesToDef))
			step := arg.Hyp("∀n:num. a(n + 1) ≤ a(n)")
			bounded := arg.Hyp("∀n:num. B ≤ a(n)")
			naturals := arg.TermAs[Set[Nat]]("𝕌")
			image := arg.TermAs[Set[Real]]("image(a, 𝕌)")
			infimum := arg.TermAs[Real]("inf(image(a, 𝕌))")
			zero := arg.Ctx().Nat(0)

			nonempty := arg.Have(
				"the range is nonempty — a(0) is in it",
				"image(a, 𝕌) ≠ ∅",
				By(
					Normalized,
					set_image.FunInImage.At(a, naturals, zero),
					set_basic.InUniv.At(zero),
					set_basic.MemberNotEmpty.At(image)))
			boundedBelow := arg.Have(
				"and B floors it: a bound on the range is a bound on every term, read back along a",
				"∀x:real. x ∈ image(a, 𝕌) ⇒ B ≤ x",
				By(
					bounded,
					set_image.ForallInImage.At(a, naturals, arg.TermAs[Set[Real]]("λx:real. B ≤ x")),
					set_basic.InUniv))
			hasInf := arg.Have(
				"so inf of the range is its infimum",
				"real_has_inf(image(a, 𝕌), inf(image(a, 𝕌)))",
				By(nonempty, boundedBelow, real_sup_inf.HasInfIsInf.At(image, infimum)))

			arg.FixAs[Real]()
			pos := arg.Assume()
			aboveInf := arg.TermAs[Real]("inf(image(a, 𝕌)) + ε")
			strictlyAbove := arg.Have(
				"the strict ordering the approximation law asks for: inf + ε lies above the infimum",
				"inf(image(a, 𝕌)) < inf(image(a, 𝕌)) + ε",
				ByArith(pos))
			N, below := arg.ObtainAs[Nat](
				"the infimum is approached from inside: a member of the range "+
					"lies below inf + ε, and a member of the range is a term a(N)",
				"∃N:num. a(N) < inf(image(a, 𝕌)) + ε",
				By(
					hasInf,
					strictlyAbove,
					real_sup_inf.HasInfApproach.At(image, infimum, aboveInf),
					set_image.ExistsInImage.At(
						a, naturals, arg.TermAs[Set[Real]]("λy:real. y < inf(image(a, 𝕌)) + ε"))))

			arg.Take(N)
			n := arg.FixAs[Nat]()
			past := arg.Assume()
			fallen := arg.Have(
				"past N the sequence has fallen at least to a(N)",
				"a(n) ≤ a(N)",
				By(step, past, DecreasingLessEq.At(a, N, n)))
			floored := arg.Have(
				"and the infimum floors every term — a(n) is in the range",
				"inf(image(a, 𝕌)) ≤ a(n)",
				By(
					hasInf,
					set_image.FunInImage.At(a, naturals, n),
					set_basic.InUniv.At(n),
					real_sup_inf.HasInfLowerBound.At(image, infimum, a.Apply(n))))
			arg.Show(
				"so inf ≤ a(n) ≤ a(N) < inf + ε: the term lies within ε of inf",
				ByArith(below, fallen, floored, pos))
		}),
})}

// MonotoneBoundedConvergent — a monotone bounded sequence converges:
// the classical sentence, the corollary of the two named-limit
// theorems.
//
// A bound B on the size of every term bounds the terms from both
// sides, at B and at -B. So a rising sequence is rising and bounded
// above, and its limit is the supremum of its range; a falling one is
// falling and bounded below, and its limit is the infimum. Either way
// the limit exists.
var MonotoneBoundedConvergent = monotoneBoundedConvergentThm{family.Add(registry.ProofEntry{
	Name: "MonotoneBoundedConvergent",
	Key:  "prop_f250c27d7367c8f4",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"(∀n:num. a(n) ≤ a(n + 1)) ∨ (∀n:num. a(n + 1) ≤ a(n))",
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "∃l:real. a ⟶ l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], monotone, bounded Fact) {
			arg.Do(monotone.SplitDisj(
				LeftHolds(
					"rising: the bound caps the terms, and the limit is the supremum of the range",
					Given(func(b *Argument, rising Fact) {
						capped := b.Have(
							"every term is at most B, the upper side of the two-sided reading of |a(n)| ≤ B",
							"∀n:num. a(n) ≤ B",
							b.ForEach(func(n *Expr[Nat]) Action {
								return By(bounded.At(n), real_sgn_abs.AbsBounds.At(a.Apply(n), B))
							}))
						b.Take(b.TermAs[Real]("sup(image(a, 𝕌))"))
						b.Show(
							"a rising sequence bounded above converges to the supremum of its range",
							By(rising, capped, IncreasingBoundedConvergesToSup.At(a, B)))
					})),
				RightHolds(
					"falling: the bound floors the terms, and the limit is the infimum of the range",
					Given(func(b *Argument, falling Fact) {
						floored := b.Have(
							"every term is at least -B, the lower side of the two-sided reading of |a(n)| ≤ B",
							"∀n:num. -B ≤ a(n)",
							b.ForEach(func(n *Expr[Nat]) Action {
								return By(bounded.At(n), real_sgn_abs.AbsBounds.At(a.Apply(n), B))
							}))
						b.Take(b.TermAs[Real]("inf(image(a, 𝕌))"))
						b.Show(
							"a falling sequence bounded below converges to the infimum of its range",
							By(falling, floored, DecreasingBoundedConvergesToInf.At(a, b.TermAs[Real]("-B"))))
					})),
			))
		}),
})}

// PowerTendsToZero — the powers of a number below 1 in size tend to 0.
//
// First for |x|. Its powers never go below 0 and fall, each |x| times
// the one before, so they converge, to some L. The powers from the
// second on then tend to L twice over: as the shifted sequence, and as
// |x| times the powers, which tend to |x|·L. A sequence has one limit,
// so L = |x|·L, that is (1 − |x|)·L = 0, and 1 − |x| is not 0: L = 0.
// Then for x: each xⁿ lies exactly |x|ⁿ from 0, a distance that
// vanishes, so the squeeze on the distance puts xⁿ at the limit of the
// constant sequence 0.
var PowerTendsToZero = powerTendsToZeroThm{family.Add(registry.ProofEntry{
	Name: "PowerTendsToZero",
	Key:  "prop_d3de5afc7b5dc643",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"|x| < &1",
		},
		Conclusion: "(λn:num. real_pow(x, n)) ⟶ &0",
	},
		func(arg *Argument, x *Expr[Real], small Fact) {
			powers := arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(|x|, n)")
			zero := arg.TermAs[Real]("&0")

			toZero := arg.Have(
				"the powers of |x| tend to 0: they fall to a limit L, and L = |x|·L forces L = 0",
				"(λn:num. real_pow(|x|, n)) ⟶ &0",
				Derive(func(b *Argument) {
					size := b.TermAs[Real]("|x|")
					shifted := b.TermAs[Fun[Nat, Real]]("λn:num. real_pow(|x|, n + 1)")

					floor := b.Have(
						"the powers of |x| are never negative, as |x| is not",
						"∀n:num. &0 ≤ real_pow(|x|, n)",
						b.ForEach(func(n *Expr[Nat]) Action {
							return By(real_sgn_abs.AbsNonneg.At(x), real_pow.PowNonneg.At(size, n))
						}))
					fall := b.Have(
						"and they fall: the next is |x| times this one, and |x| < 1",
						"∀n:num. real_pow(|x|, n + 1) ≤ real_pow(|x|, n)",
						Simp(Fwd(real_pow.PowAddOne)),
						b.ForEach(func(n *Expr[Nat]) Action { return ByArith(floor.At(n), small) }))
					L, converges := b.ObtainAs[Real](
						"falling and bounded below by 0, they converge, to some L",
						"∃L:real. (λn:num. real_pow(|x|, n)) ⟶ L",
						By(Normalized, fall, floor, DecreasingBoundedConvergesToInf.At(powers, zero)))

					asShift := b.Have(
						"the powers from the second on are the shifted powers, so tend to L",
						"(λn:num. real_pow(|x|, n + 1)) ⟶ L",
						By(converges, LimitShift.At(powers, L)))
					asMultiple := b.Have(
						"and, |x|ⁿ⁺¹ being |x|·|x|ⁿ, they are |x| times the powers, so tend to |x|·L",
						"(λn:num. real_pow(|x|, n + 1)) ⟶ |x| * L",
						Simp(Fwd(real_pow.PowAddOne)),
						By(converges, LimitScale.At(powers, L, size)))
					fixed := b.Have(
						"a sequence has one limit, so L = |x|·L",
						"L = |x| * L",
						By(asShift, asMultiple, LimitUnique.At(shifted, L, b.TermAs[Real]("|x| * L"))))
					product := b.Have(
						"that is, (1 − |x|)·L = 0",
						"(&1 - |x|) * L = &0",
						ByArith(fixed))
					vanishes := b.Have(
						"a product vanishes only with a factor, and 1 − |x| > 0: L = 0",
						"L = &0",
						ByArith(product, small, real_ring.MulEqZero.At(b.TermAs[Real]("&1 - |x|"), L)))
					b.Show(
						"so the limit of the powers of |x| is 0",
						By(Normalized, converges, vanishes))
				}))

			distance := arg.Have(
				"xⁿ lies exactly |x|ⁿ from 0: |xⁿ| = |x|ⁿ",
				"∀n:num. |real_pow(x, n) - &0| ≤ real_pow(|x|, n)",
				Simp(Fwd(real_ring.SubRightZero), Fwd(real_pow.AbsPow)),
				By(real_order_ring.LessEqRefl))
			arg.Show(
				"so xⁿ, within a vanishing distance of the constant sequence 0, tends to 0 as well",
				By(
					toZero,
					distance,
					LimitConst.At(zero),
					LimitSqueezeDistance.At(arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(x, n)"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. &0"), powers, zero)))
		}),
})}
