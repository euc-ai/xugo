// upper_lower_limits.go — the upper and lower limits of a bounded
// sequence (README, "A bounded sequence has a cluster point, …" and "A
// bounded sequence converges exactly when its upper and lower limits
// agree").
//
// Throughout, T(N) is the range of the N-th tail, image(a, {n | N ≤ n}),
// and s(N) and i(N) are its supremum and infimum. Every tail of a
// bounded sequence has both; the tail suprema fall and converge, to the
// upper limit real_limsup(a), and the tail infima rise and converge, to the
// lower limit real_liminf(a). The lower limit is at most the upper, and the
// sequence converges exactly when the two agree — to their common value
// (whose forward direction goes through the cluster points and the
// Cauchy criterion).

package real_sequences

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// TailHasSup — every tail of a bounded sequence has its supremum.
//
// The range of the N-th tail, image(a, {n | N ≤ n}), holds the tail's
// first term a(N), so it is nonempty; and B caps every term, so it caps
// the range. A nonempty set of reals bounded above has its supremum.
var TailHasSup = tailHasSupThm{family.Add(registry.ProofEntry{
	Name: "TailHasSup",
	Key:  "prop_ee2fb014fbb3cbb5",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "real_has_sup(image(a, {n:num | N ≤ n}), sup(image(a, {n:num | N ≤ n})))",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], bounded Fact) {
			capped := arg.Have(
				"every term is at most B, the upper side of the two-sided reading of |a(n)| ≤ B",
				"∀n:num. a(n) ≤ B",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return By(bounded.At(n), real_sgn_abs.AbsBounds.At(a.Apply(n), B))
				}))

			N := arg.FixAs[Nat]("N")
			tail := arg.TermAs[Set[Nat]]("{n:num | N ≤ n}")
			tailRange := arg.TermAs[Set[Real]]("image(a, {n:num | N ≤ n})")
			boundedAbove := arg.Have(
				"so the tail's range is bounded above",
				"∃b:real. ∀x:real. x ∈ image(a, {n:num | N ≤ n}) ⇒ x ≤ b",
				Derive(func(g *Argument) {
					g.Take(B)
					g.Show(
						"B caps it: a bound on the range is a bound on every term of the tail, read back along a",
						By(capped, set_image.ForallInImage.At(a, tail, g.TermAs[Set[Real]]("λx:real. x ≤ B"))))
				}))
			first := arg.Have(
				"N is the tail's first index",
				"N ∈ {n:num | N ≤ n}",
				BySets(nat_order.LessEqRefl.At(N)))
			nonempty := arg.Have(
				"so the tail's range is nonempty — a(N) is in it",
				"image(a, {n:num | N ≤ n}) ≠ ∅",
				By(first, set_image.FunInImage.At(a, tail, N), set_basic.MemberNotEmpty.At(tailRange)))
			arg.Show(
				"a nonempty set of reals bounded above has its supremum",
				Simp(Fwd(real_sup_inf.HasSupIsSup)),
				By(nonempty, boundedAbove))
		}),
})}

// TailHasInf — every tail of a bounded sequence has its infimum.
//
// The range of the N-th tail, image(a, {n | N ≤ n}), holds the tail's
// first term a(N), so it is nonempty; and −B floors every term, so it
// floors the range. A nonempty set of reals bounded below has its
// infimum.
var TailHasInf = tailHasInfThm{family.Add(registry.ProofEntry{
	Name: "TailHasInf",
	Key:  "prop_75a78d4b04feca0b",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "real_has_inf(image(a, {n:num | N ≤ n}), inf(image(a, {n:num | N ≤ n})))",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], bounded Fact) {
			floored := arg.Have(
				"every term is at least −B, the lower side of the two-sided reading of |a(n)| ≤ B",
				"∀n:num. -B ≤ a(n)",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return By(bounded.At(n), real_sgn_abs.AbsBounds.At(a.Apply(n), B))
				}))

			N := arg.FixAs[Nat]("N")
			tail := arg.TermAs[Set[Nat]]("{n:num | N ≤ n}")
			tailRange := arg.TermAs[Set[Real]]("image(a, {n:num | N ≤ n})")
			boundedBelow := arg.Have(
				"so the tail's range is bounded below",
				"∃b:real. ∀x:real. x ∈ image(a, {n:num | N ≤ n}) ⇒ b ≤ x",
				Derive(func(g *Argument) {
					g.Take(g.TermAs[Real]("-B"))
					g.Show(
						"−B floors it: a bound on the range is a bound on every term of the tail, read back along a",
						By(floored, set_image.ForallInImage.At(a, tail, g.TermAs[Set[Real]]("λx:real. -B ≤ x"))))
				}))
			first := arg.Have(
				"N is the tail's first index",
				"N ∈ {n:num | N ≤ n}",
				BySets(nat_order.LessEqRefl.At(N)))
			nonempty := arg.Have(
				"so the tail's range is nonempty — a(N) is in it",
				"image(a, {n:num | N ≤ n}) ≠ ∅",
				By(first, set_image.FunInImage.At(a, tail, N), set_basic.MemberNotEmpty.At(tailRange)))
			arg.Show(
				"a nonempty set of reals bounded below has its infimum",
				Simp(Fwd(real_sup_inf.HasInfIsInf)),
				By(nonempty, boundedBelow))
		}),
})}

// TailSupConvergesToLimsup — the suprema of the tails of a bounded
// sequence fall and stay above −B, so they converge, and their limit is
// the upper limit: real_limsup(a), the infimum of them all.
//
// Write T(N) for the N-th tail's range image(a, {n | N ≤ n}) and s(N)
// for its supremum, which every T(N) has (TailHasSup). The tails nest,
// so T(N + 1) is a part of T(N), nonempty since it has a supremum, and
// s(N) caps T(N): so s(N + 1) ≤ s(N), and s falls. And
// −B ≤ a(N) ≤ s(N), a(N) being a member of T(N): s stays above −B. A
// falling sequence bounded below converges to the infimum of its range.
var TailSupConvergesToLimsup = tailSupConvergesToLimsupThm{family.Add(registry.ProofEntry{
	Name: "TailSupConvergesToLimsup",
	Key:  "prop_37411b4f9f162214",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "(λN:num. sup(image(a, {n:num | N ≤ n}))) ⟶ real_limsup(a)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], bounded Fact) {
			// The goal's real_limsup(a) read as what it abbreviates, the infimum of
			// the tail suprema — the limit the monotone theorem names.
			arg.Do(Unfold(RealLimsupDef))
			hasSup := arg.Have(
				"every tail's range T(N) has its supremum s(N)",
				"∀N:num. real_has_sup(image(a, {n:num | N ≤ n}), sup(image(a, {n:num | N ≤ n})))",
				By(bounded, At(TailHasSup, a, B)))

			falling := arg.Have(
				"the tail suprema fall step by step",
				"∀N:num. sup(image(a, {n:num | N + 1 ≤ n})) ≤ sup(image(a, {n:num | N ≤ n}))",
				Derive(func(g *Argument) {
					N := g.FixAs[Nat]("N")
					next := g.TermAs[Nat]("N + 1")
					later := g.TermAs[Set[Nat]]("{n:num | N + 1 ≤ n}")
					earlier := g.TermAs[Set[Nat]]("{n:num | N ≤ n}")
					laterRange := g.TermAs[Set[Real]]("image(a, {n:num | N + 1 ≤ n})")
					earlierRange := g.TermAs[Set[Real]]("image(a, {n:num | N ≤ n})")
					laterSup := g.TermAs[Real]("sup(image(a, {n:num | N + 1 ≤ n}))")
					earlierSup := g.TermAs[Real]("sup(image(a, {n:num | N ≤ n}))")
					pastNext := g.Have(
						"an index past N + 1 is past N",
						"∀n:num. N + 1 ≤ n ⇒ N ≤ n",
						Derive(func(c *Argument) {
							c.FixAs[Nat]()
							past := c.Assume()
							c.Show(
								"N ≤ N + 1 ≤ n",
								ByArith(past))
						}))
					nested := g.Have(
						"so the tails nest",
						"{n:num | N + 1 ≤ n} ⊆ {n:num | N ≤ n}",
						BySets(pastNext))
					inside := g.Have(
						"and T(N + 1) is a part of T(N)",
						"image(a, {n:num | N + 1 ≤ n}) ⊆ image(a, {n:num | N ≤ n})",
						By(nested, set_image.ImageSubset.At(a, later, earlier)))
					capped := g.Have(
						"and s(N) caps T(N): a supremum is an upper bound",
						"∀x:real. x ∈ image(a, {n:num | N ≤ n}) ⇒ x ≤ sup(image(a, {n:num | N ≤ n}))",
						g.ForEach(func(x *Expr[Real]) Action {
							return By(hasSup.At(N), real_sup_inf.HasSupUpperBound.At(earlierRange, earlierSup, x))
						}))
					g.Show(
						"T(N + 1), nonempty since it has a supremum, is a part of a "+
							"set s(N) caps, so it has no larger supremum: s(N + 1) ≤ s(N)",
						By(
							inside,
							hasSup.At(next),
							real_sup_inf.HasSupNonempty.At(laterRange, laterSup),
							capped,
							real_sup_inf.SupMonoSubset.At(laterRange, earlierRange, earlierSup)))
				}))
			negB := arg.TermAs[Real]("-B")
			boundedBelow := arg.Have(
				"and never fall below −B",
				"∀N:num. -B ≤ sup(image(a, {n:num | N ≤ n}))",
				Derive(func(g *Argument) {
					N := g.FixAs[Nat]("N")
					aN := a.Apply(N)
					tail := g.TermAs[Set[Nat]]("{n:num | N ≤ n}")
					tailRange := g.TermAs[Set[Real]]("image(a, {n:num | N ≤ n})")
					tailSup := g.TermAs[Real]("sup(image(a, {n:num | N ≤ n}))")
					firstIndex := g.Have(
						"N is the tail's first index",
						"N ∈ {n:num | N ≤ n}",
						BySets(nat_order.LessEqRefl.At(N)))
					g.Show(
						"−B ≤ a(N) ≤ s(N)",
						real_order_ring.OrderCalc(g.Ctx()).Calc(negB,
							LeLeg(
								aN,
								"the lower side of the two-sided reading of |a(N)| ≤ B",
								By(bounded.At(N), real_sgn_abs.AbsBounds.At(aN, B))),
							LeLeg(
								tailSup,
								"and s(N), an upper bound of T(N), is at least its member a(N)",
								By(
									hasSup.At(N),
									firstIndex,
									set_image.FunInImage.At(a, tail, N),
									real_sup_inf.HasSupUpperBound.At(tailRange, tailSup, aN)))))
				}))

			suprema := arg.TermAs[Fun[Nat, Real]]("λN:num. sup(image(a, {n:num | N ≤ n}))")
			arg.Show(
				"a falling sequence bounded below converges to the infimum of its range",
				By(falling, boundedBelow, DecreasingBoundedConvergesToInf.At(suprema, negB)))
		}),
})}

// TailInfConvergesToLiminf — the infima of the tails of a bounded
// sequence rise and stay below B, so they converge, and their limit is
// the lower limit: real_liminf(a), the supremum of them all.
//
// Write T(N) for the N-th tail's range image(a, {n | N ≤ n}) and i(N)
// for its infimum, which every T(N) has (TailHasInf). The tails nest,
// so T(N + 1) is a part of T(N), nonempty since it has an infimum, and
// i(N) floors T(N): so i(N) ≤ i(N + 1), and i rises. And
// i(N) ≤ a(N) ≤ B, a(N) being a member of T(N): i stays below B. A
// rising sequence bounded above converges to the supremum of its range.
var TailInfConvergesToLiminf = tailInfConvergesToLiminfThm{family.Add(registry.ProofEntry{
	Name: "TailInfConvergesToLiminf",
	Key:  "prop_7669cb212c75595d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "(λN:num. inf(image(a, {n:num | N ≤ n}))) ⟶ real_liminf(a)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], bounded Fact) {
			// The goal's real_liminf(a) read as what it abbreviates, the supremum
			// of the tail infima — the limit the monotone theorem names.
			arg.Do(Unfold(RealLiminfDef))
			hasInf := arg.Have(
				"every tail's range T(N) has its infimum i(N)",
				"∀N:num. real_has_inf(image(a, {n:num | N ≤ n}), inf(image(a, {n:num | N ≤ n})))",
				By(bounded, At(TailHasInf, a, B)))

			rising := arg.Have(
				"the tail infima rise step by step",
				"∀N:num. inf(image(a, {n:num | N ≤ n})) ≤ inf(image(a, {n:num | N + 1 ≤ n}))",
				Derive(func(g *Argument) {
					N := g.FixAs[Nat]("N")
					next := g.TermAs[Nat]("N + 1")
					later := g.TermAs[Set[Nat]]("{n:num | N + 1 ≤ n}")
					earlier := g.TermAs[Set[Nat]]("{n:num | N ≤ n}")
					laterRange := g.TermAs[Set[Real]]("image(a, {n:num | N + 1 ≤ n})")
					earlierRange := g.TermAs[Set[Real]]("image(a, {n:num | N ≤ n})")
					laterInf := g.TermAs[Real]("inf(image(a, {n:num | N + 1 ≤ n}))")
					earlierInf := g.TermAs[Real]("inf(image(a, {n:num | N ≤ n}))")
					pastNext := g.Have(
						"an index past N + 1 is past N",
						"∀n:num. N + 1 ≤ n ⇒ N ≤ n",
						Derive(func(c *Argument) {
							c.FixAs[Nat]()
							past := c.Assume()
							c.Show(
								"N ≤ N + 1 ≤ n",
								ByArith(past))
						}))
					nested := g.Have(
						"so the tails nest",
						"{n:num | N + 1 ≤ n} ⊆ {n:num | N ≤ n}",
						BySets(pastNext))
					inside := g.Have(
						"and T(N + 1) is a part of T(N)",
						"image(a, {n:num | N + 1 ≤ n}) ⊆ image(a, {n:num | N ≤ n})",
						By(nested, set_image.ImageSubset.At(a, later, earlier)))
					floored := g.Have(
						"and i(N) floors T(N): an infimum is a lower bound",
						"∀x:real. x ∈ image(a, {n:num | N ≤ n}) ⇒ inf(image(a, {n:num | N ≤ n})) ≤ x",
						g.ForEach(func(x *Expr[Real]) Action {
							return By(hasInf.At(N), real_sup_inf.HasInfLowerBound.At(earlierRange, earlierInf, x))
						}))
					g.Show(
						"T(N + 1), nonempty since it has an infimum, is a part of a "+
							"set i(N) floors, so it has no smaller infimum: i(N) ≤ i(N + 1)",
						By(
							inside,
							hasInf.At(next),
							real_sup_inf.HasInfNonempty.At(laterRange, laterInf),
							floored,
							real_sup_inf.InfAntitoneSubset.At(laterRange, earlierRange, earlierInf)))
				}))
			boundedAbove := arg.Have(
				"and never rise above B",
				"∀N:num. inf(image(a, {n:num | N ≤ n})) ≤ B",
				Derive(func(g *Argument) {
					N := g.FixAs[Nat]("N")
					aN := a.Apply(N)
					tail := g.TermAs[Set[Nat]]("{n:num | N ≤ n}")
					tailRange := g.TermAs[Set[Real]]("image(a, {n:num | N ≤ n})")
					tailInf := g.TermAs[Real]("inf(image(a, {n:num | N ≤ n}))")
					firstIndex := g.Have(
						"N is the tail's first index",
						"N ∈ {n:num | N ≤ n}",
						BySets(nat_order.LessEqRefl.At(N)))
					g.Show(
						"i(N) ≤ a(N) ≤ B",
						real_order_ring.OrderCalc(g.Ctx()).Calc(tailInf,
							LeLeg(
								aN,
								"i(N), a lower bound of T(N), is at most its member a(N)",
								By(
									hasInf.At(N),
									firstIndex,
									set_image.FunInImage.At(a, tail, N),
									real_sup_inf.HasInfLowerBound.At(tailRange, tailInf, aN))),
							LeLeg(
								B,
								"the upper side of the two-sided reading of |a(N)| ≤ B",
								By(bounded.At(N), real_sgn_abs.AbsBounds.At(aN, B)))))
				}))

			infima := arg.TermAs[Fun[Nat, Real]]("λN:num. inf(image(a, {n:num | N ≤ n}))")
			arg.Show(
				"a rising sequence bounded above converges to the supremum of its range",
				By(rising, boundedAbove, IncreasingBoundedConvergesToSup.At(infima, B)))
		}),
})}

// LiminfLessEqLimsup — the lower limit of a bounded sequence is at most
// its upper limit.
//
// Write T(N) for the N-th tail's range image(a, {n | N ≤ n}), i(N) for
// its infimum and s(N) for its supremum. The tail's first term a(N) is a
// member of T(N), so i(N) ≤ a(N) ≤ s(N). The tail infima converge to
// real_liminf(a) and the tail suprema to real_limsup(a), and limits keep order.
var LiminfLessEqLimsup = liminfLessEqLimsupThm{family.Add(registry.ProofEntry{
	Name: "LiminfLessEqLimsup",
	Key:  "prop_7f19f0b875199627",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "real_liminf(a) ≤ real_limsup(a)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], bounded Fact) {
			below := arg.Have(
				"from index 0 on, the tail infimum lies below the tail supremum",
				"∀N:num. 0 ≤ N ⇒ inf(image(a, {n:num | N ≤ n})) ≤ sup(image(a, {n:num | N ≤ n}))",
				Derive(func(g *Argument) {
					N := g.FixAs[Nat]("N")
					g.Assume()
					aN := a.Apply(N)
					tail := g.TermAs[Set[Nat]]("{n:num | N ≤ n}")
					tailRange := g.TermAs[Set[Real]]("image(a, {n:num | N ≤ n})")
					tailInf := g.TermAs[Real]("inf(image(a, {n:num | N ≤ n}))")
					tailSup := g.TermAs[Real]("sup(image(a, {n:num | N ≤ n}))")
					firstIndex := g.Have(
						"N is the tail's first index",
						"N ∈ {n:num | N ≤ n}",
						BySets(nat_order.LessEqRefl.At(N)))
					first := g.Have(
						"so a(N) is a member of T(N)",
						"a(N) ∈ image(a, {n:num | N ≤ n})",
						By(firstIndex, set_image.FunInImage.At(a, tail, N)))
					g.Show(
						"i(N) ≤ a(N) ≤ s(N)",
						real_order_ring.OrderCalc(g.Ctx()).Calc(tailInf,
							LeLeg(
								aN,
								"i(N), a lower bound of T(N), is at most its member a(N)",
								By(
									bounded,
									TailHasInf.At(a, B, N),
									first,
									real_sup_inf.HasInfLowerBound.At(tailRange, tailInf, aN))),
							LeLeg(
								tailSup,
								"and s(N), an upper bound of T(N), is at least it",
								By(
									bounded,
									TailHasSup.At(a, B, N),
									first,
									real_sup_inf.HasSupUpperBound.At(tailRange, tailSup, aN)))))
				}))

			infima := arg.TermAs[Fun[Nat, Real]]("λN:num. inf(image(a, {n:num | N ≤ n}))")
			suprema := arg.TermAs[Fun[Nat, Real]]("λN:num. sup(image(a, {n:num | N ≤ n}))")
			lower := arg.Have(
				"the tail infima converge to the lower limit",
				"(λN:num. inf(image(a, {n:num | N ≤ n}))) ⟶ real_liminf(a)",
				By(bounded, TailInfConvergesToLiminf.At(a, B)))
			upper := arg.Have(
				"and the tail suprema to the upper limit",
				"(λN:num. sup(image(a, {n:num | N ≤ n}))) ⟶ real_limsup(a)",
				By(bounded, TailSupConvergesToLimsup.At(a, B)))
			lowerLimit := arg.TermAs[Real]("real_liminf(a)")
			upperLimit := arg.TermAs[Real]("real_limsup(a)")
			arg.Show(
				"limits keep order, and from index 0 on the infima lie below the suprema",
				By(
					below,
					lower,
					upper,
					LimitLessEq.At(infima, suprema, lowerLimit, upperLimit, arg.TermAs[Nat]("0"))))
		}),
})}

// ConvergesToIffLiminfLimsup — a bounded sequence converges to l exactly when
// both its upper and lower limits are l.
//
// Forward: a convergent sequence is Cauchy, and the upper and the lower
// limit of a bounded sequence are cluster points of it; a Cauchy
// sequence converges to each of its cluster points, so the sequence
// converges to both limits, and a limit is one number. Backward: write
// T(N) for the N-th tail's range, i(N) for its infimum and s(N) for its
// supremum. Every term is squeezed between its tail's infimum and
// supremum, i(N) ≤ a(N) ≤ s(N), a(N) being a member of T(N), and both
// tend to l — the tail infima to real_liminf(a) = l, the tail suprema to
// real_limsup(a) = l: the squeeze.
var ConvergesToIffLiminfLimsup = convergesToIffLiminfLimsupThm{family.Add(registry.ProofEntry{
	Name: "ConvergesToIffLiminfLimsup",
	Key:  "prop_3e9718b650211559",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B l:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "a ⟶ l ⇔ real_liminf(a) = l ∧ real_limsup(a) = l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B, l *Expr[Real], bounded Fact) {
			arg.Iff()
			arg.Forward(
				"a convergent sequence converges to both its limits, and a limit is one number",
				func(b *Argument, toL Fact) {
					upperLimit := b.TermAs[Real]("real_limsup(a)")
					lowerLimit := b.TermAs[Real]("real_liminf(a)")
					isCauchy := b.Have(
						"a convergent sequence is Cauchy",
						"real_cauchy(a)",
						By(toL, ConvergentImpCauchy.At(a, l)))
					toUpper := b.Have(
						"the upper limit is a cluster point of it, and a Cauchy sequence converges to each of those",
						"a ⟶ real_limsup(a)",
						By(isCauchy, bounded, BoundedClusterPoint.At(a, B), CauchyClusterPointConverges.At(a, upperLimit)))
					toLower := b.Have(
						"so is the lower limit, and the sequence converges to that too",
						"a ⟶ real_liminf(a)",
						By(isCauchy, bounded, LiminfClusterPoint.At(a, B), CauchyClusterPointConverges.At(a, lowerLimit)))
					b.Show(
						"a limit is one number: real_liminf(a) = l and real_limsup(a) = l",
						By(toL, toLower, toUpper, LimitUnique.At(a, lowerLimit, l), LimitUnique.At(a, upperLimit, l)))
				})
			arg.Backward(
				"squeezed between the tail infima and the tail suprema, both tending to l, the terms tend to l",
				func(b *Argument, limits Fact) {
					pinned := b.Have(
						"from index 0 on, every term lies between the infimum "+
							"and the supremum of its own tail: i(N) ≤ a(N) ≤ s(N)",
						"∀N:num. 0 ≤ N ⇒ inf(image(a, {n:num | N ≤ n})) ≤ a(N) ∧ a(N) ≤ sup(image(a, {n:num | N ≤ n}))",
						Derive(func(g *Argument) {
							N := g.FixAs[Nat]("N")
							g.Assume()
							aN := a.Apply(N)
							tail := g.TermAs[Set[Nat]]("{n:num | N ≤ n}")
							tailRange := g.TermAs[Set[Real]]("image(a, {n:num | N ≤ n})")
							tailInf := g.TermAs[Real]("inf(image(a, {n:num | N ≤ n}))")
							tailSup := g.TermAs[Real]("sup(image(a, {n:num | N ≤ n}))")
							firstIndex := g.Have(
								"N is the tail's first index",
								"N ∈ {n:num | N ≤ n}",
								BySets(nat_order.LessEqRefl.At(N)))
							first := g.Have(
								"so a(N) is a member of T(N)",
								"a(N) ∈ image(a, {n:num | N ≤ n})",
								By(firstIndex, set_image.FunInImage.At(a, tail, N)))
							below := g.Have(
								"i(N), a lower bound of T(N), is at most its member a(N)",
								"inf(image(a, {n:num | N ≤ n})) ≤ a(N)",
								By(
									bounded,
									TailHasInf.At(a, B, N),
									first,
									real_sup_inf.HasInfLowerBound.At(tailRange, tailInf, aN)))
							above := g.Have(
								"and s(N), an upper bound of T(N), is at least it",
								"a(N) ≤ sup(image(a, {n:num | N ≤ n}))",
								By(
									bounded,
									TailHasSup.At(a, B, N),
									first,
									real_sup_inf.HasSupUpperBound.At(tailRange, tailSup, aN)))
							g.Show(
								"i(N) ≤ a(N) ≤ s(N)",
								By(below, above))
						}))

					infima := b.TermAs[Fun[Nat, Real]]("λN:num. inf(image(a, {n:num | N ≤ n}))")
					suprema := b.TermAs[Fun[Nat, Real]]("λN:num. sup(image(a, {n:num | N ≤ n}))")
					lower := b.Have(
						"the tail infima converge to the lower limit, which is l",
						"(λN:num. inf(image(a, {n:num | N ≤ n}))) ⟶ l",
						By(bounded, TailInfConvergesToLiminf.At(a, B), limits))
					upper := b.Have(
						"and the tail suprema to the upper limit, which is l too",
						"(λN:num. sup(image(a, {n:num | N ≤ n}))) ⟶ l",
						By(bounded, TailSupConvergesToLimsup.At(a, B), limits))
					b.Show(
						"the squeeze, from index 0 on: the terms tend to l",
						By(pinned, lower, upper, LimitSqueeze.At(infima, a, suprema, l, b.TermAs[Nat]("0"))))
				})
		}),
})}
