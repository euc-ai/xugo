// ambient.go — the ambient of a lattice pair as a localization of either
// chart, and what a finite-dimensional chart quotient does on the overlap:
// it localizes onto the quotient of the ambients, which is no bigger.

package lattice_pair

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The ambient
// ---------------------------------------------------------------------------

// AmbientContains — the ambient of a lattice pair is an R-submodule of V
// holding both charts.
var AmbientContains = ambientContainsThm{family.Add(registry.ProofEntry{
	Name: "AmbientContains",
	Key:  "prop_7118e442120700ce",
	Reading: "The ambient is the span of chart 0 alone: chart 1 lies in it only " +
		"through the lattice-pair condition that the two charts span one submodule.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waPair»(M)",
		},
		Conclusion: "submodule(R, V, lattice_pair_ambient(R, V, M)) ∧ " +
			"fst(M) ⊆ lattice_pair_ambient(R, V, M) ∧ " +
			"snd(M) ⊆ lattice_pair_ambient(R, V, M)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			V *Expr[ModuleOps[A, B]],
			M *Expr[Prod[Set[B], Set[B]]],
			pair Fact,
		) {
			parts := a.Conjuncts(
				a.Unfolded(pair, LatticePairDef),
				"V is an R-module",
				"fst(M) is an A₀-submodule of V",
				"snd(M) is an A₁-submodule of V",
				"the two charts span the same R-submodule")
			moduleOn, firstSubmodule, sameSpan := parts[0], parts[1], parts[3]
			first, second := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("snd(M)")
			secondInSpan := a.Have(
				"chart 1 lies in its own span, which is the span of chart 0",
				"snd(M) ⊆ module_span(R, V, fst(M))",
				sameSpan.Rw(),
				By(submodule.SubsetSpan.At(R, V, second)))
			a.Show(
				"the ambient is the span of chart 0: a submodule holding chart 0, and chart 1 with it",
				By(
					Normalized,
					LatticePairAmbientDef.At(R, V, M),
					submodule.SubmoduleSubset.Read(firstSubmodule),
					submodule.SpanSubmodule.Read(moduleOn).At(first),
					submodule.SubsetSpan.At(R, V, first),
					secondInSpan))
		}),
})}

// ChartSpanAway — the R-span of an A₀-submodule of V is its localization
// at t computed in V: the members of V that a power of t brings into it.
// At fst(M) it is the ambient of M; at snd(M), through the exchanged
// datum, the members a power of s brings into chart 1. The set S of those
// members is an R-submodule of V holding M₀: one power of t brings a sum
// into M₀ once powers bring both terms there, and since R = A₀[1/t] a
// scalar c has tᵏ · c ∈ A₀ for some k, so tᵏ⁺ᵐ · (c · u) = (tᵏ · c) · (tᵐ · u)
// lies in M₀ when tᵐ · u does. So S holds the span. Conversely v ∈ S is
// sⁿ · (tⁿ · v), s being the inverse of t, a multiple of a member of M₀.
var ChartSpanAway = chartSpanAwayThm{family.Add(registry.ProofEntry{
	Name: "ChartSpanAway",
	Key:  "prop_15cb8c96d250862e",
	Reading: "R = A₀[1/t] is load-bearing for ⊆: one power of t must clear the " +
		"denominators of all the scalars of a combination. The inclusion ⊇ rests on t · s = one.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀V:module_ops(A, B). ∀M₀:set(B).",
		Hypotheses: []string{
			"«waBiaffine»",
			"module_on(R, V)",
			"submodule(restrict_ring(R, A₀), V, M₀)",
		},
		Conclusion: "module_span(R, V, M₀) = " +
			"{v:B | v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀)}",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M0 *Expr[Set[B]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the charts and t, s form a biaffine datum",
				"V is a module over R",
				"M₀ is an A₀-submodule of V")
			isModule, chart := hypotheses[1], hypotheses[2]
			datum := a.Conjuncts(
				a.Unfolded(hypotheses[0], BiaffineDef),
				"R is a ring on its carrier",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring := datum[0]
			multiplicative := comm_ring.MulMonoidOn.Read(ring)
			tInR := a.Have(
				"t lies in R",
				"t ∈ R.carrier",
				By(a.Unfolded(comm_ring.SubringSubset.Read(datum[1]).AsFact(), set_basic.SubsetDef), datum[3]))
			sInR := a.Have(
				"s lies in R",
				"s ∈ R.carrier",
				By(a.Unfolded(comm_ring.SubringSubset.Read(datum[2]).AsFact(), set_basic.SubsetDef), datum[4]))
			chartRing := a.Have(
				"A₀ is a ring under R's operations",
				"comm_ring_on(restrict_ring(R, A₀))",
				By(datum[1], comm_ring.SubringRingOn.Read(ring).At(A0)))
			chartPowers := a.Have(
				"every power of t lies in A₀",
				"∀n:num. monoid_pow(R.mul, R.one, t, n) ∈ A₀",
				By(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(chartRing)), datum[3]))
			inverse := a.Have(
				"s · t = one, R being commutative",
				"s * t = R.one",
				ByArith(ring, tInR, sInR, datum[5]))
			sMember, tMember := proof.MemberOf(s, sInR), proof.MemberOf(t, tInR)
			inversePowers := a.Have(
				"so their powers are inverse too: sⁿ · tⁿ = one",
				"∀n:num. monoid_pow(R.mul, R.one, s, n) * monoid_pow(R.mul, R.one, t, n) = R.one",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(inverse, comm_monoid.PowInverseOn.Read(multiplicative).At(sMember, tMember, n))
				}))
			denominators := a.Have(
				"R is A₀[1/t]: a power of t brings each member of R into A₀",
				"∀c:A. c ∈ R.carrier ⇒ ∃k:num. monoid_pow(R.mul, R.one, t, k) * c ∈ A₀",
				a.ForEach(func(c *Expr[A]) Action {
					return By(datum[6], ring_away.RingAwayMember.At(R, A0, t, c))
				}))
			chartScaling := a.Have(
				"M₀ is closed under scaling by A₀",
				"∀c:A. ∀u:B. c ∈ A₀ ∧ u ∈ M₀ ⇒ c • u ∈ M₀",
				By(submodule.SubmoduleSmul.Read(chart)))
			chartVectors := a.Unfolded(submodule.SubmoduleSubset.Read(chart).AsFact(), set_basic.SubsetDef)

			S, localized := a.LetAs[Set[B]](
				"S", "{v:B | v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀)}")
			membership := a.Have(
				"v lies in S when it is a vector some power of t brings into M₀",
				"∀v:B. v ∈ S ⇔ v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀)",
				BySets(localized))

			chartInS := a.Have(
				"M₀ lies in S, at the exponent 0",
				"M₀ ⊆ S",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					inChart := b.Assume()
					atZero := b.Have(
						"t⁰ · v lies in M₀, t⁰ lying in A₀",
						"monoid_pow(R.mul, R.one, t, 0) • v ∈ M₀",
						By(chartScaling, chartPowers, inChart))
					b.Show(
						"so v lies in S",
						By(Normalized, membership.At(v), chartVectors, inChart, atZero))
				}))

			scaled := a.Have(
				"S is closed under scaling by R: tᵏ⁺ᵐ · (c · u) = (tᵏ "+
					"· c) · (tᵐ · u) with tᵏ · c in A₀ and tᵐ · u in M₀",
				"∀c:A. ∀u:B. c ∈ R.carrier ∧ u ∈ S ⇒ c • u ∈ S",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					u := b.FixAs[B]("u")
					scalar := b.Conjuncts(
						b.Assume(),
						"c lies in R",
						"u lies in S")
					_, cleared := b.ObtainAs[Nat](
						"a power tᵏ brings c into A₀",
						"∃k:num. monoid_pow(R.mul, R.one, t, k) * c ∈ A₀",
						By(denominators.At(c), scalar[0]))
					vector := b.Have(
						"u is a vector",
						"u ∈ V.carrier",
						By(membership.At(u), scalar[1]))
					_, uPower := b.ObtainAs[Nat](
						"a power tᵐ brings u into M₀",
						"∃m:num. monoid_pow(R.mul, R.one, t, m) • u ∈ M₀",
						By(membership.At(u), scalar[1]))
					powerSum := b.Have(
						"tᵏ⁺ᵐ = tᵏ · tᵐ",
						"monoid_pow(R.mul, R.one, t, k + m) = "+
							"monoid_pow(R.mul, R.one, t, k) * monoid_pow(R.mul, R.one, t, m)",
						By(comm_monoid.PowAddOn.Read(multiplicative), tInR))
					regroup := b.Have(
						"so tᵏ⁺ᵐ · c = (tᵏ · c) · tᵐ",
						"monoid_pow(R.mul, R.one, t, k + m) * c = "+
							"(monoid_pow(R.mul, R.one, t, k) * c) * monoid_pow(R.mul, R.one, t, m)",
						ByArith(ring, tInR, scalar[0], Scaled(c, powerSum)))
					power := b.TermAs[A]("monoid_pow(R.mul, R.one, t, k + m)")
					clearedScalar := b.TermAs[A]("monoid_pow(R.mul, R.one, t, k) * c")
					tm := b.TermAs[A]("monoid_pow(R.mul, R.one, t, m)")
					product := b.Have(
						"a product of scalars scales in turn, so tᵏ⁺ᵐ · (c · u) = (tᵏ · c) · (tᵐ · u)",
						"monoid_pow(R.mul, R.one, t, k + m) • (c • u) = "+
							"(monoid_pow(R.mul, R.one, t, k) * c) • (monoid_pow(R.mul, R.one, t, m) • u)",
						By(
							regroup,
							module.SmulMul.Read(isModule).AsFact().At(power, c, u),
							module.SmulMul.Read(isModule).AsFact().At(clearedScalar, tm, u),
							tInR,
							scalar[0],
							vector,
							comm_monoid.PowIn.Read(multiplicative),
							comm_ring.MulIn.Read(ring)))
					inChart := b.Have(
						"which lies in M₀, tᵏ · c lying in A₀ and tᵐ · u in M₀",
						"monoid_pow(R.mul, R.one, t, k + m) • (c • u) ∈ M₀",
						product.Rw(),
						By(chartScaling, cleared, uPower))
					b.Show(
						"so c · u lies in S, at the exponent k + m",
						By(
							Normalized,
							membership.At(b.TermAs[B]("c • u")),
							module.SmulIn.Read(isModule).AsFact().At(c, u),
							scalar[0],
							vector,
							inChart))
				}))

			sums := a.Have(
				"S is closed under the sum: tᵐ⁺ⁿ brings u + v into M₀ when tᵐ brings u and tⁿ brings v there",
				"∀u v:B. u ∈ S ∧ v ∈ S ⇒ u + v ∈ S",
				Derive(func(b *Argument) {
					u, v := b.FixAs[B]("u"), b.FixAs[B]("v")
					members := b.Conjuncts(
						b.Assume(),
						"u lies in S",
						"so does v")
					uVector := b.Have(
						"u is a vector",
						"u ∈ V.carrier",
						By(membership.At(u), members[0]))
					_, uPower := b.ObtainAs[Nat](
						"a power tᵐ brings u into M₀",
						"∃m:num. monoid_pow(R.mul, R.one, t, m) • u ∈ M₀",
						By(membership.At(u), members[0]))
					vVector := b.Have(
						"v is a vector",
						"v ∈ V.carrier",
						By(membership.At(v), members[1]))
					_, vPower := b.ObtainAs[Nat](
						"a power tⁿ brings v into M₀",
						"∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀",
						By(membership.At(v), members[1]))
					tm, tn :=
						b.TermAs[A]("monoid_pow(R.mul, R.one, t, m)"), b.TermAs[A]("monoid_pow(R.mul, R.one, t, n)")
					power := b.TermAs[A]("monoid_pow(R.mul, R.one, t, m + n)")
					powerSum := b.Have(
						"tᵐ⁺ⁿ = tᵐ · tⁿ",
						"monoid_pow(R.mul, R.one, t, m + n) = "+
							"monoid_pow(R.mul, R.one, t, m) * monoid_pow(R.mul, R.one, t, n)",
						By(comm_monoid.PowAddOn.Read(multiplicative), tInR))
					swapped := b.Have(
						"and tᵐ⁺ⁿ = tⁿ · tᵐ, R being commutative",
						"monoid_pow(R.mul, R.one, t, m + n) = "+
							"monoid_pow(R.mul, R.one, t, n) * monoid_pow(R.mul, R.one, t, m)",
						ByArith(ring, tInR, powerSum))
					uSplit := b.Have(
						"so tᵐ⁺ⁿ · u = tⁿ · (tᵐ · u)",
						"monoid_pow(R.mul, R.one, t, m + n) • u = "+
							"monoid_pow(R.mul, R.one, t, n) • (monoid_pow(R.mul, R.one, t, m) • u)",
						By(
							swapped,
							module.SmulMul.Read(isModule).AsFact().At(tn, tm, u),
							tInR,
							uVector,
							comm_monoid.PowIn.Read(multiplicative)))
					vSplit := b.Have(
						"and tᵐ⁺ⁿ · v = tᵐ · (tⁿ · v)",
						"monoid_pow(R.mul, R.one, t, m + n) • v = "+
							"monoid_pow(R.mul, R.one, t, m) • (monoid_pow(R.mul, R.one, t, n) • v)",
						By(
							powerSum,
							module.SmulMul.Read(isModule).AsFact().At(tm, tn, v),
							tInR,
							vVector,
							comm_monoid.PowIn.Read(multiplicative)))
					uIn := b.Have(
						"tᵐ⁺ⁿ · u lies in M₀, tⁿ lying in A₀",
						"monoid_pow(R.mul, R.one, t, m + n) • u ∈ M₀",
						uSplit.Rw(),
						By(chartScaling, chartPowers, uPower))
					vIn := b.Have(
						"so does tᵐ⁺ⁿ · v",
						"monoid_pow(R.mul, R.one, t, m + n) • v ∈ M₀",
						vSplit.Rw(),
						By(chartScaling, chartPowers, vPower))
					distribute := b.Have(
						"tᵐ⁺ⁿ distributes over u + v",
						"monoid_pow(R.mul, R.one, t, m + n) • (u + v) = "+
							"monoid_pow(R.mul, R.one, t, m + n) • u + monoid_pow(R.mul, R.one, t, m + n) • v",
						By(
							module.SmulAddLeft.Read(isModule).AsFact().At(power, u, v),
							tInR,
							uVector,
							vVector,
							comm_monoid.PowIn.Read(multiplicative)))
					sumIn := b.Have(
						"so tᵐ⁺ⁿ · (u + v) lies in M₀, a sum of two of its members",
						"monoid_pow(R.mul, R.one, t, m + n) • (u + v) ∈ M₀",
						distribute.Rw(),
						By(submodule.SubmoduleAdd.Read(chart), uIn, vIn))
					b.Show(
						"so u + v lies in S, at the exponent m + n",
						By(
							Normalized,
							membership.At(b.TermAs[B]("u + v")),
							group.MulIn.Read(module.AddGroupOn.Read(isModule)).AsFact().At(u, v),
							uVector,
							vVector,
							sumIn))
				}))

			within := a.Have(
				"S lies in V",
				"S ⊆ V.carrier",
				Unfold(set_basic.SubsetDef),
				a.ForEach(func(v *Expr[B]) Action { return By(membership.At(v)) }))
			zero := a.Have(
				"the zero vector lies in M₀, so in S",
				"V.zero ∈ S",
				By(a.Unfolded(chartInS, set_basic.SubsetDef), submodule.SubmoduleZero.Read(chart)))
			localSubmodule := a.Have(
				"S is an R-submodule of V: it lies in V, holds the zero "+
					"vector, and is closed under the sum and under scaling by R",
				"submodule(R, V, S)",
				By(within, zero, sums, scaled, submodule.SubmoduleCriterion.Read(isModule).At(S)))
			spanInS := a.Have(
				"so S holds the span of M₀, the least submodule holding M₀",
				"module_span(R, V, M₀) ⊆ S",
				By(submodule.SpanLeast.At(R, V, M0, S), localSubmodule, chartInS))

			spanSubmodule := a.Have(
				"the span of M₀ is a submodule of V",
				"submodule(R, V, module_span(R, V, M₀))",
				By(submodule.SpanSubmodule.Read(isModule), submodule.SubmoduleSubset.Read(chart)))
			chartInSpan := a.Unfolded(submodule.SubsetSpan.At(R, V, M0), set_basic.SubsetDef)
			sInSpan := a.Have(
				"each v of S lies in the span: v = sⁿ · (tⁿ · v), and tⁿ · v lies in M₀",
				"S ⊆ module_span(R, V, M₀)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					inS := b.Assume()
					n, power := b.ObtainAs[Nat](
						"a power tⁿ brings v into M₀",
						"∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀",
						By(membership.At(v), inS))
					sn, tn :=
						b.TermAs[A]("monoid_pow(R.mul, R.one, s, n)"), b.TermAs[A]("monoid_pow(R.mul, R.one, t, n)")
					multiple := b.Have(
						"sⁿ · (tⁿ · v) lies in the span, a multiple of a member of M₀",
						"monoid_pow(R.mul, R.one, s, n) • (monoid_pow(R.mul, R.one, t, n) • v) ∈ module_span(R, V, M₀)",
						By(
							submodule.SubmoduleSmul.Read(spanSubmodule),
							sInR,
							comm_monoid.PowIn.Read(multiplicative),
							chartInSpan,
							power))
					undone := b.Have(
						"sⁿ · (tⁿ · v) = (sⁿ · tⁿ) · v = one · v = v",
						"monoid_pow(R.mul, R.one, s, n) • (monoid_pow(R.mul, R.one, t, n) • v) = v",
						By(
							module.SmulMul.Read(isModule).AsFact().At(sn, tn, v),
							inversePowers.At(n),
							module.SmulOne.Read(isModule).AsFact().At(v),
							comm_monoid.PowIn.Read(multiplicative).AsFact().At(s, n),
							comm_monoid.PowIn.Read(multiplicative).AsFact().At(t, n),
							sInR,
							tInR,
							membership.At(v),
							inS))
					b.Show(
						"so v lies in the span",
						By(Normalized, undone, multiple))
				}))
			span := a.TermAs[Set[B]]("module_span(R, V, M₀)")
			a.Show(
				"the span of M₀ and S contain each other",
				By(set_order.SubsetAntisym.At(span, S), spanInS, sInSpan))
		}),
})}

// ChartSpanInter — over a biaffine datum, the R-span of the meet of two
// A₀-submodules of V is the meet of their spans: by ChartSpanAway each
// span is the set of vectors of V a power of t brings into the submodule.
// The span of the meet lies in both spans; and a vector that tⁿ brings
// into M₀ and tᵐ into N₀ is brought into both by tⁿ⁺ᵐ, which is tᵐ · tⁿ
// and tⁿ · tᵐ, each power of t lying in A₀ and the charts closed under it.
var ChartSpanInter = chartSpanInterThm{family.Add(registry.ProofEntry{
	Name: "ChartSpanInter",
	Key:  "prop_9d80119ae4016729",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀V:module_ops(A, B). ∀M₀ N₀:set(B).",
		Hypotheses: []string{
			"«waBiaffine»",
			"module_on(R, V)",
			"submodule(restrict_ring(R, A₀), V, M₀)",
			"submodule(restrict_ring(R, A₀), V, N₀)",
		},
		Conclusion: "module_span(R, V, M₀ ∩ N₀) = module_span(R, V, M₀) ∩ module_span(R, V, N₀)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M0, N0 *Expr[Set[B]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the charts and t, s form a biaffine datum",
				"V is a module over R",
				"M₀ is an A₀-submodule of V",
				"so is N₀")
			datum, isModule, chartM, chartN := hypotheses[0], hypotheses[1], hypotheses[2], hypotheses[3]
			parts := a.Conjuncts(
				a.Unfolded(datum, BiaffineDef),
				"R is a ring on its carrier",
				"A₀ is a subring of R",
				"and so is A₁",
				"t lies in A₀",
				"s lies in A₁",
				"t · s = one",
				"R is A₀ with t inverted",
				"R is A₁ with s inverted")
			ring := parts[0]
			chartRing := a.Have(
				"A₀ is a ring under R's operations",
				"comm_ring_on(restrict_ring(R, A₀))",
				By(comm_ring.SubringRingOn.Read(ring), parts[1]))
			chartPowers := a.Have(
				"every power of t lies in A₀",
				"∀n:num. monoid_pow(R.mul, R.one, t, n) ∈ A₀",
				By(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(chartRing)), parts[3]))
			tInR := a.Have(
				"t lies in R",
				"t ∈ R.carrier",
				By(comm_ring.SubringSubset.Read(parts[1]), parts[3], set_basic.SubsetDef))

			meet := a.TermAs[Set[B]]("M₀ ∩ N₀")
			awayM := a.Have(
				"a vector lies in the span of M₀ when it lies in V and a power of t brings it into M₀",
				"∀v:B. "+
					"    v ∈ module_span(R, V, M₀) ⇔ v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀)",
				BySets(ChartSpanAway.At(R, A0, A1, t, s, V, M0), datum, isModule, chartM))
			awayN := a.Have(
				"and in the span of N₀ when a power of t brings it into N₀",
				"∀v:B. "+
					"    v ∈ module_span(R, V, N₀) ⇔ v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ N₀)",
				BySets(ChartSpanAway.At(R, A0, A1, t, s, V, N0), datum, isModule, chartN))
			awayMeet := a.Have(
				"and in the span of M₀ ∩ N₀, an A₀-submodule too, when a power of t brings it into both",
				"∀v:B. "+
					"    v ∈ module_span(R, V, M₀ ∩ N₀) ⇔ "+
					"    v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀ ∩ N₀)",
				BySets(
					ChartSpanAway.At(R, A0, A1, t, s, V, meet),
					submodule.SubmoduleInter.At(a.TermAs[RingOps[A]]("restrict_ring(R, A₀)"), V, M0, N0),
					datum,
					isModule,
					chartM,
					chartN))

			powers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))
			tR := proof.MemberOf(t, tInR)
			spansInSpan := a.Have(
				"the meet of the spans lies in the span of the meet: tⁿ⁺ᵐ "+
					"brings v into both when tⁿ brings it into M₀ and tᵐ into N₀",
				"module_span(R, V, M₀) ∩ module_span(R, V, N₀) ⊆ module_span(R, V, M₀ ∩ N₀)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					v := b.FixAs[B]("v")
					spans := b.Conjuncts(
						b.Simplified(b.Assume(), Fwd(set_basic.InInter)),
						"v lies in the span of M₀",
						"and in the span of N₀")
					n, nPower := b.ObtainAs[Nat](
						"a power tⁿ brings v into M₀",
						"∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀",
						By(awayM.At(v), spans[0]))
					m, mPower := b.ObtainAs[Nat](
						"and a power tᵐ into N₀",
						"∃m:num. monoid_pow(R.mul, R.one, t, m) • v ∈ N₀",
						By(awayN.At(v), spans[1]))
					vector := b.Have(
						"v is a vector",
						"v ∈ V.carrier",
						By(awayM.At(v), spans[0]))
					vm := proof.MemberOf(v, vector)
					tn, tm := powers.At(tR, n), powers.At(tR, m)
					powerSum := b.Have(
						"tⁿ⁺ᵐ = tⁿ · tᵐ",
						"monoid_pow(R.mul, R.one, t, n + m) = "+
							"monoid_pow(R.mul, R.one, t, n) * monoid_pow(R.mul, R.one, t, m)",
						By(comm_monoid.PowAddOn.Read(comm_ring.MulMonoidOn.Read(ring)), tInR))
					inN := b.Have(
						"so tⁿ⁺ᵐ · v = tⁿ · (tᵐ · v) lies in N₀, tⁿ lying in A₀",
						"monoid_pow(R.mul, R.one, t, n + m) • v ∈ N₀",
						By(
							powerSum,
							module.SmulMul.Read(isModule).At(tn, tm, vm),
							submodule.SubmoduleSmul.Read(chartN).AsFact().At(
								tn, b.TermAs[B]("monoid_pow(R.mul, R.one, t, m) • v")),
							chartPowers.At(n),
							mPower))
					swapped := b.Have(
						"and tⁿ⁺ᵐ = tᵐ · tⁿ, R being commutative",
						"monoid_pow(R.mul, R.one, t, n + m) = "+
							"monoid_pow(R.mul, R.one, t, m) * monoid_pow(R.mul, R.one, t, n)",
						ByArith(ring, tInR, powerSum))
					inM := b.Have(
						"so tⁿ⁺ᵐ · v = tᵐ · (tⁿ · v) lies in M₀, tᵐ lying in A₀",
						"monoid_pow(R.mul, R.one, t, n + m) • v ∈ M₀",
						By(
							swapped,
							module.SmulMul.Read(isModule).At(tm, tn, vm),
							submodule.SubmoduleSmul.Read(chartM).AsFact().At(
								tm, b.TermAs[B]("monoid_pow(R.mul, R.one, t, n) • v")),
							chartPowers.At(m),
							nPower))
					b.Show(
						"so v lies in the span of M₀ ∩ N₀, at the exponent n + m",
						BySets(awayMeet.At(v), vector, inM, inN))
				}))
			a.Show(
				"the span of the meet lies in each span, so with the reverse inclusion the two are equal",
				BySets(spansInSpan, submodule.SpanMono.At(R, V, meet, M0), submodule.SpanMono.At(R, V, meet, N0)))
		}),
})}

// AmbientOfIntersection — the chartwise meet of two lattice pairs in V is
// a lattice pair, and its ambient is the meet of their ambients: over each
// chart the span of the meet is the meet of the spans (ChartSpanInter, at
// the exchanged datum for chart 1), so the two meets span one submodule,
// the meet of the spans of the first charts, which are the ambients.
var AmbientOfIntersection = ambientOfIntersectionThm{family.Add(registry.ProofEntry{
	Name: "AmbientOfIntersection",
	Key:  "prop_80be3fbae15e679a",
	Reading: "The biaffine datum is load-bearing: it makes the span of a " +
		"chart's submodule the vectors some power of t (of s at the other chart) " +
		"carries into it, which is what lets the meet be taken chart by chart.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀V:module_ops(A, B). " +
			"∀M N:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waBiaffine»",
			"«waPair»(M)",
			"«waPair»(N)",
		},
		Conclusion: "«waPair»((fst(M) ∩ fst(N), snd(M) ∩ snd(N))) ∧ " +
			"lattice_pair_ambient(R, V, (fst(M) ∩ fst(N), snd(M) ∩ snd(N))) = " +
			"lattice_pair_ambient(R, V, M) ∩ lattice_pair_ambient(R, V, N)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			V *Expr[ModuleOps[A, B]],
			M, N *Expr[Prod[Set[B], Set[B]]],
			given Fact,
		) {
			hypotheses := a.Conjuncts(
				given,
				"the charts and t, s form a biaffine datum",
				"M is a lattice pair",
				"so is N")
			datum := hypotheses[0]
			pairM := a.Conjuncts(
				a.Unfolded(hypotheses[1], LatticePairDef),
				"V is an R-module",
				"fst(M) is an A₀-submodule of V",
				"snd(M) is an A₁-submodule of V",
				"the charts of M span one R-submodule")
			pairN := a.Unfolded(hypotheses[2], LatticePairDef)
			fstM, fstN := a.TermAs[Set[B]]("fst(M)"), a.TermAs[Set[B]]("fst(N)")
			sndM, sndN := a.TermAs[Set[B]]("snd(M)"), a.TermAs[Set[B]]("snd(N)")

			firstMeet := a.Have(
				"over chart 0, the span of the meet of the first charts is the meet of their spans",
				"module_span(R, V, fst(M) ∩ fst(N)) = module_span(R, V, fst(M)) ∩ module_span(R, V, fst(N))",
				By(ChartSpanInter.At(R, A0, A1, t, s, V, fstM, fstN), datum, pairM[0], pairM[1], pairN))
			secondMeet := a.Have(
				"and over chart 1, through the exchanged datum, so is the span of the meet of the second charts",
				"module_span(R, V, snd(M) ∩ snd(N)) = module_span(R, V, snd(M)) ∩ module_span(R, V, snd(N))",
				By(
					ChartSpanInter.At(R, A1, A0, s, t, V, sndM, sndN),
					BiaffineSwap.At(R, A0, A1, t, s),
					datum,
					pairM[0],
					pairM[2],
					pairN))

			meet := a.TermAs[Prod[Set[B], Set[B]]]("(fst(M) ∩ fst(N), snd(M) ∩ snd(N))")
			first, second := a.TermAs[Set[B]]("fst(M) ∩ fst(N)"), a.TermAs[Set[B]]("snd(M) ∩ snd(N)")
			a.Show(
				"the chartwise meet is a lattice pair whose ambient is the meet of the ambients",
				SplitConj(
					Case(
						"its charts are submodules over A₀ and A₁, and their spans agree: "+
							"they are the meets of the chart spans of M and of N, which agree",
						By(
							LatticePairDef.At(R, A0, A1, V, meet),
							pairs.Fst.At(first, second),
							pairs.Snd.At(first, second),
							submodule.SubmoduleInter.At(a.TermAs[RingOps[A]]("restrict_ring(R, A₀)"), V, fstM, fstN),
							submodule.SubmoduleInter.At(a.TermAs[RingOps[A]]("restrict_ring(R, A₁)"), V, sndM, sndN),
							pairM[0],
							pairM[1],
							pairM[2],
							pairM[3],
							pairN,
							firstMeet,
							secondMeet)),
					Case(
						"its ambient, the span of its first chart, is the meet of the ambients of M and N",
						By(
							firstMeet,
							LatticePairAmbientDef.At(R, V, meet),
							LatticePairAmbientDef.At(R, V, M),
							LatticePairAmbientDef.At(R, V, N),
							pairs.Fst.At(first, second))),
				))
		}),
})}

// LatticePairByPowers — a pair of chart submodules is a lattice pair
// exactly when a power of t brings each member of chart 1 into chart 0
// and a power of s each member of chart 0 into chart 1.
var LatticePairByPowers = latticePairByPowersThm{family.Add(registry.ProofEntry{
	Name: "LatticePairByPowers",
	Key:  "prop_8af2ff32c456b18c",
	Reading: "Neither a containing pair nor finite dimension enters: a sub-pair of a " +
		"lattice pair is a lattice pair exactly when it passes the criterion. Over k[t, 1/t] " +
		"the pair ((t − 1) · k[t], k[1/t]) fails it — one lies in chart 1 and no power of t " +
		"is a multiple of t − 1 in k[t] — a point of the overlap twisted on one chart only.",
	Deps: []registry.EntryLike{
		BiaffineDef,
		BiaffineSwap,
		LatticePairDef,
		ChartSpanAway,
		submodule.SpanLeast,
		submodule.SpanSubmodule,
		submodule.SubsetSpan,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀t s:A. ∀V:module_ops(A, B). ∀M:prod(set(B), set(B)).",
		Hypotheses: []string{
			"«waBiaffine»",
			"module_on(R, V)",
			"submodule(restrict_ring(R, A₀), V, fst(M))",
			"submodule(restrict_ring(R, A₁), V, snd(M))",
		},
		Conclusion: "«waPair»(M) ⇔ " +
			"(∀v:B. v ∈ snd(M) ⇒ ∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ fst(M)) ∧ " +
			"(∀v:B. v ∈ fst(M) ⇒ ∃n:num. monoid_pow(R.mul, R.one, s, n) • v ∈ snd(M))",
	},
		"by ChartSpanAway, and at the exchanged datum (BiaffineSwap), the span of fst(M) is the "+
			"set of members of V a power of t brings into fst(M), and the span of snd(M) the set a "+
			"power of s brings into snd(M); the criterion says each chart lies in the other's span, "+
			"which is equality of the spans (SpanLeast, SubsetSpan), the lattice-pair condition"),
})}

// ---------------------------------------------------------------------------
// Localizing a chart quotient
// ---------------------------------------------------------------------------

// StableImageSurjectsOnLocalization — for A₀-submodules N₀ ⊆ M₀ with
// M₀/N₀ finite-dimensional over k, every v ∈ M₀ is, up to a member of
// N₀ after some power of t, a tⁿ-multiple of a member of M₀: the stable
// image of t on M₀/N₀ maps onto that quotient with t inverted. The images
// of M₀/N₀ under the powers of t stop shrinking at some N, multiplication
// by t being k-linear on a finite-dimensional space; so tᴺ(v + N₀) lies in
// tᴺ⁺ⁿ(M₀/N₀), as tᴺ⁺ⁿ(w + N₀) for some w ∈ M₀, and j = N.
var StableImageSurjectsOnLocalization = stableImageSurjectsOnLocalizationThm{family.Add(registry.ProofEntry{
	Name: "StableImageSurjectsOnLocalization",
	Key:  "prop_e999d7c4cefb6a3d",
	Reading: "Finite dimension is load-bearing: over k[t] with M₀ = k[t] and N₀ = {0}, " +
		"for n = 1 and v = one no w and j make tʲ · (one − t · w) zero. No biaffine datum is " +
		"used: t and k lie in the commutative ring A₀, which is all the k-linearity of t needs.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀:set(A). " +
			"∀t:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M₀ N₀:set(B). " +
			"∀v:B. " +
			"∀n:num.",
		Hypotheses: []string{
			"module_on(restrict_ring(R, A₀), V)",
			"t ∈ A₀",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"submodule(restrict_ring(R, A₀), V, M₀)",
			"submodule(restrict_ring(R, A₀), V, N₀)",
			"N₀ ⊆ M₀",
			"finite_dimensional(restrict_ring(R, k), quotient_module(restrict_module(V, M₀), N₀))",
			"v ∈ M₀",
		},
		Conclusion: "∃w:B. ∃j:num. " +
			"    w ∈ M₀ ∧ monoid_pow(R.mul, R.one, t, j) • (v + -(monoid_pow(R.mul, R.one, t, n) • w)) ∈ N₀",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0 *Expr[Set[A]],
			t *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[ModuleOps[A, B]],
			M0, N0 *Expr[Set[B]],
			hypotheses Fact,
			v *Expr[B],
			n *Expr[Nat],
			vIn Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"V is a module over A₀",
				"t lies in A₀",
				"k is a field under R's operations",
				"k lies in A₀",
				"M₀ is an A₀-submodule of V",
				"so is N₀",
				"N₀ lies in M₀",
				"M₀/N₀ is finite-dimensional over k")
			overA0, tIn, subfieldK, kIn, subM, subN, inside, finite :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6], given[7]

			chart := a.Have(
				"M₀, with V's operations, is a module over A₀",
				"module_on(restrict_ring(R, A₀), restrict_module(V, M₀))",
				By(submodule.SubmoduleModuleOn.Read(overA0).At(M0), subM))
			nSubM := a.Have(
				"N₀ is an A₀-submodule of M₀",
				"submodule(restrict_ring(R, A₀), restrict_module(V, M₀), N₀)",
				By(
					submodule.SubmoduleRestrict.At(a.TermAs[RingOps[A]]("restrict_ring(R, A₀)"), V, M0, N0),
					subN,
					inside))
			Q := a.TermAs[ModuleOps[A, Set[B]]]("quotient_module(restrict_module(V, M₀), N₀)")

			N, stable := a.ObtainAs[Nat](
				"the images of M₀/N₀ under the powers of t stop shrinking at some N",
				"∃N:num. ∀m:num. "+
					"    N ≤ m ⇒ "+
					"    image(λX:set(B). quotient_smul(V.add, V.smul, N₀, monoid_pow(R.mul, R.one, t, m), X), "+
					"        left_cosets(V.add, M₀, N₀)) = "+
					"    image(λX:set(B). quotient_smul(V.add, V.smul, N₀, monoid_pow(R.mul, R.one, t, N), X), "+
					"        left_cosets(V.add, M₀, N₀))",
				By(
					module_dimension.ScalarPowerImagesStabilize.At(R, A0, k, inv, Q, t),
					submodule.QuotientModuleOn.Read(chart).At(N0),
					nSubM,
					subfieldK,
					kIn,
					finite,
					tIn))
			beyond := a.TermAs[Nat]("N + n")

			additive := module.AddGroupOn.Read(chart)
			class := a.Have(
				"the classes of M₀/N₀ are the images of M₀ under the coset map, v + N₀ among them",
				"left_coset(V.add, v, N₀) ∈ left_cosets(V.add, M₀, N₀)",
				Simp(Fwd(quotient_group.LeftCosetsImage.Read(additive)), Fwd(group.CosetMapDef)),
				By(set_image.FunInImage.At(a.TermAs[Fun[B, Set[B]]]("λx:B. left_coset(V.add, x, N₀)"), M0, v), vIn))
			reached := a.Have(
				"tᴺ(v + N₀) lies in the image of tᴺ⁺ⁿ, the chain having stopped at N",
				"quotient_smul(V.add, V.smul, N₀, monoid_pow(R.mul, R.one, t, N), left_coset(V.add, v, N₀)) ∈ "+
					"image(λX:set(B). quotient_smul(V.add, V.smul, N₀, monoid_pow(R.mul, R.one, t, N + n), X), "+
					"    left_cosets(V.add, M₀, N₀))",
				By(
					stable.At(beyond),
					nat_order.LessEqAdd.At(N, n),
					class,
					set_image.FunInImage.At(
						a.TermAs[Fun[Set[B], Set[B]]](
							"λX:set(B). quotient_smul(V.add, V.smul, N₀, monoid_pow(R.mul, R.one, t, N), X)"),
						a.TermAs[Set[Set[B]]]("left_cosets(V.add, M₀, N₀)"),
						a.TermAs[Set[B]]("left_coset(V.add, v, N₀)"))))
			_, preimage := a.UnpackAs[Set[B]](a.Simplified(reached, Fwd(set_basic.InImage)), "Y")
			image := a.Conjuncts(
				preimage,
				"tᴺ(v + N₀) is tᴺ⁺ⁿ(Y)",
				"for a class Y of M₀/N₀")
			w, representative := a.UnpackAs[B](a.Simplified(
				image[1],
				Fwd(quotient_group.InLeftCosets.Read(additive))), "w")
			chosen := a.Conjuncts(
				representative,
				"Y is w + N₀",
				"for some w in M₀")
			wIn := chosen[1]

			ring := module.RingOn.Read(chart)
			powers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))
			tm, vm, wm := proof.MemberOf(t, tIn), proof.MemberOf(v, vIn), proof.MemberOf(w, wIn)
			tN, tn, tNn := powers.At(tm, N), powers.At(tm, n), powers.At(tm, beyond)
			sameClass := a.Have(
				"tᴺv and tᴺ⁺ⁿw lie in one class of N₀",
				"left_coset(V.add, monoid_pow(R.mul, R.one, t, N) • v, N₀) = "+
					"left_coset(V.add, monoid_pow(R.mul, R.one, t, N + n) • w, N₀)",
				By(
					submodule.QuotientSmulCoset.Read(chart).At(N0, tN, vm),
					submodule.QuotientSmulCoset.Read(chart).At(N0, tNn, wm),
					nSubM,
					image[0],
					chosen[0]))
			scaledV, scaledW := module.SmulIn.Read(chart).At(tN, vm), module.SmulIn.Read(chart).At(tNn, wm)
			difference := a.Have(
				"so -(tᴺ⁺ⁿw) + tᴺv lies in N₀",
				"-(monoid_pow(R.mul, R.one, t, N + n) • w) + monoid_pow(R.mul, R.one, t, N) • v ∈ N₀",
				By(
					group.LeftCosetEqOn.Read(additive).At(scaledW, scaledV, N0),
					sameClass,
					submodule.SubmoduleSubgroup.Read(nSubM)))
			shifted := module.SmulIn.Read(chart).At(tn, wm)
			expand := a.Have(
				"tᴺ(v − tⁿw) is that difference: tᴺ distributes and "+
					"passes the negation, tᴺtⁿ = tᴺ⁺ⁿ, and the sum commutes",
				"monoid_pow(R.mul, R.one, t, N) • (v + -(monoid_pow(R.mul, R.one, t, n) • w)) = "+
					"-(monoid_pow(R.mul, R.one, t, N + n) • w) + monoid_pow(R.mul, R.one, t, N) • v",
				By(
					module.SmulAddLeft.Read(chart).At(tN, vm, group.InvIn.Read(additive).At(shifted)),
					module.SmulNeg.Read(chart).At(tN, shifted),
					module.SmulMul.Read(chart).At(tN, tn, wm),
					comm_monoid.PowAddOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(tm, N, n),
					module.AddComm.Read(chart).At(scaledV, group.InvIn.Read(additive).At(scaledW))))
			a.Take(w)
			a.Take(N)
			a.Show(
				"w lies in M₀, and tᴺ(v − tⁿw) is the difference that lies in N₀",
				By(wIn, difference, expand))
		}),
})}

// QuotientLocalizes — for A₀-submodules N₀ ⊆ M₀ of V with M₀/N₀
// finite-dimensional over k, the R-span of M₀ is M₀ plus the R-span of
// N₀: at a sub-pair M' ⊆ M, ambient(M) = M₀ + ambient(M'). A vector x of
// the span has tⁿ • x ∈ M₀; the stable image gives w ∈ M₀ and j with
// tʲ • (tⁿ • x − tⁿ • w) ∈ N₀, which is t^(j + n) • (x − w), so x − w
// lies in the span of N₀ and x = w + (x − w). Conversely M₀ and the span
// of N₀ lie in the span of M₀, a group under the addition.
var QuotientLocalizes = quotientLocalizesThm{family.Add(registry.ProofEntry{
	Name: "QuotientLocalizes",
	Key:  "prop_3da791a26124956a",
	Reading: "⊇ holds of any N₀ ⊆ M₀. For ⊆ finite dimension is load-bearing: at k[t] ⊆ k[t, " +
		"1/t] with M₀ = k[t] and N₀ = {0} the span of M₀ is k[t, 1/t], not k[t] + {0}. Only " +
		"chart 0 enters; at chart 1 it is this theorem at the exchanged datum (BiaffineSwap).",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M₀ N₀:set(B).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"module_on(R, V)",
			"submodule(restrict_ring(R, A₀), V, M₀)",
			"submodule(restrict_ring(R, A₀), V, N₀)",
			"N₀ ⊆ M₀",
			"finite_dimensional(restrict_ring(R, k), quotient_module(restrict_module(V, M₀), N₀))",
		},
		Conclusion: "module_span(R, V, M₀) = set_mul(V.add, M₀, module_span(R, V, N₀))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[ModuleOps[A, B]],
			M0, N0 *Expr[Set[B]],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the biaffine datum",
				"k is a field",
				"k lies in chart 0",
				"V is a module over R",
				"M₀ is an A₀-submodule of V",
				"so is N₀",
				"N₀ lies in M₀",
				"and M₀/N₀ is finite-dimensional over k")
			datum, vModule, subM, subN, below := parts[0], parts[3], parts[4], parts[5], parts[6]
			chart := a.Conjuncts(
				a.Have(
					"chart 0 is a subring of R holding t",
					"subring(R, A₀) ∧ t ∈ A₀",
					By(a.Unfolded(datum, BiaffineDef))),
				"A₀ is a subring of R",
				"t lies in A₀")
			tInR := a.Have(
				"t is a scalar of R",
				"t ∈ R.carrier",
				By(comm_ring.SubringSubset.Read(chart[0]), chart[1], set_basic.SubsetDef))
			inV := a.Have(
				"M₀ lies in V's carrier",
				"M₀ ⊆ V.carrier",
				By(submodule.SubmoduleSubset.Read(subM)))
			additive := module.AddGroupOn.Read(vModule)
			multiplicative := comm_ring.MulMonoidOn.Read(module.RingOn.Read(vModule))
			spanM := a.Have(
				"the span of M₀ is the set of vectors of V a power of t brings into M₀",
				"module_span(R, V, M₀) = {v:B | v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀)}",
				By(ChartSpanAway.At(R, A0, A1, t, s, V, M0), datum, vModule, subM))
			awayM := a.Have(
				"so a vector lies in the span of M₀ exactly when it lies in V and a power of t brings it into M₀",
				"∀v:B. "+
					"    v ∈ module_span(R, V, M₀) ⇔ v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ M₀)",
				BySets(spanM))
			spanN := a.Have(
				"and the span of N₀ the set of vectors of V a power of t brings into N₀",
				"module_span(R, V, N₀) = {v:B | v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ N₀)}",
				By(ChartSpanAway.At(R, A0, A1, t, s, V, N0), datum, vModule, subN))
			awayN := a.Have(
				"so a vector lies in the span of N₀ exactly when it lies in V and a power of t brings it into N₀",
				"∀v:B. "+
					"    v ∈ module_span(R, V, N₀) ⇔ v ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • v ∈ N₀)",
				BySets(spanN))

			within := a.Have(
				"every vector of the span of M₀ is a member of M₀ plus a vector of the span of N₀",
				"module_span(R, V, M₀) ⊆ set_mul(V.add, M₀, module_span(R, V, N₀))",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inSpan := b.Assume()
					away := b.Conjuncts(
						b.Have(
							"x lies in V, and a power of t brings it into M₀",
							"x ∈ V.carrier ∧ (∃n:num. monoid_pow(R.mul, R.one, t, n) • x ∈ M₀)",
							By(awayM.At(x), inSpan)),
						"x is a vector",
						"some tⁿ • x lies in M₀")
					xm := proof.MemberOf(x, away[0])
					n, power := b.UnpackAs[Nat](away[1], "n")
					w, j, stable := b.Obtain2As[B, Nat](
						"the stable image of t on M₀/N₀ meets tⁿ • x: some tʲ • (tⁿ • x − tⁿ • w) lies in N₀",
						"∃w:B. ∃j:num. "+
							"    w ∈ M₀ ∧ "+
							"    monoid_pow(R.mul, R.one, t, j) • "+
							"    (monoid_pow(R.mul, R.one, t, n) • x + -(monoid_pow(R.mul, R.one, t, n) • w)) ∈ "+
							"    N₀",
						By(
							StableImageSurjectsOnLocalization.At(
								R, A0, t, k, inv, V, M0, N0, b.TermAs[B]("monoid_pow(R.mul, R.one, t, n) • x"), n),
							module.ModuleRestrictScalars.Read(vModule).At(A0),
							chart[0],
							chart[1],
							parts[1],
							parts[2],
							subM,
							subN,
							below,
							parts[7],
							power))
					found := b.Conjuncts(
						stable,
						"w lies in M₀",
						"tʲ brings tⁿ • x − tⁿ • w into N₀")
					wm := proof.MemberOf(w, b.Have(
						"w is a vector, M₀ lying in V's carrier",
						"w ∈ V.carrier",
						By(inV, found[0], set_basic.SubsetDef)))
					negW := group.InvIn.Read(additive).At(wm)
					difference := group.MulIn.Read(additive).At(xm, negW)
					tm := proof.MemberOf(t, tInR)
					tj, tn :=
						comm_monoid.PowIn.Read(multiplicative).At(tm, j), comm_monoid.PowIn.Read(multiplicative).At(tm, n)
					brought := b.Have(
						"so the power t^(j + n) brings x − w into N₀",
						"∃m:num. monoid_pow(R.mul, R.one, t, m) • (x + -w) ∈ N₀",
						Derive(func(c *Argument) {
							c.Take(c.TermAs[Nat]("j + n"))
							expand := c.Have(
								"t^(j + n) • (x − w) is tʲ • (tⁿ • x − tⁿ • w)",
								"monoid_pow(R.mul, R.one, t, j + n) • (x + -w) = "+
									"monoid_pow(R.mul, R.one, t, j) • "+
									"(monoid_pow(R.mul, R.one, t, n) • x + -(monoid_pow(R.mul, R.one, t, n) • w))",
								CalcEq(
									Leg(
										c.TermAs[B]("(monoid_pow(R.mul, R.one, t, j) * monoid_pow(R.mul, R.one, t, n)) • (x + -w)"),
										"the power splits",
										By(comm_monoid.PowAddOn.Read(multiplicative).At(tm, j, n))),
									Leg(
										c.TermAs[B]("monoid_pow(R.mul, R.one, t, j) • (monoid_pow(R.mul, R.one, t, n) • (x + -w))"),
										"the two scalings compose",
										By(module.SmulMul.Read(vModule).At(tj, tn, difference))),
									Leg(
										c.TermAs[B](
											"monoid_pow(R.mul, R.one, t, j) • "+
												"(monoid_pow(R.mul, R.one, t, n) • x + monoid_pow(R.mul, R.one, t, n) • -w)"),
										"tⁿ distributes over x − w",
										By(module.SmulAddLeft.Read(vModule).At(tn, xm, negW))),
									FinalLeg(
										"and passes the negation",
										By(module.SmulNeg.Read(vModule).At(tn, wm))),
								))
							c.Show(
								"which is the member of N₀ the stable image gave",
								expand.Rw(),
								By(found[1]))
						}))
					inSpanN := b.Have(
						"so x − w lies in the span of N₀",
						"x + -w ∈ module_span(R, V, N₀)",
						By(awayN.At(b.TermAs[B]("x + -w")), difference, brought))
					split := b.Have(
						"x is w + (x − w), the addition commuting",
						"x = w + (x + -w)",
						By(
							Normalized,
							module.AddComm.Read(vModule).At(xm, negW),
							group.MulInvCancelLeftOn.Read(additive).At(wm, xm)))
					b.Do(Simp(Fwd(quotient_group.InSetMul)))
					b.Take(w)
					b.Take(b.TermAs[B]("x + -w"))
					b.Show(
						"so x is the member w of M₀ plus the vector x − w of the span of N₀",
						By(found[0], inSpanN, split))
				}))

			spanM0 := a.TermAs[Set[B]]("module_span(R, V, M₀)")
			spanSubmodule := a.Have(
				"the span of M₀ is a submodule of V",
				"submodule(R, V, module_span(R, V, M₀))",
				By(submodule.SpanSubmodule.Read(vModule).At(M0), inV))
			spanGroup := a.Have(
				"so a group under V's addition",
				"group_on(restrict_group(module_additive_group(V), module_span(R, V, M₀)))",
				By(
					group.SubgroupGroupOn.Read(additive).At(spanM0),
					submodule.SubmoduleSubgroup.Read(spanSubmodule)))
			sums := a.TermAs[Set[B]]("set_mul(V.add, M₀, module_span(R, V, N₀))")
			covers := a.Have(
				"M₀ and the span of N₀ lie in the span of M₀, so their sums do",
				"set_mul(V.add, M₀, module_span(R, V, N₀)) ⊆ module_span(R, V, M₀)",
				By(
					quotient_group.SetMulIn.Read(spanGroup).At(M0, a.TermAs[Set[B]]("module_span(R, V, N₀)")),
					submodule.SubsetSpan.At(R, V, M0),
					submodule.SpanMono.At(R, V, N0, M0),
					below))
			a.Show(
				"the two inclusions make the sets equal",
				By(within, covers, set_order.SubsetAntisym.At(spanM0, sums)))
		}),
})}

// QuotientDimLocalizes — for A₀-submodules N₀ ⊆ M₀ of V with M₀/N₀
// finite-dimensional over k, the span of M₀ modulo the span of N₀ is
// finite-dimensional, of dimension at most that of M₀/N₀: the k-linear
// v ↦ v + span(N₀) on M₀ kills N₀ and so descends to M₀/N₀, and it is
// onto, the span of M₀ being M₀ plus the span of N₀ (QuotientLocalizes);
// an image of M₀/N₀ is no bigger than M₀/N₀.
var QuotientDimLocalizes = quotientDimLocalizesThm{family.Add(registry.ProofEntry{
	Name: "QuotientDimLocalizes",
	Key:  "prop_ad8ba5c9c757a099",
	Reading: "The inequality can be strict: the classes of M₀/N₀ killed by a " +
		"power of t — the points of chart 0 off the overlap — vanish on the overlap.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀A₀ A₁:set(A). " +
			"∀t s:A. " +
			"∀k:set(A). " +
			"∀inv:(A → A). " +
			"∀V:module_ops(A, B). " +
			"∀M₀ N₀:set(B).",
		Hypotheses: []string{
			"biaffine(R, A₀, A₁, t, s)",
			"ring_subfield(R, inv, k)",
			"k ⊆ A₀",
			"module_on(R, V)",
			"submodule(restrict_ring(R, A₀), V, M₀)",
			"submodule(restrict_ring(R, A₀), V, N₀)",
			"N₀ ⊆ M₀",
			"finite_dimensional(restrict_ring(R, k), quotient_module(restrict_module(V, M₀), N₀))",
		},
		Conclusion: "finite_dimensional(restrict_ring(R, k), " +
			"    quotient_module(restrict_module(V, module_span(R, V, M₀)), module_span(R, V, N₀))) ∧ " +
			"module_dim(restrict_ring(R, k), " +
			"    quotient_module(restrict_module(V, module_span(R, V, M₀)), module_span(R, V, N₀))) ≤ " +
			"module_dim(restrict_ring(R, k), quotient_module(restrict_module(V, M₀), N₀))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1 *Expr[Set[A]],
			t, s *Expr[A],
			k *Expr[Set[A]],
			inv *Arrow[A, A],
			V *Expr[ModuleOps[A, B]],
			M0, N0 *Expr[Set[B]],
			hypotheses Fact,
		) {
			given := a.Conjuncts(
				hypotheses,
				"R, A₀ and A₁ form a biaffine datum",
				"k is a field",
				"k lies in A₀",
				"V is a module over R",
				"M₀ is a submodule of V over A₀",
				"so is N₀",
				"N₀ lies in M₀",
				"M₀/N₀ is finite-dimensional over k")
			datum, subfieldK, kInA0, moduleV, subM0, subN0, nInM, finiteQ :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6], given[7]
			K := a.TermAs[RingOps[A]]("restrict_ring(R, k)")
			spanM, spanN := a.TermAs[Set[B]]("module_span(R, V, M₀)"), a.TermAs[Set[B]]("module_span(R, V, N₀)")
			W, U :=
				a.TermAs[ModuleOps[A, B]]("restrict_module(V, module_span(R, V, M₀))"),
				a.TermAs[ModuleOps[A, B]]("restrict_module(V, M₀)")
			Q := a.TermAs[ModuleOps[A, Set[B]]]("quotient_module(restrict_module(V, M₀), N₀)")
			target := a.TermAs[ModuleOps[A, Set[B]]](
				"quotient_module(restrict_module(V, module_span(R, V, M₀)), module_span(R, V, N₀))")
			f := a.TermAs[Fun[B, Set[B]]]("λu:B. left_coset(V.add, u, module_span(R, V, N₀))")
			g := a.TermAs[Fun[Set[B], Set[B]]]("induced_map(λu:B. left_coset(V.add, u, module_span(R, V, N₀)))")
			classes := a.TermAs[Set[Set[B]]]("left_cosets(V.add, M₀, N₀)")

			// The two spans, the span of N₀ inside that of M₀.
			kInR := a.Have(
				"k lies in R, chart 0 lying there",
				"k ⊆ R.carrier",
				By(ChartSubsetInOverlap.At(R, A0, A1, t, s, k), datum, kInA0))
			mInV := a.Have(
				"M₀ lies in V",
				"M₀ ⊆ V.carrier",
				By(submodule.SubmoduleSubset.Read(subM0)))
			spanNSub := a.Have(
				"the span of N₀ is a submodule of V",
				"submodule(R, V, module_span(R, V, N₀))",
				By(submodule.SubmoduleSubset.Read(subN0), submodule.SpanSubmodule.Read(moduleV).At(N0)))
			spans := a.Have(
				"the span of N₀ lies in that of M₀",
				"module_span(R, V, N₀) ⊆ module_span(R, V, M₀)",
				By(nInM, submodule.SpanMono.At(R, V, N0, M0)))

			// Everything read over k: the span of M₀ is a k-module, holding M₀
			// and the span of N₀ as k-submodules, and N₀ is one of M₀.
			moduleW := a.Have(
				"the span of M₀ is a module over R",
				"module_on(R, restrict_module(V, module_span(R, V, M₀)))",
				By(
					mInV,
					submodule.SpanSubmodule.Read(moduleV).At(M0),
					submodule.SubmoduleModuleOn.Read(moduleV).At(spanM)))
			subringK := a.Have(
				"k is a subring of R",
				"subring(R, k)",
				By(ChartFieldSubring.At(R, A0, A1, t, s, k, inv), datum, subfieldK, kInA0))
			moduleWk := a.Have(
				"and over its subring k",
				"module_on(restrict_ring(R, k), restrict_module(V, module_span(R, V, M₀)))",
				By(moduleW, subringK, module.ModuleRestrictScalars.At(R, W, k)))
			spanNInW := a.Have(
				"the span of N₀ is a k-submodule of the span of M₀",
				"submodule(restrict_ring(R, k), restrict_module(V, module_span(R, V, M₀)), module_span(R, V, N₀))",
				By(
					submodule.SubmoduleRestrictScalars.Read(spanNSub).At(K),
					kInR,
					spans,
					submodule.SubmoduleRestrict.At(K, V, spanM, spanN)))
			mInW := a.Have(
				"so is M₀",
				"submodule(restrict_ring(R, k), restrict_module(V, module_span(R, V, M₀)), M₀)",
				By(
					submodule.SubmoduleRestrictScalars.Read(subM0).At(K),
					kInA0,
					submodule.SubsetSpan.At(R, V, M0),
					submodule.SubmoduleRestrict.At(K, V, spanM, M0)))
			nInU := a.Have(
				"N₀ is a k-submodule of M₀",
				"submodule(restrict_ring(R, k), restrict_module(V, M₀), N₀)",
				By(
					submodule.SubmoduleRestrictScalars.Read(subN0).At(K),
					kInA0,
					nInM,
					submodule.SubmoduleRestrict.At(K, V, M0, N0)))

			projection := a.Unfolded(a.Have(
				"the projection of the span of M₀ onto the target is k-linear",
				"module_homomorphism(restrict_ring(R, k), "+
					"    restrict_module(V, module_span(R, V, M₀)), "+
					"    quotient_module(restrict_module(V, module_span(R, V, M₀)), module_span(R, V, N₀)), "+
					"    coset_map(V.add, module_span(R, V, N₀)))",
				By(moduleWk, spanNInW, module_homomorphism.ProjectionHom.At(K, W, spanN))), group.CosetMapDef)
			sameVectors := a.Have(
				"M₀ inside the span of M₀ carries V's operations",
				"restrict_module(restrict_module(V, module_span(R, V, M₀)), M₀) = restrict_module(V, M₀)",
				Unfold(module_record.RestrictModuleDef))
			onM := a.Have(
				"so is its restriction to M₀",
				"module_homomorphism(restrict_ring(R, k), "+
					"    restrict_module(V, M₀), "+
					"    quotient_module(restrict_module(V, module_span(R, V, M₀)), module_span(R, V, N₀)), "+
					"    λu:B. left_coset(V.add, u, module_span(R, V, N₀)))",
				sameVectors.RwRev(),
				By(projection, mInW, module_homomorphism.HomRestrictSource.At(K, W, target, f, M0)))
			kernel := a.Unfolded(a.Have(
				"the projection kills exactly the span of N₀",
				"group_kernel(module_span(R, V, N₀), "+
					"    module_span(R, V, M₀), "+
					"    coset_map(V.add, module_span(R, V, N₀))) = "+
					"module_span(R, V, N₀)",
				By(moduleWk, spanNInW, module_homomorphism.ProjectionKernel.At(K, W, spanN))), group.CosetMapDef)
			kills := a.Have(
				"so on M₀ it kills N₀",
				"N₀ ⊆ group_kernel(module_span(R, V, N₀), M₀, λu:B. left_coset(V.add, u, module_span(R, V, N₀)))",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[B]("x")
					inN := b.Assume()
					inM := b.Have(
						"x lies in M₀",
						"x ∈ M₀",
						By(inN, nInM, set_basic.SubsetDef))
					inKernel := b.Have(
						"and in the span of N₀, the kernel of the projection",
						"x ∈ "+
							"group_kernel(module_span(R, V, N₀), "+
							"    module_span(R, V, M₀), "+
							"    λu:B. left_coset(V.add, u, module_span(R, V, N₀)))",
						kernel.Rw(),
						By(inN, submodule.SubsetSpan.At(R, V, N0), set_basic.SubsetDef))
					b.Show(
						"x is a member of M₀ the projection kills",
						By(
							inM,
							inKernel,
							group_homomorphism.InKernel.At(spanN, spanM, f, x),
							group_homomorphism.InKernel.At(spanN, M0, f, x)))
				}))
			induced := a.Conjuncts(
				a.Have(
					"so it descends to a k-linear g on M₀/N₀, g(v + N₀) = v + span(N₀)",
					"module_homomorphism(restrict_ring(R, k), "+
						"    quotient_module(restrict_module(V, M₀), N₀), "+
						"    quotient_module(restrict_module(V, module_span(R, V, M₀)), module_span(R, V, N₀)), "+
						"    induced_map(λu:B. left_coset(V.add, u, module_span(R, V, N₀)))) ∧ "+
						"(∀x:B. "+
						"    x ∈ M₀ ⇒ "+
						"    induced_map(λu:B. left_coset(V.add, u, module_span(R, V, N₀)), left_coset(V.add, x, N₀)) = "+
						"    left_coset(V.add, x, module_span(R, V, N₀)))",
					By(nInU, onM, kills, module_homomorphism.InducedMapHom.At(K, U, target, N0, f))),
				"g is k-linear",
				"g(v + N₀) = v + span(N₀)")
			linear, values := induced[0], induced[1]

			// g is onto: a class x + span(N₀) of the target has x = m + n with
			// m ∈ M₀ and n in the span of N₀ (QuotientLocalizes), and it is
			// m + span(N₀) = g(m + N₀).
			localizes := a.Have(
				"the span of M₀ is M₀ plus the span of N₀",
				"module_span(R, V, M₀) = set_mul(V.add, M₀, module_span(R, V, N₀))",
				By(hypotheses, QuotientLocalizes.At(R, A0, A1, t, s, k, inv, V, M0, N0)))
			additive := module.AddGroupOn.Read(moduleV)
			subgroupN := submodule.SubmoduleSubgroup.Read(spanNSub)
			moduleU := module_homomorphism.HomSource.Read(onM)
			into := a.Have(
				"g takes its values in the target",
				"image(induced_map(λu:B. left_coset(V.add, u, module_span(R, V, N₀))), "+
					"    left_cosets(V.add, M₀, N₀)) ⊆ "+
					"left_cosets(V.add, module_span(R, V, M₀), module_span(R, V, N₀))",
				By(submodule.SubmoduleSubset.Read(module_homomorphism.ImageSubmodule.Read(linear))))
			covers := a.Have(
				"every class of the target is a value of g",
				"left_cosets(V.add, module_span(R, V, M₀), module_span(R, V, N₀)) ⊆ "+
					"image(induced_map(λu:B. left_coset(V.add, u, module_span(R, V, N₀))), left_cosets(V.add, M₀, N₀))",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					Y := b.FixAs[Set[B]]("Y")
					inTarget := b.Assume()
					x, ofX := b.ObtainAs[B](
						"Y is the class of a member x of the span of M₀",
						"∃x:B. Y = left_coset(V.add, x, module_span(R, V, N₀)) ∧ x ∈ module_span(R, V, M₀)",
						By(inTarget, spans, quotient_group.InLeftCosets.Read(module.AddGroupOn.Read(moduleW)).At(spanN, Y)))
					aboutX := b.Conjuncts(
						ofX,
						"Y is the class of x",
						"x lies in the span of M₀")
					inSum := b.Have(
						"so x lies in M₀ plus the span of N₀",
						"x ∈ set_mul(V.add, M₀, module_span(R, V, N₀))",
						localizes.RwRev(),
						By(aboutX[1]))
					m, n, split := b.Obtain2As[B, B](
						"x is m + n with m ∈ M₀ and n in the span of N₀",
						"∃m n:B. m ∈ M₀ ∧ n ∈ module_span(R, V, N₀) ∧ x = m + n",
						By(inSum, quotient_group.InSetMul.At(b.TermAs[Op[B]]("V.add"), M0, spanN, x)))
					parts := b.Conjuncts(
						split,
						"m lies in M₀",
						"n lies in the span of N₀",
						"x is m + n")
					mm := proof.MemberOf(m, b.Have(
						"m lies in V",
						"m ∈ V.carrier",
						By(parts[0], mInV, set_basic.SubsetDef)))
					nm := proof.MemberOf(n, b.Have(
						"so does n",
						"n ∈ V.carrier",
						By(parts[1], submodule.SubmoduleSubset.Read(spanNSub), set_basic.SubsetDef)))
					sameClass := b.Have(
						"m and m + n have one class, -m + (m + n) = n lying in the span of N₀",
						"left_coset(V.add, m, module_span(R, V, N₀)) = left_coset(V.add, m + n, module_span(R, V, N₀))",
						By(
							group.InvMulCancelLeftOn.Read(additive).At(mm, nm),
							parts[1],
							subgroupN,
							group.LeftCosetEqOn.Read(additive).At(mm, group.MulIn.Read(additive).At(mm, nm), spanN)))
					class := b.TermAs[Set[B]]("left_coset(V.add, m, N₀)")
					ofM := b.Have(
						"m + N₀ is the class of a member of M₀, m itself",
						"∃y:B. left_coset(V.add, m, N₀) = left_coset(V.add, y, N₀) ∧ y ∈ M₀",
						Witness(m),
						By(parts[0]))
					classOfM := b.Have(
						"so it is a class of M₀/N₀",
						"left_coset(V.add, m, N₀) ∈ left_cosets(V.add, M₀, N₀)",
						By(ofM, nInM, quotient_group.InLeftCosets.Read(module.AddGroupOn.Read(moduleU)).At(N0, class)))
					b.Show(
						"Y = m + span(N₀) = g(m + N₀)",
						By(
							aboutX[0],
							parts[2],
							sameClass,
							classOfM,
							parts[0],
							values.At(m),
							set_image.FunInImage.At(g, classes, class)))
				}))
			onto := a.Have(
				"so g is onto the target",
				"image(induced_map(λu:B. left_coset(V.add, u, module_span(R, V, N₀))), "+
					"    left_cosets(V.add, M₀, N₀)) = "+
					"left_cosets(V.add, module_span(R, V, M₀), module_span(R, V, N₀))",
				By(into, covers, set_order.SubsetAntisym))

			// The target is the image of g, a linear map out of the
			// finite-dimensional M₀/N₀ over the field k.
			a.Show(
				"the target, the image of M₀/N₀ under g, is finite-dimensional of dimension at most that of M₀/N₀",
				By(
					subfieldK,
					field.RingSubfieldRestrict.At(R, k, inv, k),
					linear,
					finiteQ,
					onto,
					module_record.RestrictModuleCarrier.At(target),
					module_dimension.ImageDim.At(K, inv, Q, target, g)))
		}),
})}
