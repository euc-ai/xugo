// bolzano_weierstrass.go — cluster points and the Bolzano–Weierstrass
// theorem (README, "A bounded sequence has a cluster point, and a
// cluster point is the limit of a subsequence").
//
// The upper and the lower limit of a bounded sequence are cluster
// points (the limits themselves, and the convergence of the tail suprema
// and infima to them, are TailSupConvergesToLimsup and
// TailInfConvergesToLiminf); a cluster point is the limit of a
// subsequence, through the 1/(n + 1) criterion placed just above it; a
// subsequence of a convergent sequence has its limit, so the shift by
// one keeps a sequence's limits, and LimitShift adds the converse; and
// Bolzano–Weierstrass is the corollary.

package real_sequences

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// BoundedClusterPoint — the upper limit of a bounded sequence is a
// cluster point of it: Bolzano–Weierstrass, by the upper limit. (The
// name says what it gives a bounded sequence — the cluster point that
// Bolzano–Weierstrass and the Cauchy criterion use; its mirror at the
// lower limit is LiminfClusterPoint.)
//
// Write s(N) for the supremum of the N-th tail's range (TailHasSup) and
// L = real_limsup(a), the infimum of the s(N). Given ε > 0 and an index N, the tail suprema tend to L,
// so past some M every s(K) is within ε of L; take K = N + M. Then s(K)
// lies above L − ε, and a supremum is approached from inside: some term
// a(n) of the K-th tail exceeds L − ε. That term is at most s(K), which
// lies below L + ε; so a(n) is within ε of L, and n ≥ K ≥ N.
var BoundedClusterPoint = boundedClusterPointThm{family.Add(registry.ProofEntry{
	Name: "BoundedClusterPoint",
	Key:  "prop_d58ff31d726694fa",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "real_cluster_point(a, real_limsup(a))",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], bounded Fact) {
			hasSup := arg.Have(
				"every tail's range has its supremum s(N)",
				"∀N:num. real_has_sup(image(a, {n:num | N ≤ n}), sup(image(a, {n:num | N ≤ n})))",
				By(bounded, At(TailHasSup, a, B)))
			supsConverge := arg.Have(
				"the tail suprema converge to L, the upper limit",
				"(λN:num. sup(image(a, {n:num | N ≤ n}))) ⟶ real_limsup(a)",
				By(bounded, TailSupConvergesToLimsup.At(a, B)))
			supsNear := arg.Unfolded(supsConverge, RealConvergesToDef)

			// The goal read as its ε-N statement: past every index N, a term
			// within ε of L.
			arg.Do(Unfold(RealClusterPointDef))
			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			N := arg.FixAs[Nat]()
			M, settled := arg.ObtainAs[Nat](
				"the tail suprema's limit at ε hands over an index M past which every s(K) is within ε of L",
				"∃M:num. ∀K:num. M ≤ K ⇒ |sup(image(a, {n:num | K ≤ n})) - real_limsup(a)| < ε",
				By(supsNear.At(eps), pos))
			K := arg.TermAs[Nat]("N + M₀")
			pastM := arg.Have(
				"K = N + M is past M",
				"M₀ ≤ N + M₀",
				Cite(nat_order.LessEqAddLeft))
			nearK := arg.Have(
				"so s(K) is within ε of L",
				"|sup(image(a, {n:num | N + M₀ ≤ n})) - real_limsup(a)| < ε",
				By(settled.At(K), pastM))

			kthTail := arg.TermAs[Set[Nat]]("{n:num | N + M₀ ≤ n}")
			kthRange := arg.TermAs[Set[Real]]("image(a, {n:num | N + M₀ ≤ n})")
			tailSup := arg.TermAs[Real]("sup(image(a, {n:num | N + M₀ ≤ n}))")
			belowL := arg.TermAs[Real]("real_limsup(a) - ε")
			strictlyBelow := arg.Have(
				"so L − ε lies strictly below s(K)",
				"real_limsup(a) - ε < sup(image(a, {n:num | N + M₀ ≤ n}))",
				ByArith(nearK))
			n, approach := arg.ObtainAs[Nat](
				"the supremum is approached from inside: some term a(n), n in the K-th tail, exceeds L − ε",
				"∃n:num. n ∈ {k:num | N + M₀ ≤ k} ∧ real_limsup(a) - ε < a(n)",
				By(
					hasSup.At(K),
					strictlyBelow,
					real_sup_inf.HasSupApproach.At(kthRange, tailSup, belowL),
					set_image.ExistsInImage.At(a, kthTail, arg.TermAs[Set[Real]]("λy:real. real_limsup(a) - ε < y"))))
			inTail := arg.Have(
				"the term's index lies in the K-th tail",
				"n₀ ∈ {k:num | N + M₀ ≤ k}",
				By(approach))
			belowSup := arg.Have(
				"the supremum caps the term, a(n) being in the K-th tail's range",
				"a(n₀) ≤ sup(image(a, {n:num | N + M₀ ≤ n}))",
				By(
					hasSup.At(K),
					inTail,
					set_image.FunInImage.At(a, kthTail, n),
					real_sup_inf.HasSupUpperBound.At(kthRange, tailSup, a.Apply(n))))
			pastN := arg.Have(
				"n ≥ K = N + M ≥ N",
				"N ≤ n₀",
				BySets(inTail, nat_order.LessEqAdd.At(N, M), nat_order.LessEqTrans.At(N, K, n)))

			arg.Take(n)
			arg.Show(
				"L − ε < a(n) ≤ s(K) < L + ε: the term lies within ε of L, past N",
				ByArith(pastN, approach, belowSup, nearK))
		}),
})}

// LiminfClusterPoint — the lower limit of a bounded sequence is a
// cluster point of it too: the mirror of BoundedClusterPoint.
//
// Write i(N) for the infimum of the N-th tail's range (TailHasInf) and
// L = real_liminf(a), the supremum of the i(N). Given ε > 0 and an index N,
// the tail infima tend to L, so past some M every i(K) is within ε of L;
// take K = N + M. Then i(K) lies below L + ε, and an infimum is
// approached from inside: some term a(n) of the K-th tail lies below
// L + ε. That term is at least i(K), which lies above L − ε; so a(n) is
// within ε of L, and n ≥ K ≥ N.
var LiminfClusterPoint = liminfClusterPointThm{family.Add(registry.ProofEntry{
	Name: "LiminfClusterPoint",
	Key:  "prop_3012b5c7774bd624",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "real_cluster_point(a, real_liminf(a))",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], bounded Fact) {
			hasInf := arg.Have(
				"every tail's range has its infimum i(N)",
				"∀N:num. real_has_inf(image(a, {n:num | N ≤ n}), inf(image(a, {n:num | N ≤ n})))",
				By(bounded, At(TailHasInf, a, B)))
			infsConverge := arg.Have(
				"the tail infima converge to L, the lower limit",
				"(λN:num. inf(image(a, {n:num | N ≤ n}))) ⟶ real_liminf(a)",
				By(bounded, TailInfConvergesToLiminf.At(a, B)))
			infsNear := arg.Unfolded(infsConverge, RealConvergesToDef)

			// The goal read as its ε-N statement: past every index N, a term
			// within ε of L.
			arg.Do(Unfold(RealClusterPointDef))
			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			N := arg.FixAs[Nat]()
			M, settled := arg.ObtainAs[Nat](
				"the tail infima's limit at ε hands over an index M past which every i(K) is within ε of L",
				"∃M:num. ∀K:num. M ≤ K ⇒ |inf(image(a, {n:num | K ≤ n})) - real_liminf(a)| < ε",
				By(infsNear.At(eps), pos))
			K := arg.TermAs[Nat]("N + M₀")
			pastM := arg.Have(
				"K = N + M is past M",
				"M₀ ≤ N + M₀",
				Cite(nat_order.LessEqAddLeft))
			nearK := arg.Have(
				"so i(K) is within ε of L",
				"|inf(image(a, {n:num | N + M₀ ≤ n})) - real_liminf(a)| < ε",
				By(settled.At(K), pastM))

			kthTail := arg.TermAs[Set[Nat]]("{n:num | N + M₀ ≤ n}")
			kthRange := arg.TermAs[Set[Real]]("image(a, {n:num | N + M₀ ≤ n})")
			tailInf := arg.TermAs[Real]("inf(image(a, {n:num | N + M₀ ≤ n}))")
			aboveL := arg.TermAs[Real]("real_liminf(a) + ε")
			strictlyBelow := arg.Have(
				"so i(K) lies strictly below L + ε",
				"inf(image(a, {n:num | N + M₀ ≤ n})) < real_liminf(a) + ε",
				ByArith(nearK))
			n, approach := arg.ObtainAs[Nat](
				"the infimum is approached from inside: some term a(n), n in the K-th tail, lies below L + ε",
				"∃n:num. n ∈ {k:num | N + M₀ ≤ k} ∧ a(n) < real_liminf(a) + ε",
				By(
					hasInf.At(K),
					strictlyBelow,
					real_sup_inf.HasInfApproach.At(kthRange, tailInf, aboveL),
					set_image.ExistsInImage.At(a, kthTail, arg.TermAs[Set[Real]]("λy:real. y < real_liminf(a) + ε"))))
			inTail := arg.Have(
				"the term's index lies in the K-th tail",
				"n₀ ∈ {k:num | N + M₀ ≤ k}",
				By(approach))
			aboveInf := arg.Have(
				"the infimum floors the term, a(n) being in the K-th tail's range",
				"inf(image(a, {n:num | N + M₀ ≤ n})) ≤ a(n₀)",
				By(
					hasInf.At(K),
					inTail,
					set_image.FunInImage.At(a, kthTail, n),
					real_sup_inf.HasInfLowerBound.At(kthRange, tailInf, a.Apply(n))))
			pastN := arg.Have(
				"n ≥ K = N + M ≥ N",
				"N ≤ n₀",
				BySets(inTail, nat_order.LessEqAdd.At(N, M), nat_order.LessEqTrans.At(N, K, n)))

			arg.Take(n)
			arg.Show(
				"L − ε < i(K) ≤ a(n) < L + ε: the term lies within ε of L, past N",
				ByArith(pastN, approach, aboveInf, nearK))
		}),
})}

// WithinReciprocalConverges — a sequence whose n-th term lies within
// 1/(n + 1) of c tends to c.
//
// For ε > 0 the Archimedean property hands over an m with 1/m < ε, and
// past m every 1/(n + 1) lies below 1/m, so the terms past m are within
// ε of c.
var WithinReciprocalConverges = withinReciprocalConvergesThm{family.Add(registry.ProofEntry{
	Name: "WithinReciprocalConverges",
	Key:  "prop_45b3fd9460496d0a",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀c:real.",
		Hypotheses: []string{
			"∀n:num. |a(n) - c| < real_inv(&n + &1)",
		},
		Conclusion: "a ⟶ c",
	},
		func(arg *Argument, a *Arrow[Nat, Real], c *Expr[Real], shrinking Fact) {
			// The goal read as its ε-N statement; the hypothesis does not
			// mention `⟶`, so the unfolding leaves it as it is.
			arg.Do(Unfold(RealConvergesToDef))
			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			m0, small := arg.ObtainAs[Nat](
				"the Archimedean property puts some 1/m, m ≠ 0, strictly between 0 and ε",
				"∃m:num. m ≠ 0 ∧ &0 < real_inv(&m) ∧ real_inv(&m) < ε",
				// The claim restates the right side of the law's ⇔ at ε.
				By(real_archimedean.PosIffExistsSmallInv.At(eps), pos))

			arg.Take(m0)
			n := arg.FixAs[Nat]()
			past := arg.Assume()
			mReal := arg.TermAs[Real]("&m₀")
			below := arg.Have(
				"m ≤ n puts m below n + 1",
				"&m₀ < &n + &1",
				ByArith(past, real_construction.OfNumLessEq.At(m0, n)))
			shrunk := arg.Have(
				"so 1/(n + 1) lies below 1/m, m being positive since 1/m is",
				"real_inv(&n + &1) < real_inv(&m₀)",
				By(
					below,
					small,
					real_order_field.InvPos.At(mReal),
					real_order_field.InvAntitone.At(mReal, arg.TermAs[Real]("&n + &1"))))
			arg.Show(
				"|a(n) − c| < 1/(n + 1) < 1/m < ε",
				ByArith(shrinking.At(n), shrunk, small))
		}),
})}

// ClusterPointSubsequence — a cluster point is the limit of a
// subsequence.
//
// For each k the cluster point hands over, past any index N, a term
// within 1/(k + 1) of l; choosing one for every k and N is a function g.
// Recursion then picks the indices: σ(0) is g's choice at (0, 0), and
// σ(k + 1) its choice at (k + 1, σ(k) + 1) — past σ(k), so σ rises
// strictly. The k-th term of a ∘ σ lies within 1/(k + 1) of l, whether
// k is 0 or a successor, so a ∘ σ tends to l.
var ClusterPointSubsequence = clusterPointSubsequenceThm{family.Add(registry.ProofEntry{
	Name: "ClusterPointSubsequence",
	Key:  "prop_2f6a6429846b6a8c",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀l:real.",
		Hypotheses: []string{
			"real_cluster_point(a, l)",
		},
		Conclusion: "∃σ:(num → num). (∀k:num. σ(k) < σ(k + 1)) ∧ a ∘ σ ⟶ l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], l *Expr[Real], cluster Fact) {
			near := arg.Unfolded(cluster, RealClusterPointDef)
			perIndex := arg.Have(
				"the cluster point read at the radius 1/(k + 1), for each k",
				"∀k N:num. ∃n:num. N ≤ n ∧ |a(n) - l| < real_inv(&k + &1)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					positive := b.Have(
						"1/(k + 1) is a positive radius, k + 1 being positive",
						"&0 < real_inv(&k + &1)",
						ByArith(real_order_field.InvPos.At(b.TermAs[Real]("&k + &1"))))
					b.Show(
						"so past every index some term lies within 1/(k + 1) of l",
						By(near.At(b.TermAs[Real]("real_inv(&k + &1)")), positive))
				}))
			_, choice := arg.Obtain(
				"choosing one such term for every k and every index N is a function; call it g₀",
				"∃g:(num → num → num). ∀k N:num. N ≤ g(k, N) ∧ |a(g(k, N)) - l| < real_inv(&k + &1)",
				By(perIndex))
			sigma, recursion := arg.Obtain(
				"recursion picks the indices: σ(0) = g(0, 0), and σ(k + 1) = g(k + 1, σ(k) + 1)",
				"∃σ:(num → num). σ(0) = g₀(0, 0) ∧ ∀k:num. σ(suc(k)) = g₀(suc(k), σ(k) + 1)",
				By(nat_arith.PrimRecursion.At(
					arg.TermAs[Fun2[Nat, Nat, Nat]]("λp:num. λk:num. g₀(suc(k), p + 1)"),
					arg.TermAs[Nat]("g₀(0, 0)"))))
			next := arg.Have(
				"each next index is g's choice past the previous one",
				"∀k:num. σ₀(suc(k)) = g₀(suc(k), σ₀(k) + 1)",
				By(recursion))

			arg.Take(sigma)
			rises := arg.Have(
				"σ rises strictly",
				"∀k:num. σ₀(k) < σ₀(k + 1)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					past := b.Have(
						"σ(k + 1) is σ(suc k), g's choice past σ(k) + 1",
						"σ₀(k) + 1 ≤ σ₀(k + 1)",
						By(
							choice.At(b.TermAs[Nat]("suc(k)"), b.TermAs[Nat]("σ₀(k) + 1")),
							next.At(k),
							nat_arith.Add1.At(k)))
					b.Show(
						"so σ(k) < σ(k) + 1 ≤ σ(k + 1)",
						ByArith(past))
				}))
			within := arg.Have(
				"the k-th term of a ∘ σ lies within 1/(k + 1) of l",
				"∀k:num. |a(σ₀(k)) - l| < real_inv(&k + &1)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					zeroOrSuccessor := b.Have(
						"k is 0 or a successor",
						"k = 0 ∨ ∃j:num. k = suc(j)",
						By(peano.Cases.At(k)))
					b.Do(zeroOrSuccessor.SplitDisj(
						LeftHolds(
							"k = 0: σ(0) is g's choice at (0, 0)",
							Given(func(c *Argument, zero Fact) {
								origin := c.Ctx().Nat(0)
								c.Show(
									"so its term lies within 1/(0 + 1) of l",
									zero.Rw(),
									By(Normalized, choice.At(origin, origin), recursion))
							})),
						RightHolds(
							"k = suc j: σ(suc j) is g's choice at (suc j, σ(j) + 1)",
							Given(func(c *Argument, successor Fact) {
								j, isSuccessor := c.Unpack(successor)
								c.Show(
									"so its term lies within 1/(suc j + 1) of l",
									isSuccessor.Rw(),
									By(choice.At(c.TermAs[Nat]("suc(j₀)"), c.TermAs[Nat]("σ₀(j₀) + 1")), next.At(j)))
							})),
					))
				}))
			converges := arg.Have(
				"so a ∘ σ ⟶ l, its k-th term a(σ(k)) lying within 1/(k + 1) of l",
				"a ∘ σ₀ ⟶ l",
				// `o` is the constant behind `∘`: unfolded, the k-th term of
				// a ∘ σ is a(σ(k)).
				Unfold(functions.ComposeApply),
				By(within, WithinReciprocalConverges.At(arg.TermAs[Fun[Nat, Real]]("λx:num. a(σ₀(x))"), l)))
			arg.Show(
				"σ rises strictly and a ∘ σ tends to l",
				By(rises, converges))
		}),
})}

// LimitSubsequence — a subsequence of a convergent sequence converges to
// the same limit.
//
// A strictly increasing σ never falls below the identity. So the index
// N₀ that a ⟶ l hands over at ε serves a ∘ σ as well: past it,
// N₀ ≤ k ≤ σ(k), and the k-th term of the subsequence, a(σ(k)), is a
// term of a past N₀, within ε of l.
var LimitSubsequence = limitSubsequenceThm{family.Add(registry.ProofEntry{
	Name: "LimitSubsequence",
	Key:  "prop_3177758884e605c7",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀σ:(num → num). ∀l:real.",
		Hypotheses: []string{
			"∀k:num. σ(k) < σ(k + 1)",
			"a ⟶ l",
		},
		Conclusion: "a ∘ σ ⟶ l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], σ *Arrow[Nat, Nat], l *Expr[Real], given Fact) {
			limit := arg.Have(
				"a ⟶ l",
				"a ⟶ l",
				By(given))
			near := arg.Unfolded(limit, RealConvergesToDef)
			climbs := arg.Have(
				"a strictly increasing σ never falls below the identity",
				"∀k:num. k ≤ σ(k)",
				By(given, nat_order.LessEqStrictlyIncreasing))

			// The goal read as its ε-N statement; `o` is the constant behind
			// `∘`: unfolded, the k-th term of a ∘ σ is a(σ(k)).
			arg.Do(Unfold(RealConvergesToDef), Unfold(functions.ComposeApply))
			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			N0, tail := arg.ObtainAs[Nat](
				"a ⟶ l at ε hands over an index N₀ past which every term of a is within ε of l",
				"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε",
				By(near.At(eps), pos))

			arg.Take(N0)
			k := arg.FixAs[Nat]("k")
			past := arg.Assume()
			beyond := arg.Have(
				"σ(k) lies past N₀: N₀ ≤ k ≤ σ(k)",
				"N₀ ≤ σ(k)",
				By(past, climbs.At(k), nat_order.LessEqTrans.At(N0, k, σ.Apply(k))))
			arg.Show(
				"so a(σ(k)), a term of a past N₀, is within ε of l",
				By(tail.At(σ.Apply(k)), beyond))
		}),
})}

// LimitShift — a sequence and its shift by one have the same limits.
//
// If the shifted sequence settles within ε of l past an index N, then a
// does past N + 1: a term a(n) with n ≥ N + 1 is the shifted sequence's
// term at n − 1, and n − 1 ≥ N. Conversely, the shifted sequence is the
// subsequence a ∘ (k ↦ k + 1), whose indices rise strictly, so it keeps
// every limit of a.
var LimitShift = limitShiftThm{family.Add(registry.ProofEntry{
	Name: "LimitShift",
	Key:  "prop_4948a8e9af2ae91d",
	Build: family.Theorem("∀a:(num → real). ∀l:real. (λn:num. a(n + 1)) ⟶ l ⇔ a ⟶ l",
		func(arg *Argument, a *Arrow[Nat, Real], l *Expr[Real]) {
			arg.Iff()

			arg.Forward(
				"the shifted sequence's index, moved on by one, serves a",
				func(b *Argument, shifted Fact) {
					near := b.Unfolded(shifted, RealConvergesToDef)

					// The goal read as its ε-N statement.
					b.Do(Unfold(RealConvergesToDef))
					eps := b.FixAs[Real]()
					pos := b.Assume()
					// The witness is spelled by its binder, N, in the texts below.
					_, tail := b.ObtainAs[Nat](
						"the shifted sequence at ε hands over an index N past which every a(n + 1) is within ε of l",
						"∃N:num. ∀n:num. N ≤ n ⇒ |a(n + 1) - l| < ε",
						By(near.At(eps), pos))

					b.Take(b.TermAs[Nat]("N + 1"))
					b.FixAs[Nat]()
					past := b.Assume()
					previous := b.TermAs[Nat]("n - 1")
					previousPast := b.Have(
						"n − 1 lies past N, n lying past N + 1",
						"N ≤ n - 1",
						ByArith(past))
					successor := b.Have(
						"and n, being positive, is (n − 1) + 1",
						"n - 1 + 1 = n",
						ByArith(past))
					b.Show(
						"so a(n), the shifted sequence's term at n − 1, is within ε of l",
						// Normalized: (n − 1) + 1 = n rewrites that term, a((n − 1) + 1),
						// to a(n).
						By(Normalized, tail.At(previous), previousPast, successor))
				})

			// The subsequence half is the Backward branch: the statement
			// names the shifted sequence first, so its ⇐ is a ⟶ l ⇒ shift ⟶ l.
			arg.Backward(
				"the shifted sequence is a subsequence of a, so it keeps a's limit",
				func(b *Argument, limit Fact) {
					shift := b.TermAs[Fun[Nat, Nat]]("λk:num. k + 1")
					rises := b.Have(
						"the indices k + 1 rise strictly",
						"∀k:num. k + 1 < k + 1 + 1",
						ByArith())
					b.Show(
						"so a ∘ (k ↦ k + 1), which is the shifted sequence, tends to l",
						// Normalized: the definition of ∘ rewrites a ∘ (k ↦ k + 1)
						// to the shifted sequence λn. a(n + 1).
						By(Normalized, rises, limit, LimitSubsequence.At(a, shift, l), functions.ComposeApply.At(a, shift)))
				})
		}),
})}

// BolzanoWeierstrass — every bounded sequence has a convergent
// subsequence: the classical sentence, the corollary of
// BoundedClusterPoint and ClusterPointSubsequence.
//
// The upper limit L of a bounded sequence — the infimum of its tail
// suprema — is a cluster point of it, and a cluster point is the limit
// of a subsequence whose indices rise strictly. That subsequence and L
// answer the statement.
var BolzanoWeierstrass = bolzanoWeierstrassThm{family.Add(registry.ProofEntry{
	Name: "BolzanoWeierstrass",
	Key:  "prop_6ae1058a5caca737",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "∃σ:(num → num). ∃l:real. (∀k:num. σ(k) < σ(k + 1)) ∧ a ∘ σ ⟶ l",
	},
		func(arg *Argument, a *Arrow[Nat, Real], B *Expr[Real], bounded Fact) {
			L := arg.TermAs[Real]("real_limsup(a)")
			cluster := arg.Have(
				"the upper limit L = real_limsup(a) is a cluster point of a bounded sequence",
				"real_cluster_point(a, real_limsup(a))",
				By(bounded, BoundedClusterPoint.At(a, B)))
			sigma, subsequence := arg.Obtain(
				"and a cluster point is the limit of a subsequence, its indices rising strictly",
				"∃σ:(num → num). (∀k:num. σ(k) < σ(k + 1)) ∧ a ∘ σ ⟶ real_limsup(a)",
				By(cluster, ClusterPointSubsequence.At(a, L)))

			arg.Take(sigma)
			arg.Take(L)
			arg.Show(
				"σ rises strictly and a ∘ σ tends to L",
				By(subsequence))
		}),
})}
