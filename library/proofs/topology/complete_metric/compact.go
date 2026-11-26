// compact.go — compact metric spaces: compactness is sequential
// compactness, total boundedness is the existence of Cauchy
// subsequences, and so compactness is completeness with total
// boundedness; an open cover of a compact space has a Lebesgue number,
// and so a continuous map out of a compact space is uniformly
// continuous.

package complete_metric

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Subsequences
// ---------------------------------------------------------------------------

// IncreasingSelection — infinitely many indices at every level can be
// threaded by a strictly increasing sequence: one index from each level,
// each past the one before.
//
// An infinite set of indices holds indices past every bound, those at or
// below a bound being finitely many; choosing one past m in each infinite
// K is a function next. Recursion then picks σ(0) = next(J(0), 0) and
// σ(j + 1) = next(J(j + 1), σ(j)): each lies in its level, and past the
// one before.
var IncreasingSelection = increasingSelectionThm{family.Add(registry.ProofEntry{
	Name: "IncreasingSelection",
	Key:  "prop_8dedcebeaef94f32",
	Build: family.Theorem(Statement{
		Binders: "∀J:(num → set(num)).",
		Hypotheses: []string{
			"∀j:num. infinite(J(j))",
		},
		Conclusion: "∃σ:(num → num). (∀j:num. σ(j) < σ(j + 1)) ∧ (∀j:num. σ(j) ∈ J(j))",
	},
		func(a *Argument, J *Arrow[Nat, Set[Nat]], infinitely Fact) {
			beyond := a.Have(
				"an infinite set of indices holds indices past every bound",
				"∀K:set(num). ∀m:num. infinite(K) ⇒ ∃k:num. k ∈ K ∧ m < k",
				Derive(func(b *Argument) {
					K := b.FixAs[Set[Nat]]("K")
					m := b.FixAs[Nat]("m")
					infinite := b.Assume()
					bounded := b.SupposeNot()
					below := b.Have(
						"then every index of K is at most m",
						"K ⊆ {x:num | x ≤ m}",
						BySets(bounded, nat_order.NotLessThan))
					b.Show(
						"so K would be finite, the indices at most m being finitely many",
						By(
							infinite,
							below,
							finite_set.InfiniteDef,
							finite_set.FiniteSubset.At(K, b.TermAs[Set[Nat]]("{x:num | x ≤ m}")),
							num_segment.FiniteBelow.At(m)))
				}))
			_, next := a.ObtainAs[Fun2[Set[Nat], Nat, Nat]](
				"choosing, in each infinite K and past each bound m, an index of K is a function next",
				"∃next:(set(num) → num → num). ∀K:set(num). ∀m:num. infinite(K) ⇒ next(K, m) ∈ K ∧ m < next(K, m)",
				By(beyond))
			σ, recursion := a.ObtainAs[Fun[Nat, Nat]](
				"recursion picks σ(0) = next(J(0), 0) and σ(j + 1) = next(J(j + 1), σ(j))",
				"∃σ:(num → num). σ(0) = next(J(0), 0) ∧ ∀j:num. σ(j + 1) = next(J(j + 1), σ(j))",
				By(
					peano.Recursion.At(
						a.TermAs[Fun2[Nat, Nat, Nat]]("λp:num. λj:num. next(J(j + 1), p)"),
						a.TermAs[Nat]("next(J(0), 0)")),
					nat_arith.Add1))
			steps := a.Conjuncts(
				recursion,
				"σ(0) is next's choice in J(0)",
				"σ(j + 1) is next's choice in J(j + 1) past σ(j)")
			a.Take(σ)
			a.Do(SplitConj(
				Case(
					"σ rises strictly, each index chosen past the one before",
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						b.Show(
							"σ(j + 1) is chosen in J(j + 1) past σ(j)",
							By(
								steps[1].At(j),
								next.At(b.TermAs[Set[Nat]]("J(j + 1)"), b.TermAs[Nat]("σ(j)")),
								infinitely.At(b.TermAs[Nat]("j + 1"))))
					})),
				Case(
					"each index lies in its level",
					Derive(func(b *Argument) {
						b.Induct("j")
						b.Base(
							"σ(0) is chosen in J(0)",
							By(
								Normalized,
								steps[0],
								next.At(b.TermAs[Set[Nat]]("J(0)"), b.TermAs[Nat]("0")),
								infinitely.At(b.TermAs[Nat]("0"))))
						b.Step(
							"σ(j + 1) is chosen in J(j + 1)",
							func(c *Argument, _ Fact) {
								j := c.TermAs[Nat]("j")
								c.Show(
									"next's choice in J(j + 1) lies in it",
									By(
										steps[1].At(j),
										next.At(c.TermAs[Set[Nat]]("J(j + 1)"), c.TermAs[Nat]("σ(j)")),
										infinitely.At(c.TermAs[Nat]("j + 1")),
										nat_arith.Add1.At(j)))
							})
					})),
			))
		}),
})}

// ClusterPointSubsequence — a cluster point of a sequence, every ball about
// which holds terms past every index, is the limit of a subsequence.
//
// The distances of the terms from l form a sequence of reals of which 0 is
// a cluster point, so a subsequence of them tends to 0
// (real_sequences.ClusterPointSubsequence) — which is the convergence of
// the same subsequence of terms to l.
var ClusterPointSubsequence = clusterPointSubsequenceThm{family.Add(registry.ProofEntry{
	Name: "ClusterPointSubsequence",
	Key:  "prop_ada782aec65fbca5",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:(num → A). ∀l:A.",
		Hypotheses: []string{
			"metric_space(M, d)",
			"∀n:num. x(n) ∈ M",
			"l ∈ M",
			"∀r:real. &0 < r ⇒ ∀N:num. ∃n:num. N ≤ n ∧ d(x(n), l) < r",
		},
		Conclusion: "∃σ:(num → num). (∀j:num. σ(j) < σ(j + 1)) ∧ metric_converges_to(M, d, x ∘ σ, l)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			x *Arrow[Nat, A],
			terms Fact,
			l *Expr[A],
			inM, cluster Fact,
		) {
			lm := a.MemberOf[on.M](l, inM)
			distances := a.TermAs[Fun[Nat, Real]]("λn:num. d(x(n), l)")
			zero := a.TermAs[Real]("&0")
			clusterAtZero := a.Have(
				"0 is a cluster point of the distances of the terms from l",
				"real_cluster_point(λn:num. d(x(n), l), &0)",
				Unfold(real_sequences.RealClusterPointDef),
				Derive(func(b *Argument) {
					eps := b.FixAs[Real]()
					pos := b.Assume()
					N := b.FixAs[Nat]("N")
					n, near := b.ObtainAs[Nat](
						"past N some term lies within ε of l",
						"∃n:num. N ≤ n ∧ d(x(n), l) < ε",
						By(cluster.At(eps, N), pos))
					b.Take(n)
					xn := b.MemberOf[on.M](x.Apply(n), terms.At(n))
					b.Show(
						"its distance from l is at least 0 and below ε",
						ByArith(near, metric_space.DistNonneg.Read(metric).At(xn, lm)))
				}))
			σ, subsequence := a.UnpackAs[Fun[Nat, Nat]](
				GroupPremises(clusterAtZero, real_sequences.ClusterPointSubsequence.At(distances, zero)),
				"σ")
			sub := a.Conjuncts(
				subsequence,
				"σ is strictly increasing",
				"the distances of the subsequence's terms from l tend to 0")
			// `o` is the constant behind `∘`: unfolded, the j-th term of a
			// subsequence is the σ(j)-th term of the sequence.
			shrinking := a.Unfolded(
				a.Unfolded(sub[1], real_sequences.RealConvergesToDef), functions.ComposeApply)
			a.Take(σ)
			a.Do(SplitConj(
				Case(
					"σ is strictly increasing",
					By(sub[0])),
				Case(
					"x ∘ σ converges to l, the distances of its terms from l tending to 0",
					Derive(func(b *Argument) {
						b.Do(Unfold(MetricConvergesToDef), Unfold(functions.ComposeApply))
						b.Do(SplitConjAll(
							Case(
								"l is a point of M",
								By(inM)),
							Case(
								"every term is a point of M",
								By(terms)),
							Case(
								"past some index every term is within ε of l",
								Derive(func(c *Argument) {
									eps := c.FixAs[Real]()
									pos := c.Assume()
									K, tail := c.ObtainAs[Nat](
										"past some index K the distances are below ε",
										"∃K:num. ∀n:num. K ≤ n ⇒ |d(x(σ(n)), l) - &0| < ε",
										By(shrinking.At(eps), pos))
									c.Take(K)
									n := c.FixAs[Nat]()
									past := c.Assume()
									c.Show(
										"so d(x(σ(n)), l) < ε",
										ByArith(tail.At(n), past))
								})),
						))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Total boundedness by sequences
// ---------------------------------------------------------------------------

// TotallyBoundedImpBounded — a totally bounded set is bounded.
//
// At distance 1 total boundedness hands over finitely many points of s,
// a set k, within 1 of every point of s. The balls of radius 1 about them
// are finitely many, each a ball about a point of M and so bounded; their
// union is bounded, and s lies in it.
var TotallyBoundedImpBounded = totallyBoundedImpBoundedThm{family.Add(registry.ProofEntry{
	Name: "TotallyBoundedImpBounded",
	Key:  "prop_5e9a352b0f1a9a3f",
	Build: metric_space.MetricSpace.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"totally_bounded(s)",
		},
		Conclusion: "metric_bounded(s)",
		Abbrev: Abbrev{
			{Name: "unitBalls", Text: "{ball(x, &1) | x:A | x ∈ k}"},
		},
	},
		func(a *Argument, metric metric_space.MetricSpaceFact[on.M], s *Expr[Set[A]], bounded Fact) {
			parts := a.Conjuncts(
				a.Unfolded(bounded, TotallyBoundedDef),
				"s lies in M",
				"for every positive distance finitely many points of s come within it of every point of s")
			k, net := a.ObtainAs[Set[A]](
				"at distance 1, finitely many points of s, a set k, come within 1 of every point of s",
				"∃k:set(A). finite(k) ∧ k ⊆ s ∧ ∀y:A. y ∈ s ⇒ ∃x:A. x ∈ k ∧ d(x, y) < &1",
				By(parts[1].At(a.TermAs[Real]("&1"))))
			held := a.Conjuncts(
				net,
				"k is finite",
				"k lies in s",
				"every point of s lies within 1 of a point of k")
			kInM := a.Have(
				"k lies in M, s lying in M",
				"k ⊆ M",
				BySets(held[1], parts[0]))
			unitBall := a.TermAs[Fun[A, Set[A]]]("λx:A. ball(x, &1)")
			finitely := a.Have(
				"the balls of radius 1 about the points of k are finitely many, the image of the finite k",
				"finite(«unitBalls»)",
				By(held[0], finite_set.FiniteImage.At(unitBall, k), set_image.SimpleImage.At(unitBall, k)))
			each := a.Have(
				"each of them is a ball about a point of M, and so bounded",
				"∀u:set(A). u ∈ «unitBalls» ⇒ metric_bounded(u)",
				BySets(kInM, metric_space.BallBounded.Read(metric)))
			union := a.Have(
				"finitely many bounded sets unite to a bounded set",
				"metric_bounded(⋃«unitBalls»)",
				By(
					metric_space.BoundedUnions.Read(metric).At(a.TermAs[Set[Set[A]]]("«unitBalls»")),
					finitely,
					each))
			covered := a.Have(
				"the balls cover s: a point y of s lies within 1 of a point c of k, so in the ball about c",
				"s ⊆ ⋃«unitBalls»",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					inS := b.Assume()
					_, near := b.ObtainAs[A](
						"y lies within 1 of some point c of k",
						"∃c:A. c ∈ k ∧ d(c, y) < &1",
						By(held[2].At(y), inS))
					centre := b.Conjuncts(
						near,
						"c is a point of k",
						"y lies within 1 of c")
					inBall := b.Have(
						"y, a point of M, lies in the ball of radius 1 about c",
						"y ∈ ball(c, &1)",
						BySets(centre[1], inS, parts[0], metric_space.BallDef))
					b.Show(
						"so y lies in the union of the balls",
						BySets(centre[0], inBall))
				}))
			a.Show(
				"and s lies in that union",
				By(metric_space.BoundedSubset, union, covered))
		}),
})}

// TotallyBoundedRefine — of infinitely many terms of a sequence of a
// totally bounded set, infinitely many lie within any positive distance
// of one point of the set.
//
// Finitely many points of s, a set k, come within r of every point of s;
// choosing for each index a point of k within r of its term is a map f
// into k. On the infinitely many indices of I it takes finitely many
// values, so one value f(i) is taken infinitely often
// (finite_set.FiniteImageInfinite), and the indices taking it put their
// terms within r of f(i).
var TotallyBoundedRefine = totallyBoundedRefineThm{family.Add(registry.ProofEntry{
	Name: "TotallyBoundedRefine",
	Key:  "prop_1fc985470274c012",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀s:set(A). ∀x:(num → A). ∀I:set(num). ∀r:real.",
		Hypotheses: []string{
			"totally_bounded(M, d, s)",
			"∀n:num. x(n) ∈ s",
			"infinite(I)",
			"&0 < r",
		},
		Conclusion: "∃J:set(num). J ⊆ I ∧ infinite(J) ∧ (∃c:A. c ∈ s ∧ (∀n:num. n ∈ J ⇒ d(c, x(n)) < r))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			s *Expr[Set[A]],
			bounded Fact,
			x *Arrow[Nat, A],
			terms Fact,
			I *Expr[Set[Nat]],
			infinitely Fact,
			r *Expr[Real],
			positive Fact,
		) {
			nets := a.Conjuncts(
				a.Unfolded(bounded, TotallyBoundedDef),
				"s lies in M",
				"for every positive distance finitely many points of s come within it of every point of s")
			k, near := a.ObtainAs[Set[A]](
				"at distance r, finitely many points of s, a set k, come within r of every point of s",
				"∃k:set(A). finite(k) ∧ k ⊆ s ∧ (∀y:A. y ∈ s ⇒ ∃c:A. c ∈ k ∧ d(c, y) < r)",
				By(nets[1].At(r), positive))
			net := a.Conjuncts(
				near,
				"k is finite",
				"k lies in s",
				"every point of s lies within r of a point of k")
			f, chosen := a.ObtainAs[Fun[Nat, A]](
				"choosing for each index a point of k within r of its term is a map f into k",
				"∃f:(num → A). ∀n:num. f(n) ∈ k ∧ d(f(n), x(n)) < r",
				By(net[2], terms))
			values := a.Have(
				"the values f takes on I lie in k",
				"image(f, I) ⊆ k",
				By(chosen, set_image.ImageSubsetIff))
			_, fibre := a.ObtainAs[Nat](
				"on the infinitely many indices of I, f takes finitely many "+
					"values, so its value at some index i of I infinitely often",
				"∃i:num. i ∈ I ∧ infinite({n:num | n ∈ I ∧ f(n) = f(i)})",
				By(
					infinitely,
					values,
					net[0],
					finite_set.FiniteImageInfinite.At(f, I),
					finite_set.FiniteSubset.At(a.TermAs[Set[A]]("image(f, I)"), k)))
			shared := a.Conjuncts(
				fibre,
				"i is an index of I",
				"infinitely many indices of I share f's value at i")
			a.Take(a.TermAs[Set[Nat]]("{n:num | n ∈ I ∧ f(n) = f(i)}"))
			a.Do(SplitConj(
				Case(
					"the indices sharing f's value at i lie in I, and are infinitely many",
					BySets(shared[1])),
				Case(
					"and put their terms within r of f(i), a point of s",
					Derive(func(b *Argument) {
						b.Take(b.TermAs[A]("f(i)"))
						b.Show(
							"f(i) lies in k, so in s, and d(f(i), x(n)) is d(f(n), x(n)) < r at an index n sharing it",
							BySets(chosen, net[1]))
					})),
			))
		}),
})}

// SeparatedSequence — a set that no finitely many of its points come
// within ε of holds a sequence of points pairwise at least ε apart.
//
// Each finite subset of s leaves a point of s at least ε from all of its
// points; choosing one for each finite subset is a function g. Recursion
// gathers the chosen points in finite sets, K(0) = ∅ and K(n + 1) adding
// g(K(n)) to K(n), each a finite subset of s; the n-th term is g(K(n)). An
// earlier term g(K(m)), m < n, lies in K(n), and g(K(n)) is at least ε
// from every point of K(n).
var SeparatedSequence = separatedSequenceThm{family.Add(registry.ProofEntry{
	Name: "SeparatedSequence",
	Key:  "prop_32a5a12f9761fb5d",
	Build: family.Theorem(Statement{
		Binders: "∀d:(A → A → real). ∀s:set(A). ∀ε:real.",
		Hypotheses: []string{
			"¬(∃k:set(A). finite(k) ∧ k ⊆ s ∧ (∀y:A. y ∈ s ⇒ ∃x:A. x ∈ k ∧ d(x, y) < ε))",
		},
		Conclusion: "∃x:(num → A). (∀n:num. x(n) ∈ s) ∧ (∀m n:num. m < n ⇒ ε ≤ d(x(m), x(n)))",
	},
		func(a *Argument, d *Expr[Fun2[A, A, Real]], s *Expr[Set[A]], ε *Expr[Real], noNet Fact) {
			away := a.Have(
				"each finite subset k of s leaves a point of s at least ε from all of its points",
				"∀k:set(A). finite(k) ∧ k ⊆ s ⇒ ∃y:A. y ∈ s ∧ (∀z:A. z ∈ k ⇒ ε ≤ d(z, y))",
				By(noNet, real_order_ring.NotLessThan))
			_, choice := a.ObtainAs[Fun[Set[A], A]](
				"choosing one such point for each finite subset of s is a function g",
				"∃g:(set(A) → A). ∀k:set(A). finite(k) ∧ k ⊆ s ⇒ g(k) ∈ s ∧ (∀z:A. z ∈ k ⇒ ε ≤ d(z, g(k)))",
				By(away))
			_, recursion := a.ObtainAs[Fun[Nat, Set[A]]](
				"recursion gathers the chosen points: K(0) = ∅, and K(n + 1) adds g(K(n)) to K(n)",
				"∃K:(num → set(A)). K(0) = ∅ ∧ ∀n:num. K(n + 1) = insert(g(K(n)), K(n))",
				By(
					peano.Recursion.At(
						a.TermAs[Fun2[Set[A], Nat, Set[A]]]("λt:set(A). λn:num. insert(g(t), t)"),
						a.TermAs[Set[A]]("∅")),
					nat_arith.Add1))
			gather := a.Conjuncts(
				recursion,
				"K(0) is empty",
				"K(n + 1) adds g(K(n)) to K(n)")
			finitelyIn := a.Have(
				"each K(n) is a finite subset of s",
				"∀n:num. finite(K(n)) ∧ K(n) ⊆ s",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"K(0) is empty",
						BySets(gather[0], finite_set.FiniteRules))
					b.Step(
						"K(n + 1) adds a point of s to a finite subset of s",
						func(c *Argument, ih Fact) {
							point := c.Have(
								"g(K(n)) is a point of s, K(n) being a finite subset of s",
								"g(K(n)) ∈ s",
								By(ih, choice.At(c.TermAs[Set[A]]("K(n)"))))
							c.Do(Simp(Fwd(nat_arith.Add1)))
							c.Do(gather[1].At(c.TermAs[Nat]("n")).Rw())
							c.Show(
								"so K(n) with g(K(n)) added is a finite subset of s",
								BySets(ih, point, finite_set.FiniteInsert))
						})
				}))
			earlier := a.Have(
				"each point chosen earlier lies in K(n)",
				"∀n m:num. m < n ⇒ g(K(m)) ∈ K(n)",
				Derive(func(b *Argument) {
					b.Induct("n")
					b.Base(
						"no index lies below 0",
						By(nat_order.LessThanZeroClause))
					b.Step(
						"an index below n + 1 is n, whose point K(n + 1) adds, or below n, its point lying in K(n)",
						func(c *Argument, ih Fact) {
							c.Do(Simp(Fwd(nat_arith.Add1)))
							c.Do(gather[1].At(c.TermAs[Nat]("n")).Rw())
							c.Show(
								"K(n + 1) holds K(n) and g(K(n))",
								BySets(ih, nat_order.LessThanSucClause, nat_arith.Add1))
						})
				}))
			a.Take(a.TermAs[Fun[Nat, A]]("λn:num. g(K(n))"))
			a.Do(SplitConj(
				Case(
					"each term is a point of s",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"g(K(n)) is chosen in s, K(n) being a finite subset of s",
							By(choice.At(b.TermAs[Set[A]]("K(n)")), finitelyIn.At(n)))
					})),
				Case(
					"a later term is at least ε from an earlier one",
					Derive(func(b *Argument) {
						m := b.FixAs[Nat]("m")
						n := b.FixAs[Nat]("n")
						before := b.Assume()
						b.Show(
							"g(K(m)) lies in K(n), and g(K(n)) is at least ε from every point of K(n)",
							By(earlier.At(n, m), before, choice.At(b.TermAs[Set[A]]("K(n)")), finitelyIn.At(n)))
					})),
			))
		}),
})}

// TotallyBoundedSequential — a subset is totally bounded exactly when every
// sequence of its points has a Cauchy subsequence.
//
// Forward: the indices are refined level by level (TotallyBoundedRefine).
// I(0) holds every index, and I(n + 1) is an infinite part of I(n) whose
// terms lie within 1/(n + 1) of one point of s. A strictly increasing σ
// picks an index from each I(j + 1) (IncreasingSelection). Past N every
// σ(j) lies in I(N + 1), the levels decreasing, so any two of those terms
// lie within 2/(N + 1) of each other, through the point of that level —
// below ε once 1/N is below ε/2. Backward: were some ε to admit no finite
// net, a sequence of points pairwise at least ε apart would exist
// (SeparatedSequence), and no subsequence of it is Cauchy: past any index
// two of its terms are still ε apart.
var TotallyBoundedSequential = totallyBoundedSequentialThm{family.Add(registry.ProofEntry{
	Name: "TotallyBoundedSequential",
	Key:  "prop_16317056eecea76f",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀s:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
		},
		Conclusion: "totally_bounded(M, d, s) ⇔ " +
			"s ⊆ M ∧ " +
			"(∀x:(num → A). " +
			"    (∀n:num. x(n) ∈ s) ⇒ ∃σ:(num → num). (∀j:num. σ(j) < σ(j + 1)) ∧ metric_cauchy(M, d, x ∘ σ))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			s *Expr[Set[A]],
		) {
			a.Iff()

			a.Forward(
				"refining the indices level by level, one index from each level makes a Cauchy subsequence",
				func(b *Argument, bounded Fact) {
					nets := b.Conjuncts(
						b.Unfolded(bounded, TotallyBoundedDef),
						"s lies in M",
						"for every positive distance finitely many points of s come within it of every point of s")
					b.Do(SplitConj(
						Case(
							"s lies in M",
							By(nets[0])),
						Case(
							"every sequence of points of s has a Cauchy subsequence",
							Derive(func(c *Argument) {
								x := c.FixAs[Fun[Nat, A]]("x")
								terms := c.Assume()
								inM := c.Have(
									"every term is a point of M, s lying in M",
									"∀k:num. x(k) ∈ M",
									BySets(terms, nets[0]))
								refinable := c.Have(
									"at each level n, an infinite I has an infinite part "+
										"whose terms lie within 1/(n + 1) of a point of s",
									Statement{
										Binders: "∀I:set(num). ∀n:num.",
										Hypotheses: []string{
											"infinite(I)",
										},
										Conclusion: "∃J:set(num). " +
											"    J ⊆ I ∧ infinite(J) ∧ (∃p:A. p ∈ s ∧ (∀k:num. k ∈ J ⇒ d(p, x(k)) < real_inv(&n + &1)))",
									},
									Derive(func(e *Argument) {
										I := e.FixAs[Set[Nat]]("I")
										e.FixAs[Nat]("n")
										infinite := e.Assume()
										positive := e.Have(
											"1/(n + 1) is a positive radius",
											"&0 < real_inv(&n + &1)",
											ByArith(real_order_field.InvPos.At(e.TermAs[Real]("&n + &1"))))
										e.Show(
											"refining I at that radius gives such a part",
											By(
												bounded,
												terms,
												infinite,
												positive,
												TotallyBoundedRefine.At(M, d, s, x, I, e.TermAs[Real]("real_inv(&n + &1)"))))
									}))
								// R(I, n) chooses, in an infinite I, an infinite part whose terms lie
								// within 1/(n + 1) of one point of s.
								R, refinement := c.ObtainAs[Fun2[Set[Nat], Nat, Set[Nat]]](
									"one such part chosen for every infinite I and every level n",
									"∃R:(set(num) → num → set(num)). ∀I:set(num). ∀n:num. "+
										"    infinite(I) ⇒ "+
										"    R(I, n) ⊆ I ∧ "+
										"    infinite(R(I, n)) ∧ "+
										"    (∃p:A. p ∈ s ∧ (∀k:num. k ∈ R(I, n) ⇒ d(p, x(k)) < real_inv(&n + &1)))",
									By(refinable))
								I, levels := c.ObtainAs[Fun[Nat, Set[Nat]]](
									"the levels: I(0) holds every index, and I(n + 1) is R(I(n), n)",
									"∃I:(num → set(num)). I(0) = 𝕌 ∧ (∀n:num. I(n + 1) = R(I(n), n))",
									By(peano.Recursion.At(R, c.TermAs[Set[Nat]]("𝕌")), nat_arith.Add1))
								level := c.Conjuncts(
									levels,
									"I(0) holds every index",
									"I(n + 1) refines I(n)")
								infiniteLevels := c.Have(
									"every level is infinite",
									"∀n:num. infinite(I(n))",
									Derive(func(e *Argument) {
										e.Induct("n")
										e.Base(
											"I(0) holds every index, infinitely many",
											By(level[0], num_segment.Infinite))
										e.Step(
											"R keeps infinitely many indices of an infinite level",
											func(g *Argument, ih Fact) {
												n := g.TermAs[Nat]("n")
												g.Do(Simp(Fwd(nat_arith.Add1)))
												g.Show(
													"I(n + 1) is R(I(n), n), infinite as I(n) is",
													By(Normalized, ih, level[1].At(n), refinement.At(g.TermAs[Set[Nat]]("I(n)"), n)))
											})
									}))
								shrink := c.Have(
									"each level lies in the one before, and its terms lie within 1/(n + 1) of one point of s",
									"∀n:num. I(n + 1) ⊆ I(n) ∧ (∃p:A. p ∈ s ∧ (∀k:num. k ∈ I(n + 1) ⇒ d(p, x(k)) < real_inv(&n + &1)))",
									Derive(func(e *Argument) {
										n := e.FixAs[Nat]("n")
										e.Show(
											"I(n + 1) is R(I(n), n), and I(n) is infinite",
											By(Normalized, level[1].At(n), refinement.At(e.TermAs[Set[Nat]]("I(n)"), n), infiniteLevels.At(n)))
									}))
								decreasing := c.Have(
									"the levels decrease all the way: I(n) lies in I(m) whenever m ≤ n",
									"∀n m:num. m ≤ n ⇒ I(n) ⊆ I(m)",
									By(shrink, At(order.DecreasingFromSteps, I)))
								_, selection := c.ObtainAs[Fun[Nat, Nat]](
									"a strictly increasing σ picks an index from each level I(j + 1)",
									"∃σ:(num → num). (∀j:num. σ(j) < σ(j + 1)) ∧ (∀j:num. σ(j) ∈ I(j + 1))",
									By(infiniteLevels, IncreasingSelection.At(c.TermAs[Fun[Nat, Set[Nat]]]("λj:num. I(j + 1)"))))
								picked := c.Conjuncts(
									selection,
									"σ is strictly increasing",
									"σ(j) lies in the level I(j + 1)")
								c.Take(c.TermAs[Fun[Nat, Nat]]("σ"))
								c.Do(SplitConj(
									Case(
										"σ is strictly increasing",
										By(picked[0])),
									Case(
										"x ∘ σ is Cauchy: past N its terms lie in level N + 1, within 2/(N + 1) of each other",
										Derive(func(e *Argument) {
											e.Do(Unfold(MetricCauchyDef), Unfold(functions.ComposeApply))
											e.Do(SplitConj(
												Case(
													"every term x(σ(j)) is a point of M",
													By(inM)),
												Case(
													"past some N any two terms are within ε of each other",
													Derive(func(g *Argument) {
														g.FixAs[Real]()
														pos := g.Assume()
														half := g.Have(
															"ε/2 is positive",
															"&0 < ε / &2",
															ByArith(pos))
														N, small := g.ObtainAs[Nat](
															"the Archimedean property puts some 1/N, N ≠ 0, between 0 and ε/2",
															"∃N:num. N ≠ 0 ∧ &0 < real_inv(&N) ∧ real_inv(&N) < ε / &2",
															By(real_archimedean.PosIffExistsSmallInv.At(g.TermAs[Real]("ε / &2")), half))
														below := g.Conjuncts(
															small,
															"N is not 0",
															"1/N is positive",
															"1/N is below ε/2")
														radius := g.Have(
															"so 1/(N + 1) lies below 1/N, N being positive since 1/N is",
															"real_inv(&N + &1) < real_inv(&N)",
															ByArith(
																below[1],
																real_order_field.InvPos.At(g.TermAs[Real]("&N")),
																real_order_field.InvAntitone.At(g.TermAs[Real]("&N"), g.TermAs[Real]("&N + &1"))))
														centred := g.Conjuncts(
															shrink.At(N),
															"level N + 1 lies in level N",
															"the terms of level N + 1 lie within 1/(N + 1) of one point of s")
														p, centre := g.UnpackAs[A](centred[1], "p")
														around := g.Conjuncts(
															centre,
															"p is a point of s",
															"the terms of level N + 1 lie within 1/(N + 1) of p")
														pm := g.MemberOf[on.M](p, g.Have(
															"p is a point of M, s lying in M",
															"p ∈ M",
															BySets(around[0], nets[0])))
														g.Take(N)
														i := g.FixAs[Nat]("i")
														j := g.FixAs[Nat]("j")
														past := g.Conjuncts(
															g.Assume(),
															"i is past N",
															"j is past N")
														σi := g.TermAs[Nat]("σ(i)")
														σj := g.TermAs[Nat]("σ(j)")
														inLevel := g.Have(
															"σ(i) and σ(j) lie in their levels i + 1 and j + 1, which lie in level N + 1",
															"σ(i) ∈ I(N + 1) ∧ σ(j) ∈ I(N + 1)",
															ByArith(
																picked[1].At(i),
																picked[1].At(j),
																past[0],
																past[1],
																decreasing.At(g.TermAs[Nat]("i + 1"), g.TermAs[Nat]("N + 1")),
																decreasing.At(g.TermAs[Nat]("j + 1"), g.TermAs[Nat]("N + 1")),
																set_basic.SubsetDef))
														levelParts := g.Conjuncts(
															inLevel,
															"σ(i) lies in level N + 1",
															"σ(j) lies in level N + 1")
														xi := g.MemberOf[on.M](g.TermAs[A]("x(σ(i))"), inM.At(σi))
														xj := g.MemberOf[on.M](g.TermAs[A]("x(σ(j))"), inM.At(σj))
														g.Show(
															"x(σ(i)) and x(σ(j)) are each within 1/(N + 1) < 1/N < ε/2 of p",
															ByArith(
																around[1].At(σi),
																around[1].At(σj),
																levelParts[0],
																levelParts[1],
																radius,
																below[2],
																metric_space.DistTriangle.Read(metric).At(xi, pm, xj),
																metric_space.DistSym.Read(metric).At(xi, pm)))
													})),
											))
										})),
								))
							})),
					))
				})

			a.Backward(
				"were some ε to admit no finite net, a sequence of points ε apart would have no Cauchy subsequence",
				func(b *Argument, sequential Fact) {
					keeps := b.Conjuncts(
						sequential,
						"s lies in M",
						"every sequence of points of s has a Cauchy subsequence")
					b.Do(Unfold(TotallyBoundedDef))
					b.Do(SplitConj(
						Case(
							"s lies in M",
							By(keeps[0])),
						Case(
							"every positive distance has a finite net of points of s",
							Derive(func(c *Argument) {
								ε := c.FixAs[Real]()
								pos := c.Assume()
								noNet := c.SupposeNot()
								x, separated := c.ObtainAs[Fun[Nat, A]](
									"then some sequence x of points of s has its terms pairwise at least ε apart",
									"∃x:(num → A). (∀n:num. x(n) ∈ s) ∧ (∀m n:num. m < n ⇒ ε ≤ d(x(m), x(n)))",
									By(noNet, SeparatedSequence.At(d, s, ε)))
								apart := c.Conjuncts(
									separated,
									"every term is a point of s",
									"a later term is at least ε from an earlier one")
								_, subsequence := c.ObtainAs[Fun[Nat, Nat]](
									"x has a Cauchy subsequence x ∘ σ",
									"∃σ:(num → num). (∀j:num. σ(j) < σ(j + 1)) ∧ metric_cauchy(M, d, x ∘ σ)",
									By(keeps[1].At(x), apart[0]))
								sub := c.Conjuncts(
									subsequence,
									"σ is strictly increasing",
									"x ∘ σ is Cauchy")
								cauchy := c.Conjuncts(
									c.Unfolded(c.Unfolded(sub[1], MetricCauchyDef), functions.ComposeApply),
									"every term of the subsequence is a point of M",
									"every positive distance holds any two terms of the subsequence past some index")
								N, pairs := c.ObtainAs[Nat](
									"at ε, past some index N any two terms of the subsequence are within ε of each other",
									"∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ d(x(σ(m)), x(σ(n))) < ε",
									By(cauchy[1].At(ε), pos))
								c.Show(
									"yet σ(N) < σ(N + 1), so x(σ(N)) and x(σ(N + 1)) are at least ε apart",
									ByArith(
										pairs.At(N, c.TermAs[Nat]("N + 1")),
										apart[1].At(c.TermAs[Nat]("σ(N)"), c.TermAs[Nat]("σ(N + 1)")),
										sub[0].At(N)))
							})),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Compactness by sequences
// ---------------------------------------------------------------------------

// CompactImpSequential — a compact set of a metric space lies in M, and
// every sequence of its points has a subsequence converging to one of
// them.
//
// Some point of k is a cluster point of the sequence. Were none, each
// point l of k would have a radius ρ(l) and an index B(l) past which no
// term comes within ρ(l) of l. The balls of those radii are open and cover
// k, and finitely many of them, about the points of a finite F, already
// do; past every B(z), z in F — at an index K — the term x(K), a point of
// k, lies in none of them. A cluster point is the limit of a subsequence
// (ClusterPointSubsequence).
var CompactImpSequential = compactImpSequentialThm{family.Add(registry.ProofEntry{
	Name: "CompactImpSequential",
	Key:  "prop_30e4e800be027ac9",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀k:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"compact_in(metric_topology(M, d), k)",
		},
		Conclusion: "k ⊆ M ∧ " +
			"(∀x:(num → A). " +
			"    (∀n:num. x(n) ∈ k) ⇒ " +
			"    ∃σ:(num → num). ∃l:A. " +
			"        (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, x ∘ σ, l))",
		Abbrev: Abbrev{
			{Name: "balls", Text: "{ball(M, d, l, ρ(l)) | l:A | l ∈ k}"},
		},
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			k *Expr[Set[A]],
			kCompact Fact,
		) {
			covers := a.Conjuncts(
				a.Unfolded(kCompact, compact.CompactInDef),
				"k lies in the space of the topology",
				"every open cover of k has a finite subcover")
			kM := a.Have(
				"k lies in M, the space of the topology",
				"k ⊆ M",
				By(covers[0], metric_space.MetricTopologySpace))
			a.Do(SplitConj(
				Case(
					"k lies in M",
					By(kM)),
				Case(
					"every sequence of points of k has a subsequence converging to a point of k",
					Derive(func(b *Argument) {
						x := b.FixAs[Fun[Nat, A]]("x")
						terms := b.Assume()
						inM := b.Have(
							"every term is a point of M",
							"∀n:num. x(n) ∈ M",
							BySets(terms, kM))
						l, cluster := b.ObtainAs[A](
							"some point l of k is a cluster point of x",
							"∃l:A. l ∈ k ∧ (∀r:real. &0 < r ⇒ ∀N:num. ∃n:num. N ≤ n ∧ d(x(n), l) < r)",
							Derive(func(c *Argument) {
								none := c.SupposeNot()
								away := c.Have(
									"then each point l of k has a radius and an index past which no term comes within it of l",
									"∀l:A. l ∈ k ⇒ ∃r:real. &0 < r ∧ (∃N:num. ∀n:num. N ≤ n ⇒ r ≤ d(x(n), l))",
									By(none, real_order_ring.NotLessThan))
								_, B, chosen := c.Obtain2As[Fun[A, Real], Fun[A, Nat]](
									"choosing them at each point of k gives functions ρ and B",
									"∃ρ:(A → real). ∃B:(A → num). ∀l:A. l ∈ k ⇒ &0 < ρ(l) ∧ (∀n:num. B(l) ≤ n ⇒ ρ(l) ≤ d(x(n), l))",
									By(away))
								open := c.Have(
									"the balls of those radii about the points of k are open",
									"«balls» ⊆ metric_topology(M, d)",
									BySets(kM, metric_space.BallOpen.Read(metric)))
								centred := c.Have(
									"each holds its centre, its radius being positive",
									"∀l:A. l ∈ k ⇒ l ∈ ball(M, d, l, ρ(l))",
									Derive(func(e *Argument) {
										z := e.FixAs[A]("z")
										inK := e.Assume()
										zm := e.MemberOf[on.M](z, e.Have(
											"z is a point of M, k lying in M",
											"z ∈ M",
											BySets(inK, kM)))
										e.Show(
											"ρ(z) is positive",
											ByArith(chosen.At(z), inK, metric_space.CentreInBall.Read(metric).At(zm, e.TermAs[Real]("ρ(z)"))))
									}))
								cover := c.Have(
									"so the balls cover k",
									"k ⊆ ⋃«balls»",
									BySets(centred))
								e, subcover := c.ObtainAs[Set[Set[A]]](
									"compactness: finitely many of the balls, a family e, cover k",
									"∃e:set(set(A)). e ⊆ «balls» ∧ finite(e) ∧ k ⊆ ⋃e",
									By(covers[1], open, cover))
								held := c.Conjuncts(
									subcover,
									"e is made of the balls",
									"e is finite",
									"e covers k")
								ballAt := c.TermAs[Fun[A, Set[A]]]("λl:A. ball(M, d, l, ρ(l))")
								F, centres := c.ObtainAs[Set[A]](
									"the balls of e are centred at finitely many points of k, a set F",
									"∃F:set(A). finite(F) ∧ F ⊆ k ∧ e ⊆ image(λl:A. ball(M, d, l, ρ(l)), F)",
									By(
										held[0],
										held[1],
										finite_set.FiniteSubsetImageImp.At(ballAt, k, e),
										set_image.SimpleImage.At(ballAt, k)))
								atF := c.Conjuncts(
									centres,
									"F is finite",
									"F lies in k",
									"every ball of e is centred at a point of F")
								coverF := c.Have(
									"so the balls about the points of F cover k",
									"k ⊆ ⋃{ball(M, d, l, ρ(l)) | l:A | l ∈ F}",
									BySets(held[2], atF[2]))
								K, bound := c.ObtainAs[Nat](
									"the finitely many indices B(l), l in F, are all at most some K",
									"∃K:num. image(B, F) ⊆ 0 .. K",
									By(atF[0], finite_set.FiniteImage.At(B, F), num_segment.FiniteIffBounded))
								xK := c.TermAs[A]("x(K)")
								z, near := c.ObtainAs[A](
									"x(K), a point of k, lies in the ball about some point z of F",
									"∃z:A. z ∈ F ∧ x(K) ∈ ball(M, d, z, ρ(z))",
									BySets(terms.At(K), coverF))
								at := c.Conjuncts(
									near,
									"z is a point of F",
									"x(K) lies in the ball about z")
								zK := c.Have(
									"z is a point of k, F lying in k",
									"z ∈ k",
									BySets(at[0], atF[1]))
								past := c.Have(
									"B(z) is at most K",
									"B(z) ≤ K",
									By(bound, at[0], set_image.FunInImage.At(B, F, z), set_basic.SubsetDef))
								apart := c.Conjuncts(
									GroupPremises(zK, chosen.At(z)),
									"ρ(z) is positive",
									"past B(z) no term comes within ρ(z) of z")
								inBall := c.Conjuncts(
									c.Unfolded(at[1], metric_space.BallDef),
									"x(K) is a point of M",
									"x(K) lies within ρ(z) of z")
								zm := c.MemberOf[on.M](z, c.Have(
									"z is a point of M, k lying in M",
									"z ∈ M",
									BySets(zK, kM)))
								c.Show(
									"yet K is past B(z), so x(K) is at least ρ(z) from z",
									ByArith(
										apart[1].At(K),
										past,
										inBall[1],
										metric_space.DistSym.Read(metric).At(zm, c.MemberOf[on.M](xK, inBall[0]))))
							}))
						found := b.Conjuncts(
							cluster,
							"l is a point of k",
							"every ball about l holds terms past every index")
						lM := b.Have(
							"l is a point of M, k lying in M",
							"l ∈ M",
							BySets(found[0], kM))
						σ, subsequence := b.ObtainAs[Fun[Nat, Nat]](
							"a cluster point is the limit of a subsequence x ∘ σ",
							"∃σ:(num → num). (∀j:num. σ(j) < σ(j + 1)) ∧ metric_converges_to(M, d, x ∘ σ, l)",
							By(metric, inM, lM, found[1], ClusterPointSubsequence.At(M, d, x, l)))
						b.Take(σ)
						b.Take(l)
						b.Show(
							"σ is strictly increasing, l is a point of k, and x ∘ σ converges to l",
							By(subsequence, found[0]))
					})),
			))
		}),
})}

// SequentialLebesgue — an open cover of a set every sequence of which has a
// subsequence converging in the set has a Lebesgue number: a positive
// radius every ball of which about a point of the set lies in one member.
//
// Were there none, each n would leave a point y(n) of k whose ball of
// radius 1/(n + 1) lies in no member. A subsequence y ∘ σ converges to a
// point l of k, which lies in an open member u, with the ball of some
// radius r about l inside u. Far out, at j = N + K, y(σ(j)) lies within r/2
// of l and 1/(σ(j) + 1) is below 1/N < r/2, so the ball of radius
// 1/(σ(j) + 1) about y(σ(j)) lies in the ball of radius r about l, inside u.
var SequentialLebesgue = sequentialLebesgueThm{family.Add(registry.ProofEntry{
	Name: "SequentialLebesgue",
	Key:  "prop_3e6e3adfe8409410",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀k:set(A). ∀c:set(set(A)).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"k ⊆ M",
			"∀x:(num → A). " +
				"    (∀n:num. x(n) ∈ k) ⇒ " +
				"    ∃σ:(num → num). ∃l:A. (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, x ∘ σ, l)",
			"c ⊆ metric_topology(M, d)",
			"k ⊆ ⋃c",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ (∀x:A. x ∈ k ⇒ ∃u:set(A). u ∈ c ∧ ball(M, d, x, δ) ⊆ u)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			k *Expr[Set[A]],
			kM, sequential Fact,
			c *Expr[Set[Set[A]]],
			open, covers Fact,
		) {
			noNumber := a.SupposeNot()
			bad := a.Have(
				"then for each n some point of k has its ball of radius 1/(n + 1) in no member of c",
				"∀n:num. ∃y:A. y ∈ k ∧ (∀u:set(A). u ∈ c ⇒ ¬(ball(M, d, y, real_inv(&n + &1)) ⊆ u))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					positive := b.Have(
						"1/(n + 1) is a positive radius",
						"&0 < real_inv(&n + &1)",
						ByArith(real_order_field.InvPos.At(b.TermAs[Real]("&n + &1"))))
					b.Show(
						"so 1/(n + 1) is no Lebesgue number",
						By(noNumber, positive))
				}))
			y, chosen := a.ObtainAs[Fun[Nat, A]](
				"choosing one such point for each n is a sequence y of points of k",
				"∃y:(num → A). ∀n:num. y(n) ∈ k ∧ (∀u:set(A). u ∈ c ⇒ ¬(ball(M, d, y(n), real_inv(&n + &1)) ⊆ u))",
				By(bad))
			terms := a.Have(
				"every y(n) is a point of k",
				"∀n:num. y(n) ∈ k",
				By(chosen))
			σ, l, limit := a.Obtain2As[Fun[Nat, Nat], A](
				"a subsequence y ∘ σ converges to a point l of k",
				"∃σ:(num → num). ∃l:A. (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, y ∘ σ, l)",
				By(sequential.At(y), terms))
			lim := a.Conjuncts(
				limit,
				"σ is strictly increasing",
				"l is a point of k",
				"y ∘ σ converges to l")
			_, member := a.ObtainAs[Set[A]](
				"l lies in some member u of c",
				"∃u:set(A). u ∈ c ∧ l ∈ u",
				BySets(lim[1], covers))
			memberOf := a.Conjuncts(
				member,
				"u is a member of c",
				"l lies in u")
			_, inside := a.ObtainAs[Real](
				"u is open: the ball of some radius r about l lies in u",
				"∃r:real. &0 < r ∧ ball(M, d, l, r) ⊆ u",
				By(open, member, metric_space.OpenIff, set_basic.SubsetDef))
			around := a.Conjuncts(
				inside,
				"r is positive",
				"the ball of radius r about l lies in u")
			half := a.TermAs[Real]("r / &2")
			halfPositive := a.Have(
				"r/2 is positive",
				"&0 < r / &2",
				ByArith(around[0]))
			_, small := a.ObtainAs[Nat](
				"the Archimedean property puts some 1/N, N ≠ 0, between 0 and r/2",
				"∃N:num. N ≠ 0 ∧ &0 < real_inv(&N) ∧ real_inv(&N) < r / &2",
				By(real_archimedean.PosIffExistsSmallInv.At(half), halfPositive))
			below := a.Conjuncts(
				small,
				"N is not 0",
				"1/N is positive",
				"1/N is below r/2")
			converges := a.Conjuncts(
				a.Unfolded(a.Unfolded(lim[2], MetricConvergesToDef), functions.ComposeApply),
				"l is a point of M",
				"every term of the subsequence is a point of M",
				"every positive distance about l holds a tail of the subsequence")
			_, tail := a.ObtainAs[Nat](
				"past some index K the terms of the subsequence lie within r/2 of l",
				"∃K:num. ∀n:num. K ≤ n ⇒ d(y(σ(n)), l) < r / &2",
				By(converges[2].At(half), halfPositive))
			j := a.TermAs[Nat]("N + K")
			σj := a.TermAs[Nat]("σ(N + K)")
			late := a.Have(
				"σ(N + K) is at least N + K, so at least N",
				"N ≤ σ(N + K)",
				ByArith(nat_order.LessEqStrictlyIncreasing.At(σ, j), lim[0]))
			radius := a.Have(
				"so 1/(σ(N + K) + 1) lies below 1/N, below r/2",
				"real_inv(&σ(N + K) + &1) < r / &2",
				ByArith(
					late,
					below[1],
					below[2],
					real_order_field.InvPos.At(a.TermAs[Real]("&N")),
					real_order_field.InvAntitone.At(a.TermAs[Real]("&N"), a.TermAs[Real]("&σ(N + K) + &1"))))
			near := a.Have(
				"y(σ(N + K)) lies within r/2 of l, N + K being past K",
				"d(y(σ(N + K)), l) < r / &2",
				ByArith(tail.At(j)))
			lm := a.MemberOf[on.M](l, converges[0])
			ym := a.MemberOf[on.M](a.TermAs[A]("y(σ(N + K))"), converges[1].At(j))
			shrunk := a.Have(
				"so the ball of radius 1/(σ(N + K) + 1) about y(σ(N + K)) lies in the ball of radius r about l",
				"ball(M, d, y(σ(N + K)), real_inv(&σ(N + K) + &1)) ⊆ ball(M, d, l, r)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					w := b.FixAs[A]("w")
					wNear := b.Conjuncts(
						b.Unfolded(b.Assume(), metric_space.BallDef),
						"w is a point of M",
						"w lies within 1/(σ(N + K) + 1) of y(σ(N + K))")
					wm := b.MemberOf[on.M](w, wNear[0])
					within := b.Have(
						"d(l, w) ≤ d(l, y(σ(N + K))) + d(y(σ(N + K)), w) < r/2 + r/2",
						"d(l, w) < r",
						ByArith(
							near,
							wNear[1],
							radius,
							metric_space.DistTriangle.Read(metric).At(lm, ym, wm),
							metric_space.DistSym.Read(metric).At(lm, ym)))
					b.Show(
						"so w lies in the ball of radius r about l",
						BySets(metric_space.BallDef, wNear[0], within))
				}))
			a.Show(
				"so that ball lies in u, though y(σ(N + K)) was chosen with its ball in no member of c",
				By(chosen.At(σj), memberOf[0], shrunk, around[1], set_order.SubsetTrans))
		}),
})}

// SequentialTotallyBounded — a set every sequence of which has a
// subsequence converging in it is totally bounded: a convergent
// subsequence is Cauchy (ConvergentImpCauchy), and a set whose sequences
// all have Cauchy subsequences is totally bounded (TotallyBoundedSequential).
var SequentialTotallyBounded = sequentialTotallyBoundedThm{family.Add(registry.ProofEntry{
	Name: "SequentialTotallyBounded",
	Key:  "prop_771a000cc36f1154",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀k:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"k ⊆ M",
			"∀x:(num → A). " +
				"    (∀n:num. x(n) ∈ k) ⇒ " +
				"    ∃σ:(num → num). ∃l:A. (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, x ∘ σ, l)",
		},
		Conclusion: "totally_bounded(M, d, k)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			k *Expr[Set[A]],
			kM, sequential Fact,
		) {
			cauchy := a.Have(
				"every sequence of points of k has a Cauchy subsequence, a convergent one",
				Statement{
					Binders: "∀x:(num → A).",
					Hypotheses: []string{
						"∀n:num. x(n) ∈ k",
					},
					Conclusion: "∃σ:(num → num). (∀j:num. σ(j) < σ(j + 1)) ∧ metric_cauchy(M, d, x ∘ σ)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[Fun[Nat, A]]("x")
					terms := b.Assume()
					σ, l, limit := b.Obtain2As[Fun[Nat, Nat], A](
						"a subsequence x ∘ σ converges to a point l of k",
						"∃σ:(num → num). ∃l:A. (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, x ∘ σ, l)",
						By(sequential.At(x), terms))
					lim := b.Conjuncts(
						limit,
						"σ is strictly increasing",
						"l is a point of k",
						"x ∘ σ converges to l")
					b.Take(σ)
					b.Show(
						"x ∘ σ converges, so it is Cauchy",
						By(lim[0], metric, lim[2], ConvergentImpCauchy.At(M, d, b.TermAs[Fun[Nat, A]]("x ∘ σ"), l)))
				}))
			a.Show(
				"so k is totally bounded",
				By(metric, kM, cauchy, TotallyBoundedSequential.At(M, d, k)))
		}),
})}

// SequentialImpCompact — a subset of M every sequence of which has a
// subsequence converging in it is compact.
//
// k is totally bounded (SequentialTotallyBounded). Given an open cover,
// take a Lebesgue number δ (SequentialLebesgue) and finitely many points of
// k, a set F, within δ of every point of k: the members of the cover
// holding the balls of radius δ about the points of F are finitely many
// and cover k.
var SequentialImpCompact = sequentialImpCompactThm{family.Add(registry.ProofEntry{
	Name: "SequentialImpCompact",
	Key:  "prop_3ae5fb58ccaf93ff",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀k:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"k ⊆ M",
			"∀x:(num → A). " +
				"    (∀n:num. x(n) ∈ k) ⇒ " +
				"    ∃σ:(num → num). ∃l:A. (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, x ∘ σ, l)",
		},
		Conclusion: "compact_in(metric_topology(M, d), k)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			k *Expr[Set[A]],
			kM, sequential Fact,
		) {
			bounded := a.Have(
				"k is totally bounded, its convergent subsequences being Cauchy",
				"totally_bounded(M, d, k)",
				By(metric, kM, sequential, SequentialTotallyBounded.At(M, d, k)))
			nets := a.Conjuncts(
				a.Unfolded(bounded, TotallyBoundedDef),
				"k lies in M",
				"for every positive distance finitely many points of k come within it of every point of k")

			a.Do(Unfold(compact.CompactInDef))
			a.Do(SplitConj(
				Case(
					"k lies in M, the space of the topology",
					By(kM, metric_space.MetricTopologySpace)),
				Case(
					"every open cover of k has a finite subcover",
					Derive(func(b *Argument) {
						c := b.FixAs[Set[Set[A]]]("c")
						cover := b.Conjuncts(
							b.Assume(),
							"c is made of open sets",
							"c covers k")
						δ, number := b.ObtainAs[Real](
							"the cover has a Lebesgue number δ",
							"∃δ:real. &0 < δ ∧ (∀x:A. x ∈ k ⇒ ∃u:set(A). u ∈ c ∧ ball(M, d, x, δ) ⊆ u)",
							By(metric, kM, sequential, cover[0], cover[1], SequentialLebesgue.At(M, d, k, c)))
						lebesgue := b.Conjuncts(
							number,
							"δ is positive",
							"the ball of radius δ about a point of k lies in a member of c")
						F, net := b.ObtainAs[Set[A]](
							"finitely many points of k, a set F, come within δ of every point of k",
							"∃F:set(A). finite(F) ∧ F ⊆ k ∧ (∀y:A. y ∈ k ⇒ ∃x:A. x ∈ F ∧ d(x, y) < δ)",
							By(nets[1].At(δ), lebesgue[0]))
						atF := b.Conjuncts(
							net,
							"F is finite",
							"F lies in k",
							"every point of k lies within δ of a point of F")
						U, members := b.ObtainAs[Fun[A, Set[A]]](
							"choosing at each point of k a member of c holding its ball of radius δ is a map U",
							"∃U:(A → set(A)). ∀x:A. x ∈ k ⇒ U(x) ∈ c ∧ ball(M, d, x, δ) ⊆ U(x)",
							By(lebesgue[1]))
						b.Take(b.TermAs[Set[Set[A]]]("image(U, F)"))
						b.Do(SplitConjAll(
							Case(
								"the members chosen at the points of F lie in c",
								BySets(members, atF[1])),
							Case(
								"and are finitely many",
								By(atF[0], finite_set.FiniteImage.At(U, F))),
							Case(
								"and cover k: a point y of k lies within δ of a point x of F, so in U(x)",
								Derive(func(e *Argument) {
									e.Do(Simp(Fwd(set_basic.SubsetDef)))
									y := e.FixAs[A]("y")
									inK := e.Assume()
									x, close := e.ObtainAs[A](
										"y lies within δ of some point x of F",
										"∃x:A. x ∈ F ∧ d(x, y) < δ",
										By(atF[2].At(y), inK))
									at := e.Conjuncts(
										close,
										"x is a point of F",
										"y lies within δ of x")
									inBall := e.Have(
										"so y, a point of M, lies in the ball of radius δ about x",
										"y ∈ ball(M, d, x, δ)",
										BySets(metric_space.BallDef, inK, kM, at[1]))
									e.Show(
										"which lies in U(x), a member of the image",
										BySets(inBall, at[0], atF[1], members.At(x)))
								})),
						))
					})),
			))
		}),
})}

// CompactSequential — a subset of a metric space is compact exactly when
// every sequence of its points has a subsequence converging to one of
// them: compactness gives cluster points (CompactImpSequential), and
// sequential compactness gives Lebesgue numbers and finite nets
// (SequentialImpCompact).
var CompactSequential = compactSequentialThm{family.Add(registry.ProofEntry{
	Name: "CompactSequential",
	Key:  "prop_456aee6a66f467ec",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀k:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
		},
		Conclusion: "compact_in(metric_topology(M, d), k) ⇔ " +
			"k ⊆ M ∧ " +
			"(∀x:(num → A). " +
			"    (∀n:num. x(n) ∈ k) ⇒ " +
			"    ∃σ:(num → num). ∃l:A. " +
			"        (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, x ∘ σ, l))",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			k *Expr[Set[A]],
		) {
			a.Iff()
			a.Forward(
				"a compact set has convergent subsequences",
				func(b *Argument, compact Fact) {
					b.Show(
						"by its cluster points",
						By(metric, compact, CompactImpSequential.At(M, d, k)))
				})
			a.Backward(
				"a sequentially compact set is compact",
				func(b *Argument, sequential Fact) {
					parts := b.Conjuncts(
						sequential,
						"k lies in M",
						"every sequence of points of k has a subsequence converging in k")
					b.Show(
						"by its Lebesgue numbers and finite nets",
						By(metric, parts[0], parts[1], SequentialImpCompact.At(M, d, k)))
				})
		}),
})}

// CompactCompleteTotallyBounded — a subset of a metric space is compact
// exactly when it is complete and totally bounded.
//
// Forward: the sequences of a compact k have subsequences converging in k
// (CompactImpSequential), so k is totally bounded (SequentialTotallyBounded);
// and a Cauchy sequence of k converges where such a subsequence does
// (CauchySubsequenceConverges), in k. Backward: a sequence of k has a
// Cauchy subsequence (TotallyBoundedSequential), which converges in k by
// completeness, so k is compact (CompactSequential).
var CompactCompleteTotallyBounded = compactCompleteTotallyBoundedThm{family.Add(registry.ProofEntry{
	Name: "CompactCompleteTotallyBounded",
	Key:  "prop_16034c17b64eeabf",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀k:set(A).",
		Hypotheses: []string{
			"metric_space(M, d)",
		},
		Conclusion: "compact_in(metric_topology(M, d), k) ⇔ " +
			"metric_complete(k, d) ∧ totally_bounded(M, d, k)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			k *Expr[Set[A]],
		) {
			a.Iff()

			a.Forward(
				"a compact set is complete and totally bounded, through its convergent subsequences",
				func(b *Argument, compact Fact) {
					sequential := b.Conjuncts(
						GroupPremises(metric, compact, CompactImpSequential.At(M, d, k)),
						"k lies in M",
						"every sequence of points of k has a subsequence converging to a point of k")
					b.Do(SplitConj(
						Case(
							"a Cauchy sequence of k converges in k, where a subsequence does",
							Derive(func(c *Argument) {
								c.Do(Unfold(MetricCompleteDef))
								x := c.FixAs[Fun[Nat, A]]("x")
								cauchy := c.Conjuncts(
									c.Unfolded(c.Assume(), MetricCauchyDef),
									"every term is a point of k",
									"every positive distance holds any two terms past some index")
								σ, l, limit := c.Obtain2As[Fun[Nat, Nat], A](
									"a subsequence x ∘ σ converges to a point l of k",
									"∃σ:(num → num). ∃l:A. (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, x ∘ σ, l)",
									By(sequential[1].At(x), cauchy[0]))
								lim := c.Conjuncts(
									limit,
									"σ is strictly increasing",
									"l is a point of k",
									"x ∘ σ converges to l")
								inM := c.Have(
									"the terms are points of M, k lying in M",
									"∀n:num. x(n) ∈ M",
									BySets(cauchy[0], sequential[0]))
								cauchyM := c.Have(
									"so x is a Cauchy sequence of M as well",
									"metric_cauchy(M, d, x)",
									By(inM, cauchy[1], MetricCauchyDef))
								convergesM := c.Have(
									"x converges in M where its subsequence does, to l",
									"metric_converges_to(M, d, x, l)",
									By(metric, cauchyM, lim[0], lim[2], CauchySubsequenceConverges.At(M, d, x, σ, l)))
								near := c.Conjuncts(
									c.Unfolded(convergesM, MetricConvergesToDef),
									"l is a point of M",
									"every term is a point of M",
									"every positive distance about l holds a tail of x")
								c.Take(l)
								c.Show(
									"so x converges to l in k, its terms and l being points of k",
									Unfold(MetricConvergesToDef),
									By(lim[1], cauchy[0], near[2]))
							})),
						Case(
							"k is totally bounded, its convergent subsequences being Cauchy",
							By(metric, sequential[0], sequential[1], SequentialTotallyBounded.At(M, d, k))),
					))
				})

			a.Backward(
				"a Cauchy subsequence of a sequence of k converges in k, so k is compact",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"k is complete",
						"k is totally bounded")
					converge := b.Unfolded(parts[0], MetricCompleteDef)
					kM := b.Have(
						"k lies in M, being totally bounded",
						"k ⊆ M",
						By(parts[1], TotallyBoundedDef))
					sequential := b.Have(
						"every sequence of points of k has a subsequence converging to a point of k",
						Statement{
							Binders: "∀x:(num → A).",
							Hypotheses: []string{
								"∀n:num. x(n) ∈ k",
							},
							Conclusion: "∃σ:(num → num). ∃l:A. " +
								"    (∀j:num. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(M, d, x ∘ σ, l)",
						},
						Derive(func(c *Argument) {
							c.FixAs[Fun[Nat, A]]("x")
							terms := c.Assume()
							σ, subsequence := c.ObtainAs[Fun[Nat, Nat]](
								"k being totally bounded, x has a Cauchy subsequence x ∘ σ",
								"∃σ:(num → num). (∀j:num. σ(j) < σ(j + 1)) ∧ metric_cauchy(M, d, x ∘ σ)",
								By(metric, parts[1], terms, TotallyBoundedSequential.At(M, d, k)))
							sub := c.Conjuncts(
								subsequence,
								"σ is strictly increasing",
								"x ∘ σ is Cauchy")
							pairs := c.Conjuncts(
								c.Unfolded(c.Unfolded(sub[1], MetricCauchyDef), functions.ComposeApply),
								"every term of the subsequence is a point of M",
								"every positive distance holds any two terms of the subsequence past some index")
							cauchyK := c.Have(
								"x ∘ σ is a Cauchy sequence of k as well, its terms being points of k",
								"metric_cauchy(k, d, x ∘ σ)",
								Unfold(MetricCauchyDef),
								Unfold(functions.ComposeApply),
								By(terms, pairs[1]))
							l, limit := c.ObtainAs[A](
								"k being complete, x ∘ σ converges in k to some l",
								"∃l:A. metric_converges_to(k, d, x ∘ σ, l)",
								By(converge.At(c.TermAs[Fun[Nat, A]]("x ∘ σ")), cauchyK))
							near := c.Conjuncts(
								c.Unfolded(c.Unfolded(limit, MetricConvergesToDef), functions.ComposeApply),
								"l is a point of k",
								"every term of the subsequence is a point of k",
								"every positive distance about l holds a tail of the subsequence")
							c.Take(σ)
							c.Take(l)
							c.Show(
								"σ is strictly increasing, l is a point of k, and x ∘ σ converges to l in M, k lying in M",
								Unfold(MetricConvergesToDef),
								Unfold(functions.ComposeApply),
								BySets(sub[0], near[0], near[2], pairs[0], kM))
						}))
					b.Show(
						"so k is compact, by its convergent subsequences",
						By(metric, kM, sequential, CompactSequential.At(M, d, k)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Uniform continuity on a compact space
// ---------------------------------------------------------------------------

// LebesgueNumber — an open cover of a compact metric space has a positive
// radius every ball of which lies in one member.
//
// M is compact, so every sequence of its points has a subsequence
// converging in M (CompactImpSequential, at k = M), and an open cover of
// such a set has a Lebesgue number (SequentialLebesgue).
var LebesgueNumber = lebesgueNumberThm{family.Add(registry.ProofEntry{
	Name: "LebesgueNumber",
	Key:  "prop_848a8f2f26a974b8",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀c:set(set(A)).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"compact_in(metric_topology(M, d), M)",
			"c ⊆ metric_topology(M, d)",
			"M ⊆ ⋃c",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ (∀x:A. x ∈ M ⇒ ∃u:set(A). u ∈ c ∧ ball(M, d, x, δ) ⊆ u)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			compact Fact,
			c *Expr[Set[Set[A]]],
			open, covers Fact,
		) {
			sequential := a.Conjuncts(
				GroupPremises(metric, compact, CompactImpSequential.At(M, d, M)),
				"M lies in M",
				"every sequence of points of M has a subsequence converging to a point of M")
			a.Show(
				"so the open cover c has a Lebesgue number, by those subsequences",
				By(metric, sequential[0], sequential[1], open, covers, SequentialLebesgue.At(M, d, M, c)))
		}),
})}

// HeineCantor — a continuous map out of a compact metric space is
// uniformly continuous.
//
// Given ε > 0, the preimages under f of the balls of radius ε/2 about the
// values f(z), z a point of M, are open, f being continuous, and cover M,
// each holding the point it is taken at. A Lebesgue number δ of that cover
// serves ε: two points x and y of M within δ of each other both lie in the
// ball of radius δ about x, which lies in the preimage taken at some z, so
// f(x) and f(y) both lie within ε/2 of f(z), and within ε of each other.
var HeineCantor = heineCantorThm{family.Add(registry.ProofEntry{
	Name: "HeineCantor",
	Key:  "prop_309239094389b79",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀N:set(B). ∀e:(B → B → real). ∀f:(A → B).",
		Hypotheses: []string{
			"metric_space(M, d)",
			"metric_space(N, e)",
			"compact_in(metric_topology(M, d), M)",
			"continuous_map(metric_topology(M, d), metric_topology(N, e), f)",
		},
		Conclusion: "uniformly_continuous_map(M, d, N, e, f)",
		Abbrev: Abbrev{
			{Name: "preimages", Text: "{preimage_on(M, f, ball(N, e, f(z), ε / &2)) | z:A | z ∈ M}"},
		},
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			metric metric_space.MetricSpaceFact[on.M],
			compact Fact,
			N *Expr[Set[B]],
			e *Expr[Fun2[B, B, Real]],
			target metric_space.MetricSpaceFact[on.N],
			f *Arrow[A, B],
			continuity Fact,
		) {
			into := a.Have(
				"f carries M into N",
				"∀x:A. x ∈ M ⇒ f(x) ∈ N",
				By(continuity, target, metric_space.ContinuousMapIff))

			a.Do(Unfold(UniformlyContinuousMap))
			a.Do(SplitConj(
				Case(
					"f carries M into N",
					By(into)),
				Case(
					"a Lebesgue number of the preimages of the balls of radius ε/2 serves ε",
					Derive(func(b *Argument) {
						b.FixAs[Real]()
						pos := b.Assume()
						open := b.Have(
							"f being continuous, the preimage of the ball of radius ε/2 about a value is open",
							"∀z:A. z ∈ M ⇒ preimage_on(M, f, ball(N, e, f(z), ε / &2)) ∈ metric_topology(M, d)",
							Derive(func(c *Argument) {
								z := c.FixAs[A]("z")
								fz := c.MemberOf[on.N](f.Apply(z), GroupPremises(c.Assume(), into.At(z)))
								c.Show(
									"the ball is open in N, and M is the space of the topology of M",
									By(
										continuous.PreimageOpen.Read(continuity).AsFact().At(
											c.TermAs[Set[B]]("ball(N, e, f(z), ε / &2)")),
										metric_space.BallOpen.Read(target).At(fz, c.TermAs[Real]("ε / &2")),
										metric_space.MetricTopologySpace.At(M, d)))
							}))
						preimagesOpen := b.Have(
							"so the preimages are open sets of M",
							"«preimages» ⊆ metric_topology(M, d)",
							BySets(open))
						held := b.Have(
							"each point x of M lies in the preimage taken at x itself",
							"∀x:A. x ∈ M ⇒ x ∈ preimage_on(M, f, ball(N, e, f(x), ε / &2))",
							Derive(func(c *Argument) {
								x := c.FixAs[A]("x")
								xM := c.Assume()
								fx := c.MemberOf[on.N](f.Apply(x), GroupPremises(xM, into.At(x)))
								inBall := c.Have(
									"f(x) lies in the ball of radius ε/2 about itself",
									"f(x) ∈ ball(N, e, f(x), ε / &2)",
									ByArith(pos, fx, metric_space.CentreInBall.Read(target).At(fx, c.TermAs[Real]("ε / &2"))))
								c.Show(
									"so x lies in the preimage of that ball",
									BySets(xM, inBall))
							}))
						covered := b.Have(
							"so the preimages cover M",
							"M ⊆ ⋃«preimages»",
							BySets(held))
						δ, lebesgue := b.ObtainAs[Real](
							"M being compact, the cover has a Lebesgue number δ",
							"∃δ:real. &0 < δ ∧ (∀x:A. x ∈ M ⇒ ∃u:set(A). u ∈ «preimages» ∧ ball(M, d, x, δ) ⊆ u)",
							By(
								metric,
								compact,
								preimagesOpen,
								covered,
								LebesgueNumber.At(M, d, b.TermAs[Set[Set[A]]]("«preimages»"))))
						number := b.Conjuncts(
							lebesgue,
							"δ is positive",
							"the ball of radius δ about a point of M lies in one of the preimages")
						b.Take(δ)
						b.Do(SplitConj(
							Case(
								"δ is positive",
								By(number[0])),
							Case(
								"two points of M within δ of each other have values within ε of each other",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									y := c.FixAs[A]("y")
									near := c.Conjuncts(
										c.Assume(),
										"x is a point of M",
										"y is a point of M",
										"x and y are within δ of each other")
									xm := c.MemberOf[on.M](x, near[0])
									z, inside := c.ObtainAs[A](
										"the ball of radius δ about x lies in the preimage taken at some point z of M",
										"∃z:A. z ∈ M ∧ ball(M, d, x, δ) ⊆ preimage_on(M, f, ball(N, e, f(z), ε / &2))",
										By(number[1].At(x), near[0]))
									taken := c.Conjuncts(
										inside,
										"z is a point of M",
										"the ball of radius δ about x lies in the preimage taken at z")
									both := c.Have(
										"x and y lie in the ball of radius δ about x",
										"x ∈ ball(M, d, x, δ) ∧ y ∈ ball(M, d, x, δ)",
										BySets(
											xm,
											near[1],
											near[2],
											number[0],
											metric_space.CentreInBall.Read(metric).At(xm, δ),
											metric_space.BallDef))
									values := c.Have(
										"so f(x) and f(y) lie in the ball of radius ε/2 about f(z)",
										"f(x) ∈ ball(N, e, f(z), ε / &2) ∧ f(y) ∈ ball(N, e, f(z), ε / &2)",
										BySets(both, taken[1]))
									distances := c.Have(
										"both values lie within ε/2 of f(z)",
										"e(f(z), f(x)) < ε / &2 ∧ e(f(z), f(y)) < ε / &2",
										BySets(values, metric_space.BallDef))
									fx := c.MemberOf[on.N](f.Apply(x), GroupPremises(near[0], into.At(x)))
									fy := c.MemberOf[on.N](f.Apply(y), GroupPremises(near[1], into.At(y)))
									fz := c.MemberOf[on.N](f.Apply(z), GroupPremises(taken[0], into.At(z)))
									c.Show(
										"so f(x) and f(y) lie within ε of each other, by the detour through f(z)",
										ByArith(
											distances,
											metric_space.DistTriangle.Read(target).At(fx, fz, fy),
											metric_space.DistSym.Read(target).At(fz, fx)))
								})),
						))
					})),
			))
		}),
})}
