// space.go — the real line as a topological space: what an open set of
// reals is, that the open sets form a topology, and the open and closed
// sets every later argument is built from — balls, rays and intervals,
// with membership in the four bounded intervals.

package real_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The open sets
// ---------------------------------------------------------------------------

// OpenIff — a set of reals is open exactly when each of its points has
// a radius inside it: the family's definition read as membership in the
// family. It is the form every member of the chapter reads openness in.
var OpenIff = openIffThm{family.Add(registry.ProofEntry{
	Name: "OpenIff",
	Key:  "prop_9725e6d7b728b974",
	Build: family.Theorem("∀u:set(real). "+
		"    u ∈ real_topology ⇔ ∀x:real. x ∈ u ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∈ u",
		func(a *Argument, u *Expr[Set[Real]]) {
			a.Show(
				"membership in the family is the condition it is built from",
				Unfold(RealTopologyDef),
				BySets())
		}),
})}

// RealTopology — the open sets of the real line form a topology: they
// are the open sets of the line's distance (RealTopologyMetric), and
// the open sets of any distance form a topology.
var RealTopology = realTopologyThm{family.Add(registry.ProofEntry{
	Name: "RealTopology",
	Key:  "prop_df51c264744c44cc",
	Build: family.Theorem(
		"is_topology(real_topology)",
		Chain(Simp(Fwd(RealTopologyMetric)), By(metric_space.MetricTopology))),
})}

// RealSpace — the points of the space are all the reals: the space of
// a distance's topology is its carrier, and the line's carrier is 𝕌.
var RealSpace = realSpaceThm{family.Add(registry.ProofEntry{
	Name: "RealSpace",
	Key:  "prop_87b0266acf3ea588",
	Build: family.Theorem(
		"⋃real_topology = 𝕌", Chain(Simp(Fwd(RealTopologyMetric)), By(metric_space.MetricTopologySpace))),
})}

// ClosedIff — a set of reals is closed exactly when each real outside
// it has a radius missing it: closed for the distance is that each
// real outside s has a ball about it missing s, and a ball misses s
// exactly when every real within its radius of its centre is outside
// s. The line's space is all of 𝕌, so no membership in the space is
// asked.
var ClosedIff = closedIffThm{family.Add(registry.ProofEntry{
	Name: "ClosedIff",
	Key:  "prop_d5c96934e199821a",
	Build: family.Sections("∀s:set(real). "+
		"    closed_in(real_topology, s) ⇔ ∀x:real. x ∉ s ⇒ ∃δ:real. &0 < δ ∧ ∀y:real. |y - x| < δ ⇒ y ∉ s",
		func(ctx *Script, headline string) *GoalStackNode {
			ballMisses := ctx.Lemma("∀s:set(real). ∀x r:real. "+
				"    ball(𝕌, real_dist, x, r) ∩ s = ∅ ⇔ ∀y:real. |y - x| < r ⇒ y ∉ s",
				func(a *Argument, s *Expr[Set[Real]], x, r *Expr[Real]) {
					a.Show(
						"read pointwise, the ball's points being the reals within r of x",
						Simp(
							Fwd(set_basic.Extension.Inst[Real]()),
							Fwd(set_basic.InInter.Inst[Real]()),
							Fwd(set_basic.NotInEmpty.Inst[Real]()),
							Fwd(RealBall)),
						TrivialNormalized())
				})

			return ctx.Theorem(headline,
				func(a *Argument, s *Expr[Set[Real]]) {
					a.Show(
						"closed for the distance, read on the line, is the radius condition",
						// Closed for the distance: s lies in the carrier, which every
						// set of reals does, and each point of the carrier outside s
						// has a ball about it missing s.
						Simp(Fwd(RealTopologyMetric)),
						Simp(Fwd(metric_space.ClosedIff.Inst[Real]())),
						Simp(Fwd(set_order.SubsetUniv.Inst[Real]()), Fwd(set_basic.InUniv.Inst[Real]())),
						Simp(Fwd(ballMisses)),
						TrivialNormalized())
				})
		}),
})}

// ---------------------------------------------------------------------------
// Balls, rays and intervals
// ---------------------------------------------------------------------------

// BallOpen — the reals within r of c form an open set: they are the
// ball of the distance about c, and a ball is open in the metric
// topology.
var BallOpen = ballOpenThm{family.Add(registry.ProofEntry{
	Name: "BallOpen",
	Key:  "prop_ad481448e9cc0d15",
	Build: family.Theorem("∀c r:real. {y:real | |y - c| < r} ∈ real_topology",
		func(a *Argument, c, r *Expr[Real]) {
			ball := a.Have(
				"the reals within r of c are the ball of the distance about c",
				"{y:real | |y - c| < r} = ball(𝕌⟨A:real⟩, real_dist, c, r)",
				Simp(Fwd(set_basic.Extension.Inst[Real]()), Fwd(RealBall)),
				BySets())
			centre := a.Have(
				"c is a point of the line",
				"c ∈ 𝕌",
				BySets())
			a.Show(
				"and a ball about a point of the carrier is open",
				Simp(Fwd(RealTopologyMetric)),
				ball.Rw(),
				By(metric_space.BallOpen.Read(RealMetric).At(proof.MemberOf(c, centre), r)))
		}),
})}

// RayAboveOpen — the reals above a point form an open set.
//
// A point x of the ray has the radius x − a, positive because x lies
// above a. A point y within x − a of x lies above x − (x − a) = a — an
// estimate that asks nothing of x — so the whole ball stays in the ray.
var RayAboveOpen = rayAboveOpenThm{family.Add(registry.ProofEntry{
	Name: "RayAboveOpen",
	Key:  "prop_84c0673d36f460ed",
	Build: family.Theorem("∀a:real. {x:real | a < x} ∈ real_topology",
		func(arg *Argument, a *Expr[Real]) {
			arg.Do(Simp(Fwd(OpenIff)))
			arg.FixAs[Real]("x")
			above := arg.Have(
				"x lies above a",
				"a < x",
				BySets(arg.Assume()))
			arg.Take(arg.TermAs[Real]("x - a"))
			arg.Do(SplitConj(
				Case(
					"the radius x − a is positive, x lying above a",
					ByArith(above)),
				Case(
					"and a point y within it of x lies in the ray",
					Derive(func(b *Argument) {
						b.FixAs[Real]("y")
						closeToX := b.Assume()
						beyond := b.Have(
							"y lies above x − (x − a) = a",
							"a < y",
							ByArith(closeToX))
						b.Show(
							"so y lies in the ray",
							BySets(beyond))
					})),
			))
		}),
})}

// RayBelowOpen — the reals below a point form an open set: the mirror of
// RayAboveOpen. A point x of the ray has the radius b − x, and a point y
// within b − x of x lies below x + (b − x) = b.
var RayBelowOpen = rayBelowOpenThm{family.Add(registry.ProofEntry{
	Name: "RayBelowOpen",
	Key:  "prop_75cb71717e0289aa",
	Build: family.Theorem("∀b:real. {x:real | x < b} ∈ real_topology",
		func(arg *Argument, b *Expr[Real]) {
			arg.Do(Simp(Fwd(OpenIff)))
			arg.FixAs[Real]("x")
			below := arg.Have(
				"x lies below b",
				"x < b",
				BySets(arg.Assume()))
			arg.Take(arg.TermAs[Real]("b - x"))
			arg.Do(SplitConj(
				Case(
					"the radius b − x is positive, x lying below b",
					ByArith(below)),
				Case(
					"and a point y within it of x lies in the ray",
					Derive(func(c *Argument) {
						c.FixAs[Real]("y")
						closeToX := c.Assume()
						short := c.Have(
							"y lies below x + (b − x) = b",
							"y < b",
							ByArith(closeToX))
						c.Show(
							"so y lies in the ray",
							BySets(short))
					})),
			))
		}),
})}

// ClosedIntervalMembership — a real lies in ⟦a, b⟧ exactly when it lies
// between the ends. The closers read the membership so themselves
// (RealClosedIntervalDef's MembershipRead); the law is the reading as a
// statement, for a rewrite or an instance.
var ClosedIntervalMembership = closedIntervalMembershipThm{family.Add(registry.ProofEntry{
	Name: "ClosedIntervalMembership",
	Key:  "prop_aa6784630942ef1b",
	Build: family.Theorem(
		"∀x a b:real. x ∈ ⟦a, b⟧ ⇔ a ≤ x ∧ x ≤ b",
		func(arg *Argument, x, a, b *Expr[Real]) {
			arg.Show(
				"membership in ⟦a, b⟧ is its condition, read at x",
				BySets())
		}),
})}

// OpenIntervalMembership — a real lies in ⟬a, b⟭ exactly when it lies
// strictly between the ends.
var OpenIntervalMembership = openIntervalMembershipThm{family.Add(registry.ProofEntry{
	Name: "OpenIntervalMembership",
	Key:  "prop_382e0035a1329015",
	Build: family.Theorem(
		"∀x a b:real. x ∈ ⟬a, b⟭ ⇔ a < x ∧ x < b",
		func(arg *Argument, x, a, b *Expr[Real]) {
			arg.Show(
				"membership in ⟬a, b⟭ is its condition, read at x",
				BySets())
		}),
})}

// ClosedOpenIntervalMembership — a real lies in ⟦a, b⟭ exactly when it
// lies from a up to b, b excluded.
var ClosedOpenIntervalMembership = closedOpenIntervalMembershipThm{family.Add(registry.ProofEntry{
	Name: "ClosedOpenIntervalMembership",
	Key:  "prop_44c7fd0dfa1970c4",
	Build: family.Theorem(
		"∀x a b:real. x ∈ ⟦a, b⟭ ⇔ a ≤ x ∧ x < b",
		func(arg *Argument, x, a, b *Expr[Real]) {
			arg.Show(
				"membership in ⟦a, b⟭ is its condition, read at x",
				BySets())
		}),
})}

// OpenClosedIntervalMembership — a real lies in ⟬a, b⟧ exactly when it
// lies above a up to b, b included.
var OpenClosedIntervalMembership = openClosedIntervalMembershipThm{family.Add(registry.ProofEntry{
	Name: "OpenClosedIntervalMembership",
	Key:  "prop_d1c56d2fd3654159",
	Build: family.Theorem(
		"∀x a b:real. x ∈ ⟬a, b⟧ ⇔ a < x ∧ x ≤ b",
		func(arg *Argument, x, a, b *Expr[Real]) {
			arg.Show(
				"membership in ⟬a, b⟧ is its condition, read at x",
				BySets())
		}),
})}

// OpenIntervalOpen — an open interval is open: it is the meet of the ray
// above its left end and the ray below its right end, and two open sets
// meet in an open set.
var OpenIntervalOpen = openIntervalOpenThm{family.Add(registry.ProofEntry{
	Name: "OpenIntervalOpen",
	Key:  "prop_f58f2cd2de8ff2d1",
	Build: family.Theorem("∀a b:real. ⟬a, b⟭ ∈ real_topology",
		func(arg *Argument, a, b *Expr[Real]) {
			meet := arg.Have(
				"the interval is the meet of the two rays",
				"⟬a, b⟭ = {x:real | a < x} ∩ {x:real | x < b}",
				BySets())
			arg.Show(
				"and two open rays meet in an open set",
				meet.Rw(),
				By(topological_space.InterOpen, RealTopology, RayAboveOpen.At(a), RayBelowOpen.At(b)))
		}),
})}

// ClosedIntervalClosed — a closed interval is closed: the space is the
// whole line, and the complement of ⟦a, b⟧ there is the union of the ray
// below a and the ray above b, two open sets.
var ClosedIntervalClosed = closedIntervalClosedThm{family.Add(registry.ProofEntry{
	Name: "ClosedIntervalClosed",
	Key:  "prop_44ab640d82bf9d6b",
	Build: family.Theorem("∀a b:real. closed_in(real_topology, ⟦a, b⟧)",
		func(arg *Argument, a, b *Expr[Real]) {
			arg.Do(Unfold(topological_space.ClosedInDef), Simp(Fwd(RealSpace)))
			outside := arg.Have(
				"a real outside ⟦a, b⟧ lies below a or above b, ≤ failing exactly where the reversed < holds",
				"∀x:real. ¬(a ≤ x ∧ x ≤ b) ⇔ x < a ∨ b < x",
				ByArith())
			complement := arg.Have(
				"so the complement of ⟦a, b⟧ is the two rays",
				"𝕌 ∖ ⟦a, b⟧ = {x:real | x < a} ∪ {x:real | b < x}",
				BySets(outside))
			arg.Do(SplitConj(
				Case(
					"the interval lies in the line",
					BySets()),
				Case(
					"and its complement, the two open rays, is open",
					complement.Rw(),
					By(topological_space.UnionOpen, RealTopology, RayBelowOpen.At(a), RayAboveOpen.At(b)))))
		}),
})}

// ---------------------------------------------------------------------------
// Separation
// ---------------------------------------------------------------------------

// RealHausdorff — two distinct reals lie in disjoint open sets: the
// open sets of a metric space separate points, and the line is one.
var RealHausdorff = realHausdorffThm{family.Add(registry.ProofEntry{
	Name: "RealHausdorff",
	Key:  "prop_9a7a6a507a0a7dea",
	Build: family.Theorem(
		"hausdorff(real_topology)",
		Chain(Simp(Fwd(RealTopologyMetric)), By(metric_space.MetricHausdorff.Read(RealMetric)))),
})}
