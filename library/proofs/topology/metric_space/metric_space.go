// metric_space.go — the structure and its axioms, what the axioms say
// about the distance alone, and the balls about a point.

package metric_space

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its axioms
// ---------------------------------------------------------------------------

// MetricSpace — a metric space is a set M of points of a type A with a
// distance d between any two of them: the distance vanishes exactly
// between a point and itself, reads the same both ways, and never
// exceeds the length of a detour through a third point. Two components,
// the carrier and the distance, since a distance does not determine its
// carrier (the README says why that matters). That a distance is never
// negative is a theorem, not a fourth axiom.
var MetricSpace = metricSpaceThm{family.DefineStructure(registry.DefEntry{
	Name:    "MetricSpace",
	Key:     "prop_18bf2017c71899c4",
	Const:   "metric_space",
	Subject: "M",
	Type:    "set(A) → (A → A → real) → bool",
	Equations: []string{
		"∀M:set(A). ∀d:(A → A → real). " +
			"    metric_space(M, d) ⇔ " +
			"    (∀x y:A. x ∈ M ∧ y ∈ M ⇒ (d(x, y) = &0 ⇔ x = y)) ∧ " +
			"    (∀x y:A. x ∈ M ∧ y ∈ M ⇒ d(x, y) = d(y, x)) ∧ " +
			"    (∀x y z:A. x ∈ M ∧ y ∈ M ∧ z ∈ M ⇒ d(x, z) ≤ d(x, y) + d(y, z))",
	},
	// The mints of the constants the definiens spells: membership, the
	// embedding `&`, `≤` and `+` on the reals.
})}

// DistZeroIff — two points are at distance zero exactly when they are
// one point.
var DistZeroIff = distZeroIffThm{family.Add(registry.ProofEntry{
	Name: "DistZeroIff",
	Key:  "prop_3b7e5782816f7d25",
	Build: MetricSpace.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ M",
			"y ∈ M",
		},
		Conclusion: "d(x, y) = &0 ⇔ x = y",
	}),
})}

// DistSym — the distance reads the same both ways.
var DistSym = distSymThm{family.Add(registry.ProofEntry{
	Name: "DistSym",
	Key:  "prop_e1090bd379574aa7",
	Build: MetricSpace.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ M",
			"y ∈ M",
		},
		Conclusion: "d(x, y) = d(y, x)",
	}),
})}

// DistTriangle — a detour through a third point is never shorter.
var DistTriangle = distTriangleThm{family.Add(registry.ProofEntry{
	Name: "DistTriangle",
	Key:  "prop_a8faa6cbb7c466da",
	Build: MetricSpace.Axiom(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ M",
			"y ∈ M",
			"z ∈ M",
		},
		Conclusion: "d(x, z) ≤ d(x, y) + d(y, z)",
	}),
})}

// ---------------------------------------------------------------------------
// The distance
// ---------------------------------------------------------------------------

// DistSelf — a point is at distance zero from itself: the first axiom,
// read from right to left at a point and itself.
var DistSelf = distSelfThm{family.Add(registry.ProofEntry{
	Name: "DistSelf",
	Key:  "prop_dffe7be6b00e3a36",
	Build: MetricSpace.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ M",
		},
		Conclusion: "d(x, x) = &0",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], x *Member[A, on.M]) {
			xM := x
			a.Show(
				"a point and itself are at distance zero, x being x",
				By(DistZeroIff.Read(metric).At(xM, xM)))
		}),
})}

// DistNonneg — a distance is never negative. Going from x to y and
// back is a detour from x to itself, so it is at least d(x, x), which
// is zero; the way back is as long as the way out, so twice d(x, y) is
// at least zero.
var DistNonneg = distNonnegThm{family.Add(registry.ProofEntry{
	Name: "DistNonneg",
	Key:  "prop_1eb669c0c6c62820",
	Build: MetricSpace.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ M",
			"y ∈ M",
		},
		Conclusion: "&0 ≤ d(x, y)",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], x, y *Member[A, on.M]) {
			detour := a.Have(
				"the round trip through y is no shorter than staying at x",
				"d(x, x) ≤ d(x, y) + d(y, x)",
				By(DistTriangle, metric, x, y))
			stay := a.Have(
				"and staying at x covers no distance",
				"d(x, x) = &0",
				By(DistSelf, metric, x, y))
			back := a.Have(
				"the way back is as long as the way out",
				"d(y, x) = d(x, y)",
				By(DistSym, metric, x, y))
			a.Show(
				"so twice the distance is at least zero",
				ByArith(detour, stay, back))
		}),
})}

// ---------------------------------------------------------------------------
// Balls
// ---------------------------------------------------------------------------

// CentreInBall — a point of M lies in every ball of positive radius
// about it, being at distance zero from itself.
var CentreInBall = centreInBallThm{family.Add(registry.ProofEntry{
	Name: "CentreInBall",
	Key:  "prop_33c8a4eff55cdb62",
	Build: MetricSpace.Law(Statement{
		Binders: "∀x:A. ∀r:real.",
		Hypotheses: []string{
			"x ∈ M",
			"&0 < r",
		},
		Conclusion: "x ∈ ball(x, r)",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], x *Member[A, on.M], r *Expr[Real], positive Fact) {
			self := a.Have(
				"x is at distance zero from itself",
				"d(x, x) = &0",
				By(DistSelf.Read(metric).At(x)))
			a.Show(
				"which is below the radius, so x is a point of M within r of x",
				Simp(Fwd(BallDef)),
				ByArith(x, self, positive))
		}),
})}

// BallConcentric — a ball lies in every ball about the same point with
// a radius at least as large. Nothing is asked of the distance.
var BallConcentric = ballConcentricThm{family.Add(registry.ProofEntry{
	Name: "BallConcentric",
	Key:  "prop_6e719ca3d29538e1",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:A. ∀r s:real.",
		Hypotheses: []string{
			"r ≤ s",
		},
		Conclusion: "ball(M, d, x, r) ⊆ ball(M, d, x, s)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			x *Expr[A],
			r, s *Expr[Real],
			radii Fact,
		) {
			closer := a.Have(
				"a distance below r is below s, r being at most s",
				"∀y:A. d(x, y) < r ⇒ d(x, y) < s",
				a.ForEach(func(y *Expr[A]) Action { return ByArith(radii) }))
			a.Show(
				"so a point of M within r of x is within s of it",
				Unfold(BallDef),
				BySets(closer))
		}),
})}

// CentreInClosedBall — a point of M lies in every closed ball about it
// of radius at least zero, being at distance zero from itself.
var CentreInClosedBall = centreInClosedBallThm{family.Add(registry.ProofEntry{
	Name: "CentreInClosedBall",
	Key:  "prop_875cd779b03e5dcb",
	Build: MetricSpace.Law(Statement{
		Binders: "∀x:A. ∀r:real.",
		Hypotheses: []string{
			"x ∈ M",
			"&0 ≤ r",
		},
		Conclusion: "x ∈ closed_ball(x, r)",
	},
		func(a *Argument, metric MetricSpaceFact[on.M], x *Member[A, on.M], r *Expr[Real], nonneg Fact) {
			self := a.Have(
				"x is at distance zero from itself",
				"d(x, x) = &0",
				By(DistSelf.Read(metric).At(x)))
			a.Show(
				"which is at most the radius, so x is a point of M within r of x",
				Simp(Fwd(ClosedBallDef)),
				ByArith(x, self, nonneg))
		}),
})}

// BallSubsetClosedBall — a ball lies in the closed ball of the same
// centre and radius, a distance below r being at most r. Nothing is
// asked of the distance.
var BallSubsetClosedBall = ballSubsetClosedBallThm{family.Add(registry.ProofEntry{
	Name: "BallSubsetClosedBall",
	Key:  "prop_56890e709e872d50",
	Build: family.Theorem("∀M:set(A). ∀d:(A → A → real). ∀x:A. ∀r:real. "+
		"    ball(M, d, x, r) ⊆ closed_ball(M, d, x, r)",
		func(a *Argument, M *Expr[Set[A]], d *Expr[Fun2[A, A, Real]], x *Expr[A], r *Expr[Real]) {
			weak := a.Have(
				"a distance below r is at most r",
				"∀y:A. d(x, y) < r ⇒ d(x, y) ≤ r",
				a.ForEach(func(y *Expr[A]) Action { return ByArith() }))
			a.Show(
				"so a point of M within r of x, strictly, is within r of it",
				Unfold(BallDef),
				Unfold(ClosedBallDef),
				BySets(weak))
		}),
})}

// ClosedBallSubsetBall — a closed ball lies in the ball about the same
// point of any larger radius. Nothing is asked of the distance.
var ClosedBallSubsetBall = closedBallSubsetBallThm{family.Add(registry.ProofEntry{
	Name: "ClosedBallSubsetBall",
	Key:  "prop_12fe1c3fb7c630aa",
	Build: family.Theorem(Statement{
		Binders: "∀M:set(A). ∀d:(A → A → real). ∀x:A. ∀r s:real.",
		Hypotheses: []string{
			"r < s",
		},
		Conclusion: "closed_ball(M, d, x, r) ⊆ ball(M, d, x, s)",
	},
		func(
			a *Argument,
			M *Expr[Set[A]],
			d *Expr[Fun2[A, A, Real]],
			x *Expr[A],
			r, s *Expr[Real],
			radii Fact,
		) {
			closer := a.Have(
				"a distance at most r is below s, r being below s",
				"∀y:A. d(x, y) ≤ r ⇒ d(x, y) < s",
				a.ForEach(func(y *Expr[A]) Action { return ByArith(radii) }))
			a.Show(
				"so a point of M within r of x is within s of it, strictly",
				Unfold(ClosedBallDef),
				Unfold(BallDef),
				BySets(closer))
		}),
})}
