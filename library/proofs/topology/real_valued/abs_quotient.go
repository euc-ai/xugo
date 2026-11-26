// abs_quotient.go — two more ways of combining continuous real functions
// on a space: the absolute value of one is continuous, the absolute value
// moving no more than its argument, and so is the quotient of one by a
// positive one, read through the rays: where the divisor is positive, the
// quotient lies below a value a exactly where f − a·g is negative.

package real_valued

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousRealAbs — the absolute value of a continuous real function is
// continuous: the absolute value is jointly continuous as a function of
// its first argument, since it moves by no more than its argument does.
var ContinuousRealAbs = continuousRealAbsThm{family.Add(registry.ProofEntry{
	Name: "ContinuousRealAbs",
	Key:  "prop_bc644195489ced8a",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f:(A → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, real_topology, f)",
		},
		Conclusion: "continuous_map(T, real_topology, λx:A. |f(x)|)",
	}, func(a *Argument, T *Expr[Set[Set[A]]], f *Arrow[A, Real], h Fact) {
		estimate := a.Have(
			"moving a real by less than ε moves its absolute value by less than ε",
			"∀a b ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ (∀c d:real. |c - a| < δ ∧ |d - b| < δ ⇒ ||c| - |a|| < ε)",
			Derive(func(arg *Argument) {
				arg.FixAs[Real]("a")
				arg.FixAs[Real]("b")
				ε := arg.FixAs[Real]("ε")
				positive := arg.Assume()
				arg.Take(ε)
				arg.Show(
					"ε itself serves, by the triangle inequality",
					ByArith(positive))
			}))
		a.Show(
			"the absolute value is carried along f",
			By(h, estimate, ContinuousRealJoint.At(T, f, f, a.TermAs[Op[Real]]("λa:real. λb:real. |a|"))))
	}),
})}

// ContinuousRealDiv — the quotient of a continuous real function f by a
// positive continuous real function g is continuous. It is read through
// the rays: at a value a, g being positive, f/g lies below a exactly
// where f − a·g is negative and above a exactly where f − a·g is
// positive, and f − a·g is continuous.
var ContinuousRealDiv = continuousRealDivThm{family.Add(registry.ProofEntry{
	Name: "ContinuousRealDiv",
	Key:  "prop_b08472aa73756828",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀f g:(A → real).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, real_topology, f)",
			"continuous_map(T, real_topology, g)",
			"∀x:A. x ∈ ⋃T ⇒ &0 < g(x)",
		},
		Conclusion: "continuous_map(T, real_topology, λx:A. f(x) / g(x))",
	}, func(
		arg *Argument,
		T *Expr[Set[Set[A]]],
		f, g *Arrow[A, Real],
		topology, fContinuous, gContinuous, positive Fact,
	) {
		line := arg.TermAs[Set[Set[Real]]]("real_topology")
		rays := arg.Have(
			"the points where f/g lies below a value, and those where it lies above it, form open sets",
			"∀a:real. {x:A | x ∈ ⋃T ∧ f(x) / g(x) < a} ∈ T ∧ {x:A | x ∈ ⋃T ∧ a < f(x) / g(x)} ∈ T",
			Derive(func(b *Argument) {
				a := b.FixAs[Real]("a")
				gap := b.Have(
					"f − a·g is continuous",
					"continuous_map(T, real_topology, λx:A. f(x) - a * g(x))",
					By(
						topology,
						fContinuous,
						gContinuous,
						ContinuousRealSub.At(T, f, b.TermAs[Fun[A, Real]]("λx:A. a * g(x)")),
						ContinuousRealMul.At(T, b.TermAs[Fun[A, Real]]("λx:A. a"), g),
						continuous.Constant.At(T, line, a),
						real_topology.RealSpace,
						set_basic.InUniv))
				gapRays := b.Conjuncts(
					b.Simplified(gap, Fwd(ContinuousIntoRealIff)),
					"the points where f − a·g lies below a value form an open set",
					"and so do those where it lies above one")
				sides := b.Have(
					"g being positive, f/g lies below a where f − a·g is negative and above a where it is positive",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ ⋃T",
						},
						Conclusion: "(f(x) / g(x) < a ⇔ f(x) - a * g(x) < &0) ∧ (a < f(x) / g(x) ⇔ &0 < f(x) - a * g(x))",
					},
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						xIn := c.Assume()
						c.Show(
							"cross-multiply by g(x)",
							ByArith(
								positive.At(x),
								xIn,
								real_order_field.LessThanDivMulRight.At(f.Apply(x), a, g.Apply(x)),
								real_order_field.LessThanDivMulLeft.At(a, f.Apply(x), g.Apply(x))))
					}))
				same := b.Have(
					"so the two sets are where f − a·g is negative and where it is positive",
					"{x:A | x ∈ ⋃T ∧ f(x) / g(x) < a} = {x:A | x ∈ ⋃T ∧ f(x) - a * g(x) < &0} ∧ "+
						"{x:A | x ∈ ⋃T ∧ a < f(x) / g(x)} = {x:A | x ∈ ⋃T ∧ &0 < f(x) - a * g(x)}",
					BySets(sides))
				zero := b.TermAs[Real]("&0")
				b.Show(
					"which are open, f − a·g being continuous",
					By(same, gapRays[0].At(zero), gapRays[1].At(zero)))
			}))
		arg.Show(
			"so f/g is continuous",
			By(ContinuousIntoRealIff.At(T, arg.TermAs[Fun[A, Real]]("λx:A. f(x) / g(x)")), topology, rays))
	}),
})}
