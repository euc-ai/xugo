// algebra.go — the algebra of continuity (README, "The algebra of
// continuity"): constants and the identity, and sums, negatives, sizes,
// differences, products and composites of functions continuous on a set;
// products and composites of functions continuous at a point.

package real_continuous

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousOnConst — a constant function is continuous on every set.
//
// Its values are all k, at distance |k − k| = 0 from its value at any
// point c, so every positive radius answers every ε; ε itself is taken.
var ContinuousOnConst = continuousOnConstThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnConst",
	Key:  "prop_14898d8e3e18ef25",
	Build: family.Theorem("∀k:real. ∀s:set(real). real_continuous_on(s, λx:real. k)",
		func(a *Argument, k *Expr[Real], s *Expr[Set[Real]]) {
			a.Do(Unfold(RealContinuousOnDef))
			a.FixAs[Real]()
			a.Assume()
			eps := a.FixAs[Real]()
			pos := a.Assume()
			a.Take(eps)
			a.Show(
				"the radius ε is positive, and inside it the value "+
					"k is at distance |k − k| = 0 < ε from the value at c",
				ByArith(pos))
		}),
})}

// ContinuousOnId — the identity is continuous on every set: within ε of
// c it stays within ε of c, so ε itself is the radius.
var ContinuousOnId = continuousOnIdThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnId",
	Key:  "prop_5da465863bbb477c",
	Build: family.Theorem("∀s:set(real). real_continuous_on(s, λx:real. x)",
		func(a *Argument, s *Expr[Set[Real]]) {
			a.Do(Unfold(RealContinuousOnDef))
			a.FixAs[Real]()
			a.Assume()
			eps := a.FixAs[Real]()
			pos := a.Assume()
			a.Take(eps)
			a.Show(
				"the radius ε is positive, and a point within ε of c has its value within ε of c's",
				ByArith(pos))
		}),
})}

// ContinuousOnAdd — the sum of two functions continuous on s is
// continuous on s, by the sum law for continuous maps from the subspace s.
var ContinuousOnAdd = continuousOnAddThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnAdd",
	Key:  "prop_8b23a6a8e2835fbb",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
			"real_continuous_on(s, g)",
		},
		Conclusion: "real_continuous_on(s, λx:real. f(x) + g(x))",
	},
		func(a *Argument, f, g *Arrow[Real, Real], s *Expr[Set[Real]], continuous Fact) {
			sum := a.TermAs[Fun[Real, Real]]("λx:real. f(x) + g(x)")
			a.Show(
				"the sum of two continuous maps from the subspace s to the line is continuous",
				By(
					continuous,
					ContinuousOnIffMap.At(f, s),
					ContinuousOnIffMap.At(g, s),
					ContinuousOnIffMap.At(sum, s),
					real_valued.ContinuousRealAdd,
					topological_space.SubtopologyTopology.Read(real_topology.RealTopology)))
		}),
})}

// ContinuousOnNeg — the negative of a function continuous on s is
// continuous on s, by the negation law for continuous maps from the subspace s.
var ContinuousOnNeg = continuousOnNegThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnNeg",
	Key:  "prop_8e3eb80f1edcf9f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
		},
		Conclusion: "real_continuous_on(s, λx:real. -f(x))",
	},
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], continuous Fact) {
			negative := a.TermAs[Fun[Real, Real]]("λx:real. -f(x)")
			a.Show(
				"the negative of a continuous map from the subspace s to the line is continuous",
				By(
					continuous,
					ContinuousOnIffMap.At(f, s),
					ContinuousOnIffMap.At(negative, s),
					real_valued.ContinuousRealNeg,
					topological_space.SubtopologyTopology.Read(real_topology.RealTopology)))
		}),
})}

// ContinuousOnAbs — the size of a function continuous on s is continuous
// on s, by the size law for continuous maps from the subspace s.
var ContinuousOnAbs = continuousOnAbsThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnAbs",
	Key:  "prop_882d5651e25de5ee",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
		},
		Conclusion: "real_continuous_on(s, λx:real. |f(x)|)",
	},
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], continuous Fact) {
			size := a.TermAs[Fun[Real, Real]]("λx:real. |f(x)|")
			a.Show(
				"the size of a continuous map from the subspace s to the line is continuous",
				By(
					continuous,
					ContinuousOnIffMap.At(f, s),
					ContinuousOnIffMap.At(size, s),
					real_valued.ContinuousRealAbs,
					topological_space.SubtopologyTopology.Read(real_topology.RealTopology)))
		}),
})}

// ContinuousOnSub — the difference of two functions continuous on s is
// continuous on s.
//
// f − g is f + (−g), and −g is continuous on s with g.
var ContinuousOnSub = continuousOnSubThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnSub",
	Key:  "prop_fcf960d861f6dd6",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
			"real_continuous_on(s, g)",
		},
		Conclusion: "real_continuous_on(s, λx:real. f(x) - g(x))",
	},
		func(a *Argument, f, g *Arrow[Real, Real], s *Expr[Set[Real]], continuous Fact) {
			negG := a.Have(
				"g is continuous on s, so its negative is",
				"real_continuous_on(s, λx:real. -g(x))",
				By(ContinuousOnNeg, continuous))
			a.Do(Simp(Fwd(real_ring.RealSubDef)))
			a.Show(
				"f and −g are continuous on s, so f + (−g) is",
				By(ContinuousOnAdd, continuous, negG))
		}),
})}

// ContinuousOnMul — the product of two functions continuous on a set is
// continuous on it.
//
// Continuity on s is continuity as a map from the subspace s to the line,
// a subspace of a topological space is a topological space, and a product
// of two continuous real-valued maps on a topological space is continuous.
var ContinuousOnMul = continuousOnMulThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnMul",
	Key:  "prop_db082e62b5bd4d5f",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
			"real_continuous_on(s, g)",
		},
		Conclusion: "real_continuous_on(s, λx:real. f(x) * g(x))",
	},
		func(a *Argument, f, g *Arrow[Real, Real], s *Expr[Set[Real]], fContinuous, gContinuous Fact) {
			product := a.TermAs[Fun[Real, Real]]("λx:real. f(x) * g(x)")
			a.Show(
				"the product of two continuous maps from the subspace s to the line is continuous",
				By(
					fContinuous,
					gContinuous,
					ContinuousOnIffMap.At(f, s),
					ContinuousOnIffMap.At(g, s),
					ContinuousOnIffMap.At(product, s),
					real_valued.ContinuousRealMul,
					topological_space.SubtopologyTopology.Read(real_topology.RealTopology)))
		}),
})}

// ContinuousAtMul — the product of two functions continuous at c is
// continuous at c.
//
// Continuity at c is tending to the value at c, and the limit of a
// product is the product of the limits.
var ContinuousAtMul = continuousAtMulThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtMul",
	Key:  "prop_bd1faa580a6787d0",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c:real.",
		Hypotheses: []string{
			"real_continuous_at(f, c)",
			"real_continuous_at(g, c)",
		},
		Conclusion: "real_continuous_at(λx:real. f(x) * g(x), c)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c *Expr[Real], continuous Fact) {
			limits := a.Have(
				"f and g tend to their values at c",
				"f ⟶ f(c) (at c) ∧ g ⟶ g(c) (at c)",
				By(ContinuousAtIffLimit.At(f, c), ContinuousAtIffLimit.At(g, c), continuous))
			product := a.Have(
				"so f·g tends to f(c)·g(c), its value at c",
				"(λx:real. f(x) * g(x)) ⟶ f(c) * g(c) (at c)",
				By(real_function_limits.LimitAtMul, limits))
			a.Do(Simp(Fwd(ContinuousAtIffLimit)))
			a.Show(
				"continuity of f·g at c is that limit",
				By(product))
		}),
})}

// ContinuousAtCompose — a composite of continuous functions is
// continuous.
//
// Fix ε > 0. Continuity of f at g(c) answers ε with a radius η₀, inside
// which the values of f are within ε of f(g(c)); continuity of g at c,
// asked for η₀ as its ε, answers with a radius δ₀, inside which the
// values of g are within η₀ of g(c). So a point within δ₀ of c is carried
// by g within η₀ of g(c), and then by f within ε of f(g(c)). The limit
// form of the argument needs a case on g(x) = g(c), its balls being
// punctured; continuity's ball keeps its centre, so no case arises.
var ContinuousAtCompose = continuousAtComposeThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtCompose",
	Key:  "prop_89a257fb06fb0501",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c:real.",
		Hypotheses: []string{
			"real_continuous_at(g, c)",
			"real_continuous_at(f, g(c))",
		},
		Conclusion: "real_continuous_at(f ∘ g, c)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c *Expr[Real], given Fact) {
			parts := a.Conjuncts(
				given,
				"g is continuous at c",
				"f is continuous at g(c)")
			gNear := a.Unfolded(parts[0], RealContinuousAtDef)
			fNear := a.Unfolded(parts[1], RealContinuousAtDef)

			// The goal read as its ε-δ statement, and `o` unfolded so that the
			// values of f ∘ g are the values f(g(x)).
			a.Do(Unfold(RealContinuousAtDef), Unfold(functions.ComposeApply))
			eps := a.FixAs[Real]()
			pos := a.Assume()
			eta, fRadius := a.ObtainAs[Real](
				"continuity of f at g(c) answers ε with a radius η₀ "+
					"inside which the values of f are within ε of f(g(c))",
				"∃η:real. &0 < η ∧ ∀y:real. |y - g(c)| < η ⇒ |f(y) - f(g(c))| < ε",
				By(fNear.At(eps), pos))
			fHeld := a.Conjuncts(
				fRadius,
				"η₀ is positive",
				"inside η₀ around g(c) the values of f are within ε of f(g(c))")
			d0, gRadius := a.ObtainAs[Real](
				"continuity of g at c, asked for the positive radius η₀ as its ε, answers "+
					"with a radius δ₀ inside which the values of g are within η₀ of g(c)",
				"∃δ:real. &0 < δ ∧ ∀x:real. |x - c| < δ ⇒ |g(x) - g(c)| < η₀",
				By(gNear.At(eta), fHeld[0]))
			gHeld := a.Conjuncts(
				gRadius,
				"δ₀ is positive",
				"inside δ₀ around c the values of g are within η₀ of g(c)")

			a.Take(d0)
			a.Do(SplitConj(
				Case(
					"the radius δ₀ is positive",
					By(gHeld[0])),
				Case(
					"and f ∘ g carries a point within δ₀ of c within ε of f(g(c))",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						inside := b.Assume()
						b.Show(
							"g carries x within η₀ of g(c), and f carries g(x) within ε of f(g(c))",
							By(gHeld[1].At(x), fHeld[1].At(g.Apply(x)), inside))
					})),
			))
		}),
})}

// ContinuousOnCompose — f continuous on t after g continuous on s, g
// mapping s into t, is continuous on s. The image condition makes g a
// continuous map between the subspaces s and t, so the map composition
// law applies before continuity is read back on s.
var ContinuousOnCompose = continuousOnComposeThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnCompose",
	Key:  "prop_f7eafdf44ca3004c",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀s t:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, g)",
			"real_continuous_on(t, f)",
			"∀x:real. x ∈ s ⇒ g(x) ∈ t",
		},
		Conclusion: "real_continuous_on(s, f ∘ g)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], s, t *Expr[Set[Real]], given Fact) {
			subspaceS := a.TermAs[Set[Set[Real]]]("subtopology(s)")
			subspaceT := a.TermAs[Set[Set[Real]]]("subtopology(t)")
			line := a.TermAs[Set[Set[Real]]]("real_topology")
			composite := a.TermAs[Fun[Real, Real]]("f ∘ g")
			a.Show(
				"g maps the subspace s continuously into t, so composing with f gives a continuous map to the line",
				BySets(
					given,
					ContinuousOnIffMap.At(g, s),
					ContinuousOnIffMap.At(f, t),
					ContinuousOnIffMap.At(composite, s),
					topological_space.SubtopologySpace.At(line, s),
					continuous.IntoSubtopology.At(subspaceS, line, g, t),
					continuous.Compose.At(subspaceS, subspaceT, g, line, f)))
		}),
})}
