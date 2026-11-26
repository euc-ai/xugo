// borel.go — the Borel sets and Borel functions of the real line. The Borel
// sets form a σ-algebra on the line, holding its rays and closed intervals;
// the identity and every function continuous on the line are Borel
// measurable; a Borel function composed after a measurable real function is
// measurable; and a real function generates a σ-algebra, the preimages of
// the Borel sets, inside which a Borel function of it generates its own.

package borel_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/proofs/topology/borel_space"
	"github.com/euc-ai/xugo/library/registry"
)

// LineBorelSigmaAlgebra — the Borel sets of the line form a σ-algebra on
// it, the line's points being all the reals.
var LineBorelSigmaAlgebra = lineBorelSigmaAlgebraThm{family.Add(registry.ProofEntry{
	Name: "LineBorelSigmaAlgebra",
	Key:  "prop_605f6c555effc07b",
	Build: family.Theorem("sigma_algebra_on(𝕌, borel_sets(real_topology))",
		func(a *Argument) {
			a.Show(
				"the Borel sets of a space are a σ-algebra on its points, and the line's points are all the reals",
				By(
					borel_space.BorelSigmaAlgebra.At(a.TermAs[Set[Set[Real]]]("real_topology")),
					real_topology.RealSpace))
		}),
})}

// RaysBorel — the rays {x | x ≤ b} and {x | b < x} of the line are Borel:
// the open ray is open (RayAboveOpen), hence Borel, and the closed ray is
// its complement in the line.
var RaysBorel = raysBorelThm{family.Add(registry.ProofEntry{
	Name: "RaysBorel",
	Key:  "prop_db0fae3cb8fadf3c",
	Build: family.Theorem(
		"∀b:real. "+
			"    {x:real | x ≤ b} ∈ borel_sets(real_topology) ∧ {x:real | b < x} ∈ borel_sets(real_topology)",
		func(arg *Argument, b *Expr[Real]) {
			line := arg.TermAs[Set[Real]]("𝕌")
			borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			open := arg.Have(
				"the open ray is open, hence Borel",
				"{x:real | b < x} ∈ borel_sets(real_topology)",
				BySets(
					borel_space.BorelSigmaAlgebra.At(arg.TermAs[Set[Set[Real]]]("real_topology")),
					real_topology.RayAboveOpen.At(b)))
			complement := arg.Have(
				"the closed ray is the complement of the open ray",
				"{x:real | x ≤ b} = 𝕌 ∖ {x:real | b < x}",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(d *Argument) {
					x := d.FixAs[Real]("x")
					d.Show(
						"x ≤ b exactly when b < x fails",
						BySets(real_order_ring.NotLessThan.At(b, x)))
				}))
			arg.Show(
				"and a σ-algebra on the line holds the complement of each of its sets",
				By(
					LineBorelSigmaAlgebra,
					open,
					complement,
					sigma_algebra.SigmaFiniteOperations.At(
						line, borel),
					sigma_algebra.SigmaAlgebraOnDef.At(line, borel)))
		}),
})}

// ClosedIntervalBorel — a closed interval ⟦a, b⟧ of the line is Borel: it
// is what the line leaves outside the open rays {x | x < a} and
// {x | b < x}, both open and so Borel.
var ClosedIntervalBorel = closedIntervalBorelThm{family.Add(registry.ProofEntry{
	Name: "ClosedIntervalBorel",
	Key:  "prop_758f1d5d3aede55",
	Build: family.Theorem("∀a b:real. ⟦a, b⟧ ∈ borel_sets(real_topology)",
		func(arg *Argument, a, b *Expr[Real]) {
			line := arg.TermAs[Set[Real]]("𝕌")
			borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			rays := arg.Have(
				"the two outer rays are open, hence Borel",
				"{x:real | x < a} ∈ borel_sets(real_topology) ∧ {x:real | b < x} ∈ borel_sets(real_topology)",
				BySets(
					borel_space.BorelSigmaAlgebra.At(arg.TermAs[Set[Set[Real]]]("real_topology")),
					real_topology.RayBelowOpen.At(a),
					real_topology.RayAboveOpen.At(b)))
			complement := arg.Have(
				"⟦a, b⟧ is what the line leaves outside the two rays",
				"⟦a, b⟧ = 𝕌 ∖ ({x:real | x < a} ∪ {x:real | b < x})",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(d *Argument) {
					x := d.FixAs[Real]("x")
					d.Show(
						"a ≤ x ≤ b exactly when neither x < a nor b < x",
						BySets(real_order_ring.NotLessThan.At(b, x), real_order_ring.NotLessThan.At(x, a)))
				}))
			arg.Show(
				"and a σ-algebra on the line holds unions and complements",
				By(
					LineBorelSigmaAlgebra,
					rays,
					complement,
					sigma_algebra.SigmaFiniteOperations.At(
						line, borel),
					sigma_algebra.SigmaAlgebraOnDef.At(line, borel)))
		}),
})}

// RealMeasurableIdentity — the identity of the line is Borel measurable:
// every Borel set is a set of reals, so it is its own preimage.
var RealMeasurableIdentity = realMeasurableIdentityThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableIdentity",
	Key:  "prop_8a1dd33391554cca",
	Build: family.Theorem("real_measurable(𝕌, borel_sets(real_topology), λx:real. x)",
		func(a *Argument) {
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			a.Show(
				"the identity is a measurable map of the line to itself",
				BySets(
					measurable_space.MeasurableIdentity.At(line, borel),
					measurable_function.RealMeasurableDef.At(line, borel, a.TermAs[Fun[Real, Real]]("λx:real. x"))))
		}),
})}

// ContinuousBorelMeasurable — a function continuous on the line is Borel
// measurable: continuity on the whole line is continuity for its topology
// (ContinuousOnUnivIffMap), and a continuous map is a Borel map
// (ContinuousMapBorel), measurable between the Borel sets of the line.
var ContinuousBorelMeasurable = continuousBorelMeasurableThm{family.Add(registry.ProofEntry{
	Name: "ContinuousBorelMeasurable",
	Key:  "prop_d9c7167ab9e8cb7a",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real).",
		Hypotheses: []string{
			"real_continuous_on(𝕌, f)",
		},
		Conclusion: "real_measurable(𝕌, borel_sets(real_topology), f)",
	},
		func(arg *Argument, f *Arrow[Real, Real], continuous Fact) {
			line := arg.TermAs[Set[Real]]("𝕌")
			topology := arg.TermAs[Set[Set[Real]]]("real_topology")
			borel := arg.Have(
				"continuity on the line is continuity for its topology, and a continuous map is a Borel map",
				"borel_map(real_topology, real_topology, f)",
				By(
					continuous,
					real_continuous.ContinuousOnUnivIffMap.At(f),
					real_topology.RealTopology,
					borel_space.ContinuousMapBorel.At(topology, topology, f)))
			arg.Show(
				"measurable between the Borel sets of the line",
				By(
					Normalized,
					borel,
					real_topology.RealSpace,
					borel_space.BorelMapDef.At(topology, topology, f),
					measurable_function.RealMeasurableDef.At(
						line, arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), f)))
		}),
})}

// RealMeasurableCompose — a Borel function of a measurable function is
// measurable: the composite of the measurable map u into the Borel line and
// the Borel measurable f pulls each Borel set back into S.
var RealMeasurableCompose = realMeasurableComposeThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableCompose",
	Key:  "prop_58dcbf93ca5716af",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀u:(A → real). ∀f:(real → real).",
		Hypotheses: []string{
			"real_measurable(Ω, S, u)",
			"real_measurable(𝕌, borel_sets(real_topology), f)",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. f(u(x)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		u *Arrow[A, Real],
		f *Arrow[Real, Real],
		inner, outer Fact,
	) {
		line := a.TermAs[Set[Real]]("𝕌")
		borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
		a.Show(
			"measurable maps compose",
			By(
				inner,
				outer,
				measurable_space.MeasurableCompose.At(Ω, S, line, borel, line, borel, u, f),
				measurable_function.RealMeasurableDef.At(Ω, S, u),
				measurable_function.RealMeasurableDef.At(line, borel, f),
				measurable_function.RealMeasurableDef.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. f(u(x))")),
				functions.ComposeApply.At(f, u)))
	}),
})}

// RealPullbackSigma — a real function X on Ω generates a σ-algebra there,
// the preimages on Ω of the Borel sets: it is a σ-algebra on Ω, X is
// measurable for it, and it lies in every family that makes X measurable.
// Real measurability is measurability into the line with its Borel
// σ-algebra, and X maps Ω into the line, so this is the pullback of a
// σ-algebra.
var RealPullbackSigma = realPullbackSigmaThm{family.Add(registry.ProofEntry{
	Name: "RealPullbackSigma",
	Key:  "prop_eb1f2715b56c9817",
	Build: family.Theorem("∀Ω:set(A). ∀X:(A → real). "+
		"    sigma_algebra_on(Ω, pullback_sigma(Ω, X, borel_sets(real_topology))) ∧ "+
		"    real_measurable(Ω, pullback_sigma(Ω, X, borel_sets(real_topology)), X) ∧ "+
		"    (∀S:set(set(A)). "+
		"        real_measurable(Ω, S, X) ⇒ pullback_sigma(Ω, X, borel_sets(real_topology)) ⊆ S)",
		func(a *Argument, Ω *Expr[Set[A]], X *Arrow[A, Real]) {
			a.Show(
				"the pullback of the Borel σ-algebra of the line, into which X maps Ω",
				Simp(Fwd(measurable_function.RealMeasurableDef)),
				By(
					LineBorelSigmaAlgebra,
					measurable_space.PullbackSigmaAlgebra.At(
						Ω, a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), X),
					set_order.SubsetUniv))
		}),
})}

// RealPullbackCompose — a Borel function h of X generates a σ-algebra inside
// the one X generates: X is measurable for its own σ-algebra, so h ∘ X is
// too, and the σ-algebra h ∘ X generates lies in every family that makes
// it measurable.
var RealPullbackCompose = realPullbackComposeThm{family.Add(registry.ProofEntry{
	Name: "RealPullbackCompose",
	Key:  "prop_561011ad19f0408",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀X:(A → real). ∀h:(real → real).",
		Hypotheses: []string{
			"real_measurable(𝕌, borel_sets(real_topology), h)",
		},
		Conclusion: "pullback_sigma(Ω, λx:A. h(X(x)), borel_sets(real_topology)) ⊆ " +
			"pullback_sigma(Ω, X, borel_sets(real_topology))",
	}, func(a *Argument, Ω *Expr[Set[A]], X *Arrow[A, Real], h *Arrow[Real, Real], hBorel Fact) {
		through := a.Have(
			"h ∘ X is measurable for the σ-algebra X generates, X being measurable for it and h Borel",
			"real_measurable(Ω, pullback_sigma(Ω, X, borel_sets(real_topology)), λx:A. h(X(x)))",
			By(hBorel, RealPullbackSigma.At(Ω, X), RealMeasurableCompose))
		a.Show(
			"and the σ-algebra h ∘ X generates lies in every family that makes it measurable",
			By(through, RealPullbackSigma.At(Ω, a.TermAs[Fun[A, Real]]("λx:A. h(X(x))"))))
	}),
})}
