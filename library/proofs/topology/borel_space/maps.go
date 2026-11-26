package borel_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

// BorelSigmaAlgebra — the Borel sets of a space form a σ-algebra on its
// points, and they hold its open sets: they are the σ-algebra the open
// sets generate on the points, each open set being a set of points.
var BorelSigmaAlgebra = borelSigmaAlgebraThm{family.Add(registry.ProofEntry{
	Name: "BorelSigmaAlgebra",
	Key:  "prop_684517e49acbdf56",
	Build: family.Theorem("∀T:set(set(A)). sigma_algebra_on(⋃T, borel_sets(T)) ∧ T ⊆ borel_sets(T)",
		func(a *Argument, T *Expr[Set[Set[A]]]) {
			generated := a.Have(
				"the Borel sets are the σ-algebra the open sets generate on the points",
				"borel_sets(T) = generated_sigma(⋃T, T)",
				Simp(Fwd(BorelSetsDef), Fwd(sigma_algebra.GeneratedSigmaDef)),
				Basic())
			opens := a.Have(
				"each open set is a set of points",
				"T ⊆ {s:set(A) | s ⊆ ⋃T}",
				BySets())
			a.Show(
				"a generated σ-algebra holds its generators",
				By(generated, opens, sigma_algebra.GeneratedSigmaAlgebra.At(a.TermAs[Set[A]]("⋃T"), T)))
		}),
})}

// ContinuousMapBorel — a continuous map between topological spaces is a
// Borel map. The Borel sets of a space are the σ-algebra its open sets
// generate on its points. The map carries the points of the source into
// those of the target (MapsInto) and pulls every open set of the target
// back to an open, hence Borel, set of the source (PreimageOpen), so it is
// measurable into the σ-algebra the target's open sets generate.
var ContinuousMapBorel = continuousMapBorelThm{family.Add(registry.ProofEntry{
	Name: "ContinuousMapBorel",
	Key:  "prop_4b60c6a0c5c5552a",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀U:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"is_topology(T)",
			"is_topology(U)",
			"continuous_map(T, U, f)",
		},
		Conclusion: "borel_map(T, U, f)",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		U *Expr[Set[Set[B]]],
		f *Arrow[A, B],
		sourceSpace, targetSpace, continuity Fact,
	) {
		borelSets := a.Have(
			"the Borel sets of a space are the σ-algebra its open sets generate on its points",
			"borel_sets(T) = generated_sigma(⋃T, T) ∧ borel_sets(U) = generated_sigma(⋃U, U)",
			Simp(Fwd(BorelSetsDef), Fwd(sigma_algebra.GeneratedSigmaDef)),
			Basic())
		opens := a.Have(
			"the open sets of a space are sets of its points",
			"T ⊆ {s:set(A) | s ⊆ ⋃T} ∧ U ⊆ {t:set(B) | t ⊆ ⋃U}",
			BySets())
		source := BorelSigmaAlgebra.At(T)
		into := a.Have(
			"f carries the points of T into the points of U",
			"image(f, ⋃T) ⊆ ⋃U",
			BySets(continuous.MapsInto.Read(continuity)))
		preimages := a.Have(
			"f pulls each open set of U back to an open, hence Borel, set of T",
			"∀t:set(B). t ∈ U ⇒ preimage_on(⋃T, f, t) ∈ borel_sets(T)",
			BySets(source, continuous.PreimageOpen.Read(continuity)))
		generated := a.Have(
			"so f is measurable into the σ-algebra the open sets of U generate",
			"measurable_map(⋃T, borel_sets(T), ⋃U, generated_sigma(⋃U, U), f)",
			By(source, opens, into, preimages, measurable_space.MeasurableGenerated))
		a.Show(
			"which is the Borel σ-algebra of U",
			Simp(Fwd(BorelMapDef)),
			By(Normalized, sourceSpace, targetSpace, borelSets, generated))
	}),
})}

// BorelMapCompose — Borel maps compose: both are measurable between the
// Borel σ-algebras of their spaces, and measurable maps compose.
var BorelMapCompose = borelMapComposeThm{family.Add(registry.ProofEntry{
	Name: "BorelMapCompose",
	Key:  "prop_f64f6f262daf70b6",
	Build: family.Theorem(Statement{
		Binders: "∀T:set(set(A)). ∀U:set(set(B)). ∀V:set(set(C)). ∀f:(A → B). ∀g:(B → C).",
		Hypotheses: []string{
			"borel_map(T, U, f)",
			"borel_map(U, V, g)",
		},
		Conclusion: "borel_map(T, V, g ∘ f)",
	}, func(
		a *Argument,
		T *Expr[Set[Set[A]]],
		U *Expr[Set[Set[B]]],
		V *Expr[Set[Set[C]]],
		f *Arrow[A, B],
		g *Arrow[B, C],
		fBorel, gBorel Fact,
	) {
		fParts := a.Conjuncts(
			a.Unfolded(fBorel, BorelMapDef),
			"T is a topology",
			"U is a topology",
			"f is measurable between the Borel sets of T and U")
		gParts := a.Conjuncts(
			a.Unfolded(gBorel, BorelMapDef),
			"U is a topology",
			"V is a topology",
			"g is measurable between the Borel sets of U and V")
		a.Show(
			"g ∘ f is measurable between the Borel sets of T and V",
			Simp(Fwd(BorelMapDef)),
			By(fParts[0], gParts[1], fParts[2], gParts[2], measurable_space.MeasurableCompose))
	}),
})}
