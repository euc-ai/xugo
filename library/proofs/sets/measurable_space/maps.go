package measurable_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// MeasurableIdentity — the identity is measurable from a family of subsets
// of Ω to itself: it keeps Ω, and each member, lying in Ω, is its own
// preimage.
var MeasurableIdentity = measurableIdentityThm{family.Add(registry.ProofEntry{
	Name: "MeasurableIdentity",
	Reading: "S ⊆ {s | s ⊆ Ω} is load-bearing: with Ω = {0} and S = " +
		"{{0, 1}}, the inverse image of {0, 1} is {0}, which is not in S.",
	Key: "prop_56480d20335cea41",
	Build: family.Theorem(Statement{Binders: "∀Ω:set(A). ∀S:set(set(A)).",
		Hypotheses: []string{"S ⊆ {s:set(A) | s ⊆ Ω}"},
		Conclusion: "measurable_map(Ω, S, Ω, S, λx:A. x)"},
		func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], inside Fact) {
			image := a.Have(
				"the identity maps Ω into Ω",
				"image(λx:A. x, Ω) ⊆ Ω",
				BySets())
			preimages := a.Have(
				"each member is its own preimage, a member",
				"∀t:set(A). t ∈ S ⇒ preimage_on(Ω, λx:A. x, t) ∈ S",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("t")
					member := b.Assume()
					itself := b.Have(
						"t lies in Ω, so its preimage under the identity is t",
						"preimage_on(Ω, λx:A. x, t) = t",
						BySets(member, inside))
					b.Show(
						"which is a member",
						By(Normalized, itself, member))
				}))
			a.Show(
				"so the identity is measurable",
				Simp(Fwd(MeasurableMapDef)),
				By(image, preimages))
		}),
})}

// MeasurableCompose — measurable maps compose: g ∘ f maps Ω into W, as f
// maps Ω into V and g maps V into W; and since f maps Ω into V, pulling a
// member of U back along g ∘ f is pulling it back along g into T, then
// along f into S.
var MeasurableCompose = measurableComposeThm{family.Add(registry.ProofEntry{
	Name: "MeasurableCompose",
	Reading: "No sigma algebra hypothesis is read. The carrier inclusion " +
		"image(f, Ω) ⊆ V lets the V-relative inverse image under g compose.",
	Key: "prop_6eeb3e2a79b9182a",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀W:set(C). " +
			"∀U:set(set(C)). " +
			"∀f:(A → B). " +
			"∀g:(B → C).",
		Hypotheses: []string{"measurable_map(Ω, S, V, T, f)", "measurable_map(V, T, W, U, g)"},
		Conclusion: "measurable_map(Ω, S, W, U, g ∘ f)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		V *Expr[Set[B]],
		T *Expr[Set[Set[B]]],
		W *Expr[Set[C]],
		U *Expr[Set[Set[C]]],
		f *Arrow[A, B],
		g *Arrow[B, C],
		fMeasurable, gMeasurable Fact,
	) {
		fParts := a.Conjuncts(
			a.Unfolded(fMeasurable, MeasurableMapDef),
			"f maps Ω into V",
			"f pulls the members of T back into S")
		gParts := a.Conjuncts(
			a.Unfolded(gMeasurable, MeasurableMapDef),
			"g maps V into W",
			"g pulls the members of U back into T")
		image := a.Have(
			"g ∘ f maps Ω into W",
			"image(g ∘ f, Ω) ⊆ W",
			BySets(fParts[0], gParts[0], functions.ComposeApply))
		preimages := a.Have(
			"g ∘ f pulls the members of U back into S",
			"∀u:set(C). u ∈ U ⇒ preimage_on(Ω, g ∘ f, u) ∈ S",
			Derive(func(b *Argument) {
				u := b.FixAs[Set[C]]("u")
				member := b.Assume()
				through := b.Have(
					"pulling u back along g ∘ f is pulling it back along g, then along f",
					"preimage_on(Ω, g ∘ f, u) = preimage_on(Ω, f, preimage_on(V, g, u))",
					BySets(fParts[0], functions.ComposeApply))
				b.Show(
					"g pulls u back into T, and f pulls that set back into S",
					By(
						Normalized,
						through,
						member,
						gParts[1].At(u),
						fParts[1].At(b.TermAs[Set[B]]("preimage_on(V, g, u)"))))
			}))
		a.Show(
			"so g ∘ f is measurable",
			Simp(Fwd(MeasurableMapDef)),
			By(image, preimages))
	}),
})}

// MeasurableGenerated — a map is measurable into the σ-algebra generated
// by C as soon as it maps Ω into V and pulls each generator back into S.
// The subsets of V whose preimages lie in S form a σ-algebra on V, since
// pulling back commutes with complements in V and countable unions and
// pulls V back to Ω; it holds the generators, so it holds the generated
// σ-algebra.
var MeasurableGenerated = measurableGeneratedThm{family.Add(registry.ProofEntry{
	Name: "MeasurableGenerated",
	Reading: "C ⊆ {t | t ⊆ V} keeps generated_sigma(V, C) a sigma algebra on V, " +
		"and image(f, Ω) ⊆ V makes complements in V pull back to complements in Ω.",
	Key: "prop_56c36539febd5801",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀V:set(B). ∀C:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"C ⊆ {t:set(B) | t ⊆ V}",
			"image(f, Ω) ⊆ V",
			"∀t:set(B). t ∈ C ⇒ preimage_on(Ω, f, t) ∈ S",
		},
		Conclusion: "measurable_map(Ω, S, V, generated_sigma(V, C), f)",
		Abbrev: Abbrev{
			{Name: "traced", Text: "{t:set(B) | t ⊆ V ∧ preimage_on(Ω, f, t) ∈ S}"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		V *Expr[Set[B]],
		C *Expr[Set[Set[B]]],
		f *Arrow[A, B],
		sigma, generators, into, preimages Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef),
			"the members of S lie in Ω",
			"Ω is a member",
			"the complement in Ω of a member is a member",
			"the union of a sequence of members is a member")
		whole := a.Have(
			"f pulls V back to Ω, mapping Ω into V",
			"preimage_on(Ω, f, V) = Ω",
			BySets(into))
		complement := a.Have(
			"pulling back along f turns complements in V into complements in Ω",
			"∀t:set(B). preimage_on(Ω, f, V ∖ t) = Ω ∖ preimage_on(Ω, f, t)",
			BySets(into))
		union := a.Have(
			"pulling back commutes with countable unions",
			"∀a:(num → set(B)). preimage_on(Ω, f, ⋃image(a, 𝕌)) = ⋃image(λn:num. preimage_on(Ω, f, a(n)), 𝕌)",
			BySets())
		inV := a.Have(
			"the traced sets lie in V",
			"«traced» ⊆ {u:set(B) | u ⊆ V}",
			BySets())
		carrier := a.Have(
			"V is traced, f pulling it back to the member Ω",
			"V ∈ «traced»",
			By(Normalized, whole, laws[1], set_order.SubsetRefl))
		complements := a.Have(
			"the complement in V of a traced set is traced",
			"∀u:set(B). u ∈ «traced» ⇒ V ∖ u ∈ «traced»",
			Derive(func(b *Argument) {
				u := b.FixAs[Set[B]]("u")
				member := b.Assume()
				b.Show(
					"its preimage is the complement in Ω of a member",
					By(Normalized, member, complement.At(u), laws[2], set_order.SubsetDiff))
			}))
		unions := a.Have(
			"the union of a sequence of traced sets is traced",
			"∀a:(num → set(B)). (∀n:num. a(n) ∈ «traced») ⇒ ⋃image(a, 𝕌) ∈ «traced»",
			Derive(func(b *Argument) {
				sequence := b.FixAs[Fun[Nat, Set[B]]]("a")
				terms := b.Assume()
				pieces := b.Have(
					"the union lies in V, and the preimages of its terms have a union in S",
					"⋃image(a, 𝕌) ⊆ V ∧ ⋃image(λn:num. preimage_on(Ω, f, a(n)), 𝕌) ∈ S",
					BySets(terms, laws[3]))
				b.Show(
					"which is the preimage of the union",
					By(pieces, union.At(sequence)))
			}))
		traced := a.Have(
			"so the traced sets form a σ-algebra on V",
			"sigma_algebra_on(V, «traced»)",
			Simp(Fwd(sigma_algebra.SigmaAlgebraOnDef)),
			By(inV, carrier, complements, unions))
		held := a.Have(
			"the generators are traced",
			"C ⊆ «traced»",
			BySets(generators, preimages))
		least := a.Have(
			"so the generated σ-algebra lies in the traced sets",
			"generated_sigma(V, C) ⊆ «traced»",
			By(traced, held, sigma_algebra.GeneratedSigmaLeast))
		a.Show(
			"f maps Ω into V and pulls every generated set back into S",
			Simp(Fwd(MeasurableMapDef)),
			BySets(into, least))
	}),
})}

// MeasurableCongruence — a map agreeing on Ω with a measurable map is
// measurable: the two have the same image of Ω and pull every set back to
// the same subset of Ω.
var MeasurableCongruence = measurableCongruenceThm{family.Add(registry.ProofEntry{
	Name: "MeasurableCongruence",
	Key:  "prop_25b73fcb1f0757ca",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀V:set(B). ∀T:set(set(B)). ∀f g:(A → B).",
		Hypotheses: []string{"measurable_map(Ω, S, V, T, f)", "∀x:A. x ∈ Ω ⇒ f(x) = g(x)"},
		Conclusion: "measurable_map(Ω, S, V, T, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		V *Expr[Set[B]],
		T *Expr[Set[Set[B]]],
		f, g *Arrow[A, B],
		measurable, agree Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(measurable, MeasurableMapDef),
			"f maps Ω into V",
			"f pulls the members of T back into S")
		image := a.Have(
			"g maps Ω into V, agreeing there with f",
			"image(g, Ω) ⊆ V",
			BySets(agree, parts[0]))
		preimages := a.Have(
			"g pulls the members of T back into S",
			"∀t:set(B). t ∈ T ⇒ preimage_on(Ω, g, t) ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Set[B]]("t")
				member := b.Assume()
				same := b.Have(
					"g and f pull t back to the same subset of Ω",
					"preimage_on(Ω, g, t) = preimage_on(Ω, f, t)",
					BySets(agree))
				b.Show(
					"which f pulls into S",
					By(Normalized, same, member, parts[1]))
			}))
		a.Show(
			"so g is measurable",
			Simp(Fwd(MeasurableMapDef)),
			By(image, preimages))
	}),
})}
