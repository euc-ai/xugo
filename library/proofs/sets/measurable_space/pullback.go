package measurable_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// PullbackSigmaAlgebra — the inverse images under f of the members of a
// σ-algebra T on V form a σ-algebra on Ω when f maps Ω into V; f is
// measurable from it into T, and it lies in every family that makes f
// measurable. Inverse images on Ω commute with complements in V and with
// countable unions: the union of a sequence of inverse images is the
// inverse image of the union of sets chosen in T, one for each term.
var PullbackSigmaAlgebra = pullbackSigmaAlgebraThm{family.Add(registry.ProofEntry{
	Name: "PullbackSigmaAlgebra",
	Reading: "image(f, Ω) ⊆ V is load-bearing three times: it gives Ω = f⁻¹(V) as " +
		"a member, Ω ∖ f⁻¹(t) = f⁻¹(V ∖ t), and the first clause of measurable_map. " +
		"The clause of sigma_algebra_on(V, T) that its members lie in V is not read.",
	Key: "prop_89b4afd47e35e848",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀V:set(B). ∀T:set(set(B)). ∀f:(A → B).",
		Hypotheses: []string{"sigma_algebra_on(V, T)", "image(f, Ω) ⊆ V"},
		Conclusion: "sigma_algebra_on(Ω, pullback_sigma(Ω, f, T)) ∧ " +
			"measurable_map(Ω, pullback_sigma(Ω, f, T), V, T, f) ∧ " +
			"(∀S:set(set(A)). measurable_map(Ω, S, V, T, f) ⇒ pullback_sigma(Ω, f, T) ⊆ S)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		V *Expr[Set[B]],
		T *Expr[Set[Set[B]]],
		f *Arrow[A, B],
		sigma, into Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef),
			"the members of T lie in V",
			"V is a member",
			"the complement in V of a member is a member",
			"the union of a sequence of members is a member")
		preimages := a.Have(
			"f pulls each member of T back to a member of the pullback",
			"∀t:set(B). t ∈ T ⇒ preimage_on(Ω, f, t) ∈ pullback_sigma(Ω, f, T)",
			Simp(Fwd(PullbackSigmaDef)),
			By(set_image.FunInImage))
		members := a.Have(
			"each member of the pullback is the preimage of a member of T",
			"∀s:set(A). s ∈ pullback_sigma(Ω, f, T) ⇒ ∃t:set(B). t ∈ T ∧ s = preimage_on(Ω, f, t)",
			Simp(Fwd(PullbackSigmaDef)),
			BySets())
		inside := a.Have(
			"the members of the pullback lie in Ω, as every preimage on Ω does",
			"pullback_sigma(Ω, f, T) ⊆ {u:set(A) | u ⊆ Ω}",
			Simp(Fwd(PullbackSigmaDef), Fwd(set_image.ImageSubsetIff)),
			BySets())
		whole := a.Have(
			"f pulls V back to Ω, mapping Ω into V",
			"preimage_on(Ω, f, V) = Ω",
			BySets(into))
		carrier := a.Have(
			"so Ω is a member, the preimage of the member V",
			"Ω ∈ pullback_sigma(Ω, f, T)",
			By(Normalized, whole, laws[1], preimages.At(V)))
		complements := a.Have(
			"the complement in Ω of a member is a member",
			"∀u:set(A). u ∈ pullback_sigma(Ω, f, T) ⇒ Ω ∖ u ∈ pullback_sigma(Ω, f, T)",
			Derive(func(b *Argument) {
				u := b.FixAs[Set[A]]("u")
				member := b.Assume()
				t, source := b.UnpackAs[Set[B]](GroupPremises(member, members.At(u)), "t")
				complement := b.Have(
					"f maps Ω into V, so the complement of u in Ω is the preimage of V ∖ t",
					"Ω ∖ u = preimage_on(Ω, f, V ∖ t)",
					BySets(into, source))
				b.Show(
					"and V ∖ t is a member of T",
					By(Normalized, complement, source, laws[2].At(t), preimages.At(b.TermAs[Set[B]]("V ∖ t"))))
			}))
		unions := a.Have(
			"the union of a sequence of members is a member",
			Statement{
				Binders:    "∀a:(num → set(A)).",
				Hypotheses: []string{"∀n:num. a(n) ∈ pullback_sigma(Ω, f, T)"},
				Conclusion: "⋃image(a, 𝕌) ∈ pullback_sigma(Ω, f, T)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, Set[A]]]("a")
				terms := b.Assume()
				c, chosen := b.ObtainAs[Fun[Nat, Set[B]]](
					"choose for each n a member c(n) of T whose preimage is a(n)",
					"∃c:(num → set(B)). ∀n:num. c(n) ∈ T ∧ a(n) = preimage_on(Ω, f, c(n))",
					By(terms, members))
				union := b.Have(
					"so the union of the a(n) is the preimage of the union of the c(n)",
					"⋃image(a, 𝕌) = preimage_on(Ω, f, ⋃image(c, 𝕌))",
					BySets(chosen))
				b.Show(
					"and the union of the c(n) is a member of T",
					By(Normalized, union, chosen, laws[3].At(c), preimages.At(b.TermAs[Set[B]]("⋃image(c, 𝕌)"))))
			}))
		a.Show(
			"so the pullback is a σ-algebra on Ω, f is measurable from it "+
				"into T, and it lies in every family that makes f measurable",
			SplitConjAll(
				Case(
					"the pullback is a σ-algebra on Ω, by the four clauses above",
					Simp(Fwd(sigma_algebra.SigmaAlgebraOnDef)),
					By(inside, carrier, complements, unions)),
				Case(
					"f maps Ω into V and pulls each member of T back into the pullback",
					Simp(Fwd(MeasurableMapDef)),
					By(into, preimages)),
				Case(
					"a family making f measurable holds every preimage of a member of T",
					Derive(func(b *Argument) {
						b.FixAs[Set[Set[A]]]("S")
						measurable := b.Assume()
						pulled := b.Unfolded(measurable, MeasurableMapDef)
						b.Show(
							"and the pullback consists of those preimages",
							Simp(Fwd(PullbackSigmaDef), Fwd(set_image.ImageSubsetIff)),
							By(pulled))
					}))))
	}),
})}
