package spec_functor

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/structure_sheaf"
	"github.com/euc-ai/xugo/library/registry"
)

// SpecPointMapExtensional — contraction reads a homomorphism only on the ring carrier.
var SpecPointMapExtensional = specPointMapExtensionalThm{family.Add(registry.ProofEntry{
	Name: "SpecPointMapExtensional",
	Key:  "prop_db926784dda9d096",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:comm_ring_on(A). ∀S:comm_ring_on(B). ∀φ ψ:(A → B). ∀q:set(B).",
			Hypotheses: []string{
				"∀a:A. a ∈ R.carrier ⇒ φ(a) = ψ(a)",
			},
			Conclusion: "preimage_on(R.carrier, φ, q) = preimage_on(R.carrier, ψ, q)",
		},
		func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			S comm_ring.CommRingFact[on.S],
			φ, ψ *Arrow[A, B],
			agreeOnCarrier Fact,
			q *Expr[Set[B]],
		) {
			a.Show(
				"The guarded preimages have the same members",
				BySets(agreeOnCarrier))
		}),
})}

// SpecSectionMapExtensional — regular sections use fractions with both coordinates in the ring carrier.
var SpecSectionMapExtensional = specSectionMapExtensionalThm{family.Add(registry.ProofEntry{
	Name: "SpecSectionMapExtensional",
	Key:  "prop_a8e6d051c305b02f",
	Build: family.Sections(
		Statement{
			Binders: "∀R:comm_ring_on(A). " +
				"∀S:comm_ring_on(B). " +
				"∀φ ψ:(A → B). " +
				"∀V:set(set(A)). " +
				"∀s:(set(A) → set(prod(A, A))).",
			Hypotheses: []string{
				"∀a:A. a ∈ R.carrier ⇒ φ(a) = ψ(a)",
				"s ∈ structure_sections(R, V)",
			},
			Conclusion: "spec_section_map(R, S, φ, V, s) = spec_section_map(R, S, ψ, V, s)",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			mapRepresentatives := ctx.Lemma(
				Statement{
					Binders: "∀mul':(B → B → B). " +
						"∀c':set(B). " +
						"∀φ ψ:(A → B). " +
						"∀c t:set(A). " +
						"∀t':set(B). " +
						"∀X:set(prod(A, A)).",
					Hypotheses: []string{
						"∀a:A. a ∈ c ⇒ φ(a) = ψ(a)",
						"∀a u:A. (a, u) ∈ X ⇒ a ∈ c ∧ u ∈ c",
					},
					Conclusion: "fraction_map(mul', c', φ, t, t', X) = fraction_map(mul', c', ψ, t, t', X)",
				},
				func(
					a *Argument,
					mulʹ *Arrow2[B, B, B],
					cʹ *Expr[Set[B]],
					φ, ψ *Arrow[A, B],
					c, t *Expr[Set[A]],
					tʹ *Expr[Set[B]],
					X *Expr[Set[Prod[A, A]]],
					_ Fact,
				) {
					a.Do(Unfold(ring_localization.FractionMapDef))
					representatives := a.Hyp("∀a u:A.(a, u) ∈ X ⇒ a ∈ c ∧ u ∈ c")
					agreeOnCarrier := a.Hyp("∀a:A. a ∈ c ⇒ φ(a) = ψ(a)")
					a.Show(
						"Every representative has the same image fraction",
						BySets(representatives, agreeOnCarrier))
				})
			sectionRepresentatives := ctx.Lemma(
				"∀R:comm_ring_on(A). ∀V:set(set(A)). ∀s:(set(A) → set(prod(A, A))). ∀p:set(A). "+
					"    s ∈ structure_sections(R, V) ∧ p ∈ V ⇒ ∀a u:A.(a, u) ∈ s(p) ⇒ a ∈ R.carrier ∧ u ∈ R.carrier",
				func(
					a *Argument,
					R Fact,
					V *Expr[Set[Set[A]]],
					s *Arrow[Set[A], Set[Prod[A, A]]],
					p *Expr[Set[A]],
					located Fact,
				) {
					regular := a.Unfolded(located, structure_sheaf.StructureSectionsDef)
					localExpressions := a.Have(
						"The section is locally a fraction",
						"locally_fraction(R, V, p, s)",
						BySets(regular))
					r, v, sectionValue := a.Obtain2As[A, A](
						"Evaluate a local fraction at the chosen point",
						"∃r v:A. s(p) = fraction_class(R.carrier, R.carrier ∖ p, r, v)",
						By(a.Unfolded(localExpressions, structure_sheaf.LocallyFractionDef)))
					a.Show(
						"A fraction class has numerator and denominator in the ring",
						sectionValue.Rw(),
						BySets(At(
							ring_localization.FractionClassMember,
							a.TermAs[Op[A]]("R.mul"),
							a.TermAs[Set[A]]("R.carrier"),
							a.TermAs[Set[A]]("R.carrier ∖ p"),
							r,
							v)))
				})
			return ctx.Theorem(headline,
				func(
					a *Argument,
					R comm_ring.CommRingFact[on.R],
					S comm_ring.CommRingFact[on.S],
					φ, ψ *Arrow[A, B],
					V *Expr[Set[Set[A]]],
					s *Arrow[Set[A], Set[Prod[A, A]]],
					agreeOnCarrier, section Fact,
				) {
					a.Do(Funext())
					a.FixAs[Set[B]]("q")
					a.FixAs[Prod[B, B]]("z")
					a.Do(Unfold(SpecSectionMapDef))
					a.Assuming(
						a.TermAs[Bool]("q ∈ prime_spectrum(S)").Core(),
						"Both maps are empty outside the spectrum",
						Given(func(b *Argument, outside Fact) {
							b.Show(
								"The guards are false",
								By(outside))
						}))
					contractedPrimeEq := a.Have(
						"The homomorphisms contract the prime to the same point",
						"preimage_on(R.carrier, φ, q) = preimage_on(R.carrier, ψ, q)",
						By(agreeOnCarrier, R, S, SpecPointMapExtensional))
					a.Do(contractedPrimeEq.RwRev())
					inDomain := a.Assuming(
						a.TermAs[Bool]("preimage_on(R.carrier, φ, q) ∈ V").Core(),
						"Both maps are empty outside the section domain",
						Given(func(b *Argument, outside Fact) {
							b.Show(
								"The common guard is false",
								By(outside))
						}))
					representatives := a.Have(
						"Section representatives lie in the source ring",
						"∀a u:A. (a, u) ∈ s(preimage_on(R.carrier, φ, q)) ⇒ a ∈ R.carrier ∧ u ∈ R.carrier",
						By(inDomain, section, R, sectionRepresentatives))
					mappedFractionEq := a.Have(
						"Agreement on the ring gives agreement on each mapped fraction",
						"fraction_map(S.mul, "+
							"    S.carrier, "+
							"    φ, "+
							"    R.carrier ∖ preimage_on(R.carrier, φ, q), "+
							"    S.carrier ∖ q, "+
							"    s(preimage_on(R.carrier, φ, q))) = "+
							"fraction_map(S.mul, "+
							"    S.carrier, "+
							"    ψ, "+
							"    R.carrier ∖ preimage_on(R.carrier, φ, q), "+
							"    S.carrier ∖ q, "+
							"    s(preimage_on(R.carrier, φ, q)))",
						By(representatives, agreeOnCarrier, Where(mapRepresentatives, "c", a.TermAs[Set[A]]("R.carrier"))))
					a.Show(
						"The guarded section values agree",
						mappedFractionEq.Rw(),
						Basic())
				})
		}),
})}
