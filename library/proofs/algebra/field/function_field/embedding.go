// embedding.go — a function field of one variable over the base field k₀
// embeds into an algebraically closed field along any embedding of k₀,
// sending a transcendental generator to any point transcendental over the
// image of k₀.

package function_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// FunctionFieldEmbedding — a field K₀ generated over the base field k₀ by a
// finite E, algebraic over k₀(s) for a transcendental s, embeds into an
// algebraically closed M along any embedding σ of k₀, sending s to any u
// transcendental over σ(k₀): σ extends to k₀[s] by s ↦ u, one-to-one since u
// satisfies no relation over σ(k₀), hence to the field of fractions k₀(s), and
// on to K₀ = k₀(s)(E), one element of E at a time.
var FunctionFieldEmbedding = functionFieldEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "FunctionFieldEmbedding",
	Reading: "u transcendental over σ(k₀) is load-bearing: for an algebraic u, s ↦ u has " +
		"a kernel on k₀[s] and does not extend to k₀(s). Finite generation spares Zorn's lemma.",
	Key: "prop_c9487e827507dd0e",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(B). ∀M:field_on(A). ∀k₀ K₀:set(B). ∀s:B. ∀σ:(B → A). ∀u:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(F, k₀)",
			"subfield(F, K₀)",
			"k₀ ⊆ K₀",
			"∃E:set(B). finite(E) ∧ E ⊆ K₀ ∧ field_adjoin(F, k₀, E) = K₀",
			"s ∈ K₀",
			"¬algebraic_over(F, k₀, s)",
			"∀x:B. x ∈ K₀ ⇒ algebraic_over(F, field_adjoin(F, k₀, {s}), x)",
			"ring_homomorphism(restrict_ring(field_ring(F), k₀), field_ring(M), σ)",
			"u ∈ M.carrier",
			"¬algebraic_over(M, image(σ, k₀), u)",
		},
		Conclusion: "∃τ:(B → A). " +
			"    ring_homomorphism(restrict_ring(field_ring(F), K₀), field_ring(M), τ) ∧ " +
			"    (∀x:B. x ∈ k₀ ⇒ τ(x) = σ(x)) ∧ " +
			"    τ(s) = u",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "polynomial_image(field_ring(F), k₀, s)"},
			{Name: "rationalFunctions", Text: "field_adjoin(F, k₀, {s})"},
			{Name: "rationalFunctionsWith", Text: "λE:set(B). field_adjoin(F, field_adjoin(F, k₀, {s}), E)"},
		},
	}, func(
		a *Argument,
		F field.FieldFact[on.F],
		M field.FieldFact[on.M],
		k0, K0 *Expr[Set[B]],
		s *Expr[B],
		σ *Arrow[B, A],
		u *Expr[A],
		closed, subk, subK, kInK, generated, sInK, transcendental, algebraic, hom, uIn, transcendentalImage Fact,
	) {
		fieldF := a.TermAs[FieldOps[B]]("F")
		fieldM := a.TermAs[FieldOps[A]]("M")
		polynomials := a.TermAs[Set[B]]("«polynomials»")
		rationalFunctions := a.TermAs[Set[B]]("«rationalFunctions»")
		sInF := a.Have(
			"s lies in F",
			"s ∈ F.carrier",
			BySets(sInK, subK, field.SubfieldSubset.At(fieldF, K0)))
		σInjective := a.Have(
			"σ, a ring map out of the subfield k₀, is one-to-one",
			"injective_on(k₀, σ)",
			By(M, subk, hom, ring_homomorphism.SubfieldHomomorphismEmbedding.Read(F).At(fieldM, k0, σ)))
		φ, lift := a.ObtainAs[Fun[B, A]](
			"σ extends to k₀[s], sending s to u, as s is transcendental over k₀",
			"∃φ:(B → A). "+
				"    ring_homomorphism(restrict_ring(field_ring(F), «polynomials»), field_ring(M), φ) ∧ "+
				"    (∀c:B. c ∈ k₀ ⇒ φ(c) = σ(c)) ∧ "+
				"    φ(s) = u",
			By(
				F,
				transcendental,
				uIn,
				sInF,
				subk,
				hom,
				field.SubfieldSubring.Read(F),
				algebraic_element.TranscendentalLift.At(
					fieldF, a.TermAs[module_record.RingOps[A]]("field_ring(M)"), k0, σ, s, u)))
		lifted := a.Conjuncts(
			lift,
			"φ is a ring map on k₀[s]",
			"φ is σ on k₀",
			"φ sends s to u")
		φHom, φOnK, φAtS := lifted[0], lifted[1], lifted[2]
		tower := a.Have(
			"k₀[s] holds k₀ and s and lies in k₀(s)",
			"k₀ ⊆ «polynomials» ∧ s ∈ «polynomials» ∧ «polynomials» ⊆ «rationalFunctions»",
			By(sInF, subk, algebraic_element.PolynomialImageRing.Read(F).AsFact().At(k0, s)))
		injective := a.Have(
			"φ is one-to-one: u satisfies no relation over σ(k₀), and σ is one-to-one",
			"injective_on(«polynomials», φ)",
			By(
				F,
				M,
				sInF,
				subk,
				hom,
				σInjective,
				uIn,
				transcendentalImage,
				φHom,
				φOnK,
				φAtS,
				field.SubfieldSubring.Read(F),
				algebraic_element.TranscendentalLiftInjective.At(fieldF, fieldM, k0, σ, φ, s, u)))
		between := a.Have(
			"k₀(s) is a subfield between k₀ and K₀",
			"subfield(F, «rationalFunctions») ∧ k₀ ⊆ «rationalFunctions» ∧ «rationalFunctions» ⊆ K₀",
			BySets(
				sInK,
				sInF,
				subK,
				subk,
				kInK,
				algebraic_element.AdjoinElementSubfield.Read(F).AsFact().At(k0, s),
				algebraic_element.AdjoinLeast.Read(F).At(k0, a.TermAs[Set[B]]("{s}"), K0)))
		ψ, extension := a.ObtainAs[Fun[B, A]](
			"φ extends to k₀(s), the field of fractions of k₀[s]",
			"∃ψ:(B → A). "+
				"    ring_homomorphism(restrict_ring(field_ring(F), «rationalFunctions»), field_ring(M), ψ) ∧ "+
				"    (∀x:B. x ∈ «polynomials» ⇒ ψ(x) = φ(x))",
			By(
				F,
				M,
				between,
				φHom,
				injective,
				sInF,
				subk,
				integral_element.RationalFunctionsFractionField.At(fieldF, k0, s),
				ring_localization.FractionFieldLift.At(fieldF, fieldM, polynomials, rationalFunctions, φ)))
		extended := a.Conjuncts(
			extension,
			"ψ is a ring map on k₀(s)",
			"ψ is φ on k₀[s]")
		ψHom, ψOnPolynomials := extended[0], extended[1]
		E, finitelyGenerated := a.UnpackAs[Set[B]](generated, "E")
		overRationalFunctions := a.Have(
			"E lies in F, and its elements are algebraic over k₀(s)",
			"E ⊆ F.carrier ∧ (∀x:B. x ∈ E ⇒ algebraic_over(F, «rationalFunctions», x))",
			BySets(algebraic, subK, finitelyGenerated, field.SubfieldSubset.At(fieldF, K0)))
		τ, τExtends := a.ObtainAs[Fun[B, A]](
			"adjoin the elements of E to k₀(s) one at a time inside the closed field M",
			"∃τ:(B → A). "+
				"    ring_homomorphism(restrict_ring(field_ring(F), «rationalFunctionsWith»(E)), "+
				"        field_ring(M), "+
				"        τ) ∧ "+
				"    (∀x:B. x ∈ «rationalFunctions» ⇒ τ(x) = ψ(x))",
			By(
				closed,
				F,
				M,
				between,
				overRationalFunctions,
				finitelyGenerated,
				ψHom,
				algebraic_closure.FiniteAdjoinEmbedding.At(fieldF, fieldM, rationalFunctions, E, ψ)))
		reached := a.Conjuncts(
			τExtends,
			"τ is a ring map on k₀(s)(E)",
			"τ is ψ on k₀(s)")
		τHom, τOnRationalFunctions := reached[0], reached[1]
		adjoined := a.TermAs[Set[B]]("«rationalFunctionsWith»(E)")
		bigger := a.Have(
			"k₀(s)(E) is a subfield holding k₀, k₀(s) and E",
			"subfield(F, «rationalFunctionsWith»(E)) ∧ "+
				"k₀ ⊆ «rationalFunctionsWith»(E) ∧ "+
				"«rationalFunctions» ⊆ «rationalFunctionsWith»(E) ∧ "+
				"E ⊆ «rationalFunctionsWith»(E)",
			BySets(
				between,
				overRationalFunctions,
				field.SubfieldSubset.At(fieldF, rationalFunctions),
				algebraic_element.AdjoinSubfield.Read(F).At(rationalFunctions, E)))
		generatesK := a.Have(
			"adjoining E to k₀(s) gives K₀, which k₀ and E generate",
			"«rationalFunctionsWith»(E) = K₀",
			By(
				subK,
				between,
				bigger,
				finitelyGenerated,
				algebraic_element.AdjoinLeast.Read(F).At(rationalFunctions, E, K0),
				algebraic_element.AdjoinLeast.Read(F).At(k0, E, adjoined),
				set_order.SubsetAntisym.At(adjoined, K0)))
		a.Take(τ)
		a.Show(
			"τ embeds K₀, is σ on k₀ and sends s to u",
			SplitConjAll(
				Case(
					"τ is a ring map on K₀ = k₀(s)(E)",
					By(Normalized, generatesK, τHom)),
				Case(
					"on k₀ ⊆ k₀[s] ⊆ k₀(s), τ is ψ, which is φ, which is σ",
					Derive(func(b *Argument) {
						b.FixAs[B]("x")
						member := b.Assume()
						inside := b.Have(
							"x lies in k₀[s] and in k₀(s)",
							"x ∈ «polynomials» ∧ x ∈ «rationalFunctions»",
							BySets(member, tower))
						b.Show(
							"τ(x) = ψ(x) = φ(x) = σ(x)",
							By(φOnK, member, inside, ψOnPolynomials, τOnRationalFunctions))
					})),
				Case(
					"s lies in k₀[s], so τ(s) = ψ(s) = φ(s) = u",
					BySets(φAtS, tower, ψOnPolynomials, τOnRationalFunctions))))
	}),
})}
