// adjunction.go — a root of an irreducible polynomial adjoined to a field
// inside the field's own type: the polynomials modulo the polynomial are
// a field holding a copy of the constants and a root, and an injection
// that fixes the constants and sends the other classes to points off the
// carrier carries that field back into the type as an extension.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_quotient"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_transport"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// RootAdjunctionInHost — a field whose type has room for its polynomials
// outside its carrier has, in the same type, an extension holding a root
// of a given irreducible polynomial and algebraic over it. The polynomials
// over F modulo p are a field Q whose points are sets of polynomials,
// holding the constant classes, a copy of F, and the variable's class ξ, a
// root (polynomial_quotient.QuotientAlgebraicExtension). The room gives an
// injection of Q's carrier off F's carrier; the map j undoes the constants
// map a ↦ class of a on the constant classes and sends every other class
// by that injection off F's carrier, so it is injective on Q's carrier, and
// the transported field transport_field(j, Q) is a field on A with j a ring
// homomorphism (ring_transport.TransportFieldOn,
// ring_transport.TransportFieldHomomorphism). The composite of the
// constants map and j fixes F's carrier, so the transported field extends F
// (FixedFieldEmbeddingExtends); j(ξ) is a root of p there
// (polynomial_evaluation.EvalAlongHomomorphism), and every point is algebraic over F's
// carrier (AlgebraicOverTransport).
var RootAdjunctionInHost = rootAdjunctionInHostThm{family.Add(registry.ProofEntry{
	Name: "RootAdjunctionInHost",
	Key:  "prop_2d4363312107a275",
	Reading: "G lives on F's own type, not on the quotient's sets of polynomials: it holds F's " +
		"carrier and extends F, agreeing with F only on F's carrier, so the two records may differ off it.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_on(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_irreducible(field_ring(F), p)",
			"card_le(«fieldPolynomialRing».carrier, {x:A | x ∉ F.carrier})",
		},
		Conclusion: "∃G:field_ops(A). " +
			"    field_on(G) ∧ " +
			"    field_extends(F, G) ∧ " +
			"    (∃x:A. x ∈ G.carrier ∧ polynomial_eval(G.add, G.zero, G.mul, G.one, p, x) = G.zero) ∧ " +
			"    (∀x:A. x ∈ G.carrier ⇒ algebraic_over(G, F.carrier, x))",
	}, func(a *Argument, F field.FieldFact[on.F], p *Arrow[Nat, A], assumptions Fact) {
		inputs := a.Conjuncts(
			assumptions,
			"the polynomial is irreducible",
			"the host has room outside the source field")
		irreducible, room := inputs[0], inputs[1]
		f := a.TermAs[FieldOps[A]]("F")
		fCarrier := a.TermAs[Set[A]]("F.carrier")
		fZero := a.TermAs[A]("F.zero")
		polynomials := a.TermAs[module_record.RingOps[Fun[Nat, A]]]("«fieldPolynomialRing»")
		polynomialCarrier := a.TermAs[Set[Fun[Nat, A]]]("«fieldPolynomialRing».carrier")
		outside := a.TermAs[Set[A]]("{a:A | a ∉ F.carrier}")
		ideal, idealDef := a.LetAs[Set[Fun[Nat, A]]]("I", "ideal_span(«fieldPolynomialRing», {p})")
		embedding, embeddingDef := a.LetAs[Fun[A, Set[Fun[Nat, A]]]](
			"e",
			"λa:A. ideal_quotient_projection(«fieldPolynomialRing», I, a • basis_vector(F.zero, F.one, 0))")
		quotient, quotientDef := a.LetAs[FieldOps[Set[Fun[Nat, A]]]](
			"Q", "ideal_quotient_field(«fieldPolynomialRing», I)")
		variable, variableDef := a.LetAs[Set[Fun[Nat, A]]](
			"ξ", "ideal_quotient_projection(«fieldPolynomialRing», I, basis_vector(F.zero, F.one, 1))")
		base, baseDef := a.LetAs[Set[Set[Fun[Nat, A]]]]("base", "image(e, F.carrier)")
		mapped, mappedDef := a.LetAs[Fun[Nat, Set[Fun[Nat, A]]]]("pQ", "λi:num. e(p(i))")
		quotientParts := a.Conjuncts(
			a.Have(
				"the polynomials modulo p are a field holding a "+
					"copy of F and a root of pQ, algebraic over the copy",
				"field_on(Q) ∧ "+
					"ring_homomorphism(field_ring(F), field_ring(Q), e) ∧ "+
					"injective_on(F.carrier, e) ∧ "+
					"ξ ∈ Q.carrier ∧ "+
					"polynomial_eval(Q.add, Q.zero, Q.mul, Q.one, pQ, ξ) = Q.zero ∧ "+
					"subfield(Q, base) ∧ "+
					"(∀y:set(num → A). y ∈ Q.carrier ⇒ algebraic_over(Q, base, y))",
				Simp(
					Fwd(mappedDef),
					Fwd(baseDef),
					Fwd(variableDef),
					Fwd(quotientDef),
					Fwd(embeddingDef),
					Fwd(idealDef)),
				By(irreducible, polynomial_quotient.QuotientAlgebraicExtension.Read(F).At(p))),
			"the polynomials modulo p are a field",
			"the constant classes preserve its ring operations",
			"the constant classes are injective",
			"the variable class is a quotient point",
			"the variable class is a root of pQ",
			"the constant classes form a subfield",
			"every quotient point is algebraic over the constant classes")
		quotientField, constantHom, constantInjective, variableIn :=
			quotientParts[0], quotientParts[1], quotientParts[2], quotientParts[3]
		quotientRoot, baseField, quotientAlgebraic := quotientParts[4], quotientParts[5], quotientParts[6]
		qCarrier := a.TermAs[Set[Set[Fun[Nat, A]]]]("Q.carrier")
		quotientBound := a.Have(
			"the quotient carrier fits in the polynomial carrier",
			"card_le(Q.carrier, «fieldPolynomialRing».carrier)",
			Simp(Fwd(quotientDef), Fwd(quotient_ring.IdealQuotientFieldDef.Inst[Fun[Nat, A]]())),
			By(quotient_ring.QuotientCarrierCardLe.At(polynomials, ideal)))
		quotientRoom := a.Have(
			"there is room for the quotient outside the original field",
			"card_le(Q.carrier, {a:A | a ∉ F.carrier})",
			By(quotientBound, room, cardinal.CardLeTrans.At(qCarrier, polynomialCarrier, outside)))
		_, hostInjection := a.UnpackAs[Fun[Set[Fun[Nat, A]], A]](
			a.Unfolded(quotientRoom, cardinal.CardLeDef), "h")
		hostParts := a.Conjuncts(
			hostInjection,
			"the room injection lands outside the original carrier",
			"the room map is injective")
		hostOutside, hostInjective := hostParts[0], hostParts[1]
		j, jDef := a.LetAs[Fun[Set[Fun[Nat, A]], A]](
			"j", "λq:set(num → A). COND(q ∈ base, inverse_on(F.carrier, e, q), h(q))")
		onBase := a.Have(
			"on constant classes the host map takes the inverse embedding",
			"∀q:set(num → A). q ∈ base ⇒ j(q) = inverse_on(F.carrier, e, q)",
			Derive(func(b *Argument) {
				b.FixAs[Set[Fun[Nat, A]]]("q")
				inBase := b.Assume()
				b.Show(
					"the constant branch reads its chosen inverse",
					Simp(Fwd(jDef), Fwd(inBase)),
					Basic())
			}))
		offBase := a.Have(
			"away from constant classes the host map uses the room injection",
			"∀q:set(num → A). q ∉ base ⇒ j(q) = h(q)",
			Derive(func(b *Argument) {
				b.FixAs[Set[Fun[Nat, A]]]("q")
				notBase := b.Assume()
				b.Show(
					"the other branch reads the room map",
					Simp(Fwd(jDef), Fwd(notBase)),
					Basic())
			}))
		fixed := a.Have(
			"every source constant returns to itself",
			"∀a:A. a ∈ F.carrier ⇒ j(e(a)) = a",
			Derive(func(b *Argument) {
				point := b.FixAs[A]("a")
				aF := b.MemberOf[on.F](point, b.Assume())
				image := b.TermAs[Set[Fun[Nat, A]]]("e(a)")
				inBase := b.Have(
					"the constant class belongs to the base",
					"e(a) ∈ base",
					BySets(baseDef, aF, set_image.FunInImage.At(embedding, fCarrier, aF)))
				b.Show(
					"the inverse embedding recovers the constant",
					By(
						Normalized,
						onBase.At(image),
						constantInjective,
						aF,
						inBase,
						functions.InverseOnLeft.At(fCarrier, embedding, aF)))
			}))
		baseValues := a.Have(
			"the constant branch takes values in the source field",
			"∀q:set(num → A). q ∈ base ⇒ j(q) ∈ F.carrier",
			Derive(func(b *Argument) {
				q := b.FixAs[Set[Fun[Nat, A]]]("q")
				inBase := b.Assume()
				b.Show(
					"the inverse lies in the carrier it was chosen from",
					By(Normalized, onBase.At(q), baseDef, inBase, functions.InverseOnIn.At(fCarrier, embedding, q)))
			}))
		otherValues := a.Have(
			"the other quotient classes land outside the source field",
			"∀q:set(num → A). q ∈ Q.carrier ∧ q ∉ base ⇒ j(q) ∉ F.carrier",
			Derive(func(b *Argument) {
				q := b.FixAs[Set[Fun[Nat, A]]]("q")
				point := b.Assume()
				b.Show(
					"the room injection separates the two ranges",
					BySets(offBase.At(q), hostOutside.At(q), point))
			}))
		injective := a.Have(
			"the two injective branches have disjoint ranges",
			"injective_on(Q.carrier, j)",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				u := b.FixAs[Set[Fun[Nat, A]]]("u")
				v := b.FixAs[Set[Fun[Nat, A]]]("v")
				points := b.Assume()
				b.Cases(b.TermAs[Bool]("u ∈ base"))
				b.When(
					"the first class is constant",
					func(c *Argument, uBase Fact) {
						c.Cases(c.TermAs[Bool]("v ∈ base"))
						c.When(
							"both inputs are constant classes",
							func(d *Argument, vBase Fact) {
								d.Show(
									"applying the embedding recovers both classes",
									By(
										Normalized,
										onBase.At(u),
										onBase.At(v),
										baseDef,
										uBase,
										vBase,
										points,
										functions.InverseOnRight.At(fCarrier, embedding, u),
										functions.InverseOnRight.At(fCarrier, embedding, v)))
							})
						c.Otherwise(
							"the second input lies outside the constant classes",
							func(d *Argument, vOther Fact) {
								d.Show(
									"equal images cannot lie in these disjoint ranges",
									By(Normalized, baseValues.At(u), otherValues.At(v), vOther, uBase, points))
							})
					})
				b.Otherwise(
					"the first class is outside the constant classes",
					func(c *Argument, uOther Fact) {
						c.Cases(c.TermAs[Bool]("v ∈ base"))
						c.When(
							"only the second input is a constant class",
							func(d *Argument, vBase Fact) {
								d.Show(
									"the symmetric mixed ranges are disjoint",
									By(Normalized, baseValues.At(v), otherValues.At(u), uOther, vBase, points))
							})
						c.Otherwise(
							"both inputs use the room injection",
							func(d *Argument, vOther Fact) {
								roomInjectivity := d.Unfolded(hostInjective, functions.InjectiveOnDef)
								d.Show(
									"injectivity of the room map identifies the classes",
									By(Normalized, roomInjectivity.At(u, v), offBase.At(u), offBase.At(v), uOther, vOther, points))
							})
					})
			}))
		L, transportDef := a.LetAs[FieldOps[A]]("L", "transport_field(j, Q)")
		transportedField := a.Have(
			"transport gives a field on the host type",
			"field_on(L)",
			By(
				Normalized,
				quotientField,
				transportDef,
				injective,
				ring_transport.TransportFieldOn.At(j, quotient)))
		carrierDescription := a.Have(
			"the transported carrier is the image of the quotient",
			"L.carrier = image(j, Q.carrier)",
			Simp(Fwd(transportDef), Fwd(ring_transport.TransportFieldDef)),
			Basic())
		transportHom := a.Have(
			"the transport injection preserves the quotient ring operations",
			"ring_homomorphism(field_ring(Q), field_ring(L), j)",
			By(
				Normalized,
				quotientField,
				transportDef,
				injective,
				ring_transport.TransportFieldHomomorphism.At(j, quotient)))
		fRing := a.TermAs[module_record.RingOps[A]]("field_ring(F)")
		qRing := a.TermAs[module_record.RingOps[Set[Fun[Nat, A]]]]("field_ring(Q)")
		lRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
		composite := a.TermAs[Fun[A, A]]("λa:A. j(e(a))")
		compositeHom := a.Have(
			"the composite embeds the source field into the transported field",
			"ring_homomorphism(field_ring(F), field_ring(L), λa:A. j(e(a)))",
			By(
				constantHom,
				transportHom,
				ring_homomorphism.RingHomCompose.At(fRing, qRing, lRing, embedding, j)))
		extension := a.Have(
			"the fixed composite makes the transported field an extension",
			"field_extends(F, L)",
			By(F, transportedField, fixed, compositeHom, FixedFieldEmbeddingExtends.At(f, L, composite)))
		constantZero := a.Have(
			"the constant embedding preserves zero",
			"e(F.zero) = Q.zero",
			By(ring_homomorphism.MapZero.Read(constantHom)))
		sourcePolynomial := a.Have(
			"irreducibility supplies a polynomial over the source field",
			"polynomial_over(F.zero, F.carrier, p)",
			By(irreducible, polynomial_division.PolynomialIrreducibleDef.At(fRing, p)))
		qZero := a.TermAs[Set[Fun[Nat, A]]]("Q.zero")
		mappedPolynomial := a.Have(
			"mapping coefficients gives a polynomial over the quotient field",
			"polynomial_over(Q.zero, Q.carrier, pQ)",
			By(
				Normalized,
				mappedDef,
				sourcePolynomial,
				constantZero,
				ring_homomorphism.MapIn.Read(constantHom),
				polynomial.PolynomialOverMap.At(embedding, fZero, qZero, fCarrier, qCarrier, p)))
		evaluation := a.Have(
			"evaluation commutes with the transport homomorphism",
			"j(polynomial_eval(Q.add, Q.zero, Q.mul, Q.one, pQ, ξ)) = "+
				"polynomial_eval(L.add, L.zero, L.mul, L.one, λi:num. j(pQ(i)), j(ξ))",
			By(
				variableIn,
				mappedPolynomial,
				transportHom,
				polynomial_evaluation.EvalAlongHomomorphism.At(qRing, lRing, j, mapped, variable)))
		originalCoefficients := a.Have(
			"transport recovers the original coefficient sequence",
			"(λi:num. j(pQ(i))) = p",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				coefficient := b.TermAs[A]("p(i)")
				inSource := b.Have(
					"the coefficient is a source field point",
					"p(i) ∈ F.carrier",
					By(sourcePolynomial, polynomial.PolynomialOverDef.At(fZero, fCarrier, p)))
				b.Show(
					"the fixed composite recovers this coefficient",
					By(Normalized, fixed.At(coefficient), inSource, mappedDef))
			}))
		transportZero := a.Have(
			"the transported zero is the image of quotient zero",
			"j(Q.zero) = L.zero",
			Simp(Fwd(transportDef), Fwd(ring_transport.TransportFieldDef)),
			Basic())
		root := a.Have(
			"the transported variable is a root of the original polynomial",
			"polynomial_eval(L.add, L.zero, L.mul, L.one, p, j(ξ)) = L.zero",
			By(transportZero, evaluation, quotientRoot, originalCoefficients))
		baseImage := a.Have(
			"the transported constant classes are exactly the source carrier",
			"image(j, base) = F.carrier",
			Simp(Fwd(baseDef), Rev(set_image.ImageCompose)),
			Simp(Fwd(functions.ComposeApply)),
			By(
				Normalized,
				fixed,
				set_image.ImageCongruence.At(composite, a.TermAs[Fun[A, A]]("λa:A. a"), fCarrier),
				set_image.ImageIdentity.At(fCarrier)))
		baseInQuotient := a.Have(
			"the constant subfield lies in the quotient carrier",
			"base ⊆ Q.carrier",
			By(baseField, field.SubfieldSubset.At(quotient, base)))
		imageAlgebraic := a.Have(
			"every transported quotient point is algebraic over the source",
			"∀q:set(num → A). q ∈ Q.carrier ⇒ algebraic_over(L, F.carrier, j(q))",
			Derive(func(b *Argument) {
				q := b.FixAs[Set[Fun[Nat, A]]]("q")
				point := b.Assume()
				b.Show(
					"the canonical quotient algebraicity transports across j",
					By(
						Normalized,
						quotientAlgebraic.At(q),
						transportDef,
						baseImage,
						injective,
						point,
						baseInQuotient,
						quotientField,
						AlgebraicOverTransport.At(j, quotient, base, q)))
			}))
		allAlgebraic := a.Have(
			"every point of the transported field is algebraic over the source",
			"∀a:A. a ∈ L.carrier ⇒ algebraic_over(L, F.carrier, a)",
			Simp(Fwd(carrierDescription), Fwd(set_image.ForallInImage)),
			By(imageAlgebraic))
		rootIn := a.Have(
			"the root belongs to the transported carrier",
			"j(ξ) ∈ L.carrier",
			By(variableIn, ring_homomorphism.MapIn.Read(transportHom).AsFact().At(variable)))
		a.Show(
			"the transported field adjoins the required algebraic root",
			Witness(L),
			SplitConjAll(
				Case(
					"the witness is a field",
					By(transportedField)),
				Case(
					"it extends the original field",
					By(extension)),
				Case(
					"it holds a root of the original polynomial",
					Witness(a.TermAs[A]("j(ξ)")),
					By(rootIn, root)),
				Case(
					"all its points are algebraic over the original carrier",
					By(allAlgebraic))))
	}),
})}
