// point_criterion.go — when the ideal of a point is invertible: the ideal
// (u, v) of two members satisfying a relation whose coefficients span S
// with them, the Jacobian criterion at a k-rational point, and a maximal
// ideal one of whose nonzero members generates it away from the ideal.

package invertible_fractional_ideal

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// RelationIdealInvertible — the ideal m = (u, v) of a subring S is
// invertible when u is nonzero, u and v satisfy a relation v * g = u * h
// with g and h in S, and u, v, g and h span S. The ratio ρ = g/u takes u
// to g and, by the relation, v to h, so it takes r * u + s * v to
// r * g + s * h in S and lies in (S : m). The ideal m · (S : m) of S then
// holds u and v, one lying in (S : m), and g and h, their products with ρ;
// so it holds the ideal u, v, g and h span, which is S.
var RelationIdealInvertible = relationIdealInvertibleThm{family.Add(registry.ProofEntry{
	Name: "RelationIdealInvertible",
	Key:  "prop_98fd41a29074005",
	Reading: "u ≠ L.zero is load-bearing: ρ = g/u divides by it. No residue field, " +
		"maximality or rationality is asked: the caller shows that u, v, g and h span S.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀u v g h:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"u ∈ S",
			"v ∈ S",
			"g ∈ S",
			"h ∈ S",
			"u ≠ L.zero",
			"v * g = u * h",
			"ideal_span(«wfScalars», {u, v, g, h}) = S",
		},
		Conclusion: "«wfInvertible»(ideal_span(«wfScalars», {u, v}))",
		Abbrev: Abbrev{
			{Name: "m", Text: "ideal_span(«wfScalars», {u, v})"},
			{Name: "ρ", Text: "g * L.inv(u)"},
			{Name: "mTimesInverse", Text: "«wfMul»(«m», «wfInverse»(«m»))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			S *Expr[Set[A]],
			u, v, g, h *Expr[A],
			subring, uInS, vInS, gInS, hInS, nonzero, relation, spansS Fact,
		) {
			ringL := field.RingOn.Read(L)
			fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
			scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
			m := a.TermAs[Set[A]]("«m»")
			inverse := a.TermAs[Set[A]]("«wfInverse»(«m»)")
			product := a.TermAs[Set[A]]("«mTimesInverse»")
			ratio := a.TermAs[A]("«ρ»")
			invU := a.TermAs[A]("L.inv(u)")
			pair, singleton := a.TermAs[Set[A]]("{u, v}"), a.TermAs[Set[A]]("{v}")
			sInL := a.Have(
				"S lies in the field",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subring)))
			uvghInL := a.Have(
				"the four given elements lie in the field",
				"u ∈ L.carrier ∧ v ∈ L.carrier ∧ g ∈ L.carrier ∧ h ∈ L.carrier",
				BySets(sInL, uInS, vInS, gInS, hInS))
			ringS := a.Have(
				"S is a ring under the inherited operations",
				"comm_ring_on(«wfScalars»)",
				By(subring, comm_ring.SubringRingOn.Read(ringL).At(S)))
			ideal := a.Have(
				"the span m of u and v, both in S, is an ideal of S",
				"«wfIdeal»(«m»)",
				BySets(uInS, vInS, ring_ideal.SpanIdeal.Read(ringS).At(pair)))
			fractionalIdeal := a.Have(
				"an integral ideal is a fractional ideal contained in S",
				"«wfFractional»(«m») ∧ «m» ⊆ S",
				By(subring, ideal, fractional_ideal.IntegralIdealFractional.Read(L).At(S, m)))
			idealInL := a.Have(
				"m lies in the field",
				"«m» ⊆ L.carrier",
				BySets(fractionalIdeal, sInL))
			insert := a.Have(
				"adjoining u adds its multiples to the ideal of v",
				"«m» = {r * u + t | r:A, t:A | r ∈ S ∧ t ∈ ideal_span(«wfScalars», {v})}",
				By(
					vInS,
					set_order.SingSubset.At(S, v),
					uInS,
					ring_ideal.SpanInsert.Read(ringS).AsFact().At(singleton, u)))
			unitU := a.Have(
				"the inverse of nonzero u cancels u",
				"L.inv(u) * u = L.one",
				By(uvghInL, nonzero, field.MulLeftInverseOn.Read(L).AsFact().At(u)))
			ratioInL := a.Have(
				"g divided by u lies in the field",
				"«ρ» ∈ L.carrier",
				By(uvghInL, field.InvIn.Read(L).AsFact().At(u), comm_ring.MulIn.Read(ringL).AsFact().At(g, invU)))
			ratioU := a.Have(
				"multiplying u by the ratio recovers g",
				"u * «ρ» = g",
				ByArith(uvghInL, Scaled(g, unitU), field.InvIn.Read(L).AsFact().At(u)))
			ratioV := a.Have(
				"the relation gives the corresponding product with v",
				"v * «ρ» = h",
				ByArith(uvghInL, Scaled(invU, relation), Scaled(h, unitU), field.InvIn.Read(L).AsFact().At(u)))
			preserves := a.Have(
				"the ratio multiplies m into S",
				"∀x:A. x ∈ «m» ⇒ «ρ» * x ∈ S",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					xInM := b.Assume()
					r, _, decomposition := b.Obtain2As[A, A](
						"write x as a multiple of u plus an element of the ideal of v",
						"∃r t:A. r ∈ S ∧ t ∈ ideal_span(«wfScalars», {v}) ∧ x = r * u + t",
						BySets(insert, xInM))
					parts := b.Conjuncts(
						decomposition,
						"r lies in S",
						"t lies in the ideal of v",
						"x has the chosen expression")
					rInS, tInIdeal, expression := parts[0], parts[1], parts[2]
					s, multiple := b.ObtainAs[A](
						"write the remaining element as a multiple of v",
						"∃s:A. s ∈ S ∧ t = s * v",
						BySets(vInS, ring_ideal.PrincipalIdealMultiples.Read(ringS).AsFact().At(v), tInIdeal))
					tParts := b.Conjuncts(
						multiple,
						"s lies in S",
						"t is s times v")
					sInS, tMultiple := tParts[0], tParts[1]
					coefficientCarriers := b.Have(
						"both coefficients lie in the field",
						"r ∈ L.carrier ∧ s ∈ L.carrier",
						BySets(sInL, rInS, sInS))
					combination := b.Have(
						"the ratio takes the generator expression to an S-linear combination of g and h",
						"«ρ» * x = r * g + s * h",
						expression.Rw(),
						tMultiple.Rw(),
						ByArith(
							uvghInL,
							coefficientCarriers,
							Scaled(r, ratioU),
							Scaled(s, ratioV),
							field.InvIn.Read(L).AsFact().At(u)))
					b.Show(
						"the two resulting products and their sum lie in S",
						By(
							combination,
							subring,
							rInS,
							sInS,
							gInS,
							hInS,
							comm_ring.SubringMul.At(fieldRing, S, r, g),
							comm_ring.SubringMul.At(fieldRing, S, s, h),
							comm_ring.SubringAdd.At(fieldRing, S, b.TermAs[A]("r * g"), b.TermAs[A]("s * h"))))
				}))
			ratioInInverse := a.Have(
				"therefore g divided by u lies in the fractional inverse",
				"«ρ» ∈ «wfInverse»(«m»)",
				BySets(ratioInL, preserves, fractional_ideal.FractionalInverseDef.At(fieldRing, S, m)))
			inverseInL := fractional_ideal.FractionalInverseSubset.Read(L).At(S, m)
			productFractional := a.Have(
				"the product with the inverse is a fractional ideal",
				"«wfFractional»(«mTimesInverse»)",
				By(
					subring,
					idealInL,
					inverseInL,
					fractional_ideal.FractionalMulSubmodule.Read(L).At(S, m, inverse)))
			productSubset := a.Have(
				"(S : m) multiplies m into S and the product commutes, so m · (S : m) lies in S",
				"«mTimesInverse» ⊆ S",
				BySets(
					subring,
					fractional_ideal.SubringSubmodule.Read(L).At(S),
					fractional_ideal.FractionalInverseDef.At(fieldRing, S, m),
					fractional_ideal.FractionalMulLeast.Read(L).At(S, inverse, m, S),
					idealInL,
					fractional_ideal.FractionalMulComm.Read(L).At(S, m, inverse)))
			productIdeal := a.Have(
				"the product is an ideal of S",
				"«wfIdeal»(«mTimesInverse»)",
				By(
					subring,
					productFractional,
					productSubset,
					fractional_ideal.IntegralIdealFractional.Read(L).At(S, product)))
			multiplicative := comm_ring.MulMonoidOn.Read(ringL)
			oneInverse := a.Have(
				"one multiplies every member of m into S",
				"L.one ∈ «wfInverse»(«m»)",
				BySets(
					comm_ring.OneIn.Read(ringL),
					comm_monoid.LeftIdentityOn.Read(multiplicative),
					fractionalIdeal,
					idealInL,
					fractional_ideal.FractionalInverseDef.At(fieldRing, S, m)))
			mInProduct := a.Have(
				"multiplication by one puts all of m in the product",
				"«m» ⊆ «mTimesInverse»",
				BySets(
					comm_monoid.RightIdentityOn.Read(multiplicative),
					idealInL,
					oneInverse,
					At(fractional_ideal.FractionalMulHolds.Read(L), S, m, inverse)))
			ratioImages := a.Have(
				"u and v lie in the m they generate and the ratio in (S "+
					": m), so m · (S : m) holds their products g and h with it",
				"g ∈ «mTimesInverse» ∧ h ∈ «mTimesInverse»",
				BySets(
					ring_ideal.SpanContains,
					ratioInInverse,
					ratioU,
					ratioV,
					fractional_ideal.FractionalMulHolds.Read(L).At(S, m, inverse, u, ratio),
					fractional_ideal.FractionalMulHolds.Read(L).At(S, m, inverse, v, ratio)))
			generatorsInProduct := a.Have(
				"so m · (S : m) holds all four of u, v, g and h",
				"{u, v, g, h} ⊆ «mTimesInverse»",
				BySets(mInProduct, ring_ideal.SpanContains.At(scalars, pair), ratioImages))
			wholeInProduct := a.Have(
				"an ideal of S, it holds the ideal they span, which is S",
				"S ⊆ «mTimesInverse»",
				By(
					spansS,
					productIdeal,
					generatorsInProduct,
					ring_ideal.SpanLeast.At(scalars, a.TermAs[Set[A]]("{u, v, g, h}"), product)))
			a.Show(
				"m is fractional and m · (S : m) = S, so m is invertible",
				By(
					fractionalIdeal,
					productSubset,
					wholeInProduct,
					set_order.SubsetAntisym.At(product, S),
					fractional_ideal.InvertibleFractionalDef.At(fieldRing, S, m)))
		}),
})}

// LocallyPrincipalMaximalInvertible — a maximal ideal of S is invertible when
// one of its nonzero members generates it away from the ideal: some member of
// S outside it carries the whole ideal into the multiples of that member. The
// quotient of the outside member by the generator multiplies the ideal into
// S, so the ideal times its inverse is an ideal of S holding the ideal and the
// outside member, which maximality makes S.
var LocallyPrincipalMaximalInvertible = locallyPrincipalMaximalInvertibleThm{family.Add(registry.ProofEntry{
	Name: "LocallyPrincipalMaximalInvertible",
	Key:  "prop_3940f2620cf96550",
	Reading: "This is m·S_m = u·S_m written without the localization. u ≠ L.zero is load-bearing: " +
		"at u = L.zero the relations s * z = L.zero with s ≠ L.zero force m = {L.zero}, which is not " +
		"invertible. Maximality is spent once, on the ideal m · (S : m), which holds m and s ∉ m.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S m:set(A). ∀u s:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"maximal_ideal(«wfScalars», m)",
			"u ∈ m",
			"u ≠ L.zero",
			"s ∈ S",
			"s ∉ m",
			"∀z:A. z ∈ m ⇒ ∃h:A. h ∈ S ∧ s * z = u * h",
		},
		Conclusion: "«wfInvertible»(m)",
		Abbrev: Abbrev{
			{Name: "ratio", Text: "s * L.inv(u)"},
			{Name: "product", Text: "«wfMul»(m, «wfInverse»(m))"},
		},
	}, func(a *Argument, L field.FieldFact[on.L], S, m *Expr[Set[A]], u, s *Expr[A], hypotheses Fact) {
		p := a.Conjuncts(
			hypotheses,
			"S is a subring of L",
			"m is a maximal ideal of S",
			"u lies in m",
			"u is nonzero",
			"s lies in S",
			"s lies outside m",
			"s carries m into the multiples of u")
		subring, maximal, uInM, nonzero, sInS, outside, multiples :=
			p[0], p[1], p[2], p[3], p[4], p[5], p[6]
		ringL := field.RingOn.Read(L)
		fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
		inverse := a.TermAs[Set[A]]("«wfInverse»(m)")
		product := a.TermAs[Set[A]]("«product»")
		ratio := a.TermAs[A]("«ratio»")
		invU := a.TermAs[A]("L.inv(u)")
		invUIn := field.InvIn.Read(L).AsFact().At(u)
		sInL := a.Have(
			"S lies in the field",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subring)))
		ideal := a.Have(
			"a maximal ideal is an ideal",
			"«wfIdeal»(m)",
			By(maximal, ring_ideal.MaximalIdealIdeal))
		fractionalIdeal := a.Have(
			"an integral ideal is a fractional ideal contained in S",
			"«wfFractional»(m) ∧ m ⊆ S",
			By(subring, ideal, fractional_ideal.IntegralIdealFractional.Read(L).At(S, m)))
		idealInL := a.Have(
			"m lies in the field",
			"m ⊆ L.carrier",
			BySets(fractionalIdeal, sInL))
		usInL := a.Have(
			"u and s lie in the field",
			"u ∈ L.carrier ∧ s ∈ L.carrier",
			BySets(sInL, idealInL, uInM, sInS))
		unitU := a.Have(
			"the inverse of nonzero u cancels u",
			"L.inv(u) * u = L.one",
			By(usInL, nonzero, field.MulLeftInverseOn.Read(L).AsFact().At(u)))
		ratioInL := a.Have(
			"s divided by u lies in the field",
			"«ratio» ∈ L.carrier",
			By(usInL, invUIn, comm_ring.MulIn.Read(ringL).AsFact().At(s, invU)))
		ratioU := a.Have(
			"multiplying u by the ratio recovers s",
			"u * «ratio» = s",
			ByArith(usInL, Scaled(s, unitU), invUIn))
		preserves := a.Have(
			"the ratio multiplies m into S",
			"∀x:A. x ∈ m ⇒ «ratio» * x ∈ S",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xInM := b.Assume()
				h, multiple := b.UnpackAs[A](GroupPremises(xInM, multiples.At(x)), "h")
				parts := b.Conjuncts(
					multiple,
					"h lies in S",
					"s times x is u times h")
				hInS, relation := parts[0], parts[1]
				xhInL := b.Have(
					"x and h lie in the field",
					"x ∈ L.carrier ∧ h ∈ L.carrier",
					BySets(sInL, idealInL, xInM, hInS))
				quotient := b.Have(
					"the ratio takes x to h",
					"«ratio» * x = h",
					ByArith(usInL, xhInL, Scaled(invU, relation), Scaled(h, unitU), invUIn))
				b.Show(
					"and h lies in S",
					By(Normalized, quotient, hInS))
			}))
		ratioInInverse := a.Have(
			"therefore s divided by u lies in the fractional inverse",
			"«ratio» ∈ «wfInverse»(m)",
			BySets(ratioInL, preserves, fractional_ideal.FractionalInverseDef.At(fieldRing, S, m)))
		productFractional := a.Have(
			"the product with the inverse is a fractional ideal",
			"«wfFractional»(«product»)",
			By(
				subring,
				idealInL,
				fractional_ideal.FractionalInverseSubset.Read(L).At(S, m),
				fractional_ideal.FractionalMulSubmodule.Read(L).At(S, m, inverse)))
		productSubset := a.Have(
			"(S : m) multiplies m into S and the product commutes, so m · (S : m) lies in S",
			"«product» ⊆ S",
			BySets(
				subring,
				fractional_ideal.SubringSubmodule.Read(L).At(S),
				fractional_ideal.FractionalInverseDef.At(fieldRing, S, m),
				fractional_ideal.FractionalMulLeast.Read(L).At(S, inverse, m, S),
				idealInL,
				fractional_ideal.FractionalMulComm.Read(L).At(S, m, inverse)))
		multiplicative := comm_ring.MulMonoidOn.Read(ringL)
		oneInverse := a.Have(
			"one multiplies every member of m into S",
			"L.one ∈ «wfInverse»(m)",
			BySets(
				comm_ring.OneIn.Read(ringL),
				comm_monoid.LeftIdentityOn.Read(multiplicative),
				fractionalIdeal,
				idealInL,
				fractional_ideal.FractionalInverseDef.At(fieldRing, S, m)))
		mInProduct := a.Have(
			"multiplication by one puts all of m in the product",
			"m ⊆ «product»",
			BySets(
				comm_monoid.RightIdentityOn.Read(multiplicative),
				idealInL,
				oneInverse,
				At(fractional_ideal.FractionalMulHolds.Read(L), S, m, inverse)))
		sInProduct := a.Have(
			"u lies in m and the ratio in (S : m), so m · (S : m) holds their product s",
			"s ∈ «product»",
			BySets(
				uInM,
				ratioInInverse,
				ratioU,
				fractional_ideal.FractionalMulHolds.Read(L).At(S, m, inverse, u, ratio)))
		productIdeal := a.Have(
			"the product is an ideal of S",
			"«wfIdeal»(«product»)",
			By(
				subring,
				productFractional,
				productSubset,
				fractional_ideal.IntegralIdealFractional.Read(L).At(S, product)))
		oneInProduct := a.Have(
			"the ideal m · (S : m) lies above the maximal m and holds s outside it, so it holds one",
			"L.one ∈ «product»",
			By(
				productIdeal,
				mInProduct,
				sInProduct,
				outside,
				ring_ideal.MaximalIdealMaximal.Read(maximal).At(product)))
		productSpan := a.Have(
			"a subset of S holding one spans S",
			"«wfSpan»(«product») = S",
			By(subring, productSubset, oneInProduct, fractional_ideal.SpanHoldingOne.Read(L).At(S, product)))
		a.Show(
			"m is fractional and its product with (S : m), a submodule spanning S, is S",
			By(
				fractionalIdeal,
				submodule.SpanOfSubmodule.Read(productFractional),
				productSpan,
				fractional_ideal.InvertibleFractionalDef.At(fieldRing, S, m)))
	}),
})}

// JacobianRelationInvertible — an ideal m of S with residue field k,
// spanned by two members u and v that satisfy a relation v * g = u * h,
// is invertible when g lies outside m with u nonzero, or h lies outside
// m with v nonzero. Residues in k make m the ideal of a k-rational point,
// so maximal; the ideal I spanned by u, v, g and h lies above m and holds
// g ∉ m, so it holds one and is S, and RelationIdealInvertible makes m
// invertible. The second case is the first with (u, g) and (v, h)
// exchanged.
var JacobianRelationInvertible = jacobianRelationInvertibleThm{family.Add(registry.ProofEntry{
	Name: "JacobianRelationInvertible",
	Key:  "prop_a0f049771e3805d8",
	Reading: "The relation is a curve's equation read at a point: u and v two functions vanishing " +
		"there, g and h the quotients the equation factors into, and g ∉ m the nonvanishing of a " +
		"partial derivative at the point. u ≠ L.zero is load-bearing: at u = L.zero, v * g = L.zero " +
		"with g ∉ m forces v = L.zero and m = {L.zero}, the residue clause then makes S = k, and " +
		"{L.zero} is not invertible. Properness of m is not assumed: g ∈ S with g ∉ m says m ≠ S.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀k S m:set(A). ∀u v g h:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"∀x:A. x ∈ S ⇒ ∃y:A. y ∈ k ∧ x + -y ∈ m",
			"u ∈ S",
			"v ∈ S",
			"g ∈ S",
			"h ∈ S",
			"m = ideal_span(«wfScalars», {u, v})",
			"v * g = u * h",
			"u ≠ L.zero ∧ g ∉ m ∨ (v ≠ L.zero ∧ h ∉ m)",
		},
		Conclusion: "«wfInvertible»(m)",
		Abbrev: Abbrev{
			{Name: "I", Text: "ideal_span(«wfScalars», {u, v, g, h})"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			criterionAtU := ctx.Lemma(Statement{
				Binders: "∀L:field_on(A). ∀k S m:set(A). ∀u v g h:A.",
				Hypotheses: []string{
					"subring(field_ring(L), S)",
					"subfield(L, k)",
					"k ⊆ S",
					"∀x:A. x ∈ S ⇒ ∃y:A. y ∈ k ∧ x + -y ∈ m",
					"u ∈ S", "v ∈ S", "g ∈ S", "h ∈ S",
					"m = ideal_span(«wfScalars», {u, v})",
					"v * g = u * h", "u ≠ L.zero", "g ∉ m",
				},
				Conclusion: "«wfInvertible»(m)",
			}, func(
				a *Argument,
				L field.FieldFact[on.L],
				k, S, m *Expr[Set[A]],
				u, v, g, h *Expr[A],
				hypotheses Fact,
			) {
				p := a.Conjuncts(
					hypotheses,
					"S is a subring of L",
					"k is a subfield",
					"k lies in S",
					"every residue is represented in k",
					"u lies in S",
					"v lies in S",
					"g lies in S",
					"h lies in S",
					"u and v generate m",
					"the generators satisfy the relation",
					"u is nonzero",
					"g lies outside m")
				subring, subfield, kInS, residue := p[0], p[1], p[2], p[3]
				uInS, vInS, gInS, hInS, span, relation, nonzero, outside :=
					p[4], p[5], p[6], p[7], p[8], p[9], p[10], p[11]
				ringL := field.RingOn.Read(L)
				fieldRing := a.TermAs[module_record.RingOps[A]]("field_ring(L)")
				scalars := a.TermAs[module_record.RingOps[A]]("«wfScalars»")
				invL := a.TermAs[Fun[A, A]]("L.inv")
				pair, generators := a.TermAs[Set[A]]("{u, v}"), a.TermAs[Set[A]]("{u, v, g, h}")
				spanned := a.TermAs[Set[A]]("«I»")
				ringS := a.Have(
					"S is a ring under the inherited operations",
					"comm_ring_on(«wfScalars»)",
					By(subring, comm_ring.SubringRingOn.Read(ringL).At(S)))
				ideal := a.Have(
					"the span m of u and v, both in S, is an ideal of S",
					"«wfIdeal»(m)",
					BySets(uInS, vInS, span, ring_ideal.SpanIdeal.Read(ringS).At(pair)))
				residueField := a.Have(
					"k is a field under the operations of L's ring",
					"ring_subfield(field_ring(L), L.inv, k)",
					By(
						subfield,
						field.SubfieldRingSubfield.Read(L).At(k, S),
						field.RingSubfieldRestrict.At(fieldRing, S, invL, k)))
				oneOutside := a.Have(
					"m misses one: holding it, m would be all of S, and g lies in S outside m",
					"L.one ∉ m",
					BySets(ideal, gInS, outside, ring_ideal.IdealOneIff.Read(ringS).At(m)))
				rational := a.Have(
					"m is the ideal of a k-rational point",
					"rational_ideal(field_ring(L), k, S, m)",
					Simp(Fwd(quotient_ring.RationalIdealDef)),
					By(ideal, oneOutside, residue))
				maximal := a.Have(
					"so m is maximal in S",
					"maximal_ideal(«wfScalars», m)",
					By(
						residueField,
						subring,
						kInS,
						rational,
						quotient_ring.FieldResiduesMaximal.Read(ringL).At(k, invL, S, m)))
				spannedIdeal := a.Have(
					"u, v, g and h lie in S, so the ideal I they span is an ideal of S",
					"«wfIdeal»(«I»)",
					BySets(uInS, vInS, gInS, hInS, ring_ideal.SpanIdeal.Read(ringS).At(generators)))
				above := a.Have(
					"I lies above the m that u and v span, and holds g",
					"m ⊆ «I» ∧ g ∈ «I»",
					span.Rw(),
					BySets(
						ring_ideal.SpanMono.At(scalars, pair, generators),
						ring_ideal.SpanContains.At(scalars, generators)))
				oneInSpan := a.Have(
					"the ideal I lies above the maximal m and holds g outside it, so it holds one",
					"L.one ∈ «I»",
					By(spannedIdeal, above, outside, ring_ideal.MaximalIdealMaximal.Read(maximal).At(spanned)))
				unitIdeal := a.Have(
					"an ideal of S holding one is S",
					"«I» = S",
					By(spannedIdeal, oneInSpan, ring_ideal.IdealOneIff.Read(ringS).At(spanned)))
				a.Show(
					"u is nonzero and u, v, g and h satisfy the relation and span S, so m = (u, v) is invertible",
					By(
						Normalized,
						span,
						subring,
						uInS,
						vInS,
						gInS,
						hInS,
						nonzero,
						relation,
						unitIdeal,
						RelationIdealInvertible.Read(L).At(S, u, v, g, h)))
			})
			return ctx.Theorem(headline, func(
				a *Argument,
				L field.FieldFact[on.L],
				k, S, m *Expr[Set[A]],
				u, v, g, h *Expr[A],
				hypotheses Fact,
			) {
				p := a.Conjuncts(
					hypotheses,
					"S is a subring",
					"k is a subfield",
					"k lies in S",
					"k represents the residues",
					"u lies in S",
					"v lies in S",
					"g lies in S",
					"h lies in S",
					"u and v generate m",
					"the relation holds",
					"one generator is nonzero and the other generator's coefficient lies outside m")
				span, criterion := p[8], p[10]
				a.Show(
					"apply the criterion at the chosen nonzero generator",
					criterion.SplitDisj(
						LeftHolds(
							"u is nonzero and g lies outside m",
							Given(func(b *Argument, atU Fact) {
								b.Show(
									"the criterion at u proves invertibility",
									By(L, hypotheses, atU, At(criterionAtU, b.TermAs[FieldOps[A]]("L"), k, S, m, u, v, g, h)))
							})),
						RightHolds(
							"v is nonzero and h lies outside m",
							Given(func(b *Argument, atV Fact) {
								swappedSpan := b.Have(
									"v and u generate the same ideal, the pair remembering no order",
									"m = ideal_span(«wfScalars», {v, u})",
									By(Normalized, span, set_algebra.InsertComm.At(b.TermAs[Set[A]]("∅"), v, u)))
								b.Show(
									"the criterion at v proves invertibility",
									By(
										L,
										hypotheses,
										swappedSpan,
										atV,
										At(criterionAtU, b.TermAs[FieldOps[A]]("L"), k, S, m, v, u, h, g)))
							}))))
			})
		}),
})}
