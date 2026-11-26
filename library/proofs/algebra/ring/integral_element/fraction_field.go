// fraction_field.go — fraction fields inside a field: the field a subring
// generates is its fraction field, so the field k(t) that a subfield k and
// one element t of a field generate is the fraction field of the polynomial
// values k[t]; finitely many members of a subring, spanning it over a
// subfield, span its fraction field; finitely many fractions over a subring,
// and the coefficients of a polynomial over its fraction field, share a
// common denominator in it, as do finitely many members of K(z) over B[z] for
// z algebraic over the fraction field K of B; so algebraic over the fraction
// field is algebraic over the subring, and independence over the subring
// survives the passage to its fraction field.

package integral_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// SubringFractionField — a subring S of a field has the field it generates as
// its fraction field: the fractions of S form a subfield containing S, so the
// field S generates, the least such, consists of fractions.
var SubringFractionField = subringFractionFieldThm{family.Add(registry.ProofEntry{
	Name: "SubringFractionField",
	Key:  "prop_9af959adf524866b",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{"subring(field_ring(L), S)"},
		Conclusion: "subfield(L, field_adjoin(L, S, ∅)) ∧ " +
			"S ⊆ field_adjoin(L, S, ∅) ∧ " +
			"fraction_field_carrier(restrict_ring(field_ring(L), field_adjoin(L, S, ∅)), S)",
	}, func(arg *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subringS Fact) {
		Q, qDef := arg.LetAs[Set[A]](
			"Q", "{z:A | z ∈ L.carrier ∧ (∃a b:A. a ∈ S ∧ b ∈ S ∧ b ≠ L.zero ∧ z * b = a)}")
		sInL := arg.Have(
			"S lies in the field",
			"S ⊆ L.carrier",
			By(subringS, comm_ring.SubringSubset))
		ratio := arg.Have(
			"membership means a fraction of S",
			"∀z:A. z ∈ Q ⇔ z ∈ L.carrier ∧ (∃a b:A. a ∈ S ∧ b ∈ S ∧ b ≠ L.zero ∧ z * b = a)",
			BySets(qDef))
		isFraction := arg.Have(
			"an element of the field with a numerator and a nonzero denominator in S is a fraction",
			"∀z n m:A. z ∈ L.carrier ∧ n ∈ S ∧ m ∈ S ∧ m ≠ L.zero ∧ z * m = n ⇒ z ∈ Q",
			By(ratio))
		sInQ := arg.Have(
			"an element of S has denominator one",
			"S ⊆ Q",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(element *Argument) {
				x := element.FixAs[A]("x")
				xInS := element.Assume()
				xInField := element.Have(
					"the numerator lies in the field",
					"x ∈ L.carrier",
					By(xInS, sInL, set_basic.SubsetDef))
				fixed := element.Have(
					"multiplication by one fixes x",
					"x * L.one = x",
					ByArith(L, xInField))
				element.Show(
					"so x is the fraction x / one",
					By(
						isFraction.At(x, x, element.TermAs[A]("L.one")),
						L,
						xInS,
						xInField,
						subringS,
						comm_ring.SubringOne,
						field.OneNotZeroOn,
						fixed))
			}))
		fractions := arg.Have(
			"a fraction of S, its numerator and its denominator lie in the field",
			Statement{
				Binders: "∀z:A.",
				Hypotheses: []string{
					"z ∈ Q",
				},
				Conclusion: "∃a b:A. " +
					"    z ∈ L.carrier ∧ a ∈ L.carrier ∧ b ∈ L.carrier ∧ a ∈ S ∧ b ∈ S ∧ b ≠ L.zero ∧ z * b = a",
			},
			By(ratio, sInL, set_basic.SubsetDef))
		// A member of Q written as a fraction: all that fractions states of
		// it together, and the parts a close reads alone.
		type _FractionOfS struct {
			written, inField, numeratorIn, denominatorIn, nonzero, equation Fact
		}
		// represent writes z, resident as a member of Q, as a fraction of S
		// whose numerator and denominator take the given names.
		represent := func(
			branch *Argument,
			z *Expr[A],
			inQ Fact,
			numerator, denominator string,
		) _FractionOfS {
			_, _, written := branch.Unpack2As[A, A](GroupPremises(inQ, fractions.At(z)), numerator, denominator)
			parts := branch.Conjuncts(
				written,
				"the fraction lies in the field",
				"the numerator lies in the field",
				"the denominator lies in the field",
				"the numerator lies in S",
				"the denominator lies in S",
				"the denominator is nonzero",
				"the fraction equation")
			return _FractionOfS{
				written:       written,
				inField:       parts[0],
				numeratorIn:   parts[3],
				denominatorIn: parts[4],
				nonzero:       parts[5],
				equation:      parts[6],
			}
		}
		ring := field.RingOn.Read(L)
		qField := arg.Have(
			"the fractions form a subfield",
			"subfield(L, Q)",
			Simp(Fwd(field.SubfieldDef)),
			SplitConjAll(
				Case(
					"fractions lie in the ambient field",
					By(ratio, set_basic.SubsetDef)),
				Case(
					"zero is a fraction",
					By(sInQ, subringS, comm_ring.SubringZero, set_basic.SubsetDef)),
				Case(
					"one is a fraction",
					By(sInQ, subringS, comm_ring.SubringOne, set_basic.SubsetDef)),
				Case(
					"add fractions with a common denominator",
					Derive(func(sum *Argument) {
						x, y := sum.FixAs[A]("x"), sum.FixAs[A]("y")
						both := sum.Assume()
						first := represent(sum, x, both, "a", "b")
						second := represent(sum, y, both, "c", "d")
						numerator := sum.Have(
							"the cross-product sum lies in S",
							"a * d + c * b ∈ S",
							By(subringS, first.written, second.written, comm_ring.SubringMul, comm_ring.SubringAdd))
						denominator := sum.Have(
							"the product denominator lies in S",
							"b * d ∈ S",
							By(subringS, first.denominatorIn, second.denominatorIn, comm_ring.SubringMul))
						nonzero := sum.Have(
							"the product denominator is nonzero",
							"b * d ≠ L.zero",
							By(field.MulEqZeroOn.Read(L), first.written, second.written))
						equation := sum.Have(
							"the cross-multiplied equations add",
							"(x + y) * (b * d) = a * d + c * b",
							ByArith(
								L,
								first.written,
								second.written,
								Scaled(sum.TermAs[A]("d"), first.equation),
								Scaled(sum.TermAs[A]("b"), second.equation)))
						sum.Show(
							"so the sum is a fraction",
							By(
								isFraction.At(sum.TermAs[A]("x + y"), sum.TermAs[A]("a * d + c * b"), sum.TermAs[A]("b * d")),
								comm_ring.AddIn.Read(ring),
								first.inField,
								second.inField,
								numerator,
								denominator,
								nonzero,
								equation))
					})),
				Case(
					"negate the numerator",
					Derive(func(negation *Argument) {
						x := negation.FixAs[A]("x")
						xInQ := negation.Assume()
						fraction := represent(negation, x, xInQ, "a", "b")
						numerator := negation.Have(
							"the negative numerator lies in S",
							"-a ∈ S",
							By(subringS, fraction.numeratorIn, comm_ring.SubringNeg))
						equation := negation.Have(
							"negate the fraction equation",
							"(-x) * b = -a",
							ByArith(L, fraction.written))
						negation.Show(
							"so the negative is a fraction over the same denominator",
							By(
								isFraction.At(negation.TermAs[A]("-x"), negation.TermAs[A]("-a"), negation.TermAs[A]("b")),
								comm_ring.NegIn.Read(ring),
								fraction.inField,
								numerator,
								fraction.denominatorIn,
								fraction.nonzero,
								equation))
					})),
				Case(
					"multiply numerator and denominator pairs",
					Derive(func(product *Argument) {
						x, y := product.FixAs[A]("x"), product.FixAs[A]("y")
						both := product.Assume()
						first := represent(product, x, both, "a", "b")
						second := represent(product, y, both, "c", "d")
						numerator := product.Have(
							"the numerator product lies in S",
							"a * c ∈ S",
							By(subringS, first.numeratorIn, second.numeratorIn, comm_ring.SubringMul))
						denominator := product.Have(
							"the denominator product lies in S",
							"b * d ∈ S",
							By(subringS, first.denominatorIn, second.denominatorIn, comm_ring.SubringMul))
						nonzero := product.Have(
							"the denominator product is nonzero",
							"b * d ≠ L.zero",
							By(field.MulEqZeroOn.Read(L), first.written, second.written))
						equation := product.Have(
							"multiply the fraction equations",
							"(x * y) * (b * d) = a * c",
							ByArith(
								L,
								first.written,
								second.written,
								Scaled(product.TermAs[A]("y * d"), first.equation),
								Scaled(product.TermAs[A]("a"), second.equation)))
						product.Show(
							"so the product is a fraction",
							By(
								isFraction.At(product.TermAs[A]("x * y"), product.TermAs[A]("a * c"), product.TermAs[A]("b * d")),
								comm_ring.MulIn.Read(ring),
								first.inField,
								second.inField,
								numerator,
								denominator,
								nonzero,
								equation))
					})),
				Case(
					"exchange numerator and denominator of a nonzero fraction",
					Derive(func(inverse *Argument) {
						x := inverse.FixAs[A]("x")
						xInQ := inverse.Assume()
						xNonzero := inverse.Assuming(
							inverse.TermAs[Bool]("x ≠ L.zero"),
							"the inverse of zero is a fraction",
							Derive(func(atZero *Argument) {
								zero := atZero.Hyp("x = L.zero")
								atZero.Show(
									"the inverse of zero belongs to Q",
									By(L, zero, sInQ, subringS, field.InvZeroOn, comm_ring.SubringZero, set_basic.SubsetDef))
							}))
						fraction := represent(inverse, x, xInQ, "a", "b")
						numeratorNonzero := inverse.Have(
							"a nonzero fraction has nonzero numerator",
							"a ≠ L.zero",
							By(Normalized, field.MulEqZeroOn.Read(L), xNonzero, fraction.written))
						cancels := inverse.Have(
							"the inverse cancels the fraction",
							"L.inv(x) * x = L.one",
							By(field.MulLeftInverseOn.Read(L), xNonzero, fraction.inField))
						equation := inverse.Have(
							"multiply by the inverse fraction",
							"L.inv(x) * a = b",
							ByArith(
								L,
								fraction.written,
								Scaled(inverse.TermAs[A]("L.inv(x)"), fraction.equation),
								Scaled(inverse.TermAs[A]("b"), cancels)))
						inverse.Show(
							"so the inverse is a fraction, numerator and denominator exchanged",
							By(
								isFraction.At(inverse.TermAs[A]("L.inv(x)"), inverse.TermAs[A]("b"), inverse.TermAs[A]("a")),
								field.InvIn.Read(L),
								fraction.inField,
								fraction.denominatorIn,
								fraction.numeratorIn,
								numeratorNonzero,
								equation))
					})),
			))
		l := arg.TermAs[FieldOps[A]]("L")
		empty := arg.TermAs[Set[A]]("∅")
		adjoin := arg.Have(
			"the field generated by S contains S",
			"subfield(L, field_adjoin(L, S, ∅)) ∧ S ⊆ field_adjoin(L, S, ∅)",
			BySets(L, sInL, algebraic_element.AdjoinSubfield.At(l, S, empty)))
		least := arg.Have(
			"the generated field consists of fractions of S",
			"field_adjoin(L, S, ∅) ⊆ Q",
			BySets(L, qField, sInQ, algebraic_element.AdjoinLeast.At(l, S, empty, Q)))
		arg.Show(
			"S has the generated field as fraction field",
			BySets(adjoin, least, ratio, field.FractionFieldCarrierDef))
	}),
})}

// RationalFunctionsFractionField — every rational function in t is a
// quotient of polynomials in t: the polynomials are a subring, so the field
// they generate is their fraction field, and that field is k(t), since each
// of the two contains what generates the other.
var RationalFunctionsFractionField = rationalFunctionsFractionFieldThm{family.Add(registry.ProofEntry{
	Name: "RationalFunctionsFractionField",
	Key:  "prop_af5bcae2ca186250",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
		},
		Conclusion: "fraction_field_carrier(restrict_ring(field_ring(L), field_adjoin(L, k, {t})), " +
			"    polynomial_image(field_ring(L), k, t))",
		Abbrev: Abbrev{
			{Name: "polynomials", Text: "polynomial_image(field_ring(L), k, t)"},
			{Name: "rationalFunctions", Text: "field_adjoin(L, k, {t})"},
			{Name: "generated", Text: "field_adjoin(L, «polynomials», ∅)"},
		},
	}, func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], h Fact) {
		polynomials := arg.Have(
			"polynomials form a ring between k and k(t)",
			"subring(field_ring(L), «polynomials») ∧ "+
				"k ⊆ «polynomials» ∧ "+
				"t ∈ «polynomials» ∧ "+
				"«polynomials» ⊆ «rationalFunctions»",
			By(h, algebraic_element.PolynomialImageRing.Read(L).AsFact().At(k, t)))
		polynomialSet := arg.TermAs[Set[A]]("«polynomials»")
		fractions := arg.Have(
			"the polynomials have the field they generate as fraction field",
			"subfield(L, «generated») ∧ "+
				"«polynomials» ⊆ «generated» ∧ "+
				"fraction_field_carrier(restrict_ring(field_ring(L), «generated»), «polynomials»)",
			By(polynomials, SubringFractionField.Read(L).At(polynomialSet)))
		sameField := arg.Have(
			"each of the two fields contains what generates the other",
			"«generated» = «rationalFunctions»",
			BySets(
				h,
				polynomials,
				fractions,
				algebraic_element.AdjoinElementSubfield.Read(L).AsFact().At(k, t),
				algebraic_element.AdjoinLeast.Read(L).At(
					polynomialSet,
					arg.TermAs[Set[A]]("∅"),
					arg.TermAs[Set[A]]("«rationalFunctions»")),
				algebraic_element.AdjoinLeast.Read(L).At(
					k,
					arg.TermAs[Set[A]]("{t}"),
					arg.TermAs[Set[A]]("«generated»"))))
		arg.Show(
			"so k(t) is the fraction field of the polynomials",
			sameField.RwRev(),
			By(fractions))
	}),
})}

// FiniteSubringSpansField — finitely many members of a subring with fraction
// field L, spanning it over K, span L over K: their span is a
// finite-dimensional K-space stable under multiplication by the subring, and
// the pivot is that a nonzero multiplier, injective on the span, therefore
// maps it onto itself (InjectiveImageDim, SubmoduleDimEq); so every fraction
// a/b lands in the span as the preimage of a under b.
var FiniteSubringSpansField = finiteSubringSpansFieldThm{family.Add(registry.ProofEntry{
	Name: "FiniteSubringSpansField",
	Key:  "prop_a3b6ab0eb04f9221",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K B E:set(A).",
		Hypotheses: []string{
			"subfield(L, K)",
			"subring(field_ring(L), B)",
			"fraction_field_carrier(field_ring(L), B)",
			"finite(E)",
			"E ⊆ B",
			"B ⊆ «span»",
		},
		Conclusion: "«span» = L.carrier",
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), K)"},
			{Name: "ambient", Text: "regular_module(field_ring(L))"},
			{Name: "restricted", Text: "λT:set(A). restrict_module(«ambient», T)"},
			{Name: "span", Text: "module_span(«scalars», «ambient», E)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		K, B, E *Expr[Set[A]],
		subfieldK, subringB, fractionsB, finiteE, eInB, bInW Fact,
	) {
		l := a.TermAs[FieldOps[A]]("L")
		kRing := a.TermAs[RingOps[A]]("«scalars»")
		ambient := a.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
		inv := a.TermAs[Fun[A, A]]("L.inv")
		W := a.TermAs[Set[A]]("«span»")
		restrictedW := a.TermAs[module_record.ModuleOps[A, A]]("«restricted»(«span»)")
		ambientK := a.Have(
			"the ambient field is a K-vector space",
			"module_on(«scalars», «ambient»)",
			By(subfieldK, field_extension.SubfieldScalars.Read(L).At(K)))
		bInL := a.Have(
			"B lies in the field",
			"B ⊆ L.carrier",
			By(subringB, comm_ring.SubringSubset))
		eInL := a.Have(
			"E lies in the field",
			"E ⊆ L.carrier",
			By(eInB, bInL, set_order.SubsetTrans))
		wSubmodule := a.Have(
			"the K-span is a submodule",
			"submodule(«scalars», «ambient», «span»)",
			By(ambientK, eInL, submodule.SpanSubmodule))
		wIsSpace := a.Have(
			"the span is a K-vector space",
			"module_on(«scalars», «restricted»(«span»))",
			By(ambientK, wSubmodule, submodule.SubmoduleModuleOn))
		fieldK := a.Have(
			"the scalar ring is a field",
			"ring_subfield(«scalars», L.inv, K)",
			By(L, subfieldK, field.SubfieldRingSubfield.At(l, K, K)))
		finiteW := a.Have(
			"E, finite, spans the span as a module of its own, so the span has finite dimension",
			"finite_dimensional(«scalars», «restricted»(«span»))",
			By(
				wIsSpace,
				fieldK,
				finiteE,
				ambientK,
				wSubmodule,
				submodule.SubsetSpan.At(kRing, ambient, E),
				linear_independence.SpanRestrict.At(kRing, ambient, W, E),
				module_dimension.FiniteDimensionalSpanning.At(kRing, restrictedW, inv)))
		wInL := a.Have(
			"the span lies in the ambient field",
			"«span» ⊆ L.carrier",
			By(wSubmodule, submodule.SubmoduleSubset))
		onTo := a.Have(
			"a nonzero element of B maps the span onto itself",
			"∀b:A. b ∈ B ∧ b ≠ L.zero ⇒ image(L.mul(b), «span») = «span»",
			Derive(func(scaling *Argument) {
				b := scaling.FixAs[A]("b")
				multiplier := scaling.Assume()
				bInField := scaling.Have(
					"the multiplier lies in the field",
					"b ∈ L.carrier",
					By(bInL, multiplier, set_basic.SubsetDef))
				bMember := scaling.MemberOf[on.L](b, bInField)
				mulB := scaling.TermAs[Fun[A, A]]("L.mul(b)")
				linear := scaling.Have(
					"multiplication is K-linear on the field",
					"module_homomorphism(«scalars», «ambient», «ambient», L.mul(b))",
					By(subfieldK, field_extension.MultiplicationLinear.Read(L).At(K, bMember)))
				multiplesInW := scaling.Have(
					"multiplication by b sends E into B, so into the span",
					"image(L.mul(b), E) ⊆ «span»",
					BySets(subringB, multiplier, eInB, bInW, comm_ring.SubringMul))
				preservesW := scaling.Have(
					"so it preserves the K-span of E",
					"image(L.mul(b), «span») ⊆ «span»",
					By(
						linear,
						eInL,
						wSubmodule,
						multiplesInW,
						linear_independence.HomSpanInSubmodule.At(kRing, ambient, ambient, mulB, E, W)))
				endomorphism := scaling.Have(
					"multiplication restricts to an endomorphism",
					"module_homomorphism(«scalars», «restricted»(«span»), «restricted»(«span»), L.mul(b))",
					BySets(
						linear,
						wSubmodule,
						preservesW,
						module_homomorphism.HomRestrict.At(kRing, ambient, ambient, mulB, W, W)))
				injective := scaling.Have(
					"a nonzero multiplier is injective on the span",
					"injective_on(«span», L.mul(b))",
					By(multiplier, wInL, field.MulBijective.Read(L).At(bMember), functions.InjectiveOnSubset))
				dimension := scaling.Have(
					"the image has the dimension of the span",
					"module_dim(«scalars», restrict_module(«restricted»(«span»), image(L.mul(b), «span»))) = "+
						"module_dim(«scalars», «restricted»(«span»))",
					By(
						fieldK,
						endomorphism,
						injective,
						finiteW,
						module_dimension.InjectiveImageDim.At(kRing, inv, restrictedW, restrictedW, mulB)))
				scaling.Show(
					"equal finite dimension makes the image the whole span",
					By(
						wIsSpace,
						fieldK,
						finiteW,
						endomorphism,
						module_homomorphism.ImageSubmodule.At(kRing, restrictedW, restrictedW, mulB),
						dimension,
						module_dimension.SubmoduleDimEq.At(
							kRing, restrictedW, inv, scaling.TermAs[Set[A]]("image(L.mul(b), «span»)"))))
			}))
		lInW := a.Have(
			"every fraction of B lies in the span",
			"L.carrier ⊆ «span»",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(element *Argument) {
				x := element.FixAs[A]("x")
				xInL := element.Assume()
				_, b, fraction := element.Obtain2As[A, A](
					"choose a numerator and a denominator in B",
					"∃a b:A. a ∈ B ∧ b ∈ B ∧ b ≠ L.zero ∧ x * b = a",
					By(fractionsB, xInL, field.FractionFieldCarrierDef))
				y, preimage := element.ObtainAs[A](
					"the denominator reaches the numerator from the span",
					"∃y:A. y ∈ «span» ∧ b * y = a",
					BySets(onTo, bInW, fraction))
				byInL := element.Have(
					"the multiplier and preimage lie in the field",
					"b ∈ L.carrier ∧ y ∈ L.carrier",
					By(bInL, wInL, fraction, preimage, set_basic.SubsetDef))
				fieldPoints := element.Conjuncts(
					byInL,
					"the denominator lies in the field",
					"the preimage lies in the field")
				bMember := element.MemberOf[on.L](b, fieldPoints[0])
				aInL := element.Have(
					"the numerator lies in the field",
					"a ∈ L.carrier",
					By(bInL, fraction, set_basic.SubsetDef))
				equalImages := element.Have(
					"the fraction and preimage have the same multiple",
					"b * x = b * y",
					ByArith(L, xInL, aInL, byInL, fraction, preimage))
				element.Show(
					"a nonzero denominator cancels, so the fraction is its preimage",
					By(
						integral_domain.MulCancelLeft.Read(integral_domain.FieldIntegralDomain.Read(L)).At(
							bMember,
							element.MemberOf[on.L](x, xInL),
							element.MemberOf[on.L](y, fieldPoints[1])),
						fraction,
						preimage,
						equalImages))
			}))
		a.Show(
			"the span is the whole field",
			By(lInW, wInL, set_order.SubsetAntisym))
	}),
})}

// FiniteCommonDenominator — finitely many fractions over S share one
// nonzero denominator: on inserting a fraction, multiply its denominator
// by the denominator that clears the previous set.
var FiniteCommonDenominator = finiteCommonDenominatorThm{family.Add(registry.ProofEntry{
	Name: "FiniteCommonDenominator",
	Key:  "prop_93ee368bcce5c44a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S E:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"fraction_field_carrier(field_ring(L), S)",
			"finite(E)",
			"E ⊆ L.carrier",
		},
		Conclusion: "∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), E) ⊆ S",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			S, E *Expr[Set[A]],
			subring, fractions, finite, inside Fact,
		) {
			ring := field.RingOn.Read(L)
			ambient := a.TermAs[RingOps[A]]("field_ring(L)")
			points := a.Unfolded(inside, set_basic.SubsetDef)
			a.Show(
				"finite induction, multiplying the denominators at each insertion",
				ByInduction(finite_set.FiniteInductFreshOn, finite, points,
					Case(
						"one clears the empty set",
						Derive(func(b *Argument) {
							b.Do(
								Witness(b.TermAs[A]("L.one")),
								BySets(comm_ring.SubringOne.Read(subring), field.OneNotZeroOn.Read(L)),
							)
						})),
					Case(
						"multiply the old common denominator by a denominator of the inserted point",
						Derive(func(step *Argument) {
							x := step.FixAs[A]("x")
							step.FixAs[Set[A]]("t")
							induction := step.Assume()
							conditions := step.Conjuncts(
								induction,
								"t has a common nonzero denominator",
								"x is outside t",
								"t is finite",
								"x lies in the field",
								"every point of t lies in the field")
							xInL, oldPoints := conditions[3], conditions[4]
							d, previous := step.UnpackAs[A](conditions[0], "d")
							old := step.Conjuncts(
								previous,
								"d lies in S",
								"d is nonzero",
								"d clears t")
							dInS, dNonzero, clears := old[0], old[1], old[2]
							fractionAtX := step.Have(
								"x has a numerator and a nonzero denominator in S",
								"∃c b:A. c ∈ S ∧ b ∈ S ∧ b ≠ L.zero ∧ x * b = c",
								By(fractions, xInL, field.FractionFieldCarrierDef.At(ambient, S)))
							c, denominator, relation := step.Unpack2As[A, A](fractionAtX, "c", "b")
							fractionParts := step.Conjuncts(
								relation,
								"c lies in S",
								"b lies in S",
								"b is nonzero",
								"multiplying x by b gives c")
							cInS, bInS, bNonzero, fraction :=
								fractionParts[0], fractionParts[1], fractionParts[2], fractionParts[3]
							inField := step.Have(
								"the denominators and numerator lie in the ambient field",
								"d ∈ L.carrier ∧ c ∈ L.carrier ∧ b ∈ L.carrier",
								BySets(comm_ring.SubringSubset.Read(subring), dInS, cInS, bInS))
							fieldPoints := step.Conjuncts(
								inField,
								"d lies in L",
								"c lies in L",
								"b lies in L")
							dMember := step.MemberOf[on.L](d, fieldPoints[0])
							cMember := step.MemberOf[on.L](c, fieldPoints[1])
							bMember := step.MemberOf[on.L](denominator, fieldPoints[2])
							xMember := step.MemberOf[on.L](x, xInL)
							oldCleared := step.Have(
								"the extra denominator factor keeps the previous products in S",
								"∀y:A. y ∈ t ⇒ d * b * y ∈ S",
								Derive(func(g *Argument) {
									y := g.FixAs[A]("y")
									yInT := g.Assume()
									oldProduct := g.Have(
										"d already clears y",
										"d * y ∈ S",
										BySets(clears, yInT))
									reassociate := g.Have(
										"the new product is b times the old cleared product",
										"(d * b) * y = b * (d * y)",
										ByArith(ring, dMember, bMember, oldPoints.At(y), yInT))
									g.Show(
										"both factors of b times d y belong to S",
										By(
											Normalized,
											reassociate,
											oldProduct,
											bInS,
											comm_ring.SubringMul.Read(subring).AsFact().At(denominator, g.TermAs[A]("d * y"))))
								}))
							scaled := step.Have(
								"multiplying x b = c by d gives the cleared product d c",
								"(d * b) * x = d * c",
								ByArith(ring, dMember, bMember, cMember, xMember, Scaled(d, fraction)))
							newCleared := step.Have(
								"the fraction identity clears the inserted point",
								"(d * b) * x ∈ S",
								By(Normalized, scaled, dInS, cInS, comm_ring.SubringMul.Read(subring).AsFact().At(d, c)))
							step.Do(Witness(step.TermAs[A]("d * b")), SplitConjAll(
								Case(
									"the product denominator belongs to S",
									By(dInS, bInS, comm_ring.SubringMul.Read(subring).AsFact().At(d, denominator))),
								Case(
									"a product of nonzero field elements is nonzero",
									By(dNonzero, bNonzero, field.MulEqZeroOn.Read(L).At(dMember, bMember))),
								Case(
									"the product clears both the previous set and the new point",
									BySets(newCleared, oldCleared)),
							))
						})),
				))
		}),
})}

// PolynomialCommonDenominator — a polynomial over the fraction field B of a
// subring S has a common denominator in S: a nonzero d ∈ S with every d·p(i)
// in S. The coefficients of p below the index from which it vanishes, with
// zero, form a finite subset E of B; B, a field under the operations of L, is
// the fraction field of S, so E has a common denominator in S
// (FiniteCommonDenominator), and every coefficient of p lies in E.
var PolynomialCommonDenominator = polynomialCommonDenominatorThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCommonDenominator",
	Key:  "prop_9fd14d8a88270552",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀B S:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"subfield(L, B)",
			"subring(field_ring(L), S)",
			"fraction_field_carrier(restrict_ring(field_ring(L), B), S)",
			"polynomial_over(B, p)",
		},
		Conclusion: "∃d:A. d ∈ S ∧ d ≠ L.zero ∧ (∀i:num. d * p(i) ∈ S)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		B, S *Expr[Set[A]],
		p *Arrow[Nat, A],
		BField, subring, fractions, pOver Fact,
	) {
		fieldOps := a.TermAs[FieldOps[A]]("L")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")

		// B is a field with the operations of L, and the fraction field of S.
		restrictedField := a.Have(
			"B is a field under the operations of L",
			"field_on(restrict_field(L, B))",
			By(BField, field.SubfieldFieldOn.Read(L).At(B)))
		restricted := a.Have(
			"the ring of that field is the restriction of the ring of L to B",
			"restrict_ring(field_ring(L), B) = field_ring(restrict_field(L, B))",
			Cite(field.RestrictFieldRing))
		SInB := a.Have(
			"S lies in B",
			"S ⊆ B",
			By(fractions, field.FractionFieldCarrierDef))
		subringOfB := a.Have(
			"S is a subring of the field B",
			"subring(field_ring(restrict_field(L, B)), S)",
			Simp(Rev(restricted)),
			By(subring, SInB, comm_ring.SubringRestrict.At(fieldRing, S, B)))
		fractionsOfB := a.Have(
			"B is the fraction field of S",
			"fraction_field_carrier(field_ring(restrict_field(L, B)), S)",
			Simp(Rev(restricted)),
			By(fractions))

		// The coefficients of p, with zero, form a finite subset E of B.
		n, support := a.ObtainAs[Nat](
			"p vanishes from some index n on, and its coefficients lie in B",
			"∃n:num. vec⟨n⟩(p) ∧ (∀i:num. p(i) ∈ B)",
			By(pOver, polynomial.PolynomialOverDef),
			Named("n"))
		E, EDef := a.LetAs[Set[A]]("E", "insert(L.zero, image(p, {i:num | i < n}))")
		finiteE := a.Have(
			"the coefficients below n, with zero, form a finite set E",
			"finite(E)",
			By(
				EDef,
				num_segment.FiniteBelowStrict.At(n),
				finite_set.FiniteImage.At(p, a.TermAs[Set[Nat]]("{i:num | i < n}")),
				finite_set.FiniteRules))
		insideB := a.Have(
			"E lies in B",
			"E ⊆ B",
			BySets(field.SubfieldZero.At(fieldOps, B), BField, EDef, support))
		everyCoefficient := a.Have(
			"every coefficient of p lies in E",
			"∀i:num. p(i) ∈ E",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Cases(b.TermAs[Bool]("i < n"))
				b.When(
					"below n the coefficient is one of those listed in E",
					func(c *Argument, below Fact) {
						c.Show(
							"p(i) is in the image part of E",
							BySets(below, EDef))
					})
				b.Otherwise(
					"from n on the coefficient is zero, which E contains",
					BySets(
						EDef,
						support,
						At(vec_space.VecDef, b.TermAs[A]("L.zero"), n, p),
						nat_order.NotLessThan.At(i, n)))
			}))
		d, denominator := a.ObtainAs[A](
			"E has a common denominator d ∈ S, B being the fraction field of S",
			"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), E) ⊆ S",
			By(
				restrictedField,
				subringOfB,
				fractionsOfB,
				finiteE,
				insideB,
				FiniteCommonDenominator.At(a.TermAs[FieldOps[A]]("restrict_field(L, B)"), S, E)),
			Named("d"))
		a.Take(d)
		a.Show(
			"d clears every coefficient of p, each a member of E",
			BySets(everyCoefficient, denominator))
	}),
})}

// AlgebraicOverFractionSubring — an element z of L algebraic over a subfield
// B that is the fraction field of a subring S is algebraic over S. A nonzero
// polynomial p over B vanishing at z has a common denominator d ∈ S
// (PolynomialCommonDenominator), which makes d·p a polynomial over S; it is
// nonzero, d and a nonzero coefficient of p having a nonzero product, and it
// vanishes at z.
var AlgebraicOverFractionSubring = algebraicOverFractionSubringThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicOverFractionSubring",
	Key:  "prop_ee2808a72fc3ba3a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀B S:set(A). ∀z:A.",
		Hypotheses: []string{
			"subfield(L, B)",
			"subring(field_ring(L), S)",
			"fraction_field_carrier(restrict_ring(field_ring(L), B), S)",
			"z ∈ L.carrier",
			"algebraic_over(L, B, z)",
		},
		Conclusion: "algebraic_over(L, S, z)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		B, S *Expr[Set[A]],
		z *Expr[A],
		BField, subring, fractions, zIn, algebraic Fact,
	) {
		ring := field.RingOn.Read(L)
		fieldOps := a.TermAs[FieldOps[A]]("L")
		p, relation := a.ObtainAs[Fun[Nat, A]](
			"a nonzero polynomial p over B vanishes at z",
			"∃p:(num → A). polynomial_over(B, p) ∧ p ≠ vec_zero ∧ polynomial_eval(p, z) = L.zero",
			By(algebraic, algebraic_element.AlgebraicOverDef),
			Named("p"))
		parts := a.Conjuncts(
			relation,
			"p is a polynomial over B",
			"p is not zero",
			"p vanishes at z")
		pOver, pNonzero, pRoot := parts[0], parts[1], parts[2]
		d, denominator := a.ObtainAs[A](
			"a common denominator d ∈ S of the coefficients of p",
			"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ (∀i:num. d * p(i) ∈ S)",
			By(BField, subring, fractions, pOver, PolynomialCommonDenominator.Read(L).At(B, S, p)),
			Named("d"))
		denominatorParts := a.Conjuncts(
			denominator,
			"d lies in S",
			"d is not zero",
			"d clears every coefficient of p")
		dInS, dNonzero, cleared := denominatorParts[0], denominatorParts[1], denominatorParts[2]
		_, support := a.ObtainAs[Nat](
			"p vanishes from some index n on, and its coefficients lie in B",
			"∃n:num. vec⟨n⟩(p) ∧ (∀i:num. p(i) ∈ B)",
			By(pOver, polynomial.PolynomialOverDef),
			Named("n"))
		dInL := a.Have(
			"d lies in L",
			"d ∈ L.carrier",
			BySets(dInS, comm_ring.SubringSubset.Read(subring)))
		coefficientsInL := a.Have(
			"so do the coefficients of p",
			"∀i:num. p(i) ∈ L.carrier",
			BySets(support, BField, field.SubfieldSubset.At(fieldOps, B)))
		pOverL := a.Have(
			"p is a polynomial over L",
			"polynomial_over(L.carrier, p)",
			By(Normalized, coefficientsInL, support, polynomial.PolynomialOverDef))

		// The scaled polynomial d·p.
		scaledVanishes := a.Have(
			"d·p vanishes from n on, d times zero being zero",
			"vec⟨n⟩(d • p)",
			By(support, dInL, vec_space.VecDef, vec_space.VecScalarMulDef, comm_ring.MulRightZeroOn.Read(ring)))
		scaledOver := a.Have(
			"so d·p is a polynomial over S",
			"polynomial_over(S, d • p)",
			By(scaledVanishes, cleared, vec_space.VecScalarMulDef, polynomial.PolynomialOverDef))
		scaledNonzero := a.Have(
			"d·p is not zero: d and a nonzero coefficient of p have a nonzero product",
			"d • p ≠ vec_zero",
			By(
				pNonzero,
				dNonzero,
				dInL,
				coefficientsInL,
				vec_space.VecZeroDef,
				vec_space.VecScalarMulDef,
				field.MulEqZeroOn.Read(L)))
		scaledRoot := a.Have(
			"d·p vanishes at z, its value being d times the value of p",
			"polynomial_eval(d • p, z) = L.zero",
			By(
				pRoot,
				pOverL,
				polynomial_evaluation.EvalScalar.Read(ring).At(
					a.MemberOf[on.L](d, dInL), a.MemberOf[on.L](z, zIn), p),
				comm_ring.MulRightZeroOn.Read(ring)))
		a.Show(
			"d·p is a nonzero polynomial over S vanishing at z",
			By(scaledOver, scaledNonzero, scaledRoot, algebraic_element.AlgebraicOverDef))
	}),
})}

// AdjoinCommonDenominator — let z be algebraic over a subfield K, the field of
// fractions of a subring B. Every y in K(z) has a denominator in B carrying it into
// B[z]: y is the value at z of a polynomial over K, and a common denominator of its
// finitely many coefficients clears them into B.
var AdjoinCommonDenominator = adjoinCommonDenominatorThm{family.Add(registry.ProofEntry{
	Name: "AdjoinCommonDenominator",
	Key:  "prop_afb6951681a029eb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K B:set(A). ∀z y:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subring(field_ring(L), B)",
			"fraction_field_carrier(restrict_ring(field_ring(L), K), B)",
			"z ∈ L.carrier",
			"algebraic_over(L, K, z)",
			"y ∈ field_adjoin(L, K, {z})",
		},
		Conclusion: "∃d:A. d ∈ B ∧ d ≠ L.zero ∧ d * y ∈ polynomial_image(field_ring(L), B, z)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, B *Expr[Set[A]],
		z, y *Expr[A],
		subK, subB, fractions, zIn, algebraic, yIn Fact,
	) {
		ring := field.RingOn.Read(L)
		zero := arg.TermAs[A]("L.zero")
		R := arg.TermAs[RingOps[A]]("field_ring(L)")
		inImage := arg.Have(
			"y is a polynomial in z over K",
			"y ∈ polynomial_image(field_ring(L), K, z)",
			By(
				Normalized,
				subK,
				zIn,
				algebraic,
				yIn,
				algebraic_element.AdjoinEqImage.Read(L).At(K, arg.MemberOf[on.L](z, zIn))))
		p, value := arg.ObtainAs[Fun[Nat, A]](
			"write y as the value at z of a polynomial over K",
			"∃p:(num → A). polynomial_over(K, p) ∧ y = polynomial_eval(p, z)",
			BySets(inImage, algebraic_element.PolynomialImageDef.At(R, K, z)))
		parts := arg.Conjuncts(
			value,
			"p is over K",
			"y is its value at z")
		pOver, yIs := parts[0], parts[1]
		F := arg.TermAs[FieldOps[A]]("restrict_field(L, K)")
		fieldF := arg.Have(
			"K is a field",
			"field_on(restrict_field(L, K))",
			By(subK, field.SubfieldFieldOn.Read(L).At(K)))
		ringF := arg.Have(
			"its ring is K under the operations of L",
			"field_ring(restrict_field(L, K)) = restrict_ring(field_ring(L), K)",
			By(field.RestrictFieldRing.At(arg.TermAs[FieldOps[A]]("L"), K)))
		subF := arg.Have(
			"B is a subring of it, with fraction field K",
			"subring(field_ring(restrict_field(L, K)), B) ∧ "+
				"fraction_field_carrier(field_ring(restrict_field(L, K)), B)",
			ringF.Rw(),
			Derive(func(b *Argument) {
				inK := b.Have(
					"B lies in K",
					"B ⊆ K",
					By(
						fractions,
						field.FractionFieldCarrierDef.At(b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), K)"), B)))
				b.Show(
					"B is a subring inside K",
					By(subB, inK, fractions, comm_ring.SubringRestrict.At(R, B, K)))
			}))
		E, EDef := arg.LetAs[Set[A]](
			"E", "insert(L.zero, image(p, {i:num | i < suc(polynomial_degree(p))}))")
		eFinite := arg.Have(
			"p has finitely many coefficients",
			"finite(E)",
			EDef.Rw(),
			By(
				finite_set.FiniteRules,
				finite_set.FiniteImage.At(p, arg.TermAs[Set[Nat]]("{i:num | i < suc(polynomial_degree(p))}")),
				num_segment.FiniteBelowStrict.At(arg.TermAs[Nat]("suc(polynomial_degree(p))"))))
		pCoefficients := arg.Have(
			"every coefficient of p lies in E",
			"∀i:num. p(i) ∈ E",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				top := b.Have(
					"past the degree a coefficient vanishes",
					"¬(i < suc(polynomial_degree(p))) ⇒ p(i) = L.zero",
					By(
						pOver,
						polynomial.DegreeVec.At(zero, K, p),
						At(vec_space.VecDef, zero, b.TermAs[Nat]("suc(polynomial_degree(p))"), p),
						nat_order.NotLessThan))
				b.Show(
					"so it is zero or among the first coefficients",
					BySets(EDef, top))
			}))
		pOverE := arg.Have(
			"p is a polynomial with coefficients in E",
			"polynomial_over(E, p)",
			By(pOver, pCoefficients, polynomial.PolynomialOverDef))
		eInK := arg.Have(
			"E lies in K",
			"E ⊆ K",
			Derive(func(b *Argument) {
				zeroInK := b.Have(
					"K holds zero",
					"L.zero ∈ K",
					By(subK, field.SubfieldZero.At(b.TermAs[FieldOps[A]]("L"), K)))
				coefficients := b.Have(
					"K holds the coefficients of p",
					"∀i:num. p(i) ∈ K",
					By(pOver, polynomial.PolynomialOverDef))
				b.Show(
					"so K holds E",
					BySets(EDef, zeroInK, coefficients))
			}))
		d, cleared := arg.ObtainAs[A](
			"a common denominator of the coefficients lies in B",
			"∃d:A. d ∈ B ∧ d ≠ L.zero ∧ image(L.mul(d), E) ⊆ B",
			By(fieldF, subF, eFinite, eInK, FiniteCommonDenominator.At(F, B, E)))
		clear := arg.Conjuncts(
			cleared,
			"d lies in B",
			"d is not zero",
			"d clears E into B")
		dIn, dNonzero, clears := clear[0], clear[1], clear[2]
		dInField := arg.Have(
			"d lies in L",
			"d ∈ L.carrier",
			BySets(dIn, subB, comm_ring.SubringSubset.At(R, B)))
		scaled := arg.Have(
			"so d p is a polynomial over B",
			"polynomial_over(B, λi:num. L.mul(d, p(i)))",
			Derive(func(b *Argument) {
				inB := b.Have(
					"d carries E into B",
					"∀x:A. x ∈ E ⇒ L.mul(d, x) ∈ B",
					BySets(clears))
				zeroFixed := b.Have(
					"d times zero is zero",
					"L.mul(d, L.zero) = L.zero",
					ByArith(ring, dInField))
				b.Show(
					"move the coefficients of p along multiplication by d",
					By(
						pOverE,
						inB,
						zeroFixed,
						polynomial.PolynomialOverMap.At(b.TermAs[Fun[A, A]]("L.mul(d)"), zero, zero, E, B, p)))
			}))
		witness := arg.Have(
			"d y is the value at z of the polynomial d p",
			"∃q:(num → A). polynomial_over(B, q) ∧ d * y = polynomial_eval(q, z)",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Fun[Nat, A]]("λi:num. L.mul(d, p(i))"))
				scalar := b.Have(
					"d p is the scalar multiple of p by d",
					"(λi:num. L.mul(d, p(i))) = vec_scalar_mul(d, p)",
					Derive(func(c *Argument) {
						c.Do(Funext())
						c.FixAs[Nat]("i")
						c.Do(Simp(Fwd(vec_space.VecScalarMulDef)))
						c.Do(Refl())
					}))
				pOverL := b.Have(
					"p is a polynomial over L",
					"polynomial_over(L.carrier, p)",
					By(
						pOver,
						subK,
						field.SubfieldSubset.At(b.TermAs[FieldOps[A]]("L"), K),
						polynomial.PolynomialOverMono.At(zero, K, b.TermAs[Set[A]]("L.carrier"), p)))
				b.Do(SplitConj(
					Case(
						"d p is over B",
						By(scaled)),
					Case(
						"its value at z is d y",
						scalar.Rw(),
						yIs.Rw(),
						GroupPremises(
							dInField, zIn, pOverL, polynomial_evaluation.EvalScalar.Read(ring).AsFact().At(d, z, p)).Rw(),
						Basic())))
			}))
		arg.Take(d)
		member := arg.Have(
			"so d y lies in B[z]",
			"d * y ∈ polynomial_image(field_ring(L), B, z)",
			BySets(witness, algebraic_element.PolynomialImageDef.At(R, B, z)))
		arg.Show(
			"d is a denominator of y in B",
			By(dIn, dNonzero, member))
	}),
})}

// FiniteAdjoinDenominator — finitely many elements of K(z) have one denominator in
// B carrying them into B[z], the product of denominators of the elements one at a
// time.
var FiniteAdjoinDenominator = finiteAdjoinDenominatorThm{family.Add(registry.ProofEntry{
	Name: "FiniteAdjoinDenominator",
	Key:  "prop_809a7bde51686a5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀K B E:set(A). ∀z:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subring(field_ring(L), B)",
			"fraction_field_carrier(restrict_ring(field_ring(L), K), B)",
			"z ∈ L.carrier",
			"algebraic_over(L, K, z)",
			"finite(E)",
			"E ⊆ field_adjoin(L, K, {z})",
		},
		Conclusion: "∃d:A. " +
			"    d ∈ B ∧ d ≠ L.zero ∧ (∀y:A. y ∈ E ⇒ d * y ∈ polynomial_image(field_ring(L), B, z))",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		K, B, E *Expr[Set[A]],
		z *Expr[A],
		subK, subB, fractions, zIn, algebraic, finiteE, inside Fact,
	) {
		ring := field.RingOn.Read(L)
		fieldL := arg.TermAs[FieldOps[A]]("L")
		R := arg.TermAs[RingOps[A]]("field_ring(L)")
		elements := arg.Have(
			"every element of E lies in K(z)",
			"∀y:A. y ∈ E ⇒ y ∈ field_adjoin(L, K, {z})",
			BySets(inside))
		image := arg.Conjuncts(
			GroupPremises(
				subB, algebraic_element.PolynomialImageSubring.Read(L).At(B, arg.MemberOf[on.L](z, zIn))),
			"B[z] is a subring",
			"holding B",
			"and z")
		subBz, bInBz := image[0], image[1]
		absorbs := arg.Have(
			"B[z] absorbs multiplication by B",
			Statement{
				Binders: "∀b w:A.",
				Hypotheses: []string{
					"b ∈ B",
					"w ∈ polynomial_image(field_ring(L), B, z)",
				},
				Conclusion: "b * w ∈ polynomial_image(field_ring(L), B, z)",
			},
			Derive(func(c *Argument) {
				b := c.FixAs[A]("b")
				w := c.FixAs[A]("w")
				parts := c.Conjuncts(
					c.Assume(),
					"b lies in B",
					"w lies in B[z]")
				bIn := c.Have(
					"b lies in B[z]",
					"b ∈ polynomial_image(field_ring(L), B, z)",
					BySets(parts[0], bInBz))
				c.Show(
					"B[z] is a subring",
					By(
						subBz,
						bIn,
						parts[1],
						comm_ring.SubringMul.At(R, c.TermAs[Set[A]]("polynomial_image(field_ring(L), B, z)"), b, w)))
			}))
		inField := arg.Have(
			"K(z) lies in L",
			"field_adjoin(L, K, {z}) ⊆ L.carrier",
			Derive(func(c *Argument) {
				adjoined := c.Have(
					"K(z) is a subfield",
					"subfield(L, field_adjoin(L, K, {z}))",
					By(subK, zIn, algebraic_element.AdjoinElementSubfield.Read(L).At(K, c.MemberOf[on.L](z, zIn))))
				c.Show(
					"a subfield lies in L",
					By(adjoined, field.SubfieldSubset.At(fieldL, c.TermAs[Set[A]]("field_adjoin(L, K, {z})"))))
			}))
		single := arg.Have(
			"each element of K(z) has a denominator",
			Statement{
				Binders:    "∀y:A.",
				Hypotheses: []string{"y ∈ field_adjoin(L, K, {z})"},
				Conclusion: "∃d:A. d ∈ B ∧ d ≠ L.zero ∧ d * y ∈ polynomial_image(field_ring(L), B, z)",
			},
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				b.Show(
					"the denominator of a single element",
					By(
						L,
						subK,
						subB,
						fractions,
						zIn,
						algebraic,
						b.Assume(),
						AdjoinCommonDenominator.At(fieldL, K, B, z, y)))
			}))
		arg.Show(
			"induction on the finite set E",
			ByInduction(finite_set.FiniteInductFreshOn, elements, finiteE,
				Case(
					"one is a denominator of the empty set",
					Derive(func(b *Argument) {
						b.Take(b.TermAs[A]("L.one"))
						b.Show(
							"one lies in B and is not zero",
							By(subB, comm_ring.SubringOne.At(R, B), field.OneNotZeroOn.Read(L), set_basic.NotInEmpty))
					})),
				Case(
					"a new element multiplies the denominator by its own",
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						c.FixAs[Set[A]]("F")
						given := c.Conjuncts(
							c.Assume(),
							"F has a denominator",
							"x is new",
							"F is finite",
							"x lies in K(z)",
							"F lies in K(z)")
						d0, first := c.UnpackAs[A](given[0], "d₀")
						d0Parts := c.Conjuncts(
							first,
							"d₀ lies in B",
							"d₀ is not zero",
							"d₀ clears F")
						d1, second := c.UnpackAs[A](GroupPremises(given[3], single.At(x)), "d₁")
						d1Parts := c.Conjuncts(
							second,
							"d₁ lies in B",
							"d₁ is not zero",
							"d₁ clears x")
						inL := c.Have(
							"d₀ and d₁ lie in L",
							"d₀ ∈ L.carrier ∧ d₁ ∈ L.carrier",
							BySets(d0Parts[0], d1Parts[0], subB, comm_ring.SubringSubset.At(R, B)))
						c.Take(c.TermAs[A]("d₀ * d₁"))
						c.Do(SplitConjAll(
							Case(
								"d₀ d₁ lies in B",
								By(d0Parts[0], d1Parts[0], subB, comm_ring.SubringMul.At(R, B, d0, d1))),
							Case(
								"d₀ d₁ is not zero",
								By(inL, d0Parts[1], d1Parts[1], field.MulEqZeroOn.Read(L).AsFact().At(d0, d1))),
							Case(
								"d₀ d₁ clears x and F",
								Derive(func(d *Argument) {
									y := d.FixAs[A]("y")
									yIn := d.Assume()
									cases := d.Have(
										"y is x, or lies in F",
										"y = x ∨ y ∈ F",
										BySets(yIn))
									d.Cases(d.Term("y = x"))
									d.When(
										"at x, d₀ multiplies the value d₁ clears",
										func(e *Argument, atX Fact) {
											xField := e.Have(
												"x lies in L",
												"x ∈ L.carrier",
												BySets(given[3], inField))
											regroup := e.Have(
												"(d₀ d₁) x is d₀ (d₁ x)",
												"(d₀ * d₁) * x = d₀ * (d₁ * x)",
												ByArith(ring, inL, xField))
											e.Show(
												"which lies in B[z]",
												atX.Rw(),
												regroup.Rw(),
												By(absorbs.At(d0, e.TermAs[A]("d₁ * x")), d0Parts[0], d1Parts[2]))
										})
									d.Otherwise(
										"on F, d₁ multiplies the value d₀ clears",
										func(e *Argument, away Fact) {
											yInF := e.Have(
												"y lies in F",
												"y ∈ F",
												By(cases, away))
											yField := e.Have(
												"y lies in L",
												"y ∈ L.carrier",
												BySets(yInF, given[4], inField))
											regroup := e.Have(
												"(d₀ d₁) y is d₁ (d₀ y)",
												"(d₀ * d₁) * y = d₁ * (d₀ * y)",
												ByArith(ring, inL, yField))
											e.Show(
												"which lies in B[z]",
												regroup.Rw(),
												By(absorbs.At(d1, e.TermAs[A]("d₀ * y")), d1Parts[0], d0Parts[2].At(y), yInF))
										})
								}))))
					}))))
	}),
})}

// FiniteSpanCommonDenominator — the S-span of finitely many elements of a
// field, with the field the fraction field of a subring B that is an
// S-submodule, has one nonzero denominator in B: the one clearing the
// generators (FiniteCommonDenominator) scales them into B, and multiplication
// by it, being S-linear, carries their span into the submodule B.
var FiniteSpanCommonDenominator = finiteSpanCommonDenominatorThm{family.Add(registry.ProofEntry{
	Name: "FiniteSpanCommonDenominator",
	Key:  "prop_5a1603f67e753034",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S B G D:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subring(field_ring(L), B)",
			"fraction_field_carrier(field_ring(L), B)",
			"submodule(«scalars», «ambient», B)",
			"finite(G)",
			"G ⊆ L.carrier",
			"D ⊆ module_span(«scalars», «ambient», G)",
		},
		Conclusion: "∃r:A. r ∈ B ∧ r ≠ L.zero ∧ image(L.mul(r), D) ⊆ B",
		Abbrev: Abbrev{
			{Name: "ambient", Text: "regular_module(field_ring(L))"},
			{Name: "scalars", Text: "restrict_ring(field_ring(L), S)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, B, G, D *Expr[Set[A]],
		subS, subringB, fractionB, latticeB, finiteG, gInL, dInSpan Fact,
	) {
		r, cleared := a.ObtainAs[A](
			"clear the denominators of the finite generators",
			"∃r:A. r ∈ B ∧ r ≠ L.zero ∧ image(L.mul(r), G) ⊆ B",
			By(subringB, fractionB, finiteG, gInL, FiniteCommonDenominator.Read(L).At(B, G)),
			Named("r"))
		rInL := a.Have(
			"the denominator lies in L",
			"r ∈ L.carrier",
			BySets(cleared, comm_ring.SubringSubset.Read(subringB)))
		scale := a.Have(
			"multiplication by r is S-linear",
			"module_homomorphism(«scalars», «ambient», «ambient», L.mul(r))",
			By(subS, rInL, field_extension.ScaleLinear.Read(L).AsFact().At(S, r)))
		spanned := a.Have(
			"it carries the generators into the submodule B, so their whole span",
			"image(L.mul(r), module_span(«scalars», «ambient», G)) ⊆ B",
			By(gInL, latticeB, cleared, linear_independence.HomSpanInSubmodule.Read(scale).At(G, B)))
		a.Take(r)
		a.Show(
			"r is the common denominator of D, which lies in that span",
			BySets(cleared, dInSpan, spanned))
	}),
})}

// IndependentOverFractionField — a set independent over a subring S of a
// field stays independent over the fraction field K of S: a common
// denominator of the finitely many coefficients of a K-relation turns it
// into an S-relation, whose coefficients vanish, and the nonzero
// denominator cancels.
var IndependentOverFractionField = independentOverFractionFieldThm{family.Add(registry.ProofEntry{
	Name: "IndependentOverFractionField",
	Key:  "prop_b5cfb95f05ad192e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S K E:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, K)",
			"fraction_field_carrier(«scalars», S)",
			"module_independent(«subringScalars», «ambient», E)",
		},
		Conclusion: "module_independent(«scalars», «ambient», E)",
		Abbrev: Abbrev{
			{Name: "ambient", Text: "regular_module(field_ring(L))"},
			{Name: "subringScalars", Text: "restrict_ring(field_ring(L), S)"},
			{Name: "scalars", Text: "restrict_ring(field_ring(L), K)"},
		},
	}, func(arg *Argument, L field.FieldFact[on.L], S, K, E *Expr[Set[A]], h Fact) {
		given := arg.Conjuncts(
			h,
			"S is a subring of L",
			"K is a subfield of L",
			"K is the fraction field of S",
			"E is independent over S")
		independent := given[3]
		subringScalars := arg.TermAs[RingOps[A]]("«subringScalars»")
		ambient := arg.TermAs[module_record.ModuleOps[A, A]]("«ambient»")
		fieldData := arg.Have(
			"K lies in L and inherits a field structure",
			"K ⊆ L.carrier ∧ field_on(restrict_field(L, K))",
			By(given[1], field.SubfieldFieldOn.Read(L).At(K)))
		fields := arg.Conjuncts(
			fieldData,
			"K lies in L",
			"the restricted operations form a field")
		fractions := arg.Have(
			"K, as a field of its own, is the fraction field of S",
			"fraction_field_carrier(field_ring(restrict_field(L, K)), S)",
			Simp(Rev(field.RestrictFieldRing)),
			By(given[2]))
		sInK := arg.Have(
			"as the fraction field of S, K contains S",
			"S ⊆ K",
			By(
				given[2],
				field.FractionFieldCarrierDef.At(arg.TermAs[RingOps[A]]("«scalars»"), S),
				module_record.RestrictRingDef.At(arg.TermAs[RingOps[A]]("field_ring(L)"), K)))
		subringLaws := arg.Unfolded(given[0], comm_ring.SubringDef)
		subringInK := arg.Have(
			"S is also a subring of the field K",
			"subring(field_ring(restrict_field(L, K)), S)",
			Simp(Rev(field.RestrictFieldRing)),
			Simp(Fwd(comm_ring.SubringDef)),
			By(subringLaws, sInK))
		arg.Show(
			"every relation over K has all coefficients zero",
			Simp(Fwd(linear_independence.ModuleIndependentDef)),
			SplitConj(
				Case(
					"E lies in L",
					By(independent, linear_independence.ModuleIndependentDef.At(subringScalars, ambient, E))),
				Case(
					"clear the finitely many coefficients of a relation over K",
					Derive(func(b *Argument) {
						T := b.FixAs[Set[A]]("T")
						c := b.FixAs[Fun[A, A]]("c")
						combination := b.Assume()
						coefficientImage := b.Have(
							"the coefficient image is a finite subset of K",
							"finite(image(c, T)) ∧ image(c, T) ⊆ K",
							By(combination, finite_set.FiniteImage.At(c, T), set_image.ImageSubsetIff.At(c, T, K)))
						d, denominator := b.ObtainAs[A](
							"choose one nonzero denominator in S for the coefficient image",
							"∃d:A. d ∈ S ∧ d ≠ L.zero ∧ image(L.mul(d), image(c, T)) ⊆ S",
							By(
								fractions,
								subringInK,
								coefficientImage,
								FiniteCommonDenominator.Read(fields[1]).At(S, b.TermAs[Set[A]]("image(c, T)"))))
						clearedCoefficients := b.Have(
							"multiplication by d puts every coefficient in S",
							"∀x:A. x ∈ T ⇒ d * c(x) ∈ S",
							BySets(denominator))
						subringInField := b.Have(
							"S lies in L",
							"S ⊆ L.carrier",
							By(subringLaws))
						inField := b.Have(
							"the denominator, support, and coefficients lie in L",
							"d ∈ L.carrier ∧ (∀x:A. x ∈ T ⇒ x ∈ L.carrier ∧ c(x) ∈ L.carrier)",
							BySets(
								linear_independence.IndependentInCarrier.Read(independent),
								denominator,
								subringInField,
								fields[0],
								combination))
						members := b.Conjuncts(
							inField,
							"the denominator lies in L",
							"each support element and its coefficient lie in L")
						vanishes := b.Conjuncts(
							combination,
							"the support is finite",
							"the support lies in E",
							"the coefficients lie in K",
							"the original combination vanishes")[3]
						regrouped := b.Have(
							"regroup each summand using its cleared coefficient",
							"∀x:A. x ∈ T ⇒ d * c(x) * x = d * (c(x) * x)",
							Derive(func(e *Argument) {
								x := e.FixAs[A]("x")
								xIn := e.Assume()
								e.Show(
									"associate the scalar product",
									ByArith(L, members[0], xIn, members[1].At(x)))
							}))
						clearedSum := b.Have(
							"the cleared combination over S still vanishes",
							"module_sum(L.add, L.zero, T, λx:A. (d * c(x)) * x) = L.zero",
							CalcEq(
								Leg(
									b.TermAs[A]("module_sum(L.add, L.zero, T, λx:A. d * (c(x) * x))"),
									"the regrouped summands have the same sum",
									By(
										regrouped,
										module.ModuleSumCongruence.At(b.TermAs[Op[A]]("L.add"), b.TermAs[A]("L.zero"), T,
											b.TermAs[Fun[A, A]]("λx:A. (d * c(x)) * x"), b.TermAs[Fun[A, A]]("λx:A. d * (c(x) * x)")))),
								Leg(
									b.TermAs[A]("d * module_sum(L.add, L.zero, T, λx:A. c(x) * x)"),
									"the common denominator comes out of the finite sum",
									By(
										comm_ring.MulIn.Read(field.RingOn.Read(L)),
										inField,
										combination,
										module.ModuleSumSmul.Read(module.RegularModuleOn.Read(field.RingOn.Read(L))).AsFact().At(T, d,
											b.TermAs[Fun[A, A]]("λx:A. c(x) * x")))),
								Leg(
									b.TermAs[A]("d * L.zero"),
									"substitute the vanishing original combination",
									vanishes.Rw(),
									Basic()),
								FinalLeg(
									"d times zero is zero",
									ByArith(L, members[0]))))
						x := b.FixAs[A]("x")
						xIn := b.Assume()
						clearedZero := b.Have(
							"independence over S kills the cleared coefficient",
							"d * c(x) = L.zero",
							By(
								combination,
								clearedCoefficients,
								clearedSum,
								xIn,
								linear_independence.IndependentVanishingCombination.Read(independent).At(T,
									b.TermAs[Fun[A, A]]("λx:A. d * c(x)"), x)))
						b.Show(
							"cancel the nonzero denominator to recover a zero coefficient",
							By(
								clearedZero,
								denominator,
								members[0],
								xIn,
								members[1].At(x),
								field.MulEqZeroOn.Read(L).AsFact().At(d, b.TermAs[A]("c(x)"))))
					}))))
	}),
})}
