// conjugate_automorphism.go — an embedding of a simple extension sending
// a to a conjugate extends across a finite basis of a normal extension;
// the proof reduces to the field M itself because the embeddings must land
// in M, where normality splits. Finite dimension makes the resulting
// embedding onto, and its permutation represents the automorphism.

package galois_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ConjugateAutomorphism — in a finite normal extension, a member and
// each of its conjugates are joined by an automorphism fixing K.
var ConjugateAutomorphism = conjugateAutomorphismThm{family.Add(registry.ProofEntry{
	Name: "ConjugateAutomorphism",
	Key:  "prop_25ea3dd65e939ca2",
	Reading: "Separability is not asked: the extension of " +
		"the isomorphism K(a) → K(b) to M uses normality alone.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀K M:set(A). ∀a b:A.",
		Hypotheses: []string{
			"subfield(L, K)",
			"subfield(L, M)",
			"K ⊆ M",
			"finite_extension(L, K, M)",
			"normal_over(L, K, M)",
			"a ∈ M",
			"b ∈ M",
			"polynomial_eval(minimal_polynomial(L, K, a), b) = L.zero",
		},
		Conclusion: "∃p:permutation(A). p ∈ field_automorphisms(L, K, M) ∧ permutation_map(p, a) = b",
	}, func(ctx *Script, headline string) *GoalStackNode {
		transportedRoot := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K E:set(A). ∀f:(A → A). ∀a:A.",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, E)",
				"K ⊆ E",
				"ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), f)",
				"∀x:A. x ∈ K ⇒ f(x) = x",
				"a ∈ L.carrier",
				"algebraic_over(L, K, a)",
				"normal_over(L, K, L.carrier)",
			},
			Conclusion: "∃b:A. " +
				"    b ∈ L.carrier ∧ polynomial_eval(λi:num. f(minimal_polynomial(L, E, a, i)), b) = L.zero",
		}, func(
			arg *Argument,
			L field.FieldFact[on.L],
			K, E *Expr[Set[A]],
			f *Arrow[A, A],
			a *Member[A, on.L],
			kField, eField, nested, hom, fixesK, algebraic, normal Fact,
		) {
			l, carrier := arg.TermAs[FieldOps[A]]("L"), arg.TermAs[Set[A]]("L.carrier")
			p, pDef := arg.LetAs[Fun[Nat, A]]("p", "minimal_polynomial(L, K, a)")
			_, qDef := arg.LetAs[Fun[Nat, A]]("q", "minimal_polynomial(L, E, a)")
			Q, qImageDef := arg.LetAs[Fun[Nat, A]]("Q", "λi:num. f(q(i))")
			algebraicE := arg.Have(
				"a remains algebraic over the intermediate field",
				"algebraic_over(L, E, a)",
				By(nested, algebraic, algebraic_element.AlgebraicOverMono.Read(L).At(K, E, a)))
			basePolynomial := arg.Have(
				"p is a polynomial over K vanishing at a",
				"polynomial_over(K, p) ∧ polynomial_eval(p, a) = L.zero",
				By(pDef, a, kField, algebraic, algebraic_element.MinimalPolynomialSpec.Read(L).At(K, a)))
			transported := arg.Have(
				"Q is a polynomial over L of the degree of q that divides p",
				"polynomial_over(L.carrier, Q) ∧ "+
					"polynomial_degree(Q) = polynomial_degree(q) ∧ "+
					"polynomial_divides(field_ring(L), Q, p)",
				By(
					qImageDef,
					qDef,
					eField,
					nested,
					hom,
					fixesK,
					algebraicE,
					basePolynomial,
					algebraic_element.TransportedMinimalPolynomial.Read(L).At(K, E, f, a, p)))
			baseSplits := arg.Have(
				"normality splits the base minimal polynomial",
				"polynomial_splits(field_ring(L), p)",
				By(
					Normalized,
					pDef,
					kField,
					normal,
					a,
					algebraic,
					basePolynomial,
					algebraic_element.MinimalPolynomialIrreducible.Read(L).At(K, a),
					NormalOverDef.At(l, K, carrier),
					module_record.RestrictRingCarrier.At(arg.TermAs[comm_ring.RingOps[A]]("field_ring(L)")),
					field.FieldRingDef.At(l)))
			imageSplits := arg.Have(
				"a divisor of the split polynomial p also splits",
				"polynomial_splits(field_ring(L), Q)",
				By(baseSplits, transported, separable_polynomial.SplitsDivisor.Read(field.RingOn.Read(L)).At(Q, p)))
			positiveDegree := arg.Have(
				"the transported minimal polynomial has positive degree",
				"0 < polynomial_degree(Q)",
				By(
					Normalized,
					qDef,
					transported,
					a,
					eField,
					algebraicE,
					algebraic_element.MinimalPolynomialPositive.Read(L).At(E, a)))
			arg.Show(
				"the split polynomial Q has a root in L",
				By(transported, positiveDegree, imageSplits, separable_polynomial.SplitsRoot.Read(L).At(Q)))
		})

		extendAcrossGenerators := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K E S:set(A). ∀f:(A → A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, E)",
				"K ⊆ E",
				"ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), f)",
				"∀x:A. x ∈ K ⇒ f(x) = x",
				"finite(S)",
				"S ⊆ L.carrier",
				"∀x:A. x ∈ S ⇒ algebraic_over(L, K, x)",
				"normal_over(L, K, L.carrier)",
			},
			Conclusion: "∃D:set(A). ∃g:(A → A). " +
				"    subfield(L, D) ∧ " +
				"    E ⊆ D ∧ " +
				"    S ⊆ D ∧ " +
				"    ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g) ∧ " +
				"    (∀x:A. x ∈ E ⇒ g(x) = f(x))",
		}, func(
			arg *Argument,
			L field.FieldFact[on.L],
			K, E, S *Expr[Set[A]],
			f *Arrow[A, A],
			kField, eField, nested, hom, fixesK, finiteS, inside, algebraic, normal Fact,
		) {
			l := arg.TermAs[FieldOps[A]]("L")
			arg.Show(
				"extend over the finite set of algebraic generators",
				ByInduction(finite_set.FiniteInduct, finiteS, Generalizing(inside, algebraic), Case(
					"the original embedding suffices when no generator is adjoined",
					Derive(func(a *Argument) {
						a.Assume()
						a.Take(E)
						a.Take(f)
						a.Show(
							"E and f meet every condition at once",
							BySets(eField, hom))
					})),
					Case(
						"extend the embedding that covers the smaller set across one more algebraic element",
						Derive(func(a *Argument) {
							x := a.FixAs[A]("x")
							a.FixAs[Set[A]]("s")
							inductive, enlarged := a.Assume(), a.Assume()
							conditions := a.Have(
								"the smaller set and the inserted point retain the algebraicity conditions",
								"s ⊆ L.carrier ∧ x ∈ L.carrier ∧ algebraic_over(L, K, x) ∧ (∀y:A. y ∈ s ⇒ algebraic_over(L, K, y))",
								BySets(enlarged))
							D, g, extension := a.Obtain2As[Set[A], Fun[A, A]](
								"choose an embedding of a field containing the smaller set",
								"∃D:set(A). ∃g:(A → A). "+
									"    subfield(L, D) ∧ "+
									"    E ⊆ D ∧ "+
									"    s ⊆ D ∧ "+
									"    ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g) ∧ "+
									"    (∀y:A. y ∈ E ⇒ g(y) = f(y))",
								By(conditions, inductive))
							parts := a.Conjuncts(
								extension,
								"D is a subfield",
								"D contains E",
								"D contains the smaller set",
								"g embeds D",
								"g agrees with f on E")
							fixesBase := a.Have(
								"the embedding of D fixes K",
								"K ⊆ D ∧ (∀y:A. y ∈ K ⇒ g(y) = y)",
								BySets(nested, parts[1], parts[4], fixesK))
							b, root := a.ObtainAs[A](
								"choose a root b of the transported minimal polynomial of x over D",
								"∃b:A. b ∈ L.carrier ∧ polynomial_eval(λi:num. g(minimal_polynomial(L, D, x, i)), b) = L.zero",
								By(
									L,
									kField,
									parts[0],
									fixesBase,
									parts[3],
									conditions,
									normal,
									At(transportedRoot, l, K, D, g, x)))
							algebraicD := a.Have(
								"the new point is algebraic over D",
								"algebraic_over(L, D, x)",
								By(fixesBase, conditions, algebraic_element.AlgebraicOverMono.Read(L).At(K, D, x)))
							conditionParts := a.Conjuncts(
								conditions,
								"the smaller set lies in L",
								"the inserted point lies in L",
								"the inserted point is algebraic",
								"the smaller set is algebraic")
							xm := a.MemberOf[on.L](x, conditionParts[1])
							h, extended := a.ObtainAs[Fun[A, A]](
								"extend g to an embedding h of D(x) sending x to b",
								"∃h:(A → A). "+
									"    ring_homomorphism(restrict_ring(field_ring(L), field_adjoin(L, D, {x})), "+
									"        field_ring(L), "+
									"        h) ∧ "+
									"    (∀y:A. y ∈ D ⇒ h(y) = g(y)) ∧ "+
									"    h(x) = b",
								By(
									L,
									parts[0],
									parts[3],
									algebraicD,
									root,
									algebraic_element.AdjoinEmbeddingAtRoot.Read(L).At(l, D, g, xm, b)))
							J, jDef := a.LetAs[Set[A]]("J", "field_adjoin(L, D, {x})")
							enlargedField := a.Have(
								"the new adjunction contains D and the inserted point",
								"subfield(L, J) ∧ D ⊆ J ∧ x ∈ J",
								By(
									Normalized,
									jDef,
									parts[0],
									conditions,
									algebraic_element.AdjoinElementSubfield.Read(L).At(D, xm)))
							a.Take(J)
							a.Take(h)
							a.Show(
								"the new embedding contains all generators and agrees with f on E",
								BySets(enlargedField, parts[1], parts[2], parts[4], extended))
						}))))
		})

		basisGenerates := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K D S:set(A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, D)",
				"K ⊆ D",
				"module_basis(restrict_ring(field_ring(L), K), " +
					"    restrict_module(regular_module(field_ring(L)), L.carrier), " +
					"    S)",
				"S ⊆ D",
			},
			Conclusion: "D = L.carrier",
		}, func(
			arg *Argument,
			L field.FieldFact[on.L],
			K, D, S *Expr[Set[A]],
			kField, dField, nested, basis, generators Fact,
		) {
			R, rDef := arg.LetAs[comm_ring.RingOps[A]]("R", "restrict_ring(field_ring(L), K)")
			V, vDef := arg.LetAs[module_record.ModuleOps[A, A]](
				"V", "restrict_module(regular_module(field_ring(L)), L.carrier)")
			sameCarrier := arg.Have(
				"the restriction keeps the ambient carrier",
				"V.carrier = L.carrier",
				Simp(Fwd(vDef), Fwd(module_record.RestrictModuleDef)),
				Basic())
			closed := arg.Have(
				"D is a K-submodule of the ambient field",
				"submodule(R, V, D)",
				By(
					Normalized,
					rDef,
					vDef,
					kField,
					dField,
					nested,
					field.SubfieldSubset.Read(dField),
					field_extension.SubfieldSubmodule.Read(L).At(K, D, arg.TermAs[Set[A]]("L.carrier"))))
			span := arg.Have(
				"the basis spans the ambient carrier",
				"module_span(R, V, S) = L.carrier",
				By(Normalized, basis, sameCarrier, linear_independence.ModuleBasisDef.At(R, V, S)))
			spanInside := arg.Have(
				"leastness puts the span inside D",
				"module_span(R, V, S) ⊆ D",
				By(closed, generators, submodule.SpanLeast.At(R, V, S, D)))
			arg.Show(
				"D contains the ambient carrier and is contained in it",
				BySets(span, spanInside, field.SubfieldSubset.Read(dField)))
		})

		extendEmbedding := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K E:set(A). ∀f:(A → A).",
			Hypotheses: []string{
				"subfield(L, K)",
				"subfield(L, E)",
				"K ⊆ E",
				"finite_extension(L, K, L.carrier)",
				"normal_over(L, K, L.carrier)",
				"ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), f)",
				"∀x:A. x ∈ K ⇒ f(x) = x",
			},
			Conclusion: "∃g:(A → A). " +
				"    ring_homomorphism(restrict_ring(field_ring(L), L.carrier), field_ring(L), g) ∧ " +
				"    (∀x:A. x ∈ E ⇒ g(x) = f(x))",
		}, func(
			arg *Argument,
			L field.FieldFact[on.L],
			K, E *Expr[Set[A]],
			f *Arrow[A, A],
			kField, eField, nested, finite, normal, hom, fixesK Fact,
		) {
			l, carrier := arg.TermAs[FieldOps[A]]("L"), arg.TermAs[Set[A]]("L.carrier")
			R := arg.TermAs[comm_ring.RingOps[A]]("restrict_ring(field_ring(L), K)")
			V := arg.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(L)), L.carrier)")
			carrierField := arg.Have(
				"the ambient carrier is a subfield containing K",
				"subfield(L, L.carrier) ∧ K ⊆ L.carrier",
				By(field.CarrierSubfield.Read(L), field.SubfieldSubset.Read(kField)))
			S, finiteBasis := arg.ObtainAs[Set[A]](
				"L has a finite basis S over K",
				"∃S:set(A). "+
					"    finite(S) ∧ "+
					"    module_basis(restrict_ring(field_ring(L), K), "+
					"        restrict_module(regular_module(field_ring(L)), L.carrier), "+
					"        S)",
				By(finite, field_extension.FiniteExtensionDef, module_dimension.FiniteDimensionalDef))
			inside := arg.Have(
				"basis vectors lie in L",
				"S ⊆ L.carrier",
				By(
					finiteBasis,
					linear_independence.ModuleBasisDef.At(R, V, S),
					linear_independence.IndependentInCarrier.At(R, V, S),
					module_record.RestrictModuleDef.At(
						arg.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"), carrier)))
			algebraic := arg.Have(
				"every basis vector is algebraic over K",
				"∀x:A. x ∈ S ⇒ algebraic_over(L, K, x)",
				Derive(func(a *Argument) {
					x := a.FixAs[A]("x")
					member := a.Assume()
					inL := a.Have(
						"the vector belongs to the ambient field",
						"x ∈ L.carrier",
						By(member, inside, set_basic.SubsetDef.At(S, carrier)))
					xm := a.MemberOf[on.L](x, inL)
					a.Show(
						"finite extensions have algebraic elements",
						By(
							kField,
							carrierField,
							finite,
							inL,
							algebraic_element.FiniteExtensionAlgebraic.Read(L).At(K, carrier, xm)))
				}))
			D, g, extension := arg.Obtain2As[Set[A], Fun[A, A]](
				"extend f to an embedding g of a subfield D containing E and the basis",
				"∃D:set(A). ∃g:(A → A). "+
					"    subfield(L, D) ∧ "+
					"    E ⊆ D ∧ "+
					"    S ⊆ D ∧ "+
					"    ring_homomorphism(restrict_ring(field_ring(L), D), field_ring(L), g) ∧ "+
					"    (∀x:A. x ∈ E ⇒ g(x) = f(x))",
				By(
					L,
					kField,
					eField,
					nested,
					hom,
					fixesK,
					finiteBasis,
					inside,
					algebraic,
					normal,
					At(extendAcrossGenerators, l, K, E, S, f)))
			whole := arg.Have(
				"a subfield containing the basis is the whole field",
				"D = L.carrier",
				By(
					L,
					kField,
					nested,
					extension,
					finiteBasis,
					set_order.SubsetTrans.At(K, E, D),
					At(basisGenerates, l, K, D, S)))
			arg.Take(g)
			arg.Show(
				"the resulting embedding is defined on all of L",
				By(Normalized, whole, extension))
		})

		automorphismOfWholeField := ctx.Lemma(Statement{
			Binders: "∀L:field_on(A). ∀K:set(A). ∀a b:A.",
			Hypotheses: []string{
				"subfield(L, K)",
				"finite_extension(L, K, L.carrier)",
				"normal_over(L, K, L.carrier)",
				"a ∈ L.carrier",
				"b ∈ L.carrier",
				"polynomial_eval(minimal_polynomial(L, K, a), b) = L.zero",
			},
			Conclusion: "∃p:permutation(A). " +
				"    p ∈ field_automorphisms(L, K, L.carrier) ∧ permutation_map(p, a) = b",
		}, func(
			arg *Argument,
			L field.FieldFact[on.L],
			K *Expr[Set[A]],
			a, b *Member[A, on.L],
			kField, finite, normal, root Fact,
		) {
			l, carrier := arg.TermAs[FieldOps[A]]("L"), arg.TermAs[Set[A]]("L.carrier")
			E, eDef := arg.LetAs[Set[A]]("E", "field_adjoin(L, K, {a})")
			simpleField := arg.Have(
				"the simple extension contains K and a",
				"subfield(L, E) ∧ K ⊆ E ∧ a ∈ E",
				By(Normalized, eDef, kField, a, algebraic_element.AdjoinElementSubfield.Read(L).At(K, a)))
			rings := arg.Have(
				"the base and ambient field define commutative rings",
				"comm_ring_on(restrict_ring(field_ring(L), K)) ∧ comm_ring_on(field_ring(L)) ∧ K ⊆ L.carrier",
				By(
					field.RingOn.Read(L),
					kField,
					field.SubfieldSubset.Read(kField),
					field.SubfieldCommRing.Read(L).At(K)))
			identity := arg.TermAs[Fun[A, A]]("λx:A. x")
			inclusion := arg.Have(
				"the inclusion of K is a ring homomorphism",
				"ring_homomorphism(restrict_ring(field_ring(L), K), field_ring(L), λx:A. x)",
				By(
					kField,
					field.SubfieldSubring.Read(L).At(K),
					ring_homomorphism.SubringInclusionHom.Read(field.RingOn.Read(L)).At(K)))
			algebraic := arg.Have(
				"a is algebraic over K",
				"algebraic_over(L, K, a)",
				By(
					field.CarrierSubfield.Read(L),
					kField,
					rings,
					a,
					finite,
					algebraic_element.FiniteExtensionAlgebraic.Read(L).At(K, carrier, a)))
			f, simpleEmbedding := arg.ObtainAs[Fun[A, A]](
				"send a to b by an embedding f of E fixing K",
				"∃f:(A → A). "+
					"    ring_homomorphism(restrict_ring(field_ring(L), E), field_ring(L), f) ∧ "+
					"    (∀x:A. x ∈ K ⇒ f(x) = x) ∧ "+
					"    f(a) = b",
				By(
					L,
					eDef,
					kField,
					inclusion,
					b,
					algebraic,
					root,
					algebraic_element.AdjoinEmbeddingAtRoot.Read(L).At(l, K, identity, a, b)))
			g, extension := arg.ObtainAs[Fun[A, A]](
				"extend f to an embedding g of all of L",
				"∃g:(A → A). "+
					"    ring_homomorphism(restrict_ring(field_ring(L), L.carrier), field_ring(L), g) ∧ "+
					"    (∀x:A. x ∈ E ⇒ g(x) = f(x))",
				By(L, kField, simpleField, finite, normal, simpleEmbedding, At(extendEmbedding, l, K, E, f)))
			parts := arg.Conjuncts(
				extension,
				"g is an embedding of L",
				"g agrees with f on E")
			fixes := arg.Have(
				"g fixes K and carries a to b",
				"(∀x:A. x ∈ K ⇒ g(x) = x) ∧ g(a) = b",
				BySets(simpleField, simpleEmbedding, parts[1]))
			into := arg.Have(
				"g maps L into itself",
				"image(g, L.carrier) ⊆ L.carrier",
				BySets(ring_homomorphism.MapIn.Read(parts[0])))
			onto := arg.Have(
				"a finite extension embedding fixing its base is onto",
				"image(g, L.carrier) = L.carrier",
				By(
					field.CarrierSubfield.Read(L),
					kField,
					rings,
					finite,
					fixes,
					parts[0],
					into,
					field_extension.FiniteEmbeddingOnto.Read(L).At(K, carrier, g)))
			p, permutation := arg.ObtainAs[Permutation[A]](
				"represent g by an automorphism p of L over K",
				"∃p:permutation(A). "+
					"    p ∈ field_automorphisms(L, K, L.carrier) ∧ "+
					"    (∀x:A. x ∈ L.carrier ⇒ permutation_map(p, x) = g(x))",
				By(
					field.CarrierSubfield.Read(L),
					fixes,
					parts[0],
					onto,
					field_automorphism.EmbeddingPermutation.Read(L).At(K, carrier, g)))
			arg.Take(p)
			arg.Show(
				"the automorphism carries a to its conjugate b",
				By(Normalized, permutation, fixes, a))
		})

		return ctx.Theorem(headline, func(
			arg *Argument,
			L field.FieldFact[on.L],
			K, M *Expr[Set[A]],
			a, b *Member[A, on.M],
			subK, subM, nested, finite, normal, root Fact,
		) {
			F, fDef := arg.LetAs[FieldOps[A]]("F", "restrict_field(L, M)")
			fieldF := arg.Have(
				"restriction to M gives a field with carrier M",
				"field_on(F)",
				By(Normalized, fDef, subM, field.SubfieldFieldOn.Read(L).At(M)))
			baseF := arg.Have(
				"K is a subfield of the restricted field",
				"subfield(F, K)",
				By(Normalized, fDef, subK, nested, field.SubfieldRestrict.At(arg.TermAs[FieldOps[A]]("L"), M, K)))
			normalF := arg.Have(
				"normality uses the same coefficients and roots after restriction",
				"normal_over(F, K, F.carrier) ⇔ normal_over(L, K, M)",
				Simp(
					Fwd(fDef),
					Fwd(NormalOverDef),
					Fwd(field.RestrictFieldDef),
					Fwd(field.FieldRingDef),
					Fwd(module_record.RestrictRingDef)),
				Basic())
			minimalF := arg.Have(
				"the minimal polynomial uses the unchanged field operations",
				"minimal_polynomial(F, K, a) = minimal_polynomial(L, K, a)",
				Simp(Fwd(fDef), Fwd(algebraic_element.MinimalPolynomialDef), Fwd(field.RestrictFieldDef)),
				Basic())
			automorphismsF := arg.Have(
				"the automorphism sets use the same carrier and operations",
				"field_automorphisms(F, K, F.carrier) = field_automorphisms(L, K, M)",
				Simp(Fwd(fDef), Fwd(field_automorphism.FieldAutomorphismsDef), Fwd(field.RestrictFieldDef)),
				Basic())
			finiteF := arg.Have(
				"the restricted field has the same finite extension module",
				"finite_extension(F, K, F.carrier) ⇔ finite_extension(L, K, M)",
				Simp(
					Fwd(fDef),
					Fwd(field_extension.FiniteExtensionDef),
					Fwd(field.RestrictFieldDef),
					Fwd(field.FieldRingDef),
					Fwd(module_record.RestrictRingDef),
					Fwd(module_record.RegularModuleDef),
					Fwd(module_record.RestrictModuleDef)),
				Basic())
			normalExtension := arg.Have(
				"F is a finite normal extension of K",
				"finite_extension(F, K, F.carrier) ∧ normal_over(F, K, F.carrier)",
				By(finiteF, normalF, finite, normal))
			conjugate := arg.Have(
				"a and b are members of F and b remains a conjugate of a",
				"a ∈ F.carrier ∧ "+
					"b ∈ F.carrier ∧ "+
					"polynomial_eval(F.add, F.zero, F.mul, F.one, minimal_polynomial(F, K, a), b) = F.zero",
				Simp(Fwd(minimalF)),
				Simp(Fwd(fDef), Fwd(field.RestrictFieldDef)),
				By(a, b, root))
			arg.Show(
				"the automorphism of the restricted field is the required automorphism",
				Simp(Rev(automorphismsF)),
				By(fieldF, baseF, normalExtension, conjugate, At(automorphismOfWholeField, F, K, a, b)))
		})
	}),
})}
