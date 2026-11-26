package constant_twist

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// _constantComposite is constant_galois.ConstantCompositeData read apart: k and L are subfields
// with k in L, and the constants of L are k; l, the field of q^e constants, is a
// subfield holding k and finite over it; and N = L·l is a subfield holding L and
// l.
type _constantComposite struct {
	subK, subL, kInL, exact, subC, kInC, finiteC, subN, LInN, cInN Fact
}

// readConstantComposite reads constant_galois.ConstantCompositeData apart at L, k and the
// exponent e of l, the premises discharging its hypotheses.
func readConstantComposite(
	a *Argument,
	M field.FieldFact[on.M],
	L, k *Expr[Set[A]],
	e *Expr[Nat],
	premises ...Fact,
) _constantComposite {
	listed := make([]any, 0, len(premises)+1)
	for _, f := range premises {
		listed = append(listed, f)
	}
	parts := a.Conjuncts(
		GroupPremises(append(listed, constant_galois.ConstantCompositeData.Read(M).At(L, k, e))...),
		"k is a subfield",
		"L is a subfield",
		"k lies in L",
		"the constants of L are k",
		"l is a subfield",
		"k lies in l",
		"l is finite",
		"l is finite over k",
		"N is a subfield",
		"L lies in N",
		"l lies in N")
	return _constantComposite{
		parts[0],
		parts[1],
		parts[2],
		parts[3],
		parts[4],
		parts[5],
		parts[7],
		parts[8],
		parts[9],
		parts[10],
	}
}

// ConstantAutomorphismExtends — an automorphism of the constants extends over
// L. N = L·l is Galois over L of degree [l : k], so Aut(N/L) has [l : k]
// members. Each carries l into itself, as l is the set of roots of a
// polynomial over L, and restricts to an automorphism of l over k. Restriction
// is injective (field_automorphism.AutomorphismsAgreeOnGenerators), into a group of at most
// [l : k] members, so onto.
var ConstantAutomorphismExtends = constantAutomorphismExtendsThm{family.Add(registry.ProofEntry{
	Name: "ConstantAutomorphismExtends",
	Key:  "prop_ed311d5326c22fe6",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), e)"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
		},
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀e:num. ∀r:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"0 < e",
			"r ∈ field_automorphisms(M, k, «constants»)",
		},
		Conclusion: "∃u:permutation(A). " +
			"    u ∈ field_automorphisms(M, L, «composite») ∧ " +
			"    (∀c:A. c ∈ «constants» ⇒ permutation_map(u, c) = permutation_map(r, c))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			e *Expr[Nat],
			r *Expr[Permutation[A]],
			closed, regular, finiteK, positive, rIn Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			constants := a.TermAs[Set[A]]("«constants»")
			composite := a.TermAs[Set[A]]("«composite»")
			upstairs := a.TermAs[Set[Permutation[A]]]("field_automorphisms(M, L, «composite»)")
			downstairs := a.TermAs[Set[Permutation[A]]]("field_automorphisms(M, k, «constants»)")
			nothing := a.TermAs[Set[A]]("∅")
			q := a.TermAs[Nat]("card(k)")
			xPowerMinusX := a.TermAs[Fun[Nat, A]]("vec_sub(basis_vector(card(k) ^ e), basis_vector(1))")
			data := readConstantComposite(a, M, L, k, e, regular, finiteK, positive)
			perfect := a.Have(
				"k is perfect",
				"perfect_field(restrict_field(M, k))",
				By(a.Unfolded(regular, function_field.RegularFunctionFieldDef)))
			degree := a.Have(
				"N has degree [l : k] over L",
				"finite_extension(M, L, «composite») ∧ "+
					"extension_degree(M, L, «composite») = extension_degree(M, k, «constants»)",
				Simp(Fwd(constant_composite.ConstantCompositeDef)),
				By(
					data.subK,
					data.subL,
					data.subC,
					data.kInL,
					data.kInC,
					data.finiteC,
					perfect,
					data.exact,
					constant_composite.ConstantExtensionDegree.Read(M).At(k, L, constants)))
			galois := a.Have(
				"N is Galois over L",
				"galois_over(M, L, «composite»)",
				By(closed, regular, finiteK, positive, constant_galois.ConstantCompositeGalois.Read(M).At(L, k, e)))
			count := a.Have(
				"so Aut(N/L) is finite with [l : k] members",
				"finite(field_automorphisms(M, L, «composite»)) ∧ "+
					"card(field_automorphisms(M, L, «composite»)) = extension_degree(M, k, «constants»)",
				By(
					data.subL,
					data.subN,
					data.LInN,
					degree,
					galois,
					field_automorphism.AutomorphismsBound.Read(M).At(L, composite),
					galois_correspondence.GaloisIffCard.Read(M).At(L, composite)))
			bound := a.Have(
				"Aut(l/k) is finite with at most [l : k] members",
				"finite(field_automorphisms(M, k, «constants»)) ∧ "+
					"card(field_automorphisms(M, k, «constants»)) ≤ extension_degree(M, k, «constants»)",
				By(
					data.subK,
					data.subC,
					data.kInC,
					data.finiteC,
					field_automorphism.AutomorphismsBound.Read(M).At(k, constants)))
			NInCarrier := a.Have(
				"N lies in M",
				"«composite» ⊆ M.carrier",
				By(data.subN, field.SubfieldSubset.At(m, composite)))
			rootPolynomial := a.Conjuncts(
				GroupPremises(data.subL, finite_field.FiniteConstantsRootPolynomial.Read(M).At(L, q, e)),
				"X^Q − X has coefficients in L",
				"its roots in M are the constants")
			restrictions := a.Have(
				"an automorphism of N over L restricts to one of l over k",
				Statement{
					Binders:    "∀u:permutation(A).",
					Hypotheses: []string{"u ∈ field_automorphisms(M, L, «composite»)"},
					Conclusion: "∃v:permutation(A). " +
						"    v ∈ field_automorphisms(M, k, «constants») ∧ " +
						"    (∀c:A. c ∈ «constants» ⇒ permutation_map(v, c) = permutation_map(u, c))",
				},
				Derive(func(b *Argument) {
					u := b.FixAs[Permutation[A]]("u")
					member := b.Assume()
					laws := b.Have(
						"u permutes N, keeps sums and products and fixes L",
						"u ∈ symmetric_group(«composite») ∧ "+
							"(∀x y:A. "+
							"    x ∈ «composite» ∧ y ∈ «composite» ⇒ "+
							"    permutation_map(u, x + y) = permutation_map(u, x) + permutation_map(u, y)) ∧ "+
							"(∀x y:A. "+
							"    x ∈ «composite» ∧ y ∈ «composite» ⇒ "+
							"    permutation_map(u, x * y) = permutation_map(u, x) * permutation_map(u, y)) ∧ "+
							"(∀x:A. x ∈ L ⇒ permutation_map(u, x) = x)",
						BySets(b.Unfolded(member, field_automorphism.FieldAutomorphismsDef)))
					into := b.Have(
						"u carries a root of X^Q − X to a root",
						"∀c:A. c ∈ «constants» ⇒ permutation_map(u, c) ∈ «constants»",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							inConstants := c.Assume()
							inN := c.Have(
								"x and its image lie in N",
								"x ∈ «composite» ∧ permutation_map(u, x) ∈ «composite»",
								BySets(inConstants, data.cInN, laws, symmetric_group.SymmetricGroupMapsInto.At(composite, u, x)))
							image := c.TermAs[A]("permutation_map(u, x)")
							c.Show(
								"its image is a root in M",
								BySets(
									inN,
									NInCarrier,
									inConstants,
									data.subN,
									data.LInN,
									member,
									rootPolynomial[0],
									rootPolynomial[1].At(x),
									rootPolynomial[1].At(image),
									field_automorphism.AutomorphismPermutesRoots.Read(M).At(L, composite, xPowerMinusX, u, x)))
						}))
					unit := b.Have(
						"u keeps one",
						"permutation_map(u, M.one) = M.one",
						By(data.subN, member, field_automorphism.AutomorphismFixesUnits.Read(M).At(L, composite, u)))
					sums := b.Have(
						"u keeps sums on l",
						Statement{
							Binders: "∀x y:A.",
							Hypotheses: []string{
								"x ∈ «constants»",
								"y ∈ «constants»",
							},
							Conclusion: "permutation_map(u, x + y) = permutation_map(u, x) + permutation_map(u, y)",
						},
						BySets(laws, data.cInN))
					products := b.Have(
						"u keeps products on l",
						Statement{
							Binders: "∀x y:A.",
							Hypotheses: []string{
								"x ∈ «constants»",
								"y ∈ «constants»",
							},
							Conclusion: "permutation_map(u, x * y) = permutation_map(u, x) * permutation_map(u, y)",
						},
						BySets(laws, data.cInN))
					fixesK := b.Have(
						"u fixes k",
						"∀x:A. x ∈ k ⇒ permutation_map(u, x) = x",
						BySets(laws, data.kInL))
					b.Show(
						"so it is an automorphism of l over k",
						By(
							data.subK,
							data.subC,
							data.kInC,
							data.finiteC,
							sums,
							products,
							unit,
							fixesK,
							into,
							field_automorphism.FiniteSubfieldAutomorphism.Read(M).At(
								k, constants, b.TermAs[Fun[A, A]]("permutation_map(u)"))))
				}))
			g, chosen := a.ObtainAs[Fun[Permutation[A], Permutation[A]]](
				"choose a restriction of each",
				"∃g:(permutation(A) → permutation(A)). ∀u:permutation(A). "+
					"    u ∈ field_automorphisms(M, L, «composite») ⇒ "+
					"    g(u) ∈ field_automorphisms(M, k, «constants») ∧ "+
					"    (∀c:A. c ∈ «constants» ⇒ permutation_map(g(u), c) = permutation_map(u, c))",
				By(restrictions))
			widened := a.Have(
				"automorphisms over L are automorphisms over ∅ of the adjoined field",
				"field_automorphisms(M, L, «composite») ⊆ "+
					"field_automorphisms(M, ∅, field_adjoin(M, L, «constants»))",
				Simp(Fwd(constant_composite.ConstantCompositeDef)),
				By(
					set_order.EmptySubset,
					field_automorphism.AutomorphismsAntitone.Read(M).At(
						nothing, L, a.TermAs[Set[A]]("field_adjoin(M, L, «constants»)"))))
			fixesField := a.Have(
				"an automorphism over L fixes L",
				Statement{
					Binders: "∀u:permutation(A). ∀x:A.",
					Hypotheses: []string{
						"u ∈ field_automorphisms(M, L, «composite»)",
						"x ∈ L",
					},
					Conclusion: "permutation_map(u, x) = x",
				},
				Derive(func(b *Argument) {
					b.FixAs[Permutation[A]]("u")
					b.FixAs[A]("x")
					both := b.Assume()
					b.Show(
						"it is among the conditions",
						BySets(b.Unfolded(both, field_automorphism.FieldAutomorphismsDef)))
				}))
			injective := a.Have(
				"two automorphisms over L with one restriction are equal",
				"injective_on(field_automorphisms(M, L, «composite»), g)",
				Derive(func(b *Argument) {
					b.Do(Unfold(functions.InjectiveOnDef))
					u, v := b.FixAs[Permutation[A]]("u"), b.FixAs[Permutation[A]]("v")
					same := b.Assume()
					carriers := b.Have(
						"L and l lie in M",
						"L ⊆ M.carrier ∧ «constants» ⊆ M.carrier",
						By(data.subL, data.subC, field.SubfieldSubset.At(m, L), field.SubfieldSubset.At(m, constants)))
					onConstants := b.Have(
						"they agree on l, through g",
						"∀c:A. c ∈ «constants» ⇒ permutation_map(u, c) = permutation_map(v, c)",
						By(same, chosen.At(u), chosen.At(v)))
					onField := b.Have(
						"they agree on L, fixing it",
						"∀x:A. x ∈ L ⇒ permutation_map(u, x) = permutation_map(v, x)",
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							inField := c.Assume()
							c.Show(
								"both fix x",
								By(same, inField, fixesField.At(u, x), fixesField.At(v, x)))
						}))
					b.Show(
						"L and l generate N",
						BySets(
							M,
							same,
							widened,
							carriers,
							onConstants,
							onField,
							field_automorphism.AutomorphismsAgreeOnGenerators.Read(M).At(L, constants, u, v)))
				}))
			images := a.TermAs[Set[Permutation[A]]]("image(g, field_automorphisms(M, L, «composite»))")
			inside := a.Have(
				"restrictions lie in Aut(l/k)",
				"image(g, field_automorphisms(M, L, «composite»)) ⊆ field_automorphisms(M, k, «constants»)",
				BySets(chosen))
			imageCount := a.Have(
				"they number [l : k]",
				"card(image(g, field_automorphisms(M, L, «composite»))) = extension_degree(M, k, «constants»)",
				By(injective, count, cardinality.CardImageInj.At(g, upstairs)))
			small := a.Have(
				"and at most |Aut(l/k)|",
				"card(image(g, field_automorphisms(M, L, «composite»))) ≤ "+
					"card(field_automorphisms(M, k, «constants»))",
				ByArith(
					inside,
					bound,
					cardinality.BoundedCountOfSubset.At(
						images, downstairs, a.TermAs[Nat]("card(field_automorphisms(M, k, «constants»))"))))
			counted := a.Have(
				"the two counts agree",
				"card(image(g, field_automorphisms(M, L, «composite»))) = "+
					"card(field_automorphisms(M, k, «constants»))",
				ByArith(imageCount, small, bound))
			onto := a.Have(
				"so every automorphism of l over k is a restriction",
				"image(g, field_automorphisms(M, L, «composite»)) = field_automorphisms(M, k, «constants»)",
				By(inside, bound, counted, cardinality.CardSubsetEq.At(images, downstairs)))
			u, restriction := a.ObtainAs[Permutation[A]](
				"r is the restriction of some u",
				"∃u:permutation(A). u ∈ field_automorphisms(M, L, «composite») ∧ r = g(u)",
				BySets(onto, rIn))
			a.Take(u)
			a.Show(
				"u extends r",
				By(restriction, chosen.At(u)))
		}),
})}

// ConstantAutomorphismLiftExists — an automorphism of L over k(t) extends to
// the composite N = L·l fixing l: L is regular over k, so its exact constants
// are k itself, and GeometricGaloisBaseChange at r = 1 carries s to an
// automorphism of N over l(t).
var ConstantAutomorphismLiftExists = constantAutomorphismLiftExistsThm{family.Add(registry.ProofEntry{
	Name: "ConstantAutomorphismLiftExists",
	Key:  "prop_76a23fefb5d8bc7a",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), e)"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
		},
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀e:num. ∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, field_adjoin(M, k, {t}), L)",
			"0 < e",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "∃u:permutation(A). " +
			"    u ∈ field_automorphisms(M, «constants», «composite») ∧ " +
			"    (∀x:A. x ∈ L ⇒ permutation_map(u, x) = permutation_map(s, x))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			e *Expr[Nat],
			s *Expr[Permutation[A]],
			closed, regular, finiteK, tIn, transcendental, galois, positive, sIn Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			one := a.TermAs[Nat]("1")
			constants := a.TermAs[Set[A]]("«constants»")
			composite := a.TermAs[Set[A]]("«composite»")
			data := readConstantComposite(a, M, L, k, e, regular, finiteK, positive)
			exactConstants := a.Have(
				"the exact constants of L are k",
				"k = {x:A | x ∈ L ∧ algebraic_over(M, k, x)}",
				BySets(data.kInL, data.exact, data.subK, algebraic_element.MemberAlgebraic.Read(M)))
			extension := a.Have(
				"base change extends the automorphisms of L over k(t)",
				"∃rho:(permutation(A) → permutation(A)). "+
					"    group_isomorphism(galois_group(M, field_adjoin(M, k, {t}), L), "+
					"        galois_group(M, field_adjoin(M, «constants», {t}), «composite»), "+
					"        rho) ∧ "+
					"    (∀u:permutation(A). "+
					"        u ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L) ⇒ "+
					"        ∀x:A. x ∈ L ⇒ permutation_map(rho(u), x) = permutation_map(u, x))",
				By(
					closed,
					data.subK,
					finiteK,
					exactConstants,
					data.subL,
					data.kInL,
					tIn,
					transcendental,
					galois,
					positive,
					nat_arith.PowOne.At(a.TermAs[Nat]("card(k)")),
					set_order.SubsetRefl.At(L),
					nat_divides.OneDivides.At(e),
					constant_galois.GeometricGaloisBaseChange.Read(M).At(k, k, L, L, t, one, e)))
			rho, extends := a.UnpackAs[Fun[Permutation[A], Permutation[A]]](extension, "rho")
			parts := a.Conjuncts(
				extends,
				"rho is an isomorphism of the two groups",
				"rho extends each automorphism")
			image := a.TermAs[Permutation[A]]("rho(s)")
			sourceGroup := a.TermAs[group.GroupOps[Permutation[A]]](
				"galois_group(M, field_adjoin(M, k, {t}), L)")
			targetGroup := a.TermAs[group.GroupOps[Permutation[A]]](
				"galois_group(M, field_adjoin(M, «constants», {t}), «composite»)")
			inside := a.Have(
				"the homomorphism rho carries s to an automorphism of N over l(t)",
				"rho(s) ∈ field_automorphisms(M, field_adjoin(M, «constants», {t}), «composite»)",
				By(
					parts[0],
					sIn,
					group_homomorphism.GroupIsomorphismDef.At(sourceGroup, targetGroup, rho),
					group_homomorphism.MapIn.At(sourceGroup, targetGroup, rho, s)))
			tInCarrier := a.Have(
				"t lies in M",
				"t ∈ M.carrier",
				BySets(tIn, data.subL, field.SubfieldSubset.At(m, L)))
			enlarged := a.Have(
				"l lies in l(t)",
				"«constants» ⊆ field_adjoin(M, «constants», {t})",
				By(
					data.subC,
					tInCarrier,
					algebraic_element.AdjoinElementSubfield.Read(M).AsFact().At(constants, t)))
			a.Take(image)
			a.Show(
				"rho(s) fixes l and extends s",
				BySets(
					inside,
					enlarged,
					sIn,
					parts[1].At(s),
					field_automorphism.AutomorphismsAntitone.Read(M).At(
						constants, a.TermAs[Set[A]]("field_adjoin(M, «constants», {t})"), composite)))
		}),
})}

// ConstantTwistOrder — an automorphism p of N = L·l acting as s on L and as the
// q-power on l has the order e of s, when s^e = 1 and l has q^e elements. By
// induction p^j acts as s^j on L and as the q^j-power on l; so p^e is the
// identity on L and on l, which generate N. If p^d is the identity then every
// point of l is fixed by the q^d-power, of which there are at most q^d, so
// q^e ≤ q^d.
var ConstantTwistOrder = constantTwistOrderThm{family.Add(registry.ProofEntry{
	Name: "ConstantTwistOrder",
	Key:  "prop_772d5c4e3c1a0afd",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "power", Text: "λs:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        s, " +
				"        d)"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), e)"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
		},
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀e:num. ∀s p:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"0 < e",
			"s ∈ field_automorphisms(M, ∅, L)",
			"«power»(s, e) = permutation_identity",
			"p ∈ field_automorphisms(M, ∅, «composite»)",
			"∀x:A. x ∈ L ⇒ permutation_map(p, x) = permutation_map(s, x)",
			"∀c:A. c ∈ «constants» ⇒ permutation_map(p, c) = monoid_pow(M.mul, M.one, c, card(k))",
		},
		Conclusion: "«power»(p, e) = permutation_identity ∧ " +
			"(∀d:num. 0 < d ∧ «power»(p, d) = permutation_identity ⇒ e ≤ d)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			e *Expr[Nat],
			s, p *Expr[Permutation[A]],
			closed, regular, finiteK, positive, sIn, annihilates, pIn, onField, onConstants Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			q := a.TermAs[Nat]("card(k)")
			constants := a.TermAs[Set[A]]("«constants»")
			nothing := a.TermAs[Set[A]]("∅")
			composite := a.TermAs[Set[A]]("«composite»")
			permutations := a.TermAs[group.GroupOps[Permutation[A]]]("permutation_group")
			fieldGroup := a.TermAs[Set[Permutation[A]]]("field_automorphisms(M, ∅, L)")
			compositeGroup := a.TermAs[Set[Permutation[A]]]("field_automorphisms(M, ∅, «composite»)")
			identity := a.TermAs[Permutation[A]]("permutation_identity")
			monoid := comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))
			data := readConstantComposite(a, M, L, k, e, closed, regular, finiteK, positive)
			fieldSubgroup := a.Have(
				"the automorphisms of L are a subgroup of permutations of L",
				"subgroup(permutation_group, field_automorphisms(M, ∅, L)) ∧ "+
					"field_automorphisms(M, ∅, L) ⊆ symmetric_group(L)",
				By(field_automorphism.AutomorphismsSubgroup.Read(M).At(nothing, L)))
			compositeSubgroup := a.Have(
				"and those of N",
				"subgroup(permutation_group, field_automorphisms(M, ∅, «composite»))",
				By(field_automorphism.AutomorphismsSubgroup.Read(M).At(nothing, composite)))
			powerOnField := a.Have(
				"p^j acts on L as s^j",
				"∀j:num. ∀x:A. x ∈ L ⇒ permutation_map(«power»(p, j), x) = permutation_map(«power»(s, j), x)",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					b.Induct(j)
					b.Base(
						"both zeroth powers are the identity",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						Basic())
					b.Step(
						"one more factor is p on the left and s on the right",
						func(c *Argument, inductive Fact) {
							x := c.FixAs[A]("x")
							inField := c.Assume()
							sPower := c.TermAs[Permutation[A]]("«power»(s, j)")
							pPower := c.TermAs[Permutation[A]]("«power»(p, j)")
							value := c.TermAs[A]("permutation_map(«power»(s, j), x)")
							stays := c.Have(
								"s^j keeps L",
								"permutation_map(«power»(s, j), x) ∈ L",
								BySets(
									inField,
									sIn,
									fieldSubgroup,
									symmetric_group.PermutationPowerIn.At(fieldGroup, s, j),
									symmetric_group.SymmetricGroupMapsInto.At(L, sPower, x)))
							c.Show(
								"unfold the next powers and apply p, then s",
								By(
									inField,
									stays,
									inductive.At(x),
									onField.At(value),
									comm_monoid.MonoidPowDef,
									symmetric_group.MapCompose.At(p, pPower, x),
									symmetric_group.MapCompose.At(s, sPower, x)))
						})
				}))
			inCarrier := a.Have(
				"l lies in M",
				"«constants» ⊆ M.carrier",
				By(data.subC, field.SubfieldSubset.At(m, constants)))
			powerStays := a.Have(
				"l is closed under powers",
				"∀c:A. ∀n:num. c ∈ «constants» ⇒ monoid_pow(M.mul, M.one, c, n) ∈ «constants»",
				By(M, data.subC, At(field.SubfieldPowerIn, m, constants)))
			powerOnConstants := a.Have(
				"p^j acts on l as the q^j-power",
				Statement{
					Binders: "∀j:num. ∀c:A.",
					Hypotheses: []string{
						"c ∈ «constants»",
					},
					Conclusion: "permutation_map(«power»(p, j), c) = monoid_pow(M.mul, M.one, c, card(k) ^ j)",
				},
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					b.Induct(j)
					b.Base(
						"the first power of c is c",
						func(c *Argument) {
							x := c.FixAs[A]("x")
							member := c.Assume()
							inside := c.Have(
								"x lies in M",
								"x ∈ M.carrier",
								BySets(member, inCarrier))
							c.Do(Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(nat_arith.NatPow), Fwd(symmetric_group.MapIdentity)))
							c.Show(
								"the zeroth powers are the identity",
								By(inside, comm_monoid.PowOneOn.Read(monoid).AsFact().At(x)))
						})
					b.Step(
						"one more factor of p raises to the q-th power once more",
						func(c *Argument, inductive Fact) {
							x := c.FixAs[A]("x")
							member := c.Assume()
							exponent := c.TermAs[Nat]("card(k) ^ j")
							value := c.TermAs[A]("monoid_pow(M.mul, M.one, x, card(k) ^ j)")
							inside := c.Have(
								"x lies in M",
								"x ∈ M.carrier",
								BySets(member, inCarrier))
							exponentStep := c.Have(
								"the exponent is multiplied by q",
								"card(k) ^ suc(j) = (card(k) ^ j) * card(k)",
								By(Normalized, nat_arith.NatPow, nat_arith.MulSym.At(q, exponent)))
							c.Do(
								exponentStep.Rw(),
								Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(symmetric_group.MapCompose)))
							c.Show(
								"apply p to the q^j-power, then multiply the exponents",
								By(
									member,
									inside,
									inductive.At(x),
									powerStays.At(x, exponent),
									onConstants.At(value),
									comm_monoid.PowPowOn.Read(monoid).AsFact().At(x, exponent, q)))
						})
				}))
			fixedConstants := a.Have(
				"the q^e-power fixes l",
				"∀c:A. c ∈ «constants» ⇒ monoid_pow(M.mul, M.one, c, card(k) ^ e) = c",
				Simp(Fwd(finite_field.FiniteConstantsDef), Fwd(field.FieldRingDef)),
				BySets())
			sameGroup := a.Have(
				"N is L(l)",
				"field_automorphisms(M, ∅, field_adjoin(M, L, «constants»)) = "+
					"field_automorphisms(M, ∅, «composite»)",
				Simp(Fwd(constant_composite.ConstantCompositeDef)),
				Basic())
			carriers := a.Have(
				"L and l lie in M",
				"L ⊆ M.carrier ∧ «constants» ⊆ M.carrier",
				By(data.subL, inCarrier, field.SubfieldSubset.At(m, L)))
			pPowerE := a.TermAs[Permutation[A]]("«power»(p, e)")
			top := a.Have(
				"p^e and the identity agree on L and on l, which generate N",
				"«power»(p, e) = permutation_identity",
				BySets(
					M,
					carriers,
					sameGroup,
					pIn,
					compositeSubgroup,
					symmetric_group.PermutationPowerIn.At(compositeGroup, p, e),
					group.SubgroupOne.At(permutations, compositeGroup),
					field_automorphism.AutomorphismsAgreeOnGenerators.Read(M).At(L, constants, pPowerE, identity),
					symmetric_group.MapIdentity,
					powerOnField.At(e),
					powerOnConstants.At(e),
					fixedConstants,
					annihilates))
			size := a.Have(
				"l has q^e members",
				"has_size(«constants», card(k) ^ e)",
				By(closed, data.subK, finiteK, positive, finite_field.FiniteConstantsSubfield.Read(M).At(k, e)))
			a.Show(
				"p^e is the identity, and a smaller positive exponent would not fix l",
				SplitConj(
					Case(
						"p^e is the identity",
						By(top)),
					Case(
						"every positive annihilator is at least e",
						Derive(func(b *Argument) {
							d := b.FixAs[Nat]("d")
							annihilator := b.Assume()
							parts := b.Conjuncts(
								annihilator,
								"d is positive",
								"p^d is the identity")
							_, _, atLeastTwo := b.Obtain2As[Nat, Nat](
								"q is at least two",
								"∃c n:num. ring_prime_characteristic(field_ring(M), c) ∧ 0 < n ∧ card(k) = c ^ n ∧ 2 ≤ card(k)",
								By(data.subK, finiteK, finite_field.FiniteSubfieldPrimePower.Read(M).At(k)))
							exponentSize := b.Have(
								"q^d exceeds one",
								"1 < card(k) ^ d",
								ByArith(atLeastTwo, parts[0], nat_arith.NatPow, nat_order.LessThanPow.At(q, b.TermAs[Nat]("0"), d)))
							larger := b.TermAs[Set[A]]("finite_constants(field_ring(M), card(k), d)")
							fixed := b.Have(
								"every point of l is fixed by the q^d-power",
								"∀c:A. c ∈ «constants» ⇒ monoid_pow(M.mul, M.one, c, card(k) ^ d) = c",
								Derive(func(c *Argument) {
									x := c.FixAs[A]("x")
									member := c.Assume()
									c.Show(
										"p^d is the identity",
										By(member, parts[1], powerOnConstants.At(d, x), symmetric_group.MapIdentity))
								}))
							contained := b.Have(
								"so l lies among the q^d-fixed points",
								"«constants» ⊆ finite_constants(field_ring(M), card(k), d)",
								Simp(Fwd(finite_field.FiniteConstantsDef), Fwd(field.FieldRingDef)),
								BySets(fixed, inCarrier, finite_field.FiniteConstantsDef))
							bounded := b.Have(
								"of which there are at most q^d",
								"finite(«constants») ∧ card(«constants») ≤ card(k) ^ d",
								By(
									contained,
									exponentSize,
									finite_field.FiniteConstantsBound.Read(M).At(q, d),
									cardinality.BoundedCountOfSubset.At(constants, larger, b.TermAs[Nat]("card(k) ^ d"))))
							b.Show(
								"q^e ≤ q^d, so e ≤ d",
								ByArith(bounded, size, cardinality.HasSizeDef, atLeastTwo, nat_order.LessThanPow.At(q, d, e)))
						})),
				))
		}),
})}

// _twistSetting is the setting of a constant twist read apart: k and L are
// subfields with k in L and k is perfect, k(t) lies between k and L, L is finite
// over k(t), and the order of s is positive and annihilates s.
type _twistSetting struct {
	regularity, tower, finite, positive, annihilates Fact
}

// readTwistSetting reads the setting of a constant twist off its hypotheses: L
// regular over k, t a point of L, L Galois over k(t) and s an automorphism of L
// over k(t). The order of s is field_automorphism.AutomorphismOrderFacts read at k(t).
func readTwistSetting(
	a *Argument,
	M field.FieldFact[on.M],
	k, L *Expr[Set[A]],
	t *Expr[A],
	s *Expr[Permutation[A]],
	regular, tIn, galois, sIn Fact,
) _twistSetting {
	base := a.TermAs[Set[A]]("field_adjoin(M, k, {t})")
	regularity := a.Have(
		"k and L are subfields with k in L, and k is perfect",
		"subfield(M, k) ∧ subfield(M, L) ∧ k ⊆ L ∧ perfect_field(restrict_field(M, k))",
		By(a.Unfolded(regular, function_field.RegularFunctionFieldDef)))
	tower := a.Have(
		"k(t) lies between k and L",
		"subfield(M, field_adjoin(M, k, {t})) ∧ "+
			"k ⊆ field_adjoin(M, k, {t}) ∧ "+
			"t ∈ field_adjoin(M, k, {t}) ∧ "+
			"field_adjoin(M, k, {t}) ⊆ L",
		By(regularity, tIn, algebraic_element.AdjoinElementBetween.Read(M).At(k, L, t)))
	finite := a.Have(
		"L is finite over k(t)",
		"finite_extension(M, field_adjoin(M, k, {t}), L)",
		By(a.Unfolded(galois, galois_correspondence.GaloisOverDef)))
	order := a.Conjuncts(
		GroupPremises(
			tower, regularity, sIn, finite, field_automorphism.AutomorphismOrderFacts.Read(M).At(base, L, s)),
		"the order is positive",
		"it annihilates s",
		"it is the least such",
		"it divides the group order")
	return _twistSetting{regularity, tower, finite, order[0], order[1]}
}

// _twistOrder is ConstantTwistOrder read at the twist φ: φ^e is the identity,
// and no smaller positive power of φ is.
type _twistOrder struct {
	returns, least Fact
}

// readTwistOrder reads ConstantTwistOrder at the twist φ, an automorphism of N
// over k(t) acting as s on L and as the q-power on l: automorphisms over k(t),
// φ and s are automorphisms of N and of L.
func readTwistOrder(
	a *Argument,
	M field.FieldFact[on.M],
	k, L *Expr[Set[A]],
	t *Expr[A],
	s *Expr[Permutation[A]],
	setting _twistSetting,
	closed, regular, finiteK, sIn, twistIn, onField, onConstants Fact,
) _twistOrder {
	e := a.TermAs[Nat]("permutation_order(s)")
	nothing := a.TermAs[Set[A]]("∅")
	base := a.TermAs[Set[A]]("field_adjoin(M, k, {t})")
	composite := a.TermAs[Set[A]](
		"constant_composite(M, L, finite_constants(field_ring(M), card(k), permutation_order(s)))")
	twist := a.TermAs[Permutation[A]]("constant_twist_automorphism(M, k, L, s)")
	twistFree := a.Have(
		"φ is an automorphism of N",
		"constant_twist_automorphism(M, k, L, s) ∈ "+
			"field_automorphisms(M, "+
			"    ∅, "+
			"    constant_composite(M, L, finite_constants(field_ring(M), card(k), permutation_order(s))))",
		BySets(twistIn, field_automorphism.AutomorphismsAntitone.Read(M).At(nothing, base, composite)))
	sFree := a.Have(
		"s is an automorphism of L",
		"s ∈ field_automorphisms(M, ∅, L)",
		BySets(sIn, field_automorphism.AutomorphismsAntitone.Read(M).At(nothing, base, L)))
	parts := a.Conjuncts(
		GroupPremises(
			closed,
			regular,
			finiteK,
			setting.positive,
			sFree,
			setting.annihilates,
			twistFree,
			onField,
			onConstants,
			ConstantTwistOrder.Read(M).At(k, L, e, s, twist)),
		"φ^e is the identity",
		"no smaller positive power of φ is")
	return _twistOrder{parts[0], parts[1]}
}

// ConstantTwistActs — the two lifts exist, and their product φ fixes k(t), acts
// as s on L and as the q-power on the constants, and fixes the twisted field.
// The lift of s is ConstantAutomorphismLiftExists, and the Frobenius lift is
// the q-power on l (finite_field.FrobeniusConstantAutomorphism) extended over L
// (ConstantAutomorphismExtends); each meets the description that defines it.
// On L the Frobenius lift is the identity and on l the lift of s is, which gives
// the two actions. A point of the twisted field is fixed by φ¹ when 1 < e, and
// when e = 1, φ itself is the identity (ConstantTwistOrder).
var ConstantTwistActs = constantTwistActsThm{family.Add(registry.ProofEntry{
	Name: "ConstantTwistActs",
	Key:  "prop_d32cc28887a3b0d4",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
			{Name: "frobenius", Text: "constant_frobenius_lift(M, k, L, s)"},
			{Name: "lift", Text: "constant_automorphism_lift(M, k, L, s)"},
			{Name: "twist", Text: "constant_twist_automorphism(M, k, L, s)"},
			{Name: "power", Text: "λu:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        u, " +
				"        d)"},
		},
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, field_adjoin(M, k, {t}), L)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "«frobenius» ∈ field_automorphisms(M, L, «composite») ∧ " +
			"(∀c:A. " +
			"    c ∈ «constants» ⇒ permutation_map(«frobenius», c) = monoid_pow(M.mul, M.one, c, card(k))) ∧ " +
			"«lift» ∈ field_automorphisms(M, «constants», «composite») ∧ " +
			"(∀x:A. x ∈ L ⇒ permutation_map(«lift», x) = permutation_map(s, x)) ∧ " +
			"«twist» ∈ field_automorphisms(M, field_adjoin(M, k, {t}), «composite») ∧ " +
			"(∀x:A. x ∈ L ⇒ permutation_map(«twist», x) = permutation_map(s, x)) ∧ " +
			"(∀c:A. c ∈ «constants» ⇒ permutation_map(«twist», c) = monoid_pow(M.mul, M.one, c, card(k))) ∧ " +
			"(∀y:A. y ∈ constant_twist_field(M, k, L, s) ⇒ permutation_map(«twist», y) = y)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			s *Expr[Permutation[A]],
			closed, regular, finiteK, tIn, transcendental, galois, sIn Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			e := a.TermAs[Nat]("permutation_order(s)")
			q := a.TermAs[Nat]("card(k)")
			constants := a.TermAs[Set[A]]("«constants»")
			composite := a.TermAs[Set[A]]("«composite»")
			base := a.TermAs[Set[A]]("field_adjoin(M, k, {t})")
			frobenius := a.TermAs[Permutation[A]]("«frobenius»")
			lift := a.TermAs[Permutation[A]]("«lift»")
			permutations := a.TermAs[group.GroupOps[Permutation[A]]]("permutation_group")
			twistGroup := a.TermAs[Set[Permutation[A]]](
				"field_automorphisms(M, field_adjoin(M, k, {t}), «composite»)")
			setting := readTwistSetting(a, M, k, L, t, s, regular, tIn, galois, sIn)
			data := readConstantComposite(a, M, L, k, e, setting.positive, closed, regular, finiteK)
			r, frobeniusOnConstants := a.ObtainAs[Permutation[A]](
				"the q-power is an automorphism of l over k",
				"∃r:permutation(A). "+
					"    r ∈ field_automorphisms(M, k, «constants») ∧ "+
					"    (∀c:A. c ∈ «constants» ⇒ permutation_map(r, c) = monoid_pow(M.mul, M.one, c, card(k)))",
				By(
					data.subK,
					finiteK,
					data.subC,
					data.kInC,
					data.finiteC,
					finite_field.FrobeniusConstantAutomorphism.Read(M).At(k, constants)))
			rParts := a.Conjuncts(
				frobeniusOnConstants,
				"r is an automorphism",
				"r is the q-power")
			u, extended := a.ObtainAs[Permutation[A]](
				"it extends to an automorphism of N over L",
				"∃u:permutation(A). "+
					"    u ∈ field_automorphisms(M, L, «composite») ∧ "+
					"    (∀c:A. c ∈ «constants» ⇒ permutation_map(u, c) = permutation_map(r, c))",
				By(
					closed,
					regular,
					finiteK,
					setting.positive,
					rParts[0],
					ConstantAutomorphismExtends.Read(M).At(k, L, e, r)))
			frobeniusExists := a.Have(
				"so the description of the Frobenius lift is met",
				"∃u:permutation(A). "+
					"    u ∈ field_automorphisms(M, L, «composite») ∧ "+
					"    (∀c:A. c ∈ «constants» ⇒ permutation_map(u, c) = monoid_pow(M.mul, M.one, c, card(k)))",
				Witness(u),
				By(extended, rParts[1]))
			_, frobeniusChosen := a.ObtainChosen(
				"the choice in the definition meets it",
				"∃u:permutation(A). "+
					"    u ∈ field_automorphisms(M, L, «composite») ∧ "+
					"    (∀c:A. c ∈ «constants» ⇒ permutation_map(u, c) = monoid_pow(M.mul, M.one, c, card(k)))",
				frobeniusExists)
			frobeniusParts := a.Conjuncts(
				a.Have(
					"the Frobenius lift is that choice",
					"«frobenius» ∈ field_automorphisms(M, L, «composite») ∧ "+
						"(∀c:A. c ∈ «constants» ⇒ permutation_map(«frobenius», c) = monoid_pow(M.mul, M.one, c, card(k)))",
					By(frobeniusChosen, constantFrobeniusLiftDef.At(m, k, L, s))),
				"the Frobenius lift is an automorphism over L",
				"it is the q-power on l")
			liftExists := a.Have(
				"the description of the automorphism lift is met",
				"∃u:permutation(A). "+
					"    u ∈ field_automorphisms(M, «constants», «composite») ∧ "+
					"    (∀x:A. x ∈ L ⇒ permutation_map(u, x) = permutation_map(s, x))",
				By(
					closed,
					regular,
					finiteK,
					tIn,
					transcendental,
					galois,
					setting.positive,
					sIn,
					ConstantAutomorphismLiftExists.Read(M).At(k, L, t, e, s)))
			_, liftChosen := a.ObtainChosen(
				"the choice in the definition meets it",
				"∃u:permutation(A). "+
					"    u ∈ field_automorphisms(M, «constants», «composite») ∧ "+
					"    (∀x:A. x ∈ L ⇒ permutation_map(u, x) = permutation_map(s, x))",
				liftExists)
			liftParts := a.Conjuncts(
				a.Have(
					"the automorphism lift is that choice",
					"«lift» ∈ field_automorphisms(M, «constants», «composite») ∧ "+
						"(∀x:A. x ∈ L ⇒ permutation_map(«lift», x) = permutation_map(s, x))",
					By(liftChosen, constantAutomorphismLiftDef.At(m, k, L, s))),
				"the automorphism lift is an automorphism over l",
				"it is s on L")
			frobeniusLaws := a.Have(
				"the Frobenius lift fixes L",
				"∀x:A. x ∈ L ⇒ permutation_map(«frobenius», x) = x",
				BySets(a.Unfolded(frobeniusParts[0], field_automorphism.FieldAutomorphismsDef)))
			liftLaws := a.Have(
				"the automorphism lift permutes N, keeps its operations and fixes l",
				"«lift» ∈ symmetric_group(«composite») ∧ "+
					"(∀x y:A. "+
					"    x ∈ «composite» ∧ y ∈ «composite» ⇒ "+
					"    permutation_map(«lift», x + y) = permutation_map(«lift», x) + permutation_map(«lift», y)) ∧ "+
					"(∀x y:A. "+
					"    x ∈ «composite» ∧ y ∈ «composite» ⇒ "+
					"    permutation_map(«lift», x * y) = permutation_map(«lift», x) * permutation_map(«lift», y)) ∧ "+
					"(∀x:A. x ∈ «constants» ⇒ permutation_map(«lift», x) = x)",
				BySets(a.Unfolded(liftParts[0], field_automorphism.FieldAutomorphismsDef)))
			sFixesBase := a.Have(
				"s fixes k(t)",
				"∀x:A. x ∈ field_adjoin(M, k, {t}) ⇒ permutation_map(s, x) = x",
				BySets(a.Unfolded(sIn, field_automorphism.FieldAutomorphismsDef)))
			liftFixesBase := a.Have(
				"so the automorphism lift fixes k(t)",
				"∀x:A. x ∈ field_adjoin(M, k, {t}) ⇒ permutation_map(«lift», x) = x",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					inField := b.Have(
						"x lies in L",
						"x ∈ L",
						BySets(member, setting.tower))
					b.Show(
						"it is s on L",
						By(member, inField, liftParts[1].At(x), sFixesBase.At(x)))
				}))
			liftInGroup := a.Have(
				"the automorphism lift is an automorphism of N over k(t)",
				"«lift» ∈ field_automorphisms(M, field_adjoin(M, k, {t}), «composite»)",
				Simp(Fwd(field_automorphism.FieldAutomorphismsDef)),
				BySets(liftLaws, liftFixesBase))
			frobeniusInGroup := a.Have(
				"and so is the Frobenius lift",
				"«frobenius» ∈ field_automorphisms(M, field_adjoin(M, k, {t}), «composite»)",
				BySets(
					frobeniusParts[0],
					setting.tower,
					field_automorphism.AutomorphismsAntitone.Read(M).At(base, L, composite)))
			twistDefinition := ConstantTwistAutomorphismDef.At(m, k, L, s)
			twistInGroup := a.Have(
				"their product is an automorphism of N over k(t)",
				"«twist» ∈ field_automorphisms(M, field_adjoin(M, k, {t}), «composite»)",
				By(
					twistDefinition,
					liftInGroup,
					frobeniusInGroup,
					field_automorphism.AutomorphismsSubgroup.Read(M).At(base, composite),
					group.SubgroupMul.At(permutations, twistGroup, lift, frobenius)))
			twistOnField := a.Have(
				"on L the product is s, the Frobenius lift fixing L",
				"∀x:A. x ∈ L ⇒ permutation_map(«twist», x) = permutation_map(s, x)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inField := b.Assume()
					b.Show(
						"apply the Frobenius lift, then the automorphism lift",
						By(
							inField,
							twistDefinition,
							frobeniusLaws.At(x),
							liftParts[1].At(x),
							symmetric_group.MapCompose.At(lift, frobenius, x)))
				}))
			twistOnConstants := a.Have(
				"on l the product is the q-power, the automorphism lift fixing l",
				"∀c:A. c ∈ «constants» ⇒ permutation_map(«twist», c) = monoid_pow(M.mul, M.one, c, card(k))",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					stays := b.Have(
						"the q-th power of x lies in l",
						"monoid_pow(M.mul, M.one, x, card(k)) ∈ «constants»",
						By(data.subC, member, field.SubfieldPowerIn.Read(M).At(constants, x, q)))
					liftFixes := b.Have(
						"the automorphism lift fixes it",
						"permutation_map(«lift», monoid_pow(M.mul, M.one, x, card(k))) = "+
							"monoid_pow(M.mul, M.one, x, card(k))",
						BySets(stays, liftLaws))
					b.Show(
						"apply the Frobenius lift, then the automorphism lift",
						By(
							member,
							twistDefinition,
							liftFixes,
							frobeniusParts[1].At(x),
							symmetric_group.MapCompose.At(lift, frobenius, x)))
				}))
			order := readTwistOrder(
				a,
				M,
				k,
				L,
				t,
				s,
				setting,
				closed,
				regular,
				finiteK,
				sIn,
				twistInGroup,
				twistOnField,
				twistOnConstants)
			firstPower := a.Have(
				"the first power of the product is the product",
				"«power»(«twist», 1) = «twist»",
				Simp(Fwd(nat_arith.OneIsSucZero), Fwd(comm_monoid.MonoidPowDef)),
				By(group.RightIdentity.Read(symmetric_group.SymmetricGroup)))
			fixedByPowers := a.Have(
				"a point of the twisted field is fixed by the powers below e",
				"∀y:A. "+
					"    y ∈ constant_twist_field(M, k, L, s) ⇒ "+
					"    ∀j:num. j < permutation_order(s) ⇒ permutation_map(«power»(«twist», j), y) = y",
				Simp(Fwd(ConstantTwistFieldDef), Fwd(field_automorphism.FixedFieldDef)),
				BySets())
			fixedPoints := a.Have(
				"so the product fixes the twisted field",
				"∀y:A. y ∈ constant_twist_field(M, k, L, s) ⇒ permutation_map(«twist», y) = y",
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					member := b.Assume()
					one := b.TermAs[Nat]("1")
					b.Cases(b.Term("1 < permutation_order(s)"))
					b.When(
						"when 1 < e the product is among the powers",
						func(c *Argument, large Fact) {
							c.Show(
								"it is the first power",
								By(large, member, firstPower, fixedByPowers.At(y, one)))
						})
					b.Otherwise(
						"when e = 1 the product is its e-th power, the identity",
						func(c *Argument, small Fact) {
							top := c.Have(
								"the order is 1",
								"permutation_order(s) = 1",
								ByArith(small, setting.positive))
							c.Show(
								"the identity fixes every point",
								By(top, order.returns, firstPower, symmetric_group.MapIdentity))
						})
				}))
			a.Show(
				"the lifts are as described, and φ is an automorphism of N over "+
					"k(t) that is s on L and the q-power on l and fixes the twisted field",
				By(
					frobeniusParts[0],
					frobeniusParts[1],
					liftParts[0],
					liftParts[1],
					twistInGroup,
					twistOnField,
					twistOnConstants,
					fixedPoints))
		}),
})}

// ConstantTwistFieldData — the twisted field is the fixed field of a cyclic
// group of order e: φ has order e (ConstantTwistOrder), so its powers below e
// are a subgroup of e automorphisms of N over k(t) (symmetric_group.PowersSubgroup), and Artin
// gives [N : L_s] = e with k(t) inside L_s.
var ConstantTwistFieldData = constantTwistFieldDataThm{family.Add(registry.ProofEntry{
	Name: "ConstantTwistFieldData",
	Key:  "prop_3c737b2910d58fb9",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
			{Name: "twist", Text: "constant_twist_automorphism(M, k, L, s)"},
			{Name: "twisted", Text: "constant_twist_field(M, k, L, s)"},
			{Name: "power", Text: "λu:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        u, " +
				"        d)"},
			{Name: "powers", Text: "{«power»(«twist», j) | j:num | j < permutation_order(s)}"},
		},
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, field_adjoin(M, k, {t}), L)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "subfield(M, «twisted») ∧ " +
			"field_adjoin(M, k, {t}) ⊆ «twisted» ∧ " +
			"«twisted» ⊆ «composite» ∧ " +
			"finite_extension(M, «twisted», «composite») ∧ " +
			"extension_degree(M, «twisted», «composite») = permutation_order(s) ∧ " +
			"permutation_order(«twist») = permutation_order(s)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			s *Expr[Permutation[A]],
			closed, regular, finiteK, tIn, transcendental, galois, sIn Fact,
		) {
			e := a.TermAs[Nat]("permutation_order(s)")
			composite := a.TermAs[Set[A]]("«composite»")
			base := a.TermAs[Set[A]]("field_adjoin(M, k, {t})")
			nothing := a.TermAs[Set[A]]("∅")
			twist := a.TermAs[Permutation[A]]("«twist»")
			powers := a.TermAs[Set[Permutation[A]]]("«powers»")
			twistGroup := a.TermAs[Set[Permutation[A]]](
				"field_automorphisms(M, field_adjoin(M, k, {t}), «composite»)")
			setting := readTwistSetting(a, M, k, L, t, s, regular, tIn, galois, sIn)
			data := readConstantComposite(a, M, L, k, e, setting.positive, closed, regular, finiteK)
			acts := a.Conjuncts(
				GroupPremises(
					closed,
					regular,
					finiteK,
					tIn,
					transcendental,
					galois,
					sIn,
					ConstantTwistActs.Read(M).At(k, L, t, s)),
				"the Frobenius lift is an automorphism over L",
				"it is the q-power on l",
				"the automorphism lift is an automorphism over l",
				"it is s on L",
				"φ is an automorphism of N over k(t)",
				"φ is s on L",
				"φ is the q-power on l",
				"φ fixes the twisted field")
			order := readTwistOrder(
				a, M, k, L, t, s, setting, closed, regular, finiteK, sIn, acts[4], acts[5], acts[6])
			orderOfTwist := a.Have(
				"so φ has order e",
				"permutation_order(«twist») = permutation_order(s)",
				By(
					setting.positive,
					order.returns,
					order.least,
					symmetric_group.PermutationOrderUnique.At(twist, e)))
			cyclic := a.Have(
				"the powers of φ below e are a subgroup of e members",
				"subgroup(permutation_group, «powers») ∧ has_size(«powers», permutation_order(s))",
				By(setting.positive, order.returns, order.least, symmetric_group.PowersSubgroup.At(twist, e)))
			cyclicParts := a.Conjuncts(
				cyclic,
				"they are a subgroup",
				"there are e of them")
			eachIn := a.Have(
				"each power of φ is an automorphism of N over k(t)",
				"∀j:num. «power»(«twist», j) ∈ field_automorphisms(M, field_adjoin(M, k, {t}), «composite»)",
				a.ForEach(func(j *Expr[Nat]) Action {
					return By(
						acts[4],
						field_automorphism.AutomorphismsSubgroup.Read(M).At(base, composite),
						symmetric_group.PermutationPowerIn.At(twistGroup, twist, j))
				}))
			inGroup := a.Have(
				"so the powers lie in Aut(N/k(t))",
				"«powers» ⊆ field_automorphisms(M, field_adjoin(M, k, {t}), «composite»)",
				BySets(eachIn))
			free := a.Have(
				"and in Aut(N)",
				"«powers» ⊆ field_automorphisms(M, ∅, «composite»)",
				BySets(inGroup, field_automorphism.AutomorphismsAntitone.Read(M).At(nothing, base, composite)))
			count := a.Have(
				"the subgroup is finite with e members",
				"finite(«powers») ∧ card(«powers») = permutation_order(s)",
				By(cyclicParts[1], cardinality.HasSizeDef.At(powers, e)))
			artin := a.Have(
				"Artin: N has degree e over the fixed field",
				"finite_extension(M, fixed_field(«composite», «powers»), «composite») ∧ "+
					"extension_degree(M, fixed_field(«composite», «powers»), «composite») = permutation_order(s)",
				By(
					data.subN,
					count,
					cyclicParts[0],
					free,
					field_automorphism.ArtinFixedField.Read(M).At(composite, powers)))
			fixedSubfield := a.Have(
				"the fixed field is a subfield",
				"subfield(M, fixed_field(«composite», «powers»))",
				By(data.subN, free, field_automorphism.FixedFieldSubfield.Read(M).At(composite, powers)))
			baseInN := a.Have(
				"k(t) lies in N",
				"field_adjoin(M, k, {t}) ⊆ «composite»",
				BySets(setting.tower, data.LInN))
			powersFixBase := a.Have(
				"each power of φ fixes k(t)",
				"∀u:permutation(A). ∀x:A. u ∈ «powers» ∧ x ∈ field_adjoin(M, k, {t}) ⇒ permutation_map(u, x) = x",
				Derive(func(b *Argument) {
					b.FixAs[Permutation[A]]("u")
					b.FixAs[A]("x")
					both := b.Assume()
					inside := b.Have(
						"u is an automorphism over k(t)",
						"u ∈ field_automorphisms(M, field_adjoin(M, k, {t}), «composite»)",
						BySets(both, inGroup))
					b.Show(
						"among the conditions",
						BySets(both, b.Unfolded(inside, field_automorphism.FieldAutomorphismsDef)))
				}))
			baseFixed := a.Have(
				"k(t) is fixed by the powers of φ",
				"field_adjoin(M, k, {t}) ⊆ fixed_field(«composite», «powers»)",
				Simp(Fwd(field_automorphism.FixedFieldDef)),
				BySets(baseInN, powersFixBase))
			fixedInN := a.Have(
				"the fixed field lies in N",
				"fixed_field(«composite», «powers») ⊆ «composite»",
				Simp(Fwd(field_automorphism.FixedFieldDef)),
				BySets())
			a.Do(Simp(Fwd(ConstantTwistFieldDef)))
			a.Show(
				"the twisted field is that fixed field",
				By(fixedSubfield, baseFixed, fixedInN, artin, orderOfTwist))
		}),
})}

// TwistedFieldConstants — the elements of L_s algebraic over k are k. Such a
// point lies in N and is algebraic over l, so it lies in l, the constants of N
// (constant_composite.RegularConstantExtension); φ fixes it and acts on l as the
// q-power, so it is a fixed point of the q-power, a point of k
// (finite_field.SubfieldFrobeniusPoints).
var TwistedFieldConstants = twistedFieldConstantsThm{family.Add(registry.ProofEntry{
	Name: "TwistedFieldConstants",
	Key:  "prop_5ed8c4eba172cb",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
			{Name: "twist", Text: "constant_twist_automorphism(M, k, L, s)"},
			{Name: "twisted", Text: "constant_twist_field(M, k, L, s)"},
			{Name: "power", Text: "λu:permutation(A). λd:num. " +
				"    monoid_pow⟨A:permutation(A)⟩( " +
				"        (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
				"        permutation_identity⟨A:A⟩, " +
				"        u, " +
				"        d)"},
			{Name: "powers", Text: "{«power»(«twist», j) | j:num | j < permutation_order(s)}"},
		},
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀s:permutation(A). ∀x:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, field_adjoin(M, k, {t}), L)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
			"x ∈ «twisted»",
			"algebraic_over(M, k, x)",
		},
		Conclusion: "x ∈ k",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			s *Expr[Permutation[A]],
			closed, regular, finiteK, tIn, transcendental, galois, sIn Fact,
			x *Expr[A],
			inTwisted, algebraic Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			e := a.TermAs[Nat]("permutation_order(s)")
			constants := a.TermAs[Set[A]]("«constants»")
			setting := readTwistSetting(a, M, k, L, t, s, regular, tIn, galois, sIn)
			data := readConstantComposite(a, M, L, k, e, setting.positive, closed, regular, finiteK)
			regularN := a.Have(
				"N is regular over l",
				"regular_function_field(M, «constants», «composite»)",
				By(
					regular,
					data.subC,
					data.kInC,
					data.finiteC,
					constant_composite.RegularConstantExtension.Read(M).At(k, L, constants)))
			exactN := a.Have(
				"so the constants of N are l",
				"∀x:A. x ∈ «composite» ∧ algebraic_over(M, «constants», x) ⇒ x ∈ «constants»",
				By(a.Unfolded(regularN, function_field.RegularFunctionFieldDef)))
			fieldData := a.Have(
				"L_s lies in N",
				"«twisted» ⊆ «composite»",
				By(
					closed,
					regular,
					finiteK,
					tIn,
					transcendental,
					galois,
					sIn,
					ConstantTwistFieldData.Read(M).At(k, L, t, s)))
			acts := a.Conjuncts(
				GroupPremises(
					closed,
					regular,
					finiteK,
					tIn,
					transcendental,
					galois,
					sIn,
					ConstantTwistActs.Read(M).At(k, L, t, s)),
				"the Frobenius lift is an automorphism over L",
				"it is the q-power on l",
				"the automorphism lift is an automorphism over l",
				"it is s on L",
				"φ is an automorphism of N over k(t)",
				"φ is s on L",
				"φ is the q-power on l",
				"φ fixes the twisted field")
			lInCarrier := a.Have(
				"l lies in M",
				"«constants» ⊆ M.carrier",
				By(data.subC, field.SubfieldSubset.At(m, constants)))
			inN := a.Have(
				"x lies in N",
				"x ∈ «composite»",
				BySets(inTwisted, fieldData))
			inConstants := a.Have(
				"x is algebraic over l, so it lies in l",
				"x ∈ «constants»",
				By(
					algebraic,
					inN,
					data.kInC,
					exactN.At(x),
					algebraic_element.AlgebraicOverMono.Read(M).At(k, constants, x)))
			fixed := a.Have(
				"φ fixes x and acts on it as the q-power",
				"monoid_pow(M.mul, M.one, x, card(k)) = x",
				By(inTwisted, inConstants, acts[6].At(x), acts[7].At(x)))
			inCarrier := a.Have(
				"x lies in M",
				"x ∈ M.carrier",
				BySets(inConstants, lInCarrier))
			a.Show(
				"so x is a point of k",
				By(
					data.subK,
					finiteK,
					inCarrier,
					fixed,
					finite_field.SubfieldFrobeniusPoints.Read(M).AsFact().At(k, x)))
		}),
})}

// CyclicConstantTwistDescent — L_s is a regular function field over k, of degree
// |G| over k(t), with the same composite with l as L. [N : k(t)] = [N : L][L : k(t)]
// = e|G| and [N : L_s] = e (ConstantTwistFieldData), so the tower law gives
// [L_s : k(t)] = |G|. Its algebraic constants are k (TwistedFieldConstants), so
// it is regular over k (function_field.ExactConstantFieldFinite), and L_s·l has
// degree e over L_s inside N, so it is N. The Frobenius lift fixes t since it
// fixes L.
var CyclicConstantTwistDescent = cyclicConstantTwistDescentThm{family.Add(registry.ProofEntry{
	Name: "CyclicConstantTwistDescent",
	Key:  "prop_f21c390ed4c66584",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), permutation_order(s))"},
			{Name: "composite", Text: "constant_composite(M, L, «constants»)"},
			{Name: "twisted", Text: "constant_twist_field(M, k, L, s)"},
		},
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A. ∀s:permutation(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, field_adjoin(M, k, {t}), L)",
			"s ∈ field_automorphisms(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "permutation_order(constant_twist_automorphism(M, k, L, s)) = permutation_order(s) ∧ " +
			"regular_function_field(M, k, «twisted») ∧ " +
			"finite_extension(M, field_adjoin(M, k, {t}), «twisted») ∧ " +
			"extension_degree(M, field_adjoin(M, k, {t}), «twisted») = " +
			"card(field_automorphisms(M, field_adjoin(M, k, {t}), L)) ∧ " +
			"constant_composite(M, «twisted», «constants») = «composite» ∧ " +
			"permutation_map(constant_frobenius_lift(M, k, L, s), t) = t",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			k, L *Expr[Set[A]],
			t *Expr[A],
			s *Expr[Permutation[A]],
			closed, regular, finiteK, tIn, transcendental, galois, sIn Fact,
		) {
			m := a.TermAs[FieldOps[A]]("M")
			e := a.TermAs[Nat]("permutation_order(s)")
			constants := a.TermAs[Set[A]]("«constants»")
			composite := a.TermAs[Set[A]]("«composite»")
			twisted := a.TermAs[Set[A]]("«twisted»")
			base := a.TermAs[Set[A]]("field_adjoin(M, k, {t})")
			sum := a.TermAs[Set[A]]("field_adjoin(M, «twisted», «constants»)")
			setting := readTwistSetting(a, M, k, L, t, s, regular, tIn, galois, sIn)
			data := readConstantComposite(a, M, L, k, e, setting.positive, closed, regular, finiteK)
			constantsDegree := a.Have(
				"l has degree e over k",
				"extension_degree(M, k, «constants») = permutation_order(s)",
				By(
					closed,
					data.subK,
					finiteK,
					setting.positive,
					finite_field.FiniteConstantsAutomorphisms.Read(M).At(k, e)))
			compositeDegree := a.Have(
				"N has degree e over L",
				"finite_extension(M, L, «composite») ∧ extension_degree(M, L, «composite») = permutation_order(s)",
				Simp(Fwd(constant_composite.ConstantCompositeDef)),
				By(
					constantsDegree,
					data.subK,
					data.subL,
					data.subC,
					data.kInL,
					data.kInC,
					data.finiteC,
					setting.regularity,
					data.exact,
					constant_composite.ConstantExtensionDegree.Read(M).At(k, L, constants)))
			fieldData := a.Have(
				"L_s is a subfield over k(t) inside N, of index e",
				"subfield(M, «twisted») ∧ "+
					"field_adjoin(M, k, {t}) ⊆ «twisted» ∧ "+
					"«twisted» ⊆ «composite» ∧ "+
					"finite_extension(M, «twisted», «composite») ∧ "+
					"extension_degree(M, «twisted», «composite») = permutation_order(s) ∧ "+
					"permutation_order(constant_twist_automorphism(M, k, L, s)) = permutation_order(s)",
				By(
					closed,
					regular,
					finiteK,
					tIn,
					transcendental,
					galois,
					sIn,
					ConstantTwistFieldData.Read(M).At(k, L, t, s)))
			fieldParts := a.Conjuncts(
				fieldData,
				"L_s is a subfield",
				"it holds k(t)",
				"it lies in N",
				"N is finite over it",
				"of degree e",
				"φ has order e")
			subT, baseInT, tInN, finiteN, indexT, orderOfTwist :=
				fieldParts[0], fieldParts[1], fieldParts[2], fieldParts[3], fieldParts[4], fieldParts[5]
			kInT := a.Have(
				"k lies in L_s",
				"k ⊆ «twisted»",
				BySets(setting.tower, baseInT))
			groupCount := a.Have(
				"L has degree |G| over k(t)",
				"extension_degree(M, field_adjoin(M, k, {t}), L) = "+
					"card(field_automorphisms(M, field_adjoin(M, k, {t}), L))",
				By(
					setting.tower,
					data.subL,
					setting.finite,
					galois,
					galois_correspondence.GaloisIffCard.Read(M).At(base, L)))
			throughL := a.Have(
				"N has degree |G|·e over k(t)",
				"finite_extension(M, field_adjoin(M, k, {t}), «composite») ∧ "+
					"extension_degree(M, field_adjoin(M, k, {t}), «composite») = "+
					"extension_degree(M, field_adjoin(M, k, {t}), L) * extension_degree(M, L, «composite»)",
				By(
					setting.tower,
					data.subL,
					data.subN,
					data.LInN,
					setting.finite,
					compositeDegree,
					field_extension.TowerLaw.Read(M).At(base, L, composite)))
			finiteT := a.Have(
				"so L_s is finite over k(t)",
				"finite_extension(M, field_adjoin(M, k, {t}), «twisted»)",
				By(
					setting.tower,
					subT,
					data.subN,
					baseInT,
					tInN,
					throughL,
					field_extension.TowerFinite.Read(M).At(base, twisted, composite)))
			throughT := a.Have(
				"and N has degree [L_s : k(t)]·e over k(t)",
				"extension_degree(M, field_adjoin(M, k, {t}), «composite») = "+
					"extension_degree(M, field_adjoin(M, k, {t}), «twisted») * "+
					"extension_degree(M, «twisted», «composite»)",
				By(
					setting.tower,
					subT,
					data.subN,
					baseInT,
					tInN,
					finiteT,
					finiteN,
					field_extension.TowerLaw.Read(M).At(base, twisted, composite)))
			degreeT := a.Have(
				"so [L_s : k(t)] = |G|",
				"extension_degree(M, field_adjoin(M, k, {t}), «twisted») = "+
					"card(field_automorphisms(M, field_adjoin(M, k, {t}), L))",
				ByArith(
					setting.positive,
					groupCount,
					throughL,
					throughT,
					compositeDegree,
					indexT,
					nat_arith.MulEqLCancel.At(
						e,
						a.TermAs[Nat]("extension_degree(M, field_adjoin(M, k, {t}), «twisted»)"),
						a.TermAs[Nat]("card(field_automorphisms(M, field_adjoin(M, k, {t}), L))")),
					nat_arith.MulSym.At(e, a.TermAs[Nat]("extension_degree(M, field_adjoin(M, k, {t}), «twisted»)")),
					nat_arith.MulSym.At(e, a.TermAs[Nat]("card(field_automorphisms(M, field_adjoin(M, k, {t}), L))"))))
			exactT := a.Have(
				"the constants of L_s are k",
				"∀x:A. x ∈ «twisted» ∧ algebraic_over(M, k, x) ⇒ x ∈ k",
				By(
					M,
					closed,
					regular,
					finiteK,
					tIn,
					transcendental,
					galois,
					sIn,
					At(TwistedFieldConstants, m, k, L, t, s)))
			exactSet := a.Have(
				"so the elements of L_s algebraic over k are k",
				"{x:A | x ∈ «twisted» ∧ algebraic_over(M, k, x)} = k",
				BySets(kInT, exactT, data.subK, algebraic_element.MemberAlgebraic.Read(M)))
			tInT := a.Have(
				"t lies in L_s",
				"t ∈ «twisted»",
				BySets(setting.tower, baseInT))
			regularT := a.Have(
				"L_s is regular over k",
				"regular_function_field(M, k, «twisted»)",
				By(
					exactSet,
					data.subK,
					subT,
					finiteK,
					kInT,
					tInT,
					transcendental,
					finiteT,
					function_field.ExactConstantFieldFinite.Read(M).At(k, twisted, t)))
			compositeSum := a.Have(
				"L_s·l has degree e over L_s",
				"finite_extension(M, «twisted», field_adjoin(M, «twisted», «constants»)) ∧ "+
					"extension_degree(M, «twisted», field_adjoin(M, «twisted», «constants»)) = permutation_order(s)",
				By(
					constantsDegree,
					data.subK,
					subT,
					data.subC,
					kInT,
					data.kInC,
					data.finiteC,
					setting.regularity,
					exactT,
					constant_composite.ConstantExtensionDegree.Read(M).At(k, twisted, constants)))
			carriers := a.Have(
				"L_s and l lie in M",
				"«twisted» ⊆ M.carrier ∧ «constants» ⊆ M.carrier",
				By(subT, data.subC, field.SubfieldSubset.At(m, twisted), field.SubfieldSubset.At(m, constants)))
			sumData := a.Have(
				"L_s·l is a subfield between L_s and N",
				"subfield(M, field_adjoin(M, «twisted», «constants»)) ∧ "+
					"«twisted» ⊆ field_adjoin(M, «twisted», «constants»)",
				By(carriers, algebraic_element.AdjoinSubfield.Read(M).At(twisted, constants)))
			sumInN := a.Have(
				"L_s·l lies in N",
				"field_adjoin(M, «twisted», «constants») ⊆ «composite»",
				By(
					data.subN,
					tInN,
					data.cInN,
					algebraic_element.AdjoinLeast.Read(M).At(twisted, constants, composite)))
			compositeEqual := a.Have(
				"so L_s·l is N",
				"field_adjoin(M, «twisted», «constants») = «composite»",
				By(
					subT,
					data.subN,
					sumData,
					sumInN,
					finiteN,
					indexT,
					compositeSum,
					field_extension.IntermediateDegree.Read(M).At(twisted, sum, composite)))
			frobeniusFixes := a.Have(
				"the Frobenius lift fixes L",
				"∀x:A. x ∈ L ⇒ permutation_map(constant_frobenius_lift(M, k, L, s), x) = x",
				Derive(func(b *Argument) {
					inAut := b.Have(
						"it is an automorphism of N over L",
						"constant_frobenius_lift(M, k, L, s) ∈ field_automorphisms(M, L, «composite»)",
						By(
							closed,
							regular,
							finiteK,
							tIn,
							transcendental,
							galois,
							sIn,
							ConstantTwistActs.Read(M).At(k, L, t, s)))
					b.Show(
						"among the conditions",
						BySets(b.Unfolded(inAut, field_automorphism.FieldAutomorphismsDef)))
				}))
			a.Show(
				"φ has order e, L_s is regular over k of degree |G| "+
					"over k(t), L_s·l is N, and the Frobenius lift fixes t",
				SplitConjAll(
					Case(
						"φ has order e",
						By(orderOfTwist)),
					Case(
						"L_s is regular over k",
						By(regularT)),
					Case(
						"L_s is finite over k(t)",
						By(finiteT)),
					Case(
						"of degree |G|",
						By(degreeT)),
					Case(
						"L_s·l is N",
						Simp(Fwd(constant_composite.ConstantCompositeDef)),
						By(compositeEqual, constant_composite.ConstantCompositeDef)),
					Case(
						"the Frobenius lift fixes t",
						By(tIn, frobeniusFixes.At(t)))))
		}),
})}
