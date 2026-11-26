package twist_quotient_bound

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/separating_parameter"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_fibres"
	"github.com/euc-ai/xugo/library/proofs/scheme/plane_model"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ExactGaloisClosure — a separating parameter, a finite Galois closure over its
// line and the exact constants of that closure: K, regular over the finite field
// k, has a separating parameter u (separating_parameter.SeparatingParameterExists);
// a finite Galois closure L of K over k(u) (separating_parameter.FiniteGaloisClosureExists);
// the exact constants of L, a finite field of q^r elements with r > 0, over which
// L is regular (function_field.ExactConstantFieldFinite); and the group of L over
// their line has a positive order, l(u) holding k(u)
// (field_automorphism.AutomorphismsOrderPositive).
var ExactGaloisClosure = exactGaloisClosureThm{family.Add(registry.ProofEntry{
	Name: "ExactGaloisClosure",
	Key:  "prop_856f6c12bb5abf2e",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "exact", Text: "λL:set(A). {x:A | x ∈ L ∧ algebraic_over(M, k, x)}"},
		},
		Binders: "∀M:field_on(A). ∀K k:set(A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
		},
		Conclusion: "∃u:A. ∃L:set(A). ∃r:num. " +
			"    u ∈ K ∧ " +
			"    ¬algebraic_over(M, k, u) ∧ " +
			"    finite_extension(M, field_adjoin(M, k, {u}), K) ∧ " +
			"    (∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {u}), x)) ∧ " +
			"    subfield(M, L) ∧ " +
			"    K ⊆ L ∧ " +
			"    galois_over(M, field_adjoin(M, k, {u}), L) ∧ " +
			"    0 < r ∧ " +
			"    finite(«exact»(L)) ∧ " +
			"    regular_function_field(M, «exact»(L), L) ∧ " +
			"    card(«exact»(L)) = card(k) ^ r ∧ " +
			"    0 < card(field_automorphisms(M, field_adjoin(M, «exact»(L), {u}), L))",
	},
		func(a *Argument, M field.FieldFact[on.M], K, k *Expr[Set[A]], closed, regular, finiteK Fact) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			regularity := function_field.RegularFunctionFieldDef.At(fieldM, k, K)
			base := a.Have(
				"k and K are subfields, k inside K",
				"subfield(M, k) ∧ subfield(M, K) ∧ k ⊆ K",
				By(regular, regularity))
			u, parameter := a.ObtainAs[A](
				"K has a separating parameter over k",
				"∃u:A. "+
					"    u ∈ K ∧ "+
					"    ¬algebraic_over(M, k, u) ∧ "+
					"    finite_extension(M, field_adjoin(M, k, {u}), K) ∧ "+
					"    (∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {u}), x))",
				By(regular, regularity, separating_parameter.SeparatingParameterExists.Read(M).At(k, K)))
			L, closure := a.ObtainAs[Set[A]](
				"K has a finite Galois closure over k(u)",
				"∃L:set(A). subfield(M, L) ∧ K ⊆ L ∧ galois_over(M, field_adjoin(M, k, {u}), L)",
				By(closed, base, parameter, separating_parameter.FiniteGaloisClosureExists.Read(M).At(k, K, u)))
			rational := a.TermAs[Set[A]]("field_adjoin(M, k, {u})")
			finiteOverRational := a.Have(
				"L is finite over k(u)",
				"finite_extension(M, field_adjoin(M, k, {u}), L)",
				By(closure, galois_correspondence.GaloisOverDef.At(fieldM, rational, L)))
			tower := a.Have(
				"k and u lie in L",
				"k ⊆ L ∧ u ∈ L",
				BySets(base, closure, parameter))
			exactFacts := a.Conjuncts(
				GroupPremises(
					base,
					closure,
					finiteK,
					tower,
					parameter,
					finiteOverRational,
					function_field.ExactConstantFieldFinite.Read(M).At(k, L, u)),
				"the exact constants are finite",
				"they are a subfield",
				"L is regular over them",
				"they have q^r points for some r > 0")
			finiteExact, subfieldExact, regularOverExact, sizedExact :=
				exactFacts[0], exactFacts[1], exactFacts[2], exactFacts[3]
			r, size := a.UnpackAs[Nat](sizedExact, "r")
			exact := a.TermAs[Set[A]]("«exact»(L)")
			between := a.Have(
				"the exact constants lie between k and L",
				"k ⊆ «exact»(L) ∧ «exact»(L) ⊆ L",
				BySets(M, base, tower, At(algebraic_element.MemberAlgebraic, fieldM, k)))
			line := a.Have(
				"l(u) is a subfield inside L, holding l and u",
				"subfield(M, field_adjoin(M, «exact»(L), {u})) ∧ "+
					"«exact»(L) ⊆ field_adjoin(M, «exact»(L), {u}) ∧ "+
					"u ∈ field_adjoin(M, «exact»(L), {u}) ∧ "+
					"field_adjoin(M, «exact»(L), {u}) ⊆ L",
				By(
					subfieldExact,
					closure,
					between,
					tower,
					algebraic_element.AdjoinElementBetween.Read(M).At(exact, L, u)))
			geometricLine := a.TermAs[Set[A]]("field_adjoin(M, «exact»(L), {u})")
			rationalInL := a.Have(
				"k(u) is a subfield inside L",
				"subfield(M, field_adjoin(M, k, {u})) ∧ field_adjoin(M, k, {u}) ⊆ L",
				By(base, closure, tower, algebraic_element.AdjoinElementBetween.Read(M).At(k, L, u)))
			rationalInLine := a.Have(
				"k(u) lies in l(u)",
				"field_adjoin(M, k, {u}) ⊆ field_adjoin(M, «exact»(L), {u})",
				By(
					base,
					line,
					between,
					set_order.SubsetTrans,
					algebraic_element.AdjoinElementBetween.Read(M).At(k, geometricLine, u)))
			positive := a.Have(
				"the group of L over l(u) has a positive order",
				"0 < card(field_automorphisms(M, field_adjoin(M, «exact»(L), {u}), L))",
				By(
					rationalInL,
					closure,
					finiteOverRational,
					rationalInLine,
					field_automorphism.AutomorphismsOrderPositive.Read(M).At(rational, geometricLine, L)))
			a.Take(u)
			a.Take(L)
			a.Take(r)
			a.Show(
				"these are the data stated",
				By(parameter, closure, size, finiteExact, regularOverExact, positive))
		}),
})}

// ExtendedConstantsData — what extending the constants to the field c of q^R
// elements does to the data of ExactGaloisClosure, for r dividing R. The exact
// constants of L lie in c (finite_field.FiniteSubfieldInConstants,
// finite_field.FiniteConstantsMono), so L·c is regular over c and Galois over c(u)
// with the group of L over l(u) (constant_composite.RegularConstantExtension,
// constant_galois.GeometricGaloisBaseChange), and K·c is regular, finite and
// separable over c(u). The subgroup of that group fixing K·l is carried by the
// isomorphism onto a subgroup H of the new group, and K·c is the fixed field of H.
var ExtendedConstantsData = extendedConstantsDataThm{family.Add(registry.ProofEntry{
	Name: "ExtendedConstantsData",
	Key:  "prop_526f66c0d3fd5156",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "exact", Text: "{x:A | x ∈ L ∧ algebraic_over(M, k, x)}"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), R)"},
			{Name: "tower", Text: "constant_composite(M, L, «constants»)"},
			{Name: "composite", Text: "constant_composite(M, K, «constants»)"},
			{Name: "line", Text: "field_adjoin(M, «constants», {u})"},
			{Name: "exactLine", Text: "field_adjoin(M, «exact», {u})"},
			{Name: "exactComposite", Text: "constant_composite(M, K, «exact»)"},
			{Name: "source", Text: "field_automorphisms(M, «exactLine», L)"},
			{Name: "target", Text: "field_automorphisms(M, «line», «tower»)"},
			{Name: "fixing", Text: "field_automorphisms(M, «exactComposite», L)"},
		},
		Binders: "∀M:field_on(A). ∀K k L:set(A). ∀u:A. ∀r R:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
			"u ∈ K",
			"¬algebraic_over(M, k, u)",
			"finite_extension(M, field_adjoin(M, k, {u}), K)",
			"∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {u}), x)",
			"subfield(M, L)",
			"K ⊆ L",
			"galois_over(M, field_adjoin(M, k, {u}), L)",
			"finite(«exact»)",
			"regular_function_field(M, «exact», L)",
			"card(«exact») = card(k) ^ r",
			"0 < R",
			"r ∣ R",
		},
		Conclusion: "subfield(M, «constants») ∧ " +
			"finite(«constants») ∧ " +
			"card(«constants») = card(k) ^ R ∧ " +
			"subfield(M, «composite») ∧ " +
			"regular_function_field(M, «constants», «composite») ∧ " +
			"regular_function_field(M, «constants», «tower») ∧ " +
			"u ∈ «composite» ∧ " +
			"u ∈ «tower» ∧ " +
			"¬algebraic_over(M, «constants», u) ∧ " +
			"galois_over(M, «line», «tower») ∧ " +
			"finite_extension(M, «line», «composite») ∧ " +
			"(∀x:A. x ∈ «composite» ⇒ separable_over(M, «line», x)) ∧ " +
			"card(«target») = card(«source») ∧ " +
			"(∃H:set(permutation(A)). " +
			"    subgroup(galois_group(M, «line», «tower»), H) ∧ «composite» = fixed_field(«tower», H))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, L *Expr[Set[A]],
			u *Expr[A],
			r, R *Expr[Nat],
			closed, regular, finiteK, uInK, transcendental, finiteOverRational, separable, inField, KInL, galois, finiteExact, regularL, exactSize, positiveR, divides Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			ring := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
			exact := a.TermAs[Set[A]]("«exact»")
			constants := a.TermAs[Set[A]]("«constants»")
			line := a.TermAs[Set[A]]("«line»")
			tower := a.TermAs[Set[A]]("«tower»")
			order := a.TermAs[Nat]("card(k)")
			compositeData := constant_galois.ConstantCompositeData.Read(M).At(K, k, R)
			data := a.Have(
				"the constants of degree R are a finite subfield above k, and K·c is a subfield holding K and c",
				"subfield(M, k) ∧ "+
					"subfield(M, K) ∧ "+
					"k ⊆ K ∧ "+
					"subfield(M, «constants») ∧ "+
					"k ⊆ «constants» ∧ "+
					"finite(«constants») ∧ "+
					"finite_extension(M, k, «constants») ∧ "+
					"subfield(M, «composite») ∧ "+
					"K ⊆ «composite» ∧ "+
					"«constants» ⊆ «composite»",
				By(closed, regular, finiteK, positiveR, compositeData))
			size := a.Have(
				"c has q^R points",
				"card(«constants») = card(k) ^ R",
				By(
					closed,
					data,
					finiteK,
					positiveR,
					finite_field.FiniteConstantsSubfield.Read(M).At(k, R),
					cardinality.HasSizeDef))
			geometric := a.Conjuncts(
				a.Have(
					"the Galois data of L pass to L·c over c(u)",
					"galois_over(M, «line», «tower») ∧ "+
						"extension_degree(M, «line», «tower») = card(«source») ∧ "+
						"(∃rho:(permutation(A) → permutation(A)). "+
						"    group_isomorphism(galois_group(M, «exactLine», L), galois_group(M, «line», «tower»), rho) ∧ "+
						"    fixed_field(«tower», image(rho, «fixing»)) = «composite»)",
					By(
						closed,
						data,
						finiteK,
						inField,
						KInL,
						uInK,
						transcendental,
						galois,
						exactSize,
						positiveR,
						divides,
						constant_galois.GeometricGaloisBaseChange.Read(M).At(k, exact, K, L, u, r, R))),
				"L·c is Galois over c(u)",
				"its degree there is the order of the group of L over l(u)",
				"an isomorphism of the groups has the fixed field K·c")
			galoisTower, degree, isomorphic := geometric[0], geometric[1], geometric[2]
			rho, isomorphism := a.UnpackAs[Fun[Permutation[A], Permutation[A]]](isomorphic, "rho")
			exactSubfield := a.Have(
				"the exact constants are a subfield",
				"subfield(M, «exact»)",
				By(regularL, function_field.RegularFunctionFieldDef.At(fieldM, exact, L)))
			inFrobenius := a.Have(
				"the exact constants are fixed by the q^r-th power",
				"«exact» ⊆ finite_constants(field_ring(M), card(k), r)",
				By(
					exactSubfield,
					finiteExact,
					exactSize,
					finite_field.FiniteSubfieldInConstants.Read(M).At(exact, order, r)))
			exactInConstants := a.Have(
				"so they lie in c, r dividing R",
				"«exact» ⊆ «constants»",
				By(
					divides,
					inFrobenius,
					field.RingOn.Read(M),
					finite_field.FiniteConstantsMono.At(ring, order, r, R),
					set_order.SubsetTrans))
			finiteOverExact := a.Have(
				"c is finite over the exact constants",
				"finite_extension(M, «exact», «constants»)",
				By(
					exactSubfield,
					data,
					exactInConstants,
					finite_field.FiniteSubfieldSize.Read(M).At(exact, constants)))
			regularTower := a.Have(
				"L·c is regular over c",
				"regular_function_field(M, «constants», «tower»)",
				By(
					regularL,
					data,
					exactInConstants,
					finiteOverExact,
					constant_composite.RegularConstantExtension.Read(M).At(exact, L, constants)))
			regularComposite := a.Have(
				"K·c is regular over c, and finite and separable over c(u)",
				"regular_function_field(M, «constants», «composite») ∧ "+
					"finite_extension(M, «line», «composite») ∧ "+
					"(∀x:A. x ∈ «composite» ⇒ separable_over(M, «line», x))",
				By(
					regular,
					data,
					uInK,
					transcendental,
					finiteOverRational,
					separable,
					constant_composite.RegularConstantExtension.Read(M).At(k, K, constants)))
			towerData := a.Have(
				"L·c is a subfield holding L and c",
				"subfield(M, «tower») ∧ L ⊆ «tower» ∧ «constants» ⊆ «tower»",
				By(inField, data, constant_composite.ConstantCompositeSubfield.Read(M).At(L, constants)))
			uInFields := a.Have(
				"u lies in K·c and in L·c",
				"u ∈ «composite» ∧ u ∈ «tower»",
				BySets(uInK, data, KInL, towerData))
			uInM := a.MemberOf[on.M](u, a.Have(
				"u lies in M",
				"u ∈ M.carrier",
				BySets(uInFields, towerData, field.SubfieldSubset.At(fieldM, tower))))
			transcendentalOverConstants := a.Have(
				"u stays transcendental over c",
				"¬algebraic_over(M, «constants», u)",
				By(data, transcendental, algebraic_element.ConstantTranscendental.Read(M).At(k, constants, uInM)))
			lineInTower := a.Have(
				"c(u) is a subfield inside L·c",
				"subfield(M, «line») ∧ «line» ⊆ «tower»",
				By(
					data,
					towerData,
					uInFields,
					algebraic_element.AdjoinElementBetween.Read(M).At(constants, tower, u)))
			finiteOverLine := a.Have(
				"L·c is finite over c(u)",
				"finite_extension(M, «line», «tower»)",
				By(galoisTower, galois_correspondence.GaloisOverDef.At(fieldM, line, tower)))
			sameOrder := a.Have(
				"the group of L·c over c(u) has its degree for order, the order of the group of L over l(u)",
				"card(«target») = card(«source»)",
				By(
					towerData,
					lineInTower,
					finiteOverLine,
					galoisTower,
					degree,
					galois_correspondence.GaloisIffCard.Read(M).At(line, tower)))
			exactCompositeField := a.TermAs[Set[A]]("«exactComposite»")
			exactComposite := a.Have(
				"K·l is a subfield holding K and l",
				"subfield(M, «exactComposite») ∧ K ⊆ «exactComposite» ∧ «exact» ⊆ «exactComposite»",
				By(data, exactSubfield, constant_composite.ConstantCompositeSubfield.Read(M).At(K, exact)))
			uInExactComposite := a.Have(
				"u lies in K·l",
				"u ∈ «exactComposite»",
				BySets(uInK, exactComposite))
			geometricLine := a.TermAs[Set[A]]("«exactLine»")
			lineInComposite := a.Have(
				"l(u) lies in K·l",
				"«exactLine» ⊆ «exactComposite»",
				By(
					exactSubfield,
					exactComposite,
					uInExactComposite,
					algebraic_element.AdjoinElementBetween.Read(M).At(exact, exactCompositeField, u)))
			sourceGroup := a.TermAs[group.GroupOps[Permutation[A]]]("galois_group(M, «exactLine», L)")
			targetGroup := a.TermAs[group.GroupOps[Permutation[A]]]("galois_group(M, «line», «tower»)")
			imageSubgroup := a.Have(
				"rho carries the subgroup fixing K·l of the group of L "+
					"over l(u) to a subgroup of the group of L·c over c(u)",
				"subgroup(galois_group(M, «line», «tower»), image(rho, «fixing»))",
				By(
					isomorphism,
					lineInComposite,
					group_homomorphism.IsomorphismHomomorphism.At(sourceGroup, targetGroup, rho),
					field_automorphism.AutomorphismsTowerSubgroup.Read(M).At(geometricLine, exactCompositeField, L),
					group_homomorphism.SubgroupImage))
			subgroupWithFixedField := a.Have(
				"K·c is the fixed field of that subgroup",
				"∃H:set(permutation(A)). "+
					"    subgroup(galois_group(M, «line», «tower»), H) ∧ «composite» = fixed_field(«tower», H)",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Set[Permutation[A]]]("image(rho, «fixing»)"))
					b.Show(
						"the isomorphism states its fixed field",
						By(imageSubgroup, isomorphism))
				}))
			a.Show(
				"these are the data stated",
				By(
					data,
					size,
					regularComposite,
					regularTower,
					uInFields,
					transcendentalOverConstants,
					galoisTower,
					sameOrder,
					subgroupWithFixedField))
		}),
})}

// SeparatingModelCoarseBound — a function field K, fixed by a subgroup H of the
// group of a Galois extension L of k(u), has a plane model over the line of its
// separating parameter u, and when q is a square the two-sided bound holds for
// it: L has a good open (galois_good_fibres.GaloisGoodFibresAreTorsors), K an
// integral plane model (plane_model.IntegralPlaneModelExists), which is a curve
// over the line (plane_model.PlaneEquationBiaffineCurve), and
// QuotientTwoSidedCoarseBound applies.
var SeparatingModelCoarseBound = separatingModelCoarseBoundThm{family.Add(registry.ProofEntry{
	Name: "SeparatingModelCoarseBound",
	Key:  "prop_430da4f6e416ecad",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "line", Text: "field_adjoin(M, k, {u})"},
		},
		Binders: "∀M:field_on(A). ∀K k L:set(A). ∀u:A. ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, K)",
			"finite(k)",
			"u ∈ K",
			"¬algebraic_over(M, k, u)",
			"finite_extension(M, «line», K)",
			"∀x:A. x ∈ K ⇒ separable_over(M, «line», x)",
			"regular_function_field(M, k, L)",
			"u ∈ L",
			"galois_over(M, «line», L)",
			"subgroup(galois_group(M, «line», L), H)",
			"K = fixed_field(L, H)",
			"∃r:num. card(k) = r * r",
		},
		Conclusion: "∃P₀ P₁ P₀₁:set(A). " +
			"    curve_over_line(restrict_field(M, K), k, u, P₀, P₁, P₀₁) ∧ " +
			"    (∃B:real. ∃m₀:num. " +
			"        real_of_num(0) ≤ B ∧ " +
			"        (∀m:num. " +
			"            0 < m ∧ m₀ ≤ m ∧ 2 * card(field_automorphisms(M, «line», L)) ∣ m - 1 ⇒ " +
			"            real_abs(real_of_num(curve_extension_count(field_ring(M), k, P₀, P₁, P₀₁, m)) - " +
			"                real_of_num(card(k) ^ m + 1)) ≤ " +
			"            B * real_sqrt(real_of_num(card(k) ^ m))))",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k, L *Expr[Set[A]],
			u *Expr[A],
			H *Expr[Set[Permutation[A]]],
			closed, regularK, finiteK, uInK, transcendental, finiteOverLine, separable, regularL, uInL, galois, isSubgroup, fixed, square Fact,
		) {
			inField := arg.Have(
				"K is a subfield",
				"subfield(M, K)",
				By(regularK, function_field.RegularFunctionFieldDef.At(arg.TermAs[FieldOps[A]]("M"), k, K)))
			C, a, goodOpen := arg.Obtain2As[Set[A], Fun[Nat, A]](
				"L has a good open over the line of u",
				"∃C:set(A). ∃a:(num → A). galois_good_open(M, k, L, u, C, a)",
				By(
					closed,
					regularL,
					finiteK,
					uInL,
					transcendental,
					galois,
					galois_good_fibres.GaloisGoodFibresAreTorsors.Read(M).At(k, L, u)))
			z, F, weight, planeModel := arg.Obtain3As[A, Fun[Nat, A], Nat](
				"K has an integral plane model over the line of u",
				"∃z:A. ∃F:(num → A). ∃b:num. integral_plane_model(restrict_field(M, K), k, u, z, F, b)",
				By(
					regularK,
					uInK,
					transcendental,
					finiteOverLine,
					separable,
					plane_model.IntegralPlaneModelExists.Read(M).At(K, k, u)))
			chartZero := arg.TermAs[Set[A]]("plane_chart_zero(restrict_ring(field_ring(M), K), k, u, z)")
			chartOne := arg.TermAs[Set[A]]("plane_chart_one(restrict_field(M, K), k, u, z, b)")
			overlap := arg.TermAs[Set[A]](
				"ring_away(restrict_ring(field_ring(M), K), " +
					"    plane_chart_zero(restrict_ring(field_ring(M), K), k, u, z), " +
					"    u)")
			curve := arg.Have(
				"the plane model is a curve over the line of u",
				"curve_over_line(restrict_field(M, K), "+
					"    k, "+
					"    u, "+
					"    plane_chart_zero(restrict_ring(field_ring(M), K), k, u, z), "+
					"    plane_chart_one(restrict_field(M, K), k, u, z, b), "+
					"    ring_away(restrict_ring(field_ring(M), K), "+
					"        plane_chart_zero(restrict_ring(field_ring(M), K), k, u, z), "+
					"        u))",
				By(inField, planeModel, plane_model.PlaneEquationBiaffineCurve.Read(M).At(K, k, u, z, F, weight)))
			arg.Take(chartZero)
			arg.Take(chartOne)
			arg.Take(overlap)
			arg.Show(
				"the quotient bound holds for it",
				By(
					closed,
					inField,
					curve,
					finiteK,
					regularK,
					goodOpen,
					isSubgroup,
					fixed,
					square,
					QuotientTwoSidedCoarseBound.Read(M).At(K, k, chartZero, chartOne, overlap, u, L, C, a, H)))
		}),
})}

// countNearComparedCount — a count within E of another keeps a square-root bound
// around Q + 1 at the cost of E√Q, since √Q ≥ 1.
var countNearComparedCount = countNearComparedCountThm{family.Add(registry.ProofEntry{
	Name: "countNearComparedCount",
	Key:  "prop_709114364c5aec70",
	Build: family.Theorem(Statement{
		Binders: "∀a b Q E:num. ∀B:real.",
		Hypotheses: []string{
			"dist((a, b)) ≤ E",
			"real_abs(real_of_num(b) - real_of_num(Q + 1)) ≤ B * real_sqrt(real_of_num(Q))",
			"0 < Q",
		},
		Conclusion: "real_abs(real_of_num(a) - real_of_num(Q + 1)) ≤ " +
			"(B + real_of_num(E)) * real_sqrt(real_of_num(Q))",
	},
		func(arg *Argument, a, b, Q, E *Expr[Nat], B *Expr[Real], near, bound, positive Fact) {
			one := arg.TermAs[Real]("real_of_num(1)")
			rootBelow := arg.Have(
				"√Q is at least one",
				"real_of_num(1) ≤ real_sqrt(real_of_num(Q))",
				ByArith(
					positive,
					real_construction.OfNumLessEq.At(arg.TermAs[Nat]("1"), Q),
					real_sqrt.SqrtLowerBound.At(one, arg.TermAs[Real]("real_of_num(Q)"))))
			sides := arg.Conjuncts(
				arg.Simplified(near, Fwd(nat_monus.DistLessEqCases)),
				"a is at most b + E",
				"b is at most a + E")
			above, below := sides[0], sides[1]
			order := arg.Have(
				"the two counts stay within E in ℝ",
				"real_of_num(a) ≤ real_of_num(b) + real_of_num(E) ∧ "+
					"real_of_num(b) ≤ real_of_num(a) + real_of_num(E)",
				ByArith(
					above,
					below,
					real_construction.OfNumLessEq.At(a, arg.TermAs[Nat]("b + E")),
					real_construction.OfNumLessEq.At(b, arg.TermAs[Nat]("a + E"))))
			scaled := arg.Have(
				"E is at most E√Q",
				"real_of_num(E) ≤ real_of_num(E) * real_sqrt(real_of_num(Q))",
				ByArith(rootBelow))
			arg.Show(
				"the error adds to the bound",
				ByArith(bound, order, scaled))
		}),
})}

// CoarseBoundAtExtendedConstants — the coarse bound at R·m for a fixed even R
// divisible by r: over the field c of q^R elements the curve K·c has square q^R
// constants and a plane model bounded by SeparatingModelCoarseBound with the data
// of ExtendedConstantsData. The extended charts of the given curve count, at m, what
// the curve counts at R·m (curve_point_count.ExtensionCountBaseChange), and stay within a
// fixed error of the plane model (curve_point_count.ExtensionCountComparison). The
// exponents are read in q by (q^R)^m = q^(R·m).
var CoarseBoundAtExtendedConstants = coarseBoundAtExtendedConstantsThm{family.Add(registry.ProofEntry{
	Name: "CoarseBoundAtExtendedConstants",
	Key:  "prop_da6557326f7dd8e6",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "exact", Text: "{x:A | x ∈ L ∧ algebraic_over(M, k, x)}"},
			{Name: "constants", Text: "finite_constants(field_ring(M), card(k), R)"},
			{Name: "tower", Text: "constant_composite(M, L, «constants»)"},
			{Name: "composite", Text: "constant_composite(M, K, «constants»)"},
			{Name: "line", Text: "field_adjoin(M, «constants», {u})"},
			{Name: "chart", Text: "λB:set(A). constant_chart(field_ring(M), «constants», B)"},
			{Name: "source", Text: "field_automorphisms(M, field_adjoin(M, «exact», {u}), L)"},
			{Name: "target", Text: "field_automorphisms(M, «line», «tower»)"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀L:set(A). ∀u:A. ∀r R:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
			"u ∈ K",
			"¬algebraic_over(M, k, u)",
			"finite_extension(M, field_adjoin(M, k, {u}), K)",
			"∀x:A. x ∈ K ⇒ separable_over(M, field_adjoin(M, k, {u}), x)",
			"subfield(M, L)",
			"K ⊆ L",
			"galois_over(M, field_adjoin(M, k, {u}), L)",
			"finite(«exact»)",
			"regular_function_field(M, «exact», L)",
			"card(«exact») = card(k) ^ r",
			"0 < R",
			"r ∣ R",
			"2 ∣ R",
		},
		Conclusion: "∃B:real. ∃m₀:num. " +
			"    real_of_num(0) ≤ B ∧ " +
			"    (∀m:num. " +
			"        0 < m ∧ m₀ ≤ m ∧ 2 * card(«source») ∣ m - 1 ⇒ " +
			"        real_abs(real_of_num(curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, R * m)) - " +
			"            real_of_num(card(k) ^ (R * m) + 1)) ≤ " +
			"        B * real_sqrt(real_of_num(card(k) ^ (R * m))))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			L *Expr[Set[A]],
			u *Expr[A],
			r, R *Expr[Nat],
			closed, subfieldK, curve, uInK, transcendental, finiteOverRational, separable, subfieldL, KInL, galois, finiteExact, regularL, exactSize, positiveR, rDividesR, twoDividesR Fact,
		) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			order := a.TermAs[Nat]("card(k)")
			constants := a.TermAs[Set[A]]("«constants»")
			tower := a.TermAs[Set[A]]("«tower»")
			composite := a.TermAs[Set[A]]("«composite»")
			regular := a.Have(
				"K is regular over k in M",
				"regular_function_field(M, k, K)",
				By(subfieldK, curve, curve_point_count.SmoothCurveRegular.Read(M).At(K, k, A0, A1, A01, t)))
			finiteConstants := a.Have(
				"the constants of a smooth curve are finite",
				"finite(k)",
				By(a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef)))
			data := a.Simplified(GroupPremises(
				closed,
				regular,
				finiteConstants,
				uInK,
				transcendental,
				finiteOverRational,
				separable,
				subfieldL,
				KInL,
				galois,
				finiteExact,
				regularL,
				exactSize,
				positiveR,
				rDividesR,
				ExtendedConstantsData.Read(M).At(K, k, L, u, r, R)))
			H, subgroupH := a.ObtainAs[Set[Permutation[A]]](
				"K·c is the fixed field of a subgroup H of the group of L·c over c(u)",
				"∃H:set(permutation(A)). "+
					"    subgroup(galois_group(M, «line», «tower»), H) ∧ «composite» = fixed_field(«tower», H)",
				By(data))
			half, even := a.ObtainAs[Nat](
				"R is even",
				"∃d:num. R = 2 * d",
				By(twoDividesR, nat_divides.DividesFactor.At(a.TermAs[Nat]("2"), R)))
			twice := a.Have(
				"R is d + d",
				"R = d + d",
				ByArith(even))
			square := a.Have(
				"so c has a square number of points",
				"∃s:num. card(«constants») = s * s",
				Derive(func(b *Argument) {
					b.Take(b.TermAs[Nat]("card(k) ^ d"))
					b.Show(
						"q^R is q^d · q^d",
						By(twice, data, nat_arith.PowAdd.At(order, half, half)))
				}))
			chart0, chart1, chart01 :=
				a.TermAs[Set[A]]("«chart»(A₀)"), a.TermAs[Set[A]]("«chart»(A₁)"), a.TermAs[Set[A]]("«chart»(A₀₁)")
			P0, P1, P01, model := a.Obtain3As[Set[A], Set[A], Set[A]](
				"K·c has a plane model over the line of u, bounded when m - 1 is a multiple of 2|G|",
				"∃P₀ P₁ P₀₁:set(A). "+
					"    curve_over_line(restrict_field(M, «composite»), «constants», u, P₀, P₁, P₀₁) ∧ "+
					"    (∃B:real. ∃m₁:num. "+
					"        real_of_num(0) ≤ B ∧ "+
					"        (∀m:num. "+
					"            0 < m ∧ m₁ ≤ m ∧ 2 * card(«target») ∣ m - 1 ⇒ "+
					"            real_abs(real_of_num( "+
					"                    curve_extension_count(field_ring(M), «constants», P₀, P₁, P₀₁, m)) - "+
					"                real_of_num(card(«constants») ^ m + 1)) ≤ "+
					"            B * real_sqrt(real_of_num(card(«constants») ^ m))))",
				By(
					closed,
					data,
					subgroupH,
					square,
					SeparatingModelCoarseBound.Read(M).At(composite, constants, tower, u, H)))
			modelParts := a.Conjuncts(
				model,
				"the plane model is a curve over the line of u",
				"it has a bound B past a threshold")
			curveP, boundedModel := modelParts[0], modelParts[1]
			bound, threshold, modelBound := a.Unpack2As[Real, Nat](boundedModel, "B", "m₁")
			bounded := a.Conjuncts(
				modelBound,
				"B is not negative",
				"the bound holds at each admissible m")
			boundSign, boundAt := bounded[0], bounded[1]
			extended := a.Have(
				"the charts extended to c are a smooth curve with function field K·c",
				"smooth_finite_curve(restrict_field(M, «composite»), "+
					"    «constants», "+
					"    t, "+
					"    «chart»(A₀), "+
					"    «chart»(A₁), "+
					"    «chart»(A₀₁))",
				By(
					closed,
					subfieldK,
					curve,
					positiveR,
					curve_point_count.SmoothCurveConstantExtension.Read(M).At(K, k, A0, A1, A01, t, R)))
			overLine := a.Have(
				"so they are a curve over the line of t",
				"curve_over_line(restrict_field(M, «composite»), "+
					"    «constants», "+
					"    t, "+
					"    «chart»(A₀), "+
					"    «chart»(A₁), "+
					"    «chart»(A₀₁))",
				By(a.Unfolded(extended, smooth_curve.SmoothFiniteFieldCurveDef)))
			gap, compared := a.ObtainAs[Nat](
				"the extended curve and the plane model count alike up to a fixed C",
				"∃C:num. ∀m:num. "+
					"    0 < m ⇒ "+
					"    dist((curve_extension_count(field_ring(M), "+
					"                «constants», "+
					"                «chart»(A₀), "+
					"                «chart»(A₁), "+
					"                «chart»(A₀₁), "+
					"                m), "+
					"            curve_extension_count(field_ring(M), «constants», P₀, P₁, P₀₁, m))) ≤ "+
					"    C",
				By(
					closed,
					data,
					overLine,
					curveP,
					curve_point_count.ExtensionCountComparison.Read(M).At(
						composite, constants, chart0, chart1, chart01, t, P0, P1, P01, u)))
			nonnegative := a.Have(
				"B + C is not negative",
				"real_of_num(0) ≤ B + real_of_num(C)",
				ByArith(boundSign))
			kSubfield := a.Have(
				"k is a subfield",
				"subfield(M, k)",
				By(regular, function_field.RegularFunctionFieldDef.At(fieldM, k, K)))
			atLeastTwo := a.Have(
				"k is a finite subfield, so it has at least two elements",
				"2 ≤ card(k)",
				By(kSubfield, finiteConstants, finite_field.FiniteSubfieldPrimePower.Read(M).At(k)))
			pointwise := a.Have(
				"at each admissible m the curve's count at R·m is near q^(R·m) + 1",
				Statement{
					Binders: "∀m:num.",
					Hypotheses: []string{
						"0 < m",
						"m₁ ≤ m",
						"2 * card(«source») ∣ m - 1",
					},
					Conclusion: "real_abs(real_of_num(curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, R * m)) - " +
						"    real_of_num(card(k) ^ (R * m) + 1)) ≤ " +
						"(B + real_of_num(C)) * real_sqrt(real_of_num(card(k) ^ (R * m)))",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]("m")
					atM := b.Conjuncts(
						b.Assume(),
						"m is positive",
						"m passes the threshold",
						"2|G| divides m - 1")
					positive, past, divides := atM[0], atM[1], atM[2]
					exponent := b.TermAs[Nat]("R * m")
					power := b.TermAs[Nat]("card(k) ^ (R * m)")
					admissible := b.Have(
						"the groups have one order, so 2|G| divides m - 1 for the new group too",
						"2 * card(«target») ∣ m - 1",
						By(divides, data))
					sameCount := b.Have(
						"the extended curve counts at m what the curve counts at R·m",
						"curve_extension_count(field_ring(M), «constants», «chart»(A₀), «chart»(A₁), «chart»(A₀₁), m) = "+
							"curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, R * m)",
						By(
							closed,
							subfieldK,
							curve,
							positiveR,
							positive,
							curve_point_count.ExtensionCountBaseChange.Read(M).At(K, k, A0, A1, A01, t, R, m)))
					samePower := b.Have(
						"(q^R)^m is q^(R·m)",
						"card(«constants») ^ m = card(k) ^ (R * m)",
						By(data, nat_arith.PowPow.At(order, R, m)))
					modelAtM := b.Have(
						"the plane model's bound at m, in powers of q",
						"real_abs(real_of_num(curve_extension_count(field_ring(M), «constants», P₀, P₁, P₀₁, m)) - "+
							"    real_of_num(card(k) ^ (R * m) + 1)) ≤ "+
							"B * real_sqrt(real_of_num(card(k) ^ (R * m)))",
						By(boundAt.At(m), positive, past, admissible, samePower))
					positivePower := b.Have(
						"q^(R·m) is positive",
						"0 < card(k) ^ (R * m)",
						ByArith(atLeastTwo, nat_order.PowPositive.At(order, exponent)))
					curveCount := b.TermAs[Nat]("curve_extension_count(field_ring(M), k, A₀, A₁, A₀₁, R * m)")
					modelCount := b.TermAs[Nat]("curve_extension_count(field_ring(M), «constants», P₀, P₁, P₀₁, m)")
					b.Show(
						"the comparison adds C to the bound",
						By(
							compared.At(m),
							positive,
							sameCount,
							modelAtM,
							positivePower,
							countNearComparedCount.At(curveCount, modelCount, power, gap, bound)))
				}))
			a.Take(a.TermAs[Real]("B + real_of_num(C)"))
			a.Take(threshold)
			a.Show(
				"B + C and the threshold of the plane model serve",
				By(nonnegative, pointwise))
		}),
})}

// AdmissibleExponent — m = 1 + h·n, for h > 0, is positive, at least n, and m - 1
// is a multiple of h.
var AdmissibleExponent = admissibleExponentThm{family.Add(registry.ProofEntry{
	Name: "AdmissibleExponent",
	Key:  "prop_8e7e754396d4870d",
	Build: family.Theorem(Statement{
		Binders:    "∀h n:num.",
		Hypotheses: []string{"0 < h"},
		Conclusion: "0 < 1 + h * n ∧ n ≤ 1 + h * n ∧ h ∣ (1 + h * n) - 1",
	},
		func(a *Argument, h, n *Expr[Nat], positive Fact) {
			shift := a.Have(
				"m - 1 is h·n",
				"(1 + h * n) - 1 = h * n",
				ByArith())
			atLeast := a.Have(
				"n is at most n·h",
				"n ≤ n * h",
				ByArith(positive, nat_order.LessEqSelfMul.At(n, h)))
			divides := a.Have(
				"so h divides m - 1",
				"h ∣ (1 + h * n) - 1",
				By(shift, nat_divides.DividesOwnMultiple.At(h, n)))
			a.Show(
				"m is positive and at least n",
				ByArith(atLeast, divides))
		}),
})}

// CoarseBoundAfterAdmissibleBaseChange — a Galois closure with its exact
// constants (ExactGaloisClosure) fixes r, their degree, and h₀ = 2·|G₀|, G₀ its
// group over the exact constants' line. For an admissible R the count at R·m is
// bounded for m past a threshold with 2|G₀| dividing m - 1
// (CoarseBoundAtExtendedConstants), and m = 1 + h₀·n is such an m once n passes
// the threshold (AdmissibleExponent).
var CoarseBoundAfterAdmissibleBaseChange = coarseBoundAfterAdmissibleBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "CoarseBoundAfterAdmissibleBaseChange",
	Key:  "prop_687756f5c7884086",
	Reading: "r and h₀ come before R, the bound B and the threshold n₀ after it: each positive " +
		"multiple R of 2r has a bound of its own, and nothing is uniform in R. So R may be chosen " +
		"once the reciprocal roots of the curve are known, as " +
		"weil_curve.CurveReciprocalRootsUpperModulus chooses it, past every collision of their powers.",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "exact", Text: "λL:set(A). {x:A | x ∈ L ∧ algebraic_over(M, k, x)}"},
		},
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"smooth_finite_curve(restrict_field(M, K), k, t, A₀, A₁, A₀₁)",
		},
		Conclusion: "∃r h₀:num. " +
			"    0 < r ∧ " +
			"    0 < h₀ ∧ " +
			"    (∀R:num. " +
			"        0 < R ∧ 2 * r ∣ R ⇒ " +
			"        ∃B:real. ∃n₀:num. " +
			"            real_of_num(0) ≤ B ∧ " +
			"            (∀n:num. " +
			"                n₀ ≤ n ⇒ " +
			"                real_abs(real_of_num(curve_extension_count(field_ring(M), " +
			"                            k, " +
			"                            A₀, " +
			"                            A₁, " +
			"                            A₀₁, " +
			"                            R * (1 + h₀ * n))) - " +
			"                    real_of_num(card(k) ^ (R * (1 + h₀ * n)) + 1)) ≤ " +
			"                B * real_sqrt(real_of_num(card(k) ^ (R * (1 + h₀ * n))))))",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			closed, inField, curve Fact,
		) {
			two := a.TermAs[Nat]("2")
			regularOverK := a.Have(
				"K is regular over k in M",
				"regular_function_field(M, k, K)",
				By(inField, curve, curve_point_count.SmoothCurveRegular.Read(M).At(K, k, A0, A1, A01, t)))
			finiteConstants := a.Have(
				"the constants of a smooth curve are finite",
				"finite(k)",
				By(a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef)))
			u, L, r, data := a.Unpack3As[A, Set[A], Nat](
				GroupPremises(closed, regularOverK, finiteConstants, ExactGaloisClosure.Read(M).At(K, k)),
				"u",
				"L",
				"r")
			h := a.TermAs[Nat]("2 * card(field_automorphisms(M, field_adjoin(M, «exact»(L), {u}), L))")
			positiveOrder := a.Have(
				"the geometric group has a positive order",
				"0 < card(field_automorphisms(M, field_adjoin(M, «exact»(L), {u}), L))",
				By(data))
			positiveH := a.Have(
				"so twice its order is positive",
				"0 < 2 * card(field_automorphisms(M, field_adjoin(M, «exact»(L), {u}), L))",
				ByArith(positiveOrder))
			a.Take(r)
			a.Take(h)
			a.Show(
				"r and twice the order of the geometric group serve",
				SplitConjAll(
					Case(
						"r is positive",
						By(data)),
					Case(
						"twice the order is positive",
						By(positiveH)),
					Case(
						"each admissible R has its bound and threshold",
						Derive(func(b *Argument) {
							R := b.FixAs[Nat]("R")
							given := b.Conjuncts(
								b.Assume(),
								"R is positive",
								"2r divides R")
							positiveR, twiceRDividesR := given[0], given[1]
							twiceR := b.TermAs[Nat]("2 * r")
							rDividesR := b.Have(
								"r divides R",
								"r ∣ R",
								By(
									twiceRDividesR,
									nat_divides.DividesOwnMultiple.At(r, two),
									nat_divides.DividesTrans.At(r, twiceR, R)))
							twoDividesR := b.Have(
								"2 divides R",
								"2 ∣ R",
								By(
									twiceRDividesR,
									nat_divides.DividesOwnMultiple.At(two, r),
									nat_divides.DividesTrans.At(two, twiceR, R)))
							bound, threshold, stated := b.Unpack2As[Real, Nat](
								GroupPremises(
									closed,
									inField,
									curve,
									data,
									positiveR,
									rDividesR,
									twoDividesR,
									CoarseBoundAtExtendedConstants.Read(M).At(K, k, A0, A1, A01, t, L, u, r, R)),
								"B",
								"m₀")
							bounded := b.Conjuncts(
								stated,
								"B is not negative",
								"the bound holds at each admissible m")
							boundSign, boundAt := bounded[0], bounded[1]
							b.Take(bound)
							b.Take(threshold)
							b.Show(
								"m = 1 + h₀ n is admissible once n passes the threshold",
								SplitConjAll(
									Case(
										"B is not negative",
										By(boundSign)),
									Case(
										"the bound along 1 + h₀ n is the bound at m",
										Derive(func(c *Argument) {
											n := c.FixAs[Nat]("n")
											past := c.Assume()
											m := c.TermAs[Nat]("1 + 2 * card(field_automorphisms(M, field_adjoin(M, «exact»(L), {u}), L)) * n")
											exponent := AdmissibleExponent.At(h, n)
											pastThreshold := c.Have(
												"m passes the threshold with n",
												"m₀ ≤ 1 + 2 * card(field_automorphisms(M, field_adjoin(M, «exact»(L), {u}), L)) * n",
												ByArith(past, positiveH, exponent))
											c.Show(
												"the bound at m is the claim",
												By(boundAt.At(m), positiveH, exponent, pastThreshold))
										}))))
						}))))
		}),
})}
