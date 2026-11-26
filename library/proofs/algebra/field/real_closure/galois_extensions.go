package real_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/finite_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/finite_group/sylow"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// OddDegreeExtensionTrivial — If every odd-degree polynomial over K has a root
// in K, each finite extension of K of odd degree is K: each simple
// subextension has odd degree, so its irreducible minimal polynomial has a root
// and is linear.
var OddDegreeExtensionTrivial = oddDegreeExtensionTrivialThm{family.Add(registry.ProofEntry{
	Name: "OddDegreeExtensionTrivial",
	Key:  "prop_3d562e61b27c16d1",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_ops(A). ∀K E:set(A).",
		Hypotheses: []string{
			"field_on(M)",
			"subfield(M, K)",
			"subfield(M, E)",
			"K ⊆ E",
			"finite_extension(M, K, E)",
			"nat_odd(extension_degree(M, K, E))",
			"odd_degree_roots(restrict_field(M, K))",
		},
		Conclusion: "E = K",
	}, func(
		a *Argument,
		M *Expr[FieldOps[A]],
		K, E *Expr[Set[A]],
		fieldM field.FieldFact[on.M],
		subfieldK, subfieldE, contains, finite, odd, roots Fact,
	) {
		rootsInK := a.Simplified(
			roots,
			Fwd(polynomial_evaluation.OddDegreeRootsDef),
			Fwd(field.RestrictFieldDef))
		allIn := a.Have(
			"Every element of E lies in K",
			"∀x:A. x ∈ E ⇒ x ∈ K",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xE := b.Assume()
				xIn := b.Have(
					"The element lies in the ambient field",
					"x ∈ M.carrier",
					BySets(xE, subfieldE, field.SubfieldSubset.At(M, E)))
				xm := b.MemberOf[on.M](x, xIn)
				algebraic := b.Have(
					"Finite extensions are algebraic",
					"algebraic_over(M, K, x)",
					By(
						xE,
						subfieldE,
						subfieldK,
						contains,
						finite,
						algebraic_element.FiniteExtensionAlgebraic.Read(fieldM).At(K, E, x)))
				p, pDef := b.LetAs[Fun[Nat, A]]("p", "minimal_polynomial(M, K, x)")
				divides := b.Have(
					"The minimal-polynomial degree divides the extension degree",
					"polynomial_degree(p) ∣ extension_degree(M, K, E)",
					By(
						Normalized,
						pDef,
						subfieldK,
						subfieldE,
						contains,
						finite,
						xE,
						algebraic_element.MinimalPolynomialDegreeDivides.Read(fieldM).At(K, E, x)))
				degree := b.TermAs[Nat]("polynomial_degree(p)")
				c, factored := b.ObtainAs[Nat](
					"So the extension degree is the minimal-polynomial degree times a cofactor c",
					"∃c:num. extension_degree(M, K, E) = polynomial_degree(p) * c",
					By(divides, nat_divides.DividesFactor.At(degree, b.TermAs[Nat]("extension_degree(M, K, E)"))))
				oddDegree := b.Have(
					"A factor of an odd degree is odd",
					"nat_odd(polynomial_degree(p))",
					By(
						Normalized,
						odd,
						factored,
						nat_parity.EvenMul.At(degree, c),
						nat_parity.OddIffNotEven.At(b.TermAs[Nat]("extension_degree(M, K, E)")),
						nat_parity.OddIffNotEven.At(degree)))
				polynomialData := b.Have(
					"The minimal polynomial is irreducible over K",
					"field_on(restrict_field(M, K)) ∧ "+
						"polynomial_over(K, p) ∧ "+
						"polynomial_irreducible(field_ring(restrict_field(M, K)), p)",
					By(
						Normalized,
						pDef,
						subfieldK,
						algebraic,
						algebraic_element.MinimalPolynomialSpec.Read(fieldM).At(K, xm),
						algebraic_element.MinimalPolynomialIrreducible.Read(fieldM).At(K, xm),
						field.SubfieldFieldOn.Read(fieldM).At(K),
						field.RestrictFieldRing.At(M, K)))
				oddShape := b.Have(
					"The degree has the odd form used by the root hypothesis",
					"∃j:num. polynomial_degree(p) = 2 * j + 1",
					By(oddDegree, nat_parity.OddIffSucDouble.At(b.TermAs[Nat]("polynomial_degree(p)")), nat_arith.Add1))
				y, yRoot := b.ObtainAs[A](
					"Choose a root of the minimal polynomial in K",
					"∃y:A. y ∈ K ∧ polynomial_eval(p, y) = M.zero",
					By(rootsInK.At(p), oddShape, polynomialData))
				fieldK := b.Conjuncts(
					polynomialData,
					"K is a field in its own right",
					"The minimal polynomial is over K",
					"The minimal polynomial is irreducible")[0]
				rootData := b.Conjuncts(
					yRoot,
					"The root lies in K",
					"The minimal polynomial vanishes at the root")
				ym := b.MemberOf[on.Any](y, rootData[0])
				linearDegree := b.Have(
					"An irreducible polynomial with a field root is linear",
					"polynomial_degree(p) = 1",
					By(
						rootData[1],
						polynomialData,
						polynomial_roots.IrreducibleRootLinear.Read(integral_domain.FieldIntegralDomain.Read(fieldK)).At(
							p, ym)))
				b.Show(
					"An element whose minimal polynomial is linear belongs to K",
					By(
						Normalized,
						pDef,
						linearDegree,
						subfieldK,
						algebraic,
						algebraic_element.MinimalPolynomialLinearIff.Read(fieldM).At(K, xm)))
			}))
		a.Show(
			"The two subfields are equal",
			BySets(allIn, contains))
	}),
})}

// FiniteGaloisImaginaryAdjoin — A finite Galois extension of a Euclidean
// subfield over which every odd-degree polynomial has a root, containing a
// square root of minus one, is generated by that root. The Galois group has
// the degree as its order, and N has the order of a subgroup as its degree
// over the subgroup's fixed field (ArtinFixedField). The fixed field of a
// subgroup of order 2 ^ s, the whole power of 2 in the degree, has odd degree
// over K, so it is K (OddDegreeExtensionTrivial), and the degree is 2 ^ s. The
// automorphisms fixing K(i) then form a group whose order divides 2 ^ s; were
// that order more than 1, the group would have a subgroup of index 2
// (PGroupIndexPrime), whose fixed field would be a quadratic extension of K(i),
// which is square-closed (ImaginaryAdjoinSquareClosed) and so has none
// (SquareClosedNoQuadraticExtension).
var FiniteGaloisImaginaryAdjoin = finiteGaloisImaginaryAdjoinThm{family.Add(registry.ProofEntry{
	Name: "FiniteGaloisImaginaryAdjoin",
	Key:  "prop_64e36485c68bba5b",
	Build: family.Sections(Statement{
		Binders: "∀M:field_ops(A). ∀K N:set(A). ∀lt:(A → A → bool). ∀i:A.",
		Hypotheses: []string{
			"field_on(M)",
			"subfield(M, K)",
			"subfield(M, N)",
			"K ⊆ N",
			"galois_over(M, K, N)",
			"euclidean_field(restrict_field(M, K), lt)",
			"odd_degree_roots(restrict_field(M, K))",
			"i ∈ N",
			"i * i = -M.one",
		},
		Conclusion: "N = «C»",
		Abbrev: Abbrev{
			{Name: "C", Text: "field_adjoin(M, K, {i})"},
			{Name: "H", Text: "field_automorphisms(M, «C», N)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		galoisGroup := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K N:set(A).",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"subfield(M, N)",
				"K ⊆ N",
				"galois_over(M, K, N)",
			},
			Conclusion: "finite_extension(M, K, N) ∧ " +
				"group_on(galois_group(M, K, N)) ∧ " +
				"galois_group(M, K, N).carrier = field_automorphisms(M, K, N) ∧ " +
				"finite(field_automorphisms(M, K, N)) ∧ " +
				"card(field_automorphisms(M, K, N)) = extension_degree(M, K, N) ∧ " +
				"0 < extension_degree(M, K, N)",
		}, func(a *Argument, M *Expr[FieldOps[A]], K, N *Expr[Set[A]],
			fieldM field.FieldFact[on.M], subK, subN, contains, galois Fact) {
			finite := a.Have(
				"A Galois extension is finite",
				"finite_extension(M, K, N)",
				By(galois, galois_correspondence.GaloisOverDef.At(M, K, N)))
			count := a.Have(
				"The finite automorphism group has the positive extension degree",
				"finite(field_automorphisms(M, K, N)) ∧ "+
					"card(field_automorphisms(M, K, N)) = extension_degree(M, K, N) ∧ "+
					"0 < extension_degree(M, K, N)",
				By(
					fieldM,
					subK,
					subN,
					contains,
					finite,
					galois,
					field_automorphism.AutomorphismsBound.Read(fieldM).At(K, N),
					galois_correspondence.GaloisIffCard.Read(fieldM).At(K, N),
					field_extension.ExtensionDegreePositive.Read(fieldM).At(K, N)))
			a.Show(
				"The Galois group is a finite group whose order is the degree",
				By(finite, count, field_automorphism.GaloisGroupOn.Read(fieldM).At(K, N)))
		})

		fixedFieldTower := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K N:set(A). ∀H:set(permutation(A)).",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"subfield(M, N)",
				"K ⊆ N",
				"finite_extension(M, K, N)",
				"subgroup(galois_group(M, K, N), H)",
			},
			Conclusion: "subfield(M, fixed_field(N, H)) ∧ " +
				"K ⊆ fixed_field(N, H) ∧ " +
				"fixed_field(N, H) ⊆ N ∧ " +
				"finite_extension(M, K, fixed_field(N, H)) ∧ " +
				"finite_extension(M, fixed_field(N, H), N) ∧ " +
				"extension_degree(M, fixed_field(N, H), N) = card(H) ∧ " +
				"extension_degree(M, K, N) = extension_degree(M, K, fixed_field(N, H)) * card(H)",
		}, func(a *Argument, M *Expr[FieldOps[A]], K, N *Expr[Set[A]],
			H *Expr[Set[field_automorphism.Permutation[A]]], fieldM field.FieldFact[on.M],
			subK, subN, contains, finite, subgroupG Fact) {
			aut := a.TermAs[Set[field_automorphism.Permutation[A]]]("field_automorphisms(M, K, N)")
			F := a.TermAs[Set[A]]("fixed_field(N, H)")
			opened := a.Conjuncts(
				a.Have(
					"A subgroup of the Galois group is a group of permutations made of automorphisms fixing K",
					"subgroup(permutation_group, H) ∧ H ⊆ field_automorphisms(M, K, N)",
					By(subgroupG, field_automorphism.GaloisGroupSubgroup.At(M, K, N, H))),
				"The subgroup is a group of permutations",
				"The subgroup consists of automorphisms fixing K")
			subgroupH, fixesK := opened[0], opened[1]
			finiteH := a.Have(
				"A subgroup of the finite automorphism group is finite",
				"finite(H)",
				By(
					fieldM,
					subK,
					subN,
					contains,
					finite,
					fixesK,
					field_automorphism.AutomorphismsBound.Read(fieldM).At(K, N),
					finite_set.FiniteSubset.At(H, aut)))
			ambient := a.Have(
				"Forgetting the fixed base preserves field automorphisms",
				"H ⊆ field_automorphisms(M, ∅, N)",
				BySets(
					fieldM,
					fixesK,
					field_automorphism.AutomorphismsAntitone.Read(fieldM).At(a.TermAs[Set[A]]("∅"), K, N)))
			intermediate := a.Have(
				"By the Galois correspondence the fixed field F of H is a subfield lying between K and N",
				"subfield(M, fixed_field(N, H)) ∧ K ⊆ fixed_field(N, H) ∧ fixed_field(N, H) ⊆ N",
				By(
					subK,
					subN,
					contains,
					finite,
					subgroupG,
					galois_correspondence.CorrespondenceAutomorphisms.Read(fieldM).At(K, N, H)))
			artin := a.Have(
				"Artin: N is finite over F, of degree the order of H",
				"finite_extension(M, fixed_field(N, H), N) ∧ extension_degree(M, fixed_field(N, H), N) = card(H)",
				By(
					fieldM,
					finiteH,
					subN,
					subgroupH,
					ambient,
					field_automorphism.ArtinFixedField.Read(fieldM).At(N, H)))
			finiteTower := a.Have(
				"Both parts of the intermediate tower are finite",
				"finite_extension(M, K, fixed_field(N, H)) ∧ finite_extension(M, fixed_field(N, H), N)",
				By(fieldM, subK, subN, intermediate, finite, field_extension.TowerFinite.Read(fieldM).At(K, F, N)))
			a.Show(
				"The tower law gives the fixed-field degree factorization",
				By(
					Normalized,
					fieldM,
					subK,
					subN,
					intermediate,
					finiteTower,
					artin,
					field_extension.TowerLaw.Read(fieldM).At(K, F, N)))
		})

		galoisDegreePower := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K N:set(A).",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"subfield(M, N)",
				"K ⊆ N",
				"galois_over(M, K, N)",
				"odd_degree_roots(restrict_field(M, K))",
			},
			Conclusion: "∃s:num. extension_degree(M, K, N) = 2 ^ s",
		}, func(a *Argument, M *Expr[FieldOps[A]], K, N *Expr[Set[A]],
			fieldM field.FieldFact[on.M], subK, subN, contains, galois, roots Fact) {
			G := a.TermAs[group.GroupOps[field_automorphism.Permutation[A]]]("galois_group(M, K, N)")
			two, degree := a.TermAs[Nat]("2"), a.TermAs[Nat]("extension_degree(M, K, N)")
			groupG := a.Simplified(
				GroupPremises(fieldM, subK, subN, contains, galois, At(galoisGroup, M, K, N)))
			s, sDef := a.LetAs[Nat]("s", "nat_multiplicity(2, extension_degree(M, K, N))")
			c, factored := a.ObtainAs[Nat](
				"The degree is 2 ^ s, the whole power of 2 in it, times a cofactor c that 2 does not divide",
				"∃c:num. extension_degree(M, K, N) = 2 ^ s * c ∧ ¬(2 ∣ c)",
				By(
					Normalized,
					groupG,
					sDef,
					nat_order.LessEqRefl.At(two),
					nat_order.PosIffNonzero.At(degree),
					nat_multiplicity.MultiplicityCofactor.At(two, degree)))
			factors := a.Conjuncts(
				factored,
				"The degree is 2 ^ s * c",
				"2 does not divide c")
			factor, indivisible := factors[0], factors[1]
			power := a.TermAs[Nat]("2 ^ s")
			divides := a.Have(
				"The full two-primary factor divides the group order",
				"2 ^ s ∣ card(galois_group(M, K, N).carrier)",
				By(Normalized, factor, groupG, nat_divides.DividesOwnMultiple.At(power, c)))
			P, twoPower := a.ObtainAs[Set[field_automorphism.Permutation[A]]](
				"Choose a subgroup of order 2 ^ s, the whole power of 2 in the order",
				"∃P:set(permutation(A)). subgroup(galois_group(M, K, N), P) ∧ card(P) = 2 ^ s",
				By(divides, groupG, nat_prime.PrimeTwo, sylow.PrimePowerOrderSubgroup.At(G, two, s)))
			F := a.TermAs[Set[A]]("fixed_field(N, P)")
			fixedDegree := a.TermAs[Nat]("extension_degree(M, K, fixed_field(N, P))")
			tower := a.Simplified(
				GroupPremises(
					fieldM,
					subK,
					subN,
					contains,
					groupG,
					twoPower,
					At(fixedFieldTower, M, K, N, P)))
			cofactor := a.Have(
				"Cancelling 2 ^ s = card(P) in the tower, the fixed field has degree c over K",
				"extension_degree(M, K, fixed_field(N, P)) = c",
				By(
					factor,
					twoPower,
					tower,
					nat_arith.MulSym,
					nat_arith.MulEqLCancel.At(power, fixedDegree, c),
					nat_arith.PowTwoNonzero.At(s)))
			odd := a.Have(
				"That degree is odd, as 2 does not divide c",
				"nat_odd(extension_degree(M, K, fixed_field(N, P)))",
				By(
					Normalized,
					cofactor,
					indivisible,
					nat_parity.OddIffNotEven.At(c),
					nat_parity.EvenIffModTwoZero.At(c),
					nat_divides.DividesMod.At(two, c)))
			equal := a.Have(
				"The odd fixed-field extension is trivial",
				"fixed_field(N, P) = K",
				By(fieldM, subK, tower, odd, roots, OddDegreeExtensionTrivial.At(M, K, F)))
			a.Take(s)
			a.Show(
				"With the fixed field K, the degree is the order 2 ^ s of P",
				By(Normalized, equal, twoPower, tower))
		})

		squareClosedTrivial := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K N:set(A). ∀s:num.",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"subfield(M, N)",
				"K ⊆ N",
				"galois_over(M, K, N)",
				"M.one + M.one ≠ M.zero",
				"square_closed(M, K)",
				"card(field_automorphisms(M, K, N)) ∣ 2 ^ s",
			},
			Conclusion: "N = K",
		}, func(a *Argument, M *Expr[FieldOps[A]], K, N *Expr[Set[A]], s *Expr[Nat],
			fieldM field.FieldFact[on.M],
			subK, subN, contains, galois, twoNonzero, squares, divides Fact) {
			G := a.TermAs[group.GroupOps[field_automorphism.Permutation[A]]]("galois_group(M, K, N)")
			two := a.TermAs[Nat]("2")
			groupG := a.Simplified(
				GroupPremises(fieldM, subK, subN, contains, galois, At(galoisGroup, M, K, N)))
			notOne := a.Unless(
				a.TermAs[Bool]("card(field_automorphisms(M, K, N)) = 1"),
				"A unit automorphism group gives a degree-one extension",
				Given(func(b *Argument, one Fact) {
					b.Show(
						"Degree one identifies the two subfields",
						By(
							Normalized,
							fieldM,
							subK,
							subN,
							contains,
							groupG,
							one,
							field_extension.DegreeOneIff.Read(fieldM).At(K, N)))
				}))
			nontrivial := a.Have(
				"The positive nonunit order exceeds one",
				"1 < card(galois_group(M, K, N).carrier)",
				ByArith(groupG, notOne))
			U, indexTwo := a.ObtainAs[Set[field_automorphism.Permutation[A]]](
				"Choose a subgroup of index two",
				"∃U:set(permutation(A)). "+
					"    subgroup(galois_group(M, K, N), U) ∧ card(field_automorphisms(M, K, N)) = 2 * card(U)",
				By(
					nontrivial,
					divides,
					groupG,
					nat_prime.PrimeTwo,
					sylow.PGroupOfOrderDividing.At(G, two, s),
					sylow.PGroupIndexPrime.At(G, two)))
			F := a.TermAs[Set[A]]("fixed_field(N, U)")
			order := a.TermAs[Nat]("card(U)")
			fixedDegree := a.TermAs[Nat]("extension_degree(M, K, fixed_field(N, U))")
			tower := a.Simplified(
				GroupPremises(
					fieldM,
					subK,
					subN,
					contains,
					groupG,
					indexTwo,
					At(fixedFieldTower, M, K, N, U)))
			positive := a.Have(
				"The subgroup order is a positive fixed-field extension degree",
				"0 < card(U)",
				By(Normalized, fieldM, subN, tower, field_extension.ExtensionDegreePositive.Read(fieldM).At(F, N)))
			quadratic := a.Have(
				"The index-two fixed field has degree two over K",
				"extension_degree(M, K, fixed_field(N, U)) = 2",
				By(
					positive,
					indexTwo,
					groupG,
					tower,
					nat_arith.MulSym,
					nat_arith.MulEqLCancel.At(order, fixedDegree, two),
					nat_order.PosIffNonzero.At(order)))
			a.Show(
				"Square closure rules out this quadratic extension",
				By(
					fieldM,
					subK,
					tower,
					quadratic,
					twoNonzero,
					squares,
					algebraic_element.SquareClosedNoQuadraticExtension.At(M, K, F)))
		})

		return ctx.Theorem(headline,
			func(a *Argument, M *Expr[FieldOps[A]], K, N *Expr[Set[A]], lt *Arrow2[A, A, Bool],
				i *Expr[A], fieldM field.FieldFact[on.M], subK, subN, contains, galois,
				euclidean, oddRoots, iIn, iSquared Fact) {
				C := a.TermAs[Set[A]]("«C»")
				G := a.TermAs[group.GroupOps[field_automorphism.Permutation[A]]]("galois_group(M, K, N)")
				H := a.TermAs[Set[field_automorphism.Permutation[A]]]("«H»")

				ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
				between := a.Have(
					"The imaginary adjunction lies between K and N",
					"subfield(M, «C») ∧ K ⊆ «C» ∧ i ∈ «C» ∧ «C» ⊆ N",
					By(
						fieldM,
						subK,
						subN,
						contains,
						iIn,
						algebraic_element.AdjoinElementBetween.Read(fieldM).At(K, N, i)))
				ambientI := a.Have(
					"The imaginary generator lies in the ambient field",
					"i ∈ M.carrier",
					BySets(subN, iIn, field.SubfieldSubset.At(M, N)))
				squares := a.Have(
					"Every element of the imaginary adjunction is a square",
					"square_closed(M, «C»)",
					By(fieldM, subK, euclidean, ambientI, iSquared, ImaginaryAdjoinSquareClosed.At(M, K, lt, i)))
				twoNonzero := a.Have(
					"Two is not zero in the ordered field K, whose operations are M's",
					"M.one + M.one ≠ M.zero",
					By(ordered_field.TwoNonzero.Read(ordered)))
				s, power := a.ObtainAs[Nat](
					"The Galois degree is a power of two",
					"∃s:num. extension_degree(M, K, N) = 2 ^ s",
					By(fieldM, subK, subN, contains, galois, oddRoots, At(galoisDegreePower, M, K, N)))
				divides := a.Have(
					"Lagrange bounds the remaining automorphism order by a power of two",
					"card(«H») ∣ 2 ^ s",
					By(
						fieldM,
						subK,
						subN,
						contains,
						galois,
						power,
						between,
						field_automorphism.AutomorphismsTowerSubgroup.Read(fieldM).At(K, C, N),
						At(galoisGroup, M, K, N),
						finite_group.LagrangeDividesOn.At(G, H)))
				galoisC := a.Have(
					"The extension above the imaginary adjunction is Galois",
					"galois_over(M, «C», N)",
					By(fieldM, subK, subN, between, galois, galois_correspondence.GaloisTower.Read(fieldM).At(K, C, N)))
				a.Show(
					"The square-closed imaginary adjunction admits no remaining two-primary Galois extension",
					By(
						fieldM,
						subN,
						between,
						twoNonzero,
						squares,
						divides,
						galoisC,
						At(squareClosedTrivial, M, C, N, s)))
			})
	}),
})}
