// degree_index.go — the divisor index and the classes of a degree, the effective
// counts summed over those classes, and the comparison with a constant extension
// that forces the index to one.

package curve_zeta

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_galois"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_div_rem"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_divides"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_formal_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_zpow"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/divisor_lattice_correspondence"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve_riemann_roch"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

// DivisorDegreeImage — the index is positive, and the degrees of the closed
// divisors are exactly its multiples. Those degrees form a subgroup of the
// integers, and such a subgroup is the multiples of one natural number. A closed
// point has positive degree, so that number is not zero: it is a positive
// generator, which is what the index is chosen to be.
var DivisorDegreeImage = divisorDegreeImageThm{family.Add(registry.ProofEntry{
	Name: "DivisorDegreeImage",
	Key:  "prop_8a69a326a6bdb29b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "0 < «scIndex» ∧ " +
			"(∀n:int. " +
			"    (∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scDegree»(D) = n) ⇔ " +
			"    int_of_num(«scIndex») ∣ n)",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			H, setDefinition := a.LetAs[Set[Int]](
				"H", "{«scDegree»(D) | D:(prod(set(A), set(A)) → int) | «scDivisor»(D)}")
			degrees := a.Have(
				"H holds the degrees of the closed divisors",
				"∀n:int. n ∈ H ⇔ ∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scDegree»(D) = n",
				BySets(setDefinition))
			zero := a.Have(
				"the zero divisor has degree zero",
				"int_of_num(0) ∈ H",
				By(
					degrees.At(a.TermAs[Int]("0")),
					curve,
					closed_divisor.ClosedDivisorZero.Read(L).At(k, A0, A1, A01, t)))
			sums := a.Have(
				"the degree of a sum of closed divisors is the sum of their degrees",
				"∀x y:int. x ∈ H ∧ y ∈ H ⇒ x + y ∈ H",
				Derive(func(b *Argument) {
					x, y := b.FixAs[Int]("x"), b.FixAs[Int]("y")
					given := b.Conjuncts(
						b.Assume(),
						"x is a degree",
						"y is a degree")
					D, ofX := b.ObtainAs[_Divisor](
						"x is the degree of a closed divisor D",
						"∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scDegree»(D) = x",
						By(given[0], degrees.At(x)))
					E, ofY := b.ObtainAs[_Divisor](
						"y is the degree of a closed divisor E",
						"∃E:(prod(set(A), set(A)) → int). «scDivisor»(E) ∧ «scDegree»(E) = y",
						By(given[1], degrees.At(y)))
					b.Show(
						"D + E is a closed divisor of degree x + y",
						By(
							degrees.At(b.TermAs[Int]("x + y")),
							curve,
							ofX,
							ofY,
							closed_divisor.ClosedDivisorAdd.Read(L).At(k, A0, A1, A01, t, D, E)))
				}))
			negatives := a.Have(
				"the degree of the negative of a closed divisor is the negative of its degree",
				"∀x:int. x ∈ H ⇒ -x ∈ H",
				Derive(func(b *Argument) {
					x := b.FixAs[Int]("x")
					D, ofX := b.ObtainAs[_Divisor](
						"x is the degree of a closed divisor D",
						"∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scDegree»(D) = x",
						By(b.Assume(), degrees.At(x)))
					b.Show(
						"−D is a closed divisor of degree −x",
						By(
							degrees.At(b.TermAs[Int]("-x")),
							curve,
							ofX,
							closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, D)))
				}))
			subgroup := a.Have(
				"so H is a subgroup of the integers",
				"subgroup(additive_group(int_ring), H)",
				Unfold(group.SubgroupDef),
				By(sums, negatives, zero, set_order.SubsetUniv))
			d, generator := a.ObtainAs[Nat](
				"so H is the set of multiples of a natural number d",
				"∃d:num. H = image(λz:int. d * z, 𝕌)",
				By(subgroup, int_div_rem.IntegerSubgroupPrincipal.At(H)))
			multiples := a.Have(
				"written as a set of multiples",
				"H = {int_of_num(d) * z | z:int | true}",
				BySets(generator))
			points := a.Conjuncts(
				GroupPremises(curve, smooth_curve.ClosedPointsFiniteByDegree.Read(L).At(k, A0, A1, A01, t)),
				"the curve has a closed point",
				"closed points have finite positive degree",
				"finitely many have bounded degree, and finitely many effective divisors each degree")
			P, point := a.UnpackAs[_LatticePair](points[0], "P")
			degreeOfP := a.TermAs[Int]("«scPointDegree»(P)")
			occupied := a.Have(
				"P with coefficient one is a closed divisor of the degree of P",
				"int_of_num(«scPointDegree»(P)) ∈ H",
				By(
					degrees.At(degreeOfP),
					curve,
					point,
					int_real_lift.MulLeftIdentity.At(degreeOfP),
					closed_divisor.ClosedDivisorPoint.Read(L).At(k, A0, A1, A01, t, P, a.TermAs[Int]("1"))))
			z, multiple := a.ObtainAs[Int](
				"that degree is a multiple of d",
				"∃z:int. «scPointDegree»(P) = int_of_num(d) * z",
				BySets(multiples, occupied))
			nonzero := a.Have(
				"it is not zero, since a closed point has positive degree",
				"int_of_num(«scPointDegree»(P)) ≠ 0",
				ByArith(point, points[1].At(P)))
			positive := a.Have(
				"so neither is d",
				"0 < d",
				By(multiple, nonzero, int_real_lift.MulLeftZero.At(z), nat_order.PosIffNonzero.At(d)))
			possible := a.Have(
				"so a positive generator of H exists",
				"∃d:num. 0 < d ∧ H = {d * z | z:int | true}",
				Witness(d),
				By(positive, multiples))
			indexGenerates := a.Have(
				"so the generator the index chooses is one",
				"0 < «scIndex» ∧ H = {int_of_num(«scIndex») * z | z:int | true}",
				Simp(Fwd(divisorIndexDef)),
				By(HilbertDenoted, possible, setDefinition))
			multiplesOfIndex := a.Have(
				"so H is the set of multiples of the index",
				"∀n:int. n ∈ H ⇔ int_of_num(«scIndex») ∣ n",
				Simp(Fwd(int_divides.IntDividesDef)),
				BySets(indexGenerates))
			a.Show(
				"the index is positive, and the degrees are its multiples",
				By(degrees, multiplesOfIndex, indexGenerates))
		}),
})}

// DegreeClassTranslation — multiplication by the class of an invertible pair X
// carries Pic⁰ one-to-one onto the classes of the degree of X. Multiplication by
// the class of the inverse of X is the map back: on representatives the two
// multiply by X and by its inverse, which keep a pair invertible, move its degree
// by the degree of X and cancel each other.
var DegreeClassTranslation = degreeClassTranslationThm{family.Add(registry.ProofEntry{
	Name: "DegreeClassTranslation",
	Key:  "prop_84fa587a073baa0b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(X)",
		},
		Conclusion: "injective_on(«scPicZero», «translate») ∧ " +
			"image(«translate», «scPicZero») = «scClasses»(«scPairDegree»(X))",
		Abbrev: Abbrev{
			{Name: "pairClass", Text: "curve_pair_class(field_ring(L))"},
			{Name: "classMul", Text: "curve_class_mul(field_ring(L), A₀, A₁)"},
			{Name: "translate", Text: "λc:set(prod(set(A), set(A))). «classMul»(c, «pairClass»(X))"},
			{Name: "translateBack", Text: "λc:set(prod(set(A), set(A))). " +
				"    «classMul»(c, «pairClass»(«scInverse»(X)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X *Expr[_LatticePair],
			curve, invertible Fact,
		) {
			overLine := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			picZero := At(curve_degree.InPicZero.Read(L), k, A0, A1, A01, t)
			data := algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)
			classProduct := At(curve_degree.PairClassMul.Read(L), A0, A1, A01, t)
			fibre := a.Have(
				"a class of degree n is the class of an invertible pair of degree n",
				"∀n:int. ∀Z:set(prod(set(A), set(A))). "+
					"    Z ∈ «scClasses»(n) ⇔ "+
					"    ∃W:prod(set(A), set(A)). «scInvertible»(W) ∧ «scPairDegree»(W) = n ∧ Z = «pairClass»(W)",
				Simp(Fwd(degreeClassFibreDef)),
				BySets())
			monoid := a.Have(
				"the invertible pairs are a commutative monoid",
				"comm_monoid_on({N:prod(set(A), set(A)) | «scInvertible»(N)}, «scMul», (A₀, A₁))",
				By(curve, closed_divisor.ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)))
			degrees := divisor_lattice_correspondence.CurveDegreeOnInvertiblePairs.Read(L).At(k, A0, A1, A01, t)
			products := a.Have(
				"a product of invertible pairs is invertible, of the sum of their degrees",
				Statement{
					Binders:    "∀Y Z:prod(set(A), set(A)).",
					Hypotheses: []string{"«scInvertible»(Y)", "«scInvertible»(Z)"},
					Conclusion: "«scInvertible»(«scMul»(Y, Z)) ∧ " +
						"«scPairDegree»(«scMul»(Y, Z)) = «scPairDegree»(Y) + «scPairDegree»(Z)",
				},
				Derive(func(b *Argument) {
					Y, Z := b.FixAs[_LatticePair]("Y"), b.FixAs[_LatticePair]("Z")
					b.Show(
						"the monoid is closed, and the degree adds on it",
						By(b.Assume(), curve, Read(comm_monoid.OpIn, monoid).At(Y, Z), degrees))
				}))
			inverseX := a.TermAs[_LatticePair]("«scInverse»(X)")
			inverse := a.Have(
				"the inverse of X is invertible, and its product with X is the structure pair",
				"«scInvertible»(«scInverse»(X)) ∧ «scMul»(X, «scInverse»(X)) = (A₀, A₁)",
				By(
					curve,
					invertible,
					divisor_lattice_correspondence.InvertiblePairLaws.Read(L).At(k, A0, A1, A01, t)))
			inverseDegree := a.Have(
				"so its degree is the negative of the degree of X",
				"«scPairDegree»(«scInverse»(X)) = -«scPairDegree»(X)",
				ByArith(products.At(X, inverseX), inverse, invertible, curve, degrees))
			forth := a.Have(
				"translation by X sends Pic⁰ to the classes of the degree "+
					"of X, and translation by the inverse of X undoes it",
				Statement{
					Binders:    "∀c:set(prod(set(A), set(A))).",
					Hypotheses: []string{"c ∈ «scPicZero»"},
					Conclusion: "«classMul»(c, «pairClass»(X)) ∈ «scClasses»(«scPairDegree»(X)) ∧ " +
						"«classMul»(«classMul»(c, «pairClass»(X)), «pairClass»(«scInverse»(X))) = c",
				},
				Derive(func(b *Argument) {
					c := b.FixAs[_Class]("c")
					Y, represented := b.ObtainAs[_LatticePair](
						"c is the class of an invertible pair Y of degree zero",
						"∃Y:prod(set(A), set(A)). «scInvertible»(Y) ∧ «scPairDegree»(Y) = 0 ∧ c = «pairClass»(Y)",
						By(overLine, b.Assume(), picZero.At(c)))
					given := b.Conjuncts(
						represented,
						"Y is invertible",
						"of degree zero",
						"c is its class")
					product := b.Have(
						"the product of Y and X is invertible, of the degree of X",
						"«scInvertible»(«scMul»(Y, X)) ∧ «scPairDegree»(«scMul»(Y, X)) = «scPairDegree»(X)",
						ByArith(products.At(Y, X), given[0], given[1], invertible))
					moved := b.Have(
						"and the translate of c is its class",
						"«classMul»(c, «pairClass»(X)) = «pairClass»(«scMul»(Y, X))",
						By(given[2], overLine, data, given[0], invertible, classProduct.At(Y, X)))
					cancelled := b.Have(
						"multiplying by the inverse of X returns Y",
						"«scMul»(«scMul»(Y, X), «scInverse»(X)) = Y",
						By(curve, invertible, given[0], closed_divisor.PairQuotient.Read(L).At(k, A0, A1, A01, t, Y, X)))
					b.Show(
						"so the translate has the degree of X, and translating it back gives the class of Y",
						moved.Rw(),
						By(
							fibre.At(b.TermAs[Int]("«scPairDegree»(X)"), b.TermAs[_Class]("«pairClass»(«scMul»(Y, X))")),
							product,
							overLine,
							data,
							classProduct.At(b.TermAs[_LatticePair]("«scMul»(Y, X)"), inverseX),
							inverse,
							cancelled,
							given[2]))
				}))
			back := a.Have(
				"translation by the inverse of X sends the classes of "+
					"the degree of X to Pic⁰, and translation by X undoes it",
				Statement{
					Binders:    "∀Z:set(prod(set(A), set(A))).",
					Hypotheses: []string{"Z ∈ «scClasses»(«scPairDegree»(X))"},
					Conclusion: "«classMul»(Z, «pairClass»(«scInverse»(X))) ∈ «scPicZero» ∧ " +
						"«classMul»(«classMul»(Z, «pairClass»(«scInverse»(X))), «pairClass»(X)) = Z",
				},
				Derive(func(b *Argument) {
					Z := b.FixAs[_Class]("Z")
					W, represented := b.ObtainAs[_LatticePair](
						"Z is the class of an invertible pair W of the degree of X",
						"∃W:prod(set(A), set(A)). "+
							"    «scInvertible»(W) ∧ «scPairDegree»(W) = «scPairDegree»(X) ∧ Z = «pairClass»(W)",
						By(b.Assume(), fibre.At(b.TermAs[Int]("«scPairDegree»(X)"), Z)))
					given := b.Conjuncts(
						represented,
						"W is invertible",
						"of the degree of X",
						"Z is its class")
					product := b.Have(
						"the product of W and the inverse of X is invertible, of degree zero",
						"«scInvertible»(«scMul»(W, «scInverse»(X))) ∧ «scPairDegree»(«scMul»(W, «scInverse»(X))) = 0",
						ByArith(products.At(W, inverseX), given[0], inverse, given[1], inverseDegree))
					moved := b.Have(
						"and the translate of Z is its class",
						"«classMul»(Z, «pairClass»(«scInverse»(X))) = «pairClass»(«scMul»(W, «scInverse»(X)))",
						By(given[2], overLine, data, given[0], inverse, classProduct.At(W, inverseX)))
					cancelled := b.Have(
						"multiplying by X returns W",
						"«scMul»(«scMul»(W, «scInverse»(X)), X) = W",
						By(curve, invertible, given[0], closed_divisor.PairQuotient.Read(L).At(k, A0, A1, A01, t, W, X)))
					b.Show(
						"so the translate lies in Pic⁰, and translating it back gives the class of W",
						moved.Rw(),
						By(
							overLine,
							data,
							picZero.At(b.TermAs[_Class]("«pairClass»(«scMul»(W, «scInverse»(X)))")),
							product,
							classProduct.At(b.TermAs[_LatticePair]("«scMul»(W, «scInverse»(X))"), X),
							invertible,
							cancelled,
							given[2]))
				}))
			a.Show(
				"the two translations are inverse bijections between Pic⁰ and the classes of the degree of X",
				By(
					forth,
					back,
					functions.TwoSidedInverseBijection.At(
						a.TermAs[Set[_Class]]("«scPicZero»"),
						a.TermAs[Set[_Class]]("«scClasses»(«scPairDegree»(X))"),
						a.TermAs[Fun[_Class, _Class]]("«translate»"),
						a.TermAs[Fun[_Class, _Class]]("«translateBack»"))))
		}),
})}

// ClassComplementBijection — for a closed divisor E the map c ↦ [E]·c⁻¹ carries the
// classes of degree n one-to-one onto the classes of degree deg E − n. On the class
// of a divisor D it gives the class of E − D, of degree deg E − deg D; and it is its
// own inverse, since E − (E − D) = D.
var ClassComplementBijection = classComplementBijectionThm{family.Add(registry.ProofEntry{
	Name: "ClassComplementBijection",
	Key:  "prop_4727e9b67c91795e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀E:(prod(set(A), set(A)) → int). ∀n:int.",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(E)",
		},
		Conclusion: "injective_on(«scClasses»(n), «complement») ∧ " +
			"image(«complement», «scClasses»(n)) = «scClasses»(«scDegree»(E) - n)",
		Abbrev: Abbrev{
			{Name: "complement", Text: "λc:set(prod(set(A), set(A))). " +
				"    curve_class_mul(field_ring(L), " +
				"        A₀, " +
				"        A₁, " +
				"        «scClass»(E), " +
				"        curve_class_inverse(field_ring(L), A₀, A₁, c))"},
			{Name: "difference", Text: "λD:(prod(set(A), set(A)) → int). λP:prod(set(A), set(A)). E(P) - D(P)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E *Arrow[_LatticePair, Int],
			n *Expr[Int],
			curve, divisorE Fact,
		) {
			moved := a.Have(
				"the complement sends degree m to deg E − m, and applied twice it is the identity",
				Statement{
					Binders:    "∀m:int. ∀c:set(prod(set(A), set(A))).",
					Hypotheses: []string{"c ∈ «scClasses»(m)"},
					Conclusion: "«complement»(c) ∈ «scClasses»(«scDegree»(E) - m) ∧ «complement»(«complement»(c)) = c",
				},
				Derive(func(b *Argument) {
					m, c := b.FixAs[Int]("m"), b.FixAs[_Class]("c")
					D, represented := b.ObtainAs[_Divisor](
						"c is the class of a closed divisor D of degree m",
						"∃D:prod(set(A), set(A)) → int. «scDivisor»(D) ∧ «scDegree»(D) = m ∧ «scClass»(D) = c",
						By(b.Assume(), curve, InDegreeClasses.Read(L).At(k, A0, A1, A01, t, m, c)))
					given := b.Conjuncts(
						represented,
						"D is a closed divisor",
						"of degree m",
						"c is its class")
					eMinusD := b.TermAs[_Divisor]("«difference»(D)")
					difference := b.Have(
						"E − D is a closed divisor, of degree deg E − m",
						"«scDivisor»(«difference»(D)) ∧ «scDegree»(«difference»(D)) = «scDegree»(E) - m",
						By(
							given[1],
							curve,
							divisorE,
							given[0],
							closed_divisor.ClosedDivisorSub.Read(L).At(k, A0, A1, A01, t, E, D)))
					first := b.Have(
						"the complement of the class of D is the class of E − D",
						"«complement»(«scClass»(D)) = «scClass»(«difference»(D))",
						By(
							curve,
							divisorE,
							given[0],
							smooth_curve_riemann_roch.ClassOfDifference.Read(L).At(k, A0, A1, A01, t, E, D)))
					second := b.Have(
						"the complement of the class of E − D is the class of E − (E − D)",
						"«complement»(«scClass»(«difference»(D))) = "+
							"«scClass»(λP:prod(set(A), set(A)). E(P) - (E(P) - D(P)))",
						By(
							curve,
							divisorE,
							difference,
							smooth_curve_riemann_roch.ClassOfDifference.Read(L).At(k, A0, A1, A01, t, E, eMinusD)))
					cancelled := b.Have(
						"which is D",
						"(λP:prod(set(A), set(A)). E(P) - (E(P) - D(P))) = D",
						Funext(),
						ByArith())
					b.Show(
						"so the complement of c has degree deg E − m, and the complement of that is c",
						given[2].RwRev(),
						first.Rw(),
						second.Rw(),
						cancelled.Rw(),
						By(
							curve,
							difference,
							InDegreeClasses.Read(L).At(
								k,
								A0,
								A1,
								A01,
								t,
								b.TermAs[Int]("«scDegree»(E) - m"),
								b.TermAs[_Class]("«scClass»(«difference»(D))"))))
				}))
			reflected := a.TermAs[Int]("«scDegree»(E) - n")
			twice := a.Have(
				"reflecting twice returns n",
				"«scDegree»(E) - («scDegree»(E) - n) = n",
				ByArith())
			back := a.Have(
				"so the complement sends degree deg E − n back to n",
				Statement{
					Binders:    "∀c:set(prod(set(A), set(A))).",
					Hypotheses: []string{"c ∈ «scClasses»(«scDegree»(E) - n)"},
					Conclusion: "«complement»(c) ∈ «scClasses»(n) ∧ «complement»(«complement»(c)) = c",
				},
				By(moved.At(reflected), twice))
			complement := a.TermAs[Fun[_Class, _Class]]("«complement»")
			a.Show(
				"the complement is a two-sided inverse of itself between the two sets of classes",
				By(
					back,
					moved.At(n),
					functions.TwoSidedInverseBijection.At(
						a.TermAs[Set[_Class]]("«scClasses»(n)"),
						a.TermAs[Set[_Class]]("«scClasses»(«scDegree»(E) - n)"),
						complement,
						complement)))
		}),
})}

// InDegreeClasses — a class has degree n exactly when it is the class of a closed
// divisor of degree n. An invertible pair is the pair of a closed divisor, of its
// own degree, and the pair of a closed divisor is invertible.
var InDegreeClasses = inDegreeClassesThm{family.Add(registry.ProofEntry{
	Name: "InDegreeClasses",
	Key:  "prop_2c044f21fff0260a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:int. ∀c:set(prod(set(A), set(A))).",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "c ∈ «scClasses»(n) ⇔ " +
			"∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scDegree»(D) = n ∧ «scClass»(D) = c",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Int],
			c *Expr[_Class],
			curve Fact,
		) {
			fibre := a.Have(
				"a class of degree n is the class of an invertible pair of degree n",
				"c ∈ «scClasses»(n) ⇔ "+
					"∃X:prod(set(A), set(A)). "+
					"    «scInvertible»(X) ∧ «scPairDegree»(X) = n ∧ c = curve_pair_class(field_ring(L), X)",
				Simp(Fwd(degreeClassFibreDef)),
				BySets())
			a.Iff()
			a.Forward(
				"the invertible pair of c is the pair of a closed divisor, of its degree",
				func(b *Argument, member Fact) {
					X, pair := b.ObtainAs[_LatticePair](
						"c is the class of an invertible pair X of degree n",
						"∃X:prod(set(A), set(A)). "+
							"    «scInvertible»(X) ∧ «scPairDegree»(X) = n ∧ c = curve_pair_class(field_ring(L), X)",
						By(fibre, member))
					onX := b.Conjuncts(
						pair,
						"X is invertible",
						"of degree n",
						"c is its class")
					D, divisorOfX := b.ObtainAs[_Divisor](
						"X is the pair of a closed divisor D",
						"∃D:prod(set(A), set(A)) → int. «scDivisor»(D) ∧ «scPair»(D) = X",
						By(
							curve,
							onX[0],
							divisor_lattice_correspondence.InvertiblePairHasDivisor.Read(L).At(k, A0, A1, A01, t, X)))
					onD := b.Conjuncts(
						divisorOfX,
						"D is a closed divisor",
						"X is its pair")
					b.Take(D)
					b.Show(
						"D has the degree of its pair, and c is its class",
						By(
							Normalized,
							onD[0],
							onD[1],
							onX[1],
							onX[2],
							curve,
							divisor_lattice_correspondence.ClosedDivisorLatticeDegree.Read(L).At(k, A0, A1, A01, t, D)))
				})
			a.Backward(
				"the pair of a closed divisor of degree n is invertible, of degree n",
				func(b *Argument, represented Fact) {
					_, onD := b.UnpackAs[_Divisor](represented)
					given := b.Conjuncts(
						onD,
						"D is a closed divisor",
						"of degree n",
						"c is its class")
					pair := b.Have(
						"its pair is invertible, of the degree of D",
						"«scInvertible»(«scPair»(D)) ∧ «scPairDegree»(«scPair»(D)) = «scDegree»(D)",
						By(
							curve,
							given[0],
							divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(k, A0, A1, A01, t)))
					b.Show(
						"and c is the class of that pair",
						By(fibre, given[1], given[2], pair))
				})
		}),
})}

// DivisorDegreeClasses — the index is positive and is the degree of a closed
// divisor, and the classes of a given degree are finite: as many as Pic⁰ when the
// degree is a multiple of the index, and none otherwise. An invertible pair is
// the pair of a closed divisor of its own degree, so a degree that is no multiple
// has no classes; and a multiple is the degree of a closed divisor D, translation
// by whose class carries Pic⁰ one-to-one onto the classes of that degree.
var DivisorDegreeClasses = divisorDegreeClassesThm{family.Add(registry.ProofEntry{
	Name: "DivisorDegreeClasses",
	Key:  "prop_1a125b1491106ed0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "0 < «scIndex» ∧ " +
			"(∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scDegree»(D) = int_of_num(«scIndex»)) ∧ " +
			"(∀n:int. " +
			"    finite(«scClasses»(n)) ∧ " +
			"    card(«scClasses»(n)) = COND(int_of_num(«scIndex») ∣ n, card(«scPicZero»), 0))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			image := a.Conjuncts(
				GroupPremises(curve, DivisorDegreeImage.Read(L).At(k, A0, A1, A01, t)),
				"the index is positive",
				"the degrees of the closed divisors are its multiples")
			positive, degrees := image[0], image[1]
			integerIndex := a.TermAs[Int]("«scIndex»")
			attained := a.Have(
				"the index is a multiple of itself, so it is the degree of a closed divisor",
				"∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scDegree»(D) = int_of_num(«scIndex»)",
				By(
					degrees.At(integerIndex),
					int_real_lift.MulRightIdentity.At(integerIndex),
					int_divides.IntDividesDef.At(integerIndex, integerIndex)))
			finitePic := a.Have(
				"Pic⁰ is finite",
				"finite(«scPicZero»)",
				By(curve, smooth_curve_riemann_roch.DegreeZeroClassGroupFinite.Read(L).At(k, A0, A1, A01, t)))
			counts := a.Have(
				"the classes of each degree are counted",
				"∀n:int. "+
					"    finite(«scClasses»(n)) ∧ "+
					"    card(«scClasses»(n)) = COND(int_of_num(«scIndex») ∣ n, card(«scPicZero»), 0)",
				Derive(func(b *Argument) {
					n := b.FixAs[Int]("n")
					b.Cases(b.TermAs[Bool]("int_of_num(«scIndex») ∣ n"))
					b.When(
						"a multiple of the index is the degree of a closed divisor, "+
							"whose translations count the classes of that degree",
						func(c *Argument, multiple Fact) {
							_, ofN := c.ObtainAs[_Divisor](
								"n is the degree of a closed divisor D",
								"∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scDegree»(D) = n",
								By(multiple, degrees.At(n)))
							pair := c.Have(
								"its pair is invertible, of degree n",
								"«scInvertible»(«scPair»(D)) ∧ «scPairDegree»(«scPair»(D)) = n",
								By(
									ofN,
									curve,
									divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(k, A0, A1, A01, t)))
							translation := c.Conjuncts(
								GroupPremises(
									curve,
									pair,
									DegreeClassTranslation.Read(L).At(k, A0, A1, A01, t, c.TermAs[_LatticePair]("«scPair»(D)"))),
								"translation by the class of D is one-to-one on Pic⁰",
								"its image is the classes of the degree of the pair of D")
							onto := c.Have(
								"so the classes of degree n are the image of Pic⁰",
								"«scClasses»(n) = "+
									"image(λc:set(prod(set(A), set(A))). curve_class_mul(field_ring(L), A₀, A₁, c, «scClass»(D)), "+
									"    «scPicZero»)",
								By(translation[1], pair))
							translate := c.TermAs[Fun[_Class, _Class]](
								"λc:set(prod(set(A), set(A))). curve_class_mul(field_ring(L), A₀, A₁, c, «scClass»(D))")
							pic := c.TermAs[Set[_Class]]("«scPicZero»")
							c.Show(
								"the image of the finite set Pic⁰ under a one-to-one map is finite and has its cardinality",
								onto.Rw(),
								By(
									finitePic,
									multiple,
									translation[0],
									finite_set.FiniteImage.At(translate, pic),
									cardinality.CardImageInj.At(translate, pic)))
						})
					b.Otherwise(
						"a degree that is no multiple of the index has no classes",
						func(c *Argument, notMultiple Fact) {
							empty := c.Have(
								"so no class has degree n: it would be the class of a "+
									"closed divisor of degree n, and n is the degree of none",
								"«scClasses»(n) = ∅",
								BySets(notMultiple, degrees.At(n), curve, At(InDegreeClasses.Read(L), k, A0, A1, A01, t, n)))
							c.Show(
								"the empty set is finite, of cardinality zero",
								empty.Rw(),
								By(notMultiple, finite_set.FiniteRules, cardinality.CardClauses))
						})
				}))
			a.Show(
				"the index is positive and attained, and the classes of each degree are counted",
				By(positive, attained, counts))
		}),
})}

// EffectiveCountOfDivisors — the effective count of degree n counts the effective
// divisors of degree n, which are finite in number. At a natural number the
// effective count counts the weighted effective functions of that degree, and the
// cast and the coefficients are mutually inverse between those functions and the
// effective divisors of that degree; in negative degree there are no such divisors
// and the count vanishes.
var EffectiveCountOfDivisors = effectiveCountOfDivisorsThm{family.Add(registry.ProofEntry{
	Name: "EffectiveCountOfDivisors",
	Key:  "prop_7a1783c9cc0cff57",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "finite(«scOfDegree»(n)) ∧ «scEffective»(n) = real_of_num(card(«scOfDegree»(n)))",
		Abbrev: Abbrev{
			{Name: "weighted", Text: "λd:num. " +
				"    {x:prod(set(A), set(A)) → num | " +
				"        weighted_effective(«scPoints», «scPointDegree», x) ∧ " +
				"        weighted_degree(«scPointDegree», x) = d}"},
			{Name: "cast", Text: "λx:(prod(set(A), set(A)) → num). λP:prod(set(A), set(A)). int_of_num(x(P))"},
			{Name: "coefficients", Text: "λE:(prod(set(A), set(A)) → int). λP:prod(set(A), set(A)). " +
				"    num_of_int(E(P))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		n *Expr[Int],
		curve Fact,
	) {
		castDivisor := a.Have(
			"the cast of a weighted effective function is an effective divisor of its weighted degree",
			Statement{
				Binders:    "∀x:(prod(set(A), set(A)) → num).",
				Hypotheses: []string{"weighted_effective(«scPoints», «scPointDegree», x)"},
				Conclusion: "«cast»(x) ∈ «scOfDegree»(int_of_num(weighted_degree(«scPointDegree», x))) ∧ " +
					"«coefficients»(«cast»(x)) = x",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[_LatticePair, Nat]]("x")
				onSupport := b.Conjuncts(
					b.Unfolded(b.Assume(), weighted_divisors.WeightedEffectiveDef),
					"the support of x is finite",
					"and consists of closed points of positive degree")
				cast := b.TermAs[_Divisor]("«cast»(x)")
				divisor := b.Have(
					"the cast has the same finite support, so it is a closed divisor",
					"«scDivisor»(«cast»(x))",
					By(
						onSupport[0],
						onSupport[1],
						closed_divisor.ClosedDivisorOfSupport.At(
							b.TermAs[RingOps[A]]("field_ring(L)"),
							A0,
							A1,
							A01,
							b.TermAs[Set[_LatticePair]]("fun_support(0, x)"),
							cast)))
				retract := b.Have(
					"the coefficients of the cast are x again",
					"«coefficients»(«cast»(x)) = x",
					Funext(),
					b.ForEach(func(_ *Expr[_LatticePair]) Action { return By(int_embed.OfNumRetract) }))
				degree := b.Have(
					"so the degree of the cast is the cast of the weighted degree of x",
					"«scDegree»(«cast»(x)) = int_of_num(weighted_degree(«scPointDegree», x))",
					By(
						curve,
						divisor,
						retract,
						int_embed.EmbedNonneg,
						smooth_curve_riemann_roch.EffectiveDivisorWeighted.Read(L).At(k, A0, A1, A01, t, cast)))
				b.Show(
					"its coefficients are nonnegative as casts",
					By(divisor, degree, retract, int_embed.EmbedNonneg))
			}))
		coefficientFunction := a.Have(
			"the coefficients of an effective divisor are a weighted "+
				"effective function of its degree, and their cast is the divisor",
			Statement{
				Binders: "∀E:(prod(set(A), set(A)) → int).",
				Hypotheses: []string{
					"«scDivisor»(E)",
					"∀P:prod(set(A), set(A)). int_of_num(0) ≤ E(P)",
				},
				Conclusion: "weighted_effective(«scPoints», «scPointDegree», «coefficients»(E)) ∧ " +
					"«scDegree»(E) = int_of_num(weighted_degree(«scPointDegree», «coefficients»(E))) ∧ " +
					"«cast»(«coefficients»(E)) = E",
			},
			Derive(func(b *Argument) {
				E := b.FixAs[_Divisor]("E")
				given := b.Conjuncts(
					b.Assume(),
					"E is a closed divisor",
					"E is effective")
				section := b.Have(
					"a nonnegative coefficient is the cast of its natural number",
					"«cast»(«coefficients»(E)) = E",
					Funext(),
					b.ForEach(func(P *Expr[_LatticePair]) Action {
						return By(given[1].At(P), int_embed.NumOfIntSection)
					}))
				b.Show(
					"the rest is the weighted reading of an effective divisor",
					By(
						section,
						curve,
						given[0],
						given[1],
						smooth_curve_riemann_roch.EffectiveDivisorWeighted.Read(L).At(k, A0, A1, A01, t, E)))
			}))
		a.Cases(a.TermAs[Bool]("n < int_of_num(0)"))
		a.When(
			"in negative degree there are none, and the count is zero",
			func(c *Argument, negative Fact) {
				none := c.Have(
					"no effective divisor has the negative degree n",
					"∀E:(prod(set(A), set(A)) → int). E ∉ «scOfDegree»(n)",
					Derive(func(d *Argument) {
						E := d.FixAs[_Divisor]("E")
						d.Show(
							"its degree is the cast of a natural number, which is not negative",
							ByArith(
								negative,
								coefficientFunction.At(E),
								int_embed.EmbedNonneg.At(d.TermAs[Nat]("weighted_degree(«scPointDegree», «coefficients»(E))"))))
					}))
				empty := c.Have(
					"so the set of them is empty",
					"«scOfDegree»(n) = ∅",
					BySets(none))
				c.Show(
					"and the effective count of a negative degree is zero",
					empty.Rw(),
					By(negative, CurveEffectiveCountDef, finite_set.FiniteRules, cardinality.CardClauses))
			})
		a.Otherwise(
			"at a natural number the cast carries the weighted effective functions onto them",
			func(c *Argument, nonnegative Fact) {
				m, natural := c.ObtainAs[Nat](
					"a nonnegative integer is a natural number",
					"∃m:num. n = int_of_num(m)",
					ByArith(nonnegative, int_embed.OfNumExists.At(n)))
				there := c.Have(
					"the cast sends a weighted effective function of degree m to an effective divisor of degree m",
					Statement{
						Binders:    "∀x:(prod(set(A), set(A)) → num).",
						Hypotheses: []string{"x ∈ «weighted»(m)"},
						Conclusion: "«cast»(x) ∈ «scOfDegree»(int_of_num(m)) ∧ «coefficients»(«cast»(x)) = x",
					},
					Derive(func(d *Argument) {
						x := d.FixAs[Fun[_LatticePair, Nat]]("x")
						member := d.Assume()
						d.Show(
							"x has weighted degree m",
							By(castDivisor.At(x), member))
					}))
				back := c.Have(
					"the coefficients send an effective divisor of "+
						"degree m to a weighted effective function of degree m",
					Statement{
						Binders:    "∀E:(prod(set(A), set(A)) → int).",
						Hypotheses: []string{"E ∈ «scOfDegree»(int_of_num(m))"},
						Conclusion: "«coefficients»(E) ∈ «weighted»(m) ∧ «cast»(«coefficients»(E)) = E",
					},
					Derive(func(d *Argument) {
						E := d.FixAs[_Divisor]("E")
						member := d.Assume()
						d.Show(
							"the cast is one-to-one, so the weighted degree is m",
							By(
								coefficientFunction.At(E),
								member,
								int_embed.OfNumEq.At(d.TermAs[Nat]("weighted_degree(«scPointDegree», «coefficients»(E))"), m)))
					}))
				counted := c.Have(
					"finitely many weighted effective functions have degree m, and "+
						"mutually inverse maps carry their count to the divisors of degree m",
					"finite(«scOfDegree»(int_of_num(m))) ∧ card(«scOfDegree»(int_of_num(m))) = card(«weighted»(m))",
					By(
						there,
						back,
						curve,
						smooth_curve.ClosedPointsFiniteByDegree.Read(L).At(k, A0, A1, A01, t),
						cardinality.MutualInversesCard.At(
							c.TermAs[Set[Fun[_LatticePair, Nat]]]("«weighted»(m)"),
							c.TermAs[Set[_Divisor]]("«scOfDegree»(int_of_num(m))"),
							c.TermAs[Fun[Fun[_LatticePair, Nat], _Divisor]]("«cast»"),
							c.TermAs[Fun[_Divisor, Fun[_LatticePair, Nat]]]("«coefficients»"))))
				count := c.Have(
					"at a natural number the effective count is the cast of the weighted count",
					"«scEffective»(int_of_num(m)) = real_of_num(card(«weighted»(m)))",
					By(
						weighted_divisors.WeightedCountDef,
						CurveEffectiveCountDef,
						int_embed.OfNumRetract,
						int_embed.OfNumLt,
						nat_order.LessThanZeroClause))
				c.Show(
					"which is what the two sides say at n = m",
					natural.Rw(),
					By(counted, count))
			})
	}),
})}

// ClassHasOneDegree — a divisor in a class of degree n has degree n. The class is
// the class of an invertible pair X of degree n, so X is a nonzero multiple of the
// pair of the divisor, and scaling a pair keeps its degree.
var ClassHasOneDegree = classHasOneDegreeThm{family.Add(registry.ProofEntry{
	Name: "ClassHasOneDegree",
	Key:  "prop_4da0e6e2f1b90349",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:int. ∀E:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(E)",
			"«scClass»(E) ∈ «scClasses»(n)",
		},
		Conclusion: "«scDegree»(E) = n",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Int],
			E *Arrow[_LatticePair, Int],
			curve, divisor, inClasses Fact,
		) {
			correspondence := divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(
				k, A0, A1, A01, t)
			overLine := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			X, pair := a.ObtainAs[_LatticePair](
				"the class of E is the class of an invertible pair X of degree n",
				"∃X:prod(set(A), set(A)). "+
					"    «scInvertible»(X) ∧ «scPairDegree»(X) = n ∧ «scClass»(E) = curve_pair_class(field_ring(L), X)",
				By(a.Simplified(inClasses, Fwd(degreeClassFibreDef))))
			onX := a.Conjuncts(
				pair,
				"X is invertible",
				"of degree n",
				"the class of E is the class of X")
			pairE := a.TermAs[_LatticePair]("«scPair»(E)")
			invertible := a.Have(
				"the pair of E is invertible",
				"«scInvertible»(«scPair»(E))",
				By(curve, divisor, correspondence))
			s, multiple := a.ObtainAs[A](
				"one class means that X is a nonzero multiple of the pair of E",
				"∃s:A. s ∈ L.carrier ∧ s ≠ L.zero ∧ X = lattice_pair_scale(s, «scPair»(E))",
				By(
					overLine,
					invertible,
					onX[0],
					onX[2],
					algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
					curve_degree.PairClassEqIff.Read(L).At(A0, A1, A01, t, pairE, X)))
			scale := a.Conjuncts(
				multiple,
				"s lies in L",
				"s is not zero",
				"X is s times the pair of E")
			a.Show(
				"scaling keeps the degree, and the pair of E has the degree of E",
				By(
					overLine,
					invertible,
					scale[1],
					scale[2],
					onX[1],
					curve,
					divisor,
					curve_degree.DegreeScale.Read(L).At(k, A0, A1, A01, t, a.MemberOf[on.L](s, scale[0]), pairE),
					divisor_lattice_correspondence.ClosedDivisorLatticeDegree.Read(L).At(k, A0, A1, A01, t, E)))
		}),
})}

// EffectiveCountOverClasses — the number of effective divisors of degree n is
// the sum, over the classes of degree n, of the number of effective divisors in
// each. The effective count counts the effective divisors of degree n; each of
// them has exactly one class of degree n, and a divisor in a class of degree n has
// degree n, so the fibre over a class of degree n is the set of effective divisors
// in that class.
var EffectiveCountOverClasses = effectiveCountOverClassesThm{family.Add(registry.ProofEntry{
	Name: "EffectiveCountOverClasses",
	Key:  "prop_821e0adb08f57e22",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "«scEffective»(n) = " +
			"real_of_num(sum(«scClasses»(n), λc:set(prod(set(A), set(A))). card(«scEffectiveInClass»(c))))",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		n *Expr[Int],
		curve Fact,
	) {
		divisors := a.Conjuncts(
			GroupPremises(curve, EffectiveCountOfDivisors.Read(L).At(k, A0, A1, A01, t, n)),
			"the effective divisors of degree n are finite in number",
			"and the effective count counts them")
		classIn := a.Have(
			"an effective divisor of degree n has its class among the classes of degree n",
			"∀E:(prod(set(A), set(A)) → int). E ∈ «scOfDegree»(n) ⇒ «scClass»(E) ∈ «scClasses»(n)",
			Derive(func(b *Argument) {
				b.FixAs[_Divisor]("E")
				b.Show(
					"it is a closed divisor of degree n, and its class is that divisor's class",
					By(
						b.Assume(),
						curve,
						InDegreeClasses.Read(L).At(k, A0, A1, A01, t, n, b.TermAs[_Class]("«scClass»(E)"))))
			}))
		unique := a.Have(
			"so each effective divisor of degree n has exactly one class of degree n",
			Statement{
				Binders: "∀E:(prod(set(A), set(A)) → int).",
				Hypotheses: []string{
					"E ∈ «scOfDegree»(n)",
				},
				Conclusion: "∃!c:set(prod(set(A), set(A))). c ∈ «scClasses»(n) ∧ «scClass»(E) = c",
			},
			By(classIn))
		effectiveDivisors := a.TermAs[Set[_Divisor]]("«scOfDegree»(n)")
		fibres := a.Have(
			"and the fibre over a class of degree n is the set of effective divisors in the class",
			Statement{
				Binders:    "∀c:set(prod(set(A), set(A))).",
				Hypotheses: []string{"c ∈ «scClasses»(n)"},
				Conclusion: "has_size({E:prod(set(A), set(A)) → int | E ∈ «scOfDegree»(n) ∧ «scClass»(E) = c}, " +
					"    card(«scEffectiveInClass»(c)))",
			},
			Derive(func(b *Argument) {
				b.FixAs[_Class]("c")
				member := b.Assume()
				fibre := b.Have(
					"every divisor of the class has degree n",
					"{E:prod(set(A), set(A)) → int | E ∈ «scOfDegree»(n) ∧ «scClass»(E) = c} = «scEffectiveInClass»(c)",
					BySets(curve, member, At(ClassHasOneDegree.Read(L), k, A0, A1, A01, t, n)))
				finite := b.Have(
					"a part of a finite set is finite",
					"finite(«scEffectiveInClass»(c))",
					fibre.RwRev(),
					By(
						divisors[0],
						finite_set.FiniteRestrict.At(
							effectiveDivisors,
							b.TermAs[Set[_Divisor]]("λE:prod(set(A), set(A)) → int. «scClass»(E) = c"))))
				b.Show(
					"so the fibre has the size of that set",
					fibre.Rw(),
					By(finite, cardinality.HasSizeDef))
			}))
		total := a.Have(
			"counting the effective divisors of degree n by their classes",
			"card(«scOfDegree»(n)) = "+
				"sum(«scClasses»(n), λc:set(prod(set(A), set(A))). card(«scEffectiveInClass»(c)))",
			By(
				divisors[0],
				unique,
				fibres,
				nat_sum.CardByFibres.At(
					effectiveDivisors,
					a.TermAs[Set[_Class]]("«scClasses»(n)"),
					a.TermAs[Fun2[_Divisor, _Class, Bool]](
						"λE:prod(set(A), set(A)) → int. λc:set(prod(set(A), set(A))). «scClass»(E) = c"),
					a.TermAs[Fun[_Class, Nat]]("λc:set(prod(set(A), set(A))). card(«scEffectiveInClass»(c))"))))
		a.Show(
			"the effective count is the cast of that sum",
			By(divisors[1], total))
	}),
})}

// EffectiveCountTail — in a degree past 2g − 2 that the index divides, the
// effective count is the size of the degree-zero class group times one geometric
// term in the size of the constants. Past 2g − 2 the exponent n + 1 − g is a
// natural number s. Every class of degree n is the class of a divisor of degree
// n, which has s sections by Riemann–Roch, so the effective divisors of every
// class are one projective space over the constants; a degree the index divides
// has as many classes as degree zero, and the effective count is the sum over
// them.
var EffectiveCountTail = effectiveCountTailThm{family.Add(registry.ProofEntry{
	Name: "EffectiveCountTail",
	Key:  "prop_c5fa9e00b0b6cbeb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"«scCurve»",
			"int_of_num(«scIndex») ∣ n",
			"2 * «scGenus» - int_of_num(2) < n",
		},
		Conclusion: "real_of_num(card(k) - 1) * «scEffective»(n) = " +
			"real_of_num(card(«scPicZero»)) * " +
			"(real_zpow(«q», n + int_of_num(1) - int_of_num(«scGenus»)) - real_of_num(1))",
		Abbrev: Abbrev{
			{Name: "classSum", Text: "sum(«scClasses»(n), " +
				"    λc:set(prod(set(A), set(A))). card(«scEffectiveInClass»(c)))"},
			{Name: "constantSum", Text: "sum(«scClasses»(n), λc:set(prod(set(A), set(A))). card(k) ^ s - 1)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		n *Expr[Int],
		curve, divides, large Fact,
	) {
		exponent := a.TermAs[Int]("n + &1 - int_of_num(«scGenus»)")
		genus := a.TermAs[Nat]("«scGenus»")
		s, natural := a.ObtainAs[Nat](
			"past 2g − 2 the exponent n + 1 − g is at least g, so it is a natural number s",
			"∃s:num. n + 1 - int_of_num(«scGenus») = s",
			ByArith(
				large,
				int_embed.OfNumExists.At(exponent),
				int_embed.EmbedNonneg.At(genus),
				int_embed.OfNumMul.At(a.TermAs[Nat]("2"), genus)))
		common := a.Have(
			"every class of degree n holds one number of effective "+
				"divisors, a projective space of dimension s − 1",
			Statement{
				Binders:    "∀c:set(prod(set(A), set(A))).",
				Hypotheses: []string{"c ∈ «scClasses»(n)"},
				Conclusion: "(card(k) - 1) * card(«scEffectiveInClass»(c)) = card(k) ^ s - 1",
			},
			Derive(func(b *Argument) {
				c := b.FixAs[_Class]("c")
				D, ofDegree := b.ObtainAs[_Divisor](
					"c is the class of a closed divisor D of degree n",
					"∃D:prod(set(A), set(A)) → int. «scDivisor»(D) ∧ «scDegree»(D) = n ∧ «scClass»(D) = c",
					By(b.Assume(), curve, InDegreeClasses.Read(L).At(k, A0, A1, A01, t, n, c)))
				onD := b.Conjuncts(
					ofDegree,
					"D is a closed divisor",
					"of degree n",
					"c is its class")
				sections := b.Have(
					"past 2g − 2 Riemann–Roch gives D s sections",
					"«scSections»(«scPair»(D)) = s",
					By(
						natural,
						onD[1],
						large,
						curve,
						onD[0],
						smooth_curve_riemann_roch.SectionsByDivisorDegree.Read(L).At(k, A0, A1, A01, t, D),
						int_embed.OfNumEq.At(b.TermAs[Nat]("«scSections»(«scPair»(D))"), s)))
				b.Show(
					"and c is the class of D, whose effective divisors are its nonzero sections up to the constants",
					By(onD[2], sections, curve, onD[0], EffectiveDivisorsInClass.Read(L).At(k, A0, A1, A01, t, D)))
			}))
		sized := a.Conjuncts(
			a.Have(
				"the index divides n, so there are h classes of degree n",
				"finite(«scClasses»(n)) ∧ card(«scClasses»(n)) = card(«scPicZero»)",
				By(curve, divides, DivisorDegreeClasses.Read(L).At(k, A0, A1, A01, t))),
			"finitely many classes have degree n",
			"namely h")
		classes := a.TermAs[Set[_Class]]("«scClasses»(n)")
		value := a.TermAs[Nat]("card(k) ^ s - 1")
		total := a.Have(
			"so q − 1 times the sum over the classes is h times the common value",
			"(card(k) - 1) * «classSum» = card(«scPicZero») * (card(k) ^ s - 1)",
			CalcEq(
				Leg(
					a.TermAs[Nat]("«constantSum»"),
					"each term of the scaled sum is the common value",
					By(
						sized[0],
						common,
						nat_sum.ScalarLeft.At(
							a.TermAs[Nat]("card(k) - 1"),
							a.TermAs[Fun[_Class, Nat]]("λc:set(prod(set(A), set(A))). card(«scEffectiveInClass»(c))"),
							classes),
						nat_sum.Congruence.At(
							classes,
							a.TermAs[Fun[_Class, Nat]](
								"λc:set(prod(set(A), set(A))). (card(k) - 1) * card(«scEffectiveInClass»(c))"),
							a.TermAs[Fun[_Class, Nat]]("λc:set(prod(set(A), set(A))). card(k) ^ s - 1")))),
				FinalLeg(
					"a sum of a constant over h classes is h times the constant",
					ByArith(
						sized[0],
						sized[1],
						nat_sum.ScalarLeft.At(
							value, a.TermAs[Fun[_Class, Nat]]("λc:set(prod(set(A), set(A))). 1"), classes),
						nat_sum.SumOfOnes.At(classes)))))
		atLeastTwo := a.Have(
			"the constants are a finite subfield, of at least two elements",
			"1 < card(k)",
			By(curve, ConstantsAtLeastTwo.Read(L).At(k, A0, A1, A01, t)))
		exact := a.Have(
			"so q^s is at least one, and subtracting one from it is exact",
			"card(k) ^ s = (card(k) ^ s - 1) + 1",
			ByArith(atLeastTwo, nat_order.PowPositive.At(a.TermAs[Nat]("card(k)"), s)))
		cast := a.Have(
			"so the common value casts to q^s − 1",
			"real_of_num(card(k) ^ s - 1) = «q» ^ s - real_of_num(1)",
			ByArith(
				exact,
				real_pow.OfNumPow.At(a.TermAs[Nat]("card(k)"), s),
				real_construction.OfNumAdd.At(value, a.TermAs[Nat]("1"))))
		power := a.Have(
			"and the integer power of q at the natural number s is the power",
			"real_zpow(«q», n + 1 - int_of_num(«scGenus»)) = «q» ^ s",
			natural.Rw(),
			By(real_zpow.RealZpowDef, int_embed.EmbedNonneg.At(s), int_embed.OfNumRetract))
		a.Show(
			"casting the equation between natural numbers to ℝ is the statement",
			By(
				curve,
				EffectiveCountOverClasses.Read(L).At(k, A0, A1, A01, t, n),
				total,
				cast,
				power,
				real_construction.OfNumMul.At(a.TermAs[Nat]("card(k) - 1"), a.TermAs[Nat]("«classSum»")),
				real_construction.OfNumMul.At(a.TermAs[Nat]("card(«scPicZero»)"), value)))
	}),
})}

// ZetaSimplePole — with d the divisor index, the effective counts
// of a curve over a finite field vanish off the multiples of d, their series has
// a simple pole at one, and multiplying it by 1 − Tᵈ and 1 − qᵈTᵈ leaves a
// polynomial. A degree that is no multiple of d has no classes, so its class sum
// is empty, and past 2g − 2 a multiple of d follows the geometric tail;
// periodic-tail rationality turns these two facts into the pole and the
// polynomial.
var ZetaSimplePole = zetaSimplePoleThm{family.Add(registry.ProofEntry{
	Name: "ZetaSimplePole",
	Key:  "prop_e324f14cd18ae560",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "series_simple_pole_one(«scZeta») ∧ " +
			"polynomial_over(real_of_num(0), " +
			"    𝕌, " +
			"    polynomial_mul(real_add, " +
			"        real_of_num(0), " +
			"        real_mul, " +
			"        polynomial_mul(real_add, " +
			"            real_of_num(0), " +
			"            real_mul, " +
			"            «1−Tᵈ»(«scIndex»), " +
			"            «1−qᵈTᵈ»(«scIndex»)), " +
			"        «scZeta»)) ∧ " +
			"(∀n:num. ¬(«scIndex» ∣ n) ⇒ «scEffective»(n) = real_of_num(0))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			classes := a.Conjuncts(
				GroupPremises(curve, DivisorDegreeClasses.Read(L).At(k, A0, A1, A01, t)),
				"the index is positive",
				"it is the degree of a closed divisor",
				"the classes of each degree are counted")
			positive, counted := classes[0], classes[2]
			base := a.Have(
				"k is a finite subfield of L, so q is more than one",
				"1 < card(k)",
				By(curve, ConstantsAtLeastTwo.Read(L).At(k, A0, A1, A01, t)))
			picard := a.Have(
				"the degree-zero class group is not empty",
				"0 < card(«scPicZero»)",
				By(curve, smooth_curve_riemann_roch.DegreeZeroClassGroupFinite.Read(L).At(k, A0, A1, A01, t)))
			index := a.TermAs[Nat]("«scIndex»")
			vanishing := a.Have(
				"the effective count vanishes off the multiples of the index",
				"∀n:num. ¬(«scIndex» ∣ n) ⇒ «scEffective»(n) = &0",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					degree := b.TermAs[Int]("n")
					noClasses := b.Have(
						"no class has degree n",
						"«scClasses»(n) = ∅",
						By(
							b.Assume(),
							int_divides.OfNumDivides.At(index, n),
							counted.At(degree),
							cardinality.CardEqZero.At(b.TermAs[Set[_Class]]("«scClasses»(n)"))))
					b.Show(
						"so the sum over the classes of degree n is empty",
						By(
							noClasses,
							curve,
							EffectiveCountOverClasses.Read(L).At(k, A0, A1, A01, t, degree),
							nat_sum.Clauses))
				}))
			tail := a.Have(
				"from 2g on, the multiples of the index follow the tail formula",
				"∃N:num. ∀n:num. "+
					"    N ≤ n ∧ «scIndex» ∣ n ⇒ "+
					"    real_of_num(card(k) - 1) * «scEffective»(n) = "+
					"    real_of_num(card(«scPicZero»)) * "+
					"    (real_zpow(«q», n + &1 - int_of_num(«scGenus»)) - real_of_num(1))",
				Witness(a.TermAs[Nat]("2 * «scGenus»")),
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					past := b.Conjuncts(
						b.Assume(),
						"n is at least 2g",
						"the index divides n")
					beyond := b.Have(
						"so n exceeds 2g − 2 as an integer",
						"2 * «scGenus» - &2 < int_of_num(n)",
						ByArith(past[0], int_embed.OfNumLe.At(b.TermAs[Nat]("2 * «scGenus»"), n)))
					b.Show(
						"and n has the tail of the class sum",
						By(
							past[1],
							beyond,
							int_divides.OfNumDivides.At(index, n),
							curve,
							EffectiveCountTail.Read(L).At(k, A0, A1, A01, t, b.TermAs[Int]("n"))))
				}))
			a.Show(
				"periodic-tail rationality gives the pole and the polynomial",
				By(
					base,
					picard,
					positive,
					vanishing,
					tail,
					real_formal_series.PeriodicTailRationality.At(
						a.TermAs[Nat]("card(k)"),
						a.TermAs[Nat]("«scGenus»"),
						a.TermAs[Nat]("card(«scPicZero»)"),
						index,
						a.TermAs[Fun[Int, Real]]("«scEffective»"))))
		}),
})}

// ConstantExtensionCurve — over the constants with q^r elements the charts of a
// smooth curve are again a smooth curve. Its function field is the composite of K
// with those constants, a subfield of M, and they have q^r elements, the charts
// being the constant extensions of the charts of the curve.
var ConstantExtensionCurve = constantExtensionCurveThm{family.Add(registry.ProofEntry{
	Name: "ConstantExtensionCurve",
	Key:  "prop_704cac779ff0483d",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
			"0 < r",
		},
		Conclusion: "subfield(M, «composite»(r)) ∧ " +
			"smooth_finite_curve(restrict_field(M, «composite»(r)), " +
			"    «constants»(r), " +
			"    t, " +
			"    «constantChart»(r, A₀), " +
			"    «constantChart»(r, A₁), " +
			"    «constantChart»(r, A₀₁)) ∧ " +
			"card(«constants»(r)) = card(k) ^ r",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		r *Expr[Nat],
		algebraicallyClosed, inField, curve, positive Fact,
	) {
		unfolded := a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef)
		a.Show(
			"the composite, the curve in it, and the size of its constants",
			SplitConjAll(
				Case(
					"K is regular over k, so its composite with the constants is a subfield of M",
					By(
						algebraicallyClosed,
						inField,
						curve,
						positive,
						unfolded,
						curve_point_count.SmoothCurveRegular.Read(M).At(K, k, A0, A1, A01, t),
						constant_galois.ConstantCompositeData.Read(M).At(K, k, r))),
				Case(
					"the extended charts are a smooth curve in the composite",
					By(
						algebraicallyClosed,
						inField,
						curve,
						positive,
						curve_point_count.SmoothCurveConstantExtension.Read(M).At(K, k, A0, A1, A01, t, r))),
				Case(
					"the finite constants of degree r over k have q^r elements",
					By(
						algebraicallyClosed,
						inField,
						curve,
						positive,
						unfolded,
						curve_point_count.CurveChartsInField.Read(M).At(K, k, A0, A1, A01, t),
						finite_field.FiniteConstantsSubfield.Read(M).At(k, r),
						cardinality.HasSizeDef))))
	}),
})}

// IndexBaseChangeZetaIdentity — for r dividing the divisor index of the curve, the zeta
// series of the same curve over the constants with q^r elements, read at T^r, is
// the r-th power of the zeta series of the curve. Taking the r-th power and
// substituting T^r each multiply a counting sequence by r, so the two series
// have r times the same sequence. The substituted extended counts are the
// counts of the curve: at r·j by base change, and off the multiples of r both
// vanish, every closed point having degree a multiple of r. In characteristic
// zero a recurrence determines its series.
var IndexBaseChangeZetaIdentity = indexBaseChangeZetaIdentityThm{family.Add(registry.ProofEntry{
	Name: "IndexBaseChangeZetaIdentity",
	Key:  "prop_fbfaa63ca50ffd93",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A. ∀r:num.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
			"r ∣ «index»",
		},
		Conclusion: "series_substitute(real_ring, «extendedZeta»(r), r) = " +
			"polynomial_pow(real_add, real_of_num(0), real_mul, real_of_num(1), «zeta», r)",
		Abbrev: Abbrev{
			{Name: "pointCounts", Text: "λm:num. real_of_num(«count»(m))"},
			{Name: "extendedCounts", Text: "λm:num. real_of_num(«extendedCount»(r)(m))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, A0, A1, A01 *Expr[Set[A]],
		t *Expr[A],
		r *Expr[Nat],
		algebraicallyClosed, inField, curve, divides Fact,
	) {
		functionField := a.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(inField, field.SubfieldFieldOn.Read(M).At(K)))
		image := a.Conjuncts(
			a.Simplified(
				GroupPremises(curve, DivisorDegreeImage.Read(functionField).At(k, A0, A1, A01, t)),
				curve_point_count.InAmbient),
			"the index is positive",
			"and the degrees of the closed divisors are its multiples")
		multiples := image[1]
		index := a.TermAs[Nat]("«index»")
		positive := a.Have(
			"r divides the positive index, so it is positive",
			"0 < r",
			By(image[0], divides, nat_divides.ZeroDivides.At(index), nat_order.PosIffNonzero.At(r)))
		extension := a.Conjuncts(
			GroupPremises(
				algebraicallyClosed,
				inField,
				curve,
				positive,
				ConstantExtensionCurve.Read(M).At(K, k, A0, A1, A01, t, r)),
			"the composite of K with the constants of q^r elements is a subfield of M",
			"over those constants the charts are a smooth curve",
			"and the constants have q^r elements")
		compositeField, extended := extension[0], extension[1]
		constants := a.TermAs[Set[A]]("«constants»(r)")
		composite := a.TermAs[Set[A]]("«composite»(r)")
		chart0, chart1, chart01 :=
			a.TermAs[Set[A]]("«constantChart»(r, A₀)"),
			a.TermAs[Set[A]]("«constantChart»(r, A₁)"),
			a.TermAs[Set[A]]("«constantChart»(r, A₀₁)")
		series := a.Have(
			"the effective counts of the curve satisfy the recurrence with its point counts",
			"series_recurrence(real_ring, «zeta», «pointCounts»)",
			By(
				algebraicallyClosed,
				inField,
				curve,
				ZetaEulerProductAndLogDerivative.Read(M).At(K, k, A0, A1, A01, t)))
		extendedSeries := a.Have(
			"and so do those of the extended curve",
			"series_recurrence(real_ring, «extendedZeta»(r), «extendedCounts»)",
			By(
				algebraicallyClosed,
				compositeField,
				extended,
				ZetaEulerProductAndLogDerivative.Read(M).At(composite, constants, chart0, chart1, chart01, t)))
		numeral := a.Have(
			"r ones sum to the numeral r",
			"monoid_pow(real_add, &0, &1, r) = &r",
			Cite(real_ring.AddPowOne))
		power := a.Have(
			"the r-th power multiplies the counting sequence by r",
			"series_recurrence(real_ring, "+
				"    polynomial_pow(real_add, &0, real_mul, &1, «zeta», r), "+
				"    λn:num. &r * &«count»(n))",
			numeral.RwRev(),
			By(series, formal_series.RecurrencePower.Read(real_ring.CommRingOn), real_ring.RealRingDef))
		substituted := a.Have(
			"and substituting T^r multiplies the substituted counting sequence by r",
			"series_recurrence(real_ring, "+
				"    series_substitute(real_ring, «extendedZeta»(r), r), "+
				"    λn:num. &r * series_substitute(real_ring, «extendedCounts», r, n))",
			numeral.RwRev(),
			By(
				positive,
				extendedSeries,
				formal_series.RecurrenceSubstitute.Read(real_ring.CommRingOn),
				real_ring.RealRingDef))
		baseChange := a.Have(
			"the extended curve counts at j what the curve counts at r·j",
			"∀j:num. «extendedCount»(r)(j) = «count»(r * j)",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				nonzero := b.Unless(
					b.TermAs[Bool]("j = 0"),
					"at zero both counts are defined to be zero",
					Given(func(c *Argument, zero Fact) {
						c.Show(
							"the count at index zero is zero",
							By(zero, curve_point_count.CurveExtensionCountDef, nat_arith.MulZero))
					}))
				b.Show(
					"at positive j this is the base change of the count",
					By(
						algebraicallyClosed,
						inField,
						curve,
						positive,
						nonzero,
						nat_order.PosIffNonzero.At(j),
						curve_point_count.ExtensionCountBaseChange.Read(M).At(K, k, A0, A1, A01, t, r, j)))
			}))
		degrees := a.Have(
			"r divides the degree of every closed point",
			"∀P:prod(set(A), set(A)). «point»(P) ⇒ r ∣ «pointDegree»(P)",
			Derive(func(b *Argument) {
				P := b.FixAs[_LatticePair]("P")
				point := b.Assume()
				degree := b.TermAs[Int]("«pointDegree»(P)")
				pointDegree := b.TermAs[Nat]("«pointDegree»(P)")
				multipleOfIndex := b.Have(
					"P with coefficient one is a closed divisor of that degree, a "+
						"multiple of the index in the integers and so in the natural numbers",
					"«index» ∣ «pointDegree»(P)",
					By(
						inField,
						curve,
						point,
						multiples.At(degree),
						b.Simplified(
							closed_divisor.ClosedDivisorPoint.Read(functionField).At(k, A0, A1, A01, t, P, b.TermAs[Int]("1")),
							curve_point_count.InAmbient),
						int_real_lift.MulLeftIdentity.At(degree),
						int_divides.OfNumDivides.At(index, pointDegree)))
				b.Show(
					"and r divides the index",
					By(divides, multipleOfIndex, nat_divides.DividesTrans.At(r, index, pointDegree)))
			}))
		agreement := a.Have(
			"so substituting T^r in the extended counts gives the point counts of the curve",
			"∀n:num. series_substitute(real_ring, «extendedCounts», r, n) = real_of_num(«count»(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Cases(b.TermAs[Bool]("∃j:num. r * j = n"))
				b.When(
					"at a multiple r·j the substitution puts the extended count at j",
					func(c *Argument, multiple Fact) {
						j, nIsMultiple := c.UnpackAs[Nat](multiple, "j")
						c.Show(
							"which is the count of the curve at r·j",
							nIsMultiple.RwRev(),
							Simp(Fwd(formal_series.SeriesSubstituteAtMultiple)),
							By(baseChange.At(j)))
					})
				b.Otherwise(
					"off the multiples of r both vanish",
					func(c *Argument, absent Fact) {
						none := c.Have(
							"no closed point has degree dividing n, for r would divide n",
							"{P:prod(set(A), set(A)) | «point»(P) ∧ «pointDegree»(P) ∣ n} = ∅",
							BySets(absent, degrees, nat_divides.DividesTrans, nat_divides.DividesFactor))
						nPositive := c.Have(
							"n is positive, 0 being a multiple of r",
							"0 < n",
							By(absent, nat_arith.MulZero.At(r), nat_order.PosIffNonzero.At(n)))
						count := c.Have(
							"so the count at n is an empty sum",
							"«count»(n) = 0",
							By(
								algebraicallyClosed,
								inField,
								curve,
								nPositive,
								none,
								curve_point_count.ExtensionCountClosedPoints.Read(M).At(K, k, A0, A1, A01, t, n),
								nat_sum.Clauses))
						c.Show(
							"and the substituted sequence is zero off the multiples of r",
							By(absent, count, formal_series.SeriesSubstituteOffMultiples, real_ring.RealRingDef))
					})
			}))
		common := a.Simplified(substituted, Fwd(agreement))
		a.Show(
			"over ℝ, of characteristic zero, the recurrence with the common sequence determines the series",
			By(
				common,
				power,
				real_formal_series.RealCharacteristicZero,
				formal_series.RecurrenceDeterminesCoefficients.Read(real_formal_series.RealIntegralDomain)))
	}),
})}

// DegreeOneDivisorExists — the divisor index of a smooth curve over a finite
// field is one, so the curve has a closed divisor of degree one. Extending the
// constants to those with q^r elements, for r the index, gives another smooth
// curve, and the series of both have a simple pole at one. The base-change
// identity says the extended series with Tʳ substituted is the r-th power of the
// base series; the left side keeps a simple pole at one where the right side has
// a pole of order r, so r is one.
var DegreeOneDivisorExists = degreeOneDivisorExistsThm{family.Add(registry.ProofEntry{
	Name: "DegreeOneDivisorExists",
	Key:  "prop_96755439fa983ee4",
	Reading: "The divisor is integral and need not be effective. The argument proves no " +
		"rational-point existence and uses neither root modulus bounds nor the Hasse–Weil estimate.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"«curve»",
		},
		Conclusion: "«index» = 1 ∧ (∃D:(prod(set(A), set(A)) → int). «divisor»(D) ∧ «degree»(D) = 1)",
	},
		func(
			a *Argument,
			M field.FieldFact[on.M],
			K, k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			algebraicallyClosed, inField, curve Fact,
		) {
			functionField := a.Have(
				"K is a field under M's operations",
				"field_on(restrict_field(M, K))",
				By(inField, field.SubfieldFieldOn.Read(M).At(K)))
			classes := a.Conjuncts(
				a.Simplified(
					GroupPremises(curve, DivisorDegreeClasses.Read(functionField).At(k, A0, A1, A01, t)),
					curve_point_count.InAmbient),
				"the index is positive",
				"it is the degree of a closed divisor",
				"the classes of each degree are counted")
			positive, attained := classes[0], classes[1]
			r := a.TermAs[Nat]("«index»")
			extension := a.Conjuncts(
				GroupPremises(
					algebraicallyClosed,
					inField,
					curve,
					classes[0],
					ConstantExtensionCurve.Read(M).At(K, k, A0, A1, A01, t, r)),
				"the composite of K with the constants of q^r elements is a subfield of M",
				"the curve extended to those constants is a smooth curve in it",
				"and the constants have q^r elements")
			compositeField := extension[0]
			extendedField := a.Have(
				"the composite is a field under M's operations",
				"field_on(restrict_field(M, «composite»(«index»)))",
				By(compositeField, field.SubfieldFieldOn.Read(M).At(a.TermAs[Set[A]]("«composite»(«index»)"))))
			pole := a.Have(
				"the series of the curve has a simple pole at one",
				"series_simple_pole_one(«zeta»)",
				By(
					a.Simplified(
						GroupPremises(curve, ZetaSimplePole.Read(functionField).At(k, A0, A1, A01, t)),
						curve_point_count.InAmbient)))
			extendedPole := a.Have(
				"and so has the series of the extended curve",
				"series_simple_pole_one(«extendedZeta»(«index»))",
				By(
					a.Simplified(
						GroupPremises(extension[1], ZetaSimplePole.Read(extendedField).At(
							a.TermAs[Set[A]]("«constants»(«index»)"),
							a.TermAs[Set[A]]("«constantChart»(«index», A₀)"),
							a.TermAs[Set[A]]("«constantChart»(«index», A₁)"),
							a.TermAs[Set[A]]("«constantChart»(«index», A₀₁)"),
							t)),
						curve_point_count.InAmbient)))
			one := a.Have(
				"the extended series at Tʳ is the r-th power of the "+
					"base series, which two simple poles allow only at r = 1",
				"«index» = 1",
				By(
					positive,
					pole,
					extendedPole,
					algebraicallyClosed,
					inField,
					curve,
					nat_divides.DividesRefl.At(r),
					IndexBaseChangeZetaIdentity.Read(M).At(K, k, A0, A1, A01, t, r),
					real_formal_series.SimplePolePowerSubstitution.At(
						a.TermAs[Fun[Nat, Real]]("«zeta»"),
						a.TermAs[Fun[Nat, Real]]("«extendedZeta»(«index»)"),
						r)))
			a.Show(
				"the closed divisor of degree the index then has degree one",
				By(one, attained))
		}),
})}
