package smooth_curve_riemann_roch

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/divisor_lattice_correspondence"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

// EffectiveDivisorWeighted — an effective closed divisor, its coefficients read
// as natural numbers, is a weighted effective function of the closed points,
// and its degree is the cast of the weighted degree. The two functions have one
// support, and the two degrees are sums over it, term by term casts of each
// other, since the cast of a finite sum of natural numbers is the sum of the
// casts.
var EffectiveDivisorWeighted = effectiveDivisorWeightedThm{family.Add(registry.ProofEntry{
	Name: "EffectiveDivisorWeighted",
	Key:  "prop_fa45cbdf618cf7d9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
			"∀P:prod(set(A), set(A)). int_of_num(0) ≤ D(P)",
		},
		Conclusion: "weighted_effective({P:prod(set(A), set(A)) | «scPoint»(P)}, " +
			"    «scPointDegree», " +
			"    «counted») ∧ " +
			"«scDegree»(D) = int_of_num(weighted_degree(«scPointDegree», «counted»))",
		Abbrev: Abbrev{
			{Name: "counted", Text: "λP:prod(set(A), set(A)). num_of_int(D(P))"},
			{Name: "support", Text: "fun_support(int_of_num(0), D)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_IdealPair, Int],
			curve, divisor, nonnegative Fact,
		) {
			closed := a.Conjuncts(
				a.Unfolded(divisor, closed_divisor.ClosedDivisorDef),
				"the support of D is finite",
				"its pairs are closed points")
			integer := a.Have(
				"a nonnegative coefficient is the cast of its natural number",
				"∀P:prod(set(A), set(A)). num_of_int(D(P)) = D(P)",
				a.ForEach(func(P *Expr[_IdealPair]) Action {
					return By(nonnegative.At(P), int_embed.NumOfIntSection)
				}))
			vanishes := a.Have(
				"so the natural number vanishes exactly where the coefficient does",
				"∀P:prod(set(A), set(A)). num_of_int(D(P)) = 0 ⇔ D(P) = 0",
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					b.Show(
						"the cast is one-to-one",
						By(
							Normalized,
							integer.At(P),
							int_embed.OfNumEq.At(b.TermAs[Nat]("num_of_int(D(P))"), b.TermAs[Nat]("0"))))
				}))
			supports := a.Have(
				"and the two functions have one support",
				"fun_support(0, λP:prod(set(A), set(A)). num_of_int(D(P))) = «support»",
				BySets(vanishes))
			closedPoints := a.Have(
				"a point of the support is a closed point, of positive degree",
				"∀x:prod(set(A), set(A)). num_of_int(D(x)) ≠ 0 ⇒ «scPoint»(x) ∧ 0 < «scPointDegree»(x)",
				Derive(func(b *Argument) {
					x := b.FixAs[_IdealPair]("x")
					nonzero := b.Assume()
					point := b.Have(
						"x lies on the support of D",
						"«scPoint»(x)",
						By(nonzero, vanishes.At(x), closed[1].At(x)))
					b.Show(
						"a closed point has positive degree",
						By(curve, point, smooth_curve.ClosedPointsFiniteByDegree.Read(L).At(k, A0, A1, A01, t)))
				}))
			effective := a.Have(
				"the support is finite and consists of closed points of positive degree",
				"weighted_effective({P:prod(set(A), set(A)) | «scPoint»(P)}, «scPointDegree», «counted»)",
				Simp(Fwd(weighted_divisors.WeightedEffectiveDef)),
				supports.Rw(),
				BySets(closed[0], closedPoints))
			integers := a.Have(
				"the integers are a commutative monoid under addition",
				"comm_monoid_on(𝕌, int_add, 0)",
				By(
					int_real_lift.AddMonoid,
					comm_monoid.CommMonoidOnUniverse.At(a.TermAs[Fun2[Int, Int, Int]]("int_add"), a.TermAs[Int]("0"))))
			casts := a.Have(
				"the cast of a finite sum of natural numbers is the sum of the casts",
				Statement{
					Binders:    "∀s:set(prod(set(A), set(A))). ∀f:(prod(set(A), set(A)) → num).",
					Hypotheses: []string{"finite(s)"},
					Conclusion: "nat_sum(s, f) = module_sum(int_add, &0, s, λx:prod(set(A), set(A)). int_of_num(f(x)))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[_IdealPair]]("s")
					b.FixAs[Fun[_IdealPair, Nat]]("f")
					finite := b.Assume()
					b.Show(
						"by induction on the finite set s",
						ByInduction(
							finite_set.FiniteInductFresh,
							finite,
							Case(
								"both empty sums are 0",
								By(Normalized, nat_sum.Clauses, module.ModuleSumEmpty)),
							Case(
								"a new index adds its term to both sums",
								Derive(func(c *Argument) {
									x := c.FixAs[_IdealPair]("x")
									u := c.FixAs[Set[_IdealPair]]("u")
									carried := c.Conjuncts(
										c.Assume(),
										"the two sums agree on u",
										"x is a new index of u",
										"u is finite")
									c.Show(
										"each takes the term at x in front of the sum over u",
										By(
											carried[0],
											carried[1],
											carried[2],
											nat_sum.Clauses,
											int_embed.OfNumAdd,
											set_basic.InUniv,
											Read(module.ModuleSumInsertMonoid, integers).At(
												u,
												x,
												c.TermAs[Fun[_IdealPair, Int]]("λy:prod(set(A), set(A)). f(y)"))))
								}))))
				}))
			terms := a.Have(
				"term by term the two degrees are casts of each other",
				"∀P:prod(set(A), set(A)). D(P) * «scPointDegree»(P) = «scPointDegree»(P) * num_of_int(D(P))",
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					b.Show(
						"the cast of a product is the product of the casts",
						ByArith(
							integer.At(P),
							int_embed.OfNumMul.At(b.TermAs[Nat]("«scPointDegree»(P)"), b.TermAs[Nat]("num_of_int(D(P))"))))
				}))
			support := a.TermAs[Set[_IdealPair]]("«support»")
			degree := a.Have(
				"the degree of D is the cast of the weighted degree",
				"«scDegree»(D) = int_of_num(weighted_degree(«scPointDegree», «counted»))",
				Simp(Fwd(closed_divisor.ClosedDivisorDegreeDef), Fwd(weighted_divisors.WeightedDegreeDef)),
				supports.Rw(),
				By(
					closed[0],
					terms,
					casts.At(
						support,
						a.TermAs[Fun[_IdealPair, Nat]]("λP:prod(set(A), set(A)). «scPointDegree»(P) * num_of_int(D(P))")),
					module.ModuleSumCongruence.At(
						a.TermAs[Fun2[Int, Int, Int]]("int_add"),
						a.TermAs[Int]("0"),
						support,
						a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). D(P) * «scPointDegree»(P)"),
						a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). «scPointDegree»(P) * num_of_int(D(P))"))))
			a.Show(
				"the coefficients are weighted effective, and the degree is the cast of their weighted degree",
				By(effective, degree))
		}),
})}

// DegreeZeroClassGroupFinite — Pic⁰ of a smooth curve over a finite field is
// finite and not empty. Let E be g times a closed point P₀, of degree e ≥ g. A
// class of degree zero, translated by E, has degree at least g, so it has a
// nonzero section, whose zeros are an effective divisor F of degree e: the class
// is the class of F − E. There are finitely many effective divisors of degree
// e, so Pic⁰ lies in a finite image; and it holds the class of the structure
// pair.
var DegreeZeroClassGroupFinite = degreeZeroClassGroupFiniteThm{family.Add(registry.ProofEntry{
	Name: "DegreeZeroClassGroupFinite",
	Key:  "prop_1e66afb267fb2ab",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "finite(curve_pic_zero(field_ring(L), k, A₀, A₁, A₀₁)) ∧ " +
			"0 < card(curve_pic_zero(field_ring(L), k, A₀, A₁, A₀₁))",
		Abbrev: Abbrev{
			{Name: "picZero", Text: "curve_pic_zero(field_ring(L), k, A₀, A₁, A₀₁)"},
			{Name: "genus", Text: "curve_genus(field_ring(L), k, A₀, A₁, A₀₁)"},
			{Name: "pairDegree", Text: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁)"},
			{Name: "pairClass", Text: "curve_pair_class(field_ring(L))"},
			{Name: "baseDegree", Text: "int_of_num(«genus») * «scPointDegree»(P₀)"},
			{Name: "effective", Text: "{D:prod(set(A), set(A)) → num | " +
				"    weighted_effective({P:prod(set(A), set(A)) | «scPoint»(P)}, «scPointDegree», D) ∧ " +
				"    weighted_degree(«scPointDegree», D) = «genus» * «scPointDegree»(P₀)}"},
			{Name: "translate", Text: "λD:prod(set(A), set(A)) → num. " +
				"    «pairClass»(«scPair»(λP:prod(set(A), set(A)). int_of_num(D(P)) - E(P)))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			correspondence := divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(
				k, A0, A1, A01, t)
			overLine := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			data := algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)
			points := a.Conjuncts(
				GroupPremises(curve, smooth_curve.ClosedPointsFiniteByDegree.Read(L).At(k, A0, A1, A01, t)),
				"the curve has a closed point",
				"closed points have finite positive degree",
				"finitely many have bounded degree, and finitely many effective divisors each degree")
			P0, point := a.UnpackAs[_IdealPair](points[0], "P₀")
			_, baseDefinition := a.LetAs[Fun[_IdealPair, Int]](
				"E", "λQ:prod(set(A), set(A)). COND(Q = P₀, int_of_num(«genus»), 0)")
			base := a.Have(
				"E, g times P₀, is a closed divisor of g times the degree of P₀",
				"«scDivisor»(E) ∧ «scDegree»(E) = «baseDegree»",
				baseDefinition.Rw(),
				By(
					curve,
					point,
					closed_divisor.ClosedDivisorPoint.Read(L).At(k, A0, A1, A01, t, P0, a.TermAs[Int]("«genus»"))))
			basePair := a.Have(
				"its pair is invertible, of that degree",
				"«scInvertible»(«scPair»(E)) ∧ «pairDegree»(«scPair»(E)) = «scDegree»(E)",
				By(curve, base, correspondence))
			pairE := a.TermAs[_IdealPair]("«scPair»(E)")
			sections := a.Have(
				"a pair of degree zero, translated by E, is a multiple of an effective divisor of the degree of E",
				Statement{
					Binders: "∀N:prod(set(A), set(A)).",
					Hypotheses: []string{
						"«scInvertible»(N)",
						"«pairDegree»(N) = 0",
					},
					Conclusion: "∃s:A. ∃F:(prod(set(A), set(A)) → int). " +
						"    s ∈ L.carrier ∧ " +
						"    s ≠ L.zero ∧ " +
						"    «scDivisor»(F) ∧ " +
						"    (∀P:prod(set(A), set(A)). 0 ≤ F(P)) ∧ " +
						"    «scDegree»(F) = «baseDegree» ∧ " +
						"    «scMul»(N, «scPair»(E)) = lattice_pair_scale(s, «scPair»(F))",
				},
				Derive(func(b *Argument) {
					N := b.FixAs[_IdealPair]("N")
					given := b.Conjuncts(
						b.Assume(),
						"N is invertible",
						"of degree zero")
					twisted := b.TermAs[_IdealPair]("«scMul»(N, «scPair»(E))")
					product := b.Have(
						"the translate is invertible, and the degrees add",
						"«scInvertible»(«scMul»(N, «scPair»(E))) ∧ "+
							"«pairDegree»(«scMul»(N, «scPair»(E))) = «pairDegree»(N) + «pairDegree»(«scPair»(E))",
						By(
							overLine,
							data,
							given[0],
							basePair,
							invertible_lattice_pair.InvertibleLatticeProduct.Read(L).At(A0, A1, A01, t, N, pairE),
							curve_degree.DegreeAdditive.Read(L).At(k, A0, A1, A01, t, N, pairE)))
					large := b.Have(
						"so its degree is at least g",
						"int_of_num(«genus») ≤ «pairDegree»(«scMul»(N, «scPair»(E)))",
						ByArith(
							given[1],
							product,
							basePair,
							base,
							point,
							points[1].At(P0),
							int_embed.EmbedNonneg.At(b.TermAs[Nat]("«genus»"))))
					s, section := b.ObtainAs[A](
						"so it has a nonzero section",
						"∃s:A. s ∈ fst(«scMul»(N, «scPair»(E))) ∩ snd(«scMul»(N, «scPair»(E))) ∧ s ≠ L.zero",
						By(
							overLine,
							product,
							large,
							curve_degree.LargeDegreeHasSection.Read(L).At(k, A0, A1, A01, t, twisted)))
					sParts := b.Conjuncts(
						section,
						"s lies on both charts",
						"s is not zero")
					inL := b.Have(
						"s lies in L",
						"s ∈ L.carrier",
						BySets(
							sParts[0],
							product,
							invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, twisted)))
					F, effective := b.UnpackAs[Fun[_IdealPair, Int]](
						b.Have(
							"its zeros are an effective divisor F, and the translate is s times the pair of F",
							"∃F:(prod(set(A), set(A)) → int). "+
								"    «scDivisor»(F) ∧ "+
								"    (∀P:prod(set(A), set(A)). 0 ≤ F(P)) ∧ "+
								"    «scMul»(N, «scPair»(E)) = lattice_pair_scale(s, «scPair»(F))",
							By(curve, product, sParts[0], sParts[1], correspondence)),
						"F")
					fParts := b.Conjuncts(
						effective,
						"F is a closed divisor",
						"F is effective",
						"the translate is s times the pair of F")
					pairF := b.TermAs[_IdealPair]("«scPair»(F)")
					effectivePair := b.Have(
						"the pair of F is invertible, of the degree of F",
						"«scInvertible»(«scPair»(F)) ∧ «pairDegree»(«scPair»(F)) = «scDegree»(F)",
						By(curve, fParts[0], correspondence))
					scaled := b.Have(
						"scaling by s keeps the degree",
						"«pairDegree»(lattice_pair_scale(s, «scPair»(F))) = «pairDegree»(«scPair»(F))",
						By(
							overLine,
							effectivePair,
							sParts[1],
							curve_degree.DegreeScale.Read(L).At(k, A0, A1, A01, t, b.MemberOf[on.L](s, inL), pairF)))
					degree := b.Have(
						"so F has the degree of E",
						"«scDegree»(F) = «baseDegree»",
						ByArith(effectivePair, scaled, fParts[2], product, given[1], basePair, base))
					b.Show(
						"s and F are the witnesses",
						Witness(s),
						Witness(F),
						By(inL, sParts[1], fParts[0], fParts[1], degree, fParts[2]))
				}))
			counted := a.Have(
				"the coefficients of an effective divisor of that degree, as natural "+
					"numbers, are an effective function of g times the degree of P₀",
				Statement{
					Binders: "∀F:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{
						"«scDivisor»(F)",
						"∀P:prod(set(A), set(A)). 0 ≤ F(P)",
						"«scDegree»(F) = «baseDegree»",
					},
					Conclusion: "(λP:prod(set(A), set(A)). num_of_int(F(P))) ∈ «effective»",
				},
				Derive(func(b *Argument) {
					F := b.FixAs[Fun[_IdealPair, Int]]("F")
					given := b.Conjuncts(
						b.Assume(),
						"F is a closed divisor",
						"F is effective",
						"of the degree of E")
					weighted := b.Conjuncts(
						GroupPremises(curve, given[0], given[1], EffectiveDivisorWeighted.Read(L).At(k, A0, A1, A01, t, F)),
						"its coefficients are weighted effective",
						"and its degree is the cast of their weighted degree")
					genus := b.TermAs[Nat]("«genus»")
					pointDegree := b.TermAs[Nat]("«scPointDegree»(P₀)")
					total := b.Have(
						"their weighted degree is g times the degree of P₀",
						"weighted_degree(«scPointDegree», λP:prod(set(A), set(A)). num_of_int(F(P))) = "+
							"«genus» * «scPointDegree»(P₀)",
						By(
							weighted[1],
							given[2],
							int_embed.OfNumEq.At(
								b.TermAs[Nat]("weighted_degree(«scPointDegree», λP:prod(set(A), set(A)). num_of_int(F(P)))"),
								b.TermAs[Nat]("«genus» * «scPointDegree»(P₀)")),
							int_embed.OfNumMul.At(genus, pointDegree)))
					b.Show(
						"they are weighted effective, of weighted degree g times the degree of P₀",
						By(weighted[0], total))
				}))
			classes := a.Have(
				"N is a multiple of the pair of F − E, so the two have one class",
				Statement{
					Binders: "∀N:prod(set(A), set(A)). ∀s:A. ∀F:(prod(set(A), set(A)) → int).",
					Hypotheses: []string{
						"«scInvertible»(N)",
						"s ∈ L.carrier",
						"s ≠ L.zero",
						"«scDivisor»(F)",
						"«scMul»(N, «scPair»(E)) = lattice_pair_scale(s, «scPair»(F))",
					},
					Conclusion: "«pairClass»(N) = «pairClass»(«scPair»(λP:prod(set(A), set(A)). F(P) + -E(P)))",
				},
				Derive(func(b *Argument) {
					N := b.FixAs[_IdealPair]("N")
					s := b.FixAs[A]("s")
					F := b.FixAs[Fun[_IdealPair, Int]]("F")
					given := b.Conjuncts(
						b.Assume(),
						"N is invertible",
						"s lies in L",
						"s is not zero",
						"F is a closed divisor",
						"the translate of N is s times the pair of F")
					negated := b.Have(
						"−E is a closed divisor, and its pair is the inverse of the pair of E",
						"«scDivisor»(λP:prod(set(A), set(A)). -E(P)) ∧ "+
							"«scPair»(λP:prod(set(A), set(A)). -E(P)) = «scInverse»(«scPair»(E))",
						By(
							curve,
							base,
							closed_divisor.ClosedDivisorNegate.Read(L).At(
								k, A0, A1, A01, t, b.TermAs[Fun[_IdealPair, Int]]("E"))))
					difference := b.Have(
						"F − E is a closed divisor, and its pair is the pair of F over the pair of E",
						"«scDivisor»(λP:prod(set(A), set(A)). F(P) + -E(P)) ∧ "+
							"«scPair»(λP:prod(set(A), set(A)). F(P) + -E(P)) = «scMul»(«scPair»(F), «scInverse»(«scPair»(E)))",
						By(
							curve,
							given[3],
							negated,
							closed_divisor.ClosedDivisorAdd.Read(L).At(
								k, A0, A1, A01, t, F, b.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). -E(P)"))))
					pairF := b.TermAs[_IdealPair]("«scPair»(F)")
					inverse := b.TermAs[_IdealPair]("«scInverse»(«scPair»(E))")
					invertibleF := b.Have(
						"the pair of F is invertible",
						"«scInvertible»(«scPair»(F))",
						By(curve, given[3], correspondence))
					invertibleInverse := b.Have(
						"and so is the inverse of the pair of E",
						"«scInvertible»(«scInverse»(«scPair»(E)))",
						By(
							overLine,
							data,
							basePair,
							invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, pairE)))
					regrouped := b.Have(
						"scaling passes through the product",
						"«scMul»(lattice_pair_scale(s, «scPair»(F)), «scInverse»(«scPair»(E))) = "+
							"lattice_pair_scale(s, «scMul»(«scPair»(F), «scInverse»(«scPair»(E))))",
						By(
							overLine,
							data,
							invertibleF,
							invertibleInverse,
							invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, pairF),
							invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, inverse),
							invertible_lattice_pair.ScaleMulAssoc.Read(L).At(
								A0, A1, A01, t, b.MemberOf[on.L](s, given[1]), pairF, inverse)))
					multiple := b.Have(
						"so N is s times the pair of F − E",
						"N = lattice_pair_scale(s, «scPair»(λP:prod(set(A), set(A)). F(P) + -E(P)))",
						By(
							curve,
							given[0],
							basePair,
							given[4],
							regrouped,
							difference,
							closed_divisor.PairQuotient.Read(L).At(k, A0, A1, A01, t, N, pairE)))
					pairDifference := b.TermAs[_IdealPair]("«scPair»(λP:prod(set(A), set(A)). F(P) + -E(P))")
					differencePair := b.Have(
						"the pair of F − E is invertible",
						"«scInvertible»(«scPair»(λP:prod(set(A), set(A)). F(P) + -E(P)))",
						By(curve, difference, correspondence))
					related := b.Have(
						"and N is a nonzero multiple of it",
						"∃a:A. "+
							"    a ∈ L.carrier ∧ "+
							"    a ≠ L.zero ∧ "+
							"    N = lattice_pair_scale(a, «scPair»(λP:prod(set(A), set(A)). F(P) + -E(P)))",
						Witness(s),
						By(given[1], given[2], multiple))
					b.Show(
						"so the two have one class",
						By(
							overLine,
							data,
							differencePair,
							given[0],
							related,
							curve_degree.PairClassEqIff.Read(L).At(A0, A1, A01, t, pairDifference, N)))
				}))
			cover := a.Have(
				"so Pic⁰ lies in the image of those functions under D ↦ the class of D − E",
				"«picZero» ⊆ image(«translate», «effective»)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					X := b.FixAs[Set[_IdealPair]]("X")
					member := b.Assume()
					N, pair := b.ObtainAs[_IdealPair](
						"X is the class of an invertible pair N of degree zero",
						"∃N:prod(set(A), set(A)). «scInvertible»(N) ∧ «pairDegree»(N) = 0 ∧ X = «pairClass»(N)",
						By(overLine, member, curve_degree.InPicZero.Read(L).At(k, A0, A1, A01, t, X)))
					given := b.Conjuncts(
						pair,
						"N is invertible",
						"of degree zero",
						"X is its class")
					s, F, translated := b.Unpack2As[A, Fun[_IdealPair, Int]](
						GroupPremises(given[0], given[1], sections.At(N)), "s", "F")
					parts := b.Conjuncts(
						translated,
						"s lies in L",
						"s is not zero",
						"F is a closed divisor",
						"F is effective",
						"of the degree of E",
						"the translate of N is s times the pair of F")
					effectiveFunction := b.Have(
						"the coefficients of F are such a function",
						"(λP:prod(set(A), set(A)). num_of_int(F(P))) ∈ «effective»",
						By(parts[2], parts[3], parts[4], counted.At(F)))
					classX := b.Have(
						"X is the class of F − E",
						"X = «pairClass»(«scPair»(λP:prod(set(A), set(A)). F(P) + -E(P)))",
						By(given[0], given[2], parts[0], parts[1], parts[2], parts[5], classes.At(N, s, F)))
					reading := b.Have(
						"and F − E is the difference of the cast of its coefficients and E",
						"(λP:prod(set(A), set(A)). int_of_num(num_of_int(F(P))) - E(P)) = "+
							"(λP:prod(set(A), set(A)). F(P) + -E(P))",
						Funext(),
						Derive(func(c *Argument) {
							P := c.FixAs[_IdealPair]("P")
							c.Show(
								"F is nonnegative at P",
								ByArith(parts[3].At(P), int_embed.NumOfIntSection.At(c.TermAs[Int]("F(P)"))))
						}))
					b.Show(
						"so X is the image of that function",
						Simp(Fwd(set_basic.InImage)),
						Witness(b.TermAs[Fun[_IdealPair, Nat]]("λP:prod(set(A), set(A)). num_of_int(F(P))")),
						reading.Rw(),
						By(classX, effectiveFunction))
				}))
			translate := a.TermAs[Fun[Fun[_IdealPair, Nat], Set[_IdealPair]]]("«translate»")
			divisors := a.TermAs[Set[Fun[_IdealPair, Nat]]]("«effective»")
			pic := a.TermAs[Set[Set[_IdealPair]]]("«picZero»")
			finite := a.Have(
				"finitely many functions are effective of that degree, so their image and Pic⁰ are finite",
				"finite(«picZero»)",
				By(
					points[2].At(a.TermAs[Nat]("«genus» * «scPointDegree»(P₀)")),
					cover,
					finite_set.FiniteImage.At(translate, divisors),
					finite_set.FiniteSubset.At(pic, a.TermAs[Set[Set[_IdealPair]]]("image(«translate», «effective»)"))))
			structureClass := a.TermAs[Set[_IdealPair]]("«pairClass»((A₀, A₁))")
			occupied := a.Have(
				"the structure pair is invertible, of degree zero, so its class is such a class",
				"∃N:prod(set(A), set(A)). "+
					"    «scInvertible»(N) ∧ «pairDegree»(N) = 0 ∧ «pairClass»((A₀, A₁)) = «pairClass»(N)",
				Witness(a.TermAs[_IdealPair]("(A₀, A₁)")),
				By(overLine, data, curve_degree.DegreeStructure.Read(L).At(k, A0, A1, A01)))
			nonempty := a.Have(
				"and Pic⁰ is not empty",
				"«picZero» ≠ ∅",
				By(
					overLine,
					occupied,
					curve_degree.InPicZero.Read(L).At(k, A0, A1, A01, t, structureClass),
					set_basic.NotInEmpty.At(structureClass)))
			a.Show(
				"Pic⁰ is finite, and a finite set that is not empty has positive cardinality",
				ByArith(finite, nonempty, cardinality.CardEqZero.At(pic)))
		}),
})}

// ClassOfDifference — the class of a difference of closed divisors is the quotient
// of their classes. The pair of a difference is the product of the first pair with
// the inverse of the second, and the classes of invertible pairs multiply and
// invert as the pairs do.
var ClassOfDifference = classOfDifferenceThm{family.Add(registry.ProofEntry{
	Name: "ClassOfDifference",
	Key:  "prop_6cb5f6317c328cc9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀E D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(E)",
			"«scDivisor»(D)",
		},
		Conclusion: "curve_class_mul(field_ring(L), " +
			"    A₀, " +
			"    A₁, " +
			"    curve_pair_class(field_ring(L), «scPair»(E)), " +
			"    curve_class_inverse(field_ring(L), A₀, A₁, curve_pair_class(field_ring(L), «scPair»(D)))) = " +
			"curve_pair_class(field_ring(L), «scPair»(λP:prod(set(A), set(A)). E(P) - D(P)))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E, D *Arrow[_IdealPair, Int],
			curve, divisorE, divisorD Fact,
		) {
			overLine := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			pairs := a.Have(
				"the pairs of E and D are invertible, and so is the inverse of the pair of D",
				"«scInvertible»(«scPair»(E)) ∧ "+
					"«scInvertible»(«scPair»(D)) ∧ "+
					"«scInvertible»(«scInverse»(«scPair»(D)))",
				By(
					curve,
					divisorE,
					divisorD,
					divisor_lattice_correspondence.WeightedDivisorLatticeCorrespondence.Read(L).At(k, A0, A1, A01, t),
					divisor_lattice_correspondence.InvertiblePairLaws.Read(L).At(k, A0, A1, A01, t)))
			pairOfE := a.TermAs[_IdealPair]("«scPair»(E)")
			pairOfD := a.TermAs[_IdealPair]("«scPair»(D)")
			multiplied := a.Have(
				"the classes multiply and invert as the pairs do",
				"curve_class_mul(field_ring(L), "+
					"    A₀, "+
					"    A₁, "+
					"    curve_pair_class(field_ring(L), «scPair»(E)), "+
					"    curve_class_inverse(field_ring(L), A₀, A₁, curve_pair_class(field_ring(L), «scPair»(D)))) = "+
					"curve_pair_class(field_ring(L), «scMul»(«scPair»(E), «scInverse»(«scPair»(D))))",
				By(
					overLine,
					algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
					pairs,
					curve_degree.PairClassMul.Read(L).At(
						A0, A1, A01, t, pairOfE, a.TermAs[_IdealPair]("«scInverse»(«scPair»(D))")),
					curve_degree.PairClassInverse.Read(L).At(A0, A1, A01, pairOfD)))
			pairOfDifference := a.Have(
				"the pair of E − D is the pair of E times the inverse of the pair of D",
				"«scPair»(λP:prod(set(A), set(A)). E(P) - D(P)) = «scMul»(«scPair»(E), «scInverse»(«scPair»(D)))",
				By(curve, divisorE, divisorD, closed_divisor.ClosedDivisorSub.Read(L).At(k, A0, A1, A01, t, E, D)))
			a.Show(
				"so the class of E − D is the quotient of the classes",
				pairOfDifference.Rw(),
				By(multiplied))
		}),
})}
