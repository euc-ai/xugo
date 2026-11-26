// genus.go — the genus of an integral plane model: its structure pair is the
// free line pair along the powers zⁱ below deg F, zⁱ twisted by −bi, and its
// genus, h¹ of that pair on the line, is the sum of bi − 1 over 0 < i < deg F.

package plane_model

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"

	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line_free_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// PlaneStructurePairFree — the structure pair of a plane model is the free
// line pair along the powers of z below deg F, each power zⁱ twisted by −bi:
// chart zero, k[t][z], is the k[t]-span of the powers of z, F being monic over
// k[t] with z a root; chart one, k[1/t][w] with w = t^(−b) z, is the
// k[1/t]-span of the powers of w, the scaled equation being monic over k[1/t]
// of degree deg F with w a root (IntegralPowerSpan, read in K); and the
// twisted power t^(−bi) zⁱ is wⁱ.
var PlaneStructurePairFree = planeStructurePairFreeThm{family.Add(registry.ProofEntry{
	Name: "PlaneStructurePairFree",
	Key:  "prop_42beea6853cace2f",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num. ∀N:(A → int).",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
			"∀i:num. i < polynomial_degree(F) ⇒ N(monoid_pow(M.mul, M.one, z, i)) = -&(b * i)",
		},
		Conclusion: "(«pmChart0», «pmChart1») = " +
			"projective_line_free_pair(restrict_field(M, K), k, t, «pmPowersZ», N)",
		Abbrev: Abbrev{
			{Name: "ringOver", Text: "restrict_ring(field_ring(restrict_field(M, K)))"},
			{Name: "vectors", Text: "regular_module(field_ring(restrict_field(M, K)))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		N *Arrow[A, Int],
		subfieldK, model, twisted Fact,
	) {
		multiplicative := comm_ring.MulMonoidOn.Read(field.RingOn.Read(M))
		ops, functionField := a.TermAs[FieldOps[A]]("M"), a.TermAs[FieldOps[A]]("restrict_field(M, K)")
		chart0, chart1, overlap :=
			a.TermAs[Set[A]]("«pmChart0»"), a.TermAs[Set[A]]("«pmChart1»"), a.TermAs[Set[A]]("«pmOverlap»")
		line0, line1 := a.TermAs[Set[A]]("«pmPolynomials»"), a.TermAs[Set[A]]("«pmInversePolynomials»")
		u, w, G :=
			a.TermAs[A]("M.inv(t)"), a.TermAs[A]("«pmGenerator»"), a.TermAs[Fun[Nat, A]]("«pmScaled»")
		points := a.Conjuncts(
			a.Have(
				"read in M, t and z lie in K and in M",
				"t ∈ K ∧ z ∈ K ∧ t ∈ M.carrier ∧ z ∈ M.carrier",
				By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
			"t lies in K",
			"z lies in K",
			"t lies in M",
			"z lies in M")
		tInK, zInK := points[0], points[1]
		tm, zm := a.MemberOf[on.M](t, points[2]), a.MemberOf[on.M](z, points[3])
		um := field.InvIn.Read(M).At(tm)
		scale := comm_monoid.PowIn.Read(multiplicative).At(um, b)
		wInK := a.Have(
			"w = t^(−b) z lies in K, a subfield holding t and z",
			"«pmGenerator» ∈ K",
			By(
				subfieldK,
				tInK,
				zInK,
				field.SubfieldInv.At(ops, K, t),
				field.SubfieldPowerIn.Read(M).At(K, u, b),
				field.SubfieldMul.At(ops, K, a.TermAs[A]("monoid_pow(M.mul, M.one, M.inv(t), b)"), z)))

		// Each chart is spanned, over its line, by the powers of its generator.
		function := a.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
		sameImages := a.Conjuncts(
			a.Have(
				"k[t], k[1/t], k[t][z] and k[1/t][w] read in K are those "+
					"read in M, a polynomial evaluating by the operations alone",
				"«pmPolynomialsInK» = «pmPolynomials» ∧ "+
					"polynomial_image(field_ring(restrict_field(M, K)), k, M.inv(t)) = «pmInversePolynomials» ∧ "+
					"polynomial_image(field_ring(restrict_field(M, K)), «pmPolynomials», z) = «pmImage0» ∧ "+
					"polynomial_image(field_ring(restrict_field(M, K)), «pmInversePolynomials», «pmGenerator») = "+
					"«pmImage1»",
				By(
					algebraic_element.PolynomialsOverRestriction.At(ops, K, k, t),
					algebraic_element.PolynomialsOverRestriction.At(ops, K, k, u),
					algebraic_element.PolynomialsOverRestriction.At(ops, K, line0, z),
					algebraic_element.PolynomialsOverRestriction.At(ops, K, line1, w))),
			"k[t] read in K is k[t]",
			"k[1/t] read in K is k[1/t]",
			"k[t][z] read in K is k[t][z]",
			"k[1/t][w] read in K is k[1/t][w]")
		curve := a.Have(
			"the charts make K a curve over the line",
			"curve_over_line(restrict_field(M, K), k, t, «pmChart0», «pmChart1», «pmOverlap»)",
			By(subfieldK, model, PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, b)))
		lines := a.Have(
			"so k[t] and k[1/t] are subrings of K",
			"subring(field_ring(restrict_field(M, K)), «pmPolynomials») ∧ "+
				"subring(field_ring(restrict_field(M, K)), «pmInversePolynomials»)",
			By(
				curve,
				algebraic_curve.CurveOverItsLine.Read(function).At(k, chart0, chart1, overlap, t),
				sameImages[0],
				sameImages[1]))
		relation := a.Have(
			"F is monic over k[t] and vanishes at z",
			"polynomial_over(«pmPolynomials», F) ∧ polynomial_monic(F) ∧ polynomial_eval(F, z) = M.zero",
			By(subfieldK, model, PlaneModelRelation.Read(M).At(K, k, t, z, F, b)))
		span0 := a.Have(
			"so chart zero, k[t][z] read in K, is the k[t]-span of the powers of z below deg F",
			"«pmChart0» = module_span(«ringOver»(«pmPolynomials»), «vectors», «pmPowersZ»)",
			By(
				lines,
				relation,
				integral_element.IntegralPowerSpan.Read(function).At(line0, a.MemberOf[on.Any](z, zInK), F),
				PlaneChartsInAmbient.At(ops, K, k, t, z, b),
				sameImages[2]))
		scaled := a.Conjuncts(
			GroupPremises(subfieldK, model, ScaledMonicEquation.Read(M).At(K, k, t, z, F, b)),
			"the scaled equation G of w is over k[1/t]",
			"G is monic",
			"w is a root of G",
			"G has degree deg F")
		spanG := a.Have(
			"so chart one, k[1/t][w] read in K, is the k[1/t]-span of the powers of w below deg G",
			"«pmChart1» = "+
				"module_span(«ringOver»(«pmInversePolynomials»), "+
				"    «vectors», "+
				"    {monoid_pow(M.mul, M.one, «pmGenerator», i) | i:num | i < polynomial_degree(«pmScaled»)})",
			By(
				lines,
				scaled[0],
				scaled[1],
				scaled[2],
				integral_element.IntegralPowerSpan.Read(function).At(line1, a.MemberOf[on.Any](w, wInK), G),
				PlaneChartsInAmbient.At(ops, K, k, t, z, b),
				sameImages[3]))
		degree := scaled[3]
		span1 := a.Have(
			"which are the powers of w below deg F",
			"«pmChart1» = module_span(«ringOver»(«pmInversePolynomials»), «vectors», «pmPowersW»)",
			spanG.Rw(),
			degree.Rw(),
			Basic())

		// The twist of zⁱ by t^N(zⁱ) = t^(−bi) is wⁱ.
		twistedPowers := a.Have(
			"t^N(zⁱ) zⁱ = t^(−bi) zⁱ is wⁱ = (t^(−b) z)ⁱ",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i < polynomial_degree(F)"},
				Conclusion: "laurent_monomial(t, N(monoid_pow(M.mul, M.one, z, i))) * " +
					"monoid_pow(M.mul, M.one, z, i) = " +
					"monoid_pow(M.mul, M.one, «pmGenerator», i)",
			},
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				below := c.Assume()
				c.Show(
					"t^(−bi) is the i-th power of t^(−b), and the powers of t^(−b) and of z multiply to those of w",
					By(
						below,
						twisted.At(i),
						laurent_polynomial.LaurentMonomialOfNum.At(
							c.TermAs[Op[A]]("M.mul"),
							c.TermAs[A]("M.one"),
							c.TermAs[Fun[A, A]]("M.inv"),
							t,
							c.TermAs[Nat]("b * i")),
						comm_monoid.PowPowOn.Read(multiplicative).At(um, b, i),
						comm_monoid.MulPowOn.Read(multiplicative).At(scale, zm, i)))
			}))
		generators := a.Have(
			"so the twisted powers of z are the powers of w",
			"{laurent_monomial(t, N(e)) * e | e:A | e ∈ «pmPowersZ»} = «pmPowersW»",
			BySets(twistedPowers))
		a.Show(
			"the charts are the spans of the free pair along the powers of z, twisted by N",
			By(
				span0,
				span1,
				generators,
				projective_line_free_pair.ProjectiveLineFreePairDef.At(
					functionField, k, t, a.TermAs[Set[A]]("«pmPowersZ»"), N),
				sameImages[0],
				sameImages[1]))
	}),
})}

// PlaneModelArithmeticGenus — the genus of an integral plane model is the sum
// of bi − 1 over the positive exponents i below deg F: read over the
// projective line of t, the structure pair is the free pair along the powers
// zⁱ below deg F, zⁱ twisted by −bi (PlaneStructurePairFree), the powers being
// distinct and independent over k[t]; H¹ of the curve is H¹ of that pair on the
// line (CurvePairOnLine), of dimension the sum of max(bi − 1, 0)
// (FreeLinePairH1Dim), which is bi ∸ 1 read in ℕ, and the exponent 0
// contributes nothing.
var PlaneModelArithmeticGenus = planeModelArithmeticGenusThm{family.Add(registry.ProofEntry{
	Name: "PlaneModelArithmeticGenus",
	Key:  "prop_d734645375c657ff",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "curve_genus(«pmRing», k, «pmChart0», «pmChart1», «pmOverlap») = " +
			"nat_sum({i:num | 0 < i ∧ i < polynomial_degree(F)}, λi:num. b * i - 1)",
		Abbrev: Abbrev{
			{Name: "vectors", Text: "regular_module(field_ring(restrict_field(M, K)))"},
			{Name: "lineRing", Text: "restrict_ring(field_ring(restrict_field(M, K)), " +
				"    ring_away(field_ring(restrict_field(M, K)), «pmPolynomialsInK», t))"},
			{Name: "exponents", Text: "{i:num | i < polynomial_degree(F)}"},
			{Name: "power", Text: "λi:num. monoid_pow(M.mul, M.one, z, i)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		subfieldK, model Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		chart0, chart1, overlap :=
			a.TermAs[Set[A]]("«pmChart0»"), a.TermAs[Set[A]]("«pmChart1»"), a.TermAs[Set[A]]("«pmOverlap»")
		powers, rational := a.TermAs[Set[A]]("«pmPowersZ»"), a.TermAs[Set[A]]("«pmRational»")
		degree := a.TermAs[Nat]("polynomial_degree(F)")
		exponents := a.TermAs[Set[Nat]]("«exponents»")
		power := a.TermAs[Fun[Nat, A]]("«power»")
		summand := a.TermAs[Fun[Nat, Nat]]("λi:num. b * i - 1")
		ambient := a.Conjuncts(
			a.Have(
				"read in M: k is a subfield, t lies in K and in M, z in "+
					"M, and z is algebraic over k(t) with minimal polynomial F",
				"subfield(M, k) ∧ "+
					"t ∈ K ∧ "+
					"t ∈ M.carrier ∧ "+
					"z ∈ M.carrier ∧ "+
					"algebraic_over(M, «pmRational», z) ∧ "+
					"F = minimal_polynomial(M, «pmRational», z)",
				By(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b))),
			"k is a subfield of M",
			"t lies in K",
			"t lies in M",
			"z lies in M",
			"z is algebraic over k(t)",
			"F is its minimal polynomial")
		tInK := ambient[1]
		tm, zm := a.MemberOf[on.M](t, ambient[2]), a.MemberOf[on.M](z, ambient[3])

		// The powers of z below deg F are distinct: i ↦ zⁱ is one-to-one there.
		size := a.Have(
			"the powers of z below deg F, a basis of k(t)(z) over k(t), are deg F in number",
			"has_size(«pmPowersZ», polynomial_degree(F))",
			By(
				ambient[0],
				ambient[4],
				ambient[5],
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm),
				algebraic_element.AdjoinPowerBasis.Read(M).At(rational, zm)))
		image := a.Have(
			"they are the image of i ↦ zⁱ on the numbers below deg F",
			"«pmPowersZ» = image(«power», «exponents»)",
			BySets())
		counted := a.Unfolded(size, cardinality.HasSizeDef)
		distinct := a.Have(
			"so i ↦ zⁱ is one-to-one below deg F, the image having as many members as the numbers below deg F",
			"injective_on(«exponents», «power»)",
			By(
				image,
				counted,
				a.Unfolded(num_segment.HasSizeBelowStrict.At(degree), cardinality.HasSizeDef),
				cardinality.ImageImpInjectiveGen.At(exponents, powers, power)))

		// The twist: N(zⁱ) = −bi.
		N, twists := a.ObtainAs[Fun[A, Int]](
			"some N twists each power zⁱ below deg F by −bi",
			"∃N:(A → int). ∀i:num. i < polynomial_degree(F) ⇒ N(monoid_pow(M.mul, M.one, z, i)) = -&(b * i)",
			Derive(func(c *Argument) {
				_, index := c.ObtainAs[Fun[A, Nat]](
					"each power zⁱ below deg F has its exponent i",
					"∃g:(A → num). ∀i:num. i < polynomial_degree(F) ⇒ g(monoid_pow(M.mul, M.one, z, i)) = i",
					By(distinct, functions.InjectiveOnLeftInverse.At(power, exponents)))
				N, nDef := c.LetAs[Fun[A, Int]]("N", "λe:A. -int_of_num(b * g(e))")
				c.Take(N)
				c.Show(
					"N(e) is −b times the exponent of e",
					By(nDef, index))
			}),
			Named("N"))

		// The structure pair is the free pair along the powers of z, independent over k[t].
		pair := a.Have(
			"so the structure pair is the free pair along the powers of z, twisted by N",
			"(«pmChart0», «pmChart1») = projective_line_free_pair(restrict_field(M, K), k, t, «pmPowersZ», N)",
			By(subfieldK, model, twists, PlaneStructurePairFree.Read(M).At(K, k, t, z, F, b, N)))
		function := a.Have(
			"K is a field under M's operations",
			"field_on(restrict_field(M, K))",
			By(subfieldK, field.SubfieldFieldOn.Read(M).At(K)))
		biaffine := a.Conjuncts(
			GroupPremises(subfieldK, model, PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, b)),
			"the charts make K a curve over the line",
			"chart zero has a finite basis over k[t], the powers of z below deg F")
		curve, basis := biaffine[0], biaffine[1]
		line := algebraic_curve.CurveOverItsLine.Read(function).At(k, chart0, chart1, overlap, t)
		sameRings := a.Have(
			"restricted to a set, the ring of K is that of M",
			"∀X:set(A). restrict_ring(field_ring(restrict_field(M, K)), X) = restrict_ring(field_ring(M), X)",
			Unfold(module_record.RestrictRingDef))
		sameModules := a.Have(
			"and so is its regular module",
			"∀X:set(A). restrict_module(«vectors», X) = restrict_module(regular_module(field_ring(M)), X)",
			Unfold(module_record.RestrictModuleDef))
		chartInK := a.Have(
			"chart zero, a subring of K, lies in K",
			"«pmChart0» ⊆ K",
			By(
				curve,
				line,
				comm_ring.SubringSubset.At(
					a.TermAs[module_record.RingOps[A]]("field_ring(restrict_field(M, K))"), chart0)))
		independent := a.Have(
			"so the powers of z are independent over k[t] in K, as they are in chart zero",
			"module_independent(restrict_ring(field_ring(restrict_field(M, K)), «pmPolynomialsInK»), "+
				"    «vectors», "+
				"    «pmPowersZ»)",
			By(
				sameModules.At(chart0),
				sameRings.At(a.TermAs[Set[A]]("«pmPolynomialsInK»")),
				chartInK,
				a.Unfolded(basis, linear_independence.ModuleBasisDef),
				linear_independence.IndependentRestrict.At(
					a.TermAs[module_record.RingOps[A]](
						"restrict_ring(field_ring(restrict_field(M, K)), «pmPolynomialsInK»)"),
					a.TermAs[module_record.ModuleOps[A, A]]("«vectors»"),
					chart0,
					powers),
				algebraic_element.PolynomialsOverRestriction.At(ops, K, k, t)))

		// H¹ on the line.
		count := a.Have(
			"along the finite independent powers of z, h¹ of the free pair is the sum of max(−N(e) − 1, 0)",
			"int_of_num(lattice_pair_h1_dim(«lineRing», "+
				"        k, "+
				"        «vectors», "+
				"        projective_line_free_pair(restrict_field(M, K), k, t, «pmPowersZ», N))) = "+
				"Σ_{e∈«pmPowersZ»} max(-N(e) - &1, &0)",
			By(
				curve,
				counted,
				independent,
				line,
				projective_line_free_pair.FreeLinePairH1Dim.Read(function).At(
					k, a.MemberOf[on.Any](t, tInK), powers, N)))

		// The count, read by exponent and in ℕ.
		sum := a.Have(
			"the count is the sum of bi − 1 over the positive exponents i below deg F, read in ℤ",
			"Σ_{e∈«pmPowersZ»} max(-N(e) - &1, &0) = "+
				"int_of_num(nat_sum({i:num | 0 < i ∧ i < polynomial_degree(F)}, λi:num. b * i - 1))",
			Derive(func(c *Argument) {
				truncated := c.Have(
					"for a natural n, max(n − 1, 0) in ℤ is the truncated difference n ∸ 1",
					"∀n:num. max(int_of_num(n) - &1, &0) = n - 1",
					Derive(func(d *Argument) {
						n := d.FixAs[Nat]("n")
						d.Cases(d.Term("1 ≤ n"))
						d.When(
							"from n ≥ 1 on, ℕ keeps the difference",
							func(e *Argument, positive Fact) {
								e.Show(
									"so max(n − 1, 0) = n − 1 = n ∸ 1",
									ByArith(positive, int_embed.OfNumSub.At(e.TermAs[Nat]("1"), n)))
							})
						d.Otherwise(
							"at n = 0 both sides are 0",
							func(e *Argument, small Fact) {
								zero := e.Have(
									"n is 0, and so is n ∸ 1",
									"n = 0 ∧ n - 1 = 0",
									ByArith(small))
								e.Show(
									"so max(−1, 0) = 0 = 0 ∸ 1",
									ByArith(zero))
							})
					}))
				summands := c.Have(
					"each power zⁱ below deg F is in the basis and contributes max(bi − 1, 0) = bi ∸ 1",
					Statement{
						Binders:    "∀i:num.",
						Hypotheses: []string{"i < polynomial_degree(F)"},
						Conclusion: "monoid_pow(M.mul, M.one, z, i) ∈ «pmPowersZ» ∧ " +
							"max(-N(monoid_pow(M.mul, M.one, z, i)) - &1, &0) = int_of_num(b * i - 1)",
					},
					Derive(func(d *Argument) {
						i := d.FixAs[Nat]("i")
						below := d.Assume()
						value := d.Have(
							"zⁱ, twisted by −bi, contributes max(bi − 1, 0)",
							"max(-N(monoid_pow(M.mul, M.one, z, i)) - &1, &0) = int_of_num(b * i - 1)",
							ByArith(twists.At(i), below, truncated.At(d.TermAs[Nat]("b * i"))))
						d.Show(
							"and zⁱ is one of the powers below deg F",
							BySets(below, value))
					}))
				unique := c.Have(
					"each power in the basis is zⁱ for exactly one i below deg F",
					"∀y:A. y ∈ «pmPowersZ» ⇒ ∃!i:num. i < polynomial_degree(F) ∧ monoid_pow(M.mul, M.one, z, i) = y",
					By(distinct, functions.InjectiveOnDef))
				reindexed := c.Have(
					"so the sum over the powers is the sum over their exponents",
					"Σ_{i<polynomial_degree(F)} int_of_num(b * i - 1) = Σ_{e∈«pmPowersZ»} max(-N(e) - &1, &0)",
					Simp(Fwd(int_sum.IntSumDef)),
					By(
						unique,
						summands,
						int_real_lift.MonoidalAdd,
						monoidal.ReindexGeneral.At(
							c.TermAs[Op[Int]]("int_add"),
							exponents,
							powers,
							c.TermAs[Fun[Nat, Int]]("λi:num. b * i - 1"),
							c.TermAs[Fun[A, Int]]("λe:A. max(-N(e) - &1, &0)"),
							power)))
				cast := c.Have(
					"a sum of naturals read in ℤ is the sum of the readings",
					"int_of_num(Σ_{i<polynomial_degree(F)} (b * i - 1)) = "+
						"Σ_{i<polynomial_degree(F)} int_of_num(b * i - 1)",
					Simp(Fwd(int_sum.IntSumDef), Fwd(nat_sum.NatSumDef)),
					By(
						nat_sum.MonoidalNatAdd,
						int_real_lift.MonoidalAdd,
						nat_sum.NeutralNatAdd,
						int_real_lift.NeutralAdd,
						int_embed.OfNumAdd,
						num_segment.FiniteBelowStrict.At(degree),
						monoidal.Homomorphic.At(
							c.TermAs[Op[Nat]]("(+)"),
							c.TermAs[Op[Int]]("int_add"),
							c.TermAs[Fun[Nat, Int]]("int_of_num"),
							exponents,
							summand)))
				positive := c.TermAs[Set[Nat]]("{i:num | 0 < i ∧ i < polynomial_degree(F)}")
				zeroTerm := c.Have(
					"the exponent 0 contributes b·0 ∸ 1 = 0",
					"∀i:num. i < polynomial_degree(F) ∧ ¬(0 < i ∧ i < polynomial_degree(F)) ⇒ b * i - 1 = 0",
					Derive(func(d *Argument) {
						d.FixAs[Nat]("i")
						outside := d.Assume()
						zero := d.Have(
							"an exponent below deg F that is not positive is 0",
							"i = 0",
							ByArith(outside))
						d.Show(
							"and b·0 ∸ 1 = 0",
							ByArith(zero))
					}))
				among := c.Have(
					"the positive exponents are among the exponents below deg F",
					"{i:num | 0 < i ∧ i < polynomial_degree(F)} ⊆ «exponents»",
					BySets())
				dropped := c.Have(
					"so the sum over the positive exponents is the sum over all of them",
					"nat_sum({i:num | 0 < i ∧ i < polynomial_degree(F)}, λi:num. b * i - 1) = "+
						"Σ_{i<polynomial_degree(F)} (b * i - 1)",
					By(zeroTerm, among, nat_sum.Superset.At(positive, exponents, summand)))
				c.Show(
					"the sum over the powers is the sum over the exponents, the sum "+
						"of the readings in ℤ, and the sum over the positive exponents",
					dropped.Rw(),
					cast.Rw(),
					reindexed.Rw(),
					Basic())
			}))

		// The genus.
		onLine := a.Have(
			"H¹ of the structure pair is one module over the line's overlap k[t, 1/t] and over the curve's",
			"lattice_pair_h1(«lineRing», «vectors», («pmChart0», «pmChart1»)) = "+
				"lattice_pair_h1(restrict_ring(field_ring(restrict_field(M, K)), «pmOverlap»), "+
				"    «vectors», "+
				"    («pmChart0», «pmChart1»))",
			By(
				curve,
				algebraic_curve.CurveLatticeData.Read(function).At(k, chart0, chart1, overlap, t),
				algebraic_curve.CurvePairOnLine.Read(function).At(
					k, chart0, chart1, overlap, t, a.TermAs[Prod[Set[A], Set[A]]]("(«pmChart0», «pmChart1»)"))))
		// The Simp reads the goal in M's ring, field_ring(restrict_field(M, K)) as
		// restrict_ring(field_ring(M), K) and a restriction of a restriction as one;
		// onLine is spelled in K's ring, and the By reads it by the same two laws.
		genus := a.Have(
			"so the genus, h¹ of the structure pair over k, is h¹ of the free pair on the line",
			"curve_genus(«pmRing», k, «pmChart0», «pmChart1», «pmOverlap») = "+
				"lattice_pair_h1_dim(«lineRing», "+
				"    k, "+
				"    «vectors», "+
				"    projective_line_free_pair(restrict_field(M, K), k, t, «pmPowersZ», N))",
			Simp(
				Fwd(algebraic_curve.CurveGenusDef),
				Fwd(lattice_pair.LatticePairH1DimDef),
				Rev(field.RestrictFieldRing),
				Fwd(module_record.RestrictRingTwice)),
			By(onLine, pair, field.RestrictFieldRing, module_record.RestrictRingTwice))
		a.Show(
			"the genus is that count, read in ℕ",
			By(genus, count, sum, int_embed.OfNumEq))
	}),
})}
