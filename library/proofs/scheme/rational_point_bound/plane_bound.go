// plane_bound.go — the point bound for an integral plane model. The Bezout
// identity between F and its derivative clears its denominators over k[t]
// (PlaneModelHasCertificate). Over a finite constant field l its nonvanishing
// locus gives regular points, Bombieri bounds those, and the bad-fibre estimate
// absorbs the rest (PlaneModelChartBound). The threshold on the size of l is
// read off the genus, which constant extension keeps. A plane equation takes the
// bound from its generic model, whose chart holds every solution
// (PlaneEquationSquareFieldUpperBound).

package rational_point_bound

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_splitting"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/perfect_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/good_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_point_count"
	"github.com/euc-ai/xugo/library/proofs/scheme/plane_model"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PlaneModelHasCertificate — a plane model carries a Bezout certificate over
// k[t]. F lies over k[t] and is separable over its fraction field k(t), so it has
// a Bezout identity with its derivative over k[t], whose constant c is the value
// a(t) of a nonzero a over k.
var PlaneModelHasCertificate = planeModelHasCertificateThm{family.Add(registry.ProofEntry{
	Name: "PlaneModelHasCertificate",
	Key:  "prop_ac6d6198aca1a345",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "∃a U V:(num → A). plane_good_certificate(«rbAmbientRing», k, t, F, a, U, V)",
		Abbrev: Abbrev{
			{Name: "rational", Text: "field_adjoin(restrict_field(M, K), k, {t})"},
			{Name: "polynomials", Text: "polynomial_image(field_ring(restrict_field(M, K)), k, t)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		inField, model Fact,
	) {
		functionOps := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
		functionRing := a.TermAs[RingOps[A]]("field_ring(restrict_field(M, K))")
		rational := a.TermAs[Set[A]]("«rational»")
		polynomials := a.TermAs[Set[A]]("«polynomials»")
		functionField := a.Have(
			"K is a field under the operations of M",
			"field_on(restrict_field(M, K))",
			By(inField, field.SubfieldFieldOn.Read(M).At(K)))
		data := a.Conjuncts(
			a.Unfolded(model, plane_model.IntegralPlaneModelDef),
			"K is regular over k",
			"t lies in K",
			"t is transcendental over k",
			"z lies in K",
			"z generates K over k(t)",
			"F is the minimal polynomial of z over k(t)",
			"F is separable over k(t)",
			"F has positive degree",
			"the weight is positive",
			"the lower coefficients of F are polynomials in t")
		regular, tInK, separable := data[0], data[1], data[6]
		tMember := a.MemberOf[on.Any](t, tInK)
		kField := a.Have(
			"k is a subfield of K",
			"subfield(restrict_field(M, K), k)",
			By(regular, function_field.RegularFunctionFieldDef.At(functionOps, k, K)))
		rationalField := a.Have(
			"k(t) is a subfield of K",
			"subfield(restrict_field(M, K), «rational»)",
			By(kField, tInK, algebraic_element.AdjoinElementSubfield.Read(functionField).At(k, tMember)))
		polynomialFacts := a.Conjuncts(
			GroupPremises(kField, algebraic_element.PolynomialImageRing.Read(functionField).At(k, tMember)),
			"k[t] is a subring of K",
			"it holds k",
			"it holds t",
			"it lies in k(t)")
		polynomialsSubring, polynomialsInRational := polynomialFacts[0], polynomialFacts[3]
		values := a.Have(
			"k[t] is the set of the values at t of the polynomials over k",
			"∀u:A. u ∈ «polynomials» ⇔ ∃p:(num → A). polynomial_over(k, p) ∧ u = polynomial_eval(p, t)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTac())
		rationalFieldOn := a.Have(
			"k(t) is a field under the same operations",
			"field_on(restrict_field(restrict_field(M, K), «rational»))",
			By(rationalField, field.SubfieldFieldOn.Read(functionField).At(rational)))
		restricted := a.Have(
			"the ring of that field is the restricted ring",
			"restrict_ring(field_ring(restrict_field(M, K)), «rational») = "+
				"field_ring(restrict_field(restrict_field(M, K), «rational»))",
			Cite(field.RestrictFieldRing))
		subringOfRational := a.Have(
			"k[t] is a subring of k(t)",
			"subring(field_ring(restrict_field(restrict_field(M, K), «rational»)), «polynomials»)",
			Simp(Rev(restricted)),
			By(
				polynomialsSubring,
				polynomialsInRational,
				comm_ring.SubringRestrict.At(functionRing, polynomials, rational)))
		fractions := a.Have(
			"k(t) is its fraction field",
			"fraction_field_carrier(field_ring(restrict_field(restrict_field(M, K), «rational»)), "+
				"    «polynomials»)",
			Simp(Rev(restricted)),
			By(
				kField,
				tMember,
				integral_element.RationalFunctionsFractionField.Read(functionField).At(k, tMember)))
		separableInRational := a.Have(
			"F is separable in the field k(t)",
			"polynomial_separable(field_ring(restrict_field(restrict_field(M, K), «rational»)), F)",
			Simp(Rev(restricted)),
			By(separable))
		c, U, V, bezout := a.Obtain3As[A, Fun[Nat, A], Fun[Nat, A]](
			"F and its derivative combine over k[t] to a nonzero constant c of k[t]",
			"∃c:A. ∃U V:(num → A). "+
				"    c ∈ «polynomials» ∧ "+
				"    c ≠ M.zero ∧ "+
				"    polynomial_over(«polynomials», U) ∧ "+
				"    polynomial_over(«polynomials», V) ∧ "+
				"    fun_add(polynomial_mul(U, F), polynomial_mul(V, polynomial_derivative(F))) = "+
				"    (λn:num. COND(n = 0, c, M.zero))",
			By(
				subringOfRational,
				fractions,
				inField,
				model,
				plane_model.PlaneModelOverPolynomials.Read(M).At(K, k, t, z, F, b),
				separableInRational,
				good_localization.SeparablePolynomialGoodOpen.Read(rationalFieldOn).At(polynomials, F)))
		parts := a.Conjuncts(
			bezout,
			"c lies in k[t]",
			"c is not zero",
			"U is a polynomial over k[t]",
			"V is a polynomial over k[t]",
			"they combine F and its derivative to c")
		constantIn, constantNonzero, overU, overV, combination :=
			parts[0], parts[1], parts[2], parts[3], parts[4]
		denominator, valueData := a.ObtainAs[Fun[Nat, A]](
			"write c as the value at t of a polynomial a over k",
			"∃a:(num → A). polynomial_over(k, a) ∧ c = polynomial_eval(a, t)",
			By(constantIn, values.At(c)))
		value := a.Conjuncts(
			valueData,
			"a is a polynomial over k",
			"its value at t is c")
		overK, valueAtT := value[0], value[1]
		nonzero := a.Have(
			"a is not the zero polynomial, whose value at t is zero while c is not",
			"a ≠ vec_zero",
			By(
				Normalized,
				constantNonzero,
				valueAtT,
				polynomial_evaluation.EvalVecZero.Read(field.RingOn.Read(functionField)).At(tMember)))
		constantInField := a.Have(
			"c lies in k[t], inside K, so in M",
			"c ∈ M.carrier",
			BySets(
				constantIn,
				polynomialsSubring,
				inField,
				comm_ring.SubringSubset.At(functionRing, polynomials),
				field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("M"), K)))
		cm := a.MemberOf[on.M](c, constantInField)
		ring := field.RingOn.Read(M)
		productU := a.TermAs[Fun[Nat, A]]("polynomial_mul(U, F)")
		productV := a.TermAs[Fun[Nat, A]]("polynomial_mul(V, polynomial_derivative(F))")
		identity := a.Have(
			"so U·F + V·F′ is c times the unit polynomial",
			"vec_add(polynomial_mul(U, F), polynomial_mul(V, polynomial_derivative(F))) = "+
				"vec_scalar_mul(c, basis_vector(0))",
			Derive(func(b *Argument) {
				b.Do(Funext())
				n := b.FixAs[Nat]("n")
				b.Do(Simp(Fwd(vec_space.VecAddDef), Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)))
				b.Show(
					"each coefficient of the combination is c times that of the unit polynomial",
					By(
						combination,
						function_module.FunAddDef.At(b.TermAs[Op[A]]("M.add"), productU, productV, n),
						comm_ring.MulRightZeroOn.Read(ring).At(cm),
						comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(cm)))
			}))
		a.Take(denominator)
		a.Take(U)
		a.Take(V)
		a.Show(
			"they are the certificate, read in the ring of K",
			Simp(Fwd(field.RestrictFieldRing)),
			Unfold(plane_model.PlaneGoodCertificateDef),
			valueAtT.RwRev(),
			By(overK, nonzero, overU, overV, identity))
	}),
})}

// PlaneModelChartBound — over one finite constant field l with s² elements the
// first chart has at most s² + (2g + 1)s + d(e + 1) points in l, for g the genus,
// d the degree of F and e that of a. Extended to l the model is a curve of the
// same genus and Bombieri bounds its regular points. A point of the extended
// chart at which a(t) survives gives a regular point, determined by its kernel;
// the bad-fibre estimate adds the rest; the overlap only lowers the count; and
// the points of the extended chart are those of the chart itself in l.
var PlaneModelChartBound = planeModelChartBoundThm{family.Add(registry.ProofEntry{
	Name: "PlaneModelChartBound",
	Key:  "prop_35e29eee013e36dd",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀K k:set(A). " +
			"∀t z:A. " +
			"∀F:(num → A). " +
			"∀b:num. " +
			"∀l:set(A). " +
			"∀a U V:(num → A). " +
			"∀s:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
			"subfield(M, l)",
			"finite(l)",
			"k ⊆ l",
			"plane_good_certificate(«rbAmbientRing», k, t, F, a, U, V)",
			"card(l) = s * s",
			"«genus» * «genus» + 3 * «genus» + 1 < s",
		},
		Conclusion: "card(«below») ≤ s * s + (2 * «genus» + 1) * s + «badPoints»",
		Abbrev: Abbrev{
			{Name: "chart", Text: "plane_chart_zero(«rbAmbientRing», k, t, z)"},
			{Name: "infinity", Text: "plane_chart_one(restrict_field(M, K), k, t, z, b)"},
			{Name: "overlap", Text: "ring_away(«rbAmbientRing», «chart», t)"},
			{Name: "genus", Text: "curve_genus(«rbAmbientRing», k, «chart», «infinity», «overlap»)"},
			{Name: "below", Text: "algebra_points(restrict_ring(field_ring(M), «chart»), " +
				"    restrict_ring(field_ring(M), l), " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "badPoints", Text: "polynomial_degree(F) * (polynomial_degree(a) + 1)"},
			{Name: "lChart", Text: "constant_chart(field_ring(M), l, «chart»)"},
			{Name: "lInfinity", Text: "constant_chart(field_ring(M), l, «infinity»)"},
			{Name: "lOverlap", Text: "constant_chart(field_ring(M), l, «overlap»)"},
			{Name: "lGenus", Text: "curve_genus(restrict_ring(field_ring(M), constant_composite(M, K, l)), " +
				"    l, " +
				"    «lChart», " +
				"    «lInfinity», " +
				"    «lOverlap»)"},
			{Name: "pointsOn", Text: "λX:set(A). " +
				"    algebra_points(restrict_ring(field_ring(M), X), restrict_ring(field_ring(M), l), l, λx:A. x)"},
			{Name: "good", Text: "{φ:A → A | φ ∈ «pointsOn»(«lChart») ∧ φ(polynomial_eval(a, t)) ≠ M.zero}"},
			{Name: "kernel", Text: "λφ:(A → A). {x:A | x ∈ «lChart» ∧ φ(x) = M.zero}"},
			{Name: "regularPoint", Text: "λφ:(A → A). " +
				"    («kernel»(φ), " +
				"        «lInfinity» ∩ ideal_span(restrict_ring(field_ring(M), «lOverlap»), «kernel»(φ)))"},
			{Name: "regular", Text: "{P:prod(set(A), set(A)) | " +
				"    biaffine_regular_point(restrict_ring(field_ring(M), constant_composite(M, K, l)), " +
				"        l, " +
				"        «lChart», " +
				"        «lInfinity», " +
				"        «lOverlap», " +
				"        P)}"},
			{Name: "count", Text: "curve_rational_point_count(field_ring(M), " +
				"    l, " +
				"    l, " +
				"    «lChart», " +
				"    «lInfinity», " +
				"    «lOverlap»)"},
			{Name: "toChart", Text: "λφ:(A → A). λx:A. " +
				"    COND(x ∈ «lInfinity», φ(x), restrict_ring(field_ring(M), l).zero)"},
			{Name: "away", Text: "{ψ:A → A | " +
				"    ψ ∈ «pointsOn»(«lInfinity») ∧ ring_unit(restrict_ring(field_ring(M), l), ψ(M.inv(t)))}"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		l *Expr[Set[A]],
		a, U, V *Arrow[Nat, A],
		s *Expr[Nat],
		inField, model, lField, finiteL, kInL, certificate, squareSize, large Fact,
	) {
		ops := arg.TermAs[FieldOps[A]]("M")
		fieldRing := arg.TermAs[RingOps[A]]("field_ring(M)")
		chart := arg.TermAs[Set[A]]("«chart»")
		infinity := arg.TermAs[Set[A]]("«infinity»")
		overlap := arg.TermAs[Set[A]]("«overlap»")
		composite := arg.TermAs[Set[A]]("constant_composite(M, K, l)")
		lChart := arg.TermAs[Set[A]]("«lChart»")
		lInfinity := arg.TermAs[Set[A]]("«lInfinity»")
		lOverlap := arg.TermAs[Set[A]]("«lOverlap»")
		good := arg.TermAs[Set[Fun[A, A]]]("«good»")
		regular := arg.TermAs[Set[_LatticePair]]("«regular»")
		regularPoint := arg.TermAs[Fun[Fun[A, A], _LatticePair]]("«regularPoint»")
		pointsOnOverlap := arg.TermAs[Set[Fun[A, A]]]("«pointsOn»(«lOverlap»)")
		pointsAtInfinity := arg.TermAs[Set[Fun[A, A]]]("«pointsOn»(«lInfinity»)")
		pointsOnChart := arg.TermAs[Set[Fun[A, A]]]("«pointsOn»(«lChart»)")
		away := arg.TermAs[Set[Fun[A, A]]]("«away»")

		// Regularity and the curve survive the extension of constants to l.
		regularAmbient := arg.Have(
			"K is regular over k inside M",
			"regular_function_field(M, k, K)",
			By(inField, model, plane_model.PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b)))
		finiteOverK := arg.Have(
			"l is finite over k",
			"finite_extension(M, k, l)",
			By(
				regularAmbient,
				lField,
				kInL,
				finiteL,
				function_field.RegularFunctionFieldDef.At(ops, k, K),
				finite_field.FiniteSubfieldSize.Read(M).At(k, l)))
		regularComposite := arg.Have(
			"the composite is regular over l",
			"regular_function_field(M, l, constant_composite(M, K, l))",
			By(
				regularAmbient,
				lField,
				kInL,
				finiteOverK,
				constant_composite.RegularConstantExtension.Read(M).At(k, K, l)))
		compositeField := arg.Have(
			"so it is a subfield of M",
			"subfield(M, constant_composite(M, K, l))",
			By(regularComposite, function_field.RegularFunctionFieldDef.At(ops, l, composite)))
		extended := arg.Conjuncts(
			arg.Have(
				"the extended charts are a curve over l, of the genus of the model",
				"curve_over_line(restrict_field(M, constant_composite(M, K, l)), "+
					"    l, "+
					"    t, "+
					"    «lChart», "+
					"    «lInfinity», "+
					"    «lOverlap») ∧ "+
					"«lGenus» = «genus»",
				By(
					inField,
					model,
					lField,
					kInL,
					finiteOverK,
					plane_model.PlaneModelBaseChange.Read(M).At(K, k, t, z, F, b, l))),
			"the extended charts are a curve over l",
			"of the genus of the model")
		curveL, genusEqual := extended[0], extended[1]

		// Bombieri bounds the regular points of the extended curve, read in the
		// composite as a field of its own.
		compositeFieldOn := arg.Have(
			"the composite is a field under the operations of M",
			"field_on(restrict_field(M, constant_composite(M, K, l)))",
			By(compositeField, field.SubfieldFieldOn.Read(M).At(composite)))
		bombieri := arg.Conjuncts(
			arg.Have(
				"so Bombieri bounds the regular points by s² + (2g + 1)s",
				"finite(«regular») ∧ card(«regular») ≤ s * s + (2 * «genus» + 1) * s",
				By(
					curveL,
					genusEqual,
					finiteL,
					squareSize,
					large,
					arg.Simplified(
						BombieriUpperRegularPoints.Read(compositeFieldOn).At(l, lChart, lInfinity, lOverlap, t, s),
						curve_point_count.InAmbient))),
			"the regular points are finite",
			"and at most s² + (2g + 1)s")
		finiteRegular, regularBound := bombieri[0], bombieri[1]
		lInChart := arg.Have(
			"l lies in the extended chart",
			"l ⊆ «lChart»",
			By(
				curveL,
				set_order.SubsetTrans,
				algebraic_curve.CurveOverItsLine.Read(compositeFieldOn).At(l, lChart, lInfinity, lOverlap, t)))
		finitePoints := arg.Conjuncts(
			GroupPremises(
				compositeField,
				extended[0],
				finiteL,
				curve_point_count.CurvePointSetsFinite.Read(M).At(composite, l, lChart, lInfinity, lOverlap, t, l)),
			"the extended chart has finitely many points",
			"so has the second chart",
			"so has the overlap")
		finiteChart, finiteInfinity, finiteOverlap := finitePoints[0], finitePoints[1], finitePoints[2]

		// The points at which a(t) survives inject into the regular points.
		toRegular := arg.Have(
			"a point at which a(t) survives gives a regular point",
			"∀φ:(A → A). φ ∈ «good» ⇒ «regularPoint»(φ) ∈ «regular»",
			Derive(func(c *Argument) {
				φ := c.FixAs[Fun[A, A]]("φ")
				parts := c.Conjuncts(
					c.Have(
						"φ is a point of the extended chart at which a(t) survives",
						"φ ∈ «pointsOn»(«lChart») ∧ φ(polynomial_eval(a, t)) ≠ M.zero",
						BySets(c.Assume())),
					"φ is a point of the extended chart",
					"a(t) survives there")
				c.Show(
					"the Bezout identity makes it regular",
					BySets(
						inField,
						model,
						lField,
						kInL,
						finiteOverK,
						certificate,
						parts[0],
						parts[1],
						plane_model.PlaneRegularPointsFromBezout.Read(M).At(K, k, t, z, F, b, l, a, U, V, φ)))
			}))
		injective := arg.Have(
			"the regular point determines the point, its first component being the kernel",
			"injective_on(«good», «regularPoint»)",
			Unfold(functions.InjectiveOnDef),
			Derive(func(c *Argument) {
				φ := c.FixAs[Fun[A, A]]("φ")
				ψ := c.FixAs[Fun[A, A]]("ψ")
				parts := c.Conjuncts(
					c.Assume(),
					"φ is good",
					"ψ is good",
					"they give one regular point")
				kernels := c.Have(
					"their kernels agree",
					"«kernel»(φ) = «kernel»(ψ)",
					By(parts[2], pairs.PairEq))
				both := c.Have(
					"both are points of the extended chart",
					"φ ∈ «pointsOn»(«lChart») ∧ ψ ∈ «pointsOn»(«lChart»)",
					BySets(parts[0], parts[1]))
				c.Show(
					"a point is determined by its kernel",
					By(lInChart, both, kernels, algebra_points.PointDeterminedByKernel.At(fieldRing, lChart, l, φ, ψ)))
			}))
		goodBelowRegular := arg.Have(
			"so there are at most as many of them as of regular points",
			"card(«good») ≤ card(«regular»)",
			By(
				injective,
				finiteChart,
				finite_set.FiniteRestrict.At(
					pointsOnChart, arg.TermAs[Fun[Fun[A, A], Bool]]("λφ:(A → A). φ(polynomial_eval(a, t)) ≠ M.zero")),
				finiteRegular,
				toRegular,
				set_image.ImageSubsetIff.At(regularPoint, good, regular),
				cardinality.CardImageInj.At(regularPoint, good),
				cardinality.CardSubset.At(arg.TermAs[Set[_LatticePair]]("image(«regularPoint», «good»)"), regular)))

		// The overlap has no more points than the second chart.
		overlapAway := arg.Conjuncts(
			GroupPremises(
				compositeField,
				extended[0],
				curve_point_count.OverlapPointsAway.Read(M).At(composite, l, lChart, lInfinity, lOverlap, t, l)),
			"restriction from the overlap to the second chart is injective",
			"its image is the points away from infinity")
		overlapCount := arg.Have(
			"the overlap has as many points as there are away from infinity",
			"card(«away») = card(«pointsOn»(«lOverlap»))",
			overlapAway[1].RwRev(),
			By(
				overlapAway[0],
				finiteOverlap,
				cardinality.CardImageInj.At(arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«toChart»"), pointsOnOverlap)))
		awayCount := arg.Have(
			"so they are at most its size",
			"card(«away») ≤ card(«pointsOn»(«lInfinity»))",
			By(
				finiteInfinity,
				set_basic.SubsetDef.At(away, pointsAtInfinity),
				cardinality.CardSubset.At(away, pointsAtInfinity)))

		// The points of the extended chart are those of the chart itself.
		curve := arg.Have(
			"the charts of the model are a curve over the line",
			"curve_over_line(restrict_field(M, K), k, t, «chart», «infinity», «overlap»)",
			By(inField, model, plane_model.PlaneEquationBiaffineCurve.Read(M).At(K, k, t, z, F, b)))
		charts := arg.Have(
			"so the chart is a subring of M lying between k and K",
			"subring(field_ring(M), «chart») ∧ k ⊆ «chart» ∧ «chart» ⊆ K",
			By(
				inField,
				curve,
				curve_point_count.CurveOverLineChartsInField.Read(M).At(K, k, chart, infinity, overlap, t)))
		finiteBelow := arg.Have(
			"and it has finitely many points in l",
			"finite(«below»)",
			By(
				inField,
				curve,
				finiteL,
				curve_point_count.CurvePointSetsFinite.Read(M).At(K, k, chart, infinity, overlap, t, l)))
		chartCount := arg.Have(
			"extending the constants to l keeps the number of points of the chart",
			"card(«below») = card(«pointsOn»(«lChart»))",
			By(
				regularAmbient,
				lField,
				kInL,
				finiteOverK,
				charts,
				finiteBelow,
				set_order.SubsetRefl.At(l),
				constant_splitting.ConstantChartPointCount.Read(M).At(K, k, l, chart, l)))
		chartBelowCount := arg.Have(
			"the count is |A₀| + |A₁| - |A₀₁|, and |A₀₁| ≤ |A₁|, so the extended chart has at most the count",
			"card(«pointsOn»(«lChart»)) ≤ «count»",
			Unfold(curve_point_count.CurveRationalPointCountDef),
			ByArith(overlapCount, awayCount))
		countBound := arg.Conjuncts(
			GroupPremises(
				inField,
				model,
				lField,
				finiteL,
				kInL,
				certificate,
				plane_model.PlaneGoodOpenUniformBadPointBound.Read(M).At(K, k, t, z, F, b, l, a, U, V)),
			"the good points are among those counted",
			"and the count exceeds them by the bad fibres, at most d(e + 1)")
		arg.Show(
			"the chart, the count, the good points and the regular points in turn give the bound",
			ByArith(chartCount, chartBelowCount, countBound[1], goodBelowRegular, regularBound))
	}),
})}

// IntegralPlaneModelSquareFieldUpperBound — an integral plane model has at most
// card(l) + B·s points in every finite constant extension l with s² elements
// large enough for a fixed threshold Q₀. The certificate and the genus are fixed
// before l: with g the genus, d and e the degrees of F and a, B = 2g + 1 + d(e + 1)
// and Q₀ = (g² + 3g + 2)² do, since Q₀ ≤ s² makes s large for PlaneModelChartBound
// and at least one, which absorbs d(e + 1).
var IntegralPlaneModelSquareFieldUpperBound = integralPlaneModelSquareFieldUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "IntegralPlaneModelSquareFieldUpperBound",
	Key:  "prop_a0cdd125eae83b79",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "∃B Q₀:num. ∀l:set(A). ∀s:num. " +
			"    subfield(M, l) ∧ finite(l) ∧ k ⊆ l ∧ card(l) = s * s ∧ Q₀ ≤ card(l) ⇒ " +
			"    card(algebra_points(restrict_ring(field_ring(M), «chart»), " +
			"            restrict_ring(field_ring(M), l), " +
			"            k, " +
			"            λx:A. x)) ≤ " +
			"    card(l) + B * s",
		Abbrev: Abbrev{
			{Name: "chart", Text: "plane_chart_zero(«rbAmbientRing», k, t, z)"},
			{Name: "infinity", Text: "plane_chart_one(restrict_field(M, K), k, t, z, b)"},
			{Name: "overlap", Text: "ring_away(«rbAmbientRing», «chart», t)"},
			{Name: "genus", Text: "curve_genus(«rbAmbientRing», k, «chart», «infinity», «overlap»)"},
			{Name: "size", Text: "«genus» * «genus» + 3 * «genus» + 2"},
			{Name: "badPointsOf", Text: "λp:(num → A). polynomial_degree(F) * (polynomial_degree(p) + 1)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		inField, model Fact,
	) {
		a, U, V, certificate := arg.Unpack3As[Fun[Nat, A], Fun[Nat, A], Fun[Nat, A]](
			GroupPremises(inField, model, PlaneModelHasCertificate.Read(M).At(K, k, t, z, F, b)),
			"a",
			"U",
			"V")
		arg.Take(arg.TermAs[Nat]("2 * «genus» + 1 + «badPointsOf»(a)"))
		arg.Take(arg.TermAs[Nat]("«size» * «size»"))
		l := arg.FixAs[Set[A]]("l")
		s := arg.FixAs[Nat]("s")
		assumed := arg.Conjuncts(
			arg.Assume(),
			"l is a subfield of M",
			"it is finite",
			"it holds k",
			"it has s² elements",
			"at least the threshold")
		lField, finiteL, kInL, squareSize, threshold :=
			assumed[0], assumed[1], assumed[2], assumed[3], assumed[4]
		size := arg.TermAs[Nat]("«size»")
		atLeastSize := arg.Have(
			"s is at least g² + 3g + 2, as the squares compare",
			"«size» ≤ s",
			Derive(func(c *Argument) {
				below := c.SupposeNot()
				c.Show(
					"a smaller s would have a smaller square",
					ByArith(
						below,
						squareSize,
						threshold,
						nat_order.LessEqMulRightCancel.At(s, size, s),
						nat_order.LessThanMulCancel.At(size, s, size)))
			}))
		large := arg.Have(
			"so s is large for the genus",
			"«genus» * «genus» + 3 * «genus» + 1 < s",
			ByArith(atLeastSize))
		chartBound := arg.Have(
			"Bombieri over l bounds the chart",
			"card(algebra_points(restrict_ring(field_ring(M), «chart»), "+
				"        restrict_ring(field_ring(M), l), "+
				"        k, "+
				"        λx:A. x)) ≤ "+
				"s * s + (2 * «genus» + 1) * s + «badPointsOf»(a)",
			By(
				inField,
				model,
				lField,
				finiteL,
				kInL,
				certificate,
				squareSize,
				large,
				PlaneModelChartBound.Read(M).At(K, k, t, z, F, b, l, a, U, V, s)))
		arg.Show(
			"and s, at least one, absorbs d(e + 1) into B·s",
			ByArith(
				chartBound,
				squareSize,
				atLeastSize,
				nat_order.LessEqMulCancel.At(arg.TermAs[Nat]("«badPointsOf»(a)"), arg.TermAs[Nat]("1"), s)))
	}),
})}

// PlaneEquationSquareFieldUpperBound — the Bombieri bound for the solutions of an
// absolutely irreducible plane equation over a finite field: a parameter t of M and the
// generic root z of the equation over k(t) make a fixed integral model, whose chart k[t][z]
// has at most card(l) + B * s points in every large square field l. Each solution is a
// point of that chart, recovered from the point by its values at t and z.
var PlaneEquationSquareFieldUpperBound = planeEquationSquareFieldUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "PlaneEquationSquareFieldUpperBound",
	Key:  "prop_72ac76bb18bdbf3",
	Reading: "The algebraically closed host is assumed to contain a transcendental " +
		"element over k, so the generic model and all finite constant extensions coexist " +
		"in it. Curve applications have such an element from their given function field.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀F:(num → num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"finite(k)",
			"∃u:A. u ∈ M.carrier ∧ ¬algebraic_over(M, k, u)",
			"absolute_plane_equation(M, k, F)",
		},
		Conclusion: "∃B Q₀:num. ∀l:set(A). ∀s:num. " +
			"    subfield(M, l) ∧ finite(l) ∧ k ⊆ l ∧ card(l) = s * s ∧ Q₀ ≤ card(l) ⇒ " +
			"    plane_equation_count(field_ring(M), l, F) ≤ card(l) + B * s",
		Abbrev: Abbrev{
			{Name: "rational", Text: "field_adjoin(M, k, {t})"},
			{Name: "generic", Text: "λy:A. field_adjoin(M, «rational», {y})"},
			{Name: "f", Text: "λi:num. polynomial_eval(F(i), t)"},
			{Name: "points", Text: "algebra_points(restrict_ring(field_ring(M), " +
				"        plane_chart_zero(restrict_ring(field_ring(M), «generic»(z)), k, t, z)), " +
				"    restrict_ring(field_ring(M), l), " +
				"    k, " +
				"    λx:A. x)"},
			{Name: "solves", Text: "λp:prod(A, A). " +
				"    fst(p) ∈ l ∧ " +
				"    snd(p) ∈ l ∧ " +
				"    polynomial_eval(λi:num. polynomial_eval(F(i), fst(p)), snd(p)) = M.zero"},
			{Name: "solutions", Text: "{p:prod(A, A) | «solves»(p)}"},
			{Name: "values", Text: "λφ:(A → A). (φ(t), φ(z))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		F *Arrow2[Nat, Nat, A],
		closed, kField, finiteK, parameter, equation Fact,
	) {
		ops := a.TermAs[FieldOps[A]]("M")
		t, transcendental := a.UnpackAs[A](parameter, "t")
		tData := a.Conjuncts(
			transcendental,
			"t lies in M",
			"t is transcendental over k")
		constants := a.Have(
			"k is a field",
			"field_on(restrict_field(M, k))",
			By(kField, field.SubfieldFieldOn.Read(M).At(k)))
		perfect := a.Have(
			"a finite field is perfect",
			"perfect_field(restrict_field(M, k))",
			By(finiteK, perfect_field.FiniteFieldIsPerfect.Read(constants)))
		z, b, generic := a.Obtain2As[A, Nat](
			"t is a parameter of the generic model of the equation",
			"∃z:A. ∃b:num. "+
				"    z ∈ M.carrier ∧ "+
				"    integral_plane_model(restrict_field(M, «generic»(z)), k, t, z, «f», b) ∧ "+
				"    polynomial_degree(«f») = polynomial_degree(λi:num. M.zero, F)",
			By(
				M,
				closed,
				kField,
				perfect,
				tData[0],
				tData[1],
				equation,
				plane_model.AbsoluteEquationGenericModel.At(ops, k, F, t)))
		zData := a.Conjuncts(
			generic,
			"z lies in M",
			"k(t, z) is an integral plane model of the equation",
			"which keeps the degree of the equation")
		rational := a.TermAs[Set[A]]("«rational»")
		rationalField := a.Have(
			"k(t) is a subfield of M",
			"subfield(M, «rational»)",
			By(
				kField,
				tData[0],
				algebraic_element.AdjoinElementSubfield.Read(M).At(k, a.MemberOf[on.M](t, tData[0]))))
		genericField := a.Have(
			"k(t, z) is a subfield of M",
			"subfield(M, «generic»(z))",
			By(
				rationalField,
				zData[0],
				algebraic_element.AdjoinElementSubfield.Read(M).At(rational, a.MemberOf[on.M](z, zData[0]))))
		K := a.TermAs[Set[A]]("«generic»(z)")
		f := a.TermAs[Fun[Nat, A]]("«f»")
		B, Q0, bound := a.Unpack2As[Nat, Nat](
			GroupPremises(
				M, genericField, zData[1], IntegralPlaneModelSquareFieldUpperBound.At(ops, K, k, t, z, f, b)),
			"B",
			"Q₀")
		curve := a.Conjuncts(
			GroupPremises(
				M, genericField, zData[1], plane_model.PlaneEquationBiaffineCurve.At(ops, K, k, t, z, f, b)),
			"the charts make a curve over the line",
			"the powers of z are a basis of the chart")
		a.Take(B)
		a.Take(Q0)
		l := a.FixAs[Set[A]]("l")
		s := a.FixAs[Nat]("s")
		given := a.Conjuncts(
			a.Assume(),
			"l is a subfield of M",
			"l is finite",
			"l holds k",
			"l has square cardinality s²",
			"l is large")
		pointsFinite := a.Have(
			"the chart has finitely many points in l",
			"finite(«points»)",
			By(genericField, curve[0], given[1], curve_point_count.CurvePointSetsFinite.Read(M)))
		covered := a.Have(
			"a solution is the pair of values of a point of the chart",
			"«solutions» ⊆ image(«values», «points»)",
			Simp(Fwd(set_basic.SubsetDef)),
			Derive(func(c *Argument) {
				p := c.FixAs[Prod[A, A]]("p")
				inSolutions := c.Assume()
				x, y := c.TermAs[A]("fst(p)"), c.TermAs[A]("snd(p)")
				solution := c.Have(
					"p solves the equation in l",
					"«solves»(p)",
					BySets(inSolutions))
				_, point := c.ObtainAs[Fun[A, A]](
					"the solution is a point of the chart",
					"∃φ:(A → A). φ ∈ «points» ∧ φ(t) = fst(p) ∧ φ(z) = snd(p)",
					By(
						M,
						genericField,
						zData[1],
						equation,
						given[0],
						given[2],
						solution,
						plane_model.PlaneSolutionPoint.At(ops, K, k, l, t, z, F, b, x, y)))
				c.Show(
					"its values at t and z are the two coordinates of p",
					BySets(point, pairs.PairEta.At(p)))
			}))
		count := a.Have(
			"plane_equation_count counts the solutions",
			"plane_equation_count(field_ring(M), l, F) = card(«solutions»)",
			Simp(Fwd(plane_model.PlaneEquationCountDef)),
			Basic())
		points := a.TermAs[Set[Fun[A, A]]]("«points»")
		values := a.TermAs[Fun[Fun[A, A], Prod[A, A]]]("«values»")
		fewer := a.Have(
			"so there are no more solutions than points",
			"card(«solutions») ≤ card(«points»)",
			ByArith(
				covered,
				finite_set.FiniteImage.At(values, points),
				pointsFinite,
				cardinality.CardSubset.At(
					a.TermAs[Set[Prod[A, A]]]("«solutions»"), a.TermAs[Set[Prod[A, A]]]("image(«values», «points»)")),
				cardinality.CardImageLe.At(values, points)))
		pointBound := a.Have(
			"and the integral bound counts the points",
			"card(«points») ≤ card(l) + B * s",
			By(given[0], given[1], given[2], given[3], given[4], bound.At(l, s)))
		a.Show(
			"count the solutions by the points, and the points by the integral bound",
			ByArith(count, fewer, pointBound))
	}),
})}
