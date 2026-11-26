package galois_good_fibres

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_automorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/galois_correspondence"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/separating_parameter"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/twisted_counting"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_point_bounds"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/good_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/scheme/galois_good_open"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// GaloisPrimitiveElement — L, Galois over k(t), is generated over k(t) by one
// element z integral over k[t]: the minimal polynomial of z has its coefficients in
// k[t], is monic and separable, and its degree [L : k(t)] is the order of the group.
var GaloisPrimitiveElement = galoisPrimitiveElementThm{family.Add(registry.ProofEntry{
	Name: "GaloisPrimitiveElement",
	Key:  "prop_d11bd85a2245206a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A.",
		Hypotheses: []string{
			"regular_function_field(M, k, L)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, «K», L)",
		},
		Conclusion: "∃z:A. " +
			"    z ∈ L ∧ " +
			"    field_adjoin(M, «K», {z}) = L ∧ " +
			"    polynomial_over(«B», «F»(z)) ∧ " +
			"    polynomial_monic(«F»(z)) ∧ " +
			"    polynomial_degree(«F»(z)) = card(field_automorphisms(M, «K», L)) ∧ " +
			"    polynomial_separable(restrict_ring(field_ring(M), «K»), «F»(z))",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "F", Text: "λz:A. minimal_polynomial(M, «K», z)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		regular, tIn, transcendental, galois Fact,
	) {
		K := a.TermAs[Set[A]]("«K»")
		parts := a.Conjuncts(
			a.Unfolded(regular, function_field.RegularFunctionFieldDef),
			"k is a subfield",
			"L is a subfield",
			"k lies in L",
			"k is perfect",
			"L is finitely generated over k",
			"L is algebraic over some k(s)",
			"k is closed in L")
		subk, subL, kInL := parts[0], parts[1], parts[2]
		between := a.Conjuncts(
			a.Have(
				"k(t) lies between k and L",
				"subfield(M, «K») ∧ k ⊆ «K» ∧ t ∈ «K» ∧ «K» ⊆ L",
				By(subk, subL, kInL, tIn, algebraic_element.AdjoinElementBetween.Read(M).At(k, L, t))),
			"k(t) is a subfield",
			"holding k",
			"and t",
			"inside L")
		data := a.Conjuncts(
			a.Unfolded(galois, galois_correspondence.GaloisOverDef),
			"L is finite over k(t)",
			"L is normal over k(t)",
			"L is separable over k(t)")
		degree := a.Have(
			"the order of the group is the degree",
			"card(field_automorphisms(M, «K», L)) = extension_degree(M, «K», L)",
			By(
				between[0],
				subL,
				between[3],
				data[0],
				galois,
				galois_correspondence.GaloisIffCard.Read(M).At(K, L)))
		z, primitive := a.ObtainAs[A](
			"an integral primitive element",
			"∃z:A. "+
				"    z ∈ L ∧ "+
				"    field_adjoin(M, «K», {z}) = L ∧ "+
				"    polynomial_over(«B», «F»(z)) ∧ "+
				"    polynomial_monic(«F»(z)) ∧ "+
				"    polynomial_degree(«F»(z)) = extension_degree(M, «K», L) ∧ "+
				"    polynomial_separable(restrict_ring(field_ring(M), «K»), «F»(z))",
			By(
				subk,
				subL,
				kInL,
				tIn,
				transcendental,
				data[0],
				data[2],
				separating_parameter.IntegralPrimitiveElement.Read(M).At(k, L, t)))
		a.Take(z)
		a.Show(
			"z generates L, with the degree the order of the group",
			By(primitive, degree))
	}),
})}

// SeparableChartDenominator — let z be algebraic over k(t), with minimal polynomial F
// over k[t], separable. For a finite set E inside k(t)(z) there is a polynomial a over
// k with a(t) ≠ 0 such that E lies in the ring C = k[t][z][1/a(t)], and the derivative
// of F is a unit of C at every root of F in C. Here a(t) = b d, for b the constant of a
// Bezout relation P F + Q F′ = b over k[t] and d a common denominator of E.
var SeparableChartDenominator = separableChartDenominatorThm{family.Add(registry.ProofEntry{
	Name: "SeparableChartDenominator",
	Key:  "prop_d3361b8b974b4f2a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k E:set(A). ∀t z:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"t ∈ M.carrier",
			"z ∈ M.carrier",
			"algebraic_over(M, «K», z)",
			"polynomial_over(«B», «F»)",
			"polynomial_separable(restrict_ring(field_ring(M), «K»), «F»)",
			"finite(E)",
			"E ⊆ field_adjoin(M, «K», {z})",
		},
		Conclusion: "∃a:(num → A). " +
			"    polynomial_over(k, a) ∧ " +
			"    polynomial_eval(a, t) ≠ M.zero ∧ " +
			"    E ⊆ «C»(a) ∧ " +
			"    (∀r:A. " +
			"        r ∈ «C»(a) ∧ polynomial_eval(«F», r) = M.zero ⇒ " +
			"        ring_unit(restrict_ring(field_ring(M), «C»(a)), " +
			"            polynomial_eval(polynomial_derivative(«F»), r)))",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "F", Text: "minimal_polynomial(M, «K», z)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "λa:(num → A). ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, E *Expr[Set[A]],
		t, z *Expr[A],
		subk, tIn, zIn, algebraic, fOver, separable, finiteE, inside Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		zero := arg.TermAs[A]("M.zero")
		carrier := arg.TermAs[Set[A]]("M.carrier")
		K, B, U := arg.TermAs[Set[A]]("«K»"), arg.TermAs[Set[A]]("«B»"), arg.TermAs[Set[A]]("«U»")
		F := arg.TermAs[Fun[Nat, A]]("«F»")
		tm, zm := arg.MemberOf[on.M](t, tIn), arg.MemberOf[on.M](z, zIn)
		adjoined := arg.Conjuncts(
			GroupPremises(subk, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)),
			"k(t) is a subfield",
			"holding k",
			"and t")
		subK := adjoined[0]
		subkRing := arg.Have(
			"k is a subring",
			"subring(field_ring(M), k)",
			By(subk, field.SubfieldSubring.Read(M).At(k)))
		base := arg.Conjuncts(
			GroupPremises(subkRing, algebraic_element.PolynomialImageSubring.Read(M).At(k, tm)),
			"k[t] is a subring",
			"holding k",
			"and t")
		subB := base[0]
		image := arg.Conjuncts(
			GroupPremises(base[0], algebraic_element.PolynomialImageSubring.Read(M).At(B, zm)),
			"k[t][z] is a subring",
			"holding k[t]",
			"and z")
		subU, bInU := image[0], image[1]
		adjoinInField := arg.Have(
			"k(t)(z) lies in M",
			"field_adjoin(M, «K», {z}) ⊆ M.carrier",
			Derive(func(c *Argument) {
				adjoinedField := c.Have(
					"k(t)(z) is a subfield",
					"subfield(M, field_adjoin(M, «K», {z}))",
					By(subK, zIn, algebraic_element.AdjoinElementSubfield.Read(M).At(K, zm)))
				c.Show(
					"a subfield lies in M",
					By(adjoinedField, field.SubfieldSubset.At(fieldM, c.TermAs[Set[A]]("field_adjoin(M, «K», {z})"))))
			}))
		fractions := arg.Have(
			"k(t) is the fraction field of k[t]",
			"fraction_field_carrier(restrict_ring(field_ring(M), «K»), «B»)",
			By(subk, tIn, integral_element.RationalFunctionsFractionField.Read(M).At(k, tm)))
		bInK := arg.Have(
			"k[t] lies in k(t)",
			"«B» ⊆ «K»",
			By(subk, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		ringK := arg.Have(
			"the ring of the field k(t) is k(t) under the operations of M",
			"field_ring(restrict_field(M, «K»)) = restrict_ring(field_ring(M), «K»)",
			By(field.RestrictFieldRing.At(fieldM, K)))
		subBK := arg.Have(
			"k[t] is a subring of k(t)",
			"subring(field_ring(restrict_field(M, «K»)), «B»)",
			ringK.Rw(),
			By(subB, bInK, comm_ring.SubringRestrict.At(R, B, K)))
		fractionsK := arg.Have(
			"k(t) as a field is the fraction field of k[t]",
			"fraction_field_carrier(field_ring(restrict_field(M, «K»)), «B»)",
			ringK.Rw(),
			By(fractions))
		separableK := arg.Have(
			"F is separable over the field k(t)",
			"polynomial_separable(field_ring(restrict_field(M, «K»)), «F»)",
			ringK.Rw(),
			By(separable))
		fieldK := arg.Have(
			"k(t) is a field",
			"field_on(restrict_field(M, «K»))",
			By(subK, field.SubfieldFieldOn.Read(M).At(K)))
		b, P, Q, bezout := arg.Obtain3As[A, Fun[Nat, A], Fun[Nat, A]](
			"a Bezout relation over k[t] with constant b",
			"∃b:A. ∃P Q:(num → A). "+
				"    b ∈ «B» ∧ "+
				"    b ≠ M.zero ∧ "+
				"    polynomial_over(«B», P) ∧ "+
				"    polynomial_over(«B», Q) ∧ "+
				"    fun_add(polynomial_mul(P, «F»), polynomial_mul(Q, polynomial_derivative(«F»))) = "+
				"    λn:num. COND(n = 0, b, M.zero)",
			By(
				fieldK,
				subBK,
				fractionsK,
				fOver,
				separableK,
				good_localization.SeparablePolynomialGoodOpen.At(
					arg.TermAs[FieldOps[A]]("restrict_field(M, «K»)"), B, F)))
		relation := arg.Conjuncts(
			bezout,
			"b lies in k[t]",
			"b is not zero",
			"P is over k[t]",
			"Q is over k[t]",
			"P F + Q F′ is the constant b")
		bInB, bNonzero, pOver, qOver, identity :=
			relation[0], relation[1], relation[2], relation[3], relation[4]
		d, denominator := arg.ObtainAs[A](
			"a common denominator of E in k[t]",
			"∃d:A. d ∈ «B» ∧ d ≠ M.zero ∧ (∀y:A. y ∈ E ⇒ d * y ∈ «U»)",
			By(
				subK,
				subB,
				fractions,
				zIn,
				algebraic,
				finiteE,
				inside,
				integral_element.FiniteAdjoinDenominator.Read(M).AsFact().At(K, B, E, z)))
		clears := arg.Conjuncts(
			denominator,
			"d lies in k[t]",
			"d is not zero",
			"d clears E")
		dInB, dNonzero, dClears := clears[0], clears[1], clears[2]
		p, pFacts := arg.ObtainAs[Fun[Nat, A]](
			"b is a polynomial over k at t",
			"∃p:(num → A). polynomial_over(k, p) ∧ b = polynomial_eval(p, t)",
			BySets(bInB, algebraic_element.PolynomialImageDef.At(R, k, t)))
		q, qFacts := arg.ObtainAs[Fun[Nat, A]](
			"so is d",
			"∃q:(num → A). polynomial_over(k, q) ∧ d = polynomial_eval(q, t)",
			BySets(dInB, algebraic_element.PolynomialImageDef.At(R, k, t)))
		pParts := arg.Conjuncts(
			pFacts,
			"p is over k",
			"b is its value at t")
		qParts := arg.Conjuncts(
			qFacts,
			"q is over k",
			"d is its value at t")
		kInField := arg.Have(
			"k lies in M",
			"k ⊆ M.carrier",
			By(subk, field.SubfieldSubset.At(fieldM, k)))
		kRing := arg.Have(
			"k is a ring",
			"comm_ring_on(restrict_ring(field_ring(M), k))",
			By(subk, field.SubfieldCommRing.Read(M).At(k)))
		overField := arg.Have(
			"p and q are polynomials over M",
			"polynomial_over(M.carrier, p) ∧ polynomial_over(M.carrier, q)",
			By(
				kInField,
				pParts[0],
				qParts[0],
				polynomial.PolynomialOverMono.At(zero, k, carrier, p),
				polynomial.PolynomialOverMono.At(zero, k, carrier, q)))
		aOver := arg.Have(
			"their product is a polynomial over k",
			"polynomial_over(k, polynomial_mul(p, q))",
			By(pParts[0], qParts[0], polynomial.PolynomialMulOver.Read(kRing).AsFact().At(p, q)))
		value := arg.Have(
			"its value at t is b d",
			"polynomial_eval(polynomial_mul(p, q), t) = b * d",
			By(
				overField,
				tIn,
				pParts[1],
				qParts[1],
				polynomial_evaluation.EvalMul.Read(ring).AsFact().At(p, q, t)))
		bField := arg.Have(
			"b and d lie in M",
			"b ∈ M.carrier ∧ d ∈ M.carrier",
			BySets(bInB, dInB, subB, comm_ring.SubringSubset.At(R, B)))
		uNonzero := arg.Have(
			"b d is not zero",
			"b * d ≠ M.zero",
			By(bField, bNonzero, dNonzero, field.MulEqZeroOn.Read(M).AsFact().At(b, d)))
		arg.Take(arg.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)"))
		arg.Do(value.Rw())
		u := arg.TermAs[A]("b * d")
		uInU := arg.Have(
			"b d lies in k[t][z]",
			"b * d ∈ «U»",
			Derive(func(c *Argument) {
				inU := c.Have(
					"b and d lie in k[t][z]",
					"b ∈ «U» ∧ d ∈ «U»",
					BySets(bInB, dInB, bInU))
				c.Show(
					"which is a ring",
					By(subU, inU, comm_ring.SubringMul.At(R, U, b, d)))
			}))
		uField := arg.Have(
			"k[t][z] lies in M",
			"«U» ⊆ M.carrier",
			By(subU, comm_ring.SubringSubset.At(R, U)))
		uInField := arg.Have(
			"so b d lies in M",
			"b * d ∈ M.carrier",
			BySets(uInU, uField))
		chart := arg.Conjuncts(
			arg.Have(
				"C is a subring of M holding k[t][z] and the inverse of b d",
				"subring(field_ring(M), ring_away(field_ring(M), «U», b * d)) ∧ "+
					"«U» ⊆ ring_away(field_ring(M), «U», b * d) ∧ "+
					"ring_away(field_ring(M), «U», b * d) ⊆ M.carrier ∧ "+
					"M.inv(b * d) ∈ ring_away(field_ring(M), «U», b * d) ∧ "+
					"ring_away(field_ring(M), ring_away(field_ring(M), «U», b * d), b * d) = "+
					"ring_away(field_ring(M), «U», b * d)",
				By(
					subU,
					field.CarrierSubfield.Read(M),
					uField,
					uInU,
					uNonzero,
					ring_away.RingAwayInSubfield.Read(M).At(U, carrier, u))),
			"C is a subring",
			"holding k[t][z]",
			"inside M",
			"with the inverse of b d",
			"inverting b d again adds nothing")
		subC, uInC, cInField, inverseInC := chart[0], chart[1], chart[2], chart[3]
		C := arg.TermAs[Set[A]]("ring_away(field_ring(M), «U», b * d)")
		arg.Do(SplitConjAll(
			Case(
				"the product is a polynomial over k",
				By(aOver)),
			Case(
				"b d is not zero",
				By(uNonzero)),
			Case(
				"E lies in C",
				Derive(func(top *Argument) {
					pointwise := top.Have(
						"each point of E lies in C",
						"∀y:A. y ∈ E ⇒ y ∈ ring_away(field_ring(M), «U», b * d)",
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							yIn := c.Assume()
							yField := c.Have(
								"y lies in M",
								"y ∈ M.carrier",
								BySets(yIn, inside, adjoinInField))
							power := c.Have(
								"b d is its own first power",
								"monoid_pow(M.mul, M.one, b * d, 1) = b * d",
								By(uInField, comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(u)))
							regroup := c.Have(
								"(b d) y is b (d y)",
								"(b * d) * y = b * (d * y)",
								ByArith(ring, bField, yField))
							inU := c.Have(
								"which lies in k[t][z]",
								"b * (d * y) ∈ «U»",
								By(
									subU,
									dClears.At(y),
									yIn,
									c.Have(
										"b lies in k[t][z]",
										"b ∈ «U»",
										BySets(bInB, bInU)),
									comm_ring.SubringMul.At(R, U, b, c.TermAs[A]("d * y"))))
							cleared := c.Have(
								"so one power of b d carries y into k[t][z]",
								"∃n:num. monoid_pow(M.mul, M.one, b * d, n) * y ∈ «U»",
								Derive(func(e *Argument) {
									e.Take(e.TermAs[Nat]("1"))
									e.Show(
										"the first power",
										power.Rw(),
										regroup.Rw(),
										By(inU))
								}))
							c.Show(
								"which is membership in C",
								By(yField, cleared, ring_away.RingAwayMember.At(R, U, u, y)))
						}))
					top.Show(
						"so E lies in C",
						BySets(pointwise))
				})),
			Case(
				"F′ is a unit of C at each root of F in C",
				Derive(func(c *Argument) {
					r := c.FixAs[A]("r")
					parts := c.Conjuncts(
						c.Assume(),
						"r lies in C",
						"r is a root of F")
					rC, rRoot := parts[0], parts[1]
					rField := c.Have(
						"r lies in M",
						"r ∈ M.carrier",
						BySets(rC, cInField))
					rm := c.MemberOf[on.M](r, rField)
					ringC := c.Have(
						"C is a ring",
						"comm_ring_on(restrict_ring(field_ring(M), ring_away(field_ring(M), «U», b * d)))",
						By(subC, comm_ring.SubringRingOn.Read(ring).At(C)))
					bInC := c.Have(
						"k[t] lies in C",
						"«B» ⊆ ring_away(field_ring(M), «U», b * d)",
						Derive(func(e *Argument) {
							e.Show(
								"through k[t][z]",
								BySets(bInU, uInC))
						}))
					qC := c.Have(
						"Q is over C",
						"polynomial_over(ring_away(field_ring(M), «U», b * d), Q)",
						By(bInC, qOver, polynomial.PolynomialOverMono.At(zero, B, C, Q)))
					cField := c.Have(
						"so all the polynomials of the relation are over M",
						"polynomial_over(M.carrier, P) ∧ polynomial_over(M.carrier, Q) ∧ polynomial_over(M.carrier, «F»)",
						Derive(func(e *Argument) {
							inField := e.Have(
								"k[t] lies in M",
								"«B» ⊆ M.carrier",
								By(subB, comm_ring.SubringSubset.At(R, B)))
							e.Show(
								"each by its coefficients",
								By(
									inField,
									pOver,
									qOver,
									fOver,
									polynomial.PolynomialOverMono.At(zero, B, carrier, P),
									polynomial.PolynomialOverMono.At(zero, B, carrier, Q),
									polynomial.PolynomialOverMono.At(zero, B, carrier, F)))
						}))
					derivative := c.TermAs[Fun[Nat, A]]("polynomial_derivative(«F»)")
					pTimesF := c.TermAs[Fun[Nat, A]]("polynomial_mul(P, «F»)")
					qTimesDerivative := c.TermAs[Fun[Nat, A]]("polynomial_mul(Q, polynomial_derivative(«F»))")
					dfOver := c.Have(
						"F′ is over M",
						"polynomial_over(M.carrier, polynomial_derivative(«F»))",
						By(cField, polynomial.DerivativeOverCarrier.Read(ring).AsFact().At(F)))
					asSum := c.Have(
						"the relation is a sum of polynomials",
						"fun_add(polynomial_mul(P, «F»), polynomial_mul(Q, polynomial_derivative(«F»))) = "+
							"vec_add(polynomial_mul(P, «F»), polynomial_mul(Q, polynomial_derivative(«F»)))",
						Derive(func(e *Argument) {
							e.Do(Funext())
							e.FixAs[Nat]("n")
							e.Do(Simp(Fwd(function_module.FunAddDef), Fwd(vec_space.VecAddDef)))
							e.Do(Basic())
						}))
					constant := c.Have(
						"the constant polynomial b is b times one",
						"(λn:num. COND(n = 0, b, M.zero)) = vec_scalar_mul(b, basis_vector(0))",
						Derive(func(e *Argument) {
							e.Do(Funext())
							e.FixAs[Nat]("n")
							e.Do(Simp(Fwd(vec_space.VecScalarMulDef), Fwd(vec_space.BasisVectorDef)))
							bm := e.MemberOf[on.M](b, e.Have(
								"b lies in M",
								"b ∈ M.carrier",
								By(bField)))
							e.Show(
								"b times one, and b times zero",
								By(
									bm,
									comm_ring.MulRightZeroOn.Read(ring).At(bm),
									comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(bm)))
						}))
					pField := polynomial.PolynomialMulOver.Read(ring).AsFact().At(P, F)
					qField := polynomial.PolynomialMulOver.Read(ring).AsFact().At(Q, derivative)
					split := c.Have(
						"so at r the relation reads Q(r) F′(r) = b",
						"polynomial_eval(Q, r) * polynomial_eval(polynomial_derivative(«F»), r) = b",
						Derive(func(e *Argument) {
							evaluated := e.Have(
								"evaluate the relation at r",
								"polynomial_eval(vec_add(polynomial_mul(P, «F»), polynomial_mul(Q, polynomial_derivative(«F»))), "+
									"    r) = "+
									"b",
								asSum.RwRev(),
								identity.Rw(),
								constant.Rw(),
								By(bField, rField, polynomial_evaluation.EvalConstant.Read(ring).AsFact().At(b, r)))
							sum := e.Have(
								"the value of a sum is the sum of the values",
								"polynomial_eval(vec_add(polynomial_mul(P, «F»), polynomial_mul(Q, polynomial_derivative(«F»))), "+
									"    r) = "+
									"polynomial_eval(polynomial_mul(P, «F»), r) + "+
									"polynomial_eval(polynomial_mul(Q, polynomial_derivative(«F»)), r)",
								By(
									cField,
									dfOver,
									rField,
									pField,
									qField,
									polynomial_evaluation.EvalAdd.Read(ring).AsFact().At(pTimesF, qTimesDerivative, r)))
							first := e.Have(
								"the first term vanishes at the root r",
								"polynomial_eval(polynomial_mul(P, «F»), r) = M.zero",
								By(cField, rField, rRoot, polynomial_evaluation.EvalMulRoot.Read(ring).AsFact().At(F, P, r)))
							second := e.Have(
								"the second is the product of the values",
								"polynomial_eval(polynomial_mul(Q, polynomial_derivative(«F»)), r) = "+
									"polynomial_eval(Q, r) * polynomial_eval(polynomial_derivative(«F»), r)",
								By(cField, dfOver, rField, polynomial_evaluation.EvalMul.Read(ring).AsFact().At(Q, derivative, r)))
							yIn := e.Have(
								"the second term lies in M",
								"polynomial_eval(polynomial_mul(Q, polynomial_derivative(«F»)), r) ∈ M.carrier",
								By(
									cField,
									dfOver,
									rField,
									qField,
									polynomial_evaluation.EvalIn.Read(ring).AsFact().At(qTimesDerivative, r)))
							step := e.Have(
								"the sum is its second term",
								"polynomial_eval(vec_add(polynomial_mul(P, «F»), polynomial_mul(Q, polynomial_derivative(«F»))), "+
									"    r) = "+
									"polynomial_eval(polynomial_mul(Q, polynomial_derivative(«F»)), r)",
								sum.Rw(),
								first.Rw(),
								ByArith(ring, yIn))
							e.Show(
								"which leaves the second term",
								second.RwRev(),
								step.RwRev(),
								By(evaluated))
						}))
					w, wDef := c.LetAs[A]("w", "M.inv(b * d)")
					qValue := c.TermAs[A]("polynomial_eval(Q, r)")
					inverse := c.Have(
						"b d times w is one",
						"(b * d) * w = M.one",
						wDef.Rw(),
						By(uNonzero, uInField, field.MulRightInverseOn.Read(M).AsFact().At(u)))
					valueInC := c.Have(
						"F′(r) lies in C",
						"polynomial_eval(polynomial_derivative(«F»), r) ∈ ring_away(field_ring(M), «U», b * d)",
						By(
							c.Have(
								"F′ is over C",
								"polynomial_over(ring_away(field_ring(M), «U», b * d), polynomial_derivative(«F»))",
								By(
									subC,
									c.Have(
										"F is over C",
										"polynomial_over(ring_away(field_ring(M), «U», b * d), «F»)",
										By(bInC, fOver, polynomial.PolynomialOverMono.At(zero, B, C, F))),
									polynomial.DerivativeOver.Read(ring).AsFact().At(C, F))),
							rC,
							polynomial_evaluation.EvalIn.Read(ringC).AsFact().At(derivative, r)))
					inverted := c.Have(
						"Q(r) d w inverts it in C",
						"∃v:A. "+
							"    v ∈ ring_away(field_ring(M), «U», b * d) ∧ "+
							"    polynomial_eval(polynomial_derivative(«F»), r) * v = M.one",
						Derive(func(f *Argument) {
							f.Take(f.TermAs[A]("polynomial_eval(Q, r) * (d * w)"))
							f.Do(SplitConj(
								Case(
									"the cofactor lies in C",
									Derive(func(e *Argument) {
										qIn := e.Have(
											"Q(r) lies in C",
											"polynomial_eval(Q, r) ∈ ring_away(field_ring(M), «U», b * d)",
											By(qC, rC, polynomial_evaluation.EvalIn.Read(ringC).AsFact().At(Q, r)))
										dIn := e.Have(
											"d lies in C",
											"d ∈ ring_away(field_ring(M), «U», b * d)",
											BySets(dInB, bInC))
										dwIn := e.Have(
											"d w lies in C",
											"d * w ∈ ring_away(field_ring(M), «U», b * d)",
											By(subC, dIn, inverseInC, comm_ring.SubringMul.At(R, C, d, w)))
										e.Show(
											"as does the product",
											By(subC, qIn, dwIn, comm_ring.SubringMul.At(R, C, qValue, e.TermAs[A]("d * w"))))
									})),
								Case(
									"the product with F′(r) is one",
									Derive(func(e *Argument) {
										wField := e.Have(
											"w lies in M",
											"w ∈ M.carrier",
											BySets(inverseInC, cInField))
										values := e.Have(
											"Q(r) and F′(r) lie in M",
											"polynomial_eval(Q, r) ∈ M.carrier ∧ polynomial_eval(polynomial_derivative(«F»), r) ∈ M.carrier",
											By(
												cField,
												dfOver,
												polynomial_evaluation.EvalIn.Read(ring).At(Q, rm),
												polynomial_evaluation.EvalIn.Read(ring).At(derivative, rm)))
										regroup := e.Have(
											"regroup the product",
											"polynomial_eval(polynomial_derivative(«F»), r) * (polynomial_eval(Q, r) * (d * w)) = "+
												"(polynomial_eval(Q, r) * polynomial_eval(polynomial_derivative(«F»), r)) * (d * w)",
											ByArith(ring, values, bField, wField))
										again := e.Have(
											"and b (d w)",
											"b * (d * w) = (b * d) * w",
											ByArith(ring, bField, wField))
										e.Show(
											"which is (b d) w, one",
											regroup.Rw(),
											split.Rw(),
											again.Rw(),
											By(inverse))
									}))))
						}))
					c.Show(
						"so F′(r) is a unit of C",
						By(
							valueInC,
							inverted,
							ring_ideal.RingUnitDef.At(
								c.TermAs[module_record.RingOps[A]](
									"restrict_ring(field_ring(M), ring_away(field_ring(M), «U», b * d))"),
								c.TermAs[A]("polynomial_eval(polynomial_derivative(«F»), r)"))))
				}))))
	}),
})}

// ChartFacts — the rings of the chart. The ring k[t] holds k, t and u = a(t), the ring
// k[t][z] holds k[t] and z, and C = k[t][z][1/u] holds k[t][z] and the inverse of u
// inside L, so that inverting u again adds nothing.
var ChartFacts = chartFactsThm{family.Add(registry.ProofEntry{
	Name: "ChartFacts",
	Key:  "prop_fe14e82bb8a288d2",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t z:A. ∀a:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, L)",
			"k ⊆ L",
			"t ∈ L",
			"z ∈ L",
			"polynomial_over(k, a)",
			"polynomial_eval(a, t) ≠ M.zero",
		},
		Conclusion: "subring(field_ring(M), «B») ∧ " +
			"k ⊆ «B» ∧ " +
			"t ∈ «B» ∧ " +
			"polynomial_eval(a, t) ∈ «B» ∧ " +
			"subring(field_ring(M), «U») ∧ " +
			"«B» ⊆ «U» ∧ " +
			"z ∈ «U» ∧ " +
			"subring(field_ring(M), «C») ∧ " +
			"«U» ⊆ «C» ∧ " +
			"«C» ⊆ L ∧ " +
			"M.inv(polynomial_eval(a, t)) ∈ «C» ∧ " +
			"ring_away(field_ring(M), «C», polynomial_eval(a, t)) = «C»",
		Abbrev: Abbrev{
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t, z *Expr[A],
		a *Arrow[Nat, A],
		subk, subL, kInL, tIn, zIn, aOver, nonzero Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		B, U := arg.TermAs[Set[A]]("«B»"), arg.TermAs[Set[A]]("«U»")
		u := arg.TermAs[A]("polynomial_eval(a, t)")
		lField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subL, field.SubfieldSubset.At(fieldM, L)))
		tField := arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(tIn, lField))
		zField := arg.Have(
			"z lies in M",
			"z ∈ M.carrier",
			BySets(zIn, lField))
		tm, zm := arg.MemberOf[on.M](t, tField), arg.MemberOf[on.M](z, zField)
		kSubring := arg.Have(
			"k is a subring",
			"subring(field_ring(M), k)",
			By(subk, field.SubfieldSubring.Read(M).At(k)))
		ringL := arg.Have(
			"L is a ring",
			"comm_ring_on(restrict_ring(field_ring(M), L))",
			By(subL, field.SubfieldCommRing.Read(M).At(L)))
		base := arg.Conjuncts(
			GroupPremises(kSubring, algebraic_element.PolynomialImageSubring.Read(M).At(k, tm)),
			"k[t] is a subring",
			"holding k",
			"and t")
		image := arg.Conjuncts(
			GroupPremises(base[0], algebraic_element.PolynomialImageSubring.Read(M).At(B, zm)),
			"k[t][z] is a subring",
			"holding k[t]",
			"and z")
		subU, bInU := image[0], image[1]
		bInL := arg.Have(
			"k[t] lies in L",
			"«B» ⊆ L",
			By(ringL, kInL, tIn, algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(k, L, t)))
		uInL := arg.Have(
			"k[t][z] lies in L",
			"«U» ⊆ L",
			By(ringL, bInL, zIn, algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(B, L, z)))
		uInB := arg.Have(
			"u lies in k[t], the value of a polynomial over k",
			"polynomial_eval(a, t) ∈ «B»",
			BySets(aOver, algebraic_element.PolynomialImageDef.At(R, k, t)))
		uIn := arg.Have(
			"u lies in k[t][z]",
			"polynomial_eval(a, t) ∈ «U»",
			BySets(uInB, bInU))
		chart := arg.Have(
			"C is a subring holding k[t][z], inside L, stable under inverting u",
			"subring(field_ring(M), «C») ∧ "+
				"«U» ⊆ «C» ∧ "+
				"«C» ⊆ L ∧ "+
				"M.inv(polynomial_eval(a, t)) ∈ «C» ∧ "+
				"ring_away(field_ring(M), «C», polynomial_eval(a, t)) = «C»",
			By(subU, subL, uInL, uIn, nonzero, ring_away.RingAwayInSubfield.Read(M).At(U, L, u)))
		arg.Show(
			"which are the claims",
			By(base[0], base[1], base[2], uInB, subU, bInU, image[2], chart))
	}),
})}

// GaloisChartRing — the ring C = k[t][z][1/u], for u = a(t) a nonzero value of a
// polynomial over k, is a subring of L holding k[t][1/u], unchanged by inverting u
// again, finite over k[t][1/u] on the powers of z, and with fraction field L since
// every element of L has a denominator in k[t] carrying it into k[t][z].
var GaloisChartRing = galoisChartRingThm{family.Add(registry.ProofEntry{
	Name: "GaloisChartRing",
	Key:  "prop_d8b06b78c3ba8b1",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t z:A. ∀a:(num → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, L)",
			"k ⊆ L",
			"t ∈ L",
			"z ∈ L",
			"field_adjoin(M, «K», {z}) = L",
			"algebraic_over(M, «K», z)",
			"polynomial_over(«B», minimal_polynomial(M, «K», z))",
			"polynomial_over(k, a)",
			"polynomial_eval(a, t) ≠ M.zero",
		},
		Conclusion: "«C» ⊆ L ∧ " +
			"comm_ring_on(restrict_ring(field_ring(M), «C»)) ∧ " +
			"ring_away(field_ring(M), «B», polynomial_eval(a, t)) ⊆ «C» ∧ " +
			"«C» = ring_away(field_ring(M), «C», polynomial_eval(a, t)) ∧ " +
			"fraction_field_carrier(restrict_ring(field_ring(M), L), «C») ∧ " +
			"module_finitely_generated( " +
			"    restrict_ring(field_ring(M), ring_away(field_ring(M), «B», polynomial_eval(a, t))), " +
			"    restrict_module(regular_module(field_ring(M)), «C»))",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
			{Name: "powers", Text: "{monoid_pow(M.mul, M.one, z, i) | " +
				"    i:num | " +
				"    i < polynomial_degree(minimal_polynomial(M, «K», z))}"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t, z *Expr[A],
		a *Arrow[Nat, A],
		subk, subL, kInL, tIn, zIn, generated, algebraic, fOver, aOver, nonzero Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		K, B, U := arg.TermAs[Set[A]]("«K»"), arg.TermAs[Set[A]]("«B»"), arg.TermAs[Set[A]]("«U»")
		C := arg.TermAs[Set[A]]("«C»")
		u := arg.TermAs[A]("polynomial_eval(a, t)")
		lField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subL, field.SubfieldSubset.At(fieldM, L)))
		tField := arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(tIn, lField))
		zField := arg.Have(
			"z lies in M",
			"z ∈ M.carrier",
			BySets(zIn, lField))
		tm := arg.MemberOf[on.M](t, tField)
		facts := arg.Conjuncts(
			GroupPremises(subk, subL, kInL, tIn, zIn, aOver, nonzero, ChartFacts.Read(M).At(k, L, t, z, a)),
			"k[t] is a subring",
			"holding k",
			"and t",
			"and u",
			"k[t][z] is a subring",
			"holding k[t]",
			"and z",
			"C is a subring",
			"holding k[t][z]",
			"inside L",
			"with the inverse of u",
			"stable under inverting u")
		subB, uInB, subU, bInU := facts[0], facts[3], facts[4], facts[5]
		subC, uInC, cInL, stable := facts[7], facts[8], facts[9], facts[11]
		bInL := arg.Have(
			"k[t] lies in L",
			"«B» ⊆ L",
			BySets(bInU, uInC, cInL))
		adjoinedK := arg.Conjuncts(
			GroupPremises(subk, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)),
			"k(t) is a subfield",
			"holding k",
			"and t")
		subK := adjoinedK[0]
		fractions := arg.Have(
			"k(t) is the fraction field of k[t]",
			"fraction_field_carrier(restrict_ring(field_ring(M), «K»), «B»)",
			By(subk, tField, integral_element.RationalFunctionsFractionField.Read(M).At(k, tm)))
		bInK := arg.Have(
			"k[t] lies in k(t)",
			"«B» ⊆ «K»",
			By(subk, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		uNonzeroFacts := arg.Have(
			"u is a nonzero element of k[t]",
			"polynomial_eval(a, t) ∈ «B» ∧ polynomial_eval(a, t) ≠ M.zero",
			By(uInB, nonzero))
		basis := arg.Conjuncts(
			arg.Have(
				"the powers of z below the degree are a basis of k[t][z] over k[t]",
				"module_on(restrict_ring(field_ring(M), «B»), "+
					"    restrict_module(regular_module(field_ring(M)), «U»)) ∧ "+
					"module_basis(restrict_ring(field_ring(M), «B»), "+
					"    restrict_module(regular_module(field_ring(M)), «U»), "+
					"    «powers») ∧ "+
					"has_size(«powers», polynomial_degree(minimal_polynomial(M, «K», z)))",
				By(
					subK,
					zField,
					algebraic,
					bInK,
					subB,
					fOver,
					integral_element.MonicSubringPowerBasis.Read(M).AsFact().At(K, B, z))),
			"k[t][z] is a module over k[t]",
			"the powers are a basis",
			"there are degree many")
		awayBasis := arg.Have(
			"they stay a basis after inverting u",
			"module_basis( "+
				"    restrict_ring(field_ring(M), ring_away(field_ring(M), «B», polynomial_eval(a, t))), "+
				"    restrict_module(regular_module(field_ring(M)), «C»), "+
				"    «powers»)",
			By(
				subB,
				subU,
				bInU,
				uNonzeroFacts,
				basis[1],
				ring_away.BasisAway.Read(M).At(B, U, u, arg.TermAs[Set[A]]("«powers»"))))
		arg.Do(SplitConjAll(
			Case(
				"C lies in L",
				By(cInL)),
			Case(
				"C is a ring",
				By(subC, comm_ring.SubringRingOn.Read(ring).At(C))),
			Case(
				"k[t][1/u] lies in C",
				Derive(func(c *Argument) {
					pointwise := c.Have(
						"a clearing power into k[t] clears into k[t][z]",
						"∀r:A. r ∈ ring_away(field_ring(M), «B», polynomial_eval(a, t)) ⇒ r ∈ «C»",
						Derive(func(e *Argument) {
							r := e.FixAs[A]("r")
							rIn := e.Assume()
							member := e.Conjuncts(
								e.Have(
									"r lies in M with a power of u carrying it into k[t]",
									"r ∈ M.carrier ∧ ∃n:num. monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * r ∈ «B»",
									By(rIn, ring_away.RingAwayMember.At(R, B, u, r))),
								"r lies in M",
								"a power of u clears it")
							witness := e.Have(
								"the same power carries it into k[t][z]",
								"∃n:num. monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * r ∈ «U»",
								BySets(member[1], bInU))
							e.Show(
								"which is membership in C",
								By(member[0], witness, ring_away.RingAwayMember.At(R, U, u, r)))
						}))
					c.Show(
						"so the inclusion holds",
						BySets(pointwise))
				})),
			Case(
				"inverting u again adds nothing",
				By(stable)),
			Case(
				"L is the fraction field of C",
				Derive(func(c *Argument) {
					quotients := c.Have(
						"each element of L is a fraction of C",
						"∀y:A. y ∈ L ⇒ ∃p q:A. p ∈ «C» ∧ q ∈ «C» ∧ q ≠ M.zero ∧ y * q = p",
						Derive(func(e *Argument) {
							y := e.FixAs[A]("y")
							yIn := e.Assume()
							inAdjoin := e.Have(
								"y lies in k(t)(z)",
								"y ∈ field_adjoin(M, «K», {z})",
								generated.Rw(),
								By(yIn))
							d, denominator := e.ObtainAs[A](
								"a denominator of y in k[t]",
								"∃d:A. d ∈ «B» ∧ d ≠ M.zero ∧ d * y ∈ «U»",
								By(
									subK,
									subB,
									fractions,
									zField,
									algebraic,
									inAdjoin,
									integral_element.AdjoinCommonDenominator.Read(M).AsFact().At(K, B, z, y)))
							parts := e.Conjuncts(
								denominator,
								"d lies in k[t]",
								"d is not zero",
								"d y lies in k[t][z]")
							dField := e.Have(
								"d lies in M",
								"d ∈ M.carrier",
								BySets(parts[0], bInL, lField))
							yField := e.Have(
								"y lies in M",
								"y ∈ M.carrier",
								BySets(yIn, lField))
							inC := e.Have(
								"d and d y lie in C",
								"d ∈ «C» ∧ d * y ∈ «C»",
								BySets(parts[0], parts[2], bInU, uInC))
							swap := e.Have(
								"y d is d y",
								"y * d = d * y",
								ByArith(ring, dField, yField))
							e.Take(e.TermAs[A]("d * y"))
							e.Take(d)
							e.Show(
								"d y over d",
								By(inC, parts[1], swap))
						}))
					c.Show(
						"which is the fraction field",
						By(
							cInL,
							quotients,
							field.FractionFieldCarrierDef.At(
								c.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), L)"), C)))
				})),
			Case(
				"C is finite over k[t][1/u]",
				Derive(func(c *Argument) {
					opened := c.Conjuncts(
						c.Have(
							"the basis spans C and is finite",
							"finite(«powers») ∧ "+
								"«powers» ⊆ restrict_module(regular_module(field_ring(M)), «C»).carrier ∧ "+
								"module_span(restrict_ring(field_ring(M), ring_away(field_ring(M), «B», polynomial_eval(a, t))), "+
								"    restrict_module(regular_module(field_ring(M)), «C»), "+
								"    «powers») = "+
								"restrict_module(regular_module(field_ring(M)), «C»).carrier",
							Derive(func(e *Argument) {
								sized := e.Unfolded(basis[2], cardinality.HasSizeDef)
								spanning := e.Unfolded(awayBasis, linear_independence.ModuleBasisDef)
								independent := e.Conjuncts(
									spanning,
									"the powers are independent",
									"they span")
								inside := e.Unfolded(independent[0], linear_independence.ModuleIndependentDef)
								e.Show(
									"read off the definitions",
									By(sized, inside, independent[1]))
							})),
						"the powers are finite",
						"they lie in C",
						"they span C")
					c.Do(Unfold(principal_ideal_domain.FinitelyGeneratedDef))
					c.Take(c.TermAs[Set[A]]("«powers»"))
					c.Show(
						"the powers generate C",
						By(opened[0], opened[1], opened[2]))
				}))))
	}),
})}

// GaloisChartStable — the group preserves the chart C = k[t][z][1/u] once it holds the
// conjugates of z. An automorphism p fixes k(t), so it sends the value at z of a
// polynomial over k[t] to the value at p(z) of the same polynomial, a point of C, and
// it fixes the powers of u, so a member r of C goes to a member of C. The inverse of an
// automorphism does the same, so the image of C is all of C.
var GaloisChartStable = galoisChartStableThm{family.Add(registry.ProofEntry{
	Name: "GaloisChartStable",
	Key:  "prop_f3247c76fb318ca0",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t z:A. ∀a:(num → A). ∀s:permutation(A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, L)",
			"k ⊆ L",
			"t ∈ L",
			"z ∈ L",
			"polynomial_over(k, a)",
			"polynomial_eval(a, t) ≠ M.zero",
			"∀p:permutation(A). p ∈ «G» ⇒ permutation_map(p, z) ∈ «C»",
			"s ∈ «G»",
		},
		Conclusion: "image(permutation_map(s), «C») = «C»",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
			{Name: "G", Text: "field_automorphisms(M, «K», L)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t, z *Expr[A],
		a *Arrow[Nat, A],
		s *Expr[symmetric_group.Permutation[A]],
		subk, subL, kInL, tIn, zIn, aOver, nonzero, conjugates, sIn Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		zero := arg.TermAs[A]("M.zero")
		K, B, U := arg.TermAs[Set[A]]("«K»"), arg.TermAs[Set[A]]("«B»"), arg.TermAs[Set[A]]("«U»")
		C := arg.TermAs[Set[A]]("«C»")
		u := arg.TermAs[A]("polynomial_eval(a, t)")
		G := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«G»")
		lField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subL, field.SubfieldSubset.At(fieldM, L)))
		tField := arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(tIn, lField))
		tm := arg.MemberOf[on.M](t, tField)
		facts := arg.Conjuncts(
			GroupPremises(subk, subL, kInL, tIn, zIn, aOver, nonzero, ChartFacts.Read(M).At(k, L, t, z, a)),
			"k[t] is a subring",
			"holding k",
			"and t",
			"and u",
			"k[t][z] is a subring",
			"holding k[t]",
			"and z",
			"C is a subring",
			"holding k[t][z]",
			"inside L",
			"with the inverse of u",
			"stable under inverting u")
		subB, uInB, bInU := facts[0], facts[3], facts[5]
		subC, uInC, cInL, stable := facts[7], facts[8], facts[9], facts[11]
		bInL := arg.Have(
			"k[t] lies in L",
			"«B» ⊆ L",
			BySets(bInU, uInC, cInL))
		ringC := arg.Have(
			"C is a ring",
			"comm_ring_on(restrict_ring(field_ring(M), «C»))",
			By(subC, comm_ring.SubringRingOn.Read(ring).At(C)))
		ringB := arg.Have(
			"k[t] is a ring",
			"comm_ring_on(restrict_ring(field_ring(M), «B»))",
			By(subB, comm_ring.SubringRingOn.Read(ring).At(B)))
		bInK := arg.Have(
			"k[t] lies in k(t)",
			"«B» ⊆ «K»",
			By(subk, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		rL := arg.TermAs[module_record.RingOps[A]]("field_ring(restrict_field(M, L))")
		keeps := arg.Have(
			"each automorphism keeps C",
			"∀p:permutation(A). ∀r:A. p ∈ «G» ∧ r ∈ «C» ⇒ permutation_map(p, r) ∈ «C»",
			Derive(func(b *Argument) {
				p := b.FixAs[symmetric_group.Permutation[A]]("p")
				r := b.FixAs[A]("r")
				parts := b.Conjuncts(
					b.Assume(),
					"p is an automorphism",
					"r lies in C")
				pIn, rIn := parts[0], parts[1]
				e := b.TermAs[Fun[A, A]]("permutation_map(p)")
				hom := b.Have(
					"p is a homomorphism of L",
					"ring_homomorphism(field_ring(restrict_field(M, L)), "+
						"    field_ring(restrict_field(M, L)), "+
						"    permutation_map(p))",
					By(subL, pIn, field_automorphism.AutomorphismRingHomomorphism.Read(M).AsFact().At(K, L, p)))
				opened := b.Unfolded(pIn, field_automorphism.FieldAutomorphismsDef)
				fixed := b.Have(
					"p fixes k(t)",
					"∀x:A. x ∈ «K» ⇒ permutation_map(p, x) = x",
					BySets(opened))
				rInL := b.Have(
					"r lies in L",
					"r ∈ L",
					BySets(rIn, cInL))
				member := b.Conjuncts(
					b.Have(
						"r lies in M with a power of u carrying it into k[t][z]",
						"r ∈ M.carrier ∧ ∃n:num. monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * r ∈ «U»",
						By(rIn, ring_away.RingAwayMember.At(R, U, u, r))),
					"r lies in M",
					"a power of u clears it")
				n, cleared := b.UnpackAs[Nat](member[1], "n")
				q, value := b.ObtainAs[Fun[Nat, A]](
					"uⁿ r is a polynomial in z over k[t]",
					"∃q:(num → A). "+
						"    polynomial_over(«B», q) ∧ "+
						"    monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * r = polynomial_eval(q, z)",
					BySets(cleared, algebraic_element.PolynomialImageDef.At(R, B, z)))
				qParts := b.Conjuncts(
					value,
					"q is over k[t]",
					"uⁿ r is its value at z")
				qOver, rewritten := qParts[0], qParts[1]
				qL := b.Have(
					"q is a polynomial over L",
					"polynomial_over(L, q)",
					By(bInL, qOver, polynomial.PolynomialOverMono.At(zero, B, L, q)))
				qC := b.Have(
					"q is a polynomial over C",
					"polynomial_over(«C», q)",
					By(
						qOver,
						b.Have(
							"k[t] lies in C",
							"«B» ⊆ «C»",
							BySets(bInU, uInC)),
						polynomial.PolynomialOverMono.At(zero, B, C, q)))
				along := b.Have(
					"p moves the value of q to the value of the moved polynomial at p(z)",
					"permutation_map(p, polynomial_eval(q, z)) = "+
						"polynomial_eval(λi:num. permutation_map(p, q(i)), permutation_map(p, z))",
					By(hom, qL, zIn, polynomial_evaluation.EvalAlongHomomorphism.At(rL, rL, e, q, z)))
				same := b.Have(
					"which fixes the coefficients of q",
					"(λi:num. permutation_map(p, q(i))) = q",
					Derive(func(c *Argument) {
						c.Do(Funext())
						c.FixAs[Nat]("i")
						inB := c.Have(
							"each coefficient lies in k[t]",
							"q(i) ∈ «B»",
							By(qOver, polynomial.PolynomialOverDef.At(zero, B, q)))
						c.Show(
							"so in k(t)",
							By(
								fixed.At(c.TermAs[A]("q(i)")),
								c.Have(
									"it lies in k(t)",
									"q(i) ∈ «K»",
									BySets(inB, bInK))))
					}))
				moved := b.Have(
					"p(uⁿ r) lies in C",
					"permutation_map(p, monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * r) ∈ «C»",
					rewritten.Rw(),
					along.Rw(),
					same.Rw(),
					By(
						qC,
						conjugates.At(p),
						pIn,
						polynomial_evaluation.EvalIn.Read(ringC).AsFact().At(q, b.TermAs[A]("permutation_map(p, z)"))))
				pow := b.TermAs[A]("monoid_pow(M.mul, M.one, polynomial_eval(a, t), n)")
				powB := b.Have(
					"uⁿ lies in k[t]",
					"monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) ∈ «B»",
					By(uInB, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringB)).AsFact().At(u, n)))
				powFixed := b.Have(
					"so p fixes it",
					"permutation_map(p, monoid_pow(M.mul, M.one, polynomial_eval(a, t), n)) = "+
						"monoid_pow(M.mul, M.one, polynomial_eval(a, t), n)",
					By(
						fixed.At(pow),
						b.Have(
							"uⁿ lies in k(t)",
							"monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) ∈ «K»",
							BySets(powB, bInK))))
				split := b.Have(
					"p is multiplicative on L",
					"permutation_map(p, monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * r) = "+
						"monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * permutation_map(p, r)",
					Derive(func(c *Argument) {
						powerAndRInL := c.Have(
							"uⁿ and r lie in L",
							"monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) ∈ L ∧ r ∈ L",
							Derive(func(d *Argument) {
								d.Show(
									"through k[t]",
									BySets(powB, bInL, rInL))
							}))
						c.Show(
							"so p(uⁿ r) is uⁿ p(r)",
							GroupPremises(powerAndRInL, ring_homomorphism.MapMul.Read(hom).AsFact().At(pow, r)).Rw(),
							powFixed.Rw(),
							Basic())
					}))
				witness := b.Have(
					"one power of u carries p(r) into C",
					"∃n:num. monoid_pow(M.mul, M.one, polynomial_eval(a, t), n) * permutation_map(p, r) ∈ «C»",
					Derive(func(c *Argument) {
						c.Take(n)
						c.Show(
							"the same power",
							split.RwRev(),
							By(moved))
					}))
				inField := b.Have(
					"p(r) lies in M",
					"permutation_map(p, r) ∈ M.carrier",
					BySets(rInL, lField, ring_homomorphism.MapIn.Read(hom).AsFact().At(r)))
				member2 := b.Have(
					"so p(r) lies in the localization of C at u",
					"permutation_map(p, r) ∈ ring_away(field_ring(M), «C», polynomial_eval(a, t))",
					By(inField, witness, ring_away.RingAwayMember.At(R, C, u, b.TermAs[A]("permutation_map(p, r)"))))
				b.Show(
					"which is C",
					By(stable, member2))
			}))
		inverse := arg.Have(
			"the inverse of s is an automorphism",
			"permutation_inverse(s) ∈ «G»",
			By(
				sIn,
				field_automorphism.AutomorphismsSubgroup.Read(M).At(K, L),
				group.SubgroupInv.At(
					arg.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("permutation_group"), G, s)))
		forward := arg.Have(
			"s keeps C",
			"image(permutation_map(s), «C») ⊆ «C»",
			BySets(sIn, keeps))
		backward := arg.Have(
			"each point of C is the image of a point of C",
			"«C» ⊆ image(permutation_map(s), «C»)",
			Derive(func(c *Argument) {
				pointwise := c.Have(
					"its preimage under s lies in C",
					"∀y:A. y ∈ «C» ⇒ ∃x:A. x ∈ «C» ∧ y = permutation_map(s, x)",
					Derive(func(e *Argument) {
						y := e.FixAs[A]("y")
						yIn := e.Assume()
						e.Take(e.TermAs[A]("permutation_map(permutation_inverse(s), y)"))
						e.Show(
							"the inverse of s keeps C",
							By(
								inverse,
								yIn,
								keeps.At(e.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)"), y),
								symmetric_group.MapInverseRight.At(s, y)))
					}))
				c.Show(
					"so C lies in the image",
					BySets(pointwise))
			}))
		arg.Show(
			"the two inclusions",
			By(
				forward,
				backward,
				set_order.SubsetAntisym.At(arg.TermAs[Set[A]]("image(permutation_map(s), «C»)"), C)))
	}),
})}

// ChartPointDetermined — a point of the chart C = k[t][z][1/u] is determined by its
// values at t and z. Two points that agree there agree on k, which they fix, so on
// k[t] and on k[t][z], and a point of C is determined by its restriction to k[t][z],
// of which C is the localization at u.
var ChartPointDetermined = chartPointDeterminedThm{family.Add(registry.ProofEntry{
	Name: "ChartPointDetermined",
	Key:  "prop_f36404031dc8f3f6",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀t z:A. ∀a:(num → A). ∀ev ew:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"t ∈ M.carrier",
			"z ∈ M.carrier",
			"polynomial_over(k, a)",
			"polynomial_eval(a, t) ≠ M.zero",
			"ev ∈ geometric_evaluation_points(M, k, «C»)",
			"ew ∈ geometric_evaluation_points(M, k, «C»)",
			"ev(t) = ew(t)",
			"ev(z) = ew(z)",
		},
		Conclusion: "ev = ew",
		Abbrev: Abbrev{
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
			{Name: "chart", Text: "restrict_ring(field_ring(M), «C»)"},
			{Name: "target", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		t, z *Expr[A],
		a *Arrow[Nat, A],
		ev, ew *Arrow[A, A],
		subk, tIn, zIn, aOver, nonzero, evIn, ewIn, atT, atZ Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldM := arg.TermAs[FieldOps[A]]("M")
		carrier := arg.TermAs[Set[A]]("M.carrier")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		chartRing := arg.TermAs[module_record.RingOps[A]]("«chart»")
		target := arg.TermAs[module_record.RingOps[A]]("«target»")
		B, U, C := arg.TermAs[Set[A]]("«B»"), arg.TermAs[Set[A]]("«U»"), arg.TermAs[Set[A]]("«C»")
		u := arg.TermAs[A]("polynomial_eval(a, t)")
		mSubfield := arg.Have(
			"M is a subfield of itself",
			"subfield(M, M.carrier)",
			By(field.CarrierSubfield.Read(M)))
		kInM := arg.Have(
			"k lies in M",
			"k ⊆ M.carrier",
			By(subk, field.SubfieldSubset.At(fieldM, k)))
		facts := arg.Conjuncts(
			GroupPremises(
				subk, mSubfield, kInM, tIn, zIn, aOver, nonzero, ChartFacts.Read(M).At(k, carrier, t, z, a)),
			"k[t] is a subring",
			"holding k",
			"and t",
			"and u",
			"k[t][z] is a subring",
			"holding k[t]",
			"and z",
			"C is a subring",
			"holding k[t][z]",
			"inside M",
			"with the inverse of u",
			"inverting u again adds nothing")
		kInB, tInB, uInB, subU, bInU, zInU := facts[1], facts[2], facts[3], facts[4], facts[5], facts[6]
		uInC, cInField := facts[8], facts[9]
		bInC := arg.Have(
			"k[t] lies in C",
			"«B» ⊆ «C»",
			BySets(bInU, uInC))
		kInC := arg.Have(
			"k lies in C",
			"k ⊆ «C»",
			BySets(kInB, bInC))
		tInC := arg.Have(
			"t lies in C",
			"t ∈ «C»",
			BySets(tInB, bInC))
		zInC := arg.Have(
			"z lies in C",
			"z ∈ «C»",
			BySets(zInU, uInC))
		evData := arg.Conjuncts(
			arg.Have(
				"ev is a ring map on C, fixing k",
				"ring_homomorphism(«chart», «target», ev) ∧ (∀x:A. x ∈ k ⇒ ev(x) = x)",
				By(evIn, galois_good_open.GeometricPointMember.At(fieldM, k, C, ev))),
			"ev is a ring map",
			"ev fixes k")
		ewData := arg.Conjuncts(
			arg.Have(
				"so is ew",
				"ring_homomorphism(«chart», «target», ew) ∧ (∀x:A. x ∈ k ⇒ ew(x) = x)",
				By(ewIn, galois_good_open.GeometricPointMember.At(fieldM, k, C, ew))),
			"ew is a ring map",
			"ew fixes k")
		constants := arg.Have(
			"the two agree on k",
			"∀c:A. c ∈ k ⇒ ev(c) = ew(c)",
			By(Normalized, evData[1], ewData[1]))
		polynomials := arg.Have(
			"so on k[t]",
			"∀y:A. y ∈ «B» ⇒ ev(y) = ew(y)",
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				b.Show(
					"polynomials over k at t",
					By(
						evData[0],
						ewData[0],
						kInC,
						tInC,
						constants,
						atT,
						b.Assume(),
						integral_element.PolynomialImageAgreement.Read(M).At(target, C, k, ev, ew, t, y)))
			}))
		values := arg.Have(
			"and on k[t][z]",
			"∀y:A. y ∈ «U» ⇒ ev(y) = ew(y)",
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				b.Show(
					"polynomials over k[t] at z",
					By(
						evData[0],
						ewData[0],
						bInC,
						zInC,
						polynomials,
						atZ,
						b.Assume(),
						integral_element.PolynomialImageAgreement.Read(M).At(target, C, B, ev, ew, z, y)))
			}))
		uField := arg.Have(
			"u lies in M",
			"polynomial_eval(a, t) ∈ M.carrier",
			BySets(uInB, bInU, uInC, cInField))
		um := arg.MemberOf[on.M](u, uField)
		inverse := field.InvIn.Read(M).At(um)
		uInU := arg.Have(
			"u lies in k[t][z]",
			"polynomial_eval(a, t) ∈ «U»",
			BySets(uInB, bInU))
		localization := arg.Have(
			"C is the localization of k[t][z] at the powers of u",
			"is_localization_on(restrict_ring(«chart», «U»), "+
				"    monoid_powers(«chart».mul, «chart».one, polynomial_eval(a, t)), "+
				"    «chart», "+
				"    λx:A. x)",
			By(
				ring,
				uInU,
				subU,
				inverse,
				nonzero,
				field.MulRightInverseOn.Read(M).At(um),
				ring_away.RingAwayIsLocalization.At(R, U, u, inverse),
				module_record.RestrictRingTwice.At(R, C, U),
				module_record.RingMulDef,
				module_record.RingOneDef,
				module_record.RestrictRingDef))
		injective := arg.Have(
			"so restriction to k[t][z] is injective on the points of C",
			"injective_on(algebra_points(«chart», «target», k, λx:A. x), "+
				"    λφ:(A → A). λx:A. COND(x ∈ «U», φ(x), «target».zero))",
			By(
				localization,
				uInU,
				arg.Have(
					"k lies in k[t][z]",
					"k ⊆ «U»",
					BySets(kInB, bInU)),
				algebra_point_bounds.AlgebraPointsAway.At(
					chartRing, target, U, k, arg.TermAs[Fun[A, A]]("λx:A. x"), u)))
		restricted := arg.Have(
			"and the restrictions of ev and ew are one",
			"(λx:A. COND(x ∈ «U», ev(x), «target».zero)) = (λx:A. COND(x ∈ «U», ew(x), «target».zero))",
			Derive(func(b *Argument) {
				b.Do(Funext())
				b.FixAs[A]("x")
				b.Show(
					"they agree on k[t][z]",
					BySets(values))
			}))
		arg.Show(
			"so ev and ew are one",
			By(
				arg.Have(
					"ev and ew are points of C",
					"ev ∈ algebra_points(«chart», «target», k, λx:A. x) ∧ "+
						"ew ∈ algebra_points(«chart», «target», k, λx:A. x)",
					By(evIn, ewIn, galois_good_open.GeometricEvaluationPointsDef.At(fieldM, k, C))),
				injective,
				restricted,
				functions.InjectiveOnDef))
	}),
})}

// PointExtendsAtRoot — in an algebraically closed M, let g be monic of positive degree
// over a subring S, a relation of z over S of least degree. A point e of S extends to a
// point of S[z]: the image of g, of the degree of g, has a root among the algebraic
// elements, and e extends at that root.
var PointExtendsAtRoot = pointExtendsAtRootThm{family.Add(registry.ProofEntry{
	Name: "PointExtendsAtRoot",
	Key:  "prop_8d88a3d28e6e0512",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k S:set(A). ∀e:(A → A). ∀g:(num → A). ∀z:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"subring(field_ring(M), S)",
			"k ⊆ S",
			"z ∈ M.carrier",
			"polynomial_over(S, g)",
			"polynomial_monic(g)",
			"0 < polynomial_degree(g)",
			"polynomial_eval(g, z) = M.zero",
			"∀q:(num → A). " +
				"    polynomial_over(S, q) ∧ q ≠ vec_zero ∧ polynomial_eval(q, z) = M.zero ⇒ " +
				"    polynomial_degree(g) ≤ polynomial_degree(q)",
			"ring_homomorphism(restrict_ring(field_ring(M), S), «target», e)",
			"∀c:A. c ∈ k ⇒ e(c) = c",
		},
		Conclusion: "∃ev:(A → A). ev ∈ geometric_evaluation_points(M, k, «I») ∧ ∀x:A. x ∈ S ⇒ ev(x) = e(x)",
		Abbrev: Abbrev{
			{Name: "target", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
			{Name: "I", Text: "polynomial_image(field_ring(M), S, z)"},
			{Name: "image", Text: "λi:num. e(g(i))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, S *Expr[Set[A]],
		e *Arrow[A, A],
		g *Arrow[Nat, A],
		z *Expr[A],
		closed, subk, subS, kInS, zIn, over, monic, positive, root, least, hom, fixes Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		zero := arg.TermAs[A]("M.zero")
		target := arg.TermAs[module_record.RingOps[A]]("«target»")
		image := arg.TermAs[Fun[Nat, A]]("«image»")
		closure, I := arg.TermAs[Set[A]]("algebraic_elements(M, k)"), arg.TermAs[Set[A]]("«I»")
		keepsZero := ring_homomorphism.MapZero.Read(hom)
		imageOver := arg.Have(
			"the image of g is a polynomial over the algebraic elements",
			"polynomial_over(algebraic_elements(M, k), «image»)",
			By(
				over,
				keepsZero,
				ring_homomorphism.MapIn.Read(hom),
				polynomial.PolynomialOverMap.At(e, zero, zero, S, closure, g)))
		leading := arg.Have(
			"its coefficient at the degree of g is one",
			"e(g(polynomial_degree(g))) = M.one",
			arg.Unfolded(monic, polynomial.PolynomialMonicDef).Rw(),
			By(ring_homomorphism.MapOne.Read(hom)))
		degree := arg.Have(
			"so it has the degree of g",
			"polynomial_degree(«image») = polynomial_degree(g)",
			By(
				imageOver,
				over,
				keepsZero,
				leading,
				field.OneNotZeroOn.Read(M),
				polynomial.DegreeVec.At(zero, S, g),
				At(polynomial.VecMap, e, zero, zero, arg.TermAs[Nat]("suc(polynomial_degree(g))"), g),
				polynomial.DegreeExact.At(zero, closure, image, arg.TermAs[Nat]("polynomial_degree(g)"))))
		w, atRoot := arg.ObtainAs[A](
			"it has a root w among the algebraic elements",
			"∃w:A. w ∈ algebraic_elements(M, k) ∧ polynomial_eval(«image», w) = M.zero",
			By(
				closed,
				subk,
				imageOver,
				arg.Have(
					"of positive degree",
					"0 < polynomial_degree(«image»)",
					degree.Rw(),
					By(positive)),
				algebraic_closure.AlgebraicElementsClosed.Read(M).At(k, image)))
		rootParts := arg.Conjuncts(
			atRoot,
			"w is algebraic",
			"the image of g vanishes at w")
		h, extended := arg.ObtainAs[Fun[A, A]](
			"e extends to S[z], sending z to w",
			"∃h:(A → A). "+
				"    ring_homomorphism(restrict_ring(field_ring(M), «I»), «target», h) ∧ "+
				"    (∀x:A. x ∈ S ⇒ h(x) = e(x)) ∧ "+
				"    h(z) = w",
			By(
				subS,
				zIn,
				over,
				monic,
				root,
				least,
				hom,
				rootParts[0],
				rootParts[1],
				algebraic_element.HomomorphismExtendsAtRoot.Read(field.RingOn.Read(M)).AsFact().At(
					target, S, e, g, z, w)))
		parts := arg.Conjuncts(
			extended,
			"h is a ring map on S[z]",
			"h agrees with e on S",
			"h sends z to w")
		onI := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), «I»)")
		restricted := arg.TermAs[Fun[A, A]]("λy:A. COND(y ∈ «I», h(y), M.zero)")
		sInI := arg.Conjuncts(
			GroupPremises(
				subS, algebraic_element.PolynomialImageSubring.Read(M).At(S, arg.MemberOf[on.M](z, zIn))),
			"S[z] is a subring",
			"holding S",
			"and z")[1]
		restrictedMap := arg.Have(
			"h cut off outside S[z] is the same ring map",
			"ring_homomorphism(restrict_ring(field_ring(M), «I»), «target», λy:A. COND(y ∈ «I», h(y), M.zero))",
			By(parts[0], ring_homomorphism.RingHomCongruence.At(onI, target, h, restricted)))
		agrees := arg.Have(
			"on S it is e",
			"∀x:A. x ∈ S ⇒ COND(x ∈ «I», h(x), M.zero) = e(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				inI := b.Have(
					"x lies in S[z]",
					"x ∈ «I»",
					BySets(xIn, sInI))
				b.Show(
					"where h agrees with e",
					By(xIn, inI, parts[1].At(x)))
			}))
		fixed := arg.Have(
			"so it fixes k",
			"∀c:A. c ∈ k ⇒ COND(c ∈ «I», h(c), M.zero) = c",
			Derive(func(b *Argument) {
				c := b.FixAs[A]("c")
				cIn := b.Assume()
				inS := b.Have(
					"c lies in S",
					"c ∈ S",
					BySets(cIn, kInS))
				b.Show(
					"and e fixes c",
					By(cIn, inS, agrees.At(c), fixes.At(c)))
			}))
		point := arg.Have(
			"it is a point of S[z]",
			"(λy:A. COND(y ∈ «I», h(y), M.zero)) ∈ geometric_evaluation_points(M, k, «I»)",
			By(
				restrictedMap,
				fixed,
				arg.Have(
					"and it vanishes off S[z]",
					"∀y:A. y ∉ «I» ⇒ COND(y ∈ «I», h(y), M.zero) = M.zero",
					BySets()),
				galois_good_open.GeometricPointMember.At(fieldM, k, I, restricted)))
		arg.Take(restricted)
		arg.Show(
			"extending e",
			By(point, agrees))
	}),
})}

// ChartFibreNonempty — in an algebraically closed M, the chart has a point over each
// algebraic x with a(x) ≠ 0. As t is transcendental, k[t] has a point sending t to x, it
// extends to k[t][z] at a root of the image of the minimal polynomial of z, and then to
// C, the point sending a(t) to a(x) ≠ 0.
var ChartFibreNonempty = chartFibreNonemptyThm{family.Add(registry.ProofEntry{
	Name: "ChartFibreNonempty",
	Key:  "prop_d84cf44942ec84ce",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀t z x:A. ∀a:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"t ∈ M.carrier",
			"z ∈ M.carrier",
			"¬algebraic_over(M, k, t)",
			"algebraic_over(M, «K», z)",
			"polynomial_over(«B», «F»)",
			"polynomial_over(k, a)",
			"polynomial_eval(a, t) ≠ M.zero",
			"x ∈ algebraic_elements(M, k)",
			"polynomial_eval(a, x) ≠ M.zero",
		},
		Conclusion: "∃ev:(A → A). ev ∈ geometric_evaluation_points(M, k, «C») ∧ ev(t) = x",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "F", Text: "minimal_polynomial(M, «K», z)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
			{Name: "target", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
			{Name: "fibre", Text: "λX:set(A). geometric_fibre(M, k, X, t, x)"},
			{Name: "restriction", Text: "λev:(A → A). λy:A. COND(y ∈ «U», ev(y), M.zero)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		t, z, x *Expr[A],
		a *Arrow[Nat, A],
		closed, subk, tIn, zIn, transcendental, algebraic, fOver, aOver, nonzero, xIn, xGood Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldM := arg.TermAs[FieldOps[A]]("M")
		carrier := arg.TermAs[Set[A]]("M.carrier")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		onK := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), k)")
		target := arg.TermAs[module_record.RingOps[A]]("«target»")
		identity := arg.TermAs[Fun[A, A]]("λy:A. y")
		K, B, U, C :=
			arg.TermAs[Set[A]]("«K»"),
			arg.TermAs[Set[A]]("«B»"),
			arg.TermAs[Set[A]]("«U»"),
			arg.TermAs[Set[A]]("«C»")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		F := arg.TermAs[Fun[Nat, A]]("«F»")
		tm, zm := arg.MemberOf[on.M](t, tIn), arg.MemberOf[on.M](z, zIn)
		mSubfield := arg.Have(
			"M is a subfield of itself",
			"subfield(M, M.carrier)",
			By(field.CarrierSubfield.Read(M)))
		kInM := arg.Have(
			"k lies in M",
			"k ⊆ M.carrier",
			By(subk, field.SubfieldSubset.At(fieldM, k)))
		facts := arg.Conjuncts(
			GroupPremises(
				subk, mSubfield, kInM, tIn, zIn, aOver, nonzero, ChartFacts.Read(M).At(k, carrier, t, z, a)),
			"k[t] is a subring",
			"holding k",
			"and t",
			"and u",
			"k[t][z] is a subring",
			"holding k[t]",
			"and z",
			"C is a subring",
			"holding k[t][z]",
			"inside M",
			"with the inverse of u",
			"inverting u again adds nothing")
		subB, kInB, tInB, subU, bInU := facts[0], facts[1], facts[2], facts[4], facts[5]
		kInU := arg.Have(
			"k lies in k[t][z]",
			"k ⊆ «U»",
			BySets(kInB, bInU))
		tInU := arg.Have(
			"t lies in k[t][z]",
			"t ∈ «U»",
			BySets(tInB, bInU))
		closureData := arg.Conjuncts(
			GroupPremises(subk, algebraic_element.AlgebraicElementsSubfield.Read(M).AsFact().At(k)),
			"the algebraic elements are a subfield",
			"holding k")
		subClosure := arg.Have(
			"they are a subring",
			"subring(field_ring(M), algebraic_elements(M, k))",
			By(closureData[0], field.SubfieldSubring.Read(M).At(closure)))
		subkRing := arg.Have(
			"k is a subring",
			"subring(field_ring(M), k)",
			By(subk, field.SubfieldSubring.Read(M).At(k)))
		inclusion := arg.Have(
			"the inclusion of k into the algebraic elements is a ring map",
			"ring_homomorphism(restrict_ring(field_ring(M), k), «target», λy:A. y)",
			By(
				subkRing,
				ring_homomorphism.SubringInclusionHom.Read(ring).At(k),
				subClosure,
				arg.Have(
					"whose values are algebraic",
					"∀y:A. y ∈ k ⇒ y ∈ algebraic_elements(M, k)",
					BySets(closureData[1])),
				ring_homomorphism.RingHomCorestrict.At(onK, R, identity, closure)))
		e, overB := arg.ObtainAs[Fun[A, A]](
			"t being transcendental, k[t] has a ring map fixing k and sending t to x",
			"∃e:(A → A). "+
				"    ring_homomorphism(restrict_ring(field_ring(M), «B»), «target», e) ∧ "+
				"    (∀c:A. c ∈ k ⇒ e(c) = c) ∧ "+
				"    e(t) = x",
			By(
				subkRing,
				tIn,
				transcendental,
				inclusion,
				xIn,
				algebraic_element.TranscendentalLift.Read(M).AsFact().At(target, k, identity, t, x)))
		eParts := arg.Conjuncts(
			overB,
			"e is a ring map on k[t]",
			"e fixes k",
			"e sends t to x")
		adjoined := arg.Conjuncts(
			GroupPremises(subk, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)),
			"k(t) is a subfield",
			"holding k",
			"and t")
		subK := adjoined[0]
		bInK := arg.Have(
			"k[t] lies in k(t)",
			"«B» ⊆ «K»",
			By(subk, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		spec := arg.Conjuncts(
			GroupPremises(adjoined[0], algebraic, algebraic_element.MinimalPolynomialSpec.Read(M).At(K, zm)),
			"F is over k(t)",
			"F is monic",
			"F vanishes at z",
			"F is of least degree")
		least := arg.Have(
			"F is of least degree over k[t]",
			Statement{
				Binders: "∀q:(num → A).",
				Hypotheses: []string{
					"polynomial_over(«B», q)",
					"q ≠ vec_zero",
					"polynomial_eval(q, z) = M.zero",
				},
				Conclusion: "polynomial_degree(«F») ≤ polynomial_degree(q)",
			},
			Derive(func(b *Argument) {
				q := b.FixAs[Fun[Nat, A]]("q")
				given := b.Conjuncts(
					b.Assume(),
					"q is over k[t]",
					"q is not zero",
					"q vanishes at z")
				b.Show(
					"a polynomial over k[t] is one over k(t)",
					By(
						given[0],
						given[1],
						given[2],
						bInK,
						polynomial.PolynomialOverMono.At(arg.TermAs[A]("M.zero"), B, K, q),
						spec[3].At(q)))
			}))
		positive := arg.Have(
			"F has positive degree",
			"0 < polynomial_degree(«F»)",
			By(subK, algebraic, algebraic_element.MinimalPolynomialPositive.Read(M).At(K, zm)))
		_, overU := arg.ObtainAs[Fun[A, A]](
			"e extends to a point of k[t][z]",
			"∃ψ:(A → A). ψ ∈ geometric_evaluation_points(M, k, «U») ∧ ∀y:A. y ∈ «B» ⇒ ψ(y) = e(y)",
			By(
				closed,
				subk,
				subB,
				kInB,
				zIn,
				fOver,
				spec[1],
				positive,
				spec[2],
				least,
				eParts[0],
				eParts[1],
				PointExtendsAtRoot.Read(M).AsFact().At(k, B, e, F, z)))
		ψParts := arg.Conjuncts(
			overU,
			"ψ is a point of k[t][z]",
			"ψ extends e")
		onFibre := arg.Have(
			"ψ lies over x",
			"ψ ∈ «fibre»(«U»)",
			BySets(
				ψParts[0],
				arg.Have(
					"ψ sends t to x",
					"ψ(t) = x",
					By(Normalized, tInB, eParts[2], ψParts[1].At(t))),
				galois_good_open.GeometricFibreDef.At(fieldM, k, U, t, x)))
		away := arg.Conjuncts(
			GroupPremises(
				subU,
				kInU,
				tInU,
				aOver,
				nonzero,
				xIn,
				subk,
				xGood,
				galois_good_open.FibreAway.Read(M).At(k, U, t, x, a)),
			"restriction is injective on the fibre of C",
			"and onto the fibre of k[t][z]")
		ev, onC := arg.ObtainAs[Fun[A, A]](
			"ψ is the restriction of a point ev of C over x",
			"∃ev:(A → A). ev ∈ «fibre»(«C») ∧ ψ = «restriction»(ev)",
			BySets(
				arg.Have(
					"ψ lies in the image of the fibre of C",
					"ψ ∈ image(«restriction», «fibre»(«C»))",
					away[1].Rw(),
					By(onFibre))))
		evParts := arg.Conjuncts(
			onC,
			"ev lies on the fibre of C",
			"ψ is its restriction")
		arg.Take(ev)
		arg.Show(
			"ev is the point",
			BySets(evParts[0], galois_good_open.GeometricFibreDef.At(fieldM, k, C, t, x)))
	}),
})}

// PointSeparatesRoots — a point of a subring C of M keeps apart the roots in C of a
// nonzero polynomial F over C when the derivative of F is a unit of C at every root
// of F in C.
var PointSeparatesRoots = pointSeparatesRootsThm{family.Add(registry.ProofEntry{
	Name: "PointSeparatesRoots",
	Key:  "prop_ad76947a30a578ac",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k C Y:set(A). ∀F:(num → A). ∀ev:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subring(field_ring(M), C)",
			"polynomial_over(C, F)",
			"F ≠ vec_zero",
			"Y ⊆ C",
			"∀r:A. r ∈ Y ⇒ polynomial_eval(F, r) = M.zero",
			"∀r:A. " +
				"    r ∈ C ∧ polynomial_eval(F, r) = M.zero ⇒ " +
				"    ring_unit(restrict_ring(field_ring(M), C), polynomial_eval(polynomial_derivative(F), r))",
			"ev ∈ geometric_evaluation_points(M, k, C)",
		},
		Conclusion: "injective_on(Y, ev)",
		Abbrev: Abbrev{
			{Name: "target", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, C, Y *Expr[Set[A]],
		F *Arrow[Nat, A],
		ev *Arrow[A, A],
		subk, subC, over, nonzero, inside, roots, units, evIn Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		target := arg.TermAs[module_record.RingOps[A]]("«target»")
		evMap := arg.Have(
			"ev is a ring map on C",
			"ring_homomorphism(restrict_ring(field_ring(M), C), «target», ev)",
			By(evIn, galois_good_open.GeometricPointMember.At(fieldM, k, C, ev)))
		arg.Show(
			"two distinct roots keep distinct values",
			Unfold(functions.InjectiveOnDef),
			Derive(func(b *Argument) {
				r := b.FixAs[A]("r")
				s := b.FixAs[A]("s")
				given := b.Conjuncts(
					b.Assume(),
					"r lies in Y",
					"s lies in Y",
					"ev agrees at r and s")
				distinct := b.SupposeNot()
				rIn := b.Have(
					"r lies in C",
					"r ∈ C",
					BySets(given[0], inside))
				sIn := b.Have(
					"s lies in C",
					"s ∈ C",
					BySets(given[1], inside))
				rRoot := b.Have(
					"r is a root of F",
					"polynomial_eval(F, r) = M.zero",
					By(given[0], roots.At(r)))
				unitAt := b.Conjuncts(
					b.Simplified(GroupPremises(rIn, rRoot, units.At(r)), Fwd(ring_ideal.RingUnitDef)),
					"F′(r) lies in C",
					"with an inverse in C")
				v, unit := b.UnpackAs[A](unitAt[1], "v")
				parts := b.Conjuncts(
					unit,
					"v lies in C",
					"it inverts F′ at r")
				b.Show(
					"the simple roots r and s are kept apart",
					By(
						subC,
						evMap,
						field.OneNotZeroOn.Read(M),
						over,
						nonzero,
						rIn,
						sIn,
						distinct,
						rRoot,
						roots.At(s),
						given[1],
						parts[0],
						parts[1],
						given[2],
						integral_element.HomomorphismSeparatesSimpleRoots.Read(M).At(target, C, ev, F, r, s, v)))
			}))
	}),
})}

// PointsOnOneOrbit — let H be a finite set of automorphisms of L over K, closed under
// inverses, keeping a subring C and holding the identity, and let p be monic over C of
// degree the size of the orbit Y of z under H, vanishing on Y. Let ev and ew be points
// of C that agree at t and on the coefficients of p, with ev injective on Y, points of C
// being determined at t and z. Then ew is a translate of ev by H: ew(z) is a root of the
// image of p, so it is the value of ev at a point s(z) of the orbit, and the translate
// of ev by the inverse of s agrees with ew at t and z.
var PointsOnOneOrbit = pointsOnOneOrbitThm{family.Add(registry.ProofEntry{
	Name: "PointsOnOneOrbit",
	Key:  "prop_1a8ba4d2723bf61a",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀k K L C:set(A). " +
			"∀H:set(permutation(A)). " +
			"∀t z:A. " +
			"∀p:(num → A). " +
			"∀ev ew:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, L)",
			"k ⊆ K",
			"subring(field_ring(M), C)",
			"C ⊆ L",
			"k ⊆ C",
			"t ∈ K",
			"t ∈ C",
			"z ∈ C",
			"subgroup(galois_group(M, K, L), H)",
			"∀s:permutation(A). ∀y:A. s ∈ H ∧ y ∈ C ⇒ permutation_map(s, y) ∈ C",
			"finite(H)",
			"polynomial_over(C, p)",
			"polynomial_monic(p)",
			"polynomial_degree(p) = card(«Y»)",
			"∀r:A. r ∈ «Y» ⇒ polynomial_eval(p, r) = M.zero",
			"∀f g:(A → A). " +
				"    f ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    g ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    f(t) = g(t) ∧ " +
				"    f(z) = g(z) ⇒ " +
				"    f = g",
			"ev ∈ geometric_evaluation_points(M, k, C)",
			"ew ∈ geometric_evaluation_points(M, k, C)",
			"injective_on(«Y», ev)",
			"ev(t) = ew(t)",
			"∀i:num. ev(p(i)) = ew(p(i))",
		},
		Conclusion: "∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), C, s, ev) = ew",
		Abbrev: Abbrev{
			{Name: "Y", Text: "image(λs:permutation(A). permutation_map(s, z), H)"},
			{Name: "chart", Text: "restrict_ring(field_ring(M), C)"},
			{Name: "target", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, K, L, C *Expr[Set[A]],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		t, z *Expr[A],
		p *Arrow[Nat, A],
		ev, ew *Arrow[A, A],
		subk, subL, kInK, subC, cInL, kInC, tInK, tInC, zInC, subgroup, keeps, finiteH, pOver, pMonic, pDegree, pVanishes, determined, evIn, ewIn, injective, atT, coefficients Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		closures := arg.Conjuncts(
			arg.Unfolded(subgroup, group.SubgroupDef),
			"H consists of automorphisms",
			"holding the identity",
			"products",
			"and inverses")
		hInG, identity, inverses := closures[0], closures[1], closures[3]
		chart := arg.TermAs[module_record.RingOps[A]]("«chart»")
		target := arg.TermAs[module_record.RingOps[A]]("«target»")
		Y := arg.TermAs[Set[A]]("«Y»")
		value := arg.TermAs[A]("ew(z)")
		orbitMap := arg.TermAs[Fun[symmetric_group.Permutation[A], A]](
			"λs:permutation(A). permutation_map(s, z)")
		closure := arg.TermAs[Set[A]]("algebraic_elements(M, k)")
		algebraic := arg.Have(
			"the algebraic elements are a subring of M",
			"subring(field_ring(M), algebraic_elements(M, k))",
			By(
				subk,
				algebraic_element.AlgebraicElementsSubfield.Read(M).AsFact().At(k),
				field.SubfieldSubring.Read(M).At(closure)))
		evMap := arg.Have(
			"ev is a ring map on C",
			"ring_homomorphism(«chart», «target», ev)",
			By(evIn, galois_good_open.GeometricPointMember.At(fieldM, k, C, ev)))
		ewMap := arg.Have(
			"so is ew",
			"ring_homomorphism(«chart», «target», ew)",
			By(ewIn, galois_good_open.GeometricPointMember.At(fieldM, k, C, ew)))
		finiteY := arg.Have(
			"the orbit is finite",
			"finite(«Y»)",
			By(finiteH, finite_set.FiniteImage.At(orbitMap, H)))
		inside := arg.Have(
			"the orbit lies in C",
			"«Y» ⊆ C",
			BySets(zInC, keeps))
		zInY := arg.Have(
			"z lies on its orbit",
			"z ∈ «Y»",
			BySets(identity, symmetric_group.MapIdentity.At(z)))
		root := arg.Have(
			"so p vanishes at z",
			"polynomial_eval(p, z) = M.zero",
			By(zInY, pVanishes.At(z)))
		along := arg.Have(
			"ew moves the value of p at z to the value of the moved polynomial at ew(z)",
			"ew(polynomial_eval(p, z)) = polynomial_eval(λi:num. ew(p(i)), ew(z))",
			By(ewMap, pOver, zInC, polynomial_evaluation.EvalAlongHomomorphism.At(chart, target, ew, p, z)))
		moved := arg.Have(
			"the images of p along ev and ew are one",
			"(λi:num. ev(p(i))) = (λi:num. ew(p(i)))",
			Derive(func(b *Argument) {
				b.Do(Funext())
				i := b.FixAs[Nat]("i")
				b.Show(
					"ev and ew agree on the coefficients of p",
					By(coefficients.At(i)))
			}))
		wRoot := arg.Have(
			"so ew(z) is a root of the image of p along ev",
			"polynomial_eval(λi:num. ev(p(i)), ew(z)) = M.zero",
			moved.Rw(),
			along.RwRev(),
			root.Rw(),
			By(ring_homomorphism.MapZero.Read(evMap), ring_homomorphism.MapZero.Read(ewMap)))
		wIn := arg.Have(
			"ew(z) is algebraic",
			"ew(z) ∈ «target».carrier",
			By(zInC, ring_homomorphism.MapIn.Read(ewMap).AsFact().At(z)))
		_, found := arg.ObtainAs[A](
			"ew(z) is the value of ev at a point r of the orbit",
			"∃r:A. r ∈ «Y» ∧ ev(r) = ew(z)",
			By(
				algebraic,
				integral_domain.SubringOfFieldDomain.Read(M).At(closure),
				evMap,
				pOver,
				pMonic,
				finiteY,
				inside,
				pDegree,
				pVanishes,
				injective,
				wIn,
				wRoot,
				integral_element.RootsOfImagePolynomial.At(target, chart, Y, ev, p, value)))
		parts := arg.Conjuncts(
			found,
			"r lies on the orbit",
			"ev sends r to ew(z)")
		s, onOrbit := arg.ObtainAs[symmetric_group.Permutation[A]](
			"r is s(z) for some s of H",
			"∃s:permutation(A). s ∈ H ∧ r = permutation_map(s, z)",
			BySets(parts[0]))
		sParts := arg.Conjuncts(
			onOrbit,
			"s lies in H",
			"r is s(z)")
		sInv := arg.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)")
		sInvInv := arg.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(permutation_inverse(s))")
		image := arg.TermAs[A]("permutation_map(s, z)")
		sInvIn := arg.Have(
			"the inverse of s lies in H",
			"permutation_inverse(s) ∈ H",
			By(sParts[0], inverses.At(s)))
		sInvInvIn := arg.Have(
			"and so does its inverse",
			"permutation_inverse(permutation_inverse(s)) ∈ H",
			By(sInvIn, inverses.At(sInv)))
		sInvInvAuto := arg.Have(
			"which is an automorphism",
			"permutation_inverse(permutation_inverse(s)) ∈ field_automorphisms(M, K, L)",
			BySets(sInvInvIn, hInG))
		keepsUndo := arg.Have(
			"which keeps C",
			"∀y:A. y ∈ C ⇒ permutation_map(permutation_inverse(permutation_inverse(s)), y) ∈ C",
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				b.Show(
					"H keeps C",
					By(sInvInvIn, b.Assume(), keeps.At(sInvInv, y)))
			}))
		translated := arg.Conjuncts(
			arg.Have(
				"the translate of ev by the inverse of s is a point of C, with the value of ev at t",
				"evaluation_action(field_ring(M), C, permutation_inverse(s), ev) ∈ "+
					"geometric_evaluation_points(M, k, C) ∧ "+
					"evaluation_action(field_ring(M), C, permutation_inverse(s), ev, t) = ev(t)",
				By(
					subL,
					kInK,
					subC,
					cInL,
					kInC,
					tInK,
					tInC,
					sInvInvAuto,
					keepsUndo,
					evIn,
					galois_good_open.EvaluationActionKeepsFibre.Read(M).At(k, K, L, C, t, sInv, ev))),
			"the translate is a point of C",
			"with the value of ev at t")
		sInvInvZ := arg.Have(
			"the inverse of the inverse of s sends z to s(z)",
			"permutation_map(permutation_inverse(permutation_inverse(s)), z) = permutation_map(s, z)",
			By(Normalized, symmetric_group.MapInverse.At(sInv, image), symmetric_group.MapInverse.At(s, z)))
		atZ := arg.Have(
			"at z the translate agrees with ew",
			"evaluation_action(field_ring(M), C, permutation_inverse(s), ev, z) = ew(z)",
			Simp(Fwd(galois_good_open.EvaluationActionDef)),
			sInvInvZ.Rw(),
			sParts[1].RwRev(),
			By(zInC, parts[1]))
		arg.Take(sInv)
		arg.Show(
			"so the translate is ew",
			By(
				sInvIn,
				translated[0],
				ewIn,
				arg.Have(
					"at t it agrees with ew",
					"evaluation_action(field_ring(M), C, permutation_inverse(s), ev, t) = ew(t)",
					By(translated[1], atT)),
				atZ,
				determined.At(
					arg.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), C, permutation_inverse(s), ev)"), ew)))
	}),
})}

// InvariantChartGenerates — the invariants D of the chart C under automorphisms over
// k(t) hold k, t and the inverse of u, all fixed, and C is D[z]: D[z] lies in C, and it
// holds k[t][z] and the inverse of u, so all of C.
var InvariantChartGenerates = invariantChartGeneratesThm{family.Add(registry.ProofEntry{
	Name: "InvariantChartGenerates",
	Key:  "prop_c494a8c1693afd4e",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t z:A. ∀a:(num → A). ∀H:set(permutation(A)).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, L)",
			"k ⊆ L",
			"t ∈ L",
			"z ∈ L",
			"polynomial_over(k, a)",
			"polynomial_eval(a, t) ≠ M.zero",
			"H ⊆ field_automorphisms(M, «K», L)",
		},
		Conclusion: "subring(field_ring(M), «D») ∧ " +
			"k ⊆ «D» ∧ " +
			"t ∈ «D» ∧ " +
			"«D» ⊆ «C» ∧ " +
			"polynomial_image(field_ring(M), «D», z) = «C»",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
			{Name: "D", Text: "invariant_chart(«C», H)"},
			{Name: "I", Text: "polynomial_image(field_ring(M), «D», z)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t, z *Expr[A],
		a *Arrow[Nat, A],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		subk, subL, kInL, tIn, zIn, aOver, nonzero, hInG Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldM := arg.TermAs[FieldOps[A]]("M")
		K, B, U, C :=
			arg.TermAs[Set[A]]("«K»"),
			arg.TermAs[Set[A]]("«B»"),
			arg.TermAs[Set[A]]("«U»"),
			arg.TermAs[Set[A]]("«C»")
		D, I := arg.TermAs[Set[A]]("«D»"), arg.TermAs[Set[A]]("«I»")
		u := arg.TermAs[A]("polynomial_eval(a, t)")
		lField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subL, field.SubfieldSubset.At(fieldM, L)))
		tField := arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(tIn, lField))
		zField := arg.Have(
			"z lies in M",
			"z ∈ M.carrier",
			BySets(zIn, lField))
		tm, zm := arg.MemberOf[on.M](t, tField), arg.MemberOf[on.M](z, zField)
		facts := arg.Conjuncts(
			GroupPremises(subk, subL, kInL, tIn, zIn, aOver, nonzero, ChartFacts.Read(M).At(k, L, t, z, a)),
			"k[t] is a subring",
			"holding k",
			"and t",
			"and u",
			"k[t][z] is a subring",
			"holding k[t]",
			"and z",
			"C is a subring",
			"holding k[t][z]",
			"inside L",
			"with the inverse of u",
			"inverting u again adds nothing")
		kInB, tInB, uInB, bInU, zInU := facts[1], facts[2], facts[3], facts[5], facts[6]
		subC, uInC, cInL, inverseInC := facts[7], facts[8], facts[9], facts[10]
		adjoined := arg.Conjuncts(
			GroupPremises(subk, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)),
			"k(t) is a subfield",
			"holding k",
			"and t")
		subK, kInK, tInK := adjoined[0], adjoined[1], adjoined[2]
		bInK := arg.Have(
			"k[t] lies in k(t)",
			"«B» ⊆ «K»",
			By(subk, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
		invariants := arg.Conjuncts(
			GroupPremises(subL, subC, cInL, hInG, galois_good_open.InvariantChartFacts.Read(M).At(K, L, C, H)),
			"D is a subring",
			"inside C",
			"holding what C shares with k(t)")
		subD, dInC, shared := invariants[0], invariants[1], invariants[2]
		bInC := arg.Have(
			"k[t] lies in C",
			"«B» ⊆ «C»",
			BySets(bInU, uInC))
		kInD := arg.Have(
			"k lies in D",
			"k ⊆ «D»",
			BySets(kInB, bInC, kInK, shared))
		tInD := arg.Have(
			"t lies in D",
			"t ∈ «D»",
			BySets(tInB, bInC, tInK, shared))
		ringD := arg.Have(
			"D is a ring",
			"comm_ring_on(restrict_ring(field_ring(M), «D»))",
			By(subD, comm_ring.SubringRingOn.Read(ring).At(D)))
		bInD := arg.Have(
			"so k[t] lies in D",
			"«B» ⊆ «D»",
			By(ringD, kInD, tInD, algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(k, D, t)))
		inverseInK := arg.Have(
			"the inverse of u lies in k(t)",
			"M.inv(polynomial_eval(a, t)) ∈ «K»",
			By(
				subK,
				arg.Have(
					"u lies in k(t)",
					"polynomial_eval(a, t) ∈ «K»",
					BySets(uInB, bInK)),
				field.SubfieldInv.At(fieldM, K, u)))
		inverseInD := arg.Have(
			"so it lies in D",
			"M.inv(polynomial_eval(a, t)) ∈ «D»",
			BySets(inverseInC, inverseInK, shared))
		image := arg.Conjuncts(
			GroupPremises(invariants[0], algebraic_element.PolynomialImageSubring.Read(M).At(D, zm)),
			"D[z] is a subring",
			"holding D",
			"and z")
		subI, dInI, zInI := image[0], image[1], image[2]
		ringI := arg.Have(
			"D[z] is a ring",
			"comm_ring_on(restrict_ring(field_ring(M), «I»))",
			By(subI, comm_ring.SubringRingOn.Read(ring).At(I)))
		uInI := arg.Have(
			"k[t][z] lies in D[z]",
			"«U» ⊆ «I»",
			By(
				ringI,
				arg.Have(
					"k[t] lies in D[z]",
					"«B» ⊆ «I»",
					BySets(bInD, dInI)),
				zInI,
				algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(B, I, z)))
		cInI := arg.Have(
			"so C lies in D[z], which holds the inverse of u",
			"«C» ⊆ «I»",
			By(
				subI,
				uInI,
				arg.Have(
					"u lies in M",
					"polynomial_eval(a, t) ∈ M.carrier",
					BySets(uInB, bInU, uInC, cInL, lField)),
				nonzero,
				arg.Have(
					"the inverse of u lies in D[z]",
					"M.inv(polynomial_eval(a, t)) ∈ «I»",
					BySets(inverseInD, dInI)),
				ring_away.RingAwayLeast.Read(M).AsFact().At(U, I, u)))
		iInC := arg.Have(
			"and D[z] lies in C",
			"«I» ⊆ «C»",
			By(
				subC,
				comm_ring.SubringRingOn.Read(ring).At(C),
				dInC,
				arg.Have(
					"z lies in C",
					"z ∈ «C»",
					BySets(zInU, uInC)),
				algebraic_element.PolynomialImageLeast.Read(M).AsFact().At(D, C, z)))
		arg.Show(
			"which are the claims",
			By(subD, kInD, tInD, dInC, iInC, cInI, set_order.SubsetAntisym.At(I, C)))
	}),
})}

// OrbitPolynomial — let H be a finite subgroup of the automorphisms of L keeping a
// subring C of L holding z. The monic polynomial of degree the size of the orbit Y of z
// that vanishes on Y has its coefficients in the invariants of C: each s of H is a ring
// map of C and moves Y onto Y, so it fixes that polynomial.
var OrbitPolynomial = orbitPolynomialThm{family.Add(registry.ProofEntry{
	Name: "OrbitPolynomial",
	Key:  "prop_95c82483fb276eed",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K L C:set(A). ∀H:set(permutation(A)). ∀z:A.",
		Hypotheses: []string{
			"subfield(M, L)",
			"subring(field_ring(M), C)",
			"C ⊆ L",
			"z ∈ C",
			"subgroup(galois_group(M, K, L), H)",
			"finite(H)",
			"∀s:permutation(A). ∀y:A. s ∈ H ∧ y ∈ C ⇒ permutation_map(s, y) ∈ C",
		},
		Conclusion: "∃g:(num → A). " +
			"    polynomial_over(invariant_chart(C, H), g) ∧ " +
			"    polynomial_monic(g) ∧ " +
			"    polynomial_degree(g) = card(«Y») ∧ " +
			"    ∀r:A. r ∈ «Y» ⇒ polynomial_eval(g, r) = M.zero",
		Abbrev: Abbrev{
			{Name: "Y", Text: "image(λs:permutation(A). permutation_map(s, z), H)"},
			{Name: "chart", Text: "restrict_ring(field_ring(M), C)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, L, C *Expr[Set[A]],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		z *Expr[A],
		subL, subC, cInL, zIn, subgroup, finiteH, keeps Fact,
	) {
		zero := arg.TermAs[A]("M.zero")
		Y := arg.TermAs[Set[A]]("«Y»")
		orbitMap := arg.TermAs[Fun[symmetric_group.Permutation[A], A]](
			"λs:permutation(A). permutation_map(s, z)")
		closed := arg.Conjuncts(
			arg.Unfolded(subgroup, group.SubgroupDef),
			"H consists of automorphisms",
			"holding the identity",
			"products",
			"and inverses")
		hInG, products, inverses := closed[0], closed[2], closed[3]
		domain := arg.Have(
			"C is a domain",
			"integral_domain_on(«chart»)",
			By(subC, integral_domain.SubringOfFieldDomain.Read(M).At(C)))
		finiteY := arg.Have(
			"the orbit is finite",
			"finite(«Y»)",
			By(finiteH, finite_set.FiniteImage.At(orbitMap, H)))
		inside := arg.Have(
			"the orbit lies in C",
			"«Y» ⊆ C",
			BySets(zIn, keeps))
		g, data := arg.ObtainAs[Fun[Nat, A]](
			"a monic polynomial g over C of degree card(Y) vanishes on Y",
			"∃g:(num → A). "+
				"    polynomial_over(C, g) ∧ "+
				"    polynomial_monic(g) ∧ "+
				"    polynomial_degree(g) = card(«Y») ∧ "+
				"    ∀r:A. r ∈ «Y» ⇒ polynomial_eval(g, r) = M.zero",
			By(finiteY, inside, polynomial_roots.MonicVanishingPolynomial.Read(domain).At(Y)))
		parts := arg.Conjuncts(
			data,
			"g is over C",
			"it is monic",
			"of degree card(Y)",
			"vanishing on Y")
		fixed := arg.Have(
			"each s of H fixes the coefficients of g",
			"∀s:permutation(A). ∀i:num. s ∈ H ⇒ permutation_map(s, g(i)) = g(i)",
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				b.FixAs[Nat]("i")
				sIn := b.Assume()
				inverse := b.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)")
				e := b.TermAs[Fun[A, A]]("permutation_map(s)")
				keepsS := b.Have(
					"s keeps C",
					"∀y:A. y ∈ C ⇒ permutation_map(s, y) ∈ C",
					Derive(func(c *Argument) {
						y := c.FixAs[A]("y")
						c.Show(
							"H keeps C",
							By(sIn, c.Assume(), keeps.At(s, y)))
					}))
				hom := b.Have(
					"s is a ring map of C",
					"ring_homomorphism(«chart», «chart», permutation_map(s))",
					By(
						subL,
						subC,
						cInL,
						b.Have(
							"s is an automorphism",
							"s ∈ field_automorphisms(M, K, L)",
							BySets(sIn, hInG)),
						keepsS,
						galois_good_open.AutomorphismOnStableRing.Read(M).At(K, L, C, s)))
				onto := b.Have(
					"s moves Y onto Y",
					"∀r:A. r ∈ «Y» ⇒ ∃y:A. y ∈ «Y» ∧ permutation_map(s, y) = r",
					Derive(func(c *Argument) {
						c.FixAs[A]("r")
						rIn := c.Assume()
						q, onOrbit := c.ObtainAs[symmetric_group.Permutation[A]](
							"r is q(z) for some q of H",
							"∃q:permutation(A). q ∈ H ∧ r = permutation_map(q, z)",
							BySets(rIn))
						qParts := c.Conjuncts(
							onOrbit,
							"q lies in H",
							"r is q(z)")
						moved := c.TermAs[A]("permutation_map(q, z)")
						product := c.Have(
							"the product of the inverse of s and q lies in H",
							"permutation_compose(permutation_inverse(s), q) ∈ H",
							By(sIn, qParts[0], inverses.At(s), products.At(inverse, q)))
						c.Take(c.TermAs[A]("permutation_map(permutation_inverse(s), r)"))
						c.Show(
							"the inverse of s moves r along the orbit, and s moves it back",
							qParts[1].Rw(),
							SplitConj(
								Case(
									"the product moves z there",
									BySets(product, symmetric_group.MapCompose.At(inverse, q, z))),
								Case(
									"s undoes its inverse",
									By(symmetric_group.MapInverseRight.At(s, moved)))))
					}))
				same := b.Have(
					"so s fixes g",
					"(λj:num. permutation_map(s, g(j))) = g",
					By(
						hom,
						finiteY,
						inside,
						onto,
						parts[0],
						parts[1],
						parts[2],
						parts[3],
						polynomial_roots.MonicVanishingFixed.Read(domain).At(Y, e, g)))
				b.Show(
					"read at i",
					By(Normalized, same))
			}))
		invariant := arg.Have(
			"so the coefficients of g lie in the invariants",
			"∀i:num. g(i) ∈ invariant_chart(C, H)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				inC := b.Have(
					"they lie in C",
					"g(i) ∈ C",
					By(parts[0], polynomial.PolynomialOverDef.At(zero, C, g)))
				b.Show(
					"and H fixes them",
					Simp(Fwd(galois_good_open.InvariantChartDef)),
					By(inC, fixed))
			}))
		arg.Take(g)
		arg.Show(
			"g is the polynomial",
			By(
				parts[1],
				parts[2],
				parts[3],
				arg.Have(
					"g is over the invariants",
					"polynomial_over(invariant_chart(C, H), g)",
					By(parts[0], invariant, polynomial.PolynomialOverDef))))
	}),
})}

// OrbitPolynomialLeast — a nonzero relation of z with coefficients in the invariants of
// C under H vanishes on the whole orbit of z, since each s of H fixes its coefficients,
// so its degree is at least the size of the orbit.
var OrbitPolynomialLeast = orbitPolynomialLeastThm{family.Add(registry.ProofEntry{
	Name: "OrbitPolynomialLeast",
	Key:  "prop_369c533068ae6fae",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K L C:set(A). ∀H:set(permutation(A)). ∀z:A. ∀q:(num → A).",
		Hypotheses: []string{
			"subfield(M, L)",
			"C ⊆ L",
			"z ∈ C",
			"H ⊆ field_automorphisms(M, K, L)",
			"polynomial_over(invariant_chart(C, H), q)",
			"q ≠ vec_zero",
			"polynomial_eval(q, z) = M.zero",
		},
		Conclusion: "card(«Y») ≤ polynomial_degree(q)",
		Abbrev: Abbrev{
			{Name: "Y", Text: "image(λs:permutation(A). permutation_map(s, z), H)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		K, L, C *Expr[Set[A]],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		z *Expr[A],
		q *Arrow[Nat, A],
		subL, cInL, zIn, hInG, qOver, nonzero, root Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		zero := arg.TermAs[A]("M.zero")
		D := arg.TermAs[Set[A]]("invariant_chart(C, H)")
		carrier := arg.TermAs[Set[A]]("M.carrier")
		Y, roots := arg.TermAs[Set[A]]("«Y»"), arg.TermAs[Set[A]]("polynomial_roots(M.carrier, q)")
		domain := integral_domain.FieldIntegralDomain.Read(M)
		dInL := arg.Have(
			"the invariants lie in L",
			"invariant_chart(C, H) ⊆ L",
			BySets(cInL, galois_good_open.InvariantChartDef.At(C, H)))
		zL := arg.Have(
			"z lies in L",
			"z ∈ L",
			BySets(zIn, cInL))
		lField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subL, field.SubfieldSubset.At(fieldM, L)))
		qL := arg.Have(
			"q is a polynomial over L",
			"polynomial_over(L, q)",
			By(qOver, dInL, polynomial.PolynomialOverMono.At(zero, D, L, q)))
		qOverM := arg.Have(
			"so over M",
			"polynomial_over(M.carrier, q)",
			By(qL, lField, polynomial.PolynomialOverMono.At(zero, L, carrier, q)))
		bound := arg.Conjuncts(
			GroupPremises(qOverM, nonzero, polynomial_roots.RootBound.Read(domain).At(q)),
			"q has finitely many roots",
			"at most its degree")
		inRoots := arg.Have(
			"the orbit of z lies among the roots of q",
			"«Y» ⊆ polynomial_roots(M.carrier, q)",
			Derive(func(b *Argument) {
				pointwise := b.Have(
					"each s of H moves z to a root",
					"∀s:permutation(A). s ∈ H ⇒ permutation_map(s, z) ∈ polynomial_roots(M.carrier, q)",
					Derive(func(c *Argument) {
						s := c.FixAs[symmetric_group.Permutation[A]]("s")
						sIn := c.Assume()
						auto := c.Have(
							"s is an automorphism",
							"s ∈ field_automorphisms(M, K, L)",
							BySets(sIn, hInG))
						hom := c.Have(
							"s is a ring map of L",
							"ring_homomorphism(field_ring(restrict_field(M, L)), "+
								"    field_ring(restrict_field(M, L)), "+
								"    permutation_map(s))",
							By(subL, auto, field_automorphism.AutomorphismRingHomomorphism.Read(M).AsFact().At(K, L, s)))
						fixing := c.Have(
							"s fixes the invariants, so it is an automorphism over them",
							"s ∈ field_automorphisms(M, invariant_chart(C, H), L)",
							BySets(
								auto,
								sIn,
								galois_good_open.InvariantChartDef.At(C, H),
								field_automorphism.FieldAutomorphismsDef.At(fieldM, K, L),
								field_automorphism.FieldAutomorphismsDef.At(fieldM, D, L)))
						value := c.Have(
							"so it carries the root z of q to a root",
							"polynomial_eval(q, permutation_map(s, z)) = M.zero",
							By(
								subL,
								dInL,
								fixing,
								qOver,
								zL,
								root,
								field_automorphism.AutomorphismPermutesRoots.Read(M).At(D, L, q, s, z)))
						c.Show(
							"and s(z) lies in M",
							Simp(Fwd(polynomial_roots.PolynomialRootsDef)),
							By(
								value,
								c.Have(
									"s(z) lies in M",
									"permutation_map(s, z) ∈ M.carrier",
									BySets(zL, lField, ring_homomorphism.MapIn.Read(hom).AsFact().At(z)))))
					}))
				b.Show(
					"so the orbit lies among the roots",
					BySets(pointwise))
			}))
		arg.Show(
			"and q has at most its degree of roots",
			ByArith(
				bound[1],
				arg.Have(
					"the orbit has at most as many points as there are roots",
					"card(«Y») ≤ card(polynomial_roots(M.carrier, q))",
					By(bound[0], inRoots, cardinality.CardSubset.At(Y, roots)))))
	}),
})}

// ChartFibreTorsor — let the automorphisms G of L over K keep a subring C, each be
// determined by its value at z, and let F, monic over C of degree card(G), vanish on the
// orbit Y of z. If points of C are determined at t and z, are injective on Y, and agree
// on the coefficients of F along a fibre over x, then G acts freely and transitively on
// that fibre when it has a point e, and the fibre has card(G) points. Two translates of
// a point that agree at z come from one automorphism, and the fibre is the translates
// of e.
var ChartFibreTorsor = chartFibreTorsorThm{family.Add(registry.ProofEntry{
	Name: "ChartFibreTorsor",
	Key:  "prop_964250b4b52b1b38",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K L C:set(A). ∀t z x:A. ∀F:(num → A). ∀e:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, L)",
			"k ⊆ K",
			"subring(field_ring(M), C)",
			"C ⊆ L",
			"k ⊆ C",
			"t ∈ K",
			"t ∈ C",
			"z ∈ C",
			"finite(field_automorphisms(M, K, L))",
			"∀s:permutation(A). ∀y:A. s ∈ field_automorphisms(M, K, L) ∧ y ∈ C ⇒ permutation_map(s, y) ∈ C",
			"injective_on(field_automorphisms(M, K, L), λs:permutation(A). permutation_map(s, z))",
			"polynomial_over(C, F)",
			"polynomial_monic(F)",
			"polynomial_degree(F) = card(field_automorphisms(M, K, L))",
			"∀r:A. r ∈ «Y» ⇒ polynomial_eval(F, r) = M.zero",
			"∀f g:(A → A). " +
				"    f ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    g ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    f(t) = g(t) ∧ " +
				"    f(z) = g(z) ⇒ " +
				"    f = g",
			"∀ev:(A → A). ev ∈ geometric_evaluation_points(M, k, C) ⇒ injective_on(«Y», ev)",
			"∀ev ew:(A → A). ∀i:num. ev ∈ «fibre» ∧ ew ∈ «fibre» ⇒ ev(F(i)) = ew(F(i))",
			"e ∈ «fibre»",
		},
		Conclusion: "free_finite_action(galois_group(M, K, L), " +
			"    «fibre», " +
			"    evaluation_action(field_ring(M), C)) ∧ " +
			"card(«fibre») = card(field_automorphisms(M, K, L)) ∧ " +
			"∀ev ew:(A → A). " +
			"    ev ∈ «fibre» ∧ ew ∈ «fibre» ⇒ " +
			"    ∃s:permutation(A). " +
			"        s ∈ field_automorphisms(M, K, L) ∧ evaluation_action(field_ring(M), C, s, ev) = ew",
		Abbrev: Abbrev{
			{Name: "Y", Text: "image(λs:permutation(A). permutation_map(s, z), field_automorphisms(M, K, L))"},
			{Name: "fibre", Text: "geometric_fibre(M, k, C, t, x)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, K, L, C *Expr[Set[A]],
		t, z, x *Expr[A],
		F *Arrow[Nat, A],
		e *Arrow[A, A],
		subk, subL, kInK, subC, cInL, kInC, tInK, tInC, zIn, finiteG, keeps, injective, fOver, fMonic, fDegree, fRoots, determined, separated, coefficients, eIn Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		G := arg.TermAs[Set[symmetric_group.Permutation[A]]]("field_automorphisms(M, K, L)")
		Y := arg.TermAs[Set[A]]("«Y»")
		orbitMap := arg.TermAs[Fun[symmetric_group.Permutation[A], A]](
			"λs:permutation(A). permutation_map(s, z)")
		translates := arg.TermAs[Fun[symmetric_group.Permutation[A], Fun[A, A]]](
			"λs:permutation(A). evaluation_action(field_ring(M), C, s, e)")
		universe := arg.TermAs[group.GroupOps[symmetric_group.Permutation[A]]]("permutation_group")
		subgroupG := field_automorphism.AutomorphismsSubgroup.At(fieldM, K, L)
		identityIn := arg.Have(
			"the identity is an automorphism",
			"permutation_identity ∈ field_automorphisms(M, K, L)",
			By(M, subgroupG, group.SubgroupOne.At(universe, G)))
		wholeGroup := arg.Have(
			"the automorphisms are a group of permutations lying in "+
				"themselves, so the whole Galois group is a subgroup of itself",
			"subgroup(galois_group(M, K, L), field_automorphisms(M, K, L))",
			By(
				M,
				subgroupG,
				set_order.SubsetRefl.At(G),
				field_automorphism.GaloisGroupSubgroup.At(fieldM, K, L, G)))
		inverses := arg.Have(
			"the inverse of an automorphism is one",
			Statement{
				Binders:    "∀s:permutation(A).",
				Hypotheses: []string{"s ∈ field_automorphisms(M, K, L)"},
				Conclusion: "permutation_inverse(s) ∈ field_automorphisms(M, K, L)",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				b.Show(
					"the automorphisms are a subgroup",
					By(M, b.Assume(), subgroupG, group.SubgroupInv.At(universe, G, s)))
			}))
		keepsInverse := arg.Have(
			"inverses keep C too",
			"∀s:permutation(A). "+
				"    s ∈ field_automorphisms(M, K, L) ⇒ "+
				"    ∀y:A. y ∈ C ⇒ permutation_map(permutation_inverse(s), y) ∈ C",
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				sIn := b.Assume()
				y := b.FixAs[A]("y")
				b.Show(
					"the inverse is an automorphism",
					By(
						sIn,
						b.Assume(),
						inverses.At(s),
						keeps.At(b.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)"), y)))
			}))
		onOrbit := arg.Have(
			"inverses move z along the orbit",
			Statement{
				Binders:    "∀s:permutation(A).",
				Hypotheses: []string{"s ∈ field_automorphisms(M, K, L)"},
				Conclusion: "permutation_map(permutation_inverse(s), z) ∈ «Y»",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				b.Show(
					"the inverse is an automorphism",
					BySets(b.Assume(), inverses.At(s)))
			}))
		onFibre := arg.Have(
			"a map lies on the fibre when it is a geometric point of C over x",
			"∀ev:(A → A). ev ∈ «fibre» ⇔ ev ∈ geometric_evaluation_points(M, k, C) ∧ ev(t) = x",
			BySets(galois_good_open.GeometricFibreDef.At(fieldM, k, C, t, x)))
		moved := arg.Have(
			"an automorphism keeps the fibre",
			Statement{
				Binders:    "∀s:permutation(A). ∀ev:(A → A).",
				Hypotheses: []string{"s ∈ field_automorphisms(M, K, L)", "ev ∈ «fibre»"},
				Conclusion: "evaluation_action(field_ring(M), C, s, ev) ∈ «fibre»",
			},
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				ev := b.FixAs[Fun[A, A]]("ev")
				given := b.Conjuncts(
					b.Assume(),
					"s is an automorphism",
					"ev lies on the fibre")
				point := b.Conjuncts(
					b.Have(
						"ev is a point over x",
						"ev ∈ geometric_evaluation_points(M, k, C) ∧ ev(t) = x",
						By(onFibre.At(ev), given[1])),
					"ev is a point",
					"over x")
				translated := b.Conjuncts(
					b.Have(
						"the translate is a point with the value of ev at t",
						"evaluation_action(field_ring(M), C, s, ev) ∈ geometric_evaluation_points(M, k, C) ∧ "+
							"evaluation_action(field_ring(M), C, s, ev, t) = ev(t)",
						By(
							subL,
							kInK,
							subC,
							cInL,
							kInC,
							tInK,
							tInC,
							given[0],
							inverses.At(s),
							keepsInverse.At(s),
							point[0],
							galois_good_open.EvaluationActionKeepsFibre.Read(M).At(k, K, L, C, t, s, ev))),
					"the translate is a point",
					"with the value of ev at t")
				b.Show(
					"so it lies over x",
					By(
						onFibre.At(b.TermAs[Fun[A, A]]("evaluation_action(field_ring(M), C, s, ev)")),
						translated[0],
						translated[1],
						point[1]))
			}))
		degree := arg.Have(
			"F has the degree of the size of the orbit",
			"polynomial_degree(F) = card(«Y»)",
			fDegree.Rw(),
			By(injective, finiteG, cardinality.CardImageInj.At(orbitMap, G)))
		transitive := arg.Have(
			"any two points of the fibre differ by an automorphism",
			Statement{
				Binders:    "∀ev ew:(A → A).",
				Hypotheses: []string{"ev ∈ «fibre»", "ew ∈ «fibre»"},
				Conclusion: "∃s:permutation(A). " +
					"    s ∈ field_automorphisms(M, K, L) ∧ evaluation_action(field_ring(M), C, s, ev) = ew",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				ew := b.FixAs[Fun[A, A]]("ew")
				given := b.Conjuncts(
					b.Assume(),
					"ev lies on the fibre",
					"ew lies on the fibre")
				evPoint := b.Conjuncts(
					b.Have(
						"ev is a point over x",
						"ev ∈ geometric_evaluation_points(M, k, C) ∧ ev(t) = x",
						By(onFibre.At(ev), given[0])),
					"ev is a point",
					"over x")
				ewPoint := b.Conjuncts(
					b.Have(
						"ew is a point over x",
						"ew ∈ geometric_evaluation_points(M, k, C) ∧ ew(t) = x",
						By(onFibre.At(ew), given[1])),
					"ew is a point",
					"over x")
				b.Show(
					"the orbit of z under the whole group",
					By(
						subk,
						subL,
						kInK,
						subC,
						cInL,
						kInC,
						tInK,
						tInC,
						zIn,
						wholeGroup,
						keeps,
						finiteG,
						fOver,
						fMonic,
						degree,
						fRoots,
						determined,
						evPoint[0],
						ewPoint[0],
						separated.At(ev),
						b.Have(
							"ev and ew agree at t",
							"ev(t) = ew(t)",
							By(Normalized, evPoint[1], ewPoint[1])),
						b.Have(
							"and on the coefficients of F",
							"∀i:num. ev(F(i)) = ew(F(i))",
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]("i")
								c.Show(
									"along the fibre",
									By(given[0], given[1], coefficients.At(ev, ew, i)))
							})),
						PointsOnOneOrbit.Read(M).At(k, K, L, C, G, t, z, F, ev, ew)))
			}))
		atZ := arg.Have(
			"a translate reads the point at the inverse image of z",
			"∀s:permutation(A). ∀ev:(A → A). "+
				"    evaluation_action(field_ring(M), C, s, ev, z) = "+
				"    ev(permutation_map(permutation_inverse(s), z))",
			Derive(func(b *Argument) {
				b.FixAs[symmetric_group.Permutation[A]]("s")
				b.FixAs[Fun[A, A]]("ev")
				b.Show(
					"z lies in C",
					Simp(Fwd(galois_good_open.EvaluationActionDef)),
					By(zIn))
			}))
		cancels := arg.Have(
			"two automorphisms with one translate of a point are one",
			Statement{
				Binders: "∀p q:permutation(A). ∀ev:(A → A).",
				Hypotheses: []string{
					"p ∈ field_automorphisms(M, K, L)",
					"q ∈ field_automorphisms(M, K, L)",
					"ev ∈ geometric_evaluation_points(M, k, C)",
					"evaluation_action(field_ring(M), C, p, ev) = evaluation_action(field_ring(M), C, q, ev)",
				},
				Conclusion: "p = q",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[symmetric_group.Permutation[A]]("p")
				q := b.FixAs[symmetric_group.Permutation[A]]("q")
				ev := b.FixAs[Fun[A, A]]("ev")
				given := b.Conjuncts(
					b.Assume(),
					"p is an automorphism",
					"q is an automorphism",
					"ev is a point",
					"their translates are one")
				values := b.Have(
					"the point agrees at the inverse images of z",
					"ev(permutation_map(permutation_inverse(p), z)) = ev(permutation_map(permutation_inverse(q), z))",
					atZ.At(p, ev).RwRev(),
					atZ.At(q, ev).RwRev(),
					given[3].Rw(),
					Basic())
				sameImage := b.Have(
					"so the inverse images are one, the point being injective on the orbit",
					"permutation_map(permutation_inverse(p), z) = permutation_map(permutation_inverse(q), z)",
					By(
						given[0],
						given[1],
						given[2],
						values,
						separated.At(ev),
						onOrbit.At(p),
						onOrbit.At(q),
						functions.InjectiveOnDef.At(Y, ev)))
				sameInverse := b.Have(
					"so the inverses are one, an automorphism being read off at z",
					"permutation_inverse(p) = permutation_inverse(q)",
					By(
						given[0],
						given[1],
						sameImage,
						inverses.At(p),
						inverses.At(q),
						injective,
						functions.InjectiveOnDef.At(G, orbitMap)))
				agree := b.Have(
					"so p and q agree at each point",
					"∀y:A. permutation_map(p, y) = permutation_map(q, y)",
					Derive(func(c *Argument) {
						y := c.FixAs[A]("y")
						image := c.TermAs[A]("permutation_map(q, y)")
						c.Show(
							"p undoes the inverse of q",
							By(sameInverse, symmetric_group.MapInverseRight.At(p, image), symmetric_group.MapInverse.At(q, y)))
					}))
				b.Show(
					"permutations with the same values are equal",
					By(agree, symmetric_group.PermutationEq.At(p, q)))
			}))
		identity := arg.Have(
			"the identity moves no point of the fibre",
			"∀ev:(A → A). ev ∈ «fibre» ⇒ evaluation_action(field_ring(M), C, permutation_identity, ev) = ev",
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				evIn := b.Have(
					"ev is a point",
					"ev ∈ geometric_evaluation_points(M, k, C)",
					By(onFibre.At(ev), b.Assume()))
				b.Show(
					"a point vanishes off C",
					By(
						b.Have(
							"ev vanishes off C",
							"∀y:A. y ∉ C ⇒ ev(y) = M.zero",
							By(evIn, galois_good_open.GeometricPointMember.At(fieldM, k, C, ev))),
						galois_good_open.EvaluationActionIdentity.At(R, C, ev)))
			}))
		laws := arg.Have(
			"the group acts on the fibre, freely",
			Statement{
				Binders: "∀g h:permutation(A). ∀ev:(A → A).",
				Hypotheses: []string{
					"g ∈ field_automorphisms(M, K, L)",
					"h ∈ field_automorphisms(M, K, L)",
					"ev ∈ «fibre»",
				},
				Conclusion: "evaluation_action(field_ring(M), C, g, ev) ∈ «fibre» ∧ " +
					"evaluation_action(field_ring(M), C, permutation_compose(g, h), ev) = " +
					"evaluation_action(field_ring(M), C, g, evaluation_action(field_ring(M), C, h, ev)) ∧ " +
					"(evaluation_action(field_ring(M), C, g, ev) = ev ⇒ g = permutation_identity)",
			},
			Derive(func(b *Argument) {
				g := b.FixAs[symmetric_group.Permutation[A]]("g")
				h := b.FixAs[symmetric_group.Permutation[A]]("h")
				ev := b.FixAs[Fun[A, A]]("ev")
				given := b.Conjuncts(
					b.Assume(),
					"g is an automorphism",
					"h is an automorphism",
					"ev lies on the fibre")
				evIn := b.Have(
					"ev is a point",
					"ev ∈ geometric_evaluation_points(M, k, C)",
					By(onFibre.At(ev), given[2]))
				identityPermutation := b.TermAs[symmetric_group.Permutation[A]]("permutation_identity")
				b.Do(SplitConjAll(
					Case(
						"the action keeps the fibre",
						By(given[0], given[2], moved.At(g, ev))),
					Case(
						"it is multiplicative",
						By(given[0], keepsInverse.At(g), galois_good_open.EvaluationActionCompose.At(R, C, g, h, ev))),
					Case(
						"only the identity fixes a point",
						Derive(func(c *Argument) {
							fixed := c.Assume()
							c.Show(
								"g and the identity have one translate of ev",
								By(
									given[0],
									identityIn,
									evIn,
									fixed,
									identity.At(ev),
									given[2],
									cancels.At(g, identityPermutation, ev)))
						}))))
			}))
		fibreIs := arg.Have(
			"the fibre is the set of translates of e",
			"«fibre» = "+
				"image(λs:permutation(A). evaluation_action(field_ring(M), C, s, e), field_automorphisms(M, K, L))",
			Derive(func(b *Argument) {
				reached := b.Have(
					"each point of the fibre is a translate of e",
					Statement{
						Binders:    "∀ew:(A → A).",
						Hypotheses: []string{"ew ∈ «fibre»"},
						Conclusion: "∃s:permutation(A). " +
							"    s ∈ field_automorphisms(M, K, L) ∧ evaluation_action(field_ring(M), C, s, e) = ew",
					},
					Derive(func(c *Argument) {
						ew := c.FixAs[Fun[A, A]]("ew")
						c.Show(
							"e lies on the fibre",
							By(eIn, c.Assume(), transitive.At(e, ew)))
					}))
				translatesIn := b.Have(
					"and each translate of e lies on it",
					Statement{
						Binders:    "∀s:permutation(A).",
						Hypotheses: []string{"s ∈ field_automorphisms(M, K, L)"},
						Conclusion: "evaluation_action(field_ring(M), C, s, e) ∈ «fibre»",
					},
					Derive(func(c *Argument) {
						s := c.FixAs[symmetric_group.Permutation[A]]("s")
						c.Show(
							"the group keeps the fibre",
							By(eIn, c.Assume(), moved.At(s, e)))
					}))
				b.Show(
					"the two inclusions",
					BySets(reached, translatesIn))
			}))
		ePoint := arg.Have(
			"e is a point",
			"e ∈ geometric_evaluation_points(M, k, C)",
			By(onFibre.At(e), eIn))
		translatesInjective := arg.Have(
			"distinct automorphisms give distinct translates of e",
			"injective_on(field_automorphisms(M, K, L), "+
				"    λs:permutation(A). evaluation_action(field_ring(M), C, s, e))",
			Unfold(functions.InjectiveOnDef),
			Derive(func(b *Argument) {
				p := b.FixAs[symmetric_group.Permutation[A]]("p")
				q := b.FixAs[symmetric_group.Permutation[A]]("q")
				given := b.Conjuncts(
					b.Assume(),
					"p is an automorphism",
					"q is an automorphism",
					"their translates are one")
				b.Show(
					"translates determine the automorphism",
					By(given[0], given[1], ePoint, given[2], cancels.At(p, q, e)))
			}))
		size := arg.Have(
			"so the fibre has card(G) points",
			"card(«fibre») = card(field_automorphisms(M, K, L))",
			fibreIs.Rw(),
			By(translatesInjective, finiteG, cardinality.CardImageInj.At(translates, G)))
		finiteFibre := arg.Have(
			"and is finite",
			"finite(«fibre»)",
			fibreIs.Rw(),
			By(finiteG, finite_set.FiniteImage.At(translates, G)))
		free := arg.Have(
			"so the group acts freely on the finite fibre",
			"free_finite_action(galois_group(M, K, L), «fibre», evaluation_action(field_ring(M), C))",
			Unfold(twisted_counting.FreeFiniteActionDef),
			By(field_automorphism.GaloisGroupOn.Read(M).At(K, L), finiteG, finiteFibre, identity, laws))
		arg.Show(
			"which are the claims",
			By(free, size, transitive))
	}),
})}

// InvariantFibreImage — when C is D[z], for D the invariants of C under a finite
// subgroup H, the points of C over x restrict onto the points of D over x. A restriction
// is a point of D, and a point of D extends to D[z] along the polynomial of the orbit
// of z, monic over D and of least degree among the relations of z over D.
var InvariantFibreImage = invariantFibreImageThm{family.Add(registry.ProofEntry{
	Name: "InvariantFibreImage",
	Key:  "prop_4fcc4bf5b7d24523",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K L C:set(A). ∀H:set(permutation(A)). ∀t z x:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"subfield(M, L)",
			"subring(field_ring(M), C)",
			"C ⊆ L",
			"z ∈ C",
			"subring(field_ring(M), invariant_chart(C, H))",
			"k ⊆ invariant_chart(C, H)",
			"t ∈ invariant_chart(C, H)",
			"polynomial_image(field_ring(M), invariant_chart(C, H), z) = C",
			"subgroup(galois_group(M, K, L), H)",
			"finite(H)",
			"∀s:permutation(A). ∀y:A. s ∈ H ∧ y ∈ C ⇒ permutation_map(s, y) ∈ C",
		},
		Conclusion: "image(«restriction», «fibre») = «invariantFibre»",
		Abbrev: Abbrev{
			{Name: "Y", Text: "image(λs:permutation(A). permutation_map(s, z), H)"},
			{Name: "chart", Text: "restrict_ring(field_ring(M), C)"},
			{Name: "target", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
			{Name: "fibre", Text: "geometric_fibre(M, k, C, t, x)"},
			{Name: "invariantFibre", Text: "{ev:(A → A) | " +
				"    ev ∈ " +
				"    algebra_points(restrict_ring(field_ring(M), invariant_chart(C, H)), «target», k, λy:A. y) ∧ " +
				"    ev(t) = x}"},
			{Name: "restriction", Text: "λev:(A → A). λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, K, L, C *Expr[Set[A]],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		t, z, x *Expr[A],
		closed, subk, subL, subC, cInL, zIn, subD, kInD, tInD, generated, subgroup, finiteH, keeps Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		chart := arg.TermAs[module_record.RingOps[A]]("«chart»")
		target := arg.TermAs[module_record.RingOps[A]]("«target»")
		onD := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), invariant_chart(C, H))")
		D := arg.TermAs[Set[A]]("invariant_chart(C, H)")
		Y := arg.TermAs[Set[A]]("«Y»")
		identity := arg.TermAs[Fun[A, A]]("λy:A. y")
		orbitMap := arg.TermAs[Fun[symmetric_group.Permutation[A], A]](
			"λs:permutation(A). permutation_map(s, z)")
		closures := arg.Conjuncts(
			arg.Unfolded(subgroup, group.SubgroupDef),
			"H consists of automorphisms",
			"holding the identity",
			"products",
			"and inverses")
		hInG, identityIn := closures[0], closures[1]
		dInC := arg.Have(
			"the invariants lie in C",
			"invariant_chart(C, H) ⊆ C",
			BySets(galois_good_open.InvariantChartDef.At(C, H)))
		onFibre := arg.Have(
			"a map lies on the fibre when it is a geometric point of C over x",
			"∀ev:(A → A). ev ∈ «fibre» ⇔ ev ∈ geometric_evaluation_points(M, k, C) ∧ ev(t) = x",
			BySets(galois_good_open.GeometricFibreDef.At(fieldM, k, C, t, x)))
		forward := arg.Have(
			"a point of C over x restricts to a point of D over x",
			Statement{
				Binders:    "∀ev:(A → A).",
				Hypotheses: []string{"ev ∈ «fibre»"},
				Conclusion: "(λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero)) ∈ «invariantFibre»",
			},
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				point := b.Conjuncts(
					b.Have(
						"ev is a point over x",
						"ev ∈ algebra_points(«chart», «target», k, λy:A. y) ∧ ev(t) = x",
						BySets(b.Assume(), onFibre.At(ev), galois_good_open.GeometricEvaluationPointsDef.At(fieldM, k, C))),
					"ev is a point",
					"over x")
				restricted := b.Have(
					"it restricts to a point of D",
					"(λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero)) ∈ "+
						"algebra_points(restrict_ring(«chart», invariant_chart(C, H)), «target», k, λy:A. y)",
					By(
						b.Have(
							"D is a subring of C",
							"subring(«chart», invariant_chart(C, H))",
							By(subD, dInC, comm_ring.SubringRestrict.At(R, D, C))),
						kInD,
						point[0],
						galois_good_open.PointRestricts.At(chart, target, D, k, identity, ev)))
				b.Show(
					"with the value of ev at t",
					BySets(
						b.Have(
							"the restriction is a point of D under the operations of M",
							"(λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero)) ∈ "+
								"algebra_points(restrict_ring(field_ring(M), invariant_chart(C, H)), «target», k, λy:A. y)",
							By(restricted, module_record.RestrictRingTwice.At(R, C, D))),
						tInD,
						point[1]))
			}))
		backward := arg.Have(
			"a point of D over x is the restriction of a point of C over x",
			Statement{
				Binders:    "∀ψ:(A → A).",
				Hypotheses: []string{"ψ ∈ «invariantFibre»"},
				Conclusion: "∃ev:(A → A). " +
					"    ev ∈ «fibre» ∧ (λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero)) = ψ",
			},
			Derive(func(b *Argument) {
				ψ := b.FixAs[Fun[A, A]]("ψ")
				point := b.Conjuncts(
					b.Have(
						"ψ is a point over x",
						"ψ ∈ algebra_points(restrict_ring(field_ring(M), invariant_chart(C, H)), «target», k, λy:A. y) ∧ "+
							"ψ(t) = x",
						BySets(b.Assume())),
					"ψ is a point",
					"over x")
				data := b.Conjuncts(
					b.Have(
						"ψ is a ring map on D, fixing k and vanishing off D",
						"ring_homomorphism(restrict_ring(field_ring(M), invariant_chart(C, H)), «target», ψ) ∧ "+
							"(∀c:A. c ∈ k ⇒ ψ(c) = c) ∧ "+
							"(∀y:A. y ∉ invariant_chart(C, H) ⇒ ψ(y) = M.zero)",
						By(point[0], algebra_points.AlgebraPointsMember.At(onD, target, k, identity, ψ))),
					"ψ is a ring map",
					"ψ fixes k",
					"ψ vanishes off D")
				g, polynomialData := b.ObtainAs[Fun[Nat, A]](
					"a monic polynomial g over D vanishes on the orbit of z, of degree its size",
					"∃g:(num → A). "+
						"    polynomial_over(invariant_chart(C, H), g) ∧ "+
						"    polynomial_monic(g) ∧ "+
						"    polynomial_degree(g) = card(«Y») ∧ "+
						"    ∀r:A. r ∈ «Y» ⇒ polynomial_eval(g, r) = M.zero",
					By(subL, subC, cInL, zIn, subgroup, finiteH, keeps, OrbitPolynomial.Read(M).At(K, L, C, H, z)))
				parts := b.Conjuncts(
					polynomialData,
					"g is over D",
					"it is monic",
					"of degree card(Y)",
					"vanishing on Y")
				zInY := b.Have(
					"z lies on its orbit",
					"z ∈ «Y»",
					BySets(identityIn, symmetric_group.MapIdentity.At(z)))
				finiteY := b.Have(
					"the orbit is finite",
					"finite(«Y»)",
					By(finiteH, finite_set.FiniteImage.At(orbitMap, H)))
				positive := b.Have(
					"so g has positive degree",
					"0 < polynomial_degree(g)",
					parts[2].Rw(),
					ByArith(
						b.Have(
							"the orbit is not empty",
							"card(«Y») ≠ 0",
							By(finiteY, zInY, cardinality.CardEqZero.At(Y), set_basic.NotInEmpty.At(z)))))
				least := b.Have(
					"g is of least degree among the relations of z over D",
					Statement{
						Binders: "∀q:(num → A).",
						Hypotheses: []string{
							"polynomial_over(invariant_chart(C, H), q)",
							"q ≠ vec_zero",
							"polynomial_eval(q, z) = M.zero",
						},
						Conclusion: "polynomial_degree(g) ≤ polynomial_degree(q)",
					},
					Derive(func(c *Argument) {
						q := c.FixAs[Fun[Nat, A]]("q")
						given := c.Conjuncts(
							c.Assume(),
							"q is over D",
							"q is not zero",
							"q vanishes at z")
						c.Show(
							"a relation over D vanishes on the orbit",
							parts[2].Rw(),
							By(
								subL,
								cInL,
								zIn,
								hInG,
								given[0],
								given[1],
								given[2],
								OrbitPolynomialLeast.Read(M).At(K, L, C, H, z, q)))
					}))
				zField := b.Have(
					"z lies in M",
					"z ∈ M.carrier",
					BySets(zIn, cInL, subL, field.SubfieldSubset.At(fieldM, L)))
				ev, overD := b.ObtainAs[Fun[A, A]](
					"ψ extends to a point ev of D[z]",
					"∃ev:(A → A). "+
						"    ev ∈ "+
						"    geometric_evaluation_points(M, "+
						"        k, "+
						"        polynomial_image(field_ring(M), invariant_chart(C, H), z)) ∧ "+
						"    ∀y:A. y ∈ invariant_chart(C, H) ⇒ ev(y) = ψ(y)",
					By(
						closed,
						subk,
						subD,
						kInD,
						zField,
						parts[0],
						parts[1],
						positive,
						b.Have(
							"g vanishes at z",
							"polynomial_eval(g, z) = M.zero",
							By(zInY, parts[3].At(z))),
						least,
						data[0],
						data[1],
						PointExtendsAtRoot.Read(M).AsFact().At(k, D, ψ, g, z)))
				evParts := b.Conjuncts(
					overD,
					"ev is a point of D[z]",
					"ev extends ψ")
				onChart := b.Have(
					"which is C",
					"ev ∈ geometric_evaluation_points(M, k, C)",
					By(Normalized, evParts[0], generated))
				b.Take(ev)
				b.Do(SplitConj(
					Case(
						"ev lies over x",
						By(
							onFibre.At(ev),
							onChart,
							b.Have(
								"ev agrees with ψ at t",
								"ev(t) = x",
								By(Normalized, tInD, point[1], evParts[1].At(t))))),
					Case(
						"its restriction to D is ψ",
						Derive(func(c *Argument) {
							c.Do(Funext())
							y := c.FixAs[A]("y")
							c.Show(
								"on D they agree, and off D both vanish",
								By(evParts[1].At(y), data[2].At(y)))
						}))))
			}))
		restriction := arg.TermAs[Fun[Fun[A, A], Fun[A, A]]]("«restriction»")
		fibre := arg.TermAs[Set[Fun[A, A]]]("«fibre»")
		pointwise := arg.Have(
			"a map is a restriction exactly when it is a point of D over x",
			"∀ψ:(A → A). ψ ∈ image(«restriction», «fibre») ⇔ ψ ∈ «invariantFibre»",
			Derive(func(b *Argument) {
				ψ := b.FixAs[Fun[A, A]]("ψ")
				membership := set_basic.InImage.At(restriction, fibre, ψ)
				b.Iff()
				b.Forward(
					"a restriction is a point of D over x",
					func(c *Argument, inImage Fact) {
						ev, chosen := c.UnpackAs[Fun[A, A]](
							c.Have(
								"ψ restricts a point ev of C over x",
								"∃ev:(A → A). ev ∈ «fibre» ∧ ψ = (λy:A. COND(y ∈ invariant_chart(C, H), ev(y), M.zero))",
								By(inImage, membership)),
							"ev")
						parts := c.Conjuncts(
							chosen,
							"ev lies on the fibre",
							"ψ is its restriction")
						c.Show(
							"as a restriction of a point of C is",
							parts[1].Rw(),
							By(parts[0], forward.At(ev)))
					})
				b.Backward(
					"a point of D over x is a restriction",
					func(c *Argument, inFibre Fact) {
						c.Show(
							"the extension to C restricts to it",
							By(inFibre, backward.At(ψ), membership))
					})
			}))
		restrictions := arg.TermAs[Set[Fun[A, A]]]("image(«restriction», «fibre»)")
		invariantFibre := arg.TermAs[Set[Fun[A, A]]]("«invariantFibre»")
		arg.Show(
			"the two sets have the same members",
			By(pointwise, set_basic.Extension.At(restrictions, invariantFibre)))
	}),
})}

// InvariantAgreement — two points of C with the same value at t agree on the invariants
// of a finite subgroup H exactly when one is a translate of the other by H. A translate
// by H reads a point at an H-image, which on an invariant is the point itself, and two
// points agreeing on the invariants agree on the polynomial of the orbit of z.
var InvariantAgreement = invariantAgreementThm{family.Add(registry.ProofEntry{
	Name: "InvariantAgreement",
	Key:  "prop_acfe441b6163361b",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k K L C:set(A). ∀H:set(permutation(A)). ∀t z:A. ∀ev ew:(A → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"subfield(M, L)",
			"k ⊆ K",
			"subring(field_ring(M), C)",
			"C ⊆ L",
			"k ⊆ C",
			"t ∈ K",
			"t ∈ C",
			"z ∈ C",
			"subgroup(galois_group(M, K, L), H)",
			"finite(H)",
			"∀s:permutation(A). ∀y:A. s ∈ H ∧ y ∈ C ⇒ permutation_map(s, y) ∈ C",
			"∀f g:(A → A). " +
				"    f ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    g ∈ geometric_evaluation_points(M, k, C) ∧ " +
				"    f(t) = g(t) ∧ " +
				"    f(z) = g(z) ⇒ " +
				"    f = g",
			"ev ∈ geometric_evaluation_points(M, k, C)",
			"ew ∈ geometric_evaluation_points(M, k, C)",
			"injective_on(«Y», ev)",
			"ev(t) = ew(t)",
		},
		Conclusion: "(∀y:A. y ∈ invariant_chart(C, H) ⇒ ev(y) = ew(y)) ⇔ " +
			"∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), C, s, ev) = ew",
		Abbrev: Abbrev{
			{Name: "Y", Text: "image(λs:permutation(A). permutation_map(s, z), H)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, K, L, C *Expr[Set[A]],
		H *Expr[Set[symmetric_group.Permutation[A]]],
		t, z *Expr[A],
		ev, ew *Arrow[A, A],
		subk, subL, kInK, subC, cInL, kInC, tInK, tInC, zIn, subgroup, finiteH, keeps, determined, evIn, ewIn, injective, atT Fact,
	) {
		zero := arg.TermAs[A]("M.zero")
		D := arg.TermAs[Set[A]]("invariant_chart(C, H)")
		closures := arg.Conjuncts(
			arg.Unfolded(subgroup, group.SubgroupDef),
			"H consists of automorphisms",
			"holding the identity",
			"products",
			"and inverses")
		inverses := closures[3]
		arg.Iff()
		arg.Forward(
			"agreement on the invariants gives agreement on the coefficients of the orbit polynomial",
			func(b *Argument, agree Fact) {
				g, polynomialData := b.ObtainAs[Fun[Nat, A]](
					"a monic polynomial g over D vanishes on the orbit of z, of degree its size",
					"∃g:(num → A). "+
						"    polynomial_over(invariant_chart(C, H), g) ∧ "+
						"    polynomial_monic(g) ∧ "+
						"    polynomial_degree(g) = card(«Y») ∧ "+
						"    ∀r:A. r ∈ «Y» ⇒ polynomial_eval(g, r) = M.zero",
					By(subL, subC, cInL, zIn, subgroup, finiteH, keeps, OrbitPolynomial.Read(M).At(K, L, C, H, z)))
				parts := b.Conjuncts(
					polynomialData,
					"g is over D",
					"it is monic",
					"of degree card(Y)",
					"vanishing on Y")
				dInC := b.Have(
					"the invariants lie in C",
					"invariant_chart(C, H) ⊆ C",
					BySets(galois_good_open.InvariantChartDef.At(C, H)))
				b.Show(
					"the two points lie on one orbit",
					By(
						subk,
						subL,
						kInK,
						subC,
						cInL,
						kInC,
						tInK,
						tInC,
						zIn,
						subgroup,
						keeps,
						finiteH,
						b.Have(
							"g is over C",
							"polynomial_over(C, g)",
							By(parts[0], dInC, polynomial.PolynomialOverMono.At(zero, D, C, g))),
						parts[1],
						parts[2],
						parts[3],
						determined,
						evIn,
						ewIn,
						injective,
						atT,
						b.Have(
							"ev and ew agree on the coefficients of g",
							"∀i:num. ev(g(i)) = ew(g(i))",
							Derive(func(c *Argument) {
								c.FixAs[Nat]("i")
								c.Show(
									"which lie in D",
									By(agree.At(c.TermAs[A]("g(i)")), parts[0], polynomial.PolynomialOverDef.At(zero, D, g)))
							})),
						PointsOnOneOrbit.Read(M).At(k, K, L, C, H, t, z, g, ev, ew)))
			})
		arg.Backward(
			"a translate by H reads a point at an H-image, and H fixes the invariants",
			func(b *Argument, translate Fact) {
				s, chosen := b.UnpackAs[symmetric_group.Permutation[A]](translate, "s")
				parts := b.Conjuncts(
					chosen,
					"s lies in H",
					"its translate of ev is ew")
				b.FixAs[A]("y")
				yIn := b.Assume()
				invariant := b.Conjuncts(
					b.Have(
						"y lies in C and H fixes it",
						"y ∈ C ∧ ∀p:permutation(A). p ∈ H ⇒ permutation_map(p, y) = y",
						BySets(yIn, galois_good_open.InvariantChartDef.At(C, H))),
					"y lies in C",
					"H fixes y")
				inverse := b.TermAs[symmetric_group.Permutation[A]]("permutation_inverse(s)")
				fixed := b.Have(
					"so the inverse of s fixes y",
					"permutation_map(permutation_inverse(s), y) = y",
					By(parts[0], inverses.At(s), invariant[1].At(inverse)))
				b.Show(
					"so ew reads ev at y",
					parts[1].RwRev(),
					Simp(Fwd(galois_good_open.EvaluationActionDef)),
					fixed.Rw(),
					By(invariant[0]))
			})
	}),
})}

// ChartFibres — over an algebraic x with a(x) ≠ 0, the fibre of the chart C is a torsor
// of the group G, with the subgroups acting as the galois_good_open clause reads. The
// chart holds the conjugates of z, the derivative of the minimal polynomial F of z is a
// unit of C at its roots, and F, over k[t], has degree card(G). So points are determined
// at t and z, are injective on the orbit of z, and agree on the coefficients of F along
// the fibre, which is what the torsor and the invariant members ask.
var ChartFibres = chartFibresThm{family.Add(registry.ProofEntry{
	Name: "ChartFibres",
	Key:  "prop_56a0832d18999cdf",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t z x:A. ∀a:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, k)",
			"subfield(M, L)",
			"k ⊆ L",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"z ∈ L",
			"field_adjoin(M, «K», {z}) = L",
			"algebraic_over(M, «K», z)",
			"polynomial_over(«B», «F»)",
			"polynomial_degree(«F») = card(«G»)",
			"finite(«G»)",
			"polynomial_over(k, a)",
			"polynomial_eval(a, t) ≠ M.zero",
			"∀p:permutation(A). p ∈ «G» ⇒ permutation_map(p, z) ∈ «C»",
			"∀r:A. " +
				"    r ∈ «C» ∧ polynomial_eval(«F», r) = M.zero ⇒ " +
				"    ring_unit(restrict_ring(field_ring(M), «C»), polynomial_eval(polynomial_derivative(«F»), r))",
			"x ∈ algebraic_elements(M, k)",
			"polynomial_eval(a, x) ≠ M.zero",
		},
		Conclusion: "free_finite_action(galois_group(M, «K», L), " +
			"    «fibre», " +
			"    evaluation_action(field_ring(M), «C»)) ∧ " +
			"card(«fibre») = card(«G») ∧ " +
			"(∀ev ew:(A → A). " +
			"    ev ∈ «fibre» ∧ ew ∈ «fibre» ⇒ " +
			"    ∃s:permutation(A). s ∈ «G» ∧ evaluation_action(field_ring(M), «C», s, ev) = ew) ∧ " +
			"(∀H:set(permutation(A)). " +
			"    subgroup(galois_group(M, «K», L), H) ⇒ " +
			"    image(«restriction»(H), «fibre») = «invariantFibre»(H) ∧ " +
			"    (∀ev ew:(A → A). " +
			"        ev ∈ «fibre» ∧ ew ∈ «fibre» ⇒ " +
			"        ((∀y:A. y ∈ invariant_chart(«C», H) ⇒ ev(y) = ew(y)) ⇔ " +
			"            ∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), «C», s, ev) = ew)))",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "F", Text: "minimal_polynomial(M, «K», z)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
			{Name: "G", Text: "field_automorphisms(M, «K», L)"},
			{Name: "target", Text: "restrict_ring(field_ring(M), algebraic_elements(M, k))"},
			{Name: "fibre", Text: "geometric_fibre(M, k, «C», t, x)"},
			{Name: "invariantFibre", Text: "λH:set(permutation(A)). " +
				"    {ev:(A → A) | " +
				"        ev ∈ " +
				"        algebra_points(restrict_ring(field_ring(M), invariant_chart(«C», H)), " +
				"            «target», " +
				"            k, " +
				"            λy:A. y) ∧ " +
				"        ev(t) = x}"},
			{Name: "restriction", Text: "λH:set(permutation(A)). λev:(A → A). λy:A. " +
				"    COND(y ∈ invariant_chart(«C», H), ev(y), M.zero)"},
			{Name: "Y", Text: "image(λs:permutation(A). permutation_map(s, z), «G»)"},
			{Name: "chart", Text: "restrict_ring(field_ring(M), «C»)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t, z, x *Expr[A],
		a *Arrow[Nat, A],
		closed, subk, subL, kInL, tIn, transcendental, zIn, generated, algebraic, fOver, fDegree, finiteG, aOver, nonzero, conjugates, units, xIn, xGood Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		zero := arg.TermAs[A]("M.zero")
		target := arg.TermAs[module_record.RingOps[A]]("«target»")
		K, B, C := arg.TermAs[Set[A]]("«K»"), arg.TermAs[Set[A]]("«B»"), arg.TermAs[Set[A]]("«C»")
		Y := arg.TermAs[Set[A]]("«Y»")
		F := arg.TermAs[Fun[Nat, A]]("«F»")
		G := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«G»")
		nothing := arg.TermAs[Set[A]]("∅")
		single := arg.TermAs[Set[A]]("{z}")
		lField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subL, field.SubfieldSubset.At(fieldM, L)))
		tField := arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(tIn, lField))
		zField := arg.Have(
			"z lies in M",
			"z ∈ M.carrier",
			BySets(zIn, lField))
		tm, zm := arg.MemberOf[on.M](t, tField), arg.MemberOf[on.M](z, zField)
		facts := arg.Conjuncts(
			GroupPremises(subk, subL, kInL, tIn, zIn, aOver, nonzero, ChartFacts.Read(M).At(k, L, t, z, a)),
			"k[t] is a subring",
			"holding k",
			"and t",
			"and u",
			"k[t][z] is a subring",
			"holding k[t]",
			"and z",
			"C is a subring",
			"holding k[t][z]",
			"inside L",
			"with the inverse of u",
			"inverting u again adds nothing")
		kInB, tInB, bInU, zInU, subC, uInC, cInL :=
			facts[1], facts[2], facts[5], facts[6], facts[7], facts[8], facts[9]
		bInC := arg.Have(
			"k[t] lies in C",
			"«B» ⊆ «C»",
			BySets(bInU, uInC))
		kInC := arg.Have(
			"k lies in C",
			"k ⊆ «C»",
			BySets(kInB, bInC))
		tInC := arg.Have(
			"t lies in C",
			"t ∈ «C»",
			BySets(tInB, bInC))
		zInC := arg.Have(
			"z lies in C",
			"z ∈ «C»",
			BySets(zInU, uInC))
		adjoined := arg.Conjuncts(
			GroupPremises(subk, algebraic_element.AdjoinElementSubfield.Read(M).At(k, tm)),
			"k(t) is a subfield",
			"holding k",
			"and t")
		subK, kInK, tInK := adjoined[0], adjoined[1], adjoined[2]
		kField := arg.Have(
			"k(t) lies in M",
			"«K» ⊆ M.carrier",
			By(subK, field.SubfieldSubset.At(fieldM, K)))
		kInLField := arg.Have(
			"k(t) lies in L",
			"«K» ⊆ L",
			generated.RwRev(),
			By(subK, zField, algebraic_element.AdjoinElementSubfield.Read(M).At(K, zm)))
		spec := arg.Conjuncts(
			GroupPremises(adjoined[0], algebraic, algebraic_element.MinimalPolynomialSpec.Read(M).At(K, zm)),
			"F is over k(t)",
			"F is monic",
			"F vanishes at z",
			"F is of least degree")
		fOverK, fMonic, fRoot := spec[0], spec[1], spec[2]
		fOverC := arg.Have(
			"F is over C",
			"polynomial_over(«C», «F»)",
			By(fOver, bInC, polynomial.PolynomialOverMono.At(zero, B, C, F)))
		fNonzero := arg.Have(
			"F is not zero",
			"«F» ≠ vec_zero",
			By(fMonic, polynomial.MonicNonzero.Read(integral_domain.FieldIntegralDomain.Read(M)).At(F)))
		keeps := arg.Have(
			"the group keeps C",
			"∀s:permutation(A). ∀y:A. s ∈ «G» ∧ y ∈ «C» ⇒ permutation_map(s, y) ∈ «C»",
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"s is an automorphism",
					"y lies in C")
				stable := b.Have(
					"s maps C onto itself",
					"image(permutation_map(s), «C») = «C»",
					By(
						subk,
						subL,
						kInL,
						tIn,
						zIn,
						aOver,
						nonzero,
						conjugates,
						given[0],
						GaloisChartStable.Read(M).At(k, L, t, z, a, s)))
				b.Show(
					"so s(y) lies in C",
					By(
						stable,
						b.Have(
							"s(y) lies in the image of C",
							"permutation_map(s, y) ∈ image(permutation_map(s), «C»)",
							BySets(given[1]))))
			}))
		overNothing := arg.Have(
			"an automorphism over k(t) is one of k(t)(z)",
			"∀p:permutation(A). p ∈ «G» ⇒ p ∈ field_automorphisms(M, ∅, field_adjoin(M, «K», {z}))",
			Derive(func(b *Argument) {
				b.FixAs[symmetric_group.Permutation[A]]("p")
				pIn := b.Assume()
				b.Show(
					"forgetting what it fixes",
					generated.Rw(),
					BySets(
						pIn,
						field_automorphism.FieldAutomorphismsDef.At(fieldM, K, L),
						field_automorphism.FieldAutomorphismsDef.At(fieldM, nothing, L)))
			}))
		fixes := arg.Have(
			"the group fixes k(t)",
			"∀p:permutation(A). p ∈ «G» ⇒ ∀y:A. y ∈ «K» ⇒ permutation_map(p, y) = y",
			Derive(func(b *Argument) {
				b.FixAs[symmetric_group.Permutation[A]]("p")
				b.Show(
					"by the definition of the group",
					BySets(b.Assume(), field_automorphism.FieldAutomorphismsDef.At(fieldM, K, L)))
			}))
		injective := arg.Have(
			"an automorphism is read off at z",
			"injective_on(«G», λs:permutation(A). permutation_map(s, z))",
			Unfold(functions.InjectiveOnDef),
			Derive(func(b *Argument) {
				p := b.FixAs[symmetric_group.Permutation[A]]("p")
				q := b.FixAs[symmetric_group.Permutation[A]]("q")
				given := b.Conjuncts(
					b.Assume(),
					"p is an automorphism",
					"q is an automorphism",
					"they agree at z")
				b.Show(
					"two automorphisms agreeing on the generators are one",
					By(
						kField,
						b.Have(
							"z lies in M",
							"{z} ⊆ M.carrier",
							BySets(zField)),
						overNothing.At(p),
						overNothing.At(q),
						given[0],
						given[1],
						b.Have(
							"they fix k(t)",
							"∀y:A. y ∈ «K» ⇒ permutation_map(p, y) = permutation_map(q, y)",
							Derive(func(c *Argument) {
								y := c.FixAs[A]("y")
								c.Show(
									"so they agree there",
									By(c.Assume(), given[0], given[1], fixes.At(p, y), fixes.At(q, y)))
							})),
						b.Have(
							"and agree at z",
							"∀y:A. y ∈ {z} ⇒ permutation_map(p, y) = permutation_map(q, y)",
							BySets(given[2])),
						field_automorphism.AutomorphismsAgreeOnGenerators.Read(M).At(K, single, p, q)))
			}))
		roots := arg.Have(
			"F vanishes on the orbit of z",
			"∀r:A. r ∈ «Y» ⇒ polynomial_eval(«F», r) = M.zero",
			Derive(func(b *Argument) {
				b.FixAs[A]("r")
				rIn := b.Assume()
				s, onOrbit := b.ObtainAs[symmetric_group.Permutation[A]](
					"r is s(z) for an automorphism s",
					"∃s:permutation(A). s ∈ «G» ∧ r = permutation_map(s, z)",
					BySets(rIn))
				parts := b.Conjuncts(
					onOrbit,
					"s is an automorphism",
					"r is s(z)")
				b.Show(
					"automorphisms over k(t) permute the roots of F",
					parts[1].Rw(),
					By(
						subL,
						kInLField,
						parts[0],
						fOverK,
						zIn,
						fRoot,
						field_automorphism.AutomorphismPermutesRoots.Read(M).AsFact().At(K, L, F, s, z)))
			}))
		determined := arg.Have(
			"points of C are determined at t and z",
			Statement{
				Binders: "∀f g:(A → A).",
				Hypotheses: []string{
					"f ∈ geometric_evaluation_points(M, k, «C»)",
					"g ∈ geometric_evaluation_points(M, k, «C»)",
					"f(t) = g(t)",
					"f(z) = g(z)",
				},
				Conclusion: "f = g",
			},
			Derive(func(b *Argument) {
				f := b.FixAs[Fun[A, A]]("f")
				g := b.FixAs[Fun[A, A]]("g")
				given := b.Conjuncts(
					b.Assume(),
					"f is a point",
					"g is a point",
					"they agree at t",
					"and at z")
				b.Show(
					"which is the chart's rigidity",
					By(
						subk,
						tField,
						zField,
						aOver,
						nonzero,
						given[0],
						given[1],
						given[2],
						given[3],
						ChartPointDetermined.Read(M).AsFact().At(k, t, z, a, f, g)))
			}))
		orbitInC := arg.Have(
			"the orbit lies in C",
			"«Y» ⊆ «C»",
			BySets(conjugates))
		separated := arg.Have(
			"points of C are injective on the orbit",
			"∀ev:(A → A). ev ∈ geometric_evaluation_points(M, k, «C») ⇒ injective_on(«Y», ev)",
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				b.Show(
					"F′ is a unit of C at the roots of F",
					By(
						subk,
						subC,
						fOverC,
						fNonzero,
						orbitInC,
						roots,
						units,
						b.Assume(),
						PointSeparatesRoots.Read(M).At(k, C, Y, F, ev)))
			}))
		onFibre := arg.Have(
			"a map lies on the fibre when it is a geometric point of C over x",
			"∀ev:(A → A). ev ∈ «fibre» ⇔ ev ∈ geometric_evaluation_points(M, k, «C») ∧ ev(t) = x",
			BySets(galois_good_open.GeometricFibreDef.At(fieldM, k, C, t, x)))
		coefficients := arg.Have(
			"points over x agree on the coefficients of F, which lie in k[t]",
			"∀ev ew:(A → A). ∀i:num. ev ∈ «fibre» ∧ ew ∈ «fibre» ⇒ ev(«F»(i)) = ew(«F»(i))",
			Derive(func(b *Argument) {
				ev := b.FixAs[Fun[A, A]]("ev")
				ew := b.FixAs[Fun[A, A]]("ew")
				b.FixAs[Nat]("i")
				given := b.Conjuncts(
					b.Assume(),
					"ev lies on the fibre",
					"ew lies on the fibre")
				evData := b.Conjuncts(
					b.Have(
						"ev is a ring map on C over x, fixing k",
						"ring_homomorphism(«chart», «target», ev) ∧ (∀c:A. c ∈ k ⇒ ev(c) = c) ∧ ev(t) = x",
						BySets(given[0], onFibre.At(ev), galois_good_open.GeometricPointMember.At(fieldM, k, C, ev))),
					"ev is a ring map",
					"ev fixes k",
					"ev sends t to x")
				ewData := b.Conjuncts(
					b.Have(
						"so is ew",
						"ring_homomorphism(«chart», «target», ew) ∧ (∀c:A. c ∈ k ⇒ ew(c) = c) ∧ ew(t) = x",
						BySets(given[1], onFibre.At(ew), galois_good_open.GeometricPointMember.At(fieldM, k, C, ew))),
					"ew is a ring map",
					"ew fixes k",
					"ew sends t to x")
				value := b.TermAs[A]("«F»(i)")
				b.Show(
					"they agree on k and at t, so on k[t]",
					By(
						evData[0],
						ewData[0],
						kInC,
						tInC,
						b.Have(
							"they agree on k",
							"∀c:A. c ∈ k ⇒ ev(c) = ew(c)",
							By(Normalized, evData[1], ewData[1])),
						b.Have(
							"and at t",
							"ev(t) = ew(t)",
							By(Normalized, evData[2], ewData[2])),
						b.Have(
							"the coefficient lies in k[t]",
							"«F»(i) ∈ «B»",
							By(fOver, polynomial.PolynomialOverDef.At(zero, B, F))),
						integral_element.PolynomialImageAgreement.Read(M).At(target, C, k, ev, ew, t, value)))
			}))
		e, pointOver := arg.ObtainAs[Fun[A, A]](
			"the chart has a point over x",
			"∃e:(A → A). e ∈ «fibre»",
			Derive(func(b *Argument) {
				ev, chosen := b.UnpackAs[Fun[A, A]](
					b.Have(
						"M being closed, C has a point over x",
						"∃ev:(A → A). ev ∈ geometric_evaluation_points(M, k, «C») ∧ ev(t) = x",
						By(
							closed,
							subk,
							tField,
							zField,
							transcendental,
							algebraic,
							fOver,
							aOver,
							nonzero,
							xIn,
							xGood,
							ChartFibreNonempty.Read(M).AsFact().At(k, t, z, x, a))),
					"ev")
				b.Take(ev)
				b.Show(
					"it lies on the fibre",
					By(onFibre.At(ev), chosen))
			}))
		torsor := arg.Conjuncts(
			arg.Have(
				"so the group acts on the fibre freely and transitively, with card(G) points",
				"free_finite_action(galois_group(M, «K», L), «fibre», evaluation_action(field_ring(M), «C»)) ∧ "+
					"card(«fibre») = card(«G») ∧ "+
					"∀ev ew:(A → A). "+
					"    ev ∈ «fibre» ∧ ew ∈ «fibre» ⇒ "+
					"    ∃s:permutation(A). s ∈ «G» ∧ evaluation_action(field_ring(M), «C», s, ev) = ew",
				By(
					subk,
					subL,
					kInK,
					subC,
					cInL,
					kInC,
					tInK,
					tInC,
					zInC,
					finiteG,
					keeps,
					injective,
					fOverC,
					fMonic,
					fDegree,
					roots,
					determined,
					separated,
					coefficients,
					pointOver,
					ChartFibreTorsor.Read(M).At(k, K, L, C, t, z, x, F, e))),
			"the action is free and finite",
			"the fibre has card(G) points",
			"and the action is transitive")
		subgroups := arg.Have(
			"a subgroup H acts as the clause reads",
			Statement{
				Binders: "∀H:set(permutation(A)).",
				Hypotheses: []string{
					"subgroup(galois_group(M, «K», L), H)",
				},
				Conclusion: "image(«restriction»(H), «fibre») = «invariantFibre»(H) ∧ " +
					"(∀ev ew:(A → A). " +
					"    ev ∈ «fibre» ∧ ew ∈ «fibre» ⇒ " +
					"    ((∀y:A. y ∈ invariant_chart(«C», H) ⇒ ev(y) = ew(y)) ⇔ " +
					"        ∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), «C», s, ev) = ew))",
			},
			Derive(func(b *Argument) {
				H := b.FixAs[Set[symmetric_group.Permutation[A]]]("H")
				subgroup := b.Assume()
				hInG := b.Conjuncts(
					b.Unfolded(subgroup, group.SubgroupDef),
					"H consists of automorphisms",
					"holding the identity",
					"products",
					"and inverses")[0]
				finiteH := b.Have(
					"H is finite",
					"finite(H)",
					By(finiteG, hInG, finite_set.FiniteSubset.At(H, G)))
				keepsH := b.Have(
					"H keeps C",
					"∀s:permutation(A). ∀y:A. s ∈ H ∧ y ∈ «C» ⇒ permutation_map(s, y) ∈ «C»",
					Derive(func(c *Argument) {
						s := c.FixAs[symmetric_group.Permutation[A]]("s")
						y := c.FixAs[A]("y")
						given := c.Conjuncts(
							c.Assume(),
							"s lies in H",
							"y lies in C")
						c.Show(
							"H lies in the group",
							By(
								c.Have(
									"s is an automorphism",
									"s ∈ «G»",
									BySets(given[0], hInG)),
								given[1],
								keeps.At(s, y)))
					}))
				invariants := b.Conjuncts(
					b.Have(
						"the invariants D generate C with z",
						"subring(field_ring(M), invariant_chart(«C», H)) ∧ "+
							"k ⊆ invariant_chart(«C», H) ∧ "+
							"t ∈ invariant_chart(«C», H) ∧ "+
							"invariant_chart(«C», H) ⊆ «C» ∧ "+
							"polynomial_image(field_ring(M), invariant_chart(«C», H), z) = «C»",
						By(
							subk,
							subL,
							kInL,
							tIn,
							zIn,
							aOver,
							nonzero,
							hInG,
							InvariantChartGenerates.Read(M).At(k, L, t, z, a, H))),
					"D is a subring",
					"holding k",
					"and t",
					"inside C",
					"and D[z] is C")
				image := b.Have(
					"the fibre of C restricts onto the fibre of D",
					"image(«restriction»(H), «fibre») = «invariantFibre»(H)",
					By(
						closed,
						subk,
						subL,
						subC,
						cInL,
						zInC,
						invariants[0],
						invariants[1],
						invariants[2],
						invariants[4],
						subgroup,
						finiteH,
						keepsH,
						InvariantFibreImage.Read(M).At(k, K, L, C, H, t, z, x)))
				agreement := b.Have(
					"and two of its points agree on D just when they differ by H",
					Statement{
						Binders:    "∀ev ew:(A → A).",
						Hypotheses: []string{"ev ∈ «fibre»", "ew ∈ «fibre»"},
						Conclusion: "(∀y:A. y ∈ invariant_chart(«C», H) ⇒ ev(y) = ew(y)) ⇔ " +
							"∃s:permutation(A). s ∈ H ∧ evaluation_action(field_ring(M), «C», s, ev) = ew",
					},
					Derive(func(c *Argument) {
						ev := c.FixAs[Fun[A, A]]("ev")
						ew := c.FixAs[Fun[A, A]]("ew")
						given := c.Conjuncts(
							c.Assume(),
							"ev lies on the fibre",
							"ew lies on the fibre")
						evOn := c.Conjuncts(
							c.Have(
								"ev is a point over x",
								"ev ∈ geometric_evaluation_points(M, k, «C») ∧ ev(t) = x",
								By(onFibre.At(ev), given[0])),
							"ev is a point",
							"over x")
						ewOn := c.Conjuncts(
							c.Have(
								"ew is a point over x",
								"ew ∈ geometric_evaluation_points(M, k, «C») ∧ ew(t) = x",
								By(onFibre.At(ew), given[1])),
							"ew is a point",
							"over x")
						orbitH := c.TermAs[Set[A]]("image(λs:permutation(A). permutation_map(s, z), H)")
						c.Show(
							"H is a finite subgroup keeping C",
							By(
								subk,
								subL,
								kInK,
								subC,
								cInL,
								kInC,
								tInK,
								tInC,
								zInC,
								subgroup,
								finiteH,
								keepsH,
								determined,
								evOn[0],
								ewOn[0],
								c.Have(
									"ev is injective on the orbit of H, part of the orbit of G",
									"injective_on(image(λs:permutation(A). permutation_map(s, z), H), ev)",
									By(
										evOn[0],
										separated.At(ev),
										c.Have(
											"the orbit of H lies in the orbit of G",
											"image(λs:permutation(A). permutation_map(s, z), H) ⊆ «Y»",
											BySets(hInG)),
										functions.InjectiveOnSubset.At(ev, orbitH, Y))),
								c.Have(
									"ev and ew agree at t",
									"ev(t) = ew(t)",
									By(Normalized, evOn[1], ewOn[1])),
								InvariantAgreement.Read(M).At(k, K, L, C, H, t, z, ev, ew)))
					}))
				b.Show(
					"which is the clause at H",
					By(image, agreement))
			}))
		arg.Show(
			"the fibre is a torsor, with the subgroups acting as claimed",
			By(torsor[0], torsor[1], torsor[2], subgroups))
	}),
})}

// ChartGoodOpen — the chart C = k[t][z][1/a(t)] of a primitive element z, integral over
// k[t] with the degree of F the order of the group, is a good open once it holds the
// conjugates of z and the derivative of F is a unit of C at the roots of F.
var ChartGoodOpen = chartGoodOpenThm{family.Add(registry.ProofEntry{
	Name: "ChartGoodOpen",
	Key:  "prop_5db1cbfa91971dfb",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t z:A. ∀a:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, «K», L)",
			"finite(«G»)",
			"z ∈ L",
			"field_adjoin(M, «K», {z}) = L",
			"algebraic_over(M, «K», z)",
			"polynomial_over(«B», «F»)",
			"polynomial_degree(«F») = card(«G»)",
			"polynomial_over(k, a)",
			"polynomial_eval(a, t) ≠ M.zero",
			"∀p:permutation(A). p ∈ «G» ⇒ permutation_map(p, z) ∈ «C»",
			"∀r:A. " +
				"    r ∈ «C» ∧ polynomial_eval(«F», r) = M.zero ⇒ " +
				"    ring_unit(restrict_ring(field_ring(M), «C»), polynomial_eval(polynomial_derivative(«F»), r))",
		},
		Conclusion: "galois_good_open(M, k, L, t, «C», a)",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "F", Text: "minimal_polynomial(M, «K», z)"},
			{Name: "U", Text: "polynomial_image(field_ring(M), «B», z)"},
			{Name: "C", Text: "ring_away(field_ring(M), «U», polynomial_eval(a, t))"},
			{Name: "G", Text: "field_automorphisms(M, «K», L)"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t, z *Expr[A],
		a *Arrow[Nat, A],
		closed, regular, finiteK, tIn, transcendental, galois, finiteG, zIn, generated, algebraic, fOver, fDegree, aOver, nonzero, conjugates, units Fact,
	) {
		ring := field.RingOn.Read(M)
		fieldM := arg.TermAs[FieldOps[A]]("M")
		parts := arg.Conjuncts(
			arg.Unfolded(regular, function_field.RegularFunctionFieldDef),
			"k is a subfield",
			"L is a subfield",
			"k lies in L",
			"k is perfect",
			"L is finitely generated over k",
			"L is algebraic over some k(s)",
			"k is closed in L")
		subk, subL, kInL := parts[0], parts[1], parts[2]
		tm := arg.MemberOf[on.M](t, arg.Have(
			"t lies in M",
			"t ∈ M.carrier",
			BySets(tIn, subL, field.SubfieldSubset.At(fieldM, L))))
		chart := arg.Conjuncts(
			GroupPremises(
				parts[0],
				parts[1],
				parts[2],
				tIn,
				zIn,
				generated,
				algebraic,
				fOver,
				aOver,
				nonzero,
				GaloisChartRing.Read(M).At(k, L, t, z, a)),
			"C lies in L",
			"C is a ring",
			"k[t][1/u] lies in C",
			"inverting u again adds nothing",
			"L is the fraction field of C",
			"C is finite over k[t][1/u]")
		stable := arg.Have(
			"the group preserves C",
			"∀s:permutation(A). s ∈ «G» ⇒ image(permutation_map(s), «C») = «C»",
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				b.Show(
					"it holds the conjugates of z",
					By(
						subk,
						subL,
						kInL,
						tIn,
						zIn,
						aOver,
						nonzero,
						conjugates,
						b.Assume(),
						GaloisChartStable.Read(M).At(k, L, t, z, a, s)))
			}))
		polynomialNonzero := arg.Have(
			"a is not the zero polynomial, its value at t not being zero",
			"a ≠ vec_zero",
			Derive(func(b *Argument) {
				b.Show(
					"the zero polynomial vanishes at t",
					By(Normalized, b.SupposeNot(), nonzero, polynomial_evaluation.EvalVecZero.Read(ring).At(tm)))
			}))
		arg.Do(
			Unfold(galois_good_open.GaloisGoodOpenDef),
			SplitConjAll(
				Case(
					"L is a regular function field",
					By(regular)),
				Case(
					"k is finite",
					By(finiteK)),
				Case(
					"t lies in L",
					By(tIn)),
				Case(
					"t is transcendental",
					By(transcendental)),
				Case(
					"L is Galois over k(t)",
					By(galois)),
				Case(
					"C lies in L",
					By(chart[0])),
				Case(
					"C is a ring",
					By(chart[1])),
				Case(
					"a is over k",
					By(aOver)),
				Case(
					"a is not zero",
					By(polynomialNonzero)),
				Case(
					"k[t][1/u] lies in C",
					By(chart[2])),
				Case(
					"inverting u again adds nothing",
					By(chart[3])),
				Case(
					"L is the fraction field of C",
					By(chart[4])),
				Case(
					"C is finite over k[t][1/u]",
					By(chart[5])),
				Case(
					"the group preserves C",
					By(stable)),
				Case(
					"over each good x the fibre is a torsor",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						given := b.Conjuncts(
							b.Assume(),
							"x is algebraic",
							"a does not vanish at x")
						fibres := b.Conjuncts(
							GroupPremises(
								closed,
								subk,
								subL,
								kInL,
								tIn,
								transcendental,
								zIn,
								generated,
								algebraic,
								fOver,
								fDegree,
								finiteG,
								aOver,
								nonzero,
								conjugates,
								units,
								given[0],
								given[1],
								ChartFibres.Read(M).At(k, L, t, z, x, a)),
							"the group acts freely on the fibre",
							"the fibre has as many points as the group",
							"any two points of the fibre are translates",
							"the subgroups read off the fibre, the invariant fibres spelled out")
						quotients := b.Simplified(
							fibres[3],
							Rev(galois_good_open.GeometricEvaluationPointsDef),
							Rev(galois_good_open.GeometricFibreDef))
						b.Show(
							"as the chart's fibres are",
							By(fibres[0], fibres[1], fibres[2], quotients))
					}))))
	}),
})}

// GaloisGoodFibresAreTorsors — L, Galois over k(t), has a good open. Take a primitive
// element z integral over k[t], and a denominator a(t) clearing the conjugates of z into
// C = k[t][z][1/a(t)] and making the derivative of its minimal polynomial a unit of C at
// the roots there; then C is the chart.
var GaloisGoodFibresAreTorsors = galoisGoodFibresAreTorsorsThm{family.Add(registry.ProofEntry{
	Name: "GaloisGoodFibresAreTorsors",
	Key:  "prop_87f16d4e0e18987c",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k L:set(A). ∀t:A.",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"regular_function_field(M, k, L)",
			"finite(k)",
			"t ∈ L",
			"¬algebraic_over(M, k, t)",
			"galois_over(M, field_adjoin(M, k, {t}), L)",
		},
		Conclusion: "∃C:set(A). ∃a:(num → A). galois_good_open(M, k, L, t, C, a)",
		Abbrev: Abbrev{
			{Name: "K", Text: "field_adjoin(M, k, {t})"},
			{Name: "B", Text: "polynomial_image(field_ring(M), k, t)"},
			{Name: "G", Text: "field_automorphisms(M, «K», L)"},
			{Name: "F", Text: "λz:A. minimal_polynomial(M, «K», z)"},
			{Name: "orbit", Text: "λz:A. image(λs:permutation(A). permutation_map(s, z), «G»)"},
			{Name: "chart", Text: "λz:A. λa:(num → A). " +
				"    ring_away(field_ring(M), polynomial_image(field_ring(M), «B», z), polynomial_eval(a, t))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k, L *Expr[Set[A]],
		t *Expr[A],
		closed, regular, finiteK, tIn, transcendental, galois Fact,
	) {
		fieldM := arg.TermAs[FieldOps[A]]("M")
		K := arg.TermAs[Set[A]]("«K»")
		G := arg.TermAs[Set[symmetric_group.Permutation[A]]]("«G»")
		parts := arg.Conjuncts(
			arg.Unfolded(regular, function_field.RegularFunctionFieldDef),
			"k is a subfield",
			"L is a subfield",
			"k lies in L",
			"k is perfect",
			"L is finitely generated over k",
			"L is algebraic over some k(s)",
			"k is closed in L")
		subk, subL, kInL := parts[0], parts[1], parts[2]
		data := arg.Conjuncts(
			arg.Unfolded(galois, galois_correspondence.GaloisOverDef),
			"L is finite over k(t)",
			"L is normal over k(t)",
			"L is separable over k(t)")
		between := arg.Conjuncts(
			arg.Have(
				"k(t) lies between k and L",
				"subfield(M, «K») ∧ «K» ⊆ L",
				By(subk, subL, kInL, tIn, algebraic_element.AdjoinElementBetween.Read(M).At(k, L, t))),
			"k(t) is a subfield",
			"inside L")
		finiteG := arg.Have(
			"the group is finite",
			"finite(«G»)",
			By(between[0], subL, between[1], data[0], field_automorphism.AutomorphismsBound.Read(M).At(K, L)))
		lField := arg.Have(
			"L lies in M",
			"L ⊆ M.carrier",
			By(subL, field.SubfieldSubset.At(fieldM, L)))
		z, primitive := arg.ObtainAs[A](
			"an integral primitive element z",
			"∃z:A. "+
				"    z ∈ L ∧ "+
				"    field_adjoin(M, «K», {z}) = L ∧ "+
				"    polynomial_over(«B», «F»(z)) ∧ "+
				"    polynomial_monic(«F»(z)) ∧ "+
				"    polynomial_degree(«F»(z)) = card(«G») ∧ "+
				"    polynomial_separable(restrict_ring(field_ring(M), «K»), «F»(z))",
			By(regular, tIn, transcendental, galois, GaloisPrimitiveElement.Read(M).At(k, L, t)))
		zParts := arg.Conjuncts(
			primitive,
			"z lies in L",
			"z generates L over k(t)",
			"F is over k[t]",
			"F is monic",
			"F has the degree of the order of the group",
			"F is separable")
		zIn, generated, fOver, fDegree, separable := zParts[0], zParts[1], zParts[2], zParts[4], zParts[5]
		algebraic := arg.Have(
			"z is algebraic over k(t), L being finite over it",
			"algebraic_over(M, «K», z)",
			By(
				M,
				between[0],
				subL,
				between[1],
				data[0],
				zIn,
				algebraic_element.FiniteExtensionAlgebraic.Read(M).AsFact().At(K, L, z)))
		orbitMap := arg.TermAs[Fun[symmetric_group.Permutation[A], A]](
			"λs:permutation(A). permutation_map(s, z)")
		conjugates := arg.Have(
			"the conjugates of z lie in L",
			"∀s:permutation(A). s ∈ «G» ⇒ permutation_map(s, z) ∈ L",
			Derive(func(b *Argument) {
				s := b.FixAs[symmetric_group.Permutation[A]]("s")
				hom := b.Have(
					"s is a ring map of L",
					"ring_homomorphism(field_ring(restrict_field(M, L)), "+
						"    field_ring(restrict_field(M, L)), "+
						"    permutation_map(s))",
					By(subL, b.Assume(), field_automorphism.AutomorphismRingHomomorphism.Read(M).AsFact().At(K, L, s)))
				b.Show(
					"which keeps L",
					BySets(zIn, ring_homomorphism.MapIn.Read(hom).AsFact().At(z)))
			}))
		orbit := arg.TermAs[Set[A]]("«orbit»(z)")
		a, cleared := arg.ObtainAs[Fun[Nat, A]](
			"a denominator a over k clearing the orbit and making the derivative of F a unit at its roots",
			"∃a:(num → A). "+
				"    polynomial_over(k, a) ∧ "+
				"    polynomial_eval(a, t) ≠ M.zero ∧ "+
				"    «orbit»(z) ⊆ «chart»(z, a) ∧ "+
				"    (∀r:A. "+
				"        r ∈ «chart»(z, a) ∧ polynomial_eval(«F»(z), r) = M.zero ⇒ "+
				"        ring_unit(restrict_ring(field_ring(M), «chart»(z, a)), "+
				"            polynomial_eval(polynomial_derivative(«F»(z)), r)))",
			By(
				subk,
				arg.Have(
					"t lies in M",
					"t ∈ M.carrier",
					BySets(tIn, lField)),
				arg.Have(
					"z lies in M",
					"z ∈ M.carrier",
					BySets(zIn, lField)),
				algebraic,
				fOver,
				separable,
				arg.Have(
					"the orbit is finite",
					"finite(«orbit»(z))",
					By(finiteG, finite_set.FiniteImage.At(orbitMap, G))),
				arg.Have(
					"it lies in k(t)(z)",
					"«orbit»(z) ⊆ field_adjoin(M, «K», {z})",
					generated.Rw(),
					BySets(conjugates)),
				SeparableChartDenominator.Read(M).AsFact().At(k, orbit, t, z)))
		chart := arg.Conjuncts(
			cleared,
			"a is over k",
			"a(t) is not zero",
			"C holds the orbit",
			"F′ is a unit of C at the roots of F")
		arg.Take(arg.TermAs[Set[A]]("«chart»(z, a)"))
		arg.Take(a)
		arg.Show(
			"C is a good open",
			By(
				closed,
				regular,
				finiteK,
				tIn,
				transcendental,
				galois,
				finiteG,
				zIn,
				generated,
				algebraic,
				fOver,
				fDegree,
				chart[0],
				chart[1],
				arg.Have(
					"C holds the conjugates of z",
					"∀p:permutation(A). p ∈ «G» ⇒ permutation_map(p, z) ∈ «chart»(z, a)",
					BySets(chart[2])),
				chart[3],
				ChartGoodOpen.Read(M).At(k, L, t, z, a)))
	}),
})}
