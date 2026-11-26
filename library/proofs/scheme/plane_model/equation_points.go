// equation_points.go — a solution of the plane equation is a point of the chart.
// The chart is k[t][z], and the point is the inclusion of k lifted twice: to k[t],
// t being transcendental, and on to k[t][z], the solution being a root of the moved
// minimal polynomial of z, whose coefficients lie in k[t].

package plane_model

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/rational_function_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PlaneModelOverPolynomials — the polynomial of an integral plane model lies over k[t]:
// below its degree the weight clause writes each coefficient as a polynomial in t, at its
// degree the coefficient is one, the minimal polynomial being monic, and above it zero.
var PlaneModelOverPolynomials = planeModelOverPolynomialsThm{family.Add(registry.ProofEntry{
	Name: "PlaneModelOverPolynomials",
	Key:  "prop_eb660f2f1fc03620",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k:set(A). ∀t z:A. ∀F:(num → A). ∀b:num.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
		},
		Conclusion: "polynomial_over(«pmPolynomialsInK», F)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow[Nat, A],
		b *Expr[Nat],
		inField, model Fact,
	) {
		function := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
		functionRing := a.TermAs[RingOps[A]]("field_ring(restrict_field(M, K))")
		zero, one := a.TermAs[A]("M.zero"), a.TermAs[A]("M.one")
		polynomials := a.TermAs[Set[A]]("«pmPolynomialsInK»")
		rational := a.TermAs[Set[A]]("«pmRationalInK»")
		functionField := a.Have(
			"K is a field under the operations of M",
			"field_on(restrict_field(M, K))",
			By(inField, field.SubfieldFieldOn.Read(M).At(K)))
		data := a.Conjuncts(
			a.Unfolded(model, IntegralPlaneModelDef),
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
		regular, tInK, transcendental, zInK, minimal, lower :=
			data[0], data[1], data[2], data[3], data[5], data[9]
		tMember := a.MemberOf[on.Any](t, tInK)
		zMember := a.MemberOf[on.Any](z, zInK)
		kField := a.Have(
			"k is a subfield of K",
			"subfield(restrict_field(M, K), k)",
			By(regular, function_field.RegularFunctionFieldDef.At(function, k, K)))
		rationalField := a.Have(
			"k(t) is a subfield of K",
			"subfield(restrict_field(M, K), «pmRationalInK»)",
			By(kField, tInK, algebraic_element.AdjoinElementSubfield.Read(functionField).At(k, tMember)))
		polynomialRing := a.Have(
			"k[t] is a subring of K",
			"subring(field_ring(restrict_field(M, K)), «pmPolynomialsInK»)",
			By(kField, tInK, algebraic_element.PolynomialImageRing.Read(functionField).At(k, tMember)))
		algebraic := a.Have(
			"z is algebraic over k(t), K being algebraic over "+
				"the rational functions of any transcendental element",
			"algebraic_over(restrict_field(M, K), «pmRationalInK», z)",
			By(
				regular,
				tInK,
				transcendental,
				zInK,
				rational_function_field.AlgebraicOverAnyTranscendental.Read(functionField).At(k, K, t, z)))
		spec := a.Conjuncts(
			a.Have(
				"so F is a monic polynomial over k(t)",
				"polynomial_over(«pmRationalInK», F) ∧ polynomial_monic(F)",
				minimal.Rw(),
				By(
					rationalField,
					algebraic,
					algebraic_element.MinimalPolynomialSpec.Read(functionField).At(rational, zMember))),
			"F is a polynomial over k(t)",
			"it is monic")
		overRational, monic := spec[0], spec[1]
		values := a.Have(
			"k[t] is the set of the values at t of the polynomials over k",
			"∀u:A. u ∈ «pmPolynomialsInK» ⇔ ∃p:(num → A). polynomial_over(k, p) ∧ u = polynomial_eval(p, t)",
			Unfold(algebraic_element.PolynomialImageDef),
			SetTac())
		coefficients := a.Have(
			"every coefficient of F lies in k[t]",
			"∀i:num. F(i) ∈ «pmPolynomialsInK»",
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				c.Cases(c.TermAs[Bool]("i < polynomial_degree(F)"))
				c.When(
					"below the degree the weight clause writes it as a polynomial in t",
					func(d *Argument, below Fact) {
						d.Show(
							"so it lies in k[t]",
							By(below, lower.At(i), values.At(d.TermAs[A]("F(i)"))))
					})
				c.Otherwise(
					"at or above the degree it is one or zero",
					func(d *Argument, notBelow Fact) {
						d.Cases(d.TermAs[Bool]("i = polynomial_degree(F)"))
						d.When(
							"at the degree F is monic",
							func(e *Argument, at Fact) {
								e.Show(
									"and k[t] holds one",
									By(
										Normalized,
										monic,
										polynomialRing,
										at,
										polynomial.PolynomialMonicDef.At(zero, one, F),
										comm_ring.SubringOne.At(functionRing, polynomials)))
							})
						d.Otherwise(
							"above the degree the coefficient of a polynomial is zero",
							func(e *Argument, notAt Fact) {
								above := e.Have(
									"i lies past the degree",
									"suc(polynomial_degree(F)) ≤ i",
									ByArith(notBelow, notAt))
								e.Show(
									"and k[t] holds zero",
									By(
										above,
										overRational,
										polynomialRing,
										comm_ring.SubringZero.At(functionRing, polynomials),
										polynomial.DegreeVec.At(zero, rational, F),
										vec_space.VecDef.At(zero, e.VecAt[A](e.TermAs[Nat]("suc(polynomial_degree(F))"), "F"))))
							})
					})
			}))
		a.Show(
			"F has finite support, being over k(t), and its coefficients lie in k[t]",
			By(
				coefficients,
				overRational,
				polynomial.PolynomialOverDef.At(zero, rational, F),
				polynomial.PolynomialOverDef.At(zero, polynomials, F)))
	}),
})}

// PlaneSolutionPoint — a solution (x, y) of the plane equation in a field l over k is a
// point of the chart k[t][z] over k, sending t to x and z to y: the point is the identity
// of k lifted to k[t] at x, t being transcendental, and then to k[t][z] at y, y being a
// root of the minimal polynomial of z moved to the coefficients F(i)(x).
var PlaneSolutionPoint = planeSolutionPointThm{family.Add(registry.ProofEntry{
	Name: "PlaneSolutionPoint",
	Key:  "prop_7f1e2a5131380eeb",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀K k l:set(A). ∀t z:A. ∀F:(num → num → A). ∀b:num. ∀x y:A.",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, «f», b)",
			"absolute_plane_equation(M, k, F)",
			"subfield(M, l)",
			"k ⊆ l",
			"x ∈ l",
			"y ∈ l",
			"polynomial_eval(λi:num. polynomial_eval(F(i), x), y) = M.zero",
		},
		Conclusion: "∃φ:(A → A). φ ∈ algebra_points(«chartRing», «T», k, λu:A. u) ∧ φ(t) = x ∧ φ(z) = y",
		Abbrev: Abbrev{
			{Name: "f", Text: "λi:num. polynomial_eval(F(i), t)"},
			{Name: "chartRing", Text: "restrict_ring(field_ring(M), «pmChart0»)"},
			{Name: "T", Text: "restrict_ring(field_ring(M), l)"},
			{Name: "Pk", Text: "polynomial_ring(restrict_ring(field_ring(M), k))"},
			{Name: "minimal", Text: "minimal_polynomial(restrict_field(M, K), «pmRationalInK», z)"},
			{Name: "zeroed", Text: "λw:A. COND(w ∈ «chartRing».carrier, ψ(w), «T».zero)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		K, k, l *Expr[Set[A]],
		t, z *Expr[A],
		F *Arrow2[Nat, Nat, A],
		b *Expr[Nat],
		x, y *Expr[A],
		inField, model, equation, lField, kInL, xIn, yIn, root Fact,
	) {
		function := a.TermAs[FieldOps[A]]("restrict_field(M, K)")
		target := a.TermAs[RingOps[A]]("«T»")
		polynomials := a.TermAs[Set[A]]("«pmPolynomialsInK»")
		rational := a.TermAs[Set[A]]("«pmRationalInK»")
		identity := a.TermAs[Fun[A, A]]("λu:A. u")
		zero := a.TermAs[A]("M.zero")
		f := a.TermAs[Fun[Nat, A]]("«f»")
		functionField := a.Have(
			"K is a field under the operations of M",
			"field_on(restrict_field(M, K))",
			By(inField, field.SubfieldFieldOn.Read(M).At(K)))
		data := a.Conjuncts(
			a.Unfolded(model, IntegralPlaneModelDef),
			"K is a regular function field over k",
			"t lies in K",
			"t is transcendental over k",
			"z lies in K",
			"t and z generate K",
			"f is the minimal polynomial of z over k(t)",
			"f is separable",
			"f has positive degree",
			"the weight is positive",
			"the coefficients of f have bounded degree")
		regular, tInK, transcendental, zInK, isMinimal := data[0], data[1], data[2], data[3], data[5]
		kField := a.Have(
			"k is a subfield of K",
			"subfield(restrict_field(M, K), k)",
			By(
				regular,
				function_field.RegularFunctionFieldDef.At(
					function, k, a.TermAs[Set[A]]("restrict_field(M, K).carrier"))))
		algebraic := a.Have(
			"z is algebraic over k(t), K being algebraic over "+
				"the rational functions of any transcendental element",
			"algebraic_over(restrict_field(M, K), «pmRationalInK», z)",
			By(
				regular,
				tInK,
				transcendental,
				zInK,
				rational_function_field.AlgebraicOverAnyTranscendental.Read(functionField).At(k, K, t, z)))
		rationalField := a.Have(
			"k(t) is a subfield of K",
			"subfield(restrict_field(M, K), «pmRationalInK»)",
			By(kField, tInK, algebraic_element.AdjoinElementSubfield.Read(functionField).AsFact().At(k, t)))
		polynomialFacts := a.Conjuncts(
			a.Have(
				"k[t] is a subring of K between k and k(t)",
				"subring(field_ring(restrict_field(M, K)), «pmPolynomialsInK») ∧ "+
					"k ⊆ «pmPolynomialsInK» ∧ "+
					"t ∈ «pmPolynomialsInK» ∧ "+
					"«pmPolynomialsInK» ⊆ «pmRationalInK»",
				By(kField, tInK, algebraic_element.PolynomialImageRing.Read(functionField).AsFact().At(k, t))),
			"k[t] is a subring of K",
			"holding k",
			"and t",
			"inside k(t)")
		polynomialsSubring, kInPolynomials, tInPolynomials, polynomialsInRational :=
			polynomialFacts[0], polynomialFacts[1], polynomialFacts[2], polynomialFacts[3]
		equationData := a.Conjuncts(
			a.Unfolded(equation, AbsolutePlaneEquationDef),
			"F is a polynomial over k[X]",
			"F is monic",
			"F has positive degree",
			"F is absolutely irreducible",
			"F is separable in Z")
		rowsOverK := equationData[0]
		coefficients := a.Have(
			"each coefficient of F is a polynomial over k",
			"∀i:num. polynomial_over(k, F(i))",
			By(
				rowsOverK,
				polynomial.PolynomialOverDef.At(
					a.TermAs[Fun[Nat, A]]("«Pk».zero"), a.TermAs[Set[Fun[Nat, A]]]("«Pk».carrier"), F)))
		minimalOver := a.Have(
			"the minimal polynomial of z over k(t) is f, so it is over k[t]",
			"polynomial_over(restrict_field(M, K).zero, «pmPolynomialsInK», «minimal»)",
			isMinimal.RwRev(),
			By(inField, model, PlaneModelOverPolynomials.Read(M).At(K, k, t, z, f, b)))
		scalarRing := a.Have(
			"k is a ring under the operations of M",
			"comm_ring_on(restrict_ring(field_ring(restrict_field(M, K)), k))",
			By(kField, field.SubfieldCommRing.Read(functionField).AsFact().At(k)))
		targetRing := a.Have(
			"l is a ring under the operations of M",
			"comm_ring_on(«T»)",
			By(lField, field.SubfieldCommRing.Read(M).At(l)))
		inclusion := a.Have(
			"k includes into l",
			"ring_homomorphism(restrict_ring(field_ring(restrict_field(M, K)), k), «T», λu:A. u)",
			Unfold(ring_homomorphism.RingHomomorphism),
			BySets(scalarRing, targetRing, kInL))
		φ, firstLift := a.ObtainAs[Fun[A, A]](
			"the inclusion of k lifts to k[t], sending t to x",
			"∃φ:(A → A). "+
				"    ring_homomorphism(restrict_ring(field_ring(restrict_field(M, K)), «pmPolynomialsInK»), "+
				"        «T», "+
				"        φ) ∧ "+
				"    (∀c:A. c ∈ k ⇒ φ(c) = c) ∧ "+
				"    φ(t) = x",
			By(
				functionField,
				kField,
				field.SubfieldSubring.Read(functionField).AsFact().At(k),
				tInK,
				transcendental,
				inclusion,
				xIn,
				algebraic_element.TranscendentalLift.At(function, target, k, identity, t, x)))
		first := a.Conjuncts(
			firstLift,
			"φ is a ring map on k[t]",
			"φ fixes k",
			"φ sends t to x")
		φMap, φFixes, φAtT := first[0], first[1], first[2]
		polynomialScalars := a.TermAs[RingOps[A]](
			"restrict_ring(field_ring(restrict_field(M, K)), «pmPolynomialsInK»)")
		moved := a.Have(
			"φ moves each coefficient of f to the value of F(i) at x",
			"∀i:num. φ(polynomial_eval(F(i), t)) = polynomial_eval(F(i), x)",
			Derive(func(c *Argument) {
				i := c.FixAs[Nat]("i")
				row := c.TermAs[Fun[Nat, A]]("F(i)")
				fixed := c.Have(
					"φ fixes the coefficients of F(i), which lie in k",
					"(λj:num. φ(F(i, j))) = F(i)",
					Derive(func(d *Argument) {
						d.Do(Funext())
						d.FixAs[Nat]("j")
						d.Show(
							"a coefficient of F(i) lies in k",
							By(
								coefficients.At(i),
								polynomial.PolynomialOverDef.At(zero, k, row),
								φFixes.At(d.TermAs[A]("F(i, j)"))))
					}))
				overPolynomials := c.Have(
					"F(i) is a polynomial over k[t]",
					"polynomial_over(«pmPolynomialsInK», F(i))",
					By(kInPolynomials, coefficients.At(i), polynomial.PolynomialOverMono.At(zero, k, polynomials, row)))
				c.Show(
					"a ring map carries the value at t to the value at its image x",
					By(
						fixed,
						φMap,
						φAtT,
						overPolynomials,
						tInPolynomials,
						polynomial_evaluation.EvalAlongHomomorphism.At(polynomialScalars, target, φ, row, t)))
			}))
		rootMoved := a.Have(
			"y is a root of the minimal polynomial moved along φ",
			"polynomial_eval(λi:num. φ(«minimal»(i)), y) = M.zero",
			Derive(func(c *Argument) {
				pointwise := c.Have(
					"the moved coefficients are the coefficients of the equation at x",
					"(λi:num. φ(«minimal»(i))) = λi:num. polynomial_eval(F(i), x)",
					Derive(func(d *Argument) {
						d.Do(Funext())
						d.FixAs[Nat]("i")
						d.Show(
							"the minimal polynomial is f",
							By(isMinimal, moved))
					}))
				c.Show(
					"which is the equation at (x, y)",
					By(pointwise, root))
			}))
		spec := a.Conjuncts(
			a.Have(
				"the minimal polynomial is monic and vanishes at z, and no "+
					"nonzero polynomial over k(t) vanishing at z has smaller degree",
				"polynomial_monic(restrict_field(M, K).zero, restrict_field(M, K).one, «minimal») ∧ "+
					"polynomial_eval(restrict_field(M, K).add, "+
					"    restrict_field(M, K).zero, "+
					"    restrict_field(M, K).mul, "+
					"    restrict_field(M, K).one, "+
					"    «minimal», "+
					"    z) = "+
					"restrict_field(M, K).zero ∧ "+
					"(∀q:(num → A). "+
					"    polynomial_over(restrict_field(M, K).zero, «pmRationalInK», q) ∧ "+
					"    q ≠ vec_zero(restrict_field(M, K).zero) ∧ "+
					"    polynomial_eval(restrict_field(M, K).add, "+
					"        restrict_field(M, K).zero, "+
					"        restrict_field(M, K).mul, "+
					"        restrict_field(M, K).one, "+
					"        q, "+
					"        z) = "+
					"    restrict_field(M, K).zero ⇒ "+
					"    polynomial_degree(restrict_field(M, K).zero, «minimal») ≤ "+
					"    polynomial_degree(restrict_field(M, K).zero, q))",
				By(
					rationalField,
					algebraic,
					algebraic_element.MinimalPolynomialSpec.Read(functionField).At(
						rational, a.MemberOf[on.Any](z, zInK)))),
			"it is monic",
			"it vanishes at z",
			"it has least degree over k(t)")
		monic, minimalRoot, leastOverRational := spec[0], spec[1], spec[2]
		least := a.Have(
			"so no nonzero polynomial over k[t] vanishing at z has smaller degree, k[t] lying in k(t)",
			Statement{
				Binders: "∀q:(num → A).",
				Hypotheses: []string{
					"polynomial_over(restrict_field(M, K).zero, «pmPolynomialsInK», q)",
					"q ≠ vec_zero(restrict_field(M, K).zero)",
					"polynomial_eval(restrict_field(M, K).add, " +
						"    restrict_field(M, K).zero, " +
						"    restrict_field(M, K).mul, " +
						"    restrict_field(M, K).one, " +
						"    q, " +
						"    z) = " +
						"restrict_field(M, K).zero",
				},
				Conclusion: "polynomial_degree(restrict_field(M, K).zero, «minimal») ≤ " +
					"polynomial_degree(restrict_field(M, K).zero, q)",
			},
			By(leastOverRational, polynomialsInRational, polynomial.PolynomialOverMono))
		ψ, secondLift := a.ObtainAs[Fun[A, A]](
			"φ lifts to k[t][z], sending z to y",
			"∃ψ:(A → A). "+
				"    ring_homomorphism(restrict_ring(field_ring(restrict_field(M, K)), "+
				"            polynomial_image(field_ring(restrict_field(M, K)), «pmPolynomialsInK», z)), "+
				"        «T», "+
				"        ψ) ∧ "+
				"    (∀c:A. c ∈ «pmPolynomialsInK» ⇒ ψ(c) = φ(c)) ∧ "+
				"    ψ(z) = y",
			By(
				functionField,
				polynomialsSubring,
				zInK,
				minimalOver,
				monic,
				minimalRoot,
				least,
				φMap,
				yIn,
				rootMoved,
				algebraic_element.HomomorphismExtendsAtRoot.Read(field.RingOn.Read(functionField)).AsFact().At(
					target, polynomials, φ, a.TermAs[Fun[Nat, A]]("«minimal»"), z, y)))
		second := a.Conjuncts(
			secondLift,
			"ψ is a ring map on k[t][z]",
			"ψ extends φ",
			"ψ sends z to y")
		ψMap, ψExtends, ψAtZ := second[0], second[1], second[2]
		chartIs := a.Have(
			"the chart is k[t][z]",
			"«pmChart0» = polynomial_image(field_ring(restrict_field(M, K)), «pmPolynomialsInK», z)",
			Simp(Fwd(PlaneChartZeroDef), Fwd(field.RestrictFieldRing)),
			Refl())
		chartRing := a.TermAs[RingOps[A]]("«chartRing»")
		inAmbient := a.Simplified(ψMap, Rev(field.RestrictFieldRing), Fwd(module_record.RestrictRingTwice))
		pointMap := a.Have(
			"ψ is a ring map on the chart, restriction from K being restriction from M",
			"ring_homomorphism(«chartRing», «T», ψ)",
			Simp(Fwd(PlaneChartZeroDef)),
			By(inAmbient))
		inChart := a.Conjuncts(
			a.Have(
				"the chart holds k[t] and z",
				"«pmPolynomialsInK» ⊆ «pmChart0» ∧ z ∈ «pmChart0»",
				By(
					chartIs,
					polynomialsSubring,
					zInK,
					algebraic_element.PolynomialImageSubring.Read(functionField).AsFact().At(polynomials, z))),
			"the chart holds k[t]",
			"the chart holds z")
		polynomialsInChart, zInChart := inChart[0], inChart[1]
		kInChart := a.Have(
			"k lies in the chart",
			"k ⊆ «chartRing».carrier",
			BySets(kInPolynomials, polynomialsInChart))
		fixesK := a.Have(
			"ψ fixes k, extending φ",
			"∀c:A. c ∈ k ⇒ ψ(c) = c",
			Derive(func(d *Argument) {
				c := d.FixAs[A]("c")
				inScalars := d.Assume()
				inPolynomials := d.Have(
					"c lies in k[t]",
					"c ∈ «pmPolynomialsInK»",
					BySets(kInPolynomials, inScalars))
				d.Show(
					"ψ extends φ, and φ fixes k",
					By(inPolynomials, inScalars, ψExtends.At(c), φFixes.At(c)))
			}))
		zeroed := a.Conjuncts(
			a.Have(
				"set to zero off the chart, ψ is a point of the chart",
				"«zeroed» ∈ algebra_points(«chartRing», «T», k, λu:A. u) ∧ "+
					"(∀w:A. w ∈ «chartRing».carrier ⇒ «zeroed»(w) = ψ(w))",
				By(
					pointMap,
					kInChart,
					fixesK,
					algebra_points.AlgebraPointsOfRingMap.At(chartRing, target, k, identity, ψ))),
			"it is a point of the chart",
			"it is ψ on the chart")
		point, agreesWithψ := zeroed[0], zeroed[1]
		onChart := a.Have(
			"the chart holds t and z",
			"t ∈ «chartRing».carrier ∧ z ∈ «chartRing».carrier",
			BySets(polynomialsInChart, zInChart, tInPolynomials))
		a.Take(a.TermAs[Fun[A, A]]("«zeroed»"))
		a.Show(
			"it sends t to x and z to y",
			By(
				point,
				onChart,
				agreesWithψ.At(t),
				agreesWithψ.At(z),
				tInPolynomials,
				ψExtends.At(t),
				ψAtZ,
				φAtT))
	}),
})}
