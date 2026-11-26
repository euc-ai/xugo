// canonical.go — the dualizing pair of the Weierstrass curve. Read over
// the line of x, the overlap A₀[1/x] is free over k[x, 1/x] on 1 and y,
// and y*, the coordinate functional of y, generates the dualizing pair ω
// on both charts: chart 0 of ω has the basis y • y*, y* over k[x], dual to
// 1, y, and chart 1 the basis u • y*, y* over k[s]. Multiplication by y*
// is an isomorphism from the structure pair onto ω, so the canonical pair
// is trivial and Riemann–Roch reads ℓ(M) − ℓ(M⁻¹) = deg M. Where the curve
// is smooth, ω should be the module of Kähler differentials and y* the
// invariant differential dx/2y; those two statements are cards.

package elliptic_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/kaehler"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_map"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_line"
	"github.com/euc-ai/xugo/library/proofs/scheme/serre_duality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The functional y*
// ---------------------------------------------------------------------------

// weierstrassDualGeneratorDef — `weierstrass_dual_generator(R, k, x, y)`,
// written y*: on the overlap A₀[1/x], the coefficient of y in the basis 1,
// y over k[x, 1/x]; zero off the overlap.
var weierstrassDualGeneratorDef = weierstrassDualGeneratorDefThm{family.Define(registry.DefEntry{
	Name:     "weierstrassDualGeneratorDef",
	Key:      "prop_5c535f124b33d073",
	Const:    "weierstrass_dual_generator",
	Type:     "ring_ops(A) → set(A) → A → A → A → A",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀x:A. ∀y:A. " +
			"    weierstrass_dual_generator(R, k, x, y) = " +
			"    λz:A. " +
			"        COND(z ∈ ring_away(R, weierstrass_chart_zero(R, k, x, y), x), " +
			"            (εq:A. " +
			"                q ∈ ring_away(R, polynomial_image(R, k, x), x) ∧ " +
			"                (∃p:A. " +
			"                    p ∈ ring_away(R, polynomial_image(R, k, x), x) ∧ " +
			"                    z = R.add(p, R.mul(q, y)))), " +
			"            R.zero)",
	},
	Reading: "The coordinate functional of y, extended by zero. At a Weierstrass datum each " +
		"member of the overlap is p + q·y with p and q in k[x, 1/x] in one way, 1 and y being " +
		"independent over k[x, 1/x] (WeierstrassLaurentCoefficients), so the choice is determined; " +
		"off a datum nothing is said of it. Where 2 ≠ 0 it should be z ↦ Tr(z/2y), the trace of k(x, " +
		"y) over k(x), the invariant differential dx/2y read as a functional; that is not proved here.",
	Deps: []registry.EntryLike{WeierstrassChartZeroDef},
})}

// ---------------------------------------------------------------------------
// The dual bases and the generator of each chart
// ---------------------------------------------------------------------------

// DualGeneratorReads — y* is a vector of the dualizing container that
// reads the coefficient of y, and at y · (p + q·y) the coefficient of one.
// Every member of the overlap is p + q·y in one way
// (WeierstrassOverlapCoordinates), so the ε defining y* picks q, and y* is
// additive and k[x, 1/x]-linear on the overlap and zero off it;
// y · (p + q·y) is q·(x³ + ax + b) + p·y, whose coefficient of y is p.
var DualGeneratorReads = dualGeneratorReadsThm{family.Add(registry.ProofEntry{
	Name: "DualGeneratorReads",
	Key:  "prop_c73e88f204d9e2a1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "«omegaGenerator» ∈ «omegaContainer».carrier ∧ " +
			"(∀p q:A. " +
			"    p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ⇒ " +
			"    «omegaGenerator»(p + q * y) = q ∧ «omegaGenerator»(y * (p + q * y)) = p)",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			chart0, chart1 := arg.TermAs[Set[A]]("«curveChart0»"), arg.TermAs[Set[A]]("«curveChart1»")
			overlap, laurent := arg.TermAs[Set[A]]("«curveOverlap»"), arg.TermAs[Set[A]]("«curveLaurent»")
			generator := arg.TermAs[Fun[A, A]]("«omegaGenerator»")
			fieldOps, fieldModule :=
				arg.TermAs[module_record.RingOps[A]]("field_ring(L)"),
				arg.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			laurentOps := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveLaurent»)")
			through := arg.TermAs[module_record.ModuleOps[A, A]]("«overlapThroughInclusion»")
			laurentVectors := arg.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(L)), «curveLaurent»)")
			ring := field.RingOn.Read(L)

			// The line of x under the curve, and the overlap read in the basis 1, y.
			curve := arg.Have(
				"the datum is a curve over the line of x",
				"«curveOverLine»",
				By(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			line := algebraic_curve.CurveOverItsLine.Read(L).At(k, chart0, chart1, overlap, x)
			coordinates := arg.Conjuncts(
				GroupPremises(datum, WeierstrassOverlapCoordinates.Read(L).At(k, x, y, a, b)),
				"the overlap is k[x, 1/x] · 1 + k[x, 1/x] · y",
				"each of its members so in one way")
			members, unique := coordinates[0], coordinates[1]
			onLaurent := arg.Conjuncts(
				GroupPremises(curve, serre_duality.DualizingModuleOn.Read(L).At(k, chart0, chart1, overlap, x)),
				"k[x, 1/x] is a subring of L",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")
			overlapModule := onLaurent[3]
			laurentRing := arg.Have(
				"k[x, 1/x] is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «curveLaurent»))",
				By(onLaurent[0], comm_ring.SubringRingOn.Read(ring).At(laurent)))
			sets := arg.Conjuncts(
				arg.Have(
					"k[x] lies in k[x, 1/x], which lies in L",
					"«curveKx» ⊆ «curveLaurent» ∧ «curveLaurent» ⊆ L.carrier",
					By(curve, line, comm_ring.SubringSubset.Read(onLaurent[0]))),
				"k[x] lies in k[x, 1/x]",
				"k[x, 1/x] lies in L")
			constants := arg.Have(
				"k and x lie in k[x]",
				"k ⊆ «curveKx» ∧ x ∈ «curveKx»",
				By(curve, line))
			points := arg.Have(
				"x, a and b lie in k[x], and x, y, a and b in L",
				"x ∈ «curveKx» ∧ "+
					"a ∈ «curveKx» ∧ "+
					"b ∈ «curveKx» ∧ "+
					"x ∈ L.carrier ∧ "+
					"y ∈ L.carrier ∧ "+
					"a ∈ L.carrier ∧ "+
					"b ∈ L.carrier",
				BySets(
					constants,
					WeierstrassCoefficientA.Read(datum),
					WeierstrassCoefficientB.Read(datum),
					WeierstrassXInField.Read(datum),
					WeierstrassYInField.Read(datum),
					field.SubfieldSubset.Read(WeierstrassSubfield.Read(datum).AsFact())))

			// y*(p + q·y) = q: the ε of y* chooses a coefficient of y, and the coefficients are unique.
			values := arg.Have(
				"y* reads the coefficient of y",
				"∀p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ⇒ «omegaGenerator»(p + q * y) = q",
				Derive(func(c *Argument) {
					p, q := c.FixAs[A]("p"), c.FixAs[A]("q")
					coefficients := c.Assume()
					constant := c.Have(
						"p is a constant term for the coefficient q",
						"∃d:A. d ∈ «curveLaurent» ∧ p + q * y = d + q * y",
						Derive(func(d *Argument) {
							d.Take(p)
							d.Show(
								"p itself",
								By(coefficients))
						}))
					expansion := c.Have(
						"so q is a coefficient of y in an expansion of p + q·y",
						"∃c:A. c ∈ «curveLaurent» ∧ (∃d:A. d ∈ «curveLaurent» ∧ p + q * y = d + c * y)",
						Derive(func(d *Argument) {
							d.Take(q)
							d.Show(
								"q itself",
								By(coefficients, constant))
						}))
					chosen, choice := c.ObtainChosen(
						"the ε defining y* chooses such a coefficient",
						"∃c:A. c ∈ «curveLaurent» ∧ (∃d:A. d ∈ «curveLaurent» ∧ p + q * y = d + c * y)",
						expansion)
					chosenParts := c.Conjuncts(
						choice,
						"the chosen coefficient lies in k[x, 1/x]",
						"it has an expansion")
					d, chosenExpansion := c.UnpackAs[A](chosenParts[1], "d")
					c.Show(
						"the expansions being unique, the chosen coefficient is q",
						Simp(Fwd(weierstrassDualGeneratorDef)),
						By(members, coefficients, chosenParts[0], chosenExpansion, unique.At(p, q, d, chosen)))
				}))

			// y*(y · (p + q·y)) = y*(q·(x³ + ax + b) + p·y) = p, y² being x³ + ax + b.
			inLaurent := arg.Conjuncts(
				arg.Have(
					"x, a and b lie in k[x, 1/x]",
					"x ∈ «curveLaurent» ∧ a ∈ «curveLaurent» ∧ b ∈ «curveLaurent»",
					BySets(points, sets[0])),
				"x lies in k[x, 1/x]",
				"a lies in k[x, 1/x]",
				"b lies in k[x, 1/x]")
			xm, am, bm :=
				proof.MemberOf(x, inLaurent[0]), proof.MemberOf(a, inLaurent[1]), proof.MemberOf(b, inLaurent[2])
			laurentMul, laurentAdd := comm_ring.MulIn.Read(laurentRing), comm_ring.AddIn.Read(laurentRing)
			cubic := proof.MemberOf(arg.TermAs[A]("x * (x * x) + a * x + b"), arg.Have(
				"x³ + ax + b lies in k[x, 1/x], a ring holding x, a and b",
				"x * (x * x) + a * x + b ∈ «curveLaurent»",
				By(laurentAdd.At(
					laurentAdd.At(laurentMul.At(xm, laurentMul.At(xm, xm)), laurentMul.At(am, xm)), bm))))
			product := arg.Have(
				"y · (p + q·y) = q · (x³ + ax + b) + p · y, y² being x³ + ax + b",
				"∀p q:A. p ∈ L.carrier ∧ q ∈ L.carrier ⇒ y * (p + q * y) = q * (x * (x * x) + a * x + b) + p * y",
				Derive(func(c *Argument) {
					c.FixAs[A]("p")
					q := c.FixAs[A]("q")
					inL := c.Assume()
					c.Show(
						"q times the cubic relation",
						ByArith(ring, inL, points, Scaled(q, WeierstrassEquation.Read(datum))))
				}))
			shifted := arg.Have(
				"the coefficient of y in y · (p + q·y) = q · (x³ + ax + b) + p · y is p",
				"∀p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ⇒ «omegaGenerator»(y * (p + q * y)) = p",
				Derive(func(c *Argument) {
					p, q := c.FixAs[A]("p"), c.FixAs[A]("q")
					coefficients := c.Assume()
					parts := c.Conjuncts(
						coefficients,
						"p lies in k[x, 1/x]",
						"q lies in k[x, 1/x]")
					inL := c.Have(
						"p and q lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(coefficients, sets[1]))
					c.Show(
						"y* reads p there",
						By(
							inL,
							product.At(p, q),
							laurentMul.At(proof.MemberOf(q, parts[1]), cubic),
							parts[0],
							values.At(c.TermAs[A]("q * (x * (x * x) + a * x + b)"), p)))
				}))

			// y* is a vector of the container: k[x, 1/x]-linear on the overlap, zero off it.
			throughModule := arg.Have(
				"the overlap is a module over k[x, 1/x], the field's product acting",
				"module_on(restrict_ring(field_ring(L), «curveLaurent»), «overlapThroughInclusion»)",
				By(
					overlapModule,
					module_record.ScalarRestrictionDef.At(
						arg.TermAs[Fun[A, A]]("λx:A. x"),
						arg.TermAs[module_record.ModuleOps[A, A]](
							"regular_module(restrict_ring(field_ring(L), «curveOverlap»))")),
					module_record.RestrictModuleDef.At(fieldModule, overlap),
					module_record.RegularModuleDef.At(fieldOps)))
			laurentModule := arg.Have(
				"k[x, 1/x] is a module over itself",
				"module_on(restrict_ring(field_ring(L), «curveLaurent»), "+
					"    restrict_module(regular_module(field_ring(L)), «curveLaurent»))",
				By(
					module.RegularModuleOn.Read(laurentRing),
					module_record.RegularModuleDef.At(laurentOps),
					module_record.RestrictModuleDef.At(fieldModule, laurent)))
			intoLaurent := arg.Have(
				"y* takes the overlap into k[x, 1/x]",
				"∀u:A. u ∈ «curveOverlap» ⇒ «omegaGenerator»(u) ∈ «curveLaurent»",
				Derive(func(c *Argument) {
					c.FixAs[A]("u")
					uIn := c.Assume()
					p, q, form := c.Unpack2As[A, A](c.Have(
						"u is p + q·y",
						"∃p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ∧ u = p + q * y",
						By(uIn, members)), "p", "q")
					c.Show(
						"its value is q",
						By(form, values.At(p, q)))
				}))
			additive := arg.Have(
				"y* is additive on the overlap, the coefficients of a sum being the sums of the coefficients",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ «curveOverlap»",
						"v ∈ «curveOverlap»",
					},
					Conclusion: "«omegaGenerator»(u + v) = «omegaGenerator»(u) + «omegaGenerator»(v)",
				},
				Derive(func(c *Argument) {
					c.FixAs[A]("u")
					c.FixAs[A]("v")
					both := c.Conjuncts(
						c.Assume(),
						"u lies in the overlap",
						"v lies in the overlap")
					p, q, uForm := c.Unpack2As[A, A](c.Have(
						"u is p + q·y",
						"∃p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ∧ u = p + q * y",
						By(both[0], members)), "p", "q")
					p1, q1, vForm := c.Unpack2As[A, A](c.Have(
						"v is p₁ + q₁·y",
						"∃p₁ q₁:A. p₁ ∈ «curveLaurent» ∧ q₁ ∈ «curveLaurent» ∧ v = p₁ + q₁ * y",
						By(both[1], members)), "p₁", "q₁")
					uParts := c.Conjuncts(
						uForm,
						"p lies in k[x, 1/x]",
						"q lies in k[x, 1/x]",
						"u = p + q·y")
					vParts := c.Conjuncts(
						vForm,
						"p₁ lies in k[x, 1/x]",
						"q₁ lies in k[x, 1/x]",
						"v = p₁ + q₁·y")
					inL := c.Have(
						"the coefficients lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier ∧ p₁ ∈ L.carrier ∧ q₁ ∈ L.carrier",
						BySets(uParts[0], uParts[1], vParts[0], vParts[1], sets[1]))
					sum := c.Have(
						"(p + q·y) + (p₁ + q₁·y) = (p + p₁) + (q + q₁)·y",
						"(p + q * y) + (p₁ + q₁ * y) = (p + p₁) + (q + q₁) * y",
						ByArith(ring, inL, points))
					constants := laurentAdd.At(proof.MemberOf(p, uParts[0]), proof.MemberOf(p1, vParts[0]))
					coefficients := laurentAdd.At(proof.MemberOf(q, uParts[1]), proof.MemberOf(q1, vParts[1]))
					c.Show(
						"y*(u + v) = q + q₁ = y*(u) + y*(v)",
						By(
							uParts[2],
							vParts[2],
							sum,
							constants,
							coefficients,
							uForm,
							vForm,
							values.At(p, q),
							values.At(p1, q1),
							values.At(c.TermAs[A]("p + p₁"), c.TermAs[A]("q + q₁"))))
				}))
			homogeneous := arg.Have(
				"and k[x, 1/x]-linear, c·(p + q·y) = c·p + (c·q)·y",
				Statement{
					Binders: "∀c u:A.",
					Hypotheses: []string{
						"c ∈ «curveLaurent»",
						"u ∈ «curveOverlap»",
					},
					Conclusion: "«omegaGenerator»(c * u) = c * «omegaGenerator»(u)",
				},
				Derive(func(d *Argument) {
					c := d.FixAs[A]("c")
					d.FixAs[A]("u")
					both := d.Conjuncts(
						d.Assume(),
						"c lies in k[x, 1/x]",
						"u lies in the overlap")
					p, q, uForm := d.Unpack2As[A, A](d.Have(
						"u is p + q·y",
						"∃p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ∧ u = p + q * y",
						By(both[1], members)), "p", "q")
					uParts := d.Conjuncts(
						uForm,
						"p lies in k[x, 1/x]",
						"q lies in k[x, 1/x]",
						"u = p + q·y")
					inL := d.Have(
						"c and the coefficients lie in L",
						"c ∈ L.carrier ∧ p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(both[0], uParts[0], uParts[1], sets[1]))
					scaledSum := d.Have(
						"c · (p + q·y) = c·p + (c·q)·y",
						"c * (p + q * y) = c * p + (c * q) * y",
						ByArith(ring, inL, points))
					cm := proof.MemberOf(c, both[0])
					constant, coefficient :=
						laurentMul.At(cm, proof.MemberOf(p, uParts[0])), laurentMul.At(cm, proof.MemberOf(q, uParts[1]))
					d.Show(
						"y*(c · u) = c · q = c · y*(u)",
						By(
							uParts[2],
							scaledSum,
							constant,
							coefficient,
							uForm,
							values.At(p, q),
							values.At(d.TermAs[A]("c * p"), d.TermAs[A]("c * q"))))
				}))
			vanishes := arg.Have(
				"y* is zero off the overlap",
				"∀u:A. u ∉ «curveOverlap» ⇒ «omegaGenerator»(u) = L.zero",
				Derive(func(c *Argument) {
					c.FixAs[A]("u")
					outside := c.Assume()
					c.Show(
						"off the overlap the definition reads zero",
						Simp(Fwd(weierstrassDualGeneratorDef)),
						By(outside))
				}))
			generatorLinear := arg.Have(
				"so y* is a k[x, 1/x]-linear map from the overlap into k[x, 1/x]",
				"module_homomorphism(restrict_ring(field_ring(L), «curveLaurent»), "+
					"    «overlapThroughInclusion», "+
					"    restrict_module(regular_module(field_ring(L)), «curveLaurent»), "+
					"    «omegaGenerator»)",
				By(
					throughModule,
					laurentModule,
					intoLaurent,
					additive,
					homogeneous,
					module_homomorphism.ModuleHomomorphismDef.At(laurentOps, through, laurentVectors, generator)))
			generatorMap := arg.Have(
				"so y* is one of the container's maps",
				"«omegaGenerator» ∈ «omegaMaps»",
				By(
					generatorLinear,
					vanishes,
					hom_module.InHomSet.At(laurentOps, through, laurentVectors, generator)))
			carrier := arg.Have(
				"the container's vectors are the k[x, 1/x]-linear "+
					"maps from the overlap into k[x, 1/x], zero off it",
				"«omegaContainer».carrier = «omegaMaps»",
				Simp(Fwd(serre_duality.CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
				Basic())
			readsBoth := arg.Have(
				"so at p + q·y, y* reads q and at y · (p + q·y) it reads p",
				Statement{
					Binders: "∀p q:A.",
					Hypotheses: []string{
						"p ∈ «curveLaurent»",
						"q ∈ «curveLaurent»",
					},
					Conclusion: "«omegaGenerator»(p + q * y) = q ∧ «omegaGenerator»(y * (p + q * y)) = p",
				},
				Derive(func(c *Argument) {
					p, q := c.FixAs[A]("p"), c.FixAs[A]("q")
					coefficients := c.Assume()
					c.Show(
						"the two readings",
						By(coefficients, values.At(p, q), shifted.At(p, q)))
				}))
			arg.Show(
				"y* is a vector of the container reading the coefficient "+
					"of y, and at y · (p + q·y) the coefficient of one",
				carrier.Rw(),
				By(generatorMap, readsBoth))
		}),
})}

// DualGeneratorZero — chart 0 of ω is generated over A₀ by y*: it is the
// image of A₀ under r ↦ r • y*. Chart 0 of ω is a submodule over A₀
// (DualizingIsLattice) holding y*, which carries A₀ into k[x], so it holds
// every r • y*. A map φ of it takes one and y into k[x], so
// r = φ(y) + φ(1)·y lies in A₀, and r • y* reads y*(r · 1) = φ(1) at one
// and y*(r · y) = φ(y) at y: it agrees with φ on the basis 1, y of the
// overlap (BasisSpansOverlap), so it is φ (ContainerMapsAgreeOnBasis).
var DualGeneratorZero = dualGeneratorZeroThm{family.Add(registry.ProofEntry{
	Name: "DualGeneratorZero",
	Key:  "prop_d4dec8e7a3e6957",
	Reading: "Chart 0 of ω is free of rank one over A₀, on y*: the " +
		"curve is Gorenstein at every point of chart 0, singular or not.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "«omegaChart0» = " +
			"{«omegaContainer».smul(r, «omegaGenerator») | r:A | r ∈ «curveChart0»}",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			chart0, chart1 := arg.TermAs[Set[A]]("«curveChart0»"), arg.TermAs[Set[A]]("«curveChart1»")
			overlap, polynomials := arg.TermAs[Set[A]]("«curveOverlap»"), arg.TermAs[Set[A]]("«curveKx»")
			one, pair, single :=
				arg.TermAs[A]("L.one"), arg.TermAs[Set[A]]("{L.one, y}"), arg.TermAs[Set[A]]("{y}")
			generator := arg.TermAs[Fun[A, A]]("«omegaGenerator»")
			scaled := arg.TermAs[Fun[A, Fun[A, A]]]("«omegaScaled»")
			fieldOps := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			ring := field.RingOn.Read(L)
			ym := arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())

			reads := arg.Conjuncts(
				GroupPremises(datum, DualGeneratorReads.Read(L).At(k, x, y, a, b)),
				"y* is a vector of the container",
				"y* reads the coefficient of y, and at y · (p + q·y) the coefficient of one")
			generatorIn, values := reads[0], reads[1]
			curve := arg.Have(
				"the datum is a curve over the line of x",
				"«curveOverLine»",
				By(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			line := algebraic_curve.CurveOverItsLine.Read(L).At(k, chart0, chart1, overlap, x)
			containerModule := arg.Conjuncts(
				GroupPremises(curve, serre_duality.DualizingModuleOn.Read(L).At(k, chart0, chart1, overlap, x)),
				"k[x, 1/x] is a ring",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")[4]
			sets := arg.Conjuncts(
				arg.Have(
					"k[x] lies in k[x, 1/x], chart 0 in the overlap, and k[x, 1/x] in L",
					"«curveKx» ⊆ «curveLaurent» ∧ «curveChart0» ⊆ «curveOverlap» ∧ «curveLaurent» ⊆ L.carrier",
					By(curve, line, comm_ring.SubringSubset.At(fieldOps, arg.TermAs[Set[A]]("«curveLaurent»")))),
				"k[x] lies in k[x, 1/x]",
				"chart 0 lies in the overlap",
				"k[x, 1/x] lies in L")
			chartBasis := arg.Conjuncts(
				GroupPremises(datum, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
				"chart 0 is a subring of L",
				"k[x] lies in chart 0",
				"1 and y are a basis of chart 0 over k[x]",
				"one is not y")[2]
			chartParts := arg.Conjuncts(
				arg.Unfolded(chartBasis, linear_independence.ModuleBasisDef),
				"1 and y are independent over k[x]",
				"they span chart 0")
			inChart := arg.Conjuncts(
				arg.Have(
					"1 and y, being independent in chart 0, lie in it, and so in the overlap",
					"L.one ∈ «curveChart0» ∧ y ∈ «curveChart0» ∧ L.one ∈ «curveOverlap» ∧ y ∈ «curveOverlap»",
					By(
						arg.Simplified(
							linear_independence.IndependentInCarrier.Read(chartParts[0]),
							Fwd(set_order.InsertSubset),
							Fwd(set_order.EmptySubset)),
						sets[1],
						set_basic.SubsetDef.At(chart0, overlap))),
				"1 lies in chart 0",
				"y lies in chart 0",
				"1 lies in the overlap",
				"y lies in the overlap")
			overlapBasis := arg.Have(
				"1 and y are a basis of the overlap over k[x, 1/x]",
				"module_basis(restrict_ring(field_ring(L), «curveLaurent»), "+
					"    restrict_module(regular_module(field_ring(L)), «curveOverlap»), "+
					"    {L.one, y})",
				By(curve, chartBasis, algebraic_curve.BasisSpansOverlap.Read(L).At(k, chart0, chart1, overlap, x)))

			// For r = p + q·y, y* reads q at r · 1 and p at r · y.
			evaluations := arg.Have(
				"for r = p + q·y, y*(r · 1) = q and y*(r · y) = p",
				Statement{
					Binders: "∀p q:A.",
					Hypotheses: []string{
						"p ∈ «curveLaurent»",
						"q ∈ «curveLaurent»",
					},
					Conclusion: "«omegaGenerator»((p + q * y) * L.one) = q ∧ «omegaGenerator»((p + q * y) * y) = p",
				},
				Derive(func(c *Argument) {
					p, q := c.FixAs[A]("p"), c.FixAs[A]("q")
					coefficients := c.Assume()
					inL := c.Have(
						"p and q lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(coefficients, sets[2]))
					unit := c.Have(
						"(p + q·y) · 1 = p + q·y",
						"(p + q * y) * L.one = p + q * y",
						ByArith(ring, inL, ym))
					swap := c.Have(
						"(p + q·y) · y = y · (p + q·y)",
						"(p + q * y) * y = y * (p + q * y)",
						ByArith(ring, inL, ym))
					atOne := c.Have(
						"so y* reads q at (p + q·y) · 1",
						"«omegaGenerator»((p + q * y) * L.one) = q",
						unit.Rw(),
						By(coefficients, values.At(p, q)))
					atY := c.Have(
						"and p at (p + q·y) · y = y · (p + q·y)",
						"«omegaGenerator»((p + q * y) * y) = p",
						swap.Rw(),
						By(coefficients, values.At(p, q)))
					c.Show(
						"y* reads q at (p + q·y) · 1 and p at (p + q·y) · y",
						By(atOne, atY))
				}))

			// Chart 0 of ω is the maps carrying chart 0 into k[x], a submodule over chart 0 holding y*.
			onChart := arg.Have(
				"y* carries chart 0 into k[x]: it reads the coefficient of y",
				"∀r:A. r ∈ «curveChart0» ⇒ «omegaGenerator»(r) ∈ «curveKx»",
				Derive(func(c *Argument) {
					r := c.FixAs[A]("r")
					rIn := c.Assume()
					p, q, form := c.Unpack2As[A, A](c.Have(
						"r is p + q·y with p and q in k[x]",
						"∃p q:A. p ∈ «curveKx» ∧ q ∈ «curveKx» ∧ r = p + q * y",
						By(rIn, WeierstrassChartZeroMembers.At(fieldOps, k, x, y, r))), "p", "q")
					inK := c.Have(
						"p and q lie in k[x, 1/x]",
						"p ∈ «curveLaurent» ∧ q ∈ «curveLaurent»",
						BySets(form, sets[0]))
					c.Show(
						"so y*(r) = q lies in k[x]",
						By(form, inK, values.At(p, q)))
				}))
			omegaChart := arg.Have(
				"chart 0 of ω is the maps of the container carrying chart 0 into k[x], chart 0 of O(−2)",
				"«omegaChart0» = {φ:A → A | φ ∈ «omegaMaps» ∧ image(φ, «curveChart0») ⊆ «curveKx»}",
				Simp(
					Fwd(serre_duality.CurveDualizingPairDef),
					Fwd(pairs.Fst),
					Fwd(projective_line.ProjectiveLinePairDef),
					Fwd(serre_duality.CurveDualizingModuleDef),
					Fwd(hom_module.CoextendScalarsDef)),
				Basic())
			omegaIff := arg.Have(
				"so a map lies in chart 0 of ω exactly when it is "+
					"a map of the container carrying chart 0 into k[x]",
				"∀φ:(A → A). φ ∈ «omegaChart0» ⇔ φ ∈ «omegaMaps» ∧ image(φ, «curveChart0») ⊆ «curveKx»",
				BySets(omegaChart))
			generatorInOmega := arg.Have(
				"so y* lies in chart 0 of ω",
				"«omegaGenerator» ∈ «omegaChart0»",
				By(
					generatorIn,
					onChart,
					set_image.ImageSubsetIff.At(generator, chart0, polynomials),
					omegaIff.At(generator)))
			lattice := arg.Have(
				"ω is a lattice pair over the overlap",
				"lattice_pair(restrict_ring(field_ring(L), «curveOverlap»), "+
					"    «curveChart0», "+
					"    «curveChart1», "+
					"    «omegaContainer», "+
					"    curve_dualizing_pair(L, k, x, «curveChart0», «curveChart1», «curveOverlap»))",
				By(curve, serre_duality.DualizingIsLattice.Read(L).At(k, chart0, chart1, overlap, x)))
			overChart := arg.Have(
				"chart 0 of ω is a submodule over chart 0",
				"submodule(restrict_ring(restrict_ring(field_ring(L), «curveOverlap»), «curveChart0»), "+
					"    «omegaContainer», "+
					"    «omegaChart0»)",
				By(arg.Unfolded(lattice, lattice_pair.LatticePairDef)))

			// Every r • y* with r in chart 0 lies in chart 0 of ω, and every member of chart 0 of ω is one.
			generatorMember := proof.MemberOf(generator, generatorIn)
			intoOmega := arg.Have(
				"r • y* lies in chart 0 of ω, a submodule over chart 0 holding y*",
				Statement{
					Binders: "∀r:A.",
					Hypotheses: []string{
						"r ∈ «curveChart0»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero)) ∈ «omegaChart0»",
				},
				Derive(func(c *Argument) {
					r := c.FixAs[A]("r")
					rIn := c.Assume()
					c.Show(
						"chart 0 of ω is closed under chart 0's action",
						By(submodule.SubmoduleSmul.Read(overChart).At(
							proof.MemberOf(r, rIn), proof.MemberOf(generator, generatorInOmega))))
				}))
			fromOmega := arg.Have(
				"every φ of chart 0 of ω is r • y* for r = φ(y) + φ(1) · y in chart 0",
				"∀φ:(A → A). φ ∈ «omegaChart0» ⇒ φ ∈ image(«omegaScaled», «curveChart0»)",
				Derive(func(c *Argument) {
					φ := c.FixAs[Fun[A, A]]("φ")
					φIn := c.Assume()
					parts := c.Conjuncts(
						c.Have(
							"φ is a map of the container carrying chart 0 into k[x]",
							"φ ∈ «omegaMaps» ∧ image(φ, «curveChart0») ⊆ «curveKx»",
							By(φIn, omegaIff.At(φ))),
						"φ is a map of the container",
						"φ carries chart 0 into k[x]")
					atBasis := c.Have(
						"φ(1) and φ(y) lie in k[x]",
						"φ(L.one) ∈ «curveKx» ∧ φ(y) ∈ «curveKx»",
						By(parts[1], inChart[0], inChart[1], set_image.ImageSubsetIff.At(φ, chart0, polynomials)))
					r := c.TermAs[A]("φ(y) + φ(L.one) * y")
					expansion := c.Have(
						"r = φ(y) + φ(1) · y has its coefficients in k[x]",
						"∃p q:A. p ∈ «curveKx» ∧ q ∈ «curveKx» ∧ φ(y) + φ(L.one) * y = p + q * y",
						Derive(func(d *Argument) {
							d.Take(d.TermAs[A]("φ(y)"))
							d.Take(d.TermAs[A]("φ(L.one)"))
							d.Show(
								"φ(y) and φ(1) are they",
								By(atBasis))
						}))
					rIn := c.Have(
						"so r lies in chart 0",
						"φ(y) + φ(L.one) * y ∈ «curveChart0»",
						By(expansion, WeierstrassChartZeroMembers.At(fieldOps, k, x, y, r)))
					rOverlap := c.Have(
						"and in the overlap",
						"φ(y) + φ(L.one) * y ∈ «curveOverlap»",
						BySets(rIn, sets[1]))
					inK := c.Have(
						"φ(y) and φ(1) lie in k[x, 1/x]",
						"φ(y) ∈ «curveLaurent» ∧ φ(L.one) ∈ «curveLaurent»",
						BySets(atBasis, sets[0]))
					scaledR := c.TermAs[Fun[A, A]](
						"λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((φ(y) + φ(L.one) * y) * z), L.zero)")
					agree := c.Have(
						"r • y* and φ agree on 1 and y: y* reads φ(1) in r · 1 and φ(y) in r · y",
						Statement{
							Binders: "∀e:A.",
							Hypotheses: []string{
								"e ∈ {L.one, y}",
							},
							Conclusion: "(λz:A. " +
								"    COND(z ∈ «curveOverlap», «omegaGenerator»((φ(y) + φ(L.one) * y) * z), L.zero))(e) = " +
								"φ(e)",
						},
						Simp(Fwd(set_basic.ForallInInsert), Fwd(set_basic.NotInEmpty)),
						By(inK, inChart[2], inChart[3], evaluations.At(c.TermAs[A]("φ(y)"), c.TermAs[A]("φ(L.one)"))))
					scaledVector := c.Have(
						"r • y* is a vector of the container",
						"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((φ(y) + φ(L.one) * y) * z), L.zero)) ∈ "+
							"«omegaContainer».carrier",
						By(module.SmulIn.Read(containerModule).At(proof.MemberOf(r, rOverlap), generatorMember)))
					same := c.Have(
						"so r • y* is φ, the two agreeing on the basis 1, y of the overlap",
						"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((φ(y) + φ(L.one) * y) * z), L.zero)) = φ",
						By(
							curve,
							finite_set.FiniteSing.At(y),
							finite_set.FiniteInsert.At(one, single),
							overlapBasis,
							scaledVector,
							parts[0],
							agree,
							serre_duality.ContainerMapsAgreeOnBasis.Read(L).At(
								k, chart0, chart1, overlap, x, pair, scaledR, φ)))
					witnessed := c.Have(
						"so φ is s • y* for an s of chart 0, namely r",
						"∃s:A. φ = (λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(s * z), L.zero)) ∧ s ∈ «curveChart0»",
						Derive(func(d *Argument) {
							d.Take(r)
							d.Show(
								"r is one",
								By(same, rIn))
						}))
					c.Show(
						"so φ is the image of r",
						By(witnessed, set_basic.InImage.At(scaled, chart0, φ)))
				}))
			imageSet, omega :=
				arg.TermAs[Set[Fun[A, A]]]("image(«omegaScaled», «curveChart0»)"),
				arg.TermAs[Set[Fun[A, A]]]("«omegaChart0»")
			onto := arg.Have(
				"so r ↦ r • y* maps chart 0 onto chart 0 of ω",
				"image(«omegaScaled», «curveChart0») = «omegaChart0»",
				By(
					intoOmega,
					set_image.ImageSubsetIff.At(scaled, chart0, omega),
					fromOmega,
					set_basic.SubsetDef.At(omega, imageSet),
					set_order.SubsetAntisym.At(imageSet, omega)))
			acting := arg.Have(
				"the overlap acts on y* through the argument",
				"∀r:A. "+
					"    «omegaContainer».smul(r, «omegaGenerator») = "+
					"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero)",
				Simp(Fwd(serre_duality.CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
				Basic())
			arg.Show(
				"so chart 0 of ω is the image of chart 0 under r ↦ r • y*",
				Simp(Fwd(acting)),
				By(onto, set_image.SimpleImage))
		}),
})}

// DualBasisZero — y* lies in the dualizing container and reads the
// coefficient of y, y • y* reads the coefficient of one, and the two are
// a basis of chart 0 of ω over k[x]: the dual basis of 1, y. The readings
// are DualGeneratorReads'. r ↦ r • y* is k[x]-linear on chart 0,
// one-to-one there, r being y*(r · y) + y*(r · 1) · y, and onto chart 0
// of ω (DualGeneratorZero), so it carries the basis 1, y of chart 0
// (WeierstrassBasisZero) to a basis, y* and y • y*.
var DualBasisZero = dualBasisZeroThm{family.Add(registry.ProofEntry{
	Name: "DualBasisZero",
	Key:  "prop_856b3b45f653aafa",
	Reading: "{y • y*, y*} is the basis of chart 0 of ω dual to the basis 1, y " +
		"of chart 0: y* is the coordinate functional of y, and y • y* that of one.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "«omegaGenerator» ∈ «omegaContainer».carrier ∧ " +
			"(∀p q:A. " +
			"    p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ⇒ " +
			"    «omegaGenerator»(p + q * y) = q ∧ " +
			"    «omegaContainer».smul(y, «omegaGenerator»)(p + q * y) = p) ∧ " +
			"module_basis(restrict_ring(field_ring(L), «curveKx»), " +
			"    restrict_module(«omegaContainer», «omegaChart0»), " +
			"    {«omegaContainer».smul(y, «omegaGenerator»), «omegaGenerator»})",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			chart0, chart1 := arg.TermAs[Set[A]]("«curveChart0»"), arg.TermAs[Set[A]]("«curveChart1»")
			overlap, polynomials := arg.TermAs[Set[A]]("«curveOverlap»"), arg.TermAs[Set[A]]("«curveKx»")
			pair := arg.TermAs[Set[A]]("{L.one, y}")
			generator := arg.TermAs[Fun[A, A]]("«omegaGenerator»")
			scaled := arg.TermAs[Fun[A, Fun[A, A]]]("«omegaScaled»")
			fieldOps := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			overlapOps, chart0Ops :=
				arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveOverlap»)"),
				arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveChart0»)")
			polynomialOps := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveKx»)")
			chartVectors := arg.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(L)), «curveChart0»)")
			container := arg.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«omegaContainer»")
			ring := field.RingOn.Read(L)
			ym := arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())

			reads := arg.Conjuncts(
				GroupPremises(datum, DualGeneratorReads.Read(L).At(k, x, y, a, b)),
				"y* is a vector of the container",
				"y* reads the coefficient of y, and at y · (p + q·y) the coefficient of one")
			generatorIn, values := reads[0], reads[1]
			generatorMember := proof.MemberOf(generator, generatorIn)
			curve := arg.Have(
				"the datum is a curve over the line of x",
				"«curveOverLine»",
				By(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			line := algebraic_curve.CurveOverItsLine.Read(L).At(k, chart0, chart1, overlap, x)
			onLaurent := arg.Conjuncts(
				GroupPremises(curve, serre_duality.DualizingModuleOn.Read(L).At(k, chart0, chart1, overlap, x)),
				"k[x, 1/x] is a ring",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")
			containerModule := onLaurent[4]
			chart := arg.Conjuncts(
				GroupPremises(datum, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
				"chart 0 is a subring of L",
				"k[x] lies in chart 0",
				"1 and y are a basis of chart 0 over k[x]",
				"one is not y")
			polynomialsIn0, chartBasis := chart[1], chart[2]
			chartRing := arg.Have(
				"chart 0 is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveChart0»))",
				By(chart[0], comm_ring.SubringRingOn.Read(ring).At(chart0)))
			sets := arg.Conjuncts(
				arg.Have(
					"the sets in play, one inside the next",
					"«curveKx» ⊆ «curveLaurent» ∧ "+
						"«curveChart0» ⊆ «curveOverlap» ∧ "+
						"«curveLaurent» ⊆ L.carrier ∧ "+
						"subring(field_ring(L), «curveKx»)",
					By(curve, line, comm_ring.SubringSubset.At(fieldOps, arg.TermAs[Set[A]]("«curveLaurent»")))),
				"k[x] lies in k[x, 1/x]",
				"chart 0 lies in the overlap",
				"k[x, 1/x] lies in L",
				"k[x] is a subring of L")
			chartParts := arg.Conjuncts(
				arg.Unfolded(chartBasis, linear_independence.ModuleBasisDef),
				"1 and y are independent over k[x]",
				"they span chart 0")
			inChart := arg.Conjuncts(
				arg.Have(
					"1 and y, being independent in chart 0, lie in it, and so in the overlap",
					"L.one ∈ «curveChart0» ∧ y ∈ «curveChart0» ∧ L.one ∈ «curveOverlap» ∧ y ∈ «curveOverlap»",
					By(
						arg.Simplified(
							linear_independence.IndependentInCarrier.Read(chartParts[0]),
							Fwd(set_order.InsertSubset),
							Fwd(set_order.EmptySubset)),
						sets[1],
						set_basic.SubsetDef.At(chart0, overlap))),
				"1 lies in chart 0",
				"y lies in chart 0",
				"1 lies in the overlap",
				"y lies in the overlap")
			polynomialsInOverlap := arg.Have(
				"k[x] lies in the overlap",
				"«curveKx» ⊆ «curveOverlap»",
				BySets(polynomialsIn0, sets[1]))
			overlapRing := arg.Have(
				"the overlap is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveOverlap»))",
				By(curve, line, comm_ring.SubringRingOn.Read(ring).At(overlap)))
			polynomialsRing := arg.Have(
				"k[x] is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveKx»))",
				By(sets[3], comm_ring.SubringRingOn.Read(ring).At(polynomials)))
			subringOf0 := arg.Have(
				"so k[x], lying in chart 0, is a subring of it",
				"subring(restrict_ring(field_ring(L), «curveChart0»), «curveKx»)",
				By(
					polynomialsRing,
					polynomialsIn0,
					comm_ring.SubringRingOn.Read(chartRing).At(polynomials),
					module_record.RestrictRingTwice.At(fieldOps, chart0, polynomials)))
			subringOfOverlap := arg.Have(
				"and, lying in the overlap, a subring of the overlap",
				"subring(restrict_ring(field_ring(L), «curveOverlap»), «curveKx»)",
				By(
					polynomialsRing,
					polynomialsInOverlap,
					comm_ring.SubringRingOn.Read(overlapRing).At(polynomials),
					module_record.RestrictRingTwice.At(fieldOps, overlap, polynomials)))
			members := arg.Conjuncts(
				GroupPremises(datum, WeierstrassOverlapCoordinates.Read(L).At(k, x, y, a, b)),
				"the overlap is k[x, 1/x] · 1 + k[x, 1/x] · y",
				"each of its members so in one way")[0]
			evaluations := arg.Have(
				"for r = p + q·y, y*(r · 1) = q and y*(r · y) = p",
				Statement{
					Binders: "∀p q:A.",
					Hypotheses: []string{
						"p ∈ «curveLaurent»",
						"q ∈ «curveLaurent»",
					},
					Conclusion: "«omegaGenerator»((p + q * y) * L.one) = q ∧ «omegaGenerator»((p + q * y) * y) = p",
				},
				Derive(func(c *Argument) {
					p, q := c.FixAs[A]("p"), c.FixAs[A]("q")
					coefficients := c.Assume()
					inL := c.Have(
						"p and q lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(coefficients, sets[2]))
					unit := c.Have(
						"(p + q·y) · 1 = p + q·y",
						"(p + q * y) * L.one = p + q * y",
						ByArith(ring, inL, ym))
					swap := c.Have(
						"(p + q·y) · y = y · (p + q·y)",
						"(p + q * y) * y = y * (p + q * y)",
						ByArith(ring, inL, ym))
					atOne := c.Have(
						"so y* reads q at (p + q·y) · 1",
						"«omegaGenerator»((p + q * y) * L.one) = q",
						unit.Rw(),
						By(coefficients, values.At(p, q)))
					atY := c.Have(
						"and p at (p + q·y) · y = y · (p + q·y)",
						"«omegaGenerator»((p + q * y) * y) = p",
						swap.Rw(),
						By(coefficients, values.At(p, q)))
					c.Show(
						"y* reads q at (p + q·y) · 1 and p at (p + q·y) · y",
						By(atOne, atY))
				}))

			// r ↦ r • y* is a k[x]-linear map from chart 0 into the container.
			chartModule := arg.Have(
				"chart 0 is a module over k[x], a ring inside it",
				"module_on(restrict_ring(field_ring(L), «curveKx»), "+
					"    restrict_module(regular_module(field_ring(L)), «curveChart0»))",
				Simp(Fwd(module_record.RestrictModuleDef)),
				By(
					subringOf0,
					module.RegularModuleOverSubring.Read(chartRing).At(polynomials),
					module_record.RestrictRingDef.At(chart0Ops, polynomials),
					module_record.RestrictRingDef.At(fieldOps, polynomials),
					module_record.RegularModuleDef.At(chart0Ops)))
			containerOverPolynomials := arg.Have(
				"the container is a module over k[x], which lies in the overlap",
				"module_on(restrict_ring(field_ring(L), «curveKx»), «omegaContainer»)",
				By(
					subringOfOverlap,
					module.ModuleRestrictScalars.Read(containerModule).At(polynomials),
					module_record.RestrictRingDef.At(overlapOps, polynomials),
					module_record.RestrictRingDef.At(fieldOps, polynomials)))
			scaledIn := arg.Have(
				"r • y* is a map of the container",
				Statement{
					Binders: "∀r:A.",
					Hypotheses: []string{
						"r ∈ «curveChart0»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero)) ∈ «omegaMaps»",
				},
				Derive(func(c *Argument) {
					r := c.FixAs[A]("r")
					rIn := c.Assume()
					rO := c.Have(
						"r lies in the overlap",
						"r ∈ «curveOverlap»",
						BySets(rIn, sets[1]))
					c.Show(
						"the container is closed under the overlap's action",
						By(module.SmulIn.Read(containerModule).At(proof.MemberOf(r, rO), generatorMember)))
				}))
			scaledAdd := arg.Have(
				"(r + s) • y* = r • y* + s • y*",
				Statement{
					Binders: "∀r s:A.",
					Hypotheses: []string{
						"r ∈ «curveChart0»",
						"s ∈ «curveChart0»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((r + s) * z), L.zero)) = " +
						"fun_add(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero), " +
						"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(s * z), L.zero))",
				},
				Derive(func(c *Argument) {
					r, s := c.FixAs[A]("r"), c.FixAs[A]("s")
					both := c.Conjuncts(
						c.Assume(),
						"r lies in chart 0",
						"s lies in chart 0")
					inOverlap := c.Conjuncts(
						c.Have(
							"r and s lie in the overlap",
							"r ∈ «curveOverlap» ∧ s ∈ «curveOverlap»",
							BySets(both[0], both[1], sets[1])),
						"r lies in the overlap",
						"s lies in the overlap")
					c.Show(
						"the action distributes over the overlap's sum",
						By(module.SmulAddRight.Read(containerModule).At(
							proof.MemberOf(r, inOverlap[0]), proof.MemberOf(s, inOverlap[1]), generatorMember)))
				}))
			scaledMul := arg.Have(
				"(c · r) • y* = c • (r • y*)",
				Statement{
					Binders: "∀c r:A.",
					Hypotheses: []string{
						"c ∈ «curveKx»",
						"r ∈ «curveChart0»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(c * r * z), L.zero)) = " +
						"λz:A. " +
						"    COND(z ∈ «curveOverlap», " +
						"        COND(c * z ∈ «curveOverlap», «omegaGenerator»(r * (c * z)), L.zero), " +
						"        L.zero)",
				},
				Derive(func(d *Argument) {
					c, r := d.FixAs[A]("c"), d.FixAs[A]("r")
					both := d.Conjuncts(
						d.Assume(),
						"c lies in k[x]",
						"r lies in chart 0")
					inOverlap := d.Conjuncts(
						d.Have(
							"c and r lie in the overlap",
							"c ∈ «curveOverlap» ∧ r ∈ «curveOverlap»",
							BySets(both[0], both[1], polynomialsInOverlap, sets[1])),
						"c lies in the overlap",
						"r lies in the overlap")
					d.Show(
						"the action is associative",
						By(module.SmulMul.Read(containerModule).At(
							proof.MemberOf(c, inOverlap[0]), proof.MemberOf(r, inOverlap[1]), generatorMember)))
				}))
			homomorphism := arg.Have(
				"so r ↦ r • y* is k[x]-linear from chart 0 into the container",
				"module_homomorphism(restrict_ring(field_ring(L), «curveKx»), "+
					"    restrict_module(regular_module(field_ring(L)), «curveChart0»), "+
					"    «omegaContainer», "+
					"    «omegaScaled»)",
				By(
					chartModule,
					containerOverPolynomials,
					scaledIn,
					scaledAdd,
					scaledMul,
					module_homomorphism.ModuleHomomorphismDef.At(polynomialOps, chartVectors, container, scaled)))

			// One-to-one on chart 0: r is read back off r • y* at y and at one.
			reconstruct := arg.Have(
				"a member r of chart 0 is y*(r · y) + y*(r · 1) · y, read off r • y* at y and at one",
				"∀r:A. r ∈ «curveChart0» ⇒ r = «omegaGenerator»(r * y) + «omegaGenerator»(r * L.one) * y",
				Derive(func(c *Argument) {
					r := c.FixAs[A]("r")
					rIn := c.Assume()
					p, q, form := c.Unpack2As[A, A](c.Have(
						"r is p + q·y with p and q in k[x]",
						"∃p q:A. p ∈ «curveKx» ∧ q ∈ «curveKx» ∧ r = p + q * y",
						By(rIn, WeierstrassChartZeroMembers.At(fieldOps, k, x, y, r))), "p", "q")
					inK := c.Have(
						"p and q lie in k[x, 1/x]",
						"p ∈ «curveLaurent» ∧ q ∈ «curveLaurent»",
						BySets(form, sets[0]))
					c.Show(
						"y*(r · y) = p and y*(r · 1) = q",
						By(form, inK, evaluations.At(p, q)))
				}))
			injective := arg.Have(
				"so r ↦ r • y* is one-to-one on chart 0",
				"injective_on(«curveChart0», «omegaScaled»)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(c *Argument) {
					r, s := c.FixAs[A]("r"), c.FixAs[A]("s")
					parts := c.Conjuncts(
						c.Assume(),
						"r lies in chart 0",
						"s lies in chart 0",
						"r • y* = s • y*")
					atY := c.Have(
						"so r • y* and s • y* agree at y",
						"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero))(y) = "+
							"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(s * z), L.zero))(y)",
						parts[2].Rw(),
						Basic())
					atOne := c.Have(
						"and at one",
						"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero))(L.one) = "+
							"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(s * z), L.zero))(L.one)",
						parts[2].Rw(),
						Basic())
					readY := c.Have(
						"so y*(r · y) = y*(s · y), y lying in the overlap",
						"«omegaGenerator»(r * y) = «omegaGenerator»(s * y)",
						By(atY, inChart[3]))
					readOne := c.Have(
						"and y*(r · 1) = y*(s · 1), one lying in the overlap",
						"«omegaGenerator»(r * L.one) = «omegaGenerator»(s * L.one)",
						By(atOne, inChart[2]))
					c.Show(
						"r and s are read off the one map",
						CalcEq(
							Leg(
								c.TermAs[A]("«omegaGenerator»(r * y) + «omegaGenerator»(r * L.one) * y"),
								"r is read off r • y*",
								By(reconstruct.At(r), parts[0])),
							FinalLeg(
								"which reads off s • y* as s",
								readY.Rw(),
								readOne.Rw(),
								By(reconstruct.At(s), parts[1]))))
				}))
			onto := arg.Have(
				"and it maps chart 0 onto chart 0 of ω",
				"image(«omegaScaled», «curveChart0») = «omegaChart0»",
				GroupPremises(datum, DualGeneratorZero.Read(L).At(k, x, y, a, b)).Rw(),
				By(set_image.SimpleImage))

			// The images y* and y • y* of the basis 1, y are a basis of chart 0 of ω.
			lattice := arg.Have(
				"ω is a lattice pair over the overlap",
				"lattice_pair(restrict_ring(field_ring(L), «curveOverlap»), "+
					"    «curveChart0», "+
					"    «curveChart1», "+
					"    «omegaContainer», "+
					"    curve_dualizing_pair(L, k, x, «curveChart0», «curveChart1», «curveOverlap»))",
				By(curve, serre_duality.DualizingIsLattice.Read(L).At(k, chart0, chart1, overlap, x)))
			overChart := arg.Have(
				"chart 0 of ω is a submodule over chart 0",
				"submodule(restrict_ring(restrict_ring(field_ring(L), «curveOverlap»), «curveChart0»), "+
					"    «omegaContainer», "+
					"    «omegaChart0»)",
				By(arg.Unfolded(lattice, lattice_pair.LatticePairDef)))
			omega := arg.TermAs[Set[Fun[A, A]]]("«omegaChart0»")
			independentImage := arg.Have(
				"the images of 1 and y are independent over k[x]",
				"module_independent(restrict_ring(field_ring(L), «curveKx»), "+
					"    «omegaContainer», "+
					"    image(«omegaScaled», {L.one, y}))",
				By(
					homomorphism,
					injective,
					chartParts[0],
					linear_independence.IndependentImage.At(polynomialOps, chartVectors, container, scaled, pair)))
			spanImage := arg.Have(
				"and they span the image of the span of 1 and y",
				"image(«omegaScaled», "+
					"    module_span(restrict_ring(field_ring(L), «curveKx»), "+
					"        restrict_module(regular_module(field_ring(L)), «curveChart0»), "+
					"        {L.one, y})) = "+
					"module_span(restrict_ring(field_ring(L), «curveKx»), "+
					"    «omegaContainer», "+
					"    image(«omegaScaled», {L.one, y}))",
				By(
					homomorphism,
					linear_independence.IndependentInCarrier.Read(chartParts[0]),
					linear_independence.HomSpan.At(polynomialOps, chartVectors, container, scaled, pair)))
			spansOmega := arg.Have(
				"which is the image of chart 0, chart 0 of ω",
				"module_span(restrict_ring(field_ring(L), «curveKx»), "+
					"    «omegaContainer», "+
					"    image(«omegaScaled», {L.one, y})) = "+
					"«omegaChart0»",
				spanImage.RwRev(),
				chartParts[1].Rw(),
				By(onto))
			imagePair := arg.TermAs[Set[Fun[A, A]]]("image(«omegaScaled», {L.one, y})")
			basisImage := arg.Have(
				"so the images of 1 and y are a basis of chart 0 of ω over k[x]",
				"module_basis(restrict_ring(field_ring(L), «curveKx»), "+
					"    restrict_module(«omegaContainer», «omegaChart0»), "+
					"    image(«omegaScaled», {L.one, y}))",
				By(
					polynomialsIn0,
					submodule.SubmoduleRestrictScalars.Read(overChart).At(polynomialOps),
					independentImage,
					spansOmega,
					linear_independence.BasisRestrict.Read(containerOverPolynomials).At(omega, imagePair)))

			// Read back in the statement's spelling: the container's action, the readings, and the two images.
			unitAct := arg.Have(
				"one acts trivially, 1 • y* = y*",
				"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(L.one * z), L.zero)) = «omegaGenerator»",
				By(module.SmulOne.Read(containerModule).At(generatorMember)))
			pairImage := arg.Have(
				"the images of 1 and y are y* and y • y*",
				"image(«omegaScaled», {L.one, y}) = "+
					"{λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(y * z), L.zero), «omegaGenerator»}",
				Simp(Fwd(set_image.ImageClauses)),
				unitAct.Rw(),
				By(set_algebra.InsertComm))
			acting := arg.Have(
				"y acts on y* through the argument",
				"«omegaContainer».smul(y, «omegaGenerator») = "+
					"λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(y * z), L.zero)",
				Simp(Fwd(serre_duality.CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
				Basic())
			readings := arg.Have(
				"so y* reads the coefficient of y and y • y* that of one",
				Statement{
					Binders: "∀p q:A.",
					Hypotheses: []string{
						"p ∈ «curveLaurent»",
						"q ∈ «curveLaurent»",
					},
					Conclusion: "«omegaGenerator»(p + q * y) = q ∧ " +
						"«omegaContainer».smul(y, «omegaGenerator»)(p + q * y) = p",
				},
				Derive(func(c *Argument) {
					p, q := c.FixAs[A]("p"), c.FixAs[A]("q")
					coefficients := c.Assume()
					inOverlap := c.Have(
						"p + q·y lies in the overlap",
						"p + q * y ∈ «curveOverlap»",
						By(coefficients, members))
					c.Show(
						"(y • y*)(p + q·y) is y* at y · (p + q·y), which is p",
						acting.Rw(),
						Simp(Fwd(inOverlap)),
						By(coefficients, values.At(p, q)))
				}))
			basis := arg.Have(
				"{y • y*, y*} is a basis of chart 0 of ω over k[x]",
				"module_basis(restrict_ring(field_ring(L), «curveKx»), "+
					"    restrict_module(«omegaContainer», «omegaChart0»), "+
					"    {«omegaContainer».smul(y, «omegaGenerator»), «omegaGenerator»})",
				acting.Rw(),
				pairImage.RwRev(),
				By(basisImage))
			arg.Show(
				"y* is a vector reading the coefficient of y, y • y* "+
					"reads that of one, and the two are a basis of chart 0 of ω",
				By(generatorIn, readings, basis))
		}),
})}

// DualGeneratorsAgree — read on chart 1: y* is s² times the coefficient of
// u and u • y* is s² times the coefficient of one, in the basis 1, u, with
// s = 1/x, so the generator of chart 1 is y* itself: the two charts'
// generators agree, the unit relating them being one. Both values are
// DualGeneratorReads': p + q·u is p + (q·s²)·y, and u·(p + q·u) is
// q·s·(1 + a·s² + b·s³) + (p·s²)·y by u² = s·(1 + a·s² + b·s³), the
// coefficients lying in k[x, 1/x]; the container scales through the
// argument, p + q·u lying in the overlap.
var DualGeneratorsAgree = dualGeneratorsAgreeThm{family.Add(registry.ProofEntry{
	Name: "DualGeneratorsAgree",
	Key:  "prop_5156dd210a327bc8",
	Reading: "In the basis 1, u of the overlap over k[x, 1/x] the coordinate functional of " +
		"u is u* = x² • y* and that of one is x² • (u • y*). Chart 1 of O(−2) being s²·k[s], " +
		"the dual basis on chart 1 is s² times the coordinate functionals, and s² • u* = y*.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b p q:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"p ∈ «curveLaurent»",
			"q ∈ «curveLaurent»",
		},
		Conclusion: "«omegaGenerator»(p + q * «curveU») = «curveS2» * q ∧ " +
			"«omegaContainer».smul(«curveU», «omegaGenerator»)(p + q * «curveU») = «curveS2» * p",
		Abbrev: Abbrev{
			{Name: "dualGeneratorsAgreeConstant", Text: "q * " +
				"(L.inv(x) * (L.one + a * «curveS2» + b * (L.inv(x) * «curveS2»)))"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			datum Fact,
			p, q *Expr[A],
			coefficients Fact,
		) {
			// k is a subfield of L and x a unit of it, so k[x, 1/x] is a ring inside L holding k and s = inv(x).
			xIn, yIn := WeierstrassXInField.Read(datum).AsFact(), WeierstrassYInField.Read(datum).AsFact()
			xm := arg.MemberOf[on.L](x, xIn)
			ringL := field.RingOn.Read(L)
			unit := arg.Conjuncts(
				GroupPremises(datum, WeierstrassXInvertible.Read(L).At(k, x, y, a, b)),
				"x is not zero",
				"inv(x) lies in L",
				"x · inv(x) = one",
				"inv(x) · x = one")
			laurent := arg.Conjuncts(
				arg.Have(
					"k[x, 1/x] is a subring of L holding k, x and s = inv(x)",
					"subring(field_ring(L), «curveLaurent») ∧ "+
						"k ⊆ «curveLaurent» ∧ "+
						"x ∈ «curveLaurent» ∧ "+
						"L.inv(x) ∈ «curveLaurent»",
					By(
						WeierstrassSubfield.Read(datum).AsFact(),
						xIn,
						unit[0],
						laurent_polynomial.LaurentRingSubring.Read(L).At(k, xm))),
				"k[x, 1/x] is a subring of L",
				"it holds k",
				"it holds x",
				"it holds s = inv(x)")
			sIn := laurent[3]
			laurentRing := arg.Have(
				"so k[x, 1/x] is a ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «curveLaurent»))",
				By(laurent[0], comm_ring.SubringRingOn.Read(ringL).At(arg.TermAs[Set[A]]("«curveLaurent»"))))
			coefficient := arg.Conjuncts(
				coefficients,
				"p lies in k[x, 1/x]",
				"q lies in k[x, 1/x]")
			inL := arg.Have(
				"p, q, a and b lie in L",
				"p ∈ L.carrier ∧ q ∈ L.carrier ∧ a ∈ L.carrier ∧ b ∈ L.carrier",
				BySets(
					coefficients,
					comm_ring.SubringSubset.Read(laurent[0]),
					laurent[1],
					WeierstrassCoefficientA.Read(datum),
					WeierstrassCoefficientB.Read(datum)))
			constants := arg.Have(
				"a and b lie in k[x, 1/x], which holds k",
				"a ∈ «curveLaurent» ∧ b ∈ «curveLaurent»",
				BySets(laurent[1], WeierstrassCoefficientA.Read(datum), WeierstrassCoefficientB.Read(datum)))

			// The value of y*: p + q·u written in the basis 1, y.
			regroup := arg.Have(
				"p + q·u = p + (q·s²)·y, u being y·s²",
				"p + q * «curveU» = p + q * «curveS2» * y",
				ByArith(ringL, inL, xIn, unit[1], yIn))
			qScaled := arg.Have(
				"q·s² lies in k[x, 1/x]",
				"q * «curveS2» ∈ «curveLaurent»",
				By(comm_ring.MulIn.Read(laurentRing), sIn, coefficient[1]))
			atY := arg.Have(
				"so y* reads the coefficient q·s² of y",
				"«omegaGenerator»(p + q * «curveS2» * y) = q * «curveS2»",
				By(datum, coefficient[0], qScaled, DualGeneratorReads.Read(L).At(k, x, y, a, b)))
			first := arg.Have(
				"y* reads s²·q at p + q·u",
				"«omegaGenerator»(p + q * «curveU») = «curveS2» * q",
				regroup.Rw(),
				atY.Rw(),
				ByArith(ringL, inL, xIn, unit[1]))

			// The value of u • y*: u·(p + q·u) written in the basis 1, y.
			relation := arg.Have(
				"u² = s·(1 + a·s² + b·s³), the relation of chart 1",
				"«curveU» * «curveU» = "+
					"L.inv(x) * (L.one + a * (L.inv(x) * L.inv(x)) + b * (L.inv(x) * (L.inv(x) * L.inv(x))))",
				By(datum, WeierstrassChartOneEquation.Read(L).At(k, x, y, a, b)))
			expand := arg.Have(
				"so u·(p + q·u) = q·s·(1 + a·s² + b·s³) + (p·s²)·y",
				"«curveU» * (p + q * «curveU») = «dualGeneratorsAgreeConstant» + p * «curveS2» * y",
				ByArith(ringL, inL, xIn, unit[1], yIn, Scaled(q, relation)))
			constantIn := arg.Have(
				"q·s·(1 + a·s² + b·s³) lies in k[x, 1/x], a ring holding s, a and b",
				"«dualGeneratorsAgreeConstant» ∈ «curveLaurent»",
				By(
					comm_ring.MulIn.Read(laurentRing),
					comm_ring.AddIn.Read(laurentRing),
					comm_ring.OneIn.Read(laurentRing),
					sIn,
					coefficient[1],
					constants))
			pScaled := arg.Have(
				"p·s² lies in k[x, 1/x]",
				"p * «curveS2» ∈ «curveLaurent»",
				By(comm_ring.MulIn.Read(laurentRing), sIn, coefficient[0]))
			atU := arg.Have(
				"so y* reads the coefficient p·s² of y in u·(p + q·u)",
				"«omegaGenerator»(«dualGeneratorsAgreeConstant» + p * «curveS2» * y) = p * «curveS2»",
				By(datum, constantIn, pScaled, DualGeneratorReads.Read(L).At(k, x, y, a, b)))

			// p + q·u lies in the overlap, where the container scales through the argument.
			chart0, chart1, overlap :=
				arg.TermAs[Set[A]]("«curveChart0»"),
				arg.TermAs[Set[A]]("«curveChart1»"),
				arg.TermAs[Set[A]]("«curveOverlap»")
			curve := arg.Have(
				"the datum is a curve over the line of x",
				"«curveOverLine»",
				By(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			line := algebraic_curve.CurveOverItsLine.Read(L).At(k, chart0, chart1, overlap, x)
			overlapRing := arg.Have(
				"the overlap is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveOverlap»))",
				By(curve, line, comm_ring.SubringRingOn.Read(ringL).At(overlap)))
			chartBasis := arg.Conjuncts(
				GroupPremises(datum, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
				"chart 0 is a subring of L",
				"k[x] lies in chart 0",
				"1 and y are a basis of chart 0 over k[x]",
				"one is not y")[2]
			chartParts := arg.Conjuncts(
				arg.Unfolded(chartBasis, linear_independence.ModuleBasisDef),
				"1 and y are independent over k[x]",
				"they span chart 0")
			yOverlap := arg.Have(
				"y, being independent in chart 0, lies in it, and so in the overlap",
				"y ∈ «curveOverlap»",
				By(
					arg.Simplified(
						linear_independence.IndependentInCarrier.Read(chartParts[0]),
						Fwd(set_order.InsertSubset),
						Fwd(set_order.EmptySubset)),
					curve,
					line,
					set_basic.SubsetDef.At(chart0, overlap)))
			summandsIn := arg.Have(
				"p, q·s² and y lie in the overlap",
				"p ∈ «curveOverlap» ∧ q * «curveS2» ∈ «curveOverlap» ∧ y ∈ «curveOverlap»",
				BySets(
					yOverlap,
					qScaled,
					curve,
					algebraic_curve.LaurentRingInOverlap.Read(L).At(k, chart0, chart1, overlap, x),
					coefficients))
			sumIn := arg.Have(
				"so does p + q·u = p + (q·s²)·y",
				"p + q * «curveU» ∈ «curveOverlap»",
				regroup.Rw(),
				By(comm_ring.AddIn.Read(overlapRing), comm_ring.MulIn.Read(overlapRing), summandsIn))
			second := arg.Have(
				"(u • y*)(p + q·u) = y*(u·(p + q·u)) = s²·p",
				"«omegaContainer».smul(«curveU», «omegaGenerator»)(p + q * «curveU») = «curveS2» * p",
				Simp(Fwd(serre_duality.CurveDualizingModuleDef), Fwd(sumIn)),
				expand.Rw(),
				atU.Rw(),
				ByArith(ringL, inL, xIn, unit[1]))
			arg.Show(
				"y* and u • y* take s²·q and s²·p at p + q·u",
				By(first, second))
		}),
})}

// DualGeneratorOne — chart 1 of ω is generated over A₁ by y*: it is the
// image of A₁ under r ↦ r • y*. Chart 1 of ω is a submodule over A₁
// (DualizingIsLattice) holding y*, which carries A₁ into s² · k[s]
// (DualGeneratorsAgree), so it holds every r • y*. A map φ of it takes one
// to s² · P and u to s² · Q with P and Q in k[s], so r = Q + P·u lies in
// A₁, and r • y* reads y*(r · 1) = s² · P at one and y*(r · u) = s² · Q at
// u: it agrees with φ on the basis 1, u of the overlap (BasisSpansOverlap),
// so it is φ (ContainerMapsAgreeOnBasis).
var DualGeneratorOne = dualGeneratorOneThm{family.Add(registry.ProofEntry{
	Name: "DualGeneratorOne",
	Key:  "prop_cd4a0d74f83f60c0",
	Reading: "Chart 1 of ω is free of rank one over A₁, on the same y* as chart 0: " +
		"the curve is Gorenstein at every point of chart 1, the point at infinity included.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "«omegaChart1» = " +
			"{«omegaContainer».smul(r, «omegaGenerator») | r:A | r ∈ «curveChart1»}",
		Abbrev: Abbrev{
			{Name: "minusTwoChart1", Text: "image(L.mul«curveS2», «curveKs»)"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			chart0, chart1 := arg.TermAs[Set[A]]("«curveChart0»"), arg.TermAs[Set[A]]("«curveChart1»")
			overlap, polynomials := arg.TermAs[Set[A]]("«curveOverlap»"), arg.TermAs[Set[A]]("«curveKs»")
			one, u := arg.TermAs[A]("L.one"), arg.TermAs[A]("«curveU»")
			pair, single := arg.TermAs[Set[A]]("{L.one, «curveU»}"), arg.TermAs[Set[A]]("{«curveU»}")
			generator := arg.TermAs[Fun[A, A]]("«omegaGenerator»")
			scaled := arg.TermAs[Fun[A, Fun[A, A]]]("«omegaScaled»")
			square := arg.TermAs[Fun[A, A]]("L.mul(«curveS2»)")
			ringL := field.RingOn.Read(L)

			reads := arg.Conjuncts(
				GroupPremises(datum, DualGeneratorReads.Read(L).At(k, x, y, a, b)),
				"y* is a vector of the container",
				"y* reads the coefficient of y, and at y · (p + q·y) the coefficient of one")
			generatorIn := reads[0]
			generatorMember := proof.MemberOf(generator, generatorIn)
			curve := arg.Have(
				"the datum is a curve over the line of x",
				"«curveOverLine»",
				By(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			line := algebraic_curve.CurveOverItsLine.Read(L).At(k, chart0, chart1, overlap, x)
			onLaurent := arg.Conjuncts(
				GroupPremises(curve, serre_duality.DualizingModuleOn.Read(L).At(k, chart0, chart1, overlap, x)),
				"k[x, 1/x] is a ring",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")
			laurentIn, containerModule := onLaurent[1], onLaurent[4]
			sets := arg.Conjuncts(
				arg.Have(
					"chart 1 lies in the overlap, k[s] in k[x, 1/x], and k[x, 1/x] in L",
					"«curveChart1» ⊆ «curveOverlap» ∧ «curveKs» ⊆ «curveLaurent» ∧ «curveLaurent» ⊆ L.carrier",
					By(curve, line, comm_ring.SubringSubset.Read(onLaurent[0]))),
				"chart 1 lies in the overlap",
				"k[s] lies in k[x, 1/x]",
				"k[x, 1/x] lies in L")
			overlapRing := arg.Have(
				"the overlap is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveOverlap»))",
				By(curve, line, comm_ring.SubringRingOn.Read(ringL).At(overlap)))
			xm := arg.MemberOf[on.L](x, WeierstrassXInField.Read(datum).AsFact())
			sm := field.InvIn.Read(L).At(xm)
			ym := arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())
			fieldL := arg.TermAs[field.FieldOps[A]]("L")

			// One and u lie in chart 1 and in the overlap, and are a basis of the overlap over k[x, 1/x].
			chartBasis := arg.Conjuncts(
				GroupPremises(datum, WeierstrassBasisOne.Read(L).At(k, x, y, a, b)),
				"chart 1 is a subring of L",
				"k[s] lies in chart 1",
				"1 and u are a basis of chart 1 over k[s]",
				"one is not u")[2]
			chartParts := arg.Conjuncts(
				arg.Unfolded(chartBasis, linear_independence.ModuleBasisDef),
				"1 and u are independent over k[s]",
				"they span chart 1")
			points := arg.Conjuncts(
				arg.Have(
					"1 and u, being independent in chart 1, lie in it, and so in the overlap",
					"L.one ∈ «curveChart1» ∧ "+
						"«curveU» ∈ «curveChart1» ∧ "+
						"L.one ∈ «curveOverlap» ∧ "+
						"«curveU» ∈ «curveOverlap»",
					By(
						arg.Simplified(
							linear_independence.IndependentInCarrier.Read(chartParts[0]),
							Fwd(set_order.InsertSubset),
							Fwd(set_order.EmptySubset)),
						sets[0],
						set_basic.SubsetDef.At(chart1, overlap))),
				"1 lies in chart 1",
				"u lies in chart 1",
				"1 lies in the overlap",
				"u lies in the overlap")
			uOverlap := proof.MemberOf(u, points[3])
			overlapBases := arg.Conjuncts(
				GroupPremises(curve, algebraic_curve.BasisSpansOverlap.Read(L).At(k, chart0, chart1, overlap, x)),
				"a basis of chart 0 over k[x] is one of the overlap over k[x, 1/x]",
				"and so is a basis of chart 1 over k[s]")
			overlapBasis := arg.Have(
				"so one and u are a basis of the overlap over k[x, 1/x]",
				"module_basis(restrict_ring(field_ring(L), «curveLaurent»), "+
					"    restrict_module(regular_module(field_ring(L)), «curveOverlap»), "+
					"    {L.one, «curveU»})",
				By(curve, chartBasis, overlapBases[1].At(pair)))

			// For r = p + q·u, y* reads s² · q at r · 1 and s² · p at r · u (DualGeneratorsAgree).
			evaluations := arg.Have(
				"for r = p + q·u, y*(r · 1) = s² · q and y*(r · u) = s² · p",
				Statement{
					Binders: "∀p q:A.",
					Hypotheses: []string{
						"p ∈ «curveLaurent»",
						"q ∈ «curveLaurent»",
					},
					Conclusion: "«omegaGenerator»((p + q * «curveU») * L.one) = «curveS2» * q ∧ " +
						"«omegaGenerator»((p + q * «curveU») * «curveU») = «curveS2» * p",
				},
				Derive(func(c *Argument) {
					p, q := c.FixAs[A]("p"), c.FixAs[A]("q")
					coefficients := c.Assume()
					parts := c.Conjuncts(
						coefficients,
						"p lies in k[x, 1/x]",
						"q lies in k[x, 1/x]")
					inL := c.Have(
						"p and q lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(coefficients, sets[2]))
					inOverlap := c.Conjuncts(
						c.Have(
							"p and q lie in the overlap",
							"p ∈ «curveOverlap» ∧ q ∈ «curveOverlap»",
							BySets(parts[0], parts[1], laurentIn)),
						"p lies in the overlap",
						"q lies in the overlap")
					pM, qM := proof.MemberOf(p, inOverlap[0]), proof.MemberOf(q, inOverlap[1])
					sumIn := c.Have(
						"p + q·u lies in the overlap, a ring",
						"p + q * «curveU» ∈ «curveOverlap»",
						By(comm_ring.AddIn.Read(overlapRing).At(pM, comm_ring.MulIn.Read(overlapRing).At(qM, uOverlap))))
					values := c.Conjuncts(
						GroupPremises(datum, parts[0], parts[1], DualGeneratorsAgree.Read(L).At(k, x, y, a, b, p, q)),
						"y* is s² · q at p + q · u",
						"u • y* is s² · p there")
					acting := c.Have(
						"u • y* reads y* at u · (p + q·u)",
						"«omegaContainer».smul(«curveU», «omegaGenerator»)(p + q * «curveU») = "+
							"«omegaGenerator»(«curveU» * (p + q * «curveU»))",
						Simp(Fwd(serre_duality.CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
						By(sumIn))
					unit := c.Have(
						"(p + q·u) · 1 = p + q·u",
						"(p + q * «curveU») * L.one = p + q * «curveU»",
						ByArith(ringL, inL, ym, sm))
					swap := c.Have(
						"(p + q·u) · u = u · (p + q·u)",
						"(p + q * «curveU») * «curveU» = «curveU» * (p + q * «curveU»)",
						ByArith(ringL, inL, ym, sm))
					atOne := c.Have(
						"so y* reads s² · q at (p + q·u) · 1",
						"«omegaGenerator»((p + q * «curveU») * L.one) = «curveS2» * q",
						unit.Rw(),
						By(values[0]))
					atU := c.Have(
						"and s² · p at (p + q·u) · u = u · (p + q·u)",
						"«omegaGenerator»((p + q * «curveU») * «curveU») = «curveS2» * p",
						swap.Rw(),
						By(sumIn, acting, values[1]))
					c.Show(
						"y* reads s² · q at (p + q·u) · 1 and s² · p at (p + q·u) · u",
						By(atOne, atU))
				}))

			// Chart 1 of ω is the maps carrying chart 1 into s² · k[s], a submodule over chart 1 holding y*.
			powTwo := arg.Have(
				"s² is the second power of s",
				"monoid_pow(L.mul, L.one, L.inv(x), 2) = «curveS2»",
				ByArith(ringL, sm))
			omegaChart := arg.Have(
				"chart 1 of ω is the maps of the container carrying A₁ into s² · k[s]",
				"«omegaChart1» = {φ:A → A | φ ∈ «omegaMaps» ∧ image(φ, «curveChart1») ⊆ «minusTwoChart1»}",
				Simp(
					Fwd(serre_duality.CurveDualizingPairDef),
					Fwd(pairs.Snd),
					Fwd(projective_line.ProjectiveLinePairDef),
					Fwd(laurent_polynomial.LaurentMonomialOfNum),
					Fwd(powTwo)),
				Basic())
			omegaIff := arg.Have(
				"so a map lies in it exactly when it is such a map",
				"∀φ:(A → A). φ ∈ «omegaChart1» ⇔ φ ∈ «omegaMaps» ∧ image(φ, «curveChart1») ⊆ «minusTwoChart1»",
				omegaChart.Rw(),
				BySets())
			onChart := arg.Have(
				"y* carries chart 1 into s² · k[s]: at p + q · u it is s² · q",
				"∀z:A. z ∈ «curveChart1» ⇒ «omegaGenerator»(z) ∈ «minusTwoChart1»",
				Derive(func(d *Argument) {
					z := d.FixAs[A]("z")
					zIn := d.Assume()
					p, q, form := d.Obtain2As[A, A](
						"z is p + q · u with p and q in k[s]",
						"∃p q:A. p ∈ «curveKs» ∧ q ∈ «curveKs» ∧ z = p + q * «curveU»",
						By(zIn, WeierstrassChartOneMembers.At(fieldL, k, x, y, z)))
					parts := d.Conjuncts(
						form,
						"p lies in k[s]",
						"q lies in k[s]",
						"z is p + q · u")
					inLaurent := d.Have(
						"so p and q lie in k[x, 1/x]",
						"p ∈ «curveLaurent» ∧ q ∈ «curveLaurent»",
						BySets(parts[0], parts[1], sets[1]))
					atZ := d.Have(
						"so y* is s² · q at p + q · u",
						"«omegaGenerator»(p + q * «curveU») = «curveS2» * q",
						By(datum, inLaurent, DualGeneratorsAgree.Read(L).At(k, x, y, a, b, p, q)))
					d.Show(
						"which is s² times a member of k[s]",
						parts[2].Rw(),
						By(atZ, parts[1], set_image.FunInImage.At(square, polynomials, q)))
				}))
			lineChart := arg.TermAs[Set[A]]("«minusTwoChart1»")
			generatorInOmega := arg.Have(
				"so y* lies in chart 1 of ω",
				"«omegaGenerator» ∈ «omegaChart1»",
				By(
					generatorIn,
					onChart,
					set_image.ImageSubsetIff.At(generator, chart1, lineChart),
					omegaIff.At(generator)))
			lattice := arg.Unfolded(arg.Have(
				"ω is a lattice pair over the overlap",
				"lattice_pair(restrict_ring(field_ring(L), «curveOverlap»), "+
					"    «curveChart0», "+
					"    «curveChart1», "+
					"    «omegaContainer», "+
					"    «omegaPair»)",
				By(curve, serre_duality.DualizingIsLattice.Read(L).At(k, chart0, chart1, overlap, x))),
				lattice_pair.LatticePairDef)
			overChart := arg.Have(
				"chart 1 of ω is a submodule over chart 1",
				"submodule(restrict_ring(restrict_ring(field_ring(L), «curveOverlap»), «curveChart1»), "+
					"    «omegaContainer», "+
					"    «omegaChart1»)",
				By(lattice))

			// Every r • y* with r in chart 1 lies in chart 1 of ω, and every member of chart 1 of ω is one.
			intoOmega := arg.Have(
				"r • y* lies in chart 1 of ω, a submodule over chart 1 holding y*",
				Statement{
					Binders: "∀r:A.",
					Hypotheses: []string{
						"r ∈ «curveChart1»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero)) ∈ «omegaChart1»",
				},
				Derive(func(c *Argument) {
					r := c.FixAs[A]("r")
					rIn := c.Assume()
					c.Show(
						"chart 1 of ω is closed under chart 1's action",
						By(submodule.SubmoduleSmul.Read(overChart).At(
							proof.MemberOf(r, rIn), proof.MemberOf(generator, generatorInOmega))))
				}))
			fromOmega := arg.Have(
				"every φ of chart 1 of ω is r • y* for r = Q + P · u, φ taking s² · P at one and s² · Q at u",
				"∀φ:(A → A). φ ∈ «omegaChart1» ⇒ φ ∈ image(«omegaScaled», «curveChart1»)",
				Derive(func(c *Argument) {
					φ := c.FixAs[Fun[A, A]]("φ")
					φIn := c.Assume()
					ofφ := c.Conjuncts(
						c.Have(
							"φ is a map of the container carrying A₁ into s² · k[s]",
							"φ ∈ «omegaMaps» ∧ image(φ, «curveChart1») ⊆ «minusTwoChart1»",
							By(φIn, omegaIff.At(φ))),
						"φ is a map of the container",
						"φ carries chart 1 into s² · k[s]")
					values := c.Have(
						"so φ(one) and φ(u) lie in s² · k[s]",
						"φ(L.one) ∈ «minusTwoChart1» ∧ φ(«curveU») ∈ «minusTwoChart1»",
						By(ofφ[1], set_image.ImageSubsetIff.At(φ, chart1, lineChart), points[0], points[1]))
					P, ofP := c.UnpackAs[A](c.Have(
						"so φ(one) = s² · P for some P in k[s]",
						"∃P:A. φ(L.one) = «curveS2» * P ∧ P ∈ «curveKs»",
						By(values, set_basic.InImage.At(square, polynomials, c.TermAs[A]("φ(L.one)")))), "P")
					Q, ofQ := c.UnpackAs[A](c.Have(
						"and φ(u) = s² · Q for some Q in k[s]",
						"∃Q:A. φ(«curveU») = «curveS2» * Q ∧ Q ∈ «curveKs»",
						By(values, set_basic.InImage.At(square, polynomials, c.TermAs[A]("φ(«curveU»)")))), "Q")
					onP := c.Conjuncts(
						ofP,
						"φ(one) = s² · P",
						"P lies in k[s]")
					onQ := c.Conjuncts(
						ofQ,
						"φ(u) = s² · Q",
						"Q lies in k[s]")
					r := c.TermAs[A]("Q + P * «curveU»")
					expansion := c.Have(
						"r = Q + P · u has its coefficients in k[s]",
						"∃p q:A. p ∈ «curveKs» ∧ q ∈ «curveKs» ∧ Q + P * «curveU» = p + q * «curveU»",
						Derive(func(d *Argument) {
							d.Take(Q)
							d.Take(P)
							d.Show(
								"Q and P are they",
								By(onQ[1], onP[1]))
						}))
					rIn := c.Have(
						"so r lies in chart 1",
						"Q + P * «curveU» ∈ «curveChart1»",
						By(expansion, WeierstrassChartOneMembers.At(fieldL, k, x, y, r)))
					rOverlap := c.Have(
						"and in the overlap",
						"Q + P * «curveU» ∈ «curveOverlap»",
						BySets(rIn, sets[0]))
					inLaurent := c.Have(
						"P and Q lie in k[x, 1/x]",
						"P ∈ «curveLaurent» ∧ Q ∈ «curveLaurent»",
						BySets(onP[1], onQ[1], sets[1]))
					scaledR := c.TermAs[Fun[A, A]](
						"λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((Q + P * «curveU») * z), L.zero)")
					agree := c.Have(
						"r • y* and φ agree on one and u: y* reads s² · P in r · 1 and s² · Q in r · u",
						Statement{
							Binders: "∀e:A.",
							Hypotheses: []string{
								"e ∈ {L.one, «curveU»}",
							},
							Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((Q + P * «curveU») * z), L.zero))( " +
								"    e) = " +
								"φ(e)",
						},
						Simp(Fwd(set_basic.ForallInInsert), Fwd(set_basic.NotInEmpty)),
						By(inLaurent, points[2], points[3], onP[0], onQ[0], evaluations.At(Q, P)))
					scaledVector := c.Have(
						"r • y* is a vector of the container",
						"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((Q + P * «curveU») * z), L.zero)) ∈ "+
							"«omegaContainer».carrier",
						By(module.SmulIn.Read(containerModule).At(proof.MemberOf(r, rOverlap), generatorMember)))
					same := c.Have(
						"so r • y* is φ, the two agreeing on the basis 1, u of the overlap",
						"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((Q + P * «curveU») * z), L.zero)) = φ",
						By(
							curve,
							finite_set.FiniteSing.At(u),
							finite_set.FiniteInsert.At(one, single),
							overlapBasis,
							scaledVector,
							ofφ[0],
							agree,
							serre_duality.ContainerMapsAgreeOnBasis.Read(L).At(
								k, chart0, chart1, overlap, x, pair, scaledR, φ)))
					witnessed := c.Have(
						"so φ is s • y* for an s of chart 1, namely r",
						"∃s:A. φ = (λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(s * z), L.zero)) ∧ s ∈ «curveChart1»",
						Derive(func(d *Argument) {
							d.Take(r)
							d.Show(
								"r is one",
								By(same, rIn))
						}))
					c.Show(
						"so φ is the image of r",
						By(witnessed, set_basic.InImage.At(scaled, chart1, φ)))
				}))
			imageSet, omega :=
				arg.TermAs[Set[Fun[A, A]]]("image(«omegaScaled», «curveChart1»)"),
				arg.TermAs[Set[Fun[A, A]]]("«omegaChart1»")
			onto := arg.Have(
				"so r ↦ r • y* maps chart 1 onto chart 1 of ω",
				"image(«omegaScaled», «curveChart1») = «omegaChart1»",
				By(
					intoOmega,
					set_image.ImageSubsetIff.At(scaled, chart1, omega),
					fromOmega,
					set_basic.SubsetDef.At(omega, imageSet),
					set_order.SubsetAntisym.At(imageSet, omega)))
			acting := arg.Have(
				"the overlap acts on y* through the argument",
				"∀r:A. "+
					"    «omegaContainer».smul(r, «omegaGenerator») = "+
					"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero)",
				Simp(Fwd(serre_duality.CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
				Basic())
			arg.Show(
				"so chart 1 of ω is the image of chart 1 under r ↦ r • y*",
				Simp(Fwd(acting)),
				By(onto, set_image.SimpleImage))
		}),
})}

// DualBasisOne — u • y* and y* are a basis of chart 1 of ω over k[s],
// s = 1/x: s² times the dual basis of 1, u. r ↦ r • y* is k[s]-linear on
// chart 1, one-to-one there, r = p + q·u being read back off its values
// s² · q at one and s² · p at u (DualGeneratorsAgree), and onto chart 1 of
// ω (DualGeneratorOne), so it carries the basis 1, u of chart 1
// (WeierstrassBasisOne) to a basis, y* and u • y*.
var DualBasisOne = dualBasisOneThm{family.Add(registry.ProofEntry{
	Name: "DualBasisOne",
	Key:  "prop_3c314cca13133a75",
	Reading: "{u • y*, y*} is s² times the basis dual to 1, u, chart 1 of O(−2) being " +
		"s²·k[s]: y* is s² times the coordinate functional of u, and u • y* s² times that of one.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "module_basis(restrict_ring(field_ring(L), «curveKs»), " +
			"    restrict_module(«omegaContainer», «omegaChart1»), " +
			"    {«omegaContainer».smul(«curveU», «omegaGenerator»), «omegaGenerator»})",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			chart0, chart1 := arg.TermAs[Set[A]]("«curveChart0»"), arg.TermAs[Set[A]]("«curveChart1»")
			overlap, polynomials := arg.TermAs[Set[A]]("«curveOverlap»"), arg.TermAs[Set[A]]("«curveKs»")
			pair := arg.TermAs[Set[A]]("{L.one, «curveU»}")
			generator := arg.TermAs[Fun[A, A]]("«omegaGenerator»")
			scaled := arg.TermAs[Fun[A, Fun[A, A]]]("«omegaScaled»")
			fieldOps := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			overlapOps, chart1Ops :=
				arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveOverlap»)"),
				arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveChart1»)")
			polynomialOps := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveKs»)")
			chartVectors := arg.TermAs[module_record.ModuleOps[A, A]](
				"restrict_module(regular_module(field_ring(L)), «curveChart1»)")
			container := arg.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«omegaContainer»")
			ringL := field.RingOn.Read(L)

			reads := arg.Conjuncts(
				GroupPremises(datum, DualGeneratorReads.Read(L).At(k, x, y, a, b)),
				"y* is a vector of the container",
				"y* reads the coefficient of y, and at y · (p + q·y) the coefficient of one")
			generatorMember := proof.MemberOf(generator, reads[0])
			curve := arg.Have(
				"the datum is a curve over the line of x",
				"«curveOverLine»",
				By(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			line := algebraic_curve.CurveOverItsLine.Read(L).At(k, chart0, chart1, overlap, x)
			onLaurent := arg.Conjuncts(
				GroupPremises(curve, serre_duality.DualizingModuleOn.Read(L).At(k, chart0, chart1, overlap, x)),
				"k[x, 1/x] is a ring",
				"it lies in the overlap",
				"its inclusion is a ring map",
				"the overlap is a module over it",
				"the container is a module over the overlap")
			laurentIn, containerModule := onLaurent[1], onLaurent[4]
			sets := arg.Conjuncts(
				arg.Have(
					"chart 1 lies in the overlap, k[s] in k[x, 1/x], and k[x, 1/x] in L, k[s] being a subring of L",
					"«curveChart1» ⊆ «curveOverlap» ∧ "+
						"«curveKs» ⊆ «curveLaurent» ∧ "+
						"«curveLaurent» ⊆ L.carrier ∧ "+
						"subring(field_ring(L), «curveKs»)",
					By(curve, line, comm_ring.SubringSubset.At(fieldOps, arg.TermAs[Set[A]]("«curveLaurent»")))),
				"chart 1 lies in the overlap",
				"k[s] lies in k[x, 1/x]",
				"k[x, 1/x] lies in L",
				"k[s] is a subring of L")
			overlapRing := arg.Have(
				"the overlap is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveOverlap»))",
				By(curve, line, comm_ring.SubringRingOn.Read(ringL).At(overlap)))
			xm := arg.MemberOf[on.L](x, WeierstrassXInField.Read(datum).AsFact())
			sm := field.InvIn.Read(L).At(xm)
			ym := arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())
			cancel := arg.Have(
				"x · s = one",
				"x * L.inv(x) = L.one",
				By(curve, line))
			unit := arg.Have(
				"so x² · s² = one",
				"x * x * «curveS2» = L.one",
				ByArith(ringL, xm, sm, cancel, Scaled(arg.TermAs[A]("x * L.inv(x)"), cancel)))
			fieldL := arg.TermAs[field.FieldOps[A]]("L")

			// Chart 1 is free over k[s] on one and u, which lie in the overlap.
			chart := arg.Conjuncts(
				GroupPremises(datum, WeierstrassBasisOne.Read(L).At(k, x, y, a, b)),
				"chart 1 is a subring of L",
				"k[s] lies in chart 1",
				"1 and u are a basis of chart 1 over k[s]",
				"one is not u")
			polynomialsIn1, chartBasis := chart[1], chart[2]
			chartRing := arg.Have(
				"chart 1 is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveChart1»))",
				By(chart[0], comm_ring.SubringRingOn.Read(ringL).At(chart1)))
			polynomialsInOverlap := arg.Have(
				"so k[s] lies in the overlap",
				"«curveKs» ⊆ «curveOverlap»",
				BySets(polynomialsIn1, sets[0]))
			polynomialsRing := arg.Have(
				"k[s] is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), «curveKs»))",
				By(sets[3], comm_ring.SubringRingOn.Read(ringL).At(polynomials)))
			subringOf1 := arg.Have(
				"so k[s], lying in chart 1, is a subring of it",
				"subring(restrict_ring(field_ring(L), «curveChart1»), «curveKs»)",
				By(
					polynomialsRing,
					polynomialsIn1,
					comm_ring.SubringRingOn.Read(chartRing).At(polynomials),
					module_record.RestrictRingTwice.At(fieldOps, chart1, polynomials)))
			subringOfOverlap := arg.Have(
				"and, lying in the overlap, a subring of the overlap",
				"subring(restrict_ring(field_ring(L), «curveOverlap»), «curveKs»)",
				By(
					polynomialsRing,
					polynomialsInOverlap,
					comm_ring.SubringRingOn.Read(overlapRing).At(polynomials),
					module_record.RestrictRingTwice.At(fieldOps, overlap, polynomials)))
			chartParts := arg.Conjuncts(
				arg.Unfolded(chartBasis, linear_independence.ModuleBasisDef),
				"1 and u are independent over k[s]",
				"they span chart 1")
			points := arg.Conjuncts(
				arg.Have(
					"1 and u, being independent in chart 1, lie in it, and so in the overlap",
					"L.one ∈ «curveChart1» ∧ "+
						"«curveU» ∈ «curveChart1» ∧ "+
						"L.one ∈ «curveOverlap» ∧ "+
						"«curveU» ∈ «curveOverlap»",
					By(
						arg.Simplified(
							linear_independence.IndependentInCarrier.Read(chartParts[0]),
							Fwd(set_order.InsertSubset),
							Fwd(set_order.EmptySubset)),
						sets[0],
						set_basic.SubsetDef.At(chart1, overlap))),
				"1 lies in chart 1",
				"u lies in chart 1",
				"1 lies in the overlap",
				"u lies in the overlap")
			uOverlap := proof.MemberOf(arg.TermAs[A]("«curveU»"), points[3])

			// For r = p + q·u, y* reads s² · q at r · 1 and s² · p at r · u (DualGeneratorsAgree).
			evaluations := arg.Have(
				"for r = p + q·u, y*(r · 1) = s² · q and y*(r · u) = s² · p",
				Statement{
					Binders: "∀p q:A.",
					Hypotheses: []string{
						"p ∈ «curveLaurent»",
						"q ∈ «curveLaurent»",
					},
					Conclusion: "«omegaGenerator»((p + q * «curveU») * L.one) = «curveS2» * q ∧ " +
						"«omegaGenerator»((p + q * «curveU») * «curveU») = «curveS2» * p",
				},
				Derive(func(c *Argument) {
					p, q := c.FixAs[A]("p"), c.FixAs[A]("q")
					coefficients := c.Assume()
					parts := c.Conjuncts(
						coefficients,
						"p lies in k[x, 1/x]",
						"q lies in k[x, 1/x]")
					inL := c.Have(
						"p and q lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(coefficients, sets[2]))
					inOverlap := c.Conjuncts(
						c.Have(
							"p and q lie in the overlap",
							"p ∈ «curveOverlap» ∧ q ∈ «curveOverlap»",
							BySets(parts[0], parts[1], laurentIn)),
						"p lies in the overlap",
						"q lies in the overlap")
					pM, qM := proof.MemberOf(p, inOverlap[0]), proof.MemberOf(q, inOverlap[1])
					sumIn := c.Have(
						"p + q·u lies in the overlap, a ring",
						"p + q * «curveU» ∈ «curveOverlap»",
						By(comm_ring.AddIn.Read(overlapRing).At(pM, comm_ring.MulIn.Read(overlapRing).At(qM, uOverlap))))
					values := c.Conjuncts(
						GroupPremises(datum, parts[0], parts[1], DualGeneratorsAgree.Read(L).At(k, x, y, a, b, p, q)),
						"y* is s² · q at p + q · u",
						"u • y* is s² · p there")
					acting := c.Have(
						"u • y* reads y* at u · (p + q·u)",
						"«omegaContainer».smul(«curveU», «omegaGenerator»)(p + q * «curveU») = "+
							"«omegaGenerator»(«curveU» * (p + q * «curveU»))",
						Simp(Fwd(serre_duality.CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
						By(sumIn))
					unitR := c.Have(
						"(p + q·u) · 1 = p + q·u",
						"(p + q * «curveU») * L.one = p + q * «curveU»",
						ByArith(ringL, inL, ym, sm))
					swap := c.Have(
						"(p + q·u) · u = u · (p + q·u)",
						"(p + q * «curveU») * «curveU» = «curveU» * (p + q * «curveU»)",
						ByArith(ringL, inL, ym, sm))
					atOne := c.Have(
						"so y* reads s² · q at (p + q·u) · 1",
						"«omegaGenerator»((p + q * «curveU») * L.one) = «curveS2» * q",
						unitR.Rw(),
						By(values[0]))
					atU := c.Have(
						"and s² · p at (p + q·u) · u = u · (p + q·u)",
						"«omegaGenerator»((p + q * «curveU») * «curveU») = «curveS2» * p",
						swap.Rw(),
						By(sumIn, acting, values[1]))
					c.Show(
						"y* reads s² · q at (p + q·u) · 1 and s² · p at (p + q·u) · u",
						By(atOne, atU))
				}))

			// r ↦ r • y* is a k[s]-linear map from chart 1 into the container.
			chartModule := arg.Have(
				"chart 1 is a module over k[s], a ring inside it",
				"module_on(restrict_ring(field_ring(L), «curveKs»), "+
					"    restrict_module(regular_module(field_ring(L)), «curveChart1»))",
				Simp(Fwd(module_record.RestrictModuleDef)),
				By(
					subringOf1,
					module.RegularModuleOverSubring.Read(chartRing).At(polynomials),
					module_record.RestrictRingDef.At(chart1Ops, polynomials),
					module_record.RestrictRingDef.At(fieldOps, polynomials),
					module_record.RegularModuleDef.At(chart1Ops)))
			containerOverPolynomials := arg.Have(
				"the container is a module over k[s], which lies in the overlap",
				"module_on(restrict_ring(field_ring(L), «curveKs»), «omegaContainer»)",
				By(
					subringOfOverlap,
					module.ModuleRestrictScalars.Read(containerModule).At(polynomials),
					module_record.RestrictRingDef.At(overlapOps, polynomials),
					module_record.RestrictRingDef.At(fieldOps, polynomials)))
			scaledIn := arg.Have(
				"r • y* is a map of the container",
				Statement{
					Binders: "∀r:A.",
					Hypotheses: []string{
						"r ∈ «curveChart1»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero)) ∈ «omegaMaps»",
				},
				Derive(func(c *Argument) {
					r := c.FixAs[A]("r")
					rIn := c.Assume()
					rO := c.Have(
						"r lies in the overlap",
						"r ∈ «curveOverlap»",
						BySets(rIn, sets[0]))
					c.Show(
						"the container is closed under the overlap's action",
						By(module.SmulIn.Read(containerModule).At(proof.MemberOf(r, rO), generatorMember)))
				}))
			scaledAdd := arg.Have(
				"(r + s) • y* = r • y* + s • y*",
				Statement{
					Binders: "∀r s:A.",
					Hypotheses: []string{
						"r ∈ «curveChart1»",
						"s ∈ «curveChart1»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((r + s) * z), L.zero)) = " +
						"fun_add(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero), " +
						"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(s * z), L.zero))",
				},
				Derive(func(c *Argument) {
					r, s := c.FixAs[A]("r"), c.FixAs[A]("s")
					both := c.Conjuncts(
						c.Assume(),
						"r lies in chart 1",
						"s lies in chart 1")
					inOverlap := c.Conjuncts(
						c.Have(
							"r and s lie in the overlap",
							"r ∈ «curveOverlap» ∧ s ∈ «curveOverlap»",
							BySets(both[0], both[1], sets[0])),
						"r lies in the overlap",
						"s lies in the overlap")
					c.Show(
						"the action distributes over the overlap's sum",
						By(module.SmulAddRight.Read(containerModule).At(
							proof.MemberOf(r, inOverlap[0]), proof.MemberOf(s, inOverlap[1]), generatorMember)))
				}))
			scaledMul := arg.Have(
				"(c · r) • y* = c • (r • y*)",
				Statement{
					Binders: "∀c r:A.",
					Hypotheses: []string{
						"c ∈ «curveKs»",
						"r ∈ «curveChart1»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(c * r * z), L.zero)) = " +
						"λz:A. " +
						"    COND(z ∈ «curveOverlap», " +
						"        COND(c * z ∈ «curveOverlap», «omegaGenerator»(r * (c * z)), L.zero), " +
						"        L.zero)",
				},
				Derive(func(d *Argument) {
					c, r := d.FixAs[A]("c"), d.FixAs[A]("r")
					both := d.Conjuncts(
						d.Assume(),
						"c lies in k[s]",
						"r lies in chart 1")
					inOverlap := d.Conjuncts(
						d.Have(
							"c and r lie in the overlap",
							"c ∈ «curveOverlap» ∧ r ∈ «curveOverlap»",
							BySets(both[0], both[1], polynomialsInOverlap, sets[0])),
						"c lies in the overlap",
						"r lies in the overlap")
					d.Show(
						"the action is associative",
						By(module.SmulMul.Read(containerModule).At(
							proof.MemberOf(c, inOverlap[0]), proof.MemberOf(r, inOverlap[1]), generatorMember)))
				}))
			homomorphism := arg.Have(
				"so r ↦ r • y* is k[s]-linear from chart 1 into the container",
				"module_homomorphism(restrict_ring(field_ring(L), «curveKs»), "+
					"    restrict_module(regular_module(field_ring(L)), «curveChart1»), "+
					"    «omegaContainer», "+
					"    «omegaScaled»)",
				By(
					chartModule,
					containerOverPolynomials,
					scaledIn,
					scaledAdd,
					scaledMul,
					module_homomorphism.ModuleHomomorphismDef.At(polynomialOps, chartVectors, container, scaled)))

			// One-to-one on chart 1: r = p + q·u is read back off r • y* at u and at one.
			reconstruct := arg.Have(
				"a member r of chart 1 is x² · y*(r · u) + x² · y*(r · 1) · u",
				Statement{
					Binders: "∀r:A.",
					Hypotheses: []string{
						"r ∈ «curveChart1»",
					},
					Conclusion: "r = " +
						"x * x * «omegaGenerator»(r * «curveU») + x * x * «omegaGenerator»(r * L.one) * «curveU»",
				},
				Derive(func(c *Argument) {
					r := c.FixAs[A]("r")
					rIn := c.Assume()
					p, q, form := c.Obtain2As[A, A](
						"r is p + q · u with p and q in k[s]",
						"∃p q:A. p ∈ «curveKs» ∧ q ∈ «curveKs» ∧ r = p + q * «curveU»",
						By(rIn, WeierstrassChartOneMembers.At(fieldL, k, x, y, r)))
					parts := c.Conjuncts(
						form,
						"p lies in k[s]",
						"q lies in k[s]",
						"r is p + q · u")
					inLaurent := c.Have(
						"p and q lie in k[x, 1/x]",
						"p ∈ «curveLaurent» ∧ q ∈ «curveLaurent»",
						BySets(parts[0], parts[1], sets[1]))
					inL := c.Have(
						"and in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(inLaurent, sets[2]))
					read := c.Conjuncts(
						GroupPremises(inLaurent, evaluations.At(p, q)),
						"y*(r · 1) = s² · q",
						"y*(r · u) = s² · p")
					c.Show(
						"x² · s² · p + x² · s² · q · u is p + q · u, x² · s² being one",
						parts[2].Rw(),
						read[0].Rw(),
						read[1].Rw(),
						ByArith(
							ringL,
							inL,
							xm,
							sm,
							ym,
							Scaled(c.TermAs[A]("p"), unit),
							Scaled(c.TermAs[A]("q * «curveU»"), unit)))
				}))
			injective := arg.Have(
				"so r ↦ r • y* is one-to-one on chart 1",
				"injective_on(«curveChart1», «omegaScaled»)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(c *Argument) {
					r, s := c.FixAs[A]("r"), c.FixAs[A]("s")
					parts := c.Conjuncts(
						c.Assume(),
						"r lies in chart 1",
						"s lies in chart 1",
						"r • y* = s • y*")
					atU := c.Have(
						"so r • y* and s • y* agree at u",
						"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero))(«curveU») = "+
							"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(s * z), L.zero))(«curveU»)",
						parts[2].Rw(),
						Basic())
					atOne := c.Have(
						"and at one",
						"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero))(L.one) = "+
							"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(s * z), L.zero))(L.one)",
						parts[2].Rw(),
						Basic())
					readU := c.Have(
						"so y*(r · u) = y*(s · u), u lying in the overlap",
						"«omegaGenerator»(r * «curveU») = «omegaGenerator»(s * «curveU»)",
						By(atU, points[3]))
					readOne := c.Have(
						"and y*(r · 1) = y*(s · 1), one lying in the overlap",
						"«omegaGenerator»(r * L.one) = «omegaGenerator»(s * L.one)",
						By(atOne, points[2]))
					c.Show(
						"r and s are read off the one map",
						CalcEq(
							Leg(
								c.TermAs[A](
									"x * x * «omegaGenerator»(r * «curveU») + x * x * «omegaGenerator»(r * L.one) * «curveU»"),
								"r is read off r • y*",
								By(reconstruct.At(r), parts[0])),
							FinalLeg(
								"which reads off s • y* as s",
								readU.Rw(),
								readOne.Rw(),
								By(reconstruct.At(s), parts[1]))))
				}))
			onto := arg.Have(
				"and it maps chart 1 onto chart 1 of ω",
				"image(«omegaScaled», «curveChart1») = «omegaChart1»",
				GroupPremises(datum, DualGeneratorOne.Read(L).At(k, x, y, a, b)).Rw(),
				By(set_image.SimpleImage))

			// The images y* and u • y* of the basis 1, u are a basis of chart 1 of ω.
			lattice := arg.Unfolded(arg.Have(
				"ω is a lattice pair over the overlap",
				"lattice_pair(restrict_ring(field_ring(L), «curveOverlap»), "+
					"    «curveChart0», "+
					"    «curveChart1», "+
					"    «omegaContainer», "+
					"    «omegaPair»)",
				By(curve, serre_duality.DualizingIsLattice.Read(L).At(k, chart0, chart1, overlap, x))),
				lattice_pair.LatticePairDef)
			overChart := arg.Have(
				"chart 1 of ω is a submodule over chart 1",
				"submodule(restrict_ring(restrict_ring(field_ring(L), «curveOverlap»), «curveChart1»), "+
					"    «omegaContainer», "+
					"    «omegaChart1»)",
				By(lattice))
			omega := arg.TermAs[Set[Fun[A, A]]]("«omegaChart1»")
			independentImage := arg.Have(
				"the images of one and u are independent over k[s]",
				"module_independent(restrict_ring(field_ring(L), «curveKs»), "+
					"    «omegaContainer», "+
					"    image(«omegaScaled», {L.one, «curveU»}))",
				By(
					homomorphism,
					injective,
					chartParts[0],
					linear_independence.IndependentImage.At(polynomialOps, chartVectors, container, scaled, pair)))
			spanImage := arg.Have(
				"and they span the image of the span of one and u",
				"image(«omegaScaled», "+
					"    module_span(restrict_ring(field_ring(L), «curveKs»), "+
					"        restrict_module(regular_module(field_ring(L)), «curveChart1»), "+
					"        {L.one, «curveU»})) = "+
					"module_span(restrict_ring(field_ring(L), «curveKs»), "+
					"    «omegaContainer», "+
					"    image(«omegaScaled», {L.one, «curveU»}))",
				By(
					homomorphism,
					linear_independence.IndependentInCarrier.Read(chartParts[0]),
					linear_independence.HomSpan.At(polynomialOps, chartVectors, container, scaled, pair)))
			spansOmega := arg.Have(
				"which is the image of chart 1, chart 1 of ω",
				"module_span(restrict_ring(field_ring(L), «curveKs»), "+
					"    «omegaContainer», "+
					"    image(«omegaScaled», {L.one, «curveU»})) = "+
					"«omegaChart1»",
				spanImage.RwRev(),
				chartParts[1].Rw(),
				By(onto))
			imagePair := arg.TermAs[Set[Fun[A, A]]]("image(«omegaScaled», {L.one, «curveU»})")
			basisImage := arg.Have(
				"so the images of one and u are a basis of chart 1 of ω over k[s]",
				"module_basis(restrict_ring(field_ring(L), «curveKs»), "+
					"    restrict_module(«omegaContainer», «omegaChart1»), "+
					"    image(«omegaScaled», {L.one, «curveU»}))",
				By(
					polynomialsIn1,
					submodule.SubmoduleRestrictScalars.Read(overChart).At(polynomialOps),
					independentImage,
					spansOmega,
					linear_independence.BasisRestrict.Read(containerOverPolynomials).At(omega, imagePair)))

			// Read back in the statement's spelling: the two images are u • y* and y*.
			unitAct := arg.Have(
				"one acts trivially, 1 • y* = y*",
				"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(L.one * z), L.zero)) = «omegaGenerator»",
				By(module.SmulOne.Read(containerModule).At(generatorMember)))
			pairImage := arg.Have(
				"the images of one and u are u • y* and y*",
				"image(«omegaScaled», {L.one, «curveU»}) = "+
					"{λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(«curveU» * z), L.zero), «omegaGenerator»}",
				Simp(Fwd(set_image.ImageClauses)),
				unitAct.Rw(),
				By(set_algebra.InsertComm))
			acting := arg.Have(
				"u acts on y* through the argument",
				"«omegaContainer».smul(«curveU», «omegaGenerator») = "+
					"λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(«curveU» * z), L.zero)",
				Simp(Fwd(serre_duality.CurveDualizingModuleDef), Fwd(hom_module.CoextendScalarsDef)),
				Basic())
			arg.Show(
				"{u • y*, y*} is a basis of chart 1 of ω over k[s]",
				acting.Rw(),
				pairImage.RwRev(),
				By(basisImage))
		}),
})}

// ---------------------------------------------------------------------------
// The canonical pair is trivial
// ---------------------------------------------------------------------------

// CanonicalTrivial — ω ≅ O: r ↦ r • y* on the overlap, zero off it, is an
// isomorphism of lattice pairs from the structure pair (A₀, A₁) onto the
// dualizing pair. It is linear over the overlap, carries each chart onto
// that chart of ω (DualGeneratorZero, DualGeneratorOne), and is one-to-one
// on the overlap, a member w being y*(w · y) + y*(w · 1) · y.
var CanonicalTrivial = canonicalTrivialThm{family.Add(registry.ProofEntry{
	Name: "CanonicalTrivial",
	Key:  "prop_2509564702d91164",
	Reading: "The canonical pair is trivial. A map of lattice pairs is zero off the " +
		"ambient of its source, here the overlap (CurveLatticeData), whence the COND.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "lattice_pair_isomorphism(«curveOverlapRing», " +
			"    regular_module(field_ring(L)), " +
			"    («curveChart0», «curveChart1»), " +
			"    «omegaContainer», " +
			"    «omegaPair», " +
			"    λr:A. " +
			"        COND(r ∈ «curveOverlap», " +
			"            «omegaContainer».smul(r, «omegaGenerator»), " +
			"            «omegaContainer».zero))",
		Abbrev: Abbrev{
			{Name: "canonicalTrivialOverlapVectors", Text: "restrict_module(regular_module(field_ring(L)), " +
				"    «curveOverlap»)"},
			{Name: "canonicalTrivialMap", Text: "(λr:A. " +
				"    COND(r ∈ «curveOverlap», " +
				"        (λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(r * z), L.zero)), " +
				"        fun_zero))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], datum Fact) {
			A0, A1, A01 :=
				arg.TermAs[Set[A]]("«curveChart0»"),
				arg.TermAs[Set[A]]("«curveChart1»"),
				arg.TermAs[Set[A]]("«curveOverlap»")
			curve := arg.Have(
				"the datum is a curve over the line of x",
				"«curveOverLine»",
				By(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			line := algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, x)
			ambient := arg.Have(
				"the ambient of the structure pair is the overlap",
				"lattice_pair_ambient(«curveOverlapRing», "+
					"    regular_module(field_ring(L)), "+
					"    («curveChart0», «curveChart1»)) = "+
					"«curveOverlap»",
				By(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, x)))
			chart0In := arg.Have(
				"chart 0 lies in the overlap",
				"«curveChart0» ⊆ «curveOverlap»",
				By(curve, line))
			chart1In := arg.Have(
				"so does chart 1",
				"«curveChart1» ⊆ «curveOverlap»",
				By(curve, line))
			overlapSubring := arg.Have(
				"the overlap is a subring of L",
				"subring(field_ring(L), «curveOverlap»)",
				By(curve, line))
			ringOverlap := arg.Have(
				"and is a ring under the field's operations",
				"comm_ring_on(«curveOverlapRing»)",
				By(overlapSubring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A01)))

			// The container is a module over the overlap, and y* is one of its vectors.
			containerModule := arg.Conjuncts(
				GroupPremises(curve, serre_duality.DualizingIsLattice.Read(L).At(k, A0, A1, A01, x)),
				"the container is a module over the overlap",
				"ω is a lattice pair over the overlap",
				"whose ambient is the whole container")[0]
			dual := arg.Conjuncts(
				GroupPremises(datum, DualGeneratorReads.Read(L).At(k, x, y, a, b)),
				"y* is a vector of the container",
				"y* reads the coefficient of y, and at y · (p + q·y) the coefficient of one")
			generatorIn, values := dual[0], dual[1]
			generatorMember := proof.MemberOf(arg.TermAs[Fun[A, A]]("«omegaGenerator»"), generatorIn)

			// The overlap as a module over itself is the field's regular module restricted to it: the same record.
			overlapOps, overlapVectors :=
				arg.TermAs[RingOps[A]]("«curveOverlapRing»"),
				arg.TermAs[module_record.ModuleOps[A, A]]("«canonicalTrivialOverlapVectors»")
			overSelf := arg.Have(
				"the overlap is a module over itself",
				"module_on(«curveOverlapRing», «canonicalTrivialOverlapVectors»)",
				Simp(Fwd(module_record.RestrictModuleDef)),
				By(module.RegularModuleOn.Read(ringOverlap), module_record.RegularModuleDef.At(overlapOps)))
			inContainer := arg.Have(
				"r • y* lies in the container for every r of the overlap",
				Statement{
					Binders: "∀u:A.",
					Hypotheses: []string{
						"u ∈ «curveOverlap»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero)) ∈ «omegaMaps»",
				},
				Derive(func(c *Argument) {
					u := c.FixAs[A]("u")
					c.Show(
						"the container is closed under the overlap's action",
						By(module.SmulIn.Read(containerModule).At(proof.MemberOf(u, c.Assume()), generatorMember)))
				}))
			additive := arg.Have(
				"(u + v) • y* = u • y* + v • y*",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ «curveOverlap»",
						"v ∈ «curveOverlap»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»((u + v) * z), L.zero)) = " +
						"fun_add(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero), " +
						"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(v * z), L.zero))",
				},
				Derive(func(c *Argument) {
					u, v := c.FixAs[A]("u"), c.FixAs[A]("v")
					in := c.Conjuncts(
						c.Assume(),
						"u lies in the overlap",
						"so does v")
					c.Show(
						"scalars add in the container",
						By(module.SmulAddRight.Read(containerModule).At(
							proof.MemberOf(u, in[0]), proof.MemberOf(v, in[1]), generatorMember)))
				}))
			homogeneous := arg.Have(
				"(c · u) • y* = c • (u • y*), the overlap acting on the argument",
				Statement{
					Binders: "∀c u:A.",
					Hypotheses: []string{
						"c ∈ «curveOverlap»",
						"u ∈ «curveOverlap»",
					},
					Conclusion: "(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(c * u * z), L.zero)) = " +
						"λz:A. " +
						"    COND(z ∈ «curveOverlap», " +
						"        COND(c * z ∈ «curveOverlap», «omegaGenerator»(u * (c * z)), L.zero), " +
						"        L.zero)",
				},
				Derive(func(d *Argument) {
					c, u := d.FixAs[A]("c"), d.FixAs[A]("u")
					in := d.Conjuncts(
						d.Assume(),
						"c lies in the overlap",
						"so does u")
					d.Show(
						"scalars multiply in the container",
						By(module.SmulMul.Read(containerModule).At(
							proof.MemberOf(c, in[0]), proof.MemberOf(u, in[1]), generatorMember)))
				}))
			scaled, container :=
				arg.TermAs[Fun[A, Fun[A, A]]]("«omegaScaled»"),
				arg.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«omegaContainer»")
			linear := arg.Have(
				"so r ↦ r • y* is linear over the overlap, from the overlap into the container",
				"module_homomorphism(«curveOverlapRing», "+
					"    «canonicalTrivialOverlapVectors», "+
					"    «omegaContainer», "+
					"    «omegaScaled»)",
				By(
					module_homomorphism.ModuleHomomorphismDef.At(overlapOps, overlapVectors, container, scaled),
					overSelf,
					containerModule,
					inContainer,
					additive,
					homogeneous))

			// The map is r ↦ r • y* on the overlap and zero off it.
			theMap := arg.TermAs[Fun[A, Fun[A, A]]]("«canonicalTrivialMap»")
			agrees := arg.Have(
				"on the overlap the map is r ↦ r • y*",
				Statement{
					Binders: "∀u:A.",
					Hypotheses: []string{
						"u ∈ «curveOverlap»",
					},
					Conclusion: "COND(u ∈ «curveOverlap», " +
						"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero), " +
						"    fun_zero) = " +
						"λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero)",
				},
				Derive(func(c *Argument) {
					c.FixAs[A]("u")
					c.Show(
						"there the map takes its first branch",
						By(c.Assume()))
				}))
			vanishes := arg.Have(
				"and off the overlap it is the zero map",
				Statement{
					Binders: "∀u:A.",
					Hypotheses: []string{
						"u ∉ «curveOverlap»",
					},
					Conclusion: "COND(u ∈ «curveOverlap», " +
						"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero), " +
						"    fun_zero) = " +
						"fun_zero",
				},
				Derive(func(c *Argument) {
					c.FixAs[A]("u")
					c.Show(
						"there it takes the zero map",
						By(c.Assume()))
				}))
			mapLinear := arg.Have(
				"so the map is linear over the overlap as well",
				"module_homomorphism(«curveOverlapRing», "+
					"    «canonicalTrivialOverlapVectors», "+
					"    «omegaContainer», "+
					"    «canonicalTrivialMap»)",
				By(
					module_homomorphism.HomCongruence.At(overlapOps, overlapVectors, container, scaled, theMap),
					linear,
					agrees))
			inHomSet := arg.Have(
				"being zero off the overlap, the map lies in hom_set",
				"«canonicalTrivialMap» ∈ "+
					"hom_set(«curveOverlapRing», «canonicalTrivialOverlapVectors», «omegaContainer»)",
				By(hom_module.InHomSet.At(overlapOps, overlapVectors, container, theMap), mapLinear, vanishes))

			// Each chart lies in the overlap, where the map is r ↦ r • y*, so it carries the chart onto that chart times y*, the chart of ω.
			agreesOn := func(label, claim string, within Fact) Fact {
				return arg.Have(
					label,
					claim,
					Derive(func(c *Argument) {
						c.FixAs[A]("u")
						inOverlap := c.Have(
							"u lies in the overlap, as the chart does",
							"u ∈ «curveOverlap»",
							BySets(within, c.Assume()))
						c.Show(
							"where the map is u ↦ u • y*",
							By(inOverlap))
					}))
			}
			agrees0 := agreesOn("chart 0 lies in the overlap, so there the map is r ↦ r • y*",
				"∀u:A. u ∈ «curveChart0» ⇒ COND(u ∈ «curveOverlap», (λz:A. COND(z "+
					"∈ «curveOverlap», «omegaGenerator»(u * z), L.zero)), fun_zero) = "+
					"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero))",
				chart0In)
			agrees1 := agreesOn("and so does chart 1",
				"∀u:A. u ∈ «curveChart1» ⇒ COND(u ∈ «curveOverlap», (λz:A. COND(z "+
					"∈ «curveOverlap», «omegaGenerator»(u * z), L.zero)), fun_zero) = "+
					"(λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero))",
				chart1In)
			sameOn0 := arg.Have(
				"so the map and r ↦ r • y* carry chart 0 onto one set",
				"image(«canonicalTrivialMap», «curveChart0») = image(«omegaScaled», «curveChart0»)",
				By(set_image.ImageCongruence.At(theMap, scaled, A0), agrees0))
			sameOn1 := arg.Have(
				"and chart 1 onto one set",
				"image(«canonicalTrivialMap», «curveChart1») = image(«omegaScaled», «curveChart1»)",
				By(set_image.ImageCongruence.At(theMap, scaled, A1), agrees1))
			image0 := arg.Have(
				"the map carries chart 0 onto A₀ • y*, chart 0 of ω",
				"image(«canonicalTrivialMap», «curveChart0») = «omegaChart0»",
				sameOn0.Rw(),
				GroupPremises(datum, DualGeneratorZero.Read(L).At(k, x, y, a, b)).Rw(),
				By(set_image.SimpleImage))
			image1 := arg.Have(
				"and chart 1 onto A₁ • y*, chart 1 of ω",
				"image(«canonicalTrivialMap», «curveChart1») = «omegaChart1»",
				sameOn1.Rw(),
				GroupPremises(datum, DualGeneratorOne.Read(L).At(k, x, y, a, b)).Rw(),
				By(set_image.SimpleImage))

			// One-to-one: y* reads a member w of the overlap off its values at w and at w · y.
			ringL := field.RingOn.Read(L)
			ym := arg.MemberOf[on.L](y, WeierstrassYInField.Read(datum).AsFact())
			laurentSubring := arg.Have(
				"k[x, 1/x] is a subring of L",
				"subring(field_ring(L), «curveLaurent»)",
				By(curve, line))
			expansions := arg.Conjuncts(
				GroupPremises(datum, WeierstrassOverlapCoordinates.Read(L).At(k, x, y, a, b)),
				"the overlap is k[x, 1/x] · 1 + k[x, 1/x] · y",
				"each of its members so in one way")[0]
			reconstructs := arg.Have(
				"every member w of the overlap is y*(w · y) + y*(w · one) · y",
				"∀w:A. w ∈ «curveOverlap» ⇒ w = «omegaGenerator»(w * y) + «omegaGenerator»(w * L.one) * y",
				Derive(func(c *Argument) {
					w := c.FixAs[A]("w")
					wIn := c.Assume()
					p, q, split := c.Obtain2As[A, A](
						"w is p + q · y with p and q in k[x, 1/x]",
						"∃p q:A. p ∈ «curveLaurent» ∧ q ∈ «curveLaurent» ∧ w = p + q * y",
						By(expansions.At(w), wIn))
					parts := c.Conjuncts(
						split,
						"p lies in k[x, 1/x]",
						"so does q",
						"w = p + q · y")
					read := c.Conjuncts(
						GroupPremises(parts[0], parts[1], values.At(p, q)),
						"y* reads q at p + q · y",
						"and p at y · (p + q · y)")
					wm := c.MemberOf[on.L](w, c.Have(
						"w lies in L",
						"w ∈ L.carrier",
						BySets(comm_ring.SubringSubset.Read(overlapSubring), wIn)))
					inL := c.Conjuncts(
						c.Have(
							"p and q lie in L",
							"p ∈ L.carrier ∧ q ∈ L.carrier",
							BySets(comm_ring.SubringSubset.Read(laurentSubring), parts[0], parts[1])),
						"p lies in L",
						"q lies in L")
					products := c.Have(
						"w · one = p + q · y and w · y = y · (p + q · y)",
						"w * L.one = p + q * y ∧ w * y = y * (p + q * y)",
						ByArith(
							ringL,
							wm,
							c.MemberOf[on.L](p, inL[0]),
							c.MemberOf[on.L](q, inL[1]),
							ym,
							Scaled(y, parts[2])))
					c.Show(
						"so y*(w · one) = q and y*(w · y) = p",
						By(wIn, parts[2], products, read[0], read[1]))
				}))
			chartBasis := arg.Conjuncts(
				GroupPremises(datum, WeierstrassBasisZero.Read(L).At(k, x, y, a, b)),
				"chart 0 is a subring of L",
				"k[x] lies in chart 0",
				"1 and y are a basis of chart 0 over k[x]",
				"one is not y")[2]
			chartParts := arg.Conjuncts(
				arg.Unfolded(chartBasis, linear_independence.ModuleBasisDef),
				"1 and y are independent over k[x]",
				"they span chart 0")
			oneIn := comm_ring.OneIn.Read(ringOverlap)
			yIn := arg.Have(
				"y, being independent in chart 0, lies in it, and so in the overlap",
				"y ∈ «curveOverlap»",
				By(
					arg.Simplified(
						linear_independence.IndependentInCarrier.Read(chartParts[0]),
						Fwd(set_order.InsertSubset),
						Fwd(set_order.EmptySubset)),
					chart0In,
					set_basic.SubsetDef.At(A0, A01)))
			injective := arg.Have(
				"the map is one-to-one on the overlap",
				"injective_on(«curveOverlap», «canonicalTrivialMap»)",
				Unfold(functions.InjectiveOnDef),
				Derive(func(c *Argument) {
					u, v := c.FixAs[A]("u"), c.FixAs[A]("v")
					points := c.Conjuncts(
						c.Assume(),
						"u lies in the overlap",
						"so does v",
						"and the map takes one value at u and at v")
					atY := c.Have(
						"so the two values agree at y",
						"COND(u ∈ «curveOverlap», "+
							"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero), "+
							"    fun_zero)(y) = "+
							"COND(v ∈ «curveOverlap», "+
							"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(v * z), L.zero), "+
							"    fun_zero)(y)",
						points[2].Rw(),
						Basic())
					atOne := c.Have(
						"and at one",
						"COND(u ∈ «curveOverlap», "+
							"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(u * z), L.zero), "+
							"    fun_zero)(L.one) = "+
							"COND(v ∈ «curveOverlap», "+
							"    λz:A. COND(z ∈ «curveOverlap», «omegaGenerator»(v * z), L.zero), "+
							"    fun_zero)(L.one)",
						points[2].Rw(),
						Basic())
					readY := c.Have(
						"so y*(u · y) = y*(v · y), u, v and y lying in the overlap",
						"«omegaGenerator»(u * y) = «omegaGenerator»(v * y)",
						By(atY, points[0], points[1], yIn))
					readOne := c.Have(
						"and y*(u · 1) = y*(v · 1)",
						"«omegaGenerator»(u * L.one) = «omegaGenerator»(v * L.one)",
						By(atOne, points[0], points[1], oneIn))
					c.Show(
						"so u and v, each read off its value, are equal",
						CalcEq(
							Leg(
								c.TermAs[A]("«omegaGenerator»(u * y) + «omegaGenerator»(u * L.one) * y"),
								"u is read off u • y*",
								By(reconstructs.At(u), points[0])),
							FinalLeg(
								"which reads off v • y* as v",
								readY.Rw(),
								readOne.Rw(),
								By(reconstructs.At(v), points[1]))))
				}))

			arg.Show(
				"so the map is an isomorphism of the structure pair onto ω: a "+
					"map of lattice pairs onto each chart, one-to-one on the overlap",
				Simp(
					Fwd(lattice_pair_map.LatticePairIsomorphismDef),
					Fwd(lattice_pair_map.LatticePairMapsDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				ambient.Rw(),
				BySets(inHomSet, injective, image0, image1))
		}),
})}

// ---------------------------------------------------------------------------
// Riemann–Roch on the curve
// ---------------------------------------------------------------------------

// WeierstrassRiemannRoch — Riemann–Roch on the Weierstrass curve: for an
// invertible pair M, M and M⁻¹ have finite cohomology and
// ℓ(M) − ℓ(M⁻¹) = deg M. Riemann–Roch on the curve gives
// ℓ(M) − dim Hom(M, ω) = deg M + 1 − g, and g = 1 (GenusOne); composing
// with the isomorphism f of CanonicalTrivial carries Hom(M, O) onto
// Hom(M, ω), and Hom(M, O) is H⁰(O · M⁻¹) = H⁰(M⁻¹) (SectionsAreMaps, MulOne).
var WeierstrassRiemannRoch = weierstrassRiemannRochThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassRiemannRoch",
	Key:  "prop_6389dd7138903de9",
	Reading: "ℓ(M) − ℓ(K − M) = deg M + 1 − g at K = 0 and g = 1. M " +
		"invertible is what makes the cohomology of M and of M⁻¹ finite.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"weierstrass(L, k, x, y, a, b)",
			"invertible_lattice_pair(field_ring(L), «curveChart0», «curveChart1», «curveOverlap», M)",
		},
		Conclusion: "lattice_pair_finite(«curveOverlapRing», k, regular_module(field_ring(L)), M) ∧ " +
			"lattice_pair_finite(«curveOverlapRing», " +
			"    k, " +
			"    regular_module(field_ring(L)), " +
			"    «weierstrassRiemannRochInverse») ∧ " +
			"int_of_num(lattice_pair_h0_dim(«curveOverlapRing», k, regular_module(field_ring(L)), M)) - " +
			"int_of_num(lattice_pair_h0_dim(«curveOverlapRing», " +
			"        k, " +
			"        regular_module(field_ring(L)), " +
			"        «weierstrassRiemannRochInverse»)) = " +
			"curve_degree(field_ring(L), k, «curveChart0», «curveChart1», «curveOverlap», M)",
		Abbrev: Abbrev{
			{Name: "weierstrassRiemannRochScalars", Text: "restrict_ring(«curveOverlapRing», k)"},
			{Name: "weierstrassRiemannRochField", Text: "regular_module(field_ring(L))"},
			{Name: "weierstrassRiemannRochInverse", Text: "lattice_pair_inverse(field_ring(L), " +
				"    «curveChart0», " +
				"    «curveChart1», " +
				"    M)"},
			{Name: "weierstrassRiemannRochSections", Text: "lattice_pair_h0(«weierstrassRiemannRochField», " +
				"    «weierstrassRiemannRochInverse»)"},
			{Name: "weierstrassRiemannRochAmbient", Text: "lattice_pair_ambient(«curveOverlapRing», " +
				"    «weierstrassRiemannRochField», " +
				"    M)"},
			{Name: "weierstrassRiemannRochDualizingMaps", Text: "curve_dualizing_maps(L, " +
				"    k, " +
				"    x, " +
				"    «curveChart0», " +
				"    «curveChart1», " +
				"    «curveOverlap», " +
				"    M)"},
			{Name: "weierstrassRiemannRochMultiplication", Text: "λc:A. λz:A. " +
				"    COND(z ∈ «weierstrassRiemannRochAmbient», c * z, L.zero)"},
			{Name: "weierstrassRiemannRochComposing", Text: "λh:(A → A). f ∘ h"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			M *Expr[Prod[Set[A], Set[A]]],
			given Fact,
		) {
			hypotheses := arg.Conjuncts(
				given,
				"the Weierstrass datum",
				"M is an invertible pair")
			datum, invertible := hypotheses[0], hypotheses[1]
			A0, A1, A01 :=
				arg.TermAs[Set[A]]("«curveChart0»"),
				arg.TermAs[Set[A]]("«curveChart1»"),
				arg.TermAs[Set[A]]("«curveOverlap»")
			inverse := arg.TermAs[Prod[Set[A], Set[A]]]("«weierstrassRiemannRochInverse»")

			// Riemann–Roch on the curve, at genus one.
			curve := arg.Have(
				"the datum is a curve over the line of x",
				"«curveOverLine»",
				By(datum, WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			riemannRoch := arg.Conjuncts(
				GroupPremises(curve, hypotheses[1], serre_duality.RiemannRoch.Read(L).At(k, A0, A1, A01, x, M)),
				"M has finite cohomology",
				"Hom(M, ω) is finite-dimensional over k",
				"ℓ(M) − dim Hom(M, ω) = deg M + 1 − g")
			genus := arg.Have(
				"the genus is one",
				"curve_genus(field_ring(L), k, «curveChart0», «curveChart1», «curveOverlap») = 1",
				By(datum, GenusOne.Read(L).At(k, x, y, a, b)))
			data := arg.Conjuncts(
				GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, x)),
				"the overlap lies in L",
				"the charts and the overlap are a biaffine datum",
				"k is a subfield of L",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"it is invertible",
				"k is a field",
				"k lies in both charts")
			inField, biaffine, subfield, pairO, kField, kInCharts :=
				data[0], data[1], data[2], data[3], data[6], data[7]

			// M⁻¹ is invertible, so its cohomology is finite too.
			inverseInvertible := arg.Have(
				"M⁻¹ is invertible",
				"invertible_lattice_pair(field_ring(L), "+
					"    «curveChart0», "+
					"    «curveChart1», "+
					"    «curveOverlap», "+
					"    «weierstrassRiemannRochInverse»)",
				By(
					inField,
					biaffine,
					invertible,
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, x, M)))
			inverseFinite := arg.Have(
				"so M⁻¹ has finite cohomology",
				"lattice_pair_finite(«curveOverlapRing», "+
					"    k, "+
					"    «weierstrassRiemannRochField», "+
					"    «weierstrassRiemannRochInverse»)",
				By(
					curve,
					inverseInvertible,
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, x, inverse)))

			// k as the scalars of the maps, a ring inside both charts.
			fieldOps := arg.TermAs[FieldOps[A]]("L")
			overlapRing, scalars :=
				arg.TermAs[RingOps[A]]("«curveOverlapRing»"),
				arg.TermAs[RingOps[A]]("«weierstrassRiemannRochScalars»")
			fieldModule := arg.TermAs[module_record.ModuleOps[A, A]]("«weierstrassRiemannRochField»")
			kRing := arg.Have(
				"k is a ring under the overlap's operations",
				"comm_ring_on(«weierstrassRiemannRochScalars»)",
				By(
					field.RingOn.Read(kField),
					field.FieldRingDef.At(arg.TermAs[FieldOps[A]]("restrict_field(L, k)")),
					field.RestrictFieldDef.At(fieldOps, k),
					module_record.RestrictRingDef.At(overlapRing, k)))
			kCharts := arg.Conjuncts(
				arg.Have(
					"k lies in each chart",
					"k ⊆ «curveChart0» ∧ k ⊆ «curveChart1»",
					BySets(kInCharts)),
				"k lies in chart 0",
				"k lies in chart 1")
			rings := arg.Conjuncts(
				GroupPremises(
					data[0], data[1], invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, x)),
				"chart 0 lies in the overlap",
				"and so does chart 1",
				"the overlap is a subring of L",
				"and so is chart 0",
				"and so is chart 1")
			overlapIsRing := arg.Have(
				"the overlap is a ring under L's operations",
				"comm_ring_on(«curveOverlapRing»)",
				By(rings[2], comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A01)))
			kInOverlap := arg.Have(
				"k lies in the overlap, as chart 0 does",
				"k ⊆ «curveOverlap»",
				BySets(kCharts[0], rings[0]))
			kSubring := arg.Have(
				"so k is a subring of the overlap",
				"subring(«curveOverlapRing», k)",
				By(kInOverlap, kRing, comm_ring.SubringRingOn.Read(overlapIsRing).At(k)))

			// H⁰(M⁻¹) ≅ Hom(M, O) ≅ Hom(M, ω).
			structure := arg.TermAs[Prod[Set[A], Set[A]]]("(«curveChart0», «curveChart1»)")
			unit := arg.Have(
				"the structure pair is the unit: O · M⁻¹ = M⁻¹",
				"lattice_pair_mul(field_ring(L), "+
					"    «curveChart0», "+
					"    «curveChart1», "+
					"    («curveChart0», «curveChart1»), "+
					"    «weierstrassRiemannRochInverse») = "+
					"«weierstrassRiemannRochInverse»",
				By(
					inField,
					biaffine,
					arg.Unfolded(inverseInvertible, invertible_lattice_pair.InvertibleLatticePairDef),
					invertible_lattice_pair.MulOne.Read(L).At(A0, A1, A01, x, inverse)))
			sections := arg.Have(
				"multiplication is a k-isomorphism of H⁰(M⁻¹) onto the maps M → O",
				"module_isomorphism(«weierstrassRiemannRochScalars», "+
					"    «weierstrassRiemannRochSections», "+
					"    lattice_pair_hom(«curveOverlapRing», "+
					"        «weierstrassRiemannRochField», "+
					"        M, "+
					"        «weierstrassRiemannRochField», "+
					"        («curveChart0», «curveChart1»)), "+
					"    «weierstrassRiemannRochMultiplication»)",
				By(
					unit,
					inField,
					biaffine,
					kSubring,
					kCharts[0],
					kCharts[1],
					invertible,
					pairO,
					invertible_lattice_pair.SectionsAreMaps.Read(L).At(A0, A1, A01, k, x, M, structure)))
			f, canonical := arg.ObtainAs[Fun[A, Fun[A, A]]](
				"the canonical pair is trivial: an isomorphism f carries O onto ω",
				"∃f:(A → A → A). "+
					"    lattice_pair_isomorphism(«curveOverlapRing», "+
					"        «weierstrassRiemannRochField», "+
					"        («curveChart0», «curveChart1»), "+
					"        «omegaContainer», "+
					"        «omegaPair», "+
					"        f)",
				By(datum, CanonicalTrivial.Read(L).At(k, x, y, a, b)))
			pairM := arg.Have(
				"M is a lattice pair over the overlap",
				"lattice_pair(«curveOverlapRing», «curveChart0», «curveChart1», «weierstrassRiemannRochField», M)",
				By(arg.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef)))
			dualizingModule := arg.TermAs[module_record.ModuleOps[A, Fun[A, A]]]("«omegaContainer»")
			dualizingPair := arg.TermAs[Prod[Set[Fun[A, A]], Set[Fun[A, A]]]]("«omegaPair»")
			postcompose := arg.Have(
				"composing with f is a k-isomorphism of the maps M → O onto Hom(M, ω)",
				"module_isomorphism(«weierstrassRiemannRochScalars», "+
					"    lattice_pair_hom(«curveOverlapRing», "+
					"        «weierstrassRiemannRochField», "+
					"        M, "+
					"        «weierstrassRiemannRochField», "+
					"        («curveChart0», «curveChart1»)), "+
					"    «weierstrassRiemannRochDualizingMaps», "+
					"    «weierstrassRiemannRochComposing»)",
				By(
					biaffine,
					kSubring,
					kCharts[0],
					kCharts[1],
					pairM,
					pairO,
					canonical,
					lattice_pair_map.MapsPostcomposeIsomorphism.At(
						overlapRing,
						A0,
						A1,
						k,
						x,
						arg.TermAs[A]("L.inv(x)"),
						fieldModule,
						fieldModule,
						dualizingModule,
						M,
						structure,
						dualizingPair,
						f),
					serre_duality.CurveDualizingMapsDef))
			sectionsModule := arg.TermAs[module_record.ModuleOps[A, A]]("«weierstrassRiemannRochSections»")
			structureMaps := arg.TermAs[module_record.ModuleOps[A, Fun[A, A]]](
				"lattice_pair_hom(«curveOverlapRing», " +
					"    «weierstrassRiemannRochField», " +
					"    M, " +
					"    «weierstrassRiemannRochField», " +
					"    («curveChart0», «curveChart1»))")
			dualizingMaps := arg.TermAs[module_record.ModuleOps[A, Fun[A, Fun[A, A]]]](
				"«weierstrassRiemannRochDualizingMaps»")
			multiplication := arg.TermAs[Fun[A, Fun[A, A]]]("«weierstrassRiemannRochMultiplication»")
			composing := arg.TermAs[Fun[Fun[A, A], Fun[A, Fun[A, A]]]]("«weierstrassRiemannRochComposing»")
			composed := arg.TermAs[Fun[A, Fun[A, Fun[A, A]]]](
				"«weierstrassRiemannRochComposing» ∘ «weierstrassRiemannRochMultiplication»")
			compositeIso := arg.Have(
				"so multiplication, then composing with f, is a k-isomorphism of H⁰(M⁻¹) onto Hom(M, ω)",
				"module_isomorphism(«weierstrassRiemannRochScalars», "+
					"    «weierstrassRiemannRochSections», "+
					"    «weierstrassRiemannRochDualizingMaps», "+
					"    «weierstrassRiemannRochComposing» ∘ «weierstrassRiemannRochMultiplication»)",
				By(
					sections,
					postcompose,
					module_homomorphism.IsomorphismCompose.At(
						scalars, sectionsModule, structureMaps, dualizingMaps, multiplication, composing)))

			// So the two have one dimension, ℓ(M⁻¹), measured over k as a field
			// under L's operations, with L's inverse.
			kInverse := arg.TermAs[Fun[A, A]]("L.inv")
			dimension := arg.Have(
				"so dim Hom(M, ω) = ℓ(M⁻¹)",
				"module_dim(«weierstrassRiemannRochScalars», «weierstrassRiemannRochDualizingMaps») = "+
					"lattice_pair_h0_dim(«curveOverlapRing», "+
					"    k, "+
					"    «weierstrassRiemannRochField», "+
					"    «weierstrassRiemannRochInverse»)",
				By(
					inverseFinite,
					lattice_pair.LatticePairFiniteDef.At(overlapRing, k, fieldModule, inverse),
					compositeIso,
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, A01),
					field.RingSubfieldRestrict.At(overlapRing, k, kInverse, k),
					module_dimension.IsomorphismDim.At(scalars, sectionsModule, kInverse, dualizingMaps, composed),
					lattice_pair.LatticePairH0DimDef.At(overlapRing, k, fieldModule, inverse)))
			count := arg.Have(
				"ℓ(M) − ℓ(M⁻¹) = deg M + 1 − g = deg M",
				"int_of_num(lattice_pair_h0_dim(«curveOverlapRing», k, «weierstrassRiemannRochField», M)) - "+
					"int_of_num(lattice_pair_h0_dim(«curveOverlapRing», "+
					"        k, "+
					"        «weierstrassRiemannRochField», "+
					"        «weierstrassRiemannRochInverse»)) = "+
					"curve_degree(field_ring(L), k, «curveChart0», «curveChart1», «curveOverlap», M)",
				ByArith(riemannRoch[2], genus, dimension))
			arg.Show(
				"M and M⁻¹ have finite cohomology, and ℓ(M) − ℓ(M⁻¹) = deg M",
				By(riemannRoch[0], inverseFinite, count))
		}),
})}

// ---------------------------------------------------------------------------
// The dualizing pair and the Kähler differentials
// ---------------------------------------------------------------------------

// WeierstrassKaehlerCharts — where the curve is smooth, the module of
// Kähler differentials over k of each chart, a subring of the field, is
// free of rank one on an invariant differential: dx = 2y·ω and
// dy = (3x² + a)·ω on chart 0, ds = 2u·ω and du = (1 + 3as² + 4bs³)·ω on
// chart 1.
var WeierstrassKaehlerCharts = weierstrassKaehlerChartsThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassKaehlerCharts",
	Key:  "prop_d022e6f752db8183",
	Reading: "WeierstrassKaehlerAffine read on the charts inside the field: each chart is " +
		"its model ring, a quotient of a free algebra, through the image isomorphisms " +
		"(WeierstrassImageIsomorphism, WeierstrassChartOneEmbeds), and the Kähler module and " +
		"the universal derivation go along a ring isomorphism fixing k. The two clauses the " +
		"smooth datum adds, 2 ≠ 0 and 4a³ + 27b² ≠ 0, are WeierstrassKaehlerAffine's hypotheses " +
		"and load-bearing as there: on the cusp a = b = 0 chart 0 needs dx and dy at x = y = 0.",
	Deps: []registry.EntryLike{
		WeierstrassKaehlerAffine,
		WeierstrassImageIsomorphism,
		WeierstrassChartOneEmbeds,
		WeierstrassDef,
		simplicial_ring.PowerSetUniverse,
		field.SubfieldFieldOn,
		kaehler.KaehlerUniversalExists,
		kaehler.KaehlerUniversalUnique,
		kaehler.KaehlerSpan,
		kaehler.KaehlerModuleOn,
		kaehler.UniversalDerivationIsDerivation,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∃ω:set(A → A). " +
			"    module_isomorphism( " +
			"        restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        restrict_module(regular_module(field_ring(L)), " +
			"            weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        kaehler_module(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"            λc:A. c), " +
			"        λr:A. " +
			"            kaehler_module(restrict_ring(field_ring(L), k), " +
			"                restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"                λc:A. c).smul(r, ω)) ∧ " +
			"    universal_derivation(restrict_ring(field_ring(L), k), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        λc:A. c, " +
			"        x) = " +
			"    kaehler_module(restrict_ring(field_ring(L), k), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        λc:A. c).smul(y + y, ω) ∧ " +
			"    universal_derivation(restrict_ring(field_ring(L), k), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        λc:A. c, " +
			"        y) = " +
			"    kaehler_module(restrict_ring(field_ring(L), k), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        λc:A. c).smul(monoid_pow(L.add, L.zero, L.one, 3) * (x * x) + a, ω)) ∧ " +
			"(∃ω:set(A → A). " +
			"    module_isomorphism(restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"        restrict_module(regular_module(field_ring(L)), weierstrass_chart_one(L, k, x, y)), " +
			"        kaehler_module(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"            λc:A. c), " +
			"        λr:A. " +
			"            kaehler_module(restrict_ring(field_ring(L), k), " +
			"                restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"                λc:A. c).smul(r, ω)) ∧ " +
			"    universal_derivation(restrict_ring(field_ring(L), k), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"        λc:A. c, " +
			"        L.inv(x)) = " +
			"    kaehler_module(restrict_ring(field_ring(L), k), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"        λc:A. c).smul(y * (L.inv(x) * L.inv(x)) + y * (L.inv(x) * L.inv(x)), ω) ∧ " +
			"    universal_derivation(restrict_ring(field_ring(L), k), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"        λc:A. c, " +
			"        y * (L.inv(x) * L.inv(x))) = " +
			"    kaehler_module(restrict_ring(field_ring(L), k), " +
			"        restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"        λc:A. c).smul(L.one + " +
			"        monoid_pow(L.add, L.zero, L.one, 3) * a * (L.inv(x) * L.inv(x)) + " +
			"        monoid_pow(L.add, L.zero, L.one, 4) * b * (L.inv(x) * (L.inv(x) * L.inv(x))), " +
			"        ω))",
	},
		"k is a field with L's operations (SubfieldFieldOn), and the host set(prod(num, A)) has "+
			"room for it, c ↦ {(0, c)} being one-to-one (PowerSetUniverse); take two distinct names "+
			"of the host for each chart. WeierstrassKaehlerAffine gives each model ring's Kähler "+
			"module free on ω with the stated values at the classes of the variables; "+
			"WeierstrassImageIsomorphism and WeierstrassChartOneEmbeds give ring isomorphisms φ from "+
			"the model rings onto the charts, fixing k and sending the variables to x, y and to "+
			"inv(x), u. A ring isomorphism fixing k carries Kähler modules along: d ∘ φ is a "+
			"derivation of the model ring over k into the chart's module read through φ, and the maps "+
			"KaehlerUniversalExists gives in the two directions are inverse by KaehlerUniversalUnique "+
			"(KaehlerSpan for the generators); the image of the model's ω is the chart's"),
})}

// KaehlerCanonical — ω ≅ Ω¹: where the curve is smooth, each chart of the
// dualizing pair is isomorphic, over its chart, to that chart's module of
// Kähler differentials, by an isomorphism sending dx/2y to y* — dx to
// 2y • y* and dy to (3x² + a) • y* on chart 0, and, as ds/2u = −dx/2y, ds to
// −2u • y* and du to −(1 + 3as² + 4bs³) • y* on chart 1.
var KaehlerCanonical = kaehlerCanonicalThm{family.Add(registry.ProofEntry{
	Name: "KaehlerCanonical",
	Key:  "prop_dd6c9b11459783d7",
	Reading: "Stated chart by chart, on the Kähler modules of the charts as subrings of the " +
		"field: Ω¹ of the curve is these two modules glued over the overlap, and the gluing is " +
		"carried by the values at the generators. The values fix each isomorphism, dx, dy generating " +
		"chart 0's module and ds, du chart 1's (KaehlerSpan), and they say the two isomorphisms send " +
		"one differential to one functional: s = 1/x and u = y/x² give ds/2u = −dx/2y, and dx/2y goes " +
		"to y* on both charts. The model rings' modules (WeierstrassKaehlerAffine) enter through " +
		"WeierstrassKaehlerCharts. 2 ≠ 0 and 4a³ + 27b² ≠ 0 are load-bearing: ω is free on every " +
		"Weierstrass cubic (CanonicalTrivial), Ω¹ only on the smooth ones. On chart 1 the values ds ↦ " +
		"−2u • y* and du ↦ −(1 + 3as² + 4bs³) • y* both send ω₁ to −y*, the sign of ds/2u = −dx/2y.",
	Deps: []registry.EntryLike{
		WeierstrassKaehlerCharts,
		CanonicalTrivial,
		DualGeneratorZero,
		DualGeneratorOne,
		DualBasisZero,
		serre_duality.DualizingIsLattice,
		WeierstrassIsCurve,
		kaehler.KaehlerSpan,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.ModuleHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(∃Θ:(set(A → A) → A → A). " +
			"    module_isomorphism( " +
			"        restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"        kaehler_module(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"            λc:A. c), " +
			"        restrict_module(curve_dualizing_module(field_ring(L), " +
			"                k, " +
			"                x, " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            fst(curve_dualizing_pair(L, " +
			"                    k, " +
			"                    x, " +
			"                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)))), " +
			"        Θ) ∧ " +
			"    Θ(universal_derivation(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"            λc:A. c, " +
			"            x)) = " +
			"    curve_dualizing_module(field_ring(L), " +
			"        k, " +
			"        x, " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)).smul( " +
			"        y + y, weierstrass_dual_generator(field_ring(L), k, x, y)) ∧ " +
			"    Θ(universal_derivation(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y)), " +
			"            λc:A. c, " +
			"            y)) = " +
			"    curve_dualizing_module(field_ring(L), " +
			"        k, " +
			"        x, " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)).smul( " +
			"        monoid_pow(L.add, L.zero, L.one, 3) * (x * x) + a, " +
			"        weierstrass_dual_generator(field_ring(L), k, x, y))) ∧ " +
			"(∃Θ:(set(A → A) → A → A). " +
			"    module_isomorphism(restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"        kaehler_module(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"            λc:A. c), " +
			"        restrict_module(curve_dualizing_module(field_ring(L), " +
			"                k, " +
			"                x, " +
			"                ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)), " +
			"            snd(curve_dualizing_pair(L, " +
			"                    k, " +
			"                    x, " +
			"                    weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                    weierstrass_chart_one(L, k, x, y), " +
			"                    ring_away(field_ring(L), " +
			"                        weierstrass_chart_zero(field_ring(L), k, x, y), " +
			"                        x)))), " +
			"        Θ) ∧ " +
			"    Θ(universal_derivation(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"            λc:A. c, " +
			"            L.inv(x))) = " +
			"    curve_dualizing_module(field_ring(L), " +
			"        k, " +
			"        x, " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)).smul( " +
			"        L.neg(y * (L.inv(x) * L.inv(x)) + y * (L.inv(x) * L.inv(x))), " +
			"        weierstrass_dual_generator(field_ring(L), k, x, y)) ∧ " +
			"    Θ(universal_derivation(restrict_ring(field_ring(L), k), " +
			"            restrict_ring(field_ring(L), weierstrass_chart_one(L, k, x, y)), " +
			"            λc:A. c, " +
			"            y * (L.inv(x) * L.inv(x)))) = " +
			"    curve_dualizing_module(field_ring(L), " +
			"        k, " +
			"        x, " +
			"        ring_away(field_ring(L), weierstrass_chart_zero(field_ring(L), k, x, y), x)).smul( " +
			"        L.neg(L.one + " +
			"            monoid_pow(L.add, L.zero, L.one, 3) * a * (L.inv(x) * L.inv(x)) + " +
			"            monoid_pow(L.add, L.zero, L.one, 4) * b * (L.inv(x) * (L.inv(x) * L.inv(x)))), " +
			"        weierstrass_dual_generator(field_ring(L), k, x, y)))",
	},
		"WeierstrassKaehlerCharts gives chart 0's module free on ω₀ with dx = 2y·ω₀, dy = (3x² + "+
			"a)·ω₀, and chart 1's free on ω₁ with ds = 2u·ω₁, du = (1 + 3as² + 4bs³)·ω₁; "+
			"CanonicalTrivial with DualGeneratorZero and DualGeneratorOne makes fst(ω) free over A₀ on "+
			"y* and snd(ω) free over A₁ on y*, r • y* = zero only at r = zero, the container a module "+
			"over the overlap (DualizingIsLattice). Put Θ₀(r • ω₀) = r • y* and Θ₁(r • ω₁) = (−r) • y*, "+
			"each the composite of two isomorphisms with the chart as a module over itself; then Θ₀(dx) "+
			"= 2y • y*, Θ₀(dy) = (3x² + a) • y*, Θ₁(ds) = −2u • y* and Θ₁(du) = −(1 + 3as² + 4bs³) • y*"),
})}
